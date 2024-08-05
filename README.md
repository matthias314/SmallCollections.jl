# SmallCollections.jl

This Julia package defines three immutable collections types, `SmallVector`,
`PackedVector` and `SmallBitSet`. They don't allocate and are often much faster
than their allocating counterparts `Vector` and `BitSet`. Unlike the static vectors
provided by [StaticArrays.jl](https://github.com/JuliaArrays/StaticArrays.jl),
[StaticVectors.jl](https://github.com/chakravala/StaticVectors.jl) and
[SIMD.jl](https://github.com/eschnett/SIMD.jl),
the length of a `SmallVector` or `PackedVector` is variable with a user-defined limit.

If the package [BangBang.jl](https://github.com/JuliaFolds2/BangBang.jl)
is loaded, then many functions defined by this package are also available
in a `!!`-form. For example, both `push` and `push!!` add an element
to a `SmallVector`, `PackedVector` or `SmallBitSet`.

Below are [examples](#examples) and [benchmarks](#benchmarks). For details see
the [documentation](https://matthias314.github.io/SmallCollections.jl/stable/).

## Examples

### `SmallVector`

A vector of type `SmallVector{N,T}` can hold up to `N` elements of type `T`.
Both `N` and `T` can be arbitrary. (If `T` is not a concrete type, however,
then creating a small vector does allocate.)
```julia
julia> v = SmallVector{8,Int8}(2*x for x in 1:3)
3-element SmallVector{8, Int8}:
 2
 4
 6

julia> setindex(v, 7, 3)
3-element SmallVector{8, Int8}:
 2
 4
 7

julia> w = SmallVector{9}((1, 2.5, 4))
3-element SmallVector{9, Float64}:
 1.0
 2.5
 4.0

julia> v+2*w
3-element SmallVector{8, Float64}:
  4.0
  9.0
 14.0
```
Non-numeric element types are possible. (One may have to define
a default element used for padding via `SmallCollections.default(T)`.
For `Char`, `String` and `Symbol` they are pre-defined.)
```julia
julia> u = SmallVector{6}(['a', 'b', 'c'])
3-element SmallVector{6, Char}:
 'a': ASCII/Unicode U+0061 (category Ll: Letter, lowercase)
 'b': ASCII/Unicode U+0062 (category Ll: Letter, lowercase)
 'c': ASCII/Unicode U+0063 (category Ll: Letter, lowercase)

julia> popfirst(u)
(['b', 'c'], 'a')

julia> map(uppercase, u)
3-element SmallVector{6, Char}:
 'A': ASCII/Unicode U+0041 (category Lu: Letter, uppercase)
 'B': ASCII/Unicode U+0042 (category Lu: Letter, uppercase)
 'C': ASCII/Unicode U+0043 (category Lu: Letter, uppercase)
```

### `PackedVector`

A `PackedVector` can store bit integers or `Bool` values.
The elements of a `PackedVector{U,M,T}` are stored in a common bit mask of type `U`
with `M` bits for each entry. When retrieving elements, they are of type `T`.

Compared to a `SmallVector`, a `PackedVector` may have faster insert and delete operations.
Arithmetic operations are usually slower unless `M` is the size of a hardware integer.
```julia
julia> v = PackedVector{UInt64,5,Int}(4:6)
3-element PackedVector{UInt64, 5, Int64}:
 4
 5
 6

julia> capacity(v)  # 64 bits available, 5 for each entry
12

julia> pushfirst(v, 7)
4-element PackedVector{UInt64, 5, Int64}:
 7
 4
 5
 6

julia> duplicate(v, 2)
4-element PackedVector{UInt64, 5, Int64}:
 4
 5
 5
 6

julia> 3*v   # note the overflow in the last entry
3-element PackedVector{UInt64, 5, Int64}:
  12
  15
 -14
```

### `SmallBitSet`

The default `SmallBitSet` type `SmallBitSet{UInt64}` can hold integers
between `1` and `64`.
```julia
julia> s = SmallBitSet([1, 4, 7])
SmallBitSet{UInt64} with 3 elements:
  1
  4
  7

julia> t = SmallBitSet([3, 4, 5])
SmallBitSet{UInt64} with 3 elements:
  3
  4
  5

julia> union(s, t)
SmallBitSet{UInt64} with 5 elements:
  1
  3
  4
  5
  7

julia> push(s, 9)
SmallBitSet{UInt64} with 4 elements:
  1
  4
  7
  9

julia> filter(iseven, s)
SmallBitSet{UInt64} with 1 element:
  4
```
Smaller or larger sets are possible by choosing a different unsigned bit integer
as bitmask type, for example `UInt16` or `UInt128` or types like `UInt256` defined
by the package [BitIntegers.jl](https://github.com/rfourquet/BitIntegers.jl).
```julia
julia> using BitIntegers

julia> SmallBitSet{UInt256}(n for n in 1:256 if isodd(n) && isinteger(sqrt(n)))
SmallBitSet{UInt256} with 8 elements:
  1
  9
  25
  49
  81
  121
  169
  225
```

## Benchmarks

### `SmallVector`

The timings are for pairwise adding the elements of two `Vector`s,
each containing 1000 vectors with element type `T`.
For `Vector` and `SmallVector` the length of each pair of elements is **variable** and
chosen randomly between 1 and `N`. For `SVector{N,T}` (from StaticArrays.jl),
`Values{N,T}` (from StaticVectors.jl) and `Vec{N,T}` (from SIMD.jl) the vectors have
**fixed** length `N`.

| `(N, T)` | `Vector{T}` | `SmallVector{N,T}` | `SVector{N,T}` | `Values{N,T}` | `Vec{N,T}` |
| ---: | ---: | ---: | ---: | ---: | ---: |
| (8, Float64) | 66.682 μs | 3.341 μs | 3.452 μs | 3.197 μs | 3.046 μs |
| (8, Int64) | 48.642 μs | 4.962 μs | 3.196 μs | 4.551 μs | 2.954 μs |
| (16, Int32) | 49.449 μs | 3.866 μs | 3.284 μs | 3.623 μs | 3.757 μs |
| (32, Int16) | 55.027 μs | 5.046 μs | 4.212 μs | 3.618 μs | 3.548 μs |

### `PackedVector`

Here we compare a `PackedVector{UInt128, 4, Int8}` (that can hold 32 elements) to a `SmallVector{32, Int8}`
and to a `Vector{Int8}` with 30 elements.
The function `duplicate(v, i)` is equivalent to `insert(v, i+1, v[i])`.
For the operations listed in the table below we have chosen the mutating variant for `Vector`.

| operation | `Vector` | `SmallVector` | `PackedVector` |
| ---: | ---: | ---: | ---: |
| getindex | 2.902 ns | 2.647 ns | 3.167 ns |
| setindex | 2.638 ns | 5.279 ns | 6.861 ns |
| add | 12.419 ns | 2.375 ns | 4.222 ns |
| scalar_mul | 9.762 ns | 4.749 ns | 4.223 ns |
| push | 8.241 ns | 5.541 ns | 8.970 ns |
| pushfirst | 8.750 ns | 4.221 ns | 4.223 ns |
| pop | 8.600 ns | 6.000 ns | 4.933 ns |
| popfirst | 11.267 ns | 4.667 ns | 3.867 ns |
| insert | 12.928 ns | 24.804 ns | 7.328 ns |
| deleteat | 12.933 ns | 18.200 ns | 5.667 ns |
| duplicate | 13.546 ns | 20.845 ns | 4.486 ns |

### `SmallBitSet`

The timings are for taking the pairwise union of the elements of two `Vector`s,
each containing 1000 sets of the indicated type.
Each set contains up to `b` integers between 1 and `b = 8*sizeof(U)-1`.

| `U` | `Set{Int16}` | `BitSet` | `SmallBitSet` |
| ---: | ---: | ---: | ---: |
| UInt8 | 366.256 μs | 69.439 μs | 95.698 ns |
| UInt16 | 801.736 μs | 68.195 μs | 311.559 ns |
| UInt32 | 1.537 ms | 68.354 μs | 400.259 ns |
| UInt64 | 2.836 ms | 68.751 μs | 640.833 ns |
| UInt128 | 5.686 ms | 68.846 μs | 1.540 μs |
| UInt256 | 11.579 ms | 69.398 μs | 2.441 μs |
| UInt512 | 23.819 ms | 92.041 μs | 4.866 μs |

Versions: Julia v1.10.4,
Chairmarks v1.2.1,
SmallCollections v0.3.0,
StaticArrays v1.9.7,
StaticVectors v1.0.5,
SIMD v3.5.0,
BitIntegers v0.3.1

Computer: Intel Core i3-10110U CPU @ 2.10GHz with 8GB RAM

The benchmark code can be found in the `benchmark` directory.
