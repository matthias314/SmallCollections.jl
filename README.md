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
to a `SmallVector` or `SmallBitSet`.

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

Compared to `SmallVector`, a `PackedVector` often has faster `push` and `pop` operations,
with `pushfirst` and `popfirst` being particularly fast. Arithmetic operations are usually
slower unless `M` is the size of a hardware integer.
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
| (8, Float64) | 455.530 μs | 40.682 μs | 39.750 μs | 39.371 μs | 30.801 μs |
| (8, Int64) | 469.030 μs | 38.203 μs | 41.150 μs | 40.511 μs | 30.697 μs |
| (16, Int32) | 473.250 μs | 37.240 μs | 41.281 μs | 42.200 μs | 32.883 μs |
| (32, Int16) | 522.150 μs | 44.418 μs | 33.390 μs | 32.934 μs | 36.219 μs |

### `SmallBitSet`

The timings are for taking the pairwise union of the elements of two `Vector`s,
each containing 1000 sets of the indicated type.
Each set contains up to `b` integers between 1 and `b = 8*sizeof(U)-1`.

| `U` | `Set{Int16}` | `BitSet` | `SmallBitSet` |
| ---: | ---: | ---: | ---: |
| UInt8 | 3.047 ms | 684.980 μs | 975.095 ns |
| UInt16 | 7.484 ms | 685.170 μs | 3.147 μs |
| UInt32 | 14.712 ms | 681.080 μs | 4.208 μs |
| UInt64 | 27.161 ms | 682.310 μs | 7.116 μs |
| UInt128 | 55.051 ms | 682.950 μs | 15.583 μs |
| UInt256 | 112.145 ms | 693.970 μs | 25.316 μs |
| UInt512 | 224.086 ms | 923.660 μs | 50.205 μs |

Versions:
Julia v1.10.0,
StaticArrays v1.9.3,
StaticVectors v1.0.3,
SIMD 3.4.6,
BitIntegers v0.3.1

Computer: Intel Core i3-10110U CPU @ 2.10GHz with 8GB RAM

The benchmark code can be found in the `benchmark` directory.
