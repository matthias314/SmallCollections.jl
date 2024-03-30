# SmallCollections.jl

This package provides the two immutable collections `SmallVector` and
`SmallBitSet` that don't allocate and are therefore faster than their
allocating counterparts `BitSet` and `Vector`. Unlike the static vectors
provided by [StaticArrays.jl](https://github.com/JuliaArrays/StaticArrays.jl)
and [StaticVectors.jl](https://github.com/chakravala/StaticVectors.jl),
the types defined by SmallCollections.jl have a variable size with a
user-defined limit.

If the package [BangBang.jl](https://github.com/JuliaFolds2/BangBang.jl)
is loaded, then many functions defined by this package are also available
in a `!!`-form. For example, both `push` and `push!!` add an element
to a `SmallVector` or `SmallBitSet`.

Below are [examples](#examples) and [benchmarks](#benchmarks). Also see
the [documentation](https://matthias314.github.io/SmallCollections.jl/stable/) for details.

## Examples

### `SmallVector`

A vector of type `SmallVector{N,T}` can hold up to `N` elements of type `T`.
Both `N` and `T` can be arbitrary. (However, if `T` is not a concrete type,
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
(Char[b,c], 'a')

julia> map(uppercase, u)
3-element SmallVector{6, Char}:
 'A': ASCII/Unicode U+0041 (category Lu: Letter, uppercase)
 'B': ASCII/Unicode U+0042 (category Lu: Letter, uppercase)
 'C': ASCII/Unicode U+0043 (category Lu: Letter, uppercase)
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
chosen randomly between 1 and `N`. For `SVector{N,T}` (from StaticArrays.jl) and
`Values{N,T}` (from StaticVectors.jl) the vectors have **fixed** length `N`.

| `(N, T)` | `Vector{T}` | `SmallVector{N,T}` | `SVector{N,T}` | `Values{N,T}` |
| ---: | ---: | ---: | ---: | ---: |
| (8, Float64) | 459.420 μs | 46.263 μs | 43.499 μs | 43.180 μs |
| (8, Int64) | 466.080 μs | 43.108 μs | 44.244 μs | 42.930 μs |
| (16, Int32) | 473.810 μs | 45.963 μs | 36.244 μs | 34.851 μs |
| (32, Int16) | 515.400 μs | 40.662 μs | 42.906 μs | 43.820 μs |

### `SmallBitSet`

The timings are for taking the pairwise union of the elements of two `Vector`s,
each containing 1000 sets of the indicated type.
Each set contains up to `b` integers between 1 and `b = 8*sizeof(U)-1`.

| `U` | `Set{Int16}` | `BitSet` | `SmallBitSet` |
| ---: | ---: | ---: | ---: |
| UInt8 | 3.123 ms | 700.450 μs | 1.069 μs |
| UInt16 | 7.677 ms | 700.280 μs | 3.112 μs |
| UInt32 | 15.395 ms | 704.350 μs | 4.223 μs |
| UInt64 | 28.707 ms | 708.350 μs | 6.946 μs |
| UInt128 | 57.626 ms | 694.000 μs | 15.243 μs |
| UInt256 | 115.954 ms | 717.110 μs | 25.693 μs |
| UInt512 | 239.506 ms | 940.300 μs | 49.812 μs |

Package versions:
StaticArrays v1.9.3,
StaticVectors v1.0.3,
BitIntegers v0.3.1

Computer: Intel Core i3-10110U CPU @ 2.10GHz with 8GB RAM

The benchmark code can be found in the `benchmark` directory.
