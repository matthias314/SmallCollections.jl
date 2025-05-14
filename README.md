# SmallCollections.jl

`SmallCollections.jl` offers vector, set and dictionary types that can hold
any number of elements up to some (small) limit. Most of these types come
in a mutable and an immutable version. With bit type elements, the immutable
versions don't allocate. The mutable ones usually require bit type elements
for full functionality.
This approach leads to significant speed-ups compared to the standard types.
For example, the performance of the vector types `SmallVector` and `MutableSmallVector`
is close to that to `SVector` and `MVector` from
[`StaticArrays.jl`](https://github.com/JuliaArrays/StaticArrays.jl).
The most extreme performance gain is with `SmallBitSet`, which can be 100x faster than `BitSet`.
(The exact speed-ups depend much on your processor.)

Below we present the major new types and also the submodule `Combinatorics`,
which contains a few functions related to enumerative combinatorics.
Compared to the analogous functions in
[Combinatorics.jl](https://github.com/JuliaMath/Combinatorics.jl)
and [Combinat.jl](https://github.com/jmichel7/Combinat.jl),
they are at least 8x faster.

The full documentation  for `SmallCollections` is available
[here](https://matthias314.github.io/SmallCollections.jl/).

## New types

### `(Mutable)SmallVector` and `(Mutable)FixedVector`

The types
[`SmallVector{N,T}`](https://matthias314.github.io/SmallCollections.jl/stable/capacityvector/#SmallCollections.SmallVector)
and
[`MutableSmallVector{N,T}`](https://matthias314.github.io/SmallCollections.jl/stable/capacityvector/#SmallCollections.MutableSmallVector)
can hold up to `N` elements of type `T`.
In many cases they are almost as fast as fixed-length vectors.
Internally, these types use fixed-length vectors and fill the unused elements with some
[`default`](https://matthias314.github.io/SmallCollections.jl/stable/nonexported/#SmallCollections.default)
value. The underlying types
[`FixedVector{N,T}`](https://matthias314.github.io/SmallCollections.jl/stable/fixedvector/#SmallCollections.FixedVector)
and
[`MutableFixedVector{N,T}`](https://matthias314.github.io/SmallCollections.jl/stable/fixedvector/#SmallCollections.MutableFixedVector)
store exactly `N` elements of type `T`.
Up to a few implementation details, they are analogous to `SVector` and `MVector`.
(However, broadcasting with assignment is currently much faster for `MutableSmallVector` than for `MVector`.)

<details>
<summary>Benchmarks for <code>SmallVector</code> and <code>MutableSmallVector</code></summary>

The timings are for **1000** operations of the given type on vectors having between 1 and 31 elements
(or exactly 32 elements for fixed-length vectors). If possible, mutating operations were used.

| `N = 32`, `T = Int16` | `v + w` | `v .+= w` |`sum` | `push(!)` | `count(>(c), v)` |
| --- | --- | --- | --- | --- | --- |
| `Vector{T}` | 44.827 μs | 21.258 μs | 7.612 μs | 5.003 μs | 11.241 μs |
| `MVector{N,T}` | 5.606 μs | 19.478 μs | 2.301 μs | 9.764 μs | 2.679 μs |
| **`MutableSmallVector{N,T}`** | 3.880 μs | 5.258 μs | 3.233 μs | 3.084 μs | 2.131 μs |
| `SVector{N,T}` | 2.012 μs | n/a | 1.395 μs | 2.053 μs | 1.185 μs |
| **`SmallVector{N,T}`** | 2.392 μs | n/a | 2.660 μs | 6.437 μs | 1.796 μs |

Notes: `sum` for `SVector` and `MVector` returns an `Int16` instead of `Int`. `SmallCollections`
has a separate function `sum_fast` for this. Addition allocates for `Vector`. To avoid this for
`MVector`, the result was transformed to `SVector`. `push!` for `MVector` and `push` for `SVector`
are not directly comparable to the others because they change the type of the returned vector,
which leads to type instabilities in cases like loops.

For the benchmark code see the file `benchmark/benchmark_vec.jl` in the repository.

</details>

How broadcasting or functions like
[`map`](https://matthias314.github.io/SmallCollections.jl/stable/capacityvector/#Base.map)
or
[`any`](https://matthias314.github.io/SmallCollections.jl/stable/capacityvector/#Base.any-Tuple{Function,%20AbstractSmallVector})
deal with default values for a `(Mutable)SmallVector` is governed by a trait called
[`MapStyle`](https://matthias314.github.io/SmallCollections.jl/stable/nonexported/#SmallCollections.MapStyle).
Except for broadcasting one can override the automatically chosen style.

### `PackedVector`

A
[`PackedVector{U,M,T}`](https://matthias314.github.io/SmallCollections.jl/stable/capacityvector/#SmallCollections.PackedVector)
uses the unsigned integer type `U` to store integers with `M` bits,
which to the outside appear as having integer type `T`. For example, a `PackedVector{UInt128,5,Int8}`
can store `25` (`128÷5`) signed integers with `5` bits. When retrieving them, they are of type `Int8`.
Indexing and algebraic operations are usually slower for `PackedVector` than for `SmallVector`,
while `push`/`pushfirst` and `pop`/`popfirst` may be faster.

### `(Mutable)SmallSet` and `SmallBitSet`

The types
[`SmallSet{N,T}`](https://matthias314.github.io/SmallCollections.jl/stable/smallset/#SmallCollections.SmallSet)
and
[`MutableSmallSet{N,T}`](https://matthias314.github.io/SmallCollections.jl/stable/smallset/#SmallCollections.MutableSmallSet)
 can hold up to `N` elements of type `T`. The type
[`SmallBitSet{U}`](https://matthias314.github.io/SmallCollections.jl/stable/smallbitset/#SmallCollections.SmallBitSet)
can hold integers between `1` and `M` where `M` is the bit size of the unsigned integer type `U`
(taken to be `UInt` if omitted).
For small integers, `MutableSmallSet` is as fast (or even faster than) `BitSet`.
`SmallBitSet` can be up to 100x faster than `BitSet`.

<details>
<summary>Benchmarks for <code>SmallSet</code>, <code>MutableSmallSet</code> and <code>SmallBitSet</code></summary>

The timings are for **1000** operations of the given type on sets having between 1 and 8 elements.
If possible, mutating operations were used.
Note that while a `BitSet` can hold arbitrarily many elements, the timings for `MutableSmallSet`
wouldn't change if the elements were drawn from `Int16` without restrictions.

| `N = 16`, `T = Int16` | `push(!)` | `intersect(!)` | `issubset` | `in` |
| --- | --- | --- | --- | --- |
| `Set{T}` | 14.817 μs | 87.199 μs | 77.615 μs | 4.586 μs |
| **`MutableSmallSet{N,T}`** | 9.532 μs | 14.244 μs | 4.392 μs | 1.167 μs |
| **`SmallSet{N,T}`** | 13.645 μs | 17.705 μs | 8.806 μs | 2.182 μs |
| `BitSet` | 16.184 μs | 21.225 μs | 7.518 μs | 1.983 μs |
| **`SmallBitSet{UInt16}`** | 1.377 μs | 36.318 **ns** | 56.222 **ns** | 1.094 μs |

For the benchmark code see the file `benchmark/benchmark_set.jl` in the repository.

</details>

### `(Mutable)SmallDict`

The types
[`SmallDict{N,K,V}`](https://matthias314.github.io/SmallCollections.jl/stable/smalldict/#SmallCollections.SmallDict)
and
[`MutableSmallDict{N,K,V}`](https://matthias314.github.io/SmallCollections.jl/stable/smalldict/#SmallCollections.MutableSmallDict)
can hold up to `N` entries with key type `K` and value type `V`.

Operations for `MutableSmallDict` are typically faster than for `Dict`.
For `SmallDict` this holds often, but not always.
Since keys and values are stored as small vectors, inverse lookup with
[`invget`](https://matthias314.github.io/SmallCollections.jl/stable/smalldict/#SmallCollections.invget)
is as fast as regular lookup.

<details>
<summary>Benchmarks for <code>SmallDict</code> and <code>MutableSmallDict</code></summary>

The timings are for **1000** operations of the given type on dictionaries created with 30
randomly chosen key-value pairs. If possible, mutating operations were used.

| `N = 32`, `K = V = Int8` | `getindex` | `invget` | `setindex(!)` | `pop(!)` | `iterate` |
| --- | --- | --- | --- | --- | --- |
| `Dict{Int8,Int8}` | 10.739 μs | n/a | 27.604 μs | 19.932 μs | 406.180 μs |
| **`MutableSmallDict{32,Int8,Int8}`** | 1.853 μs | 2.650 μs | 8.762 μs | 7.460 μs | 18.653 μs |
| **`SmallDict{32,Int8,Int8}`** | 1.864 μs | 1.495 μs | 9.516 μs | 17.761 μs | 16.514 μs |

For the benchmark code see the file `benchmark/benchmark_dict.jl` in the repository.

</details>

## Combinatorics

The submodule
[`Combinatorics`](https://matthias314.github.io/SmallCollections.jl/stable/combinatorics/)
contains functions for enumerative combinatorics
that are based on types provided by `SmallCollections.jl`. Currently this module
is more of a proof-of-concept; it may be turned into a separate package in the future.
Here are two example benchmarks (done with Julia 1.11.5,
[Combinatorics.jl](https://github.com/JuliaMath/Combinatorics.jl) 1.0.3
and [Combinat.jl](https://github.com/jmichel7/Combinat.jl) 0.1.3).
On a different computer, GAP and Sage were 2-3 orders of magnitude slower.

### Permutations

Loop over all permutations of `1:9` and add up the image of `1` under each permutation.
The iterator returned by
[`permutations`](https://matthias314.github.io/SmallCollections.jl/stable/combinatorics/#SmallCollections.Combinatorics.permutations)
 yields each permutation as a `SmallVector{16,Int8}`.
```julia
julia> n = 9; @b sum(p[1] for p in Combinatorics.permutations($n))  # SmallCollections.jl
1.909 ms  # 688.006 μs with @inbounds(p[1])

julia> n = 9; @b sum(p[1] for p in permutations(1:$n))  # Combinatorics.jl
14.535 s (725763 allocs: 44.297 MiB, 0.04% gc time, without a warmup)

julia> n = 9; @b sum(p[1] for p in Combinat.Permutations($n))  # Combinat.jl
12.473 ms (725762 allocs: 44.297 MiB, 5.38% gc time)
```

### Subsets

Loop over all `10`-element subsets of `1:20` and add up the sum of the elements of each subset.
The iterator returned by
[`subsets`](https://matthias314.github.io/SmallCollections.jl/stable/combinatorics/#SmallCollections.Combinatorics.subsets-Tuple{Integer,%20Integer})
yields each subset as a `SmallBitSet`.
```julia
julia> n = 20; k = 10; @b sum(sum, Combinatorics.subsets($n, $k))  # SmallCollections.jl
1.121 ms

julia> n = 20; k = 10; @b sum(sum, combinations(1:$n, $k))  # Combinatorics.jl
9.484 ms (369514 allocs: 25.373 MiB, 7.09% gc time)

julia> n = 20; k = 10; @b sum(sum, Combinat.Combinations(1:$n, $k))  # Combinat.jl
9.605 ms (369521 allocs: 25.373 MiB, 7.04% gc time)
```
