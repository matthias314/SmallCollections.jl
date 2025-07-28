# SmallCollections.jl

This package offers vector, set and dictionary types that can hold
any number of elements up to some (small) limit. Most of these types come
in a mutable and an immutable version. With bit type elements, the immutable
versions don't allocate. The mutable ones usually require bit type elements
for full functionality.
This approach leads to significant speed-ups compared to the standard types.
For example, the performance of the vector types `SmallVector` and `MutableSmallVector`
is close to that to `SVector` and `MVector` from
[StaticArrays.jl](https://github.com/JuliaArrays/StaticArrays.jl).
The most extreme performance gain is with `SmallBitSet`, which can be 100x faster than `BitSet`.
(The exact speed-ups depend much on your processor.)

**Note:** The former submodule `Combinatorics` has been turned into the separate package
[SmallCombinatorics.jl](https://github.com/matthias314/SmallCombinatorics.jl).

The full documentation for `SmallCollections` is available
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
<summary>Benchmarks for <code>(Mutable)SmallVector</code> and <code>(Mutable)FixedVector</code></summary>

The timings are for **1000** operations of the given type on vectors having between 1 and 31 elements
(or exactly 32 elements for fixed-length vectors). If possible, mutating operations were used.

| `N = 32`, `T = Int16` | `v + w` | `v .+= w` |`sum` | `push(!)` | `count(>(c), v)` |
| --- | --- | --- | --- | --- | --- |
| `Vector{T}` | 45.893 μs | 20.441 μs | 8.403 μs | 5.104 μs | 9.860 μs |
| `MVector{N,T}` | 5.770 μs | 19.196 μs | 2.370 μs | 9.866 μs | 2.801 μs |
| **`MutableFixedVector{N,T}`** | 2.932 μs | 4.494 μs | 3.086 μs | n/a | 1.492 μs |
| **`MutableSmallVector{N,T}`** | 3.276 μs | 4.975 μs | 2.977 μs | 3.154 μs | 1.871 μs |
| `SVector{N,T}` | 1.979 μs | n/a | 1.396 μs | 1.988 μs | 1.218 μs |
| **`FixedVector{N,T}`** | 2.054 μs | n/a | 2.661 μs | n/a | 1.217 μs |
| **`SmallVector{N,T}`** | 2.517 μs | n/a | 2.661 μs | 6.408 μs | 1.617 μs |

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
| `Set{T}` | 15.669 μs | 88.370 μs | 23.482 μs | 1.610 μs |
| `MutableSmallSet{N,T}` | 8.269 μs | 14.422 μs | 4.357 μs | 1.658 μs |
| `SmallSet{N,T}` | 12.688 μs | 15.011 μs | 10.234 μs | 2.122 μs |
| `BitSet` | 17.481 μs | 23.403 μs | 7.407 μs | 1.836 μs |
| `SmallBitSet{UInt16}` | 1.377 μs | 31.240 **ns** | 56.226 **ns** | 1.067 μs |

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
should be as fast as regular lookup.

<details>
<summary>Benchmarks for <code>SmallDict</code> and <code>MutableSmallDict</code></summary>

The timings are for **1000** operations of the given type on dictionaries created with 30
randomly chosen key-value pairs. If possible, mutating operations were used.

| `N = 32`, `K = V = Int8` | `getindex` | `invget` | `setindex(!)` | `pop(!)` | `iterate` |
| --- | --- | --- | --- | --- | --- |
| `Dict{K,V}` | 10.799 μs | n/a | 26.992 μs | 18.931 μs | 404.342 μs |
| `MutableSmallDict{N,K,V}` | 4.273 μs | 5.325 μs | 8.900 μs | 7.213 μs | 17.104 μs |
| `SmallDict{N,K,V}` | 1.856 μs | 8.775 μs | 9.823 | 20.368 μs | 15.840 μs |

Note: For `SmallDict`, `invget` appears much slower than `getindex` in this benchmark.
(This started with commit [#8f6b498](https://github.com/matthias314/SmallCollections.jl/commit/8f6b4987dfeca26297a4d98a0a5b068c6ae74886).)
I don't know the reason for this. The code shown by `@code_native` for these two functions looks identical,
and the timings for a single call to `getindex` and `invget` are identical, too.

For the benchmark code see the file `benchmark/benchmark_dict.jl` in the repository.

</details>
