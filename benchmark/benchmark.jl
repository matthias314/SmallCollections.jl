using BenchmarkTools

prettytime(t) = BenchmarkTools.prettytime(t*10e9)

using SmallCollections, StaticArrays, StaticVectors, SIMD, BitIntegers

const n = 1000

s = """
### `SmallVector`

The timings are for pairwise adding the elements of two `Vector`s,
each containing $n vectors with element type `T`.
For `Vector` and `SmallVector` the length of each pair of elements is **variable** and
chosen randomly between 1 and `N`. For `SVector{N,T}` (from StaticArrays.jl),
`Values{N,T}` (from StaticVectors.jl) and `Vec{N,T}` (from SIMD.jl) the vectors have
**fixed** length `N`.

| `(N, T)` | `Vector{T}` | `SmallVector{N,T}` | `SVector{N,T}` | `Values{N,T}` | `Vec{N,T}` |
| ---: | ---: | ---: | ---: | ---: | ---: |
"""
for (N, T) in [(8, Float64), (8, Int64), (16, Int32), (32, Int16)]
    # @show N T
    v1 = [rand(T, rand(1:N)) for _ in 1:n]
    w1 = [rand(T, length(v1[i])) for i in 1:n]
    v2 = map(SmallVector{N,T}, v1)
    w2 = map(SmallVector{N,T}, w1)
    v3 = [Values{N,T}(rand(T, N)) for _ in 1:n]
    w3 = [Values{N,T}(rand(T, N)) for _ in 1:n]
    v4 = map(SVector{N,T}, v3)
    w4 = map(SVector{N,T}, w3)
    v5 = map(x -> Vec{N,T}(Tuple(x)), v3)
    w5 = map(x -> Vec{N,T}(Tuple(x)), w3)

    # @show typeof(v1) typeof(v2) typeof(v3) typeof(v4) typeof(v5)

    t1 = prettytime(@belapsed map(+, $v1, $w1))
    t2 = prettytime(@belapsed map(+, $v2, $w2))
    t3 = prettytime(@belapsed map(+, $v3, $w3))
    t4 = prettytime(@belapsed map(+, $v4, $w4))
    t5 = prettytime(@belapsed map(+, $v5, $w5))
    s0 = "| ($N, $T) | $t1 | $t2 | $t4 | $t3 | $t5 |\n"

    print(stderr, s0)
    global s *= s0
end

s *= """

### `SmallBitSet`

The timings are for taking the pairwise union of the elements of two `Vector`s,
each containing $n sets of the indicated type.
Each set contains up to `b` integers between 1 and `b = 8*sizeof(U)-1`.

| `U` | `Set{Int16}` | `BitSet` | `SmallBitSet` |
| ---: | ---: | ---: | ---: |
"""
for U in (UInt8, UInt16, UInt32, UInt64, UInt128, UInt256, UInt512)
    b = 8*sizeof(U)-1
    s1 = [Set{Int16}(rand(1:b) for _ in 1:b) for _ in 1:n]
    u1 = [Set{Int16}(rand(1:b) for _ in 1:b) for _ in 1:n]
    s2 = map(BitSet, s1)
    u2 = map(BitSet, u1)
    s3 = map(SmallBitSet{U}, s1)
    u3 = map(SmallBitSet{U}, u1)

    # @show typeof(s1) typeof(s2) typeof(s3)

    t1 = prettytime(@belapsed map(union, $s1, $u1))
    t2 = prettytime(@belapsed map(union, $s2, $u2))
    t3 = prettytime(@belapsed map(union, $s3, $u3))
    s0 = "| $U | $t1 | $t2 | $t3 |\n"

    print(stderr, s0)
    global s *= s0
end

s *= """

Versions: Julia v$VERSION,
"""

w = map([SmallCollections, StaticArrays, StaticVectors, SIMD, BitIntegers]) do M
    v = pkgversion(M)
    "$M: v$v"
end

s *= join(w, ",\n")

println(s)
