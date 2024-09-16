using Chairmarks

function pretty_time(sample)
    io = IOBuffer()
    Chairmarks.print_time(io, sample)
    String(take!(io))
end

macro bstr(ex...)
    esc(:(pretty_time((@b $(ex...)).time)))
end

using SmallCollections, StaticArrays, StaticVectors, SIMD, BitIntegers, BangBang

const n = 1000

s = """
## Benchmarks

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

    t1 = @bstr map(+, $v1, $w1)
    t2 = @bstr map(+, $v2, $w2)
    t3 = @bstr map(+, $v3, $w3)
    t4 = @bstr map(+, $v4, $w4)
    t5 = @bstr map(+, $v5, $w5)
    s0 = "| ($N, $T) | $t1 | $t2 | $t4 | $t3 | $t5 |\n"

    print(stderr, s0)
    global s *= s0
end

mul!!(v::Vector, x) = v .*= x
mul!!(v::AbstractCapacityVector, x) = x * v

insert!!(v::Vector, i, x) = insert!(v, i, x)
insert!!(v::AbstractCapacityVector, i, x) = SmallCollections.insert(v, i, x)

@inline function duplicate!!(v::Vector, i)
    @boundscheck checkbounds(v, i)
    @inbounds insert!(v, i+1, v[i])
end

duplicate!!(v::AbstractCapacityVector, i) = duplicate(v, i)

let
    m = 30
    U = UInt128
    M = 4
    N = SmallCollections.bitsize(U) ÷ M
    r = Int8(-2^(M-1)):Int8(2^(M-1)-1)
    v1 = rand(r, m)
    w1 = rand(r, m)
    v2 = PackedVector{U,M,Int8}(v1)
    w2 = PackedVector{U,M,Int8}(w1)
    v3 = SmallVector{N,Int8}(v1)
    w3 = SmallVector{N,Int8}(w1)
    types = [Vector{Int8}, SmallVector{N,Int8}, PackedVector{U,M,Int8}]

    global s *= """

### `PackedVector`

Here we compare a `$(types[3])` (that can hold $N elements) to a `$(types[2])`
and to a `$(types[1])` with $m elements.
The function `duplicate(v, i)` is equivalent to `insert(v, i+1, v[i])`.
For the operations listed in the table below we have chosen the mutating variant for `Vector`.

"""

    c = Int8(3)
    i = m ÷ 2
    t = Dict{Any,String}()
    for (v, w) in [(v1, w1), (v2, w2), (v3, w3)]
        T = typeof(v)
        println(stderr, T)
        t[T, :getindex] = @bstr $v[$i]
        t[T, :setindex] = @bstr copy(v) setindex!!(_, $c, $i)
        t[T, :add] = @bstr copy(v) add!!(_, $w)
        t[T, :scalar_mul] = @bstr copy(v) mul!!(_, $c)
        t[T, :pushfirst] = @bstr copy(v) pushfirst!!(_, $c)
        t[T, :push] = @bstr copy(v) push!!(_, $c)
        t[T, :popfirst] = @bstr copy(v) popfirst!!(_) evals = i
        t[T, :pop] = @bstr copy(v) pop!!(_) evals = i
        t[T, :insert] = @bstr copy(v) insert!!(_, $i, $c)
        t[T, :deleteat] = @bstr copy(v) deleteat!!(_, $i) evals = i
        t[T, :duplicate] = @bstr copy(v) duplicate!!(_, $i)
    end

    global s *= """
    | operation | `Vector` | `SmallVector` | `PackedVector` |
    | ---: | ---: | ---: | ---: |
    """

    for f in [:getindex, :setindex, :add, :scalar_mul, :push, :pushfirst, :pop, :popfirst, :insert, :deleteat, :duplicate]
        global s *= "| $f | " * join((t[T, f] for T in types), " | ") * " |\n"
    end

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

    t1 = @bstr map(union, $s1, $u1)
    t2 = @bstr map(union, $s2, $u2)
    t3 = @bstr map(union, $s3, $u3)
    s0 = "| $U | $t1 | $t2 | $t3 |\n"

    print(stderr, s0)
    global s *= s0
end

s *= """

Versions: Julia v$VERSION,
"""

w = map([Chairmarks, SmallCollections, StaticArrays, StaticVectors, SIMD, BitIntegers]) do M
    v = pkgversion(M)
    "$M v$v"
end

s *= join(w, ",\n")

println(s)
