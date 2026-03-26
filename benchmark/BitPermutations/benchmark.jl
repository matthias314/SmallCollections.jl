using BitPermutations, SmallCollections, Chairmarks
using Base: Fix2
using Random: randperm

@info first(Sys.cpu_info()).model

@inline inbounds_invreplace(s, v) = @inbounds invreplace(s, v)

@info "bitpermute / invreplace"
for U in [UInt8, UInt16, UInt32, UInt64, UInt128]
    print("$U\t")
    N = bitsize(U)
    v = randperm(N)
    p1 = BitPermutation{U}(v)
    p2 = FixedVector{N,UInt8}(v)
    s = rand(SmallBitSet{U})
    x = bits(s)
    @assert bitpermute(x, p1) == bits(inbounds_invreplace(s, p2))
    display(@b bitpermute($x, $p1), inbounds_invreplace($s, $p2))
end

@info "bitpermute! / map bitpermute / map invreplace"
M = 1000
for U in [UInt8, UInt16, UInt32, UInt64, UInt128]
    print("$U\t")
    N = bitsize(U)
    v = randperm(N)
    p1 = BitPermutation{U}(v)
    p2 = FixedVector{N,UInt8}(v)
    q2 = rand(SmallBitSet{U}, M)
    q1 = map(bits, q2)
    @assert map(Fix2(bitpermute, p1), q1) == map(bits∘Fix2(inbounds_invreplace, p2), q2)
    display(@b bitpermute!($q1, $p1), map!(Fix2(bitpermute, $p1), $q1, $q1), map!(Fix2(inbounds_invreplace, $p2), $q2, $q2))
end
