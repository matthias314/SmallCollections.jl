using BangBang

@testset "SmallBitSet !!" begin
    s = SmallBitSet(1:3)
    t = SmallBitSet(3:5)
    x = 6
    @test_inferred push!!(s, x) push(s, x)
    @test_inferred pop!!(s) pop(s)
    @test_inferred delete!!(s, x) delete(s, x)
    @test_broken filter!!(isodd, s) == filter(isodd, s)
    @test_inferred union!!(s, t) union(s, t)
    @test_inferred intersect!!(s, t) intersect(s, t)
    @test_inferred setdiff!!(s, t) setdiff(s, t)
    @test_inferred symdiff!!(s, t) symdiff(s, t)
end

@testset "SmallVector !!" begin
    v = SmallVector{8}(1:6)
    w = SmallVector{8}(4:9)
    x = -1
    i = 5
    @test_inferred setindex!!(v, x, i) setindex(v, x, i)
    @test_inferred push!!(v, x) push(v, x)
    @test_inferred pushfirst!!(v, x) pushfirst(v, x)
    @test_inferred pop!!(v) pop(v)
    @test_inferred popfirst!!(v) popfirst(v)
    @test_broken insert!!(v, i, x) == insert(v, i, x)
    @test_inferred deleteat!!(v, i) deleteat(v, i)
    @test_inferred append!!(v, (x,)) append(v, (x,))
    @test_broken prepend!!(v, (x,)) == prepend(v, (x,))
    @test_broken filter!!(isodd, v) == filter(isodd, v)
    @test_broken isdefined(BangBang, :map!!)
    @test_inferred add!!(v, w) v+w
end

@testset "PackedVector !!" begin
    v = PackedVector{UInt64,8,Int8}(1:6)
    w = PackedVector{UInt64,8,Int8}(4:9)
    x = -1
    i = 5
    @test_inferred setindex!!(v, x, i) setindex(v, x, i)
    @test_inferred push!!(v, x) push(v, x)
    @test_inferred pushfirst!!(v, x) pushfirst(v, x)
    @test_inferred pop!!(v) pop(v)
    @test_inferred popfirst!!(v) popfirst(v)
    @test_broken insert!!(v, i, x) == insert(v, i, x)
    @test_inferred deleteat!!(v, i) deleteat(v, i)
    @test_inferred append!!(v, (x,)) append(v, (x,))
    @test_broken prepend!!(v, (x,)) == prepend(v, (x,))
    @test_broken filter!!(isodd, v) == filter(isodd, v)
    @test_broken isdefined(BangBang, :map!!)
    @test_inferred add!!(v, w) v+w
end
