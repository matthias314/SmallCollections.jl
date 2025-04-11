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

@testset "SmallSet !!" begin
    s = SmallSet{8}(1:3)
    t = SmallSet{8}(3:5)
    x = 6
    @test_inferred push!!(s, x) push(s, x)
    @test_inferred pop!!(s) pop(s)
    @test_inferred delete!!(s, x) delete(s, x)
    @test_broken isdefined(BangBang, :filter!!)
    @test_inferred union!!(s, t) union(s, t)
    @test_inferred intersect!!(s, t) intersect(s, t)
    @test_inferred setdiff!!(s, t) setdiff(s, t)
    @test_inferred symdiff!!(s, t) symdiff(s, t)
end

@testset "MutableSmallSet !!" begin
    s = MutableSmallSet{8}(1:3)
    t = SmallSet{8}(3:5)
    x = 6
    u = copy(s)
    uu = @test_inferred push!!(u, x) push!(copy(s), x)
    @test uu === u
    u = copy(s)
    uu, y = @inferred pop!!(u)
    @test uu === u && y == pop!(copy(s))
    u = copy(s)
    uu = @test_inferred delete!!(u, x) delete!(copy(s), x)
    @test uu === u
    @test_broken isdefined(BangBang, :filter!!)
    u = copy(s)
    uu = @test_inferred union!!(u, t) union!(copy(s), t)
    @test uu === u
    u = copy(s)
    uu = @test_inferred intersect!!(u, t) intersect!(copy(s), t)
    @test uu === u
    u = copy(s)
    uu = @test_inferred setdiff!!(u, t) setdiff!(copy(s), t)
    @test uu === u
    u = copy(s)
    uu = @test_inferred symdiff!!(u, t) symdiff!(copy(s), t)
    @test uu === u
end

@testset "SmallDict !!" begin
    d = SmallDict{8}('a' => 1, 'b' => 2)
    e = SmallDict{8}('b' => 3, 'c' => 4)
    x = 'x' => -1
    @test_inferred push!!(d, x) push(d, x)
    @test_inferred pop!!(d) pop(d)
    @test_inferred delete!!(d, x) delete(d, x)
    @test_broken isdefined(BangBang, :filter!!)
    @test_inferred mergewith!!(+, d, e) mergewith(+, d, e)
end

@testset "MutableSmallDict !!" begin
    d = MutableSmallDict{8}('a' => 1, 'b' => 2)
    e = SmallDict{8}('b' => 3, 'c' => 4)
    x = 'x' => -1
    u = copy(d)
    uu = @test_inferred push!!(u, x) push!(copy(d), x)
    @test uu === u
    u = copy(d)
    uu, y = @inferred pop!!(u)
    @test uu === u && y == pop!(copy(d))
    u = copy(d)
    uu = @test_inferred delete!!(u, x) delete!(copy(d), x)
    @test uu === u
    @test_broken isdefined(BangBang, :filter!!)
    u = copy(d)
    uu = @test_inferred mergewith!!(+, u, e) mergewith!(+, copy(d), e)
    @test uu === u
end

@testset "FixedVector !!" begin
    v = FixedVector{6}(1:6)
    w = FixedVector{6}(4:9)
    x = -1
    i = 5
    @test_inferred setindex!!(v, x, i) setindex(v, x, i)
    @test_broken isdefined(BangBang, :map!!)
    @test_inferred add!!(v, w) v+w
end

@testset "MutableFixedVector !!" begin
    v = MutableFixedVector{6}(1:6)
    w = FixedVector{6}(4:9)
    x = -1
    i = 5
    u = copy(v)
    uu = @test_inferred setindex!!(u, x, i) setindex!(copy(u), x, i)
    @test uu === u
    @test_broken isdefined(BangBang, :map!!)
    u = copy(v)
    uu = @test_inferred add!!(u, w) v+w u
    @test uu === u
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

@testset "MutableSmallVector !!" begin
    v = MutableSmallVector{8}(1:6)
    w = SmallVector{8}(4:9)
    x = -1
    i = 5
    u = copy(v)
    uu = @test_inferred setindex!!(u, x, i) setindex!(copy(u), x, i)
    @test uu === u
    u = copy(v)
    uu = @test_inferred push!!(u, x) push!(copy(u), x)
    @test uu === u
    u = copy(v)
    uu = @test_inferred pushfirst!!(u, x) pushfirst!(copy(u), x)
    @test uu === u
    u = copy(v)
    uu, y = @inferred pop!!(u)
    @test uu === u && y == pop!(copy(v))
    u = copy(v)
    uu, y = @inferred popfirst!!(u)
    @test uu === u && y == popfirst!(copy(v))
    u = copy(v)
    @test_broken insert!!(u, i, x) == insert!(copy(u), i, x)
    u = copy(v)
    uu = @test_inferred deleteat!!(u, i) deleteat!(copy(v), i)
    @test uu === u
    u = copy(v)
    uu = @test_inferred append!!(u, (x,)) append!(copy(u), (x,))
    @test uu === u
    u = copy(v)
    @test_broken prepend!!(u, (x,)) == prepend!(copy(u), (x,))
    u = copy(v)
    @test_broken filter!!(isodd, u) == filter!(isodd, copy(z))
    @test_broken isdefined(BangBang, :map!!)
    u = copy(v)
    uu = @test_inferred add!!(u, w) v+w u
    @test uu === u
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
