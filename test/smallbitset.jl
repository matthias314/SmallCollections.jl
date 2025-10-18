using SmallCollections: bitsize

unsigned_types = (UInt8, UInt64, UInt256, UInt440)

@testset "SmallBitSet" begin
    @test_inferred SmallBitSet([1,2,3]) SmallBitSet{UInt64}([1,2,3])
    for U in unsigned_types
        s = SmallBitSet{U}()
        @test_inferred isempty(s) true
        @test_inferred empty(s) SmallBitSet{U}()
        m = bitsize(U)
        @test_throws Exception SmallBitSet{U}([1, 2, 'x'])
        @test_throws Exception SmallBitSet{U}([1, 2, m+1])
        @test_throws Exception SmallBitSet{U}([0, 1, 2])
        t = Set{Int}(rand(1:m, rand(0:m)))
        s = @inferred SmallBitSet{U}(t)
        @test_inferred capacity(s) m
        @test_inferred isempty(s) isempty(t)
        @test_inferred length(s) == length(t) true
        @test_inferred s == t true
        @test_inferred copy(s) === s true
        @test_inferred s == s true
        v = collect(Float32, t)
        @test_inferred SmallBitSet{U}(v) s
        s3 = @inferred SmallBitSet{UInt512}(s)
        @test s3 == s
        @test_inferred hash(s) hash(t)
        @test_inferred fasthash(s) fasthash(s3)
        @test_inferred Set(s) t
    end
end

@testset "SmallBitSet first/min etc" begin
    for U in unsigned_types
        m = bitsize(U)
        t = Set{Int}(rand(1:m, rand(1:m)))
        s = @inferred SmallBitSet{U}(t)
        if isempty(t)
            @test_throws Exception minimum(s)
            @test_inferred minimum(s; init = m+1) minimum(t; init = m+1)
            @test_throws Exception maximum(s)
            @test_inferred maximum(s; init = 0) maximum(t; init = 0)
            @test_throws Exception extrema(s)
            @test_inferred extrema(s; init = (m+1, 0)) extrema(t; init = (m+1, 0))
        else
            @test_inferred first(s) minimum(t)
            @test_inferred minimum(s) minimum(t)
            @test_inferred last(s) maximum(t)
            @test_inferred maximum(s) maximum(t)
            @test_inferred extrema(s) extrema(t)
        end
    end
end

@testset "SmallBitSet in/subset" begin
    for U in unsigned_types
        m = bitsize(U)
        t = Set{Int}(rand(1:m, rand(0:m)))
        s = @inferred SmallBitSet{U}(t)
        for i in 1:m
            @test_inferred i in s i in t
            @test_inferred Int16(i) in s i in t
            @test_inferred Float64(i) in s i in t
        end
        @test_inferred 1.5 in s false
        @test_inferred 'x' in s false
        t2 = Set{Int}(rand(1:m, rand(0:2)))
        s2 = @inferred SmallBitSet{U}(t2)
        @test_inferred issubset(s2, s) issubset(t2, t)
        @test_inferred issubset(s2, t) issubset(t2, t)
        @test_inferred issubset(t2, s) issubset(t2, t)
        @test_inferred s2 ⊊ s t2 ⊊ t
        @test_inferred s2 ⊊ t t2 ⊊ t
        @test_inferred t2 ⊊ s t2 ⊊ t
    end
end

@testset "SmallBitSet push/pop etc" begin
    for U in unsigned_types
        m = bitsize(U)
        t = Set{Int}(rand(1:m, rand(0:m)))
        s = @inferred SmallBitSet{U}(t)
        i = rand(1:m)
        @test_inferred push(s, i) push!(copy(t), i) SmallBitSet{U}
        @test_inferred push(s, Float32(i)) push!(copy(t), i) SmallBitSet{U}
        @test_throws Exception push(s, 0)
        @test_throws Exception push(s, m+1)
        @test_throws Exception push(s, 'x')
        @test_inferred push(s, 3, 4, 5, 6) push!(copy(t), 3, 4, 5, 6) SmallBitSet{U}
        if !isempty(t)
            i = maximum(t)
            @test_inferred pop(s) (delete!(copy(t), i), i) Tuple{SmallBitSet{U}, Int}
            i = rand(t)
            @test_inferred pop(s, i) (delete!(copy(t), i), i) Tuple{SmallBitSet{U}, Int}
            @test_inferred pop(s, Float64(i)) (delete!(copy(t), i), i) Tuple{SmallBitSet{U}, Float64}
            @test_inferred pop(s, 0, -1) (s, -1)
            @test_throws KeyError pop(s, 0)
            @test_throws KeyError pop(s, 'x')
            @test_inferred delete(s, i) delete!(copy(t), i) SmallBitSet{U}
            @test_inferred delete(s, m+1) s
        end
        @test_inferred filter(isodd, s) filter(isodd, t) s
    end
end

@testset "SmallBitSet union etc" begin
    for U1 in unsigned_types, U2 in unsigned_types
        m1 = bitsize(U1)
        m2 = bitsize(U2)
        U = promote_type(U1, U2)
        t1 = Set{Int}(rand(1:m1, rand(0:m1)))
        s1 = @inferred SmallBitSet{U1}(t1)
        t2 = Set{Int}(rand(1:m2, rand(0:m2)))
        s2 = @inferred SmallBitSet{U2}(t2)
        @test_inferred union(s1, s2) union(t1, t2) SmallBitSet{U}
        @test_inferred intersect(s1, s2) intersect(t1, t2) SmallBitSet{U1}
        @test_inferred intersect(s1, t2) intersect(t1, t2) SmallBitSet{U1}
        @test_inferred setdiff(s1, s2) setdiff(t1, t2) SmallBitSet{U1}
        @test_inferred setdiff(s1, t2) setdiff(t1, t2) SmallBitSet{U1}
        @test_inferred symdiff(s1, s2) symdiff(t1, t2) SmallBitSet{U}
    end
end

@testset "SmallBitSet rand" begin
    for U in unsigned_types
        s = @inferred rand(SmallBitSet{U})
        @test s isa SmallBitSet{U}
    end
    s = @inferred rand(SmallBitSet)
    @test s isa SmallBitSet{UInt}
end

VERSION >= v"1.11" && @testset "SmallBitSet checkbounds" begin
    for V in [FixedVector{16,Int16}, MutableSmallVector{22,Int8}, PackedVector{UInt32,5,Int8}]
        v = rand(V)
        for s in [SmallBitSet(), SmallBitSet{UInt32}(1:3:length(v)), SmallBitSet{UInt128}((1, length(v)+1))]
            @test_inferred checkbounds(Bool, v, s) checkbounds(Bool, v, collect(s))
        end
    end
end
