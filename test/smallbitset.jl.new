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
            @test_throws Exception pop(s, 0)
            @test_throws Exception pop(s, 'x')
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

@testset "subsets(n,k)" begin
    for n in [-1, 0, 1, 2, 10], k in [-1, 0, 1, n-1, n, n+1]
        if n < 0
            @test_throws Exception subsets(n, k)
            continue
        end
        ss = @inferred subsets(n, k)
        if 0 <= k <= n
            @test_inferred length(ss) binomial(n, k)
        else
            @test_inferred length(ss) 0
        end
        @test eltype(ss) == SmallBitSet{UInt}
        ssv = @inferred collect(ss)
        @test length(ssv) == length(ss) == length(unique(ssv))
        length(ss) == 0 && continue
        @test unique(map(length, ssv)) == [k]
    end

    for U in unsigned_types, a in map(SmallBitSet{U}, [Int[], [3], [bitsize(U)-3, bitsize(U)], [2, 4, 6, 7]])
        n = length(a)
        for k in [-1, 0, 1, n-1, n, n+1]
            ss = @inferred subsets(a, k)
            if 0 <= k <= n
                @test_inferred length(ss) binomial(n, k)
            else
                @test_inferred length(ss) 0
            end
            @test eltype(ss) == SmallBitSet{U}
            ssv = @inferred collect(ss)
            @test length(ssv) == length(ss) == length(unique(ssv))
            length(ss) == 0 && continue
            @test unique(map(length, ssv)) == [k]
        end
    end
end

@testset "subsets(n)" begin
    for n in [-1, 0, 1, 2, 10]
        if n < 0
            @test_throws Exception subsets(n)
            continue
        end
        ss = subsets(n)
        @test_inferred length(ss) 2^n
        @test eltype(ss) == SmallBitSet{UInt}
        ssv = @inferred collect(ss)
        @test length(ssv) == length(ss) == length(unique(ssv))
        @test_throws BoundsError ss[firstindex(ss)-1]
        @test_throws BoundsError ss[lastindex(ss)+1]
    end

    for U in unsigned_types, a in map(SmallBitSet{U}, [Int[], [3], [bitsize(U)-3, bitsize(U)], [2, 4, 6, 7]])
        ss = subsets(a)
        @test_inferred length(ss) 2^length(a)
        @test eltype(ss) == SmallBitSet{U}
        ssv = @inferred collect(ss)
        @test length(ssv) == length(ss) == length(unique(ssv))
        @test_throws BoundsError ss[firstindex(ss)-1]
        @test_throws BoundsError ss[lastindex(ss)+1]
    end
end

@testset "shuffles" begin
    function test_shuffles(ks)
        N = length(ks)
        sh = @inferred shuffles(ks...)
        a = SmallBitSet(1:sum(ks; init = 0))
        @test @inferred(length(sh)) == factorial(big(sum(ks; init = 0))) ÷ prod(map(factorial∘big, ks); init = 1)
        @test @inferred(eltype(sh)) == Tuple{NTuple{N, SmallBitSet{UInt}}, Bool}
        @test all(map(length, t) == ks && s isa Bool &&
            (isempty(t) ? isempty(a) : (union(t...) == a)) &&
            shuffle_signbit(t...) == s for (t, s) in sh)
        @test allunique(sh)
    end

    function test_shuffles(a::S, ks::NTuple{N,Int}) where {S <: SmallBitSet, N}
        test_shuffles(ks)
        sh = @inferred shuffles(a, ks...)
        @test @inferred(length(sh)) == factorial(big(sum(ks; init = 0))) ÷ prod(map(factorial∘big, ks); init = 1)
        @test @inferred(eltype(sh)) == Tuple{NTuple{N, S}, Bool}
        @test all(t isa NTuple{N, S} && s isa Bool &&
            map(length, t) == ks &&
            (isempty(t) ? isempty(a) : (union(t...) == a)) &&
            shuffle_signbit(t...) == s for (t, s) in sh)
        @test allunique(sh)
    end

    for U in unsigned_types, (v, ks) in [(Int[], ()), (Int[], (0,)), (Int[], (0, 0)),
                (bitsize(U)-4:2:bitsize(U), (1, 1, 1)),
                (3:2:11, (5,)), (3:2:11, (2, 3)),  (3:2:11, (0, 2, 3)),  (3:2:11, (2, 0, 3)),  (3:2:11, (2, 3, 0)),
                (20:2:38, (2, 3, 2, 3)), (20:2:38, (1, 4, 0, 2, 3))]
        maximum(v; init = 0) <= bitsize(U) || continue
        a = SmallBitSet{U}(v)
        test_shuffles(a, ks)
    end

    @test_throws Exception shuffles(-1, 2)
    @test_throws Exception shuffles(bitsize(UInt)-1, 2)
    for U in unsigned_types
        @test_throws Exception shuffles(SmallBitSet{U}(2:2:6))
        @test_throws Exception shuffles(SmallBitSet{U}(2:2:6), -1, 2, 2)
        @test_throws Exception shuffles(SmallBitSet{U}(2:2:6), 3, 4)
        @test (shuffles(SmallBitSet{U}(1:bitsize(U)), bitsize(U)-2, 2); true)
    end

    # check that unsafe_lshr in iterate for Shuffles is safe
    @test collect(subsets(bitsize(UInt), 1)) == [SmallBitSet((k,)) for k in 1:bitsize(UInt)]
end

@testset "compositions" begin
    function test_compositions(ks)
        N = length(ks)
        sh = @inferred compositions(ks...)
        a = SmallBitSet(1:sum(ks; init = 0))
        @test @inferred(length(sh)) == factorial(big(sum(ks; init = 0))) ÷ prod(map(factorial∘big, ks); init = 1)
        @test @inferred(eltype(sh)) == NTuple{N, SmallBitSet{UInt}}
        @test all(map(length, t) == ks && (isempty(t) ? isempty(a) : (union(t...) == a)) for t in sh)
        @test allunique(sh)
    end

    function test_compositions(a::S, ks::NTuple{N,Int}) where {S <: SmallBitSet, N}
        test_compositions(ks)
        sh = @inferred compositions(a, ks...)
        @test @inferred(length(sh)) == factorial(big(sum(ks; init = 0))) ÷ prod(map(factorial∘big, ks); init = 1)
        @test @inferred(eltype(sh)) == NTuple{N, S}
        @test all(t isa NTuple{N, S} && map(length, t) == ks && (isempty(t) ? isempty(a) : (union(t...) == a)) for t in sh)
        @test allunique(sh)
    end

    for U in unsigned_types, (v, ks) in [(Int[], ()), (Int[], (0,)), (Int[], (0, 0)),
                (bitsize(U)-4:2:bitsize(U), (1, 1, 1)),
                (3:2:11, (5,)), (3:2:11, (2, 3)),  (3:2:11, (0, 2, 3)),  (3:2:11, (2, 0, 3)),  (3:2:11, (2, 3, 0)),
                (20:2:38, (2, 3, 2, 3)), (20:2:38, (1, 4, 0, 2, 3))]
        maximum(v; init = 0) <= bitsize(U) || continue
        a = SmallBitSet{U}(v)
        test_compositions(a, ks)
    end

    @test_throws Exception compositions(-1, 2)
    @test_throws Exception compositions(bitsize(UInt)-1, 2)
    for U in unsigned_types
        @test_throws Exception compositions(SmallBitSet{U}(2:2:6))
        @test_throws Exception compositions(SmallBitSet{U}(2:2:6), -1, 2, 2)
        @test_throws Exception compositions(SmallBitSet{U}(2:2:6), 3, 4)
        @test (compositions(SmallBitSet{U}(1:bitsize(U)), bitsize(U)-2, 2); true)
    end
end
