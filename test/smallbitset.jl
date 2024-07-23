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

    for U in unsigned_types, a in map(SmallBitSet{U}, [Int[], [3], [3, 5], [2, 4, 6, 7]])
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
    end

    for U in unsigned_types, a in map(SmallBitSet{U}, [Int[], [3], [3, 5], [2, 4, 6, 7]])
        ss = subsets(a)
        @test_inferred length(ss) 2^length(a)
        @test eltype(ss) == SmallBitSet{U}
        ssv = @inferred collect(ss)
        @test length(ssv) == length(ss) == length(unique(ssv))
    end
end

@testset "shuffles" begin
    function test_shuffles(ks)
        sh = @inferred shuffles(ks...)
        a = SmallBitSet(1:sum(ks; init = 0))
        # TODO: length
        @test all(map(length, t) == ks &&
            (isempty(t) ? isempty(a) : (union(t...) == a)) &&
            shuffle_signbit(t...) == s for (t, s) in sh)
        @test allunique(sh)
    end

    function test_shuffles(a::S, ks::NTuple{N,Int}) where {S <: SmallBitSet, N}
        test_shuffles(ks)
        sh = @inferred shuffles(a, ks...)
        # TODO: length
        @test eltype(sh) == Tuple{NTuple{N, S}, Bool}
        @test all(t isa NTuple{N, S} && s isa Bool &&
            map(length, t) == ks &&
            (isempty(t) ? isempty(a) : (union(t...) == a)) &&
            shuffle_signbit(t...) == s for (t, s) in sh)
        @test allunique(sh)
    end

    for U in unsigned_types, (v, ks) in [(Int[], ()), (Int[], (0,)), (Int[], (0, 0)),
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
        if bitsize(U) <= bitsize(UInt)
            @test (shuffles(SmallBitSet{U}(1:bitsize(U)), bitsize(U)-4, 4); true)
        else
            @test_throws Exception shuffles(SmallBitSet{U}(1:bitsize(UInt)+1), bitsize(UInt), 1)
        end
    end

    # TODO: still necessary?
    for k in [-1, 0, 1, 2, 4], l in [-1, 0, 1, 2, 4]
        if !(k >= 0 && l >= 0)
            @test_throws Exception shuffles(k, l)
            continue
        end
        sh = @inferred shuffles(k, l)
        @test_inferred length(sh) binomial(k+l, l)
        @test eltype(sh) == Tuple{NTuple{2,SmallBitSet{UInt}},Bool}
        @test allunique(sh)
        for ((a, b), s) in sh
            @test a isa SmallBitSet{UInt} && b isa SmallBitSet{UInt} && s isa Bool
            @test length(a) == k && length(b) == l && union(a, b) == SmallBitSet(1:k+l)
            s2 = false
            for i in a, j in b
                s2 ⊻= i > j
            end
            @test s == s2
            s3 = @inferred shuffle_signbit(a, b)
            @test s == s3
            @test shuffle_signbit(a) == false
            c = convert(SmallBitSet{UInt8}, rand(UInt8))
            a1 = SmallBitSet{UInt8}(intersect(a, c))
            a2 = SmallBitSet{UInt128}(setdiff(a, c))
            s4 = @inferred shuffle_signbit(a1, a2, b)
            @test s4 == shuffle_signbit(a1, a2) ⊻ shuffle_signbit(a, b)
        end
    end
    @test shuffle_signbit() == false
    # check that unsafe_lshr in iterate for Shuffles is safe
    @test collect(subsets(bitsize(UInt), 1)) == [SmallBitSet((k,)) for k in 1:bitsize(UInt)]
end
