using SmallCollections: bitsize

unsigned_types = (UInt8, UInt64, UInt256, UInt440)

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
        sh = @inferred set_compositions(ks...)
        a = SmallBitSet(1:sum(ks; init = 0))
        @test @inferred(length(sh)) == factorial(big(sum(ks; init = 0))) ÷ prod(map(factorial∘big, ks); init = 1)
        @test @inferred(eltype(sh)) == NTuple{N, SmallBitSet{UInt}}
        @test all(map(length, t) == ks && (isempty(t) ? isempty(a) : (union(t...) == a)) for t in sh)
        @test allunique(sh)
    end

    function test_compositions(a::S, ks::NTuple{N,Int}) where {S <: SmallBitSet, N}
        test_compositions(ks)
        sh = @inferred set_compositions(a, ks...)
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

    @test_throws Exception set_compositions(-1, 2)
    @test_throws Exception set_compositions(bitsize(UInt)-1, 2)
    for U in unsigned_types
        @test_throws Exception set_compositions(SmallBitSet{U}(2:2:6))
        @test_throws Exception set_compositions(SmallBitSet{U}(2:2:6), -1, 2, 2)
        @test_throws Exception set_compositions(SmallBitSet{U}(2:2:6), 3, 4)
        @test (set_compositions(SmallBitSet{U}(1:bitsize(U)), bitsize(U)-2, 2); true)
    end
end
