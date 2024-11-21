DS = (SmallDict, MutableSmallDict)

key_types = [Int8, UInt32, Float64, String, TestEnum]
val_types = [Bool, Int64, Char, TestStruct]

@testset "SmallDict" begin
    for D in DS, N in (1, 2, 9, 16), K in key_types, V in val_types, m in (0, 1, N-1, N)
        D == SmallDict || (isbitstype(K) && isbitstype(V)) || continue
        d = @inferred D{N,K,V}()
        @test d isa D{N,K,V} && isempty(d)

        itr = (rand(K) => rand(V) for _ in 1:m)
        d = @inferred D{N,K,V}(rand(K) => rand(V) for _ in 1:m)
        @test d == Dict(d)

        kv = collect(Pair{K,V}, itr)
        d = @inferred D{N}(kv)
        e = Dict(d)
        @test d == e
        @test_inferred capacity(d) N
        @test_inferred length(d) length(e)
        @test_inferred isempty(d) isempty(e)

        @test_inferred SmallDict(d) d SmallDict{N,K,V}
        @test_inferred MutableSmallDict(d) d MutableSmallDict{N,K,V}

        @test_inferred D{N}(e) e D{N,K,V}
        @test_inferred D{N,K,V}(e) e D{N,K,V}

        e = @test_inferred copy(d) d
        D == MutableSmallDict && @test e !== d
        @test_inferred Set(d) Set(e)   # iteration
        @test_inferred Set(keys(d)) Set(keys(e))
        @test_inferred collect(values(d)) V[d[k] for k in keys(d)]
    end
end

@testset "SmallDict getindex/setindex" begin
    for D in DS, N in (1, 2, 9, 16), K in key_types, V in val_types, m in (0, 1, N-1, N)
        D == SmallDict || (isbitstype(K) && isbitstype(V)) || continue
        K == TestEnum && length(instances(K)) <= m && continue
        K == Bool && m >= 2 && continue
        d = D{N,K,V}(rand(K) => rand(V) for _ in 1:m)
        (isempty(d) || m == N) && continue

        k = rand(keys(d))
        v = rand(V)
        @test_inferred setindex(d, v, k) setindex!(Dict(d), v, k) SmallDict(d)
        k0 = rand_notin(K, keys(d))
        v0 = rand(V)
        @test_inferred setindex(d, v0, k0) setindex!(Dict(d), v0, k0) SmallDict(d)

        D == MutableSmallDict || continue
        e = @test_inferred setindex!(d, v, k) setindex!(Dict(d), v, k) d
        @test e === d
        e = @test_inferred setindex!(d, v0, k0) setindex!(Dict(d), v0, k0) d
        @test e === d
    end
end

@testset "SmallDict in/get/getkey" begin
    for D in DS, N in (1, 2, 9, 16), K in key_types, V in val_types, m in (0, 1, N-1, N)
        D == SmallDict || (isbitstype(K) && isbitstype(V)) || continue
        K == TestEnum && length(instances(K)) <= m && continue
        (K == Bool || V == Bool) && m >= 2 && continue
        kvs = [rand(K) => rand(V) for _ in 1:m]
        d = D{N,K,V}(kvs)
        @test_inferred Base.hasfastin(d) Base.hasfastin(d.keys)
        k0 = rand_notin(K, keys(d))
        v0 = rand_notin(V, values(d))
        for (k, v) in d
            @test_inferred (k => v) in d true
            @test_inferred (k => v0) in d false
            @test_inferred (k0 => v) in d false
            @test_inferred haskey(d, k) true
            @test_inferred getkey(d, k, k0) k
            @test_inferred d[k] v
            @test_inferred get(d, k, v0) v
        end
        @test_inferred (k0 => v0) in d false
        @test_inferred haskey(d, k0) false
        @test_throws Exception d[k0]
        @test_inferred get(d, k0, v0) v0

        D == MutableSmallDict || continue
        e = copy(d)
        if !isempty(d)
            k = rand(keys(d))
            @test_inferred get!(e, k, v0) d[k]
            @test e == d
        end
        m < N || continue
        @test_inferred get!(e, k0, v0) v0
        @test (k0 => v0) in e
    end

    d = SmallDict{4,Float32,Int8}(0.0 => 1, -0.0 => 2, 1.0 => 3, NaN => 4)
    @test_inferred d[0.0] Int8(1)
    @test_inferred d[-0.0] Int8(2)
    @test_inferred d[NaN] Int8(4)
    @test_inferred getkey(d, 1, Float32(0.0)) Float32(1.0)
end

@testset "SmallDict empty" begin
    for D in DS, N in (1, 2, 9, 16), K in key_types, V in val_types, m in (0, 1, N-1, N)
        D == SmallDict || (isbitstype(K) && isbitstype(V)) || continue
        d = D{N,K,V}(rand(K) => rand(V) for _ in 1:m)
        @test_inferred empty(d) D{N,K,V}()
        @test_inferred empty(d, Char) D{N,K,Char}()
        @test_inferred empty(d, UInt, Char) D{N,UInt,Char}()
        D == MutableSmallDict || continue
        e = @inferred empty!(d)
        @test isempty(e) && e === d
    end
end

@testset "SmallDict push!/pop!" begin
    for D in (MutableSmallDict,), N in (1, 2, 9, 16), K in key_types, V in val_types, m in (0, 1, N-1, N)
        (isbitstype(K) && isbitstype(V)) || continue
        K == TestEnum && length(instances(K)) <= m && continue
        (K == Bool || V == Bool) && m >= 2 && continue
        kvs = [rand(K) => rand(V) for _ in 1:m]
        d = D{N,K,V}(kvs)
        isempty(d) && continue

        e = D{N,K,V}()
        # kvs must not be empty because Base.push!(e) is not defined except for AbstractArray
        @test_inferred push!(e, kvs...) d
        @test_inferred push!(e, kvs...) e
        e = copy(d)
        kv = @inferred pop!(e)
        @test kv in d && !(kv in e)
        @test_inferred push!(e, kv) d

        e = copy(d)
        k = rand(keys(d))
        v = @inferred pop!(e, k)
        kv = k => v
        @test kv in d && !(kv in e)
        @test_inferred push!(e, kv) d

        e = copy(d)
        v0 = rand_notin(V, values(d))
        v = @test_inferred pop!(e, k, v0) d[k]
        kv = k => v
        @test !(kv in e)
        @test_inferred push!(e, kv) d

        e = copy(d)
        k0 = rand_notin(K, keys(d))
        @test_throws Exception pop!(e, k0)
        @test_inferred pop!(e, k0, v0) v0
        @test e == d
    end
end

@testset "SmallDict push/pop" begin
    for D in DS, N in (1, 2, 9, 16), K in key_types, V in val_types, m in (0, 1, N-1, N)
        D == SmallDict || (isbitstype(K) && isbitstype(V)) || continue
        K == TestEnum && length(instances(K)) <= m && continue
        (K == Bool || V == Bool) && m >= 2 && continue
        kvs = [rand(K) => rand(V) for _ in 1:m]
        d = D{N,K,V}(kvs)

        e = D{N,K,V}()
        @test_inferred push(e, kvs...) SmallDict(d)
        @test_inferred push(d, kvs...) SmallDict(d)

        isempty(d) && continue

        e, kv = @inferred pop(d)
        @test kv in d && !(kv in e)
        @test_inferred push(e, kv) SmallDict(d)

        k = rand(keys(d))
        e, v = @inferred pop(d, k)
        kv = k => v
        @test kv in d && !(kv in e)
        @test_inferred push(e, kv) SmallDict(d)

        v0 = rand_notin(V, values(d))
        e, v = @inferred pop(d, k, v0)
        kv = k => v
        @test kv in d && !(kv in e)
        @test_inferred push(e, kv) SmallDict(d)

        k0 = rand_notin(K, keys(d))
        @test_throws Exception pop(d, k0)
        @test_inferred pop(d, k0, v0) (SmallDict(d), v0)
    end
end

@testset "SmallDict filter!" begin
    for D in (MutableSmallDict,), N in (1, 2, 9, 16), K in key_types, V in val_types, m in (0, 1, N-1, N)
        (isbitstype(K) && isbitstype(V)) || continue
        V == Bool && m >= 2 && continue
        kvs = [rand(K) => rand(V) for _ in 1:m]
        d = D{N,K,V}(kvs)
        if K <: Integer
            e = copy(d)
            f = @test_inferred filter!(kv -> isodd(kv.first), e) filter!(kv -> isodd(kv.first), Dict(e)) e
            @test f === e
        else
            v0 = rand_notin(V, values(d))
            @test_inferred filter!(kv -> kv.second != v0, d) d
            e = copy(d)
            f = @test_inferred filter!(kv -> kv.second == v0, e) empty(e)
            @test f === e
        end
    end
end

@testset "SmallDict mergewith" begin
    op(x, y) = y
    op(x::Number, y::Number) = x*y
    for D in DS, N in (1, 2, 9, 16), K in key_types, V in val_types, m in (0, 1, N-1, N)
        D == SmallDict || (isbitstype(K) && isbitstype(V)) || continue
        K == TestEnum && length(instances(K)) <= m && continue
        (K == Bool || V == Bool) && m >= 2 && continue
        l = m÷3
        kvs1 = [rand(K) => rand(V) for _ in 1:l]
        kvs2 = [rand(K) => rand(V) for _ in 1:l]
        kvs3 = [rand(K) => rand(V) for _ in 1:m-2*l]
        d = D{N,K,V}([kvs1..., kvs2...])
        @test_inferred mergewith(op, d) SmallDict(d)
        e = Dict{K,V}([kvs2..., kvs3...])
        @test_inferred mergewith(op, d, e) mergewith!(op, Dict(d), e) SmallDict(d)
        f = Dict{K,V}([kvs1..., kvs3...])
        @test_inferred mergewith(op, d, e, f) mergewith!(op, Dict(d), e, f) SmallDict(d)
        D == MutableSmallDict || continue
        d2 = @test_inferred mergewith!(op, d, e) mergewith!(op, Dict(d), e) d
        @test d2 === d
    end
end
