using SmallCollections: bitsize

using Base.FastMath: eq_fast

@testset "FixedVector" begin
    for N in (1, 2, 9, 16), T in test_types, V in (FixedVector, MutableFixedVector)
        u = rand(T, N)
        v = @inferred V{N,T}(u)
        if ismutabletype(V)
            @test v !== @inferred copy(v)
        else
            @test v === @inferred copy(v)
        end
        @test_inferred v == u true
        @test_inferred collect(v) u Vector{T}
        @test_inferred V(v) == v true
        @test_inferred FixedVector(v) == v true
        @test_inferred MutableFixedVector(v) == v true
        v2 = V{N,T}(u)
        @test_inferred v == v2 true
        if T <: Number
            @test_inferred eq_fast(v, v2) true
            T <: Integer && bitsize(T) >= bitsize(Float64) && continue
            v4 = V{N,Float64}(u)
            @test_inferred v == v4 true
            @test_inferred eq_fast(v, v4) true
        end
        if !isempty(u)
            i = rand(1:N)
            x = rand(T)
            while x == v[i]
                x = rand(T)
            end
            v5 = setindex(v, x, i)
            @test_inferred v == v5 false
            if T <: Number
                @test_inferred eq_fast(v, v5) false
            end
        end
        @test_inferred hash(v) hash(u)
        @test_inferred length(v) N
    end
end

@testset "FixedVector indices" begin
    for N in (1, 2, 9, 16), T in test_types, V in (FixedVector, MutableFixedVector)
        u = rand(T, N)
        v = @inferred V{N,T}(u)
        if isempty(u)
            @test_throws Exception first(v)
            @test_throws Exception last(v)
        else
            @test_inferred first(v) first(u) T
            @test_inferred last(v) last(u) T
        end
        x = rand(T)
        for i in -1:length(u)+1
            if 1 <= i <= length(u)
                @test_inferred v[i] u[i] T
                w = @test_inferred setindex(v, x, i) setindex!(copy(u), x, i) FixedVector(v)
                if T <: Number
                    w = @test_inferred addindex(v, x, i) setindex!(copy(u), u[i]+x, i) FixedVector(v)
                end
            else
                @test_throws Exception v[i]
                @test_throws Exception setindex(v, x, i)
                T <: Number && @test_throws Exception addindex(v, x, i)
            end
            (V == MutableFixedVector && isbitstype(T)) || continue
            if 1 <= i <= length(u)
                w = @test_inferred setindex!(copy(v), x, i) setindex!(copy(u), x, i) v
            else
                @test_throws Exception setindex!(copy(v), x, i)
            end
        end
    end
end

@testset "FixedVector bool inds" begin
    for N in (1, 2, 9, 16), T in (Bool, Int16), V in (FixedVector, MutableFixedVector)
        u = rand(T, N)
        v = V{N,T}(u)

        jj = rand(Bool, N-1)
        iis = Any[SmallVector{N+2}(jj), PackedVector{UInt32,1,Bool}(jj)]
        N > 1 && pushfirst!(iis, FixedVector{N-1}(jj))
        for ii in iis
            @test_throws Exception v[ii]
        end

        jj = rand(Bool, N)
        for ii in [FixedVector{N}(jj), SmallVector{N+2}(jj), PackedVector{UInt32,1,Bool}(jj)]
            @test_inferred v[ii] u[jj] SmallVector{N,T}
        end
    end
end

@testset "FixedVector vec inds" begin
    for N in (1, 2, 9, 16), T in (Bool, Int16), V in (FixedVector, MutableFixedVector)
        u = rand(T, N)
        v = V{N,T}(u)

        ii = 1:max(0, N-2)
        @test_inferred v[ii] u[ii] SmallVector{N,T}
        ii = collect(ii)
        @test_inferred v[ii] u[ii] Vector{T}

        M = 7
        jj = rand(Int8(1):Int8(N), M)
        ii = jj
        @test_inferred v[ii] u[ii] u
        ii = FixedVector{M}(jj)
        @test_inferred v[ii] u[ii] FixedVector{M,T}
        ii = SmallVector{M+1}(jj)
        @test_inferred v[ii] u[ii] SmallVector{M+1,T}
        ii = PackedVector{UInt128,7,Int8}(jj)
        @test_inferred v[ii] u[ii] u
        ii = 2:min(N, 5)
        @test_inferred v[ii] u[ii] SmallVector{N,T}
        ii = 1:2:min(N, 7)
        @test_inferred v[ii] u[ii] SmallVector{N,T}
    end
end

@testset "FixedVector reverse" begin
    for N in (1, 2, 9, 16), T in test_types, V in (FixedVector, MutableFixedVector)
        u = rand(T, N)
        v = @inferred V{N,T}(u)
        for i in 0:N+2
            if 1 <= i <= N+1
                @test_inferred reverse(v, i) reverse(u, i) FixedVector(v)
            elseif isempty(i:N)
                @test_inferred reverse(v, i) FixedVector(v)
            else
                @test_throws Exception reverse(v, i)
            end
            for j in i-2:N+1
                if 1 <= i <= N+1 && i-1 <= j <= N
                    @test_inferred reverse(v, i, j) reverse(u, i, j) FixedVector(v)
                elseif isempty(i:j)
                    @test_inferred reverse(v, i, j) FixedVector(v)
                else
                    @test_throws Exception reverse(v, i, j)
                end
            end
        end
    end
end

@testset "FixedVector bits" begin
    for N in [1, 2, 7, 8, 21, 64, 150], V in (FixedVector, MutableFixedVector)
        for T in test_types
            T <: Union{Base.BitInteger, Char, Enum} || continue
            b = nextpow(2, N*bitsize(T))
            b <= 1024 || continue
            v = V{N,T}(rand(T, N))
            m = @inferred bits(v)
            U = eval(Symbol(:UInt, b))
            @test m isa U
            W = eval(Symbol(:UInt, bitsize(T)))
            for (i, x) in enumerate(v)
                @test m % W == reinterpret(W, x)
                m >>= bitsize(T)
            end
            @test iszero(m)
        end

        # Bool
        v = V{N,Bool}(rand(Bool, N))
        m = @inferred bits(v)
        @test m isa Unsigned && bitsize(m) == max(8, nextpow(2, N))
        for (i, x) in enumerate(v)
            isodd(m) == x
            m >>= 1
        end
        @test iszero(m)
    end
end

@testset "FixedVector circshift" begin
    for N in [1, 4, 7, 16], V in (FixedVector, MutableFixedVector)
        for T in test_types
            u = rand(T, N)
            v = V{N,T}(u)
            for k in (-2*N, -2*N+1, -3, -1, 0, 1, 7, N+5, 2*N+7)
                @test_inferred circshift(v, k) circshift(u, k) FixedVector{N,T}
                -N < k < N && @test_inferred circshift(v, Val(k)) circshift(u, k) FixedVector{N,T}
                (V <: MutableFixedVector && isbitstype(T)) || continue
                v2 = copy(v)
                v3 = @test_inferred circshift!(v2, k) circshift(u, k) v2
                @test v3 === v2
                -N < k < N || continue
                v2 = copy(v)
                v3 = @test_inferred circshift!(v2, Val(k)) circshift(u, k) v2
                @test v3 === v2
            end
        end
    end
end

@testset "FixedVector sum/max" begin
    for N in (1, 2, 9, 16), T in test_types, V in (FixedVector, MutableFixedVector)
        T <: Number || continue
        if T <: Unsigned
            u = rand(T(1):T(9), N)
        else
            u = rand(T(-9):T(9), N)
        end
        v = FixedVector{N}(u)
        for f in (maximum, minimum)
            if isempty(u)
                @test_throws Exception f(v)
                @test_inferred f(v; init = zero(T)) f(u; init = zero(T))
            else
                @test_inferred f(v) f(u)
            end
        end
        if isempty(u)
            @test_throws Exception extrema(v)
            @test_inferred extrema(v; init = (one(T), zero(T))) extrema(u; init = (one(T), zero(T)))
        else
            @test_inferred extrema(v) extrema(u)
        end
        @test_inferred sum(v) sum(u)
        s = @inferred sum_fast(v)
        @test s ≈ sum(u)
        @test_inferred prod(v) prod(u)
        T <: AbstractFloat || continue
        u = fill(-T(0), N)
        v = SmallVector{N}(u)
        @test_inferred sum(v) sum(u)
        @test_inferred prod(-v) prod(-u)
    end
    for T in (Float32, Float64), V in (FixedVector, MutableFixedVector), x in (Inf, -Inf, NaN)
        u = T[x, -1, 0, 1]
        v = V{4}(u)
        @test_inferred maximum(v) maximum(u)
        @test_inferred minimum(v) minimum(u)
        @test_inferred sum(v) sum(u)
        if isnan(prod(u))
            @test_inferred isnan(prod(v)) true
        else
            @test_inferred prod(v) prod(u)
        end
    end
    for T in (Float32, Float64), V in (FixedVector, MutableFixedVector)
        u = T[NaN, -1, 0, 1]
        v = V{4}(u)
        @test_inferred isnan(maximum(v)) true
        @test_inferred isnan(minimum(v)) true
        @test_inferred isnan(sum(v)) true
        @test_inferred isnan(prod(v)) true
    end
end

@testset "FixedVector map" begin
    f(x) = Int32(2)*x
    f(x, y) = 2*x + y
    g(x) = iszero(x) ? 1 : 1.0
    for N in (1, 2, 9, 16), T1 in test_types, V in (FixedVector, MutableFixedVector)
        T1 <: Number || continue
        u1 = rand(T1, N)
        v1 = V{N}(u1)
        u3 = map(f, u1)
        w = @test_inferred map(f, v1) u3 FixedVector{N,eltype(u3)}
        for T2 in test_types
            T2 <: Number || continue
            u2 = rand(T2, N+1)
            v2 = V{N+1}(u2)
            u4 = map(f, u1, u2)
            w = @test_inferred map(f, v1, v2) u4 FixedVector{N,eltype(u4)}
        end
    end
    v = FixedVector{8}(1:8)
    u = collect(v)
    u5 = map(g, u)
    w = map(g, v)
    @test w == u5
    @test eltype(w) == eltype(u5)
end

@testset "FixedVector find" begin
    for N in (1, 2, 9, 16), T in [Bool, test_types...], V in (FixedVector, MutableFixedVector)
        T <: Number || continue
        k = max(N ÷ 2, 1)
        for u in (rand(T(0):(T == Bool ? true : T(2)), N), zeros(T, N), ones(T, N))
            v = V{N,T}(u)
            @test_inferred support(iszero, v) Set(findall(iszero, u)) SmallBitSet
            for style in (LazyStyle(), EagerStyle(), RigidStyle(), StrictStyle())
                i = @inferred Nothing findfirst(!iszero, v; style)
                @test i == findfirst(!iszero, u)
                i = @inferred Nothing findlast(!iszero, v; style)
                @test i == findlast(!iszero, u)
                i = @inferred Nothing findnext(!iszero, v, k; style)
                @test i == findnext(!iszero, u, k)
                i = @inferred Nothing findprev(!iszero, v, k; style)
                @test i == findprev(!iszero, u, k)
            end
            @test_inferred findmin(v) findmin(u) Tuple{T, Int}
            @test_inferred findmax(v) findmax(u) Tuple{T, Int}
            if T != Bool
                @test_inferred findmin(-, v) findmin(-, u) Tuple{T, Int}
                @test_inferred findmax(-, v) findmax(-, u) Tuple{T, Int}
            end
            @test_inferred allequal(v) allequal(u) Bool
            VERSION >= v"1.11" && @test_inferred allequal(isodd, v) allequal(isodd, u) Bool
            @test_inferred allunique(v) allunique(u) Bool
            VERSION >= v"1.11" && @test_inferred allunique(-, v) allunique(-, u) Bool
            @test_inferred findall(!iszero, v) findall(!iszero, u) SmallVector{N,SmallLength}
            @test_inferred count(!iszero, v; init = 0.0) count(!iszero, u; init = 0.0) Float64
            @test_inferred any(isodd, v) any(isodd, u) Bool
            @test_inferred all(isodd, v) all(isodd, u) Bool
            if T == Bool
                @test_inferred support(v) Set(findall(u)) SmallBitSet
                @test_inferred findall(v) findall(u) SmallVector{N,SmallLength}
                @test_inferred any(v) any(u) Bool
                @test_inferred all(v) all(u) Bool
                @test_inferred count(v) count(u) Int
            end
        end
    end
end

@testset "FixedVector support" begin
    for N in (1, 2, 9, 16), T in test_types, V in (FixedVector, MutableFixedVector)
        T <: Number || continue
        u = rand(0:2, N)
        v = V{N,T}(u)
        @test_inferred support(v) Set{Int}(i for i in 1:N if u[i] != 0) SmallBitSet
    end
end

VERSION >= v"1.11" && @testset "FixedVector rand" begin
    for N in (1, 2, 9, 16), T in test_types, V in (FixedVector, MutableFixedVector)
        v = @inferred rand(V{N,T})
        @test v isa V{N,T}
    end
end
