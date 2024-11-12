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
        v1 = SmallVector{N}(u1)
        u3 = map(f, u1)
        w = @test_inferred map(f, v1) u3 SmallVector{N,eltype(u3)}
        for T2 in test_types
            T2 <: Number || continue
            u2 = rand(T2, N+1)
            v2 = SmallVector{N+1}(u2)
            u4 = map(f, u1, u2)
            w = @test_inferred map(f, v1, v2) u4 SmallVector{N,eltype(u4)}
        end
    end
    v = FixedVector{8}(1:8)
    u = collect(v)
    u5 = map(g, u)
    w = map(g, v)
    @test w == u5
    @test eltype(w) == eltype(u5)
end

@testset "FixedVector support" begin
    for N in (1, 2, 9, 16), T in test_types, V in (FixedVector, MutableFixedVector)
        T <: Number || continue
        u = rand(0:2, N)
        v = @inferred SmallVector{N,T}(u)
        @test_inferred support(v) Set{Int}(i for i in 1:N if u[i] != 0) SmallBitSet
    end
end