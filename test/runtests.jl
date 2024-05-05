using Test, SmallCollections, BitIntegers

using SmallCollections: bitsize, top_set_bit, default

using Base.FastMath: eq_fast

macro test_inferred(cmd, good)
    esc(quote
        let result = @inferred($cmd), good = $good
            @test isequal(result, good)
            @test typeof(result) == typeof(good)
            result
        end
    end)
end

macro test_inferred(cmd, good, type)
    esc(quote
        let result = @inferred($cmd), good = $good, type = $type
            @test isequal(result, good)
            if type isa Type
                @test result isa type
            else
                @test result isa typeof(type)
            end
            result
        end
    end)
end

#
# bitsize & top_set_bit
#

BitIntegers.@define_integers 440

@testset "bitsize" begin
    for T in (Int8, UInt16, Int32, UInt64, Int128, UInt256, Int440)
        @test_inferred bitsize(T) 8*sizeof(T)
    end
end

@testset "top_set_bit" begin
    for T in (UInt8, UInt16, UInt32, UInt64, UInt128, UInt256, UInt512, UInt440)
        @test_inferred top_set_bit(T(0)) 0
        m = bitsize(T)
        x = T(1) << (m-3) - T(3)
        @test_inferred top_set_bit(x) m-3
    end
end

#
# SmallBitSet
#

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
        if !isempty(t)
            @test_inferred first(s) minimum(t)
            @test_inferred minimum(s) minimum(t)
            @test_inferred last(s) maximum(t)
            @test_inferred maximum(s) maximum(t)
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

@testset "Subsets" begin
    for n in [-1, 0, 1, 2, 10], k in [-1, 0, 1, n-1, n, n+1]
        ss = Subsets(n, k)
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
end


@testset "AllSubsets" begin
    for n in [-1, 0, 1, 2, 10]
        ss = AllSubsets(n)
        if n >= 0
            @test_inferred length(ss) 2^n
        else
            @test_inferred length(ss) 0
        end
        @test eltype(ss) == SmallBitSet{UInt}
        ssv = @inferred collect(ss)
        @test length(ssv) == length(ss) == length(unique(ssv))
    end
end

#
# SmallVector
#

function isvalid(v::SmallVector{N,T}) where {N,T}
    n = length(v)
    0 <= n <= N && all(==(default(T)), view(v.b, n+1:N))
end

using StructEqualHash: @struct_equal_hash

struct A
    x::Char
    y::Int
end

@struct_equal_hash A

test_types = (Int8, UInt64, Int128, UInt256, Float32, Float64, Char, String, Symbol, A)

Base.rand(::Type{String}) = string(rand(Char, 3)...)
Base.rand(::Type{Symbol}) = Symbol(rand(Char, 3)...)
Base.rand(::Type{A}) = A(map(rand, fieldtypes(A))...)
Base.rand(::Type{T}, n::Integer) where T <: Union{String,Symbol,A} = T[rand(T) for _ in 1:n]

@testset failfast = true "SmallVector" begin
    for N in (1, 2, 9, 16), T in test_types, m in (0, 1, round(Int, 0.7*N), N-1, N)
        u = rand(T, m)
        v = @inferred SmallVector{N,T}(u)
        @test_inferred capacity(v) N Int
        @test_inferred v == u true
        @test isvalid(v)
        @test_inferred collect(v) u Vector{T}
        v2 = SmallVector{N,T}(u)
        @test_inferred v == v2 true
        v3 = SmallVector{2*N,T}(u)
        @test_inferred v == v3 true
        if T <: Number
            @test_inferred eq_fast(v, v2) true
            @test_inferred eq_fast(v, v3) true
            v4 = SmallVector{N,Float64}(u)
            @test_inferred v == v4 true
            @test_inferred eq_fast(v, v4) true
        end
        if !isempty(u)
            i = rand(1:m)
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
        v6 = SmallVector{N+2,T}(push!(copy(u), rand(T)))
        @test_inferred v == v6 false
        if T <: Number
            @test_inferred eq_fast(v, v6) false
        end
        if !isempty(u)
            u7 = copy(u)
            pop!(u7)
            v7 = SmallVector{N+2,T}(u7)
            @test_inferred v == v7 false
            if T <: Number
                @test_inferred eq_fast(v, v7) false
            end
        end
        @test_inferred hash(v) hash(u) UInt
        v8 = SmallVector{2*N,T}(u)
        @test_inferred fasthash(v) fasthash(v8) UInt
        @test_inferred length(v) length(u) Int
        @test_inferred SmallVector{N,T}() SmallVector{N,T}(())
        @test_inferred empty(v) SmallVector{N,T}()
        @test_inferred empty(v, Char) SmallVector{N,Char}()
    end
end

@testset failfast = true "SmallVector indices" begin
    for N in (1, 2, 9, 16), T in test_types, m in (0, 1, round(Int, 0.7*N), N-1, N)
        u = rand(T, m)
        v = @inferred SmallVector{N,T}(u)
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
                w = @test_inferred setindex(v, x, i) setindex!(copy(u), x, i) v
                @test isvalid(w)
                if T <: Number
                    w = @test_inferred addindex(v, x, i) setindex!(copy(u), u[i]+x, i) v
                    @test isvalid(w)
                end
            else
                @test_throws Exception v[i]
                @test_throws Exception setindex(v, x, i)
                T <: Number && @test_throws Exception addindex(v, x, i)
            end
        end
        for i in 0:m, j in i-1:m+1
            if checkbounds(Bool, u, i:j)
                w = @test_inferred v[i:j] u[i:j] v
                @test isvalid(w)
            else
                @test_throws Exception v[i:j]
            end
        end
    end
end

@testset failfast = true "SmallVector zeros" begin
    for N in (1, 2, 9, 16), T in test_types, m in (0, 1, round(Int, 0.7*N), N-1, N)
        T <: Number || continue
        u = zeros(T, m)
        v = SmallVector{N,T}(u)
        @test_inferred iszero(v) true
        w = @test_inferred zero(v) u v
        @test isvalid(w)
        w = @test_inferred zeros(SmallVector{N,T}, m) v
        @test isvalid(w)
        w = @test_inferred ones(SmallVector{N,T}, m) ones(T, m) SmallVector{N,T}
        @test isvalid(w)
    end
end

@testset failfast = true "SmallVector push/pop" begin
    for N in (1, 2, 9, 16), T in test_types, m in (0, 1, round(Int, 0.7*N), N-1, N)
        u = rand(T, m)
        v = @inferred SmallVector{N,T}(u)
        x = rand(T)
        y = rand(T)
        @test_inferred push(v) v
        @test_inferred pushfirst(v) v
        if length(u) == N
            @test_throws Exception push(v, x)
            @test_throws Exception push(v, x, y)
            @test_throws Exception pushfirst(v, x)
            @test_throws Exception pushfirst(v, x, y)
        else
            w = @test_inferred push(v, x) push!(copy(u), x) v
            @test isvalid(w)
            w = @test_inferred pushfirst(v, x) pushfirst!(copy(u), x) v
            @test isvalid(w)
            if length(u) <= N-2
                w = @test_inferred push(v, x, y) push(push(v, x), y)
                @test isvalid(w)
                w = @test_inferred pushfirst(v, x, y) pushfirst(pushfirst(v, y), x)
                @test isvalid(w)
            end
        end
        if isempty(u)
            @test_throws Exception pop(v)
            @test_throws Exception popfirst(v)
        else
            w, _ = @test_inferred pop(v) (deleteat!(copy(u), length(u)), last(u)) (v, last(v))
            @test isvalid(w)
            w, _ = @test_inferred popfirst(v) (deleteat!(copy(u), 1), first(u)) (v, first(v))
            @test isvalid(w)
        end
        for i in (-1, 0, 1, 2, length(u), length(u)+1)
            if 1 <= i <= length(u)+1 && length(u) < N
                w = @test_inferred insert(v, i, x) insert!(copy(u), i, x) v
                @test isvalid(w)
                if i <= length(u)
                    w = @test_inferred duplicate(v, i) insert(v, i, v[i])
                    @test isvalid(w)
                else
                    @test_throws Exception duplicate(v, i)
                end
            else
                @test_throws Exception insert(v, i, x)
                @test_throws Exception duplicate(v, i)
            end
            if 1 <= i <= length(u)
                w = @test_inferred deleteat(v, i) deleteat!(copy(u), i) v
                @test isvalid(w)
            else
                @test_throws Exception deleteat(v, i)
            end
        end
        @test_inferred append(v) v
        @test_inferred prepend(v) v
        xy = [x, y]
        if length(u) <= N-2
            w = @test_inferred append(v, SmallVector{4}(xy)) push(v, x, y)
            @test isvalid(w)
            w = @test_inferred append(v, xy[i] for i in 1:2) push(v, x, y)
            @test isvalid(w)
            w = @test_inferred append(v, (x,), [y]) push(v, x, y)
            @test isvalid(w)
            w = @test_inferred prepend(v, SmallVector{4}(xy)) pushfirst(v, x, y)
            @test isvalid(w)
            w = @test_inferred prepend(v, xy[i] for i in 1:2) pushfirst(v, x, y)
            @test isvalid(w)
            w = @test_inferred prepend(v, (x,), [y]) pushfirst(v, x, y)
            @test isvalid(w)
        else
            @test_throws Exception append(v, SmallVector{4}(xy))
            @test_throws Exception append(v, xy[i] for i in 1:2)
            @test_throws Exception append(v, (x,), [y])
            @test_throws Exception prepend(v, SmallVector{4}(xy))
            @test_throws Exception prepend(v, xy[i] for i in 1:2)
            @test_throws Exception prepend(v, (x,), [y])
        end
    end
end

@testset failfast = true "SmallVector add/mul" begin
    for N in (1, 2, 9, 16), T1 in test_types, m in (1, round(Int, 0.7*N), N-1, N)
        T1 <: Number || continue
        if T1 <: Unsigned
            u1 = rand(T1(1):T1(9), m)
        else
            u1 = rand(T1(-9):T1(9), m)
        end
        v1 = SmallVector{N}(u1)
        for op in (+, -)
            w = @test_inferred op(v1) op(u1) SmallVector{N,T1}
            @test isvalid(w)
        end
        for T2 in test_types
            T2 <: Number || continue
            if T2 <: Unsigned
                u2 = rand(T2(1):T2(9), m)
                c = rand(T2(1):T2(9))
            else
                u2 = rand(T2(-9):T2(9), m)
                c = rand(T2(-9):T2(9))
            end
            v2 = SmallVector{N}(u2)
            T = promote_type(T1, T2)
            for op in (+, -)
                w = @test_inferred op(v1, v2) op(u1, u2) SmallVector{N,T}
                @test isvalid(w)
                v3 = SmallVector{N+4}(u2)
                w = @test_inferred op(v1, v3) op(u1, u2) SmallVector{N,T}
                @test isvalid(w)
                w = @test_inferred op(v3, v1) op(u2, u1) SmallVector{N,T}
                @test isvalid(w)
            end
            w = @test_inferred c*v1 c*u1 SmallVector{N,T}
            @test isvalid(w)
            w = @test_inferred Base.FastMath.mul_fast(c, v1) c*u1 SmallVector{N,T}
            @test isvalid(w)
            @test_inferred v1*c c*v1
        end
    end

    N = 8
    T = Float64
    u = T[-Inf, -1, 0, 1, Inf, NaN]
    v = SmallVector{8,Float64}(u)
    for c in (Inf, -Inf, NaN)
        w = @test_inferred c*v c*u SmallVector{N,T}
        @test isvalid(w)
    end
end

@testset failfast = false "SmallVector sum/max" begin
    for N in (1, 2, 9, 16), T in test_types, m in (0, 1, round(Int, 0.7*N), N-1, N)
        T <: Number || continue
        if T <: Unsigned
            u = rand(T(1):T(9), m)
        else
            u = rand(T(-9):T(9), m)
        end
        v = SmallVector{N}(u)
        for f in (maximum, minimum)
            if isempty(u)
                @test_throws Exception f(v)
                @test_inferred f(v; init = zero(T)) f(u; init = zero(T))
            else
                @test_inferred f(v) f(u)
            end
        end
        @test_inferred sum(v) sum(u)
        s = @inferred sum_fast(v)
        @test abs(s-sum(u)) < 1e-5
        @test_inferred prod(v) prod(u)
        T <: AbstractFloat || continue
        u = fill(-T(0), m)
        v = SmallVector{N}(u)
        @test_inferred sum(v) sum(u)
        @test_inferred prod(-v) prod(-u)
    end
    for N in (5, 16), T in (Float32, Float64), x in (Inf, -Inf, NaN)
        u = T[x, -1, 0, 1]
        v = SmallVector{N}(u)
        @test_inferred maximum(v) maximum(u)
        @test_inferred minimum(v) minimum(u)
        @test_inferred sum(v) sum(u)
        if isnan(prod(u))
            @test_inferred isnan(prod(v)) true
        else
            @test_inferred prod(v) prod(u)
        end
    end
    for N in (5, 16), T in (Float32, Float64)
        u = T[NaN, -1, 0, 1]
        v = SmallVector{N}(u)
        @test_inferred isnan(maximum(v)) true
        @test_inferred isnan(minimum(v)) true
        @test_inferred isnan(sum(v)) true
        @test_inferred isnan(prod(v)) true
    end
end

@testset failfast = true "SmallVector map" begin
    f(x) = Int32(2)*x
    f(x, y) = 2*x + y
    g(x) = iszero(x) ? 1 : 1.0
    for N in (1, 2, 9, 16), T1 in test_types, m in (0, 1, round(Int, 0.7*N), N-1)
        T1 <: Number || continue
        u1 = rand(T1, m)
        v1 = SmallVector{N}(u1)
        u3 = map(f, u1)
        w = @test_inferred map(f, v1) u3 SmallVector{N,eltype(u3)}
        @test isvalid(w)
        for T2 in test_types
            T2 <: Number || continue
            u2 = rand(T2, m+1)
            v2 = SmallVector{N+2}(u2)
            u4 = map(f, u1, u2)
            w = @test_inferred map(f, v1, v2) u4 SmallVector{N,eltype(u4)}
            @test isvalid(w)
        end
    end
    for m in (0, 1, 3)
        v = SmallVector{8}(1:m)
        u = collect(v)
        u5 = map(g, u)
        w = map(g, v)
        @test w == u5
        @test eltype(w) == eltype(u5)
    end
end

@testset "SmallVector rest" begin
    v = SmallVector{8}([1,2])
    x1, w... = v
    @test w == v[2:2] && typeof(w) == typeof(v) && isvalid(w)
    x1, x2, w... = v
    @test w == v[3:2] && typeof(w) == typeof(v) && isvalid(w)
    @test_throws Exception x1, x2, x3, w... = v
end

@testset failfast = true "SmallVector support" begin
    for N in (1, 2, 9, 16), T in test_types, m in (0, 1, round(Int, 0.7*N), N-1, N)
        T <: Number || continue
        u = rand(0:2, m)
        v = @inferred SmallVector{N,T}(u)
        @test_inferred support(v) Set{Int}(i for i in 1:m if u[i] != 0) SmallBitSet
    end
end

@testset "broadcast" begin
    N = 8
    for T in (Int, Float64), m in (0, 1, 3, 8)
        u = collect(T, 1:m)
        v = SmallVector{N}(u)
        t = Tuple(u)
        c = T(2)
        uu = m < N ? push!(copy(u), c) : copy(u)
        vv = SmallVector{N}(uu)
        w = @test_inferred v .+ v u .+ u SmallVector{N,T}
        @test isvalid(w)
        w = @test_inferred v .- v u .- u SmallVector{N,T}
        @test isvalid(w)
        w = @test_inferred v .* v u .* u SmallVector{N,T}
        @test isvalid(w)
        w = @test_inferred (c .* v) (c .* u) SmallVector{N,T}
        @test isvalid(w)

        w = abs.(-v)
        @test w == v && w isa SmallVector{N,T} && isvalid(w)

        f(x, y) = x + 2*y
        # @test_inferred map(f, v, v) map(f, u, u) SmallVector{N,T}
        # @test_inferred map(f, vv, v) map(f, uu, u) SmallVector{N,T}
        w = f.(v, v)
        @test w == f.(u, u) && w isa SmallVector{N,T}
        w = f.(v, c)
        @test w == f.(u, c) && w isa SmallVector{N,T}
        if m > 0
            w = f.(v, t)
            @test w == f.(u, t) && w isa SmallVector{N,T}
        end
    end

    for T in (Int16, Float32)
        if T <: Integer
            u1 = T[2, -1, 4, -3, 7]
            u2 = T[-3, 9, 4, -1, -5, 6]
        else
            u1 = 10 .* rand(T, 5) .- 5
            u2 = 10 .* rand(T, 6) .- 5
        end
        v1 = SmallVector{8,T}(u1)
        v2 = SmallVector{8,T}(u2)
        for f in (+, -, *, /, ==, !=, <, >, <=, >=, ===, isequal)
            ww = map(f, u1, u2)
            w = @test_inferred map(f, v1, v2) ww SmallVector{8,eltype(ww)}
            @test isvalid(w)
        end
        for f in (round, floor, ceil, trunc, abs, abs2, sign, sqrt, signbit)
            if f === sqrt
                uu = map(abs, u1)
                vv = map(abs, v1)
                ww = map(f, uu)
                w = @test_inferred map(f, vv) ww SmallVector{8,eltype(ww)}
                @test isvalid(w)
            else
                ww = map(f, u1)
                w = @test_inferred map(f, v1) ww SmallVector{8,eltype(ww)}
                @test isvalid(w)
            end
        end
        T <: Integer || continue
        for f in (&, |, xor, nand, nor)
            w = @test_inferred map(f, v1, v2) map(f, u1, u2) SmallVector{8,T}
            @test isvalid(w)
        end
        for f in (~,)
            w = @test_inferred map(f, v1) map(f, u1) SmallVector{8,T}
            @test isvalid(w)
        end
    end

    u = [7, 8]
    v = SmallVector{3}(u)
    a = [1 2; 3 4]
    @test a .+ v == a .+ u

    u = ['a', 'b', 'c']
    v = SmallVector{5}(u)
    w = v .* 'x'
    @test w == u .* 'x' && w isa SmallVector{5,String}
end

#
# BangBang
#

using BangBang

@testset "SmallBitSet !!" begin
    s = SmallBitSet(1:3)
    t = SmallBitSet(3:5)
    x = 6
    @test_inferred push!!(s, x) push(s, x)
    @test_inferred pop!!(s) pop(s)
    @test_inferred delete!!(s, x) delete(s, x)
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
    @test_broken isdefined(BangBang, :map!!)
    @test_inferred add!!(v, w) v+w
end
