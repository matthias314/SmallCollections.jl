using SmallCollections: default, bitsize

using Base.FastMath: eq_fast

const VS = (SmallVector, MutableSmallVector)

function isvalid(v::AbstractSmallVector{N,T}) where {N,T}
    n = length(v)
    0 <= n <= N && all(==(default(T)), view(v.b, n+1:N))
end

@testset "SmallVector" begin
    for V in VS, N in (1, 2, 9, 16), T in test_types, m in (0, 1, round(Int, 0.7*N), N-1, N)
        u = rand(T, m)
        v = @inferred V{N,T}(u)
        if ismutabletype(V)
            @test v == @inferred(copy(v)) !== v
        else
            @test v === @inferred copy(v)
        end
        @test_inferred capacity(v) N Int
        @test_inferred v == u true
        @test isvalid(v)
        @test_inferred collect(v) u Vector{T}
        v2 = V{N,T}(u)
        @test_inferred v == v2 true
        v3 = V{2*N,T}(u)
        @test_inferred v == v3 true
        if T <: Number
            @test_inferred eq_fast(v, v2) true
            @test_inferred eq_fast(v, v3) true
            T <: Integer && bitsize(T) >= bitsize(Float64) && continue
            v4 = V{N,Float64}(u)
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
        v6 = V{N+2,T}(push!(copy(u), rand(T)))
        @test_inferred v == v6 false
        if T <: Number
            @test_inferred eq_fast(v, v6) false
        end
        if !isempty(u)
            u7 = copy(u)
            pop!(u7)
            v7 = V{N+2,T}(u7)
            @test_inferred v == v7 false
            if T <: Number
                @test_inferred eq_fast(v, v7) false
            end
        end
        @test_inferred hash(v) hash(u) UInt
        v8 = V{2*N,T}(u)
        @test_inferred fasthash(v) fasthash(v8) UInt
        @test_inferred length(v) length(u) Int
        @test_inferred V{N,T}() V{N,T}(())
        @test_inferred empty(v) V{N,T}()
        @test_inferred empty(v, Char) V{N,Char}()
    end
end

@testset "SmallVector indices" begin
    for V in VS, N in (1, 2, 9, 16), T in test_types, m in (0, 1, round(Int, 0.7*N), N-1, N)
        u = rand(T, m)
        v = V{N,T}(u)
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
                w = @test_inferred setindex(v, x, i) setindex!(copy(u), x, i) SmallVector(v)
                @test isvalid(w)
                if T <: Number
                    w = @test_inferred addindex(v, x, i) setindex!(copy(u), u[i]+x, i) SmallVector(v)
                    @test isvalid(w)
                end
                if ismutabletype(V) && isbitstype(T)
                    w = @test_inferred setindex!(copy(v), x, i) setindex!(copy(u), x, i) v
                    @test isvalid(w)
                end
            else
                @test_throws Exception v[i]
                @test_throws Exception setindex(v, x, i)
                T <: Number && @test_throws Exception addindex(v, x, i)
                if ismutabletype(V) && isbitstype(T)
                    @test_throws Exception setindex!(v, x, i)
                end
            end
        end
        for i in 0:m, j in i-1:m+1
            if checkbounds(Bool, u, i:j)
                w = @test_inferred v[i:j] u[i:j] SmallVector(v)
                @test isvalid(w)
            else
                @test_throws Exception v[i:j]
            end
        end
    end
end

@testset "SmallVector zeros" begin
    for V in VS, N in (1, 2, 9, 16), T in test_types, m in (0, 1, round(Int, 0.7*N), N-1, N)
        T <: Number || continue
        u = zeros(T, m)
        v = V{N,T}(u)
        @test_inferred iszero(v) true
        w = @test_inferred zero(v) u v
        @test isvalid(w)
        w = @test_inferred zeros(V{N,T}, m) v
        @test isvalid(w)
        w = @test_inferred ones(V{N,T}, m) ones(T, m) V{N,T}
        @test isvalid(w)
    end
end

@testset "SmallVector reverse" begin
    for V in VS, N in (1, 2, 9, 16), T in test_types, m in (0, 1, round(Int, 0.7*N), N-1, N)
        u = rand(T, m)
        v = V{N,T}(u)
        for i in 0:m+2
            if 1 <= i <= m+1
                @test_inferred reverse(v, i) reverse(u, i) SmallVector(v)
            elseif isempty(i:m)
                @test_inferred reverse(v, i) SmallVector(v)
            else
                @test_throws Exception reverse(v, i)
            end
            for j in i-2:m+1
                if 1 <= i <= m+1 && i-1 <= j <= m
                    @test_inferred reverse(v, i, j) reverse(u, i, j) SmallVector(v)
                elseif isempty(i:j)
                    @test_inferred reverse(v, i, j) SmallVector(v)
                else
                    @test_throws Exception reverse(v, i, j)
                end
            end
        end
    end
end

@testset "SmallVector push/pop" begin
    for V in VS, N in (1, 2, 9, 16), T in test_types, m in (0, 1, round(Int, 0.7*N), N-1, N)
        u = rand(T, m)
        v = V{N,T}(u)
        x = rand(T)
        y = rand(T)
        @test_inferred push(v) SmallVector(v)
        @test_inferred pushfirst(v) SmallVector(v)
        if length(u) == N
            @test_throws Exception push(v, x)
            @test_throws Exception push(v, x, y)
            @test_throws Exception pushfirst(v, x)
            @test_throws Exception pushfirst(v, x, y)
        else
            w = @test_inferred push(v, x) push!(copy(u), x) SmallVector(v)
            @test isvalid(w)
            w = @test_inferred pushfirst(v, x) pushfirst!(copy(u), x) SmallVector(v)
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
            w, _ = @test_inferred pop(v) (deleteat!(copy(u), length(u)), last(u)) (SmallVector(v), last(v))
            @test isvalid(w)
            w, _ = @test_inferred popfirst(v) (deleteat!(copy(u), 1), first(u)) (SmallVector(v), first(v))
            @test isvalid(w)
        end
        for i in (-1, 0, 1, 2, length(u), length(u)+1)
            if 1 <= i <= length(u)+1 && length(u) < N
                w = @test_inferred insert(v, i, x) insert!(copy(u), i, x) SmallVector(v)
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
                w = @test_inferred deleteat(v, i) deleteat!(copy(u), i) SmallVector(v)
                @test isvalid(w)
            else
                @test_throws Exception deleteat(v, i)
            end
        end
        @test_inferred append(v) SmallVector(v)
        @test_inferred prepend(v) SmallVector(v)
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
        if T <: Integer
            @test_inferred filter(isodd, v) filter(isodd, u) v
        end
    end
end

@testset "SmallVector push!/pop!" begin
    for V in (MutableSmallVector,), N in (1, 2, 9, 16), T in test_types, m in (0, 1, round(Int, 0.7*N), N-1, N)
        isbitstype(T) || continue
        u = rand(T, m)
        v = V{N,T}(u)
        x = rand(T)
        y = rand(T)
        @test_inferred push!(copy(v)) v
        @test_inferred pushfirst!(copy(v)) v
        if length(u) == N
            @test_throws Exception push!(copy(v), x)
            @test_throws Exception push!(copy(v), x, y)
            @test_throws Exception pushfirst!(copy(v), x)
            @test_throws Exception pushfirst!(copy(v), x, y)
        else
            w = @test_inferred push!(copy(v), x) push!(copy(u), x) v
            @test isvalid(w)
            w = @test_inferred pushfirst!(copy(v), x) pushfirst!(copy(u), x) v
            @test isvalid(w)
            if length(u) <= N-2
                w = @test_inferred push!(copy(v), x, y) push!(push!(copy(v), x), y)
                @test isvalid(w)
                w = @test_inferred pushfirst!(copy(v), x, y) pushfirst!(pushfirst!(copy(v), y), x)
                @test isvalid(w)
            end
        end
        if isempty(u)
            @test_throws Exception pop!(copy(v))
            @test_throws Exception popfirst!(copy(v))
        else
            @test_inferred pop!(copy(v)) pop!(copy(u)) T
            @test_inferred popfirst!(copy(v)) popfirst!(copy(u)) T
        end
        for i in (-1, 0, 1, 2, length(u), length(u)+1)
            if 1 <= i <= length(u)+1 && length(u) < N
                w = @test_inferred insert!(copy(v), i, x) insert!(copy(u), i, x) v
                @test isvalid(w)
                if i <= length(u)
                    w = @test_inferred duplicate!(copy(v), i) insert!(copy(v), i, v[i])
                    @test isvalid(w)
                else
                    @test_throws Exception duplicate!(copy(v), i)
                end
            else
                @test_throws Exception insert!(copy(v), i, x)
                @test_throws Exception duplicate!(copy(v), i)
            end
            if 1 <= i <= length(u)
                w = @test_inferred deleteat!(copy(v), i) deleteat!(copy(u), i) v
                @test isvalid(w)
            else
                @test_throws Exception deleteat!(copy(v), i)
            end
        end
        @test_inferred append!(v) v
        @test_inferred prepend!(v) v
        xy = [x, y]
        if length(u) <= N-2
            w = @test_inferred append!(copy(v), SmallVector{4}(xy)) push!(copy(v), x, y)
            @test isvalid(w)
            w = @test_inferred append!(copy(v), xy[i] for i in 1:2) push!(copy(v), x, y)
            @test isvalid(w)
            w = @test_inferred append!(copy(v), (x,), [y]) push!(copy(v), x, y)
            @test isvalid(w)
            w = @test_inferred prepend!(copy(v), SmallVector{4}(xy)) pushfirst!(copy(v), x, y)
            @test isvalid(w)
            w = @test_inferred prepend!(copy(v), xy[i] for i in 1:2) pushfirst!(copy(v), x, y)
            @test isvalid(w)
            w = @test_inferred prepend!(copy(v), (x,), [y]) pushfirst!(copy(v), x, y)
            @test isvalid(w)
        else
            @test_throws Exception append!(copy(v), SmallVector{4}(xy))
            @test_throws Exception append!(copy(v), xy[i] for i in 1:2)
            @test_throws Exception append!(copy(v), (x,), [y])
            @test_throws Exception prepend!(copy(v), SmallVector{4}(xy))
            @test_throws Exception prepend!(copy(v), xy[i] for i in 1:2)
            @test_throws Exception prepend!(copy(v), (x,), [y])
        end
        if T <: Integer
            @test_inferred filter!(isodd, copy(v)) filter!(isodd, copy(u)) v
        end
    end
end

using Base.FastMath: mul_fast

@testset "SmallVector add/mul" begin
    for V in VS, N in (1, 2, 9, 16), T1 in test_types, m in (1, round(Int, 0.7*N), N-1, N)
        T1 <: Number || continue
        if T1 <: Unsigned
            u1 = rand(T1(1):T1(9), m)
        else
            u1 = rand(T1(-9):T1(9), m)
        end
        v1 = V{N}(u1)
        w = @test_inferred +v1 u1 v1
        @test isvalid(w)
        w = @test_inferred -v1 -u1 SmallVector(v1)
        @test isvalid(w)
        for T2 in test_types
            T2 <: Number || continue
            if T2 <: Unsigned
                u2 = rand(T2(1):T2(9), m)
                c = rand(T2(1):T2(9))
            else
                u2 = rand(T2(-9):T2(9), m)
                c = rand(T2(-9):T2(9))
            end
            v2 = V{N}(u2)
            T = promote_type(T1, T2)
            for op in (+, -)
                w = @test_inferred op(v1, v2) op(u1, u2) SmallVector{N,T}
                @test isvalid(w)
                v3 = V{N+4}(u2)
                w = @test_inferred op(v1, v3) op(u1, u2) SmallVector{N,T}
                @test isvalid(w)
                w = @test_inferred op(v3, v1) op(u2, u1) SmallVector{N,T}
                @test isvalid(w)
            end
            w = @test_inferred c*v1 c*u1 SmallVector{N,T}
            @test isvalid(w)
            if T <: Unsigned && (minimum(v1; init = zero(T1)) < 0 ||
                (c < 0 && !(isempty(v1) && SmallCollections.MapStyle(mul_fast, T2, T1) isa SmallCollections.DefaultMapStyle)))
                # Julia bug, see julia#58188
                @test_broken mul_fast(c, v1) == mul_fast.(c, u1)
            else
                w = @inferred mul_fast(c, v1)
                @test isapprox(w, mul_fast.(c, u1)) && w isa SmallVector{N,T}
                @test isvalid(w)
            end
            @test_inferred v1*c c*v1
        end
    end

    N = 8
    T = Float64
    u = T[-Inf, -1, 0, 1, Inf, NaN]
    for V in VS
        v = V{8,Float64}(u)
        for c in (Inf, -Inf, NaN)
            w = @test_inferred c*v c*u SmallVector{N,T}
            @test isvalid(w)
        end
    end
end

@testset "SmallVector sum/max" begin
    for V in VS, N in (1, 2, 9, 16), T in test_types, m in (0, 1, round(Int, 0.7*N), N-1, N)
        T <: Number || continue
        if T <: Unsigned
            u = rand(T(1):T(9), m)
        else
            u = rand(T(-9):T(9), m)
        end
        v = V{N}(u)
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
        u = fill(-T(0), m)
        v = V{N}(u)
        @test_inferred sum(v) sum(u)
        @test_inferred prod(-v) prod(-u)
    end
    for V in VS, N in (5, 16), T in (Float32, Float64), x in (Inf, -Inf, NaN)
        u = T[x, -1, 0, 1]
        v = V{N}(u)
        @test_inferred maximum(v) maximum(u)
        @test_inferred minimum(v) minimum(u)
        @test_inferred sum(v) sum(u)
        if isnan(prod(u))
            @test_inferred isnan(prod(v)) true
        else
            @test_inferred prod(v) prod(u)
        end
    end
    for V in VS, N in (5, 16), T in (Float32, Float64)
        u = T[NaN, -1, 0, 1]
        v = V{N}(u)
        @test_inferred isnan(maximum(v)) true
        @test_inferred isnan(minimum(v)) true
        @test_inferred isnan(sum(v)) true
        @test_inferred isnan(prod(v)) true
    end
end

@testset "SmallVector map" begin
    f(x) = Int32(2)*x
    f(x, y) = 2*x + y
    g(x) = iszero(x) ? 1 : 1.0
    for V in VS, N in (1, 2, 9, 16), T1 in test_types, m in (0, 1, round(Int, 0.7*N), N-1)
        T1 <: Number || continue
        u1 = rand(T1, m)
        v1 = V{N}(u1)
        u3 = map(f, u1)
        w = @test_inferred map(f, v1) u3 SmallVector{N,eltype(u3)}
        @test isvalid(w)
        for T2 in test_types
            T2 <: Number || continue
            u2 = rand(T2, m+1)
            v2 = V{N+2}(u2)
            u4 = map(f, u1, u2)
            w = @test_inferred map(f, v1, v2) u4 SmallVector{N,eltype(u4)}
            @test isvalid(w)
        end
    end
    for V in VS,  m in (0, 1, 3)
        v = V{8}(1:m)
        u = collect(v)
        u5 = map(g, u)
        w = map(g, v)
        @test w == u5
        @test eltype(w) == eltype(u5)
    end
end

@testset "SmallVector rest" begin
    for V in VS
        v = V{8}(1:2)
        W = typeof(SmallVector(v))
        w..., = v
        @test w == v && w isa W && isvalid(w)
        x1, w... = v
        @test w == v[2:end] && w isa W && isvalid(w)
        x1, x2, w... = v
        @test w == v[3:end] && w isa W && isvalid(w)
        @test_throws Exception x1, x2, x3, w... = v

        if VERSION >= v"1.9"
            v = V{8,UInt8}(1:3)
            W = typeof(SmallVector(v))
            w..., y1 = v
            @test w == v[1:end-1] && w isa W && isvalid(w) && y1 === v[end]
            x1, w..., y1 = v
            @test w == v[2:end-1] && w isa W && isvalid(w) && y1 === v[end]
            x1, x2, w..., y1 = v
            @test w == v[3:end-1] && w isa W && isvalid(w) && y1 === v[end]
            @test_throws Exception x1, x2, x3, w..., y1 = v

            v = SmallVector{8,Int16}(1:4)
            W = typeof(SmallVector(v))
            w..., y1, y2 = v
            @test w == v[1:end-2] && w isa W && isvalid(w) && y1 === v[end-1] && y2 === v[end]
            x1, w..., y1, y2 = v
            @test w == v[2:end-2] && w isa W && isvalid(w) && y1 === v[end-1] && y2 === v[end]
            x1, x2, w..., y1, y2 = v
            @test w == v[3:end-2] && w isa W && isvalid(w) && y1 === v[end-1] && y2 === v[end]
            @test_throws Exception x1, x2, x3, w..., y1, y2 = v
        end
    end
end

@testset "SmallVector support" begin
    for V in VS, N in (1, 2, 9, 16), T in test_types, m in (0, 1, round(Int, 0.7*N), N-1, N)
        T <: Number || continue
        u = rand(0:2, m)
        v = V{N,T}(u)
        @test_inferred support(v) Set{Int}(i for i in 1:m if u[i] != 0) SmallBitSet
    end
end

@testset "broadcast" begin
    N = 8
    for V in VS, T in (Int, Float64), m in (0, 1, 3, 8)
        u = collect(T, 1:m)
        v = V{N}(u)
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

    for V in VS
        u = [7, 8]
        v = V{3}(u)
        a = [1 2; 3 4]
        @test a .+ v == a .+ u

        u = ['a', 'b', 'c']
        v = V{5}(u)
        w = v .* 'x'
        @test w == u .* 'x' && w isa SmallVector{5,String}
    end
end
