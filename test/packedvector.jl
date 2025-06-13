using SmallCollections: bitsize

function checkvalue(::Type{Bool}, N, x::T) where T
    @assert bitsize(T) >= N
    if bitsize(T) == N
        true
    elseif T <: Signed
        -one(T) << (N-1) <= x < one(T) << (N-1)
    else
        x < one(T) << N
    end
end

function packed_rand(N, T)
    if T <: Unsigned || T == Bool
        rand(T(0):T(BigInt(2)^N-1))
    else
        rand(T(-BigInt(2)^(N-1)):T(BigInt(2)^(N-1)-1))
    end
end

packed_rand(N, T, n) = T[packed_rand(N, T) for _ in 1:n]

@testset "PackedVector" begin
    for T in (Bool, Int8, UInt16, Int64, UInt128), N in (1, 2, 5, 8, max(1, bitsize(T)÷2-1), bitsize(T)), U in (UInt8, UInt32, UInt64, UInt128)
        if bitsize(T) < N
            @test_throws Exception PackedVector{U,N,T}()
            continue
        end
        c = bitsize(U)÷N
        c == 0 && continue
    for m in (0, 1, round(Int, 0.7*c), c-1, c)
        u = packed_rand(N, T, m)
        v = @inferred PackedVector{U,N,T}(u)
        @test v === @inferred copy(v)
        @test_inferred capacity(v) c Int
        @test_inferred v == u true
        @test isvalid(v)
        @test_inferred collect(v) u Vector{T}
        v2 = PackedVector{U,N,T}(u)
        @test_inferred v == v2 true
        if (N+1)*m <= bitsize(U) && N+1 <= bitsize(T)
            v3 = PackedVector{U,N+1,T}(u)
            @test_inferred v == v3 true
        end
        if !isempty(u)
            i = rand(1:m)
            x = packed_rand(N, T)
            while x == v[i]
                x = packed_rand(N, T)
            end
            v5 = setindex(v, x, i)
            @test_inferred v == v5 false
        end
        if m < c
            v6 = PackedVector{U,N,T}(push!(copy(u), packed_rand(N, T)))
            @test_inferred v == v6 false
        end
        if !isempty(u)
            u7 = copy(u)
            pop!(u7)
            v7 = PackedVector{U,N,T}(u7)
            @test_inferred v == v7 false
        end
        @test_inferred hash(v) hash(u) UInt
        if bitsize(U) < bitsize(UInt256)
            v1 = PackedVector{UInt256,N,T}(u)
            @test_inferred fasthash(v) fasthash(v1) UInt
        end
        let uu = map(x -> clamp(x, 0, BigInt(2)^(N-1)-1), u)
            w1 = PackedVector{U,N,signed(T)}(uu)
            w2 = PackedVector{U,N,unsigned(T)}(uu)
            @test_inferred fasthash(w1) fasthash(w2) UInt
        end
        @test_inferred length(v) length(u) Int
        @test_inferred PackedVector{U,N,T}() PackedVector{U,N,T}(())
        @test_inferred empty(v) PackedVector{U,N,T}()
        N <= bitsize(Int) && @test_inferred empty(v, Int) PackedVector{U,N,Int}()
    end
    end
end

@testset "PackedVector indices" begin
    for T in (Bool, Int8, UInt16, Int64, UInt128), N in (1, 2, 5, 8, max(1, bitsize(T)÷2-1), bitsize(T)), U in (UInt8, UInt32, UInt64, UInt128)
        bitsize(T) < N && continue
        c = bitsize(U)÷N
        c == 0 && continue
    for m in (0, 1, round(Int, 0.7*c), c-1, c)
        u = packed_rand(N, T, m)
        v = @inferred PackedVector{U,N,T}(u)
        if isempty(u)
            @test_throws Exception first(v)
            @test_throws Exception last(v)
        else
            @test_inferred first(v) first(u) T
            @test_inferred last(v) last(u) T
        end
        x = packed_rand(N, T)
        for i in -1:length(u)+1
            if 1 <= i <= length(u)
                @test_inferred v[i] u[i] T
                w = @test_inferred setindex(v, x, i) setindex!(copy(u), x, i) v
                @test isvalid(w)
            else
                @test_throws Exception v[i]
                @test_throws Exception setindex(v, x, i)
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
end

@testset "PackedVector zeros" begin
    for T in (Bool, Int8, UInt16, Int64, UInt128), N in (1, 2, 5, 8, max(1, bitsize(T)÷2-1), bitsize(T)), U in (UInt8, UInt32, UInt64, UInt128)
        bitsize(T) < N && continue
        c = bitsize(U)÷N
        c == 0 && continue
    for m in (0, 1, round(Int, 0.7*c), c-1, c)
        u = zeros(T, m)
        v = PackedVector{U,N,T}(u)
        @test_inferred iszero(v) true
        w = @test_inferred zero(v) u v
        @test isvalid(w)
        w = @test_inferred zeros(PackedVector{U,N,T}, m) v
        @test isvalid(w)
        T <: Signed && N == 1 && continue
        w = @test_inferred ones(PackedVector{U,N,T}, m) ones(T, m) PackedVector{U,N,T}
        @test isvalid(w)
    end
    end
end

@testset "PackedVector push/pop" begin
    for T in (Bool, Int8, UInt16, Int64, UInt128),
            N in (1, 2, 5, 8, max(1, bitsize(T)÷2-1), bitsize(T)),
            U in (UInt8, UInt32, UInt64, UInt128)
        bitsize(T) < N && continue
        c = bitsize(U)÷N
        c == 0 && continue
    for m in (0, 1, round(Int, 0.7*c), c-1, c)
        u = packed_rand(N, T, m)
        v = @inferred PackedVector{U,N,T}(u)
        x = packed_rand(N, T)
        y = packed_rand(N, T)
        @test_inferred push(v) v
        @test_inferred pushfirst(v) v
        if length(u) == c
            @test_throws Exception push(v, x)
            @test_throws Exception push(v, x, y)
            @test_throws Exception pushfirst(v, x)
            @test_throws Exception pushfirst(v, x, y)
        else
            w = @test_inferred push(v, x) push!(copy(u), x) v
            @test isvalid(w)
            w = @test_inferred pushfirst(v, x) pushfirst!(copy(u), x) v
            @test isvalid(w)
            if length(u) <= c-2
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
            if 1 <= i <= length(u)+1 && length(u) < c
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
        if length(u) <= c-2
            w = @test_inferred append(v, PackedVector{U,N,T}(xy)) push(v, x, y)
            @test isvalid(w)
            w = @test_inferred append(v, xy[i] for i in 1:2) push(v, x, y)
            @test isvalid(w)
            w = @test_inferred append(v, (x,), [y]) push(v, x, y)
            @test isvalid(w)
            w = @test_inferred prepend(v, PackedVector{U,N,T}(xy)) pushfirst(v, x, y)
            @test isvalid(w)
            w = @test_inferred prepend(v, xy[i] for i in 1:2) pushfirst(v, x, y)
            @test isvalid(w)
            w = @test_inferred prepend(v, (x,), [y]) pushfirst(v, x, y)
            @test isvalid(w)
        else
            @test_throws Exception append(v, PackedVector{U,N,T}(xy))
            @test_throws Exception append(v, xy[i] for i in 1:2)
            @test_throws Exception append(v, (x,), [y])
            @test_throws Exception prepend(v, PackedVector{U,N,T}(xy))
            @test_throws Exception prepend(v, xy[i] for i in 1:2)
            @test_throws Exception prepend(v, (x,), [y])
        end
        if T <: Integer
            @test_inferred filter(isodd, v) filter(isodd, u) v
        end
    end
    end
end

@testset "PackedVector circshift" begin
    for U in (UInt8, UInt16, UInt32, UInt64, UInt128),
            T in (Int8, UInt8, Int16, UInt16, Int32, UInt32),
            N in 1:3:bitsize(T)
        c = bitsize(U)÷N
        c == 0 && continue
        for n in 0:4:c
            w = packed_rand(N, T, n)
            v = PackedVector{U,N,T}(w)
            for k in (-2*c, -2*c+1, -3, -1, 0, 1, 7, c+5, 2*c+7)
                @test_inferred circshift(v, k) circshift(w, k) v
                @test isvalid(circshift(v, k))
            end
        end
    end
end

function red_mod(N, v::AbstractVector{T}) where T <: Integer
    k = bitsize(T)-N
    map(x -> (x << k) >> k, v)
end

@testset "PackedVector add/mul" begin
    for U in (UInt8, UInt16, UInt32, UInt64, UInt128),
            T in (Int8, UInt8, Int16, UInt16, Int32, UInt32),
            N in 1:bitsize(T)
        c = bitsize(U)÷N
        c == 0 && continue
        for n in 0:c
            u1 = packed_rand(N, T, n)
            v1 = PackedVector{U,N,T}(u1)
            u2 = packed_rand(N, T, n)
            v2 = PackedVector{U,N,T}(u2)
            w = @test_inferred +v1 red_mod(N, +u1) v1
            @test isvalid(w)
            w = @test_inferred -v1 red_mod(N, -u1) v1
            @test isvalid(w)
            w = @test_inferred v1+v2 red_mod(N, u1+u2) v1
            @test isvalid(w)
            w = @test_inferred v1-v2 red_mod(N, u1-u2) v1
            @test isvalid(w)
            cc = packed_rand(N, T)
            w = @test_inferred cc*v1 red_mod(N, cc*u1) v1
            @test isvalid(w)
            for i in -1:length(u1)+1
                x = packed_rand(N, T)
                if checkbounds(Bool, u1, i) && checkvalue(Bool, N, u1[i]+x)
                    w = @test_inferred addindex(v1, x, i) setindex!(copy(u1), u1[i]+x, i) v1
                    @test isvalid(w)
                else
                    @test_throws Exception addindex(v1, x, i)
                end
            end
        end
    end
end

@testset "PackedVector sum/max" begin
    for U in (UInt8, UInt16, UInt32, UInt64, UInt128),
        T in (Bool, Int8, UInt8, Int16, UInt16, Int32, UInt32),
        N in 1:bitsize(T)
        c = bitsize(U)÷N
        c == 0 && continue
        for n in 0:c
            u = packed_rand(N, T, n)
            v = PackedVector{U,N,T}(u)
            @test_inferred sum(v) sum(u)
            for f in (maximum, minimum)
                if isempty(u)
                    @test_throws Exception f(v)
                    @test_inferred f(v; init = zero(T)) f(u; init = zero(T))
                else
                    @test_inferred f(v) f(u)
                end
            end
        end
    end
end

@testset "PackedVector rest" begin
    v = PackedVector{UInt64,4,Int16}(1:2)
    w..., = v
    @test w == v && typeof(w) == typeof(v) && isvalid(w)
    x1, w... = v
    @test w == v[2:end] && typeof(w) == typeof(v) && isvalid(w)
    x1, x2, w... = v
    @test w == v[3:end] && typeof(w) == typeof(v) && isvalid(w)
    @test_throws Exception x1, x2, x3, w... = v

    if VERSION >= v"1.9"
        v = PackedVector{UInt32,5,UInt8}(1:3)
        w..., y1 = v
        @test w == v[1:end-1] && typeof(w) == typeof(v) && isvalid(w) && y1 === v[end]
        x1, w..., y1 = v
        @test w == v[2:end-1] && typeof(w) == typeof(v) && isvalid(w) && y1 === v[end]
        x1, x2, w..., y1 = v
        @test w == v[3:end-1] && typeof(w) == typeof(v) && isvalid(w) && y1 === v[end]
        @test_throws Exception x1, x2, x3, w..., y1 = v

        v = PackedVector{UInt128,7,Int32}(1:4)
        w..., y1, y2 = v
        @test w == v[1:end-2] && typeof(w) == typeof(v) && isvalid(w) && y1 === v[end-1] && y2 === v[end]
        x1, w..., y1, y2 = v
        @test w == v[2:end-2] && typeof(w) == typeof(v) && isvalid(w) && y1 === v[end-1] && y2 === v[end]
        x1, x2, w..., y1, y2 = v
        @test w == v[3:end-2] && typeof(w) == typeof(v) && isvalid(w) && y1 === v[end-1] && y2 === v[end]
        @test_throws Exception x1, x2, x3, w..., y1, y2 = v
    end
end

@testset "PackedVector support" begin
    for U in (UInt8, UInt32, UInt128), T in (Int8, UInt32), N in 1:bitsize(T)
        c = bitsize(U)÷N
        c == 0 && continue
        for m in 0:min(c, bitsize(UInt))
            u = T <: Unsigned ? rand(T(0):T(1), m) : rand(T(-1):T(0), m)
            v = @inferred PackedVector{U,N,T}(u)
            @test_inferred support(v) Set{Int}(i for i in 1:m if u[i] != 0) SmallBitSet
        end
    end
end

@testset "PackedVector rand" begin
    for U in (UInt8, UInt32, UInt128), T in (Bool, Int8, UInt32), M in 1:3:bitsize(T)
        c = bitsize(U)÷M
        c == 0 && continue
        v = @inferred rand(PackedVector{U,M,T})
        @test v isa PackedVector{U,M,T} && isvalid(v)
    end
end
