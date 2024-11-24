SS = (SmallSet, MutableSmallSet)

@testset "SmallSet" begin
    for S in SS, N in (1, 2, 9, 16), T in test_types, m in (0, 1, N-1, N)
        S == SmallSet || isbitstype(T) || continue
        v = T[rand(T) for _ in 1:m]
        n = length(unique(v))
        s = @test_inferred S{N,T}(v) Set{T}(v) S{N,T}

        @test_inferred capacity(s) N
        @test_inferred length(s) n
        @test_inferred Set(collect(s)) Set(v)

        t = Tuple(v)
        @test_inferred S{N,T}(t) Set{T}(t) S{N,T}
        w = unique(v)
        @test_inferred S{N,T}(w; unique = true) Set{T}(w) S{N,T}
        t = Tuple(w)
        @test_inferred S{N,T}(t; unique = true) Set{T}(t) S{N,T}
        d = Set{T}(v)
        @test_inferred S{N,T}(d) d S{N,T}
        s = SmallSet{N,T}(v)
        @test_inferred S{N,T}(s) s S{N,T}
        if isbitstype(T)
            s = MutableSmallSet{N,T}(v)
            @test_inferred S{N,T}(s) s S{N,T}
        end

        @test_inferred S{N}(v) Set(v) S{N,T}
        t = Tuple(v)
        if !isempty(t)
            @test_inferred S{N}(t) Set(t) S{N,T}
        end
        w = unique(v)
        @test_inferred S{N}(w; unique = true) Set(w) S{N,T}
        t = Tuple(w)
        if !isempty(t)
            @test_inferred S{N}(t; unique = true) Set(t) S{N,T}
        end
        d = Set{T}(v)
        @test_inferred S{N}(d) d S{N,T}
        s = SmallSet{N}(v)
        @test_inferred S{N,T}(s) s S{N,T}
        if isbitstype(T)
            s = MutableSmallSet{N,T}(v)
            @test_inferred S{N}(s) s S{N,T}
        end
    end
end

@testset "SmallSet in" begin
    for S in SS, N in (1, 2, 9, 16), T in test_types, m in (0, 1, N÷2, N)
        S == SmallSet || isbitstype(T) || continue
        T == TestEnum && length(instances(T)) <= m && continue
        v = T[rand(T) for _ in 1:m]
        s = S{N,T}(v)
        for x in v
            @test_inferred x in s true
        end
        y = rand_notin(T, s)
        @test_inferred y in s false
    end

    s = SmallSet{4,Float32}((0.0, 1.0, NaN))
    @test_inferred 1 in s true
    @test_inferred NaN in s true
    @test_inferred -0.0 in s false
end

@testset "SmallSet empty" begin
    for S in SS, N in (1, 2, 9, 16), T in test_types, m in (0, 1, N÷2, N)
        S == SmallSet || isbitstype(T) || continue
        T == TestEnum && length(instances(T)) <= m && continue
        v = T[rand(T) for _ in 1:m]
        s = S{N,T}(v)
        @test_inferred isempty(s) iszero(m)
        @test_inferred empty(s) S{N,T}()
        @test_inferred empty(s, Char) S{N,Char}()
        ismutable(s) || continue
        t = @inferred empty!(s)
        @test t === s & isempty(t)
    end
end

@testset "SmallSet push/pop" begin
    for S in SS, N in (1, 2, 9, 16), T in test_types, m in (0, 1, N÷2, N)
        S == SmallSet || isbitstype(T) || continue
        T == TestEnum && length(instances(T)) <= m && continue
        s = S{N,T}(rand_unique(T, m))
        x = rand_notin(T, s)
        if m == N
            @test_throws Exception push(s, x)
        else
            @test_inferred push(s, x) push!(Set(s), x) SmallSet{N,T}
            y = rand(T)
            if m <= N-2
                @test_inferred push(s, x, y) push!(Set(s), x, y) SmallSet{N,T}
            end
        end

        if m == 0
            @test_throws Exception pop(s)
        else
            (t, x) = @inferred pop(s)
            @test t isa SmallSet{N,T} && x isa T && !(x in t)
            @test push(t, x) == s
            @test push(s, x) == s

            @test_inferred pop(s, x) (t, x)
            @test_inferred delete(s, x) t
            T <: Union{Bool,Enum} && continue
            y = rand_notin(T, s)
            @test_throws Exception pop(s, y)
            @test_inferred delete(s, y) SmallSet(s)
            @test_inferred pop(s, x, y) (t, x)
            @test_inferred pop(s, y, x) (SmallSet(s), x)
        end
    end

    s = SmallSet{4}((0.0, 1.0))
    @test_inferred 1 in s true
    @test_inferred -0.0 in s false
    @test_throws Exception pop(s, -0.0)
    @test_inferred pop(s, 1) pop(s, 1.0)
    @test_inferred delete(s, 1) delete(s, 1.0)
    @test_inferred pop(s, 1, 2.0) pop(s, 1.0, 2.0)
end

@testset "SmallSet push!/pop!" begin
    for N in (1, 2, 9, 16), T in test_types, m in (0, 1, N÷2, N)
        isbitstype(T) || continue
        T == TestEnum && length(instances(T)) <= m && continue
        s = MutableSmallSet{N,T}(rand_unique(T, m))
        x = rand_notin(T, s)
        if m == N
            @test_throws Exception push!(copy(s), x)
        else
            t = copy(s)
            u = @test_inferred push!(t, x) push!(Set(s), x) t
            @test u === t
            y = rand(T)
            if m <= N-2
                @test_inferred push!(copy(s), x, y) push!(Set(s), x, y) s
            end
        end

        if m == 0
            @test_throws Exception pop!(copy(s))
        else
            t = copy(s)
            x = @inferred pop!(t)
            @test t isa MutableSmallSet{N,T} && x isa T && !(x in t)
            @test push!(copy(t), x) == s
            @test push!(copy(s), x) == s

            @test_inferred pop!(copy(s)) x
            u = copy(s)
            w = @test_inferred delete!(u, x) t
            @test w === u
            T <: Union{Bool,Enum} && continue
            y = rand_notin(T, s)
            @test_throws Exception pop!(copy(s), y)
            u = copy(s)
            w = @test_inferred delete!(u, y) s
            @test w === u
            u = copy(s)
            @test_inferred pop!(u, x, y) x
            @test !(x in u)
            u = copy(s)
            @test_inferred pop!(u, y, x) x
            @test u == s
        end
    end

    s = MutableSmallSet{4}((0.0, 1.0))
    @test_throws Exception pop!(copy(s), -0.0)
    @test_inferred pop!(copy(s), 1) pop!(copy(s), 1.0)
    @test_inferred delete!(copy(s), 1) delete!(copy(s), 1.0)
    @test_inferred pop!(copy(s), 1, 2.0) pop!(copy(s), 1.0, 2.0)
end

@testset "SmallSet filter" begin
    for S in SS, N in (1, 2, 9, 16), T in test_types, m in (0, 1, N÷2, N)
        S == SmallSet || isbitstype(T) || continue
        T == TestEnum && length(instances(T)) <= m && continue
        s = S{N,T}(rand_unique(T, m))
        if T <: Integer
            @test_inferred filter(isodd, s) filter(isodd, Set(s)) SmallSet(s)
        else
            x = rand_notin(T, s)
            @test_inferred filter(!=(x), s) SmallSet(s)
            @test_inferred filter(==(x), s) empty(SmallSet(s))
        end

        S == MutableSmallSet || continue
        if T <: Integer
            t = copy(s)
            u = @test_inferred filter!(isodd, t) filter!(isodd, Set(s)) t
            @test u === t
        else
            x = rand_notin(T, s)
            @test_inferred filter!(!=(x), s) s
            t = copy(s)
            u = @test_inferred filter!(==(x), t) empty(s)
            @test u === t
        end
    end
end

@testset "SmallSet union etc" begin
    for S in SS, T in test_types
        isbitstype(T) || continue
        T == TestEnum && length(instances(T)) <= 5 && continue
        N = 8
        v, w, x, y, z = rand_unique(T, 5)
        s = S{N,T}((v, w, x, y))
        t = S{N,T}((x, y, z))
        @test_inferred union(s, t) union(Set(s), Set(t)) MutableSmallSet{N,T}
        @test_inferred intersect(s, t) intersect(Set(s), Set(t)) MutableSmallSet{N,T}
        @test_inferred setdiff(s, t) setdiff(Set(s), Set(t)) MutableSmallSet{N,T}
        @test_inferred symdiff(s, t) symdiff(Set(s), Set(t)) MutableSmallSet{N,T}
    end
end

@testset "SmallSet union! etc" begin
    N = 8
    for T in test_types, S in [SmallSet{N,T}, MutableSmallSet{N,T}, Set{T}]
        isbitstype(T) || continue
        T == TestEnum && length(instances(T)) <= 5 && continue
        v, w, x, y, z = rand_unique(T, 5)
        s = MutableSmallSet{N,T}((v, w, x, y))
        t = S((x, y, z))
        u = copy(s)
        w = @test_inferred union!(u, t) union!(Set(s), Set(t)) s
        @test w === u
        u = copy(s)
        w = @test_inferred intersect!(u, t) intersect!(Set(s), Set(t)) s
        @test w === u
        u = copy(s)
        w = @test_inferred setdiff!(u, t) setdiff!(Set(s), Set(t)) s
        @test w === u
        u = copy(s)
        w = @test_inferred symdiff!(u, t) symdiff!(Set(s), Set(t)) s
        @test w === u
    end
end
