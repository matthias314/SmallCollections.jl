using Chairmarks

macro bs(args...)
    b = esc(Expr(:macrocall, Symbol("@b"), __source__, args...))
    quote
        io = IOBuffer()
        show(io, MIME"text/plain"(), $b)
        String(take!(io))
    end
end

using Markdown: parse

using SmallCollections

function benchmark_dict(::Val{N}, ::Type{T}, M) where {N,T}
    pp = [MutableSmallDict{N,T,T}(rand(T) => k for k in 1:N-2) for _ in 1:M]

    pq = [map(d -> sizehint!(Dict(d), 2*N), pp), pp, map(SmallDict, pp)]

    k = map(rand, map(collect∘keys, pp))
    v = map(rand, map(collect∘values, pp))
    np = [Pair{T,T}(rand(T), rand(T)) for _ in 1:M]
    npk = map(first, np)
    npv = map(last, np)

    a = fill("", length(pq), 11)

    for (i, p) in enumerate(pq)
        D = eltype(p)

        a[i, 1] = string('`', eltype(p), '`')

        e = [rand(T) for _ in 1:M]
        a[i, 2] = if D <: Dict
            @bs similar(p) map!(y -> Dict{T,T}(k+y => k-y for k in T(1):T(N)), _, $e)
        elseif D <: SmallDict
            @bs similar(p) map!(y -> SmallDict{N,T,T}(k+y => k-y for k in T(1):T(N)), _, $e)
        elseif D <: MutableSmallDict
            @bs similar(p) map!(y -> MutableSmallDict{N,T,T}(k+y => k-y for k in T(1):T(N)), _, $e)
        end

        a[i, 3] = @bs similar(v) map!(getindex, _, $p, $k)

        a[i, 4] = if D <: AbstractSmallDict
            @bs similar(k) map!(invget, _, $p, $v)
            # @bs sum(splat(invget), zip($p, $v))
        else
            "n/a"
        end

        a[i, 5] = if D <: SmallDict
            @bs similar(p) map!(setindex, _, $p, $npv, $npk)
        else
            @bs deepcopy(p) foreach((d, v, k) -> setindex!(d, v, k), _, $npv, $npk) evals = 1
        end

        a[i, 6] = if D <: SmallDict
            @bs similar(p) map!(first∘pop, _, $p, $k)
        else
            @bs deepcopy(p) foreach(pop!, _, $k) evals = 1
        end

        a[i, 7] = @bs similar(p, Int) map!(d -> sum(p -> first(p)+last(p), d), _, $p)
    end

    return a
end

function make_table_dict(a)
    b = ["| " * join(a[i, :], " | ") * " |" for i in axes(a, 1)]

    c = """
        | type | create itr | getindex | invget | setindex(!) | pop(!) | iterate |
        | --- | --- | --- | --- | --- | --- | --- |
        """

    c *= join(b, '\n') * '\n'

    # c = replace(c, r"000 allocs: [^)]*" => " A")
    c = replace(c, r"\((\d)[^)]*\)" => s"**(\1)**", r"\bns\b" => "**ns**")
    return c
end

function make_table_dict_raw(a)
    cols = [1, 3, 4, 5, 6, 7]
    b = ["| " * join(a[i, cols], " | ") * " |" for i in axes(a, 1)]

    c = """
        | type | `getindex` | `invget` | `setindex(!)` | `pop(!)` | `iterate` |
        | --- | --- | --- | --- | --- | --- |
        """

    c *= join(b, '\n') * '\n'

    # c = replace(c, r"000 allocs: [^)]*" => " A")
    c = replace(c, r"\((\d)[^)]*\)" => s"**(\1)**", r"\bns\b" => "**ns**")
    return c
end

M = 1000

for (N, T) in [(16, Int16), (32, Int16), (32, Int8), (64, Int8)]
    bs = benchmark_dict(Val(N), T, M)
    display(parse(make_table_dict(bs)))
    println()
    println(make_table_dict_raw(bs))
    println()
end
