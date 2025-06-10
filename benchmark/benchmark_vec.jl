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

using SmallCollections, StaticArrays, FixedSizeArrays, Collects
using SmallCollections: push, pop
using Base: Fix1, Fix2

newcollect(v::Vector{T}, w) where T = collect(T, w)
newcollect(v::V, w) where V <: AbstractVector = V(w)

newsum(v) = sum(v)
newsum(v::Union{AbstractFixedVector,AbstractSmallVector}) = sum_fast(v)

function benchmark_vec(::Val{N}, ::Type{T}, M) where {N,T}
    pp = [sizehint!(rand(T, rand(1:N-1)), N) for _ in 1:M]
    qq = [sizehint!(rand(T, length(pp[k])), N) for k in 1:M]
    pp2 = [rand(T, N) for _ in 1:M]
    qq2 = [rand(T, N) for k in 1:M]

    pq = [(pp, qq),
        (map(FixedSizeVectorDefault, pp2), map(FixedSizeVectorDefault, qq2)),
        (map(MutableSmallVector{N}, pp), map(MutableSmallVector{N}, qq)),
        (map(MutableFixedVector{N}, pp2), map(MutableFixedVector{N}, qq2)),
        (map(MVector{N}, pp2), map(MVector{N}, qq2)),
        (map(SmallVector{N}, pp), map(SmallVector{N}, qq)),
        (map(FixedVector{N}, pp2), map(FixedVector{N}, qq2)),
        (map(SVector{N}, pp2), map(SVector{N}, qq2)),
    ]

    a = fill("", length(pq), 11)

    for (i, (p, q)) in enumerate(pq)
        V = eltype(p)

        a[i, 1] = string('`', eltype(p), '`')

        # @bd similar(p) map!(newcollect, _, $p)
        r = map(collect, p)
        a[i, 2] = @bs similar(p) map!(newcollect, _, $p, $r)

        e = [rand(T) for _ in 1:M]
        # a[i, 3] = @bs similar(p) map!(v -> newcollect(v, T(x) for x in 1:length(v)), _, $e)
        a[i, 3] = if V <: Vector
            @bs similar(p) map!(y -> collect(k+y for k in T(1):T(N)), _, $e)
        elseif V <: FixedSizeVector
            @bs similar(p) map!(y -> collect_as(FixedSizeVectorDefault{T}, k+y for k in T(1):T(N)), _, $e)
        elseif V <: MutableSmallVector
            @bs similar(p) map!(y -> MutableSmallVector{N,T}(k+y for k in T(1):T(N)), _, $e)
        elseif V <: SmallVector
            @bs similar(p) map!(y -> SmallVector{N,T}(k+y for k in T(1):T(N)), _, $e)
        elseif V <: MutableFixedVector
            @bs similar(p) map!(y -> MutableFixedVector{N,T}(k+y for k in T(1):T(N)), _, $e)
        elseif V <: FixedVector
            @bs similar(p) map!(y -> FixedVector{N,T}(k+y for k in T(1):T(N)), _, $e)
        elseif V <: MVector
            @bs similar(p) map!(y -> MVector{N,T}(k+y for k in T(1):T(N)), _, $e)
        elseif V <: SVector
            @bs similar(p) map!(y -> SVector{N,T}(k+y for k in T(1):T(N)), _, $e)
        end

        a[i, 4] = if false # V <: Union{AbstractFixedVector,AbstractSmallVector}
            @bs p sum(sum_fast, _)
        else
            @bs p sum(sum, _)
        end

        a[i, 5] = if V <: MutableFixedVector
            @bs similar(p, FixedVector{N,T}) map!(+, _, $p, $q)
        elseif V <: MutableSmallVector
            @bs similar(p, SmallVector{N,T}) map!(+, _, $p, $q)
        elseif V <: MVector
            @bs similar(p, SVector{N,T}) map!((x, y) -> SVector{N,T}(x+y), _, $p, $q)
        else
            @bs similar(p) map!(+, _, $p, $q)
        end

        a[i, 6] = if V <: Union{Vector,FixedSizeVector,MutableSmallVector,MVector,MutableFixedVector}
            @bs deepcopy(p) for (v, w) in zip(_, $q) v .+= w end evals = 1
        else
            "n/a"
        end

        c = map(v -> v[(length(v)+1)÷2], p)
        a[i, 7] = if V <: Union{Vector,MutableSmallVector}
            @bs deepcopy(p) for (v, x) in zip(_, $c) push!(v, x) end evals = 1
        elseif V <: SmallVector
            @bs copy(p) map!(SmallCollections.push, _, $p, $c)
        elseif V <: SVector
            @bs similar(p, SVector{N+1,T}) map!(StaticArrays.push, _, $p, $c)
        elseif V <: MVector
            @bs similar(p, MVector{N+1,T}) map!(StaticArrays.push, _, $p, $c)
        else
            "n/a"
        end

        a[i, 8] = if V <: Union{Vector,MutableSmallVector}
            @bs deepcopy(p) foreach(pop!, _) evals = 1
        elseif V <: SmallVector
            @bs similar(p) map!(first∘SmallCollections.pop, _, $p)
        elseif V <: SVector
            @bs similar(p, SVector{N-1,T}) map!(StaticArrays.pop, _, $p)
        elseif V <: MVector
            @bs similar(p, MVector{N-1,T}) map!(StaticArrays.pop, _, $p)
        else
            "n/a"
        end

        # a[i, 9] = @bs similar(p, Int) map!((v, x) -> findfirst(==(x), v)::Int, _, $p, $c)
        e = rand(T)
        # a[i, 9] = @bs similar(p, Int) map!(Fix1(count, isodd), _, $p)
        a[i, 9] = @bs similar(p, Int) map!(Fix1(count, >($e)), _, $p)

        a[i, 10] = @bs similar(p, Bool) map!(==, _, $p, $q)
        a[i, 11] = @bs similar(p, Bool) map!(==, _, $p, $(deepcopy(p)))

        # a[i, 9] = @bs similar(p, Int) map!(Fix1(newcount, isodd), _, $p)
        # d = [rand(typemax(T)-10:typemax(T)) for _ in 1:1000]
        # a[i, 9] = @bs similar(p, Bool) map!((v, x) -> all(<(x), v), _, $p, $d)
        # a[i, 11] = @bs similar(p, Bool) map!(Fix1(any, iszero), _, $p)
    end

    return a
end

function make_table_vec(a)
    b = ["| " * join(a[i, :], " | ") * " |" for i in axes(a, 1)]

    c = """
        | type | create vec | create itr | `sum` | add | add! | `push(!)` | `pop(!)` | `count` | eq min | eq max |
        | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
        """

    c *= join(b, '\n') * '\n'

    c = replace(c, r"FixedSizeArray{([[:alnum:]]+), \d+, Memory{[[:alnum:]]+}}" => s"FixedSizeVectorDefault{\1}")

    # c = replace(c, r"000 allocs: [^)]*" => " A")
    c = replace(c, r"\((\d)[^)]*\)" => s"**(\1)**", r"\bns\b" => "**ns**")
    return c
end

function make_table_vec_raw(a)
    cols = [1, 5, 6, 4, 7, 9]
    b = ["| " * join(a[i, cols], " | ") * " |" for i in axes(a, 1)]

    c = """
        | type | `v + w` | `v .+= w` |`sum(v)` | `push(!)(v, c)` | `count(>(c), v)` |
        | --- | --- | --- | --- | --- | --- |
        """

    c *= join(b, '\n') * '\n'

    c = replace(c, r"FixedSizeArray{([[:alnum:]]+), \d+, Memory{[[:alnum:]]+}}" => s"FixedSizeVectorDefault{\1}")

    # c = replace(c, r"000 allocs: [^)]*" => " A")
    c = replace(c, r"\((\d)[^)]*\)" => s"**(\1)**", r"\bns\b" => "**ns**")
    return c
end

M = 1000

for (N, T) in [(16, Int16), (32, Int16), (32, Int8), (64, Int8)]
    bs = benchmark_vec(Val(N), T, M)
    display(parse(make_table_vec(bs)))
    println()
    println(make_table_vec_raw(bs))
    println()
end
