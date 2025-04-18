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
using Base: Fix1, Fix2

function benchmark_set(::Val{N}, ::Type{U}, ::Type{T}, M) where {N,U,T}
    R = 1:N

    pp = [sizehint!(Set{T}(rand(R, rand(1:N÷2))), N) for M in 1:M]
    qq = [sizehint!(Set{T}(rand(R, rand(1:N÷2))), N) for M in 1:M]

    pq = [(pp, qq),
        (map(MutableSmallSet{N}, pp), map(MutableSmallSet{N}, qq)),
        (map(SmallSet{N}, pp), map(SmallSet{N}, qq)),
        (map(BitSet, pp), map(BitSet, qq)),
        (map(SmallBitSet{U}, pp), map(SmallBitSet{U}, qq)),
    ]

    c = [rand(T(1):T(N)) for _ in 1:M]

    a = fill("", length(pq), 12)

    for (i, (p, q)) in enumerate(pq)
        a[i, 1] = string('`', eltype(p), '`')
        a[i, 2] = @bs sum(sum, $p)
        a[i, 3] = if eltype(p) <: Union{SmallSet,SmallBitSet}
            @bs similar(p) map!(push, _, $p, $c) evals = 1
        else
            @bs deepcopy(p) foreach(push!,  _, $c) evals = 1
        end
        a[i, 4] = if eltype(p) <: Union{SmallSet,SmallBitSet}
            @bs similar(p) map!(first∘pop, _, $p) evals = 1
        else
            @bs deepcopy(p) foreach(pop!, _) evals = 1
        end
        a[i, 5] = if eltype(p) <: Union{SmallSet,SmallBitSet}
            @bs similar(p) map!(union, _, $p, $q)
        else
            @bs foreach(union!, $p, $q) evals = 1
        end
        a[i, 6] = if eltype(p) <: Union{SmallSet,SmallBitSet}
            @bs similar(p) map!(intersect, _, $p, $q)
        else
            @bs foreach(intersect!, $p, $q) evals = 1
        end
        a[i, 7] = if eltype(p) <: Union{SmallSet,SmallBitSet}
            @bs similar(p) map!(setdiff, _, $p, $q)
        else
            @bs foreach(setdiff!, $p, $q) evals = 1
        end
        a[i, 8] = if eltype(p) <: Union{SmallSet,SmallBitSet}
            @bs similar(p) map!(symdiff, _, $p, $q)
        else
            @bs foreach(symdiff!, $p, $q) evals = 1
        end
        r = deepcopy(p)
        a[i, 9] = @bs similar(p, Bool) map!(issubset, _, $p, $r)
        a[i, 10] = if eltype(p) <: Union{SmallSet,SmallBitSet}
            @bs similar(p) map!((v, x) -> filter(>(x), v), _, $p, $c)
        else
            @bs foreach((v, x) -> filter!(>(x), v), $p, $c) evals = 1
        end
        a[i, 11] = @bs similar(p, Bool) map!(==, _, $p, $r)
        a[i, 12] = @bs similar(p, Bool) map!(in, _, $c, $p)
    end
    return a
end

function make_table_set(a)
    b = ["| " * join(a[i, :], " | ") * " |" for i in axes(a, 1)]

    c = """
        | type | sum | push | pop | union | intersect | setdiff | symdiff | issubset | filter | equal | in |
        | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
        """

    c *= join(b, '\n') * '\n'

    c = replace(c, r"\((\d)[^)]*\)" => s"**(\1)**", r"\bns\b" => "**ns**")
end

function make_table_set_raw(a)
    cols = [1, 3, 6, 9, 12]
    b = ["| " * join(a[i, cols], " | ") * " |" for i in axes(a, 1)]

    c = """
        | type | `push(!)` | `intersect(!)` | `issubset` | `in` |
        | --- | --- | --- | --- | --- |
        """

    c *= join(b, '\n') * '\n'

    c = replace(c, r"\((\d)[^)]*\)" => s"**(\1)**", r"\bns\b" => "**ns**")
end

M = 1000

for (N, U, T) in [(16, UInt16, Int16), (32, UInt32, Int16), (32, UInt32, Int8), (64, UInt64, Int8)]
    bs = benchmark_set(Val(N), U, T, M)
    display(parse(make_table_set(bs)))
    println()
    println(make_table_set_raw(bs))
    println()
end
