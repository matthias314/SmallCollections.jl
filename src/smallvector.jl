#
# small vectors
#

export SmallVector, setindex,
    push, pop, pushfirst, popfirst, insert, deleteat, popat,
    support, fasthash

import Base: show, ==, copy, empty,
    length, size, getindex, setindex,
    zero, zeros, ones,
    +, -, *, sum, prod, maximum, minimum

struct SmallVector{N,T} <: AbstractVector{T}
    b::Values{N,T}
    n::Int
end

function show(io::IO, v::SmallVector{N,T}) where {N,T}
    print(io, "$T[")
    join(io, v, ',')
    print(io, ']')
end

function ==(v::SmallVector, w::SmallVector)
    length(v) == length(w) && iszero(padded_sub(v.b, w.b))
end

#=
function ==(v::SmallVector, w::SmallVector)
    length(v) == length(w) && all(splat(==), zip(v.b, w.b))
end
=#

fasthash(v::SmallVector, h0::UInt) = hash(bits(v.b), hash(length(v), h0))

copy(v::SmallVector) = v

length(v::SmallVector) = v.n

size(v::SmallVector) = (length(v),)

getindex(v::SmallVector, i::Int) = v.b[i]

setindex(v::SmallVector, x, i::Integer) = SmallVector(setindex(v.b, x, i), length(v))

empty(v::SmallVector) = SmallVector(zero(v.b), 0)

zero(v::SmallVector) = SmallVector(zero(v.b), length(v))

function zeros(::Type{SmallVector{N,T}}, n::Integer) where {N,T}
    SmallVector(zero(Values{N,T}), n)
end

function ones(::Type{SmallVector{N,T}}, n::Integer) where {N,T}
    b = ones(Values{N,T})
    SmallVector((@inbounds padtail(b, -one(T), n)), n)
end

function SmallVector{N,T}(v::SmallVector{M}) where {N,T,M}
    t = ntuple(i -> i <= M ? T(v[i]) : zero(T), Val(N))
    SmallVector{N,T}(t, length(v))
end

function SmallVector{N,T}(v::Union{AbstractVector,Tuple}) where {N,T}
    n = length(v)
    i1 = firstindex(v)
    t = ntuple(i -> i <= n ? T(v[i+i1-1]) : zero(T), Val(N))
    SmallVector{N,T}(t, n)
end

function SmallVector{N,T}(iter) where {N,T}
    b = zero(Values{N,T})
    n = 0
    for (i, x) in enumerate(iter)
        b = setindex(b, x, i)
        n = i
    end
    SmallVector(b, n)
end

SmallVector{N}(v::AbstractVector{T}) where {N,T} = SmallVector{N,T}(v)

function SmallVector{N}(v::V) where {N, V <: Tuple}
    T = promote_type(fieldtypes(V)...)
    SmallVector{N,T}(v)
end

+(v::SmallVector) = v

+(v::SmallVector, w::SmallVector) = SmallVector(padded_add(v.b, w.b), length(v))

-(v::SmallVector) = SmallVector(-v.b, length(v))

-(v::SmallVector, w::SmallVector) = SmallVector(padded_sub(v.b, w.b), length(v))

*(c::Number, v::SmallVector) = SmallVector(c*v.b, length(v))

*(v::SmallVector, c::Number) = c*v

sum(v::SmallVector{N}) where N = sum(Values{N,Int}(v.b))

prod(v::SmallVector{N,T}) where {N,T} = prod(Values{N,Int}(@inbounds padtail(v.b, T(1), length(v))))

function maximum(v::SmallVector{N,T}) where {N,T}
    if T <: Unsigned
        maximum(v.b)
    else
        maximum(@inbounds padtail(v.b, typemin(T), length(v)))
    end
end

minimum(v::SmallVector{N,T}) where {N,T} = minimum(@inbounds padtail(v.b, typemax(T), length(v)))

function push(v::SmallVector, x)
    n = length(v)
    SmallVector(setindex(v.b, x, n+1), n+1)
end

push(v::SmallVector, xs...) = foldl(push, xs; init = v)

function pop(v::SmallVector{N,T}) where {N,T}
    n = length(v)
    SmallVector(setindex(v.b, zero(T), n), n-1), v[n]
end

function pushfirst(v::SmallVector, x)
    n = length(v)
    SmallVector(pushfirst(v.b, x), n+1)
end

pushfirst(v::SmallVector, xs...) = foldr((x, v) -> pushfirst(v, x), xs; init = v)

function popfirst(v::SmallVector)
    n = length(v)
    c, x = popfirst(v.b)
    SmallVector(c, n-1), x
end

function insert(v::SmallVector, i::Integer, x)
    n = length(v)
    SmallVector(insert(v.b, i, x), n+1)
end

deleteat(v::SmallVector) = first(popat(v, 1))

function popat(v::SmallVector, i::Integer)
    n = length(v)
    c, x = deleteat(v.b, i)
    SmallVector(c, n-1), x
end

# TODO: do we want UInt?
support(v::SmallVector) = convert(SmallSet{UInt}, bits(map(!iszero, v.b)))
