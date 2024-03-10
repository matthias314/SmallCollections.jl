#
# small vectors
#

export SmallVector, setindex, small_zeros,
    push, pop, pushfirst, popfirst, deleteat,
    support, fasthash

import Base: show, ==, copy,
    length, size, getindex, setindex,
    +, -, *, sum, prod, maximum, minimum

const T = Int8
const N = 16

struct SmallVector <: AbstractVector{T}
    b::Values{N,T}
    n::Int
end

function show(io::IO, v::SmallVector)
    print(io, "$T[")
    join(io, v, ',')
    print(io, ']')
end

==(v::SmallVector, w::SmallVector) = length(v) == length(w) && iszero(v.b-w.b)

fasthash(v::SmallVector, h0::UInt) = hash(bits(v.b), hash(length(v), h0))

copy(v::SmallVector) = v

length(v::SmallVector) = v.n

size(v::SmallVector) = (length(v),)

getindex(v::SmallVector, i::Int) = v.b[i]

setindex(v::SmallVector, x, i::Integer) = SmallVector(setindex(v.b, x, i), length(v))

small_zeros(n::Integer) = SmallVector(zero(Values{N,T}), n)

SmallVector(v::SmallVector) = v

function SmallVector(iter)
    b = zero(Values{N,T})
    n = 0
    for (i, x) in enumerate(iter)
        b = setindex(b, x, i)
        n = i
    end
    SmallVector(b, n)
end

+(v::SmallVector) = v

+(v::SmallVector, w::SmallVector) = SmallVector(v.b+w.b, length(v))

-(v::SmallVector) = SmallVector(-v.b, length(v))

-(v::SmallVector, w::SmallVector) = SmallVector(v.b-w.b, length(v))

*(c::Number, v::SmallVector) = SmallVector(T(c)*v.b, length(v))

sum(v::SmallVector) = sum(Values{N,Int}(v.b))

prod(v::SmallVector) = prod(Values{N,Int}(@inbounds padtail(v.b, T(1), length(v))))

function maximum(v::SmallVector)
    if T <: Unsigned
        maximum(v.b)
    else
        maximum(@inbounds padtail(v.b, typemin(T), length(v)))
    end
end

minimum(v::SmallVector) = minimum(@inbounds padtail(v.b, typemax(T), length(v)))

function push(v::SmallVector, x)
    n = length(v)
    SmallVector(setindex(v.b, x, n+1), n+1)
end

push(v::SmallVector, xs...) = foldl(push, xs; init = v)

function pop(v::SmallVector)
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

function deleteat(v::SmallVector, i::Integer)
    n = length(v)
    t = ntuple(Val(N)) do j
        if j < i
            v[j]
        elseif j == N
            zero(T)
        else
            v[j+1]
        end
    end
    SmallVector(Values{N,T}(t), n-1), v[i]
end

# TODO: do we want UInt?
support(v::SmallVector) = convert(SmallSet{UInt}, bits(map(!iszero, v.b)))
