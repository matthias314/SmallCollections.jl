#
# small sets
#

export SmallSet, bitmask, delete!!, pop!!, push!!

import Base: show, ==, hash, convert,
    isempty, in, first, last, iterate,
    length, issubset, maximum, minimum,
    union, intersect, setdiff, symdiff

const TS = UInt64
const NS = 8*sizeof(TS)

struct SmallSet <: AbstractSet{Int}
    mask::TS
    SmallSet(::Nothing, mask) = new(mask)
end

_SmallSet(mask) = SmallSet(nothing, mask)

bitmask(s::SmallSet) = s.mask

SmallSet(s::SmallSet) = s

convert(::Type{SmallSet}, mask::Integer) = _SmallSet(mask)

@propagate_inbounds function _push(mask::TS, iter)
    for n in iter
        @boundscheck (isinteger(n) && n > 0 && n <= NS) || error("SmallSet can only contain integers between 1 and $NS")
        mask |= one(TS) << (Int(n)-1)
    end
    _SmallSet(mask)
end

@propagate_inbounds SmallSet(iter) = _push(zero(TS), iter)

SmallSet(ns::Integer...) = SmallSet(ns)

function SmallSet(r::AbstractUnitRange{<:Integer})
    r0, r1 = first(r), last(r)
    (r0 > 0 && r1 <= NS) || error("SmallSet can only contain integers between 1 and $NS")
    if r1 < r0
        SmallSet()
    else
        m = one(TS) << (r1-r0+1)
        _SmallSet((m-1) << (r0-1))
    end
end

isempty(s::SmallSet) = iszero(bitmask(s))

length(s::SmallSet) = count_ones(bitmask(s))

@propagate_inbounds function first(s::SmallSet)
    @boundscheck isempty(s) && error("collection must be non-empty")
    trailing_zeros(bitmask(s))+1
end

@propagate_inbounds function last(s::SmallSet)
    @boundscheck isempty(s) && error("collection must be non-empty")
    NS-leading_zeros(bitmask(s))
end

function minimum(s::SmallSet; init = missing)
    if !isempty(s)
        @inbounds first(s)
    elseif init !== missing
        init
    else
        error("collection must be non-empty unless `init` is given")
    end
end

function maximum(s::SmallSet; init = missing)
    if !isempty(s)
        @inbounds last(s)
    elseif init !== missing
        init
    else
        error("collection must be non-empty unless `init` is given")
    end
end

# hasfastin(::Type{SmallSet}) = true
# this is the default for AbstractSet

in(n::Integer, s::SmallSet) = !iszero(s.mask & one(TS) << (n-1))

in(n, s::SmallSet) = false

function delete!!(s::SmallSet, n::Integer)
    m = one(TS) << (n-1)
    _SmallSet(s.mask & ~m)
end

delete!!(s::SmallSet, n) = s

@propagate_inbounds function pop!!(s::SmallSet)
    @boundscheck isempty(s) && error("collection must be non-empty")
    n = last(s)
    n, delete!!(s, n)
end

@propagate_inbounds function pop!!(s::SmallSet, n::Integer)
    @boundscheck n in s || error("element not found")
    n % Int, delete!!(s, n)
end

function pop!!(s::SmallSet, n::Integer, default::Integer)
    n in s ? (n % Int, delete!!(s, n)) : (default % Int, s)
end

@propagate_inbounds push!!(s::SmallSet, ns...) = _push(s.mask, ns)

function iterate(s::SmallSet, state = (s.mask, 0))
    mask, n = state
    if iszero(mask)
        return nothing
    else
        t = trailing_zeros(mask)+1
        n += t
        return (n, (mask >> t, n))
    end
end

function show(io::IO, s::SmallSet)
    print(io, "SmallSet(")
    join(io, s, ',')
    print(io, ')')
end

==(s::SmallSet, t::SmallSet) = s.mask == t.mask

# TODO: this does not give the same result as for Set
hash(s::SmallSet, h0::UInt) = hash(s.mask, h0)

union(s::SmallSet, t::SmallSet) = _SmallSet(s.mask | t.mask)

union(s::SmallSet, ts::SmallSet...) = foldl(union, ts; init = s)

intersect(s::SmallSet, t::SmallSet) = _SmallSet(s.mask & t.mask)

@propagate_inbounds function intersect(s::SmallSet, t::T) where T
    u = SmallSet()
    for n in (hasfastin(T) ? s : t)
        if n in (hasfastin(T) ? t : s)
            @inbounds u = push!!(u, n)
        end
    end
    u
end

@propagate_inbounds intersect(s::SmallSet, ts...) = foldl(intersect, ts; init = s)

setdiff(s::SmallSet, t::SmallSet) = _SmallSet(s.mask & ~t.mask)

@propagate_inbounds function setdiff(s::SmallSet, t::T) where T
    if hasfastin(T)
        u = s
        for n in s
            if n in t
                u = delete!!(u, n)
            end
        end
        return u
    else
        foldl(delete!!, t; init = s)
    end
end

@propagate_inbounds setdiff(s::SmallSet, ts...) = foldl(setdiff, ts; init = s)

symdiff(s::SmallSet, t::SmallSet) = _SmallSet(s.mask ⊻ t.mask)

#=
function symdiff(s::SmallSet, t)
    foldl(t; init = s) do u, n
        n isa Integer ? _SmallSet(xor(u.mask, one(TS) << (n-1))) : u
    end
end
=#

symdiff(s::SmallSet, ts::SmallSet...) = foldl(symdiff, ts; init = s)

issubset(s::SmallSet, t::SmallSet) = isempty(setdiff(s, t))
