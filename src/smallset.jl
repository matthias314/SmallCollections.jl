#
# small sets
#

export SmallSet, bits, delete, pop, push

using Base: hasfastin, top_set_bit

import Base: show, ==, hash, copy, convert,
    isempty, in, first, last, iterate,
    length, issubset, maximum, minimum,
    union, intersect, setdiff, symdiff

bitsize(::Type{U}) where U = 8*sizeof(U)

struct SmallSet{U<:Unsigned} <: AbstractSet{Int}
    mask::U
    SmallSet(::Nothing, mask::U) where U = new{U}(mask)
end

_SmallSet(mask) = SmallSet(nothing, mask)

bits(s::SmallSet) = s.mask

capacity(::Type{SmallSet{U}}) where U = bitsize(U)

copy(s::SmallSet) = s

SmallSet(args...) = SmallSet{UInt}(args...)

SmallSet{U}(s::SmallSet) where U = _SmallSet(s.mask % U)

convert(::Type{SmallSet{U}}, mask::Integer) where U = _SmallSet(U(mask))

@propagate_inbounds function _push(mask::U, iter) where U
    for n in iter
        @boundscheck if !isinteger(n) || n <= 0 || n > bitsize(U)
                error("SmallSet can only contain integers between 1 and $(bitsize(U))")
            end
        mask |= one(U) << (Int(n)-1)
    end
    _SmallSet(mask)
end

@propagate_inbounds SmallSet{U}(iter) where U = _push(zero(U), iter)

SmallSet{U}(ns::Integer...) where U = SmallSet{U}(ns)

function SmallSet{U}(r::AbstractUnitRange{<:Integer}) where U
    r0, r1 = first(r), last(r)
    if r0 <= 0 || r1 > bitsize(U)
        error("SmallSet{$U} can only contain integers between 1 and $(bitsize(U))")
    end
    if r1 < r0
        _SmallSet(zero(U))
    else
        m = one(U) << (r1-r0+1) - one(U)
        _SmallSet(m << (r0-1))
    end
end

isempty(s::SmallSet) = iszero(bits(s))

length(s::SmallSet) = count_ones(bits(s))

@propagate_inbounds function first(s::SmallSet)
    @boundscheck isempty(s) && error("collection must be non-empty")
    trailing_zeros(bits(s))+1
end

@propagate_inbounds function last(s::SmallSet)
    @boundscheck isempty(s) && error("collection must be non-empty")
    top_set_bit(bits(s))
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

# hasfastin(::Type{<:SmallSet}) = true
# this is the default for AbstractSet

in(n::Integer, s::SmallSet{U}) where U <: Unsigned = !iszero(s.mask & one(U) << (n-1))

in(n, s::SmallSet) = false

function delete(s::SmallSet{U}, n::Integer) where U
    m = one(U) << (n-1)
    _SmallSet(s.mask & ~m)
end

delete(s::SmallSet{U}, n) where U = s

@propagate_inbounds function pop(s::SmallSet)
    @boundscheck isempty(s) && error("collection must be non-empty")
    n = last(s)
    n, delete(s, n)
end

@propagate_inbounds function pop(s::SmallSet, n::Integer)
    @boundscheck n in s || error("element not found")
    n % Int, delete(s, n)
end

function pop(s::SmallSet, n::Integer, default::Integer)
    n in s ? (n % Int, delete(s, n)) : (default % Int, s)
end

@propagate_inbounds push(s::SmallSet, ns...) = _push(s.mask, ns)

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
    print(io, "SmallSet([")
    join(io, s, ',')
    print(io, "])")
end

==(s::SmallSet, t::SmallSet) = s.mask == t.mask

fasthash(s::SmallSet, h0::UInt) = hash(s.mask, h0)

union(s::SmallSet, t::SmallSet) = _SmallSet(s.mask | t.mask)

union(s::SmallSet, ts::SmallSet...) = foldl(union, ts; init = s)

intersect(s::SmallSet{U}, t::SmallSet) where U <: Unsigned = _SmallSet(s.mask & (t.mask % U))

@propagate_inbounds function intersect(s::SmallSet{U}, t) where U <: Unsigned
    u = _SmallSet(zero(U))
    for n in (hasfastin(t) ? s : t)
        if n in (hasfastin(t) ? t : s)
            @inbounds u = push(u, n)
        end
    end
    u
end

@propagate_inbounds intersect(s::SmallSet, ts...) = foldl(intersect, ts; init = s)

setdiff(s::SmallSet{U}, t::SmallSet) where U <: Unsigned = _SmallSet(s.mask & ~(t.mask % U))

@propagate_inbounds function setdiff(s::SmallSet, t)
    if hasfastin(t)
        u = s
        for n in s
            if n in t
                u = delete(u, n)
            end
        end
        return u
    else
        foldl(delete, t; init = s)
    end
end

@propagate_inbounds setdiff(s::SmallSet, ts...) = foldl(setdiff, ts; init = s)

symdiff(s::SmallSet, t::SmallSet) = _SmallSet(s.mask ⊻ t.mask)

symdiff(s::SmallSet, ts::SmallSet...) = foldl(symdiff, ts; init = s)

issubset(s::SmallSet, t::SmallSet) = isempty(setdiff(s, t))
