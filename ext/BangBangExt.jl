module BangBangExt

using SmallCollections

using BangBang: BangBang, NoBang, Mutator, Extras

BangBang.implements(::Mutator, ::Type{<:Union{SmallDict, SmallSet, SmallBitSet}}) = false

for f in (:push, :pop, :delete)
    @eval NoBang.$f(c::SmallDict, x::Pair) = $f(c, x)
    @eval NoBang.$f(c::Union{SmallSet, SmallBitSet}, x) = $f(c, x)
end

NoBang.pop(c::Union{SmallDict, SmallSet, SmallBitSet}) = pop(c)

function Extras.modify!!(f, d::SmallDict, key)
    i = SmallCollections.token(d, key)
    if i === nothing
        ret = f(nothing)
        if ret !== nothing
            keys = push(d.keys, key)
            vals = @inbounds push(d.vals, something(ret))
        end
    else
        ret = f(Some(@inbounds(d.vals[i])))
        if ret !== nothing
            keys = @inbounds setindex(d.keys, key, i)
            vals = @inbounds setindex(d.vals, something(ret), i)
        end
    end
    SmallDict(keys, vals), ret
end

const CapacityVector = Union{SmallVector, PackedVector}

BangBang.implements(::Mutator, ::Type{<:Union{FixedVector,CapacityVector}}) = false

for f in (:push, :pop, :pushfirst, :popfirst, :deleteat, :append)
    @eval NoBang.$f(v::CapacityVector, args...) = $f(v, args...)
end

BangBang.NoBang._setindex(v::Union{FixedVector,CapacityVector}, args...) = Base.setindex(v, args...)
# otherwise a Vector is returned

BangBang.add!!(v::Union{FixedVector,CapacityVector}, w::AbstractVector) = v+w
# faster than without this line

end # module
