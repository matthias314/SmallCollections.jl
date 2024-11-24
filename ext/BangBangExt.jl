module BangBangExt

using SmallCollections

using BangBang: BangBang, NoBang, Mutator

BangBang.implements(::Mutator, ::Type{<:Union{SmallDict, SmallSet, SmallBitSet}}) = false

for f in (:push, :pop, :delete)
    @eval NoBang.$f(c::SmallDict, x::Pair) = $f(c, x)
    @eval NoBang.$f(c::Union{SmallSet, SmallBitSet}, x) = $f(c, x)
end

NoBang.pop(c::Union{SmallDict, SmallSet, SmallBitSet}) = pop(c)

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
