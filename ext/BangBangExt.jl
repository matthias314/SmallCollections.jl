module BangBangExt

using SmallCollections

using BangBang: BangBang, NoBang, Mutator

BangBang.implements(::Mutator, ::Type{<:SmallBitSet}) = false

for f in (:push, :pop, :delete)
    @eval NoBang.$f(v::SmallBitSet, args...) = $f(v, args...)
end

BangBang.implements(::Mutator, ::Type{<:AbstractCapacityVector}) = false

for f in (:push, :pop, :pushfirst, :popfirst, :deleteat, :append)
    @eval NoBang.$f(v::AbstractCapacityVector, args...) = $f(v, args...)
end

BangBang.NoBang._setindex(v::AbstractCapacityVector, args...) = setindex(v, args...)
BangBang.add!!(v::AbstractCapacityVector, w::AbstractVector) = v+w

end # module
