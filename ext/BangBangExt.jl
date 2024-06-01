module BangBangExt

using SmallCollections

using BangBang: BangBang, NoBang, Mutator

BangBang.implements(::Mutator, ::Type{<:SmallBitSet}) = false

for f in (:push, :pop, :delete)
    @eval NoBang.$f(v::SmallBitSet, args...) = $f(v, args...)
end

BangBang.implements(::Mutator, ::Type{<:AbstractSmallVector}) = false

for f in (:push, :pop, :pushfirst, :popfirst, :deleteat, :append)
    @eval NoBang.$f(v::AbstractSmallVector, args...) = $f(v, args...)
end

BangBang.NoBang._setindex(v::AbstractSmallVector, args...) = setindex(v, args...)
BangBang.add!!(v::AbstractSmallVector, w::AbstractVector) = v+w

end # module
