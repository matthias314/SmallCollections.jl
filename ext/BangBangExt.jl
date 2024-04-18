module BangBangExt

using SmallCollections

using BangBang: BangBang, NoBang, Mutator

BangBang.implements(::Mutator, ::Type{<:SmallBitSet}) = false

for f in (:push, :pop, :delete)
    @eval NoBang.$f(v::SmallBitSet, args...) = $f(v, args...)
end

BangBang.implements(::Mutator, ::Type{<:Union{SmallVector,PackedVector}}) = false

for f in (:push, :pop, :pushfirst, :popfirst, :deleteat, :append)
    @eval NoBang.$f(v::Union{SmallVector,PackedVector}, args...) = $f(v, args...)
end

BangBang.NoBang._setindex(v::Union{SmallVector,PackedVector}, args...) = setindex(v, args...)
BangBang.add!!(v::Union{SmallVector,PackedVector}, w::AbstractVector) = v+w

end # module
