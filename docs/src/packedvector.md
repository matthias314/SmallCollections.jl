```@meta
DocTestSetup = :(using SmallCollections)
```

# [Packed vectors](@id sec-packedvector)

```@docs
PackedVector
capacity(::Type{<:PackedVector})
bits(::PackedVector)
fasthash(::PackedVector, ::UInt)
empty(::PackedVector)
getindex(::PackedVector, ::SmallBitSet)
setindex(::PackedVector, ::Any, ::Integer)
addindex(::PackedVector, ::Any, ::Integer)
push(::PackedVector, ::Vararg)
pop(::PackedVector)
pushfirst(::PackedVector, ::Vararg)
popfirst(::PackedVector)
insert(::PackedVector, ::Integer, ::Any)
duplicate(::PackedVector, ::Integer)
deleteat(::PackedVector, ::Integer)
popat(::PackedVector, ::Integer)
append(::PackedVector, ::Vararg)
prepend(::PackedVector, ::Vararg)
zeros(::Type{<:PackedVector}, ::Integer)
ones(::Type{<:PackedVector}, ::Integer)
SmallCollections.unsafe_add
SmallCollections.unsafe_sub
support(::PackedVector)
```
