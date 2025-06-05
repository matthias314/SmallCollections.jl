```@meta
DocTestSetup = :(using SmallCollections)
```

# [Small and packed vectors](@id sec-abstractsmallvector)

```@docs
AbstractCapacityVector
capacity(::Type{<:AbstractCapacityVector})
empty(::AbstractCapacityVector)
zeros
ones
setindex(::AbstractCapacityVector, ::Any, i::Integer)
addindex(::AbstractCapacityVector, ::Any, i::Integer)
push(::AbstractCapacityVector, ::Vararg)
pop(::AbstractCapacityVector)
pushfirst
popfirst
insert
duplicate
deleteat
popat
append
prepend
support
```

## [Small vectors](@id sec-smallvector)

```@docs
AbstractSmallVector
SmallVector
MutableSmallVector
fixedvector
empty(::AbstractSmallVector, ::Type)
unsafe_copyto!(::MutableSmallVector{N}, ::AbstractSmallVector{N}) where N
unsafe_copyto!(::MutableSmallVector{N}, ::Union{AbstractFixedVector{N},NTuple{N}}) where N
resize
fasthash(::AbstractSmallVector, ::UInt)
sum_fast(::AbstractSmallVector)
extrema_fast(::AbstractSmallVector)
any(::Function, ::AbstractSmallVector)
map
```

## [Packed vectors](@id sec-packedvector)

```@docs
PackedVector
bits(::PackedVector)
empty(::PackedVector, ::Type)
fasthash(::PackedVector, ::UInt)
SmallCollections.unsafe_add
SmallCollections.unsafe_sub
```
