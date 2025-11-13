```@meta
DocTestSetup = :(using SmallCollections)
```

# [Small vectors](@id sec-smallvector)

```@docs
AbstractSmallVector
SmallVector
MutableSmallVector
capacity(::Type{<:AbstractSmallVector})
fixedvector(::AbstractSmallVector)
bits(::AbstractSmallVector)
fasthash(::AbstractSmallVector, ::UInt)
unsafe_copyto!(::MutableSmallVector{N}, ::AbstractSmallVector{N}) where N
unsafe_copyto!(::MutableSmallVector, ::Union{NTuple, AbstractFixedVector})
resize
empty(::AbstractSmallVector)
getindex(::AbstractSmallVector, ::SmallBitSet)
setindex(::AbstractSmallVector, ::Any, ::Integer)
addindex(::AbstractSmallVector, ::Any, ::Integer)
push(::AbstractSmallVector, ::Vararg)
pop(::AbstractSmallVector)
pushfirst(::AbstractSmallVector, ::Vararg)
popfirst(::AbstractSmallVector)
insert(::AbstractSmallVector, ::Integer, ::Any)
duplicate(::AbstractSmallVector, ::Integer)
deleteat(::AbstractSmallVector, ::Integer)
popat(::AbstractSmallVector, ::Integer)
append(::AbstractSmallVector, ::Vararg)
prepend(::AbstractSmallVector, ::Vararg)
zeros(::Type{<:AbstractSmallVector}, ::Integer)
ones(::Type{<:AbstractSmallVector}, ::Integer)
sum_fast(::AbstractSmallVector)
dot_fast(::AbstractSmallVector, ::AbstractSmallVector)
extrema_fast(::AbstractSmallVector)
any(::Function, ::AbstractSmallVector)
issorted(::AbstractSmallVector)
map
support(::AbstractSmallVector)
support(::Any, ::AbstractSmallVector)
```
