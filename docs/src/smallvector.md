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
fixedvector(::AbstractSmallVector, ::Val)
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
Base.Checked.checked_neg(::AbstractSmallVector)
Base.Checked.checked_add(::AbstractSmallVector, ::AbstractSmallVector...)
Base.Checked.checked_sub(::AbstractSmallVector, ::AbstractSmallVector)
Base.Checked.checked_mul(::Integer, ::AbstractSmallVector)
Base.Checked.add_with_overflow(::AbstractSmallVector, ::AbstractSmallVector)
Base.Checked.sub_with_overflow(::AbstractSmallVector, ::AbstractSmallVector)
Base.Checked.mul_with_overflow(::Integer, ::AbstractSmallVector)
any(::Function, ::AbstractSmallVector)
issorted(::AbstractSmallVector)
map
support(::AbstractSmallVector)
support(::Any, ::AbstractSmallVector)
```
