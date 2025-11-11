```@meta
DocTestSetup = :(using SmallCollections)
```

# [Fixed-length vectors](@id sec-abstractfixedvector)

```@docs
AbstractFixedVector
FixedVector
MutableFixedVector
capacity(::Type{<:AbstractFixedVector})
fixedvector(::AbstractFixedVector)
bits(::AbstractFixedVector)
convert(::Type{<:AbstractFixedVector}, ::Unsigned)
fasthash(::AbstractFixedVector, ::UInt)
setindex(::AbstractFixedVector, ::Any, ::Integer)
addindex(::AbstractFixedVector, ::Any, ::Integer)
circshift(::AbstractFixedVector, ::Union{Integer,Val})
circshift!(::MutableFixedVector, ::Union{Integer,Val})
sum_fast(::AbstractFixedVector)
extrema_fast(::AbstractFixedVector)
extrema_fast(::Any, ::AbstractFixedVector)
any(::Function, ::AbstractFixedVector)
issorted(::AbstractFixedVector)
support(::AbstractFixedVector)
support(::Any, ::AbstractFixedVector)
StaticArrays.SVector
```
