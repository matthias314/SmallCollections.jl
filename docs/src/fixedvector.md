```@meta
DocTestSetup = :(using SmallCollections)
```

# [Fixed-length vectors](@id sec-abstractfixedvector)

```@docs
AbstractFixedVector
FixedVector
MutableFixedVector
bits(::AbstractFixedVector)
fasthash(::AbstractFixedVector, ::UInt)
setindex(::AbstractFixedVector, ::Any, ::Integer)
addindex(::AbstractFixedVector, ::Any, ::Integer)
circshift(::AbstractFixedVector, ::Union{Integer,Val})
circshift!(::MutableFixedVector, ::Union{Integer,Val})
sum_fast(::AbstractFixedVector)
extrema_fast(::AbstractFixedVector)
extrema_fast(::Any, ::AbstractFixedVector)
any(::Function, ::AbstractFixedVector)
support(::AbstractFixedVector)
StaticArrays.SVector
```
