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
sum_fast(::AbstractFixedVector)
extrema_fast(::AbstractFixedVector)
extrema_fast(::Any, ::AbstractFixedVector)
support(::AbstractFixedVector)
```
