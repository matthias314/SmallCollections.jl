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
fixedvector(::AbstractFixedVector, ::Val)
bits(::AbstractFixedVector)
convert(::Type{<:AbstractFixedVector}, ::Unsigned)
fasthash(::AbstractFixedVector, ::UInt)
setindex(::AbstractFixedVector, ::Any, ::Integer)
addindex(::AbstractFixedVector, ::Any, ::Integer)
circshift(::AbstractFixedVector, ::Union{Integer,Val})
circshift!(::MutableFixedVector, ::Union{Integer,Val})
sum_fast(::AbstractFixedVector)
dot_fast(::AbstractFixedVector, ::AbstractFixedVector)
extrema_fast(::AbstractFixedVector)
extrema_fast(::Any, ::AbstractFixedVector)
Base.Checked.checked_neg(::AbstractFixedVector)
Base.Checked.checked_add(::AbstractFixedVector, ::AbstractFixedVector...)
Base.Checked.checked_sub(::AbstractFixedVector, ::AbstractFixedVector)
Base.Checked.checked_mul(::Integer, ::AbstractFixedVector)
Base.Checked.add_with_overflow(::AbstractFixedVector, ::AbstractFixedVector)
Base.Checked.sub_with_overflow(::AbstractFixedVector, ::AbstractFixedVector)
Base.Checked.mul_with_overflow(::Integer, ::AbstractFixedVector)
any(::Function, ::AbstractFixedVector)
issorted(::AbstractFixedVector)
support(::AbstractFixedVector)
support(::Any, ::AbstractFixedVector)
StaticArrays.SVector
```
