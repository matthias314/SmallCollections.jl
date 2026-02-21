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
dot_fast(::AbstractFixedVector, ::AbstractFixedVector)
extrema_fast(::AbstractFixedVector)
extrema_fast(::Any, ::AbstractFixedVector)
Base.Checked.checked_neg(::FixedVector)
Base.Checked.checked_add(::FixedVector, ::FixedVector...)
Base.Checked.checked_sub(::FixedVector, ::FixedVector)
Base.Checked.checked_mul(::Integer, ::FixedVector)
Base.Checked.add_with_overflow(::FixedVector, ::FixedVector)
Base.Checked.sub_with_overflow(::FixedVector, ::FixedVector)
Base.Checked.mul_with_overflow(::Integer, ::FixedVector)
any(::Function, ::AbstractFixedVector)
issorted(::AbstractFixedVector)
support(::AbstractFixedVector)
support(::Any, ::AbstractFixedVector)
StaticArrays.SVector
```
