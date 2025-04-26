```@meta
DocTestSetup = :(using SmallCollections)
```

# [Small bit sets](@id sec-smallbitset)

```@docs
SmallBitSet
bits(::SmallBitSet)
convert(::Type{SmallBitSet}, ::Integer)
capacity(::Type{<:SmallBitSet})
fasthash(::SmallBitSet, ::UInt)
empty(::SmallBitSet)
push(::SmallBitSet, ::Vararg)
pop(::SmallBitSet)
pop(::SmallBitSet, ::Any)
pop(::SmallBitSet, ::Any, ::Any)
delete(::SmallBitSet, ::Any)
exchange
any(::Function, ::SmallBitSet)
```

## Subsets and shuffles

When used with a `SmallBitSet` as first argument, the following functions internally use
the function [`pdep`](@ref SmallCollections.pdep).
As discussed in the docstring for `pdep`, performance is much better if the processor supports the BMI2 instruction set.
The same applies to `shuffles` with more than two parts, even if the first argument is not a `SmallBitSet`.

```@docs
subsets(::Integer)
subsets(::Integer, ::Integer)
compositions
shuffles(::Vararg{Integer})
shuffle_signbit
```
