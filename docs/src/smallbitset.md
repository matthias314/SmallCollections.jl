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
checkbounds
```
