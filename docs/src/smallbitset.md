```@meta
DocTestSetup = :(using SmallCollections)
```

# [Small bit sets](@id sec-smallbitset)

```@docs
SmallBitSet
bits(::SmallBitSet)
convert(::Type{SmallBitSet}, ::Integer)
capacity(::Type{<:SmallBitSet})
smallbitsettype
fasthash(::SmallBitSet, ::UInt)
empty(::SmallBitSet)
first_as_set
push(::SmallBitSet, ::Vararg)
pop(::SmallBitSet)
pop(::SmallBitSet, ::Any)
pop(::SmallBitSet, ::Any, ::Any)
delete(::SmallBitSet, ::Any)
exchange
any(::Function, ::SmallBitSet)
checkbounds
```

## Orderings

The following orderings are available to compare one `SmallBitSet` to another.

```@docs
isless(::SmallBitSet, ::SmallBitSet)
SmallCollections.Lex
SmallCollections.Colex
SmallCollections.GradedLex
SmallCollections.GradedColex
```
