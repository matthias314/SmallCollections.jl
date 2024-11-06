```@meta
DocTestSetup = :(using SmallCollections)
```

# [Small sets](@id sec-abstractsmallset)

```@docs
AbstractSmallSet
SmallSet
MutableSmallSet
capacity(::Type{<:AbstractSmallSet})
empty(::AbstractSmallSet)
push(::AbstractSmallSet, ::Pair)
pop(::AbstractSmallSet)
pop(::AbstractSmallSet, ::Any)
pop(::AbstractSmallSet, ::Any, Any)
delete(::AbstractSmallSet, ::Any)
```
