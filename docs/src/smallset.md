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
values(::AbstractSmallSet)
push(::AbstractSmallSet, ::Pair)
pop(::AbstractSmallSet)
pop(::AbstractSmallSet, ::Any)
pop(::AbstractSmallSet, ::Any, Any)
delete(::AbstractSmallSet, ::Any)
sum_fast(::AbstractSmallSet)
extrema_fast(::AbstractSmallSet)
filter(::Any, ::AbstractSmallSet)
```
