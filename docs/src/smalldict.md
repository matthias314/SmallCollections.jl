```@meta
DocTestSetup = :(using SmallCollections)
```

# [Small dictionaries](@id sec-abstractsmalldict)

```@docs
AbstractSmallDict
SmallDict
MutableSmallDict
capacity(::Type{<:AbstractSmallDict})
empty(::AbstractSmallDict)
setindex(::AbstractSmallDict, ::Any, ::Any)
push(::AbstractSmallDict, ::Pair)
pop(::AbstractSmallDict)
pop(::AbstractSmallDict, ::Any)
pop(::AbstractSmallDict, ::Any, Any)
delete(::AbstractSmallDict, ::Any)
```
