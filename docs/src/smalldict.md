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
invget
getmin
push(::AbstractSmallDict, ::Pair)
pop(::AbstractSmallDict)
pop(::AbstractSmallDict, ::Any)
pop(::AbstractSmallDict, ::Any, Any)
delete(::AbstractSmallDict, ::Any)
popmin
popmin!
```
