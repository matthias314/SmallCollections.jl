```@meta
DocTestSetup = quote
        using SmallCollections
    # for jldoctest outside of docstrings
    end
```

# SmallCollections.jl

```@docs
SmallCollections
```

## [`SmallSet`](@id sec-smallset)

```@docs
SmallSet
bits
convert(::Type{SmallSet}, ::Integer)
capacity(::Type{<:SmallSet})
fasthash(::SmallSet, ::UInt)
push(::SmallSet, ::Vararg{Any})
pop(::SmallSet)
pop(::SmallSet, ::Any)
pop(::SmallSet, ::Any, ::Any)
delete
```

## [`SmallVector`](@id sec-smallset)

```@docs
SmallVector
capacity(::Type{<:SmallVector{N}}) where N
fasthash(::SmallVector, ::UInt)
empty
zeros(::Type{<:SmallVector}, ::Integer)
ones(::Type{<:SmallVector}, ::Integer)
setindex
push(::SmallVector, ::Vararg{Any})
pop(::SmallVector)
pushfirst
popfirst
insert
deleteat
popat
support
```

## BangBang support

If the package [`BangBang.jl`](https://github.com/JuliaFolds2/BangBang.jl)
is loaded, then the functions
[`push`](@ref push(::SmallSet, ::Vararg{Any})),
[`pop`](@ref pop(::SmallSet)),
[`delete`](@ref),
`union`,
`intersect`,
`setdiff` and
`symdiff`
for `SmallSet` as well as
[`setindex`](@ref),
[`push`](@ref push(::SmallVector, ::Vararg{Any})),
[`pushfirst`](@ref),
[ `pop`](@ref pop(::SmallVector)),
[`popfirst`](@ref) and
[`deleteat`](@ref)
for `SmallVector`
are also available in `!!`-form.
For example, `setindex!!` with a `SmallVector` as first argument calls `setindex`.
(For some reason, `BangBang.jl` does not implement `insert!!`.)
Moreover, `add!!(v::SmallVector, w::SmallVector)` is a synonym for `v+w`.

This allows to write efficient code that works for both mutable and immutable arguments.
For example, the function
```julia
f!!(v, ws...) = foldl(add!!, ws; init = v)
```
adds up its arguments, mutating the first argument `v` if possible.

## Internal functions

```@docs
SmallCollections.bitsize
SmallCollections.default
SmallCollections.top_set_bit
```
