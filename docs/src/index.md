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

## [`SmallVector`](@id sec-smallvector)

```@docs
SmallVector
capacity(::Type{<:SmallVector{N}}) where N
fasthash(::SmallVector, ::UInt)
empty(::SmallVector)
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
append
prepend
sum_fast
map
support
```

## [`SmallBitSet`](@id sec-smallbitset)

```@docs
SmallBitSet
bits
convert(::Type{SmallBitSet}, ::Integer)
capacity(::Type{<:SmallBitSet})
fasthash(::SmallBitSet, ::UInt)
empty(::SmallBitSet)
push(::SmallBitSet, ::Vararg{Any})
pop(::SmallBitSet)
pop(::SmallBitSet, ::Any)
pop(::SmallBitSet, ::Any, ::Any)
delete
```

## BangBang support

If the package [`BangBang.jl`](https://github.com/JuliaFolds2/BangBang.jl)
is loaded, then the functions
[`push`](@ref push(::SmallBitSet, ::Vararg{Any})),
[`pop`](@ref pop(::SmallBitSet)),
[`delete`](@ref),
`union`,
`intersect`,
`setdiff` and
`symdiff`
for `SmallBitSet` as well as
[`setindex`](@ref),
[`push`](@ref push(::SmallVector, ::Vararg{Any})),
[`pushfirst`](@ref),
[ `pop`](@ref pop(::SmallVector)),
[`popfirst`](@ref),
[`deleteat`](@ref) and
[`append`](@ref)
for `SmallVector`
are also available in `!!`-form.
For example, `setindex!!` with a `SmallVector` as first argument calls `setindex`.
(For some reason, `BangBang.jl` does not implement `insert!!` and `prepend!!`.)
Moreover, `add!!(v::SmallVector, w::SmallVector)` is a synonym for `v+w`.

This allows to write efficient code that works for both mutable and immutable arguments.
For example, the function
```julia
f!!(v, ws...) = foldl(add!!, ws; init = v)
```
adds up its arguments, mutating the first argument `v` if possible.

## Non-exported functions

### Public functions

```@docs
SmallCollections.default
```

### Internal functions

```@docs
SmallCollections.bitsize
SmallCollections.top_set_bit
```
