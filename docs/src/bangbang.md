```@meta
DocTestSetup = :(using SmallCollections)
```

# [BangBang support](@id sec-bangbang)

If the package [`BangBang.jl`](https://github.com/JuliaFolds2/BangBang.jl)
is loaded, then the functions
`push`,
`pop` and
`delete`
for `SmallDict`, `SmallSet` and `SmallBitSet`,
`union`,
`intersect`,
`setdiff` and
`symdiff`
for `SmallSet` and `SmallBitSet` as well as
[`setindex`](@ref setindex(::AbstractSmallVector, ::Any, ::Integer)),
[`push`](@ref push(::AbstractSmallVector, ::Vararg)),
[`pushfirst`](@ref pushfirst(::AbstractSmallVector, ::Vararg)),
[ `pop`](@ref pop(::AbstractSmallVector)),
[`popfirst`](@ref popfirst(::AbstractSmallVector)),
[`deleteat`](@ref deleteat(::AbstractSmallVector, ::Integer)) and
[`append`](@ref append(::AbstractSmallVector, ::Vararg))
for `AbstractSmallVector` as well as `PackedVector`
are also available in `!!`-form.
For example, `setindex!!` with a `SmallVector` as first argument calls `setindex`.
(`BangBang.jl` does not define `insert!!`, `prepend!!`, `filter!!` and `map!!`.)
Moreover, `add!!(v, w)` is a synonym for `v+w` for the immutable vector types defined by this package.

This allows to write efficient code that works for both mutable and immutable arguments.
For example, the function
```julia
f!!(v, ws...) = foldl(add!!, ws; init = v)
```
adds up its arguments, mutating the first argument `v` if possible.
