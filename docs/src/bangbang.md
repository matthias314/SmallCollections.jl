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
[`setindex`](@ref),
[`push`](@ref push(::AbstractSmallVector, ::Vararg)),
[`pushfirst`](@ref),
[ `pop`](@ref pop(::AbstractSmallVector)),
[`popfirst`](@ref),
[`deleteat`](@ref) and
[`append`](@ref)
for `AbstractCapacityVector`
are also available in `!!`-form.
For example, `setindex!!` with an `AbstractCapacityVector` as first argument calls `setindex`.
(`BangBang.jl` does not define `insert!!`, `prepend!!`, `filter!!` and `map!!`.)
Moreover, `add!!(v::AbstractCapacityVector, w::AbstractCapacityVector)` is a synonym for `v+w`.

This allows to write efficient code that works for both mutable and immutable arguments.
For example, the function
```julia
f!!(v, ws...) = foldl(add!!, ws; init = v)
```
adds up its arguments, mutating the first argument `v` if possible.
