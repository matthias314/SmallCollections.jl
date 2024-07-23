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

## [`AbstractSmallVector`](@id sec-abstractsmallvector)

```@docs
AbstractSmallVector
capacity(::Type{<:AbstractSmallVector})
zeros
ones
setindex
addindex
push(::AbstractSmallVector, ::Vararg)
pop(::AbstractSmallVector)
pushfirst
popfirst
insert
duplicate
deleteat
popat
append
prepend
support
```

### [`SmallVector`](@id sec-smallvector)

```@docs
SmallVector
empty(::SmallVector)
fasthash(::SmallVector, ::UInt)
sum_fast
map
```

### [`PackedVector`](@id sec-packedvector)

```@docs
PackedVector
bits(::PackedVector)
SmallCollections.unsafe_add
SmallCollections.unsafe_sub
```

### [Broadcasting](@id sec-broadcasting)

Broadcasting is supported for `SmallVector`. The result is again a `SmallVector`
if at least one argument is a `SmallVector` and all other arguments (if any) are
`Tuple`s or scalars. The capacity of the result is the minimum of the capacities
of the `SmallVector` arguments. Broadcasted assignments to a `SmallVector` are
of course not possible.

See also [`map`](@ref), [`capacity`](@ref capacity(::Type{<:AbstractSmallVector})),
[`SmallCollections.SmallVectorStyle`](@ref).

#### Examples
```jldoctest
julia> v = SmallVector{8}(1:3); w = SmallVector{6}(2:4); v .* w .- 1.0
3-element SmallVector{6, Float64}:
  1.0
  5.0
 11.0

julia> v = SmallVector{8}(1:3); w = [2, 3, 4]; v .* w
3-element Vector{Int64}:
  2
  6
 12

julia> v = SmallVector{8}('a':'c'); t = ('p', 'q', 'r'); uppercase.(v .* t .* 'x')
3-element SmallVector{8, String}:
 "APX"
 "BQX"
 "CRX"
```

## [`SmallBitSet`](@id sec-smallbitset)

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
delete
```

### Subsets and shuffles

When used with a `SmallBitSet` as first argument, the following functions internally use
the function [`pdep`](@ref SmallCollections.pdep).
As discussed in the docstring for `pdep`, performance is much better if the processor supports the BMI2 instruction set.
The same applies to `shuffles` with more than two parts, even if the first argument is not a `SmallBitSet`.

```@docs
subsets(::Integer)
subsets(::Integer, ::Integer)
shuffles(::Vararg{Integer})
shuffle_signbit
```

## [BangBang support](@id sec-bangbang)

If the package [`BangBang.jl`](https://github.com/JuliaFolds2/BangBang.jl)
is loaded, then the functions
[`push`](@ref push(::SmallBitSet, ::Vararg)),
[`pop`](@ref pop(::SmallBitSet)),
[`delete`](@ref),
`union`,
`intersect`,
`setdiff` and
`symdiff`
for `SmallBitSet` as well as
[`setindex`](@ref),
[`push`](@ref push(::SmallVector, ::Vararg)),
[`pushfirst`](@ref),
[ `pop`](@ref pop(::SmallVector)),
[`popfirst`](@ref),
[`deleteat`](@ref) and
[`append`](@ref)
for `AbstractSmallVector`
are also available in `!!`-form.
For example, `setindex!!` with an `AbstractSmallVector` as first argument calls `setindex`.
(`BangBang.jl` does not define `insert!!`, `prepend!!`, `filter!!` and `map!!`.)
Moreover, `add!!(v::AbstractSmallVector, w::AbstractSmallVector)` is a synonym for `v+w`.

This allows to write efficient code that works for both mutable and immutable arguments.
For example, the function
```julia
f!!(v, ws...) = foldl(add!!, ws; init = v)
```
adds up its arguments, mutating the first argument `v` if possible.

## Non-exported names

### Public names

```@docs
SmallCollections.bitsize
SmallCollections.default
SmallCollections.SmallVectorStyle
```

### Internal names

These names are not public and may change in future versions.

```@docs
SmallCollections.AbstractBitInteger
SmallCollections.top_set_bit
SmallCollections.unsafe_shl
SmallCollections.unsafe_lshr
SmallCollections.pdep
```
