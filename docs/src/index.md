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

## [`AbstractFixedVector`](@id sec-abstractfixedvector)
```@docs
AbstractFixedVector
FixedVector
MutableFixedVector
setindex(::AbstractFixedVector, ::Any, ::Integer)
addindex(::AbstractFixedVector, ::Any, ::Integer)
sum_fast(::AbstractFixedVector)
extrema_fast(::AbstractFixedVector)
extrema_fast(::Any, ::AbstractFixedVector)
```

## [`AbstractCapacityVector`](@id sec-abstractsmallvector)

```@docs
AbstractCapacityVector
capacity(::Type{<:AbstractCapacityVector})
empty(::AbstractCapacityVector)
zeros
ones
setindex(::AbstractCapacityVector, ::Any, i::Integer)
addindex(::AbstractCapacityVector, ::Any, i::Integer)
push(::AbstractCapacityVector, ::Vararg)
pop(::AbstractCapacityVector)
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

### [`AbstractSmallVector`](@id sec-smallvector)

```@docs
AbstractSmallVector
SmallVector
MutableSmallVector
empty(::AbstractSmallVector, ::Type)
fasthash(::AbstractSmallVector, ::UInt)
sum_fast(::AbstractSmallVector)
extrema_fast(::AbstractSmallVector)
map
```

### [`PackedVector`](@id sec-packedvector)

```@docs
PackedVector
bits(::PackedVector)
empty(::PackedVector, ::Type)
fasthash(::PackedVector, ::UInt)
SmallCollections.unsafe_add
SmallCollections.unsafe_sub
```

## [Broadcasting](@id sec-broadcasting)

All vector types defined by this package can participate in broadcasting.
Efficient implementations exist for `AbstractFixedVector` and `AbstractSmallVector`,
including broadcasted assignments to a `MutableFixedVector` or `MutableSmallVector`.
Without assignment, the result is a `FixedVector` (or `SmallVector`) if at least
one argument is an `AbstractFixedVector` (or `AbstractSmallVector`) and all other
arguments (if any) are `Tuple`s or scalars. Otherwise Julia's generic broadcasting
method applies. The capacity of a resulting `SmallVector` is the minimum of the
capacities of the `AbstractSmallVector` arguments.

See also [`map`](@ref), [`capacity`](@ref capacity(::Type{<:AbstractCapacityVector})),
[`SmallCollections.FixedVectorStyle`](@ref), [`SmallCollections.SmallVectorStyle`](@ref).

#### Examples
```jldoctest
julia> v = MutableSmallVector{8}(1:3); w = SmallVector{6}(2:4); v .* w .- 1.0
3-element SmallVector{6, Float64}:
  1.0
  5.0
 11.0

julia> v .+= 3 .* w
3-element MutableSmallVector{8, Int64}:
  7
 11
 15

julia> v = FixedVector{3}(1:3); w = [2, 3, 4]; v .* w
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
compositions
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

## Non-exported names

### Public names

```@docs
SmallCollections.bitsize
SmallCollections.default
SmallCollections.FixedVectorStyle
SmallCollections.SmallVectorStyle
```

### Internal names

These names are not public and may change in future versions.

```@docs
SmallCollections.element_type
SmallCollections.AbstractBitInteger
SmallCollections.top_set_bit
SmallCollections.unsafe_shl
SmallCollections.unsafe_lshr
SmallCollections.pdep
```
