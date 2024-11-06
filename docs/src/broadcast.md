```@meta
DocTestSetup = :(using SmallCollections)
```

# [Broadcasting](@id sec-broadcasting)

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

### Examples
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
