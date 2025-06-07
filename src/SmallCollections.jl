"""
    $(@__MODULE__)

This packages provides several mutable and immutable collections that
can hold a fixed or limited (small) number of elements and are much more efficient
than `Set` and `Vector`, for example. This applies in particular to the immutable
variants because they don't allocate if `isbitstype` holds for the element type.
At present, `FixedVector`, `SmallVector`, `SmallDict` and `SmallSet` and their
mutable counterparts are defined as well as `PackedVector` and `SmallBitSet`.

The submodule [`Combinatorics`](@ref) contains functions related to
enumerative combinatorics.

If the package `BangBang.jl` is loaded, then many functions defined by
this package are also available in `!!`-form. For example, `setindex!!`
with a `SmallVector` as first argument calls [`setindex`](@ref).

Bounds checking can be skipped for the functions defined in this package
by using the `@inbounds` macro.

See [`AbstractFixedVector`](@ref), [`AbstractSmallDict`](@ref),
[`AbstractSmallSet`](@ref), [`AbstractSmallVector`](@ref),
[`PackedVector`](@ref), [`SmallBitSet`](@ref), [`Combinatorics`](@ref),
`Base.@inbounds`, `Base.isbitstype`,
[Section "BangBang support"](@ref sec-bangbang).
"""
module SmallCollections

using Base: @propagate_inbounds, BitInteger
using Base: _InitialValue as Void

using BitIntegers: AbstractBitSigned, AbstractBitUnsigned,
    UInt256, UInt512, UInt1024

"""
    $(@__MODULE__).AbstractBitInteger

This type is the union of `Base.BitInteger`, `BitIntegers.AbstractBitSigned`
and `BitIntegers.AbstractBitUnsigned`.
"""
const AbstractBitInteger = Union{BitInteger,AbstractBitSigned,AbstractBitUnsigned}

const HWTypeExpr = :( Union{Base.HWReal, Bool, Char, Enum} )
@eval const HWType = $HWTypeExpr

export capacity, fasthash

capacity(::T) where T = capacity(T)
capacity(::Type{Union{}}) = error("not defined")   # for JET analysis

fasthash(x) = fasthash(x, UInt(0))

"""
    $(@__MODULE__).element_type(itr) -> Type
    $(@__MODULE__).element_type(::Type) -> Type

Return the element type of an iterator or its type. This differs from `eltype`
in that the element type of a `Tuple` or `NamedTuple` is determined via `promote_type`
instead of `promote_typejoin`. For all other iterators there is no difference.

See also `Base.eltype`, `Base.promote_type`, `Base.promote_typejoin`.

# Example
```jldoctest
julia> eltype((1, 2, 3.0))
Real

julia> $(@__MODULE__).element_type((1, 2, 3.0))
Float64
```
"""
element_type(::I) where I = element_type(I)
element_type(::Type{Union{}}) = error("not defined")   # for JET analysis
element_type(::Type{I}) where I = eltype(I)
element_type(::Type{<:Tuple{Vararg{T}}}) where T = T
element_type(::Type{<:Tuple{Vararg{T}}}) where T <: Pair = T

Base.@assume_effects :foldable function element_type(::Type{I}) where I <: Union{Tuple,NamedTuple}
    promote_type(fieldtypes(I)...)
end

Base.@assume_effects :foldable function element_type(::Type{I}) where I <: Tuple{Vararg{Pair}}
    K = promote_type(map(first∘fieldtypes, fieldtypes(I))...)
    V = promote_type(map(last∘fieldtypes, fieldtypes(I))...)
    Pair{K,V}
end

ntuple(f, n) = Base.ntuple(f, n)
@inline @generated ntuple(f, ::Val{N}) where N = :(Base.Cartesian.@ntuple $N i -> f(i))

@noinline keyerror(key) = throw(KeyError(key))

include("bits.jl")
include("mapstyle.jl")

include("smallbitset.jl")

include("fixedvector.jl")
include("staticvectors.jl")

include("capacityvector.jl")
include("smallvector.jl")
include("mutablesmallvector.jl")
include("packedvector.jl")
include("smalldict.jl")
include("smallset.jl")

include("combinatorics.jl")

if VERSION > v"1.11-alpha"
    eval(Expr(:public, :default, :isfasttype, :FixedVectorStyle, :SmallVectorStyle,
        :MapStyle, :LazyStyle, :EagerStyle, :RigidStyle, :StrictStyle, :padtail,
        :bitsize, :unsafe_shl, :unsafe_lshr, :blsi, :blsr, :blsmsk, :pdep))
end

end
