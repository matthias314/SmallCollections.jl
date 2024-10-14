"""
    $(@__MODULE__)

This packages provides several mutable and immutable collections that
can hold a limited (small) number of elements and are much more efficient
than `Set` and `Vector`, for example. This applies in particular
to the immutable variants because they don't allocate. At present
`SmallBitSet` and subtypes of `AbstractCapacityVector` are defined.

If the package `BangBang.jl` is loaded, then many functions defined by
this package are also available in `!!`-form. For example, `setindex!!`
with a `SmallVector` as first argument calls [`setindex`](@ref).

Bounds checking can be skipped for the functions defined in this package
by using the `@inbounds` macro.

See [`SmallBitSet`](@ref), [`AbstractCapacityVector`](@ref), `Base.@inbounds`,
[Section "BangBang support"](@ref sec-bangbang).
"""
module SmallCollections

using Base: @propagate_inbounds, BitInteger

using BitIntegers: AbstractBitSigned, AbstractBitUnsigned,
    UInt256, UInt512, UInt1024

"""
    $(@__MODULE__).AbstractBitInteger

This type is the union of `Base.BitInteger`, `BitIntegers.AbstractBitSigned`
and `BitIntegers.AbstractBitUnsigned`.
"""
const AbstractBitInteger = Union{BitInteger,AbstractBitSigned,AbstractBitUnsigned}

const FastInteger = Union{BitInteger,Complex{<:BitInteger}}
const FastFloat = Union{Float32,Float64,Complex{Float32},Complex{Float64}}

include("staticvectors.jl")

export capacity, fasthash

capacity(::T) where T = capacity(T)

fasthash(x) = fasthash(x, UInt(0))

include("bits.jl")
include("smallbitset.jl")
include("abstractsmallvector.jl")
include("smallvector.jl")
include("mutablesmallvector.jl")
include("packedvector.jl")

if VERSION > v"1.11-alpha"
    eval(Expr(:public, :default, :bitsize, :SmallVectorStyle))
end

end
