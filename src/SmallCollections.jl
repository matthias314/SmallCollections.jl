"""
    SmallCollections

This packages provides several immutable collections that don't allocate
and are therefore faster than the usual types. The number of elements
that these collections can hold is necessarily limited. At present
`SmallSet` and `SmallVector` are defined.

If the package `BangBang.jl` is loaded, then many functions defined by
this package are also available in `!!`-form. For example, `setindex!!`
with a `SmallVector` as first argument calls [`setindex`](@ref).

See [`SmallSet`](@ref), [`SmallVector`](@ref).
"""
module SmallCollections

using Base: @propagate_inbounds, BitInteger

using BitIntegers: UInt256, UInt512, UInt1024

const FastInteger = Union{BitInteger,Complex{<:BitInteger}}
const FastFloat = Union{Float32,Float64,Complex{Float32},Complex{Float64}}

include("staticvectors.jl")

export capacity, fasthash

capacity(::T) where T = capacity(T)

fasthash(x) = fasthash(x, UInt(0))

include("bits.jl")
include("smallset.jl")
include("smallvector.jl")

end
