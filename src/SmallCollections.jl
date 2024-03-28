"""
    SmallCollections

This packages provides several immutable collections that don't allocate
and are therefore faster than the usual types. The number of elements
that these collections can hold is necessarily limited.

If the package [`BangBang.jl`](https://github.com/JuliaFolds2/BangBang.jl)
is loaded, then the functions `push`, `pop`, `pushfirst`, `popfirst`,
`delete`, `deleteat` and `setindex` are also available as
[`push!!`](https://juliafolds2.github.io/BangBang.jl/stable/#BangBang.push!!),
[`pop!!`](https://juliafolds2.github.io/BangBang.jl/stable/#BangBang.pop!!),
[`pushfirst!!`](https://juliafolds2.github.io/BangBang.jl/stable/#BangBang.pushfirst!!),
[`popfirst!!`](https://juliafolds2.github.io/BangBang.jl/stable/#BangBang.popfirst!!),
[`delete!!`](https://juliafolds2.github.io/BangBang.jl/stable/#BangBang.delete!!),
[`deleteat!!`](https://juliafolds2.github.io/BangBang.jl/stable/#BangBang.deleteat!!)
and
[`setindex!!`](https://juliafolds2.github.io/BangBang.jl/stable/#BangBang.setindex!!).


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
