module SmallCollections

using Base: @propagate_inbounds

using BitIntegers: UInt256, UInt512, UInt1024

include("staticvectors.jl")

export capacity, fasthash

capacity(::T) where T = capacity(T)

fasthash(x) = fasthash(x, UInt(0))

bitsize(::Type{U}) where U = 8*sizeof(U)

include("smallset.jl")
include("smallvector.jl")

end
