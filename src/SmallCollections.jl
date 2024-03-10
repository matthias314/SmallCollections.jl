module SmallCollections

using Base: @propagate_inbounds

include("staticvectors.jl")

export fasthash

fasthash(x) = fasthash(x, UInt(0))

include("smallset.jl")
include("smallvector.jl")

end
