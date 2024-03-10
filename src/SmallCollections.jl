module SmallCollections

using Base: @propagate_inbounds

include("staticvectors.jl")

include("smallset.jl")
include("smallvector.jl")

end
