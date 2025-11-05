module StaticArraysExt

using SmallCollections, StaticArrays

"""
    FixedVector(v::StaticVector{N,T}) where {N,T} -> FixedVector{N,T}
    MutableFixedVector(v::StaticVector{N,T}) where {N,T} -> MutableFixedVector{N,T}

Convert a `StaticVector` to a `FixedVector` or `MutableFixedVector`.
The length `N` is inferred from the given vector `v`.
For example, `v` can be an `SVector` or `MVector`.

These methods are only available if the package `StaticArrays.jl` is loaded.

See also [`AbstractFixedVector`](@ref), `StaticArrays.StaticVector`.
"""
FixedVector, MutableFixedVector

SmallCollections.FixedVector(v::StaticVector{N}) where N = FixedVector{N}(v)
SmallCollections.MutableFixedVector(v::StaticVector{N}) where N = MutableFixedVector{N}(v)

"""
    SVector(v::AbstractFixedVector{N,T}) where {N,T} -> SVector{N,T}
    MVector(v::AbstractFixedVector{N,T}) where {N,T} -> MVector{N,T}

Convert an `AbstractFixedVector` to an `SVector` or `MVector`.
The length `N` is inferred from the argument.

These methods are only available if the package `StaticArrays.jl` is loaded.

See also `StaticArrays.SVector`, `StaticArrays.MVector`,
[`AbstractFixedVector`](@ref).
"""
SVector, MVector

StaticArrays.SVector(v::AbstractFixedVector{N}) where N = SVector{N}(v)
StaticArrays.MVector(v::AbstractFixedVector{N}) where N = MVector{N}(v)

SmallCollections.hasfixedlength(::Type{<:StaticArray}) = true

end
