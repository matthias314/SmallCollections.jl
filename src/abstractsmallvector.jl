#
# AbstractSmallVector
#

export AbstractSmallVector, capacity, support,
    setindex, addindex, push, pop, pushfirst, popfirst,
    insert, duplicate, deleteat, popat, append, prepend

import Base: setindex, zeros, ones

abstract type AbstractSmallVector{T} <: AbstractVector{T} end

"""
    capacity(::Type{<:AbstractSmallVector}) -> Int
    capacity(v::AbstractSmallVector) -> Int

Return the largest number of elements this vector type can hold.
"""
capacity(::Type{<:AbstractSmallVector})

capacity(::V) where V <: AbstractSmallVector = capacity(V)

"""
    setindex(v::V, x, i::Integer) where V <: AbstractSmallVector -> V

Substitute `x` for the `i`-th component of `v` and return the new vector.

See also `Base.setindex`,  [`addindex`](@ref).
"""
setindex(::AbstractSmallVector, ::Any, ::Integer)

"""
    addindex(v::V, x, i::Integer) where V <: AbstractSmallVector -> V

Add `x` to the `i`-th component of `v` and return the new vector.

See also [`setindex`](@ref).
"""
addindex(::AbstractSmallVector, ::Any, ::Integer)

"""
    zeros(::Type{V}, n::Integer) where V <: AbstractSmallVector -> V

Return an `AbstractSmallVector` of type `V` containing `n` zeros.

See also [`ones`](@ref).
"""
zeros(::Type{<:AbstractSmallVector}, ::Integer)

"""
    ones(::Type{V}, n::Integer) where V <: AbstractSmallVector -> V

Return a `AbstractSmallVector` of type `V` containing `n` ones.

See also [`zeros`](@ref).
"""
ones(::Type{<:AbstractSmallVector}, ::Integer)

"""
    push(v::V, xs...) where V <: AbstractSmallVector -> V

Return the `AbstractSmallVector` obtained from `v` by appending the arguments `xs`.

See also `Base.push!`, `BangBang.push!!`.
"""
push(::AbstractSmallVector, ::Vararg)

"""
    pop(v::V) where {T, V <: AbstractSmallVector{T}} -> Tuple{V,T}

Return the tuple `(w, x)` where `x` is the last element of `v`
and `w` obtained from `v` by dropping this element.
The vector `v` must not be empty.

See also `Base.pop!`, `BangBang.pop!!`.
"""
pop(v::AbstractSmallVector)

"""
    pushfirst((v::V, xs...) where V <: AbstractSmallVector -> V

Return the `AbstractSmallVector` obtained from `v` by prepending the arguments `xs`.

See also `Base.pushfirst!`, `BangBang.pushfirst!!`.
"""
pushfirst(::AbstractSmallVector, ::Vararg)

"""
    popfirst(v::V) where {T, V <: AbstractSmallVector{T}} -> Tuple{V,T}

Return the tuple `(w, x)` where `x` is the first element of `v`
and `w` obtained from `v` by dropping this element.
The vector `v` must not be empty.

See also `Base.popfirst!`, `BangBang.popfirst!!`.
"""
popfirst(v::AbstractSmallVector)

"""
    insert(v::V, i::Integer, x) where V <: AbstractSmallVector{T} -> V

Return the `AbstractSmallVector` obtained from `v` by inserting `x` at position `i`.
The position `i` must be between `1` and `length(v)+1`.

This is the non-mutating analog of `Base.insert!`.

See also [`duplicate`](@ref).
"""
insert(::AbstractSmallVector, ::Integer, ::Any)

"""
    duplicate(v::V, i::Integer, x) where V <: AbstractSmallVector{T} -> V

Duplicate the `i`-th entry of `v` by inserting it at position `i+1` and return the new vector.

See also [`insert`](@ref).

# Example
```jldoctest
julia> v = SmallVector{8,Int8}(1:3)
3-element SmallVector{8, Int8}:
 1
 2
 3

julia> duplicate(v, 2)
4-element SmallVector{8, Int8}:
 1
 2
 2
 3
```
"""
duplicate(::AbstractSmallVector, ::Integer, ::Any)

"""
    deleteat(v::V, i::Integer) where V <: AbstractSmallVector -> V

Return the `AbstractSmallVector` obtained from `v` by deleting the element at position `i`.
The latter must be between `1` and `length(v)`.

See also `Base.deleteat!`, `BangBang.deleteat!!`.
"""
deleteat(::AbstractSmallVector, ::Integer)

"""
    popat(v::V, i::Integer) where {T, V <: AbstractSmallVector{T}} -> Tuple{V,T}

Return the tuple `(w, x)` where `w` obtained from `v` by deleting the element `x`
at position `i`. The latter must be between `1` and `length(v)`.

See also `Base.popat!`, `BangBang.popat!!`.
"""
popat(::AbstractSmallVector, ::Integer)

"""
    append(v::V, ws...) where V <: AbstractSmallVector -> V

Append all elements of the collections `ws` to `v` and return the new vector.
Note that the resulting `AbstractSmallVector` has the same capacity as `v`.

See also `Base.append!`, `BangBang.append!!`.
"""
append(::AbstractSmallVector, ::Vararg)

"""
    prepend(v::V, ws...) where V <: AbstractSmallVector -> V

Prepend all elements of the collections `ws` to `v` and return the new vector.
Note that the resulting `AbstractSmallVector` has the same capacity as `v`.

See also `Base.prepend!`.
"""
prepend(::AbstractSmallVector, ::Vararg)

"""
    support(v::AbstractSmallVector) -> SmallBitSet

Return the `SmallBitSet` with the indices of the non-zero elements of `v`.

See also [`SmallBitSet`](@ref).

# Example
```jldoctest
julia> v = SmallVector{8,Int8}([1, 0, 2, 0, 0, 3]);

julia> support(v)
SmallBitSet{UInt64} with 3 elements:
  1
  3
  6
```
"""
support(::AbstractSmallVector)
