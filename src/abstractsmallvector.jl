#
# AbstractCapacityVector
#

export AbstractCapacityVector, capacity, support,
    setindex, addindex, push, pop, pushfirst, popfirst,
    insert, duplicate, deleteat, popat, append, prepend

import Base: setindex, empty, zeros, ones, filter

"""
    AbstractCapacityVector{T} <: AbstractVector{T}

`AbstractCapacityVector` is the supertype of the vector types provided
by this module. At present, these are `AbstractSmallVector` and `PackedVector`.
Both can hold a variable number of elements up to a predefined maximal capacity.
If the element type `T` is concrete, then the immutable vector types do not allocate.

See also [`AbstractSmallVector`](@ref), [`PackedVector`](@ref).
"""
abstract type AbstractCapacityVector{T} <: AbstractVector{T} end

copy(v::AbstractCapacityVector) = v

"""
    capacity(::Type{<:AbstractCapacityVector}) -> Int
    capacity(v::AbstractCapacityVector) -> Int

Return the largest number of elements this vector type can hold.
"""
capacity(::Type{<:AbstractCapacityVector})

capacity(::V) where V <: AbstractCapacityVector = capacity(V)

"""
    setindex(v::V, x, i::Integer) where V <: AbstractCapacityVector -> V

Substitute `x` for the `i`-th component of `v` and return the new vector.

See also `Base.setindex`,  [`addindex`](@ref).
"""
setindex(::AbstractCapacityVector, ::Any, ::Integer)

"""
    addindex(v::V, x, i::Integer) where V <: AbstractCapacityVector -> V

Add `x` to the `i`-th component of `v` and return the new vector.

See also [`setindex`](@ref).
"""
@propagate_inbounds addindex(v::AbstractCapacityVector, x, i::Integer) =
    setindex(v, v[i]+x, i)

"""
    empty(v::V) where V <: AbstractCapacityVector -> V

Return an empty `AbstractCapacityVector` of the same type as `v`.

See also [`empty(v::AbstractSmallVector, ::Type)`](@ref),  [`empty(v::PackedVector, ::Type)`](@ref).
"""
empty(v::AbstractCapacityVector)

"""
    zeros(::Type{V}, n::Integer) where V <: AbstractCapacityVector -> V

Return an `AbstractCapacityVector` of type `V` containing `n` zeros.

See also [`ones`](@ref).
"""
zeros(::Type{<:AbstractCapacityVector}, ::Integer)

"""
    ones(::Type{V}, n::Integer) where V <: AbstractCapacityVector -> V

Return a `AbstractCapacityVector` of type `V` containing `n` ones.

See also [`zeros`](@ref).
"""
ones(::Type{<:AbstractCapacityVector}, ::Integer)

"""
    push(v::V, xs...) where V <: AbstractCapacityVector -> V

Return the `AbstractCapacityVector` obtained from `v` by appending the arguments `xs`.

See also `Base.push!`, `BangBang.push!!`.
"""
push(::AbstractCapacityVector, ::Vararg)

"""
    pop(v::V) where {T, V <: AbstractCapacityVector{T}} -> Tuple{V,T}

Return the tuple `(w, x)` where `x` is the last element of `v`
and `w` obtained from `v` by dropping this element.
The vector `v` must not be empty.

See also `Base.pop!`, `BangBang.pop!!`.
"""
pop(v::AbstractCapacityVector)

"""
    pushfirst((v::V, xs...) where V <: AbstractCapacityVector -> V

Return the `AbstractCapacityVector` obtained from `v` by prepending the arguments `xs`.

See also `Base.pushfirst!`, `BangBang.pushfirst!!`.
"""
pushfirst(::AbstractCapacityVector, ::Vararg)

"""
    popfirst(v::V) where {T, V <: AbstractCapacityVector{T}} -> Tuple{V,T}

Return the tuple `(w, x)` where `x` is the first element of `v`
and `w` obtained from `v` by dropping this element.
The vector `v` must not be empty.

See also `Base.popfirst!`, `BangBang.popfirst!!`.
"""
popfirst(v::AbstractCapacityVector)

"""
    insert(v::V, i::Integer, x) where V <: AbstractCapacityVector{T} -> V

Return the `AbstractCapacityVector` obtained from `v` by inserting `x` at position `i`.
The position `i` must be between `1` and `length(v)+1`.

This is the non-mutating analog of `Base.insert!`.

See also [`duplicate`](@ref).
"""
insert(::AbstractCapacityVector, ::Integer, ::Any)

"""
    duplicate(v::V, i::Integer, x) where V <: AbstractCapacityVector{T} -> V

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
duplicate(::AbstractCapacityVector, ::Integer, ::Any)

"""
    deleteat(v::V, i::Integer) where V <: AbstractCapacityVector -> V

Return the `AbstractCapacityVector` obtained from `v` by deleting the element at position `i`.
The latter must be between `1` and `length(v)`.

See also `Base.deleteat!`, `BangBang.deleteat!!`.
"""
deleteat(::AbstractCapacityVector, ::Integer)

"""
    popat(v::V, i::Integer) where {T, V <: AbstractCapacityVector{T}} -> Tuple{V,T}

Return the tuple `(w, x)` where `w` obtained from `v` by deleting the element `x`
at position `i`. The latter must be between `1` and `length(v)`.

See also `Base.popat!`, `BangBang.popat!!`.
"""
popat(::AbstractCapacityVector, ::Integer)

"""
    append(v::V, ws...) where V <: AbstractCapacityVector -> V

Append all elements of the collections `ws` to `v` and return the new vector.
Note that the resulting `AbstractCapacityVector` has the same capacity as `v`.

See also `Base.append!`, `BangBang.append!!`.
"""
append(::AbstractCapacityVector, ::Vararg)

"""
    prepend(v::V, ws...) where V <: AbstractCapacityVector -> V

Prepend all elements of the collections `ws` to `v` and return the new vector.
Note that the resulting `AbstractCapacityVector` has the same capacity as `v`.

See also `Base.prepend!`.
"""
prepend(::AbstractCapacityVector, ::Vararg)

function filter(f::F, v::AbstractCapacityVector) where F
    w = empty(v)
    for x in v
        if f(x)
            w = @inbounds push(w, x)
        end
    end
    w
end

"""
    support(v::AbstractCapacityVector) -> SmallBitSet

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
support(::AbstractCapacityVector)
