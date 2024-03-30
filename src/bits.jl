"""
    $(@__MODULE__).bitsize(T::Type) -> Int

Return the size of the internal binary representation of `T` in bits.

See also `Base.sizeof`.
"""
bitsize(::Type{U}) where U = 8*sizeof(U)

"""
    $(@__MODULE__).top_set_bit(x::Unsigned) -> Int

Return the position of the highest set bit in `x` (counting from `1`),
or return `0` if `x` is `0`.

This function is analogous to Julia's internal function `Base.top_set_bit`,
but it is also fast and correct for bit integers defined by `BitIntegers.jl`.

See also `Base.top_set_bit`.
"""
top_set_bit(x::Unsigned)

top_set_bit(x::T) where T <: Unsigned = bitsize(T) - leading_zeros(x)
