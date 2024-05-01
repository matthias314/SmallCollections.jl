"""
    $(@__MODULE__).bitsize(T::Type) -> Int
    $(@__MODULE__).bitsize(x::T) where T -> Int

Return the size of the internal binary representation of `T` in bits.
For `Bool` the function returns `1`.

See also `Base.sizeof`.
"""
bitsize(::T) where T = bitsize(T)
bitsize(::Type{T}) where T = 8*sizeof(T)
bitsize(::Type{Bool}) = 1

"""
    $(@__MODULE__).top_set_bit(x) -> Int

Return the position of the highest set bit in `x` (counting from `1`),
or return `0` if `x` is `0`. Here `x` must be of type `BitInteger`,
`AbstractBitSigned` or `AbstractBitUnsigned`.

This function is analogous to Julia's internal function `Base.top_set_bit`,
but it is also fast and correct for bit integers defined by `BitIntegers.jl`.

See also `Base.top_set_bit`, `Base.BitInteger`,
`BitIntegers.AbstractBitSigned`, `BitIntegers.AbstractBitUnsigned`.
"""
top_set_bit(x::T) where T <: AbstractBitInteger = bitsize(T) - leading_zeros(x)

@generated function unsafe_shl(x::U, i::Integer) where U <: AbstractBitInteger
    b = bitsize(U)
    ir = """
        %r = shl i$b %0, %1
        ret i$b %r
    """
    quote
        $(Expr(:meta, :inline))
        Base.llvmcall($ir, U, Tuple{U, U}, x, i % U)
    end
end

@generated function unsafe_lshr(x::U, i::Integer) where U <: AbstractBitInteger
    b = bitsize(U)
    ir = """
        %r = lshr i$b %0, %1
        ret i$b %r
    """
    quote
        $(Expr(:meta, :inline))
        Base.llvmcall($ir, U, Tuple{U, U}, x, i % U)
    end
end

blsr(x::Integer) = x & (x-one(x))
# reset lowest set bit, compiles to single blsr instruction
