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

top_set_bit(x::Base.BitUnsigned) = Base.top_set_bit(x)
# avoid unneccesary generation of methods

@generated function top_set_bit(x::T) where T <: Unsigned
    b = bitsize(T)
    ir = """
        declare i$b @llvm.ctlz.i$b (i$b, i1)
        define i$b @ctlz(i$b) #0 {
            %a = call i$b @llvm.ctlz.i$b (i$b %0, i1 0)
            ret i$b %a
        }
        attributes #0 = { alwaysinline }
    """
    quote
        lz = Base.llvmcall(($ir, "ctlz"), T, Tuple{T}, x)
        $b-(lz % Int)
    end
end
