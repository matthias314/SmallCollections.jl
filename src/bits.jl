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
    $(@__MODULE__).top_set_bit(x::AbstractBitInteger) -> Int

Return the position of the highest set bit in `x` (counting from `1`),
or return `0` if `x` is `0`.

This function is analogous to Julia's internal function `Base.top_set_bit`,
but it is also fast and correct for bit integers defined by `BitIntegers.jl`.

See also `Base.top_set_bit`, [`$(@__MODULE__).AbstractBitInteger`](@ref).
"""
top_set_bit(x::T) where T <: AbstractBitInteger = bitsize(T) - leading_zeros(x)

"""
    $(@__MODULE__).unsafe_shl(x::U, i::Integer) where U <: AbstractBitInteger -> U

This is a fast, but unsafe version of the left bit shift operator `x << i`.
The shift `i` is assumed to be between `0` and `bitsize(x)-1`.

See also [`$(@__MODULE__).bitsize`](@ref), [`$(@__MODULE__).AbstractBitInteger`](@ref).
"""
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

"""
    $(@__MODULE__).unsafe_lshr(x::U, i::Integer) where U <: AbstractBitInteger -> U

This is a fast, but unsafe version of the logical (or unsigned) right bit shift operator `x >>> i`.
The shift `i` is assumed to be between `0` and `bitsize(x)-1`.

See also [`$(@__MODULE__).bitsize`](@ref), [`$(@__MODULE__).AbstractBitInteger`](@ref).
"""
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

blsi(x::Integer) = x & -x
# extract lowest set bit, compiles to single blsi instruction

blsr(x::Integer) = x & (x-one(x))
# reset lowest set bit, compiles to single blsr instruction

blsmsk(x::Integer) = x ⊻ (x-one(x))
# get mask up to lowest set bit, compiles to single blsmsk instruction

"""
    $(@__MODULE__).pdep(x::Unsigned, y::U) where U <: Unsigned -> U

Assume that `y` has exactly `m` `1`-bits. Then `pdep(x, y)` replaces these bits by the `m` lowest bits
of `x` (in order) and returns the result. The remaining bits of `x` are ignored.

On `x86_64` and `i686` machines, this function uses the corresponding instruction from the
[BMI2](https://en.wikipedia.org/wiki/X86_Bit_manipulation_instruction_set#BMI2) instruction set
if possible. Without hardware support it is much slower.
"""
function pdep(x::Unsigned, y::U) where U <: Unsigned
    a = zero(U)
    while !iszero(y)
        b = blsi(y)
        a |= b & -(isodd(x) % U)
        y ⊻= b
        x >>>= 1
    end
    a
end

using CpuId: cpufeature

if (Sys.ARCH == :x86_64 || Sys.ARCH == :i686) && cpufeature(:BMI2)
    const llvm_pdep = "llvm.x86.bmi.pdep.$(bitsize(UInt))"

    pdep(x::Unsigned, y::U) where U <: Union{UInt8,UInt16,UInt32,UInt} =
        ccall(llvm_pdep, llvmcall, UInt, (UInt, UInt), x % UInt, y % UInt) % U
end
