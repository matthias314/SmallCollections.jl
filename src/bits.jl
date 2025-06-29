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

llvm_type(::Type{Float16}) = "half"
llvm_type(::Type{Float32}) = "float"
llvm_type(::Type{Float64}) = "double"
llvm_type(::Type{T}) where T <: Union{Bool, BitInteger, Char, Enum} = string('i', 8*sizeof(T))

function llvm_type(N, ::Type{T}) where T
    if T <: AbstractFloat
        string('v', N, 'f', bitsize(T))
    else
        string('v', N, 'i', 8*sizeof(T))
    end
end

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

"""
    $(@__MODULE__).blsi(x::T) where T <: Integer -> T

Extract the lowest set bit of `x`.
For hardware integers, this compiles to a single `BLSI` instruction from the
[BMI1](https://en.wikipedia.org/wiki/X86_Bit_manipulation_instruction_set#BMI1_(Bit_Manipulation_Instruction_Set_1))
instruction set on `x86_64` and `i686` machines.

See also [`$(@__MODULE__).blsr`](@ref), [`$(@__MODULE__).blsmsk`](@ref).
"""
blsi(x::Integer) = x & -x

"""
    $(@__MODULE__).blsr(x::T) where T <: Integer -> T

Reset the lowest set bit of `x`.
For hardware integers, this compiles to a single `BLSR` instruction from the
[BMI1](https://en.wikipedia.org/wiki/X86_Bit_manipulation_instruction_set#BMI1_(Bit_Manipulation_Instruction_Set_1))
instruction set on `x86_64` and `i686` machines.

See also [`$(@__MODULE__).blsi`](@ref), [`$(@__MODULE__).blsmsk`](@ref).
"""
blsr(x::Integer) = x & (x-one(x))

"""
    $(@__MODULE__).blsmsk(x::T) where T <: Integer -> T

Get the bit mask up to lowest set bit of `x`.
For hardware integers, this compiles to a single `BLSMSK` instruction from the
[BMI1](https://en.wikipedia.org/wiki/X86_Bit_manipulation_instruction_set#BMI1_(Bit_Manipulation_Instruction_Set_1))
instruction set on `x86_64` and `i686` machines.

See also [`$(@__MODULE__).blsi`](@ref), [`$(@__MODULE__).blsr`](@ref).
"""
blsmsk(x::Integer) = x ⊻ (x-one(x))

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

"""
    $(@__MODULE__).pext(x::Unsigned, y::U) where U <: Union{UInt8,UInt16,UInt32,UInt} -> U

The bits in `x` corresponding to the `1`-bits in `y` are compressed to the lowest bits of the result;
the higher bits are set to `0`.

This function is only available on `x86_64` and `i686` machines and uses the corresponding instruction from the
[BMI2](https://en.wikipedia.org/wiki/X86_Bit_manipulation_instruction_set#BMI2) instruction set.
"""
pext(x::Unsigned, y::Union{UInt8,UInt16,UInt32,UInt})

using CpuId: cpufeature

if (Sys.ARCH == :x86_64 || Sys.ARCH == :i686) && cpufeature(:BMI2)
    const llvm_pdep = "llvm.x86.bmi.pdep.$(bitsize(UInt))"
    const llvm_pext = "llvm.x86.bmi.pext.$(bitsize(UInt))"

    pdep(x::Unsigned, y::U) where U <: Union{UInt8,UInt16,UInt32,UInt} =
        ccall(llvm_pdep, llvmcall, UInt, (UInt, UInt), x % UInt, y % UInt) % U

    pext(x::Unsigned, y::U) where U <: Union{UInt8,UInt16,UInt32,UInt} =
            ccall(llvm_pext, llvmcall, UInt, (UInt, UInt), x % UInt, y % UInt) % U

    const HAS_PEXT = true
else
    const HAS_PEXT = false
end
