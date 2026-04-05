using CpuId: cpufeature, CpuFeature, __ECX

if cpufeature(:BMI1)
    const llvm_bextr = "llvm.x86.bmi.bextr.$(bitsize(UInt))"

    bextr(x::U, y::Unsigned) where U <: Union{UInt8,UInt16,UInt32,UInt} =
        ccall((llvm_bextr,), llvmcall, UInt, (UInt, UInt), x % UInt, y % UInt) % U

    const HAS_BEXTR = true
else
    const HAS_BEXTR = false
end

if cpufeature(:BMI2)
    const llvm_pdep = "llvm.x86.bmi.pdep.$(bitsize(UInt))"
    const llvm_pext = "llvm.x86.bmi.pext.$(bitsize(UInt))"

    pdep(x::Unsigned, y::U) where U <: Union{UInt8,UInt16,UInt32,UInt} =
        ccall((llvm_pdep,), llvmcall, UInt, (UInt, UInt), x % UInt, y % UInt) % U

    pext(x::Unsigned, y::U) where U <: Union{UInt8,UInt16,UInt32,UInt} =
        ccall((llvm_pext,), llvmcall, UInt, (UInt, UInt), x % UInt, y % UInt) % U

    const HAS_PEXT = true
else
    const HAS_PEXT = false
end

const AVX512VBMI2 = CpuFeature(0x0000_0007, 0x00, __ECX, 6)
const HAS_COMPRESS = cpufeature(:AVX512VL) || cpufeature(AVX512VBMI2)
