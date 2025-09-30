using CpuId: cpufeature

if cpufeature(:BMI1)
    const llvm_bextr = "llvm.x86.bmi.bextr.$(bitsize(UInt))"

    bextr(x::U, y::Unsigned) where U <: Union{UInt8,UInt16,UInt32,UInt} =
        ccall(llvm_bextr, llvmcall, UInt, (UInt, UInt), x % UInt, y % UInt) % U

    const HAS_BEXTR = true
else
    const HAS_BEXTR = false
end

if cpufeature(:BMI2)
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

using CpuId: CpuFeature, __ECX
const AVX512VBMI2 = CpuFeature(0x0000_0007, 0x00, __ECX, 6)
const HAS_COMPRESS = cpufeature(:AVX512VL) || cpufeature(AVX512VBMI2)

@generated function shuffle(::Val{M}, ::Val{NR}, v::AbstractFixedVector{NV,VT}, p::NTuple{NP,PT}) where {M, NR, NV, VT <: HWType, NP, PT <: BitInteger}
    shuf = if M == 16
        "@llvm.x86.ssse3.pshuf.b.128"
    elseif M == 32
        "@llvm.x86.avx2.pshuf.b"
    elseif M == 64
        "@llvm.x86.avx512.vpermi2var.qi.512"
    else
        error("unsupported bit length")
    end
    VB = sizeof(VT)
    PB = sizeof(PT)
    @assert max(NV, NP, NR)*VB <= M

    N = M ÷ VB
    LVT = llvm_type(VT)
    LVI = string('i', 8*VB)
    LPT = llvm_type(PT)

    ssv = join((string("i32 ", min(k, NV)) for k in 0:N-1), ',')
    ssp = join((string("i32 ", min(k, NP)) for k in 0:N-1), ',')
    ssr = join((string("i32 ", k) for k in 0:NP-1), ',')

    sp1 = if PB == VB
        "select i1 1, <$NP x $LPT> %1, <$NP x $LPT> poison"
    elseif PB < VB
        "sext <$NP x $LPT> %1 to <$NP x $LVI>"
    else # PB > VB
        "trunc <$NP x $LPT> %1 to <$NP x $LVI>"
    end

    pp2 = VB*sum(256^k for k in 0:VB-1)
    pp3 = sum(k*256^k for k in 0:VB-1)

    ir1 = if M == 64
        """
            declare <$M x i8> $shuf(<$M x i8>, <$M x i8>, <$M x i8>)
        """
    else
        """
            declare <$M x i8> $shuf(<$M x i8>, <$M x i8>)
        """
    end

    ir2 = if M == 32
        s1 = join((string("i32 ", i & 15) for i in 0:31), ',')
        s2 = join((string("i32 ", i | 16) for i in 0:31), ',')
        m1 = join(("i8 -1" for i in 0:31), ',')
        """
            %a = insertelement <32 x i8> poison, i8 16, i32 0
            %b = shufflevector <32 x i8> %a, <32 x i8> poison, <32 x i32> zeroinitializer
            %c = icmp ult <32 x i8> %p, %b

            %q1 = select <32 x i1> %c, <32 x i8> %p, <32 x i8> <$m1>
            %v1 = shufflevector <32 x i8> %v, <32 x i8> poison, <32 x i32> <$s1>
            %w1 = call <32 x i8> $shuf(<32 x i8> %v1, <32 x i8> %q1)

            %q2 = select <32 x i1> %c, <32 x i8> <$m1>, <32 x i8> %p
            %v2 = shufflevector <32 x i8> %v, <32 x i8> poison, <32 x i32> <$s2>
            %w2 = call <32 x i8> $shuf(<32 x i8> %v2, <32 x i8> %q2)

            %w = xor <32 x i8> %w1, %w2
        """
    elseif M == 64
        """
            %w = call <$M x i8> $shuf(<$M x i8> %v, <$M x i8> %p, <$M x i8> zeroinitializer)
        """
    else
        """
            %w = call <$M x i8> $shuf(<$M x i8> %v, <$M x i8> %p)
        """
    end

    ir = """
        $ir1
        define <$NP x $LVT> @shuffle(<$NV x $LVT>, <$NP x $LPT>) #0 {
            %u = shufflevector <$NV x $LVT> %0, <$NV x $LVT> zeroinitializer, <$N x i32> <$ssv>
            %v = bitcast <$N x $LVT> %u to <$M x i8>

            %pp2 = insertelement <$NP x $LVI> poison, $LVI $pp2, i32 0
            %sp2 = shufflevector <$NP x $LVI> %pp2, <$NP x $LVI> poison, <$NP x i32> zeroinitializer
            %pp3 = insertelement <$NP x $LVI> poison, $LVI $pp3, i32 0
            %sp3 = shufflevector <$NP x $LVI> %pp3, <$NP x $LVI> poison, <$NP x i32> zeroinitializer

            %p1 = $sp1
            %p2 = mul <$NP x $LVI> %p1, %sp2
            %p3 = add <$NP x $LVI> %p2, %sp3
            %p4 = shufflevector <$NP x $LVI> %p3, <$NP x $LVI> zeroinitializer, <$N x i32> <$ssp>
            %p = bitcast <$N x $LVI> %p4 to <$M x i8>

            $ir2

            %r1 = bitcast <$M x i8> %w to <$N x $LVT>
            %r = shufflevector <$N x $LVT> %r1, <$N x $LVT> zeroinitializer, <$NR x i32> <$ssr>

            ret <$NR x $LVT> %r
        }
        attributes #0 = { alwaysinline }
    """
    quote
        @inline
        w = Base.llvmcall(($ir, "shuffle"), NTuple{NR,VecElement{VT}},
            Tuple{NTuple{NV,VecElement{VT}}, NTuple{NP,VecElement{PT}}},
            vec(Tuple(v)), vec(p))
        FixedVector{NR,VT}(unvec(w))
    end
end

function shufflewidth(::Val{N}, ::Type{T}) where {N, T <: HWType}
    M = N*sizeof(T)
    @static if cpufeature(:AVX)
        M <= 16 && return 16
    end
    @static if cpufeature(:AVX512VBMI)
        M <= 64 && return 64
    end
    @static if cpufeature(:AVX2)
        M <= 32 && return 32
    end
    return 0
end

#=
@inline function newpopfirst(v::AbstractSmallVector{N,T}) where {N, T <: HWType}
    @boundscheck isempty(v) && error("vector must not be empty")
    M = N*sizeof(T)
    P = inttype(T)
    p = ntuple(i -> i < N ? P(i) : P(-1), Val(N))
    w = shuffle(M <= 16 ? Val(16) : Val(32), fixedvector(v), p)
    SmallVector(w, length(v)-1), @inbounds v[1]
end
=#
