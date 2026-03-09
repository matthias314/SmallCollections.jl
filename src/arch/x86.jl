using CpuId: cpufeature

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

using CpuId: CpuFeature, __ECX
const AVX512VBMI2 = CpuFeature(0x0000_0007, 0x00, __ECX, 6)
const HAS_COMPRESS = cpufeature(:AVX512VL) || cpufeature(AVX512VBMI2)

@inline @generated function shuffle(::Val{:avx}, v::AbstractFixedVector{N,T}, p::AbstractFixedVector{N,U}) where {N, T, U}
    @assert N*sizeof(T) == N*sizeof(U) == 16
    HT = hwtype(T)
    LHT = llvm_type(HT)
    LU = llvm_type(U)
    ir = """
        declare <16 x i8> @llvm.x86.ssse3.pshuf.b.128(<16 x i8>, <16 x i8>)
        define <$N x $LHT> @shuffle(<$N x $LHT>, <$N x $LU>) #0 {
            %v = bitcast <$N x $LHT> %0 to <16 x i8>
            %p = bitcast <$N x $LU> %1 to <16 x i8>
            %w = call <16 x i8> @llvm.x86.ssse3.pshuf.b.128(<16 x i8> %v, <16 x i8> %p)
            %r = bitcast <16 x i8> %w to <$N x $LHT>
            ret <$N x $LHT> %r
        }
        attributes #0 = { alwaysinline }
    """
    quote
        a = (0x0101010101010101 * sizeof(T)) % U
        b = 0x0706050403020100 % U
        q = p .* a .+ b
        t = Base.llvmcall(($ir, "shuffle"), NTuple{N,VecElement{$HT}},
            Tuple{NTuple{N,VecElement{$HT}}, NTuple{N,VecElement{U}}},
            vec(Tuple(v)), vec(Tuple(q)))
        FixedVector{N,T}(unvec(T, t))
    end
end

@inline @generated function shuffle(::Val{:avx2}, v::AbstractFixedVector{N,T}, p::AbstractFixedVector{N,U}) where {N, T, U}
    @assert N*sizeof(T) == N*sizeof(U) == 32
    HT = hwtype(T)
    LHT = llvm_type(HT)
    LU = llvm_type(U)
    s1 = join((string("i32 ", i & 15) for i in 0:31), ',')
    s2 = join((string("i32 ", i | 16) for i in 0:31), ',')
    m1 = VERSION >= v"1.12" ? "splat(i8 -1)" : '<' * join(("i8 -1" for i in 0:31), ',') * '>'
    ir = """
        declare <32 x i8> @llvm.x86.avx2.pshuf.b(<32 x i8>, <32 x i8>)
        define <$N x $LHT> @shuffle(<$N x $LHT>, <$N x $LU>) #0 {
            %v = bitcast <$N x $LHT> %0 to <32 x i8>
            %p = bitcast <$N x $LU> %1 to <32 x i8>

            %a = insertelement <32 x i8> poison, i8 16, i32 0
            %b = shufflevector <32 x i8> %a, <32 x i8> poison, <32 x i32> zeroinitializer
            %c = icmp ult <32 x i8> %p, %b

            %q1 = select <32 x i1> %c, <32 x i8> %p, <32 x i8> $m1
            %v1 = shufflevector <32 x i8> %v, <32 x i8> poison, <32 x i32> <$s1>
            %w1 = call <32 x i8> @llvm.x86.avx2.pshuf.b(<32 x i8> %v1, <32 x i8> %q1)

            %q2 = select <32 x i1> %c, <32 x i8> $m1, <32 x i8> %p
            %v2 = shufflevector <32 x i8> %v, <32 x i8> poison, <32 x i32> <$s2>
            %w2 = call <32 x i8> @llvm.x86.avx2.pshuf.b(<32 x i8> %v2, <32 x i8> %q2)

            %w = xor <32 x i8> %w1, %w2
            %r = bitcast <32 x i8> %w to <$N x $LHT>
            ret <$N x $LHT> %r
        }
        attributes #0 = { alwaysinline }
    """
    quote
        a = (0x0101010101010101 * sizeof(T)) % U
        b = 0x0706050403020100 % U
        q = p .* a .+ b
        t = Base.llvmcall(($ir, "shuffle"), NTuple{N,VecElement{$HT}},
            Tuple{NTuple{N,VecElement{$HT}}, NTuple{N,VecElement{U}}},
            vec(Tuple(v)), vec(Tuple(q)))
        FixedVector{N,T}(unvec(T, t))
    end
end

avx512_suffix(::Type{<:Union{Int8, UInt8, Bool}}) = "qi"
avx512_suffix(::Type{<:Union{Int16, UInt16}}) = "hi"
avx512_suffix(::Type{<:Union{Int32, UInt32, Char}}) = "d"
avx512_suffix(::Type{<:Union{Int64, UInt64}}) = "q"
avx512_suffix(::Type{Float32}) = "ps"
avx512_suffix(::Type{Float64}) = "pd"
avx512_suffix(::Type{<:Enum{T}}) where T = avx512_suffix(T)

@inline @generated function shuffle(::Val{:avx512}, v::AbstractFixedVector{N,T}, p::AbstractFixedVector{N,U}) where {N,T,U}
    @assert N*sizeof(T) == N*sizeof(U) in (16, 32, 64)
    HT = hwtype(T)
    LHT = llvm_type(HT)
    LU = llvm_type(U)
    LS = avx512_suffix(HT)
    M = 8 * sizeof(HT) * N
    ir = """
        declare <$N x $LHT> @llvm.x86.avx512.vpermi2var.$LS.$M(<$N x $LHT>, <$N x $LU>, <$N x $LHT>)
        define <$N x $LHT> @shuffle(<$N x $LHT>, <$N x $LU>) #0 {
            %w = call <$N x $LHT> @llvm.x86.avx512.vpermi2var.$LS.$M(<$N x $LHT> %0, <$N x $LU> %1, <$N x $LHT> zeroinitializer)
            ret <$N x $LHT> %w
        }
        attributes #0 = { alwaysinline }
    """
    quote
        # we use `llvmcall` because `ccall` treats `Bool` as `i1`, not `i8`
        t = Base.llvmcall(($ir, "shuffle"),
            NTuple{N, VecElement{$HT}},
            Tuple{NTuple{N, VecElement{$HT}}, NTuple{N, VecElement{U}}},
            vec(Tuple(v)), vec(Tuple(p)))
        FixedVector{N,T}(unvec(T, t))
    end
end

@inline function shuffle(::Val{:avx512}, v::AbstractFixedVector{N,Float16}, p::AbstractFixedVector{N}) where N
    u = reinterpret.(UInt16, v)
    w = shuffle(Val(:avx512), u, p)
    reinterpret.(Float16, w)
end

@inline @generated function shuffle(::Val{:avx512_1024}, v::AbstractFixedVector{N,T}, p::AbstractFixedVector{N,U}) where {N,T,U}
    @assert N*sizeof(T) == N*sizeof(U) == 128
    HT = hwtype(T)
    LHT = llvm_type(HT)
    LU = llvm_type(U)
    LS = avx512_suffix(HT)
    N2 = N ÷ 2
    t1 = join((string("i32 ", k) for k in 0:N2-1), ", ")
    t2 = join((string("i32 ", k) for k in N2:N-1), ", ")
    ir = """
        declare <$N2 x $LHT> @llvm.x86.avx512.vpermi2var.$LS.512(<$N2 x $LHT>, <$N2 x $LU>, <$N2 x $LHT>)
        define <$N x $LHT> @shuffle(<$N x $LHT>, <$N x $LU>) #0 {
            %v1 = shufflevector <$N x $LHT> %0, <$N x $LHT> poison, <$N2 x i32> <$t1>
            %v2 = shufflevector <$N x $LHT> %0, <$N x $LHT> poison, <$N2 x i32> <$t2>
            %p1 = shufflevector <$N x $LU> %1, <$N x $LU> poison, <$N2 x i32> <$t1>
            %p2 = shufflevector <$N x $LU> %1, <$N x $LU> poison, <$N2 x i32> <$t2>
            %w1 = call <$N2 x $LHT> @llvm.x86.avx512.vpermi2var.$LS.512(<$N2 x $LHT> %v1, <$N2 x $LU> %p1, <$N2 x $LHT> %v2)
            %w2 = call <$N2 x $LHT> @llvm.x86.avx512.vpermi2var.$LS.512(<$N2 x $LHT> %v1, <$N2 x $LU> %p2, <$N2 x $LHT> %v2)
            %w = shufflevector <$N2 x $LHT> %w1, <$N2 x $LHT> %w2, <$N x i32> <$t1, $t2>
            %f = icmp sge <$N x $LU> %1, zeroinitializer
            %r = select <$N x i1> %f, <$N x $LHT> %w, <$N x $LHT> zeroinitializer  ; clear entry if highest bit of mask is set
            ret <$N x $LHT> %r
        }
        attributes #0 = { alwaysinline }
    """
    quote
        t = Base.llvmcall(($ir, "shuffle"),
            NTuple{N, VecElement{$HT}},
            Tuple{NTuple{N, VecElement{$HT}}, NTuple{N, VecElement{U}}},
            vec(Tuple(v)), vec(Tuple(p)))
        FixedVector{N,T}(unvec(T, t))
    end
end

@inline function shuffle(::Val{:avx512_1024}, v::AbstractFixedVector{64,Float16}, p::AbstractFixedVector{64})
    u = reinterpret.(UInt16, v)
    w = shuffle(Val(:avx512_1024), u, p)
    reinterpret.(Float16, w)
end

@inline function shuffle(v::AbstractFixedVector{NT,T}, p::AbstractFixedVector{NU}) where {NT,T,NU}
    @assert ishwtype(T)
    M = max(16, nextpow(2, max(NT,NU) * sizeof(T)))
    if (@static cpufeature(:AVX512VBMI) ? true : false) && M == 16 && sizeof(T) >= 4
        mode = :avx512
    elseif (@static cpufeature(:AVX) ? true : false) && M == 16
        mode = :avx
    elseif (@static cpufeature(:AVX512VBMI) ? true : false) && M <= 128
        mode = M <= 64 ? :avx512 : :avx512_1024
    elseif (@static cpufeature(:AVX2) ? true : false) && M == 32
        mode = :avx2
    else
        error("no available shuffle mode")
    end
    N = M ÷ sizeof(T)
    U = uinttype(T)
    vv = fixedvector(v, Val(N))
    pp = fixedvector(p, Val(N)) .% U
    ww = shuffle(Val(mode), vv, pp)
    fixedvector(ww, Val(NU))
end

function hasshuffle(::Val{N}, ::Type{T}) where {N,T}
    ishwtype(T) || return false
    M = N*sizeof(T)
    @static if cpufeature(:AVX)
        M <= 16 && return true
    end
    @static if cpufeature(:AVX512VBMI)
        M <= 128 && return true
    end
    @static if cpufeature(:AVX2)
        M <= 32 && return true
    end
    return false
end
