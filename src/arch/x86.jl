using CpuId: cpufeature

@inline @generated function shuffle(::Val{:avx}, v::AbstractFixedVector{N,T}, p::AbstractFixedVector{N,U}, @nospecialize(_)) where {N, T, U}
    @assert N*sizeof(T) == N*sizeof(U) == 16
    HT = hwtype(T)
    LHT = llvm_type(HT)
    LU = llvm_type(U)
    ir = """
        declare <16 x i8> @llvm.x86.ssse3.pshuf.b.128(<16 x i8>, <16 x i8>)
        define <$N x $LHT> @shuffle(<$N x $LHT>, <$N x $LU>) alwaysinline {
            %v = bitcast <$N x $LHT> %0 to <16 x i8>
            %p = bitcast <$N x $LU> %1 to <16 x i8>
            %w = call <16 x i8> @llvm.x86.ssse3.pshuf.b.128(<16 x i8> %v, <16 x i8> %p)
            %r = bitcast <16 x i8> %w to <$N x $LHT>
            ret <$N x $LHT> %r
        }
    """
    quote
        a = (0x0101010101010101 * sizeof(T)) % U
        b = 0x0706050403020100 % U
        q = p .* a .+ b
        t = Base.llvmcall(($ir, "shuffle"), NTuple{N,VecElement{$HT}},
            Tuple{NTuple{N,VecElement{$HT}}, NTuple{N,VecElement{U}}},
            vec(v), vec(q))
        FixedVector{N,T}(unvec(T, t))
    end
end

@inline @generated function shuffle(::Val{:avx2}, v::AbstractFixedVector{N,T}, p::AbstractFixedVector{N,U}, @nospecialize(_)) where {N, T, U}
    @assert N*sizeof(T) == N*sizeof(U) == 32
    HT = hwtype(T)
    LHT = llvm_type(HT)
    LU = llvm_type(U)
    s1 = join((string("i32 ", i & 15) for i in 0:31), ',')
    s2 = join((string("i32 ", i | 16) for i in 0:31), ',')
    m1 = VERSION >= v"1.12" ? "splat(i8 -1)" : '<' * join(("i8 -1" for i in 0:31), ',') * '>'
    ir = """
        declare <32 x i8> @llvm.x86.avx2.pshuf.b(<32 x i8>, <32 x i8>)
        define <$N x $LHT> @shuffle(<$N x $LHT>, <$N x $LU>) alwaysinline {
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
    """
    quote
        a = (0x0101010101010101 * sizeof(T)) % U
        b = 0x0706050403020100 % U
        q = p .* a .+ b
        t = Base.llvmcall(($ir, "shuffle"), NTuple{N,VecElement{$HT}},
            Tuple{NTuple{N,VecElement{$HT}}, NTuple{N,VecElement{U}}},
            vec(v), vec(q))
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

@inline @generated function shuffle(::Val{:avx512}, v::AbstractFixedVector{N,T}, p::AbstractFixedVector{N,U}, @nospecialize(_)) where {N,T,U}
    @assert N*sizeof(T) == N*sizeof(U) in (16, 32, 64)
    HT = hwtype(T)
    LHT = llvm_type(HT)
    LU = llvm_type(U)
    LS = avx512_suffix(HT)
    M = 8 * sizeof(HT) * N
    ir = """
        declare <$N x $LHT> @llvm.x86.avx512.vpermi2var.$LS.$M(<$N x $LHT>, <$N x $LU>, <$N x $LHT>)
        define <$N x $LHT> @shuffle(<$N x $LHT>, <$N x $LU>) alwaysinline {
            %w = call <$N x $LHT> @llvm.x86.avx512.vpermi2var.$LS.$M(<$N x $LHT> %0, <$N x $LU> %1, <$N x $LHT> zeroinitializer)
            ret <$N x $LHT> %w
        }
    """
    quote
        # we use `llvmcall` because `ccall` treats `Bool` as `i1`, not `i8`
        t = Base.llvmcall(($ir, "shuffle"),
            NTuple{N, VecElement{$HT}},
            Tuple{NTuple{N, VecElement{$HT}}, NTuple{N, VecElement{U}}},
            vec(v), vec(p))
        FixedVector{N,T}(unvec(T, t))
    end
end

@inline function shuffle(::Val{:avx512}, v::AbstractFixedVector{N,Float16}, p::AbstractFixedVector{N}, inbounds::Val) where N
    u = reinterpret.(UInt16, v)
    w = shuffle(Val(:avx512), u, p, inbounds)
    reinterpret.(Float16, w)
end

function shuffle2ir(M, N, LT, LU, LS)
    if M == 512
        """
            declare <$N x $LT> @llvm.x86.avx512.vpermi2var.$LS.512(<$N x $LT>, <$N x $LU>, <$N x $LT>)
            define <$N x $LT> @shuffle2.512(<$N x $LT>, <$N x $LU>, <$N x $LT>) alwaysinline {
                %w = call <$N x $LT> @llvm.x86.avx512.vpermi2var.$LS.512(<$N x $LT> %0, <$N x $LU> %1, <$N x $LT> %2)
                ret <$N x $LT> %w
            }
        """
    else
        M2 = M ÷ 2
        N2 = N ÷ 2
        t1 = join((string("i32 ", k) for k in 0:N2-1), ", ")
        t2 = join((string("i32 ", k) for k in N2:N-1), ", ")
        m = VERSION >= v"1.12" ? "splat($LU $N)" : '<' * join(("$LU $N" for i in 0:N2-1), ',') * '>'
        shuffle2ir(M2, N2, LT, LU, LS) * """
            define <$N x $LT> @shuffle2.$M(<$N x $LT>, <$N x $LU>, <$N x $LT>) alwaysinline {
                %u1 = shufflevector <$N x $LT> %0, <$N x $LT> poison, <$N2 x i32> <$t1>
                %u2 = shufflevector <$N x $LT> %0, <$N x $LT> poison, <$N2 x i32> <$t2>
                %v1 = shufflevector <$N x $LT> %2, <$N x $LT> poison, <$N2 x i32> <$t1>
                %v2 = shufflevector <$N x $LT> %2, <$N x $LT> poison, <$N2 x i32> <$t2>
                %p1 = shufflevector <$N x $LU> %1, <$N x $LU> poison, <$N2 x i32> <$t1>
                %p2 = shufflevector <$N x $LU> %1, <$N x $LU> poison, <$N2 x i32> <$t2>
                %w11 = call <$N2 x $LT> @shuffle2.$M2(<$N2 x $LT> %u1, <$N2 x $LU> %p1, <$N2 x $LT> %u2)
                %w12 = call <$N2 x $LT> @shuffle2.$M2(<$N2 x $LT> %v1, <$N2 x $LU> %p1, <$N2 x $LT> %v2)
                %m1 = and <$N2 x $LU> %p1, $m
                %f1 = icmp ne <$N2 x $LU> %m1, zeroinitializer
                %w1 = select <$N2 x i1> %f1, <$N2 x $LT> %w12, <$N2 x $LT> %w11
                %w21 = call <$N2 x $LT> @shuffle2.$M2(<$N2 x $LT> %u1, <$N2 x $LU> %p2, <$N2 x $LT> %u2)
                %w22 = call <$N2 x $LT> @shuffle2.$M2(<$N2 x $LT> %v1, <$N2 x $LU> %p2, <$N2 x $LT> %v2)
                %m2 = and <$N2 x $LU> %p2, $m
                %f2 = icmp ne <$N2 x $LU> %m2, zeroinitializer
                %w2 = select <$N2 x i1> %f2, <$N2 x $LT> %w22, <$N2 x $LT> %w21
                %w = shufflevector <$N2 x $LT> %w1, <$N2 x $LT> %w2, <$N x i32> <$t1, $t2>
                ret <$N x $LT> %w
            }
        """
    end
end

const avx512_maxbits_inline = 2048

@generated function shuffle(::Val{:avx512merge}, v::AbstractFixedVector{N,T}, p::AbstractFixedVector{N,U}, ::Val{INB}) where {N,T,U,INB}
    @assert N*sizeof(T) == N*sizeof(U) >= 128 && ispow2(N)
    HT = hwtype(T)
    LT = llvm_type(HT)
    LU = llvm_type(U)
    LS = avx512_suffix(HT)
    M = 8 * sizeof(HT) * N
    inline = M <= avx512_maxbits_inline ? "alwaysinline" : ""
    M2 = M ÷ 2
    N2 = N ÷ 2
    t1 = join((string("i32 ", k) for k in 0:N2-1), ", ")
    t2 = join((string("i32 ", k) for k in N2:N-1), ", ")
    tail = if INB
        """
            ret <$N x $LT> %w
        """
    else
        """
            %f = icmp sge <$N x $LU> %1, zeroinitializer
            %r = select <$N x i1> %f, <$N x $LT> %w, <$N x $LT> zeroinitializer  ; clear entry if highest bit of mask is set
            ret <$N x $LT> %r
        """
    end
    ir = shuffle2ir(M, N, LT, LU, LS) * """
        define <$N x $LT> @shuffle(<$N x $LT>, <$N x $LU>) $inline {
            %v1 = shufflevector <$N x $LT> %0, <$N x $LT> poison, <$N2 x i32> <$t1>
            %v2 = shufflevector <$N x $LT> %0, <$N x $LT> poison, <$N2 x i32> <$t2>
            %p1 = shufflevector <$N x $LU> %1, <$N x $LU> poison, <$N2 x i32> <$t1>
            %p2 = shufflevector <$N x $LU> %1, <$N x $LU> poison, <$N2 x i32> <$t2>
            %w1 = call <$N2 x $LT> @shuffle2.$M2(<$N2 x $LT> %v1, <$N2 x $LU> %p1, <$N2 x $LT> %v2)
            %w2 = call <$N2 x $LT> @shuffle2.$M2(<$N2 x $LT> %v1, <$N2 x $LU> %p2, <$N2 x $LT> %v2)
            %w = shufflevector <$N2 x $LT> %w1, <$N2 x $LT> %w2, <$N x i32> <$t1, $t2>
            $tail
        }
    """
    quote
        t = Base.llvmcall(($ir, "shuffle"),
            NTuple{N, VecElement{$HT}},
            Tuple{NTuple{N, VecElement{$HT}}, NTuple{N, VecElement{U}}},
            vec(v), vec(p))
        FixedVector{N,T}(unvec(T, t))
    end
end

@inline function shuffle(::Val{:avx512merge}, v::AbstractFixedVector{N,Float16}, p::AbstractFixedVector{N}, inbounds::Val) where N
    u = reinterpret.(UInt16, v)
    w = shuffle(Val(:avx512merge), u, p, inbounds)
    reinterpret.(Float16, w)
end

@inline function shuffle(v::AbstractFixedVector{NT,T}, p::AbstractFixedVector{NU}, inbounds::Val) where {NT,T,NU}
    @assert ishwtype(T)
    M = max(16, nextpow(2, max(NT,NU) * sizeof(T)))
    if (@static cpufeature(:AVX512VBMI) ? true : false) && M == 16 && sizeof(T) >= 4
        mode = :avx512
    elseif (@static cpufeature(:AVX) ? true : false) && M == 16
        mode = :avx
    elseif (@static cpufeature(:AVX512VBMI) ? true : false)
        mode = M <= 64 ? :avx512 : :avx512merge
    elseif (@static cpufeature(:AVX2) ? true : false) && M == 32
        mode = :avx2
    else
        error("no available shuffle mode")
    end
    N = M ÷ sizeof(T)
    U = uinttype(T)
    vv = fixedvector(v, Val(N))
    pp = fixedvector(p, Val(N)) .% U
    ww = shuffle(Val(mode), vv, pp, inbounds)
    fixedvector(ww, Val(NU))
end

function hasshuffle(::Val{N}, ::Type{T}, ::Val{INB}) where {N,T,INB}
    ishwtype(T) || return false
    N-1 <= typemax(INB ? uinttype(T) : inttype(T)) || return false
    M = N*sizeof(T)
    @static if cpufeature(:AVX)
        M <= 16 && return true
    end
    @static if cpufeature(:AVX512VBMI)
        M <= avx512_maxbits && return true
    end
    @static if cpufeature(:AVX2)
        M <= 32 && return true
    end
    return false
end
