#
# extensions of StaticVectors.jl
#

using StaticVectors

using Base: BitInteger, @assume_effects
import Base: setindex, convert

#=
@propagate_inbounds @generated function setindex(b::Values{N,T}, x, i::Integer) where {N,T}
    basis = ntuple(N) do j
        Values{N,T}(ntuple(==(j), N))
    end
    quote
        b + (T(x)-b[i])*$basis[i]
    end
end
=#

function basis(::Val{N}) where N
    ntuple(Val(N)) do j
        Values{N,Int8}(ntuple(==(j), Val(N)))
    end
end

@propagate_inbounds function setindex(b::Values{N,T}, x, i::Integer) where {N, T}
    b + (T(x)-b[i])*basis(Val(N))[i]
end

@propagate_inbounds @generated function padtail(b::Values{N,T}, x, i::Integer) where {N,T}
    pads = ntuple(N+1) do j
        Values{N,Int8}(ntuple(>=(j), N))
    end
    quote
        b + T(x)*$pads[i+1]
    end
end

#=
@assume_effects :total function pads(::Val{N}) where N
    ntuple(Val(N+1)) do j
        Values{N,Int8}(ntuple(>=(j), Val(N)))
    end
end

@propagate_inbounds function padtail(b::V, x, i::Integer) where {N, T, V <: Values{N,T}}
    b .| x*pads(Val(N))[i+1]
end
=#

function pushfirst(b::Values{N,T}, x) where {N, T}
    t = ntuple(Val(N)) do i
        i == 1 ? T(x) : b[i-1]
    end
    Values{N,T}(t)
end

function popfirst(b::Values{N,T}) where {N, T}
    t = ntuple(Val(N)) do i
        i == N ? zero(T) : b[i+1]
    end
    Values{N,T}(t), b[1]
end

function padded_add(v::TupleVector{N1,T1}, w::TupleVector{N2,T2}) where {N1,T1,N2,T2}
    T = promote_type(T1, T2)
    if N1 <= N2
        Values{N2,T}(ntuple(i -> i <= N1 ? v[i]+w[i] : w[i], Val(N2)))
    else
        Values{N2,T}(ntuple(i -> i <= N2 ? v[i]+w[i] : v[i], Val(N1)))
    end
end

function padded_sub(v::TupleVector{N1,T1}, w::TupleVector{N2,T2}) where {N1,T1,N2,T2}
    T = promote_type(T1, T2)
    if N1 <= N2
        Values{N2,T}(ntuple(i -> i <= N1 ? v[i]-w[i] : -w[i], Val(N2)))
    else
        Values{N1,T}(ntuple(i -> i <= N2 ? v[i]-w[i] : v[i], Val(N1)))
    end
end

#
# bit conversions
#

vec(t::NTuple{N}) where N = ntuple(i -> VecElement(t[i]), Val(N))

unvec(t::NTuple{N,VecElement}) where N = ntuple(i -> t[i].value, Val(N))

@generated function bits(v::TupleVector{N,T}) where {N, T <: BitInteger}
    s = bitsize(T)
    b = N*s
    c = nextpow(2, b)
    U = Symbol(:UInt, c)
    if b == c
        ir = """
            %b = bitcast <$N x i$s> %0 to i$b
            ret i$b %b
        """
    else
        ir = """
            %b = bitcast <$N x i$s> %0 to i$b
            %c = zext i$b %b to i$c
            ret i$c %c
        """
    end
    quote
        $(Expr(:meta, :inline))
        Base.llvmcall($ir, $U, Tuple{NTuple{N, VecElement{T}}}, vec(Tuple(v)))
    end
end

@generated function bits(v::TupleVector{N,Bool}) where N
    c = nextpow(2, N)
    U = Symbol(:UInt, c)
    if N == c
        ir = """
            %b = trunc <$N x i8> %0 to <$N x i1>
            %c = bitcast <$N x i1> %b to i$N
            ret i$N %c
        """
    else
        ir = """
            %a = trunc <$N x i8> %0 to <$N x i1>
            %b = bitcast <$N x i1> %a to i$N
            %c = zext i$N %b to i$c
            ret i$c %c
        """
    end
    quote
        $(Expr(:meta, :inline))
        Base.llvmcall($ir, $U, Tuple{NTuple{N, VecElement{Bool}}}, vec(Tuple(v)))
    end
end

@generated function convert(::Type{Values{N,T}}, x::U) where {N, T <: BitInteger, U <: Unsigned}
    s = bitsize(T)
    b = N*s
    c = bitsize(U)
    if b == c
        ir = """
            %b = bitcast i$b %0 to <$N x i$s>
            ret <$N x i$s> %b
        """
    elseif b > c
        ir = """
            %b = zext i$c %0 to i$b
            %a = bitcast i$b %b to <$N x i$s>
            ret <$N x i$s> %a
        """
    else
        ir = """
            %b = trunc i$c %0 to i$b
            %a = bitcast i$b %b to <$N x i$s>
            ret <$N x i$s> %a
        """
    end
    quote
        $(Expr(:meta, :inline))
        v = Base.llvmcall($ir, NTuple{N, VecElement{T}}, Tuple{$U}, x)
        Values{N,T}(unvec(v))
    end
end

@generated function convert(::Type{Values{N,Bool}}, x::U) where {N, U <: Unsigned}
    c = bitsize(U)
    N2 = nextpow(2, N)   # work around an LLVM bug
    if N2 == c
        ir = """
            %b = bitcast i$N2 %0 to <$N2 x i1>
            %c = zext <$N2 x i1> %b to <$N2 x i8>
            ret <$N2 x i8> %c
        """
    elseif N2 > c
        ir = """
            %a = zext i$c %0 to i$N2
            %b = bitcast i$N2 %a to <$N2 x i1>
            %c = zext <$N2 x i1> %b to <$N2 x i8>
            ret <$N2 x i8> %c
        """
    else
        ir = """
            %a = trunc i$c %0 to i$N2
            %b = bitcast i$N2 %a to <$N2 x i1>
            %c = zext <$N2 x i1> %b to <$N2 x i8>
            ret <$N2 x i8> %c
        """
    end
    quote
        $(Expr(:meta, :inline))
        v2 = Base.llvmcall($ir, NTuple{$N2, VecElement{Bool}}, Tuple{$U}, x)
        v = ntuple(Base.Fix1(getindex, v2), Val(N))
        Values{N,Bool}(unvec(v))
    end
end

#=
function convert2(::Type{Values{N,Bool}}, x::U) where {N, U <: Unsigned}
    c = bitsize(U)
    t = ntuple(i -> i <= c && !iszero(x & 1 << (i-1)), Val(N))
    Values{N,Bool}(t)
end
=#
