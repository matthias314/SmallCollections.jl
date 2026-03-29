using SmallCollections, Chairmarks
using SmallCollections: uinttype, cpufeature, hasshuffle
import SmallCollections: shuffle

@info first(Sys.cpu_info()).model

@inline function shuffle(::Val{:default}, v, p::FixedVector{N,U}, _) where {N,U}
    if N > typemax(U)
        @inbounds v[p .+ one(UInt16)]
    else
        @inbounds v[p .+ one(U)]
    end
end

@inline function shuffle(::Val{:none}, v, p::FixedVector{N,U}, _) where {N,U}
    if N > typemax(U)
        map(i -> @inbounds(v[i+one(UInt16)]), p)
    else
        map(i -> @inbounds(v[i+one(U)]), p)
    end
end

for M in [16, 32, 64, 128, 256, 512, 1024]
    modes = [:default, :none]
    if Sys.ARCH in (:x86_64, :i686)
        cpufeature(:AVX) && M == 16 && push!(modes, :avx)
        cpufeature(:AVX2) && M == 32 && push!(modes, :avx2)
        cpufeature(:AVX512VBMI) && M <= 64 && push!(modes, :avx512)
        cpufeature(:AVX512VBMI) && M >= 128 && push!(modes, :avx512merge)
    end
    @show M, modes

    assert_ex = Expr(:comparison, [isodd(i) ? :(shuffle(Val($(QuoteNode(modes[(i+1)÷2]))), v, p, Val(true))) : :(==) for i in 1:2*length(modes)-1]...)

    vv = Expr(:$, :v)
    pp = Expr(:$, :p)
    bench_ex = Expr(:tuple, [:(shuffle(Val($(QuoteNode(mode))), $vv, $pp, Val(true))) for mode in modes]...)

    aa = Expr(:$, :a)
    bb = Expr(:$, :b)
    bench_map_ex = Expr(:tuple, [:(map!((v, p) -> shuffle(Val($(QuoteNode(mode))), v, p, Val(true)), $aa, $aa, $bb)) for mode in modes]...)

    @eval for T in [Int8, UInt8, Bool, Int16, UInt16, Float16, Int32, UInt32, Float32, Char, Int64, UInt64, Float64]
        N = $M ÷ sizeof(T)
        hasshuffle(Val(N), T, Val(true)) || continue
        U = uinttype(T)
        print("$T\t")
        v = rand(FixedVector{N,T})
        p = FixedVector{N,U}(rand(0:min(N-1, typemax(U)), N))
        @assert $assert_ex
        show(stdout, MIME("text/plain"), @b $bench_ex)
        print("\t\t")
        a = rand(FixedVector{N,T}, 1000)
        b = [FixedVector{N,U}(rand(0:min(N-1, typemax(U)), N)) for _ in 1:1000]
        show(stdout, MIME("text/plain"), @b $bench_map_ex)
        println()
    end
end
