using SmallCollections, Chairmarks
using SmallCollections: uinttype, cpufeature
import SmallCollections: shuffle

@info first(Sys.cpu_info()).model

@inline shuffle(::Val{:default}, v, p::FixedVector{N,U}) where {N,U} = @inbounds v[p .+ one(U)]
@inline shuffle(::Val{:none}, v, p::FixedVector{N,U}) where {N,U} = map(i -> @inbounds(v[i+one(U)]), p)

for M in [16, 32, 64, 128]
    modes = [:default, :none]
    if Sys.ARCH in (:x86_64, :i686)
        cpufeature(:AVX) && M == 16 && push!(modes, :avx)
        cpufeature(:AVX2) && M == 32 && push!(modes, :avx2)
        cpufeature(:AVX512VBMI) && M <= 64 && push!(modes, :avx512)
        cpufeature(:AVX512VBMI) && M == 128 && push!(modes, :avx512_1024)
    end
    @show M, modes

    assert_ex = Expr(:comparison, [isodd(i) ? :(shuffle(Val($(QuoteNode(modes[(i+1)÷2]))), v, p)) : :(==) for i in 1:2*length(modes)-1]...)

    vv = Expr(:$, :v)
    pp = Expr(:$, :p)
    bench_ex = Expr(:tuple, [:(shuffle(Val($(QuoteNode(mode))), $vv, $pp)) for mode in modes]...)

    aa = Expr(:$, :a)
    bb = Expr(:$, :b)
    bench_map_ex = Expr(:tuple, [:(map!((v, p) -> shuffle(Val($(QuoteNode(mode))), v, p), $aa, $aa, $bb)) for mode in modes]...)

    @eval for T in [Int8, UInt8, Bool, Int16, UInt16, Float16, Int32, UInt32, Float32, Char, Int64, UInt64, Float64]
        N = $M ÷ sizeof(T)
        U = uinttype(T)
        print("$T\t")
        v = rand(FixedVector{N,T})
        p = FixedVector{N,U}(rand(0:N-1, N))
        @assert $assert_ex
        show(stdout, MIME("text/plain"), @b $bench_ex)
        print("\t\t")
        a = rand(FixedVector{N,T}, 1000)
        b = [FixedVector{N,U}(rand(1:N, N)) for _ in 1:1000]
        show(stdout, MIME("text/plain"), @b $bench_map_ex)
        println()
    end
end
