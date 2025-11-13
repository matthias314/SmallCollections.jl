using Test, SmallCollections, BitIntegers

using SmallCollections: LazyStyle, EagerStyle, RigidStyle, StrictStyle, SmallLength

using Unitful: Unitful, Quantity, @u_str, dimension, ustrip

numerictype(::Type{T}) where T = T
numerictype(::Type{<:Quantity{T}}) where T = T

setnumerictype(::Type, ::Type{S}) where S = S
setnumerictype(::Type{Quantity{T,D,U}}, ::Type{S}) where {T,D,U,S} = Quantity{S,D,U}

unitrange(a, b) = a:b
unitrange(a::Quantity, b::Quantity) = a:oneunit(a):b

@inline Base.isodd(x::Quantity) = isodd(ustrip(x))  # otherwise we get an infinite recursion

macro test_inferred(expr, good, goodtype = missing)
    msg = """

        expression:      $expr
        expected result: $good
        expected type:   $(goodtype === missing ? "type of expected result" : goodtype)
        location:        $(something(__source__.file, :none)):$(__source__.line)

        """
    quote
        let good = $good, goodtype = $goodtype,
                result = try
                    @inferred($expr)
                catch e
                    printstyled($msg; bold = true, color = :magenta)
                    rethrow(e)
                end
            if goodtype === missing
                goodtype = typeof(good)
            elseif !(goodtype isa Type)
                goodtype = typeof(goodtype)
            end
            testresult = @test isequal(result, good)
            if testresult isa Test.Pass
                testresult = @test result isa goodtype
            end
            testresult isa Test.Pass || printstyled($msg; bold = true, color = :magenta)
            result
        end
    end |> esc
end

BitIntegers.@define_integers 440

@enum TestEnum::Int16 begin
    Item1 = 5
    Item2 = 7
    Item3 = 8
end

using StructEqualHash: @struct_equal_hash

abstract type AbstractTestStruct end

struct TestStruct1 <: AbstractTestStruct
    x::SmallBitSet{UInt32}
end

struct TestStruct2 <: AbstractTestStruct
    x::TestStruct1
    y::UInt16
end

@struct_equal_hash TestStruct1
@struct_equal_hash TestStruct2

# custom rand settings

using Random: Random, AbstractRNG, SamplerType

Random.rand(rng::AbstractRNG, ::SamplerType{String}) = string(rand(Char, 3)...)
Random.rand(rng::AbstractRNG, ::SamplerType{Symbol}) = Symbol((rand_notin(Char, ('\0',)) for _ in 1:3)...)
Random.rand(rng::AbstractRNG, ::SamplerType{T}) where T <: Enum = rand(instances(T))
Random.rand(rng::AbstractRNG, ::SamplerType{T}) where T <: AbstractTestStruct = T(map(rand, fieldtypes(T))...)

function rand_notin(::Type{T}, c) where T
    local x
    while true
        x = rand(T)
        x in c || break
    end
    x
end

rand_unique(::Type{T}, m::Integer) where T = foldl((v, _) -> push!(v, rand_notin(T, v)), 1:m; init = T[])

test_types = (Int8, UInt64, typeof(Int128(1)u"m"), UInt256, typeof(Float32(1)u"s"), Float64, Char, String, Symbol, TestEnum, TestStruct1, TestStruct2)

# isvalid

function isvalid(v::AbstractSmallVector{N,T}) where {N,T}
    n = length(v)
    0 <= n <= N && all(==(SmallCollections.default(T)), view(v.b, n+1:N))
end

function isvalid(v::PackedVector{U,N,T}) where {U,N,T}
    n = length(v)
    mask = one(U) << (n*N) - one(U)
    iszero(v.m & ~mask)
end

isvalid(d::AbstractSmallDict) = isvalid(d.keys) && isvalid(d.vals) && allunique(d.keys) && length(d.keys) == length(d.vals)

isvalid(s::AbstractSmallSet) = isvalid(s.d)

# run test files

if isempty(ARGS)
    push!(ARGS,
        "bits.jl", "smallbitset.jl", "fixedvector.jl", "smallvector.jl",
        "packedvector.jl", "smalldict.jl", "smallset.jl", "bangbang.jl")
end

foreach(include, ARGS)
