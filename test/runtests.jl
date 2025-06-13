using Test, SmallCollections, BitIntegers

using SmallCollections: LazyStyle, EagerStyle, RigidStyle, StrictStyle, SmallLength

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

struct TestStruct
    x::Char
    y::Int
end

@struct_equal_hash TestStruct

# custom rand function
rand(args...) = Base.rand(args...)
rand(::Type{String}) = string(rand(Char, 3)...)
rand(::Type{Symbol}) = Symbol(rand(Char, 3)...)
rand(::Type{T}) where T <: Enum = rand(instances(T))
rand(::Type{TestStruct}) = TestStruct(map(rand, fieldtypes(TestStruct))...)
rand(::Type{T}, n::Integer) where T <: Union{String,Symbol,TestEnum,TestStruct} = T[rand(T) for _ in 1:n]

function rand_notin(::Type{T}, c) where T
    local x
    while true
        x = rand(T)
        x in c || break
    end
    x
end

rand_unique(::Type{T}, m::Integer) where T = foldl((v, _) -> push!(v, rand_notin(T, v)), 1:m; init = T[])

test_types = (Int8, UInt64, Int128, UInt256, Float32, Float64, Char, String, Symbol, TestEnum, TestStruct)

if isempty(ARGS)
    push!(ARGS,
        "bits.jl", "smallbitset.jl", "fixedvector.jl", "smallvector.jl",
        "packedvector.jl", "smalldict.jl", "smallset.jl", "bangbang.jl", "combinatorics.jl")
end

foreach(include, ARGS)
