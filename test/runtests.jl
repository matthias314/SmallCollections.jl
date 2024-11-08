using Test, SmallCollections, BitIntegers

macro test_inferred(cmd, good)
    esc(quote
        let result = @inferred($cmd), good = $good
            @test isequal(result, good)
            @test typeof(result) == typeof(good)
            result
        end
    end)
end

macro test_inferred(cmd, good, type)
    esc(quote
        let result = @inferred($cmd), good = $good, type = $type
            @test isequal(result, good)
            if type isa Type
                @test result isa type
            else
                @test result isa typeof(type)
            end
            result
        end
    end)
end

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

Base.rand(::Type{String}) = string(rand(Char, 3)...)
Base.rand(::Type{Symbol}) = Symbol(rand(Char, 3)...)
Base.rand(::Type{T}) where T <: Enum = rand(instances(T))
Base.rand(::Type{TestStruct}) = TestStruct(map(rand, fieldtypes(TestStruct))...)
Base.rand(::Type{T}, n::Integer) where T <: Union{String,Symbol,TestEnum,TestStruct} = T[rand(T) for _ in 1:n]

test_types = (Int8, UInt64, Int128, UInt256, Float32, Float64, Char, String, Symbol, TestEnum, TestStruct)

include("bits.jl")
include("smallbitset.jl")
include("smallvector.jl")
include("packedvector.jl")
include("bangbang.jl")
