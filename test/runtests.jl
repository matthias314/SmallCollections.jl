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

include("bits.jl")
include("smallbitset.jl")
include("smallvector.jl")
include("packedvector.jl")
include("bangbang.jl")
