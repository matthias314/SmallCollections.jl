using SmallCollections: bitsize, top_set_bit

BitIntegers.@define_integers 440

@testset "bitsize" begin
    for T in (Int8, UInt16, Int32, UInt64, Int128, UInt256, Int440)
        @test_inferred bitsize(T) 8*sizeof(T)
    end
end

@testset "top_set_bit" begin
    for T in (UInt8, UInt16, UInt32, UInt64, UInt128, UInt256, UInt512, UInt440)
        @test_inferred top_set_bit(T(0)) 0
        m = bitsize(T)
        x = T(1) << (m-3) - T(3)
        @test_inferred top_set_bit(x) m-3
    end
end
