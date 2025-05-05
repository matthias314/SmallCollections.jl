using Documenter
using SmallCollections
using SmallCollections.Combinatorics
using StaticArrays: StaticArrays

DocMeta.setdocmeta!(SmallCollections, :DocTestSetup, quote
        using SmallCollections
        using SmallCollections.Combinatorics
        # for jldoctest in docstrings
    end; recursive = true)

makedocs(sitename = "SmallCollections.jl",
    modules = [
        SmallCollections,
        SmallCollections.Combinatorics,
        Base.get_extension(SmallCollections, :StaticArraysExt),
    ],
    pages = [
        "index.md",
        "fixedvector.md",
        "capacityvector.md",
        "broadcast.md",
        "smalldict.md",
        "smallset.md",
        "smallbitset.md",
        "combinatorics.md",
        "bangbang.md",
        "nonexported.md",
    ],
    format = Documenter.HTML(),
    warnonly = true)
