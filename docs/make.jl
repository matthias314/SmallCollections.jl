using Documenter
using SmallCollections
using StaticArrays: StaticArrays

DocMeta.setdocmeta!(SmallCollections, :DocTestSetup, quote
        using SmallCollections
        # for jldoctest in docstrings
    end; recursive = true)

makedocs(sitename = "SmallCollections.jl",
    modules = [
        SmallCollections,
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
        "bangbang.md",
        "nonexported.md",
    ],
    format = Documenter.HTML(),
    warnonly = true)
