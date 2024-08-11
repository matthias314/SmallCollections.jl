using Documenter
using SmallCollections

DocMeta.setdocmeta!(SmallCollections, :DocTestSetup, quote
        using SmallCollections
        # for jldoctest in docstrings
    end; recursive = true)

makedocs(sitename = "SmallCollections.jl",
    modules = [SmallCollections],
    format = Documenter.HTML(),
    warnonly = true)
