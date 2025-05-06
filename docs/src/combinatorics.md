```@meta
DocTestSetup = :(using SmallCollections)
```

# [Combinatorics](@id combinatorics)

```@docs
Combinatorics
```

## Subsets and set compositions

When used with a `SmallBitSet` as first argument, the following functions internally use
the function [`pdep`](@ref SmallCollections.pdep).
As discussed in the docstring for `pdep`, performance is much better if the processor supports the BMI2 instruction set.
The same applies to `set_compositions` with more than two parts, even if the first argument is not a `SmallBitSet`.

```@docs
subsets(::Integer)
subsets(::Integer, ::Integer)
set_compositions
set_compositions_parity(::Vararg{Integer})
set_composition_parity
```

## Permutations

```@docs
permutations
permutations_parity_transposition
```
