```@meta
DocTestSetup = :(using SmallCollections)
```

# [Combinatorics](@id combinatorics)

```@docs
Combinatorics
```

## Subsets and shuffles

When used with a `SmallBitSet` as first argument, the following functions internally use
the function [`pdep`](@ref SmallCollections.pdep).
As discussed in the docstring for `pdep`, performance is much better if the processor supports the BMI2 instruction set.
The same applies to `shuffles` with more than two parts, even if the first argument is not a `SmallBitSet`.

```@docs
subsets(::Integer)
subsets(::Integer, ::Integer)
set_compositions
shuffles(::Vararg{Integer})
shuffle_signbit
```

## Permutations

```@docs
permutations
permutations_sign_transposition
```
