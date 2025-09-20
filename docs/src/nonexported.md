```@meta
DocTestSetup = :(using SmallCollections)
```

# Non-exported names

## Public names

### Functionality for small and fixed vectors

```@docs
SmallCollections.default
SmallCollections.isfasttype
SmallCollections.MapStyle
SmallCollections.FixedVectorStyle
SmallCollections.SmallVectorStyle
SmallCollections.padtail
```

### Bit operations

```@docs
SmallCollections.bitsize
SmallCollections.unsafe_shl
SmallCollections.unsafe_lshr
SmallCollections.blsi
SmallCollections.blsr
SmallCollections.blsmsk
SmallCollections.pdep
SmallCollections.pext
```

## Internal names

These names are not public and may change in future versions.

```@docs
SmallCollections.element_type
SmallCollections.AbstractBitInteger
SmallCollections.top_set_bit
SmallCollections.shuffle
SmallCollections.shufflewidth
```
