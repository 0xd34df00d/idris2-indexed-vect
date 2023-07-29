**indexed-vect** — like `Data.Vect`, but with element types indexed by their position in the vector

As a simplest example, consider a vector of `5` elements
where each element also carries a proof that it is equal to its index in the vector.
This is unexpressable with the standard `Data.Vect`, but we can do this:
```idris
sample : IVect 5 (\idx => (n ** n = idx))
sample = [ (0 ** Refl), (1 ** Refl), (2 ** Refl), (3 ** Refl), (4 ** Refl) ]
```

Merely copying `Data.Vect`'s API is not a good idea since some APIs won't work,
so if there's a particular use case that this library misses,
please open an issue, and hopefully we'll be able to implement that!
