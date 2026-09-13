# Spectral, circular-colouring, resolution and zero-error structure

Let

`G=Cay(Z_41, ±{1,2,3,5,7,10,13,15,16,17})`.

This note records exact deductions from the September-4 third-pass audit. Most use classical graph-theoretic theorems applied to this old graph; they are released as structural mathematics, not novelty claims.

## Fractional and circular chromatic number

Since `G` is vertex-transitive and `alpha(G)=4`,

`chi_f(G)=41/4`.

Define

`f(x)=31x mod 41`,

where `31=4^{-1} mod 41`. Under this permutation, graph edges avoid circular distances `1,2,3`, giving a `(41,4)` circular coloring. Hence

`chi_c(G) <= 41/4`.

The general inequality `chi_f <= chi_c` gives equality:

> `chi_f(G)=chi_c(G)=41/4`.

In particular `chi(G)=11`.

## Explicit strong-square code and Shannon capacity

The map

`phi(x)=9x mod 41`

is an isomorphism `G -> complement(G)`.

Consider

`C={(x,9x): x in Z_41}`

inside the strong square `G ⊠ G`. For distinct `x,y`, exactly one of `xy` and `phi(x)phi(y)` is an edge, so the corresponding two codewords are nonadjacent in the strong product. Therefore

`alpha(G ⊠ G) >= 41`.

For a vertex-transitive self-complementary graph on 41 vertices, Lovász's classical theorem gives

`theta(G)=Theta(G)=sqrt(41)`.

Multiplicativity of `theta` gives the reverse strong-square bound, so

> `alpha(G ⊠ G)=41`, and `C` is an explicit optimal zero-error code for the square.

Consequently

> `Theta(G)=sqrt(41)`.

The capacity value is classical once vertex-transitive self-complementarity is recognized; the displayed optimal code is the direct arithmetic realization furnished by the multiplier-9 symmetry.

## Dual four-set resolutions after deleting one vertex

For every vertex `v`, the graph `G-v` partitions into ten independent four-sets. Applying the complementing multiplier gives simultaneously a partition into ten `K4`s.

Thus for every `v`:

- `G-v` has an independent-four-set resolution;
- `G-v` has a `K4` resolution.

Elementary arithmetic resolutions recorded by the audit are:

- independent-block step sizes `d in {4,6,9,11}`;
- clique-block step sizes `d in {1,5,13,17}`.

Multiplier `9` pairs the two families.

## Exact spectral self-complementarity

The characteristic polynomial has the form

`chi_G(x)=(x-20)P(x)^2`,

where `P` has degree 20. The nontrivial eigenvalues pair as

`lambda <-> -1-lambda`.

More strongly,

`P(x)=Q(x(x+1))`,

where

```text
Q(y)=y^10 - 100 y^9 + 4049 y^8 - 85970 y^7 + 1037731 y^6
     - 7228716 y^5 + 28351714 y^4 - 59077666 y^3
     + 56051861 y^2 - 13005734 y - 3020141.
```

Thus the complementing involution is visible directly in the reduced spectral coordinate `y=lambda(lambda+1)`.

## Bonus: the order-24 circulant `(4,5)` witness

The audited session also studied the old order-24 circulant graph with positive distances

`{1,2,4,8,9}`.

For this graph `G_24`:

- `alpha(G_24)=4`;
- `omega(G_24)=3`;
- an explicit partition into six independent four-sets gives `chi(G_24)=6`;
- an explicit partition into eight triangles gives `chi(complement(G_24))=8`;
- vertex transitivity yields
  `chi_f(G_24)=chi_c(G_24)=6` and
  `chi_f(complement(G_24))=chi_c(complement(G_24))=8`.

The underlying order-24 witness is known in the circulant Ramsey literature; these statements are published as exact extracted invariants, not as a new Ramsey construction.