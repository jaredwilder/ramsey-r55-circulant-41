# Exact fixed-k extension criterion for a K5-free two-colouring

**Author:** Jared Wilder  
**Recovered from:** R(5,5) estate gold ledger, Pass 3  
**Public extraction:** 2026-09-11

This theorem is more general than the order-41 circulant application elsewhere in this directory.
It describes **any** attempt to append `k` new vertices to a fixed red/blue colouring of a complete
graph while leaving every old edge untouched.

## Theorem

Let `G` be a red/blue colouring of the complete graph on an old vertex set `V`, and assume `G`
contains no monochromatic `K5`. Add a finite new vertex set `W`, colour every edge inside `W`, and
colour every edge between `W` and `V`.

For a colour `c∈{red,blue}` and a subset `Q⊆W`, let

\[
N_c(Q)=\{v\in V:\text{ every edge }qv\text{ with }q\in Q\text{ has colour }c\}.
\]

Then the extended colouring is monochromatic-`K5`-free **if and only if** both conditions hold:

1. the colouring induced on `W` contains no monochromatic `K5`;
2. for every monochromatic `j`-clique `Q⊆W` of colour `c`, with
   `1<=j<=min(4,|W|)`, the old graph induced by `N_c(Q)` contains no monochromatic
   `K_{5-j}` of colour `c`.

Equivalently:

\[
\boxed{
Q\subseteq W\text{ mono-}K_j^c
\Longrightarrow
G[N_c(Q)]\text{ is }K_{5-j}^c\text{-free}
}
\]

for every `j=1,2,3,4`, together with the requirement that `W` itself contain no monochromatic
`K5`.

## Proof

Every monochromatic `K5` in the extension uses some number `j` of new vertices.

- `j=0` is impossible because the old base `G` is already monochromatic-`K5`-free.
- `j=5` is exactly a monochromatic `K5` lying wholly inside `W`.
- For `1<=j<=4`, let `Q` be the `j` new vertices of such a monochromatic `K5`, of colour `c`.
  Then `Q` is a monochromatic `K_j` in `W`. The remaining `5-j` old vertices all lie in the common
  same-colour neighbourhood `N_c(Q)` and form a monochromatic `K_{5-j}` there.

Thus any monochromatic `K5` violates one of the stated conditions.

Conversely, if condition 1 fails, its monochromatic `K5` inside `W` is already forbidden. If
condition 2 fails for some monochromatic `Q`, append the offending old `K_{5-j}` inside
`N_c(Q)` to `Q`; all cross edges have colour `c` by definition of the common neighbourhood, so the
union is a monochromatic `K5`. This proves equivalence.

## One- and two-vertex special cases

For one new vertex `u`, let `A` be its red neighbourhood in `V`. The theorem becomes the exact
criterion already used in `ONE-VERTEX-EXTENSION.md`:

- red `G[A]` contains no red `K4`;
- blue `G[V\A]` contains no blue `K4`.

For two new vertices `u,v`, with red neighbourhoods `A,B`, the one-vertex `K4` conditions must hold
for both vertices. In addition:

- if `uv` is red, `G[A∩B]` contains no red triangle;
- if `uv` is blue, `G[(V\A)∩(V\B)]` contains no blue triangle.

This is exactly the recovered two-vertex criterion from the R(5,5) estate.

## Fixed-k SAT consequence

For fixed `k=|W|`, exact untouched-base extension can be encoded using

\[
kn+\binom{k}{2}
\]

Boolean edge-colour variables when `|V|=n`: `kn` new-to-old edges and `C(k,2)` new-to-new edges.
Clauses are generated from the theorem above by combining monochromatic subsets of `W` with
monochromatic old cliques of the complementary order.

For fixed `k`, the largest old cliques that need enumeration are `K4`s, so the naive base-side
enumeration is polynomial (`O(n^4)`) rather than a fresh search over all
`C(n+k,2)` edge colours. This does **not** make the global Ramsey problem easy; it makes the exact
question "can this particular base be retained intact?" sharply finite and structurally explicit.

## Extension depth

The source ledger packages this into a useful object invariant:

\[
e(G)=\max\{k:\text{ some untouched-base }k\text{-vertex extension remains mono-}K5\text{-free}\}.
\]

The theorem above is the exact decision criterion for `e(G)>=k`. Object-specific values from the
historical search are evidence about those particular stored colourings and are not promoted here
without their witness bytes.

## Scope boundary

This is a theorem about **untouched-base extension**, not arbitrary repair. A search that is allowed
to recolour old edges may cross an extension obstruction by substantially rewriting the base; the
historical campaign measured exactly that distinction.

No global value of `R(5,5)` follows from this theorem alone.

## License

Apache-2.0 for repository-authored material.
