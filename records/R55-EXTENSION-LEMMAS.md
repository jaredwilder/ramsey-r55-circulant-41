# Ramsey R(5,5) — untouched-base extension lemmas

**Status:** pure finite Ramsey-graph mathematics extracted from the September 2026 campaign.  
**Scope:** these are structural lemmas about extending an already `(5,5)`-Ramsey colouring while leaving the old edges unchanged. They are not a new bound on `R(5,5)` and no historical-novelty claim is made here.

Let `V` carry a red/blue colouring of `K_V` with no monochromatic `K_5`.

## 1. One-new-vertex extension criterion

Add a new vertex `v`. Let

\[
A=\{x\in V: vx\text{ is red}\}.
\]

Then the colouring extends to `V ∪ {v}` with the old colouring untouched **if and only if**

- the red graph induced by `A` contains no red `K_4`; and
- the blue graph induced by `V\setminus A` contains no blue `K_4`.

### Proof

Any new monochromatic `K_5` must contain `v`, because the old colouring on `V` was already valid. A red `K_5` through `v` is exactly `v` together with a red `K_4` in its red neighbourhood `A`. The blue case is identical on `V\setminus A`. Conversely, if both neighbourhood conditions hold, no monochromatic `K_5` containing `v` exists.

## 2. Two-new-vertex extension criterion

Add two new vertices `u,v`. Let

\[
A=\{x\in V: ux\text{ is red}\},\qquad
B=\{x\in V: vx\text{ is red}\}.
\]

An untouched-base extension exists **if and only if** there are sets `A,B` and a colour for `uv` such that

1. red[`A`] and red[`B`] contain no red `K_4`;
2. blue[`V\setminus A`] and blue[`V\setminus B`] contain no blue `K_4`;
3. if `uv` is red, red[`A∩B`] contains no red triangle;
4. if `uv` is blue, blue[`(V\setminus A)∩(V\setminus B)`] contains no blue triangle.

### Proof

A new monochromatic `K_5` uses either one or both new vertices. The one-new-vertex cases are exactly the two conditions from the previous lemma. If a monochromatic `K_5` uses both `u,v`, the edge `uv` has that colour and the remaining three old vertices must lie in both corresponding colour-neighbourhoods and form a monochromatic triangle. These are precisely conditions 3 and 4.

## 3. General descending obstruction order

For an untouched-base extension by `k` new vertices, any new monochromatic `K_5` using exactly `j` new vertices uses exactly `5-j` old vertices.

Therefore the extension constraints descend through old-base clique orders:

- `j=1`: old-base `K_4` obstructions;
- `j=2`: old-base `K_3` obstructions;
- `j=3`: old-base `K_2` obstructions;
- `j=4`: old-base `K_1` compatibility;
- `j=5`: a monochromatic `K_5` wholly among the new vertices.

More generally, for every `1≤j≤min(k,5)`, each monochromatic `j`-clique among the new vertices of a given colour imposes a forbidden monochromatic `(5-j)`-clique in the intersection of their old-base neighbourhoods of that colour.

This is an exact characterization schema, not merely a necessary heuristic.

## 4. Campaign consequence

The campaign’s successful growth from smaller witnesses was not a pure untouched-base extension process: its tabu/repair search was allowed to modify old edges. Hence failure of the criteria above at a given base does not imply that no larger `(5,5)` witness can be reached after recolouring the base.

That distinction is preserved because “extension impossible” and “repair search failed” are mathematically different statements.
