# R(5,5) — 41-vertex circulant structure

**Author:** Jared Wilder  
**Status:** exact structural/computational study of a classical 41-vertex circulant Ramsey witness; **not** a new Ramsey lower bound and **not** a claim that the graph is new.

This repository is the canonical public home for the estate's order-41 circulant `(5,5)` program.

The underlying 41-vertex graph is classical. The mathematically interesting release here is the exact structural package around it: complete classification inside the order-41 circulant family, explicit self-complementation, exact chromatic/circular/coding invariants, and—most sharply—a proof that the entire circulant phase **cannot survive intact into order 42 even after the new vertex is allowed completely arbitrary adjacency**.

## Structural headline: the order-41 circulant phase ends before 42

Let

`G = Cay(Z_41, ±{1,2,3,5,7,10,13,15,16,17})`.

The focused program establishes:

1. among all half-density circulant graphs on `Z_41`, exactly **20 labelled** `(5,5)` Ramsey connection sets survive;
2. all 20 lie in a single multiplier orbit, hence form **one affine-isomorphism class**;
3. multiplication by `9` sends the connection set to its complement and satisfies `9^2 ≡ -1 (mod 41)`, giving an explicit self-complementation;
4. the graph has exactly `1025` copies of `K4` and `1025` independent four-sets;
5. adjoining one new vertex with **unrestricted** adjacency to the old 41 vertices gives a `41`-variable, `2050`-clause extension CNF;
6. two independent exact methods—mixed-integer feasibility and an independently written DPLL solver—find that CNF infeasible; after normalizing by self-complementarity, the DPLL proof tree has only `21` nodes.

Therefore:

> **No order-41 circulant `(5,5)` Ramsey graph can be retained intact and extended by one arbitrary new vertex to an order-42 `(5,5)` Ramsey graph.**

Equivalently, every genuine 42-vertex `(5,5)` Ramsey graph must reorganize edges inside the old 41-vertex core; it cannot contain this unique order-41 circulant class as an induced 41-vertex subgraph.

This is strictly stronger than saying “there is no circulant witness on 42 vertices.” The new vertex is allowed to break circulant symmetry completely.

See [`program/ONE-VERTEX-EXTENSION.md`](program/ONE-VERTEX-EXTENSION.md) for the exact SAT formulation and certificate boundary, and [`program/README.md`](program/README.md) for the complete structural study.

Historical priority of the one-class classification, one-vertex nonextension theorem, and exact circular chromatic value remains unresolved; no novelty claim is inferred from search absence.

## Exact chromatic and coding structure

The same old graph has the exact extracted invariants

- `omega(G)=alpha(G)=4`;
- `chi(G)=11` and `chi(G-v)=10` for every vertex `v`;
- `chi_f(G)=chi_c(G)=41/4`;
- `Aut(G) ≅ D_41` with 82 graph automorphisms;
- an explicit optimal 41-word independent code in `G ⊠ G` from the complementing multiplier;
- classical Shannon capacity `Theta(G)=sqrt(41)` once vertex-transitive self-complementarity is invoked.

See [`program/SPECTRAL-AND-CODING.md`](program/SPECTRAL-AND-CODING.md). The capacity value is classical; the page records the arithmetic realization and exact graph invariants, not a novelty claim.

## Small Ramsey numbers in one Lean file

[`lean-proof/R55Final.lean`](lean-proof/R55Final.lean) proves `R(3,3)=6`, `R(3,4)=9`, `R(3,5)=14` and `R(4,4)=18` exactly, plus `25 <= R(4,5) <= 31` and `42 <= R(5,5) <= 62`. It is a single no-import Lean file.

### Fresh kernel audit — 2026-09-14

GitHub Actions run `34855581797` independently installed pinned **Lean 4.31.0-rc1**, compiled the full file, audited its admission surface, and then asked Lean itself for the dependency closure of the campaign theorem:

```text
'R55_CAMPAIGN' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The source contains exactly one standalone `sorry`, in the explicitly quarantined theorem `frontier_obligation62 : SufficesN 43 5 5`. The final theorem `R55_CAMPAIGN` does **not** depend on that admission: its `#print axioms` output contains no `sorryAx`.

So the correct authority statement is:

- the displayed classical exact Ramsey numbers and weaker bounds bundled by `R55_CAMPAIGN` are freshly kernel-checked;
- the separate attempted frontier obligation at 43 remains admitted and is **not** part of the campaign theorem;
- none of this improves the current research frontier for `R(5,5)`.

The replay workflow is in [`.github/workflows/lean-proof.yml`](.github/workflows/lean-proof.yml).

## Source layout

Exact public source bytes are migrated under:

- `program/` — the focused structural program;
- `records/` — related compact records;
- `lean-proof/` — the audited Lean small-Ramsey package and receipts.

Construction-family exhaustion is never promoted into a general Ramsey bound unless the implication is actually valid.
