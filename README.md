# R(5,5) — 41-vertex circulant structure

**Author:** Jared Wilder  
**Status:** exact structural/computational study of a 41-vertex circulant Ramsey witness; not a new lower bound for `R(5,5)`.

This repository is the canonical public home for the estate's 41-vertex circulant `(5,5)` Ramsey program. The witness establishes `R(5,5) >= 42`, which is weaker than the published lower bound, but the estate's contribution here is the **exact internal structure** of this highly symmetric witness and its surrounding finite classification work.

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

## Structural package

The recovered program includes:

- affine/multiplier classification of the relevant half-density circulant family;
- an explicit self-complementing multiplier;
- exact clique, independence, chromatic, circular/fractional, automorphism, and polynomial data;
- one-vertex nonextension;
- fixed-`k` extension criteria and SAT interface;
- exact nonexistence statements inside specified circulant construction classes.

The graph is kept distinct from Paley(41); the program records that the chosen witness is not strongly regular and that Paley(41) is not itself a `(5,5)` witness.

## Source layout

Exact public source bytes are migrated under:

- `program/` — `unpublished-math-papers/ramsey-r55-circulant-structure/`;
- `records/` — the related `combinatorial-records/ramsey-r55/` material.

Construction-family exhaustion is never promoted into a general Ramsey bound unless the logical implication is actually valid.
