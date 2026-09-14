# R(5,5) — 41-vertex circulant structure

**Author:** Jared Wilder  
**Status:** exact structural/computational study of a 41-vertex circulant Ramsey witness; not a new lower bound for `R(5,5)`.

This repository is the canonical public home for the estate's 41-vertex circulant `(5,5)` Ramsey program. The witness establishes `R(5,5) >= 42`, which is weaker than the published lower bound, but the estate's contribution here is the **exact internal structure** of this highly symmetric witness and its surrounding finite classification work.

## New: small Ramsey numbers in one Lean file

[`lean-proof/`](lean-proof/) proves R(3,3)=6, R(3,4)=9, R(3,5)=14 and R(4,4)=18 exactly, plus 25 ≤ R(4,5) ≤ 31 and 42 ≤ R(5,5) ≤ 62. It's a single file with no imports, checked by the Lean kernel.

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
