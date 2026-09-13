# Ramsey R(5,5) — pure-math campaign extraction

**Campaign deep dive:** 2026-09-04  
**Court:** the campaign **did not improve the world bound on `R(5,5)`**.  
**Purpose:** release the exact finite computations and hidden structure without mislabeling prior-art reconstruction as a new Ramsey bound.

At the time of the audit, the live literature bracket was

\[
43\le R(5,5)\le46.
\]

The campaign's 41-vertex witness proves only `R(5,5)>=42`, weaker than the known lower bound. Its importance in this estate is computational reconstruction and exact structure, not a world-record diagonal Ramsey result.

## 1. The 41-vertex circulant witness

Define

\[
G=\operatorname{Cay}(\mathbb Z_{41},S),
\]

with

\[
S=\pm\{1,2,3,5,7,10,13,15,16,17\}.
\]

Equivalently,

\[
S=\{1,2,3,5,7,10,13,15,16,17,24,25,26,28,31,34,36,38,39,40\}.
\]

The session independently checked that `G` has neither a `K5` nor an independent 5-set. Therefore `G` is a valid 41-vertex `(5,5)` Ramsey graph and establishes only

\[
R(5,5)>41.
\]

That witness is old; the exact connection set appears in the specialist circulant-Ramsey literature.

## 2. Exact exhaustive `Z_42` family obstruction

The dedicated order-42 run checked all

\[
2^{21}-1=2,097,151
\]

nonempty inverse-closed connection choices for circulants on `Z_42` and found no `(5,5)` witness.

The correct theorem is therefore:

> **There is no circulant `(5,5)` Ramsey graph on `Z_42`.**

This is a **restricted-family obstruction**. It is not an upper bound on `R(5,5)` and says nothing about arbitrary noncirculant 42-vertex witnesses. The same circulant obstruction was already present in prior literature / later dedicated computational work, so no novelty claim is made here.

## 3. Nonmonotonicity inside the circulant family

The campaign exhaustively records the `(5,5)` circulant pattern

- no witness at `n=39`;
- witness at `n=40`;
- witness at `n=41`;
- no witness at `n=42`.

On the `(4,5)` lane it records

- no circulant witness at `n=23`;
- witness at `n=24`.

This is enough to kill any naive monotonicity inference inside the restricted circulant family.

## 4. Reconstruction of the Harborth–Krause table

For directly comparable `(5,5)` positive witness rows, the unattended campaign reconstructed **15 of 16** connection sets digit-for-digit from the 2003 Harborth–Krause table. The sole mismatch at order 26 is a different valid witness.

Recovered positive half-connection sets include:

| n | half connection set |
|---:|---|
| 25 | `1,2,3,5,8` |
| 26 | `2,4,6,10` — different valid witness from the published row |
| 27 | `1,3,4,6,7` |
| 28 | `1,2,10,11,12` |
| 29 | `1,2,3,8,10,11` |
| 30 | `1,4,5,6,7,8` |
| 31 | `1,2,3,11,12,13` |
| 32 | `1,2,3,10,12,13,14` |
| 33 | `1,2,3,5,12,13,15` |
| 34 | `1,2,6,7,8,15,16` |
| 35 | `1,2,3,5,12,13,14,16` |
| 36 | `1,2,4,5,12,14,15,16` |
| 37 | `1,2,6,8,9,11,12,17` |
| 38 | `1,2,6,10,11,12,15,17,18` |
| 40 | `1,2,4,5,7,12,16,17,18` |
| 41 | `1,2,3,5,7,10,13,15,16,17` |

The campaign likewise reproduced the explicitly tabulated `(4,5)` circulant rows it compared against.

The research fact being released here is therefore **independent computational reconstruction of a specialized published witness table**, not independent invention of those already-published witnesses.

## 5. Hidden structure mined from the known order-41 graph

A later second-pass audit extracted exact structure from the order-41 graph:

\[
G\cong\overline G,
\qquad
\chi(G)=11,
\qquad
\chi(G-v)=10\quad\text{for every vertex }v,
\]

\[
\operatorname{Aut}(G)\cong D_{41},
\qquad
\alpha(G)=\omega(G)=4.
\]

The report also records exact clique/independence polynomial data and local incidence counts. These are valid deductions/checks for a known graph. Focused searches did not locate all of them explicitly for this exact connection set, but **that is not a publication-grade novelty certificate**. A serious novelty claim would require a catalog/isomorphism audit against the original Clapham construction, Ramsey graph databases, and subsequent classifications.

An explicit color-swap multiplier `x -> 9x` gives the self-complementation in the recovered audit.

## 6. Claims deliberately demoted

The release preserves the campaign's corrections:

- half density is **not** a necessary property of arbitrary diagonal Ramsey witnesses; here it comes from self-complementarity;
- failed circulant search is only a **circulant-family** obstruction;
- timeouts at 43–45 prove nothing;
- the usual Ramsey recursion and parity sharpening are classical input, not new mathematics;
- `R(3,3)=6` is calibration rather than research novelty;
- the 41-vertex witness does not improve the known `R(5,5)` lower bound.

## 7. Reproducibility status

The source deep dive records companion artifacts `r55_hidden_invariants.py` and `r55_hidden_invariants.json` that recompute the order-41 invariants from its connection set. Those post-session mining artifacts are distinct from what the unattended run itself explicitly discovered.

## Court

The campaign did **not** solve `R(5,5)` and did **not** establish a major new Ramsey-number bound. Its public mathematical value is an exact restricted-family computation, independent reconstruction of specialized historical data, and a set of exact structural invariants mined from the known 41-vertex circulant graph.