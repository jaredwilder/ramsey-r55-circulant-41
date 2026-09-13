# No arbitrary one-vertex Ramsey extension of the 41-vertex circulant core

Let

`G=Cay(Z_41, ±{1,2,3,5,7,10,13,15,16,17})`.

The graph has exactly `1025` copies of `K4` and, by self-complementarity, exactly `1025` independent four-sets.

## Extension theorem

Add one new vertex `u` with **completely unrestricted** adjacency to the 41 old vertices. Let Boolean variable `x_v` mean that `u` is adjacent to old vertex `v`.

To prevent a `K5`, every old `K4`, `C`, imposes

`OR_{v in C} not x_v`.

To prevent an independent 5-set, every old independent 4-set, `I`, imposes

`OR_{v in I} x_v`.

Therefore one-vertex extension is exactly a Boolean satisfiability problem with

- 41 variables;
- 1025 negative four-literal clauses from `K4`s;
- 1025 positive four-literal clauses from independent 4-sets;
- 2050 clauses total.

Two materially different exact computations found this formula infeasible:

1. mixed-integer feasibility;
2. an independently written DPLL solver with unit propagation.

Using the graph-to-complement symmetry to normalize `x_0=1`, the DPLL proof explores only **21 nodes** before every branch closes.

Hence:

> **Theorem.** `G` has no one-vertex `(5,5)` Ramsey extension.

Because the 41-vertex circulant `(5,5)` family has only one affine-isomorphism class:

> **Corollary.** No 41-vertex circulant `(5,5)` Ramsey graph can be retained intact and extended by one arbitrary vertex to a 42-vertex `(5,5)` Ramsey graph.

Equivalently, every genuine 42-vertex `(5,5)` Ramsey graph must avoid this unique 41-vertex circulant graph as an induced 41-vertex subgraph.

This is strictly stronger than the older statement that there is no **circulant** witness on `Z_42`: even breaking circulant symmetry completely at the new vertex cannot preserve the order-41 core.

## Small branching certificate

With `x_0=1`, the recorded DPLL trace branches only on

`1,5,13,28,7,15,2,16,25,8`

before unit propagation closes every branch.

Representative terminal conflicts include the old-graph four-sets

- `K4 {9,19,24,34}`;
- `I4 {3,15,26,38}`;
- `K4 {19,21,34,36}`;
- `I4 {2,10,31,39}`;
- `I4 {3,17,26,40}`;
- `K4 {20,22,25,35}`;
- `I4 {18,26,32,40}`.

The original machine trace was part of the September-4 audit package but has not yet been recovered as a standalone public artifact in this estate pass. The theorem statement and the two-independent-method verification are therefore published now, with exact artifact recovery left as a provenance task rather than reconstructed from memory.

## Novelty boundary

Focused searches in the source audit did not find this exact one-vertex nonextension theorem stated for the old 41-vertex circulant graph. Because the underlying graph is decades old and graph catalogs/computations may contain unpublished or poorly indexed invariants, **no historical-priority claim is made**.