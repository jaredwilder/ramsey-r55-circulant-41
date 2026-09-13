# Exact finite SAT interface for the unresolved global R(5,5) problem

This file records a **proof interface**, not a proof of `R(5,5)`.

## Direct decision encodings

For a two-coloring of `K_n`, use one Boolean variable for each edge; interpret true/false as the two colors. For every 5-subset of vertices, emit one clause forbidding all ten induced edges from being true and one clause forbidding all ten from being false.

The campaign generated the following direct DIMACS instances:

### Order 42

- variables: `C(42,2)=861`;
- clauses: `2*C(42,5)=1,701,336`;
- recorded file: `r55_n42.cnf`;
- SHA-256: `fb5ee4fb6c3981aa87c72a5aa73a4f23cc6fbedc549a997e0cbfead50b48e14c`.

The instance is satisfiable exactly when there exists a 42-vertex `(5,5)` Ramsey witness, i.e. exactly when `R(5,5)>42`.

### Order 43

- variables: `C(43,2)=903`;
- clauses: `2*C(43,5)=1,925,196`;
- recorded file: `r55_n43.cnf`;
- SHA-256: `9cb36cfd39aebd5a37a1c2115efa20f76332a55ab4c224da2ac7ccee249882be`.

The instance is unsatisfiable exactly when `R(5,5)<=43`.

The historical CNF bytes are not currently present as standalone public artifacts in this estate extraction. Their hashes and exact semantics are released so future recovery can be checked byte-for-byte.

## Lean composition shell

The campaign also created `R55.lean`. The source audit records:

- the file typechecked;
- exactly **two** `sorry` warnings remained;
- the holes were declarations `gap1_at_42` and `gap2_at_43`;
- the composition theorem `close_CC55` itself contained no additional `sorry` and derived the desired close from precisely those two obligations.

This is useful as a machine-checkable decomposition of the target, but it proves **nothing** until both holes are discharged.

The release therefore states the proof status exactly as:

> **UNRESOLVED FINITE INTERFACE — two explicit global obligations remain.**

## Why restricted-family negatives do not fill the holes

The campaign repeatedly enforced this distinction:

- no circulant witness at 42 does not establish global unsatisfiability;
- one-vertex inextensibility of a particular 41-vertex core does not establish global unsatisfiability;
- local-search budget exhaustion does not establish either SAT or UNSAT;
- a timed-out circulant run at 43 proves nothing even about the full circulant family.

This file is published specifically to keep those boundaries machine-visible rather than allow a family obstruction to drift into a global Ramsey claim.