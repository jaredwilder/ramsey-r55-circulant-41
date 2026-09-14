# Small Ramsey numbers, proved from scratch in one Lean file

`R55Final.lean` proves these facts about two-colourings of complete graphs, starting from nothing but the definition:

| | |
|---|---|
| R(3,3) = 6 | exact |
| R(3,4) = 9 | exact |
| R(3,5) = 14 | exact |
| R(4,4) = 18 | exact |
| 25 ≤ R(4,5) ≤ 31 | bounds |
| 42 ≤ R(5,5) ≤ 62 | bounds |

None of these values is new. R(3,5) and R(4,4) have been known since the 1950s, and the published bounds on R(5,5) are tighter than ours (43 ≤ R(5,5) ≤ 46). What's interesting here is that all six results come out of the same small machine in a single self-contained file. For each pair, a colouring shows the lower bound and a counting chain shows the upper bound. You can see exactly how far the method reaches: it gets the first four values on the nose, and on R(4,5) its upper bound stops at 31 instead of the true 25.

## Check it

The whole result is one declaration:

```lean
theorem R55_CAMPAIGN :
    IsExactlyN 6 3 3 ∧ IsExactlyN 9 3 4 ∧ IsExactlyN 14 3 5 ∧ IsExactlyN 18 4 4 ∧
    (∀ N, IsExactlyN N 4 5 → 25 ≤ N ∧ N ≤ 31) ∧
    (∀ N, IsExactlyN N 5 5 → 42 ≤ N ∧ N ≤ 62)
```

The file has no imports, not even Mathlib. It compiles in about a minute on Lean 4 (v4.31.0-rc1):

```bash
lean R55Final.lean
```

To see what it depends on, add `#print axioms R55_CAMPAIGN` at the end. You should get only the three standard axioms: `propext`, `Classical.choice` and `Quot.sound`.

The file contains exactly one `sorry`, in `frontier_obligation62 : SufficesN 43 5 5`. That statement is the next open step, not a gap in the proof: proving it would show R(5,5) ≤ 43. `R55_CAMPAIGN` doesn't use it. The companion theorem `R55_OPEN` spells out what it would buy: if that one statement is ever proved, R(5,5) must be 42 or 43.

## Receipts

`receipts/` holds the kernel-run records for the final summary, the named upper-bound chain, and the checks that each counting step really bites on the colourings it is applied to.

Built September 4, 2026.
