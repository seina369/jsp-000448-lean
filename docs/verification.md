# Verification notes

Checks run on the sources of this repository before publication (2026-11-22).

| Check | Result |
| --- | --- |
| `lake build` (clean, 8029 jobs) | success, no warnings |
| `#print axioms` on every declaration of `JSP448` (enumerated from the environment) | only `propext`, `Classical.choice`, `Quot.sound` |
| `lean4checker` v4.28.0 on module `JSP448` and on `Erdos548.Resolutions.Erdos548_192usd_21h` | exit 0 (Mathlib `.olean`s not re-checked) |
| Scan for `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, `implemented_by`, custom syntax | none |
| Small values from the definition (independent brute force, outside Lean) | `R_2(K_{1,3}) = 6`, `R_2(K_{1,4}) = 7`, `R_2(K_{1,5}) = 10`, `R_3(K_{1,3}) = 8`, `R_1(K_{1,3}) = 4`, `R_2(K_{1,2}) = 3`, `R_3(K_{1,2}) = 5` — all equal to `ramseyNumber_star_all` |
| Consistency of `ramseyNumber_star_all` and `ramseyNumber_tree_eq_of_prime` on their overlap | both give `p² + 1` |

Three independent AI reviewers with no knowledge of how the proofs were written
audited an earlier revision (formal soundness; statement fidelity and literature
values; referee-style review). They found no formal or mathematical error; their
remarks on wording, attribution and generality were addressed afterwards (the tight
and parity upper bounds were then generalized from stars / `k ≥ 3` to all trees, and
`star` was renamed `starGraph`). The section on two-coloured paths
(`MonoPath` … `ramseyNumber_two_not_two_mul_sub_const`) was added after those reviews
and has been checked by the build, the axiom enumeration and `lean4checker` only.
The checks in the table above were re-run on the final sources (209 constants in
module `JSP448`, 67 user-facing).

To reproduce:

```
lake exe cache get && lake build
printf 'import JSP448\n#print axioms JSP448.ramseyNumber_star_all\n' > Ax.lean
lake env lean Ax.lean
```
