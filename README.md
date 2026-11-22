# JSP-000448 — Multicolour Ramsey numbers of trees

Lean 4 formalization for [JSP-000448](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0401-0500.md#JSP-000448)
(Erdős problem 557, Erdős–Graham 1975):

> Does the multicolor Ramsey number of a tree grow linearly with its order?

**What is proved.** Yes for the upper bound: `R_r(T) ≤ r·n + O(1)` for every tree
`T` on `n` vertices — precisely `R_r(T) ≤ r(n-2) + 2` — together with `R_r(T) ≥ n`,
and exact values showing that this upper bound cannot be improved in general.

**What is not proved.** The two-sided equality `R_r(T) = r·n + O(1)`. For a fixed
number of colours it is false for some trees: the two-colour Ramsey number of the
path on `n` vertices is `⌊3n/2⌋ − 1` (Gerencsér–Gyárfás 1967). That fact is not
formalized here.

**This is a formalization of known mathematics**, not new mathematics; see
[References](#references).

## Main declarations (`JSP448.lean`)

`k` = number of edges of the tree (`n = k + 1` vertices).

| Declaration | Statement |
| --- | --- |
| `JSP448.ramseyNumber` | `R_r(T)` = least `n` such that every `r`-colouring of the edges of `K_n` has a monochromatic copy of `T`. |
| `JSP448.ramseyNumber_tree_linear` | `k + 1 ≤ R_r(T) ≤ r*k + 1` for `r ≥ 1`, `k ≥ 1`. |
| `JSP448.ramseyNumber_tree_le_tight` | `R_r(T) ≤ r*(k-1) + 2` for every tree and every `r`. |
| `JSP448.ramseyNumber_tree_le_parity` | `R_r(T) ≤ r*(k-1) + 1` when `r` and `k` are both even. |
| `JSP448.ramseyNumber_star_all` | Stars, all `r ≥ 1`, `k ≥ 1`: `R_r = r(k-1) + 1` if `r` and `k` are both even, `r(k-1) + 2` otherwise (diagonal case of Burr–Roberts). |
| `JSP448.ramseyNumber_tree_eq_of_prime` | For every prime `p`, every tree with `p` edges has `R_{p+1}(T) = p² + 1` (so the tight bound is attained by every such tree when `r = p + 1`). |
| `JSP448.multicolor_ramsey_trees_asym_tight` | Off-diagonal: with trees of `kᵢ` edges in colour `i`, `∑ (kᵢ − 1) + 2` vertices suffice. |
| `JSP448.ramseyNumber_tree_error_unbounded` | One-sided remark: no constant independent of `r` bounds `r·n − R_r(T)`. |
| `JSP448.starGraph_isTree`, `JSP448.exists_star_tree`, `JSP448.ramsey_set_nonempty` | Non-vacuity. |

Every declaration depends only on the standard axioms `propext`, `Classical.choice`,
`Quot.sound`. No `sorry`, no extra axioms, no `native_decide`.

## How the proofs go

A longer account is in [docs/exposition.md](docs/exposition.md).

*Upper bounds.* The input is the Erdős–Sós theorem (JSP-000439): a graph on `n`
vertices with no copy of some tree with `k` edges has at most `(k−1)n/2` edges. The
`r` colour classes cover all `n(n−1)/2` edges of `K_n`; if no class contained the
tree, `n(n−1)/2 ≤ r(k−1)n/2`, i.e. `n ≤ r(k−1) + 1`. When `r` and `k` are even and
`n = r(k−1) + 1`, equality would force each class to have exactly `(k−1)n/2` edges,
which is not an integer.

*Lower bounds.* Three explicit colourings:

- **cyclic** — on `Z_N`, `N = r(k−1)+1`, `k` odd: colour `{a,b}` by `⌊(d−1)/h⌋`,
  `d` the cyclic distance, `h = (k−1)/2`. Every vertex has `k−1` neighbours per colour.
- **matching** — `K_{M+1}` (`M` odd) splits into `M` perfect matchings; give each
  colour a block of `k−1` of them. Handles stars with `k` even.
- **affine plane** — on the `p × p` grid, colour an edge by its slope (`p + 1`
  colours). Edges of one colour lie on parallel lines of `p` points, so a connected
  graph on `p + 1` vertices does not fit.

## Relation to earlier formalizations

[zhangjun725/erdos557](https://github.com/zhangjun725/erdos557) (September 2026)
formalized the upper bounds `R_k(T) ≤ k(n−2) + 2` and, for `n` odd and `k` even,
`≤ k(n−2) + 1`, earlier than this repository, also from `tadamcz/erdos548`. The
upper bounds here are the same statements. What this repository adds are the
**lower-bound constructions and the resulting exact values** (stars; all trees with
`p` edges and `p + 1` colours), the off-diagonal form, and the trivial lower bound.

## Build

```
lake exe cache get
lake build
```

Toolchain `leanprover/lean4:v4.28.0`, Mathlib `v4.28.0`; the Erdős–Sós formalization
is imported, unmodified, as a Lake dependency pinned to
`tadamcz/erdos548@82ffb751f3d37768927df9239ed08439bbe0dd09` (the commit recorded in
the JSP-000439 catalog entry). See `lean-toolchain`, `lakefile.toml`,
`lake-manifest.json`. Verification notes: [docs/verification.md](docs/verification.md).

## References

- P. Erdős, R. L. Graham, *On partition theorems for finite graphs*, 1975 — the
  problem, the observation that the upper bound follows from Erdős–Sós, and the
  design-based lower bound (of which the affine-plane colouring is the simplest case).
- S. A. Burr, J. A. Roberts, *On Ramsey numbers for stars*, Utilitas Math. 4 (1973) —
  the star values.
- L. Gerencsér, A. Gyárfás, *On Ramsey-type problems*, 1967 — two-coloured paths.
- B. Reed, M. Stein, *The Erdős–Sós conjecture in dense graphs*, arXiv:2609.05417 —
  the catalog's publication reference for JSP-000448.
- D. R. Wood, *The Erdős–Sós Theorem*, arXiv:2609.17877 — exposition of the proof
  formalized in `tadamcz/erdos548`.
- Erdős problems [#557](https://www.erdosproblems.com/557), [#548](https://www.erdosproblems.com/548).

## Attribution and licence

- Erdős–Sós formalization (dependency, not part of this repository): Lean proof by
  GPT-6 Astra (OpenAI); repository `tadamcz/erdos548` prepared under the direction of
  Tom Adamczewski (Epoch AI); problem statement credited there to Thomas F. Bloom's
  erdosproblems.com. Apache-2.0.
- This repository: `JSP448.lean` © 2026 seina369, written with the assistance of
  Claude (Anthropic). Apache-2.0, see `LICENSE`.
