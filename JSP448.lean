/-
Copyright (c) 2026 seina369. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Formalized with the assistance of Claude (Anthropic).
-/
import Mathlib
import Erdos548.Resolutions.Erdos548_192usd_21h

/-!
# JSP-000448 — Multicolour Ramsey numbers of trees are linear in the order

**Problem (Erdős–Graham, 1975; Erdős problem 557).** Is the `r`-colour Ramsey number
of a tree `T` on `n` vertices equal to `r·n + O(1)`?  In the catalog's words: does the
multicolour Ramsey number of a tree grow linearly with its order?

**What is proved here.** The upper bound `R_r(T) ≤ r·n + O(1)` (indeed
`R_r(T) ≤ r(n-2) + 2`), which is the part that follows from the Erdős–Sós theorem;
the trivial lower bound `R_r(T) ≥ n`; and exact values showing the upper bound
cannot be improved in general.  The two-sided equality `R_r(T) = r·n + O(1)` is
*not* proved, and for fixed `r` it is false for some trees (e.g. two-coloured paths,
Gerencsér–Gyárfás 1967); that fact is not formalized here.

All of the mathematics is known; this file is a formalization.  Upper bounds:
Erdős–Graham's observation applied to the Erdős–Sós theorem.  Stars: Burr–Roberts
(1973).  Affine-plane lower bound: the simplest case of Erdős–Graham's design
construction.

## Results

Write `k` for the number of edges of the tree (`k + 1 = n` vertices), and `j = k - 1`.

* `ramseyNumber_tree_linear` : for all `r ≥ 1`, `k ≥ 1`, every tree `T` with `k` edges
  satisfies `k + 1 ≤ R_r(T) ≤ r*k + 1`.
* `ramseyNumber_tree_le_tight` : `R_r(T) ≤ r*(k-1) + 2` for every tree and every `r`.
* `ramseyNumber_tree_le_parity` : if `r` and `k` are both even, `R_r(T) ≤ r*(k-1) + 1`.
* `ramseyNumber_star_all` : stars (diagonal case of Burr–Roberts), every `r ≥ 1` and
  every `k ≥ 1`: `R_r = r(k-1) + 1` if `r` and `k` are both even, and
  `R_r = r(k-1) + 2` otherwise.  (`ramseyNumber_star_eq`, `ramseyNumber_star` are the
  case `k` odd, proved by a different colouring.)
* `ramseyNumber_tree_eq_of_prime` : for each prime `p`, *every* tree with `p` edges
  has `R_{p+1}(T) = p² + 1`; so with `r = p + 1` colours the tight bound
  `r(k-1) + 2` is attained by every tree with `k = p` edges.
* `multicolor_ramsey_trees_asym_tight` : the off-diagonal version, a different tree
  size for each colour.
* `ramseyNumber_tree_error_unbounded` : a one-sided remark — no constant independent
  of `r` bounds `r·n - R_r(T)`.
* `starGraph_isTree`, `exists_star_tree`, `ramsey_set_nonempty` : non-vacuity.

## Method

The linear upper bound uses JSP-000439 (the Erdős–Sós conjecture) as formalized in
`Erdos548.erdos_548`: the `r` colour classes cover all `n(n-1)/2` edges of `K_n`, so
if each had fewer than `(k-1)/2·n + 1` edges the total would be too small.  The tight
and parity bounds use the sharper statement behind it, `Erdos548.tree_free_edge_bound`
(a graph with no copy of a tree with `k` edges has at most `(k-1)n/2` edges); the
parity bound adds that `(k-1)n` is odd when `k` is even and `n = r(k-1)+1` with `r`
even, so the edge bound cannot be attained with equality.

The lower bounds are three explicit colourings:
* *cyclic* (`cyclicColouring`): on `Z_N`, `N = 2rh+1`, colour `{a,b}` by
  `⌊(d-1)/h⌋`, `d` the cyclic distance;
* *matching* (`matchColouring`): group the perfect matchings of the standard
  1-factorization of `K_{M+1}` (`M` odd) into blocks, one block per colour;
* *affine plane* (`affineColouring`): on the `p × p` grid colour an edge by its
  slope; each colour class is contained in a union of `p` disjoint cliques of size
  `p` (the lines of that slope), too small for any connected graph on `p + 1` vertices.
-/

open SimpleGraph

namespace JSP448

/-! ## Upper bounds -/

/-- Core counting lemma: if `r` graphs cover `K_n` and the Erdős–Sós threshold
times `r` does not exceed the number of edges of `K_n`, some graph contains every
tree on `k+1` vertices. -/
theorem exists_colour_of_edge_count
    (r n k : ℕ) (hr : 1 ≤ r) (hk1 : k + 1 ≤ n)
    (harith : (r : ℚ) * (((k : ℚ) - 1) / 2 * n + 1) ≤ (n : ℚ) * ((n : ℚ) - 1) / 2)
    (G : Fin r → SimpleGraph (Fin n))
    (hcover : (⊤ : SimpleGraph (Fin n)) ≤ ⨆ i, G i) :
    ∃ i, ∀ T : SimpleGraph (Fin (k + 1)), T.IsTree → T.IsContained (G i) := by
  classical
  by_contra hcon
  push_neg at hcon
  -- every colour class falls below the Erdős–Sós threshold
  have hlt : ∀ i, ((G i).edgeFinset.card : ℚ) < ((k : ℚ) - 1) / 2 * n + 1 := by
    intro i
    by_contra h
    push_neg at h
    obtain ⟨T, hT, hTn⟩ := hcon i
    have hc : T.IsContained (G i) := by
      refine Erdos548.erdos_548 n k hk1 (G i) ?_ T hT
      rw [← coe_edgeFinset, Set.ncard_coe_finset]
      exact h
    exact hTn.false hc.some
  -- the colour classes cover all edges of the complete graph
  have hsub : (⊤ : SimpleGraph (Fin n)).edgeFinset ⊆
      Finset.univ.biUnion fun i => (G i).edgeFinset := by
    intro e he
    induction e using Sym2.ind with
    | _ v w =>
      rw [mem_edgeFinset, mem_edgeSet] at he
      have h := hcover he
      rw [iSup_adj] at h
      obtain ⟨i, hi⟩ := h
      rw [Finset.mem_biUnion]
      exact ⟨i, Finset.mem_univ _, by rw [mem_edgeFinset, mem_edgeSet]; exact hi⟩
  have hcard := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  rw [card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin] at hcard
  have hsum : ((n.choose 2 : ℕ) : ℚ) ≤ ∑ i : Fin r, ((G i).edgeFinset.card : ℚ) := by
    exact_mod_cast hcard
  have hsumlt : ∑ i : Fin r, ((G i).edgeFinset.card : ℚ) <
      ∑ _i : Fin r, (((k : ℚ) - 1) / 2 * n + 1) :=
    Finset.sum_lt_sum_of_nonempty ⟨⟨0, hr⟩, Finset.mem_univ _⟩ (fun i _ => hlt i)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsumlt
  rw [Nat.cast_choose_two] at hsum
  linarith

/-- **JSP-000448, covering form.** For `r ≥ 1` colours and `k ≥ 1`, if `n ≥ r*k + 1`
and the `r` graphs `G i` cover the complete graph on `Fin n`, then some colour `i`
contains every tree on `k+1` vertices. -/
theorem multicolor_ramsey_tree_linear
    (r n k : ℕ) (hr : 1 ≤ r) (hk : 1 ≤ k)
    (hn : r * k + 1 ≤ n)
    (G : Fin r → SimpleGraph (Fin n))
    (hcover : (⊤ : SimpleGraph (Fin n)) ≤ ⨆ i, G i) :
    ∃ i, ∀ T : SimpleGraph (Fin (k + 1)), T.IsTree → T.IsContained (G i) := by
  have hk1 : k + 1 ≤ n := by
    have : k ≤ r * k := Nat.le_mul_of_pos_left k hr
    omega
  refine exists_colour_of_edge_count r n k hr hk1 ?_ G hcover
  have hnq : (r : ℚ) * k + 1 ≤ n := by exact_mod_cast hn
  have hrq : (1 : ℚ) ≤ r := by exact_mod_cast hr
  have hkq : (1 : ℚ) ≤ k := by exact_mod_cast hk
  have hn2 : (2 : ℚ) ≤ n := by nlinarith
  have h1 : 0 ≤ (n : ℚ) * ((n : ℚ) - 1 - r * k) := mul_nonneg (by linarith) (by linarith)
  have h2 : 0 ≤ (r : ℚ) * ((n : ℚ) - 2) := mul_nonneg (by linarith) (by linarith)
  nlinarith

/-! ## Sharp upper bounds from the tree-free edge bound

`Erdos548.tree_free_edge_bound` (the statement behind `erdos_548`): a graph on `n`
vertices containing no copy of a tree with `j + 1` edges has at most `j n / 2` edges. -/

/-- A graph on `Fin n` with no copy of a tree `T` on `j + 2` vertices satisfies
`2 |E| ≤ j n`. -/
theorem two_mul_edges_le_of_tree_free (n j : ℕ) (hn : 0 < n) (G : SimpleGraph (Fin n))
    (T : SimpleGraph (Fin (j + 1 + 1))) (hT : T.IsTree) (hfree : ¬ T.IsContained G) :
    2 * G.edgeSet.ncard ≤ j * n := by
  have h := Erdos548.tree_free_edge_bound T hT (by simp) G (by simpa using hn) hfree
  have he : j + 1 + 1 - 2 = j := by omega
  simpa [Fintype.card_fin, he] using h

/-- If `r` graphs cover `K_n`, their edge counts add up to at least `n (n - 1) / 2`. -/
theorem mul_pred_le_sum_edges (r n : ℕ) (G : Fin r → SimpleGraph (Fin n))
    (hcover : (⊤ : SimpleGraph (Fin n)) ≤ ⨆ i, G i) :
    n * (n - 1) ≤ ∑ i, 2 * (G i).edgeSet.ncard := by
  classical
  have hsub : (⊤ : SimpleGraph (Fin n)).edgeFinset ⊆
      Finset.univ.biUnion fun i => (G i).edgeFinset := by
    intro e he
    induction e using Sym2.ind with
    | _ v w =>
      rw [mem_edgeFinset, mem_edgeSet] at he
      have h := hcover he
      rw [iSup_adj] at h
      obtain ⟨i, hi⟩ := h
      rw [Finset.mem_biUnion]
      exact ⟨i, Finset.mem_univ _, by rw [mem_edgeFinset, mem_edgeSet]; exact hi⟩
  have hcard := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  rw [card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin, Nat.choose_two_right] at hcard
  have hconv : ∀ i, (G i).edgeFinset.card = (G i).edgeSet.ncard := fun i => by
    rw [← coe_edgeFinset, Set.ncard_coe_finset]
  simp only [hconv] at hcard
  have heven : n * (n - 1) = 2 * (n * (n - 1) / 2) :=
    (Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self n)).symm
  rw [heven, ← Finset.mul_sum]
  exact Nat.mul_le_mul_left 2 hcard

/-- **Tight off-diagonal form.** Assign to colour `i` trees with `j i + 1` edges. If
`n ≥ ∑ j i + 2` and the graphs `G i` cover `K_n`, then some colour `i` contains every
tree with `j i + 1` edges.  In particular `R(T₁, …, T_r) ≤ ∑ (|Tᵢ| - 2) + 2`. -/
theorem multicolor_ramsey_trees_asym_tight
    (r n : ℕ) (j : Fin r → ℕ) (hn : ∑ i, j i + 2 ≤ n)
    (G : Fin r → SimpleGraph (Fin n))
    (hcover : (⊤ : SimpleGraph (Fin n)) ≤ ⨆ i, G i) :
    ∃ i, ∀ T : SimpleGraph (Fin (j i + 1 + 1)), T.IsTree → T.IsContained (G i) := by
  by_contra hcon
  push_neg at hcon
  have hnpos : 0 < n := by omega
  have hb : ∀ i, 2 * (G i).edgeSet.ncard ≤ j i * n := by
    intro i
    obtain ⟨T, hT, hTn⟩ := hcon i
    exact two_mul_edges_le_of_tree_free n (j i) hnpos (G i) T hT (fun hc => hTn.false hc.some)
  have h1 : n * (n - 1) ≤ (∑ i, j i) * n := by
    rw [Finset.sum_mul]
    exact (mul_pred_le_sum_edges r n G hcover).trans (Finset.sum_le_sum fun i _ => hb i)
  have h2 : n - 1 ≤ ∑ i, j i := by
    rw [mul_comm (∑ i, j i) n] at h1
    exact Nat.le_of_mul_le_mul_left h1 hnpos
  omega

/-- **Tight covering form.** For trees with `k = j + 1` edges it suffices that
`n ≥ r*j + 2 = r*(k-1) + 2`. -/
theorem multicolor_ramsey_tree_tight
    (r n j : ℕ) (hn : r * j + 2 ≤ n)
    (G : Fin r → SimpleGraph (Fin n))
    (hcover : (⊤ : SimpleGraph (Fin n)) ≤ ⨆ i, G i) :
    ∃ i, ∀ T : SimpleGraph (Fin (j + 1 + 1)), T.IsTree → T.IsContained (G i) :=
  multicolor_ramsey_trees_asym_tight r n (fun _ => j) (by simpa using hn) G hcover

/-- **Parity form.** If `r` is even and `j` is odd, then already `n = r*j + 1` suffices:
otherwise every colour class would have exactly `j n / 2` edges, but `j n` is odd. -/
theorem multicolor_ramsey_tree_parity
    (r j : ℕ) (hr1 : 1 ≤ r) (hr : Even r) (hj : Odd j)
    (G : Fin r → SimpleGraph (Fin (r * j + 1)))
    (hcover : (⊤ : SimpleGraph (Fin (r * j + 1))) ≤ ⨆ i, G i) :
    ∃ i, ∀ T : SimpleGraph (Fin (j + 1 + 1)), T.IsTree → T.IsContained (G i) := by
  by_contra hcon
  push_neg at hcon
  have hb : ∀ i, 2 * (G i).edgeSet.ncard ≤ j * (r * j + 1) := by
    intro i
    obtain ⟨T, hT, hTn⟩ := hcon i
    exact two_mul_edges_le_of_tree_free (r * j + 1) j (by omega) (G i) T hT
      (fun hc => hTn.false hc.some)
  have hsum := mul_pred_le_sum_edges r (r * j + 1) G hcover
  have hodd : Odd (j * (r * j + 1)) := hj.mul ((hr.mul_right j).add_one)
  have hlt : ∀ i, 2 * (G i).edgeSet.ncard < j * (r * j + 1) := fun i =>
    lt_of_le_of_ne (hb i) (fun h => (Nat.not_even_iff_odd.mpr hodd) (h ▸ even_two_mul _))
  have h2 : ∑ i, 2 * (G i).edgeSet.ncard < ∑ _i : Fin r, j * (r * j + 1) :=
    Finset.sum_lt_sum_of_nonempty ⟨⟨0, hr1⟩, Finset.mem_univ _⟩ (fun i _ => hlt i)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h2
  have h3 : (r * j + 1) * (r * j + 1 - 1) = r * (j * (r * j + 1)) := by
    rw [Nat.add_sub_cancel]; ring
  omega

/-! ## Edge colourings and the Ramsey number -/

/-- The graph formed by the edges of colour `i` under an edge-colouring `c` of the
complete graph on `Fin n`. -/
def colourClass {n r : ℕ} (c : Sym2 (Fin n) → Fin r) (i : Fin r) : SimpleGraph (Fin n) where
  Adj v w := v ≠ w ∧ c s(v, w) = i
  symm := fun v w ⟨hne, hc⟩ => ⟨hne.symm, by rw [Sym2.eq_swap]; exact hc⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem top_le_iSup_colourClass {n r : ℕ} (c : Sym2 (Fin n) → Fin r) :
    (⊤ : SimpleGraph (Fin n)) ≤ ⨆ i, colourClass c i := by
  intro v w hvw
  rw [iSup_adj]
  exact ⟨c s(v, w), hvw.ne, rfl⟩

/-- **JSP-000448, edge-colouring form.** In every colouring of the edges of the
complete graph on `n ≥ r*k + 1` vertices with `r ≥ 1` colours, some colour class
contains every tree on `k+1` vertices. -/
theorem multicolor_ramsey_tree_linear_colouring
    (r n k : ℕ) (hr : 1 ≤ r) (hk : 1 ≤ k) (hn : r * k + 1 ≤ n)
    (c : Sym2 (Fin n) → Fin r) :
    ∃ i, ∀ T : SimpleGraph (Fin (k + 1)), T.IsTree → T.IsContained (colourClass c i) :=
  multicolor_ramsey_tree_linear r n k hr hk hn (colourClass c) (top_le_iSup_colourClass c)

/-- The `r`-colour Ramsey number of a graph `T`: the least `n` such that every
colouring of the edges of the complete graph on `n` vertices with `r` colours has
a monochromatic copy of `T`.  (By convention `sInf ∅ = 0` if no such `n` exists;
for trees and `r ≥ 1` the set is non-empty by the theorems above.) -/
noncomputable def ramseyNumber {m : ℕ} (r : ℕ) (T : SimpleGraph (Fin m)) : ℕ :=
  sInf {n | ∀ c : Sym2 (Fin n) → Fin r, ∃ i, T.IsContained (colourClass c i)}

/-- Upper bound: `R_r(T) ≤ r * k + 1` for every tree `T` on `k + 1 ≥ 2` vertices. -/
theorem ramseyNumber_tree_le (r k : ℕ) (hr : 1 ≤ r) (hk : 1 ≤ k)
    (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree) :
    ramseyNumber r T ≤ r * k + 1 := by
  apply Nat.sInf_le
  intro c
  obtain ⟨i, hi⟩ := multicolor_ramsey_tree_linear_colouring r (r * k + 1) k hr hk le_rfl c
  exact ⟨i, hi T hT⟩

/-- The set defining `R_r(T)` is non-empty for every tree `T`: the Ramsey number of a
tree exists. -/
theorem ramsey_set_nonempty (r j : ℕ) (T : SimpleGraph (Fin (j + 1 + 1))) (hT : T.IsTree) :
    {n | ∀ c : Sym2 (Fin n) → Fin r, ∃ i, T.IsContained (colourClass c i)}.Nonempty :=
  ⟨r * j + 2, fun c => by
    obtain ⟨i, hi⟩ := multicolor_ramsey_tree_tight r (r * j + 2) j le_rfl
      (colourClass c) (top_le_iSup_colourClass c)
    exact ⟨i, hi T hT⟩⟩

/-- Tight upper bound: `R_r(T) ≤ r * (k - 1) + 2` for every tree `T` with
`k = j + 1 ≥ 1` edges and every `r`. -/
theorem ramseyNumber_tree_le_tight (r j : ℕ)
    (T : SimpleGraph (Fin (j + 1 + 1))) (hT : T.IsTree) :
    ramseyNumber r T ≤ r * j + 2 := by
  apply Nat.sInf_le
  intro c
  obtain ⟨i, hi⟩ := multicolor_ramsey_tree_tight r (r * j + 2) j le_rfl
    (colourClass c) (top_le_iSup_colourClass c)
  exact ⟨i, hi T hT⟩

/-- Parity upper bound: if `r` is even and `j` is odd (an even number `k = j + 1` of
edges), then `R_r(T) ≤ r * (k - 1) + 1` for every tree `T` with `k` edges. -/
theorem ramseyNumber_tree_le_parity (r j : ℕ) (hr1 : 1 ≤ r) (hr : Even r) (hj : Odd j)
    (T : SimpleGraph (Fin (j + 1 + 1))) (hT : T.IsTree) :
    ramseyNumber r T ≤ r * j + 1 := by
  apply Nat.sInf_le
  intro c
  obtain ⟨i, hi⟩ := multicolor_ramsey_tree_parity r j hr1 hr hj
    (colourClass c) (top_le_iSup_colourClass c)
  exact ⟨i, hi T hT⟩

/-- Lower bound: `k + 1 ≤ R_r(T)` for every tree `T` on `k + 1 ≥ 2` vertices. -/
theorem le_ramseyNumber_tree (r k : ℕ) (hr : 1 ≤ r) (hk : 1 ≤ k)
    (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree) :
    k + 1 ≤ ramseyNumber r T := by
  have hne : {n | ∀ c : Sym2 (Fin n) → Fin r, ∃ i, T.IsContained (colourClass c i)}.Nonempty :=
    ⟨r * k + 1, fun c => by
      obtain ⟨i, hi⟩ := multicolor_ramsey_tree_linear_colouring r (r * k + 1) k hr hk le_rfl c
      exact ⟨i, hi T hT⟩⟩
  have hmem := Nat.sInf_mem hne
  obtain ⟨i, ⟨f⟩⟩ := hmem (fun _ => ⟨0, hr⟩)
  simpa using Fintype.card_le_of_injective f f.injective

/-- **JSP-000448, Ramsey-number form.** For every number of colours `r ≥ 1` and every
tree `T` on `k + 1 ≥ 2` vertices, `k + 1 ≤ R_r(T) ≤ r * k + 1`: the multicolour
Ramsey number of a tree is bounded above and below by linear functions of its order. -/
theorem ramseyNumber_tree_linear (r k : ℕ) (hr : 1 ≤ r) (hk : 1 ≤ k)
    (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree) :
    k + 1 ≤ ramseyNumber r T ∧ ramseyNumber r T ≤ r * k + 1 :=
  ⟨le_ramseyNumber_tree r k hr hk T hT, ramseyNumber_tree_le r k hr hk T hT⟩

/-! ## Sharpness: a cyclic colouring without large monochromatic stars -/

/-- Restricting a colouring to an initial segment of the vertices. -/
def restrictColouring {n n' r : ℕ} (h : n ≤ n') (c : Sym2 (Fin n') → Fin r) :
    Sym2 (Fin n) → Fin r :=
  fun e => c (e.map (Fin.castLE h))

theorem isContained_of_restrict {m n n' r : ℕ} (h : n ≤ n') (c : Sym2 (Fin n') → Fin r)
    (i : Fin r) (T : SimpleGraph (Fin m))
    (hT : T.IsContained (colourClass (restrictColouring h c) i)) :
    T.IsContained (colourClass c i) := by
  obtain ⟨f⟩ := hT
  refine ⟨⟨⟨fun v => Fin.castLE h (f v), ?_⟩, ?_⟩⟩
  · intro a b hab
    have := f.toHom.map_adj hab
    obtain ⟨hne, hc⟩ := this
    refine ⟨fun heq => hne (Fin.castLE_injective h heq), ?_⟩
    simpa [restrictColouring] using hc
  · intro a b hab
    exact f.injective (Fin.castLE_injective h hab)

/-- The cyclic colouring of `K_N`: the edge `{a, b}` gets colour `⌊(d - 1) / h⌋`
(reduced mod `r`), where `d = min(|a - b|, N - |a - b|)` is the cyclic distance. -/
def cyclicColouring (r h N : ℕ) (hr : 0 < r) : Sym2 (Fin N) → Fin r :=
  Sym2.lift ⟨fun a b =>
    ⟨((min (Nat.dist a b) (N - Nat.dist a b) - 1) / h) % r, Nat.mod_lt _ hr⟩, by
    intro a b
    simp [Nat.dist_comm]⟩

/-- The candidate neighbours of `v` in colour `i` under the cyclic colouring. -/
def cyclicNbrs (h N i v : ℕ) : Finset ℕ :=
  (Finset.Icc (i * h + 1) (i * h + h)).image (fun m => (v + m) % N) ∪
  (Finset.Icc (i * h + 1) (i * h + h)).image (fun m => (v + N - m) % N)

theorem card_cyclicNbrs_le (h N i v : ℕ) : (cyclicNbrs h N i v).card ≤ 2 * h := by
  unfold cyclicNbrs
  refine (Finset.card_union_le _ _).trans ?_
  have h1 := Finset.card_image_le (s := Finset.Icc (i * h + 1) (i * h + h))
    (f := fun m => (v + m) % N)
  have h2 := Finset.card_image_le (s := Finset.Icc (i * h + 1) (i * h + h))
    (f := fun m => (v + N - m) % N)
  simp only [Nat.card_Icc] at h1 h2
  omega

theorem mem_cyclicNbrs (r h N : ℕ) (hN : N = 2 * r * h + 1) (hr : 0 < r) (hh : 0 < h)
    (i : Fin r) (v w : Fin N) (hvw : v ≠ w)
    (hc : cyclicColouring r h N hr s(v, w) = i) :
    (w : ℕ) ∈ cyclicNbrs h N i v := by
  have hv := v.isLt
  have hw := w.isLt
  have hne : (v : ℕ) ≠ w := fun h' => hvw (Fin.ext h')
  set D := Nat.dist (v : ℕ) w with hD
  set m := min D (N - D) with hm
  have hval : ((m - 1) / h) % r = i := by
    have := congrArg Fin.val hc
    simpa [cyclicColouring] using this
  have hDdef : D = (v : ℕ) - w + (w - v) := rfl
  have hD1 : 1 ≤ D := by omega
  have hDN : D < N := by omega
  have hm1 : 1 ≤ m := by omega
  have hmD : m = D ∨ m = N - D := by omega
  have hrh : 2 * (r * h) + 1 = N := by rw [hN]; ring
  have hmle : m ≤ r * h := by omega
  have hq : (m - 1) / h < r := by
    rw [Nat.div_lt_iff_lt_mul hh]
    omega
  rw [Nat.mod_eq_of_lt hq] at hval
  have hlo : (i : ℕ) * h ≤ m - 1 := by
    rw [← hval]; exact Nat.div_mul_le_self _ _
  have hhi : m - 1 < (i : ℕ) * h + h := by
    rw [← hval]
    have := Nat.lt_div_mul_add hh (a := m - 1)
    linarith
  have hmI : m ∈ Finset.Icc ((i : ℕ) * h + 1) ((i : ℕ) * h + h) := by
    rw [Finset.mem_Icc]; omega
  unfold cyclicNbrs
  rw [Finset.mem_union, Finset.mem_image, Finset.mem_image]
  have key : (w : ℕ) = (v : ℕ) + m ∨ (w : ℕ) + N = (v : ℕ) + m ∨
      (w : ℕ) = (v : ℕ) + N - m ∨ (w : ℕ) + N = (v : ℕ) + N - m := by omega
  rcases key with k1 | k1 | k1 | k1
  · left; exact ⟨m, hmI, by rw [← k1]; exact Nat.mod_eq_of_lt hw⟩
  · left; exact ⟨m, hmI, by rw [← k1, Nat.add_mod_right]; exact Nat.mod_eq_of_lt hw⟩
  · right; exact ⟨m, hmI, by rw [← k1]; exact Nat.mod_eq_of_lt hw⟩
  · right; exact ⟨m, hmI, by rw [← k1, Nat.add_mod_right]; exact Nat.mod_eq_of_lt hw⟩

/-- Under the cyclic colouring of `K_{2rh+1}`, no colour class contains a graph on
`2h+2` vertices having a vertex adjacent to all the others. -/
theorem not_isContained_cyclic (r h : ℕ) (hr : 0 < r) (hh : 0 < h)
    (T : SimpleGraph (Fin (2 * h + 2))) (v₀ : Fin (2 * h + 2))
    (hv₀ : ∀ w, w ≠ v₀ → T.Adj v₀ w) (i : Fin r) :
    ¬ T.IsContained (colourClass (cyclicColouring r h (2 * r * h + 1) hr) i) := by
  classical
  rintro ⟨f⟩
  have hmaps : ∀ w ∈ (Finset.univ.erase v₀ : Finset (Fin (2 * h + 2))),
      ((f w : Fin (2 * r * h + 1)) : ℕ) ∈ cyclicNbrs h (2 * r * h + 1) i (f v₀) := by
    intro w hw
    have hadj := f.toHom.map_adj (hv₀ w (Finset.ne_of_mem_erase hw))
    exact mem_cyclicNbrs r h (2 * r * h + 1) rfl hr hh i (f v₀) (f w) hadj.1 hadj.2
  have hinj : Set.InjOn (fun w => ((f w : Fin (2 * r * h + 1)) : ℕ))
      (Finset.univ.erase v₀ : Finset (Fin (2 * h + 2))) := by
    intro a _ b _ hab
    exact f.injective (Fin.ext hab)
  have hcard := Finset.card_le_card_of_injOn (fun w => ((f w : Fin (2 * r * h + 1)) : ℕ))
    (fun w hw => Finset.mem_coe.mpr (hmaps w (Finset.mem_coe.mp hw))) hinj
  have h2 := card_cyclicNbrs_le h (2 * r * h + 1) i (f v₀)
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at hcard
  omega

/-- **Sharpness (cyclic colouring).** If `T` is a tree on `2h + 2` vertices (`h ≥ 1`)
with a vertex adjacent to all others — the star with `k = 2h + 1` edges — then for
every `r ≥ 1` its `r`-colour Ramsey number is exactly `2rh + 2 = r(k - 1) + 2`. -/
theorem ramseyNumber_star_eq (r h : ℕ) (hr : 1 ≤ r) (hh : 1 ≤ h)
    (T : SimpleGraph (Fin (2 * h + 2))) (hT : T.IsTree) (v₀ : Fin (2 * h + 2))
    (hv₀ : ∀ w, w ≠ v₀ → T.Adj v₀ w) :
    ramseyNumber r T = 2 * r * h + 2 := by
  have hup : ramseyNumber r T ≤ r * (2 * h) + 2 := ramseyNumber_tree_le_tight r (2 * h) T hT
  have hmem := Nat.sInf_mem (ramsey_set_nonempty r (2 * h) T hT)
  have hlow : 2 * r * h + 2 ≤ ramseyNumber r T := by
    by_contra hlt
    push_neg at hlt
    have hle : ramseyNumber r T ≤ 2 * r * h + 1 := by omega
    obtain ⟨i, hi⟩ := hmem (restrictColouring hle (cyclicColouring r h (2 * r * h + 1) hr))
    exact not_isContained_cyclic r h hr hh T v₀ hv₀ i (isContained_of_restrict hle _ i T hi)
  have : r * (2 * h) = 2 * r * h := by ring
  omega

/-! ## The star is a tree (non-vacuity) -/

/-- The star on `m + 1` vertices with centre `0`. -/
def starGraph (m : ℕ) : SimpleGraph (Fin (m + 1)) where
  Adj a b := (a = 0 ∧ b ≠ 0) ∨ (b = 0 ∧ a ≠ 0)
  symm := fun _ _ h => h.symm
  loopless := ⟨fun a h => by rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> exact h2 h1⟩

theorem starGraph_adj_centre (m : ℕ) (w : Fin (m + 1)) (hw : w ≠ 0) : (starGraph m).Adj 0 w :=
  Or.inl ⟨rfl, hw⟩

theorem starGraph_isTree (m : ℕ) : (starGraph m).IsTree := by
  classical
  rw [isTree_iff_connected_and_card]
  have hreach : ∀ a : Fin (m + 1), (starGraph m).Reachable 0 a := by
    intro a
    by_cases ha : a = 0
    · subst ha; exact Reachable.refl _
    · exact (starGraph_adj_centre m a ha).reachable
  refine ⟨⟨fun a b => (hreach a).symm.trans (hreach b)⟩, ?_⟩
  have hE : (starGraph m).edgeSet = (fun b : Fin (m + 1) => s(0, b)) '' {b | b ≠ 0} := by
    ext e
    induction e using Sym2.ind with
    | _ a b =>
      simp only [mem_edgeSet, Set.mem_image, Set.mem_setOf_eq, Sym2.eq_iff]
      constructor
      · rintro (⟨rfl, hb⟩ | ⟨rfl, ha⟩)
        · exact ⟨b, hb, Or.inl ⟨rfl, rfl⟩⟩
        · exact ⟨a, ha, Or.inr ⟨rfl, rfl⟩⟩
      · rintro ⟨c, hc, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩
        · exact Or.inl ⟨rfl, hc⟩
        · exact Or.inr ⟨rfl, hc⟩
  have hinj : Set.InjOn (fun b : Fin (m + 1) => s(0, b)) {b | b ≠ 0} := by
    intro a ha b hb hab
    rcases Sym2.eq_iff.mp hab with ⟨_, h⟩ | ⟨h1, h2⟩
    · exact h
    · exact absurd h2 ha
  rw [hE, Nat.card_coe_set_eq, hinj.ncard_image, Nat.card_eq_fintype_card,
    Fintype.card_fin]
  have : ({b : Fin (m + 1) | b ≠ 0} : Set _) = ({0} : Set (Fin (m + 1)))ᶜ := by ext; simp
  rw [this, Set.ncard_compl, Set.ncard_singleton, Nat.card_eq_fintype_card, Fintype.card_fin]
  omega

/-- Non-vacuity of `ramseyNumber_star_eq`: for every `h` there is a tree on `2h + 2`
vertices with a vertex adjacent to all the others. -/
theorem exists_star_tree (h : ℕ) :
    ∃ (T : SimpleGraph (Fin (2 * h + 2))) (v₀ : Fin (2 * h + 2)),
      T.IsTree ∧ ∀ w, w ≠ v₀ → T.Adj v₀ w :=
  ⟨starGraph (2 * h + 1), 0, starGraph_isTree _, starGraph_adj_centre _⟩

/-- The star with `2h + 1` edges has `r`-colour Ramsey number exactly `2rh + 2`. -/
theorem ramseyNumber_star (r h : ℕ) (hr : 1 ≤ r) (hh : 1 ≤ h) :
    ramseyNumber r (starGraph (2 * h + 1)) = 2 * r * h + 2 :=
  ramseyNumber_star_eq r h hr hh _ (starGraph_isTree _) 0 (starGraph_adj_centre _)

/-! ## Stars: the matching colouring and the complete determination -/

/-- If in colour `i` every vertex `v` has its neighbours injected (by `g v`) into a
set of at most `d` elements, then colour `i` contains no graph on `d + 2` vertices
having a vertex adjacent to all others. -/
theorem not_isContained_of_few_nbrs {N r d : ℕ} (c : Sym2 (Fin N) → Fin r) (i : Fin r)
    (g : Fin N → Fin N → ℕ) (S : Finset ℕ) (hS : S.card ≤ d)
    (hmem : ∀ v w, (colourClass c i).Adj v w → g v w ∈ S)
    (hinj : ∀ v w w', (colourClass c i).Adj v w → (colourClass c i).Adj v w' →
      g v w = g v w' → w = w')
    (T : SimpleGraph (Fin (d + 2))) (v₀ : Fin (d + 2)) (hv₀ : ∀ w, w ≠ v₀ → T.Adj v₀ w) :
    ¬ T.IsContained (colourClass c i) := by
  classical
  rintro ⟨f⟩
  have hadj : ∀ w ∈ (Finset.univ.erase v₀ : Finset (Fin (d + 2))),
      (colourClass c i).Adj (f v₀) (f w) := fun w hw =>
    f.toHom.map_adj (hv₀ w (Finset.ne_of_mem_erase hw))
  have hcard := Finset.card_le_card_of_injOn (s := Finset.univ.erase v₀) (t := S)
    (fun w => g (f v₀) (f w))
    (fun w hw => Finset.mem_coe.mpr (hmem _ _ (hadj w (Finset.mem_coe.mp hw))))
    (fun a ha b hb hab => f.injective
      (hinj _ _ _ (hadj a (Finset.mem_coe.mp ha)) (hadj b (Finset.mem_coe.mp hb)) hab))
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at hcard
  omega

/-- Index of the perfect matching of `K_{M+1}` (`M` odd) containing the edge `{a, b}`:
vertices `0, …, M-1` are the residues mod `M`, the vertex `M` is "the point at
infinity"; `{a, b}` lies in matching `a + b`, and `{∞, a}` in matching `2a`. -/
def matchIdx (M a b : ℕ) : ℕ :=
  if a = M then (2 * b) % M else if b = M then (2 * a) % M else (a + b) % M

theorem matchIdx_comm (M a b : ℕ) : matchIdx M a b = matchIdx M b a := by
  unfold matchIdx
  by_cases ha : a = M <;> by_cases hb : b = M <;> simp [ha, hb, Nat.add_comm]

theorem matchIdx_lt (M a b : ℕ) (hM : 0 < M) : matchIdx M a b < M := by
  unfold matchIdx
  split_ifs <;> exact Nat.mod_lt _ hM

theorem matchIdx_inj (M v w w' : ℕ) (hM : Odd M) (hv : v ≤ M) (hw : w ≤ M) (hw' : w' ≤ M)
    (hvw : w ≠ v) (hvw' : w' ≠ v) (h : matchIdx M v w = matchIdx M v w') : w = w' := by
  have hcop : Nat.gcd M 2 = 1 := by
    rw [Nat.gcd_comm]; exact (Nat.coprime_two_left.mpr hM)
  unfold matchIdx at h
  by_cases hvM : v = M
  · subst hvM
    simp only [if_true] at h
    have hwl : w < v := lt_of_le_of_ne hw hvw
    have hwl' : w' < v := lt_of_le_of_ne hw' hvw'
    have h2 : w ≡ w' [MOD v] := Nat.ModEq.cancel_left_of_coprime hcop h
    exact Nat.ModEq.eq_of_lt_of_lt h2 hwl hwl'
  · have hvl : v < M := lt_of_le_of_ne hv hvM
    simp only [hvM, if_false] at h
    by_cases hwM : w = M <;> by_cases hwM' : w' = M
    · rw [hwM, hwM']
    · exfalso
      simp only [hwM, hwM', if_true, if_false] at h
      have hwl' : w' < M := lt_of_le_of_ne hw' hwM'
      have h2 : v + v ≡ v + w' [MOD M] := by rw [← two_mul]; exact h
      have h3 : v ≡ w' [MOD M] := Nat.ModEq.add_left_cancel' v h2
      exact hvw' (Nat.ModEq.eq_of_lt_of_lt h3 hvl hwl').symm
    · exfalso
      simp only [hwM, hwM', if_true, if_false] at h
      have hwl : w < M := lt_of_le_of_ne hw hwM
      have h2 : v + w ≡ v + v [MOD M] := by rw [← two_mul]; exact h
      have h3 : w ≡ v [MOD M] := Nat.ModEq.add_left_cancel' v h2
      exact hvw (Nat.ModEq.eq_of_lt_of_lt h3 hwl hvl)
    · simp only [hwM, hwM', if_false] at h
      have hwl : w < M := lt_of_le_of_ne hw hwM
      have hwl' : w' < M := lt_of_le_of_ne hw' hwM'
      have h3 : w ≡ w' [MOD M] := Nat.ModEq.add_left_cancel' v h
      exact Nat.ModEq.eq_of_lt_of_lt h3 hwl hwl'

/-- The matching colouring of `K_{M+1}`: the `M` perfect matchings are grouped into
consecutive blocks of `q`, one block per colour. -/
def matchColouring (r q M : ℕ) (hr : 0 < r) : Sym2 (Fin (M + 1)) → Fin r :=
  Sym2.lift ⟨fun a b => ⟨(matchIdx M a b / q) % r, Nat.mod_lt _ hr⟩, by
    intro a b
    simp [matchIdx_comm M a b]⟩

/-- Under the matching colouring of `K_{M+1}` (`M` odd, `M ≤ r q`), no colour class
contains a graph on `q + 2` vertices having a vertex adjacent to all others. -/
theorem not_isContained_match (r q M : ℕ) (hr : 0 < r) (hq : 0 < q) (hM : Odd M)
    (hMle : M ≤ r * q) (T : SimpleGraph (Fin (q + 2))) (v₀ : Fin (q + 2))
    (hv₀ : ∀ w, w ≠ v₀ → T.Adj v₀ w) (i : Fin r) :
    ¬ T.IsContained (colourClass (matchColouring r q M hr) i) := by
  have hMpos : 0 < M := hM.pos
  refine not_isContained_of_few_nbrs (matchColouring r q M hr) i
    (fun v w => matchIdx M v w) (Finset.Ico ((i : ℕ) * q) ((i : ℕ) * q + q))
    (by simp) ?_ ?_ T v₀ hv₀
  · rintro v w ⟨_, hc⟩
    have hval : (matchIdx M v w / q) % r = i := by
      have := congrArg Fin.val hc
      simpa [matchColouring] using this
    have hlt := matchIdx_lt M v w hMpos
    have hdiv : matchIdx M v w / q < r := by
      rw [Nat.div_lt_iff_lt_mul hq]; omega
    rw [Nat.mod_eq_of_lt hdiv] at hval
    rw [Finset.mem_Ico, ← hval]
    refine ⟨Nat.div_mul_le_self _ _, ?_⟩
    have := Nat.lt_div_mul_add hq (a := matchIdx M v w)
    linarith
  · rintro v w w' ⟨h1, _⟩ ⟨h2, _⟩ h
    have hv := Nat.lt_succ_iff.mp v.isLt
    have hw := Nat.lt_succ_iff.mp w.isLt
    have hw' := Nat.lt_succ_iff.mp w'.isLt
    exact Fin.ext (matchIdx_inj M v w w' hM hv hw hw'
      (fun e => h1 (Fin.ext e.symm)) (fun e => h2 (Fin.ext e.symm)) h)

/-- Lower bound from the matching colouring: for `M` odd with `M ≤ r q`, a graph on
`q + 2` vertices with a vertex adjacent to all others has `R_r(T) ≥ M + 2`
(provided the Ramsey number exists). -/
theorem le_ramseyNumber_of_match (r q M : ℕ) (hr : 1 ≤ r) (hq : 1 ≤ q) (hM : Odd M)
    (hMle : M ≤ r * q) (T : SimpleGraph (Fin (q + 2)))
    (hne : {n | ∀ c : Sym2 (Fin n) → Fin r, ∃ i, T.IsContained (colourClass c i)}.Nonempty)
    (v₀ : Fin (q + 2)) (hv₀ : ∀ w, w ≠ v₀ → T.Adj v₀ w) :
    M + 2 ≤ ramseyNumber r T := by
  have hmem := Nat.sInf_mem hne
  by_contra hlt
  push_neg at hlt
  have hle : ramseyNumber r T ≤ M + 1 := by omega
  obtain ⟨i, hi⟩ := hmem (restrictColouring hle (matchColouring r q M hr))
  exact not_isContained_match r q M hr hq hM hMle T v₀ hv₀ i
    (isContained_of_restrict hle _ i T hi)

/-- **Stars (Burr–Roberts, diagonal case).** For `r ≥ 1` colours and the star with
`k = j + 1 ≥ 1` edges, `R_r = r (k - 1) + 1` if `r` and `k` are both even, and
`R_r = r (k - 1) + 2` otherwise. -/
theorem ramseyNumber_star_all (r j : ℕ) (hr : 1 ≤ r) :
    ramseyNumber r (starGraph (j + 1)) =
      if Even r ∧ Odd j then r * j + 1 else r * j + 2 := by
  have hv₀ : ∀ w : Fin (j + 2), w ≠ 0 → (starGraph (j + 1)).Adj 0 w :=
    starGraph_adj_centre (j + 1)
  have hT := starGraph_isTree (j + 1)
  have hup : ramseyNumber r (starGraph (j + 1)) ≤ r * j + 2 :=
    ramseyNumber_tree_le_tight r j _ hT
  have hne := ramsey_set_nonempty r j _ hT
  rcases Nat.even_or_odd j with hje | hjo
  · have hcond : ¬ (Even r ∧ Odd j) := fun h => (Nat.not_odd_iff_even.mpr hje) h.2
    rw [if_neg hcond]
    obtain ⟨h, rfl⟩ : ∃ h, j = 2 * h := ⟨j / 2, by obtain ⟨t, rfl⟩ := hje; omega⟩
    rcases Nat.eq_zero_or_pos h with rfl | hh
    · -- a single edge
      have hlow := le_ramseyNumber_tree r 1 hr le_rfl (starGraph (2 * 0 + 1)) hT
      omega
    · -- `j` even: the cyclic colouring
      have := ramseyNumber_star r h hr hh
      rw [this]; ring
  · have hj1 : 1 ≤ j := hjo.pos
    have hrj : 1 ≤ r * j := Nat.mul_pos hr hj1
    rcases Nat.even_or_odd r with hre | hro
    · -- `r` even, `j` odd: parity upper bound, matching colouring of `K_{rj}`
      rw [if_pos ⟨hre, hjo⟩]
      have hup' := ramseyNumber_tree_le_parity r j hr hre hjo _ hT
      have hM : Odd (r * j - 1) := Nat.Even.sub_odd hrj (hre.mul_right j) odd_one
      have hlow := le_ramseyNumber_of_match r j (r * j - 1) hr hj1 hM (by omega)
        (starGraph (j + 1)) hne 0 hv₀
      omega
    · -- `r` odd, `j` odd: matching colouring of `K_{rj+1}`
      have hcond : ¬ (Even r ∧ Odd j) := fun h => (Nat.not_even_iff_odd.mpr hro) h.1
      rw [if_neg hcond]
      have hlow := le_ramseyNumber_of_match r j (r * j) hr hj1 (hro.mul hjo) le_rfl
        (starGraph (j + 1)) hne 0 hv₀
      omega

/-! ## Sharpness for every tree: the affine-plane colouring -/

/-- If, in colour `i`, adjacent vertices always share a label and every label is
carried by at most `k` vertices, then colour `i` contains no connected graph on
`k + 1` vertices. -/
theorem not_isContained_of_labels {α : Type*} [DecidableEq α] {N r k : ℕ}
    (c : Sym2 (Fin N) → Fin r) (i : Fin r) (L : Fin N → α)
    (hadj : ∀ a b, (colourClass c i).Adj a b → L a = L b)
    (hfib : ∀ t, (Finset.univ.filter fun a => L a = t).card ≤ k)
    (T : SimpleGraph (Fin (k + 1))) (hT : T.Connected) :
    ¬ T.IsContained (colourClass c i) := by
  rintro ⟨f⟩
  have hreach : ∀ a b, (colourClass c i).Reachable a b → L a = L b := by
    rintro a b ⟨w⟩
    induction w with
    | nil => rfl
    | cons h _ ih => exact (hadj _ _ h).trans ih
  have hall : ∀ v, L (f v) = L (f 0) := fun v =>
    hreach _ _ ((hT.preconnected v 0).map f.toHom)
  have hcard : (Finset.univ : Finset (Fin (k + 1))).card ≤
      (Finset.univ.filter fun a => L a = L (f 0)).card :=
    Finset.card_le_card_of_injOn (fun v => f v)
      (fun v _ => by simp [hall v]) (fun a _ b _ hab => f.injective hab)
  have := hfib (L (f 0))
  rw [Finset.card_univ, Fintype.card_fin] at hcard
  omega

/-- First coordinate of a point of the `p × p` grid. -/
def gridX (p : ℕ) (a : Fin (p * p)) : ZMod p := ((a : ℕ) / p : ℕ)
/-- Second coordinate of a point of the `p × p` grid. -/
def gridY (p : ℕ) (a : Fin (p * p)) : ZMod p := ((a : ℕ) % p : ℕ)

theorem grid_ext (p : ℕ) [Fact p.Prime] (a b : Fin (p * p))
    (hx : gridX p a = gridX p b) (hy : gridY p a = gridY p b) : a = b := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have ha : (a : ℕ) / p < p := Nat.div_lt_of_lt_mul a.isLt
  have hb : (b : ℕ) / p < p := Nat.div_lt_of_lt_mul b.isLt
  have hx' : (a : ℕ) / p = (b : ℕ) / p := by
    have := congrArg ZMod.val hx
    simpa [gridX, ZMod.val_natCast, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using this
  have hy' : (a : ℕ) % p = (b : ℕ) % p := by
    have := congrArg ZMod.val hy
    simpa [gridY, ZMod.val_natCast] using this
  apply Fin.ext
  rw [← Nat.div_add_mod (a : ℕ) p, ← Nat.div_add_mod (b : ℕ) p, hx', hy']

/-- The affine-plane colouring of `K_{p²}` with `p + 1` colours: an edge is coloured
by its slope (`p` stands for "vertical"). -/
noncomputable def affineColouring (p : ℕ) [Fact p.Prime] : Sym2 (Fin (p * p)) → Fin (p + 1) :=
  Sym2.lift ⟨fun a b =>
    if gridX p a = gridX p b then Fin.last p
    else ⟨((gridY p a - gridY p b) * (gridX p a - gridX p b)⁻¹).val,
      Nat.lt_succ_of_lt (ZMod.val_lt _)⟩, by
    intro a b
    by_cases h : gridX p a = gridX p b
    · simp [h]
    · have h' : ¬ gridX p b = gridX p a := fun e => h e.symm
      simp only [h, h', if_false]
      congr 2
      rw [← neg_sub (gridY p b), ← neg_sub (gridX p b), inv_neg, neg_mul_neg]⟩

/-- The label of a point in colour `i`: the intercept of the line of slope `i`
through it (or its first coordinate, for the vertical colour). -/
noncomputable def affineLabel (p : ℕ) (i : Fin (p + 1)) (a : Fin (p * p)) : ZMod p :=
  if (i : ℕ) < p then gridY p a - ((i : ℕ) : ZMod p) * gridX p a else gridX p a

theorem affineLabel_adj (p : ℕ) [Fact p.Prime] (i : Fin (p + 1)) (a b : Fin (p * p))
    (h : (colourClass (affineColouring p) i).Adj a b) :
    affineLabel p i a = affineLabel p i b := by
  obtain ⟨_, hc⟩ := h
  unfold affineLabel
  by_cases hx : gridX p a = gridX p b
  · have : i = Fin.last p := by rw [← hc]; simp [affineColouring, hx]
    subst this
    simp [hx]
  · have hval : ((gridY p a - gridY p b) * (gridX p a - gridX p b)⁻¹).val = (i : ℕ) := by
      have := congrArg Fin.val hc
      simpa [affineColouring, hx] using this
    have hlt : (i : ℕ) < p := by rw [← hval]; exact ZMod.val_lt _
    have hs : (((i : ℕ) : ZMod p)) = (gridY p a - gridY p b) * (gridX p a - gridX p b)⁻¹ := by
      rw [← hval, ZMod.natCast_zmod_val]
    have hne : gridX p a - gridX p b ≠ 0 := sub_ne_zero.mpr hx
    simp only [hlt, if_true]
    rw [hs]
    field_simp
    ring

theorem affineLabel_fibre (p : ℕ) [Fact p.Prime] (i : Fin (p + 1)) (t : ZMod p) :
    (Finset.univ.filter fun a => affineLabel p i a = t).card ≤ p := by
  classical
  have hcard : (Finset.univ : Finset (ZMod p)).card = p := by
    rw [Finset.card_univ, ZMod.card]
  suffices h : (Finset.univ.filter fun a => affineLabel p i a = t).card ≤
      (Finset.univ : Finset (ZMod p)).card from h.trans hcard.le
  by_cases hi : (i : ℕ) < p
  · refine Finset.card_le_card_of_injOn (fun a => gridX p a) (fun _ _ => by simp) ?_
    intro a ha b hb hab
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq, affineLabel, hi,
      if_true] at ha hb
    have hab' : gridX p a = gridX p b := hab
    refine grid_ext p a b hab' ?_
    have : gridY p a - ((i : ℕ) : ZMod p) * gridX p a = gridY p b - ((i : ℕ) : ZMod p) * gridX p b :=
      ha.trans hb.symm
    rw [hab'] at this
    exact sub_left_injective this
  · refine Finset.card_le_card_of_injOn (fun a => gridY p a) (fun _ _ => by simp) ?_
    intro a ha b hb hab
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq, affineLabel, hi,
      if_false] at ha hb
    exact grid_ext p a b (ha.trans hb.symm) hab

/-- **Sharpness for all trees (Erdős–Graham's construction, affine planes of prime
order).** Let `p = j + 1` be prime. Then *every* tree with `p` edges has
`(p + 1)`-colour Ramsey number exactly `p² + 1` (`= r (k - 1) + 2` with `r = p + 1`,
`k = p`). -/
theorem ramseyNumber_tree_eq_of_prime (j : ℕ) (hp : (j + 1).Prime)
    (T : SimpleGraph (Fin (j + 1 + 1))) (hT : T.IsTree) :
    ramseyNumber (j + 1 + 1) T = (j + 1) * (j + 1) + 1 := by
  haveI : Fact (j + 1).Prime := ⟨hp⟩
  have hup : ramseyNumber (j + 1 + 1) T ≤ (j + 1 + 1) * j + 2 :=
    ramseyNumber_tree_le_tight (j + 1 + 1) j T hT
  have hmem := Nat.sInf_mem (ramsey_set_nonempty (j + 1 + 1) j T hT)
  have hlow : (j + 1) * (j + 1) + 1 ≤ ramseyNumber (j + 1 + 1) T := by
    by_contra hlt
    push_neg at hlt
    have hle : ramseyNumber (j + 1 + 1) T ≤ (j + 1) * (j + 1) := by omega
    obtain ⟨i, hi⟩ := hmem (restrictColouring hle (affineColouring (j + 1)))
    exact not_isContained_of_labels (affineColouring (j + 1)) i (affineLabel (j + 1) i)
      (affineLabel_adj (j + 1) i) (affineLabel_fibre (j + 1) i) T hT.isConnected
      (isContained_of_restrict hle _ i T hi)
  have : (j + 1 + 1) * j + 2 = (j + 1) * (j + 1) + 1 := by ring
  omega

/-! ## The error term depends on the number of colours -/

/-- For every constant `C`, with `r = C + 2` colours every tree `T` has
`R_r(T) + C < r · |T|`.  So no bound `r · |T| ≤ R_r(T) + C` holds with `C`
independent of the number of colours.  (This is a one-sided statement: it does not
say that `R_r(T) = r·|T| + O_r(1)` holds for fixed `r`; that fails for paths.) -/
theorem ramseyNumber_tree_error_unbounded (C : ℕ) :
    ∃ r, 1 ≤ r ∧ ∀ j, ∀ T : SimpleGraph (Fin (j + 1 + 1)), T.IsTree →
      ramseyNumber r T + C < r * (j + 1 + 1) := by
  refine ⟨C + 2, by omega, fun j T hT => ?_⟩
  have h := ramseyNumber_tree_le_tight (C + 2) j T hT
  have : (C + 2) * (j + 1 + 1) = (C + 2) * j + 2 * C + 4 := by ring
  omega

end JSP448
