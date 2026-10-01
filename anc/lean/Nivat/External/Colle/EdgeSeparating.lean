/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.LatticeEdges

/-!
# `exists_edge_separating`: a point outside a lattice polygon is cut off by an edge

If `T` is a finite lattice-convex set of positive area and `g ∉ T`, then some **edge
normal** of `T` separates `g` strictly from all of `T`.

This is the lemma the uniform-window argument for `ChainData.maximalHat` needs.  It turned
out to be pure wiring, not new convex geometry: `LatticeEdges.lean`'s H-representation
section already contains the contrapositive,

  `mem_of_dot_le_suppVal` (`LatticeEdges.lean:1393`)
    `(h : ∀ n ∈ E T, dot n z ≤ suppVal T n) : z ∈ T`

so the whole content is `le_suppVal` plus a double negation.

## `PosArea` is not optional

Without it the statement is **false**, in two ways:

* `T = {(0,0)}`, `g = (1,0)`: every `face T n = {(0,0)}` is a singleton, hence not
  `Set.Nontrivial`, hence `E T = ∅` and `∃ n ∈ E T, _` is unsatisfiable.
* `T = {(0,0),(1,0)}`, `g = (0,1)`: `E T = {±(1,0)}`, and neither of those normals
  separates a point displaced transversally to the segment.

`PosArea T` (`LatticeEdges.lean:235`) rules both out, and it already implies `T.Nonempty`,
so no separate nonemptiness hypothesis is needed.

## On `suppVal` and the `ℤ`-valued `sSup` junk value

`suppVal T n := sSup (dot n '' T)` lands in `ℤ` (`LatticeEdges.lean:743`), where `sSup`
of an empty or upward-unbounded set is the junk value `0`.  That hazard does **not** reach
this file: every use here goes through `le_suppVal` / `mem_of_dot_le_suppVal`, both of
which take `T.Finite` and `T.Nonempty`, and on a finite non-empty `T` the value is pinned
to a genuine maximum by `suppVal_eq` (`LatticeEdges.lean:745`), which reads it off an
element of `face T n`.  No statement in this file is true only by junk value.

No `sorry`, no local `axiom`.
-/

namespace Nivat.EdgeSeparating

open Nivat.LE2

/-- Positive area gives a point, hence non-emptiness. -/
theorem PosArea.nonempty {T : Set (ℤ × ℤ)} (h : PosArea T) : T.Nonempty := by
  obtain ⟨a, ha, -⟩ := h
  exact ⟨a, ha⟩

/-- **A point outside a lattice polygon is cut off by one of its edges.**

`T` finite, lattice-convex, of positive area, and `g ∉ T`; then some `n ∈ E T` satisfies
`dot n z < dot n g` for every `z ∈ T`.

`PosArea` is required: see the module docstring for the two degenerate counterexamples. -/
theorem exists_edge_separating {T : Set (ℤ × ℤ)} (hfin : T.Finite)
    (hlc : Nivat.IsLatticeConvexRegion T) (harea : PosArea T)
    {g : ℤ × ℤ} (hg : g ∉ T) :
    ∃ n ∈ E T, ∀ z ∈ T, dot n z < dot n g := by
  have hne : T.Nonempty := PosArea.nonempty harea
  by_contra hcon
  refine hg (mem_of_dot_le_suppVal hfin hne harea hlc ?_)
  intro n hn
  by_contra hlt
  exact hcon ⟨n, hn, fun z hz => lt_of_le_of_lt (le_suppVal hfin hne hz) (not_le.mp hlt)⟩

/-- **`PosArea` cannot be dropped.**  A singleton is finite, lattice-convex and non-empty,
but has no edges at all, so the conclusion is unsatisfiable for any `g` outside it.

This is proved rather than asserted, so that a later reader cannot "simplify" the
hypothesis away — the exact failure mode CLAUDE.md records for this project. -/
theorem E_singleton_eq_empty (a : ℤ × ℤ) : E ({a} : Set (ℤ × ℤ)) = ∅ := by
  ext n
  simp only [Set.mem_empty_iff_false, iff_false, mem_E_iff, not_and]
  rintro - ⟨x, hx, y, hy, hxy⟩
  have hx' : x = a := face_subset ({a} : Set (ℤ × ℤ)) n hx
  have hy' : y = a := face_subset ({a} : Set (ℤ × ℤ)) n hy
  exact hxy (hx'.trans hy'.symm)

theorem latticeConvex_singleton_zero :
    Nivat.IsLatticeConvexRegion ({((0 : ℤ), (0 : ℤ))} : Set (ℤ × ℤ)) := by
  refine ⟨{p : ℝ × ℝ | p.1 = 0 ∧ p.2 = 0}, ?_, ?_, ?_⟩
  · rintro x ⟨hx1, hx2⟩ y ⟨hy1, hy2⟩ a b ha hb hab
    refine ⟨?_, ?_⟩ <;>
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    · rw [hx1, hy1]; ring
    · rw [hx2, hy2]; ring
  · exact (isClosed_eq continuous_fst continuous_const).inter
      (isClosed_eq continuous_snd continuous_const)
  · ext z
    simp only [Set.mem_singleton_iff, Nivat.toReal, Set.mem_preimage, Set.mem_ofPred_eq,
      Prod.ext_iff]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by rw [h1]; norm_num, by rw [h2]; norm_num⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩

/-- Dropping `PosArea` makes `exists_edge_separating` false. -/
theorem exists_edge_separating_false_without_posArea :
    ¬ ∀ (T : Set (ℤ × ℤ)), T.Finite → Nivat.IsLatticeConvexRegion T → T.Nonempty →
        ∀ g, g ∉ T → ∃ n ∈ E T, ∀ z ∈ T, dot n z < dot n g := by
  intro h
  obtain ⟨n, hn, -⟩ :=
    h ({((0 : ℤ), (0 : ℤ))} : Set (ℤ × ℤ)) (Set.finite_singleton _)
      latticeConvex_singleton_zero ⟨_, rfl⟩ ((1 : ℤ), (0 : ℤ))
      (by simp [Prod.ext_iff])
  rw [E_singleton_eq_empty] at hn
  exact hn

/-- The separating normal is automatically an **outer** normal for the sweep direction:
if `T` sits inside the half-strip `H_B(v)` and contains `B`, and `g ∈ H_B(v)` is cut off
by `n`, then `0 < dot n v`.

This is the step `geo-bound` was missing.  It needs no convexity at all — only
`B ⊆ T` and the fact that `g` is reached from `B` by a **non-negative** multiple of `v`. -/
theorem dot_pos_of_separating {B T : Set (ℤ × ℤ)} {v n g : ℤ × ℤ}
    (hBT : B ⊆ T) (hg : g ∈ halfStrip B v)
    (hsep : ∀ z ∈ T, dot n z < dot n g) : 0 < dot n v := by
  obtain ⟨b, hb, t, rfl⟩ := hg
  have hbT : dot n b < dot n (b + (t : ℤ) • v) := hsep b (hBT hb)
  rw [dot_add] at hbT
  have ht : 0 < dot n ((t : ℤ) • v) := by omega
  rcases Nat.eq_zero_or_pos t with rfl | htpos
  · simp [dot] at ht
  · by_contra hle
    have hvle : dot n v ≤ 0 := not_lt.mp hle
    have : dot n ((t : ℤ) • v) = (t : ℤ) * dot n v := by
      simp only [dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      ring
    rw [this] at ht
    have : (t : ℤ) * dot n v ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg t) hvle
    omega

/-- **The uniform reach bound.**  Combining the two: for `T` in the family, every point of
`T` is reached from `B` by at most `(dot n g - dot n b) / dot n v` steps along `v`, where
`n` is the separating edge normal.  Stated as the inequality that bounds the step count. -/
theorem reach_bound {T : Set (ℤ × ℤ)} {v n g b z : ℤ × ℤ} {t : ℕ}
    (hsep : ∀ z ∈ T, dot n z < dot n g)
    (hzT : z ∈ T) (hz : z = b + (t : ℤ) • v) :
    (t : ℤ) * dot n v < dot n g - dot n b := by
  have h1 : dot n z < dot n g := hsep z hzT
  rw [hz, dot_add] at h1
  have h2 : dot n ((t : ℤ) • v) = (t : ℤ) * dot n v := by
    simp only [dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  rw [h2] at h1
  omega

end Nivat.EdgeSeparating

#print axioms Nivat.EdgeSeparating.exists_edge_separating
#print axioms Nivat.EdgeSeparating.exists_edge_separating_false_without_posArea
#print axioms Nivat.EdgeSeparating.dot_pos_of_separating
#print axioms Nivat.EdgeSeparating.reach_bound
#print axioms Nivat.EdgeSeparating.E_singleton_eq_empty
