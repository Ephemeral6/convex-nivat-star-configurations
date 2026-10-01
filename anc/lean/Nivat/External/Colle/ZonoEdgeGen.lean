/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.MinkowskiEdges
import Nivat.External.Colle.NewtonZonotope

/-!
# Lemma C: Zonotope edges are determined by generators

原文：b3_colle2.txt:766

For a zonotope `Z = ∑ j ∈ s, {0, h j}` with pairwise non-parallel generators,
the edges of `Z` are exactly the segments `{x, x + h j}`, and the edge normals
are exactly the primitive perpendiculars to the generators.

**Consumer (hard rule 7):** `tmp/wip/EnvCornerFit.lean` (lane-hsupp-prove) Lemma C/D,
which needs `ν ∈ E Z → ∃ j, dot ν (h j) = 0` and face cardinality.
Final consumer: `RegionSteps.lean` binder `hsuppZ`.

## Main results

* `face_zonoF_eq` — every edge normal ν has exactly one generator with `dot ν (h j) = 0`
* `mem_E_zonoF` — every generator contributes two edge normals (±genPerp)
* `face_encard_zonoF` — edge has exactly 2 points

## Status

All 3 theorems proved; axioms `[propext, Classical.choice, Quot.sound]` (integrator, 2026-09-22).
`genPerp` is named to avoid the `ColleReg.perp` / `ANormal.perp_ne_zero` clashes.
-/

namespace Nivat.LE2

open Nivat Nivat.Colle Finset Classical Pointwise

variable {m : ℕ}

/-! ## §1. The perpendicular operator

For a vector `v`, the perpendicular `genPerp v` is `dir v`, the direction orthogonal to `v`. -/

/-- The perpendicular operator: same as `dir`. -/
def genPerp (v : ℤ × ℤ) : ℤ × ℤ := dir v

theorem dot_genPerp (v : ℤ × ℤ) : dot v (genPerp v) = 0 := dot_dir v

theorem genPerp_ne_zero {v : ℤ × ℤ} (hv : v ≠ 0) : genPerp v ≠ 0 := by
  intro h
  unfold genPerp at h
  cases v with | mk a b =>
  have : (-b, a) = (0, 0) := h
  simp at this
  have : (a, b) = (0, 0) := by ext <;> simp [this.1, this.2]
  exact hv this

/-- The primitized perpendicular. -/
def genPerp' (v : ℤ × ℤ) : ℤ × ℤ := primPart (genPerp v)

theorem genPerp'_prim {v : ℤ × ℤ} (hv : v ≠ 0) : Prim (genPerp' v) := by
  unfold genPerp'
  exact (primPart_spec (genPerp_ne_zero hv)).1

theorem dot_zsmul_right' (m : ℤ × ℤ) (k : ℤ) (z : ℤ × ℤ) : dot m (k • z) = k * dot m z := by
  simp only [dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

theorem dot_genPerp' {v : ℤ × ℤ} (hv : v ≠ 0) : dot v (genPerp' v) = 0 := by
  unfold genPerp'
  obtain ⟨_, g, hg, heq⟩ := primPart_spec (genPerp_ne_zero hv)
  have hdot : dot v (genPerp v) = 0 := dot_genPerp v
  have : dot v (genPerp v) = (g : ℤ) * dot v (primPart (genPerp v)) := by
    conv_lhs => rw [heq]
    rw [dot_zsmul_right']
  rw [hdot] at this
  have hg_pos : (0 : ℤ) < g := by omega
  nlinarith [sq_nonneg (dot v (primPart (genPerp v)))]

/-! ## §2. Core lemma: at most one orthogonal generator -/

theorem at_most_one_orthogonal (h : Fin m → ℤ × ℤ)
    (h_dir : ∀ j k : Fin m, j ≠ k → det (h j) (h k) ≠ 0)
    (n : ℤ × ℤ) (hn : n ≠ 0) :
    ∀ j k : Fin m, dot n (h j) = 0 → dot n (h k) = 0 → j = k := by
  intro j k hj hk
  by_contra hjk
  have hdet : det (h j) (h k) = 0 := det_eq_zero_of_dot_eq_zero hn hj hk
  exact h_dir j k hjk hdet

/-! ## §3. Main theorems -/

/-- **Lemma C, part 1: edge normals correspond to generators.**

For every edge normal `ν` of the zonotope, there exists a unique generator `h j`
such that `dot ν (h j) = 0`. -/
theorem face_zonoF_eq (h : Fin m → ℤ × ℤ) (h_ne : ∀ j, h j ≠ 0)
    (h_dir : ∀ j k, j ≠ k → det (h j) (h k) ≠ 0)
    (ν : ℤ × ℤ) (hν : ν ∈ E (↑(zonoF Finset.univ h) : Set (ℤ × ℤ))) :
    ∃! j : Fin m, dot ν (h j) = 0 := by
  -- Convert to Set-level zonotope using coe_zonoF
  rw [coe_zonoF] at hν
  -- Use E_zono to decompose edge normals
  rw [E_zono] at hν
  simp only [Set.mem_iUnion, Finset.mem_univ] at hν
  obtain ⟨j, -, hνj⟩ := hν
  -- Use E_segOf to characterize edge normals of segments
  -- E_segOf gives: E (segOf v) = {n | Prim n ∧ dot n v = 0}
  rw [E_segOf (h_ne j)] at hνj
  simp only [Set.mem_ofPred_eq] at hνj
  have hν_prim : Prim ν := hνj.1
  have hν_orth : dot ν (h j) = 0 := hνj.2
  -- j is the unique generator orthogonal to ν
  refine ⟨j, hν_orth, fun k hk => (at_most_one_orthogonal h h_dir ν hν_prim.ne_zero j k hν_orth hk).symm⟩

/-- **Lemma C, part 2: every generator contributes edge normals.**

Both `genPerp' (h j)` and `-genPerp' (h j)` are edge normals of the zonotope. -/
theorem mem_E_zonoF (h : Fin m → ℤ × ℤ) (h_ne : ∀ j, h j ≠ 0)
    (h_dir : ∀ j k, j ≠ k → det (h j) (h k) ≠ 0)
    (j : Fin m) :
    genPerp' (h j) ∈ E (↑(zonoF Finset.univ h) : Set (ℤ × ℤ)) ∧
    -genPerp' (h j) ∈ E (↑(zonoF Finset.univ h) : Set (ℤ × ℤ)) := by
  constructor
  · -- genPerp' (h j) is an edge normal
    rw [coe_zonoF, E_zono]
    refine Set.mem_biUnion (Finset.mem_univ j) ?_
    rw [E_segOf (h_ne j)]
    constructor
    · exact genPerp'_prim (h_ne j)
    · rw [dot_comm]
      exact dot_genPerp' (h_ne j)
  · -- -genPerp' (h j) is also an edge normal
    rw [coe_zonoF, E_zono]
    refine Set.mem_biUnion (Finset.mem_univ j) ?_
    rw [E_segOf (h_ne j)]
    constructor
    · exact (genPerp'_prim (h_ne j)).neg
    · rw [dot_neg_left, dot_comm]
      simp [dot_genPerp' (h_ne j)]

/-- The face of a segment `{0, v}` in direction `ν`: the whole segment if `ν ⟂ v`, the
endpoint `v` if `dot ν v > 0`, the origin if `dot ν v < 0`. -/
theorem face_segOf_cases (v ν : ℤ × ℤ) :
    face (segOf v) ν = if dot ν v = 0 then segOf v
                        else if 0 < dot ν v then {v} else {0} := by
  by_cases hk : dot ν v = 0
  · simp only [hk, ↓reduceIte]
    exact face_segOf_of_dot_eq_zero hk
  · simp only [hk, ↓reduceIte]
    by_cases hpos : 0 < dot ν v
    · simp only [hpos, ↓reduceIte]
      ext z
      simp only [face, segOf, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨hz, hmax⟩
        rcases hz with rfl | rfl
        · have := hmax v (Or.inr rfl)
          rw [dot_zero_right] at this
          omega
        · rfl
      · rintro rfl
        refine ⟨Or.inr rfl, fun y hy => ?_⟩
        rcases hy with rfl | rfl
        · rw [dot_zero_right]; omega
        · exact le_rfl
    · have hneg : dot ν v < 0 := lt_of_le_of_ne (not_lt.mp hpos) hk
      simp only [hpos, ↓reduceIte]
      ext z
      simp only [face, segOf, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨hz, hmax⟩
        rcases hz with rfl | rfl
        · rfl
        · have := hmax 0 (Or.inl rfl)
          rw [dot_zero_right] at this
          omega
      · rintro rfl
        refine ⟨Or.inl rfl, fun y hy => ?_⟩
        rcases hy with rfl | rfl
        · exact le_rfl
        · rw [dot_zero_right]; omega

/-- The face of a finite Minkowski sum is the Minkowski sum of the faces (iterated
`face_add`). -/
theorem face_sum {ι : Type*} [DecidableEq ι] (s : Finset ι) (A : ι → Set (ℤ × ℤ))
    (ν : ℤ × ℤ) :
    face (∑ i ∈ s, A i) ν = ∑ i ∈ s, face (A i) ν := by
  induction s using Finset.induction with
  | empty =>
      simp only [Finset.sum_empty]
      ext z
      simp only [face, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨rfl, _⟩; rfl
      · rintro rfl
        exact ⟨rfl, fun y hy => by rw [Set.mem_singleton_iff.mp hy]⟩
  | insert k t hkt ih =>
      rw [Finset.sum_insert hkt, Finset.sum_insert hkt, face_add, ih]

/-- A finite Minkowski sum of singletons is the singleton of the sum. -/
theorem sum_singleton_eq {ι : Type*} [DecidableEq ι] (s : Finset ι) (x : ι → ℤ × ℤ) :
    (∑ i ∈ s, ({x i} : Set (ℤ × ℤ))) = {∑ i ∈ s, x i} := by
  induction s using Finset.induction with
  | empty => simp only [Finset.sum_empty]; rfl
  | insert k t hkt ih =>
      rw [Finset.sum_insert hkt, Finset.sum_insert hkt, ih, Set.singleton_add_singleton]

/-- **Lemma C, part 3: edge face has exactly 2 lattice points.**

The edge face with normal `genPerp' (h j)` has exactly 2 lattice points. -/
theorem face_encard_zonoF (h : Fin m → ℤ × ℤ) (h_ne : ∀ j, h j ≠ 0)
    (h_dir : ∀ j k, j ≠ k → det (h j) (h k) ≠ 0)
    (j : Fin m) :
    (face (↑(zonoF Finset.univ h) : Set (ℤ × ℤ)) (genPerp' (h j))).encard = 2 := by
  set ν := genPerp' (h j) with hν_def
  have hν_E : ν ∈ E (↑(zonoF Finset.univ h) : Set (ℤ × ℤ)) := (mem_E_zonoF h h_ne h_dir j).1
  have hν_ne : ν ≠ 0 := (genPerp'_prim (h_ne j)).ne_zero
  have hj_orth : dot ν (h j) = 0 := by rw [hν_def, dot_comm]; exact dot_genPerp' (h_ne j)
  -- every other generator is non-orthogonal to ν
  have hk_orth : ∀ k, k ≠ j → dot ν (h k) ≠ 0 := fun k hkj hk =>
    hkj (at_most_one_orthogonal h h_dir ν hν_ne k j hk hj_orth)
  -- the point contributed by the non-orthogonal generators
  let x : ℤ × ℤ := ∑ k ∈ (Finset.univ.erase j), (if 0 < dot ν (h k) then h k else 0)
  have hrest : ∑ k ∈ (Finset.univ.erase j), face (segOf (h k)) ν = {x} := by
    rw [← sum_singleton_eq]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hkj : k ≠ j := Finset.ne_of_mem_erase hk
    rw [face_segOf_cases, if_neg (hk_orth k hkj)]
    split_ifs <;> rfl
  rw [coe_zonoF, face_sum, ← Finset.sum_erase_add _ _ (Finset.mem_univ j), hrest,
    face_segOf_cases, if_pos hj_orth]
  have hpair : ({x} : Set (ℤ × ℤ)) + segOf (h j) = {x, x + h j} := by
    simp only [segOf, Set.singleton_add, Set.image_insert_eq, Set.image_singleton, add_zero]
  rw [hpair]
  refine Set.encard_pair fun heq => h_ne j ?_
  have := congrArg (fun p : ℤ × ℤ => p - x) heq
  simpa using this.symm

end Nivat.LE2
