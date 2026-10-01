/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.Laurent.Newton
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.LocallyConvex.Separation

/-!
# Ostrowski's theorem: Newton polygons are additive

Formalisation of the standard fact quoted in §0.3 and §2.2 of *The Convex Nivat Conjecture*
(Pan):

> over an integral domain, `Newt(f g) = Newt(f) + Newt(g)` (Ostrowski).

The paper uses this twice: in (2.3) to identify `Newt(A) = Z` with the zonotope, and in
Lemma 2.5 to convert `f = A g` into `supp(g) ⊆ R_Z(S)`.

Mathlib has no Newton polygon at all, so this is proved from scratch (line A).

The inclusion `⊆` is elementary: a coefficient of `f g` is a finite sum over pairs, so
`supp (f g) ⊆ supp f + supp g`, and `convexHull` turns Minkowski sums into Minkowski sums
(`convexHull_add`).  The inclusion `⊇` is the Ostrowski content.  The argument used here is
the supporting-functional one: for a linear functional `ℓ` on `ℝ²`, restrict `f` and `g` to
their `ℓ`-maximal faces; `ℤ²` has `UniqueSums`, so the two faces have a lattice point in their
sum reachable in exactly one way, and the corresponding coefficient of `f g` is a product of
two non-zero complex numbers, hence non-zero.  So the `ℓ`-maximum of `Newt(f g)` is at least
the sum of the `ℓ`-maxima of `Newt f` and `Newt g`, for every `ℓ`; since `Newt (f g)` is a
compact convex set, geometric Hahn–Banach turns this into the missing inclusion.

## Main results

* `Nivat.newt_mul` — `Newt(f g) = Newt(f) + Newt(g)`.

## Status

Complete; no `sorry`.
-/

namespace Nivat

open scoped Pointwise

/-! ### Elementary facts about the lattice embedding -/

private lemma toReal_add (a b : ℤ × ℤ) : toReal (a + b) = toReal a + toReal b := by
  simp [toReal]

private lemma image_toReal_add (A B : Set (ℤ × ℤ)) :
    toReal '' (A + B) = toReal '' A + toReal '' B := by
  ext x
  constructor
  · rintro ⟨_, ⟨a, ha, b, hb, rfl⟩, rfl⟩
    exact ⟨toReal a, ⟨a, ha, rfl⟩, toReal b, ⟨b, hb, rfl⟩, (toReal_add a b).symm⟩
  · rintro ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩
    exact ⟨a + b, ⟨a, ha, b, hb, rfl⟩, toReal_add a b⟩

/-! ### The supporting-functional argument -/

/-- A linear functional bounded by `c` on `supp f` is bounded by `c` on all of `Newt f`:
the maximum of a linear functional on a convex hull is attained on the generating set. -/
private lemma le_of_mem_newt {R : Type*} [CommRing R] {f : LaurentTwo R} {ℓ : ℝ × ℝ → ℝ}
    (hℓ : IsLinearMap ℝ ℓ) {c : ℝ}
    (h : ∀ u ∈ supp f, ℓ (toReal u) ≤ c) {x : ℝ × ℝ} (hx : x ∈ newt f) : ℓ x ≤ c := by
  rw [newt_eq_convexHull] at hx
  refine convexHull_min ?_ (convex_halfSpace_le hℓ c) hx
  rintro _ ⟨u, hu, rfl⟩
  exact h u hu

/-- The integral-domain input to Ostrowski's theorem.

For every linear functional `ℓ` on `ℝ²` the support of `f g` contains a point whose `ℓ`-value
dominates `ℓ u + ℓ v` for all `u ∈ supp f`, `v ∈ supp g`; that is, the `ℓ`-maximal face of
`Newt (f g)` is at least as far out as the sum of the `ℓ`-maximal faces of `Newt f` and
`Newt g`.

The witness is produced by intersecting the supports with their `ℓ`-maximal faces and applying
`UniqueSums (ℤ × ℤ)`: it yields lattice points `a₀`, `b₀` of the two faces whose sum is
reachable in exactly one way, so the coefficient of `f g` at `a₀ + b₀` is the single product
`c_{a₀} d_{b₀} ≠ 0`.  Paper §0.3. -/
private theorem exists_mem_supp_mul_ge {R : Type*} [CommRing R] [IsDomain R]
    {f g : LaurentTwo R} (hf : f ≠ 0) (hg : g ≠ 0)
    {ℓ : ℝ × ℝ → ℝ} (hℓ : IsLinearMap ℝ ℓ) :
    ∃ w ∈ supp (f * g), ∀ u ∈ supp f, ∀ v ∈ supp g,
      ℓ (toReal u) + ℓ (toReal v) ≤ ℓ (toReal w) := by
  classical
  obtain ⟨a₁, ha₁, ha₁max⟩ :=
    Finset.exists_max_image (supp f) (fun z => ℓ (toReal z)) (supp_nonempty hf)
  obtain ⟨b₁, hb₁, hb₁max⟩ :=
    Finset.exists_max_image (supp g) (fun z => ℓ (toReal z)) (supp_nonempty hg)
  -- the `ℓ`-maximal faces of the two supports
  set F : Finset (ℤ × ℤ) := (supp f).filter fun z => ℓ (toReal a₁) ≤ ℓ (toReal z) with hFdef
  set G : Finset (ℤ × ℤ) := (supp g).filter fun z => ℓ (toReal b₁) ≤ ℓ (toReal z) with hGdef
  have hFmem : ∀ {z}, z ∈ F ↔ z ∈ supp f ∧ ℓ (toReal a₁) ≤ ℓ (toReal z) := by
    intro z; rw [hFdef, Finset.mem_filter]
  have hGmem : ∀ {z}, z ∈ G ↔ z ∈ supp g ∧ ℓ (toReal b₁) ≤ ℓ (toReal z) := by
    intro z; rw [hGdef, Finset.mem_filter]
  have hFne : F.Nonempty := ⟨a₁, hFmem.mpr ⟨ha₁, le_rfl⟩⟩
  have hGne : G.Nonempty := ⟨b₁, hGmem.mpr ⟨hb₁, le_rfl⟩⟩
  obtain ⟨a₀, ha₀F, b₀, hb₀G, huniq⟩ := UniqueSums.uniqueAdd_of_nonempty hFne hGne
  have ha₀ : a₀ ∈ supp f := (hFmem.mp ha₀F).1
  have hb₀ : b₀ ∈ supp g := (hGmem.mp hb₀G).1
  have ha₀val : ℓ (toReal a₀) = ℓ (toReal a₁) :=
    le_antisymm (ha₁max a₀ ha₀) (hFmem.mp ha₀F).2
  have hb₀val : ℓ (toReal b₀) = ℓ (toReal b₁) :=
    le_antisymm (hb₁max b₀ hb₀) (hGmem.mp hb₀G).2
  -- `a₀ + b₀` is reachable in exactly one way from `supp f + supp g`, not just from `F + G`
  have huniq' : UniqueAdd (supp f) (supp g) a₀ b₀ := by
    intro u v hu hv huv
    have hsum : ℓ (toReal u) + ℓ (toReal v) = ℓ (toReal a₀) + ℓ (toReal b₀) := by
      rw [← hℓ.map_add, ← hℓ.map_add, ← toReal_add, ← toReal_add, huv]
    rw [ha₀val, hb₀val] at hsum
    have h1 := ha₁max u hu
    have h2 := hb₁max v hv
    exact huniq (hFmem.mpr ⟨hu, by linarith⟩) (hGmem.mpr ⟨hv, by linarith⟩) huv
  refine ⟨a₀ + b₀, ?_, ?_⟩
  · rw [mem_supp, AddMonoidAlgebra.coeff_mul_add_of_uniqueAdd huniq']
    exact mul_ne_zero (mem_supp.mp ha₀) (mem_supp.mp hb₀)
  · intro u hu v hv
    rw [toReal_add, hℓ.map_add, ha₀val, hb₀val]
    have h1 := ha₁max u hu
    have h2 := hb₁max v hv
    linarith

/-! ### Ostrowski's theorem -/

/-- The easy inclusion: a coefficient of `f g` is a finite sum over pairs, so
`supp (f g) ⊆ supp f + supp g`, and `convexHull` is additive for Minkowski sums. -/
private theorem newt_mul_subset {R : Type*} [CommRing R] (f g : LaurentTwo R) :
    newt (f * g) ⊆ newt f + newt g := by
  classical
  have hss : supp (f * g) ⊆ supp f + supp g := AddMonoidAlgebra.support_coeff_mul_subset f g
  rw [newt_eq_convexHull, newt_eq_convexHull, newt_eq_convexHull, ← convexHull_add,
    ← image_toReal_add, ← Finset.coe_add]
  exact convexHull_mono (Set.image_mono (Finset.coe_subset.mpr hss))

/-- **Ostrowski.**  Over an integral domain the Newton polygon of a product is the Minkowski
sum of the Newton polygons.  Paper §0.3, used at (2.3) and in Lemma 2.5. -/
theorem newt_mul {R : Type*} [CommRing R] [IsDomain R] {f g : LaurentTwo R}
    (hf : f ≠ 0) (hg : g ≠ 0) :
    newt (f * g) = newt f + newt g := by
  refine Set.Subset.antisymm (newt_mul_subset f g) ?_
  intro x hx
  by_contra hxn
  obtain ⟨ℓ, c, hc₁, hc₂⟩ :=
    geometric_hahn_banach_closed_point (newt_convex (f * g)) (newt_isClosed (f * g)) hxn
  have hℓ : IsLinearMap ℝ (ℓ : ℝ × ℝ → ℝ) := ⟨ℓ.map_add, ℓ.map_smul⟩
  obtain ⟨w, hw, hwmax⟩ := exists_mem_supp_mul_ge hf hg hℓ
  obtain ⟨a₁, ha₁, ha₁max⟩ :=
    Finset.exists_max_image (supp f) (fun z => ℓ (toReal z)) (supp_nonempty hf)
  obtain ⟨b₁, hb₁, hb₁max⟩ :=
    Finset.exists_max_image (supp g) (fun z => ℓ (toReal z)) (supp_nonempty hg)
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  have hA : ℓ a ≤ ℓ (toReal a₁) := le_of_mem_newt hℓ ha₁max ha
  have hB : ℓ b ≤ ℓ (toReal b₁) := le_of_mem_newt hℓ hb₁max hb
  have hW : ℓ (toReal a₁) + ℓ (toReal b₁) ≤ ℓ (toReal w) := hwmax a₁ ha₁ b₁ hb₁
  have hwlt : ℓ (toReal w) < c := hc₁ (toReal w) (mem_newt_of_mem_supp hw)
  rw [hℓ.map_add] at hc₂
  linarith

/-- The Minkowski-sum inclusion that Lemma 2.5 actually consumes: every point of `supp g`,
translated by `Newt f`, stays inside `Newt (f * g)`. -/
theorem add_newt_subset_newt_mul {R : Type*} [CommRing R] [IsDomain R]
    {f g : LaurentTwo R} (hf : f ≠ 0) (hg : g ≠ 0)
    {r : ℤ × ℤ} (hr : r ∈ supp g) {x : ℝ × ℝ} (hx : x ∈ newt f) :
    toReal r + x ∈ newt (f * g) := by
  rw [newt_mul hf hg, add_comm (newt f) (newt g)]
  exact Set.add_mem_add (mem_newt_of_mem_supp hr) hx

/-- The Newton polygon of `1` is the origin. -/
@[simp] theorem newt_one {R : Type*} [CommRing R] [Nontrivial R] :
    newt (1 : LaurentTwo R) = 0 := by
  have h : (toReal 0 : ℝ × ℝ) = 0 := by simp [toReal]
  rw [← mono_zero, newt_mono, h, Set.singleton_zero]

/-- The Newton polygon of a product over a finite index set. -/
theorem newt_prod {R : Type*} [CommRing R] [IsDomain R] {ι : Type*}
    (s : Finset ι) (f : ι → LaurentTwo R) (hf : ∀ i ∈ s, f i ≠ 0) :
    newt (∏ i ∈ s, f i) = ∑ i ∈ s, newt (f i) := by
  classical
  revert hf
  induction s using Finset.induction_on with
  | empty =>
    intro _
    simp only [Finset.prod_empty, Finset.sum_empty]
    exact newt_one
  | @insert a s ha ih =>
    intro hf
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    have hfa : f a ≠ 0 := hf a (Finset.mem_insert_self a s)
    have hrest : ∀ i ∈ s, f i ≠ 0 := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    rw [newt_mul hfa (Finset.prod_ne_zero_iff.mpr hrest), ih hrest]

end Nivat
