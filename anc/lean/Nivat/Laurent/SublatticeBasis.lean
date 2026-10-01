/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.Laurent.Basic
import Nivat.Lattice.Zonotope
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.MonoidAlgebra.Support
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# A monomial spanning set for the quotient by two line-supported Laurent polynomials

Step 2 of the proof of **Lemma 5.2** of *The Convex Nivat Conjecture* (Pan),
paper §5.2 (pp. 15–16).

Fix two non-parallel lattice vectors `v, w` and two Laurent polynomials `A`, `B` supported on
the segments `[0, dv v]` and `[0, dw w]` of the lines `ℤv`, `ℤw`, with **both extreme
coefficients non-zero**.  The paper's `A` is `aᵢ = Aᵢ(u)` with `u = Y^{vᵢ}`, and its `B` is
`c_j = A_j(X^{v_j} w)` with `w = Y^{-v_j}`; in the application `v = vᵢ` and `w = -v_j`.
`span_quotient_pair` states that the quotient `R/(A, B)` is spanned, as a `K`-vector space, by
the monomials whose exponent lies in the parallelogram `P = [0, dv v] + [0, dw w]` of (5.4).

## The proof, and how it differs from the paper

The paper phrases the middle of Step 2 as: `R` is *free* as a `K[u^±, w^±]`-module with basis
`{Y^{r_n}}`, the `r_n` running over the `ν = |det(v, w)|` lattice points of a half-open
fundamental parallelogram.  Only the *spanning* half of that is ever used, so linear
independence is not proved here, and neither the representatives `r_n` nor the index `ν` are
ever constructed: `exists_fract_decomp` produces, for each individual `z`, some representative
of `z` modulo `ℤv + ℤw` lying in the half-open parallelogram, which is all the argument needs.

The reduction of an arbitrary integer power of `u` into the `K`-span of `u^0, …, u^{dv-1}` is
likewise not routed through `Polynomial K` and `AdjoinRoot`: it is the pair of relations
`reduce_top` and `reduce_bot`, read straight off `A ≡ 0` via the support hypothesis.  The
non-zero *trailing* coefficient is what powers `reduce_bot`, i.e. what makes `u` invertible in
the quotient.

## Main definitions and results

* `Nivat.Sublattice.exists_fract_decomp` — the half-open fundamental domain of `ℤv + ℤw`.
* `Nivat.Sublattice.fundBox` — the exponent set (5.3), as a half-open real box.
* `Nivat.Sublattice.span_quotient_pair` — **Step 2 of Lemma 5.2**.
* `Nivat.Sublattice.supp_prod_binomial_subset` — the support of a product of binomials.
* `Nivat.Sublattice.span_quotient_pair_of_prod` — the same, with `A`, `B` given as products
  of binomials `α Y^v - β`, the shape in which `aᵢ` and `c_j` actually arrive
  (`Nivat.StarConfig.aFac_eq_prod`, `cFac_eq_prod`).

## Status

Complete; no `sorry`.
-/

namespace Nivat.Sublattice

open scoped Pointwise

variable {K : Type*} [Field K]

/-! ### Lattice preliminaries -/

private theorem toReal_zsmul (n : ℤ) (z : ℤ × ℤ) : toReal (n • z) = (n : ℝ) • toReal z := by
  simp [toReal]

/-- Cramer's rule in the plane: `det(v,w) z = det(z,w) v + det(v,z) w`. -/
private theorem cramer (v w z : ℤ × ℤ) : det v w • z = det z w • v + det v z • w := by
  simp only [Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul, det]
  constructor <;> ring

/-- Every lattice point is congruent modulo the sublattice `ℤv + ℤw` to a point of the
half-open fundamental parallelogram `Π = {s v + t w : 0 ≤ s < 1, 0 ≤ t < 1}`.  Paper §5.2,
Step 2.

Real coordinates and `Int.fract` are used rather than integer division: `Int.emod` is always
non-negative, so for `det v w < 0` the quotient `s` would land in `(-1, 0]` instead. -/
theorem exists_fract_decomp {v w : ℤ × ℤ} (hdet : det v w ≠ 0) (z : ℤ × ℤ) :
    ∃ (r : ℤ × ℤ) (a b : ℤ) (s t : ℝ), z = r + a • v + b • w ∧
      0 ≤ s ∧ s < 1 ∧ 0 ≤ t ∧ t < 1 ∧ toReal r = s • toReal v + t • toReal w := by
  have hD : ((det v w : ℤ) : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hdet
  set x₁ : ℝ := ((det z w : ℤ) : ℝ) / ((det v w : ℤ) : ℝ) with hx₁
  set x₂ : ℝ := ((det v z : ℤ) : ℝ) / ((det v w : ℤ) : ℝ) with hx₂
  refine ⟨z - ⌊x₁⌋ • v - ⌊x₂⌋ • w, ⌊x₁⌋, ⌊x₂⌋, Int.fract x₁, Int.fract x₂, by abel,
    Int.fract_nonneg _, Int.fract_lt_one _, Int.fract_nonneg _, Int.fract_lt_one _, ?_⟩
  have hc : ((det v w : ℤ) : ℝ) • toReal z
      = ((det z w : ℤ) : ℝ) • toReal v + ((det v z : ℤ) : ℝ) • toReal w := by
    have h := congrArg toReal (cramer v w z)
    rwa [toReal_zsmul, toReal_add, toReal_zsmul, toReal_zsmul] at h
  have hz : toReal z = x₁ • toReal v + x₂ • toReal w := by
    have h := congrArg (fun p : ℝ × ℝ => ((det v w : ℤ) : ℝ)⁻¹ • p) hc
    simp only [smul_add, smul_smul, inv_mul_cancel₀ hD, one_smul] at h
    rw [hx₁, hx₂, div_eq_inv_mul, div_eq_inv_mul]
    exact h
  have key : toReal z
      = ((⌊x₁⌋ : ℝ) + Int.fract x₁) • toReal v + ((⌊x₂⌋ : ℝ) + Int.fract x₂) • toReal w := by
    rw [Int.floor_add_fract, Int.floor_add_fract]; exact hz
  rw [toReal_sub, toReal_sub, toReal_zsmul, toReal_zsmul, key]
  module

/-- The half-open box `{s v + t w : 0 ≤ s < dv, 0 ≤ t < dw}`, as a set of lattice points.
This is the exponent set (5.3) of the paper, described by its real coordinates rather than by
an explicit enumeration over coset representatives. -/
def fundBox (dv dw : ℕ) (v w : ℤ × ℤ) : Set (ℤ × ℤ) :=
  {e | ∃ s t : ℝ, 0 ≤ s ∧ s < dv ∧ 0 ≤ t ∧ t < dw ∧ toReal e = s • toReal v + t • toReal w}

private theorem smul_mem_latSegment {d : ℕ} {v : ℤ × ℤ} {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    c • toReal ((d : ℤ) • v) ∈ latSegment d v :=
  ⟨1 - c, c, by linarith, hc0, by ring, by simp⟩

/-- The exponents (5.3) lie in the parallelogram `P = [0, dv v] + [0, dw w]` of (5.4). -/
theorem fundBox_subset_latticePts (dv dw : ℕ) (v w : ℤ × ℤ) :
    fundBox dv dw v w ⊆ latticePts (latSegment dv v + latSegment dw w) := by
  rintro e ⟨s, t, hs0, hs1, ht0, ht1, he⟩
  have hdv : (0 : ℝ) < dv := lt_of_le_of_lt hs0 hs1
  have hdw : (0 : ℝ) < dw := lt_of_le_of_lt ht0 ht1
  have hx : s • toReal v ∈ latSegment dv v := by
    have h : s • toReal v = (s / dv) • toReal ((dv : ℤ) • v) := by
      rw [toReal_zsmul, smul_smul]
      congr 1
      push_cast
      field_simp
    rw [h]
    exact smul_mem_latSegment (div_nonneg hs0 hdv.le) ((div_le_one hdv).mpr hs1.le)
  have hy : t • toReal w ∈ latSegment dw w := by
    have h : t • toReal w = (t / dw) • toReal ((dw : ℤ) • w) := by
      rw [toReal_zsmul, smul_smul]
      congr 1
      push_cast
      field_simp
    rw [h]
    exact smul_mem_latSegment (div_nonneg ht0 hdw.le) ((div_le_one hdw).mpr ht1.le)
  show toReal e ∈ latSegment dv v + latSegment dw w
  rw [he]
  exact Set.add_mem_add hx hy

private theorem fundBox_comm (dv dw : ℕ) (v w : ℤ × ℤ) :
    fundBox dv dw v w = fundBox dw dv w v := by
  ext e
  constructor <;> rintro ⟨s, t, h1, h2, h3, h4, h5⟩ <;>
    exact ⟨t, s, h3, h4, h1, h2, by rw [h5]; abel⟩

/-! ### Expanding a product against the support -/

private theorem mono_mul_eq_sum (x : LaurentTwo K) (z : ℤ × ℤ) :
    mono z * x = ∑ u ∈ supp x, x.coeff u • mono (z + u) := by
  simp only [supp]
  conv_lhs => rw [← AddMonoidAlgebra.sum_coeff_single x]
  rw [Finsupp.mul_sum]
  simp only [Finsupp.sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  simp only [mono, AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.smul_single',
    one_mul, mul_one]

private noncomputable def mkL (I : Ideal (LaurentTwo K)) :
    LaurentTwo K →ₗ[K] LaurentTwo K ⧸ I := (Ideal.Quotient.mkₐ K I).toLinearMap

private theorem mkL_apply (I : Ideal (LaurentTwo K)) (x : LaurentTwo K) :
    mkL I x = Ideal.Quotient.mk I x := rfl

private theorem mk_smul (I : Ideal (LaurentTwo K)) (c : K) (x : LaurentTwo K) :
    Ideal.Quotient.mk I (c • x) = c • Ideal.Quotient.mk I x := by
  rw [← mkL_apply, ← mkL_apply, map_smul]

/-- The relation obtained by multiplying an element of the ideal by a monomial: in the
quotient, the coefficients of `x` give a linear dependence among the translates of `x`'s
support.  Both reduction lemmas below are read off this. -/
private theorem sum_smul_mk_eq_zero {I : Ideal (LaurentTwo K)} {x : LaurentTwo K} (hx : x ∈ I)
    (z : ℤ × ℤ) : ∑ u ∈ supp x, x.coeff u • Ideal.Quotient.mk I (mono (z + u)) = 0 := by
  have h : Ideal.Quotient.mk I (mono z * x) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mul_mem_left _ _ hx)
  rw [mono_mul_eq_sum, map_sum] at h
  rw [← h]
  exact Finset.sum_congr rfl fun u _ => (mk_smul I _ _).symm

/-- If `u ∈ supp x` and `supp x` lies on the segment `[0, d v]` of the line `ℤ v`, then
`u = k • v` for a unique `k ∈ [0, d]`. -/
private theorem exists_coeff_of_mem_supp {d : ℕ} {v : ℤ × ℤ} {x : LaurentTwo K}
    (hsupp : supp x ⊆ (Finset.Icc (0 : ℤ) d).image (· • v)) {u : ℤ × ℤ} (hu : u ∈ supp x) :
    ∃ k : ℤ, 0 ≤ k ∧ k ≤ d ∧ u = k • v := by
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp (hsupp hu)
  exact ⟨k, (Finset.mem_Icc.mp hk).1, (Finset.mem_Icc.mp hk).2, rfl⟩

/-- **Downward reduction.**  The non-zero leading coefficient of `x` expresses `Y^{z + d v}`
through the lower translates `Y^{z + k v}`, `0 ≤ k < d`. -/
private theorem reduce_top {I : Ideal (LaurentTwo K)} {d : ℕ} {v : ℤ × ℤ}
    {x : LaurentTwo K} (hsupp : supp x ⊆ (Finset.Icc (0 : ℤ) d).image (· • v))
    (htop : (d : ℤ) • v ∈ supp x) (hx : x ∈ I) (N : Submodule K (LaurentTwo K ⧸ I))
    (z : ℤ × ℤ)
    (hz : ∀ k : ℤ, 0 ≤ k → k < d → Ideal.Quotient.mk I (mono (z + k • v)) ∈ N) :
    Ideal.Quotient.mk I (mono (z + (d : ℤ) • v)) ∈ N := by
  classical
  have hsum := sum_smul_mk_eq_zero hx z
  rw [← Finset.add_sum_erase _ _ htop] at hsum
  have hrest : ∑ u ∈ (supp x).erase ((d : ℤ) • v),
      x.coeff u • Ideal.Quotient.mk I (mono (z + u)) ∈ N := by
    refine Submodule.sum_mem _ fun u hu => ?_
    obtain ⟨k, hk0, hkd, rfl⟩ :=
      exists_coeff_of_mem_supp hsupp (Finset.mem_of_mem_erase hu)
    have hne : k ≠ (d : ℤ) := fun h =>
      Finset.ne_of_mem_erase hu (by rw [h])
    exact Submodule.smul_mem _ _ (hz k hk0 (lt_of_le_of_ne hkd hne))
  have hmain : x.coeff ((d : ℤ) • v) • Ideal.Quotient.mk I (mono (z + (d : ℤ) • v)) ∈ N := by
    have : x.coeff ((d : ℤ) • v) • Ideal.Quotient.mk I (mono (z + (d : ℤ) • v))
        = -∑ u ∈ (supp x).erase ((d : ℤ) • v),
            x.coeff u • Ideal.Quotient.mk I (mono (z + u)) := by
      rw [eq_neg_iff_add_eq_zero]; exact hsum
    rw [this]
    exact Submodule.neg_mem _ hrest
  have hne : x.coeff ((d : ℤ) • v) ≠ 0 := mem_supp.mp htop
  have := Submodule.smul_mem N (x.coeff ((d : ℤ) • v))⁻¹ hmain
  rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at this

/-- **Upward reduction.**  The non-zero trailing coefficient of `x` expresses `Y^z` through the
higher translates `Y^{z + k v}`, `1 ≤ k ≤ d`.  This is what makes `Y^v` invertible in the
quotient, and is the only place the hypothesis `A(0) ≠ 0` of the paper is used. -/
private theorem reduce_bot {I : Ideal (LaurentTwo K)} {d : ℕ} {v : ℤ × ℤ}
    {x : LaurentTwo K} (hsupp : supp x ⊆ (Finset.Icc (0 : ℤ) d).image (· • v))
    (hbot : (0 : ℤ × ℤ) ∈ supp x) (hx : x ∈ I) (N : Submodule K (LaurentTwo K ⧸ I))
    (z : ℤ × ℤ)
    (hz : ∀ k : ℤ, 1 ≤ k → k ≤ d → Ideal.Quotient.mk I (mono (z + k • v)) ∈ N) :
    Ideal.Quotient.mk I (mono z) ∈ N := by
  classical
  have hsum := sum_smul_mk_eq_zero hx z
  rw [← Finset.add_sum_erase _ _ hbot] at hsum
  have hrest : ∑ u ∈ (supp x).erase 0,
      x.coeff u • Ideal.Quotient.mk I (mono (z + u)) ∈ N := by
    refine Submodule.sum_mem _ fun u hu => ?_
    obtain ⟨k, hk0, hkd, rfl⟩ :=
      exists_coeff_of_mem_supp hsupp (Finset.mem_of_mem_erase hu)
    have hne : k ≠ 0 := fun h => Finset.ne_of_mem_erase hu (by rw [h]; simp)
    exact Submodule.smul_mem _ _ (hz k (lt_of_le_of_ne hk0 (Ne.symm hne)) hkd)
  have hmain : x.coeff 0 • Ideal.Quotient.mk I (mono z) ∈ N := by
    have heq : x.coeff 0 • Ideal.Quotient.mk I (mono z)
        = -∑ u ∈ (supp x).erase 0, x.coeff u • Ideal.Quotient.mk I (mono (z + u)) := by
      rw [eq_neg_iff_add_eq_zero, ← add_zero z]
      simpa using hsum
    rw [heq]
    exact Submodule.neg_mem _ hrest
  have hne : x.coeff 0 ≠ 0 := mem_supp.mp hbot
  have := Submodule.smul_mem N (x.coeff 0)⁻¹ hmain
  rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at this

/-! ### Stability of the span under translation by `±v` -/

/-- Translating a generator by `+v` stays in the span: either the box coordinate `s + 1` is
still `< dv`, or `reduce_top` applies at the base point `e + v - dv • v`. -/
private theorem stab_add {I : Ideal (LaurentTwo K)} {dv dw : ℕ} {v w : ℤ × ℤ}
    {A : LaurentTwo K} (hAsupp : supp A ⊆ (Finset.Icc (0 : ℤ) dv).image (· • v))
    (hAtop : (dv : ℤ) • v ∈ supp A) (hAI : A ∈ I) (N : Submodule K (LaurentTwo K ⧸ I))
    (hgen : ∀ e ∈ fundBox dv dw v w, Ideal.Quotient.mk I (mono e) ∈ N)
    {e : ℤ × ℤ} (he : e ∈ fundBox dv dw v w) :
    Ideal.Quotient.mk I (mono (e + v)) ∈ N := by
  obtain ⟨s, t, hs0, hs1, ht0, ht1, he'⟩ := he
  by_cases hlt : s + 1 < dv
  · refine hgen _ ⟨s + 1, t, by linarith, hlt, ht0, ht1, ?_⟩
    rw [toReal_add, he']
    module
  · have hlt' : (dv : ℝ) ≤ s + 1 := not_lt.mp hlt
    have hrw : e + v = e + v - (dv : ℤ) • v + (dv : ℤ) • v := by abel
    rw [hrw]
    refine reduce_top hAsupp hAtop hAI N _ fun k hk0 hkd => ?_
    have hk1 : (k : ℝ) ≤ (dv : ℝ) - 1 := by
      have : k ≤ (dv : ℤ) - 1 := by omega
      exact_mod_cast this
    have hk0' : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk0
    refine hgen _ ⟨s + 1 + k - dv, t, by linarith, by linarith, ht0, ht1, ?_⟩
    rw [show e + v - (dv : ℤ) • v + k • v = e + v - (dv : ℤ) • v + k • v from rfl,
      toReal_add, toReal_sub, toReal_add, toReal_zsmul, toReal_zsmul, he']
    push_cast
    module

/-- Translating a generator by `-v` stays in the span: either the box coordinate `s - 1` is
still `≥ 0`, or `reduce_bot` applies at the base point `e - v`. -/
private theorem stab_sub {I : Ideal (LaurentTwo K)} {dv dw : ℕ} {v w : ℤ × ℤ}
    {A : LaurentTwo K} (hAsupp : supp A ⊆ (Finset.Icc (0 : ℤ) dv).image (· • v))
    (hAbot : (0 : ℤ × ℤ) ∈ supp A) (hAI : A ∈ I) (N : Submodule K (LaurentTwo K ⧸ I))
    (hgen : ∀ e ∈ fundBox dv dw v w, Ideal.Quotient.mk I (mono e) ∈ N)
    {e : ℤ × ℤ} (he : e ∈ fundBox dv dw v w) :
    Ideal.Quotient.mk I (mono (e + -v)) ∈ N := by
  obtain ⟨s, t, hs0, hs1, ht0, ht1, he'⟩ := he
  by_cases hge : 0 ≤ s - 1
  · refine hgen _ ⟨s - 1, t, hge, by linarith, ht0, ht1, ?_⟩
    rw [toReal_add, he']
    have hneg : toReal (-v) = -toReal v := by
      simpa using toReal_zsmul (-1) v
    rw [hneg]
    module
  · have hge' : s - 1 < 0 := not_le.mp hge
    refine reduce_bot hAsupp hAbot hAI N _ fun k hk1 hkd => ?_
    have hk1' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    have hkd' : (k : ℝ) ≤ (dv : ℝ) := by exact_mod_cast hkd
    refine hgen _ ⟨s - 1 + k, t, by linarith, by linarith, ht0, ht1, ?_⟩
    have hneg : toReal (-v) = -toReal v := by simpa using toReal_zsmul (-1) v
    rw [toReal_add, toReal_add, toReal_zsmul, hneg, he']
    module

/-! ### Step 2 of Lemma 5.2 -/

private theorem span_eq_top_of_mem_isUnit {I : Ideal (LaurentTwo K)} {x : LaurentTwo K}
    (hx : x ∈ I) (hu : IsUnit x) (s : Set (LaurentTwo K ⧸ I)) :
    Submodule.span K s = ⊤ := by
  have hI : I = ⊤ := Ideal.eq_top_of_isUnit_mem I hx hu
  have : Subsingleton (LaurentTwo K ⧸ I) := Ideal.Quotient.subsingleton_iff.mpr hI
  refine Submodule.eq_top_iff'.mpr fun y => ?_
  rw [Subsingleton.elim y 0]
  exact Submodule.zero_mem _

private theorem isUnit_of_supp_subset_zero {x : LaurentTwo K} (h : supp x ⊆ {0})
    (h0 : (0 : ℤ × ℤ) ∈ supp x) : IsUnit x := by
  have hsupp : supp x = {0} := Finset.Subset.antisymm h (Finset.singleton_subset_iff.mpr h0)
  have hx : x = algebraMap K (LaurentTwo K) (x.coeff 0) := by
    have h1 := mono_mul_eq_sum x 0
    rw [mono_zero, one_mul, hsupp, Finset.sum_singleton, zero_add, mono_zero,
      Algebra.smul_def, mul_one] at h1
    exact h1
  rw [hx]
  exact (isUnit_iff_ne_zero.mpr (mem_supp.mp h0)).map _

/-- **Step 2 of Lemma 5.2.**  Let `v, w` be non-parallel lattice vectors and let `A`, `B` be
Laurent polynomials supported on the segments `[0, dv v]`, `[0, dw w]` with both extreme
coefficients non-zero.  Then, as a `K`-vector space, `R/(A, B)` is spanned by the images of
the monomials `Y^d` with `d` a lattice point of the parallelogram `[0, dv v] + [0, dw w]`.

In the application (paper §5.2) `v = vᵢ`, `w = -v_j`, `A = aᵢ`, `B = c_j`, and the
parallelogram is `P_ij` of (5.4). -/
theorem span_quotient_pair {v w : ℤ × ℤ} (hdet : det v w ≠ 0) {dv dw : ℕ}
    {A B : LaurentTwo K}
    (hAsupp : supp A ⊆ (Finset.Icc (0 : ℤ) dv).image (· • v))
    (hA0 : (0 : ℤ × ℤ) ∈ supp A) (hAtop : (dv : ℤ) • v ∈ supp A)
    (hBsupp : supp B ⊆ (Finset.Icc (0 : ℤ) dw).image (· • w))
    (hB0 : (0 : ℤ × ℤ) ∈ supp B) (hBtop : (dw : ℤ) • w ∈ supp B) :
    Submodule.span K
        ((fun d : ℤ × ℤ => Ideal.Quotient.mk (Ideal.span {A, B}) (mono d)) ''
          latticePts (latSegment dv v + latSegment dw w)) = ⊤ := by
  classical
  set I : Ideal (LaurentTwo K) := Ideal.span {A, B} with hIdef
  have hAI : A ∈ I := Ideal.subset_span (by simp)
  have hBI : B ∈ I := Ideal.subset_span (by simp)
  -- The degenerate cases: a Laurent polynomial of degree `0` with non-zero constant term is a
  -- unit, so the quotient vanishes and every submodule is `⊤`.
  rcases Nat.eq_zero_or_pos dv with hdv0 | hdv
  · refine span_eq_top_of_mem_isUnit hAI (isUnit_of_supp_subset_zero ?_ hA0) _
    intro u hu
    obtain ⟨k, hk0, hkd, rfl⟩ := exists_coeff_of_mem_supp hAsupp hu
    rw [hdv0] at hkd
    simp only [Nat.cast_zero] at hkd
    rw [le_antisymm hkd hk0]
    simp
  rcases Nat.eq_zero_or_pos dw with hdw0 | hdw
  · refine span_eq_top_of_mem_isUnit hBI (isUnit_of_supp_subset_zero ?_ hB0) _
    intro u hu
    obtain ⟨k, hk0, hkd, rfl⟩ := exists_coeff_of_mem_supp hBsupp hu
    rw [hdw0] at hkd
    simp only [Nat.cast_zero] at hkd
    rw [le_antisymm hkd hk0]
    simp
  set N : Submodule K (LaurentTwo K ⧸ I) :=
    Submodule.span K
      ((fun d : ℤ × ℤ => Ideal.Quotient.mk I (mono d)) '' fundBox dv dw v w) with hNdef
  have hgen : ∀ e ∈ fundBox dv dw v w, Ideal.Quotient.mk I (mono e) ∈ N := fun e he =>
    Submodule.subset_span ⟨e, he, rfl⟩
  -- `N` is stable under multiplication by `Y^{±v}` and `Y^{±w}`.
  have hstab : ∀ u : ℤ × ℤ,
      (∀ e ∈ fundBox dv dw v w, Ideal.Quotient.mk I (mono (e + u)) ∈ N) →
      ∀ y ∈ N, Ideal.Quotient.mk I (mono u) * y ∈ N := by
    intro u hu y hy
    have hle : N ≤ N.comap (LinearMap.mulLeft K (Ideal.Quotient.mk I (mono u))) := by
      rw [hNdef]
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨e, he, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap, LinearMap.mulLeft_apply, ← map_mul,
        mono_mul_mono, add_comm u e]
      exact hu e he
    exact hle hy
  have hgenBw : ∀ e ∈ fundBox dw dv w v, Ideal.Quotient.mk I (mono e) ∈ N := by
    rw [← fundBox_comm]; exact hgen
  have hsv : ∀ y ∈ N, Ideal.Quotient.mk I (mono v) * y ∈ N :=
    hstab v fun e he => stab_add hAsupp hAtop hAI N hgen he
  have hsv' : ∀ y ∈ N, Ideal.Quotient.mk I (mono (-v)) * y ∈ N :=
    hstab (-v) fun e he => stab_sub hAsupp hA0 hAI N hgen he
  have hsw : ∀ y ∈ N, Ideal.Quotient.mk I (mono w) * y ∈ N :=
    hstab w fun e he =>
      stab_add hBsupp hBtop hBI N hgenBw ((fundBox_comm dv dw v w) ▸ he)
  have hsw' : ∀ y ∈ N, Ideal.Quotient.mk I (mono (-w)) * y ∈ N :=
    hstab (-w) fun e he =>
      stab_sub hBsupp hB0 hBI N hgenBw ((fundBox_comm dv dw v w) ▸ he)
  -- Hence every translate of a generator by a lattice vector of `ℤv + ℤw` stays in `N`.
  have key : ∀ u : ℤ × ℤ, (∀ y ∈ N, Ideal.Quotient.mk I (mono u) * y ∈ N) →
      (∀ y ∈ N, Ideal.Quotient.mk I (mono (-u)) * y ∈ N) →
      ∀ (n : ℤ) (c : ℤ × ℤ), Ideal.Quotient.mk I (mono c) ∈ N →
        Ideal.Quotient.mk I (mono (c + n • u)) ∈ N := by
    intro u hpos hneg n
    induction n using Int.induction_on with
    | zero => intro c hc; simpa using hc
    | succ k ih =>
      intro c hc
      have h := hpos _ (ih c hc)
      rw [← map_mul, mono_mul_mono,
        show u + (c + (k : ℤ) • u) = c + ((k : ℤ) + 1) • u by rw [add_smul, one_smul]; abel] at h
      exact h
    | pred k ih =>
      intro c hc
      have h := hneg _ (ih c hc)
      rw [← map_mul, mono_mul_mono,
        show -u + (c + (-(k : ℤ)) • u) = c + (-(k : ℤ) - 1) • u by
          rw [sub_smul, one_smul]; abel] at h
      exact h
  -- Every monomial lies in `N`.
  have hmono : ∀ z : ℤ × ℤ, Ideal.Quotient.mk I (mono z) ∈ N := by
    intro z
    obtain ⟨r, a, b, s, t, hzr, hs0, hs1, ht0, ht1, hr⟩ := exists_fract_decomp hdet z
    have hrbox : r ∈ fundBox dv dw v w := by
      refine ⟨s, t, hs0, lt_of_lt_of_le hs1 ?_, ht0, lt_of_lt_of_le ht1 ?_, hr⟩
      · exact_mod_cast hdv
      · exact_mod_cast hdw
    rw [hzr]
    exact key w hsw hsw' b _ (key v hsv hsv' a r (hgen r hrbox))
  -- `N` is everything, and `N` is contained in the span over the parallelogram.
  have hNtop : N = ⊤ := by
    refine Submodule.eq_top_iff'.mpr fun y => ?_
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
    have hp : p = ∑ u ∈ supp p, p.coeff u • mono u := by
      have h1 := mono_mul_eq_sum p 0
      rw [mono_zero, one_mul] at h1
      simpa using h1
    rw [hp, map_sum]
    refine Submodule.sum_mem _ fun u _ => ?_
    rw [mk_smul]
    exact Submodule.smul_mem _ _ (hmono u)
  refine eq_top_iff.mpr ?_
  rw [← hNtop, hNdef]
  exact Submodule.span_mono (Set.image_mono (fundBox_subset_latticePts dv dw v w))

/-! ### Products of binomials `α Y^v - β`

The paper's `aᵢ` and `c_j` are products of `dᵢ` linear factors in the single variable
`Y^{vᵢ}` (resp. `X^{v_j} Y^{-v_j}`).  The lemmas below extract, for such a product, the three
support facts that `span_quotient_pair` consumes: the support lies on `{k v : 0 ≤ k ≤ d}`, and
the constant and leading coefficients are the products of the `-β_k` and of the `α_k`. -/

/-- Structure of a product of binomials `α_k Y^v - β_k`, `v ≠ 0`: its support lies in
`{k • v : 0 ≤ k ≤ s.card}`, its constant coefficient is `∏ (-β_k)` and its coefficient at
`s.card • v` is `∏ α_k`.  (No non-vanishing of `α_k`, `β_k` is needed for this.) -/
private theorem prod_binomial_struct {v : ℤ × ℤ} (hv : v ≠ 0) {ι : Type*} (s : Finset ι)
    (α β : ι → K) :
    supp (∏ k ∈ s, (AddMonoidAlgebra.single v (α k) - AddMonoidAlgebra.single 0 (β k)))
        ⊆ (Finset.Icc (0 : ℤ) s.card).image (· • v) ∧
      (∏ k ∈ s, (AddMonoidAlgebra.single v (α k) - AddMonoidAlgebra.single 0 (β k))).coeff 0
        = ∏ k ∈ s, (-β k) ∧
      (∏ k ∈ s, (AddMonoidAlgebra.single v (α k) - AddMonoidAlgebra.single 0 (β k))).coeff
          ((s.card : ℤ) • v)
        = ∏ k ∈ s, α k := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨?_, by simp [AddMonoidAlgebra.one_def], by simp [AddMonoidAlgebra.one_def]⟩
    intro u hu
    rw [supp, Finset.prod_empty, AddMonoidAlgebra.one_def] at hu
    have h0 : u = 0 := Finset.mem_singleton.mp (Finsupp.support_single_subset hu)
    rw [h0]
    exact Finset.mem_image.mpr ⟨0, by simp, by simp⟩
  | insert a s ha ih =>
    obtain ⟨ihsupp, ih0, ihtop⟩ := ih
    set P := ∏ k ∈ s, (AddMonoidAlgebra.single v (α k) - AddMonoidAlgebra.single 0 (β k))
      with hP
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.prod_insert ha, ← hP,
      Finset.card_insert_of_notMem ha]
    -- Two coefficients of `P` that vanish for support reasons.
    have hneg : P.coeff (-v) = 0 := by
      by_contra h
      obtain ⟨k, hk, hkv⟩ := Finset.mem_image.mp (ihsupp (mem_supp.mpr h))
      have hk0 : 0 ≤ k := (Finset.mem_Icc.mp hk).1
      have : (k + 1) • v = 0 := by rw [add_smul, one_smul, hkv]; simp
      rcases smul_eq_zero.mp this with h1 | h1
      · omega
      · exact hv h1
    have hbig : P.coeff (((s.card : ℤ) + 1) • v) = 0 := by
      by_contra h
      obtain ⟨k, hk, hkv⟩ := Finset.mem_image.mp (ihsupp (mem_supp.mpr h))
      have hkd : k ≤ s.card := (Finset.mem_Icc.mp hk).2
      have : ((s.card : ℤ) + 1 - k) • v = 0 := by rw [sub_smul, hkv]; simp
      rcases smul_eq_zero.mp this with h1 | h1
      · omega
      · exact hv h1
    refine ⟨?_, ?_, ?_⟩
    · -- support
      intro u hu
      rw [supp, sub_mul] at hu
      rcases Finset.mem_union.mp (Finsupp.support_sub hu) with hu | hu
      · obtain ⟨u', hu', rfl⟩ :=
          Finset.mem_image.mp (AddMonoidAlgebra.support_coeff_single_mul_subset P (α a) v hu)
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp (ihsupp hu')
        refine Finset.mem_image.mpr ⟨k + 1, ?_, ?_⟩
        · have := Finset.mem_Icc.mp hk
          exact Finset.mem_Icc.mpr ⟨by omega, by push_cast; omega⟩
        · simp only [add_smul, one_smul]; abel
      · obtain ⟨u', hu', rfl⟩ :=
          Finset.mem_image.mp (AddMonoidAlgebra.support_coeff_single_mul_subset P (β a) 0 hu)
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp (ihsupp hu')
        refine Finset.mem_image.mpr ⟨k, ?_, by simp⟩
        have := Finset.mem_Icc.mp hk
        exact Finset.mem_Icc.mpr ⟨by omega, by push_cast; omega⟩
    · -- constant coefficient
      rw [sub_mul, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply,
        AddMonoidAlgebra.coeff_single_mul_apply, AddMonoidAlgebra.coeff_single_mul_apply,
        add_zero, neg_zero, add_zero, hneg, ih0, mul_zero, zero_sub, ← neg_mul]
    · -- leading coefficient
      rw [sub_mul, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply,
        AddMonoidAlgebra.coeff_single_mul_apply, AddMonoidAlgebra.coeff_single_mul_apply,
        neg_zero, zero_add]
      push_cast
      rw [hbig, mul_zero, sub_zero,
        show -v + ((s.card : ℤ) + 1) • v = (s.card : ℤ) • v by rw [add_smul, one_smul]; abel,
        ihtop]

/-- The support half of `prod_binomial_struct`, exposed for callers that need only it: a
product of binomials `α_k Y^v - β_k` is supported on the segment `{k v : 0 ≤ k ≤ s.card}` of
the line `ℤ v`.  No non-vanishing of the coefficients is required. -/
theorem supp_prod_binomial_subset {v : ℤ × ℤ} (hv : v ≠ 0) {ι : Type*} (s : Finset ι)
    (α β : ι → K) :
    supp (∏ k ∈ s, (AddMonoidAlgebra.single v (α k) - AddMonoidAlgebra.single 0 (β k)))
      ⊆ (Finset.Icc (0 : ℤ) s.card).image (· • v) :=
  (prod_binomial_struct hv s α β).1

/-- **Step 2 of Lemma 5.2, for products of binomials.**  The form in which the paper's
`aᵢ = ∏ (Y^{vᵢ} - λ)` and `c_j = ∏ (X^{v_j} Y^{-v_j} - μ)` are actually given: `A` is a product
of `s.card` binomials `α_k Y^v - β_k` and `B` a product of `t.card` binomials `γ_k Y^w - δ_k`,
all coefficients non-zero.  Then `R/(A, B)` is spanned by the monomials with exponent in
`[0, s.card v] + [0, t.card w]`.

In the application `v = vᵢ`, `w = -v_j`, `s = t = ` the eigenvalue lists, `α = 1`, `β = λ`,
`γ = X^{v_j}`, `δ = μ`. -/
theorem span_quotient_pair_of_prod {v w : ℤ × ℤ} (hdet : det v w ≠ 0)
    {ι κ : Type*} {s : Finset ι} {t : Finset κ} {α β : ι → K} {γ δ : κ → K}
    (hα : ∀ k ∈ s, α k ≠ 0) (hβ : ∀ k ∈ s, β k ≠ 0)
    (hγ : ∀ k ∈ t, γ k ≠ 0) (hδ : ∀ k ∈ t, δ k ≠ 0)
    {A B : LaurentTwo K}
    (hA : A = ∏ k ∈ s, (AddMonoidAlgebra.single v (α k) - AddMonoidAlgebra.single 0 (β k)))
    (hB : B = ∏ k ∈ t, (AddMonoidAlgebra.single w (γ k) - AddMonoidAlgebra.single 0 (δ k))) :
    Submodule.span K
        ((fun d : ℤ × ℤ => Ideal.Quotient.mk (Ideal.span {A, B}) (mono d)) ''
          latticePts (latSegment s.card v + latSegment t.card w)) = ⊤ := by
  have hv : v ≠ 0 := fun h => hdet (by rw [h]; simp [det])
  have hw : w ≠ 0 := fun h => hdet (by rw [h]; simp [det])
  obtain ⟨hAsupp, hA0, hAtop⟩ := prod_binomial_struct hv s α β
  obtain ⟨hBsupp, hB0, hBtop⟩ := prod_binomial_struct hw t γ δ
  rw [← hA] at hAsupp hA0 hAtop
  rw [← hB] at hBsupp hB0 hBtop
  refine span_quotient_pair hdet hAsupp ?_ ?_ hBsupp ?_ ?_
  · rw [mem_supp, hA0]
    exact Finset.prod_ne_zero_iff.mpr fun k hk => neg_ne_zero.mpr (hβ k hk)
  · rw [mem_supp, hAtop]
    exact Finset.prod_ne_zero_iff.mpr hα
  · rw [mem_supp, hB0]
    exact Finset.prod_ne_zero_iff.mpr fun k hk => neg_ne_zero.mpr (hδ k hk)
  · rw [mem_supp, hBtop]
    exact Finset.prod_ne_zero_iff.mpr hγ

end Nivat.Sublattice
