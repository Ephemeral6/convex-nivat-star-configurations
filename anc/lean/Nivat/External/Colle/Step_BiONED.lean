/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.Section8.External
import Nivat.External.Colle.Lemma45
import Nivat.External.Colle.DirectionRigidity
import Nivat.External.Colle.R2Orientation
import Nivat.Lattice.Primitive

/-!
# The rationality step of Collé Lemma 2.6, at `A := ℤ`

`Nivat.ColleReg.exists_biONED_direction` (`RegionSteps.lean`) is the first of the six read-off
steps of `colle_region`.  This file proves it, under the name
`Nivat.ColleStep.exists_biONED_direction`, with a signature that is word-for-word the one in
`RegionSteps.lean` (the ambient `variable` binding `{ξ : Config ℤ}` inlined).

The statement: a minimal counterexample which has a *real* direction `w` with
`w, -w ∈ ONED ξ` has a *lattice* direction `ℓ`, primitive, which is nonexpansive and one-sided
nonexpansive on both sides.

## Proof

Following the recipe in the `RegionSteps.lean` docstring.

1. `hξ.1` gives `(Set.range ξ).Finite` and `LowConvexComplexity ξ`, hence `HasNonzeroAnn ξ`
   by `Nivat.hasNonzeroAnn_of_low_complexity` (Kari–Szabados 8.4(a)).
2. `Nivat.kari_szabados_prodShift` (8.4(b)) produces pairwise transverse non-zero
   `h : Fin n → ℤ × ℤ` with `act (prodShift h) ξ = 0`, and `Nivat.prodShift h` *is*
   `∏ i, (mono (h i) - 1)`.
3. `Nivat.Colle.exists_tangent_of_orbit_halfPlane_ambiguity` applied to the witnesses of
   `hw₁ : w ∈ ONED ξ` at `w := -w`, `c := 0` (legitimate since
   `inner2 (-w) z = -inner2 w z`, so `0 ≤ inner2 (-w) z ↔ z ∈ sideOf w`) yields an index `i`
   with `inner2 w (h i) = 0`.
4. Elementary lattice geometry.  With `v := h i ≠ 0` orthogonal to `w ≠ 0`, we get
   `w = t • (-(v.2 : ℝ), (v.1 : ℝ))` with `t ≠ 0`; taking `m := (-v.2, v.1)` when `t > 0` and
   `m := (v.2, -v.1)` when `t < 0` makes `inner2 w z = c * dot m z` with `c > 0`.  Writing
   `m = k • ℓ` with `ℓ` primitive and `k > 0` (`Nivat.exists_primitive_nsmul_eq`) gives
   `inner2 w z = (c * k) * dot ℓ z`, so `sideOf w = halfPlaneLE ℓ 0` and
   `sideOf (-w) = halfPlaneLE (-ℓ) 0` on the nose.

The two half-plane agreements then come from the two *independent* witness pairs supplied by
`hw₁` and `hw₂` — which is exactly what the obstacle recorded in `Lemma45.lean` demands.

`hξ` is used only through `IsCounterexample`; minimality is not needed.

## Status

Complete; no `sorry`, no new `axiom`.
-/

namespace Nivat.ColleStep

open Nivat Nivat.LE2

/-- Multiplying by a positive real does not change the sign of an integer. -/
private theorem mul_cast_nonpos_iff {c : ℝ} (hc : 0 < c) (s : ℤ) :
    c * (s : ℝ) ≤ 0 ↔ s ≤ 0 := by
  constructor
  · intro h
    have hs : (s : ℝ) ≤ 0 := by nlinarith
    exact_mod_cast hs
  · intro h
    have hs : (s : ℝ) ≤ 0 := by exact_mod_cast h
    nlinarith

/-- **The rationality step at `A := ℤ`** (Collé, Lemma 2.6).  A minimal counterexample with a
real direction `w` such that both `w` and `-w` are one-sided nonexpansive admits a *lattice*
direction `ℓ` that is nonexpansive and one-sided nonexpansive on *both* sides.

Signature identical to `Nivat.ColleReg.exists_biONED_direction`. -/
theorem exists_biONED_direction {ξ : Config ℤ} (hξ : IsMinimalCounterexample ξ)
    {w : ℝ × ℝ} (hw : w ≠ 0) (hw₁ : w ∈ ONED ξ) (hw₂ : -w ∈ ONED ξ) :
    ∃ ℓ : ℤ × ℤ, ℓ ∈ Colle45.NonExpansiveLine ξ ∧
      Colle45.IsOneSidedNonexpansive ξ ℓ ∧
      Colle45.IsOneSidedNonexpansive ξ (-ℓ) := by
  -- Step 1: a non-zero annihilator.
  obtain ⟨hA, -, -, hlow⟩ := hξ.1
  obtain ⟨S, hSne, -, hSP⟩ := hlow
  have hann : HasNonzeroAnn ξ := hasNonzeroAnn_of_low_complexity hA hSne hSP
  -- Step 2: Kari–Szabados product of transverse shift differences.
  obtain ⟨n, hh, -, hhne, hnp, hact⟩ := kari_szabados_prodShift hA hann
  have hact' : act (∏ i, (mono (hh i) - 1) : LaurentTwo ℤ) ξ = 0 := hact
  -- Step 3: the direction is orthogonal to one of the factors.
  obtain ⟨-, x, hx, y, hy, hxy, hagree⟩ := hw₁
  have hagree' : ∀ z : ℤ × ℤ, (0 : ℝ) ≤ inner2 (-w) z → x z = y z := by
    intro z hz
    refine hagree z ?_
    show inner2 w z ≤ 0
    rw [Nivat.R2.inner2_neg_left] at hz
    linarith
  obtain ⟨i, hi⟩ :=
    Nivat.Colle.exists_tangent_of_orbit_halfPlane_ambiguity hnp hact' hx hy hxy hagree'
  have hperp : inner2 w (hh i) = 0 := by
    rw [Nivat.R2.inner2_neg_left] at hi
    linarith
  set v : ℤ × ℤ := hh i with hvdef
  have hv : v ≠ 0 := hhne i
  -- Step 4a: `w` is a non-zero multiple of the rotation of `v`.
  have hperp' : (v.1 : ℝ) * w.1 + (v.2 : ℝ) * w.2 = 0 := hperp
  obtain ⟨t, ht1, ht2⟩ :
      ∃ t : ℝ, w.1 = t * (-(v.2 : ℝ)) ∧ w.2 = t * (v.1 : ℝ) := by
    by_cases h1 : v.1 = 0
    · have h2 : v.2 ≠ 0 := fun h2 => hv (Prod.ext h1 h2)
      have h2R : (v.2 : ℝ) ≠ 0 := Int.cast_ne_zero.mpr h2
      have h1R : (v.1 : ℝ) = 0 := by exact_mod_cast h1
      have hw2 : w.2 = 0 := by
        rw [h1R] at hperp'
        have : (v.2 : ℝ) * w.2 = 0 := by linarith
        rcases mul_eq_zero.mp this with h | h
        · exact absurd h h2R
        · exact h
      refine ⟨-w.1 / (v.2 : ℝ), ?_, ?_⟩
      · field_simp
      · rw [h1R, hw2, mul_zero]
    · have h1R : (v.1 : ℝ) ≠ 0 := Int.cast_ne_zero.mpr h1
      refine ⟨w.2 / (v.1 : ℝ), ?_, ?_⟩
      · field_simp
        linarith
      · field_simp
  have htne : t ≠ 0 := by
    intro h0
    rw [h0] at ht1 ht2
    exact hw (Prod.ext (by simpa using ht1) (by simpa using ht2))
  have hform : ∀ z : ℤ × ℤ, inner2 w z = t * ((dot (-v.2, v.1) z : ℤ) : ℝ) := by
    intro z
    simp only [inner2, dot, ht1, ht2]
    push_cast
    ring
  -- Step 4b: normalise the sign, so the multiplier is positive.
  obtain ⟨m, c, hcpos, hm, hmform⟩ :
      ∃ (m : ℤ × ℤ) (c : ℝ), 0 < c ∧ m ≠ 0 ∧
        ∀ z : ℤ × ℤ, inner2 w z = c * ((dot m z : ℤ) : ℝ) := by
    have hm0 : ((-v.2, v.1) : ℤ × ℤ) ≠ 0 := by
      simp only [ne_eq, Prod.mk_eq_zero, neg_eq_zero, not_and]
      intro h2 h1
      exact hv (Prod.ext h1 h2)
    rcases lt_or_gt_of_ne htne with hneg | hpos
    · refine ⟨(v.2, -v.1), -t, by linarith, ?_, ?_⟩
      · simp only [ne_eq, Prod.mk_eq_zero, neg_eq_zero, not_and]
        intro h2 h1
        exact hv (Prod.ext h1 h2)
      · intro z
        rw [hform z]
        simp only [dot]
        push_cast
        ring
    · exact ⟨(-v.2, v.1), t, hpos, hm0, hform⟩
  -- Step 4c: read off a primitive direction.
  obtain ⟨ℓ, k, hℓprim, hkpos, hmk⟩ := Nivat.exists_primitive_nsmul_eq hm
  have hdotk : ∀ z : ℤ × ℤ, dot m z = (k : ℤ) * dot ℓ z := by
    intro z
    rw [hmk]
    simp only [dot, Prod.smul_def, smul_eq_mul]
    ring
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hkpos
  have hck : (0 : ℝ) < c * (k : ℝ) := mul_pos hcpos hkR
  have hR : ∀ z : ℤ × ℤ, inner2 w z = (c * (k : ℝ)) * ((dot ℓ z : ℤ) : ℝ) := by
    intro z
    rw [hmform z, hdotk z]
    push_cast
    ring
  have hR' : ∀ z : ℤ × ℤ, inner2 (-w) z = (c * (k : ℝ)) * ((dot (-ℓ) z : ℤ) : ℝ) := by
    intro z
    rw [Nivat.R2.inner2_neg_left, hR z, dot_neg_left]
    push_cast
    ring
  have hside : ∀ z : ℤ × ℤ, z ∈ sideOf w ↔ dot ℓ z ≤ 0 := by
    intro z
    show inner2 w z ≤ 0 ↔ dot ℓ z ≤ 0
    rw [hR z]
    exact mul_cast_nonpos_iff hck _
  have hside' : ∀ z : ℤ × ℤ, z ∈ sideOf (-w) ↔ dot (-ℓ) z ≤ 0 := by
    intro z
    show inner2 (-w) z ≤ 0 ↔ dot (-ℓ) z ≤ 0
    rw [hR' z]
    exact mul_cast_nonpos_iff hck _
  -- Assembly.  `hw₂` supplies the second, independent witness pair.
  obtain ⟨-, x', hx', y', hy', hxy', hagree2⟩ := hw₂
  refine ⟨ℓ, ⟨hℓprim, x, y, hx, hy, hxy, ?_⟩, ⟨x, y, hx, hy, hxy, ?_⟩,
    ⟨x', y', hx', hy', hxy', ?_⟩⟩
  · intro z hz
    exact hagree z ((hside z).mpr hz)
  · intro z hz
    exact hagree z ((hside z).mpr hz)
  · intro z hz
    exact hagree2 z ((hside' z).mpr hz)

end Nivat.ColleStep
