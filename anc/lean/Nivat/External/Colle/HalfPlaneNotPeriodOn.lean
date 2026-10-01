/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.Interfaces
import Nivat.External.Colle.Lemma41
import Nivat.External.Colle.Claim414Ell
import Nivat.External.Colle.PeriodTransport
import Nivat.Defs.Orbit

set_option autoImplicit false

/-!
# Half-plane periodicity implies not `PeriodOn`

Paper reference: `b3_colle2.txt:810-814`.

Collé writes: "$(T^u η)|_{\mathcal{H}(\ell_{\iota-m})}$ does not have a period parallel to
$\ell_{\iota-m}$ or $\ell = \ell_\iota$, since otherwise Proposition 2.12 would imply that
$T^u η$ is periodic."

This theorem establishes that when a half-plane (characterized by `{z | c ≤ dot w z} ⊆ R`)
supports local periodicity, then global `PeriodOn` over `R` cannot hold, because Proposition 2.12
(instantiated as `exists_zsmul_mem_Per_of_halfPlane_period`) would produce a nonzero period of
`T e ξ`, contradicting minimality.
-/

open Nivat

namespace Nivat.HalfPlaneNotPeriodOn

/-- 原文：b3_colle2.txt:810-814
If a half-plane `{z | c ≤ dot w z}` is contained in `R`, and `u` is orthogonal to `w`,
then `T e ξ` cannot satisfy `PeriodOn` over `R` with period `u`, because that would make
`T e ξ` globally periodic (via Proposition 2.12), contradicting minimality of `ξ`. -/
theorem not_periodOn_of_halfPlane_subset {ξ : Config ℤ} (hξ : IsMinimalCounterexample ξ)
    (e : ℤ × ℤ) {R : Set (ℤ × ℤ)} {w u : ℤ × ℤ} (hw : w ≠ 0) (hu : u ≠ 0)
    (hwu : LE2.dot w u = 0) {c : ℤ}
    (hR : {z : ℤ × ℤ | c ≤ LE2.dot w z} ⊆ R) :
    ¬ Colle41.PeriodOn (T e ξ) R u := by
  intro hper
  -- Step 1: `y := T e ξ` is in the orbit closure
  set y := T e ξ
  have hy : y ∈ orbitClosure ξ := T_mem_orbitClosure ξ e

  -- Step 2: On the half-plane, `PeriodOn` gives local periodicity
  have hlocal : ∀ z, c ≤ LE2.dot w z → y (z + u) = y z := by
    intro z hz
    have hz_in : z ∈ R := hR hz
    have hzu_calc : LE2.dot w (z + u) = LE2.dot w z + LE2.dot w u := by
      simp [LE2.dot]
      ring
    rw [hwu] at hzu_calc
    simp at hzu_calc
    have hzu_in : z + u ∈ R := hR (by simp [hzu_calc]; exact hz)
    exact hper z hz_in hzu_in

  -- Step 3: Apply Proposition 2.12 (instantiated)
  obtain ⟨k, hk_ne, hk_mem⟩ :=
    Claim414.exists_zsmul_mem_Per_of_halfPlane_period hξ hy hw hu hwu hlocal

  -- Step 4: This gives a nonzero period of `y`
  have hku_ne : k • u ≠ 0 := by
    intro h
    cases smul_eq_zero.mp h with
    | inl hk => exact hk_ne hk
    | inr hu' => exact hu hu'
  have hper_y : IsPeriodic y := ⟨k • u, hk_mem, hku_ne⟩

  -- Step 5: Contradiction with minimality
  have hξ_not_per : ¬ IsPeriodic ξ := hξ.1.2.2.1
  have hy_not_per : ¬ IsPeriodic (T e ξ) :=
    CosetPigeonhole.not_isPeriodic_T_of_not_isPeriodic e hξ_not_per
  exact hy_not_per hper_y

#print axioms not_periodOn_of_halfPlane_subset

end Nivat.HalfPlaneNotPeriodOn
