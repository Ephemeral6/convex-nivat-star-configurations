/-
Copyright (c) 2026. Released under Apache 2.0 license.
Authors: lane-tower3
-/
import Nivat.External.Colle.L1Region
import Nivat.External.Colle.RegionSweep

/-!
# `hbase` — generic reduction of `cut Rinf m lev 0` to the previous tower level

`exists_cutResidualR_of_claim46`'s tower obligation (`RegionSteps.lean:1748-1749`) asks for

    ∀ lev : ℕ → ℤ, lev 0 = b₀ →
      PeriodOn (T e ξ) (cut Rinf m lev 0) (c • vl)

**Correction (2026-09-23, lane-tower3):** an earlier version of this file (`TowerHBase.lean`)
wrongly reduced this to bare periodicity of `Rinf` itself, via `Rinf ⊆ halfPlaneGE m b₀`. That
hypothesis can never hold together with `hunb` (`RegionSteps.lean:1747`, `dot m` unbounded
*below* on `Rinf`), and it would also directly contradict `hinf` (`Rinf` itself is *not*
periodic). Per `RegionSteps.lean:1602-1613`'s own account, the real mechanism is: `Rinf` is the
outer tower's non-periodic level `R (I+1) = sweep C w'` for the *previous* level `C := R I`
(periodic, `RegionSteps.lean:1607-1609`), swept along a direction `w'` with `dot m w' < 0`
(the orientation-free descent fact, `TowerPackage.lean`'s `dot_m_next_neg`). Since sweeping
along a strictly `m`-decreasing direction can only ever *lower* `dot m`, the top `m`-level of
the swept set equals the top `m`-level of `C` — so `cut Rinf m lev 0 ⊆ C`, and periodicity
transfers down via `PeriodOn.mono`. This file makes that reduction generic and
indexing-independent.
-/

set_option autoImplicit false

namespace Nivat.ColleReg

open Nivat Nivat.LE2 Nivat.L1Region Nivat.RegionSweep

/-- If `b₀` is the maximum `dot m`-value on `C`, and `w'` strictly decreases `dot m`
(`dot m w' < 0`), then intersecting `sweep C w'` with the `b₀`-level half-plane recovers
exactly `C`'s own top level: any `t ≥ 1` step along `w'` strictly drops below `b₀`. -/
theorem sweep_inter_halfPlaneGE_eq_of_max {C : Set (ℤ × ℤ)} {m w' : ℤ × ℤ} {b₀ : ℤ}
    (hmax : ∀ z ∈ C, dot m z ≤ b₀) (hneg : dot m w' < 0) :
    sweep C w' ∩ halfPlaneGE m b₀ = C ∩ halfPlaneGE m b₀ := by
  apply Set.eq_of_subset_of_subset
  · rintro z ⟨⟨g, hg, t, rfl⟩, hz⟩
    simp only [halfPlaneGE, Set.mem_ofPred_eq] at hz ⊢
    have hgt : dot m (g + (t : ℤ) • w') = dot m g + (t : ℤ) * dot m w' := by
      rw [dot_add]
      congr 1
      cases m; cases w'
      simp only [dot, Prod.smul_mk, smul_eq_mul]
      ring
    rw [hgt] at hz
    have hg_le := hmax g hg
    have ht0 : t = 0 := by
      by_contra ht
      have ht1 : (1 : ℤ) ≤ (t : ℤ) := by
        have : 1 ≤ t := Nat.one_le_iff_ne_zero.mpr ht
        exact_mod_cast this
      nlinarith
    subst ht0
    simp only [Nat.cast_zero, zero_smul, add_zero, zero_mul] at hz ⊢
    exact ⟨hg, hz⟩
  · rintro z ⟨hzC, hz⟩
    exact ⟨subset_sweep C w' hzC, hz⟩

/-- **`hbase` from the previous tower level's periodicity.** The generic reduction: if `C` is
`(c • vl)`-periodic, `b₀` is `C`'s `m`-support maximum, `Rinf = sweep C w'` for some `w'` with
`dot m w' < 0`, then the `cut`-indexed `hbase` obligation holds for every `lev` starting at
`b₀`. -/
theorem hbase_of_prev_level_periodOn {A : Type*} {ξ : Config A} {e : ℤ × ℤ}
    {C Rinf : Set (ℤ × ℤ)} {m vl w' : ℤ × ℤ} {c : ℤ} {b₀ : ℤ}
    (hRinf : Rinf = sweep C w') (hmax : ∀ z ∈ C, dot m z ≤ b₀) (hneg : dot m w' < 0)
    (hper : Nivat.Colle41.PeriodOn (T e ξ) C (c • vl)) :
    ∀ lev : ℕ → ℤ, lev 0 = b₀ →
      Nivat.Colle41.PeriodOn (T e ξ) (cut Rinf m lev 0) (c • vl) := by
  intro lev hlev0
  have hceq : cut Rinf m lev 0 = C ∩ halfPlaneGE m b₀ := by
    show Rinf ∩ halfPlaneGE m (lev 0) = _
    rw [hlev0, hRinf]
    exact sweep_inter_halfPlaneGE_eq_of_max hmax hneg
  rw [hceq]
  exact Nivat.Colle41.PeriodOn.mono (Set.inter_subset_left) hper

/-- **`h0` from the previous tower level's attained maximum.** If some point of `C` attains
`dot m` value `b₀`, that same point witnesses `h0` for `Rinf = sweep C w'` — `C ⊆ sweep C w'`
via `subset_sweep`, with `t = 0`. Paired with `hmax` above, this is exactly Collé's
`:818` "`d_0` is the `m`-height of `𝓡_I`'s own support line", attained (not just an upper bound)
because the support line of a lattice-convex region is attained on its finite generating set. -/
theorem h0_of_prev_level_attained {C Rinf : Set (ℤ × ℤ)} {m w' : ℤ × ℤ} {b₀ : ℤ}
    (hRinf : Rinf = sweep C w') (hattain : ∃ z ∈ C, dot m z = b₀) :
    ∃ z ∈ Rinf, dot m z = b₀ := by
  obtain ⟨z, hzC, hz⟩ := hattain
  exact ⟨z, hRinf ▸ subset_sweep C w' hzC, hz⟩

end Nivat.ColleReg

#print axioms Nivat.ColleReg.sweep_inter_halfPlaneGE_eq_of_max
#print axioms Nivat.ColleReg.hbase_of_prev_level_periodOn
#print axioms Nivat.ColleReg.h0_of_prev_level_attained
