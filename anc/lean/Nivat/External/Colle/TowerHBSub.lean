/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.TowerPackage

/-!
# `B ⊆ tower (coneRegion B vl u') w n` — extracted from `tower_top_contains_halfPlane`'s
inline `hBR` step (`Nivat.ColleReg.tower_top_contains_halfPlane`,
`Nivat/External/Colle/TowerPackage.lean:156-165`).

Lane `lane-hroom-close`, 2026-09-22. This is `hB_sub` (`Nivat.TowerRoom.hroomT_of_wedge_and_cont`'s
first hypothesis, `TowerRoom.lean:69`) instantiated at `towerI := tower (coneRegion B vl u') w n`
for the specific `n` chosen by the assembly (whatever `I` turns out to be) — proved here for
every `n`, so the caller does not need to case on which `n` it picked.

`B_subset_tower`: 0 sorry, axioms `[propext, Quot.sound]`.
-/

set_option autoImplicit false

namespace Nivat.ColleReg

open Nivat Nivat.Colle41 Nivat.LE2 Nivat.ConeRegion

/-- `B` embeds in `coneRegion B vl u'` at `s = t = 0`, hence in every tower level built on it
(the tower is monotone: `tower R w 0 = R`, and each step is a `sweep`, which only adds points). -/
theorem B_subset_tower {B : Set (ℤ × ℤ)} {vl u' : ℤ × ℤ} (w : ℕ → ℤ × ℤ) (n : ℕ) :
    B ⊆ tower (coneRegion B vl u') w n := by
  intro z hz
  have h0 : z ∈ coneRegion B vl u' := mem_coneRegion_iff.mpr ⟨z, hz, 0, 0, by simp⟩
  clear hz
  induction n with
  | zero => exact h0
  | succ m ih =>
    simp only [tower]
    exact ⟨z, ih, 0, by simp⟩

end Nivat.ColleReg
