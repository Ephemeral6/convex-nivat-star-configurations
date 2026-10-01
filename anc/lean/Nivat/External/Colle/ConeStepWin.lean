/-
Copyright (c) 2026 Theorem-proving agent Hcone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hcone
-/
import Nivat.External.Colle.ConeRegion
import Nivat.External.Colle.EnvFit

set_option autoImplicit false

/-!
# Cone step for hole 5 of RegionSteps.lean

原文：b3_colle2.txt:792-804 — the inductive extension of periodicity from `H_B(ℓ)` to the
full region `𝓡_{ι-1}`.

The key geometric fact: when `w ∈ coneRegion B vl u'` and `dot nℓ w < cz`, the point `w` is
"below the cut level `cz`". Translating by `z - a₀` for `z ∈ Sw.erase a₀` shifts the point,
and if `dot nℓ (z + (w - a₀)) < cz` still holds (i.e., the translated point remains below
the cut), then the result must still lie in the cone.

The proof uses:
- `mem_coneRegion_iff_coords`: membership criterion in dual coordinates
- The hypothesis `hvlmin` pins the window to the cone's corner for the vl-coordinate
- The u'-coordinate constraint comes from `hcz` and `hzw_below` via the identity
  `uCoord u' vl 0 x = -dot nℓ x`

## Main theorem

`hcone_coneStep_of_window`: if `w ∈ coneRegion B vl u'` is below the cut (`dot nℓ w < cz`),
and for `z ∈ Sw.erase a₀` the translated point `z + (w - a₀)` is also below the cut, then
`z + (w - a₀) ∈ coneRegion B vl u'`.
-/

namespace Nivat.ConeStepWin

open Nivat Nivat.LE2 Nivat.ColleReg Nivat.ConeRegion Nivat.L1Line0

/-- **Hole 5 of `RegionSteps.lean:1961`** — the cone step for window translation.

原文：b3_colle2.txt:792-804 — extending periodicity along the region by induction.

When `w` is in the cone and below the cut level, and translating by `z - a₀` (for `z` in the
window minus the anchor) keeps the result below the cut, the translated point remains in the cone.

The hypothesis `hvlmin` pins the window to the cone's corner by requiring all window points
have non-negative `vl`-coordinate relative to the anchor `a₀`. The u'-coordinate constraint
is free from `hcz` and `hzw_below`. -/
theorem hcone_coneStep_of_window
    {B : Set (ℤ × ℤ)} {Sw : Finset (ℤ × ℤ)} {vl u' nℓ a₀ w z : ℤ × ℤ} {cz : ℤ}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hperp : dot nℓ vl = 0)
    (hnu : dot nℓ u' = -1)
    (hcz : ∀ b ∈ B, cz ≤ dot nℓ b)
    (hvlmin : ∀ z ∈ Sw, 0 ≤ dot (expNormal u' vl) (z - a₀))
    (hw : w ∈ coneRegion B vl u')
    (_hw_below : dot nℓ w < cz)
    (hz : z ∈ Sw.erase a₀)
    (hzw_below : dot nℓ (z + (w - a₀)) < cz) :
    z + (w - a₀) ∈ coneRegion B vl u' := by
  -- Use the coordinate criterion for cone membership
  rw [Nivat.EnvFit.mem_coneRegion_iff_coords hunimod] at hw ⊢
  obtain ⟨b, hb, hψ_w, _⟩ := hw
  -- Extract `z ∈ Sw` from `z ∈ Sw.erase a₀`
  have hz_mem : z ∈ Sw := Finset.mem_of_mem_erase hz
  -- From `hvlmin`, get the vl-coordinate constraint: `0 ≤ dot (expNormal u' vl) (z - a₀)`
  have hvl_nonneg : 0 ≤ dot (expNormal u' vl) (z - a₀) := hvlmin z hz_mem
  -- Witness: use the same base point `b ∈ B` that witnesses `w`'s cone membership
  refine ⟨b, hb, ?_, ?_⟩
  · -- First coordinate (vl-component): `dot (expNormal u' vl) b ≤ dot (expNormal u' vl) (z + (w - a₀))`
    calc dot (expNormal u' vl) b
        ≤ dot (expNormal u' vl) w := hψ_w
      _ ≤ dot (expNormal u' vl) (z - a₀) + dot (expNormal u' vl) w := by omega
      _ = dot (expNormal u' vl) ((z - a₀) + w) := by rw [← dot_add]
      _ = dot (expNormal u' vl) (z + (w - a₀)) := by ring_nf
  · -- Second coordinate (u'-component): free from hcz + hzw_below, no window hypothesis
    have hb' : uCoord u' vl 0 b = - dot nℓ b := by
      rw [Nivat.EnvFit.uCoord_eq_neg_dot_of_basis (u' := u') (vl := vl) hunimod hperp hnu,
        sub_zero]
    have ht' : uCoord u' vl 0 (z + (w - a₀)) = - dot nℓ (z + (w - a₀)) := by
      rw [Nivat.EnvFit.uCoord_eq_neg_dot_of_basis (u' := u') (vl := vl) hunimod hperp hnu,
        sub_zero]
    have hbz := hcz b hb
    omega

#print axioms hcone_coneStep_of_window

end Nivat.ConeStepWin
