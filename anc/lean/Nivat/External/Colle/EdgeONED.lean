/-
Copyright (c) 2026 Nivat formalisation project. All rights reserved.
-/
import Nivat.External.Colle.L1Assemble

/-!
# The `LatticeEdges` (integer normal) ↔ `R2Orientation` (real normal) bridge

**Diagnosis (2026-09-19, Afill, during the Lemma 2.3 formalisation task).**  Collé's Lemma 2.3
(`b3_colle2.txt:275-277`) is already proved three times in the tree
(`Interfaces.lean:76 not_mem_ONED_of_generatesAt`, `GeneratedHalfPlane.lean:32
eq_of_halfPlane_of_generatesAt`, `R2Orientation.lean:171 two_le_face_card_of_mem_ONED`), all
through `ONED`/`face` at a **real** normal `w : ℝ × ℝ`.  Every leaf that needs it, though, carries
its hypothesis at an **integer** normal (`ℓ : ℤ × ℤ`, `Colle45.NonExpansiveLine` /
`Colle45.IsOneSidedNonexpansive`, `LatticeEdges.lean`'s `IsEdge`/`E`).  The sign-resolution step
that reconciles "`ℓ ⟂ u`, both primitive" with "which of `±perp u` is `ℓ` and which is `-ℓ`" was
being done **twice**, independently:

* `L1Assemble.lean:1766 two_le_min_faces_of_nel` — `det (perp vl) ℓ = 0` laundered by hand via
  `eq_or_eq_neg_of_det_eq_zero`, then `two_le_min_faces_of_ONED` called once per branch.
* `C11Bridge.lean:56 perp_vl_mem_ONED` — the identical `det`/`eq_or_eq_neg_of_det_eq_zero`
  case split, producing the `ONED`-membership pair instead of the face-cardinality conclusion.

This file factors that one case split into a single lemma
(`toReal_perp_mem_ONED_pair`) and supplies both consumer shapes as one-line corollaries
(`toReal_perp_mem_ONED_pair_of_oneSided` for `C11Bridge.perp_vl_mem_ONED`'s shape,
`two_le_min_faces_of_dot_eq_zero` for `L1Assemble.two_le_min_faces_of_nel`'s shape) so both call
sites can shrink to a single `exact`.  **I am not editing either consumer file** (`L1Assemble.lean`
is L1asm's, `C11Bridge.lean` is Cconv's/closed leaf C's) — this file is the plumbing, landing it
is the integrator's or the file owners' call.

Consumers (named per team-lead's redirect, so this is not an orphan per `PROTOCOL.md` §20):
* `Nivat.ColleReg.L1Data.two_le_min_faces_of_nel` (`L1Assemble.lean:1766`)
* `Nivat.ColleReg.C11Bridge.perp_vl_mem_ONED` (`C11Bridge.lean:56`)
-/

set_option autoImplicit false

namespace Nivat.EdgeONED

open Nivat Nivat.LE2 Nivat.KM Nivat.ColleReg

/-- **The shared sign-resolution step.**  `u` primitive, `ℓ` primitive and orthogonal to it
(`det (perp u) ℓ = 0`, i.e. `perp u = ℓ` or `perp u = -ℓ`): both real-normal orientations of
`ℓ` being in `ONED ξ` transports to both real-normal orientations of `perp u`.  This is exactly
the `rcases eq_or_eq_neg_of_det_eq_zero ...` block duplicated in `L1Assemble.lean:1766` and
`C11Bridge.lean:56`. -/
theorem toReal_perp_mem_ONED_pair {ξ : Config ℤ} {u ℓ : ℤ × ℤ}
    (hu : Primitive u) (hℓ : Primitive ℓ) (hdet : det (perp u) ℓ = 0)
    (hpos : toReal ℓ ∈ ONED ξ) (hneg : toReal (-ℓ) ∈ ONED ξ) :
    toReal (perp u) ∈ ONED ξ ∧ toReal (-perp u) ∈ ONED ξ := by
  rcases eq_or_eq_neg_of_det_eq_zero (primitive_perp hu) hℓ hdet with h | h
  · rw [← h]; exact ⟨hpos, hneg⟩
  · have h' : perp u = -ℓ := by rw [h, neg_neg]
    rw [h', neg_neg]; exact ⟨hneg, hpos⟩

/-- `det (perp u) ℓ = 0` from the leaf's native vocabulary `dot ℓ u = 0` — the other half of the
hand-laundering at both call sites. -/
theorem det_perp_eq_zero_of_dot_eq_zero {u ℓ : ℤ × ℤ} (h : dot ℓ u = 0) :
    det (perp u) ℓ = 0 := by
  simp only [det, perp, dot] at h ⊢; linarith

/-- **`C11Bridge.perp_vl_mem_ONED`'s exact shape**, from `IsOneSidedNonexpansive` on both signs
of `ℓ` instead of raw `ONED` membership (bridged internally via `ONEDRational`). Once landed,
`perp_vl_mem_ONED`'s body reduces to `exact toReal_perp_mem_ONED_pair_of_oneSided hvl_prim hℓ_nel.1
hℓ_pos hℓ_neg (det_perp_eq_zero_of_dot_eq_zero hdet_ℓ)`. -/
theorem toReal_perp_mem_ONED_pair_of_oneSided {ξ : Config ℤ} {u ℓ : ℤ × ℤ}
    (hu : Primitive u) (hℓ : Primitive ℓ)
    (hℓ_pos : Colle45.IsOneSidedNonexpansive ξ ℓ)
    (hℓ_neg : Colle45.IsOneSidedNonexpansive ξ (-ℓ))
    (hdet : det (perp u) ℓ = 0) :
    toReal (perp u) ∈ ONED ξ ∧ toReal (-perp u) ∈ ONED ξ :=
  toReal_perp_mem_ONED_pair hu hℓ hdet
    (Nivat.ONEDRational.toReal_mem_ONED_of_isOneSidedNonexpansive hℓ.ne_zero hℓ_pos)
    (Nivat.ONEDRational.toReal_mem_ONED_of_isOneSidedNonexpansive
      (neg_ne_zero.mpr hℓ.ne_zero) hℓ_neg)

/-- Face-cardinality form of `toReal_perp_mem_ONED_pair`, via `two_le_min_faces_of_ONED`. -/
theorem two_le_min_faces_of_det_eq_zero {ξ : Config ℤ} {S₁ : Finset (ℤ × ℤ)}
    (hgen : Nivat.Colle.IsGeneratingSet ξ S₁) {u ℓ : ℤ × ℤ}
    (hu : Primitive u) (hℓ : Primitive ℓ) (hdet : det (perp u) ℓ = 0)
    (hpos : toReal ℓ ∈ ONED ξ) (hneg : toReal (-ℓ) ∈ ONED ξ) :
    2 ≤ min (Nivat.ColleReg.L1Data.topFace true u S₁).card
          (Nivat.ColleReg.L1Data.bottomFace true u S₁).card := by
  obtain ⟨hp, hn⟩ := toReal_perp_mem_ONED_pair hu hℓ hdet hpos hneg
  exact Nivat.ColleReg.L1Data.two_le_min_faces_of_ONED hgen u hp hn

/-- **`L1Assemble.two_le_min_faces_of_nel`'s exact shape**, taking `dot ℓ u = 0` directly (its
`hdet_ℓ`) instead of the pre-laundered `det` form.  Once landed, that theorem's body reduces to
`exact two_le_min_faces_of_dot_eq_zero hgen hℓp hvl hpos hneg hdet_ℓ` (after computing `hpos`,
`hneg` exactly as it already does). -/
theorem two_le_min_faces_of_dot_eq_zero {ξ : Config ℤ} {S₁ : Finset (ℤ × ℤ)}
    (hgen : Nivat.Colle.IsGeneratingSet ξ S₁) {u ℓ : ℤ × ℤ}
    (hu : Primitive u) (hℓ : Primitive ℓ)
    (hpos : toReal ℓ ∈ ONED ξ) (hneg : toReal (-ℓ) ∈ ONED ξ)
    (hdot : dot ℓ u = 0) :
    2 ≤ min (Nivat.ColleReg.L1Data.topFace true u S₁).card
          (Nivat.ColleReg.L1Data.bottomFace true u S₁).card :=
  two_le_min_faces_of_det_eq_zero hgen hu hℓ (det_perp_eq_zero_of_dot_eq_zero hdot) hpos hneg

#print axioms toReal_perp_mem_ONED_pair
#print axioms det_perp_eq_zero_of_dot_eq_zero
#print axioms toReal_perp_mem_ONED_pair_of_oneSided
#print axioms two_le_min_faces_of_det_eq_zero
#print axioms two_le_min_faces_of_dot_eq_zero

end Nivat.EdgeONED
