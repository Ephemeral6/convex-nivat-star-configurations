/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.PolyChainSum

/-!
# `0 ≤ D` from a window's fan-adjacency data (lane-hole3-nlmax)

Consumer: `tmp/wip/LeafAAssemble.lean` (ccw branch), which `obtain`s exactly the hypotheses
below, verbatim named, at two points — `Nivat.LeafAJSelect.exists_nprevJ_vJ1` giving
`hnprevE, hnprevdet, hnprevempty, hnprevor` and `Nivat.LeafAShellNNext.exists_w_hsweepW` giving
`hνJ1E, hνJ1pos, hνJ1empty, hνJ1or` — and needs `0 ≤ det nprevJ νJ1` to close the analogous `hD`
binder of `shellEnv_of_faceEndpoints` (`tmp/wip/lane-leafa-shell-shellenv.lean:5651`).

Route: `b3_colle2.txt:432` (Lemma 3.5(i), the window conclusion), `:498-506` (`J`-selection,
already transcribed by `exists_J_stable`), `:764` (fan-adjacency, already transcribed by
`exists_fan_pred` / `exists_nnextJ`).  No new `Prop` is introduced; this file wires the
*output shapes* of three already-delivered mainline theorems together.

**Correction (round 177, lane-leafa-shell):** an earlier `∃`-shaped version of this lemma
could not be applied at the call site above, because the consumer already has concrete
`nprevJ`/`νJ1` from its own `obtain`s, and a freshly-`∃`-constructed pair is not
definitionally equal to them.  The `∀`-form below consumes the consumer's hypotheses as-is.
-/

set_option autoImplicit false

namespace Nivat.LaneHole3Nlmax

open Nivat Nivat.LE2 Nivat.PolyChainSum

variable {Sphi : Finset (ℤ × ℤ)}

/-- `dot (dir n) x = det n x`, pure algebraic unfolding.  Named `_left` to avoid colliding with
the pre-existing (argument-flipped, `dot x (dir ν) = det ν x`) `dot_dir_eq_det` already present
three times in mainline (`HsuppAssemble.lean:275`, `HsuppCaseCW.lean:242`,
`HsuppRoomCone.lean:149`) — same identity up to `dot`'s symmetry, not reused here to keep this
file import-independent of those three. -/
theorem dot_dir_eq_det_left (n x : ℤ × ℤ) : dot (dir n) x = det n x := by
  simp only [dot, dir, det]; ring

/-- `det u (-v) = -det u v`. -/
theorem det_neg_right' (u v : ℤ × ℤ) : det u (-v) = -det u v := by
  simp only [det, Prod.fst_neg, Prod.snd_neg]; ring

/-- **`0 ≤ D`, the `∀`-form matching `LeafAAssemble.lean`'s existing `obtain` output.**
Consumes `hnprevor`/`hνJ1or`/`hℓJ`/`hnprevdet`/`hνJ1pos` (the remaining hypotheses are accepted
but unused, to keep the signature aligned with the caller's full tuple). -/
theorem D_nonneg_of_window {ℓ J nprevJ νJ1 : ℤ × ℤ}
    (hℓE : ℓ ∈ E (↑Sphi : Set (ℤ × ℤ))) (hnegℓE : (-ℓ) ∈ E (↑Sphi : Set (ℤ × ℤ)))
    (hJE : J ∈ E (↑Sphi : Set (ℤ × ℤ))) (hℓJ : 0 < det ℓ J)
    (hnprevE : nprevJ ∈ E (↑Sphi : Set (ℤ × ℤ)))
    (hnprevdet : 0 < det nprevJ J)
    (hnprevempty : Nivat.PolyChainSum.Arc (Sphi.finite_toSet) nprevJ J = ∅)
    (hnprevor : nprevJ = ℓ ∨ nprevJ ∈ Nivat.PolyChainSum.Arc (Sphi.finite_toSet) ℓ J)
    (hνJ1E : νJ1 ∈ E (↑Sphi : Set (ℤ × ℤ)))
    (hνJ1pos : 0 < det J νJ1)
    (hνJ1empty : Nivat.PolyChainSum.Arc (Sphi.finite_toSet) J νJ1 = ∅)
    (hνJ1or : νJ1 = -ℓ ∨ νJ1 ∈ Nivat.PolyChainSum.Arc (Sphi.finite_toSet) J (-ℓ)) :
    0 ≤ det nprevJ νJ1 := by
  have hWprev : 0 ≤ det ℓ nprevJ := by
    rcases hnprevor with rfl | hmem
    · simp [det_self]
    · exact (mem_Arc.mp hmem).2.1.le
  have hWnext : 0 ≤ det ℓ νJ1 := by
    rcases hνJ1or with rfl | hmem
    · have : det ℓ (-ℓ) = -det ℓ ℓ := det_neg_right' ℓ ℓ
      simp [det_self] at this; omega
    · have h2 : 0 < det νJ1 (-ℓ) := (mem_Arc.mp hmem).2.2
      have h3 : det νJ1 (-ℓ) = -det νJ1 ℓ := det_neg_right' νJ1 ℓ
      have h4 : det νJ1 ℓ = -det ℓ νJ1 := det_skew νJ1 ℓ
      omega
  set e := dir ℓ with he_def
  have ha : 0 ≤ dot e nprevJ := by rw [he_def, dot_dir_eq_det_left]; exact hWprev
  have hb : 0 < dot e J := by rw [he_def, dot_dir_eq_det_left]; exact hℓJ
  have hc : 0 ≤ dot e νJ1 := by rw [he_def, dot_dir_eq_det_left]; exact hWnext
  have hid : dot e J * det nprevJ νJ1
      = dot e nprevJ * det J νJ1 + dot e νJ1 * det nprevJ J := by
    simp only [dot, det]; ring
  by_contra hcon
  push_neg at hcon
  have h1 : dot e J * det nprevJ νJ1 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hb.le hcon.le
  nlinarith [mul_nonneg ha hνJ1pos.le, mul_nonneg hc hnprevdet.le]

end Nivat.LaneHole3Nlmax

#print axioms Nivat.LaneHole3Nlmax.dot_dir_eq_det_left
#print axioms Nivat.LaneHole3Nlmax.det_neg_right'
#print axioms Nivat.LaneHole3Nlmax.D_nonneg_of_window
