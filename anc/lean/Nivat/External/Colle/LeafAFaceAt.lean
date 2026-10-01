/-
Lane leafa, 2026-09-22.  Landed in `Nivat/` 2026-09-22 after `check1.sh` EXIT=0, 0 sorry, axioms `[propext, Classical.choice, Quot.sound]`.

**Purpose**: `DecompDataZ.exists_faceBlock_at` — the prescribed-normal analogue of
`DecompDataZ.exists_faceBlock` (`ANormal.lean:634`), which always lets `d.exists_nJ_vJ` pick
its own edge normal transverse to `p`.  Team-lead's 2026-09-22 ruling on `LeafAAssemble.lean`'s
J-package requires `nJ := -J`, `vJ := v`, `F : FaceBlock S nJ vJ` all built from the SAME `J`
lane-recp's `exists_J_stable` produces — so the face block has to be constructed at a normal
the caller supplies (`-J`), not one `exists_faceBlock` chooses internally.

Recipe (team-lead): reuse `exists_lex_max`/`exists_lex_max'`/`exists_r_edge`/`exists_edge'`/
`r_pos_of_mem_E` (`FaceData.lean`, `ANormal.lean:196` — all already generic in the normal/
direction pair, 0 sorry, already in the main-tree import graph via `ANormal.lean`), with
`v := dir ν` (`LatticeEdges.lean:248`) for the orthogonal direction: `prim_dir` (`CyrKra224.lean
:1150`) gives `Primitive v` from `Primitive ν`, `dot_dir` (`LatticeEdges.lean:250`) gives
`dot ν v = 0` for free, and the antipodal membership `-ν ∈ E ↑d.Sphi` (needed by
`r_pos_of_mem_E`) is free from `ν ∈ E ↑d.Sphi` via `DecompData.Sphi_negSymm`
(`DecompData.lean:406`) — no need to thread it as a separate hypothesis at all, unlike the
`exists_faceBlock` design (which had it as an output, not an input, because there it came from
`d.exists_nJ_vJ`'s own construction).  `det p v ≠ 0` (`ofPartsExhaustsInter`'s `hpvJ` binder)
follows from `dot ν p ≠ 0` (the caller's `hνp`) by the identity `det p (dir ν) = dot p ν`
(unfold `det`/`dir`, `ring`), not by lemma search.
-/
import Nivat.External.Colle.ANormal
import Nivat.External.Colle.CyrKra224

set_option autoImplicit false

namespace Nivat.Colle35

open Nivat Nivat.LE2

/-- `det p (dir ν) = dot p ν`, by direct unfolding (`det a b = a.1*b.2 - a.2*b.1`,
`dir n = (-n.2, n.1)`). -/
theorem det_dir_eq_dot (p ν : ℤ × ℤ) : det p (dir ν) = dot p ν := by
  simp only [det, dir, dot]
  ring

/-- **The face block of `S_φ` at a prescribed edge normal `ν`, transverse to `p`.**

Unlike `DecompDataZ.exists_faceBlock` (`ANormal.lean:634`), which lets `d.exists_nJ_vJ` pick
its own normal, this constructs `FaceBlock d.Sphi ν v` for a `ν` the *caller* supplies —
needed so `nJ`, `vJ`, and `F` in `ChainDataGeom.ofPartsExhaustsInter` can all be built from the
same `J` that lane-recp's `exists_J_stable`/`exists_J_stable_cw` produce (team-lead's
2026-09-22 ruling: "nJ/vJ/F must all come from the SAME J"). -/
theorem DecompDataZ.exists_faceBlock_at {ξ : Config ℤ} (d : DecompDataZ ξ)
    {ν p : ℤ × ℤ} (hν : ν ∈ E (↑d.Sphi : Set (ℤ × ℤ))) (hνp : dot ν p ≠ 0) :
    ∃ (v : ℤ × ℤ) (F : FaceBlock d.Sphi ν v),
      Primitive v ∧ v ≠ 0 ∧ dot ν v = 0 ∧ det p v ≠ 0 ∧
      F.a' = F.a + (F.r : ℤ) • v ∧ 0 < F.r ∧ F.a ≠ F.a' := by
  have hνprimP : Prim ν := hν.1
  have hνprim : Primitive ν := Nivat.LE2.prim_iff_primitive.mp hνprimP
  have hνne : ν ≠ 0 := hνprim.ne_zero
  have hνneg : -ν ∈ E (↑d.Sphi : Set (ℤ × ℤ)) := (Sphi_negSymm d.toDecompData ν).mp hν
  set v : ℤ × ℤ := dir ν with hv_def
  have hvprim : Primitive v := Nivat.CK224.prim_dir hνprimP
  have hvne : v ≠ 0 := hvprim.ne_zero
  have hdotnv : dot ν v = 0 := dot_dir ν
  have hdetpv : det p v ≠ 0 := by
    rw [hv_def, det_dir_eq_dot, dot_comm]
    exact hνp
  obtain ⟨a, ha, hlex⟩ := exists_lex_max d.Sphi d.Sphi_nonempty hνne hvne hdotnv
  obtain ⟨a', ha', hlex'⟩ := exists_lex_max' d.Sphi d.Sphi_nonempty hνne hvne hdotnv
  obtain ⟨r, hr_eq, hedge⟩ := exists_r_edge hνne ha ha' hvprim hdotnv hlex hlex'
  have hedge' := exists_edge' hdotnv hr_eq hedge
  have hrpos : 0 < r := r_pos_of_mem_E ha hνneg hedge
  have hane : a ≠ a' := by
    intro h
    have hrne : (r : ℤ) ≠ 0 := by exact_mod_cast hrpos.ne'
    have h2 : a = a + (r : ℤ) • v := h.trans hr_eq
    have h3 : a + (0 : ℤ × ℤ) = a + (r : ℤ) • v := by rw [add_zero]; exact h2
    exact zsmul_ne_zero_of_ne_zero hrne hvne (add_left_cancel h3).symm
  exact ⟨v, ⟨a, a', r, d.Sphi_conv, ha, ha', hlex, hlex', hedge, hedge', hdotnv⟩,
    hvprim, hvne, hdotnv, hdetpv, hr_eq, hrpos, hane⟩

end Nivat.Colle35

#print axioms Nivat.Colle35.DecompDataZ.exists_faceBlock_at
