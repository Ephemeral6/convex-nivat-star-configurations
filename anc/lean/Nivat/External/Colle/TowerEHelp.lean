/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.ZonoEdgeGen
import Nivat.External.Colle.LatticeEdges

/-!
# Exact characterization of `E (zonoF univ h)` (lane-hsupp helping lane-tower, 2026-09-22)

`ZonoEdgeGen.lean` only lands the two one-directional halves (`face_zonoF_eq`: every edge
normal is orthogonal to a unique generator; `mem_E_zonoF`: every `±genPerp' (h j)` is an edge
normal). Neither states the full `iff`. Lane-tower's `wtower`/`hadjB` base case (via
`TowerConstruct.lean`) needs the full characterization of `E B` (`= E ↑d.Sphi = E (zonoF univ
d.h)` via `E_Sphi_eq_E_zonoF`) to know `E B` has *no extra elements* beyond the `±genPerp'`
family. This file supplies that `iff`, purely by combining the two existing halves with
`eq_or_neg_of_prim_of_det_eq_zero` (`LatticeEdges.lean:133`) and `at_most_one_orthogonal`
(`ZonoEdgeGen.lean:82`) — no new geometry.
-/

namespace Nivat.LE2

open Nivat Nivat.Colle Finset Classical Pointwise

variable {m : ℕ}

/-- **Exact characterization**: `ν` is an edge normal of the zonotope `zonoF univ h` iff it is
`± genPerp' (h j)` for some generator `j`. The forward direction is the new content: from
`face_zonoF_eq` get the (unique) `j` with `dot ν (h j) = 0`; `ν` is `Prim` (from `mem_E_iff`)
and so is `genPerp' (h j)` (`genPerp'_prim`), both orthogonal to the same nonzero `h j`, so
`det ν (genPerp' (h j)) = 0` and `eq_or_neg_of_prim_of_det_eq_zero` finishes. -/
theorem E_zonoF_eq_genPerp_set (h : Fin m → ℤ × ℤ) (h_ne : ∀ j, h j ≠ 0)
    (h_dir : ∀ j k, j ≠ k → det (h j) (h k) ≠ 0) (ν : ℤ × ℤ) :
    ν ∈ E (↑(zonoF Finset.univ h) : Set (ℤ × ℤ)) ↔
      ∃ j : Fin m, ν = genPerp' (h j) ∨ ν = -genPerp' (h j) := by
  constructor
  · intro hν
    obtain ⟨j, hνj, -⟩ := face_zonoF_eq h h_ne h_dir ν hν
    have hνprim : Prim ν := (mem_E_iff.mp hν).1
    have hgprim : Prim (genPerp' (h j)) := genPerp'_prim (h_ne j)
    have hgorth : dot (h j) (genPerp' (h j)) = 0 := dot_genPerp' (h_ne j)
    have hdet : det ν (genPerp' (h j)) = 0 :=
      det_eq_zero_of_dot_eq_zero (h_ne j) (by rw [dot_comm]; exact hνj) hgorth
    -- `eq_or_neg_of_prim_of_det_eq_zero` wants `det n m = 0` with `n := genPerp' (h j)`.
    have hdet' : det (genPerp' (h j)) ν = 0 := by rw [det_skew]; omega
    rcases eq_or_neg_of_prim_of_det_eq_zero hgprim hνprim hdet' with heq | heq
    · exact ⟨j, Or.inl heq⟩
    · exact ⟨j, Or.inr heq⟩
  · rintro ⟨j, rfl | rfl⟩
    · exact (mem_E_zonoF h h_ne h_dir j).1
    · exact (mem_E_zonoF h h_ne h_dir j).2

#print axioms Nivat.LE2.E_zonoF_eq_genPerp_set

end Nivat.LE2
