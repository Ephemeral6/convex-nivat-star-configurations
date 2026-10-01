/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.RegionEdges

/-!
# `semiInfUnique` is a theorem, not an input

`RegionEdges.lean:553` (`isRegion_of_two_semiInf`) still takes

    huniq : ∀ k, IsSemiInfEdge R k → k = n ∨ k = n'

as a hypothesis, and its own `Status` block (`RegionEdges.lean:763-765`) records that
`IsRegion` can be built "without the fields `posArea`, `edgesFinite`, `precedes`" —
i.e. `semiInfUnique` was still required from the caller.

It is not required.  The proof of `finite_E_of_two_semiInf` (`RegionEdges.lean:285`)
already contains the whole argument: any edge normal strictly between `n` and `n'` in
the cyclic order has its face trapped in the finite box of `finite_of_dot_bounded`
(`:109`) by `face_subset_box` (`:237`).  A trapped face is finite, hence not
semi-infinite.  So the only semi-infinite edges are `n` and `n'`.

This matters for `isRegion_inter_halfPlaneLE`: `semiInfUnique` for the cut region was
the field with a known hazard (`not_E_inter_subset`, `RegionEdges.lean:740`, shows
`E(R ∩ ℋ) ⊆ E R ∪ {k}` is false).  With `semiInfUnique_of_two_semiInf` that hazard is
routed around entirely — the cut region never has to be compared edge-by-edge with `R`.
-/

namespace Nivat.LE2

open Nivat

/-- **The two semi-infinite edges are the only ones.**  No convexity, closedness or
boundedness hypothesis is used — exactly as for `finite_E_of_two_semiInf`. -/
theorem semiInfUnique_of_two_semiInf {R : Set (ℤ × ℤ)} {n n' : ℤ × ℤ}
    (hn : IsSemiInfEdge R n) (hn' : IsSemiInfEdge R n') (hD : 0 < det n n')
    (k : ℤ × ℤ) (hk : IsSemiInfEdge R k) : k = n ∨ k = n' := by
  by_cases h1 : k = n
  · exact Or.inl h1
  by_cases h2 : k = n'
  · exact Or.inr h2
  exfalso
  obtain ⟨hnE, hinf⟩ := hn
  obtain ⟨hn'E, hinf'⟩ := hn'
  obtain ⟨a, ha⟩ := hinf.nonempty
  obtain ⟨a', ha'⟩ := hinf'.nonempty
  obtain ⟨hB, hA⟩ := det_nonneg_of_semiInf hD hinf hinf' hk.2.nonempty
  have hA0 : det k n' ≠ 0 := fun h => h2 (eq_right_of_det_eq_zero hD hk.1.1 hn'E.1 hB h)
  have hB0 : det n k ≠ 0 := fun h => h1 (eq_left_of_det_eq_zero hD hnE.1 hk.1.1 hA h)
  exact hk.2 ((finite_of_dot_bounded hD.ne' _ _ _ _).subset
    (face_subset_box ha ha' (lt_of_le_of_ne hA (Ne.symm hA0))
      (lt_of_le_of_ne hB (Ne.symm hB0)) hD))

/-- **Colle, Definition 3.1, as a constructor — final form.**  To exhibit an
`(ℓ,ℓ')`-region one has to produce exactly three things: lattice convexity, and the two
semi-infinite edges in the right cyclic order.  Everything else is a theorem. -/
theorem isRegion_of_two_semiInf' {R : Set (ℤ × ℤ)} {n n' : ℤ × ℤ}
    (hlc : IsLatticeConvexRegion R) (hn : IsSemiInfEdge R n) (hn' : IsSemiInfEdge R n')
    (hD : 0 < det n n') : IsRegion R n n' :=
  isRegion_of_two_semiInf hlc hn hn' hD (semiInfUnique_of_two_semiInf hn hn' hD)

/-- Non-vacuity: rebuilds `isRegion_quad` from three inputs. -/
theorem isRegion_quad'' : IsRegion quad (-1, 0) (0, -1) :=
  isRegion_of_two_semiInf' isLatticeConvexRegion_quad
    ⟨by rw [E_quad]; simp, infinite_face_quad_left⟩
    ⟨by rw [E_quad]; simp, infinite_face_quad_bot⟩ (by decide)

end Nivat.LE2

#print axioms Nivat.LE2.semiInfUnique_of_two_semiInf
#print axioms Nivat.LE2.isRegion_of_two_semiInf'
#print axioms Nivat.LE2.isRegion_quad''
