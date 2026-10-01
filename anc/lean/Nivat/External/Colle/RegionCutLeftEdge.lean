/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.RegionEdges

/-!
# The `ℓ`-edge survives a cut parallel to the `ℓ'`-edge

Half of `isRegion_inter_halfPlaneLE`.  Cutting an `(n,n')`-region `R` by
`halfPlaneLE n' c` (outer normal `n'`; the orientation is forced, see
`RegionHalfPlaneOrientation.lean`) leaves the `n`-edge semi-infinite.

**No recession-cone/ray machinery is needed.**  The point is that
`finite_of_dot_bounded` (`RegionEdges.lean:109`) already says a set on which both
`dot n` and `dot n'` are bounded is finite.  On `face R n` the form `dot n` is
*constant*, and `dot n'` is bounded above because `n' ∈ E R`.  So if only finitely
many points of `face R n` survived the cut, the discarded ones would form an infinite
set trapped between `c < dot n' ≤ dot n' a'` — impossible.
-/

namespace Nivat.LE2

open Nivat

section Probes
#check @Set.not_infinite
#check @Set.Infinite.nontrivial
#check @finite_of_dot_bounded
#check @dot_eq_of_mem_face
end Probes

/-- **The `n`-face keeps infinitely many points after a cut in the `n'` direction.**
Stated on `face R n` alone, with no hypothesis on `R` beyond the two faces: `dot n` is
constant on `face R n`, and `dot n` is bounded above on `R`. -/
theorem infinite_face_inter_halfPlaneLE {R : Set (ℤ × ℤ)} {n n' : ℤ × ℤ}
    (hn : (face R n).Infinite) (hn' : (face R n').Nonempty) (hD : det n n' ≠ 0) (c : ℤ) :
    (face R n ∩ halfPlaneLE n' c).Infinite := by
  obtain ⟨a, ha⟩ := hn.nonempty
  obtain ⟨a', ha'⟩ := hn'
  by_contra hfin
  rw [Set.not_infinite] at hfin
  have hsub : face R n \ (face R n ∩ halfPlaneLE n' c) ⊆
      {z : ℤ × ℤ | dot n a ≤ dot n z ∧ dot n z ≤ dot n a ∧
        c + 1 ≤ dot n' z ∧ dot n' z ≤ dot n' a'} := by
    rintro z ⟨hzF, hzn⟩
    have h1 : dot n z = dot n a := dot_eq_of_mem_face hzF ha
    have h2 : ¬ dot n' z ≤ c := fun hc => hzn ⟨hzF, hc⟩
    exact ⟨le_of_eq h1.symm, le_of_eq h1, by omega, ha'.2 z hzF.1⟩
  have hdiff : (face R n \ (face R n ∩ halfPlaneLE n' c)).Finite :=
    (finite_of_dot_bounded hD _ _ _ _).subset hsub
  refine hn ((hdiff.union hfin).subset ?_)
  intro z hz
  by_cases h : z ∈ face R n ∩ halfPlaneLE n' c
  · exact Or.inr h
  · exact Or.inl ⟨hz, h⟩

/-- **`?semiInf`, closed.**  The edge parallel to `ℓ` is still semi-infinite after the
cut parallel to `ℓ'`. -/
theorem isSemiInfEdge_inter_halfPlaneLE_left {R : Set (ℤ × ℤ)} {n n' : ℤ × ℤ}
    (hR : IsRegion R n n') (c : ℤ) :
    IsSemiInfEdge (R ∩ halfPlaneLE n' c) n := by
  have hinf : (face (R ∩ halfPlaneLE n' c) n).Infinite := by
    refine (infinite_face_inter_halfPlaneLE hR.semiInf.2 hR.semiInf'.2.nonempty
      hR.detPos.ne' c).mono ?_
    rintro z ⟨hzF, hzH⟩
    exact ⟨⟨hzF.1, hzH⟩, fun y hy => hzF.2 y hy.1⟩
  exact ⟨⟨hR.semiInf.1.1, hinf.nontrivial⟩, hinf⟩

/-- Sanity check against the worked example: `quad` cut at `z₂ ≥ 1`. -/
theorem isSemiInfEdge_quad_cut_left :
    IsSemiInfEdge (quad ∩ halfPlaneLE ((0 : ℤ), (-1 : ℤ)) (-1)) (-1, 0) :=
  isSemiInfEdge_inter_halfPlaneLE_left isRegion_quad (-1)

#print axioms infinite_face_inter_halfPlaneLE
#print axioms isSemiInfEdge_inter_halfPlaneLE_left
#print axioms isSemiInfEdge_quad_cut_left

end Nivat.LE2
