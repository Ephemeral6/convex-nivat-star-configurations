/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.LatticeEdges

set_option autoImplicit false

namespace Nivat.ColleReg
open Nivat Nivat.LE2

/-! # Minkowski erosion

Erosion of a lattice-convex region by a segment `{0, d}`, used in the proof of
`exists_shift_subset_of_envOf` (the Minkowski decomposition needed for hole 6).

**原文对应：** The erosion lemmas support the inductive construction of a translate
of the zonotope `𝒮_φ` that fits inside the enveloped set `B` (Definition 3.2,
`b3_colle2.txt:402`). Each generator contributes one erosion step.
-/

/-- **Minkowski erosion** of `T` by the segment `{0, d}`. -/
def erode (T : Set (ℤ × ℤ)) (d : ℤ × ℤ) : Set (ℤ × ℤ) := {z | z ∈ T ∧ z + d ∈ T}

theorem erode_subset (T : Set (ℤ × ℤ)) (d : ℤ × ℤ) : erode T d ⊆ T := by
  intro z hz
  exact hz.1

theorem erode_finite {T : Set (ℤ × ℤ)} (hfin : T.Finite) (d : ℤ × ℤ) : (erode T d).Finite := by
  apply Set.Finite.subset hfin
  exact erode_subset T d

theorem isLatticeConvexRegion_erode {T : Set (ℤ × ℤ)}
    (hlc : Nivat.IsLatticeConvexRegion T) (d : ℤ × ℤ) :
    Nivat.IsLatticeConvexRegion (erode T d) := by
  -- erode T d = T ∩ (fun z => z + d)⁻¹' T
  have heq : erode T d = T ∩ (fun z => z + d) ⁻¹' T := by
    ext z
    simp only [erode, Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf]
  rw [heq]
  -- (fun z => z + d)⁻¹' T = shift (-d) T is a translate of T
  have hshift : IsLatticeConvexRegion ((fun z => z + d) ⁻¹' T) := by
    have heq' : (fun z => z + d) ⁻¹' T = shift (-d) T := by
      ext z
      simp only [Set.mem_preimage, mem_shift_iff]
      ring_nf
    rw [heq']
    exact isLatticeConvexRegion_shift_of (-d) hlc
  -- Intersection of two lattice-convex regions is lattice-convex
  obtain ⟨C₁, hC₁conv, hC₁closed, hT₁eq⟩ := hlc
  obtain ⟨C₂, hC₂conv, hC₂closed, hT₂eq⟩ := hshift
  use C₁ ∩ C₂
  refine ⟨hC₁conv.inter hC₂conv, hC₁closed.inter hC₂closed, ?_⟩
  ext z
  simp only [Set.mem_preimage, Set.mem_inter_iff]
  constructor
  · intro ⟨hz1, hz2⟩
    rw [hT₁eq] at hz1
    have hz2' : toReal z ∈ C₂ := by
      have : z ∈ (fun z => z + d) ⁻¹' T := hz2
      rw [hT₂eq] at this
      exact this
    exact ⟨hz1, hz2'⟩
  · intro ⟨hz1, hz2⟩
    constructor
    · rw [hT₁eq]
      exact hz1
    · show z + d ∈ T
      have : z ∈ (fun z => z + d) ⁻¹' T := by
        rw [hT₂eq]
        exact hz2
      exact this

theorem suppVal_erode_le {T : Set (ℤ × ℤ)} (hfin : T.Finite)
    {d : ℤ × ℤ} (hne : (erode T d).Nonempty) (n : ℤ × ℤ) :
    suppVal (erode T d) n ≤ suppVal T n - max 0 (dot n d) := by
  obtain ⟨v, hv, hvmax⟩ := exists_suppVal_eq (erode_finite hfin d) hne n
  rw [← hvmax]
  -- v ∈ erode T d means v ∈ T and v + d ∈ T
  have hv_mem : v ∈ T := hv.1
  have hvd_mem : v + d ∈ T := hv.2
  -- We have dot n v ≤ suppVal T n
  have h1 : dot n v ≤ suppVal T n := by
    exact le_suppVal hfin ⟨v, hv_mem⟩ hv_mem
  -- We have dot n (v + d) = dot n v + dot n d ≤ suppVal T n
  have h2 : dot n (v + d) ≤ suppVal T n := by
    exact le_suppVal hfin ⟨v, hv_mem⟩ hvd_mem
  -- From h2: dot n v + dot n d ≤ suppVal T n
  rw [dot_add] at h2
  -- So dot n v ≤ suppVal T n - dot n d
  have h3 : dot n v ≤ suppVal T n - dot n d := by omega
  -- Therefore dot n v ≤ suppVal T n - max 0 (dot n d)
  omega

end Nivat.ColleReg

#print axioms Nivat.ColleReg.erode_subset
#print axioms Nivat.ColleReg.erode_finite
#print axioms Nivat.ColleReg.isLatticeConvexRegion_erode
#print axioms Nivat.ColleReg.suppVal_erode_le
