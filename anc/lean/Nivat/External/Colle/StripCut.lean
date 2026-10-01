/-
Copyright (c) 2026 Nivat contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nivat contributors
-/
import Nivat.Section8.HalfPlane
import Nivat.External.Colle.LatticeEdges

/-!
# Lattice convexity under half-plane cuts

Two mechanical lemmas needed for occupancy with ψ-bounds.

-/

namespace Nivat.StripStep

open Nivat (IsLatticeConvexRegion toReal)
open Nivat.LE2 (dot)

/-- **Lattice convexity is preserved by half-plane intersections.**

If `R` is the preimage of a convex set `C ⊆ ℝ²`, then `R ∩ {x | dot m x ≤ c}` is the
preimage of `C` intersected with the real half-space, which is convex and closed. -/
theorem latticeConvex_inter_halfPlane {R : Set (ℤ × ℤ)} {m : ℤ × ℤ} {c : ℤ}
    (h : IsLatticeConvexRegion R) :
    IsLatticeConvexRegion (R ∩ {x | dot m x ≤ c}) := by
  -- Unfold to get C
  obtain ⟨C, hCconv, hCclosed, hR⟩ := h

  -- Define the real half-space
  set H : Set (ℝ × ℝ) := {p : ℝ × ℝ | (m.1 : ℝ) * p.1 + (m.2 : ℝ) * p.2 ≤ (c : ℝ)}

  -- Show H is convex
  have hHconv : Convex ℝ H := by
    intro x hx y hy a b ha hb hab
    simp only [H, Set.mem_setOf] at hx hy ⊢
    calc (m.1 : ℝ) * (a * x.1 + b * y.1) + (m.2 : ℝ) * (a * x.2 + b * y.2)
        = a * ((m.1 : ℝ) * x.1 + (m.2 : ℝ) * x.2) + b * ((m.1 : ℝ) * y.1 + (m.2 : ℝ) * y.2) := by ring
      _ ≤ a * (c : ℝ) + b * (c : ℝ) := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left hx ha
          · exact mul_le_mul_of_nonneg_left hy hb
      _ = (c : ℝ) := by rw [←add_mul, hab]; ring

  -- Show H is closed
  have hHclosed : IsClosed H := by
    have : H = (fun p : ℝ × ℝ => (m.1 : ℝ) * p.1 + (m.2 : ℝ) * p.2) ⁻¹' Set.Iic (c : ℝ) := by
      ext p; simp [H, Set.mem_Iic]
    rw [this]
    apply IsClosed.preimage
    · continuity
    · exact isClosed_Iic

  -- Show C ∩ H is convex and closed
  have hCHconv : Convex ℝ (C ∩ H) := Convex.inter hCconv hHconv
  have hCHclosed : IsClosed (C ∩ H) := IsClosed.inter hCclosed hHclosed

  -- Show toReal splits the preimage
  have hpre : toReal ⁻¹' (C ∩ H) = toReal ⁻¹' C ∩ toReal ⁻¹' H := Set.preimage_inter

  -- Show toReal ⁻¹' H = {x | dot m x ≤ c}
  have hH_pre : toReal ⁻¹' H = {x : ℤ × ℤ | dot m x ≤ c} := by
    ext x
    simp only [Set.mem_preimage, H, Set.mem_setOf, toReal, dot]
    norm_cast

  -- Combine
  refine ⟨C ∩ H, hCHconv, hCHclosed, ?_⟩
  rw [hpre, hH_pre, hR]


/-- **Face intersection when maximum is attained in the cut.**

If the maximum of `dot n` over `R` is attained inside `R ∩ H`, then
`face (R ∩ H) n = face R n ∩ H`. One direction is immediate; the reverse uses
that any point of `face R n` has `dot n` equal to the maximum, which is attained in `H`. -/
theorem face_inter_of_attained {R H : Set (ℤ × ℤ)} {n : ℤ × ℤ}
    (hmax : ∃ x ∈ R ∩ H, ∀ y ∈ R, dot n y ≤ dot n x) :
    Nivat.LE2.face (R ∩ H) n = Nivat.LE2.face R n ∩ H := by
  obtain ⟨x₀, ⟨hx₀R, hx₀H⟩, hx₀max⟩ := hmax
  ext z
  constructor
  · -- face (R ∩ H) n ⊆ face R n ∩ H
    intro hz
    obtain ⟨hzRH, hzface⟩ := Nivat.LE2.mem_face_iff.mp hz
    obtain ⟨hzR, hzH⟩ := hzRH
    refine ⟨Nivat.LE2.mem_face_iff.mpr ⟨hzR, ?_⟩, hzH⟩
    intro y hy
    -- Need: dot n y ≤ dot n z
    -- All points in R have dot n ≤ dot n x₀, and z ∈ face (R ∩ H) n means all points
    -- in R ∩ H have dot n ≤ dot n z, so dot n z ≥ dot n x₀
    -- Combined with dot n z ≤ dot n x₀ (since z ∈ R), we get equality
    have hz_eq : dot n z = dot n x₀ := by
      apply le_antisymm
      · exact hx₀max z hzR
      · exact hzface x₀ ⟨hx₀R, hx₀H⟩
    rw [hz_eq]
    exact hx₀max y hy
  · -- face R n ∩ H ⊆ face (R ∩ H) n
    intro hz
    obtain ⟨hzfaceR, hzH⟩ := hz
    obtain ⟨hzR, hzface⟩ := Nivat.LE2.mem_face_iff.mp hzfaceR
    refine Nivat.LE2.mem_face_iff.mpr ⟨⟨hzR, hzH⟩, ?_⟩
    intro y ⟨hyR, _⟩
    exact hzface y hyR


end Nivat.StripStep

#print axioms Nivat.StripStep.latticeConvex_inter_halfPlane
#print axioms Nivat.StripStep.face_inter_of_attained
