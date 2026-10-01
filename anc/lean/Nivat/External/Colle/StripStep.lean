/-
Copyright (c) 2026 Nivat contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nivat contributors
-/
import Nivat.External.Colle.StripCut
import Nivat.External.Colle.EnvFit

/-!
# Strip step infrastructure

**Target**: Build towards `hstrip` via occupancy on ψ-bounded cuts.

Two pieces:
1. `edge_of_cut`: half-plane cuts preserve edge structure when the face remains nontrivial
2. `exists_level_psi_min`: finite sets have ψ-minimizers at each occupied level

-/

namespace Nivat.StripStep

open Nivat.LE2 (dot Prim E face)

/-- **Edge preservation under half-plane cuts.**

If `n` is primitive and `face R n ∩ H` is nontrivial, then `n ∈ E (R ∩ H)`.
The hypothesis `hnt` provides a point of `face R n ∩ H`, which is a maximizer
over `R` by definition of face, so `face_inter_of_attained` applies. -/
theorem edge_of_cut {R H : Set (ℤ × ℤ)} {n : ℤ × ℤ}
    (hn : Prim n) (hnt : (face R n ∩ H).Nontrivial) :
    n ∈ E (R ∩ H) := by
  -- E (R ∩ H) = {n | Prim n ∧ (face (R ∩ H) n).Nontrivial}
  rw [Nivat.LE2.mem_E_iff]
  refine ⟨hn, ?_⟩

  -- Build hmax for face_inter_of_attained from a point in face R n ∩ H
  obtain ⟨x, hx, y, hy, hne⟩ := hnt
  obtain ⟨hxface, hxH⟩ := hx
  obtain ⟨hyface, hyH⟩ := hy
  -- hxface : x ∈ face R n means x ∈ R and ∀ z ∈ R, dot n z ≤ dot n x
  obtain ⟨hxR, hxmax⟩ := Nivat.LE2.mem_face_iff.mp hxface

  -- So we have hmax: ∃ x ∈ R ∩ H, ∀ z ∈ R, dot n z ≤ dot n x
  have hmax : ∃ x₀ ∈ R ∩ H, ∀ z ∈ R, dot n z ≤ dot n x₀ := ⟨x, ⟨hxR, hxH⟩, hxmax⟩

  -- Apply face_inter_of_attained: face (R ∩ H) n = face R n ∩ H
  rw [face_inter_of_attained hmax]

  -- Now need: (face R n ∩ H).Nontrivial
  exact ⟨x, ⟨hxface, hxH⟩, y, ⟨hyface, hyH⟩, hne⟩

#print axioms edge_of_cut

/-- **Existence of ψ-minimizers at each level.**

For a finite set `B` and an occupied level `lev` (with respect to `nl`), there exists
a point `g ∈ B` at that level minimizing `dot m`. Pure finiteness argument. -/
theorem exists_level_psi_min {B : Set (ℤ × ℤ)} {nl m : ℤ × ℤ} {lev : ℤ}
    (hBfin : B.Finite) (hocc : ∃ g ∈ B, dot nl g = lev) :
    ∃ g ∈ B, dot nl g = lev ∧
      ∀ y ∈ B, dot nl y = lev → dot m g ≤ dot m y := by
  -- The level set {g ∈ B | dot nl g = lev} is finite and nonempty
  set S := {g ∈ B | dot nl g = lev}
  have hSfin : S.Finite := hBfin.subset (fun _ h => h.1)
  obtain ⟨g₀, hg₀B, hg₀lev⟩ := hocc
  have hSne : S.Nonempty := ⟨g₀, ⟨hg₀B, hg₀lev⟩⟩

  -- Take the dot m-minimizer
  obtain ⟨g, hgS, hgmin⟩ := Set.exists_min_image S (fun z => dot m z) hSfin hSne
  obtain ⟨hgB, hglev⟩ := hgS
  refine ⟨g, hgB, hglev, ?_⟩
  intro y hyB hylev
  exact hgmin y ⟨hyB, hylev⟩

#print axioms exists_level_psi_min

end Nivat.StripStep
