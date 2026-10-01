/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.LatticeEdges

/-!
# Recession cone lemma for lattice-convex regions

**Source**: b3_colle2.txt:506 "Â_∞ is a weakly E(𝒮_φ)-enveloped set with two semi-infinite edges"

This file proves that a lattice-convex region containing a ray in direction d is closed
under translation by d. This is the mechanism behind rec_p and rec_vJ binders in
ChainDataGeom.ofParts.

## Mathematical content

A set R ⊆ ℤ² is **lattice-convex** if R = toReal⁻¹(C) for some closed convex C ⊆ ℝ².
If R contains a ray {g + t•d : t ∈ ℕ}, then R is closed under +d.

**Proof**: Let C be the closed convex set with R = toReal⁻¹(C).
For any z ∈ R, we have toReal z ∈ C.
Since C contains the ray {toReal(g + t•d) : t ∈ ℕ} = {toReal g + t • toReal d : t ∈ ℕ},
the recession cone of C contains toReal d.
By definition of recession cone: for all y ∈ C and all s ≥ 0, y + s • toReal d ∈ C.
In particular, toReal z + toReal d ∈ C.
Since toReal is injective (when restricted to a bounded region), z + d ∈ R.

Alternative direct proof using convexity:
For z ∈ R and the ray points g + t•d ∈ R:
  z + d = lim_{t→∞} ((1 - 1/t) • z + (1/t) • (g + t•d))
Since C is closed and convex, taking the limit preserves membership.
-/

set_option autoImplicit false

namespace Nivat.RecessionCone

open Nivat Nivat.LE2

/-- **Recession property of lattice-convex regions.**

If a lattice-convex region R contains a ray {g + t•d : t ∈ ℕ}, then R is closed
under translation by d.

原文：b3_colle2.txt:506 "Â_∞ is a weakly E(𝒮_φ)-enveloped set with two semi-infinite edges,
one of which is parallel to ℓ and the other one is parallel to ℓ_J."

A closed convex set containing a ray in direction d has d in its recession cone, which means
every point in the set can be translated by d and remain in the set. -/
theorem recession_of_ray {R : Set (ℤ × ℤ)} 
    (hR : IsLatticeConvexRegion R) 
    {g d : ℤ × ℤ} 
    (hray : ∀ t : ℕ, g + (t : ℤ) • d ∈ R) : 
    ∀ z ∈ R, z + d ∈ R := by
  intro z hz
  -- Unfold IsLatticeConvexRegion
  obtain ⟨C, hC_convex, hC_closed, hR_eq⟩ := hR
  rw [hR_eq] at hz ⊢
  simp only [Set.mem_preimage] at hz ⊢
  
  -- hz: toReal z ∈ C
  -- Goal: toReal (z + d) ∈ C
  
  -- Key insight: toReal (z + d) = toReal z + toReal d
  have h_add : toReal (z + d) = toReal z + toReal d := by
    simp only [toReal]
    ext
    · simp [Prod.fst_add]
    · simp [Prod.snd_add]
  
  rw [h_add]
  
  -- Need to show: toReal z + toReal d ∈ C
  -- Strategy: Use that C contains the ray {toReal g + t • toReal d : t ∈ ℕ}
  -- and C is closed convex, so toReal d is in the recession cone
  
  -- First, get the ray in C
  have hray_C : ∀ t : ℕ, toReal g + (t : ℝ) • toReal d ∈ C := by
    intro t
    have : g + (t : ℤ) • d ∈ R := hray t
    rw [hR_eq] at this
    simp only [Set.mem_preimage] at this
    -- Need: toReal (g + t • d) = toReal g + t • toReal d
    convert this using 1
    simp only [toReal]
    -- Goal: (↑g.1, ↑g.2) + ↑t • (↑d.1, ↑d.2) = (↑g.1 + ↑(↑t • d.1), ↑g.2 + ↑(↑t • d.2))
    ext <;> simp [Prod.smul_fst, Prod.smul_snd, Int.cast_add]
  
  -- Now use convexity and closedness to show toReal z + toReal d ∈ C
  -- Key: For each n ≥ 1, the convex combination
  --   y_n := (1 - 1/n) • toReal z + (1/n) • (toReal g + n • toReal d)
  -- is in C, and y_n → toReal z + toReal d as n → ∞

  -- Step 1: Simplify y_n algebraically (using n+1 to match tendsto theorem)
  have hy_eq : ∀ n : ℕ,
      ((1 : ℝ) - 1 / ((n : ℝ) + 1)) • toReal z + (1 / ((n : ℝ) + 1)) • (toReal g + ((n : ℝ) + 1) • toReal d) =
      toReal z + toReal d + (1 / ((n : ℝ) + 1)) • (toReal g - toReal z) := by
    intro n
    have hn_ne : ((n : ℝ) + 1) ≠ 0 := by positivity
    -- Algebraic manipulation in ℝ²
    have key : (1 / ((n : ℝ) + 1)) * ((n : ℝ) + 1) = 1 := by field_simp
    simp only [smul_add, smul_sub, sub_smul]
    rw [show (1 / ((n : ℝ) + 1)) • ((n : ℝ) + 1) • toReal d = toReal d by
      rw [smul_smul, key, one_smul]]
    module

  -- Step 2: For each n, y_n ∈ C by convexity
  have hy_mem : ∀ n : ℕ,
      ((1 : ℝ) - 1 / ((n : ℝ) + 1)) • toReal z + (1 / ((n : ℝ) + 1)) • (toReal g + ((n : ℝ) + 1) • toReal d) ∈ C := by
    intro n
    have hn_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hn_ne : ((n : ℝ) + 1) ≠ 0 := by positivity
    -- Coefficients sum to 1 and are nonneg
    have ha : (0 : ℝ) ≤ 1 - 1 / ((n : ℝ) + 1) := by
      have : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith
      have : 1 / ((n : ℝ) + 1) ≤ 1 := by
        rw [div_le_one hn_pos]
        exact this
      linarith
    have hb : (0 : ℝ) ≤ 1 / ((n : ℝ) + 1) := by positivity
    have hsum : (1 : ℝ) - 1 / ((n : ℝ) + 1) + 1 / ((n : ℝ) + 1) = 1 := by ring
    -- Apply convexity using the openSegment characterization
    have hray_n1 : toReal g + (↑(n + 1) : ℝ) • toReal d ∈ C := hray_C (n + 1)
    have : ((1 : ℝ) - 1 / ((n : ℝ) + 1)) • toReal z + (1 / ((n : ℝ) + 1)) • (toReal g + ((n : ℝ) + 1) • toReal d) ∈
        segment ℝ (toReal z) (toReal g + (↑(n + 1) : ℝ) • toReal d) := by
      rw [segment_eq_image']
      use (1 / ((n : ℝ) + 1))
      constructor
      · exact ⟨hb, by linarith⟩
      · have h_cast : ((n : ℝ) + 1) = (↑(n + 1) : ℝ) := by norm_cast
        rw [h_cast]
        simp only [smul_add, smul_sub, sub_smul, one_smul]
        -- Simplify (1 / ↑(n + 1)) • ↑(n + 1) • toReal d = toReal d
        have key : (1 / (↑(n + 1) : ℝ)) • (↑(n + 1) : ℝ) • toReal d = toReal d := by
          have hn_ne' : (↑(n + 1) : ℝ) ≠ 0 := by norm_cast
          rw [smul_smul, div_mul_cancel₀ _ hn_ne', one_smul]
        rw [key]
        ring
    exact hC_convex.segment_subset hz hray_n1 this

  -- Step 3: As n → ∞, the sequence converges to toReal z + toReal d
  have hlim : Filter.Tendsto
      (fun n : ℕ => toReal z + toReal d + ((1 : ℝ) / ((n : ℝ) + 1)) • (toReal g - toReal z))
      Filter.atTop (nhds (toReal z + toReal d)) := by
    have h_smul : Filter.Tendsto (fun n : ℕ => ((1 : ℝ) / ((n : ℝ) + 1)) • (toReal g - toReal z))
        Filter.atTop (nhds ((0 : ℝ) • (toReal g - toReal z))) := by
      exact Filter.Tendsto.smul_const tendsto_one_div_add_atTop_nhds_zero_nat _
    simp only [zero_smul] at h_smul
    convert h_smul.const_add (toReal z + toReal d) using 1
    simp

  -- Step 4: Combine: the sequence y_n → toReal z + toReal d
  have hlim' : Filter.Tendsto
      (fun n : ℕ => ((1 : ℝ) - 1 / ((n : ℝ) + 1)) • toReal z + (1 / ((n : ℝ) + 1)) • (toReal g + ((n : ℝ) + 1) • toReal d))
      Filter.atTop (nhds (toReal z + toReal d)) := by
    convert hlim using 1
    ext n : 1
    exact hy_eq n

  -- Step 5: C is closed, so the limit point is in C
  exact IsClosed.mem_of_tendsto hC_closed hlim'
    (Filter.eventually_atTop.mpr ⟨0, fun n _ => hy_mem n⟩)

end Nivat.RecessionCone

#print axioms Nivat.RecessionCone.recession_of_ray
