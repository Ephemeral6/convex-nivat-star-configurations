/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.WindowFit

set_option autoImplicit false

namespace Nivat.ColleReg
open Nivat Nivat.LE2 Finset
open scoped Pointwise

/-! ## Zonotope subset-sum characterization

Every point of the zonotope `zonoF s h = ∑ j ∈ s, {0, h j}` is a subset sum of generators,
and conversely every subset sum is in the zonotope. -/

/-- Every subset sum of the generators lies in the zonotope. -/
theorem sum_mem_zonoF {ι : Type*} [DecidableEq ι] (s : Finset ι) (h : ι → ℤ × ℤ)
    {S : Finset ι} (hS : S ⊆ s) : (∑ j ∈ S, h j) ∈ zonoF s h := by
  classical
  unfold zonoF
  induction s using Finset.induction generalizing S with
  | empty =>
      simp only [subset_empty] at hS
      rw [hS]
      simp
  | insert a s' ha ih =>
      rw [Finset.sum_insert ha]
      by_cases ha_in : a ∈ S
      · have hS' : S.erase a ⊆ s' := by
          intro x hx
          have hx_mem : x ∈ S.erase a := hx
          have hx_ne : x ≠ a := (mem_erase.mp hx_mem).1
          have hx_in_S : x ∈ S := (mem_erase.mp hx_mem).2
          have hx_in : x ∈ insert a s' := hS hx_in_S
          simp only [mem_insert] at hx_in
          cases hx_in with
          | inl h => exact absurd h hx_ne
          | inr h => exact h
        have hsum_eq : ∑ j ∈ S, h j = h a + ∑ j ∈ S.erase a, h j := by
          conv_lhs => rw [← insert_erase ha_in]
          rw [sum_insert]
          intro h_contra
          have : a ∈ S.erase a := h_contra
          exact absurd rfl (mem_erase.mp this).1
        rw [hsum_eq]
        refine Finset.add_mem_add ?_ (ih hS')
        show h a ∈ ({0, h a} : Finset (ℤ × ℤ))
        simp [mem_insert, mem_singleton]
      · have hS' : S ⊆ s' := by
          intro x hx
          have hx_in : x ∈ insert a s' := hS hx
          simp only [mem_insert] at hx_in
          cases hx_in with
          | inl h => exact absurd (h ▸ hx) ha_in
          | inr h => exact h
        have hsum_eq : ∑ j ∈ S, h j = 0 + ∑ j ∈ S, h j := by simp
        rw [hsum_eq]
        refine Finset.add_mem_add ?_ (ih hS')
        show (0 : ℤ × ℤ) ∈ ({0, h a} : Finset (ℤ × ℤ))
        simp [mem_insert, mem_singleton]

/-- Conversely every point of the zonotope is such a subset sum. -/
theorem exists_subset_sum_of_mem_zonoF {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (h : ι → ℤ × ℤ) {z : ℤ × ℤ} (hz : z ∈ zonoF s h) :
    ∃ S ⊆ s, z = ∑ j ∈ S, h j := by
  classical
  unfold zonoF at hz
  induction s using Finset.induction generalizing z with
  | empty =>
      simp only [sum_empty] at hz
      refine ⟨∅, by simp, ?_⟩
      simp only [sum_empty]
      have : z = (0 : ℤ × ℤ) := by
        have h_mem : z ∈ ({0} : Finset (ℤ × ℤ)) := hz
        simp only [mem_singleton] at h_mem
        exact h_mem
      exact this
  | insert a s' ha ih =>
      rw [sum_insert ha] at hz
      -- Use Finset.mem_add to decompose the sum
      have hz_add : ∃ va ∈ ({0, h a} : Finset (ℤ × ℤ)), ∃ ws' ∈ ∑ i ∈ s', ({0, h i} : Finset (ℤ × ℤ)), va + ws' = z := by
        rw [Finset.mem_add] at hz
        exact hz
      obtain ⟨va, hva_mem, ws', hws', hz_eq⟩ := hz_add
      have hva_cases : va = 0 ∨ va = h a := by
        simp only [mem_insert, mem_singleton] at hva_mem
        exact hva_mem
      obtain ⟨S', hS'_sub, hw_eq⟩ := ih hws'
      cases hva_cases with
      | inl hv_zero =>
          refine ⟨S', ?_, ?_⟩
          · exact Subset.trans hS'_sub (Finset.subset_insert a s')
          · rw [← hz_eq, hv_zero, hw_eq]
            ring
      | inr hv_a =>
          refine ⟨insert a S', insert_subset_insert a hS'_sub, ?_⟩
          rw [← hz_eq, sum_insert (mt (mem_of_subset hS'_sub) ha), hv_a, hw_eq]

#print axioms sum_mem_zonoF
#print axioms exists_subset_sum_of_mem_zonoF

end Nivat.ColleReg
