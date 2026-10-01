import Nivat.External.Colle.TransverseUniqueness
import Nivat.Lattice.Primitive

/-!
# Colle Proposition 2.12: extension of a half-plane period

The proof is algebraic: use a common multiple to remove the components
parallel to the boundary, then apply transverse half-plane uniqueness.
The argument works over any additive commutative group, without finite
range or pairwise distinct component directions.
-/

namespace Nivat.Colle

variable {A : Type*}

/-- Two lattice vectors tangent to the same nonzero normal are parallel. -/
theorem det_eq_zero_of_inner2_eq_zero {w : ℝ × ℝ} (hw : w ≠ 0)
    {u v : ℤ × ℤ} (hu : inner2 w u = 0) (hv : inner2 w v = 0) :
    det u v = 0 := by
  have hd₁ : (det u v : ℝ) * w.1 = 0 := by
    simp only [inner2] at hu hv
    simp only [det, Int.cast_sub, Int.cast_mul]
    linear_combination (v.2 : ℝ) * hu - (u.2 : ℝ) * hv
  have hd₂ : (det u v : ℝ) * w.2 = 0 := by
    simp only [inner2] at hu hv
    simp only [det, Int.cast_sub, Int.cast_mul]
    linear_combination (u.1 : ℝ) * hv - (v.1 : ℝ) * hu
  by_contra hd
  have hd' : (det u v : ℝ) ≠ 0 := by exact_mod_cast hd
  exact hw (Prod.ext ((mul_eq_zero.mp hd₁).resolve_left hd')
    ((mul_eq_zero.mp hd₂).resolve_left hd'))

/-- Parallel nonzero lattice vectors have a common multiple with a nonzero
coefficient on the first vector. -/
theorem exists_common_multiple_of_det_eq_zero {u v : ℤ × ℤ}
    (hu : u ≠ 0) (hv : v ≠ 0) (huv : det u v = 0) :
    ∃ k l : ℤ, k ≠ 0 ∧ k • u = l • v := by
  obtain ⟨a, k, ha, hk, rfl⟩ := exists_primitive_nsmul_eq hu
  have hk' : (k : ℤ) ≠ 0 := by exact_mod_cast hk.ne'
  have hd : det a v = 0 := by
    have heq : det ((k : ℤ) • a) v = (k : ℤ) * det a v := by
      simp only [det, Prod.smul_def, smul_eq_mul]; ring
    rw [heq] at huv
    exact (mul_eq_zero.mp huv).resolve_left hk'
  obtain ⟨l, rfl⟩ := eq_zsmul_of_det_eq_zero ha hd
  have hl : l ≠ 0 := by
    intro h
    exact hv (by rw [h, zero_smul])
  exact ⟨l, k, hl, by simp only [smul_smul, mul_comm]⟩

/-- A finite family of tangent periodic components admits a common nonzero
multiple of any given nonzero tangent vector as a period. -/
theorem exists_common_tangent_period {ι : Type*} (s : Finset ι)
    (f : ι → Config A) (v : ι → ℤ × ℤ) {w : ℝ × ℝ} (hw : w ≠ 0)
    {u : ℤ × ℤ} (hu : u ≠ 0) (hwu : inner2 w u = 0)
    (hp : ∀ i ∈ s, v i ∈ Per (f i)) (hv : ∀ i ∈ s, v i ≠ 0)
    (hwv : ∀ i ∈ s, inner2 w (v i) = 0) :
    ∃ k : ℤ, k ≠ 0 ∧ ∀ i ∈ s, k • u ∈ Per (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, by simp⟩
  | @insert i s his ih =>
    obtain ⟨k, hk, hkp⟩ := ih (fun j hj => hp j (Finset.mem_insert_of_mem hj))
      (fun j hj => hv j (Finset.mem_insert_of_mem hj))
      (fun j hj => hwv j (Finset.mem_insert_of_mem hj))
    obtain ⟨l, m, hl, hlm⟩ := exists_common_multiple_of_det_eq_zero hu
      (hv i (Finset.mem_insert_self ..))
      (det_eq_zero_of_inner2_eq_zero hw hwu (hwv i (Finset.mem_insert_self ..)))
    refine ⟨k * l, mul_ne_zero hk hl, ?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · rw [mul_smul, hlm]
      exact (Per (f j)).zsmul_mem
        ((Per (f j)).zsmul_mem (hp j (Finset.mem_insert_self ..)) m) k
    · rw [mul_comm, mul_smul]
      exact (Per (f j)).zsmul_mem (hkp j hj) l

/-- A tangent period on a half-plane can be iterated by every integer. -/
theorem halfPlane_period_zsmul {f : Config A} {w : ℝ × ℝ} {c : ℝ}
    {u : ℤ × ℤ} (hwu : inner2 w u = 0)
    (hp : ∀ z, c ≤ inner2 w z → f (z + u) = f z) (k : ℤ) :
    ∀ z, c ≤ inner2 w z → f (z + k • u) = f z := by
  have hmem (z : ℤ × ℤ) (hz : c ≤ inner2 w z) (l : ℤ) :
      c ≤ inner2 w (z + l • u) := by
    simpa only [inner2_add, inner2_zsmul, hwu, mul_zero, add_zero] using hz
  induction k using Int.induction_on with
  | zero => simp
  | succ n ih =>
    intro z hz
    rw [add_smul, one_smul, ← add_assoc, hp _ (hmem z hz n)]
    exact ih z hz
  | pred n ih =>
    intro z hz
    have heq : (z + (-(n : ℤ) - 1) • u) + u = z + (-(n : ℤ)) • u := by
      rw [sub_smul, one_smul]; abel
    rw [← hp _ (hmem z hz (-(n : ℤ) - 1)), heq]
    exact ih z hz

/-- Colle Proposition 2.12, with the stronger conclusion that a nonzero
integer multiple of the specified half-plane period is a global period.
Only existence of a finite periodic decomposition is assumed. -/
theorem exists_period_multiple_of_halfPlane [AddCommGroup A]
    {ι : Type*} (s : Finset ι) (f : ι → Config A) (v : ι → ℤ × ℤ)
    {w : ℝ × ℝ} (hw : w ≠ 0) {c : ℝ} {u : ℤ × ℤ}
    (hu : u ≠ 0) (hwu : inner2 w u = 0)
    (hp : ∀ i ∈ s, v i ∈ Per (f i)) (hv : ∀ i ∈ s, v i ≠ 0)
    (hlocal : ∀ z, c ≤ inner2 w z →
      (∑ i ∈ s, f i (z + u)) = ∑ i ∈ s, f i z) :
    ∃ k : ℤ, k ≠ 0 ∧ k • u ∈ Per (fun z => ∑ i ∈ s, f i z) := by
  classical
  obtain ⟨k, hk, hkp⟩ := exists_common_tangent_period
    (s.filter fun i => inner2 w (v i) = 0) f v hw hu hwu
    (fun i hi => hp i (Finset.mem_filter.mp hi).1)
    (fun i hi => hv i (Finset.mem_filter.mp hi).1)
    (fun i hi => (Finset.mem_filter.mp hi).2)
  let g : ι → Config A := fun i z => f i (z + k • u) - f i z
  let r := s.filter fun i => inner2 w (v i) ≠ 0
  have hsum (z : ℤ × ℤ) : (∑ i ∈ r, g i z) = ∑ i ∈ s, g i z := by
    simp only [r, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hwi : inner2 w (v i) = 0
    · have hki := hkp i (Finset.mem_filter.mpr ⟨hi, hwi⟩)
      simp only [hwi, ne_eq, not_true_eq_false, if_false, g, Per.apply hki z, sub_self]
    · simp only [hwi, ne_eq, not_false_eq_true, if_true]
  have hgp : ∀ i ∈ r, v i ∈ Per (g i) := by
    intro i hi
    have hip := hp i (Finset.mem_filter.mp hi).1
    rw [mem_Per_iff]
    funext z
    change f i (z + v i + k • u) - f i (z + v i) = f i (z + k • u) - f i z
    rw [show z + v i + k • u = (z + k • u) + v i by abel,
      Per.apply hip, Per.apply hip]
  have hgz : ∀ z, c ≤ inner2 w z → ∑ i ∈ r, g i z = 0 := by
    intro z hz
    rw [hsum]
    simpa only [g, Finset.sum_sub_distrib, sub_eq_zero] using
      halfPlane_period_zsmul (f := fun a => ∑ i ∈ s, f i a) hwu hlocal k z hz
  have hgzero := sum_eq_zero_of_halfPlane r g v hgp
    (fun i hi => (Finset.mem_filter.mp hi).2) hgz
  refine ⟨k, hk, ?_⟩
  rw [mem_Per_iff]
  funext z
  have h := hgzero z
  rw [hsum] at h
  simpa only [g, Finset.sum_sub_distrib, sub_eq_zero, T_apply] using h

end Nivat.Colle
