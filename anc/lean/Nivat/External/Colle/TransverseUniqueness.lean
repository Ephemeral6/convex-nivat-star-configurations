import Nivat.Section8.HalfPlane

/-!
# Half-plane uniqueness for sums of transverse periodic configurations

This is an elementary substitute for the expansiveness argument used in
Colle, arXiv:1909.08195v4, Proposition 2.12. It uses no finite-alphabet
hypothesis, no Laurent annihilator existence theorem, and no Colle axiom.
-/

namespace Nivat.Colle

variable {A : Type*} [AddCommGroup A]

/-- A transverse global period propagates zero from a half-plane everywhere. -/
theorem eq_zero_of_period_of_halfPlane {f : Config A} {w : ℝ × ℝ} {c : ℝ}
    {v : ℤ × ℤ} (hv : v ∈ Per f) (hwv : 0 < inner2 w v)
    (hzero : ∀ z, c ≤ inner2 w z → f z = 0) : ∀ z, f z = 0 := by
  intro z
  obtain ⟨N, hN⟩ := exists_nat_gt ((c - inner2 w z) / inner2 w v)
  have hlt : c - inner2 w z < (N : ℝ) * inner2 w v :=
    (div_lt_iff₀ hwv).mp hN
  have hz : c ≤ inner2 w (z + (N : ℤ) • v) := by
    rw [inner2_add, inner2_zsmul]
    push_cast
    linarith
  rw [← Per.apply ((Per f).zsmul_mem hv (N : ℤ)) z]
  exact hzero _ hz

/-- A finite sum of transversely periodic components vanishing on a half-plane
vanishes everywhere. No bound on the values of the components is needed. -/
theorem sum_eq_zero_of_halfPlane {ι : Type*} (s : Finset ι)
    (f : ι → Config A) (v : ι → ℤ × ℤ) {w : ℝ × ℝ} {c : ℝ}
    (hp : ∀ i ∈ s, v i ∈ Per (f i))
    (hv : ∀ i ∈ s, inner2 w (v i) ≠ 0)
    (hzero : ∀ z, c ≤ inner2 w z → ∑ i ∈ s, f i z = 0) :
    ∀ z, ∑ i ∈ s, f i z = 0 := by
  classical
  induction s using Finset.induction_on generalizing f with
  | empty => simp
  | @insert i s his ih =>
    obtain ⟨a, ha, hwa⟩ : ∃ a : ℤ × ℤ, a ∈ Per (f i) ∧ 0 < inner2 w a := by
      rcases lt_or_gt_of_ne (hv i (Finset.mem_insert_self ..)) with hneg | hpos
      · exact ⟨-v i, (Per (f i)).neg_mem (hp i (Finset.mem_insert_self ..)),
          by rw [inner2_neg]; linarith⟩
      · exact ⟨v i, hp i (Finset.mem_insert_self ..), hpos⟩
    let g : ι → Config A := fun j z => f j (z + a) - f j z
    have hgp : ∀ j ∈ s, v j ∈ Per (g j) := by
      intro j hj
      have hjp := hp j (Finset.mem_insert_of_mem hj)
      rw [mem_Per_iff]
      funext z
      change f j (z + v j + a) - f j (z + v j) = f j (z + a) - f j z
      rw [show z + v j + a = (z + a) + v j by abel,
        Per.apply hjp, Per.apply hjp]
    have hgz : ∀ z, c ≤ inner2 w z → ∑ j ∈ s, g j z = 0 := by
      intro z hz
      have hz' : c ≤ inner2 w (z + a) := by rw [inner2_add]; linarith
      have h₁ := hzero z hz
      have h₂ := hzero (z + a) hz'
      rw [Finset.sum_insert his] at h₁ h₂
      rw [Per.apply ha z] at h₂
      have heq : ∑ j ∈ s, f j (z + a) = ∑ j ∈ s, f j z :=
        add_left_cancel (h₂.trans h₁.symm)
      simp only [g, Finset.sum_sub_distrib, heq, sub_self]
    have hgzero := ih g hgp (fun j hj => hv j (Finset.mem_insert_of_mem hj)) hgz
    let F : Config A := fun z => ∑ j ∈ insert i s, f j z
    have hFp : a ∈ Per F := by
      rw [mem_Per_iff]
      funext z
      change (∑ j ∈ insert i s, f j (z + a)) = ∑ j ∈ insert i s, f j z
      rw [Finset.sum_insert his, Finset.sum_insert his, Per.apply ha z]
      congr 1
      have hg := hgzero z
      simpa only [g, Finset.sum_sub_distrib, sub_eq_zero] using hg
    exact eq_zero_of_period_of_halfPlane hFp hwa hzero

end Nivat.Colle
