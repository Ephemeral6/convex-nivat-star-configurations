import Nivat.Section8.External
import Nivat.External.Colle.HalfPlanePeriodicity
import Nivat.External.Colle.DirectionRigidity
import Nivat.External.Colle.LowComplexityGenerating
import Nivat.External.Colle.GeneratedHalfPlane

/-!
# Proved Colle lemmas in the existing section-8 vocabulary

These adapters use the existing `ONED`, `prodShift`, and `PeriodicDecompZ`
definitions. Importing `External` exposes its axioms, but none of the
proofs in this file uses them; the kernel audit checks that distinction.
The two Colle structure axioms are not discharged by these adapters.
-/

namespace Nivat.Colle

private theorem inner2_neg_normal (w : ℝ × ℝ) (z : ℤ × ℤ) :
    inner2 (-w) z = -inner2 w z := by
  simp only [inner2, Prod.fst_neg, Prod.snd_neg]
  ring

/-- Colle Proposition 2.12 using `PeriodicDecompZ`: a nonzero multiple of
a tangent half-plane period is a global period of the configuration. -/
theorem period_multiple_of_periodicDecompZ {ξ : Config ℤ} {n : ℕ}
    (hdec : PeriodicDecompZ ξ n) {w : ℝ × ℝ} (hw : w ≠ 0) {c : ℝ}
    {u : ℤ × ℤ} (hu : u ≠ 0) (hwu : inner2 w u = 0)
    (hlocal : ∀ z, c ≤ inner2 w z → ξ (z + u) = ξ z) :
    ∃ k : ℤ, k ≠ 0 ∧ k • u ∈ Per ξ := by
  obtain ⟨f, hfp, hsum⟩ := hdec
  choose v hvp hv0 using hfp
  have hlocal' : ∀ z, c ≤ inner2 w z →
      (∑ i, f i (z + u)) = ∑ i, f i z := by
    intro z hz
    rw [← hsum, ← hsum]
    exact hlocal z hz
  obtain ⟨k, hk, hkp⟩ := exists_period_multiple_of_halfPlane Finset.univ f v
    hw hu hwu (fun i _ => hvp i) (fun i _ => hv0 i) hlocal'
  refine ⟨k, hk, ?_⟩
  rw [show ξ = (fun z => ∑ i, f i z) from funext hsum]
  exact hkp

/-- Colle Proposition 2.12 in overlap-periodicity form: a period tangent
to a half-plane gives a nonzero parallel global period. -/
theorem exists_parallel_period_of_overlap_halfPlane {ξ : Config ℤ} {n : ℕ}
    (hdec : PeriodicDecompZ ξ n) {w : ℝ × ℝ} (hw : w ≠ 0) {c : ℝ}
    {u : ℤ × ℤ} (hu : u ≠ 0) (hwu : inner2 w u = 0)
    (hlocal : ∀ z, c ≤ inner2 w z → c ≤ inner2 w (z + u) → ξ (z + u) = ξ z) :
    ∃ v : ℤ × ℤ, v ∈ Per ξ ∧ v ≠ 0 ∧ inner2 w v = 0 := by
  have hlocal' : ∀ z, c ≤ inner2 w z → ξ (z + u) = ξ z := by
    intro z hz
    apply hlocal z hz
    simpa only [inner2_add, hwu, add_zero] using hz
  obtain ⟨k, hk, hkp⟩ := period_multiple_of_periodicDecompZ hdec hw hu hwu hlocal'
  refine ⟨k • u, hkp, zsmul_ne_zero_of_ne_zero hk hu, ?_⟩
  rw [inner2_zsmul, hwu, mul_zero]

/-- Every existing one-sided nonexpansive direction is tangent to a factor
of any supplied nonparallel product annihilator. -/
theorem exists_tangent_of_mem_ONED {ξ : Config ℤ} {n : ℕ}
    {v : Fin n → ℤ × ℤ}
    (hnp : Pairwise fun i j => det (v i) (v j) ≠ 0)
    (hann : act (prodShift v) ξ = 0) {w : ℝ × ℝ} (hw : w ∈ ONED ξ) :
    ∃ i, inner2 w (v i) = 0 := by
  obtain ⟨_, x, hx, y, hy, hne, hagree⟩ := hw
  have hagree' : ∀ z, (0 : ℝ) ≤ inner2 (-w) z → x z = y z := by
    intro z hz
    apply hagree z
    change inner2 w z ≤ 0
    rw [inner2_neg_normal] at hz
    linarith
  obtain ⟨i, hi⟩ := exists_tangent_of_orbit_halfPlane_ambiguity hnp hann hx hy hne hagree'
  exact ⟨i, by simpa only [inner2_neg_normal, neg_eq_zero] using hi⟩

/-- Colle Lemma 2.3 in `ONED` notation: a generated unique support point
excludes the corresponding one-sided nonexpansive direction. -/
theorem not_mem_ONED_of_generatesAt {A : Type*} {ξ : Config A}
    {S : Finset (ℤ × ℤ)} {a : ℤ × ℤ} (hgen : GeneratesAt ξ S a)
    {w : ℝ × ℝ} (hmax : ∀ b ∈ S.erase a, inner2 w b < inner2 w a) :
    w ∉ ONED ξ := by
  intro hw
  obtain ⟨_, x, hx, y, hy, hne, hagree⟩ := hw
  apply hne
  apply eq_of_halfPlane_of_generatesAt (w := -w) (c := 0) hx hy hgen
  · intro b hb
    rw [inner2_neg_normal, inner2_neg_normal]
    exact neg_lt_neg (hmax b hb)
  · intro z hz
    apply hagree z
    change inner2 w z ≤ 0
    rw [inner2_neg_normal] at hz
    linarith

end Nivat.Colle
