/-
lane-place, 2026-09-22.
-/
import Nivat.External.Colle.L1Cut
import Nivat.External.Colle.Claim47Core
import Nivat.Lattice.Primitive

/-!
# The `topFace`/`derivedQ` split, characterised via a perpendicular `m`

Consumer: `hedge` (`RegionSteps.lean:1769-1774`) and the extension of
`Nivat.L1LinePackage.exists_line_package` needed to jointly produce it.

`derivedQ ε w S` / `topFace ε w S` split `S` by the REAL normal `cutNormal ε w = toReal(±perp w)`.
When `m : ℤ × ℤ` is perpendicular to `w` (`dot m w = 0`) and `w` is primitive, `m` is an integer
multiple `lam • perp w` of `perp w` (`Nivat.eq_zsmul_of_det_eq_zero`), so `dot m` and
`inner2 (cutNormal ε w) ·` agree up to the sign of `lam` and the choice of `ε`. This file proves
the two instances actually needed: whichever `ε` makes `topFace ε w S` the `dot m`-MINIMUM face
of `S` (the only choice compatible with `hedge`'s requirement that the top face sit in the gap
band while the rest of `derivedQ` sits above it, `L1LinePackage.lean:80` / team-lead ruling
2026-09-22).
-/

set_option autoImplicit false

namespace Nivat.ColleReg

open Nivat Nivat.LE2 Nivat.R2

/-- `m` perpendicular to primitive `w` is an integer multiple of `perp w`. -/
theorem exists_lam_of_perp {w m : ℤ × ℤ} (hw_prim : Primitive w) (hmw : dot m w = 0) :
    ∃ lam : ℤ, m = lam • perp w := by
  have hdpm : det (perp w) m = 0 := by
    have heq : det (perp w) m = - dot m w := by
      obtain ⟨w1, w2⟩ := w
      obtain ⟨m1, m2⟩ := m
      simp only [perp, det, dot]
      ring
    rw [heq, hmw]; ring
  exact Nivat.eq_zsmul_of_det_eq_zero (primitive_perp hw_prim) hdpm

/-- `dot m z = lam * det w z` when `m = lam • perp w`. -/
theorem dot_eq_lam_mul_det {w m : ℤ × ℤ} {lam : ℤ} (hm : m = lam • perp w) (z : ℤ × ℤ) :
    dot m z = lam * det w z := by
  rw [hm]
  have hexp : dot ((lam : ℤ) • perp w) z = lam * dot (perp w) z := by
    obtain ⟨n1, n2⟩ := perp w
    obtain ⟨z1, z2⟩ := z
    simp only [dot, Prod.smul_mk, smul_eq_mul]
    ring
  rw [hexp, dot_perp]

/-- `z ∈ topFace ε w S ↔ z ∈ S` and `z` maximises `inner2 (cutNormal ε w) ·` on `S`. -/
theorem mem_topFace_iff_max {ε : Bool} {w : ℤ × ℤ} {S : Finset (ℤ × ℤ)} {z : ℤ × ℤ} :
    z ∈ L1Data.topFace ε w S ↔ z ∈ S ∧ ∀ y ∈ S, inner2 (L1Data.cutNormal ε w) y ≤
      inner2 (L1Data.cutNormal ε w) z := by
  unfold L1Data.topFace
  constructor
  · intro hz
    obtain ⟨hzS, hzeq⟩ := mem_face.mp hz
    refine ⟨hzS, fun y hy => ?_⟩
    rw [hzeq]
    exact L1Data.le_levelMax ⟨z, hzS⟩ y hy
  · rintro ⟨hzS, hmax⟩
    refine mem_face.mpr ⟨hzS, le_antisymm (L1Data.le_levelMax ⟨z, hzS⟩ z hzS) ?_⟩
    unfold L1Data.levelMax
    rw [dif_pos ⟨z, hzS⟩]
    exact Finset.sup'_le ⟨z, hzS⟩ _ hmax

/-- **Case `lam < 0`**: `ε := true` makes `topFace` the `dot m`-MINIMUM face of `S`. -/
theorem topFace_true_eq_argmin {w m : ℤ × ℤ} {lam : ℤ} (hm : m = lam • perp w) (hlam : lam < 0)
    {S : Finset (ℤ × ℤ)} {z : ℤ × ℤ} :
    z ∈ L1Data.topFace true w S ↔ z ∈ S ∧ ∀ y ∈ S, dot m z ≤ dot m y := by
  rw [mem_topFace_iff_max]
  refine and_congr_right (fun hzS => ?_)
  have hcn : ∀ y : ℤ × ℤ, inner2 (L1Data.cutNormal true w) y = (det w y : ℝ) := by
    intro y
    unfold L1Data.cutNormal
    simp only [reduceIte]
    rw [Nivat.LE2.inner2_toReal, dot_perp]
  constructor
  · intro hmax y hy
    have h1 : (det w y : ℝ) ≤ (det w z : ℝ) := by rw [← hcn y, ← hcn z]; exact hmax y hy
    have h2 : det w y ≤ det w z := by exact_mod_cast h1
    have hdy : dot m y = lam * det w y := dot_eq_lam_mul_det hm y
    have hdz : dot m z = lam * det w z := dot_eq_lam_mul_det hm z
    nlinarith
  · intro hmin y hy
    have hdy : dot m y = lam * det w y := dot_eq_lam_mul_det hm y
    have hdz : dot m z = lam * det w z := dot_eq_lam_mul_det hm z
    have h2 : det w y ≤ det w z := by nlinarith [hmin y hy]
    have h1 : (det w y : ℝ) ≤ (det w z : ℝ) := by exact_mod_cast h2
    rw [hcn y, hcn z]; exact h1

/-- **Case `lam > 0`**: `ε := false` makes `topFace` the `dot m`-MINIMUM face of `S`. -/
theorem topFace_false_eq_argmin {w m : ℤ × ℤ} {lam : ℤ} (hm : m = lam • perp w) (hlam : 0 < lam)
    {S : Finset (ℤ × ℤ)} {z : ℤ × ℤ} :
    z ∈ L1Data.topFace false w S ↔ z ∈ S ∧ ∀ y ∈ S, dot m z ≤ dot m y := by
  rw [mem_topFace_iff_max]
  refine and_congr_right (fun hzS => ?_)
  have hcn : ∀ y : ℤ × ℤ, inner2 (L1Data.cutNormal false w) y = -(det w y : ℝ) := by
    intro y
    show inner2 (Nivat.toReal (-perp w)) y = -(det w y : ℝ)
    rw [Nivat.LE2.inner2_toReal, Nivat.LE2.dot_neg_left, dot_perp]
    push_cast
    ring
  constructor
  · intro hmax y hy
    have h1 : -(det w y : ℝ) ≤ -(det w z : ℝ) := by rw [← hcn y, ← hcn z]; exact hmax y hy
    have h2 : det w z ≤ det w y := by
      have h1' : (det w z : ℝ) ≤ (det w y : ℝ) := by linarith
      exact_mod_cast h1'
    have hdy : dot m y = lam * det w y := dot_eq_lam_mul_det hm y
    have hdz : dot m z = lam * det w z := dot_eq_lam_mul_det hm z
    nlinarith
  · intro hmin y hy
    have hdy : dot m y = lam * det w y := dot_eq_lam_mul_det hm y
    have hdz : dot m z = lam * det w z := dot_eq_lam_mul_det hm z
    have h2 : det w z ≤ det w y := by nlinarith [hmin y hy]
    have h1 : (det w z : ℝ) ≤ (det w y : ℝ) := by exact_mod_cast h2
    rw [hcn y, hcn z]; linarith

end Nivat.ColleReg

#print axioms Nivat.ColleReg.exists_lam_of_perp
#print axioms Nivat.ColleReg.dot_eq_lam_mul_det
#print axioms Nivat.ColleReg.mem_topFace_iff_max
#print axioms Nivat.ColleReg.topFace_true_eq_argmin
#print axioms Nivat.ColleReg.topFace_false_eq_argmin
