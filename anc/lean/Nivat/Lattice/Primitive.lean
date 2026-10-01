/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.Defs.Config

/-!
# Primitive lattice vectors

Elementary arithmetic of primitive vectors in `ℤ²`, used throughout *The Convex Nivat
Conjecture* (Pan) whenever a period is normalised as `h = k v` with `v`
primitive and `k ≥ 1` (§8.5, Appendix D).

Nothing here depends on §8 or on Appendix D: it is pure lattice arithmetic, on top of the
definitions `Nivat.det`, `Nivat.Primitive` and `Nivat.pi` of `Nivat.Defs.Config`.

## Main results

* `Nivat.exists_primitive_nsmul_eq` — every non-zero `h : ℤ²` is `k • v` with `v` primitive
  and `k > 0`, namely `k = gcd h.1 h.2`.
* `Nivat.eq_zsmul_of_det_eq_zero` — a vector parallel to a primitive `v` is an integer
  multiple of it.
* `Nivat.eq_or_eq_neg_of_det_eq_zero` — two parallel primitive vectors agree up to sign.

## Status

Complete; no `sorry`.
-/

namespace Nivat

/-- `det` is bilinear for integer scalars. -/
theorem det_zsmul_zsmul (c d : ℤ) (u v : ℤ × ℤ) :
    det (c • u) (d • v) = c * d * det u v := by
  simp only [det, Prod.smul_def, smul_eq_mul]; ring

/-- A non-zero integer multiple of a non-zero lattice vector is non-zero. -/
theorem zsmul_ne_zero_of_ne_zero {N : ℤ} (hN : N ≠ 0) {v : ℤ × ℤ} (hv : v ≠ 0) :
    N • v ≠ 0 := by
  intro hcon
  apply hv
  have h1 : N * v.1 = 0 := by have := congrArg Prod.fst hcon; simpa [Prod.smul_def] using this
  have h2 : N * v.2 = 0 := by have := congrArg Prod.snd hcon; simpa [Prod.smul_def] using this
  exact Prod.ext ((mul_eq_zero.mp h1).resolve_left hN) ((mul_eq_zero.mp h2).resolve_left hN)

/-- `pi` is negated by negating its first argument. -/
theorem pi_neg_left (v z : ℤ × ℤ) : pi (-v) z = -pi v z := by
  simp only [pi, det, Prod.fst_neg, Prod.snd_neg]; ring

/-- Every non-zero lattice vector is a positive integer multiple of a primitive vector: divide
through by `k = gcd h.1 h.2`, and read off a Bézout certificate for the quotient from the one
for `h`. -/
theorem exists_primitive_nsmul_eq {h : ℤ × ℤ} (hh : h ≠ 0) :
    ∃ (v : ℤ × ℤ) (k : ℕ), Primitive v ∧ 0 < k ∧ h = (k : ℤ) • v := by
  set d : ℕ := Int.gcd h.1 h.2 with hddef
  have hd_pos : 0 < d := by
    rw [hddef, Int.gcd_pos_iff]
    rcases eq_or_ne h.1 0 with h1 | h1
    · rcases eq_or_ne h.2 0 with h2 | h2
      · exact absurd (show h = 0 from Prod.ext h1 h2) hh
      · exact Or.inr h2
    · exact Or.inl h1
  have hdvd1 : (d : ℤ) ∣ h.1 := Int.gcd_dvd_left ..
  have hdvd2 : (d : ℤ) ∣ h.2 := Int.gcd_dvd_right ..
  set v : ℤ × ℤ := (h.1 / d, h.2 / d) with hvdef
  have heq1 : (d : ℤ) * v.1 = h.1 := by rw [hvdef]; exact Int.mul_ediv_cancel' hdvd1
  have heq2 : (d : ℤ) * v.2 = h.2 := by rw [hvdef]; exact Int.mul_ediv_cancel' hdvd2
  have hdne : (d : ℤ) ≠ 0 := by exact_mod_cast hd_pos.ne'
  have hbezout : (d : ℤ) = h.1 * Int.gcdA h.1 h.2 + h.2 * Int.gcdB h.1 h.2 :=
    Int.gcd_eq_gcd_ab h.1 h.2
  have hcoprime : Int.gcdA h.1 h.2 * v.1 + Int.gcdB h.1 h.2 * v.2 = 1 := by
    have hcancel : (d : ℤ) * (Int.gcdA h.1 h.2 * v.1 + Int.gcdB h.1 h.2 * v.2) = (d : ℤ) * 1 := by
      linear_combination Int.gcdA h.1 h.2 * heq1 + Int.gcdB h.1 h.2 * heq2 - hbezout
    exact mul_left_cancel₀ hdne hcancel
  refine ⟨v, d, ⟨Int.gcdA h.1 h.2, Int.gcdB h.1 h.2, hcoprime⟩, hd_pos, ?_⟩
  apply Prod.ext
  · show h.1 = (d : ℤ) * v.1
    exact heq1.symm
  · show h.2 = (d : ℤ) * v.2
    exact heq2.symm

/-- A vector orthogonal (in the `det` sense) to a primitive vector is an integer multiple of it:
in the unimodular basis `(v, u)` its `u`-coordinate is `det v x = 0`. -/
theorem eq_zsmul_of_det_eq_zero {v x : ℤ × ℤ} (hv : Primitive v) (hd : det v x = 0) :
    ∃ c : ℤ, x = c • v := by
  obtain ⟨u, hvu⟩ := hv.exists_dual
  refine ⟨det x u, ?_⟩
  have heq := eq_smul_add_smul hvu x
  rwa [hd, zero_smul, add_zero] at heq

/-- Two parallel primitive vectors are equal or opposite. -/
theorem eq_or_eq_neg_of_det_eq_zero {v w : ℤ × ℤ} (hv : Primitive v) (hw : Primitive w)
    (hdet : det v w = 0) : w = v ∨ w = -v := by
  obtain ⟨c, hc⟩ := eq_zsmul_of_det_eq_zero hv hdet
  obtain ⟨x, y, hxy⟩ := hw
  have hw1 : w.1 = c * v.1 := by rw [hc]; simp [Prod.smul_def]
  have hw2 : w.2 = c * v.2 := by rw [hc]; simp [Prod.smul_def]
  have hc1 : c * (x * v.1 + y * v.2) = 1 := by rw [← hxy, hw1, hw2]; ring
  rcases Int.isUnit_iff.mp (IsUnit.of_mul_eq_one _ hc1) with hc' | hc'
  · left; rw [hc, hc', one_smul]
  · right; rw [hc, hc']; simp

end Nivat
