/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.EnvFit
import Nivat.External.Colle.L1RegionBuild
import Nivat.External.Colle.L1Line0

/-!
# Corner condition sign dictionary

Lane Hcorner's file (exclusive, 2026-09-20). Three mechanical parts: the `u' ↦ -u'` dictionary,
discharge of the second conjunct by `hstrict`, and the named residual.

原文：b3_colle2.txt:790-804 (the placement step)
原文：b3_colle2.txt:796 (Figure 10: "The set `Ŝ_{φ_ι}` denotes **a translation of** `𝒮_{φ_ι}`")

Background established this round (treat as given):
With `hunimod : det u' vl = 1 ∨ det u' vl = -1`, `hperp : dot nℓ vl = 0`, `hnu : dot nℓ u' = -1`,
the pair `(u', vl)` is a ℤ-basis and `uCoord u' vl a b = - dot nℓ (b - a)`.
This is `Nivat.EnvFit.uCoord_eq_neg_dot_of_basis` with corollaries `uCoord_nonneg_iff_dot_le` /
`uCoord_nonpos_iff_dot_le`.
-/

set_option autoImplicit false

namespace Nivat.CornerNeg

open Nivat.LE2 Nivat.ColleReg Nivat.L1Line0

/-! ## Part 1: the `u' ↦ -u'` dictionary -/

/-- The `expNormal` of `-u'` equals the `expNormal` of `u'`. -/
theorem expNormal_neg (u' vl : ℤ × ℤ) : expNormal (-u') vl = expNormal u' vl := by
  simp only [expNormal, det, Prod.fst_neg, Prod.snd_neg]
  ext <;> simp <;> ring

/-- The `uCoord` flips sign under `u' ↦ -u'`. -/
theorem uCoord_neg (u' vl b₀ z : ℤ × ℤ) : uCoord (-u') vl b₀ z = - uCoord u' vl b₀ z := by
  simp only [uCoord, det, Prod.fst_neg, Prod.snd_neg]
  ring

/-- Unimodularity is preserved under `u' ↦ -u'`. -/
theorem unimod_neg {u' vl : ℤ × ℤ} (hunimod : det u' vl = 1 ∨ det u' vl = -1) :
    det (-u') vl = 1 ∨ det (-u') vl = -1 := by
  unfold det at *
  simp only [Prod.fst_neg, Prod.snd_neg]
  rcases hunimod with h | h
  · right
    have : -u'.1 * vl.2 - -u'.2 * vl.1 = -(u'.1 * vl.2 - u'.2 * vl.1) := by ring
    rw [this, h]
  · left
    have : -u'.1 * vl.2 - -u'.2 * vl.1 = -(u'.1 * vl.2 - u'.2 * vl.1) := by ring
    rw [this, h]
    norm_num

/-- The flipped-sign corner condition at `u'` is literally the original-sign corner condition
at `-u'`. -/
theorem corner_le_iff_corner_neg {u' vl : ℤ × ℤ} {S : Finset (ℤ × ℤ)} {a : ℤ × ℤ} :
    (∀ b ∈ S, 0 ≤ dot (expNormal u' vl) (b - a) ∧ uCoord u' vl a b ≤ 0) ↔
    (∀ b ∈ S, 0 ≤ dot (expNormal (-u') vl) (b - a) ∧ 0 ≤ uCoord (-u') vl a b) := by
  simp only [expNormal_neg, uCoord_neg]
  constructor
  · intro h b hb
    obtain ⟨h1, h2⟩ := h b hb
    exact ⟨h1, neg_nonneg.mpr h2⟩
  · intro h b hb
    obtain ⟨h1, h2⟩ := h b hb
    exact ⟨h1, nonpos_of_neg_nonneg h2⟩

/-! ## Part 2: `hstrict` discharges the second conjunct -/

/-- When `a₀` is a strict `nℓ`-minimiser over `Sw`, the `uCoord` half of the corner condition
holds for free. -/
theorem corner_second_conjunct_of_strict {nℓ u' vl a₀ : ℤ × ℤ} {Sw : Finset (ℤ × ℤ)}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hperp : dot nℓ vl = 0) (hnu : dot nℓ u' = -1)
    (_ha₀ : a₀ ∈ Sw)
    (hstrict : ∀ z ∈ Sw.erase a₀, dot nℓ a₀ < dot nℓ z) :
    ∀ b ∈ Sw, uCoord u' vl a₀ b ≤ 0 := by
  intro b hb
  by_cases h : b = a₀
  · rw [h, uCoord, sub_self]
    simp only [det, Prod.fst_zero, Prod.snd_zero, mul_zero, sub_zero]
    exact le_refl 0
  · have hb' : b ∈ Sw.erase a₀ := by
      simp only [Finset.mem_erase]
      exact ⟨h, hb⟩
    have hlt : dot nℓ a₀ < dot nℓ b := hstrict b hb'
    rw [Nivat.EnvFit.uCoord_nonpos_iff_dot_le hunimod hperp hnu]
    exact le_of_lt hlt

/-! ## Part 3: the residual, named -/

/-- The only residual content of the corner condition when `hstrict` holds: the `vl`-coordinate
half `hvlmin`. Original text: b3_colle2.txt:790-804 (placement step), specifically :796
(Figure 10). -/
theorem corner_le_of_strict_of_vlmin {nℓ u' vl a₀ : ℤ × ℤ} {Sw : Finset (ℤ × ℤ)}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hperp : dot nℓ vl = 0) (hnu : dot nℓ u' = -1)
    (ha₀ : a₀ ∈ Sw)
    (hstrict : ∀ z ∈ Sw.erase a₀, dot nℓ a₀ < dot nℓ z)
    (hvlmin : ∀ z ∈ Sw, 0 ≤ dot (expNormal u' vl) (z - a₀)) :
    ∀ b ∈ Sw, 0 ≤ dot (expNormal u' vl) (b - a₀) ∧ uCoord u' vl a₀ b ≤ 0 := by
  intro b hb
  exact ⟨hvlmin b hb, corner_second_conjunct_of_strict hunimod hperp hnu ha₀ hstrict b hb⟩

end Nivat.CornerNeg
