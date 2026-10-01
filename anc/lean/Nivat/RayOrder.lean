/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Nivat.Defs.Config
import Nivat.Defs.Complexity

/-!
# Angular (counterclockwise) order of rays

Infrastructure for §8.3/§8.4 of *The Convex Nivat Conjecture* (Pan): Lemma 8.15
argues by "sweeping counterclockwise around the origin and taking the first ray encountered",
and the sector cone `IsSector` of §8.3 is naturally described by "lying between two rays".

Rather than real angles (`Real.Angle`, `atan2`), we use the classical *pseudo-angle*
comparison: split the plane into the two half-turns `[0, π)` and `[π, 2π)` around a reference
direction, then compare within a half-turn by the sign of the `2 × 2` determinant.  This only
uses the arithmetic of a linear ordered field, so it specializes to both `ℝ × ℝ` and (after
composing with `toReal`) to `ℤ × ℤ`.

## Main definitions

* `Nivat.det₂` — the `2 × 2` determinant / cross product on `K × K`.
* `Nivat.argHalf` — which half-turn (`[0, π)` or `[π, 2π)`, measured from the positive `x`-axis)
  a vector's direction lies in.
* `Nivat.argLt` — the strict counterclockwise order on directions: `argLt w₁ w₂` means "sweeping
  counterclockwise from the positive `x`-axis, `w₁`'s ray is met before `w₂`'s".
* `Nivat.InFirstHalf` / `Nivat.argLtFrom` — the same comparisons measured from an arbitrary
  reference direction `e` instead of the positive `x`-axis; used for "next ray after `r`".

## Main results

* `Nivat.argLt_trans` — transitivity of the counterclockwise order.
* `Nivat.argLt_trichotomy` — for nonzero `w₁ w₂`, exactly one of `argLt w₁ w₂`, `w₁ ∥ w₂` with
  the same sign, or `argLt w₂ w₁` holds.
* `Nivat.argLt_smul_left` / `Nivat.argLt_smul_right` — `argLt` only depends on the rays of its
  arguments.
* `Nivat.mem_coneSpan_iff` — the cone spanned by two vectors with nonzero determinant is exactly
  the vectors "angularly between" them; this is the cone used by `IsSector` in §8.3.
* `Nivat.coneSpan_lt_pi` — such a cone never contains both `y` and `-y`.
* `Nivat.exists_argLtFrom_min` — a nonempty finite set of nonzero vectors has an
  `argLtFrom`-least element, i.e. a "next ray" after any starting direction; this is the tool
  Lemma 8.15 needs.
* `Nivat.det₂_toReal` — `det₂` on `toReal '' _` agrees with `Nivat.det` on `ℤ × ℤ`.
* `Nivat.InFirstHalf.total` / `Nivat.InFirstHalf.trans_of_mem` — restricted to a common `e`-half,
  `InFirstHalf` behaves like a total preorder on rays.
* `Nivat.exists_angular_min` — a nonempty finite family of vectors in a common `e`-half has an
  angularly first element; the form of Lemma 8.15 consumed by `Section8.SecondHalfPlane`.
* `Nivat.InFirstHalf_neg_iff` — `w` and `-w` are never both, and never neither, in an `e`-half.

## Status

Complete; no `sorry`.
-/

namespace Nivat

set_option linter.unusedSectionVars false

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The `2 × 2` determinant (cross product) of two planar vectors. -/
def det₂ (w₁ w₂ : K × K) : K := w₁.1 * w₂.2 - w₁.2 * w₂.1

/-- The standard dot product of two planar vectors. -/
def dot₂ (w₁ w₂ : K × K) : K := w₁.1 * w₂.1 + w₁.2 * w₂.2

@[simp] theorem det₂_self (w : K × K) : det₂ w w = 0 := by simp [det₂]; ring

theorem det₂_comm (w₁ w₂ : K × K) : det₂ w₁ w₂ = -det₂ w₂ w₁ := by simp [det₂]; ring

theorem det₂_add_left (u v w : K × K) : det₂ (u + v) w = det₂ u w + det₂ v w := by
  simp [det₂]; ring

theorem det₂_add_right (u v w : K × K) : det₂ u (v + w) = det₂ u v + det₂ u w := by
  simp [det₂]; ring

@[simp] theorem det₂_smul_left (c : K) (w₁ w₂ : K × K) :
    det₂ (c • w₁) w₂ = c * det₂ w₁ w₂ := by
  simp only [det₂, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

@[simp] theorem det₂_smul_right (c : K) (w₁ w₂ : K × K) :
    det₂ w₁ (c • w₂) = c * det₂ w₁ w₂ := by
  simp only [det₂, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

theorem dot₂_comm (w₁ w₂ : K × K) : dot₂ w₁ w₂ = dot₂ w₂ w₁ := by simp [dot₂]; ring

@[simp] theorem dot₂_smul_left (c : K) (w₁ w₂ : K × K) :
    dot₂ (c • w₁) w₂ = c * dot₂ w₁ w₂ := by
  simp only [dot₂, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

@[simp] theorem dot₂_smul_right (c : K) (w₁ w₂ : K × K) :
    dot₂ w₁ (c • w₂) = c * dot₂ w₁ w₂ := by
  simp only [dot₂, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

/-- The dot product of a nonzero vector with itself is positive. -/
theorem dot₂_self_pos {w : K × K} (hw : w ≠ 0) : 0 < dot₂ w w := by
  have h : w.1 ≠ 0 ∨ w.2 ≠ 0 := by
    rcases eq_or_ne w.1 0 with h1 | h1
    · rcases eq_or_ne w.2 0 with h2 | h2
      · exact absurd (Prod.ext h1 h2) hw
      · exact Or.inr h2
    · exact Or.inl h1
  have h1 : 0 ≤ w.1 * w.1 := mul_self_nonneg _
  have h2 : 0 ≤ w.2 * w.2 := mul_self_nonneg _
  simp only [dot₂]
  rcases h with h | h
  · have h3 : 0 < w.1 * w.1 := mul_self_pos.mpr h
    linarith
  · have h3 : 0 < w.2 * w.2 := mul_self_pos.mpr h
    linarith

/-- If two vectors have zero determinant and the first is nonzero, the second is a scalar
multiple of the first. -/
theorem exists_smul_of_det₂_eq_zero {u v : K × K} (hu : u ≠ 0) (h : det₂ u v = 0) :
    ∃ k : K, v = k • u := by
  have h1 : u.1 ≠ 0 ∨ u.2 ≠ 0 := by
    rcases eq_or_ne u.1 0 with h1 | h1
    · rcases eq_or_ne u.2 0 with h2 | h2
      · exact absurd (Prod.ext h1 h2) hu
      · exact Or.inr h2
    · exact Or.inl h1
  rcases h1 with h1 | h1
  · refine ⟨v.1 / u.1, ?_⟩
    have heq : u.1 * v.2 = u.2 * v.1 := by simp only [det₂] at h; linarith
    refine Prod.ext ?_ ?_
    · show v.1 = v.1 / u.1 * u.1
      field_simp
    · show v.2 = v.1 / u.1 * u.2
      have : v.2 * u.1 = v.1 * u.2 := by linarith
      field_simp
      linarith
  · refine ⟨v.2 / u.2, ?_⟩
    have heq : u.1 * v.2 = u.2 * v.1 := by simp only [det₂] at h; linarith
    refine Prod.ext ?_ ?_
    · show v.1 = v.2 / u.2 * u.1
      have : v.1 * u.2 = v.2 * u.1 := by linarith
      field_simp
      linarith
    · show v.2 = v.2 / u.2 * u.2
      field_simp

/-- The half-turn `[0, π)` measured counterclockwise from a reference direction `e`: `w` lies
here iff it is reached from `e` by a counterclockwise turn strictly less than `π`. -/
def InFirstHalf (e w : K × K) : Prop := 0 < det₂ e w ∨ (det₂ e w = 0 ∧ 0 < dot₂ e w)

instance : DecidablePred fun p : (K × K) × (K × K) => InFirstHalf p.1 p.2 := fun _ =>
  inferInstanceAs (Decidable (_ ∨ _))

theorem InFirstHalf.det₂_nonneg {e w : K × K} (h : InFirstHalf e w) : 0 ≤ det₂ e w := by
  rcases h with h | ⟨h, _⟩
  · exact h.le
  · exact h.ge

theorem not_InFirstHalf.det₂_nonpos {e w : K × K} (h : ¬ InFirstHalf e w) : det₂ e w ≤ 0 := by
  by_contra hc
  push Not at hc
  exact h (Or.inl hc)

/-- The master 2D Plücker identity underlying transitivity of the angular order: for any four
planar vectors, `det (a,b) · det (e,c) + det (b,c) · det (e,a) = det (a,c) · det (e,b)`. -/
theorem det₂_identity (a b c e : K × K) :
    det₂ a b * det₂ e c + det₂ b c * det₂ e a = det₂ a c * det₂ e b := by
  simp only [det₂]; ring

/-- If `y` is in the first half relative to `e`, `x` is not "behind" `e` (`0 ≤ det₂ e x`), and
`x` comes strictly before `y` (`0 < det₂ x y`), then `det₂ e y ≠ 0`.  The technical core of
`argLt_trans`. -/
theorem det₂_ne_zero_of_pos {e x y : K × K} (hy : InFirstHalf e y) (hx : 0 ≤ det₂ e x)
    (hxy : 0 < det₂ x y) (he : e ≠ 0) : det₂ e y ≠ 0 := by
  intro heq
  have hdoty : 0 < dot₂ e y := by
    rcases hy with h | ⟨_, h⟩
    · exact absurd heq h.ne'
    · exact h
  obtain ⟨k, hk⟩ := exists_smul_of_det₂_eq_zero he heq
  have hee : 0 < dot₂ e e := dot₂_self_pos he
  have hprod : 0 < k * dot₂ e e := by
    rw [hk, dot₂_comm e (k • e), dot₂_smul_left, dot₂_comm e e] at hdoty
    exact hdoty
  have hkpos : 0 < k := by
    rcases mul_pos_iff.mp hprod with h | h
    · exact h.1
    · exact absurd hee (not_lt.mpr h.2.le)
  have hxyeq : det₂ x y = -k * det₂ e x := by
    rw [hk, det₂_smul_right, det₂_comm x e]; ring
  rw [hxyeq] at hxy
  have hneg : det₂ e x < 0 := by
    rcases mul_pos_iff.mp hxy with h | h
    · exact absurd h.1 (not_lt.mpr (by linarith))
    · exact h.2
  linarith

/-- Mirror of `det₂_ne_zero_of_pos` for the second half. -/
theorem det₂_ne_zero_of_neg {e x y : K × K} (hy : ¬ InFirstHalf e y) (hy0 : y ≠ 0)
    (hx : det₂ e x ≤ 0) (hxy : 0 < det₂ x y) (he : e ≠ 0) : det₂ e y ≠ 0 := by
  intro heq
  have hdoty : dot₂ e y ≤ 0 := by
    by_contra hc
    exact hy (Or.inr ⟨heq, not_le.mp hc⟩)
  obtain ⟨k, hk⟩ := exists_smul_of_det₂_eq_zero he heq
  have hk0 : k ≠ 0 := by
    intro hk0
    apply hy0
    rw [hk, hk0]; simp
  have hee : 0 < dot₂ e e := dot₂_self_pos he
  have hprod : k * dot₂ e e ≤ 0 := by
    rw [hk, dot₂_comm e (k • e), dot₂_smul_left, dot₂_comm e e] at hdoty
    exact hdoty
  have hkneg : k < 0 := by
    rcases lt_or_gt_of_ne hk0 with h | h
    · exact h
    · exact absurd (mul_pos h hee) (not_lt.mpr hprod)
  have hxyeq : det₂ x y = -k * det₂ e x := by
    rw [hk, det₂_smul_right, det₂_comm x e]; ring
  rw [hxyeq] at hxy
  have h1 : 0 ≤ -k := by linarith
  have hle : -k * det₂ e x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h1 hx
  linarith

/-- The counterclockwise order measured from an arbitrary reference direction `e`: `w₁`'s ray is
met before `w₂`'s when sweeping counterclockwise starting at `e`. -/
def argLtFrom (e w₁ w₂ : K × K) : Prop :=
  (InFirstHalf e w₁ ∧ ¬ InFirstHalf e w₂) ∨
    ((InFirstHalf e w₁ ↔ InFirstHalf e w₂) ∧ 0 < det₂ w₁ w₂)

theorem argLtFrom_irrefl (e w : K × K) : ¬ argLtFrom e w w := by
  rintro (⟨h1, h2⟩ | ⟨_, h⟩)
  · exact h2 h1
  · simp only [det₂_self] at h; exact absurd h (lt_irrefl 0)

/-- Transitivity of the counterclockwise order from a fixed reference direction `e ≠ 0`, for
nonzero vectors.  The technical core of the file: within one half-turn this reduces to the
Plücker identity `det₂_identity` via `det₂_ne_zero_of_pos` / `det₂_ne_zero_of_neg`. -/
theorem argLtFrom_trans {e : K × K} (he : e ≠ 0) {a b c : K × K} (hb : b ≠ 0) (hc : c ≠ 0)
    (hab : argLtFrom e a b) (hbc : argLtFrom e b c) : argLtFrom e a c := by
  classical
  rcases hab with ⟨ha1, hb1⟩ | ⟨hiff1, hd1⟩
  · rcases hbc with ⟨hb2, hc2⟩ | ⟨hiff2, hd2⟩
    · exact absurd hb2 hb1
    · exact Or.inl ⟨ha1, fun hc' => hb1 (hiff2.mpr hc')⟩
  · rcases hbc with ⟨hb2, hc2⟩ | ⟨hiff2, hd2⟩
    · exact Or.inl ⟨hiff1.mpr hb2, hc2⟩
    · refine Or.inr ⟨hiff1.trans hiff2, ?_⟩
      by_cases hHa : InFirstHalf e a
      · have hHb : InFirstHalf e b := hiff1.mp hHa
        have hHc : InFirstHalf e c := hiff2.mp hHb
        have hea : 0 ≤ det₂ e a := hHa.det₂_nonneg
        have heb0 : 0 ≤ det₂ e b := hHb.det₂_nonneg
        have heb_ne : det₂ e b ≠ 0 := det₂_ne_zero_of_pos hHb hea hd1 he
        have heb : 0 < det₂ e b := heb0.lt_of_ne (Ne.symm heb_ne)
        have hec_ne : det₂ e c ≠ 0 := det₂_ne_zero_of_pos hHc heb0 hd2 he
        have hident := det₂_identity a b c e
        have hrhs : 0 < det₂ a b * det₂ e c + det₂ b c * det₂ e a := by
          have hec : 0 < det₂ e c := (hHc.det₂_nonneg).lt_of_ne (Ne.symm hec_ne)
          have t1 : 0 < det₂ a b * det₂ e c := mul_pos hd1 hec
          have t2 : 0 ≤ det₂ b c * det₂ e a := mul_nonneg hd2.le hea
          linarith
        rw [hident] at hrhs
        rcases mul_pos_iff.mp hrhs with h | h
        · exact h.1
        · exact absurd h.2 (lt_asymm heb)
      · have hHb : ¬ InFirstHalf e b := fun hb' => hHa (hiff1.mpr hb')
        have hHc : ¬ InFirstHalf e c := fun hc' => hHb (hiff2.mpr hc')
        have hea : det₂ e a ≤ 0 := not_InFirstHalf.det₂_nonpos hHa
        have heb0 : det₂ e b ≤ 0 := not_InFirstHalf.det₂_nonpos hHb
        have heb_ne : det₂ e b ≠ 0 := det₂_ne_zero_of_neg hHb hb hea hd1 he
        have heb : det₂ e b < 0 := heb0.lt_of_ne heb_ne
        have hec_ne : det₂ e c ≠ 0 := det₂_ne_zero_of_neg hHc hc heb0 hd2 he
        have hident := det₂_identity a b c e
        have hrhs : det₂ a b * det₂ e c + det₂ b c * det₂ e a < 0 := by
          have hec : det₂ e c < 0 := (not_InFirstHalf.det₂_nonpos hHc).lt_of_ne hec_ne
          have t1 : det₂ a b * det₂ e c < 0 := mul_neg_of_pos_of_neg hd1 hec
          have t2 : det₂ b c * det₂ e a ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hd2.le hea
          linarith
        rw [hident] at hrhs
        rcases mul_neg_iff.mp hrhs with h | h
        · exact h.1
        · exact absurd h.2 (lt_asymm heb)

/-- `InFirstHalf` only depends on the ray of `w`: scaling by a positive constant does not
change which half-turn `w` lies in. -/
theorem InFirstHalf_smul_pos {k : K} (hk : 0 < k) (e w : K × K) :
    InFirstHalf e (k • w) ↔ InFirstHalf e w := by
  have hd : det₂ e (k • w) = k * det₂ e w := det₂_smul_right k e w
  have hdo : dot₂ e (k • w) = k * dot₂ e w := dot₂_smul_right k e w
  have hkz : ∀ x : K, k * x = 0 ↔ x = 0 := by
    intro x
    constructor
    · intro h
      rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' hk.ne'
      · exact h'
    · intro hx; rw [hx, mul_zero]
  simp only [InFirstHalf, hd, hdo, mul_pos_iff_of_pos_left hk, hkz]

/-- Scaling a nonzero vector `w` by a negative constant moves it to the opposite half-turn
relative to any reference direction `e ≠ 0`. -/
theorem InFirstHalf_smul_neg {k : K} (hk : k < 0) {e w : K × K} (he : e ≠ 0) (hw : w ≠ 0) :
    InFirstHalf e (k • w) ↔ ¬ InFirstHalf e w := by
  have hd : det₂ e (k • w) = k * det₂ e w := det₂_smul_right k e w
  have hdo : dot₂ e (k • w) = k * dot₂ e w := dot₂_smul_right k e w
  have hnd : ¬ (det₂ e w = 0 ∧ dot₂ e w = 0) := by
    rintro ⟨h1, h2⟩
    obtain ⟨m, hm⟩ := exists_smul_of_det₂_eq_zero he h1
    have : m * dot₂ e e = 0 := by rw [← dot₂_smul_right m e e, ← hm]; exact h2
    have hee : dot₂ e e ≠ 0 := (dot₂_self_pos he).ne'
    have hm0 : m = 0 := by
      rcases mul_eq_zero.mp this with h | h
      · exact h
      · exact absurd h hee
    exact hw (by rw [hm, hm0]; simp)
  have hkx : ∀ x : K, 0 < k * x ↔ x < 0 := by
    intro x
    constructor
    · intro h
      rcases mul_pos_iff.mp h with h' | h'
      · exact absurd h'.1 (not_lt.mpr hk.le)
      · exact h'.2
    · intro hx
      exact mul_pos_of_neg_of_neg hk hx
  have hkz : ∀ x : K, k * x = 0 ↔ x = 0 := by
    intro x
    constructor
    · intro h
      rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' hk.ne
      · exact h'
    · intro hx; rw [hx, mul_zero]
  simp only [InFirstHalf, hd, hdo, hkx, hkz]
  constructor
  · rintro (h | ⟨h1, h2⟩) (h' | ⟨h1', h2'⟩) <;> linarith
  · intro hn
    by_cases hd0 : det₂ e w < 0
    · exact Or.inl hd0
    · by_cases hd0' : det₂ e w = 0
      · refine Or.inr ⟨hd0', ?_⟩
        by_cases hdo0 : dot₂ e w < 0
        · exact hdo0
        · exfalso
          have hne : dot₂ e w ≠ 0 := fun h2 => hnd ⟨hd0', h2⟩
          have hge : 0 ≤ dot₂ e w := not_lt.mp hdo0
          have hgt : 0 < dot₂ e w := hge.lt_of_ne (Ne.symm hne)
          exact hn (Or.inr ⟨hd0', hgt⟩)
      · exfalso
        have hge : 0 ≤ det₂ e w := not_lt.mp hd0
        exact hn (Or.inl (hge.lt_of_ne (Ne.symm hd0')))

/-- Core of `argLtFrom_trichotomy` for the case where `a` and `b` are known to lie in the same
half-turn relative to `e`. -/
theorem argLtFrom_or_parallel_or {e a b : K × K} (he : e ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (hiff : InFirstHalf e a ↔ InFirstHalf e b) :
    argLtFrom e a b ∨ (det₂ a b = 0 ∧ ∃ m : K, 0 < m ∧ b = m • a) ∨ argLtFrom e b a := by
  rcases lt_trichotomy (det₂ a b) 0 with hlt | heq | hgt
  · have hba : 0 < det₂ b a := by have h := det₂_comm a b; linarith
    exact Or.inr (Or.inr (Or.inr ⟨hiff.symm, hba⟩))
  · obtain ⟨k, hk⟩ := exists_smul_of_det₂_eq_zero ha heq
    have hkpos : 0 < k := by
      rcases lt_trichotomy k 0 with hneg | hz | hpos
      · exfalso
        have hflip : InFirstHalf e (k • a) ↔ ¬ InFirstHalf e a := InFirstHalf_smul_neg hneg he ha
        rw [← hk] at hflip
        have hcontra : InFirstHalf e a ↔ ¬ InFirstHalf e a := hiff.trans hflip
        by_cases hHa' : InFirstHalf e a
        · exact (hcontra.mp hHa') hHa'
        · exact hHa' (hcontra.mpr hHa')
      · exact absurd (by rw [hk, hz]; simp) hb
      · exact hpos
    exact Or.inr (Or.inl ⟨heq, k, hkpos, hk⟩)
  · exact Or.inl (Or.inr ⟨hiff, hgt⟩)

/-- **Trichotomy.**  For nonzero `a b`, sweeping counterclockwise from `e ≠ 0`, exactly one of:
`a`'s ray is met before `b`'s, `a` and `b` are on the same ray, or `b`'s ray is met before `a`'s.
(Mutual exclusivity is immediate from `argLtFrom_irrefl` and `argLtFrom_trans`.) -/
theorem argLtFrom_trichotomy {e : K × K} (he : e ≠ 0) {a b : K × K} (ha : a ≠ 0) (hb : b ≠ 0) :
    argLtFrom e a b ∨ (det₂ a b = 0 ∧ ∃ m : K, 0 < m ∧ b = m • a) ∨ argLtFrom e b a := by
  classical
  by_cases hHa : InFirstHalf e a
  · by_cases hHb : InFirstHalf e b
    · exact argLtFrom_or_parallel_or he ha hb (iff_of_true hHa hHb)
    · exact Or.inl (Or.inl ⟨hHa, hHb⟩)
  · by_cases hHb : InFirstHalf e b
    · exact Or.inr (Or.inr (Or.inl ⟨hHb, hHa⟩))
    · exact argLtFrom_or_parallel_or he ha hb (iff_of_false hHa hHb)

/-- The half-turn containing `w`'s direction, measured counterclockwise from the positive
`x`-axis: `false` for `[0, π)` (upper half-plane and the positive `x`-axis), `true` for `[π, 2π)`
(lower half-plane and the negative `x`-axis). -/
def argHalf (w : K × K) : Bool := decide (w.2 < 0 ∨ (w.2 = 0 ∧ w.1 < 0))

/-- The strict counterclockwise order on directions, sweeping from the positive `x`-axis:
`argLt w₁ w₂` means `w₁`'s ray is met before `w₂`'s. -/
def argLt (w₁ w₂ : K × K) : Prop :=
  argHalf w₁ < argHalf w₂ ∨ (argHalf w₁ = argHalf w₂ ∧ 0 < det₂ w₁ w₂)

private theorem not_pos_or_iff {x y : K} (hxy : x ≠ 0 ∨ y ≠ 0) :
    (x < 0 ∨ (x = 0 ∧ y < 0)) ↔ ¬ (0 < x ∨ (x = 0 ∧ 0 < y)) := by
  constructor
  · rintro (h | ⟨h1, h2⟩) (h' | ⟨h1', h2'⟩) <;> linarith
  · intro hn
    by_cases hd0 : x < 0
    · exact Or.inl hd0
    · by_cases hd0' : x = 0
      · refine Or.inr ⟨hd0', ?_⟩
        by_cases hdo0 : y < 0
        · exact hdo0
        · exfalso
          have hne : y ≠ 0 := by
            rcases hxy with h1 | h1
            · exact absurd hd0' h1
            · exact h1
          have hge : 0 ≤ y := not_lt.mp hdo0
          have hgt : 0 < y := hge.lt_of_ne (Ne.symm hne)
          exact hn (Or.inr ⟨hd0', hgt⟩)
      · exfalso
        have hge : 0 ≤ x := not_lt.mp hd0
        exact hn (Or.inl (hge.lt_of_ne (Ne.symm hd0')))

theorem InFirstHalf_one_zero_iff (w : K × K) :
    InFirstHalf (1, 0) w ↔ 0 < w.2 ∨ (w.2 = 0 ∧ 0 < w.1) := by
  simp [InFirstHalf, det₂, dot₂]

theorem argHalf_eq_true_iff {w : K × K} (hw : w ≠ 0) :
    argHalf w = true ↔ ¬ InFirstHalf (1, 0) w := by
  rw [InFirstHalf_one_zero_iff]
  have hne : w.2 ≠ 0 ∨ w.1 ≠ 0 := by
    rcases eq_or_ne w.2 0 with h2 | h2
    · rcases eq_or_ne w.1 0 with h1 | h1
      · exact absurd (Prod.ext h1 h2) hw
      · exact Or.inr h1
    · exact Or.inl h2
  simp only [argHalf, decide_eq_true_eq]
  exact not_pos_or_iff hne

theorem argHalf_eq_false_iff {w : K × K} (hw : w ≠ 0) :
    argHalf w = false ↔ InFirstHalf (1, 0) w := by
  rw [← Bool.not_eq_true, argHalf_eq_true_iff hw, not_not]

private theorem bool_lt_iff (x y : Bool) : x < y ↔ x = false ∧ y = true := by
  cases x <;> cases y <;> decide

/-- `argLt` is exactly `argLtFrom` measured from the positive `x`-axis `(1, 0)`. -/
theorem argLt_iff_argLtFrom {a b : K × K} (ha : a ≠ 0) (hb : b ≠ 0) :
    argLt a b ↔ argLtFrom (1, 0) a b := by
  have heq : argHalf a = argHalf b ↔ (InFirstHalf (1, 0) a ↔ InFirstHalf (1, 0) b) := by
    rw [← argHalf_eq_false_iff ha, ← argHalf_eq_false_iff hb]
    cases argHalf a <;> cases argHalf b <;> simp
  unfold argLt argLtFrom
  rw [bool_lt_iff, argHalf_eq_false_iff ha, argHalf_eq_true_iff hb, heq]

theorem one_zero_ne_zero : ((1, 0) : K × K) ≠ 0 := fun h => one_ne_zero (congrArg Prod.fst h)

/-- `argLt` is irreflexive. -/
theorem argLt_irrefl (w : K × K) : ¬ argLt w w := by
  rintro (h1 | ⟨_, h⟩)
  · exact lt_irrefl _ h1
  · simp only [det₂_self] at h; exact absurd h (lt_irrefl 0)

/-- **Transitivity** of the counterclockwise order. -/
theorem argLt_trans {a b c : K × K} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hab : argLt a b) (hbc : argLt b c) : argLt a c := by
  rw [argLt_iff_argLtFrom ha hb] at hab
  rw [argLt_iff_argLtFrom hb hc] at hbc
  rw [argLt_iff_argLtFrom ha hc]
  exact argLtFrom_trans one_zero_ne_zero hb hc hab hbc

/-- **Trichotomy.**  For nonzero `a b`, exactly one of: `a`'s ray is met before `b`'s sweeping
counterclockwise from the positive `x`-axis, `a` and `b` are on the same ray, or `b`'s ray is met
before `a`'s. -/
theorem argLt_trichotomy {a b : K × K} (ha : a ≠ 0) (hb : b ≠ 0) :
    argLt a b ∨ (det₂ a b = 0 ∧ ∃ m : K, 0 < m ∧ b = m • a) ∨ argLt b a := by
  rw [argLt_iff_argLtFrom ha hb, argLt_iff_argLtFrom hb ha]
  exact argLtFrom_trichotomy one_zero_ne_zero ha hb

theorem argLtFrom_smul_left {e : K × K} {c : K} (hc : 0 < c) (a b : K × K) :
    argLtFrom e (c • a) b ↔ argLtFrom e a b := by
  unfold argLtFrom
  rw [InFirstHalf_smul_pos hc e a, det₂_smul_left]
  constructor
  · rintro (h | ⟨hiff, hd⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hiff, (mul_pos_iff_of_pos_left hc).mp hd⟩
  · rintro (h | ⟨hiff, hd⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hiff, mul_pos hc hd⟩

theorem argLtFrom_smul_right {e : K × K} {c : K} (hc : 0 < c) (a b : K × K) :
    argLtFrom e a (c • b) ↔ argLtFrom e a b := by
  unfold argLtFrom
  rw [InFirstHalf_smul_pos hc e b, det₂_smul_right]
  constructor
  · rintro (h | ⟨hiff, hd⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hiff, (mul_pos_iff_of_pos_left hc).mp hd⟩
  · rintro (h | ⟨hiff, hd⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hiff, mul_pos hc hd⟩

/-- `argLt` only depends on the ray of its left argument: positive scalars don't change it. -/
theorem argLt_smul_left {c : K} (hc : 0 < c) {a b : K × K} (ha : a ≠ 0) (hb : b ≠ 0) :
    argLt (c • a) b ↔ argLt a b := by
  have hca : c • a ≠ 0 := smul_ne_zero hc.ne' ha
  rw [argLt_iff_argLtFrom hca hb, argLt_iff_argLtFrom ha hb]
  exact argLtFrom_smul_left hc a b

/-- `argLt` only depends on the ray of its right argument: positive scalars don't change it. -/
theorem argLt_smul_right {c : K} (hc : 0 < c) {a b : K × K} (ha : a ≠ 0) (hb : b ≠ 0) :
    argLt a (c • b) ↔ argLt a b := by
  have hcb : c • b ≠ 0 := smul_ne_zero hc.ne' hb
  rw [argLt_iff_argLtFrom ha hcb, argLt_iff_argLtFrom ha hb]
  exact argLtFrom_smul_right hc a b

/-- The cone spanned by two vectors with nonnegative coefficients: `{s • w₁ + t • w₂ : s, t ≥ 0}`.
This is the cone used to build `IsSector` in §8.3. -/
def coneSpan (w₁ w₂ : K × K) : Set (K × K) := {y | ∃ s t : K, 0 ≤ s ∧ 0 ≤ t ∧ y = s • w₁ + t • w₂}

/-- Solve `y = s • w₁ + t • w₂` for `s, t` by Cramer's rule, when `w₁, w₂` are independent. -/
theorem eq_smul_add_smul_of_det₂_ne_zero {w₁ w₂ : K × K} (hD : det₂ w₁ w₂ ≠ 0) (y : K × K) :
    y = (det₂ y w₂ / det₂ w₁ w₂) • w₁ + (det₂ w₁ y / det₂ w₁ w₂) • w₂ := by
  refine Prod.ext ?_ ?_
  · show y.1 = (det₂ y w₂ / det₂ w₁ w₂) * w₁.1 + (det₂ w₁ y / det₂ w₁ w₂) * w₂.1
    have key : y.1 * det₂ w₁ w₂ = det₂ y w₂ * w₁.1 + det₂ w₁ y * w₂.1 := by
      simp only [det₂]; ring
    field_simp
    linarith [key]
  · show y.2 = (det₂ y w₂ / det₂ w₁ w₂) * w₁.2 + (det₂ w₁ y / det₂ w₁ w₂) * w₂.2
    have key : y.2 * det₂ w₁ w₂ = det₂ y w₂ * w₁.2 + det₂ w₁ y * w₂.2 := by
      simp only [det₂]; ring
    field_simp
    linarith [key]

/-- The cone spanned by `w₁, w₂` (with `w₁` before `w₂` in the counterclockwise order) is exactly
the set of nonzero vectors "angularly between" them: this is the cone used by `IsSector` in
§8.3. Proved directly from cross-product inequalities, without going back through `argLt`. -/
theorem mem_coneSpan_iff {w₁ w₂ y : K × K} (hD : 0 < det₂ w₁ w₂) (hy : y ≠ 0) :
    y ∈ coneSpan w₁ w₂ ↔ 0 ≤ det₂ w₁ y ∧ 0 ≤ det₂ y w₂ := by
  constructor
  · rintro ⟨s, t, hs, ht, rfl⟩
    constructor
    · rw [det₂_add_right, det₂_smul_right, det₂_smul_right, det₂_self, mul_zero, zero_add]
      exact mul_nonneg ht hD.le
    · rw [det₂_add_left, det₂_smul_left, det₂_smul_left, det₂_self, mul_zero, add_zero]
      exact mul_nonneg hs hD.le
  · rintro ⟨h1, h2⟩
    exact ⟨det₂ y w₂ / det₂ w₁ w₂, det₂ w₁ y / det₂ w₁ w₂,
      div_nonneg h2 hD.le, div_nonneg h1 hD.le, eq_smul_add_smul_of_det₂_ne_zero hD.ne' y⟩

/-- A cone `coneSpan w₁ w₂` with `0 < det₂ w₁ w₂` spans an angle strictly less than `π`: it never
contains both a nonzero vector and its negation. -/
theorem coneSpan_lt_pi {w₁ w₂ : K × K} (hD : 0 < det₂ w₁ w₂) {y : K × K}
    (hy : y ∈ coneSpan w₁ w₂) (hy0 : y ≠ 0) : -y ∉ coneSpan w₁ w₂ := by
  intro hny
  have hw₁ : w₁ ≠ 0 := by
    rintro rfl
    have hz : det₂ (0 : K × K) w₂ = 0 := by simp [det₂]
    rw [hz] at hD
    exact lt_irrefl 0 hD
  rw [mem_coneSpan_iff hD hy0] at hy
  rw [mem_coneSpan_iff hD (neg_ne_zero.mpr hy0)] at hny
  have e1 : det₂ w₁ (-y) = - det₂ w₁ y := by
    rw [show (-y) = (-1 : K) • y from (neg_one_smul K y).symm, det₂_smul_right]; ring
  have e2 : det₂ (-y) w₂ = - det₂ y w₂ := by
    rw [show (-y) = (-1 : K) • y from (neg_one_smul K y).symm, det₂_smul_left]; ring
  have h1' : det₂ w₁ y ≤ 0 := by have := hny.1; rw [e1] at this; linarith
  have h2' : det₂ y w₂ ≤ 0 := by have := hny.2; rw [e2] at this; linarith
  have hz1 : det₂ w₁ y = 0 := le_antisymm h1' hy.1
  have hz2 : det₂ y w₂ = 0 := le_antisymm h2' hy.2
  obtain ⟨k, hk⟩ := exists_smul_of_det₂_eq_zero hw₁ hz1
  have hkD : k * det₂ w₁ w₂ = 0 := by rw [← det₂_smul_left k w₁ w₂, ← hk]; exact hz2
  have hk0 : k = 0 := by
    rcases mul_eq_zero.mp hkD with h | h
    · exact h
    · exact absurd h hD.ne'
  exact hy0 (by rw [hk, hk0]; simp)

/-- **Existence of the next ray.**  Given a nonempty finite set `S` of nonzero vectors and a
nonzero starting direction `r`, some `c ∈ S` is angularly first when sweeping counterclockwise
from `r`: no `w ∈ S` comes strictly before `c`.  This is exactly the tool Lemma 8.15 needs
("sweep counterclockwise around the origin, find the first ray encountered"). -/
theorem exists_argLtFrom_min {r : K × K} (hr : r ≠ 0) {S : Finset (K × K)}
    (hS : S.Nonempty) (hS0 : ∀ w ∈ S, w ≠ 0) :
    ∃ c ∈ S, ∀ w ∈ S, ¬ argLtFrom r w c := by
  classical
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    obtain ⟨a, ha⟩ := hS
    rcases (S.erase a).eq_empty_or_nonempty with he | hne
    · refine ⟨a, ha, fun w hw hlt => ?_⟩
      have hwa : w = a := by
        by_contra hne'
        have : w ∈ S.erase a := Finset.mem_erase.mpr ⟨hne', hw⟩
        rw [he] at this
        exact absurd this (Finset.notMem_empty _)
      rw [hwa] at hlt
      exact argLtFrom_irrefl r a hlt
    · have hsub : S.erase a ⊂ S := Finset.erase_ssubset ha
      obtain ⟨c, hc, hmin⟩ := ih (S.erase a) hsub hne
        (fun w hw => hS0 w (Finset.mem_of_mem_erase hw))
      have hcS : c ∈ S := Finset.mem_of_mem_erase hc
      have haS0 : a ≠ 0 := hS0 a ha
      have hcS0 : c ≠ 0 := hS0 c hcS
      by_cases hac : argLtFrom r a c
      · refine ⟨a, ha, fun w hw hlt => ?_⟩
        by_cases hwa : w = a
        · rw [hwa] at hlt; exact argLtFrom_irrefl r a hlt
        · have hwc : w ∈ S.erase a := Finset.mem_erase.mpr ⟨hwa, hw⟩
          exact hmin w hwc (argLtFrom_trans hr haS0 hcS0 hlt hac)
      · refine ⟨c, hcS, fun w hw hlt => ?_⟩
        by_cases hwa : w = a
        · rw [hwa] at hlt; exact hac hlt
        · have hwc : w ∈ S.erase a := Finset.mem_erase.mpr ⟨hwa, hw⟩
          exact hmin w hwc hlt

/-- `InFirstHalf` only depends on the ray of its reference direction: scaling `e` by a positive
constant does not change the half-turn it defines. -/
theorem InFirstHalf_smul_pos_left {k : K} (hk : 0 < k) (e w : K × K) :
    InFirstHalf (k • e) w ↔ InFirstHalf e w := by
  have hd : det₂ (k • e) w = k * det₂ e w := det₂_smul_left k e w
  have hdo : dot₂ (k • e) w = k * dot₂ e w := dot₂_smul_left k e w
  have hkz : ∀ x : K, k * x = 0 ↔ x = 0 := by
    intro x
    constructor
    · intro h
      rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' hk.ne'
      · exact h'
    · intro hx; rw [hx, mul_zero]
  simp only [InFirstHalf, hd, hdo, mul_pos_iff_of_pos_left hk, hkz]

/-- The `ℝ × ℝ` cross product agrees with `Nivat.det` on the integer lattice after embedding
via `Nivat.toReal`; this is the bridge letting §8.3/§8.4 use `argLt`/`coneSpan` on `ℤ × ℤ`. -/

theorem det₂_toReal (a b : ℤ × ℤ) :
    det₂ (Nivat.toReal a) (Nivat.toReal b) = ((Nivat.det a b : ℤ) : ℝ) := by
  simp only [det₂, Nivat.toReal, Nivat.det]
  push_cast
  ring

theorem not_InFirstHalf_zero_right (e : K × K) : ¬ InFirstHalf e 0 := by
  simp [InFirstHalf, det₂, dot₂]

theorem not_InFirstHalf_left_zero (w : K × K) : ¬ InFirstHalf 0 w := by
  simp [InFirstHalf, det₂, dot₂]

/-- If `x, z` both lie in the first half relative to `e` and `x`'s ray is not strictly after
`z`'s (`0 ≤ det₂ x z`), then `z` lies in the first half relative to `x`.  The common technical
core of `InFirstHalf.total` and `InFirstHalf.trans_of_mem`: it rules out `x, z` being exact
opposites, which cannot happen since both already lie in the same `e`-half. -/
theorem InFirstHalf_of_det₂_nonneg {e x z : K × K} (he : e ≠ 0)
    (hx : InFirstHalf e x) (hz : InFirstHalf e z) (h : 0 ≤ det₂ x z) : InFirstHalf x z := by
  have hxne : x ≠ 0 := fun h0 => not_InFirstHalf_zero_right e (h0 ▸ hx)
  have hzne : z ≠ 0 := fun h0 => not_InFirstHalf_zero_right e (h0 ▸ hz)
  rcases eq_or_lt_of_le h with heq | hgt
  · refine Or.inr ⟨heq.symm, ?_⟩
    obtain ⟨k, hk⟩ := exists_smul_of_det₂_eq_zero hxne heq.symm
    rcases lt_trichotomy k 0 with hneg | hz0 | hpos
    · exfalso
      have hflip : InFirstHalf e (k • x) ↔ ¬ InFirstHalf e x := InFirstHalf_smul_neg hneg he hxne
      rw [← hk] at hflip
      exact (hflip.mp hz) hx
    · exact absurd (by rw [hk, hz0]; simp) hzne
    · rw [hk, dot₂_smul_right]
      exact mul_pos hpos (dot₂_self_pos hxne)
  · exact Or.inl hgt

/-- **Comparability.**  Two vectors in the same `e`-half are comparable from each other's point
of view: sweeping from `x`, either `z` is met at or after angle `0`, or vice versa.  This is the
"total order within a half-plane" fact that lets `exists_angular_min` find a genuine minimum. -/
theorem InFirstHalf.total {e x y : K × K} (hx : InFirstHalf e x) (hy : InFirstHalf e y) :
    InFirstHalf x y ∨ InFirstHalf y x := by
  have he : e ≠ 0 := fun h0 => not_InFirstHalf_left_zero x (h0 ▸ hx)
  rcases lt_trichotomy (det₂ x y) 0 with hlt | heq | hgt
  · have hyx : 0 ≤ det₂ y x := by have := det₂_comm x y; linarith
    exact Or.inr (InFirstHalf_of_det₂_nonneg he hy hx hyx)
  · exact Or.inl (InFirstHalf_of_det₂_nonneg he hx hy heq.ge)
  · exact Or.inl (InFirstHalf_of_det₂_nonneg he hx hy hgt.le)

/-- **Transitivity of `InFirstHalf` as a relation between rays.**  If `x, y, z` all lie in the
`e`-half and `y` is angularly after `x` while `z` is angularly after `y` (in the sense of
`InFirstHalf` measured from `x`, resp. `y`), then `z` is angularly after `x`.  Together with
`InFirstHalf.total` this makes `InFirstHalf` restricted to a half-plane behave like a total
preorder, which `exists_angular_min` uses to extract a minimum. -/
theorem InFirstHalf.trans_of_mem {e x y z : K × K}
    (hx : InFirstHalf e x) (hy : InFirstHalf e y) (hz : InFirstHalf e z)
    (hxy : InFirstHalf x y) (hyz : InFirstHalf y z) : InFirstHalf x z := by
  have he : e ≠ 0 := fun h0 => not_InFirstHalf_left_zero x (h0 ▸ hx)
  have hxne : x ≠ 0 := fun h0 => not_InFirstHalf_zero_right e (h0 ▸ hx)
  have hex : 0 ≤ det₂ e x := hx.det₂_nonneg
  have hey : 0 ≤ det₂ e y := hy.det₂_nonneg
  have hez : 0 ≤ det₂ e z := hz.det₂_nonneg
  have hxy' : 0 ≤ det₂ x y := hxy.det₂_nonneg
  have hyz' : 0 ≤ det₂ y z := hyz.det₂_nonneg
  rcases eq_or_lt_of_le hey with hey0 | hey0
  · -- `y` lies exactly on the ray `e`.
    have hdoty : 0 < dot₂ e y := by
      rcases hy with h | ⟨_, h⟩
      · exfalso; linarith
      · exact h
    obtain ⟨k, hk⟩ := exists_smul_of_det₂_eq_zero he hey0.symm
    have hkpos : 0 < k := by
      have hprod : 0 < k * dot₂ e e := by
        rw [hk, dot₂_comm e (k • e), dot₂_smul_left, dot₂_comm e e] at hdoty; exact hdoty
      rcases mul_pos_iff.mp hprod with h | h
      · exact h.1
      · exact absurd (dot₂_self_pos he) (not_lt.mpr h.2.le)
    have hxe : 0 ≤ det₂ x e := by
      by_contra hc
      push Not at hc
      have heq2 : det₂ x y = k * det₂ x e := by rw [hk, det₂_smul_right]
      rw [heq2] at hxy'
      exact absurd hxy' (not_le.mpr (mul_neg_of_pos_of_neg hkpos hc))
    have hex0 : det₂ e x = 0 := by
      have hc := det₂_comm x e
      linarith
    have hdotx : 0 < dot₂ e x := by
      rcases hx with h | ⟨_, h⟩
      · exfalso; linarith
      · exact h
    obtain ⟨m, hm⟩ := exists_smul_of_det₂_eq_zero he hex0
    have hmpos : 0 < m := by
      have hprod : 0 < m * dot₂ e e := by
        rw [hm, dot₂_comm e (m • e), dot₂_smul_left, dot₂_comm e e] at hdotx; exact hdotx
      rcases mul_pos_iff.mp hprod with h | h
      · exact h.1
      · exact absurd (dot₂_self_pos he) (not_lt.mpr h.2.le)
    rw [hm]
    exact (InFirstHalf_smul_pos_left hmpos e z).mpr hz
  · -- `0 < det₂ e y`: the generic case, via the Plücker identity.
    have hident := det₂_identity x y z e
    have hxz : 0 ≤ det₂ x z := by
      by_contra hc
      push Not at hc
      have t1 : 0 ≤ det₂ x y * det₂ e z := mul_nonneg hxy' hez
      have t2 : 0 ≤ det₂ y z * det₂ e x := mul_nonneg hyz' hex
      have : det₂ x z * det₂ e y < 0 := mul_neg_of_neg_of_pos hc hey0
      linarith
    exact InFirstHalf_of_det₂_nonneg he hx hz hxz

/-- **Existence of the angular minimum.**  Among a nonempty finite family of vectors all lying
in the same `e`-half, some `w i₀` is angularly first: every other `w i` in the family lies in
the first half measured from `w i₀`.  This is the tool Lemma 8.15 needs to pick out "the first
ray strictly after the boundary ray, in anticlockwise order". -/
theorem exists_angular_min {ι : Type*} [DecidableEq ι] (w : ι → K × K) (e : K × K)
    (S : Finset ι) (hS : S.Nonempty) (hSsub : ∀ i ∈ S, InFirstHalf e (w i)) :
    ∃ i₀ ∈ S, ∀ i ∈ S, InFirstHalf (w i₀) (w i) := by
  classical
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    obtain ⟨a, ha⟩ := hS
    rcases (S.erase a).eq_empty_or_nonempty with hempty | hne
    · refine ⟨a, ha, fun i hi => ?_⟩
      have hia : i = a := by
        by_contra hne'
        have hmem : i ∈ S.erase a := Finset.mem_erase.mpr ⟨hne', hi⟩
        rw [hempty] at hmem
        exact absurd hmem (Finset.notMem_empty _)
      rw [hia]
      exact Or.inr ⟨det₂_self _,
        dot₂_self_pos (fun h0 => not_InFirstHalf_zero_right e (h0 ▸ hSsub a ha))⟩
    · have hsub : S.erase a ⊂ S := Finset.erase_ssubset ha
      obtain ⟨i₀, hi₀, hmin⟩ := ih (S.erase a) hsub hne
        (fun i hi => hSsub i (Finset.mem_of_mem_erase hi))
      have hi₀S : i₀ ∈ S := Finset.mem_of_mem_erase hi₀
      have haS : InFirstHalf e (w a) := hSsub a ha
      have hi₀half : InFirstHalf e (w i₀) := hSsub i₀ hi₀S
      rcases InFirstHalf.total haS hi₀half with hcase | hcase
      · refine ⟨a, ha, fun i hi => ?_⟩
        by_cases hia : i = a
        · rw [hia]
          exact Or.inr ⟨det₂_self _, dot₂_self_pos (fun h0 => not_InFirstHalf_zero_right e (h0 ▸ haS))⟩
        · have hiS' : i ∈ S.erase a := Finset.mem_erase.mpr ⟨hia, hi⟩
          exact InFirstHalf.trans_of_mem haS hi₀half (hSsub i hi) hcase (hmin i hiS')
      · refine ⟨i₀, hi₀S, fun i hi => ?_⟩
        by_cases hia : i = a
        · rw [hia]; exact hcase
        · have hiS' : i ∈ S.erase a := Finset.mem_erase.mpr ⟨hia, hi⟩
          exact hmin i hiS'

/-- Scaling a nonzero vector by `-1` flips which half-plane it lies in, relative to any nonzero
reference direction `e`: `w` and `-w` are never both, and never neither, in the `e`-half. -/
theorem InFirstHalf_neg_iff {e w : K × K} (he : e ≠ 0) (hw : w ≠ 0) :
    InFirstHalf e (-w) ↔ ¬ InFirstHalf e w := by
  have h := InFirstHalf_smul_neg (show (-1 : K) < 0 by norm_num) he hw
  rwa [neg_one_smul] at h

end Nivat
