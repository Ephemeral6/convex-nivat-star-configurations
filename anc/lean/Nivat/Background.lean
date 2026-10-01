/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.Spectrum
import Mathlib.Logic.Relation

/-!
# §3. `A` applied to the colour field yields a doubly periodic background

Formalisation of §3 of *The Convex Nivat Conjecture* (Pan).

The complement of `⋃ᵢ ℝ vᵢ` has `2m` open sectors; on each, `θ` agrees far out with a doubly
periodic *sector background* `β_σ = ∑ᵢ τᵢ^{σᵢ}`.  Sectors adjacent along a ray have
backgrounds `Gᵢ^{ε,L}` and `Gᵢ^{ε,R}` (Lemma 3.0), whose colour fields differ by exceptional
difference fields, hence are identified by `A` (Lemma 3.1).  Since the `2m` sectors form a
cycle, `A e_β` is one and the same doubly periodic `b` for all realised `σ`.  Outside a bounded
set `θ` equals some realised background (Lemma 3.2), so `A e_θ - b` has finite support; (1.1)
and Lemma 1.2 then force it to vanish (Proposition 3.3).

## Main definitions

* `Nivat.piR` — the real linear form `π v` on `ℝ²`.
* `Nivat.StarConfig.Realised` — sign vectors of genuine sectors.
* `Nivat.StarConfig.bgSector` — the sector background `β_σ`.
* `Nivat.StarConfig.bcol`, `Nivat.StarConfig.bpsi` — the doubly periodic background `b`
  and its encoding `b_ψ`.

## Main results

* `Nivat.StarConfig.adjSign_spec` — **Lemma 3.0**.
* `Nivat.StarConfig.act_Aop_ind_bgSector` — **Lemma 3.1**.
* `Nivat.StarConfig.finite_support_act_Aop_ind_sub` — **Lemma 3.2**.
* `Nivat.StarConfig.act_Aop_ind_eq_bcol` — **Proposition 3.3**.

## Status

Complete; no `sorry`.
-/

namespace Nivat

open Finset

/-- The real linear form `π v y = v₁ y₂ - v₂ y₁` on `ℝ²`, extending `pi`. -/
def piR (v : ℤ × ℤ) (y : ℝ × ℝ) : ℝ := (v.1 : ℝ) * y.2 - (v.2 : ℝ) * y.1

@[simp] theorem piR_toReal (v z : ℤ × ℤ) : piR v (toReal z) = (pi v z : ℝ) := by
  simp [piR, toReal, pi, det]

/-- `f(T) g` evaluated at `z` depends only on the values of `g` on the window `z + supp f`.
This is what makes the case analysis of Lemma 3.2 local. -/
theorem act_congr {R : Type*} [CommRing R] (f : LaurentTwo R) {g h : Config R} (z : ℤ × ℤ)
    (hgh : ∀ s ∈ supp f, g (z + s) = h (z + s)) : act f g z = act f h z := by
  simp only [act_apply, Finsupp.sum]
  exact Finset.sum_congr rfl fun s hs => by rw [hgh s hs]

namespace StarConfig

variable {p m : ℕ} [Fact p.Prime] (S : StarConfig p m)

/-! ### §3.1 Realised sectors and adjacent sectors -/

/-- A sign vector `σ ∈ {+, -}^m` is **realised** if it is the sign vector of one of the `2m`
open sectors of `ℝ² \ ⋃ᵢ ℝ vᵢ`.  Paper §3.1. -/
def Realised (ε : Fin m → Bool) : Prop :=
  ∃ y : ℝ × ℝ, ∀ i, if ε i then 0 < piR (S.v i) y else piR (S.v i) y < 0

/-- The sector background `β_σ = ∑ᵢ τᵢ^{σᵢ}`, with `τᵢ^+ = Rᵢ` and `τᵢ^- = Lᵢ`.
Paper §3.1. -/
def bgSector (ε : Fin m → Bool) : Config (ZMod p) :=
  fun z => ∑ i, (if ε i then S.R i z else S.L i z)

omit [Fact p.Prime] in
/-- Every element of `Γ` is a period of the sector background `β_σ`. -/
theorem mem_Per_bgSector {u : ℤ × ℤ} (hu : u ∈ S.Gamma) (ε : Fin m → Bool) :
    u ∈ Per (S.bgSector ε) := by
  rw [mem_Per_iff]
  funext z
  show ∑ i, (if ε i then S.R i (z + u) else S.L i (z + u))
      = ∑ i, (if ε i then S.R i z else S.L i z)
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hεi : ε i
  · rw [if_pos hεi, if_pos hεi]
    exact Per.apply (S.mem_Gamma_iff.mp hu i).2 z
  · rw [if_neg hεi, if_neg hεi]
    exact Per.apply (S.mem_Gamma_iff.mp hu i).1 z

omit [Fact p.Prime] in
theorem bgSector_doublyPeriodic (ε : Fin m → Bool) : DoublyPeriodic (S.bgSector ε) :=
  S.doublyPeriodic_of_Gamma_le fun _ hu => S.mem_Per_bgSector hu ε

omit [Fact p.Prime] in
theorem H_mem_Per_bgSector (j : Fin m) (ε : Fin m → Bool) : S.H j ∈ Per (S.bgSector ε) :=
  S.mem_Per_bgSector (S.H_mem_Gamma j) ε

/-- The sign vector of the sector on side `δ` of the ray `ε vᵢ`: it takes the value `δ` in
coordinate `i`, and `sign πⱼ(ε vᵢ)` in every other coordinate.  Paper Lemma 3.0. -/
def adjSign (i : Fin m) (ε δ : Bool) : Fin m → Bool :=
  fun j => if j = i then δ else decide (0 < pi (S.v j) (if ε then S.v i else -S.v i))

omit [Fact p.Prime] in
theorem pi_neg_right (v w : ℤ × ℤ) : pi v (-w) = -pi v w := by
  simp [pi, det]; ring

omit [Fact p.Prime] in
theorem bgSector_adjSign (i : Fin m) (ε δ : Bool) :
    S.bgSector (S.adjSign i ε δ) = S.Gfield i ε δ := by
  funext z
  show ∑ j, (if S.adjSign i ε δ j then S.R j z else S.L j z)
      = (if δ then S.R i z else S.L i z) + ∑ j ∈ univ.erase i, S.tailSel i j ε z
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  congr 1
  · simp [adjSign]
  · refine Finset.sum_congr rfl fun j hj => ?_
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    have hadj : S.adjSign i ε δ j = decide (0 < pi (S.v j) (if ε then S.v i else -S.v i)) := by
      simp [adjSign, hji]
    rw [hadj, tailSel]
    have hd : pi (S.v j) (S.v i) ≠ 0 := S.nonparallel j i hji
    cases ε with
    | true =>
      simp only [if_true]
      split_ifs <;> rfl
    | false =>
      have hcond : (if (false : Bool) then S.v i else -S.v i) = -S.v i := rfl
      rw [hcond, pi_neg_right]
      by_cases h : 0 < pi (S.v j) (S.v i)
      · have h2 : ¬ (0 < -pi (S.v j) (S.v i)) := by omega
        simp only [h2, decide_false, h, decide_true]
        simp
      · have h2 : 0 < -pi (S.v j) (S.v i) := by omega
        simp only [h2, decide_true, h, decide_false]
        simp

omit [Fact p.Prime] in
theorem realised_adjSign (i : Fin m) (ε δ : Bool) : S.Realised (S.adjSign i ε δ) := by
  obtain ⟨u, hu⟩ := pi_surjective (S.primitive i) (if δ then 1 else -1)
  have hCpos : (0:ℤ) < 1 + ∑ j, |pi (S.v j) u| := by
    have := Finset.sum_nonneg (s := (univ : Finset (Fin m))) (f := fun j => |pi (S.v j) u|)
      (fun j _ => abs_nonneg _)
    linarith
  set C : ℤ := 1 + ∑ j, |pi (S.v j) u| with hC
  refine ⟨toReal (C • (if ε then S.v i else -S.v i) + u), fun k => ?_⟩
  rw [piR_toReal, pi_add, pi_smul]
  have hwi : pi (S.v i) (if ε then S.v i else -S.v i) = 0 := by
    rcases ε with _ | _
    · show pi (S.v i) (-S.v i) = 0
      rw [pi_neg_right]; simp [pi]
    · show pi (S.v i) (S.v i) = 0
      simp [pi]
  by_cases hki : k = i
  · rw [hki, hwi, mul_zero, zero_add, hu]
    have hadj : S.adjSign i ε δ i = δ := by simp [adjSign]
    rw [hadj]
    rcases δ with _ | _ <;> norm_num
  · have hane : pi (S.v k) (if ε then S.v i else -S.v i) ≠ 0 := by
      rcases ε with _ | _
      · show pi (S.v k) (-S.v i) ≠ 0
        rw [pi_neg_right]
        exact neg_ne_zero.mpr (S.nonparallel k i hki)
      · show pi (S.v k) (S.v i) ≠ 0
        exact S.nonparallel k i hki
    have hble : |pi (S.v k) u| ≤ C - 1 := by
      have hmem := Finset.single_le_sum (f := fun j : Fin m => |pi (S.v j) u|)
        (fun j _ => abs_nonneg _) (Finset.mem_univ k)
      omega
    have hadjk : S.adjSign i ε δ k = decide (0 < pi (S.v k) (if ε then S.v i else -S.v i)) := by
      simp [adjSign, hki]
    rw [hadjk]
    rcases lt_or_gt_of_ne hane with ha | ha
    · have hfalse : decide (0 < pi (S.v k) (if ε then S.v i else -S.v i)) = false :=
        decide_eq_false (not_lt.mpr ha.le)
      rw [hfalse]
      simp only [Bool.false_eq_true, if_false]
      have h1 : pi (S.v k) (if ε then S.v i else -S.v i) ≤ -1 := by linarith
      have : C * pi (S.v k) (if ε then S.v i else -S.v i) + pi (S.v k) u < 0 := by
        nlinarith [abs_le.mp hble]
      exact_mod_cast this
    · have htrue : decide (0 < pi (S.v k) (if ε then S.v i else -S.v i)) = true :=
        decide_eq_true ha
      rw [htrue]
      simp only [if_true]
      have h1 : 1 ≤ pi (S.v k) (if ε then S.v i else -S.v i) := by linarith
      have : 0 < C * pi (S.v k) (if ε then S.v i else -S.v i) + pi (S.v k) u := by
        nlinarith [abs_le.mp hble]
      exact_mod_cast this

omit [Fact p.Prime] in
/-- **Lemma 3.0.**  The two sectors adjacent along the ray `ε vᵢ` have realised sign vectors
differing exactly in coordinate `i`, and their backgrounds are exactly `Gᵢ^{ε,L}` and
`Gᵢ^{ε,R}`. -/
theorem adjSign_spec (i : Fin m) (ε δ : Bool) :
    S.Realised (S.adjSign i ε δ) ∧ S.bgSector (S.adjSign i ε δ) = S.Gfield i ε δ := by
  exact ⟨S.realised_adjSign i ε δ, S.bgSector_adjSign i ε δ⟩

/-- Two realised sign vectors are **ray-adjacent** if they are the two sides of a common
ray `ε vᵢ`.  Paper Lemma 3.0. -/
def AdjRay (ε₁ ε₂ : Fin m → Bool) : Prop :=
  ∃ (i : Fin m) (ε : Bool),
    (ε₁ = S.adjSign i ε true ∧ ε₂ = S.adjSign i ε false) ∨
    (ε₁ = S.adjSign i ε false ∧ ε₂ = S.adjSign i ε true)

/-- Point on the segment from `z` to `q` at parameter `s`. -/
noncomputable def segPt (z q : ℝ × ℝ) (s : ℝ) : ℝ × ℝ := ((1 - s) * z.1 + s * q.1, (1 - s) * z.2 + s * q.2)

omit [Fact p.Prime] in
theorem piR_segPt (v : ℤ × ℤ) (z q : ℝ × ℝ) (s : ℝ) :
    piR v (segPt z q s) = (1 - s) * piR v z + s * piR v q := by
  simp [piR, segPt]; ring

omit [Fact p.Prime] in
theorem segPt_one (z q : ℝ × ℝ) : segPt z q 1 = q := by
  simp [segPt]

omit [Fact p.Prime] in
theorem segPt_comp (z q : ℝ × ℝ) (s t : ℝ) :
    segPt z (segPt z q t) s = segPt z q (s * t) := by
  simp only [segPt]
  exact Prod.ext (by ring) (by ring)

omit [Fact p.Prime] in
theorem exists_smul_of_piR_eq_zero {v : ℤ × ℤ} (hv : v ≠ 0) {y : ℝ × ℝ} (h : piR v y = 0) :
    ∃ c : ℝ, y = (c * v.1, c * v.2) := by
  have hkey : (v.1 : ℝ) * y.2 = (v.2 : ℝ) * y.1 := by
    have := h
    simp only [piR] at this
    linarith
  by_cases hv1 : v.1 ≠ 0
  · refine ⟨y.1 / v.1, ?_⟩
    have hv1' : (v.1 : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hv1
    refine Prod.ext (by field_simp) ?_
    field_simp
    linarith
  · have hv2 : v.2 ≠ 0 := by
      rcases v with ⟨v1, v2⟩
      simp only [ne_eq, not_not] at hv1
      subst hv1
      simpa using hv
    refine ⟨y.2 / v.2, ?_⟩
    have hv2' : (v.2 : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hv2
    refine Prod.ext ?_ (by field_simp)
    field_simp
    linarith

/-- The indices `k ≠ i` at which `q` and `z` lie on opposite (weakly) sides of `ℝ vₖ`. -/
noncomputable def defect (z q : ℝ × ℝ) (i : Fin m) : Finset (Fin m) :=
  (univ.erase i).filter (fun k => ¬ (0 < piR (S.v k) q * piR (S.v k) z))

omit [Fact p.Prime] in
theorem exists_defect_eq_empty (z : ℝ × ℝ) (hz : ∀ k, piR (S.v k) z ≠ 0) :
    ∀ (n : ℕ) (i : Fin m) (q : ℝ × ℝ), q ≠ 0 → piR (S.v i) q = 0 → (S.defect z q i).card ≤ n →
    ∃ (i₀ : Fin m) (s : ℝ), 0 < s ∧ s ≤ 1 ∧
      piR (S.v i₀) (segPt z q s) = 0 ∧ segPt z q s ≠ 0 ∧
      S.defect z (segPt z q s) i₀ = ∅ := by
  intro n
  induction n with
  | zero =>
    intro i q hq0 hqi hcard
    have hemp : S.defect z q i = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
    exact ⟨i, 1, one_pos, le_refl 1, by rw [segPt_one]; exact hqi,
      by rw [segPt_one]; exact hq0, by rw [segPt_one]; exact hemp⟩
  | succ n ih =>
    intro i q hq0 hqi hcard
    by_cases hempty : S.defect z q i = ∅
    · exact ⟨i, 1, one_pos, le_refl 1, by rw [segPt_one]; exact hqi,
        by rw [segPt_one]; exact hq0, by rw [segPt_one]; exact hempty⟩
    · obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
      have hji : j ≠ i := Finset.ne_of_mem_erase (Finset.mem_filter.mp hj).1
      have hjdef : ¬ (0 < piR (S.v j) q * piR (S.v j) z) := (Finset.mem_filter.mp hj).2
      -- q is a multiple of S.v i, with nonzero coefficient
      obtain ⟨c, hc⟩ := exists_smul_of_piR_eq_zero (S.primitive i).ne_zero hqi
      have hcne : c ≠ 0 := by
        rintro rfl
        apply hq0
        rw [hc]; simp
      have hbne : piR (S.v j) q ≠ 0 := by
        have : piR (S.v j) q = c * (pi (S.v j) (S.v i) : ℝ) := by
          rw [hc]; simp [piR]; ring
        rw [this]
        exact mul_ne_zero hcne (Int.cast_ne_zero.mpr (S.nonparallel j i hji))
      have hane : piR (S.v j) z ≠ 0 := hz j
      set a : ℝ := piR (S.v j) z with ha_def
      set b : ℝ := piR (S.v j) q with hb_def
      have hab : a * b < 0 := by
        have h1 : a * b ≤ 0 := by rw [mul_comm]; exact not_lt.mp hjdef
        exact lt_of_le_of_ne h1 (mul_ne_zero hane hbne)
      have habne : a ≠ b := fun h => by rw [h] at hab; nlinarith [sq_nonneg b]
      set s : ℝ := a / (a - b) with hs_def
      have hscomp : s * (a - b) = a := div_mul_cancel₀ a (sub_ne_zero.mpr habne)
      have hs01 : 0 < s ∧ s < 1 := by
        rcases lt_trichotomy a 0 with ha0 | ha0 | ha0
        · have hb0 : 0 < b := by nlinarith
          have hd : a - b < 0 := by linarith
          exact ⟨div_pos_of_neg_of_neg ha0 hd, (div_lt_one_of_neg hd).mpr (by linarith)⟩
        · exact absurd ha0 hane
        · have hb0 : b < 0 := by nlinarith
          have hd : 0 < a - b := by linarith
          exact ⟨div_pos ha0 hd, (div_lt_one hd).mpr (by linarith)⟩
      set q' : ℝ × ℝ := segPt z q s with hq'_def
      have hseg0 : piR (S.v j) q' = 0 := by
        rw [hq'_def, piR_segPt, ← ha_def, ← hb_def]
        nlinarith [hscomp]
      have hq'ne0 : q' ≠ 0 := by
        intro hq'0
        apply hz i
        have hpi0 : piR (S.v i) q' = 0 := by rw [hq'0]; simp [piR]
        rw [hq'_def, piR_segPt, hqi, mul_zero, add_zero] at hpi0
        have h1s : (1 - s) ≠ 0 := by linarith [hs01.2]
        exact (mul_eq_zero.mp hpi0).resolve_left h1s
      have hsub : S.defect z q' j ⊆ S.defect z q i := by
        intro k hk
        have hkj : k ≠ j := Finset.ne_of_mem_erase (Finset.mem_filter.mp hk).1
        have hkdef : ¬ (0 < piR (S.v k) q' * piR (S.v k) z) := (Finset.mem_filter.mp hk).2
        have hki : k ≠ i := by
          rintro rfl
          apply hkdef
          have heq0 : piR (S.v k) q' = (1 - s) * piR (S.v k) z := by
            rw [hq'_def, piR_segPt, hqi, mul_zero, add_zero]
          rw [heq0]
          have hzk := hz k
          nlinarith [hs01.1, hs01.2, mul_self_pos.mpr hzk]
        refine Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hki, Finset.mem_univ k⟩, ?_⟩
        intro hcontra
        apply hkdef
        have heq1 : piR (S.v k) q' = (1 - s) * piR (S.v k) z + s * piR (S.v k) q := by
          rw [hq'_def, piR_segPt]
        rw [heq1]
        nlinarith [hs01.1, hs01.2, hz k, mul_self_pos.mpr (hz k)]
      have hjnotin : j ∉ S.defect z q' j :=
        fun h => (Finset.mem_erase.mp (Finset.mem_filter.mp h).1).1 rfl
      have hjin : j ∈ S.defect z q i := hj
      have hssub : S.defect z q' j ⊂ S.defect z q i :=
        Finset.ssubset_iff_of_subset hsub |>.mpr ⟨j, hjin, hjnotin⟩
      have hcard' : (S.defect z q' j).card ≤ n := by
        have := Finset.card_lt_card hssub
        omega
      obtain ⟨i₀, s', hs'0, hs'1, hpi0, hq'0, hdefempty⟩ := ih j q' hq'ne0 hseg0 hcard'
      have heqfinal : segPt z q (s' * s) = segPt z q' s' := by
        rw [hq'_def]; exact (segPt_comp z q s' s).symm
      refine ⟨i₀, s' * s, mul_pos hs'0 hs01.1, ?_, ?_, ?_, ?_⟩
      · have := mul_le_mul hs'1 hs01.2.le hs01.1.le (by norm_num : (0:ℝ) ≤ 1)
        linarith [this]
      · rw [heqfinal]; exact hpi0
      · rw [heqfinal]; exact hq'0
      · rw [heqfinal]; exact hdefempty

omit [Fact p.Prime] in
theorem eq_adjSign_of_defect_empty {y : ℝ × ℝ} {ε : Fin m → Bool}
    (hε : ∀ k, if ε k then 0 < piR (S.v k) y else piR (S.v k) y < 0)
    {q : ℝ × ℝ} (hq0 : q ≠ 0) {i : Fin m} (hqi : piR (S.v i) q = 0)
    (hdef : S.defect y q i = ∅) :
    ∃ e : Bool, ε = S.adjSign i e (ε i) := by
  obtain ⟨c, hc⟩ := exists_smul_of_piR_eq_zero (S.primitive i).ne_zero hqi
  have hcne : c ≠ 0 := by rintro rfl; apply hq0; rw [hc]; simp
  have hqk : ∀ k, piR (S.v k) q = c * (pi (S.v k) (S.v i) : ℝ) := by
    intro k; rw [hc]; simp [piR]; ring
  have hmemall : ∀ k, k ≠ i → 0 < piR (S.v k) q * piR (S.v k) y := by
    intro k hki
    by_contra hcon
    have hk : k ∈ S.defect y q i :=
      Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hki, Finset.mem_univ k⟩, hcon⟩
    rw [hdef] at hk
    simp at hk
  rcases lt_or_gt_of_ne hcne with hc0 | hc0
  · refine ⟨false, ?_⟩
    funext k
    by_cases hki : k = i
    · simp [adjSign, hki]
    · have hmem := hmemall k hki
      rw [hqk k] at hmem
      have hdne : (pi (S.v k) (S.v i) : ℝ) ≠ 0 := Int.cast_ne_zero.mpr (S.nonparallel k i hki)
      have hadjk : S.adjSign i false (ε i) k = decide (0 < pi (S.v k) (-S.v i)) := by
        simp [adjSign, hki]
      rw [hadjk, pi_neg_right]
      generalize hεk : ε k = b at hmem ⊢
      have hPcond : (if b then 0 < piR (S.v k) y else piR (S.v k) y < 0) := hεk ▸ hε k
      cases b with
      | true =>
        simp only [if_true] at hPcond
        have hdneg : (pi (S.v k) (S.v i) : ℝ) < 0 := by
          rcases lt_or_gt_of_ne hdne with hneg | hpos
          · exact hneg
          · exfalso
            have hcd : c * (pi (S.v k) (S.v i) : ℝ) < 0 := mul_neg_of_neg_of_pos hc0 hpos
            nlinarith [mul_neg_of_neg_of_pos hcd hPcond]
        have h2 : (0:ℤ) < -pi (S.v k) (S.v i) := by
          have : (0:ℝ) < -pi (S.v k) (S.v i) := by linarith
          exact_mod_cast this
        exact (decide_eq_true h2).symm
      | false =>
        have hdpos : (0:ℝ) < pi (S.v k) (S.v i) := by
          rcases lt_or_gt_of_ne hdne with hneg | hpos
          · exfalso
            have hcd : 0 < c * (pi (S.v k) (S.v i) : ℝ) := mul_pos_of_neg_of_neg hc0 hneg
            nlinarith [mul_neg_of_pos_of_neg hcd hPcond]
          · exact hpos
        have h2 : ¬ (0 < -pi (S.v k) (S.v i)) := by
          intro hcontra
          have : (0:ℝ) < -pi (S.v k) (S.v i) := by exact_mod_cast hcontra
          linarith
        exact (decide_eq_false h2).symm
  · refine ⟨true, ?_⟩
    funext k
    by_cases hki : k = i
    · simp [adjSign, hki]
    · have hmem := hmemall k hki
      rw [hqk k] at hmem
      have hdne : (pi (S.v k) (S.v i) : ℝ) ≠ 0 := Int.cast_ne_zero.mpr (S.nonparallel k i hki)
      have hadjk : S.adjSign i true (ε i) k = decide (0 < pi (S.v k) (S.v i)) := by
        simp [adjSign, hki]
      rw [hadjk]
      generalize hεk : ε k = b at hmem ⊢
      have hPcond : (if b then 0 < piR (S.v k) y else piR (S.v k) y < 0) := hεk ▸ hε k
      cases b with
      | true =>
        simp only [if_true] at hPcond
        have hdpos : (0:ℝ) < pi (S.v k) (S.v i) := by
          rcases lt_or_gt_of_ne hdne with hneg | hpos
          · exfalso
            have hcd : c * (pi (S.v k) (S.v i) : ℝ) < 0 := mul_neg_of_pos_of_neg hc0 hneg
            nlinarith [mul_neg_of_neg_of_pos hcd hPcond]
          · exact hpos
        have h2 : (0:ℤ) < pi (S.v k) (S.v i) := by exact_mod_cast hdpos
        exact (decide_eq_true h2).symm
      | false =>
        have hdneg : pi (S.v k) (S.v i) < (0:ℝ) := by
          rcases lt_or_gt_of_ne hdne with hneg | hpos
          · exact hneg
          · exfalso
            have hcd : 0 < c * (pi (S.v k) (S.v i) : ℝ) := mul_pos hc0 hpos
            nlinarith [mul_neg_of_pos_of_neg hcd hPcond]
        have h2 : ¬ (0 < pi (S.v k) (S.v i)) := by
          intro hcontra
          have : (0:ℝ) < pi (S.v k) (S.v i) := by exact_mod_cast hcontra
          linarith
        exact (decide_eq_false h2).symm

omit [Fact p.Prime] in
theorem ne_zero_of_realised {ε : Fin m → Bool} {y : ℝ × ℝ}
    (hy : ∀ k, if ε k then 0 < piR (S.v k) y else piR (S.v k) y < 0) (k : Fin m) :
    piR (S.v k) y ≠ 0 := by
  have h := hy k
  cases hb : ε k with
  | true => rw [hb] at h; exact ne_of_gt h
  | false => rw [hb] at h; exact ne_of_lt h

omit [Fact p.Prime] in
/-- The straight segment from `z` to `q` (both off every ray) either agrees in sign
everywhere, or has a first crossing point which lies on some ray `j` that already
disagrees between `z` and `q`, with no other ray crossed yet. -/
theorem exists_crossing {z q : ℝ × ℝ}
    (hz : ∀ k, piR (S.v k) z ≠ 0) (hq : ∀ k, piR (S.v k) q ≠ 0)
    (hnc : ¬ ∃ c : ℝ, c < 0 ∧ q = (c * z.1, c * z.2))
    (hD : ∃ k, piR (S.v k) z * piR (S.v k) q < 0) :
    ∃ (j : Fin m) (s : ℝ), 0 < s ∧ s < 1 ∧ piR (S.v j) z * piR (S.v j) q < 0 ∧
      piR (S.v j) (segPt z q s) = 0 ∧ segPt z q s ≠ 0 ∧
      S.defect z (segPt z q s) j = ∅ := by
  classical
  set D : Finset (Fin m) := univ.filter (fun k => piR (S.v k) z * piR (S.v k) q < 0) with hD_def
  have hDne : D.Nonempty := by
    obtain ⟨k, hk⟩ := hD
    exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ k, hk⟩⟩
  set sfun : Fin m → ℝ := fun k => piR (S.v k) z / (piR (S.v k) z - piR (S.v k) q) with hsfun_def
  obtain ⟨j, hjD, hjmin⟩ := Finset.exists_min_image D sfun hDne
  have hjab : piR (S.v j) z * piR (S.v j) q < 0 := (Finset.mem_filter.mp hjD).2
  set a : ℝ := piR (S.v j) z with ha_def
  set b : ℝ := piR (S.v j) q with hb_def
  set s : ℝ := a / (a - b) with hs_def
  have habne : a ≠ b := fun h => by rw [h] at hjab; nlinarith [sq_nonneg b]
  have hscomp : s * (a - b) = a := div_mul_cancel₀ a (sub_ne_zero.mpr habne)
  have hs01 : 0 < s ∧ s < 1 := by
    rcases lt_trichotomy a 0 with ha0 | ha0 | ha0
    · have hb0 : 0 < b := by nlinarith
      have hd : a - b < 0 := by linarith
      exact ⟨div_pos_of_neg_of_neg ha0 hd, (div_lt_one_of_neg hd).mpr (by linarith)⟩
    · exact absurd ha0 (hz j)
    · have hb0 : b < 0 := by nlinarith
      have hd : 0 < a - b := by linarith
      exact ⟨div_pos ha0 hd, (div_lt_one hd).mpr (by linarith)⟩
  have hseg0 : piR (S.v j) (segPt z q s) = 0 := by
    rw [piR_segPt, ← ha_def, ← hb_def]; nlinarith [hscomp]
  have hsegne : segPt z q s ≠ 0 := by
    intro hp0
    have h1 : (1 - s) * z.1 + s * q.1 = 0 := by
      have := congrArg Prod.fst hp0; simpa [segPt] using this
    have h2 : (1 - s) * z.2 + s * q.2 = 0 := by
      have := congrArg Prod.snd hp0; simpa [segPt] using this
    have hsne : s ≠ 0 := ne_of_gt hs01.1
    apply hnc
    refine ⟨-(1 - s) / s, div_neg_of_neg_of_pos (by linarith [hs01.2]) hs01.1, ?_⟩
    apply Prod.ext
    · field_simp
      linarith [h1]
    · field_simp
      linarith [h2]
  refine ⟨j, s, hs01.1, hs01.2, hjab, hseg0, hsegne, ?_⟩
  rw [Finset.eq_empty_iff_forall_notMem]
  intro k hk
  have hkj : k ≠ j := Finset.ne_of_mem_erase (Finset.mem_filter.mp hk).1
  have hkdef : ¬ (0 < piR (S.v k) (segPt z q s) * piR (S.v k) z) :=
    (Finset.mem_filter.mp hk).2
  by_cases hkD : k ∈ D
  · have hsk_ge : s ≤ sfun k := hjmin k hkD
    have hkab : piR (S.v k) z * piR (S.v k) q < 0 := (Finset.mem_filter.mp hkD).2
    set ak : ℝ := piR (S.v k) z with hak_def
    set bk : ℝ := piR (S.v k) q with hbk_def
    have hakne : ak ≠ bk := fun h => by rw [h] at hkab; nlinarith [sq_nonneg bk]
    have hne_sk : s ≠ sfun k := by
      intro heq
      have hscompk : s * (ak - bk) = ak := by
        rw [heq, hsfun_def]; exact div_mul_cancel₀ ak (sub_ne_zero.mpr hakne)
      have hsk_eq : piR (S.v k) (segPt z q s) = 0 := by
        rw [piR_segPt, ← hak_def, ← hbk_def]; nlinarith [hscompk]
      obtain ⟨cc, hcc⟩ := exists_smul_of_piR_eq_zero (S.primitive j).ne_zero hseg0
      obtain ⟨cc2, hcc2⟩ := exists_smul_of_piR_eq_zero (S.primitive k).ne_zero hsk_eq
      have hccne : cc ≠ 0 := by intro h; apply hsegne; rw [hcc, h]; simp
      have hcc2ne : cc2 ≠ 0 := by intro h; apply hsegne; rw [hcc2, h]; simp
      have heqvec : (cc * (S.v j).1, cc * (S.v j).2) = ((cc2 : ℝ) * (S.v k).1, cc2 * (S.v k).2) := by
        rw [← hcc, ← hcc2]
      have h1 : cc * ((S.v j).1 : ℝ) = cc2 * (S.v k).1 := (Prod.mk.injEq .. ▸ heqvec).1
      have h2 : cc * ((S.v j).2 : ℝ) = cc2 * (S.v k).2 := (Prod.mk.injEq .. ▸ heqvec).2
      have hpar : cc * (pi (S.v j) (S.v k) : ℝ) = 0 := by
        have hcast : (pi (S.v j) (S.v k) : ℝ)
            = ((S.v j).1 : ℝ) * (S.v k).2 - ((S.v j).2 : ℝ) * (S.v k).1 := by
          simp [pi, det]
        rw [hcast]; linear_combination (S.v k).2 * h1 - (S.v k).1 * h2
      have hpar0 : (pi (S.v j) (S.v k) : ℝ) = 0 := (mul_eq_zero.mp hpar).resolve_left hccne
      exact S.nonparallel j k (Ne.symm hkj) (by exact_mod_cast hpar0)
    have hslt : s < sfun k := lt_of_le_of_ne hsk_ge hne_sk
    rw [hsfun_def] at hslt
    dsimp only at hslt
    apply hkdef
    rw [piR_segPt, ← hak_def, ← hbk_def]
    rcases lt_trichotomy ak 0 with hak0 | hak0 | hak0
    · have hbk0 : 0 < bk := by nlinarith
      have hcneg : ak - bk < 0 := by linarith
      have hdmc : ak / (ak - bk) * (ak - bk) = ak := div_mul_cancel₀ ak (sub_ne_zero.mpr hakne)
      have hmul : ak / (ak - bk) * (ak - bk) < s * (ak - bk) :=
        mul_lt_mul_of_neg_right hslt hcneg
      rw [hdmc] at hmul
      nlinarith [hmul]
    · exact absurd hak0 (hz k)
    · have hbk0 : bk < 0 := by nlinarith
      have hcpos : 0 < ak - bk := by linarith
      have hdmc : ak / (ak - bk) * (ak - bk) = ak := div_mul_cancel₀ ak (sub_ne_zero.mpr hakne)
      have hmul : s * (ak - bk) < ak / (ak - bk) * (ak - bk) :=
        mul_lt_mul_of_pos_right hslt hcpos
      rw [hdmc] at hmul
      nlinarith [hmul]
  · have hkab : ¬ (piR (S.v k) z * piR (S.v k) q < 0) := fun h =>
      hkD (Finset.mem_filter.mpr ⟨Finset.mem_univ k, h⟩)
    push Not at hkab
    have hkzne := hz k
    have hkqne := hq k
    apply hkdef
    rw [piR_segPt]
    rcases lt_trichotomy (piR (S.v k) z) 0 with hzlt | hzlt | hzlt
    · have hqlt : piR (S.v k) q < 0 := by
        rcases lt_trichotomy (piR (S.v k) q) 0 with h | h | h
        · exact h
        · exact absurd h hkqne
        · nlinarith
      nlinarith [mul_pos (show (0:ℝ) < 1 - s by linarith [hs01.2]) (mul_pos_of_neg_of_neg hzlt hzlt),
        mul_pos hs01.1 (mul_pos_of_neg_of_neg hzlt hqlt)]
    · exact absurd hzlt hkzne
    · have hqgt : 0 < piR (S.v k) q := by
        rcases lt_trichotomy (piR (S.v k) q) 0 with h | h | h
        · nlinarith
        · exact absurd h hkqne
        · exact h
      nlinarith [mul_pos (show (0:ℝ) < 1 - s by linarith [hs01.2]) (mul_pos hzlt hzlt),
        mul_pos hs01.1 (mul_pos hzlt hqgt)]

omit [Fact p.Prime] in
/-- From `ε₁ = adjSign i₀ e (ε₁ i₀)` and a coordinate `i₀` on which `ε₁,ε₂` differ, produce
the ray-adjacent neighbour of `ε₁` across `i₀`, and show it strictly decreases the Hamming
distance to `ε₂`. -/
theorem step_of_eq_adjSign {ε₁ ε₂ : Fin m → Bool} {i₀ : Fin m} {e : Bool}
    (hi0 : ε₁ i₀ ≠ ε₂ i₀) (heq : ε₁ = S.adjSign i₀ e (ε₁ i₀)) :
    ∃ ε₃ : Fin m → Bool, S.Realised ε₃ ∧ S.AdjRay ε₁ ε₃ ∧
      (univ.filter (fun j => ε₃ j ≠ ε₂ j)).card
        = (univ.filter (fun j => ε₁ j ≠ ε₂ j)).card - 1 := by
  cases hb : ε₁ i₀ with
  | true =>
    refine ⟨S.adjSign i₀ e false, S.realised_adjSign i₀ e false, ⟨i₀, e, Or.inl ⟨?_, rfl⟩⟩, ?_⟩
    · rw [heq, hb]
    have hagree : ∀ j, j ≠ i₀ → ε₁ j = S.adjSign i₀ e false j := by
      intro j hj
      have h1 : ε₁ j = S.adjSign i₀ e true j := by rw [heq, hb]
      have h2 : S.adjSign i₀ e true j = S.adjSign i₀ e false j := by simp [adjSign, hj]
      rw [h1, h2]
    have hi0e : S.adjSign i₀ e false i₀ = ε₂ i₀ := by
      have h3 : S.adjSign i₀ e false i₀ = false := by simp [adjSign]
      rw [h3]
      rw [hb] at hi0
      cases h2 : ε₂ i₀ with
      | true => exact absurd h2 (Ne.symm hi0)
      | false => rfl
    have hset : univ.filter (fun j => S.adjSign i₀ e false j ≠ ε₂ j)
        = (univ.filter (fun j => ε₁ j ≠ ε₂ j)).erase i₀ := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
      by_cases hj : j = i₀
      · subst hj; simp [hi0e]
      · rw [← hagree j hj]; exact ⟨fun h => ⟨hj, h⟩, fun h => h.2⟩
    rw [hset, Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ i₀, hi0⟩)]
  | false =>
    refine ⟨S.adjSign i₀ e true, S.realised_adjSign i₀ e true, ⟨i₀, e, Or.inr ⟨?_, rfl⟩⟩, ?_⟩
    · rw [heq, hb]
    have hagree : ∀ j, j ≠ i₀ → ε₁ j = S.adjSign i₀ e true j := by
      intro j hj
      have h1 : ε₁ j = S.adjSign i₀ e false j := by rw [heq, hb]
      have h2 : S.adjSign i₀ e false j = S.adjSign i₀ e true j := by simp [adjSign, hj]
      rw [h1, h2]
    have hi0e : S.adjSign i₀ e true i₀ = ε₂ i₀ := by
      have h3 : S.adjSign i₀ e true i₀ = true := by simp [adjSign]
      rw [h3]
      rw [hb] at hi0
      cases h2 : ε₂ i₀ with
      | true => rfl
      | false => exact absurd h2.symm hi0
    have hset : univ.filter (fun j => S.adjSign i₀ e true j ≠ ε₂ j)
        = (univ.filter (fun j => ε₁ j ≠ ε₂ j)).erase i₀ := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
      by_cases hj : j = i₀
      · subst hj; simp [hi0e]
      · rw [← hagree j hj]; exact ⟨fun h => ⟨hj, h⟩, fun h => h.2⟩
    rw [hset, Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ i₀, hi0⟩)]

omit [Fact p.Prime] in
/-- One step of ray-adjacent descent: given two distinct realised sign vectors, produces a
realised neighbour of `ε₁` across some ray, which is strictly closer (in Hamming distance)
to `ε₂`. -/
theorem exists_step {ε₁ ε₂ : Fin m → Bool} (hne : ε₁ ≠ ε₂)
    {y1 y2 : ℝ × ℝ}
    (hy1 : ∀ k, if ε₁ k then 0 < piR (S.v k) y1 else piR (S.v k) y1 < 0)
    (hy2 : ∀ k, if ε₂ k then 0 < piR (S.v k) y2 else piR (S.v k) y2 < 0) :
    ∃ ε₃ : Fin m → Bool, S.Realised ε₃ ∧ S.AdjRay ε₁ ε₃ ∧
      (univ.filter (fun j => ε₃ j ≠ ε₂ j)).card
        = (univ.filter (fun j => ε₁ j ≠ ε₂ j)).card - 1 := by
  have hforward : ∀ k, ε₁ k ≠ ε₂ k → piR (S.v k) y1 * piR (S.v k) y2 < 0 := by
    intro k hk
    have h1 := hy1 k
    have h2 := hy2 k
    cases hb1 : ε₁ k with
    | true =>
      rw [hb1] at hk
      have hp1 : 0 < piR (S.v k) y1 := by rw [hb1] at h1; simpa using h1
      have hb2 : ε₂ k = false := by
        cases hc : ε₂ k with
        | true => exact absurd hc.symm hk
        | false => rfl
      have hp2 : piR (S.v k) y2 < 0 := by rw [hb2] at h2; simpa using h2
      nlinarith
    | false =>
      rw [hb1] at hk
      have hp1 : piR (S.v k) y1 < 0 := by rw [hb1] at h1; simpa using h1
      have hb2 : ε₂ k = true := by
        cases hc : ε₂ k with
        | true => rfl
        | false => exact absurd hc.symm hk
      have hp2 : 0 < piR (S.v k) y2 := by rw [hb2] at h2; simpa using h2
      nlinarith
  have hreverse : ∀ k, piR (S.v k) y1 * piR (S.v k) y2 < 0 → ε₁ k ≠ ε₂ k := by
    intro k hk h
    have h1 := hy1 k
    have h2 := hy2 k
    rw [h] at h1
    cases hb2 : ε₂ k with
    | true =>
      have hp1 : 0 < piR (S.v k) y1 := by rw [hb2] at h1; simpa using h1
      have hp2 : 0 < piR (S.v k) y2 := by rw [hb2] at h2; simpa using h2
      nlinarith
    | false =>
      have hp1 : piR (S.v k) y1 < 0 := by rw [hb2] at h1; simpa using h1
      have hp2 : piR (S.v k) y2 < 0 := by rw [hb2] at h2; simpa using h2
      nlinarith
  have hex : ∃ k, ε₁ k ≠ ε₂ k := by
    by_contra hc
    push Not at hc
    exact hne (funext hc)
  have hz1 : ∀ k, piR (S.v k) y1 ≠ 0 := ne_zero_of_realised S hy1
  have hz2 : ∀ k, piR (S.v k) y2 ≠ 0 := ne_zero_of_realised S hy2
  by_cases hdeg : ∃ c : ℝ, c < 0 ∧ y2 = (c * y1.1, c * y1.2)
  · obtain ⟨c, hc0, hc⟩ := hdeg
    have hy2k : ∀ k, piR (S.v k) y2 = c * piR (S.v k) y1 := by
      intro k; rw [hc]; simp [piR]; ring
    have hne_all : ∀ k, ε₁ k ≠ ε₂ k := by
      intro k
      apply hreverse k
      have h1 := hz1 k
      rw [hy2k k]
      have hzsq : 0 < piR (S.v k) y1 * piR (S.v k) y1 := mul_self_pos.mpr h1
      nlinarith [mul_neg_of_neg_of_pos hc0 hzsq]
    set i : Fin m := ⟨0, lt_of_lt_of_le (by norm_num) S.two_le⟩ with hi_def
    set q : ℝ × ℝ := toReal (S.v i) with hq_def
    have hq0 : q ≠ 0 := by
      rw [hq_def]
      intro h
      apply (S.primitive i).ne_zero
      have h1 : ((S.v i).1 : ℝ) = 0 := by
        have := congrArg Prod.fst h; simpa [toReal] using this
      have h2 : ((S.v i).2 : ℝ) = 0 := by
        have := congrArg Prod.snd h; simpa [toReal] using this
      exact Prod.ext (by exact_mod_cast h1) (by exact_mod_cast h2)
    have hqi : piR (S.v i) q = 0 := by
      rw [hq_def, piR_toReal]
      have hvv : pi (S.v i) (S.v i) = (S.v i).1 * (S.v i).2 - (S.v i).2 * (S.v i).1 := by
        simp [pi, det]
      have hzero : pi (S.v i) (S.v i) = 0 := by rw [hvv]; ring
      exact_mod_cast hzero
    obtain ⟨i₀, s, hs0, hs1, hpi0, hqne, hdefe⟩ :=
      S.exists_defect_eq_empty y1 hz1 (S.defect y1 q i).card i q hq0 hqi (le_refl _)
    obtain ⟨e, heq⟩ := eq_adjSign_of_defect_empty S hy1 hqne hpi0 hdefe
    exact step_of_eq_adjSign S (hne_all i₀) heq
  · have hD : ∃ k, piR (S.v k) y1 * piR (S.v k) y2 < 0 := by
      obtain ⟨k, hk⟩ := hex
      exact ⟨k, hforward k hk⟩
    obtain ⟨j, s, hs0, hs1, hjab, hseg0, hsegne, hdefe⟩ :=
      S.exists_crossing hz1 hz2 hdeg hD
    obtain ⟨e, heq⟩ := eq_adjSign_of_defect_empty S hy1 hsegne hseg0 hdefe
    exact step_of_eq_adjSign S (hreverse j hjab) heq

omit [Fact p.Prime] in
/-- **Lemma 3.0.**  In the angular order the `2m` sectors form a `2m`-cycle under ray
adjacency; in particular the adjacency graph on realised sign vectors is connected. -/
theorem realised_connected {ε₁ ε₂ : Fin m → Bool} (h₁ : S.Realised ε₁) (h₂ : S.Realised ε₂) :
    Relation.ReflTransGen S.AdjRay ε₁ ε₂ := by
  obtain ⟨y2, hy2⟩ := h₂
  suffices H : ∀ n : ℕ, ∀ ε : Fin m → Bool, S.Realised ε →
      (univ.filter (fun j => ε j ≠ ε₂ j)).card = n →
      Relation.ReflTransGen S.AdjRay ε ε₂ by
    exact H _ ε₁ h₁ rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro ε hε hcard
    by_cases heq : ε = ε₂
    · rw [heq]
    · obtain ⟨y1, hy1⟩ := hε
      obtain ⟨ε₃, hε₃real, hadj, hcard3⟩ := S.exists_step heq hy1 hy2
      have hpos : 0 < n := by
        rw [← hcard, Finset.card_pos]
        obtain ⟨k, hk⟩ : ∃ k, ε k ≠ ε₂ k := by
          by_contra hc
          push Not at hc
          exact heq (funext hc)
        exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ k, hk⟩⟩
      have hcard3' : (univ.filter (fun j => ε₃ j ≠ ε₂ j)).card = n - 1 := by
        rw [hcard3, hcard]
      have hlt : n - 1 < n := by omega
      exact Relation.ReflTransGen.head hadj (ih (n - 1) hlt ε₃ hε₃real hcard3')

/-- A distinguished index, available since `m ≥ 2`. -/
def idx₀ : Fin m := ⟨0, lt_of_lt_of_le (by norm_num) S.two_le⟩

/-- A second distinguished index, available since `m ≥ 2`. -/
def idx₁ : Fin m := ⟨1, lt_of_lt_of_le (by norm_num) S.two_le⟩

omit [Fact p.Prime] in
theorem idx₀_ne_idx₁ : S.idx₀ ≠ S.idx₁ :=
  Fin.ne_of_val_ne (by show (0 : ℕ) ≠ 1; norm_num)

omit [Fact p.Prime] in
/-- The tangential periods `Hᵢ`, `Hⱼ` are non-parallel for `i ≠ j`, since they are non-zero
multiples of the non-parallel directions `vᵢ`, `vⱼ`. -/
theorem det_H_ne_zero {i j : Fin m} (hij : i ≠ j) : det (S.H i) (S.H j) ≠ 0 := by
  have h : det (S.H i) (S.H j)
      = ((S.kappa i : ℤ) * (S.kappa j : ℤ)) * det (S.v i) (S.v j) := by
    simp only [H, det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  rw [h]
  refine mul_ne_zero (mul_ne_zero ?_ ?_) (S.nonparallel i j hij)
  · exact_mod_cast (S.kappa_pos i).ne'
  · exact_mod_cast (S.kappa_pos j).ne'

/-- A distinguished realised sign vector, used to pin down `b`. -/
def refSign : Fin m → Bool := S.adjSign S.idx₀ true true

omit [Fact p.Prime] in
theorem realised_refSign : S.Realised S.refSign := (S.adjSign_spec S.idx₀ true true).1

/-- The doubly periodic background `b = (b_a) := A(T) e_β` for any realised sector
background `β`.  Paper Lemma 3.1. -/
noncomputable def bcol (a : ZMod p) : Config ℂ :=
  act S.Aop (ind (S.bgSector S.refSign) a)

/-- **Lemma 3.1.**  `A(T) e_{Gᵢ^{ε,R}} = A(T) e_{Gᵢ^{ε,L}}`: the two colour fields differ by
exceptional difference fields, which `Aᵢ(T^{vᵢ})` kills by (P3). -/
theorem act_Aop_ind_Gfield (i : Fin m) (ε : Bool) (a : ZMod p) :
    act S.Aop (ind (S.Gfield i ε true) a) = act S.Aop (ind (S.Gfield i ε false) a) := by
  classical
  -- The two colour fields differ by a difference of exceptional difference fields.
  have hdiff : ind (S.Gfield i ε true) a - ind (S.Gfield i ε false) a
      = S.diffField i ε false a - S.diffField i ε true a := by
    funext z
    show ind (S.Gfield i ε true) a z - ind (S.Gfield i ε false) a z
        = (ind (S.sigma i ε) a z - ind (S.Gfield i ε false) a z)
          - (ind (S.sigma i ε) a z - ind (S.Gfield i ε true) a z)
    ring
  -- `Aᵢ(T^{vᵢ})` kills both of them by (P3).
  have hkill : act (S.Afac i) (ind (S.Gfield i ε true) a - ind (S.Gfield i ε false) a) = 0 := by
    rw [hdiff, act_sub_right, S.act_Afac_diffField i ε false a,
      S.act_Afac_diffField i ε true a, sub_zero]
  rw [← sub_eq_zero, ← act_sub_right, Aop,
    ← Finset.prod_erase_mul _ _ (Finset.mem_univ i), act_mul, hkill, act_zero_right]

/-- **Lemma 3.1.**  `A(T) e_β` is one and the same for every realised sector background. -/
theorem act_Aop_ind_bgSector {ε : Fin m → Bool} (hε : S.Realised ε) (a : ZMod p) :
    act S.Aop (ind (S.bgSector ε) a) = S.bcol a := by
  -- One adjacency step changes nothing, by Lemma 3.0 and Lemma 3.1.
  have key : ∀ ε₁ ε₂ : Fin m → Bool, S.AdjRay ε₁ ε₂ →
      act S.Aop (ind (S.bgSector ε₁) a) = act S.Aop (ind (S.bgSector ε₂) a) := by
    rintro ε₁ ε₂ ⟨i, e, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · rw [(S.adjSign_spec i e true).2, (S.adjSign_spec i e false).2]
      exact S.act_Aop_ind_Gfield i e a
    · rw [(S.adjSign_spec i e false).2, (S.adjSign_spec i e true).2]
      exact (S.act_Aop_ind_Gfield i e a).symm
  -- Hence nothing changes along a chain of adjacencies.
  have main : ∀ ε₁ ε₂ : Fin m → Bool, Relation.ReflTransGen S.AdjRay ε₁ ε₂ →
      act S.Aop (ind (S.bgSector ε₁) a) = act S.Aop (ind (S.bgSector ε₂) a) := by
    intro ε₁ ε₂ h
    induction h with
    | refl => rfl
    | tail _ hstep ih => rw [ih]; exact key _ _ hstep
  exact main _ _ (S.realised_connected hε S.realised_refSign)

theorem bcol_doublyPeriodic (a : ZMod p) : DoublyPeriodic (S.bcol a) := by
  obtain ⟨u, hu, w, hw, hdet⟩ := S.bgSector_doublyPeriodic S.refSign
  exact ⟨u, act_mem_Per (mem_Per_ind hu a), w, act_mem_Per (mem_Per_ind hw a), hdet⟩

theorem H_mem_Per_bcol (j : Fin m) (a : ZMod p) : S.H j ∈ Per (S.bcol a) :=
  act_mem_Per (mem_Per_ind (S.H_mem_Per_bgSector j S.refSign) a)

/-!
**Remark 3.1 (The lemma does not extend to unrealised tail choices).**  The generalisation
"`A e_{β_σ} = A e_{β_τ}` for all `σ, τ ∈ {L, R}^m`, realised or not" is false: `Λᵢ` is defined
using only the backgrounds `Bᵢ^±`, whereas a mixed tail choice may have periods along `vᵢ`
that `Bᵢ^±` do not have.  An explicit counterexample is in Appendix C.3 of the paper, which is
outside the scope of this formalisation.  Lemma 3.2 uses only realised sectors, so the main
line is unaffected.
-/

/-! ### §3.2 `A e_θ - b` has finite support -/

/-- The widths `ρᵢ = cᵢ + max_{s ∈ supp A} |πᵢ(s)|` cutting out the strips `Σᵢ` of the proof of
Lemma 3.2. -/
noncomputable def rho (i : Fin m) : ℤ :=
  max |S.ell i| |S.r i| + (((supp S.Aop).sup fun s => (pi (S.v i) s).natAbs : ℕ) : ℤ)

/-- Direction `i` is **active** at `z` if `|πᵢ(z)| ≤ ρᵢ`; otherwise all of `z + supp A` lies in
one and the same tail region of component `i`.  Paper Lemma 3.2. -/
def Active (i : Fin m) (z : ℤ × ℤ) : Prop := |pi (S.v i) z| ≤ S.rho i

/-- If `0 < A` and `|R| < |A|` then `0 < A + R`, and conversely: adding a perturbation smaller
in absolute value than `A` does not change the sign of `A`. -/
theorem sign_add_of_abs_lt {A R : ℤ} (h : |R| < |A|) : (0 < A + R) ↔ (0 < A) := by
  rcases abs_cases A with ⟨hA1, hA2⟩ | ⟨hA1, hA2⟩ <;>
    rcases abs_cases R with ⟨hR1, hR2⟩ | ⟨hR1, hR2⟩ <;>
    rw [hA1, hR1] at h <;> omega

/-- `x` and `y` have the same sign iff `x * y > 0`. -/
theorem decide_pos_mul_eq {x y : ℤ} (hx : x ≠ 0) (hy : y ≠ 0) :
    (decide (0 < x) = decide (0 < y)) ↔ 0 < x * y := by
  rw [decide_eq_decide]
  constructor
  · intro h
    rcases lt_or_gt_of_ne hx with hxn | hxp
    · have hyn : y < 0 := by
        by_contra hy'
        push Not at hy'
        have hyp : 0 < y := lt_of_le_of_ne hy' (Ne.symm hy)
        exact absurd (h.mpr hyp) (not_lt.mpr hxn.le)
      exact mul_pos_of_neg_of_neg hxn hyn
    · have hyp : 0 < y := by
        by_contra hy'
        push Not at hy'
        have hyn : y < 0 := lt_of_le_of_ne hy' hy
        exact absurd (h.mp hxp) (not_lt.mpr hyn.le)
      exact mul_pos hxp hyp
  · intro h
    rcases mul_pos_iff.mp h with ⟨hxp, hyp⟩ | ⟨hxn, hyn⟩
    · exact iff_of_true hxp hyp
    · exact iff_of_false (not_lt.mpr hxn.le) (not_lt.mpr hyn.le)

/-- The window `z + supp A` reads `πᵢ` within `ρᵢ - max |ℓᵢ| |rᵢ|` of `πᵢ z`. -/
theorem abs_pi_le_rho_sub (i : Fin m) {s : ℤ × ℤ} (hs : s ∈ supp S.Aop) :
    |pi (S.v i) s| ≤ S.rho i - max |S.ell i| |S.r i| := by
  have hle : (pi (S.v i) s).natAbs ≤ (supp S.Aop).sup fun t => (pi (S.v i) t).natAbs :=
    Finset.le_sup (f := fun t => (pi (S.v i) t).natAbs) hs
  have hcast : |pi (S.v i) s| ≤ (((supp S.Aop).sup fun t => (pi (S.v i) t).natAbs : ℕ) : ℤ) := by
    rw [Int.abs_eq_natAbs]; exact_mod_cast hle
  rw [rho]; omega

theorem rho_nonneg (i : Fin m) : 0 ≤ S.rho i := by
  rw [rho]
  have h1 : (0:ℤ) ≤ max |S.ell i| |S.r i| := (abs_nonneg _).trans (le_max_left _ _)
  have h2 : (0:ℤ) ≤ (((supp S.Aop).sup fun t => (pi (S.v i) t).natAbs : ℕ) : ℤ) :=
    Int.natCast_nonneg _
  linarith

/-- Step (a) of Lemma 3.2: with no active direction, the sign vector of `z` is realised and
`θ` agrees with that sector background on `z + supp A`. -/
theorem eq_bgSector_of_not_active {z : ℤ × ℤ} (hz : ∀ i, ¬ S.Active i z) :
    ∃ ε, S.Realised ε ∧ ∀ s ∈ supp S.Aop, S.θ (z + s) = S.bgSector ε (z + s) := by
  classical
  have hne : ∀ i, pi (S.v i) z ≠ 0 := by
    intro i h0
    have hact : S.rho i < |pi (S.v i) z| := not_le.mp (hz i)
    rw [h0, abs_zero] at hact
    have := S.rho_nonneg i
    omega
  refine ⟨fun i => decide (0 < pi (S.v i) z), ⟨toReal z, fun i => ?_⟩, ?_⟩
  · split_ifs with hp
    · simp only [decide_eq_true_eq] at hp
      show 0 < piR (S.v i) (toReal z)
      rw [piR_toReal]; exact_mod_cast hp
    · simp only [decide_eq_true_eq] at hp
      have hneg : pi (S.v i) z < 0 := lt_of_le_of_ne (not_lt.mp hp) (hne i)
      show piR (S.v i) (toReal z) < 0
      rw [piR_toReal]; exact_mod_cast hneg
  · intro s hs
    show ∑ i, S.F i (z + s) = ∑ i, (if decide (0 < pi (S.v i) z) then S.R i (z + s) else S.L i (z + s))
    apply Finset.sum_congr rfl
    intro i _
    have hact : S.rho i < |pi (S.v i) z| := not_le.mp (hz i)
    have hbound := S.abs_pi_le_rho_sub i hs
    split_ifs with hp
    · simp only [decide_eq_true_eq] at hp
      have h2 : S.rho i < pi (S.v i) z := by rwa [abs_of_pos hp] at hact
      have h1 : S.r i ≤ max |S.ell i| |S.r i| := (le_abs_self _).trans (le_max_right _ _)
      have h3 := abs_le.mp hbound
      have hgt : S.r i < pi (S.v i) (z + s) := by rw [pi_add]; omega
      exact S.S3_R i (z + s) hgt
    · simp only [decide_eq_true_eq] at hp
      have hneg : pi (S.v i) z < 0 := lt_of_le_of_ne (not_lt.mp hp) (hne i)
      have h2 : pi (S.v i) z < -S.rho i := by
        have := abs_of_neg hneg; omega
      have h1 : -max |S.ell i| |S.r i| ≤ S.ell i :=
        le_trans (neg_le_neg (le_max_left _ _)) (neg_abs_le _)
      have h3 := abs_le.mp hbound
      have hlt : pi (S.v i) (z + s) < S.ell i := by rw [pi_add]; omega
      exact S.S3_L i (z + s) hlt

/-- Step (b) of Lemma 3.2: two active directions confine `z` to the intersection of two strips
of bounded width in non-parallel directions, which is finite. -/
theorem finite_two_active :
    {z : ℤ × ℤ | ∃ i j, i ≠ j ∧ S.Active i z ∧ S.Active j z}.Finite := by
  classical
  set c : ℤ := ∑ k : Fin m, (S.rho k + |S.ell k| + |S.r k|) with hc
  have hsub1 : ∀ i, ∀ z : ℤ × ℤ, S.Active i z → z ∈ S.widenedStrip i c := by
    intro i z hact
    have hterm : S.rho i + |S.ell i| + |S.r i| ≤ c := by
      rw [hc]
      exact Finset.single_le_sum (f := fun k => S.rho k + |S.ell k| + |S.r k|)
        (fun k _ => by
          have h1 := S.rho_nonneg k
          have h2 := abs_nonneg (S.ell k)
          have h3 := abs_nonneg (S.r k)
          linarith)
        (Finset.mem_univ i)
    have habs := abs_le.mp hact
    have hle1 : S.ell i ≤ |S.ell i| := le_abs_self _
    have hle2 : -(S.r i) ≤ |S.r i| := neg_le_abs _
    have hnn1 : (0:ℤ) ≤ |S.ell i| := abs_nonneg _
    have hnn2 : (0:ℤ) ≤ |S.r i| := abs_nonneg _
    refine ⟨by omega, by omega⟩
  have hfin : (⋃ i ∈ (Finset.univ : Finset (Fin m)),
      ⋃ j ∈ (Finset.univ.filter (· ≠ i)), (S.widenedStrip i c ∩ S.widenedStrip j c)).Finite :=
    Set.Finite.biUnion (Finset.finite_toSet _) fun i _ =>
      Set.Finite.biUnion (Finset.finite_toSet _) fun j hj =>
        S.widenedStrip_inter_finite (Finset.mem_filter.mp hj).2.symm c
  refine hfin.subset ?_
  rintro z ⟨i, j, hij, hi, hj⟩
  simp only [Set.mem_iUnion]
  exact ⟨i, Finset.mem_univ i, j,
    Finset.mem_filter.mpr ⟨Finset.mem_univ j, hij.symm⟩,
    Set.mem_inter (hsub1 i z hi) (hsub1 j z hj)⟩

/-- `A(T) e_{σᵢ^ε} = b`: the sector background pinned to `Gᵢ^{ε,R}` by definition of `σᵢ`
collapses to `b` exactly as in Lemma 3.1. -/
theorem act_Aop_ind_sigma (i : Fin m) (e : Bool) (a : ZMod p) :
    act S.Aop (ind (S.sigma i e) a) = S.bcol a := by
  classical
  have hkill : act (S.Afac i) (ind (S.sigma i e) a - ind (S.Gfield i e true) a) = 0 := by
    have h := S.act_Afac_diffField i e true a
    unfold diffField at h
    exact h
  have step1 : act S.Aop (ind (S.sigma i e) a) = act S.Aop (ind (S.Gfield i e true) a) := by
    rw [← sub_eq_zero, ← act_sub_right, Aop,
      ← Finset.prod_erase_mul _ _ (Finset.mem_univ i), act_mul, hkill, act_zero_right]
  rw [step1, ← (S.adjSign_spec i e true).2]
  exact S.act_Aop_ind_bgSector (S.adjSign_spec i e true).1 a

/-- Step (c) of Lemma 3.2: with exactly one active direction `i`, outside finitely many
points `θ` agrees with `σᵢ^{sign t}` on `z + supp A`, and `A e_{σᵢ^ε} = A e_{Gᵢ^{ε,R}} = b`
there by (P3) and Lemma 3.0. -/
theorem finite_one_active_exceptional (a : ZMod p) :
    {z : ℤ × ℤ | (∃ i, S.Active i z ∧ ∀ j, j ≠ i → ¬ S.Active j z) ∧
      act S.Aop (ind S.θ a) z ≠ S.bcol a z}.Finite := by
  classical
  choose u hu using fun i => (S.primitive i).exists_dual
  set B : Fin m → ℤ := fun i => 1 + ∑ j, S.rho i * |pi (S.v j) (u i)| with hBdef
  have hBpos : ∀ i, 0 < B i := by
    intro i
    simp only [hBdef]
    have : (0:ℤ) ≤ ∑ j, S.rho i * |pi (S.v j) (u i)| :=
      Finset.sum_nonneg fun j _ => mul_nonneg (S.rho_nonneg i) (abs_nonneg _)
    omega
  have hsub : {z : ℤ × ℤ | (∃ i, S.Active i z ∧ ∀ j, j ≠ i → ¬ S.Active j z) ∧
      act S.Aop (ind S.θ a) z ≠ S.bcol a z}
      ⊆ ⋃ i : Fin m, {z : ℤ × ℤ | S.Active i z ∧ |det z (u i)| ≤ B i} := by
    rintro z ⟨⟨i, hActi, hnAct⟩, hne⟩
    simp only [Set.mem_iUnion]
    refine ⟨i, ?_⟩
    by_contra hcon
    simp only [Set.mem_ofPred_eq] at hcon
    push Not at hcon
    have hbig : B i < |det z (u i)| := hcon hActi
    apply hne
    set e : Bool := decide (0 < det z (u i)) with hedef
    have hscne : det z (u i) ≠ 0 := by
      intro h0
      rw [h0, abs_zero] at hbig
      exact absurd hbig (not_lt.mpr (hBpos i).le)
    have hagree : ∀ s ∈ supp S.Aop, S.θ (z + s) = S.sigma i e (z + s) := by
      intro s hs
      show ∑ k, S.F k (z + s) = S.F i (z + s) + ∑ j ∈ univ.erase i, S.tailSel i j e (z + s)
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      have hji : j ≠ i := (Finset.mem_erase.mp hj).1
      have hnActj : ¬ S.Active j z := hnAct j hji
      have hact : S.rho j < |pi (S.v j) z| := not_le.mp hnActj
      have hbound := S.abs_pi_le_rho_sub j hs
      have hzdecomp : z = (det z (u i)) • (S.v i) + (pi (S.v i) z) • (u i) :=
        eq_smul_add_smul (hu i) z
      have hpi_decomp : pi (S.v j) z
          = det z (u i) * pi (S.v j) (S.v i) + pi (S.v i) z * pi (S.v j) (u i) := by
        conv_lhs => rw [hzdecomp]
        rw [pi_add, pi_smul, pi_smul]
      have ht : |pi (S.v i) z| ≤ S.rho i := hActi
      have hvj0 : pi (S.v j) (S.v i) ≠ 0 := S.nonparallel j i hji
      have hone : (1:ℤ) ≤ |pi (S.v j) (S.v i)| := by
        have := abs_pos.mpr hvj0; omega
      have hsc : S.rho i * |pi (S.v j) (u i)| < |det z (u i)| := by
        have hterm : S.rho i * |pi (S.v j) (u i)| ≤ ∑ k, S.rho i * |pi (S.v k) (u i)| :=
          Finset.single_le_sum (fun k _ => mul_nonneg (S.rho_nonneg i) (abs_nonneg _))
            (Finset.mem_univ j)
        simp only [hBdef] at hbig
        omega
      have hR : |pi (S.v i) z * pi (S.v j) (u i)| ≤ S.rho i * |pi (S.v j) (u i)| := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right ht (abs_nonneg _)
      have hA : |det z (u i)| ≤ |det z (u i) * pi (S.v j) (S.v i)| := by
        rw [abs_mul]
        calc |det z (u i)| = |det z (u i)| * 1 := by ring
        _ ≤ |det z (u i)| * |pi (S.v j) (S.v i)| :=
            mul_le_mul_of_nonneg_left hone (abs_nonneg _)
      have habsRA : |pi (S.v i) z * pi (S.v j) (u i)| < |det z (u i) * pi (S.v j) (S.v i)| :=
        (hR.trans_lt hsc).trans_le hA
      have hsign : (0 < pi (S.v j) z) ↔ (0 < det z (u i) * pi (S.v j) (S.v i)) := by
        rw [hpi_decomp]
        exact sign_add_of_abs_lt habsRA
      have hkey : (decide (0 < pi (S.v j) (S.v i)) = e) ↔ 0 < pi (S.v j) z := by
        rw [hedef, eq_comm, hsign]
        exact decide_pos_mul_eq hscne hvj0
      by_cases hpz : 0 < pi (S.v j) z
      · have hR' : S.F j (z + s) = S.R j (z + s) := by
          apply S.S3_R
          rw [pi_add]
          have h1 : S.r j ≤ max |S.ell j| |S.r j| := (le_abs_self _).trans (le_max_right _ _)
          have h2 : S.rho j < pi (S.v j) z := by rwa [abs_of_pos hpz] at hact
          have h3 := abs_le.mp hbound
          omega
        rw [hR']
        exact (congrFun (S.tailSel_eq_R i j e (hkey.mpr hpz)) (z + s)).symm
      · push Not at hpz
        have hpzne : pi (S.v j) z ≠ 0 := by
          intro h0
          rw [h0, abs_zero] at hact
          exact absurd hact (not_lt.mpr (S.rho_nonneg j))
        have hpzneg : pi (S.v j) z < 0 := lt_of_le_of_ne hpz hpzne
        have hL' : S.F j (z + s) = S.L j (z + s) := by
          apply S.S3_L
          rw [pi_add]
          have h1 : -max |S.ell j| |S.r j| ≤ S.ell j :=
            le_trans (neg_le_neg (le_max_left _ _)) (neg_abs_le _)
          have h2 : pi (S.v j) z < -S.rho j := by
            have := abs_of_neg hpzneg; omega
          have h3 := abs_le.mp hbound
          omega
        rw [hL']
        exact (congrFun (S.tailSel_eq_L i j e
          (fun hcon2 => (not_lt.mpr hpz) (hkey.mp hcon2))) (z + s)).symm
    calc act S.Aop (ind S.θ a) z
        = act S.Aop (ind (S.sigma i e) a) z :=
          act_congr S.Aop z fun s hs => ind_congr a (hagree s hs)
      _ = S.bcol a z := by rw [S.act_Aop_ind_sigma i e a]
  refine (Set.finite_iUnion fun i => ?_).subset hsub
  have hinj : Function.Injective fun z : ℤ × ℤ => (det z (u i), pi (S.v i) z) := by
    intro z w hzw
    have h1 : det z (u i) = det w (u i) := congrArg Prod.fst hzw
    have h2 : det (S.v i) z = det (S.v i) w := congrArg Prod.snd hzw
    rw [eq_smul_add_smul (hu i) z, eq_smul_add_smul (hu i) w, h1, h2]
  have himg : (fun z : ℤ × ℤ => (det z (u i), pi (S.v i) z)) ''
      {z : ℤ × ℤ | S.Active i z ∧ |det z (u i)| ≤ B i} ⊆
      Set.Icc (-(B i)) (B i) ×ˢ Set.Icc (-(S.rho i)) (S.rho i) := by
    rintro _ ⟨z, ⟨hAct, hz⟩, rfl⟩
    exact ⟨abs_le.mp hz, abs_le.mp hAct⟩
  exact Set.Finite.of_finite_image
    (((Set.finite_Icc _ _).prod (Set.finite_Icc _ _)).subset himg) hinj.injOn

/-- **Lemma 3.2.**  `A e_θ - b` has finite support. -/
theorem finite_support_act_Aop_ind_sub (a : ZMod p) :
    (Function.support (act S.Aop (ind S.θ a) - S.bcol a)).Finite := by
  classical
  refine ((S.finite_two_active).union (S.finite_one_active_exceptional a)).subset ?_
  intro z hz
  have hne : act S.Aop (ind S.θ a) z ≠ S.bcol a z := by
    simpa [Function.mem_support, Pi.sub_apply, sub_eq_zero] using hz
  by_cases hall : ∀ i, ¬ S.Active i z
  · -- Case (a): no active direction, so `θ` is a realised sector background on `z + supp A`.
    exfalso
    obtain ⟨ε, hεr, hθ⟩ := S.eq_bgSector_of_not_active hall
    refine hne ?_
    rw [← S.act_Aop_ind_bgSector hεr a]
    exact act_congr S.Aop z fun s hs => ind_congr a (hθ s hs)
  · push Not at hall
    obtain ⟨i, hi⟩ := hall
    by_cases hone : ∀ j, j ≠ i → ¬ S.Active j z
    · -- Case (c): exactly one active direction.
      exact Or.inr ⟨⟨i, hi, hone⟩, hne⟩
    · -- Case (b): two active directions.
      push Not at hone
      obtain ⟨j, hji, hj⟩ := hone
      exact Or.inl ⟨j, i, hji, hj, hi⟩

/-! ### §3.3 Conclusion -/

/-- **Proposition 3.3.**  `A(T) e_θ = b`. -/
theorem act_Aop_ind_eq_bcol (h11 : S.CaseTwo) (a : ZMod p) :
    act S.Aop (ind S.θ a) = S.bcol a := by
  -- `D` kills `A e_θ` by (1.1), and kills `b` because `b` has the period `H idx₀`.
  have h1 : act S.Dop (act S.Aop (ind S.θ a)) = 0 := by
    rw [← act_mul, mul_comm S.Dop S.Aop, act_mul, h11 a, act_zero_right]
  have h2 : act S.Dop (S.bcol a) = 0 := by
    rw [S.Dop_eq_mul S.idx₀, mul_comm, act_mul,
      (act_mono_sub_one_eq_zero_iff _ _).mpr (S.H_mem_Per_bcol S.idx₀ a), act_zero_right]
  have hD : act S.Dop (act S.Aop (ind S.θ a) - S.bcol a) = 0 := by
    rw [act_sub_right, h1, h2, sub_zero]
  -- A non-zero field of finite support cannot be killed by a non-zero operator (Lemma 1.2).
  rw [← sub_eq_zero]
  by_contra hne
  exact act_ne_zero S.Dop_ne_zero (S.finite_support_act_Aop_ind_sub a) hne hD

/-- The encoded background `b_ψ = ∑_a w(a) b_a`.  Paper Proposition 3.3. -/
noncomputable def bpsi : Config ℂ := fun z => ∑ a : ZMod p, (S.enc a : ℂ) * S.bcol a z

/-- **Proposition 3.3.**  `A ψ = b_ψ`, a doubly periodic field preserved by every `Hᵢ`. -/
theorem act_Aop_psi (h11 : S.CaseTwo) : act S.Aop S.psi = S.bpsi := by
  funext z
  have hpsi : S.psi = fun y => ∑ a : ZMod p, (S.enc a : ℂ) * ind S.θ a y := by
    funext y
    rw [sum_mul_ind]
    rfl
  rw [hpsi, act_sum_scalar]
  show ∑ a : ZMod p, (S.enc a : ℂ) * act S.Aop (ind S.θ a) z
      = ∑ a : ZMod p, (S.enc a : ℂ) * S.bcol a z
  exact Finset.sum_congr rfl fun a _ => by rw [S.act_Aop_ind_eq_bcol h11 a]

theorem H_mem_Per_bpsi (i : Fin m) : S.H i ∈ Per S.bpsi := by
  rw [mem_Per_iff]
  funext z
  show ∑ a : ZMod p, (S.enc a : ℂ) * S.bcol a (z + S.H i)
      = ∑ a : ZMod p, (S.enc a : ℂ) * S.bcol a z
  exact Finset.sum_congr rfl fun a _ => by rw [Per.apply (S.H_mem_Per_bcol i a) z]

theorem bpsi_doublyPeriodic : DoublyPeriodic S.bpsi :=
  ⟨S.H S.idx₀, S.H_mem_Per_bpsi S.idx₀, S.H S.idx₁, S.H_mem_Per_bpsi S.idx₁,
    S.det_H_ne_zero S.idx₀_ne_idx₁⟩

end StarConfig

end Nivat
