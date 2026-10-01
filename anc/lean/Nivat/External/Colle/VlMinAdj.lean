/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.CornerAdjClash

/-!
# `hvlmin`：相邻性把 `nℓ`-极小顶点压成 `vl`-坐标极小点

`RegionSteps.lean` 洞 3 之后的 `hvlmin`（`wedgeResidualR_of_cone_of_enveloped` 的装配处）：

```
∀ z ∈ Sw, 0 ≤ dot (expNormal u' vl) (z - a₀)
```

原文：b3_colle2.txt:766（`ℓ₁,…,ℓ_{2m}` 是 `𝒮_φ` 的边方向按**循环序**排列，`ℓ_{ι-1}` 是 `ℓ`
的前驱）、:792-798（把 `𝒮_{φ_ι}` 放到扫掠线 `l_k` 上：极点落在 `l_k`，其余点落在
`H_B(ℓ) ∪ A₁ ∪ … ∪ A_{k-1}` 里）。

## 量词对应（硬规矩 7）

| 原文 | 本文件 |
|---|---|
| `𝒮_{φ_ι}` 的 `nℓ`-极小点唯一（Lemma 2.6：无平行 `±ℓ` 的边） | `hstrict : ∀ z ∈ Sw.erase a₀, dot nℓ a₀ < dot nℓ z` |
| `ℓ_{ι-1}` 与 `ℓ` 相邻（`:766` 循环序） | `hadj : ∀ n ∈ E ↑Sw, ¬ (dot n vl < 0 ∧ 0 < dot n u')`：`vl`、`u'` 张成的开锥内没有边法向 |
| `𝒮_{φ_ι}` 有限 | `Sw : Finset` |
| 其余点落在 `l_k` 的 `vl`-侧 | 结论 `0 ≤ dot (expNormal u' vl) (z - a₀)` |

## 为什么成立（硬规矩 10）

在幺模基 `(vl, u')` 下每个向量 `w` 有两个坐标 `en w := ⟪expNormal u' vl, w⟫`（`vl`-系数）
与 `uc w = -⟪nℓ, w⟫`（`u'`-系数，`dot_eq_coords` + `hperp`/`hnu`）；法向 `n` 由
`(p, q) := (⟪n, vl⟫, ⟪n, u'⟫)` 刻画，`⟪n, w⟫ = en w · p + uc w · q`。

* `hadj` 说边法向都避开开象限 `{p < 0, q > 0}`。
* 取方向 `c ↦ (p, q) = (-1, 1)`，`exists_edge_cone`（`LatticeEdges.lean:937`）给出 `c` 的
  极大点 `v` 与两条边法向 `n₁, n₂`，`c = a n₁ + b n₂`（`a, b ≥ 0`），`v` 同时是三者的极大点。
  由 `hadj` 与 `-1 = a p₁ + b p₂`、`1 = a q₁ + b q₂` 只剩一种符号型
  （`pattern_of_decomp`）：一条法向 `(p ≥ 0, q > 0)`，另一条 `(p < 0, q ≤ 0)`。
* 对 `z ∈ Sw`，`w := z - v` 满足三条不等式 `-en w + uc w ≤ 0`、`en w · p_i + uc w · q_i ≤ 0`
  ⟹ `en w ≥ 0 ∧ uc w ≤ 0`（`coords_of_pattern`）。于是 `v` 同时是 `Sw` 的 `en`-极小点
  与 `nℓ`-极小点；`hstrict` 迫使 `v = a₀`。
* `exists_edge_cone` 要 `PosArea`。`m = 2` 时 `𝒮_{φ_ι}` 是一条线段，没有正面积，
  但结论仍真：此时 `Sw` 共线，若 `en (z - a₀) < 0` 则与 `z - a₀` 垂直的本原法向
  `(p, q) = (-⟪nℓ, z - a₀⟫, -en (z - a₀))` 落在 `{p < 0, q > 0}` 且暴露整条线段，
  正是 `hadj` 排除的边法向（`vlmin_of_adjacent` 的第二分支）。
  **所以本文件不要 `PosArea` 前提**——洞 3 的 binder 列表里也没有它。

## 边界

不含 `IsMinimalCounterexample`、不含 `sorry`、不含新 `Prop`。
-/

set_option autoImplicit false

namespace Nivat.VlMinAdj

open Nivat Nivat.LE2 Nivat.ColleReg Nivat.L1Line0 Nivat.L1StraddleWedge Nivat.CornerAdjClash

/-! ## §1  纯算术 -/

/-- **符号型。** `c = (-1, 1)` 分解成两条避开 `{p < 0, q > 0}` 的法向的非负组合时，
只可能一条 `(p ≥ 0, q > 0)`、另一条 `(p < 0, q ≤ 0)`。 -/
theorem pattern_of_decomp {a b p₁ q₁ p₂ q₂ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hp : a * p₁ + b * p₂ = -1) (hq : a * q₁ + b * q₂ = 1)
    (h₁ : ¬ (p₁ < 0 ∧ 0 < q₁)) (h₂ : ¬ (p₂ < 0 ∧ 0 < q₂)) :
    (0 ≤ p₁ ∧ 0 < q₁ ∧ p₂ < 0 ∧ q₂ ≤ 0) ∨ (0 ≤ p₂ ∧ 0 < q₂ ∧ p₁ < 0 ∧ q₁ ≤ 0) := by
  push Not at h₁ h₂
  rcases lt_or_ge p₁ 0 with hp₁ | hp₁ <;> rcases lt_or_ge p₂ 0 with hp₂ | hp₂
  · -- both `p < 0` ⟹ both `q ≤ 0` ⟹ `a q₁ + b q₂ ≤ 0 ≠ 1`
    have hq₁ := h₁ hp₁
    have hq₂ := h₂ hp₂
    have := mul_nonneg ha (neg_nonneg.mpr hq₁)
    have := mul_nonneg hb (neg_nonneg.mpr hq₂)
    linarith
  · right
    have hq₁ := h₁ hp₁
    refine ⟨hp₂, ?_, hp₁, hq₁⟩
    by_contra hq₂
    push Not at hq₂
    have := mul_nonneg ha (neg_nonneg.mpr hq₁)
    have := mul_nonneg hb (neg_nonneg.mpr hq₂)
    linarith
  · left
    have hq₂ := h₂ hp₂
    refine ⟨hp₁, ?_, hp₂, hq₂⟩
    by_contra hq₁
    push Not at hq₁
    have := mul_nonneg ha (neg_nonneg.mpr hq₁)
    have := mul_nonneg hb (neg_nonneg.mpr hq₂)
    linarith
  · -- both `p ≥ 0` ⟹ `a p₁ + b p₂ ≥ 0 ≠ -1`
    have := mul_nonneg ha hp₁
    have := mul_nonneg hb hp₂
    linarith

/-- **坐标结论。** 三条不等式配符号型 ⟹ `0 ≤ α ∧ β ≤ 0`。整数版。 -/
theorem coords_of_pattern {α β p₁ q₁ p₂ q₂ : ℤ}
    (h1 : -α + β ≤ 0) (h2 : α * p₁ + β * q₁ ≤ 0) (h3 : α * p₂ + β * q₂ ≤ 0)
    (hp₁ : 0 ≤ p₁) (hq₁ : 0 < q₁) (hp₂ : p₂ < 0) (hq₂ : q₂ ≤ 0) :
    0 ≤ α ∧ β ≤ 0 := by
  constructor
  · by_contra hα
    push Not at hα
    have hβ : β < 0 := by linarith
    have := mul_pos_of_neg_of_neg hα hp₂
    have := mul_nonneg_of_nonpos_of_nonpos hβ.le hq₂
    linarith
  · by_contra hβ
    push Not at hβ
    have hα : 0 < α := by linarith
    have := mul_nonneg hα.le hp₁
    have := mul_pos hβ hq₁
    linarith

/-- 平行于 `w ≠ 0` 的向量 `x` 与 `w` 的任何法向正交。 -/
theorem dot_eq_zero_of_parallel {N x w : ℤ × ℤ} (hw : w ≠ 0) (hpar : det x w = 0)
    (hNw : dot N w = 0) : dot N x = 0 := by
  simp only [det, dot] at hpar hNw ⊢
  have h1 : (N.1 * x.1 + N.2 * x.2) * w.1 = 0 := by
    linear_combination x.1 * hNw - N.2 * hpar
  have h2 : (N.1 * x.1 + N.2 * x.2) * w.2 = 0 := by
    linear_combination x.2 * hNw + N.1 * hpar
  by_cases hw1 : w.1 = 0
  · by_cases hw2 : w.2 = 0
    · exact absurd (Prod.ext hw1 hw2) hw
    · exact (mul_eq_zero.mp h2).resolve_right hw2
  · exact (mul_eq_zero.mp h1).resolve_right hw1

/-! ## §2  几何核心 -/

section Core

variable {u' vl nℓ : ℤ × ℤ}

/-- `uCoord u' vl 0 w = -⟪nℓ, w⟫`：`u'`-坐标就是 `nℓ` 配对的相反数。 -/
theorem uCoord_eq_neg_dot (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hperp : dot nℓ vl = 0) (hnu : dot nℓ u' = -1) (w : ℤ × ℤ) :
    uCoord u' vl 0 w = -dot nℓ w := by
  have := dot_eq_coords hunimod nℓ w
  rw [hperp, hnu] at this
  linarith

/-- 任意法向的配对按 `(en, -⟪nℓ,·⟫)` 展开。 -/
theorem dot_expand (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hperp : dot nℓ vl = 0) (hnu : dot nℓ u' = -1) (n w : ℤ × ℤ) :
    dot n w = dot (expNormal u' vl) w * dot n vl - dot nℓ w * dot n u' := by
  rw [dot_eq_coords hunimod n w, uCoord_eq_neg_dot hunimod hperp hnu]; ring

/-- **正面积分支的核心。** 有一个点 `v ∈ Sw` 同时是 `c ↦ (-1, 1)`、一条 `(p ≥ 0, q > 0)` 法向
`nA`、一条 `(p < 0, q ≤ 0)` 法向 `nB` 的极大点，则 `v` 是 `Sw` 的 `en`-极小点与 `nℓ`-极小点；
`hstrict` 迫使 `v = a₀`。 -/
theorem vlmin_of_frame (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hperp : dot nℓ vl = 0) (hnu : dot nℓ u' = -1)
    {Sw : Finset (ℤ × ℤ)} {a₀ v : ℤ × ℤ} (ha₀ : a₀ ∈ Sw) (hvS : v ∈ Sw)
    (hstrict : ∀ z ∈ Sw.erase a₀, dot nℓ a₀ < dot nℓ z)
    {n nA nB : ℤ × ℤ} (hnvl : dot n vl = -1) (hnu' : dot n u' = 1)
    (hvle : ∀ z ∈ Sw, dot n z ≤ dot n v)
    (hA : ∀ y ∈ Sw, dot nA y ≤ dot nA v) (hB : ∀ y ∈ Sw, dot nB y ≤ dot nB v)
    (hpA : 0 ≤ dot nA vl) (hqA : 0 < dot nA u') (hpB : dot nB vl < 0) (hqB : dot nB u' ≤ 0) :
    ∀ z ∈ Sw, 0 ≤ dot (expNormal u' vl) (z - a₀) := by
  have hcoords : ∀ z ∈ Sw,
      0 ≤ dot (expNormal u' vl) (z - v) ∧ dot nℓ v ≤ dot nℓ z := by
    intro z hz
    have h1 : dot n (z - v) ≤ 0 := by rw [dot_sub]; linarith [hvle z hz]
    have h2 : dot nA (z - v) ≤ 0 := by rw [dot_sub]; linarith [hA z hz]
    have h3 : dot nB (z - v) ≤ 0 := by rw [dot_sub]; linarith [hB z hz]
    rw [dot_expand hunimod hperp hnu, hnvl, hnu'] at h1
    rw [dot_expand hunimod hperp hnu] at h2 h3
    have key := coords_of_pattern (α := dot (expNormal u' vl) (z - v)) (β := -dot nℓ (z - v))
      (by linarith) (by linarith) (by linarith) hpA hqA hpB hqB
    refine ⟨key.1, ?_⟩
    have := key.2
    rw [dot_sub] at this
    linarith
  have hva : v = a₀ := by
    by_contra hne
    have := hstrict v (Finset.mem_erase.mpr ⟨hne, hvS⟩)
    have := (hcoords a₀ ha₀).2
    linarith
  subst hva
  exact fun z hz => (hcoords z hz).1

/-- **`hvlmin` 的生产者。** 前提恰是洞 3 之后上下文里的四条
（`ha₀`、`hstrict`、`hadjSw`，以及幺模基 `hunimod`/`hperp`/`hnu`）；**不要 `PosArea`**，
共线情形在第二分支单独处理。 -/
theorem vlmin_of_adjacent (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hperp : dot nℓ vl = 0) (hnu : dot nℓ u' = -1)
    {Sw : Finset (ℤ × ℤ)} {a₀ : ℤ × ℤ} (ha₀ : a₀ ∈ Sw)
    (hstrict : ∀ z ∈ Sw.erase a₀, dot nℓ a₀ < dot nℓ z)
    (hadj : ∀ n ∈ E (↑Sw : Set (ℤ × ℤ)), ¬ (dot n vl < 0 ∧ 0 < dot n u')) :
    ∀ z ∈ Sw, 0 ≤ dot (expNormal u' vl) (z - a₀) := by
  classical
  by_cases harea : PosArea (↑Sw : Set (ℤ × ℤ))
  · -- 正面积：`exists_edge_cone` 在方向 `(-1, 1)` 上
    obtain ⟨n, hn⟩ : ∃ n : ℤ × ℤ, n = -expNormal u' vl - nℓ := ⟨_, rfl⟩
    have hnvl : dot n vl = -1 := by
      have h1 := dot_expNormal_vl hunimod
      rw [hn]
      simp only [dot, Prod.fst_sub, Prod.snd_sub, Prod.fst_neg, Prod.snd_neg] at h1 hperp ⊢
      linear_combination -h1 - hperp
    have hnu' : dot n u' = 1 := by
      have h1 := dot_expNormal_u' (u' := u') (vl := vl)
      rw [hn]
      simp only [dot, Prod.fst_sub, Prod.snd_sub, Prod.fst_neg, Prod.snd_neg] at h1 hnu ⊢
      linear_combination -h1 - hnu
    have hc : (((n.1 : ℝ), (n.2 : ℝ)) : ℝ × ℝ) ≠ 0 := by
      intro h
      have h1 : (n.1 : ℝ) = 0 := congrArg Prod.fst h
      have h2 : (n.2 : ℝ) = 0 := congrArg Prod.snd h
      have h1' : n.1 = 0 := by exact_mod_cast h1
      have h2' : n.2 = 0 := by exact_mod_cast h2
      simp [dot, h1', h2'] at hnvl
    have hfin : (↑Sw : Set (ℤ × ℤ)).Finite := Sw.finite_toSet
    have hne : (↑Sw : Set (ℤ × ℤ)).Nonempty := ⟨a₀, Finset.mem_coe.mpr ha₀⟩
    obtain ⟨n₁, n₂, a, b, hE₁, hE₂, ha, hb, e1, e2, v, hvmax, hv1, hv2⟩ :=
      exists_edge_cone hfin hne harea hc
    have e1' : (n.1 : ℝ) = a * n₁.1 + b * n₂.1 := e1
    have e2' : (n.2 : ℝ) = a * n₁.2 + b * n₂.2 := e2
    have hpR : a * (dot n₁ vl : ℝ) + b * (dot n₂ vl : ℝ) = -1 := by
      have h : ((dot n vl : ℤ) : ℝ) = ((-1 : ℤ) : ℝ) := by rw [hnvl]
      simp only [dot] at h ⊢
      push_cast at h ⊢
      linear_combination h - (vl.1 : ℝ) * e1' - (vl.2 : ℝ) * e2'
    have hqR : a * (dot n₁ u' : ℝ) + b * (dot n₂ u' : ℝ) = 1 := by
      have h : ((dot n u' : ℤ) : ℝ) = ((1 : ℤ) : ℝ) := by rw [hnu']
      simp only [dot] at h ⊢
      push_cast at h ⊢
      linear_combination h - (u'.1 : ℝ) * e1' - (u'.2 : ℝ) * e2'
    have hc1 : (((n.1 : ℝ), (n.2 : ℝ)) : ℝ × ℝ).1 = 1 * (n.1 : ℝ) := by simp
    have hc2 : (((n.1 : ℝ), (n.2 : ℝ)) : ℝ × ℝ).2 = 1 * (n.2 : ℝ) := by simp
    have hvle : ∀ z ∈ Sw, dot n z ≤ dot n v := by
      intro z hz
      have h := hvmax z (Finset.mem_coe.mpr hz)
      rw [rdotZ_of_int n hc1 hc2, rdotZ_of_int n hc1 hc2] at h
      have : (dot n z : ℝ) ≤ (dot n v : ℝ) := by linarith
      exact_mod_cast this
    obtain ⟨hvS, hv1'⟩ := hv1
    obtain ⟨-, hv2'⟩ := hv2
    have hvS' : v ∈ Sw := Finset.mem_coe.mp hvS
    have hA1 : ∀ y ∈ Sw, dot n₁ y ≤ dot n₁ v := fun y hy => hv1' y (Finset.mem_coe.mpr hy)
    have hA2 : ∀ y ∈ Sw, dot n₂ y ≤ dot n₂ v := fun y hy => hv2' y (Finset.mem_coe.mpr hy)
    have hadj₁ : ¬ ((dot n₁ vl : ℝ) < 0 ∧ 0 < (dot n₁ u' : ℝ)) := by
      rintro ⟨h1, h2⟩
      exact hadj n₁ hE₁ ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
    have hadj₂ : ¬ ((dot n₂ vl : ℝ) < 0 ∧ 0 < (dot n₂ u' : ℝ)) := by
      rintro ⟨h1, h2⟩
      exact hadj n₂ hE₂ ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
    rcases pattern_of_decomp ha hb hpR hqR hadj₁ hadj₂ with
      ⟨hp₁, hq₁, hp₂, hq₂⟩ | ⟨hp₂, hq₂, hp₁, hq₁⟩
    · exact vlmin_of_frame hunimod hperp hnu ha₀ hvS' hstrict hnvl hnu' hvle hA1 hA2
        (by exact_mod_cast hp₁) (by exact_mod_cast hq₁)
        (by exact_mod_cast hp₂) (by exact_mod_cast hq₂)
    · exact vlmin_of_frame hunimod hperp hnu ha₀ hvS' hstrict hnvl hnu' hvle hA2 hA1
        (by exact_mod_cast hp₂) (by exact_mod_cast hq₂)
        (by exact_mod_cast hp₁) (by exact_mod_cast hq₁)
  · -- 共线：与 `z - a₀` 垂直的本原法向落在被 `hadj` 排除的开象限里
    intro z hz
    by_cases hza : z = a₀
    · subst hza; simp [dot]
    · by_contra hlt
      push Not at hlt
      have hzE : z ∈ Sw.erase a₀ := Finset.mem_erase.mpr ⟨hza, hz⟩
      have hγpos : 0 < dot nℓ (z - a₀) := by
        have := hstrict z hzE
        rw [dot_sub]; linarith
      have hwne : z - a₀ ≠ 0 := sub_ne_zero.mpr hza
      obtain ⟨γ, hγ⟩ : ∃ γ : ℤ, γ = dot nℓ (z - a₀) := ⟨_, rfl⟩
      obtain ⟨α, hα⟩ : ∃ α : ℤ, α = dot (expNormal u' vl) (z - a₀) := ⟨_, rfl⟩
      have hγpos' : 0 < γ := hγ ▸ hγpos
      have hαneg : α < 0 := hα ▸ hlt
      obtain ⟨N, hN⟩ : ∃ N : ℤ × ℤ, N = (-γ) • expNormal u' vl + α • nℓ := ⟨_, rfl⟩
      have hdotN : ∀ y, dot N y = -γ * dot (expNormal u' vl) y + α * dot nℓ y := by
        intro y
        rw [hN]
        simp only [dot, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
        ring
      have hNvl : dot N vl = -γ := by rw [hdotN, dot_expNormal_vl hunimod, hperp]; ring
      have hNu : dot N u' = -α := by rw [hdotN, dot_expNormal_u', hnu]; ring
      have hNw : dot N (z - a₀) = 0 := by rw [hdotN, ← hγ, ← hα]; ring
      have hNne : N ≠ 0 := by
        intro h
        rw [h] at hNvl
        simp [dot] at hNvl
        omega
      obtain ⟨hprim, g, hg, hgN⟩ := primPart_spec hNne
      have hN'vl : dot (primPart N) vl < 0 := by
        have h := hNvl
        rw [hgN, dot_smul] at h
        by_contra hh
        push Not at hh
        have := mul_nonneg hg.le hh
        linarith
      have hN'u : 0 < dot (primPart N) u' := by
        have h := hNu
        rw [hgN, dot_smul] at h
        by_contra hh
        push Not at hh
        have := mul_nonneg hg.le (neg_nonneg.mpr hh)
        linarith
      have hface : ∀ y ∈ Sw, dot (primPart N) y = dot (primPart N) a₀ := by
        intro y hy
        have hcol : det (y - a₀) (z - a₀) = 0 := by
          by_contra hne
          exact harea ⟨a₀, Finset.mem_coe.mpr ha₀, y, Finset.mem_coe.mpr hy,
            z, Finset.mem_coe.mpr hz, hne⟩
        have h0 : dot N (y - a₀) = 0 := dot_eq_zero_of_parallel hwne hcol hNw
        rw [hgN, dot_smul] at h0
        have : dot (primPart N) (y - a₀) = 0 := by
          rcases mul_eq_zero.mp h0 with h | h
          · omega
          · exact h
        rw [dot_sub] at this
        linarith
      have hE : primPart N ∈ E (↑Sw : Set (ℤ × ℤ)) := by
        refine ⟨hprim, ?_⟩
        have hfaceAll : ∀ y ∈ Sw, y ∈ face (↑Sw : Set (ℤ × ℤ)) (primPart N) := by
          intro y hy
          refine ⟨Finset.mem_coe.mpr hy, fun y' hy' => ?_⟩
          rw [hface y hy, hface y' (Finset.mem_coe.mp hy')]
        exact ⟨a₀, hfaceAll a₀ ha₀, z, hfaceAll z hz, fun h => hza h.symm⟩
      exact hadj _ hE ⟨hN'vl, hN'u⟩

end Core

end Nivat.VlMinAdj

section Receipts
/-! 常备 `#print axioms` 收据，可整块删除。 -/

#print axioms Nivat.VlMinAdj.vlmin_of_frame
#print axioms Nivat.VlMinAdj.vlmin_of_adjacent

end Receipts
