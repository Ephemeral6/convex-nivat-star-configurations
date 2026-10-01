/-
Copyright (c) 2026. Released under Apache 2.0 license.
Authors: lane-tower-hbase
-/
import Nivat.External.Colle.TowerConstruct
import Nivat.External.Colle.NewtonZonotope
import Nivat.External.Colle.TowerGoodW
import Nivat.External.Colle.ANormal
import Nivat.External.Colle.FanOrderCriterion
import Nivat.External.Colle.TowerPigeonhole

/-!
# 判据 ⟺ `I = len`：`crit_false_below_top` / `crit_iff_eq_top` 上链

**本文件是逐字搬运，不是新证明。** 两条定理连同它们用到的八条 `private` 辅助，
全部从 `tmp/wip/lane-tower-hbase-idxdict.lean` 的 §0 / §8 / §11 / §12 按行区间原样抽出
（抽取脚本 `tmp/lane-tower-hbase-mkcrit.py`，只做 `import` / `namespace` / docstring 三处包装，
定理语句与证明体一个字符没动）。

## 为什么搬

team-lead 第 217 轮实测：`crit_iff_eq_top` 此前**只存在于 `tmp/wip/`**，主仓里仅以注释形式
出现（本轮实测：`crit_iff_eq_top` 5 处、`crit_false_below_top` 4 处，**全是注释**，
见 `RegionSteps.lean` 的 `exists_cutResidualR_of_claim46` 段与 `TowerPkgMain.lean` 的
`lane_towerpkg_reduce_at_core` 段）。全队二十轮把它当桥用（`hstrict` ⟺ 判据 ⟺ `I_lean = len`），
但按硬规矩 1，**它对公理闭包的贡献此前是零**。本文件把桥放上链。

⭐ 命名空间**刻意**沿用 `Nivat.LaneTowerHbaseIdxDict`：`TowerPkgMain.lean` 里那两处
按全名引用（`Nivat.LaneTowerHbaseIdxDict.crit_false_below_top` / `….crit_iff_eq_top`）
因此**从悬空引用变成可解析的在册声明**，而该文件按纪律 15 我不许改。
⚠ 同处第三条引用 `Nivat.LaneTowerHbaseIdxDict.crit_at_u'_false_bothsign` **不在本文件里**，
仍然悬空，已单独报 team-lead（§57：不能就地改的烂锚要报，不能默默留着）。

## 红线适用性

本文件**不新增任何 `def` / `Prop` / 结构字段**，只有两条 `theorem` 与八条 `private theorem`。
⟹ CLAUDE.md「每条定义/`Prop`/字段 docstring 指 `b3_colle2.txt:NNN` 并逐量词对应」在本文件
**无适用对象**；两条定理谈论的对象（`DecompData` / `extChain` / `sortedCand` / `wgen` /
`candSet` / `wtower`）全部定义在 `TowerConstruct.lean` 与 `ANormal.lean`，原文锚在那两处。
⚠ 我**没有**为这两条定理本身找到 `b3_colle2.txt` 的对应句：它们是关于上述主仓定义的
**判据层推论**，不是原文某句的转写。若集成者要求原文对应物，这是一笔明账，不是我漏写。

## 还欠什么

1. `crit_iff_eq_top` 的 `hlast` 是**形参**：lane-towerpkg 的 `hlast_good_discharge` 无条件给它，
   但 §16 禁 import，故此处当形参收。消解它不在本文件射程内。
2. `RegionSteps.lean` 的破口 (C)「`crit_iff_eq_top` 的 binder 表在 `I = 0` 档不可满足」
   **非空真性未验**（我自己按 §41 标的）。关它的是 lane-tower-hlev 的 rig
   （`tmp/wip/lane-tower-hlev-idxrig.lean`），不是本文件。
   ⟹ **本文件只保证桥在链上，不保证桥承重。** 两件事分开记。
-/

set_option autoImplicit false

namespace Nivat.LaneTowerHbaseIdxDict

open Nivat Nivat.LE2 Nivat.ColleReg Nivat.Colle35

variable {ξ : Nivat.Config ℤ}


private theorem idx_det_smul_left (k : ℤ) (a b : ℤ × ℤ) : det (k • a) b = k * det a b := by
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  simp only [det, Prod.smul_mk, smul_eq_mul]
  ring

/-- `d.h j = c • wgen d nℓ j`，`c ≠ 0`（与 `predgood.lean` §0 的 `h_eq_smul_wgen` 逐字同）。 -/
private theorem idx_h_eq_smul_wgen (d : DecompData ξ) {vl nℓ : ℤ × ℤ}
    (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0) {j : Fin d.m} (hij : j ≠ i) :
    ∃ c : ℤ, c ≠ 0 ∧ d.h j = c • wgen d nℓ j := by
  have hlt := dot_orientGen_neg d hvl_prim hprim hperp i hdoth hij
  have hne : orientGen d nℓ j ≠ 0 := by
    intro h0; rw [h0] at hlt; simp [Nivat.LE2.dot] at hlt
  obtain ⟨-, G, hGpos, hGeq⟩ := Nivat.LE2.primPart_spec hne
  have hwg : wgen d nℓ j = Nivat.LE2.primPart (orientGen d nℓ j) := rfl
  rw [← hwg] at hGeq
  by_cases hpos : dot nℓ (d.h j) < 0
  · refine ⟨G, by omega, ?_⟩
    have horient : orientGen d nℓ j = d.h j := by unfold orientGen; rw [if_pos hpos]
    rw [← horient]; exact hGeq
  · refine ⟨-G, by omega, ?_⟩
    have horient : orientGen d nℓ j = -(d.h j) := by unfold orientGen; rw [if_neg hpos]
    rw [horient] at hGeq
    rw [neg_smul, ← hGeq]
    simp


/-- **垂直字典（无定向假设）**：`dot nℓ vl = 0` 时，两个线性泛函 `x ↦ dot nℓ x` 与
`x ↦ det x vl` 成比例，比例常数分别是 `det nℓ vl` 与 `dot nℓ nℓ`。

这是 §7 用的 `dot_nl_eq_det_vl`（`TowerGoodW.lean:141`，要 `nℓ = -dir vl`）的**无定向**替身：
它对 `nℓ = ±dir vl` 两支同时成立，代价是两边各带一个非零常数。 -/
private theorem idx_perp_dict {nℓ vl : ℤ × ℤ} (hperp : dot nℓ vl = 0) (x : ℤ × ℤ) :
    (det nℓ vl) * dot nℓ x = (dot nℓ nℓ) * det x vl := by
  obtain ⟨a, b⟩ := nℓ
  obtain ⟨p, q⟩ := vl
  obtain ⟨s, t⟩ := x
  simp only [Nivat.LE2.dot, det] at hperp ⊢
  linear_combination (a * t - b * s) * hperp

private theorem idx_det_neg_right (a b : ℤ × ℤ) : det a (-b) = - det a b := by
  obtain ⟨a1, a2⟩ := a; obtain ⟨b1, b2⟩ := b
  simp only [det, Prod.neg_mk]
  ring

private theorem idx_dot_self_pos {n : ℤ × ℤ} (h : Prim n) : 0 < dot n n := by
  have hne : ¬ (n.1 = 0 ∧ n.2 = 0) := by
    rintro ⟨e1, e2⟩
    simp only [Nivat.LE2.Prim, e1, e2] at h
    simp at h
  simp only [Nivat.LE2.dot]
  rcases (not_and_or.mp hne) with hh | hh <;>
    nlinarith [sq_nonneg n.1, sq_nonneg n.2, mul_self_pos.mpr hh]

private theorem idx_det_swap (a b : ℤ × ℤ) : det a b = - det b a := by
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  simp only [det]
  ring

/-- 链上每一档都在 `vl` 的同一个开半平面里：`0 < det vl (extChain … t)`。

`dot_extChain_neg`（`TowerConstruct.lean:925`）＋ §8 的 `idx_perp_dict` ＋ `hdetpos`。 -/
private theorem idx_det_vl_extChain_pos (d : DecompData ξ) {vl nℓ u' : ℤ × ℤ}
    (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (hdetpos : 0 < det nℓ vl) (hnu : dot nℓ u' < 0)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0)
    {t : ℕ} (ht : t ≤ (sortedCand d nℓ u' i).length) :
    0 < det vl (extChain d nℓ vl u' i t) := by
  have hdn := dot_extChain_neg d hvl_prim hprim hperp i hdoth hnu ht
  have hkey := idx_perp_dict hperp (extChain d nℓ vl u' i t)
  have hN := idx_dot_self_pos hprim
  have hlt : det (extChain d nℓ vl u' i t) vl < 0 := by
    nlinarith [hkey, mul_pos hdetpos (neg_pos.mpr hdn), hN]
  rw [idx_det_swap vl (extChain d nℓ vl u' i t)]
  linarith

/-- 链上严格逆时针的逐下标形式：`det_pos_extChain`（`TowerConstruct.lean:1024`）除掉常数因子。

常数因子的符号**不是假设来的**：`idx_perp_dict` 在 `x := u'` 处给
`(det nℓ vl) * dot nℓ u' = (dot nℓ nℓ) * det u' vl`，左边在 `hdetpos` ＋ `hnu` 下为负、
`dot nℓ nℓ > 0` ⟹ `det u' vl < 0` ⟹ `det u' (-vl) > 0`。
⟹ 本条**不**依赖 `RegionNlDict.det_u'_vl_eq_neg_one_of_normalized`，也不吃 `det u' vl = -1`。 -/
private theorem idx_det_extChain_ccw {B : Set (ℤ × ℤ)} (d : DecompData ξ) {vl nℓ u' : ℤ × ℤ}
    (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (henv : Nivat.LE2.EnvOf (↑d.Sphi : Set (ℤ × ℤ)) B)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0)
    (hadj : ∀ n ∈ Nivat.LE2.E (↑d.Sphi : Set (ℤ × ℤ)),
      ¬ (dot n vl < 0 ∧ 0 < dot n u'))
    (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hdetpos : 0 < det nℓ vl) (hnu : dot nℓ u' < 0)
    {a b : ℕ} (hab : a < b) (hb : b ≤ (sortedCand d nℓ u' i).length) :
    0 < det (extChain d nℓ vl u' i a) (extChain d nℓ vl u' i b) := by
  have hnlne : nℓ ≠ 0 := Nivat.LE2.Prim.ne_zero hprim
  have hkey := det_pos_extChain d hvl_prim hprim hperp henv i hdoth
    (hadjB_of_hadj d henv hadj) hunimod hnu hnlne hab hb
  have hdict := idx_perp_dict hperp u'
  have hN := idx_dot_self_pos hprim
  have huvl : det u' vl < 0 := by
    nlinarith [hdict, mul_pos hdetpos (neg_pos.mpr hnu), hN]
  have hc : 0 < det u' (-vl) := by
    rw [idx_det_neg_right]; linarith
  nlinarith [hkey, hc]

/-- ⭐⭐ **判据在链顶以下的每一档都为假。** -/
theorem crit_false_below_top {B : Set (ℤ × ℤ)} (d : DecompData ξ) {vl nℓ u' : ℤ × ℤ}
    (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (henv : Nivat.LE2.EnvOf (↑d.Sphi : Set (ℤ × ℤ)) B)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0)
    (hadj : ∀ n ∈ Nivat.LE2.E (↑d.Sphi : Set (ℤ × ℤ)),
      ¬ (dot n vl < 0 ∧ 0 < dot n u'))
    (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hdetpos : 0 < det nℓ vl) (hnu : dot nℓ u' < 0)
    {I K : ℕ} (hIK : I < K) (hK : K ≤ (sortedCand d nℓ u' i).length) :
    ¬ (∀ j : Fin d.m,
        det (d.h j) vl * det (d.h j) (extChain d nℓ vl u' i I) ≤ 0) := by
  intro hcrit
  obtain ⟨t, rfl⟩ : ∃ t, K = t + 1 := ⟨K - 1, by omega⟩
  have htlen : t < (sortedCand d nℓ u' i).length := by omega
  have hext : extChain d nℓ vl u' i (t + 1) = wtower d nℓ vl u' i t := rfl
  -- 链顶那一档本身是某个生成元的方向
  have hmem : wtower d nℓ vl u' i t ∈ candSet d nℓ u' i := mem_candSet_wtower htlen
  simp only [candSet, Finset.mem_erase, Finset.mem_image] at hmem
  obtain ⟨-, j₀, hj₀mem, hj₀eq⟩ := hmem
  have hj₀i : j₀ ≠ i := hj₀mem.1
  -- 两个因子的符号
  have hA : det (wtower d nℓ vl u' i t) vl < 0 := by
    have h := idx_det_vl_extChain_pos d hvl_prim hprim hperp hdetpos hnu i hdoth
      (t := t + 1) (by omega)
    rw [hext] at h
    rw [idx_det_swap (wtower d nℓ vl u' i t) vl]
    linarith
  have hB : det (wtower d nℓ vl u' i t) (extChain d nℓ vl u' i I) < 0 := by
    have h := idx_det_extChain_ccw d hvl_prim hprim hperp henv i hdoth hadj hunimod hdetpos hnu
      (a := I) (b := t + 1) hIK hK
    rw [hext] at h
    rw [idx_det_swap (wtower d nℓ vl u' i t) (extChain d nℓ vl u' i I)]
    linarith
  -- 判据用在 `j₀` 上当场破
  obtain ⟨c, hc, hh⟩ := idx_h_eq_smul_wgen d hvl_prim hprim hperp i hdoth hj₀i
  have hj := hcrit j₀
  rw [hh, idx_det_smul_left, idx_det_smul_left, hj₀eq] at hj
  nlinarith [hj, mul_pos (mul_self_pos.mpr hc) (mul_pos_of_neg_of_neg hA hB)]

/-- ⭐⭐⭐ **判据 ⟺ `I = len`。** 正向是 §12 的 `crit_false_below_top`，
反向是形参 `hlast`（lane-towerpkg 的 `hlast_good_discharge` 无条件给，`§16` 禁 import 故当形参）。

⟹ **集成者问的阈值 `I★` 就是 `len`**，`§11` 的「向上封闭」在这里退化成两点夹逼。 -/
theorem crit_iff_eq_top {B : Set (ℤ × ℤ)} (d : DecompData ξ) {vl nℓ u' : ℤ × ℤ}
    (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (henv : Nivat.LE2.EnvOf (↑d.Sphi : Set (ℤ × ℤ)) B)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0)
    (hadj : ∀ n ∈ Nivat.LE2.E (↑d.Sphi : Set (ℤ × ℤ)),
      ¬ (dot n vl < 0 ∧ 0 < dot n u'))
    (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hdetpos : 0 < det nℓ vl) (hnu : dot nℓ u' < 0)
    (hlast : ∀ j : Fin d.m, det (d.h j) vl *
      det (d.h j) (extChain d nℓ vl u' i (sortedCand d nℓ u' i).length) ≤ 0)
    {I : ℕ} (hI : I ≤ (sortedCand d nℓ u' i).length) :
    (∀ j : Fin d.m,
      det (d.h j) vl * det (d.h j) (extChain d nℓ vl u' i I) ≤ 0)
      ↔ I = (sortedCand d nℓ u' i).length := by
  constructor
  · intro hcrit
    by_contra hne
    exact crit_false_below_top d hvl_prim hprim hperp henv i hdoth hadj hunimod hdetpos hnu
      (I := I) (K := (sortedCand d nℓ u' i).length) (by omega) le_rfl hcrit
  · rintro rfl
    exact hlast

end Nivat.LaneTowerHbaseIdxDict

#print axioms Nivat.LaneTowerHbaseIdxDict.crit_false_below_top
#print axioms Nivat.LaneTowerHbaseIdxDict.crit_iff_eq_top
