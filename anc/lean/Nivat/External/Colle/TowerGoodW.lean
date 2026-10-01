/-
Copyright (c) 2026 Nivat Formalization Contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lane-tower-hbase
-/
import Nivat.External.Colle.TowerConstruct
import Nivat.External.Colle.RegionNlDict

/-!
# 洞 3 的几何判据：`∀ j, det (h j) vl * det (h j) w ≤ 0` 的存在性与构造

## 消费者

`RegionSteps.lean` 的 `exists_cutResidualR_of_claim46`，体内 `have hstrict` 里那个洞口
（集成者 2026-09-24 报行号为 `:2237`，⚠ 行号会漂，认洞口下方的注释）。目标逐字符：

```lean
∀ j : Fin d.toDecompData.m,
  det (d.toDecompData.h j) vl * det (d.toDecompData.h j) w ≤ 0
```

lane-towerpkg 本轮把同一条不等式塞进塔包结论（他报 `tmp/wip/lane-towerpkg-pkg4th.lean`
的 `hlast_good`，EXIT=0；我未复核），形状是把 `w` 换成
`extChain d nℓ vl u' i (sortedCand d nℓ u' i).length`。本文件 §3 就对着那个形状证。

## ⭐ §0 关键字典：`dot nℓ x = det x vl` 逐字恒等

`Nivat.RegionNlDict.nl_eq_neg_dir_vl_and_det_u'`（`RegionNlDict.lean:87`）从
`hvl_prim` / `hperp` / `hdetpos` / `hnu` 四条**原生 binder** 给出 `nℓ = -(dir vl)`
（并顺带 `det u' vl = -1`）。代进去（`dir v = (-v.2, v.1)`，`LatticeEdges.lean:248`）：

  `dot nℓ x = vl.2 * x.1 + (-vl.1) * x.2 = x.1 * vl.2 - x.2 * vl.1 = det x vl`

**逐字相等，纯 `ring`**（`dot_nl_eq_det_vl`）。两条直接后果：

1. **`j = i` 那一格白送**：`hdoth : dot nℓ (d.h i) = 0` 在字典下**就是** `det (d.h i) vl = 0`。
   ⟹ 判据只对 `j ≠ i` 有内容。
2. 判据第 `j` 格 `= dot nℓ (d.h j) * det (d.h j) w`，这个乘积在 `d.h j ↦ -(d.h j)` 下**不变**
   （两个因子同时变号），于是可以整体搬到 `wgen d nℓ j`（`orientGen` 的 `primPart`，
   `TowerConstruct.lean:144`）上：

   > **判据 ⟺ `∀ j ≠ i, 0 ≤ det (wgen d nℓ j) w`**，即「`w` 在全部候选方向的逆时针一侧」。

而全部候选都落在开半平面 `{x : dot nℓ x < 0}` 里（`dot_wgen_neg`，`TowerConstruct.lean:159`），
半平面上 `keyOf (-nℓ)` 与角序单调同构（`det_pos_iff_key_lt`，`TowerConstruct.lean:191`）。
⟹ **取 `w` := `keyOf (-nℓ)` 最大的那个候选，判据自动成立**（`crit_of_key_max`）。

## §2 数值实例（硬规矩 6，先算后证）

台架 `dGZ`（`tmp/wip/lane-tower-hbase-sortdir.lean` §27）：`m = 4`，
`h = ![(0,1), (-1,1), (-1,0), (-1,-1)]`，`vl = (0,1)`，`nℓ = (1,0)`，`u' = (-1,1)`，`i = 0`。
`det (h j) vl` 一列恒为 `0, -1, -1, -1`；乘积列：

| `j` | `h j` | `w = u' = (-1,1)` | `w = (-1,0)` | `w = (-1,-1)` |
|---|---|---|---|---|
| 0 | `(0,1)` | `0` ✓ | `0` ✓ | `0` ✓ |
| 1 | `(-1,1)` | `0` ✓ | `-1` ✓ | `-2` ✓ |
| 2 | `(-1,0)` | **`+1`** ✗ | `0` ✓ | `-1` ✓ |
| 3 | `(-1,-1)` | **`+2`** ✗ | **`+1`** ✗ | `0` ✓ |
| | | **判据假** | **判据假** | **判据真** |

与 `sortdir.lean` §30 的 `hstrict` 三行表逐行一致。好 `w = (-1,-1)` 同时是：`h 3` 本身、
`keyOf (-nℓ)` 最大的候选（`sortedCand_GZ = [(-1,0), (-1,-1)]` 的末位）、`extChain … len`。
（本表为手算，`sortdir.lean` §32 有 `decide` 收据。）

## ⛔ 债务清单（硬规矩 5）

* §1 的 `crit_of_key_max` / `exists_good_w`：**零新增前提**。前提表
  `hvl_prim` / `hprim` / `hperp` / `hdetpos` / `hnu` / `i` / `hdoth` 全是
  `exists_cutResidualR_of_claim46` 的原生 binder；`2 ≤ d.m` 是 `DecompData.hm` 字段
  （`DecompData.lean:89`），不是前提。**没用到的原生 binder**：`hξ` / `henv` / `hBfin` /
  `hBne` / `hc` / `hbase₁` / `hunimod` / **`hadj`**。
* ⭐ **`w ≠ u'` 在 §1 里既不是前提也不是义务**：判据的语句里根本不出现 `u'`。它只在 §3
  （`w` 被要求来自 `candSet`，`TowerConstruct.lean:246` 带 `.erase u'`）才成为义务，
  而 §3 的 `crit_of_sortedCand_last_native` **已经把它兑现掉了**（`det_u'_wgen_pos`，
  杠杆是 `hadjB` ＋ `henv`，全部引理主仓现成）。
* ⛔ **全文件唯一剩下的债：`hm3 : 3 ≤ d.m`**（`DecompData.hm` 只给 `2 ≤ m`，
  `DecompData.lean:89`），只有 §3 的两条接链形用到。§1 的两条不用。
  ⚠ 另：§3 **不接消费者**，因为消费者的 `w` 由周期性下标选出——差的那一步是 `Ilean = len`
  （原文 Claim 4.10，`scratch/b3_colle2.txt:876`），本文件不声称兑现它。
-/

namespace Nivat.LaneTowerHbasePredGood

open Nivat Nivat.LE2 Nivat.ColleReg

variable {ξ : Nivat.Config ℤ}

/-! ## §0 字典与三条无前提代数 -/

private theorem hbase_det_antisymm (a b : ℤ × ℤ) : det a b = - det b a := by
  simp only [det]; ring

private theorem hbase_det_smul_left (k : ℤ) (a b : ℤ × ℤ) : det (k • a) b = k * det a b := by
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  simp only [det, Prod.smul_mk, smul_eq_mul]
  ring

private theorem hbase_det_neg_left (a b : ℤ × ℤ) : det (-a) b = - det a b := by
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  simp only [det, Prod.neg_mk]
  ring

private theorem hbase_det_smul_right (k : ℤ) (a b : ℤ × ℤ) : det a (k • b) = k * det a b := by
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  simp only [det, Prod.smul_mk, smul_eq_mul]
  ring

/-- **候选方向与生成元平行，且倍数非零**：`d.h j = c • wgen d nℓ j`，`c ≠ 0`。
符号由 `orientGen` 的 `if`（`TowerConstruct.lean:125`）定，绝对值由 `primPart_spec` 定。 -/
theorem h_eq_smul_wgen (d : Nivat.Colle35.DecompData ξ) {vl nℓ : ℤ × ℤ}
    (hvl_prim : Nivat.Primitive vl) (hprim : Nivat.LE2.Prim nℓ)
    (hperp : Nivat.LE2.dot nℓ vl = 0)
    (i : Fin d.m) (hdoth : Nivat.LE2.dot nℓ (d.h i) = 0)
    {j : Fin d.m} (hij : j ≠ i) :
    ∃ c : ℤ, c ≠ 0 ∧ d.h j = c • Nivat.ColleReg.wgen d nℓ j := by
  have hlt := Nivat.ColleReg.dot_orientGen_neg d hvl_prim hprim hperp i hdoth hij
  have hne : Nivat.ColleReg.orientGen d nℓ j ≠ 0 := by
    intro h0; rw [h0] at hlt; simp [Nivat.LE2.dot] at hlt
  obtain ⟨-, G, hGpos, hGeq⟩ := Nivat.LE2.primPart_spec hne
  have hwg : Nivat.ColleReg.wgen d nℓ j = Nivat.LE2.primPart (Nivat.ColleReg.orientGen d nℓ j) :=
    rfl
  rw [← hwg] at hGeq
  by_cases hpos : Nivat.LE2.dot nℓ (d.h j) < 0
  · refine ⟨G, by omega, ?_⟩
    have horient : Nivat.ColleReg.orientGen d nℓ j = d.h j := by
      unfold Nivat.ColleReg.orientGen; rw [if_pos hpos]
    rw [← horient]; exact hGeq
  · refine ⟨-G, by omega, ?_⟩
    have horient : Nivat.ColleReg.orientGen d nℓ j = -(d.h j) := by
      unfold Nivat.ColleReg.orientGen; rw [if_neg hpos]
    rw [horient] at hGeq
    rw [neg_smul, ← hGeq]
    simp

/-- **§0 的字典。** `nℓ = -(dir vl)` 下 `dot nℓ x` 与 `det x vl` 逐字相等。
无几何内容，纯 `ring`。 -/
theorem dot_nl_eq_det_vl {nℓ vl : ℤ × ℤ} (hnl : nℓ = -(Nivat.LE2.dir vl)) (x : ℤ × ℤ) :
    Nivat.LE2.dot nℓ x = det x vl := by
  subst hnl
  obtain ⟨v1, v2⟩ := vl
  obtain ⟨x1, x2⟩ := x
  simp only [Nivat.LE2.dot, Nivat.LE2.dir, det, Prod.neg_mk]
  ring

/-! ## §1 内容：取角序最大的候选 -/

/-- **判据第 `j` 格在 `h j ↦ ±` 下不变，可以整体搬到 `wgen` 上。**

`d.h j` 与 `wgen d nℓ j` 差一个非零整数倍（符号由 `orientGen` 的 `if` 定，倍数由
`primPart_spec` 定），而判据第 `j` 格是**两个**关于 `d.h j` 的一次因子之积，所以那个符号
平方掉、倍数平方掉：存在 `G > 0` 使第 `j` 格 `= G² ·(dot nℓ (wgen j) * det (wgen j) w)`。 -/
theorem crit_slot_eq_wgen (d : Nivat.Colle35.DecompData ξ) {vl nℓ w : ℤ × ℤ}
    (hvl_prim : Nivat.Primitive vl) (hprim : Nivat.LE2.Prim nℓ)
    (hperp : Nivat.LE2.dot nℓ vl = 0)
    (i : Fin d.m) (hdoth : Nivat.LE2.dot nℓ (d.h i) = 0)
    {j : Fin d.m} (hij : j ≠ i) :
    ∃ G : ℤ, 0 < G ∧
      Nivat.LE2.dot nℓ (d.h j) * det (d.h j) w
        = (G * G) * (Nivat.LE2.dot nℓ (Nivat.ColleReg.wgen d nℓ j) *
            det (Nivat.ColleReg.wgen d nℓ j) w) := by
  have hlt := Nivat.ColleReg.dot_orientGen_neg d hvl_prim hprim hperp i hdoth hij
  have hne : Nivat.ColleReg.orientGen d nℓ j ≠ 0 := by
    intro h0; rw [h0] at hlt; simp [Nivat.LE2.dot] at hlt
  obtain ⟨-, G, hGpos, hGeq⟩ := Nivat.LE2.primPart_spec hne
  have hwg : Nivat.ColleReg.wgen d nℓ j = Nivat.LE2.primPart (Nivat.ColleReg.orientGen d nℓ j) :=
    rfl
  rw [← hwg] at hGeq
  refine ⟨G, hGpos, ?_⟩
  have hdotsm : Nivat.LE2.dot nℓ (G • Nivat.ColleReg.wgen d nℓ j)
      = G * Nivat.LE2.dot nℓ (Nivat.ColleReg.wgen d nℓ j) := by
    rw [Nivat.LE2.dot_comm, Nivat.LE2.dot_smul,
      Nivat.LE2.dot_comm (Nivat.ColleReg.wgen d nℓ j) nℓ]
  by_cases hpos : Nivat.LE2.dot nℓ (d.h j) < 0
  · have horient : Nivat.ColleReg.orientGen d nℓ j = d.h j := by
      unfold Nivat.ColleReg.orientGen; rw [if_pos hpos]
    have hhj : d.h j = G • Nivat.ColleReg.wgen d nℓ j := by rw [← horient]; exact hGeq
    rw [hhj, hdotsm, hbase_det_smul_left]
    ring
  · have horient : Nivat.ColleReg.orientGen d nℓ j = -(d.h j) := by
      unfold Nivat.ColleReg.orientGen; rw [if_neg hpos]
    have hhj : d.h j = -(G • Nivat.ColleReg.wgen d nℓ j) := by
      rw [horient] at hGeq
      rw [← hGeq]
      simp
    rw [hhj, Nivat.LE2.dot_neg_right, hdotsm, hbase_det_neg_left, hbase_det_smul_left]
    ring

/-- **角序比较**：在开半平面 `{dot nℓ · < 0}` 上，`keyOf (-nℓ)` 不比 `b` 小的 `a` 满足
`0 ≤ det b a`。杠杆是 `det_pos_iff_key_lt`（`TowerConstruct.lean:191`）。 -/
theorem det_nonneg_of_key_le {nℓ a b : ℤ × ℤ} (hnℓ : nℓ ≠ 0)
    (ha : Nivat.LE2.dot nℓ a < 0) (hb : Nivat.LE2.dot nℓ b < 0)
    (hkey : Nivat.ColleReg.keyOf (-nℓ) a ≤ Nivat.ColleReg.keyOf (-nℓ) b) :
    0 ≤ det a b := by
  have hnz : (-nℓ) ≠ 0 := neg_ne_zero.mpr hnℓ
  have hpa : 0 < Nivat.LE2.dot (-nℓ) a := by rw [Nivat.LE2.dot_neg_left]; omega
  have hpb : 0 < Nivat.LE2.dot (-nℓ) b := by rw [Nivat.LE2.dot_neg_left]; omega
  by_contra hcon
  have hneg : det a b < 0 := by omega
  have hba : 0 < det b a := by
    have := hbase_det_antisymm a b
    omega
  have := (Nivat.ColleReg.det_pos_iff_key_lt hnz hpb hpa).mp hba
  exact absurd hkey (not_le.mpr this)

/-- ⭐ **内容条**：`w` 取 `keyOf (-nℓ)` 最大的候选 `wgen d nℓ jstar`，判据成立。

前提表**全部是 `exists_cutResidualR_of_claim46` 的原生 binder**（见文件头债务清单）；
`hadj` / `hunimod` 一次都没用到，`u'` 只经 `hnu` 进来（用于 `RegionNlDict` 的字典）。 -/
theorem crit_of_key_max (d : Nivat.Colle35.DecompData ξ) {vl nℓ u' : ℤ × ℤ}
    (hvl_prim : Nivat.Primitive vl) (hprim : Nivat.LE2.Prim nℓ)
    (hperp : Nivat.LE2.dot nℓ vl = 0) (hdetpos : 0 < det nℓ vl)
    (hnu : Nivat.LE2.dot nℓ u' = -1)
    (i : Fin d.m) (hdoth : Nivat.LE2.dot nℓ (d.h i) = 0)
    {jstar : Fin d.m} (hjstar : jstar ≠ i)
    (hmax : ∀ j : Fin d.m, j ≠ i →
      Nivat.ColleReg.keyOf (-nℓ) (Nivat.ColleReg.wgen d nℓ j) ≤
        Nivat.ColleReg.keyOf (-nℓ) (Nivat.ColleReg.wgen d nℓ jstar)) :
    ∀ j : Fin d.m,
      det (d.h j) vl * det (d.h j) (Nivat.ColleReg.wgen d nℓ jstar) ≤ 0 := by
  have hnl : nℓ = -(Nivat.LE2.dir vl) :=
    (Nivat.RegionNlDict.nl_eq_neg_dir_vl_and_det_u' hvl_prim hperp hdetpos hnu).1
  have hnℓ_ne : nℓ ≠ 0 := (Nivat.LE2.prim_iff_primitive.mp hprim).ne_zero
  intro j
  rw [← dot_nl_eq_det_vl hnl (d.h j)]
  by_cases hij : j = i
  · subst hij
    rw [hdoth]
    simp
  · obtain ⟨G, hGpos, hGeq⟩ :=
      crit_slot_eq_wgen (w := Nivat.ColleReg.wgen d nℓ jstar) d hvl_prim hprim hperp i hdoth hij
    rw [hGeq]
    have hdj : Nivat.LE2.dot nℓ (Nivat.ColleReg.wgen d nℓ j) < 0 :=
      Nivat.ColleReg.dot_wgen_neg d hvl_prim hprim hperp i hdoth hij
    have hds : Nivat.LE2.dot nℓ (Nivat.ColleReg.wgen d nℓ jstar) < 0 :=
      Nivat.ColleReg.dot_wgen_neg d hvl_prim hprim hperp i hdoth hjstar
    have hside : 0 ≤ det (Nivat.ColleReg.wgen d nℓ j) (Nivat.ColleReg.wgen d nℓ jstar) :=
      det_nonneg_of_key_le hnℓ_ne hdj hds (hmax j hij)
    have hAB : Nivat.LE2.dot nℓ (Nivat.ColleReg.wgen d nℓ j) *
        det (Nivat.ColleReg.wgen d nℓ j) (Nivat.ColleReg.wgen d nℓ jstar) ≤ 0 := by
      have h1 : 0 ≤ (- Nivat.LE2.dot nℓ (Nivat.ColleReg.wgen d nℓ j)) *
          det (Nivat.ColleReg.wgen d nℓ j) (Nivat.ColleReg.wgen d nℓ jstar) :=
        mul_nonneg (by omega) hside
      nlinarith [h1]
    have hG2 : (0 : ℤ) < G * G := mul_pos hGpos hGpos
    nlinarith [mul_nonneg hG2.le (neg_nonneg.mpr hAB)]

/-- ⭐⭐ **存在形**（集成者 2026-09-24 派的那条）。零新增前提：候选集
`Finset.univ.erase i` 非空来自 `DecompData.hm : 2 ≤ m` 字段，最大值由
`Finset.exists_max_image` 取。 -/
theorem exists_good_w (d : Nivat.Colle35.DecompDataZ ξ) {vl nℓ u' : ℤ × ℤ}
    (hvl_prim : Nivat.Primitive vl) (hprim : Nivat.LE2.Prim nℓ)
    (hperp : Nivat.LE2.dot nℓ vl = 0) (hdetpos : 0 < det nℓ vl)
    (hnu : Nivat.LE2.dot nℓ u' = -1)
    (i : Fin d.toDecompData.m)
    (hdoth : Nivat.LE2.dot nℓ (d.toDecompData.h i) = 0) :
    ∃ w : ℤ × ℤ, Nivat.Primitive w ∧ Nivat.LE2.dot nℓ w < 0 ∧
      (∀ j : Fin d.toDecompData.m,
        det (d.toDecompData.h j) vl * det (d.toDecompData.h j) w ≤ 0) := by
  classical
  have hcard : 0 < ((Finset.univ : Finset (Fin d.toDecompData.m)).erase i).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    have := d.toDecompData.hm
    omega
  obtain ⟨jstar, hjstarmem, hjstarmax⟩ :=
    Finset.exists_max_image ((Finset.univ : Finset (Fin d.toDecompData.m)).erase i)
      (fun j => Nivat.ColleReg.keyOf (-nℓ) (Nivat.ColleReg.wgen d.toDecompData nℓ j))
      (Finset.card_pos.mp hcard)
  have hjstarne : jstar ≠ i := Finset.ne_of_mem_erase hjstarmem
  refine ⟨Nivat.ColleReg.wgen d.toDecompData nℓ jstar,
    Nivat.ColleReg.wgen_prim d.toDecompData hvl_prim hprim hperp i hdoth hjstarne,
    Nivat.ColleReg.dot_wgen_neg d.toDecompData hvl_prim hprim hperp i hdoth hjstarne, ?_⟩
  exact crit_of_key_max d.toDecompData hvl_prim hprim hperp hdetpos hnu i hdoth hjstarne
    (fun j hj => hjstarmax j (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩))

/-- **候选方向在 `j ≠ i` 上互不相同。** `wgen d nℓ j` 与 `d.h j` 平行（非零倍数），
所以两个候选相等会逼出 `det (d.h j) (d.h k) = 0`，与 `DecompData.h_dir`
（`DecompData.lean:104`）矛盾。 -/
theorem wgen_ne_of_ne (d : Nivat.Colle35.DecompData ξ) {vl nℓ : ℤ × ℤ}
    (hvl_prim : Nivat.Primitive vl) (hprim : Nivat.LE2.Prim nℓ)
    (hperp : Nivat.LE2.dot nℓ vl = 0)
    (i : Fin d.m) (hdoth : Nivat.LE2.dot nℓ (d.h i) = 0)
    {j k : Fin d.m} (hji : j ≠ i) (hki : k ≠ i) (hjk : j ≠ k) :
    Nivat.ColleReg.wgen d nℓ j ≠ Nivat.ColleReg.wgen d nℓ k := by
  intro heq
  obtain ⟨cj, hcj, hhj⟩ := h_eq_smul_wgen d hvl_prim hprim hperp i hdoth hji
  obtain ⟨ck, hck, hhk⟩ := h_eq_smul_wgen d hvl_prim hprim hperp i hdoth hki
  apply d.h_dir j k hjk
  rw [hhj, hhk, heq, hbase_det_smul_left, hbase_det_smul_right]
  have : det (Nivat.ColleReg.wgen d nℓ k) (Nivat.ColleReg.wgen d nℓ k) = 0 := by
    simp only [det]; ring
  rw [this]
  ring

/-- **`3 ≤ d.m` ⟹ 候选表非空。** `.erase i` 之后还剩至少两个指标，它们的候选方向互不相同
（`wgen_ne_of_ne`），所以 `.erase u'` 至多删掉其中一个。 -/
theorem sortedCand_length_pos (d : Nivat.Colle35.DecompData ξ) {vl nℓ u' : ℤ × ℤ}
    (hvl_prim : Nivat.Primitive vl) (hprim : Nivat.LE2.Prim nℓ)
    (hperp : Nivat.LE2.dot nℓ vl = 0)
    (i : Fin d.m) (hdoth : Nivat.LE2.dot nℓ (d.h i) = 0) (hm3 : 3 ≤ d.m) :
    0 < (Nivat.ColleReg.sortedCand d nℓ u' i).length := by
  classical
  have hcard : 1 < ((Finset.univ : Finset (Fin d.m)).erase i).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨j, hjmem, k, hkmem, hjk⟩ := Finset.one_lt_card.mp hcard
  have hji : j ≠ i := Finset.ne_of_mem_erase hjmem
  have hki : k ≠ i := Finset.ne_of_mem_erase hkmem
  have hne := wgen_ne_of_ne d hvl_prim hprim hperp i hdoth hji hki hjk
  have hex : ∃ v, v ∈ Nivat.ColleReg.candSet d nℓ u' i := by
    by_cases hu : Nivat.ColleReg.wgen d nℓ j = u'
    · refine ⟨Nivat.ColleReg.wgen d nℓ k, Finset.mem_erase.mpr ⟨?_, ?_⟩⟩
      · rw [← hu]; exact fun h => hne h.symm
      · exact Finset.mem_image.mpr ⟨k, hkmem, rfl⟩
    · exact ⟨Nivat.ColleReg.wgen d nℓ j,
        Finset.mem_erase.mpr ⟨hu, Finset.mem_image.mpr ⟨j, hjmem, rfl⟩⟩⟩
  obtain ⟨v, hv⟩ := hex
  have hvS := (Nivat.ColleReg.mem_sortedCand d nℓ u' i).mpr hv
  exact List.length_pos_of_mem hvS

/-! ## §3 接链形：`w = extChain … len`（lane-towerpkg 的 `hlast_good` 逐字符形状） -/

/-- **`extChain … len` 就是 `sortedCand` 的末项。**

`det u' vl = -1`（`RegionNlDict.nl_eq_neg_dir_vl_and_det_u'` 的第二个合取，同样只吃
`hvl_prim`/`hperp`/`hdetpos`/`hnu`）⟹ `towerIdx`（`TowerConstruct.lean:374`）走 `else` 支
（恒等），于是 `extChain … (t+1) = wtower … t = sortedCand[t]`。 -/
theorem extChain_len_eq_last (d : Nivat.Colle35.DecompData ξ) {vl nℓ u' : ℤ × ℤ}
    (hvl_prim : Nivat.Primitive vl) (hperp : Nivat.LE2.dot nℓ vl = 0)
    (hdetpos : 0 < det nℓ vl) (hnu : Nivat.LE2.dot nℓ u' = -1)
    (i : Fin d.m) {t : ℕ} (ht : (Nivat.ColleReg.sortedCand d nℓ u' i).length = t + 1) :
    Nivat.ColleReg.extChain d nℓ vl u' i (Nivat.ColleReg.sortedCand d nℓ u' i).length
      = (Nivat.ColleReg.sortedCand d nℓ u' i)[t]'(by omega) := by
  have hdetu' : det u' vl = -1 :=
    (Nivat.RegionNlDict.nl_eq_neg_dir_vl_and_det_u' hvl_prim hperp hdetpos hnu).2
  have hnotpos : ¬ (0 < det u' vl) := by omega
  have hti : Nivat.ColleReg.towerIdx vl u' (Nivat.ColleReg.sortedCand d nℓ u' i).length t = t := by
    unfold Nivat.ColleReg.towerIdx
    exact if_neg hnotpos
  conv_lhs => rw [ht]
  show Nivat.ColleReg.wtower d nℓ vl u' i t = _
  rw [Nivat.ColleReg.wtower_eq_getElem
    (show t < (Nivat.ColleReg.sortedCand d nℓ u' i).length by omega)]
  simp only [hti]

/-- **排序末项是全体候选里 `keyOf (-nℓ)` 最大的。** 纯列表事实，来自
`sortedCand_pairwise`（`TowerConstruct.lean:266`）。 -/
theorem key_le_last (d : Nivat.Colle35.DecompData ξ) (nℓ u' : ℤ × ℤ) (i : Fin d.m)
    {t : ℕ} (ht : (Nivat.ColleReg.sortedCand d nℓ u' i).length = t + 1)
    {x : ℤ × ℤ} (hx : x ∈ Nivat.ColleReg.sortedCand d nℓ u' i) :
    Nivat.ColleReg.keyOf (-nℓ) x ≤
      Nivat.ColleReg.keyOf (-nℓ) ((Nivat.ColleReg.sortedCand d nℓ u' i)[t]'(by omega)) := by
  obtain ⟨k, hk, hxk⟩ := List.mem_iff_getElem.mp hx
  subst hxk
  rcases eq_or_lt_of_le (show k ≤ t by omega) with rfl | hlt
  · exact le_refl _
  · have hpw := Nivat.ColleReg.sortedCand_pairwise d nℓ u' i
    rw [List.pairwise_iff_getElem] at hpw
    have h := hpw k t hk (by omega) hlt
    simpa [Nivat.ColleReg.leKey] using h

/-- ⭐⭐ **接链形**：把 `w` 换成塔包实际交出的 `extChain d nℓ vl u' i (sortedCand …).length`
（lane-towerpkg 报他的 `hlast_good` 逐字就是这个形状，`tmp/wip/lane-towerpkg-pkg4th.lean`；
我未复核他的文件，只对着他给的语句证）。

⛔ **两条额外前提，都是债，都不是本 lane 能兑现的**：

* `hlen : 0 < (sortedCand d nℓ u' i).length` —— 候选表非空。⚠ 它**可以**从 `3 ≤ d.m`
  ＋ `wgen` 在 `j ≠ i` 上的单射性推出（`.erase u'` 至多删掉一个），但 `3 ≤ d.m` 本身是债
  （`DecompData.hm` 只给 `2 ≤ m`，`DecompData.lean:89`）。lane-env-refute 2026-09-24 报
  （纸面、未编译、我未复核）：`m = 2` 那一支上 `candSet` 恰好是空的，那时本条前提为假，
  是另一种死法，要单独处理。
* `hu'` —— `.erase u'`（`TowerConstruct.lean:246`）删掉的那个候选（若它确实是某个
  `wgen d nℓ j`）也在末项的逆时针一侧。**要从 `hadj` 来，不是从 `hnu` 来**（集成者裁决；
  lane-leafa-gen 的 `good_w_passes_hnu_hunimod` 已把 `hnu` 路线证伪）。归 lane-env-refute。
  ⚠ 它在台架上可满足：`dGZ` 上 `wgen ⟨1⟩ = u' = (-1,1)`，末项 `(-1,-1)`，
  `det (-1,1) (-1,-1) = 2 ≥ 0` ✓。

⚠ 即便这两条到手，**离接进消费者仍差一步**：消费者处的 `w` 由塔包按**周期性**下标 `Ilean`
选出（`exists_tower_index`，`TowerPackage.lean:308`，结论只有 `∃ I < Mtower` 三条周期性合取），
要它等于末项就是 `Ilean = len` ＝ 原文 Claim 4.10（`scratch/b3_colle2.txt:876`，证明在
`:878`，走 𝓚 完全周期 ＋ Lemma 4.4）。本文件**不**声称兑现它；lane-towerpkg 已把它单列为
`hIlen_eq`。 -/
theorem crit_of_sortedCand_last (d : Nivat.Colle35.DecompData ξ) {vl nℓ u' : ℤ × ℤ}
    (hvl_prim : Nivat.Primitive vl) (hprim : Nivat.LE2.Prim nℓ)
    (hperp : Nivat.LE2.dot nℓ vl = 0) (hdetpos : 0 < det nℓ vl)
    (hnu : Nivat.LE2.dot nℓ u' = -1)
    (i : Fin d.m) (hdoth : Nivat.LE2.dot nℓ (d.h i) = 0)
    (hlen : 0 < (Nivat.ColleReg.sortedCand d nℓ u' i).length)
    (hu' : ∀ j : Fin d.m, j ≠ i → Nivat.ColleReg.wgen d nℓ j = u' →
      0 ≤ det u' (Nivat.ColleReg.extChain d nℓ vl u' i
        (Nivat.ColleReg.sortedCand d nℓ u' i).length)) :
    ∀ j : Fin d.m,
      det (d.h j) vl *
        det (d.h j) (Nivat.ColleReg.extChain d nℓ vl u' i
          (Nivat.ColleReg.sortedCand d nℓ u' i).length) ≤ 0 := by
  classical
  obtain ⟨t, ht⟩ : ∃ t, (Nivat.ColleReg.sortedCand d nℓ u' i).length = t + 1 :=
    ⟨(Nivat.ColleReg.sortedCand d nℓ u' i).length - 1, by omega⟩
  have hnldict := Nivat.RegionNlDict.nl_eq_neg_dir_vl_and_det_u' hvl_prim hperp hdetpos hnu
  have hnℓ_ne : nℓ ≠ 0 := (Nivat.LE2.prim_iff_primitive.mp hprim).ne_zero
  have hext := extChain_len_eq_last d hvl_prim hperp hdetpos hnu i ht
  have hmemW : (Nivat.ColleReg.sortedCand d nℓ u' i)[t]'(by omega) ∈
      Nivat.ColleReg.sortedCand d nℓ u' i := List.getElem_mem _
  have hWcand : (Nivat.ColleReg.sortedCand d nℓ u' i)[t]'(by omega) ∈
      Nivat.ColleReg.candSet d nℓ u' i := (Nivat.ColleReg.mem_sortedCand d nℓ u' i).mp hmemW
  have hWdot : Nivat.LE2.dot nℓ ((Nivat.ColleReg.sortedCand d nℓ u' i)[t]'(by omega)) < 0 :=
    Nivat.ColleReg.dot_of_mem_candSet d hvl_prim hprim hperp i hdoth hWcand
  intro j
  rw [← dot_nl_eq_det_vl hnldict.1 (d.h j)]
  by_cases hij : j = i
  · subst hij
    rw [hdoth]
    simp
  · obtain ⟨G, hGpos, hGeq⟩ :=
      crit_slot_eq_wgen (w := Nivat.ColleReg.extChain d nℓ vl u' i
        (Nivat.ColleReg.sortedCand d nℓ u' i).length) d hvl_prim hprim hperp i hdoth hij
    rw [hGeq]
    have hdj : Nivat.LE2.dot nℓ (Nivat.ColleReg.wgen d nℓ j) < 0 :=
      Nivat.ColleReg.dot_wgen_neg d hvl_prim hprim hperp i hdoth hij
    have hside : 0 ≤ det (Nivat.ColleReg.wgen d nℓ j)
        (Nivat.ColleReg.extChain d nℓ vl u' i
          (Nivat.ColleReg.sortedCand d nℓ u' i).length) := by
      by_cases hu : Nivat.ColleReg.wgen d nℓ j = u'
      · rw [hu]
        exact hu' j hij hu
      · have hmem : Nivat.ColleReg.wgen d nℓ j ∈ Nivat.ColleReg.candSet d nℓ u' i := by
          refine Finset.mem_erase.mpr ⟨hu, Finset.mem_image.mpr ⟨j, ?_, rfl⟩⟩
          exact Finset.mem_erase.mpr ⟨hij, Finset.mem_univ j⟩
        have hmemS := (Nivat.ColleReg.mem_sortedCand d nℓ u' i).mpr hmem
        rw [hext]
        exact det_nonneg_of_key_le hnℓ_ne hdj hWdot (key_le_last d nℓ u' i ht hmemS)
    have hAB : Nivat.LE2.dot nℓ (Nivat.ColleReg.wgen d nℓ j) *
        det (Nivat.ColleReg.wgen d nℓ j)
          (Nivat.ColleReg.extChain d nℓ vl u' i
            (Nivat.ColleReg.sortedCand d nℓ u' i).length) ≤ 0 := by
      have h1 : 0 ≤ (- Nivat.LE2.dot nℓ (Nivat.ColleReg.wgen d nℓ j)) *
          det (Nivat.ColleReg.wgen d nℓ j)
            (Nivat.ColleReg.extChain d nℓ vl u' i
              (Nivat.ColleReg.sortedCand d nℓ u' i).length) :=
        mul_nonneg (by omega) hside
      nlinarith [h1]
    have hG2 : (0 : ℤ) < G * G := mul_pos hGpos hGpos
    nlinarith [mul_nonneg hG2.le (neg_nonneg.mpr hAB)]

/-- ⭐ **被 `.erase u'` 删掉的那一侧也是对的**：任何候选 `wgen d nℓ j`（`j ≠ i`，`≠ u'`）
都严格在 `u'` 的逆时针一侧。

这就是 `hadj` 真正出力的地方，全部杠杆都是主仓现成的：
`det_w_u'_sign_eq_of_hadjB`（`TowerConstruct.lean:826`）＋ `det_vl_sign_eq_of_dot_nl_neg`
（`:423`）＋ `det_ne_zero_wgen_u'_of_ne`（`:802`），再配 `det u' vl = -1`
（`RegionNlDict.lean:87` 的第二个合取）把「同号」钉成负号。
⚠ `hunimod` 不必当前提：`det u' vl = -1` 已经蕴含它。
⚠ `hadjB` 量在 `E B` 上，与 `hside_boundary_u'`（`TowerConstruct.lean:861`）和
`dot_m_extChain_nonneg`（`TowerPkgMain.lean:280`）的形参**逐字同形**，不是新债。 -/
theorem det_u'_wgen_pos {B : Set (ℤ × ℤ)} (d : Nivat.Colle35.DecompData ξ) {vl nℓ u' : ℤ × ℤ}
    (hvl_prim : Nivat.Primitive vl) (hprim : Nivat.LE2.Prim nℓ)
    (hperp : Nivat.LE2.dot nℓ vl = 0) (hdetpos : 0 < det nℓ vl)
    (hnu : Nivat.LE2.dot nℓ u' = -1)
    (henv : Nivat.LE2.EnvOf (↑d.Sphi : Set (ℤ × ℤ)) B)
    (i : Fin d.m) (hdoth : Nivat.LE2.dot nℓ (d.h i) = 0)
    (hadjB : ∀ n ∈ Nivat.LE2.E B,
      ¬ (Nivat.LE2.dot n vl < 0 ∧ 0 < Nivat.LE2.dot n u'))
    {j : Fin d.m} (hij : j ≠ i) (hwu' : Nivat.ColleReg.wgen d nℓ j ≠ u') :
    0 < det u' (Nivat.ColleReg.wgen d nℓ j) := by
  have hnu' : Nivat.LE2.dot nℓ u' < 0 := by omega
  have hdetu' : det u' vl = -1 :=
    (Nivat.RegionNlDict.nl_eq_neg_dir_vl_and_det_u' hvl_prim hperp hdetpos hnu).2
  have hunimod : det u' vl = 1 ∨ det u' vl = -1 := Or.inr hdetu'
  have hdw : Nivat.LE2.dot nℓ (Nivat.ColleReg.wgen d nℓ j) < 0 :=
    Nivat.ColleReg.dot_wgen_neg d hvl_prim hprim hperp i hdoth hij
  have hiffG : 0 < det (Nivat.ColleReg.wgen d nℓ j) vl ↔ 0 < det u' vl :=
    Nivat.ColleReg.det_vl_sign_eq_of_dot_nl_neg hprim hperp hdw hnu'
  have hiffH : 0 < det (Nivat.ColleReg.wgen d nℓ j) vl ↔
      0 < det (Nivat.ColleReg.wgen d nℓ j) u' :=
    Nivat.ColleReg.det_w_u'_sign_eq_of_hadjB d hvl_prim hprim hperp henv i hdoth hadjB
      hunimod hnu' hij hwu'
  have hne : det (Nivat.ColleReg.wgen d nℓ j) u' ≠ 0 :=
    Nivat.ColleReg.det_ne_zero_wgen_u'_of_ne d hvl_prim hprim hperp i hdoth hunimod hnu' hij hwu'
  have hnotpos : ¬ (0 < det (Nivat.ColleReg.wgen d nℓ j) u') := by
    intro h
    have h1 := hiffH.mpr h
    have h2 := hiffG.mp h1
    omega
  have hskew := hbase_det_antisymm u' (Nivat.ColleReg.wgen d nℓ j)
  omega

/-- ⭐⭐⭐ **全原生接链形**：`hu'` 不再是前提，由 `hadjB` ＋ `henv` 兑现（`det_u'_wgen_pos`）。

⛔ **唯一剩下的债是 `hm3 : 3 ≤ d.m`**（`DecompData.hm` 只给 `2 ≤ m`，`DecompData.lean:89`）。
lane-env-refute 2026-09-24 报（纸面、未编译、我未复核）：`m = 2` 那一支上 `candSet` 恰好是空的，
属另一种死法，要单独处理。

⚠ **仍然不接消费者**：这里的 `w` 是 `extChain … len`，而消费者处的 `w` 由塔包按**周期性**
下标选出（`exists_tower_index`，`TowerPackage.lean:308`，结论只有三条周期性合取）。
差的那一步是 `Ilean = len` ＝ 原文 Claim 4.10（`scratch/b3_colle2.txt:876`／证明 `:878`），
lane-towerpkg 已把它单列为 `hIlen_eq`。本文件**不**声称兑现它。 -/
theorem crit_of_sortedCand_last_native {B : Set (ℤ × ℤ)} (d : Nivat.Colle35.DecompData ξ)
    {vl nℓ u' : ℤ × ℤ}
    (hvl_prim : Nivat.Primitive vl) (hprim : Nivat.LE2.Prim nℓ)
    (hperp : Nivat.LE2.dot nℓ vl = 0) (hdetpos : 0 < det nℓ vl)
    (hnu : Nivat.LE2.dot nℓ u' = -1)
    (henv : Nivat.LE2.EnvOf (↑d.Sphi : Set (ℤ × ℤ)) B)
    (i : Fin d.m) (hdoth : Nivat.LE2.dot nℓ (d.h i) = 0)
    (hadjB : ∀ n ∈ Nivat.LE2.E B,
      ¬ (Nivat.LE2.dot n vl < 0 ∧ 0 < Nivat.LE2.dot n u'))
    (hm3 : 3 ≤ d.m) :
    ∀ j : Fin d.m,
      det (d.h j) vl *
        det (d.h j) (Nivat.ColleReg.extChain d nℓ vl u' i
          (Nivat.ColleReg.sortedCand d nℓ u' i).length) ≤ 0 := by
  classical
  have hlen := sortedCand_length_pos (u' := u') d hvl_prim hprim hperp i hdoth hm3
  refine crit_of_sortedCand_last d hvl_prim hprim hperp hdetpos hnu i hdoth hlen ?_
  intro j hij hju
  obtain ⟨t, ht⟩ : ∃ t, (Nivat.ColleReg.sortedCand d nℓ u' i).length = t + 1 :=
    ⟨(Nivat.ColleReg.sortedCand d nℓ u' i).length - 1, by omega⟩
  rw [extChain_len_eq_last d hvl_prim hperp hdetpos hnu i ht]
  have hmemW : (Nivat.ColleReg.sortedCand d nℓ u' i)[t]'(by omega) ∈
      Nivat.ColleReg.sortedCand d nℓ u' i := List.getElem_mem _
  have hWcand := (Nivat.ColleReg.mem_sortedCand d nℓ u' i).mp hmemW
  obtain ⟨hWne, hWimg⟩ := Finset.mem_erase.mp hWcand
  obtain ⟨k, hkmem, hk⟩ := Finset.mem_image.mp hWimg
  have hki : k ≠ i := (Finset.mem_erase.mp hkmem).1
  have hkne : Nivat.ColleReg.wgen d nℓ k ≠ u' := by rw [hk]; exact hWne
  rw [← hk]
  exact le_of_lt (det_u'_wgen_pos d hvl_prim hprim hperp hdetpos hnu henv i hdoth hadjB hki hkne)

end Nivat.LaneTowerHbasePredGood

#print axioms Nivat.LaneTowerHbasePredGood.dot_nl_eq_det_vl
#print axioms Nivat.LaneTowerHbasePredGood.crit_slot_eq_wgen
#print axioms Nivat.LaneTowerHbasePredGood.det_nonneg_of_key_le
#print axioms Nivat.LaneTowerHbasePredGood.crit_of_key_max
#print axioms Nivat.LaneTowerHbasePredGood.exists_good_w
#print axioms Nivat.LaneTowerHbasePredGood.extChain_len_eq_last
#print axioms Nivat.LaneTowerHbasePredGood.key_le_last
#print axioms Nivat.LaneTowerHbasePredGood.crit_of_sortedCand_last
#print axioms Nivat.LaneTowerHbasePredGood.crit_slot_eq_wgen
#print axioms Nivat.LaneTowerHbasePredGood.det_nonneg_of_key_le
#print axioms Nivat.LaneTowerHbasePredGood.crit_of_key_max
#print axioms Nivat.LaneTowerHbasePredGood.exists_good_w
#print axioms Nivat.LaneTowerHbasePredGood.h_eq_smul_wgen
#print axioms Nivat.LaneTowerHbasePredGood.wgen_ne_of_ne
#print axioms Nivat.LaneTowerHbasePredGood.sortedCand_length_pos
#print axioms Nivat.LaneTowerHbasePredGood.det_u'_wgen_pos
#print axioms Nivat.LaneTowerHbasePredGood.crit_of_sortedCand_last_native
