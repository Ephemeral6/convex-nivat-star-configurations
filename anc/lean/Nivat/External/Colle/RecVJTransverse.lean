/-
# ⭐⭐ `rec_vJ` 从 `ChainDataGeomParts` 的字段推出，**不经 `bottom`**（横截格）

本文件是**装配**，不是新数学。三条料本轮由三个 lane 各自落在主仓，谁都没拼：

| 料 | 出处 | 内容 |
|---|---|---|
| (A) | `TowerHbase.rec_vJ_of_real_dir`（`TowerHbaseRecP.lean:2361`，lane-tower-hbase §19） | `toReal vJ = lam • toReal W₀`、**实** `lam ≥ 0` ⟹ `rec_vJ` |
| (B) | `EnvRefuteOrient.ray_identity_of_parts`（`:555`，lane-env-refute §20） | `(⟪nJ,p⟫ * det p vJ1) • vJ = (det p vJ) • W₀`，**无前提** |
| (C) | `EnvRefuteOrient.det_p_vJ_mul_det_p_vJ1_nonneg`（`:526`，同 lane §19） | `0 ≤ det p vJ * det p vJ1`，**不经 `bottom`** |

⭐ **(B) 是等式、(C) 是符号，两者相除正好给出 (A) 要的那个非负实数 `lam`：**

    lam := (det p vJ : ℝ) / ((⟪nJ,p⟫ : ℝ) * (det p vJ1 : ℝ))

分子分母同号由 (C) 给（再乘上 `0 < ⟪nJ,p⟫`，`dot_nJ_p_pos_of_parts`），
故 `lam ≥ 0`；`lam` 是**实数**，所以 (B) 里那个整数比值**不需要整除**。

⟹ **整除那一半彻底消失**，且**一条 `bottom` 的合取都没用到**。

## 与本轮各 lane 结论的关系（逐条，按硬规矩 2 我读的是签名与证明体，不是报告）

* lane-env-refute「`rec_vJ` 精确欠三条：`det p vJ1 ≠ 0` / `det p vJ1 ∣ det p vJ` /
  `∃ a, det vJ vJ1 = det p vJ1 * a`」——**后两条（整除）不必要**。那三条是 `hcomb`
  （`∃ a t : ℕ` 的**整**组合）的精确刻画，而 `rec_vJ` **弱于** `hcomb`：
  recession cone 是实锥，只要方向对，不要求整系数。⟹ `hcomb_iff_cramer` 仍然对，
  只是 `hcomb` 不是 `rec_vJ` 的必要条件。**剩下的唯一条件是 (1) 横截 `det p vJ1 ≠ 0`。**
* lane-tower-hbase §18「符号半由 `bottom` 的第 4 合取钉死」——**符号半不需要 `bottom`**，
  (C) 已经无条件给出（他自己的 §19 与 env-refute 的 §19 是同一天落的，没拼上）。
  他的 `orient_of_bottom_exhaust` 不撤（独立为真），但**不再是 `rec_vJ` 的必经之路**。
* lane-leafa-shell「`rec_vJ` 记成缺失字段」——⛔ **本文件否掉这个立案**（横截格）。
  `rec_vJ ↔ bottom` 的环在横截格**断了**：本文件从字段直接产 `rec_vJ`，
  再喂 `rec_vJ_of_bottom` 即得 `bottom`，方向是 `字段 ⟹ rec_vJ ⟹ bottom`。
* lane-tower-hlev「横截分支活着、缺 `vJ ∈ ⟨p,vJ1⟩` 的产者」——**那个产者就是 (B)**，
  它一直在树里，无前提。hlev 的撤回（「共线分支才是死的」）是对的，且正是本文件适用的格。

## ⛔ 射程自限

0. **与 `TowerHbase.rec_vJ_of_det_sieve`（`TowerHbaseRecP.lean:2509`）重叠，两条都留**
   （盲区 3，不许删其一）。hbase 那条在抽象 `R` 层，要**两**条横截（`hdpv : det p vJ ≠ 0`
   与 `hdpv1 : det p vJ1 ≠ 0`）再加 `hsieve`；本条代在 `ChainDataGeomParts` 上，
   只要**一**条 `hdet : det p vJ1 ≠ 0`——少的那条不是被吸收，而是本证法**只除以 `D`**
   （`D := ⟪nJ,p⟫ * det p vJ1`，非零只用到 `hdet` 与 `0 < ⟪nJ,p⟫`）；`det p vJ` 出现在
   **分子**上，为零时 (B) 直接给 `D • vJ = 0` ⟹ `vJ = 0`，`lam = 0`，两条目标照样成立。

1. **只在横截格**：`hdet : det p c.vJ1 ≠ 0` 是本文件的显式 binder，**我没有它的产者**。
   共线格（`det p vJ1 = 0`）本文件不覆盖。
   ⚠ **2026-09-26 订正（lane-leafa-shell 指出本行原先误引其读法）**：上一版这里写「共线格按
   lane-leafa-shell 的读法定向免费」，**那不是他们的读法，他们从未这样说**。事实相反：
   lane-leafa-shell §22 的内核结果给出 `W₀ nJ p vJ1 = (det p vJ1) • dir nJ`（零前提），
   ⟹ 共线格里 `W₀ = 0` ⟹ **`W₀` 这条路在共线格里是死的**（另见
   `EnvRefuteOrient.W₀_eq_zero_of_collinear_of_parts`（`EnvRefuteOrient.lean:1171`）与
   `no_pos_scale_of_collinear_of_parts`（`:1185`），同向）。共线格是**未结的硬债**，不是免费。
2. `hβ : dot nJ vJ1 ≤ 0` 由字段 `hsweep : dot nJ vJ1 < 0`（`ChainPartsFeed.lean:290`）给，
   本文件取 `.le`。
3. 本文件**没有**碰 `exists_chainData` 的 `sorry`，也没有声称洞 1 关闭：`ChainDataGeomParts`
   的 37 个字段里仍有 5 条未兑现（`escapeW`/`shellSubStrip`/`shellEnv`/`fillCover`/`bottom`），
   本文件只说**其中的 `bottom` 不再被 `rec_vJ` 需要**。
   ⚠ **2026-09-26 集成者亲读订正，勿放大上一句**：`bottom` 仍是 `ChainDataGeom` 本身的字段
   （`ChainGeom.lean:132`，四合取），且 `ChainDataGeomParts.toChainDataGeom`
   （`PartsToGeom.lean:70`）把 `c.bottom` 原样喂进去。⟹ 本文件消掉的是
   **`bottom → rec_vJ` 这条推导依赖**，不是 `bottom` 这条债。洞 1 仍然欠 `bottom`。
4. 原文本轮未亲读；`:506` 的引文转自各 lane 的批注。
-/
import Nivat.External.Colle.TowerHbaseRecP
import Nivat.External.Colle.EnvRefuteOrient
import Nivat.External.Colle.RecVJFromParts

namespace Nivat.RecVJTransverse

open Nivat Nivat.LE2 Nivat.MaxEnv Nivat.Colle35 Nivat.ChainAsm.Aparts

/-- ⭐⭐ **`rec_vJ` 由字段 ＋ 横截性推出，不经 `bottom`、不经整除。**

`lam := det p vJ / (⟪nJ,p⟫ * det p vJ1)`，非负性由
`EnvRefuteOrient.det_p_vJ_mul_det_p_vJ1_nonneg` ＋ `dot_nJ_p_pos_of_parts` 给。 -/
theorem rec_vJ_of_parts_transverse {α : Type*} {η xper : Config α} {vl p gen : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} (c : ChainDataGeomParts η xper vl p S gen)
    (hdet : det p c.vJ1 ≠ 0) :
    ∀ g ∈ ⋃ i, hatOf c.A c.kk vl i, g + c.vJ ∈ ⋃ i, hatOf c.A c.kk vl i := by
  -- 字段侧
  have hα : 0 < dot c.nJ p := Nivat.EnvRefuteOrient.dot_nJ_p_pos_of_parts c
  have hβ : dot c.nJ c.vJ1 ≤ 0 := le_of_lt c.hsweep
  have hhp : ∀ z ∈ ⋃ i, hatOf c.A c.kk vl i, c.cJ ≤ dot c.nJ z := by
    intro z hz
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
    exact c.hhp i hi
  obtain ⟨g₀, hg₀⟩ := c.ahat_nonempty
  -- 符号：0 ≤ det p vJ * det p vJ1
  have hsign : 0 ≤ det p c.vJ * det p c.vJ1 :=
    Nivat.EnvRefuteOrient.det_p_vJ_mul_det_p_vJ1_nonneg c
  -- 等式：(⟪nJ,p⟫ * det p vJ1) • vJ = (det p vJ) • W₀
  have hray : ((dot c.nJ p) * det p c.vJ1) • c.vJ
      = (det p c.vJ) • Nivat.HcombOrient.W₀ c.nJ p c.vJ1 :=
    Nivat.EnvRefuteOrient.ray_identity_of_parts c
  -- 实系数
  set D : ℤ := (dot c.nJ p) * det p c.vJ1 with hD
  have hDne : D ≠ 0 := mul_ne_zero (ne_of_gt hα) hdet
  have hDR : ((D : ℤ) : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hDne
  refine Nivat.TowerHbase.rec_vJ_of_real_dir (lam := ((det p c.vJ : ℤ) : ℝ) / ((D : ℤ) : ℝ))
    (Nivat.LaneLeafAGenRecVJ.latticeConvex_of_parts c) hg₀ hhp c.rec_p c.hswept hα.le hβ ?_ ?_
  · -- 0 ≤ det p vJ / D：分子分母同号
    rcases lt_trichotomy (det p c.vJ1) 0 with hlt | heq | hgt
    · have hvJ : det p c.vJ ≤ 0 := by nlinarith
      have hDneg : D < 0 := mul_neg_of_pos_of_neg hα hlt
      exact div_nonneg_iff.mpr
        (Or.inr ⟨by exact_mod_cast hvJ, le_of_lt (by exact_mod_cast hDneg)⟩)
    · exact absurd heq hdet
    · have hvJ : 0 ≤ det p c.vJ := by nlinarith
      have hDpos : 0 < D := mul_pos hα hgt
      apply div_nonneg (by exact_mod_cast hvJ)
      exact le_of_lt (by exact_mod_cast hDpos)
  · -- toReal vJ = lam • toReal W₀
    have hcast : ((D : ℤ) : ℝ) • toReal c.vJ
        = ((det p c.vJ : ℤ) : ℝ) • toReal (Nivat.HcombOrient.W₀ c.nJ p c.vJ1) := by
      rw [← Nivat.toReal_zsmul, ← Nivat.toReal_zsmul, hray]
    rw [div_eq_inv_mul, mul_smul, ← hcast, smul_smul, inv_mul_cancel₀ hDR, one_smul]

#print axioms Nivat.RecVJTransverse.rec_vJ_of_parts_transverse

end Nivat.RecVJTransverse
