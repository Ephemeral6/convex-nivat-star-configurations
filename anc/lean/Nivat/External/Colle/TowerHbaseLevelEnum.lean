/-
Copyright (c) 2026. Released under Apache 2.0 license.
Authors: lane-tower-hbase
-/
import Nivat.External.Colle.ShellConvex

/-!
# 层号重编码是**空操作**：原文 `:442` 的 `d_i` 枚举 ＝ 我们的算术层号

原文锚：`scratch/b3_colle2.txt:442`（「把被取到的距离递增枚举为 `d_0 < d_1 < …`」）。

判定的那一问是：把 `bottom` 的层号从算术 `cJ - ε - 1` 换成原文的 `d_i`，能不能让
`hadj : det vJ vJ1 = ±1`（等价形 `dot nJ vJ1 = -1`）整条消失。

## 结果：不能，而且这件事不需要做

**离散性与下无界性两条都是真的，但都不承重：**

* 离散 —— `attainedLevels ⊆ ℤ`，`ℤ` 本身离散。不需要 `hsweep`，没有内容。
* 下无界 —— 由 `bottom` 直接给出（`attained_unbounded_below`），不需要 `hsweep : dot nJ vJ1 < 0`。

**承重的是「枚举 `d_i` 与算术 `cJ - i - 1` 是否相等」，答案是恒相等。**
`attained_of_bottom` 是内核证明：对**任意** `ChainDataGeom` 居民、**任意** `ε`，
`bottom ε` 的第 1、2 合取合起来就说「层 `cJ - ε - 1` 被 `reachSet` 取到」。
字段 `dot_nJ_vJ`（`ChainGeom.lean`，按标识符名查）让第 2 合取的点 `z₀ + L • vJ` 与 `z₀` 同层，
于是见证就是它。⟹ `attainedLevels ⊇ {c : ℤ | c < cJ}`，`d_ε = cJ - ε - 1` 逐点成立。

**对步长没有任何要求。**`attained_of_bottom` 的证明里不出现 `vJ1` 的任何性质，`hsweep` 也没用到。
所以不存在「算术层号 ＝ 被取到的层号 ⟺ `dot nJ vJ1 = -1`」这条等价：后者是前者的**充分而非必要**条件。

## 为什么我第 228 轮那个机制不适用于链

那个机制（`exists_eps_bottom_conj123`，`TowerHbaseUnitSweep.lean`，按标识符名查）从**单个种子点**
`a + wS` 出发扫掠，于是只能命中一个等差子列。链上的 `Â_∞` 不是一个点，不同的 `g` 会补齐
其它剩余类。⟹ 我第 228 轮报的是「**我那个种子形状**逼出 `-1`」，不是「`∀ ε` 逼出 `-1`」。

**精确的判别量是 `gcd (dot nJ p) (dot nJ vJ1)`，不是步长 `dot nJ vJ1` 本身**
（`TowerHbaseRecP.lean` 的 `exists_seed_level_of_rec` / `bottom_conj123_of_rec_p`，本 lane）：
单轨道可达的层恰是 `dot nJ g₀ + gcd (dot nJ p) (dot nJ vJ1) • ℤ`，
所以只要 `rec_p` 方向的高度 `dot nJ p` 与步长互素，任意 `|dot nJ vJ1| ≥ 2` 都能填满每层。
`dot nJ vJ1 = -1` 只是 `gcd = 1` 的最粗一档。

## ⛔ 本文件**不**主张的事

* 不主张 `hadj` 为真，也不主张为假。`dot nJ vJ1 = -1` 在链上为假的见证归 lane-env-refute
  （`CyclicOrderStepT.unit_sweep_not_of_chainDataGeom`；其 EXIT／公理我未复核，按 §55 记为
  「env-refute 报」）。本文件只判定：**层号重编码消不掉它，因为两套层号本来就相等。**
* 不动 `hthin`（`BottomRoom.lean`，按标识符名查）：`e > 1` 的分情形仍然是分情形。

## ⚠⚠ `ShellConvex.cgc` 的射程限定（引 `step_two_attains_every_level` 必须一起带走）

`step_two_attains_every_level` 用 `cgc` 作非空真见证。`cgc` 是**字段齐全**的 `ChainDataGeom` 居民，
但它有三条彼此独立的射程限制：

| 限制 | 内容 | 来源 |
|---|---|---|
| 零面积窗口 | `S = Sw = {0}`，单点 | 集成者记（`Step_PeriodsRays2.lean`，按名查） |
| 平凡包络 | `Env := fun _ => True`，`shellEnv` 平凡 | 同上 |
| **不满足 `exists_chainData` 的 `hdet_vl : det p vl = 0`** | `det p2 vl2 = -5 ≠ 0`（本 lane 手核） | lane-leafa-shell 量的 |

⟹ 凡是用 `cgc` 否掉的命题，否掉的是「**`ChainDataGeom` ⊨ X**」，**不是**「**链上 ⊨ X**」。
`step_two_attains_every_level` 的准确读法是「那条等价的必要方向不是 `ChainDataGeom` 的定理」，
**不能**读成「正面积窗口上 `bottom` 已有见证」。
-/

set_option autoImplicit false

namespace Nivat.HbaseLevelEnum

open Nivat Nivat.LE2 Nivat.MaxEnv

/-- **每个算术层 `cJ - ε - 1` 都被扫掠集取到，对任意居民、任意 `ε`，对步长无要求。**

原文锚：`scratch/b3_colle2.txt:442`（`d_i` 枚举）。本条说明该枚举与算术层号逐点相等。

`bottom ε` 的第 1 合取把 `z₀` 放在层 `cJ - ε - 1` 上，第 2 合取（取 `k := L`）把
`z₀ + L • vJ` 放进 `reachSet`；字段 `dot_nJ_vJ` 说这两点同层。见证即后者。

⟹ `d_ε = cJ - ε - 1`，逐 `ε` 成立，**不需要 `dot nJ vJ1 = -1`**。 -/
theorem attained_of_bottom {α : Type*} {η xper : Config α} {vl p : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} {gen : ℤ × ℤ}
    (cg : Nivat.Colle35.ChainDataGeom η xper vl p S gen) (ε : ℕ) :
    ∃ z ∈ reachSet (⋃ i, cg.toChainData.Ahat i) cg.vJ1,
      dot cg.nJ z = cg.cJ - (ε : ℤ) - 1 := by
  obtain ⟨z₀, L, hdz, hline, -, -⟩ := cg.bottom ε
  refine ⟨z₀ + L • cg.vJ, hline L le_rfl, ?_⟩
  have e : dot cg.nJ (z₀ + L • cg.vJ) = dot cg.nJ z₀ + L * dot cg.nJ cg.vJ := by
    simp only [dot, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  rw [e, cg.dot_nJ_vJ, mul_zero, add_zero, hdz]

/-- **非空真，并且否掉「算术层 ＝ 被取到层 ⟹ 步长 `-1`」的必要方向。**

`ShellConvex.cgc` 是字段齐全的 `ChainDataGeom` 居民，步长是 `-2`，而它的每个算术层仍被取到。
⟹ 那条等价只有充分方向；层号重编码消不掉 `hadj`。

⛔ **射程**：见本文件头部那张表——`cgc` 窗口是单点、包络平凡、且 `det p vl = -5 ≠ 0`
（因此它连 `exists_chainData` 的 `hdet_vl` 都不满足）。本条否掉的是
「`ChainDataGeom` ⊨ 必要方向」，**不是**「链上 ⊨ 必要方向」，也**不是**「`bottom` 已有一般见证」。 -/
theorem step_two_attains_every_level :
    dot ShellConvex.cgc.nJ ShellConvex.cgc.vJ1 = -2 ∧
    ∀ ε : ℕ, ∃ z ∈ reachSet (⋃ i, ShellConvex.cgc.toChainData.Ahat i) ShellConvex.cgc.vJ1,
      dot ShellConvex.cgc.nJ z = ShellConvex.cgc.cJ - (ε : ℤ) - 1 :=
  ⟨ShellConvex.cgc_dot_nJ_vJ1, attained_of_bottom ShellConvex.cgc⟩

/-- **下无界性，也是自由的。**`attained_of_bottom` 直接给出：任意界 `c` 之下都有被取到的层。

原文锚：`scratch/b3_colle2.txt:442` 要求 `d_i` 是无穷递增枚举，即被取到的层在 `≤ cJ` 一侧无下界。
本条说明这一条不承重：它不需要 `hsweep`，只需要 `bottom`。 -/
theorem attained_unbounded_below {α : Type*} {η xper : Config α} {vl p : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} {gen : ℤ × ℤ}
    (cg : Nivat.Colle35.ChainDataGeom η xper vl p S gen) (c : ℤ) :
    ∃ z ∈ reachSet (⋃ i, cg.toChainData.Ahat i) cg.vJ1, dot cg.nJ z < c := by
  obtain ⟨z, hz, hlev⟩ := attained_of_bottom cg (cg.cJ - c).toNat
  refine ⟨z, hz, ?_⟩
  have h : cg.cJ - c ≤ ((cg.cJ - c).toNat : ℤ) := Int.self_le_toNat _
  omega

end Nivat.HbaseLevelEnum

#print axioms Nivat.HbaseLevelEnum.attained_of_bottom
#print axioms Nivat.HbaseLevelEnum.step_two_attains_every_level
#print axioms Nivat.HbaseLevelEnum.attained_unbounded_below
