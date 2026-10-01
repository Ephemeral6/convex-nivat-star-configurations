/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.RecVJFromParts

set_option autoImplicit false

/-! # `rec_vJ` 吸收护栏：凡吃 `ChainDataGeomParts` 的 `rec_vJ` 路线一律零增量

**本文件不含新数学，是一道护栏。** 它把一条已成立但反复被忘记的事实钉成内核见证，
防止再有 lane 把轮次花在已被吞掉的签名上。

## 事实

`Nivat.LaneLeafAGenRecVJ.rec_vJ_of_parts`（`RecVJFromParts.lean`）**只吃 `c` 一个参数**
就给出 `∀ g ∈ ⋃ i, hatOf c.A c.kk vl i, g + c.vJ ∈ ⋃ i, hatOf c.A c.kk vl i`。
它走 `Colle35.rec_vJ_of_bottom`（`ItemII.lean`），五条配料 `c.hsweep` / `c.hhp` /
`c.hswept` / `c.F.dot_nJ_vJ` / **`c.bottom`** 全是结构体字段，格凸性由
`latticeConvex_of_parts` 从 `c.maxA` / `c.hfin` / `c.AhatMono` 产出。
（第 197 轮关闭，记在 `blueprint/CORE-HOLES.md` 的 (G-a) 一格。）

## 推论（本文件证的东西）

⟹ **任何形如「`c : ChainDataGeomParts …` ＋ 若干额外前提 ⟹ 同一条 `rec_vJ` 结论」的定理，
都不是增量**：拿到 `c` 就等于同时拿到了 `c.bottom`，额外前提一条都不必用。
下面五条的证明体逐字都是 `rec_vJ_of_parts c`，额外前提全部以 `_` 丢弃——这就是见证。

被吞掉的已知签名（本轮集成者普查，按标识符名列）：
`TowerHbase.rec_vJ_of_parts_unbounded_line` / `…_unbounded_line'` /
`…_nondeg_slim` / `…_nondeg` / `…_det_sieve`、
`RecVJTransverse.rec_vJ_of_parts_transverse`、
`EnvRefuteOrient.rec_vJ_of_parts_of_det_ne` / `…_of_transverse`。

## ⛔ 射程（别放大，§50）

本文件**只**否定「吃 `c` 的 `rec_vJ` 路线」的增量性，**不**否定：

1. **抽象层**。前提是裸 `R : Set (ℤ × ℤ)` 而**不吃 `c`** 的引理
   （`TowerHbase.hb_ray_of_unbounded_line`、`TowerHbase.rec_vJ_of_unbounded_line`、
   `RecessionCone.recession_of_ray`、`Colle35.ray_of_pinned_growth`）**不在射程内**，
   因为它们不预设 `bottom`。洞 1 的真欠账是**造出 `c`**，而造 `c` 必须自己兑现 `bottom`；
   抽象层正是给那件事用的工具。
2. **`bottom` 字段本身**。它是 `:500-506` 的凝结形，仍是硬债。
3. 这些被吞的定理的**其它结论**（如 `hbQ` 系列的反例、`:506` 半无限边的否定结果）。

⚠ 特别地：`subsumes_collinear` 表明**共线格（`det p vJ1 = 0`）在 `rec_vJ` 这件事上
不欠任何东西**——「共线格 `rec_vJ` 欠债」这个说法在吃 `c` 的层面上是空的。
-/

namespace Nivat.RecVJSubsume

open Nivat Nivat.LE2 Nivat.Colle35 Nivat.MaxEnv Nivat.ChainAsm Nivat.ChainAsm.Aparts

variable {α : Type*} {η xper : Config α} {vl p gen : ℤ × ℤ} {S : Finset (ℤ × ℤ)}

/-- 「沿 `vJ` 有任意远的点」这条前提可忽略
（吞掉 `TowerHbase.rec_vJ_of_parts_unbounded_line`）。 -/
theorem subsumes_unbounded_line (c : ChainDataGeomParts η xper vl p S gen)
    (z₀ : ℤ × ℤ)
    (_hz₀ : z₀ ∈ ⋃ i, hatOf c.A c.kk vl i)
    (_hunb : ∀ N : ℤ, ∃ k : ℤ, N ≤ k ∧ z₀ + k • c.vJ ∈ ⋃ i, hatOf c.A c.kk vl i) :
    ∀ g ∈ ⋃ i, hatOf c.A c.kk vl i, g + c.vJ ∈ ⋃ i, hatOf c.A c.kk vl i :=
  Nivat.LaneLeafAGenRecVJ.rec_vJ_of_parts c

/-- `det` 筛 ＋ 定符号 ＋ 横截三条可忽略
（吞掉 `TowerHbase.rec_vJ_of_parts_nondeg_slim` 及其上游）。 -/
theorem subsumes_nondeg_slim (c : ChainDataGeomParts η xper vl p S gen)
    (_hα : 0 < dot c.nJ p)
    (_hdpv1 : det p c.vJ1 ≠ 0)
    (_hsieve : 0 ≤ det p c.vJ * det p c.vJ1) :
    ∀ g ∈ ⋃ i, hatOf c.A c.kk vl i, g + c.vJ ∈ ⋃ i, hatOf c.A c.kk vl i :=
  Nivat.LaneLeafAGenRecVJ.rec_vJ_of_parts c

/-- 起点钉住 ＋ 连续初段（`hgrow` 路线）可忽略。 -/
theorem subsumes_pinned_growth (c : ChainDataGeomParts η xper vl p S gen) (g : ℤ × ℤ)
    (_hgrow : ∀ N : ℕ, ∃ i, ∀ t : ℕ, t ≤ N → g + (t : ℤ) • c.vJ ∈ hatOf c.A c.kk vl i) :
    ∀ z ∈ ⋃ i, hatOf c.A c.kk vl i, z + c.vJ ∈ ⋃ i, hatOf c.A c.kk vl i :=
  Nivat.LaneLeafAGenRecVJ.rec_vJ_of_parts c

/-- 横截格（`det p vJ1 ≠ 0`）不必单列
（吞掉 `RecVJTransverse.rec_vJ_of_parts_transverse` 一族）。 -/
theorem subsumes_transverse (c : ChainDataGeomParts η xper vl p S gen)
    (_hdpv1 : det p c.vJ1 ≠ 0) (_hα : 0 < dot c.nJ p) :
    ∀ g ∈ ⋃ i, hatOf c.A c.kk vl i, g + c.vJ ∈ ⋃ i, hatOf c.A c.kk vl i :=
  Nivat.LaneLeafAGenRecVJ.rec_vJ_of_parts c

/-- ⭐ **共线格（`det p vJ1 = 0`）在 `rec_vJ` 上不欠任何东西。**
三条 lane 花了多轮为共线格定价的那件事，在吃 `c` 的层面上是空的。 -/
theorem subsumes_collinear (c : ChainDataGeomParts η xper vl p S gen)
    (_hcol : det p c.vJ1 = 0) :
    ∀ g ∈ ⋃ i, hatOf c.A c.kk vl i, g + c.vJ ∈ ⋃ i, hatOf c.A c.kk vl i :=
  Nivat.LaneLeafAGenRecVJ.rec_vJ_of_parts c

end Nivat.RecVJSubsume

#print axioms Nivat.RecVJSubsume.subsumes_unbounded_line
#print axioms Nivat.RecVJSubsume.subsumes_nondeg_slim
#print axioms Nivat.RecVJSubsume.subsumes_pinned_growth
#print axioms Nivat.RecVJSubsume.subsumes_transverse
#print axioms Nivat.RecVJSubsume.subsumes_collinear
