/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.ConeCover
import Nivat.External.Colle.BottomHz0Collapse

set_option autoImplicit false

/-!
# `bottom` 的前三条 binder 在横截格里全部免费

接线文件，无新数学。把 `ConeCover.cover_of_parts`（覆盖是字段推论）喂进
`BottomHz0Collapse` 的两条三合一产者，于是 `hcov` 这条 binder 从签名里消失。

结论（`hdz_hz0_hline0_free`）：在横截格（`det p vJ1 ≠ 0`）里，只要给楔形的两条
（朝向 `hdir` ＋ 支撑界 `hsupp`），`bottom` 的 `hdz` ∧ `hz₀` ∧ `hline0` 一次到手。

⚠ 射程自限（PROTOCOL §50）：
* **只覆盖横截格**。共线格（`det p vJ1 = 0`）里 `ConeCover.heights_of_parts` 的
  `rec_vJ` 来源 `rec_vJ_of_parts_of_det_ne` 不可用，退回 `rec_vJ_of_parts`（吃 `c.bottom`）
  就成环 —— 见 `ConeCover.heights_of_parts_circular` 的警告。
  🔴 **但共线格另有产者**（第 243 轮并入）：`LeafAShellPinGrow.cover_of_latticeConvex_rec`
  （lane-leafa-shell）吃散装前提而非 `c`，`EnvRefuteOrient.supp_of_collinear`（lane-env-refute）
  证共线格 `hsupp` 由 `ahat_halfPlane_L` 免费 ⟹ **共线格的楔形债已关闭**，不必再走本文件。

* 🔴🔴 **本文件的 `hsupp` 前提在半个横截格里不可满足（第 243 轮，lane-env-refute §34）。**
  `EnvRefuteOrient.det_sign_of_supp`（`EnvRefuteOrient.lean:2311`，内核）证明
  `hsupp` ⟹ `0 ≤ det vJ1 p * det vJ1 vJ`；逆否 `not_supp_of_det_sign`（`:2335`）说两个
  行列式**严格异号**时，**任何**合法楔形法向都没有支撑界。机制是 `0 < ⟪nprevJ,p⟫` 时字段
  `rec_p` 的 `+p` 射线把 `⟪nprevJ,·⟫` 推到无穷（`not_bddAbove_of_rec`，`:2250`）。
  集成者复核的数值实例：`nJ=(0,1)`、`vJ=(1,0)`、`vJ1=(0,-1)`、`p=(-1,1)` 满足本文件
  `hdz_hz0_hline0_free` 的**每一条**前提（`hne1 : det p vJ1 = -1 ≠ 0` ✔、
  `hdir : ⟪rot vJ1, vJ⟫ = -1 < 0` ✔）而乘积 `= -1 < 0` ⟹ 那里 `hsupp` 无解。
  ⟹ 在**抽象**签名下本文件对该半格空真。

  ⭐ **再订正（同轮稍后，lane-leafa-shell `LeafAShellWedgeSign.lean`）：那半格在链上根本不存在，
  且 `hsupp` 整体免费。** `LeafAShellWedgeSign.det_sign_of_parts`（内核）证明
  `0 ≤ det vJ1 p * det vJ1 vJ` **是字段的推论**，故 `not_supp_of_det_sign` 的前提在链上
  不可满足（`not_det_sign_neg`）。集成者上面那组数值满足本文件的抽象前提，却有
  `det p vJ * det p vJ1 = (-1)·1 = -1 < 0`，与字段推论
  `EnvRefuteOrient.det_p_vJ_mul_det_p_vJ1_nonneg`（`:529`）冲突 ⟹ **它不是链上构型**。
  ⟹ 上面「半格空真」只对脱离字段的抽象签名成立，**对链上无效**；本文件在链上全格可用。
  ⟹ 而且 `hsupp` 已不必由本文件的调用者提供：`LeafAShellWedgeSign.supp_of_parts` 从字段
  （`hhp` ＋ `ahat_halfPlane_L` 两条墙）直接造出支撑界，两格通用。
  ⟹ **横截格的 `hdz` ∧ `hz₀` ∧ `hline0` 现在一条 binder 都不欠**
  （`LeafAShellWedgeSign.hdz_hz0_hline0_of_parts_transverse`）。

* `hedge`（`FanEndpoint.faceBlock_edge_forget_len`）与 `hslice`
  （`BottomReachMin.bottom_of_reachMin_merged` 第五条）不在本文件射程内。

* ⚠ **`hdir` 已不是债**（第 243 轮，lane-env-refute §33 `exists_nprevJ`，`:2047`）：
  `det vJ1 vJ ≠ 0` 是字段的代数推论，合法 `nprevJ` 在 `vJ1` 的两个旋转里按
  `det vJ1 vJ` 的**符号**挑一支即可兑现。本文件把方向写死成 `(vJ1.2, -vJ1.1)`，
  只在 `det vJ1 vJ > 0` 时是那一支 —— 抽象版 `hdz_hz0_hline0_free_wedge` 无此限制。
-/

namespace Nivat.BottomFree

open Nivat Nivat.LE2 Nivat.MaxEnv Nivat.Colle35 Nivat.ChainAsm Nivat.ChainAsm.Aparts

variable {α : Type*} {η xper : Config α} {vl p gen : ℤ × ℤ} {S : Finset (ℤ × ℤ)}

/-- ⭐⭐⭐ **横截格：`hdz` ∧ `hz₀` ∧ `hline0` 只欠楔形两条。**

对照第 241 轮的签名：`hcov`（剩余类覆盖）那条 binder 没了 —— 它由
`ConeCover.cover_of_parts c hne1` 从字段直接产出。 -/
theorem hdz_hz0_hline0_free (c : ChainDataGeomParts η xper vl p S gen)
    (hne1 : det p c.vJ1 ≠ 0) (V : ℤ × ℤ)
    (hdir : dot (c.vJ1.2, -c.vJ1.1) c.vJ < 0)
    (hsupp : ∀ z ∈ ⋃ i, hatOf c.A c.kk vl i,
      dot (c.vJ1.2, -c.vJ1.1) z ≤ dot (c.vJ1.2, -c.vJ1.1) V)
    (ε : ℕ) :
    ∃ z₀ : ℤ × ℤ, dot c.nJ z₀ = c.cJ - (ε : ℤ) - 1 ∧
      z₀ ∈ reachSet (⋃ i, hatOf c.A c.kk vl i) c.vJ1 ∧
      ∀ z ∈ reachSet (⋃ i, hatOf c.A c.kk vl i) c.vJ1,
        dot c.nJ z = c.cJ - (ε : ℤ) - 1 → ∃ k : ℤ, 0 ≤ k ∧ z = z₀ + k • c.vJ :=
  Nivat.BottomHz0Collapse.hdz_hz0_hline0_transverse c V hdir hsupp
    (Nivat.ConeCover.cover_of_parts c hne1) ε

/-- **楔形抽象版**：不固定 `nprevJ := rot vJ1`，其余同上。 -/
theorem hdz_hz0_hline0_free_wedge (c : ChainDataGeomParts η xper vl p S gen)
    (hne1 : det p c.vJ1 ≠ 0) (nprevJ V : ℤ × ℤ)
    (hnpvJ1 : dot nprevJ c.vJ1 = 0) (hnpvJ : dot nprevJ c.vJ < 0)
    (hsupp : ∀ z ∈ ⋃ i, hatOf c.A c.kk vl i, dot nprevJ z ≤ dot nprevJ V)
    (ε : ℕ) :
    ∃ z₀ : ℤ × ℤ, dot c.nJ z₀ = c.cJ - (ε : ℤ) - 1 ∧
      z₀ ∈ reachSet (⋃ i, hatOf c.A c.kk vl i) c.vJ1 ∧
      ∀ z ∈ reachSet (⋃ i, hatOf c.A c.kk vl i) c.vJ1,
        dot c.nJ z = c.cJ - (ε : ℤ) - 1 → ∃ k : ℤ, 0 ≤ k ∧ z = z₀ + k • c.vJ :=
  Nivat.BottomHz0Collapse.hdz_hz0_hline0_of_wedge c nprevJ V hnpvJ1 hnpvJ hsupp
    (Nivat.ConeCover.cover_of_parts c hne1) ε

end Nivat.BottomFree

#print axioms Nivat.BottomFree.hdz_hz0_hline0_free
#print axioms Nivat.BottomFree.hdz_hz0_hline0_free_wedge
