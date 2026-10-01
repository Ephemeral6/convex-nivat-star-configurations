/-
Copyright (c) 2026 Nivat Formalization Contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lane-towerpkg
-/
import Nivat.External.Colle.TowerPkgMain

/-!
# lane-towerpkg: exporting the **wide** recession direction of `Rinf` from the tower package

原文：`scratch/b3_colle2.txt:806`（递归句）/ `:808`（display）/ `:816` / `:820`.

## 为什么要这一条

三句原文并排：

* `:806`「we define the **`(-ℓ, ℓ_i)`-region** `ℛ_i := {g + t·v⃗_{ℓ_i} : g ∈ ℛ_{i+1}, t ∈ ℤ_+}`」，
  取 `i = I-1` ⟹ `𝓡_{I-1}` 是 `(-ℓ, ℓ_{I-1})`-region；
* `:816`「we define the **`(-ℓ, ℓ')`-region** `ℛ^n_I`」，其中 `ℓ' = ℓ_I` ⟹ 每个有限截段是
  `(-ℓ, ℓ_I)`-region；
* `:820`「`⋃_{n=0}^{∞} ℛ^n_I = ℛ_{I-1}`」。

并集的第二条边界方向是 `ℓ_{I-1}`，每个有限层的是 `ℓ_I`——**原文用两个不同的括号标注了这两个对象。**
消费者 `RegionSteps.lean:1808-1811` 的塔包 `obtain` 只导出了
`Colle41.IsRegion Rinf vl w`，`w := extChain … Ilean = v⃗_{ℓ_I}`，也就是**有限层**的那个锥；
而 `hroom`（`RegionSteps.lean:1959`）的结论 `p + u ∈ Rinf` 谈的是**并集** `𝓡_{I-1}`。
PROTOCOL §28：签名过弱只有消费者能暴露。本文件把缺的那条方向导出来。

## `I-1` 的 ℕ 减法：**根本不出现**

`ColleReg.tower` 的指标**向上**数而 Collé 的指标**向下**数
（`TowerBuild.lean:45-53` 的模块注释已写明这条对应）。在 Lean 一侧：

| 原文 | Lean |
|---|---|
| `𝓡_I` | `tower (coneRegion B vl u') (wtower … i) Ilean` |
| `𝓡_{I-1} = Rinf` | `tower (coneRegion B vl u') (wtower … i) (Ilean + 1)` |
| `v⃗_{ℓ_I} = ℓ' = w` | `extChain … i Ilean` |
| `v⃗_{ℓ_{I-1}} = wm` | `extChain … i (Ilean + 1) = wtower … i Ilean` |

所以「窄方向」是 `extChain Ilean`，「宽方向」是 `extChain (Ilean + 1)`——**两个 `+1`，没有任何减法**，
也就没有 `I = 0` 的退化分支要排除：`Ilean = 0` 时 `Rinf = tower … 1`、`w = extChain 0 = u'`、
`wm = extChain 1 = wtower 0`，和一般情形逐字符同形（`extChain` 的两个 case 由
`TowerConstruct.lean:906` 定义式给出，`extChain_succ` 是 `rfl`）。

⚠ **退化支在另一端**：`Ilean = len` 时 `wm = wtower len = -vl`（`wtower_last`，
`TowerConstruct.lean:398`），锥塌成直线。见 §5b。封闭性在两端都成立且零前提，
只有 `wm` 的三条符号事实要按 `I < len` / `I = len` 分支。

## 本文件导出什么

全部**零几何前提**（`tower_add_extChain_mem`（`TowerPkgMain.lean:608`）本身就零前提）：

* `add_mem_sweep_of_closed`（§1）——`sweep` 保持「沿某方向封闭」。这是全部内容的引擎。
* `tower_closed_extChain_le`（§2）——`k ≤ n` 时 `tower … n` 沿 `+ extChain … k` 封闭。
  `TowerPkgMain.lean:608` 只给了 `k = n` 的对角线情形。
* `rinf_closed_narrow`, `rinf_closed_wide`, `rinf_closed_three`（§3）——消费者形状：
  `Rinf = tower … (I+1)` 沿 `vl`、`w = extChain I`、`wm = extChain (I+1)` 三个方向同时封闭。
* `isRegion_of_closed`（§4）——抽象升级：`IsRegion Rinf vl w` + `wm`-封闭 ⟹ `IsRegion Rinf vl wm`。
* `rinf_isRegion_wide`（§4）——上面两条合起来，在塔上把 `IsRegion Rinf vl w` 换成
  `IsRegion Rinf vl wm`。
* `wide_package`（§5）——打包成塔包第 12 条合取的逐字符形状，附 `wm` 的三条符号事实
  （`dot nℓ wm < 0`、`dot m wm < 0`、`det vl wm ≠ 0`），符号全部转包给主仓现成件。

## ⚠ 本文件**不**主张什么

它**不**主张宽锥能补上 `hroom` / `hcone` / `hstrict`。
`tmp/wip/lane-towerpkg-hcover-nlmax.lean` §9 与第 169 轮的角区间计数都指出：多出来的这一步落在
`dot m < 0` 的半边（`dot_m_step_neg`，`TowerPkgMain.lean:180`），而 `𝒮_φ - a` 被 `ha_min`
（`RegionSteps.lean:1825`）限在 `dot m ≥ 0`，所以在 `𝒮_φ - a` 上 `cone(vl, wm)` 与 `cone(vl, w)`
给出同一个条件。导出本身独立有价值（它是原文 `:806` 的字面内容，且塔包本来就有料），
救不救得了 `hstrict` 是另一个问题。
-/

set_option autoImplicit false

open Nivat Nivat.LE2 Nivat.Colle41 Nivat.L1Region Nivat.ColleReg Nivat.ConeRegion
  Nivat.RegionSweep Nivat.Colle35

namespace Nivat.LaneTowerPkgWide

variable {ξ : Config ℤ}

/-! ## §1  引擎：`sweep` 保持方向封闭

`sweep C w = {g + t•w : g ∈ C, t ∈ ℕ}`（`RegionSweep.lean:76`）。若 `C` 沿 `+e` 封闭，
则 `(g + t•w) + e = (g + e) + t•w` 仍在 `sweep C w` 里。纯集合论，零几何前提。 -/

/-- **`sweep` 保持「沿 `+e` 封闭」。**  这是本文件全部结论的引擎：塔的每一层都是上一层的
`sweep`，所以一旦某一层沿某方向封闭，**以上所有层**都沿该方向封闭。 -/
theorem add_mem_sweep_of_closed {C : Set (ℤ × ℤ)} {e w : ℤ × ℤ}
    (hC : ∀ z ∈ C, z + e ∈ C) :
    ∀ z ∈ sweep C w, z + e ∈ sweep C w := by
  rintro z ⟨g, hg, t, rfl⟩
  exact ⟨g + e, hC g hg, t, by abel⟩

/-! ## §2  `tower … n` 沿**每一个** `extChain … k`（`k ≤ n`）封闭

`TowerPkgMain.lean:608` 的 `tower_add_extChain_mem` 只给对角线 `k = n`
（「每一层沿它自己那一步封闭」）。把 §1 沿指标往上推一次就得到全部 `k ≤ n`。
几何上：塔按 `:808` 的循环序单调旋转地扫，扫过的方向一个也不会丢。 -/

/-- **`k ≤ n` ⟹ `tower … n` 沿 `+ extChain … k` 封闭。**

原文 `:808`：`𝓡_i := {g + t·v⃗_{ℓ_i} : g ∈ 𝓡_{i+1}, t ∈ ℤ_+}`——每次 `sweep` 只**加**一条
退化方向，从不删。对 `n` 从 `k` 起归纳：底 `n = k` 是
`LaneTowerPkgMain.tower_add_extChain_mem`（`TowerPkgMain.lean:608`），
归纳步是 §1 的 `add_mem_sweep_of_closed`。零前提。 -/
theorem tower_closed_extChain_le {B : Set (ℤ × ℤ)} (d : DecompData ξ) {vl nℓ u' : ℤ × ℤ}
    (i : Fin d.m) (k : ℕ) :
    ∀ n : ℕ, k ≤ n → ∀ x ∈ tower (coneRegion B vl u') (wtower d nℓ vl u' i) n,
      x + extChain d nℓ vl u' i k ∈
        tower (coneRegion B vl u') (wtower d nℓ vl u' i) n := by
  intro n hkn
  induction n, hkn using Nat.le_induction with
  | base => exact fun x hx => LaneTowerPkgMain.tower_add_extChain_mem d i k hx
  | succ n _ ih =>
      intro x hx
      simp only [tower] at hx ⊢
      exact add_mem_sweep_of_closed ih x hx

/-! ## §3  消费者形状：`Rinf = tower … (I+1)` 的三条退化方向

`RegionSteps.lean:1808-1811` 的塔包 `obtain` 现在只给 `IsRegion Rinf vl w`，
即 `vl` 与 `w = extChain … I` 两条。第三条 `wm = extChain … (I+1) = wtower … I`
就在同一个塔上，且证明比前两条还短（它是 `tower_add_extChain_mem` 的对角线情形）。 -/

/-- `extChain` 的后继分支就是 `wtower`（`TowerConstruct.lean:906` 的定义式），`rfl`。
这条只是给阅读者钉住「宽方向 = 下一步扫的方向」。 -/
theorem extChain_succ (d : DecompData ξ) (nℓ vl u' : ℤ × ℤ) (i : Fin d.m) (t : ℕ) :
    extChain d nℓ vl u' i (t + 1) = wtower d nℓ vl u' i t := rfl

/-- **窄方向**：`Rinf = 𝓡_{I-1}` 沿 `+ w`（`w = extChain … I = v⃗_{ℓ_I}`）封闭。
`§2` 取 `k := I, n := I + 1`。 -/
theorem rinf_closed_narrow {B : Set (ℤ × ℤ)} (d : DecompData ξ) {vl nℓ u' : ℤ × ℤ}
    (i : Fin d.m) (I : ℕ) :
    ∀ z ∈ tower (coneRegion B vl u') (wtower d nℓ vl u' i) (I + 1),
      z + extChain d nℓ vl u' i I ∈
        tower (coneRegion B vl u') (wtower d nℓ vl u' i) (I + 1) :=
  tower_closed_extChain_le d i I (I + 1) (Nat.le_succ I)

/-- **宽方向**：`Rinf = 𝓡_{I-1}` 沿 `+ wm`（`wm = extChain … (I+1) = wtower … I = v⃗_{ℓ_{I-1}}`）
封闭。这正是 `:806` 的定义自带的那条（`t ∈ ℤ_+`）。
`§2` 取 `k := I + 1, n := I + 1`，即 `tower_add_extChain_mem` 的对角线。 -/
theorem rinf_closed_wide {B : Set (ℤ × ℤ)} (d : DecompData ξ) {vl nℓ u' : ℤ × ℤ}
    (i : Fin d.m) (I : ℕ) :
    ∀ z ∈ tower (coneRegion B vl u') (wtower d nℓ vl u' i) (I + 1),
      z + wtower d nℓ vl u' i I ∈
        tower (coneRegion B vl u') (wtower d nℓ vl u' i) (I + 1) :=
  fun _ hz => LaneTowerPkgMain.tower_add_extChain_mem d i (I + 1) hz

/-- **三条一起**：`Rinf` 沿 `vl`、`w = extChain … I`、`wm = wtower … I` 同时封闭。
`vl` 那条是 `ColleReg.tower_add_vl_mem`（`TowerPackage.lean:47`）。
这是 `Hole3Room.room_of_strict`（`Hole3Room.lean:117`）直接吃的形状：它的 `hvl` / `hw`
两个 binder 就是这里的第一、第二条，第三条是新料。 -/
theorem rinf_closed_three {B : Set (ℤ × ℤ)} (d : DecompData ξ) {vl nℓ u' : ℤ × ℤ}
    (i : Fin d.m) (I : ℕ) :
    ∀ z ∈ tower (coneRegion B vl u') (wtower d nℓ vl u' i) (I + 1),
      z + vl ∈ tower (coneRegion B vl u') (wtower d nℓ vl u' i) (I + 1) ∧
      z + extChain d nℓ vl u' i I ∈
        tower (coneRegion B vl u') (wtower d nℓ vl u' i) (I + 1) ∧
      z + wtower d nℓ vl u' i I ∈
        tower (coneRegion B vl u') (wtower d nℓ vl u' i) (I + 1) := by
  intro z hz
  exact ⟨tower_add_vl_mem (wtower d nℓ vl u' i) (I + 1) hz,
    rinf_closed_narrow d i I z hz, rinf_closed_wide d i I z hz⟩

/-! ## §4  抽象升级：`IsRegion Rinf vl w` + 封闭 ⟹ `IsRegion Rinf vl wm`

`Colle41.IsRegion K u u' := IsLatticeConvexRegion K ∧ (∃ z₀, RayIn K z₀ u) ∧ (∃ z₀', RayIn K z₀' u')`
（`Lemma41.lean:688`）。换第二条边方向只要换第三个合取；格凸与 `vl`-射线原封不动复用。
不需要额外的非空性：`vl`-射线在 `k = 0` 处就给出一个点。 -/

/-- **换掉 `IsRegion` 的第二条边方向。**  零几何前提（只用 `hR` 自己的两条合取 + `wm`-封闭）。 -/
theorem isRegion_of_closed {Rinf : Set (ℤ × ℤ)} {vl w wm : ℤ × ℤ}
    (hR : Colle41.IsRegion Rinf vl w)
    (hwm : ∀ z ∈ Rinf, z + wm ∈ Rinf) :
    Colle41.IsRegion Rinf vl wm := by
  refine ⟨hR.1, hR.2.1, ?_⟩
  obtain ⟨z₀, hz₀⟩ := hR.2.1
  have hz₀mem : z₀ ∈ Rinf := by simpa using hz₀ 0
  refine ⟨z₀, ?_⟩
  intro k
  induction k with
  | zero => simpa using hz₀mem
  | succ j ih =>
      have hstep := hwm _ ih
      have heq : z₀ + (j : ℤ) • wm + wm = z₀ + ((j + 1 : ℕ) : ℤ) • wm := by push_cast; module
      rwa [heq] at hstep

/-- **塔上的宽 `IsRegion`**：把 `RegionSteps.lean:1808` 那条 `hR : IsRegion Rinf vl w`
升级成 `IsRegion Rinf vl wm`，`wm = wtower … I = v⃗_{ℓ_{I-1}}`。
这是原文 `:806` 对 `𝓡_{I-1}` 的那个括号标注的 Lean 形状。 -/
theorem rinf_isRegion_wide {B : Set (ℤ × ℤ)} (d : DecompData ξ) {vl nℓ u' : ℤ × ℤ}
    (i : Fin d.m) (I : ℕ) {w : ℤ × ℤ}
    (hR : Colle41.IsRegion (tower (coneRegion B vl u') (wtower d nℓ vl u' i) (I + 1)) vl w) :
    Colle41.IsRegion (tower (coneRegion B vl u') (wtower d nℓ vl u' i) (I + 1)) vl
      (wtower d nℓ vl u' i I) :=
  isRegion_of_closed hR (rinf_closed_wide d i I)

/-! ## §5  塔包第 12 条合取的逐字符形状

消费者 `RegionSteps.lean:1808-1811` 的 `obtain` 现在是 11 条合取。本节给出第 12 条
（`wm` 与它的四条性质）的打包形状：集成者只需在那条 `∃ … ∧ …` 的末尾追加
`∧ ∃ wm, (∀ z ∈ Rinf, z + wm ∈ Rinf) ∧ dot nℓ wm < 0 ∧ dot m wm < 0 ∧ det vl wm ≠ 0`，
并在 `lane_towerpkg_reduce` 的证明里（`Rinf := tower … (Ilean+1)`、`w := extChain … Ilean`
都在 scope 内）用 `wide_package` 兑现。

三条符号事实全部转包给主仓现成件，本节不重证：

* `dot nℓ wm < 0` ← `ColleReg.dot_extChain_neg`（`TowerConstruct.lean:910`）在 `t := I + 1`；
* `dot m wm < 0` ← `LaneTowerPkgMain.dot_m_step_neg`（`TowerPkgMain.lean:180`），
  `m := expNormal (extChain … I) vl`；
* `det vl wm ≠ 0` ← `ColleReg.det_ne_zero_of_dot_nl_neg`（`TowerConstruct.lean:448`）+ 反号。

⚠ 前提表逐条取自 `dot_m_step_neg` 现场，一条没加。注意 `hI1` 这里要的是 `I + 1 ≤ len`
（宽方向比窄方向多用一格链），而塔包现有的 `hI` 是 `I ≤ len`。**这两条不等价，差的那一格是真的。**
`ColleReg.exists_tower_index`（`TowerPackage.lean:308`）产出的 `Ilean` 只满足
`Ilean < Mtower = len + 1`（`TowerConstruct.lean:389`），即 `Ilean ≤ len`——`Ilean = len` **可达**。
`§5b` 写明那一支怎么退化：那里 `wm = wtower … len = -vl`（`wtower_last`，`TowerConstruct.lean:398`），
于是 `det vl wm = 0`、`dot nℓ wm = 0`，三条符号事实里有两条**为假**，`wide_package` 不适用。

**但封闭性那一条不受影响**：`rinf_closed_wide` / `rinf_closed_three` / `rinf_isRegion_wide`
/ `wide_package_isRegion` 全部**零前提**，在 `I = len` 上照样成立
（那里它说的是 `Rinf` 同时沿 `+vl` 与 `-vl` 封闭，即 `Rinf` 被整条 `vl`-直线平移不变）。
集成者接线时按 `I < len` / `I = len` 二分：前者用 `wide_package`，后者用
`wide_package_isRegion` + `wide_dir_eq_neg_vl`。 -/

/-- `det vl wm ≠ 0`，由 `dot nℓ wm < 0` 经 `det_ne_zero_of_dot_nl_neg` 反号得到。 -/
theorem det_vl_ne_zero_of_dot_nl_neg {vl nℓ v : ℤ × ℤ} (hvl_prim : Primitive vl)
    (hperp : dot nℓ vl = 0) (hv : dot nℓ v < 0) : det vl v ≠ 0 := by
  have h := det_ne_zero_of_dot_nl_neg hvl_prim hperp hv
  intro hcon
  apply h
  have : det vl v = - det v vl := by simp only [det]; ring
  omega

/-- **塔包第 12 条合取。**  `wm := wtower … I = extChain … (I+1) = v⃗_{ℓ_{I-1}}`（原文 `:806`），
`Rinf := tower … (I+1) = 𝓡_{I-1}`，`m := expNormal (extChain … I) vl` 与消费者同一条。

四条性质：沿 `wm` 封闭（`:806` 的 `t ∈ ℤ_+`）、`dot nℓ wm < 0`（`wm` 指向 `nℓ`-下方）、
`dot m wm < 0`（**`wm` 穿过 `𝓡_I` 自己的 `ℓ'`-支撑线**，这就是它比 `w` 宽的那一步）、
`det vl wm ≠ 0`（`wm` 与 `vl` 不共线，锥非退化）。 -/
theorem wide_package {B : Set (ℤ × ℤ)} (d : DecompData ξ) {vl nℓ u' : ℤ × ℤ}
    (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (henv : Nivat.LE2.EnvOf (↑d.Sphi : Set (ℤ × ℤ)) B)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0)
    (hadjB : ∀ n ∈ E B, ¬ (dot n vl < 0 ∧ 0 < dot n u'))
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) (hnu : dot nℓ u' < 0) (hnℓ_ne : nℓ ≠ 0)
    {I : ℕ} (hI : I ≤ (sortedCand d nℓ u' i).length)
    (hI1 : I + 1 ≤ (sortedCand d nℓ u' i).length) :
    ∃ wm : ℤ × ℤ,
      (∀ z ∈ tower (coneRegion B vl u') (wtower d nℓ vl u' i) (I + 1),
        z + wm ∈ tower (coneRegion B vl u') (wtower d nℓ vl u' i) (I + 1)) ∧
      dot nℓ wm < 0 ∧
      dot (expNormal (extChain d nℓ vl u' i I) vl) wm < 0 ∧
      det vl wm ≠ 0 := by
  refine ⟨wtower d nℓ vl u' i I, rinf_closed_wide d i I, ?_, ?_, ?_⟩
  · have := dot_extChain_neg d hvl_prim hprim hperp i hdoth hnu hI1
    rwa [extChain_succ] at this
  · exact LaneTowerPkgMain.dot_m_step_neg d hvl_prim hprim hperp henv i hdoth hadjB hunimod
      hnu hnℓ_ne hI
  · refine det_vl_ne_zero_of_dot_nl_neg hvl_prim hperp ?_
    have := dot_extChain_neg d hvl_prim hprim hperp i hdoth hnu hI1
    rwa [extChain_succ] at this

/-- **`IsRegion` 版的第 12 条合取**：直接把消费者手上的 `hR` 换成宽的那条。
集成者若想少改 `obtain` 的形状，可以只追加这一条。 -/
theorem wide_package_isRegion {B : Set (ℤ × ℤ)} (d : DecompData ξ) {vl nℓ u' : ℤ × ℤ}
    (i : Fin d.m) (I : ℕ) {w : ℤ × ℤ}
    (hR : Colle41.IsRegion (tower (coneRegion B vl u') (wtower d nℓ vl u' i) (I + 1)) vl w) :
    ∃ wm : ℤ × ℤ,
      wm = wtower d nℓ vl u' i I ∧
      Colle41.IsRegion (tower (coneRegion B vl u') (wtower d nℓ vl u' i) (I + 1)) vl wm ∧
      (∀ z ∈ tower (coneRegion B vl u') (wtower d nℓ vl u' i) (I + 1),
        z + wm ∈ tower (coneRegion B vl u') (wtower d nℓ vl u' i) (I + 1)) :=
  ⟨wtower d nℓ vl u' i I, rfl, rinf_isRegion_wide d i I hR, rinf_closed_wide d i I⟩

/-! ## §5b  退化支 `I = len`：宽方向就是 `-vl`

`exists_tower_index`（`TowerPackage.lean:308`）只保证 `I < Mtower = len + 1`
（`TowerConstruct.lean:389`），所以 `I = len` 可达。`wtower` 的定义式
（`TowerConstruct.lean:383-386`）在 `k ≥ len` 分支上返回 `-vl`，于是那里
`wm = -vl`：锥 `cone(vl, wm)` 塌成一条直线，`det vl wm = 0`、`dot nℓ wm = 0`。

这不是 bug，是塔的设计：`-vl` 是链尾那一格（`wtower_last`，`TowerConstruct.lean:398`），
它存在的意义是让塔顶包住一个半平面从而**非周期**（`tower_top_contains_halfPlane`）。
`tmp/wip/lane-towerpkg-rinf-floor.lean:367` 的 `rinf_no_face_floor_of_last_neg_vl` 是同一格
在另一条性质上的表现。

所以第 12 条合取要按 `I` 二分。**封闭性在两支上都成立且零前提**，只有符号事实要分支。 -/

/-- **退化支**：`I = len` 时宽方向恰是 `-vl`（`wtower_last`）。 -/
theorem wide_dir_eq_neg_vl (d : DecompData ξ) (nℓ vl u' : ℤ × ℤ) (i : Fin d.m) :
    wtower d nℓ vl u' i (sortedCand d nℓ u' i).length = -vl :=
  wtower_last d nℓ vl u' i

/-- **退化支的几何内容**：`I = len` 时 `Rinf` 同时沿 `+vl` 与 `-vl` 封闭，
即被整条 `vl`-直线的平移群作用不变。零前提。 -/
theorem rinf_closed_neg_vl_at_len {B : Set (ℤ × ℤ)} (d : DecompData ξ) {vl nℓ u' : ℤ × ℤ}
    (i : Fin d.m) :
    ∀ z ∈ tower (coneRegion B vl u') (wtower d nℓ vl u' i)
        ((sortedCand d nℓ u' i).length + 1),
      z + vl ∈ tower (coneRegion B vl u') (wtower d nℓ vl u' i)
        ((sortedCand d nℓ u' i).length + 1) ∧
      z + -vl ∈ tower (coneRegion B vl u') (wtower d nℓ vl u' i)
        ((sortedCand d nℓ u' i).length + 1) := by
  intro z hz
  refine ⟨tower_add_vl_mem (wtower d nℓ vl u' i) _ hz, ?_⟩
  have h := rinf_closed_wide d i (sortedCand d nℓ u' i).length z hz
  rwa [wide_dir_eq_neg_vl] at h

/-- **二分**：宽方向要么落在候选链里（`I < len`，非退化，`wide_package` 适用），
要么就是 `-vl`（`I = len`，退化）。`I ≤ len` 由 `exists_tower_index` 的 `I < Mtower` 给出。 -/
theorem wide_dir_dichotomy (d : DecompData ξ) (nℓ vl u' : ℤ × ℤ) (i : Fin d.m) {I : ℕ}
    (hI : I ≤ (sortedCand d nℓ u' i).length) :
    I + 1 ≤ (sortedCand d nℓ u' i).length ∨ wtower d nℓ vl u' i I = -vl := by
  rcases Nat.lt_or_ge I (sortedCand d nℓ u' i).length with h | h
  · exact Or.inl h
  · exact Or.inr (by rw [show I = (sortedCand d nℓ u' i).length from le_antisymm hI h,
      wide_dir_eq_neg_vl])

/-! ## §6  公理检查 -/

#print axioms add_mem_sweep_of_closed
#print axioms tower_closed_extChain_le
#print axioms extChain_succ
#print axioms rinf_closed_narrow
#print axioms rinf_closed_wide
#print axioms rinf_closed_three
#print axioms isRegion_of_closed
#print axioms rinf_isRegion_wide
#print axioms det_vl_ne_zero_of_dot_nl_neg
#print axioms wide_package
#print axioms wide_package_isRegion
#print axioms wide_dir_eq_neg_vl
#print axioms rinf_closed_neg_vl_at_len
#print axioms wide_dir_dichotomy

end Nivat.LaneTowerPkgWide
