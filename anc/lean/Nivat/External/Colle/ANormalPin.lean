/-
Copyright (c) 2026 Nivat Formalization Contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lane-tower-hbase
-/
import Nivat.External.Colle.LatticeEdges

/-!
# `ha_min ∧ ha_end` 唯一钉死锚点 `a`（lane-tower-hbase）

`exists_cutResidualR_of_claim46`（`Nivat/External/Colle/RegionSteps.lean`）的生成包
`obtain ⟨Sφ, a, hgenφ, hSφ, ha_min, ha_end⟩`（`RegionSteps.lean:1979-1983`，由
`Nivat.L1GenPackage.exists_gen_package'` 供给）交付两条关于锚点 `a` 的性质：

* `ha_min : ∀ b ∈ Sφ, dot m a ≤ dot m b`（`RegionSteps.lean:1982`）
* `ha_end : ∀ b ∈ Sφ, dot m b = dot m a → ∃ t : ℕ, b = a + (t : ℤ) • w`（`:1983`）

本文件只证一件事：**这两条合起来把 `a` 唯一确定**——同一个 `(S, m, w)` 上任何两个都满足它们
的点必然相等，`w ≠ 0` 是唯一的额外要求。

## 本文件在 build 里的身份（(C) 类回归护栏）

**设计上无证明项消费者**（本轮 `scripts/declscan.py --refs` 实测 `REAL=0`，分母 `FILES=388`）。
本文件是「`ha_min ∧ ha_end` 的锚点 `a` 可以挑」这条误读的回归护栏：内核结论是同一个 `(S, m, w)`
上满足这两条的点**唯一**（`a_unique_of_min_and_end`），因此台架上枚举 `w` 就是枚举整条合规支。
其余部分是一个 `by decide` 台架（`pinGens` / `pinSphi` / `pinM`）＋成对的 `good` / `bad_fails`
（`pin_ha_end_good` 对 `pin_ha_end_bad_fails`、`pin_hstrict_good` 对 `pin_hstrict_bad_fails`，
另有 `endpoint_is_load_bearing`）——`bad_fails` 那一半正是护栏本体，它只有留在 build
里才会在 `ha_end` 被写松时报警。⟹ 不是 (A) 类接线欠账，不移出 build（lane-tower-hlev 改判、
集成者 2026-09-24 第 208 轮采纳；OPEN #25 名单相应减一）。

## 原文对应（硬规矩 5）

两条前提**逐字**抄自上面那个 `obtain` 的语句，本文件没有新造任何 `Prop`。它们的原文出处是
`scratch/b3_colle2.txt:856`（Figure 11(B)，`exists_gen_package'` 的 docstring 引的那一条：
锚点取在 `𝒮_φ` 关于 `ℓ'` 的最低面的 `−w` 端），配 `:854` 逐字的射线形状
`{g + t·v⃗_{ℓ'} : t ≥ t₀}`——`t ≥ t₀` 就是 `ha_end` 里 `t : ℕ` 的原文对应物（锚在 `a` 处
把 `t₀` 归一到 `0`）。逐量词：原文的 `g` ↦ `a`，`v⃗_{ℓ'}` ↦ `w`，`t ≥ t₀` ↦ `t : ℕ`，
「最低面」↦ `ha_min` 的 `∀ b ∈ Sφ, dot m a ≤ dot m b`。

## 为什么值得单独一条

`ha_end` 的 `t : ℕ`（而不是 `t : ℤ`）此前只有**禁令式**的用途（「不许把 `a` 放宽成极小层
上的任意点」）。这条给它一个**正面**用途：因为端点是唯一的，所以在固定 `(S, m)` 的台架上
**枚举 `w` 就是枚举整条合规支**——`a` 不是可以挑的自由参数，`w` 一定 `a` 就定了。

证法：`ha_min`/`ha_min'` 互相夹出 `dot m a = dot m a'`，于是两条 `ha_end` 各给一个方向的
非负位移 `a' = a + t·w`、`a = a' + s·w`，相加得 `(t + s) • w = 0`；`w ≠ 0` 加
`smul_eq_zero` 逼出 `t + s = 0`，而 `t s : ℕ` 故 `t = 0`。全程不碰几何，没有任何
本原性 / 定向 / 凸性前提。
-/

namespace Nivat.ANormalPin

open Nivat.LE2

/-- **锚点唯一性。** 在同一个有限点集 `S` 上，若 `a` 与 `a'` 都既是 `dot m` 的极小点，
又满足「同层的点都在自己出发的 `w`-非负射线上」（`RegionSteps.lean:1982-1983` 的
`ha_min` / `ha_end`），则 `a = a'`。唯一的额外前提是 `w ≠ 0`。

原文：`scratch/b3_colle2.txt:856`（锚点 ＝ 最低面的 `−w` 端）＋ `:854`（射线 `t ≥ t₀`）。
逐量词对应见本文件抬头。 -/
theorem a_unique_of_min_and_end {w m a a' : ℤ × ℤ} {S : Finset (ℤ × ℤ)}
    (hw : w ≠ 0) (haS : a ∈ S) (ha'S : a' ∈ S)
    (hmin : ∀ b ∈ S, dot m a ≤ dot m b)
    (hmin' : ∀ b ∈ S, dot m a' ≤ dot m b)
    (hend : ∀ b ∈ S, dot m b = dot m a → ∃ t : ℕ, b = a + (t : ℤ) • w)
    (hend' : ∀ b ∈ S, dot m b = dot m a' → ∃ t : ℕ, b = a' + (t : ℤ) • w) :
    a = a' := by
  have heq : dot m a = dot m a' := le_antisymm (hmin a' ha'S) (hmin' a haS)
  obtain ⟨t, ht⟩ := hend a' ha'S heq.symm
  obtain ⟨s, hs⟩ := hend' a haS heq
  have hx : a = a + (((t : ℤ) • w) + ((s : ℤ) • w)) := by
    conv_lhs => rw [hs, ht]
    abel
  have hx2 : a + (((t : ℤ) • w) + ((s : ℤ) • w)) = a + 0 := by
    rw [add_zero]; exact hx.symm
  have h0 : ((t : ℤ) + (s : ℤ)) • w = 0 := by
    rw [add_smul]; exact add_left_cancel hx2
  rcases smul_eq_zero.mp h0 with hts | hw0
  · have ht0 : t = 0 := by omega
    rw [ht, ht0]; simp
  · exact absurd hw0 hw

#print axioms a_unique_of_min_and_end

/-! ## §2. 端点条件是承重的（lane-leafa-gen）

上面那条说的是「`ha_min ∧ ha_end` 把 `a` 钉死」。本节说的是**为什么非钉不可**：把 `ha_end`
去掉、只留 `ha_min`，洞 3 现在那条纯判据就会出现「判据真而 `hstrict` 假」的反例。

消费者侧的精确落点：`exists_cutResidualR_of_claim46`（`Nivat/External/Colle/RegionSteps.lean`）
里的 `have hstrict : ∀ b ∈ Sφ, dot m a < dot m b → dot nℓ b ≤ dot nℓ a`，现在由
`Nivat.LaneTowerHlevFanOrder.hstrict_of_det_gen_onsite`（`FanOrderCriterion.lean`；
该文件每轮都在长，按第 193 轮口径只写标识符不写行号）换成扇形判据
`∀ j, det (h j) vl * det (h j) w ≤ 0`（即 `RegionSteps.lean:2236` 剩下的那个洞口，
行号以 `scripts/sorries.sh` 为准）。**`ha_min` 与 `ha_end` 是那条引理前提表里的两项**，
本节证的就是：其中 `ha_end` 那一项不能删。

## 台架（硬规矩 6：先算数值实例）

生成元 `pinGens = [(-2,-1), (-1,-1), (-1,0)]`（两两 `det ≠ 0`），`𝒮_φ` 取其 zonotope 的
格点集 `pinSphi`，7 点。固定 `m = (1,-2)`、`w = (-2,-1)`、`vl = (1,0)`、`nℓ = (0,1)`、
`u' = (0,-1)`。判据 `∀ h ∈ pinGens, det h vl * det h w ≤ 0` 在这张台架上**恒真**，
与 `a` 无关。`dot m` 的极小层恰有两点 `(-1,0)` 与 `(-3,-1)`：

* `pinAGood = (-1,0)` 是该层的 `-w` 端点（`b3_colle2.txt:856` 的那个锚点）⟹ `ha_end` 成立，
  `hstrict` 也成立；
* `pinABad = (-3,-1)` 是同层另一点 ⟹ `ha_min` 照样成立，但 `ha_end` 需要 `t = -1`，
  `t : ℕ` 垮掉；此时 `hstrict` 在 `b = (0,0)` 处为假。

⟹ 判据与 `hstrict` 的一致性**靠 `ha_end` 的 `t : ℕ` 撑着**。这也正是 `:854` 的
`{g + t·v⃗_{ℓ'} : t ≥ t₀}` 里 `t ≥ t₀` 那半句的形式化重量所在。

⚠ 本节**不引入任何新 `Prop`**：`ha_min` / `ha_end` / `hstrict` 三个语句都逐字抄自消费者处，
只是代入了具体的数。它证伪的**只**是「判据 ⟹ `hstrict` 无需端点条件」这一写法，
不触及 `hstrict_of_det_gen_onsite` 本身（那条带着 `ha_end`，不在此列）。
-/

/-- 台架生成元：两两方向无关，对应 `DecompData.h_dir`。 -/
def pinGens : List (ℤ × ℤ) := [(-2, -1), (-1, -1), (-1, 0)]

theorem pinGens_ne : ∀ h ∈ pinGens, h ≠ (0 : ℤ × ℤ) := by decide

theorem pinGens_dir :
    det ((-2, -1) : ℤ × ℤ) ((-1, -1) : ℤ × ℤ) ≠ 0 ∧
    det ((-2, -1) : ℤ × ℤ) ((-1, 0) : ℤ × ℤ) ≠ 0 ∧
    det ((-1, -1) : ℤ × ℤ) ((-1, 0) : ℤ × ℤ) ≠ 0 := by decide

/-- `pinGens` 的 zonotope 的 H-表示。 -/
def pinZono (z : ℤ × ℤ) : Prop :=
  z.1 - 2 * z.2 ≤ 1 ∧ -z.1 + 2 * z.2 ≤ 1 ∧ z.1 ≤ z.2 ∧ z.2 - z.1 ≤ 2 ∧ -2 ≤ z.2 ∧ z.2 ≤ 0

/-- 台架的 `𝒮_φ`：`pinGens` 的 zonotope 格点集，7 点。 -/
def pinSphi : Finset (ℤ × ℤ) :=
  {(-4, -2), (-3, -2), (-3, -1), (-2, -1), (-1, -1), (-1, 0), (0, 0)}

theorem mem_pinSphi_iff (z : ℤ × ℤ) : z ∈ pinSphi ↔ pinZono z := by
  obtain ⟨x, y⟩ := z
  simp only [pinSphi, pinZono, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
  omega

def pinM : ℤ × ℤ := (1, -2)
def pinW : ℤ × ℤ := (-2, -1)
def pinVl : ℤ × ℤ := (1, 0)
def pinNl : ℤ × ℤ := (0, 1)
def pinU : ℤ × ℤ := (0, -1)

/-- `dot pinM`-极小层的 **`-w` 端点**——链上 `ha_end` 真正给的那个 `a`。 -/
def pinAGood : ℤ × ℤ := (-1, 0)

/-- 同一层里的**另一个**点：`ha_min` 照样成立，`ha_end` 的 `t : ℕ` 垮掉。 -/
def pinABad : ℤ × ℤ := (-3, -1)

/-- 台架满足消费者处那一圈几何前提。 -/
theorem pin_premises :
    dot pinM pinW = 0 ∧ 0 < dot pinM pinVl ∧ dot pinNl pinVl = 0 ∧ dot pinNl pinW < 0 ∧
    det pinVl pinW ≠ 0 ∧ (det pinU pinVl = 1 ∨ det pinU pinVl = -1) ∧
    dot pinNl pinU = -1 ∧ Prim pinW := by decide

/-- 两个 `a` 在**同一层**：`ha_min` 对两个都成立。 -/
theorem pin_same_level : dot pinM pinAGood = dot pinM pinABad := by decide

theorem pin_ha_min_good : ∀ b ∈ pinSphi, dot pinM pinAGood ≤ dot pinM b := by
  intro b hb
  rw [mem_pinSphi_iff] at hb
  simp only [pinZono] at hb
  simp only [dot, pinM, pinAGood]
  omega

theorem pin_ha_min_bad : ∀ b ∈ pinSphi, dot pinM pinABad ≤ dot pinM b := by
  intro b hb
  rw [mem_pinSphi_iff] at hb
  simp only [pinZono] at hb
  simp only [dot, pinM, pinABad]
  omega

theorem pin_level_cases : ∀ b ∈ pinSphi, dot pinM b = dot pinM pinAGood →
    b = ((-1, 0) : ℤ × ℤ) ∨ b = ((-3, -1) : ℤ × ℤ) := by
  intro b hb hl
  obtain ⟨x, y⟩ := b
  rw [mem_pinSphi_iff] at hb
  simp only [pinZono] at hb
  simp only [dot, pinM, pinAGood] at hl
  simp only [Prod.mk.injEq]
  omega

/-- **`pinAGood` 满足 `ha_end`**。 -/
theorem pin_ha_end_good :
    ∀ b ∈ pinSphi, dot pinM b = dot pinM pinAGood → ∃ t : ℕ, b = pinAGood + (t : ℤ) • pinW := by
  intro b hb hl
  rcases pin_level_cases b hb hl with h | h
  · exact ⟨0, by simp [h, pinAGood, pinW]⟩
  · exact ⟨1, by simp [h, pinAGood, pinW]⟩

/-- ⭐ **`pinABad` 不满足 `ha_end`**：同层的另一点要 `t = -1`，而链上是 `t : ℕ`。 -/
theorem pin_ha_end_bad_fails :
    ¬ (∀ b ∈ pinSphi, dot pinM b = dot pinM pinABad → ∃ t : ℕ, b = pinABad + (t : ℤ) • pinW) := by
  intro h
  obtain ⟨t, ht⟩ := h ((-1 : ℤ), (0 : ℤ)) (by decide) (by decide)
  simp only [pinABad, pinW, Prod.ext_iff, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] at ht
  omega

/-- 扇形判据在本台架上**为真**，且与 `a` 无关。 -/
theorem pin_crit : ∀ h ∈ pinGens, det h pinVl * det h pinW ≤ 0 := by decide

/-- 配 `pinAGood`（即 `ha_end` 成立时）：`hstrict` **也真**，与判据同向。 -/
theorem pin_hstrict_good :
    ∀ b ∈ pinSphi, dot pinM pinAGood < dot pinM b → dot pinNl b ≤ dot pinNl pinAGood := by
  intro b hb _
  rw [mem_pinSphi_iff] at hb
  simp only [pinZono] at hb
  simp only [dot, pinNl, pinAGood]
  omega

theorem pin_hstrict_bad_witness :
    ((0 : ℤ), (0 : ℤ)) ∈ pinSphi ∧ dot pinM pinABad < dot pinM ((0 : ℤ), (0 : ℤ)) ∧
      dot pinNl pinABad < dot pinNl ((0 : ℤ), (0 : ℤ)) := by decide

/-- ⭐ **配 `pinABad`（`ha_end` 垮掉）：判据仍真，`hstrict` 却假。** -/
theorem pin_hstrict_bad_fails :
    ¬ (∀ b ∈ pinSphi, dot pinM pinABad < dot pinM b → dot pinNl b ≤ dot pinNl pinABad) := by
  intro h
  have hb := h ((0 : ℤ), (0 : ℤ)) pin_hstrict_bad_witness.1 pin_hstrict_bad_witness.2.1
  exact absurd hb (by decide)

/-- ⭐ **端点条件承重，一条说完**：同一个 `𝒮_φ`、同一组 `m`/`w`/`vl`/`nℓ`、同一层的两个 `a`，
扇形判据恒真；`a` 取 `-w` 端点则 `hstrict` 真，取同层另一点则 `hstrict` 假。
⟹ 「判据 ⟹ `hstrict`」**必须**带着 `ha_end`，`a_unique_of_min_and_end` 钉死的正是那个 `a`。

原文：`scratch/b3_colle2.txt:854`（射线 `t ≥ t₀`）＋ `:856`（锚点取最低面的 `−w` 端）。 -/
theorem endpoint_is_load_bearing :
    (∀ h ∈ pinGens, det h pinVl * det h pinW ≤ 0) ∧
    dot pinM pinAGood = dot pinM pinABad ∧
    (∀ b ∈ pinSphi, dot pinM pinAGood ≤ dot pinM b) ∧
    (∀ b ∈ pinSphi, dot pinM pinABad ≤ dot pinM b) ∧
    (∀ b ∈ pinSphi, dot pinM b = dot pinM pinAGood → ∃ t : ℕ, b = pinAGood + (t : ℤ) • pinW) ∧
    ¬ (∀ b ∈ pinSphi, dot pinM b = dot pinM pinABad → ∃ t : ℕ, b = pinABad + (t : ℤ) • pinW) ∧
    (∀ b ∈ pinSphi, dot pinM pinAGood < dot pinM b → dot pinNl b ≤ dot pinNl pinAGood) ∧
    ¬ (∀ b ∈ pinSphi, dot pinM pinABad < dot pinM b → dot pinNl b ≤ dot pinNl pinABad) :=
  ⟨pin_crit, pin_same_level, pin_ha_min_good, pin_ha_min_bad, pin_ha_end_good,
    pin_ha_end_bad_fails, pin_hstrict_good, pin_hstrict_bad_fails⟩

#print axioms pin_ha_end_bad_fails
#print axioms pin_hstrict_bad_fails
#print axioms endpoint_is_load_bearing

end Nivat.ANormalPin
