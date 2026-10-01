/-
# `bottom` 的第二合取排除一切「细」的 `Â_∞`（lane-tower-hlev）

**这条文件只做一件事**：把 `ChainDataGeomParts.bottom`（`ChainPartsFeed.lean`，字段 `bottom`）
的第二合取

    ∀ k : ℤ, L ≤ k → z₀ + k • vJ ∈ MaxEnv.reachSet (⋃ i, hatOf A kk vl i) vJ1

翻成一条**关于 `Â_∞` 维数的必要条件**：`Â_∞` 不可能整个躺在一条 `vJ1`-方向的格直线上。

## 机制（与树上已有的两条 `bottom` 反驳都不同）

`det vJ1 ·` 是 `vJ1` 方向的线性泛函，`MaxEnv.reachSet · vJ1` 的定义（`ShellLine.lean`，
`reachSet`）只往 `vJ1` 方向平移 ⟹ `det vJ1` 在 `reachSet` 上与在 `Â_∞` 上取同一组值。
若这组值是单点 `{c}`（即 `Â_∞` ⊆ 一条直线），则 `det vJ1 (z₀ + k • vJ) = det vJ1 z₀ + k · det vJ1 vJ`
必须对 `k = L` 与 `k = L+1` **同时**等于 `c` ⟹ `det vJ1 vJ = 0`。
而 `det vJ1 vJ ≠ 0` 是本结构里三条现成字段的推论（见 `thin_det_ne_zero_of_dot_eq_zero`）：
`vJ_prim`（经 `Primitive.ne_zero`）、`F.dot_nJ_vJ`、`hsweep`。⟹ 矛盾。

⚠ **与已有两条的分工，别混记（§91）**：

* `Nivat.Colle35.not_bottom_of_shell_data`（`ANormal.lean`，标识符引）用的是**层号奇偶**：
  `dot nJ vJ1 = -2` ⟹ 扫出的层是偶数，`cJ - 1` 是奇数，第一合取就不成立。它的反模型
  `A = {z | z.2 = 0}` 里 `vJ = (1,0)` 是**沿着**那条线的，不是横截的。
* `Nivat.MaxEnv.not_bottom_of_levelHalfLine`（`BottomNotEventual.lean`，标识符引）否的是
  `LevelHalfLine ⟹ BottomShape` 这条**蕴含**，用的是第三/第五合取。
* 本文件用的是**横截性**：`vJ` 被 `nJ` 钉在 `Â_∞` 所在直线的横向。三个机制互不覆盖。

## 射程自限（§50）

1. 本文件**不主张** `bottom` 在链上为假，也不主张任何现有台架的其它字段为假。它只说：
   **凡是 `⋃ i, hatOf A kk vl i` 落在单条直线上的构型，`bottom` 这一格当场不可满足。**
   反过来它**不是**「`Â_∞` 二维 ⟹ `bottom` 成立」——那个方向没有证据。
2. 前件 `∀ z ∈ Â_∞, det vJ1 z = k` 用的是**同一个 `vJ1`** 作为直线方向。`Â_∞` 落在
   **别的**方向的直线上不被本条覆盖（那种构型会先撞 `hswept`，但本文件没证这件事）。
3. `not_thin_of_parts` 是从**完整的 parts 束**里抽出来的，所以它是一条对
   `RegionSteps.exists_chainData` 一侧的**义务性**读数：任何 populator 必须交出二维的 `Â_∞`。

## import 表（与 `grep -n "^import"` 逐字一致）

    Nivat.External.Colle.ChainPartsFeed

`ChainPartsFeed` 不 import 四个禁区文件中的任何一个（实测 `grep -n "^import"`：`ItemII`、
`ANormal`、`HalfPlaneDoublyPeriodic`、`AhatMono`、`LeafAItemII`），也不在
`grep -rln "^import Nivat.External.Colle.\(RegionSteps\|ColleRegion\|Case2WindowProbe\|NfpLPreamble\)"`
的命中表里 ⟹ 不成环。
-/
import Nivat.External.Colle.ChainPartsFeed

namespace Nivat.TowerHlevBottomThin

open Nivat Nivat.LE2 Nivat.Colle35 Nivat.MaxEnv

/-- `det u` 沿 `k • v` 的仿射展开。 -/
theorem thin_det_add_zsmul (u z v : ℤ × ℤ) (k : ℤ) :
    det u (z + k • v) = det u z + k * det u v := by
  simp only [det, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- **`det vJ1` 看不见 sweep。**  `reachSet · vJ1` 只往 `vJ1` 平移，而 `det vJ1 vJ1 = 0`，
所以 `Â_∞` 上的直线条件逐字传到 `reachSet` 上。 -/
theorem det_reachSet_eq_of_thin {R : Set (ℤ × ℤ)} {v : ℤ × ℤ} {c : ℤ}
    (hthin : ∀ z ∈ R, det v z = c) :
    ∀ z ∈ MaxEnv.reachSet R v, det v z = c := by
  rintro z ⟨g, hg, t, rfl⟩
  rw [thin_det_add_zsmul, hthin g hg]
  simp only [det]
  ring

/-- **`vJ` 横截 `vJ1`**，仅由 `nJ`-侧的两条符号事实与 `vJ ≠ 0`。

链上这三条都是现成字段：`vJ ≠ 0` 由 `vJ_prim` 经 `Primitive.ne_zero`，
`dot nJ vJ = 0` 是 `F.dot_nJ_vJ`，`dot nJ vJ1 ≠ 0` 由 `hsweep : dot nJ vJ1 < 0`。 -/
theorem thin_det_ne_zero_of_dot_eq_zero {nJ vJ v : ℤ × ℤ}
    (hvJ : vJ ≠ 0) (hdot : dot nJ vJ = 0) (hn : dot nJ v ≠ 0) :
    det v vJ ≠ 0 := by
  intro hdet
  have h1 : dot nJ v * vJ.1 - dot nJ vJ * v.1 = -nJ.2 * det v vJ := by
    simp only [dot, det]; ring
  have h2 : dot nJ v * vJ.2 - dot nJ vJ * v.2 = nJ.1 * det v vJ := by
    simp only [dot, det]; ring
  rw [hdot, hdet] at h1 h2
  simp only [zero_mul, sub_zero, mul_zero] at h1 h2
  refine hvJ (Prod.ext_iff.mpr ⟨?_, ?_⟩)
  · simpa using (mul_eq_zero.mp h1).resolve_left hn
  · simpa using (mul_eq_zero.mp h2).resolve_left hn

/-- **`bottom` 的第二合取在细构型上不可满足。**  逐字是字段 `bottom` 的第二合取，
`z₀` / `L` 任给。 -/
theorem not_forall_mem_reachSet_of_thin {R : Set (ℤ × ℤ)} {v vJ : ℤ × ℤ} {c : ℤ}
    (hthin : ∀ z ∈ R, det v z = c) (hvJ : det v vJ ≠ 0) (z₀ : ℤ × ℤ) (L : ℤ) :
    ¬ (∀ k : ℤ, L ≤ k → z₀ + k • vJ ∈ MaxEnv.reachSet R v) := by
  intro h
  have h1 := det_reachSet_eq_of_thin hthin _ (h L le_rfl)
  have h2 := det_reachSet_eq_of_thin hthin _ (h (L + 1) (by omega))
  rw [thin_det_add_zsmul] at h1 h2
  refine hvJ ?_
  have hd : (L + 1) * det v vJ - L * det v vJ = det v vJ := by ring
  linarith

/-- **任何 `ChainDataGeomParts` 的 `Â_∞` 都不是细的。**

`Â_∞ = ⋃ i, hatOf A kk vl i` 不可能整条躺在一条 `vJ1`-方向的格直线上。三条输入全是本结构的
字段：`bottom`（取 `ε = 0`，只用第二合取）、`vJ_prim`、`F.dot_nJ_vJ`、`hsweep`。

⚠ 这是一条**必要条件**，不是构造：它不给出任何二维 `Â_∞`，只排除一维的。

## 第二个独立来源：`escapeW` 字段（team-lead 本轮裁决 1）

同一个结论（**`Â_∞` 必须二维**）有第二条**独立路径**，走的不是 `bottom` 而是
`ChainDataGeomParts` 的字段 `escapeW`：`Nivat.TowerHlevEscapeW2D.escapeW_concl_false_of_thin`
（`tmp/wip/hlev-escapew-2d.lean`，同 lane，**不 import**，`PROTOCOL.md §16`）。

* ⭐ 这是一条**鲁棒性**读数，**不是加强**：结论与本文件的 `not_thin_of_parts` 逐字同一句，
  强度不变；新的只有「两个互不相干的字段各自迫使同一件事」这件事本身。
  ⛔ 别把两条合起来记成一条更强的结论，也别记成「洞已兑现」。
* **死因是两条前提，不是一条**（lane-env-refute 本轮的订正，他亲读了证明体）。那条一般形
  共有**四条**前提（`hsub` / `hthin` / `hpar` / `hw`），其中两条是死因：
  `hthin : ∀ z ∈ Â_∞, det u z = k`（`Â_∞` 沿 `vJ1` 方向细）**＋**
  `hw : det u w ≠ 0`（`w` 横截那条直线）。⚠ 只写「细」会掉 `hw`，而 `hw` 恰是**可以被台架
  改掉**的那一格：换一个平行于那条直线的 `w`，`escapeW` 这条路径当场哑掉，而本文件的
  `bottom` 路径不受影响（`bottom` 那边横截性由 `F.dot_nJ_vJ` ＋ `hsweep` 强制，
  见 `thin_det_ne_zero_of_dot_eq_zero`，不是自由参数）。
  ⟹ 两条路径**不是**互为备份：本文件这条更硬，`escapeW` 那条带一个可被改掉的前提。
* ⚠ **一名两物**（`PROTOCOL.md §97`，lane-env-refute 本轮提的）：那条一般形里
  `hpar : det u vJ1 = 0` 的 `u` 是**那条细直线的配对向量**，与共线判据 `det vl vJ1 = 0`
  里的 `vl` **不是一个东西**。两条语句长得像，含义一个是「扫掠方向躺在细直线上」、
  一个是「`vl` 与 `vJ1` 共线」。⛔ 不许让下游把 `u` 代成 `vl`。
* **等级与射程**（`PROTOCOL.md §50`）：`escapeW` 那条路径是台架文件里的声明
  （`EXIT=0`、公理全白，lane-env-refute 本轮独立复跑过一次），但它**没有**被接进本文件的
  证明项里——本文件的 `not_thin_of_parts` 只吃 `bottom`。所以「两条路径」是**记账事实**，
  不是内核合成；要用 `escapeW` 那条得另外把守卫（`0 < ε` ＋ 前件）在链上兑现。 -/
theorem not_thin_of_parts {α : Type*} {η xper : Config α} {vl p : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} {gen : ℤ × ℤ}
    (c : Nivat.ChainAsm.Aparts.ChainDataGeomParts η xper vl p S gen) :
    ¬ ∃ k : ℤ, ∀ z ∈ (⋃ i, Nivat.Colle35.hatOf c.A c.kk vl i), det c.vJ1 z = k := by
  rintro ⟨k, hk⟩
  obtain ⟨z₀, L, -, h2, -, -⟩ := c.bottom 0
  exact not_forall_mem_reachSet_of_thin hk
    (thin_det_ne_zero_of_dot_eq_zero c.vJ_prim.ne_zero c.F.dot_nJ_vJ c.hsweep.ne) z₀ L h2

end Nivat.TowerHlevBottomThin

#print axioms Nivat.TowerHlevBottomThin.thin_det_add_zsmul
#print axioms Nivat.TowerHlevBottomThin.det_reachSet_eq_of_thin
#print axioms Nivat.TowerHlevBottomThin.thin_det_ne_zero_of_dot_eq_zero
#print axioms Nivat.TowerHlevBottomThin.not_forall_mem_reachSet_of_thin
#print axioms Nivat.TowerHlevBottomThin.not_thin_of_parts
