/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.FillCoverGuarded
import Nivat.External.Colle.PolyChain

/-!
# `Enveloped` 的边长子句，写成 `faceLen` 而不是 `encard`

lane-leafa-gen, 2026-09-24（第 208 轮）.  本文件把 Definition 3.2 的第二个子句从**基数**形
翻成**段长**形，供 `hwin` 那一格使用。

## 原文对应（硬规矩 5）

`scratch/b3_colle2.txt:402`（Definition 3.2）：

> A convex set `𝒯 ⊂ ℤ²` is said to be weakly `E(𝒰)`-enveloped if, for every edge `ϖ ∈ E(𝒯)`,
> there exists an edge `w ∈ E(𝒰)` parallel to `ϖ` with **`|w ∩ 𝒰| ≤ |ϖ ∩ 𝒯|`**.

逐量词对应：

| 原文 | 本文件 |
|---|---|
| `ϖ ∈ E(𝒯)` 与平行的 `w ∈ E(𝒰)` | 同一个法向 `n`（`E` 已经按法向取，平行 ⟹ 同一个 `n`） |
| `\|w ∩ 𝒰\|` | `(face U n).encard` |
| `\|ϖ ∩ 𝒯\|` | `(face T n).encard` |
| `≤` | `faceLen U n ≤ faceLen T n` |

**没有新 `Prop`。**  `faceLen T n := (face T n).encard.toNat - 1`（`PolyChain.faceLen`），
所以 `faceLen_mono_of_encard_le` 只是在两边都有限时把同一条不等式换一个刻度，
不比原文强，也没有多加量词。`hUfin` / `hTfin` 两条有限性**不是**新假设：`ℕ∞` 上
`⊤.toNat = 0`，无限面会把 `faceLen` 压成 `0`，换刻度这一步在那里才是假的；
原文 Definition 3.2 里的 `𝒰` 本来就是 "a finite, convex set"（`:402` 同句）。

## 为什么要段长形

`encard` 活在 `ℕ∞` 里，`omega` 碰不到；而 `hwin`（`FillCoverGuarded.fillCover_of_window`
的残项）那一格上所有数值推理——`ε` 的门槛、底面被 `ε`-切口吃掉几个格点——都是 `ℤ`/`ℕ` 上的
线性算术。`faceLen_le_of_enveloped_collarY` 是守卫唯一能直接交出的这类数值不等式。

## ⚠ 本文件**没有**做到什么（读之前先读这一段）

1. **它不关 `hε`。**  `belowFail_subset_reach_of_faceLen_env`（lane 文件
   `tmp/wip/lane-leafa-gen-fillcover-depth.lean` §39）的门槛是
   `ε ≤ faceLen (A_{i₀}) (-n_J)`。守卫给的是
   `faceLen ↑S (-n_J) ≤ faceLen (collarY i₀ ε) (-n_J)`——要把后者换成前者，还缺一条
   「`ε`-切口每下降一层，底边少几个格点」的**速率**，而那个速率就是 `⟪n_J, w⟫`。
   在六边形台架上它是 `-1`（斜墙 `z.1 - z.2 ≤ 2i₀+2` 斜率为 1），于是
   `faceLen (collarY i₀ ε) = 2i₀+2-ε`，守卫的 `1 ≤ 2i₀+2-ε` 正好给出
   `lane-leafa-gen-fillcover-inter.lean` 的 `eps_lt_of_enveloped`（`ε < 2i₀+2`）。
   一般情形要的正是 `⟪n_J, w⟫ = -1`，**那条在 team-lead 的 ⛔ 名单上**
   （一般 zonotope 反例：生成元 `(0,1)`、`(2,-1)` ⟹ 相邻本原法向 `(1,0)`、`(1,2)`，`det = 2`）。
   ⟹ `hw1` 不是 `ε` 路线上一条偶然多出来的前提，它是这条路线的**速率常数**。本文件只把这件事
   定位清楚，不去证它。

2. **它不是 `eps_lt_of_enveloped` 的一般化。**  那条是台架上的**数值**结论；本文件只是它的
   **引擎**（Definition 3.2 的子句换刻度），缺的正是上一条说的速率。别把两者混为一谈。

3. **本文件设计上没有证明项消费者，它是「守卫的边长不等式 ⟹ `hε`」这条死路线的回归护栏**
   （集成者第 208 轮定的 (C) 类）。护的是一条看起来很活、我自己也差点走的推断：守卫确实
   交出了一条关于 `ε` 所在集合的边长不等式（§2），于是很容易顺手写成「所以
   `ε ≤ faceLen (A_{i₀}) (-n_J)` 也是守卫给的」。**不是。**  §2 的结论里 `ε` 只出现在
   `collarY … i ε` 这个下标位置上，`faceLen` 的两边都没有把 `ε` 解出来的项；解出来要的正是
   ⚠ 1 那个速率常数。把 §2 摆在这里、并把它与 `hε` 的距离写死，比口头提醒可靠。

## 一名多物（`blueprint/NOTATION.md`）

* ⚠ **`hwin` 一名四物。**  `FillCoverGuarded.lean` 的使用警告（该文件头注的「使用警告」一段，
  按标识符 `collarY` 附近找）本轮已补到四条，第 (3) 条就是
  `Nivat.LaneTowerHlevHwin.hwin_guarded_iff`（主仓 `HwinGuard.lean`，签名已核）：它管的是
  **bottom 侧** `BottomRoom.bottom_of_window` 的 `hwin`——单基点 `z₀`、指标跑 `d.Sphi`、
  目标 `reachSet`、守卫是 `b` 上的 `0 < dot nJ (b - a)`。`fillCover_of_window` 的 `hwin`
  量**全体** `z`、指标跑 `S`、目标 `shellInter`，而且**根本没有 `0 < dot nJ (b - gen)`
  这个守卫可删**——它那个「守卫」是 `Enveloped` 前提，是另一种东西。⟹ 那条等价性不能照名字
  搬过来，两边连签名形状都不同。
* `face` / `E` / `suppVal` 都取 `Nivat.LE2` 的（本文件 `open Nivat.LE2`）；
  `faceLen` / `faceStart` 取 `Nivat.PolyChain` 的，全名书写。

## import 表

`grep -n "^import"` 恰两条：`Nivat.External.Colle.FillCoverGuarded`、
`Nivat.External.Colle.PolyChain`。两者的传递闭包里 `RegionSteps` / `ColleRegion` /
`Case2WindowProbe` / `NfpLPreamble` 命中 0（本轮自算，盲区 2）。本文件是**新模块**，
不改任何既有文件的 import 闭包。
-/

set_option autoImplicit false

namespace Nivat.EnvFaceLen

open Nivat Nivat.LE2

/-! ## §1  换刻度：`encard` 的不等式就是 `faceLen` 的不等式 -/

/-- **`encard` 序 ⟹ `faceLen` 序**（两边有限）。`faceLen T n = (face T n).encard.toNat - 1`
是 `ℕ` 上的截断减法，在两边都有限时 `toNat` 保序，于是不等式逐字过去。

有限性是必需的而不是装饰：无限面的 `encard` 是 `⊤`、`⊤.toNat = 0`、`faceLen = 0`，
那时 `encard` 的 `≤` 与 `faceLen` 的 `≤` 会反向。 -/
theorem faceLen_mono_of_encard_le {U T : Set (ℤ × ℤ)} (hUfin : U.Finite) (hTfin : T.Finite)
    {n : ℤ × ℤ} (h : (face U n).encard ≤ (face T n).encard) :
    Nivat.PolyChain.faceLen U n ≤ Nivat.PolyChain.faceLen T n := by
  obtain ⟨a, ha⟩ := (hUfin.subset (face_subset U n)).exists_encard_eq_coe
  obtain ⟨b, hb⟩ := (hTfin.subset (face_subset T n)).exists_encard_eq_coe
  rw [ha, hb] at h
  have hab : a ≤ b := by exact_mod_cast h
  unfold Nivat.PolyChain.faceLen
  rw [ha, hb, ENat.toNat_natCast, ENat.toNat_natCast]
  omega

/-- **Definition 3.2 的第二子句，段长形**（`b3_colle2.txt:402`）。
`Enveloped U T` 给出：`U` 的**每一条**边（不止 `T` 自己的边，见
`Enveloped.face_encard_le` 的 docstring）在 `T` 上都不更短。 -/
theorem faceLen_le_of_enveloped {U T : Set (ℤ × ℤ)} (hUfin : U.Finite) (hTfin : T.Finite)
    (hEU : (E U).Finite) (h : Enveloped U T) {n : ℤ × ℤ} (hn : n ∈ E U) :
    Nivat.PolyChain.faceLen U n ≤ Nivat.PolyChain.faceLen T n :=
  faceLen_mono_of_encard_le hUfin hTfin (Enveloped.face_encard_le hEU h hn)

/-! ## §2  装到 `hwin` 的守卫上

`fillCover_of_window`（`FillCoverGuarded.lean`，按标识符找）的守卫逐字是
`∀ i, i₀ ≤ i → Enveloped ↑S (collarY Ahat vJ1 nJ w cJ i ε)`，其中 `collarY` 是
`b3_colle2.txt:518` 的 `Â_i^{(ε)}`。下面这条就是那条守卫在每个 `i` 处能直接兑出的
数值不等式，`n` 跑与 `i`、`ε` 都无关的 `E ↑S`。 -/

/-- **守卫交出的数值不等式**：在守卫成立的每一层 `i`，`Â_i^{(ε)}` 的每条 `S`-边都不短于
`S` 的对应边。

`(collarY …).Finite` 由 `FillCoverGuarded.collarY_finite` 给（要 `hfin` 与
`hsweepW : ⟪n_J, w⟫ < 0`，两条都是 `ChainExhaustInter` 现成的字段 / binder）；
`(E ↑S).Finite` 由 `finite_E_of_finite S.finite_toSet` 给。

⚠ 这条**不**蕴含 `hε`，缺的速率见文件头 ⚠ 1。 -/
theorem faceLen_le_of_enveloped_collarY {S : Finset (ℤ × ℤ)} {nJ vJ1 w : ℤ × ℤ} {cJ : ℤ}
    {Ahat : ℕ → Set (ℤ × ℤ)} (hfin : ∀ i, (Ahat i).Finite) (hsweepW : dot nJ w < 0)
    {i ε : ℕ}
    (henv : Enveloped (↑S : Set (ℤ × ℤ))
      (Nivat.FillCoverGuarded.collarY Ahat vJ1 nJ w cJ i ε))
    {n : ℤ × ℤ} (hn : n ∈ E (↑S : Set (ℤ × ℤ))) :
    Nivat.PolyChain.faceLen (↑S : Set (ℤ × ℤ)) n ≤
      Nivat.PolyChain.faceLen (Nivat.FillCoverGuarded.collarY Ahat vJ1 nJ w cJ i ε) n :=
  faceLen_le_of_enveloped S.finite_toSet
    (Nivat.FillCoverGuarded.collarY_finite hfin hsweepW i ε)
    (finite_E_of_finite S.finite_toSet) henv hn

end Nivat.EnvFaceLen

#print axioms Nivat.EnvFaceLen.faceLen_mono_of_encard_le
#print axioms Nivat.EnvFaceLen.faceLen_le_of_enveloped
#print axioms Nivat.EnvFaceLen.faceLen_le_of_enveloped_collarY
