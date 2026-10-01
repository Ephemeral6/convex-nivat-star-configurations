/-
Lane `lane-leafa-gen`, 2026-09-24.  主仓文件（0 `sorry`，第 203 轮由 `tmp/wip/` 落地）。

# 带守卫的 `fillCover` 归约：结论逐字是活字段类型

目标 binder：`Nivat.Colle35.ChainDataGeom.ofPartsInter` 的 `fillCover`
（`ChainAssembleInter.lean:213-221`）与 `ofPartsExhaustsInter` 的同名 binder
（`ChainExhaustInter.lean`）——两处逐字同形。消费者是
`tmp/wip/LeafAAssemble.lean:1064` 的 `(fillCover := by sorry)`，那里
`Env := EnvOf ↑d.Sphi`、`S := d.Sphi`、`gen := F.a'`、`w := wJ`。

## 原文对应（逐量词）

* `scratch/b3_colle2.txt:530` —— "Since $\mathcal{S}_{\varphi}$ is $\eta$-generating, by
  induction we get from (3.3) that $\vartheta_i|\hat{A}^{(\epsilon)}_i =
  \hat{x}_{per}|\hat{A}^{(\epsilon)}_i$"。这句是本 binder 的**整句**来源：
  「由归纳把 (3.3) 传遍 $\hat{A}^{(\epsilon)}_i$」。
* `:516` —— "for an appropriate $\epsilon\in\mathbb{N}$ **fixed** and all $i\in\mathbb{N}$
  sufficiently large"。⟹ binder 头上的 `∀ ε i₀ : ℕ, 0 < ε →` 是原文自己的量词：
  `ε` 是**先固定**的，不是对一切 `ε` 都要成立（第 159 轮据此加守卫，
  `not_fillCover_binder_exh` 否掉的正是被我们加强成 `∀ ε` 的那版）。
* `:520` —— "So let $\epsilon\in\mathbb{N}$ and $i_0\in\mathbb{N}$ be such that
  $\hat{A}_{i_0}^{(\epsilon)}$ is an $E(\mathcal{S}_{\varphi})$-enveloped set and consider a
  constant $I_0\in\mathbb{N}$ such that"。⟹ binder 里的 `Env (…)` 守卫与常数 `I₀`。
  ⚠ **2026-09-25 补一条本段漏掉的量词账：`I₀` 在原文里排在 `ε`、`i₀` 之后**（"let ε and i₀ be
  such that … **and consider a constant** `I₀`"），即 `∀ ε i₀, ∃ I₀`；而链上 `I₀` 是字段、
  `ε i₀` 在字段内部被 `∀` 掉，实际是 `∃ I₀, ∀ ε i₀`，**严格强一档**（§8 有内核反例）。
  ⛔ 但这**不是欠账**：`EscapeW.lean` §5 / `ChainExhaustInter.lean:65` 早已把这条残差关闭
  （命题对 `I₀` 反单调，接线取 `max` 即可），且 `exists_escape_abstract`（`EscapeW.lean:262`）
  已经把 `∃ I₀, ∀ ε i₀` 形正面证出来了。本段原来只记了「`I₀` 对应 `:520`」没记位置，
  是漏账；§8 最初把它记成「债」，是撞车，已在 §8 就地订正。
  ⚠ 诚实边界：`:520` 字面只要求**在 `i₀` 这一层** enveloped，而 binder 的守卫是
  `∀ i, i₀ ≤ i → Env (…)`。这比 `:520` 强，但不是我们加的——`:524` 自己把
  「$\hat{A}_i^{(\epsilon)}$ is an $E(\mathcal{S}_{\varphi})$-enveloped set」
  对 `i ≥ max{i₀,I₀}` 重新陈述了一遍。本文件**只消费**该守卫，不生产它
  （生产方是 `shellEnv`，不在本文件范围内）。
* `:524` —— "if we consider $i\geq\max\{i_0,I_0\}$"。⟹ binder 尾部的
  `∀ i, max i₀ I₀ ≤ i →`。本文件的结论把守卫放宽到 `∀ i, i₀ ≤ i →`（**更强**，
  因为 `max i₀ I₀ ≤ i → i₀ ≤ i`），所以直接可以填字段；放宽是免费的，
  归约本身从不用 `I₀`。
  ⚠ **2026-09-25 补账（§14，原话留着）：「放宽是免费的」只对归约方向成立。**
  对**残项**方向它是收费的 —— `fillCover_of_window` 的 `hwin` 因此必须对一切 `i ≥ i₀` 证，
  而字段只要求 `i ≥ max i₀ I₀`。§9 把 `I₀` 交还给残项
  （`fillCover_field_of_window_at_I₀`），并记下这个救法**不管用**的内核理由
  （`HwinRefute.lean` §6 `not_HwinI₀_oct8`：oct8 上的障碍对 `i` 一致）。
* `:518` —— `$\hat{A}_{i}^{(\epsilon)}:=\{g-t\vec{v}_{\ell_{J+1}}\in\hat{A}^{(\epsilon)}_{\infty}
  :g\in\hat{A}_{i},\ t\in\mathbb{Z}_{+}\}$`。⟹ `collarY` 的定义（`w := -v_{ℓ_{J+1}}`）。

## 与已落地的 `FillCoverReduce.lean` 的差别（PROTOCOL §52，必须写出差）

`Nivat.LaneFillCover.fillCover_of_local_step`（`FillCoverReduce.lean:241`）已在主仓、0 sorry。
本文件**不是**它的重复，两条在两个格子上都不同：

| | `FillCoverReduce.fillCover_of_local_step` | 本文件 `fillCover_of_window` |
|---|---|---|
| 结论 | `⋃ n, genFill S gen X n`（＝ `MaxEnv.genClosure`，**单生成元**） | `{z ∣ Colle37.GenClosure S X z}`（**全生成元**，活字段的形状） |
| 守卫 | `∀ i i₀ ε, i₀ ≤ i →`（无 `0 < ε`、无 `Env`） | `∀ ε i₀, 0 < ε → (∀ i, i₀ ≤ i → EnvOf ↑S (…)) → ∀ i, i₀ ≤ i →` |
| 残项能拿到什么 | 只有 `i₀ ≤ i` | 另加 `0 < ε` 与整条 `Enveloped` 守卫 |
| 是否被现有反例波及 | 结论是第 81 轮 `not_fillCover_at_a'` 否掉的形状 | 不是那个形状；守卫也挡掉了 `not_fillCover_binder_exh` 的 `ε = 5` 那支 |

⟹ 单生成元结论是**更强**的陈述，`fillCover_of_local_step` 的残项 `hstepLocal` 因此比本文件的
`hwin` 更难（读法，非内核事实，PROTOCOL §15：没有内核见证前不要把它写成「已证为假」）。
本文件经 `GenClosureWeaken.genClosure_subset_genClosure`（`GenClosureWeaken.lean:70`）
把单生成元塔翻成 `Colle37.GenClosure` 之后，`hconv` 由
`Colle37Geom.latticeConvex_erase_of_lexExtreme`（`ShellGeom.lean:74`）就地兑现。

## 三条残项一样强（PROTOCOL §13）

`hwin`（窗口装得下）⟺ `hdepth`（支撑函数深度）⟺ `hdepthS`（深度只跑在固定的 `E ↑S` 上）：

* `hdepth ⟹ hwin`：`window_subset_of_depth`（经 `EnvTranslate.shift_subset_of_suppVal_le`）。
* `hwin ⟹ hdepth`：`depth_of_window`。
* `hdepthS ⟺ hdepth`：`E_collarY_eq`（守卫里的 `Enveloped` 把 `E (collarY …)` 与 `E ↑S` 拉平）。

换形既没加强也没减弱；收益是 `hdepthS` 的 `∀ n` 跑在与 `i`、`ε` 无关的固定法向组上。

## 硬规矩 6：数值实例

`S := Nivat.ApexUnique.Shex`（七点），`nJ = (0,1)`、`vJ = (1,0)`、`F.a' = (1,0)`；
塔取 `tmp/wip/lane-leafa-gen-fillcover-inter.lean` 的
`Â_i = hexShape (4i+6) (3i+6) 2 (2i+2) 0`，于是
`collarY i ε = hexShape (4i+6) (3i+6) 2 (2i+2) ε`，即 `0 ≤ x ≤ 4i+6`、`-ε ≤ y ≤ 3i+6`、
`-2 ≤ x - y ≤ 2i+2`。逐条算 `h_n := suppVal ↑S n - dot n a'` 与 `suppVal (collarY i ε) n`：

| `n` | `h_n` | `suppVal (collarY i ε) n` | `hdepth` 在 `z = (x,y)` 处读作 |
|---|---|---|---|
| `(0,-1)` = `-nJ` | `0` | `ε` | `-y ≤ ε`，**恒真**（`z ∈ collarY` 自带） |
| `(1,-1)` = `νJ1` | `0` | `2i+2` | `x - y ≤ 2i+2`，**恒真**（同上） |
| `(0,1)` | `2` | `3i+6` | `y ≤ 3i+4` |
| `(1,0)` | `1` | `4i+6` | `x ≤ 4i+5` |
| `(-1,0)` | `1` | `0` | `1 ≤ x` |
| `(-1,1)` | `2` | `2` | `y ≤ x` |

⭐ 两条为零的恰是 `a'` 自己所在的两个暴露面。这**不是台架特性**：
`depth_holds_of_mem_face` 是对一般 `Ahat`、一般 `S` 证的，只要 `a'` 落在那面上，深度要求就是 0；
而 `a'` 必落在 `-nJ` 面上是 `F.lex'` 的直接推论（`a'_mem_face_negNJ`，无台架）。
`Shex_free_walls` 是这两条的内核收据。剩下四条在
`lane-leafa-gen-fillcover-inter.lean:559` 的 `hstep_instance` 覆盖的分支（`y < 0 ∧ 1 ≤ x`）上
都成立，与那条独立路线给出同一个分界。

⛔ 本归约与 `(ε,i₀) = (1,0)` 无关：结论是 `∀ ε i₀`，守卫原样传给残项，
台架上那个 `(1,0)` 只是 `shellEnv_x` 恰好给出的见证，归约本身不消费它。

## 使用警告

* 本 namespace 里有 `collarY`（`Y` 这个名字在 `FillCoverWitness.lean:105` 已占，`declscan.py` 实测），
  短名多，**别 `open Nivat.FillCoverGuarded`**，按全名引用。
* 不 import `RegionSteps` / `ColleRegion` / `Case2WindowProbe` / `NfpLPreamble`
  （import 闭包 176 模块，四个禁止模块命中 0，本轮自算）。
* ⚠ **一名四物：`hwin`。**  本文件的残项 `hwin` 是 `fillCover_of_window` 的那个假设——
  量词骨架 `∀ ε i₀, … → ∀ i ≥ i₀, ∀ z ∈ collarY i ε, ∀ b ∈ S`，结论是**集合含于**
  （`z + (b - F.a') ∈ collarY i ε`），**没有 `∃`**，而且 `∀ b ∈ S` 上**没有任何限制**。
  与它同名、但**不是同一个东西**的有三处：
  (1) `bottom` 那条线上经 `BottomRoom.window_of_shell` 的 `hPsub` / `hC` 走的 `hwin`
      （lane-leafa-shell 的 `LeafAAssemble` 里，团队长已另派）；
  (2) lane-tower-hlev 在 `escapeW` 上的层见证 `hwit`，形状是 `∃ g ∈ Â_i, …`；
  (3) `Nivat.LaneTowerHlevHwin.hwin_guarded_iff`（主仓 `HwinGuard.lean`，第 208 轮落地，
      签名已核）证的是
      `(∀ b ∈ S, 0 < ⟪n_J, b-a⟫ → z₀ + (b-a) ∈ reachSet T v_{J+1}) ↔ (∀ b ∈ S, …)`，
      **管的是 (1) 那条线**：单基点 `z₀`、目标 `reachSet`、守卫是 `b` 上的 `0 < ⟪n_J, b-a⟫`。
      ⛔ **它不能搬到本文件的 `hwin` 上**，而且不是「搬过来会变弱」而是**无处可搬**：
      本文件的 `hwin` 根本没有 `0 < ⟪n_J, b - gen⟫` 这个守卫可删。本文件里叫「守卫」的是
      `Enveloped ↑S (collarY i ε)` 这条**前提**，与 `b` 的取值范围无关，是另一种东西
      （lane-tower-hlev 2026-09-24 按名字预期了一条相反结论，前提即不成立；
      两侧签名形状不同，不是强弱之争）。
  接口对接前先按量词骨架核一遍，别照名字接。
-/
import Nivat.External.Colle.FillCoverReduce
import Nivat.External.Colle.GenClosureWeaken
import Nivat.External.Colle.EnvTranslate
import Nivat.External.Colle.AhatMono
import Nivat.External.Colle.ShellGeom
import Nivat.External.Colle.ApexUnique

set_option autoImplicit false

namespace Nivat.FillCoverGuarded

open Nivat Nivat.LE2 Nivat.MaxEnv Nivat.Colle35

variable {S : Finset (ℤ × ℤ)} {gen nJ vJ vJ1 w : ℤ × ℤ} {cJ : ℤ} {Ahat : ℕ → Set (ℤ × ℤ)}

/-! ## §1. 第 `i` 层领 `collarY i ε`，及它的四条副条件 -/

/-- 第 `i` 层领，逐字符取自 `b3_colle2.txt:518` 的
`$\hat{A}_{i}^{(\epsilon)}:=\{g-t\vec{v}_{\ell_{J+1}}\in\hat{A}^{(\epsilon)}_{\infty}
:g\in\hat{A}_{i},\ t\in\mathbb{Z}_{+}\}$`：沿 `w := -v_{ℓ_{J+1}}` 把第 `i` 层扫出去，
再与已经造好的外壳 `Â_∞^{(ε)}` 取交。外层 `MaxEnv.shell` 在**并集**上、内层
`ShellMink.shellInter` 在第 `i` 层上，与 `ChainAssembleInter.lean:217-218` 同形。 -/
def collarY (Ahat : ℕ → Set (ℤ × ℤ)) (vJ1 nJ w : ℤ × ℤ) (cJ : ℤ) (i ε : ℕ) : Set (ℤ × ℤ) :=
  ShellMink.shellInter (Ahat i) (MaxEnv.shell (⋃ i, Ahat i) vJ1 nJ cJ ε) w

theorem collarY_eq (i ε : ℕ) :
    collarY Ahat vJ1 nJ w cJ i ε =
      ShellMink.shellInter (Ahat i) (MaxEnv.shell (⋃ i, Ahat i) vJ1 nJ cJ ε) w := rfl

/-- `collarY i ε ⊆ MaxEnv.shell (Â_i) w nJ cJ ε`：`reachSet` 那一半给 `∃ g ∈ Â_i, ∃ t`，
层高那一半从外层 `shell` 的最后一个合取分量里读出来。与
`FillCoverReduce.fillCover_of_local_step`（`FillCoverReduce.lean:264`）里的同名 `have` 同证。 -/
theorem collarY_subset_shell (i ε : ℕ) :
    collarY Ahat vJ1 nJ w cJ i ε ⊆ MaxEnv.shell (Ahat i) w nJ cJ ε := by
  rintro z ⟨⟨g, hg, t, rfl⟩, hsh⟩
  obtain ⟨-, -, -, -, hlev⟩ := hsh
  exact ⟨g, hg, t, rfl, hlev⟩

/-- **`collarY i ε ⊆` 外层壳**，即 `shellInter` 的右投影
（`ShellMink.shellInter_subset_right`）。⚠ 与上面 `collarY_subset_shell` **不是同一条**：
那条落到 `MaxEnv.shell (Â_i) w nJ cJ ε`（扫掠方向 `w`、底是第 `i` 层），
这条落到 `MaxEnv.shell (⋃ j, Â_j) vJ1 nJ cJ ε`（扫掠方向 `vJ1`、底是并集）。 -/
theorem collarY_subset_outer_shell (i ε : ℕ) :
    collarY Ahat vJ1 nJ w cJ i ε ⊆ MaxEnv.shell (⋃ j, Ahat j) vJ1 nJ cJ ε :=
  ShellMink.shellInter_subset_right _ _ _

/-- `collarY i ε` 有限：`MaxEnv.shell_finite` 加 `hsweepW : dot nJ w < 0`。 -/
theorem collarY_finite (hfin : ∀ i, (Ahat i).Finite) (hsweepW : dot nJ w < 0) (i ε : ℕ) :
    (collarY Ahat vJ1 nJ w cJ i ε).Finite :=
  (MaxEnv.shell_finite (hfin i) hsweepW).subset (collarY_subset_shell i ε)

/-- **`Â_i ⊆ collarY i ε`**：`t = 0` 给 `reachSet (Â_i) w`，`s = 0` 给 `Â_∞` 的 `vJ1`-扫出，
高度切由 `hhp` 加 `0 ≤ ε` 白送。⟹ binder 第一个析取支已经吃掉整个 `Â_i`，
`i = i₀` 时整条 binder 恒真，真正要处理的只有 `collarY i ε \ Â_i`。 -/
theorem Ahat_subset_collarY {i : ℕ} (hhp : ∀ z ∈ Ahat i, cJ ≤ dot nJ z) (ε : ℕ) :
    Ahat i ⊆ collarY Ahat vJ1 nJ w cJ i ε := by
  intro z hz
  refine ⟨⟨z, hz, 0, by simp⟩, ⟨z, Set.mem_iUnion.mpr ⟨i, hz⟩, 0, by simp, ?_⟩⟩
  have h := hhp z hz
  have hε : (0 : ℤ) ≤ (ε : ℤ) := Int.natCast_nonneg ε
  omega

/-- **`collarY i ε` 的墙就是 `S` 的墙**：`Enveloped` 的两条（`E T ⊆ E U` 与 `encard` 相等）
在 `(E ↑S).Finite` 下合成等号。这让深度条件的 `∀ n` 可以跑在与 `i`、`ε` 无关的 `E ↑S` 上。 -/
theorem E_collarY_eq {i ε : ℕ}
    (henv : Enveloped (↑S : Set (ℤ × ℤ)) (collarY Ahat vJ1 nJ w cJ i ε)) :
    E (collarY Ahat vJ1 nJ w cJ i ε) = E (↑S : Set (ℤ × ℤ)) :=
  Enveloped.E_eq (finite_E_of_finite S.finite_toSet) henv

/-! ## §2. 锚点 `F.a'` 在它自己所在的墙上不要深度

`:530` 的归纳锚在 `a'`，理由是 `exists_lex_covector`（`FillCoverReduce.lean:142`）的秩协向量
只因 `F.lex'`（`ANormal.lean:601`）把 `a'` 钉在 `(⟪nJ,·⟫, -⟪vJ,·⟫)` 的字典序极小处才存在。
同一件事在支撑函数一侧读作：凡 `a'` 自己落在其上的暴露面，所需深度恰为 0。 -/

/-- **凡是 `a'` 自己就落在其上的暴露面，深度要求为零。**  `suppVal ↑S n = dot n F.a'`，
于是不等式塌成 `dot n z ≤ suppVal (collarY i ε) n`，即 `le_suppVal`。 -/
theorem depth_holds_of_mem_face (hfin : ∀ i, (Ahat i).Finite) (hsweepW : dot nJ w < 0)
    (F : FaceBlock S nJ vJ) {n : ℤ × ℤ} (hn : F.a' ∈ face (↑S : Set (ℤ × ℤ)) n)
    {i ε : ℕ} {z : ℤ × ℤ} (hz : z ∈ collarY Ahat vJ1 nJ w cJ i ε) :
    suppVal (↑S : Set (ℤ × ℤ)) n + dot n (z - F.a') ≤
      suppVal (collarY Ahat vJ1 nJ w cJ i ε) n := by
  have hle : dot n z ≤ suppVal (collarY Ahat vJ1 nJ w cJ i ε) n :=
    le_suppVal (collarY_finite hfin hsweepW i ε) ⟨z, hz⟩ hz
  rw [suppVal_eq hn, dot_sub]
  omega

/-- `a'` 是 `S` 的 `nJ`-极小点（`F.lex'`），所以它落在外法向 `-nJ` 的暴露面上。 -/
theorem a'_mem_face_negNJ (F : FaceBlock S nJ vJ) :
    F.a' ∈ face (↑S : Set (ℤ × ℤ)) (-nJ) := by
  refine ⟨Finset.mem_coe.mpr F.a'_mem, fun y hy => ?_⟩
  rw [dot_neg_left, dot_neg_left, neg_le_neg_iff]
  by_cases hy' : y = F.a'
  · simp [hy']
  · rcases F.lex' y (Finset.mem_erase.mpr ⟨hy', Finset.mem_coe.mp hy⟩) with hlt | ⟨heq, -⟩
    · rw [dot_neg_left, dot_neg_left] at hlt
      omega
    · rw [dot_neg_left, dot_neg_left] at heq
      omega

/-- **底面墙上所需深度为零**：`suppVal ↑S (-nJ) - dot (-nJ) F.a' = 0`。 -/
theorem depth_at_negNJ (F : FaceBlock S nJ vJ) :
    suppVal (↑S : Set (ℤ × ℤ)) (-nJ) = dot (-nJ) F.a' :=
  suppVal_eq (a'_mem_face_negNJ F)

/-- 深度条件在 `n = -nJ` 上是白送的：只要 `z ∈ collarY i ε`，不等式自动成立。 -/
theorem depth_holds_at_negNJ (hfin : ∀ i, (Ahat i).Finite) (hsweepW : dot nJ w < 0)
    (F : FaceBlock S nJ vJ) {i ε : ℕ} {z : ℤ × ℤ}
    (hz : z ∈ collarY Ahat vJ1 nJ w cJ i ε) :
    suppVal (↑S : Set (ℤ × ℤ)) (-nJ) + dot (-nJ) (z - F.a') ≤
      suppVal (collarY Ahat vJ1 nJ w cJ i ε) (-nJ) :=
  depth_holds_of_mem_face hfin hsweepW F (a'_mem_face_negNJ F) hz

/-! ## §3. 归约本体 -/

/-- **深度条件 ⟹ 局部步**：把 `S` 的 `a'` 锚在 `z` 上，整块窗口留在 `collarY i ε` 里。
`EnvTranslate.shift_subset_of_suppVal_le`（`EnvTranslate.lean:78`）的四条副条件
（`Finite` / `Nonempty` / `PosArea` / `IsLatticeConvexRegion`）在此就地兑现：
前一条来自 `hfin` + `hsweepW`，`Nonempty` 由手上这个 `z` 白送，后两条来自守卫里的
`Enveloped` 加 `hSarea`（`AhatMono.posArea_of_enveloped`，`AhatMono.lean:3029`）。 -/
theorem window_subset_of_depth
    (hfin : ∀ i, (Ahat i).Finite) (hsweepW : dot nJ w < 0)
    (F : FaceBlock S nJ vJ) (hSarea : PosArea (↑S : Set (ℤ × ℤ)))
    {i ε : ℕ} (henv : Enveloped (↑S : Set (ℤ × ℤ)) (collarY Ahat vJ1 nJ w cJ i ε))
    {z : ℤ × ℤ} (hz : z ∈ collarY Ahat vJ1 nJ w cJ i ε)
    (hdep : ∀ n ∈ E (collarY Ahat vJ1 nJ w cJ i ε),
      suppVal (↑S : Set (ℤ × ℤ)) n + dot n (z - F.a') ≤
        suppVal (collarY Ahat vJ1 nJ w cJ i ε) n) :
    ∀ b ∈ S, z + (b - F.a') ∈ collarY Ahat vJ1 nJ w cJ i ε := by
  have hsub : shift (z - F.a') (↑S : Set (ℤ × ℤ)) ⊆ collarY Ahat vJ1 nJ w cJ i ε :=
    shift_subset_of_suppVal_le (collarY_finite hfin hsweepW i ε) ⟨z, hz⟩
      (Nivat.AhatMono.posArea_of_enveloped S.finite_toSet hSarea henv)
      henv.1.1 S.finite_toSet ⟨F.a', Finset.mem_coe.mpr F.a'_mem⟩ hdep
  intro b hb
  have hmem : b + (z - F.a') ∈ shift (z - F.a') (↑S : Set (ℤ × ℤ)) := by
    show b + (z - F.a') - (z - F.a') ∈ (↑S : Set (ℤ × ℤ))
    simpa using Finset.mem_coe.mpr hb
  have heq : b + (z - F.a') = z + (b - F.a') := by abel
  exact hsub (heq ▸ hmem)

/-- **带守卫的 `fillCover`，归约到「窗口装得下」。**  结论逐字符是
`ChainAssembleInter.lean:213-221`（＝`ofPartsExhaustsInter` 的同名 binder，`ChainExhaustInter.lean`）的 `fillCover` 字段，
`Env` 取 `EnvOf ↑S`（调用点 `LeafAAssemble.lean:1160` 是 `(hEnv := rfl)`），
守卫从 `max i₀ I₀ ≤ i` 放宽到 `i₀ ≤ i`（更强，且免费——归约不用 `I₀`）。

残项 `hwin` 只说「除种子外，每个 `z` 处把 `S` 的 `a'` 锚在 `z` 上，整块窗口仍落在
`collarY i ε` 里」，不提 `suppVal`；它拿得到 `0 < ε` 与整条 `Enveloped` 守卫。

证法：`hwin` 的第二支就是 `FillCoverReduce.subset_genClosure_of_covector`
（`FillCoverReduce.lean:113`）要的局部步，秩协向量由 `exists_lex_covector F`
（`FillCoverReduce.lean:142`）给；最后 `GenClosureWeaken.genClosure_subset_genClosure`
（`GenClosureWeaken.lean:70`）把单生成元的 `genFill` 塔翻成字段要的
`Colle37.GenClosure`，其 `hconv` 是
`Colle37Geom.latticeConvex_erase_of_lexExtreme F.latticeConvex_S F.lex'`
（`ShellGeom.lean:74`）。 -/
theorem fillCover_of_window
    (hfin : ∀ i, (Ahat i).Finite) (hsweepW : dot nJ w < 0)
    (F : FaceBlock S nJ vJ) (gen_eq : gen = F.a')
    (hwin : ∀ ε i₀ : ℕ, 0 < ε →
      (∀ i, i₀ ≤ i → Enveloped (↑S : Set (ℤ × ℤ))
        (ShellMink.shellInter (Ahat i) (MaxEnv.shell (⋃ i, Ahat i) vJ1 nJ cJ ε) w)) →
      ∀ i, i₀ ≤ i →
      ∀ z ∈ ShellMink.shellInter (Ahat i) (MaxEnv.shell (⋃ i, Ahat i) vJ1 nJ cJ ε) w,
        z ∈ Ahat i ∪ ShellMink.shellInter (Ahat i₀)
              (MaxEnv.shell (⋃ i, Ahat i) vJ1 nJ cJ ε) w ∨
        ∀ b ∈ S, z + (b - gen) ∈
          ShellMink.shellInter (Ahat i) (MaxEnv.shell (⋃ i, Ahat i) vJ1 nJ cJ ε) w) :
    ∀ ε i₀ : ℕ, 0 < ε →
      (∀ i, i₀ ≤ i → EnvOf (↑S : Set (ℤ × ℤ))
        (ShellMink.shellInter (Ahat i) (MaxEnv.shell (⋃ i, Ahat i) vJ1 nJ cJ ε) w)) →
      ∀ i, i₀ ≤ i →
      ShellMink.shellInter (Ahat i) (MaxEnv.shell (⋃ i, Ahat i) vJ1 nJ cJ ε) w ⊆
        {z | Colle37.GenClosure S (Ahat i ∪
          ShellMink.shellInter (Ahat i₀)
            (MaxEnv.shell (⋃ i, Ahat i) vJ1 nJ cJ ε) w) z} := by
  classical
  subst gen_eq
  intro ε i₀ hε hEnv i hi
  have hYfin : (collarY Ahat vJ1 nJ w cJ i ε).Finite := collarY_finite hfin hsweepW i ε
  obtain ⟨n', hn'⟩ := Nivat.LaneFillCover.exists_lex_covector F
  obtain ⟨C, hC⟩ : ∃ C : ℤ, ∀ z ∈ collarY Ahat vJ1 nJ w cJ i ε, dot n' z ≤ C := by
    obtain ⟨C, hC⟩ := (hYfin.image (fun z => dot n' z)).bddAbove
    exact ⟨C, fun z hz => hC ⟨z, hz, rfl⟩⟩
  have hstep : ∀ z ∈ collarY Ahat vJ1 nJ w cJ i ε,
      z ∈ (Ahat i ∪ collarY Ahat vJ1 nJ w cJ i₀ ε) ∨
      ∀ b ∈ S.erase F.a', z + (b - F.a') ∈
        (Ahat i ∪ collarY Ahat vJ1 nJ w cJ i₀ ε) ∪ collarY Ahat vJ1 nJ w cJ i ε := by
    intro z hz
    rcases hwin ε i₀ hε (fun j hj => hEnv j hj) i hi z hz with hx | hw
    · exact Or.inl hx
    · exact Or.inr fun b hb => Set.mem_union_right _ (hw b (Finset.mem_of_mem_erase hb))
  intro z hz
  exact Nivat.GenClosureWeaken.genClosure_subset_genClosure F.a'_mem
    (Nivat.Colle37Geom.latticeConvex_erase_of_lexExtreme F.latticeConvex_S F.lex') z
    (Nivat.LaneFillCover.subset_genClosure_of_covector hC hn' hstep hz)

/-- **带守卫的 `fillCover`，归约到深度条件。**  `fillCover_of_window` 的推论，
第二支经 `window_subset_of_depth` 兑现；比 `fillCover_of_window` 多要 `hSarea`。 -/
theorem fillCover_of_depth
    (hfin : ∀ i, (Ahat i).Finite) (hsweepW : dot nJ w < 0)
    (F : FaceBlock S nJ vJ) (gen_eq : gen = F.a')
    (hSarea : PosArea (↑S : Set (ℤ × ℤ)))
    (hdepth : ∀ ε i₀ : ℕ, 0 < ε →
      (∀ i, i₀ ≤ i → Enveloped (↑S : Set (ℤ × ℤ))
        (ShellMink.shellInter (Ahat i) (MaxEnv.shell (⋃ i, Ahat i) vJ1 nJ cJ ε) w)) →
      ∀ i, i₀ ≤ i →
      ∀ z ∈ ShellMink.shellInter (Ahat i) (MaxEnv.shell (⋃ i, Ahat i) vJ1 nJ cJ ε) w,
        z ∈ Ahat i ∪ ShellMink.shellInter (Ahat i₀)
              (MaxEnv.shell (⋃ i, Ahat i) vJ1 nJ cJ ε) w ∨
        ∀ n ∈ E (ShellMink.shellInter (Ahat i)
              (MaxEnv.shell (⋃ i, Ahat i) vJ1 nJ cJ ε) w),
          suppVal (↑S : Set (ℤ × ℤ)) n + dot n (z - gen) ≤
            suppVal (ShellMink.shellInter (Ahat i)
              (MaxEnv.shell (⋃ i, Ahat i) vJ1 nJ cJ ε) w) n) :
    ∀ ε i₀ : ℕ, 0 < ε →
      (∀ i, i₀ ≤ i → EnvOf (↑S : Set (ℤ × ℤ))
        (ShellMink.shellInter (Ahat i) (MaxEnv.shell (⋃ i, Ahat i) vJ1 nJ cJ ε) w)) →
      ∀ i, i₀ ≤ i →
      ShellMink.shellInter (Ahat i) (MaxEnv.shell (⋃ i, Ahat i) vJ1 nJ cJ ε) w ⊆
        {z | Colle37.GenClosure S (Ahat i ∪
          ShellMink.shellInter (Ahat i₀)
            (MaxEnv.shell (⋃ i, Ahat i) vJ1 nJ cJ ε) w) z} := by
  subst gen_eq
  refine fillCover_of_window hfin hsweepW F rfl ?_
  intro ε i₀ hε hEnv i hi z hz
  rcases hdepth ε i₀ hε hEnv i hi z hz with hx | hdep
  · exact Or.inl hx
  · exact Or.inr (window_subset_of_depth hfin hsweepW F hSarea (hEnv i hi) hz hdep)

/-- **带守卫的 `fillCover`，深度条件写在固定的 `E ↑S` 上。**  与 `fillCover_of_depth`
同一结论；`E_collarY_eq` 把 `∀ n ∈ E (collarY i ε)` 换成 `∀ n ∈ E ↑S`——后者与 `i`、`ε`
无关，在调用点就是 `d.Sphi` 的那一组固定法向，可以逐条枚举。 -/
theorem fillCover_of_depthS
    (hfin : ∀ i, (Ahat i).Finite) (hsweepW : dot nJ w < 0)
    (F : FaceBlock S nJ vJ) (gen_eq : gen = F.a')
    (hSarea : PosArea (↑S : Set (ℤ × ℤ)))
    (hdepthS : ∀ ε i₀ : ℕ, 0 < ε →
      (∀ i, i₀ ≤ i → Enveloped (↑S : Set (ℤ × ℤ))
        (ShellMink.shellInter (Ahat i) (MaxEnv.shell (⋃ i, Ahat i) vJ1 nJ cJ ε) w)) →
      ∀ i, i₀ ≤ i →
      ∀ z ∈ ShellMink.shellInter (Ahat i) (MaxEnv.shell (⋃ i, Ahat i) vJ1 nJ cJ ε) w,
        z ∈ Ahat i ∪ ShellMink.shellInter (Ahat i₀)
              (MaxEnv.shell (⋃ i, Ahat i) vJ1 nJ cJ ε) w ∨
        ∀ n ∈ E (↑S : Set (ℤ × ℤ)),
          suppVal (↑S : Set (ℤ × ℤ)) n + dot n (z - gen) ≤
            suppVal (ShellMink.shellInter (Ahat i)
              (MaxEnv.shell (⋃ i, Ahat i) vJ1 nJ cJ ε) w) n) :
    ∀ ε i₀ : ℕ, 0 < ε →
      (∀ i, i₀ ≤ i → EnvOf (↑S : Set (ℤ × ℤ))
        (ShellMink.shellInter (Ahat i) (MaxEnv.shell (⋃ i, Ahat i) vJ1 nJ cJ ε) w)) →
      ∀ i, i₀ ≤ i →
      ShellMink.shellInter (Ahat i) (MaxEnv.shell (⋃ i, Ahat i) vJ1 nJ cJ ε) w ⊆
        {z | Colle37.GenClosure S (Ahat i ∪
          ShellMink.shellInter (Ahat i₀)
            (MaxEnv.shell (⋃ i, Ahat i) vJ1 nJ cJ ε) w) z} := by
  refine fillCover_of_depth hfin hsweepW F gen_eq hSarea ?_
  intro ε i₀ hε hEnv i hi z hz
  rcases hdepthS ε i₀ hε hEnv i hi z hz with hx | hdep
  · exact Or.inl hx
  · refine Or.inr fun n hn => hdep n ?_
    rwa [← E_collarY_eq (Ahat := Ahat) (vJ1 := vJ1) (nJ := nJ) (w := w) (cJ := cJ)
      (hEnv i hi)]

/-- **窗口条件 ⟹ 深度条件**，对任意法向 `n`（不必是边）。取 `S` 在 `n` 上的极大点 `b`，
`z + (b - a')` 已在 `collarY i ε` 里，`le_suppVal` 即得。与 `window_subset_of_depth` 合起来
说明 `hwin` 与 `hdepth` **一样强**（PROTOCOL §13：换形没有偷偷加强或减弱）。 -/
theorem depth_of_window (hfin : ∀ i, (Ahat i).Finite) (hsweepW : dot nJ w < 0)
    (F : FaceBlock S nJ vJ) {i ε : ℕ} {z : ℤ × ℤ}
    (hwin : ∀ b ∈ S, z + (b - F.a') ∈ collarY Ahat vJ1 nJ w cJ i ε) (n : ℤ × ℤ) :
    suppVal (↑S : Set (ℤ × ℤ)) n + dot n (z - F.a') ≤
      suppVal (collarY Ahat vJ1 nJ w cJ i ε) n := by
  obtain ⟨b, hb, hbeq⟩ :=
    exists_suppVal_eq S.finite_toSet ⟨F.a', Finset.mem_coe.mpr F.a'_mem⟩ n
  have hmem := hwin b (Finset.mem_coe.mp hb)
  have hle := le_suppVal (n := n) (collarY_finite hfin hsweepW i ε) ⟨_, hmem⟩ hmem
  rw [dot_add, dot_sub] at hle
  rw [← hbeq, dot_sub]
  omega

/-! ## §4. 数值实例的内核收据（硬规矩 6）

模块 docstring 的六墙表里，深度为零的两条是 `a'` 自己所在的两个暴露面。下面这条把
「`a' = (1,0)` 同时落在 `Shex` 的 `-nJ = (0,-1)` 面和 `νJ1 = (1,-1)` 面上」钉成内核事实，
于是 `depth_holds_of_mem_face` 在这两条墙上**非空真**。 -/

/-- 内核收据：`a' = (1,0)` 同时落在 `Shex` 的 `(0,-1)` 面与 `(1,-1)` 面上。 -/
theorem Shex_free_walls :
    ((1 : ℤ), (0 : ℤ)) ∈ face (↑Nivat.ApexUnique.Shex : Set (ℤ × ℤ)) ((0 : ℤ), (-1 : ℤ)) ∧
    ((1 : ℤ), (0 : ℤ)) ∈ face (↑Nivat.ApexUnique.Shex : Set (ℤ × ℤ)) ((1 : ℤ), (-1 : ℤ)) := by
  constructor <;>
    exact ⟨Finset.mem_coe.mpr (by decide), fun y hy => by
      rw [Finset.mem_coe] at hy; revert y; decide⟩

/-! ## §7. 守卫对齐：`fillCover_of_window` 逐字符兑现迁移后的字段

`ChainDataGeomParts.fillCover`（`ChainPartsFeed.lean:271-279`，2026-09-25 迁到 (B) 栈后）
的守卫是 **`max i₀ I₀ ≤ i`**，而 `fillCover_of_window`（`:271`）交的是 `i₀ ≤ i`。
后者**更强**（覆盖更多的 `i`），所以前者是它的直接推论 —— 但「更强所以够用」这句话
在守卫上极容易记反（`max` 到底抬高还是放松了门槛），所以这里让内核记一次，
不靠肉眼。`I₀` 在结论里除了抬守卫之外不出现，与它在结构体里是**字段**（生产者自选）
的读法一致（`ChainPartsFeed.lean:240-245`）。 -/
theorem fillCover_field_of_window
    (hfin : ∀ i, (Ahat i).Finite) (hsweepW : dot nJ w < 0)
    (F : FaceBlock S nJ vJ) (gen_eq : gen = F.a')
    (hwin : ∀ ε i₀ : ℕ, 0 < ε →
      (∀ i, i₀ ≤ i → Enveloped (↑S : Set (ℤ × ℤ))
        (ShellMink.shellInter (Ahat i) (MaxEnv.shell (⋃ i, Ahat i) vJ1 nJ cJ ε) w)) →
      ∀ i, i₀ ≤ i →
      ∀ z ∈ ShellMink.shellInter (Ahat i) (MaxEnv.shell (⋃ i, Ahat i) vJ1 nJ cJ ε) w,
        z ∈ Ahat i ∪ ShellMink.shellInter (Ahat i₀)
              (MaxEnv.shell (⋃ i, Ahat i) vJ1 nJ cJ ε) w ∨
        ∀ b ∈ S, z + (b - gen) ∈
          ShellMink.shellInter (Ahat i) (MaxEnv.shell (⋃ i, Ahat i) vJ1 nJ cJ ε) w)
    (I₀ : ℕ) :
    ∀ ε i₀ : ℕ, 0 < ε →
      (∀ i, i₀ ≤ i → EnvOf (↑S : Set (ℤ × ℤ))
        (ShellMink.shellInter (Ahat i) (MaxEnv.shell (⋃ i, Ahat i) vJ1 nJ cJ ε) w)) →
      ∀ i, max i₀ I₀ ≤ i →
      ShellMink.shellInter (Ahat i) (MaxEnv.shell (⋃ i, Ahat i) vJ1 nJ cJ ε) w ⊆
        {z | Colle37.GenClosure S (Ahat i ∪
          ShellMink.shellInter (Ahat i₀)
            (MaxEnv.shell (⋃ i, Ahat i) vJ1 nJ cJ ε) w) z} :=
  fun ε i₀ hε hEnv i hi =>
    fillCover_of_window hfin hsweepW F gen_eq hwin ε i₀ hε hEnv i
      (le_trans (le_max_left i₀ I₀) hi)

/-- **哨兵：守卫方向不可反。**  把 `max i₀ I₀ ≤ i` 换成结论侧的守卫、`i₀ ≤ i` 换成假设侧，
所陈述的一般形为假 —— 即「`i₀ ≤ i` ⟹ `max i₀ I₀ ≤ i`」不成立。若哪天有人把
`fillCover_of_window` 和字段的守卫写反，这条会先炸。 -/
theorem not_le_max_of_le_left :
    ¬ (∀ i₀ I₀ i : ℕ, i₀ ≤ i → max i₀ I₀ ≤ i) := by
  intro h
  have := h 0 1 0 (le_refl 0)
  simp at this

/-! ## §8. `I₀` 的量词位置：`∃∀` 是真加强，但它**不是欠账**（撞车订正）

lane-leafa-gen，2026-09-25。原文 `b3_colle2.txt:520` 的顺序是

> So let `ε ∈ ℕ` and `i₀ ∈ ℕ` be such that `Â_{i₀}^{(ε)}` is an `E(𝒮_φ)`-enveloped set
> **and consider a constant `I₀ ∈ ℕ` such that** `ϑ|_{Â_{i₀}^{(ε)}} = ϑ_i|_{Â_{i₀}^{(ε)}}
> `∀ i ≥ I₀`.

即 `ε` 与 `i₀` **先**选，`I₀` **后**选 —— 原文的形状是 `∀ ε i₀, ∃ I₀`。
链上的写法是 `I₀ : ℕ` 作 `ChainDataGeomParts` 的**字段**（`ChainPartsFeed.lean:245`），
而 `ε`、`i₀` 在 `fillCover` / `escapeW` / `shellSubStrip` 三条字段**内部**被 `∀` 掉，
于是实际断言 `∃ I₀, ∀ ε i₀`。这两个形状**不等价**，`∃∀` 严格强：
`forall_exists_I₀_of_exists_forall` 给免费的那个方向，
`not_exists_forall_of_forall_exists` 给反方向的内核反例（PROTOCOL §13）。

⛔ **但本节最初写成「这一档是我们加的量词，是债」，那是错的，当场订正（PROTOCOL §48/§49
撞车读数作废，§82 两本账冲突则两本都不算）。** 按 §114 换拼法广搜（`∃ I₀` 而不是名字）
才查到已有的两处前案，**都早于本节且都说这条残差已关闭**：

* `EscapeW.lean` §5（lane-tower-hlev，2026-09-25）：「`I₀` 现在是 `ChainDataGeomParts` 的**字段**
  ……与本文件 `exists_I₀_escapeW` 交的 `∃ I₀` **同形** ⟹ 量词位置那条残差已关闭」，并给出
  比本节更好的理由 —— 三条尾部都是 `∀ i, max i₀ I₀ ≤ i → P i`，`I₀` 只在前件里且是 `max`
  的一支，所以命题对 `I₀` **反单调**，接线取 `I₀ := max I₀e I₀f` 即可，不需要改签名。
* `ChainExhaustInter.lean:65`（同）：同一结论；`:68` 记着接线处
  `shellSubStrip` / `fillCover` 已改收 `∃ I₀` 形、体内取三个阈值的 `max`。
* 而且强形**已被兑现**，不只是被辩护：`LaneTowerHlevEscPos.exists_escape_abstract`
  （`EscapeW.lean:262`，0 sorry，公理白）的结论逐字就是
  `∃ I₀, ∀ ε i₀, 0 < ε → ∀ i, max i₀ I₀ ≤ i → …`。它的 `I₀` 来自一个与 `ε` 无关的
  Cramer 界，所以对 `ε` 一致是白送的。

⟹ 现行签名不动，硬规矩 5 在这一格上**没有欠账**。

## 反单调性覆盖不到的那一格（这是本节真正剩下的东西）

`EscapeW.lean` §5 的反单调性解决的是**跨三条字段**合并阈值（`max I₀e I₀f`）。它**不给**
同一条字段**内部**对 `ε` 的一致性：若某条字段的逐 `(ε,i₀)` 阈值 `I₀(ε,i₀)` 随 `ε` 无界，
再大的单个 `I₀` 也不够（反单调只说大 `I₀` 更容易，不说存在）。
`escapeW` 白拿到 `ε`-一致是因为它的阈值与 `ε` 无关；**`fillCover` 这一侧还没有人量过**。

下面 `exists_I₀_of_per_normal` 就是把这个问题钉到最小形：`hdepthS` 的 `∀ n` 跑在与 `i`、`ε`
无关的固定有限法向组 `E ↑S` 上，逐法向阈值的一致化是 `Finset.sup`（与
`LeafAGenAttain.exists_uniform_attain_of_finset` 同一形状，但不需要单调性前提）。
⚠ 它只做**跨法向**的一致化；逐法向阈值本身是否与 `ε` 无关，是留下来的那一问，本节不主张。 -/

/-- `∃ I₀, ∀ ε i₀` ⟹ `∀ ε i₀, ∃ I₀`：这个方向免费，所以现行的强形对下游**够用**。
反方向见 `not_exists_forall_of_forall_exists`。 -/
theorem forall_exists_I₀_of_exists_forall {P : ℕ → ℕ → ℕ → Prop}
    (h : ∃ I₀ : ℕ, ∀ ε i₀ i : ℕ, max i₀ I₀ ≤ i → P ε i₀ i) :
    ∀ ε i₀ : ℕ, ∃ I₀ : ℕ, ∀ i, max i₀ I₀ ≤ i → P ε i₀ i := by
  obtain ⟨I₀, hI₀⟩ := h
  exact fun ε i₀ => ⟨I₀, fun i hi => hI₀ ε i₀ i hi⟩

/-- **哨兵：反方向为假**，所以 `∃∀` 不是换形而是加强（PROTOCOL §13）——
这条是「`escapeW` 交出 `∃ I₀` 形是一件有内容的事」的度量，不是欠账的记录（见 §8 正文）。
反例 `P ε i₀ i := ε ≤ i`：每对 `(ε, i₀)` 取 `I₀ := ε` 即可，但没有对一切 `ε` 通用的 `I₀`
（取 `ε := I₀ + 1`、`i₀ := 0`、`i := I₀`）。⚠ 反单调性（`EscapeW.lean` §5）救不了这条：
它说的是 `I₀` 变大更容易，不说存在一个够用的 `I₀`。 -/
theorem not_exists_forall_of_forall_exists :
    ¬ (∀ P : ℕ → ℕ → ℕ → Prop,
        (∀ ε i₀ : ℕ, ∃ I₀ : ℕ, ∀ i, max i₀ I₀ ≤ i → P ε i₀ i) →
        ∃ I₀ : ℕ, ∀ ε i₀ i : ℕ, max i₀ I₀ ≤ i → P ε i₀ i) := by
  intro h
  obtain ⟨I₀, hI₀⟩ := h (fun ε _ i => ε ≤ i) (fun ε i₀ => ⟨ε, fun i hi => le_trans (le_max_right i₀ ε) hi⟩)
  have := hI₀ (I₀ + 1) 0 I₀ (by omega)
  omega

/-- **`I₀` 的正面用途：吸收「逐法向阈值」的 `Finset.sup`。**  深度条件
（`fillCover_of_depthS` 的 `hdepthS`）的 `∀ n` 跑在与 `i`、`ε` 无关的固定有限法向组
`E ↑S` 上；逐法向各有一个阈值时，一致阈值就是它们的 `Finset.sup`，这正是
`max i₀ I₀ ≤ i` 那个 `I₀` 该装的东西。

与 `LeafAGenAttain.exists_uniform_attain_of_finset` 同一形状（有限法向集上一致性塌成
`Finset.sup`），但**不需要单调性前提**：阈值形 `∀ i, I ≤ i → P i n` 自带向上封闭。 -/
theorem exists_I₀_of_per_normal {N : Set (ℤ × ℤ)} (hN : N.Finite) {P : ℕ → ℤ × ℤ → Prop}
    (hper : ∀ n ∈ N, ∃ I : ℕ, ∀ i, I ≤ i → P i n) :
    ∃ I₀ : ℕ, ∀ i, I₀ ≤ i → ∀ n ∈ N, P i n := by
  classical
  choose! f hf using hper
  refine ⟨hN.toFinset.sup f, fun i hi n hn => hf n hn i ?_⟩
  exact le_trans (Finset.le_sup (hN.mem_toFinset.mpr hn)) hi

/-- **哨兵：`N` 无限时 `Finset.sup` 那一步没有替代品。**  取 `N := Set.univ`、
`P i n := n.1 ≤ (i : ℤ)`：逐法向阈值存在（`I := n.1.toNat`），一致阈值不存在。 -/
theorem not_exists_I₀_of_per_normal_infinite :
    ¬ (∀ (N : Set (ℤ × ℤ)) (P : ℕ → ℤ × ℤ → Prop),
        (∀ n ∈ N, ∃ I : ℕ, ∀ i, I ≤ i → P i n) →
        ∃ I₀ : ℕ, ∀ i, I₀ ≤ i → ∀ n ∈ N, P i n) := by
  intro h
  obtain ⟨I₀, hI₀⟩ := h Set.univ (fun i n => n.1 ≤ (i : ℤ))
    (fun n _ => ⟨n.1.toNat, fun i hi => by omega⟩)
  have := hI₀ I₀ (le_refl I₀) ((I₀ : ℤ) + 1, 0) (Set.mem_univ _)
  omega

/-! ## §9. 把 `I₀` 交还给残项（lane-leafa-gen，2026-09-25）

⚠ **§7 的记账漏了一半。** `fillCover_field_of_window`（`:424`）把**结论**的守卫抬到
`max i₀ I₀ ≤ i`，但它的**残项 `hwin` 仍然带 `i₀ ≤ i`**。也就是说：字段允许生产者自选 `I₀`、
只在 `i ≥ max i₀ I₀` 处兑现，而谁去证 `hwin` 却**拿不到 `I₀`**，必须对一切 `i ≥ i₀` 证。
§7 那句「放宽是免费的」对归约方向成立，对**残项方向不成立** —— 残项被悄悄加强了一档
（PROTOCOL §13：换形不得偷偷加强或减弱；这里加强的是我自己上轮写的残项，自报）。

本节把 `I₀` 交还给残项。`fillCover_pointwise_of_window` 是归约的**逐点**核心，
它把 `hwin` 只在**给定的那一个 `i`** 上用一次，于是守卫想放哪一档都行；
`fillCover_field_of_window_at_I₀` 是带 `I₀` 的那一档，逐字符仍是字段的类型。

⭐ **顺带测出的事实：归约**根本不用**`0 < ε` 和 `Enveloped` 守卫。** 二者在
`fillCover_of_window` 的证明体里唯一的去处是喂给 `hwin`（`:311`），逐点核心里连出现的位置
都没有。⟹ 这两条是**纯透传**，归约对它们是鲁棒的；反过来说，想靠加强守卫来救残项，
救的只能是 `hwin` 自己，救不了归约。

⛔ **但把 `I₀` 交还**不能**救 `hwin`** —— 见 `LeafAGenHwinI0.lean` 的
`not_HwinI₀_oct8`：oct8 台架上的障碍对 `i` 是**一致**的（见证点随 `KK i = i+2` 平移），
所以对**任何** `I₀` 都能取到 `i ≥ max i₀ I₀` 使 `hwin` 为假。本节因此是一条
**否定性的收据**：它排掉了「残项被我写强了，放松守卫就能证」这个假想出口。 -/

/-- **归约的逐点核心。**  `hwinAt` 只在给定的这一个 `i` 上陈述，所以本条对守卫**不表态**；
`fillCover_of_window`（`:271`）与 `fillCover_field_of_window_at_I₀` 都是它在不同守卫上的实例。
⭐ 注意签名里**没有** `0 < ε`、**没有** `Enveloped` 守卫：归约不消费它们。 -/
theorem fillCover_pointwise_of_window
    (hfin : ∀ i, (Ahat i).Finite) (hsweepW : dot nJ w < 0)
    (F : FaceBlock S nJ vJ) (gen_eq : gen = F.a') {i i₀ ε : ℕ}
    (hwinAt : ∀ z ∈ ShellMink.shellInter (Ahat i)
        (MaxEnv.shell (⋃ i, Ahat i) vJ1 nJ cJ ε) w,
      z ∈ Ahat i ∪ ShellMink.shellInter (Ahat i₀)
            (MaxEnv.shell (⋃ i, Ahat i) vJ1 nJ cJ ε) w ∨
      ∀ b ∈ S, z + (b - gen) ∈
        ShellMink.shellInter (Ahat i) (MaxEnv.shell (⋃ i, Ahat i) vJ1 nJ cJ ε) w) :
    ShellMink.shellInter (Ahat i) (MaxEnv.shell (⋃ i, Ahat i) vJ1 nJ cJ ε) w ⊆
      {z | Colle37.GenClosure S (Ahat i ∪
        ShellMink.shellInter (Ahat i₀)
          (MaxEnv.shell (⋃ i, Ahat i) vJ1 nJ cJ ε) w) z} := by
  classical
  subst gen_eq
  have hYfin : (collarY Ahat vJ1 nJ w cJ i ε).Finite := collarY_finite hfin hsweepW i ε
  obtain ⟨n', hn'⟩ := Nivat.LaneFillCover.exists_lex_covector F
  obtain ⟨C, hC⟩ : ∃ C : ℤ, ∀ z ∈ collarY Ahat vJ1 nJ w cJ i ε, dot n' z ≤ C := by
    obtain ⟨C, hC⟩ := (hYfin.image (fun z => dot n' z)).bddAbove
    exact ⟨C, fun z hz => hC ⟨z, hz, rfl⟩⟩
  have hstep : ∀ z ∈ collarY Ahat vJ1 nJ w cJ i ε,
      z ∈ (Ahat i ∪ collarY Ahat vJ1 nJ w cJ i₀ ε) ∨
      ∀ b ∈ S.erase F.a', z + (b - F.a') ∈
        (Ahat i ∪ collarY Ahat vJ1 nJ w cJ i₀ ε) ∪ collarY Ahat vJ1 nJ w cJ i ε := by
    intro z hz
    rcases hwinAt z hz with hx | hw
    · exact Or.inl hx
    · exact Or.inr fun b hb => Set.mem_union_right _ (hw b (Finset.mem_of_mem_erase hb))
  intro z hz
  exact Nivat.GenClosureWeaken.genClosure_subset_genClosure F.a'_mem
    (Nivat.Colle37Geom.latticeConvex_erase_of_lexExtreme F.latticeConvex_S F.lex') z
    (Nivat.LaneFillCover.subset_genClosure_of_covector hC hn' hstep hz)

/-- **带 `I₀` 的那一档：残项也只需在 `i ≥ max i₀ I₀` 处成立。**  结论逐字符仍是
`ChainDataGeomParts.fillCover`（`ChainPartsFeed.lean:271-279`）的类型。
与 `fillCover_field_of_window`（`:424`）的差别**只在残项**：那条要 `i₀ ≤ i`，本条要
`max i₀ I₀ ≤ i`，后者严格弱（`guard_weaken_max` 给免费方向，`not_le_max_of_le_left`
说反方向不成立）。 -/
theorem fillCover_field_of_window_at_I₀
    (hfin : ∀ i, (Ahat i).Finite) (hsweepW : dot nJ w < 0)
    (F : FaceBlock S nJ vJ) (gen_eq : gen = F.a') (I₀ : ℕ)
    (hwin : ∀ ε i₀ : ℕ, 0 < ε →
      (∀ i, i₀ ≤ i → Enveloped (↑S : Set (ℤ × ℤ))
        (ShellMink.shellInter (Ahat i) (MaxEnv.shell (⋃ i, Ahat i) vJ1 nJ cJ ε) w)) →
      ∀ i, max i₀ I₀ ≤ i →
      ∀ z ∈ ShellMink.shellInter (Ahat i) (MaxEnv.shell (⋃ i, Ahat i) vJ1 nJ cJ ε) w,
        z ∈ Ahat i ∪ ShellMink.shellInter (Ahat i₀)
              (MaxEnv.shell (⋃ i, Ahat i) vJ1 nJ cJ ε) w ∨
        ∀ b ∈ S, z + (b - gen) ∈
          ShellMink.shellInter (Ahat i) (MaxEnv.shell (⋃ i, Ahat i) vJ1 nJ cJ ε) w) :
    ∀ ε i₀ : ℕ, 0 < ε →
      (∀ i, i₀ ≤ i → EnvOf (↑S : Set (ℤ × ℤ))
        (ShellMink.shellInter (Ahat i) (MaxEnv.shell (⋃ i, Ahat i) vJ1 nJ cJ ε) w)) →
      ∀ i, max i₀ I₀ ≤ i →
      ShellMink.shellInter (Ahat i) (MaxEnv.shell (⋃ i, Ahat i) vJ1 nJ cJ ε) w ⊆
        {z | Colle37.GenClosure S (Ahat i ∪
          ShellMink.shellInter (Ahat i₀)
            (MaxEnv.shell (⋃ i, Ahat i) vJ1 nJ cJ ε) w) z} :=
  fun ε i₀ hε hEnv i hi =>
    fillCover_pointwise_of_window hfin hsweepW F gen_eq (hwin ε i₀ hε hEnv i hi)

/-- 守卫放松的免费方向：`i₀ ≤ i` 版的残项蕴含 `max i₀ I₀ ≤ i` 版。配
`not_le_max_of_le_left`（`:450`）⟹ 后者**严格**弱。 -/
theorem guard_weaken_max {P : ℕ → ℕ → ℕ → Prop} (I₀ : ℕ)
    (h : ∀ ε i₀ i, i₀ ≤ i → P ε i₀ i) : ∀ ε i₀ i, max i₀ I₀ ≤ i → P ε i₀ i :=
  fun ε i₀ i hi => h ε i₀ i (le_trans (le_max_left i₀ I₀) hi)

/-! ## §10. 归约与 `collarY` 无关：把逐点核心抽成任意集合上的形状

lane-leafa-gen，2026-09-25。

§9 的 `fillCover_pointwise_of_window` 已经说明归约**不消费** `0 < ε` 与 `Enveloped` 守卫。
本节把话说到底：它连**对象是 `collarY`** 都不消费。证明体只用到三件事——
`Y` 有限（为了取覆盖向量的上界）、`F` 给出 lex 覆盖向量、以及 `hwinAt` 这条逐点二选一。
于是同一条归约对**任何**有限 `Y` 成立，特别是对
`LaneTowerHbaseCut.cutX i`（`b3_colle2.txt:518` 的 `Â_i^{(ε)}` 的「交进 `shellSubStrip` 体」版本）。

⭐ **这一节是有消费者的**：`HwinRefute` §7 在 oct8 台架上证了 `hwin` 换成 `cutX` 之后
在真锚点 `genx = (0,1)` 处**为真**，本节就是把那条正面结论接成 `fillCover` 形状的桥。
⚠ 本节**不**主张 `cutX` 是链上该用的对象，也不主张 `collarY` 那一侧的残差因此关闭
（`HwinRefute` §3/§6 的否定对 `collarY` 仍然有效，见那里的辖域）。 -/

/-- **归约的逐点核心，脱掉 `collarY`。**  `X` 扮演 `Â_i`，`Y` 扮演「本层的领子」，
`Y₀` 扮演「`i₀` 层的领子」；三者之间**不假设**任何包含关系。

⭐ 签名里没有 `ε`、没有 `w`、没有 `vJ1`、没有 `nJ`（除 `F` 自带的）、没有任何 shell：
`fillCover_pointwise_of_window`（`:581`）是它取 `Y := collarY … i ε`、`Y₀ := collarY … i₀ ε`、
`X := Ahat i` 的实例。 -/
theorem fillCover_pointwise_generic {X Y Y₀ : Set (ℤ × ℤ)}
    (hYfin : Y.Finite) (F : FaceBlock S nJ vJ) (gen_eq : gen = F.a')
    (hwinAt : ∀ z ∈ Y, z ∈ X ∪ Y₀ ∨ ∀ b ∈ S, z + (b - gen) ∈ Y) :
    Y ⊆ {z | Colle37.GenClosure S (X ∪ Y₀) z} := by
  classical
  subst gen_eq
  obtain ⟨n', hn'⟩ := Nivat.LaneFillCover.exists_lex_covector F
  obtain ⟨C, hC⟩ : ∃ C : ℤ, ∀ z ∈ Y, dot n' z ≤ C := by
    obtain ⟨C, hC⟩ := (hYfin.image (fun z => dot n' z)).bddAbove
    exact ⟨C, fun z hz => hC ⟨z, hz, rfl⟩⟩
  have hstep : ∀ z ∈ Y, z ∈ (X ∪ Y₀) ∨
      ∀ b ∈ S.erase F.a', z + (b - F.a') ∈ (X ∪ Y₀) ∪ Y := by
    intro z hz
    rcases hwinAt z hz with hx | hw
    · exact Or.inl hx
    · exact Or.inr fun b hb => Set.mem_union_right _ (hw b (Finset.mem_of_mem_erase hb))
  intro z hz
  exact Nivat.GenClosureWeaken.genClosure_subset_genClosure F.a'_mem
    (Nivat.Colle37Geom.latticeConvex_erase_of_lexExtreme F.latticeConvex_S F.lex') z
    (Nivat.LaneFillCover.subset_genClosure_of_covector hC hn' hstep hz)

/-- **内核检查：§9 的 `fillCover_pointwise_of_window`（`:581`）确实是上一条的实例。**
只把 `X := Ahat i`、`Y := collarY … i ε`、`Y₀ := collarY … i₀ ε` 代进去；
类型不定义相等就编译不过（§85.2：「它是特例」这句话要有内核见证，不能只写在注释里）。 -/
theorem pointwise_of_window_is_an_instance
    (hfin : ∀ i, (Ahat i).Finite) (hsweepW : dot nJ w < 0)
    (F : FaceBlock S nJ vJ) (gen_eq : gen = F.a') {i i₀ ε : ℕ}
    (hwinAt : ∀ z ∈ ShellMink.shellInter (Ahat i)
        (MaxEnv.shell (⋃ i, Ahat i) vJ1 nJ cJ ε) w,
      z ∈ Ahat i ∪ ShellMink.shellInter (Ahat i₀)
            (MaxEnv.shell (⋃ i, Ahat i) vJ1 nJ cJ ε) w ∨
      ∀ b ∈ S, z + (b - gen) ∈
        ShellMink.shellInter (Ahat i) (MaxEnv.shell (⋃ i, Ahat i) vJ1 nJ cJ ε) w) :
    ShellMink.shellInter (Ahat i) (MaxEnv.shell (⋃ i, Ahat i) vJ1 nJ cJ ε) w ⊆
      {z | Colle37.GenClosure S (Ahat i ∪
        ShellMink.shellInter (Ahat i₀)
          (MaxEnv.shell (⋃ i, Ahat i) vJ1 nJ cJ ε) w) z} :=
  fillCover_pointwise_generic (collarY_finite hfin hsweepW i ε) F gen_eq hwinAt

end Nivat.FillCoverGuarded
#print axioms Nivat.FillCoverGuarded.collarY_eq
#print axioms Nivat.FillCoverGuarded.collarY_subset_shell
#print axioms Nivat.FillCoverGuarded.collarY_subset_outer_shell
#print axioms Nivat.FillCoverGuarded.collarY_finite
#print axioms Nivat.FillCoverGuarded.Ahat_subset_collarY
#print axioms Nivat.FillCoverGuarded.E_collarY_eq
#print axioms Nivat.FillCoverGuarded.depth_holds_of_mem_face
#print axioms Nivat.FillCoverGuarded.a'_mem_face_negNJ
#print axioms Nivat.FillCoverGuarded.depth_at_negNJ
#print axioms Nivat.FillCoverGuarded.depth_holds_at_negNJ
#print axioms Nivat.FillCoverGuarded.window_subset_of_depth
#print axioms Nivat.FillCoverGuarded.fillCover_of_window
#print axioms Nivat.FillCoverGuarded.fillCover_of_depth
#print axioms Nivat.FillCoverGuarded.fillCover_of_depthS
#print axioms Nivat.FillCoverGuarded.depth_of_window
#print axioms Nivat.FillCoverGuarded.Shex_free_walls

#print axioms Nivat.FillCoverGuarded.fillCover_field_of_window
#print axioms Nivat.FillCoverGuarded.not_le_max_of_le_left

#print axioms Nivat.FillCoverGuarded.forall_exists_I₀_of_exists_forall
#print axioms Nivat.FillCoverGuarded.not_exists_forall_of_forall_exists
#print axioms Nivat.FillCoverGuarded.exists_I₀_of_per_normal
#print axioms Nivat.FillCoverGuarded.not_exists_I₀_of_per_normal_infinite
#print axioms Nivat.FillCoverGuarded.fillCover_pointwise_of_window
#print axioms Nivat.FillCoverGuarded.fillCover_field_of_window_at_I₀
#print axioms Nivat.FillCoverGuarded.guard_weaken_max

#print axioms Nivat.FillCoverGuarded.fillCover_pointwise_generic
#print axioms Nivat.FillCoverGuarded.pointwise_of_window_is_an_instance
