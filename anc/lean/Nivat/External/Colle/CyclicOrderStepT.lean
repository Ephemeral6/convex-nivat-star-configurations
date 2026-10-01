/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.ANormal
import Nivat.External.Colle.ShellConvex
import Nivat.External.Colle.CyclicOrderAdjRefute

/-!
# 步长 `t` 版的 `bottom` 第 1、2 合取：`-1` 是我们加的，而且它**在树上已经为假**
（lane-env-refute）

## §0  这是对哪个问题的回答

team-lead 第 228 轮：「真正被你否掉的是「**扫掠步长必须是 1**」。问题因此变成硬规矩 5 的
标准问题——`-1` 这个量词是原文的，还是我们加的？……**你**：在你的环序机器上给出「步长 `t` 版」
的 `bottom` 第 1、2 合取长什么样——即把 `dot nJ vJ1 = -1` 换成 `dot nJ vJ1 < 0` 之后，
`:424` 还撑不撑得住结论。」

**回答分三段，结论是：不用等 hbase 读原文，这一格在树上已经判完了。**

| # | 命题 | 状态 |
|---|---|---|
| 1 | `dot nJ vJ1 < 0` | ✅ **已是定理**，`Nivat.Colle35.ChainDataGeom.dot_nJ_vJ1_neg`（`ANormal.lean:753`），从 `bottom 0` ＋ `ahat_halfPlane` ＋ `dot_nJ_vJ` 推出，**不引 `:424`**。§1 重述为去 `cg` 形。 |
| 2 | `dot nJ vJ1 = -1` | ❌ **已在树上为假**。`Nivat.ShellConvex.cgc`（`ShellConvex.lean:586`）是 `ChainDataGeom` 的**完整**居民（`def … where`，含 `bottom`），而 `cgc_dot_nJ_vJ1 : dot cgc.nJ cgc.vJ1 = -2`（`ShellConvex.lean:873`）。§1 把它写成 `¬ ∀`。 |
| 3 | 步长 `t` 版第 1 合取的**真正内容** | §2：它要求 `Â_∞` 的 `n_J`-高度**覆盖 mod `e` 的非零剩余类**（`e := -dot nJ vJ1`）。这是 `Â_∞` 的**摆位**条件，`:424` 的法向环序对它一个字都没说。§3 给同一套 `:424` 数据下两个不同摆位的内核见证。 |

⟹ 硬规矩 5 的记账：**`-1` 是我方加的量词**，而且加的方式不是「比原文强」，是「与树上已有
居民矛盾」。它在 `BottomRoom.lean` 的 `hband_of_corner_thin` / `hroom_of_corner_thin` 里
作为 `hthin` 前提出现，**那是分情形，不是推导**——`hband_of_corner_thin` 的 docstring 自己
写着「For `-⟪n_J, v_{J+1}⟫ > 1` … that part is still open」。

⚠ **我不主张 `-1` 在原文里没有出处。**我没去读 `b3_colle2.txt`（永久禁令 42：别再往下读原文）。
我主张的是：**在链上它为假**，所以无论原文怎么写，`hadj`／`unit_sweep` 那条路不能作为
`bottom` 第 1、2 合取的通用归约。原文那一句归 hbase 查。

## §0.1  `e` 是什么，为什么它是唯一的自由度

`MaxEnv.reachSet A v = {g + t • v | g ∈ A, t : ℕ}`（`ShellLine.lean:35`）。
取 `e := -dot nJ vJ1 > 0`，则从高度 `h` 的点扫出的高度恰是 `h - t*e`（`t : ℕ`）。
`bottom` 的第 1 合取要在高度 `cJ - ε - 1` 上放一条 `ℓ_J`-方向的半射线，对**每个** `ε`。
配 `ahat_halfPlane`（`cJ ≤ dot nJ g`）与 `dot_nJ_vJ = 0`（射线不改高度），
第 1 合取因此等价于一个**剩余类**条件。`e = 1` 时该条件恒真——这就是 `-1` 的全部用处。

## §0.2  ⛔ 本文件不主张的

1. ⛔ 不主张 `bottom` 为假。§2 的两条都是**蕴含**的反例（对 `A` 的摆位加条件才为假），
   与 `ANormal.not_bottom_of_shell_data`（`ANormal.lean:843`）同一口径：
   「the remaining content of `bottom` is a statement about where `Â_∞` is *placed*」。
   本文件是那句话的**定量化**：缺的正好是 mod `e` 的剩余类。
2. ⛔ 不主张 `e = 1` 在链上不可能。`Step_PeriodsRays2.lean` 的 `cgw` 就有 `e = 1`
   （`ANormal.lean` 的 `ChainDataGeom.dot_nJ_vJ1_neg` docstring 记载）。两个居民一个 `e = 1`
   一个 `e = 2`，⟹ `e` 是**数据**不是定理。
3. ⛔ 不主张 `:424` 与 `bottom` 无关的**一般**命题。§3 只给一个见证对：同一条
   `NormalCycle N 3 1` ＋ 同一组 `(nprevJ, nJ, vJ, vJ1)`，两个不同的 `A`，一个满足一个不满足。
4. ⛔ 不碰 `hroom`（永久关门）、不碰 `hwadj`、不碰射线／凸性。
-/

set_option autoImplicit false

namespace Nivat.CyclicOrderStepT

open Nivat Nivat.LE2 Nivat.MaxEnv Nivat.LaneTowerHlevNormalCycle

/-! ## §1  两条已判定的命题，写成去 `cg` 形

这两条都**不是本文件的新结果**，是树上现货的重述；放在一起才看得出它们判的是同一格的两侧。 -/

/-- **`dot nJ vJ1 < 0` 是 `ChainDataGeom` 的定理**（`ANormal.lean:753`）。
它从 `bottom 0` 推出，**不引 `:424`**，所以「步长为负」这一半不欠任何环序输入。 -/
theorem sweep_neg_of_chainDataGeom :
    ∀ (ξ xper : Config ℤ) (vl p : ℤ × ℤ) (S : Finset (ℤ × ℤ)) (gen : ℤ × ℤ)
      (cg : Nivat.Colle35.ChainDataGeom ξ xper vl p S gen), dot cg.nJ cg.vJ1 < 0 :=
  fun _ _ _ _ _ _ cg => cg.dot_nJ_vJ1_neg

/-- ⭐ **`dot nJ vJ1 = -1` 不是 `ChainDataGeom` 的定理。**

见证是树上**早已存在**的完整居民 `Nivat.ShellConvex.cgc`（`ShellConvex.lean:586`，
`def … where`，`bottom` 字段已给，见 `ShellConvex.lean:501`「`bottom` is satisfied by `cgc`」），
它的步长是 `-2`（`cgc_dot_nJ_vJ1`，`ShellConvex.lean:873`）。

⟹ 把 `bottom` 的第 1、2 合取归约到 `dot nJ vJ1 = -1`（`BottomRoom.lean` 的
`hroom_of_corner_thin` 的 `hthin`）
**不可能是从 `bottom` 出发的推导**，只能是分情形；`hadj` 那条路因此不是缺的那块砖。

⚠ 陈述形逐字抄 `ShellConvex.not_forall_isLatticeConvexRegion_shellInf_of_hRconv`
（`ShellConvex.lean:866`）的 `¬ ∀` 形，参数表相同，只换结论。 -/
theorem unit_sweep_not_of_chainDataGeom :
    ¬ ∀ (ξ xper : Config ℤ) (vl p : ℤ × ℤ) (S : Finset (ℤ × ℤ)) (gen : ℤ × ℤ)
        (cg : Nivat.Colle35.ChainDataGeom ξ xper vl p S gen), dot cg.nJ cg.vJ1 = -1 := by
  intro h
  have hc := h _ _ _ _ _ _ Nivat.ShellConvex.cgc
  rw [Nivat.ShellConvex.cgc_dot_nJ_vJ1] at hc
  omega

/-! ## §2  ⭐⭐ 步长 `t` 版第 1 合取的**确切**内容：mod `e` 的剩余类

以下三条把「`-1` 有什么用」量化掉。`e := -dot nJ vJ1`。 -/

/-- **`e = 1` 时高度条件全免。**只要 `A` 里有一个点，它下方每一个高度都扫得到，
不需要任何剩余类信息。这就是 `hthin` 在 `BottomRoom.lean` 的 `hroom_of_corner_thin` 里
起的全部作用。 -/
theorem level_free_of_thin {A : Set (ℤ × ℤ)} {nJ vJ1 : ℤ × ℤ}
    (hthin : dot nJ vJ1 = -1) {g : ℤ × ℤ} (hg : g ∈ A) (c : ℤ) (hc : c ≤ dot nJ g) :
    ∃ z ∈ reachSet A vJ1, dot nJ z = c := by
  refine ⟨g + ((dot nJ g - c).toNat : ℤ) • vJ1, ⟨g, hg, (dot nJ g - c).toNat, rfl⟩, ?_⟩
  rw [dot_add, Nivat.ColleReg.dot_zsmul_right, hthin, Int.toNat_of_nonneg (by omega)]
  ring

/-- ⭐ **同余摆位下，`e ∤ (ε+1)` 的层根本取不到**（比第 1 合取更基本的形）。

只要 `A` 的 `n_J`-高度全部同余于 `cJ`（mod `e`），扫掠集 `reachSet A vJ1` 就只落在
`cJ - e·ℤ` 这些层上。⛔ 不要 `vJ`、⛔ 不要 `hvJ`、⛔ 不要线条件——单点就够。

这是 `not_bottom_conj1_of_common_residue` 的内核，抽出来是因为 lane-tower-hbase 的
`attained_of_bottom` 的结论恰好是「某层被取到」这个形状，两边要对接就得在这一层对接。 -/
theorem not_attained_of_common_residue {A : Set (ℤ × ℤ)} {nJ vJ1 : ℤ × ℤ}
    {cJ e : ℤ} {ε : ℕ}
    (hvJ1 : dot nJ vJ1 = -e)
    (hres : ∀ g ∈ A, e ∣ (dot nJ g - cJ))
    (hdiv : ¬ e ∣ ((ε : ℤ) + 1)) :
    ¬ ∃ z ∈ reachSet A vJ1, dot nJ z = cJ - (ε : ℤ) - 1 := by
  rintro ⟨z, ⟨g, hg, t, rfl⟩, hd⟩
  rw [dot_add, Nivat.ColleReg.dot_zsmul_right, hvJ1] at hd
  obtain ⟨c, hc⟩ := hres g hg
  refine hdiv ⟨(t : ℤ) - c, ?_⟩
  linear_combination hd - hc

/-- ⭐⭐ **对接 lane-tower-hbase：链上的 `Â_∞` 高度永远不可能同余（除非 `e = 1`）。**

`hatt` 逐字是 `Nivat.HbaseLevelEnum.attained_of_bottom`
（`tmp/wip/hbase_levelenum.lean:70`，2026-09-25）的结论：对**任意** `ChainDataGeom` 居民、
**任意** `ε`，层 `cJ - ε - 1` 都被 `reachSet` 取到，对步长无要求。

⟹ 合起来：**`2 ≤ e` 的居民，其 `Â_∞` 的高度一定跨越 mod `e` 的多个剩余类。**
`cgc` 就是这样（`Kc = {0 ≤ y ∧ 2y ≤ x}`，`ShellConvex.lean:470`，`e = 2` 而高度不同余），
本条说那不是巧合，是**必然**。

⚠ 我把 `hatt` 做成显式 binder 而不是自己重证：他那条在 `tmp/wip/` 里（不在模块路径上，
按 `PROTOCOL §16` 不可 import），而重证一遍等于把同一件事记两份账。⟹ 本条的内容
**只有**「同余 ⊥ 全层可达」这一步，`hatt` 的真假归他。⚠ 我未复核他那条的 EXIT／公理（§55）。

⟹ 这条同时给 §2 的两条定下射程：`not_bottom_conj1_of_common_residue` 与
`step_eq_one_of_bottom_of_common_residue` 吃的 `hres` 在链上**恒假**（`2 ≤ e` 时），
所以它们是对**同余型 `A`** 的负控，⛔ **不是**「`bottom` 逼出 `-1`」。这正是 hbase
2026-09-25 要求标清楚的那一点，这里用定理标而不是用 docstring 标。 -/
theorem not_common_residue_of_attained {A : Set (ℤ × ℤ)} {nJ vJ1 : ℤ × ℤ} {cJ e : ℤ}
    (he : 2 ≤ e) (hvJ1 : dot nJ vJ1 = -e)
    (hatt : ∀ ε : ℕ, ∃ z ∈ reachSet A vJ1, dot nJ z = cJ - (ε : ℤ) - 1) :
    ¬ ∀ g ∈ A, e ∣ (dot nJ g - cJ) := by
  intro hres
  refine not_attained_of_common_residue (ε := 0) hvJ1 hres ?_ (hatt 0)
  intro hd
  have : e ≤ 1 := Int.le_of_dvd (by norm_num) (by simpa using hd)
  omega

/-- ⭐ **`2 ≤ e` 时第 1 合取被剩余类挡住。**

若 `Â_∞` 的 `n_J`-高度全部同余于 `cJ`（mod `e`），则对任何 `e ∤ (ε+1)` 的 `ε`，
`bottom` 的第 1 合取在该 `ε` 上为假。`hvJ : dot nJ vJ = 0` 是 `ChainDataGeom` 的字段
`dot_nJ_vJ`，保证 `ℓ_J`-方向的射线不改高度；`hres` 是**摆位**假设，不是环序假设。

⚠ 射程：`hres` 在链上恒假（见 `not_common_residue_of_attained`）。本条是对同余型 `A`
的负控，⛔ 不可读成「`bottom` 逼出 `-1`」。

前提表与结论逐字对齐 `ChainDataGeomParts.bottom`（`ChainPartsFeed.lean` 的 `bottom` 字段）
的第 1 合取，只把 `MaxEnv.reachSet (⋃ i, hatOf …)` 换成一般的 `A`。 -/
theorem not_bottom_conj1_of_common_residue {A : Set (ℤ × ℤ)} {nJ vJ vJ1 : ℤ × ℤ}
    {cJ e : ℤ} {ε : ℕ}
    (hvJ1 : dot nJ vJ1 = -e) (hvJ : dot nJ vJ = 0)
    (hres : ∀ g ∈ A, e ∣ (dot nJ g - cJ))
    (hdiv : ¬ e ∣ ((ε : ℤ) + 1)) :
    ¬ ∃ (z₀ : ℤ × ℤ) (L : ℤ), dot nJ z₀ = cJ - (ε : ℤ) - 1 ∧
        ∀ q : ℤ, L ≤ q → z₀ + q • vJ ∈ reachSet A vJ1 := by
  rintro ⟨z₀, L, hdz, hline⟩
  refine not_attained_of_common_residue hvJ1 hres hdiv ⟨z₀ + L • vJ, hline L le_rfl, ?_⟩
  rw [dot_add, Nivat.ColleReg.dot_zsmul_right, hvJ, mul_zero, add_zero, hdz]

/-- ⭐⭐ **`-1` 是被 `bottom` 逼出来的——但只在「高度同余」的摆位下。**

若 `Â_∞` 的高度全部同余于 `cJ`（mod `e`），而 `bottom` 的第 1 合取在 `ε = 0` 上成立，
则 `e = 1`，即 `dot nJ vJ1 = -1`。

⟹ 这条与 §1 的 `unit_sweep_not_of_chainDataGeom` **合起来**才是完整答案：
`-1` 不是原文的量词，也不是链的定理，它**恰好等价于**「`Â_∞` 的高度同余」这条摆位假设。
`cgc` 的 `e = 2` 正是因为它的 `Â_∞ = Kc = {0 ≤ y ∧ 2y ≤ x}`（`ShellConvex.lean:470`）
的高度**不**同余。 -/
theorem step_eq_one_of_bottom_of_common_residue {A : Set (ℤ × ℤ)} {nJ vJ vJ1 : ℤ × ℤ}
    {cJ e : ℤ}
    (he : 0 < e) (hvJ1 : dot nJ vJ1 = -e) (hvJ : dot nJ vJ = 0)
    (hres : ∀ g ∈ A, e ∣ (dot nJ g - cJ))
    (hbot : ∃ (z₀ : ℤ × ℤ) (L : ℤ), dot nJ z₀ = cJ - ((0 : ℕ) : ℤ) - 1 ∧
      ∀ q : ℤ, L ≤ q → z₀ + q • vJ ∈ reachSet A vJ1) :
    dot nJ vJ1 = -1 := by
  rcases eq_or_lt_of_le (show (1 : ℤ) ≤ e by omega) with h1 | h2
  · rw [hvJ1, ← h1]
  · exfalso
    refine not_bottom_conj1_of_common_residue hvJ1 hvJ hres ?_ hbot
    intro hd
    have : e ≤ 1 := Int.le_of_dvd (by norm_num) (by simpa using hd)
    omega

/-! ## §2.5  逆向：同余摆位下第 1 合取**恰好**在 `e ∣ (ε+1)` 的层上成立

§2 只给了「挡住」的一半。这一节补另一半，于是同余摆位下第 1 合取的真值被完全算出来：

| 层号量词 | 同余摆位下第 1 合取 |
|---|---|
| `∀ ε : ℕ`（`ChainPartsFeed.lean` 的 `bottom` 字段） | 真 ⟺ `e = 1` |
| `∃ ε : ℕ`（原文层号，见 hbase 的 `TowerHbaseUnitSweep.lean` 的 `exists_eps_bottom_conj123`） | 对任意 `e` 都真 |

⟹ 硬规矩 5 的答案在这一格上是 **(b)**：`-1` 不是几何的债，是 `∀ ε` 的债。

⭐ 与 hbase 独立对上了：`exists_eps_bottom_conj123`（`TowerHbaseUnitSweep.lean` 的 `exists_eps_bottom_conj123`，我亲读
了它的陈述与证明体）挑的层号是 `ε := (r + 1) * s`，其中 `dot nJ vJ1 = -(s+1)`。
那个 `ε` 为 `0` **当且仅当 `s = 0`**，即当且仅当步长是单位步。换句话说他的构造和下面这条
说的是同一件事的两面：层号随步长线性增长，把层号钉在 `0` 才逼出 `e = 1`。
⚠ 我没有复核他那条的 `EXIT`／公理（§55）；我复核的只是陈述与所选 `ε` 的表达式。 -/

/-- `A` 在 `+ v` 下闭 ⟹ 整条 `ℕ`-射线留在 `A` 里。 -/
theorem mem_of_natCast_zsmul {A : Set (ℤ × ℤ)} {v g : ℤ × ℤ}
    (hrec : ∀ x ∈ A, x + v ∈ A) (hg : g ∈ A) :
    ∀ t : ℕ, g + (t : ℤ) • v ∈ A := by
  intro t
  induction t with
  | zero => simpa using hg
  | succ s ih =>
    have h : g + ((s + 1 : ℕ) : ℤ) • v = (g + (s : ℤ) • v) + v := by
      push_cast
      rw [add_smul, one_smul, add_assoc]
    rw [h]
    exact hrec _ ih

/-- ⭐ **同余摆位 ＋ `e ∣ (ε+1)` ⟹ 第 1 合取在该 `ε` 上成立，步长任意。**

这是 `not_bottom_conj1_of_common_residue` 的严格逆命题：那条说 `e ∤ (ε+1)` 的层为假，
这条说 `e ∣ (ε+1)` 的层为真。两条合起来 ⟹ 同余摆位下第 1 合取的真值集合恰是
`{ε | e ∣ (ε+1)}`，它非空（`ε := e - 1`）但在 `2 ≤ e` 时不是全体。

前提全部是链上已有的东西：`hrec` 是 `ChainDataGeom` 的 `vJ`-递归，`hhp` 是半平面，
`hgres` 是 `hres` 在单点上的实例。⛔ 不要 `Primitive`，⛔ 不要 `hadj`，⛔ 不要 `:424`。

⚠ `_hvJ : dot nJ vJ = 0` **故意留着且故意不用**（所以带下划线，不是关 linter）：它是
`ChainDataGeom` 的字段 `dot_nJ_vJ`，摆在这里是为了让前提表与 `not_bottom_conj1_of_common_residue`
逐项对齐——那条**需要**它（`ℓ_J`-射线不改高度才能把矛盾推到单点上），这条不需要
（第 1 合取只对 `z₀` 一个点要求高度）。删掉它会让两条的前提表对不上，读者会以为
「挡住」比「成立」多要一条几何性质，而真相相反。 -/
theorem bottom_conj1_of_common_residue_of_dvd {A : Set (ℤ × ℤ)} {nJ vJ vJ1 : ℤ × ℤ}
    {cJ e : ℤ} {ε : ℕ} {g : ℤ × ℤ}
    (he : 0 < e) (hvJ1 : dot nJ vJ1 = -e) (_hvJ : dot nJ vJ = 0)
    (hrec : ∀ x ∈ A, x + vJ ∈ A) (hg : g ∈ A)
    (hhp : cJ ≤ dot nJ g) (hgres : e ∣ (dot nJ g - cJ))
    (hdiv : e ∣ ((ε : ℤ) + 1)) :
    ∃ (z₀ : ℤ × ℤ) (L : ℤ), dot nJ z₀ = cJ - (ε : ℤ) - 1 ∧
      ∀ q : ℤ, L ≤ q → z₀ + q • vJ ∈ reachSet A vJ1 := by
  obtain ⟨k, hk⟩ := hgres
  obtain ⟨j, hj⟩ := hdiv
  have hk0 : 0 ≤ k := by nlinarith [hk, hhp, he]
  have hj0 : 0 < j := by nlinarith [hj, he]
  have hT0 : 0 ≤ k + j := by omega
  set T : ℕ := (k + j).toNat with hTdef
  have hTcast : (T : ℤ) = k + j := Int.toNat_of_nonneg hT0
  refine ⟨g + (T : ℤ) • vJ1, 0, ?_, ?_⟩
  · rw [dot_add, Nivat.ColleReg.dot_zsmul_right, hvJ1, hTcast]
    linarith [hk, hj]
  · intro q hq
    have hqcast : ((q.toNat : ℤ)) = q := Int.toNat_of_nonneg hq
    refine ⟨g + (q.toNat : ℤ) • vJ, mem_of_natCast_zsmul hrec hg q.toNat, T, ?_⟩
    rw [hqcast]
    abel

/-! ## §3  ⭐⭐⭐ `:424` 对这一格一个字都没说

见证：把 `CyclicOrderAdjRefute.adjHexCycle`（`NormalCycle adjHexN 3 1`，`m = 3`，不是
`m = 2` 退化）的那一对相邻法向拿来当 `(nprevJ, nJ)`，`vJ := dir nJ`、`vJ1 := -(dir nprevJ)`。
全部 `:424` 前提由 `adj_premises_hold` 内核见证，步长是 `-2`（`adj_dot_nJ_vJ1`）。

在**这一组固定的环序数据**上，第 1 合取的真假完全由 `A` 决定：`A = univ` 时真，
`A = {g | ⟪n_J, g⟫ = 0}` 时假。⟹ 第 1 合取不是 `:424` 的函数，把它归约到环序
（无论归约到 `hadj` 还是归约到 `dot nJ vJ1 = -1`）都接不上。

⚠ 与第 227 轮的 `exists_adjacent_pair_not_unimodular` 是**两条不同的话**：
那条说环序给不出 `det vJ vJ1 = ±1`；这条说**即使**给出了，第 1 合取也还缺一条摆位条件。
两条一起才关掉整条派工方向。 -/

/-- `A₂ := {g | ⟪n_J, g⟫ = 0}` 的三条链上性质：非空、落在半平面 `cJ = 0` 里、高度同余。 -/
theorem adjA2_props :
    ({g : ℤ × ℤ | dot Nivat.CyclicOrderAdjRefute.adjNJ g = 0}).Nonempty ∧
    (∀ g ∈ {g : ℤ × ℤ | dot Nivat.CyclicOrderAdjRefute.adjNJ g = 0},
      (0 : ℤ) ≤ dot Nivat.CyclicOrderAdjRefute.adjNJ g) ∧
    (∀ g ∈ {g : ℤ × ℤ | dot Nivat.CyclicOrderAdjRefute.adjNJ g = 0},
      (2 : ℤ) ∣ (dot Nivat.CyclicOrderAdjRefute.adjNJ g - 0)) := by
  refine ⟨⟨((1 : ℤ), (2 : ℤ)), by decide⟩, ?_, ?_⟩
  · intro g hg
    have : dot Nivat.CyclicOrderAdjRefute.adjNJ g = 0 := hg
    omega
  · intro g hg
    have : dot Nivat.CyclicOrderAdjRefute.adjNJ g = 0 := hg
    rw [this]
    decide

/-- ⭐⭐⭐ **第 1 合取不是 `:424` 的函数。**

同一条 `NormalCycle N 3 1`、同一组 `(nprevJ, nJ, vJ, vJ1)`、同一个 `cJ = 0`，
`A` 换一下，第 1 合取就从真变假。 -/
theorem bottom_conj1_not_from_cyclic_order :
    ∃ (N : Set (ℤ × ℤ)) (_C : NormalCycle N 3 1) (nprevJ nJ vJ vJ1 : ℤ × ℤ),
      -- `:424` 侧：全部前提都真（`adj_premises_hold`）
      (Primitive nJ ∧ Primitive vJ ∧ Primitive vJ1 ∧
        dot nJ vJ = 0 ∧ dot nJ vJ1 < 0 ∧ 0 < det nprevJ nJ ∧
        (∀ y ∈ N, ¬ (0 < det nprevJ y ∧ 0 < det y nJ))) ∧
      dot nJ vJ1 = -2 ∧
      -- 摆位 A₁：第 1 合取成立
      (∃ (z₀ : ℤ × ℤ) (L : ℤ), dot nJ z₀ = (0 : ℤ) - ((0 : ℕ) : ℤ) - 1 ∧
        ∀ q : ℤ, L ≤ q → z₀ + q • vJ ∈ reachSet (Set.univ : Set (ℤ × ℤ)) vJ1) ∧
      -- 摆位 A₂：非空、在同一个半平面里、第 1 合取为假
      (∃ A₂ : Set (ℤ × ℤ), A₂.Nonempty ∧ (∀ g ∈ A₂, (0 : ℤ) ≤ dot nJ g) ∧
        ¬ ∃ (z₀ : ℤ × ℤ) (L : ℤ), dot nJ z₀ = (0 : ℤ) - ((0 : ℕ) : ℤ) - 1 ∧
          ∀ q : ℤ, L ≤ q → z₀ + q • vJ ∈ reachSet A₂ vJ1) := by
  obtain ⟨hA2ne, hA2hp, hA2res⟩ := adjA2_props
  refine ⟨Nivat.CyclicOrderAdjRefute.adjHexN, Nivat.CyclicOrderAdjRefute.adjHexCycle,
    Nivat.CyclicOrderAdjRefute.adjNprev, Nivat.CyclicOrderAdjRefute.adjNJ,
    Nivat.CyclicOrderAdjRefute.adjVJ, Nivat.CyclicOrderAdjRefute.adjVJ1,
    Nivat.CyclicOrderAdjRefute.adj_premises_hold,
    Nivat.CyclicOrderAdjRefute.adj_dot_nJ_vJ1, ?_,
    ⟨{g : ℤ × ℤ | dot Nivat.CyclicOrderAdjRefute.adjNJ g = 0}, hA2ne, hA2hp, ?_⟩⟩
  · refine ⟨((0 : ℤ), (-1 : ℤ)), 0, by decide, ?_⟩
    intro q _
    refine ⟨((0 : ℤ), (-1 : ℤ)) + q • Nivat.CyclicOrderAdjRefute.adjVJ,
      Set.mem_univ _, 0, ?_⟩
    simp
  · refine not_bottom_conj1_of_common_residue (e := 2)
      Nivat.CyclicOrderAdjRefute.adj_dot_nJ_vJ1 ?_ hA2res ?_
    · decide
    · norm_num

/-! ## §2.6  单点种子上，「高度同余」就是结论本身

回答 lane-tower-hbase 2026-09-25 的去重请求（他的 `TowerHbaseUnitSweep.lean` 的
`unit_sweep_of_forall_level` 与本文件 `step_eq_one_of_bottom_of_common_residue`
是不是同一条）。**不是重复，且他 docstring 里给的关系是反的**：
在一个已扫到层 `cJ - 1` 的种子上，`hres` 不是更弱的假设，它**恰好等价于结论**。
‧ 他多一档层号、少一条同余；我多一条同余、少一档层号。互不蕴涵，两条都留。 -/

/-- ⭐ **单点种子上，「高度同余」等价于「单位步长」。**

设种子 `g₀` 沿 `vJ1` 扫到层 `cJ - 1`（即 `bottom` 第 1 合取在 `ε = 0` 上的那个层号）。
则 `e ∣ (dot nJ g₀ - cJ)` **当且仅当** `e = 1`。

理由是一行算术：`hlev` 给 `dot nJ g₀ - cJ = t * e - 1`，于是高度余数恒为 `-1`，
`e` 整除它只能靠 `e ∣ 1`。

⟹ 这是 §2 那两条的**射程下界**：`hres` 一旦碰上一个已经扫到 `cJ - 1` 的种子，
就不再是「摆位假设」，而是结论本身。与 `not_common_residue_of_attained`
（`hatt` 给出全层可达 ⟹ `2 ≤ e` 时 `hres` 恒假）是同一件事的局部形式：
那条要 `hatt` 这个 binder，这条只要**一个**层、不要任何 `ChainDataGeom` 字段。 -/
theorem dvd_height_iff_of_seed_level {nJ vJ1 g₀ : ℤ × ℤ} {cJ e : ℤ} {t : ℕ}
    (he : 0 < e) (hvJ1 : dot nJ vJ1 = -e)
    (hlev : dot nJ (g₀ + (t : ℤ) • vJ1) = cJ - ((0 : ℕ) : ℤ) - 1) :
    e ∣ (dot nJ g₀ - cJ) ↔ e = 1 := by
  rw [dot_add, Nivat.ColleReg.dot_zsmul_right, hvJ1] at hlev
  push_cast at hlev
  constructor
  · rintro ⟨c, hc⟩
    have h1 : e ∣ (1 : ℤ) := ⟨(t : ℤ) - c, by linear_combination hlev - hc⟩
    have : e ≤ 1 := Int.le_of_dvd (by norm_num) h1
    omega
  · rintro rfl
    exact one_dvd _

/-- ⭐⭐ **对接 lane-tower-hbase：他的定理不是我那条的实例。**

在他的前提（固定种子 `g₀ ∈ A` 扫到层 `cJ - 1`）下，我那条吃的 `hres`
**单独**就推出结论——`bottom` 的第 1 合取、`dot nJ vJ = 0`、`vJ` 本身，一个都没用上。

⟹ 若把 `step_eq_one_of_bottom_of_common_residue` 实例化到 `A = {g₀}` 来「涵盖」他那条，
得到的是一条循环的推理：前提已蕴含结论。⛔ 所以
`unit_sweep_of_forall_level` 的 docstring 里那句「本条是它的 `hres` 退化到单点的情形」
**不成立**，请改成「两条独立」。

⚠ 我复核的是他的**陈述**（`TowerHbaseUnitSweep.lean` 的 `unit_sweep_of_forall_level`，
2026-09-25 亲读签名与证明体：`hbase_dot_add_zsmul` + 两式相减 + `Int.isUnit_iff`）；
他的 `EXIT`／公理我未复核（§55）。 -/
theorem step_eq_one_of_res_of_seed_level {A : Set (ℤ × ℤ)} {nJ vJ1 g₀ : ℤ × ℤ}
    {cJ e : ℤ} {t : ℕ}
    (he : 0 < e) (hvJ1 : dot nJ vJ1 = -e)
    (hg : g₀ ∈ A) (hres : ∀ g ∈ A, e ∣ (dot nJ g - cJ))
    (hlev : dot nJ (g₀ + (t : ℤ) • vJ1) = cJ - ((0 : ℕ) : ℤ) - 1) :
    dot nJ vJ1 = -1 := by
  have h1 : e = 1 := (dvd_height_iff_of_seed_level he hvJ1 hlev).mp (hres g₀ hg)
  rw [hvJ1, h1]

/-! ## §2.7  「两个剩余类」的现货：`rec_p`

集成者 2026-09-25 派单：搜树上有没有现货能排除「`Â_∞` 的高度全部同余于 `cJ` (mod `e`)」。

**有，而且是 `bottom`-free 的。** 入口是 `rec_p : ∀ g ∈ ⋃ i, Ah i, g + p ∈ ⋃ i, Ah i`
配 `dot_nJ_p : dot nJ p ≠ 0`——两者在 `EscapeW.exists_escape_abstract` 里是并排的 binder，
`EscapeW.dot_p_pos` 还把它加强成 `0 < dot nJ p`。

⟹ `Â_∞` 有一条**改变高度**的 recession 方向。于是同余条件立刻被**一步**打掉：
`g` 与 `g + p` 同在 `Â_∞`，高度差恒为 `dot nJ p`，同余要求 `e ∣ dot nJ p`。

⭐ **判据因此塌成一条算术边条件**：`e ∤ dot nJ p`。
⛔ 不是缺一个几何对象，是缺这条整除关系的**符号级判定**。`e = -dot nJ vJ1` 与 `dot nJ p`
是两个既有字段上的值，二者之间树上**没有**任何关系陈述（我搜了骨架 S6，见报告）。
-/

/-- ⭐ **两个剩余类的直接产者**。只要 `Â_∞` 有一条高度步长不被 `e` 整除的 recession 方向，
它的高度就跨越 mod `e` 的至少两个剩余类。

⚠ **不吃 `bottom`**——这是本条相对 `not_common_residue_of_attained` 的全部价值：
那条从 `bottom` 推非同余（对构造 `bottom` 而言是循环的），本条从 recession 字段推，
可以拿去**喂** `bottom`。 -/
theorem two_residues_of_rec {A : Set (ℤ × ℤ)} {nJ p g : ℤ × ℤ} {e : ℤ}
    (hg : g ∈ A) (hrec : ∀ x ∈ A, x + p ∈ A) (hdp : ¬ e ∣ dot nJ p) :
    ∃ g₁ ∈ A, ∃ g₂ ∈ A, ¬ e ∣ (dot nJ g₁ - dot nJ g₂) := by
  refine ⟨g + p, hrec g hg, g, hg, ?_⟩
  rw [dot_add]
  simpa using hdp

/-- ⭐⭐ **同一件事写成 `not_bottom_conj1_of_common_residue` 的前提的否定形**，
于是 §2 那两条负控在链上被**具体地**排除，而不是像 `not_common_residue_of_attained`
那样经由 `bottom` 排除。

前提逐条的链上出处（我核过签名，未核证明体，§55）：
- `hg` ← `hne : (⋃ i, Ah i).Nonempty`（`EscapeW.exists_escape_abstract` 的 binder）
- `hrec` ← `rec_p`（同处 binder；`ShellSubStrip.lean` 的 `rec_p` 亦同形）
- `hdp` ← **无产者**。这是本条唯一的欠账，且它是一条纯整除关系。 -/
theorem not_common_residue_of_rec {A : Set (ℤ × ℤ)} {nJ p g : ℤ × ℤ} {cJ e : ℤ}
    (hg : g ∈ A) (hrec : ∀ x ∈ A, x + p ∈ A) (hdp : ¬ e ∣ dot nJ p) :
    ¬ ∀ x ∈ A, e ∣ (dot nJ x - cJ) := by
  intro hres
  obtain ⟨c1, h1⟩ := hres (g + p) (hrec g hg)
  obtain ⟨c2, h2⟩ := hres g hg
  rw [dot_add] at h1
  exact hdp ⟨c1 - c2, by linear_combination h1 - h2⟩

/-- **反向的诚实话**：`e ∣ dot nJ p` 时 `p` 这条方向一个新剩余类都不给。
⟹ `hdp` 不是可有可无的装饰，它是这条路线的**全部**内容。

⛔ 因此不要把 `two_residues_of_rec` 读成「链上高度必不同余」——它只说
「若 `e ∤ dot nJ p` 则必不同余」。`e ∣ dot nJ p` 那一支目前**无判据**。 -/
theorem dvd_height_step_of_common_residue {A : Set (ℤ × ℤ)} {nJ p g : ℤ × ℤ} {cJ e : ℤ}
    (hg : g ∈ A) (hrec : ∀ x ∈ A, x + p ∈ A)
    (hres : ∀ x ∈ A, e ∣ (dot nJ x - cJ)) :
    e ∣ dot nJ p := by
  obtain ⟨c1, h1⟩ := hres (g + p) (hrec g hg)
  obtain ⟨c2, h2⟩ := hres g hg
  rw [dot_add] at h1
  exact ⟨c1 - c2, by linear_combination h1 - h2⟩

/-! ## §2.8  数值实例（硬规矩 6）：判据在树上唯一的完整居民 `cgc` 上成立

`cgc`（`ShellConvex.lean` 的 `cgc`）的两个相关字段是 `p := p2 = (2,1)` 与
`nJ`（其 `dot nJ z = z.2`），于是 `dot cgc.nJ p = 1`，而 `e = -dot nJ vJ1 = 2`
（`ShellConvex.lean` 的 `cgc_dot_nJ_vJ1`）。⟹ `2 ∤ 1`，§2.7 的判据**成立**。

⭐ 这解释了上一轮只从 `bottom` 侧看到的现象：`cgc` 满足 `bottom` 合取 1 而 `e = 2`，
先前我只能经 `not_common_residue_of_attained` 反推「高度必不同余」；现在是**正推**——
`rec_p` 直接供货，全程不碰 `bottom`。

⚠ **只是一个居民**。`dot nJ p = 1` 不是 `ChainDataGeom` 的定理（字段只给 `dot_nJ_p : ≠ 0`）。
⛔ 不许读成「链上 `dot nJ p` 总是 `±1`」。 -/

/-- `cgc` 的 `⟪n_J, p⟫`，内核算出来的。 -/
theorem cgc_dot_nJ_p : dot Nivat.ShellConvex.cgc.nJ Nivat.ShellConvex.p2 = 1 := by decide

/-- ⭐ **判据在 `cgc` 上兑现**：`Â_∞` 里有两点高度差为奇数，故跨 mod `2` 的两个剩余类。 -/
theorem cgc_two_residues :
    ∃ g₁ ∈ (⋃ i, Nivat.ShellConvex.cgc.Ahat i), ∃ g₂ ∈ (⋃ i, Nivat.ShellConvex.cgc.Ahat i),
      ¬ ((2 : ℤ) ∣ (dot Nivat.ShellConvex.cgc.nJ g₁ - dot Nivat.ShellConvex.cgc.nJ g₂)) :=
  two_residues_of_rec Nivat.ShellConvex.cgc.ahat_nonempty.choose_spec
    Nivat.ShellConvex.cgc.rec_p (by decide)

/-- 同一件事写成 `not_bottom_conj1_of_common_residue` 的 `hres` 的否定：
对**任何**基准高度 `c`，`cgc` 的同余条件都假。⟹ §2 那两条负控对 `cgc` 空转，
而这一次是 `bottom`-free 地看出来的。 -/
theorem cgc_not_common_residue (c : ℤ) :
    ¬ ∀ x ∈ (⋃ i, Nivat.ShellConvex.cgc.Ahat i), (2 : ℤ) ∣ (dot Nivat.ShellConvex.cgc.nJ x - c) :=
  not_common_residue_of_rec Nivat.ShellConvex.cgc.ahat_nonempty.choose_spec
    Nivat.ShellConvex.cgc.rec_p (by decide)

end Nivat.CyclicOrderStepT

#print axioms Nivat.CyclicOrderStepT.sweep_neg_of_chainDataGeom
#print axioms Nivat.CyclicOrderStepT.unit_sweep_not_of_chainDataGeom
#print axioms Nivat.CyclicOrderStepT.level_free_of_thin
#print axioms Nivat.CyclicOrderStepT.not_attained_of_common_residue
#print axioms Nivat.CyclicOrderStepT.not_common_residue_of_attained
#print axioms Nivat.CyclicOrderStepT.not_bottom_conj1_of_common_residue
#print axioms Nivat.CyclicOrderStepT.step_eq_one_of_bottom_of_common_residue
#print axioms Nivat.CyclicOrderStepT.mem_of_natCast_zsmul
#print axioms Nivat.CyclicOrderStepT.bottom_conj1_of_common_residue_of_dvd
#print axioms Nivat.CyclicOrderStepT.adjA2_props
#print axioms Nivat.CyclicOrderStepT.bottom_conj1_not_from_cyclic_order
#print axioms Nivat.CyclicOrderStepT.dvd_height_iff_of_seed_level
#print axioms Nivat.CyclicOrderStepT.step_eq_one_of_res_of_seed_level
#print axioms Nivat.CyclicOrderStepT.two_residues_of_rec
#print axioms Nivat.CyclicOrderStepT.not_common_residue_of_rec
#print axioms Nivat.CyclicOrderStepT.dvd_height_step_of_common_residue
#print axioms Nivat.CyclicOrderStepT.cgc_dot_nJ_p
#print axioms Nivat.CyclicOrderStepT.cgc_two_residues
#print axioms Nivat.CyclicOrderStepT.cgc_not_common_residue
