/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
-- ⚠ import 刻意取到最浅：`ItemII` 给 `Exhausts` 与 `placement_of_exhausts`，`ChainMax` 给
-- `hatOf`，`LeafAShellAttain` 是本 lane 自己的 §7。三者并集闭包 88 个模块（本轮实测 89），
-- 不含 `RegionSteps` / `ColleRegion` / `Case2WindowProbe` / `NfpLPreamble`（实测）。
--
-- 第 233 轮加第四条 `ChainPartsFeed`（集成者裁决 4 授权，§10 的接线用）。加之前算过传递闭包：
-- `ChainPartsFeed` 闭包 99 个模块、与本文件原闭包并集 101 个，**四个禁 import 模块一个都不在**
-- （正控：`ItemII` 在 `ChainPartsFeed` 闭包里 = True）；且
-- `LeafAShellLsideFork ∉ ChainPartsFeed` 的闭包 ⟹ 不成环（全仓只有 `All.lean` import 本文件）。
import Nivat.External.Colle.ItemII
import Nivat.External.Colle.ChainMax
import Nivat.External.Colle.LeafAShellAttain
import Nivat.External.Colle.ChainPartsFeed
-- 第 236 轮加第五条 `RecVJFromParts`（lane-leafa-gen 的主仓文件，§16d 的接线用）。加之前自己
-- 算了传递闭包（`_impclosure.py` 忽略实参、只打印硬编码模块名，那条读数作废，我改手算）：
-- `RecVJFromParts` 闭包 102 个模块，**四个禁 import 模块一个都不在**（正控：`PartsToGeom` /
-- `ChainPartsFeed` 在闭包里 = True；负控 `Nivat.Bogus.Zzz` = False）；
-- `LeafAShellLsideFork ∉` 它的闭包 ⟹ 不成环。与本文件原闭包（101）并集 104，净增 3 个模块。
import Nivat.External.Colle.RecVJFromParts
-- 第 238 轮加第六条 `PartsChainFeed`（集成者的主仓文件，§18 的接线用）。加之前跑了**修复版**
-- `tmp/_impclosure.py`（旧版忽略实参，凡引旧版输出的收据作废；本轮读数来自修复版）：
--     [graph] modules parsed: 431   [ctrl:parse] total import edges = 1635
--     Nivat.External.Colle.PartsChainFeed  closure 105
--       [ctrl] self-in-closure=True  sentinel(Nivat.Bogus.Zzz)-in-closure=False
--       RegionSteps/ColleRegion/Case2WindowProbe/NfpLPreamble 四条全 False  ✓ clean
-- 成环检查：全仓 `grep -rn "import …LeafAShellLsideFork"` 除 `All.lean` 外命中 0
-- （同命令哨兵 `import …ChainPartsFeed` 命中 5，非零 ⟹ grep 确实在跑，§61.1(b)）。
import Nivat.External.Colle.PartsChainFeed
-- 第 239 轮加第七条 `HcombOrient`（lane-tower-hbase / env-refute 共用的主仓文件，§22 用它的
-- `W₀`）。加之前跑了 `tmp/_impclosure.py`：
--     [graph] modules parsed: 433   [ctrl:parse] total import edges = 1649
--     Nivat.External.Colle.HcombOrient  closure 104
--       [ctrl] self-in-closure=True  sentinel(Nivat.Bogus.Zzz)-in-closure=False
--       RegionSteps/ColleRegion/Case2WindowProbe/NfpLPreamble 四条全 False  ✓ clean
-- 成环检查：`LeafAShellLsideFork ∉ closure(HcombOrient)`（实算 False；同次实算
-- `EnvRefuteOrient ∉ closure(HcombOrient)` 也是 False —— 要紧，因为 env-refute 本轮已经
-- 反过来 import 了本文件（`EnvRefuteOrient.lean` 的 import 段），若 `HcombOrient` 经它绕回来
-- 就成环）。同命令哨兵：self-in-closure=True。
import Nivat.External.Colle.HcombOrient

/-!
# 洞 1 ℓ 侧的 `0 < k` 承重判定：它不是取向约定，是 `rec_vJ` 逼出来的

## §0 本文件回答什么

第 230 轮的问题（集成者派）：读 `TLEndgame.Lside_all_of_kpos`（`tmp/wip/lead-lside-endgame.lean`
／自足副本 `tmp/wip/nlmax-lside-package.lean`）的**证明体**，判 `0 < k` 在哪一步承重，
并**单独判** `det p vJ = 0` 那一档。三种结果都收。

**答：结果 2（分叉坐实），而且比「某个 tactic 用了 `0 < k`」强得多 ——
`0 < k` 在链上是可推的，`Lside_all_of_kpos` 的 `hkpos` binder 是冗余的。**

本文件的声明表：

* §1 `binetCauchy_lside` — 2D Binet–Cauchy 恒等式（纯 `ring`），下面三处都用它。
* §2 `det_p_vJ_ne_of_fields` — `det p vJ = 0` **那一档在链上不存在**：由现有三条字段
  `dot_nJ_vJ` / `dot_nJ_p` / `vJ_ne` 直接排除。
* §2 `dot_nl_vJ_eq_zero_of_det_p_vJ_zero_lside` / `nL_eq_zero_of_det_p_vJ_zero_lside` /
  `k_eq_zero_of_det_p_vJ_zero_lside` / `not_primitive_zero_lside` /
  `Lside_all_at_det_p_vJ_zero` — 若**强行**丢掉那三条字段进入该档，三条义务确实全成立，
  但 `n_ℓ = 0`，不是本原法向。⟹ 该档不是「分叉消失」，是「对象退化」。
* §3 `dot_nl_vJ_nonneg_of_recvJ_lside` — `rec_vJ` ＋ `Exhausts` 的**免费子集方向** ⟹
  `0 ≤ ⟪nℓ, v_J⟫`。**不吃 `ahat_halfPlane_L`**。
* §3 `k_pos_of_recvJ_lside` — 上一条 ＋ `det p vJ ≠ 0` ⟹ `0 < k`。
* §4 `det_p_vJ_pos_of_k_pos_lside` / `k_pos_iff_det_p_vJ_pos_lside` — `0 < k` 与
  `0 < det p vJ` 在 `hp_neg` ＋ `hpartner` 的 `0 < det nℓ vl` 下**等价**。
* §5 `det_p_vJ_pos_of_chain_fields` — 合成：链上现有 binder ⟹ `0 < det p vJ`（无自由选择）。
* §5 `not_hattain_of_chain_fields` — 接上本 lane 的 `LeafAShellAttain` §7 ⟹ `hattain` 为假。
* §6 `rigLsideFork` — 非空真见证（内核，`decide`/`norm_num` 级）。
* §8 `m_ne_zero_of_dot_vl_J` / `dot_vl_J_neg_of_m_neg` / `kJ_pos_of_det_p_vJ_pos_of_m_neg` /
  `fork_refutation_needs_m_pos` / `rigMsignNeg` — **`not_hattain_of_chain_fields` 的
  `hmpos : 0 < m` 分档消不掉**：`m` 翻号 ⟹ `k_J` 翻号 ⟹ §7 不适用。`m < 0` 是真逃生口。

## §1 承重点定位（逐 tactic，我亲读 `nlmax-lside-package.lean` 的证明体）

`Lside_all_of_kpos` 的三条义务，`0 < k` 的用处逐条是：

| 义务 | `0 < k` 用在哪 | 能不能换 |
|---|---|---|
| `rec_vJ`（第一条） | 只经 `have hvJ : 0 ≤ dot nℓ vJ := by nlinarith [mul_self_nonneg (det p vJ)]` | **能**换成 `0 ≤ ⟪nℓ,v_J⟫`，见 `recvJ_of_dot_nl_vJ_nonneg_lside` |
| `ahat_halfPlane_L`（第二条） | `mul_le_mul_of_nonneg_left hg (le_of_lt hkpos)`，只要 `0 ≤ k` | **不能**——`k < 0` 时该义务对**一切** `cL` 为假 |
| `ahat_attained_L`（第三条） | **一处也没有**（只用 `Primitive nℓ` 造 `(cz*x, cz*y)`） | 不适用 |

集成者上一封的警告在内核里坐实了：`(det p vJ)² = k · ⟪nℓ,v_J⟫` 在 `det p vJ ≠ 0` 时把两个
符号锁成同号，所以「改吃 `0 ≤ ⟪nℓ,v_J⟫`」**不是弱化，是等价**（`k_pos_iff_dot_nl_vJ_nonneg_lside`）。

⭐ **但真正的结论不在这张表里。** 表只说「`Lside_all_of_kpos` 这个证明在哪用了符号」。
本文件 §3 说的是更强的话：**`0 < k` 根本不是要裁的前提，它被 `rec_vJ` 这条字段推出来**。
`rec_vJ` 的原文锚点是 `b3_colle2.txt:506`（「two semi-infinite edges, one of which is parallel to
`ℓ` and the other one is parallel to `ℓ_J`」），是原文给的，不是我们的取向约定。
⟹ 集成者方案 (a)「把原文接续序 `w ≺ ⋯ ≺ w'` 找回来加回 `IsRegion`」**救不了 shell 那条路线**：
ℓ 侧的符号不是从接续序读出来的，是从 `Â_∞` 的两条退化方向读出来的。

## §2 链上 binder 出处（我亲读源码，非转述）

* `rec_vJ`：`ChainDataGeom` 第 25 条字段（`ChainGeom.lean`，标识符 `rec_vJ`），
  原文 `b3_colle2.txt:506`。
* `dot_nJ_vJ : dot nJ vJ = 0` / `dot_nJ_p : dot nJ p ≠ 0` / `vJ_ne`：`ChainDataGeom` 字段
  （`ChainGeom.lean`，标识符 `dot_nJ_vJ` / `dot_nJ_p` / `vJ_ne`）。
* `hp_neg : ∃ c : ℕ, 0 < c ∧ p = -(c : ℤ) • vl`：`exists_chainData` 的 binder
  （`RegionSteps.lean`，标识符 `hp_neg`；⚠ 禁入模块，但**读**是允许的，我亲读了那一行）。
* `Primitive nℓ` / `dot nℓ vl = 0` / `0 < det nℓ vl`：`exists_chainData` 的 `hpartner`
  合取项（`RegionSteps.lean`，标识符 `hpartner`；同上，亲读）。
* `Exhausts A nℓ cz`：`ItemII.lean` 的 `Exhausts`，原文 `b3_colle2.txt:498`。
* `hnLk : det p vJ • ((-p.2 : ℤ), p.1) = k • nℓ`：**免费**。`placement_of_exhausts`
  （`ItemII.lean`，标识符 `placement_of_exhausts`）的证明体里，`hnLk` 在 `hkpos` **之前**
  得出，只用 `hvl` / `hdet` / `hpvJ` / `hprim` / `hperp`，不用 `hhp` / `hatt`（我亲读证明体）。

## §3 本文件**不**主张什么

* 不主张 `hattain` 那条路线该被砍。它主张的是「两条路线不能同时走」，和上一轮 §7 一样：
  `0 < det p vJ` 现在有了**链上的**来源（`rec_vJ`），不再只是 `tmp/wip/lead-vjsign.lean`
  的一个选择 —— 这一步是本轮相对上一轮的**差**。
* 不主张 `Exhausts` 的**反向**包含（`{cz ≤ ⟪nℓ,·⟫} ⊆ ⋃ Â_i`）。§3 只用**正向**
  （`⋃ Â_i ⊆ {cz ≤ ⟪nℓ,·⟫}`），它对任意 `kk : ℕ → ℕ` 免费（`iUnion_hatOf_subset_halfPlane_lside`）；
  反向对一般 `kk` 我没有证，也不需要。
* 不主张 §5 的 `¬ hattain` 是「`shellEnv` 为假」。`shellEnv` 是另一条字段，不在本文件里。
-/

set_option autoImplicit false

namespace Nivat.LaneLeafAShellLsideFork

open Nivat Nivat.LE2 Nivat.Colle35

/-! ## §1 2D Binet–Cauchy -/

/-- 2D Binet–Cauchy：`(a·c)(b·d) − (a·d)(b·c) = (a×b)(c×d)`。纯 `ring`。 -/
theorem binetCauchy_lside (a b c d : ℤ × ℤ) :
    dot a c * dot b d - dot a d * dot b c = det a b * det c d := by
  simp only [dot, det]
  ring

/-- `v ≠ 0` ⟹ `0 < ⟪v,v⟫`。 -/
theorem dot_self_pos_lside {v : ℤ × ℤ} (hv : v ≠ 0) : 0 < dot v v := by
  have h1 : v.1 ≠ 0 ∨ v.2 ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hv (Prod.ext hc.1 hc.2)
  simp only [dot]
  rcases h1 with h | h
  · nlinarith [mul_self_nonneg v.2, mul_self_pos.mpr h]
  · nlinarith [mul_self_nonneg v.1, mul_self_pos.mpr h]

/-! ## §2 `det p vJ = 0` 那一档：在链上不存在 -/

/-- ⭐ **`det p vJ = 0` 那一档由现有三条 `ChainDataGeom` 字段排除。**
`dot_nJ_vJ : dot nJ vJ = 0`、`dot_nJ_p : dot nJ p ≠ 0`、`vJ_ne : vJ ≠ 0`
（三者都在 `ChainGeom.lean` 的 `ChainDataGeom` 里，标识符即字段名）⟹ `det p vJ ≠ 0`。

机理：`det p vJ = 0` 说 `p ∥ v_J`；`n_J ⊥ v_J` 于是也 `⊥ p`，与 `dot nJ p ≠ 0` 冲突。
Binet–Cauchy 取 `a := nJ, b := vJ, c := p, d := vJ`：
`⟪nJ,p⟫⟪vJ,vJ⟫ − ⟪nJ,vJ⟫⟪vJ,p⟫ = det nJ vJ · det p vJ`。

⚠ 这与 `ChainGeom.lean` 的 `det_ne_zero_of_dot` 结论相容但**不是同一条**：那条给的是
`det vJ p ≠ 0`（顺序相反），本条直接给 `det p vJ ≠ 0`，省掉调用点一步反号。 -/
theorem det_p_vJ_ne_of_fields {nJ p vJ : ℤ × ℤ}
    (hnJvJ : dot nJ vJ = 0) (hnJp : dot nJ p ≠ 0) (hvJ : vJ ≠ 0) :
    det p vJ ≠ 0 := by
  intro hzero
  have hbc := binetCauchy_lside nJ vJ p vJ
  rw [hnJvJ, hzero, mul_zero, zero_mul, sub_zero] at hbc
  exact hnJp ((mul_eq_zero.mp hbc).resolve_right (dot_self_pos_lside hvJ).ne')

/-- 在 `det p vJ = 0` 一档上，`v_J` 与 `v_ℓ` 共线，于是 `⟪nℓ, v_J⟫ = 0`。
（`p = t • v_ℓ`，`t ≠ 0` 由 `hp_neg` 的 `0 < c` 给。）

Binet–Cauchy 取 `a := nℓ, b := vl, c := vJ, d := vl`。 -/
theorem dot_nl_vJ_eq_zero_of_det_p_vJ_zero_lside {vl p vJ nℓ : ℤ × ℤ} {t : ℤ}
    (hvl : vl ≠ 0) (hpt : p = t • vl) (ht : t ≠ 0)
    (hperp : dot nℓ vl = 0) (hzero : det p vJ = 0) :
    dot nℓ vJ = 0 := by
  have hdvl : det vl vJ = 0 := by
    have h : t * det vl vJ = 0 := by
      rw [← hzero, hpt]
      simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      ring
    exact (mul_eq_zero.mp h).resolve_left ht
  have hbc := binetCauchy_lside nℓ vl vJ vl
  have hvJvl : det vJ vl = 0 := by
    have : det vJ vl = -det vl vJ := by simp only [det]; ring
    rw [this, hdvl, neg_zero]
  rw [hperp, hvJvl, zero_mul, mul_zero, sub_zero] at hbc
  exact (mul_eq_zero.mp hbc).resolve_right (dot_self_pos_lside hvl).ne'

/-- `det p vJ = 0` ⟹ `ℓ_ι` 的法向 `n_ℓ` 是**零向量**。 -/
theorem nL_eq_zero_of_det_p_vJ_zero_lside {p vJ : ℤ × ℤ} (hzero : det p vJ = 0) :
    det p vJ • ((-p.2 : ℤ), p.1) = (0 : ℤ × ℤ) := by
  rw [hzero, zero_smul]

/-- 零向量不本原：`Primitive (0,0)` 为假。⟹ `det p vJ = 0` 一档上的 `n_ℓ` 不是格线法向。 -/
theorem not_primitive_zero_lside : ¬ Primitive ((0 : ℤ), (0 : ℤ)) := by
  intro h
  obtain ⟨x, y, hxy⟩ := h
  simp only at hxy
  omega

/-- `det p vJ = 0` ⟹ `k = 0`（`nℓ ≠ 0` 由 `Primitive nℓ` 给）。 -/
theorem k_eq_zero_of_det_p_vJ_zero_lside {p vJ nℓ : ℤ × ℤ} {k : ℤ}
    (hprim : Primitive nℓ)
    (hnLk : det p vJ • ((-p.2 : ℤ), p.1) = k • nℓ) (hzero : det p vJ = 0) :
    k = 0 := by
  have hz : (0 : ℤ × ℤ) = k • nℓ := by
    rw [← nL_eq_zero_of_det_p_vJ_zero_lside (vJ := vJ) hzero, hnLk]
  by_contra hk
  refine hprim.ne_zero (Prod.ext ?_ ?_)
  · have h1 : k * nℓ.1 = 0 := by
      have := congrArg Prod.fst hz
      simpa [Prod.smul_fst, smul_eq_mul] using this.symm
    exact (mul_eq_zero.mp h1).resolve_left hk
  · have h2 : k * nℓ.2 = 0 := by
      have := congrArg Prod.snd hz
      simpa [Prod.smul_snd, smul_eq_mul] using this.symm
    exact (mul_eq_zero.mp h2).resolve_left hk

/-- ⭐ **`det p vJ = 0` 一档单独判：三条义务全成立，但对象退化。**

丢掉 `det_p_vJ_ne_of_fields` 的三条字段、强行进入 `det p vJ = 0`：`n_ℓ = 0`、`c_L = 0`，
三条义务（`rec_vJ` / `ahat_halfPlane_L` / `ahat_attained_L`）在**零个**符号前提下全部成立。
⟹ 集成者问的「三条义务若在那一档也成立，分叉才真的消失」——它们成立，但分叉**没有**消失，
因为该档的 `n_ℓ` 由 `not_primitive_zero_lside` 不是本原法向，而且该档由
`det_p_vJ_ne_of_fields` 在链上被排除。

⚠ 本条的 `U` 只当抽象集合收；`ahat_attained_L` 那一支需要 `U` 非空，由 `hne` 显式收。 -/
theorem Lside_all_at_det_p_vJ_zero {U : Set (ℤ × ℤ)} {p vJ : ℤ × ℤ}
    (hzero : det p vJ = 0) (hne : U.Nonempty)
    (hrecU : ∀ g ∈ U, g + vJ ∈ U) :
    (∀ g ∈ U, g + vJ ∈ U) ∧
    (∀ g ∈ U, (0 : ℤ) ≤ dot (det p vJ • ((-p.2 : ℤ), p.1)) g) ∧
    (∃ g ∈ U, dot (det p vJ • ((-p.2 : ℤ), p.1)) g = (0 : ℤ)) := by
  refine ⟨hrecU, ?_, ?_⟩
  · intro g _
    rw [nL_eq_zero_of_det_p_vJ_zero_lside (vJ := vJ) hzero]
    simp only [dot]
    norm_num
  · obtain ⟨g, hg⟩ := hne
    refine ⟨g, hg, ?_⟩
    rw [nL_eq_zero_of_det_p_vJ_zero_lside (vJ := vJ) hzero]
    simp only [dot]
    norm_num

/-! ## §3 `rec_vJ` 逼出 `0 < k`：不吃 `ahat_halfPlane_L` -/

/-- **`Exhausts` 的正向包含对任意 `kk` 免费**：`⋃ Â_i ⊆ {z | cz ≤ ⟪nℓ,z⟫}`。

`hatOf A kk vl i = {z | z + kk i • vl ∈ A i}`（`ChainMax.lean`，标识符 `hatOf`），而
`⟪nℓ,·⟫` 沿 `v_ℓ` 平移不变（`hperp`）。⚠ **反向包含不在本条里**，对一般 `kk` 我没有证。 -/
theorem iUnion_hatOf_subset_halfPlane_lside {A : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ}
    {nℓ vl : ℤ × ℤ} {cz : ℤ}
    (hperp : dot nℓ vl = 0) (hexh : Exhausts A nℓ cz) :
    (⋃ i, hatOf A kk vl i) ⊆ {z : ℤ × ℤ | cz ≤ dot nℓ z} := by
  intro z hz
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
  have hmem : z + (kk i : ℤ) • vl ∈ (⋃ j, A j) := Set.mem_iUnion.mpr ⟨i, hi⟩
  rw [hexh] at hmem
  have hs : dot nℓ (z + (kk i : ℤ) • vl) = dot nℓ z := dot_add_zsmul_of_perp hperp z _
  simp only [Set.mem_setOf] at hmem ⊢
  linarith [hs ▸ hmem]

/-- ⭐⭐⭐ **`rec_vJ` ⟹ `0 ≤ ⟪nℓ, v_J⟫`。不吃 `ahat_halfPlane_L`，不吃任何符号前提。**

`v_J` 是 `Â_∞` 的退化方向（`rec_vJ`，原文 `b3_colle2.txt:506`），而 `Â_∞` 落在
`{cz ≤ ⟪nℓ,·⟫}` 里（`iUnion_hatOf_subset_halfPlane_lside`，免费）。若 `⟪nℓ,v_J⟫ < 0`，
沿 `v_J` 迭代把 `⟪nℓ,·⟫` 推到 `−∞`，越过 `cz`。

⚠ **`hne` 是必需的**（空集上 `rec_vJ` 空真，推不出任何东西）；链上由
`ahat_attained_L` 或 `ahat_nonempty` 给。 -/
theorem dot_nl_vJ_nonneg_of_recvJ_lside {A : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ}
    {nℓ vl vJ : ℤ × ℤ} {cz : ℤ}
    (hperp : dot nℓ vl = 0) (hexh : Exhausts A nℓ cz)
    (hne : (⋃ i, hatOf A kk vl i).Nonempty)
    (hrec : ∀ g ∈ (⋃ i, hatOf A kk vl i), g + vJ ∈ ⋃ i, hatOf A kk vl i) :
    0 ≤ dot nℓ vJ := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨g₀, hg₀⟩ := hne
  -- `g₀ + j • vJ ∈ Â_∞` for every `j : ℕ`
  have hiter : ∀ j : ℕ, g₀ + (j : ℤ) • vJ ∈ ⋃ i, hatOf A kk vl i := by
    intro j
    induction j with
    | zero => simpa using hg₀
    | succ n ih =>
        have := hrec _ ih
        have heq : g₀ + (n : ℤ) • vJ + vJ = g₀ + ((n + 1 : ℕ) : ℤ) • vJ := by
          push_cast
          rw [add_smul, one_smul, add_assoc]
        rwa [heq] at this
  -- `⟪nℓ, g₀ + j vJ⟫ = ⟪nℓ,g₀⟫ + j ⟪nℓ,vJ⟫`
  have hval : ∀ j : ℕ, dot nℓ (g₀ + (j : ℤ) • vJ) = dot nℓ g₀ + (j : ℤ) * dot nℓ vJ := by
    intro j
    rw [dot_add]
    simp only [dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  -- choose `j` large enough to break `cz ≤ ·`
  have hsub := iUnion_hatOf_subset_halfPlane_lside (kk := kk) hperp hexh
  set N : ℕ := (dot nℓ g₀ - cz + 1).toNat with hN
  have hNge : dot nℓ g₀ - cz + 1 ≤ (N : ℤ) := by
    rw [hN]
    exact Int.self_le_toNat _
  have hmem := hsub (hiter N)
  simp only [Set.mem_setOf] at hmem
  rw [hval N] at hmem
  have hneg : (N : ℤ) * dot nℓ vJ ≤ -(N : ℤ) := by
    have h1 : dot nℓ vJ ≤ -1 := by omega
    have h2 : (0 : ℤ) ≤ (N : ℤ) := Int.natCast_nonneg N
    nlinarith
  linarith

/-- ⭐⭐⭐⭐ **`0 < k` 在链上是可推的，不是要裁的前提。**

`(det p vJ)² = ⟪n_ℓ, v_J⟫ = k ⟪nℓ, v_J⟫`，左边 `> 0`（`det p vJ ≠ 0`，由
`det_p_vJ_ne_of_fields` 从三条字段给），右边 `⟪nℓ,v_J⟫ ≥ 0`（`rec_vJ`，上一条）⟹ `0 < k`。

⟹ `TLEndgame.Lside_all_of_kpos`（`tmp/wip/nlmax-lside-package.lean`，标识符
`Lside_all_of_kpos`）的 `hkpos` binder **是冗余的**。 -/
theorem k_pos_of_recvJ_lside {A : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ}
    {nℓ vl vJ p : ℤ × ℤ} {cz k : ℤ}
    (hperp : dot nℓ vl = 0) (hexh : Exhausts A nℓ cz)
    (hne : (⋃ i, hatOf A kk vl i).Nonempty)
    (hrec : ∀ g ∈ (⋃ i, hatOf A kk vl i), g + vJ ∈ ⋃ i, hatOf A kk vl i)
    (hnLk : det p vJ • ((-p.2 : ℤ), p.1) = k • nℓ)
    (hpvJ : det p vJ ≠ 0) :
    0 < k := by
  have hnn : 0 ≤ dot nℓ vJ := dot_nl_vJ_nonneg_of_recvJ_lside hperp hexh hne hrec
  have hsq : dot (det p vJ • ((-p.2 : ℤ), p.1)) vJ = det p vJ * det p vJ := by
    simp only [dot, det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  have hk : dot (det p vJ • ((-p.2 : ℤ), p.1)) vJ = k * dot nℓ vJ := by
    rw [hnLk, dot_smul]
  have hpos : 0 < k * dot nℓ vJ := by
    rw [← hk, hsq]
    exact mul_self_pos.mpr hpvJ
  by_contra hcon
  push_neg at hcon
  nlinarith

/-- `rec_vJ` 的第一条义务只吃 `0 ≤ ⟪nℓ, v_J⟫`，不吃 `k` 的符号 ——
这是 §1 那张表第一行的内核形。 -/
theorem recvJ_of_dot_nl_vJ_nonneg_lside {nℓ vJ : ℤ × ℤ} {cz : ℤ}
    (hnn : 0 ≤ dot nℓ vJ) :
    ∀ g ∈ {z : ℤ × ℤ | cz ≤ dot nℓ z}, g + vJ ∈ {z : ℤ × ℤ | cz ≤ dot nℓ z} := by
  intro g hg
  simp only [Set.mem_setOf] at hg ⊢
  rw [dot_add]
  linarith

/-- `0 ≤ ⟪nℓ,v_J⟫ ↔ 0 < k`（在 `det p vJ ≠ 0` 下）——集成者的警告在内核里坐实：
「改吃 `0 ≤ ⟪nℓ,v_J⟫`」不是弱化，是等价。 -/
theorem k_pos_iff_dot_nl_vJ_nonneg_lside {nℓ vJ p : ℤ × ℤ} {k : ℤ}
    (hnLk : det p vJ • ((-p.2 : ℤ), p.1) = k • nℓ) (hpvJ : det p vJ ≠ 0) :
    (0 < k ↔ 0 ≤ dot nℓ vJ) := by
  have hsq : dot (det p vJ • ((-p.2 : ℤ), p.1)) vJ = det p vJ * det p vJ := by
    simp only [dot, det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  have hk : dot (det p vJ • ((-p.2 : ℤ), p.1)) vJ = k * dot nℓ vJ := by
    rw [hnLk, dot_smul]
  have hpos : 0 < k * dot nℓ vJ := by
    rw [← hk, hsq]
    exact mul_self_pos.mpr hpvJ
  constructor
  · intro hkp
    by_contra hcon
    push_neg at hcon
    nlinarith
  · intro hnn
    by_contra hcon
    push_neg at hcon
    nlinarith

/-! ## §4 `0 < k ⟺ 0 < det p vJ`（在 `hp_neg` ＋ `hpartner` 下） -/

/-- ⭐⭐ **`0 < k ⟹ 0 < det p vJ`。**

`det n_ℓ v_ℓ = det p v_J · det (dir p) v_ℓ = det p v_J · c · ⟪v_ℓ,v_ℓ⟫`（用 `hp_neg` 的
`p = -(c:ℤ) • v_ℓ`），又 `det n_ℓ v_ℓ = k · det nℓ v_ℓ`。于是
`k · det nℓ v_ℓ = det p v_J · c · ⟪v_ℓ,v_ℓ⟫`，三个正因子（`hnlvl` / `hc` / `hvl`）定号。 -/
theorem det_p_vJ_pos_of_k_pos_lside {vl p vJ nℓ : ℤ × ℤ} {c : ℕ} {k : ℤ}
    (hvl : vl ≠ 0) (hc : 0 < c) (hp : p = -(c : ℤ) • vl)
    (hnlvl : 0 < det nℓ vl)
    (hnLk : det p vJ • ((-p.2 : ℤ), p.1) = k • nℓ)
    (hkpos : 0 < k) :
    0 < det p vJ := by
  have hvv : 0 < dot vl vl := dot_self_pos_lside hvl
  have hcz : (0 : ℤ) < (c : ℤ) := by exact_mod_cast hc
  have hkey : k * det nℓ vl = det p vJ * ((c : ℤ) * dot vl vl) := by
    have hL : det (det p vJ • ((-p.2 : ℤ), p.1)) vl
        = det p vJ * ((c : ℤ) * dot vl vl) := by
      subst hp
      simp only [det, dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      ring
    rw [← hL, hnLk]
    simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  nlinarith [mul_pos hkpos hnlvl, mul_pos hcz hvv]

/-- 反向：`0 < det p vJ ⟹ 0 < k`（同一恒等式）。两条合起来是 `iff`。 -/
theorem k_pos_of_det_p_vJ_pos_lside {vl p vJ nℓ : ℤ × ℤ} {c : ℕ} {k : ℤ}
    (hvl : vl ≠ 0) (hc : 0 < c) (hp : p = -(c : ℤ) • vl)
    (hnlvl : 0 < det nℓ vl)
    (hnLk : det p vJ • ((-p.2 : ℤ), p.1) = k • nℓ)
    (hdpos : 0 < det p vJ) :
    0 < k := by
  have hvv : 0 < dot vl vl := dot_self_pos_lside hvl
  have hcz : (0 : ℤ) < (c : ℤ) := by exact_mod_cast hc
  have hkey : k * det nℓ vl = det p vJ * ((c : ℤ) * dot vl vl) := by
    have hL : det (det p vJ • ((-p.2 : ℤ), p.1)) vl
        = det p vJ * ((c : ℤ) * dot vl vl) := by
      subst hp
      simp only [det, dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      ring
    rw [← hL, hnLk]
    simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  nlinarith [mul_pos hdpos (mul_pos hcz hvv)]

theorem k_pos_iff_det_p_vJ_pos_lside {vl p vJ nℓ : ℤ × ℤ} {c : ℕ} {k : ℤ}
    (hvl : vl ≠ 0) (hc : 0 < c) (hp : p = -(c : ℤ) • vl)
    (hnlvl : 0 < det nℓ vl)
    (hnLk : det p vJ • ((-p.2 : ℤ), p.1) = k • nℓ) :
    (0 < k ↔ 0 < det p vJ) :=
  ⟨det_p_vJ_pos_of_k_pos_lside hvl hc hp hnlvl hnLk,
   k_pos_of_det_p_vJ_pos_lside hvl hc hp hnlvl hnLk⟩

/-! ## §5 合成：链上 binder ⟹ `0 < det p vJ`，⟹ `hattain` 为假 -/

/-- ⭐⭐⭐⭐⭐ **`0 < det p vJ` 在链上不是选择，是推论。**

binder 逐条都是链上现货（出处见文件头 §2）：三条 `ChainDataGeom` 字段
（`dot_nJ_vJ` / `dot_nJ_p` / `vJ_ne`）＋ `rec_vJ` ＋ `Exhausts`（原文 `:498`）＋
`hp_neg` ＋ `hpartner` 的 `dot nℓ vl = 0` 与 `0 < det nℓ vl` ＋ `Â_∞` 非空。

⟹ `tmp/wip/lead-vjsign.lean` 的 `exists_nJ_vJ_signed` 所「**选**」的 `0 < det p vJ`
其实**没有自由度**：它被 `rec_vJ` 定死。⟹ 上一轮 §7 的分叉不是「两种约定二选一」，
是「一边已被原文定死」。 -/
theorem det_p_vJ_pos_of_chain_fields {A : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ}
    {nJ nℓ vl vJ p : ℤ × ℤ} {cz k : ℤ} {c : ℕ}
    (hnJvJ : dot nJ vJ = 0) (hnJp : dot nJ p ≠ 0) (hvJne : vJ ≠ 0)
    (hvl : vl ≠ 0) (hc : 0 < c) (hp : p = -(c : ℤ) • vl)
    (hperp : dot nℓ vl = 0) (hnlvl : 0 < det nℓ vl)
    (hexh : Exhausts A nℓ cz)
    (hne : (⋃ i, hatOf A kk vl i).Nonempty)
    (hrec : ∀ g ∈ (⋃ i, hatOf A kk vl i), g + vJ ∈ ⋃ i, hatOf A kk vl i)
    (hnLk : det p vJ • ((-p.2 : ℤ), p.1) = k • nℓ) :
    0 < det p vJ :=
  det_p_vJ_pos_of_k_pos_lside hvl hc hp hnlvl hnLk
    (k_pos_of_recvJ_lside hperp hexh hne hrec hnLk
      (det_p_vJ_ne_of_fields hnJvJ hnJp hvJne))

/-- ⭐⭐⭐⭐⭐ **分叉落地：链上 binder ⟹ `hattain` 为假。**

这是上一轮 `LeafAShellAttain` §7 的 `not_hattain_of_vjsign_choice` 与本文件 §5 的合成。
`0 < det p vJ` 那一条前提被 `det_p_vJ_pos_of_chain_fields` 顶掉，于是整条不再依赖任何
「符号选择」。

⚠ **记账边界（逐条，不许压成一句）**：

1. 这**不是**对 `shellEnv` 的反驳。`shellEnv` 是另一条字段，本文件一个字都没碰。
   被否掉的是 `hattain`（`shellEnv_of_faceSeg_hD` 的那条 binder，
   `tmp/wip/lane-leafa-shell-shellenv.lean` §50）。
2. `hv` / `hw` / `hm` / `hmpos` / `he` 五条仍是 binder，逐条出处见
   `LeafAShellAttain` §7 的 docstring；本文件没有替它们找生产者。
   特别是 `hm : vJ1 = m • vl` 的 `0 < m`：那是 §7 的前提，**本轮没有新证据**。
3. `0 < D`（`hD`）由 `CyclicOrderDPos.D_pos_of_window_of_transversal` 给（env-refute 报，
   ⚠ 我复核了它的**签名与量词**——不含 `NormalCycle`、结论逐字是 `0 < det nprevJ νJ1`
   ——但**没有**复核它的证明体）。
4. 不主张 `hattain` 所在的整条 shell 路线该被砍：那是集成者的裁决。 -/
theorem not_hattain_of_chain_fields {A : ℕ → Set (ℤ × ℤ)} {R : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ}
    {nJ nℓ vl vJ p nprevJ J νJ1 vJ1 w : ℤ × ℤ} {cz k kJ m : ℤ} {c : ℕ} {i₀ : ℕ}
    -- ℓ 侧：三条字段 ＋ `rec_vJ` ＋ `Exhausts` ＋ `hp_neg` ＋ `hpartner`
    (hnJvJ : dot nJ vJ = 0) (hnJp : dot nJ p ≠ 0) (hvJne : vJ ≠ 0)
    (hvl : vl ≠ 0) (hc : 0 < c) (hp : p = -(c : ℤ) • vl)
    (hperp : dot nℓ vl = 0) (hnlvl : 0 < det nℓ vl)
    (hexh : Exhausts A nℓ cz)
    (hne : (⋃ i, hatOf A kk vl i).Nonempty)
    (hrecL : ∀ g ∈ (⋃ i, hatOf A kk vl i), g + vJ ∈ ⋃ i, hatOf A kk vl i)
    (hnLk : det p vJ • ((-p.2 : ℤ), p.1) = k • nℓ)
    -- shell 侧：`LeafAShellAttain` §7 的 binder
    (hv : vJ1 = dir nprevJ) (hw : w = -(dir νJ1))
    (hm : vJ1 = m • vl) (hmpos : 0 < m)
    (hvJdef : vJ = kJ • dir J)
    (hD : 0 < det nprevJ νJ1) (he : 0 < det nprevJ J)
    (hrec : ∀ g ∈ (⋃ j, R j), g + vJ ∈ ⋃ j, R j) :
    ¬ (∀ i, i₀ ≤ i → ∀ n : ℤ × ℤ, 0 < dot n w → dot n vJ1 ≤ 0 →
        ∃ z ∈ R i, ∀ g ∈ (⋃ j, R j), dot n g ≤ dot n z) :=
  Nivat.LaneLeafAShellAttain.not_hattain_of_vjsign_choice
    hv hw hm hmpos hp hvJdef hD he
    (det_p_vJ_pos_of_chain_fields hnJvJ hnJp hvJne hvl hc hp hperp hnlvl hexh hne hrecL hnLk)
    hrec

/-! ## §6 非空真见证（§41） -/

/-- **本文件不是空真。**（1) `det p vJ ≠ 0` 那三条字段可同时兑现；
(2) `0 < k ⟺ 0 < det p vJ` 的正反两档都有数值实例；
(3) `k < 0` 的那一档也确实存在（把 `hp_neg` 的 `c` 换号即可），所以 §4 的等价不是恒真。

台架：`vl = (0,1)`、`c = 1`、`p = (0,-1)`、`nℓ = (1,0)`、`nJ = (1,0)`。
`vJ = (1,0)` 给 `det p vJ = 1 > 0`（合规档）；`vJ = (-1,0)` 给 `det p vJ = -1 < 0`（禁档）。 -/
theorem rigLsideFork :
    -- `hp_neg` 兑现
    (-(1 : ℤ)) • ((0 : ℤ), (1 : ℤ)) = ((0 : ℤ), (-1 : ℤ)) ∧
    -- `hpartner` 的两条
    dot ((1 : ℤ), (0 : ℤ)) ((0 : ℤ), (1 : ℤ)) = 0 ∧
    0 < det ((1 : ℤ), (0 : ℤ)) ((0 : ℤ), (1 : ℤ)) ∧
    -- 合规档：`vJ = (1,0)`，三条字段兑现且 `det p vJ = 1 > 0`
    dot ((1 : ℤ), (0 : ℤ)) ((0 : ℤ), (1 : ℤ)) = 0 ∧
    dot ((0 : ℤ), (1 : ℤ)) ((0 : ℤ), (-1 : ℤ)) ≠ 0 ∧
    det ((0 : ℤ), (-1 : ℤ)) ((1 : ℤ), (0 : ℤ)) = 1 ∧
    -- 禁档：`vJ = (-1,0)` 给 `det p vJ = -1 < 0`，且 `⟪nℓ,vJ⟫ = -1 < 0`（`rec_vJ` 断了）
    det ((0 : ℤ), (-1 : ℤ)) ((-1 : ℤ), (0 : ℤ)) = -1 ∧
    dot ((1 : ℤ), (0 : ℤ)) ((-1 : ℤ), (0 : ℤ)) = -1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [dot, det, Prod.ext_iff]

/-- `det p vJ = 0` 一档确实可达（若丢掉三条字段）：`vJ = (0,1)` 给 `det p vJ = 0`，
`n_ℓ = 0`，`⟪nℓ,v_J⟫ = 0`。配 `not_primitive_zero_lside` 看「对象退化」。 -/
theorem rigLsideDegenerate :
    det ((0 : ℤ), (-1 : ℤ)) ((0 : ℤ), (1 : ℤ)) = 0 ∧
    dot ((1 : ℤ), (0 : ℤ)) ((0 : ℤ), (1 : ℤ)) = 0 ∧
    -- 这一档 `dot nJ p = 0`，正是 `dot_nJ_p` 排除的那一条
    dot ((0 : ℤ), (1 : ℤ)) ((0 : ℤ), (-1 : ℤ)) ≠ 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [dot, det]

/-! ## §8 `hmpos : 0 < m` 承的重——**不能靠分档消掉**

`not_hattain_of_chain_fields` 的结论是**有条件的**：`0 < det p v_J` 那一半我已从链上字段推出，
但 `hv` / `hw` / `hm` / `hmpos` / `he` 仍是 binder，其中 `hmpos : 0 < m` **零产者**（本 lane 的
老债）。本节回答「能不能对 `m` 的符号分档、把 `hmpos` 消掉」——**不能**，而且不能的方式可判：

`m` 的符号与 `⟪vl,J⟫` 的符号被 `m * ⟪vl,J⟫ = det ν_{J−1} J`（`LeafAShellAttain` 的
`dot_vl_J_pos_of_collinear` 证明体第一步）锁成**同号**；而 `0 < det p v_J` 又把 `k_J` 与
`⟪vl,J⟫` 锁成**反号**。⟹ **`m` 翻号 ⟹ `k_J` 翻号**，`not_hattain_of_k_neg` 就不适用了。

⟹ `m < 0` 是**真逃生口**，不是技术困难。要让分叉结论无条件，必须**产** `0 < m`。

⚠ 本节**不**主张 `m < 0` 时 `hattain` 为真——只主张那一支的**反驳路线关闭**。
-/

/-- `m ≠ 0` 是免费的：`m * ⟪vl,J⟫ = det ν_{J−1} J > 0`，不需要任何符号前提。 -/
theorem m_ne_zero_of_dot_vl_J {nprevJ J vJ1 vl : ℤ × ℤ} {m : ℤ}
    (hv : vJ1 = dir nprevJ) (hm : vJ1 = m • vl)
    (he : 0 < det nprevJ J) : m ≠ 0 := by
  intro h0
  have h1 : dot vJ1 J = m * dot vl J :=
    by rw [hm, Nivat.LaneLeafAShellAttain.dot_zsmul_left_attain]
  have h2 : dot vJ1 J = det nprevJ J :=
    by rw [hv, Nivat.LaneLeafAShellAttain.dot_dir_left_eq_det]
  rw [h0, zero_mul] at h1
  rw [h1] at h2
  linarith

/-- **`dot_vl_J_pos_of_collinear` 的镜像档**：`m < 0` ⟹ `⟪vl,J⟫ < 0`。
同一条恒等式 `m * ⟪vl,J⟫ = det ν_{J−1} J`，只换 `m` 的符号。 -/
theorem dot_vl_J_neg_of_m_neg {nprevJ J vJ1 vl : ℤ × ℤ} {m : ℤ}
    (hv : vJ1 = dir nprevJ) (hm : vJ1 = m • vl) (hmneg : m < 0)
    (he : 0 < det nprevJ J) : dot vl J < 0 := by
  have h1 : dot vJ1 J = m * dot vl J :=
    by rw [hm, Nivat.LaneLeafAShellAttain.dot_zsmul_left_attain]
  have h2 : dot vJ1 J = det nprevJ J :=
    by rw [hv, Nivat.LaneLeafAShellAttain.dot_dir_left_eq_det]
  have hkey : m * dot vl J = det nprevJ J := by rw [← h1, h2]
  by_contra hcon
  push_neg at hcon
  nlinarith [mul_nonneg (neg_nonneg.mpr hmneg.le) hcon]

/-- **`k_neg_of_det_p_vJ_pos` 的镜像档**：`m < 0` 之下，同一个 `0 < det p v_J`
给出的是 **`0 < k_J`**，不是 `k_J < 0` ⟹ §6 的 `not_hattain_of_k_neg` 不适用。
`hp_neg` 的 `0 < c` 这一档也不需要（只用 `0 ≤ (c : ℤ)`）。 -/
theorem kJ_pos_of_det_p_vJ_pos_of_m_neg {nprevJ J vJ1 vl p vJ : ℤ × ℤ} {kJ m : ℤ} {c : ℕ}
    (hv : vJ1 = dir nprevJ) (hm : vJ1 = m • vl) (hmneg : m < 0)
    (he : 0 < det nprevJ J)
    (hp : p = -(c : ℤ) • vl) (hvJ : vJ = kJ • dir J)
    (hsign : 0 < det p vJ) : 0 < kJ := by
  have hvlJ : dot vl J < 0 := dot_vl_J_neg_of_m_neg hv hm hmneg he
  have hdet : det p vJ = -((c : ℤ) * (kJ * dot vl J)) := by
    subst hp
    subst hvJ
    simp only [det, dot, dir, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  rw [hdet] at hsign
  by_contra hcon
  push_neg at hcon
  have hc0 : (0 : ℤ) ≤ (c : ℤ) := Int.natCast_nonneg c
  nlinarith [mul_nonneg hc0 (mul_nonneg (neg_nonneg.mpr hcon) (neg_nonneg.mpr hvlJ.le))]

/-- ⭐⭐ **合成：`m` 的符号就是分叉结论的开关，`hmpos` 分档消不掉。**
同一组前提（含 `0 < det p v_J`，在 `det_p_vJ_pos_of_chain_fields` 里已由链上字段推出）之下：
`0 < m` 给 `k_J < 0`（§7 走得通，`hattain` 为假）、`m < 0` 给 `0 < k_J`（§7 走不通），
且 `m ≠ 0` 免费。⟹ 要把 `not_hattain_of_chain_fields` 变成无条件，只有一条路：**产** `0 < m`。 -/
theorem fork_refutation_needs_m_pos {nprevJ J vJ1 vl p vJ : ℤ × ℤ} {kJ m : ℤ} {c : ℕ}
    (hv : vJ1 = dir nprevJ) (hm : vJ1 = m • vl)
    (he : 0 < det nprevJ J)
    (hp : p = -(c : ℤ) • vl) (hvJ : vJ = kJ • dir J)
    (hsign : 0 < det p vJ) :
    m ≠ 0 ∧ (0 < m → kJ < 0) ∧ (m < 0 → 0 < kJ) :=
  ⟨m_ne_zero_of_dot_vl_J hv hm he,
   fun hmpos =>
     Nivat.LaneLeafAShellAttain.k_neg_of_det_p_vJ_pos hv hm hmpos he hp hvJ hsign,
   fun hmneg => kJ_pos_of_det_p_vJ_pos_of_m_neg hv hm hmneg he hp hvJ hsign⟩

/-- **数值台架（§41 / 硬规矩 6），`m < 0` 那一档非空真。**  一组同时兑现的值：
`ν_{J−1} = (1,0)`、`vl = (0,−1)`、`m = −1` 故 `v_{J+1} = m • vl = (0,1) = dir ν_{J−1}`、
`J = (1,1)` 故 `e = det ν_{J−1} J = 1 > 0`、`⟪vl,J⟫ = −1 < 0`、
`c = 1` 故 `p = (0,1)`、`k_J = 1` 故 `v_J = dir J = (−1,1)`、`det p v_J = 1 > 0`。
⟹ `m < 0` 档的前提组可以同时兑现，兑现之后 `k_J = 1 > 0`（不是 `< 0`）。 -/
theorem rigMsignNeg :
    dir ((1 : ℤ), (0 : ℤ)) = ((0 : ℤ), (1 : ℤ)) ∧
    (-(1 : ℤ)) • ((0 : ℤ), (-1 : ℤ)) = ((0 : ℤ), (1 : ℤ)) ∧
    0 < det ((1 : ℤ), (0 : ℤ)) ((1 : ℤ), (1 : ℤ)) ∧
    dot ((0 : ℤ), (-1 : ℤ)) ((1 : ℤ), (1 : ℤ)) = -1 ∧
    dir ((1 : ℤ), (1 : ℤ)) = ((-1 : ℤ), (1 : ℤ)) ∧
    (-((1 : ℕ) : ℤ)) • ((0 : ℤ), (-1 : ℤ)) = ((0 : ℤ), (1 : ℤ)) ∧
    0 < det ((0 : ℤ), (1 : ℤ)) ((-1 : ℤ), (1 : ℤ)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [dot, det, dir, Prod.ext_iff]

/-! ## §8  `m` 的符号：原文**固定**了它，但固定成一个**二选一**（ccw / cw），不是 `0 < m`

§7 的 `fork_refutation_needs_m_pos` 把整条 `ℓ` 侧分叉压到一条 binder 上：`0 < m`。
本节回答它，答案分三层，**第三层是订正前两层的**。

⛔⛔ **先读 §8c 再读 §8a/§8b。** §8a/§8b 的**定理**全部为真且照常可用（它们对任意满足
`hvl : vl = dir ℓ` 的 `ℓ` 成立），错的是「链上的 `ℓ` 是谁」这个**实例化**判断。

### §8a 原文确实固定了朝向比特（硬规矩 5 不适用：`0 < m` 不是我们加的量词）

`b3_colle2.txt:424`（同句复述于 `:541`、`:764`）：

> "Suppose `ℓ_1, …, ℓ_{2m} ⊂ ℝ²` is an enumeration of the oriented lines through the origin
> parallels to the edges of `S_φ` **where the edge parallel to `ℓ_{i+1}` is a successor of the
> edge parallel to `ℓ_i`** and indices are taken modulo `2m`."

配 `b3_colle2.txt:255`（「the boundary of `conv(S)` is positively oriented」，据此每条边有
良定义的 successor / predecessor）。**这是全文唯一一处固定 `ℓ_j` 之间相对朝向的句子，
而它固定了全部。** 随之两条原文事实：`:432` 给 item (i) 的 `ι+1 ≤ J ≤ ι+m−1`、`:450` 给
item (ii) 的 `ι+m+1 ≤ J ≤ ι+2m−1`；`:740` 逐字说 `w_i` 与 `w_{i+m}` antiparallel，
即 `v_{ℓ_{i+m}} = −v_{ℓ_i}`。⟹ `v_{ℓ_{J−1}} ∥ v_{ℓ_ι}` 在 item (i) 下只有 `J−1 = ι`
（`m = +1`），在 item (ii) 下只有 `J−1 = ι+m`（`m = −1`）。**朝向比特被「走哪一项」固定，
两项符号相反**；`:936` 说 item (ii) 靠把 `ℓ̂_ι := −ℓ_ι` 重标号归约到 item (i)。

⚠ **一名多物**（已记 `NOTATION.md`）：本仓字段 `vJ1` 是原文的 `v_{ℓ_{J−1}}`（`:440`，**加**号），
**不是** `v_{ℓ_{J+1}}`；后者全文只出现一次，在 `:518`，带**减**号，对应的是 (B) 栈的 `w`。

### §8b Lean 侧不用数模 `2m` 指标就能拿到同一件事

产者 `LeafAJSelect.exists_nprevJ_vJ1` 的输出析取 `nprevJ = ℓ ∨ nprevJ ∈ Arc … ℓ J` 已经**就是**
那条约定的 Lean 形态，而 `Nivat.PolyChainSum.Arc` 的定义里带着 `0 < det ν₀ ν`——
**弧内那一支自带「不共线」**。于是 `hm : vJ1 = m • vl` 把弧内支直接打空，只剩相等支。

⚠ 结论**不依赖手性**：`not_collinear_of_det_ne` 只用 `det ℓ nprevJ ≠ 0`。蓝图记着 (u3)
报假的全部重量压在「positively oriented ＝ 逆时针」这条**外来**约定上（全文 grep
`counterclockwise/clockwise/ccw/cw` 零命中，lane-hole3-cone 实测）；本节刻意避开它。

### §8c ⛔ 订正：链上的 `ℓ`-binder 取的是 `-nℓ`，于是 ccw 支给 `m = −1`

§8b 的合成里把 `ℓ`-binder 默认读成 `nℓ`。**读错了。** 主仓**代码**（不是注释）给出反证：
`ShellSubStrip.dot_nl_vJ1_nonneg` 的 binder 逐字是
`(hor : nprevJ = -nℓ ∨ nprevJ ∈ Arc (Sphi.finite_toSet) (-nℓ) J)`，其 docstring 也写明
「`LeafAJSelect.exists_nprevJ_vJ1` with its `ℓ`-binder at `-nℓ`」。理由是 `E 𝒮_φ` 装**外**法向
而 `Â_∞` 在 `+nℓ` 一侧，故 `ℓ`-面的外法向是 `−nℓ`。

⟹ 空弧支给 `nprevJ = -nℓ`，ccw 产者 `vJ1 = dir nprevJ = -dir nℓ = -vl`，即 **`m = -1`**。
但这**不是**「`hmpos` 为假」的终局，因为主仓有**两个**符号相反的产者
（`LeafAJSelect.exists_nprevJ_vJ1` 出 `vJ1 = dir nprevJ`；`LeafACwBranch` 的
`exists_nprevJ_vJ1_cw` 出 `vJ1 = -dir nprevJ`，且 `LeafACwBranch` 写明两条等式
「CANNOT both be」同时成立）。⟹ **`m` 的符号 ＝ ccw/cw 分支比特**，与 §8a 从原文读出的
item (i)/(ii) 二选一逐字同构——`:936` 的 `ℓ̂_ι := −ℓ_ι` 正是 Lean 侧这同一次取负。

**⟹ `hmpos : 0 < m` 的账目状态**：不是自由量词（原文固定了比特），也不是无条件定理
（`m_eq_neg_one_or_one`）；它在两支里恰好一支成立。**哪一支由 `hsweep : dot nJ vJ1 < 0`
选定，这一格本节没有证，是欠账，也是 `hmpos` 现在的全部重量所在。**

⚠ 另有一格：`hvl : vl = dir nℓ` 仍是本节各条的**前提**。它可由 `hpartner` 的
`nℓ ≠ 0` / `Prim nℓ` / `Primitive vl` / `dot nℓ vl = 0` 经 `ShellRegionJ.dir_nℓ_eq_or_neg_vl`
取到析取，再由本节 `vl_eq_dir_of_neg_branch` 用 `hpartner` 的 `0 < det nℓ vl` 掐掉负支。
`dir_nℓ_eq_or_neg_vl` 我只读了签名、**未读证明体**。 -/

/-- 旋转 90° 保 `det`。（`HsuppRoomCone.det_dir_dir` 同形；此处另起名以免 §61 撞名。） -/
theorem mpos_det_dir_dir (a b : ℤ × ℤ) : det (dir a) (dir b) = det a b := by
  simp only [det, dir]
  ring

/-- `ℓ ≠ 0 ⟹ dir ℓ ≠ 0`。 -/
theorem mpos_dir_ne_zero {ℓ : ℤ × ℤ} (h : ℓ ≠ 0) : dir ℓ ≠ 0 := by
  intro h0
  apply h
  rw [Prod.ext_iff] at h0 ⊢
  simp only [dir, Prod.fst_zero, Prod.snd_zero] at h0 ⊢
  omega

/-- `dir (-n) = -dir n`。（`ShellSubStrip.dir_neg` 同形，此处另起名避撞。） -/
theorem mpos_dir_neg (n : ℤ × ℤ) : dir (-n) = -dir n := by
  simp only [dir, Prod.fst_neg, Prod.snd_neg, Prod.neg_mk, neg_neg]

/-- `v ≠ 0` 且 `v = m • v` ⟹ `m = 1`。 -/
theorem mpos_eq_one_of_smul_self {v : ℤ × ℤ} {m : ℤ} (hv : v ≠ 0) (h : v = m • v) :
    m = 1 := by
  have hcomp : v.1 ≠ 0 ∨ v.2 ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hv (Prod.ext (by simpa using hc.1) (by simpa using hc.2))
  rw [Prod.ext_iff] at h
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h
  rcases hcomp with h1 | h2
  · have : (m - 1) * v.1 = 0 := by linarith [h.1]
    rcases mul_eq_zero.mp this with hz | hz
    · omega
    · exact absurd hz h1
  · have : (m - 1) * v.2 = 0 := by linarith [h.2]
    rcases mul_eq_zero.mp this with hz | hz
    · omega
    · exact absurd hz h2

/-- `v ≠ 0` 且 `a • v = b • v` ⟹ `a = b`。 -/
theorem mpos_smul_left_cancel {v : ℤ × ℤ} {a b : ℤ} (hv : v ≠ 0) (h : a • v = b • v) :
    a = b := by
  have hcomp : v.1 ≠ 0 ∨ v.2 ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hv (Prod.ext (by simpa using hc.1) (by simpa using hc.2))
  rw [Prod.ext_iff] at h
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h
  rcases hcomp with h1 | h2
  · have : (a - b) * v.1 = 0 := by linarith [h.1]
    rcases mul_eq_zero.mp this with hz | hz
    · omega
    · exact absurd hz h1
  · have : (a - b) * v.2 = 0 := by linarith [h.2]
    rcases mul_eq_zero.mp this with hz | hz
    · omega
    · exact absurd hz h2

/-- **弧内分支是空的。** `0 < det ℓ nprevJ`（`Arc` 定义里的左合取项）⟹ `vl` 与 `vJ1`
不共线 ⟹ `hm : vJ1 = m • vl` 不可能成立。 -/
theorem not_collinear_of_arc {ℓ nprevJ vl vJ1 : ℤ × ℤ} {m : ℤ}
    (hvl : vl = dir ℓ) (hv : vJ1 = dir nprevJ) (hm : vJ1 = m • vl)
    (harc : 0 < det ℓ nprevJ) : False := by
  have h1 : det vl vJ1 = det ℓ nprevJ := by
    rw [hvl, hv]; exact mpos_det_dir_dir ℓ nprevJ
  have h2 : det vl vJ1 = 0 := by
    rw [hm]
    simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  rw [h2] at h1
  omega

/-- **手性无关版的弧内分支排除**：只用 `det ℓ nprevJ ≠ 0`，扇序约定翻号也照样成立。 -/
theorem not_collinear_of_det_ne {ℓ nprevJ vl vJ1 : ℤ × ℤ} {m : ℤ}
    (hvl : vl = dir ℓ) (hv : vJ1 = dir nprevJ) (hm : vJ1 = m • vl)
    (hdne : det ℓ nprevJ ≠ 0) : False := by
  apply hdne
  have h1 : det vl vJ1 = det ℓ nprevJ := by
    rw [hvl, hv]; exact mpos_det_dir_dir ℓ nprevJ
  have h2 : det vl vJ1 = 0 := by
    rw [hm]
    simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  rw [h2] at h1
  exact h1.symm

/-- **相等分支给 `m = 1`**（`ℓ`-binder 取 `ℓ` 本身时）。 -/
theorem m_eq_one_of_pred_eq {ℓ nprevJ vl vJ1 : ℤ × ℤ} {m : ℤ}
    (hvl : vl = dir ℓ) (hv : vJ1 = dir nprevJ) (hm : vJ1 = m • vl)
    (hℓne : ℓ ≠ 0) (heq : nprevJ = ℓ) : m = 1 := by
  have hvlne : vl ≠ 0 := by rw [hvl]; exact mpos_dir_ne_zero hℓne
  have hself : vl = m • vl := by rw [← hm, hv, heq, ← hvl]
  exact mpos_eq_one_of_smul_self hvlne hself

/-- §8b 的合成：`ℓ`-binder 取 `ℓ` 本身时得 `m = 1`。
⛔ 链上**不是**这个实例化（§8c），本条保留是因为它对任意 `ℓ` 为真、且是 §8c 两条的母形。 -/
theorem m_eq_one_of_fan_pred {ℓ nprevJ vl vJ1 : ℤ × ℤ} {m : ℤ}
    (hvl : vl = dir ℓ) (hv : vJ1 = dir nprevJ) (hm : vJ1 = m • vl)
    (hℓne : ℓ ≠ 0) (hor : nprevJ = ℓ ∨ 0 < det ℓ nprevJ) : m = 1 := by
  rcases hor with heq | harc
  · exact m_eq_one_of_pred_eq hvl hv hm hℓne heq
  · exact (not_collinear_of_arc hvl hv hm harc).elim

/-- 同上，弱化到 `fork_refutation_needs_m_pos` 的 `0 < m` 形状。 -/
theorem m_pos_of_fan_pred {ℓ nprevJ vl vJ1 : ℤ × ℤ} {m : ℤ}
    (hvl : vl = dir ℓ) (hv : vJ1 = dir nprevJ) (hm : vJ1 = m • vl)
    (hℓne : ℓ ≠ 0) (hor : nprevJ = ℓ ∨ 0 < det ℓ nprevJ) : 0 < m := by
  rw [m_eq_one_of_fan_pred hvl hv hm hℓne hor]
  norm_num

/-- 同上的手性无关版：右支只要求 `det ℓ nprevJ ≠ 0`。 -/
theorem m_pos_of_pred_or_det_ne {ℓ nprevJ vl vJ1 : ℤ × ℤ} {m : ℤ}
    (hvl : vl = dir ℓ) (hv : vJ1 = dir nprevJ) (hm : vJ1 = m • vl)
    (hℓne : ℓ ≠ 0) (hor : nprevJ = ℓ ∨ det ℓ nprevJ ≠ 0) : m = 1 ∧ 0 < m := by
  have h1 : m = 1 := by
    rcases hor with heq | hdne
    · exact m_eq_one_of_pred_eq hvl hv hm hℓne heq
    · exact (not_collinear_of_det_ne hvl hv hm hdne).elim
  exact ⟨h1, by rw [h1]; norm_num⟩

/-- ⭐⭐ **ccw 支，链上真实实例化（`ℓ`-binder 在 `-nℓ`）：`m = −1`。** -/
theorem m_eq_neg_one_of_ccw_instantiation {nℓ nprevJ vl vJ1 : ℤ × ℤ} {m : ℤ}
    (hvl : vl = dir nℓ) (hv : vJ1 = dir nprevJ) (hm : vJ1 = m • vl)
    (hnℓne : nℓ ≠ 0) (hor : nprevJ = -nℓ ∨ det nℓ nprevJ ≠ 0) : m = -1 := by
  have hvlne : vl ≠ 0 := by rw [hvl]; exact mpos_dir_ne_zero hnℓne
  rcases hor with heq | hdne
  · have hneg : vJ1 = (-1 : ℤ) • vl := by
      rw [hv, heq, mpos_dir_neg, hvl, neg_one_zsmul]
    rw [hm] at hneg
    exact mpos_smul_left_cancel hvlne hneg
  · exact (not_collinear_of_det_ne hvl hv hm hdne).elim

/-- ⭐⭐ **cw 支，同一实例化：`m = +1`。** 产者是 `LeafACwBranch` 的
`exists_nprevJ_vJ1_cw`，出 `vJ1 = -dir nprevJ`。 -/
theorem m_eq_one_of_cw_instantiation {nℓ nprevJ vl vJ1 : ℤ × ℤ} {m : ℤ}
    (hvl : vl = dir nℓ) (hv : vJ1 = -dir nprevJ) (hm : vJ1 = m • vl)
    (hnℓne : nℓ ≠ 0) (hor : nprevJ = -nℓ ∨ det nℓ nprevJ ≠ 0) : m = 1 := by
  have hvlne : vl ≠ 0 := by rw [hvl]; exact mpos_dir_ne_zero hnℓne
  rcases hor with heq | hdne
  · have hone : vJ1 = (1 : ℤ) • vl := by
      rw [hv, heq, mpos_dir_neg, neg_neg, hvl, one_zsmul]
    rw [hm] at hone
    exact mpos_smul_left_cancel hvlne hone
  · exfalso
    apply hdne
    have h1 : det vl vJ1 = 0 := by
      rw [hm]
      simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      ring
    have h2 : det vl vJ1 = -det nℓ nprevJ := by
      rw [hvl, hv, ← mpos_dir_neg, mpos_det_dir_dir]
      simp only [det, Prod.fst_neg, Prod.snd_neg]
      ring
    omega

/-- ⭐⭐ **两支的合成，就是那个二选一。** `hmpos` 的全部剩余重量在于：`hsweep` 选哪一支。 -/
theorem m_eq_neg_one_or_one {nℓ nprevJ vl vJ1 : ℤ × ℤ} {m : ℤ}
    (hvl : vl = dir nℓ) (hm : vJ1 = m • vl) (hnℓne : nℓ ≠ 0)
    (hccw_or_cw : vJ1 = dir nprevJ ∨ vJ1 = -dir nprevJ)
    (hor : nprevJ = -nℓ ∨ det nℓ nprevJ ≠ 0) : m = -1 ∨ m = 1 := by
  rcases hccw_or_cw with hv | hv
  · exact Or.inl (m_eq_neg_one_of_ccw_instantiation hvl hv hm hnℓne hor)
  · exact Or.inr (m_eq_one_of_cw_instantiation hvl hv hm hnℓne hor)

/-- **`hvl` 那一格的下半截**：用 `hpartner` 的 `0 < det nℓ vl` 掐掉 `dir nℓ = -vl` 支。
配 `ShellRegionJ.dir_nℓ_eq_or_neg_vl` 得 `vl = dir nℓ`。 -/
theorem vl_eq_dir_of_neg_branch {nℓ vl : ℤ × ℤ}
    (hor : dir nℓ = vl ∨ dir nℓ = -vl) (hdet : 0 < det nℓ vl) : vl = dir nℓ := by
  rcases hor with h | h
  · exact h.symm
  · exfalso
    have hsq : det nℓ (dir nℓ) = nℓ.1 * nℓ.1 + nℓ.2 * nℓ.2 := by
      simp only [det, dir]; ring
    rw [h] at hsq
    have hneg : det nℓ (-vl) = -det nℓ vl := by
      simp only [det, Prod.fst_neg, Prod.snd_neg]; ring
    rw [hneg] at hsq
    nlinarith [mul_self_nonneg nℓ.1, mul_self_nonneg nℓ.2]

/-- **数值台架（硬规矩 6），相等支。** `ℓ = (1,0)`、`J = (0,1)`、`vl = dir ℓ = (0,1)`，
`nprevJ = ℓ` ⟹ `vJ1 = (0,1) = 1 • vl`。 -/
theorem rigMposEq :
    (0 : ℤ) < det ((1:ℤ),(0:ℤ)) ((0:ℤ),(1:ℤ)) ∧
    dir ((1:ℤ),(0:ℤ)) = ((0:ℤ),(1:ℤ)) ∧
    ((0:ℤ),(1:ℤ)) = (1 : ℤ) • ((0:ℤ),(1:ℤ)) := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [det, dir, Prod.ext_iff]

/-- **数值台架，弧内支非空真**：`nprevJ = (1,1)` 给 `det ℓ nprevJ = 1 > 0`，
而 `dir nprevJ = (-1,1)` 不是 `vl = (0,1)` 的任何整数倍。 -/
theorem rigMposArc :
    (0 : ℤ) < det ((1:ℤ),(0:ℤ)) ((1:ℤ),(1:ℤ)) ∧
    ∀ m : ℤ, dir ((1:ℤ),(1:ℤ)) ≠ m • ((0:ℤ),(1:ℤ)) := by
  refine ⟨by norm_num [det], ?_⟩
  intro m h
  rw [Prod.ext_iff] at h
  simp only [dir, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h
  omega

/-! ### §8d 把「`hsweep` 选哪一支」化成「`dot nJ vl` 的符号」——内核版，不是散文

`hm : vJ1 = m • vl` 给 `dot nJ vJ1 = m * dot nJ vl`，于是 `hsweep : dot nJ vJ1 < 0`
**逐字就是**「`m` 与 `dot nJ vl` 异号」。⟹ §8c 末尾那格欠账有一个完全等价的形式：

> **`0 < m` ⟺ `dot nJ vl < 0`**（在 `hm` ＋ `hsweep` 之下，`m_pos_iff_dot_nJ_vl_neg`）。

⚠ **给 `GcdCollapse` 一侧的接口后果，请当成一条现货约束而不是我的意见**：
`GcdCollapse.collapse` 的证明体里 `hmpos : 0 < m` 是**承重**的——它正是用来在
`dot nJ vl = 1` 那一支上撞 `hsweep` 的。⟹ 若链上走的是 ccw 实例化（§8c 的 `m = -1`），
`collapse` 的结论**翻号**：`gcd(d, e) = 1` 那时逼出的是 `dot nJ vl = +1`，不是 `-1`。
`dot_nJ_vl_pos_of_ccw_instantiation` 是这一句的内核形式。本节**不**主张链上就是 ccw
（那正是欠的那一格），只主张两者不能同时按现在的写法成立。 -/

/-- `vJ1 = m • vl ⟹ dot nJ vJ1 = m * dot nJ vl`。 -/
theorem dot_nJ_vJ1_eq_mul {nJ vl vJ1 : ℤ × ℤ} {m : ℤ} (hm : vJ1 = m • vl) :
    dot nJ vJ1 = m * dot nJ vl := by
  rw [hm]
  simp only [dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- ⭐ **欠账的等价改写**：`hm` ＋ `hsweep` 之下，`0 < m` 与 `dot nJ vl < 0` 互为充要。 -/
theorem m_pos_iff_dot_nJ_vl_neg {nJ vl vJ1 : ℤ × ℤ} {m : ℤ}
    (hm : vJ1 = m • vl) (hsweep : dot nJ vJ1 < 0) :
    0 < m ↔ dot nJ vl < 0 := by
  have h : m * dot nJ vl < 0 := by rw [← dot_nJ_vJ1_eq_mul hm]; exact hsweep
  constructor
  · intro hmp
    by_contra hc
    push_neg at hc
    exact absurd h (not_lt.mpr (mul_nonneg hmp.le hc))
  · intro hd
    by_contra hc
    push_neg at hc
    have hnn : (0 : ℤ) ≤ (-m) * (-(dot nJ vl)) :=
      mul_nonneg (neg_nonneg.mpr hc) (neg_nonneg.mpr hd.le)
    nlinarith

/-- 同一件事的单向版：`m < 0` ⟹ `0 < dot nJ vl`。 -/
theorem dot_nJ_vl_pos_of_m_neg {nJ vl vJ1 : ℤ × ℤ} {m : ℤ}
    (hm : vJ1 = m • vl) (hsweep : dot nJ vJ1 < 0) (hmneg : m < 0) : 0 < dot nJ vl := by
  have h : m * dot nJ vl < 0 := by rw [← dot_nJ_vJ1_eq_mul hm]; exact hsweep
  by_contra hc
  push_neg at hc
  have hnn : (0 : ℤ) ≤ (-m) * (-(dot nJ vl)) :=
    mul_nonneg (neg_nonneg.mpr hmneg.le) (neg_nonneg.mpr hc)
  nlinarith

/-- ⭐⭐ **ccw 实例化下 `dot nJ vl` 为正**——与 `GcdCollapse.collapse` 结论里的
`dot nJ vl = -1` 相反。⟹ 「链上是 ccw」与「`collapse` 按现在的写法可用」二者至多一真。 -/
theorem dot_nJ_vl_pos_of_ccw_instantiation {nℓ nprevJ nJ vl vJ1 : ℤ × ℤ} {m : ℤ}
    (hvl : vl = dir nℓ) (hv : vJ1 = dir nprevJ) (hm : vJ1 = m • vl)
    (hnℓne : nℓ ≠ 0) (hor : nprevJ = -nℓ ∨ det nℓ nprevJ ≠ 0)
    (hsweep : dot nJ vJ1 < 0) : 0 < dot nJ vl :=
  dot_nJ_vl_pos_of_m_neg hm hsweep
    (by rw [m_eq_neg_one_of_ccw_instantiation hvl hv hm hnℓne hor]; norm_num)

/-! ### §8e ⭐ `hmpos` 闭合：`0 < m` 是链上现货的推论，**不需要**先裁 ccw/cw

§8d 把欠账化成「`dot nJ vl` 的符号」。本节把那个符号也从链上现货取出来，于是
`hmpos : 0 < m` 整条闭合，**且完全绕过 §8c 的 ccw/cw 二选一**。

机制与 §5 的 `dot_nl_vJ_nonneg_of_recvJ_lside` 是同一个：`Â_∞` 被 `hhp` 压在
`{cJ ≤ ⟪n_J,·⟫}` 里，而 `rec_p` 说 `p` 是 `Â_∞` 的退化方向 ⟹ 沿 `p` 迭代不能把
`⟪n_J,·⟫` 推到 `−∞` ⟹ `0 ≤ ⟪n_J,p⟫`；配 `dot_nJ_p : ⟪n_J,p⟫ ≠ 0` 得 `0 < ⟪n_J,p⟫`；
再由 `hp_neg : p = -c·v_ℓ` 与 `0 < c` 得 **`⟪n_J,v_ℓ⟫ < 0`**。

前提逐条的链上出处（全部是既有字段或既有 binder，**没有新量词**）：
* `hne` ← `ChainDataGeomParts.ahat_nonempty`（`ChainPartsFeed.lean`）。⚠ 这是**并集**非空，
  **不是** CORE-HOLES 常设纪律 #6 说「不是现货」的那条 `∀ i, (Âᵢ).Nonempty`。
* `hlb` ← 同结构的 `hhp` 字段（`∀ i, hatOf … ⊆ halfPlaneGE nJ cJ`）。⚠ **一名多物**：主仓有
  **两个** `halfPlaneGE`（`LatticeEdges` 与 `CyrKra224`），定义逐字相同（`{z | c ≤ dot n z}`，
  两处都读过）；本节把前提写成**已展开**的形式，于是两个定义下都能用
  `simpa [halfPlaneGE] using hhp i hi` 兑现，接线时不必先裁是哪一个。
* `rec_p` / `hdot_nJ_p` ← 同结构的 `rec_p` / `dot_nJ_p` 字段（`ChainDataGeom` 里也有同名两条）。
* `hc` / `hp_neg` ← `RegionSteps.exists_chainData` 的 binder `hp_neg`。
* `hsweep` ← `ShellRegionJ.hsweep_of_fan_adjacent`（主仓现货：`0 < det νJm1 J` ⟹
  `dot (-J) (dir νJm1) < 0`，配 `J = -nJ`）。
* `hm : vJ1 = m • vl` ← `LeafAShellAttain` 的共线裁决。

⛔ **随之而来的、必须报出的张力**：本节的 `dot nJ vl < 0` 与 §8c 的 ccw 实例化
（`nprevJ = -nℓ` ⟹ `m = -1`，经 `dot_nJ_vl_pos_of_ccw_instantiation` 给 `0 < dot nJ vl`）
**互相矛盾**，见 `not_ccw_instantiation_of_chain_stock`。两边都自称链上现货 ⟹ 至少有一边的
实例化读错了。本节**不裁**这件事，只把矛盾摆成一条内核定理。⚠ 注意
**`m_pos_of_chain_stock` 不依赖那条 `nprevJ = -nℓ`**，所以这个张力不削弱本节的结论。

⚠ §41：`not_ccw_instantiation_of_chain_stock` 是**条件**否定——我**没有**造出一个同时兑现
全部现货前提的见证，所以它主张的恰好是「这些不能同时成立」，不是「ccw 产者本身为假」。 -/

/-- `dot n (k • z) = k * dot n z`（一般形；§8d 的 `dot_nJ_vJ1_eq_mul` 是它的一个特例形状）。 -/
theorem mpos_dot_zsmul (n : ℤ × ℤ) (k : ℤ) (z : ℤ × ℤ) : dot n (k • z) = k * dot n z := by
  simp only [dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- 退化方向的迭代：`rec_q` ⟹ `g + j • q ∈ U` 对每个 `j : ℕ`。 -/
theorem mpos_rec_iter {U : Set (ℤ × ℤ)} {q : ℤ × ℤ}
    (rec_q : ∀ g ∈ U, g + q ∈ U) : ∀ (j : ℕ) (g : ℤ × ℤ), g ∈ U → g + (j : ℤ) • q ∈ U := by
  intro j
  induction j with
  | zero => intro g hg; simpa using hg
  | succ n ih =>
      intro g hg
      have h := rec_q _ (ih g hg)
      have heq : g + (n : ℤ) • q + q = g + ((n + 1 : ℕ) : ℤ) • q := by
        push_cast
        rw [add_smul, one_smul, add_assoc]
      rwa [heq] at h

/-- **`U` 非空 ＋ `⟪n,·⟫` 在 `U` 上有下界 ＋ `q` 是 `U` 的退化方向 ⟹ `0 ≤ ⟪n,q⟫`。**
沿 `q` 走 `N := (⟪n,g⟫ − c + 1).toNat` 步就越过下界。 -/
theorem dot_nonneg_of_rec {U : Set (ℤ × ℤ)} {q n : ℤ × ℤ} {c : ℤ}
    (hne : U.Nonempty) (hlb : ∀ g ∈ U, c ≤ dot n g)
    (rec_q : ∀ g ∈ U, g + q ∈ U) : 0 ≤ dot n q := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨g, hg⟩ := hne
  set N : ℕ := (dot n g - c + 1).toNat with hN
  have hmem := mpos_rec_iter rec_q N g hg
  have hlev : dot n (g + ((N : ℕ) : ℤ) • q) = dot n g + ((N : ℕ) : ℤ) * dot n q := by
    rw [dot_add, mpos_dot_zsmul]
  have hge := hlb _ hmem
  rw [hlev] at hge
  have hNge : dot n g - c + 1 ≤ ((N : ℕ) : ℤ) := by
    rw [hN]; exact Int.self_le_toNat _
  have hNnn : (0 : ℤ) ≤ ((N : ℕ) : ℤ) := Int.natCast_nonneg _
  have hd1 : dot n q ≤ -1 := by omega
  have hmul : ((N : ℕ) : ℤ) * dot n q ≤ ((N : ℕ) : ℤ) * (-1) :=
    mul_le_mul_of_nonneg_left hd1 hNnn
  linarith

/-- ⭐⭐⭐ **`dot nJ vl < 0` 是链上现货的推论，不是假设。**
`rec_p` ＋ `hhp` ＋ `ahat_nonempty` ＋ `dot_nJ_p` 给 `0 < ⟪n_J,p⟫`，`hp_neg` 把符号翻过去。 -/
theorem dot_nJ_vl_neg_of_rec_p {A : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ} {vl p nJ : ℤ × ℤ}
    {cJ : ℤ} {c : ℕ}
    (hne : (⋃ i, hatOf A kk vl i).Nonempty)
    (hlb : ∀ i, ∀ g ∈ hatOf A kk vl i, cJ ≤ dot nJ g)
    (rec_p : ∀ g ∈ ⋃ i, hatOf A kk vl i, g + p ∈ ⋃ i, hatOf A kk vl i)
    (hc : 0 < c) (hp_neg : p = -(c : ℤ) • vl)
    (hdot_nJ_p : dot nJ p ≠ 0) :
    dot nJ vl < 0 := by
  have hlb' : ∀ g ∈ ⋃ i, hatOf A kk vl i, cJ ≤ dot nJ g := by
    intro g hg
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hg
    exact hlb i g hi
  have h0 : 0 ≤ dot nJ p := dot_nonneg_of_rec hne hlb' rec_p
  have hpos : 0 < dot nJ p := lt_of_le_of_ne h0 (Ne.symm hdot_nJ_p)
  have hexp : dot nJ p = -(c : ℤ) * dot nJ vl := by rw [hp_neg, mpos_dot_zsmul]
  have hcpos : (0 : ℤ) < (c : ℤ) := by exact_mod_cast hc
  nlinarith [hpos, hexp, hcpos]

/-- ⭐⭐⭐⭐ **`hmpos : 0 < m` 闭合。** 前提全是链上既有字段 / binder，
**不含** ccw/cw 裁决、不含 `nprevJ` 与 `nℓ` 的任何关系。 -/
theorem m_pos_of_chain_stock {A : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ} {vl p nJ vJ1 : ℤ × ℤ}
    {cJ : ℤ} {c : ℕ} {m : ℤ}
    (hne : (⋃ i, hatOf A kk vl i).Nonempty)
    (hlb : ∀ i, ∀ g ∈ hatOf A kk vl i, cJ ≤ dot nJ g)
    (rec_p : ∀ g ∈ ⋃ i, hatOf A kk vl i, g + p ∈ ⋃ i, hatOf A kk vl i)
    (hc : 0 < c) (hp_neg : p = -(c : ℤ) • vl)
    (hdot_nJ_p : dot nJ p ≠ 0)
    (hm : vJ1 = m • vl) (hsweep : dot nJ vJ1 < 0) : 0 < m :=
  (m_pos_iff_dot_nJ_vl_neg hm hsweep).mpr
    (dot_nJ_vl_neg_of_rec_p hne hlb rec_p hc hp_neg hdot_nJ_p)

/-- ⛔ **张力的内核形**：在全部链上现货之下，ccw 产者的输出 `vJ1 = dir nprevJ` 配
`ℓ`-binder 取 `-nℓ`（§8c 的读法）**不可能**成立——它给 `0 < dot nJ vl`，而现货给 `< 0`。
⟹ 「ccw 产者在链上」与「`ℓ`-binder 在 `-nℓ`」二者至多一真。 -/
theorem not_ccw_instantiation_of_chain_stock {A : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ}
    {vl p nJ vJ1 nℓ nprevJ : ℤ × ℤ} {cJ : ℤ} {c : ℕ} {m : ℤ}
    (hne : (⋃ i, hatOf A kk vl i).Nonempty)
    (hlb : ∀ i, ∀ g ∈ hatOf A kk vl i, cJ ≤ dot nJ g)
    (rec_p : ∀ g ∈ ⋃ i, hatOf A kk vl i, g + p ∈ ⋃ i, hatOf A kk vl i)
    (hc : 0 < c) (hp_neg : p = -(c : ℤ) • vl)
    (hdot_nJ_p : dot nJ p ≠ 0)
    (hvl : vl = dir nℓ) (hv : vJ1 = dir nprevJ) (hm : vJ1 = m • vl)
    (hnℓne : nℓ ≠ 0) (hsweep : dot nJ vJ1 < 0) :
    ¬ (nprevJ = -nℓ ∨ det nℓ nprevJ ≠ 0) := by
  intro hor
  have hposv : 0 < dot nJ vl :=
    dot_nJ_vl_pos_of_ccw_instantiation hvl hv hm hnℓne hor hsweep
  have hnegv : dot nJ vl < 0 :=
    dot_nJ_vl_neg_of_rec_p hne hlb rec_p hc hp_neg hdot_nJ_p
  omega

/-- ⭐⭐⭐⭐⭐ **§7 的结论去掉 `hmpos` 之后的版本。**

与 `not_hattain_of_chain_fields` 逐字同结论，但 `hmpos : 0 < m` 这条 binder **被换成了
三条既有字段**：`hlb`（← `hhp`）、`rec_p`、`hsweep`。三条与其余前提同属
`ChainDataGeomParts`（`ChainPartsFeed.lean`，字段名依次 `hhp` / `rec_p` / `hsweep`，
另加已在签名里的 `ahat_nonempty` / `dot_nJ_p`），所以这不是把债换了个位置，
而是把它接到了现货上。

⟹ **`ℓ` 侧分叉不再有 `0 < m` 这笔债。** 剩下的欠项在 `hpartner` / `Exhausts` / `hnLk`
一侧，与本节无关。 -/
theorem not_hattain_of_chain_fields_no_mpos {A : ℕ → Set (ℤ × ℤ)} {R : ℕ → Set (ℤ × ℤ)}
    {kk : ℕ → ℕ}
    {nJ nℓ vl vJ p nprevJ J νJ1 vJ1 w : ℤ × ℤ} {cz k kJ cJ : ℤ} {m : ℤ} {c : ℕ} {i₀ : ℕ}
    (hnJvJ : dot nJ vJ = 0) (hnJp : dot nJ p ≠ 0) (hvJne : vJ ≠ 0)
    (hvl : vl ≠ 0) (hc : 0 < c) (hp : p = -(c : ℤ) • vl)
    (hperp : dot nℓ vl = 0) (hnlvl : 0 < det nℓ vl)
    (hexh : Exhausts A nℓ cz)
    (hne : (⋃ i, hatOf A kk vl i).Nonempty)
    (hrecL : ∀ g ∈ (⋃ i, hatOf A kk vl i), g + vJ ∈ ⋃ i, hatOf A kk vl i)
    (hnLk : det p vJ • ((-p.2 : ℤ), p.1) = k • nℓ)
    (hv : vJ1 = dir nprevJ) (hw : w = -(dir νJ1))
    (hm : vJ1 = m • vl)
    -- ⭐ 换掉 `hmpos` 的三条字段
    (hlb : ∀ i, ∀ g ∈ hatOf A kk vl i, cJ ≤ dot nJ g)
    (rec_p : ∀ g ∈ ⋃ i, hatOf A kk vl i, g + p ∈ ⋃ i, hatOf A kk vl i)
    (hsweep : dot nJ vJ1 < 0)
    (hvJdef : vJ = kJ • dir J)
    (hD : 0 < det nprevJ νJ1) (he : 0 < det nprevJ J)
    (hrec : ∀ g ∈ (⋃ j, R j), g + vJ ∈ ⋃ j, R j) :
    ¬ (∀ i, i₀ ≤ i → ∀ n : ℤ × ℤ, 0 < dot n w → dot n vJ1 ≤ 0 →
        ∃ z ∈ R i, ∀ g ∈ (⋃ j, R j), dot n g ≤ dot n z) :=
  not_hattain_of_chain_fields hnJvJ hnJp hvJne hvl hc hp hperp hnlvl hexh hne hrecL hnLk
    hv hw hm
    (m_pos_of_chain_stock hne hlb rec_p hc hp hnJp hm hsweep)
    hvJdef hD he hrec

/-! ## §9 原文侧的答案：`b3_colle2.txt` **不**定 `|⟪n_J, v⃗_ℓ⟫| = 1`，而且**不可能**定

第 233 轮派工：去 `b3_colle2.txt` 找一句逼出 `⟪n_J, v⃗_ℓ⟫ = ±1` 的话（定位建议 `:506` 的
「`p` 横截 `ℓ_J`」一段、`:518-520` 的扫掠段）。**答：没有那句话，而且原文自己的 `𝒮_φ` 族里
就有 `|⟪n_J, v⃗_ℓ⟫| = 2` 的成员**——所以缺的不是「我没搜到」，是那句话与原文假设相容地为假。

### §9a 把待证量翻译回原文的量（逐条原文行号）

* `:298` `𝒮_φ := conv(-supp(φ)) ∩ ℤ²`。
* `:317` `supp(φ) = {(0,0)} ∪ {h_{i₁}+⋯+h_{i_r}}`（全部子集和）⟹ `𝒮_φ` 是 `h₁,…,h_m`
  生成的 zonotope 的反射，**中心对称**。
* `:319` `|E(𝒮_φ)| = 2m`，且每条边 `w` 平行或反平行于某个 `h_i`
  ⟹ `𝒮_φ` 的边方向集恰是 `{±h₁,…,±h_m}` 的方向集。
* `:424`（`:541` / `:764` 重述）`ℓ₁,…,ℓ_{2m}` 是这些边方向的**后继（角序）枚举**，
  而 `ℓ = ℓ_ι` 本身**就是其中一条**（`1 ≤ ι ≤ 2m`）。
* `:351` `v⃗_ℓ ∈ ℓ ∩ ℤ²` 是 `ℓ` 方向上最小范数的非零向量 ⟹ **本原**。
* `n_J ⊥ v⃗_{ℓ_J}` 且本原（`𝒮_φ` 的 `J`-面法向）。

⟹ `⟪n_J, v⃗_ℓ⟫ = ± det(v⃗_{ℓ_J}, v⃗_{ℓ_ι})`（下面 `paper_unit_iff_det_unit` 把这一步做成机器检查），
即待证命题逐字是：**zonotope `𝒮_φ` 的两条边方向（本原化后）张成 `ℤ²`**。

### §9b 原文对 `h_i` 的**全部**约束

* `:424` / `:541`：`h₁,…,h_m ∈ ℤ²` 是「pairwise distinct directions」的向量，`m ≥ 2`。
* `:170`（极小分解的性质）：非周期 `η` 的 `R`-极小周期分解里，`i ≠ j` 的两个周期
  **方向不同**——这是极小性对 `h_i` 的**唯一**推论。

除此之外全篇没有任何格论约束：`unimodular` / `determinant` / `basis` / `primitive` /
`coprime` / `gcd` / `sublattice` 在 `b3_colle2.txt` 里各 **0 次命中**（同一条命令内的
哨兵 `convex` = 34、`edge` = 28 非零；`minimum norm` 1 次＝ `:351` 那条 `v⃗_ℓ` 定义，
`index` 1 次＝「indices taken modulo 2m」）。

### §9c 反例：取 `m = 2`、`h₁ = (1,0)`、`h₂ = (1,2)`

方向不同 ✓、`m ≥ 2` ✓ ⟹ 满足 `:424` / `:170` 的**全部**假设。四条边方向
`±(1,0)`、`±(1,2)` 在角序里 `(1,0)` 与 `(1,2)` **相邻**（没有第五个方向夹在中间），
两者都本原，而 `n_J = (2,-1)`（本原、`⊥ (1,2)`）给出 `⟪n_J, v⃗_ℓ⟫ = 2`。
`paper_admits_dot_nJ_vl_two` 把这七条一次性内核判定。

⚠ **射程（§41 / 纪律 9）**：本节否掉的是「**原文对 `h_i` 的假设蕴含 `|⟪n_J,v⃗_ℓ⟫| = 1`**」。
它**不**否掉「`exists_chainData` 的**全部** binder ⊨ `|⟪n_J,v⃗_ℓ⟫| = 1`」——要那么说，
还得为这个 `φ` 造出一个非周期 `η`、一条非扩张 `ℓ`、并把 `Â_i` 的极大构造走到这个 `J`。
本节**没有**兑现那些守卫，因此**不是**对链上命题的反例。结论只有一条：
**若将来有人证出 `|⟪n_J,v⃗_ℓ⟫| = 1`，那条证明必须用到 `h_i` 的方向互异之外的输入**
（非扩张性、或 `Â_i` 的极大性），不能从 `:424` / `:170` 的假设里读出来。

⚠ **旧账订正（§82）**：`LANDING.md` 第 233 轮之前那条「lane-leafa-shell
`adjacent_normals_not_unimodular` 以 `pent`（`(1,0)`、`(2,-1)` 生成的 zonotope）」把
**法向**写成了生成元。读 `tmp/wip/lane-leafa-shell-shellenv.lean` 的 `pent` 定义体
（`{z | 0 ≤ z.2 ∧ z.2 ≤ 2 ∧ z.2 ≤ 2*z.1 ∧ 2*z.1 - z.2 ≤ 2}`）可知它的四条法向是
`±(0,1)`、`±(2,-1)`，边方向是 `±(1,0)`、`±(1,2)`，顶点 `(0,0),(1,0),(2,2),(1,2)`
⟹ `pent` 正是 `h₁=(1,0)`、`h₂=(1,2)` 的 zonotope，**中心对称、4 = 2m 条边**，
与本节的反例是同一个对象（名字里的 "pent" 是误名，不是五边形）。
⟹ 那条见证比 `LANDING` 记的更硬：它落在原文允许的 `𝒮_φ` 形状上，不是随便一个格凸集。
-/

/-- `dot (dir v) z = det v z`。⟹ 面法向取 `dir` 时，「`⟪n_J,·⟫` 是单位」与
「`det v⃗_{ℓ_J} ·` 是单位」是同一句话。
⚠ 主仓另有同名引理 `dot_dir_eq_det`（`HsuppAssemble` / `HsuppCaseCW` / `HsuppRoomCone`，
declscan RAW=3），本条按 §61 改用 `mpos_` 前缀，避免歧义解析。 -/
theorem mpos_dot_dir_eq_det (v z : ℤ × ℤ) : dot (dir v) z = det v z := by
  simp only [dot, det, dir]
  ring

/-- `|⟪n_J, v_ℓ⟫| = 1 ↔ |det v_J v_ℓ| = 1`（`n_J = dir v_J` 时）。
⟹ `GcdCollapse` 的「大小」那一半与 `NlmaxDetVl` 的幺模问法逐字同一。 -/
theorem paper_unit_iff_det_unit {nJ vJ vl : ℤ × ℤ} (hnJ : nJ = dir vJ) :
    (dot nJ vl = 1 ∨ dot nJ vl = -1) ↔ (det vJ vl = 1 ∨ det vJ vl = -1) := by
  rw [hnJ, mpos_dot_dir_eq_det]

/-- **§9 的结论，七条一次性内核判定**：`m = 2`、`h₁ = (1,0)`、`h₂ = (1,2)` 满足
`b3_colle2.txt:424`（方向两两不同、`m ≥ 2`）与 `:170`（极小分解只给「方向不同」）的
全部假设，`v⃗_{ℓ_ι} = h₁`、`v⃗_{ℓ_J} = h₂` 在角序里相邻且都本原，`n_J = (2,-1)` 本原且
`⊥ v⃗_{ℓ_J}`，但 `⟪n_J, v⃗_ℓ⟫ = 2`。⟹ 原文假设**不蕴含** `|⟪n_J, v⃗_ℓ⟫| = 1`。

七条分别是：(1) 方向互异；(2)(3) 两条边方向本原（`:351` 的 `v⃗_ℓ`）；
(4) `n_J` 本原；(5) `n_J ⊥ v⃗_{ℓ_J}`；(6) 角序相邻（`𝒮_φ` 的四条边方向里没有第五个夹在中间，
`:319` + `:424`）；(7) `⟪n_J, v⃗_ℓ⟫ = 2 ≠ ±1`。 -/
theorem paper_admits_dot_nJ_vl_two :
    det ((1 : ℤ), (0 : ℤ)) ((1 : ℤ), (2 : ℤ)) ≠ 0 ∧
    Primitive ((1 : ℤ), (0 : ℤ)) ∧
    Primitive ((1 : ℤ), (2 : ℤ)) ∧
    Primitive ((2 : ℤ), (-1 : ℤ)) ∧
    dot ((2 : ℤ), (-1 : ℤ)) ((1 : ℤ), (2 : ℤ)) = 0 ∧
    (∀ d : ℤ × ℤ,
        (d = ((1 : ℤ), (0 : ℤ)) ∨ d = ((1 : ℤ), (2 : ℤ)) ∨
         d = ((-1 : ℤ), (0 : ℤ)) ∨ d = ((-1 : ℤ), (-2 : ℤ))) →
        ¬ (0 < det ((1 : ℤ), (0 : ℤ)) d ∧ 0 < det d ((1 : ℤ), (2 : ℤ)))) ∧
    dot ((2 : ℤ), (-1 : ℤ)) ((1 : ℤ), (0 : ℤ)) = 2 := by
  refine ⟨by norm_num [det], ?_, ?_, ?_, by norm_num [dot], ?_, by norm_num [dot]⟩
  · show IsCoprime (1 : ℤ) (0 : ℤ)
    exact isCoprime_one_left
  · show IsCoprime (1 : ℤ) (2 : ℤ)
    exact isCoprime_one_left
  · show IsCoprime (2 : ℤ) (-1 : ℤ)
    exact (isCoprime_one_right (R := ℤ) (x := 2)).neg_right
  · rintro d (rfl | rfl | rfl | rfl) <;> norm_num [det]

/-! ### §9d 大小那一半在原文允许的数据上**无界**，不只是「没被钉住」

lane-tower-hbase 第 233 轮落了 `arith_fields_do_not_pin_magnitude`（他报，我未复跑其证明体，
§55）：`nJ = (0,1)`、`vJ = (1,0)` 下 `vl = (0,-1)` 与 `vl = (1,-3)` 两行都满足
`nJ_prim`/`vJ_prim`/`vl_prim`/`hperp`，第二行还兑现 `hp_neg (c=1)`/`hdet_vl`/`dot nJ p ≠ 0`/
`dot nJ vl < 0`，而 `|dot nJ vl|` 分别是 1 和 3 ⟹ **算术／共线 binder 组不钉大小**。

**两座台架之间的差（§52）**：他那一组守卫里**没有** `𝒮_φ` 的 zonotope 结构，也没有角序相邻，
所以「产者必须用几何」这句话在他那里还允许「用面法向来历就够」这个出口。§9c 把那个出口也堵了：
加上 zonotope 结构 ＋ 角序相邻之后大小照样不定。⟹ 下面这条把两座台架合并并推到极限：
**他的第二行本身就是原文允许的数据** —— `(1,0)` 与 `(1,-3)` 生成的 zonotope 满足 `:424`/`:170`
的全部假设，两条方向本原、角序相邻，`n_J = (3,1)` 本原且 `⊥ (1,-3)`。

`paper_admits_dot_nJ_vl_arbitrary` 对**每个** `k > 0` 给出一个原文允许的 `𝒮_φ`
（`m = 2`、`h₁ = (1,0)`、`h₂ = (1,k)`）使 `⟪n_J, v⃗_ℓ⟫ = k`。⟹ 不是「没被钉住」，是**无界**：
任何形如「`|⟪n_J,v⃗_ℓ⟫|` 被某个常数／某个 `m` 的函数界住」的退路也一并关闭。
§9c 的 `k = 2` 与 hbase 第二行的 `k = 3`（反射后）都是它的实例。

⚠ 射程同 §9a：只否「原文假设蕴含之」，**不**否链上命题；几何守卫（`shellEnv`、窗口、
`Â_i` 的极大性、`ℓ` 的非扩张性）一条都没兑现。
-/

/-- **大小那一半在原文允许的数据上无界**：对每个 `k > 0`，`m = 2`、`h₁ = (1,0)`、`h₂ = (1,k)`
满足 `b3_colle2.txt:424`（方向两两不同、`m ≥ 2`）与 `:170` 的全部假设，两条边方向本原、
在 `𝒮_φ` 的四条边方向里角序相邻，`n_J = (k,-1)` 本原且 `⊥ v⃗_{ℓ_J}`，而 `⟪n_J, v⃗_ℓ⟫ = k`。
⟹ 原文假设既不蕴含 `|⟪n_J,v⃗_ℓ⟫| = 1`，也不蕴含它有界。 -/
theorem paper_admits_dot_nJ_vl_arbitrary (k : ℤ) (hk : 0 < k) :
    det ((1 : ℤ), (0 : ℤ)) ((1 : ℤ), k) ≠ 0 ∧
    Primitive ((1 : ℤ), (0 : ℤ)) ∧
    Primitive ((1 : ℤ), k) ∧
    Primitive (k, (-1 : ℤ)) ∧
    dot (k, (-1 : ℤ)) ((1 : ℤ), k) = 0 ∧
    (∀ d : ℤ × ℤ,
        (d = ((1 : ℤ), (0 : ℤ)) ∨ d = ((1 : ℤ), k) ∨
         d = ((-1 : ℤ), (0 : ℤ)) ∨ d = ((-1 : ℤ), -k)) →
        ¬ (0 < det ((1 : ℤ), (0 : ℤ)) d ∧ 0 < det d ((1 : ℤ), k))) ∧
    dot (k, (-1 : ℤ)) ((1 : ℤ), (0 : ℤ)) = k := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hd : det ((1 : ℤ), (0 : ℤ)) ((1 : ℤ), k) = k := by simp [det]
    rw [hd]; omega
  · show IsCoprime (1 : ℤ) (0 : ℤ)
    exact isCoprime_one_left
  · show IsCoprime (1 : ℤ) k
    exact isCoprime_one_left
  · show IsCoprime k (-1 : ℤ)
    exact (isCoprime_one_right (R := ℤ) (x := k)).neg_right
  · show k * 1 + (-1) * k = 0
    ring
  · rintro d (rfl | rfl | rfl | rfl)
    · rintro ⟨h1, -⟩
      simp [det] at h1
    · rintro ⟨-, h2⟩
      simp [det] at h2
    · rintro ⟨h1, -⟩
      simp [det] at h1
    · rintro ⟨h1, -⟩
      simp [det] at h1
      omega
  · show k * 1 + (-1) * 0 = k
    ring

/-! ## §10 接线：`ChainDataGeomParts` 的字段兑现 `not_hattain_of_chain_fields_no_mpos` 的前提

集成者第 233 轮裁决 4 授权：`ChainPartsFeed` 不在禁 import 集里，`ChainPartsFeed` 一侧的接线
由本 lane 做，跨进 `RegionSteps` 的最后一步由集成者接。

`chain_fields_of_parts` 从**一个** `ChainDataGeomParts` 实例 ＋ `exists_chainData` 的
`hp_neg` binder（`0 < c`、`p = -c • vl`）读出下面八条，全部是字段的投影或字段的一步推论：

| 结论 | 来自 |
|---|---|
| `dot nJ vJ = 0` | `cp.F.dot_nJ_vJ`（`FaceBlock` 的字段，`ANormal.lean` 的 `dot_nJ_vJ`） |
| `dot nJ p ≠ 0` | `cp.dot_nJ_p` |
| `vJ ≠ 0` | `cp.vJ_prim` ＋ `not_primitive_zero_lside`（§2） |
| `vl ≠ 0` | `cp.dot_nJ_p` ＋ `hp`：`vl = 0 ⟹ p = 0 ⟹ dot nJ p = 0` |
| `(⋃ Âᵢ).Nonempty` | `cp.ahat_nonempty` |
| `∀ i, ∀ g ∈ Âᵢ, cJ ≤ dot nJ g` | `cp.hhp` 展开 |
| `rec_p` | `cp.rec_p` |
| `dot nJ vJ1 < 0` | `cp.hsweep` |

⚠ **一名多物（已按裁决 3 记入 `NOTATION.md`）**：`halfPlaneGE` 有两份逐字相同的定义，
`Nivat.LE2.halfPlaneGE` 与 `Nivat.CK224.halfPlaneGE`。`ChainPartsFeed` 的 `open` 列表里有
`Nivat.LE2`、没有 `Nivat.CK224` ⟹ 它的 `hhp` 用的是 `Nivat.LE2` 那一份；本文件同样只 open
`Nivat.LE2`，所以两边同指。本节仍把结论写成**展开形**（`cJ ≤ dot nJ g`），这样它对**两份**
定义都成立，接线时选错模块也不会静默走偏。

⚠ **本节没有兑现的前提**，仍是 `not_hattain_of_parts` 的 binder，一条都不是
`ChainDataGeomParts` 的字段：`hperp` / `hnlvl` / `hexh` / `hnLk`（`ℓ`-侧，`exists_chainData`
binder）、`hrecL`（＝ `rec_vJ`，`ChainDataGeomParts` **显式排除**它，见该结构注释）、
`hv` / `hw` / `hm`（扇形后继与共线裁决）、`hvJdef` / `hD` / `he`、`hrec`（区域族 `R` 的）。
⟹ 本节把八条从「要接」变成「已接」，**不**声称整条已闭。
-/

/-- **接线（`ChainPartsFeed` 一侧）**：`ChainDataGeomParts` 的字段 ＋ `hp_neg` binder ⟹
`not_hattain_of_chain_fields_no_mpos` 的八条前提。逐条来源见 §10 的表。 -/
theorem chain_fields_of_parts {α : Type*} {η xper : Config α} {vl p gen : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} (cp : Nivat.ChainAsm.Aparts.ChainDataGeomParts η xper vl p S gen)
    {c : ℕ} (hp : p = -(c : ℤ) • vl) :
    dot cp.nJ cp.vJ = 0 ∧
    dot cp.nJ p ≠ 0 ∧
    cp.vJ ≠ 0 ∧
    vl ≠ 0 ∧
    (⋃ i, hatOf cp.A cp.kk vl i).Nonempty ∧
    (∀ i, ∀ g ∈ hatOf cp.A cp.kk vl i, cp.cJ ≤ dot cp.nJ g) ∧
    (∀ g ∈ ⋃ i, hatOf cp.A cp.kk vl i, g + p ∈ ⋃ i, hatOf cp.A cp.kk vl i) ∧
    dot cp.nJ cp.vJ1 < 0 := by
  refine ⟨cp.F.dot_nJ_vJ, cp.dot_nJ_p, ?_, ?_, cp.ahat_nonempty, ?_, cp.rec_p, cp.hsweep⟩
  · intro h0
    apply not_primitive_zero_lside
    have hprim := cp.vJ_prim
    rw [h0] at hprim
    exact hprim
  · intro h0
    apply cp.dot_nJ_p
    -- ⚠ 不能直接 `rw [hp, h0]`：`p` 与 `vl` 都是 `cp` 类型的索引，目标里有 `cp.nJ`
    -- ⟹ `rw` 的 motive 不类型正确。先把法向抽成任意 `n`，重写就落在不依赖它的目标上。
    have key : ∀ n : ℤ × ℤ, dot n p = 0 := by
      intro n
      rw [hp, h0]
      simp [dot]
    exact key cp.nJ
  · intro i g hg
    have hmem := cp.hhp i hg
    simpa [Nivat.LE2.halfPlaneGE, Set.mem_setOf_eq] using hmem

/-- **接线后的 ℓ-侧分叉否定**：`hmpos` 与那八条前提都不再是 binder，`ChainDataGeomParts`
一个实例就把它们全供上。剩下的 binder 全部列在 §10 的第二个 ⚠ 里，一条都不是该结构的字段。 -/
theorem not_hattain_of_parts {α : Type*} {η xper : Config α}
    {R : ℕ → Set (ℤ × ℤ)} {vl p gen : ℤ × ℤ} {S : Finset (ℤ × ℤ)}
    (cp : Nivat.ChainAsm.Aparts.ChainDataGeomParts η xper vl p S gen)
    {nℓ nprevJ J νJ1 : ℤ × ℤ} {cz k kJ : ℤ} {m : ℤ} {c : ℕ} {i₀ : ℕ}
    (hc : 0 < c) (hp : p = -(c : ℤ) • vl)
    (hperp : dot nℓ vl = 0) (hnlvl : 0 < det nℓ vl)
    (hexh : Exhausts cp.A nℓ cz)
    (hrecL : ∀ g ∈ (⋃ i, hatOf cp.A cp.kk vl i), g + cp.vJ ∈ ⋃ i, hatOf cp.A cp.kk vl i)
    (hnLk : det p cp.vJ • ((-p.2 : ℤ), p.1) = k • nℓ)
    (hv : cp.vJ1 = dir nprevJ) (hw : cp.w = -(dir νJ1))
    (hm : cp.vJ1 = m • vl)
    (hvJdef : cp.vJ = kJ • dir J)
    (hD : 0 < det nprevJ νJ1) (he : 0 < det nprevJ J)
    (hrec : ∀ g ∈ (⋃ j, R j), g + cp.vJ ∈ ⋃ j, R j) :
    ¬ (∀ i, i₀ ≤ i → ∀ n : ℤ × ℤ, 0 < dot n cp.w → dot n cp.vJ1 ≤ 0 →
        ∃ z ∈ R i, ∀ g ∈ (⋃ j, R j), dot n g ≤ dot n z) := by
  obtain ⟨hnJvJ, hnJp, hvJne, hvlne, hne, hlb, hrp, hsw⟩ := chain_fields_of_parts cp hp
  exact not_hattain_of_chain_fields_no_mpos hnJvJ hnJp hvJne hvlne hc hp hperp hnlvl hexh
    hne hrecL hnLk hv hw hm hlb hrp hsw hvJdef hD he hrec

/-! ## §11 `hm` 的射程就是窗口底端一格 ⟹ 共线前提可以换成 `vJ1 = vl`

lane-tower-hbase 报：`hm : vJ1 = m • vl` 这条前提在窗口 `ι+1 ≤ J ≤ ι+m−1`（`b3_colle2.txt:432`
item (i)，Lean 侧写成 `t + 1 < m`、`t` 跑 `0 … m−2`）里**只在 `t = 0` 一格上可满足**，
`1 ≤ t ≤ m−2` 上前件为假。

⚠ §55 / §26 记账：**我自己复核的只有一条**——`window_bot_of_det_prev_eq_zero`
（`CyclicOrderWindow.lean`，主仓，0 sorry），它确实说窗口内 `det (C.nu i) (C.nu (i+t)) = 0 ⟹ t = 0`，
而 `nu_prev_eq_of_det_prev_eq_zero`（同文件）把它加强成 `C.nu (i+t) = C.nu i`。
**没有复核的**：hbase 把这两条从法向侧搬到方向侧的那步转录，以及他 `TowerHbaseRecP.lean` §7
的六条声明（`collinear_iff_window_bot` / `vJ1_eq_vl_of_det_zero` / `prim_vJ1_iff_m_eq_one` /
`exists_pos_multiple_of_det_zero` 等）——那些是「hbase 报，我未复核」。
本节的定理**不依赖**其中任何一条：`hbot` 是签名里的前提，不是我从他那里引来的结论。

### 为什么这是收窄前提而不是收窄结论

`vl ≠ 0` 之下 `vJ1 = m • vl ⟺ det vl vJ1 = 0`，而窗口里 `det vl vJ1 = 0` 只发生在 `J = ι+1`
（`FillCoverWitness.lean` 里把这一格叫「`J = ι + 1` configuration」），此时 `vJ1 = vl`，即 `m = 1`。
于是对消费者而言：

| 供 §10 的 `hm` | 供 §11 的 `hbot` |
|---|---|
| 要先造出一个 `m : ℤ`，再证 `vJ1 = m • vl` | 只要 `vJ1 = vl` |
| `0 < m` 另需 `m_pos_of_chain_stock`（虽已闭合，仍要把四条链货摆上） | `m = 1` 直接给 |

⟹ `hbot` 严格比 `hm` 好供。**结论一字未改**，两条的结论逐字相同。

⚠ 本节**不**主张「链上一定落在 `J = ι+1`」。窗口的其余格上 `hm` 为假 ⟹ §10 / §11 这一支
在那些格上是空真（§41）；那些格要别的产者，不在 ℓ-侧分叉里。这一条我报给集成者，
没有替他改 `RegionSteps` 的分支结构。 -/

/-- **窗口底端形的 ℓ-侧分叉否定**：把 §10 的共线前提 `hm : cp.vJ1 = m • vl` 换成
`hbot : cp.vJ1 = vl`（即 `m = 1`，窗口底端 `J = ι+1` 的那一格）。结论与
`not_hattain_of_parts` 逐字相同，前提严格更好供：不必造 `m`，也不必再走 `0 < m`。 -/
theorem not_hattain_of_parts_at_window_bot {α : Type*} {η xper : Config α}
    {R : ℕ → Set (ℤ × ℤ)} {vl p gen : ℤ × ℤ} {S : Finset (ℤ × ℤ)}
    (cp : Nivat.ChainAsm.Aparts.ChainDataGeomParts η xper vl p S gen)
    {nℓ nprevJ J νJ1 : ℤ × ℤ} {cz k kJ : ℤ} {c : ℕ} {i₀ : ℕ}
    (hc : 0 < c) (hp : p = -(c : ℤ) • vl)
    (hperp : dot nℓ vl = 0) (hnlvl : 0 < det nℓ vl)
    (hexh : Exhausts cp.A nℓ cz)
    (hrecL : ∀ g ∈ (⋃ i, hatOf cp.A cp.kk vl i), g + cp.vJ ∈ ⋃ i, hatOf cp.A cp.kk vl i)
    (hnLk : det p cp.vJ • ((-p.2 : ℤ), p.1) = k • nℓ)
    (hv : cp.vJ1 = dir nprevJ) (hw : cp.w = -(dir νJ1))
    (hbot : cp.vJ1 = vl)
    (hvJdef : cp.vJ = kJ • dir J)
    (hD : 0 < det nprevJ νJ1) (he : 0 < det nprevJ J)
    (hrec : ∀ g ∈ (⋃ j, R j), g + cp.vJ ∈ ⋃ j, R j) :
    ¬ (∀ i, i₀ ≤ i → ∀ n : ℤ × ℤ, 0 < dot n cp.w → dot n cp.vJ1 ≤ 0 →
        ∃ z ∈ R i, ∀ g ∈ (⋃ j, R j), dot n g ≤ dot n z) :=
  not_hattain_of_parts cp (m := 1) hc hp hperp hnlvl hexh hrecL hnLk hv hw
    (by rw [hbot, one_smul]) hvJdef hD he hrec

/-! ## §12 `vJ1` 在 `ChainDataGeomParts` 里**不是**由 `ℓ_{J−1}` 的方向定义的

集成者第 234 轮派工（裁决 7）要么产出
`∃ m : ℤ, cp.vJ1 = m • vl ∧ Primitive cp.vJ1`，要么报「`vJ1` 实际由哪个对象给」。**答案是后者。**

### §12a 结构里提到 `vJ1` 的全部位置（`ChainPartsFeed.lean`，我自己 grep 的，逐条点开读过）

| 位置 | 内容 | 是否把 `vJ1` 与 `vl` / 边方向枚举关联 |
|---|---|---|
| 字段 `vJ1`，注释头只写 `shell data` | 独立数据，**无 docstring**、无原文锚 | 否 |
| `hsweep` | `dot nJ vJ1 < 0` | 否（只约束与 `nJ` 的符号） |
| `hswept` | `MaxEnv.SweptClosed (⋃ i, hatOf A kk vl i) vJ1 nJ cJ` | 否（`vl` 只经**那个集合**出现） |
| `escapeW` / `shellSubStrip` / `fillCover` | `vJ1` 作 `MaxEnv.shell … vJ1 nJ cJ ε` 与 `MaxEnv.reachSet … vJ1` 的 sweep 方向 | 否（同上） |

⟹ **`vJ1` 在这个结构里的角色是「shell 的 sweep 方向」，不是「边 `ℓ_{J−1}` 的方向向量」。**
`w` 字段有 docstring 明写自己是 `−v_{ℓ_{J+1}}`（`b3_colle2.txt:518`）并声明与 `vJ1` 是**两份**数据；
`vJ1` 没有对应的那句话。结构里唯一把 `vJ1` 说成 `v⃗_{ℓ_{J−1}}` 的地方是 `w` 字段 docstring 末尾
那句「`vJ1 ∥ vl`（共线，`J = ι+1` 构型）」——那是**旁注**，不是字段义务。

⟹ 集成者说的「如果是后者，那说明 `m = 1` 的裁决在链上还缺一块地基」正是实情：
`hm : cp.vJ1 = m • vl` 不可能从 `ChainDataGeomParts` 推出来，因为该结构从不说 `vJ1` 是谁的方向。
要接上必须由**生产者**（`exists_chainData` 一侧）在造 `ChainDataGeomParts` 时把
`vJ1 := v⃗_{ℓ_{J−1}}` 这个选择连同 `:351` 的 minimum-norm 性质一起带进来——那是结构外的输入，
不是结构内的定理。

### §12b 内核收据：`Primitive vJ1` 连**单约束 `vJ1` 的那两条义务**都推不出

下面三条把 §12a 的定性钉成可判的：`hsweep` 与 `hswept` 在 `vJ1 ↦ (k:ℤ) • vJ1`（`k ≥ 1`）
下都**保持**，而 `(2:ℤ) • v` 永远不 `Primitive`。⟹ 这两条义务的任何推论都不可能是
`Primitive vJ1`，也不可能是 `vJ1 = 1 • vl`（否则同一组数据上 `2 • vJ1` 也得等于 `vl`）。

⚠ **射程**：本节只覆盖 `hsweep` 与 `hswept` 两条。shell 三条（`escapeW` / `shellSubStrip` /
`fillCover`）也提到 `vJ1`，而 `shell … (2 • vJ1) …` 只含偶数倍那一半、并非上面那种保持，
所以**没有**主张「整个结构推不出 `Primitive vJ1`」。要那句话得另外造实例（25 条义务全兑现），
本节不冒充它。 -/

/-- `MaxEnv.SweptClosed` 在 sweep 方向乘正整数下保持：`g + t • (k • v) = g + (t*k) • v`，
而 `t * k : ℕ` 仍在 `t : ℕ` 的取值范围里。 -/
theorem sweptClosed_nsmul_lside {A : Set (ℤ × ℤ)} {v n : ℤ × ℤ} {c : ℤ} (k : ℕ)
    (h : MaxEnv.SweptClosed A v n c) : MaxEnv.SweptClosed A ((k : ℤ) • v) n c := by
  intro g hg t hle
  have hrw : g + (t : ℤ) • ((k : ℤ) • v) = g + ((t * k : ℕ) : ℤ) • v := by
    rw [smul_smul]
    push_cast
    ring_nf
  rw [hrw]
  rw [hrw] at hle
  exact h g hg (t * k) hle

/-- `(2:ℤ) • v` 永远不是 `Primitive`：`IsCoprime (2*v.1) (2*v.2)` 会给 `(2:ℤ) ∣ 1`。 -/
theorem not_primitive_two_smul_lside (v : ℤ × ℤ) : ¬ Primitive ((2 : ℤ) • v) := by
  intro hcop
  obtain ⟨u, w, h⟩ := hcop
  -- ⚠ 不加 `smul_eq_mul` 的话 `2 • v.1` 在 ℤ 上仍是 `zsmul` 项，`linarith` 只当它是原子。
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h
  have hdvd : (2 : ℤ) ∣ 1 := ⟨u * v.1 + w * v.2, by linear_combination -h⟩
  norm_num at hdvd

/-- ⛔ **`Primitive vJ1` 不是 `hsweep` ＋ `hswept` 的推论。**
同一组 `A / nJ / cJ` 上把 `vJ1` 换成 `2 • vJ1`，两条义务照旧成立，而它不 `Primitive`。
⟹ 该结论的产者必须来自这两条之外（`:351` 的 minimum-norm 是结构外输入，见 §12a）。 -/
theorem prim_vJ1_not_from_sweep_obligations {A : Set (ℤ × ℤ)} {vJ1 nJ : ℤ × ℤ} {cJ : ℤ}
    (hsweep : dot nJ vJ1 < 0) (hswept : MaxEnv.SweptClosed A vJ1 nJ cJ) :
    dot nJ ((2 : ℤ) • vJ1) < 0 ∧
    MaxEnv.SweptClosed A ((2 : ℤ) • vJ1) nJ cJ ∧
    ¬ Primitive ((2 : ℤ) • vJ1) := by
  refine ⟨?_, ?_, not_primitive_two_smul_lside vJ1⟩
  · rw [mpos_dot_zsmul]
    omega
  · exact sweptClosed_nsmul_lside 2 hswept

/-! ## §13 `⋃ Âᵢ` **不是**半平面——这条不用读原文，链上现货就否掉它

lane-tower-hlev 本轮报：`RecVJ.iUnion_hatOf_eq_halfPlane`（`⋃ i, hatOf A kk vl i` 等于半平面）
的五条前提里四条由 `ItemIIChain.exists_itemII_chain` 一次给全，**唯一残余是 `hkk`**，
于是「给定那四条，`hkk` 等价于那个半平面等式」（**他的实测，我未复核**，§55），
并问我 `b3_colle2.txt:506` 的 `Â_∞` 是不是链上的 `⋃ i, hatOf A kk vl i`。

原文侧的答案在 §13a，但**更强的答案是本节的定理：半平面等式与链上现货直接矛盾，不需要原文**。

### §13a 原文侧（回答 hlev 的问题，逐条行号）

* `:506` 逐字：`Â_∞ := ⋃_{i=1}^∞ Â_i` 「is a weakly `E(𝒮_φ)`-enveloped set …, with two
  semi-infinite edges, one of which is parallel to `ℓ` and the other one is parallel to `ℓ_J`.
  Actually, `Â_∞` is an `(ℓ, ℓ_J)`-region.」⟹ `:506` 说的确实是**带帽**的并集。
* `:498` 在**同一段**里逐字写 `⋃_{i=1}^∞ A_i = ℋ(ℓ^{(−)})`，而且那是选 `J` 的**理由**。
  ⟹ 原文自己把两个对象分开：**半平面是不带帽的 `⋃ Aᵢ`，楔形是带帽的 `⋃ Âᵢ`**。
* `:386` 是 `(ℓ,ℓ')`-region 的定义，逐字要求 `ℓ, ℓ'`「in distinct directions」。
  而窗口 `ι+1 ≤ J ≤ ι+m−1` 下 `ℓ_J ≠ ±ℓ_ι`（`det_eq_zero_iff_of_lt_two_mul`
  （`CyclicOrderWindow.lean`，主仓 0 sorry，本轮我读了证明体）说 `det ν_ι ν_{ι+s} = 0`
  仅在 `s = 0 ∨ s = m`，而窗口给 `1 ≤ s ≤ m−1`）⟹ 两条半无限边方向既不平行也不反平行
  ⟹ `Â_∞` 是真楔形，**不可能**是半平面。
* 字典核对：Lean 的 `hatOf A kk vl i = {z | z + kk i • vl ∈ A i}`，即 `A i − kk i • vl`；
  `:492` 把 `Â_i` 夹在 `B_i − k_i v⃗_ℓ` 与 `H_{B_i}(ℓ) − k_i v⃗_ℓ` 之间，而 `ChainDataGeomParts`
  的 `subBA` / `maxA` 是**不带移位**的那一版 ⟹ Lean `A i` ↔ 原文 `A_i`，
  Lean `hatOf … i` ↔ 原文 `Â_i`。⟹ hlev 问的那句「是不是同一个对象」答案是**是**。

⟹ 回他的三选项：不是「两种读法都容得下」，是**原文在同一段里同时陈述了两个不同对象**，
而 `RecVJ.iUnion_hatOf_eq_halfPlane` 的结论对应的是 `:498` 那个（不带帽的），
不是 `:506` 那个（带帽的）。

### §13b 链上侧（不依赖原文，也不依赖 hlev 的等价性实测）

半平面沿 `vl` 是**双向**平移不变的（`dot nℓ vl = 0`），所以若 `⋃ Âᵢ` 等于它，则 `vl` 是
`⋃ Âᵢ` 的退化方向；而 `hhp` 给 `⟪n_J,·⟫` 在 `⋃ Âᵢ` 上有下界 `cJ`，两者合起来逼出
`0 ≤ ⟪n_J,v⃗_ℓ⟫`（`dot_nonneg_of_rec`）。但链上现货给 `⟪n_J,v⃗_ℓ⟫ < 0`
（§7 的 `dot_nJ_vl_neg_of_rec_p`）。⟹ 矛盾。

⚠ 本条否掉的是**那个半平面等式本身**，不是 `hkk`。要把它读成「`hkk` 在链上为假」，
还得用 hlev 那条等价性（他的实测，我未复核）。这两句的差别不许抹掉。 -/

/-- ⛔ **`⋃ i, hatOf A kk vl i` 不等于任何以 `nℓ ⊥ vl` 为法向的半平面。**
前提全是链上现货（`ahat_nonempty` / `hhp` / `rec_p` / `dot_nJ_p` ＋ `hp_neg` ＋ `hperp`），
结论是那条等式的否定。⟹ `RecVJ.iUnion_hatOf_eq_halfPlane` 的前提在链上不可同时满足。

半平面写成**展开形** `{z | cz ≤ dot nℓ z}` 而不写 `halfPlaneGE`：后者一名两物
（`Nivat.LE2` 与 `Nivat.CK224` 两份逐字相同的定义，见 `NOTATION.md`），展开形对两份都成立。 -/
theorem not_iUnion_hatOf_eq_halfPlane_of_chain_stock {A : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ}
    {vl p nJ nℓ : ℤ × ℤ} {cJ cz : ℤ} {c : ℕ}
    (hne : (⋃ i, hatOf A kk vl i).Nonempty)
    (hlb : ∀ i, ∀ g ∈ hatOf A kk vl i, cJ ≤ dot nJ g)
    (rec_p : ∀ g ∈ ⋃ i, hatOf A kk vl i, g + p ∈ ⋃ i, hatOf A kk vl i)
    (hc : 0 < c) (hp_neg : p = -(c : ℤ) • vl)
    (hdot_nJ_p : dot nJ p ≠ 0)
    (hperp : dot nℓ vl = 0) :
    (⋃ i, hatOf A kk vl i) ≠ {z | cz ≤ dot nℓ z} := by
  intro heq
  have hlb' : ∀ g ∈ ⋃ i, hatOf A kk vl i, cJ ≤ dot nJ g := by
    intro g hg
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hg
    exact hlb i g hi
  -- `vl` 是退化方向：半平面的法向与 `vl` 垂直 ⟹ 沿 `vl` 平移不改变 `⟪nℓ,·⟫`。
  have rec_vl : ∀ g ∈ ⋃ i, hatOf A kk vl i, g + vl ∈ ⋃ i, hatOf A kk vl i := by
    intro g hg
    rw [heq] at hg ⊢
    have hgg : cz ≤ dot nℓ g := hg
    show cz ≤ dot nℓ (g + vl)
    rw [dot_add, hperp, add_zero]
    exact hgg
  have h0 : 0 ≤ dot nJ vl := dot_nonneg_of_rec hne hlb' rec_vl
  have hneg : dot nJ vl < 0 := dot_nJ_vl_neg_of_rec_p hne hlb rec_p hc hp_neg hdot_nJ_p
  omega

/-! ## §14 `parts_rec_vJ` 的侧条件在**横截格**复活

集成者第 234 轮派工：hlev 的 `TowerHlevTile.not_hcomb_of_collinear` 在**共线格**判死了
`RecVJComb.parts_rec_vJ` 的侧条件 `vJ = a • p + t • vJ1`；去掉 `hm`（进入横截格
`det vl vJ1 ≠ 0`）之后它还是不是不可满足？并要我亲读 `hcomb_satisfiable_off_chain` 的常数、
判它是否兑现横截格的其余链货。

**答：可满足，而且那条见证本来就是横截格的见证。** ⟹ `parts_rec_vJ` 在横截格复活。

### §14a 常数与 `vl` 的恢复（我亲读的，不是转述）

`hcomb_satisfiable_off_chain`（`TowerHlevTile.lean`）与 `RecVJComb.comb_nonvacuous` 用的是
**同一组**常数：`nJ = (0,1)`、`vJ = (1,0)`、`p = (1,1)`、`vJ1 = (0,-1)`、`a = t = 1`。
⚠ 那条见证**自己不提 `vl`**，只断言 `det p vJ1 ≠ 0`。所以判它是不是横截格的见证，
必须先把 `vl` 恢复出来——而链上 `p = -(c : ℤ) • vl` 且 `0 < c` 把它**钉死**：
`(1,1) = -c • vl` 在 `c : ℕ`、`0 < c` 下只有 `c = 1`、`vl = (-1,-1)`。

代回去：`det vl vJ1 = det (-1,-1) (0,-1) = 1 ≠ 0` ⟹ **横截**。
（同时 `¬ ∃ m, vJ1 = m • vl`，所以 hlev 那条共线否定确实不适用，两条不打架。）

### §14b 它兑现了横截格的哪些链货（逐条，下面的定理是内核检验）

| 链货 | 取值 | 是否兑现 |
|---|---|---|
| `0 < c` | `c = 1` | ✅ |
| `hp_neg : p = -(c:ℤ) • vl` | `(1,1) = -1 • (-1,-1)` | ✅ |
| `Primitive vl` | `IsCoprime (-1) (-1)` | ✅ |
| `dot nJ vJ = 0`（`F.dot_nJ_vJ`） | `dot (0,1) (1,0) = 0` | ✅ |
| `vJ ≠ 0` | `(1,0) ≠ 0` | ✅ |
| `dot nJ p ≠ 0`（`dot_nJ_p`） | `dot (0,1) (1,1) = 1` | ✅ |
| `dot nJ vl < 0`（§7 现货的结论） | `dot (0,1) (-1,-1) = -1` | ✅ |
| `hsweep : dot nJ vJ1 < 0` | `dot (0,1) (0,-1) = -1` | ✅ |
| `hperp : dot nℓ vl = 0`（取 `nℓ = (-1,1)`） | `dot (-1,1) (-1,-1) = 0` | ✅ |
| `hnlvl : 0 < det nℓ vl` | `det (-1,1) (-1,-1) = 2` | ✅ |
| 侧条件 `vJ = 1 • p + 1 • vJ1` | `(1,1) + (0,-1) = (1,0)` | ✅ |

⚠ **射程，别替我放大**：本节证的是「侧条件与这十一条**算术／符号**链货相容」。
`comb_nonvacuous`（`RecVJComb.lean`，hlev/集成者的文件，**我未复跑**）在同一组常数上另外
兑现了集合侧的 `hhp` 下界、`SweptClosed`、`rec_p`（取 `U = {z | 0 ≤ z.2}`）。
本节**没有**造出完整的 `ChainDataGeomParts` 实例（那要 25 条义务全兑现），
所以结论是「侧条件在横截格不被这些链货挡住」，不是「横截格已经接通」。 -/

/-- ⭐ **横截格见证**：`hcomb_satisfiable_off_chain` 的常数在恢复出 `vl = (-1,-1)`、`c = 1` 之后
落在 `det vl vJ1 ≠ 0` 一侧，且兑现十一条链货（含两个符号守卫 `dot nJ vl < 0` 与 `hsweep`）。
最后一条 `¬ ∃ m, vJ1 = m • vl` 说明 hlev 的共线否定在此**前件为假**，两条不冲突。 -/
theorem hcomb_transverse_witness_lside :
    ((1 : ℤ), (1 : ℤ)) = -((1 : ℕ) : ℤ) • ((-1 : ℤ), (-1 : ℤ)) ∧
    (0 : ℕ) < 1 ∧
    Primitive ((-1 : ℤ), (-1 : ℤ)) ∧
    det ((-1 : ℤ), (-1 : ℤ)) ((0 : ℤ), (-1 : ℤ)) ≠ 0 ∧
    dot ((0 : ℤ), (1 : ℤ)) ((1 : ℤ), (0 : ℤ)) = 0 ∧
    ((1 : ℤ), (0 : ℤ)) ≠ ((0 : ℤ), (0 : ℤ)) ∧
    dot ((0 : ℤ), (1 : ℤ)) ((1 : ℤ), (1 : ℤ)) ≠ 0 ∧
    dot ((0 : ℤ), (1 : ℤ)) ((-1 : ℤ), (-1 : ℤ)) < 0 ∧
    dot ((0 : ℤ), (1 : ℤ)) ((0 : ℤ), (-1 : ℤ)) < 0 ∧
    dot ((-1 : ℤ), (1 : ℤ)) ((-1 : ℤ), (-1 : ℤ)) = 0 ∧
    0 < det ((-1 : ℤ), (1 : ℤ)) ((-1 : ℤ), (-1 : ℤ)) ∧
    ((1 : ℤ), (0 : ℤ)) = ((1 : ℕ) : ℤ) • ((1 : ℤ), (1 : ℤ))
      + ((1 : ℕ) : ℤ) • ((0 : ℤ), (-1 : ℤ)) ∧
    ¬ (∃ m : ℤ, ((0 : ℤ), (-1 : ℤ)) = m • ((-1 : ℤ), (-1 : ℤ))) := by
  refine ⟨by norm_num [Prod.ext_iff], by norm_num, ⟨-1, 0, by norm_num⟩,
    by norm_num [det], by norm_num [dot], by norm_num [Prod.ext_iff],
    by norm_num [dot], by norm_num [dot], by norm_num [dot], by norm_num [dot],
    by norm_num [det], by norm_num [Prod.ext_iff], ?_⟩
  rintro ⟨m, hm⟩
  rw [Prod.ext_iff] at hm
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at hm
  omega

/-! ## §15 共线格的残类覆盖：**不成立**，而且缺的那条输入可以点名

集成者第 235 轮派工（洞 1 的深推目标）：设 `g := |⟪n_J, v⃗_ℓ⟫|`，问
`dot nJ '' (⋃ i, hatOf A kk vl i)` 是否覆盖 mod `g` 的每一个残类。三条硬要求：
陈述在**真对象** `⋃ i, hatOf A kk vl i` 上（不许退到抽象 `AR`）；不出现 `p` / `vJ1` / 递推；
只许用列出的那批现货。

**答：由那批现货推不出覆盖。** 下面是内核见证：`g = 2`，而整个 `⋃ Âᵢ` 的 `⟪n_J,·⟫` 像
**全是偶数**，奇残类一个都不沾。

### §15a 见证怎么造的，以及为什么它仍然陈述在真对象上

取 `nJ = (0,1)`（故 `⟪n_J,z⟫ = z.2`）、`vl = (1,-2)`、`c = 1`、`p = -1 • vl = (-1,2)`、
`vJ = (1,0)`、`cJ = 0`，并取 `kk ≡ 0`、`A i ≡ {z | 0 ≤ z.2 ∧ z.2 ≡ 0 (mod 2)}`。
因为 `hatOf A kk vl i = {z | z + (kk i : ℤ) • vl ∈ A i}`（`ChainMax.lean`，标识符 `hatOf`），
`kk ≡ 0` 时 `hatOf A kk vl i = A i`，于是 `⋃ i, hatOf A kk vl i` **逐字就是**那个集合——
没有退到抽象 `AR`，满足硬要求 1。

`g = |dot nJ vl| = |-2| = 2`，而 `dot nJ z = z.2` 在该集合上恒为偶 ⟹ 奇残类空。

### §15b 它兑现了派工里列出的**每一条**现货

`0 < c`（=1）／`hp_neg : p = -(1:ℤ) • vl`／`Primitive vl`＝`IsCoprime 1 (-2)`／
`Primitive nJ`＝`IsCoprime 0 1`／`ahat_nonempty`（`(0,0)`）／
`hhp : ∀ i, ∀ z ∈ hatOf …, 0 ≤ dot nJ z`／`rec_p`（加 `(-1,2)` 保持「非负且偶」）／
`dot_nJ_p = 2 ≠ 0`／`hperp : dot nJ vJ = 0`／`vJ ≠ 0`／`dot nJ vl = -2 < 0`（符号守卫）。

⟹ **递推确实对残类零贡献**：`dot nJ p = 2 = c·g`，沿 `p` 走只在同一个 mod `g` 残类里升高，
这正是集成者说的秩 1 机理，本见证把它变成可判的。

### §15c 缺的那条输入，点名

见证里的 `A` 当然不是「极大 `E(𝒮_φ)`-包络集」——它在高度上**跳着走**。最后三个合取
把这件事钉成可判的形状：`(0,0) ∈ ⋃ Âᵢ`、`(0,2) ∈ ⋃ Âᵢ`，而夹在正中间的 `(0,1) ∉ ⋃ Âᵢ`。

⟹ 挡住覆盖的不是 `p` / `vJ1` / 递推里的任何东西（它们在本见证里全部兑现），
而是 **`A` 自己的高度谱可以有洞**。要让覆盖成立，必须从 `ChainDataGeomParts` 的
`maxA`（`IsMaxEnvIn … (canonA η xper vl B u i) (A i)`）／`envB` 一侧取一条
「高度谱无间隙」的输入——**那两条不在派工列出的现货表里**。

⚠ **射程（三条，别替我放大）**：
1. 本节否掉的是「覆盖**由那批现货**推出」，**不是**「覆盖在链上为假」。链上的 `A` 带
   `maxA`／`envB`，本见证的不带；真链上覆盖可能仍然成立。
2. 我**没有**主张「`maxA` 足以给出覆盖」。点名的是「缺口在 `maxA`／`envB` 一侧」，
   不是「补上就够」——后者要另证。
3. `edge`（env-refute 报它允许窗口点恰在面上方 1 且无上界）我**没有**兑现，
   本见证不涉及它；若 `edge` 另有力量，本节不排除。 -/

/-- ⛔ **残类覆盖不是链上现货的推论。** `g = |dot nJ vl| = 2`，而见证里整个
`⋃ i, hatOf A kk vl i` 的 `⟪n_J,·⟫` 像全为偶数 ⟹ 奇残类空。
派工列出的现货逐条兑现（含符号守卫 `dot nJ vl < 0`）；最后三条指出挡住覆盖的是
`A` 的高度谱有洞（`(0,0)` 与 `(0,2)` 在、`(0,1)` 不在），而不是 `p`/`vJ1`/递推。 -/
theorem residue_coverage_not_from_chain_stock_lside :
    ∃ (A : ℕ → Set (ℤ × ℤ)) (kk : ℕ → ℕ) (vl p nJ vJ : ℤ × ℤ) (cJ : ℤ) (c : ℕ),
      0 < c ∧
      p = -(c : ℤ) • vl ∧
      Primitive vl ∧
      Primitive nJ ∧
      (⋃ i, hatOf A kk vl i).Nonempty ∧
      (∀ i, ∀ z ∈ hatOf A kk vl i, cJ ≤ dot nJ z) ∧
      (∀ z ∈ ⋃ i, hatOf A kk vl i, z + p ∈ ⋃ i, hatOf A kk vl i) ∧
      dot nJ p ≠ 0 ∧
      dot nJ vJ = 0 ∧
      vJ ≠ 0 ∧
      dot nJ vl < 0 ∧
      |dot nJ vl| = 2 ∧
      (∀ z ∈ ⋃ i, hatOf A kk vl i, dot nJ z % 2 = 0) ∧
      ((0 : ℤ), (0 : ℤ)) ∈ (⋃ i, hatOf A kk vl i) ∧
      ((0 : ℤ), (2 : ℤ)) ∈ (⋃ i, hatOf A kk vl i) ∧
      ((0 : ℤ), (1 : ℤ)) ∉ (⋃ i, hatOf A kk vl i) := by
  classical
  refine ⟨fun _ => {z : ℤ × ℤ | 0 ≤ z.2 ∧ z.2 % 2 = 0}, fun _ => 0,
    ((1 : ℤ), (-2 : ℤ)), ((-1 : ℤ), (2 : ℤ)), ((0 : ℤ), (1 : ℤ)), ((1 : ℤ), (0 : ℤ)), 0, 1,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- `kk ≡ 0` ⟹ `hatOf … i` 逐字等于那个常值集合；下面每条都靠这一步化简。
  · norm_num
  · norm_num [Prod.ext_iff]
  · show IsCoprime (1 : ℤ) (-2 : ℤ)
    exact isCoprime_one_left
  · show IsCoprime (0 : ℤ) (1 : ℤ)
    exact isCoprime_one_right
  · exact ⟨((0 : ℤ), (0 : ℤ)), by simp [hatOf]⟩
  · intro i z hz
    simp only [hatOf, Set.mem_setOf_eq, Nat.cast_zero, zero_smul, add_zero] at hz
    simp only [dot]
    omega
  · intro z hz
    simp only [Set.mem_iUnion, hatOf, Set.mem_setOf_eq, Nat.cast_zero, zero_smul,
      add_zero] at hz ⊢
    obtain ⟨i, hi⟩ := hz
    exact ⟨i, by simp only [Prod.snd_add] at *; omega⟩
  · simp [dot]
  · simp [dot]
  · simp [Prod.ext_iff]
  · simp [dot]
  · simp [dot]
  · intro z hz
    simp only [Set.mem_iUnion, hatOf, Set.mem_setOf_eq, Nat.cast_zero, zero_smul,
      add_zero] at hz
    obtain ⟨i, hi⟩ := hz
    simp only [dot]
    omega
  · simp [hatOf]
  · simp [hatOf]
  · simp [hatOf]

/-! ## §16 高度谱无间隙：§15 缺的那条输入是**格凸**，而它在链上是现货

### §16a 问题与答案

§15 的射程 2 留下的那句原话是「本节**不**主张 `maxA` 够用」。本节把它做完了，答案是
**共线格的残类覆盖成立**，并且挡住 §15 的不是 `p` / `vJ1` / 递推，而是**一条**没被列进派工
现货表的输入：`IsLatticeConvexRegion (⋃ i, hatOf A kk vl i)`。

这条输入在链上是现货：`ChainAsm.Aparts.ChainDataGeomParts` 的 `maxA` 字段就是
`IsMaxEnvIn (EnvOf ↑S) (canonA …) (A i)`，`.1` 即 `EnvOf ↑S (A i)` ＝ `Enveloped ↑S (A i)`，
其 `.1.1` 即 `IsLatticeConvexRegion (A i)`（`AEnv.lean` 的 `envACanon_unfolded` 把这三层
逐字展开过，我点开读了）。从逐格格凸到并集格凸，主仓已有
`Colle35.latticeConvex_iUnion_hatOf`（`ChainAssemble.lean`），它另吃 `hfin` / `AhatMono` /
`hEnv`——三条**也都是**该结构的字段（`hEnv` 因结构把 `Env` 钉成 `EnvOf ↑S` 而是 `rfl`）。
⟹ 这条组合在主仓**已有**，是 `LaneLeafAGenRecVJ.latticeConvex_of_parts`
（`RecVJFromParts.lean`，lane-leafa-gen）；本节用它，不另立一条（见 §16d 的改正段）。

### §16b 机制：递归锥 ＋ Bézout ＋ 2D Cramer

`Section8/HalfPlane.lean` 已有 `recCone` / `toReal_mem_recCone` / `smul_mem_recCone` /
`add_mem_recCone` / `eq_preimage_convHullOf`。合起来给 `mem_of_cone_lside`：`U` 格凸、含 `z₀`、
对 `+x` 与 `+y` 封闭 ⟹ 凡实系数非负组合 `toReal z₀ + a·x + b·y` 形状的**整点**都在 `U` 里。

要命中高度 `h`，取 `⟪n_J, q⟫ = 1` 的 Bézout 向量 `q`（用 `Primitive n_J`），令
`r := h − ⟪n_J, z₀⟫ ≥ 0`，见证点是

    w := z₀ + r·q + |r·det q p|·v_J

它的高度逐字是 `h`（`⟪n_J,q⟫ = 1`、`⟪n_J,v_J⟫ = 0`）。把 `w − z₀` 在基 `(v_J, p)` 下解开，
系数由 2D Cramer 给出且**分母只有 `Δ := det v_J p`**：

    a = |r·det q p| + (r·det q p)/Δ,   b = (r·det v_J q)/Δ = r/⟪n_J,p⟫

`b ≥ 0` 用 `Δ = det v_J q · ⟪n_J,p⟫`（Binet–Cauchy 的一格，只吃 `⟪n_J,v_J⟫ = 0` 与
`⟪n_J,q⟫ = 1`）；`a ≥ 0` 用 `|Δ| ≥ 1` ⟹ `|(r·k)/Δ| ≤ |r·k|`——**沿 `v_J` 平移的自由度**正是
把点推回锥内的那一步。`Δ ≠ 0` 不是新前提：`det_ne_zero_of_level_lside` 从
`⟪n_J,v_J⟫ = 0` ＋ `v_J ≠ 0` ＋ `⟪n_J,p⟫ ≠ 0` 推出来。

### §16c 两座台架之间的差（§52）

| 前提 | §15（反例成立） | §16（正面成立） |
|---|---|---|
| `p = −c·vl`、`0 < c`、`Primitive vl`、`Primitive nJ` | 有 | 只用 `Primitive nJ` |
| `⋃ hatOf` 非空、下有界 `cJ`、对 `+p` 封闭、`⟪n_J,p⟫ ≠ 0` | 有 | 有（下有界只用来定 `0 < ⟪n_J,p⟫`） |
| `⟪n_J,v_J⟫ = 0`、`v_J ≠ 0` | 有 | 有 |
| 对 `+v_J` 封闭（`rec_vJ`） | **没列进派工表，但见证恰好满足** | 有，且承重 |
| `IsLatticeConvexRegion (⋃ hatOf)` | **没有**（见证不是格凸） | 有，且承重 |

⟹ 两座台架的差**只有最后一行**。`stock_witness_recvJ_not_latticeConvex_lside` 是这句话的
内核收据：§15 那个见证集 `{z | 0 ≤ z.2 ∧ z.2 偶}` 对 `+(1,0)` 封闭（`v_J` 方向那条它满足），
但不格凸——`(0,0)` 与 `(0,2)` 在里面而中点 `(0,1)` 不在。§15 的结论**不撤回**：它说的是
「派工列出的那张现货表推不出覆盖」，那仍然成立；本节补的是「表漏了哪一条」。

### §16d 接链形态：**零 binder**

⚠ **本节第一版写错了一句，这里改正。** 第一版把 `hrecvJ` / `hrecp` / `hdp` 写成 binder，
并说「一条都不是该结构的字段」。三条都不对：

* `rec_p` 与 `dot_nJ_p` **就是** `ChainDataGeomParts` 的字段（我点开结构逐字核对了；本文件
  §10 的注里本来写对了，§16 第一版是回退）。
* `rec_vJ` 有主仓生产者：`LaneLeafAGenRecVJ.rec_vJ_of_parts`（`RecVJFromParts.lean`，
  lane-leafa-gen），它走 `ItemII.rec_vJ_of_bottom`，六个输入全是字段（`hsweep` / `hhp` /
  `hswept` / `F.dot_nJ_vJ` / `bottom`）＋ 一条格凸性。⟹ 它**不经过**
  `RecVJComb.parts_rec_vJ` 的 `hcomb` 侧条件，所以「共线格里 `hcomb` 不可满足」
  （`TowerHlevTile.not_hcomb_of_collinear`；别人的收据，我未复跑）**不挡** `rec_vJ`。
* 格凸性也已有主仓声明 `LaneLeafAGenRecVJ.latticeConvex_of_parts`，与本节第一版的
  `latticeConvex_iUnion_of_parts_lside` 是**同输入同证法的同一件事** ⟹ 按 §56 那是重复、
  不是第二份证据，本轮删掉我那条、改用它。**为什么没先查到**：我按 `rec_vJ` 的语句形状
  grep 过，却没按「`IsLatticeConvexRegion (⋃ i, hatOf …)` 由 parts 供」这个形状 grep——
  §58 的教训是「按形状不按名字」，我这次形状选窄了。

⟹ `heights_covered_of_parts_lside` / `residue_coverage_of_parts_lside` 现在**只吃一个
`ChainDataGeomParts` 实例**（＋高度 `h`／模 `g` 与残类 `m`）。共线格的残类覆盖因此按
**链上成立**记账，不再记「前提待生产者兑现」。字段来源：`maxA` / `hfin` / `AhatMono`（格凸）、
`bottom` / `hsweep` / `hswept` / `hhp` / `F.dot_nJ_vJ`（`rec_vJ`）、`rec_p`、`dot_nJ_p`、
`ahat_nonempty`、`nJ_prim`、`vJ_prim`。

⚠ 仍未兑现的是**结构本身**：`RegionSteps.exists_chainData` 造不造得出
`ChainDataGeomParts` 是另一格的欠账，本节不碰。

⚠ **射程（勿放大）**

1. 本节证的是**高度谱**无间隙：从 `⋃ hatOf` 里任一点的高度起，每个整数高度都被取到。
   它**没有**说 `⋃ hatOf` 等于任何半平面或楔形，也没碰 `Â_∞` 的上界那一半。
2. 共线／横截两格本节都不区分——`det vl vJ1` 在这里根本不出现。这是好消息（结论对两格同时
   成立），但也意味着它**不**替代共线格里任何以 `det vl vJ1 = 0` 为前提的结论。
3. `mem_of_cone_lside` 的 `recCone` 只给**单侧**射线（`rec_vJ` 只给 `+v_J`）；本节不需要双向，
   也没主张双向。 -/

/-- `⟪n,v⟫ = 0`、`v ≠ 0`、`⟪n,p⟫ ≠ 0` ⟹ `det v p ≠ 0`（2D：水平方向与非水平方向必无关）。 -/
theorem det_ne_zero_of_level_lside {n v p : ℤ × ℤ} (hlevel : dot n v = 0) (hv : v ≠ 0)
    (hp : dot n p ≠ 0) : det v p ≠ 0 := by
  intro hdet
  apply hp
  have hl : n.1 * v.1 + n.2 * v.2 = 0 := hlevel
  have hd : v.1 * p.2 - v.2 * p.1 = 0 := hdet
  have h1 : v.1 * dot n p = 0 := by
    simp only [dot]
    linear_combination p.1 * hl + n.2 * hd
  have h2 : v.2 * dot n p = 0 := by
    simp only [dot]
    linear_combination p.2 * hl - n.1 * hd
  rcases mul_eq_zero.mp h1 with h | h
  · rcases mul_eq_zero.mp h2 with h' | h'
    · exact absurd (Prod.ext h h' : v = 0) hv
    · exact h'
  · exact h

/-- 落点判据：`U` 格凸、含 `z₀`、对 `+x` 与 `+y` 封闭，则凡 `toReal z₀ + a·x + b·y`
（`a, b : ℝ` 非负）形状的整点都在 `U` 里。走 `Section8/HalfPlane.lean` 的 `recCone` 机器：
`toReal_mem_recCone` 把两条平移封闭变成锥元，`smul_mem_recCone` / `add_mem_recCone` 给非负组合，
`eq_preimage_convHullOf` 把回落到整点这一步交给格凸本身。 -/
theorem mem_of_cone_lside {U : Set (ℤ × ℤ)} (hconv : IsLatticeConvexRegion U)
    {z₀ w x y : ℤ × ℤ} (hz₀ : z₀ ∈ U)
    (hx : ∀ z ∈ U, z + x ∈ U) (hy : ∀ z ∈ U, z + y ∈ U)
    {aa bb : ℝ} (ha : 0 ≤ aa) (hb : 0 ≤ bb)
    (hiden : toReal w = toReal z₀ + (aa • toReal x + bb • toReal y)) : w ∈ U := by
  have hUeq : U = toReal ⁻¹' convHullOf U := eq_preimage_convHullOf hconv
  have hz₀C : toReal z₀ ∈ convHullOf U := by rw [hUeq] at hz₀; exact hz₀
  have hcone : aa • toReal x + bb • toReal y ∈ recCone U :=
    add_mem_recCone (smul_mem_recCone ha (toReal_mem_recCone hx))
      (smul_mem_recCone hb (toReal_mem_recCone hy))
  rw [hUeq]
  show toReal w ∈ convHullOf U
  rw [hiden]
  exact hcone (toReal z₀) hz₀C

/-- ⭐ **高度谱无间隙。** `U` 格凸、对 `+v_J`（水平）与 `+p`（升高）封闭、`n_J` 本原 ⟹
从任一 `z₀ ∈ U` 的高度起，每个整数高度都被 `U` 取到。见证点是
`z₀ + r·q + |r·det q p|·v_J`（`q` 是 Bézout 向量，`r = h − ⟪n_J,z₀⟫`），§16b 有推导。 -/
theorem heights_covered_of_latticeConvex_lside
    {U : Set (ℤ × ℤ)} {nJ vJ p z₀ : ℤ × ℤ} {h : ℤ}
    (hconv : IsLatticeConvexRegion U) (hprim : Primitive nJ) (hz₀ : z₀ ∈ U)
    (hrecvJ : ∀ z ∈ U, z + vJ ∈ U) (hrecp : ∀ z ∈ U, z + p ∈ U)
    (hlevel : dot nJ vJ = 0) (hvJ : vJ ≠ 0) (hup : 0 < dot nJ p)
    (hh : dot nJ z₀ ≤ h) :
    ∃ z ∈ U, dot nJ z = h := by
  classical
  obtain ⟨q, hq⟩ : ∃ q : ℤ × ℤ, dot nJ q = 1 := by
    obtain ⟨qu, qv, hbez⟩ := hprim
    exact ⟨(qu, qv), by simp only [dot]; linarith⟩
  obtain ⟨r, hr0, hrEq⟩ : ∃ r : ℤ, 0 ≤ r ∧ h = dot nJ z₀ + r :=
    ⟨h - dot nJ z₀, by omega, by ring⟩
  have hl : nJ.1 * vJ.1 + nJ.2 * vJ.2 = 0 := hlevel
  have hq' : nJ.1 * q.1 + nJ.2 * q.2 = 1 := hq
  have hdne : dot nJ p ≠ 0 := ne_of_gt hup
  have hDne : det vJ p ≠ 0 := det_ne_zero_of_level_lside hlevel hvJ hdne
  -- `det vJ p = det vJ q · ⟪n_J,p⟫`（Binet–Cauchy 的一格，只用 `hlevel` 与 `hq`）
  have hjd : det vJ q * dot nJ p = det vJ p := by
    simp only [det, dot]
    linear_combination (vJ.1 * p.2 - vJ.2 * p.1) * hq' + (p.1 * q.2 - p.2 * q.1) * hl
  have hjne : det vJ q ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hjd
    exact hDne hjd.symm
  have hDR : ((det vJ p : ℤ) : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hDne
  have hjR : ((det vJ q : ℤ) : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hjne
  have hdR : (0 : ℝ) < ((dot nJ p : ℤ) : ℝ) := by exact_mod_cast hup
  refine ⟨z₀ + r • q + |r * det q p| • vJ, ?_, ?_⟩
  · refine mem_of_cone_lside hconv hz₀ hrecvJ hrecp
      (aa := ((det vJ p : ℤ) : ℝ)⁻¹ *
        ((|r * det q p| * det vJ p + r * det q p : ℤ) : ℝ))
      (bb := ((det vJ p : ℤ) : ℝ)⁻¹ * ((r * det vJ q : ℤ) : ℝ)) ?_ ?_ ?_
    · -- `aa = |r·k| + (r·k)/Δ ≥ 0`，因为 `|Δ| ≥ 1` ⟹ `|(r·k)/Δ| ≤ |r·k|`
      have hkey : ((det vJ p : ℤ) : ℝ)⁻¹ *
            ((|r * det q p| * det vJ p + r * det q p : ℤ) : ℝ)
          = ((|r * det q p| : ℤ) : ℝ)
            + ((r * det q p : ℤ) : ℝ) / ((det vJ p : ℤ) : ℝ) := by
        field_simp
        push_cast
        ring
      rw [hkey]
      have hD1 : (1 : ℝ) ≤ |((det vJ p : ℤ) : ℝ)| := by
        have h1 : (1 : ℤ) ≤ |det vJ p| := Int.one_le_abs hDne
        have h2 : ((1 : ℤ) : ℝ) ≤ ((|det vJ p| : ℤ) : ℝ) := by exact_mod_cast h1
        rwa [Int.cast_abs, Int.cast_one] at h2
      have habs : |((r * det q p : ℤ) : ℝ) / ((det vJ p : ℤ) : ℝ)|
          ≤ ((|r * det q p| : ℤ) : ℝ) := by
        rw [abs_div, Int.cast_abs]
        exact div_le_self (abs_nonneg _) hD1
      have := (abs_le.mp habs).1
      linarith
    · -- `bb = r/⟪n_J,p⟫ ≥ 0`
      have hkey : ((det vJ p : ℤ) : ℝ)⁻¹ * ((r * det vJ q : ℤ) : ℝ)
          = (r : ℝ) / ((dot nJ p : ℤ) : ℝ) := by
        rw [← hjd]
        push_cast
        field_simp
      rw [hkey]
      exact div_nonneg (by exact_mod_cast hr0) (le_of_lt hdR)
    · -- 2D Cramer：`Δ·(r·q + s·v_J) = (s·Δ + r·det q p)·v_J + (r·det v_J q)·p`，纯 `ring`
      have hDR2 : ((vJ.1 : ℝ) * (p.2 : ℝ) - (vJ.2 : ℝ) * (p.1 : ℝ)) ≠ 0 := by
        intro h0
        apply hDne
        have hcast : ((det vJ p : ℤ) : ℝ) = 0 := by
          simp only [det]; push_cast; linarith
        exact_mod_cast hcast
      have hDR3 : ((p.2 : ℝ) * (vJ.1 : ℝ) - (p.1 : ℝ) * (vJ.2 : ℝ)) ≠ 0 := by
        intro h0; exact hDR2 (by linarith)
      simp only [toReal, Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
        Prod.smul_snd, smul_eq_mul, det]
      constructor
      · push_cast
        field_simp [hDR2, hDR3]
        ring
      · push_cast
        field_simp [hDR2, hDR3]
        ring
  · rw [hrEq]
    simp only [dot, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    linear_combination r * hq' + (|r * det q p| : ℤ) * hl

/-- 残类覆盖：任给模 `g > 0` 与残类 `m`，`U` 里有点的高度落在该残类。高度谱无间隙的直接推论
（连续整数高度全被取到 ⟹ 任何模的任何残类都被取到）。 -/
theorem residue_covered_of_latticeConvex_lside
    {U : Set (ℤ × ℤ)} {nJ vJ p z₀ : ℤ × ℤ}
    (hconv : IsLatticeConvexRegion U) (hprim : Primitive nJ) (hz₀ : z₀ ∈ U)
    (hrecvJ : ∀ z ∈ U, z + vJ ∈ U) (hrecp : ∀ z ∈ U, z + p ∈ U)
    (hlevel : dot nJ vJ = 0) (hvJ : vJ ≠ 0) (hup : 0 < dot nJ p)
    (g m : ℤ) (hg : 0 < g) :
    ∃ z ∈ U, dot nJ z % g = m % g := by
  obtain ⟨t, ht⟩ : ∃ t : ℤ, dot nJ z₀ ≤ m + t * g := by
    refine ⟨|dot nJ z₀ - m|, ?_⟩
    have h1 : dot nJ z₀ - m ≤ |dot nJ z₀ - m| := le_abs_self _
    have h2 : (0 : ℤ) ≤ |dot nJ z₀ - m| := abs_nonneg _
    nlinarith
  obtain ⟨z, hzU, hz⟩ :=
    heights_covered_of_latticeConvex_lside hconv hprim hz₀ hrecvJ hrecp hlevel hvJ hup ht
  exact ⟨z, hzU, by rw [hz]; exact Int.add_mul_emod_self_right _ _ _⟩

/-- **两座台架之差的内核收据（§16c）。** §15 的见证集对 `+(1,0)`（即 `v_J` 方向）封闭——
所以 `rec_vJ` **不是**分界线；它不格凸——`(0,0)` 与 `(0,2)` 在里面而中点 `(0,1)` 不在。
⟹ §15 与 §16 之间承重的输入**只有** `IsLatticeConvexRegion` 一条。 -/
theorem stock_witness_recvJ_not_latticeConvex_lside :
    (∀ z ∈ {z : ℤ × ℤ | 0 ≤ z.2 ∧ z.2 % 2 = 0},
      z + ((1 : ℤ), (0 : ℤ)) ∈ {z : ℤ × ℤ | 0 ≤ z.2 ∧ z.2 % 2 = 0}) ∧
    ¬ IsLatticeConvexRegion {z : ℤ × ℤ | 0 ≤ z.2 ∧ z.2 % 2 = 0} := by
  constructor
  · intro z hz
    simp only [Set.mem_setOf_eq, Prod.snd_add] at hz ⊢
    omega
  · rintro ⟨C, hCconv, -, hCeq⟩
    have h0 : ((0 : ℤ), (0 : ℤ)) ∈ {z : ℤ × ℤ | 0 ≤ z.2 ∧ z.2 % 2 = 0} := by
      simp only [Set.mem_setOf_eq]; omega
    have h2 : ((0 : ℤ), (2 : ℤ)) ∈ {z : ℤ × ℤ | 0 ≤ z.2 ∧ z.2 % 2 = 0} := by
      simp only [Set.mem_setOf_eq]; omega
    rw [hCeq] at h0 h2
    have hmid := hCconv h0 h2 (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    have he : (1 / 2 : ℝ) • toReal ((0 : ℤ), (0 : ℤ))
        + (1 / 2 : ℝ) • toReal ((0 : ℤ), (2 : ℤ)) = toReal ((0 : ℤ), (1 : ℤ)) := by
      simp only [toReal, Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk, Prod.ext_iff]
      norm_num
    rw [he] at hmid
    have hbad : ((0 : ℤ), (1 : ℤ)) ∈ {z : ℤ × ℤ | 0 ≤ z.2 ∧ z.2 % 2 = 0} := by
      rw [hCeq]; exact hmid
    simp only [Set.mem_setOf_eq] at hbad
    omega

/-- **接链形态的公共前件**：`ChainDataGeomParts` 的字段一次性兑现抽象版的七条前提。
`hrecvJ` 走 `LaneLeafAGenRecVJ.rec_vJ_of_parts`（`RecVJFromParts.lean`），格凸走
`LaneLeafAGenRecVJ.latticeConvex_of_parts`，其余是字段的直接投影。 -/
private theorem parts_stock_lside {α : Type*} {η xper : Config α}
    {vl p gen : ℤ × ℤ} {S : Finset (ℤ × ℤ)}
    (cp : Nivat.ChainAsm.Aparts.ChainDataGeomParts η xper vl p S gen) :
    IsLatticeConvexRegion (⋃ i, hatOf cp.A cp.kk vl i) ∧
      Primitive cp.nJ ∧
      (∀ z ∈ ⋃ i, hatOf cp.A cp.kk vl i, z + cp.vJ ∈ ⋃ i, hatOf cp.A cp.kk vl i) ∧
      (∀ z ∈ ⋃ i, hatOf cp.A cp.kk vl i, z + p ∈ ⋃ i, hatOf cp.A cp.kk vl i) ∧
      dot cp.nJ cp.vJ = 0 ∧ cp.vJ ≠ 0 ∧ 0 < dot cp.nJ p := by
  have hlb : ∀ z ∈ ⋃ i, hatOf cp.A cp.kk vl i, cp.cJ ≤ dot cp.nJ z := by
    intro z hz
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
    have hmem := cp.hhp i hi
    simpa [Nivat.LE2.halfPlaneGE, Set.mem_setOf_eq] using hmem
  have h0 : 0 ≤ dot cp.nJ p := dot_nonneg_of_rec cp.ahat_nonempty hlb cp.rec_p
  have hvJ : cp.vJ ≠ 0 := by
    intro hz
    obtain ⟨x, y, hxy⟩ := cp.vJ_prim
    rw [hz] at hxy
    simp only [Prod.fst_zero, Prod.snd_zero, mul_zero, add_zero] at hxy
    exact absurd hxy (by norm_num)
  exact ⟨Nivat.LaneLeafAGenRecVJ.latticeConvex_of_parts cp, cp.nJ_prim,
    Nivat.LaneLeafAGenRecVJ.rec_vJ_of_parts cp, cp.rec_p, cp.F.dot_nJ_vJ, hvJ,
    lt_of_le_of_ne h0 (Ne.symm cp.dot_nJ_p)⟩

/-- ⭐ **接链形态的高度谱无间隙（§16d），零 binder。** 只吃一个 `ChainDataGeomParts` 实例：
从 `⋃ i, hatOf A kk vl i` 里任一点 `z₀` 的高度起，每个整数高度 `h` 都被取到。 -/
theorem heights_covered_of_parts_lside {α : Type*} {η xper : Config α}
    {vl p gen : ℤ × ℤ} {S : Finset (ℤ × ℤ)}
    (cp : Nivat.ChainAsm.Aparts.ChainDataGeomParts η xper vl p S gen)
    {z₀ : ℤ × ℤ} (hz₀ : z₀ ∈ ⋃ i, hatOf cp.A cp.kk vl i) {h : ℤ}
    (hh : dot cp.nJ z₀ ≤ h) :
    ∃ z ∈ ⋃ i, hatOf cp.A cp.kk vl i, dot cp.nJ z = h := by
  obtain ⟨hconv, hprim, hrecvJ, hrecp, hlevel, hvJ, hup⟩ := parts_stock_lside cp
  exact heights_covered_of_latticeConvex_lside hconv hprim hz₀ hrecvJ hrecp hlevel hvJ hup hh

/-- ⭐ **接链形态的残类覆盖（§16d），零 binder。** 共线格与横截格同时成立（`det vl vJ1`
在本条里根本不出现）。

⛔ **射程（第 238 轮补，lane-tower-hbase 读出、集成者从证明项复核、我自己复读了源码）：本条
不能拿来产 `bottom`，那是循环的。** 「零 binder」只对**签名**为真；`cp` 里被**用掉**的字段
包含 `bottom`：本条经 `parts_stock_lside` 取 `hrecvJ`，而那一项是
`LaneLeafAGenRecVJ.rec_vJ_of_parts cp`（`RecVJFromParts.lean`），其证明体的最后一个实参逐字
就是 `c.bottom`。⟹ 「本条 ＋ `EnvRefuteCover.heights_iff_cover` ⟹ `bottom` 的合取 1」这条看
起来很短的路，整体是 `bottom ⟹ 覆盖 ⟹ 合取 1`，**不减债**。
⚠ 勿放大：对任何**不是 `bottom`** 的消费者本条照旧有效，共线格残类覆盖仍按链上成立记。 -/
theorem residue_coverage_of_parts_lside {α : Type*} {η xper : Config α}
    {vl p gen : ℤ × ℤ} {S : Finset (ℤ × ℤ)}
    (cp : Nivat.ChainAsm.Aparts.ChainDataGeomParts η xper vl p S gen)
    (g m : ℤ) (hg : 0 < g) :
    ∃ z ∈ ⋃ i, hatOf cp.A cp.kk vl i, dot cp.nJ z % g = m % g := by
  obtain ⟨z₀, hz₀⟩ := cp.ahat_nonempty
  obtain ⟨hconv, hprim, hrecvJ, hrecp, hlevel, hvJ, hup⟩ := parts_stock_lside cp
  exact residue_covered_of_latticeConvex_lside hconv hprim hz₀ hrecvJ hrecp hlevel hvJ hup g m hg

/-! ## §17 `bottom` 的**前两条**不是独立义务：它们由 §16 ＋ `rec_vJ` 推出

### §17a 问题

`ItemII.rec_vJ_of_bottom` 只消费 `bottom 0` 的**前两条**合取——证明体里逐字是
`obtain ⟨z₀, L, hz₀, hline, -, -⟩ := bottom 0`（我点开读了证明体，不是看签名）。
主仓另有 `Colle35.not_bottom_of_shell_data`（`ANormal.lean`）说「`bottom` 推不出自 shell 数据」，
反模型是 `A = {z | z.2 = 0}`、`nJ = (0,1)`、`vJ = (1,0)`、`vJ1 = (0,-2)`、`cJ = 0`：
可达层是偶数，而 `cJ - 1 = -1` 命不中。**那正是一个高度谱的洞。**

### §17b 答

§16 把这个失效模式整条封掉。`MaxEnv.reachSet U vJ1 = {g + t·vJ1 : g ∈ U, t ∈ ℕ}`，其层集是
`{h - t·|⟪n_J,vJ1⟫| : h ∈ U 的高度谱, t ∈ ℕ}`；§16 说高度谱从某点起**含全部整数**，
于是对**任意**目标层 `c`，取 `h := c + t·|⟪n_J,vJ1⟫|`（`t` 取够大即可）就有 `z ∈ U` 恰在 `h` 层，
`t` 步 `vJ1` 扫回来正好落在 `c` 层。再用 `rec_vJ` 把整条 `+v_J` 射线搬进去
（`⟪n_J,v_J⟫ = 0` ⟹ 平移不改层），`L` 可以取 **0**。

⟹ `reachSet_ray_at_level_lside`：任意层 `c` 都有 `z₀` ＋ 整条 `+v_J` 射线落在 `reachSet U vJ1`。
`bottom_first_two_of_stock_lside` 是它在 `c := cJ - ε - 1`、`L := 0` 的实例，形状逐字是
`bottom` 的前两条。

### §17c 与 `not_bottom_of_shell_data` 的关系（§113：两条互不包含，我打了反方向）

不冲突，两张前提表互不包含：它那张**没有** `rec_p`、没有格凸、没有 `Primitive n_J`；
我这张**没有** `hhp`。承重的差是 `rec_p`——`not_bottom_witness_no_rec_p_lside` 是内核收据：
那个反模型的 `A = {z | z.2 = 0}` **根本不存在**满足 `rec_p` 且 `0 < ⟪n_J,p⟫` 的 `p`
（`(0,0) ∈ A` ⟹ `p ∈ A` ⟹ `p.2 = 0` ⟹ `⟪(0,1),p⟫ = 0`）。
⟹ 那条反模型**在链上不出现**，因为 `rec_p` 与 `dot_nJ_p` 都是 `ChainDataGeomParts` 的字段。

⚠ **我没有主张的（勿放大）**

1. 这**不是**说 `bottom` 是多余字段。`bottom` 有四条合取，本节只碰前两条；后两条
   （`b - F.a` 的平移族、shell 的逐层分解）一个字都没碰。
2. 这**不是**说链上可以把 `bottom` 删掉。§16 经 `LaneLeafAGenRecVJ.rec_vJ_of_parts` 压在
   `bottom` 上，所以拿一个 `ChainDataGeomParts` 实例去推 `bottom`(i,ii) 是**循环**的。
   本节因此把定理写成**裸前提形**，一个 `ChainDataGeomParts` 都不吃。它的用法是给生产者
   （`RegionSteps.exists_chainData`）一个**替换选项**：供 `rec_vJ` 即可，不必单独兑现
   `bottom`(i,ii)。
3. `not_bottom_of_shell_data` 的结论**不撤回**：在它自己那张前提表上它成立。 -/

/-- **任意层上的 `+v_J` 射线落在 `reachSet U vJ1` 里（§17b）。** 由 §16 的高度谱无间隙 ＋
`rec_vJ` ＋ `⟪n_J,vJ1⟫ < 0` 推出；`L` 可以取 `0`，所以结论里不留 `L`。 -/
theorem reachSet_ray_at_level_lside
    {U : Set (ℤ × ℤ)} {nJ vJ vJ1 p : ℤ × ℤ}
    (hconv : IsLatticeConvexRegion U) (hprim : Primitive nJ) (hne : U.Nonempty)
    (hrecvJ : ∀ z ∈ U, z + vJ ∈ U) (hrecp : ∀ z ∈ U, z + p ∈ U)
    (hlevel : dot nJ vJ = 0) (hvJ : vJ ≠ 0) (hup : 0 < dot nJ p)
    (hsweep : dot nJ vJ1 < 0) (c : ℤ) :
    ∃ z₀ : ℤ × ℤ, dot nJ z₀ = c ∧
      ∀ k : ℤ, 0 ≤ k → z₀ + k • vJ ∈ MaxEnv.reachSet U vJ1 := by
  obtain ⟨zb, hzb⟩ := hne
  -- 目标层 `c` 在 `U` 之下时，先往上走到 `c + t·D`（`D := |⟪n_J,vJ1⟫|`），再 `t` 步扫回来。
  obtain ⟨D, hD, hDpos⟩ : ∃ D : ℤ, dot nJ vJ1 = -D ∧ 0 < D :=
    ⟨-dot nJ vJ1, by ring, by omega⟩
  obtain ⟨t, ht⟩ : ∃ t : ℕ, dot nJ zb - c ≤ (t : ℤ) :=
    ⟨(dot nJ zb - c).toNat, Int.self_le_toNat _⟩
  have ht0 : (0 : ℤ) ≤ (t : ℤ) := Int.natCast_nonneg t
  have hge : dot nJ zb ≤ c + (t : ℤ) * D := by nlinarith
  obtain ⟨z, hzU, hz⟩ :=
    heights_covered_of_latticeConvex_lside hconv hprim hzb hrecvJ hrecp hlevel hvJ hup hge
  refine ⟨z + (t : ℤ) • vJ1, ?_, ?_⟩
  · rw [dot_add, mpos_dot_zsmul, hz, hD]
    ring
  · intro k hk
    refine MaxEnv.mem_reachSet.mpr ⟨z + k • vJ, ?_, t, ?_⟩
    · have hiter := mpos_rec_iter hrecvJ k.toNat z hzU
      rwa [Int.toNat_of_nonneg hk] at hiter
    · abel

/-- **`bottom` 的前两条，从裸现货推出（§17b）。** 形状逐字是 `ChainDataGeomParts.bottom` 的
第一、第二条合取（取 `L := 0`），也正是 `ItemII.rec_vJ_of_bottom` 证明体里唯一用到的两条。
⚠ 一个 `ChainDataGeomParts` 都不吃——吃了就循环，见 §17c 第 2 条。 -/
theorem bottom_first_two_of_stock_lside
    {U : Set (ℤ × ℤ)} {nJ vJ vJ1 p : ℤ × ℤ} {cJ : ℤ}
    (hconv : IsLatticeConvexRegion U) (hprim : Primitive nJ) (hne : U.Nonempty)
    (hrecvJ : ∀ z ∈ U, z + vJ ∈ U) (hrecp : ∀ z ∈ U, z + p ∈ U)
    (hlevel : dot nJ vJ = 0) (hvJ : vJ ≠ 0) (hup : 0 < dot nJ p)
    (hsweep : dot nJ vJ1 < 0) (ε : ℕ) :
    ∃ (z₀ : ℤ × ℤ) (L : ℤ),
      dot nJ z₀ = cJ - (ε : ℤ) - 1 ∧
      ∀ k : ℤ, L ≤ k → z₀ + k • vJ ∈ MaxEnv.reachSet U vJ1 := by
  obtain ⟨z₀, hz₀, hray⟩ := reachSet_ray_at_level_lside hconv hprim hne hrecvJ hrecp hlevel
    hvJ hup hsweep (cJ - (ε : ℤ) - 1)
  exact ⟨z₀, 0, hz₀, hray⟩

/-- **`not_bottom_of_shell_data` 的反模型在链上不出现（§17c）。** 它的 `A = {z | z.2 = 0}`
不存在满足 `rec_p` 且 `0 < ⟪(0,1), p⟫` 的 `p`；而 `rec_p` 与 `dot_nJ_p` 都是
`ChainDataGeomParts` 的字段。⟹ 那条反模型否掉的是一张**不含 `rec_p`** 的前提表。 -/
theorem not_bottom_witness_no_rec_p_lside :
    ¬ ∃ p : ℤ × ℤ,
      (∀ g ∈ {z : ℤ × ℤ | z.2 = 0}, g + p ∈ {z : ℤ × ℤ | z.2 = 0}) ∧
        0 < dot ((0 : ℤ), (1 : ℤ)) p := by
  rintro ⟨p, hrec, hpos⟩
  have h0 : ((0 : ℤ), (0 : ℤ)) ∈ {z : ℤ × ℤ | z.2 = 0} := by norm_num
  have hp := hrec _ h0
  simp only [Set.mem_setOf_eq, Prod.snd_add] at hp
  simp only [dot] at hpos
  omega

/-! ## §18 `ahat_nonempty` 是免费的：`halign` 的 `IsGreatest` 左半直接给出

### §18a 结论

`ChainDataGeomParts.ahat_nonempty : (⋃ i, hatOf A kk vl i).Nonempty`（`ChainPartsFeed.lean`）
**不欠任何新前提**：它是 `halign` 的一个投影。

`halign i : IsGreatest {t : ℤ | g₁ + t • vl ∈ hatOf A kk vl i ∧ dot nℓ (g₁ + t • vl) = cz} 0`，
而 `IsGreatest S a` 的**左半**逐字就是 `a ∈ S`。在 `i := 0`、`t := 0` 处求值即得
`g₁ + (0 : ℤ) • vl ∈ hatOf A kk vl 0`，化简是 `g₁ ∈ hatOf A kk vl 0`，再进 `⋃`。
⟹ 见证点是 `g₁` 本身，即原文 `b3_colle2.txt:488` 的「`A_1 ∩ ℓ^{(-)}` 沿 `ℓ^{(-)}` 定向的末点」。

### §18b 为什么写成两条

`ahat_nonempty_of_halign_lside` 是**裸形**：只吃 `halign`，不吃任何结构、不吃 `PartsChainFeed`。
它是可复用的那一条。

`exists_parts_chain_half_ahat_nonempty_lside` 是**接线形**：前提表与
`PartsChainFeed.exists_parts_chain_half` 逐字符相同，结论在它原有九个合取支后面**追加**
`ahat_nonempty`。它存在的理由不是数学，是护栏——它编译通过，就同时证明了集成者第 237 轮那条
导出确实能被外部消费（`halign` 真的是第九个合取支、类型真的对得上）。若哪天
`exists_parts_chain_half` 的合取顺序或类型变了，本条**先红**。

### §18c 本节**不**主张什么

1. **不**主张洞 1 的几何侧因此少一条实质义务。`ahat_nonempty` 本来就是 37 条字段里最轻的一条；
   本节把它从「未兑现」挪到「已兑现」，闸门不动（硬规矩 1）。
2. **不**主张 `hatOf A kk vl 0` 非空对每个 `i` 都免费——`halign` 是 `∀ i` 的，所以逐格也免费，
   但本节只把 `i = 0` 那一格写进结论，因为消费者字段要的就是并集非空。
3. **不**触碰 `halign` 自己的来源。`halign` 由 `exists_parts_chain_half` 的第九个合取支给出，
   而那条是集成者第 237 轮落地的；我复读了它的 `exact` 那一行（末项 `rd.halign`），
   但**没有**独立复跑他的 `check1.sh`（§55）。
-/

/-- **`ahat_nonempty` 的裸形产者（§18a）。** 只吃 `halign`，一个结构都不吃。

见证点是 `g₁`（原文 `b3_colle2.txt:488` 的端点），由 `IsGreatest` 的左半在 `t = 0` 处给出。 -/
theorem ahat_nonempty_of_halign_lside
    {A : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ} {vl nℓ g₁ : ℤ × ℤ} {cz : ℤ}
    (halign : ∀ i, IsGreatest
      {t : ℤ | g₁ + t • vl ∈ hatOf A kk vl i ∧ dot nℓ (g₁ + t • vl) = cz} 0) :
    (⋃ i, hatOf A kk vl i).Nonempty := by
  have h0 := (halign 0).1
  simp only [Set.mem_setOf_eq, zero_smul, add_zero] at h0
  exact ⟨g₁, Set.mem_iUnion.mpr ⟨0, h0.1⟩⟩

/-- **接线护栏（§18b）。** 前提表与 `PartsChainFeed.exists_parts_chain_half` 逐字符相同，
结论是它的九个合取支 ＋ 第十条 `ahat_nonempty`。

⟹ 从 `exists_chainData` 现有的 binder 出发，`ChainDataGeomParts` 的链侧十三项**再加上**
`ahat_nonempty`，全部零新前提兑现。 -/
theorem exists_parts_chain_half_ahat_nonempty_lside {ξ xper : Config ℤ}
    (d : DecompDataZ ξ) {ℓ nℓ vl : ℤ × ℤ} (cz : ℤ)
    (hxper : xper ∈ orbitClosure ξ)
    (hvl_ne : vl ≠ 0) (hvl_prim : Primitive vl)
    (hℓ_nel : ℓ ∈ Colle45.NonExpansiveLine ξ)
    (hℓ_pos : Colle45.IsOneSidedNonexpansive ξ ℓ)
    (hℓ_neg : Colle45.IsOneSidedNonexpansive ξ (-ℓ))
    (hdet_ℓ : dot ℓ vl = 0)
    (hnℓ_prim : Primitive nℓ) (hnℓ_perp : dot nℓ vl = 0)
    (hcase2 : Nivat.ColleReg.Case2 ξ xper d.toDecompData.Sphi vl) :
    ∃ (B A : ℕ → Set (ℤ × ℤ)) (u : ℕ → ℤ × ℤ) (kk : ℕ → ℕ) (g₁ : ℤ × ℤ),
      (∀ (v : ℤ × ℤ) (T : Set (ℤ × ℤ)),
          EnvOf (↑d.toDecompData.Sphi : Set (ℤ × ℤ)) T →
          EnvOf (↑d.toDecompData.Sphi : Set (ℤ × ℤ)) {z | z + v ∈ T}) ∧
      (∀ i, EnvOf (↑d.toDecompData.Sphi : Set (ℤ × ℤ)) (B i)) ∧
      (∀ i, IsMaxEnvIn (EnvOf (↑d.toDecompData.Sphi : Set (ℤ × ℤ)))
          (canonA ξ xper vl B u i) (A i)) ∧
      (∀ i, B i ⊆ A i) ∧
      (∀ i, A i ⊆ B (i + 1)) ∧
      (∀ i j, i ≤ j → hatOf A kk vl i ⊆ hatOf A kk vl j) ∧
      (∀ i, (hatOf A kk vl i).Finite) ∧
      (∀ i j, i ≤ j → kk i ≤ kk j) ∧
      (∀ i, IsGreatest
          {t : ℤ | g₁ + t • vl ∈ hatOf A kk vl i ∧ dot nℓ (g₁ + t • vl) = cz} 0) ∧
      (⋃ i, hatOf A kk vl i).Nonempty := by
  obtain ⟨B, A, u, kk, g₁, h1, h2, h3, h4, h5, h6, h7, h8, halign⟩ :=
    Nivat.PartsChainFeed.exists_parts_chain_half d cz hxper hvl_ne hvl_prim hℓ_nel hℓ_pos
      hℓ_neg hdet_ℓ hnℓ_prim hnℓ_perp hcase2
  exact ⟨B, A, u, kk, g₁, h1, h2, h3, h4, h5, h6, h7, h8, halign,
    ahat_nonempty_of_halign_lside halign⟩

/-! ## §19 `bottom` 的原文出处与逐字段映射（集成者派工的正面回答）

### §19a 给出 `bottom` 的那一句

`bottom` 的四条合取里承重的是**第四条**（壳的差集被单条 `vJ`-射线穷尽）。它的原文出处是
`b3_colle2.txt:506`：

> 「$\hat A_\infty := \bigcup \hat A_i$ 是弱 $E(\mathcal S_\varphi)$-包络集，**带两条半无限边**，
> 一条平行于 $\boldsymbol\ell$、另一条平行于 $\boldsymbol\ell_J$。实际上 $\hat A_\infty$ 是一个
> $(\boldsymbol\ell,\boldsymbol\ell_J)$-region。」

配 `:440` 的 `Â_∞^{(ε)} := {g + t·v⃗_{ℓ_{J−1}} : g ∈ Â_∞, t ∈ ℤ₊, dist(g + t·v⃗_{ℓ_{J−1}}, ℓ_J) ≤ d_ε}`
与 `:442` 的 `0 = d_0 < d_1 < ⋯`（「对每个 `g ∈ ℋ(ℓ_J)` 存在 `i` 使 `dist(g, ℓ_J) = d_i`」）。

⚠ **§47：这一句的定位不是我本轮的新发现。** `blueprint/NOTE.md` 的 (F) 条（第 221 轮，
lane-hole3-cone 逐行读出）已经把 `:506` 钉成 `hline0` 的出处，并逐字写下
「恰两条半无限边、其一 ∥ ℓ_J」正是「固定层上的边界线是从某点出发的单条 `vJ` 方向射线」
——那就是合取 4 的内容。我本轮只复读确认，不重复记账。
§47 命中数（`grep -c`，同批哨兵 `convex` = 2/3/6 非零）：`rec_vJ` = 3/31/31，
`ahat_halfPlane_L` = 0/3/11，`半无限` = 4/5/2，`506` = 4/9/20，`缺失字段` = 2/0/3
（顺序 `OPEN.md` / `NOTE.md` / `LANDING.md`；§51：命中数只是「我搜到了」）。

### §19b 本轮的实际增量：(F) 条的 P1–P4 **不是必需的**

NOTE (F) 把 `:506` 的四条前提 P1（`w_i(j)` 按方向编号的边）／P2（`⋃ Aᵢ = ℋ(ℓ^{(−)})`）／
P3（passing to a subsequence）／P4（`J` 是最小的无穷次严格增方向）逐条对照字段表，结论是
四条**全不在**字段里，于是 `hline0` 记成债。

**那份对照表是对的，但它证的是「原文那条构造不在链上」，不是「合取 4 不可证」。**
本节给出一条**不经 P1–P4** 的路：合取 4 的几何内容只需要「底线在 `vJ` 方向上**有下界**」，
而这条下界在字段表里**有现货**——`ahat_halfPlane_L`。

逐步（§20 的 `bottom_conj124_of_recVJ_lside` 是它的内核形）：

1. `nL := det p vJ • (−p.2, p.1)` 是 `ahat_halfPlane_L` 用的那个法向。两条算术恒等式：
   `⟪nL, vJ⟫ = (det p vJ)²`（`hnL_vJ`）、`⟪nL, vJ1⟫ = det p vJ · det p vJ1`（`hnL_vJ1`）。
2. 只要 `0 ≤ det p vJ · det p vJ1`，`ahat_halfPlane_L` 的下界就**传到整个 `reachSet`**：
   `z = g + t·vJ1`（`t : ℕ`）⟹ `⟪nL,z⟫ = ⟪nL,g⟫ + t·⟪nL,vJ1⟫ ≥ cL`。
3. `det p vJ ≠ 0` ⟹ `(det p vJ)² ≥ 1` ⟹ 在层线 `{⟪nJ,·⟫ = cJ−ε−1}` 上沿 `vJ` 走一步
   `⟪nL,·⟫` 至少涨 1 ⟹ 层线 ∩ `reachSet` 在 `vJ` 方向**有下界**。
4. §17 的 `reachSet_ray_at_level_lside` 给出该集合**非空**；`rec_vJ` 给出它**向上封闭**；
   下界 ＋ 非空 ⟹ 有**最小元**（`Int.exists_least_of_bdd`）⟹ 它**恰是**一条 `vJ`-射线。

⟹ 合取 1、2、4 **同时**由这条构造给出，取 `L := 0`、`z₀ :=` 那个最小元。

### §19c 逐前提映射表（本轮的答卷）

| `bottom` 用到的东西 | 原文 | 在 37 条字段里对应谁 |
|---|---|---|
| `Â_∞^{(ε)}` ＝ `vJ1`-扫掠再按 `d_ε` 截断 | `:440` | `MaxEnv.shell` 的**定义**（`shell_eq_reach_inter`），非字段 |
| `d_ε` 无缝（相邻格线差 1 层） | `:442` | `nJ_prim` |
| `Â_∞ ⊆ ℋ(ℓ_J)` | `:492` | `hhp` |
| 沿 `v⃗_{ℓ_{J−1}}` 向下封闭（在 `ℋ(ℓ_J)` 内） | `:440` 的 `t ∈ ℤ₊` | `hswept`（本节的证法**没用上**） |
| 半无限边 ∥ `ℓ` | `:506` | `rec_p`（`p = −c·v⃗_ℓ`） |
| 「是 region」＝ 边是**射线**不是**直线** | `:386` ＋ `:506` | ⭐ `ahat_halfPlane_L` ＋ `det p vJ ≠ 0` |
| 半无限边 ∥ `ℓ_J` | `:506` | ⛔ **没有字段。这就是 `rec_vJ`。** |
| `nL` 下界能传到 `reachSet` | — | ⛔ **没有字段**：要 `0 ≤ det p vJ · det p vJ1` 这条**定向** |
| 合取 3（`S − F.a` 的平移仍可达） | `:528`（`𝒮_φ` 是 `η`-生成 ⟹ 归纳有余量） | ⛔ 未映到，见 §19e |

⟹ **两条缺失字段，一条缺失定向。**

1. **`rec_vJ : ∀ g ∈ ⋃ i, hatOf A kk vl i, g + vJ ∈ ⋃ i, hatOf A kk vl i`**。它是 `:506` 第二条
   半无限边的 Lean 影子，与**已有**字段 `rec_p`（第一条半无限边）是原文同一句话的两半。
   `ChainPartsFeed.lean` 的字段表在 `bottom` 前面自己写着
   「`region obligations (rec_vJ excluded — Result 1b discharges it)`」——而 Result 1b 就是
   `rec_vJ_of_bottom`，它吃 `bottom`。⟹ **`rec_vJ ↔ bottom` 这个环是记账造出来的**：
   原文在一句话里同时读出两条边，Lean 留下一条、想用 `bottom` 把另一条倒推回来。
   按 `Primitive vJ1` 的先例，这记成**缺失字段**。
2. 定向 `0 ≤ det p vJ · det p vJ1`。在**共线格**（`vJ1 = m·vl`、`p = −c·vl`）它是 `= 0`，
   由主仓 `GcdCollapse.det_p_vJ1_eq_zero` 无条件给出 ⟹ **共线格里这条是免费的**。
   横截格里它是一条真定向条件，与集成者 `HcombOrient.lean` 判出的「`hcomb` 欠一条定向字段」
   **同类**（都是「结构保留了太多符号自由度」）。⚠ 我**不**主张它们是同一条命题。

### §19d 一条结构结论：`L` 不是自由参数

`bottom_slice_eq_ray_of_conj24_lside`（§20）：合取 2 ＋ 合取 4 合起来**等价于**

    {z ∈ reachSet (⋃ Âᵢ) vJ1 | ⟪nJ,z⟫ = cJ − ε − 1} = {z₀ + k·vJ : k ≥ L}

即那层切片**逐点等于**该射线。⟹ `L` 被两条合取夹死在切片的**最小元**上，没有一格余量。
（合取 4 要 `L` 小、合取 2 要 `L` 大；`z ∈ shell ε` 那一支在这一层恒假，因为
`cJ − ε > cJ − ε − 1`。）

### §19e 还欠什么：只剩合取 3，而且它必须在**最小元**处成立

§19d 把合取 3 的难度钉死了：它不能靠「把 `L` 调大」绕过。要交的逐字是

    ∀ b ∈ S, ∀ k ≥ 0,  z₀ + k·vJ + (b − F.a) ∈ reachSet (⋃ Âᵢ) vJ1

其中 `z₀` 是底线的最小元。可用的料：`F.lex`（`ANormal.lean` 的 `FaceBlock`）给
`∀ b ∈ S.erase F.a, ⟪nJ,F.a⟫ < ⟪nJ,b⟫ ∨ (⟪nJ,F.a⟫ = ⟪nJ,b⟫ ∧ ⟪vJ,F.a⟫ < ⟪vJ,b⟫)`，
⟹ `⟪nJ, b − F.a⟫ ≥ 0`，且等号那一档由 §20 的 `eq_add_zsmul_of_dot_eq_lside` 化成
`b − F.a = j·vJ`（`j ≥ 0`），直接被合取 2 吞掉。**开着的是 `⟪nJ, b − F.a⟫ > 0` 那一档**：
它把点抬到层 `cJ−ε−1+δ`，而不同层的最小元之间的相对位置，在本节的前提表下**不被决定**
（`reachSet` 在层 `h` 的最小元由「`h` 模 `e := −⟪nJ,vJ1⟫` 的那一档」决定，不同 `δ` 落在不同档）。

### §19f 本节**不**主张什么

1. **不**主张 `bottom` 已有产者。§20 的 `bottom_conj124_of_recVJ_lside` 吃 `rec_vJ`，
   而 `rec_vJ` 在链上目前只能由 `bottom` 得到 ⟹ 它**不是**一条减债的产者，
   它的用途是把「`bottom` 是四条义务」压成「`bottom` ＝ `rec_vJ` ＋ 合取 3」。
   ⛔ 集成者与 lane-tower-hbase 的循环提醒在此仍然生效，我没有绕过它。
2. **不**主张 `ahat_halfPlane_L` 是唯一的下界来源。§13 的
   `not_iUnion_hatOf_eq_halfPlane_of_chain_stock` 走的是另一条路（`hhp` ＋ `rec_p` ＋
   `⟪nJ,vl⟫ < 0`）。这两条之间的等价性我**没有**在 Lean 里走过。
3. **不**主张 §20 的反例在链上出现。`not_bottom_conj4_without_ray_bound_lside` 的 `U` 是整张
   半平面，§13 已在链上否掉这个对象。该反例的作用是**鉴别**（§52）：它与
   `bottom_conj124_of_recVJ_lside` 的前提表**只差 `ahat_halfPlane_L` 一条**
   （`hswept` 我特意兑现了，就是为了说明它挡不住），⟹ 那条前提在本证法里不可删。
-/

/-- **层线是一条 `vJ`-余集。** `nJ` / `vJ` 都本原且 `⟪nJ,vJ⟫ = 0` ⟹ 同层的两点相差 `vJ` 的
整数倍。走 `det_eq_zero_of_dot_eq_zero` ＋ `exists_smul_of_det_eq_zero`（`LatticeEdges.lean`）。 -/
theorem eq_add_zsmul_of_dot_eq_lside {nJ vJ : ℤ × ℤ}
    (hnJ : Primitive nJ) (hvJ : Primitive vJ) (hlevel : dot nJ vJ = 0)
    {y z : ℤ × ℤ} (h : dot nJ y = dot nJ z) :
    ∃ j : ℤ, y = z + j • vJ := by
  have hnJ0 : nJ ≠ 0 := (prim_iff_primitive.mpr hnJ).ne_zero
  have hd : dot nJ (y - z) = 0 := by
    simp only [dot, Prod.fst_sub, Prod.snd_sub]
    simp only [dot] at h
    linear_combination h
  have hdet : det vJ (y - z) = 0 := det_eq_zero_of_dot_eq_zero hnJ0 hlevel hd
  obtain ⟨j, hj⟩ := exists_smul_of_det_eq_zero (prim_iff_primitive.mpr hvJ) hdet
  refine ⟨j, ?_⟩
  have h1 : (y - z).1 = (j • vJ).1 := by rw [hj]; simp
  have h2 : (y - z).2 = (j • vJ).2 := by rw [hj]; simp
  have hz : y - z = j • vJ := Prod.ext h1 h2
  rw [← hz]; abel

/-- **`reachSet` 继承 `rec_vJ`。** 扫掠方向与 `vJ` 无关，所以 `+vJ` 直接搬到基点上。 -/
theorem reachSet_recVJ_lside {U : Set (ℤ × ℤ)} {vJ vJ1 : ℤ × ℤ}
    (hrecvJ : ∀ z ∈ U, z + vJ ∈ U) :
    ∀ z ∈ MaxEnv.reachSet U vJ1, z + vJ ∈ MaxEnv.reachSet U vJ1 := by
  rintro z ⟨g, hg, t, rfl⟩
  exact ⟨g + vJ, hrecvJ g hg, t, by abel⟩

/-- ⭐ **`bottom` 的 `L` 不是自由参数（§19d）。** 合取 2 ＋ 合取 4 合起来说：层
`cJ − ε − 1` 的可达切片**逐点等于**射线 `{z₀ + k·vJ : k ≥ L}`。⟹ `L` 被夹死在切片的最小元上。

这一条把「合取 3 能不能靠把 `L` 调大绕过」这个问题一次关掉：不能。 -/
theorem bottom_slice_eq_ray_of_conj24_lside
    {U : Set (ℤ × ℤ)} {nJ vJ vJ1 z₀ : ℤ × ℤ} {cJ L : ℤ} {ε : ℕ}
    (hlevel : dot nJ vJ = 0) (hz₀ : dot nJ z₀ = cJ - (ε : ℤ) - 1)
    (hconj2 : ∀ k : ℤ, L ≤ k → z₀ + k • vJ ∈ MaxEnv.reachSet U vJ1)
    (hconj4 : ∀ z ∈ MaxEnv.shell U vJ1 nJ cJ (ε + 1),
      z ∈ MaxEnv.shell U vJ1 nJ cJ ε ∨ ∃ k : ℤ, L ≤ k ∧ z = z₀ + k • vJ)
    (z : ℤ × ℤ) :
    (z ∈ MaxEnv.reachSet U vJ1 ∧ dot nJ z = cJ - (ε : ℤ) - 1) ↔
      ∃ k : ℤ, L ≤ k ∧ z = z₀ + k • vJ := by
  constructor
  · rintro ⟨hr, hd⟩
    have hmem : z ∈ MaxEnv.shell U vJ1 nJ cJ (ε + 1) :=
      MaxEnv.mem_shell_succ_iff.mpr (Or.inr ⟨hr, hd⟩)
    rcases hconj4 z hmem with hs | h
    · exfalso
      obtain ⟨g, hg, t, hzg, hlowz⟩ := hs
      omega
    · exact h
  · rintro ⟨k, hk, rfl⟩
    refine ⟨hconj2 k hk, ?_⟩
    rw [dot_add, mpos_dot_zsmul, hlevel, mul_zero, add_zero]
    exact hz₀

/-- ⭐⭐ **`bottom` 的合取 1、2、4 一次产出（§19b）。**

前提里**只有 `hrecvJ` 不是字段**：`hconv` ← `maxA`（经 `latticeConvex_of_parts`），
`hne` ← `ahat_nonempty`，`hnJprim` / `hvJprim` ← 同名字段，`hrecp` ← `rec_p`，
`hlevel` ← `F.dot_nJ_vJ`，`hup` ← `hhp` ＋ `rec_p` ＋ `dot_nJ_p`（见 `parts_stock_lside`），
`hsweep` ← `hsweep`，`hLbd` ← `ahat_halfPlane_L`，`hdet` ← `det_p_vJ_ne_of_fields`（§2）。
`hLsign` 在共线格是 `0 = 0`（`GcdCollapse.det_p_vJ1_eq_zero`）。

⛔ **这不是一条减债的 `bottom` 产者**（§19f 第 1 条）：`hrecvJ` 就是 `rec_vJ`，而链上目前只有
`rec_vJ_of_bottom` 能给它。本条的用途是把「`bottom` 是四条义务」压成
「`bottom` ＝ `rec_vJ` ＋ 合取 3」。

⚠ `hswept` 与 `hhp` 都**没有**出现在前提表里——本证法不需要它们。 -/
theorem bottom_conj124_of_recVJ_lside
    {U : Set (ℤ × ℤ)} {nJ vJ vJ1 p : ℤ × ℤ} {cJ cL : ℤ}
    (hconv : IsLatticeConvexRegion U) (hne : U.Nonempty)
    (hnJprim : Primitive nJ) (hvJprim : Primitive vJ)
    (hrecvJ : ∀ z ∈ U, z + vJ ∈ U) (hrecp : ∀ z ∈ U, z + p ∈ U)
    (hlevel : dot nJ vJ = 0) (hup : 0 < dot nJ p) (hsweep : dot nJ vJ1 < 0)
    (hLbd : ∀ z ∈ U, cL ≤ dot (det p vJ • ((-p.2 : ℤ), p.1)) z)
    (hdet : det p vJ ≠ 0) (hLsign : 0 ≤ det p vJ * det p vJ1)
    (ε : ℕ) :
    ∃ (z₀ : ℤ × ℤ) (L : ℤ),
      dot nJ z₀ = cJ - (ε : ℤ) - 1 ∧
      (∀ k : ℤ, L ≤ k → z₀ + k • vJ ∈ MaxEnv.reachSet U vJ1) ∧
      (∀ z ∈ MaxEnv.shell U vJ1 nJ cJ (ε + 1),
        z ∈ MaxEnv.shell U vJ1 nJ cJ ε ∨ ∃ k : ℤ, L ≤ k ∧ z = z₀ + k • vJ) := by
  classical
  have hvJ0 : vJ ≠ 0 := (prim_iff_primitive.mpr hvJprim).ne_zero
  have hnL_vJ : dot (det p vJ • ((-p.2 : ℤ), p.1)) vJ = det p vJ * det p vJ := by
    simp only [dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, det]
    ring
  have hnL_vJ1 : dot (det p vJ • ((-p.2 : ℤ), p.1)) vJ1 = det p vJ * det p vJ1 := by
    simp only [dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, det]
    ring
  have hD1 : 1 ≤ det p vJ * det p vJ := by
    have h0 : 0 < det p vJ * det p vJ := mul_self_pos.mpr hdet
    simpa using Int.add_one_le_iff.mpr h0
  -- `ahat_halfPlane_L` 的下界传到整个 `reachSet`（用 `hLsign`）
  have hlow : ∀ z ∈ MaxEnv.reachSet U vJ1,
      cL ≤ dot (det p vJ • ((-p.2 : ℤ), p.1)) z := by
    rintro z ⟨g, hg, t, rfl⟩
    have hg' := hLbd g hg
    rw [dot_add, mpos_dot_zsmul, hnL_vJ1]
    have ht : (0 : ℤ) ≤ (t : ℤ) := Int.natCast_nonneg t
    have := mul_nonneg ht hLsign
    linarith
  obtain ⟨zb, hzb, hray⟩ := reachSet_ray_at_level_lside hconv hnJprim hne hrecvJ hrecp
    hlevel hvJ0 hup hsweep (cJ - (ε : ℤ) - 1)
  have hreachvJ := reachSet_recVJ_lside (vJ1 := vJ1) hrecvJ
  have hbdd : ∃ b : ℤ, ∀ k : ℤ, zb + k • vJ ∈ MaxEnv.reachSet U vJ1 → b ≤ k := by
    refine ⟨min 0 (cL - dot (det p vJ • ((-p.2 : ℤ), p.1)) zb), ?_⟩
    intro k hk
    have h1 := hlow _ hk
    rw [dot_add, mpos_dot_zsmul, hnL_vJ] at h1
    rcases lt_or_ge k 0 with hk0 | hk0
    · refine le_trans (min_le_right _ _) ?_
      have hstep : k * (det p vJ * det p vJ - 1) ≤ 0 :=
        mul_nonpos_iff.mpr (Or.inr ⟨le_of_lt hk0, by linarith⟩)
      rw [mul_sub, mul_one, sub_nonpos] at hstep
      linarith
    · exact le_trans (min_le_left _ _) hk0
  obtain ⟨kmin, hkmin, hkleast⟩ := Int.exists_least_of_bdd hbdd ⟨0, hray 0 le_rfl⟩
  have hKup : ∀ k : ℤ, kmin ≤ k → zb + k • vJ ∈ MaxEnv.reachSet U vJ1 := by
    intro k hk
    have hiter := mpos_rec_iter hreachvJ (k - kmin).toNat (zb + kmin • vJ) hkmin
    rw [Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ k - kmin)] at hiter
    have heq : zb + kmin • vJ + (k - kmin) • vJ = zb + k • vJ := by
      rw [add_assoc, ← add_smul]
      have hkk : kmin + (k - kmin) = k := by ring
      rw [hkk]
    rwa [heq] at hiter
  refine ⟨zb + kmin • vJ, 0, ?_, ?_, ?_⟩
  · rw [dot_add, mpos_dot_zsmul, hlevel, mul_zero, add_zero]; exact hzb
  · intro k hk
    have heq : zb + kmin • vJ + k • vJ = zb + (kmin + k) • vJ := by
      rw [add_assoc, ← add_smul]
    rw [heq]
    exact hKup _ (by omega)
  · intro z hz
    rcases MaxEnv.mem_shell_succ_iff.mp hz with hs | ⟨hr, hd⟩
    · exact Or.inl hs
    · have hlev : dot nJ z = dot nJ zb := by rw [hd, hzb]
      obtain ⟨j, hj⟩ := eq_add_zsmul_of_dot_eq_lside hnJprim hvJprim hlevel hlev
      have hjK : zb + j • vJ ∈ MaxEnv.reachSet U vJ1 := by rw [← hj]; exact hr
      refine Or.inr ⟨j - kmin, by have := hkleast j hjK; omega, ?_⟩
      rw [hj, add_assoc, ← add_smul]
      have hkk : kmin + (j - kmin) = j := by ring
      rw [hkk]

/-- 半平面 `{z | 0 ≤ z.2}` 是格凸区域（§20 反例的零件）。 -/
private theorem latticeConvex_snd_nonneg_lside :
    IsLatticeConvexRegion {z : ℤ × ℤ | 0 ≤ z.2} := by
  refine ⟨{x : ℝ × ℝ | 0 ≤ x.2}, ?_, ?_, ?_⟩
  · intro x hx y hy s t hs ht _
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    have h1 : (0 : ℝ) ≤ s * x.2 := mul_nonneg hs hx
    have h2 : (0 : ℝ) ≤ t * y.2 := mul_nonneg ht hy
    simpa [Prod.snd_add, Prod.smul_snd, smul_eq_mul] using add_nonneg h1 h2
  · exact isClosed_le continuous_const continuous_snd
  · ext z
    simp only [Set.mem_preimage, Set.mem_setOf_eq, toReal]
    exact ⟨fun h => by exact_mod_cast h, fun h => by exact_mod_cast h⟩

/-- ⛔ **鉴别性反例（§19f 第 3 条）：去掉 `ahat_halfPlane_L`，合取 4 当场假。**

见证 `U = {z | 0 ≤ z.2}`、`nJ = (0,1)`、`vJ = (1,0)`、`vJ1 = (0,−1)`、`p = (0,1)`、`cJ = 0`。
它兑现 `bottom_conj124_of_recVJ_lside` 前提表里**除 `hLbd` 以外的全部**，**外加** `hhp` 与
`hswept`（特意加上，以说明那两条挡不住），而 `nL = (1,0)` 方向上 `U` 无下界
（结论里那条 `¬ ∃ cL`），于是 `reachSet U vJ1 = ℤ²`、底线是整条直线而非射线，合取 4 对
**每个** `ε`、**每组** `(z₀, L)` 为假。

⚠ 射程：本见证的 `U` 是整张半平面，§13 的
`not_iUnion_hatOf_eq_halfPlane_of_chain_stock` 已在链上否掉这个对象。⟹ 本条说的是
「这张前提表里 `hLbd` 不可删」，**不**是「链上合取 4 需要 L-块」。 -/
theorem not_bottom_conj4_without_ray_bound_lside :
    ∃ (U : Set (ℤ × ℤ)) (nJ vJ vJ1 p : ℤ × ℤ) (cJ : ℤ),
      IsLatticeConvexRegion U ∧ U.Nonempty ∧
      Primitive nJ ∧ Primitive vJ ∧ Primitive vJ1 ∧ Primitive p ∧
      (∀ z ∈ U, z + vJ ∈ U) ∧ (∀ z ∈ U, z + p ∈ U) ∧
      (∀ z ∈ U, cJ ≤ dot nJ z) ∧ MaxEnv.SweptClosed U vJ1 nJ cJ ∧
      dot nJ vJ = 0 ∧ 0 < dot nJ p ∧ dot nJ vJ1 < 0 ∧
      det p vJ ≠ 0 ∧ 0 ≤ det p vJ * det p vJ1 ∧
      (¬ ∃ cL : ℤ, ∀ z ∈ U, cL ≤ dot (det p vJ • ((-p.2 : ℤ), p.1)) z) ∧
      (∀ ε : ℕ, ¬ ∃ (z₀ : ℤ × ℤ) (L : ℤ),
        dot nJ z₀ = cJ - (ε : ℤ) - 1 ∧
        ∀ z ∈ MaxEnv.shell U vJ1 nJ cJ (ε + 1),
          z ∈ MaxEnv.shell U vJ1 nJ cJ ε ∨ ∃ k : ℤ, L ≤ k ∧ z = z₀ + k • vJ) := by
  refine ⟨{z : ℤ × ℤ | 0 ≤ z.2}, ((0 : ℤ), (1 : ℤ)), ((1 : ℤ), (0 : ℤ)),
    ((0 : ℤ), (-1 : ℤ)), ((0 : ℤ), (1 : ℤ)), 0,
    latticeConvex_snd_nonneg_lside, ⟨((0 : ℤ), (0 : ℤ)), by norm_num⟩,
    isCoprime_one_right, isCoprime_one_left, isCoprime_one_right.neg_right,
    isCoprime_one_right, ?_, ?_, ?_, ?_, by norm_num [dot], by norm_num [dot],
    by norm_num [dot], by norm_num [det], by norm_num [det], ?_, ?_⟩
  · intro z hz
    simp only [Set.mem_setOf_eq, Prod.snd_add] at hz ⊢
    omega
  · intro z hz
    simp only [Set.mem_setOf_eq, Prod.snd_add] at hz ⊢
    omega
  · intro z hz
    simp only [Set.mem_setOf_eq, dot] at hz ⊢
    omega
  · intro g hg t hd
    simp only [Set.mem_setOf_eq, dot, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul] at hg hd ⊢
    omega
  · rintro ⟨cL, hcL⟩
    have h := hcL (cL - 1, 0) (by simp)
    simp only [dot, det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h
    omega
  · intro ε
    rintro ⟨z₀, L, hz₀, hcon⟩
    simp only [dot] at hz₀
    have hz2 : z₀.2 = -(ε : ℤ) - 1 := by omega
    have hzeq : (z₀.1 + (L - 1), z₀.2) = z₀ + (L - 1) • ((1 : ℤ), (0 : ℤ)) := by
      refine Prod.ext ?_ ?_ <;>
        simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
          mul_one, mul_zero, add_zero]
    have hmem : (z₀.1 + (L - 1), z₀.2) ∈
        MaxEnv.shell {z : ℤ × ℤ | 0 ≤ z.2} ((0 : ℤ), (-1 : ℤ)) ((0 : ℤ), (1 : ℤ)) 0 (ε + 1) := by
      refine ⟨(z₀.1 + (L - 1), z₀.2 + ((ε : ℤ) + 1)), ?_, ε + 1, ?_, ?_⟩
      · simp only [Set.mem_setOf_eq]; omega
      · refine Prod.ext ?_ ?_ <;>
          simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
            mul_zero, add_zero] <;> push_cast <;> ring
      · simp only [dot]; push_cast; omega
    rcases hcon _ hmem with hs | ⟨k, hk, hkz⟩
    · obtain ⟨g, hg, t, hzg, hlowz⟩ := hs
      simp only [dot] at hlowz
      push_cast at hlowz
      omega
    · rw [hzeq] at hkz
      have h1 := congrArg Prod.fst hkz
      simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, mul_one] at h1
      omega

/-! ## §21 合取 3 的形状：一半已结清，另一半化成 `nL` 上的一条不等式

§19e 把合取 3 钉在底线的最小元处。本节把它再切两刀。

**(甲) `⟪nJ, b − F.a⟫ = 0` 那一档已结清**（`bottom_conj3_same_level_lside`）。
`F.lex`（`ANormal.lean` 的 `FaceBlock`）在同层时给 `⟪vJ, F.a⟫ < ⟪vJ, b⟫`；层差为 0 ＋ 两条本原性
⟹ `b − F.a = j·vJ`（§20 的 `eq_add_zsmul_of_dot_eq_lside`），再由 `⟪vJ,vJ⟫ > 0` 逼出 `j > 0`
⟹ 整条平移被合取 2 自己吞掉，**不需要任何新前提、不需要定向**。

**(乙) `⟪nJ, b − F.a⟫ > 0` 那一档化成一条不等式**（`mem_reachSet_iff_nL_le_of_ray_lside`）。
一旦某一层的切片已知是射线（这正是 §20 `bottom_slice_eq_ray_of_conj24_lside` 的产出），
该层上的可达性就**逐字等价于** `nL`-坐标不小于最小元的 `nL`-坐标：

    y ∈ reachSet U vJ1  ⟺  ⟪nL, z₀⟫ ≤ ⟪nL, y⟫        （`⟪nJ,y⟫ = ⟪nJ,z₀⟫` 之下）

机理是两条恒等式：`⟪nL, w⟫ = det p vJ · det p w`（`dot_nL_eq_det_lside`，对**任意** `w`），
故沿 `vJ` 走一步 `nL` 恰涨 `(det p vJ)² ≥ 1`；层线是 `vJ`-余集 ⟹ 层上的点由 `nL` 唯一编号。

⟹ 合取 3 的残余被改写成：**对每个 `b ∈ S`，把点抬到层 `cJ−ε−1+δ`（`δ := ⟪nJ,b−F.a⟫ > 0`）之后，
它的 `nL` 是否仍不小于那一层的最小元的 `nL`**。

⚠ **本节不主张那条不等式成立。** 它把「集合成员」换成「一条整数不等式」，换掉的是**证法**，
不是**难度**；真正的内容落在「不同层的最小元之间的相对位置」上，而那一条在 §19c 的前提表下
不被决定（见 §19e）。
-/

/-- **`nL` 的闭式**：`ahat_halfPlane_L` 的法向对**任意**向量取内积都是一个行列式的倍数。
`⟪det p vJ • (−p.2, p.1), w⟫ = det p vJ · det p w`。 -/
theorem dot_nL_eq_det_lside (p vJ w : ℤ × ℤ) :
    dot (det p vJ • ((-p.2 : ℤ), p.1)) w = det p vJ * det p w := by
  simp only [dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, det]
  ring

/-- ⭐ **切片成员判据（§21 乙）。** 层线上切片已知是射线时，可达性逐字等价于一条 `nL` 不等式。

`hslice` 就是 `bottom_slice_eq_ray_of_conj24_lside` 在 `L = 0` 处的产出。 -/
theorem mem_reachSet_iff_nL_le_of_ray_lside
    {U : Set (ℤ × ℤ)} {nJ vJ vJ1 p z₀ : ℤ × ℤ}
    (hnJprim : Primitive nJ) (hvJprim : Primitive vJ) (hlevel : dot nJ vJ = 0)
    (hdet : det p vJ ≠ 0)
    (hslice : ∀ z : ℤ × ℤ,
      (z ∈ MaxEnv.reachSet U vJ1 ∧ dot nJ z = dot nJ z₀) ↔ ∃ k : ℤ, 0 ≤ k ∧ z = z₀ + k • vJ)
    {y : ℤ × ℤ} (hy : dot nJ y = dot nJ z₀) :
    y ∈ MaxEnv.reachSet U vJ1 ↔
      dot (det p vJ • ((-p.2 : ℤ), p.1)) z₀ ≤ dot (det p vJ • ((-p.2 : ℤ), p.1)) y := by
  have hD1 : 1 ≤ det p vJ * det p vJ := by
    have h0 : 0 < det p vJ * det p vJ := mul_self_pos.mpr hdet
    simpa using Int.add_one_le_iff.mpr h0
  have hstep : ∀ j : ℤ, dot (det p vJ • ((-p.2 : ℤ), p.1)) (z₀ + j • vJ)
      = dot (det p vJ • ((-p.2 : ℤ), p.1)) z₀ + j * (det p vJ * det p vJ) := by
    intro j
    rw [dot_add, mpos_dot_zsmul, dot_nL_eq_det_lside p vJ vJ]
  constructor
  · intro hmem
    obtain ⟨k, hk, hkz⟩ := (hslice y).mp ⟨hmem, hy⟩
    rw [hkz, hstep k]
    nlinarith
  · intro hle
    obtain ⟨j, hj⟩ := eq_add_zsmul_of_dot_eq_lside hnJprim hvJprim hlevel hy
    rw [hj, hstep j] at hle
    have hj0 : 0 ≤ j := by nlinarith
    exact ((hslice y).mpr ⟨j, hj0, hj⟩).1

/-- ⭐ **合取 3 的同层档已结清（§21 甲）。** `F.lex` 在 `⟪nJ, b − a⟫ = 0` 时给
`⟪vJ, a⟫ < ⟪vJ, b⟫`，两条本原性把 `b − a` 化成 `j·vJ`（`j > 0`），于是整条平移被合取 2 吞掉。

不需要定向条件，不需要 `ahat_halfPlane_L`，不需要 `hswept`。 -/
theorem bottom_conj3_same_level_lside
    {U : Set (ℤ × ℤ)} {nJ vJ vJ1 z₀ a b : ℤ × ℤ} {L : ℤ}
    (hnJprim : Primitive nJ) (hvJprim : Primitive vJ) (hlevel : dot nJ vJ = 0)
    (hconj2 : ∀ k : ℤ, L ≤ k → z₀ + k • vJ ∈ MaxEnv.reachSet U vJ1)
    (hsame : dot nJ b = dot nJ a) (hlex : dot vJ a < dot vJ b) :
    ∀ k : ℤ, L ≤ k → z₀ + k • vJ + (b - a) ∈ MaxEnv.reachSet U vJ1 := by
  have hvJ0 : vJ ≠ 0 := (prim_iff_primitive.mpr hvJprim).ne_zero
  obtain ⟨j, hj⟩ := eq_add_zsmul_of_dot_eq_lside hnJprim hvJprim hlevel hsame
  have hba : b - a = j • vJ := by rw [hj]; abel
  have hpos : 0 < j := by
    have hvv : 0 < dot vJ vJ := dot_self_pos_lside hvJ0
    have hd : dot vJ (b - a) = j * dot vJ vJ := by rw [hba, mpos_dot_zsmul]
    have hd' : dot vJ (b - a) = dot vJ b - dot vJ a := by
      simp only [dot, Prod.fst_sub, Prod.snd_sub]; ring
    nlinarith [hd, hd', hlex, hvv]
  intro k hk
  have heq : z₀ + k • vJ + (b - a) = z₀ + (k + j) • vJ := by
    rw [hba, add_assoc, ← add_smul]
  rw [heq]
  exact hconj2 _ (by omega)

/-! ## §22 ⭐⭐ `W₀` 的闭式：`W₀ nJ p vJ1 = det p vJ1 • dir nJ`
—— 于是 hbase §19 的「同向」欠账 ≡ 我 §20 的 `hLsign` 的严格形，**而且两条路各活在一个格里**

## §22a 起因

lane-tower-hbase 2026-09-26 来信（`TowerHbaseRecP.lean` §19，我**未复跑**，按他所报记账，§55）：

> `rec_vJ` 从字段出发只欠一句话 `∃ d>0, W₀ nJ p vJ1 = d • vJ`，整除那半凭空消失；
> 且这「定向」与你 §20 合取 4 要的定向是**同一格欠账**。

本节把这句话钉成内核事实，并给出**他没预料到的那一半**：那个欠账在**共线格里根本不可能兑现**。

## §22b 闭式（无条件，零前提）

`HcombOrient.W₀ nJ p vJ1 = (- ⟪nJ,vJ1⟫) • p + ⟪nJ,p⟫ • vJ1`（`HcombOrient.lean`，标识符名
`W₀`）。展开两个坐标，`p` 与 `vJ1` 的分量**恰好按 `det p vJ1` 合并**：

    W₀_eq_det_smul_dir_lside : W₀ nJ p vJ1 = (det p vJ1) • dir nJ        （无任何前提）

数值实例（硬规矩 6，写 Lean 之前先算的）：`nJ = (0,1)`、`p = (1,2)`、`vJ1 = (3,-1)` ⟹
`α = 2`、`β = 1`、`W₀ = 1•(1,2) + 2•(3,-1) = (7,0)`；`det p vJ1 = -7`、`dir nJ = (-1,0)`、
`(-7)•(-1,0) = (7,0)` ✓。随机核对 20000 组（ℤ∩[-6,6]，seed 7）0 反例。

⟹ **`W₀` 的方向完全由 `nJ` 定**（它总在 `nJ` 的垂线上——这才是
`EnvRefuteOrient.dot_nJ_W₀` 无条件成立的真正来源），`p` / `vJ1` 只贡献一个标量 `det p vJ1`。

## §22c ⛔ 共线格：`W₀ = 0`，hbase §19 的整条路在那里是空的

`det p vJ1 = 0`（＝共线格，`GcdCollapse` 的标识符 `det_p_vJ1_eq_zero` 那一支）⟹ `W₀ = 0`。
而 `rec_vJ_of_real_dir` 要的是 `toReal vJ = lam • toReal (W₀ …)`、`lam ≥ 0`；`W₀ = 0` 时
右边恒为 `0`，故它只能在 `vJ = 0` 时兑现——而 `vJ` 是本原的。⟹

    not_real_dir_of_collinear_lside :
      det p vJ1 = 0 → vJ ≠ 0 → ¬ ∃ lam : ℝ, toReal vJ = lam • toReal (W₀ nJ p vJ1)
    not_W₀_pos_multiple_of_collinear_lside :
      det p vJ1 = 0 → vJ ≠ 0 → ¬ ∃ d : ℤ, 0 < d ∧ W₀ nJ p vJ1 = d • vJ

**否掉的是哪一版签名（纪律 9）**：否的是 `TowerHbase.rec_vJ_of_real_dir` /
`rec_vJ_of_W₀_pos_multiple` 的**最后一个前提**（`hdir` / `W₀ = d • vJ`），且只在
`det p vJ1 = 0` 这一支上。⛔ **`ray_W₀_of_fields` / `recCone_W₀_of_fields` 本身不受影响**
——它们在共线格里仍为真，只是内容退化成「`R` 含 `g₀` 这一个点」，不承重。
⛔ 我**没有**否 `rec_vJ` 本身，也没有否 hbase 的任何一条已证声明；否的只是
「这条路能在共线格里产出 `rec_vJ`」。

## §22d 横截格：那个欠账 ≡ `0 < det p vJ · det p vJ1`

两条恒等式（本节所证）：

    dot_vJ_W₀_lside        : ⟪vJ, W₀ nJ p vJ1⟫ = det p vJ1 · det nJ vJ          （无前提）
    det_nJ_vJ_mul_dot_lside: ⟪nJ,vJ⟫ = 0 → det nJ vJ · ⟪nJ,p⟫ = ⟪nJ,nJ⟫ · det p vJ

第二条是二维 Cramer 恒等式在 `⟪nJ,vJ⟫ = 0` 上的特例（负控：去掉该前提，随机 1897 组里
1820 组为假 ⟹ 前提承重）。两条一夹，`⟪nJ,p⟫ > 0` 与 `⟪nJ,nJ⟫ > 0` 把符号全部传下来：

    W₀_pos_multiple_iff_detsign_lside :
      nJ ≠ 0 → Primitive vJ → ⟪nJ,vJ⟫ = 0 → 0 < ⟪nJ,p⟫ →
        ((∃ d : ℤ, 0 < d ∧ W₀ nJ p vJ1 = d • vJ) ↔ 0 < det p vJ · det p vJ1)

随机核对：过滤后 2229 组，0 处不符，其中左式为真 1062 组（⟹ 不是空真）。

⟹ **hbase 的判断在横截格里成立，而且比他说的更紧：不是「同一格欠账」，是「逐字同一个不等式」。**
我 §20 的 `bottom_conj124_of_recVJ_lside` 收的是 `hLsign : 0 ≤ det p vJ * det p vJ1`，
他的「同向」＝同一式的**严格**形。

## §22e ⭐ 但两条路不是同一条路：它们各活在一个格里

把 §22c 与 §22d 并起来，`det p vJ · det p vJ1` 这一个量的**两端**分别喂两条路：

| | `det p vJ1 = 0`（共线格） | `det p vJ1 ≠ 0`（横截格） |
|---|---|---|
| 我 §20 的 `hLsign : 0 ≤ …` | **免费**（乘积 = 0） | 真条件，欠符号 |
| hbase §19 的 `∃d>0, W₀ = d•vJ` | ⛔ **恒假**（`W₀ = 0`） | ⟺ `0 < …`，欠符号 |

⟹ 对记账的意思：
1. **共线格里 hbase 的 `W₀` 路不减债**；`rec_vJ` 在那里仍需别的产者。而我 §20 的 `bottom`
   合取 1/2/4 在那里是**白给**的（`hLsign` 取等号）。
2. **横截格里两条路欠的是同一个不等式**，只差严格/非严格 ⟹ 立案时记**一条**，不是两条。
3. ⟹ hbase 信里那句「两条路上都是同一格欠账」：**横截格对、共线格不对**（共线格里他那一格
   不是「欠」，是「不可能」）。

⛔ 射程自限（PROTOCOL §15 / §51）：本节只证下面八条纯算术命题。我**没有**证任何一格的
`rec_vJ`，**没有**复跑 hbase 的 `ray_W₀_of_fields` / `rec_vJ_of_real_dir`（按他所报记账，§55），
本轮也**没有**亲读 `b3_colle2.txt`（`:506` 的引文转自 `TowerHbaseRecP.lean` 与
`RecVJComb.lean` 的既有批注）。「共线格 ＝ `det p vJ1 = 0`」这一等同取自 `GcdCollapse`
（标识符名 `det_p_vJ1_eq_zero`），我未复跑。 -/

/-- ⭐⭐ **无条件闭式**：`W₀ nJ p vJ1 = (det p vJ1) • dir nJ`。

`W₀ nJ p vJ1 = (-⟪nJ,vJ1⟫) • p + ⟪nJ,p⟫ • vJ1`（`HcombOrient.lean`，标识符名 `W₀`）
的两个坐标分别整理成 `-nJ.2 · det p vJ1` 与 `nJ.1 · det p vJ1`。零前提。 -/
theorem W₀_eq_det_smul_dir_lside (nJ p vJ1 : ℤ × ℤ) :
    Nivat.HcombOrient.W₀ nJ p vJ1 = (det p vJ1) • dir nJ := by
  have h1 : (Nivat.HcombOrient.W₀ nJ p vJ1).1 = ((det p vJ1) • dir nJ).1 := by
    simp only [Nivat.HcombOrient.W₀, dir, det, dot, Prod.fst_add, Prod.smul_fst, smul_eq_mul]
    ring
  have h2 : (Nivat.HcombOrient.W₀ nJ p vJ1).2 = ((det p vJ1) • dir nJ).2 := by
    simp only [Nivat.HcombOrient.W₀, dir, det, dot, Prod.snd_add, Prod.smul_snd, smul_eq_mul]
    ring
  exact Prod.ext h1 h2

/-- **无条件**：`⟪vJ, W₀ nJ p vJ1⟫ = det p vJ1 · det nJ vJ`。由闭式 ＋ `⟪vJ, dir nJ⟫ = det nJ vJ`。 -/
theorem dot_vJ_W₀_lside (nJ p vJ1 vJ : ℤ × ℤ) :
    dot vJ (Nivat.HcombOrient.W₀ nJ p vJ1) = det p vJ1 * det nJ vJ := by
  rw [W₀_eq_det_smul_dir_lside]
  simp only [dot, dir, det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- **二维 Cramer 恒等式在 `⟪nJ,vJ⟫ = 0` 上的特例**：`det nJ vJ · ⟪nJ,p⟫ = ⟪nJ,nJ⟫ · det p vJ`。

⚠ `hlevel` 承重：去掉它随机 1897 组里 1820 组为假。 -/
theorem det_nJ_vJ_mul_dot_lside {nJ vJ : ℤ × ℤ} (p : ℤ × ℤ) (hlevel : dot nJ vJ = 0) :
    det nJ vJ * dot nJ p = dot nJ nJ * det p vJ := by
  simp only [dot, det] at hlevel ⊢
  linear_combination (nJ.1 * p.2 - nJ.2 * p.1) * hlevel

/-- `det vJ (W₀ nJ p vJ1) = 0`，只用 `⟪nJ,vJ⟫ = 0`。（与
`EnvRefuteOrient.det_vJ_W₀_vacuous` 同内容，这里由闭式重证，省一条 import。） -/
theorem det_vJ_W₀_lside {nJ vJ : ℤ × ℤ} (p vJ1 : ℤ × ℤ) (hlevel : dot nJ vJ = 0) :
    det vJ (Nivat.HcombOrient.W₀ nJ p vJ1) = 0 := by
  rw [W₀_eq_det_smul_dir_lside]
  simp only [dot] at hlevel
  simp only [det, dir, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  linear_combination (p.1 * vJ1.2 - p.2 * vJ1.1) * hlevel

/-- **`W₀ = 0` ⟺ 共线**（`nJ ≠ 0` 下）。 -/
theorem W₀_eq_zero_iff_lside {nJ : ℤ × ℤ} (p vJ1 : ℤ × ℤ) (hnJ0 : nJ ≠ 0) :
    Nivat.HcombOrient.W₀ nJ p vJ1 = 0 ↔ det p vJ1 = 0 := by
  rw [W₀_eq_det_smul_dir_lside, smul_eq_zero]
  constructor
  · rintro (h | h)
    · exact h
    · exfalso
      have h1 : (dir nJ).1 = 0 := by simp [h]
      have h2 : (dir nJ).2 = 0 := by simp [h]
      simp only [dir] at h1 h2
      have hz : dot nJ nJ = 0 := by simp only [dot]; nlinarith [h1, h2]
      have := dot_self_pos_lside hnJ0
      omega
  · exact fun h => Or.inl h

/-- ⛔ **共线格里 hbase §19 的整条路是空的（实数版，打的是 `rec_vJ_of_real_dir` 的 `hdir`）。**

`det p vJ1 = 0` ⟹ `W₀ = 0` ⟹ `toReal (W₀ …) = 0` ⟹ `lam • toReal (W₀ …) = 0` 恒成立，
故 `hdir` 只能在 `toReal vJ = 0` 即 `vJ = 0` 时兑现。 -/
theorem not_real_dir_of_collinear_lside {nJ p vJ1 vJ : ℤ × ℤ}
    (hvJ0 : vJ ≠ 0) (hcol : det p vJ1 = 0) :
    ¬ ∃ lam : ℝ, toReal vJ = lam • toReal (Nivat.HcombOrient.W₀ nJ p vJ1) := by
  rintro ⟨lam, hlam⟩
  have hW : Nivat.HcombOrient.W₀ nJ p vJ1 = 0 := by
    rw [W₀_eq_det_smul_dir_lside, hcol, zero_smul]
  rw [hW] at hlam
  have hz : toReal vJ = (0 : ℝ × ℝ) := by
    simpa [toReal] using hlam
  have h1 : (vJ.1 : ℝ) = 0 := congrArg Prod.fst hz
  have h2 : (vJ.2 : ℝ) = 0 := congrArg Prod.snd hz
  have e1 : vJ.1 = 0 := by exact_mod_cast h1
  have e2 : vJ.2 = 0 := by exact_mod_cast h2
  exact hvJ0 (Prod.ext (by simpa using e1) (by simpa using e2))

/-- ⛔ **共线格里 `rec_vJ_of_W₀_pos_multiple` 的最后一个前提恒假**（整数版，逐字他的形状）。 -/
theorem not_W₀_pos_multiple_of_collinear_lside {nJ p vJ1 vJ : ℤ × ℤ}
    (hvJ0 : vJ ≠ 0) (hcol : det p vJ1 = 0) :
    ¬ ∃ d : ℤ, 0 < d ∧ Nivat.HcombOrient.W₀ nJ p vJ1 = d • vJ := by
  rintro ⟨d, hd, hW⟩
  rw [W₀_eq_det_smul_dir_lside, hcol, zero_smul] at hW
  rcases smul_eq_zero.mp hW.symm with h | h
  · omega
  · exact hvJ0 h

/-- ⭐⭐ **横截格：hbase 的「同向」欠账 ＝ 我 §20 `hLsign` 的严格形，逐字同一个不等式。**

    (∃ d : ℤ, 0 < d ∧ W₀ nJ p vJ1 = d • vJ)  ↔  0 < det p vJ * det p vJ1

`→` 用 `dot_vJ_W₀_lside` ＋ `det_nJ_vJ_mul_dot_lside` 把符号传出来；
`←` 先由 `det_vJ_W₀_lside` ＋ `Primitive vJ` 取到整数 `d`，再定符号。
⚠ 共线格里两边同时为假（§22c）⟹ 本条在两格都为真，但只在横截格有内容。 -/
theorem W₀_pos_multiple_iff_detsign_lside {nJ p vJ1 vJ : ℤ × ℤ}
    (hnJ0 : nJ ≠ 0) (hvJprim : Primitive vJ)
    (hlevel : dot nJ vJ = 0) (hup : 0 < dot nJ p) :
    (∃ d : ℤ, 0 < d ∧ Nivat.HcombOrient.W₀ nJ p vJ1 = d • vJ) ↔
      0 < det p vJ * det p vJ1 := by
  have hvJ0 : vJ ≠ 0 := (prim_iff_primitive.mpr hvJprim).ne_zero
  have hvv : 0 < dot vJ vJ := dot_self_pos_lside hvJ0
  have hnn : 0 < dot nJ nJ := dot_self_pos_lside hnJ0
  have hC : det nJ vJ * dot nJ p = dot nJ nJ * det p vJ := det_nJ_vJ_mul_dot_lside p hlevel
  have hB : dot vJ (Nivat.HcombOrient.W₀ nJ p vJ1) = det p vJ1 * det nJ vJ :=
    dot_vJ_W₀_lside nJ p vJ1 vJ
  constructor
  · rintro ⟨d, hd, hW⟩
    have hdv : d * dot vJ vJ = det p vJ1 * det nJ vJ := by
      rw [← hB, hW, mpos_dot_zsmul]
    have hpos : 0 < det p vJ1 * det nJ vJ := by nlinarith [mul_pos hd hvv, hdv]
    have key : 0 < dot nJ nJ * (det p vJ * det p vJ1) := by
      calc (0 : ℤ) < det p vJ1 * det nJ vJ * dot nJ p := mul_pos hpos hup
        _ = det p vJ1 * (det nJ vJ * dot nJ p) := by ring
        _ = det p vJ1 * (dot nJ nJ * det p vJ) := by rw [hC]
        _ = dot nJ nJ * (det p vJ * det p vJ1) := by ring
    by_contra hcon
    push_neg at hcon
    nlinarith [key, mul_nonneg hnn.le (neg_nonneg.mpr hcon)]
  · intro hsign
    have hpos : 0 < det p vJ1 * det nJ vJ := by
      have key : 0 < det p vJ1 * det nJ vJ * dot nJ p := by
        calc (0 : ℤ) < dot nJ nJ * (det p vJ * det p vJ1) := mul_pos hnn hsign
          _ = det p vJ1 * (dot nJ nJ * det p vJ) := by ring
          _ = det p vJ1 * (det nJ vJ * dot nJ p) := by rw [← hC]
          _ = det p vJ1 * det nJ vJ * dot nJ p := by ring
      by_contra hcon
      push_neg at hcon
      nlinarith [key, mul_nonneg (neg_nonneg.mpr hcon) hup.le]
    obtain ⟨d, hd0⟩ :=
      exists_smul_of_det_eq_zero (prim_iff_primitive.mpr hvJprim) (det_vJ_W₀_lside p vJ1 hlevel)
    have hsm : (d : ℤ) • vJ = ((d * vJ.1, d * vJ.2) : ℤ × ℤ) := by
      simp [Prod.smul_def, smul_eq_mul]
    have hd : Nivat.HcombOrient.W₀ nJ p vJ1 = d • vJ := hd0.trans hsm.symm
    refine ⟨d, ?_, hd⟩
    have hdv : d * dot vJ vJ = det p vJ1 * det nJ vJ := by
      rw [← hB, hd, mpos_dot_zsmul]
    by_contra hcon
    push_neg at hcon
    nlinarith [hdv, hpos, mul_nonneg (neg_nonneg.mpr hcon) hvv.le]

/-! ## §23 ⭐⭐⭐ `hLsign` 不是欠账：它由字段**免费**得到
—— hbase 的 `W₀` 射线 ＋ 我 §20 的 `nL` 下界，两件东西一碰就闭合

## §23a 这一节推翻我自己上一轮的记账

§22e 我写「横截格里两条路欠的是同一个不等式 `0 < det p vJ · det p vJ1`」，并把它报成
`rec_vJ` 与 `bottom` 合取 4 的**共同唯一符号欠账**。本节证明：**那条不等式的非严格形是字段的推论**，
不是欠账。

机制是把两条已有的东西对撞：

* lane-tower-hbase 的 `ray_W₀_of_fields`（`TowerHbaseRecP.lean`，标识符名；我**未复跑**，
  但本节**不引用它**，而是就地重证同一条射线——见下）：`hhp` ＋ `rec_p` ＋ `hswept` ＋ 两个符号
  ⟹ `R` 含整条 `g₀ + ℕ•W₀`。
* 我 §20 的观察：链上有 `ahat_halfPlane_L`，即 `⟪nL, ·⟫` 在 `⋃Âᵢ` 上**有下界**，
  其中 `nL := det p vJ • dir p`。

射线上 `nL` 的读数是 `⟪nL,g₀⟫ + (α·m)·(det p vJ · det p vJ1)`（因为 `⟪nL,p⟫ = det p vJ · det p p = 0`
恒成立、`⟪nL,vJ1⟫ = det p vJ · det p vJ1`，`α := ⟪nJ,p⟫ > 0`）。若那个乘积 `< 0`，读数随 `m`
线性趋于 `−∞`，与下界矛盾。⟹

    detsign_of_fields_lside :
      U.Nonempty → (∀ z ∈ U, cJ ≤ ⟪nJ,z⟫) → (∀ z ∈ U, z + p ∈ U) →
      SweptClosed U vJ1 nJ cJ → (∀ z ∈ U, cL ≤ ⟪nL,z⟫) →
      0 < ⟪nJ,p⟫ → ⟪nJ,vJ1⟫ < 0 →
        0 ≤ det p vJ * det p vJ1

**每条前提都是现货**（对位读法，本文件不构造 `ChainDataGeomParts` 实例）：
`hne` ← `ahat_nonempty`（本文件 §18 的 `ahat_nonempty_of_halign_lside` 已从 `halign` 产出）；
`hhp` / `rec_p` / `hswept` / `ahat_halfPlane_L` ← `ChainDataGeomParts` 的同名字段；
`hup` / `hsweep` ← 字段的两个符号。⛔ **`rec_vJ` 不在前提里**——这一点要紧，否则循环。

⭐ **射线这一步是 hbase 的**（`ray_W₀_of_fields` 的机制：`s` 步 `p` 抬高 `sα`，`t` 步 `vJ1`
压低 `tβ`，取 `s = βm`、`t = αm` 使高度**不变**，于是 `hswept` 的侧条件恰被 `hhp g₀` 兑现）。
本节就地重证是为了不 import 他正在改的文件（我的 `check1.sh` 要稳定），不是因为不信他；
数学上这一步归他。我加的是「把 `hLbd` 按到那条射线上」这半句。

## §23b 合起来：`bottom_conj124` 的 `hLsign` 可以撤掉

    bottom_conj124_of_fields_lside :  与 §20 的 `bottom_conj124_of_recVJ_lside` 同结论，
      但**不收 `hLsign`**，改收字段 `hswept`。

⟹ **`bottom` 的合取 1 / 2 / 4 在两格都只欠 `rec_vJ`，不再欠任何定向。**
（§20 那条不撤，仍为真；它收的前提更弱，只是链上要另外兑现 `hLsign`。）

## §23c ⭐ 对 `rec_vJ` 的意思：横截格里 hbase 那句「同向」也是免费的

    W₀_pos_multiple_of_fields_transverse_lside :
      上面那堆字段 ＋ `det p vJ1 ≠ 0` ＋ `vJ ≠ 0` ＋ `Primitive vJ` ＋ `nJ ≠ 0` ＋ `⟪nJ,vJ⟫ = 0`
      ⟹ ∃ d : ℤ, 0 < d ∧ W₀ nJ p vJ1 = d • vJ

证法：§23a 给 `0 ≤ det p vJ · det p vJ1`；`det p vJ ≠ 0`（本文件 §2 的
`det_p_vJ_ne_of_fields`，输入是 `⟪nJ,vJ⟫=0` ＋ `⟪nJ,p⟫ ≠ 0` ＋ `vJ ≠ 0`，全是字段）
与横截假设 `det p vJ1 ≠ 0` 把「`= 0`」这一档排掉 ⟹ 严格 ⟹ §22d 的等价给出结论。

⟹ **这一条逐字就是 `TowerHbase.rec_vJ_of_W₀_pos_multiple` 的最后一个前提。**
⛔ 我**没有**把它接上去产 `rec_vJ`（那要 import 他的文件，且 `hconv` 还得从
`ColleReg.region_latticeConvex` 走，那是禁 import 的下游）。我只声明：**横截格里那格欠账没了**，
接线归他或集成者。

## §23d ⛔ 共线格照旧是死的，本节不动它

`det p vJ1 = 0` 时 §23a 给的是 `0 ≤ 0`，§23c 的严格化用不上，且 §22c 已证 `W₀ = 0`
⟹ `W₀` 路在共线格产不出 `rec_vJ`。**共线格的 `rec_vJ` 仍是真欠账**，形状未变。

## §23e 射程自限（PROTOCOL §15 / §51 / §55）

1. 本节只证下面三条。**没有**证任何一格的 `rec_vJ`；`rec_vJ` 的最后一步接线在 hbase 的文件里，
   我没跑。
2. 「每条前提都是字段」是**对位读法**：本文件不构造 `ChainDataGeomParts` 实例，也不 import
   `RegionSteps` / `ColleRegion`。`hconv` 我根本没收（§23a / §23c 都不用凸性）。
3. hbase 的 `ray_W₀_of_fields` / `rec_vJ_of_real_dir` 我**未复跑**，按他所报记账（§55）；
   §23a 的射线是我就地重证的，不依赖他的声明。
4. 本轮**没有**亲读 `b3_colle2.txt`。
5. ⚠ 本节**撤回** §22e 表格里「横截格：我 §20 `hLsign` ＝ 真条件，欠符号」那一格与
   §22e 结论 2 的「立案记一条」——**横截格里那一格不欠**，应记 0。§22c / §22d 的内核内容
   全部照旧不撤。 -/

/-- **线性下界引理**：若 `c ≤ M + (a·m)·A` 对一切 `m : ℕ` 成立且 `a > 0`，则 `A ≥ 0`。 -/
theorem nonneg_of_linear_bounded_lside {c M A a : ℤ} (hapos : 0 < a)
    (h : ∀ m : ℕ, c ≤ M + (a * (m : ℤ)) * A) : 0 ≤ A := by
  by_contra hcon
  push_neg at hcon
  have hA1 : A ≤ -1 := by omega
  have hmge : M - c + 1 ≤ (((M - c + 1).toNat : ℕ) : ℤ) := Int.self_le_toNat _
  have hm0 : (0 : ℤ) ≤ (((M - c + 1).toNat : ℕ) : ℤ) := Int.natCast_nonneg _
  have hX : (((M - c + 1).toNat : ℕ) : ℤ) ≤ a * (((M - c + 1).toNat : ℕ) : ℤ) := by nlinarith
  have hXnn : (0 : ℤ) ≤ a * (((M - c + 1).toNat : ℕ) : ℤ) := by nlinarith
  have hstep : (a * (((M - c + 1).toNat : ℕ) : ℤ)) * A
      ≤ -(a * (((M - c + 1).toNat : ℕ) : ℤ)) := by nlinarith
  have hh := h (M - c + 1).toNat
  linarith

/-- ⭐⭐⭐ **`hLsign` 是字段的推论，不是欠账。**

    0 ≤ det p vJ * det p vJ1

输入只有 `hne` / `hhp` / `rec_p` / `hswept` / `ahat_halfPlane_L` ＋ 两个符号，**不含 `rec_vJ`、
不含凸性**。机制：hbase 的 `W₀` 射线（`s = βm` 步 `p` ＋ `t = αm` 步 `vJ1`，高度不变，故
`hswept` 的侧条件由 `hhp g₀` 兑现）上 `⟪nL,·⟫` 的读数是
`⟪nL,g₀⟫ + (α·m)·(det p vJ · det p vJ1)`（`⟪nL,p⟫ = 0` 恒成立），若乘积为负则趋于 `−∞`，
与 `ahat_halfPlane_L` 的下界矛盾。 -/
theorem detsign_of_fields_lside {U : Set (ℤ × ℤ)} {nJ vJ vJ1 p : ℤ × ℤ} {cJ cL : ℤ}
    (hne : U.Nonempty)
    (hhp : ∀ z ∈ U, cJ ≤ dot nJ z)
    (hrecp : ∀ z ∈ U, z + p ∈ U)
    (hswept : MaxEnv.SweptClosed U vJ1 nJ cJ)
    (hLbd : ∀ z ∈ U, cL ≤ dot (det p vJ • ((-p.2 : ℤ), p.1)) z)
    (hup : 0 < dot nJ p) (hsweep : dot nJ vJ1 < 0) :
    0 ≤ det p vJ * det p vJ1 := by
  obtain ⟨g, hg⟩ := hne
  obtain ⟨a, ha⟩ : ∃ a : ℕ, (a : ℤ) = dot nJ p :=
    ⟨(dot nJ p).toNat, Int.toNat_of_nonneg hup.le⟩
  obtain ⟨b, hb⟩ : ∃ b : ℕ, (b : ℤ) = - dot nJ vJ1 :=
    ⟨(- dot nJ vJ1).toNat, Int.toNat_of_nonneg (by omega)⟩
  have hapos : (0 : ℤ) < (a : ℤ) := by omega
  have hnLp : dot (det p vJ • ((-p.2 : ℤ), p.1)) p = 0 := by
    rw [dot_nL_eq_det_lside]
    simp only [det]
    ring
  have hnLv : dot (det p vJ • ((-p.2 : ℤ), p.1)) vJ1 = det p vJ * det p vJ1 :=
    dot_nL_eq_det_lside p vJ vJ1
  have hray : ∀ m : ℕ, g + ((b * m : ℕ) : ℤ) • p + ((a * m : ℕ) : ℤ) • vJ1 ∈ U := by
    intro m
    have h1 : g + ((b * m : ℕ) : ℤ) • p ∈ U := mpos_rec_iter hrecp (b * m) g hg
    refine hswept _ h1 (a * m) ?_
    have hval : dot nJ (g + ((b * m : ℕ) : ℤ) • p + ((a * m : ℕ) : ℤ) • vJ1) = dot nJ g := by
      rw [dot_add, dot_add, mpos_dot_zsmul, mpos_dot_zsmul, ← ha]
      have e2 : dot nJ vJ1 = -(b : ℤ) := by omega
      rw [e2]
      push_cast
      ring
    rw [hval]
    exact hhp g hg
  refine nonneg_of_linear_bounded_lside (c := cL)
    (M := dot (det p vJ • ((-p.2 : ℤ), p.1)) g) (a := (a : ℤ)) hapos ?_
  intro m
  have hmem := hLbd _ (hray m)
  have hval : dot (det p vJ • ((-p.2 : ℤ), p.1))
        (g + ((b * m : ℕ) : ℤ) • p + ((a * m : ℕ) : ℤ) • vJ1)
      = dot (det p vJ • ((-p.2 : ℤ), p.1)) g
        + ((a : ℤ) * (m : ℤ)) * (det p vJ * det p vJ1) := by
    rw [dot_add, dot_add, mpos_dot_zsmul, mpos_dot_zsmul, hnLp, hnLv]
    push_cast
    ring
  rw [hval] at hmem
  exact hmem

/-- ⭐⭐ **§20 的 `bottom` 合取 1/2/4，去掉 `hLsign`、改收字段 `hswept`。**

与 `bottom_conj124_of_recVJ_lside` 同结论；`hLsign` 由 `detsign_of_fields_lside` 现算。
⟹ `bottom` 的这三条合取在**两格**都只欠 `rec_vJ`，不再欠任何定向。 -/
theorem bottom_conj124_of_fields_lside
    {U : Set (ℤ × ℤ)} {nJ vJ vJ1 p : ℤ × ℤ} {cJ cL : ℤ}
    (hconv : IsLatticeConvexRegion U) (hne : U.Nonempty)
    (hnJprim : Primitive nJ) (hvJprim : Primitive vJ)
    (hrecvJ : ∀ z ∈ U, z + vJ ∈ U) (hrecp : ∀ z ∈ U, z + p ∈ U)
    (hhp : ∀ z ∈ U, cJ ≤ dot nJ z)
    (hswept : MaxEnv.SweptClosed U vJ1 nJ cJ)
    (hlevel : dot nJ vJ = 0) (hup : 0 < dot nJ p) (hsweep : dot nJ vJ1 < 0)
    (hLbd : ∀ z ∈ U, cL ≤ dot (det p vJ • ((-p.2 : ℤ), p.1)) z)
    (hdet : det p vJ ≠ 0)
    (ε : ℕ) :
    ∃ (z₀ : ℤ × ℤ) (L : ℤ),
      dot nJ z₀ = cJ - (ε : ℤ) - 1 ∧
      (∀ k : ℤ, L ≤ k → z₀ + k • vJ ∈ MaxEnv.reachSet U vJ1) ∧
      (∀ z ∈ MaxEnv.shell U vJ1 nJ cJ (ε + 1),
        z ∈ MaxEnv.shell U vJ1 nJ cJ ε ∨ ∃ k : ℤ, L ≤ k ∧ z = z₀ + k • vJ) :=
  bottom_conj124_of_recVJ_lside hconv hne hnJprim hvJprim hrecvJ hrecp hlevel hup hsweep
    hLbd hdet (detsign_of_fields_lside hne hhp hrecp hswept hLbd hup hsweep) ε

/-- ⭐⭐ **横截格里 hbase 那句「同向」也是字段的推论。**

结论逐字是 `TowerHbase.rec_vJ_of_W₀_pos_multiple` 的最后一个前提。
⛔ 本文件**不**把它接上去产 `rec_vJ`（那要 import 他的文件，且 `hconv` 还得走
`ColleReg.region_latticeConvex`，在禁 import 的下游）。
⛔ 共线格（`det p vJ1 = 0`）用不上本条，且按 §22c 那里 `W₀ = 0`、结论恒假。 -/
theorem W₀_pos_multiple_of_fields_transverse_lside
    {U : Set (ℤ × ℤ)} {nJ vJ vJ1 p : ℤ × ℤ} {cJ cL : ℤ}
    (hne : U.Nonempty)
    (hhp : ∀ z ∈ U, cJ ≤ dot nJ z)
    (hrecp : ∀ z ∈ U, z + p ∈ U)
    (hswept : MaxEnv.SweptClosed U vJ1 nJ cJ)
    (hLbd : ∀ z ∈ U, cL ≤ dot (det p vJ • ((-p.2 : ℤ), p.1)) z)
    (hnJ0 : nJ ≠ 0) (hvJprim : Primitive vJ)
    (hlevel : dot nJ vJ = 0) (hup : 0 < dot nJ p) (hsweep : dot nJ vJ1 < 0)
    (htrans : det p vJ1 ≠ 0) :
    ∃ d : ℤ, 0 < d ∧ Nivat.HcombOrient.W₀ nJ p vJ1 = d • vJ := by
  have hvJ0 : vJ ≠ 0 := (prim_iff_primitive.mpr hvJprim).ne_zero
  have hdet : det p vJ ≠ 0 := det_p_vJ_ne_of_fields hlevel hup.ne' hvJ0
  have hnn : 0 ≤ det p vJ * det p vJ1 :=
    detsign_of_fields_lside hne hhp hrecp hswept hLbd hup hsweep
  have hne0 : det p vJ * det p vJ1 ≠ 0 := mul_ne_zero hdet htrans
  exact (W₀_pos_multiple_iff_detsign_lside hnJ0 hvJprim hlevel hup).mpr
    (lt_of_le_of_ne hnn (Ne.symm hne0))

/-!
### §24 共线格（`J = ι+1`）的 `rec_vJ`：**线性字段族推不出来**（内核反例）

**§24a 这一格是什么、原文允不允许。** 集成者第 240 轮派工：在 `ChainDataGeomParts` 上，
从 `det p vJ1 = 0` 加字段推出 `False`，或推出 `rec_vJ` 的另一条路。先做硬规矩 6。

原文定位（我本轮亲读 `scratch/b3_colle2.txt`，逐字）：

* `:498`「let $\iota+1\leq J\leq\iota+m-1$ be the smallest integer such that」——`J` 的窗口，
  判据是 `|Â_i ∩ w_i(J)| < |Â_{i+1} ∩ w_{i+1}(J)|` **for infinitely many `i`**（`:500`）。
* `:502`「**If $J>\iota+1$**, we also may assume that」——**条件式** ⟹ `J = ι+1` 是被允许的一支，
  不是被排除的退化情形。窗口下界 `ι+1` 在 `:432` / `:498` 两处独立出现，无一处抬到 `ι+2`。
* `:440`（＝ `:458` 的孪生条）「$\hat{A}_{\infty}^{(\epsilon)}:=\{g+t\vec{v}_{\ell_{J-1}}:\dots\}$」
  ——本仓字段 `vJ1` 的锚就在这里，是 **`v⃗_{ℓ_{J−1}}`**，且原文写的是 `g + t·(…)`，
  与 `MaxEnv.SweptClosed` 的 `g + t • vJ1` 同号。
* `:518`「$\{g-t\vec{v}_{\ell_{J+1}}\dots\}$」——这是**另一个字段 `w`**（`ChainPartsFeed` 的
  `w` 字段 docstring 自己这么写），`ℓ_{J+1}` 在全文只出现这一次（`grep -cF 'ell}_{J+1}'` = 1）。
* `:386`「Let `ℓ, ℓ'` be rational oriented lines **in distinct directions** … is called an
  `(ℓ,ℓ')`-region」＋ `:506`「`Â_∞` … **is an `(ℓ,ℓ_J)`-region**」⟹ `ℓ_J ∦ ℓ` ⟹ `det p vJ ≠ 0`。

⟹ `det p vJ1 = 0 ⟺ ℓ_{J−1} ∥ ℓ_ι ⟺ J−1 = ι ⟺ **J = ι+1**`（窗口内 `ι ≤ J−1 ≤ ι+m−2`，
故 `J−1 = ι+m` 这一支被窗口排除）。这与 `ChainPartsFeed` 的 `vJ1` 字段 docstring 第 2 条
（「`vJ1 = m • vl`（共线）… 在窗口里**只能**是 `J = ι+1`」）一致，与 lane-tower-hbase 本轮
`hb_det_p_vJ1_eq_zero_iff_collinear` 的读数一致（**他报，我未复跑**）。

⟹ **派工的第一支（推 `False`）在原文层面就没有指望**：`J = ι+1` 是原文明写允许的一支。

**§24b 数值实例（硬规矩 6）——哪个字段先崩？答案是：一个都不崩。** 取

    vl = (1,0)   p = (-1,0)（cc = 1）   vJ1 = (1,0)   vJ = (0,1)   nJ = (-1,0)   cJ = 0
    nL := det p vJ • (-p.2, p.1) = (-1) • (0,-1) = (0,1)          cL = 0
    U  := {z | z.1 ≤ 0 ∧ z.2 = 0}

（符号是被字段逼出来的，不是我挑的：`hp : p = -cc•vl` ＋ `hup : 0 < ⟪nJ,p⟫` ⟹ `⟪nJ,vl⟫ < 0`；
`det p vJ1 = 0` ⟹ `vJ1 = τ•vl`；`hsweep : ⟪nJ,vJ1⟫ < 0` ⟹ `τ > 0`；`Primitive vJ1` ⟹ `τ = 1`
⟹ **共线格里 `vJ1 = vl`**，扫掠方向与 `rec_p` 方向严格反向。）

逐条核：`hconv` ✓（`collinearStrip_convex_lside`）、`ahat_nonempty` ✓、`hfin`＋`AhatMono`
✓（`collinearStrip_chain_lside`：`U` 是一列有限集的单调并）、`rec_p` ✓、`hhp` ✓、
`hswept` ✓（`+vJ1` 降高，守卫 `cJ ≤ ⟪nJ,·⟫` 恰好把它截在 `z.1 ≤ 0`）、`ahat_halfPlane_L` ✓
（`⟪nL,z⟫ = z.2 = 0 ≥ cL`）、`hlevel` ✓、`hup` ✓、`hsweep` ✓、四条 `Primitive` ✓、
`det p vJ ≠ 0` ✓、`det p vJ1 = 0` ✓。而 `rec_vJ` 在 `(0,0)` 处就假：`(0,1) ∉ U`。

**§24c 结论（`rec_vJ_not_from_linear_fields_collinear_lside`）。** 共线格的 `rec_vJ`
**不是**下面这族前提的推论：凸性 ＋ 非空 ＋「有限集单调并」＋ `rec_p` ＋ `hhp` ＋ `hswept`
＋ `ahat_halfPlane_L` ＋ `hlevel`/`hup`/`hsweep` ＋ 四条 `Primitive` ＋ `hp`/`0 < cc`
＋ `det p vJ ≠ 0` ＋ `det p vJ1 = 0`。⟹ 任何只用这些的证法在共线格必定失败，
不必再试（也包括我自己 §20/§23 用的那一族——`detsign_of_fields_lside` 在共线格的结论退化成
`0 ≤ 0`，本来就没信息）。

⛔ **射程自限（勿放大）**：本条**没有**否 `rec_vJ` 本身，也没有否「从 `ChainDataGeomParts`
推 `rec_vJ`」。上面那族里**不含**包络/极大性/壳四条：`envShift`/`envB`/`maxA`/`subBA`/`subAB`，
以及 `escapeW`/`shellSubStrip`/`shellEnv`/`fillCover`/`bottom`。反例对象 `U` 只是一条射线，
我**没有**为它造 `A`/`B`/`u`/`kk` 与 `maxA`，所以它**不是** `ChainDataGeomParts` 的一个实例。
本条说的是「哪些字段不够」，不是「整个结构不够」。

**§24d 那么共线格该走哪条路。** 原文给 `rec_vJ` 的理由在 `:506`：`Â_∞` 是 `(ℓ,ℓ_J)`-region，
有一条**平行于 `ℓ_J` 的半无限边**——半无限边就是 `rec_vJ`。这句由「In particular」领起，
其前提是 `:498-500` 的**增长判据**（`J` 那条边的长度沿 `i` 严格增，无限次）。§24b 的反例正好
在这一点上假：那条射线的「`ℓ_J` 边」长度恒为 1，不增。⟹ 共线格缺的不是一条不等式，
而是**增长判据本身**——它在 `ChainDataGeomParts` 里没有对应字段（`AhatMono` 只给 `⊆`，
不给严格增）。按硬规矩 5，这是**生产者侧要带进来的一条新字段**，不是本结构的推论；
硬规矩 19/22：在能点名消费者之前我不自造该字段。lane-tower-hbase 本轮宣布去做
**不分格**的 `rec_vJ`，走的正是 `:506` 这条半无限边——本节的作用是把「线性那一族到此为止」
钉死，省得两边都往那里扑。
-/

/-- §24 的反例对象：`U := {z | z.1 ≤ 0 ∧ z.2 = 0}`，即 `(0,0)` 出发沿 `-vl` 的整点射线。
在 §24b 的赋值下它满足所有线性字段而 `rec_vJ` 假。 -/
def collinearStrip_lside : Set (ℤ × ℤ) := {z : ℤ × ℤ | z.1 ≤ 0 ∧ z.2 = 0}

/-- §24b 的 `hconv`：射线是格凸区域（取 `C = {q | q.1 ≤ 0 ∧ q.2 = 0}`，闭半平面 ∩ 直线）。 -/
theorem collinearStrip_convex_lside : IsLatticeConvexRegion collinearStrip_lside := by
  refine ⟨{q : ℝ × ℝ | q.1 ≤ 0 ∧ q.2 = 0}, ?_, ?_, ?_⟩
  · intro x hx y hy a b ha hb _
    refine ⟨?_, ?_⟩
    · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      have h1 : (0 : ℝ) ≤ a * (-x.1) := mul_nonneg ha (by linarith [hx.1])
      have h2 : (0 : ℝ) ≤ b * (-y.1) := mul_nonneg hb (by linarith [hy.1])
      nlinarith [h1, h2]
    · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      rw [hx.2, hy.2]
      ring
  · have h1 : IsClosed {q : ℝ × ℝ | q.1 ≤ 0} := isClosed_le continuous_fst continuous_const
    have h2 : IsClosed {q : ℝ × ℝ | q.2 = 0} := isClosed_eq continuous_snd continuous_const
    exact h1.inter h2
  · have hz : ∀ z : ℤ × ℤ,
        (toReal z ∈ {q : ℝ × ℝ | q.1 ≤ 0 ∧ q.2 = 0}) ↔ (z.1 ≤ 0 ∧ z.2 = 0) := by
      intro z
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨?_, ?_⟩
        · have h1' : ((z.1 : ℤ) : ℝ) ≤ 0 := h1
          exact_mod_cast h1'
        · have h2' : ((z.2 : ℤ) : ℝ) = 0 := h2
          exact_mod_cast h2'
      · rintro ⟨h1, h2⟩
        refine ⟨?_, ?_⟩
        · show ((z.1 : ℤ) : ℝ) ≤ 0
          exact_mod_cast h1
        · show ((z.2 : ℤ) : ℝ) = 0
          exact_mod_cast h2
    ext z
    exact (hz z).symm

/-- §24b 的 `hfin` ＋ `AhatMono`：射线是一列**有限**集的**单调**并。 -/
theorem collinearStrip_chain_lside :
    ∃ F : ℕ → Set (ℤ × ℤ), (∀ i, (F i).Finite) ∧ (∀ i j, i ≤ j → F i ⊆ F j) ∧
      collinearStrip_lside = ⋃ i, F i := by
  refine ⟨fun i => (fun k : ℕ => ((-(k : ℤ), (0 : ℤ)) : ℤ × ℤ)) '' Set.Iic i, ?_, ?_, ?_⟩
  · intro i
    exact (Set.finite_Iic i).image _
  · intro i j hij
    exact Set.image_mono (fun k hk => le_trans hk hij)
  · ext z
    simp only [collinearStrip_lside, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_image,
      Set.mem_Iic]
    constructor
    · rintro ⟨h1, h2⟩
      have ht : (((-z.1).toNat : ℕ) : ℤ) = -z.1 := Int.toNat_of_nonneg (by omega)
      refine ⟨(-z.1).toNat, (-z.1).toNat, le_refl _, Prod.ext ?_ ?_⟩
      · show -(((-z.1).toNat : ℕ) : ℤ) = z.1
        rw [ht, neg_neg]
      · show (0 : ℤ) = z.2
        exact h2.symm
    · rintro ⟨i, k, _, rfl⟩
      exact ⟨neg_nonpos.mpr (Int.natCast_nonneg k), rfl⟩

/-- ⭐ **§24c：共线格的 `rec_vJ` 不是线性字段族的推论**（内核反例，见 §24b 的赋值）。

⛔ 射程见 §24b–§24d：前提族里**不含** `envShift`/`envB`/`maxA`/`subBA`/`subAB` 与
`escapeW`/`shellSubStrip`/`shellEnv`/`fillCover`/`bottom`；本条**不**主张
`ChainDataGeomParts ⊬ rec_vJ`。 -/
theorem rec_vJ_not_from_linear_fields_collinear_lside :
    ¬ ∀ (U : Set (ℤ × ℤ)) (vl p nJ vJ vJ1 : ℤ × ℤ) (cc : ℕ) (cJ cL : ℤ),
        IsLatticeConvexRegion U →
        U.Nonempty →
        (∃ F : ℕ → Set (ℤ × ℤ), (∀ i, (F i).Finite) ∧ (∀ i j, i ≤ j → F i ⊆ F j) ∧
          U = ⋃ i, F i) →
        Primitive vl → Primitive nJ → Primitive vJ → Primitive vJ1 →
        0 < cc → p = -(cc : ℤ) • vl →
        (∀ z ∈ U, z + p ∈ U) →
        (∀ z ∈ U, cJ ≤ dot nJ z) →
        MaxEnv.SweptClosed U vJ1 nJ cJ →
        (∀ z ∈ U, cL ≤ dot (det p vJ • ((-p.2 : ℤ), p.1)) z) →
        dot nJ vJ = 0 → 0 < dot nJ p → dot nJ vJ1 < 0 →
        det p vJ ≠ 0 → det p vJ1 = 0 →
        (∀ z ∈ U, z + vJ ∈ U) := by
  intro h
  have h00 : ((0 : ℤ), (0 : ℤ)) ∈ collinearStrip_lside := ⟨le_refl 0, rfl⟩
  have hrecp : ∀ z ∈ collinearStrip_lside,
      z + ((-1 : ℤ), (0 : ℤ)) ∈ collinearStrip_lside := by
    rintro z ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · show z.1 + (-1 : ℤ) ≤ 0
      omega
    · show z.2 + (0 : ℤ) = 0
      omega
  have hhp : ∀ z ∈ collinearStrip_lside, (0 : ℤ) ≤ dot ((-1 : ℤ), (0 : ℤ)) z := by
    rintro z ⟨h1, h2⟩
    show (0 : ℤ) ≤ (-1 : ℤ) * z.1 + (0 : ℤ) * z.2
    omega
  have hswept : MaxEnv.SweptClosed collinearStrip_lside ((1 : ℤ), (0 : ℤ))
      ((-1 : ℤ), (0 : ℤ)) 0 := by
    rintro g ⟨h1, h2⟩ t ht
    simp only [dot, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul] at ht
    refine ⟨?_, ?_⟩
    · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      omega
    · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      omega
  have key := h collinearStrip_lside ((1 : ℤ), (0 : ℤ)) ((-1 : ℤ), (0 : ℤ))
      ((-1 : ℤ), (0 : ℤ)) ((0 : ℤ), (1 : ℤ)) ((1 : ℤ), (0 : ℤ)) 1 0 0
      collinearStrip_convex_lside ⟨_, h00⟩ collinearStrip_chain_lside
      (by exact isCoprime_one_left) (by exact isCoprime_one_left.neg_left)
      (by exact isCoprime_one_right) (by exact isCoprime_one_left)
      Nat.one_pos (by simp [Prod.ext_iff])
      hrecp hhp hswept
      (by
        rintro z ⟨h1, h2⟩
        simp only [det, dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
        omega)
      (by norm_num [dot]) (by norm_num [dot]) (by norm_num [dot])
      (by norm_num [det]) (by norm_num [det])
  have hbad := key ((0 : ℤ), (0 : ℤ)) h00
  have hb2 : (0 : ℤ) + 1 = 0 := hbad.2
  omega

/-!
### §25 共线格的「纤维填满」：`rec_p` ＋ `hswept` ⟹ 每条 `vl`-纤维被填满到半平面边界

§24 的反例给出了共线格 `U` 的**形状**：在 `(vl, vJ)` 坐标下它是 `{α ≤ A₀} × Λ`，
即「每一层上是一条向 `-vl` 无限延伸、被 `cJ` 截住的半直线，层集 `Λ` 待定」。
本节把这个形状里**不依赖增长判据**的那一半证出来，它是 §24d 那条原文路线的第一步，
共线/横截两格的证法都要用（横截格里 `vJ1 ∦ vl`，本节不适用，故只声明共线格）。

**§25a 机制。** `hp : p = -cc•vl`（`cc > 0`）⟹ `rec_p` 把点沿 `-vl` 方向**按 `cc` 步长**推；
`hsweep : ⟪nJ,vJ1⟫ < 0` ＋ 共线格的 `vJ1 = vl`（`NOTATION.md` 的「`m` 已钉死为 `+1`」一节，
两条独立证据：`GcdCollapse.vJ1_eq_vl_of_prim` 与本文件的
`not_ccw_instantiation_of_chain_stock`）⟹ `hswept` 把点沿 `+vl` 推、**守卫只看终点高度**
（`MaxEnv.SweptClosed` 的定义：`cJ ≤ dot n (g + t • v) → g + t • v ∈ A`，标识符名 `SweptClosed`）。
两者合起来：先用 `rec_p` 往左跨过目标（`cc ≥ 1` 保证 `k := -t` 步一定够），再用 `hswept`
一次跳回目标点，**中途高度不必检查**，因为守卫只约束终点。⟹ 步长 `cc > 1` 不构成障碍，
这正是「按 `cc` 步长推」不够而「守卫只看终点」补上的那一格。

⚠ 本节**没有**用凸性、没有用 `ahat_halfPlane_L`、没有用增长判据；也**没有**声称
`Λ` 是区间或上闭（那正是 §24 证明「线性字段族给不出」的那一半）。
-/

/-- ⭐ **§25a 纤维填满（`t` 形）**：共线格里，`z ∈ U` 且 `z + t•vl` 高度够 ⟹ `z + t•vl ∈ U`。
对**所有** `t : ℤ`（正负皆可），不需要凸性。 -/
theorem fiber_fill_collinear_lside {U : Set (ℤ × ℤ)} {nJ vl p : ℤ × ℤ} {cJ : ℤ} {cc : ℕ}
    (hccpos : 0 < cc) (hp : p = -(cc : ℤ) • vl)
    (hrecp : ∀ z ∈ U, z + p ∈ U)
    (hswept : MaxEnv.SweptClosed U vl nJ cJ)
    {z : ℤ × ℤ} (hz : z ∈ U) (t : ℤ) (hh : cJ ≤ dot nJ (z + t • vl)) :
    z + t • vl ∈ U := by
  by_cases ht : 0 ≤ t
  · obtain ⟨j, hj⟩ : ∃ j : ℕ, (j : ℤ) = t := ⟨t.toNat, Int.toNat_of_nonneg ht⟩
    have hstep := hswept z hz j (by rw [hj]; exact hh)
    rwa [hj] at hstep
  · have ht' : t < 0 := by omega
    obtain ⟨k, hkz⟩ : ∃ k : ℕ, (k : ℤ) = -t :=
      ⟨(-t).toNat, Int.toNat_of_nonneg (by omega)⟩
    have hbase : z + (k : ℤ) • p ∈ U := mpos_rec_iter hrecp k z hz
    have hpk : (k : ℤ) • p = (-((k : ℤ) * (cc : ℤ))) • vl := by
      rw [hp, smul_smul]
      congr 1
      ring
    rw [hpk] at hbase
    have h1 : (1 : ℤ) ≤ (cc : ℤ) := by exact_mod_cast hccpos
    have hs0 : 0 ≤ t + (k : ℤ) * (cc : ℤ) := by
      have h2 : (k : ℤ) * (cc : ℤ) = (-t) * (cc : ℤ) := by rw [hkz]
      rw [h2]
      nlinarith [mul_le_mul_of_nonneg_left h1 (le_of_lt (neg_pos.mpr ht'))]
    obtain ⟨j, hj⟩ : ∃ j : ℕ, (j : ℤ) = t + (k : ℤ) * (cc : ℤ) :=
      ⟨_, Int.toNat_of_nonneg hs0⟩
    have heq : (z + (-((k : ℤ) * (cc : ℤ))) • vl) + (j : ℤ) • vl = z + t • vl := by
      rw [hj, add_assoc, ← add_smul]
      congr 2
      ring
    have hstep := hswept _ hbase j (by rw [heq]; exact hh)
    rwa [heq] at hstep

/-- **§25a 纤维填满（`det` 形）**：把「同一条 `vl`-纤维」写成 `det vl (w − z) = 0`，
配 `Primitive vl` 得整系数。这是接线时要用的形状（`w` 由别处给出，不是 `z + t•vl` 的样子）。 -/
theorem fiber_fill_of_det_collinear_lside {U : Set (ℤ × ℤ)} {nJ vl p : ℤ × ℤ} {cJ : ℤ} {cc : ℕ}
    (hccpos : 0 < cc) (hp : p = -(cc : ℤ) • vl) (hvlprim : Primitive vl)
    (hrecp : ∀ z ∈ U, z + p ∈ U)
    (hswept : MaxEnv.SweptClosed U vl nJ cJ)
    {z w : ℤ × ℤ} (hz : z ∈ U) (hdet : det vl (w - z) = 0) (hh : cJ ≤ dot nJ w) :
    w ∈ U := by
  obtain ⟨d, hd⟩ := exists_smul_of_det_eq_zero (prim_iff_primitive.mpr hvlprim) hdet
  have hsm : ((d * vl.1, d * vl.2) : ℤ × ℤ) = d • vl := by
    simp [Prod.smul_def, smul_eq_mul]
  have hw : w = z + d • vl := by
    rw [← hsm, ← hd]
    abel
  rw [hw]
  exact fiber_fill_collinear_lside hccpos hp hrecp hswept hz d (by rw [← hw]; exact hh)

/-- **§25b 推论：共线格里 `rec_vJ` ⟺「层集上闭」**的那一半（向下的方向）。
`hlevel : ⟪nJ,vJ⟫ = 0` ⟹ `z + vJ` 与 `z` 同高 ⟹ 只要**该层上有一个** `U` 的点，
`z + vJ` 就自动进 `U`。⟹ 共线格的 `rec_vJ` 完全归结为「每一层非空」，
与「该层上具体哪个点」无关——这正是 §24d 说的、要由增长判据兑现的那一句。 -/
theorem rec_vJ_of_level_witness_collinear_lside {U : Set (ℤ × ℤ)} {nJ vl p vJ : ℤ × ℤ}
    {cJ : ℤ} {cc : ℕ}
    (hccpos : 0 < cc) (hp : p = -(cc : ℤ) • vl) (hvlprim : Primitive vl)
    (hrecp : ∀ z ∈ U, z + p ∈ U)
    (hswept : MaxEnv.SweptClosed U vl nJ cJ)
    (hhp : ∀ z ∈ U, cJ ≤ dot nJ z)
    (hlevel : dot nJ vJ = 0)
    (hwit : ∀ z ∈ U, ∃ y ∈ U, det vl (z + vJ - y) = 0) :
    ∀ z ∈ U, z + vJ ∈ U := by
  intro z hz
  obtain ⟨y, hy, hdy⟩ := hwit z hz
  refine fiber_fill_of_det_collinear_lside hccpos hp hvlprim hrecp hswept hy hdy ?_
  have : dot nJ (z + vJ) = dot nJ z := by
    simp only [dot, Prod.fst_add, Prod.snd_add] at hlevel ⊢
    linear_combination hlevel
  rw [this]
  exact hhp z hz

/-! ## §26  原文自己的那条路：`hgrow ⟹ rec_vJ`，**与格无关**

集成者 2026-09-26 批准整块落地（他亲跑探针 `tmp/wip/lane-leafa-shell-hgrow-probe.lean`，
EXIT=0、三条公理全白）。本节不新增 import：`ItemII` / `ChainPartsFeed` / `RecVJFromParts`
本文件头部已带齐。

**§26 的由来（原文侧，我亲读 `scratch/b3_colle2.txt`）。** §24/§25 两节把共线格
（`det p vJ1 = 0`）当成一道坎，是因为链上把 `rec_vJ` 走了 `⟨p, vJ1⟩` 锥（`hcomb` / `W₀`）
这条路。**原文不走这条路**，四处逐字为证（集成者 2026-09-26 复核四处，写进第 239 轮裁决四）：

1. `b3_colle2.txt:440` 与 `:458` 是 `ℓ_{J−1}` 在全文的**仅有两处**，都在 `Â_∞^{(ε)}` 的
   **定义式**里（items (i) / (ii)）；**没有任何推理步使用 `ℓ_{J−1}`**。
2. `b3_colle2.txt:432` 的结论是「`Â_∞` 是一个 `(ℓ_ι, ℓ_J)`-region」——Def 3.1
   （`b3_colle2.txt:386`）要求方向互异的是 `(ℓ_ι, ℓ_J)`，**不是** `(ℓ_ι, ℓ_{J−1})`。
   `J = ι+1` 时 `ℓ_{ι+1} ≠ ℓ_ι` 由 `:424` 的枚举给出，结论原样成立。
3. `b3_colle2.txt:502` 逐字是「**If $J>\iota+1$**, we also may assume that」，而 `:506` 的
   指标范围逐字是「for every $\iota+1\leq j\leq J-1$」。`J = ι+1` 时该区间**为空**
   ⟹ 那条辅助假设自动兑现；**原文自己用一个 `If` 把这一格挡掉了**。
4. `b3_colle2.txt:506` 的两条半无限边逐字是「one ∥ `ℓ`, the other ∥ `ℓ_J`」，
   **两条都不是 `ℓ_{J−1}`**。

⟹ 原文全程需要的横截方向是 `ℓ_J`，而 `det p vJ ≠ 0` 在链上是现货
（`EnvRefuteOrient.det_p_vJ_ne_zero_of_parts`，零前提）。

**§26 的内容。** `rec_vJ_of_pinned_growth_parts` 把 `CORE-HOLES.md` 的 `(G-a)` 那条路线
（`hgrow` → `ray_of_pinned_growth` → `rec_of_ray`，路线**不是**我发现的，(G-a) 已写明）
代入 `ChainDataGeomParts`：**签名里一个 `det p vJ1` 都没有** ⟹ 共线格与横截格共用同一条，
凸性由 `RecVJFromParts` 的 `latticeConvex_of_parts` 免费，不是 binder。

`no_ray_of_bounded_lside` 是 §24 那族反例的机制说清版：`dot n` 在 `U` 上有上界
＋ `0 < dot n d` ⟹ `U` 里没有 `d`-射线。它同时解释两个见证族——本文件 §24 的
`collinearStrip_lside`（取 `n = (0,1)`、`C = 0`）与 lane-tower-hbase §24 的 `hbQ`
（取 `n = (1,0)`、`C = 0`，`hbd` 逐字就是他那条的第一个合取；**他报，我未复跑**）。
⟹ 两个反例族缺的是同一样东西：**`+vJ` 方向的无界性**，也就是 `hgrow`。
-/

/-- **被上界挡死的射线**：若 `dot n` 在 `U` 上有上界 `C`，而 `0 < dot n d`，
则 `U` 里没有任何 `d`-射线。

取 `K := (C - dot n g).toNat + 1`，则 `dot n (g + K•d) ≥ dot n g + K > C`，与上界矛盾。

⚠ 本条与原文无关（纯线性代数），是 §24 那族反例的**机制**，不对应 `b3_colle2.txt` 任何一行。
它说明 §24 的反例判死的是「那张字段表」，**不是**共线格本身。 -/
theorem no_ray_of_bounded_lside {U : Set (ℤ × ℤ)} {n d g : ℤ × ℤ} {C : ℤ}
    (hbd : ∀ z ∈ U, dot n z ≤ C) (hpos : 0 < dot n d) :
    ¬ ∀ k : ℕ, g + (k : ℤ) • d ∈ U := by
  intro hray
  set K : ℕ := (C - dot n g).toNat + 1 with hK
  have hKz : (C - dot n g) < (K : ℤ) := by
    have h1 : (C - dot n g) ≤ ((C - dot n g).toNat : ℤ) := Int.self_le_toNat _
    have h2 : ((K : ℕ) : ℤ) = ((C - dot n g).toNat : ℤ) + 1 := by
      rw [hK]; push_cast; ring
    omega
  have hexp : dot n (g + (K : ℤ) • d) = dot n g + (K : ℤ) * dot n d := by
    simp only [dot, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  have hle := hbd _ (hray K)
  rw [hexp] at hle
  have h1 : (1 : ℤ) ≤ dot n d := by omega
  have hKnn : (0 : ℤ) ≤ (K : ℤ) := Int.natCast_nonneg K
  have h2 : (K : ℤ) * 1 ≤ (K : ℤ) * dot n d := mul_le_mul_of_nonneg_left h1 hKnn
  rw [mul_one] at h2
  linarith

/-- ⭐⭐ **`hgrow ⟹ rec_vJ`，代在 `ChainDataGeomParts` 上，与格无关。**

`hgrow` 逐字对应 `b3_colle2.txt:500` 的增长判据（`|Â_i ∩ w_i(J)| < |Â_{i+1} ∩ w_{i+1}(J)|`
对无穷多个 `i`）在**钉住起点**之后的形状：`∀ N, ∃ i, ∀ t ≤ N, g + t•vJ ∈ Âᵢ`
——量词对应是「对每个目标长度 `N`（原文的「任意大的截长」），存在一层 `i`（原文的
「无穷多个 `i`」里的一个），该层的 `J`-面从 `g` 起至少有 `N+1` 个格点（原文的
`|Â_i ∩ w_i(J)|`）」。起点 `g` 的钉住来自 `:488` 的 `g_1`／`k_i` 归一化。

结论是 `⋃ Âᵢ` 在 `+vJ` 方向递归闭，即 `ChainDataGeom` 的 `rec_vJ` 形。

⭐ **签名里没有 `p`、没有 `vJ1`、没有任何 `det p vJ1`** ⟹ 共线格（`det p vJ1 = 0`）
与横截格共用同一条，**不分格**；凸性由 `latticeConvex_of_parts` 免费，不是 binder。

⚠ 路线归属：`hgrow` → `ray_of_pinned_growth` → `rec_of_ray` 这条路
`blueprint/CORE-HOLES.md` 的 `(G-a)` 已写明，**不是本文件发现的**；本条的增量是
「代入 `ChainDataGeomParts`」＋「证明它不按格分叉」。
⚠ 本条**不**声称 `hgrow` 在链上可兑现：它的产者链（`LeafAJSelect` 的
`hgrow_of_pinned_ccw` 等）另有未结前提，其中 `hne : ∀ i, (Âᵢ).Nonempty` 按
`blueprint/CORE-HOLES.md` 常设纪律 #6 **不是链上现货**。
⚠ 与 `TowerHbase.rec_vJ_of_parts_unbounded_line`（lane-tower-hbase，吃「稀疏远点」
`hunb`）是**两条不同入口**，出口相同、前提不可比（本条不要凸性升级、那条不要钉住起点），
按 §110.2 两条都留，去重挂集成者。 -/
theorem rec_vJ_of_pinned_growth_parts {α : Type*} {η xper : Config α} {vl p gen : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)}
    (c : Nivat.ChainAsm.Aparts.ChainDataGeomParts η xper vl p S gen) {g : ℤ × ℤ}
    (hgrow : ∀ N : ℕ, ∃ i, ∀ t : ℕ, t ≤ N → g + (t : ℤ) • c.vJ ∈ hatOf c.A c.kk vl i) :
    ∀ z ∈ ⋃ i, hatOf c.A c.kk vl i, z + c.vJ ∈ ⋃ i, hatOf c.A c.kk vl i :=
  rec_of_ray (Nivat.LaneLeafAGenRecVJ.latticeConvex_of_parts c) (ray_of_pinned_growth hgrow)

/-- **§24 的反例集合里没有 `hgrow`**：`collinearStrip_lside = {z | z.1 ≤ 0 ∧ z.2 = 0}`
里不存在任何 `(0,1)`-射线（取 `n = (0,1)`、`C = 0` 代进 `no_ray_of_bounded_lside`）。

⟹ §24 的 `rec_vJ_not_from_linear_fields_collinear_lside` 与 `hgrow` **不冲突**：
那 18 条前提推不出 `rec_vJ`，而本条指出该见证集合恰好也不满足 `hgrow`。
⟹ 「线性字段族不够用」这句话的准确形状是「那张表里没有任何一条能让集合在 `+vJ` 上无界」。

⚠ lane-env-refute 另有内核见证 `collinearStrip_lside_not_itemII`（`nℓ` / `cz` 全称，
只要 `nℓ ≠ 0`）说明本集合在 `Colle35.ItemII` 之下**不可满足**——⟹ 该洞的定位是
`ChainDataGeomParts` 缺 `ItemII`（穷尽性），而结构里最近的 `envB` 是包络性，不是同一回事。
**他报，我未复跑**。 -/
theorem no_pinned_growth_collinearStrip_lside :
    ¬ ∃ g : ℤ × ℤ, ∀ k : ℕ,
      g + (k : ℤ) • ((0 : ℤ), (1 : ℤ)) ∈ collinearStrip_lside := by
  rintro ⟨g, hray⟩
  refine no_ray_of_bounded_lside (n := ((0 : ℤ), (1 : ℤ))) (C := 0) (g := g) ?_ ?_ hray
  · rintro z ⟨-, h2⟩
    show (0 : ℤ) * z.1 + (1 : ℤ) * z.2 ≤ 0
    omega
  · show (0 : ℤ) < (0 : ℤ) * 0 + (1 : ℤ) * 1
    norm_num

end Nivat.LaneLeafAShellLsideFork

#print axioms Nivat.LaneLeafAShellLsideFork.binetCauchy_lside
#print axioms Nivat.LaneLeafAShellLsideFork.dot_self_pos_lside
#print axioms Nivat.LaneLeafAShellLsideFork.det_p_vJ_ne_of_fields
#print axioms Nivat.LaneLeafAShellLsideFork.dot_nl_vJ_eq_zero_of_det_p_vJ_zero_lside
#print axioms Nivat.LaneLeafAShellLsideFork.nL_eq_zero_of_det_p_vJ_zero_lside
#print axioms Nivat.LaneLeafAShellLsideFork.not_primitive_zero_lside
#print axioms Nivat.LaneLeafAShellLsideFork.k_eq_zero_of_det_p_vJ_zero_lside
#print axioms Nivat.LaneLeafAShellLsideFork.Lside_all_at_det_p_vJ_zero
#print axioms Nivat.LaneLeafAShellLsideFork.iUnion_hatOf_subset_halfPlane_lside
#print axioms Nivat.LaneLeafAShellLsideFork.dot_nl_vJ_nonneg_of_recvJ_lside
#print axioms Nivat.LaneLeafAShellLsideFork.k_pos_of_recvJ_lside
#print axioms Nivat.LaneLeafAShellLsideFork.recvJ_of_dot_nl_vJ_nonneg_lside
#print axioms Nivat.LaneLeafAShellLsideFork.k_pos_iff_dot_nl_vJ_nonneg_lside
#print axioms Nivat.LaneLeafAShellLsideFork.det_p_vJ_pos_of_k_pos_lside
#print axioms Nivat.LaneLeafAShellLsideFork.k_pos_of_det_p_vJ_pos_lside
#print axioms Nivat.LaneLeafAShellLsideFork.k_pos_iff_det_p_vJ_pos_lside
#print axioms Nivat.LaneLeafAShellLsideFork.det_p_vJ_pos_of_chain_fields
#print axioms Nivat.LaneLeafAShellLsideFork.not_hattain_of_chain_fields
#print axioms Nivat.LaneLeafAShellLsideFork.rigLsideFork
#print axioms Nivat.LaneLeafAShellLsideFork.rigLsideDegenerate
#print axioms Nivat.LaneLeafAShellLsideFork.m_ne_zero_of_dot_vl_J
#print axioms Nivat.LaneLeafAShellLsideFork.dot_vl_J_neg_of_m_neg
#print axioms Nivat.LaneLeafAShellLsideFork.kJ_pos_of_det_p_vJ_pos_of_m_neg
#print axioms Nivat.LaneLeafAShellLsideFork.fork_refutation_needs_m_pos
#print axioms Nivat.LaneLeafAShellLsideFork.rigMsignNeg

#print axioms Nivat.LaneLeafAShellLsideFork.mpos_det_dir_dir
#print axioms Nivat.LaneLeafAShellLsideFork.mpos_dir_ne_zero
#print axioms Nivat.LaneLeafAShellLsideFork.mpos_dir_neg
#print axioms Nivat.LaneLeafAShellLsideFork.mpos_eq_one_of_smul_self
#print axioms Nivat.LaneLeafAShellLsideFork.mpos_smul_left_cancel
#print axioms Nivat.LaneLeafAShellLsideFork.not_collinear_of_arc
#print axioms Nivat.LaneLeafAShellLsideFork.not_collinear_of_det_ne
#print axioms Nivat.LaneLeafAShellLsideFork.m_eq_one_of_pred_eq
#print axioms Nivat.LaneLeafAShellLsideFork.m_eq_one_of_fan_pred
#print axioms Nivat.LaneLeafAShellLsideFork.m_pos_of_fan_pred
#print axioms Nivat.LaneLeafAShellLsideFork.m_pos_of_pred_or_det_ne
#print axioms Nivat.LaneLeafAShellLsideFork.m_eq_neg_one_of_ccw_instantiation
#print axioms Nivat.LaneLeafAShellLsideFork.m_eq_one_of_cw_instantiation
#print axioms Nivat.LaneLeafAShellLsideFork.m_eq_neg_one_or_one
#print axioms Nivat.LaneLeafAShellLsideFork.vl_eq_dir_of_neg_branch
#print axioms Nivat.LaneLeafAShellLsideFork.rigMposEq
#print axioms Nivat.LaneLeafAShellLsideFork.rigMposArc

#print axioms Nivat.LaneLeafAShellLsideFork.dot_nJ_vJ1_eq_mul
#print axioms Nivat.LaneLeafAShellLsideFork.m_pos_iff_dot_nJ_vl_neg
#print axioms Nivat.LaneLeafAShellLsideFork.dot_nJ_vl_pos_of_m_neg
#print axioms Nivat.LaneLeafAShellLsideFork.dot_nJ_vl_pos_of_ccw_instantiation

#print axioms Nivat.LaneLeafAShellLsideFork.mpos_dot_zsmul
#print axioms Nivat.LaneLeafAShellLsideFork.mpos_rec_iter
#print axioms Nivat.LaneLeafAShellLsideFork.dot_nonneg_of_rec
#print axioms Nivat.LaneLeafAShellLsideFork.dot_nJ_vl_neg_of_rec_p
#print axioms Nivat.LaneLeafAShellLsideFork.m_pos_of_chain_stock
#print axioms Nivat.LaneLeafAShellLsideFork.not_ccw_instantiation_of_chain_stock
#print axioms Nivat.LaneLeafAShellLsideFork.not_hattain_of_chain_fields_no_mpos

#print axioms Nivat.LaneLeafAShellLsideFork.mpos_dot_dir_eq_det
#print axioms Nivat.LaneLeafAShellLsideFork.paper_unit_iff_det_unit
#print axioms Nivat.LaneLeafAShellLsideFork.paper_admits_dot_nJ_vl_two
#print axioms Nivat.LaneLeafAShellLsideFork.paper_admits_dot_nJ_vl_arbitrary

#print axioms Nivat.LaneLeafAShellLsideFork.chain_fields_of_parts
#print axioms Nivat.LaneLeafAShellLsideFork.not_hattain_of_parts
#print axioms Nivat.LaneLeafAShellLsideFork.not_hattain_of_parts_at_window_bot
#print axioms Nivat.LaneLeafAShellLsideFork.sweptClosed_nsmul_lside
#print axioms Nivat.LaneLeafAShellLsideFork.not_primitive_two_smul_lside
#print axioms Nivat.LaneLeafAShellLsideFork.prim_vJ1_not_from_sweep_obligations
#print axioms Nivat.LaneLeafAShellLsideFork.not_iUnion_hatOf_eq_halfPlane_of_chain_stock
#print axioms Nivat.LaneLeafAShellLsideFork.hcomb_transverse_witness_lside
#print axioms Nivat.LaneLeafAShellLsideFork.residue_coverage_not_from_chain_stock_lside
#print axioms Nivat.LaneLeafAShellLsideFork.det_ne_zero_of_level_lside
#print axioms Nivat.LaneLeafAShellLsideFork.mem_of_cone_lside
#print axioms Nivat.LaneLeafAShellLsideFork.heights_covered_of_latticeConvex_lside
#print axioms Nivat.LaneLeafAShellLsideFork.residue_covered_of_latticeConvex_lside
#print axioms Nivat.LaneLeafAShellLsideFork.stock_witness_recvJ_not_latticeConvex_lside
#print axioms Nivat.LaneLeafAShellLsideFork.parts_stock_lside
#print axioms Nivat.LaneLeafAShellLsideFork.heights_covered_of_parts_lside
#print axioms Nivat.LaneLeafAShellLsideFork.residue_coverage_of_parts_lside
#print axioms Nivat.LaneLeafAShellLsideFork.reachSet_ray_at_level_lside
#print axioms Nivat.LaneLeafAShellLsideFork.bottom_first_two_of_stock_lside
#print axioms Nivat.LaneLeafAShellLsideFork.not_bottom_witness_no_rec_p_lside

#print axioms Nivat.LaneLeafAShellLsideFork.ahat_nonempty_of_halign_lside
#print axioms Nivat.LaneLeafAShellLsideFork.exists_parts_chain_half_ahat_nonempty_lside

#print axioms Nivat.LaneLeafAShellLsideFork.eq_add_zsmul_of_dot_eq_lside
#print axioms Nivat.LaneLeafAShellLsideFork.reachSet_recVJ_lside
#print axioms Nivat.LaneLeafAShellLsideFork.bottom_slice_eq_ray_of_conj24_lside
#print axioms Nivat.LaneLeafAShellLsideFork.bottom_conj124_of_recVJ_lside
#print axioms Nivat.LaneLeafAShellLsideFork.not_bottom_conj4_without_ray_bound_lside
#print axioms Nivat.LaneLeafAShellLsideFork.latticeConvex_snd_nonneg_lside
#print axioms Nivat.LaneLeafAShellLsideFork.dot_nL_eq_det_lside
#print axioms Nivat.LaneLeafAShellLsideFork.mem_reachSet_iff_nL_le_of_ray_lside
#print axioms Nivat.LaneLeafAShellLsideFork.bottom_conj3_same_level_lside
#print axioms Nivat.LaneLeafAShellLsideFork.W₀_eq_det_smul_dir_lside
#print axioms Nivat.LaneLeafAShellLsideFork.dot_vJ_W₀_lside
#print axioms Nivat.LaneLeafAShellLsideFork.det_nJ_vJ_mul_dot_lside
#print axioms Nivat.LaneLeafAShellLsideFork.det_vJ_W₀_lside
#print axioms Nivat.LaneLeafAShellLsideFork.W₀_eq_zero_iff_lside
#print axioms Nivat.LaneLeafAShellLsideFork.not_real_dir_of_collinear_lside
#print axioms Nivat.LaneLeafAShellLsideFork.not_W₀_pos_multiple_of_collinear_lside
#print axioms Nivat.LaneLeafAShellLsideFork.W₀_pos_multiple_iff_detsign_lside
#print axioms Nivat.LaneLeafAShellLsideFork.nonneg_of_linear_bounded_lside
#print axioms Nivat.LaneLeafAShellLsideFork.detsign_of_fields_lside
#print axioms Nivat.LaneLeafAShellLsideFork.bottom_conj124_of_fields_lside
#print axioms Nivat.LaneLeafAShellLsideFork.W₀_pos_multiple_of_fields_transverse_lside
#print axioms Nivat.LaneLeafAShellLsideFork.collinearStrip_lside
#print axioms Nivat.LaneLeafAShellLsideFork.collinearStrip_convex_lside
#print axioms Nivat.LaneLeafAShellLsideFork.collinearStrip_chain_lside
#print axioms Nivat.LaneLeafAShellLsideFork.rec_vJ_not_from_linear_fields_collinear_lside
#print axioms Nivat.LaneLeafAShellLsideFork.fiber_fill_collinear_lside
#print axioms Nivat.LaneLeafAShellLsideFork.fiber_fill_of_det_collinear_lside
#print axioms Nivat.LaneLeafAShellLsideFork.rec_vJ_of_level_witness_collinear_lside
#print axioms Nivat.LaneLeafAShellLsideFork.no_ray_of_bounded_lside
#print axioms Nivat.LaneLeafAShellLsideFork.rec_vJ_of_pinned_growth_parts
#print axioms Nivat.LaneLeafAShellLsideFork.no_pinned_growth_collinearStrip_lside
