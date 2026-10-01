/-
Copyright (c) 2026. Released under Apache 2.0 license.
Authors: integrator
-/
import Nivat.External.Colle.ShellSubStrip

/-!
# Wiring `exists_w_hsweepW` into the `shellSubStrip` dichotomy

集成者，2026-09-24（第 181 轮）。**这是 `LeafAShellNNext.exists_w_hsweepW`
（`LeafAShellNNext.lean:70`）在主仓的第一个项级消费者。**

## 为什么需要这个文件

`exists_w_hsweepW` 的 docstring 自己写着它是**有意的 orphan**：

> 真正缺的是接线，接线点是 `tmp/wip/LeafAAssemble.lean`，归集成者；在那之前本条保持
> orphan 状态是预期的。

而 `ChainDataGeom.ofPartsExhaustsInter`（`ChainExhaustInter.lean`）对 `w` 的唯一约束是
`hsweepW : dot nJ w < 0`，**仅凭符号 `shellEnv` 为假**（`LaneEnvShellEnvRefute.not_shellEnv`，
`w = (-1,-1)`；换成扇后继 `w = (-1,0)` 则为真）。缺口就是 `exists_w_hsweepW` 结论里被下游
丢掉的那两项：`Arc J νJ1 = ∅`（扇形相邻）与 `w = -(dir νJ1)`（把相邻性钉到 `w` 上）。

裁决（第 162 轮）是**不往 `ofPartsExhaustsInter` 的 binder 表里加这几条**——`shellEnv` /
`shellSubStrip` / `fillCover` 都是调用方供给的 binder，加进去等于加一组没有消费者的 binder
（纯债，硬规矩 5）。⟹ 正确的接法是在**调用方一侧**把这两项**用掉**，这就是本文件。

## 接的是哪一段

`ShellSubStrip.lean` 的 §1 把这个二分法**写在 docstring 里**，并把两支各自的引擎都备齐了，
但**从来没有把 `hor` 真正消掉**——`w_eq_vl_or_dot_nl_w_neg`（`ShellSubStrip.lean:136`）
把 `νJ1 = nℓ ∨ νJ1 ∈ Arc J nℓ` 当**假设**收，而这条假设的**唯一生产者**正是
`exists_w_hsweepW`（在它自己的 `ℓ`-槽上取 `ℓ := -nℓ`，于是它的 `-ℓ` 就是 `nℓ`）。

本文件做两件事，都是把假设换成产出：

* `§1 exists_w_fan_dichotomy`：调用 `exists_w_hsweepW`，**消掉 `hor`**，直接交出
  `w = vl ∨ dot nℓ w < 0`。
* `§2 fan_w_shellSubStrip_or_finite`：把 §1 的两支各自接到已有引擎上——
  平行支接 `shellSubStrip_of_w_eq_vl_of_max`（`ShellSubStrip.lean:299`），
  横截支接 `shellInter_finite_of_level`（`:245`）——交出
  「`shellSubStrip` 当场成立 **或** `:518` 的壳有限」。

⚠ **本文件不主张 `shellEnv`。** 有限性不等于 `Env`；`shellEnv` 还要 `Env` 这个谓词本身的
性质（`envShift` / `envB` / `maxA`）。这里只兑现「横截支的壳是有限集」这一条，那是
`shellInter_finite_of_level` 的原话，不多不少。`LaneCdM4.shellEnv_false_at_m_four`
（`ShellSubStrip.lean:2561`）表明 `shellEnv` 在某些 `m = 4` 台架上为假，所以**不许**把本文件
读成「`shellEnv` 已解决」。

⚠ **`hvJ1 : 0 ≤ dot nℓ vJ1` 取作假设，不是本文件产的。** 它的生产者是
`LaneCdSubstrip.dot_nl_vJ1_nonneg`（`ShellSubStrip.lean:120`），输入是
`LeafAJSelect.exists_nprevJ_vJ1` 的 `hor`。接那一条是另一件事，不在本轮范围。

⚠ **§41 空真关：只过了一半，如实记。** `hnℓE` / `hJE` / `hℓJ` / `hdir_vl` 这一组在
`ShellSubStrip.lean` §6 的手算实例（六边形 `Sphi`，`nℓ = (0,1)`，`cz = 0`）上已兑现，
那是 §1 的输入。但 §2 额外要的 `maxA` / `hfin` / `hlev` / `hvJ1` 我**没有**在同一个实例上
逐条兑现。⟹ §2 的结论按「组合已落地引理」采信，**不按「在具体见证上验过」采信**；
谁要拿它当反例的挡箭牌，先把这四条在同一实例上做出来。

原文对应：`b3_colle2.txt:518` 的 `w := −v⃗_{ℓ_{J+1}}`（`NOTATION.md:213`「`J` 另一侧的扇邻
居」），`nJ = -J`（`NOTATION.md:175,208`），`:520` 的壳 `Â_i^{(ε)}`。
-/

set_option autoImplicit false

namespace Nivat.WFanWiring

open Nivat Nivat.LE2 Nivat.MaxEnv Nivat.PolyChainSum
open Nivat.LeafAShellNNext Nivat.LaneCdSubstrip

/-! ## §1  消掉 `hor`：扇后继直接给出 `w = vl ∨ dot nℓ w < 0` -/

/-- **`exists_w_hsweepW` 的第一个项级消费者。**  在它自己的 `ℓ`-槽上取 `ℓ := -nℓ`（于是它的
`-ℓ` 就是 `nℓ`），把产出的
`νJ1 = nℓ ∨ νJ1 ∈ Arc J nℓ` 喂给 `LaneCdSubstrip.w_eq_vl_or_dot_nl_w_neg`
（`ShellSubStrip.lean:136`），**该假设当场消掉**，换来 `w = vl ∨ dot nℓ w < 0`。

`hdir_vl : dir (-nℓ) = vl` 是链上 `vl` 与 `nℓ` 的字典（归一化后 `vl = dir nℓ`，
见 `OrientationFree.lean` 与 `RegionSteps.lean` 的 `hdetpos` 段）；这里只当假设收，
本文件不主张它的生产者。

⚠ 保留输出的 `Arc J νJ1 = ∅`：它是扇形相邻性本身，下游（`shellEnv`）还要用，
不许在这里丢掉。 -/
theorem exists_w_fan_dichotomy {Sphi : Finset (ℤ × ℤ)} {nℓ J vl : ℤ × ℤ}
    (hdir_vl : dir (-nℓ) = vl)
    (hnℓE : nℓ ∈ E (↑Sphi : Set (ℤ × ℤ))) (hJE : J ∈ E (↑Sphi : Set (ℤ × ℤ)))
    (hℓJ : 0 < det (-nℓ) J) :
    ∃ νJ1 w : ℤ × ℤ,
      νJ1 ∈ E (↑Sphi : Set (ℤ × ℤ)) ∧ 0 < det J νJ1 ∧
      Arc (Sphi.finite_toSet) J νJ1 = ∅ ∧
      w = -(dir νJ1) ∧ dot (-J) w < 0 ∧ (w = vl ∨ dot nℓ w < 0) := by
  obtain ⟨νJ1, w, hE, hpos, hempty, hor, hw, hsweepW⟩ :=
    exists_w_hsweepW (Sphi := Sphi) (ℓ := -nℓ) (J := J) (by rwa [neg_neg]) hJE hℓJ
  refine ⟨νJ1, w, hE, hpos, hempty, hw, hsweepW, ?_⟩
  have hor' : νJ1 = nℓ ∨ νJ1 ∈ Arc (Sphi.finite_toSet) J nℓ := by
    rwa [neg_neg] at hor
  have hdich := w_eq_vl_or_dot_nl_w_neg (Sphi := Sphi) (nℓ := nℓ) (J := J) hor'
  rcases hdich with h | h
  · exact Or.inl (by rw [hw, h, hdir_vl])
  · exact Or.inr (by rw [hw]; exact h)

/-! ## §2  两支各自接到已有引擎上 -/

/-- **接线的成品。**  扇后继产出的 `w` 使得，对**每一个** `i`：

* 要么 `shellSubStrip` 当场成立，且对**任意**环境壳 `Ainf'`、任意 `i` 都成立
  （平行支 `w = vl`，引擎 `LaneCdSubstrip.shellSubStrip_of_w_eq_vl_of_max`，
  `ShellSubStrip.lean:299`，只用 `maxA` 给的 `subStrip`，与环境壳无关）；
* 要么 `:518` 的壳 `shellInter Âᵢ (shell Â_∞ vJ1 nJ cJ ε) w` 对每个 `ε, i` 都是**有限集**
  （横截支 `dot nℓ w < 0`，引擎 `LaneCdSubstrip.shellInter_finite_of_level`，
  `ShellSubStrip.lean:245`，机制是 `t ≤ dot nℓ g - cz` 把 sweep 参数卡死）。

⟹ `ShellSubStrip.lean` §0 记录的那条反驳
（`not_shellSubStrip_of_transverse_sweep`：`det vl ·` 在 `halfStrip` 上有界，沿 sweep 线性
增长，无界的 `t` 总能逃出条带）在这个 `w` 上**两支都打不中**：平行支根本不动壳，横截支的
`t` 有上界。这正是 §0 那句「the unbounded-`t` mechanism is gone」，现在是内核事实而非散文。

⚠ **不主张 `shellEnv`、不主张 `escapeW`、不主张 `fillCover`。** 见文件头的两条 ⚠。 -/
theorem fan_w_shellSubStrip_or_finite {α : Type*} {η xper : Config α}
    {Env : Set (ℤ × ℤ) → Prop} {A B : ℕ → Set (ℤ × ℤ)} {u : ℕ → ℤ × ℤ} {kk : ℕ → ℕ}
    {Sphi : Finset (ℤ × ℤ)} {nℓ J vl vJ1 nJ : ℤ × ℤ} {Ainf : Set (ℤ × ℤ)} {cz cJ : ℤ}
    (hdir_vl : dir (-nℓ) = vl)
    (hnℓE : nℓ ∈ E (↑Sphi : Set (ℤ × ℤ))) (hJE : J ∈ E (↑Sphi : Set (ℤ × ℤ)))
    (hℓJ : 0 < det (-nℓ) J)
    (maxA : ∀ i, Nivat.Colle35.IsMaxEnvIn Env (Nivat.Colle35.canonA η xper vl B u i) (A i))
    (hfin : ∀ i, (Nivat.Colle35.hatOf A kk vl i).Finite)
    (hlev : ∀ z ∈ Ainf, cz ≤ dot nℓ z)
    (hvJ1 : 0 ≤ dot nℓ vJ1) :
    ∃ νJ1 w : ℤ × ℤ,
      νJ1 ∈ E (↑Sphi : Set (ℤ × ℤ)) ∧ 0 < det J νJ1 ∧
      Arc (Sphi.finite_toSet) J νJ1 = ∅ ∧
      w = -(dir νJ1) ∧ dot (-J) w < 0 ∧
      ((∀ (Ainf' : Set (ℤ × ℤ)) (i : ℕ),
          ShellMink.shellInter (Nivat.Colle35.hatOf A kk vl i) Ainf' w ⊆
            {z | z + (kk i : ℤ) • vl ∈ Nivat.Colle35.halfStrip (B i) vl})
       ∨ (∀ ε i : ℕ,
          (ShellMink.shellInter (Nivat.Colle35.hatOf A kk vl i)
            (MaxEnv.shell Ainf vJ1 nJ cJ ε) w).Finite)) := by
  obtain ⟨νJ1, w, hE, hpos, hempty, hw, hsweepW, hdich⟩ :=
    exists_w_fan_dichotomy hdir_vl hnℓE hJE hℓJ
  refine ⟨νJ1, w, hE, hpos, hempty, hw, hsweepW, ?_⟩
  rcases hdich with hwvl | hwneg
  · exact Or.inl fun Ainf' i => shellSubStrip_of_w_eq_vl_of_max hwvl maxA Ainf' i
  · exact Or.inr fun ε i => shellInter_finite_of_level (hfin i) hlev hvJ1 hwneg

end Nivat.WFanWiring

#print axioms Nivat.WFanWiring.exists_w_fan_dichotomy
#print axioms Nivat.WFanWiring.fan_w_shellSubStrip_or_finite
