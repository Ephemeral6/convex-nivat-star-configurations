/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.ShellSubStrip
import Nivat.External.Colle.AhatHeight

/-!
# `shellSubStrip` 的横向情形，归约到一条只关于 `B i` 的 `(b, s, t)` 义务

集成者，2026-09-23（第 145 轮）。本文件替换掉
`ShellSubStrip.shellSubStrip_of_bounded_check`（`ShellSubStrip.lean:312`）那条归约：
它的 `hcheck` binder 已被 `HcheckRefute.hcheck_false`（`HcheckRefute.lean`，内核见证）证伪。

## 为什么旧归约漏了

`hcheck` 只留下 `sweep_param_le`（`LaneCdSubstrip.sweep_param_le`，`ShellSubStrip.lean:167`）
给出的标量界 `(t:ℤ) ≤ dot nℓ g - cz`——这个界**随 `i` 增长**——而把
`MaxEnv.shell` 的 level 条件 `cJ - ε ≤ dot nJ z` 整个丢了。
关键在于 level 条件在 `nJ` 方向上同时压住**两个**步数：`ofPartsExhaustsInter` 的 binder 里
`dot nJ vl < 0`（由 `LeafAJSelect.exists_J_stable`（`LeafAJSelect.lean:209`）/
`exists_J_stable_cw`（`:281`）的 tag 定死，见 `tmp/wip/lane-substrip-sign.lean`）与
`hsweepW : dot nJ w < 0`（`ChainExhaustInter.lean`）都是负的，于是

  `s·(−⟪n_J, v⃗_ℓ⟫) + t·(−⟪n_J, w⟫) ≤ ⟪n_J, b⟫ − c_J + ε`

把半带步数 `s` **和** 横移步数 `t` 一起卡在 `b ∈ B i` 自己在 `c_J` 之上的高度里。
旧的 `hcheck` 一条也没保留。

## 本文件给什么

* `step_sum_le_of_shell` — 上面那条双重界，直接从 `MaxEnv.shell` 的 level 条件来。
* `step_sum_le_of_shell_one` — 整数版：`dot nJ vl ≤ -1`、`dot nJ w ≤ -1` 时 `s + t` 被同一个量卡住。
* `shellSubStrip_of_base_shell` — 归约本体：把 `shellSubStrip` 的横向情形换成一条
  **只关于 `B i`** 的义务 `hbase`，量词跑 `b ∈ B i` 与 `s t : ℕ`，前提是上面那条双重界
  （带 `kk i` 的平移修正）。
* `base_shell_false_of_singleton` — 内核见证：`hbase` 单靠 `hsub` / `hhp` / 两个符号条件
  **证不出来**，必须用上 `B` 族自身的结构（`ItemII` / `Exhausts` / `envB`）。
  这条是给下游 lane 的路标，不是否证。

对原文 `scratch/b3_colle2.txt:520`
（"Furthermore, one has `B_i − k_i v⃗_ℓ ⊂ Â_i^{(ε)} ⊂ H_{B_i}(ℓ) − k_i v⃗_ℓ`"，原文**无证明**）。
本文件不断言那条包含，只把它的横向情形降成上面那条义务。

## 一名多物（`blueprint/NOTATION.md`）

`halfStrip` 有两个同体常量：`Colle35.halfStrip`（`Lemma35.lean:404`）与
`LE2.halfStrip`（`LatticeEdges.lean:1810`）。消费者 `ofPartsExhaustsInter` 在
`namespace Nivat.Colle35` 里，本文件一律写全名 `Nivat.Colle35.halfStrip`。
-/

set_option autoImplicit false

namespace Nivat.ShellBaseReduce

open Nivat Nivat.LE2 Nivat.MaxEnv

/-! ### §1. level 条件同时卡住两个步数 -/

/-- **双重步数界。**若 `b + s·v⃗_ℓ + t·w` 落在 `Â_∞` 的 `ε`-shell 里，则 shell 的 level 条件
`c_J − ε ≤ ⟪n_J, ·⟫` 立刻给

  `s·(−⟪n_J, v⃗_ℓ⟫) + t·(−⟪n_J, w⟫) ≤ ⟪n_J, b⟫ − c_J + ε`。

`shell` 的 `reachSet` 那一半在这里不用；用的只有 level 条件。
这是 `AhatHeight.mul_le_of_shell_mem`（`AhatHeight.lean:113`）的两步数版本：那条只卡 `t`，
这条把半带步数 `s` 一起卡住，而 `s` 正是旧 `hcheck` 完全看不见的量。 -/
theorem step_sum_le_of_shell {Ainf : Set (ℤ × ℤ)} {vl w vJ1 nJ : ℤ × ℤ} {cJ : ℤ} {ε : ℕ}
    {b : ℤ × ℤ} {s t : ℕ}
    (hz : b + (s : ℤ) • vl + (t : ℤ) • w ∈ shell Ainf vJ1 nJ cJ ε) :
    (s : ℤ) * (- dot nJ vl) + (t : ℤ) * (- dot nJ w) ≤ dot nJ b - cJ + (ε : ℤ) := by
  obtain ⟨-, -, -, -, hlev⟩ := hz
  rw [dot_add, dot_add, Nivat.AhatHeight.dot_smul_right,
    Nivat.AhatHeight.dot_smul_right] at hlev
  linarith

/-- **整数版**：两个方向都至少下降 1 格时，`s + t` 被 `b` 的高度卡住。
`dot nJ vl ≤ -1` 与 `dot nJ w ≤ -1` 在实际调用点由 `dot nJ vl < 0`（`lane-substrip-sign`）
与 `hsweepW`（`ChainExhaustInter.lean`）给出——整数上 `< 0` 就是 `≤ -1`。 -/
theorem step_sum_le_of_shell_one {Ainf : Set (ℤ × ℤ)} {vl w vJ1 nJ : ℤ × ℤ} {cJ : ℤ} {ε : ℕ}
    {b : ℤ × ℤ} {s t : ℕ}
    (hvl : dot nJ vl ≤ -1) (hw : dot nJ w ≤ -1)
    (hz : b + (s : ℤ) • vl + (t : ℤ) • w ∈ shell Ainf vJ1 nJ cJ ε) :
    (s : ℤ) + (t : ℤ) ≤ dot nJ b - cJ + (ε : ℤ) := by
  have h := step_sum_le_of_shell (vJ1 := vJ1) hz
  have hs0 : (0 : ℤ) ≤ (s : ℤ) := Int.natCast_nonneg s
  have ht0 : (0 : ℤ) ≤ (t : ℤ) := Int.natCast_nonneg t
  have h1 : (s : ℤ) * 1 ≤ (s : ℤ) * (- dot nJ vl) :=
    mul_le_mul_of_nonneg_left (by linarith) hs0
  have h2 : (t : ℤ) * 1 ≤ (t : ℤ) * (- dot nJ w) :=
    mul_le_mul_of_nonneg_left (by linarith) ht0
  linarith

/-! ### §2. 归约本体 -/

/-- **`shellSubStrip` 的横向情形，归约到一条只关于 `B i` 的义务。**

对比 `shellSubStrip_of_bounded_check`（`ShellSubStrip.lean:312`）：那条的 `hcheck` 量词跑
`g ∈ hatOf A kk vl i`（半带上任意高的点），前提只有标量界，已被 `HcheckRefute.hcheck_false`
证伪。这里的 `hbase` 量词只跑 `b ∈ B i` 与两个步数 `s t : ℕ`，前提是 §1 的双重界，
带上 `kk i` 的平移修正——`hs : g + k_i v⃗_ℓ = b + s v⃗_ℓ` 把 `g` 换成 `b` 时，
level 条件说的是 `g + t·w` 而不是 `b + s·v⃗_ℓ + t·w`，两者差 `k_i v⃗_ℓ`，
所以 `s` 出现的形式是 `(s : ℤ) - (k_i : ℤ)`（可以为负，这是对的：`k_i` 大时
`b + s v⃗_ℓ + t w` 比 `g + t w` 在 `n_J` 方向更低，义务反而更松）。

`hsub` 就是顶层的 `subStrip`（`A i ⊆ H_{B_i}(ℓ)`），`t = 0` 那支直接由它给出，
shell 在那里根本用不上。 -/
theorem shellSubStrip_of_base_shell {A B : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ}
    {Ainf : Set (ℤ × ℤ)} {vl w vJ1 nJ : ℤ × ℤ} {cJ : ℤ}
    (hsub : ∀ i, A i ⊆ Nivat.Colle35.halfStrip (B i) vl)
    (hbase : ∀ i ε : ℕ, ∀ b ∈ B i, ∀ s t : ℕ, 1 ≤ t →
      ((s : ℤ) - (kk i : ℤ)) * (- dot nJ vl) + (t : ℤ) * (- dot nJ w)
        ≤ dot nJ b - cJ + (ε : ℤ) →
      b + (s : ℤ) • vl + (t : ℤ) • w ∈ Nivat.Colle35.halfStrip (B i) vl) :
    ∀ i ε : ℕ, ShellMink.shellInter (Nivat.Colle35.hatOf A kk vl i)
        (shell Ainf vJ1 nJ cJ ε) w ⊆
      {z | z + (kk i : ℤ) • vl ∈ Nivat.Colle35.halfStrip (B i) vl} := by
  rintro i ε z ⟨⟨g, hg, t, rfl⟩, hshell⟩
  have hgA : g + (kk i : ℤ) • vl ∈ A i := hg
  obtain ⟨b, hb, s, hs⟩ := hsub i hgA
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · exact ⟨b, hb, s, by simpa using hs⟩
  · have hz : g + (t : ℤ) • w + (kk i : ℤ) • vl = b + (s : ℤ) • vl + (t : ℤ) • w := by
      rw [← hs]; abel
    show g + (t : ℤ) • w + (kk i : ℤ) • vl ∈ Nivat.Colle35.halfStrip (B i) vl
    rw [hz]
    refine hbase i ε b hb s t ht ?_
    obtain ⟨-, -, -, -, hlev⟩ := hshell
    have hdg : dot nJ g + (kk i : ℤ) * dot nJ vl = dot nJ b + (s : ℤ) * dot nJ vl := by
      have h := congrArg (dot nJ) hs
      rwa [dot_add, dot_add, Nivat.AhatHeight.dot_smul_right,
        Nivat.AhatHeight.dot_smul_right] at h
    rw [dot_add, Nivat.AhatHeight.dot_smul_right] at hlev
    linarith

/-! ### §3. 路标：`hbase` 不可能只从符号条件 + `hsub` + `hhp` 证出来 -/

/-- **内核见证：`hbase` 的形状需要 `B` 族自身的结构。**

取 `nℓ = (0,1)`，`vl = (1,0)`，`nJ = (-1,1)`，`w = (0,-1)`，`cJ = 0`，`kk = 0`，
`A i = B i = {(0,1)}`（常值单点族）。逐条核：

* `dot nJ vl = -1 < 0`（`lane-substrip-sign` 定死的符号）；
* `dot nJ w = -1 < 0`（`hsweepW`，`ChainExhaustInter.lean`）；
* `dot nℓ vl = 0`（`hperp`，`ChainExhaustInter.lean`）；
* `dot nℓ w = -1 < 0`（横向分支，`ShellSubStrip.lean:136`）；
* `hhp`：`dot nJ (0,1) = 1 ≥ 0 = cJ` ✓——注意这正是 `HcheckRefute.lean` 的 `Bbox` 实例**做不到**的那条；
* `hsub`：`A i = B i`，取 `t = 0` ✓。

喂 `i` 任意、`ε = 0`、`b = (0,1)`、`s = 0`、`t = 1`：双重界是 `0·1 + 1·1 = 1 ≤ 1 - 0 + 0` ✓，
结论要 `(0,0) ∈ halfStrip {(0,1)} (1,0)`，而 `+ℕ•(1,0)` 不动第二坐标。

**结论**：剩下的内容全在 `B` 族本身——`ItemII`（`ItemII.lean:80`）、
`Exhausts`（`:96`）、`envB : ∀ i, Env (B i)`（`EnvOf`，`LatticeEdges.lean:2433`）。
常值单点族把前三条符号条件和 `hhp` 全部满足，却连 `Exhausts` 都不满足（它连
`⋃ i, B i = halfPlaneGE nℓ cz` 都够不着）。下游 lane 必须用上这三条中的至少一条，
只在符号上做文章是走不通的。 -/
theorem base_shell_false_of_singleton
    (hbase : ∀ b ∈ ({((0 : ℤ), (1 : ℤ))} : Set (ℤ × ℤ)), ∀ s t : ℕ, 1 ≤ t →
      ((s : ℤ) - (0 : ℤ)) * (- dot ((-1 : ℤ), (1 : ℤ)) ((1 : ℤ), (0 : ℤ)))
          + (t : ℤ) * (- dot ((-1 : ℤ), (1 : ℤ)) ((0 : ℤ), (-1 : ℤ)))
        ≤ dot ((-1 : ℤ), (1 : ℤ)) b - 0 + ((0 : ℕ) : ℤ) →
      b + (s : ℤ) • ((1 : ℤ), (0 : ℤ)) + (t : ℤ) • ((0 : ℤ), (-1 : ℤ)) ∈
        Nivat.Colle35.halfStrip ({((0 : ℤ), (1 : ℤ))} : Set (ℤ × ℤ)) ((1 : ℤ), (0 : ℤ))) :
    False := by
  have h := hbase ((0 : ℤ), (1 : ℤ)) rfl 0 1 (le_refl 1) (by norm_num [dot])
  have heq : ((0 : ℤ), (1 : ℤ)) + ((0 : ℕ) : ℤ) • (((1 : ℤ), (0 : ℤ)) : ℤ × ℤ)
      + ((1 : ℕ) : ℤ) • (((0 : ℤ), (-1 : ℤ)) : ℤ × ℤ) = ((0 : ℤ), (0 : ℤ)) := by
    ext <;> simp
  rw [heq] at h
  obtain ⟨c, hc, s, hs⟩ := h
  have hc1 : c = ((0 : ℤ), (1 : ℤ)) := hc
  subst hc1
  have hsnd := congrArg Prod.snd hs
  simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, mul_zero, add_zero] at hsnd
  omega

end Nivat.ShellBaseReduce

/-! ### §4. 另一条归约：保留 shell 的位移见证 `g₂ / t₂`

`shellSubStrip_of_base_shell`（§2）只用了 `MaxEnv.shell` 的 level 条件，把
`reachSet` 那一半（`ShellMink.shellInter A Ainf w = reachSet A w ∩ Ainf`，`ShellMink.lean:508`；
`MaxEnv.mem_shell`，`MaximalEnveloped.lean:567`）丢了。下面这条把那一半也原样交出去：
`z = g₂ + t₂·v_{ℓ_{J−1}}`、`g₂ ∈ Â_∞`。两条归约互补，下游 lane 按需要挑。

由 lane-substrip-base 交（`tmp/wip/lane-substrip-base.lean`），集成者复核
`check1.sh` EXIT=0、公理干净后搬进主仓；原文件的 `halfStrip_step_le_of_band` 已被
§1 的 `step_sum_le_of_shell` 覆盖（那条只卡 `s`，这条 `s`、`t` 一起卡），不重复落地。 -/

namespace Nivat.ShellBaseReduce

open Nivat Nivat.LE2 Nivat.MaxEnv Nivat.LaneCdSubstrip

/-- **`shellSubStrip` 的横向情形，归约到保留 shell 位移见证的检查。**

binder `hlev` / `hvJ1` / `hw` / `hsub` 与 `shellSubStrip_of_bounded_check`
（`ShellSubStrip.lean:312`）完全一样（它们正是 `sweep_param_le`（`:167`）要的），
但 `hcheck` 换成 `hcheck'`：除标量界外还收下 `g₂ ∈ Ainf`、`t₂ : ℕ`、
`g + t·w = g₂ + t₂·vJ1` 与 `cJ - ε ≤ dot nJ (g + t·w)`，逐字不作概括。

标量界留着不是多余：`sweep_param_le` 正是从 `hlev`/`hvJ1`/`hw` 推出它的，去掉只会让
`hcheck'` 更难交。 -/
theorem shellSubStrip_of_shell_check {A B : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ}
    {Ainf : Set (ℤ × ℤ)} {vl w nℓ vJ1 nJ : ℤ × ℤ} {cz cJ : ℤ}
    (hlev : ∀ z ∈ Ainf, cz ≤ dot nℓ z) (hvJ1 : 0 ≤ dot nℓ vJ1) (hw : dot nℓ w < 0)
    (hsub : ∀ i, A i ⊆ Nivat.Colle35.halfStrip (B i) vl)
    (hcheck' : ∀ i ε : ℕ, ∀ g ∈ Nivat.Colle35.hatOf A kk vl i, ∀ t : ℕ, 1 ≤ t →
      (t : ℤ) ≤ dot nℓ g - cz →
      ∀ g₂ ∈ Ainf, ∀ t₂ : ℕ,
      g + (t : ℤ) • w = g₂ + (t₂ : ℤ) • vJ1 →
      cJ - (ε : ℤ) ≤ dot nJ (g + (t : ℤ) • w) →
      g + (t : ℤ) • w + (kk i : ℤ) • vl ∈ Nivat.Colle35.halfStrip (B i) vl) :
    ∀ i ε : ℕ, ShellMink.shellInter (Nivat.Colle35.hatOf A kk vl i)
        (shell Ainf vJ1 nJ cJ ε) w ⊆
      {z | z + (kk i : ℤ) • vl ∈ Nivat.Colle35.halfStrip (B i) vl} := by
  rintro i ε z ⟨⟨g, hg, t, rfl⟩, hshell⟩
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · have hgA : g + (kk i : ℤ) • vl ∈ A i := hg
    obtain ⟨b, hb, s, hs⟩ := hsub i hgA
    exact ⟨b, hb, s, by simpa using hs⟩
  · have hbound := sweep_param_le hlev hvJ1 hw hshell
    obtain ⟨g₂, hg₂, t₂, heq, hshlev⟩ := hshell
    exact hcheck' i ε g hg t ht hbound g₂ hg₂ t₂ heq hshlev

end Nivat.ShellBaseReduce

#print axioms Nivat.ShellBaseReduce.step_sum_le_of_shell
#print axioms Nivat.ShellBaseReduce.step_sum_le_of_shell_one
#print axioms Nivat.ShellBaseReduce.shellSubStrip_of_base_shell
#print axioms Nivat.ShellBaseReduce.base_shell_false_of_singleton
#print axioms Nivat.ShellBaseReduce.shellSubStrip_of_shell_check
