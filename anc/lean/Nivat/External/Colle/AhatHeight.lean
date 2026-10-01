/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.ChainExhaustInter

/-!
# The `n_J`-height of `Â_i` is attained on `B_i − k_i v⃗_ℓ`, and the drift bound it yields

集成者, 2026-09-23 (第 143 轮).  This file supplies the quantitative half of Collé's

> Furthermore, one has `B_i − k_i v⃗_ℓ ⊂ Â_i^{(ε)} ⊂ H_{B_i}(ℓ) − k_i v⃗_ℓ`
> (`scratch/b3_colle2.txt:520`)

i.e. the `shellSubStrip` binder of `ChainDataGeom.ofPartsExhaustsInter`
(`ChainExhaustInter.lean`, **按字段名找** — the line range this sentence used to carry,
`:54-57`, had already rotted onto the `escapeW` prose block; caught by lane-tower-hbase
2026-09-24, PROTOCOL §85).  Collé asserts that containment without proof
("Furthermore, one has …"), so there is nothing to transcribe; what is landed here is the
bound that decides whether it *can* hold.

⚠ **2026-09-25 核对（lane-tower-hlev）**：`ChainDataGeomParts`（`ChainPartsFeed.lean`）
的同名字段 `shellSubStrip` 随 (B) 栈迁移，已重述在 `ShellMink.shellInter Âi (shell Â∞ …) w`
上，守卫锚在 `max i₀ I₀`（`I₀` 在那里是**字段**，不是输入 binder）。本文件的 `shellInter … w`
读法与之**一致**，无需改形；下文所有 `shellInter Âi (shell Â∞ v_{J−1} n_J c_J ε) w`
同时服务这两处同名义务。⚠ 与之相对，`ShellMink.not_shellSubStrip_of_transverse_sweep`
否掉的是**单扫**形（`MaxEnv.shell`，`b3_colle2.txt:440`），不是本文件这个取交形
（`:518`）——两者不是同一个命题。

## The question this answers

Write `Âi := hatOf A kk vl i`, `Â∞ := ⋃ j, hatOf A kk vl j`, and `h(g) := ⟪n_J, g⟫ − c_J ≥ 0`
(non-negative by `hhp`).  A point of `shellInter Âi (shell Â∞ v_{J−1} n_J c_J ε) w` is
`g + t·w` with `g ∈ Âi`, and `hsweepW : ⟪n_J, w⟫ < 0` together with the shell's level
constraint `c_J − ε ≤ ⟪n_J, g + t·w⟫` bounds `t` by `(h(g) + ε)/|⟪n_J, w⟫|`.  The displacement
`t·w` moves the point transversally to `v⃗_ℓ` by `t·⟪n_ℓ, w⟫`, and
`halfStrip (B i) vl = B i + ℕ·v⃗_ℓ` is bounded in exactly that direction.  So the containment
can hold only if `sup_{g ∈ Âi} h(g)` is comparable to `B i`'s transverse extent — and the
danger is that `Âi` reaches far up the half strip, where `h(g)` is large and nothing about
`B i` controls it.  `Enveloped` does not rule that out on its own: `Enveloped U T`
(`LatticeEdges.lean:628`) bounds each face's `encard` from **below** only, so an enveloped set
may be arbitrarily long in any of its edge directions.

`dot_le_of_mem_hatOf` below settles it: when `⟪n_J, v⃗_ℓ⟫ ≤ 0`, climbing the half strip
*lowers* the `n_J`-level, so the supremum is attained already on the base `B i − k_i v⃗_ℓ` and
is independent of how far `A i` extends along `v⃗_ℓ`.  The sign hypothesis is not an extra
assumption at the call site: `⟪n_J, v⃗_ℓ⟫ < 0` is forced there, in both branches, by the very
tag that selects `J` — `LeafAJSelect.exists_J_stable` (`LeafAJSelect.lean:209`) emits
`0 < det (−n_ℓ) J` and `exists_J_stable_cw` (`:281`) emits `0 < det J (−n_ℓ)`, and with
`dir (−n_ℓ) = ±v⃗_ℓ` either tag is literally `0 < ⟪J, v⃗_ℓ⟫`, i.e. `⟪−J, v⃗_ℓ⟫ < 0` with
`n_J = −J` (verified against the two worked instances, `ShellSubStrip.lean` §6 and
`LeafACwBranch.lean` §0, both giving `⟪n_J, v⃗_ℓ⟫ = −1`).

## What is here

* `dot_le_of_mem_hatOf` — the height bound: every `g ∈ Âi` has `⟪n_J, g⟫ ≤ ⟪n_J, b − k_i v⃗_ℓ⟫`
  for some `b ∈ B i`.
* `mul_le_of_shell_mem` / `mul_le_of_mem_shellInter` — the `t`-bound, first from the shell's
  level constraint alone, then composed with the height bound.
* `transverse_of_mem_shellInter` — the two together: the `n_ℓ`-coordinate of the translated
  point is `⟪n_ℓ, b⟫ + t·⟪n_ℓ, w⟫` with `t` bounded by `B i`'s own height above `c_J`.

None of these asserts `shellSubStrip`; they reduce its necessary condition to a comparison
between two quantities that both live on `B i`.  What is still owed is the sufficiency — see
the ⚠ paragraph on `transverse_of_mem_shellInter` below for which conjunct of `maxA` that
does and does not buy.

## 一名多物 (`blueprint/NOTATION.md`)

`halfStrip` is **four** constants with identical bodies: `Colle35.halfStrip`
(`Lemma35.lean`), `LE2.halfStrip` (`LatticeEdges.lean`), `ColleReg.halfStrip`
(`LayerSweep.lean`) and `SweepBase.halfStrip` (`SweepBase.lean`).  (Said "two" originally;
upgraded to "three" 2026-09-24 when the compiler — not a scan — caught the third; corrected to
**four** the same day by lane-env-refute, who counted definition sites instead of trusting the
previous count.  The `def halfStrip` in `AEnv.lean` is inside a fenced code block in a
docstring and is **not** a declaration.  Identifier names only — the line numbers this
paragraph used to carry had all rotted, PROTOCOL §85.)  The consumer `ChainDataGeom.ofPartsExhaustsInter`
sits inside `namespace Nivat.Colle35`, so its `shellSubStrip` binder resolves to
`Colle35.halfStrip`, and so does `Colle35.canonA_subset_halfStrip` (`ChainCanon.lean`).
The rule that decides this is **the enclosing namespace outranks `open`**: files such as
`ChainAssembleInter.lean` / `ChainExhaustInter.lean` do `open Nivat.LE2` yet still resolve a
bare `halfStrip` to `Colle35.halfStrip`, because they sit in `namespace Nivat.Colle35`.
So the hazard is "**outside `Colle35` while `open`ing `LE2`**" (silently picks up the other
constant), or `open`ing two of them at once (ambiguity error).  Every signature below
therefore writes `Colle35.halfStrip` explicitly — a bare `halfStrip` here is an ambiguity
error, which is how this was caught.
-/

set_option autoImplicit false

namespace Nivat.AhatHeight

open Nivat Nivat.LE2 Nivat.MaxEnv Nivat.Colle35

/-- `⟪n, t • v⟫ = t * ⟪n, v⟫`.  `LatticeEdges.dot_smul` scales the *left* argument;
this is the right-argument companion, used throughout below.
(§85: 按标识符名找。旧批注写 `:705`，已烂——实际当时在 `LatticeEdges.lean:779`。) -/
theorem dot_smul_right (n : ℤ × ℤ) (t : ℤ) (v : ℤ × ℤ) : dot n (t • v) = t * dot n v := by
  simp only [dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

/-- **The `n_J`-height of `Â_i` is attained on `B_i − k_i v⃗_ℓ`** (`b3_colle2.txt:520`).

Every `g ∈ hatOf A kk vl i` satisfies `⟪n_J, g⟫ ≤ ⟪n_J, b − k_i v⃗_ℓ⟫` for some `b ∈ B i`.

The proof is one line of sign bookkeeping, and the content is entirely in the hypothesis
`hvl : dot nJ vl ≤ 0`: `g + k_i v⃗_ℓ ∈ A i ⊆ H_{B_i}(ℓ)` writes `g + k_i v⃗_ℓ = b + s·v⃗_ℓ` with
`s : ℕ`, so `⟪n_J, g⟫ = ⟪n_J, b − k_i v⃗_ℓ⟫ + s·⟪n_J, v⃗_ℓ⟫`, and the second term is `≤ 0`.
Note what the statement does **not** depend on: neither `s` nor any bound on how far `A i`
extends along `v⃗_ℓ` appears in the conclusion.  That is the whole point — it is what makes the
`shellSubStrip` drift bound a comparison of two quantities on `B i` rather than an unbounded
one.

`hstrip` is free at the call site of `ChainDataGeom.ofPartsExhaustsInter`: `maxA i` gives
`A i ⊆ canonA η xper vl B u i` (`IsMaxEnvIn`, `ChainMax.lean:62`) and
`canonA_subset_halfStrip` (`ChainCanon.lean:99`) gives the rest. -/
theorem dot_le_of_mem_hatOf {A B : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ} {vl nJ : ℤ × ℤ} {i : ℕ}
    (hstrip : A i ⊆ Colle35.halfStrip (B i) vl) (hvl : dot nJ vl ≤ 0)
    {g : ℤ × ℤ} (hg : g ∈ hatOf A kk vl i) :
    ∃ b ∈ B i, dot nJ g ≤ dot nJ (b - (kk i : ℤ) • vl) := by
  have hgA : g + (kk i : ℤ) • vl ∈ A i := hg
  obtain ⟨b, hb, s, hs⟩ := hstrip hgA
  refine ⟨b, hb, ?_⟩
  have hdot : dot nJ g + (kk i : ℤ) * dot nJ vl = dot nJ b + (s : ℤ) * dot nJ vl := by
    have h := congrArg (dot nJ) hs
    rwa [dot_add, dot_add, dot_smul_right, dot_smul_right] at h
  have hs0 : (0 : ℤ) ≤ (s : ℤ) := Int.natCast_nonneg s
  have hneg : (s : ℤ) * dot nJ vl ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hs0 hvl
  have hsub : dot nJ (b - (kk i : ℤ) • vl) = dot nJ b - (kk i : ℤ) * dot nJ vl := by
    rw [dot_sub, dot_smul_right]
  linarith

/-- **The `t`-bound.**  If `g + t·w` lies in the `ε`-shell of `Â_∞` then
`t·(−⟪n_J, w⟫) ≤ ⟪n_J, g⟫ − c_J + ε`.  Only the shell's level constraint is used; the
`reachSet` half of `shell` is discarded. -/
theorem mul_le_of_shell_mem {Ainf : Set (ℤ × ℤ)} {nJ vJ1 w : ℤ × ℤ} {cJ : ℤ} {ε : ℕ}
    {g : ℤ × ℤ} {t : ℕ} (hz : g + (t : ℤ) • w ∈ shell Ainf vJ1 nJ cJ ε) :
    (t : ℤ) * (- dot nJ w) ≤ dot nJ g - cJ + (ε : ℤ) := by
  obtain ⟨-, -, -, -, hlev⟩ := hz
  rw [dot_add, dot_smul_right] at hlev
  have hrw : (t : ℤ) * (- dot nJ w) = -((t : ℤ) * dot nJ w) := by ring
  rw [hrw]
  linarith

/-- **Height bound and `t`-bound combined** (`b3_colle2.txt:520`).  For a point
`g + t·w` of `shellInter Âi (shell Â∞ v_{J−1} n_J c_J ε) w`, the step count `t` is bounded by
the height of a single point of `B i − k_i v⃗_ℓ` above `c_J` — a quantity attached to `B i`, not
to how far `A i` reaches along `v⃗_ℓ`. -/
theorem mul_le_of_mem_shellInter {A B : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ}
    {vl nJ vJ1 w : ℤ × ℤ} {cJ : ℤ} {i ε : ℕ}
    (hstrip : A i ⊆ Colle35.halfStrip (B i) vl) (hvl : dot nJ vl ≤ 0)
    {g : ℤ × ℤ} (hg : g ∈ hatOf A kk vl i) {t : ℕ}
    (hz : g + (t : ℤ) • w ∈ shell (⋃ j, hatOf A kk vl j) vJ1 nJ cJ ε) :
    ∃ b ∈ B i, (t : ℤ) * (- dot nJ w) ≤ dot nJ (b - (kk i : ℤ) • vl) - cJ + (ε : ℤ) := by
  obtain ⟨b, hb, hble⟩ := dot_le_of_mem_hatOf hstrip hvl hg
  exact ⟨b, hb, le_trans (mul_le_of_shell_mem hz) (by linarith)⟩

/-- **The transverse coordinate of a `shellInter` point**, which is the quantity
`shellSubStrip` has to keep inside `B i`'s `n_ℓ`-extent.  With `n_ℓ ⟂ v⃗_ℓ` the `k_i v⃗_ℓ`
translation and the `s·v⃗_ℓ` inside the half strip both drop out, leaving
`⟪n_ℓ, b⟫ + t·⟪n_ℓ, w⟫` for a `b ∈ B i` whose own height above `c_J` bounds `t`.

This is the exact necessary condition of `b3_colle2.txt:520`, with every quantity now living
on `B i`.  It is **not** the containment itself: proving that requires knowing the drift lands
back in `B i + ℕ·v⃗_ℓ`.

⚠ **Which conjunct of `maxA`** (corrected 2026-09-24; the sentence that stood here said only
"needs `maxA`" and was underdetermined — lane-leafa-shell was right to refuse to guess).
`IsMaxEnvIn Env C A` (`ChainMax.lean:62`) is a **three**-fold conjunction
`Env A ∧ A ⊆ C ∧ ∀ T, Env T → A ⊆ T → T ⊆ C → T ⊆ A`, and the two uses part ways:

* `hstrip` above is free from the **second** conjunct alone — `subStrip_of_max`
  (`ChainMax.lean:96`) has proof body `fun i _ hw => ((h i).2.1 hw).1`, i.e. `A ⊆ C` followed
  by the first conjunct of `canonA` (`ChainCanon.lean`, body
  `{w | w ∈ halfStrip (B i) vl ∧ η (w + u i) = xper w}`).  No maximality, no circularity.
* The **sufficiency** would have to run through the **third** conjunct, because
  `shellInter (Â_i) … w` is a *new* set obtained by translating points of `Â_i`, so `A i ⊆ C`
  says nothing about it; one would want `T ⊆ A` at `T :=` the translated set.  But that
  conjunct's own premise is `T ⊆ C`, whose first component is the half-strip containment being
  proved.  **That route is circular** (lane-leafa-shell, `blueprint/OPEN.md` #22).

⟹ the live route is the `Enveloped ↑S` one, not maximality: `hEnv : Env = EnvOf ↑S`
(`ChainExhaustInter.lean`, the `hEnv` binder — **按字段名找**, PROTOCOL §85) pins `Env`, so
`Env (shellInter …)` carries real geometry.

⛔ **订正 2026-09-24（集成者，第 211 轮；§14 原文不删）。上一句否掉了。**
`Nivat/External/Colle/Oct8Bench.lean`（命名空间 `Nivat.LaneTowerOct8`，0 `sorry`，在 build 里，
公理由全量 build 背书。⚠ 路径与声明数已订正 2026-09-25：本段原引 `tmp/wip/lane-tower-hbase-oct8.lean`
＋「24 条声明」，该 `tmp/` 路径在盘上**零命中**——收据没丢，是搬进主仓后引用没跟着改；
现文件顶格声明头计数为 124（下界）。lane-tower-hbase 2026-09-25 按**声明名**而非文件名搜出：
`enveloped_shellInter` `:761`、`binders_hold_but_not_shellSubStrip` `:879`、
`maxA_holds_but_not_shellSubStrip` `:1486`）给出
`ofPartsExhaustsInter` 的一个八边形实例，在 `ε = 1, i₀ = 0, I₀ = 0` 处
**`Env` 守卫是正面证成的**（`enveloped_shellInter`），`maxA` 的**完整三支**、`hnotDP`、`envShift`、
`envB`、`subBA`、`subAB`、`subStrip`、`AhatMono`、`hfin`、`hhp`、`hswept`、`ahat_nonempty`、`hexh`、
`rec_p`、`dot_nJ_p`、`hdet`、`hEnv` 同时成立，而 `shellSubStrip` **假**
（`maxA_holds_but_not_shellSubStrip` / `binders_hold_but_not_shellSubStrip`）。反例点对**所有 `i`**
成立，`I₀` 救不回来。

⟹ 本文件这三条引理的地位不变（它们是**必要**条件，仍然真），但「把必要升成充分」这件事
**在本文件的假设范围内不可能做到**：`Enveloped ↑S` 既不足、maximality 也不足。`shellSubStrip`
的真正输入只能来自表外——`escapeW` / `fillCover` / `bottom` / `hsweepW` / `FaceBlock` 包 / `hpvJ`
的耦合，或链上真实的 `ξ` / `x_per` 结构。详见 `blueprint/OPEN.md` 同名条目。
**不要再派「从横截支直攻 `shellSubStrip`」的工。**

🔴 **降格 2026-09-25（集成者，第 226 轮）。上面这条禁令的依据已被其来源自我限缩，禁令作废。**
lane-tower-hbase 亲读 `Oct8Bench.lean:1504-1522`（该文件自己的 §10）：第 212 轮 lane-leafa-shell
往 `ofPartsExhaustsInter` 加了 `hp_per : p ∈ Per xper`（锚 `b3_colle2.txt:496`，集成者批准），
与既有 `hdet : det p vl = 0` 同表；在该台架的 `xperx`/`vlx` 下两者同时为真只有 `p = 0`
（机理 `mem_Per_xperx_fst_zero`，`Oct8Bench.lean:1532`），而 `p = 0` 撞表里其余 binder。
该文件自陈结论必须重述成「**第 211 轮那张表**推不出 `shellSubStrip`」，**对含 `hp_per` 的现役表
本台架是空真的**，补齐 `fillCover` 之类剩余 binder 也不构成反证。
⟹ 上面那句禁令只覆盖第 211 轮那张不含 `hp_per` 的表，**在现役签名上没有活着的依据**。
⚠ 这**不**等于主张 `shellSubStrip` 为真，也不等于推荐去攻它——只是那条禁令不再是拦它的理由。
⚠ 本文件三条引理作为**必要**条件的地位不受影响（那一段仍然成立）。

⭐ 但方向已由第 226 轮的裁决改掉，比这条禁令更要紧：壳字段统一走 **(B) 栈**
（原文 `b3_colle2.txt:518` 的**取交**形 `ShellMink.shellInter`，而非 `:440` 的单扫 `MaxEnv.shell`）。
判据：`ShellMink.not_shellSubStrip_of_transverse_sweep`（`ShellMink.lean:668`）是**全称**的
（`{Bi Ai}` 任意，只要 `Bi.Finite` + `Ai.Nonempty` + `det vl v ≠ 0`）⟹ 单扫形上 `shellSubStrip`
无条件为假；而取交形上 lane-leafa-shell 量出它**多要一条 `hreach`**
（`tmp/wip/lane-leafa-shell-detvl.lean` §4 `not_shellSubStrip_inter_of_transverse`，EXIT=0）
⟹ 不再无条件为假。⟹ **该攻的是取交形，不是横截支的单扫形。** -/
theorem transverse_of_mem_shellInter {A B : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ}
    {vl nℓ nJ vJ1 w : ℤ × ℤ} {cJ : ℤ} {i ε : ℕ}
    (hstrip : A i ⊆ Colle35.halfStrip (B i) vl) (hvl : dot nJ vl ≤ 0) (hperp : dot nℓ vl = 0)
    {g : ℤ × ℤ} (hg : g ∈ hatOf A kk vl i) {t : ℕ}
    (hz : g + (t : ℤ) • w ∈ shell (⋃ j, hatOf A kk vl j) vJ1 nJ cJ ε) :
    ∃ b ∈ B i, ∃ b' ∈ B i,
      dot nℓ (g + (t : ℤ) • w + (kk i : ℤ) • vl) = dot nℓ b' + (t : ℤ) * dot nℓ w ∧
      (t : ℤ) * (- dot nJ w) ≤ dot nJ (b - (kk i : ℤ) • vl) - cJ + (ε : ℤ) := by
  obtain ⟨b, hb, hbound⟩ := mul_le_of_mem_shellInter hstrip hvl hg hz
  have hgA : g + (kk i : ℤ) • vl ∈ A i := hg
  obtain ⟨b', hb', s, hs⟩ := hstrip hgA
  refine ⟨b, hb, b', hb', ?_, hbound⟩
  have hgvl : dot nℓ (g + (kk i : ℤ) • vl) = dot nℓ b' := by
    rw [hs, dot_add, dot_smul_right, hperp]; ring
  have hexp : dot nℓ (g + (t : ℤ) • w + (kk i : ℤ) • vl)
      = dot nℓ (g + (kk i : ℤ) • vl) + (t : ℤ) * dot nℓ w := by
    rw [dot_add, dot_add, dot_add, dot_smul_right, dot_smul_right]; ring
  rw [hexp, hgvl]

end Nivat.AhatHeight

#print axioms Nivat.AhatHeight.dot_le_of_mem_hatOf
#print axioms Nivat.AhatHeight.mul_le_of_mem_shellInter
#print axioms Nivat.AhatHeight.transverse_of_mem_shellInter
