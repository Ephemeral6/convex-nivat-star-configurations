/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.BottomRoom
import Nivat.External.Colle.ANormal

/-!
# The guard on `bottom`'s `hwin` is not a weakening

lane-tower-hlev, 2026-09-24 (第 208 轮).  **Negative result, kernel-certified.**

## 本文件在 build 里的身份（(C) 类回归护栏）

**设计上无证明项消费者。**本文件是「守卫可换更便宜义务」这条死路线的回归护栏，内核结论是
`BottomRoom.bottom_of_window` 的**带守卫** `hwin` 与 `BottomRoom.window_of_shell` 的**无守卫**
形式在调用点前提下**等价**。

它看起来违反「有消费者才导出」，因为**它的消费者不是证明项，是人**：这条路线上轮被 lane-tower-hlev
报为「错配、可利用」，集成者信了，而 `BottomRoom.lean` §4 的 docstring 还专门为它最小化过一轮接口
（`hwin ⟸ hroom ⟸ hband ⟸ (hcoreV ∧ hcoreV')`）。0 sorry 的内核事实把它钉死；移出 build 就降级
成散文，而 PROTOCOL §40 的反向形态说的正是这个——**活路线被一句话判死很贵，死路线被当活的更贵**。
⟹ 以后谁再提「守卫能换便宜义务」，指这个文件。

## 这条负结果说的是什么

`BottomRoom.bottom_of_window` consumes its window premise in the *guarded* form

    hwin : ∀ b ∈ S, 0 < dot nJ (b - a) → z₀ + (b - a) ∈ reachSet T vJ1

while the only producer in the tree, `BottomRoom.window_of_shell`, delivers the *unguarded*
one (`∀ b ∈ d.toDecompData.Sphi, z₀ + (b - a) ∈ reachSet T vJ1`, no side condition).  That
asymmetry looks like slack: the consumer appears to ask for strictly less than the producer
supplies, so one would hope to discharge the guarded form by some cheaper route that never
has to handle the `b` the guard excludes.

`hwin_guarded_iff` below shows **there is no such slack**.  Under binders that
`bottom_of_window` either already takes (`hrecT`, `hz₀`, `hedge`) or gets free at the call
site (`hnJvJ`, which is `FaceBlock.dot_nJ_vJ`), the two forms are **equivalent**.

The mechanism is that the excluded `b` are exactly the ones already paid for:

* `faceStart_of_edge hnJvJ hedge` (`BottomRoom.lean`) turns `hedge` into `ha_min` (`a`
  minimises `dot nJ` on `S`) and `ha_end` (the minimising row out of `a` is the forward
  `vJ`-run).  So `0 ≤ dot nJ (b - a)` for every `b ∈ S`, and the guard excludes exactly
  `dot nJ (b - a) = 0`, i.e. by `ha_end` exactly `b = a + t • vJ` with `t : ℕ`.
* For those, `z₀ + (b - a) = z₀ + t • vJ`, and `vJ` is a recession direction of `T` by
  `hrecT`, so `Colle35.reachSet_add_zsmul_of_rec` (`ANormal.lean`) puts the whole forward
  `vJ`-ray out of `z₀` inside `reachSet T vJ1` from `hz₀` alone.

⟹ nobody should spend a round trying to produce the guarded form more cheaply than the
unguarded one, and `window_of_shell`'s unguarded conclusion is **not** overkill.  `hwin` 一侧的
**形状优化到此为止**；剩下的全是 `window_of_shell` 的 `hPsub` / `hEeq` / `henv` 的实质内容。

⚠ 这条**只管 bottom 侧的 `hwin`**。`hwin` 是一名两物（`FillCoverGuarded.lean:98` 的警告）：
`FillCoverGuarded.fillCover_of_window` 的同名前提带 `Enveloped` 守卫、带 `∨`、对**所有** `z` 量化、
指标跑 `S` 而不是 `d.Sphi`、目标是 `shellInter`。那一侧的守卫**没有**在这里被证明是可去的，预期相反
（`eps_lt_of_enveloped` 在 `i = i₀` 卡 `ε`，守卫承重），但本文件**没有算**（PROTOCOL §51）。

## Status of the statement (hard rule 5)

This introduces **no new `Prop`**.  Both sides are the `hwin` premise of the existing
`BottomRoom.bottom_of_window`, transcribing `scratch/b3_colle2.txt:518-520`; the only content
here is the implication between its two spellings, so there is no new quantifier to align
against the source and nothing here is stronger than Collé.

The `S`/`a`/`nJ`/`vJ` of the statement are `bottom_of_window`'s own, left as bare parameters:
at the leaf-A call site they are instantiated to `d.Sphi` / `F.a` / `nJ` / `vJ`, but nothing
below needs that, so it is not assumed.

## 一名多物 (`blueprint/NOTATION.md`)

`reachSet` and `dot` each have exactly **one** definition in the tree
(`ShellLine.lean:35` in `namespace Nivat.MaxEnv`, and `LatticeEdges.lean:72`), checked this
round, so the bare names below cannot silently pick up a different constant — unlike
`halfStrip`, which has three (see `AhatHeight.lean`'s 一名多物 section).  This file sits
outside `Nivat.Colle35`, which is the configuration that rule flags as hazardous, hence the
check.

## import 表

`grep -n "^import"` gives exactly `Nivat.External.Colle.BottomRoom` and
`Nivat.External.Colle.ANormal` (PROTOCOL §57).  Neither `RegionSteps` nor `ColleRegion` nor
`Case2WindowProbe` nor `NfpLPreamble` is in the closure, and this file adds **no** import to
any consumer — being a (C)-class guard, it has none.
-/

set_option autoImplicit false

namespace Nivat.LaneTowerHlevHwin

open Nivat Nivat.LE2 Nivat.MaxEnv

/-- **The excluded `b` are free.**  If `dot nJ (b - a) ≤ 0` for a `b ∈ S` whose edge data is
`hedge`, then `b` sits on the `vJ`-run out of `a`, so `z₀ + (b - a)` is on the forward
`vJ`-ray out of `z₀` and `hrecT` alone puts it in `reachSet T vJ1`. -/
theorem mem_reachSet_of_dot_nonpos {T : Set (ℤ × ℤ)} {S : Finset (ℤ × ℤ)}
    {nJ vJ vJ1 z₀ a : ℤ × ℤ}
    (hrecT : ∀ g ∈ T, g + vJ ∈ T)
    (hnJvJ : dot nJ vJ = 0)
    (hz₀ : z₀ ∈ reachSet T vJ1)
    (hedge : ∀ b ∈ S.erase a,
      (∃ j : ℕ, 1 ≤ j ∧ b = a + (j : ℤ) • vJ) ∨ 1 ≤ dot nJ (b - a))
    {b : ℤ × ℤ} (hb : b ∈ S) (hle : dot nJ (b - a) ≤ 0) :
    z₀ + (b - a) ∈ reachSet T vJ1 := by
  obtain ⟨ha_min, ha_end⟩ := Nivat.BottomRoom.faceStart_of_edge hnJvJ hedge
  have hbS : b ∈ (↑S : Set (ℤ × ℤ)) := Finset.mem_coe.mpr hb
  have hmin := ha_min b hbS
  have hlev : dot nJ b = dot nJ a := by
    rw [dot_sub] at hle; omega
  obtain ⟨t, hbt⟩ := ha_end b hbS hlev
  have hsub : b - a = (t : ℤ) • vJ := by rw [hbt]; abel
  rw [hsub]
  exact Nivat.Colle35.reachSet_add_zsmul_of_rec hrecT hz₀ (Int.natCast_nonneg t)

/-- **The guard is not a weakening: guarded `hwin` ⟹ unguarded `hwin`.** -/
theorem hwin_unguarded_of_guarded {T : Set (ℤ × ℤ)} {S : Finset (ℤ × ℤ)}
    {nJ vJ vJ1 z₀ a : ℤ × ℤ}
    (hrecT : ∀ g ∈ T, g + vJ ∈ T)
    (hnJvJ : dot nJ vJ = 0)
    (hz₀ : z₀ ∈ reachSet T vJ1)
    (hedge : ∀ b ∈ S.erase a,
      (∃ j : ℕ, 1 ≤ j ∧ b = a + (j : ℤ) • vJ) ∨ 1 ≤ dot nJ (b - a))
    (hwin : ∀ b ∈ S, 0 < dot nJ (b - a) → z₀ + (b - a) ∈ reachSet T vJ1) :
    ∀ b ∈ S, z₀ + (b - a) ∈ reachSet T vJ1 := by
  intro b hb
  by_cases hpos : 0 < dot nJ (b - a)
  · exact hwin b hb hpos
  · exact mem_reachSet_of_dot_nonpos hrecT hnJvJ hz₀ hedge hb (by omega)

/-- **The two spellings of `hwin` are equivalent.**  The `←` direction is immediate; the `→`
direction is `hwin_unguarded_of_guarded`.  Consequence: `BottomRoom.window_of_shell`'s
unguarded conclusion is the right target, and there is no cheaper guarded obligation to aim
at instead. -/
theorem hwin_guarded_iff {T : Set (ℤ × ℤ)} {S : Finset (ℤ × ℤ)}
    {nJ vJ vJ1 z₀ a : ℤ × ℤ}
    (hrecT : ∀ g ∈ T, g + vJ ∈ T)
    (hnJvJ : dot nJ vJ = 0)
    (hz₀ : z₀ ∈ reachSet T vJ1)
    (hedge : ∀ b ∈ S.erase a,
      (∃ j : ℕ, 1 ≤ j ∧ b = a + (j : ℤ) • vJ) ∨ 1 ≤ dot nJ (b - a)) :
    (∀ b ∈ S, 0 < dot nJ (b - a) → z₀ + (b - a) ∈ reachSet T vJ1) ↔
      (∀ b ∈ S, z₀ + (b - a) ∈ reachSet T vJ1) :=
  ⟨fun hwin => hwin_unguarded_of_guarded hrecT hnJvJ hz₀ hedge hwin,
    fun h b hb _ => h b hb⟩

end Nivat.LaneTowerHlevHwin

#print axioms Nivat.LaneTowerHlevHwin.mem_reachSet_of_dot_nonpos
#print axioms Nivat.LaneTowerHlevHwin.hwin_unguarded_of_guarded
#print axioms Nivat.LaneTowerHlevHwin.hwin_guarded_iff
