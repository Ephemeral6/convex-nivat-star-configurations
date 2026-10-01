/-
Copyright (c) 2026. Released under Apache 2.0 license.
Authors: lane-chaindata-lead
-/
import Nivat.External.Colle.ShellLine
import Nivat.External.Colle.ANormal

/-!
# `bottom`'s window slice, split by `hedge`: only the raised points are still owed

Consumer: the `bottom` binder of `Nivat.Colle35.ChainDataGeom.ofPartsExhaustsInter`
(`ChainExhaustInter.lean`), consumed at `tmp/wip/LeafAAssemble.lean`'s
`(bottom := by … sorry)`.

## Where this sits relative to what is already in the tree

`Nivat.Colle35.ChainDataWithShell.bottom_of_seed` (`ANormal.lean:771`) already reduces `bottom`'s
two `∀ k ≥ L` conjuncts to their `k = L` slice, via
`Nivat.Colle35.reachSet_add_zsmul_of_rec` (`ANormal.lean:731`) — `reachSet` inherits `rec_vJ`'s
closure under `· + vJ`.  Nothing below re-proves any of that; it is imported and used.

What `bottom_of_seed` still charges a producer is the full slice

    hseedS : ∀ b ∈ S, z₀ + L • vJ + (b - a) ∈ reachSet (⋃ i, Ahat i) vJ1

— one membership for **every** point of the window.  That is what `hseedS_of_parts`
(`tmp/wip/lane-cd-bottom.lean:562`) is for, and it is where the `L`-seam bites: `hseedS_of_parts`
gets its `L` from `hstrip`'s real-analysis threshold, while `LeafABottom.hline_only_of_wedge`
supplies `hline_only` only at `L = 0`.  `tmp/wip/lane-cd-lseam.lean` settles in the kernel that
those cannot be reconciled by choosing `L`: `hseed` forces `0 ≤ L`, `hline_only_of_wedge` forces
`L ≤ 0`, so `L = 0` exactly, with no freedom left.

## What is new here

At `L = 0` the window slice splits along `FanEndpoint.faceBlock_edge_forget_len`'s dichotomy into
four cases, and only the last is still open:

* `b = a` — the slice point is `z₀` itself.
* `b - a = j • vJ` (the `vJ`-run out of `F.a`) — absorbed into the ray by
  `reachSet_add_zsmul_of_rec`, since `j ≥ 0`.
* `1 ≤ dot nJ (b - a) ≤ ε` (`hlow`) — **already proved**, and at `L = 0` already.  It is the
  `hlow` branch inside `hseedS_of_parts` (`tmp/wip/lane-cd-bottom.lean:594-606`), which returns
  `⟨0, _⟩` and closes via `mem_reachSet_of_wedge` (`lane-cd-bottom.lean:144`).  That branch never
  touches `hstrip`.
* `ε < dot nJ (b - a)` (`hhigh`) — **the only case still owed.**

So the `L`-seam is confined to a single branch.  Reading `hseedS_of_parts` back with this split:
its `hlow` branch already produces `L = 0`, and *only* its `hhigh` branch
(`lane-cd-bottom.lean:607-620`) reaches for `hexists_high`/`hstrip` and returns a large `L`.  The
big `L` was never needed for the window as a whole — just for the raised points.

## The one thing still owed, and why it is NOT provable from the data below

    hhigh : ∀ b ∈ S, (ε : ℤ) < dot nJ (b - a) → z₀ + (b - a) ∈ reachSet T vJ1

**`hhigh` is false for a general `T` satisfying every other hypothesis here.**  Kernel witness:
`tmp/wip/lane-cd-hhigh-refute.lean`, `Nivat.HhighRefute.refuting_instance`, on
`S := ApexUnique.Shex`, `T := {z | 0 ≤ z.2 ∧ 2 * z.2 ≤ z.1}`, `nJ := (0,1)`, `vJ := (1,0)`,
`vJ1 := (0,-1)`, `cJ := 0`, `ε := 0`, `a := (0,0)`, `z₀ := (0,-1)`.  There
`z₀ + ((1,2) - a) = (1,1) ∉ reachSet T vJ1`, while `hrecT`, `hdz`, `hz₀`, `hline0`, `hedge`,
`hlow` all hold — as do the whole `J`-package surround (`hhp`, `hsweep`, `hswept`, `hray`,
`hSnp`, `hsupp_prev_U`, `dot nprevJ vJ1 = 0`, `dot nprevJ vJ < 0`).  So no rearrangement of the
binders at the call site closes it; `hhigh` needs a hypothesis this signature does not have.

The missing premise is **not** any envelopedness property of `T`.  Two kernel witnesses pin
this down, both in `tmp/wip/`:

* `lane-cd-hhigh-refute.lean` (`HhighRefute.refuting_instance`) — the instance above.
* `lane-cd-hhigh-refute2.lean` (`HhighRefuteTwo.refuting_instance_weaklyEnveloped`) — a second
  instance where `WeaklyEnveloped ↑S T` holds non-vacuously (`E T₂ = {(0,-1), (-1,1)}` is
  proved there) and `hhigh` still fails.  `E T ⊆ E S` pins the *directions* of `T`'s edges but
  not their *offsets* relative to `a`, so the failure just moves into the offset.

Full `Enveloped ↑S T` is not available either: `hray` puts a `+vJ`-ray into `T`, so no normal
`n` with `dot n vJ > 0` has a nonempty face on `T`, while `S` is finite and generically does
have such edges — hence `(E T).encard < (E S).encard`.  This is why `b3_colle2.txt:506` says
only **weakly** enveloped for `Â_∞` and reserves the full form (`:520`) for the finite-stage
shell `Â_i^{(ε)}`.  (⚠ 第 201 轮订正：这里原记 `:505`，那是空行；那句在 `:506`。)

**So this lemma sits at an abstraction level that cannot carry `hhigh`.**  The premise has to
come from the finite stages — each `A i` is fully `Enveloped ↑S` via `maxA.1` and `hEnv` in
`ChainExhaustInter.ofPartsExhaustsInter`, and `b3_colle2.txt:520` asserts the shell is too —
which means a repaired version needs `A`, `kk`, `vl` in its signature rather than an abstract
`T : Set (ℤ × ℤ)`.  The three declarations below remain true as stated; what they do *not* do
is reduce `bottom` to something reachable from the call site's data.  `hhigh` must not be
dispatched in this form: a lane taking it would be proving a false statement.

`hhigh_vacuous` below records the one thing that *is* free: `S` is fixed and finite while
`bottom` quantifies over **all** `ε`, so once `ε` passes the window's `nJ`-extent
`max_{b ∈ S} dot nJ (b - a)` there is no `b` left and the obligation is empty.  That bounds the
open part to the finitely many small `ε` — but it does not shrink the hardest case, `ε = 0`,
where `hlow` is empty and `hhigh` must absorb every raised point of the window.

`hstrip` does not settle those either: it gives membership only past a threshold along `vJ`,
and `L = 0` is exactly the statement that the threshold is no longer available to spend.
-/

set_option autoImplicit false

namespace Nivat.BottomReachMin

open Nivat Nivat.LE2 Nivat.Colle35 Nivat.MaxEnv

/-- **`hseedS` at `L = 0`, with the `vJ`-run discharged.**

`hedge` is `FanEndpoint.faceBlock_edge_forget_len` (already in the main tree).

`hrecT` is `rec_vJ`.  It must **not** be taken from the `rec_vJ'` that `ofPartsExhaustsInter`
builds (`ChainExhaustInter.lean`), since that one calls `rec_vJ_of_bottom` on `bottom`
itself — feeding it back here is a circle.  The non-circular route is `Colle35.rec_of_ray`
(`ItemII.lean:757`) applied to the `J`-package's `hray` (`∀ k : ℕ, g_J + k • eJ ∈ ⋃ i, Â i`,
`LeafAAssemble.lean:289`) transported along `hvJ_eq : vJ = eJ`, with lattice-convexity of the
union from `latticeConvex_iUnion_hatOf`.  `rec_of_ray` derives closure under `+ d` from a single
`ℕ`-ray in direction `d`, so no instance of `bottom` is consumed. -/
theorem hseedS_of_edge {T : Set (ℤ × ℤ)} {S : Finset (ℤ × ℤ)} {nJ vJ vJ1 z₀ a : ℤ × ℤ} {ε : ℕ}
    (hrecT : ∀ g ∈ T, g + vJ ∈ T)
    (hz₀ : z₀ ∈ reachSet T vJ1)
    (hedge : ∀ b ∈ S.erase a,
      (∃ j : ℕ, 1 ≤ j ∧ b = a + (j : ℤ) • vJ) ∨ 1 ≤ dot nJ (b - a))
    (hlow : ∀ b ∈ S, 1 ≤ dot nJ (b - a) → dot nJ (b - a) ≤ (ε : ℤ) →
      z₀ + (b - a) ∈ reachSet T vJ1)
    (hhigh : ∀ b ∈ S, (ε : ℤ) < dot nJ (b - a) → z₀ + (b - a) ∈ reachSet T vJ1) :
    ∀ b ∈ S, z₀ + (0 : ℤ) • vJ + (b - a) ∈ reachSet T vJ1 := by
  intro b hb
  rw [zero_smul, add_zero]
  by_cases hba : b = a
  · subst hba; simpa using hz₀
  · rcases hedge b (Finset.mem_erase.mpr ⟨hba, hb⟩) with ⟨j, -, hj⟩ | hge
    · have e : z₀ + (b - a) = z₀ + (j : ℤ) • vJ := by rw [hj]; abel
      rw [e]
      exact reachSet_add_zsmul_of_rec hrecT hz₀ (Int.natCast_nonneg j)
    · by_cases hlt : (ε : ℤ) < dot nJ (b - a)
      · exact hhigh b hb hlt
      · exact hlow b hb hge (not_lt.mp hlt)

/-- **The high case is vacuous once the shell is deeper than the window.**  `S` is fixed and
finite while `bottom` quantifies over all `ε`, so for every `ε` past the window's `nJ`-extent
there is no `b` left to handle. -/
theorem hhigh_vacuous {S : Finset (ℤ × ℤ)} {T : Set (ℤ × ℤ)} {nJ vJ1 z₀ a : ℤ × ℤ} {ε : ℕ}
    (hbound : ∀ b ∈ S, dot nJ (b - a) ≤ (ε : ℤ)) :
    ∀ b ∈ S, (ε : ℤ) < dot nJ (b - a) → z₀ + (b - a) ∈ reachSet T vJ1 :=
  fun b hb hlt => absurd (hbound b hb) (not_le.mpr hlt)

/-- **`bottom` at the reach-minimal base point**, in the exact shape
`ChainDataGeom.ofPartsExhaustsInter` asks for (`MaxEnv.shell`, not `ChainData.shellInf`, which is
why `ChainDataWithShell.bottom_of_seed` is not directly applicable at that call site).

With `L := 0`, all four conjuncts reduce to `hz₀`, `hline0`, `hedge`, and `hcase2`.  Conjunct (4)
goes through `MaxEnv.mem_shell_succ_iff` (`ShellLine.lean:54`): the layer increment is the single
line `dot nJ · = cJ - ε - 1`, which is exactly `hline0`'s domain. -/
theorem bottom_of_reachMin {T : Set (ℤ × ℤ)} {S : Finset (ℤ × ℤ)}
    {nJ vJ vJ1 z₀ a : ℤ × ℤ} {cJ : ℤ} {ε : ℕ}
    (hrecT : ∀ g ∈ T, g + vJ ∈ T)
    (hdz : dot nJ z₀ = cJ - (ε : ℤ) - 1)
    (hz₀ : z₀ ∈ reachSet T vJ1)
    (hline0 : ∀ z ∈ reachSet T vJ1, dot nJ z = cJ - (ε : ℤ) - 1 →
      ∃ k : ℤ, 0 ≤ k ∧ z = z₀ + k • vJ)
    (hedge : ∀ b ∈ S.erase a,
      (∃ j : ℕ, 1 ≤ j ∧ b = a + (j : ℤ) • vJ) ∨ 1 ≤ dot nJ (b - a))
    (hlow : ∀ b ∈ S, 1 ≤ dot nJ (b - a) → dot nJ (b - a) ≤ (ε : ℤ) →
      z₀ + (b - a) ∈ reachSet T vJ1)
    (hhigh : ∀ b ∈ S, (ε : ℤ) < dot nJ (b - a) → z₀ + (b - a) ∈ reachSet T vJ1) :
    ∃ (z₀' : ℤ × ℤ) (L : ℤ),
      dot nJ z₀' = cJ - (ε : ℤ) - 1 ∧
      (∀ k : ℤ, L ≤ k → z₀' + k • vJ ∈ reachSet T vJ1) ∧
      (∀ b ∈ S, ∀ k : ℤ, L ≤ k → z₀' + k • vJ + (b - a) ∈ reachSet T vJ1) ∧
      (∀ z ∈ shell T vJ1 nJ cJ (ε + 1),
        z ∈ shell T vJ1 nJ cJ ε ∨ ∃ k : ℤ, L ≤ k ∧ z = z₀' + k • vJ) := by
  have hray : ∀ k : ℤ, 0 ≤ k → z₀ + k • vJ ∈ reachSet T vJ1 :=
    fun _ hk => reachSet_add_zsmul_of_rec hrecT hz₀ hk
  have hslice := hseedS_of_edge hrecT hz₀ hedge hlow hhigh
  refine ⟨z₀, 0, hdz, hray, ?_, ?_⟩
  · intro b hb k hk
    have e : z₀ + k • vJ + (b - a) = (z₀ + (0 : ℤ) • vJ + (b - a)) + k • vJ := by
      rw [zero_smul, add_zero]; abel
    rw [e]
    exact reachSet_add_zsmul_of_rec hrecT (hslice b hb) hk
  · intro z hz
    rcases mem_shell_succ_iff.mp hz with h | ⟨hreach, hlev⟩
    · exact Or.inl h
    · exact Or.inr (hline0 z hreach hlev)

/-! ## `hlow` / `hhigh` 是**一条** ε-无关的义务，`hhigh_vacuous` 净收益为零

集成者 2026-09-26 派的活是「数清 `bottom_of_reachMin` 那六条 binder 里还剩几条真 binder」。
本节把其中一条答案做成定理而不是散文：`hlow` 与 `hhigh` 的定义域拼起来恰好是
`{b ∈ S | 1 ≤ dot nJ (b - a)}`，**与 ε 无关** —— `hlow` 管 `1 ≤ d ≤ ε`，`hhigh` 管 `ε < d`，
并集对任何 ε 都是同一个集合。

⟹ `hhigh_vacuous`（本文件，按名引）虽然在 `ε ≥ max_{b ∈ S} dot nJ (b - a)` 时让 `hhigh`
空真，但同一个 ε 下 `hlow` 的定义域**同步扩张**到整个 `{d ≥ 1}`。**净收益为零**，
它是记账工具、不是消费掉一条义务。下面两条把这件事钉到内核：`hslice_of_low_high` 是
「两条 ⟹ 一条」，`bottom_of_reachMin_merged` 是「一条 ⟹ 两条都不用」，合起来即等价。 -/

/-- `hlow` ＋ `hhigh` ⟹ 合并形（ε 消失）。 -/
theorem hslice_of_low_high {T : Set (ℤ × ℤ)} {S : Finset (ℤ × ℤ)}
    {nJ vJ1 z₀ a : ℤ × ℤ} {ε : ℕ}
    (hlow : ∀ b ∈ S, 1 ≤ dot nJ (b - a) → dot nJ (b - a) ≤ (ε : ℤ) →
      z₀ + (b - a) ∈ reachSet T vJ1)
    (hhigh : ∀ b ∈ S, (ε : ℤ) < dot nJ (b - a) → z₀ + (b - a) ∈ reachSet T vJ1) :
    ∀ b ∈ S, 1 ≤ dot nJ (b - a) → z₀ + (b - a) ∈ reachSet T vJ1 := by
  intro b hb h1
  by_cases hlt : (ε : ℤ) < dot nJ (b - a)
  · exact hhigh b hb hlt
  · exact hlow b hb h1 (not_lt.mp hlt)

/-- **`bottom_of_reachMin` 的合并形：六条 binder 变五条，且新的那条与 ε 无关。**

与 `bottom_of_reachMin` 逐字同结论，只把 `hlow` ＋ `hhigh` 换成单条 `hslice`。
反向由 `hslice_of_low_high` 给出 ⟹ 两种写法等价，`hhigh` 不是独立义务。

⚠ `hhigh` 一侧的推导用的是 `(ε : ℕ)` 的非负性：`ε < dot nJ (b - a)` ＋ `0 ≤ (ε : ℤ)`
在整数上给 `1 ≤ dot nJ (b - a)`，所以 `hslice` 的守卫在高段自动满足、不是额外假设。 -/
theorem bottom_of_reachMin_merged {T : Set (ℤ × ℤ)} {S : Finset (ℤ × ℤ)}
    {nJ vJ vJ1 z₀ a : ℤ × ℤ} {cJ : ℤ} {ε : ℕ}
    (hrecT : ∀ g ∈ T, g + vJ ∈ T)
    (hdz : dot nJ z₀ = cJ - (ε : ℤ) - 1)
    (hz₀ : z₀ ∈ reachSet T vJ1)
    (hline0 : ∀ z ∈ reachSet T vJ1, dot nJ z = cJ - (ε : ℤ) - 1 →
      ∃ k : ℤ, 0 ≤ k ∧ z = z₀ + k • vJ)
    (hedge : ∀ b ∈ S.erase a,
      (∃ j : ℕ, 1 ≤ j ∧ b = a + (j : ℤ) • vJ) ∨ 1 ≤ dot nJ (b - a))
    (hslice : ∀ b ∈ S, 1 ≤ dot nJ (b - a) → z₀ + (b - a) ∈ reachSet T vJ1) :
    ∃ (z₀' : ℤ × ℤ) (L : ℤ),
      dot nJ z₀' = cJ - (ε : ℤ) - 1 ∧
      (∀ k : ℤ, L ≤ k → z₀' + k • vJ ∈ reachSet T vJ1) ∧
      (∀ b ∈ S, ∀ k : ℤ, L ≤ k → z₀' + k • vJ + (b - a) ∈ reachSet T vJ1) ∧
      (∀ z ∈ shell T vJ1 nJ cJ (ε + 1),
        z ∈ shell T vJ1 nJ cJ ε ∨ ∃ k : ℤ, L ≤ k ∧ z = z₀' + k • vJ) :=
  bottom_of_reachMin hrecT hdz hz₀ hline0 hedge
    (fun b hb h1 _ => hslice b hb h1)
    (fun b hb hlt => hslice b hb (by
      have hε : (0 : ℤ) ≤ (ε : ℤ) := Int.natCast_nonneg ε
      omega))

/-! ## `hne` 是六条残余里唯一的真欠账，而它的形状是一个整数方程

`NlmaxReachMin.exists_reachMin_of_L`（按名引）把 `hdz` / `hz₀` / `hline0` 三条一次产出，
它自己剩下的那条是 `hne : ∃ z ∈ reachSet T vJ1, dot nJ z = c`，其中 `c = cJ - ε - 1`。

`reachSet` 是沿 `vJ1` 的**单向**扫出（`ShellLine.lean`，`reachSet`：`t : ℕ`），所以
`dot nJ (g + t • vJ1) = dot nJ g + t * dot nJ vJ1`：可达高度恰是以 `dot nJ vJ1` 为步长、
从 `T` 各点高度出发、**只向一侧**延伸的等差数列。下面两条是这件事的两个方向，合起来说明
`hne` 与那个整数方程**等价**，不是被弱化成它。

⚠ 这两条**不证**覆盖性。`∀ ε` 版的 `hne` 等价于「`T` 的 `nJ`-高度覆盖模 `dot nJ vJ1`
的每个剩余类」，那是整除／格指标方向，本 lane 不投；`ANormal.lean` 的
`not_bottom_of_shell_data`（按名引）给的反模型正是这个障碍的一个实例
（扫出的层全为偶、而 `cJ - 1` 为奇），其 docstring 已把残余记在 `exists_chainData`
的放置义务上。这里只把义务写成它真正的形状，省得下一个人重算算术。 -/

/-- **`hne` ⟸ 一个高度见证**：`T` 里有一点 `g` 与一个 `t : ℕ` 使
`dot nJ g + t * dot nJ vJ1 = c`，即给出 `hne`。 -/
theorem hne_of_height_witness {T : Set (ℤ × ℤ)} {nJ vJ1 g : ℤ × ℤ} {c : ℤ} {t : ℕ}
    (hg : g ∈ T) (hc : dot nJ g + (t : ℤ) * dot nJ vJ1 = c) :
    ∃ z ∈ reachSet T vJ1, dot nJ z = c := by
  refine ⟨g + (t : ℤ) • vJ1, mem_reachSet.mpr ⟨g, hg, t, rfl⟩, ?_⟩
  rw [dot_add, Nivat.ColleReg.dot_zsmul_right]
  exact hc

/-- **反向**：`hne` 只能来自这样一个高度见证 ⟹ 上一条没有把义务弱化。 -/
theorem height_witness_of_hne {T : Set (ℤ × ℤ)} {nJ vJ1 : ℤ × ℤ} {c : ℤ}
    (hne : ∃ z ∈ reachSet T vJ1, dot nJ z = c) :
    ∃ g ∈ T, ∃ t : ℕ, dot nJ g + (t : ℤ) * dot nJ vJ1 = c := by
  obtain ⟨z, hzmem, hz⟩ := hne
  obtain ⟨g, hg, t, rfl⟩ := mem_reachSet.mp hzmem
  refine ⟨g, hg, t, ?_⟩
  rw [dot_add, Nivat.ColleReg.dot_zsmul_right] at hz
  exact hz

end Nivat.BottomReachMin

#print axioms Nivat.BottomReachMin.hne_of_height_witness
#print axioms Nivat.BottomReachMin.height_witness_of_hne
#print axioms Nivat.BottomReachMin.hseedS_of_edge
#print axioms Nivat.BottomReachMin.hhigh_vacuous
#print axioms Nivat.BottomReachMin.bottom_of_reachMin
#print axioms Nivat.BottomReachMin.hslice_of_low_high
#print axioms Nivat.BottomReachMin.bottom_of_reachMin_merged
