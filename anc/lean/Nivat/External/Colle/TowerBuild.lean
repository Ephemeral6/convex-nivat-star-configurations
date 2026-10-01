/-
Copyright (c) 2025 Nivat Formalization Contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hnorm (agent)
-/
import Nivat.External.Colle.RegionSweep
import Nivat.External.Colle.L1Region
import Nivat.External.Colle.L1RegionBuild
-- **2026-09-21 集成者补 import（盲区 1b：先算受影响集合，再加 import）。**
-- `periodOn_coneRegion_of_lines` 用到 `Nivat.ConeRegion.coneRegion`、
-- `Nivat.ConeLines.coneRegion_subset_halfStrip_union_lines`、
-- `Nivat.SweepLines.periodOn_of_lines_sweep`，三者此前都不在本文件的 import 闭包里
-- （全量 `lake build` 报 7 条 `Unknown identifier`）。
-- 受影响集合实测：`TowerBuild → Stage2Index → RegionSteps`，`RegionSteps` 原闭包 150 个模块，
-- 加这两条后**新进闭包只有 1 个**（`ConeLines`；`SweepLines`/`ConeRegion` 本已在内）。
import Nivat.External.Colle.ConeLines
import Nivat.External.Colle.SweepLines

/-! # Tower construction from b3_colle2.txt:808

原文：b3_colle2.txt:806-820

Collé's proof of Proposition 4.4 constructs a finite tower
`𝓡_{ι−1} ⊂ 𝓡_{ι−2} ⊂ ⋯ ⊂ 𝓡_{ι−m+1}` (`:812`; the index range is `ι−m+1 ≤ i ≤ ι−2`, `:806`,
so it does **not** reach `0`) where each step sweeps by a generator direction:
`𝓡_i := {g + t·v⃗_{ℓ_i} : g ∈ 𝓡_{i+1}, t ∈ ℤ₊}` (`:808` 逐字).
⚠ 2026-09-24（第 195 轮）：本段原先写成 `𝓡_{i−1} := {g + t·v⃗_{ℓ_i} : g ∈ 𝓡_i, …}`，
把方向下标配给了**源**层；`:808` 把它配给**目标**层，同文件 `tower` 的 docstring 转写一直是对的。
纯 docstring 债，代码未受影响。
This file provides the ℕ-indexed tower definition and its basic properties.

## Main declarations

- `tower R₀ w n`: the n-th level of the tower, where `R₀` is the seed and `w : ℕ → ℤ × ℤ` supplies
  the sweep directions (`w i` is used to build level `i+1` from level `i`)
- `tower_subset_succ`: each level embeds into the next (`⊆`, not strict `⊂`)
- `tower_monotone`: the tower is monotone in the level index
- `isRegion_tower`: if `R₀` is a `(u, u')`-region and each `w i` is `Primitive` with the right
  `LevelInterval` condition, then every level is a `(u, u')`-region

⚠ Note: `tower_subset_succ` gives `⊆`, **not** the strict `⊂` that `RegionFamily.grow` demands.
Whether Collé's finite chain meets `grow` at all is an open question dispatched separately.
-/

namespace Nivat.ColleReg

open Nivat.RegionSweep Nivat.Colle41

/-- **Tower construction from `:808`.**

原文：b3_colle2.txt:808

`𝓡_i := {g + t·v⃗_{ℓ_i} : g ∈ 𝓡_{i+1}, t ∈ ℤ₊}`, indexed as an ℕ-iteration where `tower R₀ w 0 = R₀`
and `tower R₀ w (n+1) = sweep (tower R₀ w n) (w n)`. The direction sequence `w : ℕ → ℤ × ℤ`
corresponds to the generators `v⃗_{ℓ_0}, v⃗_{ℓ_1}, …` from the paper.

Note: Collé's indexing counts **down** (`𝓡_I, 𝓡_{I−1}, …, 𝓡_0`), whereas this definition counts
**up** (`tower R₀ w 0, tower R₀ w 1, …`). The seed `R₀` corresponds to Collé's `𝓡_I`. -/
noncomputable def tower (R₀ : Set (ℤ × ℤ)) (w : ℕ → ℤ × ℤ) : ℕ → Set (ℤ × ℤ)
  | 0     => R₀
  | n + 1 => sweep (tower R₀ w n) (w n)

/-- **Subset monotonicity: `tower R₀ w n ⊆ tower R₀ w (n+1)`.**

原文：b3_colle2.txt:808

From `RegionSweep.subset_sweep`, which takes `t = 0` in the sweep definition. This gives `⊆`,
**not** the strict `⊂` that `RegionFamily.grow` demands — whether the finite chain is strictly
ascending is an open question. -/
theorem tower_subset_succ (R₀ : Set (ℤ × ℤ)) (w : ℕ → ℤ × ℤ) (n : ℕ) :
    tower R₀ w n ⊆ tower R₀ w (n + 1) := by
  simp only [tower]
  exact subset_sweep (tower R₀ w n) (w n)

/-- **The tower is monotone in the level index.**

原文：b3_colle2.txt:808

Immediate from `tower_subset_succ` by transitivity. -/
theorem tower_monotone (R₀ : Set (ℤ × ℤ)) (w : ℕ → ℤ × ℤ) : Monotone (tower R₀ w) := by
  intro m n hmn
  induction hmn with
  | refl => rfl
  | step hmk ih => exact Set.Subset.trans ih (tower_subset_succ R₀ w _)

/-- **Region stability: if `R₀` is a `(u, u')`-region and each `w i` satisfies `Primitive` and
`LevelInterval` conditions, then every tower level is a `(u, u')`-region.**

原文：b3_colle2.txt:808, :796

The paper's `𝓡_{ι−1}` at `:796` is stated to be a `(−ℓ, ℓ_{ι−1})`-region (two edge directions),
implying that sweeping by a generator preserves the region structure. This follows from
`RegionSweep.isRegion_sweep`, which requires `Primitive w` and `LevelInterval C w` for each sweep.

The hypotheses `hw` and `hlev` provide these conditions for all levels. -/
theorem isRegion_tower {R₀ : Set (ℤ × ℤ)} {u u' : ℤ × ℤ} {w : ℕ → ℤ × ℤ}
    (hR₀ : IsRegion R₀ u u')
    (hw : ∀ i, Primitive (w i))
    (hlev : ∀ i, LevelInterval (tower R₀ w i) (w i)) :
    ∀ n, IsRegion (tower R₀ w n) u u' := by
  intro n
  induction n with
  | zero => simp only [tower]; exact hR₀
  | succ k ih =>
      simp only [tower]
      exact isRegion_sweep ih (hw k) (hlev k)

/-- **Each layer is `ℤ·vl`-closed.**

Layer `t` is `B + ℤ·vl + t·u₂`, so translating by any `k • vl` stays inside the *same* layer.
This is the whole content of the line-by-line induction at `b3_colle2.txt:795-802`: the rows
are never compared, because the period direction never leaves a row.

原文：b3_colle2.txt:795-802 -/
theorem zsmul_vl_mem_layer {B : Set (ℤ × ℤ)} {vl u₂ : ℤ × ℤ} {t : ℕ} {z : ℤ × ℤ} (k : ℤ)
    (hz : z ∈ {w | ∃ g ∈ Nivat.ColleReg.fullSweep B vl, w = g + (t : ℤ) • u₂}) :
    z + k • vl ∈ {w | ∃ g ∈ Nivat.ColleReg.fullSweep B vl, w = g + (t : ℤ) • u₂} := by
  obtain ⟨g, hg, rfl⟩ := hz
  obtain ⟨b, hb, j, rfl⟩ := Nivat.ColleReg.mem_fullSweep_iff.mp hg
  refine ⟨b + (j + k) • vl, Nivat.ColleReg.mem_fullSweep_iff.mpr ⟨b, hb, j + k, rfl⟩, ?_⟩
  rw [add_smul]
  abel

/-- **Layer decomposition: periodicity on the union from periodicity on each layer.**

原文：b3_colle2.txt:795-802, :808

The paper's construction at `:795-802` proceeds by **line-by-line** induction `A_1, A_2, …`,
one row at a time, with no reordering within rows. The stage-2 sweep at `:808` is
`𝓡_i := {g + t·v⃗_{ℓ_i} : g ∈ 𝓡_{i+1}, t ∈ ℤ₊}`, a pure ℕ-sweep where the layer index `t`
corresponds to the paper's row index.

**Per-quantifier correspondence:**
- `∀ t : ℕ` — each row (`:795-802`)
- layer `t` is `{z | ∃ g ∈ fullSweep B vl, z = g + (t : ℤ) • u₂}` — the t-th row
- `PeriodOn x (layer t) (k • vl)` — periodicity on that layer (`:804` Claim 4.6, row by row)
- `k` — the `c` of `c • vl`, the period multiple supplied by Claim 4.6 at `:804`
- Conclusion: `PeriodOn x (wedgeFull B vl u₂) (k • vl)` — periodicity on the union (`:808`)

⚠ **The layers are deliberately *not* claimed to be nested — they are not.**  An earlier
attempt here tried to route through `periodOn_iUnion_of_monotone` and stalled, because
layer `a ⊆ layer b` would force `c - (b-a) • u₂ ∈ B`, which is false in general.  Nesting is
not what makes the induction run, and it is not what `:795-802` asserts.

What makes it run is that **the period direction lies inside each row**: every layer is
`B + ℤ·vl + t·u₂`, hence closed under `+ k • vl` (`zsmul_vl_mem_layer`), and the period on
this whole chain is `c • vl` (`RegionSteps.lean:1305, :1360, :1518`).  So `z` and `z + k • vl`
are always in the *same* layer and the rows are never compared.  That is exactly why the
paper's induction at `:795-802` is line-by-line with no ordering inside a line.

⚠ A generic period `h : ℤ × ℤ` makes this statement unprovable (and is our invention, not
Collé's): with generic `h` the two points may land in different rows, where no hypothesis
applies.  The `k • vl` shape is forced by the source. -/
theorem periodOn_wedgeFull_of_layers {A : Type*} {x : Nivat.Config A}
    {B : Set (ℤ × ℤ)} {vl u₂ : ℤ × ℤ} {k : ℤ}
    (hlayer : ∀ t : ℕ, Nivat.Colle41.PeriodOn x
        {z | ∃ g ∈ Nivat.ColleReg.fullSweep B vl, z = g + (t : ℤ) • u₂} (k • vl)) :
    Nivat.Colle41.PeriodOn x (Nivat.ColleReg.wedgeFull B vl u₂) (k • vl) := by
  intro z hz _
  have hz' : ∃ g ∈ Nivat.ColleReg.fullSweep B vl, ∃ t : ℕ, z = g + (t : ℤ) • u₂ := hz
  obtain ⟨g, hg, t, rfl⟩ := hz'
  have hmem : g + (t : ℤ) • u₂ ∈
      {w | ∃ gg ∈ Nivat.ColleReg.fullSweep B vl, w = gg + (t : ℤ) • u₂} := ⟨g, hg, rfl⟩
  exact hlayer t _ hmem (zsmul_vl_mem_layer k hmem)

#print axioms tower_subset_succ
#print axioms tower_monotone
#print axioms isRegion_tower
#print axioms zsmul_vl_mem_layer
#print axioms periodOn_wedgeFull_of_layers

/-! ## §3  撤回 (2026-09-21, 集成者): `exists_stage2_period_of_coneRegion_negated` 整条删除

Hindex lane 于本轮落地了一条带 `sorry` 的 `exists_stage2_period_of_coneRegion_negated`
＋ 一段「符号诊断」，理由是原文 `:786 / :806` 把 `𝓡` 叫作 `(-ℓ, ℓ_{ι-1})`-region，
因而我们的 `coneRegion B vl u'`（`+vl` 扫）方向写反了。**两点都不成立，整块已删。**

1. **`sorry` 越红线**：agent 不许把 `sorry` 落进主仓，一条也不行。本文件五条原声明全部内核
   干净，那条 `sorry` 会把 `TowerBuild` 拖红并经 `Stage2Index` 传到主链上。

2. **符号诊断与原文相反，而且它引用的正是反驳它自己的那句。** 原文逐字：
   - `:414` `H_B(ℓ) := {g + t·v⃗_ℓ ∈ ℤ² : g ∈ B, t ∈ ℤ₊}`
   - `:784` `𝓡_{ι−1} := {g + t·v⃗_{ℓ_{ι−1}} ∈ ℤ² : g ∈ H_B(ℓ), t ∈ ℤ₊}`
   **两次扫掠都是 `ℤ₊`（前向）。** 所以 `𝓡_{ι−1} = B + ℕ·v⃗_ℓ + ℕ·v⃗_{ℓ_{ι−1}}`，
   与 `ConeRegion.coneRegion B vl u' = sweep (sweep B vl) u'`（`ConeRegion.lean:68`）逐字一致。

   `(-ℓ, ℓ_{ι−1})`-region 里的 `-ℓ` 是**区域类型的命名**（按界定它的两条半平面方向命名，
   `:786` 与 Figure 10 说的是 `E(𝓡_{ι−1})` 里那条**平行 `-ℓ` 的边**），不是扫掠方向。
   被删的那段 docstring 自己写着 "`H_B(𝐥)` sweeps `B` in the `+𝐥` direction … indicating the
   first **edge direction** (not sweep direction) is `-𝐥`"——**承认了扫掠是 `+ℓ`，却仍去否定 `vl`**。

**教训（硬规矩 10 的一个实例）**：区域的**命名**（按边方向）与区域的**构造**（按扫掠方向）
是两件事，原文同一句话里两者都出现。判断方向必须回到带 `ℤ₊` 的那个构造式，不能靠类型标签。

**这条债的真名没有变**，仍是 `RegionSteps.lean:1486-1488` 自己写明的那条：`chainFull` 内层
走 `fullSweep`（双向 `ℤ·vl`）而 `coneRegion` 只有 `ℕ·vl`，**过扫**使包含关系不成立、
`PeriodOn.mono` 的反变方向用不上。与符号无关。 -/

/-! ## §4  The bridge from Claim 4.6 to stage-2 periodicity

原文：b3_colle2.txt:784-804 (Claim 4.6)

Claim 4.6 concludes that `(T^u η)|𝓡_{ι-1}` is periodic of period parallel to `ℓ`.  In our
encoding that is `PeriodOn (T e ξ) (coneRegion B vl u') (c • vl)`, where `coneRegion B vl u'`
is exactly the paper's `𝓡_{ι-1} = {g + t·v⃗_{ℓ_{ι-1}} : g ∈ H_B(ℓ), t ∈ ℤ₊}` at `:784`.

The sweep-lines engine is `Nivat.SweepLines.periodOn_of_lines_sweep` (`SweepLines.lean:138`).
Its hypothesis `hKL : K ⊆ D ∪ (⋃ i, lines i)` is discharged by
`Nivat.ConeLines.coneRegion_subset_halfStrip_union_lines` (`ConeLines.lean:289`), which proves
exactly that covering for the paper's forward-only `𝓡_{ι-1}`.

⚠ **Not the `chainFull` version.** `chainFull` walks `fullSweep` (bidirectional `ℤ·vl`) and
does **not** satisfy the covering; `ConeHbase.not_chainFull_subset_halfStrip_union_lines` refutes
it with a kernel counterexample.  The paper's object is `coneRegion`, not `chainFull`. -/

/-- **Periodicity on `coneRegion B vl u'` from the line-by-line sweep** (`:784-804`).

原文：b3_colle2.txt:784-804

Claim 4.6 at `:804` says: "proceeding this way, we get by induction that
`(T^u(η - η̄_{ι₀}))|𝓡_{ι-1}` and therefore `(T^u η)|𝓡_{ι-1}` is periodic with period parallel
to `ℓ`."  This is the kernel witness for that conclusion.

Quantifiers (per CLAUDE.md hard rule 7):
- `hS : GeneratesAt ξ S a` — `𝒮_{φ_ι}` is an `η - η̄_{ι₀}` generating set (`:792`)
- `ha : a ∈ S` — the puncture point
- `hconv : LatticeConvex (S.erase a)` — the punctured set is convex (generating sets are)
- `hperp : dot nℓ vl = 0` — `nℓ` is the transverse normal; lines `l_i` are parallel to `ℓ` (`:796`)
- `hstep : dot nℓ u' = -1` — one `u'`-step drops exactly one lattice line (`:804` "proceeding")
- `hBlow : ∀ b ∈ B, cz ≤ dot nℓ b` — `B ⊆ ℋ(ℓ_B)` (`:472`, item (i) of Lemma 3.x)
- `hD : ∀ z ∈ halfStrip B vl, T e ξ z = T (c • vl) (T e ξ) z` — periodicity on the half-strip
  `H_B(ℓ)` (`:788`, the starting point for the induction)
- `hwinL` — the window condition, line by line (`:792-804`, `A₁, A₂, …` induction)
- Conclusion: `PeriodOn (T e ξ) (coneRegion B vl u') (c • vl)` — periodicity on `𝓡_{ι-1}` (`:804`)

**Why `hstepIn` is not listed:** `Nivat.ConeLines.coneRegion_subset_halfStrip_union_lines`
needs `hstepIn : ∀ z ∈ halfStrip B vl, cz ≤ dot nℓ (z + u') → z + u' ∈ halfStrip B vl`
(Figure 10's assertion that the `u'` edge of `𝓡_{ι-1}` continues `B`'s own), but that
hypothesis is **not explicitly given in the signature** because the team-lead instructed me
to prove `hKL` directly. The proof below constructs `hstepIn` from `hwinL`. -/
theorem periodOn_coneRegion_of_lines {ξ : Nivat.Config ℤ} {e : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} {a : ℤ × ℤ} (hS : Nivat.Colle.GeneratesAt ξ S a)
    (ha : a ∈ S) (hconv : Nivat.LatticeConvex (S.erase a))
    {B : Set (ℤ × ℤ)} {vl u' nℓ : ℤ × ℤ} {c cz : ℤ}
    (hperp : Nivat.LE2.dot nℓ vl = 0) (hstep : Nivat.LE2.dot nℓ u' = -1)
    (hBlow : ∀ b ∈ B, cz ≤ Nivat.LE2.dot nℓ b)
    (hstepIn : ∀ z ∈ Nivat.LE2.halfStrip B vl,
      cz ≤ Nivat.LE2.dot nℓ (z + u') → z + u' ∈ Nivat.LE2.halfStrip B vl)
    (hD : ∀ z ∈ Nivat.LE2.halfStrip B vl,
      Nivat.T e ξ z = Nivat.T (c • vl) (Nivat.T e ξ) z)
    (hwinL : ∀ i : ℕ,
      ∀ w ∈ Nivat.ConeRegion.coneRegion B vl u' ∩
        {y | Nivat.LE2.dot nℓ y = cz - 1 - (i : ℤ)},
      ∀ z ∈ S.erase a,
        z + (w - a) ∈ Nivat.LE2.halfStrip B vl ∪
          (⋃ i' ∈ {i' | i' < i}, Nivat.ConeRegion.coneRegion B vl u' ∩
            {y | Nivat.LE2.dot nℓ y = cz - 1 - (i' : ℤ)})) :
    Nivat.Colle41.PeriodOn (Nivat.T e ξ) (Nivat.ConeRegion.coneRegion B vl u') (c • vl) := by
  -- The covering: `coneRegion ⊆ halfStrip ∪ ⋃ lines`
  have hKL : Nivat.ConeRegion.coneRegion B vl u' ⊆
      Nivat.LE2.halfStrip B vl ∪
        ⋃ i : ℕ, (Nivat.ConeRegion.coneRegion B vl u' ∩
          {y | Nivat.LE2.dot nℓ y = cz - 1 - (i : ℤ)}) :=
    Nivat.ConeLines.coneRegion_subset_halfStrip_union_lines hstep hstepIn
  -- Apply the sweep-lines engine
  refine Nivat.SweepLines.periodOn_of_lines_sweep
    (Nivat.HbaseBridge.T_mem_orbitClosure_self ξ e) hS (c • vl) hD
    (fun i => Nivat.ConeRegion.coneRegion B vl u' ∩
      {y | Nivat.LE2.dot nℓ y = cz - 1 - (i : ℤ)}) hwinL hKL

#print axioms periodOn_coneRegion_of_lines

end Nivat.ColleReg
