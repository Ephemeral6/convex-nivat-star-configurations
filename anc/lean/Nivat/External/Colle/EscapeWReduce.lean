/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.ShellSubStrip

/-!
# `escapeW` 去掉 shell：归约到「沿 `w` 走出 `Â_i`、但仍落在 `Â_∞` 里」

集成者，2026-09-23（第 146 轮）。目标 binder 是 `ChainDataGeom.ofPartsExhaustsInter`
（`ChainExhaustInter.lean`）的

```
(escapeW : ∀ (i ε : ℕ), 0 < ε → ∃ g ∈ hatOf A kk vl i, ∃ t : ℕ,
  g + (t : ℤ) • w ∈ MaxEnv.shell (⋃ i, hatOf A kk vl i) vJ1 nJ cJ ε ∧
  g + (t : ℤ) • w ∉ hatOf A kk vl i)
```

## 观察

`MaxEnv.subset_shell`（`MaximalEnveloped.lean:592`）只要 `A ⊆ halfPlaneGE n c` 就给
`A ⊆ shell A v n c ε`，而 `hhp : ∀ i, hatOf A kk vl i ⊆ halfPlaneGE nJ cJ`
（`ChainExhaustInter.lean`）正是这条前提在 `Â_∞ = ⋃ i, Â_i` 上的形式。于是

  `Â_∞ ⊆ MaxEnv.shell Â_∞ vJ1 nJ cJ ε`  对每个 `ε` 成立，

所以只要把 `g + t·w` 落进 `Â_∞` 就够——**`shell`、`vJ1`、`ε`、`0 < ε` 全部退场**。
`escapeW` 因此等价于一条纯粹关于 `hat` 塔的陈述（`escapeW_of_reach_union` 的 `hreach`）：

  `∀ i, ∃ g ∈ Â_i, ∃ t : ℕ, g + t·w ∈ Â_∞ ∧ g + t·w ∉ Â_i`。

注意 `t = 0` 那支自动不可能（`g ∈ Â_i` 与 `g ∉ Â_i` 冲突），所以 `hreach` 实际要的是 `t ≥ 1`；
本文件不把它写进签名，因为原 binder 也没写，多写一个量词就是债（硬规矩 5）。

## 为什么这不是白绕

`tmp/wip/lane-escape-escapeW-refute.lean` 的反例（常值有限族 `Â_j ≡ Â_i`）在归约后一眼可见为假：
`Â_∞ ∖ Â_i = ∅`。所以剩下的全部内容是「塔真的在长」。§4 把这一步也做掉：
只要 `A` 单调（由 `subAB` + `subBA` 给出）且 `⋃ j, A j` 无限（由 `hexh : Exhausts A nℓ cz`
给出，`ItemII.lean:96`），就有 `Â_∞` 无限，于是 `Â_∞ ⊋ Â_i`（`hfin`，`Â_i` 有限）。
缺的只剩「那个跑出去的点坐落在从 `Â_i` 出发的 `w`-射线上」。

平移不改变基数这一步用的是 `A j = (· + k_j·v⃗_ℓ) '' Â_j`（`hatOf_image`），
这正是 `Colle35.hatOf`（`Lemma35.lean`）的定义展开。

## 逐级削减一览（§1 → §3）

| 削减 | 吃掉的量词 / 结论 | 靠的是 |
|---|---|---|
| §1 `escapeW_of_reach_union` | `shell` / `vJ1` / `ε` | `subset_shell` + `hhp` |
| §2 `escapeW_of_eps_one` | `∀ ε, 0 < ε` 钉成 `ε = 1` | `shell_mono_eps` |
| §2 `escapeW_of_vJ1_witness` | `shell` 展成 `mem_shell` 四件数据 | `mem_shell` 是 `Iff.rfl` |
| §3 `escapeW_of_below_cJ` | 第二个结论 `∉ Â_i` | `hhp i` + 高度 `< c_J` |
| §3 `escapeW_of_step_below` | 位移见证 `t₂`、`g₂` 钉成 `t₂ = 1`、`g₂ = z − vJ1` | `hsweep` 抬高一格回到 `c_J` |

§1 与 §2–§3 是**两条互斥的路**：§1 要求逃出点仍在 `Â_∞` 里，而 `hsweepW : dot nJ w < 0` 说明
它多半恰好落在带 `[c_J − 1, c_J)` 里、**不**在 `Â_∞` 里；那时只有 §2–§3 这条路走得通。
`escapeW_of_step_below` 是这条路的终点，剩余义务只有一条纯几何陈述（见其 docstring）。
-/

set_option autoImplicit false

namespace Nivat.EscapeWReduce

open Nivat Nivat.LE2 Nivat.MaxEnv

/-! ### §1. 归约：shell 退场 -/

/-- **`Â_∞ ⊆ ℋ(ℓ_J)`**，由 `hhp` 逐层并起来。 -/
theorem ahatUnion_subset_halfPlaneGE {A : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ} {vl nJ : ℤ × ℤ} {cJ : ℤ}
    (hhp : ∀ i, Nivat.Colle35.hatOf A kk vl i ⊆ halfPlaneGE nJ cJ) :
    (⋃ i, Nivat.Colle35.hatOf A kk vl i) ⊆ halfPlaneGE nJ cJ :=
  Set.iUnion_subset hhp

/-- **`escapeW` 的归约。**把 `MaxEnv.shell` 换成 `Â_∞` 本身，其余逐字不动。
`subset_shell`（`MaximalEnveloped.lean:592`）吃掉 `shell` / `vJ1` / `ε`，
`0 < ε` 这条前提于是完全用不上（保留在签名里只为与目标 binder 逐字对齐）。 -/
theorem escapeW_of_reach_union {A : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ} {vl w vJ1 nJ : ℤ × ℤ} {cJ : ℤ}
    (hhp : ∀ i, Nivat.Colle35.hatOf A kk vl i ⊆ halfPlaneGE nJ cJ)
    (hreach : ∀ i : ℕ, ∃ g ∈ Nivat.Colle35.hatOf A kk vl i, ∃ t : ℕ,
      g + (t : ℤ) • w ∈ (⋃ j, Nivat.Colle35.hatOf A kk vl j) ∧
      g + (t : ℤ) • w ∉ Nivat.Colle35.hatOf A kk vl i) :
    ∀ (i ε : ℕ), 0 < ε → ∃ g ∈ Nivat.Colle35.hatOf A kk vl i, ∃ t : ℕ,
      g + (t : ℤ) • w ∈ MaxEnv.shell (⋃ j, Nivat.Colle35.hatOf A kk vl j) vJ1 nJ cJ ε ∧
      g + (t : ℤ) • w ∉ Nivat.Colle35.hatOf A kk vl i := by
  intro i _ _
  obtain ⟨g, hg, t, hmem, hnot⟩ := hreach i
  exact ⟨g, hg, t, subset_shell _ (ahatUnion_subset_halfPlaneGE hhp) hmem, hnot⟩

/-- 带指标的等价写法：把 `⋃` 换成「某个 `j`」，供下游 lane 直接造见证。 -/
theorem escapeW_of_reach_index {A : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ} {vl w vJ1 nJ : ℤ × ℤ} {cJ : ℤ}
    (hhp : ∀ i, Nivat.Colle35.hatOf A kk vl i ⊆ halfPlaneGE nJ cJ)
    (hreach : ∀ i : ℕ, ∃ g ∈ Nivat.Colle35.hatOf A kk vl i, ∃ t : ℕ, ∃ j : ℕ,
      g + (t : ℤ) • w ∈ Nivat.Colle35.hatOf A kk vl j ∧
      g + (t : ℤ) • w ∉ Nivat.Colle35.hatOf A kk vl i) :
    ∀ (i ε : ℕ), 0 < ε → ∃ g ∈ Nivat.Colle35.hatOf A kk vl i, ∃ t : ℕ,
      g + (t : ℤ) • w ∈ MaxEnv.shell (⋃ j, Nivat.Colle35.hatOf A kk vl j) vJ1 nJ cJ ε ∧
      g + (t : ℤ) • w ∉ Nivat.Colle35.hatOf A kk vl i := by
  refine escapeW_of_reach_union hhp ?_
  intro i
  obtain ⟨g, hg, t, j, hmem, hnot⟩ := hreach i
  exact ⟨g, hg, t, Set.mem_iUnion.mpr ⟨j, hmem⟩, hnot⟩

/-! ### §2. `ε` 退场：只需 `ε = 1` 一层 -/

/-- **`escapeW` 只需在 `ε = 1` 上交。**`0 < ε` 在 ℕ 上就是 `1 ≤ ε`，
`shell_mono_eps`（`MaximalEnveloped.lean` 的 `shell_mono_eps`；§85 按标识符名找，
旧批注写 `:578`，已烂，实际当时在 `:579`）把 `ε = 1` 那层抬到任意 `ε`。
与 §1 的 `escapeW_of_reach_union` 是两条**独立**的削减：这条不假设跑出去的点落在 `Â_∞` 里，
只把 `ε` 的量词钉死；`hsweepW : dot nJ w < 0`（`ChainExhaustInter.lean`）说明沿 `w` 走
`dot nJ` 严格下降，所以逃出点**很可能**恰好落在带 `[c_J − ε, c_J)` 里而**不**在 `Â_∞` 里，
那时 §1 的 `hreach` 交不出来而本条仍然可用。 -/
theorem escapeW_of_eps_one {A : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ} {vl w vJ1 nJ : ℤ × ℤ} {cJ : ℤ}
    (h1 : ∀ i : ℕ, ∃ g ∈ Nivat.Colle35.hatOf A kk vl i, ∃ t : ℕ,
      g + (t : ℤ) • w ∈ MaxEnv.shell (⋃ j, Nivat.Colle35.hatOf A kk vl j) vJ1 nJ cJ 1 ∧
      g + (t : ℤ) • w ∉ Nivat.Colle35.hatOf A kk vl i) :
    ∀ (i ε : ℕ), 0 < ε → ∃ g ∈ Nivat.Colle35.hatOf A kk vl i, ∃ t : ℕ,
      g + (t : ℤ) • w ∈ MaxEnv.shell (⋃ j, Nivat.Colle35.hatOf A kk vl j) vJ1 nJ cJ ε ∧
      g + (t : ℤ) • w ∉ Nivat.Colle35.hatOf A kk vl i := by
  intro i ε hε
  obtain ⟨g, hg, t, hmem, hnot⟩ := h1 i
  exact ⟨g, hg, t, shell_mono_eps hε hmem, hnot⟩

/-- **`escapeW` 的字面靶子，`shell` 拆成 `mem_shell`（`MaximalEnveloped.lean:567`）的四件数据，
`ε` 已钉成 1。**这是下游 lane 真正要交的东西，逐字不作概括。 -/
theorem escapeW_of_vJ1_witness {A : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ} {vl w vJ1 nJ : ℤ × ℤ} {cJ : ℤ}
    (hreach : ∀ i : ℕ, ∃ g ∈ Nivat.Colle35.hatOf A kk vl i, ∃ t : ℕ,
      ∃ g₂ ∈ (⋃ j, Nivat.Colle35.hatOf A kk vl j), ∃ t₂ : ℕ,
        g + (t : ℤ) • w = g₂ + (t₂ : ℤ) • vJ1 ∧
        cJ - 1 ≤ dot nJ (g + (t : ℤ) • w) ∧
        g + (t : ℤ) • w ∉ Nivat.Colle35.hatOf A kk vl i) :
    ∀ (i ε : ℕ), 0 < ε → ∃ g ∈ Nivat.Colle35.hatOf A kk vl i, ∃ t : ℕ,
      g + (t : ℤ) • w ∈ MaxEnv.shell (⋃ j, Nivat.Colle35.hatOf A kk vl j) vJ1 nJ cJ ε ∧
      g + (t : ℤ) • w ∉ Nivat.Colle35.hatOf A kk vl i := by
  refine escapeW_of_eps_one ?_
  intro i
  obtain ⟨g, hg, t, g₂, hg₂, t₂, heq, hlev, hnot⟩ := hreach i
  exact ⟨g, hg, t, ⟨g₂, hg₂, t₂, heq, by simpa using hlev⟩, hnot⟩

/-! ### §3. `∉ Â_i` 也退场：只要落到 `ℓ_J` 底下 -/

/-- **`escapeW` 的「跑到 `ℓ_J` 底下」版。**
`hhp`（`ChainExhaustInter.lean`）说 `Â_i ⊆ ℋ(ℓ_J) = {c_J ≤ ⟪n_J,·⟫}`，所以只要
`⟪n_J, g + t·w⟫ < c_J`，`g + t·w ∉ Â_i` **自动成立**——不用再单独造。
于是 `escapeW` 三个结论合取里的第二个整个退场，剩下的全是 `n_J` 方向上的高度算术。 -/
theorem escapeW_of_below_cJ {A : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ} {vl w vJ1 nJ : ℤ × ℤ} {cJ : ℤ}
    (hhp : ∀ i, Nivat.Colle35.hatOf A kk vl i ⊆ halfPlaneGE nJ cJ)
    (hreach : ∀ i : ℕ, ∃ g ∈ Nivat.Colle35.hatOf A kk vl i, ∃ t : ℕ,
      cJ - 1 ≤ dot nJ (g + (t : ℤ) • w) ∧ dot nJ (g + (t : ℤ) • w) < cJ ∧
      ∃ g₂ ∈ (⋃ j, Nivat.Colle35.hatOf A kk vl j), ∃ t₂ : ℕ,
        g + (t : ℤ) • w = g₂ + (t₂ : ℤ) • vJ1) :
    ∀ (i ε : ℕ), 0 < ε → ∃ g ∈ Nivat.Colle35.hatOf A kk vl i, ∃ t : ℕ,
      g + (t : ℤ) • w ∈ MaxEnv.shell (⋃ j, Nivat.Colle35.hatOf A kk vl j) vJ1 nJ cJ ε ∧
      g + (t : ℤ) • w ∉ Nivat.Colle35.hatOf A kk vl i := by
  refine escapeW_of_vJ1_witness ?_
  intro i
  obtain ⟨g, hg, t, hge, hlt, g₂, hg₂, t₂, heq⟩ := hreach i
  refine ⟨g, hg, t, g₂, hg₂, t₂, heq, hge, ?_⟩
  intro hmem
  have := hhp i hmem
  simp only [halfPlaneGE, Set.mem_ofPred_eq] at this
  omega

/-- **一步 `v⃗_{ℓ_{J−1}}` 就够。**`hsweep : dot nJ vJ1 < 0`（`ChainExhaustInter.lean`）说沿
`vJ1` 走高度严格下降，所以 `z := g + t·w` 落在带 `[c_J − 1, c_J)` 里时，
`z − vJ1` 的高度 `= ⟪n_J,z⟫ + (−⟪n_J,vJ1⟫) ≥ c_J − 1 + 1 = c_J`——正好回到 `Â_∞` 该在的那一侧。
于是 `mem_shell` 的位移见证可以一律取 `t₂ = 1`、`g₂ = z − vJ1`，`shell` 里除了
「`z − vJ1` 确实落在 `Â_∞` 里」之外的一切都已消掉。

**这就是 `escapeW` 的最小剩余义务**：对每个 `i`，找一个 `g ∈ Â_i` 与步数 `t`，使
`g + t·w` 掉到 `ℓ_J` 下面但不超过一格，且抬回去一步仍在 `Â_∞` 里。 -/
theorem escapeW_of_step_below {A : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ} {vl w vJ1 nJ : ℤ × ℤ} {cJ : ℤ}
    (hhp : ∀ i, Nivat.Colle35.hatOf A kk vl i ⊆ halfPlaneGE nJ cJ)
    (hreach : ∀ i : ℕ, ∃ g ∈ Nivat.Colle35.hatOf A kk vl i, ∃ t : ℕ,
      cJ - 1 ≤ dot nJ (g + (t : ℤ) • w) ∧ dot nJ (g + (t : ℤ) • w) < cJ ∧
      g + (t : ℤ) • w - vJ1 ∈ (⋃ j, Nivat.Colle35.hatOf A kk vl j)) :
    ∀ (i ε : ℕ), 0 < ε → ∃ g ∈ Nivat.Colle35.hatOf A kk vl i, ∃ t : ℕ,
      g + (t : ℤ) • w ∈ MaxEnv.shell (⋃ j, Nivat.Colle35.hatOf A kk vl j) vJ1 nJ cJ ε ∧
      g + (t : ℤ) • w ∉ Nivat.Colle35.hatOf A kk vl i := by
  refine escapeW_of_below_cJ hhp ?_
  intro i
  obtain ⟨g, hg, t, hge, hlt, hsub⟩ := hreach i
  refine ⟨g, hg, t, hge, hlt, g + (t : ℤ) • w - vJ1, hsub, 1, ?_⟩
  push_cast
  abel

/-! ### §4. 塔确实在长：`Â_∞` 无限，于是 `Â_∞ ⊄ Â_i` -/

/-- `A j` 是 `Â_j` 沿 `k_j·v⃗_ℓ` 的平移像。直接展开 `Colle35.hatOf` 的定义。 -/
theorem hatOf_image {A : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ} {vl : ℤ × ℤ} (j : ℕ) :
    (fun z => z + (kk j : ℤ) • vl) '' (Nivat.Colle35.hatOf A kk vl j) = A j := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hz
    refine ⟨z - (kk j : ℤ) • vl, ?_, by simp⟩
    show z - (kk j : ℤ) • vl + (kk j : ℤ) • vl ∈ A j
    simpa using hz

/-- 平移不改变基数：`(A j).ncard = (Â_j).ncard`。 -/
theorem ncard_eq {A : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ} {vl : ℤ × ℤ} (j : ℕ) :
    (A j).ncard = (Nivat.Colle35.hatOf A kk vl j).ncard := by
  rw [← hatOf_image (A := A) (kk := kk) (vl := vl) j]
  exact Set.ncard_image_of_injective _ (fun a b h => by
    simpa using add_right_cancel h)

/-- **`Â_∞` 无限。**
`A` 单调（顶层由 `subAB` + `subBA` 给出）且 `⋃ j, A j` 无限（顶层由 `hexh` 给出）时，
`Â_∞ = ⋃ j, Â_j` 不可能有限：否则每层 `Â_j ⊆ Â_∞` 都被同一个基数 `N` 卡住，
平移回去 `A j` 也被 `N` 卡住，而单调族的无限并里任取 `N+1` 个点落在同一层 `A J` 上，矛盾。 -/
theorem ahatUnion_infinite {A : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ} {vl : ℤ × ℤ}
    (hAmono : ∀ j, A j ⊆ A (j + 1)) (hinfA : (⋃ j, A j).Infinite) :
    (⋃ j, Nivat.Colle35.hatOf A kk vl j).Infinite := by
  classical
  intro hfin
  set N : ℕ := (⋃ j, Nivat.Colle35.hatOf A kk vl j).ncard with hN
  have hmono' : ∀ a b : ℕ, a ≤ b → A a ⊆ A b := by
    have hm : Monotone A := monotone_nat_of_le_succ hAmono
    exact fun a b hab => hm hab
  -- 每层 `A j` 有限且基数 `≤ N`
  have hhatfin : ∀ j, (Nivat.Colle35.hatOf A kk vl j).Finite := fun j =>
    hfin.subset (Set.subset_iUnion _ j)
  have hAfin : ∀ j, (A j).Finite := by
    intro j
    rw [← hatOf_image (A := A) (kk := kk) (vl := vl) j]
    exact (hhatfin j).image _
  have hAcard : ∀ j, (A j).ncard ≤ N := by
    intro j
    rw [ncard_eq (A := A) (kk := kk) (vl := vl) j, hN]
    exact Set.ncard_le_ncard (Set.subset_iUnion _ j) hfin
  -- 无限并里取 `N+1` 个点，落在同一层
  obtain ⟨t, hts, htc⟩ := hinfA.exists_subset_card_eq (N + 1)
  have hall : ∀ x ∈ t, ∃ j, x ∈ A j := fun x hx => Set.mem_iUnion.mp (hts hx)
  choose! g hg using hall
  set J : ℕ := t.sup g with hJ
  have hsub : (↑t : Set (ℤ × ℤ)) ⊆ A J := by
    intro x hx
    have hxt : x ∈ t := hx
    exact hmono' (g x) J (Finset.le_sup hxt) (hg x hxt)
  have hle : (↑t : Set (ℤ × ℤ)).ncard ≤ (A J).ncard := Set.ncard_le_ncard hsub (hAfin J)
  rw [Set.ncard_coe_finset, htc] at hle
  exact absurd (le_trans hle (hAcard J)) (by omega)

/-- **`Â_∞ ⊄ Â_i`**：`Â_i` 有限而 `Â_∞` 无限。这正是常值族反例
（`tmp/wip/lane-escape-escapeW-refute.lean`）被排除的地方。 -/
theorem exists_mem_ahatUnion_not_mem {A : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ} {vl : ℤ × ℤ} {i : ℕ}
    (hfin : (Nivat.Colle35.hatOf A kk vl i).Finite)
    (hinf : (⋃ j, Nivat.Colle35.hatOf A kk vl j).Infinite) :
    ∃ z ∈ ⋃ j, Nivat.Colle35.hatOf A kk vl j, z ∉ Nivat.Colle35.hatOf A kk vl i := by
  by_contra hcon
  push Not at hcon
  exact hinf (hfin.subset hcon)

end Nivat.EscapeWReduce

#print axioms Nivat.EscapeWReduce.ahatUnion_subset_halfPlaneGE
#print axioms Nivat.EscapeWReduce.escapeW_of_reach_union
#print axioms Nivat.EscapeWReduce.escapeW_of_reach_index
#print axioms Nivat.EscapeWReduce.escapeW_of_eps_one
#print axioms Nivat.EscapeWReduce.escapeW_of_vJ1_witness
#print axioms Nivat.EscapeWReduce.escapeW_of_below_cJ
#print axioms Nivat.EscapeWReduce.escapeW_of_step_below
#print axioms Nivat.EscapeWReduce.hatOf_image
#print axioms Nivat.EscapeWReduce.ncard_eq
#print axioms Nivat.EscapeWReduce.ahatUnion_infinite
#print axioms Nivat.EscapeWReduce.exists_mem_ahatUnion_not_mem
