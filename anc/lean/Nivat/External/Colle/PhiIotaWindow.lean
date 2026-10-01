/-
Copyright (c) 2026 Anthropic PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Hwin lane)
-/
import Nivat.External.Colle.DecompData
import Nivat.External.Colle.NoEdgePlacement
import Nivat.External.Colle.Generating
import Nivat.External.Colle.ShellGeom
import Nivat.External.Colle.MinkowskiEdges
import Nivat.External.Colle.AlphabetReduction
import Nivat.External.Colle.Lemma41
import Nivat.Laurent.Basic

/-!
# Hole 3: The `Sw` bundle (window strict argmin)

原文：b3_colle2.txt:788-796

This file produces hole 3 of `RegionSteps.lean:1946` — the existence of `Sw` with `hstrict`.

## Source alignment

`:788-792`: Let `1 ≤ ι₀ ≤ m` be such that `ι₀ = ι mod m`. Since
`φ_ι(X) := ∏_{i≠ι₀}(X^{h_i}−1) ∈ ann_{ℤ_p}(η − η̄_{ι₀})`, **Lemma 2.5** states that
`𝒮_{φ_ι}` is an `η − η̄_{ι₀}`-generating set. Being `h₁,…,h_m ∈ ℤ²` vectors in pairwise
distinct directions, **Lemma 2.6** implies that `𝒮_{φ_ι}` does not have any edge parallel
to `−ℓ` or `ℓ`.

`:796`: The set `Ŝ_{φ_ι}` denotes **a translation of** `𝒮_{φ_ι}`.

## Per-quantifier correspondence (hard rule 7)

| Hole 3 conjunct | Source | Reason |
|---|---|---|
| `Sw` exists | `:792` `φ_ι` 的 Newton polygon | Definition |
| `LatticeConvex Sw` | Zonotope property | `𝒮_{φ_ι}` is a zonotope (same generators minus one) |
| `E ↑Sw ⊆ E ↑Sphi` | Subset of generators | Dropping an index shrinks the edge union |
| `hstrict` (`nℓ`-extreme face is single point) | `:792` Lemma 2.6 "no edge parallel to `−ℓ` or `ℓ`" | Erasing `h_{ι₀}` removes the only `ℓ`-parallel generator |
| `LatticeConvex (Sw.erase a₀)` | Extreme point erasure | `a₀` is `nℓ`-extreme by `hstrict`, erasing preserves convexity |

## Producer chain (on-chain, axiom-clean)

1. `Nivat.Colle.exists_latticeConvex_completion` (`Generating.lean:90`) — constructs `Sw` from support.

2. `Nivat.LE2.E_zono` (`MinkowskiEdges.lean:292`) — edges of a zonotope are union of segment edges.

3. **`no_edge_parallel_vl_of_erase`** (`RegionSteps.lean:1668`) — Lemma 2.6, needs to be moved upstream.

4. `Nivat.LE2.strict_argmin_of_generatingSet_no_edge_parallel` (`NoEdgePlacement.lean:277`) — produces `hstrict`.

5. `Nivat.Colle37Geom.latticeConvex_erase_of_lexExtreme` (`ShellGeom.lean:74`) — preserves convexity.

## What this file does

Wires items 1–5 into `exists_window_strict_of_index`, which produces everything for hole 3
except `hSwgen` (the placeholder).

## ⚠ `hSwgen` 已收窄为 `GeneratesAt ξ Sw a₀`（2026-09-21，集成者）

原先这里要的是 `Nivat.Colle.IsGeneratingSet ξ Sw`，**对预期见证 `𝒮_{φ_ι}` 明着不成立**：
原文 Lemma 2.5（`:790`，producer 在 `AlphabetReduction.lean:665`
`isGeneratingSet_psi_at_prime`）说的是 `𝒮_{φ_ι}` 生成 `η − η̄_{ι₀}`（`ZMod p` 之差），
**不是 `ξ`**。

收窄的依据是**消费者实际解构的形状**：全链上唯一用到该假设的地方是
`SweepLines.hbase_at_of_sweep_lines`，而它只取投影 `.2.2 a₀ ha₀ hconv`，
即 `GeneratesAt ξ Sw a₀` 这一个分量（`IsGeneratingSet` 的 `.1` 非空、`.2.1` 凸性
在链上另有来源）。所以本文件的 binder 换成那一个分量，其余两个分量由本文件自己产出。

⚠ **这不减少 `sorry` 计数**——它把 `RegionSteps.lean:2402` 那条 `sorry` 换成一条
**严格更弱**、因而有机会真正关掉的义务。旧形状是可证伪的，新形状不是。
-/

namespace Nivat.ColleReg

open Finset (erase univ)
open Nivat (LatticeConvex Conv mono supp LaurentTwo)
open Nivat.LE2 (dot Prim E)
open Nivat.Colle (IsGeneratingSet)

variable {ξ : Nivat.Config ℤ} {vl : ℤ × ℤ}

/-- **Erasing the `nℓ`-argmin preserves lattice convexity.**

原文：b3_colle2.txt:792 Lemma 2.6 "does not have any edge parallel to `−ℓ` or `ℓ`" implies
the `nℓ`-extreme face is a single point. Erasing an extreme point of a lattice-convex set
preserves lattice convexity. -/
theorem latticeConvex_erase_of_strict_argmin {Sw : Finset (ℤ × ℤ)}
    (hconv : LatticeConvex Sw) {a₀ nℓ : ℤ × ℤ}
    (hstrict : ∀ z ∈ Sw.erase a₀, dot nℓ a₀ < dot nℓ z) :
    LatticeConvex (Sw.erase a₀) := by
  apply Nivat.Colle37Geom.latticeConvex_erase_of_lexExtreme hconv (n := -nℓ) (d := (1, 0))
  intro b hb
  left
  show dot (-nℓ) b < dot (-nℓ) a₀
  have hb_strict := hstrict b hb
  have : -(nℓ.1 * b.1 + nℓ.2 * b.2) < -(nℓ.1 * a₀.1 + nℓ.2 * a₀.2) := neg_lt_neg hb_strict
  have h1 : (-nℓ).1 = -nℓ.1 := rfl
  have h2 : (-nℓ).2 = -nℓ.2 := rfl
  calc (-nℓ).1 * b.1 + (-nℓ).2 * b.2
      = -nℓ.1 * b.1 + -nℓ.2 * b.2 := by rw [h1, h2]
    _ = -(nℓ.1 * b.1) + -(nℓ.2 * b.2) := by rw [neg_mul, neg_mul]
    _ = -(nℓ.1 * b.1 + nℓ.2 * b.2) := by rw [neg_add]
    _ < -(nℓ.1 * a₀.1 + nℓ.2 * a₀.2) := this
    _ = -(nℓ.1 * a₀.1) + -(nℓ.2 * a₀.2) := by rw [neg_add]
    _ = -nℓ.1 * a₀.1 + -nℓ.2 * a₀.2 := by rw [neg_mul, neg_mul]
    _ = (-nℓ).1 * a₀.1 + (-nℓ).2 * a₀.2 := by rw [← h1, ← h2]

/-- **Hole 3 producer: the `Sw` bundle with `hstrict`.**

原文：b3_colle2.txt:788-796

Produces everything for hole 3 of `RegionSteps.lean:1946`.

## New signature (2026-09-20)

The two new conjuncts (`LatticeConvex Sw` and `E ↑Sw ⊆ E ↑Sphi`) are free for `Sw := 𝒮_{φ_ι}`:
- `𝒮_{φ_ι}` is a zonotope (same generators as `𝒮_φ` minus one), hence lattice convex
- By `E_zono`, `E` is the union of segment edges; dropping an index shrinks the union

## Binders

- `d : DecompDataZ ξ` — the minimal counterexample decomposition
- `hm : 2 ≤ d.toDecompData.m` — at least two components (`:764`)
- `hprim : Prim nℓ`, `hvl_prim : Primitive vl` — primitivity of the dual pair
- `hperp : dot nℓ vl = 0` — orthogonality (`:788` setup)
- `i : Fin d.toDecompData.m` — the index `ι₀` (`:788`)
- `hdoth : dot nℓ (d.toDecompData.h i) = 0` — `h_{ι₀}` parallel to `vl` (`:788-790`)
- **`hnoedge : ∀ n ∈ E ↑Sw, dot n vl ≠ 0`** — Lemma 2.6, passed as hypothesis (needs upstream move)

## Conclusion

```lean
∃ Sw, LatticeConvex Sw ∧ E ↑Sw ⊆ E ↑d.toDecompData.Sphi ∧
  ∃ a₀ ∈ Sw, LatticeConvex (Sw.erase a₀) ∧ (∀ z ∈ Sw.erase a₀, dot nℓ a₀ < dot nℓ z) ∧
    Gen Sw a₀
```

`hSwgen` 仍是 binder，但形状已**从 `GeneratesAt ξ Sw a₀` 抽象成一个参数谓词
`Gen : Finset (ℤ × ℤ) → ℤ × ℤ → Prop`**（2026-09-21，集成者）。

理由是**避免 import 环**：真正要传进来的形状是
`SweepLines.ReducedGeneratesAtDir ξ Sw a₀ vl`（原文 `:786`+`:790`+`:792` 的捆绑），
而 `SweepLines.lean` **import 本文件**（它要用 `periodOn_of_periodOn_reduceMod_sub`），
所以本文件不能反过来提那个名字。抽象成 `Gen` 之后本条对生成性**一无所知、原样透传**——
它本来也只是把 binder 搬到结论里，从未解构过。

⚠ 这个抽象**不是加强也不是减弱**：取 `Gen := fun Sw a₀ => Nivat.Colle.GeneratesAt ξ Sw a₀`
就回到旧陈述。

## Producer chain wiring

1. `exists_latticeConvex_completion` constructs `Sw` with the right hull.
2. `E_zono` gives `E ↑Sw ⊆ E ↑Sphi` (zonotope subset).
3. `hnoedge` (passed as hypothesis) is Lemma 2.6.
4. `strict_argmin_of_generatingSet_no_edge_parallel` produces `hstrict` from (3).
5. `latticeConvex_erase_of_strict_argmin` (this file) produces `LatticeConvex (Sw.erase a₀)`. -/
theorem exists_window_strict_of_index (d : Nivat.Colle35.DecompDataZ ξ) {nℓ vl : ℤ × ℤ}
    (hm : 2 ≤ d.toDecompData.m) (hprim : Prim nℓ) (hvl_prim : Nivat.Primitive vl)
    (hperp : dot nℓ vl = 0) (i : Fin d.toDecompData.m)
    (hdoth : dot nℓ (d.toDecompData.h i) = 0)
    {Gen : Finset (ℤ × ℤ) → ℤ × ℤ → Prop}
    (hSwgen : ∀ Sw a₀, Conv Sw = Conv (supp (∏ j ∈ univ.erase i,
      (mono (d.toDecompData.h j) - 1 : LaurentTwo ℤ))) → a₀ ∈ Sw →
      Gen Sw a₀)
    (hnoedge : ∀ Sw, Conv Sw = Conv (supp (∏ j ∈ univ.erase i,
      (mono (d.toDecompData.h j) - 1 : LaurentTwo ℤ))) →
      ∀ n ∈ E (↑Sw : Set (ℤ × ℤ)), dot n vl ≠ 0) :
    ∃ Sw : Finset (ℤ × ℤ),
      LatticeConvex Sw ∧
      E (↑Sw : Set (ℤ × ℤ)) ⊆ E (↑d.toDecompData.Sphi : Set (ℤ × ℤ)) ∧
      ∃ a₀ ∈ Sw, LatticeConvex (Sw.erase a₀) ∧
        (∀ z ∈ Sw.erase a₀, dot nℓ a₀ < dot nℓ z) ∧
        Gen Sw a₀ := by
  -- Item 1: construct Sw
  obtain ⟨Sw, -, hconv, hhull⟩ :=
    Nivat.Colle.exists_latticeConvex_completion
      (supp (∏ j ∈ univ.erase i, (mono (d.toDecompData.h j) - 1 : LaurentTwo ℤ)))
  have hne : Sw.Nonempty := by
    -- `ψ = ∏_{j ≠ i} (X^{h_j} − 1) ≠ 0`（`LaurentTwo ℤ` 无零因子，`factor_ne_zero`），
    -- 于是 `supp ψ` 非空，而 `Conv Sw = Conv (supp ψ)` 迫使 `Sw` 非空（集成者之手，2026-09-20）。
    have hψ : (∏ j ∈ univ.erase i, (mono (d.toDecompData.h j) - 1 : LaurentTwo ℤ)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun j _ => d.toDecompData.factor_ne_zero j
    have hsupp : (supp (∏ j ∈ univ.erase i,
        (mono (d.toDecompData.h j) - 1 : LaurentTwo ℤ))).Nonempty := by
      refine Finsupp.support_nonempty_iff.mpr fun hc => ?_
      exact hψ (AddMonoidAlgebra.coeff_eq_zero.mp hc)
    obtain ⟨z, hz⟩ := hsupp
    have hzC := Nivat.subset_Conv hz
    rw [← hhull] at hzC
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    rw [hemp] at hzC
    simp [Conv] at hzC
  -- Item 3: E ↑Sw ⊆ E ↑Sphi (zonotope edge subset)
  have hE_sub : E (↑Sw : Set (ℤ × ℤ)) ⊆ E (↑d.toDecompData.Sphi : Set (ℤ × ℤ)) := by
    -- 两边都经 Ostrowski（`Conv_supp_prod_eq_Conv_zonoF`）换成 zonotope，`E_congr_of_Conv_eq`
    -- 搬 `E`，`E_zono` 把 `E` 拆成各生成元线段的并；去掉一个指标只让并变小
    -- （集成者之手，2026-09-20）。
    have h1 : E (↑Sw : Set (ℤ × ℤ))
        = E (↑(Nivat.LE2.zonoF (univ.erase i) d.toDecompData.h) : Set (ℤ × ℤ)) :=
      Nivat.LE2.E_congr_of_Conv_eq (by
        rw [hhull, Nivat.LE2.Conv_supp_prod_eq_Conv_zonoF _ _
          (fun j _ => d.toDecompData.h_ne j)])
    have h2 : E (↑d.toDecompData.Sphi : Set (ℤ × ℤ))
        = E (↑(Nivat.LE2.zonoF univ d.toDecompData.h) : Set (ℤ × ℤ)) :=
      Nivat.LE2.E_congr_of_Conv_eq (by
        rw [d.toDecompData.Sphi_eq, Nivat.LE2.Conv_supp_prod_eq_Conv_zonoF _ _
          (fun j _ => d.toDecompData.h_ne j)])
    rw [h1, h2, Nivat.LE2.coe_zonoF, Nivat.LE2.coe_zonoF, Nivat.LE2.E_zono, Nivat.LE2.E_zono]
    exact Set.biUnion_subset_biUnion_left (Finset.erase_subset i univ)
  -- Item 4: apply Lemma 2.6 + strict_argmin
  have hnoedge' : ∀ n ∈ E (↑Sw : Set (ℤ × ℤ)), dot n vl ≠ 0 := hnoedge Sw hhull
  obtain ⟨a₀, ha₀, hstrict⟩ :=
    Nivat.LE2.strict_argmin_of_generatingSet_no_edge_parallel
      hne hprim hperp hnoedge' hconv
  -- Item 5: erase a₀ preserves lattice convexity
  have hconv_erase : LatticeConvex (Sw.erase a₀) :=
    latticeConvex_erase_of_strict_argmin hconv hstrict
  -- Item 2 (narrowed 2026-09-21, 集成者): the window only ever needs `GeneratesAt` at the
  -- single point `a₀` produced by Item 4 — see `SweepLines.hbase_at_of_sweep_lines`, whose
  -- only use of the old `IsGeneratingSet` was the projection `.2.2 a₀ ha₀ hconv`.
  have hgen : Gen Sw a₀ := hSwgen Sw a₀ hhull ha₀
  exact ⟨Sw, hconv, hE_sub, a₀, ha₀, hconv_erase, hstrict, hgen⟩

/-- **Hole 3 producer at prime: the `Sw` bundle with correct Lemma 2.5 signature.**

原文：b3_colle2.txt:788-792

Produces everything for hole 3 with the **correct** generating set signature: `𝒮_{φ_ι}` generates
`η − η̄_{ι₀}` (Lemma 2.5, `AlphabetReduction.lean:665`), not `ξ`.

## Binders

- `d : DecompDataZ ξ` — the minimal counterexample decomposition
- `hm : 2 ≤ d.toDecompData.m` — at least two components (`:764`)
- `hprim : Prim nℓ`, `hvl_prim : Primitive vl` — primitivity of the dual pair
- `hperp : dot nℓ vl = 0` — orthogonality (`:788` setup)
- `i : Fin d.toDecompData.m` — the index `ι₀` (`:788`)
- `hdoth : dot nℓ (d.toDecompData.h i) = 0` — `h_{ι₀}` parallel to `vl` (`:788-790`)
- **`hp : p.Prime`** — the prime for alphabet reduction
- `hnoedge` — Lemma 2.6 (as before)

## Conclusion

The first conjunct is now `IsGeneratingSet (reduceMod p ξ - reduceMod p (d.toDecompData.eta i)) Sw`,
matching `AlphabetReduction.isGeneratingSet_psi_at_prime` (`:665-674`).

## Consumer

`RegionSteps.exists_wedgeResidualR` hole 3 (`RegionSteps.lean:2285`). -/
theorem exists_window_strict_at_prime (d : Nivat.Colle35.DecompDataZ ξ) {nℓ vl : ℤ × ℤ}
    (_hm : 2 ≤ d.toDecompData.m) (hprim : Prim nℓ) (_hvl_prim : Nivat.Primitive vl)
    (hperp : dot nℓ vl = 0) (i : Fin d.toDecompData.m)
    (_hdoth : dot nℓ (d.toDecompData.h i) = 0)
    {p : ℕ} (hp : p.Prime)
    (hhull_mod : ∀ Sw : Finset (ℤ × ℤ),
      Conv (↑Sw : Finset (ℤ × ℤ)) = Conv (supp (∏ j ∈ univ.erase i,
        (mono (d.toDecompData.h j) - 1 : LaurentTwo ℤ))) →
      Conv (↑Sw : Finset (ℤ × ℤ)) = Conv (supp (∏ j ∈ univ.erase i,
        (mono (d.toDecompData.h j) - 1 : LaurentTwo (ZMod p)))))
    (hnoedge : ∀ Sw, Conv Sw = Conv (supp (∏ j ∈ univ.erase i,
      (mono (d.toDecompData.h j) - 1 : LaurentTwo ℤ))) →
      ∀ n ∈ E (↑Sw : Set (ℤ × ℤ)), dot n vl ≠ 0) :
    ∃ Sw : Finset (ℤ × ℤ),
      IsGeneratingSet
        (Nivat.Colle.AlphabetReduction.reduceMod p ξ
          - Nivat.Colle.AlphabetReduction.reduceMod p (d.toDecompData.eta i)) Sw ∧
      LatticeConvex Sw ∧
      E (↑Sw : Set (ℤ × ℤ)) ⊆ E (↑d.toDecompData.Sphi : Set (ℤ × ℤ)) ∧
      Conv Sw = Conv (Nivat.LE2.zonoF (univ.erase i) d.toDecompData.h) ∧
      ∃ a₀ ∈ Sw, LatticeConvex (Sw.erase a₀) ∧
        ∀ z ∈ Sw.erase a₀, dot nℓ a₀ < dot nℓ z := by
  -- Item 1: construct Sw (same as before)
  obtain ⟨Sw, hsub, hconv, hhull⟩ :=
    Nivat.Colle.exists_latticeConvex_completion
      (supp (∏ j ∈ univ.erase i, (mono (d.toDecompData.h j) - 1 : LaurentTwo ℤ)))
  have hne : Sw.Nonempty := by
    have hψ : (∏ j ∈ univ.erase i, (mono (d.toDecompData.h j) - 1 : LaurentTwo ℤ)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun j _ => d.toDecompData.factor_ne_zero j
    have hsupp : (supp (∏ j ∈ univ.erase i,
        (mono (d.toDecompData.h j) - 1 : LaurentTwo ℤ))).Nonempty := by
      refine Finsupp.support_nonempty_iff.mpr fun hc => ?_
      exact hψ (AddMonoidAlgebra.coeff_eq_zero.mp hc)
    obtain ⟨z, hz⟩ := hsupp
    have hzC := Nivat.subset_Conv hz
    rw [← hhull] at hzC
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    rw [hemp] at hzC
    simp [Conv] at hzC
  -- Item 2: hSwgen via isGeneratingSet_psi_at_prime
  have hgen : IsGeneratingSet
      (Nivat.Colle.AlphabetReduction.reduceMod p ξ
        - Nivat.Colle.AlphabetReduction.reduceMod p (d.toDecompData.eta i)) Sw := by
    -- Apply AlphabetReduction.isGeneratingSet_psi_at_prime
    -- Need: hhull_mod : Conv Sw = Conv (supp (∏ j ∈ univ.erase i, (mono (h j) - 1 : LaurentTwo (ZMod p))))
    have hhull_mod' : Conv (↑Sw : Finset (ℤ × ℤ))
        = Conv (supp (∏ j ∈ univ.erase i,
            (mono (d.toDecompData.h j) - 1 : LaurentTwo (ZMod p)))) := hhull_mod Sw hhull
    exact Nivat.Colle.AlphabetReduction.isGeneratingSet_psi_at_prime hp
      d.toDecompData.sum_eq d.toDecompData.h_period i hne hconv hsub hhull_mod'
  -- Item 3: E ↑Sw ⊆ E ↑Sphi (same as before)
  have hE_sub : E (↑Sw : Set (ℤ × ℤ)) ⊆ E (↑d.toDecompData.Sphi : Set (ℤ × ℤ)) := by
    have h1 : E (↑Sw : Set (ℤ × ℤ))
        = E (↑(Nivat.LE2.zonoF (univ.erase i) d.toDecompData.h) : Set (ℤ × ℤ)) :=
      Nivat.LE2.E_congr_of_Conv_eq (by
        rw [hhull, Nivat.LE2.Conv_supp_prod_eq_Conv_zonoF _ _
          (fun j _ => d.toDecompData.h_ne j)])
    have h2 : E (↑d.toDecompData.Sphi : Set (ℤ × ℤ))
        = E (↑(Nivat.LE2.zonoF univ d.toDecompData.h) : Set (ℤ × ℤ)) :=
      Nivat.LE2.E_congr_of_Conv_eq (by
        rw [d.toDecompData.Sphi_eq, Nivat.LE2.Conv_supp_prod_eq_Conv_zonoF _ _
          (fun j _ => d.toDecompData.h_ne j)])
    rw [h1, h2, Nivat.LE2.coe_zonoF, Nivat.LE2.coe_zonoF, Nivat.LE2.E_zono, Nivat.LE2.E_zono]
    exact Set.biUnion_subset_biUnion_left (Finset.erase_subset i univ)
  -- Item 3b: 窗口的凸包就是**去掉一个生成元**的 zonotope（`:792` 的 `φ_ι := ∏_{j≠ι₀}`）。
  -- 这条在 Item 3 里已经算过一遍（`h1`），只是过去没有导出；洞 6 的 `hsupp` 要它。
  have hSw_zono : Conv Sw = Conv (Nivat.LE2.zonoF (univ.erase i) d.toDecompData.h) := by
    rw [hhull, Nivat.LE2.Conv_supp_prod_eq_Conv_zonoF _ _ (fun j _ => d.toDecompData.h_ne j)]
  -- Item 4: apply Lemma 2.6 + strict_argmin (same as before)
  have hnoedge' : ∀ n ∈ E (↑Sw : Set (ℤ × ℤ)), dot n vl ≠ 0 := hnoedge Sw hhull
  obtain ⟨a₀, ha₀, hstrict⟩ :=
    Nivat.LE2.strict_argmin_of_generatingSet_no_edge_parallel
      hne hprim hperp hnoedge' hconv
  -- Item 5: erase a₀ preserves lattice convexity (same as before)
  have hconv_erase : LatticeConvex (Sw.erase a₀) :=
    latticeConvex_erase_of_strict_argmin hconv hstrict
  exact ⟨Sw, hgen, hconv, hE_sub, hSw_zono, a₀, ha₀, hconv_erase, hstrict⟩

#print axioms Nivat.ColleReg.exists_window_strict_at_prime

/-! ### 撤回 (2026-09-21, 集成者): `generatesAt_of_hull_erase` 整条删除

lane Hcone 于 01:53 把一条 `sorry` 落进主仓（`generatesAt_of_hull_erase`），违反红线，已删。
它的**诊断是对的**，保留在这里：`GeneratesAt ξ Sw a₀` 仍产不出来，因为 Lemma 2.5
（`AlphabetReduction.lean:665` `isGeneratingSet_psi_at_prime`）给的是
`IsGeneratingSet (reduceMod p ξ - reduceMod p (eta i)) Sw` —— **`ZMod p` 之差**，不是 `ξ`。

## 但结论是「消费者要错了对象」，不是「缺一条提升引理」

原文 `b3_colle2.txt:790`：「Note that `η̄_{ι₀}` and then `(T^u(η-η̄_{ι₀}))|_{H_B(ℓ)}`
is periodic with period parallel to `ℓ`」。`:798` 图 10 说明同样写
「Since `Ŝ_{φ_ι}` is an **`η-η̄_{ι₀}`**-generating set…」。
**整条扫掠（`:794-804`）跑在 `η - η̄_{ι₀}` 上，不跑在 `η` 上**；`:804` 最后一句
「and therefore `(T^u η)|_{𝓡_{ι-1}}` is periodic」是**把周期分量 `η̄_{ι₀}` 加回去**得到的，
不是对 `η` 直接扫的。

所以 `SweepLines.hbase_at_of_sweep_lines` 的 `hS : GeneratesAt ξ S a` 是**我们自己加强的**
（硬规矩 7：比原文强 = 债）。源对齐的签名是在 `ζ := reduceMod p ξ - reduceMod p (eta ι₀)`
上扫，再两步还原：

1. **加回周期分量**：`c • vl ∈ Per (eta ι₀)`（`exists_zsmul_vl_mem_Per_eta`），故
   `PeriodOn (T e ζ) R (c•vl)` ⟹ `PeriodOn (T e (reduceMod p ξ)) R (c•vl)`。
2. **`ZMod p → ℤ` 提升**：`:786`「changing the alphabet if necessary, let `p` be a prime
   such that `𝒜 ⊆ ℤ_p`」——即 `reduceMod p` 在 `ξ` 的**字母表上单射**。树里已有件：
   `AlphabetReduction.exists_prime_injOn_intCast` (`:182`)、`mem_Per_comp_of_injOn` (`:152`)、
   `isPeriodic_comp_iff` (`:169`)。

两步都**不**需要 Hcone 草拟的那条「general lemma about lifting generation through
`reduceMod`」——提升的是**周期性**（`PeriodOn`），不是**生成性**（`GeneratesAt`）。
生成性只在 `ZMod p` 里用一次，用完就不再提。
-/

/-! ## Part 10: Periodicity transfer lemmas (b3_colle2.txt:786, :790)

原文 `:786`「changing the alphabet if necessary, let `p` be a prime such that `𝒜 ⊆ ℤ_p`」和
`:790`「Note that `η̄_{ι₀}` and then `(T^u(η-η̄_{ι₀}))|_{H_B(ℓ)}` is periodic」。

这两条把周期性从 `ZMod p` 的差配置还原到原始的 `ℤ` 配置。 -/

/-- **Step 1: Add back the periodic component** (b3_colle2.txt:790).

If `ζ - ζ'` is periodic on `R` and `ζ'` is also periodic on `R` with the same period,
then `ζ` is periodic on `R`.

原文：`:790` "Note that `η̄_{ι₀}` and then `(T^u(η-η̄_{ι₀}))|_{H_B(ℓ)}` is periodic with
period parallel to `ℓ`". The second clause combines the periodicity of the difference
with the periodicity of `η̄_{ι₀}` to get periodicity of `η`. -/
theorem periodOn_of_periodOn_sub {p : ℕ} {ζ ζ' : Nivat.Config (ZMod p)}
    {R : Set (ℤ × ℤ)} {e h : ℤ × ℤ}
    (hsub : Nivat.Colle41.PeriodOn (Nivat.T e (ζ - ζ')) R h)
    (hζ' : Nivat.Colle41.PeriodOn (Nivat.T e ζ') R h) :
    Nivat.Colle41.PeriodOn (Nivat.T e ζ) R h := by
  intro z hz hz'
  have hsub_z := hsub z hz hz'
  have hζ'_z := hζ' z hz hz'
  simp only [Nivat.T_apply, Pi.sub_apply] at hsub_z
  simp only [Nivat.T_apply] at hζ'_z ⊢
  -- ζ (z + h + e) = (ζ - ζ') (z + h + e) + ζ' (z + h + e)
  --               = (ζ - ζ') (z + e) + ζ' (z + e)     by hsub_z and hζ'_z
  --               = ζ (z + e)
  have step1 : ζ (z + h + e) = (ζ (z + h + e) - ζ' (z + h + e)) + ζ' (z + h + e) := by ring
  rw [step1, hsub_z, hζ'_z]
  ring

/-- **Step 2: Lift from `ZMod p` to `ℤ`** (b3_colle2.txt:786).

If `reduceMod p ξ` is periodic on `R` and the cast `(· : ℤ) → ZMod p` is injective on
the alphabet of `ξ`, then `ξ` itself is periodic on `R`.

原文：`:786` "changing the alphabet if necessary, let `p` be a prime such that `𝒜 ⊆ ℤ_p`".
This means `reduceMod p` is injective on the finite alphabet, so periods of the reduced
configuration lift back to the original.

Uses `AlphabetReduction.mem_Per_comp_of_injOn` (`:152`) and the fact that `PeriodOn` is
defined in terms of the period group `Per`. -/
theorem periodOn_of_periodOn_reduceMod {ξ : Nivat.Config ℤ} {p : ℕ}
    {R : Set (ℤ × ℤ)} {e h : ℤ × ℤ}
    (hinj : Set.InjOn (fun a : ℤ => (a : ZMod p)) (Set.range ξ))
    (hper : Nivat.Colle41.PeriodOn (Nivat.T e (Nivat.Colle.AlphabetReduction.reduceMod p ξ)) R h) :
    Nivat.Colle41.PeriodOn (Nivat.T e ξ) R h := by
  intro z hz hz'
  have hper_z := hper z hz hz'
  simp only [Nivat.T_apply, Nivat.Colle.AlphabetReduction.reduceMod_apply] at hper_z
  simp only [Nivat.T_apply]
  exact hinj ⟨z + h + e, rfl⟩ ⟨z + e, rfl⟩ hper_z

#print axioms Nivat.ColleReg.periodOn_of_periodOn_sub
#print axioms Nivat.ColleReg.periodOn_of_periodOn_reduceMod

/-- **End-to-end bridge: from `ZMod p` difference periodicity to `ℤ` periodicity**
(b3_colle2.txt:786, :790).

Combines the two-step lifting process:
1. Add back the periodic component `ζbar` (`:790`)
2. Lift from `ZMod p` to `ℤ` using alphabet injectivity (`:786`)

原文：`:786` "changing the alphabet if necessary, let `p` be a prime such that `𝒜 ⊆ ℤ_p`"
(alphabet injection), `:790` "Note that `η̄_{ι₀}` and then `(T^u(η-η̄_{ι₀}))|_{H_B(ℓ)}` is
periodic with period parallel to `ℓ`" (add back the periodic component).

This is the **only** missing piece for transferring Lemma 2.5's generation result
(which holds for `η - η̄_{ι₀}` in `ZMod p`) back to periodicity of `ξ` in `ℤ` through
the `:794-804` line-by-line sweep. -/
theorem periodOn_of_periodOn_reduceMod_sub {ξ : Nivat.Config ℤ} {p : ℕ}
    {ζbar : Nivat.Config (ZMod p)} {R : Set (ℤ × ℤ)} {e h : ℤ × ℤ}
    (hinj : Set.InjOn (fun a : ℤ => (a : ZMod p)) (Set.range ξ))
    (hbar : h ∈ Nivat.Per ζbar)
    (hsub : Nivat.Colle41.PeriodOn
      (Nivat.T e (Nivat.Colle.AlphabetReduction.reduceMod p ξ - ζbar)) R h) :
    Nivat.Colle41.PeriodOn (Nivat.T e ξ) R h := by
  -- Step 1: Convert `h ∈ Per ζbar` to `PeriodOn (T e ζbar) R h`
  have hζbar : Nivat.Colle41.PeriodOn (Nivat.T e ζbar) R h := by
    intro z hz hz'
    simp only [Nivat.T_apply]
    -- Need: ζbar (z + h + e) = ζbar (z + e)
    -- Have: hbar says ∀ w, ζbar (w + h) = ζbar w
    -- Apply at w = z + e
    have : ζbar ((z + e) + h) = ζbar (z + e) := congrFun hbar (z + e)
    convert this using 2
    ring
  -- Step 2: Add back the periodic component (periodOn_of_periodOn_sub)
  have hsum : Nivat.Colle41.PeriodOn
      (Nivat.T e (Nivat.Colle.AlphabetReduction.reduceMod p ξ)) R h :=
    periodOn_of_periodOn_sub hsub hζbar
  -- Step 3: Lift from ZMod p to ℤ (periodOn_of_periodOn_reduceMod)
  exact periodOn_of_periodOn_reduceMod hinj hsum

#print axioms Nivat.ColleReg.periodOn_of_periodOn_reduceMod_sub

end Nivat.ColleReg
