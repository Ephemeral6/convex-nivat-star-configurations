/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.DecompData
import Nivat.External.Colle.CaseSplit
import Nivat.External.Colle.LatticeEdges
import Nivat.External.Colle.MinkowskiEdges
import Nivat.External.Colle.NewtonZonotope

/-!
# Hole 1 of `exists_wedgeResidualR`: `vl` is parallel to some generator `h i`

原文：b3_colle2.txt:766 (the "renaming clause"), :788 (selecting `ι₀`)

## What hole 1 is

Hole 1 is **b3_colle2.txt:766's renaming clause**, verbatim:

> Suppose `ℓ₁,…,ℓ_{2m} ⊂ ℝ²` is an enumeration of the oriented lines through the origin
> **parallels to the edges of `𝒮_φ`** where the edge parallel to `ℓ_{i+1}` is a successor of
> the edge parallel to `ℓ_i` and indices are taken modulo `2m`. **Renaming the vectors
> `h₁,…,h_m` if necessary, we may assume that each `h_i`, with `1 ≤ i ≤ m`, is either parallel
> or antiparallel to `ℓ_i`.**

## Quantifier correspondence (hard rule 7)

| Source (b3_colle2.txt) | On-chain encoding |
|---|---|
| `ℓ = ℓ_ι` | `ℓ` (the `NonExpansiveLine` from `hℓ_nel`); `vl = v⃗_ℓ` fixed by `hdet_ℓ : dot ℓ vl = 0` |
| `ℓ_ι` is parallel to some edge of `𝒮_φ` | **First half of hole 1**: `vl` is an edge direction of `d.toDecompData.Sphi` (may already be available from how `ℓ` was selected; see below) |
| "renaming … `h_i` parallel or antiparallel to `ℓ_i`" | **Second half of hole 1**: `∃ i, det (h i) vl = 0` |
| `ι₀ = ι mod m` (`:788`) | The `i : Fin d.toDecompData.m` to be delivered |

## What "renaming" means

"Renaming" is not an imperative to permute data structures. It is a **provable zonotope theorem**:
the paper *defines* `ℓ₁..ℓ_{2m}` as the edge directions of `𝒮_φ`, then claims we can rename the
`h_i` so that `h_i ∥ ℓ_i`. This is true mathematically only if **every edge direction of `𝒮_φ` is
parallel to some `h_i`** — which holds because `m` pairwise-non-parallel generators span a
zonotope with exactly `2m` edges.

The on-chain premise `d.toDecompData.h_dir : ∀ i j, i ≠ j → det (h i) (h j) ≠ 0`
(`DecompData.lean:104`) encodes "pairwise non-parallel" and is **already available**.

The zonotope structure is `Sphi_eq : Conv Sphi = Conv (supp (∏ i, (mono (h i) - 1)))`
(`DecompData.lean:107`), also **already available**.

So hole 1 reduces to: **every edge direction of the zonotope `𝒮_φ` is parallel to some generator
`h_i`**. This is a theorem, not a field to add to `DecompData`.

## What is still uncertain (must verify before proceeding)

**The first half** — whether `vl` is an edge direction of `𝒮_φ` — may or may not be in hand.
Check `RegionSteps.lean` to see how `ℓ` was selected: if the call chain shows `ℓ` was taken from
an edge enumeration of `𝒮_φ`, this half is free (report the source). If not, it is a real gap
(state which binder is missing; do not invent a hypothesis).

## Why hole 1 matters

The `i` delivered here is consumed directly by hole 3 via `Nivat.ColleReg.no_edge_parallel_vl_of_erase`
(`RegionSteps.lean:1668`), whose binders `i` and `hdoth` are exactly this hole's output. At `:790`,
the paper constructs `φ_ι(X) := ∏_{i≠ι₀}(X^{h_i}−1)`, and Lemma 2.6 says `𝒮_{φ_ι}` has **no edge
parallel to `±ℓ`** — because the unique generator `h_{ι₀}` parallel to `ℓ` was **erased**. So
holes 1 and 3 are the same fact used twice; `i` must be the same. **Write the conclusion in
named form with `i` explicit**, so hole 3 can connect directly.

## Status

The free half (constructing `nℓ` from `vl` with `Prim nℓ ∧ dot nℓ vl = 0`) is complete.
The mathematical content awaits the zonotope edge-direction theorem and verification of whether
`vl` is known to be an edge direction of `𝒮_φ`.
-/

namespace Nivat.ColleReg

open Nivat Nivat.LE2 Nivat.Colle35

variable {ξ xper : Config ℤ} {S : Finset (ℤ × ℤ)} {vl : ℤ × ℤ}

/-- **The free half of hole 1**: given `vl`, construct `nℓ := (vl.2, -vl.1)` which is perpendicular
to `vl` and primitive when `vl` is primitive.

原文：b3_colle2.txt:788 ("let `ι₀` be such that `ι₀ = ι mod m`")

This constructs the normal vector `nℓ` perpendicular to `ℓ` (encoded as `vl`). -/
theorem exists_nℓ_perp_vl (hvl_prim : Primitive vl) (_hvl_ne : vl ≠ 0) :
    ∃ nℓ : ℤ × ℤ, Prim nℓ ∧ dot nℓ vl = 0 := by
  refine ⟨(vl.2, -vl.1), ?_, ?_⟩
  · -- Prim nℓ follows from Primitive vl
    rw [prim_iff_primitive]
    unfold Primitive at hvl_prim ⊢
    obtain ⟨a, b, hab⟩ := hvl_prim
    refine ⟨b, -a, ?_⟩
    calc b * vl.2 + (-a) * (-vl.1)
        = b * vl.2 + a * vl.1 := by ring
      _ = a * vl.1 + b * vl.2 := by ring
      _ = 1 := hab
  · -- dot nℓ vl = 0 by direct computation
    simp only [dot]
    ring

/-- **The equivalence needed for hole 1**: `dot nℓ (h i) = 0 ↔ det (h i) vl = 0`.

This shows that `nℓ` being perpendicular to `h i` is equivalent to `h i` being parallel to `vl`. -/
theorem dot_nℓ_eq_zero_iff_det_h_vl_eq_zero {vl h : ℤ × ℤ} :
    let nℓ := (vl.2, -vl.1)
    dot nℓ h = 0 ↔ det h vl = 0 := by
  simp [dot, det]
  constructor <;> intro h <;> linarith

/-- **Hole 1 for `exists_wedgeResidualR`: every edge direction of `𝒮_φ` is parallel to some `h i`.**

原文：b3_colle2.txt:766 (renaming clause), :788 (selecting `ι₀`)

This is the zonotope half of hole 1. Given `nℓ ∈ E ↑d.Sphi` (an edge normal of `𝒮_φ`) and
`dot nℓ vl = 0` (so `vl` is parallel to that edge), conclude that some generator `h i` is
perpendicular to `nℓ`, i.e., parallel to `vl`.

**Proof strategy**: by contrapositive via `no_edge_parallel_of_Conv_eq_supp_prod`. If all `h i`
were non-parallel to `vl` (i.e., `∀ i, det (h i) vl ≠ 0`), then by the contrapositive of
`det_eq_zero_of_dot_eq_zero`, we would have `∀ i, dot nℓ (h i) ≠ 0`, which by
`no_edge_parallel_of_Conv_eq_supp_prod` would force `dot nℓ vl ≠ 0`, contradicting `hperp`.

**What is still owed**: the hypothesis `hnℓ : nℓ ∈ E ↑d.Sphi`, i.e., that `vl` is an edge
direction of `𝒮_φ`. This is *not* free from `Case1` (which only asserts agreement on a
half-strip, not that `vl` is an edge direction). The integrator is wiring this from the
`hℓ_pos`/`hℓ_neg` route via ONED/face-card machinery. -/
theorem exists_h_parallel_vl_of_edge {ξ : Config ℤ} (d : DecompDataZ ξ) {nℓ vl : ℤ × ℤ}
    (hnℓ : nℓ ∈ E (↑d.toDecompData.Sphi : Set (ℤ × ℤ)))
    (hperp : dot nℓ vl = 0) (hvl_ne : vl ≠ 0) :
    ∃ i : Fin d.toDecompData.m, dot nℓ (d.toDecompData.h i) = 0 := by
  by_contra h_all_nonparallel
  push Not at h_all_nonparallel
  -- Extract `Prim nℓ` from `hnℓ : nℓ ∈ E ↑d.Sphi`
  rw [mem_E_iff] at hnℓ
  obtain ⟨hnℓ_prim, hnℓ_nontrivial⟩ := hnℓ
  have hnℓ_ne : nℓ ≠ 0 := Prim.ne_zero hnℓ_prim
  -- We have `∀ i, dot nℓ (h i) ≠ 0`. This means no `h i` is parallel to `vl`.
  -- Convert to the form `no_edge_parallel_of_Conv_eq_supp_prod` needs: `∀ i, det (h i) vl ≠ 0`
  have h_det : ∀ i ∈ (Finset.univ : Finset (Fin d.toDecompData.m)), det (d.toDecompData.h i) vl ≠ 0 := by
    intro i _
    intro hdet_zero
    -- Since `det (h i) vl = 0`, we have `h i ∥ vl`
    -- We need to show this implies `dot nℓ (h i) = 0`, contradicting `h_all_nonparallel i`
    -- From `det (h i) vl = 0`, we get: `(h i).1 * vl.2 - (h i).2 * vl.1 = 0`
    -- So `(h i).1 * vl.2 = (h i).2 * vl.1`
    -- We have `dot nℓ vl = nℓ.1 * vl.1 + nℓ.2 * vl.2 = 0`
    -- We want to show `dot nℓ (h i) = nℓ.1 * (h i).1 + nℓ.2 * (h i).2 = 0`
    -- From the det equation: `(h i).1 * vl.2 = (h i).2 * vl.1`
    -- From the dot equation: `nℓ.1 * vl.1 = -(nℓ.2 * vl.2)`
    have hdet : (d.toDecompData.h i).1 * vl.2 = (d.toDecompData.h i).2 * vl.1 := by
      simp only [det] at hdet_zero; linarith
    -- Now compute: `dot nℓ (h i) * vl.2 = (nℓ.1 * (h i).1 + nℓ.2 * (h i).2) * vl.2`
    --                                   `= nℓ.1 * (h i).1 * vl.2 + nℓ.2 * (h i).2 * vl.2`
    --                                   `= nℓ.1 * (h i).2 * vl.1 + nℓ.2 * (h i).2 * vl.2` (by hdet)
    --                                   `= (h i).2 * (nℓ.1 * vl.1 + nℓ.2 * vl.2)`
    --                                   `= (h i).2 * dot nℓ vl = (h i).2 * 0 = 0`
    have hdot_vl2 : dot nℓ (d.toDecompData.h i) * vl.2 = 0 := by
      simp only [dot] at hperp ⊢
      calc (nℓ.1 * (d.toDecompData.h i).1 + nℓ.2 * (d.toDecompData.h i).2) * vl.2
          = nℓ.1 * (d.toDecompData.h i).1 * vl.2 + nℓ.2 * (d.toDecompData.h i).2 * vl.2 := by ring
        _ = nℓ.1 * ((d.toDecompData.h i).1 * vl.2) + nℓ.2 * ((d.toDecompData.h i).2 * vl.2) := by ring
        _ = nℓ.1 * ((d.toDecompData.h i).2 * vl.1) + nℓ.2 * ((d.toDecompData.h i).2 * vl.2) := by rw [hdet]
        _ = (d.toDecompData.h i).2 * (nℓ.1 * vl.1 + nℓ.2 * vl.2) := by ring
        _ = (d.toDecompData.h i).2 * 0 := by rw [hperp]
        _ = 0 := by ring
    -- Similarly, `dot nℓ (h i) * vl.1 = 0`
    have hdot_vl1 : dot nℓ (d.toDecompData.h i) * vl.1 = 0 := by
      simp only [dot] at hperp ⊢
      calc (nℓ.1 * (d.toDecompData.h i).1 + nℓ.2 * (d.toDecompData.h i).2) * vl.1
          = nℓ.1 * (d.toDecompData.h i).1 * vl.1 + nℓ.2 * (d.toDecompData.h i).2 * vl.1 := by ring
        _ = nℓ.1 * ((d.toDecompData.h i).1 * vl.1) + nℓ.2 * ((d.toDecompData.h i).2 * vl.1) := by ring
        _ = nℓ.1 * ((d.toDecompData.h i).1 * vl.1) + nℓ.2 * ((d.toDecompData.h i).1 * vl.2) := by rw [← hdet]
        _ = (d.toDecompData.h i).1 * (nℓ.1 * vl.1 + nℓ.2 * vl.2) := by ring
        _ = (d.toDecompData.h i).1 * 0 := by rw [hperp]
        _ = 0 := by ring
    -- Since `dot nℓ (h i) * vl.2 = 0` and `dot nℓ (h i) * vl.1 = 0`, and `vl ≠ 0`,
    -- we must have `dot nℓ (h i) = 0`
    have : dot nℓ (d.toDecompData.h i) = 0 := by
      by_cases h1 : vl.1 = 0
      · by_cases h2 : vl.2 = 0
        · exact absurd (Prod.ext h1 h2) hvl_ne
        · exact mul_eq_zero.mp hdot_vl2 |>.resolve_right h2
      · exact mul_eq_zero.mp hdot_vl1 |>.resolve_right h1
    exact h_all_nonparallel i this
  -- Now apply `no_edge_parallel_of_Conv_eq_supp_prod`
  have hSphi_eq := d.toDecompData.Sphi_eq
  have hne : ∀ i ∈ (Finset.univ : Finset (Fin d.toDecompData.m)), d.toDecompData.h i ≠ 0 :=
    fun i _ => d.toDecompData.h_ne i
  have := no_edge_parallel_of_Conv_eq_supp_prod Finset.univ d.toDecompData.h hne h_det hSphi_eq
    ⟨hnℓ_prim, hnℓ_nontrivial⟩
  exact absurd hperp this

/-- **Bridge for hole 4**: erasing one generator from a zonotope gives a subset of edges.

原文：b3_colle2.txt:792 (`φ_ι(X) := ∏_{i≠ι₀}(X^{h_i}−1)`)

`𝒮_{φ_ι}` is the zonotope on `m−1` of `𝒮_φ`'s `m` generators. By `E_zono`, `E` of a zonotope
is the union of the `E (segOf (h i))` over the index set, so erasing one index gives a
sub-union — the inclusion is immediate from `Finset.erase_subset` plus
`Set.biUnion_subset_biUnion_left`.

This bridges hole 2's adjacency hypothesis `hadj` (over `E ↑d.Sphi`) to hole 4's `hvlmin`
requirement (over `E ↑Sw`, the erased zonotope). -/
theorem E_subset_of_erase {ι : Type*} [DecidableEq ι] (s : Finset ι) (i : ι) (h : ι → ℤ × ℤ) :
    (⋃ j ∈ s.erase i, E (segOf (h j))) ⊆ (⋃ j ∈ s, E (segOf (h j))) :=
  Set.biUnion_subset_biUnion_left (Finset.erase_subset i s)

end Nivat.ColleReg
