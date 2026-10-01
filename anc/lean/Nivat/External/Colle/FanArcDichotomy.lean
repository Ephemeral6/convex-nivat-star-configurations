/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.PolyChainSum

/-!
# The `§21` dichotomy without the degenerate-branch hypothesis (lane-hole3-nlmax)

`ShellSubStrip.lean` §21 (`:2610-2665`) shows: writing `⟪n, dir ν⟫ = det ν n` and reading the
ccw fan `ℓ = k₀, J = k₁, ν_{J+1} = k₂` off `𝒮_φ` (`b3_colle2.txt:506`, "`Â_∞` is an
`(ℓ, ℓ_J)`-region"; `:440`/`:518` for the two reach-set constraints that make the recovery
source exactly the wedge's polar cone), every normal `n ∈ E 𝒮_φ` **deleted by the `w`-sweep**
(`0 < ⟪n, w⟫`, `w := -(dir ν_{J+1})`) is either `J` or lies in the wedge's polar cone
`{det ℓ · ≤ 0} ∩ {det J · ≤ 0}` — **`Nivat.LaneCdFan.recovered_of_sweep_deleted_dot`** — but
`ShellSubStrip.lean:2637-2653` narrows this: the proof needs `harc_lJ : ∀ k ∈ E S,
¬ (0 < det l k ∧ det J k < 0)`, i.e. `Arc ℓ J = ∅` — the *degenerate* branch of `J`'s
fan-predecessor selection (`LeafAJSelect.exists_fan_pred`), and does **not** hold in general
(the gap is exactly the normals strictly between `ℓ` and `J`).

This file supplies the **general-branch replacement**: instead of asserting the disjunction
unconditionally, state what is missing from `{J} ∪ cone` *exactly* — it is `Arc ℓ J`, no more
and no less — using only `Arc J ν_{J+1} = ∅` (fan-adjacency of `J` and its own ccw successor,
which unlike `Arc ℓ J = ∅` is **not** a degenerate branch: it is unconditionally true of any
selected `J`, since nothing can sit strictly between `J` and its immediate successor by
definition of "successor"). Numeric sanity check (硬规矩 6) against a *non-degenerate*
instance (`Arc ℓ J ≠ ∅`, an octagon with `ℓ, J` two fan-steps apart) is
`tmp/wip/lane-hole3-nlmax-arc-nonempty-instance.lean`: `missingGen_eq : missingGen =
{(1,1),(0,1)} = Arc ℓ J` exactly, confirming the shape below before it was written here.

## What is here

* `det_le_zero_of_swept` — cone's second conjunct (`det J n ≤ 0`) is a *free* consequence of
  `n` being swept and `n ∈ E S`, needing only `Arc J ν_{J+1} = ∅` (not `Arc ℓ J = ∅`).
* `missing_iff_arc` — the exact replacement for `recovered_of_sweep_deleted_dot`'s conclusion on
  the general branch: for swept `n ≠ J`, "outside `{J} ∪ cone`" is exactly `n ∈ Arc ℓ J`.

`0 < det ℓ J` was in the originally proposed signature but is **unused** by the proof below
(硬规矩 5): the equivalence needs no relation between `ℓ` and `J` themselves, only between each
of `ℓ`, `J` and the swept point `n`.
-/

set_option autoImplicit false

namespace Nivat.LaneHole3Nlmax

open Nivat Nivat.LE2 Nivat.PolyChainSum

/-- **Cone's second conjunct is free for swept normals.**  Corresponds to the `det J k < 0`
half of `ShellSubStrip.lean`'s `harc_Jnu` (`:2675`), restated via `Arc` (`b3_colle2.txt:506`
fan-adjacency of `J`, `ν_{J+1}`): if `n ∈ E ↑S` and `0 < det n νJ1` (swept by
`w = -(dir νJ1)`, `Nivat.LaneCdFan.dot_neg_dir`), then `det J n ≤ 0` — the alternative
`det J n > 0` would put `n` in `Arc hfin J νJ1`, contradicting `harcJ`. -/
theorem det_le_zero_of_swept {S : Finset (ℤ × ℤ)} (hfin : (↑S : Set (ℤ × ℤ)).Finite)
    {J νJ1 n : ℤ × ℤ} (harcJ : Arc hfin J νJ1 = ∅)
    (hnE : n ∈ E (↑S : Set (ℤ × ℤ))) (hswept : 0 < det n νJ1) :
    det J n ≤ 0 := by
  by_contra hcon
  push_neg at hcon
  have hmem : n ∈ Arc hfin J νJ1 := mem_Arc.mpr ⟨hnE, hcon, hswept⟩
  rw [harcJ] at hmem
  exact absurd hmem (Finset.notMem_empty n)

/-- **The general-branch replacement for `recovered_of_sweep_deleted_dot`'s dichotomy**
(`ShellSubStrip.lean:2705-2714`, narrowed at `:2637-2653`): for swept, non-`J` normals of
`E ↑S`, "outside `{J} ∪ {det ℓ · ≤ 0 ∧ det J · ≤ 0}`" is *exactly* `n ∈ Arc hfin ℓ J`
(`b3_colle2.txt:506`'s wedge polar cone, minus its two pinned edges, minus `{J}`, is the arc
strictly between `ℓ` and `J`). Both directions route through `det_le_zero_of_swept`; the
forward direction additionally needs `hJprim`/`hJνJ1` to rule out the degenerate `n = -J`
parallel case (both primitive, `det J n = 0` ⟹ `n = J` or `n = -J`,
`eq_or_neg_of_prim_of_det_eq_zero`). -/
theorem missing_iff_arc {S : Finset (ℤ × ℤ)} (hfin : (↑S : Set (ℤ × ℤ)).Finite)
    {ℓ J νJ1 n : ℤ × ℤ} (hJprim : Prim J) (hJνJ1 : 0 < det J νJ1)
    (harcJ : Arc hfin J νJ1 = ∅)
    (hnE : n ∈ E (↑S : Set (ℤ × ℤ))) (hne : n ≠ J) (hswept : 0 < det n νJ1) :
    (¬ (det ℓ n ≤ 0 ∧ det J n ≤ 0)) ↔ n ∈ Arc hfin ℓ J := by
  have hcone2 : det J n ≤ 0 := det_le_zero_of_swept hfin harcJ hnE hswept
  constructor
  · intro hncone
    have hℓpos : 0 < det ℓ n := by
      by_contra h
      push_neg at h
      exact hncone ⟨h, hcone2⟩
    refine mem_Arc.mpr ⟨hnE, hℓpos, ?_⟩
    by_contra hnJ
    push_neg at hnJ
    have hJn : 0 ≤ det J n := by
      have hsk := det_skew n J
      omega
    have hJn0 : det J n = 0 := le_antisymm hcone2 hJn
    have hprimN : Prim n := (mem_E_iff.mp hnE).1
    rcases eq_or_neg_of_prim_of_det_eq_zero hJprim hprimN hJn0 with heq | heq
    · exact hne heq
    · rw [heq] at hswept
      have : det (-J) νJ1 = - det J νJ1 := by simp [det]; ring
      rw [this] at hswept
      linarith
  · intro harc
    obtain ⟨-, hℓpos, hJpos⟩ := mem_Arc.mp harc
    exact fun ⟨h1, _⟩ => absurd hℓpos (not_lt.mpr h1)

end Nivat.LaneHole3Nlmax

#print axioms Nivat.LaneHole3Nlmax.det_le_zero_of_swept
#print axioms Nivat.LaneHole3Nlmax.missing_iff_arc
