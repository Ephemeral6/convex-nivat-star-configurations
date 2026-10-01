/-
Copyright (c) 2025 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import Nivat.External.Colle.LatticeEdges

/-!
# Collé's Case 1 / Case 2 split, upstream of `RegionSteps`

These four declarations lived in `RegionSteps.lean` (`:297-360`) until 2026-09-19 and were
moved here **verbatim**, with no change to statements, proofs, namespace or full names.

**Why the move.**  `StepHypSeam.stepHyp_of_case2` (`StepHypSeam.lean:59`) converts `Case2`
into the `StepHyp` that `ChainRecursion` consumes — i.e. it is a producer for
`exists_chainData` (`RegionSteps.lean:830`).  But it could never be used there, because
`Case1`/`Case2` were defined *inside* `RegionSteps.lean`, so every consumer of them was
forced downstream of the very `sorry` they were meant to feed.  Measured 2026-09-19
(`scripts/offchain_kind.py`): of the 32 genuinely stranded modules, `StepHypSeam` was the
only one stuck *downstream* of the hole it fills — "不搬文件就永远接不上".  This file is that
move.  Nothing else is intended by it: no statement is strengthened, no hypothesis dropped.

`RegionSteps.lean` now imports this module, so `Nivat.ColleReg.Case1` / `.Case2` and the two
exhaustiveness lemmas keep their exact full names and every existing reference — in
`ColleRegion.lean`, `DecompData.lean`, `L1Data.lean`, `ONEDRational.lean`, `StepHypSeam.lean`
— continues to resolve unchanged.
-/

namespace Nivat.ColleReg

open Nivat

variable {ξ xper : Config ℤ} {vl : ℤ × ℤ} {S : Finset (ℤ × ℤ)}

/-! ## The case split of Lemma 4.5, and the data fixed before it

Collé proves Lemma 4.5 (`b3_colle2.txt:772`) in two complementary cases, announced at
`b3_colle2.txt:758` and quoted verbatim in the two definitions below.  **Everything
`exists_chainData` produces is Case 2's output only** — `b3_colle2.txt:760`: *"In Case 1, we
use **Lemma 4.1** … In **Case 2** … we use **Lemma 3.5**"* — so that theorem may not assert
it unconditionally, and Case 1 needs a branch of its own.

The generating set `𝒮` and the configuration `x_per` are fixed in the preamble
(`b3_colle2.txt:774-776`), *before* the split, which is why `exists_preamble` below hoists
them out of `exists_chainData`'s existential: `Case1`/`Case2` are statements *about* that
pair, so they cannot be hypotheses of a theorem that only produces it.

**Which set (2026-09-17).**  Both cases are stated over `E(𝒮_φ)`-enveloped sets, where
`𝒮_φ := conv(−supp φ) ∩ ℤ²` for `φ = ∏(X^{hᵢ} − 1)` (`b3_colle2.txt:298`, `:756`).  That is
*not* the Lemma 2.4 generating set `𝒮` of `exists_preamble` (`:286-292`), and Collé never
claims the two coincide.  `Case1`/`Case2` take the set as an explicit parameter, and the
assembly passes `d.Sphi` for `d : Nivat.Colle35.DecompDataZ ξ`
(`DecompDataZ.of_minimalCounterexample`), never `S`.  Until 2026-09-17 the assembly passed
`S`, with a field `decomp.Sphi = S` of `DecompData.ChainDataWithDecomp` as the fiat that hid
the mismatch; that field is gone. -/

/-- **Collé's Case 2**, `b3_colle2.txt:758` verbatim:

> For any `E(𝒮_φ)`-enveloped set `B ⊂ ℤ²` and all `u ∈ ℤ²` such that `(T^u η)|B = x_per|B`,
> one has `(T^u η)|H_B(ℓ_ι) ≠ x_per|H_B(ℓ_ι)`.

`vl` is Collé's `v_{ℓ_ι}`, so `Nivat.LE2.halfStrip B vl` is `H_B(ℓ_ι)` (Definition 3.4,
`b3_colle2.txt:410`).  `T u ξ z = ξ (z + u)` (`Nivat/Defs/Config.lean:50`).

This is the "but ≠" half of the hypothesis of **Lemma 3.5(i)** (`b3_colle2.txt:426-430`);
the other half — *for each `B'` there exists an enveloped `B ⊇ B'` with the same `ℓ_ι`
support line and a `u` agreeing on `B`* — is free from `x_per ∈ X_η`, and is what
`exists_chainData` must supply internally. -/
def Case2 (ξ xper : Config ℤ) (S : Finset (ℤ × ℤ)) (vl : ℤ × ℤ) : Prop :=
  ∀ B : Set (ℤ × ℤ), Nivat.LE2.EnvOf (S : Set (ℤ × ℤ)) B → ∀ u : ℤ × ℤ,
    (∀ z ∈ B, T u ξ z = xper z) →
      ¬ (∀ z ∈ Nivat.LE2.halfStrip B vl, T u ξ z = xper z)

/-- **Collé's Case 1**, `b3_colle2.txt:758` verbatim:

> For some `E(𝒮_φ)`-enveloped set `B ⊂ ℤ²` there exists `u ∈ ℤ²` such that
> `(T^u η)|H_B(ℓ_ι) = x_per|H_B(ℓ_ι)`.

Collé states no agreement on `B` here because `B ⊆ H_B(ℓ_ι)` makes it redundant
(Definition 3.4 admits `t = 0`; `Nivat.LE2.subset_halfStrip`).  That inclusion is also why
the two cases are exhaustive — see `case1_of_not_case2`. -/
def Case1 (ξ xper : Config ℤ) (S : Finset (ℤ × ℤ)) (vl : ℤ × ℤ) : Prop :=
  ∃ B : Set (ℤ × ℤ), Nivat.LE2.EnvOf (S : Set (ℤ × ℤ)) B ∧
    ∃ u : ℤ × ℤ, ∀ z ∈ Nivat.LE2.halfStrip B vl, T u ξ z = xper z

/-- The two cases are mutually exclusive: Case 1's witness agrees on `B` too, because
`B ⊆ H_B(ℓ_ι)`. -/
theorem not_case2_of_case1 (h : Case1 ξ xper S vl) : ¬ Case2 ξ xper S vl := by
  obtain ⟨B, hB, u, hu⟩ := h
  exact fun h2 =>
    h2 B hB u (fun z hz => hu z (Nivat.LE2.subset_halfStrip B vl hz)) hu

/-- The two cases are exhaustive. -/
theorem case1_of_not_case2 (h : ¬ Case2 ξ xper S vl) : Case1 ξ xper S vl := by
  classical
  by_contra hc
  refine h (fun B hB u _ hu => hc ⟨B, hB, u, hu⟩)

end Nivat.ColleReg
