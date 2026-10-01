/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.Section8.ExternalDefs
import Nivat.External.Colle.Lemma35
import Nivat.External.Colle.Lemma45
import Nivat.External.Colle.LatticeEdges
import Nivat.External.Colle.Step_BiONED
import Nivat.External.Colle.Step_Nonempty
import Nivat.External.Colle.ChainGeom
import Nivat.External.Colle.Prop210
import Nivat.External.Colle.DecompData
import Nivat.External.Colle.Lemma41
import Nivat.External.Colle.PeriodTransport
import Nivat.External.Colle.Claim47Core

/-!
# `L1Data`: leaf L1's sixteen-conjunct existential, split into named fields

`case1_claim46_and_selection` (`RegionSteps.lean:866`, leaf **L1**) has to produce a single
existential over **eleven** pieces of data satisfying **sixteen** conjuncts.  As one `sorry`
that is not dispatchable: there is no way to hand one conjunct to one worker and another to
another, and no way for a partial result to be recorded in the kernel.

This file does the mechanical half of that problem:

* `L1Data` bundles the eleven data and **fifteen** of the sixteen conjuncts as named fields;
* `L1Data.toConclusion` assembles one into exactly the conclusion of
  `case1_claim46_and_selection`, discharging the other two for free.

The two free conjuncts are `ξ' ∈ orbitClosure ξ` and `∃ e, ξ' = T e ξ`.  Both come from the
single choice `ξ' := T e ξ`: the second is `⟨e, rfl⟩`, the first is `T_mem_orbitClosure`
(`Nivat/Defs/Orbit.lean:49`).  Collé makes the same choice in the first line of Case 1
(`b3_colle2.txt:778`), where `ξ'` is *defined* as a translate.

**No freedom is given up.**  `S₁` stays a field rather than being fixed to `S`, because
Collé's `𝒯` is a translate of `𝒮` (`b3_colle2.txt:824`) and conjunct 16
(`B.Nonempty ∧ ∃ b, ∀ z ∈ S₁, b + z ∈ R`; strong form `∃ b ∈ B, …` retired 2026-09-19, see
the field) may need that translate.  Likewise `e` is a field, not
derived: the paper's translation vector and the Lean `u` (the period direction) are different
objects, as the comment at `RegionSteps.lean:890-899` records.

## What this is and is not

It is **not** progress on the mathematics: building an `L1Data` is exactly as hard as proving
the original existential, and this file contains no step of Collé's argument.  What it buys is
that the fifteen obligations now have names, so they can be attacked, refuted, or landed
one at a time, and a proof of any one of them is a statement the kernel can check on its own.

Per `CLAUDE.md` hard rule 4 ("拆而后落"), this is the mechanical move to make *before*
dispatching work on a large undivided obligation, not after.
-/

namespace Nivat.ColleReg

open Nivat Nivat.Colle35

variable {ξ xper : Config ℤ} {vl p ℓ : ℤ × ℤ} {S : Finset (ℤ × ℤ)} {gen : ℤ × ℤ}

/-- **The data and obligations of leaf L1**, one field per conjunct of
`case1_claim46_and_selection`'s conclusion (`RegionSteps.lean:877-970`).

Field order follows the conjunct order of that conclusion.  One conjunct is absent because
`L1Data.toConclusion` discharges it from `ξ' := T e ξ`; see the module docstring.

**Count** (`grep -n "^  h" L1Data.lean` gives 15, integrator-measured 2026-09-18).  The
arithmetic is 16 conjuncts **+ 1** outer binder `ξ' ∈ orbitClosure ξ` = 17 obligations, minus
the 2 that `toConclusion` discharges (conjunct 2 `∃ e, ξ' = T e ξ`, and the orbitClosure
membership), leaving **15**.  An earlier version of this docstring said "fourteen": it read
`16 − 2` and forgot that the orbitClosure membership is a binder of `toConclusion`, not one of
the sixteen conjuncts.  Caught by the L1fields lane. -/
structure L1Data (ξ : Config ℤ) (S : Finset (ℤ × ℤ)) where
  /-- The translation defining `ξ' = T e ξ`.  Supplied by `Case1` (`CaseSplit.lean:82`);
  **not** the same object as `u` below. -/
  e : ℤ × ℤ
  /-- The direction of the period `h = c • u` (`b3_colle2.txt:806`). -/
  u : ℤ × ℤ
  /-- `u' = v_{ℓ'}`, the primitive vector along `ℓ'` (`b3_colle2.txt:351`). -/
  u' : ℤ × ℤ
  /-- `Q = 𝒯 ∖ ℓ'_𝒯` (`b3_colle2.txt:822`). -/
  Q : Finset (ℤ × ℤ)
  /-- The baseline level above which the `u'`-ray stays inside `R`. -/
  τ : ℤ
  /-- Lemma 4.1's pattern width (Collé's `p`); **not** the `p ∈ Per xper` of `region_case1`. -/
  pw : ℕ
  /-- The baseline set. -/
  B : Finset (ℤ × ℤ)
  /-- `R = 𝓡^N_I`. -/
  R : Set (ℤ × ℤ)
  /-- `R' = 𝓡^{N+1}_I`, carrying the maximality of `N` (`b3_colle2.txt:816-820`). -/
  R' : Set (ℤ × ℤ)
  /-- The period multiplier, `h = c • u`. -/
  c : ℤ
  /-- `S₁ = 𝒯`, the translated generating window (`b3_colle2.txt:824`). -/
  S₁ : Finset (ℤ × ℤ)
  /-- Conjunct 1. -/
  hS₁gen : Nivat.Colle.IsGeneratingSet ξ S₁
  /-- Conjunct 3. -/
  hQS : Q ⊆ S₁
  /-- Conjunct 4: `Q` is the complement in `S₁` of the maximising face normal to `n`, and that
  face is an edge parallel to `ℓ'`.  `n ≠ 0` is load-bearing — without it `n := 0` gives
  `Q = ∅`, a branch Collé never enters (`RegionSteps.lean:924-931`). -/
  hQ_edge : ∃ (n : ℝ × ℝ) (cmax : ℝ),
    n ≠ 0 ∧
    inner2 n u' = 0 ∧
    (∀ z ∈ S₁, inner2 n z ≤ cmax) ∧
    (Nivat.R2.face S₁ n cmax).Nonempty ∧
    Q = S₁.filter fun z => inner2 n z < cmax
  /-- Conjunct 5. -/
  hdet : det u u' ≠ 0
  /-- Conjunct 6: primitivity of `u'`, **not** derivable from the other `u'`-conjuncts — all
  four are invariant under `u' ↦ 2 • u'` (`RegionSteps.lean:932-939`). -/
  hu'_prim : Primitive u'
  /-- Conjunct 7. -/
  hPQ : P ξ S₁ ≤ P ξ Q + pw
  /-- Conjunct 8. -/
  hBQ : ∀ g ∈ B, ∀ i : ℕ, i < pw → g + (i : ℤ) • u' ∈ Q
  /-- Conjunct 9. -/
  hc : c ≠ 0
  /-- Conjunct 10. -/
  hRper : Colle41.PeriodOn (T e ξ) R (c • u)
  /-- Conjunct 11. -/
  hR_region : Colle41.IsRegion R u u'
  /-- Conjunct 12. -/
  hRR' : R ⊂ R'
  /-- Conjunct 13: the maximality of `N`.  Claim 4.7 is false without it. -/
  hnonper : ¬ Colle41.PeriodOn (T e ξ) R' (c • u)
  /-- Conjunct 14. -/
  hline : ∀ t : ℤ, τ ≤ t → ∀ z ∈ Q, t • u' + z ∈ R ∧ t • u' + z + c • u ∈ R
  /-- Conjunct 15: the straddle that propagates the period from `𝓡^N_I` to `𝓡^{N+1}_I`
  (`b3_colle2.txt:850-854`, Figure 11(B)). -/
  hstraddle : ∀ g ∈ S₁, g ∉ Q → ∀ t₀ : ℤ, τ ≤ t₀ →
    Colle41.PeriodOn (T e ξ) R (c • u) →
    (∀ t : ℤ, t₀ ≤ t → (T e ξ) (t • u' + g + c • u) = (T e ξ) (t • u' + g)) →
    Colle41.PeriodOn (T e ξ) R' (c • u)
  /-- Conjunct 16: the baseline is non-empty, and some point carries a full translate of the
  generating set in `R`.

  **Weakened 2026-09-19 (integrator ruling) from `∃ b ∈ B, ∀ z ∈ S₁, b + z ∈ R`.**  No
  on-chain consumer ever destructured the coupling "the *same* `b`": `case1_sweep` takes
  `B.Nonempty ∧ ∃ b, …` (`RegionSteps.lean`), `region_case1` forgot `b ∈ B` before passing it
  on, and leaf C's `exists_case2_window` was weakened to this shape at 10:0x.  The strong form
  was the last holdout and its extra content (`b ∈ maxB` *and* `b + S₁ ⊆ R` at one `b`) had no
  reader.  Conjunct strength is set by what consumers destructure, not by what looked natural
  when the field was written.  The old form is kept in this docstring per `PROTOCOL.md` §14. -/
  hbase : B.Nonempty ∧ ∃ b, ∀ z ∈ S₁, b + z ∈ R

namespace L1Data

/-- **Assembly: an `L1Data` is exactly what leaf L1 has to produce.**

The two conjuncts absent from `L1Data` are discharged here: `∃ e, ξ' = T e ξ` by `⟨L.e, rfl⟩`,
and `ξ' ∈ orbitClosure ξ` by `T_mem_orbitClosure` (`Nivat/Defs/Orbit.lean:49`).

The statement below is a verbatim copy of the conclusion of `case1_claim46_and_selection`
(`RegionSteps.lean:876-970`); any drift between the two is a compile error at the call site,
not a silent mismatch. -/
theorem toConclusion (L : L1Data ξ S) :
    ∃ ξ' ∈ orbitClosure ξ, ∃ (u u' : ℤ × ℤ) (Q : Finset (ℤ × ℤ)) (τ : ℤ) (pw : ℕ)
      (B : Finset (ℤ × ℤ)) (R R' : Set (ℤ × ℤ)) (c : ℤ) (S₁ : Finset (ℤ × ℤ)),
      Nivat.Colle.IsGeneratingSet ξ S₁ ∧
      (∃ e : ℤ × ℤ, ξ' = T e ξ) ∧
      Q ⊆ S₁ ∧
      (∃ (n : ℝ × ℝ) (cmax : ℝ),
        n ≠ 0 ∧
        inner2 n u' = 0 ∧
        (∀ z ∈ S₁, inner2 n z ≤ cmax) ∧
        (Nivat.R2.face S₁ n cmax).Nonempty ∧
        Q = S₁.filter fun z => inner2 n z < cmax) ∧
      det u u' ≠ 0 ∧
      Primitive u' ∧
      P ξ S₁ ≤ P ξ Q + pw ∧
      (∀ g ∈ B, ∀ i : ℕ, i < pw → g + (i : ℤ) • u' ∈ Q) ∧
      c ≠ 0 ∧
      Colle41.PeriodOn ξ' R (c • u) ∧
      Colle41.IsRegion R u u' ∧
      R ⊂ R' ∧
      ¬ Colle41.PeriodOn ξ' R' (c • u) ∧
      (∀ t : ℤ, τ ≤ t → ∀ z ∈ Q, t • u' + z ∈ R ∧ t • u' + z + c • u ∈ R) ∧
      (∀ g ∈ S₁, g ∉ Q → ∀ t₀ : ℤ, τ ≤ t₀ →
        Colle41.PeriodOn ξ' R (c • u) →
        (∀ t : ℤ, t₀ ≤ t → ξ' (t • u' + g + c • u) = ξ' (t • u' + g)) →
        Colle41.PeriodOn ξ' R' (c • u)) ∧
      (B.Nonempty ∧ ∃ b, ∀ z ∈ S₁, b + z ∈ R) :=
  ⟨T L.e ξ, T_mem_orbitClosure ξ L.e, L.u, L.u', L.Q, L.τ, L.pw, L.B, L.R, L.R', L.c, L.S₁,
    L.hS₁gen, ⟨L.e, rfl⟩, L.hQS, L.hQ_edge, L.hdet, L.hu'_prim, L.hPQ, L.hBQ, L.hc,
    L.hRper, L.hR_region, L.hRR', L.hnonper, L.hline, L.hstraddle, L.hbase⟩

end L1Data

end Nivat.ColleReg
