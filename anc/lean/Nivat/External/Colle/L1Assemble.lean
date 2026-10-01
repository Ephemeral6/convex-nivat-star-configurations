/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.L1Fields
import Nivat.External.Colle.L1Region
import Nivat.External.Colle.L1Cut
import Nivat.External.Colle.ONEDRational

/-!
# `L1Assemble`: the single assembly point of leaf L1, and the residual gap it measures

Leaf **L1** is the `sorry` on `exists_L1Data` (`RegionSteps.lean:894`), whose conclusion is
`Nonempty (Nivat.ColleReg.L1Data ξ S)`.  `L1Data` (`L1Data.lean:71`) splits Claim 4.6's
sixteen-conjunct existential into eleven data fields and fifteen named proof obligations, and
`L1Data.toConclusion` (`L1Data.lean:148`) reassembles one into that existential verbatim.

Between them, `L1Fields.lean`, `L1Region.lean`, `L1Complexity.lean`, `L1Straddle.lean` and
`ONEDRational.lean` carry about 3400 lines of supporting material.  **None of it had a
consumer**: no declaration anywhere in the tree took those lemmas and produced an `L1Data`.
This file is that consumer, and it exists to make the residual gap a single countable thing
rather than a scattered pile.

`ofPieces` concludes with the literal `L1Data ξ S` — not a variant record and not a
restatement — so `L1Data.toConclusion` applies to its output with no adapter, and
`nonempty_of_pieces` below is syntactically the conclusion of `exists_L1Data`.

## What `ofPieces` discharges, and what it does not

Measured against `L1Data`'s fifteen obligations:

| conjunct | `L1Data` field | status in `ofPieces` |
|---|---|---|
| 3 | `hQS` | **discharged** — `Finset.filter_subset`, `Q` is derived |
| 4 | `hQ_edge` | **repackaged** into `hn0/hnu'/hle/hface`; `Q` by `rfl` |
| 7 | `hPQ` | **discharged** — `Nivat.L1Complexity.hPQ_of_hQ_edge`, at the pinned `pw` |
| 8 | `hBQ` | **discharged** modulo the one numeric hypothesis `hcard` — `L1Data.faceIsRun` |
| 10 | `hRper` | **discharged** — `Nivat.L1Region.exists_greatest_periodOn` |
| 11 | `hR_region` | **discharged** — `RegionFamily.isRegion` |
| 12 | `hRR'` | **discharged** — `RegionFamily.grow` |
| 13 | `hnonper` | **discharged** — the second half of `exists_greatest_periodOn` |
| 14 | `hline` | **weakened** to level `0` — `RegionFamily.line_of_line_zero` |
| 16 | `hbase` | **weakened** to level `0` — `RegionFamily.base_of_base_zero` + `weakBase_of_strong` |
| 1 | `hS₁gen` | hypothesis (but see `isGeneratingSet_image_zero` — producible at `v = 0`) |
| 5 | `hdet` | hypothesis |
| 6 | `hu'_prim` | hypothesis |
| 9 | `hc` | hypothesis |
| 15 | `hstraddle` | hypothesis, **weakened** to "at every maximal index" |

So six of the fifteen leave no trace in the signature at all (3, 7, 10, 11, 12, 13), three more
are weakened (8, 14, 16), one is repackaged (4), and five survive as hypotheses (1, 5, 6, 9, 15).
`ofPieces` has **fourteen** residual hypotheses, bundled as the fourteen fields of `Residual`
below; the count is read off `#check @Residual.mk`, not off this paragraph.

## Discharged vs. relocated

⚠ A field filled by a lemma whose own hypotheses nobody can supply is **not discharged, it is
relocated**.  The six conjuncts above that vanish from the signature split two ways:

* **3, 7, 8** are discharged against inputs the leaf already has.  Conjunct 7 runs through
  `Nivat.L1Complexity.hPQ_of_hQ_edge`, whose only non-trivial hypothesis is `hdef` — and `hdef`
  is a **binder of `exists_L1Data` itself** (`RegionSteps.lean:886-893`), in the very shape the
  lemma wants (`∀ (n : ℝ × ℝ) (cmax cmin : ℝ), …`).  Conjunct 8 runs through `L1Data.faceIsRun`,
  whose hypotheses are `LatticeConvex S₁` (from conjunct 1), `Primitive u'` (the leaf's
  `hvl_prim`), and the two normal conditions that are conjunct 4's own components.
* **10, 11, 12, 13** are discharged against `F : RegionFamily`, which is an *input*.  They are
  therefore **relocated into `F`'s four proof fields**, `union_not` being the one with content.
  `ofCutPieces` below removes `F` from the interface by routing it through
  `Nivat.L1Region.ofCut`, so that the relocation is visible as eight further arguments rather
  than hidden inside a bundled structure.  That is the honest form of the measurement.

## The trap this file is written against

A constructor whose hypotheses are strong enough to be trivially satisfiable measures nothing
and still compiles with a clean `#print axioms`.  Two guards were applied:

* **No hypothesis of `ofPieces` is the conjunct it produces.**  Conjuncts 3, 7 and 10–13 do not
  appear in the signature in any form; conjunct 8 appears only as the *cardinality comparison*
  `hcard`, with the contiguity and the membership both supplied by `faceIsRun`.
* **The weakenings are weakenings, not restatements.**  Conjunct 15 is demanded only at indices
  that are actually maximal for the family, which is strictly less than demanding it at every
  index; `Nivat.L1Region.not_straddle_four` (`L1Region.lean:460`) shows that at least one index
  of a real family fails it, so the hypothesis is not vacuous either.

⚠ **Non-vacuity of the whole bundle is NOT established.**  No `L1Data` is known to exist, here
or anywhere in the tree, and this file does not build one.  What is established is the
*relative* statement: whoever supplies the inputs below gets an `L1Data`, and hence leaf L1's
conclusion.

## Which residual is deepest

`hstraddle` (conjunct 15) among the fourteen, and `hinf` (`¬ PeriodOn (T e ξ) Rinf (c • u)`)
once `F` is unfolded through `ofCutPieces`.  `hstraddle` is the only residual that mentions the
*pair* `(R, R')` selected by the maximality argument, and `not_straddle_four` proves it does not
transport along the family, so no level-`0` form of it is available the way conjuncts 14 and 16
have one.

## Second pass (2026-09-19): fourteen → eight

Two things in the first pass were wrong, and both are corrected below in the kernel:

* "Nothing in the tree transports `IsGeneratingSet` along a translation" was a grep result,
  not a fact.  `isGeneratingSet_image` proves the transport from two lemmas that were already in
  the import closure.  So `gen` is free at every translate, not only at `v = 0`.
* Five of the fourteen (`n0`, `nu'`, `le`, `face`, `minne`) were **data**, not obligations: the
  normal is `±perp u'` and the levels are the extrema of `inner2 n` over the non-empty `S₁`.
  `ofDerived` derives them; `DerivedResidual` (eight fields, `#check @DerivedResidual.mk`) is
  what is left.

Also answered: **whether `S₁` may be `S`** (section `Translate`).  `L1Data` is
translation-equivariant in every field (`translate`, no side condition since the 2026-09-19
weakening of conjunct 16), so `S₁ := S` is free (`exists_window_eq`).  The section docstring
keeps the strong-form analysis, under which conjunct 16 alone carried an absolute-position
cost.
-/

set_option autoImplicit false

namespace Nivat.ColleReg

open Nivat Nivat.Colle35

namespace L1Data

/-- **Conjunct 1 is producible at the leaf, for the degenerate translate.**

`ofPieces` asks for `IsGeneratingSet ξ S₁` where `S₁ = S.image (· + v)`, while `exists_L1Data`
supplies `hSgen : IsGeneratingSet ξ S`.  At `v = 0` the two coincide, so a caller that does not
need to move the window has conjunct 1 for free.

⚠ For `v ≠ 0` this is **not** available: nothing in the tree transports `IsGeneratingSet` along
a translation, and the only occurrence of the idea is a docstring (`L1Straddle.lean:426`).  So
conjunct 1 is a genuine residual exactly when the argument needs to move the window.

🔴 **Correction (2026-09-19, kept per `PROTOCOL.md` §14):** the paragraph above is wrong.
`isGeneratingSet_image` below proves the transport for every `v`, from
`Nivat.Claim47.generatesAt_translate` and `Nivat.LatticeConvex.translate`, both already in the
import closure.  Conjunct 1 is never a residual. -/
theorem isGeneratingSet_image_zero {ξ : Config ℤ} {S : Finset (ℤ × ℤ)}
    (h : Nivat.Colle.IsGeneratingSet ξ S) :
    Nivat.Colle.IsGeneratingSet ξ (S.image (· + (0 : ℤ × ℤ))) := by
  simpa using h

/-! ### Conjunct 16 in its weak form (2026-09-19)

`L1Data.hbase` is `B.Nonempty ∧ ∃ b, ∀ z ∈ S₁, b + z ∈ R`.  The two lemmas below are the only
transport it needs: the strong form implies it, and it lifts along a `RegionFamily` exactly as
`RegionFamily.base_of_base_zero` (`L1Region.lean:373`) lifts the strong form. -/

/-- The retired strong conjunct 16 implies the weak one. -/
theorem weakBase_of_strong {B S₁ : Finset (ℤ × ℤ)} {R : Set (ℤ × ℤ)}
    (h : ∃ b ∈ B, ∀ z ∈ S₁, b + z ∈ R) : B.Nonempty ∧ ∃ b, ∀ z ∈ S₁, b + z ∈ R :=
  let ⟨b, hbB, hb⟩ := h
  ⟨⟨b, hbB⟩, b, hb⟩

/-- Weak conjunct 16 at level `0` gives it at every level of the family. -/
theorem weakBase_of_weakBase_zero {x : Config ℤ} {u u' : ℤ × ℤ} {c : ℤ}
    (F : Nivat.L1Region.RegionFamily x u u' c) {B S₁ : Finset (ℤ × ℤ)}
    (h0 : B.Nonempty ∧ ∃ b, ∀ z ∈ S₁, b + z ∈ F.R 0) (n : ℕ) :
    B.Nonempty ∧ ∃ b, ∀ z ∈ S₁, b + z ∈ F.R n :=
  let ⟨hB, b, hb⟩ := h0
  ⟨hB, b, fun z hz => F.monotone (Nat.zero_le n) (hb z hz)⟩

/-- **The assembly point of leaf L1.**

Every input is either data, one of the leaf's own binders (`hdef`), or a named residual
obligation.  The conclusion is the literal `L1Data ξ S`, so `toConclusion` applies with no
adapter.  Two inputs are consumed through existentials — the maximal index `N` of the region
family and the anchor `z₀` of the `u'`-run in the bottom face — which is why the definition is
`noncomputable` (`Exists.choose`) rather than a `theorem`.

**Data** (no proof content): `e u u' v`, `c τ`, `n cmax cmin`, `S₁ Q` with their defining
equations `hS₁`, `hQ`, and the family `F`.

**Free at the leaf**: `hdef`, a binder of `exists_L1Data` (`RegionSteps.lean:886-893`).

**Residual obligations**: the remaining fourteen arguments.  `hn0`, `hnu'`, `hle`, `hface` are
the four components of conjunct 4 with `Q` derived; `hminne`, `hlt`, `hcard` replace conjunct
8; `hline0` and `hbase0` are conjuncts 14 and 16 at level `0`; `hstraddle` is conjunct 15 at
the maximal indices; `hS₁gen`, `hdet`, `hu'_prim`, `hc` are conjuncts 1, 5, 6, 9 unchanged.

`hbase0` is quantified over the whole bottom face rather than stated at one point: the run
anchor `z₀` is produced inside the proof by `faceIsRun`, so the caller has no name for it.
That is a genuine strengthening of conjunct 16 and is the price of deriving `B` rather than
taking it. -/
noncomputable def ofPieces {ξ : Config ℤ} {S : Finset (ℤ × ℤ)}
    (e u u' v : ℤ × ℤ) (c τ : ℤ) (n : ℝ × ℝ) (cmax cmin : ℝ) (S₁ Q : Finset (ℤ × ℤ))
    (F : Nivat.L1Region.RegionFamily (T e ξ) u u' c)
    (hS₁ : S₁ = S.image (· + v))
    (hQ : Q = S₁.filter fun z => inner2 n z < cmax)
    (hdef : ∀ (m : ℝ × ℝ) (a b : ℝ),
      (∀ z ∈ S, inner2 m z ≤ a) → (Nivat.R2.face S m a).Nonempty →
      (∀ z ∈ S, b ≤ inner2 m z) → (Nivat.R2.face S m b).Nonempty →
        P ξ S - P ξ (S.filter fun z => inner2 m z < a) ≤ (Nivat.R2.face S m a).card - 1 ∧
        P ξ S - P ξ (S.filter fun z => b < inner2 m z) ≤ (Nivat.R2.face S m b).card - 1)
    -- conjunct 1
    (hS₁gen : Nivat.Colle.IsGeneratingSet ξ S₁)
    -- conjunct 4, in components
    (hn0 : n ≠ 0)
    (hnu' : inner2 n u' = 0)
    (hle : ∀ z ∈ S₁, inner2 n z ≤ cmax)
    (hface : (Nivat.R2.face S₁ n cmax).Nonempty)
    -- conjunct 8, via the opposite face
    (hminne : (Nivat.R2.face S₁ n cmin).Nonempty)
    (hlt : cmin < cmax)
    (hcard : (Nivat.R2.face S₁ n cmax).card - 1 ≤ (Nivat.R2.face S₁ n cmin).card)
    -- conjuncts 5, 6, 9
    (hdet : det u u' ≠ 0)
    (hu'_prim : Primitive u')
    (hc : c ≠ 0)
    -- conjuncts 14 and 16, at level 0
    (hline0 : ∀ t : ℤ, τ ≤ t → ∀ z ∈ Q, t • u' + z ∈ F.R 0 ∧ t • u' + z + c • u ∈ F.R 0)
    (hbase0 : ∀ b ∈ Nivat.R2.face S₁ n cmin, ∀ z ∈ S₁, b + z ∈ F.R 0)
    -- conjunct 15, at the maximal indices only
    (hstraddle : ∀ N : ℕ, Colle41.PeriodOn (T e ξ) (F.R N) (c • u) →
      ¬ Colle41.PeriodOn (T e ξ) (F.R (N + 1)) (c • u) →
      Nivat.L1Region.Straddle (T e ξ) (F.R N) (F.R (N + 1)) S₁ Q u u' c τ) :
    L1Data ξ S := by
  classical
  have hgp : ∃ N : ℕ, Colle41.PeriodOn (T e ξ) (F.R N) (c • u) ∧
      ¬ Colle41.PeriodOn (T e ξ) (F.R (N + 1)) (c • u) :=
    Nivat.L1Region.exists_greatest_periodOn F.monotone F.base F.union_not
  have hrun : ∃ z₀, z₀ ∈ Nivat.R2.face S₁ n cmin ∧
      ∀ i : ℕ, i < (Nivat.R2.face S₁ n cmin).card →
        z₀ + (i : ℤ) • u' ∈ Nivat.R2.face S₁ n cmin :=
    faceIsRun (cmax := cmin) (latticeConvex_of_isGeneratingSet hS₁gen) hu'_prim hn0 hnu' hminne
  refine { e := e, u := u, u' := u', Q := Q, τ := τ
           pw := (Nivat.R2.face S₁ n cmax).card - 1
           B := {hrun.choose}
           R := F.R hgp.choose
           R' := F.R (hgp.choose + 1)
           c := c, S₁ := S₁
           hS₁gen := hS₁gen
           hQS := ?_
           hQ_edge := ⟨n, cmax, hn0, hnu', hle, hface, hQ⟩
           hdet := hdet
           hu'_prim := hu'_prim
           hPQ := Nivat.L1Complexity.hPQ_of_hQ_edge hS₁ hdef hle hface hQ
           hBQ := ?_
           hc := hc
           hRper := hgp.choose_spec.1
           hR_region := F.isRegion hgp.choose
           hRR' := F.grow hgp.choose
           hnonper := hgp.choose_spec.2
           hline := F.line_of_line_zero hline0 hgp.choose
           hstraddle := hstraddle hgp.choose hgp.choose_spec.1 hgp.choose_spec.2
           hbase := ?_ }
  · rw [hQ]
    exact Finset.filter_subset _ _
  · intro g hg i hi
    rw [Finset.mem_singleton] at hg
    subst hg
    have hmem := hrun.choose_spec.2 i (lt_of_lt_of_le hi hcard)
    rw [Nivat.R2.mem_face] at hmem
    rw [hQ]
    exact Finset.mem_filter.mpr ⟨hmem.1, by rw [hmem.2]; exact hlt⟩
  · exact weakBase_of_strong (F.base_of_base_zero
      ⟨hrun.choose, Finset.mem_singleton_self _, hbase0 _ hrun.choose_spec.1⟩ hgp.choose)

/-- **`ofPieces` in the exact shape leaf L1 asks for.**

`exists_L1Data` (`RegionSteps.lean:894`) concludes `Nonempty (Nivat.ColleReg.L1Data ξ S)`;
this is that statement, so the leaf is `nonempty_of_pieces …` applied to the inputs and nothing
else.  Stated separately from `ofPieces` so that the stronger (choice-free-to-state) form
stays available to callers that want to name the fields. -/
theorem nonempty_of_pieces {ξ : Config ℤ} {S : Finset (ℤ × ℤ)}
    (e u u' v : ℤ × ℤ) (c τ : ℤ) (n : ℝ × ℝ) (cmax cmin : ℝ) (S₁ Q : Finset (ℤ × ℤ))
    (F : Nivat.L1Region.RegionFamily (T e ξ) u u' c)
    (hS₁ : S₁ = S.image (· + v))
    (hQ : Q = S₁.filter fun z => inner2 n z < cmax)
    (hdef : ∀ (m : ℝ × ℝ) (a b : ℝ),
      (∀ z ∈ S, inner2 m z ≤ a) → (Nivat.R2.face S m a).Nonempty →
      (∀ z ∈ S, b ≤ inner2 m z) → (Nivat.R2.face S m b).Nonempty →
        P ξ S - P ξ (S.filter fun z => inner2 m z < a) ≤ (Nivat.R2.face S m a).card - 1 ∧
        P ξ S - P ξ (S.filter fun z => b < inner2 m z) ≤ (Nivat.R2.face S m b).card - 1)
    (hS₁gen : Nivat.Colle.IsGeneratingSet ξ S₁)
    (hn0 : n ≠ 0) (hnu' : inner2 n u' = 0)
    (hle : ∀ z ∈ S₁, inner2 n z ≤ cmax) (hface : (Nivat.R2.face S₁ n cmax).Nonempty)
    (hminne : (Nivat.R2.face S₁ n cmin).Nonempty) (hlt : cmin < cmax)
    (hcard : (Nivat.R2.face S₁ n cmax).card - 1 ≤ (Nivat.R2.face S₁ n cmin).card)
    (hdet : det u u' ≠ 0) (hu'_prim : Primitive u') (hc : c ≠ 0)
    (hline0 : ∀ t : ℤ, τ ≤ t → ∀ z ∈ Q, t • u' + z ∈ F.R 0 ∧ t • u' + z + c • u ∈ F.R 0)
    (hbase0 : ∀ b ∈ Nivat.R2.face S₁ n cmin, ∀ z ∈ S₁, b + z ∈ F.R 0)
    (hstraddle : ∀ N : ℕ, Colle41.PeriodOn (T e ξ) (F.R N) (c • u) →
      ¬ Colle41.PeriodOn (T e ξ) (F.R (N + 1)) (c • u) →
      Nivat.L1Region.Straddle (T e ξ) (F.R N) (F.R (N + 1)) S₁ Q u u' c τ) :
    Nonempty (L1Data ξ S) :=
  ⟨ofPieces e u u' v c τ n cmax cmin S₁ Q F hS₁ hQ hdef hS₁gen hn0 hnu' hle hface
    hminne hlt hcard hdet hu'_prim hc hline0 hbase0 hstraddle⟩

/-! ## The residual, stated as one proposition

`ofPieces` has fourteen residual obligations.  `Residual` below bundles them so that "what leaf
L1 still owes, given the cut data and a region family" is a single named `Prop` that can be
`#check`ed, refuted, or handed to a worker — and so that the count is read off
`#check @Residual.mk` rather than hand-counted in a docstring.  (It was hand-counted as
"thirteen" in the first draft of this file, and `#check` corrected it — `CLAUDE.md` hard
rule 3.)

`hdef` is deliberately **not** a field: it is a binder of `exists_L1Data`
(`RegionSteps.lean:886-893`), so the leaf has it for free and it is not part of the gap.
-/

/-- **Everything `ofPieces` still asks for.**  Fourteen fields; the surviving conjuncts are
1 (`gen`), 4 (`n0`/`nu'`/`le`/`face`), 5 (`det'`), 6 (`prim`), 8 (`minne`/`lt`/`card`),
9 (`c0`), 14 (`line0`), 15 (`straddle`) and 16 (`base0`).

⚠ The region family `F` is a *parameter* of this structure, and carries four proof fields of
its own (`L1Region.lean:131-142`), `union_not` among them.  "Fourteen" counts the fields
below, not those; `ofCutPieces` is the form in which those four are also visible. -/
structure Residual {ξ : Config ℤ} (u u' : ℤ × ℤ) (c τ : ℤ) (n : ℝ × ℝ) (cmax cmin : ℝ)
    (S₁ Q : Finset (ℤ × ℤ)) {e : ℤ × ℤ}
    (F : Nivat.L1Region.RegionFamily (T e ξ) u u' c) : Prop where
  /-- Conjunct 1. -/
  gen : Nivat.Colle.IsGeneratingSet ξ S₁
  /-- Conjunct 4, first component. -/
  n0 : n ≠ 0
  /-- Conjunct 4, second component. -/
  nu' : inner2 n u' = 0
  /-- Conjunct 4, third component. -/
  le : ∀ z ∈ S₁, inner2 n z ≤ cmax
  /-- Conjunct 4, fourth component. -/
  face : (Nivat.R2.face S₁ n cmax).Nonempty
  /-- Conjunct 8: the bottom face is non-empty… -/
  minne : (Nivat.R2.face S₁ n cmin).Nonempty
  /-- …strictly below the cut… -/
  lt : cmin < cmax
  /-- …and at least as long as the run the top cut demands.  This is the whole geometric
  content of conjunct 8 after `faceIsRun`. -/
  card : (Nivat.R2.face S₁ n cmax).card - 1 ≤ (Nivat.R2.face S₁ n cmin).card
  /-- Conjunct 5. -/
  det' : det u u' ≠ 0
  /-- Conjunct 6. -/
  prim : Primitive u'
  /-- Conjunct 9. -/
  c0 : c ≠ 0
  /-- Conjunct 14 at level `0`. -/
  line0 : ∀ t : ℤ, τ ≤ t → ∀ z ∈ Q, t • u' + z ∈ F.R 0 ∧ t • u' + z + c • u ∈ F.R 0
  /-- Conjunct 16 at level `0`, over the whole bottom face. -/
  base0 : ∀ b ∈ Nivat.R2.face S₁ n cmin, ∀ z ∈ S₁, b + z ∈ F.R 0
  /-- Conjunct 15, at the maximal indices only.  The deepest of the fourteen: it is the only
  one naming the *pair* the maximality argument selects, and
  `Nivat.L1Region.not_straddle_four` (`L1Region.lean:460`) rules out a level-`0` form. -/
  straddle : ∀ N : ℕ, Colle41.PeriodOn (T e ξ) (F.R N) (c • u) →
    ¬ Colle41.PeriodOn (T e ξ) (F.R (N + 1)) (c • u) →
    Nivat.L1Region.Straddle (T e ξ) (F.R N) (F.R (N + 1)) S₁ Q u u' c τ

/-- **`ofPieces` at the bundled interface.**  The gap between leaf L1 and the tree as it stands
is exactly `Residual` — plus the leaf's own binder `hdef` and the choice of data. -/
noncomputable def ofResidual {ξ : Config ℤ} {S : Finset (ℤ × ℤ)}
    (e u u' v : ℤ × ℤ) (c τ : ℤ) (n : ℝ × ℝ) (cmax cmin : ℝ) (S₁ Q : Finset (ℤ × ℤ))
    (F : Nivat.L1Region.RegionFamily (T e ξ) u u' c)
    (hS₁ : S₁ = S.image (· + v))
    (hQ : Q = S₁.filter fun z => inner2 n z < cmax)
    (hdef : ∀ (m : ℝ × ℝ) (a b : ℝ),
      (∀ z ∈ S, inner2 m z ≤ a) → (Nivat.R2.face S m a).Nonempty →
      (∀ z ∈ S, b ≤ inner2 m z) → (Nivat.R2.face S m b).Nonempty →
        P ξ S - P ξ (S.filter fun z => inner2 m z < a) ≤ (Nivat.R2.face S m a).card - 1 ∧
        P ξ S - P ξ (S.filter fun z => b < inner2 m z) ≤ (Nivat.R2.face S m b).card - 1)
    (H : Residual u u' c τ n cmax cmin S₁ Q F) :
    L1Data ξ S :=
  ofPieces e u u' v c τ n cmax cmin S₁ Q F hS₁ hQ hdef H.gen H.n0 H.nu' H.le H.face
    H.minne H.lt H.card H.det' H.prim H.c0 H.line0 H.base0 H.straddle

/-- **Leaf L1's conclusion from the residual.**  This is the composite that puts `L1Fields`,
`L1Region` and `L1Complexity` on leaf L1's dependency path.

The statement is *not* restated here: it is read off `toConclusion`'s own type, so any drift
between `L1Data` and `RegionSteps.lean` remains a compile error at exactly one place. -/
theorem conclusion_of_residual {ξ : Config ℤ} {S : Finset (ℤ × ℤ)}
    (e u u' v : ℤ × ℤ) (c τ : ℤ) (n : ℝ × ℝ) (cmax cmin : ℝ) (S₁ Q : Finset (ℤ × ℤ))
    (F : Nivat.L1Region.RegionFamily (T e ξ) u u' c)
    (hS₁ : S₁ = S.image (· + v))
    (hQ : Q = S₁.filter fun z => inner2 n z < cmax)
    (hdef : ∀ (m : ℝ × ℝ) (a b : ℝ),
      (∀ z ∈ S, inner2 m z ≤ a) → (Nivat.R2.face S m a).Nonempty →
      (∀ z ∈ S, b ≤ inner2 m z) → (Nivat.R2.face S m b).Nonempty →
        P ξ S - P ξ (S.filter fun z => inner2 m z < a) ≤ (Nivat.R2.face S m a).card - 1 ∧
        P ξ S - P ξ (S.filter fun z => b < inner2 m z) ≤ (Nivat.R2.face S m b).card - 1)
    (H : Residual u u' c τ n cmax cmin S₁ Q F) :
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
  toConclusion (ofResidual e u u' v c τ n cmax cmin S₁ Q F hS₁ hQ hdef H)

/-! ## `F` unfolded: the measurement with nothing bundled

`Residual`'s count of fourteen holds `F : RegionFamily` fixed, and `F` is not free — it carries
`grow`, `isRegion`, `base`, `union_not`.  `ofCutPieces` therefore repeats the assembly with `F`
replaced by the inputs of `Nivat.L1Region.ofCut` (`L1Region.lean:238`), Collé's own half-plane
slicing.  Nothing is proved here that `ofPieces` did not prove; the point is that the arity is
now the honest one, and that the deepest residual of the whole leaf becomes visible as a named
argument: `hinf : ¬ Colle41.PeriodOn (T e ξ) Rinf (c • u)`.

⚠ Note the **two different normals**.  Conjunct 4 cuts `S₁` with a real normal `n : ℝ × ℝ`;
`ofCut` slices the region with an integer normal `m : ℤ × ℤ`.  Nothing here forces them to be
parallel, and `ofCutPieces` does not relate them — the paper's `m` and `n` are the same
direction, so a producer will have to supply that agreement itself.  It is not an omission that
can be repaired inside this file. -/

/-- **The assembly with the region family unfolded into Collé's slicing.**

Same output as `ofPieces`, with `F` replaced by `Nivat.L1Region.ofCut`'s eight arguments:
`hR hmu' hmu hlev hexh hgap hcut0 hinf`.  Of these, `hmu'`, `hmu`, `hlev`, `hexh`, `hgap` are
slicing data; `hR`, `hcut0`, `hinf` carry the content, and `hinf` is the one the rest of the
argument exists to produce. -/
noncomputable def ofCutPieces {ξ : Config ℤ} {S : Finset (ℤ × ℤ)}
    (e u u' v m : ℤ × ℤ) (c τ : ℤ) (lev : ℕ → ℤ) (Rinf : Set (ℤ × ℤ))
    (n : ℝ × ℝ) (cmax cmin : ℝ) (S₁ Q : Finset (ℤ × ℤ))
    (hS₁ : S₁ = S.image (· + v))
    (hQ : Q = S₁.filter fun z => inner2 n z < cmax)
    (hdef : ∀ (m : ℝ × ℝ) (a b : ℝ),
      (∀ z ∈ S, inner2 m z ≤ a) → (Nivat.R2.face S m a).Nonempty →
      (∀ z ∈ S, b ≤ inner2 m z) → (Nivat.R2.face S m b).Nonempty →
        P ξ S - P ξ (S.filter fun z => inner2 m z < a) ≤ (Nivat.R2.face S m a).card - 1 ∧
        P ξ S - P ξ (S.filter fun z => b < inner2 m z) ≤ (Nivat.R2.face S m b).card - 1)
    -- the `ofCut` inputs, in place of `F`
    (hR : Colle41.IsRegion Rinf u u')
    (hmu' : Nivat.LE2.dot m u' = 0) (hmu : 0 < Nivat.LE2.dot m u)
    (hlev : Antitone lev) (hexh : ∀ b : ℤ, ∃ k, lev k ≤ b)
    (hgap : ∀ k : ℕ, ∃ z ∈ Rinf, lev (k + 1) ≤ Nivat.LE2.dot m z ∧ Nivat.LE2.dot m z < lev k)
    (hcut0 : Colle41.PeriodOn (T e ξ) (Nivat.L1Region.cut Rinf m lev 0) (c • u))
    (hinf : ¬ Colle41.PeriodOn (T e ξ) Rinf (c • u))
    -- the fourteen of `Residual`, with `F.R` spelled out as `cut Rinf m lev`
    (hS₁gen : Nivat.Colle.IsGeneratingSet ξ S₁)
    (hn0 : n ≠ 0) (hnu' : inner2 n u' = 0)
    (hle : ∀ z ∈ S₁, inner2 n z ≤ cmax) (hface : (Nivat.R2.face S₁ n cmax).Nonempty)
    (hminne : (Nivat.R2.face S₁ n cmin).Nonempty) (hlt : cmin < cmax)
    (hcard : (Nivat.R2.face S₁ n cmax).card - 1 ≤ (Nivat.R2.face S₁ n cmin).card)
    (hdet : det u u' ≠ 0) (hu'_prim : Primitive u') (hc : c ≠ 0)
    (hline0 : ∀ t : ℤ, τ ≤ t → ∀ z ∈ Q,
      t • u' + z ∈ Nivat.L1Region.cut Rinf m lev 0 ∧
        t • u' + z + c • u ∈ Nivat.L1Region.cut Rinf m lev 0)
    (hbase0 : ∀ b ∈ Nivat.R2.face S₁ n cmin, ∀ z ∈ S₁,
      b + z ∈ Nivat.L1Region.cut Rinf m lev 0)
    (hstraddle : ∀ N : ℕ,
      Colle41.PeriodOn (T e ξ) (Nivat.L1Region.cut Rinf m lev N) (c • u) →
      ¬ Colle41.PeriodOn (T e ξ) (Nivat.L1Region.cut Rinf m lev (N + 1)) (c • u) →
      Nivat.L1Region.Straddle (T e ξ) (Nivat.L1Region.cut Rinf m lev N)
        (Nivat.L1Region.cut Rinf m lev (N + 1)) S₁ Q u u' c τ) :
    L1Data ξ S :=
  ofPieces e u u' v c τ n cmax cmin S₁ Q
    (Nivat.L1Region.ofCut hR hmu' hmu hlev hexh hgap hcut0 hinf)
    hS₁ hQ hdef hS₁gen hn0 hnu' hle hface hminne hlt hcard hdet hu'_prim hc
    hline0 hbase0 hstraddle

/-! ## Callability at the leaf

`ofPieces` is only worth its arity if the arguments it asks for are ones
`exists_L1Data` can actually supply.  `nonempty_of_leafBinders` checks that in the kernel for
the three binders that are supposed to be free: `hSgen`, `hvl_prim` and `hdef`.  It takes
them in exactly the form `exists_L1Data` (`RegionSteps.lean:880-893`) has them, fixes
`u' := vl` and `v := 0`, and asks for **twelve** residual obligations instead of fourteen —
`gen` and `prim` are gone because the leaf already has them.

⚠ `v := 0` is what makes `gen` free.  For a genuinely translated window there is no producer:
nothing in the tree transports `IsGeneratingSet` along a translation.  The twelve are therefore
the count *for the untranslated window*; a proof that needs to move `S` pays thirteen.

🔴 **Correction (2026-09-19, §14):** superseded by `isGeneratingSet_image` — `gen` is free at
every `v`.  The twelve-count stands; the "pays thirteen" clause does not.  And the twelve are
themselves superseded by `ofDerived`'s eight (`DerivedResidual`), which additionally derives
the cut.
-/

/-- **The leaf's own binders, plugged in.**  `hSgen`, `hvl_prim` and `hdef` are binders of
`exists_L1Data`; this discharges conjuncts 1 and 6 from them and leaves twelve obligations. -/
theorem nonempty_of_leafBinders {ξ : Config ℤ} {S : Finset (ℤ × ℤ)} {vl : ℤ × ℤ}
    (hSgen : Nivat.Colle.IsGeneratingSet ξ S) (hvl_prim : Primitive vl)
    (hdef : ∀ (n : ℝ × ℝ) (cmax cmin : ℝ),
      (∀ z ∈ S, inner2 n z ≤ cmax) → (Nivat.R2.face S n cmax).Nonempty →
      (∀ z ∈ S, cmin ≤ inner2 n z) → (Nivat.R2.face S n cmin).Nonempty →
        P ξ S - P ξ (S.filter fun z => inner2 n z < cmax) ≤
          (Nivat.R2.face S n cmax).card - 1 ∧
        P ξ S - P ξ (S.filter fun z => cmin < inner2 n z) ≤
          (Nivat.R2.face S n cmin).card - 1)
    (e u : ℤ × ℤ) (c τ : ℤ) (n : ℝ × ℝ) (cmax cmin : ℝ)
    (F : Nivat.L1Region.RegionFamily (T e ξ) u vl c)
    (H : Residual u vl c τ n cmax cmin (S.image (· + (0 : ℤ × ℤ)))
      ((S.image (· + (0 : ℤ × ℤ))).filter fun z => inner2 n z < cmax) F) :
    Nonempty (L1Data ξ S) :=
  ⟨ofPieces e u vl 0 c τ n cmax cmin _ _ F rfl rfl hdef
    (isGeneratingSet_image_zero hSgen) H.n0 H.nu' H.le H.face H.minne H.lt H.card
    H.det' hvl_prim H.c0 H.line0 H.base0 H.straddle⟩

/-! ## Conjunct 1 is translation-invariant, so it is free for every `v`

`isGeneratingSet_image_zero` above only covers `v = 0`, and its docstring says nothing in the
tree transports `IsGeneratingSet` along a translation.  The second half is wrong: the two
ingredients are already in the import closure — `Nivat.Claim47.generatesAt_translate`
(`Claim47Core.lean:487`) moves `GeneratesAt` to any base point through `T`-conjugation, and
`Nivat.LatticeConvex.translate` (`AppendixD.lean:109`) moves lattice convexity.  Only the
`Finset.erase`/`image` bookkeeping was missing.

Consequence for the count: `hS₁gen` is producible from the leaf's binder `hSgen` for **every**
translate, not only the degenerate one, so `gen` is not a residual obligation at any `v`.
-/

/-- **Conjunct 1 transports along any translation.**  `IsGeneratingSet ξ S → IsGeneratingSet ξ
(S + v)`, because `orbitClosure ξ` is closed under `T` and `GeneratesAt` is stated through it. -/
theorem isGeneratingSet_image {ξ : Config ℤ} {S : Finset (ℤ × ℤ)}
    (h : Nivat.Colle.IsGeneratingSet ξ S) (v : ℤ × ℤ) :
    Nivat.Colle.IsGeneratingSet ξ (S.image (· + v)) := by
  classical
  refine ⟨h.1.image _, Nivat.LatticeConvex.translate h.2.1 v, ?_⟩
  intro a ha hconv
  obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp ha
  have herase : (S.image (· + v)).erase (g + v) = (S.erase g).image (· + v) :=
    (Finset.image_erase (add_left_injective v) S g).symm
  have hconv' : Nivat.LatticeConvex (S.erase g) := by
    rw [herase] at hconv
    have h' := Nivat.LatticeConvex.translate hconv (-v)
    have e : ((S.erase g).image (· + v)).image (· + -v) = S.erase g := by
      ext z
      simp only [Finset.mem_image]
      constructor
      · rintro ⟨y, ⟨w, hw, rfl⟩, rfl⟩
        simpa using hw
      · intro hz
        exact ⟨z + v, ⟨z, hz, rfl⟩, by abel⟩
    rwa [e] at h'
  have hgen := h.2.2 g hg hconv'
  refine ⟨ha, fun x hx y hy hagree => ?_⟩
  have := Nivat.Claim47.generatesAt_translate hgen hx hy v (fun z hz => by
    rw [add_comm v z]
    exact hagree (z + v) (herase ▸ Finset.mem_image_of_mem _ hz))
  rwa [add_comm v g] at this

/-! ## Translation equivariance of `L1Data`, and the one field that was not equivariant

🔴 **Correction (2026-09-19, integrator ruling on `hbase`; kept per `PROTOCOL.md` §14).**
Everything below this paragraph was written against the *strong* conjunct 16
`∃ b ∈ B, ∀ z ∈ S₁, b + z ∈ R`.  That field is now `B.Nonempty ∧ ∃ b, ∀ z ∈ S₁, b + z ∈ R`,
and in the weak form the obstruction analysed below **does not exist**: the witness `b` is no
longer required to lie in `B`, so the displacement `2v` vs `v` is absorbed by re-choosing `b`
(`b + (s + v) − v = b + s`).  `translate` therefore takes **no side condition** any more, and
`S₁ := S` is without loss of generality for all sixteen conjuncts (`exists_window_eq`).  The
analysis is retained because it is the record of *why* the strong form was the one field with
an absolute-position cost — the same cost `RegionClaim411.lean` §"hbase is the one conjunct
with an absolute-position cost" found from leaf C's side.

**Question (integrator, 2026-09-19): can `S₁` simply be `S`?**  `hSgen : IsGeneratingSet ξ S`
is a binder of `exists_L1Data`, so if the producer may always take `S₁ := S`, conjunct 1 costs
nothing and no translate is ever needed.

The honest way to answer is to ask which fields of `L1Data` are *invariant* under moving the
window.  Moving the window by `v` is the same as moving the plane by `v`:

| field | `L` | `L.translate v` |
|---|---|---|
| `S₁`, `Q`, `B` | `S₁`, `Q`, `B` | `S₁ + v`, `Q + v`, `B + v` |
| `e` | `e` | `e − v` (so `T (e − v) ξ z = T e ξ (z − v)`, `T_sub_apply`) |
| `R`, `R'` | `R`, `R'` | `shift v R`, `shift v R'` (`Nivat.LE2.shift`, `LatticeEdges.lean:578`) |
| `u u' c τ pw` | unchanged | unchanged |

Under this dictionary **fourteen of the fifteen proof fields transport verbatim** — the proof of
`translate` below does nothing but rewrite each of them.  The one that did not (strong form) is
conjunct 16:

    hbase : ∃ b ∈ B, ∀ z ∈ S₁, b + z ∈ R          -- retired 2026-09-19

Here `b` and `z` are **both** window coordinates and `b + z` is a plane coordinate.  Moving the
window by `v` moves `b + z` by `2v`, but the plane only by `v`.  So the transported conjunct 16
read `∃ b ∈ B, ∀ z ∈ S₁, b + z + v ∈ R` (the window placed at `b + v`, not at `b`), which was
the hypothesis `hb` that `translate` used to carry.

**Why the translate could not be absorbed into `b` (strong form).**  Conjunct 16 alone would
absorb it: the displaced base `b + v` witnesses the existential.  But `b + v` had to lie in the
transported `B + v`, i.e. `b ∈ B`, while what conjunct 16 supplied after transport was
`b + v ∈ B`, i.e. `b ∈ B − v`.  The two agree only when `B` is `v`-invariant.  And `B` cannot
be replaced by `B ∪ (B − v)` either, because conjunct 8 (`hBQ`) is a **universal** statement
over `B` in window coordinates.  So the obstruction was precisely that the single field `B` was
a window subset in conjunct 8 and a set of plane displacements in conjunct 16.  **In the weak
form `b` is not a member of `B`, and the obstruction is gone.**

**Answer (weak form).**  `S₁ := S` is without loss of generality for all sixteen conjuncts:
`exists_window_eq` below.  ⚠ That some `L1Data` exists at all is **not** established here.
-/

section Translate

variable {ξ : Config ℤ} {S : Finset (ℤ × ℤ)}

/-- `T (e − v) ξ` reads `T e ξ` at the point moved back by `v`. -/
theorem T_sub_apply (e v z : ℤ × ℤ) : T (e - v) ξ z = T e ξ (z - v) := by
  simp only [T_apply]
  congr 1
  abel

/-- `PeriodOn` transports forward along the dictionary. -/
theorem periodOn_shift {e v h : ℤ × ℤ} {R : Set (ℤ × ℤ)}
    (hp : Colle41.PeriodOn (T e ξ) R h) :
    Colle41.PeriodOn (T (e - v) ξ) (Nivat.LE2.shift v R) h := by
  intro z hz hz'
  rw [Nivat.LE2.mem_shift_iff] at hz hz'
  rw [T_sub_apply, T_sub_apply]
  have := hp (z - v) hz (by rwa [show z - v + h = z + h - v by abel])
  rwa [show z - v + h = z + h - v by abel] at this

/-- …and backward. -/
theorem periodOn_of_shift {e v h : ℤ × ℤ} {R : Set (ℤ × ℤ)}
    (hp : Colle41.PeriodOn (T (e - v) ξ) (Nivat.LE2.shift v R) h) :
    Colle41.PeriodOn (T e ξ) R h := by
  intro z hz hz'
  have := hp (z + v) (by rw [Nivat.LE2.mem_shift_iff, add_sub_cancel_right]; exact hz)
    (by rw [Nivat.LE2.mem_shift_iff, show z + v + h - v = z + h by abel]; exact hz')
  rwa [T_sub_apply, T_sub_apply, show z + v + h - v = z + h by abel,
    add_sub_cancel_right] at this

/-- Conjunct 11 transports: lattice convexity by `Nivat.LE2.isLatticeConvexRegion_shift`, the
two rays by re-basing. -/
theorem isRegion_shift {u u' : ℤ × ℤ} {R : Set (ℤ × ℤ)} (v : ℤ × ℤ)
    (h : Colle41.IsRegion R u u') : Colle41.IsRegion (Nivat.LE2.shift v R) u u' := by
  obtain ⟨hconv, ⟨z₀, hray⟩, ⟨z₀', hray'⟩⟩ := h
  refine ⟨Nivat.LE2.isLatticeConvexRegion_shift v hconv, ⟨z₀ + v, fun k => ?_⟩,
    ⟨z₀' + v, fun k => ?_⟩⟩
  · rw [Nivat.LE2.mem_shift_iff, show z₀ + v + (k : ℤ) • u - v = z₀ + (k : ℤ) • u by abel]
    exact hray k
  · rw [Nivat.LE2.mem_shift_iff, show z₀' + v + (k : ℤ) • u' - v = z₀' + (k : ℤ) • u' by abel]
    exact hray' k

/-- Conjunct 12 transports. -/
theorem shift_ssubset {R R' : Set (ℤ × ℤ)} (v : ℤ × ℤ) (h : R ⊂ R') :
    Nivat.LE2.shift v R ⊂ Nivat.LE2.shift v R' := by
  rw [Set.ssubset_def] at h ⊢
  refine ⟨fun z hz => h.1 hz, fun hle => h.2 fun w hw => ?_⟩
  have hw' : w + v ∈ Nivat.LE2.shift v R' := by
    rw [Nivat.LE2.mem_shift_iff, add_sub_cancel_right]; exact hw
  have := hle hw'
  rwa [Nivat.LE2.mem_shift_iff, add_sub_cancel_right] at this

/-- **`L1Data` is translation-equivariant in every field.**

Until 2026-09-19 this carried a side condition `hb` for conjunct 16 (see the section docstring
for what it was and why the strong form needed it).  With the weak `hbase` every field is
transported by rewriting, with no side condition. -/
def translate (L : L1Data ξ S) (v : ℤ × ℤ) : L1Data ξ S where
  e := L.e - v
  u := L.u
  u' := L.u'
  Q := L.Q.image (· + v)
  τ := L.τ
  pw := L.pw
  B := L.B.image (· + v)
  R := Nivat.LE2.shift v L.R
  R' := Nivat.LE2.shift v L.R'
  c := L.c
  S₁ := L.S₁.image (· + v)
  hS₁gen := isGeneratingSet_image L.hS₁gen v
  hQS := Finset.image_subset_image L.hQS
  hQ_edge := by
    obtain ⟨n, cmax, hn0, hnu', hle, hface, hQ⟩ := L.hQ_edge
    refine ⟨n, cmax + inner2 n v, hn0, hnu', ?_, ?_, ?_⟩
    · intro z hz
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hz
      rw [inner2_add]
      linarith [hle s hs]
    · rw [Nivat.L1Complexity.face_image_add, add_sub_cancel_right]
      exact hface.image _
    · rw [Nivat.L1Complexity.filter_lt_image_add, add_sub_cancel_right, hQ]
  hdet := L.hdet
  hu'_prim := L.hu'_prim
  hPQ := by
    rw [Nivat.P_translate, Nivat.P_translate]
    exact L.hPQ
  hBQ := by
    intro g hg i hi
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hg
    rw [add_right_comm]
    exact Finset.mem_image_of_mem _ (L.hBQ b hb i hi)
  hc := L.hc
  hRper := periodOn_shift L.hRper
  hR_region := isRegion_shift v L.hR_region
  hRR' := shift_ssubset v L.hRR'
  hnonper := fun h => L.hnonper (periodOn_of_shift h)
  hline := by
    intro t ht z hz
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨h1, h2⟩ := L.hline t ht q hq
    refine ⟨?_, ?_⟩
    · rw [Nivat.LE2.mem_shift_iff, show t • L.u' + (q + v) - v = t • L.u' + q by abel]
      exact h1
    · rw [Nivat.LE2.mem_shift_iff,
        show t • L.u' + (q + v) + L.c • L.u - v = t • L.u' + q + L.c • L.u by abel]
      exact h2
  hstraddle := by
    intro g hg hgQ t₀ ht₀ hper hray
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hg
    have hsQ : s ∉ L.Q := fun h => hgQ (Finset.mem_image_of_mem _ h)
    have hray' : ∀ t : ℤ, t₀ ≤ t →
        T L.e ξ (t • L.u' + s + L.c • L.u) = T L.e ξ (t • L.u' + s) := by
      intro t ht
      have := hray t ht
      rwa [T_sub_apply, T_sub_apply,
        show t • L.u' + (s + v) + L.c • L.u - v = t • L.u' + s + L.c • L.u by abel,
        show t • L.u' + (s + v) - v = t • L.u' + s by abel] at this
    exact periodOn_shift (L.hstraddle s hs hsQ t₀ ht₀ (periodOn_of_shift hper) hray')
  hbase := by
    obtain ⟨⟨b₀, hb₀⟩, b, h⟩ := L.hbase
    refine ⟨⟨b₀ + v, Finset.mem_image_of_mem _ hb₀⟩, b, fun z hz => ?_⟩
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hz
    rw [Nivat.LE2.mem_shift_iff, show b + (s + v) - v = b + s by abel]
    exact h s hs

/-- **`S₁ := S` is free.**  From an `L1Data` whose window is `S + v`, one whose window is
literally `S` — with `e` moved by `v` and `R` moved back.  Before the 2026-09-19 weakening of
conjunct 16 this cost the displaced-base form `∃ b ∈ B, ∀ z ∈ S₁, b + z − v ∈ R`
(then named `exists_window_eq_of_displaced_base`); it now costs nothing. -/
theorem exists_window_eq (L : L1Data ξ S) (v : ℤ × ℤ)
    (hS₁ : L.S₁ = S.image (· + v)) :
    ∃ L' : L1Data ξ S, L'.S₁ = S ∧ L'.e = L.e + v ∧ L'.R = Nivat.LE2.shift (-v) L.R := by
  refine ⟨L.translate (-v), ?_, ?_, rfl⟩
  · show L.S₁.image (· + -v) = S
    rw [hS₁, Finset.image_image]
    ext z
    simp
  · show L.e - -v = L.e + v
    rw [sub_neg_eq_add]

end Translate

/-! ## The cut derived from `u'`: five of the fourteen were data, not debt

Conjunct 4 asks for a normal `n ≠ 0` with `inner2 n u' = 0`, a level `cmax` bounding `S₁`, and
a non-empty face at that level; `ofPieces` also asks for a non-empty bottom face.  None of that
is a proof obligation: the normal is `±perp u'` (`Claim47Core.lean:45`), and the two levels
are the max and min of `inner2 n` over `S₁`, which exist because `S₁` is non-empty (conjunct
1).  So `n0`, `nu'`, `le`, `face`, `minne` are *derivable from the data*, and counting them as
residual overstates the gap by five.

`ofDerived` below fixes the cut to `cutNormal ε u'` with the side `ε` explicit, derives both
levels, and asks for what is left: `DerivedResidual`, **eight** fields.  Of these, `det'`,
`prim`, `c0` are constraints on the choice of data; `lt` is non-degeneracy (`S₁` is not a
single `u'`-line, equivalently `Q ≠ ∅`); `card` is the geometric content of conjunct 8; and
`line0`, `base0`, `straddle` are the real content.

⚠ Fixing `n := cutNormal ε u'` loses nothing: every admissible `n` is a non-zero real multiple
of `perp u'` (`Nivat.KM.exists_smul_perpOf`, `KariMoutot.lean:220`), and the face and the
filter depend only on the sign of that multiple, which is `ε`.  This is a reading; the kernel
fact is only that `ofDerived` builds an `L1Data`.
-/

section DerivedCut

variable {ξ : Config ℤ} {S : Finset (ℤ × ℤ)}

/-! `cutNormal`, `levelMax`, `levelMin`, `derivedQ`, `topFace`, `bottomFace` and their lemmas
moved verbatim to `L1Cut.lean` (2026-09-19) so that `L1Data.lean` can name them in the field
`hBmax`.  Same namespace; nothing below changed. -/

/-- **Everything `ofDerived` still asks for.**  Eight fields.  Read the count off
`#check @DerivedResidual.mk`.

Compared with `Residual`: `gen` is gone (conjunct 1 comes from the leaf's `hSgen` through
`isGeneratingSet_image`), and `n0`, `nu'`, `le`, `face`, `minne` are gone (derived from `u'`
and `S₁.Nonempty`).  Nothing was added. -/
structure DerivedResidual {ξ : Config ℤ} (ε : Bool) (u u' : ℤ × ℤ) (c τ : ℤ)
    (S₁ : Finset (ℤ × ℤ)) {e : ℤ × ℤ}
    (F : Nivat.L1Region.RegionFamily (T e ξ) u u' c) : Prop where
  /-- Non-degeneracy: `S₁` is not contained in one `u'`-line, i.e. `Q ≠ ∅`. -/
  lt : levelMin S₁ (cutNormal ε u') < levelMax S₁ (cutNormal ε u')
  /-- Conjunct 8: the bottom face carries the run the top face demands. -/
  card : (topFace ε u' S₁).card - 1 ≤ (bottomFace ε u' S₁).card
  /-- Conjunct 5. -/
  det' : det u u' ≠ 0
  /-- Conjunct 6. -/
  prim : Primitive u'
  /-- Conjunct 9. -/
  c0 : c ≠ 0
  /-- Conjunct 14 at level `0`. -/
  line0 : ∀ t : ℤ, τ ≤ t → ∀ z ∈ derivedQ ε u' S₁,
    t • u' + z ∈ F.R 0 ∧ t • u' + z + c • u ∈ F.R 0
  /-- Conjunct 16 at level `0`, over the whole bottom face. -/
  base0 : ∀ b ∈ bottomFace ε u' S₁, ∀ z ∈ S₁, b + z ∈ F.R 0
  /-- Conjunct 15, at the maximal indices only. -/
  straddle : ∀ N : ℕ, Colle41.PeriodOn (T e ξ) (F.R N) (c • u) →
    ¬ Colle41.PeriodOn (T e ξ) (F.R (N + 1)) (c • u) →
    Nivat.L1Region.Straddle (T e ξ) (F.R N) (F.R (N + 1)) S₁ (derivedQ ε u' S₁) u u' c τ

/-- **The assembly with the cut derived and conjunct 1 taken from the leaf.**

Inputs: data (`e u u' v c τ ε S₁ F`), the two leaf binders `hdef` and `hSgen` in exactly the
form `exists_L1Data` (`RegionSteps.lean:877-893`) has them, the defining equation `hS₁`, and
`DerivedResidual`.  Nothing else. -/
noncomputable def ofDerived (e u u' v : ℤ × ℤ) (c τ : ℤ) (ε : Bool) (S₁ : Finset (ℤ × ℤ))
    (F : Nivat.L1Region.RegionFamily (T e ξ) u u' c)
    (hS₁ : S₁ = S.image (· + v))
    (hdef : ∀ (m : ℝ × ℝ) (a b : ℝ),
      (∀ z ∈ S, inner2 m z ≤ a) → (Nivat.R2.face S m a).Nonempty →
      (∀ z ∈ S, b ≤ inner2 m z) → (Nivat.R2.face S m b).Nonempty →
        P ξ S - P ξ (S.filter fun z => inner2 m z < a) ≤ (Nivat.R2.face S m a).card - 1 ∧
        P ξ S - P ξ (S.filter fun z => b < inner2 m z) ≤ (Nivat.R2.face S m b).card - 1)
    (hSgen : Nivat.Colle.IsGeneratingSet ξ S)
    (H : DerivedResidual ε u u' c τ S₁ F) : L1Data ξ S :=
  have hgen : Nivat.Colle.IsGeneratingSet ξ S₁ := by
    rw [hS₁]
    exact isGeneratingSet_image hSgen v
  ofPieces e u u' v c τ (cutNormal ε u') (levelMax S₁ (cutNormal ε u'))
    (levelMin S₁ (cutNormal ε u')) S₁ (derivedQ ε u' S₁) F hS₁ rfl hdef hgen
    (cutNormal_ne_zero ε H.prim.ne_zero) (inner2_cutNormal ε u')
    (le_levelMax hgen.1) (face_levelMax_nonempty hgen.1) (face_levelMin_nonempty hgen.1)
    H.lt H.card H.det' H.prim H.c0 H.line0 H.base0 H.straddle

/-- `ofDerived` in the exact shape of `exists_L1Data`'s conclusion. -/
theorem nonempty_of_derived (e u u' v : ℤ × ℤ) (c τ : ℤ) (ε : Bool) (S₁ : Finset (ℤ × ℤ))
    (F : Nivat.L1Region.RegionFamily (T e ξ) u u' c)
    (hS₁ : S₁ = S.image (· + v))
    (hdef : ∀ (m : ℝ × ℝ) (a b : ℝ),
      (∀ z ∈ S, inner2 m z ≤ a) → (Nivat.R2.face S m a).Nonempty →
      (∀ z ∈ S, b ≤ inner2 m z) → (Nivat.R2.face S m b).Nonempty →
        P ξ S - P ξ (S.filter fun z => inner2 m z < a) ≤ (Nivat.R2.face S m a).card - 1 ∧
        P ξ S - P ξ (S.filter fun z => b < inner2 m z) ≤ (Nivat.R2.face S m b).card - 1)
    (hSgen : Nivat.Colle.IsGeneratingSet ξ S)
    (H : DerivedResidual ε u u' c τ S₁ F) : Nonempty (L1Data ξ S) :=
  ⟨ofDerived e u u' v c τ ε S₁ F hS₁ hdef hSgen H⟩

end DerivedCut

/-! ## `card` is free if the side is free — so it is coupled, not independent

Flipping `ε` negates the normal, which swaps the two faces (`R2.face_neg_level`).  So
`card ε ∨ card (!ε)` holds with no hypotheses at all (`L1Data.card_pigeonhole`), and `lt` is
symmetric.  A producer who may choose the side pays nothing for `card`.  But `ε` also
appears in `line0`, `base0` and `straddle` through `derivedQ`, and `L1Straddle.lean` §4–§5
compiled that conjuncts 14 and 15 are **not** stable under `ε ↦ !ε`
(`conj14_not_stable_under_neg`, `conj15_not_stable_under_neg`).  So `card` is not removed
from `DerivedResidual`: removing it would let the side float, which is the shared-field leak
of `exists_pw_trivial` in another guise.  What the kernel certifies is that the eight are
really **seven plus a side choice**.
-/

section SideFlip

variable {S₁ : Finset (ℤ × ℤ)} {n : ℝ × ℝ}

theorem cutNormal_not (ε : Bool) (u' : ℤ × ℤ) : cutNormal (!ε) u' = -cutNormal ε u' := by
  cases ε <;> simp [cutNormal, Nivat.KM.toReal_neg]

theorem levelMin_le (hne : S₁.Nonempty) : ∀ z ∈ S₁, levelMin S₁ n ≤ inner2 n z := by
  intro z hz
  unfold levelMin
  rw [dif_pos hne]
  exact Finset.inf'_le (fun z => inner2 n z) hz

theorem levelMax_neg (hne : S₁.Nonempty) : levelMax S₁ (-n) = -levelMin S₁ n := by
  apply le_antisymm
  · obtain ⟨z, hz⟩ := face_levelMax_nonempty (n := -n) hne
    rw [Nivat.R2.mem_face] at hz
    rw [← hz.2, Nivat.R2.inner2_neg_left]
    linarith [levelMin_le (n := n) hne z hz.1]
  · obtain ⟨z, hz⟩ := face_levelMin_nonempty (n := n) hne
    rw [Nivat.R2.mem_face] at hz
    rw [← hz.2]
    have := le_levelMax (n := -n) hne z hz.1
    rw [Nivat.R2.inner2_neg_left] at this
    linarith

theorem levelMin_neg (hne : S₁.Nonempty) : levelMin S₁ (-n) = -levelMax S₁ n := by
  have := levelMax_neg (S₁ := S₁) (n := -n) hne
  rw [neg_neg] at this
  linarith

theorem topFace_not (ε : Bool) (u' : ℤ × ℤ) (hne : S₁.Nonempty) :
    topFace (!ε) u' S₁ = bottomFace ε u' S₁ := by
  unfold topFace bottomFace
  rw [cutNormal_not, levelMax_neg hne, Nivat.R2.face_neg_level]

theorem bottomFace_not (ε : Bool) (u' : ℤ × ℤ) (hne : S₁.Nonempty) :
    bottomFace (!ε) u' S₁ = topFace ε u' S₁ := by
  unfold topFace bottomFace
  rw [cutNormal_not, levelMin_neg hne, Nivat.R2.face_neg_level]

/-- **`card` holds on at least one side, unconditionally.** -/
theorem card_side (ε : Bool) (u' : ℤ × ℤ) (hne : S₁.Nonempty) :
    (topFace ε u' S₁).card - 1 ≤ (bottomFace ε u' S₁).card ∨
      (topFace (!ε) u' S₁).card - 1 ≤ (bottomFace (!ε) u' S₁).card := by
  rw [topFace_not ε u' hne, bottomFace_not ε u' hne]
  exact card_pigeonhole _ _

/-- `lt` is the same statement on both sides. -/
theorem lt_not_iff (ε : Bool) (u' : ℤ × ℤ) (hne : S₁.Nonempty) :
    levelMin S₁ (cutNormal (!ε) u') < levelMax S₁ (cutNormal (!ε) u') ↔
      levelMin S₁ (cutNormal ε u') < levelMax S₁ (cutNormal ε u') := by
  rw [cutNormal_not, levelMin_neg hne, levelMax_neg hne]
  constructor <;> intro h <;> linarith

end SideFlip

/-! ## The maximal baseline: conjunct 8 holds by definition, and `B` is as wide as `S₁` allows

`B` is existentially quantified in leaf L1's conclusion, so the producer chooses it.  Conjunct 8
(`hBQ`) is the only *universal* constraint on `B`, and conjunct 16 (`hbase`) is existential —
so the canonical choice is the **largest** `B` conjunct 8 allows:

  `maxB Q u' pw := {g ∈ Q | ∀ i < pw, g + i • u' ∈ Q}`.

With this choice conjunct 8 is `Finset.mem_filter`, and conjunct 16 is as weak as it can be.
`ofMaxB` builds an `L1Data` on it; `MaxBResidual` (six fields) is what is left.  Compared with
`DerivedResidual`: `lt` and `card` are gone (they existed only to put the bottom-face anchor
into a singleton `B`), and `base0` is now *literally* conjunct 16 at level `0` — an existential
over `maxB` — rather than the universal-over-the-bottom-face strengthening `ofPieces` charged.

`maxB` **is** the wide baseline L3 asks for.  `maxB_wide` below proves that it contains
`min |top u-face| |bottom u-face| − 1` consecutive `u`-translates (Collé's `|𝒮 ∩ ℓ_𝒮| − 1`,
`b3_colle2.txt:694`), for every lattice-convex `S₁`, given `Primitive u`, `Primitive u'` and
`det u u' ≠ 0`.  The geometric content is the concavity of chord length (`Nivat.Chord`'s
`exists_chord_of_convex`, already in the import closure): the `u'`-edge is the right end of
every `u`-chord it meets, and each such chord is at least as long as the shorter `u`-edge.
-/

section MaxB

variable {ξ : Config ℤ} {S : Finset (ℤ × ℤ)}

/-! `maxB`, `mem_maxB`, `maxB_hBQ` moved verbatim to `L1Cut.lean` (2026-09-19); same
namespace. -/

/-- **Everything `ofMaxB` still asks for.**  Six fields; read the count off
`#check @MaxBResidual.mk`. -/
structure MaxBResidual {ξ : Config ℤ} (ε : Bool) (u u' : ℤ × ℤ) (c τ : ℤ)
    (S₁ : Finset (ℤ × ℤ)) {e : ℤ × ℤ}
    (F : Nivat.L1Region.RegionFamily (T e ξ) u u' c) : Prop where
  /-- Conjunct 5. -/
  det' : det u u' ≠ 0
  /-- Conjunct 6. -/
  prim : Primitive u'
  /-- Conjunct 9. -/
  c0 : c ≠ 0
  /-- Conjunct 14 at level `0`. -/
  line0 : ∀ t : ℤ, τ ≤ t → ∀ z ∈ derivedQ ε u' S₁,
    t • u' + z ∈ F.R 0 ∧ t • u' + z + c • u ∈ F.R 0
  /-- Conjunct 16 at level `0`, verbatim, with `B := maxB`.  **Weak form (2026-09-19 ruling)**:
  `maxB` is non-empty, and *some* `b` carries `S₁` into `F.R 0`.  The strong form
  `∃ b ∈ maxB …, ∀ z ∈ S₁, b + z ∈ F.R 0` was retired together with `L1Data.hbase`; the two
  halves are `maxB_nonempty_of_two_le_faces` (Lemma 2.3) and
  `exists_translate_subset_of_isRegion` (recession cone), see `MaxBResidual.base0_of_faces`. -/
  base0 : (maxB (derivedQ ε u' S₁) u' ((topFace ε u' S₁).card - 1)).Nonempty ∧
    ∃ b, ∀ z ∈ S₁, b + z ∈ F.R 0
  /-- Conjunct 15, at the maximal indices only. -/
  straddle : ∀ N : ℕ, Colle41.PeriodOn (T e ξ) (F.R N) (c • u) →
    ¬ Colle41.PeriodOn (T e ξ) (F.R (N + 1)) (c • u) →
    Nivat.L1Region.Straddle (T e ξ) (F.R N) (F.R (N + 1)) S₁ (derivedQ ε u' S₁) u u' c τ

/-- **The assembly on the maximal baseline.** -/
noncomputable def ofMaxB (e u u' v : ℤ × ℤ) (c τ : ℤ) (ε : Bool) (S₁ : Finset (ℤ × ℤ))
    (F : Nivat.L1Region.RegionFamily (T e ξ) u u' c)
    (hS₁ : S₁ = S.image (· + v))
    (hdef : ∀ (m : ℝ × ℝ) (a b : ℝ),
      (∀ z ∈ S, inner2 m z ≤ a) → (Nivat.R2.face S m a).Nonempty →
      (∀ z ∈ S, b ≤ inner2 m z) → (Nivat.R2.face S m b).Nonempty →
        P ξ S - P ξ (S.filter fun z => inner2 m z < a) ≤ (Nivat.R2.face S m a).card - 1 ∧
        P ξ S - P ξ (S.filter fun z => b < inner2 m z) ≤ (Nivat.R2.face S m b).card - 1)
    (hSgen : Nivat.Colle.IsGeneratingSet ξ S)
    (H : MaxBResidual ε u u' c τ S₁ F) : L1Data ξ S := by
  classical
  have hgen : Nivat.Colle.IsGeneratingSet ξ S₁ := by
    rw [hS₁]
    exact isGeneratingSet_image hSgen v
  have hgp : ∃ N : ℕ, Colle41.PeriodOn (T e ξ) (F.R N) (c • u) ∧
      ¬ Colle41.PeriodOn (T e ξ) (F.R (N + 1)) (c • u) :=
    Nivat.L1Region.exists_greatest_periodOn F.monotone F.base F.union_not
  exact
    { e := e, u := u, u' := u', Q := derivedQ ε u' S₁, τ := τ
      pw := (topFace ε u' S₁).card - 1
      B := maxB (derivedQ ε u' S₁) u' ((topFace ε u' S₁).card - 1)
      R := F.R hgp.choose
      R' := F.R (hgp.choose + 1)
      c := c, S₁ := S₁
      hS₁gen := hgen
      hQS := Finset.filter_subset _ _
      hQ_edge := ⟨cutNormal ε u', levelMax S₁ (cutNormal ε u'),
        cutNormal_ne_zero ε H.prim.ne_zero, inner2_cutNormal ε u', le_levelMax hgen.1,
        face_levelMax_nonempty hgen.1, rfl⟩
      hdet := H.det'
      hu'_prim := H.prim
      hPQ := Nivat.L1Complexity.hPQ_of_hQ_edge hS₁ hdef (le_levelMax hgen.1)
        (face_levelMax_nonempty hgen.1) rfl
      hBQ := maxB_hBQ _ _ _
      hc := H.c0
      hRper := hgp.choose_spec.1
      hR_region := F.isRegion hgp.choose
      hRR' := F.grow hgp.choose
      hnonper := hgp.choose_spec.2
      hline := F.line_of_line_zero H.line0 hgp.choose
      hstraddle := H.straddle hgp.choose hgp.choose_spec.1 hgp.choose_spec.2
      hbase := weakBase_of_weakBase_zero F H.base0 hgp.choose }

/-- `ofMaxB` in the exact shape of `exists_L1Data`'s conclusion. -/
theorem nonempty_of_maxB (e u u' v : ℤ × ℤ) (c τ : ℤ) (ε : Bool) (S₁ : Finset (ℤ × ℤ))
    (F : Nivat.L1Region.RegionFamily (T e ξ) u u' c)
    (hS₁ : S₁ = S.image (· + v))
    (hdef : ∀ (m : ℝ × ℝ) (a b : ℝ),
      (∀ z ∈ S, inner2 m z ≤ a) → (Nivat.R2.face S m a).Nonempty →
      (∀ z ∈ S, b ≤ inner2 m z) → (Nivat.R2.face S m b).Nonempty →
        P ξ S - P ξ (S.filter fun z => inner2 m z < a) ≤ (Nivat.R2.face S m a).card - 1 ∧
        P ξ S - P ξ (S.filter fun z => b < inner2 m z) ≤ (Nivat.R2.face S m b).card - 1)
    (hSgen : Nivat.Colle.IsGeneratingSet ξ S)
    (H : MaxBResidual ε u u' c τ S₁ F) : Nonempty (L1Data ξ S) :=
  ⟨ofMaxB e u u' v c τ ε S₁ F hS₁ hdef hSgen H⟩


/-- **`MaxBResidual` is implied by `DerivedResidual`** — the six are not a re-encoding of the
eight, they are weaker: the bottom-face anchor that `ofPieces` put into a singleton `B` lies
in `maxB`, so `DerivedResidual.base0` (universal over the bottom face) gives
`MaxBResidual.base0` (existential over `maxB`), and `lt`/`card` are consumed in doing so. -/
theorem maxBResidual_of_derived {ε : Bool} {u u' : ℤ × ℤ} {c τ : ℤ} {S₁ : Finset (ℤ × ℤ)}
    {e : ℤ × ℤ} {F : Nivat.L1Region.RegionFamily (T e ξ) u u' c}
    (hne : S₁.Nonempty) (hconv : Nivat.LatticeConvex S₁)
    (H : DerivedResidual ε u u' c τ S₁ F) : MaxBResidual ε u u' c τ S₁ F := by
  refine ⟨H.det', H.prim, H.c0, H.line0, ?_, H.straddle⟩
  have hrun : ∃ z₀, z₀ ∈ bottomFace ε u' S₁ ∧
      ∀ i : ℕ, i < (bottomFace ε u' S₁).card → z₀ + (i : ℤ) • u' ∈ bottomFace ε u' S₁ :=
    faceIsRun (cmax := levelMin S₁ (cutNormal ε u')) hconv H.prim
      (cutNormal_ne_zero ε H.prim.ne_zero) (inner2_cutNormal ε u') (face_levelMin_nonempty hne)
  obtain ⟨z₀, hz₀, hz₀run⟩ := hrun
  refine ⟨⟨z₀, mem_maxB.mpr ⟨?_, ?_⟩⟩, z₀, H.base0 z₀ hz₀⟩
  · have hmem := hz₀run 0 (Finset.card_pos.mpr ⟨z₀, hz₀⟩)
    simp only [Nat.cast_zero, zero_smul, add_zero] at hmem
    rw [bottomFace, Nivat.R2.mem_face] at hmem
    exact Finset.mem_filter.mpr ⟨hmem.1, by rw [hmem.2]; exact H.lt⟩
  · intro i hi
    have hmem := hz₀run i (lt_of_lt_of_le hi H.card)
    rw [bottomFace, Nivat.R2.mem_face] at hmem
    exact Finset.mem_filter.mpr ⟨hmem.1, by rw [hmem.2]; exact H.lt⟩

end MaxB

end L1Data

/-! ### Conjunct 17: the baseline is `maxB`

`exists_L1Data` (`RegionSteps.lean:956`) hands back `Nonempty (L1Data ξ S)`, and `.some` erases
everything that is not a field — so nothing proved about `maxB` reaches `case1_seed` unless
it is a field.  `L1DataMax` below is `L1Data` plus the one fact `ofMaxB` has by definition:
`pw` is Collé's width `|𝒮 ∩ ℓ'_𝒮| − 1` (`b3_colle2.txt:645`) and `B` is `maxB` at it, for some
side `ε` of the cut.

Why *this* field and not a block statement: it does not mention `u`, so it survives
`case1_sweep`'s WLOG rescaling `u ↦ u₀` (`L3Band.case1_sweep_conclusion_wlog_primitive`),
and the consumer applies `L3Band.hasBlock_maxB` at whatever primitive `u` it has, with
`Primitive u` and `0 < pw` discharged where they are actually available at `case1_seed`
(`hu_prim`, `pos_pw_of_case1_hyps`).  `MaxBResidual` is **not** strengthened — the field is
two `rfl`s — so the open leaf `exists_L1MaxBResidual` is unchanged.

Why an extension and not a field of `L1Data`: the other four constructors (`ofPieces`,
`ofEdgeRun`, `translate`, `withPosPw`) and the `L1Straddle.lean` witness build `L1Data` with a
singleton or translated `B` that is *not* `maxB`; a field on `L1Data` would break every one
of them for no gain, since only `ofMaxB` is on the chain.  `L1Data.lean` is untouched. -/

/-- `L1Data` together with conjunct 17. -/
structure L1DataMax (ξ : Config ℤ) (S : Finset (ℤ × ℤ)) extends L1Data ξ S where
  /-- Conjunct 17: `pw` is the top-face width and `B` is the maximal baseline at it. -/
  hBmax : ∃ ε : Bool, pw = (L1Data.topFace ε u' S₁).card - 1 ∧
    B = L1Data.maxB (L1Data.derivedQ ε u' S₁) u' pw

namespace L1DataMax

/-- `ofMaxB` carries conjunct 17 by definition. -/
noncomputable def ofMaxB {ξ : Config ℤ} {S : Finset (ℤ × ℤ)}
    (e u u' v : ℤ × ℤ) (c τ : ℤ) (ε : Bool) (S₁ : Finset (ℤ × ℤ))
    (F : Nivat.L1Region.RegionFamily (T e ξ) u u' c)
    (hS₁ : S₁ = S.image (· + v))
    (hdef : ∀ (m : ℝ × ℝ) (a b : ℝ),
      (∀ z ∈ S, inner2 m z ≤ a) → (Nivat.R2.face S m a).Nonempty →
      (∀ z ∈ S, b ≤ inner2 m z) → (Nivat.R2.face S m b).Nonempty →
        P ξ S - P ξ (S.filter fun z => inner2 m z < a) ≤ (Nivat.R2.face S m a).card - 1 ∧
        P ξ S - P ξ (S.filter fun z => b < inner2 m z) ≤ (Nivat.R2.face S m b).card - 1)
    (hSgen : Nivat.Colle.IsGeneratingSet ξ S)
    (H : L1Data.MaxBResidual ε u u' c τ S₁ F) : L1DataMax ξ S where
  toL1Data := L1Data.ofMaxB e u u' v c τ ε S₁ F hS₁ hdef hSgen H
  hBmax := ⟨ε, rfl, rfl⟩

/-- **The replacement for `nonempty_of_maxB` at the leaf**: same binders, conclusion
`Nonempty (L1DataMax ξ S)`.  `exists_L1Data` (`RegionSteps.lean:956`) can switch to this with
no other change. -/
theorem nonempty_of_maxB {ξ : Config ℤ} {S : Finset (ℤ × ℤ)}
    (e u u' v : ℤ × ℤ) (c τ : ℤ) (ε : Bool) (S₁ : Finset (ℤ × ℤ))
    (F : Nivat.L1Region.RegionFamily (T e ξ) u u' c)
    (hS₁ : S₁ = S.image (· + v))
    (hdef : ∀ (m : ℝ × ℝ) (a b : ℝ),
      (∀ z ∈ S, inner2 m z ≤ a) → (Nivat.R2.face S m a).Nonempty →
      (∀ z ∈ S, b ≤ inner2 m z) → (Nivat.R2.face S m b).Nonempty →
        P ξ S - P ξ (S.filter fun z => inner2 m z < a) ≤ (Nivat.R2.face S m a).card - 1 ∧
        P ξ S - P ξ (S.filter fun z => b < inner2 m z) ≤ (Nivat.R2.face S m b).card - 1)
    (hSgen : Nivat.Colle.IsGeneratingSet ξ S)
    (H : L1Data.MaxBResidual ε u u' c τ S₁ F) : Nonempty (L1DataMax ξ S) :=
  ⟨ofMaxB e u u' v c τ ε S₁ F hS₁ hdef hSgen H⟩

/-- **`L1Data.toConclusion` with conjunct 17 appended.**  The first sixteen conjuncts are a
verbatim copy of `L1Data.toConclusion` (`L1Data.lean:149`); the seventeenth is `hBmax`.  This
is the statement `case1_claim46_and_selection` (`RegionSteps.lean:988`) should grow by, so the
destructuring at `:1471` gains exactly one component. -/
theorem toConclusion {ξ : Config ℤ} {S : Finset (ℤ × ℤ)} (L : L1DataMax ξ S) :
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
      (B.Nonempty ∧ ∃ b, ∀ z ∈ S₁, b + z ∈ R) ∧
      (∃ ε : Bool, pw = (L1Data.topFace ε u' S₁).card - 1 ∧
        B = L1Data.maxB (L1Data.derivedQ ε u' S₁) u' pw) :=
  ⟨T L.e ξ, T_mem_orbitClosure ξ L.e, L.u, L.u', L.Q, L.τ, L.pw, L.B, L.R, L.R', L.c, L.S₁,
    L.hS₁gen, ⟨L.e, rfl⟩, L.hQS, L.hQ_edge, L.hdet, L.hu'_prim, L.hPQ, L.hBQ, L.hc,
    L.hRper, L.hR_region, L.hRR', L.hnonper, L.hline, L.hstraddle, L.hbase, L.hBmax⟩

end L1DataMax

namespace L1Data

/-! ## `maxB` is wide along `u`: Collé's parallelogram (`b3_colle2.txt:627-631`)

Collé: *"Since `𝒮` is convex and `|𝒮 ∩ ℓ_𝒮| ≤ |𝒮 ∩ −ℓ_𝒮|`, the convex set `Q` whose vertices
are `g'_0, g'_0 − (|𝒮 ∩ ℓ_𝒮| − 1) v_ℓ, g'_1, g'_1 − (|𝒮 ∩ ℓ_𝒮| − 1) v_ℓ` is contained in `𝒮`."*
That is the `u'`-edge of the window, swept `|u-edge| − 1` steps into the window along `u`.
Every column of the sweep is a `u'`-run of the edge's full length, hence a point of `maxB`;
so `maxB` contains `|u-edge| − 1` consecutive `u`-points.  The proof is chord-length concavity
(`Nivat.exists_chord_of_convex`): each `u`-chord through the `u'`-edge has that edge as its
`n`-maximal end and is at least as long as the shorter of the two `u`-edges.
-/

section Width

/-- Two real linear forms with non-zero "determinant" separate points. -/
theorem eq_of_two_forms {m n : ℝ × ℝ} (h : m.1 * n.2 - m.2 * n.1 ≠ 0) {x y : ℝ × ℝ}
    (h1 : x.1 * m.1 + x.2 * m.2 = y.1 * m.1 + y.2 * m.2)
    (h2 : x.1 * n.1 + x.2 * n.2 = y.1 * n.1 + y.2 * n.2) : x = y := by
  have e1 : (x.1 - y.1) * (m.1 * n.2 - m.2 * n.1) = 0 := by linear_combination n.2 * h1 - m.2 * h2
  have e2 : (x.2 - y.2) * (m.1 * n.2 - m.2 * n.1) = 0 := by linear_combination m.1 * h2 - n.1 * h1
  rcases mul_eq_zero.mp e1 with e1 | e1
  · rcases mul_eq_zero.mp e2 with e2 | e2
    · exact Prod.ext (by linarith) (by linarith)
    · exact absurd e2 h
  · exact absurd e1 h

theorem toReal_sub_zsmul (p w : ℤ × ℤ) (j : ℤ) :
    toReal (p - j • w) = toReal p - (j : ℝ) • toReal w := by
  apply Prod.ext <;>
    simp only [toReal, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
      Int.cast_sub, Int.cast_mul]

/-- **The chord argument.**  `S₁` lattice-convex; `m ⊥ w`, `n` with `⟨n, w⟩ > 0`, the two forms
independent; `S₁` has a `w`-run of `k₀` points at the bottom `m`-level and one of `k₁` points at
the top `m`-level.  Then from any point `p` of `S₁` at the maximal `n`-level, the `j` steps back
along `w` stay in `S₁` for every `j + 1 ≤ min k₀ k₁`. -/
theorem sub_zsmul_mem_of_runs {S₁ : Finset (ℤ × ℤ)} (hS : Nivat.LatticeConvex S₁)
    {m n : ℝ × ℝ} (hmn : m.1 * n.2 - m.2 * n.1 ≠ 0)
    {w : ℤ × ℤ} (hmw : inner2 m w = 0) (hnw : 0 < inner2 n w)
    {cmax lo hi : ℝ} (hle : ∀ z ∈ S₁, inner2 n z ≤ cmax)
    (hlo : ∀ z ∈ S₁, lo ≤ inner2 m z) (hhi : ∀ z ∈ S₁, inner2 m z ≤ hi)
    {c₀ c₁ : ℤ × ℤ} {k₀ k₁ : ℕ} (hc₀ : inner2 m c₀ = lo) (hc₁ : inner2 m c₁ = hi)
    (hrun₀ : ∀ i : ℕ, i ≤ k₀ → c₀ + (i : ℤ) • w ∈ S₁)
    (hrun₁ : ∀ i : ℕ, i ≤ k₁ → c₁ + (i : ℤ) • w ∈ S₁)
    {p : ℤ × ℤ} (hp : p ∈ S₁) (hpc : inner2 n p = cmax) {j : ℕ} (hj₀ : j ≤ k₀) (hj₁ : j ≤ k₁) :
    p - (j : ℤ) • w ∈ S₁ := by
  classical
  set φ : ℝ × ℝ → ℝ := fun x => x.1 * m.1 + x.2 * m.2 with hφ
  set ψ : ℝ × ℝ → ℝ := fun x => x.1 * n.1 + x.2 * n.2 with hψ
  have hφlin : IsLinearMap ℝ φ :=
    ⟨fun x y => by simp only [hφ, Prod.fst_add, Prod.snd_add]; ring,
     fun a x => by simp only [hφ, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring⟩
  have hψlin : IsLinearMap ℝ ψ :=
    ⟨fun x y => by simp only [hψ, Prod.fst_add, Prod.snd_add]; ring,
     fun a x => by simp only [hψ, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring⟩
  have hφR : ∀ z : ℤ × ℤ, φ (toReal z) = inner2 m z := fun z => rfl
  have hψR : ∀ z : ℤ × ℤ, ψ (toReal z) = inner2 n z := fun z => rfl
  have hC : Convex ℝ (Conv S₁) := convex_convexHull ℝ _
  -- the four chord endpoints
  have hc₀S : c₀ ∈ S₁ := by simpa using hrun₀ 0 (Nat.zero_le _)
  have hc₁S : c₁ ∈ S₁ := by simpa using hrun₁ 0 (Nat.zero_le _)
  have hq₀S : c₀ + (k₀ : ℤ) • w ∈ S₁ := hrun₀ k₀ le_rfl
  have hq₁S : c₁ + (k₁ : ℤ) • w ∈ S₁ := hrun₁ k₁ le_rfl
  have hφ₀ : φ (toReal c₀) = φ (toReal (c₀ + (k₀ : ℤ) • w)) := by
    rw [hφR, hφR, inner2_add, inner2_zsmul, hmw, mul_zero, add_zero]
  have hφ₁ : φ (toReal c₁) = φ (toReal (c₁ + (k₁ : ℤ) • w)) := by
    rw [hφR, hφR, inner2_add, inner2_zsmul, hmw, mul_zero, add_zero]
  have hψ₀ : ψ (toReal (c₀ + (k₀ : ℤ) • w)) - ψ (toReal c₀) = (k₀ : ℝ) * inner2 n w := by
    rw [hψR, hψR, inner2_add, inner2_zsmul]; push_cast; ring
  have hψ₁ : ψ (toReal (c₁ + (k₁ : ℤ) • w)) - ψ (toReal c₁) = (k₁ : ℝ) * inner2 n w := by
    rw [hψR, hψR, inner2_add, inner2_zsmul]; push_cast; ring
  -- the level of `p`, and the convex coefficients realising it between `lo` and `hi`
  set t : ℝ := inner2 m p with ht
  have hlot : lo ≤ t := hlo p hp
  have hthi : t ≤ hi := hhi p hp
  obtain ⟨α, β, hα, hβ, hαβ, hαt⟩ :
      ∃ α β : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ α + β = 1 ∧ α * lo + β * hi = t := by
    rcases eq_or_lt_of_le hlot with heq | hlt
    · exact ⟨1, 0, zero_le_one, le_refl 0, by ring, by rw [heq]; ring⟩
    · rcases eq_or_lt_of_le hthi with heq2 | hlt2
      · exact ⟨0, 1, le_refl 0, zero_le_one, by ring, by rw [heq2]; ring⟩
      · have hpos : (0 : ℝ) < hi - lo := by linarith
        refine ⟨(hi - t) / (hi - lo), (t - lo) / (hi - lo), ?_, ?_, ?_, ?_⟩
        · exact div_nonneg (by linarith) hpos.le
        · exact div_nonneg (by linarith) hpos.le
        · field_simp; ring
        · field_simp; ring
  obtain ⟨p', q', hp'C, hq'C, hpq', hpval, hspan⟩ :=
    Nivat.exists_chord_of_convex hC hφlin hψlin (subset_Conv hc₀S) (subset_Conv hq₀S)
      (subset_Conv hc₁S) (subset_Conv hq₁S) hφ₀ hφ₁ hα hβ hαβ
  rw [hφR, hφR, hc₀, hc₁, hαt] at hpval
  -- the chord through `p` has `ψ`-length at least `j * ⟨n, w⟩`
  have hspan' : (j : ℝ) * inner2 n w ≤ ψ q' - ψ p' := by
    rw [hspan, hψ₀, hψ₁]
    have hj₀' : (j : ℝ) ≤ (k₀ : ℝ) := by exact_mod_cast hj₀
    have hj₁' : (j : ℝ) ≤ (k₁ : ℝ) := by exact_mod_cast hj₁
    have m1 : α * ((j : ℝ) * inner2 n w) ≤ α * ((k₀ : ℝ) * inner2 n w) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hj₀' hnw.le) hα
    have m2 : β * ((j : ℝ) * inner2 n w) ≤ β * ((k₁ : ℝ) * inner2 n w) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hj₁' hnw.le) hβ
    have hsum : α * ((j : ℝ) * inner2 n w) + β * ((j : ℝ) * inner2 n w) = (j : ℝ) * inner2 n w := by
      rw [← add_mul, hαβ, one_mul]
    linarith
  -- `ψ ≤ cmax` on the hull
  have hhull : Conv S₁ ⊆ {x : ℝ × ℝ | ψ x ≤ cmax} := by
    apply convexHull_min _ (convex_halfSpace_le hψlin cmax)
    rintro _ ⟨z, hz, rfl⟩
    exact hle z hz
  have hq'le : ψ q' ≤ cmax := hhull hq'C
  -- the target point, in real coordinates
  set x : ℝ × ℝ := toReal p - (j : ℝ) • toReal w with hx
  have hφx : φ x = t := by
    rw [hx, hφlin.map_sub, hφlin.map_smul, smul_eq_mul, hφR, hφR, hmw, mul_zero, sub_zero]
  have hψx : ψ x = cmax - (j : ℝ) * inner2 n w := by
    rw [hx, hψlin.map_sub, hψlin.map_smul, smul_eq_mul, hψR, hψR, hpc]
  have hpR : ψ (toReal p) = cmax := by rw [hψR, hpc]
  have hφp : φ (toReal p) = t := by rw [hφR]
  have hφp' : φ p' = t := hpval
  have hp'x : ψ p' ≤ ψ x := by linarith
  have hxp : ψ x ≤ ψ (toReal p) := by
    rw [hψx, hpR]
    have : 0 ≤ (j : ℝ) * inner2 n w := mul_nonneg (Nat.cast_nonneg _) hnw.le
    linarith
  have hxC : x ∈ Conv S₁ := by
    rcases lt_or_ge (ψ p') (ψ (toReal p)) with hlt | hge
    · set θ : ℝ := (ψ (toReal p) - ψ x) / (ψ (toReal p) - ψ p') with hθ
      have hden : 0 < ψ (toReal p) - ψ p' := by linarith
      have hθ0 : 0 ≤ θ := div_nonneg (by linarith) hden.le
      have hθ1 : θ ≤ 1 := by rw [hθ, div_le_one hden]; linarith
      have hyC : θ • p' + (1 - θ) • toReal p ∈ Conv S₁ :=
        hC hp'C (subset_Conv hp) hθ0 (by linarith) (by ring)
      have hy : θ • p' + (1 - θ) • toReal p = x := by
        apply eq_of_two_forms hmn
        · show φ _ = φ x
          rw [hφlin.map_add, hφlin.map_smul, hφlin.map_smul, smul_eq_mul, smul_eq_mul, hφp',
            hφp, hφx]; ring
        · show ψ _ = ψ x
          rw [hψlin.map_add, hψlin.map_smul, hψlin.map_smul, smul_eq_mul, smul_eq_mul, hθ]
          field_simp
          ring
      rw [← hy]; exact hyC
    · have hxp' : x = p' := by
        apply eq_of_two_forms hmn
        · show φ x = φ p'
          rw [hφx, hφp']
        · show ψ x = ψ p'
          linarith
      rw [hxp']; exact hp'C
  have : toReal (p - (j : ℤ) • w) ∈ Conv S₁ := by
    rw [toReal_sub_zsmul]; push_cast; exact hxC
  exact hS _ this

/-- The two derived normals `cutNormal true u ⊥ u` and `cutNormal ε u' ⊥ u'` are independent
exactly when `det u u' ≠ 0`. -/
theorem cutNormal_cross_ne_zero (ε : Bool) {u u' : ℤ × ℤ} (h : det u u' ≠ 0) :
    (cutNormal true u).1 * (cutNormal ε u').2 - (cutNormal true u).2 * (cutNormal ε u').1 ≠ 0 := by
  have hd : ((det u u' : ℤ) : ℝ) ≠ 0 := by exact_mod_cast h
  simp only [det, Int.cast_sub, Int.cast_mul] at hd
  cases ε <;> simp only [cutNormal, toReal, perp, Bool.false_eq_true, ↓reduceIte, Prod.fst_neg,
    Prod.snd_neg, Int.cast_neg] <;> intro hc <;> apply hd <;> linarith

/-- A `u`-run read backwards is a `(-u)`-run. -/
theorem run_neg {S₁ : Finset (ℤ × ℤ)} {c u : ℤ × ℤ} {k : ℕ}
    (h : ∀ i : ℕ, i ≤ k → c + (i : ℤ) • u ∈ S₁) :
    ∀ i : ℕ, i ≤ k → (c + (k : ℤ) • u) + (i : ℤ) • (-u) ∈ S₁ := by
  intro i hi
  have e : (c + (k : ℤ) • u) + (i : ℤ) • (-u) = c + ((k - i : ℕ) : ℤ) • u := by
    have : ((k - i : ℕ) : ℤ) = (k : ℤ) - (i : ℤ) := by omega
    rw [this]; module
  rw [e]; exact h _ (Nat.sub_le _ _)

/-- **`maxB` contains `min |top u-face| |bottom u-face| − 1` consecutive `u`-points.**

This is the wide baseline of Collé's ladder (`b3_colle2.txt:694`): each `u`-line is seeded with
`|𝒮 ∩ ℓ_𝒮| − 1` consecutive points.  Direction is `u` or `-u` (whichever points *into* the
window from the `u'`-edge); `L3Band.rayIn_sweptSeed_of_residues` is stated for `+u`, so a
consumer on the other side flips `u` — every `L1Data` field is invariant under `u ↦ -u` with
`c ↦ -c` except the explicit `c`, which is free.

Hypotheses are exactly `L1Data`'s own data constraints (`LatticeConvex S₁` from conjunct 1,
`Primitive u'` conjunct 6, `det u u' ≠ 0` conjunct 5) **plus `Primitive u`**, which `L1Data`
does not carry.  See the section note below on where `Primitive u` comes from. -/
theorem maxB_wide {S₁ : Finset (ℤ × ℤ)} (hS : Nivat.LatticeConvex S₁) (hne : S₁.Nonempty)
    {u u' : ℤ × ℤ} (hu : Primitive u) (hu' : Primitive u') (hdet : det u u' ≠ 0) (ε : Bool) :
    ∃ b₀ w : ℤ × ℤ, (w = u ∨ w = -u) ∧
      ∀ j : ℕ, j < min (topFace true u S₁).card (bottomFace true u S₁).card - 1 →
        b₀ + (j : ℤ) • w ∈ maxB (derivedQ ε u' S₁) u' ((topFace ε u' S₁).card - 1) := by
  classical
  set n := cutNormal ε u' with hn
  set m := cutNormal true u with hm
  have hn0 : n ≠ 0 := cutNormal_ne_zero ε hu'.ne_zero
  have hm0 : m ≠ 0 := cutNormal_ne_zero true hu.ne_zero
  have hnu' : inner2 n u' = 0 := inner2_cutNormal ε u'
  have hmu : inner2 m u = 0 := inner2_cutNormal true u
  have hmn : m.1 * n.2 - m.2 * n.1 ≠ 0 := cutNormal_cross_ne_zero ε hdet
  have hnu : inner2 n u ≠ 0 := fun h =>
    hdet (Nivat.Colle.det_eq_zero_of_inner2_eq_zero hn0 h hnu')
  -- the `u'`-edge, as a run
  obtain ⟨a, ha, harun⟩ := faceIsRun (cmax := levelMax S₁ n) hS hu' hn0 hnu'
    (face_levelMax_nonempty hne)
  -- the two `u`-faces, as runs
  obtain ⟨c₀, hc₀, hc₀run⟩ := faceIsRun (cmax := levelMin S₁ m) hS hu hm0 hmu
    (face_levelMin_nonempty hne)
  obtain ⟨c₁, hc₁, hc₁run⟩ := faceIsRun (cmax := levelMax S₁ m) hS hu hm0 hmu
    (face_levelMax_nonempty hne)
  set k₀ := (Nivat.R2.face S₁ m (levelMin S₁ m)).card with hk₀
  set k₁ := (Nivat.R2.face S₁ m (levelMax S₁ m)).card with hk₁
  have hk₀pos : 0 < k₀ := Finset.card_pos.mpr ⟨c₀, hc₀⟩
  have hk₁pos : 0 < k₁ := Finset.card_pos.mpr ⟨c₁, hc₁⟩
  rw [Nivat.R2.mem_face] at hc₀ hc₁
  have hrun₀ : ∀ i : ℕ, i ≤ k₀ - 1 → c₀ + (i : ℤ) • u ∈ S₁ := fun i hi =>
    (Nivat.R2.mem_face.mp (hc₀run i (by omega))).1
  have hrun₁ : ∀ i : ℕ, i ≤ k₁ - 1 → c₁ + (i : ℤ) • u ∈ S₁ := fun i hi =>
    (Nivat.R2.mem_face.mp (hc₁run i (by omega))).1
  -- the inward direction `w`, with `⟨n, w⟩ > 0`, and the runs re-anchored along it
  obtain ⟨w, hw, hnw, d₀, d₁, hd₀, hd₁, hd₀run, hd₁run⟩ :
      ∃ w : ℤ × ℤ, (w = u ∨ w = -u) ∧ 0 < inner2 n w ∧ ∃ d₀ d₁ : ℤ × ℤ,
        inner2 m d₀ = levelMin S₁ m ∧ inner2 m d₁ = levelMax S₁ m ∧
        (∀ i : ℕ, i ≤ k₀ - 1 → d₀ + (i : ℤ) • w ∈ S₁) ∧
        (∀ i : ℕ, i ≤ k₁ - 1 → d₁ + (i : ℤ) • w ∈ S₁) := by
    rcases lt_or_gt_of_ne hnu with hneg | hpos
    · refine ⟨-u, Or.inr rfl, by rw [inner2_neg]; linarith, c₀ + ((k₀ - 1 : ℕ) : ℤ) • u,
        c₁ + ((k₁ - 1 : ℕ) : ℤ) • u, ?_, ?_, run_neg hrun₀, run_neg hrun₁⟩
      · rw [inner2_add, inner2_zsmul, hmu, mul_zero, add_zero, hc₀.2]
      · rw [inner2_add, inner2_zsmul, hmu, mul_zero, add_zero, hc₁.2]
    · exact ⟨u, Or.inl rfl, hpos, c₀, c₁, hc₀.2, hc₁.2, hrun₀, hrun₁⟩
  refine ⟨a - w, -w, ?_, ?_⟩
  · rcases hw with rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl (neg_neg u)
  intro j hj
  have hbk₀ : (bottomFace true u S₁).card = k₀ := rfl
  have htk₁ : (topFace true u S₁).card = k₁ := rfl
  have hj₀ : j + 1 ≤ k₀ - 1 := by omega
  have hj₁ : j + 1 ≤ k₁ - 1 := by omega
  -- every point of the `u'`-edge, pulled back `j + 1` steps, lies in `Q`
  have key : ∀ i : ℕ, i < (topFace ε u' S₁).card →
      (a + (i : ℤ) • u') - ((j + 1 : ℕ) : ℤ) • w ∈ derivedQ ε u' S₁ := by
    intro i hi
    have hpi := Nivat.R2.mem_face.mp (harun i hi)
    have hmem : (a + (i : ℤ) • u') - ((j + 1 : ℕ) : ℤ) • w ∈ S₁ :=
      sub_zsmul_mem_of_runs hS hmn (w := w) (by rcases hw with rfl | rfl <;>
          simp [hmu, inner2_neg]) hnw (le_levelMax hne) (levelMin_le hne) (le_levelMax hne)
        hd₀ hd₁ hd₀run hd₁run hpi.1 hpi.2 hj₀ hj₁
    refine Finset.mem_filter.mpr ⟨hmem, ?_⟩
    rw [sub_eq_add_neg, inner2_add, inner2_neg, inner2_zsmul, hpi.2]
    have : 0 < ((j + 1 : ℕ) : ℤ) * inner2 n w := by
      push_cast
      exact mul_pos (by positivity) hnw
    linarith
  have e : ∀ i : ℕ, (a - w) + (j : ℤ) • (-w) + (i : ℤ) • u' =
      (a + (i : ℤ) • u') - ((j + 1 : ℕ) : ℤ) • w := by
    intro i; push_cast; module
  refine mem_maxB.mpr ⟨?_, ?_⟩
  · have := key 0 (Finset.card_pos.mpr ⟨a, ha⟩)
    have e0 : (a - w) + (j : ℤ) • (-w) = (a + ((0 : ℕ) : ℤ) • u') - ((j + 1 : ℕ) : ℤ) • w := by
      push_cast; module
    rw [e0]; exact this
  · intro i hi
    rw [e]
    exact key i (by omega)

/-! ### The same at every level: Collé's parallelogram, bottom slab

`maxB_wide` places one `u`-run in `maxB`, on the level of the `u'`-edge's start `a`.  The
ladder (`L3Band.lean` §25, `hseed_assumed`) needs a run on **every** line of the cut, and a
`u'`-ray from level `L` only visits levels `≡ L (mod det u u')`.  So the seed has to be
supplied on a full residue system: `|det u u'| + 1` consecutive levels.  Those are exactly the
levels of the bottom slab `{a + s u' − t w : 0 ≤ s ≤ 1, 0 < t ≤ W}` of the parallelogram,
which is inside `S₁` (the four corners are, by the chord argument) and below the top level
(`t > 0`).  On each level the slab's lattice points are `W` consecutive `u`-translates
(`u` primitive), and each of them carries a `pw`-run along `u'` inside the parallelogram
because `s + i ≤ pw` for `s ≤ 1`, `i < pw`.  That is where `2 ≤ |u'-edge|` enters. -/

/-- A lattice point of the real parallelogram spanned at `p` by `v₁` and `N • v₂` is in `S₁`. -/
theorem mem_of_parallelogram {S₁ : Finset (ℤ × ℤ)} (hS : Nivat.LatticeConvex S₁)
    {p v₁ v₂ : ℤ × ℤ} {N : ℕ} (hN : 0 < N)
    (h00 : p ∈ S₁) (h10 : p + v₁ ∈ S₁) (h01 : p + (N : ℤ) • v₂ ∈ S₁)
    (h11 : p + v₁ + (N : ℤ) • v₂ ∈ S₁)
    {s t : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (htN : t ≤ N)
    {z : ℤ × ℤ} (hz : toReal z = toReal p + s • toReal v₁ + t • toReal v₂) : z ∈ S₁ := by
  have hC : Convex ℝ (Conv S₁) := convex_convexHull ℝ _
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hN0 : (N : ℝ) ≠ 0 := hNr.ne'
  have h1 : (1 - s) • toReal p + s • toReal (p + v₁) ∈ Conv S₁ :=
    hC (subset_Conv h00) (subset_Conv h10) (by linarith) hs0 (by ring)
  have h2 : (1 - s) • toReal (p + (N : ℤ) • v₂) + s • toReal (p + v₁ + (N : ℤ) • v₂) ∈
      Conv S₁ :=
    hC (subset_Conv h01) (subset_Conv h11) (by linarith) hs0 (by ring)
  have h3 : (1 - t / N) • ((1 - s) • toReal p + s • toReal (p + v₁)) +
      (t / N) • ((1 - s) • toReal (p + (N : ℤ) • v₂) + s • toReal (p + v₁ + (N : ℤ) • v₂)) ∈
        Conv S₁ :=
    hC h1 h2 (sub_nonneg.mpr ((div_le_one hNr).mpr htN)) (div_nonneg ht0 hNr.le) (by ring)
  have e : toReal p + s • toReal v₁ + t • toReal v₂ =
      (1 - t / N) • ((1 - s) • toReal p + s • toReal (p + v₁)) +
        (t / N) • ((1 - s) • toReal (p + (N : ℤ) • v₂) + s • toReal (p + v₁ + (N : ℤ) • v₂)) := by
    apply Prod.ext <;>
      simp only [toReal, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;>
      push_cast <;> field_simp <;> ring
  exact hS z (by rw [hz, e]; exact h3)

/-- **A `w`-run of length `W` in `maxB` on each of `|det w u'| + 1` consecutive levels.**
Generic form: `n` the cut normal, `cmax` its top level on `S₁`, `a` a top-level point whose
parallelogram `{a + i u' − j w : i ≤ P, j ≤ W}` lies in `S₁` (`corner`), `w` primitive with
`⟨n, w⟩ > 0` (pointing into the window), `1 ≤ P`.  Levels are measured by `det w ·`. -/
theorem maxB_levels_core {S₁ : Finset (ℤ × ℤ)} (hS : Nivat.LatticeConvex S₁)
    {n : ℝ × ℝ} {cmax : ℝ}
    {a u' w : ℤ × ℤ} (hw : Primitive w) (hnu' : inner2 n u' = 0) (hnw : 0 < inner2 n w)
    (hD : det w u' ≠ 0) {P W : ℕ} (hP : 1 ≤ P) (ha : inner2 n a = cmax)
    (corner : ∀ i : ℕ, i ≤ P → ∀ j : ℕ, j ≤ W → a + (i : ℤ) • u' - (j : ℤ) • w ∈ S₁) :
    ∃ L₀ : ℤ, ∀ L : ℤ, L₀ ≤ L → L ≤ L₀ + |det w u'| → ∃ g : ℤ × ℤ, det w g = L ∧
      ∀ j : ℕ, j < W → g - (j : ℤ) • w ∈ maxB (S₁.filter fun z => inner2 n z < cmax) u' P := by
  classical
  obtain ⟨e, hwe⟩ := hw.exists_dual
  -- coordinates: `z = (−det e z) • w + (det w z) • e`
  have decomp : ∀ z : ℤ × ℤ, z = (-det e z) • w + det w z • e := by
    intro z
    simp only [det] at hwe
    apply Prod.ext <;>
      simp only [det, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    · linear_combination (-z.1) * hwe
    · linear_combination (-z.2) * hwe
  have ha1 : (a.1 : ℝ) = -(det e a : ℝ) * w.1 + (det w a : ℝ) * e.1 := by
    have h := congrArg Prod.fst (decomp a)
    simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul] at h
    exact_mod_cast h
  have ha2 : (a.2 : ℝ) = -(det e a : ℝ) * w.2 + (det w a : ℝ) * e.2 := by
    have h := congrArg Prod.snd (decomp a)
    simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul] at h
    exact_mod_cast h
  have hu'1 : (u'.1 : ℝ) = -(det e u' : ℝ) * w.1 + (det w u' : ℝ) * e.1 := by
    have h := congrArg Prod.fst (decomp u')
    simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul] at h
    exact_mod_cast h
  have hu'2 : (u'.2 : ℝ) = -(det e u' : ℝ) * w.2 + (det w u' : ℝ) * e.2 := by
    have h := congrArg Prod.snd (decomp u')
    simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul] at h
    exact_mod_cast h
  have hdet_e : ∀ m L : ℤ, det w (m • w + L • e) = L := by
    intro m L
    simp only [det] at hwe
    simp only [det, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    linear_combination L * hwe
  have hDr : (det w u' : ℝ) ≠ 0 := by exact_mod_cast hD
  refine ⟨min (det w a) (det w a + det w u'), fun L h1 h2 => ?_⟩
  -- the real `u'`-coordinate `s ∈ [0, 1]` of level `L`
  obtain ⟨s, hs0, hs1, hsD⟩ : ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ s * (det w u' : ℝ) = L - det w a := by
    refine ⟨((L : ℝ) - det w a) / det w u', ?_, ?_, div_mul_cancel₀ _ hDr⟩ <;>
      rcases lt_or_gt_of_ne hD with hneg | hpos
    · rw [abs_of_neg hneg] at h2
      have hDr' : (det w u' : ℝ) < 0 := by exact_mod_cast hneg
      have : (L : ℝ) ≤ det w a := by exact_mod_cast (show L ≤ det w a by omega)
      exact div_nonneg_of_nonpos (by linarith) hDr'.le
    · rw [abs_of_pos hpos] at h2
      have hDr' : (0 : ℝ) < det w u' := by exact_mod_cast hpos
      have : (det w a : ℝ) ≤ L := by exact_mod_cast (show det w a ≤ L by omega)
      exact div_nonneg (by linarith) hDr'.le
    · rw [abs_of_neg hneg] at h2
      have hDr' : (det w u' : ℝ) < 0 := by exact_mod_cast hneg
      have : (det w a : ℝ) + det w u' ≤ L := by
        exact_mod_cast (show det w a + det w u' ≤ L by omega)
      rw [div_le_one_of_neg hDr']; linarith
    · rw [abs_of_pos hpos] at h2
      have hDr' : (0 : ℝ) < det w u' := by exact_mod_cast hpos
      have : (L : ℝ) ≤ det w a + det w u' := by
        exact_mod_cast (show L ≤ det w a + det w u' by omega)
      rw [div_le_one hDr']; linarith
  rcases Nat.eq_zero_or_pos W with hW0 | hWpos
  · exact ⟨0 • w + L • e, hdet_e 0 L, fun j hj => absurd hj (by omega)⟩
  -- the `w`-coordinate: the last lattice point strictly below the top on level `L`
  obtain ⟨m, hm1, hm2⟩ : ∃ m : ℤ, (m : ℝ) < -(det e a : ℝ) - s * det e u' ∧
      -(det e a : ℝ) - s * det e u' ≤ m + 1 :=
    ⟨⌈-(det e a : ℝ) - s * det e u'⌉ - 1,
      by push_cast; linarith [Int.ceil_lt_add_one (-(det e a : ℝ) - s * det e u')],
      by push_cast; linarith [Int.le_ceil (-(det e a : ℝ) - s * det e u')]⟩
  refine ⟨m • w + L • e, hdet_e m L, fun j hj => ?_⟩
  have hjW : (j : ℝ) + 1 ≤ W := by exact_mod_cast (show j + 1 ≤ W by omega)
  set t : ℝ := -(det e a : ℝ) - s * det e u' - m + j with ht
  have ht0 : 0 < t := by
    have := Nat.cast_nonneg (α := ℝ) j
    linarith
  have htW : t ≤ W := by linarith
  have key : ∀ i : ℕ, i < P →
      m • w + L • e - (j : ℤ) • w + (i : ℤ) • u' ∈ S₁.filter fun z => inner2 n z < cmax := by
    intro i hi
    have hz : toReal (m • w + L • e - (j : ℤ) • w + (i : ℤ) • u') =
        toReal (a + (i : ℤ) • u') + s • toReal u' + t • toReal (-w) := by
      apply Prod.ext
      · simp only [toReal, Prod.fst_add, Prod.fst_sub, Prod.smul_fst, Prod.fst_neg, smul_eq_mul]
        push_cast
        linear_combination (w.1 : ℝ) * ht + (-1 : ℝ) * ha1 + (-s) * hu'1 + (-(e.1 : ℝ)) * hsD
      · simp only [toReal, Prod.snd_add, Prod.snd_sub, Prod.smul_snd, Prod.snd_neg, smul_eq_mul]
        push_cast
        linear_combination (w.2 : ℝ) * ht + (-1 : ℝ) * ha2 + (-s) * hu'2 + (-(e.2 : ℝ)) * hsD
    have h00 : a + (i : ℤ) • u' ∈ S₁ := by
      have := corner i (by omega) 0 (Nat.zero_le _); simpa using this
    have h10 : a + (i : ℤ) • u' + u' ∈ S₁ := by
      have := corner (i + 1) (by omega) 0 (Nat.zero_le _)
      convert this using 1; push_cast; module
    have h01 : a + (i : ℤ) • u' + (W : ℤ) • (-w) ∈ S₁ := by
      have := corner i (by omega) W le_rfl
      convert this using 1; module
    have h11 : a + (i : ℤ) • u' + u' + (W : ℤ) • (-w) ∈ S₁ := by
      have := corner (i + 1) (by omega) W le_rfl
      convert this using 1; push_cast; module
    refine Finset.mem_filter.mpr
      ⟨mem_of_parallelogram hS hWpos h00 h10 h01 h11 hs0 hs1 ht0.le htW hz, ?_⟩
    -- strictly below the top: `⟨n, z⟩ = cmax − t ⟨n, w⟩` with `t > 0`
    have hzn : inner2 n (m • w + L • e - (j : ℤ) • w + (i : ℤ) • u') =
        inner2 n (a + (i : ℤ) • u') + s * inner2 n u' - t * inner2 n w := by
      have e1 : ((m • w + L • e - (j : ℤ) • w + (i : ℤ) • u').1 : ℝ) =
          ((a + (i : ℤ) • u').1 : ℝ) + s * (u'.1 : ℝ) + t * ((-w).1 : ℝ) := congrArg Prod.fst hz
      have e2 : ((m • w + L • e - (j : ℤ) • w + (i : ℤ) • u').2 : ℝ) =
          ((a + (i : ℤ) • u').2 : ℝ) + s * (u'.2 : ℝ) + t * ((-w).2 : ℝ) := congrArg Prod.snd hz
      simp only [inner2]
      rw [e1, e2]
      simp only [Prod.fst_neg, Prod.snd_neg, Int.cast_neg]
      ring
    have hai : inner2 n (a + (i : ℤ) • u') = cmax := by
      rw [inner2_add, inner2_zsmul, hnu', ha]; ring
    rw [hzn, hai, hnu']
    have := mul_pos ht0 hnw
    linarith
  refine mem_maxB.mpr ⟨?_, fun i hi => key i hi⟩
  have := key 0 (by omega)
  simpa using this

/-- **Collé's parallelogram `Q` (`b3_colle2.txt:627-631`), as a named object.**

`a` is the start of the `u'`-edge (a `u'`-run of the edge's full cardinality, on the top face),
`w ∈ {u, -u}` points *into* the window from that edge (`0 < ⟨n, w⟩`), and every lattice point
`a + i u' − j w` with `i ≤ |u'-edge| − 1`, `j ≤ min |top u-face| |bottom u-face| − 1` is in
`S₁`.  The four corners are Collé's `g'_0, g'_1, g'_0 − (|𝒮 ∩ ℓ_𝒮| − 1) v_ℓ,
g'_1 − (|𝒮 ∩ ℓ_𝒮| − 1) v_ℓ` with `min` in place of the `:627` WLOG.

Hoisted 2026-09-19 out of `maxB_wide_levels` (where it was the inaccessible `have corner`) so
that consumers other than `maxB` — leaf C's Collé (4.1) run, the Lemma 2.3 WLOG — can call it.
`maxB_wide_levels` below is now a corollary. -/
theorem exists_parallelogram {S₁ : Finset (ℤ × ℤ)} (hS : Nivat.LatticeConvex S₁)
    (hne : S₁.Nonempty) {u u' : ℤ × ℤ} (hu : Primitive u) (hu' : Primitive u')
    (hdet : det u u' ≠ 0) (ε : Bool) :
    ∃ a w : ℤ × ℤ, (w = u ∨ w = -u) ∧ 0 < inner2 (cutNormal ε u') w ∧
      (∀ i : ℕ, i < (topFace ε u' S₁).card → a + (i : ℤ) • u' ∈ topFace ε u' S₁) ∧
      ∀ i : ℕ, i ≤ (topFace ε u' S₁).card - 1 →
        ∀ j : ℕ, j ≤ min (topFace true u S₁).card (bottomFace true u S₁).card - 1 →
          a + (i : ℤ) • u' - (j : ℤ) • w ∈ S₁ := by
  classical
  set n := cutNormal ε u' with hn
  set m := cutNormal true u with hm
  have hn0 : n ≠ 0 := cutNormal_ne_zero ε hu'.ne_zero
  have hm0 : m ≠ 0 := cutNormal_ne_zero true hu.ne_zero
  have hnu' : inner2 n u' = 0 := inner2_cutNormal ε u'
  have hmu : inner2 m u = 0 := inner2_cutNormal true u
  have hmn : m.1 * n.2 - m.2 * n.1 ≠ 0 := cutNormal_cross_ne_zero ε hdet
  have hnu : inner2 n u ≠ 0 := fun h =>
    hdet (Nivat.Colle.det_eq_zero_of_inner2_eq_zero hn0 h hnu')
  obtain ⟨a, ha, harun⟩ := faceIsRun (cmax := levelMax S₁ n) hS hu' hn0 hnu'
    (face_levelMax_nonempty hne)
  obtain ⟨c₀, hc₀, hc₀run⟩ := faceIsRun (cmax := levelMin S₁ m) hS hu hm0 hmu
    (face_levelMin_nonempty hne)
  obtain ⟨c₁, hc₁, hc₁run⟩ := faceIsRun (cmax := levelMax S₁ m) hS hu hm0 hmu
    (face_levelMax_nonempty hne)
  set k₀ := (Nivat.R2.face S₁ m (levelMin S₁ m)).card with hk₀
  set k₁ := (Nivat.R2.face S₁ m (levelMax S₁ m)).card with hk₁
  have hk₀pos : 0 < k₀ := Finset.card_pos.mpr ⟨c₀, hc₀⟩
  have hk₁pos : 0 < k₁ := Finset.card_pos.mpr ⟨c₁, hc₁⟩
  rw [Nivat.R2.mem_face] at hc₀ hc₁
  have hrun₀ : ∀ i : ℕ, i ≤ k₀ - 1 → c₀ + (i : ℤ) • u ∈ S₁ := fun i hi =>
    (Nivat.R2.mem_face.mp (hc₀run i (by omega))).1
  have hrun₁ : ∀ i : ℕ, i ≤ k₁ - 1 → c₁ + (i : ℤ) • u ∈ S₁ := fun i hi =>
    (Nivat.R2.mem_face.mp (hc₁run i (by omega))).1
  obtain ⟨w, hw, hnw, d₀, d₁, hd₀, hd₁, hd₀run, hd₁run⟩ :
      ∃ w : ℤ × ℤ, (w = u ∨ w = -u) ∧ 0 < inner2 n w ∧ ∃ d₀ d₁ : ℤ × ℤ,
        inner2 m d₀ = levelMin S₁ m ∧ inner2 m d₁ = levelMax S₁ m ∧
        (∀ i : ℕ, i ≤ k₀ - 1 → d₀ + (i : ℤ) • w ∈ S₁) ∧
        (∀ i : ℕ, i ≤ k₁ - 1 → d₁ + (i : ℤ) • w ∈ S₁) := by
    rcases lt_or_gt_of_ne hnu with hneg | hpos
    · refine ⟨-u, Or.inr rfl, by rw [inner2_neg]; linarith, c₀ + ((k₀ - 1 : ℕ) : ℤ) • u,
        c₁ + ((k₁ - 1 : ℕ) : ℤ) • u, ?_, ?_, run_neg hrun₀, run_neg hrun₁⟩
      · rw [inner2_add, inner2_zsmul, hmu, mul_zero, add_zero, hc₀.2]
      · rw [inner2_add, inner2_zsmul, hmu, mul_zero, add_zero, hc₁.2]
    · exact ⟨u, Or.inl rfl, hpos, c₀, c₁, hc₀.2, hc₁.2, hrun₀, hrun₁⟩
  have hbk₀ : (bottomFace true u S₁).card = k₀ := rfl
  have htk₁ : (topFace true u S₁).card = k₁ := rfl
  have htc : (topFace ε u' S₁).card = (Nivat.R2.face S₁ n (levelMax S₁ n)).card := rfl
  have hmw : inner2 m w = 0 := by rcases hw with rfl | rfl <;> simp [hmu, inner2_neg]
  refine ⟨a, w, hw, hnw, harun, ?_⟩
  intro i hi j hj
  have hmin₁ := Nat.min_le_left (topFace true u S₁).card (bottomFace true u S₁).card
  have hmin₀ := Nat.min_le_right (topFace true u S₁).card (bottomFace true u S₁).card
  have hapos : 0 < (topFace ε u' S₁).card := Finset.card_pos.mpr ⟨a, ha⟩
  have hpi := Nivat.R2.mem_face.mp (harun i (by omega))
  exact sub_zsmul_mem_of_runs hS hmn (w := w) hmw hnw (le_levelMax hne) (levelMin_le hne)
    (le_levelMax hne) hd₀ hd₁ hd₀run hd₁run hpi.1 hpi.2 (by omega) (by omega)

/-- **`maxB` seeds every level.**  On `|det u u'| + 1` consecutive `det u`-levels — a complete
residue system for the `u'`-ray — `maxB` contains `min |top u-face| |bottom u-face| − 1`
consecutive `u`-points.  Direction `w₀ ∈ {u, −u}` as in `maxB_wide`.  The one hypothesis
beyond `maxB_wide`'s is `2 ≤ |u'-edge|`, i.e. `1 ≤ pw`, which is what the parallelogram's
bottom slab needs to carry `pw`-runs; at the call site `0 < pw` is forced
(`pos_pw_of_case1_hyps`, `RegionSteps.lean`).

Since 2026-09-19 a corollary of `exists_parallelogram` + `maxB_levels_core`; statement
unchanged. -/
theorem maxB_wide_levels {S₁ : Finset (ℤ × ℤ)} (hS : Nivat.LatticeConvex S₁) (hne : S₁.Nonempty)
    {u u' : ℤ × ℤ} (hu : Primitive u) (hu' : Primitive u') (hdet : det u u' ≠ 0) (ε : Bool)
    (hpw : 2 ≤ (topFace ε u' S₁).card) :
    ∃ w₀ : ℤ × ℤ, (w₀ = u ∨ w₀ = -u) ∧ ∃ L₀ : ℤ, ∀ L : ℤ, L₀ ≤ L → L ≤ L₀ + |det u u'| →
      ∃ g : ℤ × ℤ, det u g = L ∧
        ∀ j : ℕ, j < min (topFace true u S₁).card (bottomFace true u S₁).card - 1 →
          g + (j : ℤ) • w₀ ∈ maxB (derivedQ ε u' S₁) u' ((topFace ε u' S₁).card - 1) := by
  classical
  obtain ⟨a, w, hw, hnw, harun, corner⟩ := exists_parallelogram hS hne hu hu' hdet ε
  have hnu' : inner2 (cutNormal ε u') u' = 0 := inner2_cutNormal ε u'
  have ha := Nivat.R2.mem_face.mp (harun 0 (by omega))
  simp only [Nat.cast_zero, zero_smul, add_zero] at ha
  have hwprim : Primitive w := by
    rcases hw with rfl | rfl
    · exact hu
    · show IsCoprime (-u.1) (-u.2); exact hu.neg_neg
  have hDw : det w u' ≠ 0 := by
    rcases hw with rfl | rfl
    · exact hdet
    · intro h; apply hdet; simp only [det, Prod.fst_neg, Prod.snd_neg] at h ⊢; linarith
  obtain ⟨L₀', hL⟩ := maxB_levels_core hS hwprim hnu' hnw hDw
    (P := (topFace ε u' S₁).card - 1) (by omega) ha.2 corner
  refine ⟨-w, ?_, ?_⟩
  · rcases hw with rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl (neg_neg u)
  rcases hw with hwu | hwu
  · rw [hwu] at hL
    refine ⟨L₀', fun L h1 h2 => ?_⟩
    obtain ⟨g, hg, hrun⟩ := hL L h1 h2
    refine ⟨g, hg, fun j hj => ?_⟩
    have e' : g + (j : ℤ) • (-w) = g - (j : ℤ) • w := by module
    rw [e', hwu]; exact hrun j hj
  · rw [hwu] at hL
    have hneg : det (-u) u' = -det u u' := by simp only [det, Prod.fst_neg, Prod.snd_neg]; ring
    refine ⟨-L₀' - |det u u'|, fun L h1 h2 => ?_⟩
    obtain ⟨g, hg, hrun⟩ := hL (-L) (by omega) (by rw [hneg, abs_neg]; omega)
    refine ⟨g, ?_, fun j hj => ?_⟩
    · have : det (-u) g = -det u g := by simp only [det, Prod.fst_neg, Prod.snd_neg]; ring
      omega
    · have e' : g + (j : ℤ) • (-w) = g - (j : ℤ) • w := by module
      rw [e', hwu]; exact hrun j hj

/-- `det u g` is the `(-u.2, u.1)`-level of `g`: the level convention of `maxB_wide_levels`
agrees with the one `L3Band.HasBlock` measures levels by. -/
theorem det_eq_dot_perp (u g : ℤ × ℤ) : det u g = Nivat.LE2.dot (-u.2, u.1) g := by
  simp only [det, Nivat.LE2.dot]; ring

/-- **The block export.**  `maxB_wide_levels` re-indexed by residues: a base `g₀` and, at each
of the `|det u u'|` consecutive levels `⟪(-u.2, u.1), g₀⟫ + ρ`, a `u`-run of width
`min(faces) − 1` inside `maxB`.  This is byte-for-byte the hypothesis of
`L3Band.hasBlock_of_either` at `B := maxB (derivedQ ε u' S₁) u' ((topFace ε u' S₁).card - 1)`,
so the consumer converts it to `HasBlock` with no glue.  `maxB_wide_levels` gives one level
more than needed (`L ≤ L₀ + |det u u'|`); only `ρ < |det u u'|` is used.

A `u'`-ray from level `L` visits only levels `≡ L (mod |det u u'|)`, so all residues are
genuinely needed downstream (`L3Band.seed_of_block`); this theorem shows `maxB` meets at least
`|det u u'| + 1` consecutive levels, one to spare, whenever the `u'`-edge has two points. -/
theorem maxB_block {S₁ : Finset (ℤ × ℤ)} (hS : Nivat.LatticeConvex S₁) (hne : S₁.Nonempty)
    {u u' : ℤ × ℤ} (hu : Primitive u) (hu' : Primitive u') (hdet : det u u' ≠ 0) (ε : Bool)
    (hpw : 2 ≤ (topFace ε u' S₁).card) :
    ∃ (g₀ w : ℤ × ℤ), (w = u ∨ w = -u) ∧
      ∀ ρ : ℕ, ρ < (det u u').natAbs → ∃ g : ℤ × ℤ,
        Nivat.LE2.dot (-u.2, u.1) g = Nivat.LE2.dot (-u.2, u.1) g₀ + ρ ∧
        ∀ j : ℕ, j < min (topFace true u S₁).card (bottomFace true u S₁).card - 1 →
          g + (j : ℤ) • w ∈ maxB (derivedQ ε u' S₁) u' ((topFace ε u' S₁).card - 1) := by
  obtain ⟨w, hw, L₀, hL⟩ := maxB_wide_levels hS hne hu hu' hdet ε hpw
  have habs : (0 : ℤ) ≤ |det u u'| := abs_nonneg _
  obtain ⟨g₀, hg₀, -⟩ := hL L₀ le_rfl (by linarith)
  refine ⟨g₀, w, hw, fun ρ hρ => ?_⟩
  have hρ' : (ρ : ℤ) ≤ |det u u'| := by
    rw [Int.abs_eq_natAbs]; exact_mod_cast hρ.le
  obtain ⟨g, hg, hrun⟩ := hL (L₀ + ρ) (by linarith) (by linarith)
  refine ⟨g, ?_, hrun⟩
  rw [← det_eq_dot_perp, ← det_eq_dot_perp, hg, hg₀]

/-! ### Where the width comes from: Lemma 2.3 (`b3_colle2.txt:627`)

`maxB_wide`'s width `min |top u-face| |bottom u-face| − 1` is `0` unless **both** `u`-faces are
edges.  Collé gets that from *"since the oriented lines `−ℓ, ℓ ∈ nexpd(η)`, from Lemma 2.3 we get
that `𝒮` has an edge parallel to `ℓ` and another one parallel to `−ℓ`"*.  In the tree Lemma 2.3
is `Nivat.R2.two_le_face_card_of_mem_ONED` (`R2Orientation.lean:171`) for a *real* normal in
`ONED ξ`; the leaf carries the integer forms `hℓ_nel : ℓ ∈ Colle45.NonExpansiveLine ξ` and (since
2026-09-19, `RegionSteps.lean`) `hℓ_pos / hℓ_neg : Colle45.IsOneSidedNonexpansive ξ (±ℓ)`.  The
bridge for the latter is `ONEDRational.toReal_mem_ONED_of_isOneSidedNonexpansive`
(`ONEDRational.lean:169`, found by the §20 scan after a duplicate had been drafted and deleted);
the former is bridged here, same six lines. -/

/-- **`NonExpansiveLine` (integer, `Lemma45.lean:85`) embeds into `ONED` (real,
`ExternalDefs.lean:32`) via `toReal`.**  Both are "two distinct points of the orbit closure
agree on a closed half-plane"; `halfPlaneLE v 0 = {dot v · ≤ 0}` and `sideOf w = {inner2 w · ≤ 0}`
coincide under `inner2_toReal`.  This is the bridge from the leaf's `hℓ_nel` to
`Nivat.R2.two_le_face_card_of_mem_ONED` (Lemma 2.3). -/
theorem toReal_mem_ONED_of_mem_nonExpansiveLine {ξ : Config ℤ} {v : ℤ × ℤ}
    (h : v ∈ Colle45.NonExpansiveLine ξ) : toReal v ∈ ONED ξ := by
  obtain ⟨hprim, x, y, hx, hy, hxy, hagree⟩ := h
  refine ⟨Nivat.KM.toReal_ne_zero hprim.ne_zero, x, hx, y, hy, hxy, fun z hz => ?_⟩
  apply hagree
  show Nivat.LE2.dot v z ≤ 0
  have : inner2 (toReal v) z ≤ 0 := hz
  rw [Nivat.LE2.inner2_toReal] at this
  exact_mod_cast this

/-- **Lemma 2.3 for the two `u`-faces** (`b3_colle2.txt:627`: "`𝒮` has an edge parallel to `ℓ`
and another one parallel to `−ℓ`").  Both orientations of the normal `perp u` in `ONED ξ`
make both `u`-faces of a generating set edges, i.e. `2 ≤ min |top| |bottom|` — exactly the
hypothesis `maxB_nonempty_of_two_le_faces` needs. -/
theorem two_le_min_faces_of_ONED {ξ : Config ℤ} {S₁ : Finset (ℤ × ℤ)}
    (hgen : Nivat.Colle.IsGeneratingSet ξ S₁) (u : ℤ × ℤ)
    (hpos : toReal (perp u) ∈ ONED ξ) (hneg : toReal (-perp u) ∈ ONED ξ) :
    2 ≤ min (topFace true u S₁).card (bottomFace true u S₁).card := by
  have hne : S₁.Nonempty := hgen.1
  have hm : cutNormal true u = toReal (perp u) := by simp [cutNormal]
  refine le_min ?_ ?_
  · unfold topFace
    rw [hm]
    exact Nivat.R2.two_le_face_card_of_mem_ONED hgen (le_levelMax hne)
      (face_levelMax_nonempty hne) hpos
  · unfold bottomFace
    rw [← Nivat.R2.face_neg_level, hm, ← Nivat.KM.toReal_neg]
    refine Nivat.R2.two_le_face_card_of_mem_ONED hgen ?_ ?_ hneg
    · intro z hz
      rw [Nivat.KM.toReal_neg, Nivat.R2.inner2_neg_left, neg_le_neg_iff, ← hm]
      exact levelMin_le hne z hz
    · rw [Nivat.KM.toReal_neg, Nivat.R2.face_neg_level, ← hm]
      exact face_levelMin_nonempty hne

/-- **Lemma 2.3 from the leaf's own vocabulary.**  `hℓ_nel : ℓ ∈ NonExpansiveLine ξ` (which
`exists_L1MaxBResidual` binds) together with `hℓ_neg : IsOneSidedNonexpansive ξ (-ℓ)` (which it
does **not** bind, but which is in scope at the only call site, `ColleRegion.lean:356`) and
`vl ∥ ℓ` (`hdet_ℓ : dot ℓ vl = 0`, `Primitive vl`) give: both `vl`-faces of a generating set
are edges.  `ℓ = ±perp vl` by primitivity, so the two orientations of `perp vl` are `ℓ` and
`-ℓ` in some order. -/
theorem two_le_min_faces_of_nel {ξ : Config ℤ} {S₁ : Finset (ℤ × ℤ)}
    (hgen : Nivat.Colle.IsGeneratingSet ξ S₁) {ℓ vl : ℤ × ℤ}
    (hℓ_nel : ℓ ∈ Colle45.NonExpansiveLine ξ) (hℓ_neg : Colle45.IsOneSidedNonexpansive ξ (-ℓ))
    (hvl : Primitive vl) (hdet_ℓ : Nivat.LE2.dot ℓ vl = 0) :
    2 ≤ min (topFace true vl S₁).card (bottomFace true vl S₁).card := by
  have hℓp : Primitive ℓ := hℓ_nel.1
  have hℓ0 : ℓ ≠ 0 := hℓp.ne_zero
  have hpos : toReal ℓ ∈ ONED ξ := toReal_mem_ONED_of_mem_nonExpansiveLine hℓ_nel
  have hneg : toReal (-ℓ) ∈ ONED ξ :=
    Nivat.ONEDRational.toReal_mem_ONED_of_isOneSidedNonexpansive (neg_ne_zero.mpr hℓ0) hℓ_neg
  have hd : det (perp vl) ℓ = 0 := by
    simp only [det, perp, Nivat.LE2.dot] at hdet_ℓ ⊢; linarith
  rcases eq_or_eq_neg_of_det_eq_zero (primitive_perp hvl) hℓp hd with h | h
  · exact two_le_min_faces_of_ONED hgen vl (h ▸ hpos) (h ▸ hneg)
  · have h' : perp vl = -ℓ := by rw [h, neg_neg]
    exact two_le_min_faces_of_ONED hgen vl (h' ▸ hneg) (by rw [h', neg_neg]; exact hpos)

/-- **`maxB` is nonempty as soon as both `u`-faces are edges** (`2 ≤ min |top| |bottom|`).
This is the exact point where Lemma 2.3 (`b3_colle2.txt:627`, "an edge parallel to `ℓ` and
another one parallel to `−ℓ`") enters `base0`; without it the width of `maxB_wide` is `0` and
`maxB` may be empty (`no_nonempty_B_run_943`'s triangle). -/
theorem maxB_nonempty_of_two_le_faces {S₁ : Finset (ℤ × ℤ)} (hS : Nivat.LatticeConvex S₁)
    (hne : S₁.Nonempty) {u u' : ℤ × ℤ} (hu : Primitive u) (hu' : Primitive u')
    (hdet : det u u' ≠ 0) (ε : Bool)
    (h2 : 2 ≤ min (topFace true u S₁).card (bottomFace true u S₁).card) :
    (maxB (derivedQ ε u' S₁) u' ((topFace ε u' S₁).card - 1)).Nonempty := by
  obtain ⟨b₀, w, -, hb⟩ := maxB_wide hS hne hu hu' hdet ε
  refine ⟨b₀, ?_⟩
  have := hb 0 (by omega)
  simpa using this

/-! ### `base0`'s second half: a region absorbs a translate of any finite set

Conjunct 16 asks for `∃ b ∈ B, ∀ z ∈ S₁, b + z ∈ R`.  Its two halves have different owners:
`b ∈ maxB` is `maxB_nonempty_of_two_le_faces` above (Lemma 2.3), and "`b + S₁ ⊆ R` for *some*
`b`" is pure recession-cone geometry, proved here with no window data at all.  What neither gives
is the **same** `b` for both — that coupling is the strong form's whole content, and as of
2026-09-19 no consumer in `RegionSteps.lean` destructures it (`case1_sweep` takes
`B.Nonempty ∧ ∃ b, …`, `region_case1:1521` forgets `b ∈ B` before passing it on). -/

/-- Cramer: `det u u' • z = det z u' • u + det u z • u'`.  §20: the tree has this only as
`private` copies (`HalfPlaneDoublyPeriodic.lean:172`, `L3Band.lean:1335`, `Claim414Ell.lean:34`)
and as `Claim411.toReal_cramer` downstream; this is the first public integer form on L1's path. -/
theorem det_smul_eq_det_smul_add_det_smul (u u' z : ℤ × ℤ) :
    det u u' • z = det z u' • u + det u z • u' := by
  ext <;> simp only [det, Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add,
    smul_eq_mul] <;> ring

/-- **A region absorbs a translate of any finite set.**  `IsRegion R u u'` gives a `u`-ray and a
`u'`-ray, hence `toReal u, toReal u' ∈ recCone R`; with `det u u' ≠ 0` every lattice point is a
real combination of `u, u'`, so pushing the ray base far enough along `u + u'` puts `b + S₁`
inside `R`.  This is the content of the *weak* conjunct 16 (`B.Nonempty ∧ ∃ b, ∀ z ∈ S₁,
b + z ∈ R`), which is the shape every consumer in `RegionSteps.lean` actually destructures. -/
theorem exists_translate_subset_of_isRegion {R : Set (ℤ × ℤ)} {u u' : ℤ × ℤ}
    (hR : Colle41.IsRegion R u u') (hdet : det u u' ≠ 0) (S₁ : Finset (ℤ × ℤ)) :
    ∃ b : ℤ × ℤ, ∀ z ∈ S₁, b + z ∈ R := by
  classical
  obtain ⟨hconv, ⟨z₀, hray⟩, ⟨z₀', hray'⟩⟩ := hR
  have hu : toReal u ∈ recCone R := toReal_mem_recCone_of_nat_ray hray
  have hu' : toReal u' ∈ recCone R := toReal_mem_recCone_of_nat_ray hray'
  set D : ℝ := (det u u' : ℝ) with hD
  have hD0 : D ≠ 0 := by rw [hD]; exact_mod_cast hdet
  -- real coordinates of `z` in the basis `u, u'`
  set α : ℤ × ℤ → ℝ := fun z => (det z u' : ℝ) / D with hα
  set β : ℤ × ℤ → ℝ := fun z => (det u z : ℝ) / D with hβ
  have hcoord : ∀ z : ℤ × ℤ, toReal z = α z • toReal u + β z • toReal u' := by
    intro z
    have h := congrArg toReal (det_smul_eq_det_smul_add_det_smul u u' z)
    rw [toReal_zsmul, toReal_add, toReal_zsmul, toReal_zsmul] at h
    have h' : toReal z = D⁻¹ • ((det z u' : ℝ) • toReal u + (det u z : ℝ) • toReal u') := by
      rw [← h, smul_smul, inv_mul_cancel₀ hD0, one_smul]
    rw [h', smul_add, smul_smul, smul_smul, hα, hβ]
    simp only [div_eq_inv_mul]
  -- a uniform lower bound on the coordinates over `S₁`
  obtain ⟨K, hK⟩ : ∃ K : ℕ, ∀ z ∈ S₁, -(K : ℝ) ≤ α z ∧ -(K : ℝ) ≤ β z := by
    obtain ⟨M, hM⟩ := (S₁.image fun z => max (-α z) (-β z)).exists_le
    refine ⟨⌈M⌉₊, fun z hz => ?_⟩
    have := hM _ (Finset.mem_image_of_mem _ hz)
    have hM' : M ≤ (⌈M⌉₊ : ℝ) := Nat.le_ceil M
    exact ⟨by linarith [le_max_left (-α z) (-β z)], by linarith [le_max_right (-α z) (-β z)]⟩
  refine ⟨z₀ + (K : ℤ) • u + (K : ℤ) • u', fun z hz => ?_⟩
  obtain ⟨hKα, hKβ⟩ := hK z hz
  have hmem : toReal ((K : ℤ) • u + (K : ℤ) • u' + z) ∈ recCone R := by
    rw [toReal_add, toReal_add, toReal_zsmul, toReal_zsmul, hcoord z]
    have e : (K : ℝ) • toReal u + (K : ℝ) • toReal u' + (α z • toReal u + β z • toReal u')
        = ((K : ℝ) + α z) • toReal u + ((K : ℝ) + β z) • toReal u' := by
      simp only [add_smul]; abel
    push_cast
    rw [e]
    exact add_mem_recCone (smul_mem_recCone (by linarith) hu) (smul_mem_recCone (by linarith) hu')
  have hz₀ : z₀ ∈ R := by simpa using hray 0
  have := add_mem_of_mem_recCone hconv hmem hz₀
  convert this using 1
  abel

/-- **`c0` is free.**  `p ∥ vl` (`hdet_vl : det p vl = 0`), `Primitive vl`, `p ≠ 0` give
`p = c • vl` with `c ≠ 0` — the period `p` of `x_per` along `vl` is the `c • u` of conjunct 9
with `u := vl`.  No Claim 4.6 is involved (integrator's correction, 2026-09-19). -/
theorem exists_zsmul_ne_zero_of_parallel {p vl : ℤ × ℤ} (hvl : Primitive vl)
    (hdet_vl : det p vl = 0) (hp : p ≠ 0) : ∃ c : ℤ, c ≠ 0 ∧ p = c • vl := by
  have hd : det vl p = 0 := by simp only [det] at hdet_vl ⊢; linarith
  obtain ⟨c, hc⟩ := eq_zsmul_of_det_eq_zero hvl hd
  refine ⟨c, fun h0 => hp ?_, hc⟩
  rw [hc, h0, zero_smul]

/-! ### `base0` closes (2026-09-19, after the `hbase` weakening ruling)

With `MaxBResidual.base0` in its weak form the two halves proved above are the whole field:
`maxB_nonempty_of_two_le_faces` (Lemma 2.3 through `two_le_min_faces_of_nel`) and
`exists_translate_subset_of_isRegion` (recession cone of `F.R 0`).  Every input is either a
binder of `exists_L1MaxBResidual` (`hSgen`, `hℓ_nel`, `hℓ_neg`, `hvl_prim`, `hdet_ℓ`) or one of
the other five fields (`det'`, `prim`), so `MaxBResidual` is now constructible from **five**
fields plus the leaf's own binders — `MaxBResidual.ofFive`.  ⚠ This is a split, not a
reduction: `sorries.sh` is unchanged by it (`CLAUDE.md` hard rule 1). -/

/-- **`base0` from Lemma 2.3 and the recession cone.**  `h2` is the both-edges input; at the
leaf it is `two_le_min_faces_of_nel`. -/
theorem MaxBResidual.base0_of_faces {ξ : Config ℤ} {e : ℤ × ℤ} {u u' : ℤ × ℤ} {c : ℤ}
    {S₁ : Finset (ℤ × ℤ)} (F : Nivat.L1Region.RegionFamily (T e ξ) u u' c) (ε : Bool)
    (hS : Nivat.LatticeConvex S₁) (hne : S₁.Nonempty) (hu : Primitive u) (hu' : Primitive u')
    (hdet : det u u' ≠ 0)
    (h2 : 2 ≤ min (topFace true u S₁).card (bottomFace true u S₁).card) :
    (maxB (derivedQ ε u' S₁) u' ((topFace ε u' S₁).card - 1)).Nonempty ∧
      ∃ b, ∀ z ∈ S₁, b + z ∈ F.R 0 :=
  ⟨maxB_nonempty_of_two_le_faces hS hne hu hu' hdet ε h2,
    exists_translate_subset_of_isRegion (F.isRegion 0) hdet S₁⟩

/-- **`MaxBResidual` from its five remaining fields.**  `u` is the period direction, parallel
to `ℓ` (`hdet_ℓ : dot ℓ u = 0`; at the leaf `u := vl`); `hℓ_nel`, `hℓ_neg` are the two
orientations `exists_L1MaxBResidual` binds.  `base0` is not asked for. -/
theorem MaxBResidual.ofFive {ξ : Config ℤ} {e : ℤ × ℤ} (ε : Bool) {u u' : ℤ × ℤ} {c τ : ℤ}
    {S₁ : Finset (ℤ × ℤ)} (F : Nivat.L1Region.RegionFamily (T e ξ) u u' c)
    (hgen : Nivat.Colle.IsGeneratingSet ξ S₁) {ℓ : ℤ × ℤ}
    (hℓ_nel : ℓ ∈ Colle45.NonExpansiveLine ξ) (hℓ_neg : Colle45.IsOneSidedNonexpansive ξ (-ℓ))
    (hu : Primitive u) (hdet_ℓ : Nivat.LE2.dot ℓ u = 0)
    (det' : det u u' ≠ 0) (prim : Primitive u') (c0 : c ≠ 0)
    (line0 : ∀ t : ℤ, τ ≤ t → ∀ z ∈ derivedQ ε u' S₁,
      t • u' + z ∈ F.R 0 ∧ t • u' + z + c • u ∈ F.R 0)
    (straddle : ∀ N : ℕ, Colle41.PeriodOn (T e ξ) (F.R N) (c • u) →
      ¬ Colle41.PeriodOn (T e ξ) (F.R (N + 1)) (c • u) →
      Nivat.L1Region.Straddle (T e ξ) (F.R N) (F.R (N + 1)) S₁ (derivedQ ε u' S₁) u u' c τ) :
    MaxBResidual ε u u' c τ S₁ F :=
  ⟨det', prim, c0, line0,
    MaxBResidual.base0_of_faces F ε (latticeConvex_of_isGeneratingSet hgen) hgen.1 hu prim det'
      (two_le_min_faces_of_nel hgen hℓ_nel hℓ_neg hu hdet_ℓ),
    straddle⟩

end Width

/-! ### Where `Primitive u` comes from, and what `maxB_wide` does not say

* `Primitive u` is not a field of `L1Data` (conjunct 6 is `Primitive u'` only).  At the leaf,
  `exists_L1Data` binds `hvl_prim : Primitive vl` with `vl ∥ ℓ` (`hdet_ℓ : dot ℓ vl = 0`,
  `RegionSteps.lean:882-883`), and Collé's period direction is `ℓ` (`h ∥ ℓ`, `b3_colle2.txt:806`),
  so the producer's natural choice is `u := vl`.  **Reading, not a kernel fact**: no declaration
  in the tree pins `u` to `vl`.  If a producer chooses a non-primitive `u = k • vl`, `maxB_wide`
  still applies with `vl` in place of `u` and yields `vl`-consecutive points, which is stronger.
* `maxB_wide` gives width `min |top u-face| |bottom u-face| − 1`.  It is `0` when either
  `u`-face is a single vertex; that both are edges is Collé Lemma 2.3 from `−ℓ, ℓ ∈ nexpd(η)`
  (`b3_colle2.txt:627`), i.e. `two_le_face_card_of_mem_ONED` (`R2Orientation.lean:171`) at
  `w = ±cutNormal true u`, which needs `±toReal (perp u) ∈ ONED ξ`.  The leaf has `hℓ_nel`
  for one orientation; the other is not a visible binder (reading).  `maxB_wide` itself needs
  no such hypothesis — it is unconditional, and just yields an empty range in that case.
* It does not say `maxB` is a complete residue system mod `|c|` along `u`
  (`L3Band.rayIn_sweptSeed_of_residues` wants `|c|` consecutive points); it says
  `|u-edge| − 1` consecutive points, which is Collé's seed count for the *ladder*
  (`:694`), not for the swept-seed ray.  Whether `|u-edge| − 1 ≥ |c|` is a separate question
  and is **not** established here.
-/

/-! ## Guard rails

Facts recorded in the kernel so that the measurement above cannot be quoted loosely.
-/

/-- **Conjunct 15 is not free at level `0`.**  Restated here from
`Nivat.L1Region.not_straddle_four` (`L1Region.lean:460`) with the level-`0` companion, so that
the reason `Residual.straddle` quantifies over maximal indices is visible at the point where
the count is made: a family can satisfy the straddle at `0 → 1` and fail it at `4 → 5`. -/
theorem straddle_not_transported :
    Nivat.L1Region.Straddle Nivat.L1Region.wx
        (Nivat.L1Region.witness.R 0) (Nivat.L1Region.witness.R 1)
        {((0 : ℤ), (0 : ℤ))} ∅ ((1 : ℤ), (0 : ℤ)) ((0 : ℤ), (1 : ℤ)) 1 0 ∧
      ¬ Nivat.L1Region.Straddle Nivat.L1Region.wx
        (Nivat.L1Region.witness.R 4) (Nivat.L1Region.witness.R 5)
        {((0 : ℤ), (0 : ℤ))} ∅ ((1 : ℤ), (0 : ℤ)) ((0 : ℤ), (1 : ℤ)) 1 0 :=
  ⟨Nivat.L1Region.straddle_zero, Nivat.L1Region.not_straddle_four⟩

/-- **`Residual` is not the conclusion in disguise.**  Conjuncts 3, 7 and 10–13 are absent from
`Residual` and are produced by `ofPieces` from the family and the derived `Q`; this states the
two cheapest of them (3 and 12) as facts about the objects `ofPieces` actually builds, so that
the claim "six conjuncts leave no trace in the signature" is checkable and not prose. -/
theorem derived_conjuncts {ξ : Config ℤ} {u u' : ℤ × ℤ} {c : ℤ}
    {n : ℝ × ℝ} {cmax : ℝ} {S₁ : Finset (ℤ × ℤ)} {e : ℤ × ℤ}
    (F : Nivat.L1Region.RegionFamily (T e ξ) u u' c) (N : ℕ) :
    (S₁.filter fun z => inner2 n z < cmax) ⊆ S₁ ∧ F.R N ⊂ F.R (N + 1) :=
  ⟨Finset.filter_subset _ _, F.grow N⟩

/-! ## §20 record (2026-09-19 11:2x): Collé (4.1) for leaf C is `C11Bridge.exists_run`

`ColleReg.exists_case2_run` (`RegionSteps.lean:1761`) as first stated was refuted at the kernel
on `Case2WindowProbe.Gen.cgg` × the trapezoid `{(0,0),…,(4,0),(1,1),(2,1)}`
(`tmp/l1asm_case2run_refute.lean`, in `tmp/`).  The repair — five binders `hℓ_nel hℓ_neg
hvl_prim hdet_ℓ hdet_vl` carrying Lemma 2.3, conclusion unchanged — was proved here from
`exists_parallelogram` as `exists_case2_run'` and, in the same hour and independently, by lane
C11 as `C11Bridge.exists_run` (`C11Bridge.lean:126`, kernel-clean, **on the chain** via
`RegionSteps.lean:1774`).  `C11Bridge` imports this file, so the copy here was the orphan; it
was deleted the moment the scan found the other.  Two proofs of the same restatement from
opposite ends is the strongest signal this project produces that the restatement is right. -/

end L1Data

end Nivat.ColleReg

/-! ## The tail of the family, and `MaxBResidual` from data at the selected index

`MaxBResidual` states `line0` and `base0` on `F.R 0`, and `straddle` at every maximal index.
Read against each other those pin the family's index `0` to the *selected* index `N`
(`b3_colle2.txt:820`: `N` is chosen first, then `𝒯` is placed with `𝒯 ∖ ℓ'_𝒯 ⊂ 𝓡^N_I`,
`𝒯 ⊄ 𝓡^N_I`; `straddle` needs the top face outside `R N` while `line0` puts `Q` inside
`R 0 ⊆ R N`).  So a producer of Collé's full family `𝓡^n_I` hands over `F` and the maximal
`N`, and the residual is stated on the **tail** `n ↦ F.R (N + n)`.  `tail` is that self-map;
`straddle_tail` shows that on it the maximal index is `0` and only `0`; `MaxBResidual.ofTail`
is the interface: three membership facts at `N`, nothing at any other index.  Written here
rather than in `L1Region.lean` only because of file ownership (2026-09-19). -/

namespace Nivat.L1Region.RegionFamily

open Nivat Nivat.Colle41

variable {x : Config ℤ} {u u' : ℤ × ℤ} {c : ℤ}

/-- **The tail of a family from a periodic index.**  `R n := F.R (N + n)`; `base` is the
supplied periodicity at `N`, `union_not` is unchanged because the union is. -/
def tail (F : RegionFamily x u u' c) (N : ℕ) (hN : PeriodOn x (F.R N) (c • u)) :
    RegionFamily x u u' c where
  R := fun n => F.R (N + n)
  grow := fun n => F.grow (N + n)
  isRegion := fun n => F.isRegion (N + n)
  base := hN
  union_not := fun h => F.union_not
    (h.mono (Set.iUnion_subset fun k =>
      Set.subset_iUnion_of_subset k (F.monotone (Nat.le_add_left k N))))

@[simp] theorem tail_R (F : RegionFamily x u u' c) (N : ℕ) (hN : PeriodOn x (F.R N) (c • u))
    (n : ℕ) : (F.tail N hN).R n = F.R (N + n) := rfl

/-- On the tail from a **maximal** periodic index, the only index at which
"periodic here, not at the next" holds is `0`; so a `Straddle` at `(N, N+1)` is the whole of
`MaxBResidual.straddle` for the tail. -/
theorem straddle_tail (F : RegionFamily x u u' c) (N : ℕ)
    (hN : PeriodOn x (F.R N) (c • u)) (hN1 : ¬ PeriodOn x (F.R (N + 1)) (c • u))
    {S₁ Q : Finset (ℤ × ℤ)} {τ : ℤ}
    (h : Straddle x (F.R N) (F.R (N + 1)) S₁ Q u u' c τ) :
    ∀ N' : ℕ, PeriodOn x ((F.tail N hN).R N') (c • u) →
      ¬ PeriodOn x ((F.tail N hN).R (N' + 1)) (c • u) →
      Straddle x ((F.tail N hN).R N') ((F.tail N hN).R (N' + 1)) S₁ Q u u' c τ := by
  intro N' hp _
  cases N' with
  | zero => exact h
  | succ k =>
    exact absurd (hp.mono (F.monotone (by omega : N + 1 ≤ N + (k + 1)))) hN1

end Nivat.L1Region.RegionFamily

namespace Nivat.ColleReg.L1Data

open Nivat Nivat.Colle35

/-- **Conjunct 14 from its seed at `t = τ`.**  A region absorbs its `u'`-ray direction
(`add_mem_of_mem_recCone`), so membership at `t = τ` propagates to every `t ≥ τ`. -/
theorem line_of_seed {R : Set (ℤ × ℤ)} {u u' : ℤ × ℤ} (hR : Colle41.IsRegion R u u')
    {Q : Finset (ℤ × ℤ)} {τ c : ℤ}
    (h : ∀ z ∈ Q, τ • u' + z ∈ R ∧ τ • u' + z + c • u ∈ R) :
    ∀ t : ℤ, τ ≤ t → ∀ z ∈ Q, t • u' + z ∈ R ∧ t • u' + z + c • u ∈ R := by
  intro t ht z hz
  obtain ⟨hconv, -, ⟨z₀', hray'⟩⟩ := hR
  have hrec : ∀ g ∈ R, g + u' ∈ R := fun g hg =>
    add_mem_of_mem_recCone hconv (toReal_mem_recCone_of_nat_ray hray') hg
  have step : ∀ g ∈ R, ∀ k : ℕ, g + (k : ℤ) • u' ∈ R := by
    intro g hg k
    induction k with
    | zero => simpa using hg
    | succ k ih =>
      have := hrec _ ih
      convert this using 1
      push_cast
      rw [add_smul, one_smul, add_assoc]
  obtain ⟨k, hk⟩ : ∃ k : ℕ, t = τ + k := ⟨(t - τ).toNat, by omega⟩
  refine ⟨?_, ?_⟩
  · have := step _ (h z hz).1 k
    convert this using 1
    rw [hk, add_smul]; abel
  · have := step _ (h z hz).2 k
    convert this using 1
    rw [hk, add_smul]; abel

/-- **`MaxBResidual` on the tail, from data at the selected index only.**  The consumer-side
interface for a producer of Collé's family `𝓡^n_I` (`b3_colle2.txt:816`): supply the full
family `F`, the maximal periodic index `N`, and the three membership facts at `N` — `line`
only at its seed `t = τ`, `base` for one `b ∈ maxB`, and one `Straddle` across `(N, N+1)` —
and `MaxBResidual` follows for `F.tail N hN`.  The three scalar fields pass through. -/
theorem MaxBResidual.ofTail {ξ : Config ℤ} {e : ℤ × ℤ} (ε : Bool) {u u' : ℤ × ℤ} {c τ : ℤ}
    {S₁ : Finset (ℤ × ℤ)} (F : Nivat.L1Region.RegionFamily (T e ξ) u u' c) (N : ℕ)
    (hN : Colle41.PeriodOn (T e ξ) (F.R N) (c • u))
    (hN1 : ¬ Colle41.PeriodOn (T e ξ) (F.R (N + 1)) (c • u))
    (det' : det u u' ≠ 0) (prim : Primitive u') (c0 : c ≠ 0)
    (line : ∀ z ∈ derivedQ ε u' S₁, τ • u' + z ∈ F.R N ∧ τ • u' + z + c • u ∈ F.R N)
    (base : (maxB (derivedQ ε u' S₁) u' ((topFace ε u' S₁).card - 1)).Nonempty ∧
      ∃ b, ∀ z ∈ S₁, b + z ∈ F.R N)
    (straddle : Nivat.L1Region.Straddle (T e ξ) (F.R N) (F.R (N + 1)) S₁ (derivedQ ε u' S₁)
      u u' c τ) :
    MaxBResidual ε u u' c τ S₁ (F.tail N hN) :=
  ⟨det', prim, c0, line_of_seed (F.isRegion N) line, base,
    Nivat.L1Region.RegionFamily.straddle_tail F N hN hN1 straddle⟩

/-- `det vl u' ≠ 0` from unimodularity of `(u', vl)`.  Consumer:
`L1Claim.exists_L1MaxBResidual_of_wedgeAt` (`L1Claim.lean`), which discharges `_of_tail`'s
`det'` with it. -/
theorem det_ne_zero_of_unimod {u' vl : ℤ × ℤ} (hunimod : det u' vl = 1 ∨ det u' vl = -1) :
    det vl u' ≠ 0 := by
  rw [det_comm]
  rcases hunimod with h | h <;> omega

/-- **`ofWedge`'s three shape hypotheses on `u'`, paid at once** (integrator's item (2),
2026-09-19; path found by Rsweep).  From `Primitive vl` alone: a `u'` that is primitive,
completes `vl` to a unimodular pair, and is transverse to it.  Wiring only —
`Primitive.exists_dual` (`Defs/Config.lean:164`) gives `det vl u' = 1`, `det_comm`
(`Config.lean:47`) turns it into `hunimod`'s right branch, and the Bézout step of
`Primitive_of_det_eq_one` (`PeriodCount.lean:340`, not imported here — inlined) gives
`Primitive u'`.

⚠ **Scope.**  This holds only when `u'` is the producer's to choose — which is the case at
`exists_L1MaxBResidual`, whose conclusion binds `u'` existentially and whose binder list never
names `v_J`.  If a producer instead pins `u' := v_{ℓ_{ι-1}}` (the adjacent-edge direction of
Claim 4.6, `b3_colle2.txt:790-806`), then `det u' vl = ±1` becomes a geometric claim about two
consecutive edge directions of `𝒮` and is **false in general** (hand-read, Rsweep: `vl = (2,1)`,
`v_{ℓ_{ι-1}} = (-1,2)`, `det = 5`; Rsweep is turning that into a kernel counterexample).  Do not
cite this lemma for a pinned `u'`. -/
theorem exists_u'_unimod {vl : ℤ × ℤ} (hvl : Primitive vl) :
    ∃ u' : ℤ × ℤ, Primitive u' ∧ (det u' vl = 1 ∨ det u' vl = -1) ∧ det vl u' ≠ 0 := by
  obtain ⟨u', hu'⟩ := hvl.exists_dual
  refine ⟨u', ?_, Or.inr ?_, ?_⟩
  · -- `Primitive_of_det_eq_one` (`PeriodCount.lean:340`) is not in this file's import closure;
    -- its three-line body is inlined (Bézout coefficients `vl.2, -vl.1`, as in
    -- `L1Claim.exists_L1MaxBResidual_of_wedgeAt`).
    show IsCoprime u'.1 u'.2
    refine ⟨-vl.2, vl.1, ?_⟩
    simp only [det] at hu'
    linear_combination hu'
  · rw [det_comm, hu']
  · rw [hu']; exact one_ne_zero

/-! ### §14 / §20 record (2026-09-19 14:xx): the concrete-family assembly lives in `L1Claim.lean`

Deleted 2026-09-19: `MaxBResidual.exists_of_wedge`, `exists_L1MaxBResidual_of_pieces`,
`exists_L1MaxBResidual_of_normal` — covered verbatim by
`L1Claim.exists_L1MaxBResidual_of_wedgeAt`; integrator's ruling and reasons in `LANDING.md`
（三条已由 `L1Claim.exists_L1MaxBResidual_of_wedgeAt` 逐字覆盖，2026-09-19 删除，理由见
`LANDING.md`）.  §14 keeps the *judgment* here; the duplicate *code* goes.

Between 13:00 and 13:22 this file gained four declarations — `det_ne_zero_of_unimod` (kept,
above: it acquired a consumer), `MaxBResidual.exists_of_wedge`, `exists_L1MaxBResidual_of_pieces`,
`exists_L1MaxBResidual_of_normal` — composing a concrete `RegionFamily` (`ofWedge` or
`ofHalfPlanes`) with `exists_greatest_periodOn`, `tail` and `ofFive`.  In the same hour lane
Cclaim landed `L1Claim.exists_L1MaxBResidual_of_tail` / `_of_family` / `_of_cover`
(`L1Claim.lean`), which do the same composition for an **abstract** `F` and conclude
`exists_L1MaxBResidual`'s existential **byte for byte**.  Two assembly points, neither with a
consumer (`CLAUDE.md`: "账本变重而 sorry 不动").

Integrator's rule (14:xx): the one whose conclusion is the leaf's verbatim is the entry; the
other becomes its body or goes.  `L1Claim.exists_L1MaxBResidual_of_tail` is the entry, and
Cclaim's `exists_L1MaxBResidual_of_wedgeAt` (14:32) is `exists_of_wedge`'s content re-done as
its body — with `F := ofWedgeAt` (base at index `k`), `hB` from `EnvOf`, `hu'` from
`hunimod`, `c0` from `hinf`.  So the three composites were deleted here on 2026-09-19 together
with the imports `L1RegionBuild` and `L1Select` they alone used (§20: this file is upstream of
`L1Claim`, so keeping them here would have been the orphan).  The `ofHalfPlanes` pair went
with them: that route was closed by the integrator the same afternoon (AnfpL's
`inner2 w' u = 0` against `ofHalfPlanes`'s `0 < dot m u`;
`L1Prim.not_halfPlaneGE_subset_of_det_ne_zero` blocks changing `m`), so `ofWedge`/`ofWedgeAt`
is the only live `RegionFamily` producer.

Two interface findings from the deleted text that still bind, stated once so they are not
re-derived:

1. **`u := vl`, not `u' := vl`.**  `ofFive` derives `base0` from Lemma 2.3 through
   `two_le_min_faces_of_nel hgen hℓ_nel hℓ_neg hu hdet_ℓ`, whose `hdet_ℓ : dot ℓ u = 0` puts the
   *period* direction along `ℓ` (`b3_colle2.txt:806`, `h ∥ ℓ`).  Any producer that sets
   `u' := vl` has no `base0`.
2. **Quantifier order.**  `line`/`straddle` mention `u' τ v ε`, so `u'` (hence `F`) is chosen
   before they are stated; the leaf binds `c` inside the outer `∃`, so `hinf` is asked at one
   `c` picked by the caller.

⚠ On `not_straddle_four` (`L1Region.lean:460`), which the deleted docstrings cited as "no
level-`0` form of `straddle` exists": that theorem is about `L1Region.witness` (the
`ofCut Set.univ (1,0) wlev` family over `wx`), **not** about `chainFull` and not about
`ofHalfPlanes`.  What it proves is only that `Straddle` does not transport `0 → N` along an
arbitrary family, i.e. that `straddle` must be stated at the maximal index — which `_of_tail`
already does.  It says nothing about whether `hstraddle` at `N` is satisfiable on `ofWedge`;
that is Cconv's/Afill's open question (`L1CoverWedge.lean`). -/

end Nivat.ColleReg.L1Data

section Receipts
/-! Standing `#print axioms` receipts and the arity measurement.  Deletable as a block:
everything between `section Receipts` and `end Receipts` is measurement, not content. -/

#check @Nivat.ColleReg.L1Data.ofPieces
#check @Nivat.ColleReg.L1Data.Residual.mk
#check @Nivat.ColleReg.L1Data.ofCutPieces
#check @Nivat.ColleReg.L1Data.DerivedResidual.mk
#check @Nivat.ColleReg.L1Data.translate
#check @Nivat.ColleReg.L1Data.exists_window_eq
#check @Nivat.ColleReg.L1Data.MaxBResidual.mk
#check @Nivat.ColleReg.L1Data.maxB_wide
#check @Nivat.ColleReg.L1Data.maxB_wide_levels

#print axioms Nivat.ColleReg.L1Data.ofPieces
#print axioms Nivat.ColleReg.L1Data.nonempty_of_pieces
#print axioms Nivat.ColleReg.L1Data.nonempty_of_leafBinders
#print axioms Nivat.ColleReg.L1Data.ofResidual
#print axioms Nivat.ColleReg.L1Data.ofCutPieces
#print axioms Nivat.ColleReg.L1Data.conclusion_of_residual
#print axioms Nivat.ColleReg.L1Data.isGeneratingSet_image_zero
#print axioms Nivat.ColleReg.L1Data.straddle_not_transported
#print axioms Nivat.ColleReg.L1Data.derived_conjuncts
#print axioms Nivat.ColleReg.L1Data.isGeneratingSet_image
#print axioms Nivat.ColleReg.L1Data.translate
#print axioms Nivat.ColleReg.L1Data.exists_window_eq
#print axioms Nivat.ColleReg.L1Data.weakBase_of_strong
#print axioms Nivat.ColleReg.L1Data.weakBase_of_weakBase_zero
#print axioms Nivat.ColleReg.L1Data.ofDerived
#print axioms Nivat.ColleReg.L1Data.nonempty_of_derived
#print axioms Nivat.ColleReg.L1Data.card_side
#print axioms Nivat.ColleReg.L1Data.lt_not_iff
#print axioms Nivat.ColleReg.L1Data.ofMaxB
#print axioms Nivat.ColleReg.L1Data.nonempty_of_maxB
#print axioms Nivat.ColleReg.L1Data.maxBResidual_of_derived
#print axioms Nivat.ColleReg.L1Data.sub_zsmul_mem_of_runs
#print axioms Nivat.ColleReg.L1Data.maxB_wide
#print axioms Nivat.ColleReg.L1Data.mem_of_parallelogram
#print axioms Nivat.ColleReg.L1Data.maxB_levels_core
#print axioms Nivat.ColleReg.L1Data.exists_parallelogram
#print axioms Nivat.ColleReg.L1Data.maxB_wide_levels
#print axioms Nivat.ColleReg.L1Data.toReal_mem_ONED_of_mem_nonExpansiveLine
#print axioms Nivat.ColleReg.L1Data.two_le_min_faces_of_ONED
#print axioms Nivat.ColleReg.L1Data.two_le_min_faces_of_nel
#print axioms Nivat.ColleReg.L1Data.maxB_nonempty_of_two_le_faces
#print axioms Nivat.ColleReg.L1Data.det_smul_eq_det_smul_add_det_smul
#print axioms Nivat.ColleReg.L1Data.exists_translate_subset_of_isRegion
#print axioms Nivat.ColleReg.L1Data.exists_zsmul_ne_zero_of_parallel
#print axioms Nivat.ColleReg.L1Data.MaxBResidual.base0_of_faces
#print axioms Nivat.ColleReg.L1Data.MaxBResidual.ofFive
#check @Nivat.ColleReg.L1Data.MaxBResidual.ofFive
#print axioms Nivat.ColleReg.L1Data.det_eq_dot_perp
#print axioms Nivat.ColleReg.L1Data.maxB_block
#check @Nivat.ColleReg.L1DataMax.mk
#check @Nivat.ColleReg.L1DataMax.nonempty_of_maxB
#print axioms Nivat.ColleReg.L1DataMax.ofMaxB
#print axioms Nivat.ColleReg.L1DataMax.nonempty_of_maxB
#print axioms Nivat.ColleReg.L1DataMax.toConclusion
#check @Nivat.ColleReg.L1Data.MaxBResidual.ofTail
#print axioms Nivat.L1Region.RegionFamily.tail
#print axioms Nivat.L1Region.RegionFamily.straddle_tail
#print axioms Nivat.ColleReg.L1Data.line_of_seed
#print axioms Nivat.ColleReg.L1Data.MaxBResidual.ofTail
#print axioms Nivat.ColleReg.L1Data.det_ne_zero_of_unimod
#print axioms Nivat.ColleReg.L1Data.exists_u'_unimod

end Receipts
