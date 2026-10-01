/-
Copyright (c) 2026 Nivat formalisation project. All rights reserved.
-/
import Nivat.External.Colle.L1StraddleFeed
import Nivat.External.Colle.WedgeBundleBuild
import Nivat.External.Colle.DecompData
import Nivat.External.Colle.L1Cut
import Nivat.External.Colle.L1Claim
import Nivat.External.Colle.HalfPlaneShells
import Nivat.PeriodCount

/-!
# `WedgeResidualR.ofCorner`'s nine non-`hbase`/`hcorner` binders: producer census

Lane Lstrad's file (exclusive), superseding the `hN₀`/`hN₀1` verdict scattered across
`L1StraddleFeed.lean`'s docstring with an explicit, standalone answer, plus the priority-2/3
follow-ups team-lead asked for.

`WedgeResidualR.ofCorner` (`WedgeBundleBuild.lean:50`) binders, excluding `hbase` (`OPEN.md #13`,
Hflat) and `hcorner` (Hvert):

```
hb₀ hunimod hc k N₀ hN₀ hN₀1 hmin hattain Sφ hSφ a ha
```

## Verdict table

| binder | verdict | producer |
|---|---|---|
| `hb₀ : b₀ ∈ B` | **data, not an obligation** | `B`/`b₀` are existentials of the final goal; any inhabited `B` works, content lives in `hbase`/`hcorner` holding for *that* `B` |
| `hunimod : det u' vl = ±1` | **has a producer** | `Primitive.exists_dual` + `Primitive_of_det_eq_one` (`PeriodCount.lean:340`), cited, closed in `LEAF-L1.md` |
| `hc : 0 < c` | **coupled to `hbase`, not independent** | shares `c` with `hbase` (`L1Claim.lean:191-200`, "one owner, two binders") |
| `k : ℕ` | **free data** | `k := 0` always admissible |
| `N₀ hN₀ hN₀1` | **has a producer, landed below** | `exists_N₀` (= `L1StraddleFeed.exists_hN₀`, re-exported) |
| `hmin hattain` | **has a producer, landed below, no coupling with `N₀`** | `exists_N₀_hmin_hattain` composes `exists_hN₀` then `L1Line0.exists_shift_min_level` at the resulting level |
| `Sφ hSφ` | **has a producer, landed below** | `Nivat.Colle35.DecompDataZ.isGeneratingSet` (`DecompData.lean:195`), `Sφ := d.Sphi` |
| `a ha` | **not independently free** | paired with `hcorner`'s choice of corner point, Hvert's territory; named as an explicit gap below so a future lane can be dispatched against exactly this shape |

## Priority 1, answered explicitly: `N₀ hN₀ hN₀1` has a producer, is not a second `hbase`

Team-lead's exact question: *"全树有没有『链最终失周期』这条？没有的话它是不是另一条隐藏的
`hbase` 级欠账？"* — **yes, the tree has it, non-vacuously**: `Nivat.ColleReg.hinf_of_ge`
(`L1CoverWedge.lean:237`, Afill) proves `¬ PeriodOn (T e ξ) (wedgeFull B vl u') (c • vl)` from
`hξ d hb₀ hunimod (c • vl ≠ 0)` via Proposition 2.12 (`union_not_of_halfPlane_cover`) — this is
real mathematical content (a covering argument), not a statement that is vacuous merely because
it carries an `hξ : IsMinimalCounterexample ξ` binder (that binder is the leaf's standing
hypothesis throughout, satisfied at every call site this route is used from — it is *not* one of
the over-constrained `hξ`-shaped propositions §24/§25 warn about, which fail because of an
*additional* unsatisfiable conjunct, not because of `hξ` alone). Combined with
`Nivat.L1Region.exists_greatest_periodOn` and a reindexed exhaustiveness fact, this is exactly
`L1StraddleFeed.exists_hN₀`, already landed and kernel-clean
(`[propext, Classical.choice, Quot.sound]`). **Reverse check (§24, no unsatisfiability
refutation found)**: grepped the tree for `not_*`/`¬∀` statements over `chainFull`/`wedgeFull`
periodicity (`HbaseBridge.not_cutBand_subset_wedgeFull_iff`, `L1CoverWedge.not_wedgeFull_univ_singleton`,
`L1CoverWedge.not_mem_chainFull_iff`, `L3Band.not_chainFull_succ_subset_genClosure`) — none of
them says the `hN₀`/`hN₀1` pair is unsatisfiable; they are about a different predicate (the cut
band escaping a region, or single-point membership), not about periodicity persisting on the
whole chain forever. **Verdict: `N₀ hN₀ hN₀1` is not a binder at all once `hbase` is granted —
it is free, with no new mathematical content and no new debt.**

## Priority 2, answered explicitly: `hmin`/`hattain` do not couple against `N₀`

`Nivat.L1Line0.exists_shift_min_level` (`L1Line0.lean:294`) is universally quantified over its
target level `L : ℤ` — it is *not* tied to any particular `N₀` in its statement. So the two
existentials compose **sequentially, not simultaneously**: first run `exists_hN₀` to fix `N₀`
(this does not need `v` at all — `hinf_of_ge`/`exists_greatest_periodOn` never mention a
translation), *then* instantiate `exists_shift_min_level`'s `L` at the resulting
`expLevel u' vl b₀ (k + N₀) - 1` to get `v`. `v` depends on `N₀` (expected: the target level it
must hit is `N₀`-dependent), but `N₀`'s production never depends on `v`, so there is **no
circularity and no coupling obstruction** — `exists_N₀_hmin_hattain` below performs exactly this
composition and is kernel-clean.

## Priority 3

`hunimod`, `hb₀`, `hc`, `Sφ hSφ`, `a ha`: see verdict table; `hunimod` and `Sφ hSφ` get landed
wiring lemmas below (`primitive_of_hunimod` as the key step for `hunimod`'s freedom and for
`exists_shift_min_level`'s own `Primitive u'` hypothesis; `Nivat.Colle35.DecompDataZ.isGeneratingSet`
is cited directly, no new lemma needed). `hb₀`/`hc`/`k` are data/coupling calls already argued
in the table, no further code needed. `a ha` gets a named gap `Prop` (`CornerPointGap`) instead
of a `sorry`, per hard rule 4.

## 2026-09-19, team-lead redispatch: signature-layer shear inventory

Team-lead's independent replay confirmed both priority verdicts above, then landed a new fact
that refutes `CornerPointGap` as stated (fixed `u'`): Hvert's
`HbaseVertexSeed.not_hcorner_of_zonoF_two_generators` exhibits a real `m = 2` zonotope `Sφ` with
no corner point at any *fixed* `u'`. `CornerPointGap` below is **kept, not deleted** (§14) with
its docstring updated to record the refutation; the true unconditional fact is
`L1StraddleWedge.exists_corner_shear` (`L1StraddleWedge.lean:424`), which finds a corner point
only after shearing `u' ↦ u' − K•vl`.

**New task**: classify every occurrence of `u'` across `ofCorner`'s binders by how it behaves
under this shear, complementing Hvert's geometric work on `chainFull`/`wedgeFull`/`det`:

| binder | shear behaviour | evidence |
|---|---|---|
| `hb₀ hc k Sφ hSφ a` | `u'`-free | no occurrence of `u'` at all |
| `hunimod` | **invariant** | `L1StraddleWedge.det_shear` (`:384`): `det (u'-K•vl) vl = det u' vl` |
| `hmin hattain hcorner` | **covariant, closed** | `dot_expNormal_shear`/`uCoord_shear` (`:388,393`) give the *exact* correction term `K * uCoord u' vl 0 w`; `exists_corner_shear` already discharges the `hcorner`-shaped instance unconditionally |
| `hbase N₀ hN₀ hN₀1` | **semantics change, no closing lemma in the tree** | `chainFull` itself is not shear-invariant (`mem_chainFull_shear_iff` below pins the exact tilted membership condition); no `chainFull_shear` equality/transport lemma exists anywhere in the tree (grep confirms) |

`mem_chainFull_shear_iff` and `ChainFullShearTransport` below make this precise instead of
leaving it as prose. `exists_N₀_hmin_hattain_shear` re-instantiates this file's own
`exists_N₀_hmin_hattain` at the sheared `u' - K•vl` to show it needs **zero new code** — the
only missing ingredient is `ChainFullShearTransport`, supplied as an explicit hypothesis, not
derived (no `sorry`).

## 2026-09-19, team-lead redirect: `ChainFullShearTransport` off the critical path, new targets
`hline`/`hstraddle`

Team-lead's §20 recheck found `WedgeResidualR.ofSweep` (`L1Claim.lean:1064`) has **no `hbase`
binder at all** — `hbase` is discharged internally via
`HbaseBridge.hbase_at_of_sweep_of_isGeneratingSet`, so nothing needs to be transported along a
shear to reach `exists_wedgeResidualR`'s goal. `ChainFullShearTransport` is kept per §14 (honest
name for a real, still-open gap noticed along the way) but is **not invested in further**.

## 2026-09-20: `ChainFullShearTransport` refuted

Hvert proved `Nivat.ChainFullShear.not_chainFullShearTransport` (team-lead verified
`[propext, Classical.choice, Quot.sound]`, no `sorryAx`). Counterexample at `K=1`, `k=0`, `c=1`
— **minimal shear, bottom layer fails**. So `exists_N₀_hmin_hattain_shear` (`:274`) cannot derive
its `hbase'` by transporting the original `hbase` along the shear; `hbase` at the sheared point
must be proved directly at that point (if true). Status per §14: previously judged "off critical
path, not invested in further" (2026-09-19); now **refuted** (2026-09-20), counterexample
on record, original judgment and refutation both retained.

The live residual targets are `ofSweep`'s `hline`/`hstraddle` (`L1Claim.lean:1075-1088`), and
team-lead asked two attribution questions before any new proof:

### Sub-question 1: does this file's `N₀`/`hmin`/`hattain` match `hline`/`hstraddle`'s `∀ N`?

**Yes, exactly — both already have producers on the tree, confirmed by direct citation, not
guessed from names (§23):**

* `hline` ⟵ `Nivat.L1Line0.hline_of_placement` (`L1Line0.lean:327`): binders
  `hb₀ hunimod hc hN₀ hN₀1 hmin`. Internally it calls `Nivat.L1Prim.maximal_index_unique` to
  collapse the target's `∀ N` to the *unique* `N₀` with `hN₀ : PeriodOn … (k+N₀) …` and
  `hN₀1 : ¬ PeriodOn … (k+(N₀+1)) …` — this is the literal confirmation that `hline`'s `N`
  and this file's `N₀` are the same index, not merely same-shaped. All six inputs are exactly
  `exists_N₀_hmin_hattain`'s output plus `hc : 0 < c` (this file's `hc0 : c ≠ 0` must be
  strengthened to `0 < c` at the call site — a sign choice, not new content, `hbase`'s own `c`
  is already fixed by whichever route produces it).
* `hstraddle` ⟵ `Nivat.L1StraddleWedge.hstraddle_of_corner` (`L1StraddleWedge.lean:310`):
  binders `hunimod hc.le hN₀ hN₀1 hmin hattain hSφ ha hcorner`. The first six are exactly
  `exists_N₀_hmin_hattain`'s output; `hSφ` is `exists_Sφ` above (`Sφ := d.Sphi`). **`a ha
  hcorner` are not available from `ofSweep`'s own binders at all** — `ofSweep` has no `Sφ`/`a`
  binder, only `S v ha : a ∈ S hconvS`. Wiring `hstraddle` all the way through therefore needs
  whichever lane closes the corner-point gap (`CornerPointGapShear` above / Hvert's territory)
  to hand its witness *through* this file's data, not the reverse. `wiring_hline` below is
  fully closed; `wiring_hstraddle` is closed *given* a corner witness as an explicit hypothesis
  (that hypothesis is `hcorner` itself — not a new gap beyond the one already tracked).

### Sub-question 2: can `ε`/`v` be chosen to make `hline` vacuous (empty `derivedQ`)?

**No, judged and landed below as kernel-checked lemmas, not merely prose.**
`cutNormal ε u'` does not depend on `S₁` or any translation. Translating `S` by `v` shifts every
`inner2 n` value by the same additive constant `inner2 n v` (`inner2_add`), so it shifts
`levelMax` by that same constant (`levelMax_image_add`) and therefore does not change *which*
points of `S` tie for the top level: `derivedQ ε u' (S.image (·+v))` is literally
`(derivedQ ε u' S).image (·+v)` (`derivedQ_image_add`), so its nonemptiness is `v`-independent
(`derivedQ_image_nonempty_iff`, via `Finset.image_nonempty`). Flipping `ε` only flips the sign
of `cutNormal` (`cutNormal_false_eq_neg_true`), and a linear functional is constant on `S` iff
its negation is (`derivedQ_eq_empty_iff_true_false`), so `ε` cannot rescue emptiness either.
**Conclusion**: `derivedQ ε u' (S.image (·+v)) = ∅` iff `inner2 (cutNormal ε u') `-equivalently
`inner2 (cutNormal (¬ε) u')`- is *constant* on `S` — an intrinsic collinearity property of `S`
along `u'`, invariant under the two free choices `ε`/`v` the assembler has. `hline`/`hstraddle`
are genuine obligations whenever `S` is not `u'`-collinear; `ε`/`v` give no escape hatch.
-/

set_option autoImplicit false

namespace Nivat.ColleReg

open Nivat Nivat.LE2 Nivat.Colle Nivat.Colle41 Nivat.L1Line0 Nivat.L1StraddleWedge
open Nivat.ColleReg.L1Data

variable {u' vl : ℤ × ℤ}

/-- **`hunimod` gives `Primitive u'`.**  Needed as `exists_shift_min_level`'s own `hu'`
hypothesis, so this is the one piece of wiring `hmin`/`hattain`'s producer needs beyond
`hunimod` itself. `Primitive_of_det_eq_one` (`PeriodCount.lean:340`) handles the `= 1` branch
directly; the `= -1` branch is reduced to it via `det u' (-vl) = 1`. -/
theorem primitive_of_hunimod (hunimod : det u' vl = 1 ∨ det u' vl = -1) : Primitive u' := by
  rcases hunimod with h | h
  · exact Primitive_of_det_eq_one h
  · refine Primitive_of_det_eq_one (v := u') (u := -vl) ?_
    simp only [det, Prod.fst_neg, Prod.snd_neg] at h ⊢
    linarith

/-- **Priority 1, standalone: `N₀ hN₀ hN₀1` has a producer.**  Re-exported from
`L1StraddleFeed.exists_hN₀` under this file's own name, so the answer to team-lead's priority-1
question is landed here rather than only implied by an import. -/
theorem exists_N₀ {ξ : Config ℤ} {e : ℤ × ℤ} (hξ : IsMinimalCounterexample ξ)
    (d : Nivat.Colle35.DecompDataZ ξ)
    {B : Set (ℤ × ℤ)} {b₀ : ℤ × ℤ} {c : ℤ} (hb₀ : b₀ ∈ B)
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) (hc0 : c ≠ 0) (hvl_prim : Primitive vl)
    (k : ℕ) (hbase : PeriodOn (T e ξ) (chainFull B vl u' b₀ k) (c • vl)) :
    ∃ N₀ : ℕ, PeriodOn (T e ξ) (chainFull B vl u' b₀ (k + N₀)) (c • vl) ∧
      ¬ PeriodOn (T e ξ) (chainFull B vl u' b₀ (k + (N₀ + 1))) (c • vl) :=
  Nivat.ColleReg.exists_hN₀ hξ d hb₀ hunimod hc0 hvl_prim k hbase

/-- **Priority 2, standalone: `N₀ hN₀ hN₀1` and `hmin hattain` compose without coupling.**
Produces all five of `ofCorner`'s `N₀ hN₀ hN₀1 hmin hattain` obligations (plus the witness `v`)
from data `ofCorner` already needs elsewhere (`hξ d hb₀ hunimod hc0 hvl_prim k hbase`) plus one
extra hypothesis `exists_shift_min_level` itself asks for, `S.Nonempty`. -/
theorem exists_N₀_hmin_hattain {ξ : Config ℤ} {e : ℤ × ℤ} (hξ : IsMinimalCounterexample ξ)
    (d : Nivat.Colle35.DecompDataZ ξ)
    {B : Set (ℤ × ℤ)} {b₀ : ℤ × ℤ} {c : ℤ} (hb₀ : b₀ ∈ B)
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) (hc0 : c ≠ 0) (hvl_prim : Primitive vl)
    (k : ℕ) (hbase : PeriodOn (T e ξ) (chainFull B vl u' b₀ k) (c • vl))
    {S : Finset (ℤ × ℤ)} (hS : S.Nonempty) :
    ∃ (N₀ : ℕ) (v : ℤ × ℤ),
      PeriodOn (T e ξ) (chainFull B vl u' b₀ (k + N₀)) (c • vl) ∧
      ¬ PeriodOn (T e ξ) (chainFull B vl u' b₀ (k + (N₀ + 1))) (c • vl) ∧
      (∀ s ∈ S.image (· + v), expLevel u' vl b₀ (k + N₀) - 1 ≤ dot (expNormal u' vl) s) ∧
      (∃ s ∈ S.image (· + v), dot (expNormal u' vl) s = expLevel u' vl b₀ (k + N₀) - 1) := by
  obtain ⟨N₀, hN₀, hN₀1⟩ := exists_N₀ hξ d hb₀ hunimod hc0 hvl_prim k hbase
  have hu' : Primitive u' := primitive_of_hunimod hunimod
  obtain ⟨v, hmin, hattain⟩ :=
    exists_shift_min_level hu' hunimod hS (expLevel u' vl b₀ (k + N₀) - 1)
  exact ⟨N₀, v, hN₀, hN₀1, hmin, hattain⟩

/-- **Priority 3, `Sφ hSφ`: has a producer**, `d.Sphi` from `DecompDataZ`. -/
theorem exists_Sφ {ξ : Config ℤ} (d : Nivat.Colle35.DecompDataZ ξ) :
    IsGeneratingSet ξ d.toDecompData.Sphi :=
  Nivat.Colle35.DecompDataZ.isGeneratingSet d

/-- **`a ha`'s gap at a *fixed* `u'`, named (not `sorry`) — ⚠ REFUTED, kept per §14.**
Hvert's `HbaseVertexSeed.not_hcorner_of_zonoF_two_generators` exhibits a real `m = 2` zonotope
`Sφ` with no corner point at any fixed `u'`, so this `Prop` is **false in general** and must not
be dispatched against as stated.  The true, unconditional fact lives at a *sheared* `u'`:
`CornerPointGapShear` below, closed by `L1StraddleWedge.exists_corner_shear`. -/
def CornerPointGap (ξ : Config ℤ) (Sφ : Finset (ℤ × ℤ)) (u' vl : ℤ × ℤ) : Prop :=
  ∃ a ∈ Sφ, ∀ b ∈ Sφ, 0 ≤ dot (expNormal u' vl) (b - a) ∧ 0 ≤ uCoord u' vl a b

/-- **The shear-corrected `CornerPointGap`, unconditionally true.** -/
def CornerPointGapShear (Sφ : Finset (ℤ × ℤ)) (u' vl : ℤ × ℤ) : Prop :=
  ∃ K : ℤ, ∃ a ∈ Sφ, ∀ b ∈ Sφ,
    0 ≤ dot (expNormal (u' - K • vl) vl) (b - a) ∧ 0 ≤ uCoord (u' - K • vl) vl a b

theorem cornerPointGapShear_holds {Sφ : Finset (ℤ × ℤ)} (hSφ : Sφ.Nonempty) :
    CornerPointGapShear Sφ u' vl :=
  exists_corner_shear hSφ

/-! ## Shear inventory for `hbase`/`N₀`/`hmin`/`hattain` -/

/-- **The exact tilt of `chainFull` under a shear.**  `chainFull` is *not* shear-invariant: at
`u' − K•vl` the cutting half-plane tilts by `K * uCoord u' vl b₀ z`, a genuinely `z`-dependent
correction (not a reindexing of `n`).  This is the concrete content behind the `hbase N₀ hN₀
hN₀1` row of the shear table above. -/
theorem mem_chainFull_shear_iff (B : Set (ℤ × ℤ)) (vl u' b₀ : ℤ × ℤ) (K : ℤ) (n : ℕ)
    (z : ℤ × ℤ) :
    z ∈ chainFull B vl (u' - K • vl) b₀ n ↔
      z ∈ wedgeFull B vl u' ∧
        expLevel u' vl b₀ n - K * uCoord u' vl b₀ z ≤ dot (expNormal u' vl) z := by
  have hz' : dot (expNormal (u' - K • vl) vl) z = dot (expNormal u' vl) z + K * uCoord u' vl 0 z :=
    dot_expNormal_shear K z
  have hb' : dot (expNormal (u' - K • vl) vl) b₀ =
      dot (expNormal u' vl) b₀ + K * uCoord u' vl 0 b₀ :=
    dot_expNormal_shear K b₀
  have huc : uCoord u' vl b₀ z = uCoord u' vl 0 z - uCoord u' vl 0 b₀ := uCoord_eq_sub b₀ z
  simp only [chainFull, Nivat.L1Region.cut, Set.mem_inter_iff, wedgeFull_shear, halfPlaneGE,
    Set.mem_setOf_eq, expLevel, hz', hb']
  constructor
  · rintro ⟨hz, hle⟩
    exact ⟨hz, by rw [huc]; linarith⟩
  · rintro ⟨hz, hle⟩
    exact ⟨hz, by rw [huc] at hle; linarith⟩

/-- **The genuine shear gap for `hbase`/`N₀`/`hmin`/`hattain` — named, not assumed.**  Whether
`PeriodOn` on the flat `chainFull B vl u' b₀ k` transports to the tilted
`chainFull B vl (u' - K•vl) b₀ k` (`mem_chainFull_shear_iff` pins the exact tilt).  No producer
for this anywhere in the tree (grepped for `chainFull_shear`, no hits beyond this file). -/
def ChainFullShearTransport (ξ : Config ℤ) (e : ℤ × ℤ) (B : Set (ℤ × ℤ)) (vl u' b₀ : ℤ × ℤ)
    (c : ℤ) (K : ℤ) (k : ℕ) : Prop :=
  PeriodOn (T e ξ) (chainFull B vl u' b₀ k) (c • vl) →
    PeriodOn (T e ξ) (chainFull B vl (u' - K • vl) b₀ k) (c • vl)

/-- **`exists_N₀_hmin_hattain` needs zero new code at a sheared `u'`.**  Re-instantiating this
file's own `exists_N₀_hmin_hattain` at `u' - K•vl` (legal since `u'` was always a free variable,
and `hunimod` survives the shear via `det_shear`) shows the *only* missing ingredient is
`hbase` at the sheared point — supplied here as an explicit hypothesis, exactly the shape
`ChainFullShearTransport` names. -/
theorem exists_N₀_hmin_hattain_shear {ξ : Config ℤ} {e : ℤ × ℤ} (hξ : IsMinimalCounterexample ξ)
    (d : Nivat.Colle35.DecompDataZ ξ)
    {B : Set (ℤ × ℤ)} {b₀ : ℤ × ℤ} {c : ℤ} (hb₀ : b₀ ∈ B)
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) (hc0 : c ≠ 0) (hvl_prim : Primitive vl)
    (K : ℤ) (k : ℕ)
    (hbase' : PeriodOn (T e ξ) (chainFull B vl (u' - K • vl) b₀ k) (c • vl))
    {S : Finset (ℤ × ℤ)} (hS : S.Nonempty) :
    ∃ (N₀ : ℕ) (v : ℤ × ℤ),
      PeriodOn (T e ξ) (chainFull B vl (u' - K • vl) b₀ (k + N₀)) (c • vl) ∧
      ¬ PeriodOn (T e ξ) (chainFull B vl (u' - K • vl) b₀ (k + (N₀ + 1))) (c • vl) ∧
      (∀ s ∈ S.image (· + v), expLevel (u' - K • vl) vl b₀ (k + N₀) - 1 ≤
        dot (expNormal (u' - K • vl) vl) s) ∧
      (∃ s ∈ S.image (· + v),
        dot (expNormal (u' - K • vl) vl) s = expLevel (u' - K • vl) vl b₀ (k + N₀) - 1) := by
  have hunimod' : det (u' - K • vl) vl = 1 ∨ det (u' - K • vl) vl = -1 := by
    rwa [det_shear]
  exact exists_N₀_hmin_hattain hξ d hb₀ hunimod' hc0 hvl_prim k hbase' hS

/-! ## `hline`/`hstraddle` for `ofSweep`: wiring + the `ε`/`v`-triviality question -/

/-- **`hline`, fully wired for `ofSweep`.**  Needs `0 < c` (a sign strengthening of `hc0`, not
new content) on top of `exists_N₀_hmin_hattain`'s own output. -/
theorem wiring_hline {ξ : Config ℤ} {e : ℤ × ℤ} (hξ : IsMinimalCounterexample ξ)
    (d : Nivat.Colle35.DecompDataZ ξ)
    {B : Set (ℤ × ℤ)} {b₀ : ℤ × ℤ} {c : ℤ} (hb₀ : b₀ ∈ B)
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) (hc : 0 < c) (hvl_prim : Primitive vl)
    (k : ℕ) (hbase : PeriodOn (T e ξ) (chainFull B vl u' b₀ k) (c • vl))
    {S : Finset (ℤ × ℤ)} (hS : S.Nonempty) :
    ∃ (N₀ : ℕ) (v : ℤ × ℤ), ∀ N : ℕ,
      PeriodOn (T e ξ) (chainFull B vl u' b₀ (k + N)) (c • vl) →
      ¬ PeriodOn (T e ξ) (chainFull B vl u' b₀ (k + (N + 1))) (c • vl) →
      ∃ τ : ℤ, ∀ z ∈ derivedQ (εOf u' vl) u' (S.image (· + v)),
        τ • u' + z ∈ chainFull B vl u' b₀ (k + N) ∧
        τ • u' + z + c • vl ∈ chainFull B vl u' b₀ (k + N) := by
  obtain ⟨N₀, v, hN₀, hN₀1, hmin, _hattain⟩ :=
    exists_N₀_hmin_hattain hξ d hb₀ hunimod hc.ne' hvl_prim k hbase hS
  exact ⟨N₀, v, hline_of_placement hb₀ hunimod hc hN₀ hN₀1 hmin⟩

/-- **`hstraddle`, wired modulo the corner-point gap.**  Takes `exists_N₀_hmin_hattain`'s output
shape (`hN₀ hN₀1 hmin hattain`, at whatever `S₁` — instantiate at `S.image (·+v)` for `ofSweep`)
as hypotheses directly, rather than re-deriving them, so no `Classical.choose` bookkeeping is
needed to match witnesses across two separate calls. `Sφ hSφ` come from `exists_Sφ` above;
`a ha hcorner` are the one piece `ofSweep`'s own binders never supply (no `Sφ`/`a` binder exists
on `ofSweep` at all) — stated here as an explicit hypothesis, exactly `hcorner`'s shape, not a
new gap on top of the one `CornerPointGapShear`/Hvert's lane already tracks. -/
theorem wiring_hstraddle {ξ : Config ℤ} {e : ℤ × ℤ}
    {B : Set (ℤ × ℤ)} {b₀ : ℤ × ℤ} {c : ℤ}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) (hc : 0 ≤ c) {k N₀ : ℕ}
    (hN₀ : PeriodOn (T e ξ) (chainFull B vl u' b₀ (k + N₀)) (c • vl))
    (hN₀1 : ¬ PeriodOn (T e ξ) (chainFull B vl u' b₀ (k + (N₀ + 1))) (c • vl))
    {S₁ : Finset (ℤ × ℤ)}
    (hmin : ∀ s ∈ S₁, expLevel u' vl b₀ (k + N₀) - 1 ≤ dot (expNormal u' vl) s)
    (hattain : ∃ s ∈ S₁, dot (expNormal u' vl) s = expLevel u' vl b₀ (k + N₀) - 1)
    (d : Nivat.Colle35.DecompDataZ ξ)
    {a : ℤ × ℤ} (ha : a ∈ d.toDecompData.Sphi)
    (hcorner : ∀ b ∈ d.toDecompData.Sphi,
      0 ≤ dot (expNormal u' vl) (b - a) ∧ 0 ≤ uCoord u' vl a b) :
    ∀ N : ℕ, PeriodOn (T e ξ) (chainFull B vl u' b₀ (k + N)) (c • vl) →
      ¬ PeriodOn (T e ξ) (chainFull B vl u' b₀ (k + (N + 1))) (c • vl) →
      ∀ τ : ℤ,
        (∀ z ∈ derivedQ (εOf u' vl) u' S₁,
          τ • u' + z ∈ chainFull B vl u' b₀ (k + N) ∧
          τ • u' + z + c • vl ∈ chainFull B vl u' b₀ (k + N)) →
        Nivat.L1Region.Straddle (T e ξ) (chainFull B vl u' b₀ (k + N))
          (chainFull B vl u' b₀ (k + (N + 1))) S₁ (derivedQ (εOf u' vl) u' S₁) vl u' c τ :=
  hstraddle_of_corner hunimod hc hN₀ hN₀1 hmin hattain (exists_Sφ d) ha hcorner

/-! ## `ε`/`v` cannot trivialise `hline`: `derivedQ` under translation and sign flip -/

/-- `levelMax` shifts by the constant `inner2 n v` under translating the finset by `v`. -/
theorem levelMax_image_add (n : ℝ × ℝ) (v : ℤ × ℤ) {S : Finset (ℤ × ℤ)} (hS : S.Nonempty) :
    levelMax (S.image (· + v)) n = levelMax S n + inner2 n v := by
  have hS' : (S.image (· + v)).Nonempty := hS.image _
  unfold levelMax
  rw [dif_pos hS, dif_pos hS']
  apply le_antisymm
  · apply Finset.sup'_le
    intro z hz
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hz
    rw [inner2_add]
    have := Finset.le_sup' (fun z => inner2 n z) hs
    linarith
  · have hle : ∀ s ∈ S, inner2 n s + inner2 n v ≤
        (S.image (· + v)).sup' hS' (fun z => inner2 n z) := by
      intro s hs
      have h1 : inner2 n (s + v) ≤ (S.image (· + v)).sup' hS' (fun z => inner2 n z) :=
        Finset.le_sup' (fun z => inner2 n z) (Finset.mem_image_of_mem (· + v) hs)
      rwa [inner2_add] at h1
    have h2 : S.sup' hS (fun z => inner2 n z) ≤
        (S.image (· + v)).sup' hS' (fun z => inner2 n z) - inner2 n v := by
      apply Finset.sup'_le
      intro s hs
      have := hle s hs
      linarith
    linarith

/-- **`derivedQ` commutes with translation of the underlying finset.**  Direct evidence that `v`
gives the assembler no freedom to make `derivedQ` (hence `hline`'s premise set) collapse. -/
theorem derivedQ_image_add (ε : Bool) (u' v : ℤ × ℤ) (S : Finset (ℤ × ℤ)) :
    derivedQ ε u' (S.image (· + v)) = (derivedQ ε u' S).image (· + v) := by
  ext z
  simp only [derivedQ, Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨⟨s, hs, rfl⟩, hlt⟩
    refine ⟨s, ⟨hs, ?_⟩, rfl⟩
    rw [levelMax_image_add (cutNormal ε u') v ⟨s, hs⟩, inner2_add] at hlt
    linarith
  · rintro ⟨s, ⟨hs, hlt⟩, rfl⟩
    refine ⟨⟨s, hs, rfl⟩, ?_⟩
    rw [levelMax_image_add (cutNormal ε u') v ⟨s, hs⟩, inner2_add]
    linarith

/-- **Corollary: `derivedQ`'s nonemptiness does not depend on `v`.**  Answers half of
sub-question 2: no choice of translation `v` can make `hline`'s premise set vacuous unless it
already was. -/
theorem derivedQ_image_nonempty_iff (ε : Bool) (u' v : ℤ × ℤ) (S : Finset (ℤ × ℤ)) :
    (derivedQ ε u' (S.image (· + v))).Nonempty ↔ (derivedQ ε u' S).Nonempty := by
  rw [derivedQ_image_add]
  exact Finset.image_nonempty

/-- `derivedQ ε u' S₁` is empty exactly when every point of `S₁` sits at the top level. -/
theorem derivedQ_eq_empty_iff (ε : Bool) {S₁ : Finset (ℤ × ℤ)} (hne : S₁.Nonempty) :
    derivedQ ε u' S₁ = ∅ ↔ ∀ z ∈ S₁, inner2 (cutNormal ε u') z = levelMax S₁ (cutNormal ε u') := by
  constructor
  · intro h z hz
    by_contra hne'
    have hmem : z ∈ derivedQ ε u' S₁ :=
      Finset.mem_filter.mpr ⟨hz, lt_of_le_of_ne (le_levelMax hne z hz) hne'⟩
    rw [h] at hmem
    exact absurd hmem (Finset.notMem_empty z)
  · intro h
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro z hz
    unfold derivedQ at hz
    rw [Finset.mem_filter] at hz
    rw [h z hz.1] at hz
    exact lt_irrefl _ hz.2

/-- Same emptiness condition, restated as "constant on `S₁`" (drops the reference to the
specific value `levelMax`). -/
theorem derivedQ_eq_empty_iff_const (ε : Bool) {S₁ : Finset (ℤ × ℤ)} (hne : S₁.Nonempty) :
    derivedQ ε u' S₁ = ∅ ↔
      ∀ z ∈ S₁, ∀ w ∈ S₁, inner2 (cutNormal ε u') z = inner2 (cutNormal ε u') w := by
  rw [derivedQ_eq_empty_iff ε hne]
  constructor
  · intro h z hz w hw
    rw [h z hz, h w hw]
  · intro h z hz
    obtain ⟨z₀, hz₀, hz₀eq⟩ := Finset.exists_mem_eq_sup' hne (fun w => inner2 (cutNormal ε u') w)
    unfold levelMax
    rw [dif_pos hne, hz₀eq]
    exact h z hz z₀ hz₀

theorem inner2_neg_left (n : ℝ × ℝ) (z : ℤ × ℤ) : inner2 (-n) z = -inner2 n z := by
  simp only [inner2, Prod.fst_neg, Prod.snd_neg]; ring

theorem cutNormal_false_eq_neg_true (u' : ℤ × ℤ) : cutNormal false u' = - cutNormal true u' := by
  simp only [cutNormal]
  ext <;> simp [toReal]

/-- **The two choices of `ε` agree on whether `derivedQ` is empty.**  Answers the other half of
sub-question 2: flipping the cut side gives the assembler no escape from a genuinely
non-collinear `S`. -/
theorem derivedQ_eq_empty_iff_true_false {S₁ : Finset (ℤ × ℤ)} (hne : S₁.Nonempty) :
    derivedQ true u' S₁ = ∅ ↔ derivedQ false u' S₁ = ∅ := by
  rw [derivedQ_eq_empty_iff_const true hne, derivedQ_eq_empty_iff_const false hne]
  constructor
  · intro h z hz w hw
    rw [cutNormal_false_eq_neg_true, inner2_neg_left, inner2_neg_left]
    exact congrArg Neg.neg (h z hz w hw)
  · intro h z hz w hw
    have h' := h z hz w hw
    rw [cutNormal_false_eq_neg_true, inner2_neg_left, inner2_neg_left] at h'
    exact neg_inj.mp h'

/-! ## §9  Team-lead's newest redirect (2026-09-19 22:xx): holes 2/3 of `L1SweepBridge.holes`

`Nivat.L1SweepBridge.wedgeResidualR_of_case1_holes` (already on the main tree, `EXIT=0`) takes a
`holes` binder producing exactly two obligations at the `b₀` it hands out: `hwin` (Hflat's) and a
single big conjunct team-lead's message split in prose into "洞 2 = `hline`" (an inner premise,
`∃ τ, ∀ z ∈ derivedQ …, …`) and "洞 3 = `hcover`" (the outer `overlap ⊆ genClosure` implication
that *consumes* that premise as a hypothesis, not as something it must reprove).

**Hole 2 needs no new work.**  Its shape, read at a single `N`, is exactly `wiring_hline`'s (§ this
file, `hξ`-free at the caller's chosen `k`) conclusion — `L1SweepBridge.lean:136-137` already
uses `wiring_hline` for precisely this content (feeding `WedgeResidualR.ofSweep`'s `hline` field).
Nothing below re-derives it; §9 only targets hole 3.

**Hole 3, reduced.**  `Nivat.L1StraddleWedge.cover_line` (`L1StraddleWedge.lean:157`) is *already*
an unconditional proof of hole 3's exact conclusion shape, modulo three hypotheses: `hunimod`,
`0 ≤ c`, and — the one with content — `hcorner` on the window that ends up as `genClosure`'s first
argument (here `S`, not a translate: team-lead's hole 3 conclusion is `genClosure S a …`, so the
corner is asked of `S` itself, at whatever `a` the caller's `hSgen` hands out via
`Colle.exists_vertex_of_generating`).  `wiring_hcover_of_corner` below is that reduction, stated
against team-lead's exact binder order (including the unused `hN hN1 hτ` binders, kept so the
statement is literally the type asked for, not a paraphrase). -/

open Nivat.MaxEnv Nivat.L1StraddleMax in
/-- **Hole 3 = `hcover`, reduced to `hcorner` on `S` at the caller's `u'`.**  `hmin`/`hattain` are
Cprobe's placement fact for `S.image (· + v)` at level `expLevel u' vl b₀ N - 1` — the same data
`wiring_hline`'s own `exists_N₀_hmin_hattain` produces, just needed here again as an explicit
hypothesis because `cover_line` consumes it directly (via `dot_eq_of_not_mem_derivedQ`) rather
than through `wiring_hline`'s packaging.  The `hN hN1 hτ` binders are literally unused — hole 3's
stated shape carries them (to match `straddle_of_cover`'s call site in `L1SweepBridge.lean`) but
`cover_line`'s proof of the cover does not need the maximal-index fact, only the corner and the
line-level of `g`. -/
theorem wiring_hcover_of_corner {ξ : Config ℤ} {u : ℤ × ℤ}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) {B : Set (ℤ × ℤ)} {b₀ : ℤ × ℤ} {c : ℤ}
    (hc : 0 ≤ c) {S : Finset (ℤ × ℤ)} {a v : ℤ × ℤ}
    (hcorner : ∀ b ∈ S, 0 ≤ dot (expNormal u' vl) (b - a) ∧ 0 ≤ uCoord u' vl a b)
    {N : ℕ}
    (hmin : ∀ s ∈ S.image (· + v), expLevel u' vl b₀ N - 1 ≤ dot (expNormal u' vl) s)
    (hattain : ∃ s ∈ S.image (· + v), dot (expNormal u' vl) s = expLevel u' vl b₀ N - 1) :
    PeriodOn (T u ξ) (chainFull B vl u' b₀ N) (c • vl) →
    ¬ PeriodOn (T u ξ) (chainFull B vl u' b₀ (N + 1)) (c • vl) →
    ∀ τ : ℤ,
      (∀ z ∈ derivedQ (εOf u' vl) u' (S.image (· + v)),
        τ • u' + z ∈ chainFull B vl u' b₀ N ∧
        τ • u' + z + c • vl ∈ chainFull B vl u' b₀ N) →
      ∀ g ∈ S.image (· + v), g ∉ derivedQ (εOf u' vl) u' (S.image (· + v)) →
        ∀ t₀ : ℤ, τ ≤ t₀ →
          overlap (chainFull B vl u' b₀ (N + 1)) (c • vl) ⊆
            genClosure S a
              (overlap (chainFull B vl u' b₀ N) (c • vl) ∪ ray g u' t₀) := by
  intro _hN _hN1 τ _hτ g hg hgQ t₀ ht₀
  exact cover_line hunimod hc hcorner (dot_eq_of_not_mem_derivedQ hunimod hmin hattain hg hgQ) t₀

/-!
⚠ **Honest limitation (do not silently plug into `L1SweepBridge`).**  `wiring_hcover_of_corner`
still needs `hcorner` on `S` at the caller's *fixed* `u'` — exactly the corner-vertex question
`OPEN.md #13` already tracks as **refuted for general finite sets**
(`Nivat.HbaseVertexSeed.not_hcorner_of_zonoF_two_generators`) and **open** for the specific `a`
that `Colle.exists_vertex_of_generating` (`HalfPlaneShells.lean:55`) actually hands out — that
`a` is the maximiser of `N * z.1 + z.2` for a spread-dependent `N`, a lexicographic-type
functional with no known relation to `(expNormal u' vl, uCoord u' vl a ·)` for a `u'` chosen only
to be unimodular with `vl`.  This file does **not** close that gap: `wiring_hcover_of_corner` is
the exact reduction of hole 3 to it, not a new proof that the reduction is dischargeable.  If
`hcorner` turns out false for the real `(S, a, u')` triple leaf L1 produces, hole 3 needs a
different route than `cover_line` (e.g. shearing `u'`, as `exists_corner_shear` does, at the cost
of reopening the shear-compatibility question `OPEN.md #13` already flags).
-/

section AxiomReceipts9

#print axioms wiring_hcover_of_corner

end AxiomReceipts9

/-! ## Task #1 (team-lead, UNFREEZE 2026-09-19): `exists_vertex_of_generating`, any direction

Team-lead's diagnosis: `Colle.exists_vertex_of_generating` (`HalfPlaneShells.lean:55`) picks its
vertex `a` as the maximizer of `g z := N*z.1+z.2`, a lexicographic-type functional along the
**standard basis** with no known relation to the `det vl`-extreme point `hcorner`
(`wiring_hcover_of_corner` above) actually needs.  `N` there exists purely to force `z.1`'s
contribution to dominate `z.2`'s (a spread bound), so the choice of "primary coordinate = `z.1`,
secondary = `z.2`" is arbitrary — nothing in the proof needs the standard basis.

This section generalizes it: primary coordinate `dot w z`, secondary `dot (perp w) z`.  The two
are an integral basis of the dual whenever `w ≠ 0` (`det w (perp w) = w.1^2+w.2^2 > 0`,
`sq_add_sq_pos_of_ne_zero`), which is exactly what the injectivity/strict-maximizer argument
below needs in place of the original's literal `z.1`/`z.2`. -/

open Nivat.Colle in
/-- **`exists_vertex_of_generating`, generalized to an arbitrary nonzero direction `w`.**  `a` is
chosen to *minimize* `dot w` over `S` (ties, if any, broken by maximizing `dot (perp w)`) — this
is the mirror generalization of the original's maximizer, with `w := -e₂ = (0,-1)`-style sign
recovering the exact original when `w := (N,1)`-degenerate cases are unwound; stated as a minimum
because that is the shape `hcorner`'s shear-invariant conjunct (`0 ≤ uCoord u' vl a b`, i.e.
`a` minimizes `det vl ·` up to sign) actually wants.  Proof is `exists_vertex_of_generating`'s
argument verbatim with `z.1 ↦ -(dot w z)`, `z.2 ↦ dot (perp w) z`: the original's algebra never
used more about `z.1`/`z.2` than that they are integers with `w.1*z.1+w.2*z.2`-style bilinearity,
which `dot`/`perp` supply for an arbitrary nonzero `w` via `det w (perp w) ≠ 0`
(`sq_add_sq_pos_of_ne_zero`) playing the role the original's literal coordinate axes played. -/
theorem exists_vertex_of_generating_dir {A : Type*} {ξ : Config A} {S : Finset (ℤ × ℤ)}
    {w : ℤ × ℤ} (hw : w ≠ 0) (hgen : IsGeneratingSet ξ S) :
    ∃ a ∈ S, (∀ b ∈ S, dot w a ≤ dot w b) ∧ LatticeConvex (S.erase a) ∧ GeneratesAt ξ S a := by
  obtain ⟨hne, hconv, hvert⟩ := hgen
  classical
  have ⟨a, ha, hmin, ha_conv⟩ :
      ∃ a ∈ S, (∀ b ∈ S, dot w a ≤ dot w b) ∧ LatticeConvex (S.erase a) := by
    have hyne : (S.image (fun z => dot (perp w) z)).Nonempty := hne.image _
    set D : ℤ := (S.image (fun z => dot (perp w) z)).sup' hyne id -
        (S.image (fun z => dot (perp w) z)).inf' hyne id with hD
    set N : ℤ := D + 1 with hN
    obtain ⟨z0, hz0⟩ := id hne
    have hDnn : (0 : ℤ) ≤ D := by
      have h1 := Finset.inf'_le (s := S.image (fun z => dot (perp w) z)) id
        (Finset.mem_image_of_mem _ hz0)
      have h2 := Finset.le_sup' (s := S.image (fun z => dot (perp w) z)) id
        (Finset.mem_image_of_mem _ hz0)
      rw [hD]; linarith
    -- `g z := N * (-(dot w z)) + dot (perp w) z`: maximizing `g` primarily minimizes `dot w`,
    -- ties broken by maximizing `dot (perp w)`.
    set g : ℤ × ℤ → ℤ := fun z => N * (-(dot w z)) + dot (perp w) z with hgdef
    have hginj : ∀ z ∈ S, ∀ y ∈ S, g z = g y → z = y := by
      intro z hz y hy heq
      by_contra hne'
      have heq' : N * (dot w y - dot w z) = dot (perp w) y - dot (perp w) z := by
        have hlin : N * (-(dot w z)) - N * (-(dot w y)) = dot (perp w) y - dot (perp w) z := by
          simp only [hgdef] at heq; linarith
        linear_combination hlin
      have hz2ge : (S.image (fun v => dot (perp w) v)).inf' hyne id ≤ dot (perp w) z :=
        Finset.inf'_le id (Finset.mem_image_of_mem _ hz)
      have hz2le : dot (perp w) z ≤ (S.image (fun v => dot (perp w) v)).sup' hyne id :=
        Finset.le_sup' id (Finset.mem_image_of_mem (fun v => dot (perp w) v) hz)
      have hy2ge : (S.image (fun v => dot (perp w) v)).inf' hyne id ≤ dot (perp w) y :=
        Finset.inf'_le id (Finset.mem_image_of_mem _ hy)
      have hy2le : dot (perp w) y ≤ (S.image (fun v => dot (perp w) v)).sup' hyne id :=
        Finset.le_sup' id (Finset.mem_image_of_mem (fun v => dot (perp w) v) hy)
      have hbound : |dot (perp w) y - dot (perp w) z| ≤ D := by
        rw [abs_le]; rw [hD]; constructor <;> linarith
      rw [← heq'] at hbound
      by_cases hxeq : dot w z = dot w y
      · have hy0 : dot (perp w) y - dot (perp w) z = 0 := by rw [← heq', hxeq]; ring
        have hwz : dot w (z - y) = 0 := by rw [Nivat.LE2.dot_sub]; omega
        have hpz : dot (perp w) (z - y) = 0 := by rw [Nivat.LE2.dot_sub]; omega
        have e1 : w.1 * (z.1 - y.1) + w.2 * (z.2 - y.2) = 0 := by
          simpa only [Nivat.LE2.dot, Prod.fst_sub, Prod.snd_sub] using hwz
        have e2 : (-w.2) * (z.1 - y.1) + w.1 * (z.2 - y.2) = 0 := by
          simpa only [Nivat.LE2.dot, perp, Prod.fst_sub, Prod.snd_sub] using hpz
        have hpos := sq_add_sq_pos_of_ne_zero hw
        have hdx : (w.1 ^ 2 + w.2 ^ 2) * (z.1 - y.1) = 0 := by
          linear_combination w.1 * e1 - w.2 * e2
        have hdy : (w.1 ^ 2 + w.2 ^ 2) * (z.2 - y.2) = 0 := by
          linear_combination w.2 * e1 + w.1 * e2
        have hdx0 : z.1 - y.1 = 0 := by
          rcases mul_eq_zero.mp hdx with h | h
          · exact absurd h (ne_of_gt hpos)
          · exact h
        have hdy0 : z.2 - y.2 = 0 := by
          rcases mul_eq_zero.mp hdy with h | h
          · exact absurd h (ne_of_gt hpos)
          · exact h
        exact hne' (Prod.ext (by omega) (by omega))
      · have hd1 : (1 : ℤ) ≤ |dot w z - dot w y| :=
          Int.one_le_abs (sub_ne_zero.mpr hxeq)
        have hNpos : (0 : ℤ) < N := by omega
        have hNle : N ≤ |N * (dot w y - dot w z)| := by
          rw [abs_mul, abs_of_pos hNpos, abs_sub_comm (dot w y) (dot w z)]
          calc N = N * 1 := (mul_one N).symm
          _ ≤ N * |dot w z - dot w y| := mul_le_mul_of_nonneg_left hd1 (le_of_lt hNpos)
        omega
    obtain ⟨a, ha, hmax⟩ := Finset.exists_max_image S g hne
    refine ⟨a, ha, ?_, ?_⟩
    · intro b hb
      by_contra hcon
      push_neg at hcon
      have hdiff : (1 : ℤ) ≤ dot w a - dot w b := by omega
      have hNnn : (0 : ℤ) ≤ N := by omega
      have hNle : N * 1 ≤ N * (dot w a - dot w b) := mul_le_mul_of_nonneg_left hdiff hNnn
      have hexpand : N * (dot w a - dot w b) = N * dot w a - N * dot w b := by ring
      have hb2ge : (S.image (fun v => dot (perp w) v)).inf' hyne id ≤ dot (perp w) b :=
        Finset.inf'_le id (Finset.mem_image_of_mem _ hb)
      have ha2le : dot (perp w) a ≤ (S.image (fun v => dot (perp w) v)).sup' hyne id :=
        Finset.le_sup' id (Finset.mem_image_of_mem (fun v => dot (perp w) v) ha)
      have hbound : dot (perp w) a - dot (perp w) b ≤ D := by rw [hD]; linarith
      have hgba : g b ≤ g a := hmax b hb
      simp only [hgdef] at hgba
      rw [mul_one] at hNle
      nlinarith [hgba, hNle, hexpand, hbound, hN]
    · have hstrict : ∀ b ∈ S.erase a, (g b : ℝ) < (g a : ℝ) := by
        intro b hb
        obtain ⟨hba, hbS⟩ := Finset.mem_erase.mp hb
        have h1 : g b ≤ g a := hmax b hbS
        have h2 : g b ≠ g a := fun h => hba (hginj b hbS a ha h)
        exact_mod_cast lt_of_le_of_ne h1 h2
      set G : (ℝ × ℝ) →ₗ[ℝ] ℝ :=
          ((-(N : ℝ) * (w.1 : ℝ) - (w.2 : ℝ)) : ℝ) • LinearMap.fst ℝ ℝ ℝ +
          ((-(N : ℝ) * (w.2 : ℝ) + (w.1 : ℝ)) : ℝ) • LinearMap.snd ℝ ℝ ℝ with hGdef
      have hGtoReal : ∀ z : ℤ × ℤ, G (toReal z) = (g z : ℝ) := by
        intro z
        simp only [hGdef, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.fst_apply,
          LinearMap.snd_apply, smul_eq_mul, toReal, hgdef, Nivat.LE2.dot, perp]
        push_cast; ring
      have haux : toReal a ∉ Conv (S.erase a) := by
        intro hmem
        have himg : Conv (S.erase a) =
            convexHull ℝ (((S.erase a).image toReal : Finset (ℝ × ℝ)) : Set (ℝ × ℝ)) := by
          rw [Conv, Finset.coe_image]
        rw [himg] at hmem
        obtain ⟨v, hv0, hv1, hvsum⟩ := Finset.mem_convexHull'.mp hmem
        have hv1' : ∑ b ∈ S.erase a, v (toReal b) = 1 := by
          rwa [Finset.sum_image (fun x _ y _ h => toReal_injective h)] at hv1
        have hvsum' : ∑ b ∈ S.erase a, v (toReal b) • toReal b = toReal a := by
          rwa [Finset.sum_image (fun x _ y _ h => toReal_injective h)] at hvsum
        have hGsum : ∑ b ∈ S.erase a, v (toReal b) * G (toReal b) = G (toReal a) := by
          rw [← hvsum', map_sum]
          refine Finset.sum_congr rfl (fun b _ => ?_)
          rw [map_smul, smul_eq_mul]
        have hle : ∀ b ∈ S.erase a, v (toReal b) * G (toReal b) ≤ v (toReal b) * G (toReal a) := by
          intro b hb
          have hGb : G (toReal b) ≤ G (toReal a) := by
            rw [hGtoReal, hGtoReal]; exact le_of_lt (hstrict b hb)
          exact mul_le_mul_of_nonneg_left hGb (hv0 (toReal b) (Finset.mem_image_of_mem _ hb))
        have hex : ∃ b ∈ S.erase a, 0 < v (toReal b) := by
          by_contra hcon
          push_neg at hcon
          have hall0 : ∀ b ∈ S.erase a, v (toReal b) = 0 := fun b hb =>
            le_antisymm (hcon b hb) (hv0 (toReal b) (Finset.mem_image_of_mem _ hb))
          rw [Finset.sum_congr rfl hall0] at hv1'
          simp at hv1'
        have hlt : ∃ b ∈ S.erase a, v (toReal b) * G (toReal b) < v (toReal b) * G (toReal a) := by
          obtain ⟨b0, hb0, hb0pos⟩ := hex
          refine ⟨b0, hb0, ?_⟩
          have hGb0 : G (toReal b0) < G (toReal a) := by
            rw [hGtoReal, hGtoReal]; exact hstrict b0 hb0
          exact mul_lt_mul_of_pos_left hGb0 hb0pos
        have hcontra : G (toReal a) < G (toReal a) := by
          calc G (toReal a) = ∑ b ∈ S.erase a, v (toReal b) * G (toReal b) := hGsum.symm
          _ < ∑ b ∈ S.erase a, v (toReal b) * G (toReal a) := Finset.sum_lt_sum hle hlt
          _ = (∑ b ∈ S.erase a, v (toReal b)) * G (toReal a) := by rw [Finset.sum_mul]
          _ = G (toReal a) := by rw [hv1']; ring
        exact lt_irrefl _ hcontra
      intro z hz
      have hzS : z ∈ S :=
        hconv z (convexHull_mono (Set.image_mono (S.erase_subset a)) hz)
      have hzne : z ≠ a := by
        intro h; subst h; exact haux hz
      exact Finset.mem_erase.mpr ⟨hzne, hzS⟩
  have ha_gen : GeneratesAt ξ S a := hvert a ha ha_conv
  exact ⟨a, ha, hmin, ha_conv, ha_gen⟩

/-- **Team-lead's decoupled reading (`straddle_of_cover`'s `a'` needs no `LatticeConvex`).**
`straddle_of_cover` (`L1StraddleMax.lean:129`) only consumes `hgen : GeneratesAt ξ S a'` — its
conclusion `Straddle …` carries no `a'`, and `LatticeConvex (S.erase a')` is not one of its
binders.  So the `hcorner`-route vertex `a'` only needs this weaker corollary, dropping the
`LatticeConvex` conjunct of `exists_vertex_of_generating_dir` entirely (a free projection, not
new proof work — the hard part of the original theorem was always the convex-hull separation
producing `LatticeConvex`, which this corollary simply discards). -/
theorem exists_vertex_of_generating_dir' {A : Type*} {ξ : Config A} {S : Finset (ℤ × ℤ)}
    {w : ℤ × ℤ} (hw : w ≠ 0) (hgen : IsGeneratingSet ξ S) :
    ∃ a ∈ S, (∀ b ∈ S, dot w a ≤ dot w b) ∧ GeneratesAt ξ S a := by
  obtain ⟨a, ha, hmin, _hconv, hgenAt⟩ := exists_vertex_of_generating_dir hw hgen
  exact ⟨a, ha, hmin, hgenAt⟩

section AxiomReceipts10

#print axioms exists_vertex_of_generating_dir

end AxiomReceipts10

section AxiomReceipts11

#print axioms exists_vertex_of_generating_dir'

end AxiomReceipts11

/-! ## Hole 2, closing it: identifying `uCoord` with `dot (perp vl) ·`

`uCoord u' vl a b = -(det u' vl) * det vl (b - a)` (`L1Line0.lean:93`) and
`dot (perp vl) z = det vl z` (`dot_perp`, `Claim47Core.lean:47`) — no sign ambiguity, so
`hcorner`'s second conjunct `0 ≤ uCoord u' vl a b` is literally `0 ≤ dot w₁ (b - a)` for
`w₁ := (-(det u' vl)) • perp vl`, i.e. `a` minimising `dot w₁ ·` over `S`. -/

/-- **`uCoord` as a `dot` against a scaled `perp vl`.**  Pure unfolding: `dot_smul` peels the
scalar, `dot_perp` turns `dot (perp vl) ·` into `det vl ·`, matching `uCoord`'s definition on the
nose. -/
theorem uCoord_eq_dot_perp (u' vl a b : ℤ × ℤ) :
    Nivat.L1Line0.uCoord u' vl a b = dot ((-(det u' vl)) • perp vl) (b - a) := by
  rw [dot_smul, dot_perp, Nivat.L1Line0.uCoord]

section AxiomReceipts12

#print axioms uCoord_eq_dot_perp

end AxiomReceipts12

/-! ## Hole 2, closed: a single vertex that generates and is corner after a shear

Team-lead's sub-tasks 2/3 (`lexMin_of_large_M`, `exists_corner_shear_at`) turn out unnecessary:
`L1StraddleWedge.exists_corner_shear` (`:424`) *already* produces the lexicographically-minimal
`a` (via its own two-step `exists_min_image` / filter-ties / `exists_min_image`, not the
large-`M` single-functional trick) — so no new lex-min machinery is needed. What was missing is
only the observation that `L1StraddleWedge.generatesAt_of_corner` (`:268`) is stated at a
*generic* `u'` (an implicit `variable`), so it applies just as well at the sheared direction
`u' - K • vl` (with `hunimod` transported through `det_shear`) as at the original one. Composing
the two closes hole 2 outright, with no intermediate lemma. -/

/-- **Hole 2, closed.**  `IsGeneratingSet ξ S` alone (no fixed corner, no `hcorner` hypothesis)
produces a shear `K` and a vertex `a ∈ S` that simultaneously generates `ξ` and is a corner of
`S` at the sheared direction `u' - K • vl`. -/
theorem exists_generatesAt_corner_shear {A : Type*} {ξ : Config A} {S : Finset (ℤ × ℤ)}
    {u' vl : ℤ × ℤ} (hSgen : IsGeneratingSet ξ S)
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) :
    ∃ K : ℤ, ∃ a ∈ S, GeneratesAt ξ S a ∧
      (∀ b ∈ S, 0 ≤ dot (expNormal (u' - K • vl) vl) (b - a) ∧
        0 ≤ Nivat.L1Line0.uCoord (u' - K • vl) vl a b) := by
  obtain ⟨K, a, ha, hcorner⟩ := Nivat.L1StraddleWedge.exists_corner_shear (u' := u') hSgen.1
  have hunimod' : det (u' - K • vl) vl = 1 ∨ det (u' - K • vl) vl = -1 := by
    rw [Nivat.L1StraddleWedge.det_shear]; exact hunimod
  exact ⟨K, a, ha, Nivat.L1StraddleWedge.generatesAt_of_corner hunimod' hSgen ha hcorner, hcorner⟩

section AxiomReceipts13

#print axioms exists_generatesAt_corner_shear

end AxiomReceipts13

/-! ## Hole 2, closed a second way: the shear itself is the linear combination

Team-lead's correction: the lex-min detour is unnecessary.  Write `w₁ := (-(det u' vl)) • perp vl`
(so `dot w₁ z = uCoord u' vl 0 z` by `uCoord_eq_dot_perp` at `a := 0`) and
`w := expNormal u' vl + K • w₁`.  `dot_expNormal_shear` says `dot w z` is **identically**
`dot (expNormal (u' - K•vl) vl) z` for *every* `K`, not just large `K` — so the shear direction
`u' - K•vl` was always secretly the same linear functional as `expNormal u' vl + K•w₁`. -/

/-- **`dot w₁ z = uCoord u' vl 0 z`**, the `a := 0` case of `uCoord_eq_dot_perp`. -/
theorem dot_wOne_eq_uCoord (u' vl z : ℤ × ℤ) :
    dot ((-(det u' vl)) • perp vl) z = Nivat.L1Line0.uCoord u' vl 0 z := by
  have h := uCoord_eq_dot_perp u' vl 0 z
  simpa using h.symm

/-- **Hole 2, closed via the direct linear-combination route.**  Same conclusion shape as
`exists_generatesAt_corner_shear`, reached without the lex-min construction: `K` only needs to
exceed the spread of `dot (expNormal u' vl)` over `S`, and the first `hcorner` conjunct is free
for *any* `K` since `dot w z = dot (expNormal (u' - K•vl) vl) z` identically. -/
theorem exists_corner_shear_of_generating {A : Type*} {ξ : Config A} {S : Finset (ℤ × ℤ)}
    {u' vl : ℤ × ℤ} (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hgen : IsGeneratingSet ξ S) :
    ∃ K : ℤ, ∃ a' ∈ S, GeneratesAt ξ S a' ∧
      ∀ b ∈ S, 0 ≤ dot (expNormal (u' - K • vl) vl) (b - a') ∧
               0 ≤ Nivat.L1Line0.uCoord (u' - K • vl) vl a' b := by
  classical
  have hSne : S.Nonempty := hgen.1
  obtain ⟨z0, hz0⟩ := id hSne
  set w₁ : ℤ × ℤ := (-(det u' vl)) • perp vl with hw₁def
  set K : ℤ := S.sup' hSne (fun z => dot (expNormal u' vl) z) -
      S.inf' hSne (fun z => dot (expNormal u' vl) z) + 1 with hKdef
  have hinfsup : S.inf' hSne (fun z => dot (expNormal u' vl) z) ≤
      S.sup' hSne (fun z => dot (expNormal u' vl) z) :=
    le_trans (Finset.inf'_le (fun z => dot (expNormal u' vl) z) hz0)
      (Finset.le_sup' (fun z => dot (expNormal u' vl) z) hz0)
  have hK1 : 1 ≤ K := by rw [hKdef]; omega
  set w : ℤ × ℤ := expNormal u' vl + K • w₁ with hwdef
  have hwz : ∀ z : ℤ × ℤ, dot w z = dot (expNormal u' vl) z + K * dot w₁ z := by
    intro z
    simp only [hwdef, Nivat.LE2.dot, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul]
    ring
  have hdotw1vl : dot w₁ vl = 0 := by
    rw [hw₁def, dot_smul, dot_perp, det_self]; ring
  have hdotwvl : dot w vl = 1 := by
    rw [hwz, hdotw1vl, mul_zero, add_zero, dot_expNormal_vl hunimod]
  have hwne : w ≠ 0 := by
    intro h
    rw [h] at hdotwvl
    simp [dot] at hdotwvl
  obtain ⟨a', ha', hmin, hgenAt⟩ := exists_vertex_of_generating_dir' hwne hgen
  refine ⟨K, a', ha', hgenAt, fun b hb => ?_⟩
  have hshear : dot (expNormal (u' - K • vl) vl) (b - a') = dot w (b - a') := by
    rw [Nivat.L1StraddleWedge.dot_expNormal_shear, hwz, ← dot_wOne_eq_uCoord]
  have hminba : 0 ≤ dot w (b - a') := by
    have h := hmin b hb
    rw [dot_sub]; omega
  refine ⟨by rw [hshear]; exact hminba, ?_⟩
  rw [Nivat.L1StraddleWedge.uCoord_shear, uCoord_eq_dot_perp, ← hw₁def]
  by_contra hneg
  push_neg at hneg
  have hle1 : dot w₁ (b - a') ≤ -1 := by omega
  have hbound : dot (expNormal u' vl) (b - a') ≤ K - 1 := by
    have hb1 := Finset.le_sup' (fun z => dot (expNormal u' vl) z) hb
    have ha1 := Finset.inf'_le (fun z => dot (expNormal u' vl) z) ha'
    rw [dot_sub, hKdef]
    omega
  have heq := hwz (b - a')
  have hprod : K * dot w₁ (b - a') ≤ -K := by
    have h2 : K * dot w₁ (b - a') ≤ K * (-1) :=
      mul_le_mul_of_nonneg_left hle1 (by omega)
    linarith
  linarith [heq, hprod, hbound, hminba]

section AxiomReceipts14

#print axioms dot_wOne_eq_uCoord
#print axioms exists_corner_shear_of_generating

end AxiomReceipts14

/-! ## §16  Attack on `L1SweepBridge.HwinHoleE`'s inner `hwin ∧ hK` obligation

`L1SweepBridge.HwinHoleE ξ S vl` (as currently landed, no `Sphi`/`EnvOf` guard — see that
file's docstring at `:588-606` for the singleton-`B` discussion) asks, after `a`/`B`/`u`/`c`/`K`
are supplied, for `b₀ ∈ B` and a *free* `enum : ℕ → ℕ → ℤ × ℤ` making both

* `hwin` : every `z ∈ S.erase a` translated by `enum i j - a` lands in
  `halfStrip B vl ∪ (rows < i) ∪ (row i, cols < j)`, and
* `hK`   : `chainFull B vl (u' - K•vl) b₀ 0 ⊆ halfStrip B vl ∪ (all rows)`

hold simultaneously.  The theorem below shows this pair is **unsatisfiable** for the singleton
witness `B = {b₀}`, independently of `S`/`a`/`enum`, *provided* `S.erase a` contains a point
generating a genuinely escaping direction from `a` (i.e. `a + u'' + vl` for the sheared
direction `u'' := u' - K•vl`).  The mechanism: the orbit `p k := b₀ + (k+1)•vl + (k+1)•u''`
lies in `chainFull {b₀} vl u'' b₀ 0` for every `k` (by `dot_expNormal_u'`/`dot_expNormal_vl`)
but never in `halfStrip {b₀} vl` (since `u''` is not a multiple of `vl`, `det u'' vl ≠ 0`); so
by `hK`, `p 0` sits at some `enum i₀ j₀`; by `hwin` applied there to the generator point,
`p 1` must sit at a **strictly lex-earlier** index; iterating forever descends the lexicographic
order on `ℕ × ℕ`, which is well-founded — contradiction, proved here by nested strong
induction rather than by invoking a `Prod.Lex` instance.

⚠ **2026-09-20 label (team-lead review): this `B = {a}` singleton is retired-signature
territory, same issue as `not_hwinHoleE_body` below.** The live `L1SweepBridge.HwinHoleZ`
(`L1SweepBridge.lean:848`) carries an extra premise `EnvOf (↑Sw) B`, and `EnvOf` forces
`E B = E Sw` exactly (`Enveloped.E_eq`, `LatticeEdges.lean:628`) — a singleton `B` has
`E B = ∅`, so `EnvOf ↑Sw {a}` forces `E Sw = ∅` too, i.e. `Sw` itself collinear
(`subsingleton_of_E_eq_empty` above). The lemma is still true and still used correctly as an
internal step of `not_hwinHoleE_body`'s *own* derivation (which supplies its own singleton `B`
and does not claim to satisfy `EnvOf`); it does **not** by itself refute `HwinHoleZ` at a
general `Sw`, only at `Sw`'s that happen to force `B` towards a singleton. -/

theorem false_of_hwin_hK_escaping_generator
    {u'' vl a : ℤ × ℤ} (hunimod : det u'' vl = 1 ∨ det u'' vl = -1)
    {S : Finset (ℤ × ℤ)} {z : ℤ × ℤ}
    (hz : z = a + u'' + vl) (hzS : z ∈ S.erase a)
    (enum : ℕ → ℕ → ℤ × ℤ)
    (hwin : ∀ i j : ℕ, ∀ w ∈ S.erase a,
      w + (enum i j - a) ∈
        halfStrip ({a} : Set (ℤ × ℤ)) vl ∪
          (⋃ i' ∈ {i' | i' < i}, Set.range (enum i')) ∪ (enum i '' {j' | j' < j}))
    (hK : chainFull ({a} : Set (ℤ × ℤ)) vl u'' a 0 ⊆
      halfStrip ({a} : Set (ℤ × ℤ)) vl ∪ (⋃ i, Set.range (enum i))) :
    False := by
  have hdet_ne : det u'' vl ≠ 0 := by rcases hunimod with h | h <;> omega
  set p : ℕ → ℤ × ℤ := fun k => a + ((k : ℤ) + 1) • vl + ((k : ℤ) + 1) • u'' with hp_def
  have hp_eq : ∀ k : ℕ, p k = a + ((k : ℤ) + 1) • vl + ((k : ℤ) + 1) • u'' := fun k => rfl
  have hp0 : p 0 = z := by
    rw [hp_eq, hz]
    push_cast
    module
  have hp_succ : ∀ k : ℕ, z + (p k - a) = p (k + 1) := by
    intro k
    rw [hz, hp_eq k, hp_eq (k + 1)]
    push_cast
    module
  have hp_wedge : ∀ k : ℕ, p k ∈ wedgeFull ({a} : Set (ℤ × ℤ)) vl u'' := by
    intro k
    refine ⟨a + ((k : ℤ) + 1) • vl, mem_fullSweep_iff.mpr ⟨a, rfl, (k : ℤ) + 1, rfl⟩,
      k + 1, ?_⟩
    rw [hp_eq]
    push_cast
    module
  have hp_level : ∀ k : ℕ,
      expLevel u'' vl a 0 ≤ dot (expNormal u'' vl) (p k) := by
    intro k
    have hnv : dot (expNormal u'' vl) vl = 1 := dot_expNormal_vl hunimod
    have hnu : dot (expNormal u'' vl) u'' = 0 := dot_expNormal_u'
    have hcomp : dot (expNormal u'' vl) (p k)
        = dot (expNormal u'' vl) a + ((k : ℤ) + 1) * dot (expNormal u'' vl) vl
          + ((k : ℤ) + 1) * dot (expNormal u'' vl) u'' := by
      rw [hp_eq, dot_add, dot_add, dot_smul_right, dot_smul_right]
    have hlev : expLevel u'' vl a 0 = dot (expNormal u'' vl) a - (0 : ℤ) := rfl
    rw [hlev, hcomp, hnv, hnu]
    have hk0 : (0 : ℤ) ≤ (k : ℤ) := Int.natCast_nonneg k
    linarith
  have hp_mem_chainFull : ∀ k : ℕ,
      p k ∈ chainFull ({a} : Set (ℤ × ℤ)) vl u'' a 0 :=
    fun k => ⟨hp_wedge k, hp_level k⟩
  have hp_not_halfStrip : ∀ k : ℕ, p k ∉ halfStrip ({a} : Set (ℤ × ℤ)) vl := by
    intro k hmem
    obtain ⟨b, hb, t, ht⟩ := hmem
    simp only [Set.mem_singleton_iff] at hb
    rw [hb] at ht
    have hcomb : a + (t : ℤ) • vl = a + ((k : ℤ) + 1) • vl + ((k : ℤ) + 1) • u'' := by
      rw [← ht, hp_eq]
    have hfst := congrArg Prod.fst hcomb
    have hsnd := congrArg Prod.snd hcomb
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at hfst hsnd
    have hprod : ((k : ℤ) + 1) * det u'' vl = 0 := by
      have : ((k : ℤ) + 1) * (u''.1 * vl.2 - u''.2 * vl.1) = 0 := by
        linear_combination vl.1 * hsnd - vl.2 * hfst
      simpa [det] using this
    have hk1 : (k : ℤ) + 1 ≠ 0 := by positivity
    rcases mul_eq_zero.mp hprod with h | h
    · exact hk1 h
    · exact hdet_ne h
  have key : ∀ i j : ℕ, ∀ m : ℕ, enum i j = p m → False := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i IH =>
      intro j
      induction j using Nat.strong_induction_on with
      | _ j IH2 =>
        intro m hm
        have hcov := hwin i j z hzS
        rw [hm, hp_succ m] at hcov
        rcases hcov with (hcov | hcov) | hcov
        · exact hp_not_halfStrip (m + 1) hcov
        · simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_range] at hcov
          obtain ⟨i', hi'lt, j', hij'⟩ := hcov
          exact IH i' hi'lt j' (m + 1) hij'
        · obtain ⟨j', hj'lt, hij'⟩ := hcov
          exact IH2 j' hj'lt (m + 1) hij'
  have h0 := hK (hp_mem_chainFull 0)
  rcases h0 with h0 | h0
  · exact hp_not_halfStrip 0 h0
  · simp only [Set.mem_iUnion, Set.mem_range] at h0
    obtain ⟨i0, j0, hij0⟩ := h0
    exact key i0 j0 0 hij0

section AxiomReceipts15

#print axioms false_of_hwin_hK_escaping_generator

end AxiomReceipts15

/-! ## §17  `HwinHoleE` unfolded and refuted at an explicit witness

`HwinHoleE` (`L1SweepBridge.lean`, quoted verbatim in `tmp/enum_snippet.lean:75-87`) cannot be
named here: `L1SweepBridge.lean` **imports this file** (`L1SweepBridge.lean:10`), so importing it
back would be circular.  The theorem below states `HwinHoleE ξ₀ S₀ vl₀`'s body **verbatim,
unfolded**, for an explicit `ξ₀ S₀ vl₀`, and refutes it.  Assembling
`¬ HwinHoleE ξ₀ S₀ vl₀ := not_hwinHoleE_body` is a one-line `unfold HwinHoleE; exact ...` step for
whoever owns `L1SweepBridge.lean`.

The exploit is `i = j = 0`: there `{i' | i' < 0} = ∅` and `{j' | j' < 0} = ∅`, so `hwin 0 0`
collapses to "a single vector translates every point of `S₀.erase a` into `halfStrip B vl₀`".
With `B = {(0,0)}` and `vl₀ = (0,1)`, `halfStrip B vl₀ = {(0,t) : t : ℕ}` is the ray `x = 0`; the
two points `(1,0)` and `(2,0)` of `S₀.erase (0,0)` cannot both land there under one shift.

⚠ **2026-09-20 label (team-lead review): refutes the pre-`EnvOf` form of `HwinHoleE`, retired
2026-09-19 when `EnvOf ↑Sw B` was added to the live definition.** This theorem's own premise
list is the unfolded body *without* an `EnvOf`-shaped hypothesis; its witness `B := {(0,0)}` is
a singleton, so if the current `HwinHoleZ`'s `EnvOf (↑S₀) B` premise were added here it would
force `E B = E S₀` (`Enveloped.E_eq`) — impossible for singleton `B` against the non-collinear
`S₀ = {(0,0),(1,0),(2,0)}`, whose `E S₀ = {(0,1),(0,-1)}` (see `singleton_of_envOf_singleton`
above, contrapositive). So this theorem does **not** refute `HwinHoleZ` as currently stated; it
refutes the retired closure that omitted the `EnvOf` guard. Kept per PROTOCOL §14 — not deleted,
because the mechanism (§16's escaping-generator descent) is exactly what `L1SweepBridge`'s §16–18
now generalize past the singleton case. -/

/-- `LatticeConvex` of a two-point set on a common line, proved from scratch (no existing
convexity hypothesis): the real segment between `(1,0)` and `(2,0)` meets `ℤ × ℤ` only at its
integer-coordinate endpoints. -/
theorem latticeConvex_pair_S017 :
    LatticeConvex ({(1, 0), (2, 0)} : Finset (ℤ × ℤ)) := by
  rintro ⟨z1, z2⟩ hz
  rw [Conv, Finset.coe_insert, Finset.coe_singleton, Set.image_insert_eq, Set.image_singleton,
    convexHull_pair] at hz
  obtain ⟨s, t, hs, ht, hst, hzeq⟩ := hz
  simp only [toReal, Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk, Prod.mk.injEq] at hzeq
  obtain ⟨hz1, hz2⟩ := hzeq
  have hz2' : z2 = 0 := by
    have h0 : (z2 : ℝ) = 0 := by rw [← hz2]; ring
    exact_mod_cast h0
  have hst' : s = 1 - t := by linarith
  have hz1' : (z1 : ℝ) = 1 + t := by rw [← hz1, hst']; ring
  have hb1 : (1 : ℤ) ≤ z1 := by
    have h0 : (1 : ℝ) ≤ (z1 : ℝ) := by rw [hz1']; linarith
    exact_mod_cast h0
  have hb2 : z1 ≤ 2 := by
    have h0 : (z1 : ℝ) ≤ 2 := by rw [hz1']; linarith
    exact_mod_cast h0
  have hcase : z1 = 1 ∨ z1 = 2 := by omega
  rcases hcase with h1 | h1 <;> subst h1 <;> subst hz2' <;> simp

/-- **`¬ HwinHoleE`'s unfolded body**, at the explicit witness `ξ₀ = 0`, `S₀ = {(0,0),(1,0),(2,0)}`,
`vl₀ = (0,1)`.  Every premise of the inner `∀` is discharged at `B := {(0,0)}`, `a := (0,0)`,
`c := 1`, `K := u'.2`, `u := (0,0)`; the contradiction is `hwin 0 0` applied to `(1,0)` and
`(2,0)`, both forced onto the single ray `halfStrip {(0,0)} (0,1) = {(0,t) : t}`. -/
theorem not_hwinHoleE_body :
    ¬ ∃ u' : ℤ × ℤ, (det u' ((0 : ℤ), (1 : ℤ)) = 1 ∨ det u' ((0 : ℤ), (1 : ℤ)) = -1) ∧
      ∀ (B : Set (ℤ × ℤ)) (u : ℤ × ℤ) (c : ℤ) (a : ℤ × ℤ) (K : ℤ),
        a ∈ ({(0, 0), (1, 0), (2, 0)} : Finset (ℤ × ℤ)) →
        LatticeConvex (({(0, 0), (1, 0), (2, 0)} : Finset (ℤ × ℤ)).erase a) → 0 < c →
        B.Finite →
        (∀ b ∈ ({(0, 0), (1, 0), (2, 0)} : Finset (ℤ × ℤ)),
          dot (expNormal (u' - K • ((0 : ℤ), (1 : ℤ))) ((0 : ℤ), (1 : ℤ))) a ≤
            dot (expNormal (u' - K • ((0 : ℤ), (1 : ℤ))) ((0 : ℤ), (1 : ℤ))) b) →
        (∀ z ∈ halfStrip B ((0 : ℤ), (1 : ℤ)),
          (T u (fun _ => (0 : ℤ))) z =
            T (c • ((0 : ℤ), (1 : ℤ))) (T u (fun _ => (0 : ℤ))) z) →
        ∃ b₀ ∈ B, ∃ enum : ℕ → ℕ → ℤ × ℤ,
          (∀ i j : ℕ, ∀ z ∈ (({(0, 0), (1, 0), (2, 0)} : Finset (ℤ × ℤ)).erase a),
            z + (enum i j - a) ∈
              halfStrip B ((0 : ℤ), (1 : ℤ)) ∪ (⋃ i' ∈ {i' | i' < i}, Set.range (enum i')) ∪
                (enum i '' {j' | j' < j})) ∧
          chainFull B ((0 : ℤ), (1 : ℤ)) (u' - K • ((0 : ℤ), (1 : ℤ))) b₀ 0 ⊆
            halfStrip B ((0 : ℤ), (1 : ℤ)) ∪ (⋃ i, Set.range (enum i)) := by
  rintro ⟨u', hunimod, h⟩
  have ha : ((0 : ℤ), (0 : ℤ)) ∈ ({(0, 0), (1, 0), (2, 0)} : Finset (ℤ × ℤ)) := by decide
  have herase : (({(0, 0), (1, 0), (2, 0)} : Finset (ℤ × ℤ)).erase ((0 : ℤ), (0 : ℤ))) =
      ({(1, 0), (2, 0)} : Finset (ℤ × ℤ)) := by decide
  have hconvS : LatticeConvex (({(0, 0), (1, 0), (2, 0)} : Finset (ℤ × ℤ)).erase ((0 : ℤ), (0 : ℤ))) := by
    rw [herase]; exact latticeConvex_pair_S017
  have hBfin : ({((0 : ℤ), (0 : ℤ))} : Set (ℤ × ℤ)).Finite := Set.finite_singleton _
  set K : ℤ := u'.2 with hK_def
  have hu''2 : (u' - K • ((0 : ℤ), (1 : ℤ))).2 = 0 := by
    show u'.2 - K * 1 = 0
    rw [hK_def]; ring
  have hn1 : (expNormal (u' - K • ((0 : ℤ), (1 : ℤ))) ((0 : ℤ), (1 : ℤ))).1 = 0 := by
    show (det (u' - K • ((0 : ℤ), (1 : ℤ))) ((0 : ℤ), (1 : ℤ))) *
        (-(u' - K • ((0 : ℤ), (1 : ℤ))).2) = 0
    rw [hu''2]; ring
  have hamin : ∀ b ∈ ({(0, 0), (1, 0), (2, 0)} : Finset (ℤ × ℤ)),
      dot (expNormal (u' - K • ((0 : ℤ), (1 : ℤ))) ((0 : ℤ), (1 : ℤ))) ((0 : ℤ), (0 : ℤ)) ≤
        dot (expNormal (u' - K • ((0 : ℤ), (1 : ℤ))) ((0 : ℤ), (1 : ℤ))) b := by
    intro b hb
    have hb2 : b.2 = 0 := by fin_cases hb <;> rfl
    unfold Nivat.LE2.dot
    rw [hn1]
    simp [hb2]
  have hD : ∀ z ∈ halfStrip ({((0 : ℤ), (0 : ℤ))} : Set (ℤ × ℤ)) ((0 : ℤ), (1 : ℤ)),
      (T ((0 : ℤ), (0 : ℤ)) (fun _ => (0 : ℤ))) z =
        T ((1 : ℤ) • ((0 : ℤ), (1 : ℤ))) (T ((0 : ℤ), (0 : ℤ)) (fun _ => (0 : ℤ))) z := by
    intro z hz
    simp [T]
  obtain ⟨b₀, hb₀, enum, hwin, hK⟩ :=
    h ({((0 : ℤ), (0 : ℤ))} : Set (ℤ × ℤ)) ((0 : ℤ), (0 : ℤ)) 1 ((0 : ℤ), (0 : ℤ)) K ha hconvS
      (by norm_num) hBfin hamin hD
  have hi0 : ({i' : ℕ | i' < 0} : Set ℕ) = ∅ := by ext x; simp
  have h1 := hwin 0 0 ((1 : ℤ), (0 : ℤ)) (by rw [herase]; decide)
  have h2 := hwin 0 0 ((2 : ℤ), (0 : ℤ)) (by rw [herase]; decide)
  rw [hi0] at h1 h2
  simp only [Set.biUnion_empty, Set.image_empty, Set.union_empty] at h1 h2
  obtain ⟨b1, hb1mem, t1, ht1⟩ := h1
  obtain ⟨b2, hb2mem, t2, ht2⟩ := h2
  simp only [Set.mem_singleton_iff] at hb1mem hb2mem
  subst hb1mem
  subst hb2mem
  have e1 := congrArg Prod.fst ht1
  have e2 := congrArg Prod.fst ht2
  simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, Prod.fst_sub] at e1 e2
  omega

section AxiomReceipts17

#print axioms latticeConvex_pair_S017
#print axioms not_hwinHoleE_body

end AxiomReceipts17

/-! ## Task 1 (team-lead, 2026-09-19): `EnvOf` with a singleton base forces a singleton
window.

`EnvOf U T := Enveloped U T`, and `Enveloped U T := WeaklyEnveloped U T ∧
(E T).encard = (E U).encard` (`LatticeEdges.lean:624-629`).  Team-lead's claim
`EnvOf (↑Sw) B` with `B` a singleton forces `Sw` singleton is exactly: the second
`Enveloped` field forces `(E ↑Sw).encard = (E B).encard = 0`, and a nonempty finite set
with empty `E` is a subsingleton.  That second fact is the content; it does not mention
`EnvOf` at all, so it is proved as a standalone lemma first. -/

/-- **A nonempty finite planar set with no edges is a single point.**  Case split on
`PosArea`: if positive, `isFrame_E` hands back a member of `E T` for *any* nonzero cone
direction, contradicting `E T = ∅` outright.  If not, `T` is collinear along the chord
through any two of its points `p ≠ q`; the left-normal `m` of that chord's primitive
direction then has *every* pairwise `dot` value on `T` equal (not just on `p, q` — the
collinearity is set-wide), so `face T m = T`, which is nontrivial once `T` has two
points — putting `m ∈ E T`, again contradicting `E T = ∅`. -/
theorem subsingleton_of_E_eq_empty {T : Set (ℤ × ℤ)} (hfin : T.Finite) (hne : T.Nonempty)
    (hE : E T = ∅) : T.Subsingleton := by
  intro p hp q hq
  by_contra hpq
  by_cases harea : PosArea T
  · obtain ⟨n₁, -, -, -, hn₁, -, -, -, -, -, -, -, -, -⟩ :=
      isFrame_E hfin hne harea (1, 0) (by norm_num [Prod.ext_iff])
    simp [hE] at hn₁
  · have hcol := collinear_of_not_posArea harea hp hq
    set w : ℤ × ℤ := q - p with hwdef
    have hw0 : w ≠ 0 := sub_ne_zero.mpr (Ne.symm hpq)
    obtain ⟨hprim, g, hg, hgeq⟩ := primPart_spec hw0
    set m : ℤ × ℤ := nrmL (primPart w) with hmdef
    have hprimM : Prim m := by
      have hgcd : Int.gcd (primPart w).1 (primPart w).2 = 1 := hprim
      show Int.gcd m.1 m.2 = 1
      have h1 : m.1 = -(primPart w).2 := by rw [hmdef]; rfl
      have h2 : m.2 = (primPart w).1 := by rw [hmdef]; rfl
      rw [h1, h2, Int.gcd, Int.natAbs_neg, Nat.gcd_comm]
      exact hgcd
    have hconst : ∀ z ∈ T, ∀ z' ∈ T, dot m z = dot m z' := by
      intro z hz z' hz'
      have hdw : det (z - z') w = 0 := hcol z hz z' hz'
      have hdw' : det (z - z') w = g * det (z - z') (primPart w) := by
        conv_lhs => rw [hgeq]
        simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
      rw [hdw'] at hdw
      have hg0 : g ≠ 0 := ne_of_gt hg
      have hdz : det (z - z') (primPart w) = 0 := by
        rcases mul_eq_zero.mp hdw with h | h
        · exact absurd h hg0
        · exact h
      have hdz' : dot m (z - z') = 0 := by
        rw [hmdef, dot_nrmL, det_skew, hdz, neg_zero]
      have hds := dot_sub m z z'
      rw [hdz'] at hds
      linarith
    have hface : face T m = T := by
      ext z
      constructor
      · exact fun h => h.1
      · intro hzT
        exact ⟨hzT, fun y hy => le_of_eq (hconst y hy z hzT)⟩
    have hnt : (face T m).Nontrivial := by
      rw [hface]; exact ⟨p, hp, q, hq, hpq⟩
    have hmE : m ∈ E T := ⟨hprimM, hnt⟩
    simp [hE] at hmE

/-- **`EnvOf` with a singleton base forces a singleton window** (team-lead's Task 1,
compiled rather than assumed).  If `Sw` is nonempty and `E({b})`-enveloped, `Sw` is
itself a singleton. -/
theorem singleton_of_envOf_singleton {Sw : Finset (ℤ × ℤ)} {b : ℤ × ℤ}
    (hSne : Sw.Nonempty) (h : EnvOf (↑Sw : Set (ℤ × ℤ)) ({b} : Set (ℤ × ℤ))) :
    ∃ a, Sw = {a} := by
  have hEB : E ({b} : Set (ℤ × ℤ)) = ∅ := by
    ext n
    simp only [Set.mem_empty_iff_false, iff_false, mem_E_iff, not_and]
    intro _ hnt
    obtain ⟨x, hx, y, hy, hxy⟩ := hnt
    have hxb : x = b := face_subset ({b} : Set (ℤ × ℤ)) n hx
    have hyb : y = b := face_subset ({b} : Set (ℤ × ℤ)) n hy
    exact hxy (hxb.trans hyb.symm)
  have hcard : (E ({b} : Set (ℤ × ℤ))).encard = (E (↑Sw : Set (ℤ × ℤ))).encard := h.2
  rw [hEB, Set.encard_empty] at hcard
  have hESw : E (↑Sw : Set (ℤ × ℤ)) = ∅ := Set.encard_eq_zero.mp hcard.symm
  have hfin : (↑Sw : Set (ℤ × ℤ)).Finite := Sw.finite_toSet
  have hne : (↑Sw : Set (ℤ × ℤ)).Nonempty := by exact_mod_cast hSne
  have hsub := subsingleton_of_E_eq_empty hfin hne hESw
  obtain ⟨a, ha⟩ := hne
  refine ⟨a, ?_⟩
  apply Finset.coe_injective
  rw [Finset.coe_singleton]
  exact hsub.eq_singleton_of_mem ha

section AxiomReceiptsTask1

#print axioms subsingleton_of_E_eq_empty
#print axioms singleton_of_envOf_singleton

end AxiomReceiptsTask1

/-! ## Task 2 (team-lead, 2026-09-19/20): shearing forces the argmin off one `det · vl` extreme

`false_of_hwin_hK_of_det_pos`/`_neg` (landed by team-lead in `L1SweepBridge.lean` §16–§17) need,
at the hole's own shear parameter `K`, that the minimizer `a` of
`dot (expNormal (u' - K•vl) vl)` over a finite `Sw` fails to be the `det · vl`-extreme of `Sw`
on the relevant side.  `K` is existentially owned by the hole (`HwinHoleZ` quantifies over it),
so it is ours to choose.

The shear identity `dot_expNormal_shear` (`L1StraddleWedge.lean:393`) turns the sheared
functional into `A + K · uCoord u' vl 0 (·)` where `A z := dot (expNormal u' vl) z`; unfolding
`uCoord u' vl 0 z = -(det u' vl) * det vl (z - 0)` (`L1Line0.lean:93`) against `det_skew` gives
`uCoord u' vl 0 z = det u' vl * det z vl`.  So for `K := det u' vl * N` the sheared functional is
*exactly* `A + N · (det · vl)` for **any** sign of `det u' vl`, since `(det u' vl)^2 = 1`
absorbs the sign into `N` itself — no case split on `hunimod` survives past this point.  Taking
`N` past the spread of `A` over `Sw` forces any minimizer's `det · vl` value all the way to
`Sw`'s minimum; `K := -(det u' vl) * N` forces it to the maximum instead.  `hnc` (two distinct
`det · vl` values on `Sw`) is exactly what makes "the minimum" and "the maximum" different
points, so the pushed-to extreme can never be the *other* extreme — which is the mirror the two
`false_of_hwin_hK_of_det_*` lemmas need.

Both theorems below are landed standalone; per team-lead's instruction, no assembly against
`HwinHoleZ` is attempted here (that would require importing `L1SweepBridge`, which imports this
file). -/

/-- `det` is additive in its first argument. -/
theorem det_sub_left (p q vl : ℤ × ℤ) : det (p - q) vl = det p vl - det q vl := by
  simp only [det, Prod.fst_sub, Prod.snd_sub]; ring

/-- **The shear forces the argmin to the `det · vl`-minimum of `Sw`**, so any minimizer of
`dot (expNormal (u' - K•vl) vl)` at this `K` is *not* the `det · vl`-maximum of `Sw`: the
witness `z` is the maximiser, distinct from `a` by `hnc`. -/
theorem exists_shear_argmin_not_detMax
    {Sw : Finset (ℤ × ℤ)} {u' vl : ℤ × ℤ} (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hnc : ∃ z₁ ∈ Sw, ∃ z₂ ∈ Sw, det z₁ vl ≠ det z₂ vl) :
    ∃ K : ℤ, ∀ a ∈ Sw,
      (∀ b ∈ Sw, dot (expNormal (u' - K • vl) vl) a ≤ dot (expNormal (u' - K • vl) vl) b) →
      ∃ z ∈ Sw.erase a, 0 < det (z - a) vl := by
  obtain ⟨z₁, hz₁, z₂, hz₂, hz12⟩ := hnc
  have hSne : Sw.Nonempty := ⟨z₁, hz₁⟩
  obtain ⟨aM, haM, hAmax⟩ := Sw.exists_max_image (fun z => dot (expNormal u' vl) z) hSne
  obtain ⟨am, ham, hAmin⟩ := Sw.exists_min_image (fun z => dot (expNormal u' vl) z) hSne
  obtain ⟨zM, hzM, hDmax⟩ := Sw.exists_max_image (fun z => det z vl) hSne
  obtain ⟨zm, hzm, hDmin⟩ := Sw.exists_min_image (fun z => det z vl) hSne
  set N : ℤ := dot (expNormal u' vl) aM - dot (expNormal u' vl) am + 1 with hNdef
  have hN1 : 1 ≤ N := by have := hAmin aM haM; omega
  refine ⟨det u' vl * N, fun a ha hamin => ?_⟩
  have hshear : ∀ z : ℤ × ℤ,
      dot (expNormal (u' - (det u' vl * N) • vl) vl) z
        = dot (expNormal u' vl) z + N * det z vl := by
    intro z
    rw [Nivat.L1StraddleWedge.dot_expNormal_shear]
    have huc : uCoord u' vl 0 z = det u' vl * det z vl := by
      simp only [uCoord, sub_zero]
      rw [det_skew vl z]; ring
    rw [huc]
    rcases hunimod with h | h <;> rw [h] <;> ring
  have hamin' : dot (expNormal u' vl) a + N * det a vl
      ≤ dot (expNormal u' vl) zm + N * det zm vl := by
    have h := hamin zm hzm
    rwa [hshear, hshear] at h
  have hne : det zm vl ≠ det zM vl := by
    intro heq
    have e1 : det z₁ vl = det zm vl := by
      have h1 := hDmin z₁ hz₁; have h2 := hDmax z₁ hz₁; omega
    have e2 : det z₂ vl = det zm vl := by
      have h1 := hDmin z₂ hz₂; have h2 := hDmax z₂ hz₂; omega
    exact hz12 (e1.trans e2.symm)
  have hspread : det zm vl < det zM vl := lt_of_le_of_ne (hDmin zM hzM) hne
  have haeq : det a vl = det zm vl := by
    by_contra hne2
    have hge : det zm vl + 1 ≤ det a vl := by have := hDmin a ha; omega
    have hprod : N * (det zm vl + 1) ≤ N * det a vl :=
      mul_le_mul_of_nonneg_left hge (by omega)
    have hAzm : dot (expNormal u' vl) zm ≤ dot (expNormal u' vl) aM := hAmax zm hzm
    have hAam : dot (expNormal u' vl) am ≤ dot (expNormal u' vl) a := hAmin a ha
    nlinarith [hamin', hprod, hAzm, hAam]
  have haM' : zM ≠ a := by
    intro h; rw [← h] at haeq; omega
  exact ⟨zM, Finset.mem_erase.mpr ⟨haM', hzM⟩, by rw [det_sub_left]; omega⟩

/-- **Mirror of `exists_shear_argmin_not_detMax`**: the shear `K := -(det u' vl) * N` forces the
argmin to the `det · vl`-maximum instead, so it is *not* the `det · vl`-minimum. -/
theorem exists_shear_argmin_not_detMin
    {Sw : Finset (ℤ × ℤ)} {u' vl : ℤ × ℤ} (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hnc : ∃ z₁ ∈ Sw, ∃ z₂ ∈ Sw, det z₁ vl ≠ det z₂ vl) :
    ∃ K : ℤ, ∀ a ∈ Sw,
      (∀ b ∈ Sw, dot (expNormal (u' - K • vl) vl) a ≤ dot (expNormal (u' - K • vl) vl) b) →
      ∃ z ∈ Sw.erase a, det (z - a) vl < 0 := by
  obtain ⟨z₁, hz₁, z₂, hz₂, hz12⟩ := hnc
  have hSne : Sw.Nonempty := ⟨z₁, hz₁⟩
  obtain ⟨aM, haM, hAmax⟩ := Sw.exists_max_image (fun z => dot (expNormal u' vl) z) hSne
  obtain ⟨am, ham, hAmin⟩ := Sw.exists_min_image (fun z => dot (expNormal u' vl) z) hSne
  obtain ⟨zM, hzM, hDmax⟩ := Sw.exists_max_image (fun z => det z vl) hSne
  obtain ⟨zm, hzm, hDmin⟩ := Sw.exists_min_image (fun z => det z vl) hSne
  set N : ℤ := dot (expNormal u' vl) aM - dot (expNormal u' vl) am + 1 with hNdef
  have hN1 : 1 ≤ N := by have := hAmin aM haM; omega
  refine ⟨-(det u' vl * N), fun a ha hamin => ?_⟩
  have hshear : ∀ z : ℤ × ℤ,
      dot (expNormal (u' - (-(det u' vl * N)) • vl) vl) z
        = dot (expNormal u' vl) z - N * det z vl := by
    intro z
    rw [Nivat.L1StraddleWedge.dot_expNormal_shear]
    have huc : uCoord u' vl 0 z = det u' vl * det z vl := by
      simp only [uCoord, sub_zero]
      rw [det_skew vl z]; ring
    rw [huc]
    rcases hunimod with h | h <;> rw [h] <;> ring
  have hamin' : dot (expNormal u' vl) a - N * det a vl
      ≤ dot (expNormal u' vl) zM - N * det zM vl := by
    have h := hamin zM hzM
    rwa [hshear, hshear] at h
  have hne : det zm vl ≠ det zM vl := by
    intro heq
    have e1 : det z₁ vl = det zm vl := by
      have h1 := hDmin z₁ hz₁; have h2 := hDmax z₁ hz₁; omega
    have e2 : det z₂ vl = det zm vl := by
      have h1 := hDmin z₂ hz₂; have h2 := hDmax z₂ hz₂; omega
    exact hz12 (e1.trans e2.symm)
  have hspread : det zm vl < det zM vl := lt_of_le_of_ne (hDmin zM hzM) hne
  have haeq : det a vl = det zM vl := by
    by_contra hne2
    have hge : det a vl + 1 ≤ det zM vl := by have := hDmax a ha; omega
    have hprod : N * (det a vl + 1) ≤ N * det zM vl :=
      mul_le_mul_of_nonneg_left hge (by omega)
    have hAaM : dot (expNormal u' vl) zM ≤ dot (expNormal u' vl) aM := hAmax zM hzM
    have hAamzM : dot (expNormal u' vl) am ≤ dot (expNormal u' vl) a := hAmin a ha
    nlinarith [hamin', hprod, hAaM, hAamzM]
  have ham' : zm ≠ a := by
    intro h; rw [← h] at haeq; omega
  exact ⟨zm, Finset.mem_erase.mpr ⟨ham', hzm⟩, by rw [det_sub_left]; omega⟩

section AxiomReceiptsTask2

#print axioms det_sub_left
#print axioms exists_shear_argmin_not_detMax
#print axioms exists_shear_argmin_not_detMin

end AxiomReceiptsTask2

/-! ## Task 3 (team-lead, 2026-09-20): shearing forces the argmin onto a `G`-extreme, unconditionally

`false_of_hwin_hK_of_seed_le`/`_of_le_seed` (§18, `L1SweepBridge.lean`) run against an
**arbitrary** seed `D`, and the shear parameter `K` is still ours to choose (`HwinHoleZ`
quantifies over it). Write `G z := dot (expNormal vl u') z` (roles of `u'`/`vl` swapped inside
`expNormal`, matching team-lead's framing via `HbaseBridge.expNormal_shear`). Unlike Task 2,
**no `hunimod` is needed here**: `dot_expNormal_shear` (`L1StraddleWedge.lean:393`) is a raw
polynomial identity, and unfolding both `uCoord u' vl 0 z` and `G z` against `det`/`expNormal`
shows they are the *same* function of `z`, namely `det u' vl * det z vl` — no case split, no
unimodularity, just `ring`. So the sheared functional is exactly `A + K·G` where
`A z := dot (expNormal u' vl) z`, for **every** `K`, matching team-lead's framing exactly (not
merely a corollary of it). -/

/-- `dot (expNormal vl u') z` and `uCoord u' vl 0 z` are the same function of `z` — both equal
`det u' vl * det z vl` — so the shear identity `dot_expNormal_shear` already *is* the `A + K·G`
decomposition, with no extra hypothesis. -/
theorem dot_expNormal_swap_eq_uCoord (u' vl z : ℤ × ℤ) :
    dot (expNormal vl u') z = uCoord u' vl 0 z := by
  have hG : dot (expNormal vl u') z = det u' vl * det z vl := by
    simp only [expNormal, dot, det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  have huc : uCoord u' vl 0 z = det u' vl * det z vl := by
    simp only [uCoord, sub_zero]
    rw [det_skew vl z]; ring
  rw [hG, huc]

/-- **The shear identity in team-lead's `A + K·G` form**, unconditional (no `hunimod`). -/
theorem dot_expNormal_shear_swap (u' vl : ℤ × ℤ) (K : ℤ) (z : ℤ × ℤ) :
    dot (expNormal (u' - K • vl) vl) z
      = dot (expNormal u' vl) z + K * dot (expNormal vl u') z := by
  rw [Nivat.L1StraddleWedge.dot_expNormal_shear, ← dot_expNormal_swap_eq_uCoord]

/-- **Every `f K`-minimiser is a `G`-minimiser, for `K` large.**  `a` is chosen as a `G`-minimiser
over `Sw`, tie-broken by `A`-minimality among the `G`-minimisers; `K := ` the `A`-spread on `Sw`
then dominates any strict `G`-gap. -/
theorem exists_K_argmin_G (Sw : Finset (ℤ × ℤ)) (hne : Sw.Nonempty) (u' vl : ℤ × ℤ) :
    ∃ K : ℤ, ∃ a ∈ Sw,
      (∀ b ∈ Sw, dot (expNormal (u' - K • vl) vl) a ≤ dot (expNormal (u' - K • vl) vl) b) ∧
      (∀ b ∈ Sw, dot (expNormal vl u') a ≤ dot (expNormal vl u') b) := by
  classical
  obtain ⟨a0, ha0, hGmin0⟩ := Sw.exists_min_image (fun z => dot (expNormal vl u') z) hne
  set T : Finset (ℤ × ℤ) :=
    Sw.filter (fun z => dot (expNormal vl u') z = dot (expNormal vl u') a0) with hTdef
  have hTne : T.Nonempty := ⟨a0, Finset.mem_filter.mpr ⟨ha0, rfl⟩⟩
  obtain ⟨a, haT, hAminT⟩ := T.exists_min_image (fun z => dot (expNormal u' vl) z) hTne
  have haSw : a ∈ Sw := (Finset.mem_filter.mp haT).1
  have haG : dot (expNormal vl u') a = dot (expNormal vl u') a0 := (Finset.mem_filter.mp haT).2
  obtain ⟨aM, haM, hAmax⟩ := Sw.exists_max_image (fun z => dot (expNormal u' vl) z) hne
  obtain ⟨am, ham, hAmin⟩ := Sw.exists_min_image (fun z => dot (expNormal u' vl) z) hne
  set N : ℤ := dot (expNormal u' vl) aM - dot (expNormal u' vl) am + 1 with hNdef
  have hN1 : 1 ≤ N := by have := hAmin aM haM; omega
  have hGle : ∀ b ∈ Sw, dot (expNormal vl u') a ≤ dot (expNormal vl u') b := by
    intro b hb; rw [haG]; exact hGmin0 b hb
  refine ⟨N, a, haSw, fun b hb => ?_, hGle⟩
  rw [dot_expNormal_shear_swap, dot_expNormal_shear_swap]
  rcases (hGle b hb).lt_or_eq with hlt | heq
  · have hAa : dot (expNormal u' vl) a ≤ dot (expNormal u' vl) aM := hAmax a haSw
    have hAb : dot (expNormal u' vl) am ≤ dot (expNormal u' vl) b := hAmin b hb
    have hge : dot (expNormal vl u') a + 1 ≤ dot (expNormal vl u') b := hlt
    have hprod : N * (dot (expNormal vl u') a + 1) ≤ N * dot (expNormal vl u') b :=
      mul_le_mul_of_nonneg_left hge (by omega)
    nlinarith [hprod, hAa, hAb]
  · have hbT : b ∈ T := Finset.mem_filter.mpr ⟨hb, heq.symm.trans haG⟩
    have hAab : dot (expNormal u' vl) a ≤ dot (expNormal u' vl) b := hAminT b hbT
    nlinarith [hAab, heq]

/-- **Mirror of `exists_K_argmin_G`**: `K` of the opposite sign forces every `f K`-minimiser to
be a `G`-**maximiser**. -/
theorem exists_K_argmax_G (Sw : Finset (ℤ × ℤ)) (hne : Sw.Nonempty) (u' vl : ℤ × ℤ) :
    ∃ K : ℤ, ∃ a ∈ Sw,
      (∀ b ∈ Sw, dot (expNormal (u' - K • vl) vl) a ≤ dot (expNormal (u' - K • vl) vl) b) ∧
      (∀ b ∈ Sw, dot (expNormal vl u') b ≤ dot (expNormal vl u') a) := by
  classical
  obtain ⟨a0, ha0, hGmax0⟩ := Sw.exists_max_image (fun z => dot (expNormal vl u') z) hne
  set T : Finset (ℤ × ℤ) :=
    Sw.filter (fun z => dot (expNormal vl u') z = dot (expNormal vl u') a0) with hTdef
  have hTne : T.Nonempty := ⟨a0, Finset.mem_filter.mpr ⟨ha0, rfl⟩⟩
  obtain ⟨a, haT, hAminT⟩ := T.exists_min_image (fun z => dot (expNormal u' vl) z) hTne
  have haSw : a ∈ Sw := (Finset.mem_filter.mp haT).1
  have haG : dot (expNormal vl u') a = dot (expNormal vl u') a0 := (Finset.mem_filter.mp haT).2
  obtain ⟨aM, haM, hAmax⟩ := Sw.exists_max_image (fun z => dot (expNormal u' vl) z) hne
  obtain ⟨am, ham, hAmin⟩ := Sw.exists_min_image (fun z => dot (expNormal u' vl) z) hne
  set N : ℤ := dot (expNormal u' vl) aM - dot (expNormal u' vl) am + 1 with hNdef
  have hN1 : 1 ≤ N := by have := hAmin aM haM; omega
  have hGge : ∀ b ∈ Sw, dot (expNormal vl u') b ≤ dot (expNormal vl u') a := by
    intro b hb; rw [haG]; exact hGmax0 b hb
  refine ⟨-N, a, haSw, fun b hb => ?_, hGge⟩
  rw [dot_expNormal_shear_swap, dot_expNormal_shear_swap]
  rcases (hGge b hb).lt_or_eq with hlt | heq
  · have hAa : dot (expNormal u' vl) a ≤ dot (expNormal u' vl) aM := hAmax a haSw
    have hAb : dot (expNormal u' vl) am ≤ dot (expNormal u' vl) b := hAmin b hb
    have hge : dot (expNormal vl u') a ≥ dot (expNormal vl u') b + 1 := hlt
    have hprod : N * (dot (expNormal vl u') b + 1) ≤ N * dot (expNormal vl u') a :=
      mul_le_mul_of_nonneg_left hge (by omega)
    nlinarith [hprod, hAa, hAb]
  · have hbT : b ∈ T := Finset.mem_filter.mpr ⟨hb, heq.trans haG⟩
    have hAab : dot (expNormal u' vl) a ≤ dot (expNormal u' vl) b := hAminT b hbT
    nlinarith [hAab, heq]

section AxiomReceiptsTask3

#print axioms dot_expNormal_swap_eq_uCoord
#print axioms dot_expNormal_shear_swap
#print axioms exists_K_argmin_G
#print axioms exists_K_argmax_G

end AxiomReceiptsTask3

/-! ## Task 4 (team-lead, 2026-09-20): `exists_corner_shear`'s vertex is the wrong `det · vl` extreme

Team-lead's question: does `L1StraddleWedge.exists_corner_shear` (`:424`) produce a vertex `a`
with the sound sign (matching §19's necessary condition on the `hamin`-vertex,
`detMax_of_hwin_hK` / `detMin_of_hwin_hK`) or the refuted one?

**Answer: refuted, always, whenever `S` is not `vl`-collinear — no reading of the proof body is
even required, it follows from `exists_corner_shear`'s own stated conclusion.**

`exists_corner_shear` returns `a` together with `∀ b ∈ S, 0 ≤ dot en' (b - a) ∧
0 ≤ uCoord (u' - K•vl) vl a b`.  `uCoord_shear` (shear-invariance, already on this file's import
path) turns the second conjunct into `0 ≤ uCoord u' vl a b`, and `uCoord_eq_sub` turns *that* into
`uCoord u' vl 0 a ≤ uCoord u' vl 0 b`.  So **`a` is the global minimiser of `z ↦ uCoord u' vl 0 z`
over `S`, independent of `K` and independent of which `K` the proof happens to choose** —
`corner_shear_a_isMin_uCoordZero` below extracts exactly this, from the signature alone.

Unconditionally (`uCoord_zero_eq_det_mul_det`, no `hunimod`), `uCoord u' vl 0 z = det u' vl *
det z vl`.  Minimising that over `S` means:
- `det u' vl = 1`: `a` is the `det · vl`-**minimum** of `S`;
- `det u' vl = -1`: `a` is the `det · vl`-**maximum** of `S`.

§19's `detMax_of_hwin_hK` / `detMin_of_hwin_hK` need exactly the opposite (`a` = **maximum** when
`det u' vl = 1`, **minimum** when `-1`).  So whenever `S` is not entirely on one `vl`-parallel
line (`hnc`), `exists_corner_shear`'s `a` sits at the extreme `hwin ∧ hK` can never reach.
`corner_shear_a_wrong_extreme` packages the clash as a closed statement about the two extremes
disagreeing — no `hwin`/`hK`/`hbase` hypothesis on either side, purely a consequence of
`exists_corner_shear`'s published output vs. the `det u' vl * det z vl` identity.

**Reading limit.**  This refutes the *corner-shear* route to `hbase`, not `hbase` itself and not
Collé's Lemma 4.5 — `sorry` count and `axiom_closure` are unchanged.  The remaining open route
(§18's arbitrary-seed / flat `hwin` path) is untouched by this. -/

theorem uCoord_zero_eq_det_mul_det (u' vl z : ℤ × ℤ) :
    uCoord u' vl 0 z = det u' vl * det z vl := by
  simp only [uCoord, sub_zero]
  rw [det_skew vl z]; ring

/-- `exists_corner_shear`'s `a` is the global `uCoord u' vl 0`-minimiser over `S`, read straight
off the theorem's stated conclusion — no need to open its proof. -/
theorem corner_shear_a_isMin_uCoordZero
    {S : Finset (ℤ × ℤ)} {u' vl : ℤ × ℤ} {K : ℤ} {a : ℤ × ℤ}
    (hcorner : ∀ b ∈ S, 0 ≤ dot (expNormal (u' - K • vl) vl) (b - a) ∧
      0 ≤ uCoord (u' - K • vl) vl a b) :
    ∀ b ∈ S, uCoord u' vl 0 a ≤ uCoord u' vl 0 b := by
  intro b hb
  have h2 := (hcorner b hb).2
  rw [uCoord_shear] at h2
  have heq := uCoord_eq_sub (u' := u') (vl := vl) (a := a) (b := b)
  omega

/-- Instantiated against `exists_corner_shear` itself: its output vertex is the global
`uCoord u' vl 0`-minimiser over `S`. -/
theorem exists_corner_shear_a_isMin_uCoordZero
    {S : Finset (ℤ × ℤ)} (hS : S.Nonempty) {u' vl : ℤ × ℤ} :
    ∃ K : ℤ, ∃ a ∈ S, ∀ b ∈ S, uCoord u' vl 0 a ≤ uCoord u' vl 0 b := by
  obtain ⟨K, a, ha, hc⟩ := exists_corner_shear (u' := u') (vl := vl) hS
  exact ⟨K, a, ha, corner_shear_a_isMin_uCoordZero hc⟩

/-- A `uCoord u' vl 0`-minimiser is the `det · vl`-**minimum** of `S` when `det u' vl = 1`, so it
cannot also be the `det · vl`-maximum unless `S` is `vl`-collinear.  This is the clash with
§19's `detMax_of_hwin_hK`. -/
theorem corner_shear_a_not_detMax
    {S : Finset (ℤ × ℤ)} {u' vl a : ℤ × ℤ}
    (haMin : ∀ b ∈ S, uCoord u' vl 0 a ≤ uCoord u' vl 0 b)
    (hdet : det u' vl = 1)
    (hnc : ∃ z₁ ∈ S, ∃ z₂ ∈ S, det z₁ vl ≠ det z₂ vl)
    (haS : a ∈ S) :
    ¬ ∀ b ∈ S.erase a, det b vl ≤ det a vl := by
  intro hmax
  obtain ⟨z₁, hz₁, z₂, hz₂, hne⟩ := hnc
  have haMinDet : ∀ b ∈ S, det a vl ≤ det b vl := by
    intro b hb
    have h := haMin b hb
    rw [uCoord_zero_eq_det_mul_det, uCoord_zero_eq_det_mul_det, hdet] at h
    omega
  have hmaxAll : ∀ b ∈ S, det b vl ≤ det a vl := by
    intro b hb
    by_cases hba : b = a
    · subst hba; exact le_refl _
    · exact hmax b (Finset.mem_erase.mpr ⟨hba, hb⟩)
  have hz1eq : det z₁ vl = det a vl := le_antisymm (hmaxAll z₁ hz₁) (haMinDet z₁ hz₁)
  have hz2eq : det z₂ vl = det a vl := le_antisymm (hmaxAll z₂ hz₂) (haMinDet z₂ hz₂)
  exact hne (hz1eq.trans hz2eq.symm)

/-- Mirror of `corner_shear_a_not_detMax`: the clash with §19's `detMin_of_hwin_hK` when
`det u' vl = -1`. -/
theorem corner_shear_a_not_detMin
    {S : Finset (ℤ × ℤ)} {u' vl a : ℤ × ℤ}
    (haMin : ∀ b ∈ S, uCoord u' vl 0 a ≤ uCoord u' vl 0 b)
    (hdet : det u' vl = -1)
    (hnc : ∃ z₁ ∈ S, ∃ z₂ ∈ S, det z₁ vl ≠ det z₂ vl)
    (haS : a ∈ S) :
    ¬ ∀ b ∈ S.erase a, det a vl ≤ det b vl := by
  intro hmin'
  obtain ⟨z₁, hz₁, z₂, hz₂, hne⟩ := hnc
  have haMaxDet : ∀ b ∈ S, det b vl ≤ det a vl := by
    intro b hb
    have h := haMin b hb
    rw [uCoord_zero_eq_det_mul_det, uCoord_zero_eq_det_mul_det, hdet] at h
    omega
  have hminAll : ∀ b ∈ S, det a vl ≤ det b vl := by
    intro b hb
    by_cases hba : b = a
    · subst hba; exact le_refl _
    · exact hmin' b (Finset.mem_erase.mpr ⟨hba, hb⟩)
  have hz1eq : det z₁ vl = det a vl := le_antisymm (haMaxDet z₁ hz₁) (hminAll z₁ hz₁)
  have hz2eq : det z₂ vl = det a vl := le_antisymm (haMaxDet z₂ hz₂) (hminAll z₂ hz₂)
  exact hne (hz1eq.trans hz2eq.symm)

/-- **The headline, positive orientation.**  Whenever `S` is not `vl`-collinear and
`det u' vl = 1`, `exists_corner_shear`'s output vertex `a` fails §19's necessary condition
(`detMax_of_hwin_hK`) for admitting any `enum` with `hwin ∧ hK` — the corner-shear route is dead
here, not because of an enumeration technicality but because the vertex itself sits at the wrong
`det · vl` extreme. -/
theorem exists_corner_shear_wrong_extreme_pos
    {S : Finset (ℤ × ℤ)} (hS : S.Nonempty) {u' vl : ℤ × ℤ}
    (hdet : det u' vl = 1) (hnc : ∃ z₁ ∈ S, ∃ z₂ ∈ S, det z₁ vl ≠ det z₂ vl) :
    ∃ K : ℤ, ∃ a ∈ S, ¬ ∀ b ∈ S.erase a, det b vl ≤ det a vl := by
  obtain ⟨K, a, ha, hmin⟩ := exists_corner_shear_a_isMin_uCoordZero hS (u' := u') (vl := vl)
  exact ⟨K, a, ha, corner_shear_a_not_detMax hmin hdet hnc ha⟩

/-- Mirror of `exists_corner_shear_wrong_extreme_pos` at `det u' vl = -1`. -/
theorem exists_corner_shear_wrong_extreme_neg
    {S : Finset (ℤ × ℤ)} (hS : S.Nonempty) {u' vl : ℤ × ℤ}
    (hdet : det u' vl = -1) (hnc : ∃ z₁ ∈ S, ∃ z₂ ∈ S, det z₁ vl ≠ det z₂ vl) :
    ∃ K : ℤ, ∃ a ∈ S, ¬ ∀ b ∈ S.erase a, det a vl ≤ det b vl := by
  obtain ⟨K, a, ha, hmin⟩ := exists_corner_shear_a_isMin_uCoordZero hS (u' := u') (vl := vl)
  exact ⟨K, a, ha, corner_shear_a_not_detMin hmin hdet hnc ha⟩

section AxiomReceiptsTask4

#print axioms uCoord_zero_eq_det_mul_det
#print axioms corner_shear_a_isMin_uCoordZero
#print axioms exists_corner_shear_a_isMin_uCoordZero
#print axioms corner_shear_a_not_detMax
#print axioms corner_shear_a_not_detMin
#print axioms exists_corner_shear_wrong_extreme_pos
#print axioms exists_corner_shear_wrong_extreme_neg

end AxiomReceiptsTask4

/-! ## Task 5 (team-lead, 2026-09-20): does §18's `hδ` have a producer, or is it an assumption?

Team-lead's question: `L1SweepBridge.not_bddAbove_det_seed_of_hwin_hK` carries
`hδ : 0 < det (z - a) vl` for some `z ∈ Sw.erase a` as a free hypothesis (mirror:
`hδ : det (z - a) vl < 0`).  Is there any tree-wide producer of `hδ` that isn't "assume the
vertex is on the good side", or does §18 quietly need the same extremality Task 4 just showed
`exists_corner_shear` gets backwards?

**Producer-scan result first (§20/§24 discipline): zero tree-wide callers.**
`grep -n "not_bddAbove_det_seed_of_hwin_hK\|not_bddBelow_det_seed_of_hwin_hK"` across `Nivat/`
returns only the two declarations themselves and their own `#print axioms` receipts in
`L1SweepBridge.lean` — **no call site anywhere**.  So as the tree stands today, the honest answer
is: **there is no producer; `hδ` is an unexercised assumption.** §18 has never been invoked, by
anyone, on any concrete `Sw`/`a`/`z`.

**But it is not merely an assumption in disguise — it is producible, and only via the exact same
defect as Task 4, which answers the deeper half of the question.**  Take `a` to be
`exists_corner_shear`'s own output vertex (the natural candidate, since that is the only producer
of a corner point anywhere on the chain).  Task 4 already showed `a` is the global
`uCoord u' vl 0`-minimiser over `S`, i.e. (unconditionally) the `det u' vl`-scaled `det·vl`
extreme.  `exists_hδ_of_corner_shear_pos`/`_neg` below extract `hδ` **directly from that same
fact** plus `hnc` (`S` non-`vl`-collinear): if `a` is the `det·vl`-minimum and `S` has spread,
some element of `S` strictly exceeds it, which *is* `hδ`.  So:

> §18's gate is **not independent** of the corner-shear defect.  At the one concrete `a` the tree
> can actually produce (`exists_corner_shear`'s), `hδ` is not a free assumption to be discharged
> separately — it **follows for free** from the same "`a` is the wrong extreme" fact Task 4
> proved.  §18 does not open a second, independent route past the corner problem; applied to
> `exists_corner_shear`'s vertex it is a *second proof of the same underlying obstruction*, via a
> different mechanism (seed-boundedness instead of enum-domination).

Reading limit, carried forward: none of this claims `hbase` is false, `S` need not be
`vl`-collinear in general (that is what `hnc` excludes, and it is supplied on the chain,
`HbaseFlatSeed.exists_hnc_of_decompData_det`), and this says nothing about a *different* choice
of corner vertex not produced by `exists_corner_shear` — only that the one the tree actually
manufactures inherits the defect. `sorry` still 2, `axiom_closure` unchanged. -/

/-- `hδ`, positive orientation, derived from the same `uCoord`-minimality fact Task 4 used —
not a fresh assumption. -/
theorem exists_hδ_of_corner_shear_pos
    {S : Finset (ℤ × ℤ)} {u' vl a : ℤ × ℤ}
    (haMin : ∀ b ∈ S, uCoord u' vl 0 a ≤ uCoord u' vl 0 b)
    (hdet : det u' vl = 1)
    (hnc : ∃ z₁ ∈ S, ∃ z₂ ∈ S, det z₁ vl ≠ det z₂ vl) :
    ∃ z ∈ S.erase a, 0 < det (z - a) vl := by
  have haMinDet : ∀ b ∈ S, det a vl ≤ det b vl := by
    intro b hb
    have h := haMin b hb
    rw [uCoord_zero_eq_det_mul_det, uCoord_zero_eq_det_mul_det, hdet] at h
    omega
  obtain ⟨z₁, hz₁, z₂, hz₂, hne⟩ := hnc
  have hcase : det a vl < det z₁ vl ∨ det a vl < det z₂ vl := by
    by_contra hcon
    push_neg at hcon
    have e1 : det z₁ vl = det a vl := le_antisymm hcon.1 (haMinDet z₁ hz₁)
    have e2 : det z₂ vl = det a vl := le_antisymm hcon.2 (haMinDet z₂ hz₂)
    exact hne (e1.trans e2.symm)
  rcases hcase with h | h
  · refine ⟨z₁, Finset.mem_erase.mpr ⟨?_, hz₁⟩, ?_⟩
    · intro heq; rw [heq] at h; omega
    · rw [det_sub_left]; omega
  · refine ⟨z₂, Finset.mem_erase.mpr ⟨?_, hz₂⟩, ?_⟩
    · intro heq; rw [heq] at h; omega
    · rw [det_sub_left]; omega

/-- Mirror of `exists_hδ_of_corner_shear_pos` at `det u' vl = -1`. -/
theorem exists_hδ_of_corner_shear_neg
    {S : Finset (ℤ × ℤ)} {u' vl a : ℤ × ℤ}
    (haMin : ∀ b ∈ S, uCoord u' vl 0 a ≤ uCoord u' vl 0 b)
    (hdet : det u' vl = -1)
    (hnc : ∃ z₁ ∈ S, ∃ z₂ ∈ S, det z₁ vl ≠ det z₂ vl) :
    ∃ z ∈ S.erase a, det (z - a) vl < 0 := by
  have haMaxDet : ∀ b ∈ S, det b vl ≤ det a vl := by
    intro b hb
    have h := haMin b hb
    rw [uCoord_zero_eq_det_mul_det, uCoord_zero_eq_det_mul_det, hdet] at h
    omega
  obtain ⟨z₁, hz₁, z₂, hz₂, hne⟩ := hnc
  have hcase : det z₁ vl < det a vl ∨ det z₂ vl < det a vl := by
    by_contra hcon
    push_neg at hcon
    have e1 : det z₁ vl = det a vl := le_antisymm (haMaxDet z₁ hz₁) hcon.1
    have e2 : det z₂ vl = det a vl := le_antisymm (haMaxDet z₂ hz₂) hcon.2
    exact hne (e1.trans e2.symm)
  rcases hcase with h | h
  · refine ⟨z₁, Finset.mem_erase.mpr ⟨?_, hz₁⟩, ?_⟩
    · intro heq; rw [heq] at h; omega
    · rw [det_sub_left]; omega
  · refine ⟨z₂, Finset.mem_erase.mpr ⟨?_, hz₂⟩, ?_⟩
    · intro heq; rw [heq] at h; omega
    · rw [det_sub_left]; omega

/-- **The headline.**  Instantiated against `exists_corner_shear` itself: its vertex `a` comes
with a genuine witness for `hδ`, positive orientation. -/
theorem exists_corner_shear_hδ_pos
    {S : Finset (ℤ × ℤ)} (hS : S.Nonempty) {u' vl : ℤ × ℤ}
    (hdet : det u' vl = 1) (hnc : ∃ z₁ ∈ S, ∃ z₂ ∈ S, det z₁ vl ≠ det z₂ vl) :
    ∃ K : ℤ, ∃ a ∈ S, ∃ z ∈ S.erase a, 0 < det (z - a) vl := by
  obtain ⟨K, a, ha, hmin⟩ := exists_corner_shear_a_isMin_uCoordZero hS (u' := u') (vl := vl)
  exact ⟨K, a, ha, exists_hδ_of_corner_shear_pos hmin hdet hnc⟩

/-- Mirror of `exists_corner_shear_hδ_pos` at `det u' vl = -1`. -/
theorem exists_corner_shear_hδ_neg
    {S : Finset (ℤ × ℤ)} (hS : S.Nonempty) {u' vl : ℤ × ℤ}
    (hdet : det u' vl = -1) (hnc : ∃ z₁ ∈ S, ∃ z₂ ∈ S, det z₁ vl ≠ det z₂ vl) :
    ∃ K : ℤ, ∃ a ∈ S, ∃ z ∈ S.erase a, det (z - a) vl < 0 := by
  obtain ⟨K, a, ha, hmin⟩ := exists_corner_shear_a_isMin_uCoordZero hS (u' := u') (vl := vl)
  exact ⟨K, a, ha, exists_hδ_of_corner_shear_neg hmin hdet hnc⟩

section AxiomReceiptsTask5

#print axioms exists_hδ_of_corner_shear_pos
#print axioms exists_hδ_of_corner_shear_neg
#print axioms exists_corner_shear_hδ_pos
#print axioms exists_corner_shear_hδ_neg

end AxiomReceiptsTask5

/-! ## Task 6 (team-lead, 2026-09-20): is §18 confined to a half-strip too?

Team-lead's fold-in question: `not_bddAbove_det_seed_of_hwin_hK` needs `hδ` **and** a `D` that is
actually `det·vl`-unbounded to escape the impossibility; `bddAbove_det_halfStrip`/
`bddBelow_det_halfStrip` already show `halfStrip B vl` (finite `B`) is bounded.  If every `D` the
tree can concretely produce is shaped like a half-strip, §18 is confined the same way the corner
route was, independent of `hδ`.

**Scan result: yes, confined.**  There are exactly two tree-wide producers of an `hD`-shaped
hypothesis:

- `L1Line0.exists_hD_of_case1` (`:527`), whose conclusion is literally
  `∀ z ∈ halfStrip B vl, …` with `EnvOf (S:Set) B` supplying `B.Finite`
  (`HbaseFlatSeed.finite_of_envOf_Sphi`) — this is the one every live call site in
  `L1SweepBridge.lean` uses (`:148,269,366,665,879`, all `D := halfStrip B vl`, per that file's
  own §1 table at `:48`).
- `HbaseBridge.hD_of_halfStrip` (`:277`), whose conclusion is
  `∀ z ∈ halfStripFrom Bf vl t₁, …` with `Bf : Finset (ℤ × ℤ)` — a second half-strip shape, along
  `vl`, over a finite base.

No other producer exists (grepped for `hD :` binder discharges tree-wide; every occurrence
terminates at one of these two, or is itself one of these two).

**Both shapes are `det·vl`-bounded, and for the same reason: `det (g + t•vl) vl = det g vl`**
(`det vl vl = 0`, so the `vl`-translate doesn't move the level at all, not merely "stays
bounded") **— bounded by the finite base's extreme, exactly like `halfStrip`.**
`bddAbove_det_halfStripFrom`/`bddBelow_det_halfStrip From` below prove this for the second shape
(stated against the literal set-builder from `Colle43.halfStripFrom:388`, not against the name
itself — no new import taken, per blindspot 1b: I checked `Claim43.lean` is not on this file's
current transitive import path and did not add the edge).

**Conclusion, stated plainly as asked: yes — §18 is half-strip-confined too, for exactly the same
underlying reason as the corner route (`bddAbove/bddBelow_det_halfStrip`), and `hδ` is not the
missing ingredient that would save it — Task 5 already showed `hδ` is available whenever `hnc`
holds. So both L1 routes die at the same finite-base half-strip fact.** This is not new
mathematics discovered here; it is the same boundedness `§17`/`§18` already proved, now checked
against the *complete* census of what `D` can ever concretely be, rather than against `halfStrip`
alone. A route that escapes this needs a genuinely new `hD`-producer — not shaped like a
`vl`-directed strip over a finite base — which is a search-for-new-mathematics task, not a proof
gap in what is already written.

Reading limit: this is about the two shapes producible *today*; it is not a proof that no such
`hD` can ever exist, and it says nothing about leaf A (§15/`OPEN.md #15` retraction stands,
not reopened here). `sorry` 2, `axiom_closure` unchanged. -/

theorem det_add_zsmul_self (p w : ℤ × ℤ) (t : ℤ) : det (p + t • w) w = det p w := by
  simp only [det, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- The `halfStripFrom`-shaped seed (`Colle43.halfStripFrom B vl t₁ = {g + t•vl : g ∈ B,
t₁ ≤ t}`, stated here against its literal definition, not its name) is `det·vl`-bounded above
whenever the base `B` is nonempty. -/
theorem bddAbove_det_halfStripFrom
    {B : Finset (ℤ × ℤ)} (hBne : B.Nonempty) (vl : ℤ × ℤ) (t₁ : ℤ) :
    ∃ M : ℤ, ∀ z ∈ {z : ℤ × ℤ | ∃ g ∈ B, ∃ t : ℤ, t₁ ≤ t ∧ z = g + t • vl}, det z vl ≤ M := by
  obtain ⟨g0, hg0, hmax⟩ := B.exists_max_image (fun g => det g vl) hBne
  refine ⟨det g0 vl, fun z hz => ?_⟩
  obtain ⟨g, hg, t, _, rfl⟩ := hz
  rw [det_add_zsmul_self]
  exact hmax g hg

/-- Mirror of `bddAbove_det_halfStripFrom`. -/
theorem bddBelow_det_halfStripFrom
    {B : Finset (ℤ × ℤ)} (hBne : B.Nonempty) (vl : ℤ × ℤ) (t₁ : ℤ) :
    ∃ M : ℤ, ∀ z ∈ {z : ℤ × ℤ | ∃ g ∈ B, ∃ t : ℤ, t₁ ≤ t ∧ z = g + t • vl}, M ≤ det z vl := by
  obtain ⟨g0, hg0, hmin⟩ := B.exists_min_image (fun g => det g vl) hBne
  refine ⟨det g0 vl, fun z hz => ?_⟩
  obtain ⟨g, hg, t, _, rfl⟩ := hz
  rw [det_add_zsmul_self]
  exact hmin g hg

section AxiomReceiptsTask6

#print axioms det_add_zsmul_self
#print axioms bddAbove_det_halfStripFrom
#print axioms bddBelow_det_halfStripFrom

end AxiomReceiptsTask6

/-! ## Task 7 (team-lead, 2026-09-20): does `exists_shear_hlt_and_doubly_lower`'s `a` land at the
right `det·vl` extreme?

**Answer: right extreme** (unlike `exists_corner_shear`, Task 4) — `dot (expNormal vl u') z
= det u' vl * det z vl` unconditionally, so under `hdet : det u' vl = 1` the source proof's
internal `hBmax` step (`HbaseBridge.lean:2059-2073`, not exported by the theorem's stated
conclusion) translates verbatim into `∀ z ∈ S, det z vl ≤ det a vl` — exactly
`detMax_of_hwin_hK`'s shape.

**Dedup (team-lead, 2026-09-20): the reproduction landed here has been deleted.** Team-lead
flagged the `mem_derivedQ_iff` trap (`NOTATION.md`) — this file already has `HbaseBridge` in its
transitive closure, so `dot_expNormal_swap_eq_det` / `exists_shear_hlt_and_doubly_lower_detMax`
existing in two namespaces at once was a live `Ambiguous term` risk for any future file opening
both, plus a second copy of the proof body to drift. The single kept copy is
`Nivat.HbaseBridge.dot_expNormal_swap_eq_det` / `Nivat.HbaseBridge.exists_shear_hlt_and_doubly_lower_detMax`,
landed beside the theorem it mirrors (`HbaseBridge.lean`, right after `exists_shear_hlt_and_doubly_lower`).
Confirmed via grep before deleting: zero consumers of the `MaxIndexProbe` copy anywhere in `Nivat/`. -/

end Nivat.ColleReg

section Receipts
/-! Standing `#print axioms` receipts.  Deletable as a block. -/

#print axioms Nivat.ColleReg.primitive_of_hunimod
#print axioms Nivat.ColleReg.exists_N₀
#print axioms Nivat.ColleReg.exists_N₀_hmin_hattain
#print axioms Nivat.ColleReg.exists_Sφ
#print axioms Nivat.ColleReg.cornerPointGapShear_holds
#print axioms Nivat.ColleReg.mem_chainFull_shear_iff
#print axioms Nivat.ColleReg.exists_N₀_hmin_hattain_shear
#print axioms Nivat.ColleReg.wiring_hline
#print axioms Nivat.ColleReg.wiring_hstraddle
#print axioms Nivat.ColleReg.levelMax_image_add
#print axioms Nivat.ColleReg.derivedQ_image_add
#print axioms Nivat.ColleReg.derivedQ_image_nonempty_iff
#print axioms Nivat.ColleReg.derivedQ_eq_empty_iff
#print axioms Nivat.ColleReg.derivedQ_eq_empty_iff_const
#print axioms Nivat.ColleReg.inner2_neg_left
#print axioms Nivat.ColleReg.cutNormal_false_eq_neg_true
#print axioms Nivat.ColleReg.derivedQ_eq_empty_iff_true_false

end Receipts
