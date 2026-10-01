/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.L1SweepBridge
import Nivat.External.Colle.HbaseBridge

/-!
# Is `Nivat.L1SweepBridge.HwinHoleE` over-specified?

Lane Wbundle's file (exclusive).  Leaf L1's entire live content is
`Nivat.L1SweepBridge.HwinHoleE ξ S Sphi vl` (`L1SweepBridge.lean`, four-argument form,
`EnvOf (Sphi : Set (ℤ×ℤ)) B` inserted between `B.Finite` and `hamin`), the `sorry` at
`RegionSteps.lean:1129`.  Team-lead's three questions, in order, each answered with a
kernel-checked declaration.

⚠ **2026-09-19 23:5x update, against the corrected signature.**  The first version of this
file was written against a three-argument `HwinHoleE ξ S vl` that team-lead had already
retracted as *false* (the `i = j = 0` collapse: `{i' | i' < 0} = ∅`, so `hwin` there demands
one vector translate all of `S.erase a` into `halfStrip B vl`, and a singleton `B` — permitted
by `B.Finite` alone — makes that geometrically impossible).  `check1.sh`'s EXIT=0 on that
version was a **false green**: it read the pre-edit `olean`, not the corrected source
(tool blindspot #1, the "source newer than olean" direction).  Section §1 below is corrected
to the real four-argument signature; §4 is new, per team-lead's request, and is the most
valuable output of this file's second pass.  **No `sorry TOTAL` / `axiom_closure` change —
this file only narrows or fails to narrow what the one remaining `Prop` says, per hard rule 1.**

🔴 **2026-09-20 update: `HwinHoleE` itself is superseded by `L1SweepBridge.HwinHoleZ`.**
`HwinHoleE`'s two sets `S`/`Sphi` were never related in the source (Collé fixes Lemma 2.4's
`𝒮` as the generating set and indexes the chain by the zonotope `𝒮_φ`, and never identifies the
two — `RegionSteps.lean:2318-2332`, `DecompData.lean:113-124`), so Hflat refuted `HwinHoleE` with
`Sphi := B := {(0,0)}` against an unrelated three-point `S`.  `HwinHoleZ ξ Sw vl` (§15 of
`L1SweepBridge.lean`) deletes the seam by using **one** set `Sw` (the window, the minimality
direction and the enveloped base) instead of two — it is what `RegionSteps.exists_wedgeResidualR`
now calls.  §1 and §4 below are retargeted at `HwinHoleZ`; `HwinHoleE`-facing code is dropped
rather than kept dead, since team-lead's file already carries the retraction docstring on
`HwinHoleE` itself.  `ofSweepEnumAt` (§3) is updated for `ofSweepEnum`'s own `S`/`Sw` split
(sweep window `Sw` vs. conclusion index `S`, mechanical — `hbase_at_of_sweep_of_isGeneratingSet`
never related its generating set to `B`/`D`, so the split was free upstream too).
-/

set_option autoImplicit false

namespace Nivat.L1SweepBridge

open Nivat Nivat.LE2 Nivat.Colle Nivat.Colle41 Nivat.Colle43 Nivat.ColleReg

/-! ## §1  Q1 — is `∃ u'` genuinely outside `∀ B u c a K`?

**Answer: syntactically yes it can be pushed in (sound), but the resulting statement is
degenerate, not a usable weakening — and Lstrad's independent check confirms the `u'`-then-`K`
order is not exploitable, so treat this as answered negatively.**  The inner `∀` (of `HwinHoleE`,
and identically of its replacement `HwinHoleZ`) has `hamin` (the "`a` is the `(u' - K•vl)`-argmin
of the set" fact) as a *hypothesis* of an implication, not a goal.  Pushing `∃ u'` in past that
hypothesis lets a would-be prover pick, **for each tuple separately**, a `u'` that makes `hamin`
*false* and discharge the implication vacuously — without touching `hwin`/`hK` at all.  That is
the general shape `(∃ x, ∀ y, P → Q) → ∀ y, (∃ x, P → Q)`, whose right side is provable the
moment `¬P` is findable for some `x`, regardless of `Q`.  **Restated as the general trap, since
it recurs: pushing an `∃` inward past a hypothesis of an implication is not a weakening of the
content, it is an invitation to vacuity — the two must not be conflated as "we weakened it".**
`hwinHoleU_of_hwinHoleZ` below is the sound direction (so the pushed-in form genuinely is
implied, i.e. (a) sound, (b) formally weaker); the vacuity paragraph is why it is **not**
recommended as the next thing to attack — flagged in the docstring, not asserted as a kernel
fact per `PROTOCOL.md` §15.  Lstrad independently checked the exploitability question via
`dot_expNormal_shear`/`exists_corner_shear`: for any fixed `u'`, `K` can walk the argmin through
every vertex of `conv S`, so the per-tuple freedom a pushed-in `u'` would buy is not new — `K`
already has it.  Two independent routes, same verdict: **`HwinHoleU` is not worth pursuing.**

🔴 **2026-09-20: re-checked against `HwinHoleZ` specifically — `EnvOf` does not close the
escape, and this is a structural fact, not a new computation.**  The vacuity mechanism only
needs `u'` and `K` (via `hamin`, a condition purely on directions and the single point `a`
against `Sw`); it never touches `B` in any way.  `EnvOf (Sw : Set (ℤ×ℤ)) B` is a *separate*
hypothesis of the same implication, constraining `B` relative to `Sw` — it says nothing about
which `u'`/`K` make `a` fail to be the `(u' - K•vl)`-argmin of `Sw`.  Since the escape's
falsifying choice of `u'` never has to interact with `B` or `hEnv` at all (it is chosen, then
the implication's hypotheses — including `hEnv` — are never reached because `hamin` already
fails), strengthening `HwinHoleE`'s `B`-side binder into `HwinHoleZ`'s single-set form changes
nothing about the escape's availability.  **`HwinHoleU` stays parked**; the retarget below
(`HwinHoleZ` instead of the now-dead `HwinHoleE`) is bookkeeping, not a new attempt to dispatch
it. -/

/-- `HwinHoleZ` with `u'` chosen after `a` and `K` rather than before all five.  Same content
at a fixed tuple (`enum` still existentially quantified inside, as in `HwinHoleZ`), syntactically
weaker as a whole `Prop` (`hwinHoleU_of_hwinHoleZ`).  **Not recommended as a dispatch target —
see the §1 docstring: this is the vacuity-risk direction, confirmed unexploitable by Lstrad via
an independent route, and confirmed still unexploitable-in-the-good-sense (i.e. `EnvOf` does not
close it either) after the `HwinHoleE → HwinHoleZ` retarget.** -/
def HwinHoleU (ξ : Config ℤ) (Sw : Finset (ℤ × ℤ)) (vl : ℤ × ℤ) : Prop :=
  ∀ (B : Set (ℤ × ℤ)) (u : ℤ × ℤ) (c : ℤ) (a : ℤ × ℤ) (K : ℤ),
    a ∈ Sw → Nivat.LatticeConvex (Sw.erase a) → 0 < c → B.Finite →
    EnvOf (Sw : Set (ℤ × ℤ)) B →
    ∃ u' : ℤ × ℤ, (det u' vl = 1 ∨ det u' vl = -1) ∧
      ((∀ b ∈ Sw, dot (expNormal (u' - K • vl) vl) a ≤ dot (expNormal (u' - K • vl) vl) b) →
       (∀ z ∈ halfStrip B vl, (T u ξ) z = T (c • vl) (T u ξ) z) →
        ∃ b₀ ∈ B, ∃ enum : ℕ → ℕ → ℤ × ℤ,
          (∀ i j : ℕ, ∀ z ∈ Sw.erase a,
            z + (enum i j - a) ∈
              halfStrip B vl ∪ (⋃ i' ∈ {i' | i' < i}, Set.range (enum i')) ∪
                (enum i '' {j' | j' < j})) ∧
          chainFull B vl (u' - K • vl) b₀ 0 ⊆ halfStrip B vl ∪ (⋃ i, Set.range (enum i)))

/-- **Sound direction**: `HwinHoleZ` already supplies a single `u'` working for every tuple,
so it a fortiori supplies one per tuple.  Trivial — the point of landing it is that it is the
*only* direction that is actually true without further hypotheses (see the module docstring). -/
theorem hwinHoleU_of_hwinHoleZ {ξ : Config ℤ} {Sw : Finset (ℤ × ℤ)} {vl : ℤ × ℤ}
    (h : HwinHoleZ ξ Sw vl) : HwinHoleU ξ Sw vl := by
  obtain ⟨u', hu, h⟩ := h
  intro B u c a K ha hconvS hc hBfin hEnv
  exact ⟨u', hu, h B u c a K ha hconvS hc hBfin hEnv⟩

/-! ## §2  Q2 — is `hK` separable from `hwin`?

**Answer: no, and the obstruction is already on the tree with a kernel witness — pin it down
as one packaged theorem so it does not have to be re-found.**  `hK` is *free* for `coverEnum`
at any `hunimod`, `B`, `D` whatsoever (`Nivat.ColleReg.hK_of_coverEnum`, `L1CoverWedge.lean:432`
— pure set algebra, `coverEnum`'s row union literally equals the half-plane).  But `coverEnum`
**cannot** satisfy `hwin` the moment `S.erase a` has a point at a different level from `a`
(`Nivat.HbaseBridge.not_hwin_coverEnum_halfStrip`, `HbaseBridge.lean:471`, itself an instance
of `not_hwin_of_row_ray_halfStrip`, `:423`: row `0` of `coverEnum` is a `u'`-ray, so it can only
ever meet one level line, and `hwin` demands it absorb a point at a different level).  So the
enum that makes `hK` trivial is a *provable counterexample* to `hwin`; whoever builds an `enum`
solving `hwin` (`L1CoverWedge.lean:441`: "`enum` is L3win's to build") gets **no discount** on
`hK` from that fact — `hK_of_rows_cover_diff` (`L1CoverWedge.lean:466`) shows `hK`'s content is
literally different data (`chainFull … k \ D ⊆ ⋃ i, range (enum i)`, a covering statement with
no ordering content), so satisfying `hwin`'s ordering constraint does not discharge it for free
either.  Both walls are real; `HbaseBridge.hbase_at_of_sweep_of_isGeneratingSet`'s conjunction
is strictly harder than either conjunct alone, demonstrated by exhibiting one enum satisfying
one wall and providably failing the other.

⚠ **Binder-list check against Hflat's `not_hwin_seed`/`not_hwin_seed_forall`
(`HbaseFlatSeed.lean:966,1007`), since the two converge in spirit but are not the same fact.**
Hflat's refutation is at the fixed indices `i = j = 0` (where `{i' | i' < 0} = {j' | j' < 0} = ∅`
collapses `hwin` to "one vector translates all of `S.erase a`"), is **enum-independent**
(`not_hwin_seed_forall` quantifies over an arbitrary `enum`), but is pinned to one concrete
`S = {(0,0),(1,0),(2,0)}`, `a = (0,0)`, `B = {(0,0)}`, `vl = (0,1)`.  `coverEnum_hK_and_not_hwin`
below is the opposite trade: **`coverEnum`-specific** (via
`not_hwin_of_row_ray_halfStrip`'s ray argument over row `0`'s *entire* range, not just `j = 0`),
but general in `S`, `B`, `a` (any level-differing pair suffices).  Neither subsumes the other;
they are independent witnesses of the same wall. -/

open Nivat.HbaseBridge in
/-- **The separation, as one theorem.**  For `enum := coverEnum vl u' b₀`: `hK` holds
unconditionally, `hwin` fails the moment `S.erase a` is not entirely at `a`'s level. Both
conjuncts cite pre-existing, `#print axioms`-clean declarations; nothing here is new geometry. -/
theorem coverEnum_hK_and_not_hwin
    {S : Finset (ℤ × ℤ)} {a : ℤ × ℤ} {Bf : Finset (ℤ × ℤ)} {vl u' b₀ : ℤ × ℤ} {t₁ : ℤ}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    {z₀ : ℤ × ℤ} (hz₀ : z₀ ∈ S.erase a)
    (hδ : dot (expNormal u' vl) z₀ ≠ dot (expNormal u' vl) a) :
    (chainFull (Bf : Set (ℤ × ℤ)) vl u' b₀ 0 ⊆
        halfStripFrom Bf vl t₁ ∪ (⋃ i, Set.range (coverEnum vl u' b₀ i))) ∧
    ¬ (∀ i j : ℕ, ∀ z ∈ S.erase a,
        z + (coverEnum vl u' b₀ i j - a) ∈
          halfStripFrom Bf vl t₁
            ∪ (⋃ i' ∈ {i' | i' < i}, Set.range (coverEnum vl u' b₀ i'))
            ∪ (coverEnum vl u' b₀ i '' {j' | j' < j})) :=
  ⟨Nivat.ColleReg.hK_of_coverEnum hunimod, not_hwin_coverEnum_halfStrip hunimod hz₀ hδ⟩

/-! ## §4  Team-lead's follow-up — is splitting the shared `∃ enum` a strict weakening?

`HwinHoleZ`'s inner content is `∃ b₀ ∈ B, ∃ enum, hwin(enum) ∧ hK(b₀, enum)`, one `enum` forced
to satisfy both conjuncts.  Team-lead's question: is
`(∃ enum, hwin(enum)) ∧ (∃ b₀ ∈ B, ∃ enum, hK(b₀, enum))` — same content, `enum` no longer
shared — a *strict* weakening?  (Retargeted 2026-09-20 from the now-superseded `HwinHoleE`;
the argument is unchanged since it never used the `S`-vs-`Sphi` split `HwinHoleZ` deleted.)

**Two things proved, one left open, stated precisely rather than hand-waved.**

1. **The split is sound** (`hwinHoleSplit_of_hwinHoleZ` below) — trivial, generic fact: a
   shared witness satisfies each conjunct separately.
2. **The `hK`-half is discharged unconditionally once split off**
   (`exists_hK_of_nonempty` below): `coverEnum` satisfies `hK` for *any* `D` including
   `halfStrip B vl` (`hK_of_coverEnum`, no dependence on `hwin` or on `Sw` at all), so as soon as
   `B` is nonempty and `hunimod` holds, the second conjunct of the split holds **regardless of
   whether `hwin` is satisfiable by anything**.  Consequence: *after* splitting, the entire
   remaining content of `HwinHoleZ`'s inner existential collapses to the single question
   `∃ enum, hwin(enum)` — `hK` contributes nothing once it is no longer forced to share `enum`
   with `hwin`.  This is a real reduction, not bookkeeping: it says the joint form's difficulty
   is entirely the sharing, not `hK` itself (consistent with §2 — `hK` is free for `coverEnum`).
   §5 sharpens this further: `hK` is free even *without* `coverEnum`, by an all-finite-row `enum`.
3. **Strictness itself (∃ split-witnesses with no joint witness) is NOT established here.**
   Proving it needs one concrete instance where `∃ enum, hwin(enum)` holds for *some* enum other
   than `coverEnum` while *no* enum satisfies `hwin(enum) ∧ hK(b₀, enum)` for any `b₀ ∈ B` —
   i.e. every `hwin`-witness must be shown to fail `hK` at every `b₀`.  §2's
   `coverEnum_hK_and_not_hwin` does not supply this: it shows `coverEnum` fails `hwin` in the
   level-differing case, not that *every* `hwin`-witness fails `hK`.  Flagging as open rather
   than asserting; the missing piece is exactly a lower bound on `hK`-violation ranging over
   *all* `hwin`-satisfying enums, which is not on the tree anywhere I can find (checked via
   `grep -rn hK_of_ Nivat/External/Colle/*.lean` — only `coverEnum`-sourced `hK` producers
   exist; no `hwin → ¬hK` implication is landed). -/

/-- The split form of `HwinHoleZ`'s inner existential: `enum` no longer shared between `hwin`
and `hK`. -/
def HwinHoleSplit (ξ : Config ℤ) (Sw : Finset (ℤ × ℤ)) (vl : ℤ × ℤ) : Prop :=
  ∃ u' : ℤ × ℤ, (det u' vl = 1 ∨ det u' vl = -1) ∧
    ∀ (B : Set (ℤ × ℤ)) (u : ℤ × ℤ) (c : ℤ) (a : ℤ × ℤ) (K : ℤ),
      a ∈ Sw → Nivat.LatticeConvex (Sw.erase a) → 0 < c →
      B.Finite → EnvOf (Sw : Set (ℤ × ℤ)) B →
      (∀ b ∈ Sw, dot (expNormal (u' - K • vl) vl) a ≤ dot (expNormal (u' - K • vl) vl) b) →
      (∀ z ∈ halfStrip B vl, (T u ξ) z = T (c • vl) (T u ξ) z) →
      (∃ enum : ℕ → ℕ → ℤ × ℤ,
        ∀ i j : ℕ, ∀ z ∈ Sw.erase a,
          z + (enum i j - a) ∈
            halfStrip B vl ∪ (⋃ i' ∈ {i' | i' < i}, Set.range (enum i')) ∪
              (enum i '' {j' | j' < j})) ∧
      (∃ b₀ ∈ B, ∃ enum : ℕ → ℕ → ℤ × ℤ,
        chainFull B vl (u' - K • vl) b₀ 0 ⊆ halfStrip B vl ∪ (⋃ i, Set.range (enum i)))

/-- **Point 1, soundness.**  Generic: a shared witness satisfies each half separately. -/
theorem hwinHoleSplit_of_hwinHoleZ {ξ : Config ℤ} {Sw : Finset (ℤ × ℤ)} {vl : ℤ × ℤ}
    (h : HwinHoleZ ξ Sw vl) : HwinHoleSplit ξ Sw vl := by
  obtain ⟨u', hu, h⟩ := h
  refine ⟨u', hu, fun B u c a K ha hconvS hc hBfin hEnv hamin hD => ?_⟩
  obtain ⟨b₀, hb₀, enum, hwin, hK⟩ := h B u c a K ha hconvS hc hBfin hEnv hamin hD
  exact ⟨⟨enum, hwin⟩, b₀, hb₀, enum, hK⟩

/-- **Point 2, the `hK`-half is free.**  Once `enum` is not forced to also satisfy `hwin`,
`coverEnum` discharges `hK` unconditionally — no dependence on `S`, `a`, `D`'s content, or
`hwin`'s satisfiability at all. -/
theorem exists_hK_of_nonempty {B : Set (ℤ × ℤ)} {vl u' : ℤ × ℤ}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) {b₀ : ℤ × ℤ} (hb₀ : b₀ ∈ B)
    (D : Set (ℤ × ℤ)) :
    ∃ b₀ ∈ B, ∃ enum : ℕ → ℕ → ℤ × ℤ,
      chainFull B vl u' b₀ 0 ⊆ D ∪ (⋃ i, Set.range (enum i)) :=
  ⟨b₀, hb₀, coverEnum vl u' b₀, Nivat.ColleReg.hK_of_coverEnum hunimod⟩

/-! ## §3  Q3 — is `k := 0` load-bearing in `ofSweepEnum`?

**Answer: no.  Every field `ofSweepEnum` builds is already `k`-generic upstream; `k := 0` is a
choice made only inside `ofSweepEnum` itself, not a constraint from `WedgeResidualR` or from
`HbaseBridge.hbase_at_of_sweep_of_isGeneratingSet`.** Evidence, read off the actual signatures,
not guessed from names (`PROTOCOL.md` §23):

* `WedgeResidualR`'s own `hline`/`hstraddle`/`hbase` fields are stated at `chainFull … (k + N)`
  for the struct's *own* field `k` (`L1Claim.lean:928`) — nothing pins `k` to `0`.
* `Nivat.HbaseBridge.hbase_at_of_sweep_of_isGeneratingSet` (`HbaseBridge.lean:185`) already
  takes `k : ℕ` as an ordinary parameter and concludes `PeriodOn … (chainFull B vl u' b₀ k) …`
  — the exact shape `hbase` needs at the struct's own `k`, no shift.
* `L1Claim.exists_L1MaxBResidual_of_convex_split` (`L1Claim.lean:819`) and everything it feeds
  (`ofWedgeAtConvex`, `L1Claim.lean:819`) are already stated for an arbitrary `k : ℕ`
  (`ofWedgeAtConvex_R : (ofWedgeAtConvex … k …).R n = chainFull B vl u' b₀ (k + n)`, read
  directly, not `k = 0` specialised).

So `ofSweepEnum`'s `k := 0` and its `Nat.zero_add` rewrites (`L1Claim.lean:1064`, body) are
purely local bookkeeping that a general `k` removes without any adaptation — no `simp only
[Nat.zero_add]` needed at all, because `hline`/`hstraddle` are handed to the struct in exactly
the `k + N` shape it wants.  `ofSweepEnumAt` below is `ofSweepEnum` generalised to a free `k`,
compiled against the real struct and the real `hbase` producer. -/

/-- `L1Claim.WedgeResidualR.ofSweep` / `L1SweepBridge.ofSweepEnum` with the base index `k`
free, not hard-set to `0`.  Answers Q3 constructively: `k ≠ 0` is admissible.

🔴 **2026-09-20: updated for `ofSweepEnum`'s own `S`/`Sw` split** (sweep window `Sw`, generating
set `hSwgen : IsGeneratingSet ξ Sw`, `hwin`/`hK` over `Sw.erase a`; conclusion still indexed by
`S`, and `hline`/`hstraddle` still range over `S.image (· + v)`, unchanged).  The split was free
upstream (`HbaseBridge.hbase_at_of_sweep_of_isGeneratingSet:185` never relates its generating set
to `B` or `D`), so the only change here is mechanical: `hSgen`/`S.erase a` become
`hSwgen`/`Sw.erase a` wherever the sweep (not the conclusion) is at stake. -/
noncomputable def ofSweepEnumAt
    {ξ : Config ℤ} {S Sw : Finset (ℤ × ℤ)} {vl : ℤ × ℤ}
    (hSwgen : IsGeneratingSet ξ Sw)
    {e u' v b₀ : ℤ × ℤ} {c : ℤ} (ε : Bool) {B : Set (ℤ × ℤ)}
    (hb₀ : b₀ ∈ B) (hconv : IsLatticeConvexRegion (wedgeFull B vl u'))
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) (c0 : c ≠ 0) (k : ℕ)
    {a : ℤ × ℤ} (ha : a ∈ Sw) (hconvS : Nivat.LatticeConvex (Sw.erase a))
    {D : Set (ℤ × ℤ)} (hD : ∀ z ∈ D, (T e ξ) z = T (c • vl) (T e ξ) z)
    (enum : ℕ → ℕ → ℤ × ℤ)
    (hwin : ∀ i j : ℕ, ∀ z ∈ Sw.erase a,
      z + (enum i j - a) ∈
        D ∪ (⋃ i' ∈ {i' | i' < i}, Set.range (enum i')) ∪ (enum i '' {j' | j' < j}))
    (hK : chainFull B vl u' b₀ k ⊆ D ∪ (⋃ i, Set.range (enum i)))
    (hline : ∀ N : ℕ, PeriodOn (T e ξ) (chainFull B vl u' b₀ (k + N)) (c • vl) →
      ¬ PeriodOn (T e ξ) (chainFull B vl u' b₀ (k + (N + 1))) (c • vl) →
      ∃ τ : ℤ, ∀ z ∈ L1Data.derivedQ ε u' (S.image (· + v)),
        τ • u' + z ∈ chainFull B vl u' b₀ (k + N) ∧
        τ • u' + z + c • vl ∈ chainFull B vl u' b₀ (k + N))
    (hstraddle : ∀ N : ℕ, PeriodOn (T e ξ) (chainFull B vl u' b₀ (k + N)) (c • vl) →
      ¬ PeriodOn (T e ξ) (chainFull B vl u' b₀ (k + (N + 1))) (c • vl) →
      ∀ τ : ℤ,
        (∀ z ∈ L1Data.derivedQ ε u' (S.image (· + v)),
          τ • u' + z ∈ chainFull B vl u' b₀ (k + N) ∧
          τ • u' + z + c • vl ∈ chainFull B vl u' b₀ (k + N)) →
        Nivat.L1Region.Straddle (T e ξ) (chainFull B vl u' b₀ (k + N))
          (chainFull B vl u' b₀ (k + (N + 1))) (S.image (· + v))
          (L1Data.derivedQ ε u' (S.image (· + v))) vl u' c τ) :
    L1Claim.WedgeResidualR ξ S vl where
  e := e
  u' := u'
  v := v
  b₀ := b₀
  c := c
  ε := ε
  B := B
  k := k
  hb₀ := hb₀
  hunimod := hunimod
  c0 := c0
  hconv := hconv
  hbase :=
    Nivat.HbaseBridge.hbase_at_of_sweep_of_isGeneratingSet hSwgen ha hconvS k hD enum hwin hK
  hline := hline
  hstraddle := hstraddle

/-! ## §5  Team-lead's question — does `hK` force some row infinite?

**Answer: no — `hK` alone is far too weak to force that.**  `hK : chainFull B vl u' b₀ 0 ⊆
D ∪ ⋃ i, Set.range (enum i)` is a pure covering condition against a target that is a subset of
the *countable* set `ℤ × ℤ`.  It does not care how the covering is distributed across rows
`i : ℕ`.  Enumerate `ℤ × ℤ` by a bijection `e : ℕ ≃ ℤ × ℤ` (`Denumerable.eqv (ℤ × ℤ)`, the same
instance `L1CoverWedge.pairEnum` draws on for `(ℤ × ℤ) × ℕ`) and set row `i` to the *constant*
function `j ↦ e i`.  Every single row then has a **singleton** — in particular finite — range,
and the union over all rows is already `Set.range e = Set.univ`, which contains `chainFull …`
regardless of what `B`, `u'`, `vl`, `b₀`, `D` are.  `exists_hK_of_finiteRows` below is exactly
this witness: it answers the second branch of the either/or team-lead posed — **`hK` has a
stated escape route with every row finite (indeed a singleton), so per team-lead's own framing
that is where `enum` should be built.**

This does **not** reopen `hwin`, and is not offered as a candidate `enum` for `HwinHoleE`'s
inner existential: `§14`'s obstruction (`not_hwin_of_row_zero_levelConst` /
`not_hwin_of_row_zero_levelConst_envOf`, cited here, not restated) is a necessary condition on
row `0` once `hwin` is *also* demanded of the same `enum`, and a constant row is certainly
level-constant in the sense `§14` needs — so this witness's row `0` is exactly the shape `§14`
rules out **if** `hwin` is asked of it too (it is finite, so `§14` does not directly apply, but
`hwin` itself fails for a constant row the instant `S.erase a` has more than one point reachable
from `a` at different offsets, since a single value `enum 0 0` cannot translate two different
`z, z'` into two different required positions simultaneously unless the target sets absorb the
difference — not investigated here, out of scope for the question asked).  The witness below
answers **only** "can `hK` alone be met by an all-finite-row `enum`", which is exactly what was
asked; it says nothing about `hwin`, and is not claimed to. -/

/-- **The escape-route witness.**  Every row has singleton (hence finite) range, and `hK` holds
unconditionally — for any `B`, `u'`, `vl`, `b₀`, `D` whatsoever, since the union of all rows is
already all of `ℤ × ℤ`.  Answers team-lead's question: `hK` does **not** force any row infinite. -/
theorem exists_hK_of_finiteRows (B : Set (ℤ × ℤ)) (vl u' b₀ : ℤ × ℤ) (D : Set (ℤ × ℤ)) :
    ∃ enum : ℕ → ℕ → ℤ × ℤ, (∀ i : ℕ, (Set.range (enum i)).Finite) ∧
      chainFull B vl u' b₀ 0 ⊆ D ∪ (⋃ i, Set.range (enum i)) := by
  classical
  set e : ℕ ≃ (ℤ × ℤ) := (Denumerable.eqv (ℤ × ℤ)).symm with he
  refine ⟨fun i _ => e i, fun i => ?_, fun z _ => ?_⟩
  · rw [Set.range_const]
    exact Set.finite_singleton _
  · right
    rw [Set.mem_iUnion]
    refine ⟨e.symm z, ?_⟩
    rw [Set.range_const]
    simp

/-! ## §6  Team-lead's follow-up — is `HwinHoleSplit` satisfiable, and is the sharing
load-bearing?

`L1SweepBridge.lean` §16–§17 (team-lead) show: `hwin ∧ hK` on a **shared** `enum` forces
`det · vl` bounded on the whole enumeration (§16), and `chainFull`'s own `u'`-ray blows that
bound whenever `det u' vl = 1` (`false_of_hwin_hK_of_det_pos`) or `= -1`
(`false_of_hwin_hK_of_det_neg`) — pure set theory, no `ξ`, no `IsMinimalCounterexample`.
Splitting `enum` (§4's `HwinHoleSplit`) removes the *sharing*, and `hK`'s half is free once
unshared (`exists_hK_of_nonempty` / `exists_hK_of_finiteRows`).  Two things proved below,
both compiled, no `sorry`.

1. **General reduction** (`hwinHoleSplit_of_forall_hwin`): `HwinHoleSplit` follows from bare
   `hwin`-satisfiability alone, for the *whole* universally-quantified statement (not one
   tuple) — `hK` costs nothing.  This makes §4 point 2 a theorem rather than prose.  Genuinely
   discharging `HwinHoleSplit` in full still requires supplying that `hwin`-satisfiability
   hypothesis, which is the sweep-construction question flagged in §2's docstring as "`enum` is
   L3win's to build" — **not solved here**, only reduced to.

2. **A genuine, non-degenerate instance, sign checked explicitly**
   (`hwinSplit_conclusion_at_example` / `not_shared_at_example`).  Data:
   `vl := (0,1)`, `u' := (1,0)`, `Sw := {(1,0),(2,0)}`, `a := (1,0)`, `K := 0`,
   `B := (↑Sw : Set (ℤ × ℤ))`.  **`a` is the `det · vl`-minimum of `Sw`**
   (`det (1,0) vl = 1 ≤ det (2,0) vl = 2`) and **`det u' vl = 1`** — the positive sign, exactly
   the case `false_of_hwin_hK_of_det_pos` refutes.  This is deliberately *not* the degenerate
   dodge (`B ⊋ Sw` chosen to make `hwin` vacuous, or `Sw.erase a = ∅`): `Sw.erase a = {(2,0)}`
   is a genuine second point, and `LatticeConvex Sw` is the already-landed
   `MaxIndexProbe.latticeConvex_pair_S017` (reused verbatim, not reproved).  At this tuple:
   * `hwin` **has** a witness (`enum ≡ a`, landing directly in `B` since `B = ↑Sw ⊇ Sw.erase a`
     — `(2,0) ∈ B` at `t := 0`), combined with `exists_hK_of_finiteRows`'s independent enum this
     witnesses `HwinHoleSplit`'s inner conjunction at this exact tuple.
   * **No enum can satisfy `hwin ∧ hK` on the *same* `enum`** at this same tuple — a direct,
     `enum`-independent corollary of `false_of_hwin_hK_of_det_pos`.
   So at this tuple the split is not a convenience, it is *necessary*: the shared form is
   uniformly false, the split form is true.  ⚠ This is one instance of `HwinHoleSplit`'s `∀ B u c
   a K`, not the full statement — `B := ↑Sw` is a choice available at *this* tuple because `Sw`
   itself happens to be lattice-convex, not a general recipe for arbitrary `B` satisfying
   `EnvOf Sw B`. -/

/-- **The reduction.**  `HwinHoleSplit` follows from bare `hwin`-satisfiability (over the same
`∀ B u c a K` binder list) plus nonemptiness of any admissible `B` — `hK` is discharged for free
by `exists_hK_of_nonempty`, independent of `hwin`, `a`, `D`'s content, or the enum `hwin` used. -/
theorem hwinHoleSplit_of_forall_hwin {ξ : Config ℤ} {Sw : Finset (ℤ × ℤ)} {vl : ℤ × ℤ}
    {u' : ℤ × ℤ} (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hBne : ∀ B : Set (ℤ × ℤ), B.Finite → EnvOf (Sw : Set (ℤ × ℤ)) B → B.Nonempty)
    (hwin : ∀ (B : Set (ℤ × ℤ)) (u : ℤ × ℤ) (c : ℤ) (a : ℤ × ℤ) (K : ℤ),
      a ∈ Sw → Nivat.LatticeConvex (Sw.erase a) → 0 < c →
      B.Finite → EnvOf (Sw : Set (ℤ × ℤ)) B →
      (∀ b ∈ Sw, dot (expNormal (u' - K • vl) vl) a ≤ dot (expNormal (u' - K • vl) vl) b) →
      (∀ z ∈ halfStrip B vl, (T u ξ) z = T (c • vl) (T u ξ) z) →
      ∃ enum : ℕ → ℕ → ℤ × ℤ,
        ∀ i j : ℕ, ∀ z ∈ Sw.erase a,
          z + (enum i j - a) ∈
            halfStrip B vl ∪ (⋃ i' ∈ {i' | i' < i}, Set.range (enum i')) ∪
              (enum i '' {j' | j' < j})) :
    HwinHoleSplit ξ Sw vl := by
  refine ⟨u', hunimod, fun B u c a K ha hconvS hc hBfin hEnv hamin hD => ?_⟩
  refine ⟨hwin B u c a K ha hconvS hc hBfin hEnv hamin hD, ?_⟩
  obtain ⟨b₀, hb₀⟩ := hBne B hBfin hEnv
  obtain ⟨enum2, -, hK2⟩ := exists_hK_of_finiteRows B vl (u' - K • vl) b₀ (halfStrip B vl)
  exact ⟨b₀, hb₀, enum2, hK2⟩

/-- **`hwin` at the example tuple.**  `enum ≡ a` lands every translate directly in `B` (since
`B = ↑Sw ⊇ Sw.erase a`), never touching the `⋃ i' < i` / `enum i '' {j' < j}` branches at all. -/
theorem hwin_at_example :
    ∀ i j : ℕ, ∀ z ∈ ({((1:ℤ), (0:ℤ)), (2, 0)} : Finset (ℤ × ℤ)).erase (1, 0),
      z + ((fun _ _ : ℕ => ((1:ℤ), (0:ℤ))) i j - (1, 0)) ∈
        halfStrip (({((1:ℤ), (0:ℤ)), (2, 0)} : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) ((0:ℤ), (1:ℤ))
          ∪ (⋃ i' ∈ {i' | i' < i}, Set.range (fun _ : ℕ => ((1:ℤ), (0:ℤ))))
          ∪ ((fun _ : ℕ => ((1:ℤ), (0:ℤ))) '' {j' | j' < j}) := by
  intro i j z hz
  left; left
  have hz2 : z = (2, 0) := by
    fin_cases hz <;> rfl
  subst hz2
  exact ⟨(2, 0), by simp, 0, by simp⟩

/-- **The split's conclusion, at the example tuple.**  Combines `hwin_at_example` with
`exists_hK_of_finiteRows` on an *independent* enum. -/
theorem hwinSplit_conclusion_at_example :
    (∃ enum : ℕ → ℕ → ℤ × ℤ,
      ∀ i j : ℕ, ∀ z ∈ ({((1:ℤ), (0:ℤ)), (2, 0)} : Finset (ℤ × ℤ)).erase (1, 0),
        z + (enum i j - (1, 0)) ∈
          halfStrip (({((1:ℤ), (0:ℤ)), (2, 0)} : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) ((0:ℤ), (1:ℤ))
            ∪ (⋃ i' ∈ {i' | i' < i}, Set.range (enum i')) ∪ (enum i '' {j' | j' < j})) ∧
    (∃ b₀ ∈ (({((1:ℤ), (0:ℤ)), (2, 0)} : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)), ∃ enum : ℕ → ℕ → ℤ × ℤ,
      chainFull (({((1:ℤ), (0:ℤ)), (2, 0)} : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) ((0:ℤ), (1:ℤ))
          ((1:ℤ), (0:ℤ)) (1, 0) 0 ⊆
        halfStrip (({((1:ℤ), (0:ℤ)), (2, 0)} : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) ((0:ℤ), (1:ℤ))
          ∪ (⋃ i, Set.range (enum i))) :=
  ⟨⟨_, hwin_at_example⟩, by
    obtain ⟨enum2, -, hK2⟩ := exists_hK_of_finiteRows
      (({((1:ℤ), (0:ℤ)), (2, 0)} : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) ((0:ℤ), (1:ℤ))
      ((1:ℤ), (0:ℤ)) (1, 0)
      (halfStrip (({((1:ℤ), (0:ℤ)), (2, 0)} : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) ((0:ℤ), (1:ℤ)))
    exact ⟨(1, 0), by simp, enum2, hK2⟩⟩

/-- **No shared `enum` works at the example tuple** — `enum`-independent, a direct corollary of
`false_of_hwin_hK_of_det_pos`: `det ((1,0)) ((0,1)) = 1` (positive orientation), `B` finite,
`(1,0) ∈ B`, and `z := (2,0) ∈ Sw.erase a` has `det (z - a) vl = det (1,0) (0,1) = 1 > 0` — the
matching sign. -/
theorem not_shared_at_example (enum : ℕ → ℕ → ℤ × ℤ)
    (hwin : ∀ i j : ℕ, ∀ z ∈ ({((1:ℤ), (0:ℤ)), (2, 0)} : Finset (ℤ × ℤ)).erase (1, 0),
      z + (enum i j - (1, 0)) ∈
        halfStrip (({((1:ℤ), (0:ℤ)), (2, 0)} : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) ((0:ℤ), (1:ℤ))
          ∪ (⋃ i' ∈ {i' | i' < i}, Set.range (enum i')) ∪ (enum i '' {j' | j' < j}))
    (hK : chainFull (({((1:ℤ), (0:ℤ)), (2, 0)} : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) ((0:ℤ), (1:ℤ))
        ((1:ℤ), (0:ℤ)) (1, 0) 0 ⊆
      halfStrip (({((1:ℤ), (0:ℤ)), (2, 0)} : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) ((0:ℤ), (1:ℤ))
        ∪ (⋃ i, Set.range (enum i))) :
    False :=
  false_of_hwin_hK_of_det_pos
    (Sw := ({((1:ℤ), (0:ℤ)), (2, 0)} : Finset (ℤ × ℤ)))
    (a := (1, 0)) (B := (({((1:ℤ), (0:ℤ)), (2, 0)} : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)))
    (vl := ((0:ℤ), (1:ℤ))) (u' := ((1:ℤ), (0:ℤ))) (b₀ := (1, 0))
    (Finset.finite_toSet _)
    (show ((1:ℤ), (0:ℤ)) ∈ (({((1:ℤ), (0:ℤ)), (2, 0)} : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) by simp)
    (by decide) enum (z := (2, 0)) (by simp) (by decide) hwin hK

section AxiomReceipts
/-! Standing `#print axioms` receipts.  Deletable as a block. -/

#print axioms Nivat.L1SweepBridge.hwinHoleU_of_hwinHoleZ
#print axioms Nivat.L1SweepBridge.coverEnum_hK_and_not_hwin
#print axioms Nivat.L1SweepBridge.hwinHoleSplit_of_hwinHoleZ
#print axioms Nivat.L1SweepBridge.exists_hK_of_nonempty
#print axioms Nivat.L1SweepBridge.ofSweepEnumAt
#print axioms Nivat.L1SweepBridge.exists_hK_of_finiteRows
#print axioms Nivat.L1SweepBridge.hwinHoleSplit_of_forall_hwin
#print axioms Nivat.L1SweepBridge.hwin_at_example
#print axioms Nivat.L1SweepBridge.hwinSplit_conclusion_at_example
#print axioms Nivat.L1SweepBridge.not_shared_at_example

end AxiomReceipts

end Nivat.L1SweepBridge
