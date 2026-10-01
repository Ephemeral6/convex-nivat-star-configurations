/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.L1Data
import Nivat.External.Colle.L1Fields
import Nivat.External.Colle.L1Region
import Nivat.External.Colle.SweptSeed

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# `L1Data`'s conjuncts 14/15/16: what is free, what is not, and what already has a consumer

Three questions were posed about `L1Data` (`L1Data.lean:128-136`); this file answers all three
at the kernel, with no `sorry` and no project axiom.

## ⚠ Read first: conjunct 14 is **not** the thing called `hline` at the call site

`L1Data.hline` (`L1Data.lean:128`) is bound to the name **`hQR`** in the destructuring at
`RegionSteps.lean:1155-1157`, and the name **`hline`** there is bound to `L1Data.hBQ`
(conjunct 8, `∀ g ∈ B, ∀ i < pw, g + i • u' ∈ Q`).  The two are different propositions.
Positions 1-16 of `L1Data.toConclusion` (`L1Data.lean:158-176`) against the destructuring
pattern line up as

    7  hPQ ↔ hdef41      8  hBQ ↔ hline       13 hnonper ↔ hnonper_R'
    14 hline ↔ hQR       15 hstraddle ↔ hR'_step   16 hbase ↔ hB_covers

⚠ **Conjunct 16 was decoupled on 2026-09-19** (`L1Data.hbase`, mirrored by `SideData.hbase`
below): it now reads `B.Nonempty ∧ ∃ b, ∀ z ∈ S₁, b + z ∈ R`, no longer requiring the covering
base point to be the member of `B`.  §1's and §6's refutations are stated with the **old**,
coupled antecedent and are therefore left alone — refuting an implication out of a stronger
hypothesis is the stronger statement, and it yields the decoupled version a fortiori.  That
conjunct 16 really lost content is `conj16_strong_not_free_of_side`.

This is a 一名多物 for `hline` and a 一物多名 for conjunct 14.  Anything quoting "`hline`"
without saying which file it came from is ambiguous.

## §1 — Is conjunct 14 free from conjunct 16 plus `IsRegion`?  **No.**

Both refutations below are compiled.  `IsRegion R u u'` (`Lemma41.lean:688`) unfolds to
`IsLatticeConvexRegion R ∧ (∃ z₀, RayIn R z₀ u) ∧ (∃ z₀', RayIn R z₀' u')`, and
`RayIn U z₀ v` (`Lemma41.lean:675`) is `∀ k : ℕ, z₀ + (k : ℤ) • v ∈ U` — a ray from **one**
point, in **non-negative** multiples only.  Two independent gaps follow:

* **Offset.**  Conjunct 16 places `b + z` in `R`; conjunct 14 wants `t • u' + z`.  Nothing ties
  `b` to `τ • u'`.  `hline_not_free_of_base` refutes the implication.
* **Sign of `c`.**  `RayIn` gives no `-u`-closure, and `hc : c ≠ 0` (conjunct 9) permits `c < 0`,
  so `· + c • u ∈ R` is not free even when the offset is zero.
  `hline_not_free_even_at_zero_offset` refutes it with `b = 0`.

§1 also lands the two things that **are** free (`base_ray_mem`, `add_pos_smul_mem`), so the
boundary is drawn on both sides rather than only asserted.

## §2 — Conjunct 15 against conjunct 13: the contraposition, and its existing consumer

⚠ **This is already in the main build and already wired.**  `case1_claim47_semiAmbiguous`
(`RegionSteps.lean:979`) takes `hR'_step` (= conjunct 15), `hQR` (= conjunct 14) and
`hnonper_R'` (= conjunct 13) and produces `SemiAmbiguousAlong ξ ξ' S Q u' τ`; the collision is
discharged inline at `RegionSteps.lean:1046`,
`exact hnonper_R' (hR'_step g hgS hgQ t₀ ht₀ hRper hray)`, and the result is consumed at
`RegionSteps.lean:1162-1164` as `case1_sweep`'s `hamb`.  Claim 4.7 is **not** open.

`not_eventually_period_of_straddle` below is that collision as a named, standalone export — ten
lines, deliberately redundant with `RegionSteps.lean:1046`, landed only so the reading
"conjunct 15's real content is a negation" is a kernel fact and not a reading.  It is the
statement *"no window point off `Q` is eventually `c • u`-periodic along its `ℓ'`-line"*.

## §3 — `τ` is a free field, but there is no free lunch

`L1Data.τ` (`L1Data.lean:82`) carries no constraint, and both conjuncts 14 and 15 are of the
form `τ ≤ t → …`, so inflating `τ` weakens them.  §3 compiles the monotonicity of all three
places `τ` occurs — conjunct 14, conjunct 15, and `SemiAmbiguousAlong`, which is
`case1_claim47_semiAmbiguous`'s **conclusion**.  All three are antitone in `τ` in the same
direction: a producer who inflates `τ` weakens its obligations *and* weakens what the consumer
(`case1_sweep`'s `hamb`, and its `t₁ = τ + pw`) receives, in lockstep.  So the missing
constraint on `τ` is **not** a soundness hole — it is a degree of freedom that cancels.  Stated
as compiled lemmas rather than as an argument.

## §4 — The same-side problem: are conjuncts 14 and 15 stable under `n ↦ -n`?  **Neither is.**

`Nivat.ColleReg.L1Data.exists_side_with_run` (`L1Fields.lean:466`) shows conjunct 8 is
satisfiable at *one of the two ends* of the `n`-axis, and its own scope note says the other
conjuncts must then be met at the **same** end.  §4 answers that for conjuncts 14, 15 and 16.

**Answer: outcome 3 of the three the question admits.**  Neither end is forced and neither
transports; which end survives is a fact about `R`, and `exists_side_with_run` says nothing
about `R`.  Concretely, all three of the possible verdicts are realised in the kernel:

* **both ends work** — `conj14_can_hold_on_both_sides`;
* **only the `cmin` end is dead** — `witness` below, on which conjuncts 14 and 15 hold at `n`
  and *fail* at `-n` (`conj14_not_stable_under_neg`, `conj15_not_stable_under_neg`);
* **only the `cmax` end is dead** — `conj14_can_fail_at_either_end`, the same window, `u'` and
  `R`, read with the normal `(1,0)` instead of `(-1,0)`.  Conjunct 4 admits both, since it
  constrains the normal only by `n ≠ 0` and `inner2 n u' = 0`.

So no rule of the form "always cut at the top" or "always cut at the bottom" can be correct.

§4.1 explains *why*, structurally, rather than only exhibiting failures.  Conjuncts 14 and 15
mention `n` only through `Q`, conjunct 14 is **antitone** in `Q` and conjunct 15 is
**monotone** in it (`conj14_antitone`, `conj15_monotone` — opposite directions), and the two
cuts differ by exactly one exposed face each way (`negCut_sdiff_cut`, `cut_sdiff_negCut`).
Two consequences are worth quoting on their own:

* `conj14_both_sides_iff` — conjunct 14 at *both* ends is literally conjunct 14 on all of `S₁`.
  So a producer that could satisfy both never needed conjunct 4's cut in conjunct 14 at all.
* `conj15_domains_disjoint` — conjunct 15's two hypothesis sets are the two exposed faces, and
  `faces_disjoint` separates them.  An instance of conjunct 15 at one end is **never** an
  instance of it at the other, so a transport lemma cannot exist that is not already a proof of
  the target from scratch.  This is the sharp form of the negative answer for conjunct 15.

**Conjunct 16 is the exception: it is stable, trivially** (`conj16_stable_under_neg`).  It
mentions neither `n` nor `Q`, so the substitution does not reach it.

⚠ **Scope.**  The two refutations carry **twelve** of the sixteen conjuncts, not all sixteen.
Omitted: conjuncts 1 and 2 (so `ξ'` is an arbitrary `Config ℤ`, not a translate of a `ξ` with
generating set `S₁`) and conjuncts 7 and 8 (both mention `pw`, which is `exists_side_with_run`'s
own subject).  The bundle is spelled out field-by-field as `SideData`.

## §5 — The same answer, universally in `S₁` rather than on one window

§4's verdict is exhibited on the particular window `wS`.  §5 removes that dependence for
conjunct 14: `conj14_free_of_side` shows that for **every** finite `S₁` there is a strictly
extendable region `R ⊂ R'` — both `IsRegion` for `(1,0)`, `(0,1)` — and a nonzero `c` at which
conjunct 14 holds on all of `S₁`, hence at **both** cuts for **every** normal and **every**
pair of levels (`conj14_both_cuts_realisable`, note the quantifier order: `R` before `n`).
The region is the half-plane `rightHalf a = {z | a ≤ z.1}`, which is `u'`-invariant, so the cut
cannot see it.  The cheap version of this — take `R := Set.univ`, which `isRegion_univ`
(`L1Region.lean:261`) supplies — is barred by conjunct 12, so §5 carries conjuncts **9, 11, 12
and 14** together.

`conj15_free_of_side` is the conjunct-15 counterpart, one instance carrying conjuncts 4, 9, 10,
11, 12, 13 on which conjunct 15 fails at one cut and holds at the other.  It is **packaging**
of `witness.hstraddle` and `conj15_not_stable_under_neg`, not a new fact, and it is *not*
universal in `S₁` — conjunct 15 has `R` in a hypothesis and `R'` in its conclusion, so
enlarging `R` makes it harder, not easier.

⚠ What §5 does **not** say: that nothing forces a side.  It says conjuncts 9, 11, 12, 14 and 16
do not, so any forcing has to come through conjuncts 10 and 13 — the maximality coupling, out of
scope here by instruction.

## §6 — Is conjunct 16 the bridge once its base point is pinned?  **No.**

§1 refuted the bridge with the base `b` unconstrained; `ofEdgeRun` (`L1Fields.lean:165-205`)
pins it to a run start `z₀ ∈ S₁ ∩ Q`.  §1's witness does not survive that pinning, so §6 rebuilds
it: `conj16_bridge_dead_with_pinned_base` carries all three of `ofEdgeRun`'s constraints on `z₀`
plus conjuncts 4, 5, 6, 9, 11 and 16, with `τ` existentially quantified, and conjunct 14 still
fails.  The sharper reason, compiled as the matching positive result
(`conj16_bridge_of_base_on_u'_line`): the obstruction is the component of `z₀` **transverse to
`u'`**, and it disappears exactly when `z₀ ∈ ℤ • u'` — a hypothesis `ofEdgeRun` does not supply.
-/

namespace Nivat.L1Straddle

open Nivat Nivat.Colle Nivat.Colle41 Nivat.Colle43

/-! ## §1  Conjunct 14 is not free from conjunct 16 -/

/-- **What *is* free from conjunct 16 plus lattice-convexity.**  `ray_all_of_rayIn`
(`SweptSeed.lean:231`) at `n = 1` propagates the `u'`-ray from the single seed point of
`RayIn` to every point of `R`, so conjunct 16's translate `b + z` carries its whole forward
`u'`-ray.

⚠ Note the shape: the ray is based at `b + z`, **not** at `z`.  That `b` is exactly what
conjunct 14 does not have, and exactly why `hline_not_free_of_base` goes through. -/
theorem base_ray_mem {R : Set (ℤ × ℤ)} (hR : IsLatticeConvexRegion R)
    {z₀ u' : ℤ × ℤ} (hray : RayIn R z₀ u')
    {S₁ : Finset (ℤ × ℤ)} {b : ℤ × ℤ} (hb : ∀ z ∈ S₁, b + z ∈ R) :
    ∀ z ∈ S₁, ∀ k : ℕ, b + z + (k : ℤ) • u' ∈ R := by
  intro z hz k
  have h := ray_all_of_rayIn hR hray 1 (b + z) (hb z hz) k
  simpa using h

/-- **What is free on the `u`-side, and only there: `0 < c`.**  A single forward `u`-step of
size `c` stays in `R` when `c` is positive.  For `c < 0` this is false in general, which is the
second gap; see `hline_not_free_even_at_zero_offset`. -/
theorem add_pos_smul_mem {R : Set (ℤ × ℤ)} (hR : IsLatticeConvexRegion R)
    {z₀ u : ℤ × ℤ} (hray : RayIn R z₀ u) {c : ℤ} (hc : 0 < c)
    {z : ℤ × ℤ} (hz : z ∈ R) : z + c • u ∈ R := by
  have h := ray_all_of_rayIn hR hray c.toNat z hz 1
  rw [Int.toNat_of_nonneg hc.le] at h
  simpa using h

/-! ### The two refutations

Both run on `upperQuad = {z | 0 ≤ z.1 ∧ 1 ≤ z.2}` (`Claim43.lean:1047`) with
`isRegion_upperQuad : IsRegion upperQuad (1,0) (0,1)` (`Claim43.lean:1069`) — an existing,
kernel-checked region, not a hand-rolled one.
-/

/-- **Conjunct 14 does not follow from conjunct 16 plus `IsRegion` plus `Q ⊆ S₁` plus `c ≠ 0`.**

The offset gap, in its purest form: `S₁ = Q = {(0,0)}`, `B = {(0,1)}`, so conjunct 16 holds with
`b = (0,1)` (namely `(0,1) ∈ upperQuad`), while conjunct 14 already fails at `t = τ = 0`, where
it demands `(0,0) ∈ upperQuad`. -/
theorem hline_not_free_of_base :
    ¬ (∀ (R : Set (ℤ × ℤ)) (u u' : ℤ × ℤ) (S₁ Q B : Finset (ℤ × ℤ)) (τ c : ℤ),
        IsRegion R u u' → c ≠ 0 → Q ⊆ S₁ →
        (∃ b ∈ B, ∀ z ∈ S₁, b + z ∈ R) →
        ∀ t : ℤ, τ ≤ t → ∀ z ∈ Q, t • u' + z ∈ R ∧ t • u' + z + c • u ∈ R) := by
  intro h
  have hbad := h upperQuad (1, 0) (0, 1) {(0, 0)} {(0, 0)} {(0, 1)} 0 1
    isRegion_upperQuad one_ne_zero (le_refl _)
    ⟨(0, 1), by simp, by
      intro z hz
      simp only [Finset.mem_singleton] at hz
      subst hz
      exact ⟨le_refl 0, le_refl 1⟩⟩
    0 (le_refl 0) (0, 0) (by simp)
  have := hbad.1
  simp only [upperQuad, Set.mem_ofPred_eq, Prod.smul_fst, Prod.smul_snd, Prod.fst_add,
    Prod.snd_add, smul_eq_mul] at this
  omega

/-- **Not even with zero offset**: the `c < 0` gap survives when conjunct 16's `b` is `0`, so
`b + z = z` and the offset explanation is unavailable.

`S₁ = Q = {(0,1)}`, `b = (0,0)`, `c = -1`, `u = (1,0)`.  Conjunct 14's *first* half holds for
every `t ≥ 0` (`(0, t+1) ∈ upperQuad`); its *second* half fails at every `t`, because
`(0, t+1) + (-1) • (1,0) = (-1, t+1)` has first coordinate `-1 < 0`. -/
theorem hline_not_free_even_at_zero_offset :
    ¬ (∀ (R : Set (ℤ × ℤ)) (u u' : ℤ × ℤ) (S₁ Q : Finset (ℤ × ℤ)) (τ c : ℤ),
        IsRegion R u u' → c ≠ 0 → Q ⊆ S₁ →
        (∀ z ∈ S₁, z ∈ R) →
        ∀ t : ℤ, τ ≤ t → ∀ z ∈ Q, t • u' + z ∈ R ∧ t • u' + z + c • u ∈ R) := by
  intro h
  have hbad := h upperQuad (1, 0) (0, 1) {(0, 1)} {(0, 1)} 0 (-1)
    isRegion_upperQuad (by decide) (le_refl _)
    (by
      intro z hz
      simp only [Finset.mem_singleton] at hz
      subst hz
      exact ⟨le_refl 0, le_refl 1⟩)
    0 (le_refl 0) (0, 1) (by simp)
  have := hbad.2
  simp only [upperQuad, Set.mem_ofPred_eq, Prod.smul_fst, Prod.smul_snd, Prod.fst_add,
    Prod.snd_add, smul_eq_mul] at this
  omega

/-! ## §2  Conjunct 15 against conjunct 13 -/

/-- **Conjunct 15's real content is a negation.**

Conjunct 15 (`hstraddle`) concludes `PeriodOn ξ' R' (c • u)`, which conjunct 13 (`hnonper`)
denies, and conjunct 15's own third premise is conjunct 10 (`hRper`) verbatim.  Feeding 10 into
15 and colliding with 13 therefore says: **no window point off `Q` is eventually
`c • u`-periodic along its `ℓ'`-line**, above any threshold `≥ τ`.

⚠ Deliberately redundant with `RegionSteps.lean:1046`, which performs this same collision inline
inside `case1_claim47_semiAmbiguous`'s `by_contra`.  Landed as a named export so the reading can
be cited as a kernel fact; **not** a new result, and it does not open anything that was closed. -/
theorem not_eventually_period_of_straddle
    {ξ' : Config ℤ} {S₁ Q : Finset (ℤ × ℤ)} {u u' : ℤ × ℤ} {R R' : Set (ℤ × ℤ)} {c τ : ℤ}
    (hRper : PeriodOn ξ' R (c • u))
    (hnonper : ¬ PeriodOn ξ' R' (c • u))
    (hstraddle : ∀ g ∈ S₁, g ∉ Q → ∀ t₀ : ℤ, τ ≤ t₀ →
      PeriodOn ξ' R (c • u) →
      (∀ t : ℤ, t₀ ≤ t → ξ' (t • u' + g + c • u) = ξ' (t • u' + g)) →
      PeriodOn ξ' R' (c • u)) :
    ∀ g ∈ S₁, g ∉ Q → ∀ t₀ : ℤ, τ ≤ t₀ →
      ∃ t : ℤ, t₀ ≤ t ∧ ξ' (t • u' + g + c • u) ≠ ξ' (t • u' + g) := by
  intro g hg hgQ t₀ ht₀
  by_contra hcon
  refine hnonper (hstraddle g hg hgQ t₀ ht₀ hRper ?_)
  intro t ht
  by_contra hne
  exact hcon ⟨t, ht, hne⟩

/-! ## §3  `τ` is antitone everywhere it occurs -/

/-- Conjunct 14 weakens as `τ` grows. -/
theorem hline_antitone {u u' : ℤ × ℤ} {Q : Finset (ℤ × ℤ)} {R : Set (ℤ × ℤ)} {c τ τ' : ℤ}
    (hτ : τ ≤ τ')
    (h : ∀ t : ℤ, τ ≤ t → ∀ z ∈ Q, t • u' + z ∈ R ∧ t • u' + z + c • u ∈ R) :
    ∀ t : ℤ, τ' ≤ t → ∀ z ∈ Q, t • u' + z ∈ R ∧ t • u' + z + c • u ∈ R :=
  fun t ht => h t (le_trans hτ ht)

/-- Conjunct 15 weakens as `τ` grows. -/
theorem hstraddle_antitone {ξ' : Config ℤ} {S₁ Q : Finset (ℤ × ℤ)} {u u' : ℤ × ℤ}
    {R R' : Set (ℤ × ℤ)} {c τ τ' : ℤ} (hτ : τ ≤ τ')
    (h : ∀ g ∈ S₁, g ∉ Q → ∀ t₀ : ℤ, τ ≤ t₀ →
      PeriodOn ξ' R (c • u) →
      (∀ t : ℤ, t₀ ≤ t → ξ' (t • u' + g + c • u) = ξ' (t • u' + g)) →
      PeriodOn ξ' R' (c • u)) :
    ∀ g ∈ S₁, g ∉ Q → ∀ t₀ : ℤ, τ' ≤ t₀ →
      PeriodOn ξ' R (c • u) →
      (∀ t : ℤ, t₀ ≤ t → ξ' (t • u' + g + c • u) = ξ' (t • u' + g)) →
      PeriodOn ξ' R' (c • u) :=
  fun g hg hgQ t₀ ht₀ => h g hg hgQ t₀ (le_trans hτ ht₀)

/-- **The conclusion weakens too**, at the same rate: `SemiAmbiguousAlong`
(`Lemma41.lean:540`) is what `case1_claim47_semiAmbiguous` produces out of conjuncts 13/14/15,
and it is antitone in `τ` as well.  This is the precise sense in which the free field `τ` buys
the producer nothing. -/
theorem semiAmbiguousAlong_antitone {A : Type*} {η x : Config A} {S Q : Finset (ℤ × ℤ)}
    {u' : ℤ × ℤ} {τ τ' : ℤ} (hτ : τ ≤ τ')
    (h : SemiAmbiguousAlong η x S Q u' τ) : SemiAmbiguousAlong η x S Q u' τ' :=
  fun t ht => h t (le_trans hτ ht)

/-! ## §4  The same-side problem: conjuncts 14 and 15 under `n ↦ -n` -/

section SameSide

variable {S₁ : Finset (ℤ × ℤ)} {n : ℝ × ℝ} {cmax cmin : ℝ}

/-! ### §4.1  What changes when the cut moves to the other end

Conjuncts 14 and 15 mention `n` **only** through `Q`, and conjunct 4 pins
`Q = S₁.filter (inner2 n · < cmax)`.  Replacing `(n, cmax)` by `(-n, -cmin)` replaces that
cut by `S₁.filter (cmin < inner2 n ·)` (`Nivat.R2.filter_lt_neg`, `R2Orientation.lean:124`).
So the whole same-side question is the set-theoretic question of how those two cuts differ,
plus the monotonicity of the two conjuncts in `Q`.  §4.1 settles both halves. -/

/-- **The `(-n)`-cut removes the bottom face, exactly as the `n`-cut removes the top one.**

`Nivat.ColleReg.L1Data.sdiff_eq_face` (`L1Fields.lean:355`) already says
`S₁ ∖ (n`-cut`) = face S₁ n cmax`; this is the same statement at `(-n, -cmin)`, transported
back to `n` by `Nivat.R2.face_neg_level` and `Nivat.R2.filter_lt_neg`.  No new content —
landed so the `(-n)` side can be quoted without re-deriving it at each use. -/
theorem sdiff_negCut_eq_face (hge : ∀ z ∈ S₁, cmin ≤ inner2 n z) :
    S₁ \ (S₁.filter fun z => cmin < inner2 n z) = Nivat.R2.face S₁ n cmin := by
  rw [← Nivat.R2.filter_lt_neg S₁ n cmin,
    Nivat.ColleReg.L1Data.sdiff_eq_face (Nivat.R2.upperBound_neg_iff.mpr hge),
    Nivat.R2.face_neg_level]

/-- **The two cuts cover the window.**  Nothing of `S₁` escapes both ends: a point that is not
strictly below `cmax` sits *on* `cmax`, hence strictly above `cmin`. -/
theorem cut_union_negCut (hlt : cmin < cmax) :
    (S₁.filter fun z => inner2 n z < cmax) ∪ (S₁.filter fun z => cmin < inner2 n z) = S₁ := by
  refine Finset.Subset.antisymm
    (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)) ?_
  intro z hz
  rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
  by_cases h : inner2 n z < cmax
  · exact Or.inl ⟨hz, h⟩
  · exact Or.inr ⟨hz, lt_of_lt_of_le hlt (not_lt.mp h)⟩

/-- **The two exposed faces are disjoint** as soon as `cmin < cmax`.  This is the whole reason
conjunct 15 admits no transport: its two hypothesis sets are these two faces. -/
theorem faces_disjoint (hlt : cmin < cmax) :
    Disjoint (Nivat.R2.face S₁ n cmax) (Nivat.R2.face S₁ n cmin) := by
  rw [Finset.disjoint_left]
  intro z hz hz'
  rw [Nivat.R2.mem_face] at hz hz'
  exact absurd (hz.2.symm.trans hz'.2) (ne_of_gt hlt)

/-- **Conjunct 14's delta, one way: the `(-n)`-cut adds exactly the top face.** -/
theorem negCut_sdiff_cut (hle : ∀ z ∈ S₁, inner2 n z ≤ cmax) (hlt : cmin < cmax) :
    (S₁.filter fun z => cmin < inner2 n z) \ (S₁.filter fun z => inner2 n z < cmax)
      = Nivat.R2.face S₁ n cmax := by
  ext z
  simp only [Finset.mem_sdiff, Finset.mem_filter, Nivat.R2.mem_face, not_and, not_lt]
  constructor
  · rintro ⟨⟨hz, _⟩, hnot⟩
    exact ⟨hz, le_antisymm (hle z hz) (hnot hz)⟩
  · rintro ⟨hz, heq⟩
    exact ⟨⟨hz, by rw [heq]; exact hlt⟩, fun _ => le_of_eq heq.symm⟩

/-- **Conjunct 14's delta, the other way: the `n`-cut adds exactly the bottom face.** -/
theorem cut_sdiff_negCut (hge : ∀ z ∈ S₁, cmin ≤ inner2 n z) (hlt : cmin < cmax) :
    (S₁.filter fun z => inner2 n z < cmax) \ (S₁.filter fun z => cmin < inner2 n z)
      = Nivat.R2.face S₁ n cmin := by
  ext z
  simp only [Finset.mem_sdiff, Finset.mem_filter, Nivat.R2.mem_face, not_and, not_lt]
  constructor
  · rintro ⟨⟨hz, _⟩, hnot⟩
    exact ⟨hz, le_antisymm (hnot hz) (hge z hz)⟩
  · rintro ⟨hz, heq⟩
    exact ⟨⟨hz, by rw [heq]; exact hlt⟩, fun _ => le_of_eq heq⟩

/-- **Conjunct 14 is antitone in `Q`**: shrinking the cut weakens the obligation. -/
theorem conj14_antitone {u u' : ℤ × ℤ} {Q Q' : Finset (ℤ × ℤ)} {R : Set (ℤ × ℤ)} {c τ : ℤ}
    (hQ : Q' ⊆ Q)
    (h : ∀ t : ℤ, τ ≤ t → ∀ z ∈ Q, t • u' + z ∈ R ∧ t • u' + z + c • u ∈ R) :
    ∀ t : ℤ, τ ≤ t → ∀ z ∈ Q', t • u' + z ∈ R ∧ t • u' + z + c • u ∈ R :=
  fun t ht z hz => h t ht z (hQ hz)

/-- **Conjunct 15 is monotone in `Q`**: growing the cut shrinks the set of `g` it constrains,
which weakens the obligation.  Note the direction is **opposite** to conjunct 14's. -/
theorem conj15_monotone {ξ' : Config ℤ} {Q Q' : Finset (ℤ × ℤ)} {u u' : ℤ × ℤ}
    {R R' : Set (ℤ × ℤ)} {c τ : ℤ} (hQ : Q ⊆ Q')
    (h : ∀ g ∈ S₁, g ∉ Q → ∀ t₀ : ℤ, τ ≤ t₀ → PeriodOn ξ' R (c • u) →
      (∀ t : ℤ, t₀ ≤ t → ξ' (t • u' + g + c • u) = ξ' (t • u' + g)) → PeriodOn ξ' R' (c • u)) :
    ∀ g ∈ S₁, g ∉ Q' → ∀ t₀ : ℤ, τ ≤ t₀ → PeriodOn ξ' R (c • u) →
      (∀ t : ℤ, t₀ ≤ t → ξ' (t • u' + g + c • u) = ξ' (t • u' + g)) → PeriodOn ξ' R' (c • u) :=
  fun g hg hgQ' => h g hg fun hgQ => hgQ' (hQ hgQ)

/-- **Conjunct 14 on both sides is exactly conjunct 14 on the whole window.**

The forward direction is `cut_union_negCut`; the backward one is `conj14_antitone` twice.  So
"both sides work" is not a weaker hypothesis than "the obligation holds on all of `S₁`" — it is
the *same* hypothesis, and a producer that could meet it on both ends never needed conjunct 4's
cut in conjunct 14 at all. -/
theorem conj14_both_sides_iff {u u' : ℤ × ℤ} {R : Set (ℤ × ℤ)} {c τ : ℤ}
    (hlt : cmin < cmax) :
    ((∀ t : ℤ, τ ≤ t → ∀ z ∈ S₁.filter fun z => inner2 n z < cmax,
        t • u' + z ∈ R ∧ t • u' + z + c • u ∈ R) ∧
     (∀ t : ℤ, τ ≤ t → ∀ z ∈ S₁.filter fun z => cmin < inner2 n z,
        t • u' + z ∈ R ∧ t • u' + z + c • u ∈ R)) ↔
    (∀ t : ℤ, τ ≤ t → ∀ z ∈ S₁, t • u' + z ∈ R ∧ t • u' + z + c • u ∈ R) := by
  constructor
  · rintro ⟨h₁, h₂⟩ t ht z hz
    have hz' : z ∈ (S₁.filter fun z => inner2 n z < cmax)
        ∪ (S₁.filter fun z => cmin < inner2 n z) := by
      rw [cut_union_negCut hlt]; exact hz
    rcases Finset.mem_union.mp hz' with h | h
    · exact h₁ t ht z h
    · exact h₂ t ht z h
  · intro h
    exact ⟨conj14_antitone (Finset.filter_subset _ _) h,
      conj14_antitone (Finset.filter_subset _ _) h⟩

/-- **Conjunct 15's two hypothesis sets never share a point.**

Every `g` that conjunct 15 at `n` constrains (`g ∈ S₁`, `g ∉ n`-cut) lies *inside* the
`(-n)`-cut, hence is one of the `g` that conjunct 15 at `-n` does **not** constrain.  With
`sdiff_eq_face` and `sdiff_negCut_eq_face` the two domains are `face S₁ n cmax` and
`face S₁ n cmin`, which `faces_disjoint` separates.

Consequence, and it is the sharp form of the answer to the same-side question for conjunct 15:
an instance of conjunct 15 at one end is **never** an instance of it at the other, so no
transport can exist that is not already a proof of the target from scratch. -/
theorem conj15_domains_disjoint (hlt : cmin < cmax) :
    ∀ g ∈ S₁, g ∉ (S₁.filter fun z => inner2 n z < cmax) →
      g ∈ (S₁.filter fun z => cmin < inner2 n z) := by
  intro g hg hgQ
  have hg' : g ∈ (S₁.filter fun z => inner2 n z < cmax)
      ∪ (S₁.filter fun z => cmin < inner2 n z) := by
    rw [cut_union_negCut hlt]; exact hg
  exact (Finset.mem_union.mp hg').resolve_left hgQ

end SameSide

/-! ### §4.2  Both transports are false, on one witness carrying twelve of the sixteen conjuncts

`SideData` below bundles, at a chosen conjunct-4 normal `n`, the twelve `L1Data` conjuncts that
do not mention the width `pw`: conjuncts 4 (as its five components, plus `cmin` and
`cmin < cmax`, which `Nivat.ColleReg.L1Data.exists_min_face` (`L1Fields.lean:632`) supplies for
free), 5, 6, 9, 10, 11, 12, 13, 14, 15, 16.  Conjunct 3 is omitted because it is
`Finset.filter_subset` and carries nothing.

⚠ **Scope: four conjuncts are omitted**, and they are named here rather than left implicit.
Conjunct 1 (`IsGeneratingSet ξ S₁`) and conjunct 2 (`ξ' = T e ξ`, with the `orbitClosure`
binder) are dropped — `ξ'` below is an arbitrary `Config ℤ`, not a translate of a `ξ` whose
generating set is `S₁`.  Conjuncts 7 (`hPQ`) and 8 (`hBQ`) are dropped because both mention
`pw`, and `pw` is what `exists_side_with_run` is about; including them would conflate the
question asked here with the one that theorem already answered.  So what follows refutes the
transport **relative to twelve conjuncts**, not relative to all sixteen.

The field names and the `hline`/`hstraddle` shapes are copied from
`Nivat.ColleReg.L1Data.ofEdgeRun`'s argument list (`L1Fields.lean:165-205`), so a witness of
`SideData` is exactly what that constructor consumes, minus the four named omissions. -/
structure SideData where
  ξ' : Config ℤ
  S₁ : Finset (ℤ × ℤ)
  B : Finset (ℤ × ℤ)
  u : ℤ × ℤ
  u' : ℤ × ℤ
  R : Set (ℤ × ℤ)
  R' : Set (ℤ × ℤ)
  c : ℤ
  τ : ℤ
  n : ℝ × ℝ
  cmax : ℝ
  cmin : ℝ
  /-- Conjunct 4, component 1. -/
  hn : n ≠ 0
  /-- Conjunct 4, component 2. -/
  hnu' : inner2 n u' = 0
  /-- Conjunct 4, component 3. -/
  hle : ∀ z ∈ S₁, inner2 n z ≤ cmax
  /-- Conjunct 4, component 4. -/
  hfacemax : (Nivat.R2.face S₁ n cmax).Nonempty
  /-- The `cmin` end, from `Nivat.ColleReg.L1Data.exists_min_face`. -/
  hge : ∀ z ∈ S₁, cmin ≤ inner2 n z
  /-- The `cmin` end, from `Nivat.ColleReg.L1Data.exists_min_face`. -/
  hfacemin : (Nivat.R2.face S₁ n cmin).Nonempty
  /-- The `cmin` end, from `Nivat.ColleReg.L1Data.exists_min_face`. -/
  hlt : cmin < cmax
  /-- Conjunct 5. -/
  hdet : det u u' ≠ 0
  /-- Conjunct 6. -/
  hu'_prim : Primitive u'
  /-- Conjunct 9. -/
  hc : c ≠ 0
  /-- Conjunct 10. -/
  hRper : PeriodOn ξ' R (c • u)
  /-- Conjunct 11. -/
  hR_region : IsRegion R u u'
  /-- Conjunct 12. -/
  hRR' : R ⊂ R'
  /-- Conjunct 13. -/
  hnonper : ¬ PeriodOn ξ' R' (c • u)
  /-- Conjunct 14, **at the `n` end**. -/
  hline : ∀ t : ℤ, τ ≤ t → ∀ z ∈ S₁.filter (fun z => inner2 n z < cmax),
    t • u' + z ∈ R ∧ t • u' + z + c • u ∈ R
  /-- Conjunct 15, **at the `n` end**. -/
  hstraddle : ∀ g ∈ S₁, g ∉ S₁.filter (fun z => inner2 n z < cmax) → ∀ t₀ : ℤ, τ ≤ t₀ →
    PeriodOn ξ' R (c • u) →
    (∀ t : ℤ, t₀ ≤ t → ξ' (t • u' + g + c • u) = ξ' (t • u' + g)) →
    PeriodOn ξ' R' (c • u)
  /-- Conjunct 16.  It mentions neither `n` nor `Q`, so it is the one of the three that is
  **invariant** under `n ↦ -n`; see `conj16_stable_under_neg`.

  **Decoupled 2026-09-19, mirroring `L1Data.hbase`.**  This field used to read
  `∃ b ∈ B, ∀ z ∈ S₁, b + z ∈ R`, i.e. the *same* `b` witnessed membership in `B` and the
  covering.  That coupling has no reader: every consumer destructures the two halves
  separately.  The strength of a conjunct is set by what consumers actually destructure, not
  by what looked natural when it was written, so the two halves are now stated apart and `B`
  is only asserted nonempty.

  Within `SideData` the decoupling is a genuine loss and not a reformulation: `B` occurs in no
  other field of this structure, so nothing reconnects it to `R`.  That is compiled below as
  `conj16_strong_not_free_of_side`, with `witnessB0` as the separating witness. -/
  hbase : B.Nonempty ∧ ∃ b, ∀ z ∈ S₁, b + z ∈ R

/-- **Conjunct 16 is stable under `n ↦ -n`, for the trivial reason.**  It contains no
occurrence of `n` and no occurrence of `Q`, so the substitution does not reach it.  Stated as a
theorem rather than as a remark so the answer to "conjunct 16 too?" is a kernel fact.

Restated 2026-09-19 to the decoupled shape of the field; the argument — "`n` does not occur" —
is untouched by the decoupling, since neither half of the new form mentions `n` either. -/
theorem conj16_stable_under_neg (w : SideData) :
    w.B.Nonempty ∧ ∃ b, ∀ z ∈ w.S₁, b + z ∈ w.R := w.hbase

/-! #### The witness

Window `S₁ = {(-1,0), (0,0)}` on the line orthogonal to `u' = (0,1)`; region
`R = upperQuad` (`Claim43.lean:1047`), extension `R' = {z | -1 ≤ z.1}`, period `c • u = (1,0)`,
threshold `τ = 1`, normal `n = (-1,0)` so that `inner2 n z = -z.1`, `cmax = 1`, `cmin = 0`.

The `n`-cut is `{(0,0)}` and the `(-n)`-cut is `{(-1,0)}` — the two singletons, swapped.  The
column above `(0,0)` lies in `upperQuad` and the column above `(-1,0)` does not, which is the
whole of the conjunct-14 failure; the configuration below then makes the conjunct-15 failure
fall out of the same geometry. -/

/-- The two-point window. -/
private def wS : Finset (ℤ × ℤ) := {(-1, 0), (0, 0)}

/-- The strict extension `R'`: one column further left than `upperQuad`. -/
private def wR' : Set (ℤ × ℤ) := {z : ℤ × ℤ | -1 ≤ z.1}

/-- The configuration.  Constant `0` on `upperQuad`, so `(1,0)` is a period there; but the
column `z.1 = -1` records its own height, which both breaks the period on `R'` and makes the
`g = (-1,0)` instance of conjunct 15 vacuous. -/
private def wX : Config ℤ := fun z => if z.1 = -1 then z.2 else if z.2 ≤ 0 then 1 else 0

/-- The normal: `inner2 wN z = -z.1`. -/
private def wN : ℝ × ℝ := (-1, 0)

private theorem wN_inner2 (z : ℤ × ℤ) : inner2 wN z = -(z.1 : ℝ) := by
  simp only [inner2, wN]
  ring

private theorem wS_mem {z : ℤ × ℤ} (hz : z ∈ wS) : z = (-1, 0) ∨ z = (0, 0) := by
  simpa [wS] using hz

private theorem w_cu : (1 : ℤ) • ((1 : ℤ), (0 : ℤ)) = ((1 : ℤ), (0 : ℤ)) := one_smul ℤ _

private theorem w_col (t : ℤ) (a : ℤ) :
    t • ((0 : ℤ), (1 : ℤ)) + (a, (0 : ℤ)) = (a, t) := by
  rw [Prod.ext_iff]
  constructor <;> simp

private theorem w_col' (t a b : ℤ) :
    t • ((0 : ℤ), (1 : ℤ)) + (a, b) = (a, t + b) := by
  rw [Prod.ext_iff]
  constructor <;> simp

private theorem mk_mem_upperQuad {a b : ℤ} (h1 : 0 ≤ a) (h2 : 1 ≤ b) : (a, b) ∈ upperQuad :=
  ⟨h1, h2⟩

/-- The witness, with all twenty-eight fields discharged. -/
private def witness : SideData where
  ξ' := wX
  S₁ := wS
  B := {((2 : ℤ), (2 : ℤ))}
  u := ((1 : ℤ), (0 : ℤ))
  u' := ((0 : ℤ), (1 : ℤ))
  R := upperQuad
  R' := wR'
  c := 1
  τ := 1
  n := wN
  cmax := 1
  cmin := 0
  hn := by simp [wN, Prod.ext_iff]
  hnu' := by rw [wN_inner2]; norm_num
  hle := by
    intro z hz
    rcases wS_mem hz with rfl | rfl <;> · rw [wN_inner2]; norm_num
  hfacemax := ⟨(-1, 0), Nivat.R2.mem_face.mpr ⟨by simp [wS], by rw [wN_inner2]; norm_num⟩⟩
  hge := by
    intro z hz
    rcases wS_mem hz with rfl | rfl <;> · rw [wN_inner2]; norm_num
  hfacemin := ⟨(0, 0), Nivat.R2.mem_face.mpr ⟨by simp [wS], by rw [wN_inner2]; norm_num⟩⟩
  hlt := by norm_num
  hdet := by decide
  hu'_prim := isCoprime_one_right
  hc := by decide
  hRper := by
    intro z hz _
    have h1 : (0 : ℤ) ≤ z.1 := hz.1
    have h2 : (1 : ℤ) ≤ z.2 := hz.2
    rw [w_cu]
    have e1 : (z + ((1 : ℤ), (0 : ℤ))).1 = z.1 + 1 := rfl
    have e2 : (z + ((1 : ℤ), (0 : ℤ))).2 = z.2 := by simp
    simp only [wX, e1, e2]
    rw [if_neg (show ¬(z.1 + 1 = -1) by omega), if_neg (show ¬(z.1 = -1) by omega)]
  hR_region := isRegion_upperQuad
  hRR' := by
    have hsub : upperQuad ⊆ wR' := by
      intro z hz
      show (-1 : ℤ) ≤ z.1
      have := hz.1
      omega
    rw [Set.ssubset_iff_of_subset hsub]
    refine ⟨((0 : ℤ), (0 : ℤ)), by show (-1 : ℤ) ≤ 0; omega, ?_⟩
    intro hmem
    have : (1 : ℤ) ≤ 0 := hmem.2
    omega
  hnonper := by
    intro h
    have hz : ((-1 : ℤ), (5 : ℤ)) ∈ wR' := by show (-1 : ℤ) ≤ -1; omega
    have e : ((-1 : ℤ), (5 : ℤ)) + (1 : ℤ) • ((1 : ℤ), (0 : ℤ)) = ((0 : ℤ), (5 : ℤ)) := by
      rw [w_cu, Prod.ext_iff]
      constructor <;> norm_num
    have hz2 : ((-1 : ℤ), (5 : ℤ)) + (1 : ℤ) • ((1 : ℤ), (0 : ℤ)) ∈ wR' := by
      rw [e]; show (-1 : ℤ) ≤ 0; omega
    have hbad := h _ hz hz2
    rw [e] at hbad
    simp only [wX] at hbad
    norm_num at hbad
  hline := by
    intro t ht z hz
    rw [Finset.mem_filter] at hz
    obtain ⟨hzS, hzlt⟩ := hz
    have hz0 : z = ((0 : ℤ), (0 : ℤ)) := by
      rcases wS_mem hzS with rfl | rfl
      · rw [wN_inner2] at hzlt; norm_num at hzlt
      · rfl
    subst hz0
    rw [w_cu, w_col t 0]
    refine ⟨mk_mem_upperQuad (le_refl 0) ht, ?_⟩
    have e : ((0 : ℤ), t) + ((1 : ℤ), (0 : ℤ)) = ((1 : ℤ), t) := by
      rw [Prod.ext_iff]; constructor <;> norm_num
    rw [e]
    exact mk_mem_upperQuad (by norm_num) ht
  hstraddle := by
    intro g hg hgQ t₀ ht₀ _ heq
    exfalso
    have hg1 : g = ((-1 : ℤ), (0 : ℤ)) := by
      rcases wS_mem hg with rfl | rfl
      · rfl
      · exact absurd (Finset.mem_filter.mpr ⟨hg, by rw [wN_inner2]; norm_num⟩) hgQ
    subst hg1
    have h := heq t₀ (le_refl t₀)
    rw [w_cu, w_col t₀ (-1)] at h
    have e : ((-1 : ℤ), t₀) + ((1 : ℤ), (0 : ℤ)) = ((0 : ℤ), t₀) := by
      rw [Prod.ext_iff]; constructor <;> norm_num
    rw [e] at h
    simp only [wX] at h
    simp only [if_true] at h
    omega
  hbase := ⟨⟨((2 : ℤ), (2 : ℤ)), Finset.mem_singleton_self _⟩, ((2 : ℤ), (2 : ℤ)), by
    intro z hz
    rcases wS_mem hz with rfl | rfl
    · exact ⟨by decide, by decide⟩
    · exact ⟨by decide, by decide⟩⟩

private theorem witness_S₁ : witness.S₁ = wS := rfl
private theorem witness_n : witness.n = wN := rfl
private theorem witness_cmin : witness.cmin = 0 := rfl
private theorem witness_τ : witness.τ = 1 := rfl
private theorem witness_u' : witness.u' = ((0 : ℤ), (1 : ℤ)) := rfl
private theorem witness_u : witness.u = ((1 : ℤ), (0 : ℤ)) := rfl
private theorem witness_c : witness.c = 1 := rfl
private theorem witness_R : witness.R = upperQuad := rfl

/-! #### The decoupling is real: `B` is not reconnected to `R` by any other field

`witness` above happens to satisfy the *old*, coupled shape of conjunct 16 as well — its
`B = {(2,2)}` contains the very base point that covers `S₁`.  So `witness` alone cannot show
that the 2026-09-19 decoupling lost anything.  `witnessB0` is `witness` with `B` moved to
`{(0,0)}` and nothing else changed: the new field still holds (the covering half is witnessed
by `(2,2)`, which no longer has to lie in `B`), and the old field fails.

This is what licenses the field docstring's claim that the decoupling is a genuine weakening of
`SideData` rather than a reformulation of it. -/
private def witnessB0 : SideData :=
  { witness with
    B := {((0 : ℤ), (0 : ℤ))}
    hbase := ⟨⟨((0 : ℤ), (0 : ℤ)), Finset.mem_singleton_self _⟩, ((2 : ℤ), (2 : ℤ)), by
      intro z hz
      rcases wS_mem hz with rfl | rfl
      · exact ⟨by decide, by decide⟩
      · exact ⟨by decide, by decide⟩⟩ }

private theorem witnessB0_B : witnessB0.B = {((0 : ℤ), (0 : ℤ))} := rfl
private theorem witnessB0_S₁ : witnessB0.S₁ = wS := rfl
private theorem witnessB0_R : witnessB0.R = upperQuad := rfl

/-- **The coupled form of conjunct 16 is not free from `SideData`.**

`SideData` carries twelve of the sixteen conjuncts, conjunct 16 among them in its decoupled
form, and the coupled form — "the base point that covers `S₁` may be taken *inside* `B`" —
still fails.  Witness `witnessB0`: `B = {(0,0)}`, `S₁ = {(-1,0), (0,0)}`, `R = upperQuad`, so
the only candidate `b ∈ B` is `(0,0)` and `(0,0) + (-1,0) = (-1,0) ∉ upperQuad`.

⚠ **Scope, as for every refutation in this file.**  This says the coupling is not derivable
*from the twelve conjuncts bundled in `SideData`*.  It does **not** say the coupling is false
at the real call site, where conjuncts 1, 2, 7 and 8 are also in hand and `B` is the run-start
set that `ofEdgeRun` (`L1Fields.lean:165-205`) pins — only that nothing in this bundle supplies
it, which is why the field is now stated decoupled. -/
theorem conj16_strong_not_free_of_side :
    ¬ ∀ w : SideData, ∃ b ∈ w.B, ∀ z ∈ w.S₁, b + z ∈ w.R := by
  intro h
  obtain ⟨b, hbB, hcov⟩ := h witnessB0
  rw [witnessB0_B, Finset.mem_singleton] at hbB
  subst hbB
  have hbad := hcov ((-1 : ℤ), (0 : ℤ)) (by rw [witnessB0_S₁]; simp [wS])
  rw [witnessB0_R] at hbad
  have h1 : (0 : ℤ) ≤ (((0 : ℤ), (0 : ℤ)) + ((-1 : ℤ), (0 : ℤ))).1 := hbad.1
  simp only [Prod.fst_add] at h1
  omega

/-- **Conjunct 14 is not stable under `n ↦ -n`.**

Twelve conjuncts hold at the normal `n`, conjunct 14 among them, and conjunct 14 at `-n` fails:
at `t = τ = 1` and `z = (-1,0)` it demands `1 • (0,1) + (-1,0) = (-1,1) ∈ upperQuad`, whose
first coordinate is `-1`.

By `negCut_sdiff_cut` the delta is exactly the top face `face S₁ n cmax = {(-1,0)}`, and this
witness shows the delta is not free. -/
theorem conj14_not_stable_under_neg :
    ¬ ∀ w : SideData, ∀ t : ℤ, w.τ ≤ t →
        ∀ z ∈ w.S₁.filter (fun z => inner2 (-w.n) z < -w.cmin),
          t • w.u' + z ∈ w.R ∧ t • w.u' + z + w.c • w.u ∈ w.R := by
  intro h
  have hmem : ((-1 : ℤ), (0 : ℤ)) ∈
      witness.S₁.filter (fun z => inner2 (-witness.n) z < -witness.cmin) := by
    rw [witness_S₁, witness_n, witness_cmin, Finset.mem_filter]
    refine ⟨by simp [wS], ?_⟩
    rw [Nivat.R2.inner2_neg_left, wN_inner2]
    norm_num
  have hbad := (h witness 1 witness_τ.le _ hmem).1
  rw [witness_u', witness_R, w_col 1 (-1)] at hbad
  have : (0 : ℤ) ≤ -1 := hbad.1
  omega

/-- **Conjunct 15 is not stable under `n ↦ -n`.**

The same witness, same twelve conjuncts.  At `-n` the constrained point is `g = (0,0)`, the
column above it is constantly `0` in `upperQuad`, so conjunct 15's eventual-agreement premise
holds at `t₀ = τ = 1` — and its conclusion `PeriodOn ξ' R' (c • u)` is conjunct 13's negation.
Conjunct 15 at `-n` therefore fails outright, not merely "is unproved".

This is `conj15_domains_disjoint` made concrete: at `n` the constrained `g` is `(-1,0)`, whose
column is *not* eventually periodic, so conjunct 15 at `n` is vacuously true; at `-n` it is
`(0,0)`, whose column *is*, so conjunct 15 at `-n` is false.  The two ends see disjoint data. -/
theorem conj15_not_stable_under_neg :
    ¬ ∀ w : SideData, ∀ g ∈ w.S₁,
        g ∉ w.S₁.filter (fun z => inner2 (-w.n) z < -w.cmin) → ∀ t₀ : ℤ, w.τ ≤ t₀ →
        PeriodOn w.ξ' w.R (w.c • w.u) →
        (∀ t : ℤ, t₀ ≤ t → w.ξ' (t • w.u' + g + w.c • w.u) = w.ξ' (t • w.u' + g)) →
        PeriodOn w.ξ' w.R' (w.c • w.u) := by
  intro h
  refine witness.hnonper (h witness ((0 : ℤ), (0 : ℤ)) (by rw [witness_S₁]; simp [wS]) ?_ 1
    witness_τ.le witness.hRper ?_)
  · rw [witness_S₁, witness_n, witness_cmin, Finset.mem_filter]
    rintro ⟨-, hlt⟩
    rw [Nivat.R2.inner2_neg_left, wN_inner2] at hlt
    norm_num at hlt
  · intro t _
    rw [witness_u', witness_c, witness_u, w_cu, w_col t 0]
    have e : ((0 : ℤ), t) + ((1 : ℤ), (0 : ℤ)) = ((1 : ℤ), t) := by
      rw [Prod.ext_iff]; constructor <;> norm_num
    rw [e]
    show wX ((1 : ℤ), t) = wX ((0 : ℤ), t)
    simp only [wX]
    rw [if_neg (show ¬((1 : ℤ) = -1) by omega), if_neg (show ¬((0 : ℤ) = -1) by omega)]

/-- The negated normal, spelled out: `inner2 wNneg z = z.1`.  Conjunct 4 admits it exactly when
it admits `wN`, since it constrains the normal only by `n ≠ 0` and `inner2 n u' = 0`. -/
private def wNneg : ℝ × ℝ := (1, 0)

private theorem wNneg_inner2 (z : ℤ × ℤ) : inner2 wNneg z = (z.1 : ℝ) := by
  simp only [inner2, wNneg]
  ring

/-- **Neither end is the systematically dead one.**

The mirror of `witness`: same window `S₁ = {(-1,0), (0,0)}`, same `u'`, same `R = upperQuad`,
but read with the normal `(1,0)` instead of `(-1,0)`.  Now it is the **`cmax` end** whose cut is
`{(-1,0)}` and therefore dead, and the `cmin` end that survives — the exact opposite of
`conj14_not_stable_under_neg`'s witness, on the same geometry.

Together with `conj14_can_hold_on_both_sides` and `conj14_not_stable_under_neg` this closes the
trichotomy in the kernel: both ends alive, `cmin` end alive only, `cmax` end alive only.  So
no rule of the form "always cut at the top" or "always cut at the bottom" can be correct, and
`exists_side_with_run`'s disjunction cannot be collapsed by anything conjunct 14 knows. -/
theorem conj14_can_fail_at_either_end :
    ∃ (S₁ : Finset (ℤ × ℤ)) (n : ℝ × ℝ) (cmax cmin : ℝ) (u u' : ℤ × ℤ) (R : Set (ℤ × ℤ))
      (c τ : ℤ),
      IsRegion R u u' ∧ n ≠ 0 ∧ inner2 n u' = 0 ∧ cmin < cmax ∧
      (∀ z ∈ S₁, inner2 n z ≤ cmax) ∧ (∀ z ∈ S₁, cmin ≤ inner2 n z) ∧
      ¬ (∀ t : ℤ, τ ≤ t → ∀ z ∈ S₁.filter (fun z => inner2 n z < cmax),
          t • u' + z ∈ R ∧ t • u' + z + c • u ∈ R) ∧
      (∀ t : ℤ, τ ≤ t → ∀ z ∈ S₁.filter (fun z => cmin < inner2 n z),
          t • u' + z ∈ R ∧ t • u' + z + c • u ∈ R) := by
  refine ⟨wS, wNneg, 0, -1, ((1 : ℤ), (0 : ℤ)), ((0 : ℤ), (1 : ℤ)), upperQuad, 1, 1,
    isRegion_upperQuad, by simp [wNneg, Prod.ext_iff], by rw [wNneg_inner2]; norm_num,
    by norm_num, ?_, ?_, ?_, ?_⟩
  · intro z hz
    rcases wS_mem hz with rfl | rfl <;> · rw [wNneg_inner2]; norm_num
  · intro z hz
    rcases wS_mem hz with rfl | rfl <;> · rw [wNneg_inner2]; norm_num
  · intro hbad
    have hmem : ((-1 : ℤ), (0 : ℤ)) ∈ wS.filter (fun z => inner2 wNneg z < 0) :=
      Finset.mem_filter.mpr ⟨by simp [wS], by rw [wNneg_inner2]; norm_num⟩
    have h := (hbad 1 (le_refl 1) _ hmem).1
    rw [w_col 1 (-1)] at h
    have : (0 : ℤ) ≤ -1 := h.1
    omega
  · intro t ht z hz
    rw [Finset.mem_filter] at hz
    obtain ⟨hzS, hzlt⟩ := hz
    have hz0 : z = ((0 : ℤ), (0 : ℤ)) := by
      rcases wS_mem hzS with rfl | rfl
      · rw [wNneg_inner2] at hzlt; norm_num at hzlt
      · rfl
    subst hz0
    rw [w_cu, w_col t 0]
    refine ⟨mk_mem_upperQuad (le_refl 0) ht, ?_⟩
    have e : ((0 : ℤ), t) + ((1 : ℤ), (0 : ℤ)) = ((1 : ℤ), t) := by
      rw [Prod.ext_iff]; constructor <;> norm_num
    rw [e]
    exact mk_mem_upperQuad (by norm_num) ht

/-- Both points of the raised window carry their whole upward column, and the `(1,0)`-shift of
it, inside `upperQuad`. -/
private theorem both_sides_aux (t : ℤ) (ht : (0 : ℤ) ≤ t) {z : ℤ × ℤ}
    (hz : z = ((0 : ℤ), (1 : ℤ)) ∨ z = ((1 : ℤ), (1 : ℤ))) :
    t • ((0 : ℤ), (1 : ℤ)) + z ∈ upperQuad ∧
      t • ((0 : ℤ), (1 : ℤ)) + z + (1 : ℤ) • ((1 : ℤ), (0 : ℤ)) ∈ upperQuad := by
  rw [w_cu]
  rcases hz with rfl | rfl
  · rw [w_col' t 0 1]
    refine ⟨mk_mem_upperQuad (le_refl 0) (by omega), ?_⟩
    have e : ((0 : ℤ), t + 1) + ((1 : ℤ), (0 : ℤ)) = ((1 : ℤ), t + 1) := by
      rw [Prod.ext_iff]; constructor <;> norm_num
    rw [e]
    exact mk_mem_upperQuad (by norm_num) (by omega)
  · rw [w_col' t 1 1]
    refine ⟨mk_mem_upperQuad (by norm_num) (by omega), ?_⟩
    have e : ((1 : ℤ), t + 1) + ((1 : ℤ), (0 : ℤ)) = ((2 : ℤ), t + 1) := by
      rw [Prod.ext_iff]; constructor <;> norm_num
    rw [e]
    exact mk_mem_upperQuad (by norm_num) (by omega)

/-- **Both ends can also succeed at once.**  Sliding the same window up into `upperQuad`'s
interior makes conjunct 14 hold at both cuts, so neither end is universally dead and the
trichotomy is fully realised: both-work, `n`-only (the witness above), and — by relabelling
that witness's normal as `(1,0)`, which is an equally legal conjunct-4 normal for the same
`S₁` and `u'` — `(-n)`-only.

Together with `conj14_not_stable_under_neg` this is the answer to the same-side question for
conjunct 14: **neither side is forced, and neither transports.**  Which end survives is a fact
about `R`, and `exists_side_with_run` (`L1Fields.lean:466`) says nothing about `R`. -/
theorem conj14_can_hold_on_both_sides :
    ∃ (S₁ : Finset (ℤ × ℤ)) (n : ℝ × ℝ) (cmax cmin : ℝ) (u u' : ℤ × ℤ) (R : Set (ℤ × ℤ))
      (c τ : ℤ),
      IsRegion R u u' ∧ n ≠ 0 ∧ inner2 n u' = 0 ∧ cmin < cmax ∧
      (∀ z ∈ S₁, inner2 n z ≤ cmax) ∧ (∀ z ∈ S₁, cmin ≤ inner2 n z) ∧
      (∀ t : ℤ, τ ≤ t → ∀ z ∈ S₁.filter (fun z => inner2 n z < cmax),
        t • u' + z ∈ R ∧ t • u' + z + c • u ∈ R) ∧
      (∀ t : ℤ, τ ≤ t → ∀ z ∈ S₁.filter (fun z => cmin < inner2 n z),
        t • u' + z ∈ R ∧ t • u' + z + c • u ∈ R) := by
  refine ⟨{((0 : ℤ), (1 : ℤ)), ((1 : ℤ), (1 : ℤ))}, wN, 0, -1, ((1 : ℤ), (0 : ℤ)),
    ((0 : ℤ), (1 : ℤ)), upperQuad, 1, 0, isRegion_upperQuad, ?_, ?_, by norm_num, ?_, ?_, ?_, ?_⟩
  · simp [wN, Prod.ext_iff]
  · rw [wN_inner2]; norm_num
  · intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl <;> · rw [wN_inner2]; norm_num
  · intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl <;> · rw [wN_inner2]; norm_num
  · intro t ht z hz
    rw [Finset.mem_filter] at hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    exact both_sides_aux t ht hz.1
  · intro t ht z hz
    rw [Finset.mem_filter] at hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    exact both_sides_aux t ht hz.1

/-! ## §5 Conjunct 14 with conjuncts 11 and 12 also in hand: the side is *still* free

§4 answered the `n ↦ -n` question on one witness at a time.  §5 answers it **universally in
`S₁`**, and does so against a stronger conjunct set, so that the freedom cannot be dismissed as
an artefact of the particular window `wS`.

The cheap version of this observation is worthless: `isRegion_univ` (`L1Region.lean:261`) gives
`IsRegion Set.univ u u'`, and with `R := Set.univ` conjunct 14 is vacuously true at both cuts.
But `Set.univ` is barred by **conjunct 12** (`R ⊂ R'` forces `R ≠ Set.univ`), so that proves
nothing about the real obligation.

`conj14_free_of_side` therefore carries conjuncts **11, 12, 9 and 14** at once: for *every*
finite `S₁` it produces a strictly-extendable region `R ⊂ R'`, both `IsRegion` for the same
pair of directions, a nonzero `c`, and conjunct 14 holding on **all of `S₁`** — hence, by
`conj14_antitone`, at both cuts simultaneously, for **every** normal `n` and **every** pair
`cmin`, `cmax` (`conj14_both_cuts_realisable`).  The region is the right half-plane
`rightHalf a = {z | a ≤ z.1}` with `a` a lower bound for the first coordinates of `S₁`; it is
`u'`-invariant, which is exactly why no `τ` threshold is needed and why the cut plays no role.

**Consequence for the coherence question.**  Conjuncts 9, 11, 12 and 14 together place *no*
constraint on which end `exists_side_with_run` (`L1Fields.lean:466`) picks.  Whatever forces a
side — if anything does — has to come through the one pair this file does not touch, conjuncts
10 and 13 (`PeriodOn ξ' R (c • u)` and `¬ PeriodOn ξ' R' (c • u)`), which is precisely the
maximality/index coupling that is being handled elsewhere and is deliberately out of scope here.
⚠ That is a statement about what §5 *proves*, not a claim that 10/13 do force a side.
-/

section SideFree

/-- The right half-plane `{z | a ≤ z.1}`.  Unlike `Set.univ` it can be strictly extended, so it
survives conjunct 12; unlike `upperQuad` it is invariant under `u' = (0,1)`.

Not built by hand: it is `L1Region.cut Set.univ (1,0) (fun _ => a) 0` (`L1Region.lean:198`),
the family `L1Region` §4 already uses for its own non-vacuity witness, so `isRegion_rightHalf`
is one application of `isRegion_cut` (`L1Region.lean:205`) rather than a second
lattice-convexity proof. -/
private def rightHalf (a : ℤ) : Set (ℤ × ℤ) :=
  Nivat.L1Region.cut (Set.univ : Set (ℤ × ℤ)) ((1 : ℤ), (0 : ℤ)) (fun _ => a) 0

private theorem mem_rightHalf {a : ℤ} {z : ℤ × ℤ} : z ∈ rightHalf a ↔ a ≤ z.1 := by
  simp [rightHalf, Nivat.L1Region.cut, Nivat.LE2.halfPlaneGE, Nivat.LE2.dot]

private theorem isRegion_rightHalf (a : ℤ) :
    IsRegion (rightHalf a) ((1 : ℤ), (0 : ℤ)) ((0 : ℤ), (1 : ℤ)) :=
  Nivat.L1Region.isRegion_cut (Nivat.L1Region.isRegion_univ _ _) (by decide) (by decide) _ 0

private theorem rightHalf_ssubset (a : ℤ) : rightHalf a ⊂ rightHalf (a - 1) := by
  have hsub : rightHalf a ⊆ rightHalf (a - 1) := by
    intro z hz
    rw [mem_rightHalf] at hz ⊢
    omega
  rw [Set.ssubset_iff_of_subset hsub]
  refine ⟨(a - 1, 0), ?_, ?_⟩
  · rw [mem_rightHalf]
  · rw [mem_rightHalf]
    omega

/-- Every finite window has a lower bound on its first coordinates. -/
private theorem exists_col_lower_bound (S : Finset (ℤ × ℤ)) : ∃ a : ℤ, ∀ z ∈ S, a ≤ z.1 := by
  obtain ⟨M, hM⟩ := (S.image (fun z => -z.1)).exists_le
  refine ⟨-M, fun z hz => ?_⟩
  have := hM (-z.1) (Finset.mem_image_of_mem _ hz)
  omega

/-- **Conjunct 14 never pins the side, for any window.**

For every finite `S₁` there are `R ⊂ R'`, both regions for `u = (1,0)`, `u' = (0,1)`, and a
nonzero `c`, with conjunct 14 satisfied on the whole of `S₁`.  Conjuncts 9, 11, 12 and 14 are
therefore jointly satisfiable without ever looking at the cut, so none of them can decide
between the `n` end and the `-n` end. -/
theorem conj14_free_of_side (S₁ : Finset (ℤ × ℤ)) :
    ∃ (R R' : Set (ℤ × ℤ)) (c τ : ℤ),
      IsRegion R ((1 : ℤ), (0 : ℤ)) ((0 : ℤ), (1 : ℤ)) ∧
      IsRegion R' ((1 : ℤ), (0 : ℤ)) ((0 : ℤ), (1 : ℤ)) ∧
      R ⊂ R' ∧ c ≠ 0 ∧
      ∀ t : ℤ, τ ≤ t → ∀ z ∈ S₁,
        t • ((0 : ℤ), (1 : ℤ)) + z ∈ R ∧
          t • ((0 : ℤ), (1 : ℤ)) + z + c • ((1 : ℤ), (0 : ℤ)) ∈ R := by
  obtain ⟨a, ha⟩ := exists_col_lower_bound S₁
  refine ⟨rightHalf a, rightHalf (a - 1), 1, 0, isRegion_rightHalf a, isRegion_rightHalf (a - 1),
    rightHalf_ssubset a, one_ne_zero, ?_⟩
  intro t _ z hz
  have hz1 : a ≤ z.1 := ha z hz
  constructor
  · rw [mem_rightHalf]
    have e : (t • ((0 : ℤ), (1 : ℤ)) + z).1 = z.1 := by simp
    rw [e]
    exact hz1
  · rw [mem_rightHalf]
    have e : (t • ((0 : ℤ), (1 : ℤ)) + z + (1 : ℤ) • ((1 : ℤ), (0 : ℤ))).1 = z.1 + 1 := by simp
    rw [e]
    omega

/-- **The same `R` works at both cuts, for every normal and every pair of levels.**

`conj14_free_of_side` plus `conj14_antitone`.  Note the quantifier order: `R`, `R'`, `c` and `τ`
are chosen *before* `n`, `cmax`, `cmin`, so a single region serves every possible conjunct-4
cut of the same window at once — in particular the `n` cut and the `-n` cut. -/
theorem conj14_both_cuts_realisable (S₁ : Finset (ℤ × ℤ)) :
    ∃ (R R' : Set (ℤ × ℤ)) (c τ : ℤ),
      IsRegion R ((1 : ℤ), (0 : ℤ)) ((0 : ℤ), (1 : ℤ)) ∧
      IsRegion R' ((1 : ℤ), (0 : ℤ)) ((0 : ℤ), (1 : ℤ)) ∧
      R ⊂ R' ∧ c ≠ 0 ∧
      ∀ (n : ℝ × ℝ) (cmax cmin : ℝ),
        (∀ t : ℤ, τ ≤ t → ∀ z ∈ S₁.filter (fun z => inner2 n z < cmax),
          t • ((0 : ℤ), (1 : ℤ)) + z ∈ R ∧
            t • ((0 : ℤ), (1 : ℤ)) + z + c • ((1 : ℤ), (0 : ℤ)) ∈ R) ∧
        (∀ t : ℤ, τ ≤ t → ∀ z ∈ S₁.filter (fun z => cmin < inner2 n z),
          t • ((0 : ℤ), (1 : ℤ)) + z ∈ R ∧
            t • ((0 : ℤ), (1 : ℤ)) + z + c • ((1 : ℤ), (0 : ℤ)) ∈ R) := by
  obtain ⟨R, R', c, τ, hR, hR', hRR', hc, hall⟩ := conj14_free_of_side S₁
  exact ⟨R, R', c, τ, hR, hR', hRR', hc, fun _ _ _ =>
    ⟨conj14_antitone (Finset.filter_subset _ _) hall,
      conj14_antitone (Finset.filter_subset _ _) hall⟩⟩

end SideFree

/-! ### §5.1 Conjunct 15: the same instance holds at one end and fails at the other

⚠ **Packaging, not a new fact.**  Both halves are already in §4 — the positive half is
`SideData.hstraddle` of `witness`, the negative half is `conj15_not_stable_under_neg`.  What
`conj15_free_of_side` adds is that they hold *of one and the same instance*, with conjuncts
9, 10, 11, 12, 13 and both halves of conjunct 4 discharged alongside, so that "neither end is
forced" is a single quotable statement for conjunct 15 as it is for conjunct 14.

Note the asymmetry with §5's main result: for conjunct 14 the freedom is **universal in `S₁`**
(`conj14_both_cuts_realisable`), for conjunct 15 it is only **exhibited on one instance**.  The
difference is real and is not an artefact of effort: conjunct 15 has `R` in a hypothesis and
`R'` in its conclusion, so the half-plane trick of `conj14_free_of_side` — enlarge `R` until
conjunct 14 is free — makes conjunct 15 *harder*, not easier.
-/

/-- **Conjunct 15 does not pin the side either.**  One instance, satisfying conjuncts 4, 9, 10,
11, 12 and 13, at which conjunct 15 fails at the `cmax` cut and holds at the `cmin` cut.
Reading the same instance with the opposite normal (`conj15_not_stable_under_neg`) exchanges
the two, so neither end is universally dead. -/
theorem conj15_free_of_side :
    ∃ (ξ' : Config ℤ) (S₁ : Finset (ℤ × ℤ)) (n : ℝ × ℝ) (cmax cmin : ℝ) (u u' : ℤ × ℤ)
      (R R' : Set (ℤ × ℤ)) (c τ : ℤ),
      IsRegion R u u' ∧ n ≠ 0 ∧ inner2 n u' = 0 ∧ cmin < cmax ∧
      (∀ z ∈ S₁, inner2 n z ≤ cmax) ∧ (∀ z ∈ S₁, cmin ≤ inner2 n z) ∧
      (Nivat.R2.face S₁ n cmax).Nonempty ∧ (Nivat.R2.face S₁ n cmin).Nonempty ∧
      c ≠ 0 ∧ PeriodOn ξ' R (c • u) ∧ R ⊂ R' ∧ ¬ PeriodOn ξ' R' (c • u) ∧
      ¬ (∀ g ∈ S₁, g ∉ S₁.filter (fun z => inner2 n z < cmax) → ∀ t₀ : ℤ, τ ≤ t₀ →
          PeriodOn ξ' R (c • u) →
          (∀ t : ℤ, t₀ ≤ t → ξ' (t • u' + g + c • u) = ξ' (t • u' + g)) →
          PeriodOn ξ' R' (c • u)) ∧
      (∀ g ∈ S₁, g ∉ S₁.filter (fun z => cmin < inner2 n z) → ∀ t₀ : ℤ, τ ≤ t₀ →
          PeriodOn ξ' R (c • u) →
          (∀ t : ℤ, t₀ ≤ t → ξ' (t • u' + g + c • u) = ξ' (t • u' + g)) →
          PeriodOn ξ' R' (c • u)) := by
  refine ⟨wX, wS, wNneg, 0, -1, ((1 : ℤ), (0 : ℤ)), ((0 : ℤ), (1 : ℤ)), upperQuad, wR', 1, 1,
    isRegion_upperQuad, by simp [wNneg, Prod.ext_iff], by rw [wNneg_inner2]; norm_num,
    by norm_num, ?_, ?_, ?_, ?_, by decide, witness.hRper, witness.hRR', witness.hnonper,
    ?_, ?_⟩
  · intro z hz
    rcases wS_mem hz with rfl | rfl <;> · rw [wNneg_inner2]; norm_num
  · intro z hz
    rcases wS_mem hz with rfl | rfl <;> · rw [wNneg_inner2]; norm_num
  · exact ⟨(0, 0), Nivat.R2.mem_face.mpr ⟨by simp [wS], by rw [wNneg_inner2]; norm_num⟩⟩
  · exact ⟨(-1, 0), Nivat.R2.mem_face.mpr ⟨by simp [wS], by rw [wNneg_inner2]; norm_num⟩⟩
  · intro h
    refine witness.hnonper (h ((0 : ℤ), (0 : ℤ)) (by simp [wS]) ?_ 1 (le_refl 1)
      witness.hRper ?_)
    · rw [Finset.mem_filter]
      rintro ⟨-, hlt⟩
      rw [wNneg_inner2] at hlt
      norm_num at hlt
    · intro t _
      rw [w_cu, w_col t 0]
      have e : ((0 : ℤ), t) + ((1 : ℤ), (0 : ℤ)) = ((1 : ℤ), t) := by
        rw [Prod.ext_iff]; constructor <;> norm_num
      rw [e]
      show wX ((1 : ℤ), t) = wX ((0 : ℤ), t)
      simp only [wX]
      rw [if_neg (show ¬((1 : ℤ) = -1) by omega), if_neg (show ¬((0 : ℤ) = -1) by omega)]
  · intro g hg hgQ t₀ ht₀ _ heq
    exfalso
    have hg1 : g = ((-1 : ℤ), (0 : ℤ)) := by
      rcases wS_mem hg with rfl | rfl
      · rfl
      · exact absurd (Finset.mem_filter.mpr ⟨hg, by rw [wNneg_inner2]; norm_num⟩) hgQ
    subst hg1
    have h := heq t₀ (le_refl t₀)
    rw [w_cu, w_col t₀ (-1)] at h
    have e : ((-1 : ℤ), t₀) + ((1 : ℤ), (0 : ℤ)) = ((0 : ℤ), t₀) := by
      rw [Prod.ext_iff]; constructor <;> norm_num
    rw [e] at h
    simp only [wX] at h
    simp only [if_true] at h
    omega

/-! ## §6 The conjunct-16 bridge with the offset pinned: still dead, but for a sharper reason

§1 refuted "conjunct 16 + `IsRegion` ⟹ conjunct 14" with the base point `b` **unconstrained**.
`ofEdgeRun` (`L1Fields.lean:165-205`) pins it: `B := {z₀}`, and `z₀` carries `h0 : z₀ ∈ S₁`,
`hlo : inner2 n z₀ < cmax` (so `z₀ ∈ Q`) and `hL : z₀ + (pw - 1) • u' ∈ S₁`.  §1's witness does
**not** survive that pinning — there `b = (0,1)` while `S₁ = {(0,0)}`, so `b ∉ S₁`.  The question
therefore had to be re-asked, not re-read.

**Answer: the bridge is still dead** (`conj16_bridge_dead_with_pinned_base`), and the refutation
carries every one of the pinning hypotheses, `τ` existentially quantified so the producer is
free to push the threshold as high as it likes.

**The sharper reason.**  The obstruction is not that the offset is arbitrary; it is that the
offset is not a multiple of `u'`.  Conjunct 16 gives the `u'`-column through `z₀ + z`
(`base_ray_mem`); conjunct 14 wants the column through `z`.  Those are the same column exactly
when `z₀ ∈ ℤ • u'`, and `conj16_bridge_of_base_on_u'_line` compiles that: once the base point
lies on the `u'`-line through the origin, conjunct 16 plus lattice-convexity **does** give
conjunct 14's first half, with `τ := m` explicit; add `0 < c` and a `u`-ray and it gives both
halves (`conj16_bridge_full_of_base_on_u'_line`).

⚠ `z₀ ∈ ℤ • u'` is **sufficient, not necessary** — `rightHalf` is itself `u'`-invariant, so on
that region conjunct 14 holds for every base point (§5).  And nothing in `ofEdgeRun` supplies
`z₀ ∈ ℤ • u'`: `z₀` is a run start inside `S₁`, and `u'` is the edge direction, so the demand is
a genuine extra hypothesis, not a re-reading of one that is already there.

The witness: `S₁ = {(0,0), (1,0), (2,0)}`, normal `(1,0)` (so `inner2 n z = z.1`), `cmax = 2` —
attained at `(2,0)`, so conjunct 4's face is nonempty — `z₀ = (1,0)`, which is in `S₁` and in
`Q = {(0,0), (1,0)}`, `pw = 1` so `hL` is `h0`, and `R = rightHalf 1`.  Conjunct 16 holds:
`z₀ + z` has first coordinate `1 + z.1 ≥ 1`.  Conjunct 14 fails at `z = (0,0) ∈ Q` for **every**
`t`, because the whole column `(0, t)` misses `R`.
-/

section PinnedBase

/-- The window for §6: three collinear points, the outer one carrying the maximal face. -/
private def bS : Finset (ℤ × ℤ) := {((0 : ℤ), (0 : ℤ)), ((1 : ℤ), (0 : ℤ)), ((2 : ℤ), (0 : ℤ))}

private theorem bS_mem {z : ℤ × ℤ} (hz : z ∈ bS) :
    z = ((0 : ℤ), (0 : ℤ)) ∨ z = ((1 : ℤ), (0 : ℤ)) ∨ z = ((2 : ℤ), (0 : ℤ)) := by
  simpa [bS] using hz

/-- **The conjunct-16 bridge does not survive pinning the base to `ofEdgeRun`'s `z₀`.**

Every hypothesis `ofEdgeRun` attaches to `z₀` is carried — `z₀ ∈ S₁`, `inner2 n z₀ < cmax`
(i.e. `z₀ ∈ Q`), `z₀ + (pw - 1) • u' ∈ S₁` — together with conjuncts 4, 5, 6, 9, 11 and 16, and
`τ` is existentially quantified, so the producer may choose the threshold after seeing the data.
Conjunct 14 still fails. -/
theorem conj16_bridge_dead_with_pinned_base :
    ¬ (∀ (S₁ : Finset (ℤ × ℤ)) (n : ℝ × ℝ) (cmax : ℝ) (u u' z₀ : ℤ × ℤ)
        (R : Set (ℤ × ℤ)) (c : ℤ) (pw : ℕ),
        IsRegion R u u' → n ≠ 0 → inner2 n u' = 0 →
        (∀ z ∈ S₁, inner2 n z ≤ cmax) → (Nivat.R2.face S₁ n cmax).Nonempty →
        inner2 n z₀ < cmax → z₀ ∈ S₁ → z₀ + ((pw : ℤ) - 1) • u' ∈ S₁ →
        det u u' ≠ 0 → Primitive u' → c ≠ 0 →
        (∀ z ∈ S₁, z₀ + z ∈ R) →
        ∃ τ : ℤ, ∀ t : ℤ, τ ≤ t → ∀ z ∈ S₁.filter (fun z => inner2 n z < cmax),
          t • u' + z ∈ R ∧ t • u' + z + c • u ∈ R) := by
  intro h
  obtain ⟨τ, hτ⟩ := h bS wNneg 2 ((1 : ℤ), (0 : ℤ)) ((0 : ℤ), (1 : ℤ)) ((1 : ℤ), (0 : ℤ))
    (rightHalf 1) 1 1
    (isRegion_rightHalf 1)
    (by simp [wNneg, Prod.ext_iff])
    (by rw [wNneg_inner2]; norm_num)
    (by
      intro z hz
      rcases bS_mem hz with rfl | rfl | rfl <;> · rw [wNneg_inner2]; norm_num)
    ⟨(2, 0), Nivat.R2.mem_face.mpr ⟨by simp [bS], by rw [wNneg_inner2]; norm_num⟩⟩
    (by rw [wNneg_inner2]; norm_num)
    (by simp [bS])
    (by
      have e : ((1 : ℤ), (0 : ℤ)) + (((1 : ℕ) : ℤ) - 1) • ((0 : ℤ), (1 : ℤ))
          = ((1 : ℤ), (0 : ℤ)) := by
        rw [Prod.ext_iff]; constructor <;> norm_num
      rw [e]
      simp [bS])
    (by decide)
    isCoprime_one_right
    (by decide)
    (by
      intro z hz
      rw [mem_rightHalf]
      have e : (((1 : ℤ), (0 : ℤ)) + z).1 = 1 + z.1 := rfl
      rw [e]
      rcases bS_mem hz with rfl | rfl | rfl <;> norm_num)
  have hmem : ((0 : ℤ), (0 : ℤ)) ∈ bS.filter (fun z => inner2 wNneg z < 2) :=
    Finset.mem_filter.mpr ⟨by simp [bS], by rw [wNneg_inner2]; norm_num⟩
  have hbad := (hτ τ (le_refl τ) _ hmem).1
  rw [w_col τ 0, mem_rightHalf] at hbad
  have : (1 : ℤ) ≤ 0 := hbad
  omega

/-- **When the base point *is* on the `u'`-line, the bridge works.**

`base_ray_mem` gives the `u'`-column through `m • u' + z`; when the offset is `m • u'` that is
the column through `z` shifted by `m`, so conjunct 14's first half holds from `τ := m` on.  This
is the exact boundary of `conj16_bridge_dead_with_pinned_base`: the obstruction is the component
of `z₀` transverse to `u'`, not the mere presence of an offset. -/
theorem conj16_bridge_of_base_on_u'_line {R : Set (ℤ × ℤ)} (hR : IsLatticeConvexRegion R)
    {zr u' : ℤ × ℤ} (hray : RayIn R zr u') {S₁ : Finset (ℤ × ℤ)} {m : ℤ}
    (hbase : ∀ z ∈ S₁, m • u' + z ∈ R) :
    ∀ t : ℤ, m ≤ t → ∀ z ∈ S₁, t • u' + z ∈ R := by
  intro t ht z hz
  obtain ⟨k, hk⟩ : ∃ k : ℕ, t = m + (k : ℤ) := ⟨(t - m).toNat, by omega⟩
  have h := base_ray_mem hR hray hbase z hz k
  have e : m • u' + z + (k : ℤ) • u' = t • u' + z := by
    rw [hk, add_smul]
    abel
  rwa [e] at h

/-- Both halves of conjunct 14, on the same boundary, at the price of `0 < c` — which §1
(`hline_not_free_even_at_zero_offset`) shows cannot be dropped. -/
theorem conj16_bridge_full_of_base_on_u'_line {R : Set (ℤ × ℤ)}
    (hR : IsLatticeConvexRegion R) {zr zu u u' : ℤ × ℤ}
    (hray : RayIn R zr u') (hrayu : RayIn R zu u)
    {S₁ : Finset (ℤ × ℤ)} {m c : ℤ} (hc : 0 < c)
    (hbase : ∀ z ∈ S₁, m • u' + z ∈ R) :
    ∀ t : ℤ, m ≤ t → ∀ z ∈ S₁, t • u' + z ∈ R ∧ t • u' + z + c • u ∈ R := by
  intro t ht z hz
  have h := conj16_bridge_of_base_on_u'_line hR hray hbase t ht z hz
  exact ⟨h, add_pos_smul_mem hR hrayu hc h⟩

end PinnedBase

end Nivat.L1Straddle
