/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.Claim43
import Nivat.Section8.RegionUpgrade

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# The swept seed: `SweptSweepData`, the repair of `SweepData.window`

Landed 2026-09-18 from four `tmp/` receipts (`swept_landing.lean`,
`seed_subset_R_discharge.lean`, `L1_pw_alt.lean`, `L3ladder_outer.lean`), all of which had
been checked with `bash scripts/check1.sh` at EXIT=0 with clean `#print axioms`.

## Why this exists

`Nivat.Colle43.SweepData.window` (`Claim43.lean:522-525`) builds its window condition on the
bare half-strip `halfStripFrom B u' t₁`.  That encoding is **refuted**: the row-0 pigeonhole
argument shows that at row `0`, column `0`, both image sets are empty *by construction*, so
`window` is maximally tight there for **any** `enum`; a fat `𝒮₁` cannot satisfy it.  See
`blueprint/LEAF-L3.md` for the two independent routes to that conclusion.

The repair is `SweptSweepData` below: the seed becomes the swept set
`sweptSeed B u' t₁ h := {z | ∃ ι : ℕ, z + ι • h ∈ halfStripFrom B u' t₁}`, i.e. the union of
all backward `h`-translates of the half-strip.  Both the `window` and `covers` conditions only
get **weaker** when the seed grows, so this is an addition, not a mutation: `SweepData.toSwept`
converts every old datum into a new one, and `hsweep_of_sweptSweepData`'s conclusion is
*verbatim* that of `hsweep_of_sweepData` (`Claim43.lean:606-611`), a drop-in replacement at the
`case1_sweep` call site (`RegionSteps.lean:1155-1166`).

## ⚠ Scope of the union (待裁决 #2, settled 2026-09-18)

`b3_colle2.txt:694` fixes **one** sufficiently large `ι` ("Let `ι ∈ ℕ` be large enough so that
`(H_Q − ih) ∩ (H_𝒯 + rh') ≠ ∅` for all `i ≥ ι − |𝒯|`"); the seed of Collé's induction is
`ℓ₁ ∩ (H_Q − ι h)` for that single `ι`, and the expansion along `ℓ₁` runs on the generating-set
property, not on enlarging `ι`.  **So `sweptSeed`'s union over all `ι : ℕ` is an upper
approximation we chose, not a literal reading of (4.4).**  The direction is safe (a larger seed
weakens every obligation, the bridge being `halfStripFrom_subset_sweptSeed`), but do not cite
(4.4) as *requiring* the union.

## What this file does **not** close

`case1_sweep` (`RegionSteps.lean:1077`) stays open.  Of `SweptSweepData`'s four fields beyond
`SweepData`:

* `h`, `h_periodOn_R` — free, via `exists_neg_nsmul_period` from `case1_sweep`'s `hRper`/`hc`;
* `seed_subset_R` — free, via `sweptSeed_subset_R` ∘ `halfStripFrom_subset_R` (this file);
* `enum`/`window`/`covers` — **Collé's ladder induction, still unformalised**, except that
  `window` is now discharged from per-row run data by `window_of_runs` (the run data itself,
  `hSrun`/`hrow`, has no producer; see 待裁决 #5).
-/

namespace Nivat.Colle43

open Nivat Nivat.Colle Nivat.Colle41

/-! ## §1  The swept seed -/

/-- Collé's base region for the Claim 4.3 induction, as an **upper approximation**: the
half-strip swept by every non-negative multiple of the `ℓ`-period `h` (`b3_colle2.txt:684`
introduces `h`; `:692` is equation (4.4), which quantifies over a single large `ι` — see the
module docstring's scope note). -/
def sweptSeed (B : Finset (ℤ × ℤ)) (u' : ℤ × ℤ) (t₁ : ℤ) (h : ℤ × ℤ) : Set (ℤ × ℤ) :=
  {z | ∃ ι : ℕ, z + (ι : ℤ) • h ∈ halfStripFrom B u' t₁}

/-- **The bridge: the swept window condition is weaker.**  `ι := 0`. -/
theorem halfStripFrom_subset_sweptSeed (B : Finset (ℤ × ℤ)) (u' : ℤ × ℤ) (t₁ : ℤ)
    (h : ℤ × ℤ) : halfStripFrom B u' t₁ ⊆ sweptSeed B u' t₁ h := by
  intro z hz
  exact ⟨0, by simpa using hz⟩

/-- The half-strip is closed under forward `u'`-shifts. -/
theorem halfStripFrom_add_nsmul {B : Finset (ℤ × ℤ)} {u' : ℤ × ℤ} {t₁ : ℤ} {z : ℤ × ℤ}
    (hz : z ∈ halfStripFrom B u' t₁) (m : ℕ) :
    z + (m : ℤ) • u' ∈ halfStripFrom B u' t₁ := by
  obtain ⟨g, hg, t, ht, rfl⟩ := hz
  refine ⟨g, hg, t + (m : ℤ), by omega, ?_⟩
  rw [add_smul]
  abel

/-! ## §2  Agreement on the swept seed -/

/-- Walking back along `h` inside the seed is invisible to `x`, because `h` is a period of
`x|R` and every intermediate point stays in the seed, hence in `R`.  This is the content that
`b3_colle2.txt:694`'s *"∀ ι ∈ ℕ"* hides. -/
theorem sweptSeed_shift_invariant {A : Type*} {x : Config A}
    {B : Finset (ℤ × ℤ)} {u' : ℤ × ℤ} {t₁ : ℤ} {h : ℤ × ℤ} {R : Set (ℤ × ℤ)}
    (hseedR : sweptSeed B u' t₁ h ⊆ R)
    (hper : ∀ z ∈ R, z + h ∈ R → x (z + h) = x z) :
    ∀ (ι : ℕ) (z : ℤ × ℤ), z + (ι : ℤ) • h ∈ halfStripFrom B u' t₁ →
      x z = x (z + (ι : ℤ) • h) := by
  intro ι
  induction ι with
  | zero => intro z _; simp
  | succ ι ih =>
    intro z hz
    have hsplit : z + ((ι + 1 : ℕ) : ℤ) • h = (z + h) + (ι : ℤ) • h := by
      push_cast
      rw [add_smul, one_smul]
      abel
    have hz' : (z + h) + (ι : ℤ) • h ∈ halfStripFrom B u' t₁ := by rw [← hsplit]; exact hz
    have hzR : z ∈ R := hseedR ⟨ι + 1, hz⟩
    have hzhR : z + h ∈ R := hseedR ⟨ι, hz'⟩
    have hstep : x (z + h) = x z := hper z hzR hzhR
    have := ih (z + h) hz'
    rw [hsplit, ← this, hstep]

/-- **The seed of the sweep on the swept region**, i.e. (4.4) with the `∀ ι ∈ ℕ`.

Same conclusion shape as `agree_T_on_halfStripFrom` (`Claim43.lean:401-404`), on the strictly
larger set `sweptSeed`.  Consumes `hqper` (the `q`-antecedent of `case1_sweep`'s conclusion)
and the `ℓ`-period of `x|R`. -/
theorem agree_T_on_sweptSeed {A : Type*} {x : Config A}
    {B : Finset (ℤ × ℤ)} {u' : ℤ × ℤ} {t₁ : ℤ} {q : ℕ} {h : ℤ × ℤ} {R : Set (ℤ × ℤ)}
    (hqper : ∀ g ∈ B, ∀ t : ℤ, t₁ ≤ t → x (g + (t + (q : ℤ)) • u') = x (g + t • u'))
    (hseedR : sweptSeed B u' t₁ h ⊆ R)
    (hper : ∀ z ∈ R, z + h ∈ R → x (z + h) = x z)
    (m : ℕ) :
    ∀ z ∈ sweptSeed B u' t₁ h, x z = T (((m * q : ℕ) : ℤ) • u') x z := by
  rintro z ⟨ι, hw⟩
  set w : ℤ × ℤ := z + (ι : ℤ) • h with hwdef
  set h' : ℤ × ℤ := ((m * q : ℕ) : ℤ) • u' with hh'
  have hshift := sweptSeed_shift_invariant hseedR hper
  -- `x z = x w`
  have e1 : x z = x w := hshift ι z hw
  -- `w + h'` is still in the strip, and `x` agrees with its `h'`-translate there.
  have hwh' : w + h' ∈ halfStripFrom B u' t₁ := by
    rw [hh']
    exact halfStripFrom_add_nsmul hw (m * q)
  have e2 : x w = x (w + h') := agree_T_on_halfStripFrom hqper m w hw
  -- `x (z + h') = x (w + h')`
  have e3 : x (z + h') = x (w + h') := by
    have hz' : (z + h') + (ι : ℤ) • h ∈ halfStripFrom B u' t₁ := by
      have e : (z + h') + (ι : ℤ) • h = w + h' := by rw [hwdef]; abel
      rw [e]; exact hwh'
    have := hshift ι (z + h') hz'
    have e : (z + h') + (ι : ℤ) • h = w + h' := by rw [hwdef]; abel
    rwa [e] at this
  show x z = x (z + h')
  rw [e1, e2, e3]

/-! ## §3  The replacement data and `hsweep`, with the engine untouched -/

/-- **`SweepData` with Collé's actual seed.**  Identical to `SweepData`
(`Claim43.lean:529-548`) except that `halfStripFrom B u' t₁` is replaced by
`sweptSeed B u' t₁ h` in `window` and `covers`, and the `ℓ`-period `h` of `x|R` is carried with
its two side conditions.  Both replacements *weaken* the condition (§1 bridge), so this is an
addition, not a mutation. -/
structure SweptSweepData {A : Type*} (η x : Config A) (u u' : ℤ × ℤ)
    (R : Set (ℤ × ℤ)) (B : Finset (ℤ × ℤ)) (t₁ : ℤ) (q : ℕ) where
  K : Set (ℤ × ℤ)
  subset_R : K ⊆ R
  isRegion : IsRegion K u u'
  nonempty : K.Nonempty
  t₀ : ℕ
  t₀_pos : 0 < t₀
  S : Finset (ℤ × ℤ)
  a : ℤ × ℤ
  generates : GeneratesAt η S a
  /-- The period `h` of `x|ℛ` parallel to `ℓ` (`b3_colle2.txt:684`, *"Indeed, let h ∈ ℤ²…"*;
  `:692` is equation (4.4) that consumes it): in `case1_sweep` this is `c • u`, supplied by
  `hRper`. -/
  h : ℤ × ℤ
  seed_subset_R : sweptSeed B u' t₁ h ⊆ R
  h_periodOn_R : ∀ z ∈ R, z + h ∈ R → x (z + h) = x z
  enum : ℕ → ℕ → ℤ × ℤ
  window : ∀ i j : ℕ, ∀ z ∈ S.erase a,
    z + (enum i j - a) ∈
      sweptSeed B u' t₁ h ∪ (⋃ i' ∈ {i' | i' < i}, Set.range (enum i'))
        ∪ (enum i '' {j' | j' < j})
  covers : K ⊆ sweptSeed B u' t₁ h ∪ (⋃ i, Set.range (enum i))

/-- **The bridge.**  A `SweepData` plus the period data it never carried is a
`SweptSweepData`: the window and coverage conditions only got weaker. -/
def SweepData.toSwept {A : Type*} {η x : Config A} {u u' : ℤ × ℤ}
    {R : Set (ℤ × ℤ)} {B : Finset (ℤ × ℤ)} {t₁ : ℤ} {q : ℕ}
    (d : SweepData η x u u' R B t₁ q) (h : ℤ × ℤ)
    (hseedR : sweptSeed B u' t₁ h ⊆ R)
    (hper : ∀ z ∈ R, z + h ∈ R → x (z + h) = x z) :
    SweptSweepData η x u u' R B t₁ q where
  K := d.K
  subset_R := d.subset_R
  isRegion := d.isRegion
  nonempty := d.nonempty
  t₀ := d.t₀
  t₀_pos := d.t₀_pos
  S := d.S
  a := d.a
  generates := d.generates
  h := h
  seed_subset_R := hseedR
  h_periodOn_R := hper
  enum := d.enum
  window := by
    intro i j z hz
    exact Set.union_subset_union_left _
      (Set.union_subset_union_left _ (halfStripFrom_subset_sweptSeed B u' t₁ h))
      (d.window i j z hz)
  covers := by
    refine subset_trans d.covers ?_
    exact Set.union_subset_union_left _ (halfStripFrom_subset_sweptSeed B u' t₁ h)

/-- **`hsweep` from `SweptSweepData`.**  The conclusion is *verbatim* that of
`hsweep_of_sweepData` (`Claim43.lean:606-611`), so this is a drop-in replacement at the
`case1_sweep` call site.

The proof calls the **existing** engine `claim43_periodOn_of_sweep` (`Claim43.lean:435`)
unchanged — it is already generic in the seed `D`.  The only new input is
`agree_T_on_sweptSeed`. -/
theorem hsweep_of_sweptSweepData {A : Type*} {η x : Config A} (hx : x ∈ orbitClosure η)
    {u u' : ℤ × ℤ} {R : Set (ℤ × ℤ)} {B : Finset (ℤ × ℤ)} {t₁ : ℤ} {q : ℕ}
    (d : SweptSweepData η x u u' R B t₁ q)
    (hqper : ∀ g ∈ B, ∀ t : ℤ, t₁ ≤ t → x (g + (t + (q : ℤ)) • u') = x (g + t • u')) :
    ∃ K : Set (ℤ × ℤ), K ⊆ R ∧ IsRegion K u u' ∧ K.Nonempty ∧
      ∃ t₀ : ℕ, 0 < t₀ ∧ PeriodOn x K (((t₀ * q : ℕ) : ℤ) • u') := by
  refine ⟨d.K, d.subset_R, d.isRegion, d.nonempty, d.t₀, d.t₀_pos, ?_⟩
  exact claim43_periodOn_of_sweep hx d.generates (((d.t₀ * q : ℕ) : ℤ) • u')
    (agree_T_on_sweptSeed hqper d.seed_subset_R d.h_periodOn_R d.t₀) d.enum d.window d.covers

/-! ## §4  Discharging `seed_subset_R` and `h_periodOn_R`

⚠ `PeriodOn.neg` is **not** restated here: it has been in the tree since
`Lemma41.lean:666`.  The `tmp/seed_subset_R_discharge.lean` receipt carried a duplicate copy;
it was dropped at landing time (`PROTOCOL.md` §3, 「仓里早有」).
-/

/-- A ray in direction `u` from one point of a lattice-convex region gives a ray in direction
`n • u` from every point (`rec_of_rayIn`, `Claim414EllPrime.lean:35`, iterated). -/
theorem ray_all_of_rayIn {R : Set (ℤ × ℤ)} (hR : IsLatticeConvexRegion R)
    {z₀ u : ℤ × ℤ} (hray : RayIn R z₀ u) (n : ℕ) :
    ∀ z ∈ R, ∀ k : ℕ, z + (k : ℤ) • ((n : ℤ) • u) ∈ R := by
  intro z hz k
  have hrec : toReal ((n : ℤ) • u) ∈ recCone R :=
    toReal_mem_recCone_of_nat_ray (hray.nsmul n)
  induction k with
  | zero => simpa using hz
  | succ k ih =>
    have heq : z + ((k + 1 : ℕ) : ℤ) • ((n : ℤ) • u)
        = (z + (k : ℤ) • ((n : ℤ) • u)) + (n : ℤ) • u := by
      push_cast [add_smul]; abel
    rw [heq]
    exact add_mem_of_mem_recCone hR hrec ih

/-- **`seed_subset_R` is dischargeable** once the sweep direction is aligned with the
region's `u`-ray: with `h := -((n : ℤ) • u)` for any `n : ℕ`, the swept seed lies in `R` as
soon as the unswept half-strip does.

The sign matters and is not free to choose twice: `tmp/L3seed_refute.lean` refutes the
`c`-sign-agnostic form (first quadrant, `u = (1,0)`, `c = 1`, with `(−1,0) ∈ sweptSeed ∖ R`).
What makes the aligned form work is that Lean's `u` plays Collé's `−v_ℓ`; see
`blueprint/LEAF-L3.md`'s direction note for the two independent textual anchors
(`b3_colle2.txt:786` and the minus sign in `Q`'s vertex table at `:631`). -/
theorem sweptSeed_subset_R {R : Set (ℤ × ℤ)} {u u' : ℤ × ℤ} {B : Finset (ℤ × ℤ)} {t₁ : ℤ}
    (hR : IsRegion R u u') (n : ℕ)
    (hstrip : halfStripFrom B u' t₁ ⊆ R) :
    sweptSeed B u' t₁ (-((n : ℤ) • u)) ⊆ R := by
  rintro z ⟨ι, hz⟩
  obtain ⟨hconv, ⟨z₀, hray⟩, -⟩ := hR
  have hw : z + (ι : ℤ) • (-((n : ℤ) • u)) ∈ R := hstrip hz
  have := ray_all_of_rayIn hconv hray n _ hw ι
  have heq : z + (ι : ℤ) • (-((n : ℤ) • u)) + (ι : ℤ) • ((n : ℤ) • u) = z := by
    rw [smul_neg]; abel
  rwa [heq] at this

/-- The period datum L3 actually hands to `SweptSweepData.h`: from `hRper : PeriodOn ξ' R (c • u)`
with `c ≠ 0` one gets a *natural* `n > 0` with `PeriodOn ξ' R (-((n : ℤ) • u))`. -/
theorem exists_neg_nsmul_period {A : Type*} {x : Config A} {R : Set (ℤ × ℤ)} {u : ℤ × ℤ}
    {c : ℤ} (hc : c ≠ 0) (hper : PeriodOn x R (c • u)) :
    ∃ n : ℕ, 0 < n ∧ PeriodOn x R (-((n : ℤ) • u)) := by
  rcases lt_or_gt_of_ne hc with hneg | hpos
  · refine ⟨(-c).toNat, by omega, ?_⟩
    have e : -(((-c).toNat : ℤ) • u) = c • u := by
      rw [Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ -c)]; simp
    rw [e]; exact hper
  · refine ⟨c.toNat, by omega, ?_⟩
    have e : -((c.toNat : ℤ) • u) = -(c • u) := by
      rw [Int.toNat_of_nonneg hpos.le]
    rw [e]; exact hper.neg

/-- The unswept half-strip is in `R`, from `hQR` and **`B ⊆ Q`**.

⚠ This is deliberately *not* the `0 < pw` form.  The earlier receipt
(`tmp/seed_subset_R_discharge.lean:94`) took `hpw : 0 < pw` together with `hline` and spent
them at the single instance `hline g hg 0 hpw : g ∈ Q` — i.e. it only ever needed `B ⊆ Q`.
Routing through `0 < pw` was strictly more expensive: the paper's `p' = |𝒮 ∩ ℓ'_𝒮| − 1`
(`b3_colle2.txt:645`) is positive only if `ℓ' ∈ nexpd(η)`, which Collé proves *after* this
step (Claim 4.9, `:870`) using the region this step produces — a circle.  Whereas `B ⊆ Q` is
cheap: it is consumed at a single instance and asks nothing of `pw`.

🔴 **Correction (2026-09-18).**  An earlier version of this docstring claimed that `B ⊆ Q` is
"what `B` literally **is** in the paper", citing `H_Q := {g + t v_{ℓ'} : g ∈ Q ∖ ℓ'_Q,
t ≥ τ + p'}` (`b3_colle2.txt:645`).  **That citation identifies the wrong `Q`.**  The `Q` of
`:645` is a local of Lemma 4.1's own proof: the lattice-convex set spanned by `g'₀`, `g'₁` and
their translates by `-(|𝒮 ∩ ℓ_𝒮| - 1) v_ℓ`, contained in `𝒮` (`:627-633`, Figure 7), used only
to run the counting estimate (4.1) at `:639`.  Case 1's `Q` is a different object, `𝒯 ∖ ℓ'_𝒯`
(`:822`), and Case 1's `B` is a *free existential* with no coverage condition attached to it in
the paper at all.  So `hBQ` here is **Lean-invented debt** (`PROTOCOL.md` §4: Lean can owe
debts the paper never owed), not a transcription of `H_Q`.  Recorded in `blueprint/LEAF-L1.md`.

⚠ The debt changed shape, it did not vanish: L1's existential witness for `B` still has to
hand over `B ⊆ Q`.  L1 has no construction of `B` yet. -/
theorem halfStripFrom_subset_R {R : Set (ℤ × ℤ)} {u u' : ℤ × ℤ} {B Q : Finset (ℤ × ℤ)}
    {τ : ℤ} {c : ℤ} (hBQ : ∀ g ∈ B, g ∈ Q)
    (hQR : ∀ t : ℤ, τ ≤ t → ∀ z ∈ Q, t • u' + z ∈ R ∧ t • u' + z + c • u ∈ R) :
    halfStripFrom B u' τ ⊆ R := by
  rintro z ⟨g, hg, t, ht, rfl⟩
  have hgQ : g ∈ Q := hBQ g hg
  have := (hQR t ht g hgQ).1
  rwa [add_comm] at this

/-- `hline` at `i = 0` gives `B ⊆ Q`, so `halfStripFrom_subset_R`'s hypothesis is **implied
by** the old `0 < pw` + `hline` pair: the replacement is a genuine weakening, not a
strengthening in disguise.

⚠ Only this direction holds.  `B ⊆ Q` does **not** give back `hline`'s `i ≥ 1` instances,
which are still real combinatorial content inside Claim 4.3's induction (conjunct
`RegionSteps.lean:943`). -/
theorem subset_Q_of_hline {B Q : Finset (ℤ × ℤ)} {u' : ℤ × ℤ} {pw : ℕ} (hpw : 0 < pw)
    (hline : ∀ g ∈ B, ∀ i : ℕ, i < pw → g + (i : ℤ) • u' ∈ Q) : ∀ g ∈ B, g ∈ Q := by
  intro g hg
  have := hline g hg 0 hpw
  simpa using this

/-! ## §5  Discharging `window` from per-row run data -/

/-- **`SweptSweepData.window`, discharged from run data.**  Literally the `window` field with
`enum := fun i j => g i + j • w` substituted.

This is the proof body of the outer ladder step (`multi_line_sweep`, `Claim43.lean:362`, wrapped
as `multi_row_sweep_of_runs` in `tmp/L3ladder_outer.lean`) extracted as a standalone lemma:
`hsweep_of_sweptSweepData` consumes `enum`/`window`/`covers` as **fields**, not the end-to-end
sweep conclusion, so the end-to-end wrapper has no call site on this chain.  No `hx`/`hy`/`hD`
appear — the window condition is a purely combinatorial fact about `hSrun`/`hrow`.

⚠ There is **no** `GeneratesAt` hypothesis and no `Config`: the receipt
(`tmp/L3ladder_outer.lean:172`) carried an `hgen` that its proof never used, and the build's
unused-variable linter said so at landing time.  Dropped rather than underscored — the window
condition is a purely combinatorial fact about `hSrun`/`hrow`, and a lemma with fewer
hypotheses is the stronger one.  Call sites pass one fewer argument than the receipt did.

⚠ Direction convention, to be pinned at the call site: `a` is the endpoint of `S` on the
`−v_{ℓ₁}` side, so `hSrun`'s `b = a − k • w` wants `w := −v_{ℓ₁}`.  With `w := +v_{ℓ₁}` the
formula flips to `b = a + k • w`.  The lemma leaves `w` abstract; this is a landing/call-site
commitment (`blueprint/LEAF-L3.md`).

⚠ **`hSrun` has no producer, and §6 now says why it cannot have one.**
`no_hSrun_of_nonCollinear` (§6) shows `hSrun` fails for *every* `a` and `w` as soon as `S`
contains three non-collinear points — which Collé's `𝒮` does (`b3_colle2.txt:774`, Lemma 2.3
gives it edges parallel to both `ℓ` and `−ℓ`).  So this lemma is true but **its antecedent is
unsatisfiable at the intended call site**; the usable form is `window_of_box` (§6).
`exists_face_end_data_gen` (`Claim47Core.lean:159`) never supplied `hSrun` either: it pins
points tied on the same face value, not a run-**width** bound on all of `S.erase a`.  That is
待裁决 #5. -/
theorem window_of_runs
    {S : Finset (ℤ × ℤ)} {a : ℤ × ℤ}
    {w : ℤ × ℤ} {N : ℕ}
    (hSrun : ∀ b ∈ S.erase a, ∃ k : ℕ, 1 ≤ k ∧ k ≤ N ∧ b = a - (k : ℤ) • w)
    {B : Finset (ℤ × ℤ)} {u' : ℤ × ℤ} {t₁ : ℤ} {h : ℤ × ℤ}
    (g : ℕ → ℤ × ℤ)
    (hrow : ∀ i : ℕ, ∀ k : ℕ, k ≤ N →
      g i - (k : ℤ) • w ∈
        sweptSeed B u' t₁ h ∪
          (⋃ i' ∈ {i' : ℕ | i' < i}, Set.range (fun j : ℕ => g i' + (j : ℤ) • w))) :
    ∀ i j : ℕ, ∀ z ∈ S.erase a,
      z + ((fun i j : ℕ => g i + (j : ℤ) • w) i j - a) ∈
        sweptSeed B u' t₁ h ∪
            (⋃ i' ∈ {i' : ℕ | i' < i}, Set.range (fun j : ℕ => g i' + (j : ℤ) • w))
          ∪ ((fun i j : ℕ => g i + (j : ℤ) • w) i '' {j' : ℕ | j' < j}) := by
  intro i j z hz
  obtain ⟨k, hk1, hkN, rfl⟩ := hSrun z hz
  have hshift : (a - (k : ℤ) • w) + (g i + (j : ℤ) • w - a)
      = g i + ((j : ℤ) - (k : ℤ)) • w := by
    module
  show (a - (k : ℤ) • w) + (g i + (j : ℤ) • w - a) ∈ _
  rw [hshift]
  rcases Nat.lt_or_ge j k with hjk | hkj
  · -- `j < k`: falls back into the run behind `g i`, hence into the seed or an earlier row.
    have he : g i + ((j : ℤ) - (k : ℤ)) • w = g i - ((k - j : ℕ) : ℤ) • w := by
      have hcast : ((k - j : ℕ) : ℤ) = (k : ℤ) - (j : ℤ) := by omega
      rw [hcast]; module
    rw [he]
    left
    exact hrow i (k - j) (by omega)
  · -- `k ≤ j`: a strictly earlier point of the very same row, index `j - k < j`.
    right
    refine ⟨j - k, ?_, ?_⟩
    · show j - k < j
      omega
    · show g i + ((j - k : ℕ) : ℤ) • w = g i + ((j : ℤ) - (k : ℤ)) • w
      have hcast : ((j - k : ℕ) : ℤ) = (j : ℤ) - (k : ℤ) := by omega
      rw [hcast]

/-! ## §6  `window_of_runs`'s antecedent is unsatisfiable for the real window, and the
two-dimensional replacement -/

/-- **Three non-collinear points already kill `hSrun`, for every `a` and every `w`.**

This retires `window_of_runs` (§5) as a *mechanism*: `hSrun` forces the whole punctured window
onto a single line through `a`, and Collé's `𝒮` (`b3_colle2.txt:774`) is a genuinely
two-dimensional lattice-convex polygon — it has an edge parallel to `ℓ` *and* one parallel to
`−ℓ` (Lemma 2.3, quoted at `:774`), and a one-dimensional convex set has only one edge
direction in total.

⚠ **Scope.**  This is a legitimate refutation in the sense of `PROTOCOL.md` §9/§11 — a general
implication, not a hand-picked finset.  It refutes the *antecedent* of `window_of_runs` for a
2D `S`; `window_of_runs` itself stays a true, `sorry`-free conditional (and remains usable if
some future call site really does have a collinear punctured window), and the engine
(`multi_line_sweep`, `sweep_induction`) is untouched.  Note the hypothesis refuted here drops
`k ≤ N`, so this is strictly stronger than refuting `window_of_runs`'s own `hSrun`. -/
theorem no_hSrun_of_nonCollinear {S : Finset (ℤ × ℤ)} {p₁ p₂ p₃ : ℤ × ℤ}
    (h₁ : p₁ ∈ S) (h₂ : p₂ ∈ S) (h₃ : p₃ ∈ S)
    (hncol : det (p₂ - p₁) (p₃ - p₁) ≠ 0) :
    ∀ a ∈ S, ∀ w : ℤ × ℤ,
      ¬ (∀ b ∈ S.erase a, ∃ k : ℕ, 1 ≤ k ∧ b = a - (k : ℤ) • w) := by
  intro a _ha w hSrun
  have honline : ∀ b ∈ S, ∃ k : ℤ, b = a - k • w := by
    intro b hb
    by_cases hba : b = a
    · exact ⟨0, by simp [hba]⟩
    · obtain ⟨k, -, hk⟩ := hSrun b (Finset.mem_erase.mpr ⟨hba, hb⟩)
      exact ⟨(k : ℤ), hk⟩
  obtain ⟨k₁, hk₁⟩ := honline p₁ h₁
  obtain ⟨k₂, hk₂⟩ := honline p₂ h₂
  obtain ⟨k₃, hk₃⟩ := honline p₃ h₃
  apply hncol
  have e₂ : p₂ - p₁ = (k₁ - k₂) • w := by rw [hk₁, hk₂]; module
  have e₃ : p₃ - p₁ = (k₁ - k₃) • w := by rw [hk₁, hk₃]; module
  rw [e₂, e₃]
  simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- **`SweptSweepData.window`, discharged from a bounded box behind `a` in two independent
directions.**  Same conclusion shape as `window_of_runs` (§5), with the refuted `hSrun`
replaced by the genuinely 2D `hSbox`, and the rows taken as the arithmetic family
`g₀ + i • w'` — Collé's own `ℓ_{i+1} := ℓ_i^{(−)}` recursion (`b3_colle2.txt:694`) is literally
an arithmetic step in one fixed transverse direction, so this is the paper's shape, not a
simplification.  `w` is the within-row direction (`≈ v_ℓ`, same role as `window_of_runs`'s
`w`); `w'` is the row-stepping direction (`≈ v_{ℓ'}`).

⚠ As in `window_of_runs`, there is **no** `GeneratesAt` hypothesis and no `Config`: the receipt
(`tmp/L3win_halfplane.lean:149`) carried an `hgen` its proof never used and the linter said so.
Call sites pass two fewer arguments than the receipt did.

⚠ **`hbase` is not free, but it is only a *half-line* — read this before citing the lemma.**
It says the seed already contains, for each of the `M` rows immediately behind row `0`, the
`w`-half-line `{ℓ : ℤ | -N ≤ ℓ}`.  That is the price of letting the outer induction start at
`i = 0`: a window reaching back `m` rows from row `i` lands in a real earlier row when `m ≤ i`,
but when `m > i` it lands behind row `0`.  **Whether the real `halfStripFrom`/`sweptSeed` data
contains such half-lines is not addressed here**; `hbase` isolates it as a hypothesis instead of
smuggling it into the conclusion.

⚠ **The `-N ≤ ℓ` bound is load-bearing, do not "simplify" it back to `∀ ℓ : ℤ`.**  The
doubly-infinite form is **refuted**: `Nivat.L3win.no_hbase_of_transverse`
(`tmp/L3win_hbase_refute.lean`, `check1.sh` EXIT=0, axioms clean) shows that whenever
`det u' w ≠ 0`, no doubly-infinite `w`-line fits inside `sweptSeed B u' t₁ h` — project along
`ψ := det u' ·`, which is bounded on one side over the whole seed (uniformly in the finite `B`,
and independent of `t` since `ψ u' = 0`) while the line's `ψ`-value is unbounded in both
directions.  The half-line escapes that argument, which needs unboundedness on the *bounded*
side.  Here `ℓ = j - k` with `k ≤ N` and `j : ℕ`, so `ℓ ≥ -N` always and the proof never
consumes more.  (Receipt for the weakening, including a proof that the old doubly-infinite form
is the special case so nothing was lost: `tmp/L3win_box_halfline.lean`.)

⚠ Writing `b = a - k • w - m • w'` with `k m : ℕ` presupposes that `S`'s offsets from `a` lie
in the sublattice spanned by `w, w'`; a caller must discharge that alongside `hSbox` (free when
`w, w'` are primitive with `det w w' = ±1`, but that is an extra fact —
`Nivat.L3win.hSbox_of_corner` (`tmp/L3win_hSbox_cramer.lean`) produces `hSbox` from
`det w w' = 1` plus a cornerness condition on `a`, which currently has **no known producer**
at the real call site). -/
theorem window_of_box
    {S : Finset (ℤ × ℤ)} {a : ℤ × ℤ}
    {w w' : ℤ × ℤ} {N M : ℕ}
    (hSbox : ∀ b ∈ S.erase a, ∃ k m : ℕ, k ≤ N ∧ m ≤ M ∧ 1 ≤ k + m ∧
      b = a - (k : ℤ) • w - (m : ℤ) • w')
    {B : Finset (ℤ × ℤ)} {u' : ℤ × ℤ} {t₁ : ℤ} {h : ℤ × ℤ}
    (g₀ : ℤ × ℤ)
    (hrow : ∀ i : ℕ, ∀ k : ℕ, k ≤ N →
      g₀ + (i : ℤ) • w' - (k : ℤ) • w ∈
        sweptSeed B u' t₁ h ∪
          (⋃ i' ∈ {i' : ℕ | i' < i}, Set.range (fun j : ℕ => g₀ + (i' : ℤ) • w' + (j : ℤ) • w)))
    (hbase : ∀ p : ℕ, 1 ≤ p → p ≤ M → ∀ ℓ : ℤ, -(N : ℤ) ≤ ℓ →
      g₀ - (p : ℤ) • w' + ℓ • w ∈ sweptSeed B u' t₁ h) :
    ∀ i j : ℕ, ∀ z ∈ S.erase a,
      z + ((fun i j : ℕ => g₀ + (i : ℤ) • w' + (j : ℤ) • w) i j - a) ∈
        sweptSeed B u' t₁ h ∪
          (⋃ i' ∈ {i' : ℕ | i' < i}, Set.range (fun j : ℕ => g₀ + (i' : ℤ) • w' + (j : ℤ) • w))
          ∪ ((fun j : ℕ => g₀ + (i : ℤ) • w' + (j : ℤ) • w) '' {j' : ℕ | j' < j}) := by
  intro i j z hz
  obtain ⟨k, m, hkN, hmM, hkm, rfl⟩ := hSbox z hz
  show (a - (k : ℤ) • w - (m : ℤ) • w') +
      (g₀ + (i : ℤ) • w' + (j : ℤ) • w - a) ∈ _
  have hshift : (a - (k : ℤ) • w - (m : ℤ) • w') + (g₀ + (i : ℤ) • w' + (j : ℤ) • w - a)
      = g₀ + ((i : ℤ) - (m : ℤ)) • w' + ((j : ℤ) - (k : ℤ)) • w := by
    module
  rw [hshift]
  by_cases hmi : m ≤ i
  · -- virtual row index `i' := i - m ≥ 0` is a real row.
    have hcast : (i : ℤ) - (m : ℤ) = ((i - m : ℕ) : ℤ) := by omega
    rw [hcast]
    set i' : ℕ := i - m with hi'def
    by_cases hkj : k ≤ j
    · -- same or earlier row, column `j' := j - k`.
      have hcast2 : (j : ℤ) - (k : ℤ) = ((j - k : ℕ) : ℤ) := by omega
      rw [hcast2]
      set j' : ℕ := j - k with hj'def
      rcases Nat.eq_zero_or_pos m with hm0 | hmpos
      · -- `m = 0`, so `i' = i`: same row, strictly earlier column (needs `k ≥ 1`).
        have hi'eq : i' = i := by omega
        have hj'lt : j' < j := by omega
        rw [hi'eq]
        exact Or.inr ⟨j', hj'lt, rfl⟩
      · -- `m ≥ 1`, so `i' < i`: strictly earlier row.
        have hi'lt : i' < i := by omega
        refine Or.inl (Or.inr ?_)
        exact Set.mem_biUnion hi'lt ⟨j', rfl⟩
    · -- `k > j`: falls back behind row `i'`'s start, handled by `hrow`.
      have hcast2 : (j : ℤ) - (k : ℤ) = -((k - j : ℕ) : ℤ) := by omega
      rw [hcast2]
      have hrowi' := hrow i' (k - j) (by omega)
      have heq : g₀ + (i' : ℤ) • w' - ((k - j : ℕ) : ℤ) • w
          = g₀ + (i' : ℤ) • w' + (-((k - j : ℕ) : ℤ)) • w := by
        rw [neg_smul]; abel
      rw [← heq]
      rcases hrowi' with hseed | hearlier
      · exact Or.inl (Or.inl hseed)
      · refine Or.inl (Or.inr ?_)
        simp only [Set.mem_iUnion] at hearlier ⊢
        obtain ⟨i'', hi'', hmem⟩ := hearlier
        exact ⟨i'', lt_of_lt_of_le hi'' (by omega : i' ≤ i), hmem⟩
  · -- `m > i`: the window reaches behind row `0`, into a fully-seeded virtual row.
    have hcast : (i : ℤ) - (m : ℤ) = -((m - i : ℕ) : ℤ) := by omega
    rw [hcast]
    have hp1 : 1 ≤ m - i := by omega
    have hpM : m - i ≤ M := by omega
    -- `ℓ = j - k ≥ -N`, since `k ≤ N` and `0 ≤ j`: the window never reaches further back
    -- than `N` along `w`, which is why `hbase` only needs a half-line.
    have hlow : -(N : ℤ) ≤ (j : ℤ) - (k : ℤ) := by
      have hk : (k : ℤ) ≤ (N : ℤ) := by exact_mod_cast hkN
      have hj : (0 : ℤ) ≤ (j : ℤ) := Int.natCast_nonneg j
      omega
    have hb := hbase (m - i) hp1 hpM ((j : ℤ) - (k : ℤ)) hlow
    have heq : g₀ - ((m - i : ℕ) : ℤ) • w' + ((j : ℤ) - (k : ℤ)) • w
        = g₀ + (-((m - i : ℕ) : ℤ)) • w' + ((j : ℤ) - (k : ℤ)) • w := by
      rw [neg_smul]; abel
    rw [← heq]
    exact Or.inl (Or.inl hb)

end Nivat.Colle43
