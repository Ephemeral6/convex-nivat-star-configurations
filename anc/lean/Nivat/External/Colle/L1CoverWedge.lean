/-
Copyright (c) 2026 Nivat formalisation project. All rights reserved.
-/
import Nivat.External.Colle.L1RegionBuild
import Nivat.External.Colle.L1StraddleMax
import Nivat.External.Colle.L1Region

/-!
# `MaxBResidual.straddle`'s cover, on `chainFull` (leaf L1, conjunct 15)

Lane Afill's file (exclusive).  Target: the one hypothesis Cconv's `straddle_of_cover`
(`L1StraddleMax.lean:129`, read-only here, only imported) leaves open —

    overlap (F.R (N+1)) (c•u) ⊆ genClosure Sφ a (overlap (F.R N) (c•u) ∪ ray g u' t₀)

— now against `F := ofWedge …` (L1B's `L1RegionBuild.lean`, read-only, only imported), the only
producer still alive per team-lead's ruling: Rsweep's `ofHalfPlanes` needs `hbase` from
`colle_prop_2_10`, whose period is forced parallel to the cutting normal (`inner2 w u = 0`),
which is incompatible with `ofHalfPlanes`'s own `hmu : 0 < dot m u` on that same producer chain.
`ofWedge`'s `hbase`/`hinf` are taken directly (`L1RegionBuild.lean:343-356`), not routed through
`colle_prop_2_10`, so no such obstruction is known against it.

## §1  What is confirmed here: the `overlap`-level residual, on top of L1B's own item 3

L1B has **already landed the row-difference fact themselves**, directly in `L1RegionBuild.lean`
(`chainFull_diff_subset_line`, `:362-369`, explicitly captioned "for Afill's `hcover` in
`L1CoverWedge.lean`") — so no re-proof of that fact belongs here; duplicating it would violate
the file-exclusivity rule from the other direction. What their lemma gives is the containment

    chainFull B vl u' b₀ (N+1) \ chainFull B vl u' b₀ N ⊆
      {z | dot (expNormal u' vl) z = expLevel u' vl b₀ (N + 1)}

i.e. every point newly admitted at step `N+1` sits on a single `u'`-line (a containment, not
claimed as an equality — that direction is not needed here and is not attempted).

What `straddle_of_cover`'s `hcover` actually needs is not about `chainFull` directly but about
`overlap` sets (`overlap R h := {z | z ∈ R ∧ z + h ∈ R}`, `L1StraddleMax.lean:108`). The two are
related but not the same shape: `z ∈ overlap Rhi h \ overlap Rlo h` only forces *one* of `z`,
`z + h` to be new at step `N+1` (the other may already have been in `Rlo`), so the residual can
land on **either** of two lines, not one. `overlap_diff_subset_lines` below makes this precise,
built as a corollary of L1B's `chainFull_diff_subset_line` with no independent geometric content
of its own beyond that case split.

## §2  What is **not** here: the generation data

`subset_genClosure_of_rank` (`MaximalEnveloped.lean:709-724`) is the tool for turning "every
point of a target set is either already known, or is the generating vertex of a window translate
whose other points are known or lower-ranked" into a `genClosure` containment — exactly the
shape a row sweep needs, one point of the line at a time. But instantiating it here needs:

* the generating window `Sφ` and vertex `a` themselves — team-lead's item 2: this is **`𝒮_φ`**,
  reached from `hcase1`'s `d.Sphi` (Figure 11(B)), **not** `S₁`/`hSgen`'s `𝒯` (Figure 11(A), the
  window `ray_period_of_window_period` uses). I do not have `hcase1`'s producer in scope in this
  file — it is case-split data, not a `chainFull`/`wedgeFull` shape fact, and manufacturing it
  from `B`/`vl`/`u'`/`b₀` alone would be exactly the kind of invented-signature mistake the
  project's failure log warns against.
* a rank function on the line (e.g. distance in `u'`-steps from `g`) under which every point not
  already in `ray g u' t₀` is a generation step from lower-ranked points — this is Collé's actual
  geometric argument (Figure 11(B)) and needs `Sφ`'s shape to state, let alone prove.

So this file stops at the exact geometric shape of the residual (§1) plus naming the tool for §2;
it does not attempt the generation step itself. Whoever supplies `hcase1.Sphi`/`hgen` next should
compose it with `overlap_diff_subset_lines` and `subset_genClosure_of_rank` directly — no further
translation of `chainFull`'s shape should be needed after that.

## §3  `hinf`, checked for vacuity first (team-lead's assignment, 2026-09-19)

`hinf : ¬ PeriodOn (T e ξ) (wedgeFull B vl u') (c • vl)` is `ofWedge`'s other genuinely open
hypothesis (`L1RegionBuild.lean:347`).  Team-lead's ordered checklist, worked in order:

**Step 1 — is `wedgeFull B vl u'` ever forced to be the whole plane?**  **No, not in general —
checked directly, negative.**  `wedgeFull B vl u' := sweep (fullSweep B vl) u'`
(`RegionSweep.sweep`, `L1RegionBuild.lean:229`), and `RegionSweep.sweep` is **forward-only**
(`sweep C w := {z | ∃ g ∈ C, ∃ t : ℕ, z = g + (t:ℤ)•w}`, `RegionSweep.lean:76-77` — `t : ℕ`, not
`ℤ`). So even though `fullSweep B vl` already runs both ways along `vl`, the outer `u'`-sweep
only ever adds *non-negative* multiples of `u'`. `not_wedgeFull_univ_singleton` below exhibits
this concretely: for `B := {0}` (a valid instance of every one of `ofWedge`'s shape hypotheses —
`isLatticeConvexRegion_singleton_zero`, `levelInterval_singleton_zero`, both already in
`RegionSweep.lean`), the point `-u'` is **not** in `wedgeFull {0} vl u'` — reaching it would need
a *negative* `u'`-multiple, and Cramer's identity (`det u' vl • z = ...`, unfolded directly here
since `t + 1 = 0` is impossible for `t : ℕ`) rules that out under `hunimod` alone, no periodicity
data involved. **So `wedgeFull B vl u' = Set.univ` is not free — it is a genuine constraint on
`B`'s shape (specifically, on how far `B` extends in the negative-`u'` direction), and whoever's
upstream data supplies the concrete `B` here (leaf A's chain data) would have to certify it. The
cheap route via `periodOn_univ_iff`/`not_periodOn_univ_of_not_isPeriodic`
(`HalfPlaneFamily.lean:48,60`) is not automatically available.** Consequently the "these two
interlock" worry — that `wedgeFull = univ` would force `hbase` to a global (hence false)
periodicity — does not arise on this witness either: `chainFull {0} vl u' 0 0` is a half-plane
cut of `wedgeFull`, not `wedgeFull` itself, whether or not the latter is `univ`; the two facts are
independent for this `B`.

**Step 2 — does `c`'s existential quantification cheapen `hinf`?**  Checked the binder site:
`exists_L1MaxBResidual`'s conclusion (`RegionSteps.lean:1119-1122`) binds `c` **inside** the
outer `∃`, alongside `F`, so yes — the leaf only ever needs *some* `c ≠ 0` with `¬PeriodOn ... (c
• vl)`, not "for all `c`". But this does not hand `hinf` over for free either: `L1Assemble.lean`'s
`MaxBResidual.exists_of_wedge` (`:2126-2159`, already landed, not mine to touch) takes `hinf` as a
**hypothesis**, at a *fixed* `c` chosen by whoever calls it — so the existential freedom on `c` is
real but is exercised by the *caller* (presumably from `hp_ne`/`exists_zsmul_ne_zero_of_parallel`,
`L1Assemble.lean:1888`, which already produces a canonical nonzero `c` from `p`'s primitivity
against `vl`), not by anything provable inside this file without that upstream data either.

**Step 3 — the `False`-guard, before touching `hξ`.**  Since steps 1–2 both come back "genuinely
open, needs upstream data", the honest disposition is: **`hinf` is not vacuous on the evidence
available here**, and no shortcut bypassing `hξ : IsMinimalCounterexample ξ` has been found.
Nothing here disproves `hinf`'s negation either (`¬hinf`, i.e. `PeriodOn (T e ξ) (wedgeFull B vl
u') (c • vl)`, is not shown false) — so this file does not claim `hinf` is unconditionally
provable or unconditionally impossible; it narrows the search to genuinely needing `¬IsPeriodic
ξ` (via `hξ`) *and* the concrete shape of `wedgeFull B vl u'` for the specific `B` leaf A
supplies, which is not in scope here.
-/

set_option autoImplicit false

namespace Nivat.ColleReg

open Nivat Nivat.Colle41 Nivat.LE2 Nivat.L1StraddleMax

variable {B : Set (ℤ × ℤ)} {vl u' b₀ h : ℤ × ℤ}

/-- **The `overlap`-level residual `straddle_of_cover`'s `hcover` has to place inside
`genClosure`**: a point newly in `overlap Rhi h` (but not in `overlap Rlo h`) fails only because
`z` or `z + h` is new at step `N+1` — and each of those, by L1B's `chainFull_diff_subset_line`,
sits on the single line `{z | dot (expNormal u' vl) z = expLevel u' vl b₀ (N+1)}`.  No new
geometric content beyond that case split and L1B's own lemma. -/
theorem overlap_diff_subset_lines (B : Set (ℤ × ℤ)) (vl u' b₀ h : ℤ × ℤ) (N : ℕ) :
    Nivat.L1StraddleMax.overlap (chainFull B vl u' b₀ (N + 1)) h \
        Nivat.L1StraddleMax.overlap (chainFull B vl u' b₀ N) h ⊆
      {z | dot (expNormal u' vl) z = expLevel u' vl b₀ (N + 1)} ∪
        {z | dot (expNormal u' vl) (z + h) = expLevel u' vl b₀ (N + 1)} := by
  rintro z ⟨⟨hz1, hz2⟩, hz3⟩
  rw [Nivat.L1StraddleMax.mem_overlap] at hz3
  by_cases hzR : z ∈ chainFull B vl u' b₀ N
  · exact Or.inr (chainFull_diff_subset_line B vl u' b₀ N ⟨hz2, fun h' => hz3 ⟨hzR, h'⟩⟩)
  · exact Or.inl (chainFull_diff_subset_line B vl u' b₀ N ⟨hz1, hzR⟩)

/-- **§3, step 1's negative witness**: `wedgeFull {0} vl u'` never reaches `-u'` — the outer
sweep in `chainFull`'s construction is forward-only (`RegionSweep.sweep`'s `t : ℕ`), so no
negative `u'`-multiple is ever admitted, for any `B` at all (here witnessed at `B := {0}`). -/
theorem not_wedgeFull_univ_singleton {vl u' : ℤ × ℤ}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) :
    wedgeFull ({(0 : ℤ × ℤ)} : Set (ℤ × ℤ)) vl u' ≠ Set.univ := by
  intro hu
  have hmem : (-u' : ℤ × ℤ) ∈ wedgeFull ({(0 : ℤ × ℤ)} : Set (ℤ × ℤ)) vl u' := hu ▸ Set.mem_univ _
  obtain ⟨g, hg, t, ht⟩ := hmem
  obtain ⟨b, hb, k, hk⟩ := mem_fullSweep_iff.mp hg
  rw [Set.mem_singleton_iff] at hb
  subst hb
  -- `-u' = 0 + k • vl + t • u'`, i.e. `0 = k • vl + (t + 1) • u'`.
  rw [hk] at ht
  have h0 : (0 : ℤ × ℤ) = k • vl + ((t : ℤ) + 1) • u' := by
    have := congrArg (· + u') ht
    simp only [neg_add_cancel] at this
    rw [this]
    module
  have h1 : k * vl.1 + ((t : ℤ) + 1) * u'.1 = 0 := by
    have := congrArg Prod.fst h0
    simpa [Prod.fst_add, Prod.smul_fst, smul_eq_mul] using this.symm
  have h2 : k * vl.2 + ((t : ℤ) + 1) * u'.2 = 0 := by
    have := congrArg Prod.snd h0
    simpa [Prod.snd_add, Prod.smul_snd, smul_eq_mul] using this.symm
  have hkey : ((t : ℤ) + 1) * (u'.1 * vl.2 - u'.2 * vl.1) = 0 := by
    linear_combination vl.2 * h1 - vl.1 * h2
  have htpos : (0 : ℤ) < (t : ℤ) + 1 := by positivity
  rcases hunimod with hd | hd <;>
    (simp only [det] at hd; rw [hd] at hkey; nlinarith)

/-! ## §4  `hinf`'s body: `wedgeFull` contains a half-plane anchored at *any* point of `B`

Team-lead's relayed structural claim (AnfpL) verifies, and turns out **not to need a `B`-boundedness
or minimality hypothesis at all** — it needs only the single point `b₀ ∈ B` that `ofWedge` already
carries.  The mechanism: `ψ := expNormal vl u'` (L1B's own `expNormal`, arguments swapped from the
`expNormal u' vl` that `expLevel` cuts on) satisfies `dot ψ u' = 1`, `dot ψ vl = 0`
(`dot_expNormal_vl`/`dot_expNormal_u'`, args swapped — see `reconstruct` below), so `ψ` is exactly
the coordinate that counts *forward* `u'`-steps.  `reconstruct` shows every lattice point
decomposes as `z = (dot (expNormal u' vl) z) • vl + (dot ψ z) • u'` unconditionally (Cramer's
identity for a unimodular pair, done by hand since `det u' vl ∈ {1,-1}` squares to `1`).  Applying
it to `z - b` for any `b ∈ B` gives the `vl`/`u'` steps taking `b` to `z`; the `u'`-step is
`dot ψ z - dot ψ b`, forward (`t : ℕ`) exactly when `dot ψ b ≤ dot ψ z`.  So **the half-plane
`{z | dot ψ b₀ ≤ dot ψ z}` is a subset of `wedgeFull B vl u'`, for the specific `b₀ ∈ B` `ofWedge`
already binds** — no minimizer needed, `b₀` itself is the anchor.

That is precisely `union_not_of_halfPlane_cover`'s (`L1Region.lean:529`, Proposition 2.12) `hcover`
hypothesis, with `Rf` the constant sequence `wedgeFull B vl u'` (so `⋃ k, Rf k = wedgeFull B vl u'`
by `Set.iUnion_const`) and `w := ψ` cast to `ℝ × ℝ`.  Its `hwu` (period `c • vl` parallel to the
cutting normal) is `dot ψ vl = 0` scaled by `c`, free.  Composing gives `hinf_of_ge` below: `ofWedge`'s
`hinf` is **discharged unconditionally** from `hξ`, `d : DecompDataZ ξ`, `hb₀`, `hunimod` and
`c • vl ≠ 0` — exactly `ofWedge`'s own hypothesis list plus the `hξ`/`d` that `exists_L1MaxBResidual`
(the leaf calling it) already binds. This is the deliverable for team-lead's §3 assignment; it
supersedes §3's "genuinely open" verdict above (kept per §14, not deleted). -/

open Nivat.LE2 in
/-- **Cramer's identity for a unimodular pair, done by hand.**  No hypothesis on `z` — this is an
unconditional decomposition of every lattice point in the `(vl, u')` basis, using L1B's own
`expNormal` with its two arguments swapped in the second summand. -/
theorem reconstruct {u' vl : ℤ × ℤ} (hunimod : det u' vl = 1 ∨ det u' vl = -1) (z : ℤ × ℤ) :
    z = (dot (expNormal u' vl) z) • vl + (dot (expNormal vl u') z) • u' := by
  have hsq : det u' vl * det u' vl = 1 := by rcases hunimod with h | h <;> rw [h] <;> ring
  apply Prod.ext
  · show z.1 = (dot (expNormal u' vl) z) * vl.1 + (dot (expNormal vl u') z) * u'.1
    simp only [expNormal, dot, det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at hsq ⊢
    linear_combination (-z.1) * hsq
  · show z.2 = (dot (expNormal u' vl) z) * vl.2 + (dot (expNormal vl u') z) * u'.2
    simp only [expNormal, dot, det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at hsq ⊢
    linear_combination (-z.2) * hsq

/-- The half-plane `{z | dot (expNormal vl u') b ≤ dot (expNormal vl u') z}`, anchored at *any*
`b ∈ B`, sits inside `wedgeFull B vl u'`.  (Not an iff: other points of `B` may push the true
boundary of `wedgeFull` further out; this direction, the one `hcover` needs, is all that is used.) -/
theorem mem_wedgeFull_of_dot_le {B : Set (ℤ × ℤ)} {vl u' b z : ℤ × ℤ}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) (hb : b ∈ B)
    (hle : dot (expNormal vl u') b ≤ dot (expNormal vl u') z) :
    z ∈ wedgeFull B vl u' := by
  have hrec := reconstruct hunimod (z - b)
  have hφlin : dot (expNormal vl u') (z - b)
      = dot (expNormal vl u') z - dot (expNormal vl u') b := dot_sub _ _ _
  have ht0 : 0 ≤ dot (expNormal vl u') (z - b) := by rw [hφlin]; omega
  have hz : z = (b + (dot (expNormal u' vl) (z - b)) • vl)
      + (dot (expNormal vl u') (z - b)) • u' := by
    rw [add_assoc, ← hrec]; abel
  refine ⟨b + (dot (expNormal u' vl) (z - b)) • vl,
    mem_fullSweep_iff.mpr ⟨b, hb, _, rfl⟩, (dot (expNormal vl u') (z - b)).toNat, ?_⟩
  rw [Int.toNat_of_nonneg ht0]
  exact hz

open Nivat.LE2 in
/-- `dot n z`, cast to `ℝ`, is `inner2` on the real coercion of `n` — the bridge to
`union_not_of_halfPlane_cover`'s real-normal hypotheses. -/
theorem inner2_ofInt (n z : ℤ × ℤ) :
    inner2 ((n.1 : ℝ), (n.2 : ℝ)) z = ((dot n z : ℤ) : ℝ) := by
  simp only [inner2, dot]; push_cast; ring

/-- **`hinf`, discharged.**  `ofWedge`'s `¬ PeriodOn (T e ξ) (wedgeFull B vl u') (c • vl)`, from
exactly the hypotheses `ofWedge` already carries (`hb₀`, `hunimod`) plus `hξ`/`d` — which
`exists_L1MaxBResidual`, the leaf calling `ofWedge`, already binds — and `c • vl ≠ 0`. Via
`union_not_of_halfPlane_cover` (Proposition 2.12) with `Rf` the constant sequence `wedgeFull B vl u'`
and cutting normal `expNormal vl u'`. -/
theorem hinf_of_ge {ξ : Config ℤ} (e : ℤ × ℤ) (hξ : IsMinimalCounterexample ξ)
    (d : Nivat.Colle35.DecompDataZ ξ)
    {B : Set (ℤ × ℤ)} {vl u' b₀ : ℤ × ℤ} {c : ℤ} (hb₀ : b₀ ∈ B)
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) (hcvl : c • vl ≠ 0) :
    ¬ Colle41.PeriodOn (T e ξ) (wedgeFull B vl u') (c • vl) := by
  have hunimod' : det vl u' = 1 ∨ det vl u' = -1 := by
    rw [det_comm vl u']; rcases hunimod with h | h
    · right; omega
    · left; omega
  have h1 : dot (expNormal vl u') vl = 0 := dot_expNormal_u' (u' := vl) (vl := u')
  have h2 : dot (expNormal vl u') u' = 1 := dot_expNormal_vl (u' := vl) (vl := u') hunimod'
  set ψ : ℤ × ℤ := expNormal vl u' with hψdef
  have hψne : ψ ≠ 0 := by
    intro h0
    rw [h0] at h2
    simp only [dot] at h2
    norm_num at h2
  set w : ℝ × ℝ := ((ψ.1 : ℝ), (ψ.2 : ℝ)) with hwdef
  have hw0 : w ≠ 0 := by
    intro h0
    apply hψne
    have h1' : (ψ.1 : ℝ) = 0 := congrArg Prod.fst h0
    have h2' : (ψ.2 : ℝ) = 0 := congrArg Prod.snd h0
    have : ψ.1 = 0 := by exact_mod_cast h1'
    have : ψ.2 = 0 := by exact_mod_cast h2'
    exact Prod.ext ‹ψ.1 = 0› ‹ψ.2 = 0›
  have hwu : inner2 w (c • vl) = 0 := by
    rw [hwdef, inner2_ofInt]
    have : dot ψ (c • vl) = c * dot ψ vl := dot_zsmul_right ψ c vl
    rw [this, h1]
    simp
  have hcover : {z : ℤ × ℤ | dot ψ b₀ ≤ inner2 w z} ⊆ ⋃ _ : ℕ, wedgeFull B vl u' := by
    intro z hz
    rw [Set.mem_setOf_eq, hwdef, inner2_ofInt] at hz
    have hzint : dot ψ b₀ ≤ dot ψ z := by exact_mod_cast hz
    exact Set.mem_iUnion.mpr ⟨0, mem_wedgeFull_of_dot_le hunimod hb₀ hzint⟩
  have := Nivat.L1Region.union_not_of_halfPlane_cover (Rf := fun _ : ℕ => wedgeFull B vl u')
    (w := w) (lvl := ((dot ψ b₀ : ℤ) : ℝ))
    (Nivat.L1Region.periodicDecompZ_T_of_decompDataZ d e) hw0 hcvl hwu hcover hξ.1.2.2.1
  rwa [Set.iUnion_const] at this

/-! ## §5  `hlev` measured against `hcase1`'s real shape (team-lead's assignment, 2026-09-19)

L1B's counterexample (`RegionSweep.lean:396,447`) is `B := {(0,0),(1,2)}`, `vl := (1,0)`:
`IsLatticeConvexRegion B` holds (`isLatticeConvexRegion_pair`) but `¬ LevelInterval B vl`
(`not_levelInterval_pair`). Team-lead's question: does that same `B` survive as a genuine
witness of `Case1 ξ xper S vl` (`CaseSplit.lean:82`), or does `Case1`'s *extra* content over
plain `EnvOf S B` — the half-strip agreement `∃ u, ∀ z ∈ halfStrip B vl, T u ξ z = xper z` —
rule it out?

**Answer: (a), `hlev` is dead under `hcase1`'s true shape too, and cheaply.** `Case1` places no
restriction on `B` beyond `EnvOf S B` that the counterexample can't satisfy for free:

* Take `S := {(0,0),(1,2)} : Finset (ℤ × ℤ)`, so `(S : Set _) = B` literally. `EnvOf S ↑S` is
  `Enveloped ↑S ↑S`, which is `enveloped_refl` applied to `isLatticeConvexRegion_pair` — the
  witness `B` in `Case1`'s existential is just `↑S` itself, no separate object needed.
* Take `xper := ξ` and `u := 0`. The half-strip agreement `∀ z ∈ halfStrip B vl, T 0 ξ z = ξ z`
  is `rfl`-level (`T 0 ξ z = ξ (z + 0) = ξ z`), true on *every* `z`, not just `halfStrip B vl` —
  it costs nothing to satisfy, for *any* `ξ` at all.

So `case1_pair` below produces `Case1 ξ ξ S vl` unconditionally, for every `ξ`, on the exact
same `(S, vl)` pair the counterexample uses — and `not_levelInterval_pair` still applies to the
same `B = ↑S`. **`hcase1`'s extra existential content over `EnvOf` is free to satisfy by choosing
`xper = ξ`, `u = 0`; it adds no leverage against this particular counterexample.** This is not a
claim that `Case1`'s existential is *always* vacuous in the real assembly (there `xper ∈
orbitClosure ξ` and other binders constrain the ambient data) — only that the specific gap
between `EnvOf` and `Case1` that one might hope closes `hlev` does not, because the half-strip
agreement can always be discharged by the trivial choice `xper := ξ`, independent of `B`'s shape.
`hlev` must be sourced from elsewhere (or dropped/weakened), not from `hcase1`. -/

/-! ### ⚠ Reading caveat (team-lead, 2026-09-19)

`case1_pair` / `case1_and_not_levelInterval` show **`hcase1` gives no leverage against `hlev`**,
**not that `hlev` is false**. `hlev`'s status is `OPEN.md #10`, undecided. The one route this
file's counterexample does *not* probe is `S = 𝒮_φ`'s own structure — Collé Lemma 2.6 says
`𝒮_φ` has no edge parallel to `±ℓ`, a constraint neither this counterexample nor L1B's uses.
(Team-lead's reading, not a kernel fact — §25; dispatched to AnfpL to measure.) Do not read the
two theorems below as "`hlev` is dead" in the file-wide sense; they are weaker and that weaker
claim is what is actually true. -/

/-- **`Case1`'s extra content over `EnvOf` is satisfiable for free**, on the exact `(S, vl)` pair
L1B's counterexample uses, for *every* `ξ` (not just a specially chosen one). -/
theorem case1_pair (ξ : Config ℤ) :
    Case1 ξ ξ ({((0 : ℤ), (0 : ℤ)), ((1 : ℤ), (2 : ℤ))} : Finset (ℤ × ℤ)) ((1 : ℤ), (0 : ℤ)) := by
  refine ⟨(({((0 : ℤ), (0 : ℤ)), ((1 : ℤ), (2 : ℤ))} : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)),
    Nivat.LE2.enveloped_refl _ ?_, 0, fun z _ => ?_⟩
  · simpa using Nivat.RegionSweep.isLatticeConvexRegion_pair
  · show ξ (z + (0 : ℤ × ℤ)) = ξ z
    simp

/-- **`hlev` is dead under `hcase1`'s real shape, not just under `EnvOf` alone**: `case1_pair`
and `not_levelInterval_pair` share the same witness `B = ↑{(0,0),(1,2)}`, `vl = (1,0)`. -/
theorem case1_and_not_levelInterval (ξ : Config ℤ) :
    Case1 ξ ξ ({((0 : ℤ), (0 : ℤ)), ((1 : ℤ), (2 : ℤ))} : Finset (ℤ × ℤ)) ((1 : ℤ), (0 : ℤ)) ∧
      ¬ Nivat.RegionSweep.LevelInterval
        (({((0 : ℤ), (0 : ℤ)), ((1 : ℤ), (2 : ℤ))} : Finset (ℤ × ℤ)) : Set (ℤ × ℤ))
        ((1 : ℤ), (0 : ℤ)) :=
  ⟨case1_pair ξ, by simpa using Nivat.RegionSweep.not_levelInterval_pair⟩

/-! ## §6  `hK`, team-lead's assignment (2026-09-19): `hbase`'s covering residual

`Aface.HbaseBridge.hbase_of_sweep` (`HbaseBridge.lean:96`, read-only, only imported) reduces
`hbase` to four named obligations; `hK : chainFull B vl u' b₀ 0 ⊆ D ∪ ⋃ i, Set.range (enum i)`
is the one with half-plane/wedge content — Aface's own docstring flags it as the direction
`Nivat.L1Prim.halfPlaneGE_forward_of_dot_nonneg` serves.

**Unfolding `chainFull B vl u' b₀ 0`** (`L1Region.cut`, `L1RegionBuild.lean:305`, `expLevel`
`:301`): `z ∈ chainFull B vl u' b₀ 0 ↔ z ∈ wedgeFull B vl u' ∧ dot (expNormal u' vl) b₀ ≤
dot (expNormal u' vl) z`. Unfolding `wedgeFull`/`fullSweep` (`mem_fullSweep_iff`), every such
`z` is `b + k • vl + t • u'` for some `b ∈ B`, `k : ℤ`, `t : ℕ`. Since `dot_expNormal_u' :
dot (expNormal u' vl) u' = 0` unconditionally and `dot_expNormal_vl` (under `hunimod`) gives
`dot (expNormal u' vl) vl = 1`, the level constraint becomes exactly `dot (expNormal u' vl) b +
k ≥ dot (expNormal u' vl) b₀`, i.e. `k ≥ dot (expNormal u' vl) b₀ - dot (expNormal u' vl) b` —
one integer lower bound per `b`, no other constraint. So `chainFull B vl u' b₀ 0` is exactly the
union, over `b ∈ B`, of the forward `u'`-swept rays based at `b + k • vl` for every `k` at or
above that bound: **a countable family of forward rays, one per `(b, shift)` pair.**

`enum : ℕ → ℕ → ℤ × ℤ` is shaped for exactly this: `Set.range (enum i)` is meant to be one row
(one ray, `j` the forward-`u'` parameter). Team-lead's read of Aface's note is right — `hK`
is a **containment**, the forward direction `halfPlaneGE_forward_of_dot_nonneg` serves; no
minimality or exactness is asked for, only that *every* `(b, shift)` pair lands in *some* row.

**Construction (uses only `hunimod` — none of `hB`/`hvl`/`hu'`/`hlev`; `B` need not be
finite).** `ℤ × ℤ × ℕ` is countably infinite, so `Denumerable.eqv (ℤ × ℤ × ℕ) : (ℤ × ℤ × ℕ) ≃ ℕ`
gives a bijection `ℕ → ℤ × ℤ × ℕ` — no genericity is lost by *not* filtering the first
component to lie in `B`: a row `enum i` based at a `b ∉ B` simply never gets hit by any `z ∈
chainFull B vl u' b₀ 0` (that direction of the containment is not needed for `hK`), and every
`b ∈ B` still gets visited (since the bijection is onto **all** of `ℤ × ℤ × ℕ`, `B × Set.univ`
included). Row `i`, decoded to `(b, n)`, is based at `b + (dot (expNormal u' vl) b₀ -
dot (expNormal u' vl) b + n) • vl` and swept forward by `u'`.

⚠ **Coordination caveat, not resolved here**: this `coverEnum` is built from raw lattice-point
countability alone, ignoring the generating set `S`/vertex `a` entirely. `hwin` (L3win's) needs
`enum`'s rows to relate to `S`-window translates via `GeneratesAt`/Lemma 2.6 — `coverEnum` almost
certainly does **not** also satisfy `hwin`, since nothing here ties row `i`'s base point to `S`.
**What this section establishes is that `hK` in isolation is never the obstruction** — a
covering `enum` always exists, unconditionally (given `hunimod`), so if `hbase` stays open it is
`hgen`/`hD`/`hwin` carrying the real content, not `hK`. Whoever builds `hwin`'s `enum` (L3win)
would need to verify *their* `enum` (built from the window-generation recursion, not this one)
also satisfies `hK`'s covering — likely by a similar but `S`-aware argument, not by reusing
`coverEnum` verbatim. -/

open Nivat.LE2 in
/-- A bijection `ℕ ≃ (ℤ × ℤ) × ℕ`, used only to enumerate `(base point, vl-shift)` pairs. -/
noncomputable def pairEnum : ℕ → (ℤ × ℤ) × ℕ := (Denumerable.eqv ((ℤ × ℤ) × ℕ)).symm

open Nivat.LE2 in
/-- **A concrete covering `enum` for `chainFull B vl u' b₀ 0`.**  Row `i`, decoded via
`pairEnum` to a pair `(b, n)`, is the forward `u'`-ray based at `b` shifted by
`expLevel`'s threshold plus `n` steps of `vl`. -/
noncomputable def coverEnum (vl u' b₀ : ℤ × ℤ) : ℕ → ℕ → ℤ × ℤ :=
  fun i j =>
    (pairEnum i).1
      + (dot (expNormal u' vl) b₀ - dot (expNormal u' vl) (pairEnum i).1
          + ((pairEnum i).2 : ℤ)) • vl
      + (j : ℤ) • u'

open Nivat.LE2 in
/-- **`hK`'s covering, unconditionally (given `hunimod`).**  No hypothesis on `B` beyond
membership; `B` need not be finite, bounded, or lattice-convex. -/
theorem chainFull_subset_iUnion_range_coverEnum {B : Set (ℤ × ℤ)} {vl u' b₀ : ℤ × ℤ}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) :
    chainFull B vl u' b₀ 0 ⊆ ⋃ i, Set.range (coverEnum vl u' b₀ i) := by
  intro z hz
  obtain ⟨hz1, hz2⟩ := hz
  obtain ⟨g, hg, t, rfl⟩ := hz1
  obtain ⟨b, hb, k, hk⟩ := mem_fullSweep_iff.mp hg
  subst hk
  have hlev0 : expLevel u' vl b₀ 0 = dot (expNormal u' vl) b₀ := by simp [expLevel]
  rw [hlev0] at hz2
  simp only [halfPlaneGE, Set.mem_setOf_eq] at hz2
  have hzcomp : dot (expNormal u' vl) (b + k • vl + (t : ℤ) • u')
      = dot (expNormal u' vl) b + k * dot (expNormal u' vl) vl
        + (t : ℤ) * dot (expNormal u' vl) u' := by
    rw [dot_add, dot_add, dot_zsmul_right, dot_zsmul_right]
  rw [dot_expNormal_u' (u' := u') (vl := vl), dot_expNormal_vl (u' := u') (vl := vl) hunimod,
    mul_zero, add_zero, mul_one] at hzcomp
  rw [hzcomp] at hz2
  set n : ℕ := (k - (dot (expNormal u' vl) b₀ - dot (expNormal u' vl) b)).toNat with hndef
  have hn : (n : ℤ) = k - (dot (expNormal u' vl) b₀ - dot (expNormal u' vl) b) := by
    rw [hndef, Int.toNat_of_nonneg]; omega
  obtain ⟨i, hi⟩ := (Denumerable.eqv ((ℤ × ℤ) × ℕ)).symm.surjective (b, n)
  refine Set.mem_iUnion.mpr ⟨i, t, ?_⟩
  show coverEnum vl u' b₀ i t = b + k • vl + (t : ℤ) • u'
  unfold coverEnum pairEnum
  rw [hi]
  congr 2
  have : k = dot (expNormal u' vl) b₀ - dot (expNormal u' vl) b + (n : ℤ) := by omega
  rw [this]

open Nivat.LE2 in
/-- **`hK` itself, PROTOCOL §27 term** — literally fills `claim43_periodOn_of_sweep`'s
(`Claim43.lean:443`) `hK : K ⊆ D ∪ (⋃ i, Set.range (enum i))` slot (equivalently
`HbaseBridge.hbase_of_sweep`'s `hK`, `HbaseBridge.lean:96`), with `K := chainFull B vl u' b₀ 0`,
`enum := coverEnum vl u' b₀`, `D` **arbitrary** — the union's left disjunct is never needed. -/
theorem hK_of_coverEnum {B : Set (ℤ × ℤ)} {vl u' b₀ : ℤ × ℤ} {D : Set (ℤ × ℤ)}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) :
    chainFull B vl u' b₀ 0 ⊆ D ∪ (⋃ i, Set.range (coverEnum vl u' b₀ i)) :=
  (chainFull_subset_iUnion_range_coverEnum hunimod).trans Set.subset_union_right

/-! ## §7  `hK`, generic in `enum` (team-lead, 2026-09-19: option (a))

`coverEnum` cannot satisfy `hwin` (reported to Aface/team-lead — the window-growth condition
needs `enum`'s rows to reproduce `S`'s own translation structure, which no `S`-blind
enumeration can). So `enum` is L3win's to build. **This section removes the need to re-derive
`hK` once they do**: whatever `enum` L3win produces, `hK` follows from a single set-theoretic
fact about the *rows*, with no reference to how `enum` was built.

This is the same content as `HbaseBridge.hK_iff_diff` (`HbaseBridge.lean:248`) — *not* imported
here (`HbaseBridge` imports `L1CoverWedge`, so the dependency would be circular), reproved
inline in three lines since it is pure `Set` algebra.

⚠ **Status correction (Aface, 2026-09-19): this is a relocation, not a discharge.** Unlike the
old `hK_of_coverEnum` (fully discharged — `coverEnum`'s row union literally *equals* the target
half-plane, `iUnion_coverEnum_eq`), `hK_of_rows_cover_diff` turns `hK` into the *premise*
`hrows : chainFull … k \ D ⊆ ⋃ i, range (enum i)`, which currently has **zero producers
tree-wide** — it is handed to whoever builds `enum`, not closed by this file. Aface has since
landed a `D`-independent sufficient condition for exactly this premise,
`HbaseBridge.hK_zero_of_halfPlane_subset` (`HbaseBridge.lean` §12): if `enum`'s rows cover the
whole half-plane `halfPlaneGE (expNormal u' vl) (expLevel u' vl b₀ 0)` (no hypothesis on `D`
needed, since `chainFull … 0 ⊆` that half-plane unconditionally, `chainFull_zero_subset_halfPlane`),
`hK` follows regardless of `D`. That is a *sufficient*, not necessary, route (`hcov` may cover
less than the whole half-plane and still suffice, as long as it covers `chainFull … 0 \ D`) — the
two theorems below remain the necessary-and-sufficient reduction, and are the right target for
whoever needs the weakest possible obligation to discharge. -/

/-- **`hK`, for *any* `enum` whatsoever** — reduces the covering obligation to "the rows cover
what `D` misses", which is exactly the shape a window-growth construction (L3win's) proves by
induction on `i`. No property of `enum` beyond this containment is used. -/
theorem hK_of_rows_cover_diff {K D : Set (ℤ × ℤ)} {enum : ℕ → ℕ → ℤ × ℤ}
    (hrows : K \ D ⊆ ⋃ i, Set.range (enum i)) :
    K ⊆ D ∪ (⋃ i, Set.range (enum i)) := by
  intro z hz
  by_cases hzD : z ∈ D
  · exact Or.inl hzD
  · exact Or.inr (hrows ⟨hz, hzD⟩)

/-- Specialised to `K := chainFull B vl u' b₀ k`, the shape every `hbase`/`hK` consumer
(`HbaseBridge.hbase_at_of_sweep`, `ofWedgeAtOfSweep`, …) actually wants. -/
theorem hK_chainFull_of_rows_cover_diff {B : Set (ℤ × ℤ)} {vl u' b₀ : ℤ × ℤ} (k : ℕ)
    {D : Set (ℤ × ℤ)} {enum : ℕ → ℕ → ℤ × ℤ}
    (hrows : chainFull B vl u' b₀ k \ D ⊆ ⋃ i, Set.range (enum i)) :
    chainFull B vl u' b₀ k ⊆ D ∪ (⋃ i, Set.range (enum i)) :=
  hK_of_rows_cover_diff hrows

/-! ## §8  Audit (not a proof): every `B`-constraint at `ofWedge`'s live call site

team-lead's task, 2026-09-19: if L1B's candidate `C := {(0,0),(1,3),(1,4)}`, `w := (1,0)`
(lattice-convex by Pick, `¬ LevelInterval C w`) holds up, `hlev` cannot come from
"lattice-convex + primitive + 2-dimensional" alone.  Question: is there some OTHER hypothesis
on `B` at the call site that `C` might violate instead, rescuing `hlev`?  **This section does
not re-verify L1B's claims about `C`** (that duplicates L1B's work) — it only enumerates the
`B`-side of the signature, kernel-checked, so the counterexample (once confirmed) can be
matched against the real hypothesis list rather than an invented one.

**§27 note**: `ofWedge` itself (`L1RegionBuild.lean:344-354`, read-only, not edited) is the
`ξ`-free constructor; the one live consumer supplying real values is
`Nivat.ColleReg.L1Claim.exists_L1MaxBResidual_of_wedgeAt` (`L1Claim.lean:244-263`, read-only —
its file imports this one, so it cannot be imported back; read directly instead).  Its `B`-related
binders, copied verbatim from the source:

```
{U B : Set (ℤ × ℤ)}
(hEnv : Nivat.LE2.EnvOf U B)
(hb₀  : b₀ ∈ B)
(hlev : Nivat.RegionSweep.LevelInterval B vl)
```

plus `hunimod : det u' vl = 1 ∨ det u' vl = -1` and `hvl_prim : Primitive vl`, which constrain
`vl`/`u'` but say nothing about `B`'s shape.  `hbase`, `hsel` (and `hinf`, discharged internally
via `hinf_of_ge`) are propositions about `PeriodOn (T e ξ) (chainFull B vl u' b₀ _) (c • vl)` —
i.e. about how `T e ξ` behaves on the *set* `chainFull B vl u' b₀ k`, built from `B` by
`wedgeFull`/`cut`; they impose no further membership/shape constraint on `B` itself beyond what
already went into building `chainFull`.  `hξ : IsMinimalCounterexample ξ` is the theorem's
*first* binder — it binds `ξ`, not `B`; per §25 it makes `hbase`/`hsel`/`hinf` untestable by a
`B`-only counterexample (they are vacuous statements about a specific `ξ`), but this is moot here
since those three carry no `B`-constraint to begin with.

`isLatticeConvexRegion_of_envOf` (`L1RegionBuild.lean:410`, `h.1.1` unfolding `EnvOf` through
`Enveloped`/`WeaklyEnveloped`, `LatticeEdges.lean:2433,628,624`) shows `hEnv : EnvOf U B` gives
`IsLatticeConvexRegion B` and *only* that — `U` is free (existentially outside, `hcase1`'s first
component, `CaseSplit.lean:82`), and `enveloped_refl` (`LatticeEdges.lean:641`) shows `U := B`
always discharges `EnvOf U B` given `IsLatticeConvexRegion B`, so `∃ U, EnvOf U B` is exactly
`IsLatticeConvexRegion B` with no extra content.  `WeaklyEnveloped`'s face-cardinality clause
says nothing about levels along a fixed direction — this is already spelled out in
`L1RegionBuild.lean:414-440` (L1B's own docstring, read but not edited), which independently
reaches the same "not free" conclusion for `hlev`.

**So the complete list of `B`-constraints at the live call site is exactly three:**
`IsLatticeConvexRegion B` (via `EnvOf`, no stronger), `b₀ ∈ B` (trivial, any element of `B`
serves), and `hlev : LevelInterval B vl` (the one in question).  **No dimensionality binder,
no primitivity-of-`B` binder, and no cardinality binder on `B` exists in this signature** —
"format: 格凸 + 本原 + 二维" as a *hypothesis list* only has the first item; the "primitive" and
"2-dimensional" parts are not separate `B`-side binders here (primitivity in scope is `hvl_prim`/
`hu'`, about `vl`/`u'`, not `B`).

**Consequence for the counterexample test (conditional on L1B's confirmation, §15 — not
re-verified here)**: if `C` is confirmed `IsLatticeConvexRegion` and `¬ LevelInterval C w`, then
`C` satisfies every other `B`-binder at this call site (pick `b₀` as any element of `C`; no
dimension/cardinality hypothesis exists to violate) and fails only `hlev` itself. There is no
second constraint left for `hlev` to hide behind — **finding: "违反了其中哪一条" has no answer
other than `hlev` itself, i.e. this is the "一条都不违反" branch.** Reported to team-lead as the
headline result; the confirmation of `C`'s two properties remains L1B's to close. -/

/-! ## §9  `hcase1`'s `B`, `L1Data`'s `maxB`, and the fringe's two sides (team-lead, 2026-09-19)

**Q1 — reconciled anywhere?  No: the connection is exactly the open `sorry`.**
`Nivat.ColleReg.RegionSteps.exists_L1MaxBResidual` (`RegionSteps.lean:1096-1127`, read-only) is
the theorem whose body is `sorry` — the leaf L1 obligation. Its *last* binder is
`hcase1 : Case1 ξ xper d.Sphi vl` (`CaseSplit.lean:82`); `d.Sphi : Finset (ℤ × ℤ)`
(`AEnv.lean:190` etc., confirmed `Finset`). `Case1 ... S vl := ∃ B, EnvOf (↑S) B ∧ ∃ u, ∀ z ∈
halfStrip B vl, T u ξ z = xper z` — so `hcase1` **already contains** a `B` with `EnvOf ↑d.Sphi B`.
`exists_L1MaxBResidual_of_wedgeAt` (`L1Claim.lean:244`) takes `U B : Set (ℤ×ℤ)`, `hEnv : EnvOf U
B` as *free* binders, not fed from `hcase1`. Nowhere in the tree does a proof `obtain ⟨B, hEnv,
u, hu⟩ := hcase1` followed by a call to `exists_L1MaxBResidual_of_wedgeAt` with `U := ↑d.Sphi`
and this `B` exist — that composition **is** the missing body of the `sorry`. `L1DataMax`'s
`hBmax` field (`maxB (derivedQ ε u' S₁) u' pw : Finset`, `L1Assemble.lean:1050`) is produced
downstream of the *same* unfilled `sorry` (via `L1DataMax.nonempty_of_maxB`, built from
`exists_L1MaxBResidual`'s output) — it is not an independent source of `B`, and being a `Finset`
it is a different type from `hcase1`'s `Set`-typed witness regardless. **So `B` has exactly one
real source (`hcase1`'s existential), not two, and it is not yet wired to `ofWedgeAt`'s binder.**

**Q2 — is `B` `vl`-deep from `EnvOf` alone?  No — but `hcase1`'s *other* conjunct, unused so far,
gives the `vl`-side for free, independent of `EnvOf`.** `EnvOf U B := Enveloped U B :=
WeaklyEnveloped U B ∧ (E B).encard = (E U).encard` and `WeaklyEnveloped U B := IsLatticeConvexRegion
B ∧ ∀ n ∈ E B, n ∈ E U ∧ (face U n).encard ≤ (face B n).encard` (`LatticeEdges.lean:624-629`) —
purely a comparison of edge-normal sets and face cardinalities; it names no direction and bounds
no translate count along any `v`. So `hEnv` alone gives nothing `vl`-deep. **But `hcase1`'s
*second* conjunct is `∃ u, ∀ z ∈ halfStrip B vl, T u ξ z = xper z`**, and `halfStrip B vl :=
{b + (t:ℕ)•vl : b ∈ B}` (`LatticeEdges.lean:1810`) is the **entire forward `vl`-sweep of `B`,
unconditionally, by definition** — not a property `B` has to satisfy, a set built from it. So
`hcase1` already hands whoever fills the `sorry` agreement of `T u ξ` with `xper` on *all* forward
`vl`-translates of `B`, exactly the shape `HbaseBridge.hD_of_halfStrip`/`agree_T_on_halfStripFrom`
consume (modulo repackaging `B` as the `Finset` seed `Bf` those theorems want — a **type
mismatch to resolve, not a missing fact**: `hcase1`'s `B` is `Set`, `hD_of_halfStrip`'s `Bf` is
`Finset`). This conjunct is **not currently a binder of `exists_L1MaxBResidual_of_wedgeAt`** —
it sits unused inside `hcase1`, available but unrouted.

**Q3 — the `u'`-side: no candidate route exists in the signature chain, at all.** `Case1`'s
definition (quoted above, `CaseSplit.lean:82-84`) mentions `vl` exactly once and never mentions
`u'` — `u'` is introduced only later, as `ofWedge`/`ofWedgeAt`'s own companion direction via
`hunimod : det u' vl = ±1`, which is a **relation between `u'` and `vl`**, not a fact about `B`'s
extent along `u'`. No half-strip, no envelope clause, no binder anywhere between `hcase1` and
`ofWedgeAt` says anything about how `B` sits relative to `u'`. Unlike the `vl`-side (where an
unused-but-present fact already exists in `hcase1`), the `u'`-side has **no analogous conjunct
to route** — confirmed by direct reading of `Case1`'s definition, not inferred. **This is a
genuine new obligation, not a wiring gap.** -/

section AuditChecks
-- `#check`, not just reading: confirms `B`'s type and the exact constraint shapes used above.
#check (Nivat.ColleReg.ofWedge :
  {ξ : Config ℤ} → {e vl u' : ℤ × ℤ} → {c : ℤ} → {B : Set (ℤ × ℤ)} → {b₀ : ℤ × ℤ} →
  b₀ ∈ B → IsLatticeConvexRegion B → Primitive vl → Primitive u' →
  Nivat.RegionSweep.LevelInterval B vl → (det u' vl = 1 ∨ det u' vl = -1) →
  Colle41.PeriodOn (T e ξ) (chainFull B vl u' b₀ 0) (c • vl) →
  ¬ Colle41.PeriodOn (T e ξ) (wedgeFull B vl u') (c • vl) →
  Nivat.L1Region.RegionFamily (T e ξ) vl u' c)
#check (Nivat.LE2.EnvOf : Set (ℤ × ℤ) → Set (ℤ × ℤ) → Prop)
#check (Nivat.ColleReg.isLatticeConvexRegion_of_envOf :
  {S B : Set (ℤ × ℤ)} → Nivat.LE2.EnvOf S B → IsLatticeConvexRegion B)
#check (Nivat.RegionSweep.LevelInterval : Set (ℤ × ℤ) → ℤ × ℤ → Prop)
end AuditChecks

section AuditChecksSec9
-- §9's claims, `#check`-backed: `Case1`'s exact two conjuncts, `halfStrip`'s definition-level
-- unconditionality, and that `exists_L1MaxBResidual_of_wedgeAt` takes `B`/`hEnv` as free binders
-- (not sourced from `hcase1`).
#check (Case1 : Config ℤ → Config ℤ → Finset (ℤ × ℤ) → ℤ × ℤ → Prop)
example {ξ xper : Config ℤ} {S : Finset (ℤ × ℤ)} {vl : ℤ × ℤ}
    (h : Case1 ξ xper S vl) :
    ∃ B : Set (ℤ × ℤ), Nivat.LE2.EnvOf (S : Set (ℤ × ℤ)) B ∧
      ∃ u : ℤ × ℤ, ∀ z ∈ Nivat.LE2.halfStrip B vl, T u ξ z = xper z := h
#check (Nivat.LE2.halfStrip : Set (ℤ × ℤ) → ℤ × ℤ → Set (ℤ × ℤ))
#check (Nivat.LE2.subset_halfStrip : ∀ (B : Set (ℤ × ℤ)) (v : ℤ × ℤ), B ⊆ Nivat.LE2.halfStrip B v)
-- `exists_L1MaxBResidual_of_wedgeAt`'s `U`/`B`/`hEnv` are free implicit/explicit binders, not a
-- destructuring of any `Case1`/`hcase1` term — confirmed directly by reading `L1Claim.lean:244-263`
-- (no `Case1` appears anywhere in that signature); not `#check`-able here since `L1Claim.lean`
-- imports this file (`#check`ing it back would be circular) — flagged, not asserted as kernel fact.
end AuditChecksSec9

/-! ## §10  `hfringe`'s two failure modes, split (team-lead's 2026-09-19 dispatch, sub-task 1)

Aface's `hwin`-reduction leaves one named binder at the `ofWedgeAt` call site's fringe:
`hfringe : ∀ k ∈ R, ∀ z ∈ S.erase a, z + (k - a) ∈ R ∪ D`, where `R := chainFull B vl u' b₀ 0`.
`chainFull B vl u' b₀ 0` unfolds (`L1RegionBuild.lean:305-306`) to
`Nivat.L1Region.cut (wedgeFull B vl u') (expNormal u' vl) (expLevel u' vl b₀) 0`, and `cut`
(`L1Region.lean:197-198`) is literally `Rinf ∩ halfPlaneGE m (lev n)`, `halfPlaneGE`
(`CyrKra224.lean:86-87`) literally `{z | c ≤ dot n z}` — both plain `Set.mem_inter_iff`/
`Set.mem_setOf_eq` unfolds, no lemma needed from any read-only file. So a failure of
`w ∈ R` splits, by `not_and_or`, into exactly two disjuncts: -/

open Nivat.L1Region Nivat.Colle41 in
/-- **Failure mode split, `Iff`-level.** `w ∉ chainFull B vl u' b₀ 0` happens for exactly one
of two structurally different reasons: (a) `w` escapes `wedgeFull B vl u'` (the `u'`-side —
`wedgeFull`'s `u'`-component is `Nivat.RegionSweep.sweep`, `ℕ`-indexed and forward-closed only,
`add_mem_sweep` `RegionSweep.lean:94` is the only closure lemma and it has no backward
counterpart), or (b) `w` drops below the level-0 cut `expLevel u' vl b₀ 0`, a purely
`expNormal u' vl`-projected (equivalently `vl`-side, since `dot (expNormal u' vl) u' = 0`,
`dot_expNormal_u'`, `L1RegionBuild.lean:295`) quantity. -/
theorem not_mem_chainFull_iff {B : Set (ℤ × ℤ)} {vl u' b₀ w : ℤ × ℤ} :
    w ∉ chainFull B vl u' b₀ 0 ↔
      w ∉ wedgeFull B vl u' ∨ dot (expNormal u' vl) w < expLevel u' vl b₀ 0 := by
  simp only [chainFull, cut, halfPlaneGE, Set.mem_inter_iff, Set.mem_setOf_eq, not_and_or, not_le]

open Nivat.L1Region Nivat.Colle41 in
/-- **`hfringe`'s failure at a fixed `(k, z)`, split.**  Directly what team-lead asked for: if
`hfringe` fails at some `k ∈ R`, `z ∈ S.erase a` (i.e. `z + (k - a) ∉ R ∪ D`), the failure is
*either* a level drop below `L₀ := expLevel u' vl b₀ 0`, *or* an escape from `wedgeFull B vl u'`
on the `u'`-side — and it is never both-or-neither, it is an `Iff`, not a mere implication. -/
theorem hfringe_fail_iff {B D : Set (ℤ × ℤ)} {vl u' b₀ a k z : ℤ × ℤ} :
    z + (k - a) ∉ chainFull B vl u' b₀ 0 ∪ D ↔
      (z + (k - a) ∉ wedgeFull B vl u' ∨
        dot (expNormal u' vl) (z + (k - a)) < expLevel u' vl b₀ 0) ∧
      z + (k - a) ∉ D := by
  rw [Set.mem_union, not_or, not_mem_chainFull_iff]

/-! ### What, if anything, at `exists_L1MaxBResidual_of_wedgeAt`'s call site supplies each half

Measured against the full binder list re-confirmed in §8/§9 (`L1Claim.lean:244-263`), not
inferred:

**Level-drop half (`dot (expNormal u' vl) (z+(k-a)) < expLevel u' vl b₀ 0`).**  Nothing in
`exists_L1MaxBResidual_of_wedgeAt`'s own binder list supplies this — `hlev`, `hbase`, `hsel`,
`hinf` all fix facts about `chainFull`/`wedgeFull` at the *given* `k`, none constrain an
arbitrary translate `z + (k - a)` for `z ∈ S.erase a`.  The one candidate with actual content is
the **same unrouted conjunct identified in §9's Q2**: `hcase1`'s second conjunct
`∃ u, ∀ z ∈ halfStrip B vl, T u ξ z = xper z` sits one level up, on `exists_L1MaxBResidual`
(`RegionSteps.lean:1096-1127`), not on `_of_wedgeAt` at all — and even there it is a periodicity
statement, not a *set-membership* (level) statement, so it would need further work (Cprobe's
dispatched bridge task) before it could discharge this half, not merely be "wired in". Status:
**structurally the more promising half** (a nonzero, on-chain, so-far-unused fact exists
upstream), but **currently zero** at `_of_wedgeAt`'s own signature — do not read "reachable" as
"already supplied".

**`u'`-side / `wedgeFull`-escape half (`z + (k-a) ∉ wedgeFull B vl u'`).**  Re-measured directly
against this specific shape (not just carried over from §9's general Q3 finding): `Case1`
(`CaseSplit.lean:82-84`) never mentions `u'`; `hunimod : det u' vl = ±1` is a `u'`–`vl` relation,
not a `B`/`wedgeFull`-shape fact; `hb₀`, `hB`, `hlev` all constrain `B` only via `vl` (`EnvOf`,
`LevelInterval B vl`) — none bound `B`'s `u'`-sweep. **Confirmed: zero candidates, exactly as
§9 Q3 found, now specifically checked against `wedgeFull`-escape rather than assumed from the
general finding.** -/

/-! ## §11  Coordinatized reduction (team-lead's 2026-09-19 17:5x sharpened ask), sub-task 2

`Cprobe`'s `hD_of_agree_halfStrip`/`exists_hD_of_case1` (`L1Line0.lean:517-534`, read-only, not
re-proved here) makes `D := halfStrip B vl` a live producer, and a `tmp/`-only probe
(`chainback_probe.lean`, not landed) shows `chainFull B vl u' b₀ 0 ⊆ sweep (halfStrip B vl) u'`
under an extra `hb₀max` hypothesis.  Rather than resting on that unlanded probe, the lemma below
gets the same two-coordinate shape **directly from machinery already in this file** —
`mem_wedgeFull_of_dot_le` (§4) already *is* the pure-`u'`-front sufficient condition, so no
`hb₀max`/`sweep`-unfolding detour is needed to expose it. -/

open Nivat.RegionSweep Nivat.L1Region Nivat.Colle41 in
/-- **The reduction, stated directly.** `z + (k - a) ∈ chainFull B vl u' b₀ 0` as soon as two
*independent*, one-sided linear conditions hold at some witness `b ∈ B`: a **front** condition,
purely on `expNormal vl u'` (`mem_wedgeFull_of_dot_le`'s hypothesis, unchanged), and a **level**
condition, purely on `expNormal u' vl` (`chainFull`'s own cut, unfolded).  Neither condition
mentions the other's normal — this *is* team-lead's "two one-sided linear conditions on the two
coordinates of the frame", with no intermediate `(t, r)` decomposition needed. -/
theorem mem_chainFull_of_dot_le {B : Set (ℤ × ℤ)} {vl u' b₀ b a k z : ℤ × ℤ}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) (hb : b ∈ B)
    (hfront : dot (expNormal vl u') b
      ≤ dot (expNormal vl u') k + dot (expNormal vl u') (z - a))
    (hlevel : dot (expNormal u' vl) b₀
      ≤ dot (expNormal u' vl) k + dot (expNormal u' vl) (z - a)) :
    z + (k - a) ∈ chainFull B vl u' b₀ 0 := by
  have hshift : z + (k - a) = k + (z - a) := by abel
  have hfront' : dot (expNormal vl u') b ≤ dot (expNormal vl u') (z + (k - a)) := by
    rw [hshift, dot_add]; exact hfront
  have hmem_wedge : z + (k - a) ∈ wedgeFull B vl u' := mem_wedgeFull_of_dot_le hunimod hb hfront'
  have hlevel' : dot (expNormal u' vl) b₀ ≤ dot (expNormal u' vl) (z + (k - a)) := by
    rw [hshift, dot_add]; exact hlevel
  refine ⟨hmem_wedge, ?_⟩
  show expLevel u' vl b₀ 0 ≤ dot (expNormal u' vl) (z + (k - a))
  simpa [expLevel] using hlevel'

/-! ### Which of the two sign conditions survives at the call site — measured, not assumed

**`hlevel` (level condition, pure `expNormal u' vl`).**  For a *fixed* `k`, `hlevel` reads
`dot (expNormal u' vl) b₀ ≤ dot (expNormal u' vl) k + dot (expNormal u' vl) (z - a)`; since
`k ∈ chainFull B vl u' b₀ 0` already gives `dot (expNormal u' vl) b₀ ≤ dot (expNormal u' vl) k`
(unfold `chainFull`/`cut`/`halfPlaneGE` on `k`'s own membership), `hlevel` follows outright
whenever `0 ≤ dot (expNormal u' vl) (z - a)` — i.e. whenever `z - a` does not point *against*
the level direction. **This is a strictly weaker demand than "`D := halfStrip B vl` covers the
failure"**: `hD_of_agree_halfStrip`'s `D` is a periodicity-agreement witness, orthogonal to this
purely arithmetic sign fact, and *neither* is currently a binder of
`exists_L1MaxBResidual_of_wedgeAt` — the call site has no hypothesis bounding
`dot (expNormal u' vl) (z - a)` for `z ∈ S.erase a`, `a` the (as-yet-unrouted, per Q3/§9) vertex
witness. **Status: zero at the call site, same as before — the sign of `dot (expNormal u' vl)
(z-a)` depends on which vertex `a` gets chosen, and nothing at the call site chooses one.**

**`hfront` (front condition, pure `expNormal vl u'`).**  Symmetric shape:
`dot (expNormal vl u') b ≤ dot (expNormal vl u') k + dot (expNormal vl u') (z - a)` for *some*
`b ∈ B`.  Since `mem_wedgeFull_of_dot_le` only needs *some* witness `b`, and `B` is nonempty
whenever `S` is (via `hb₀ : b₀ ∈ B`), the binder `b₀` itself is always an eligible witness — but
the inequality still needs `dot (expNormal vl u') (z - a)` bounded below, which again is a fact
about `a` and `z ∈ S.erase a`, not supplied by any binder of `_of_wedgeAt`. **Status: also zero,
symmetric to `hlevel` — the asymmetry team-lead's tighter `sweep (halfStrip B vl) u'` containment
suggested (only the `u'`-side survives) does not show up at *this* level of the reduction: both
sign conditions are equally unsupplied here, because both ultimately need control of
`dot (·) (z - a)` over `z ∈ S.erase a`, and the call site fixes neither `a` nor a bound on
`S.erase a`'s spread in either direction.** This does not contradict team-lead's finding — it is
a different, coarser cut of the same fact: team-lead's asymmetry appears one level down, in
*which* representation `(b, t, r)` of `k` is forced (there `t ≥ 0` becomes free once `hb₀max`
holds, `r ≥ 0` does not); at *this* level (before fixing a representation of `k`), the two
conditions are symmetric and **both** currently empty. Not a kernel refutation — a confirmed
absence on both sides, consistent with §9 Q3's finding extended to the level side as well. -/

end Nivat.ColleReg

section Receipts
#print axioms Nivat.ColleReg.overlap_diff_subset_lines
#print axioms Nivat.ColleReg.not_wedgeFull_univ_singleton
#print axioms Nivat.ColleReg.reconstruct
#print axioms Nivat.ColleReg.mem_wedgeFull_of_dot_le
#print axioms Nivat.ColleReg.inner2_ofInt
#print axioms Nivat.ColleReg.hinf_of_ge
#print axioms Nivat.ColleReg.case1_pair
#print axioms Nivat.ColleReg.case1_and_not_levelInterval
#print axioms Nivat.ColleReg.chainFull_subset_iUnion_range_coverEnum
#print axioms Nivat.ColleReg.hK_of_coverEnum
#print axioms Nivat.ColleReg.hK_of_rows_cover_diff
#print axioms Nivat.ColleReg.hK_chainFull_of_rows_cover_diff
#print axioms Nivat.ColleReg.not_mem_chainFull_iff
#print axioms Nivat.ColleReg.hfringe_fail_iff
#print axioms Nivat.ColleReg.mem_chainFull_of_dot_le
end Receipts
