/-
Copyright (c) 2026 Nivat formalisation project. All rights reserved.
-/
import Nivat.External.Colle.L1Region
import Nivat.External.Colle.CaseSplit
import Nivat.External.Colle.RegionSweep
import Nivat.External.Colle.HalfPlaneFamily

/-!
# L1 — the `RegionFamily` producer for `exists_L1MaxBResidual` (definitions only)

Lane L1B's exclusive file (`RegionSteps.lean:843-862`'s `F : RegionFamily (T e ξ) u u' c`).

**Route, and why it changed twice on 2026-09-19.**  The first plan swept `halfStrip B vl`
forward by a single fixed direction `vJ`, forever, to build the chain directly.  That is
**wrong**: `sweep C w := {z | ∃ g ∈ C, ∃ t : ℕ, z = g + t • w}` is `+w`-closed
(`z = g + t•w ⟹ z + w = g + (t+1)•w`), so `sweep (sweep C w) w = sweep C w` — definitionally
idempotent — which makes `RegionFamily.grow`'s **strict** `⊂` false from the second step on.
(Independently confirmed by an angular-width argument: the nonnegative span of two linearly
independent vectors is a proper cone of width `< π`, so no amount of sweeping a fixed pair of
directions reaches a half-plane either — same obstruction, two derivations.)

**The route used here is `Nivat.L1Region.ofCut` (`L1Region.lean:240`), not `ofHalfPlane`.**
`ofCut` builds a `RegionFamily` by slicing a single fixed region `Rinf` at increasing levels
(`cut Rinf m lev n := Rinf ∩ halfPlaneGE m (lev n)`); `grow`, `isRegion`, and `union_not` all
become properties of the *one* set `Rinf` (`Colle41.IsRegion Rinf u u'` and
`¬ Colle41.PeriodOn x Rinf (c • u)`) rather than of a chain, and `hcover` disappears entirely
— `ofCut` has no such hypothesis.  This is a strictly smaller target than the plan `ofHalfPlane`
required.

`wedgeRinf` below is the candidate `Rinf`: `B` swept forward by *both* `vl` and `u'`
(nonnegative integer combinations), which manifestly contains a ray in each direction — the
two `IsRegion` obligations `RayIn` are proved outright below.  What is **not** proved here
(tracked as comments, per the project rule that no `sorry` may land in the main tree) is
convexity of `wedgeRinf` and non-periodicity on it; see the block at the end of the file.
-/

set_option autoImplicit false

namespace Nivat.ColleReg

open Nivat Nivat.Colle41

/-- The one-time wedge: `B` swept forward by both `vl` and `u'` (nonnegative integer
combinations).  This is the single `Rinf` that `Nivat.L1Region.ofCut` slices to build the
`RegionFamily`'s chain. -/
noncomputable def wedgeRinf (B : Set (ℤ × ℤ)) (vl u' : ℤ × ℤ) : Set (ℤ × ℤ) :=
  {z | ∃ b ∈ B, ∃ s t : ℕ, z = b + (s : ℤ) • vl + (t : ℤ) • u'}

/-- Every point of `B` is in the wedge (`s = t = 0`). -/
theorem mem_wedgeRinf_of_mem {B : Set (ℤ × ℤ)} {vl u' b : ℤ × ℤ} (hb : b ∈ B) :
    b ∈ wedgeRinf B vl u' :=
  ⟨b, hb, 0, 0, by simp⟩

/-- The wedge contains a forward `vl`-ray from every point of `B`. -/
theorem rayIn_wedgeRinf_left {B : Set (ℤ × ℤ)} {vl u' b : ℤ × ℤ} (hb : b ∈ B) :
    Colle41.RayIn (wedgeRinf B vl u') b vl :=
  fun k => ⟨b, hb, k, 0, by simp⟩

/-- The wedge contains a forward `u'`-ray from every point of `B`. -/
theorem rayIn_wedgeRinf_right {B : Set (ℤ × ℤ)} {vl u' b : ℤ × ℤ} (hb : b ∈ B) :
    Colle41.RayIn (wedgeRinf B vl u') b u' :=
  fun k => ⟨b, hb, 0, k, by simp⟩

/-- The chain: `wedgeRinf` sliced by `m` at levels `lev`. -/
noncomputable def chainC (B : Set (ℤ × ℤ)) (vl u' m : ℤ × ℤ) (lev : ℕ → ℤ) : ℕ → Set (ℤ × ℤ) :=
  Nivat.L1Region.cut (wedgeRinf B vl u') m lev

open Nivat.LE2 in
/-- **Compiled refutation of the (a) route team-lead ruled out** ("do not try to show `B`
carries a free `u'`-ray").  If `B` is bounded along a normal `m` to `vl` (`dot m vl = 0`,
`dot m u' > 0`), then `Nivat.LE2.halfStrip B vl` — swept forward only along `vl` — cannot itself
carry a `u'`-ray, hence cannot be `Colle41.IsRegion`.  Reason: sweeping along `vl` never moves
`dot m` (since `dot m vl = 0`), so every point of the strip has `dot m` bounded by `B`'s own
bound; but a genuine forward `u'`-ray would force `dot m` to grow without bound along it, since
`dot m u' > 0`.  This is exactly the obstruction that makes `EnvOf`-bounded `B` (`LatticeEdges.lean`
`envOf_sq1_box`) unable to supply the `u'`-ray directly — the ray has to come from propagating
periodicity (`Nivat.Claim47.ray_period_of_window_period`), not from `B`'s own shape. -/
theorem not_isRegion_halfStrip_of_bounded {B : Set (ℤ × ℤ)} {vl u' m : ℤ × ℤ} {Rb : ℤ}
    (hmvl : dot m vl = 0) (hmu' : 0 < dot m u')
    (hbdd : ∀ b ∈ B, dot m b ≤ Rb) :
    ¬ Colle41.IsRegion (halfStrip B vl) vl u' := by
  have hsmul : ∀ (w : ℤ × ℤ) (t : ℤ), dot m (t • w) = t * dot m w := by
    intro w t
    rw [dot_comm m (t • w), dot_smul t w m, dot_comm w m]
  rintro ⟨-, -, z₀', hray⟩
  obtain ⟨b0, hb0, t0, ht0⟩ := hray 0
  simp only [Nat.cast_zero, zero_smul, add_zero] at ht0
  have hz0 : dot m z₀' ≤ Rb := by
    have hde : dot m z₀' = dot m b0 := by
      rw [ht0, dot_add, hsmul vl (t0 : ℤ), hmvl, mul_zero, add_zero]
    rw [hde]; exact hbdd b0 hb0
  set n : ℤ := Rb - dot m z₀' + 1 with hn
  have hn_pos : 0 < n := by omega
  set k : ℕ := n.toNat with hk
  have hkn : (k : ℤ) = n := Int.toNat_of_nonneg hn_pos.le
  obtain ⟨bk, hbk, tk, htk⟩ := hray k
  have hcontra : dot m z₀' + (k : ℤ) * dot m u' = dot m bk := by
    have hlhs : dot m (z₀' + (k : ℤ) • u') = dot m z₀' + (k : ℤ) * dot m u' := by
      rw [dot_add, hsmul u' (k : ℤ)]
    have hrhs : dot m (bk + (tk : ℤ) • vl) = dot m bk := by
      rw [dot_add, hsmul vl (tk : ℤ), hmvl, mul_zero, add_zero]
    rw [← hlhs, ← hrhs, htk]
  have hle : dot m bk ≤ Rb := hbdd bk hbk
  have hge1 : (1 : ℤ) ≤ dot m u' := by omega
  have h1 : (k : ℤ) * 1 ≤ (k : ℤ) * dot m u' :=
    mul_le_mul_of_nonneg_left hge1 (Int.natCast_nonneg k)
  rw [mul_one] at h1
  linarith [hcontra, hle, h1, hkn]

/-!
### 2026-09-19: `wedgeRinf` was the wrong shape for `ofCut`; `wedgeFull` replaces it

`Nivat.L1Region.ofCut` cuts a **fixed** `Rinf` at levels `lev n` measured by a normal `m` with
`dot m u' = 0` (cut boundary runs *parallel* to `u'`) and `0 < dot m u` (`u = vl` points into the
kept side).  Since `dot m u' = 0`, adding `u'` never changes which slice a point is in — so the
`u'`-ray is free at *every* level from the start, and **growth as `n` increases can only come
from `Rinf` already extending arbitrarily far in the `-vl` direction**.  `wedgeRinf`
(`s t : ℕ`, both forward) does not: `dot m` is bounded below on it by `B`'s own bound, so
`cut wedgeRinf m lev n` is eventually constant, and `hgap`/`hexh` are false outright.
(Independently, `Nivat.RegionSweep.not_isLatticeConvexRegion_sweep_sweep_two_one`
(`RegionSweep.lean:497`) shows `wedgeRinf` — literally `sweep (sweep B vl) u'` in that file's
notation — is not even lattice-convex once `|det u' vl| ≥ 2`.)

`wedgeFull` below fixes both problems from the same change: sweep `vl` **both ways**
(`fullSweep`, `s : ℤ`) before sweeping `u'` forward.  `fullSweep B vl` already contains every
`vl`-translate of `B`, so `Rinf`'s backward extent is unbounded and `hgap`/`hexh` become
one-line facts (`gap_wedgeFull`/`exh_wedgeFull` below); and requiring `u'`/`vl` to be a
*unimodular* pair (`|det u' vl| = 1`) makes `LevelInterval (fullSweep B vl) u'` **free** via
`Nivat.RegionSweep.levelInterval_sweep_of_det_eq_one`/`_neg_one` — no shape hypothesis on `B`
needed for that half.  `B` itself still needs `LevelInterval B vl` (the same fact `wedgeRinf`'s
comment (1) already flagged as `Rsweep`'s open item, just for one sweep instead of two).

**What is exported below** (all four are `#check`-able, none is `sorry`):

* `wedgeFull`/`chainFull` — the concrete `Rinf`/`cut` pair, plus `expNormal`/`expLevel` for the
  `m`/`lev` team-lead asked to see named rather than left inside a proof.
* `isRegion_wedgeFull` — `Colle41.IsRegion (wedgeFull B vl u') vl u'` **unconditionally**
  discharged, given `IsLatticeConvexRegion B`, `Primitive vl`, `Primitive u'`,
  `LevelInterval B vl`, `|det u' vl| = 1`, `B.Nonempty`.
* `ofWedge` — the full `RegionFamily (T e ξ) vl u' c` constructor: same five hypotheses on
  `B`/`vl`/`u'`, plus the two genuinely open facts about `ξ` (`hbase`, `hinf`) that no amount of
  set-shape work can discharge — they are the caller's.

**Field-by-field answer to team-lead's question** (`MaxBResidual`'s six fields, `RegionFamily`'s
four): `det'` (conjunct 5, `det u vl ≠ 0` with `u := vl`... team-lead's `det'` is
`det u u' ≠ 0`) and `prim` (conjunct 6, `Primitive u'`) are supplied **directly** by this
construction's own hypotheses (`hu'` gives `prim`; `hunimod` gives `det' ` since `|det u' vl| = 1
⟹ det u' vl ≠ 0 ⟹ det vl u' ≠ 0` by `det_skew`).  `c0` (conjunct 9, `c ≠ 0`) is **not** supplied
— nothing here names `c`, it is purely `Case1`'s choice.  `line0`/`base0` are **not** supplied
either, by the same non-triviality `Nivat.L1Region.line_of_line_zero`/`base_of_base_zero`
already record: this construction gives the *family*, not membership facts about `Q`/`S₁` inside
its level-`0` slice, which still depend on where `B` sits relative to `Case1`'s window.
`straddle` is **provably not free** in general — `Nivat.L1Region.not_straddle_four`
(`L1Region.lean:460`) already exhibits this on an unrelated family, and nothing about `wedgeFull`
avoids that obstruction; it is not even attempted here.  Of `RegionFamily`'s four fields, this
construction discharges `grow` and `isRegion` unconditionally; `base` and `union_not` are the
`hbase`/`hinf` hypotheses of `ofWedge` — genuinely open, not supplied.
-/

open Nivat.RegionSweep in
/-- `B` swept by every integer multiple of `vl`, not just the forward ones
(`Nivat.RegionSweep.sweep` is `s : ℕ`-forward only). -/
noncomputable def fullSweep (B : Set (ℤ × ℤ)) (vl : ℤ × ℤ) : Set (ℤ × ℤ) :=
  sweep (sweep B (-vl)) vl

open Nivat.RegionSweep in
theorem mem_fullSweep_iff {B : Set (ℤ × ℤ)} {vl z : ℤ × ℤ} :
    z ∈ fullSweep B vl ↔ ∃ b ∈ B, ∃ k : ℤ, z = b + k • vl := by
  unfold fullSweep
  constructor
  · rintro ⟨_, ⟨b, hb, t, rfl⟩, s, rfl⟩
    refine ⟨b, hb, (s : ℤ) - (t : ℤ), ?_⟩
    rw [sub_smul]
    simp only [smul_neg]
    abel
  · rintro ⟨b, hb, k, rfl⟩
    by_cases hk : 0 ≤ k
    · refine ⟨b, ⟨b, hb, 0, by simp⟩, k.toNat, ?_⟩
      rw [Int.toNat_of_nonneg hk]
    · refine ⟨b + k • vl, ⟨b, hb, (-k).toNat, ?_⟩, 0, by simp⟩
      rw [Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ -k)]
      simp [neg_smul, smul_neg]

open Nivat.RegionSweep in
/-- `LevelInterval` transports along a **negated-direction** sweep: shifting by `-vl` never
changes the `vl`-level (`det vl vl = 0`), so every level attained by `B` is still attained. -/
theorem levelInterval_negSweep_of_levelInterval {B : Set (ℤ × ℤ)} {vl : ℤ × ℤ}
    (h : LevelInterval B vl) : LevelInterval (sweep B (-vl)) vl := by
  rintro _ ⟨ga, hga, s, rfl⟩ _ ⟨gb, hgb, t, rfl⟩ m hma hmb
  have hea : det vl (ga + (s : ℤ) • (-vl)) = det vl ga := by
    rw [smul_neg, ← neg_smul]; exact det_add_zsmul_self vl ga (-(s : ℤ))
  have heb : det vl (gb + (t : ℤ) • (-vl)) = det vl gb := by
    rw [smul_neg, ← neg_smul]; exact det_add_zsmul_self vl gb (-(t : ℤ))
  rw [hea] at hma
  rw [heb] at hmb
  obtain ⟨c, hc, hcm⟩ := h ga hga gb hgb m hma hmb
  exact ⟨c, subset_sweep B (-vl) hc, hcm⟩

open Nivat.RegionSweep in
/-- `LevelInterval` transports to the negated direction: `det (-vl) = -det vl`, so the interval
condition just flips sign and swaps the two witnesses. -/
theorem levelInterval_neg_of_levelInterval {B : Set (ℤ × ℤ)} {vl : ℤ × ℤ}
    (h : LevelInterval B vl) : LevelInterval B (-vl) := by
  rintro a ha b hb m hma hmb
  have hda : det (-vl) a = -det vl a := by simp only [det, Prod.fst_neg, Prod.snd_neg]; ring
  have hdb : det (-vl) b = -det vl b := by simp only [det, Prod.fst_neg, Prod.snd_neg]; ring
  rw [hda] at hma
  rw [hdb] at hmb
  obtain ⟨c, hc, hcm⟩ := h b hb a ha (-m) (by omega) (by omega)
  have hdc : det (-vl) c = -det vl c := by simp only [det, Prod.fst_neg, Prod.snd_neg]; ring
  exact ⟨c, hc, by omega⟩

open Nivat.RegionSweep in
/-- `fullSweep B vl` is lattice-convex under exactly the hypotheses `wedgeRinf`'s comment (1)
already asked for (`IsLatticeConvexRegion B`, `Primitive vl`, `LevelInterval B vl`) — sweeping
both ways costs nothing extra over sweeping one way. -/
theorem isLatticeConvexRegion_fullSweep {B : Set (ℤ × ℤ)} {vl : ℤ × ℤ}
    (hB : IsLatticeConvexRegion B) (hvl : Primitive vl) (hlev : LevelInterval B vl) :
    IsLatticeConvexRegion (fullSweep B vl) := by
  have hvl' : Primitive (-vl) := by
    obtain ⟨a, b, hab⟩ := hvl
    exact ⟨-a, -b, by simp only [Prod.fst_neg, Prod.snd_neg]; linear_combination hab⟩
  exact isLatticeConvexRegion_sweep
    (isLatticeConvexRegion_sweep hB hvl' (levelInterval_neg_of_levelInterval hlev)) hvl
    (levelInterval_negSweep_of_levelInterval hlev)

/-- **`wedgeFull`, the replacement for `wedgeRinf`**: `B` extended by every `vl`-multiple, then
swept forward by `u'`. -/
noncomputable def wedgeFull (B : Set (ℤ × ℤ)) (vl u' : ℤ × ℤ) : Set (ℤ × ℤ) :=
  Nivat.RegionSweep.sweep (fullSweep B vl) u'

open Nivat.RegionSweep Nivat.LE2 in
/-- **Convexity of `wedgeFull`.**  The outer `u'`-sweep needs `LevelInterval (fullSweep B vl) u'`,
which is **free** (no hypothesis on `B`) from unimodularity of `(u', vl)` via
`levelInterval_sweep_of_det_eq_one`/`_neg_one`. -/
theorem isLatticeConvexRegion_wedgeFull {B : Set (ℤ × ℤ)} {vl u' : ℤ × ℤ}
    (hB : IsLatticeConvexRegion B) (hvl : Primitive vl) (hu' : Primitive u')
    (hlev : LevelInterval B vl) (hunimod : det u' vl = 1 ∨ det u' vl = -1) :
    IsLatticeConvexRegion (wedgeFull B vl u') := by
  apply isLatticeConvexRegion_sweep (isLatticeConvexRegion_fullSweep hB hvl hlev) hu'
  rcases hunimod with h | h
  · exact levelInterval_sweep_of_det_eq_one h
  · exact levelInterval_sweep_of_det_eq_neg_one h

open Nivat.RegionSweep in
/-- The `vl`-ray, from every point of `wedgeFull B vl u'` (stronger than needed: it holds both
ways, but only the forward `ℕ`-ray is asked for by `Colle41.RayIn`). -/
theorem rayIn_wedgeFull_left {B : Set (ℤ × ℤ)} {vl u' z₀ : ℤ × ℤ} (hz₀ : z₀ ∈ wedgeFull B vl u') :
    Colle41.RayIn (wedgeFull B vl u') z₀ vl := by
  obtain ⟨g, hg, t, rfl⟩ := hz₀
  intro k
  refine ⟨g + (k : ℤ) • vl, ?_, t, by abel⟩
  rw [mem_fullSweep_iff] at hg ⊢
  obtain ⟨b, hb, s, hs⟩ := hg
  exact ⟨b, hb, s + (k : ℤ), by rw [hs, add_smul]; abel⟩

open Nivat.RegionSweep in
/-- The `u'`-ray, from every point of `wedgeFull B vl u'`. -/
theorem rayIn_wedgeFull_right {B : Set (ℤ × ℤ)} {vl u' z₀ : ℤ × ℤ}
    (hz₀ : z₀ ∈ wedgeFull B vl u') : Colle41.RayIn (wedgeFull B vl u') z₀ u' := by
  obtain ⟨g, hg, t, rfl⟩ := hz₀
  intro k
  refine ⟨g, hg, t + k, ?_⟩
  push_cast
  rw [add_smul]
  abel

/-- **`Colle41.IsRegion (wedgeFull B vl u') vl u'`, unconditionally** (given the shape
hypotheses on `B`, `vl`, `u'` — nothing about `ξ`). -/
theorem isRegion_wedgeFull {B : Set (ℤ × ℤ)} {vl u' : ℤ × ℤ}
    (hBne : B.Nonempty) (hB : IsLatticeConvexRegion B) (hvl : Primitive vl) (hu' : Primitive u')
    (hlev : Nivat.RegionSweep.LevelInterval B vl) (hunimod : det u' vl = 1 ∨ det u' vl = -1) :
    Colle41.IsRegion (wedgeFull B vl u') vl u' := by
  obtain ⟨b, hb⟩ := hBne
  have hb' : b ∈ wedgeFull B vl u' :=
    ⟨b, mem_fullSweep_iff.mpr ⟨b, hb, 0, by simp⟩, 0, by simp⟩
  exact ⟨isLatticeConvexRegion_wedgeFull hB hvl hu' hlev hunimod,
    ⟨b, rayIn_wedgeFull_left hb'⟩, ⟨b, rayIn_wedgeFull_right hb'⟩⟩

open Nivat.LE2 in
/-- The cut normal: `(det u' vl) • (perp u')`, chosen so `dot expNormal vl = 1` and
`dot expNormal u' = 0` whenever `(u', vl)` is unimodular — see `dot_expNormal_vl`/`_u'`. -/
noncomputable def expNormal (u' vl : ℤ × ℤ) : ℤ × ℤ :=
  (det u' vl) • (-u'.2, u'.1)

open Nivat.LE2 in
theorem dot_expNormal_vl {u' vl : ℤ × ℤ} (hunimod : det u' vl = 1 ∨ det u' vl = -1) :
    dot (expNormal u' vl) vl = 1 := by
  have hsq : det u' vl * det u' vl = 1 := by rcases hunimod with h | h <;> rw [h] <;> ring
  simp only [expNormal, dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, det] at hsq ⊢
  linear_combination hsq

open Nivat.LE2 in
theorem dot_expNormal_u' {u' vl : ℤ × ℤ} : dot (expNormal u' vl) u' = 0 := by
  simp only [expNormal, dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

open Nivat.LE2 in
/-- The cut levels: descending from `dot (expNormal u' vl) b₀` by one each step. -/
noncomputable def expLevel (u' vl b₀ : ℤ × ℤ) : ℕ → ℤ :=
  fun n => dot (expNormal u' vl) b₀ - (n : ℤ)

/-- The concrete chain: `wedgeFull` cut at `expNormal`/`expLevel`. -/
noncomputable def chainFull (B : Set (ℤ × ℤ)) (vl u' b₀ : ℤ × ℤ) : ℕ → Set (ℤ × ℤ) :=
  Nivat.L1Region.cut (wedgeFull B vl u') (expNormal u' vl) (expLevel u' vl b₀)

open Nivat.LE2 in
theorem expLevel_antitone (u' vl b₀ : ℤ × ℤ) : Antitone (expLevel u' vl b₀) := by
  intro a b hab
  simp only [expLevel]
  have : (a : ℤ) ≤ (b : ℤ) := by exact_mod_cast hab
  omega

open Nivat.LE2 in
theorem expLevel_exhaustive (u' vl b₀ : ℤ × ℤ) (k : ℤ) : ∃ n, expLevel u' vl b₀ n ≤ k := by
  refine ⟨(dot (expNormal u' vl) b₀ - k).toNat, ?_⟩
  simp only [expLevel]
  omega

open Nivat.LE2 in
/-- Right-argument companion to `Nivat.LE2.dot_smul` (which only rewrites a scalar on the
left argument of `dot`). -/
theorem dot_smul_right (k : ℤ × ℤ) (g : ℤ) (v : ℤ × ℤ) : dot k (g • v) = g * dot k v := by
  rw [dot_comm, dot_smul, dot_comm]

open Nivat.LE2 in
theorem expLevel_gap {B : Set (ℤ × ℤ)} {vl u' b₀ : ℤ × ℤ} (hb₀ : b₀ ∈ B)
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) (n : ℕ) :
    ∃ z ∈ wedgeFull B vl u', expLevel u' vl b₀ (n + 1) ≤ dot (expNormal u' vl) z ∧
      dot (expNormal u' vl) z < expLevel u' vl b₀ n := by
  refine ⟨b₀ + (-(n : ℤ) - 1) • vl, ?_, ?_, ?_⟩
  · exact ⟨b₀ + (-(n : ℤ) - 1) • vl,
      mem_fullSweep_iff.mpr ⟨b₀, hb₀, (-(n : ℤ) - 1), rfl⟩, 0, by simp⟩
  · simp only [expLevel, dot_add, dot_smul_right, dot_expNormal_vl hunimod]
    omega
  · simp only [expLevel, dot_add, dot_smul_right, dot_expNormal_vl hunimod]
    omega

/-- **The `RegionFamily` export.**  Five shape hypotheses on `B`/`vl`/`u'` (unconditional, no
`ξ` involved) discharge `grow` and `isRegion`; the two remaining fields (`base`, `union_not`)
are exactly `hbase`/`hinf` below, which name `ξ` and are genuinely open — no set-shape argument
can supply them. -/
noncomputable def ofWedge {ξ : Config ℤ} {e vl u' : ℤ × ℤ} {c : ℤ} {B : Set (ℤ × ℤ)} {b₀ : ℤ × ℤ}
    (hb₀ : b₀ ∈ B) (hB : IsLatticeConvexRegion B) (hvl : Primitive vl) (hu' : Primitive u')
    (hlev : Nivat.RegionSweep.LevelInterval B vl) (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hbase : Colle41.PeriodOn (T e ξ) (chainFull B vl u' b₀ 0) (c • vl))
    (hinf : ¬ Colle41.PeriodOn (T e ξ) (wedgeFull B vl u') (c • vl)) :
    Nivat.L1Region.RegionFamily (T e ξ) vl u' c :=
  Nivat.L1Region.ofCut
    (isRegion_wedgeFull ⟨b₀, hb₀⟩ hB hvl hu' hlev hunimod)
    dot_expNormal_u' (by rw [dot_expNormal_vl hunimod]; exact one_pos)
    (expLevel_antitone u' vl b₀) (expLevel_exhaustive u' vl b₀)
    (expLevel_gap hb₀ hunimod) hbase hinf

open Nivat.LE2 in
/-- **`chainFull`'s successor slice is exactly one `u'`-line** (team-lead's interface request,
2026-09-19, for Afill's `hcover` in `L1CoverWedge.lean`).  `expLevel` descends by exactly `1`
per step (`expLevel u' vl b₀ N = expLevel u' vl b₀ (N+1) + 1`), so the half-open level window
`[expLevel (N+1), expLevel N)` that separates slice `N+1` from slice `N` contains exactly the
single integer `expLevel (N+1)` — no slack either direction.  Consequence: what Afill's `hcover`
has to place inside `genClosure` is a **line**, not a strip. -/
theorem chainFull_diff_subset_line (B : Set (ℤ × ℤ)) (vl u' b₀ : ℤ × ℤ) (N : ℕ) :
    chainFull B vl u' b₀ (N + 1) \ chainFull B vl u' b₀ N ⊆
      {z | dot (expNormal u' vl) z = expLevel u' vl b₀ (N + 1)} := by
  rintro z ⟨hz1, hz2⟩
  have hstep : expLevel u' vl b₀ N = expLevel u' vl b₀ (N + 1) + 1 := by
    simp only [expLevel]; push_cast; ring
  have hmem1 : expLevel u' vl b₀ (N + 1) ≤ dot (expNormal u' vl) z := hz1.2
  have hnotmem : ¬ (expLevel u' vl b₀ N ≤ dot (expNormal u' vl) z) := fun h => hz2 ⟨hz1.1, h⟩
  rw [hstep] at hnotmem
  simp only [Set.mem_ofPred_eq]
  omega

/-- **`ofWedge`, base at an arbitrary index `k`** — team-lead's item (2): `RegionFamily.base`
pinned at index `0` is a `structure`-writing choice, not a mathematical requirement
(`b3_colle2.txt:806` takes the *smallest* `I` with periodicity, i.e. periodicity at *some*
index).  `Nivat.HalfPlaneFamily.ofSomeIndex` (`HalfPlaneFamily.lean:332`) is already generic
over any `R : ℕ → Set (ℤ × ℤ)` with per-index `grow`/`isRegion` and an index-independent union —
`chainFull` supplies exactly that shape (`cut_ssubset`/`isRegion_cut` are per-index;
`iUnion_cut` gives the union `wedgeFull B vl u'` regardless of where `k` sits), so the
reindexing is free here too: `hinf` is untouched, only `hbase` weakens from index `0` to
index `k`. -/
noncomputable def ofWedgeAt {ξ : Config ℤ} {e vl u' : ℤ × ℤ} {c : ℤ} {B : Set (ℤ × ℤ)}
    {b₀ : ℤ × ℤ}
    (hb₀ : b₀ ∈ B) (hB : IsLatticeConvexRegion B) (hvl : Primitive vl) (hu' : Primitive u')
    (hlev : Nivat.RegionSweep.LevelInterval B vl) (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (k : ℕ)
    (hbase : Colle41.PeriodOn (T e ξ) (chainFull B vl u' b₀ k) (c • vl))
    (hinf : ¬ Colle41.PeriodOn (T e ξ) (wedgeFull B vl u') (c • vl)) :
    Nivat.L1Region.RegionFamily (T e ξ) vl u' c :=
  Nivat.HalfPlaneFamily.ofSomeIndex k
    (Nivat.L1Region.cut_ssubset (expLevel_antitone u' vl b₀) (expLevel_gap hb₀ hunimod))
    (Nivat.L1Region.isRegion_cut (isRegion_wedgeFull ⟨b₀, hb₀⟩ hB hvl hu' hlev hunimod)
      dot_expNormal_u' (by rw [dot_expNormal_vl hunimod]; exact one_pos) (expLevel u' vl b₀))
    hbase
    (by rw [Nivat.L1Region.iUnion_cut (expLevel_exhaustive u' vl b₀)]; exact hinf)

end Nivat.ColleReg

namespace Nivat.ColleReg

open Nivat.LE2 in
/-- **`ofWedge`'s `hB` is free once `B` comes from `Case1`'s `EnvOf` witness** (team-lead's
item, 2026-09-19).  `Case1 ξ xper S vl := ∃ B, EnvOf S B ∧ …` (`CaseSplit.lean:82`), and
`EnvOf S B` unfolds (`LatticeEdges.lean:2433,628,624`) to
`Enveloped S B := WeaklyEnveloped S B ∧ …`, whose *first* conjunct of `WeaklyEnveloped` is
`IsLatticeConvexRegion B` verbatim (`LatticeEdges.lean:624-625`).  So `hB` is `h.1.1` — no
separate convexity argument is needed downstream of `hcase1`. -/
theorem isLatticeConvexRegion_of_envOf {S B : Set (ℤ × ℤ)} (h : Nivat.LE2.EnvOf S B) :
    IsLatticeConvexRegion B :=
  h.1.1

/-!
## `hlev : LevelInterval B vl` is **not** free from `EnvOf` — a real gap, not a shape lemma

Checked directly rather than assumed (team-lead: "两条都可能是空真陷阱").  `IsLatticeConvexRegion`
alone does **not** imply `LevelInterval` for an arbitrary direction, and the counterexample is
already compiled in the tree, no new work needed: `Nivat.RegionSweep.isLatticeConvexRegion_pair`
(`RegionSweep.lean:396`) proves `IsLatticeConvexRegion {(0,0),(1,2)}` (the segment has no
interior lattice point, so it is literally the lattice points of a closed real segment — a
bona fide instance, not a degenerate one), while `Nivat.RegionSweep.not_levelInterval_pair`
(`:447`) proves `¬ LevelInterval {(0,0),(1,2)} (1,0)` on the very same set: levels `0` and `2`
are attained, level `1` is skipped.  Both are `#print axioms`-clean in `RegionSweep.lean`
already (`[propext, Classical.choice, Quot.sound]` / `[propext, Quot.sound]`).

So `isLatticeConvexRegion_of_envOf` cannot be strengthened to also hand out `hlev` — `EnvOf`'s
face-cardinality clause (`WeaklyEnveloped`'s second conjunct, `∀ n ∈ E T, n ∈ E U ∧ (face U
n).encard ≤ (face T n).encard`) says nothing about levels *along a fixed direction `vl`*; it is
a statement about edges and their face sizes, orthogonal to "which `det vl`-levels are hit".
**`hlev` is a genuine, separate geometric claim about how `Case1`'s specific `B` sits relative
to `vl`** — not a corollary of convexity, and not discharged by anything in `EnvOf`'s own
definition. It needs either: (a) a fact tying `EnvOf S B`'s edge set `E B` to `vl` (e.g. if `vl`
is forced to be parallel to an edge direction of `B`, which is plausible given `vl` is `Case1`'s
period direction and `S`-related, but not visible from `Case1`'s statement alone), or (b) a
weaker route into `ofWedge`/`ofWedgeAt` that doesn't need `LevelInterval` on all of `B`, only on
whatever sub-region is actually swept. Not resolved here — reporting to team-lead rather than
guessing at (a)/(b), since manufacturing either from `B`/`vl` alone risks exactly the
invented-signature mistake the project's failure log (`PROTOCOL.md`) warns against.
-/

end Nivat.ColleReg

#print axioms Nivat.ColleReg.isLatticeConvexRegion_fullSweep
#print axioms Nivat.ColleReg.isLatticeConvexRegion_wedgeFull
#print axioms Nivat.ColleReg.isRegion_wedgeFull
#print axioms Nivat.ColleReg.ofWedge
#print axioms Nivat.ColleReg.chainFull_diff_subset_line
#print axioms Nivat.ColleReg.ofWedgeAt
#print axioms Nivat.ColleReg.isLatticeConvexRegion_of_envOf
