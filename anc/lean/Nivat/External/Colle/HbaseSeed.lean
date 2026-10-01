/-
Copyright (c) 2026 Nivat formalisation project. All rights reserved.
-/
import Nivat.External.Colle.Claim43
import Nivat.External.Colle.L1Base
import Nivat.External.Colle.HbaseBridge

/-!
# `HbaseSeed` — the `hD` half of Claim 4.6's `hbase` obligation

team-lead's 2026-09-19 split of `hbase` into four named obligations (`hgen`/`hD`/`hwin`/`hK`)
assigns `hD` and `hwin` here.  This file discharges the **wiring** part of `hD` exactly, and
locates the remaining scope precisely.

## What `hD` is, concretely, off disk

`Nivat.Colle43.claim43_periodOn_of_sweep` (`Claim43.lean:435-444`) needs
`hD : ∀ z ∈ D, x z = T h' x z` for some seed set `D` chosen by whoever instantiates the
theorem.  Its mechanical content is **already proven** as `Nivat.Colle43.agree_T_on_halfStripFrom`
(`Claim43.lean:401-424`): for `D := halfStripFrom B u' t₁` (a `Finset` base `B` swept forward by
`u'` past threshold `t₁`), a single `q`-step periodicity hypothesis `hqper` on that half-strip
gives agreement with the `(n*q)•u'`-translate, for every `n`.  So `hD` is not open mathematics —
it is a matter of exhibiting a `Finset` `B`, direction, threshold, and step for which:
(a) the seed `D` is the one `ofWedge`'s `hbase` (`L1RegionBuild.lean:344-354`) actually needs,
and (b) `hqper` holds.

## The geometric identification

`ofWedge`'s `hbase` target is `PeriodOn (T e ξ) (chainFull B vl u' b₀ 0) (c • vl)`
(`L1RegionBuild.lean:347`).  `L1Base.chainFull_zero_eq_sweep_band0` (`L1Base.lean:147-166`,
already proved) rewrites the level-`0` slice as `sweep (band0 B vl u' b₀) u'` — a `u'`-sweep of
the bounded band `band0 B vl u' b₀ := fullSweep B vl ∩ halfPlaneGE (expNormal u' vl)
(expLevel u' vl b₀ 0)`.

So `band0` is the natural seed candidate for `D`, and the period direction `c • vl` (not `u'`) is
what must be established on it.  `agree_T_on_halfStripFrom` is stated for period direction `u'`
(matching its own half-strip direction) — instantiating its generic `u'` argument with `vl`
instead gives exactly what `hbase`'s seed needs, **provided** `band0` literally is a
`halfStripFrom`-shaped set in the `vl` direction.

`band0`'s definition uses a *level cut* (`dot (expNormal u' vl) z ≥` a single threshold), while
`halfStripFrom`'s definition uses a threshold that is uniform across the `Finset` base `B`.  These
coincide exactly when `B` lies on a single `(expNormal u' vl)`-level — i.e. `B` is a finite,
level-`vl`-constant set, which is the natural shape of a chain's finite base (`AEnv`/`ChainAssemble`
use exactly this convention for `B 0`).  §1 below proves this identification is exact under that
one hypothesis (`hconst`), and §2 uses it to reduce `hD` to a single `hqper` obligation, matching
team-lead's "produce `B`/`u'`/`t₁`/`q`/`hqper`" framing verbatim: here `t₁` is *derived*
(`dot (expNormal u' vl) b₀ - L`), not a free choice.

## Scope: `q ≥ 0` only

`agree_T_on_halfStripFrom`'s step is `q : ℕ`, so §2's `hD` bridge only covers `c = (q : ℤ)` for
some `q : ℕ`, i.e. **`c ≥ 0`**. `ofWedge`'s `c : ℤ` carries no sign constraint from `hinf` alone
(`¬ PeriodOn … (c • vl)` is symmetric-ish but not literally sign-free — not checked here). The
`c < 0` case needs a signed variant of `agree_T_on_halfStripFrom` that does not exist yet; this
file does not attempt it. Flagging per §14/§15 discipline: **this is a real gap, not swept under
`hqper`.**

## What is *not* done here: `hwin`

`hwin`/`hK` require the generating window `S`/`a` and the enumeration `enum`, both blocked on
AnfpL's `𝒮_φ` construction (needs the ZMod-`p` case of Lemma 2.6, not yet landed). `SweepData`'s
`window`/`covers` fields (`Claim43.lean:544-551`) are **not** derivable from the other fields
(`sweep_covers_not_derivable`, `Claim43.lean:997` — that refutation is against the *generic*
`SweepData` telescope with no extra geometric input, not against "any possible L1 instantiation";
see the module docstring caution there before citing it for anything stronger). This file supplies
none of `enum`/`hwin`/`hK`; it is deliberately restricted to the `hD` half, which needed no `S`/`a`
and so was safe to build now (team-lead's assembly-order ruling: `enum` may depend on `a`, `a` must
not depend on `enum` — nothing here touches either).
-/

set_option autoImplicit false

namespace Nivat.HbaseSeed

open Nivat Nivat.Colle41 Nivat.LE2 Nivat.ColleReg Nivat.RegionSweep Nivat.Colle43 Nivat.L1Base

/-! ## §1  `band0` is a `halfStripFrom`, when the base is at a single level -/

/-- **The identification.**  If every point of the finite base `B'` sits at the same
`(expNormal u' vl)`-level `L`, then `band0 (↑B') vl u' b₀` is exactly the `vl`-half-strip over
`B'` from the derived threshold `dot (expNormal u' vl) b₀ - L`. Pure algebra from
`mem_fullSweep_iff`, `dot_expNormal_vl` (needs `hunimod`), and `dot_add`/`dot_smul`. -/
theorem band0_eq_halfStripFrom {u' vl b₀ : ℤ × ℤ} {B' : Finset (ℤ × ℤ)} {L : ℤ}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hconst : ∀ b ∈ B', dot (expNormal u' vl) b = L) :
    band0 (↑B' : Set (ℤ × ℤ)) vl u' b₀
      = halfStripFrom B' vl (dot (expNormal u' vl) b₀ - L) := by
  have hvl1 : dot (expNormal u' vl) vl = 1 := dot_expNormal_vl hunimod
  ext z
  simp only [band0, Set.mem_inter_iff, mem_fullSweep_iff, halfPlaneGE, Set.mem_ofPred_eq,
    expLevel, Nat.cast_zero, sub_zero, halfStripFrom]
  constructor
  · rintro ⟨⟨b, hb, k, rfl⟩, hlev⟩
    have hbL : dot (expNormal u' vl) b = L := hconst b hb
    have hdk : dot (expNormal u' vl) (b + k • vl) = L + k := by
      rw [dot_add, dot_smul_right, hvl1, hbL]; ring
    refine ⟨b, hb, k, ?_, rfl⟩
    rw [hdk] at hlev
    omega
  · rintro ⟨g, hg, t, ht, rfl⟩
    have hgL : dot (expNormal u' vl) g = L := hconst g hg
    have hdt : dot (expNormal u' vl) (g + t • vl) = L + t := by
      rw [dot_add, dot_smul_right, hvl1, hgL]; ring
    refine ⟨⟨g, hg, t, rfl⟩, ?_⟩
    rw [hdt]
    omega

/-! ## §2  `hD`, reduced to one `hqper` obligation (scope: `c = (q : ℤ)`, `q : ℕ`) -/

/-- **`hD` for `ofWedge`'s seed `band0`, given a single `q`-step periodicity on it.**
Combines §1 with `Nivat.Colle43.agree_T_on_halfStripFrom` (`Claim43.lean:401`, already proved):
under the single-level hypothesis on the finite base `B'`, a `q`-step periodicity hypothesis on
the `vl`-half-strip gives exactly the `hD` shape `claim43_periodOn_of_sweep` needs, for
`D := band0 (↑B') vl u' b₀` and `h' := (q : ℤ) • vl`. -/
theorem hD_band0_of_hqper {A : Type*} {x : Config A} {u' vl b₀ : ℤ × ℤ} {B' : Finset (ℤ × ℤ)}
    {L : ℤ} (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hconst : ∀ b ∈ B', dot (expNormal u' vl) b = L)
    {q : ℕ}
    (hqper : ∀ g ∈ B', ∀ t : ℤ, dot (expNormal u' vl) b₀ - L ≤ t →
      x (g + (t + (q : ℤ)) • vl) = x (g + t • vl)) :
    ∀ z ∈ band0 (↑B' : Set (ℤ × ℤ)) vl u' b₀, x z = T ((q : ℤ) • vl) x z := by
  rw [band0_eq_halfStripFrom hunimod hconst]
  intro z hz
  have h1 := agree_T_on_halfStripFrom (B := B') (u' := vl)
    (t₁ := dot (expNormal u' vl) b₀ - L) (q := q) hqper 1 z hz
  simpa using h1

/-! ## §3  `hbot`: a lower bound on any `dot n`-positive `n` over `chainFull … 0`

Aface's `HbaseBridge.exists_generic_normal` (`HbaseBridge.lean:782`) supplies a row-direction
normal `n` with `0 < dot n vl`, `0 < dot n u'`, `0 < dot n (expNormal u' vl)`, but returns it as
an opaque witness — its own `dot_generic_ge_on_chainFull_zero` (`:863`) is stated only for the
*literal* construction `n = c • expNormal u' vl + expNormal vl u'` with `c` exposed, which
`exists_generic_normal`'s existential does not hand back. Rather than exposing that internal
`c`, this section reproves the bound directly for **any** `n` with `0 ≤ dot n vl`, `0 ≤ dot n u'`
(weaker than what `exists_generic_normal` gives, so it applies regardless) — no dependence on
`n`'s specific shape, only on the two sign facts `exists_generic_normal` exports.

Per Aface's correction (message this session): `Finset.exists_min_image` cannot run on
`chainFull … 0` itself (infinite `Set`) — it runs here on `B'` alone, which is exactly where it
belongs: the argmin is over the *finite base*, not the infinite swept region. -/

open Nivat.RegionSweep in
theorem hbot_chainFull_zero {B' : Finset (ℤ × ℤ)} {u' vl b₀ n : ℤ × ℤ}
    (hb₀ : b₀ ∈ B') (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hnvl : 0 ≤ dot n vl) (hnu' : 0 ≤ dot n u') :
    ∃ β : ℤ, ∀ w ∈ chainFull (↑B' : Set (ℤ × ℤ)) vl u' b₀ 0, β ≤ dot n w := by
  classical
  obtain ⟨b, hbmem, hbmin⟩ :=
    B'.exists_min_image (fun b => dot n b - dot (expNormal u' vl) b * dot n vl) ⟨b₀, hb₀⟩
  refine ⟨dot n b - dot (expNormal u' vl) b * dot n vl
      + dot (expNormal u' vl) b₀ * dot n vl, ?_⟩
  rintro w ⟨hw1, hw2⟩
  obtain ⟨g, hg, t, rfl⟩ := hw1
  rw [mem_fullSweep_iff] at hg
  obtain ⟨b', hb'mem, k, rfl⟩ := hg
  set m : ℤ × ℤ := expNormal u' vl with hm
  have hmvl : dot m vl = 1 := dot_expNormal_vl hunimod
  have hmu' : dot m u' = 0 := dot_expNormal_u'
  have hlev : dot m b₀ ≤ dot m (b' + k • vl + (t : ℤ) • u') := by
    simpa [expLevel, halfPlaneGE, Set.mem_ofPred_eq] using hw2
  have hmw : dot m (b' + k • vl + (t : ℤ) • u') = dot m b' + k := by
    rw [dot_add, dot_add, dot_smul_right, dot_smul_right, hmvl, hmu']; ring
  have hk : dot m b₀ - dot m b' ≤ k := by rw [hmw] at hlev; omega
  have hkmul : (dot m b₀ - dot m b') * dot n vl ≤ k * dot n vl :=
    mul_le_mul_of_nonneg_right hk hnvl
  have hnw : dot n (b' + k • vl + (t : ℤ) • u')
      = dot n b' + k * dot n vl + (t : ℤ) * dot n u' := by
    rw [dot_add, dot_add, dot_smul_right, dot_smul_right]
  have htpos : (0 : ℤ) ≤ (t : ℤ) * dot n u' :=
    mul_nonneg (Int.natCast_nonneg t) hnu'
  have hbb' : dot n b - dot m b * dot n vl ≤ dot n b' - dot m b' * dot n vl :=
    hbmin b' hb'mem
  rw [hnw]
  nlinarith [hkmul, htpos, hbb']

/-! ## §4  `b₀` itself witnesses `chainFull … 0`'s nonemptiness, and `L₀` follows

Aface's simplification (read-only, this session): `b₀ ∈ B'` puts `b₀` in `chainFull B' vl u' b₀
0` directly — the level-`0` cut's anchor is literally `b₀`, so the half-plane condition is
`dot (expNormal u' vl) b₀ ≤ dot (expNormal u' vl) b₀` (`le_refl`), and `wedgeFull` membership is
`fullSweep`'s `k := 0` step composed with `sweep`'s `t := 0` step. No `band0`/`hconst` needed. -/

theorem b₀_mem_chainFull_zero {B' : Finset (ℤ × ℤ)} {u' vl b₀ : ℤ × ℤ} (hb₀ : b₀ ∈ B') :
    b₀ ∈ chainFull (↑B' : Set (ℤ × ℤ)) vl u' b₀ 0 := by
  refine ⟨⟨b₀, ?_, 0, by simp⟩, ?_⟩
  · exact mem_fullSweep_iff.mpr ⟨b₀, hb₀, 0, by simp⟩
  · simp only [expLevel, halfPlaneGE, Set.mem_ofPred_eq, Nat.cast_zero, sub_zero, le_refl]

/-- **`L₀` for the row order** (`hwin_of_level_rows`/`hK_of_level_rows`'s `L₀`, `HbaseBridge.lean:
700,733`): the least `dot n`-level attained on `chainFull B' vl u' b₀ 0`, extracted from
`hbot_chainFull_zero` (bound) and `b₀_mem_chainFull_zero` (nonemptiness) via
`Int.exists_least_of_bdd`. Its second conjunct **is** `hbot` verbatim after unfolding `L₀`'s
defining property; the point achieving it is the level-`0` row's starting witness. -/
theorem exists_L0_chainFull_zero {B' : Finset (ℤ × ℤ)} {u' vl b₀ n : ℤ × ℤ}
    (hb₀ : b₀ ∈ B') (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hnvl : 0 ≤ dot n vl) (hnu' : 0 ≤ dot n u') :
    ∃ L₀ : ℤ, (∃ w ∈ chainFull (↑B' : Set (ℤ × ℤ)) vl u' b₀ 0, dot n w = L₀) ∧
      ∀ w ∈ chainFull (↑B' : Set (ℤ × ℤ)) vl u' b₀ 0, L₀ ≤ dot n w := by
  obtain ⟨β, hβ⟩ := hbot_chainFull_zero hb₀ hunimod hnvl hnu'
  obtain ⟨L₀, ⟨w, hwmem, hweq⟩, hmin⟩ := Int.exists_least_of_bdd
    (P := fun L => ∃ w ∈ chainFull (↑B' : Set (ℤ × ℤ)) vl u' b₀ 0, dot n w = L)
    ⟨β, fun z ⟨w, hwmem, hweq⟩ => hweq ▸ hβ w hwmem⟩
    ⟨dot n b₀, b₀, b₀_mem_chainFull_zero hb₀, rfl⟩
  exact ⟨L₀, ⟨w, hwmem, hweq⟩, fun w hw => hmin _ ⟨w, hw, rfl⟩⟩

/-! ## §5  Every level `L₀ + i` (`i : ℕ`) is attained — the `hmemR`/`hlevel` nonemptiness gap

Aface flagged this as a fourth, unverified constraint on `enum` (`HbaseBridge.lean`, message this
session): `hmemR i j`/`hlevel i j` implicitly need every level `L₀ + i` nonempty, or `enum i`
cannot be built. This closes it, using exactly the sketch Aface gave: the level-`L₀` witness
`w₀` from `exists_L0_chainFull_zero`, pushed forward by `i • u'`. Two ingredients, both free of
new geometry: `chainFull`'s `u'`-forward closure (the wedge half via `rayIn_wedgeFull_right`, the
cut half via `dot_expNormal_u' : dot (expNormal u' vl) u' = 0`, so the cut's level threshold is
untouched by a `u'`-shift), and `dot n u' = 1` **exactly** (not just `≥ 0` — this is why
`exists_generic_normal`'s literal output is needed here, `hbot`'s weaker `≥` does not suffice). -/

theorem add_nsmul_u'_mem_chainFull_zero {B' : Finset (ℤ × ℤ)} {u' vl b₀ w : ℤ × ℤ}
    (hw : w ∈ chainFull (↑B' : Set (ℤ × ℤ)) vl u' b₀ 0) (i : ℕ) :
    w + (i : ℤ) • u' ∈ chainFull (↑B' : Set (ℤ × ℤ)) vl u' b₀ 0 := by
  obtain ⟨⟨g, hg, t, rfl⟩, hlev⟩ := hw
  refine ⟨⟨g, hg, t + i, ?_⟩, ?_⟩
  · push_cast; rw [add_smul]; abel
  · have hmu' : dot (expNormal u' vl) u' = 0 := dot_expNormal_u'
    have heq : dot (expNormal u' vl) (g + (t : ℤ) • u' + (i : ℤ) • u')
        = dot (expNormal u' vl) (g + (t : ℤ) • u') := by
      rw [dot_add, dot_add, dot_smul_right, dot_smul_right, hmu']; ring
    show expLevel u' vl b₀ 0 ≤ dot (expNormal u' vl) (g + (t : ℤ) • u' + (i : ℤ) • u')
    rw [heq]; exact hlev

theorem exists_level_witness {B' : Finset (ℤ × ℤ)} {u' vl b₀ n : ℤ × ℤ}
    (hnu' : dot n u' = 1) (L₀ : ℤ)
    (hL₀ : ∃ w ∈ chainFull (↑B' : Set (ℤ × ℤ)) vl u' b₀ 0, dot n w = L₀) (i : ℕ) :
    ∃ w ∈ chainFull (↑B' : Set (ℤ × ℤ)) vl u' b₀ 0, dot n w = L₀ + (i : ℤ) := by
  obtain ⟨w₀, hw₀mem, hw₀eq⟩ := hL₀
  refine ⟨w₀ + (i : ℤ) • u', add_nsmul_u'_mem_chainFull_zero hw₀mem i, ?_⟩
  rw [dot_add, dot_smul_right, hnu', hw₀eq]; ring

/-! ## §6  The actual `enum : ℕ → ℕ → ℤ×ℤ`, by classical choice over `Set.Countable.exists_eq_range`

`HbaseBridge.hwin_of_level_rows`/`hK_of_level_rows` (`HbaseBridge.lean:700,733`) need a concrete
`enum` satisfying `hmemR`/`hlevel`/`hsurj`.  §5 only gave existence of *some* witness at each
level, one at a time — `hsurj` needs `enum i` to hit **every** point of the level-`i` slice, not
just one.  Since `ℤ × ℤ` is a `Countable` type, each level slice `{w ∈ R | dot n w = L₀ + i}` is a
countable set, and `Set.Countable.exists_eq_range` (`Mathlib/Data/Set/Countable.lean:151`) turns
nonemptiness (from §5) into a literal `f : ℕ → ℤ×ℤ` with `levelSet i = Set.range f` — read off via
`choose`, one `f` per level `i`. No new geometry: this is pure cardinality bookkeeping. -/

theorem exists_enum_of_level_witness {B' : Finset (ℤ × ℤ)} {u' vl b₀ n : ℤ × ℤ}
    (L₀ : ℤ)
    (hL₀ : ∀ i : ℕ, ∃ w ∈ chainFull (↑B' : Set (ℤ × ℤ)) vl u' b₀ 0, dot n w = L₀ + (i : ℤ)) :
    ∃ enum : ℕ → ℕ → ℤ × ℤ,
      (∀ i j, enum i j ∈ chainFull (↑B' : Set (ℤ × ℤ)) vl u' b₀ 0) ∧
      (∀ i j, dot n (enum i j) = L₀ + (i : ℤ)) ∧
      (∀ (i : ℕ) (w : ℤ × ℤ), w ∈ chainFull (↑B' : Set (ℤ × ℤ)) vl u' b₀ 0 →
        dot n w = L₀ + (i : ℤ) → ∃ j, enum i j = w) := by
  classical
  set R : Set (ℤ × ℤ) := chainFull (↑B' : Set (ℤ × ℤ)) vl u' b₀ 0 with hR
  set levelSet : ℕ → Set (ℤ × ℤ) := fun i => {w | w ∈ R ∧ dot n w = L₀ + (i : ℤ)} with hlevelSet
  have hchoice : ∀ i, ∃ f : ℕ → ℤ × ℤ, levelSet i = Set.range f := by
    intro i
    exact (Set.to_countable (levelSet i)).exists_eq_range (hL₀ i)
  choose f hf using hchoice
  refine ⟨f, ?_, ?_, ?_⟩
  · intro i j
    have hmem : f i j ∈ levelSet i := by rw [hf i]; exact ⟨j, rfl⟩
    exact hmem.1
  · intro i j
    have hmem : f i j ∈ levelSet i := by rw [hf i]; exact ⟨j, rfl⟩
    exact hmem.2
  · intro i w hwR hwlev
    have hmem : w ∈ levelSet i := ⟨hwR, hwlev⟩
    rw [hf i] at hmem
    obtain ⟨j, hj⟩ := hmem
    exact ⟨j, hj⟩

/-- **Capstone**: from `HbaseBridge.exists_generic_normal_unit`'s output (`dot n u' = 1` exactly)
plus the base-finiteness/nonemptiness data, assembles `L₀` and a concrete `enum` satisfying
`hmemR`/`hlevel`/`hsurj`/`hbot` — everything `hwin_of_level_rows`/`hK_of_level_rows` need except
`hlt` (depends on the window generator `S`/`a`, not built here) and `hfringe` (the flagged, still
open, geometric obligation). -/
theorem exists_enum_chainFull_zero {B' : Finset (ℤ × ℤ)} {u' vl b₀ n : ℤ × ℤ}
    (hb₀ : b₀ ∈ B') (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hnvl : 0 ≤ dot n vl) (hnu' : dot n u' = 1) :
    ∃ (L₀ : ℤ) (enum : ℕ → ℕ → ℤ × ℤ),
      (∀ i j, enum i j ∈ chainFull (↑B' : Set (ℤ × ℤ)) vl u' b₀ 0) ∧
      (∀ i j, dot n (enum i j) = L₀ + (i : ℤ)) ∧
      (∀ (i : ℕ) (w : ℤ × ℤ), w ∈ chainFull (↑B' : Set (ℤ × ℤ)) vl u' b₀ 0 →
        dot n w = L₀ + (i : ℤ) → ∃ j, enum i j = w) ∧
      (∀ w ∈ chainFull (↑B' : Set (ℤ × ℤ)) vl u' b₀ 0, L₀ ≤ dot n w) := by
  obtain ⟨L₀, hex, hmin⟩ :=
    exists_L0_chainFull_zero hb₀ hunimod hnvl (by omega : (0:ℤ) ≤ dot n u')
  have hL₀i : ∀ i : ℕ, ∃ w ∈ chainFull (↑B' : Set (ℤ × ℤ)) vl u' b₀ 0, dot n w = L₀ + (i : ℤ) :=
    fun i => exists_level_witness hnu' L₀ hex i
  obtain ⟨enum, hmemR, hlevel, hsurj⟩ := exists_enum_of_level_witness L₀ hL₀i
  exact ⟨L₀, enum, hmemR, hlevel, hsurj, hmin⟩

/-! ## §7  End-to-end wiring: `chainFull B' vl u' b₀ 0` as `hwin_of_level_rows`/`hK_of_level_rows`'s `R`

Dispatched by team-lead: close the `R`-unification question flagged when `enum` was first
reported. Aface independently built the same `enum` existence (`HbaseBridge.exists_enum_of_levels`
§14) and packaged it with `hwin_of_level_rows`/`hK_of_level_rows` into one capstone,
`HbaseBridge.exists_enum_hwin_hK` (`HbaseBridge.lean:971`), whose hypotheses are exactly
`hlt`/`hlevne`/`hbot`/`hfringe`/`hKR` with **no mention of `enum`** — so wiring is just supplying
`hlevne`/`hbot` for `R := chainFull B' vl u' b₀ 0` (this file's own machinery, §3–§4) and
`hlt`/`hfringe`/`hKR` as-is from the caller.

`n`/`a` are **not** produced here — per Aface's §15, `exists_vertex_and_row_order` gives both from
one normal, but that is a separate existential the caller must destructure first, so `n`/`a` are
left as explicit hypotheses here rather than re-derived (the caller composes them). This keeps the
level-order machinery generic: it does not care whether `a` is a generic vertex or the stricter
corner-vertex L3band's `hwin_corner` wants — only `hlt`, `dot n vl ≥ 0`, `dot n u' = 1` matter. -/

theorem exists_hwin_hK_chainFull_zero
    {S B' : Finset (ℤ × ℤ)} {u' vl b₀ n a : ℤ × ℤ} {D K : Set (ℤ × ℤ)}
    (hb₀ : b₀ ∈ B') (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hlt : ∀ z ∈ S.erase a, dot n z < dot n a)
    (hnvl : 0 ≤ dot n vl) (hnu' : dot n u' = 1)
    (hfringe : ∀ k ∈ chainFull (↑B' : Set (ℤ × ℤ)) vl u' b₀ 0, ∀ z ∈ S.erase a,
        z + (k - a) ∈ chainFull (↑B' : Set (ℤ × ℤ)) vl u' b₀ 0 ∪ D)
    (hKR : K ⊆ chainFull (↑B' : Set (ℤ × ℤ)) vl u' b₀ 0) :
    ∃ enum : ℕ → ℕ → ℤ × ℤ,
      (∀ i j : ℕ, ∀ z ∈ S.erase a,
        z + (enum i j - a) ∈
          D ∪ (⋃ i' ∈ {i' | i' < i}, Set.range (enum i')) ∪ (enum i '' {j' | j' < j}))
      ∧ K ⊆ D ∪ (⋃ i, Set.range (enum i)) := by
  set R : Set (ℤ × ℤ) := chainFull (↑B' : Set (ℤ × ℤ)) vl u' b₀ 0 with hR
  obtain ⟨L₀, hex, hmin⟩ :=
    exists_L0_chainFull_zero hb₀ hunimod hnvl (by omega : (0:ℤ) ≤ dot n u')
  have hlevne : ∀ i : ℕ, ∃ w ∈ R, dot n w = L₀ + (i : ℤ) :=
    fun i => exists_level_witness hnu' L₀ hex i
  exact Nivat.HbaseBridge.exists_enum_hwin_hK hlt hlevne hmin hfringe hKR

/-! ## §8. Hard-wall witness: `hlt` (row-order argmax) vs. escape-freeness

team-lead's dispatch: does `exists_hwin_hK_chainFull_zero`'s `hlt` (`a` is the strict `n`-argmax
on `S`) conflict with `hfringe`'s escape-free case (`HbaseBridge.not_cutBand_subset_wedgeFull_iff`
wants `a` to *not* have any point of `S.erase a` strictly below it in *both*
`expNormal u' vl` and `expNormal vl u'`)?  **Answer: hard wall**, witnessed concretely below —
not a mis-framing, and no weakened `hlt` rescues it for this `S`.

Take `u' := (1,0)`, `vl := (0,1)` (`det u' vl = 1`, `expNormal u' vl = (0,1)`,
`expNormal vl u' = (1,0)` — i.e. these two functionals are exactly the `y`- and `x`-coordinate
maps).  `dot n u' = 1` forces `n.1 = 1`; `0 < dot n vl` forces `n.2 > 0`.  For every such `n`
(there is no further freedom: this pins `n = (1, n.2)` for some `n.2 ≥ 1`), the strict argmax
of `n` on `S := {(0,0),(1,1),(2,-1)}` is **always** `a = (1,1)` — checked below by case split,
no dependence on the actual value of `n.2`.  But `(0,0) ∈ S.erase (1,1)` is strictly below
`(1,1)` in *both* coordinates.  So `hlt`'s forced `a` is *never* escape-free on this `S`: the
row-order construction cannot avoid the cut-band escape, it can only be handled by `hfringe`'s
`D`-covering clause. -/

theorem hlt_forces_escape_witness
    {n a : ℤ × ℤ} (hnu' : dot n ((1 : ℤ), (0 : ℤ)) = 1) (hnvl : 0 < dot n ((0 : ℤ), (1 : ℤ)))
    (haS : a ∈ ({((0 : ℤ), (0 : ℤ)), ((1 : ℤ), (1 : ℤ)), ((2 : ℤ), (-1 : ℤ))} : Finset (ℤ × ℤ)))
    (hlt : ∀ z ∈ ({((0 : ℤ), (0 : ℤ)), ((1 : ℤ), (1 : ℤ)), ((2 : ℤ), (-1 : ℤ))} : Finset (ℤ × ℤ)).erase a,
      dot n z < dot n a) :
    a = ((1 : ℤ), (1 : ℤ)) ∧
      dot (expNormal ((1 : ℤ), (0 : ℤ)) ((0 : ℤ), (1 : ℤ))) ((0 : ℤ), (0 : ℤ))
        < dot (expNormal ((1 : ℤ), (0 : ℤ)) ((0 : ℤ), (1 : ℤ))) a ∧
      dot (expNormal ((0 : ℤ), (1 : ℤ)) ((1 : ℤ), (0 : ℤ))) ((0 : ℤ), (0 : ℤ))
        < dot (expNormal ((0 : ℤ), (1 : ℤ)) ((1 : ℤ), (0 : ℤ))) a := by
  simp only [dot] at hnu' hnvl
  have key : a = ((1 : ℤ), (1 : ℤ)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at haS
    rcases haS with rfl | rfl | rfl
    · exfalso
      have h := hlt ((1 : ℤ), (1 : ℤ)) (Finset.mem_erase.2 ⟨by decide, by decide⟩)
      simp only [dot] at h
      omega
    · rfl
    · exfalso
      have h0 := hlt ((0 : ℤ), (0 : ℤ)) (Finset.mem_erase.2 ⟨by decide, by decide⟩)
      have h1 := hlt ((1 : ℤ), (1 : ℤ)) (Finset.mem_erase.2 ⟨by decide, by decide⟩)
      simp only [dot] at h0 h1
      omega
  refine ⟨key, ?_, ?_⟩ <;> subst key <;> simp [expNormal, dot, Nivat.det]

end Nivat.HbaseSeed

#print axioms Nivat.HbaseSeed.band0_eq_halfStripFrom
#print axioms Nivat.HbaseSeed.hD_band0_of_hqper
#print axioms Nivat.HbaseSeed.hbot_chainFull_zero
#print axioms Nivat.HbaseSeed.b₀_mem_chainFull_zero
#print axioms Nivat.HbaseSeed.exists_L0_chainFull_zero
#print axioms Nivat.HbaseSeed.add_nsmul_u'_mem_chainFull_zero
#print axioms Nivat.HbaseSeed.exists_level_witness
#print axioms Nivat.HbaseSeed.exists_enum_of_level_witness
#print axioms Nivat.HbaseSeed.exists_enum_chainFull_zero
#print axioms Nivat.HbaseSeed.exists_hwin_hK_chainFull_zero
#print axioms Nivat.HbaseSeed.hlt_forces_escape_witness
