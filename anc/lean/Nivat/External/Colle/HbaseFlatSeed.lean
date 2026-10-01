/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.HbaseBridge
import Nivat.External.Colle.DecompData
import Nivat.External.Colle.VertexFromEdge
import Nivat.External.Colle.L1CoverWedge

/-!
# `HbaseFlatSeed` — closing the "flat `hwin` route" wall of `OPEN.md #13`

Lane **Hflat**.  `OPEN.md #13` names two walls blocking a generic producer of `hbase`.  For the
**flat `hwin` route** it records (reading, not compiled):

> 唯一活口：把 `u'` 选到 `S` 的共线方向且保持 `det u' vl = ±1`… 读法：不共线，活口死。
> 未派人编，因为 Route 的另一半更有希望。

This file compiles that reading, **without the shear machinery of `HbaseBridge` §20** (no
existential over `T`, no `hnc` binder): under the row-order hypothesis `hlt` that pins `a` as the
*strict* `expNormal u' vl`-maximum of `S` — which is exactly the hypothesis the flat route already
has in hand (`HbaseBridge.hbase_of_row_order`, `HbaseBridge.lean:1506`) — escape (`doubly-lower`)
reduces to one clean condition, and a genuine two-generator (non-collinear) window is exhibited
where that condition fails, at the very `u'` the route would use.

## What is new here vs. `HbaseBridge` §18–§20

* `not_doubly_lower_iff_dual_min` — **given `hlt`**, "no doubly-lower point" collapses to "`a` is
  also the `expNormal vl u'`-minimum of `S`" — the *first* conjunct of the doubly-lower
  existential is discharged by `hlt` itself, so only the second is content.  This is a plain
  propositional fact, no `hunimod`, no shear, no finiteness beyond what `hlt` already assumes.
* `cutBand_subset_wedgeFull_of_dual_min` — the positive half: `hlt` + "`a` is the dual
  minimum" together give escape-freedom (`cutBand ⊆ wedgeFull`) directly from
  `HbaseBridge.cutBand_subset_wedgeFull_of_not_doubly_lower`.
* `hlt_but_not_dual_min_witness` / `escapes_witness` — **the wall, compiled**: a concrete
  4-point window `SF = {0, h₁, h₂, h₁ + h₂}` with `h₁ = (2,1)`, `h₂ = (1,-1)` non-parallel
  (`det h₁ h₂ = -3 ≠ 0`, matching the on-chain shape "support of a product of ≥ 2 pairwise
  non-parallel binomials", `DecompData.lean:106`) — the shape `OPEN.md #13` says the real chain's
  `S := d.Sphi` has, hence is *not* collinear.  At the natural unimodular pair `u' = (1,0)`,
  `vl = (0,1)` the `expNormal u' vl`-max vertex `a = h₁ = (2,1)` is **unique** (`hlt` holds with
  no perturbation needed) yet is **not** the `expNormal vl u'`-minimum: two other points of `S`
  sit strictly below it in *both* functionals.  So escape (`¬ cutBand ⊆ chainFull ∪ wedgeFull`)
  actually happens at this `u'`, with no `hξ`, no minimality assumption — pure finite geometry.

## ⚠ Reading limits (kept, `PROTOCOL.md` §15/§25)

1. This is **one instance**, not a universal quantifier over all non-collinear `S`.  It shows the
   flat route's "activate `hlt` and hope for the dual minimum for free" hope is false in a
   realistic shape; it does **not** prove no `u'` ever works for any non-collinear `S` (that
   would need a statement quantified over all admissible `u'`, which is not attempted here).
2. `d.Sphi` on the actual chain is **not** identified with `SF` — the shape match (≥ 2 pairwise
   non-parallel binomial generators) is what `OPEN.md #13` already reads off `DecompData.lean`;
   this file only supplies the finite arithmetic that such a shape *can* fail the flat route, at
   the simplest non-degenerate instance of it.
3. `hlt` here is *hand-fed* as a hypothesis (checked to hold at the witness by `decide`), not
   re-derived from `exists_generic_normal_data` (`HbaseBridge.lean:785`); the two are compatible
   (same shape of conclusion) but this file does not thread the generic-normal construction.
-/

set_option autoImplicit false

namespace Nivat.HbaseFlatSeed

open Nivat Nivat.ColleReg Nivat.HbaseBridge

/-! ## §1  The clean iff: under `hlt`, escape is exactly "`a` is not the dual minimum" -/

/-- **Given the row-order hypothesis `hlt`** (`a` is the strict `expNormal u' vl`-maximum of
`S`), "no doubly-lower point" collapses to "`a` is the `expNormal vl u'`-minimum of `S`".  The
`hlt`-conjunct of the doubly-lower existential is discharged for free; only the dual-minimum
conjunct is live.  No `hunimod`, no shear. -/
theorem not_doubly_lower_iff_dual_min {S : Finset (ℤ × ℤ)} {a u' vl : ℤ × ℤ}
    (hlt : ∀ z ∈ S.erase a,
      Nivat.LE2.dot (expNormal u' vl) z < Nivat.LE2.dot (expNormal u' vl) a) :
    (¬ ∃ z ∈ S.erase a,
        Nivat.LE2.dot (expNormal u' vl) z < Nivat.LE2.dot (expNormal u' vl) a ∧
        Nivat.LE2.dot (expNormal vl u') z < Nivat.LE2.dot (expNormal vl u') a) ↔
      ∀ z ∈ S.erase a,
        Nivat.LE2.dot (expNormal vl u') a ≤ Nivat.LE2.dot (expNormal vl u') z := by
  constructor
  · intro hno z hz
    by_contra hc
    exact hno ⟨z, hz, hlt z hz, not_le.mp hc⟩
  · intro hmin
    rintro ⟨z, hz, -, hlt2⟩
    exact absurd (hmin z hz) (not_le.mpr hlt2)

/-- **The positive half, packaged**: "`a` is the dual minimum" alone gives escape-freedom
directly, via `HbaseBridge.cutBand_subset_wedgeFull_of_not_doubly_lower` — the implication's
`hlt`-premise is simply discharged unconditionally by `hmin`, so `hlt` itself is *not* needed for
this direction (only for the converse packaging in `not_doubly_lower_iff_dual_min`).  This is the
flat route's best case; §2 shows it is not automatic. -/
theorem cutBand_subset_wedgeFull_of_dual_min {B : Set (ℤ × ℤ)}
    {vl u' b₀ a : ℤ × ℤ} {S : Finset (ℤ × ℤ)}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hmin : ∀ z ∈ S.erase a,
      Nivat.LE2.dot (expNormal vl u') a ≤ Nivat.LE2.dot (expNormal vl u') z) :
    cutBand B vl u' b₀ S a ⊆ wedgeFull B vl u' :=
  cutBand_subset_wedgeFull_of_not_doubly_lower hunimod (fun z hz _ => hmin z hz)

/-! ## §2  The wall, compiled: a genuine two-generator window where `hlt` holds but the dual
minimum fails, at the natural unimodular pair

`h₁ := (2,1)`, `h₂ := (1,-1)` are non-parallel (`det h₁ h₂ = -3 ≠ 0`) — the shape of a product of
two pairwise non-parallel binomials, matching `OPEN.md #13`'s reading of `d.Sphi`.  `SF` is the
support `{0, h₁, h₂, h₁ + h₂}` of that product. -/

def h1F : ℤ × ℤ := (2, 1)
def h2F : ℤ × ℤ := (1, -1)
def uF : ℤ × ℤ := (1, 0)
def vlF : ℤ × ℤ := (0, 1)
def SF : Finset (ℤ × ℤ) := {((0 : ℤ), (0 : ℤ)), h1F, h2F, h1F + h2F}
def aF : ℤ × ℤ := h1F
def BF : Finset (ℤ × ℤ) := {((0 : ℤ), (0 : ℤ))}
def b₀F : ℤ × ℤ := (0, 0)

theorem det_h1F_h2F : det h1F h2F = -3 := by simp only [h1F, h2F, det]; decide

theorem hunimodF : det uF vlF = 1 := by simp only [uF, vlF, det]; decide

theorem erase_SF : SF.erase aF = {((0 : ℤ), (0 : ℤ)), h2F, h1F + h2F} := by
  simp only [SF, aF, h1F, h2F]; decide

theorem expNormal_uv_F : expNormal uF vlF = ((0 : ℤ), (1 : ℤ)) := by
  simp only [expNormal, uF, vlF, det]; decide

theorem expNormal_vu_F : expNormal vlF uF = ((1 : ℤ), (0 : ℤ)) := by
  simp only [expNormal, uF, vlF, det]; decide

/-- **`hlt` holds at `a := h₁F`, no perturbation needed** — `a` is the unique
`expNormal uF vlF`-maximum of `SF`. -/
theorem hlt_F : ∀ z ∈ SF.erase aF,
    Nivat.LE2.dot (expNormal uF vlF) z < Nivat.LE2.dot (expNormal uF vlF) aF := by
  rw [erase_SF, expNormal_uv_F]
  intro z hz
  fin_cases hz <;> simp only [h1F, h2F, Nivat.LE2.dot] <;> decide

/-- **`a` is *not* the dual (`expNormal vlF uF`) minimum**: two points of `SF.erase aF` sit
strictly below it, killing the flat route's only remaining life at this `u'`. -/
theorem not_dual_min_F : ¬ (∀ z ∈ SF.erase aF,
    Nivat.LE2.dot (expNormal vlF uF) aF ≤ Nivat.LE2.dot (expNormal vlF uF) z) := by
  rw [erase_SF, expNormal_vu_F]
  intro hmin
  have h := hmin ((0 : ℤ), (0 : ℤ)) (by decide)
  simp only [aF, h1F, Nivat.LE2.dot] at h
  omega

/-- **The doubly-lower witness itself**, spelled out: `(0,0)` is strictly below `a` in *both*
functionals. -/
theorem doubly_lower_witness_F :
    ∃ z ∈ SF.erase aF,
      Nivat.LE2.dot (expNormal uF vlF) z < Nivat.LE2.dot (expNormal uF vlF) aF ∧
      Nivat.LE2.dot (expNormal vlF uF) z < Nivat.LE2.dot (expNormal vlF uF) aF := by
  refine ⟨((0 : ℤ), (0 : ℤ)), by rw [erase_SF]; decide, ?_, ?_⟩
  · rw [expNormal_uv_F]; simp only [aF, h1F, Nivat.LE2.dot]; decide
  · rw [expNormal_vu_F]; simp only [aF, h1F, Nivat.LE2.dot]; decide

/-- **The wall, in `cutBand`/`wedgeFull` terms**: escape actually happens for this window, at
the natural unimodular pair, with no `hξ` and no minimality assumption. -/
theorem escapes_witness :
    ¬ cutBand (↑BF : Set (ℤ × ℤ)) vlF uF b₀F SF aF ⊆
        chainFull (↑BF : Set (ℤ × ℤ)) vlF uF b₀F 0 ∪ wedgeFull (↑BF : Set (ℤ × ℤ)) vlF uF :=
  (not_cutBand_subset_wedgeFull_iff (B := BF) (by decide) (Or.inl hunimodF)).mpr
    doubly_lower_witness_F

/-! ## §3  The universal statement is **false**: "max in `N1`, min in `N2`" does not force
collinearity

Team-lead's follow-up asked to upgrade `OPEN.md #13`'s reading to a kernel fact of the shape
"`S` not collinear ⟹ every unimodular `u'`, every `a ∈ S`, has a doubly-lower point" via
(1) `not_doubly_lower_iff_dual_min` then (2) "`a` extremal in both functionals ⟹
`S ⊆ a + ℤ·u'`" (`cutWidth_eq_zero_iff_collinear`, Cramer).

**Step (2) is false, checked before attempting the general proof (`PROTOCOL.md` §23/§25 — don't
guess from names).**  `cutWidth` is spread in `N1 = expNormal u' vl` *alone*
(`cutWidth_eq_zero_iff_level`, `HbaseBridge.lean:1814`); nothing forces it to vanish from `a`
being extremal in *two different* functionals `N1`/`N2`.  Basis expansion makes this exact: for
`z ∈ S`, `z - a = p • vl + q • u'` with `p := dot N1 (z - a)`, `q := dot N2 (z - a)`.  `a` is the
`N1`-max exactly means `p ≤ 0` for every `z ∈ S`; `a` is the `N2`-min exactly means `q ≥ 0`.
Neither forces `p = 0` — `p < 0`, `q > 0` simultaneously is a completely ordinary lattice point,
and `cutWidth ≠ 0` needs exactly `p ≠ 0` for some `z`.  The counterexample below realises this at
the smallest possible size: two points, one direction.

⚠ This does **not** resurrect the flat route — `no_escape_despite_noncollinear` below is a
genuine "no escape" instance with `S` *not* collinear, so the intended universal closing
statement is false as phrased.  What *is* true and trivial (not needed here, recorded for
the record) is the same-functional pairing: `hlt` (`N1`-max) together with `cutFringe`-empty in
`Nivat.ColleReg.L1Claim.cutFringe_nonempty_iff`'s sense (`L1Claim.lean:661`, which is an `N1`-*min*,
the *same* functional as `hlt`, not `N2`) directly *is* "`N1` constant on `S`", i.e. `cutWidth = 0`
by `cutWidth_eq_zero_iff_level`'s definition — no Cramer step even needed for that pairing.  The
two "walls" in `OPEN.md #13` are about different functional pairings; conflating them is the bug
this section catches.

`SGF := {(0,1), (5,-3)}`, `uGF := (1,0)`, `vlGF := (0,1)` (`det = 1`), `aGF := (0,1)`: `aGF` is
the unique `N1`-max of `SGF` (`hlt` free), *and* the `N2`-min (only one other point, and its
`N2`-value `5 ≥ 0`) — yet `SGF` is manifestly not collinear along `uGF` (`(5,-3)` and `(0,1)`
differ in the second coordinate, which `uGF`-translates never change). -/

def uGF : ℤ × ℤ := (1, 0)
def vlGF : ℤ × ℤ := (0, 1)
def SGF : Finset (ℤ × ℤ) := {((0 : ℤ), (1 : ℤ)), ((5 : ℤ), (-3 : ℤ))}
def aGF : ℤ × ℤ := (0, 1)
def BGF : Finset (ℤ × ℤ) := {aGF}
def b₀GF : ℤ × ℤ := aGF

theorem hunimodGF : det uGF vlGF = 1 := by simp only [uGF, vlGF, det]; decide

theorem erase_SGF : SGF.erase aGF = {((5 : ℤ), (-3 : ℤ))} := by simp only [SGF, aGF]; decide

theorem expNormal_uv_GF : expNormal uGF vlGF = ((0 : ℤ), (1 : ℤ)) := by
  simp only [expNormal, uGF, vlGF, det]; decide

theorem expNormal_vu_GF : expNormal vlGF uGF = ((1 : ℤ), (0 : ℤ)) := by
  simp only [expNormal, uGF, vlGF, det]; decide

/-- `aGF` is the unique `N1`-max of `SGF` — `hlt` holds with no perturbation. -/
theorem hlt_GF : ∀ z ∈ SGF.erase aGF,
    Nivat.LE2.dot (expNormal uGF vlGF) z < Nivat.LE2.dot (expNormal uGF vlGF) aGF := by
  rw [erase_SGF, expNormal_uv_GF]
  intro z hz
  fin_cases hz
  simp only [aGF, Nivat.LE2.dot]
  decide

/-- `aGF` is also the `N2`-min of `SGF`. -/
theorem dual_min_GF : ∀ z ∈ SGF.erase aGF,
    Nivat.LE2.dot (expNormal vlGF uGF) aGF ≤ Nivat.LE2.dot (expNormal vlGF uGF) z := by
  rw [erase_SGF, expNormal_vu_GF]
  intro z hz
  fin_cases hz
  simp only [aGF, Nivat.LE2.dot]
  decide

/-- **`SGF` is not collinear along `uGF`**: `(5,-3)` and `aGF = (0,1)` differ in the
`uGF`-invariant (second) coordinate. -/
theorem not_collinear_GF : ¬ ∀ z ∈ SGF, ∃ t : ℤ, z = aGF + t • uGF := by
  intro h
  obtain ⟨t, ht⟩ := h ((5 : ℤ), (-3 : ℤ)) (by simp [SGF])
  simp only [aGF, uGF, Prod.mk_add_mk, Prod.smul_mk, smul_eq_mul, mul_zero, mul_one,
    add_zero, Prod.mk.injEq] at ht
  omega

/-- **The refutation itself**: `aGF`'s window has *no* escape (`cutBand ⊆ wedgeFull`, via
`cutBand_subset_wedgeFull_of_dual_min`) even though `SGF` is not collinear.  So "not collinear"
does **not** force escape at every unimodular `u'`/vertex `a` — the universal statement asked for
is false, at the smallest possible instance. -/
theorem no_escape_despite_noncollinear :
    cutBand (↑BGF : Set (ℤ × ℤ)) vlGF uGF b₀GF SGF aGF ⊆ wedgeFull (↑BGF : Set (ℤ × ℤ)) vlGF uGF :=
  cutBand_subset_wedgeFull_of_dual_min (Or.inl hunimodGF) dual_min_GF

/-! ## §4  The shear side's `hnc` binder, discharged on the actual chain window `d.Sphi`

Team-lead's redirect (2026-09-19, after retracting §3's would-be universal statement, which is
refuted by `HbaseBridge.lean` §18.4's `SEx`): the real producer of doubly-lower is
`Nivat.HbaseBridge.exists_shear_hlt_and_doubly_lower` (`HbaseBridge.lean:1992`), whose only
undischarged binder is `hnc : dot (expNormal vl u') z₀ ≠ dot (expNormal vl u') w₀` for some
`z₀ w₀ ∈ S` — **not** "`S` not collinear along `u'`" (§3's condition), but "`S` not confined to a
single line parallel to `vl`".

This section proves `hnc` unconditionally for `S := d.Sphi`, `d : DecompData η`, using only
`d.hm : 2 ≤ d.m` and `d.h_dir` (pairwise non-parallel periods) — exactly the reading `OPEN.md #13`
recorded as uncompiled. -/

open Nivat.LE2 (dot rdot zonoF)
open Nivat.Colle35 (DecompData)

/-- **`dot (expNormal vl u') z` is `(det vl u') * (det vl z)`** — a plain unfolding identity, no
hypotheses. -/
theorem dot_expNormal_swap_eq (u' vl z : ℤ × ℤ) :
    dot (expNormal vl u') z = det vl u' * det vl z := by
  simp only [expNormal, dot, det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- **`dot (expNormal vl u') z = 0 ↔ z` parallel to `vl`** (`det vl z = 0`), given `u' vl`
unimodular (so `det vl u' ≠ 0` and cancels). -/
theorem dot_expNormal_swap_eq_zero_iff {u' vl z : ℤ × ℤ}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) :
    dot (expNormal vl u') z = 0 ↔ det vl z = 0 := by
  rw [dot_expNormal_swap_eq]
  rcases Nivat.HbaseBridge.det_swap_unimod hunimod with h | h <;> rw [h] <;> omega

/-- **`G z := dot (expNormal vl u') z` equals `det u' vl * det z vl` — unconditionally, no
`hunimod` needed.**  Derivation: `dot_expNormal_swap_eq` gives `G z = det vl u' * det vl z`;
antisymmetry of `det` (`det vl u' = -det u' vl`, `det vl z = -det z vl`, both plain unfolding)
turns the product of two negations back into `det u' vl * det z vl`.  This *is* the derivation of
`λ` in `G z = λ * det z vl`: reading it off, `λ = det u' vl`, not asserted but forced by this
identity together with `dot_expNormal_swap_eq`. -/
theorem dot_expNormal_swap_eq_lambda (u' vl z : ℤ × ℤ) :
    dot (expNormal vl u') z = det u' vl * det z vl := by
  rw [dot_expNormal_swap_eq]
  simp only [det]
  ring

/-- **The normalisation, spelled out per `hunimod` case.**  `G u' = (det u' vl)^2 = 1` in *both*
cases (`det u' vl = 1` or `det u' vl = -1` square to the same thing) — not `∓1`: squaring erases
the sign.  Recorded because it is the fact that actually falls out of `dot_expNormal_swap_eq_lambda`
at `z := u'`, as opposed to the unsquared `det u' vl = ∓1` one might naively expect. -/
theorem dot_expNormal_swap_self_eq_one {u' vl : ℤ × ℤ}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) :
    dot (expNormal vl u') u' = 1 := by
  rw [dot_expNormal_swap_eq_lambda]
  rcases hunimod with h | h <;> rw [h] <;> ring

/-- **`λ` by case, as requested**: under `hunimod`, `G z = det z vl` when `det u' vl = 1`, and
`G z = -det z vl` when `det u' vl = -1`.  Both are the same statement as
`dot_expNormal_swap_eq_lambda` with `det u' vl` substituted by its two possible values — recorded
separately only because the case-by-case form is what was asked for. -/
theorem dot_expNormal_swap_eq_lambda_cases {u' vl z : ℤ × ℤ}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) :
    (det u' vl = 1 → dot (expNormal vl u') z = det z vl) ∧
      (det u' vl = -1 → dot (expNormal vl u') z = -det z vl) := by
  constructor <;> intro h <;> rw [dot_expNormal_swap_eq_lambda, h] <;> ring

/-- **Two nonzero vectors both `det`-parallel to a common nonzero `vl` are parallel to each
other.**  Cross-multiplication: `vl.1 * det a b = 0` and `vl.2 * det a b = 0` follow from
`det vl a = 0`/`det vl b = 0` by a `linear_combination`; `vl ≠ 0` then forces `det a b = 0`. -/
theorem det_eq_zero_of_det_vl_eq_zero {vl a b : ℤ × ℤ} (hvl : vl ≠ 0)
    (ha : det vl a = 0) (hb : det vl b = 0) : det a b = 0 := by
  have h1 : vl.1 * det a b = 0 := by
    simp only [det] at ha hb ⊢; linear_combination a.1 * hb - b.1 * ha
  have h2 : vl.2 * det a b = 0 := by
    simp only [det] at ha hb ⊢; linear_combination a.2 * hb - b.2 * ha
  rcases mul_eq_zero.mp h1 with h1' | h1'
  · rcases mul_eq_zero.mp h2 with h2' | h2'
    · exact absurd (Prod.ext h1' h2' : vl = (0, 0)) hvl
    · exact h2'
  · exact h1'

/-- **`d.hm` (`2 ≤ m`) + `d.h_dir` (pairwise non-parallel) ⟹ at most one period is `vl`-parallel,
hence at least one is not.**  If two distinct periods were both `vl`-parallel they would be
parallel to each other by `det_eq_zero_of_det_vl_eq_zero`, contradicting `h_dir`. -/
theorem exists_not_parallel_vl_of_h_dir {α : Type*} [AddCommMonoid α] {η : Config α}
    (d : DecompData η) {vl : ℤ × ℤ} (hvl : vl ≠ 0) :
    ∃ i : Fin d.m, det vl (d.h i) ≠ 0 := by
  by_contra hc
  push_neg at hc
  have hm2 := d.hm
  have hm0 : 0 < d.m := by omega
  have hm1 : 1 < d.m := by omega
  exact absurd (det_eq_zero_of_det_vl_eq_zero hvl (hc ⟨0, hm0⟩) (hc ⟨1, hm1⟩))
    (d.h_dir ⟨0, hm0⟩ ⟨1, hm1⟩ (by simp))

/-- `d.Sphi` is nonempty: `Conv d.Sphi = Conv (zonoF univ d.h)` (via `d.Sphi_eq` +
`Conv_supp_prod_eq_Conv_zonoF`) contains `toReal 0`, so `Conv d.Sphi` is nonempty, which forces
`d.Sphi` itself to be nonempty (`Conv` of the empty `Finset` is `∅`). -/
theorem Sphi_nonempty {α : Type*} [AddCommMonoid α] {η : Config α} (d : DecompData η) :
    d.Sphi.Nonempty := by
  have hconv : Conv d.Sphi = Conv (zonoF (Finset.univ : Finset (Fin d.m)) d.h) := by
    rw [d.Sphi_eq, Nivat.LE2.Conv_supp_prod_eq_Conv_zonoF Finset.univ d.h (fun i _ => d.h_ne i)]
  have hmem0 : (0 : ℤ × ℤ) ∈ zonoF (Finset.univ : Finset (Fin d.m)) d.h :=
    (Nivat.VertexFromEdge.mem_zonoF_iff d.h 0).mpr ⟨fun _ => 0, fun _ => Or.inl rfl, by simp⟩
  rw [Finset.nonempty_iff_ne_empty]
  intro hEmpty
  have hE : Conv d.Sphi = (∅ : Set (ℝ × ℝ)) := by
    simp only [Conv, hEmpty, Finset.coe_empty, Set.image_empty, convexHull_empty]
  rw [hE] at hconv
  exact (hconv ▸ Nivat.subset_Conv hmem0 : toReal (0 : ℤ × ℤ) ∈ (∅ : Set (ℝ × ℝ)))

/-- `rdot (toReal (-n)) y = - rdot (toReal n) y`, plain algebra. -/
theorem rdot_toReal_neg (n : ℤ × ℤ) (y : ℝ × ℝ) :
    rdot (toReal (-n)) y = - rdot (toReal n) y := by
  simp only [rdot, toReal, Prod.fst_neg, Prod.snd_neg, Int.cast_neg]
  ring

/-- **The main theorem: `hnc` holds unconditionally for `S := d.Sphi`.**  Assuming the negation
(`d.Sphi` confined to a single `N2 := expNormal vl u'`-level `c`) forces, via `Sphi_eq` +
`Conv_subset_halfSpace` (both directions), that *all* of `Conv (zonoF univ d.h)` sits on the
`N2 = c` hyperplane.  But `toReal 0` and `toReal (d.h i0)` (`i0` from
`exists_not_parallel_vl_of_h_dir`) both lie in that hull and differ in `N2` by
`dot N2 (d.h i0) ≠ 0` (`dot_expNormal_swap_eq_zero_iff`) — contradiction. -/
theorem exists_hnc_of_decompData {α : Type*} [AddCommMonoid α] {η : Config α} (d : DecompData η)
    {vl u' : ℤ × ℤ} (hvl : vl ≠ 0) (hunimod : det u' vl = 1 ∨ det u' vl = -1) :
    ∃ z₀ ∈ d.Sphi, ∃ w₀ ∈ d.Sphi, dot (expNormal vl u') z₀ ≠ dot (expNormal vl u') w₀ := by
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨i0, hi0⟩ := exists_not_parallel_vl_of_h_dir d hvl
  obtain ⟨z0, hz0⟩ := Sphi_nonempty d
  set c : ℤ := dot (expNormal vl u') z0 with hc_def
  have hlevel : ∀ z ∈ d.Sphi, dot (expNormal vl u') z = c := fun z hz => hcon z hz z0 hz0
  have hconv : Conv d.Sphi = Conv (zonoF (Finset.univ : Finset (Fin d.m)) d.h) := by
    rw [d.Sphi_eq, Nivat.LE2.Conv_supp_prod_eq_Conv_zonoF Finset.univ d.h (fun i _ => d.h_ne i)]
  have heq : ∀ y ∈ Conv d.Sphi, rdot (toReal (expNormal vl u')) y = (c : ℝ) := by
    intro y hy
    have hle : rdot (toReal (expNormal vl u')) y ≤ (c : ℝ) :=
      Nivat.LE2.Conv_subset_halfSpace (fun z hz => (hlevel z hz).le) y hy
    have hle' : rdot (toReal (-(expNormal vl u'))) y ≤ ((-c : ℤ) : ℝ) := by
      apply Nivat.LE2.Conv_subset_halfSpace (S := d.Sphi) (n := -(expNormal vl u'))
        (c := -c) _ y hy
      intro z hz
      have hz' := hlevel z hz
      simp only [Nivat.LE2.dot_neg_left]
      omega
    rw [rdot_toReal_neg] at hle'
    push_cast at hle'
    linarith
  have hmem0 : (0 : ℤ × ℤ) ∈ zonoF (Finset.univ : Finset (Fin d.m)) d.h :=
    (Nivat.VertexFromEdge.mem_zonoF_iff d.h 0).mpr ⟨fun _ => 0, fun _ => Or.inl rfl, by simp⟩
  have hmemi0 : d.h i0 ∈ zonoF (Finset.univ : Finset (Fin d.m)) d.h :=
    (Nivat.VertexFromEdge.mem_zonoF_iff d.h _).mpr
      ⟨fun j => if j = i0 then d.h i0 else 0,
        fun j => by by_cases hji : j = i0 <;> simp [hji],
        by simp⟩
  have h0 : rdot (toReal (expNormal vl u')) (toReal (0 : ℤ × ℤ)) = (c : ℝ) :=
    heq _ (hconv ▸ Nivat.subset_Conv hmem0)
  have hi0' : rdot (toReal (expNormal vl u')) (toReal (d.h i0)) = (c : ℝ) :=
    heq _ (hconv ▸ Nivat.subset_Conv hmemi0)
  rw [Nivat.LE2.rdot_toReal] at h0
  rw [Nivat.LE2.rdot_toReal] at hi0'
  have hval : dot (expNormal vl u') (d.h i0) = dot (expNormal vl u') (0 : ℤ × ℤ) := by
    exact_mod_cast hi0'.trans h0.symm
  have hz00 : dot (expNormal vl u') (0 : ℤ × ℤ) = 0 := by simp [dot]
  rw [hz00] at hval
  exact hi0 ((dot_expNormal_swap_eq_zero_iff hunimod).mp hval)

/-- **`exists_hnc_of_decompData`, restated in `det · vl` form.**  This is the proposition Lstrad
asked about: `∃ z₁ ∈ d.Sphi, ∃ z₂ ∈ d.Sphi, det z₁ vl ≠ det z₂ vl`.  It is **not literally the
same `Prop`** as `exists_hnc_of_decompData` (that one is stated against
`dot (expNormal vl u') z`, this one against `det z vl` directly) — but the two are equivalent
given `hunimod`, via `dot_expNormal_swap_eq_lambda : dot (expNormal vl u') z = det u' vl * det z vl`
(unconditional) and `det u' vl ≠ 0` (from `hunimod`) cancelling the common nonzero factor out of
a `≠`.  So: different statement, same content once `hunimod` is in hand; this lemma is the bridge,
landed rather than left implicit. -/
theorem exists_hnc_of_decompData_det {α : Type*} [AddCommMonoid α] {η : Config α} (d : DecompData η)
    {vl u' : ℤ × ℤ} (hvl : vl ≠ 0) (hunimod : det u' vl = 1 ∨ det u' vl = -1) :
    ∃ z₀ ∈ d.Sphi, ∃ w₀ ∈ d.Sphi, det z₀ vl ≠ det w₀ vl := by
  obtain ⟨z₀, hz₀, w₀, hw₀, hne⟩ := exists_hnc_of_decompData d hvl hunimod
  refine ⟨z₀, hz₀, w₀, hw₀, fun heq => hne ?_⟩
  rw [dot_expNormal_swap_eq_lambda, dot_expNormal_swap_eq_lambda, heq]

/-! ## §4b  Task C: dual-min at zonotope shapes, decided by shearing `u'` along `vl`

**Answer to team-lead's Q1**: the condition on `(S, u', vl)` for dual-min to hold at the
`N1`-maximizing zonotope vertex is exactly the hypothesis `hsign` of
`Nivat.VertexFromEdge.exists_common_min_of_sign_agree` (applied to `n₁ := -(expNormal u' vl)`,
`n₂ := expNormal vl u'`): **no generator `h i` lies in a sign-disagreement quadrant of the basis
`(u', vl)`**, i.e. `dot (expNormal u' vl) (h i) * dot (expNormal vl u') (h i) ≤ 0` for every `i`.
That existing lemma then hands back a single vertex of the zonotope simultaneously extremal for
both functionals — this *is* dual-min, read off a genuine zonotope (`h : ι → ℤ × ℤ`), not an
arbitrary `Finset` (contrast §3, which was refuted precisely because it forgot this structure).

**Answer to Q2**: yes, always achievable, for *any* `m` (in particular `2 ≤ m`) — not by
searching a fixed finite list of candidate `u'`, but by shearing: replacing `u'₀` with
`u'₀ + k • vl` for `k` large enough drives the condition above to hold at *every* generator at
once.  The reason is `dot_expNormal_shear_fst`/`_snd` below: shearing leaves `N2 := dot
(expNormal vl ·)` completely unchanged (`dot_expNormal_shear_fst`) while shifting `N1 := dot
(expNormal · vl)` by exactly `-k * N2 (h i)` at each generator (`dot_expNormal_shear_snd`) — so
for `k` past a threshold depending only on the (finitely many) values `N1base i * N2 i`, every
generator's product flips to `≤ 0`.  **This closes Task C with a positive existence result, not
a second wall**: leaf L1's route through `HbaseFlatSeed`'s `hseed` is *not* dead at zonotope
shapes; the chain's free choice of `u'` (given `vl`) can always reach the region where dual-min
holds. -/

/-- **`N2` is invariant under shearing `u'` by any integer multiple of `vl`.**  In fact the whole
vector `expNormal vl (u' + k • vl)` equals `expNormal vl u'` (the shear term inside `det vl (u' +
k • vl)` is `k * det vl vl = 0`); `dot` with a fixed `z` is the weakest corollary needed below. -/
theorem dot_expNormal_shear_fst (u' vl z : ℤ × ℤ) (k : ℤ) :
    dot (expNormal vl (u' + k • vl)) z = dot (expNormal vl u') z := by
  simp only [expNormal, dot, det, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul]
  ring

/-- **`N1` shifts linearly under shearing `u'` by `vl`, with slope `-N2`.**  This is the
algebraic engine behind Q2: the two functionals trade off exactly, so pushing `k` far enough in
one direction eventually flips `N1 (h i)`'s sign to cancel any sign clash with the (shear-fixed)
`N2 (h i)`. -/
theorem dot_expNormal_shear_snd (u' vl z : ℤ × ℤ) (k : ℤ) :
    dot (expNormal (u' + k • vl) vl) z =
      dot (expNormal u' vl) z - k * dot (expNormal vl u') z := by
  simp only [expNormal, dot, det, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul]
  ring

/-- **`det u' vl` is invariant under shearing `u'` by `vl`**, so `hunimod` transfers for free to
every sheared `u'₀ + k • vl`. -/
theorem det_shear_snd_vl (u' vl : ℤ × ℤ) (k : ℤ) : det (u' + k • vl) vl = det u' vl := by
  simp only [det, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- **Q1 + Q2, landed**: for any finite generator family `h : ι → ℤ × ℤ` and any `u'₀ vl`, there
is a threshold `K` such that shearing `u'₀` by any `k ≥ K` (i.e. using `u'₀ + k • vl` in place of
`u'₀`) makes `N1` and `N2` agree in sign (in the `exists_common_min_of_sign_agree` sense, up to
the `N1 ↦ -N1` flip that turns "simultaneous min" into "simultaneous max-then-min") at *every*
generator simultaneously.  Feeding this `hsign`-shaped conclusion to
`Nivat.VertexFromEdge.exists_common_min_of_sign_agree` (with `n₁ := -(expNormal (u'₀+k•vl) vl)`,
`n₂ := expNormal vl (u'₀+k•vl)`) produces the dual-min vertex.  No hypothesis on `h` is needed
beyond `Fintype ι` — in particular no non-collinearity, no `2 ≤ m`: shearing works regardless,
which is *stronger* than what Task C asked for. -/
theorem exists_shear_sign_agree {ι : Type*} [Fintype ι] (h : ι → ℤ × ℤ) (u'₀ vl : ℤ × ℤ) :
    ∃ K : ℤ, ∀ k : ℤ, K ≤ k → ∀ i : ι,
      dot (expNormal (u'₀ + k • vl) vl) (h i) *
        dot (expNormal vl (u'₀ + k • vl)) (h i) ≤ 0 := by
  classical
  set N2 : ι → ℤ := fun i => dot (expNormal vl u'₀) (h i) with hN2def
  set N1base : ι → ℤ := fun i => dot (expNormal u'₀ vl) (h i) with hN1def
  have hsumnn : (0 : ℤ) ≤ ∑ j, |N1base j * N2 j| := Finset.sum_nonneg (fun j _ => abs_nonneg _)
  refine ⟨1 + ∑ j, |N1base j * N2 j|, fun k hk i => ?_⟩
  have hshearfst : dot (expNormal vl (u'₀ + k • vl)) (h i) = N2 i :=
    dot_expNormal_shear_fst u'₀ vl (h i) k
  have hshearsnd : dot (expNormal (u'₀ + k • vl) vl) (h i) = N1base i - k * N2 i :=
    dot_expNormal_shear_snd u'₀ vl (h i) k
  rw [hshearfst, hshearsnd]
  have hmem : N1base i * N2 i ≤ ∑ j, |N1base j * N2 j| :=
    (le_abs_self _).trans
      (Finset.single_le_sum (f := fun j => |N1base j * N2 j|)
        (fun j _ => abs_nonneg _) (Finset.mem_univ i))
  have hk0 : (0 : ℤ) ≤ k := by linarith
  rcases eq_or_ne (N2 i) 0 with hz | hz
  · simp [hz]
  · have hsq : (1 : ℤ) ≤ (N2 i) ^ 2 := by
      have h2 : 1 ≤ N2 i ∨ N2 i ≤ -1 := by omega
      rcases h2 with h2 | h2 <;> nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hsq hk0]

/-- **The `k → -∞` mirror of `exists_shear_sign_agree` is FALSE.**  Team-lead's `hunimod`
disjunction needs the `det u' vl = -1` branch to shear with `k → -∞` (`detMax_of_hamin_of_shear_unimod`
in `L1SweepBridge.lean` §22); this refutes that the sign-agreement condition can be reached that
way.  Mechanism (already visible in `dot_expNormal_shear_snd`): at a generator with `N2 (h i) ≠
0`, `N1_k (h i) * N2 (h i)` is *linear in `k` with slope `-N2 (h i)^2 ≤ 0`* — monotonically
non-increasing, so it is eventually `≤ 0` going `k → +∞` (that's `exists_shear_sign_agree`) but
diverges to `+∞` going `k → -∞`.  Concrete witness making this explicit: `ι := Unit`,
`h () := (1,0)`, `u'₀ := (1,0)`, `vl := (0,1)` — there `N2 = 1`, `N1base = 0`, so the product is
exactly `-k`, unbounded above as `k → -∞`.  **Consequence for the route**: the `det u' vl = -1`
branch of `hunimod` has *no* compatible shear direction for sign-agreement; whatever discharges
that branch will need a mechanism other than "shear `u'` along `vl`". -/
theorem not_exists_shear_sign_agree_neg :
    ¬ ∃ K : ℤ, ∀ k : ℤ, k ≤ K →
      dot (expNormal (((1, 0) : ℤ × ℤ) + k • ((0, 1) : ℤ × ℤ)) ((0, 1) : ℤ × ℤ))
          ((1, 0) : ℤ × ℤ) *
        dot (expNormal ((0, 1) : ℤ × ℤ) (((1, 0) : ℤ × ℤ) + k • ((0, 1) : ℤ × ℤ)))
          ((1, 0) : ℤ × ℤ) ≤ 0 := by
  rintro ⟨K, hK⟩
  have hkK : -(|K| + 1) ≤ K := by
    rcases le_or_gt 0 K with h | h
    · rw [abs_of_nonneg h]; omega
    · rw [abs_of_neg h]; omega
  have hcontra := hK (-(|K| + 1)) hkK
  rw [dot_expNormal_shear_snd, dot_expNormal_shear_fst] at hcontra
  have hN2 : dot (expNormal ((0 : ℤ), (1 : ℤ)) ((1 : ℤ), (0 : ℤ))) ((1 : ℤ), (0 : ℤ)) = 1 := by
    simp [expNormal, dot, det]
  have hN1 : dot (expNormal ((1 : ℤ), (0 : ℤ)) ((0 : ℤ), (1 : ℤ))) ((1 : ℤ), (0 : ℤ)) = 0 := by
    simp [expNormal, dot, det]
  rw [hN1, hN2] at hcontra
  have habs : (0 : ℤ) ≤ |K| := abs_nonneg K
  nlinarith [hcontra, habs]

/-! ## §5  Team-lead's leverage point (`UPushable`, `HbaseBridge.lean:1295`) is dead for any
finite `B` — the decidable question answered, per instruction, before any long proof.

Team-lead's redirect asked: can `Case1`'s envelope `B` be swapped for / extended to some `B'`
satisfying `UPushable B' vl u' (edgeWidth S a u' vl)` (`hfringe_of_uPushable`,
`HbaseBridge.lean:1309`), preserving `hb₀`/`hD`?

**Corrected reading (team-lead, kernel-checked counterexample `uPushable_Bhp` below):
`not_UPushable_of_finite_pos` only covers *finite* `B` — it is not a claim that `UPushable` is
unconditionally dead.**  My original docstring said "无条件死亡"; that is false and has been
struck.  The half-plane `Bhp u' vl := {z | 0 ≤ dot (expNormal u' vl) z}` is `UPushable` at
*every* `N` (shift any `b ∈ Bhp` back by `N • u'`; `dot (expNormal u' vl) u' = 0`
(`dot_expNormal_u'`) keeps it in `Bhp`) and is infinite (it contains `{n • vl | n : ℕ}`, since
`dot (expNormal u' vl) vl = 1` under `hunimod`).  Nothing on the chain forces `Case1`'s `B` to be
finite: `IsLatticeConvexRegion` (`AEnv.lean:83` = `Section8/HalfPlane.lean:174-175`) admits
unbounded convex sets, and `EnvOf`/`Enveloped` (`LatticeEdges.lean:2433`, unfolding
`WeaklyEnveloped` + an `encard` match on `E`) constrains only edge *directions* and *face
cardinalities*, never `B.Finite` or `↑Sphi ⊆ B`.

**What *is* still true (`not_UPushable_of_finite_pos` below, unchanged, only the reading
corrected).**  Set `c z := dot (expNormal vl u') z`.  Since `dot_expNormal_swap_vl` gives
`c vl = 0` unconditionally and `dot_expNormal_swap_u'` gives `c u' = 1` under unimodularity,
`b = b' + s•vl + N•u'` forces `c b = c b' + N`.  Unwound, `UPushable B vl u' N` says exactly:
**`B`'s projection onto the `u'`-coordinate (in the `(u', vl)` basis) is closed under subtracting
`N`.**  A finite nonempty `B` always fails this once `N ≥ 1` (iterate down from `max (c '' B)`,
producing an infinite strictly-decreasing sequence of attained values — impossible).  It is
**exactly** the sets unbounded in the `−u'` direction, like `Bhp`, that can satisfy it.

**Next question (team-lead's dispatch, not yet attempted below): can `Case1`'s actual `B` be
taken unbounded in `−u'` this way while still satisfying `EnvOf ↑Sphi B` and not making `hD`
harder?** That is genuinely open and is the next target, not this section. -/

theorem c_shift_of_UPushable_rep {u' vl b b' : ℤ × ℤ} {s : ℤ} {N : ℕ}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) (hb : b = b' + s • vl + (N : ℤ) • u') :
    dot (expNormal vl u') b = dot (expNormal vl u') b' + (N : ℤ) := by
  have h1 : dot (expNormal vl u') vl = 0 := Nivat.HbaseBridge.dot_expNormal_swap_vl u' vl
  have h2 : dot (expNormal vl u') u' = 1 := Nivat.HbaseBridge.dot_expNormal_swap_u' hunimod
  subst hb
  simp only [Nivat.LE2.dot_add, dot_smul_right, h1, h2]
  ring

theorem not_UPushable_of_finite_pos {B : Set (ℤ × ℤ)} {vl u' : ℤ × ℤ} {N : ℕ}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) (hN : 0 < N)
    (hBfin : B.Finite) (hBne : B.Nonempty) :
    ¬ Nivat.HbaseBridge.UPushable B vl u' N := by
  classical
  intro hpush
  obtain ⟨b0, hb0⟩ := hBne
  have hstepfun : ∀ p : {b // b ∈ B}, ∃ p' : {b // b ∈ B},
      dot (expNormal vl u') p.1 = dot (expNormal vl u') p'.1 + (N : ℤ) := by
    rintro ⟨b, hb⟩
    obtain ⟨b', hb', s, hbeq⟩ := hpush b hb
    exact ⟨⟨b', hb'⟩, c_shift_of_UPushable_rep hunimod hbeq⟩
  choose F hF using hstepfun
  set h : ℕ → {b // b ∈ B} := fun n => F^[n] ⟨b0, hb0⟩ with hh_def
  have hc : ∀ n, dot (expNormal vl u') (h n).1
      = dot (expNormal vl u') b0 - (n : ℤ) * (N : ℤ) := by
    intro n
    induction n with
    | zero => simp [hh_def]
    | succ n ih =>
      have hstep : (h (n + 1)) = F (h n) := by
        rw [hh_def]; exact Function.iterate_succ_apply' F n ⟨b0, hb0⟩
      have hFn := hF (h n)
      rw [hstep]
      push_cast
      linarith
  have hinj : Function.Injective (fun n => (h n).1) := by
    intro m n hmn
    have hcm := hc m
    have hcn := hc n
    have hmn' : (h m).1 = (h n).1 := hmn
    rw [hmn'] at hcm
    have heq : (m : ℤ) * (N : ℤ) = (n : ℤ) * (N : ℤ) := by
      have := hcm.symm.trans hcn
      linarith
    have hNZ : (N : ℤ) ≠ 0 := by exact_mod_cast hN.ne'
    have : (m : ℤ) = (n : ℤ) := mul_right_cancel₀ hNZ heq
    exact_mod_cast this
  have hrange_sub : Set.range (fun n => (h n).1) ⊆ B := by
    rintro _ ⟨n, rfl⟩; exact (h n).2
  exact (Set.infinite_range_of_injective hinj) (hBfin.subset hrange_sub)

/-! ### The counterexample witnessing that `UPushable` is *not* unconditionally dead

`Bhp u' vl` is the half-plane `{z | 0 ≤ dot (expNormal u' vl) z}` — `IsLatticeConvexRegion`
(it is a preimage of a real half-plane under `toReal`) and infinite (it contains the whole ray
`{n • vl | n : ℕ}`).  It is `UPushable` at *every* `N`, by the same coordinate reading as above:
its projection onto the `u'`-coordinate is all of `ℤ` restricted to `≥ 0`... no — concretely,
shifting any member back by `N • u'` keeps `dot (expNormal u' vl) ·` unchanged
(`dot_expNormal_u' : dot (expNormal u' vl) u' = 0`), so it never leaves `Bhp` at all; `s := 0`
suffices, unconditionally in `N`. -/

/-- The half-plane witness. -/
def Bhp (u' vl : ℤ × ℤ) : Set (ℤ × ℤ) := {z | 0 ≤ dot (expNormal u' vl) z}

theorem uPushable_Bhp (u' vl : ℤ × ℤ) (N : ℕ) :
    Nivat.HbaseBridge.UPushable (Bhp u' vl) vl u' N := by
  intro b hb
  refine ⟨b + (-(N : ℤ)) • u', ?_, 0, by module⟩
  have h0 : dot (expNormal u' vl) u' = 0 := dot_expNormal_u'
  simp only [Bhp, Set.mem_setOf_eq] at hb ⊢
  rw [Nivat.LE2.dot_add, dot_smul_right, h0, mul_zero, add_zero]
  exact hb

theorem infinite_Bhp {u' vl : ℤ × ℤ} (hunimod : det u' vl = 1 ∨ det u' vl = -1) :
    (Bhp u' vl).Infinite := by
  have hvl : dot (expNormal u' vl) vl = 1 := dot_expNormal_vl hunimod
  have hval : ∀ n : ℕ, dot (expNormal u' vl) ((n : ℤ) • vl) = (n : ℤ) := by
    intro n; rw [dot_smul_right, hvl, mul_one]
  have hsub : Set.range (fun n : ℕ => (n : ℤ) • vl) ⊆ Bhp u' vl := by
    rintro _ ⟨n, rfl⟩
    simp only [Bhp, Set.mem_setOf_eq, hval n]
    positivity
  have hinj : Function.Injective (fun n : ℕ => (n : ℤ) • vl) := by
    intro m n hmn
    have := congrArg (dot (expNormal u' vl)) hmn
    simp only [hval] at this
    exact_mod_cast this
  exact Set.Infinite.mono hsub (Set.infinite_range_of_injective hinj)

/-! ## §6  Step (1) of team-lead's dispatch: is `EnvOf ↑Sphi B` even *compatible* with `B`
unbounded in `−u'`?  **No, whenever `Sphi` has two non-parallel edge normals** (always true for
`m ≥ 2` pairwise-non-parallel generators) — general geometric obstruction, no `hξ`, no `S`-side
combinatorics.

**The mechanism.**  If `B` contains a whole forward ray `b₀ + t • r` (`t : ℕ`) and `n ∈ E B`
(so `face B n` has an actual maximizer `z`), then `dot n r ≤ 0` — otherwise the ray eventually
beats `z`, contradicting maximality (`dot_le_of_ray_mem_face`).  Apply this to `r := -u'` (`B`'s
assumed recession direction) and to **both** `n` and `-n` for `n ∈ E B`: `dot n r ≤ 0` and
`dot (-n) r ≤ 0` force `dot n r = 0`.  `EnvOf ↑Sphi B` forces `E B = E Sphi`
(`WeaklyEnveloped.E_subset` + matching `encard`, finite case), and `Sphi_negSymm`
(`DecompData.lean:417`) already gives `n ∈ E Sphi ↔ -n ∈ E Sphi`, so *every* edge normal of
`Sphi` is forced to satisfy `dot n u' = 0`.  **Two non-parallel edge normals `n, n'` (`det n n' ≠
0`) then force `u' = 0`** — impossible, since `det u' vl = ±1` needs `u' ≠ 0`.  So the whole
"take `B` unbounded in `−u'`" strategy needs `Sphi` to have **at most one edge direction** (a
degenerate 1D `Sphi`), which `m ≥ 2` pairwise-non-parallel generators never produce (concrete
witness: §7 below exhibits two non-parallel edges on a real `m = 2` zonotope).

⚠ Reading limit: this refutes recession in the *single* direction `u'` (a ray).  It does not by
itself refute a `B` unbounded along a whole *line* through the origin (both `+u'` and `-u'` rays)
or along `vl` — those change which `r` the argument is run at, not the argument itself; `vl` is
excluded the same way since `Sphi_negSymm`'s antipodal pairs are exactly what breaks any single
recession ray, not a particular one. -/

theorem dot_le_of_ray_mem_face {B : Set (ℤ × ℤ)} {b₀ r n z : ℤ × ℤ}
    (hray : ∀ t : ℕ, b₀ + (t : ℤ) • r ∈ B) (hz : z ∈ Nivat.LE2.face B n) :
    dot n r ≤ 0 := by
  by_contra hpos
  push_neg at hpos
  obtain ⟨-, hzmax⟩ := hz
  set D : ℤ := dot n z - dot n b₀ with hD_def
  have hDt : D ≤ (D.toNat : ℤ) := Int.self_le_toNat D
  have hstep := hzmax (b₀ + ((D.toNat + 1 : ℕ) : ℤ) • r) (hray (D.toNat + 1))
  rw [Nivat.LE2.dot_add, dot_smul_right] at hstep
  have hcast : ((D.toNat + 1 : ℕ) : ℤ) = (D.toNat : ℤ) + 1 := by push_cast; ring
  rw [hcast] at hstep
  have hnn : (0 : ℤ) ≤ (D.toNat : ℤ) + 1 := by positivity
  have hkey : ((D.toNat : ℤ) + 1) * (dot n r - 1) ≥ 0 := mul_nonneg hnn (by linarith)
  nlinarith [hstep, hDt, hkey]

/-- `dot n (-e) = -dot n e`: the right-argument analogue of `Nivat.LE2.dot_neg_left`, not present
in `Nivat.LE2` under this name (`RegionCut.lean:156` has an unrelated-namespace copy) — proved
locally by unfolding `dot`. -/
theorem dot_neg_right (n e : ℤ × ℤ) : dot n (-e) = -dot n e := by
  simp only [dot, Prod.fst_neg, Prod.snd_neg]; ring

theorem eq_zero_of_dot_eq_zero_of_det_ne_zero {n n' r : ℤ × ℤ}
    (hn : dot n r = 0) (hn' : dot n' r = 0) (hdet : det n n' ≠ 0) : r = 0 := by
  have h1 : n.1 * r.1 + n.2 * r.2 = 0 := hn
  have h2 : n'.1 * r.1 + n'.2 * r.2 = 0 := hn'
  have hd : n.1 * n'.2 - n.2 * n'.1 ≠ 0 := hdet
  have hr1 : (n.1 * n'.2 - n.2 * n'.1) * r.1 = 0 := by linear_combination n'.2 * h1 - n.2 * h2
  have hr2 : (n.1 * n'.2 - n.2 * n'.1) * r.2 = 0 := by linear_combination n.1 * h2 - n'.1 * h1
  have hr1' : r.1 = 0 := by
    rcases mul_eq_zero.mp hr1 with h | h
    · exact absurd h hd
    · exact h
  have hr2' : r.2 = 0 := by
    rcases mul_eq_zero.mp hr2 with h | h
    · exact absurd h hd
    · exact h
  exact Prod.ext hr1' hr2'

theorem not_envOf_of_ray_of_two_edges {Sphi : Finset (ℤ × ℤ)} {B : Set (ℤ × ℤ)}
    {u' b₀ n n' : ℤ × ℤ}
    (hray : ∀ t : ℕ, b₀ + (t : ℤ) • (-u') ∈ B)
    (hEB : Nivat.LE2.E B = Nivat.LE2.E (Sphi : Set (ℤ × ℤ)))
    (hn : n ∈ Nivat.LE2.E (Sphi : Set (ℤ × ℤ)))
    (hn' : n' ∈ Nivat.LE2.E (Sphi : Set (ℤ × ℤ)))
    (hnegSymm : ∀ m ∈ Nivat.LE2.E (Sphi : Set (ℤ × ℤ)), -m ∈ Nivat.LE2.E (Sphi : Set (ℤ × ℤ)))
    (hdet : det n n' ≠ 0) : u' = 0 := by
  have hnB : n ∈ Nivat.LE2.E B := hEB ▸ hn
  have hnB' : n' ∈ Nivat.LE2.E B := hEB ▸ hn'
  have hnegB : -n ∈ Nivat.LE2.E B := hEB ▸ hnegSymm n hn
  have hnegB' : -n' ∈ Nivat.LE2.E B := hEB ▸ hnegSymm n' hn'
  obtain ⟨-, z, hz⟩ := hnB
  obtain ⟨-, z', hz'⟩ := hnB'
  obtain ⟨-, w, hw⟩ := hnegB
  obtain ⟨-, w', hw'⟩ := hnegB'
  have h1 : dot n (-u') ≤ 0 := dot_le_of_ray_mem_face hray hz.1
  have h2 : dot (-n) (-u') ≤ 0 := dot_le_of_ray_mem_face hray hw.1
  have h3 : dot n' (-u') ≤ 0 := dot_le_of_ray_mem_face hray hz'.1
  have h4 : dot (-n') (-u') ≤ 0 := dot_le_of_ray_mem_face hray hw'.1
  simp only [Nivat.LE2.dot_neg_left] at h2 h4
  have heq1 : dot n (-u') = 0 := by omega
  have heq2 : dot n' (-u') = 0 := by omega
  have heq1' : dot n u' = 0 := by rw [dot_neg_right] at heq1; linarith
  have heq2' : dot n' u' = 0 := by rw [dot_neg_right] at heq2; linarith
  exact eq_zero_of_dot_eq_zero_of_det_ne_zero heq1' heq2' hdet

/-! ## §7  `Sphi` genuinely has two non-parallel edge normals whenever `m ≥ 2`

Closes the remaining gap in §6's reading: `d.h_dir` (pairwise non-parallel generators) always
produces two non-parallel primitive edge normals of `d.Sphi`, via
`DecompData.mem_E_Sphi_of_dot_eq_zero` (`FaceDistinct.lean:146`) applied to the primitive part
of `perp (d.h i)` for two distinct generator indices — rotating by 90° preserves non-parallelism
(`det_perp_perp` below), so `d.h_dir i j` transfers straight to `det n n' ≠ 0`. -/

theorem det_perp_perp (u v : ℤ × ℤ) : det (perp u) (perp v) = det u v := by
  simp only [perp, det]; ring

theorem perp_ne_zero_local {v : ℤ × ℤ} (hv : v ≠ 0) : perp v ≠ 0 := by
  intro h
  apply hv
  have h1 : -v.2 = 0 := by simpa [perp] using congrArg Prod.fst h
  have h2 : v.1 = 0 := by simpa [perp] using congrArg Prod.snd h
  exact Prod.ext h2 (by simpa using neg_eq_zero.mp h1)

/-- Local restatement of `DecompData.mem_E_Sphi_of_dot_eq_zero` (`FaceDistinct.lean:146`, not
imported here to avoid widening this file's import set): a primitive normal orthogonal to one
decomposition period is an edge normal of `d.Sphi`, via `d.Sphi_eq` transporting `E` to the
zonotope `zonoF Finset.univ d.h`. -/
theorem mem_E_Sphi_of_dot_eq_zero_local {α} [AddCommMonoid α] {η : Config α}
    (d : Nivat.Colle35.DecompData η) {n : ℤ × ℤ} (hprim : Nivat.LE2.Prim n) (i : Fin d.m)
    (hdot : dot n (d.h i) = 0) :
    n ∈ Nivat.LE2.E ((d.Sphi : Set (ℤ × ℤ))) := by
  have hconv : Conv d.Sphi = Conv (Nivat.LE2.zonoF Finset.univ d.h) := by
    rw [d.Sphi_eq,
      Nivat.LE2.Conv_supp_prod_eq_Conv_zonoF Finset.univ d.h (fun j _ => d.h_ne j)]
  rw [Nivat.LE2.E_congr_of_Conv_eq hconv, Nivat.LE2.coe_zonoF, Nivat.LE2.E_zono]
  simp only [Set.mem_iUnion]
  exact ⟨i, Finset.mem_univ i, (Nivat.LE2.E_segOf (d.h_ne i)) ▸ ⟨hprim, hdot⟩⟩

theorem exists_edgeNormal_of_dot_h_eq_zero {α} [AddCommMonoid α] {η : Config α}
    (d : Nivat.Colle35.DecompData η) (i : Fin d.m) :
    ∃ n : ℤ × ℤ, Nivat.LE2.Prim n ∧ dot n (d.h i) = 0 ∧
      n ∈ Nivat.LE2.E ((d.Sphi : Set (ℤ × ℤ))) ∧ ∃ k : ℕ, 0 < k ∧ perp (d.h i) = (k : ℤ) • n := by
  obtain ⟨n, k, hprim, hkpos, heq⟩ :=
    exists_primitive_nsmul_eq (perp_ne_zero_local (d.h_ne i))
  have hprim' : Nivat.LE2.Prim n := Nivat.LE2.prim_iff_primitive.mpr hprim
  have hdotperp : dot (perp (d.h i)) (d.h i) = 0 := by
    rw [dot_perp]; exact det_self (d.h i)
  have hdot : dot n (d.h i) = 0 := by
    have hk0 : (k : ℤ) ≠ 0 := by exact_mod_cast hkpos.ne'
    have := hdotperp
    rw [heq, dot_smul_left] at this
    exact (mul_eq_zero.mp this).resolve_left hk0
  exact ⟨n, hprim', hdot, mem_E_Sphi_of_dot_eq_zero_local d hprim' i hdot, k, hkpos, heq⟩

/-- **The witness for §6's remaining premise.**  For `i ≠ j`, the two edge normals produced by
`exists_edgeNormal_of_dot_h_eq_zero` are non-parallel: `d.h_dir i j` (`det (d.h i) (d.h j) ≠ 0`)
transfers through the `perp`-rotation (`det_perp_perp`) and the positive scalars `k i`, `k j`. -/
theorem exists_two_nonparallel_edgeNormals_of_Sphi {α} [AddCommMonoid α] {η : Config α}
    (d : Nivat.Colle35.DecompData η) (i j : Fin d.m) (hij : i ≠ j) :
    ∃ n n' : ℤ × ℤ,
      n ∈ Nivat.LE2.E ((d.Sphi : Set (ℤ × ℤ))) ∧
      n' ∈ Nivat.LE2.E ((d.Sphi : Set (ℤ × ℤ))) ∧ det n n' ≠ 0 := by
  obtain ⟨n, -, -, hnE, ki, hkipos, hkieq⟩ := exists_edgeNormal_of_dot_h_eq_zero d i
  obtain ⟨n', -, -, hn'E, kj, hkjpos, hkjeq⟩ := exists_edgeNormal_of_dot_h_eq_zero d j
  refine ⟨n, n', hnE, hn'E, ?_⟩
  intro hcontra
  have hdethj : det (perp (d.h i)) (perp (d.h j)) = 0 := by
    rw [hkieq, hkjeq, det_zsmul_zsmul, hcontra, mul_zero]
  rw [det_perp_perp] at hdethj
  exact d.h_dir i j hij hdethj

/-- **Headline: step 1 answered negatively whenever `d.m ≥ 2`.**  No `B` unbounded along the ray
`b₀ - t • u'` (`u' ≠ 0`) can satisfy `EnvOf ↑d.Sphi B`, once `d` has (at least) two generators —
which every `DecompData` does (`d.hm : 2 ≤ d.m`).  Combines §6 (`not_envOf_of_ray_of_two_edges`)
with §7's edge-normal witness and `Sphi_negSymm` (`DecompData.lean:417`). -/
theorem not_envOf_of_ray_of_case1 {α} [AddCommMonoid α] {η : Config α}
    (d : Nivat.Colle35.DecompData η) {B : Set (ℤ × ℤ)} {u' b₀ : ℤ × ℤ}
    (hray : ∀ t : ℕ, b₀ + (t : ℤ) • (-u') ∈ B)
    (hEB : Nivat.LE2.E B = Nivat.LE2.E ((d.Sphi : Set (ℤ × ℤ)))) :
    u' = 0 := by
  have hm2 : 2 ≤ d.m := d.hm
  have hlt1 : 1 < d.m := by omega
  have hlt0 : 0 < d.m := by omega
  have h01 : (⟨0, hlt0⟩ : Fin d.m) ≠ ⟨1, hlt1⟩ := by
    intro hcontra
    exact absurd (congrArg Fin.val hcontra) (by norm_num)
  obtain ⟨n, n', hn, hn', hdet⟩ :=
    exists_two_nonparallel_edgeNormals_of_Sphi d ⟨0, hlt0⟩ ⟨1, hlt1⟩ h01
  exact not_envOf_of_ray_of_two_edges hray hEB hn hn'
    (fun m hm => (Nivat.Colle35.Sphi_negSymm d m).mp hm) hdet

/-! ## §8  From a raw `E`-equality hypothesis to the actual `EnvOf` predicate, and the kill of `Bhp`

`not_envOf_of_ray_of_case1` takes `hEB : E B = E Sphi` as a bare hypothesis.  `EnvOf` only gives
`E B ⊆ E Sphi` plus equal `encard` (`LatticeEdges.lean:624-629`); for **finite** `Sphi` these
combine to the full equality via the tree's own `Enveloped.E_eq` (`LatticeEdges.lean:1657`) and
`finite_E_of_finite` (`:317`) — no hand-rolled subset/encard argument needed. -/

/-- **Team-lead's step 1, from `EnvOf` itself.**  For any `DecompData d` (`d.m ≥ 2` always), no
`Set` `B` containing a ray `b₀ - t•u'` can satisfy `EnvOf ↑d.Sphi B`, unless `u' = 0`. -/
theorem not_envOf_of_ray_of_case1' {α} [AddCommMonoid α] {η : Config α}
    (d : Nivat.Colle35.DecompData η) {B : Set (ℤ × ℤ)} {u' b₀ : ℤ × ℤ}
    (hray : ∀ t : ℕ, b₀ + (t : ℤ) • (-u') ∈ B)
    (hEnv : Nivat.LE2.EnvOf ((d.Sphi : Set (ℤ × ℤ))) B) :
    u' = 0 :=
  not_envOf_of_ray_of_case1 d hray
    (Nivat.LE2.Enveloped.E_eq (Nivat.LE2.finite_E_of_finite d.Sphi.finite_toSet) hEnv)

/-- **`Bhp` is dead as a step-1 witness.**  `Bhp u' vl` (`:476`) contains the whole ray `t • (-u')`
(since `expNormal u' vl ⊥ u'`, `dot_expNormal_u'`), so `not_envOf_of_ray_of_case1'` applies at
`b₀ := 0` and forces `u' = 0` — contradicting `hunimod` (`det u' vl = ±1` needs `u' ≠ 0`).  So
whatever `EnvOf`-compatible `B` `Case1` hands out, it is **never** `Bhp`, and more generally never
unbounded along a single ray in any direction: `not_envOf_of_ray_of_case1'` did not use `-u'`
specifically, only that `hray`'s direction is nonzero after the conclusion. -/
theorem not_envOf_Bhp {α} [AddCommMonoid α] {η : Config α}
    (d : Nivat.Colle35.DecompData η) {u' vl : ℤ × ℤ}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) :
    ¬ Nivat.LE2.EnvOf ((d.Sphi : Set (ℤ × ℤ))) (Bhp u' vl) := by
  intro hEnv
  have hray : ∀ t : ℕ, ((0 : ℤ × ℤ)) + (t : ℤ) • (-u') ∈ Bhp u' vl := by
    intro t
    simp only [Bhp, Set.mem_setOf_eq, zero_add]
    rw [dot_smul_right, dot_neg_right, dot_expNormal_u', neg_zero, mul_zero]
  have hu'0 : u' = 0 := not_envOf_of_ray_of_case1' d hray hEnv
  have hne : det u' vl ≠ 0 := by rcases hunimod with h | h <;> simp [h]
  exact hne (by simp [hu'0, det])

/-! ## §9  From `E`-boundedness to `B.Finite`, and the actual death of `UPushable`

`E B` membership doesn't merely forbid rays (§6–§8) — `IsEdge` requires `(face B n).Nontrivial`,
hence *nonempty*, hence an actual `dot n`-maximiser on `B` (`LatticeEdges.lean:160/214/217`).  Two
non-parallel bounding directions make `B` itself finite, handing `UPushable` straight to
`not_UPushable_of_finite_pos` (`:423`, binders `hunimod hN hBfin hBne` — checked by `grep` before
writing this section). -/

/-- **`n ∈ E B` bounds `dot n` above on `B`.**  The face's nonempty maximiser is the bound. -/
theorem bddAbove_dot_of_mem_E {B : Set (ℤ × ℤ)} {n : ℤ × ℤ} (hn : n ∈ Nivat.LE2.E B) :
    ∃ c : ℤ, ∀ y ∈ B, dot n y ≤ c := by
  obtain ⟨-, hnt⟩ := hn
  obtain ⟨z, hz⟩ := hnt.nonempty
  exact ⟨dot n z, hz.2⟩

/-- **Two non-parallel bounded directions make a set finite.**  `z ↦ (dot n z, dot n' z)` is
injective on `B` (`eq_zero_of_dot_eq_zero_of_det_ne_zero` applied to `z - w`) with image inside a
finite `Set.Icc`. -/
theorem finite_of_two_nonparallel_bounded {B : Set (ℤ × ℤ)} {n n' : ℤ × ℤ} {c₁ c₂ c₃ c₄ : ℤ}
    (hdet : det n n' ≠ 0)
    (h1 : ∀ y ∈ B, dot n y ≤ c₁) (h2 : ∀ y ∈ B, -c₂ ≤ dot n y)
    (h3 : ∀ y ∈ B, dot n' y ≤ c₃) (h4 : ∀ y ∈ B, -c₄ ≤ dot n' y) :
    B.Finite := by
  have himg : ((fun z => (dot n z, dot n' z)) '' B).Finite := by
    apply Set.Finite.subset (Set.finite_Icc ((-c₂, -c₄) : ℤ × ℤ) (c₁, c₃))
    rintro _ ⟨z, hz, rfl⟩
    refine Set.mem_Icc.mpr ⟨?_, ?_⟩
    · exact ⟨h2 z hz, h4 z hz⟩
    · exact ⟨h1 z hz, h3 z hz⟩
  have hinj : Set.InjOn (fun z => (dot n z, dot n' z)) B := by
    rintro z hz w hw hzw
    simp only [Prod.mk.injEq] at hzw
    have hn0 : dot n (z - w) = 0 := by rw [Nivat.LE2.dot_sub]; omega
    have hn0' : dot n' (z - w) = 0 := by rw [Nivat.LE2.dot_sub]; omega
    have hzw0 : z - w = 0 := eq_zero_of_dot_eq_zero_of_det_ne_zero hn0 hn0' hdet
    exact sub_eq_zero.mp hzw0
  exact Set.Finite.of_finite_image himg hinj

/-- **`EnvOf ↑d.Sphi B ⟹ B.Finite`.**  Combines `bddAbove_dot_of_mem_E` at the two non-parallel
edge normals `exists_two_nonparallel_edgeNormals_of_Sphi` produces, transported into `E B` via
`Enveloped.E_eq` + `Sphi_negSymm` (for the antipodal bound on each side). -/
theorem finite_of_envOf_Sphi {α} [AddCommMonoid α] {η : Config α}
    (d : Nivat.Colle35.DecompData η) {B : Set (ℤ × ℤ)}
    (hEnv : Nivat.LE2.EnvOf ((d.Sphi : Set (ℤ × ℤ))) B) :
    B.Finite := by
  have hEB : Nivat.LE2.E B = Nivat.LE2.E ((d.Sphi : Set (ℤ × ℤ))) :=
    Nivat.LE2.Enveloped.E_eq (Nivat.LE2.finite_E_of_finite d.Sphi.finite_toSet) hEnv
  have hm2 : 2 ≤ d.m := d.hm
  have hlt1 : 1 < d.m := by omega
  have hlt0 : 0 < d.m := by omega
  have h01 : (⟨0, hlt0⟩ : Fin d.m) ≠ ⟨1, hlt1⟩ := by
    intro hcontra
    exact absurd (congrArg Fin.val hcontra) (by norm_num)
  obtain ⟨n, n', hn, hn', hdet⟩ :=
    exists_two_nonparallel_edgeNormals_of_Sphi d ⟨0, hlt0⟩ ⟨1, hlt1⟩ h01
  have hnB : n ∈ Nivat.LE2.E B := hEB ▸ hn
  have hn'B : n' ∈ Nivat.LE2.E B := hEB ▸ hn'
  have hnegn : -n ∈ Nivat.LE2.E ((d.Sphi : Set (ℤ × ℤ))) :=
    (Nivat.Colle35.Sphi_negSymm d n).mp hn
  have hnegn' : -n' ∈ Nivat.LE2.E ((d.Sphi : Set (ℤ × ℤ))) :=
    (Nivat.Colle35.Sphi_negSymm d n').mp hn'
  have hnegnB : -n ∈ Nivat.LE2.E B := hEB ▸ hnegn
  have hnegn'B : -n' ∈ Nivat.LE2.E B := hEB ▸ hnegn'
  obtain ⟨c1, h1⟩ := bddAbove_dot_of_mem_E hnB
  obtain ⟨c2, h2⟩ := bddAbove_dot_of_mem_E hnegnB
  obtain ⟨c3, h3⟩ := bddAbove_dot_of_mem_E hn'B
  obtain ⟨c4, h4⟩ := bddAbove_dot_of_mem_E hnegn'B
  refine finite_of_two_nonparallel_bounded (c₁ := c1) (c₂ := c2) (c₃ := c3) (c₄ := c4)
    hdet h1 ?_ h3 ?_
  · intro y hy
    have := h2 y hy
    rw [Nivat.LE2.dot_neg_left] at this
    linarith
  · intro y hy
    have := h4 y hy
    rw [Nivat.LE2.dot_neg_left] at this
    linarith

/-- **Headline: `UPushable` is dead for `Case1`'s `B`, unconditionally.**  Not just "no ray" —
`B` itself is finite, so `not_UPushable_of_finite_pos` applies outright once `B` is nonempty
(supplied here directly from `E B`'s nonempty face, *not* from `↑d.Sphi ⊆ B` — `L1SweepBridge.lean`
`:106-108` is right that the latter doesn't hold in general, but it's not what is used here). -/
theorem not_uPushable_of_case1 {α} [AddCommMonoid α] {η : Config α}
    (d : Nivat.Colle35.DecompData η) {B : Set (ℤ × ℤ)} {u' vl : ℤ × ℤ} {N : ℕ}
    (hEnv : Nivat.LE2.EnvOf ((d.Sphi : Set (ℤ × ℤ))) B)
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) (hN : 0 < N) :
    ¬ Nivat.HbaseBridge.UPushable B vl u' N := by
  have hBfin := finite_of_envOf_Sphi d hEnv
  have hBne : B.Nonempty := by
    have hEB : Nivat.LE2.E B = Nivat.LE2.E ((d.Sphi : Set (ℤ × ℤ))) :=
      Nivat.LE2.Enveloped.E_eq (Nivat.LE2.finite_E_of_finite d.Sphi.finite_toSet) hEnv
    have hm2 : 2 ≤ d.m := d.hm
    have hlt0 : 0 < d.m := by omega
    obtain ⟨n, -, -, hnE, -, -, -⟩ :=
      exists_edgeNormal_of_dot_h_eq_zero d (⟨0, hlt0⟩ : Fin d.m)
    have hnB : n ∈ Nivat.LE2.E B := hEB ▸ hnE
    obtain ⟨-, hnt⟩ := hnB
    obtain ⟨z, hz⟩ := hnt.nonempty
    exact ⟨z, hz.1⟩
  exact not_UPushable_of_finite_pos hunimod hN hBfin hBne

/-! ## §10  Hole 1 (`hwin`): the level of row `i` is constant, `= dot (expNormal u' vl) b₀ + n`

Team-lead's dispatch, step 1.  `coverEnum vl u' b₀ i j` (`L1CoverWedge.lean:387`) decodes `i` via
`pairEnum i = (p, n)` and is `p + (d b₀ - d p + n) • vl + j • u'` where `d := dot (expNormal u' vl)`.
Since `d vl = 1` (`dot_expNormal_vl hunimod`) and `d u' = 0` (`dot_expNormal_u'`), the `p`- and
`j`-dependence cancels and only `d b₀ + n` survives — pure linear-algebra, no `S`/`a`/`hwin`
content yet. -/

theorem dot_expNormal_coverEnum {u' vl b₀ : ℤ × ℤ} (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (i j : ℕ) :
    dot (expNormal u' vl) (Nivat.ColleReg.coverEnum vl u' b₀ i j) =
      dot (expNormal u' vl) b₀ + ((Nivat.ColleReg.pairEnum i).2 : ℤ) := by
  unfold Nivat.ColleReg.coverEnum
  simp only [Nivat.LE2.dot_add, dot_smul_right, dot_expNormal_vl hunimod, dot_expNormal_u',
    mul_one, mul_zero, add_zero]
  ring

/-! ## §11  Hole 1 (`hwin`) forces the first conjunct of `hcorner`

Team-lead's dispatch, step 2.  Given `B.Finite`, `hunimod`, and a genuine `hwin` witness, no
`z ∈ S.erase a` can have `dot (expNormal u' vl) (z - a) < 0`: the row through `b₀` at `n = 0`
forces `z + (coverEnum … j - a)` off every row (§10: rows sit at level `≥ dot (expNormal u' vl)
b₀`, strictly above our point's level) and, for `j` large enough that `dot (expDual u' vl)
(z + (coverEnum … j - a))` exceeds every value `B` realises under `dot (expDual u' vl)` (a finite
set, `B.Finite`), off `halfStrip B vl` too — leaving `hwin` nothing to land the translate on. -/

/-- Pure arithmetic: some natural number pushes `base + j` past any fixed integer `M`. -/
theorem exists_nat_gt_sub (M base : ℤ) : ∃ j : ℕ, M < base + (j : ℤ) := by
  by_cases h : 0 ≤ M - base + 1
  · refine ⟨(M - base + 1).toNat, ?_⟩
    rw [Int.toNat_of_nonneg h]; omega
  · exact ⟨0, by simp only [Nat.cast_zero, add_zero]; omega⟩

theorem hwin_imp_corner_fst {S : Finset (ℤ × ℤ)} {a u' vl b₀ : ℤ × ℤ} {B : Set (ℤ × ℤ)}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) (hBfin : B.Finite) (hb₀ : b₀ ∈ B)
    (hwin : ∀ i j : ℕ, ∀ z ∈ S.erase a,
      z + (Nivat.ColleReg.coverEnum vl u' b₀ i j - a) ∈
        Nivat.Colle35.halfStrip B vl ∪
          (⋃ i' ∈ {i' : ℕ | i' < i}, Set.range (Nivat.ColleReg.coverEnum vl u' b₀ i')) ∪
          (Nivat.ColleReg.coverEnum vl u' b₀ i '' {j' : ℕ | j' < j})) :
    ∀ z ∈ S.erase a, 0 ≤ dot (expNormal u' vl) (z - a) := by
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨z₀, hz₀, hneg⟩ := hcon
  set i₀ : ℕ := Denumerable.eqv ((ℤ × ℤ) × ℕ) (b₀, 0) with hi₀def
  have hpair : Nivat.ColleReg.pairEnum i₀ = (b₀, 0) := by
    show (Denumerable.eqv ((ℤ × ℤ) × ℕ)).symm i₀ = (b₀, 0)
    rw [hi₀def, Equiv.symm_apply_apply]
  have hlevel_row : ∀ i' j' : ℕ,
      dot (expNormal u' vl) (Nivat.ColleReg.coverEnum vl u' b₀ i' j') =
        dot (expNormal u' vl) b₀ + ((Nivat.ColleReg.pairEnum i').2 : ℤ) :=
    fun i' j' => dot_expNormal_coverEnum hunimod i' j'
  have hlevel_ge : ∀ i' j' : ℕ, dot (expNormal u' vl) b₀ ≤
      dot (expNormal u' vl) (Nivat.ColleReg.coverEnum vl u' b₀ i' j') := by
    intro i' j'
    rw [hlevel_row i' j']
    have h0 : (0 : ℤ) ≤ ((Nivat.ColleReg.pairEnum i').2 : ℤ) := by positivity
    linarith
  have hrow_i0 : ∀ j : ℕ, Nivat.ColleReg.coverEnum vl u' b₀ i₀ j = b₀ + (j : ℤ) • u' := by
    intro j
    simp [Nivat.ColleReg.coverEnum, hpair]
  have hlevel_p : ∀ j : ℕ, dot (expNormal u' vl)
      (z₀ + (Nivat.ColleReg.coverEnum vl u' b₀ i₀ j - a)) =
        dot (expNormal u' vl) (z₀ - a) + dot (expNormal u' vl) b₀ := by
    intro j
    have heq : z₀ + (Nivat.ColleReg.coverEnum vl u' b₀ i₀ j - a) =
        (z₀ - a) + Nivat.ColleReg.coverEnum vl u' b₀ i₀ j := by abel
    have h1 := hlevel_row i₀ j
    rw [hpair] at h1
    simp only [Nat.cast_zero, add_zero] at h1
    rw [heq, Nivat.LE2.dot_add, h1]
  have hnotrow : ∀ j i' j' : ℕ,
      z₀ + (Nivat.ColleReg.coverEnum vl u' b₀ i₀ j - a) ≠
        Nivat.ColleReg.coverEnum vl u' b₀ i' j' := by
    intro j i' j' hcontra
    have h1 := hlevel_p j
    have h2 := hlevel_ge i' j'
    rw [hcontra] at h1
    linarith [h1, h2, hneg]
  set DB : Finset ℤ := hBfin.toFinset.image (fun b => dot (Nivat.L3Band.expDual u' vl) b) with hDBdef
  obtain ⟨j₀, hj₀⟩ : ∃ j : ℕ,
      dot (Nivat.L3Band.expDual u' vl) (z₀ - a + b₀) + (j : ℤ) ∉ (DB : Set ℤ) := by
    rcases DB.eq_empty_or_nonempty with hDBe | hDBne
    · exact ⟨0, by simp [hDBe]⟩
    · obtain ⟨j, hj⟩ :=
        exists_nat_gt_sub (DB.max' hDBne) (dot (Nivat.L3Band.expDual u' vl) (z₀ - a + b₀))
      refine ⟨j, fun hmem => ?_⟩
      have hle := DB.le_max' _ hmem
      exact absurd hj (not_lt.mpr hle)
  have hrow_p : z₀ + (Nivat.ColleReg.coverEnum vl u' b₀ i₀ j₀ - a) =
      (z₀ - a + b₀) + (j₀ : ℤ) • u' := by
    rw [hrow_i0 j₀]; abel
  have hmem := hwin i₀ j₀ z₀ hz₀
  rcases hmem with (hmem | hmem) | hmem
  · obtain ⟨b, hbB, t, hbt⟩ := hmem
    apply hj₀
    have hdualp : dot (Nivat.L3Band.expDual u' vl)
        (z₀ + (Nivat.ColleReg.coverEnum vl u' b₀ i₀ j₀ - a)) =
        dot (Nivat.L3Band.expDual u' vl) (z₀ - a + b₀) + (j₀ : ℤ) := by
      rw [hrow_p, Nivat.LE2.dot_add, dot_smul_right (Nivat.L3Band.expDual u' vl) (j₀ : ℤ) u',
        Nivat.L3Band.dot_expDual_u' hunimod, mul_one]
    rw [hbt, Nivat.LE2.dot_add, dot_smul_right (Nivat.L3Band.expDual u' vl) (t : ℤ) vl,
      Nivat.L3Band.dot_expDual_vl u' vl, mul_zero, add_zero] at hdualp
    rw [← hdualp]
    exact Finset.mem_image.mpr ⟨b, hBfin.mem_toFinset.mpr hbB, rfl⟩
  · simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_range] at hmem
    obtain ⟨i', hi'lt, j', hj'eq⟩ := hmem
    exact hnotrow j₀ i' j' hj'eq.symm
  · simp only [Set.mem_image, Set.mem_setOf_eq] at hmem
    obtain ⟨j', hj'lt, hj'eq⟩ := hmem
    exact hnotrow j₀ i₀ j' hj'eq.symm

/-! ## §12  `hwin` still fails at a corner satisfying `expNormal`-minimality

Team-lead's bridge fix (`L1SweepBridge.wedgeResidualR_of_hwin`) adds, for free, that `a` is
`expNormal (u' - K•vl) vl`-minimal over all of `S` (from `exists_vertex_of_generating_dir`).
This section checks whether that extra hypothesis is enough to force `hwin`: **it is not.**  The
obstruction is exactly the one flagged in the dispatch — `coverEnum`'s row index `i` (via the
opaque `Denumerable.eqv` bijection `pairEnum`) carries **no relation** to the `expNormal`-level
`n`, so "no prior row" (`i = 0`) does not mean "no row at a comparable level"; it can starve a
finite `halfStrip` of any chance to absorb more than one point of `S`.  The witness below needs
no knowledge of the actual value `pairEnum 0` — only that whatever `x`-offset it contributes is a
single fixed integer, which cannot equal two different required values at once. -/

section HwinCounterexample

theorem expNormal_hwin_seed_eq : expNormal ((1 : ℤ), (0 : ℤ)) ((0 : ℤ), (1 : ℤ)) = (0, 1) := by
  simp [expNormal, det]

/-- `a := (0,0)` is `expNormal`-minimal over `S := {(0,0),(1,0),(2,0)}` (all three points share
`expNormal`-level `0`, so minimality holds with equality — this is the hypothesis the fixed
bridge hands over for free). -/
theorem hwin_seed_minimal :
    ∀ b ∈ ({((0 : ℤ), (0 : ℤ)), (1, 0), (2, 0)} : Finset (ℤ × ℤ)),
      dot (expNormal ((1 : ℤ), (0 : ℤ)) ((0 : ℤ), (1 : ℤ))) ((0 : ℤ), (0 : ℤ)) ≤
        dot (expNormal ((1 : ℤ), (0 : ℤ)) ((0 : ℤ), (1 : ℤ))) b := by
  intro b hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  rw [expNormal_hwin_seed_eq]
  rcases hb with rfl | rfl | rfl <;> simp [dot]

/-- **The obstruction, stated for an arbitrary enumeration.**  The original proof of this fact
(below, specialized to `coverEnum`) never used anything about the enumeration beyond "`enum 0 0`
is *some* single fixed point" — at `i = j = 0`, `{i' | i' < 0} = ∅` and `{j' | j' < 0} = ∅` in
`ℕ`, so `hwin` collapses to one fixed vector translating **every** point of `S.erase a` into
`halfStrip {(0,0)} (0,1)`.  Universally quantifying `enum` here means the kernel certifies the
general claim — this refutes `hwin` for `coverEnum`, `levelEnum`, or any other choice at once,
i.e. it refutes `∃ enum, hwin ∧ …` (`not_exists_enum_hwin_seed` below), not just one witness. -/
theorem not_hwin_seed_forall (enum : ℕ → ℕ → ℤ × ℤ) :
    ¬ (∀ i j : ℕ, ∀ z ∈ ({((0 : ℤ), (0 : ℤ)), (1, 0), (2, 0)} : Finset (ℤ × ℤ)).erase (0, 0),
        z + (enum i j - (0, 0)) ∈
          Nivat.Colle35.halfStrip ({((0 : ℤ), (0 : ℤ))} : Set (ℤ × ℤ)) ((0 : ℤ), (1 : ℤ))
            ∪ (⋃ i' ∈ {i' : ℕ | i' < i}, Set.range (enum i'))
            ∪ (enum i '' {j' : ℕ | j' < j})) := by
  intro hwin
  have h1 := hwin 0 0 (1, 0) (by decide)
  have h2 := hwin 0 0 (2, 0) (by decide)
  have hempty1 : ({x : ℕ | x < 0} : Set ℕ) = ∅ := by ext x; simp
  rw [hempty1] at h1 h2
  simp only [Set.biUnion_empty, Set.image_empty, Set.union_empty] at h1 h2
  unfold Nivat.Colle35.halfStrip at h1 h2
  obtain ⟨b1, hb1, t1, ht1⟩ := h1
  obtain ⟨b2, hb2, t2, ht2⟩ := h2
  simp only [Set.mem_singleton_iff] at hb1 hb2
  subst hb1; subst hb2
  have f1 := congrArg Prod.fst ht1
  have f2 := congrArg Prod.fst ht2
  simp only [Prod.fst_add, Prod.fst_sub, Prod.smul_fst, smul_eq_mul, mul_zero, add_zero,
    zero_add] at f1 f2
  omega

/-- **No enumeration at all works for this seed**, `HwinHoleE`'s own `∃ enum` shape. -/
theorem not_exists_enum_hwin_seed :
    ¬ ∃ enum : ℕ → ℕ → ℤ × ℤ,
        ∀ i j : ℕ, ∀ z ∈ ({((0 : ℤ), (0 : ℤ)), (1, 0), (2, 0)} : Finset (ℤ × ℤ)).erase (0, 0),
          z + (enum i j - (0, 0)) ∈
            Nivat.Colle35.halfStrip ({((0 : ℤ), (0 : ℤ))} : Set (ℤ × ℤ)) ((0 : ℤ), (1 : ℤ))
              ∪ (⋃ i' ∈ {i' : ℕ | i' < i}, Set.range (enum i'))
              ∪ (enum i '' {j' : ℕ | j' < j}) :=
  fun ⟨enum, hwin⟩ => not_hwin_seed_forall enum hwin

/-- **The counterexample.**  `hwin` fails at `i = j = 0`: with no prior rows and an empty current
row prefix, both `(1,0)` and `(2,0)` (the two nonzero points of `S.erase a`) would need row `0`'s
translate to land in `halfStrip {(0,0)} (0,1) = {(0,t) : t ≥ 0}`, i.e. the `x`-coordinate of the
translate must be exactly `0`.  Since the translate's `x`-coordinate is `z.1 + X₀` for a single
fixed (unknown) integer `X₀` (row `0`'s own `x`-offset, contributed by `coverEnum ... 0 0`, whose
`vl = (0,1)`-multiple leaves the `x`-coordinate untouched), it can equal `0` for at most one of
`z = (1,0)` (needs `X₀ = -1`) and `z = (2,0)` (needs `X₀ = -2`) — never both.  Now a one-line
specialization of `not_hwin_seed_forall`.

**Which hole this refutes.**  This kills `hwin` for the `B.Finite`-only version of `HwinHoleE`
(no `EnvOf` conjunct), retracted 2026-09-19 in favor of the `B.Finite → EnvOf (Sphi:Set(ℤ×ℤ)) B →`
form now in `L1SweepBridge.lean`. -/
theorem not_hwin_seed :
    ¬ (∀ i j : ℕ, ∀ z ∈ ({((0 : ℤ), (0 : ℤ)), (1, 0), (2, 0)} : Finset (ℤ × ℤ)).erase (0, 0),
        z + (Nivat.ColleReg.coverEnum ((0 : ℤ), (1 : ℤ)) ((1 : ℤ), (0 : ℤ)) (0, 0) i j
              - (0, 0)) ∈
          Nivat.Colle35.halfStrip ({((0 : ℤ), (0 : ℤ))} : Set (ℤ × ℤ)) ((0 : ℤ), (1 : ℤ))
            ∪ (⋃ i' ∈ {i' : ℕ | i' < i},
                 Set.range
                   (Nivat.ColleReg.coverEnum ((0 : ℤ), (1 : ℤ)) ((1 : ℤ), (0 : ℤ)) (0, 0) i'))
            ∪ (Nivat.ColleReg.coverEnum ((0 : ℤ), (1 : ℤ)) ((1 : ℤ), (0 : ℤ)) (0, 0) i ''
                 {j' : ℕ | j' < j})) :=
  not_hwin_seed_forall (Nivat.ColleReg.coverEnum ((0 : ℤ), (1 : ℤ)) ((1 : ℤ), (0 : ℤ)) (0, 0))

end HwinCounterexample

/-! ## §13  A level-ordered enumeration, and its `hK`

Team-lead's dispatch: §12's counterexample showed the obstruction is exactly `coverEnum`'s row
index carrying no relation to `expNormal`-level (`pairEnum` is an arbitrary bijection).  Since
`HbaseBridge.hbase_at_of_sweep_of_isGeneratingSet` takes `enum : ℕ → ℕ → ℤ × ℤ` as an ordinary
parameter (`coverEnum` was never forced), `levelEnum` below replaces it: **row `i` is entirely the
level-`(dot (expNormal u' vl) b₀ + i)` slice** of `wedgeFull B vl u'`.  Column `j`, decoded via
`pairEnum` to a pair `(p, t)`, places `p`'s `u'`-ray at step `t`, shifted along `vl` to land
exactly on level `i`; if `p ∉ B` the column falls back to `b₀`'s own level-`i` point (column
`t = 0` on every row), so no coverage is lost — only some columns are wasted on the fallback.
`dot_expNormal_levelEnum` is the unconditional analogue of `dot_expNormal_coverEnum`: *every*
point of row `i`, not just some of them, sits at exactly that level. -/

section LevelEnum

open Classical in
/-- **The level-ordered replacement for `coverEnum`.**  Row `i` is the level-`(dot (expNormal u'
vl) b₀ + i)` slice of `wedgeFull B vl u'`: column `j`, decoded via `pairEnum` to `(p, t)`, is `p`'s
`u'`-ray at step `t`, shifted along `vl` to land on level `i` — provided `p ∈ B`; otherwise the
column falls back to `b₀`'s own level-`i` point. -/
noncomputable def levelEnum (vl u' b₀ : ℤ × ℤ) (B : Set (ℤ × ℤ)) : ℕ → ℕ → ℤ × ℤ :=
  fun i j =>
    if (Nivat.ColleReg.pairEnum j).1 ∈ B then
      (Nivat.ColleReg.pairEnum j).1
        + (dot (expNormal u' vl) b₀ + (i : ℤ)
            - dot (expNormal u' vl) (Nivat.ColleReg.pairEnum j).1) • vl
        + ((Nivat.ColleReg.pairEnum j).2 : ℤ) • u'
    else
      b₀ + (i : ℤ) • vl

/-- **Every point of row `i` sits at exactly level `dot (expNormal u' vl) b₀ + i`** — the
monotone replacement for `dot_expNormal_coverEnum`, and unconditional (both branches of the `if`
give the same level). -/
theorem dot_expNormal_levelEnum {u' vl b₀ : ℤ × ℤ} {B : Set (ℤ × ℤ)}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) (i j : ℕ) :
    dot (expNormal u' vl) (levelEnum vl u' b₀ B i j) = dot (expNormal u' vl) b₀ + (i : ℤ) := by
  unfold levelEnum
  split
  · rw [Nivat.LE2.dot_add, Nivat.LE2.dot_add, dot_smul_right, dot_smul_right, dot_expNormal_u',
      mul_zero, add_zero, dot_expNormal_vl hunimod, mul_one]
    ring
  · rw [Nivat.LE2.dot_add, dot_smul_right, dot_expNormal_vl hunimod, mul_one]

/-- **`hK`'s covering, level-ordered.**  Every point of `chainFull B vl u' b₀ 0` (i.e. `wedgeFull`
cut at level `≥ dot (expNormal u' vl) b₀`) lands in the row of `levelEnum` matching its level. -/
theorem chainFull_subset_iUnion_range_levelEnum {B : Set (ℤ × ℤ)} {vl u' b₀ : ℤ × ℤ}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) :
    chainFull B vl u' b₀ 0 ⊆ ⋃ i, Set.range (levelEnum vl u' b₀ B i) := by
  intro z hz
  obtain ⟨hz1, hz2⟩ := hz
  obtain ⟨g, hg, t, rfl⟩ := hz1
  obtain ⟨b, hb, k, hk⟩ := mem_fullSweep_iff.mp hg
  subst hk
  have hlev0 : expLevel u' vl b₀ 0 = dot (expNormal u' vl) b₀ := by simp [expLevel]
  rw [hlev0] at hz2
  simp only [Nivat.LE2.halfPlaneGE, Set.mem_setOf_eq] at hz2
  have hzcomp : dot (expNormal u' vl) (b + k • vl + (t : ℤ) • u')
      = dot (expNormal u' vl) b + k := by
    rw [Nivat.LE2.dot_add, Nivat.LE2.dot_add, dot_smul_right, dot_smul_right, dot_expNormal_u',
      dot_expNormal_vl hunimod]
    ring
  rw [hzcomp] at hz2
  set i : ℕ := (dot (expNormal u' vl) b + k - dot (expNormal u' vl) b₀).toNat with hidef
  have hi : (i : ℤ) = dot (expNormal u' vl) b + k - dot (expNormal u' vl) b₀ := by
    rw [hidef, Int.toNat_of_nonneg]; omega
  obtain ⟨j, hj⟩ := (Denumerable.eqv ((ℤ × ℤ) × ℕ)).symm.surjective (b, t)
  have hpe : Nivat.ColleReg.pairEnum j = (b, t) := hj
  have hveq : dot (expNormal u' vl) b₀ + (i : ℤ) - dot (expNormal u' vl) b = k := by
    rw [hi]; ring
  refine Set.mem_iUnion.mpr ⟨i, j, ?_⟩
  show levelEnum vl u' b₀ B i j = b + k • vl + (t : ℤ) • u'
  unfold levelEnum
  rw [hpe, if_pos hb]
  show b + (dot (expNormal u' vl) b₀ + (i : ℤ) - dot (expNormal u' vl) b) • vl + (t : ℤ) • u'
        = b + k • vl + (t : ℤ) • u'
  rw [hveq]

/-- **`hK` itself**, packaged with an arbitrary extra disjunct `D`, matching the shape
`hK_of_coverEnum` supplies to `hbase_at_of_sweep_of_isGeneratingSet` /
`ofSweepEnum` (`L1SweepBridge.lean`). -/
theorem hK_of_levelEnum {B : Set (ℤ × ℤ)} {vl u' b₀ : ℤ × ℤ} {D : Set (ℤ × ℤ)}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) :
    chainFull B vl u' b₀ 0 ⊆ D ∪ (⋃ i, Set.range (levelEnum vl u' b₀ B i)) :=
  (chainFull_subset_iUnion_range_levelEnum hunimod).trans Set.subset_union_right

/-! ### `hwin` against `levelEnum`: still refutable, and the obstruction is enum-agnostic

Deliverable (b).  `not_hwin_seed` (§12) never used anything about `coverEnum`'s internals beyond
"row `0`, column `0` is *some* single fixed point, and no prior row/column exists to absorb a
second erased point of `S`."  That argument goes through verbatim for `levelEnum`: at `i = j = 0`
`hwin` again asks a single fixed translate to place **every** point of `S.erase a` into a
size-`1` `halfStrip`, which is impossible for `|S.erase a| ≥ 2` with distinct `x`-offsets needed.
**So the obstruction is not `coverEnum`'s arbitrary ordering — it is the shape of `hwin` itself**
(finite `D`, only "already-swept" rows/columns) colliding with a `B` too small to hold every
minimal-level point of `S` at once.  Ordering the rows by level does not touch this; the seed
below reuses the exact `S, a, B, u', vl` of §12 and needs no knowledge of the concrete value
`Nivat.ColleReg.pairEnum 0` computes to.

**Which hole this refutes.**  Like `not_hwin_seed`, this kills the `B.Finite`-only `HwinHoleE`
(retracted 2026-09-19).  Unlike `not_hwin_seed`, it also **survives the retraction**: `levelEnum`'s
row `0` is level-constant by construction (`dot_expNormal_levelEnum`), which is exactly the
hypothesis of `L1SweepBridge.not_hwin_of_row_zero_levelConst_envOf` — so this seed is not just a
counterexample to the old hole, it is a concrete instance of that theorem's general obstruction
against the current `B.Finite → EnvOf (Sphi:Set(ℤ×ℤ)) B →` form.  Cited there, not restated. -/

theorem not_hwin_seed_levelEnum :
    ¬ (∀ i j : ℕ, ∀ z ∈ ({((0 : ℤ), (0 : ℤ)), (1, 0), (2, 0)} : Finset (ℤ × ℤ)).erase (0, 0),
        z + (levelEnum ((0 : ℤ), (1 : ℤ)) ((1 : ℤ), (0 : ℤ)) ((0 : ℤ), (0 : ℤ))
              ({((0 : ℤ), (0 : ℤ))} : Set (ℤ × ℤ)) i j - (0, 0)) ∈
          Nivat.Colle35.halfStrip ({((0 : ℤ), (0 : ℤ))} : Set (ℤ × ℤ)) ((0 : ℤ), (1 : ℤ))
            ∪ (⋃ i' ∈ {i' : ℕ | i' < i},
                 Set.range
                   (levelEnum ((0 : ℤ), (1 : ℤ)) ((1 : ℤ), (0 : ℤ)) ((0 : ℤ), (0 : ℤ))
                     ({((0 : ℤ), (0 : ℤ))} : Set (ℤ × ℤ)) i'))
            ∪ (levelEnum ((0 : ℤ), (1 : ℤ)) ((1 : ℤ), (0 : ℤ)) ((0 : ℤ), (0 : ℤ))
                 ({((0 : ℤ), (0 : ℤ))} : Set (ℤ × ℤ)) i ''
                 {j' : ℕ | j' < j})) :=
  not_hwin_seed_forall
    (levelEnum ((0 : ℤ), (1 : ℤ)) ((1 : ℤ), (0 : ℤ)) ((0 : ℤ), (0 : ℤ))
      ({((0 : ℤ), (0 : ℤ))} : Set (ℤ × ℤ)))

/-! ### The live question (team-lead §3): does `EnvOf ↑Sphi B` save `hwin`?

**No — because `Sphi` and `S` are provably unrelated in the tree.**  `RegionSteps.lean:2316-2332`
records, in its own words, that "Collé never identifies the two sets" (`Sgen`, Lemma 2.4's
generating set — the `S` inside `hwin` — versus `𝒮_φ` = `d.Sphi`, the chain's index set), and
that a field once asserting `decomp.Sphi = S` by fiat was deleted for exactly this reason.  So
`HwinHoleE`'s `Sphi` argument is a genuinely free `Finset`, independent of `S`: nothing forces a
witness's `B` (fat enough only relative to `Sphi`) to be fat enough relative to `S`.

The witness: take `Sphi := B := {(0,0)}`.  A singleton is lattice-convex
(`Nivat.LE2.isLatticeConvexRegion_singleton`) and reflexively `Enveloped`
(`Nivat.LE2.enveloped_refl`), so `EnvOf {(0,0)} {(0,0)}` holds outright — `B` is maximally fat
*relative to `Sphi`* (it equals it) while remaining exactly the too-small `B` of `not_hwin_seed`
relative to the untouched `S = {(0,0),(1,0),(2,0)}`.  `not_exists_enum_hwin_seed` already refutes
the `∃ enum` conjunct for this `S`/`B`/`vl`, so `EnvOf` contributes nothing here: the same
counterexample survives unchanged.  **This does not kill `hwin` for the real chain** (there
`Sphi = d.Sphi` is *not* a free parameter — it is whatever `DecompDataZ` actually produces, and
may in fact relate to `S` through some unproved geometric fact); it shows the `Prop` `HwinHoleE`
as currently stated is refutable by choosing an adversarial `Sphi`, i.e. **the gap is a missing
lemma tying `S` to `Sphi`, not a proof obligation dischargeable from `EnvOf` alone.** -/

theorem envOf_singleton_self : Nivat.LE2.EnvOf ({((0 : ℤ), (0 : ℤ))} : Set (ℤ × ℤ))
    ({((0 : ℤ), (0 : ℤ))} : Set (ℤ × ℤ)) :=
  Nivat.LE2.enveloped_refl _ (Nivat.LE2.isLatticeConvexRegion_singleton _)

/-- **The `EnvOf` finding.**  `EnvOf Sphi B` is satisfiable (by `Sphi = B = {(0,0)}`) at the same
time as the `∃ enum, hwin` conjunct is refuted (for the untouched `S = {(0,0),(1,0),(2,0)}`) —
so requiring `EnvOf ↑Sphi B` in `HwinHoleE` does not, by itself, save `hwin` when `Sphi` is free. -/
theorem envOf_holds_and_hwin_seed_refuted :
    Nivat.LE2.EnvOf ({((0 : ℤ), (0 : ℤ))} : Set (ℤ × ℤ)) ({((0 : ℤ), (0 : ℤ))} : Set (ℤ × ℤ)) ∧
      ¬ ∃ enum : ℕ → ℕ → ℤ × ℤ,
          ∀ i j : ℕ, ∀ z ∈ ({((0 : ℤ), (0 : ℤ)), (1, 0), (2, 0)} : Finset (ℤ × ℤ)).erase (0, 0),
            z + (enum i j - (0, 0)) ∈
              Nivat.Colle35.halfStrip ({((0 : ℤ), (0 : ℤ))} : Set (ℤ × ℤ)) ((0 : ℤ), (1 : ℤ))
                ∪ (⋃ i' ∈ {i' : ℕ | i' < i}, Set.range (enum i'))
                ∪ (enum i '' {j' : ℕ | j' < j}) :=
  ⟨envOf_singleton_self, not_exists_enum_hwin_seed⟩

end LevelEnum

end Nivat.HbaseFlatSeed

section HflatReceipts

#print axioms Nivat.HbaseFlatSeed.not_doubly_lower_iff_dual_min
#print axioms Nivat.HbaseFlatSeed.cutBand_subset_wedgeFull_of_dual_min
#print axioms Nivat.HbaseFlatSeed.det_h1F_h2F
#print axioms Nivat.HbaseFlatSeed.hunimodF
#print axioms Nivat.HbaseFlatSeed.hlt_F
#print axioms Nivat.HbaseFlatSeed.dot_expNormal_levelEnum
#print axioms Nivat.HbaseFlatSeed.chainFull_subset_iUnion_range_levelEnum
#print axioms Nivat.HbaseFlatSeed.hK_of_levelEnum
#print axioms Nivat.HbaseFlatSeed.not_hwin_seed_levelEnum
#print axioms Nivat.HbaseFlatSeed.not_hwin_seed_forall
#print axioms Nivat.HbaseFlatSeed.not_exists_enum_hwin_seed
#print axioms Nivat.HbaseFlatSeed.envOf_singleton_self
#print axioms Nivat.HbaseFlatSeed.envOf_holds_and_hwin_seed_refuted
#print axioms Nivat.HbaseFlatSeed.not_dual_min_F
#print axioms Nivat.HbaseFlatSeed.doubly_lower_witness_F
#print axioms Nivat.HbaseFlatSeed.escapes_witness
#print axioms Nivat.HbaseFlatSeed.hunimodGF
#print axioms Nivat.HbaseFlatSeed.hlt_GF
#print axioms Nivat.HbaseFlatSeed.dual_min_GF
#print axioms Nivat.HbaseFlatSeed.not_collinear_GF
#print axioms Nivat.HbaseFlatSeed.no_escape_despite_noncollinear
#print axioms Nivat.HbaseFlatSeed.dot_expNormal_swap_eq
#print axioms Nivat.HbaseFlatSeed.dot_expNormal_swap_eq_lambda
#print axioms Nivat.HbaseFlatSeed.dot_expNormal_swap_self_eq_one
#print axioms Nivat.HbaseFlatSeed.dot_expNormal_swap_eq_lambda_cases
#print axioms Nivat.HbaseFlatSeed.dot_expNormal_swap_eq_zero_iff
#print axioms Nivat.HbaseFlatSeed.det_eq_zero_of_det_vl_eq_zero
#print axioms Nivat.HbaseFlatSeed.exists_not_parallel_vl_of_h_dir
#print axioms Nivat.HbaseFlatSeed.Sphi_nonempty
#print axioms Nivat.HbaseFlatSeed.rdot_toReal_neg
#print axioms Nivat.HbaseFlatSeed.exists_hnc_of_decompData
#print axioms Nivat.HbaseFlatSeed.exists_hnc_of_decompData_det
#print axioms Nivat.HbaseFlatSeed.dot_expNormal_shear_fst
#print axioms Nivat.HbaseFlatSeed.dot_expNormal_shear_snd
#print axioms Nivat.HbaseFlatSeed.det_shear_snd_vl
#print axioms Nivat.HbaseFlatSeed.exists_shear_sign_agree
#print axioms Nivat.HbaseFlatSeed.not_exists_shear_sign_agree_neg
#print axioms Nivat.HbaseFlatSeed.c_shift_of_UPushable_rep
#print axioms Nivat.HbaseFlatSeed.not_UPushable_of_finite_pos
#print axioms Nivat.HbaseFlatSeed.uPushable_Bhp
#print axioms Nivat.HbaseFlatSeed.infinite_Bhp
#print axioms Nivat.HbaseFlatSeed.dot_le_of_ray_mem_face
#print axioms Nivat.HbaseFlatSeed.dot_neg_right
#print axioms Nivat.HbaseFlatSeed.eq_zero_of_dot_eq_zero_of_det_ne_zero
#print axioms Nivat.HbaseFlatSeed.not_envOf_of_ray_of_two_edges
#print axioms Nivat.HbaseFlatSeed.det_perp_perp
#print axioms Nivat.HbaseFlatSeed.perp_ne_zero_local
#print axioms Nivat.HbaseFlatSeed.mem_E_Sphi_of_dot_eq_zero_local
#print axioms Nivat.HbaseFlatSeed.exists_edgeNormal_of_dot_h_eq_zero
#print axioms Nivat.HbaseFlatSeed.exists_two_nonparallel_edgeNormals_of_Sphi
#print axioms Nivat.HbaseFlatSeed.not_envOf_of_ray_of_case1
#print axioms Nivat.HbaseFlatSeed.not_envOf_of_ray_of_case1'
#print axioms Nivat.HbaseFlatSeed.not_envOf_Bhp
#print axioms Nivat.HbaseFlatSeed.bddAbove_dot_of_mem_E
#print axioms Nivat.HbaseFlatSeed.finite_of_two_nonparallel_bounded
#print axioms Nivat.HbaseFlatSeed.finite_of_envOf_Sphi
#print axioms Nivat.HbaseFlatSeed.not_uPushable_of_case1
#print axioms Nivat.HbaseFlatSeed.dot_expNormal_coverEnum
#print axioms Nivat.HbaseFlatSeed.exists_nat_gt_sub
#print axioms Nivat.HbaseFlatSeed.hwin_imp_corner_fst
#print axioms Nivat.HbaseFlatSeed.expNormal_hwin_seed_eq
#print axioms Nivat.HbaseFlatSeed.hwin_seed_minimal
#print axioms Nivat.HbaseFlatSeed.not_hwin_seed

end HflatReceipts
