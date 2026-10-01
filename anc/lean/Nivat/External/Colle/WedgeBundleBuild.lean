/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.L1StraddleWedge

/-!
# `WedgeResidualR`: packaging the corner route as a bundle constructor

Lane Wbundle's file (exclusive).  Target: `Nivat.ColleReg.exists_wedgeResidualR`
(`RegionSteps.lean:1114`), whose goal is `Nonempty (L1Claim.WedgeResidualR ξ S vl)`.

## What this file is (and is not)

`WedgeResidualR` (`L1Claim.lean:928`) already has an `ofUnimod` smart constructor
(`L1Claim.lean:997`) discharging `hconv` for free from `hunimod` alone — that already reduces
the bundle's six proof fields to three live ones (`hbase`, `hline`, `hstraddle`).  This file
does **not** repeat that reduction; it packages the *further* reduction that already exists for
`hline` and `hstraddle` on one concrete route — Cprobe's placement (`L1Line0.hline_of_placement`,
`L1Line0.lean:327`) and Cconv's corner (`L1StraddleWedge.hstraddle_of_corner`,
`L1StraddleWedge.lean:310`) — as a single bundle-shaped constructor, `WedgeResidualR.ofCorner`,
and checks it against `exists_wedgeResidualR`'s exact goal shape with an `example`.

**This is a further split of the `sorry` at `RegionSteps.lean:1114`, not a discharge of it.**
`hbase` is untouched (no producer anywhere in the tree, `OPEN.md #13`) and `ofCorner` still asks
for it verbatim as a binder, together with the maximal-index witnesses, the placement data, and
the corner data — none of which are proved here, all of which are cited from already-landed,
`#print axioms`-clean declarations.  Per hard rule 4, `sorry TOTAL` and `axiom_closure` are
**unaffected** by this file; what it buys is that a later lane can attack the placement/corner
data against a bundle-shaped goal (`Nonempty (WedgeResidualR ξ S vl)`) instead of the raw
sixteen-argument `exists_L1MaxBResidual_of_corner` term.
-/

set_option autoImplicit false

namespace Nivat.ColleReg.L1Claim

open Nivat Nivat.LE2 Nivat.Colle Nivat.Colle41 Nivat.MaxEnv Nivat.ColleReg
  Nivat.ColleReg.L1Data Nivat.L1StraddleMax Nivat.L1Line0 Nivat.L1StraddleWedge

variable {u' vl : ℤ × ℤ}

/-- **`WedgeResidualR` from Cprobe's placement + Cconv's corner, `hbase` still a binder.**
Builds the bundle's `hline` field from `L1Line0.hline_of_placement`, its `hstraddle` field from
`L1StraddleWedge.hstraddle_of_corner`, and its `hconv` field from `hunimod` alone via
`isLatticeConvexRegion_wedgeFull_of_unimod` (the route `WedgeResidualR.ofUnimod` already uses,
not reproved here — `hconv`'s freedom is cited, not rederived).  What remains as binders:
`hb₀ hunimod hc k hbase` (the C-group data), the maximal index `N₀` with its two `PeriodOn`
witnesses, the placement (`hmin hattain`, jointly the output of `L1Line0.exists_shift_min_level`),
and a corner `a` of a generating set `Sφ`. -/
noncomputable def WedgeResidualR.ofCorner
    {ξ : Config ℤ} {S : Finset (ℤ × ℤ)}
    {e v b₀ : ℤ × ℤ} {c : ℤ} {B : Set (ℤ × ℤ)}
    (hb₀ : b₀ ∈ B) (hunimod : det u' vl = 1 ∨ det u' vl = -1) (hc : 0 < c) (k : ℕ)
    (hbase : PeriodOn (T e ξ) (chainFull B vl u' b₀ k) (c • vl))
    {N₀ : ℕ}
    (hN₀ : PeriodOn (T e ξ) (chainFull B vl u' b₀ (k + N₀)) (c • vl))
    (hN₀1 : ¬ PeriodOn (T e ξ) (chainFull B vl u' b₀ (k + (N₀ + 1))) (c • vl))
    (hmin : ∀ s ∈ S.image (· + v),
      expLevel u' vl b₀ (k + N₀) - 1 ≤ dot (expNormal u' vl) s)
    (hattain : ∃ s ∈ S.image (· + v),
      dot (expNormal u' vl) s = expLevel u' vl b₀ (k + N₀) - 1)
    {Sφ : Finset (ℤ × ℤ)} (hSφ : IsGeneratingSet ξ Sφ) {a : ℤ × ℤ} (ha : a ∈ Sφ)
    (hcorner : ∀ b ∈ Sφ, 0 ≤ dot (expNormal u' vl) (b - a) ∧ 0 ≤ uCoord u' vl a b) :
    WedgeResidualR ξ S vl where
  e := e
  u' := u'
  v := v
  b₀ := b₀
  c := c
  ε := εOf u' vl
  B := B
  k := k
  hb₀ := hb₀
  hunimod := hunimod
  c0 := hc.ne'
  hconv := Nivat.ColleReg.L1Data.isLatticeConvexRegion_wedgeFull_of_unimod hunimod
  hbase := hbase
  hline := hline_of_placement hb₀ hunimod hc hN₀ hN₀1 hmin
  hstraddle := hstraddle_of_corner hunimod hc.le hN₀ hN₀1 hmin hattain hSφ ha hcorner

/-- **Sanity check**: `ofCorner`'s output has exactly `exists_wedgeResidualR`'s goal shape,
`Nonempty (WedgeResidualR ξ S vl)`, with the binder list `WedgeResidualR.ofCorner` asks for
listed out explicitly (not inferred from a name — `PROTOCOL.md` §23). -/
example
    {ξ : Config ℤ} {S : Finset (ℤ × ℤ)}
    {e v b₀ : ℤ × ℤ} {c : ℤ} {B : Set (ℤ × ℤ)}
    (hb₀ : b₀ ∈ B) (hunimod : det u' vl = 1 ∨ det u' vl = -1) (hc : 0 < c) (k : ℕ)
    (hbase : PeriodOn (T e ξ) (chainFull B vl u' b₀ k) (c • vl))
    {N₀ : ℕ}
    (hN₀ : PeriodOn (T e ξ) (chainFull B vl u' b₀ (k + N₀)) (c • vl))
    (hN₀1 : ¬ PeriodOn (T e ξ) (chainFull B vl u' b₀ (k + (N₀ + 1))) (c • vl))
    (hmin : ∀ s ∈ S.image (· + v),
      expLevel u' vl b₀ (k + N₀) - 1 ≤ dot (expNormal u' vl) s)
    (hattain : ∃ s ∈ S.image (· + v),
      dot (expNormal u' vl) s = expLevel u' vl b₀ (k + N₀) - 1)
    {Sφ : Finset (ℤ × ℤ)} (hSφ : IsGeneratingSet ξ Sφ) {a : ℤ × ℤ} (ha : a ∈ Sφ)
    (hcorner : ∀ b ∈ Sφ, 0 ≤ dot (expNormal u' vl) (b - a) ∧ 0 ≤ uCoord u' vl a b) :
    Nonempty (WedgeResidualR ξ S vl) :=
  ⟨WedgeResidualR.ofCorner hb₀ hunimod hc k hbase hN₀ hN₀1 hmin hattain hSφ ha hcorner⟩

section Receipts
/-! Standing `#print axioms` receipt.  Deletable as a block. -/

#print axioms Nivat.ColleReg.L1Claim.WedgeResidualR.ofCorner

end Receipts

end Nivat.ColleReg.L1Claim
