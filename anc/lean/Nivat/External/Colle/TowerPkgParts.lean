/-
Copyright (c) 2026 Nivat Formalization Contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lane-towerpkg
-/
import Nivat.External.Colle.L1RegionBuild

/-!
# lane-towerpkg: `hmw`/`hmvl` for the tower package's composite `m`, generic in `w`

Target consumer: `Nivat/External/Colle/RegionSteps.lean:1743-1757`
(`exists_cutResidualR_of_claim46`'s tower-package `obtain`). This file's scope is the two
conjuncts `∃ m, dot m w = 0 ∧ 0 < dot m vl` (`hmw`/`hmvl`), stated **generically in `w`** so it
composes with whichever choice of `w` the geometric producer (`hR`, still open — see report to
team-lead 2026-09-23) settles on, rather than committing to a specific `w`.

## Status of the rest of the 11-conjunct package (not attempted here — see report)

Reusable landed pieces found already in the main tree, **none yet assembled together**:
* `Nivat.HsuppTowerBase.exists_hbase_nprevOf` (`HsuppTowerGeneral.lean:367`) — `hbase` (and half
  of `h0`) for the *interior* case (`I + 1 < (sortedCand ...).length`), using
  `m := nprevOf d nℓ vl u' i (I + 1)` and `w' := wtower d nℓ vl u' i I` as the *sweep* direction
  from `C := tower (coneRegion B vl u') wtower I` to `Rinf := sweep C w'`.
* `Nivat.ColleReg.hunb_of_sweep_neg` (`TowerUnb.lean:47`) — generic `hunb`, any `Rinf = sweep
  towerPrev wPrev` with `dot m wPrev < 0` and a witness point.
* `Nivat.TowerRoom.hroomT_of_wedge_and_cont` (`TowerRoom.lean:68`) — `hroomT`'s conclusion from
  `hWedge`/`hcont` binders (lane-hroomT's scope, not discharged here).

**Finding, not yet resolved**: the composite's own `w` (the *second cone direction* of
`Colle41.IsRegion Rinf vl w`, per `isRegion_cut`'s `(u, u') := (vl, w)` role — `hmw`/`hmu` there
match this file's `hmw`/`hmvl` exactly) is **not** the same vector as `exists_hbase_nprevOf`'s
sweep direction `w' := wtower ... I`. The only geometric producer for `IsRegion Rinf vl w` found
so far (`tmp/wip/lane-hroom-hR-assembly.lean`'s `hR_final`, itself unlanded / mid-correction as
of "round 67-68") uses `w := wComb d nℓ vl u' i (I + 1)`, generically a *different* tower
direction (`wtower ... (I - 1)` for `I ≥ 1`, or `u'` at `I = 0`) than the sweep direction
`wtower ... I`. Composing `exists_hbase_nprevOf`'s `m := nprevOf ... (I+1)` (chosen to be
strictly negative against the *sweep* direction, for the `hbase` descent argument) with
`hR_final`'s `w := wComb ... (I+1)` requires `dot m w = 0`, i.e.
`dot (nprevOf ... (I+1)) (wComb ... (I+1)) = 0` — this is **not** established anywhere in the
tree, and is not obviously true (`nprevOf ... (I+1)` is defined as `± genPerp' (wtower ... (I+1))`,
i.e. perpendicular to `wtower (I+1)`, not to `wComb (I+1) = wtower (I-1)`). Until this is
checked (or a different pairing of `m`/`w` is chosen), `hR`, `hmw`, `hbase`, `hunb`, `hwneg`,
`htop` cannot be soundly assembled into one package — landing any one of them alone risks a
wrong wiring that only fails at final composition. Flagging this now rather than guessing.

## What this file lands

`exists_hmw_hmvl` — 0 sorry, fully generic in `w` (only needs `det vl w ≠ 0`, which is exactly
the composite's own `hw_det` binder). Safe to reuse regardless of how the `w`/`m` mismatch above
is eventually resolved, since it makes no commitment to a specific `w`.
-/

set_option autoImplicit false

namespace Nivat.LaneTowerPkg

open Nivat Nivat.LE2 Nivat.ColleReg

/-- `expNormal a b`'s `dot` against `b` is `(det a b)^2` — nonneg always, strictly positive
exactly when `det a b ≠ 0`. -/
theorem dot_expNormal_pos {a b : ℤ × ℤ} (hdet : det a b ≠ 0) :
    0 < dot (expNormal a b) b := by
  have hval : dot (expNormal a b) b = det a b * det a b := by
    simp only [expNormal, dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, det]
    ring
  rw [hval]
  rcases lt_or_gt_of_ne hdet with h | h
  · nlinarith
  · nlinarith

/-- **`hmw`/`hmvl` for the composite obtain, generic in `w`.** From `hw_det : det vl w ≠ 0`
alone (the composite's own binder, `RegionSteps.lean:1743`'s `det vl w ≠ 0`), produces an `m`
with `dot m w = 0 ∧ 0 < dot m vl`. -/
theorem exists_hmw_hmvl {vl w : ℤ × ℤ} (hw_det : det vl w ≠ 0) :
    ∃ m : ℤ × ℤ, dot m w = 0 ∧ 0 < dot m vl := by
  refine ⟨expNormal w vl, dot_expNormal_u', ?_⟩
  refine dot_expNormal_pos ?_
  intro h
  apply hw_det
  have heq : det vl w = - det w vl := by simp only [det]; ring
  rw [heq, h]; ring

end Nivat.LaneTowerPkg

#print axioms Nivat.LaneTowerPkg.dot_expNormal_pos
#print axioms Nivat.LaneTowerPkg.exists_hmw_hmvl
