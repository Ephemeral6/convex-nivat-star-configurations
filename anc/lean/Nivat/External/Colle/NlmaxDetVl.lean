/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.TowerHbaseUnitSweep

set_option autoImplicit false

/-!
# `|dot nJ vl| = 1` is the same equivalence as `unit_sweep_iff_unimodular`, at `vl`

Dispatched by the integrator (round 233, after `GcdCollapse.collapse` folded
`gcd(d, e) = 1` back onto `dot nJ vJ1 = -1`): the real open target is

> **`|dot nJ vl| = 1`**  (equivalently `det vJ vl = ±1`, i.e. `{vJ, vl}` is a basis of `ℤ²`).

`Nivat.TowerHbase.dot_dvd_det` / `det_dvd_dot` (`TowerHbaseUnitSweep.lean:117,127`) are already
stated for an *arbitrary* third vector (named `vJ1` there, but the proof never uses anything
about `vJ1` beyond being a vector) — so the "step size is the determinant" identity applies
verbatim with `vl` substituted for `vJ1`.  This file just instantiates that and records the
`±1` equivalence integrator asked to nail first, as the cheapest step. **No new hypothesis is
introduced past what `TowerHbaseUnitSweep.lean` already uses**:

* `hnJ_prim : Primitive nJ` — field `nJ_prim` (`ChainGeom.lean`, mirrors `ChainPartsFeed.lean:286`).
* `hvJ_prim : Primitive vJ` — field `vJ_prim` (`ChainGeom.lean`, mirrors `ChainPartsFeed.lean:285`).
* `hperp : dot nJ vJ = 0` — `dot_nJ_vJ` (`ChainGeom.lean`), from `FaceBlock` (`ANormal.lean:616`).

⚠ **What this file does NOT do**: it does not produce `det vJ vl = ±1` (equivalently
`dot nJ vl = ±1`) from `exists_chainData`'s binder.  That is the actual remaining debt — it
needs tracing `nJ`'s origin as the `J`-face normal and showing `{vJ, vl}` is a lattice basis,
which this file's search did not find a producer for (see the module-end note).  Landing this
equivalence only fixes the *target shape*; it does not discharge it.
-/

namespace Nivat.NlmaxDetVl

open Nivat Nivat.LE2 Nivat.TowerHbase

/-- `dot nJ vl` divides `det vJ vl`.  `dot_dvd_det` specialised at `vl`. -/
theorem dot_nJ_vl_dvd_det {nJ vJ vl : ℤ × ℤ} (hnJ_prim : Primitive nJ)
    (hperp : dot nJ vJ = 0) : dot nJ vl ∣ det vJ vl :=
  dot_dvd_det hnJ_prim hperp vl

/-- `det vJ vl` divides `dot nJ vl`.  `det_dvd_dot` specialised at `vl`. -/
theorem det_vJ_vl_dvd_dot {nJ vJ vl : ℤ × ℤ} (hvJ_prim : Primitive vJ)
    (hperp : dot nJ vJ = 0) : det vJ vl ∣ dot nJ vl :=
  det_dvd_dot hvJ_prim hperp

/-- **The equivalence the integrator asked to nail first**: under the chain's own primitivity
and perpendicularity fields, `|dot nJ vl| = 1` and `|det vJ vl| = 1` (`{vJ, vl}` a basis of
`ℤ²`) are the *same* statement.  Verbatim analogue of `unit_sweep_iff_unimodular`, at `vl`
instead of `vJ1` — no new argument, just re-pointing the existing one. -/
theorem unit_vl_iff_unimodular {nJ vJ vl : ℤ × ℤ}
    (hnJ_prim : Primitive nJ) (hvJ_prim : Primitive vJ) (hperp : dot nJ vJ = 0) :
    (dot nJ vl = 1 ∨ dot nJ vl = -1) ↔ (det vJ vl = 1 ∨ det vJ vl = -1) := by
  constructor
  · intro h
    have hdvd : det vJ vl ∣ dot nJ vl := det_vJ_vl_dvd_dot hvJ_prim hperp
    rcases h with h | h
    · rw [h] at hdvd; exact Int.isUnit_iff.mp (isUnit_of_dvd_one hdvd)
    · rw [h] at hdvd
      exact Int.isUnit_iff.mp (isUnit_of_dvd_one ((dvd_neg).mp hdvd))
  · intro h
    have hdvd : dot nJ vl ∣ det vJ vl := dot_nJ_vl_dvd_det hnJ_prim hperp
    rcases h with h | h
    · rw [h] at hdvd; exact Int.isUnit_iff.mp (isUnit_of_dvd_one hdvd)
    · rw [h] at hdvd
      exact Int.isUnit_iff.mp (isUnit_of_dvd_one ((dvd_neg).mp hdvd))

end Nivat.NlmaxDetVl

/-! ## 公理审计（分母＝本文件声明数 3） -/

#print axioms Nivat.NlmaxDetVl.dot_nJ_vl_dvd_det
#print axioms Nivat.NlmaxDetVl.det_vJ_vl_dvd_dot
#print axioms Nivat.NlmaxDetVl.unit_vl_iff_unimodular
