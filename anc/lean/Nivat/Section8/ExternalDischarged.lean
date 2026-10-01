/-
Copyright (c) 2026. Released under Apache 2.0 licence.
-/
import Nivat.External.Colle.Theorem114Final
import Nivat.External.Colle.ColleRegion

/-!
# Discharging the external inputs of §8

`Nivat/Section8/External.lean` used to state the two results §8 borrows from Collé as
`axiom`s (`colle_doublyPeriodic`, `colle_region`) and combine them in
`Nivat.exists_fullyPeriodic_region`, which `Nivat.Section8.FirstHalfPlane` consumed on the way to
`Nivat.nivat_conjecture`.  That file is *upstream* of everything under `Nivat/External/Colle/`,
so a proof of either result could never be substituted where the axiom was stated: the import
would be circular.

This file is where the substitution happens.  It sits below the whole Collé development and
re-proves §8's combining lemma from what is actually proved.  `FirstHalfPlane.lean` imports this
file and calls `exists_fullyPeriodic_region'`; that is what keeps the axioms out of
`nivat_conjecture`'s closure, and it is the only reason this file exists.

## Status

**Closed 2026-09-30.**  The open leaves of `RegionSteps.lean` described below are all proved
(the last, `exists_chainData`, by `Nivat.ColleReg.exists_chainData_closed` in
`Hole1PushShell.lean`); measured that day, `#print axioms Nivat.nivat_conjecture` reports
`[propext, Classical.choice, Quot.sound]` and `bash scripts/sorries.sh` reports `TOTAL: 0`.
The rest of this section is the 2026-09-18 reading, kept as history.

## Status, measured 2026-09-18 (history)

Both axioms are discharged **and deleted from the tree**; `External.lean` declares no `axiom`
any more, and `scripts/check_axioms.lean`'s whitelist is back to the three foundational axioms.

* `colle_doublyPeriodic` → `Nivat.Colle.theorem114`, closure
  `[propext, Classical.choice, Quot.sound]`.  `exists_mem_ONED'` below is the old
  `exists_mem_ONED` with the axiom swapped out (done 2026-09-14).
* `colle_region` → `Nivat.ColleReg.colle_region` (`Nivat/External/Colle/ColleRegion.lean`).
  Substituted on the marked line of `exists_fullyPeriodic_region'` on 2026-09-18, after that
  theorem's conclusion was brought to the axiom's exact statement (FROZEN E1's `rfl`
  substitution check, `tmp/subst_check.lean`, red → green that day).  Its closure is
  `[propext, sorryAx, Classical.choice, Quot.sound]`: the `sorryAx` is the open leaves of
  `RegionSteps.lean`, which are thereby **on the main chain for the first time**.

So the measured closure of `Nivat.nivat_conjecture` is now
`[propext, sorryAx, Classical.choice, Quot.sound]` — no project axiom, one `sorryAx`.  Removing
the axioms *moved* the open work onto the main chain; it did not finish it.  `bash
scripts/sorries.sh` is the authoritative list of what remains, and `python scripts/gate.py` the
authoritative closure; do not take this paragraph for either reading.

`RegionClassification.lean`'s `chainData_yields_region` is **not** on this path —
`ColleRegion.lean`'s `import` lines do not include it.
-/

namespace Nivat

/-- **Theorem 8.6**, with the Collé input discharged: a non-periodic `ξ` has a line `ℓ` with
`±ℓ ∈ ONED(ξ)`.

Identical in statement to `Nivat.exists_mem_ONED`; the only difference is that this version
routes through the *proved* `Nivat.Colle.theorem114` rather than the axiom
`Nivat.colle_doublyPeriodic`. -/
theorem exists_mem_ONED' {ξ : Config ℤ} (hA : (Set.range ξ).Finite) (hann : HasNonzeroAnn ξ)
    (hnp : ¬ IsPeriodic ξ) : ∃ w : ℝ × ℝ, w ≠ 0 ∧ w ∈ ONED ξ ∧ -w ∈ ONED ξ := by
  by_contra hc
  refine hnp (Nivat.Colle.theorem114 hA hann ?_).isPeriodic
  intro w hw hmem
  exact hc ⟨w, hw, hmem.1, hmem.2⟩

/-- **Theorems 8.6 and 8.7 combined**, with Theorem 8.6's input discharged.

Statement-identical to the `exists_fullyPeriodic_region` that `External.lean` carried until
2026-09-18; the proof is the same one, with `exists_mem_ONED` replaced by `exists_mem_ONED'`
and the axiom `colle_region` replaced by the theorem `Nivat.ColleReg.colle_region` on the marked
line.  This is the only place §8 touches the Collé development. -/
theorem exists_fullyPeriodic_region' {ξ : Config ℤ} (hξ : IsMinimalCounterexample ξ) :
    ∃ ξ' ∈ orbitClosure ξ, ¬ IsPeriodic ξ' ∧ ∃ R : Set (ℤ × ℤ),
      IsLatticeConvexRegion R ∧ R.Nonempty ∧ FullyPeriodicOn ξ' R := by
  obtain ⟨hA, hpos, hnp, S, hSne, hSconv, hSP⟩ := hξ.1
  obtain ⟨w, hw, hw₁, hw₂⟩ :=
    exists_mem_ONED' hA (hasNonzeroAnn_of_low_complexity hA hSne hSP) hnp
  obtain ⟨ξ', horb, hξ'np, R, hR, hRne, h, h', z₀, z₀', hdet, hray, hray', hper, hper'⟩ :=
    Nivat.ColleReg.colle_region hξ hw hw₁ hw₂   -- ← substituted 2026-09-18 (was the axiom `colle_region`)
  exact ⟨ξ', horb, hξ'np, R, hR, hRne,
    fullyPeriodicOn_of_overlap_of_nat_ray hR hdet hray hray' hper hper'⟩

end Nivat
