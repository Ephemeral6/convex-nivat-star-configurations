/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.RegionSweep

/-!
# `sweep_closure_add` — a set built by `sweep C w` is closed under further `ℕ•w` steps

Lane `lane-hroom-close`, 2026-09-22.

Consumer: `Nivat.TowerRoom.hroomT_of_wedge_and_cont` (`TowerRoom.lean:68-85`) needs two
structurally identical closure facts as binders:

* `hTowerW_gen : ∀ z ∈ towerI, ∀ n : ℕ, z + (n : ℤ) • w ∈ towerI`
* `hRinf_sweep_gen : ∀ z ∈ towerI, ∀ k : ℕ, z + (k : ℤ) • wtowerI ∈ Rinf`

Both instantiate this single lemma once `towerI`/`Rinf` are exhibited as one further `sweep`
step: `towerI = Nivat.RegionSweep.sweep C w` for some earlier stage `C`, and similarly for
`Rinf = Nivat.RegionSweep.sweep towerI wtowerI`. This is immediate from `sweep`'s definition
(`RegionSweep.lean:76-77`, `sweep C w = {z | ∃ g ∈ C, ∃ t : ℕ, z = g + t•w}`): a point already
reached after `t` steps reaches `t + n` steps for free, no hypothesis on `C`/`w` needed at all.

## Status

`sweep_closure_add`: 0 sorry.
-/

set_option autoImplicit false

namespace Nivat.RegionSweep

/-- **`sweep C w` is closed under adding further `ℕ`-multiples of `w`.**

No hypothesis on `C` or `w` is needed — this is immediate unfolding of `sweep`'s definition:
a point `z = g + t • w` (`g ∈ C`) reaches `z + n • w = g + (t + n) • w`, still in `sweep C w`. -/
theorem sweep_closure_add {C : Set (ℤ × ℤ)} (w : ℤ × ℤ) :
    ∀ z ∈ sweep C w, ∀ n : ℕ, z + (n : ℤ) • w ∈ sweep C w := by
  rintro z ⟨g, hg, t, rfl⟩ n
  refine ⟨g, hg, t + n, ?_⟩
  push_cast
  module

end Nivat.RegionSweep

#print axioms Nivat.RegionSweep.sweep_closure_add
