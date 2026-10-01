/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.RegionSweep

/-!
# `hunb` — the tower's unbounded-below-in-`m` ray

Lane `lane-tower3`, dispatched by team-lead for `RegionSteps.lean:1741-1757`'s tower `obtain`.

## Role

Consumer: `exists_cutResidualR_of_claim46`'s `obtain`, the `hunb` conjunct
`∀ b : ℤ, ∃ z ∈ Rinf, dot m z < b`.

Mechanism (matches `TowerPackage.lean`'s `dot_m_next_neg` docstring, "This lets `hunb` be
discharged identically in both sign branches"): whatever the eventual `Rinf` turns out to be
(the specific tower-level indexing is still being finalised by the `hR`/`hroomT` assembly),
`Rinf` is always defined as `sweep towerPrev wPrev` for the immediately preceding tower stage
`towerPrev` and its own sweep direction `wPrev` (the "previous" tower edge, `wtower (I-1)` or
`u'` at `I = 0`). `dot_m_next_neg` (already landed, `TowerPackage.lean:361`) gives
`dot m wPrev < 0` from the `hside` orientation fact. Given any single witness point
`g ∈ towerPrev` (nonempty, since `towerPrev` always contains the finite seed `B`), the ray
`g + t • wPrev ∈ Rinf` (`t : ℕ`) has `dot m` decreasing without bound in `t`, giving `hunb`
directly — pure integer arithmetic, no further geometric content, independent of exactly how
`Rinf`/`wPrev` end up indexed by the final assembly.

Kept generic (no dependence on `TowerBuild.lean`'s `tower` recursion or any specific `wComb`/
`sortedCand` indexing) so it can be instantiated by whichever assembly file ends up fixing the
concrete `Rinf`/`wPrev`/`g` — avoids colliding with `lane-hroom-close`'s in-flight `hR`
indexing work.

## Status

`hunb_of_sweep_neg`: 0 sorry.
-/

set_option autoImplicit false

namespace Nivat.ColleReg

open Nivat Nivat.LE2 Nivat.RegionSweep

/-- **`hunb`, generic form.** `Rinf := sweep towerPrev wPrev`, `dot m wPrev < 0`, and any
witness `g ∈ towerPrev` together give: for every integer bound `b`, some point of `Rinf` has
`dot m` strictly below `b`. -/
theorem hunb_of_sweep_neg {towerPrev : Set (ℤ × ℤ)} {wPrev m g : ℤ × ℤ}
    (hg : g ∈ towerPrev) (hneg : dot m wPrev < 0) (b : ℤ) :
    ∃ z ∈ sweep towerPrev wPrev, dot m z < b := by
  -- `dot m (g + t • wPrev) = dot m g + t * dot m wPrev`, and `dot m wPrev ≤ -1`,
  -- so it suffices to take `t` large enough that `t * dot m wPrev < b - dot m g`.
  set δ : ℤ := -dot m wPrev with hδ_def
  have hδpos : 0 < δ := by simp only [hδ_def]; linarith
  -- choose `t : ℕ` with `(t : ℤ) * δ > dot m g - b`, e.g. `t = (dot m g - b).toNat + 1`.
  set t : ℕ := (dot m g - b).toNat + 1 with ht_def
  have htcast : (dot m g - b) < (t : ℤ) := by
    have h1 : (dot m g - b) ≤ ((dot m g - b).toNat : ℤ) := Int.self_le_toNat _
    have h2 : ((dot m g - b).toNat : ℤ) < (t : ℤ) := by
      simp only [ht_def]; push_cast; linarith
    linarith
  have htδ : (dot m g - b) < (t : ℤ) * δ := by
    have hδge1 : (1 : ℤ) ≤ δ := hδpos
    calc (dot m g - b) < (t : ℤ) := htcast
      _ ≤ (t : ℤ) * δ := by nlinarith [Nat.cast_nonneg (α := ℤ) t]
  refine ⟨g + (t : ℤ) • wPrev, add_nsmul_mem_sweep hg t, ?_⟩
  have heq : dot m (g + (t : ℤ) • wPrev) = dot m g + (t : ℤ) * dot m wPrev := by
    rw [dot_add]
    congr 1
    cases m; cases wPrev
    simp only [dot, Prod.smul_mk, smul_eq_mul]
    ring
  rw [heq]
  have : (t : ℤ) * dot m wPrev = - ((t : ℤ) * δ) := by rw [hδ_def]; ring
  linarith [htδ]

end Nivat.ColleReg

#print axioms Nivat.ColleReg.hunb_of_sweep_neg
