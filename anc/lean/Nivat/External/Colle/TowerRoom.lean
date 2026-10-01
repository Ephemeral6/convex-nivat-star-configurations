/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.TowerConstruct
import Nivat.External.Colle.TowerPackage
import Nivat.External.Colle.LatticeEdges

/-!
# `hroomT` — the tower's "room" fact for `hcover`

Lane `lane-place`, dispatched by team-lead 2026-09-22.

Consumer: `RegionSteps.lean:1748-1755`, the last conjunct of the tower `obtain` in
`exists_cutResidualR_of_claim46` — verbatim:

```
∀ a ∈ d.toDecompData.Sphi,
  (∀ b ∈ d.toDecompData.Sphi, dot m a ≤ dot m b) →
  (∀ b ∈ d.toDecompData.Sphi, dot m b = dot m a → ∃ t : ℕ, b = a + (t:ℤ) • w) →
  ∀ p ∈ Rinf, dot m p < b₀ →
    ∀ b ∈ d.toDecompData.Sphi, 0 < dot m (b - a) → p + (b - a) ∈ Rinf
```

## Mechanism (team-lead 2026-09-22, revision 2 — supersedes the earlier `hcone`/`τ ≤ L_B`
real-coefficient argument, which foundered on a false bound `τ ≤ gcd(h_j)` — lane-hsupp gave a
kernel-witnessed counterexample on the hexagon example, since the zonotope's extent in the
`wtower I` direction is the *sum* of all generators' components there, not one generator's gcd)

Write `V` for the tower corner at the breaking level `I`, `towerI := tower R₀ wtower I`,
`B` for Definition 3.2's zonotope at level `I` (a vertex of which is `V`, the "`w`-face" corner
corresponding to `Sphi`'s own `w`-face corner `a`). The gap region `G := Rinf ∩ {dot m < b₀}` is
exactly the lattice points of `V + ℕ•w + ℕ₊•wtower I` (`hWedge` below, taken as a binder, derived
by lane-tower from `hlow`/`hprev`/orthogonality).

The only substantive input is `hcont : ∀ b ∈ Sphi, V + (b - a) ∈ B` — Definition 3.2's "`B`
contains a translate of `Sphi` with corresponding vertices `a ↔ V`" (lane-hsupp's, via the
`HsuppAssemble` chain-sum at the vertex pair `(a, V)`).

For `x = V + s•w + t•wtower I ∈ G` (`s, t : ℕ`) and `b ∈ Sphi`:
`x + (b - a) = (V + (b - a)) + s•w + t•wtower I`. Since `V + (b - a) ∈ B ⊆ towerI` (`hcont` +
`hB_sub`), closure of `towerI` under `+ ℕ•w` (`hTowerW_gen`) puts `(V + (b-a)) + s•w ∈ towerI`,
and then the sweep defining `Rinf` from `towerI` via `+ ℕ•wtower I` (`hRinf_sweep_gen`, the
generalisation of the old `V`-specific ray fact to an arbitrary base point of `towerI`) finishes
it. **Pure integer/group closure — no real coefficients, no convexity machinery, no bound on any
`τ` is needed at all**; this is considerably simpler than the superseded mechanism, and drops the
`RegionTranslate`/`HsuppRoomCone`/`ConeRegion`/`Lemma41`/`AEnv`/`CutRecConvex` imports entirely.

## Status

`hroomT_of_wedge_and_cont`: 0 sorry, proves `hroomT`'s conclusion from `hWedge` + `hcont` +
tower-closure facts (`hB_sub`, `hTowerW_gen`, `hRinf_sweep_gen` — all lane-tower's / lane-hsupp's,
taken as binders per the parallel-lane protocol).
-/

set_option autoImplicit false

namespace Nivat.TowerRoom

open Nivat.LE2

variable {towerI Rinf B : Set (ℤ × ℤ)} {w wtowerI m V : ℤ × ℤ} {b₀ : ℤ}
  {Sphi : Finset (ℤ × ℤ)} {a : ℤ × ℤ}

/-- **Main theorem.** `hroomT`'s conclusion, given the tower's wedge/closure structure as
binders (lane-tower's, from the `hbase` induction) and the anchored zonotope-containment fact
`hcont` (lane-hsupp's, `HsuppAssemble`'s chain-sum at the vertex pair `(a, V)`). Pure integer
closure — no real-coefficient/convexity reasoning needed. -/
theorem hroomT_of_wedge_and_cont
    (hB_sub : B ⊆ towerI)
    (hTowerW_gen : ∀ z ∈ towerI, ∀ n : ℕ, z + (n : ℤ) • w ∈ towerI)
    (hRinf_sweep_gen : ∀ z ∈ towerI, ∀ k : ℕ, z + (k : ℤ) • wtowerI ∈ Rinf)
    (hWedge : ∀ x ∈ Rinf, dot m x < b₀ →
      ∃ s t : ℕ, 0 < t ∧ x = V + (s : ℤ) • w + (t : ℤ) • wtowerI)
    (hcont : ∀ b ∈ Sphi, V + (b - a) ∈ B) :
    ∀ x ∈ Rinf, dot m x < b₀ →
      ∀ b ∈ Sphi, 0 < dot m (b - a) → x + (b - a) ∈ Rinf := by
  intro x hx hxlt b hb _hbpos
  obtain ⟨s, t, _htpos, hxeq⟩ := hWedge x hx hxlt
  have hVba : V + (b - a) ∈ towerI := hB_sub (hcont b hb)
  have hstep : V + (b - a) + (s : ℤ) • w ∈ towerI := hTowerW_gen _ hVba s
  have hfinal : V + (b - a) + (s : ℤ) • w + (t : ℤ) • wtowerI ∈ Rinf :=
    hRinf_sweep_gen _ hstep t
  have heq : x + (b - a) = V + (b - a) + (s : ℤ) • w + (t : ℤ) • wtowerI := by
    rw [hxeq]; abel
  rw [heq]; exact hfinal

end Nivat.TowerRoom
