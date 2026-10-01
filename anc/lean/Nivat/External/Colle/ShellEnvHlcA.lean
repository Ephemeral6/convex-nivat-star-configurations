/-
Copyright (c) 2026. Released under Apache 2.0 license.
Authors: lane-shellenv
-/
import Nivat.External.Colle.SweepOppEdge
import Nivat.External.Colle.AhatMono

/-!
# `shellEnv`'s `hlcT`, first factor: `IsLatticeConvexRegion (reachSet Â_i wJ)` at the call site

Lane `lane-shellenv`, 2026-09-23.  `tmp/wip/`, 0 sorry.

`ShellSubStrip.lean` §25/§27 splits `shellEnv`'s `IsLatticeConvexRegion (Tset i)` obligation
(`Tset i := ShellMink.shellInter Â_i (MaxEnv.shell Â_∞ vJ1 nJ cJ ε) w`) into two sweep-convexity
facts via `LaneCdHlc.isLatticeConvexRegion_shellInter` (`ShellSubStrip.lean:3468`):

1. `IsLatticeConvexRegion (reachSet Â_i w)`;
2. `IsLatticeConvexRegion (reachSet Â_∞ vJ1)`.

Team-lead's message (2026-09-23) identifies (1) as **discharged at the real call site** by
`Nivat.LaneCdOppEdge.isLatticeConvexRegion_reachSet_dir_of_mem_E` (`SweepOppEdge.lean:146`,
main tree, 0 sorry) applied at `w := dir (-νJ1) = -(dir νJ1)` (`LaneCdOppEdge.dir_neg`,
`SweepOppEdge.lean:169`), with `νJ1 ∈ E ↑d.Sphi` from the fan-adjacency data at the
`LeafAAssemble` call site and `-νJ1 ∈ E ↑d.Sphi` free from `Nivat.Colle35.Sphi_negSymm`
(`DecompData.lean:417`, zonotope `±`-symmetry).

This file lands that composition as a standalone theorem against a general `(U, B, νJ1)` triple
— no `DecompData`/`DecompDataZ` import, so it stays upstream and stateable at whichever level
the integrator wants to instantiate `U := ↑d.Sphi`, `B := hatOf A kk vl i`.  Every hypothesis is
either a binder `ofPartsExhaustsInter` already carries (`hAhatFin i` ↦ `hfin i`, `hlcAhat i`
from `LaneCdFaceFree`/upstream lattice-convexity of `Â_i`, `henvAhat i` from `Enveloped ↑S Âi`)
or is free on the chain (`hSarea` ↦ `AhatMono.posArea_Sphi`, `h_νJ1` ↦ `Sphi_negSymm`).

No `sorry`.  Does **not** import `RegionSteps` / `ColleRegion` / `Case2WindowProbe` /
`NfpLPreamble`.
-/

set_option autoImplicit false

namespace Nivat.LaneShellEnv

open Nivat Nivat.LE2 Nivat.MaxEnv Nivat.LaneCdOppEdge

/-- **`hlcT`'s first factor, at the real call site's `w := dir (-νJ1)`.**

`U` plays `↑d.Sphi`, `B` plays `hatOf A kk vl i`, `νJ1` is the edge normal whose antipode
supplies the sweep direction (`wJ = -dir νJ1 = dir (-νJ1)`, `LaneCdOppEdge.dir_neg`).  `harea`
is derived rather than assumed, via `AhatMono.posArea_of_enveloped`, so the caller only has to
supply `PosArea U` (free on the chain from `AhatMono.posArea_Sphi`), not `PosArea B` directly. -/
theorem isLatticeConvexRegion_reachSet_hatOf_of_mem_E
    {U B : Set (ℤ × ℤ)} {νJ1 : ℤ × ℤ}
    (hUfin : U.Finite) (hUarea : PosArea U)
    (hBfin : B.Finite) (hBne : B.Nonempty)
    (hlcB : IsLatticeConvexRegion B)
    (henvB : Enveloped U B)
    (hνJ1 : νJ1 ∈ E U) (h_νJ1 : -νJ1 ∈ E U) :
    IsLatticeConvexRegion (reachSet B (dir (-νJ1))) := by
  have hUE : (E U).Finite := finite_E_of_finite hUfin
  have hBarea : PosArea B := AhatMono.posArea_of_enveloped hUfin hUarea henvB
  have hnU : (-νJ1) ∈ E U := h_νJ1
  have h_nU : -(-νJ1) ∈ E U := by simpa using hνJ1
  exact isLatticeConvexRegion_reachSet_dir_of_mem_E hUE hBfin hBne hBarea hlcB henvB hnU h_nU

end Nivat.LaneShellEnv

#print axioms Nivat.LaneShellEnv.isLatticeConvexRegion_reachSet_hatOf_of_mem_E
