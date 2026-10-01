/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.LatticeEdges

/-!
# `lane-substrip-tight-env`: `envB` gives no transverse bound — kernel witness

Retasked by `team-lead` (2026-09-23, following `ShellBaseReduce.lean`'s `hbase` reduction and
`base_shell_false_of_singleton`'s road-sign that the missing ingredient lives in `B`'s own
structure — `ItemII` / `Exhausts` / `envB`). Assignment: does
`envB : ∀ i, Env (B i)` (`Env = EnvOf ↑S`, `LatticeEdges.lean:2433`, fixed window `S`) supply a
usable transverse bound for `hbase`? **Answer: no — kernel witness below (deliverable (b)).**

## Numerical instance first (硬规矩 6)

`S := sq1 = box (0,0) (1,1)` (`LatticeEdges.lean:2159`, the unit square, four edges, `E sq1 =
{(1,0),(-1,0),(0,1),(0,-1)}`, `LatticeEdges.lean:2004`). Take `B := box (0,0) (1,5)`: a `1×5`
lattice rectangle. `E_box` (`LatticeEdges.lean:1963`, needs `p.1<q.1 ∧ p.2<q.2`, here `0<1` and
`0<5`) gives `E B = {(1,0),(-1,0),(0,1),(0,-1)} = E sq1`, so `(E B).encard = (E sq1).encard = 4`
— the `Enveloped` edge-count clause holds *on the nose*, not just `≤`. Each face of `B`:
`face B (1,0)` (right edge, `x=1`) has 6 points (`y ∈ [0,5]`), `≥ 2 = |face sq1 (1,0)|`;
`face B (0,1)` (top edge, `y=5`) has 2 points (`x ∈ [0,1]`), `≥ 2 = |face sq1 (0,1)|`. Both
inequalities `(face sq1 n).encard ≤ (face B n).encard` (`WeaklyEnveloped`,
`LatticeEdges.lean:624`) hold, so `Enveloped sq1 B` holds — checked by hand before proving the
general statement below (`envOf_sq1_box`, already in the main tree,
`LatticeEdges.lean:2492-2503`, is exactly this computation generalised to arbitrary corners).

Meanwhile `B`'s `(0,1)`-extent (5) already exceeds its `(1,0)`-extent (1) by a factor that is
*not* forced by `S = sq1`'s own `1×1` shape — replacing `5` by any `N` keeps `Enveloped sq1 B`
true (§1 below). **`Enveloped`/`EnvOf` places no upper bound on how far a `nJ`-enveloped set
extends in any single direction; it is a shape/lower-bound condition, not a size condition.**

## Why, structurally (from the definitions themselves)

`Enveloped U T := WeaklyEnveloped U T ∧ (E T).encard = (E U).encard`
(`LatticeEdges.lean:628-629`), and
`WeaklyEnveloped U T := IsLatticeConvexRegion T ∧ ∀ n ∈ E T, n ∈ E U ∧
  (face U n).encard ≤ (face T n).encard` (`:624-625`). Every clause is one of:
* a **shape** condition (`IsLatticeConvexRegion T`, convex + closed + lattice-cut, no size
  bound — `Section8/HalfPlane.lean:174-175`, quoted in `AEnv.lean:83`);
* an **edge-direction** condition (`E T = E U` as sets, forced by `⊆` + equal `encard` when `E U`
  is finite, `Enveloped.E_eq`, `LatticeEdges.lean:1657`) — which directions occur, not how far;
* a **lower** bound on face size (`(face U n).encard ≤ (face T n).encard`) — exactly the
  direction `AhatHeight.lean`'s module docstring (lines ~29-31) already flags: *"`Enveloped U T`
  … bounds each face's `encard` from below only … an enveloped set may be arbitrarily long in
  any of its edge directions."* §1 below is the promised kernel witness of that claim, generalised
  from a single numeric instance to unboundedly many.

So `envB` alone (i.e. `Enveloped ↑S (B i)` for the fixed generating window `S`) cannot be the
source of any bound of the shape `hbase` needs (`dot n' b - dot n' b'` controlled by a quantity
depending only on `S`) — **deliverable (b)**: no usable bound exists, kernel-witnessed.

## Where the real bound comes from instead

The actual chain construction (`Nivat.AenvfixProbe`, `ItemIIRec.lean`) does *not* get its
transverse control from `envB` in isolation. `stepB_growth` (`ItemIIRec.lean:144-151`) supplies
a dilation parameter `K` with `∀ f ∈ boxHP nℓ cz i, ∀ m ∈ E ↑S, dot m f - dot m b ≤ K` for a
fixed `b`, and that `K` comes from `AbsorbHyp`'s own growth clause (`ItemIIRec.lean:33-38`,
`Ctx.habs`) — a strictly *stronger* hypothesis than `EnvOf`, bundled in separately at the
absorption step, not implied by `Enveloped` alone (§1 shows it cannot be). So the missing
ingredient `base_shell_false_of_singleton` points at is not recoverable from `envB`'s bare type;
whichever lane closes `hbase` needs `stepB_growth`'s `K` (or an equivalent explicit growth
bound), not just `∀ i, EnvOf ↑S (B i)`.

## §1: the kernel witness
-/

set_option autoImplicit false

namespace Nivat.LaneSubstripTightEnv

open Nivat Nivat.LE2

/-- **Numeric instance check, `N = 5`** (spelled out by hand above): `Enveloped sq1 (box (0,0)
(1,5))` holds, and this box's `(0,1)`-extent (`5`) already exceeds `sq1`'s own extent (`1`) in
that direction, with `(1,0)`-extent pinned at `1` throughout. Immediate from `envOf_sq1_box`. -/
example : EnvOf sq1 (box ((0 : ℤ), (0 : ℤ)) ((1 : ℤ), (5 : ℤ))) :=
  envOf_sq1_box (by norm_num) (by norm_num)

/-- **`envB` gives no transverse bound: kernel witness, unboundedly many instances.**
For every `N : ℕ` there is a set `B` that is `E(sq1)`-enveloped (`sq1` = the fixed unit-square
generating window) in which two points of `B` differ by at least `N` in the `(0,1)`-direction,
while every pair of points of `B` differs by at most `1` in the `(1,0)`-direction. So no
function of `sq1` alone bounds the `(0,1)`-spread of an `E(sq1)`-enveloped set: `envB`'s type
carries no such bound, for any fixed window. -/
theorem no_transverse_bound_from_envOf (N : ℕ) :
    ∃ B : Set (ℤ × ℤ), EnvOf sq1 B ∧
      (∃ b ∈ B, ∃ b' ∈ B, (N : ℤ) ≤ dot ((0 : ℤ), (1 : ℤ)) b - dot ((0 : ℤ), (1 : ℤ)) b') ∧
      (∀ c ∈ B, ∀ c' ∈ B,
        |dot ((1 : ℤ), (0 : ℤ)) c - dot ((1 : ℤ), (0 : ℤ)) c'| ≤ 1) := by
  refine ⟨box ((0 : ℤ), (0 : ℤ)) ((1 : ℤ), (N : ℤ) + 1), ?_, ?_, ?_⟩
  · exact envOf_sq1_box (by norm_num) (by omega)
  · refine ⟨((0 : ℤ), (N : ℤ) + 1), ?_, ((0 : ℤ), (0 : ℤ)), ?_, ?_⟩
    · exact mem_box.mpr ⟨le_refl _, by norm_num, by omega, le_refl _⟩
    · exact mem_box.mpr ⟨le_refl _, by norm_num, le_refl _, by omega⟩
    · simp only [dot_e2]; omega
  · intro c hc c' hc'
    obtain ⟨hc1, hc2, -, -⟩ := mem_box.mp hc
    obtain ⟨hc1', hc2', -, -⟩ := mem_box.mp hc'
    simp only [dot_e1]
    exact abs_le.mpr ⟨by omega, by omega⟩

end Nivat.LaneSubstripTightEnv

#print axioms Nivat.LaneSubstripTightEnv.no_transverse_bound_from_envOf

#print axioms Nivat.LaneSubstripTightEnv.no_transverse_bound_from_envOf
