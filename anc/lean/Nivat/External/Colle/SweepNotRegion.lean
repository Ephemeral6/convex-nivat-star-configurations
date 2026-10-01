/-
Copyright (c) 2026 Nivat conjecture contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SweepNotRegion lane
-/
import Nivat.External.Colle.Lemma41
import Nivat.Section8.HalfPlane

/-!
# Forward sweep does not preserve `IsRegion`

**原文对应：OPEN.md #22** — falsification targets for the closure question.

`Nivat.Colle41.IsRegion K u u'` requires `IsLatticeConvexRegion K` (Definition 3.1), which
means `K = C ∩ ℤ²` for a closed convex `C ⊆ ℝ²` (`HalfPlane.lean:174`). Forward sweep
`{g + t•w : g ∈ K, t ∈ ℕ}` can break lattice-convexity in two ways:

1. **Infinite unbounded case**: `K = ℤ × {0}`, `w = (1,2)` — the sweep has no interior points,
   so any closed convex `C` containing the swept points must contain points not in the sweep.

2. **Finite case** (optional): `K = {(0,0), (1,2)}`, `w = (1,0)` — convex hull contains `(1,1)`
   but the sweep does not.

This file establishes (1) in the kernel. Consumer: `OPEN.md #22` resolution (add premise or
define a directed region predicate).

-/

set_option autoImplicit false

namespace Nivat.Colle41

open Nivat

/-- **Target 1: Forward sweep does not preserve `IsRegion`.**

**原文对应**: `OPEN.md #22`, infinite unbounded witness.

**Witness**:
- `K = ℤ × {0}` (the x-axis)
- `u = (1, 0)`, `u' = (-1, 0)` (bidirectional horizontal rays)
- `w = (1, 2)` (sweep direction)

**Why `K` satisfies `IsRegion K u u'`**:
- `IsLatticeConvexRegion K`: Take `C = {p : ℝ × ℝ | p.2 = 0}`, which is closed and convex.
- `RayIn K (0,0) (1,0)`: The ray `{(t,0) : t ∈ ℕ}` lies in `K`.
- `RayIn K (0,0) (-1,0)`: The ray `{(-t,0) : t ∈ ℕ}` lies in `K`.

**Why the sweep breaks `IsLatticeConvexRegion`**:
The swept set is `{(x, 2t) : x ∈ ℤ, t ∈ ℕ}` — all points have even y-coordinate.
Any closed convex set `C` containing `(0,0)` and `(0,2)` must contain their midpoint `(0,1)`
by convexity. But `(0,1)` has odd y-coordinate, so `(0,1) ∉` swept set, contradicting
`swept set = toReal ⁻¹' C`.

-/
theorem not_forall_isRegion_sweep :
    ¬ ∀ (K : Set (ℤ × ℤ)) (u u' w : ℤ × ℤ),
        IsRegion K u u' →
        IsRegion {z | ∃ g ∈ K, ∃ t : ℕ, z = g + (t : ℤ) • w} u u' := by
  intro h
  -- Witness: K = ℤ × {0}, u = (1,0), u' = (-1,0), w = (1,2)
  let K : Set (ℤ × ℤ) := {p | p.2 = 0}
  let u : ℤ × ℤ := (1, 0)
  let u' : ℤ × ℤ := (-1, 0)
  let w : ℤ × ℤ := (1, 2)

  -- K satisfies IsRegion K u u'
  have hK : IsRegion K u u' := by
    constructor
    · -- IsLatticeConvexRegion K
      use {p : ℝ × ℝ | p.2 = 0}
      constructor
      · -- Convex
        intro x hx y hy a b ha hb hab
        simp at hx hy ⊢
        rw [hx, hy]
        ring
      constructor
      · -- IsClosed
        apply isClosed_eq continuous_snd continuous_const
      · -- K = toReal ⁻¹' C
        ext p
        simp [toReal, K]
    constructor
    · -- ∃ z₀, RayIn K z₀ u
      use (0, 0)
      intro t
      simp [K, u]
    · -- ∃ z₀', RayIn K z₀' u'
      use (0, 0)
      intro t
      simp [K, u']

  -- Apply hypothesis to get IsRegion on the swept set
  have hsweep := h K u u' w hK

  -- The swept set
  let S := {z | ∃ g ∈ K, ∃ t : ℕ, z = g + (t : ℤ) • w}

  -- S = {(x, 2t) : x ∈ ℤ, t ∈ ℕ}
  have hS_char : ∀ z : ℤ × ℤ, z ∈ S ↔ ∃ x : ℤ, ∃ t : ℕ, z = (x, (2 * t : ℤ)) := by
    intro z
    constructor
    · rintro ⟨g, hg : g.2 = 0, t, rfl⟩
      use g.1 + t, t
      ext
      · simp [w]
      · simp [w, hg]
        ring
    · rintro ⟨x, t, rfl⟩
      use (x - t, 0)
      refine ⟨?_, t, ?_⟩
      · simp [K]
      · ext
        · simp [w]
        · simp [w]
          ring

  -- Extract IsLatticeConvexRegion from IsRegion
  obtain ⟨⟨C, hCconv, hCclosed, hSeq⟩, _, _⟩ := hsweep

  -- (0,0) ∈ S and (0,2) ∈ S
  have h00 : (0, 0) ∈ S := by
    rw [hS_char]
    use 0, 0
    simp

  have h02 : (0, 2) ∈ S := by
    rw [hS_char]
    use 0, 1
    norm_num

  -- Therefore toReal (0,0) ∈ C and toReal (0,2) ∈ C
  have h00_C : toReal (0, 0) ∈ C := by
    have : (0, 0) ∈ toReal ⁻¹' C := by rw [← hSeq]; exact h00
    exact this

  have h02_C : toReal (0, 2) ∈ C := by
    have : (0, 2) ∈ toReal ⁻¹' C := by rw [← hSeq]; exact h02
    exact this

  -- By convexity, toReal (0,1) ∈ C
  have h01_C : toReal (0, 1) ∈ C := by
    have := hCconv h00_C h02_C (by norm_num : (0:ℝ) ≤ (1/2:ℝ)) (by norm_num : (0:ℝ) ≤ (1/2:ℝ))
      (by norm_num : (1/2:ℝ) + (1/2:ℝ) = 1)
    convert this using 1
    simp [toReal]

  -- Therefore (0,1) ∈ S by hSeq
  have h01_S : (0, 1) ∈ S := by
    have : (0, 1) ∈ toReal ⁻¹' C := h01_C
    rw [← hSeq] at this
    exact this

  -- But (0,1) ∉ S by characterization (odd y-coordinate)
  have h01_not_S : (0, 1) ∉ S := by
    rw [hS_char]
    rintro ⟨x, t, h⟩
    simp at h
    omega

  exact h01_not_S h01_S

#print axioms not_forall_isRegion_sweep

/-- **Target 2: Quadrant sweep with det = -3 breaks lattice-convexity.**

**原文：b3_colle2.txt:806, :31, :386**

This witness targets the literal statement at `:806` "𝓡_i is a region" when
`det(ℓ_{i+1}, ℓ_i) = -3`. The first quadrant `K = {p | 0 ≤ p.1 ∧ 0 ≤ p.2}` is
an `IsRegion K (0,1) (1,0)`, but sweeping it by `w = (2,-3)` (the level-dropping
direction with `det(w, (0,1)) = -3`) produces a set that is not lattice-convex.

**Witness**:
- `K = {p : ℤ × ℤ | 0 ≤ p.1 ∧ 0 ≤ p.2}` (first quadrant)
- `w = (2, -3)` (sweep direction with det = -3)

**Why `K` satisfies `IsRegion K (0,1) (1,0)`**:
- `IsLatticeConvexRegion K`: Take `C = {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2}`, closed and convex.
- `RayIn K (0,0) (0,1)`: The ray `{(0,t) : t ∈ ℕ}` lies in `K`.
- `RayIn K (0,0) (1,0)`: The ray `{(t,0) : t ∈ ℕ}` lies in `K`.

**Why the sweep breaks `IsLatticeConvexRegion`**:
The swept set contains `(0,0)`, `(1,0)`, and `(2,-3)`. Any closed convex set `C`
containing these three points must contain their convex combination
`⅓(0,0) + ⅓(1,0) + ⅓(2,-3) = (1,-1)` (computed via two binary convex combinations:
`½(0,0) + ½(2,-3) = (1,-3/2)`, then `⅔(1,-3/2) + ⅓(1,0) = (1,-1)`). But `(1,-1)`
is not in the swept set: if `(1,-1) = g + t•(2,-3)` with `g ∈ K` and `t ∈ ℕ`, then
- `t = 0` ⇒ `g = (1,-1)`, but `g.2 = -1 < 0` contradicts `g ∈ K`.
- `t ≥ 1` ⇒ `g.1 = 1 - 2t ≤ -1 < 0`, contradicting `g ∈ K`.

-/
theorem not_isLatticeConvexRegion_sweep_quadrant :
    ¬ IsLatticeConvexRegion {z : ℤ × ℤ | ∃ g ∈ ({p : ℤ × ℤ | 0 ≤ p.1 ∧ 0 ≤ p.2} : Set (ℤ × ℤ)),
        ∃ t : ℕ, z = g + (t : ℤ) • ((2 : ℤ), (-3 : ℤ))} := by
  intro ⟨C, hCconv, hCclosed, hSeq⟩

  let K : Set (ℤ × ℤ) := {p | 0 ≤ p.1 ∧ 0 ≤ p.2}
  let w : ℤ × ℤ := (2, -3)
  let S := {z : ℤ × ℤ | ∃ g ∈ K, ∃ t : ℕ, z = g + (t : ℤ) • w}

  -- (0,0), (1,0), (2,-3) ∈ S
  have h00 : (0, 0) ∈ S := by
    use (0, 0)
    simp [K]
    use 0
    simp

  have h10 : (1, 0) ∈ S := by
    use (1, 0)
    simp [K]
    use 0
    simp

  have h2m3 : (2, -3) ∈ S := by
    use (0, 0)
    simp [K]
    use 1
    simp [w]

  -- Therefore toReal of these points are in C
  have h00_C : toReal (0, 0) ∈ C := by
    have : (0, 0) ∈ toReal ⁻¹' C := by rw [← hSeq]; exact h00
    exact this

  have h10_C : toReal (1, 0) ∈ C := by
    have : (1, 0) ∈ toReal ⁻¹' C := by rw [← hSeq]; exact h10
    exact this

  have h2m3_C : toReal (2, -3) ∈ C := by
    have : (2, -3) ∈ toReal ⁻¹' C := by rw [← hSeq]; exact h2m3
    exact this

  -- Compute ½(0,0) + ½(2,-3) = (1, -3/2)
  have h1m32_C : ((1:ℝ), (-3/2:ℝ)) ∈ C := by
    have := hCconv h00_C h2m3_C (by norm_num : (0:ℝ) ≤ (1/2:ℝ)) (by norm_num : (0:ℝ) ≤ (1/2:ℝ))
      (by norm_num : (1/2:ℝ) + (1/2:ℝ) = 1)
    convert this using 1
    simp [toReal]
    norm_num

  -- Compute ⅔(1,-3/2) + ⅓(1,0) = (1,-1)
  have h1m1_C : ((1:ℝ), (-1:ℝ)) ∈ C := by
    have := hCconv h1m32_C h10_C (by norm_num : (0:ℝ) ≤ (2/3:ℝ)) (by norm_num : (0:ℝ) ≤ (1/3:ℝ))
      (by norm_num : (2/3:ℝ) + (1/3:ℝ) = 1)
    convert this using 1
    simp [toReal]
    norm_num

  -- Therefore (1,-1) ∈ S by hSeq
  have h1m1_S : (1, -1) ∈ S := by
    have : (1, -1) ∈ toReal ⁻¹' C := by
      simp [toReal]
      exact h1m1_C
    rw [← hSeq] at this
    exact this

  -- But (1,-1) ∉ S
  have h1m1_not_S : (1, -1) ∉ S := by
    intro ⟨g, ⟨hg1, hg2⟩, t, heq⟩
    -- From heq: g + t•(2,-3) = (1,-1)
    have heq1 : g.1 + (t : ℤ) * 2 = 1 := by
      have this := congr_arg Prod.fst heq
      simp [w] at this
      exact this.symm
    have heq2 : g.2 + (t : ℤ) * (-3) = -1 := by
      have this := congr_arg Prod.snd heq
      simp [w] at this
      exact this.symm
    -- If t = 0, then g.2 = -1 < 0, contradicting hg2
    -- If t ≥ 1, then g.1 = 1 - 2*t ≤ -1 < 0, contradicting hg1
    omega

  exact h1m1_not_S h1m1_S

#print axioms not_isLatticeConvexRegion_sweep_quadrant

end Nivat.Colle41
