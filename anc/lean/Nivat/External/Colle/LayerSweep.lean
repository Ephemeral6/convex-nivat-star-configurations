/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.L1RegionBuild
import Nivat.External.Colle.Lemma41

/-!
# Layer-by-layer periodicity: forward vs bidirectional sweep

原文：b3_colle2.txt:414, 784

This file investigates whether periodicity on the forward-only half-strip `halfStrip B vl`
(the paper's `H_B(ℓ) = {g + t·v⃗_ℓ : g ∈ B, t ∈ ℤ₊}`) implies periodicity on the
bidirectional `fullSweep B vl` (our `B + ℤ·vl`).

**Why this matters**: `RegionSteps.lean:1539` needs `PeriodOn` on `chainFull`, whose inner
construction uses `fullSweep` (bidirectional). But the paper's constructions at :414 and :784
use only forward sweeps (`ℤ₊`). The question is whether the bidirectional sweep is an
over-strengthening that breaks the periodicity argument.

## Main results

1. `not_periodOn_fullSweep_of_forward_only`: A counterexample showing that periodicity on
   `halfStrip B vl` does NOT imply periodicity on `fullSweep B vl`.

2. (If needed) Forward-only version of the layer lemma for the actual proof.

-/

set_option autoImplicit false

namespace Nivat.ColleReg

open Nivat Nivat.LE2 Nivat.Colle41

/-- **Forward-only half-strip**: `{b + t·vl : b ∈ B, t ∈ ℕ}`.

原文：b3_colle2.txt:414 — `H_B(ℓ) := {g + s·v⃗_ℓ : g ∈ B, s ∈ ℤ₊}`

This is what the paper actually uses. It's the same as `Nivat.RegionSweep.sweep B vl`. -/
def halfStrip (B : Set (ℤ × ℤ)) (vl : ℤ × ℤ) : Set (ℤ × ℤ) :=
  {z | ∃ b ∈ B, ∃ t : ℕ, z = b + (t : ℤ) • vl}

theorem mem_halfStrip_iff {B : Set (ℤ × ℤ)} {vl z : ℤ × ℤ} :
    z ∈ halfStrip B vl ↔ ∃ b ∈ B, ∃ t : ℕ, z = b + (t : ℤ) • vl := Iff.rfl

/-- **Counterexample**: Periodicity on `halfStrip` does NOT imply periodicity on `fullSweep`.

原文：b3_colle2.txt:414, 784 — the paper uses `ℤ₊` in both places, not `ℤ`.

**Construction**: Take `B = {(0,0)}`, `vl = (1,0)`, `c = 1`, and a configuration `x` that is
periodic with period `(1,0)` on the forward half-strip `{(t,0) : t ≥ 0}` but NOT periodic
on the full line `ℤ × {0}`.

Specifically, define `x (t, 0) = 0` for `t ≥ 0` and `x (t, 0) = 1` for `t < 0`.
Then `x` is constant (hence periodic) on `halfStrip B vl`, but `x(-1, 0) = 1 ≠ 0 = x(0, 0)`,
so the period fails at `z = (-1, 0) ∈ fullSweep B vl`. -/
theorem not_periodOn_fullSweep_of_forward_only :
    ∃ (x : Config ℤ) (B : Set (ℤ × ℤ)) (vl : ℤ × ℤ) (c : ℤ),
      (∀ z ∈ halfStrip B vl, x z = T (c • vl) x z) ∧
      ¬ PeriodOn x (fullSweep B vl) (c • vl) := by
  -- Configuration: 0 on the non-negative side, 1 on the negative side
  let x : Config ℤ := fun z => if 0 ≤ z.1 then 0 else 1
  -- Base set: just the origin
  let B : Set (ℤ × ℤ) := {(0, 0)}
  -- Direction: horizontal
  let vl : ℤ × ℤ := (1, 0)
  -- Period value
  let c : ℤ := 1

  refine ⟨x, B, vl, c, ?_, ?_⟩

  · -- Part 1: x is constant on halfStrip B vl, hence trivially periodic
    intro z hz
    rw [mem_halfStrip_iff] at hz
    obtain ⟨b, hb, t, rfl⟩ := hz
    have : b = (0, 0) := Set.mem_singleton_iff.mp hb
    rw [this]
    -- Unfold T: T (c • vl) x z = x (z + c • vl)
    -- Both arguments evaluate to points with non-negative first coordinate
    rfl

  · -- Part 2: x is NOT periodic on fullSweep B vl
    intro hp
    -- The point (-1, 0) is in fullSweep B vl
    have h_neg1 : (-1, 0) ∈ fullSweep B vl := by
      rw [mem_fullSweep_iff]
      refine ⟨(0, 0), Set.mem_singleton (0, 0), -1, ?_⟩
      rfl
    -- And (-1, 0) + (1, 0) = (0, 0) is also in fullSweep B vl
    have h_zero : (0, 0) ∈ fullSweep B vl := by
      rw [mem_fullSweep_iff]
      exact ⟨(0, 0), Set.mem_singleton (0, 0), 0, by rfl⟩
    -- Apply PeriodOn at z = (-1, 0)
    have hper := hp (-1, 0) h_neg1 h_zero
    -- hper says: x((-1, 0) + c • vl) = x(-1, 0)
    -- Since c = 1 and vl = (1, 0), we have c • vl = (1, 0)
    show False
    have : c • vl = (1, 0) := by rfl
    rw [this] at hper
    -- Now: x((-1, 0) + (1, 0)) = x(-1, 0)
    -- Directly compute the addition and evaluate
    show False
    change x ((0, 0)) = x (-1, 0) at hper
    unfold x at hper
    -- x (0, 0) = if 0 ≤ 0 then 0 else 1 = 0
    -- x (-1, 0) = if 0 ≤ -1 then 0 else 1 = 1
    norm_num at hper

end Nivat.ColleReg
