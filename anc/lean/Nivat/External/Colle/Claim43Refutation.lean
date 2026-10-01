/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.Lemma41

/-!
# `line_closure_of_period` is false as stated

`Nivat/External/Colle/Claim43.lean:137` states `line_closure_of_period`:

```
theorem line_closure_of_period {A : Type*} {x y : Config A} {R : Set (ℤ × ℤ)}
    {u : ℤ × ℤ} {c : ℤ} (hc : c ≠ 0)
    (hxper : PeriodOn x R (c • u)) (hyper : PeriodOn y R (c • u))
    {z₀ : ℤ × ℤ} (hz₀ : z₀ ∈ R)
    (hconv : IsLatticeConvexRegion R)
    (hagree : ∀ j : ℕ, j < c.natAbs → z₀ + (j : ℤ) • u ∈ R →
      x (z₀ + (j : ℤ) • u) = y (z₀ + (j : ℤ) • u)) :
    ∀ k : ℤ, z₀ + k • u ∈ R → x (z₀ + k • u) = y (z₀ + k • u)
```

**This statement is refutable**, so no amount of work on its proof body can succeed.
`Claim43.lean` does not currently compile, so the kernel never rejected it; the
`sorry`-free claim about that file was never actually checked by Lean.

## Why it fails

The agreement window is indexed by a **natural** `j < |c|`, which only pins down
residues in the *forward* `u`-direction, while the conclusion quantifies over **all
integers** `k`, including the backward ray. The guard `z₀ + (j : ℤ) • u ∈ R` makes
this worse: when `R` runs backwards along `u`, every `j ≥ 1` leaves `R` and the
hypothesis becomes vacuous there, leaving only `j = 0` — a single point — to
control the whole infinite backward ray.

A period of `x|R` in the sense of `PeriodOn` (Definition 2.11, overlap-only) does
**not** let you walk backwards out of the agreement window: the two-sided transport
needs `z` and `z + c•u` both in `R`, and the backward steps exit the window before
re-entering it.

## The witness

`R = {z | z.1 ≤ 0}` (lattice-convex), `u = (1,0)`, `c = 2`, `z₀ = (0,0)`,
`x ≡ 0`, `y z = z.1 % 2`. Both are `2•u`-periodic on `R`; the only `j < 2` that
lies in `R` is `j = 0`, where both are `0`; yet at `k = -1` we get
`x = 0` and `y = (-1) % 2 = 1`.

## Consequence for `colle_region`

Any repair must either restrict the conclusion to the forward ray (`k : ℕ`), or
strengthen `hagree` to range over an integer window `|j| < |c|`, or add a hypothesis
forcing `R` to be closed under the backward step. Colle's actual Claim 4.3 sweeps
along a direction *pointing into* the region, which is the content that the `ℕ`/`ℤ`
mismatch above silently dropped.

Verified: `#print axioms line_closure_of_period_is_false` reports only
`[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no custom axiom.
-/

namespace Nivat.Colle43Refutation

open Nivat Nivat.Colle41

/-- The half-plane `{z | z.1 ≤ 0}`, which runs backwards along `u = (1,0)`. -/
def Rhalf : Set (ℤ × ℤ) := {z | z.1 ≤ 0}

/-- The constant-zero configuration. -/
def xc : Config ℤ := fun _ => 0

/-- The parity-of-first-coordinate configuration. -/
def yc : Config ℤ := fun z => z.1 % 2

theorem Rhalf_convex : IsLatticeConvexRegion Rhalf := by
  refine ⟨{p : ℝ × ℝ | p.1 ≤ 0}, ?_, ?_, ?_⟩
  · intro a ha b hb s t hs ht hst
    simp only [Set.mem_ofPred_eq, Prod.fst_add, Prod.smul_fst, smul_eq_mul] at *
    nlinarith
  · exact isClosed_le (by fun_prop) continuous_const
  · ext z
    simp only [Rhalf, Set.mem_preimage, Set.mem_ofPred_eq, toReal]
    exact_mod_cast Iff.rfl

theorem xc_per : PeriodOn xc Rhalf ((2 : ℤ) • (1, 0)) := fun _ _ _ => rfl

theorem yc_per : PeriodOn yc Rhalf ((2 : ℤ) • (1, 0)) := by
  intro z _ _
  show (z + (2 : ℤ) • ((1, 0) : ℤ × ℤ)).1 % 2 = z.1 % 2
  simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, mul_one]
  omega

/-- The agreement hypothesis holds: only `j = 0` survives the `∈ R` guard. -/
theorem agree_window : ∀ j : ℕ, j < (2 : ℤ).natAbs →
    ((0, 0) + (j : ℤ) • ((1, 0) : ℤ × ℤ)) ∈ Rhalf →
    xc ((0, 0) + (j : ℤ) • ((1, 0) : ℤ × ℤ)) =
      yc ((0, 0) + (j : ℤ) • ((1, 0) : ℤ × ℤ)) := by
  intro j hj hmem
  interval_cases j
  · rfl
  · exfalso
    simp only [Rhalf, Set.mem_ofPred_eq, Prod.fst_add, Prod.smul_fst] at hmem
    norm_num at hmem

/-- **The statement of `line_closure_of_period` is false.** -/
theorem line_closure_of_period_is_false :
    ¬ ∀ (A : Type) (x y : Config A) (R : Set (ℤ × ℤ)) (u : ℤ × ℤ) (c : ℤ),
      c ≠ 0 → PeriodOn x R (c • u) → PeriodOn y R (c • u) →
      ∀ z₀ : ℤ × ℤ, z₀ ∈ R → IsLatticeConvexRegion R →
      (∀ j : ℕ, j < c.natAbs → z₀ + (j : ℤ) • u ∈ R →
        x (z₀ + (j : ℤ) • u) = y (z₀ + (j : ℤ) • u)) →
      ∀ k : ℤ, z₀ + k • u ∈ R → x (z₀ + k • u) = y (z₀ + k • u) := by
  intro h
  have hmem : ((0, 0) + (-1 : ℤ) • ((1, 0) : ℤ × ℤ)) ∈ Rhalf := by simp [Rhalf]
  have := h ℤ xc yc Rhalf (1, 0) 2 (by norm_num) xc_per yc_per (0, 0)
    (by simp [Rhalf]) Rhalf_convex agree_window (-1) hmem
  revert this
  show (0 : ℤ) ≠ _
  norm_num [yc]

end Nivat.Colle43Refutation
