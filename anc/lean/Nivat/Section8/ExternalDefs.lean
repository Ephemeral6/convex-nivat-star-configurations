/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.Section8.HalfPlane

/-!
# Shared definitions for External.lean and downstream modules

Extracted from `External.lean` to break circular dependencies. Contains definitions
needed by both `External.lean` itself and `ColleRegion.lean`.

* `sideOf` — closed half-plane {z | ⟨w,z⟩ ≤ 0}
* `ONED` — one-sided nonexpansive directions
* `PeriodicDecompZ`, `HasOrderZ` — periodic decomposition and order
* `IsCounterexample`, `IsMinimalCounterexample` — minimal counterexamples
-/

namespace Nivat

variable {α : Type*}

/-! ### Half-plane and ONED -/

/-- The closed half-plane on the non-positive side of the direction `w`. -/
def sideOf (w : ℝ × ℝ) : Set (ℤ × ℤ) := {z | inner2 w z ≤ 0}

/-- A *one-sided nonexpansive direction* `w` of a configuration `ξ`, relative to the subshift
`X = orbitClosure ξ`, in the sense of Colle [2]: an oriented line, recorded here by a non-zero
normal `w`, is one-sided nonexpansive if two distinct elements of `X` agree on the whole closed
half-plane `{⟨z, w⟩ ≤ 0}`.  The paper quotes this notion from [2] without restating it; the two
orientations of a line `ℓ` are `w` and `-w`. -/
def ONED (ξ : Config α) : Set (ℝ × ℝ) :=
  {w | w ≠ 0 ∧ ∃ x ∈ orbitClosure ξ, ∃ y ∈ orbitClosure ξ, x ≠ y ∧ ∀ z ∈ sideOf w, x z = y z}

/-! ### Counterexamples of minimal order -/

/-- A *periodic decomposition* of a `ℤ`-valued configuration of length `n`; the values of the
components may be unbounded.  Paper Remark 8.3. -/
def PeriodicDecompZ (ξ : Config ℤ) (n : ℕ) : Prop :=
  ∃ f : Fin n → Config ℤ, (∀ i, IsPeriodic (f i)) ∧ ∀ z, ξ z = ∑ i, f i z

/-- `ord(ξ) = n`, the length of a `ℤ`-minimal periodic decomposition.  Paper Remark 8.3. -/
def HasOrderZ (ξ : Config ℤ) (n : ℕ) : Prop :=
  PeriodicDecompZ ξ n ∧ ∀ k, PeriodicDecompZ ξ k → n ≤ k

/-- A counterexample to the convex Nivat conjecture: a non-periodic configuration of low convex
complexity with finite alphabet `A ⊆ ℤ_{>0}`.  Paper Remark 8.3. -/
def IsCounterexample (ξ : Config ℤ) : Prop :=
  (Set.range ξ).Finite ∧ (∀ z, 0 < ξ z) ∧ ¬ IsPeriodic ξ ∧ LowConvexComplexity ξ

/-- A counterexample whose order is minimal among all counterexamples.  Paper Remark 8.3. -/
def IsMinimalCounterexample (ξ : Config ℤ) : Prop :=
  IsCounterexample ξ ∧ ∃ n, HasOrderZ ξ n ∧
    ∀ ζ : Config ℤ, IsCounterexample ζ → ∀ k, HasOrderZ ζ k → n ≤ k

end Nivat
