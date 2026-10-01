import Nivat.Defs.Complexity
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Sum
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! # Counting ambiguous fibers

An ambiguous fiber uses one element in addition to the baseline element
provided by surjectivity. This is the finite counting step used for
ambiguous pattern restrictions in Colle Proposition 2.10.
-/

namespace Nivat.Colle

open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- A finite surjection has one source element per target and at least
one additional element for every target with two distinct preimages. -/
theorem card_add_card_ambiguous_fibers_le {X Y : Type*}
    [Fintype X] [Fintype Y] (f : X → Y) (hf : Function.Surjective f) :
    Fintype.card Y +
      Fintype.card {y : Y // ∃ a b : X, a ≠ b ∧ f a = y ∧ f b = y} ≤
      Fintype.card X := by
  classical
  let ambiguous : Y → Prop := fun y => ∃ a b : X, a ≠ b ∧ f a = y ∧ f b = y
  have hpoint (y : Y) :
      1 + (if ambiguous y then 1 else 0) ≤ Fintype.card {x : X // f x = y} := by
    split_ifs with hy
    · obtain ⟨a, b, hab, ha, hb⟩ := hy
      apply Nat.succ_le_of_lt
      exact Fintype.one_lt_card_iff.mpr
        ⟨⟨a, ha⟩, ⟨b, hb⟩, fun h => hab (congrArg Subtype.val h)⟩
    · obtain ⟨a, ha⟩ := hf y
      exact Fintype.card_pos_iff.mpr ⟨⟨a, ha⟩⟩
  have hsum :
      (∑ y : Y, (1 + (if ambiguous y then 1 else 0))) ≤
        ∑ y : Y, Fintype.card {x : X // f x = y} := by
    exact Finset.sum_le_sum fun y _ => hpoint y
  have hfibers : (∑ y : Y, Fintype.card {x : X // f x = y}) = Fintype.card X := by
    rw [← Fintype.card_sigma]
    exact Fintype.card_congr (Equiv.sigmaFiberEquiv f)
  rw [hfibers] at hsum
  simpa [Finset.sum_add_distrib, Fintype.card_subtype, ambiguous] using hsum

/-- The number of ambiguous fibers is bounded by the cardinality surplus
of a finite surjection. -/
theorem card_ambiguous_fibers_le_sub {X Y : Type*}
    [Fintype X] [Fintype Y] (f : X → Y) (hf : Function.Surjective f) :
    Fintype.card {y : Y // ∃ a b : X, a ≠ b ∧ f a = y ∧ f b = y} ≤
      Fintype.card X - Fintype.card Y := by
  have := card_add_card_ambiguous_fibers_le f hf
  omega

/-- Restriction sends an occurring pattern to an occurring pattern. -/
def restrict_occurring_pattern {α : Type*} (θ : Config α)
    {Q S : Finset (ℤ × ℤ)} (hQS : Q ⊆ S) :
    patterns θ S → patterns θ Q := fun p =>
  ⟨fun q => p.1 ⟨q.1, hQS q.2⟩, by
    obtain ⟨u, hu⟩ := p.2
    exact ⟨u, funext fun q => congrFun hu ⟨q.1, hQS q.2⟩⟩⟩

/-- Every occurring pattern on the smaller window extends to one on the
larger window, using the same occurrence in the configuration. -/
theorem restrict_occurring_pattern_surjective {α : Type*} (θ : Config α)
    {Q S : Finset (ℤ × ℤ)} (hQS : Q ⊆ S) :
    Function.Surjective (restrict_occurring_pattern θ hQS) := by
  rintro ⟨p, u, rfl⟩
  exact ⟨⟨pattern θ S u, u, rfl⟩, rfl⟩

/-- Occurring smaller-window patterns with two distinct larger-window
extensions. The set is a subset of the occurring patterns on `Q`. -/
def ambiguous_patterns {α : Type*} (θ : Config α)
    {Q S : Finset (ℤ × ℤ)} (hQS : Q ⊆ S) : Set (patterns θ Q) :=
  {p | ∃ a b : patterns θ S, a ≠ b ∧
    restrict_occurring_pattern θ hQS a = p ∧ restrict_occurring_pattern θ hQS b = p}

/-- Ambiguous restrictions are bounded by the loss of pattern complexity. -/
theorem ncard_ambiguous_patterns_le_sub {α : Type*} {θ : Config α}
    (hθ : (Set.range θ).Finite) {Q S : Finset (ℤ × ℤ)} (hQS : Q ⊆ S) :
    (ambiguous_patterns θ hQS).ncard ≤ P θ S - P θ Q := by
  classical
  let := (patterns_finite_of_range_finite hθ S).fintype
  let := (patterns_finite_of_range_finite hθ Q).fintype
  change Nat.card {p : patterns θ Q // ∃ a b : patterns θ S, a ≠ b ∧
      restrict_occurring_pattern θ hQS a = p ∧
      restrict_occurring_pattern θ hQS b = p} ≤
    Nat.card (patterns θ S) - Nat.card (patterns θ Q)
  have h := card_ambiguous_fibers_le_sub (restrict_occurring_pattern θ hQS)
    (restrict_occurring_pattern_surjective θ hQS)
  simpa only [← Nat.card_eq_fintype_card] using h

/-- If restriction loses no complexity, every occurring smaller-window
pattern has a unique larger-window extension. -/
theorem restrict_occurring_pattern_injective_of_P_eq {α : Type*} {θ : Config α}
    (hθ : (Set.range θ).Finite) {Q S : Finset (ℤ × ℤ)} (hQS : Q ⊆ S)
    (hP : P θ Q = P θ S) : Function.Injective (restrict_occurring_pattern θ hQS) := by
  classical
  let := (patterns_finite_of_range_finite hθ S).fintype
  let := (patterns_finite_of_range_finite hθ Q).fintype
  apply (Fintype.bijective_iff_surjective_and_card _).mpr ?_ |>.1
  refine ⟨restrict_occurring_pattern_surjective θ hQS, ?_⟩
  change Nat.card (patterns θ Q) = Nat.card (patterns θ S) at hP
  simpa only [Nat.card_eq_fintype_card] using hP.symm

/-- Pattern complexity is monotone in the window for a configuration of
finite range, without requiring its ambient alphabet to be finite. -/
theorem P_mono_of_range_finite {α : Type*} {θ : Config α}
    (hθ : (Set.range θ).Finite) {Q S : Finset (ℤ × ℤ)} (hQS : Q ⊆ S) :
    P θ Q ≤ P θ S := by
  classical
  let := (patterns_finite_of_range_finite hθ S).fintype
  let := (patterns_finite_of_range_finite hθ Q).fintype
  change Nat.card (patterns θ Q) ≤ Nat.card (patterns θ S)
  simp only [Nat.card_eq_fintype_card]
  exact Fintype.card_le_of_surjective _ (restrict_occurring_pattern_surjective θ hQS)

/-- Injective restriction preserves the number of occurring patterns. -/
theorem P_eq_of_restrict_occurring_pattern_injective {α : Type*} {θ : Config α}
    (hθ : (Set.range θ).Finite) {Q S : Finset (ℤ × ℤ)} (hQS : Q ⊆ S)
    (hi : Function.Injective (restrict_occurring_pattern θ hQS)) : P θ Q = P θ S := by
  classical
  let := (patterns_finite_of_range_finite hθ S).fintype
  let := (patterns_finite_of_range_finite hθ Q).fintype
  change Nat.card (patterns θ Q) = Nat.card (patterns θ S)
  simp only [Nat.card_eq_fintype_card]
  exact (Fintype.card_of_bijective ⟨hi, restrict_occurring_pattern_surjective θ hQS⟩).symm

end Nivat.Colle
