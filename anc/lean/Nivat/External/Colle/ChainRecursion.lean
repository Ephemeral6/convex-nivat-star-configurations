/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.LatticeEdges
import Nivat.Defs.Config

/-!
# Global recursive assembly of the `A`/`B` chains of `ChainData`

Team-lead's task (2026-09-17): assemble the *single-step* wiring already proved in
`tmp/chaindata_wiring_combined.lean` (`wire_maximal_element`) into `ℕ`-indexed chains
`A B : ℕ → Set (ℤ × ℤ)` satisfying `ChainData`'s `envB/envA/subBA/subAB/subStrip/agreeA`
fields (`Lemma35.lean:714-724`).

Per instruction #3: `supply_edge_structure`'s `sorryAx` is NOT touched here. The single-step
conclusion of `wire_maximal_element` is taken as an explicit hypothesis (`step`), so this file
is independent of that gap; the two can be composed later by literally substituting a proof of
`step` derived from `wire_maximal_element` once `supply_edge_structure` lands.

Construction choice (accepted by team-lead): `B (i+1) := A i`, so `subAB` is `subset_rfl`;
`u` is held constant at the seed's `u₀` (a valid instantiation — `ChainData.u` is not required
to vary, and `wire_maximal_element`'s output agrees under the *same* `u` as its input).

Base case `B 0`: per team-lead's pointer, `subset_halfStrip B vl` (`LatticeEdges.lean:1813`,
a proved theorem, `t = 0` case) shows `B ⊆ Nivat.LE2.halfStrip B vl` for ANY `B` — but that is
not what `B 0` itself needs. `B 0` needs `EnvOf S (B 0)` and agreement under `u₀`, which are
external data (the actual `EnvOf`-enveloped set from `hcase2`/`extract_disagreement_point`'s
context), not something `subset_halfStrip` supplies. So `B 0`, like `step`, is taken as an
explicit hypothesis here (`hB0`, `hagree0`) — this file does not manufacture the seed, it only
assembles the recursion from seed + step.
-/

set_option autoImplicit false

namespace Nivat.ColleReg4

open Nivat Nivat.LE2

variable {ξ : Config ℤ} {xper : Config ℤ} {S : Finset (ℤ × ℤ)} {vl u₀ : ℤ × ℤ}

/-- The type of a single "state": an `EnvOf S`-enveloped set on which `T u₀ ξ` agrees with
`xper`. This is exactly what both the seed `B 0` and every subsequent `B (i+1) := A i` are. -/
def AgreeState (ξ : Config ℤ) (xper : Config ℤ) (S : Finset (ℤ × ℤ)) (u₀ : ℤ × ℤ) : Type :=
  {B : Set (ℤ × ℤ) // EnvOf (↑S : Set (ℤ × ℤ)) B ∧ ∀ z ∈ B, T u₀ ξ z = xper z}

/-- The single-step hypothesis: exactly `wire_maximal_element`'s conclusion shape
(`tmp/chaindata_wiring_combined.lean:157-179`), taken as a parameter so this file does not
depend on `supply_edge_structure`'s `sorryAx`. -/
def StepHyp (ξ : Config ℤ) (xper : Config ℤ) (S : Finset (ℤ × ℤ)) (vl u₀ : ℤ × ℤ) : Prop :=
  ∀ B : Set (ℤ × ℤ), EnvOf (↑S : Set (ℤ × ℤ)) B → (∀ z ∈ B, T u₀ ξ z = xper z) →
    ∃ A : Set (ℤ × ℤ),
      EnvOf (↑S : Set (ℤ × ℤ)) A ∧
      B ⊆ A ∧
      A ⊆ Nivat.LE2.halfStrip B vl ∧
      (∀ z ∈ A, T u₀ ξ z = xper z) ∧
      (∀ Tset, EnvOf (↑S : Set (ℤ × ℤ)) Tset →
        B ⊆ Tset → Tset ⊆ Nivat.LE2.halfStrip B vl →
        (∀ z ∈ Tset, T u₀ ξ z = xper z) →
        A ⊆ Tset → Tset = A)

variable (ξ xper S vl u₀)

/-- The recursively-built sequence of states, `state 0 = ⟨B₀, ...⟩` and
`state (i+1) = ⟨A i, ...⟩` where `A i` is the (classically chosen) output of `step` applied to
`state i`. Structural recursion on `ℕ`, no `sorry`. -/
noncomputable def chainState (hstep : StepHyp ξ xper S vl u₀)
    (B0 : Set (ℤ × ℤ)) (hB0 : EnvOf (↑S : Set (ℤ × ℤ)) B0)
    (hagree0 : ∀ z ∈ B0, T u₀ ξ z = xper z) :
    ℕ → AgreeState ξ xper S u₀
  | 0 => ⟨B0, hB0, hagree0⟩
  | n + 1 =>
      let prev := chainState hstep B0 hB0 hagree0 n
      ⟨Classical.choose (hstep prev.1 prev.2.1 prev.2.2),
        (Classical.choose_spec (hstep prev.1 prev.2.1 prev.2.2)).1,
        (Classical.choose_spec (hstep prev.1 prev.2.1 prev.2.2)).2.2.2.1⟩

variable (hstep : StepHyp ξ xper S vl u₀)
variable (B0 : Set (ℤ × ℤ)) (hB0 : EnvOf (↑S : Set (ℤ × ℤ)) B0)
variable (hagree0 : ∀ z ∈ B0, T u₀ ξ z = xper z)

/-- The chain of `B`'s: `B i := (chainState i).val`. -/
noncomputable def chainB : ℕ → Set (ℤ × ℤ) := fun i => (chainState ξ xper S vl u₀ hstep B0 hB0 hagree0 i).1

/-- The chain of `A`'s: `A i` is the maximal element produced by `step` applied to `B i`,
i.e. exactly `(chainState (i+1)).val`, by construction of `chainState`. -/
noncomputable def chainA : ℕ → Set (ℤ × ℤ) :=
  fun i => Classical.choose (hstep (chainB ξ xper S vl u₀ hstep B0 hB0 hagree0 i)
    (chainState ξ xper S vl u₀ hstep B0 hB0 hagree0 i).2.1
    (chainState ξ xper S vl u₀ hstep B0 hB0 hagree0 i).2.2)

theorem chainB_succ_eq_chainA (i : ℕ) :
    chainB ξ xper S vl u₀ hstep B0 hB0 hagree0 (i + 1) = chainA ξ xper S vl u₀ hstep B0 hB0 hagree0 i := rfl

/-- Package of the four properties `step` grants for `A i` relative to `B i`. -/
theorem chainA_spec (i : ℕ) :
    EnvOf (↑S : Set (ℤ × ℤ)) (chainA ξ xper S vl u₀ hstep B0 hB0 hagree0 i) ∧
    chainB ξ xper S vl u₀ hstep B0 hB0 hagree0 i ⊆ chainA ξ xper S vl u₀ hstep B0 hB0 hagree0 i ∧
    chainA ξ xper S vl u₀ hstep B0 hB0 hagree0 i ⊆
      Nivat.LE2.halfStrip (chainB ξ xper S vl u₀ hstep B0 hB0 hagree0 i) vl ∧
    (∀ z ∈ chainA ξ xper S vl u₀ hstep B0 hB0 hagree0 i, T u₀ ξ z = xper z) :=
  ⟨(Classical.choose_spec (hstep (chainB ξ xper S vl u₀ hstep B0 hB0 hagree0 i)
      (chainState ξ xper S vl u₀ hstep B0 hB0 hagree0 i).2.1
      (chainState ξ xper S vl u₀ hstep B0 hB0 hagree0 i).2.2)).1,
    (Classical.choose_spec (hstep (chainB ξ xper S vl u₀ hstep B0 hB0 hagree0 i)
      (chainState ξ xper S vl u₀ hstep B0 hB0 hagree0 i).2.1
      (chainState ξ xper S vl u₀ hstep B0 hB0 hagree0 i).2.2)).2.1,
    (Classical.choose_spec (hstep (chainB ξ xper S vl u₀ hstep B0 hB0 hagree0 i)
      (chainState ξ xper S vl u₀ hstep B0 hB0 hagree0 i).2.1
      (chainState ξ xper S vl u₀ hstep B0 hB0 hagree0 i).2.2)).2.2.1,
    (Classical.choose_spec (hstep (chainB ξ xper S vl u₀ hstep B0 hB0 hagree0 i)
      (chainState ξ xper S vl u₀ hstep B0 hB0 hagree0 i).2.1
      (chainState ξ xper S vl u₀ hstep B0 hB0 hagree0 i).2.2)).2.2.2.1⟩

/-! ## The six `ChainData` fields -/

/-- `ChainData.envB` (`Lemma35.lean:714`): each `B i` is `EnvOf S`. -/
theorem envB_chain (i : ℕ) : EnvOf (↑S : Set (ℤ × ℤ)) (chainB ξ xper S vl u₀ hstep B0 hB0 hagree0 i) :=
  (chainState ξ xper S vl u₀ hstep B0 hB0 hagree0 i).2.1

/-- `ChainData.envA` (`Lemma35.lean:716`): each `A i` is `EnvOf S`. -/
theorem envA_chain (i : ℕ) : EnvOf (↑S : Set (ℤ × ℤ)) (chainA ξ xper S vl u₀ hstep B0 hB0 hagree0 i) :=
  (chainA_spec ξ xper S vl u₀ hstep B0 hB0 hagree0 i).1

/-- `ChainData.subBA` (`Lemma35.lean:718`): `B i ⊆ A i`. -/
theorem subBA_chain (i : ℕ) :
    chainB ξ xper S vl u₀ hstep B0 hB0 hagree0 i ⊆ chainA ξ xper S vl u₀ hstep B0 hB0 hagree0 i :=
  (chainA_spec ξ xper S vl u₀ hstep B0 hB0 hagree0 i).2.1

/-- `ChainData.subAB` (`Lemma35.lean:720`): `A i ⊆ B (i+1)`. Free, by the construction
choice `B (i+1) := A i`. -/
theorem subAB_chain (i : ℕ) :
    chainA ξ xper S vl u₀ hstep B0 hB0 hagree0 i ⊆ chainB ξ xper S vl u₀ hstep B0 hB0 hagree0 (i + 1) := by
  rw [chainB_succ_eq_chainA]

/-- `ChainData.subStrip` (`Lemma35.lean:722`): `A i ⊆ halfStrip (B i) vl`. -/
theorem subStrip_chain (i : ℕ) :
    chainA ξ xper S vl u₀ hstep B0 hB0 hagree0 i ⊆
      Nivat.LE2.halfStrip (chainB ξ xper S vl u₀ hstep B0 hB0 hagree0 i) vl :=
  (chainA_spec ξ xper S vl u₀ hstep B0 hB0 hagree0 i).2.2.1

/-- `ChainData.agreeA` (`Lemma35.lean:724`), with `u i := u₀` constant: agreement on `A i`. -/
theorem agreeA_chain (i : ℕ) :
    ∀ z ∈ chainA ξ xper S vl u₀ hstep B0 hB0 hagree0 i, T u₀ ξ z = xper z :=
  (chainA_spec ξ xper S vl u₀ hstep B0 hB0 hagree0 i).2.2.2

end Nivat.ColleReg4

