/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.ChainGeom
import Nivat.External.Colle.Theorem114Step3

/-!
# Claim 3.7 delivers clause 2 of `ColleStep3Chain`

`Nivat.Colle3.ColleStep3Chain` (`Theorem114Step3.lean:682`) is the one unproved hypothesis of
`colle114_of`.  It asks for a `ϑ ∈ orbitClosure η` and a direction `v ≠ 0` with

* **clause 1** — `∀ y, IsAccPointAlong v ϑ y → IsPeriodic y` (Proposition 2.12), and
* **clause 2** — `∀ y, IsAccPointAlong v ϑ y → ¬ DoublyPeriodic y` (Claim 3.7).

This file records, as a compiled theorem rather than a comment, that
`ColleReg.region_not_periodic_of_geom` **is** clause 2 — that the shape it was weakened to
under FROZEN E1 lands exactly on the target and not merely near it.  Two identifications are
involved, both `rfl` and both checked here:

* `Nivat.Colle45.IsFullyPeriodic = DoublyPeriodic` (`Lemma45.lean:75`, a plain alias);
* the quantifier block `∀ W M, ∃ t, M ≤ t ∧ ∀ z ∈ W, y z = T (t • v) ϑ z` is the definition of
  `Nivat.Colle3.IsAccPointAlong` (`Theorem114Step3.lean:293`) — same `t : ℕ` (so the same
  one-sided orbit), same `Finset` windows, same cofinality.

The remaining step is De Morgan.

## Scope

This does **not** prove `ColleStep3Chain`: clause 1 and the construction of `ϑ` are untouched,
and the two routes do not share hypotheses — `ColleStep3Chain` assumes *no* line is
bi-nonexpansive (`hONED`), whereas `ColleReg.colle_region` assumes one is.  What is settled
here is only that Claim 3.7's conclusion, in the form this tree proves it, needs no further
mathematics to serve as clause 2.

## Main results

* `Nivat.Colle3.accPointAlong_not_doublyPeriodic` — the De Morgan bridge.
* `Nivat.Colle3.clause2_of_chainDataGeom` — clause 2 from a `ChainDataGeom` and the output of
  Lemma 3.5.
-/

namespace Nivat.Colle3

open Nivat Nivat.Colle35 Nivat.ColleReg

/-- `IsFullyPeriodic` is a plain alias of `DoublyPeriodic` — no extra conditions. -/
theorem isFullyPeriodic_iff_doublyPeriodic {α : Type*} (η : Config α) :
    Colle45.IsFullyPeriodic η ↔ DoublyPeriodic η := Iff.rfl

/-- **The De Morgan bridge.**  "No accumulation point along `v` is fully periodic", stated as
a negated existential, is "every accumulation point along `v` fails to be doubly periodic". -/
theorem accPointAlong_not_doublyPeriodic {ϑ : Config ℤ} {v : ℤ × ℤ}
    (h : ¬ ∃ y : Config ℤ, Colle45.IsFullyPeriodic y ∧
      ∀ (W : Finset (ℤ × ℤ)) (M : ℕ), ∃ t : ℕ, M ≤ t ∧
        ∀ z ∈ W, y z = T ((t : ℤ) • v) ϑ z) :
    ∀ y, IsAccPointAlong v ϑ y → ¬ DoublyPeriodic y :=
  fun _ hy hDP => h ⟨_, hDP, hy⟩

/-- **Clause 2 of `ColleStep3Chain`, from the §3 chain data.**

The hypotheses are exactly those of `ColleReg.region_not_periodic_of_geom`: the bundle, the
generating window, and the shell mismatch `hshell` / `hshell_not` that Lemma 3.5 produces.
The orbit direction is `cg.vJ = v_{ℓ_J}`. -/
theorem clause2_of_chainDataGeom {ξ xper ϑ : Config ℤ} {vl p : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} {gen : ℤ × ℤ}
    (cg : ChainDataGeom ξ xper vl p S gen) {K ε : ℕ}
    (hp_ne : p ≠ 0) (hp_per : p ∈ Per xper)
    (hxper_mem : xper ∈ orbitClosure ξ) (hϑ_mem : ϑ ∈ orbitClosure ξ)
    (hshell : ∀ z ∈ cg.toChainData.shellInf ε, ϑ z = T ((K : ℤ) • vl) xper z)
    (hshell_not : ¬ (∀ z ∈ cg.toChainData.shellInf (ε + 1), ϑ z = T ((K : ℤ) • vl) xper z))
    (hS : Nivat.Colle.IsGeneratingSet ξ S) :
    ∀ y, IsAccPointAlong cg.vJ ϑ y → ¬ DoublyPeriodic y :=
  accPointAlong_not_doublyPeriodic
    (region_not_periodic_of_geom cg hp_ne hp_per hxper_mem hϑ_mem hshell hshell_not hS)

end Nivat.Colle3
