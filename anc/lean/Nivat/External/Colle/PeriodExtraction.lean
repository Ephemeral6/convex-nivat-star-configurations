/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.Defs.Orbit
import Nivat.Defs.Config

/-!
# L1: Period extraction from agreement with globally periodic configurations

This file contains the core L1 lemma needed by `region_periods_and_rays`:
if a configuration `ϑ` agrees with a globally periodic configuration `xper`
on a region `R`, then `ϑ` inherits the periods of `xper` within `R`.

This corresponds to Collé's argument in Lemma 3.5 (colle_full.txt:716-717):

> "by compactness of X, the sequence (ψ_i)_{i∈ℕ} has an accumulation point
>  ϑ ∈ X such that ϑ|Â_∞ = x̂_per|Â_∞. In particular, one has that ϑ|Â_∞ is
>  a periodic configuration with period parallel to ℓ."

The key observation: Collé does NOT prove that `ϑ` is globally periodic.
He only proves **restricted periodicity** (Definition 2.11): `ϑ` is periodic
*within* `Â_∞` with respect to directions parallel to the unbounded edges.

## Main results

* `periodicOnWith_of_agree_periodic` — L1a: inherit restricted periodicity from agreement
* `periodicOnWith_of_mem_Per` — L1b: global period implies restricted period

-/

namespace Nivat.ColleReg

open Nivat

/-- **Colle, Definition 2.11.**  `η|𝒰` is periodic with period `h` if `h ≠ 0` and
`η_{g+h} = η_g` for all `g ∈ 𝒰 ∩ (𝒰 - h)`, i.e. for all `g ∈ 𝒰` with `g + h ∈ 𝒰`.

NOTE: This is a local copy to avoid dependency on `Lemma35.lean` which transitively
depends on the currently broken `LatticeEdges.lean`. Once that is fixed, this file
should import `Nivat.External.Colle.Lemma35` and remove this definition. -/
def PeriodicOnWith {α : Type*} (η : Config α) (U : Set (ℤ × ℤ)) (h : ℤ × ℤ) : Prop :=
  h ≠ 0 ∧ ∀ g ∈ U, g + h ∈ U → η (g + h) = η g

variable {α : Type*}

/-- **L1a: Period extraction from agreement.**
If `ϑ` agrees with `xper` on region `R`, and `xper` has global period `h`,
then `ϑ` has restricted period `h` on `R`. -/
theorem periodicOnWith_of_agree_periodic {ϑ xper : Config α} {R : Set (ℤ × ℤ)} {h : ℤ × ℤ}
    (hagree : ∀ z ∈ R, ϑ z = xper z)
    (hper : h ∈ Per xper)
    (hne : h ≠ 0) :
    PeriodicOnWith ϑ R h := by
  constructor
  · exact hne
  · intro z hz hz_h
    rw [hagree z hz, hagree (z + h) hz_h, Per.apply hper z]

/-- **L1b: Global period implies restricted period.**
Any global period of a configuration is also a restricted period on any subset. -/
theorem periodicOnWith_of_mem_Per {ϑ : Config α} {R : Set (ℤ × ℤ)} {h : ℤ × ℤ}
    (hper : h ∈ Per ϑ)
    (hne : h ≠ 0) :
    PeriodicOnWith ϑ R h := by
  constructor
  · exact hne
  · intro z _ _
    exact Per.apply hper z

/-- **Combining agreement and periodicity.**
If `ϑ` agrees with a periodic configuration on `R`, and `R` is closed under
shifting by `h`, then `ϑ` is periodic on `R` with period `h`. -/
theorem periodicOnWith_of_agree_periodic_closed {ϑ xper : Config α} {R : Set (ℤ × ℤ)} {h : ℤ × ℤ}
    (hagree : ∀ z ∈ R, ϑ z = xper z)
    (hper : h ∈ Per xper)
    (hne : h ≠ 0)
    (hclosed : ∀ z ∈ R, z + h ∈ R) :
    PeriodicOnWith ϑ R h := by
  constructor
  · exact hne
  · intro z hz _
    have hz_h : z + h ∈ R := hclosed z hz
    rw [hagree z hz, hagree (z + h) hz_h, Per.apply hper z]

end Nivat.ColleReg
