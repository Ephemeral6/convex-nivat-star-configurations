/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.Lemma41
import Nivat.External.Colle.Lemma35
import Nivat.External.Colle.AmbiguousCounting
import Nivat.Defs.Complexity

/-!
# Two bridging lemmas for Claim 4.7 (and, verbatim, Claim 4.11)

Collé's Claim 4.7 (`scratch/b3_colle2.txt:826-837`) runs periodicity up through two layers:

* **step 2** (`:826-828`) — from "`(T^u η)|_{R^N_I}` has period `h`" to "the `Q`-pattern of
  `η` at `t` equals the one at `t + h`";
* **step 3** (`:830-837`) — from "the two patterns agree on `Q`" plus `N_𝒯(ℓ', γ) = 1`
  (i.e. the restriction map `Q ← S` is injective) to "they agree on all of `S`".

Both steps are stated in the paper about `η` and its translates only, so they are recorded
here as statements about a single configuration at two base points `t₁`, `t₂`.  The paper
says the proof of Claim 4.11 is the same argument, so the same two lemmas serve there.

Step 3 is the *logical* form of `Nivat.Colle.restrict_occurring_pattern_injective_of_P_eq`
(`AmbiguousCounting.lean:96`), which delivers the injectivity in counting form.

## Main results

* `pattern_eq_of_periodicOnWith` — step 2.
* `eqOn_S_of_unique_extension_config` — step 3.
-/

namespace Nivat.Colle47

open Nivat Nivat.Colle35 Nivat.Colle

variable {A : Type*}

/-- **Claim 4.7 step 2** (`b3_colle2.txt:826-828`).

If `x` has period `h` on the region `R`, and both translated copies `t + Q` and `t + h + Q`
of the window sit inside `R`, then the `Q`-patterns of `x` at `t` and at `t + h` coincide. -/
theorem pattern_eq_of_periodicOnWith
    {x : Config A} {R : Set (ℤ × ℤ)} {h : ℤ × ℤ}
    (hper : PeriodicOnWith x R h)
    {Q : Finset (ℤ × ℤ)} {t : ℤ × ℤ}
    (hsub : ∀ z ∈ Q, t + z ∈ R ∧ t + h + z ∈ R) :
    pattern x Q t = pattern x Q (t + h) := by
  funext q
  have hper_eq := hper.2
  have hq_mem : t + (q : ℤ × ℤ) ∈ R := (hsub q.val q.property).1
  have hrw : t + h + (q : ℤ × ℤ) = t + (q : ℤ × ℤ) + h := by ring
  have hq_h_mem : t + (q : ℤ × ℤ) + h ∈ R := by rw [← hrw]; exact (hsub q.val q.property).2
  have hperiod : x (t + (q : ℤ × ℤ) + h) = x (t + (q : ℤ × ℤ)) := hper_eq _ hq_mem hq_h_mem
  simp only [pattern]
  rw [hrw]
  exact hperiod.symm

/-- **Claim 4.7 step 3** (`b3_colle2.txt:830-837`).

Two translates of the same configuration `η` that agree on the window `Q` agree on the whole
of `S ⊇ Q`, provided the restriction map on occurring patterns is injective — which is what
`N_𝒯(ℓ', γ) = 1` gives, via
`Nivat.Colle.restrict_occurring_pattern_injective_of_P_eq` (`AmbiguousCounting.lean:96`). -/
theorem eqOn_S_of_unique_extension_config
    {η : Config A} {S Q : Finset (ℤ × ℤ)} (hQS : Q ⊆ S)
    {t₁ t₂ : ℤ × ℤ}
    (heqQ : ∀ z ∈ Q, η (t₁ + z) = η (t₂ + z))
    (hunique : Function.Injective (restrict_occurring_pattern η hQS)) :
    (∀ z ∈ S, η (t₁ + z) = η (t₂ + z)) := by
  intro z hz
  have h1_occurs : pattern η S t₁ ∈ patterns η S := ⟨t₁, rfl⟩
  have h2_occurs : pattern η S t₂ ∈ patterns η S := ⟨t₂, rfl⟩
  have hrestrict_eq : restrict_occurring_pattern η hQS ⟨pattern η S t₁, h1_occurs⟩ =
                       restrict_occurring_pattern η hQS ⟨pattern η S t₂, h2_occurs⟩ := by
    ext q
    simp only [restrict_occurring_pattern, pattern]
    exact heqQ q.val q.property
  have hpat_eq : (⟨pattern η S t₁, h1_occurs⟩ : patterns η S) = ⟨pattern η S t₂, h2_occurs⟩ :=
    hunique hrestrict_eq
  have hfun_eq : pattern η S t₁ = pattern η S t₂ := congrArg Subtype.val hpat_eq
  have : pattern η S t₁ ⟨z, hz⟩ = pattern η S t₂ ⟨z, hz⟩ := congrFun hfun_eq ⟨z, hz⟩
  simp only [pattern] at this
  exact this

end Nivat.Colle47
