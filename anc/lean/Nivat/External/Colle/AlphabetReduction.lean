/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.Generating
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Nat.Prime.Infinite

/-!
# Colle's alphabet reduction ("changing the alphabet if necessary")

This file formalises the step Colle (arXiv:1909.08195v4) writes three times, in essentially
identical words, at the start of the proofs of Proposition 2.12, Claim 3.6 and its §4.2
analogue (the occurrences differ only in capitalisation and lead-in):

> "Changing the alphabet if necessary, let `p ∈ ℕ` be a prime number such that
> `A ⊂ ℤ_p` and consider the `ℤ_p`-periodic decomposition `η = η̄₁ + ⋯ + η̄_m`,
> where `(η̄ᵢ)_g := (ηᵢ)_g mod p` for all `g ∈ ℤ²`."

(`scratch/b3_colle2.txt` lines 379, 563, 788.  Beyond "such that `A ⊂ ℤ_p`" Colle states no
condition on `p` — no `|A| < p`, no injectivity, no homomorphism property — and gives no
argument that the `ℤ_p` conclusion lifts back to `ℤ`.  Both are supplied here.)

## Why the step is needed

`Nivat/External/Colle/Generating.lean` `isGeneratingSet_of_annihilator` (Lemma 2.5) requires
`{R : Type*} [CommRing R] [NoZeroDivisors R]` with the alphabet *equal to* `R`, because
`Nivat/Laurent/Basic.lean:99` defines

    def act (f : LaurentTwo R) (g : Config R) : Config R :=
      fun z => f.coeff.sum fun u c => c * g (z + u)

under `variable {R : Type*} [CommRing R]`.  There is no `Module R A` variant of `act`
anywhere in the tree, so the alphabet must *be* the coefficient ring.  Meanwhile
`Nivat/External/Colle/Claim36.lean` states `claim36` and `periodic_of_agree_on_strip` over
`[AddCommMonoid A]`, and `HalfPlanePeriodicity.lean` `exists_period_multiple_of_halfPlane`
(Prop 2.12) needs `[AddCommGroup A]`.

**Correction, after an adversarial audit of the first version of this file.**  The paragraph
above is the motivation for the *`[AddCommMonoid A]`* statement of `claim36`.  It is **not**
the motivation for the `Config ℤ` material in Parts 2–4 of this file, and the first version
of this docstring wrongly presented it as such.  `ℤ` is already a domain, so Lemma 2.5
applies to `Config ℤ` directly and no reduction is needed for it.  The error is recorded
rather than deleted.  Two consequences:

* Colle's actual reason for reducing mod `p` is not Lemma 2.5.  It is that the summands
  `ηᵢ`, hence `η − η_m`, may take infinitely many integer values (`b3_colle2.txt:166`:
  the `ηᵢ` "may be defined on infinite alphabets"), while the expansiveness/`nexpd`
  machinery of Lemma 2.6 needs a finite alphabet.  **This file does not address that**;
  it delivers the alphabet bookkeeping only.
* In `exists_prime_colle_reduction` the two conclusions are logically independent.  The
  annihilator half holds for *every* `p`, including `p = 0` (`ZMod 0 = ℤ`); only the
  `Per (reduceMod p η) = Per η` half uses primality and `hfin`.  They are bundled because
  Colle's sentence bundles them, not because one needs the other.

## What is in force in the paper at Claim 3.6

Colle §1.3: "From now on, we will suppose `A ⊂ R`, where `R` is `ℤ` or some finite filed
[sic]."  Theorem 1.14, whose proof is §3.1 and therefore contains Claim 3.6, further fixes
`A ⊂ ℤ`.  Configurations are elements of `R[[X^{±1}]]`, i.e. `ℤ² → R`, **not** `ℤ² → A`;
Colle warns explicitly (line 166) that the summands `ηᵢ` of a periodic decomposition "may be
defined on infinite alphabets".  So the ambient type is `Config ℤ`, and `A` is only a finite
*subset* of `ℤ` constraining the original `η`.  That is why this file works over `Config ℤ`.

## Contents

* Part 1 — periods transport along any alphabet map and *reflect* along one injective on
  the range.  The tree had only the one-way `Nivat/Defs/Config.lean:85` `mem_Per_comp`;
  the converse existed twice but only as a local `have` inside a proof
  (`Nivat/Section8/Main.lean:60`, `Nivat/Section8/External.lean:485`).
* Part 2 — a prime `p` for which reduction is injective on a finite integer alphabet.
* Part 3 — `reduceMod`, additive (it is a ring hom applied pointwise) and, for a good `p`,
  period-faithful in *both* directions.  The reflection direction is the one Colle needs
  and does not justify: he derives periodicity of `T^u η` over `ℤ_p` and calls it a
  contradiction with the non-periodicity of the *integer-valued* `η`.
* Part 4 — the annihilator: `ψ = ∏_{i ≠ i_m}(X^{hᵢ} - 1)` annihilates
  `reduceMod p η - reduceMod p (ηs i_m)` over `ZMod p`.  This is exactly the hypothesis
  Lemma 2.5 consumes, and `exists_prime_colle_reduction` takes exactly the data
  `claim36` already has (at `A = ℤ`) and produces it.
* Part 5 — degeneracy guard: satisfiability and refutation witnesses.
* Part 6 — **the obstruction.**  The reduction cannot be built at `claim36`'s
  `[AddCommMonoid A]` generality, and not even at `[AddCommGroup A]` generality.
* Part 7 — **and why that matters less than Part 6 first claimed.**  Lemma 2.5's
  `[NoZeroDivisors R]` is avoidable: unit vertex coefficients suffice, over any `CommRing`.

## The obstruction, stated precisely

`not_injective_addMonoidHom_zmodFour`: the finite alphabet `ZMod 4` — a legitimate
`AddCommMonoid`, indeed an `AddCommGroup` — admits **no** injective additive map into **any**
`CommRing` with `NoZeroDivisors`.  Since `claim36` quantifies over all `[AddCommMonoid A]`,
and since transporting the decomposition `η = η₁ + ⋯ + η_m` requires the alphabet map to
respect `+`, no mod-`p` reduction can exist at that generality.
`exists_injective_not_additive` shows the gap is real rather than an artefact of demanding
a bundled hom: injections `ZMod 4 → ZMod 5` do exist, and by the theorem above none of them
is additive.

**Scope of the obstruction — and the way around it.**  The obstruction is a fact about the
**current statement** of `isGeneratingSet_of_annihilator`, not a mathematical obstruction.
The first version of this file presented it as the latter; an adversarial audit refuted
that, and Part 7 below now proves the audit right.  `Generating.lean` uses
`[NoZeroDivisors R]` in exactly one step — cancelling the vertex coefficient from
`p.coeff a * (x a - y a) = 0` — and that step needs only `IsUnit (p.coeff a)`.  Every factor
`X^{hᵢ} - 1` of Colle's `ψ` has coefficient `1` at `hᵢ` (`coeff_mono_sub_one_self`), a unit
in any ring.  So `isGeneratingSet_of_unit_coeff` (Part 7) applies over any `CommRing`,
including non-domains such as `ZMod 4`.

Two things the obstruction still does rule out: a reduction that is additive *and* injective
into a domain (impossible for `A = ZMod 4`), and a non-injective one (which cannot reflect
periodicity — see `reduceMod_two_spike_Per_ne`).  It does not rule out that some non-additive
injection might accidentally land `ι ∘ η` in the kernel of an unrelated Laurent polynomial;
no such route is known to the author of this file and none is attempted here.

**Two options for the lead; the choice is the lead's, not taken here.**

1. *Generalise Lemma 2.5.*  Move `isGeneratingSet_of_unit_coeff` (Part 7, proved, no
   `sorry`) into `Generating.lean`, then prove that every vertex of `Conv (supp ψ)` for
   `ψ = ∏(X^{hᵢ} - 1)` carries coefficient `±1` — true because `Newt ψ` is a zonotope and
   each vertex has a unique representation as a subset sum, but **待跑**: not proved here,
   and `Claim36.lean`'s docstring records that the lattice-level Minkowski rule needed for
   it is absent from the tree.  This keeps `claim36` at `[AddCommGroup A]` and is the
   larger theorem.
2. *Narrow the alphabet.*  Replace `{η : Config A} [AddCommMonoid A]` in `claim36` and
   `periodic_of_agree_on_strip` by `{η : Config ℤ}` plus
   `(hfin : (Set.range η).Finite)` — Colle's actual hypothesis `A ⊂ ℤ` finite.  Then
   `exists_prime_colle_reduction` closes the alphabet half immediately.  This is cheaper and
   strictly weaker, since narrowing the alphabet narrows the theorem.

## Note on duplication

`reduceMod` is definitionally the existing `Nivat/Section8/External.lean:435`
`def modP (p : ℕ) (ξ : Config ℤ) : Config (ZMod p) := fun z => (ξ z : ZMod p)`.
It is restated rather than imported because `Nivat/Section8/External.lean` pulls in
`Nivat.AppendixD` and the whole `Nivat.External.KS*` chain, which a Colle-layer file should
not depend on.  The clean fix is to lift `modP` into `Nivat/Defs/`; that edit is outside this
file's remit.  Likewise `act_prod_eq_zero_of_mem_Per` restates
`Nivat/External/Colle/Claim36.lean:207`, which cannot be imported here because `Claim36.lean`
is the intended *consumer* of this file.

## Status

No `sorry`, no `axiom`.
-/

namespace Nivat.Colle.AlphabetReduction

open Nivat

/-! ## Part 1: periods transport along alphabet maps, and reflect along injective ones -/

/-- If `ι` is injective on the values actually taken by `f`, then every period of the
recoloured configuration `ι ∘ f` is already a period of `f`. -/
theorem mem_Per_comp_of_injOn {α β : Type*} {ι : α → β} {f : Config α}
    (h : Set.InjOn ι (Set.range f)) {u : ℤ × ℤ} (hu : u ∈ Per (fun z => ι (f z))) :
    u ∈ Per f := by
  rw [mem_Per_iff]
  funext z
  exact h ⟨z + u, rfl⟩ ⟨z, rfl⟩ (congrFun hu z)

/-- Recolouring by a map injective on the range preserves the period group exactly.
The `≥` direction is `Nivat/Defs/Config.lean:85` `mem_Per_comp` and needs no hypothesis;
the `≤` direction is where injectivity is load-bearing (see
`reduceMod_two_spike_Per_ne` for a refutation without it). -/
theorem Per_comp_of_injOn {α β : Type*} {ι : α → β} {f : Config α}
    (h : Set.InjOn ι (Set.range f)) :
    Per (fun z => ι (f z)) = Per f := by
  ext u
  exact ⟨mem_Per_comp_of_injOn h, fun hu => mem_Per_comp hu ι⟩

theorem isPeriodic_comp_iff {α β : Type*} {ι : α → β} {f : Config α}
    (h : Set.InjOn ι (Set.range f)) :
    IsPeriodic (fun z => ι (f z)) ↔ IsPeriodic f := by
  constructor
  · rintro ⟨u, hu, hu0⟩; exact ⟨u, (Per_comp_of_injOn h) ▸ hu, hu0⟩
  · rintro ⟨u, hu, hu0⟩; exact ⟨u, (Per_comp_of_injOn h) ▸ hu, hu0⟩

/-! ## Part 2: choosing the prime

Colle's "let `p` be a prime number such that `A ⊂ ℤ_p`" with the missing condition supplied:
`p` must exceed the diameter of the finite alphabet, which is possible because there are
infinitely many primes. -/

theorem exists_prime_injOn_intCast {S : Set ℤ} (hS : S.Finite) :
    ∃ p : ℕ, p.Prime ∧ Set.InjOn (fun a : ℤ => (a : ZMod p)) S := by
  classical
  set F : Finset ℤ := hS.toFinset with hF
  set B : ℕ := F.sup Int.natAbs with hB
  obtain ⟨p, hpge, hp⟩ := Nat.exists_infinite_primes (2 * B + 1)
  refine ⟨p, hp, ?_⟩
  intro a ha b hb hab
  have hbd : ∀ c ∈ S, c.natAbs ≤ B := by
    intro c hc
    exact Finset.le_sup (f := Int.natAbs) (hS.mem_toFinset.mpr hc)
  have hdvd : (p : ℤ) ∣ b - a := Int.ModEq.dvd ((ZMod.intCast_eq_intCast_iff a b p).mp hab)
  have hlt : (b - a).natAbs < p := by
    have h1 := hbd a ha
    have h2 := hbd b hb
    have : (b - a).natAbs ≤ b.natAbs + a.natAbs := by
      simpa using Int.natAbs_sub_le b a
    omega
  have hdvd' : p ∣ (b - a).natAbs := by
    have := Int.natAbs_dvd_natAbs.mpr hdvd
    simpa using this
  have hz : (b - a).natAbs = 0 := by
    by_contra hne
    exact absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hdvd') (by omega)
  have : b - a = 0 := Int.natAbs_eq_zero.mp hz
  omega

/-! ## Part 3: the reduction map -/

/-- Colle's `η ↦ η mod p`.  Definitionally `Nivat/Section8/External.lean:435` `modP`; see the
module docstring for why it is restated rather than imported. -/
def reduceMod (p : ℕ) (η : Config ℤ) : Config (ZMod p) := fun z => ((η z : ℤ) : ZMod p)

@[simp] theorem reduceMod_apply (p : ℕ) (η : Config ℤ) (z : ℤ × ℤ) :
    reduceMod p η z = ((η z : ℤ) : ZMod p) := rfl

/-- Additivity is free: `reduceMod` is the ring homomorphism `ℤ → ZMod p` applied pointwise.
This is precisely what an arbitrary alphabet injection does *not* give (Part 6). -/
theorem reduceMod_add (p : ℕ) (η₁ η₂ : Config ℤ) :
    reduceMod p (fun z => η₁ z + η₂ z) = fun z => reduceMod p η₁ z + reduceMod p η₂ z := by
  funext z; simp

/-- Colle's "consider the `ℤ_p`-periodic decomposition `η = η̄₁ + ⋯ + η̄_m`". -/
theorem reduceMod_sum {ι : Type*} (p : ℕ) (s : Finset ι) (f : ι → Config ℤ) :
    reduceMod p (fun z => ∑ i ∈ s, f i z) = fun z => ∑ i ∈ s, reduceMod p (f i) z := by
  funext z
  simp only [reduceMod]
  exact map_sum (Int.castRingHom (ZMod p)) (fun i => f i z) s

theorem mem_Per_reduceMod (p : ℕ) {η : Config ℤ} {u : ℤ × ℤ} (hu : u ∈ Per η) :
    u ∈ Per (reduceMod p η) := mem_Per_comp hu _

theorem Per_reduceMod_eq_of_injOn (p : ℕ) {η : Config ℤ}
    (h : Set.InjOn (fun a : ℤ => (a : ZMod p)) (Set.range η)) :
    Per (reduceMod p η) = Per η := Per_comp_of_injOn h

/-- A finite integer alphabet admits a faithful reduction.  The `≤` half of the conclusion
is the step Colle needs to contradict non-periodicity of the integer-valued `η`, and which
he does not justify. -/
theorem exists_prime_reduceMod {η : Config ℤ} (hfin : (Set.range η).Finite) :
    ∃ p : ℕ, p.Prime ∧ Per (reduceMod p η) = Per η := by
  obtain ⟨p, hp, hinj⟩ := exists_prime_injOn_intCast hfin
  exact ⟨p, hp, Per_reduceMod_eq_of_injOn p hinj⟩

/-! ## Part 4: the annihilator produced by the reduction -/

private theorem act_sum_right {R : Type*} [CommRing R] {ι : Type*} (s : Finset ι)
    (f : LaurentTwo R) (gs : ι → Config R) :
    act f (∑ i ∈ s, gs i) = ∑ i ∈ s, act f (gs i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, act_add_right, ih, Finset.sum_insert ha]

/-- Restatement of `Nivat/External/Colle/Claim36.lean:207` (which cannot be imported here,
since `Claim36.lean` is the intended consumer of this file). -/
theorem act_prod_eq_zero_of_mem_Per {R : Type*} [CommRing R] {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (H : ι → ℤ × ℤ) (gs : ι → Config R)
    (hper : ∀ i ∈ s, H i ∈ Per (gs i)) :
    act (∏ i ∈ s, (mono (H i) - 1 : LaurentTwo R)) (∑ i ∈ s, gs i) = 0 := by
  classical
  rw [act_sum_right]
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [← Finset.prod_erase_mul s _ hi, act_mul,
    (act_mono_sub_one_eq_zero_iff (H i) (gs i)).mpr (hper i hi), act_zero_right]

/-- The annihilator half of `exists_prime_colle_reduction`, on its own and for **every**
`p` — no primality, no finiteness.  The file docstring (`:60-63`) already records that this
half holds for every `p` including `p = 0`; this is that sentence as a declaration.

Used by `exists_prime_colle_reduction` below and by `isGeneratingSet_psi_at_prime`
(Part 8), which is what turns it into Colle's Lemma 2.5 conclusion. -/
theorem act_psi_reduceMod_eq_zero {m : ℕ} (p : ℕ) {η : Config ℤ} {ηs : Fin m → Config ℤ}
    (hdecomp : ∀ z, η z = ∑ i, ηs i z)
    {h : Fin m → ℤ × ℤ} (hper : ∀ i, h i ∈ Per (ηs i)) (i_m : Fin m) :
    act (∏ i ∈ Finset.univ.erase i_m, (mono (h i) - 1 : LaurentTwo (ZMod p)))
        (reduceMod p η - reduceMod p (ηs i_m)) = 0 := by
  classical
  have hsplit : reduceMod p η - reduceMod p (ηs i_m)
      = ∑ i ∈ Finset.univ.erase i_m, reduceMod p (ηs i) := by
    funext z
    have hz : ((η z : ℤ) : ZMod p) = ∑ i, ((ηs i z : ℤ) : ZMod p) := by
      rw [hdecomp z]
      exact map_sum (Int.castRingHom (ZMod p)) (fun i => ηs i z) Finset.univ
    have hsum := Finset.sum_erase_add (Finset.univ : Finset (Fin m))
      (fun i => ((ηs i z : ℤ) : ZMod p)) (Finset.mem_univ i_m)
    simp only [Pi.sub_apply, reduceMod_apply, Finset.sum_apply, hz]
    rw [← hsum]
    ring
  rw [hsplit]
  exact act_prod_eq_zero_of_mem_Per _ h (fun i => reduceMod p (ηs i))
    (fun i _ => mem_Per_reduceMod p (hper i))

/-- **The bridge.**  From exactly the data `claim36` already carries — a pointwise periodic
decomposition (`IsMinimalPeriodicDecomp`'s first clause, `Lemma45.lean:50`) and periods
`hᵢ ∈ Per (ηs i)` (`claim36`'s `hh_per`) — with the alphabet finite and integer-valued,
this produces both halves of Colle's sentence:

* `Per (reduceMod p η) = Per η`, so periodicity over `ZMod p` lifts back to `ℤ`;
* `ψ = ∏_{i ≠ i_m}(X^{hᵢ} - 1) ∈ ann_{ZMod p}(η - η̄_{i_m})`, the exact hypothesis of
  Lemma 2.5 (`isGeneratingSet_of_annihilator`), now over a domain. -/
theorem exists_prime_colle_reduction {m : ℕ} {η : Config ℤ} {ηs : Fin m → Config ℤ}
    (hfin : (Set.range η).Finite)
    (hdecomp : ∀ z, η z = ∑ i, ηs i z)
    {h : Fin m → ℤ × ℤ} (hper : ∀ i, h i ∈ Per (ηs i)) (i_m : Fin m) :
    ∃ p : ℕ, p.Prime ∧
      Per (reduceMod p η) = Per η ∧
      act (∏ i ∈ Finset.univ.erase i_m, (mono (h i) - 1 : LaurentTwo (ZMod p)))
          (reduceMod p η - reduceMod p (ηs i_m)) = 0 := by
  obtain ⟨p, hp, hPer⟩ := exists_prime_reduceMod hfin
  exact ⟨p, hp, hPer, act_psi_reduceMod_eq_zero p hdecomp hper i_m⟩

/-- Lemma 2.5 does apply to the reduced configuration: `ZMod p` is a domain for `p` prime.
Pure instantiation of `isGeneratingSet_of_annihilator`; recorded to show the chain closes. -/
theorem isGeneratingSet_reduceMod {p : ℕ} [Fact p.Prime]
    {ξ : Config (ZMod p)} {ψ : LaurentTwo (ZMod p)} (hann : act ψ ξ = 0)
    {S : Finset (ℤ × ℤ)} (hne : S.Nonempty) (hconv : LatticeConvex S)
    (hS : supp ψ ⊆ S) (hhull : Conv S = Conv (supp ψ)) :
    IsGeneratingSet ξ S :=
  isGeneratingSet_of_annihilator hann hne hconv hS hhull

/-! ## Part 5: degeneracy guard

Every statement above is checked against the project's recurring failure mode: a definition
or hypothesis that is vacuously true for everything, or true for nothing. -/

/-- A non-periodic integer configuration with finite range: value `2` at the origin, `0`
elsewhere. -/
def spike : Config ℤ := fun z => if z = 0 then 2 else 0

theorem spike_range_finite : (Set.range spike).Finite := by
  refine Set.Finite.subset (Set.toFinite ({0, 2} : Set ℤ)) ?_
  rintro _ ⟨z, rfl⟩
  by_cases hz : z = 0 <;> simp [spike, hz]

theorem spike_not_mem_Per : ((1, 0) : ℤ × ℤ) ∉ Per spike := by
  intro hu
  have := Per.apply hu 0
  simp [spike] at this

theorem spike_isPeriodic_false : ¬ IsPeriodic spike := by
  rintro ⟨u, hu, hu0⟩
  have := Per.apply hu 0
  simp only [spike, zero_add, if_neg hu0] at this
  exact absurd this (by norm_num)

/-- **Refutation.**  The prime supplied by `exists_prime_reduceMod` is not decoration and
the injectivity hypothesis of `Per_comp_of_injOn` is not decoration: at `p = 2` the
reduction merges the alphabet `{0, 2}` and `Per` strictly grows, so the conclusion
`Per (reduceMod p η) = Per η` is false for a badly chosen `p`. -/
theorem reduceMod_two_spike_Per_ne : Per (reduceMod 2 spike) ≠ Per spike := by
  intro hEq
  apply spike_not_mem_Per
  rw [← hEq, mem_Per_iff]
  funext z
  have hval : ∀ w : ℤ × ℤ, ((spike w : ℤ) : ZMod 2) = 0 := by
    intro w
    by_cases hw : w = 0
    · simp only [spike, if_pos hw]
      decide
    · simp [spike, hw]
  show ((spike (z + (1, 0)) : ℤ) : ZMod 2) = ((spike z : ℤ) : ZMod 2)
  rw [hval, hval]

/-- A genuinely periodic finite-range integer configuration: the vertical stripes
`z ↦ z.1 mod 2`. -/
def stripe : Config ℤ := fun z => z.1 % 2

theorem stripe_range_finite : (Set.range stripe).Finite := by
  refine Set.Finite.subset (Set.toFinite ({0, 1} : Set ℤ)) ?_
  rintro _ ⟨z, rfl⟩
  have h1 : 0 ≤ z.1 % 2 := Int.emod_nonneg z.1 (by norm_num)
  have h2 : z.1 % 2 < 2 := Int.emod_lt_of_pos z.1 (by norm_num)
  simp only [stripe, Set.mem_insert_iff, Set.mem_singleton_iff]
  omega

theorem stripe_period : ((2, 0) : ℤ × ℤ) ∈ Per stripe := by
  rw [mem_Per_iff]
  funext z
  show (z + (2, 0)).1 % 2 = z.1 % 2
  simp only [Prod.fst_add]
  omega

/-- **Satisfiability.**  The hypotheses of the Part 3–4 theorems are satisfiable by a
configuration with a *non-zero* period, so those theorems are not vacuous. -/
theorem colle_reduction_nonvacuous :
    ∃ p : ℕ, p.Prime ∧ Per (reduceMod p stripe) = Per stripe ∧
      ((2, 0) : ℤ × ℤ) ∈ Per stripe ∧ ((2, 0) : ℤ × ℤ) ≠ 0 :=
  let ⟨p, hp, hPer⟩ := exists_prime_reduceMod stripe_range_finite
  ⟨p, hp, hPer, stripe_period, by decide⟩

/-! ## Part 6: the obstruction at `AddCommMonoid` generality -/

/-- **The obstruction.**  `ZMod 4` is a legitimate finite alphabet carrying `AddCommMonoid`
(indeed `AddCommGroup`), yet it admits **no** injective additive map into **any** commutative
ring without zero divisors.

Proof: if `ι` were injective then `y := ι 2 ≠ ι 0 = 0`, while `y + y = ι (2 + 2) = ι 0 = 0`,
i.e. `(2 : R) * y = 0`.  In a domain that forces `(2 : R) = 0`, whence
`y = (2 : R) * ι 1 = 0`, contradiction.

Consequence: since `isGeneratingSet_of_annihilator` (Lemma 2.5) **as currently stated**
requires the alphabet to *be* a `CommRing` with `NoZeroDivisors`, and since transporting a
periodic decomposition `η = η₁ + ⋯ + η_m` requires the alphabet map to respect `+`, no
mod-`p` reduction — indeed no reduction into any domain — exists at `claim36`'s
`[AddCommMonoid A]` generality, nor at `[AddCommGroup A]` generality.

**But read Part 7 before acting on this.**  The `NoZeroDivisors` requirement is itself
avoidable (`isGeneratingSet_of_unit_coeff`), so what this theorem establishes is a limit of
the tree's current Lemma 2.5, not a limit of the mathematics.  The first version of this
file claimed the latter; that claim was wrong and is corrected rather than deleted. -/
theorem not_injective_addMonoidHom_zmodFour {R : Type*} [CommRing R] [NoZeroDivisors R]
    (ι : ZMod 4 →+ R) : ¬ Function.Injective ι := by
  intro hinj
  have hy0 : ι 2 ≠ 0 := by
    intro hc
    have h20 : (2 : ZMod 4) = 0 := hinj (by rw [hc, map_zero])
    exact absurd h20 (by decide)
  have hsum : ι 2 + ι 2 = 0 := by
    rw [← map_add, show (2 : ZMod 4) + 2 = 0 from by decide, map_zero]
  have h2 : (2 : R) * ι 2 = 0 := by rw [two_mul]; exact hsum
  rcases mul_eq_zero.mp h2 with h2r | hcon
  · refine hy0 ?_
    have hrw : ι 2 = (2 : R) * ι 1 := by
      rw [show (2 : ZMod 4) = 1 + 1 from by decide, map_add, two_mul]
    rw [hrw, h2r, zero_mul]
  · exact hy0 hcon

/-- Specialisation to the paper's target `ℤ_p`: for no prime `p` whatsoever does the
alphabet `ZMod 4` embed additively into `ZMod p`. -/
theorem not_injective_addMonoidHom_zmodFour_zmodPrime {p : ℕ} (hp : p.Prime)
    (ι : ZMod 4 →+ ZMod p) : ¬ Function.Injective ι := by
  have : Fact p.Prime := Fact.mk hp
  exact not_injective_addMonoidHom_zmodFour ι

/-- The gap is not an artefact of demanding a bundled hom.  Injections `ZMod 4 → ZMod 5`
do exist — here `a ↦ a.val` — and by `not_injective_addMonoidHom_zmodFour` none of them
is additive.  So "embed the alphabet in `ZMod p` for `p > |A|`" is available, and useless:
it transports `Per` (Part 1) but not `+`, hence not the periodic decomposition and not the
annihilator. -/
theorem exists_injective_not_additive :
    ∃ e : ZMod 4 → ZMod 5, Function.Injective e ∧ ¬ (∀ a b, e (a + b) = e a + e b) := by
  refine ⟨fun a => (a.val : ZMod 5), by decide, ?_⟩
  intro hadd
  have := hadd 2 2
  revert this
  decide

/-! ## Part 7: the `NoZeroDivisors` hypothesis of Lemma 2.5 is avoidable

Added after an adversarial audit of Parts 1–6 pointed out that Part 6's obstruction is a
fact about the *current statement* of `isGeneratingSet_of_annihilator` rather than a
mathematical obstruction.  The audit's objection is correct and is recorded here with a
proof rather than being argued away.

`Nivat/External/Colle/Generating.lean` uses `[NoZeroDivisors R]` in exactly one place: the
final step of `eq_at_of_annihilator_of_agree_off_support`, which cancels the vertex
coefficient `p.coeff a` from `p.coeff a * (x a - y a) = 0`.  Cancellation needs only that
`p.coeff a` be a **unit**, which holds over an arbitrary `CommRing`.  The three lemmas below
are the `NoZeroDivisors`-free replacements. -/

theorem eq_at_of_annihilator_of_unit_coeff {R : Type*} [CommRing R]
    {p : LaurentTwo R} {x y : Config R} {a : ℤ × ℤ}
    (ha : a ∈ supp p) (hu : IsUnit (p.coeff a)) (hx : act p x = 0) (hy : act p y = 0)
    (hagree : ∀ z ∈ (supp p).erase a, x z = y z) : x a = y a := by
  classical
  have hxy : act p (x - y) = 0 := by rw [act_sub_right, hx, hy, sub_self]
  have hsum : (∑ z ∈ supp p, p.coeff z * (x z - y z)) = 0 := by
    have h := congrFun hxy (0 : ℤ × ℤ)
    simpa only [act_apply, Finsupp.sum, zero_add, Pi.sub_apply, Pi.zero_apply, supp] using h
  have hrest : (∑ z ∈ (supp p).erase a, p.coeff z * (x z - y z)) = 0 := by
    apply Finset.sum_eq_zero
    intro z hz
    rw [hagree z hz, sub_self, mul_zero]
  rw [← Finset.sum_erase_add _ _ ha, hrest, zero_add] at hsum
  exact sub_eq_zero.mp (hu.mul_right_eq_zero.mp hsum)

theorem generatesAt_of_unit_coeff {R : Type*} [CommRing R]
    {ξ : Config R} {p : LaurentTwo R} (hann : act p ξ = 0)
    {S : Finset (ℤ × ℤ)} (hS : supp p ⊆ S) {a : ℤ × ℤ} (ha : a ∈ supp p)
    (hu : IsUnit (p.coeff a)) :
    GeneratesAt ξ S a := by
  refine ⟨hS ha, ?_⟩
  intro x hx y hy hagree
  apply eq_at_of_annihilator_of_unit_coeff ha hu
    (act_eq_zero_on_orbitClosure hann hx) (act_eq_zero_on_orbitClosure hann hy)
  intro z hz
  exact hagree z (Finset.mem_erase.mpr
    ⟨(Finset.mem_erase.mp hz).1, hS (Finset.mem_erase.mp hz).2⟩)

/-- **Lemma 2.5 without `NoZeroDivisors`.**  Compare
`Nivat/External/Colle/Generating.lean` `isGeneratingSet_of_annihilator`, which is the same
statement with `[NoZeroDivisors R]` in place of the `hunit` hypothesis.  Neither implies the
other, and neither is a weakening: this version drops a typeclass and adds a hypothesis on
the vertex coefficients only. -/
theorem isGeneratingSet_of_unit_coeff {R : Type*} [CommRing R]
    {ξ : Config R} {p : LaurentTwo R} (hann : act p ξ = 0)
    {S : Finset (ℤ × ℤ)} (hne : S.Nonempty) (hconv : LatticeConvex S)
    (hS : supp p ⊆ S) (hhull : Conv S = Conv (supp p))
    (hunit : ∀ a ∈ supp p, IsUnit (p.coeff a)) :
    IsGeneratingSet ξ S := by
  refine ⟨hne, hconv, ?_⟩
  intro a ha hdel
  have hap : a ∈ supp p := by
    by_contra hn
    have hsub : supp p ⊆ S.erase a := by
      intro z hz
      refine Finset.mem_erase.mpr ⟨?_, hS hz⟩
      intro hza
      exact hn (hza ▸ hz)
    have hconvsub : Conv (supp p) ⊆ Conv (S.erase a) :=
      convexHull_mono (Set.image_mono hsub)
    have haHull : toReal a ∈ Conv (supp p) := by
      rw [← hhull]
      exact subset_Conv ha
    exact Finset.notMem_erase a S (hdel a (hconvsub haHull))
  exact generatesAt_of_unit_coeff hann hS hap (hunit a hap)

/-- The bypass is not vacuous: `ZMod 4` is a `CommRing` that is *not* a domain, so
`isGeneratingSet_of_annihilator` does not apply over it — but each factor `X^u - 1` of
Colle's `ψ` has coefficient `1` at `u`, a unit in any ring, so
`isGeneratingSet_of_unit_coeff` does. -/
theorem zmodFour_not_noZeroDivisors : ∃ a b : ZMod 4, a ≠ 0 ∧ b ≠ 0 ∧ a * b = 0 :=
  ⟨2, 2, by decide, by decide, by decide⟩

theorem coeff_mono_sub_one_self {R : Type*} [CommRing R] {u : ℤ × ℤ} (hu : u ≠ 0) :
    (mono u - 1 : LaurentTwo R).coeff u = 1 := by
  rw [← mono_zero]
  simp only [mono, AddMonoidAlgebra.coeff_sub, AddMonoidAlgebra.coeff_single,
    Finsupp.coe_sub, Pi.sub_apply, Finsupp.single_apply]
  simp [Ne.symm hu]

theorem coeff_mono_sub_one_isUnit {R : Type*} [CommRing R] {u : ℤ × ℤ} (hu : u ≠ 0) :
    IsUnit ((mono u - 1 : LaurentTwo R).coeff u) := by
  rw [coeff_mono_sub_one_self hu]
  exact isUnit_one

/-! ## Part 8: Lemma 2.5 for `η − η̄_{ι₀}` (`b3_colle2.txt:792`)

`b3_colle2.txt:792` says `𝒮_{φ_ι}` is an **`η − η̄_{ι₀}`-generating set**, citing Lemma 2.5.
`blueprint/OPEN.md #15` records that our Case-1 sweep composer currently uses one set for
both the generating set and the sweep window, and that these are two different sets in the
source.  Part 4 already produced the annihilator half; this part turns it into the
`IsGeneratingSet` conclusion.

**Quantifier correspondence with `:792`.**  "`𝒮_{φ_ι}` is an `η − η̄_{ι₀}`-generating set"
— `S_ψ` is `𝒮_{φ_ι}`, `reduceMod p η - reduceMod p (ηs i_m)` is `η − η̄_{ι₀}` after the
alphabet change of `:788` (which `:788` performs precisely so that the summands land in a
finite alphabet), and `IsGeneratingSet` (`Generating.lean:58`) is Colle's generating-set
notion.  `ι₀` is `i_m`; `φ_ι(X) = ∏_{i≠ι₀}(X^{h_i} − 1)` is the product below.

**⚠ The `ℤ` vs `ZMod p` hull mismatch — answered, not papered over.**  The producer on the
chain is `Claim36.generatingSet_no_edge_parallel` (`Claim36.lean:741`), whose `hS_hull` is
stated over `LaurentTwo ℤ`; the consumer `isGeneratingSet_of_annihilator`
(`Generating.lean:65`) needs it over `LaurentTwo (ZMod p)`.  **These are not the same
statement**, and the two halves behave differently:

* the **support inclusion transfers for free, in one direction**:
  `supp ψ_{ZMod p} ⊆ supp ψ_ℤ` always (`supp_psi_mod_subset`, below), because coefficient
  reduction can kill a coefficient but never create one.  So `hS` over `ℤ` implies `hS`
  over `ZMod p`, and a producer need only supply the `ℤ` form.
* the **hull equality does not transfer for free**.  `Conv S_ψ = Conv (supp ψ_ℤ)` gives
  `Conv (supp ψ_{ZMod p}) ⊆ Conv S_ψ` by the inclusion above, but the reverse needs that
  reduction kills no **vertex**.  That is true — a vertex of the zonotope
  `Conv (supp ∏(X^{h_i} − 1))` is reached by a unique subset sum, so its coefficient is
  `±1` and survives in any `ZMod p` — but the vertex-coefficient statement is **not on the
  chain**, so it is not asserted here.  This is a 读法, not a kernel fact; see (c) of the
  report and `OPEN.md #15`.

Consequently both `hS` and `hhull` are taken as binders below, at the ring where they are
used, and nothing silently picks one.

The annihilator input, `act_psi_reduceMod_eq_zero`, lives in Part 4 (it is the half of
`exists_prime_colle_reduction` that needs neither primality nor finiteness). -/

/-- `φ_ι` over `ZMod p` is the coefficient reduction of `φ_ι` over `ℤ`. -/
theorem psi_mod_eq_map (p : ℕ) {ι : Type*} (s : Finset ι) (h : ι → ℤ × ℤ) :
    (∏ i ∈ s, (mono (h i) - 1 : LaurentTwo (ZMod p)))
      = AddMonoidAlgebra.mapRingHom (ℤ × ℤ) (Int.castRingHom (ZMod p))
          (∏ i ∈ s, (mono (h i) - 1 : LaurentTwo ℤ)) := by
  rw [map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_sub, map_one]
  congr 1
  simp [mono]

/-- **The free direction of the `ℤ` / `ZMod p` mismatch.**  Reduction can kill a coefficient
but never create one, so the mod-`p` support is contained in the integer support.  Hence a
producer that establishes `supp ψ_ℤ ⊆ S_ψ` — the form `Claim36.lean` uses — has already
established the mod-`p` form needed by `isGeneratingSet_of_annihilator`.

The companion hull *equality* does **not** follow this way; see the Part 8 docstring. -/
theorem supp_psi_mod_subset (p : ℕ) {ι : Type*} (s : Finset ι) (h : ι → ℤ × ℤ) :
    supp (∏ i ∈ s, (mono (h i) - 1 : LaurentTwo (ZMod p)))
      ⊆ supp (∏ i ∈ s, (mono (h i) - 1 : LaurentTwo ℤ)) := by
  intro a ha
  rw [psi_mod_eq_map p s h] at ha
  simp only [supp, Finsupp.mem_support_iff, AddMonoidAlgebra.coeff_mapRingHom] at ha ⊢
  intro hz
  exact ha (by rw [hz]; simp)

/-- Two **equal** shifts — the degenerate case that separates the two rings.  `hh_dir` of
`Claim36.generatingSet_no_edge_parallel` forbids this at the intended instance; see the
scope note on `supp_psi_mod_ne_witness`. -/
noncomputable def twoEqualShifts : Fin 2 → ℤ × ℤ := fun _ => ((1 : ℤ), (0 : ℤ))

private theorem prod_twoEqualShifts (R : Type*) [CommRing R] :
    (∏ i ∈ (Finset.univ : Finset (Fin 2)), (mono (twoEqualShifts i) - 1 : LaurentTwo R))
      = mono ((2 : ℤ), (0 : ℤ)) - mono ((1 : ℤ), (0 : ℤ)) - mono ((1 : ℤ), (0 : ℤ)) + 1 := by
  rw [Fin.prod_univ_two]
  have hexp : (mono (twoEqualShifts 0) - 1 : LaurentTwo R) * (mono (twoEqualShifts 1) - 1)
      = mono (twoEqualShifts 0) * mono (twoEqualShifts 1)
        - mono (twoEqualShifts 0) - mono (twoEqualShifts 1) + 1 := by ring
  rw [hexp, mono_mul_mono]
  norm_num [twoEqualShifts]

private theorem coeff_prod_twoEqualShifts (R : Type*) [CommRing R] :
    (∏ i ∈ (Finset.univ : Finset (Fin 2)),
      (mono (twoEqualShifts i) - 1 : LaurentTwo R)).coeff ((1 : ℤ), (0 : ℤ)) = -2 := by
  rw [prod_twoEqualShifts R, ← mono_zero]
  simp only [mono, AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_sub,
    AddMonoidAlgebra.coeff_single]
  norm_num

/-- **The two hull conditions are not the same statement — a kernel witness, not prose.**

`ψ = (X^{(1,0)} − 1)²  =  X^{(2,0)} − 2·X^{(1,0)} + 1` has middle coefficient `−2`, which is
nonzero in `ℤ` and zero in `ZMod 2`.  So `(1,0)` lies in the integer support and not in the
mod-`2` support, and `supp ψ_ℤ ≠ supp ψ_{ZMod 2}`.  Together with `supp_psi_mod_subset`
(which gives `⊆` always) the inclusion is therefore **strict** here.

⚠ **Scope, stated because it matters** (hard rule 10).  This witness uses two *equal*
exponents, and `hh_dir` of `Claim36.generatingSet_no_edge_parallel` (`Claim36.lean:743`)
forbids that at the intended instance.  So this settles "the `ℤ` and `ZMod p` forms of `hS`
and `hhull` are different statements" **in general**; it does **not** settle whether they
differ at the intended instance, where the exponents are pairwise non-parallel.  That
remains open — pairwise non-parallel exponents can still have colliding subset sums (for
example `(1,0) + (0,1) = (2,−1) + (−1,2)`, all six pairwise determinants nonzero), which is
what produces a coefficient `±2`.  Not asserted here, and not asserted anywhere on the
chain. -/
theorem supp_psi_mod_ne_witness :
    ((1 : ℤ), (0 : ℤ)) ∈ supp (∏ i ∈ (Finset.univ : Finset (Fin 2)),
        (mono (twoEqualShifts i) - 1 : LaurentTwo ℤ)) ∧
      ((1 : ℤ), (0 : ℤ)) ∉ supp (∏ i ∈ (Finset.univ : Finset (Fin 2)),
        (mono (twoEqualShifts i) - 1 : LaurentTwo (ZMod 2))) := by
  constructor
  · simp only [supp, Finsupp.mem_support_iff]
    rw [coeff_prod_twoEqualShifts ℤ]
    norm_num
  · simp only [supp, Finsupp.mem_support_iff, not_not]
    rw [coeff_prod_twoEqualShifts (ZMod 2)]
    decide

/-- **Colle Lemma 2.5 for `η − η̄_{ι₀}` at a fixed prime** (`b3_colle2.txt:792`).
`𝒮_{φ_ι}` generates `η − η̄_{ι₀}` once it is a lattice-convex completion of the support of
`φ_ι = ∏_{i ≠ ι₀}(X^{h_i} − 1)` over `ZMod p`.  The annihilator hypothesis of
`isGeneratingSet_of_annihilator` is supplied by `act_psi_reduceMod_eq_zero`; the domain
hypothesis `NoZeroDivisors (ZMod p)` is supplied by `Fact.mk hp`.

Neither `hfin` nor `Per (reduceMod p η) = Per η` is needed here — those belong to the
*other* half of Colle's sentence (`exists_prime_reduceMod`), which is what the caller uses
to carry a period back to `ℤ`.  Keeping them out makes clear that this half is pure
Lemma 2.5. -/
theorem isGeneratingSet_psi_at_prime {m : ℕ} {p : ℕ} (hp : p.Prime)
    {η : Config ℤ} {ηs : Fin m → Config ℤ}
    (hdecomp : ∀ z, η z = ∑ i, ηs i z)
    {h : Fin m → ℤ × ℤ} (hper : ∀ i, h i ∈ Per (ηs i)) (i_m : Fin m)
    {S_ψ : Finset (ℤ × ℤ)} (hne : S_ψ.Nonempty) (hconv : LatticeConvex S_ψ)
    (hS : supp (∏ i ∈ Finset.univ.erase i_m, (mono (h i) - 1 : LaurentTwo ℤ)) ⊆ S_ψ)
    (hhull : Conv (↑S_ψ : Finset (ℤ × ℤ))
      = Conv (supp (∏ i ∈ Finset.univ.erase i_m,
          (mono (h i) - 1 : LaurentTwo (ZMod p))))) :
    IsGeneratingSet (reduceMod p η - reduceMod p (ηs i_m)) S_ψ := by
  classical
  have : Fact p.Prime := Fact.mk hp
  exact isGeneratingSet_of_annihilator
    (act_psi_reduceMod_eq_zero p hdecomp hper i_m) hne hconv
    ((supp_psi_mod_subset p _ h).trans hS) hhull

/-- **Colle Lemma 2.5 for `η − η̄_{ι₀}`, with the prime produced** (`b3_colle2.txt:788, 792`)
— Colle's sentence in full: change the alphabet, *then* read off the generating set.

⚠ **Why `hhull` is quantified over all primes.**  `p` is existentially bound, so a
hypothesis mentioning `ZMod p` cannot be stated before it is produced.  This is an artefact
of the existential, not a strengthening we chose: at a fixed `p` the honest form is
`isGeneratingSet_psi_at_prime`, and a producer that pins `p` should use that one.  The
`∀ q` form is implied by the `ℤ`-hull equality **plus** vertex survival under reduction,
which is not on the chain — see the Part 8 docstring.

`hS` is taken over `ℤ` in both statements, because `supp_psi_mod_subset` makes that
direction free. -/
theorem isGeneratingSet_psi_of_prime {m : ℕ} {η : Config ℤ} {ηs : Fin m → Config ℤ}
    (hfin : (Set.range η).Finite)
    (hdecomp : ∀ z, η z = ∑ i, ηs i z)
    {h : Fin m → ℤ × ℤ} (hper : ∀ i, h i ∈ Per (ηs i)) (i_m : Fin m)
    {S_ψ : Finset (ℤ × ℤ)} (hne : S_ψ.Nonempty) (hconv : LatticeConvex S_ψ)
    (hS : supp (∏ i ∈ Finset.univ.erase i_m, (mono (h i) - 1 : LaurentTwo ℤ)) ⊆ S_ψ)
    (hhull : ∀ q : ℕ, q.Prime → Conv (↑S_ψ : Finset (ℤ × ℤ))
      = Conv (supp (∏ i ∈ Finset.univ.erase i_m,
          (mono (h i) - 1 : LaurentTwo (ZMod q))))) :
    ∃ p : ℕ, p.Prime ∧ Per (reduceMod p η) = Per η ∧
      IsGeneratingSet (reduceMod p η - reduceMod p (ηs i_m)) S_ψ := by
  obtain ⟨p, hp, hPer⟩ := exists_prime_reduceMod hfin
  exact ⟨p, hp, hPer,
    isGeneratingSet_psi_at_prime hp hdecomp hper i_m hne hconv hS (hhull p hp)⟩

end Nivat.Colle.AlphabetReduction

#print axioms Nivat.Colle.AlphabetReduction.act_psi_reduceMod_eq_zero
#print axioms Nivat.Colle.AlphabetReduction.exists_prime_colle_reduction
#print axioms Nivat.Colle.AlphabetReduction.psi_mod_eq_map
#print axioms Nivat.Colle.AlphabetReduction.supp_psi_mod_subset
#print axioms Nivat.Colle.AlphabetReduction.isGeneratingSet_psi_at_prime
#print axioms Nivat.Colle.AlphabetReduction.isGeneratingSet_psi_of_prime

#print axioms Nivat.Colle.AlphabetReduction.supp_psi_mod_ne_witness
