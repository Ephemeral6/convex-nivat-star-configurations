/-
Copyright (c) 2026. Released under Apache 2.0 license.
Authors: lane-chaindata-lead
-/
import Nivat.External.Colle.MaximalEnveloped
import Nivat.External.Colle.Claim37

/-!
# `genFill ⊆ GenClosure`: the single-generator filtration weakens into the unrestricted one

Round 80 ruling (`LANDING.md`), step 1 of 3.

`fillCover` is kernel-refuted as stated (`FillCoverWitness.lean`): `ChainData.fill` is built on
`MaxEnv.genFill S gen X` (`MaximalEnveloped.lean:670`), a filtration that may only ever generate
at translates of the **one** distinguished point `gen`.  `FillCoverWitness.lean:161` vs `:204`
exhibits the same shell covered from `gen = (1,0)` and *not* covered from `gen = (0,0)` in the
same window — so `fillCover` is sensitive to a choice that the paper never makes.

`Colle37.GenClosure S D` (`Claim37.lean:288-291`) is the unrestricted alternative already in the
tree: its `step` generates at **every** `a ∈ S` with `LatticeConvex (S.erase a)`, not at a fixed
one, and `Colle37.agree_on_genClosure` (`:297-308`) — the only thing any consumer actually wants
out of the filtration — is already proved for it, in full, from `IsGeneratingSet`.

This file proves the weakening direction: anything the single-generator filtration reaches, the
unrestricted closure reaches too.  That is what lets a consumer phrased against `genFill` be
re-phrased against `GenClosure` without reproving its own induction.

## Why the two hypotheses are free at the real call site

`GenClosure.step` demands `ha : a ∈ S` and `hconv : LatticeConvex (S.erase a)`; `genFill`'s step
demands neither, because it never has to justify that generating at `gen` is legitimate — it just
declares it.  So the weakening cannot be hypothesis-free: `hgen`/`hconv` are exactly the debt
`genFill` silently carries.  At the chain's call site both are already present and neither is new
work: `gen := F.a'` and `FaceBlock.generatesAt_a'` carries the full `IsGeneratingSet` datum, whose
`a ∈ S` and `LatticeConvex (S.erase a)` components are precisely these.

Note the direction is one-way, and must be: `GenClosure ⊆ genFill` is FALSE for the same reason
`fillCover` is refuted — `GenClosure` may generate at `(0,0)` and at `(1,0)`, while
`genFill _ (1,0) _` may not generate at `(0,0)` at all.  `FillCoverWitness.lean:161/:204` is
already a kernel witness to that asymmetry; nothing below tries to invert it.
-/

set_option autoImplicit false

namespace Nivat.GenClosureWeaken

open Nivat Nivat.MaxEnv Nivat.Colle37

/-- **Step 1 of the Round 80 plan.**  Every site the single-generator filtration reaches at
stage `n` is forced by the unrestricted generating closure.

Induction on `n`.  The base case is `genFill_zero` (`genFill S gen X 0 = X`, `rfl`) against
`GenClosure.base`; the successor case is `genFill_step` against `GenClosure.step`, whose `a := gen`
and whose `w := t` are the very `t` that `genFill`'s step produces. -/
theorem genFill_subset_genClosure {S : Finset (ℤ × ℤ)} {gen : ℤ × ℤ} {X : Set (ℤ × ℤ)}
    (hgen : gen ∈ S) (hconv : LatticeConvex (S.erase gen)) :
    ∀ (n : ℕ), ∀ z ∈ genFill S gen X n, GenClosure S X z := by
  intro n
  induction n with
  | zero => intro z hz; exact GenClosure.base hz
  | succ n ih =>
      intro z hz
      rcases genFill_step S gen X n z hz with h | ⟨t, rfl, hb⟩
      · exact ih z h
      · exact GenClosure.step hgen hconv (fun b hbmem => ih (b + t) (hb b hbmem))

/-- The same statement at the level of the closure `genClosure = ⋃ n, genFill`
(`MaximalEnveloped.lean`), which is the shape every `fillCover`-style consumer is phrased
against (`ChainExhaustInter.lean`, `ChainAssembleInter.lean:177`). -/
theorem genClosure_subset_genClosure {S : Finset (ℤ × ℤ)} {gen : ℤ × ℤ} {X : Set (ℤ × ℤ)}
    (hgen : gen ∈ S) (hconv : LatticeConvex (S.erase gen)) :
    ∀ z ∈ MaxEnv.genClosure S gen X, GenClosure S X z := by
  intro z hz
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hz
  exact genFill_subset_genClosure hgen hconv n z hn

/-- **The payoff, in the only form a consumer needs.**  Composing with
`Colle37.agree_on_genClosure` (`Claim37.lean:297`): two orbit-closure members agreeing on `X`
agree on everything the single-generator filtration reaches.

This is the drop-in replacement for the `genFill`-phrased agreement propagation.  It is strictly
more available than the `genFill` route, because `agree_on_genClosure` was already proved
unconditionally from `IsGeneratingSet`, whereas the `genFill` route additionally needs `gen` to be
the *right* generator — which is exactly the unjustified choice `FillCoverWitness.lean` refutes. -/
theorem agree_on_genFill {A : Type*} {η : Config A} {S : Finset (ℤ × ℤ)}
    (hS : Nivat.Colle.IsGeneratingSet η S) {gen : ℤ × ℤ} {X : Set (ℤ × ℤ)}
    (hgen : gen ∈ S) (hconv : LatticeConvex (S.erase gen))
    {x y : Config A} (hx : x ∈ orbitClosure η) (hy : y ∈ orbitClosure η)
    (hX : ∀ z ∈ X, x z = y z) :
    ∀ (n : ℕ), ∀ z ∈ genFill S gen X n, x z = y z :=
  fun n z hz =>
    agree_on_genClosure hS hx hy hX z (genFill_subset_genClosure hgen hconv n z hz)

/-! ## Step 2: the abstract form, and why `Lemma35`'s filtration index is eliminable

`Lemma35.lean` never mentions `genFill`.  It consumes four abstract `ChainData` fields
(`Lemma35.lean:750-758`):

    fill      : ℕ → ℕ → ℕ → ℕ → Set (ℤ × ℤ)
    fillZero  : ∀ i i₀ ε, fill i i₀ ε 0 ⊆ Ahat i ∪ shell i₀ ε
    fillStep  : ∀ i i₀ ε n, ∀ z ∈ fill i i₀ ε (n+1), z ∈ fill i i₀ ε n ∨
                  ∃ t, z = gen + t ∧ ∀ b ∈ S.erase gen, b + t ∈ fill i i₀ ε n
    fillCover : ∀ i i₀ ε, i₀ ≤ i → shell i ε ⊆ ⋃ n, fill i i₀ ε n

`fillStep` is `genFill`'s step verbatim, against the structure's single `gen` field — which is
where the collapse enters the abstract interface, not merely the concrete instance.

`genFill_of_abstract_fill` below is `genFill_subset_genClosure` restated for an arbitrary such
filtration.  Its point is **backwards compatibility**: the four fields every existing
`ChainData` instance already supplies are enough to produce the single `GenClosure`-shaped fact,
so a consumer rewritten against `GenClosure` still accepts every instance built today — the
rewrite is a weakening of the interface, not a new obligation on producers. -/

/-- The abstract filtration weakens into `GenClosure` exactly as `genFill` does; only
`fillZero` and `fillStep` are used, never a concrete definition of `fill`. -/
theorem genFill_of_abstract_fill {S : Finset (ℤ × ℤ)} {gen : ℤ × ℤ} {X : Set (ℤ × ℤ)}
    {fill : ℕ → Set (ℤ × ℤ)}
    (hgen : gen ∈ S) (hconv : LatticeConvex (S.erase gen))
    (hzero : fill 0 ⊆ X)
    (hstep : ∀ (n : ℕ), ∀ z ∈ fill (n + 1), z ∈ fill n ∨
      ∃ t : ℤ × ℤ, z = gen + t ∧ ∀ b ∈ S.erase gen, b + t ∈ fill n) :
    ∀ (n : ℕ), ∀ z ∈ fill n, GenClosure S X z := by
  intro n
  induction n with
  | zero => intro z hz; exact GenClosure.base (hzero hz)
  | succ n ih =>
      intro z hz
      rcases hstep n z hz with h | ⟨t, rfl, hb⟩
      · exact ih z h
      · exact GenClosure.step hgen hconv (fun b hbmem => ih (b + t) (hb b hbmem))

/-- **The replacement for `Lemma35.lean:942-948`.**  Those seven lines build `hspread` (an
`∀ n` statement, by induction along the filtration), then destructure `fillCover`'s `⋃ n` to
recover a single `n` and apply `hspread` at it.  With the `GenClosure` phrasing the whole block
is this one application: no induction, no filtration index, no `gen`.

**Verdict on whether `n` is genuinely needed there: it is not.**  `n` is bound at `:942` purely
as the induction index of `eqOn_of_generatesAt_of_shells`, destructured out of `fillCover` at
`:947`, and consumed at `:948`.  It appears in no other hypothesis, in no conclusion, and never
escapes `hshelleq`'s proof — the statement `hshelleq` proves (`∀ z ∈ c.shell (σ j) ε, F j z =
xhat z`) is already index-free.  So three of the four `fill` fields (`fill`, `fillZero`,
`fillStep`) exist only to carry an index that is discarded one line after it is introduced. -/
theorem shell_agree_of_genClosure {A : Type*} {η : Config A} {S : Finset (ℤ × ℤ)}
    (hS : Nivat.Colle.IsGeneratingSet η S) {X shell : Set (ℤ × ℤ)} {x y : Config A}
    (hx : x ∈ orbitClosure η) (hy : y ∈ orbitClosure η)
    (hX : ∀ z ∈ X, x z = y z)
    (hcover : ∀ z ∈ shell, GenClosure S X z) :
    ∀ z ∈ shell, x z = y z :=
  fun z hz => agree_on_genClosure hS hx hy hX z (hcover z hz)

end Nivat.GenClosureWeaken

#print axioms Nivat.GenClosureWeaken.genFill_subset_genClosure
#print axioms Nivat.GenClosureWeaken.genClosure_subset_genClosure
#print axioms Nivat.GenClosureWeaken.agree_on_genFill
#print axioms Nivat.GenClosureWeaken.genFill_of_abstract_fill
#print axioms Nivat.GenClosureWeaken.shell_agree_of_genClosure
