/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.ChainCanon

/-!
# `ChainMaxData`: Collé's `A_i` as a *maximal* enveloped subset, not as the whole constraint set

## Why this file exists

`ChainCanon.lean` (2026-09-18) identified Collé's `A_i` with the agreement set inside the
half-strip, `canonA η xper vl B u i = {w ∈ H_{B_i}(ℓ) | η (w + u i) = x_per w}`
(`ChainCanon.lean:58`).  That identification was **refuted in the kernel** on the same day:
`Nivat.AEnv.not_canonA_latticeConvex` (`AEnv.lean:290`) exhibits parameters at which `canonA`
is not lattice-convex, hence cannot be `E(S_φ)`-enveloped, so `ChainCanonData.envA`
(`ChainCanon.lean:134`) is unsatisfiable there.

The refuted statement was never Collé's.  `b3_colle2.txt:484`, verbatim:

> fixed a sequence `(u_i)_{i∈ℕ} ⊂ ℤ²` fulfilling the previous item, `A_i` is a maximal set with
> respect to partial ordering by inclusion among all `E(𝒮_φ)`-enveloped sets `𝒯 ⊂ ℤ²` such that
> `B_i ⊂ 𝒯 ⊂ H_{B_i}(ℓ)` and `(T^{u_i}η)|𝒯 = x_per|𝒯` (see Figure 5).

Envelopment (and with it convexity, Definition 3.2 at `:402`) is asserted of the maximal
*element* `A_i`, never of the constraint set `{𝒯 ⊂ H_{B_i}(ℓ) : (T^{u_i}η)|𝒯 = x_per|𝒯}`.
The main-build witness `nonempty_chainData` (`Lemma35.lean:768`) already has `A 0 = {0}` while
`(2,0) ∈ canonA … 0`, so `ChainData` never forced `A i = canonA … i` either
(`canonA_ne_A_at_nonempty_witness`, `tmp/Aprice_maxenv_fields.lean`, kernel).

This file states `A_i` the way `:484` does — `IsMaxEnvIn Env (canonA …) (A i)` — and shows the
four obligations `ChainCanon.lean` bought (`subStrip`, `agreeA`, `AhatEq`, `maximalHat`,
`Lemma35.lean:722-733`) are **still free** under that shape.  `Env` itself is untouched:
`WeaklyEnveloped` (`LatticeEdges.lean:624`) matches `:402` verbatim.

## What this costs

Compared with `ChainCanonData` (15 obligations), `ChainMaxData` has **16**: `envA` is replaced
by `maxA` (the `:484` maximality, which contains `Env (A i)`), and one new field `envShift`
(translation-invariance of `Env`) is needed to transport maximality from `A_i` to
`Â_i = A_i − k_i v_ℓ` (Collé's "It is easy to see", `:492`).  For the intended
`Env := EnvOf ↑𝒮_φ`, `envShift` is `envOf_shift_mem` below — zero cost.

## ⚠ No consumers yet (`PROTOCOL.md` §20)

`exists_chainData` (`RegionSteps.lean:813`) produces a `ChainDataGeom` and never mentioned
`ChainCanonData`; so `ChainMaxData` inherits **zero** consumers.  This module retires a false
intermediate obligation; it does **not** discharge any of leaf A's four `sorry`s, and the
`sorry` count is unchanged by it.  The residual obligation it isolates is `HasMaxEnvIn` below —
a named `Prop`, dispatchable, not yet produced by anyone.
-/

set_option autoImplicit false

namespace Nivat.Colle35

open Nivat

variable {α : Type*}

/-- **Collé `b3_colle2.txt:484`, verbatim shape.**  `A` is `Env`, sits inside the constraint
set `C`, and no `Env` set strictly between `A` and `C` exists. -/
def IsMaxEnvIn (Env : Set (ℤ × ℤ) → Prop) (C A : Set (ℤ × ℤ)) : Prop :=
  Env A ∧ A ⊆ C ∧ ∀ T, Env T → A ⊆ T → T ⊆ C → T ⊆ A

/-- **The residual obligation of Collé's item (iv)** (`b3_colle2.txt:484`): a maximal
`E(𝒮_φ)`-enveloped set *exists* inside the constraint set `C`.

> `A_i` is a maximal set with respect to partial ordering by inclusion among all
> `E(𝒮_φ)`-enveloped sets `𝒯 ⊂ ℤ²` such that `B_i ⊂ 𝒯 ⊂ H_{B_i}(ℓ)` and
> `(T^{u_i}η)|𝒯 = x_per|𝒯`.

Collé gives no argument for existence (no Zorn, no chain bound — `Zorn` occurs zero times in
`b3_colle2.txt`, see `RegionSteps.lean:784-792`).  It is not free from the half-strip alone:
`Nivat.MaxEnv.no_maximal_enveloped_halfStrip` (`MaximalEnveloped.lean:352`) shows the family of
enveloped sets inside a half-strip has **no** maximal element, so the agreement clause
`η (w + u) = x_per w` in `C` has to carry the whole weight.  Named as a `Prop` so it can be
dispatched.

*Status (2026-09-19, PROTOCOL §14; the earlier text "nobody produces it yet" is superseded):*
produced at every `B` by `ChainRecursion.StepHyp` — `ChainAsm.hasMaxEnvIn_of_stepHyp`
(`ChainAssemble.lean`) gives `HasMaxEnvIn (EnvOf ↑S) {w | w ∈ halfStrip B vl ∧ ξ (w + u₀) = xper w}`
from `StepHyp ξ xper S vl u₀`, `EnvOf ↑S B` and agreement of `T u₀ ξ` with `xper` on `B`. -/
def HasMaxEnvIn (Env : Set (ℤ × ℤ) → Prop) (C : Set (ℤ × ℤ)) : Prop :=
  ∃ A, IsMaxEnvIn Env C A

/-- `Â_i := A_i − k_i v_ℓ` (`b3_colle2.txt:488`), as a definition so that `AhatEq` is `rfl`. -/
def hatOf (A : ℕ → Set (ℤ × ℤ)) (kk : ℕ → ℕ) (vl : ℤ × ℤ) (i : ℕ) : Set (ℤ × ℤ) :=
  {z | z + (kk i : ℤ) • vl ∈ A i}

section Max

variable {Env : Set (ℤ × ℤ) → Prop} {η xper : Config α} {vl : ℤ × ℤ}
  {B : ℕ → Set (ℤ × ℤ)} {u : ℕ → ℤ × ℤ} {kk : ℕ → ℕ} {A : ℕ → Set (ℤ × ℤ)}

/-- `subStrip` (`Lemma35.lean:722`) from `:484` maximality. -/
theorem subStrip_of_max (h : ∀ i, IsMaxEnvIn Env (canonA η xper vl B u i) (A i)) :
    ∀ i, A i ⊆ halfStrip (B i) vl :=
  fun i _ hw => ((h i).2.1 hw).1

/-- `agreeA` (`Lemma35.lean:724`) from `:484` maximality. -/
theorem agreeA_of_max (h : ∀ i, IsMaxEnvIn Env (canonA η xper vl B u i) (A i)) :
    ∀ i, ∀ z ∈ A i, η (z + u i) = xper z :=
  fun i _ hw => ((h i).2.1 hw).2

/-- `envA` (`Lemma35.lean:716`) from `:484` maximality. -/
theorem envA_of_max (h : ∀ i, IsMaxEnvIn Env (canonA η xper vl B u i) (A i)) :
    ∀ i, Env (A i) :=
  fun i => (h i).1

/-- `AhatEq` (`Lemma35.lean:726`) is definitional. -/
theorem hatOf_eq (i : ℕ) : hatOf A kk vl i = {z | z + (kk i : ℤ) • vl ∈ A i} := rfl

/-- `maximalHat` (`Lemma35.lean:730-733`) from `:484` maximality, given translation-invariance
of `Env`.  This is Collé's `:492` ("It is easy to see that each `Â_i` is a maximal set …"):
the strip and agreement hypotheses on `Tset` say exactly that `Tset + k_i v_ℓ ⊆ canonA`, so
`:484` maximality of `A_i` applies to that translate. -/
theorem maximalHat_of_max
    (hshift : ∀ (v : ℤ × ℤ) (T : Set (ℤ × ℤ)), Env T → Env {z | z + v ∈ T})
    (h : ∀ i, IsMaxEnvIn Env (canonA η xper vl B u i) (A i)) :
    ∀ i (Tset : Set (ℤ × ℤ)), Env Tset → hatOf A kk vl i ⊆ Tset →
      Tset ⊆ {z | z + (kk i : ℤ) • vl ∈ halfStrip (B i) vl} →
      (∀ z ∈ Tset, η (z + ((kk i : ℤ) • vl + u i)) = xper (z + (kk i : ℤ) • vl)) →
      Tset ⊆ hatOf A kk vl i := by
  intro i Tset hEnv hsub hstrip hagree z hz
  -- the un-normalised candidate `T' := Tset + kk i • vl`
  set T' : Set (ℤ × ℤ) := {w | w + (-((kk i : ℤ) • vl)) ∈ Tset} with hT'
  have hEnvT' : Env T' := hshift _ _ hEnv
  have hAT' : A i ⊆ T' := by
    intro w hw
    have : w + (-((kk i : ℤ) • vl)) + (kk i : ℤ) • vl ∈ A i := by
      simpa [add_assoc] using hw
    exact hsub this
  have hT'C : T' ⊆ canonA η xper vl B u i := by
    intro w hw
    have hw' : w + (-((kk i : ℤ) • vl)) ∈ Tset := hw
    refine ⟨?_, ?_⟩
    · have := hstrip hw'
      simpa [add_assoc] using this
    · have := hagree _ hw'
      simpa [add_assoc] using this
  have hmax := (h i).2.2 T' hEnvT' hAT' hT'C
  have hz' : z + (kk i : ℤ) • vl ∈ T' := by
    show z + (kk i : ℤ) • vl + (-((kk i : ℤ) • vl)) ∈ Tset
    simpa [add_assoc] using hz
  exact hmax hz'

end Max

/-- `EnvOf U` is translation-invariant in the form `envShift` wants; this is
`Nivat.LE2.envOf_shift` (`LatticeEdges.lean:2445`) with the translate written as a
membership set.  So for `Env := EnvOf ↑𝒮_φ` the field `envShift` below costs nothing. -/
theorem envOf_shift_mem (U : Set (ℤ × ℤ)) (v : ℤ × ℤ) (T : Set (ℤ × ℤ))
    (hT : Nivat.LE2.EnvOf U T) : Nivat.LE2.EnvOf U {z | z + v ∈ T} := by
  have := Nivat.LE2.envOf_shift (-v) hT
  have heq : Nivat.LE2.shift (-v) T = {z | z + v ∈ T} := by
    ext z; simp [Nivat.LE2.shift, sub_eq_add_neg]
  simpa [heq] using this

/-- **`ChainData` with `A_i` as Collé's `:484` maximal element.**

Sixteen obligations.  Relative to `ChainData` (`Lemma35.lean:695-758`, 19 obligations):
`envA`, `subStrip`, `agreeA`, `AhatEq`, `maximalHat` are replaced by `maxA` + `envShift`;
every other field is copied verbatim with `Ahat i` written as `hatOf A kk vl i`.
Relative to `ChainCanonData` (`ChainCanon.lean:114`, 15 obligations): `A` is free data again,
`envA` becomes `maxA`, and `envShift` is added. -/
structure ChainMaxData {α : Type*} (η xper : Config α) (vl : ℤ × ℤ)
    (S : Finset (ℤ × ℤ)) (gen : ℤ × ℤ) where
  /-- "is an `E(S_φ)`-enveloped set" (Definition 3.2), left abstract. -/
  Env : Set (ℤ × ℤ) → Prop
  /-- The sets `B_i` of the chain. -/
  B : ℕ → Set (ℤ × ℤ)
  /-- The sets `A_i` of the chain — free data, constrained only by `maxA`. -/
  A : ℕ → Set (ℤ × ℤ)
  /-- The translations `u_i` of item (iii). -/
  u : ℕ → ℤ × ℤ
  /-- The normalising amounts `k_i`. -/
  kk : ℕ → ℕ
  /-- `Â_i^{(ε)}`. -/
  shell : ℕ → ℕ → Set (ℤ × ℤ)
  /-- `Â_∞^{(ε)}`. -/
  shellInf : ℕ → Set (ℤ × ℤ)
  /-- The filtration along which the generation induction of (3.3) runs. -/
  fill : ℕ → ℕ → ℕ → ℕ → Set (ℤ × ℤ)
  /-- `Env` is translation-invariant (free for `EnvOf U`: `envOf_shift_mem`). -/
  envShift : ∀ (v : ℤ × ℤ) (T : Set (ℤ × ℤ)), Env T → Env {z | z + v ∈ T}
  /-- Item (i): each `B_i` is `E(S_φ)`-enveloped. -/
  envB : ∀ i, Env (B i)
  /-- Item (iv), `b3_colle2.txt:484` verbatim: `A_i` is a maximal `Env` set inside the
  agreement-in-half-strip constraint set. -/
  maxA : ∀ i, IsMaxEnvIn Env (canonA η xper vl B u i) (A i)
  /-- The chain `B_i ⊂ A_i`. -/
  subBA : ∀ i, B i ⊆ A i
  /-- The chain `A_i ⊂ B_{i+1}`. -/
  subAB : ∀ i, A i ⊆ B (i + 1)
  /-- The normalised sets are nested. -/
  AhatMono : ∀ i j, i ≤ j → hatOf A kk vl i ⊆ hatOf A kk vl j
  /-- Each `Â_i^{(ε)}` is finite. -/
  shellFinite : ∀ i ε, (shell i ε).Finite
  /-- `Â_i ⊆ Â_i^{(ε)}` (the case `t = 0`). -/
  subShell : ∀ i ε, hatOf A kk vl i ⊆ shell i ε
  /-- `Â_i^{(ε)} ⊆ Â_∞^{(ε)}`. -/
  shellSubInf : ∀ i ε, shell i ε ⊆ shellInf ε
  /-- `Â_∞^{(0)} ⊆ Â_∞`. -/
  shellInfZero : shellInf 0 ⊆ ⋃ i, hatOf A kk vl i
  /-- **`I₀`, 原文 `b3_colle2.txt:520` 的第二个常数**，`:524` 用在 `i ≥ max{i₀, I₀}`。
  见 `ChainData.I₀`（`Lemma35.lean`）的对齐说明。 -/
  I₀ : ℕ
  /-- `Â_i^{(ε)} ⊆ H_{B_i}(ℓ) - k_i v_ℓ`, for the `(ε, i₀)` of `shellEnv` and all `i ≥ i₀`
  (`b3_colle2.txt:520`, same sentence as `shellEnv`; see `ChainData.shellSubStrip`,
  `Lemma35.lean:744`, for why the old `∀ i ε` form was a quantifier we added). -/
  shellSubStrip : ∀ ε i₀ : ℕ, 0 < ε → (∀ i, i₀ ≤ i → Env (shell i ε)) →
    ∀ i, max i₀ I₀ ≤ i → shell i ε ⊆ {z | z + (kk i : ℤ) • vl ∈ halfStrip (B i) vl}
  /-- A shell of positive thickness is strictly larger than `Â_i`, for the `(ε, i₀)` of
  `shellEnv` and all `i ≥ i₀` (`b3_colle2.txt:530` under `:516`; see `ChainData.shellProper`,
  `Lemma35.lean:758`, for why the old `∀ i ε` form was a quantifier we added). -/
  shellProper : ∀ ε i₀ : ℕ, 0 < ε → (∀ i, i₀ ≤ i → Env (shell i ε)) →
    ∀ i, max i₀ I₀ ≤ i → ¬ (shell i ε ⊆ hatOf A kk vl i)
  /-- For an appropriate `ε` and all large `i`, `Â_i^{(ε)}` is `E(S_φ)`-enveloped. -/
  shellEnv : ∃ ε i₀, 0 < ε ∧ ∀ i, i₀ ≤ i → Env (shell i ε)
  /-- The filtration starts inside `Â_i ∪ Â_{i₀}^{(ε)}`. -/
  fillZero : ∀ i i₀ ε, fill i i₀ ε 0 ⊆ hatOf A kk vl i ∪ shell i₀ ε
  /-- Each new site is a translate of the distinguished point of the window `S`, all of whose
  other points are already filled. -/
  fillStep : ∀ i i₀ ε n, ∀ z ∈ fill i i₀ ε (n + 1),
    z ∈ fill i i₀ ε n ∨ ∃ t : ℤ × ℤ, z = gen + t ∧ ∀ b ∈ S.erase gen, b + t ∈ fill i i₀ ε n
  /-- The filtration exhausts `Â_i^{(ε)}`, for the `(ε, i₀)` of `shellEnv` and all `i ≥ i₀`
  (see `ChainCanon.lean`'s `fillCover` for why the unconstrained `∀ i₀` version is false, and
  `ChainData.fillCover` (`Lemma35.lean:777`) for the kernel refutation of the old `∀ ε` form).
  Phrased against `Colle37.GenClosure`, matching `Lemma35.lean`'s `ChainData.fillCover`
  (Round 80). -/
  fillCover : ∀ ε i₀ : ℕ, 0 < ε → (∀ i, i₀ ≤ i → Env (shell i ε)) →
    ∀ i, max i₀ I₀ ≤ i →
    shell i ε ⊆ {z | Colle37.GenClosure S (hatOf A kk vl i ∪ shell i₀ ε) z}

namespace ChainMaxData

variable {η xper : Config α} {vl : ℤ × ℤ} {S : Finset (ℤ × ℤ)} {gen : ℤ × ℤ}

/-- **Sixteen obligations suffice.**  `envA`, `subStrip`, `agreeA`, `AhatEq`, `maximalHat` are
discharged from `maxA` + `envShift`. -/
def toChainData (c : ChainMaxData η xper vl S gen) : ChainData η xper vl S gen where
  Env := c.Env
  B := c.B
  A := c.A
  u := c.u
  kk := c.kk
  Ahat := hatOf c.A c.kk vl
  shell := c.shell
  shellInf := c.shellInf
  fill := c.fill
  envB := c.envB
  envA := envA_of_max c.maxA
  subBA := c.subBA
  subAB := c.subAB
  subStrip := subStrip_of_max c.maxA
  agreeA := agreeA_of_max c.maxA
  AhatEq := fun i => hatOf_eq i
  AhatMono := c.AhatMono
  maximalHat := maximalHat_of_max c.envShift c.maxA
  shellFinite := c.shellFinite
  subShell := c.subShell
  shellSubInf := c.shellSubInf
  shellInfZero := c.shellInfZero
  I₀ := c.I₀
  shellSubStrip := c.shellSubStrip
  shellProper := c.shellProper
  shellEnv := c.shellEnv
  fillZero := c.fillZero
  fillStep := c.fillStep
  fillCover := c.fillCover

@[simp] theorem toChainData_A (c : ChainMaxData η xper vl S gen) : c.toChainData.A = c.A := rfl

@[simp] theorem toChainData_Ahat (c : ChainMaxData η xper vl S gen) (i : ℕ) :
    c.toChainData.Ahat i = hatOf c.A c.kk vl i := rfl

@[simp] theorem toChainData_Env (c : ChainMaxData η xper vl S gen) :
    c.toChainData.Env = c.Env := rfl

@[simp] theorem toChainData_shell (c : ChainMaxData η xper vl S gen) :
    c.toChainData.shell = c.shell := rfl

end ChainMaxData

end Nivat.Colle35
