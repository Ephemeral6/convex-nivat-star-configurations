/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.Lemma35

/-!
# The canonical `A` / `Â`: four of `ChainData`'s nineteen obligations, for free

`ChainData` (`Lemma35.lean:695`) leaves `A` and `Ahat` as free data and then charges four
obligations that constrain them:

* `subStrip` (`Lemma35.lean:722`)  — `A i ⊆ H_{B_i}(ℓ)`,
* `agreeA`   (`Lemma35.lean:724`)  — `(T^{u_i} η)|A_i = x_per|A_i`,
* `AhatEq`   (`Lemma35.lean:726`)  — `Â_i = A_i - k_i v_ℓ`,
* `maximalHat` (`Lemma35.lean:730`) — `Â_i` is the **largest** admissible set.

Together these say: `A i` is contained in the half-strip, `η` agrees with `x_per` on it after
the shift `u i`, and nothing larger does both.  So `A i` is *determined*: it is the agreement
set inside the half-strip.  Taking that as the **definition** rather than as a constraint makes
all four obligations disappear.

This is not a new idea — it is what `chainB` (`Lemma35Wiring.lean:239`) already does.  Its
`maximalHat` proof opens with `intro i Tset _ _ hstrip hagree` (`Lemma35Wiring.lean:283`),
discarding the hypotheses `Env Tset` and `Â_i ⊆ Tset`, which is only possible because its
`Â_i` is exactly this set.  The present file extracts the general mechanism so that the
construction discharging `exists_chainData` need not rediscover it.

## What this buys and what it costs

`ChainCanonData` below carries **15** obligations instead of 19, and
`ChainCanonData.toChainData` turns one into a `ChainData`.

The cost is that `envA` (`Lemma35.lean:716`) is no longer a statement about a set of the
builder's choosing: it becomes

    `Env {w ∈ H_{B_i}(ℓ) | η (w + u i) = x_per w}`,

i.e. *the agreement set inside the half-strip is `E(S_φ)`-enveloped* — which is Collé's actual
geometric content, and now the only place it can live.  Likewise `subBA` becomes the statement
that `η` agrees with `x_per` on all of `B i` after the shift.  **The work is redistributed, not
removed**; the redistribution is favourable because the four fields cost nothing and the residue
lands on a field the construction owes anyway.

`canonA_agreement_maximal` records the converse direction: the canonical `Â_i` itself satisfies
the two hypotheses that `maximalHat` consumes, so the maximality statement is not vacuous.
-/

namespace Nivat.Colle35

open Nivat

variable {α : Type*}

/-- **The agreement set inside the half-strip** — ~~the canonical value of `A_i`~~.

~~Forced by `subStrip` + `agreeA` + `maximalHat` together: those three say `A_i` is contained in
this set and that nothing admissible is larger.~~

## 🔴 2026-09-19 — the identification `A i := canonA …` is RETRACTED (kept under `PROTOCOL.md` §14)

The sentence above is false, and it is the reason `canonA_latticeConvex` was kernel-refuted by
`Nivat.AEnv.not_canonA_latticeConvex`.  `maximalHat` says *"no admissible set is strictly
larger"*, which is **not** *"equals the constraint set"*.  Measured, not argued:
`Nivat.APrice.canonA_ne_A_at_nonempty_witness` (`tmp/Aprice_maxenv_fields.lean`, in `tmp/`,
not landed; `[propext, Quot.sound]`) exhibits a complete `ChainData` — the main build's own
`Colle35.nonempty_chainData`, `Lemma35.lean:768` — with `(2,0) ∈ canonA … 0` but `A 0 = {0}`.

Collé asserts envelopment, and hence convexity, of the maximal **element** only, never of the
constraint set.  `b3_colle2.txt:484`, verbatim:

> `A_i` is a maximal set with respect to partial ordering by inclusion among all
> `E(S_φ)`-enveloped sets `T ⊂ Z²` such that `B_i ⊂ T ⊂ H_{B_i}(ℓ)` and
> `(T^{u_i}η)|T = x_per|T`

So `canonA_latticeConvex` is a claim this repository invented on 2026-09-18, not a gap in the
paper and **not** a defect in `Env`: Definition 3.2 (`b3_colle2.txt:402`) reads *"**A convex
set** `T ⊂ Z²` is said to be weakly `E(U)`-enveloped…"*, with convexity inside the definiens,
which is exactly what `LatticeEdges.WeaklyEnveloped` transcribes.  `Env` stays as it is; the
repo already weakened it once by mistake and reverted that in ea5bbc5 / 456cada / d6f80d9.

The replacement is `Nivat/External/Colle/ChainMax.lean`: `A` becomes free data constrained by
`IsMaxEnvIn Env (canonA …) (A i)`, under which `subStrip`, `agreeA`, `envA` and `maximalHat`
are all still free.  **`canonA` itself is kept and is still correct** — it is the constraint
set `{w ∈ H_{B_i}(ℓ) : (T^{u_i}η)(w) = x_per(w)}`, which is what `IsMaxEnvIn` takes maxima
inside of.  Only the identification of `A i` *with* it is withdrawn. -/
def canonA (η xper : Config α) (vl : ℤ × ℤ) (B : ℕ → Set (ℤ × ℤ)) (u : ℕ → ℤ × ℤ)
    (i : ℕ) : Set (ℤ × ℤ) :=
  {w | w ∈ halfStrip (B i) vl ∧ η (w + u i) = xper w}

/-- Its normalisation by `k_i v_ℓ` — the canonical value of `Â_i`. -/
def canonAhat (η xper : Config α) (vl : ℤ × ℤ) (B : ℕ → Set (ℤ × ℤ)) (u : ℕ → ℤ × ℤ)
    (kk : ℕ → ℕ) (i : ℕ) : Set (ℤ × ℤ) :=
  {z | z + (kk i : ℤ) • vl ∈ canonA η xper vl B u i}

section Canon

variable {η xper : Config α} {vl : ℤ × ℤ} {B : ℕ → Set (ℤ × ℤ)} {u : ℕ → ℤ × ℤ} {kk : ℕ → ℕ}

theorem canonA_subset_halfStrip (i : ℕ) : canonA η xper vl B u i ⊆ halfStrip (B i) vl :=
  fun _ hw => hw.1

theorem canonA_agree (i : ℕ) : ∀ w ∈ canonA η xper vl B u i, η (w + u i) = xper w :=
  fun _ hw => hw.2

theorem canonAhat_eq (i : ℕ) :
    canonAhat η xper vl B u kk i = {z | z + (kk i : ℤ) • vl ∈ canonA η xper vl B u i} := rfl

/-- **Maximality of the canonical `Â_i`, in a form strictly stronger than the `maximalHat`
field**: the hypotheses `Env Tset` and `Â_i ⊆ Tset` are not needed.  Half-strip containment
and agreement alone already force `Tset ⊆ Â_i`. -/
theorem subset_canonAhat_of_agree (i : ℕ) (Tset : Set (ℤ × ℤ))
    (hstrip : Tset ⊆ {z | z + (kk i : ℤ) • vl ∈ halfStrip (B i) vl})
    (hagree : ∀ z ∈ Tset, η (z + ((kk i : ℤ) • vl + u i)) = xper (z + (kk i : ℤ) • vl)) :
    Tset ⊆ canonAhat η xper vl B u kk i := by
  intro z hz
  refine ⟨hstrip hz, ?_⟩
  have h := hagree z hz
  have hrw : z + (kk i : ℤ) • vl + u i = z + ((kk i : ℤ) • vl + u i) := by rw [add_assoc]
  rw [hrw]
  exact h

/-- The canonical `Â_i` meets the two hypotheses that `maximalHat` consumes, so
`subset_canonAhat_of_agree` is not vacuously applicable only to smaller sets. -/
theorem canonA_agreement_maximal (i : ℕ) :
    canonAhat η xper vl B u kk i ⊆ {z | z + (kk i : ℤ) • vl ∈ halfStrip (B i) vl} ∧
      ∀ z ∈ canonAhat η xper vl B u kk i,
        η (z + ((kk i : ℤ) • vl + u i)) = xper (z + (kk i : ℤ) • vl) := by
  refine ⟨fun _ hz => hz.1, ?_⟩
  intro z hz
  have h := hz.2
  have hrw : z + (kk i : ℤ) • vl + u i = z + ((kk i : ℤ) • vl + u i) := by rw [add_assoc]
  rwa [hrw] at h

end Canon

/-- **`ChainData` with `A` and `Â` taken canonically.**

Fifteen obligations instead of nineteen: `subStrip`, `agreeA`, `AhatEq` and `maximalHat` are
discharged by `ChainCanonData.toChainData` below.  Field names and statements are otherwise
copied verbatim from `ChainData` (`Lemma35.lean:695-758`), with `A i` replaced by
`canonA η xper vl B u i` and `Â i` by `canonAhat η xper vl B u kk i`. -/
structure ChainCanonData {α : Type*} (η xper : Config α) (vl : ℤ × ℤ)
    (S : Finset (ℤ × ℤ)) (gen : ℤ × ℤ) where
  /-- "is an `E(S_φ)`-enveloped set" (Definition 3.2), left abstract. -/
  Env : Set (ℤ × ℤ) → Prop
  /-- The sets `B_i` of the chain. -/
  B : ℕ → Set (ℤ × ℤ)
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
  /-- Item (i): each `B_i` is `E(S_φ)`-enveloped. -/
  envB : ∀ i, Env (B i)
  /-- Item (iv), now Collé's geometric content: **the agreement set inside the half-strip is
  `E(S_φ)`-enveloped**. -/
  envA : ∀ i, Env (canonA η xper vl B u i)
  /-- `B_i ⊂ A_i`, now: `η` agrees with `x_per` on all of `B_i` after the shift `u_i`. -/
  subBA : ∀ i, B i ⊆ canonA η xper vl B u i
  /-- `A_i ⊂ B_{i+1}`. -/
  subAB : ∀ i, canonA η xper vl B u i ⊆ B (i + 1)
  /-- The normalised sets are nested. -/
  AhatMono : ∀ i j, i ≤ j →
    canonAhat η xper vl B u kk i ⊆ canonAhat η xper vl B u kk j
  /-- Each `Â_i^{(ε)}` is finite. -/
  shellFinite : ∀ i ε, (shell i ε).Finite
  /-- `Â_i ⊆ Â_i^{(ε)}` (the case `t = 0`). -/
  subShell : ∀ i ε, canonAhat η xper vl B u kk i ⊆ shell i ε
  /-- `Â_i^{(ε)} ⊆ Â_∞^{(ε)}`. -/
  shellSubInf : ∀ i ε, shell i ε ⊆ shellInf ε
  /-- `Â_∞^{(0)} ⊆ Â_∞`. -/
  shellInfZero : shellInf 0 ⊆ ⋃ i, canonAhat η xper vl B u kk i
  /-- **`I₀`**，原文 `b3_colle2.txt:520` 的第二个常数，`:524` 用在 `i ≥ max{i₀, I₀}`。
  见 `ChainData.I₀`（`Lemma35.lean`）。 -/
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
    ∀ i, max i₀ I₀ ≤ i → ¬ (shell i ε ⊆ canonAhat η xper vl B u kk i)
  /-- For an appropriate `ε` and all large `i`, `Â_i^{(ε)}` is `E(S_φ)`-enveloped. -/
  shellEnv : ∃ ε i₀, 0 < ε ∧ ∀ i, i₀ ≤ i → Env (shell i ε)
  /-- The filtration starts inside `Â_i ∪ Â_{i₀}^{(ε)}`. -/
  fillZero : ∀ i i₀ ε, fill i i₀ ε 0 ⊆ canonAhat η xper vl B u kk i ∪ shell i₀ ε
  /-- Each new site is a translate of the distinguished point of the window `S`, all of whose
  other points are already filled. -/
  fillStep : ∀ i i₀ ε n, ∀ z ∈ fill i i₀ ε (n + 1),
    z ∈ fill i i₀ ε n ∨ ∃ t : ℤ × ℤ, z = gen + t ∧ ∀ b ∈ S.erase gen, b + t ∈ fill i i₀ ε n
  /-- The filtration exhausts `Â_i^{(ε)}`, from a lower filtration base `i₀ ≤ i`.  The
  unconstrained `∀ i₀` version is false (`lane-tower3`, hand-verified on the `hexShape` shell
  family: at `i=2, ε=1, i₀=0`, `(0,-1) ∈ shell 2 1` is unreachable from `Â_0^{(1)} = {(0,0)}`).
  The only real call site (`Lemma35.lean`) always has `i₀ ≤ i` on hand before invoking this.
  Phrased against `Colle37.GenClosure`, matching `Lemma35.lean`'s `ChainData.fillCover`
  (Round 80).  **The `∀ ε` was also ours and is kernel-refuted** — see `ChainData.fillCover`
  (`Lemma35.lean:777`); the field now carries `shellEnv`'s `(ε, i₀)` guard. -/
  fillCover : ∀ ε i₀ : ℕ, 0 < ε → (∀ i, i₀ ≤ i → Env (shell i ε)) →
    ∀ i, max i₀ I₀ ≤ i →
    shell i ε ⊆ {z | Colle37.GenClosure S (canonAhat η xper vl B u kk i ∪ shell i₀ ε) z}

namespace ChainCanonData

variable {η xper : Config α} {vl : ℤ × ℤ} {S : Finset (ℤ × ℤ)} {gen : ℤ × ℤ}

/-- **Fifteen obligations suffice.**  `subStrip`, `agreeA`, `AhatEq` and `maximalHat` are
discharged from the canonical shape, with no hypotheses. -/
def toChainData (c : ChainCanonData η xper vl S gen) : ChainData η xper vl S gen where
  Env := c.Env
  B := c.B
  A := canonA η xper vl c.B c.u
  u := c.u
  kk := c.kk
  Ahat := canonAhat η xper vl c.B c.u c.kk
  shell := c.shell
  shellInf := c.shellInf
  fill := c.fill
  envB := c.envB
  envA := c.envA
  subBA := c.subBA
  subAB := c.subAB
  subStrip := fun i => canonA_subset_halfStrip i
  agreeA := fun i => canonA_agree i
  AhatEq := fun i => canonAhat_eq i
  AhatMono := c.AhatMono
  maximalHat := fun i Tset _ _ hstrip hagree =>
    subset_canonAhat_of_agree i Tset hstrip hagree
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

@[simp] theorem toChainData_A (c : ChainCanonData η xper vl S gen) (i : ℕ) :
    c.toChainData.A i = canonA η xper vl c.B c.u i := rfl

@[simp] theorem toChainData_Ahat (c : ChainCanonData η xper vl S gen) (i : ℕ) :
    c.toChainData.Ahat i = canonAhat η xper vl c.B c.u c.kk i := rfl

@[simp] theorem toChainData_Env (c : ChainCanonData η xper vl S gen) :
    c.toChainData.Env = c.Env := rfl

@[simp] theorem toChainData_shell (c : ChainCanonData η xper vl S gen) :
    c.toChainData.shell = c.shell := rfl

end ChainCanonData

end Nivat.Colle35
