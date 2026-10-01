/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.Lemma35
import Nivat.External.Colle.Lemma45
import Nivat.External.Colle.Generating
import Nivat.External.Colle.GenClosureDef

/-!
# Colle Claim 3.7: No fully periodic accumulation points

Formalization of Colle, *On periodic decompositions, one-sided nonexpansive directions
and Nivat's conjecture*, arXiv:1909.08195v4, §3.1, Claim 3.7.

## Paper Reference

**Source:** Cleber Fernando Colle, arXiv:1909.08195v4, page 16 (§3.1, proof of Theorem 1.14).

**Exact location:** The claim appears immediately after equation (3.5), which establishes
the existence of an (ℓ_m, ℓ_J)-region from Lemma 3.5.

**Colle, Claim 3.7 (arXiv:1909.08195v4, page 16):**

> The set {T^{t·v_ℓ'}ϑ : t ∈ ℤ_+} does not have fully periodic accumulation points.
>
> Indeed, suppose, by contradiction, that {T^{t·v_ℓ'}ϑ : t ∈ ℤ_+} has a fully periodic
> accumulation point. Then, for each square Q = [-i,i]² ∩ ℤ², with i ∈ ℕ, we may find
> an integer t₀ ∈ ℤ_+ such that (T^{t₀·v_ℓ'}ϑ)|_Q = ϑ|_{Q+t₀·v_ℓ'} is fully periodic
> and thus periodic with period parallel to ℓ_m. Since x̂_per is periodic with period
> parallel to ℓ_m, ϑ|_{Â_∞^(ε)} = x̂_per|_{Â_∞^(ε)} and the set Q ∩ Â_∞^(ε) can be
> taken as large as we want, then
>   ϑ|_{Â_∞^(ε) ∪ (Â_∞^(ε+1) ∩ (Q+t₀·v_ℓ'))} = x̂_per|_{Â_∞^(ε) ∪ (Â_∞^(ε+1) ∩ (Q+t₀·v_ℓ'))}
> for a square Q large enough and some t₀ ∈ ℕ. Since S_φ is an η-generating set,
> we may enlarge the set where ϑ and x̂_per coincide so that
> ϑ|_{Â_∞^(ε+1)} = x̂_per|_{Â_∞^(ε+1)}, which contradicts (3.5) and proves the claim.

## STATUS: the previously formalized statement is FALSE and is refuted here

An earlier revision of this file carried a theorem `claim37` whose hypotheses were

* `IsGeneratingSet η S_φ`,
* `x_per` fully periodic and in `orbitClosure η`, `ϑ ∈ orbitClosure η`,
* an *arbitrary* family `A_infty : ℕ → Set (ℤ × ℤ)` with `ϑ = x_per` on `A_infty ε`
  and `ϑ ≠ x_per` somewhere on `A_infty (ε+1)`,
* `v` primitive and nonzero,

and concluded that `{T^{t·v}ϑ : t ∈ ℕ}` has no fully periodic accumulation point.
That statement is **false**; `not_claim37Statement` below is a machine-checked refutation.

**The counterexample** (`Counterexample` section, alphabet `Bool`):

* `η = ϑ` is the indicator of the vertical line `{z : z.1 = 0}`.
* `x_per` is the constant-`false` configuration; it is doubly periodic and it lies in
  `orbitClosure η` (translate the line out of any finite window).
* `S_φ = {(0,0), (0,1)}` is lattice convex and is a generating set for `η`, because every
  member of `orbitClosure η` is invariant under the vertical shift `(0,1)`, so the value at
  either site of `S_φ` is determined by the value at the other one.
* `A_infty 0 = ∅` and `A_infty n = univ` for `n ≥ 1`, `ε = 0`: the agreement hypothesis is
  vacuous, and `ϑ (0,0) = true ≠ false = x_per (0,0)` gives the disagreement hypothesis.
* `v = (1,0)` is primitive and nonzero, and `T^{t·v}ϑ → x_per` pointwise as `t → ∞`
  (the line escapes every finite window), so the constant-`false` configuration *is* a
  fully periodic accumulation point of `{T^{t·v}ϑ}`.

**Why the formalization was wrong.** The paper's `Â_∞^(ε)` and `Â_∞^(ε+1)` are not arbitrary
sets: they are the successive layers of the `(ℓ_m, ℓ_J)`-region produced by Lemma 3.5, and
the argument uses (i) that the accumulation point's period is parallel to `ℓ_m`, the same
direction in which `x̂_per` is periodic, and (ii) that `Â_∞^(ε+1)` is reached from
`Â_∞^(ε)` together with one extra square `Q + t₀ v` by `S_φ`-generation. Dropping (i) and
(ii) — as the quantification over an arbitrary `A_infty` does — destroys the claim: the
counterexample above has an agreement region carrying no information at all.

## What is proved here instead

* `Counterexample.*` — the data above, with all hypotheses of the old statement verified.
* `Claim37Statement` — the old statement, packaged as a `Prop` (specialized to `Type`).
* `not_claim37Statement` — `¬ Claim37Statement`. Machine-checked refutation.
* `GenClosure` — the sites forced from a known set `D` by repeated `S_φ`-generation.
* `agree_on_genClosure` — two members of the orbit closure that agree on `D` agree on the
  whole `GenClosure S_φ D`. This is the paper's Step 3 ("since `S_φ` is an η-generating set,
  we may enlarge the set where `ϑ` and `x̂_per` coincide"), proved in full.
* `claim37_final_step` — the paper's closing sentence, proved: given the agreement on
  `Â_∞^(ε)` and an extra agreement window `D` from which `Â_∞^(ε+1)` is `S_φ`-generated,
  `ϑ` and `x̂_per` agree on all of `Â_∞^(ε+1)` (so (3.5) is contradicted). It mentions no
  accumulation point, hence does not presuppose Claim 3.7's conclusion.

**What is still missing for Claim 3.7:** nothing, given the hypothesis bundle of §8 —
see below.

## The corrected statement (§8), and how it differs

`claim37` (§8) is a statement of Claim 3.7 that is **proved**, `sorry`-free and
`axiom`-free.  The difference from the refuted `Claim37Statement` is a single extra argument
`R : RegionLayers`, a hypothesis bundle recording exactly what the proof needs from the
`(ℓ_m, ℓ_J)`-region of Lemma 3.5:

* `R.reach` — sliding along `ℓ_m` carries every site of `Â_∞^(ε+1)` into `Â_∞^(ε)` in
  boundedly many steps (the paper's *"`Q ∩ Â_∞^(ε)` can be taken as large as we want"*);
* `R.gen` — `Â_∞^(ε+1)` is `S_φ`-generated from `Â_∞^(ε)` together with one far square
  `Q + t₀·v` (the paper's closing sentence).

and `IsFullyPeriodic x_per` weakened to what is actually used: `x̂_per` has a nonzero period
parallel to `ℓ_m`.

Three safeguards, all machine-checked:

* **Non-vacuity** (§10): `Witness.witnessRegion` inhabits `RegionLayers` and
  `Witness.claim37_hypotheses_satisfiable` satisfies every other hypothesis, so `claim37` is
  not vacuously true.  `Witness.witness_no_fully_periodic_acc` instantiates `claim37` and
  gets a conclusion that is independently true by hand.
* **The §2 counterexample is genuinely excluded** (§11): `counterexample_violates_gen` shows
  that for the §2 configuration data, `R.gen` fails for **every** choice of layers.  So
  `not_claim37Statement` does not touch `claim37`.
* **No hypothesis can imply the conclusion**: every field of `RegionLayers` is *config-free*
  — it mentions only `A`, `ε`, `S_φ`, `v_m`, `v`, never `η`, `ϑ`, `x̂_per` or the
  accumulation point.  A statement that never mentions `ϑ` cannot assert anything about
  accumulation points of `{T^{t·v}ϑ}`.

**On `R.gen`.** `R.gen` is a hypothesis of this file, but it is *not* a gap in Colle. The
earlier flag here — which called Colle's justification, *"since `S_φ` is an η-generating set,
we may enlarge the set where `ϑ` and `x̂_per` coincide"*, an unjustified induction — was
**withdrawn 2026-09-16**; the forcing order is in the paper, and was missed only because the
OCR drops the subscripts of the displayed formulas. See §"WITHDRAWN 2026-09-16" below for the
line-by-line check against the original LaTeX, and `ShellLine.lean` / `ShellGen.lean` for the
two kernel-clean pieces of the proof now in the tree.

## Gap Assessment: Enveloped vs WeaklyEnveloped

The theorem `RegionEdges.not_E_inter_subset` refutes `E(R ∩ ℋ(k, b)) ⊆ E(R) ∪ {k}`.
Claim 3.7 does not use the `Enveloped` property or track edge directions under
intersection; it uses `S_φ` purely as a generating set. That refutation therefore does not
bear on this file (see §6 below, which also records why that assessment is prose and not a
theorem). What *is* missing here is the region structure from Lemma 3.5, as described above.
-/

namespace Nivat.Colle37

open Nivat Nivat.Colle Nivat.Colle35 Nivat.Colle45 Nivat.LE2

/-! ## §1. The statement as previously formalized -/

/-- The statement of Claim 3.7 exactly as it was formalized in this file, packaged as a
`Prop` and specialized to `Type 0`.  `not_claim37Statement` refutes it. -/
def Claim37Statement : Prop :=
  ∀ (A : Type) [Fintype A] [Nonempty A] [DecidableEq A]
    (η : Config A) (S_φ : Finset (ℤ × ℤ)), IsGeneratingSet η S_φ →
    ∀ (x_per : Config A), IsFullyPeriodic x_per → x_per ∈ orbitClosure η →
    ∀ (ϑ : Config A), ϑ ∈ orbitClosure η →
    ∀ (A_infty : ℕ → Set (ℤ × ℤ)) (ε : ℕ),
      (∀ z ∈ A_infty ε, ϑ z = x_per z) →
      (∃ z ∈ A_infty (ε + 1), ϑ z ≠ x_per z) →
    ∀ (v : ℤ × ℤ), Primitive v → v ≠ 0 →
      ¬ ∃ y : Config A, IsFullyPeriodic y ∧
        (∀ (W : Finset (ℤ × ℤ)) (M : ℕ),
          ∃ t : ℕ, M ≤ t ∧ ∀ z ∈ W, y z = (T ((t : ℤ) • v) ϑ) z)

/-! ## §2. The counterexample

Alphabet `Bool`; `η` is the indicator of the vertical line through the origin.
-/

namespace Counterexample

/-- The indicator of the vertical line `{z : z.1 = 0}`. -/
def eta : Config Bool := fun z => decide (z.1 = 0)

/-- The constant `false` configuration. -/
def zeroCfg : Config Bool := fun _ => false

theorem zeroCfg_fp : IsFullyPeriodic zeroCfg :=
  ⟨(1, 0), by rw [mem_Per_iff]; rfl, (0, 1), by rw [mem_Per_iff]; rfl, by decide⟩

/-- Every member of the orbit closure of `eta` is invariant under the vertical shift. -/
theorem vert_inv {x : Config Bool} (hx : x ∈ orbitClosure eta) (z : ℤ × ℤ) :
    x (z + (0, 1)) = x z := by
  classical
  obtain ⟨u, hu⟩ := hx {z, z + (0, 1)}
  have h1 : x z = eta (u + z) := hu z (by simp)
  have h2 : x (z + (0, 1)) = eta (u + (z + (0, 1))) := hu _ (by simp)
  rw [h1, h2]
  simp [eta]

theorem vert_inv' {x : Config Bool} (hx : x ∈ orbitClosure eta) : x (0, 1) = x (0, 0) := by
  simpa using vert_inv hx (0, 0)

/-- The generating window `{(0,0), (0,1)}`. -/
def Sphi : Finset (ℤ × ℤ) := {(0, 0), (0, 1)}

theorem convex_slab : Convex ℝ {p : ℝ × ℝ | p.1 = 0 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1} := by
  intro p hp q hq a b ha hb hab
  obtain ⟨hp1, hp2, hp3⟩ := hp
  obtain ⟨hq1, hq2, hq3⟩ := hq
  refine ⟨?_, ?_, ?_⟩
  · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, hp1, hq1]; ring
  · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
    have := mul_nonneg ha hp2
    have := mul_nonneg hb hq2
    linarith
  · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
    nlinarith

theorem latticeConvex_Sphi : LatticeConvex Sphi := by
  intro z hz
  have hsub : Conv Sphi ⊆ {p : ℝ × ℝ | p.1 = 0 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1} := by
    apply convexHull_min _ convex_slab
    rintro _ ⟨w, hw, rfl⟩
    rw [Finset.mem_coe] at hw
    have hw' : w = (0, 0) ∨ w = (0, 1) := by simpa [Sphi] using hw
    rcases hw' with rfl | rfl <;>
      exact ⟨by norm_num [toReal], by norm_num [toReal], by norm_num [toReal]⟩
  obtain ⟨h1, h2, h3⟩ := hsub hz
  simp only [toReal] at h1 h2 h3
  have e1 : z.1 = 0 := by exact_mod_cast h1
  have e2 : (0 : ℤ) ≤ z.2 := by exact_mod_cast h2
  have e3 : z.2 ≤ 1 := by exact_mod_cast h3
  have e4 : z.2 = 0 ∨ z.2 = 1 := by omega
  rcases e4 with h | h <;> simp [Sphi, Prod.ext_iff, e1, h]

theorem isGeneratingSet_eta : IsGeneratingSet eta Sphi := by
  refine ⟨⟨(0, 0), by simp [Sphi]⟩, latticeConvex_Sphi, ?_⟩
  intro a ha _
  have ha' : a = (0, 0) ∨ a = (0, 1) := by simpa [Sphi] using ha
  rcases ha' with rfl | rfl
  · refine ⟨ha, ?_⟩
    intro x hx y hy hagree
    have h01 : x (0, 1) = y (0, 1) := hagree (0, 1) (by decide)
    rw [← vert_inv' hx, ← vert_inv' hy, h01]
  · refine ⟨ha, ?_⟩
    intro x hx y hy hagree
    have h00 : x (0, 0) = y (0, 0) := hagree (0, 0) (by decide)
    rw [vert_inv' hx, vert_inv' hy, h00]

/-- A horizontal shift pushing a whole finite window strictly to the right of column `0`. -/
def shift (W : Finset (ℤ × ℤ)) : ℤ := ∑ w ∈ W, (1 + |w.1|)

theorem shift_nonneg (W : Finset (ℤ × ℤ)) : 0 ≤ shift W :=
  Finset.sum_nonneg fun w _ => by positivity

theorem le_shift {W : Finset (ℤ × ℤ)} {w : ℤ × ℤ} (hw : w ∈ W) : 1 + |w.1| ≤ shift W :=
  Finset.single_le_sum (f := fun w : ℤ × ℤ => 1 + |w.1|) (fun i _ => by positivity) hw

theorem zeroCfg_mem : zeroCfg ∈ orbitClosure eta := by
  intro W
  refine ⟨(shift W, 0), ?_⟩
  intro w hw
  have h := le_shift hw
  have habs : -w.1 ≤ |w.1| := neg_le_abs _
  have hne : shift W + w.1 ≠ 0 := by omega
  simp [zeroCfg, eta, hne]

/-- The constant-`false` configuration is an accumulation point of `{T^{t·(1,0)}η}`. -/
theorem acc : ∀ (W : Finset (ℤ × ℤ)) (M : ℕ), ∃ t : ℕ, M ≤ t ∧
    ∀ z ∈ W, zeroCfg z = (T ((t : ℤ) • ((1, 0) : ℤ × ℤ)) eta) z := by
  intro W M
  refine ⟨M + (shift W).toNat, Nat.le_add_right _ _, ?_⟩
  intro z hz
  have h := le_shift hz
  have habs : -z.1 ≤ |z.1| := neg_le_abs _
  have hcast : ((shift W).toNat : ℤ) = shift W := Int.toNat_of_nonneg (shift_nonneg W)
  have hM : (0 : ℤ) ≤ (M : ℤ) := Int.natCast_nonneg M
  have key : z.1 + ((M : ℤ) + shift W) ≠ 0 := by omega
  simp only [T_apply, zeroCfg, eta, Prod.smul_def, smul_eq_mul, Nat.cast_add, hcast,
    mul_one, mul_zero]
  simpa using key

end Counterexample

/-! ## §3. Refutation -/

open Counterexample in
/-- **The statement of Claim 3.7 as previously formalized is false.**

Witness: `η = ϑ` the indicator of a vertical line, `x_per` the constant-`false`
configuration, `S_φ = {(0,0),(0,1)}`, `A_infty 0 = ∅`, `A_infty (n+1) = univ`, `v = (1,0)`.
Shifting the line horizontally to infinity converges to `x_per`, which is fully periodic. -/
theorem not_claim37Statement : ¬ Claim37Statement := by
  intro h
  exact h Bool eta Sphi isGeneratingSet_eta zeroCfg zeroCfg_fp zeroCfg_mem
    eta (self_mem_orbitClosure eta)
    (fun n => if n = 0 then ∅ else Set.univ) 0 (by simp)
    ⟨(0, 0), by simp, by simp [eta, zeroCfg]⟩
    (1, 0) isCoprime_one_left (by decide)
    ⟨zeroCfg, zeroCfg_fp, acc⟩

/-! ## §4. What survives: the generating-set extension (the paper's Step 3)

`GenClosure`/`agree_on_genClosure` moved to `GenClosureDef.lean` (Round 80 step 2: `Lemma35.lean`
needs them and cannot import this file, which already imports `Lemma35.lean`). Re-exported here
under the same qualified names by the `import` below; nothing else in this section changed. -/

/-- **Colle, Claim 3.7, final step.**

The paper's proof ends: from a fully periodic accumulation point one extracts an extra
agreement window `D = Â_∞^(ε+1) ∩ (Q + t₀ v)`, and then "since `S_φ` is an η-generating
set, we may enlarge the set where `ϑ` and `x̂_per` coincide so that
`ϑ|_{Â_∞^(ε+1)} = x̂_per|_{Â_∞^(ε+1)}`, which contradicts (3.5)".

This theorem is exactly that last step, and it is proved: once such a `D` exists, the
disagreement hypothesis (3.5) is contradicted.  It mentions no accumulation point, so it
does not presuppose what Claim 3.7 asserts.

What is *missing* for Claim 3.7 is the production of `D`: that a fully periodic
accumulation point yields an agreement window from which `Â_∞^(ε+1)` is `S_φ`-generated.
That step uses the period of the accumulation point being parallel to `ℓ_m` and the
`(ℓ_m, ℓ_J)`-region structure of Lemma 3.5, neither of which is available here — and
`not_claim37Statement` shows it cannot be skipped. -/
theorem claim37_final_step {A : Type*} {η : Config A} {S_φ : Finset (ℤ × ℤ)}
    (hS_gen : IsGeneratingSet η S_φ)
    {x_per ϑ : Config A} (hx_orbit : x_per ∈ orbitClosure η) (hϑ_orbit : ϑ ∈ orbitClosure η)
    {A_infty : ℕ → Set (ℤ × ℤ)} {ε : ℕ}
    (h_agree : ∀ z ∈ A_infty ε, ϑ z = x_per z)
    {D : Set (ℤ × ℤ)} (hD : ∀ z ∈ D, ϑ z = x_per z)
    (hreach : ∀ z ∈ A_infty (ε + 1), GenClosure S_φ (A_infty ε ∪ D) z) :
    ∀ z ∈ A_infty (ε + 1), ϑ z = x_per z := by
  intro z hz
  refine agree_on_genClosure hS_gen hϑ_orbit hx_orbit ?_ z (hreach z hz)
  rintro w (hw | hw)
  · exact h_agree w hw
  · exact hD w hw

/-! ## §5. Non-degeneracy

The hypotheses of the refuted statement are simultaneously satisfiable — indeed the
counterexample of §2 satisfies all of them, which is exactly why the statement fails.
-/

open Counterexample in
/-- All hypotheses of the refuted `Claim37Statement` can be met simultaneously. -/
theorem claim37_nondegenerate :
    ∃ (A : Type) (_ : Fintype A) (_ : Nonempty A) (_ : DecidableEq A)
      (η : Config A) (S_φ : Finset (ℤ × ℤ))
      (x_per ϑ : Config A) (A_infty : ℕ → Set (ℤ × ℤ)) (ε : ℕ) (v : ℤ × ℤ),
      IsGeneratingSet η S_φ ∧
      IsFullyPeriodic x_per ∧ x_per ∈ orbitClosure η ∧
      ϑ ∈ orbitClosure η ∧
      (∀ z ∈ A_infty ε, ϑ z = x_per z) ∧
      (∃ z ∈ A_infty (ε + 1), ϑ z ≠ x_per z) ∧
      Primitive v ∧ v ≠ 0 :=
  ⟨Bool, inferInstance, inferInstance, inferInstance, eta, Sphi, zeroCfg, eta,
    (fun n => if n = 0 then ∅ else Set.univ), 0, (1, 0),
    isGeneratingSet_eta, zeroCfg_fp, zeroCfg_mem, self_mem_orbitClosure eta,
    (by simp), ⟨(0, 0), by simp, by simp [eta, zeroCfg]⟩,
    isCoprime_one_left, (by decide)⟩

/-! ## §6. Assessment of the not_E_inter_subset refutation

`RegionEdges.not_E_inter_subset` proves that `E(R ∩ ℋ(k, b)) ⊆ E(R) ∪ {k}` is false.
Claim 3.7 does not use `Enveloped` or `E(·)` under intersection: it uses `S_φ` as a
generating set (`agree_on_genClosure`).  So that refutation is not the reason the
formalized statement above fails; the reason is the missing `(ℓ_m, ℓ_J)`-region structure.

**This assessment is deliberately left as prose and is NOT stated as a theorem.**  An
earlier revision carried

```lean
theorem claim37_independent_of_E_inter :
    ∀ (R : Set (ℤ × ℤ)) (k : ℤ × ℤ) (b : ℤ),
      ¬ (E (R ∩ halfPlaneLE k b) ⊆ E R ∪ {k}) → True := by
  intro R k b _
  trivial
```

which concludes `True` and is therefore proved by `trivial` for any antecedent whatsoever.
It carried **zero** mathematical content while its name and docstring claimed to establish
independence from `not_E_inter_subset` — a declaration that misleads an auditor into
thinking a scope question had been settled formally.  Removed 2026-09-13.

A genuine formal version would have to quantify over the *uses* of `E(·)` in this file and
show none occurs, which is a statement about the development rather than about `ℤ²`, and so
is not expressible as a theorem here.  Prose is the honest form for it.
-/

/-! ## §7. Windows

Colle's squares `Q = [-i,i]² ∩ ℤ²` and their translates `Q + u`.  The name is `win` rather
than `box` because `Nivat.LE2.box` already exists and this file opens `Nivat.LE2`.
-/

/-- The square window of radius `i` centred at `u`: Colle's `Q + u` with `Q = [-i,i]²`. -/
noncomputable def win (i : ℕ) (u : ℤ × ℤ) : Finset (ℤ × ℤ) :=
  Finset.Icc (u.1 - (i : ℤ)) (u.1 + (i : ℤ)) ×ˢ Finset.Icc (u.2 - (i : ℤ)) (u.2 + (i : ℤ))

theorem mem_win {i : ℕ} {u z : ℤ × ℤ} :
    z ∈ win i u ↔ (u.1 - (i : ℤ) ≤ z.1 ∧ z.1 ≤ u.1 + (i : ℤ)) ∧
      (u.2 - (i : ℤ) ≤ z.2 ∧ z.2 ≤ u.2 + (i : ℤ)) := by
  simp [win, Finset.mem_product, Finset.mem_Icc]

/-- The same window as a `Set`. -/
noncomputable def winS (i : ℕ) (u : ℤ × ℤ) : Set (ℤ × ℤ) := (win i u : Set (ℤ × ℤ))

theorem mem_winS {i : ℕ} {u z : ℤ × ℤ} :
    z ∈ winS i u ↔ (u.1 - (i : ℤ) ≤ z.1 ∧ z.1 ≤ u.1 + (i : ℤ)) ∧
      (u.2 - (i : ℤ) ≤ z.2 ∧ z.2 ≤ u.2 + (i : ℤ)) := by
  rw [winS, Finset.mem_coe, mem_win]

/-! ## §8. A corrected statement of Claim 3.7

`not_claim37Statement` (§3) refutes the old formalization because it quantified over an
*arbitrary* family `A_infty`.  This section restores the two properties of the
`(ℓ_m, ℓ_J)`-region that Colle's proof actually consumes, as an explicit hypothesis bundle.

### Why a bespoke bundle rather than `Colle35.ChainData`

Two independent reasons, both checked:

1. `ColleRegion.lean`, `RegionEdges.lean` and `Lemma35Wiring.lean` are **not** in this
   file's import closure (this file imports only `Lemma35`, `Lemma45`, `Generating`), so
   `ChainData`'s wiring is not reachable from here.
2. `ChainData.Env` is a free data field, which makes `Nonempty (ChainData ...)` strictly
   weaker than Lemma 3.5 itself; depending on it would buy nothing and would couple this
   file to another agent's in-flight edits.

Stating the bundle here makes the dependency on Lemma 3.5 **legible**: `RegionLayers` is
exactly the list of things that must later be discharged from the region construction.

### Justification of each field against Colle's text

* `A`, `ε` — the layers `Â_∞^(ε)`, `Â_∞^(ε+1)` of equation (3.5).  Present in the paper
  verbatim.
* `Sphi` — the η-generating set `S_φ`.  Present verbatim.
* `v_m` — a direction vector for the line `ℓ_m`.  Colle's sentence *"and thus periodic with
  period parallel to ℓ_m"* and *"Since x̂_per is periodic with period parallel to ℓ_m"* both
  refer to it.
* `v` — the direction `v_{ℓ'}` along which the orbit `{T^{t·v_{ℓ'}}ϑ}` is taken.  Present
  verbatim in the claim's statement.
* `v_m_ne : v_m ≠ 0` — `ℓ_m` is a line, so its direction vector is nonzero.  Needed only to
  know the common period constructed in the proof is not `0`.
* `reach` — the geometric content of *"the set Q ∩ Â_∞^(ε) can be taken as large as we
  want"*.  Formally: sliding any nonzero vector parallel to `ℓ_m` moves every site of
  `Â_∞^(ε+1)` into `Â_∞^(ε)` within a bounded number of steps.  This is the property that
  distinguishes the paper's layered region from the arbitrary `A_infty` of §3: it says the
  inner layer is *reachable* from the outer one along `ℓ_m`, uniformly.  It is precisely
  what the §3 counterexample's `A_infty 0 = ∅` fails to provide (see `reach_fails_of_empty`).
* `gen` — the reachability of `Â_∞^(ε+1)` from `Â_∞^(ε)` together with one far square
  `Q + t₀·v` by repeated `S_φ`-generation.  This is Colle's closing sentence *"Since S_φ is
  an η-generating set, we may enlarge the set where ϑ and x̂_per coincide so that
  ϑ|_{Â_∞^(ε+1)} = x̂_per|_{Â_∞^(ε+1)}"*.

**WITHDRAWN 2026-09-16 — the flag below was wrong.**  It used to read:

> **HONESTY FLAG on `gen`.** That closing sentence is, in the paper, an *unjustified*
> induction: Colle asserts the enlargement without exhibiting the order in which sites are
> forced, and the generating property alone does not supply it […].  `gen` therefore
> records a gap in **Colle's argument**, not an artifact of this formalization.

The forcing order *is* in the paper; it was missed because the OCR of
`colle_full.txt` drops the subscripts of the displayed formulas.  Checked against the
original LaTeX (`delivery/scratch/b3_colle.html`, the `alttext` attributes):

* `b3_colle.html:743` gives the layer formula in full,
  `Â_∞^(ε) := {g + t·v_{ℓ_{J−1}} : g ∈ Â_∞, t ∈ ℤ₊, dist(g + t·v_{ℓ_{J−1}}, ℓ_J) ≤ d_ε}`;
* `colle_full.txt:641-642` says of the sequence `0 = d₀ < d₁ < ⋯`: *"is the sequence where,
  for each `g ∈ ℋ(ℓ_J)`, there exists `i ∈ ℤ₊` such that `Dist(g, ℓ_J) = d_i`"* — i.e.
  `{d_i}` enumerates **every** distance to `ℓ_J` realised by a lattice point of the
  half-plane, with nothing skipped.

Consequently `Â_∞^(ε+1) ∖ Â_∞^(ε) = {g : Dist(g, ℓ_J) = d_{ε+1}}` is a **single lattice line
parallel to `ℓ_J`**, not a two-dimensional annulus.  And `ℓ_J` is parallel to an edge of
`S_φ` (`colle_full.txt:605-607`).  So the enlargement is the one-dimensional induction
"start from the long already-known segment `Â_∞^(ε+1) ∩ (Q + t₀·v)` and extend one site at a
time along that line", each step forcing the next site from a window translate whose other
sites are already known — the same move the paper makes explicitly at `colle_full.txt:738`.

`gen` is therefore a **provable** statement about the layered region, not a gap in Colle.
Two thirds of that proof are now in the tree, both kernel-clean:

* `Nivat.MaxEnv.mem_shell_succ_iff` (`ShellLine.lean`) — the layer split above, for
  `Nivat.MaxEnv.shell` (`MaximalEnveloped.lean:563`), which *is* the `:440` formula;
* `Nivat.Colle37.gen_of_line` (`ShellGen.lean`) — the induction, producing literally this
  field's statement with `v := d`, and *constructing* the window radius `i` and the
  threshold `M` rather than assuming them.

What `gen_of_line` still consumes is geometry, not combinatorics: `LatticeConvex (S.erase a)`
at the two endpoints of the `ℓ_J`-edge of `S_φ`, and the "off the line" clauses, which say
`S_φ - a` lies in the recession cone of the `(ℓ_ι, ℓ_J)`-region `Â_∞^(ε+1)`
(`b3_colle2.txt:440` asserts the shell *is* such a region).  The remaining wiring step is
`ChainData.shellInf` (`Lemma35.lean:711`), which is declared opaque; see
`delivery/blueprint/NOTE.md`, entry "ChainData.shellInf 丢掉了 Â^{(ε)} 的公式 — 2026-09-16"
and its 更正.

### Why no hypothesis can secretly imply the conclusion

The single most dangerous failure mode when *designing* a hypothesis list is a hypothesis
that already contains the conclusion.  The structural guard used here: **every field of
`RegionLayers` is config-free.**  `reach` and `gen` mention only `A`, `ε`, `Sphi`, `v_m`,
`v` — never `η`, `ϑ`, `x_per`, or the accumulation point `y`.  A statement that does not
mention `ϑ` or `y` cannot assert anything about accumulation points of `{T^{t·v}ϑ}`, so
neither field can smuggle in the conclusion.  Only `IsGeneratingSet η Sphi` and the
agreement/disagreement hypotheses mention configurations, and those three are already
present in the refuted statement of §1.

### Hypotheses of §1 that were *dropped*, making `claim37` strictly stronger

`IsFullyPeriodic x_per` (replaced by the weaker `hxp_par`, which is what the proof uses),
`Primitive v_m`, `Primitive v`, `v ≠ 0`, and layer monotonicity `A ε ⊆ A (ε+1)`.  None is
needed.
-/

/-- The properties of Colle's `(ℓ_m, ℓ_J)`-region layers that the proof of Claim 3.7
consumes.  See the section docstring above for the justification of each field, and for the
argument that every field is config-free and therefore cannot imply Claim 3.7's conclusion.

`Witness.witnessRegion` is an inhabitant, so this bundle is not vacuous. -/
structure RegionLayers where
  /-- The layers `Â_∞^(n)` of equation (3.5). -/
  A : ℕ → Set (ℤ × ℤ)
  /-- The index at which agreement holds and fails one layer out. -/
  ε : ℕ
  /-- The η-generating set `S_φ`. -/
  Sphi : Finset (ℤ × ℤ)
  /-- A direction vector for the line `ℓ_m`. -/
  v_m : ℤ × ℤ
  /-- The direction `v_{ℓ'}` of the orbit in the statement of the claim. -/
  v : ℤ × ℤ
  /-- `ℓ_m` is a line, so its direction is nonzero. -/
  v_m_ne : v_m ≠ 0
  /-- *"the set `Q ∩ Â_∞^(ε)` can be taken as large as we want"*: sliding along `ℓ_m`
  carries every site of the outer layer into the inner layer in boundedly many steps. -/
  reach : ∀ p : ℤ × ℤ, p ≠ 0 → (∃ n : ℤ, p = n • v_m) →
    ∃ N : ℕ, ∀ z ∈ A (ε + 1), ∃ k : ℤ,
      |k * p.1| ≤ (N : ℤ) ∧ |k * p.2| ≤ (N : ℤ) ∧ z + k • p ∈ A ε
  /-- *"Since `S_φ` is an η-generating set, we may enlarge the set where `ϑ` and `x̂_per`
  coincide"*: the outer layer is `S_φ`-generated from the inner layer plus one far square.
  This is a **provable** statement about the layered region, not a gap in Colle; see the
  section docstring, and `Nivat.Colle37.gen_of_line` (`ShellGen.lean`), which derives exactly
  this shape from the line structure of the top layer. -/
  gen : ∃ i M : ℕ, ∀ t : ℕ, M ≤ t →
    ∀ z ∈ A (ε + 1), GenClosure Sphi (A ε ∪ (A (ε + 1) ∩ winS i ((t : ℤ) • v))) z

/-- **Colle, Claim 3.7 — corrected statement, proved.**

> The set `{T^{t·v_ℓ'}ϑ : t ∈ ℤ_+}` does not have fully periodic accumulation points.

The difference from the refuted `Claim37Statement` of §1 is the bundle `R : RegionLayers`,
which supplies the two region properties Colle's proof uses and the old statement discarded.
`hxp_par` replaces `IsFullyPeriodic x_per` by exactly what the proof needs: `x̂_per` has a
nonzero period parallel to `ℓ_m`.

**Proof (the paper's Steps 1–3).**

*Step 1.* A fully periodic `y` has a finite-index period subgroup, hence
`DoublyPeriodic.exists_smul_mem` gives `n₁ ≠ 0` with `n₁ • w ∈ Per y` for every `w`; in
particular `n₁ • v_m ∈ Per y`.  With `hxp_par`'s `n₂ • v_m ∈ Per x_per`, the vector
`p = (n₁ n₂) • v_m` is a **common** nonzero period of `y` and `x̂_per`, parallel to `ℓ_m`.

*Step 2 (the step missing before).*  Accumulation on the square `win (i + N) 0` gives `t ≥ M`
with `y = T^{t·v} ϑ` on that whole square.  For `z` in `Â_∞^(ε+1) ∩ (Q_i + t·v)`, `reach`
supplies `k` with `z + k·p ∈ Â_∞^(ε)` and `k·p` of size at most `N`, so both `z - t·v` and
`z - t·v + k·p` lie in the larger square, and

  `ϑ z = y (z - t·v) = y (z - t·v + k·p) = ϑ (z + k·p) = x̂_per (z + k·p) = x̂_per z`,

using `p ∈ Per y` for the second equality, agreement on `Â_∞^(ε)` for the fourth, and
`p ∈ Per x_per` for the fifth.  Note only the two *endpoints* need to lie in the window:
`y` is globally periodic and matches `ϑ` on the whole square at once, so no chain of
intermediate sites is required.

*Step 3.*  `gen` and `claim37_final_step` (§4) spread the agreement over all of
`Â_∞^(ε+1)`, contradicting the disagreement hypothesis (3.5). -/
theorem claim37 {α : Type*} {η : Config α} (R : RegionLayers)
    (hS : IsGeneratingSet η R.Sphi)
    {x_per ϑ : Config α}
    (hxp_par : ∃ n : ℤ, n ≠ 0 ∧ n • R.v_m ∈ Per x_per)
    (hxp_orb : x_per ∈ orbitClosure η) (hϑ_orb : ϑ ∈ orbitClosure η)
    (h_agree : ∀ z ∈ R.A R.ε, ϑ z = x_per z)
    (h_disagree : ∃ z ∈ R.A (R.ε + 1), ϑ z ≠ x_per z) :
    ¬ ∃ y : Config α, IsFullyPeriodic y ∧
        ∀ (W : Finset (ℤ × ℤ)) (M : ℕ), ∃ t : ℕ, M ≤ t ∧
          ∀ z ∈ W, y z = T ((t : ℤ) • R.v) ϑ z := by
  rintro ⟨y, hy_fp, hacc⟩
  obtain ⟨n₂, hn₂, hn₂mem⟩ := hxp_par
  obtain ⟨n₁, hn₁, hn₁mem⟩ := DoublyPeriodic.exists_smul_mem hy_fp
  -- Step 1: the common period `p = (n₁ * n₂) • v_m`, parallel to `ℓ_m`
  set p : ℤ × ℤ := (n₁ * n₂) • R.v_m with hp_def
  have hp_y : p ∈ Per y := by
    rw [hp_def, mul_comm, mul_smul]; exact AddSubgroup.zsmul_mem _ (hn₁mem _) _
  have hp_x : p ∈ Per x_per := by
    rw [hp_def, mul_smul]; exact AddSubgroup.zsmul_mem _ hn₂mem _
  have hp_ne : p ≠ 0 := by
    rw [hp_def]
    intro hc
    have h1 : (n₁ * n₂) * R.v_m.1 = 0 := by
      have := congrArg Prod.fst hc; simpa using this
    have h2 : (n₁ * n₂) * R.v_m.2 = 0 := by
      have := congrArg Prod.snd hc; simpa using this
    have hn : n₁ * n₂ ≠ 0 := mul_ne_zero hn₁ hn₂
    refine R.v_m_ne (Prod.ext ?_ ?_)
    · rcases mul_eq_zero.mp h1 with h | h
      · exact absurd h hn
      · simpa using h
    · rcases mul_eq_zero.mp h2 with h | h
      · exact absurd h hn
      · simpa using h
  obtain ⟨N, hreach⟩ := R.reach p hp_ne ⟨n₁ * n₂, rfl⟩
  obtain ⟨i, M, hgen⟩ := R.gen
  obtain ⟨t, htM, hty⟩ := hacc (win (i + N) 0) M
  -- Step 2: the agreement window produced by the accumulation point.
  -- `u` is kept opaque so that the window arithmetic is pure `omega`.
  have key : ∀ u : ℤ × ℤ, (∀ w ∈ win (i + N) (0 : ℤ × ℤ), y w = ϑ (w + u)) →
      ∀ z ∈ R.A (R.ε + 1) ∩ winS i u, ϑ z = x_per z := by
    rintro u hu z ⟨hzA, hzwin⟩
    obtain ⟨k, hk1, hk2, hkA⟩ := hreach z hzA
    rw [mem_winS] at hzwin
    have hb1 := abs_le.mp hk1
    have hb2 := abs_le.mp hk2
    have hkp1 : (k • p).1 = k * p.1 := by simp
    have hkp2 : (k • p).2 = k * p.2 := by simp
    have hz' : z - u ∈ win (i + N) (0 : ℤ × ℤ) := by
      rw [mem_win]
      simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero, Nat.cast_add]
      omega
    have hz'' : z - u + k • p ∈ win (i + N) (0 : ℤ × ℤ) := by
      rw [mem_win]
      simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_zero,
        Prod.snd_zero, Nat.cast_add, hkp1, hkp2]
      omega
    have e1 : y (z - u) = ϑ z := by
      have h := hu _ hz'; rw [h]; congr 1; abel
    have e2 : y (z - u + k • p) = ϑ (z + k • p) := by
      have h := hu _ hz''; rw [h]; congr 1; abel
    have e3 : y (z - u + k • p) = y (z - u) :=
      Per.apply (AddSubgroup.zsmul_mem _ hp_y k) _
    have e4 : ϑ (z + k • p) = x_per (z + k • p) := h_agree _ hkA
    have e5 : x_per (z + k • p) = x_per z :=
      Per.apply (AddSubgroup.zsmul_mem _ hp_x k) z
    rw [← e1, ← e3, e2, e4, e5]
  have step2 : ∀ z ∈ R.A (R.ε + 1) ∩ winS i ((t : ℤ) • R.v), ϑ z = x_per z :=
    key ((t : ℤ) • R.v) (fun w hw => by have h := hty w hw; rwa [T_apply] at h)
  -- Step 3: spread the agreement over the whole layer, contradicting (3.5)
  obtain ⟨z₀, hz₀, hne⟩ := h_disagree
  exact hne (claim37_final_step hS hxp_orb hϑ_orb h_agree step2 (hgen t htM) z₀ hz₀)

/-! ## §9. `GenClosure` for the two-point window `S_φ = {(0,0), (0,1)}`

These are used twice: to build the satisfiability witness of §10, and to prove in §11 that
the counterexample of §2 cannot satisfy `RegionLayers.gen`.  The content is that this
particular `S_φ` propagates information along vertical lines and only along vertical lines.
-/

open Counterexample in
theorem latticeConvex_singleton (a : ℤ × ℤ) : LatticeConvex ({a} : Finset (ℤ × ℤ)) := by
  intro z hz
  rw [Conv, Finset.coe_singleton, Set.image_singleton, convexHull_singleton,
    Set.mem_singleton_iff] at hz
  rw [Finset.mem_singleton]
  exact toReal_injective hz

open Counterexample in
theorem erase00 : Sphi.erase (0, 0) = {((0 : ℤ), (1 : ℤ))} := by decide

open Counterexample in
theorem erase01 : Sphi.erase (0, 1) = {((0 : ℤ), (0 : ℤ))} := by decide

open Counterexample in
/-- From a known site, `Sphi`-generation reaches every site above it. -/
theorem genUp {D : Set (ℤ × ℤ)} {x t : ℤ} (h : GenClosure Sphi D (x, t)) :
    ∀ j : ℕ, GenClosure Sphi D (x, t + (j : ℤ)) := by
  intro j
  induction j with
  | zero => simpa using h
  | succ n ih =>
      have hprem : ∀ b ∈ Sphi.erase ((0 : ℤ), (1 : ℤ)),
          GenClosure Sphi D (b + (x, t + (n : ℤ))) := by
        intro b hb
        rw [erase01, Finset.mem_singleton] at hb
        subst hb
        simpa using ih
      have hstep := GenClosure.step (S := Sphi) (D := D) (a := ((0 : ℤ), (1 : ℤ)))
        (w := (x, t + (n : ℤ))) (by decide)
        (by rw [erase01]; exact latticeConvex_singleton _) hprem
      have heq : ((0 : ℤ), (1 : ℤ)) + (x, t + (n : ℤ)) = (x, t + ((n + 1 : ℕ) : ℤ)) := by
        push_cast
        exact Prod.ext (by simp) (by simp; ring)
      rwa [heq] at hstep

open Counterexample in
/-- From a known site, `Sphi`-generation reaches every site below it. -/
theorem genDown {D : Set (ℤ × ℤ)} {x t : ℤ} (h : GenClosure Sphi D (x, t)) :
    ∀ j : ℕ, GenClosure Sphi D (x, t - (j : ℤ)) := by
  intro j
  induction j with
  | zero => simpa using h
  | succ n ih =>
      have hprem : ∀ b ∈ Sphi.erase ((0 : ℤ), (0 : ℤ)),
          GenClosure Sphi D (b + (x, t - ((n : ℤ) + 1))) := by
        intro b hb
        rw [erase00, Finset.mem_singleton] at hb
        subst hb
        have heq2 : ((0 : ℤ), (1 : ℤ)) + (x, t - ((n : ℤ) + 1)) = (x, t - (n : ℤ)) :=
          Prod.ext (by simp) (by simp; ring)
        rw [heq2]; exact ih
      have hstep := GenClosure.step (S := Sphi) (D := D) (a := ((0 : ℤ), (0 : ℤ)))
        (w := (x, t - ((n : ℤ) + 1))) (by decide)
        (by rw [erase00]; exact latticeConvex_singleton _) hprem
      have heq : ((0 : ℤ), (0 : ℤ)) + (x, t - ((n : ℤ) + 1)) = (x, t - ((n + 1 : ℕ) : ℤ)) := by
        push_cast
        exact Prod.ext (by simp) (by simp)
      rwa [heq] at hstep

open Counterexample in
/-- `Sphi`-generation propagates along a whole vertical line. -/
theorem genVert {D : Set (ℤ × ℤ)} {x t : ℤ} (h : GenClosure Sphi D (x, t)) (m : ℤ) :
    GenClosure Sphi D (x, m) := by
  by_cases hle : t ≤ m
  · have hx := genUp h (m - t).toNat
    rwa [Int.toNat_of_nonneg (by omega), show t + (m - t) = m by ring] at hx
  · have hx := genDown h (t - m).toNat
    rwa [Int.toNat_of_nonneg (by omega), show t - (t - m) = m by ring] at hx

open Counterexample in
/-- `Sphi`-generation moves only vertically, so it cannot change a first coordinate.
This is the engine of `counterexample_violates_gen`. -/
theorem genClosure_Sphi_fst_ne {D : Set (ℤ × ℤ)} (hD : ∀ z ∈ D, z.1 ≠ 0) :
    ∀ z, GenClosure Sphi D z → z.1 ≠ 0 := by
  intro z hz
  induction hz with
  | base hz => exact hD _ hz
  | @step a w ha _ _ ih =>
      have ha' : a = (0, 0) ∨ a = (0, 1) := by simpa [Sphi] using ha
      have hb : ∃ b, b ∈ Sphi.erase a ∧ b.1 = 0 := by
        rcases ha' with rfl | rfl
        · exact ⟨(0, 1), by rw [erase00]; decide, rfl⟩
        · exact ⟨(0, 0), by rw [erase01]; decide, rfl⟩
      obtain ⟨b, hbmem, hb1⟩ := hb
      have hw : (b + w).1 ≠ 0 := ih b hbmem
      have ha1 : a.1 = 0 := by rcases ha' with rfl | rfl <;> rfl
      simp only [Prod.fst_add, hb1, zero_add] at hw
      simpa [Prod.fst_add, ha1] using hw

/-! ## §10. Non-degeneracy of the new statement

**This section is mandatory, not decorative.**  A hypothesis bundle nobody can satisfy would
make `claim37` vacuously true, and this project has shipped six such definitions already
(two of them literally `:= ∅` and `:= False`).  So `RegionLayers` gets an explicit
inhabitant *together with* configuration data satisfying every remaining hypothesis of
`claim37`, and then `claim37` is actually applied to it to produce a nontrivial conclusion.

The witness: `η = ϑ` is the indicator of the vertical line `{z : z.1 = 1}`, `x_per` is the
constant-`false` configuration, `S_φ = {(0,0),(0,1)}`, the layers are the half-planes
`A n = {z : z.1 ≤ n}` with `ε = 0`, `v_m = (1,0)` and `v = (0,1)`.  Sliding along
`v_m = (1,0)` crosses the layer boundary, which is what `reach` needs; `v = (0,1)` is the
direction in which `η` is already periodic, which is what makes the conclusion of `claim37`
verifiable by hand — see `witness_no_fully_periodic_acc`.
-/

namespace Witness

open Counterexample

/-- The indicator of the vertical line `{z : z.1 = 1}`. -/
def eta1 : Config Bool := fun z => decide (z.1 = 1)

theorem vert_inv1 {x : Config Bool} (hx : x ∈ orbitClosure eta1) (z : ℤ × ℤ) :
    x (z + (0, 1)) = x z := by
  classical
  obtain ⟨u, hu⟩ := hx {z, z + (0, 1)}
  have h1 : x z = eta1 (u + z) := hu z (by simp)
  have h2 : x (z + (0, 1)) = eta1 (u + (z + (0, 1))) := hu _ (by simp)
  rw [h1, h2]
  simp [eta1]

theorem vert_inv1' {x : Config Bool} (hx : x ∈ orbitClosure eta1) : x (0, 1) = x (0, 0) := by
  simpa using vert_inv1 hx (0, 0)

theorem isGeneratingSet_eta1 : IsGeneratingSet eta1 Sphi := by
  refine ⟨⟨(0, 0), by simp [Sphi]⟩, latticeConvex_Sphi, ?_⟩
  intro a ha _
  have ha' : a = (0, 0) ∨ a = (0, 1) := by simpa [Sphi] using ha
  rcases ha' with rfl | rfl
  · refine ⟨ha, ?_⟩
    intro x hx y hy hagree
    have h01 : x (0, 1) = y (0, 1) := hagree (0, 1) (by decide)
    rw [← vert_inv1' hx, ← vert_inv1' hy, h01]
  · refine ⟨ha, ?_⟩
    intro x hx y hy hagree
    have h00 : x (0, 0) = y (0, 0) := hagree (0, 0) (by decide)
    rw [vert_inv1' hx, vert_inv1' hy, h00]

theorem zeroCfg_mem1 : zeroCfg ∈ orbitClosure eta1 := by
  intro W
  refine ⟨(shift W + 1, 0), ?_⟩
  intro w hw
  have h := le_shift hw
  have habs : -w.1 ≤ |w.1| := neg_le_abs _
  have hne : shift W + 1 + w.1 ≠ 1 := by omega
  simp [zeroCfg, eta1, hne]

/-- The layers: `A n = {z : z.1 ≤ n}`, a half-plane chain advancing one column at a time.
This is the simplest set family with the geometry Colle's `(ℓ_m, ℓ_J)`-region has in the
`ℓ_m`-direction: sliding along `v_m = (1,0)` crosses the boundary. -/
def Alayer : ℕ → Set (ℤ × ℤ) := fun n => {z | z.1 ≤ (n : ℤ)}

theorem witness_reach : ∀ p : ℤ × ℤ, p ≠ 0 → (∃ n : ℤ, p = n • ((1, 0) : ℤ × ℤ)) →
    ∃ N : ℕ, ∀ z ∈ Alayer (0 + 1), ∃ k : ℤ,
      |k * p.1| ≤ (N : ℤ) ∧ |k * p.2| ≤ (N : ℤ) ∧ z + k • p ∈ Alayer 0 := by
  rintro p hp ⟨n, rfl⟩
  have hp1 : (n • ((1, 0) : ℤ × ℤ)).1 = n := by simp
  have hp2 : (n • ((1, 0) : ℤ × ℤ)).2 = 0 := by simp
  have hn : n ≠ 0 := by
    intro h; apply hp; rw [h]; simp
  refine ⟨n.natAbs, ?_⟩
  intro z hz
  have hz1 : z.1 ≤ 1 := by simpa [Alayer] using hz
  refine ⟨if z.1 ≤ 0 then 0 else (if 0 < n then -1 else 1), ?_, ?_, ?_⟩
  · rw [hp1, abs_le]; split_ifs <;> omega
  · rw [hp2]; simp
  · show (z + _ • _).1 ≤ ((0 : ℕ) : ℤ)
    simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, hp1, Nat.cast_zero]
    split_ifs <;> omega

theorem witness_gen : ∃ i M : ℕ, ∀ t : ℕ, M ≤ t →
    ∀ z ∈ Alayer (0 + 1),
      GenClosure Sphi
        (Alayer 0 ∪ (Alayer (0 + 1) ∩ winS i ((t : ℤ) • ((0, 1) : ℤ × ℤ)))) z := by
  refine ⟨1, 0, ?_⟩
  intro t _ z hz
  have hzle : z.1 ≤ 1 := by simpa [Alayer] using hz
  by_cases h0 : z.1 ≤ 0
  · exact GenClosure.base (Or.inl h0)
  · have hz1 : z.1 = 1 := by omega
    have hu : ((t : ℤ) • ((0, 1) : ℤ × ℤ)) = (0, (t : ℤ)) :=
      Prod.ext (by simp) (by simp)
    have hseed : ((1 : ℤ), (t : ℤ)) ∈
        Alayer 0 ∪ (Alayer (0 + 1) ∩ winS 1 ((t : ℤ) • ((0, 1) : ℤ × ℤ))) := by
      refine Or.inr ⟨by simp [Alayer], ?_⟩
      rw [mem_winS, hu]
      norm_num
    have hv := genVert (GenClosure.base hseed) z.2
    rwa [show ((1 : ℤ), z.2) = z from Prod.ext hz1.symm rfl] at hv

/-- A `RegionLayers` bundle that is actually inhabited, so `claim37` is not vacuous. -/
noncomputable def witnessRegion : RegionLayers where
  A := Alayer
  ε := 0
  Sphi := Sphi
  v_m := (1, 0)
  v := (0, 1)
  v_m_ne := by decide
  reach := witness_reach
  gen := witness_gen

/-- **Satisfiability witness.**  Every hypothesis of `claim37` other than the bundle itself
holds simultaneously for `η = ϑ = eta1`, `x_per = zeroCfg` and `witnessRegion`.  Together
with `witnessRegion` this discharges the degeneracy guard: `claim37` is not vacuously true.

Note the disagreement clause is genuine: `eta1 (1,0) = true ≠ false = zeroCfg (1,0)` and
`(1,0)` lies in `Alayer 1` but not `Alayer 0`. -/
theorem claim37_hypotheses_satisfiable :
    IsGeneratingSet eta1 witnessRegion.Sphi ∧
    (∃ n : ℤ, n ≠ 0 ∧ n • witnessRegion.v_m ∈ Per zeroCfg) ∧
    zeroCfg ∈ orbitClosure eta1 ∧
    eta1 ∈ orbitClosure eta1 ∧
    (∀ z ∈ witnessRegion.A witnessRegion.ε, eta1 z = zeroCfg z) ∧
    (∃ z ∈ witnessRegion.A (witnessRegion.ε + 1), eta1 z ≠ zeroCfg z) := by
  refine ⟨isGeneratingSet_eta1, ⟨1, one_ne_zero, ?_⟩, zeroCfg_mem1,
    self_mem_orbitClosure eta1, ?_, ⟨(1, 0), ?_, ?_⟩⟩
  · rw [mem_Per_iff]; rfl
  · intro z hz
    have hz0 : z.1 ≤ 0 := by simpa [witnessRegion, Alayer] using hz
    simp [eta1, zeroCfg]
    omega
  · show ((1 : ℤ), (0 : ℤ)) ∈ witnessRegion.A (witnessRegion.ε + 1)
    simp [witnessRegion, Alayer]
  · simp [eta1, zeroCfg]

/-- The bundle is not merely inhabited: `claim37` applied to it yields a conclusion that is
independently checkable by hand, which is a consistency test on `claim37` itself.

Indeed `eta1` is `(0,1)`-periodic, so `T^{t·(0,1)} eta1 = eta1` for every `t`, hence the only
accumulation point of the orbit is `eta1` itself; and `Per eta1` contains only vectors of the
form `(0, b)`, any two of which have determinant `0`, so `eta1` is not fully periodic.  The
conclusion below is therefore true and non-vacuous, and it is obtained here purely by
instantiating `claim37`. -/
theorem witness_no_fully_periodic_acc :
    ¬ ∃ y : Config Bool, IsFullyPeriodic y ∧
        ∀ (W : Finset (ℤ × ℤ)) (M : ℕ), ∃ t : ℕ, M ≤ t ∧
          ∀ z ∈ W, y z = T ((t : ℤ) • witnessRegion.v) eta1 z := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := claim37_hypotheses_satisfiable
  exact claim37 witnessRegion h1 h2 h3 h4 h5 h6

end Witness

/-! ## §11. The counterexample of §2 does NOT refute the new statement

Task discipline: if the new statement were *also* satisfied by the §2 counterexample, it
would be a restatement of the false thing.  So the blocking hypothesis is identified
explicitly, and as theorems rather than prose.

**Which hypothesis blocks it.**  The §2 data is `η = ϑ = eta` (indicator of the column
`z.1 = 0`), `x_per = zeroCfg`, `S_φ = Sphi`, `v = (1,0)`, and layers
`A_infty 0 = ∅`, `A_infty (n+1) = univ` with `ε = 0`.

* With *those* layers, `RegionLayers.reach` fails immediately: `reach` demands that every
  site of the outer layer slide into the inner layer, and the inner layer is empty
  (`reach_fails_of_empty`).
* `reach` alone is not the whole story, because other layer families for the same
  configuration data *do* satisfy `reach` (e.g. `A ε = {z : 1 ≤ z.1}`,
  `A (ε+1) = {z : 0 ≤ z.1}` with `v_m = (1,0)`).  The hypothesis that blocks the
  counterexample **for every possible choice of layers** is `RegionLayers.gen`
  (`counterexample_violates_gen`).  That is the stronger and the decisive statement.
-/

open Counterexample in
/-- `reach` fails outright whenever the inner layer is empty — which is exactly the shape of
the `A_infty` used by `not_claim37Statement` (`A_infty 0 = ∅`). -/
theorem reach_fails_of_empty {A : ℕ → Set (ℤ × ℤ)} {ε : ℕ} (h0 : A ε = ∅)
    (h1 : (A (ε + 1)).Nonempty) (p : ℤ × ℤ) :
    ¬ ∃ N : ℕ, ∀ z ∈ A (ε + 1), ∃ k : ℤ,
        |k * p.1| ≤ (N : ℤ) ∧ |k * p.2| ≤ (N : ℤ) ∧ z + k • p ∈ A ε := by
  rintro ⟨N, hN⟩
  obtain ⟨z, hz⟩ := h1
  obtain ⟨k, -, -, hk⟩ := hN z hz
  rw [h0] at hk
  exact hk

open Counterexample in
/-- **The counterexample of §2 cannot satisfy the new bundle, for *any* choice of layers.**

For the §2 data (`η = ϑ = eta`, `x_per = zeroCfg`, `S_φ = Sphi`, `v = (1,0)`), no family of
layers `A` satisfying the agreement/disagreement hypotheses can satisfy `gen`.  The reason is
structural: `Sphi` generates only vertically (`genClosure_Sphi_fst_ne`), so it can never
reach the column `z.1 = 0` where `eta` and `zeroCfg` disagree, while the far window
`Q + t·(1,0)` with `t := M + i + 1` misses that column entirely.

Consequently the machine-checked refutation `not_claim37Statement` of §3 does **not** apply
to `claim37`: `RegionLayers.gen` is the hypothesis it violates. -/
theorem counterexample_violates_gen
    (A : ℕ → Set (ℤ × ℤ)) (ε : ℕ)
    (h_agree : ∀ z ∈ A ε, eta z = zeroCfg z)
    (h_disagree : ∃ z ∈ A (ε + 1), eta z ≠ zeroCfg z) :
    ¬ ∃ i M : ℕ, ∀ t : ℕ, M ≤ t →
        ∀ z ∈ A (ε + 1),
          GenClosure Sphi (A ε ∪ (A (ε + 1) ∩ winS i ((t : ℤ) • ((1, 0) : ℤ × ℤ)))) z := by
  rintro ⟨i, M, hgen⟩
  obtain ⟨z₀, hz₀, hne⟩ := h_disagree
  -- the disagreement site sits on the column `z.1 = 0`
  have hz₀1 : z₀.1 = 0 := by
    by_contra hc
    exact hne (by simp [eta, zeroCfg, hc])
  -- pick a translate far enough right that the window misses that column
  set t : ℕ := M + i + 1 with ht
  have htM : M ≤ t := by omega
  have hu : ((t : ℤ) • ((1, 0) : ℤ × ℤ)) = ((t : ℤ), 0) := Prod.ext (by simp) (by simp)
  have hsub : ∀ z ∈ A ε ∪ (A (ε + 1) ∩ winS i ((t : ℤ) • ((1, 0) : ℤ × ℤ))), z.1 ≠ 0 := by
    rintro z (hz | ⟨-, hz⟩)
    · have := h_agree z hz
      simp only [eta, zeroCfg, decide_eq_false_iff_not] at this
      exact this
    · rw [mem_winS, hu] at hz
      have h1 : (t : ℤ) - (i : ℤ) ≤ z.1 := hz.1.1
      have h2 : (1 : ℤ) ≤ (t : ℤ) - (i : ℤ) := by
        rw [ht]; push_cast; omega
      omega
  exact genClosure_Sphi_fst_ne hsub z₀ (hgen t htM z₀ hz₀) hz₀1

end Nivat.Colle37
