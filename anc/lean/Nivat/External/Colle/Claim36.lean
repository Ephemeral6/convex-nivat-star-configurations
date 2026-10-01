/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.Lemma45
import Nivat.External.Colle.LatticeEdges
import Nivat.External.Colle.NewtonZonotope
import Nivat.External.Colle.Generating
import Nivat.Laurent.Basic
import Nivat.Section8.ExternalDefs
import Nivat.Defs.Orbit

/-!
# Colle, Claim 3.6 — periodicity does not propagate along `ℓ_m`

Formalization of Claim 3.6 from Cleber F. Colle, *On periodic decompositions, one-sided
nonexpansive directions and Nivat's conjecture*, arXiv:1909.08195 **v4**, §3.1 (proof of
Theorem 1.14); published as DCDS **43** (2023).

## Paper statement

Verbatim setting (arXiv v4, lines 545-571).  In the proof of Theorem 1.14 one has

* `η` non-periodic (Proposition 1.8, from the contradiction hypothesis);
* `x_per ∈ X_η` fully periodic (Theorem 1.9 + Boyle-Lind);
* a `ℤ`-minimal periodic decomposition `η = η₁ + ⋯ + η_m` (Theorem 1.10) with
  `h_i` a period of `η_i`, the `h_i` in pairwise distinct directions;
* `φ(X) := (X^{h₁}-1)⋯(X^{h_m}-1)` and the `η`-generating set `S_φ` (Lemma 2.5);
* `ℓ₁, …, ℓ_{2m}` the oriented lines through the origin parallel to the edges of `S_φ`,
  cyclically enumerated, with `h_i` parallel or antiparallel to `ℓ_i` for `1 ≤ i ≤ m`.

> **Claim 3.6.** Given an `E(S_φ)`-enveloped set `B ⊂ ℤ²`, there exists `u ∈ ℤ²` such that
> `(T^u η)|_B = x_per|_B`, but `(T^u η)|_{St_B(ℓ_m)} ≠ x_per|_{St_B(ℓ_m)}`,  (3.4)
> where `St_B(ℓ_m) := H_B(ℓ_m) ∪ H_B(-ℓ_m)` is the strip of `B` along `ℓ_m`.

Proof (paper): suppose agreement on `B` always forced agreement on `St_B(ℓ_m)`.  Since `B`
is **non-empty and finite** there is some `u` with `(T^u η)|_B = x_per|_B`.  Reduce the
alphabet mod a prime `p` with `A ⊂ ℤ_p`; then
`ψ(X) := (X^{h₁}-1)⋯(X^{h_{m-1}}-1) ∈ ann_{ℤ_p}(η - η̄_m)`, so by Lemma 2.5 `S_ψ` is an
`η - η̄_m`-generating set, and — because the `h_i` point in pairwise distinct directions —
`S_ψ` has no edge parallel to `±ℓ_m`.  Agreement on the strip makes
`(T^u(η - η̄_m))|_{St_B(ℓ_m)}` periodic with period parallel to `ℓ_m`; applying the
generating set `S_ψ` propagates that periodicity to all of `T^u(η - η̄_m)`, hence to
`T^u η`, contradicting the non-periodicity of `η`.

## Role in the chain

Claim 3.6 is the entry point of Colle step 3.  Its witness `u` is what feeds the
half-plane dichotomy just below (3.4) — `(T^u η)` must already differ from `x_per` on
`H_B(ℓ_m)` or on `H_B(-ℓ_m)` — which is then fed into Lemma 3.5 (i) to produce the
`(ℓ_m, ℓ_J)`-region `Â_∞`, the configuration `ϑ` and the index `ε` of (3.5).  Those are
exactly the inputs of `Claim37.claim37`.

## Proof status: one named gap

`claim36` is **no longer a monolithic `sorry`**.  Its proof (§4) is a four-line assembly
from two ingredients:

* `exists_shift_agreeing_on_finite` (§3) — **proved**, and it is precisely the step where
  the paper's "since `B` is a non-empty, finite set" is used;
* `periodic_of_agree_on_strip` (§4) — **`sorry`**, the single remaining gap.

`periodic_of_agree_on_strip` in turn decomposes into the paper's two sub-steps, of which
the algebraic one is proved here and the geometric one is the honest hole:

| sub-step | status |
|---|---|
| `ψ = ∏_{i≠m}(X^{h_i}-1)` annihilates `η₁+⋯+η_{m-1}` | **proved**, `act_prod_eq_zero_of_mem_Per` (§3) |
| `x_per` has a period parallel to any direction | **proved**, `exists_period_parallel` (§3) |
| `∃u` agreeing with `x_per` on a finite `B` | **proved**, `exists_shift_agreeing_on_finite` (§3) |
| `S_ψ` has no edge parallel to `±ℓ_m` | **proved**, `generatingSet_no_edge_parallel` (§4), *after re-orienting the statement* |
| strip-periodicity ⟹ global periodicity | **`sorry`**, `periodic_of_agree_on_strip` (§4) |
| the sweeping induction (band ⟹ everything) | **proved**, `eq_of_band_of_generatesAt` (§3.5) |
| Gap 2 from explicit sweep data | **proved**, `isPeriodic_of_strip_agree_of_sweepData` (§3.5) |

## Correction (2026-09-14, third pass): Gap 1 was FALSE as stated, and is now closed

`generatingSet_no_edge_parallel` used to conclude `±ℓ_m ∉ E ↑S_ψ` and carried a `sorry`.
That conclusion is **false**, and is refuted `sorry`-free in `MinkowskiEdges.lean` §6
(`generatingSet_no_edge_parallel_false`, and `…_false_posArea` with `conv S_ψ` of positive
area).  Those refutations are deliberately **kept**.

`Nivat.LE2.E` is indexed by primitive outer *normals*, while `ℓ_m` is a *direction*; the two
differ by a 90° rotation.  Colle's "no edge parallel to `±ℓ_m`" is therefore
`∀ n ∈ E ↑S_ψ, dot n ℓ_m ≠ 0` (by `det_dir`, the edge with normal `n` runs along
`dir n = (-n.2, n.1)`).  The statement was re-oriented to that form on 2026-09-14 and is now
**proved**, via `NewtonZonotope.lean`'s `no_edge_parallel_of_Conv_eq_supp_prod`.  The full
record is on the declaration itself.

**This does not shrink the axiom closure.**  Neither `Nivat.colle_doublyPeriodic` nor
`Nivat.colle_region` depends on Claim 3.6; what changed is one fewer `sorry` and one fewer
false statement in the tree.

## Correction (2026-09-13, second pass): what blocks Gap 2 is not Gap 1

The two rows above marked `sorry` were previously described as one depending on the other.
That is **wrong** and is corrected here rather than deleted:

* the *sweeping induction*, named in the old `sorry` note on `periodic_of_agree_on_strip` as
  the missing middle step, is now proved (§3.5, `eq_of_band_of_generatesAt`), together with
  the assembly of all of Gap 2 from explicit sweep data
  (`isPeriodic_of_strip_agree_of_sweepData`);
* what remains open in Gap 2 is the *production* of that sweep data, which fails for two
  reasons independent of Gap 1 — `S_φ` necessarily has an edge parallel to `ℓ_m` (so it has
  no strict extreme in the only usable sweep direction, see `band_forces_orthogonal`), and
  the paper's passage to `η - η̄_m` has no `[AddCommMonoid A]` analogue (see
  `summand_period_not_reflected` in §5);
* Gap 1 as stated was moreover *not* the statement the sweep needs, and was refuted
  `sorry`-free in `MinkowskiEdges.lean` §6 — `E` is indexed by primitive normals, so the
  paper's "no edge parallel to `±ℓ_m`" is `∀ n ∈ E ↑S_ψ, dot n ℓ_m ≠ 0`, a 90° rotation away
  from `±ℓ_m ∉ E ↑S_ψ`.  The correctly oriented form is proved there as
  `zono_no_edge_parallel`, and (2026-09-14) is now what `generatingSet_no_edge_parallel`
  states.  Accordingly the claim below that a missing lattice-level
  `E (A + B) = E A ∪ E B` "is the reason `generatingSet_no_edge_parallel` is a `sorry`" is
  also superseded: that rule would not have rescued a false statement.  See the detailed note
  on `periodic_of_agree_on_strip`.

## Infrastructure audit (2026-09-13) — correcting an earlier claim in this file

An earlier revision of this docstring asserted that "the mod-`p` alphabet reduction and
`ann_{ℤ_p}` bookkeeping" were "not available in this tree".  **That was wrong**, and the
error is recorded here rather than silently deleted.  The Laurent/annihilator layer is
present and `sorry`-free:

* `Nivat/Laurent/Basic.lean:202` `act_mul : act (f₁ * f₂) g = act f₁ (act f₂ g)`;
* `Nivat/Laurent/Basic.lean:242` `act_mono_sub_one_eq_zero_iff : act (mono u - 1) g = 0 ↔ u ∈ Per g`;
* `Nivat/Laurent/Basic.lean:237` `act_mem_Per`; `:249` `act_prod_mono_sub_one`;
* `Nivat/External/Colle/Generating.lean:65` `isGeneratingSet_of_annihilator` (Lemma 2.5);
* `Nivat/External/Colle/HalfPlanePeriodicity.lean:103` `exists_period_multiple_of_halfPlane`
  (Prop 2.12: half-plane periodicity of a sum of periodic components ⟹ a global period);
* `Nivat/External/Colle/GeneratedHalfPlane.lean:32` `eq_of_halfPlane_of_generatesAt`;
* `Nivat/Laurent/Ostrowski.lean:136,171` `newt_mul`, `newt_prod` (Newton-polygon Minkowski
  additivity `Newt(fg) = Newt f + Newt g`, over `ℂ`).

### Superseded (2026-09-14)

An earlier revision of this section said: "What is genuinely **absent** (confirmed by search,
0 hits): any lattice-level rule `E (A + B) = E A ∪ E B` for Minkowski sums of subsets of
`ℤ²`, and hence any route from `newt_prod` to the edge directions of `S_ψ`.  That absence is
the reason `generatingSet_no_edge_parallel` is a `sorry` and not a proof."

Both halves are now wrong and are corrected rather than deleted:

* the rule is **present**: `MinkowskiEdges.lean` proves `face_add` unconditionally and
  `E_add_of_finite : E (A + B) = E A ∪ E B` for finite non-empty `A`, `B` (the unrestricted
  form is false — see `E_add_ne` there);
* it was never the reason for the `sorry`: the old statement was **false**, and no Minkowski
  rule proves a false statement.  The route from `newt_prod` to the edges of `S_ψ` is now
  complete — `NewtonZonotope.lean` (Ostrowski transported from `ℂ` to `ℤ`) plus
  `ConvTransport.lean`'s `E_congr_of_Conv_eq` plus `MinkowskiEdges.lean`'s
  `zono_no_edge_parallel`.

## Fidelity notes

* **`B` finite and non-empty are load-bearing and are stated here.**  The paper uses both
  explicitly.  They are *not* implied by `Nivat.LE2.Enveloped`: `Enveloped ∅ ∅` holds by
  `enveloped_refl`, and `strip ∅ ℓ = ∅`, so clause (2) would read `¬ True`.  An earlier
  draft omitted them and was therefore refutable.  `exists_shift_agreeing_on_finite`
  now *uses* `B.Finite`, so the hypothesis is not decoration.
* **`S_φ` is pinned to `φ`'s Newton polygon, not merely assumed `η`-generating.**  See the
  decision note on `claim36` below.
* **The `h_i` are required pairwise non-parallel** (`det (h i) (h j) ≠ 0` for `i ≠ j`),
  which is what the paper's proof uses to know `S_ψ` has no edge parallel to `±ℓ_m`.

## References

Colle, arXiv:1909.08195v4, §3.1, lines 545-571.
-/

namespace Nivat.Colle36

open Nivat Nivat.Colle Nivat.Colle45 Nivat.LE2

variable {A : Type*}

/-! ## §1. Geometry of the strip

These are the facts that make the *shape* of (3.4) coherent: clause (2) is not the
negation of clause (1), because the strip strictly contains the base set.
-/

/-- **The strip strictly contains a finite non-empty base set.**

This is what makes Claim 3.6 non-contradictory: clauses (1) and (2) of (3.4) speak about
`B` and about `St_B(ℓ_m) ⊋ B`, so they can hold simultaneously.

The finiteness hypothesis is necessary: for `B = ℤ²` one has `strip B ℓ = B`, see
`scratch/cl36_nondeg.lean : strip_not_proper_univ`. -/
theorem strip_ssubset_of_finite {B : Set (ℤ × ℤ)} (hfin : B.Finite) (hne : B.Nonempty)
    {ℓ : ℤ × ℤ} (hℓ : ℓ ≠ 0) : B ⊂ strip B ℓ := by
  obtain ⟨b, hb⟩ := hne
  have hcoord : ℓ.1 ≠ 0 ∨ ℓ.2 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hℓ (Prod.ext hcon.1 hcon.2)
  have hinj : Function.Injective (fun t : ℤ => b + t • ℓ) := by
    intro s t hst
    simp only [add_right_inj] at hst
    have h1 : s * ℓ.1 = t * ℓ.1 := by
      have := congrArg Prod.fst hst
      simpa [Prod.smul_fst, smul_eq_mul] using this
    have h2 : s * ℓ.2 = t * ℓ.2 := by
      have := congrArg Prod.snd hst
      simpa [Prod.smul_snd, smul_eq_mul] using this
    rcases hcoord with h | h
    · exact mul_right_cancel₀ h h1
    · exact mul_right_cancel₀ h h2
  rw [Set.ssubset_def]
  refine ⟨subset_strip B ℓ, fun hsub => ?_⟩
  have hrange : Set.range (fun t : ℤ => b + t • ℓ) ⊆ B := by
    rintro _ ⟨t, rfl⟩
    refine hsub ?_
    rw [strip_eq]
    exact ⟨b, hb, t, rfl⟩
  exact (Set.infinite_range_of_injective hinj) (hfin.subset hrange)

/-- **The disagreement produced by Claim 3.6 lives strictly outside `B`.**

Given the two clauses of (3.4), the site where `T^u η` and `x_per` differ is in the strip
but not in the base set.  This is the form in which the dichotomy just below (3.4)
(`H_B(ℓ_m)` or `H_B(-ℓ_m)`) is read off. -/
theorem disagreement_outside_base {x y : Config A} {u : ℤ × ℤ}
    {B : Set (ℤ × ℤ)} {ℓ : ℤ × ℤ}
    (hagree : ∀ z ∈ B, T u x z = y z)
    (hdis : ¬ (∀ z ∈ strip B ℓ, T u x z = y z)) :
    ∃ z ∈ strip B ℓ, z ∉ B ∧ T u x z ≠ y z := by
  push Not at hdis
  obtain ⟨z, hz, hne⟩ := hdis
  exact ⟨z, hz, fun hzB => hne (hagree z hzB), hne⟩

/-- **The witness `u` of Claim 3.6 never makes `T^u η` equal to `x_per`.** -/
theorem shift_ne_of_disagree {x y : Config A} {u : ℤ × ℤ} {B : Set (ℤ × ℤ)} {ℓ : ℤ × ℤ}
    (hdis : ¬ (∀ z ∈ strip B ℓ, T u x z = y z)) : T u x ≠ y :=
  fun heq => hdis fun z _ => congrFun heq z

/-! ## §2. The polynomial `φ`

`φ(X) = (X^{h₁}-1)⋯(X^{h_m}-1)`, as an element of `ℤ[X₁^±, X₂^±]`.  Only its *support*
matters for the geometry of `S_φ`, and the support is independent of the alphabet, so it
is taken over `ℤ` here.
-/

/-- `φ(X) := (X^{h₁}-1)⋯(X^{h_m}-1)`, over `ℤ`. -/
noncomputable def phi {m : ℕ} (h : Fin m → ℤ × ℤ) : LaurentTwo ℤ :=
  ∏ i, (mono (h i) - 1)

/-! ## §3. Proved ingredients of the paper's argument -/

/-- `act f` is additive over a `Finset.sum` in its configuration argument. -/
theorem act_finset_sum_right {R : Type*} [CommRing R] {ι : Type*} (s : Finset ι)
    (f : LaurentTwo R) (gs : ι → Config R) :
    act f (∑ i ∈ s, gs i) = ∑ i ∈ s, act f (gs i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, act_add_right, ih, Finset.sum_insert ha]

/-- **The `ψ`-annihilation step of Claim 3.6** (paper: `ψ ∈ ann_{ℤ_p}(η - η̄_m)`).

If `H i` is a period of `gs i` for every `i ∈ s`, then `∏_{i ∈ s} (X^{H i} - 1)`
annihilates `∑_{i ∈ s} gs i`.  Taking `s = {1, …, m-1}` gives exactly the paper's `ψ`
annihilating `η - η̄_m`.

This is the ingredient the earlier revision of this file wrongly declared unavailable. -/
theorem act_prod_eq_zero_of_mem_Per {R : Type*} [CommRing R] {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (H : ι → ℤ × ℤ) (gs : ι → Config R)
    (hper : ∀ i ∈ s, H i ∈ Per (gs i)) :
    act (∏ i ∈ s, (mono (H i) - 1 : LaurentTwo R)) (∑ i ∈ s, gs i) = 0 := by
  classical
  rw [act_finset_sum_right]
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [← Finset.prod_erase_mul s _ hi, act_mul,
    (act_mono_sub_one_eq_zero_iff (H i) (gs i)).mpr (hper i hi), act_zero_right]

/-- **"`x_per` is periodic with period parallel to any `ℓ_i`."**

The paper asserts this one-liner immediately before Claim 3.6.  It follows from
`DoublyPeriodic.exists_smul_mem`. -/
theorem exists_period_parallel {f : Config A} (h : DoublyPeriodic f)
    {ℓ : ℤ × ℤ} (hℓ : ℓ ≠ 0) :
    ∃ N : ℤ, N ≠ 0 ∧ N • ℓ ≠ 0 ∧ N • ℓ ∈ Per f := by
  obtain ⟨N, hN, hmem⟩ := h.exists_smul_mem
  refine ⟨N, hN, ?_, hmem ℓ⟩
  intro hzero
  rcases smul_eq_zero.mp hzero with h1 | h1
  · exact hN h1
  · exact hℓ h1

/-- **"Since `B` is a non-empty, finite set, there exists `u` with `(T^u η)|_B = x_per|_B`."**

This is the paper's sentence at the start of the proof of Claim 3.6, and it is exactly
where finiteness of `B` is consumed: `orbitClosure` is defined by agreement on arbitrary
*finite* windows, so a finite `B` can be matched but an infinite one cannot.

Note `B.Nonempty` is *not* needed for this step (the empty window is matched trivially);
non-emptiness is what makes the strip strictly larger, via `strip_ssubset_of_finite`. -/
theorem exists_shift_agreeing_on_finite {η x : Config A} (hx : x ∈ orbitClosure η)
    {B : Set (ℤ × ℤ)} (hB : B.Finite) :
    ∃ u : ℤ × ℤ, ∀ z ∈ B, T u η z = x z := by
  classical
  obtain ⟨u, hu⟩ := hx hB.toFinset
  refine ⟨u, fun z hz => ?_⟩
  rw [hu z (hB.mem_toFinset.mpr hz)]
  show η (z + u) = η (u + z)
  rw [add_comm]

/-! ## §3.5. The sweeping induction — band periodicity ⟹ global periodicity

This section is the *middle step* of Gap 2, the one the docstring of
`periodic_of_agree_on_strip` calls "the sweeping induction".  It is proved here, `sorry`-free,
and in a form that makes precise what data it needs.

### The band is a level set

Write `n` for a primitive normal of `ℓ` (`dot n ℓ = 0`).  For `ℓ` primitive the strip
`St_B(ℓ) = B + ℤℓ` is a union of *full* lattice lines in direction `ℓ`, and `dot n` is
constant on each of them.  So the only information the sweep can use about the strip is the
set of `n`-levels it covers; that is why `eq_of_band_of_generatesAt` below takes its
hypothesis in the form "agreement on the levels `[c, c+M]`" and why `M` must dominate the
`n`-width of the generating window.

### Why the sweep direction must be `n ⊥ ℓ`, and what that costs

The local rule attached to a site `a` of a generating window `S` determines the value at `z`
from the values at `z + b - a`, `b ∈ S \ {a}`.  For the known region to grow, those sites
must already be known; since the strip is bounded transverse to `ℓ` and unbounded along `ℓ`,
the only linear form along which "already known" is a half-line condition is a form
vanishing on `ℓ`.  Hence:

* the sweep must run in a direction `n` with `dot n ℓ = 0`, and
* `a` must be the *strict* `dot n`-minimum of `S` (and `a'` the strict maximum), i.e.
  `n ∉ E ↑S` and `-n ∉ E ↑S` — no edge of `S` parallel to `ℓ`.

This is exactly the corrected reading of the paper's "`S_ψ` has no edge parallel to `±ℓ_m`":
`E` is indexed by primitive *normals*, so the condition is `∀ n ∈ E ↑S, dot n ℓ ≠ 0`.  See
the note on `periodic_of_agree_on_strip` for the consequences.

### Asymmetry of the two halves of the sweep

Only the *downward* half consumes the band width `M`: it turns `M+1` consecutive known
levels into one new level below them.  Once a whole half-plane is known, the *upward* half
needs no width at all — the sites `z + b - a'` all sit strictly below `z`.  So `hM` is
attached to `a` only.
-/

/-- `dot` is `ℤ`-linear in its second argument. -/
theorem dot_zsmul_right (n : ℤ × ℤ) (k : ℤ) (v : ℤ × ℤ) : dot n (k • v) = k * dot n v := by
  simp only [dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- `dot n` on a site of the shifted window. -/
theorem dot_add_sub (n b z a : ℤ × ℤ) : dot n (b + (z - a)) = dot n z + (dot n b - dot n a) := by
  simp only [dot, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]
  ring

/-- **The strip is invariant under translation along `ℓ`.**  This is the one property of
`St_B(ℓ)` the sweep uses on the `x_per` side. -/
theorem strip_add_zsmul (B : Set (ℤ × ℤ)) (ℓ : ℤ × ℤ) {z : ℤ × ℤ}
    (hz : z ∈ strip B ℓ) (k : ℤ) : z + k • ℓ ∈ strip B ℓ := by
  rw [strip_eq] at hz ⊢
  obtain ⟨b, hb, t, rfl⟩ := hz
  exact ⟨b, hb, t + k, by rw [add_smul]; abel⟩

/-- **The sweeping induction.**

Two members of an orbit closure that agree on a *band* of `M+1` consecutive `dot n`-levels
agree everywhere, provided the generating window `S` has a strict `dot n`-minimum `a` and a
strict `dot n`-maximum `a'`, both generating, and `M` dominates the `n`-width of `S`.

No hypothesis on the alphabet, on finiteness of its range, or on `n ≠ 0` is needed.  The
band hypothesis is a *fixed* pair of cuts `c` and `c + M`: neither cut is existentially
quantified, so the hypothesis is a genuine restriction (an existentially quantified cut
`∃ t, dot n z ≤ t` would hold at every `z` and make the statement say `x = y` outright). -/
theorem eq_of_band_of_generatesAt {ξ x y : Config A}
    (hx : x ∈ orbitClosure ξ) (hy : y ∈ orbitClosure ξ)
    {S : Finset (ℤ × ℤ)} {a a' : ℤ × ℤ}
    (hgen : GeneratesAt ξ S a) (hgen' : GeneratesAt ξ S a')
    {n : ℤ × ℤ}
    (hmin : ∀ b ∈ S.erase a, dot n a < dot n b)
    (hmax : ∀ b ∈ S.erase a', dot n b < dot n a')
    {c M : ℤ} (hM : ∀ b ∈ S, dot n b - dot n a ≤ M)
    (hagree : ∀ z, c ≤ dot n z → dot n z ≤ c + M → x z = y z) :
    x = y := by
  -- the local rule of a generating site, transported to an arbitrary site `z`
  have hstep : ∀ p : ℤ × ℤ, GeneratesAt ξ S p → ∀ z : ℤ × ℤ,
      (∀ b ∈ S.erase p, x (b + (z - p)) = y (b + (z - p))) → x z = y z := by
    intro p hp z hloc
    have h := hp.2 (T (z - p) x) (T_mem_of_mem_orbitClosure hx (z - p))
      (T (z - p) y) (T_mem_of_mem_orbitClosure hy (z - p)) hloc
    simpa only [T_apply, show p + (z - p) = z by abel] using h
  -- downward: the band sweeps to the whole lower half-plane `dot n z ≤ c + M`
  have hdown : ∀ k : ℕ, ∀ z : ℤ × ℤ, c - (k : ℤ) ≤ dot n z → dot n z ≤ c + M → x z = y z := by
    intro k
    induction k with
    | zero => simpa using hagree
    | succ k ih =>
        intro z hlo hhi
        by_cases hk : c - (k : ℤ) ≤ dot n z
        · exact ih z hk hhi
        · have hlo' : c - ((k : ℤ) + 1) ≤ dot n z := by exact_mod_cast hlo
          have hz : dot n z = c - (k : ℤ) - 1 := by omega
          refine hstep a hgen z (fun b hb => ?_)
          have h1 : dot n a < dot n b := hmin b hb
          have h2 : dot n b - dot n a ≤ M := hM b (Finset.mem_of_mem_erase hb)
          have hlevel : dot n (b + (z - a)) = dot n z + (dot n b - dot n a) := dot_add_sub ..
          exact ih _ (by rw [hlevel, hz]; omega) (by rw [hlevel, hz]; omega)
  have hlower : ∀ z : ℤ × ℤ, dot n z ≤ c + M → x z = y z := by
    intro z hz
    exact hdown (c - dot n z).toNat z (by omega) hz
  -- upward: a known half-plane sweeps to everything, with no width condition
  have hup : ∀ k : ℕ, ∀ z : ℤ × ℤ, dot n z ≤ c + M + (k : ℤ) → x z = y z := by
    intro k
    induction k with
    | zero => simpa using hlower
    | succ k ih =>
        intro z hhi
        by_cases hk : dot n z ≤ c + M + (k : ℤ)
        · exact ih z hk
        · have hhi' : dot n z ≤ c + M + ((k : ℤ) + 1) := by exact_mod_cast hhi
          refine hstep a' hgen' z (fun b hb => ?_)
          have h1 : dot n b < dot n a' := hmax b hb
          have hlevel : dot n (b + (z - a')) = dot n z + (dot n b - dot n a') := dot_add_sub ..
          exact ih _ (by rw [hlevel]; omega)
  funext z
  exact hup (dot n z - (c + M)).toNat z (by omega)

/-- **Gap 2 modulo the generating window: strip agreement with a fully periodic
configuration forces `η` to be periodic.**

This is `periodic_of_agree_on_strip` with the paper's geometric input spelled out as
explicit *sweep data* — a generating window `S` for `η` whose strict `dot n`-extremes are
generating sites, for a normal `n` of `ℓ`, together with a band of the strip wide enough to
seed the induction.  Everything else in Claim 3.6's proof of Gap 2 is discharged here:

* `exists_period_parallel` produces a period `N • ℓ ≠ 0` of `x_per`;
* `strip_add_zsmul` moves inside the strip along `ℓ`, so agreement with `x_per` on the strip
  makes `T^u η` and its `N • ℓ`-shift agree there;
* `eq_of_band_of_generatesAt` sweeps that agreement to all of `ℤ²`;
* a period of `T^u η` is a period of `η`.

Note what is *not* assumed: `x_per ∈ orbitClosure η` is never used (the two configurations
fed to the sweep are `T^u η` and its own shift, both automatically in the orbit closure), and
the alphabet is an arbitrary type — no `AddCommMonoid`, no finiteness.

Nor is `dot n ℓ = 0` assumed.  It would be inert: the proof never uses it, because the whole
geometric content sits in `hband`.  It is not lost, though — `band_forces_orthogonal` below
shows `hband` *implies* `dot n ℓ = 0` as soon as `B` is finite, `n` is primitive and
`0 ≤ M`, so the orthogonality is a theorem about this hypothesis rather than a decoration on
it, and `hband` is not innocuous. -/
theorem isPeriodic_of_strip_agree_of_sweepData
    {η x_per : Config A} (hx_fp : IsFullyPeriodic x_per)
    {ℓ : ℤ × ℤ} (hℓ : ℓ ≠ 0)
    {S : Finset (ℤ × ℤ)} {a a' : ℤ × ℤ}
    (hgen : GeneratesAt η S a) (hgen' : GeneratesAt η S a')
    {n : ℤ × ℤ}
    (hmin : ∀ b ∈ S.erase a, dot n a < dot n b)
    (hmax : ∀ b ∈ S.erase a', dot n b < dot n a')
    {c M : ℤ} (hM : ∀ b ∈ S, dot n b - dot n a ≤ M)
    {B : Set (ℤ × ℤ)}
    (hband : ∀ z : ℤ × ℤ, c ≤ dot n z → dot n z ≤ c + M → z ∈ strip B ℓ)
    (u : ℤ × ℤ) (hagree : ∀ z ∈ strip B ℓ, T u η z = x_per z) :
    IsPeriodic η := by
  obtain ⟨N, hN, hv_ne, hv_per⟩ := exists_period_parallel hx_fp hℓ
  have hxmem : T u η ∈ orbitClosure η := T_mem_orbitClosure η u
  have hymem : T (N • ℓ) (T u η) ∈ orbitClosure η := by
    rw [← T_add]; exact T_mem_orbitClosure η (N • ℓ + u)
  -- on the band, `T^u η` agrees with its own `N • ℓ`-shift
  have hband_agree : ∀ z : ℤ × ℤ, c ≤ dot n z → dot n z ≤ c + M →
      T u η z = T (N • ℓ) (T u η) z := by
    intro z h1 h2
    have hz : z ∈ strip B ℓ := hband z h1 h2
    have hz' : z + N • ℓ ∈ strip B ℓ := strip_add_zsmul B ℓ hz N
    show T u η z = T u η (z + N • ℓ)
    rw [hagree z hz, hagree (z + N • ℓ) hz', Per.apply hv_per z]
  have heq : T u η = T (N • ℓ) (T u η) :=
    eq_of_band_of_generatesAt hxmem hymem hgen hgen' hmin hmax hM hband_agree
  refine ⟨N • ℓ, ?_, hv_ne⟩
  rw [mem_Per_iff]
  funext w
  have h := congrFun heq (w - u)
  simp only [T_apply] at h
  rw [show w - u + u = w by abel, show w - u + N • ℓ + u = w + N • ℓ by abel] at h
  show η (w + N • ℓ) = η w
  exact h.symm

/-! ### Non-degeneracy of the sweep data

The band hypothesis `hband` is where this project's recurring bug would live, so it is
checked in both directions: it is *not* vacuous (`sweepData_satisfiable`) and it is *not*
free (`band_forces_orthogonal`).  Both cuts `c` and `c + M` are fixed integers; neither is
existentially quantified, which is what an earlier generation of bugs in this tree
(`∃ t, z ∈ halfPlaneLE ℓ t`, true at every `z`) got wrong.
-/

/-- **The band hypothesis pins the sweep direction: it forces `dot n ℓ = 0`.**

If a *finite* `B` has a strip covering the whole band of `n`-levels `[c, c + M]`, with `n`
primitive and `0 ≤ M`, then `n` is orthogonal to `ℓ`.  So a sweep direction not orthogonal to
`ℓ` makes `hband` outright unsatisfiable; this is the formal content of "the strip is bounded
transverse to `ℓ`, and unbounded along it", and the reason
`isPeriodic_of_strip_agree_of_sweepData` need not — and does not — assume orthogonality. -/
theorem band_forces_orthogonal {B : Set (ℤ × ℤ)} (hB : B.Finite) {ℓ n : ℤ × ℤ}
    (hn : Prim n) {c M : ℤ} (hM : 0 ≤ M)
    (hband : ∀ z : ℤ × ℤ, c ≤ dot n z → dot n z ≤ c + M → z ∈ strip B ℓ) :
    dot n ℓ = 0 := by
  -- `w` spans the lattice line `dot n = 0`
  have hdotw : dot n (-n.2, n.1) = 0 := by simp only [dot]; ring
  obtain ⟨z₀, hz₀⟩ := dot_surjective hn c
  -- the whole line `z₀ + ℤ w` sits at level `c`, hence inside the strip
  have hline : ∀ j : ℤ, ∃ b ∈ B, ∃ t : ℤ, z₀ + j • (-n.2, n.1) = b + t • ℓ := by
    intro j
    have hlev : dot n (z₀ + j • (-n.2, n.1)) = c := by
      rw [dot_add, dot_zsmul_right, hdotw, mul_zero, add_zero, hz₀]
    have hmem := hband (z₀ + j • (-n.2, n.1)) (by omega) (by omega)
    rw [strip_eq] at hmem
    exact hmem
  choose bb hbb tt hbbt using hline
  -- `B` is finite and `ℤ` is not, so two distinct lines' worth of `j` share a base point
  obtain ⟨j₁, -, j₂, -, hjne, hjeq⟩ :=
    Set.Infinite.exists_ne_map_eq_of_mapsTo (Set.infinite_univ (α := ℤ))
      (fun j _ => hbb j) hB
  have hvec : (j₁ - j₂) • ((-n.2, n.1) : ℤ × ℤ) = (tt j₁ - tt j₂) • ℓ := by
    have h₁ := hbbt j₁
    have h₂ := hbbt j₂
    rw [hjeq] at h₁
    rw [sub_smul, sub_smul]
    rw [show (j₁ • ((-n.2, n.1) : ℤ × ℤ)) = (bb j₂ + tt j₁ • ℓ) - z₀ by rw [← h₁]; abel,
      show (j₂ • ((-n.2, n.1) : ℤ × ℤ)) = (bb j₂ + tt j₂ • ℓ) - z₀ by rw [← h₂]; abel]
    abel
  have e1 : (j₁ - j₂) * (-n.2) = (tt j₁ - tt j₂) * ℓ.1 := by
    have := congrArg Prod.fst hvec
    simpa only [Prod.smul_fst, smul_eq_mul] using this
  have e2 : (j₁ - j₂) * n.1 = (tt j₁ - tt j₂) * ℓ.2 := by
    have := congrArg Prod.snd hvec
    simpa only [Prod.smul_snd, smul_eq_mul] using this
  have hJ : j₁ - j₂ ≠ 0 := sub_ne_zero_of_ne hjne
  -- `(t₁ - t₂) · ⟨n, ℓ⟩ = 0`, and `t₁ = t₂` would force `n = 0`
  have key : (tt j₁ - tt j₂) * dot n ℓ = 0 := by
    simp only [dot]
    linear_combination (-n.1) * e1 + (-n.2) * e2
  rcases mul_eq_zero.mp key with hT | hdot
  · exfalso
    rw [hT, zero_mul] at e1 e2
    have hn2 : n.2 = 0 := by
      rcases mul_eq_zero.mp e1 with h | h
      · exact absurd h hJ
      · omega
    have hn1 : n.1 = 0 := by
      rcases mul_eq_zero.mp e2 with h | h
      · exact absurd h hJ
      · exact h
    exact hn.ne_zero (Prod.ext hn1 hn2)
  · exact hdot

/-- Vertical stripes of period `2`, the witness configuration for `sweepData_satisfiable`. -/
def stripes2 : Config ℤ := fun z => z.1 % 2

/-- Members of the orbit closure of `stripes2` cannot separate `(0,0)` from `(2,0)`: that is
the local rule which makes `{(0,0), (2,0)}` a generating window at both of its sites. -/
theorem stripes2_eq_of_mem_orbitClosure {x : Config ℤ} (hx : x ∈ orbitClosure stripes2) :
    x (0, 0) = x (2, 0) := by
  obtain ⟨u, hu⟩ := hx {((0 : ℤ), (0 : ℤ)), ((2 : ℤ), (0 : ℤ))}
  rw [hu (0, 0) (by simp), hu (2, 0) (by simp)]
  show (u + ((0 : ℤ), (0 : ℤ))).1 % 2 = (u + ((2 : ℤ), (0 : ℤ))).1 % 2
  simp only [Prod.fst_add]
  omega

/-- **The hypothesis bundle of `isPeriodic_of_strip_agree_of_sweepData` is satisfiable**, with
a finite `B`, a primitive `n` orthogonal to `ℓ`, a generating window with two distinct strict
extremes, and a strip that is a *proper* subset of `ℤ²`.

Witness: `η = x_per = stripes2` (vertical stripes of period `2`), window
`S = {(0,0), (2,0)}`, `n = (1,0)`, `ℓ = (0,1)`, `B = {(0,0), (1,0), (2,0)}`, `c = 0`, `M = 2`,
`u = 0`.  Without this check the sweeping induction could be a statement about an empty class
of data; the companion `band_forces_orthogonal` rules out the opposite failure, a hypothesis
so weak that every direction satisfies it. -/
theorem sweepData_satisfiable :
    ∃ (η x_per : Config ℤ) (S : Finset (ℤ × ℤ)) (a a' n ℓ : ℤ × ℤ) (B : Set (ℤ × ℤ))
      (c M : ℤ) (u : ℤ × ℤ),
      IsFullyPeriodic x_per ∧ ℓ ≠ 0 ∧ Prim n ∧ dot n ℓ = 0 ∧ B.Finite ∧ 0 ≤ M ∧
      a ≠ a' ∧
      GeneratesAt η S a ∧ GeneratesAt η S a' ∧
      (∀ b ∈ S.erase a, dot n a < dot n b) ∧
      (∀ b ∈ S.erase a', dot n b < dot n a') ∧
      (∀ b ∈ S, dot n b - dot n a ≤ M) ∧
      (∀ z : ℤ × ℤ, c ≤ dot n z → dot n z ≤ c + M → z ∈ strip B ℓ) ∧
      (∀ z ∈ strip B ℓ, T u η z = x_per z) ∧
      strip B ℓ ≠ Set.univ := by
  classical
  refine ⟨stripes2, stripes2, {((0 : ℤ), (0 : ℤ)), ((2 : ℤ), (0 : ℤ))}, (0, 0), (2, 0),
    (1, 0), (0, 1), {((0 : ℤ), (0 : ℤ)), ((1 : ℤ), (0 : ℤ)), ((2 : ℤ), (0 : ℤ))}, 0, 2, 0,
    ?_, by decide, by decide, by decide,
    (Set.finite_singleton _).insert _ |>.insert _, by norm_num, by decide,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- `stripes2` is doubly periodic
  · refine ⟨(2, 0), ?_, (0, 1), ?_, by decide⟩
    · rw [mem_Per_iff]; funext z
      show (z + ((2 : ℤ), (0 : ℤ))).1 % 2 = z.1 % 2
      simp only [Prod.fst_add]; omega
    · rw [mem_Per_iff]; funext z
      show (z + ((0 : ℤ), (1 : ℤ))).1 % 2 = z.1 % 2
      simp only [Prod.fst_add]; omega
  -- the window generates at `(0,0)`
  · refine ⟨by simp, fun x hx y hy hag => ?_⟩
    have h1 := stripes2_eq_of_mem_orbitClosure hx
    have h2 := stripes2_eq_of_mem_orbitClosure hy
    have h3 := hag (2, 0) (by simp)
    rw [h1, h3, ← h2]
  -- and at `(2,0)`
  · refine ⟨by simp, fun x hx y hy hag => ?_⟩
    have h1 := stripes2_eq_of_mem_orbitClosure hx
    have h2 := stripes2_eq_of_mem_orbitClosure hy
    have h3 := hag (0, 0) (by simp)
    rw [← h1, h3, h2]
  -- `(0,0)` is the strict `dot n`-minimum, `(2,0)` the strict maximum
  · intro b hb
    rw [Finset.mem_erase] at hb
    have : b = ((2 : ℤ), (0 : ℤ)) := by
      rcases Finset.mem_insert.mp hb.2 with rfl | h
      · exact absurd rfl hb.1
      · exact Finset.mem_singleton.mp h
    subst this; decide
  · intro b hb
    rw [Finset.mem_erase] at hb
    have : b = ((0 : ℤ), (0 : ℤ)) := by
      rcases Finset.mem_insert.mp hb.2 with rfl | h
      · rfl
      · exact absurd (Finset.mem_singleton.mp h) hb.1
    subst this; decide
  · intro b hb
    rcases Finset.mem_insert.mp hb with rfl | hb
    · decide
    · rw [Finset.mem_singleton] at hb; subst hb; decide
  -- the band of levels `[0, 2]` lies inside the strip
  · intro z h1 h2
    simp only [dot] at h1 h2
    rw [strip_eq]
    refine ⟨(z.1, 0), ?_, z.2, ?_⟩
    · have h : z.1 = 0 ∨ z.1 = 1 ∨ z.1 = 2 := by omega
      rcases h with h | h | h <;> simp [Set.mem_insert_iff, h]
    · refine Prod.ext ?_ ?_ <;> simp
  -- `T⁰ η = x_per` everywhere, in particular on the strip
  · intro z _
    show stripes2 (z + 0) = stripes2 z
    rw [add_zero]
  -- the strip is a proper subset: `(5,0)` is outside it
  · intro hcon
    have hmem : ((5 : ℤ), (0 : ℤ)) ∈
        strip ({((0 : ℤ), (0 : ℤ)), ((1 : ℤ), (0 : ℤ)), ((2 : ℤ), (0 : ℤ))} : Set (ℤ × ℤ))
          ((0 : ℤ), (1 : ℤ)) := hcon ▸ Set.mem_univ _
    rw [strip_eq] at hmem
    obtain ⟨b, hb, t, ht⟩ := hmem
    have hfst : (5 : ℤ) = b.1 := by
      have := congrArg Prod.fst ht
      simpa only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, mul_zero, add_zero] using this
    rcases hb with rfl | rfl | rfl <;> simp at hfst

/-! ## §4. Claim 3.6

### Decision record: why `S_φ` is pinned to `φ`, not left as a generic generating set

An intermediate revision of this file used only `hS_gen : IsGeneratingSet η S_φ`, i.e.
*some* `η`-generating set.  That is a weaker hypothesis and hence a formally stronger
theorem, which is safe for soundness but **makes the theorem unprovable**: the paper
derives "`S_ψ` has no edge parallel to `±ℓ_m`" from the product structure of `φ` and the
resulting cyclic edge enumeration `ℓ₁, …, ℓ_{2m}`, never from generic generation.  A
search of the tree confirms there is no lemma computing `E` of a generating set from the
`IsGeneratingSet` predicate alone.

So the `φ`-derived hypothesis is **restored**, in the form `isGeneratingSetFor` below:

* **before** (intermediate revision): `(hS_gen : IsGeneratingSet η S_φ)`
* **after** (this revision): `(hS_gen : IsGeneratingSet η S_φ)` *together with*
  `(hS_hull : Conv S_φ = Conv (supp (phi h)))`

The added `hS_hull` is exactly the hypothesis `isGeneratingSet_of_annihilator`
(`Generating.lean:65`) already takes, so it is the tree's own notion of "the generating
set of `φ`", not an invention.  It does not imply the conclusion: it constrains only the
*shape* of `S_φ`, saying nothing about `η` versus `x_per`.
-/

/-- **Gap 1 (closed, 2026-09-14): the generating set of `ψ` has no edge parallel to `±ℓ_m`.**

### The statement this replaces was FALSE

Until 2026-09-14 this declaration read

```
    ℓ_m ∉ E (↑S_ψ : Set (ℤ × ℤ)) ∧ -ℓ_m ∉ E (↑S_ψ : Set (ℤ × ℤ))
```

and carried a `sorry`.  That statement is **refuted**, `sorry`-free, by
`Nivat.LE2.Colle36Fit.generatingSet_no_edge_parallel_false` in `MinkowskiEdges.lean` §6
(and again, with `conv S_ψ` of positive area, by `…_false_posArea`).  The refutation is
stated as the verbatim universal closure of the old signature — implicit binders made
explicit, nothing weakened, no hypothesis dropped — with witness `m = 2`,
`h = ((1,0), (0,1))`, `i_m = 1`, `ℓ_m = (0,1)`.  **Those refutations are kept**; they are
not deleted by this repair.

The defect was a units mismatch, not a missing lemma: `Nivat.LE2.E` is indexed by primitive
outer **normals** (see the `IsEdge`/`E` docstrings in `LatticeEdges.lean`), whereas `ℓ_m` is
a **direction** — `hℓ_dir` says `h i_m = c • ℓ_m`.  `ℓ_m` shows up as a *normal* of `S_ψ`
exactly when some surviving period `h i`, `i ≠ i_m`, is orthogonal to `ℓ_m`, which `hh_dir`
(pairwise non-parallel) explicitly permits.  No Minkowski rule can repair a false statement.

### Why the new conclusion is the paper's sentence

Colle writes "`S_ψ` has no edge parallel to `±ℓ_m`".  An edge with outer normal `n` runs in
direction `dir n = (-n.2, n.1)`, and `det_dir : det (dir n) ℓ = - dot n ℓ`
(`MinkowskiEdges.lean`), so "the edge `n` is parallel to `ℓ_m`" is `dot n ℓ_m = 0`.  Hence
the paper's sentence is

```
    ∀ n ∈ E (↑S_ψ : Set (ℤ × ℤ)), dot n ℓ_m ≠ 0
```

which is the conclusion below — the 90° rotation of the old one.  This is also exactly the
shape the downstream sweep consumes: `eq_of_band_of_generatesAt` (§3.5) needs a *normal*
`n` with `dot n ℓ_m ≠ 0` along which the window has strict extremes, and
`band_forces_orthogonal` (§3.5) is stated in the same units.  So the repair is not a
weakening: the old statement was unusable downstream *and* false, the new one is the
hypothesis the sweep actually asks for.

### Proof

`no_edge_parallel_of_Conv_eq_supp_prod` (`NewtonZonotope.lean` §4), which chains

* `Conv_supp_prod_eq_Conv_zonoF` — Ostrowski over `ℤ`: `Conv (supp ψ)` is the zonotope
  `∑_{i ≠ i_m} [0, h_i]` (the paper's (2.3)), obtained from `Nivat.newt_prod` by transport
  along the injective ring map `ℤ → ℂ`;
* `E_congr_of_Conv_eq` (`ConvTransport.lean`) — equal convex hulls have equal edge sets,
  which is what turns the hypothesis `hS_hull` (about hulls) into information about
  `E ↑S_ψ` (about lattice points);
* `zono_no_edge_parallel` (`MinkowskiEdges.lean` §4) — a zonotope has no edge parallel to
  `ℓ` if none of its generators is.

`hm` and `hℓ_prim` are **not used** by the proof; they are kept so that the signature stays
the paper's setting and stays comparable, hypothesis for hypothesis, with the refuted
version in `MinkowskiEdges.lean` §6.  Keeping unused hypotheses only weakens the theorem, so
this cannot hide a gap. -/
theorem generatingSet_no_edge_parallel {m : ℕ} (hm : 2 ≤ m) {h : Fin m → ℤ × ℤ}
    (hh_ne : ∀ i, h i ≠ 0)
    (hh_dir : ∀ i j, i ≠ j → det (h i) (h j) ≠ 0)
    {i_m : Fin m} {ℓ_m : ℤ × ℤ} (hℓ_prim : Primitive ℓ_m)
    (hℓ_dir : ∃ c : ℤ, c ≠ 0 ∧ h i_m = c • ℓ_m)
    {S_ψ : Finset (ℤ × ℤ)}
    (hS_hull : Conv S_ψ = Conv (supp (∏ i ∈ Finset.univ.erase i_m, (mono (h i) - 1 :
      LaurentTwo ℤ)))) :
    ∀ n ∈ E (↑S_ψ : Set (ℤ × ℤ)), dot n ℓ_m ≠ 0 := by
  obtain ⟨c, hc_ne, hc⟩ := hℓ_dir
  -- every *surviving* period is non-parallel to `ℓ_m`: this is `hh_dir` plus `h i_m = c • ℓ_m`
  have hpar : ∀ i ∈ Finset.univ.erase i_m, det (h i) ℓ_m ≠ 0 := by
    intro i hi hzero
    refine hh_dir i i_m (Finset.ne_of_mem_erase hi) ?_
    have hz : (h i).1 * ℓ_m.2 - (h i).2 * ℓ_m.1 = 0 := hzero
    rw [hc]
    simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    have hring : (h i).1 * (c * ℓ_m.2) - (h i).2 * (c * ℓ_m.1)
        = c * ((h i).1 * ℓ_m.2 - (h i).2 * ℓ_m.1) := by ring
    rw [hring, hz, mul_zero]
  intro n hn
  exact no_edge_parallel_of_Conv_eq_supp_prod _ h (fun i _ => hh_ne i) hpar hS_hull hn

/-! ## Gap 2: agreement on the strip forces global periodicity of `η`

The theorem this text used to introduce was deleted on 2026-09-16 (see the end of this
block).  The text is kept as a section comment; it must not be a doc comment, which would
demand a declaration after it.


This is the geometric core of Claim 3.6: `x_per` is periodic along `ℓ_m`
(`exists_period_parallel`), so agreement on `St_B(ℓ_m)` makes `T^u(η - η̄_m)` periodic
along `ℓ_m` *on the strip*; the `η - η̄_m`-generating set `S_ψ`, having no edge parallel
to `±ℓ_m` (`generatingSet_no_edge_parallel`), sweeps that periodicity outward to a
half-plane; Prop 2.12 (`HalfPlanePeriodicity.lean:103`
`exists_period_multiple_of_halfPlane`) then upgrades half-plane periodicity of the sum
`η = η₁ + ⋯ + η_m` to a genuine global period.

`sorry` reason (revised; the earlier reason "it rests on `generatingSet_no_edge_parallel`
(Gap 1)" was wrong and is corrected rather than deleted):

The sweeping induction itself is **no longer missing**.  It is `eq_of_band_of_generatesAt`
(§3.5), and `isPeriodic_of_strip_agree_of_sweepData` (§3.5) assembles the *whole* of Gap 2
from it `sorry`-free — given *sweep data*: a window `S` generating `η`, whose strict
`dot n`-extremes for a normal `n` of `ℓ_m` are themselves generating sites, together with a
band of `St_B(ℓ_m)` whose `n`-width is at least that of `S`.

What is missing is exactly the production of that sweep data from *this theorem's*
hypotheses, and it is blocked by two independent facts, neither of which is Gap 1:

1. **`S_φ` is the wrong window, and it is the only one this signature supplies.**  `hS_hull`
   pins `Conv S_φ` to the Newton polygon of `φ = ∏_i (X^{h_i} - 1)`, a zonotope with an edge
   parallel to each `h_i` — including `h_{i_m} = c • ℓ_m`.  A window with an edge parallel to
   `ℓ_m` has **no** strict `dot n`-extreme for `n ⊥ ℓ_m`, since two lattice points of that
   edge tie; so `eq_of_band_of_generatesAt` cannot be applied to `S_φ`.  Nor can the sweep
   direction be changed to dodge the tie: `band_forces_orthogonal` (§3.5) shows that any `n`
   with `dot n ℓ_m ≠ 0` makes the band hypothesis unsatisfiable for a finite `B`.  This is
   the formal reason the paper passes to `ψ = ∏_{i ≠ i_m}(X^{h_i} - 1)`, whose zonotope has
   no `ℓ_m`-parallel edge.

2. **The passage to `η - η̄_m` has no analogue at `[AddCommMonoid A]`.**  The paper sweeps
   `η - η̄_m`, not `η`.  Writing `ζ := ∑_{i ≠ i_m} η_i`, the decomposition `η = ζ + η_{i_m}`
   *is* available in a monoid, and so is the return trip (`v ∈ Per ζ` together with
   `v ∈ Per η_{i_m}` gives `v ∈ Per η`).  The outward trip is not: strip periodicity of `η`
   plus periodicity of `η_{i_m}` yields `ζ (z + v) + η_{i_m} z = ζ z + η_{i_m} z`, and
   cancelling the common summand requires a group.  `summand_period_not_reflected` (§5)
   exhibits an `AddCommMonoid` in which that cancellation fails outright, so this is a
   genuine obstruction and not a missing lemma.  `AlphabetReduction.lean` §6 independently
   proves the companion obstruction for the mod-`p` reduction that Lemma 2.5 requires
   (`not_injective_addMonoidHom_zmodFour`: `ZMod 4` admits no injective additive map into any
   `CommRing` with `NoZeroDivisors`).

So Gap 2 is **not** closable "modulo Gap 1" at this signature.  Two further notes:

* Gap 1's signature has since been repaired (2026-09-14) and Gap 1 is now **proved**, but
  that does not move Gap 2.  The old Gap 1 conclusion `±ℓ_m ∉ E ↑S_ψ` was not the statement
  the sweep needs: `Nivat.LE2.E` is indexed by primitive *normals*, so the paper's "`S_ψ` has
  no edge parallel to `±ℓ_m`" is `∀ n ∈ E ↑S_ψ, dot n ℓ_m ≠ 0`, a 90° rotation away, and the
  old form is *refuted*, `sorry`-free, in `MinkowskiEdges.lean` §6
  (`generatingSet_no_edge_parallel_false`).  `generatingSet_no_edge_parallel` above now
  states and proves the correctly oriented form.  The two obstructions listed above are
  untouched by that: they concern `S_φ` (not `S_ψ`) and the monoid `A`.
* `hB_env : Enveloped (↑S_φ) B` is the paper's device for making the band wide enough, but
  `Enveloped` carries no convexity requirement, so `dot n '' B` need not be an interval at
  all; deriving the band hypothesis from `hB_env` is an additional open step, independent of
  the two above.

**Both `periodic_of_agree_on_strip` and `claim36` were deleted 2026-09-16** (false under
current signature: arbitrary AddCommMonoid, unbounded range; counterexample WithTop ℤ,
PLAUSIBLE by A1). See blueprint/NOTE.md.

-/

/-! ## §5. Non-degeneracy

Two things could make §4 empty talk:

* the two clauses of (3.4) could be jointly unsatisfiable (then `claim36` would be false
  for trivial reasons);
* the strip could coincide with the base set (then clause (2) would contradict clause (1)).

Both are ruled out below, with complete proofs.  `strip_ssubset_of_finite` in §1 handles
the second.  The first is handled by an explicit `Bool`-valued witness.

The companion probe `scratch/cl36_nondeg.lean` additionally *refutes* two statements that
an earlier draft of this file asserted (behind `sorry`):
`∀ B ℓ, B.Nonempty → ℓ ≠ 0 → B ⊂ strip B ℓ` is false at `B = Set.univ`, and a fully
periodic configuration *can* admit a shift agreeing on `B` yet disagreeing on the strip.
-/

/-- Indicator of the sublattice `2ℤ × 2ℤ`, used as a concrete witness below. -/
def sublatticeIndicator : Config Bool := fun z => decide (z.1 % 2 = 0 ∧ z.2 % 2 = 0)

/-- **The conclusion shape of Claim 3.6 is satisfiable.**

Explicit witness: `B = {(0,1)}`, `u = (1,0)`, `ℓ = (0,1)` and
`x = y = sublatticeIndicator`.  The shift agrees with the target on `B` yet disagrees at
`(0,0) ∈ strip B ℓ`.  Hence clauses (1) and (2) of (3.4) are jointly satisfiable and
`claim36` is not vacuously false.

Note this witness also shows the disagreement of clause (2) can occur for a configuration
that is itself fully periodic — so clause (2) alone does not encode non-periodicity of
`η`; that is carried by `hη_nonperiodic`. -/
theorem claim36_conclusion_satisfiable :
    ∃ (x y : Config Bool) (u ℓ : ℤ × ℤ) (B : Set (ℤ × ℤ)),
      B.Finite ∧ B.Nonempty ∧ ℓ ≠ 0 ∧ B ⊂ strip B ℓ ∧
      (∀ z ∈ B, T u x z = y z) ∧
      ¬ (∀ z ∈ strip B ℓ, T u x z = y z) := by
  refine ⟨sublatticeIndicator, sublatticeIndicator, (1, 0), (0, 1),
    {((0 : ℤ), (1 : ℤ))}, Set.finite_singleton _, ⟨(0, 1), rfl⟩, by decide, ?_, ?_, ?_⟩
  · exact strip_ssubset_of_finite (Set.finite_singleton _) ⟨(0, 1), rfl⟩ (by decide)
  · rintro z rfl
    show sublatticeIndicator ((0, 1) + (1, 0)) = sublatticeIndicator (0, 1)
    decide
  · intro hcon
    have hmem : ((0 : ℤ), (0 : ℤ)) ∈ strip ({((0 : ℤ), (1 : ℤ))} : Set (ℤ × ℤ)) (0, 1) := by
      refine Or.inr ⟨(0, 1), rfl, 1, ?_⟩
      decide
    have := hcon _ hmem
    revert this
    show sublatticeIndicator ((0, 0) + (1, 0)) = sublatticeIndicator (0, 0) → False
    decide

/-- **The monoid obstruction to Gap 2** (see note 2 on `periodic_of_agree_on_strip`).

Colle's proof of Claim 3.6 sweeps `η - η̄_m`.  At `[AddCommMonoid A]` there is no subtraction,
and the substitute — recover a period of `ζ := ∑_{i ≠ i_m} η_i` from a period of
`η = ζ + η_{i_m}` and a period of `η_{i_m}` — is **false**, not merely unproved.

Witness: `A = ℕ∞`, `η_{i_m} ≡ ⊤` (every vector is a period of it), `ζ` the indicator-style
configuration `z ↦ if z.1 = 0 then 0 else 1`, and `v = (1,0)`.  Then `ζ + η_{i_m} ≡ ⊤` is
`v`-periodic and `η_{i_m}` is `v`-periodic, yet `ζ` is not.  So no amount of periodicity of
the sum and of one summand constrains the other summand in a monoid.

Note this does **not** refute `periodic_of_agree_on_strip`; it refutes the one route to it
that the paper uses.  Whether the theorem is true at `[AddCommMonoid A]` is open. -/
theorem summand_period_not_reflected :
    ∃ (ζ ηm : Config ℕ∞) (v : ℤ × ℤ),
      v ≠ 0 ∧ v ∈ Per ηm ∧ v ∈ Per (fun z => ζ z + ηm z) ∧ v ∉ Per ζ := by
  refine ⟨fun z => if z.1 = 0 then (0 : ℕ∞) else 1, fun _ => ⊤, (1, 0), by decide, ?_, ?_, ?_⟩
  · rw [mem_Per_iff]; rfl
  · rw [mem_Per_iff]; funext z; simp only [T_apply, add_top]
  · intro hcon
    have h := congrFun hcon ((0 : ℤ), (0 : ℤ))
    simp only [T_apply] at h
    norm_num at h

end Nivat.Colle36
