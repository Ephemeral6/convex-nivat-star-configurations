/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.Section8.External
import Nivat.External.Colle.OrbitClosureBasics
import Nivat.External.Colle.HalfPlanePeriodicity
import Nivat.External.Colle.BoyleLind
import Nivat.External.Colle.KMProp18Assembly

/-!
# Towards Colle Theorem 1.14 (= `Nivat.colle_doublyPeriodic`)

This file collects **proved leaves** of the dependency tree of

> **Colle, arXiv:1909.08195v4, Theorem 1.14.**  *"Let `η ∈ 𝒜^{ℤ²}`, with `𝒜 ⊂ ℤ`, be a
> configuration with a non-trivial annihilator.  If `−ℓ ∉ ONED(η)` or `ℓ ∉ ONED(η)` for all
> lines `ℓ ⊂ ℝ²` through the origin, then `η` is fully periodic."*

(quoted verbatim from the arXiv v4 HTML, §1.4).  In `Nivat/Section8/External.lean` this is the
axiom `Nivat.colle_doublyPeriodic`.  **This file does not discharge that axiom.**  What it does
is prove, unconditionally, the elementary leaves of Colle's argument, and give one *machine
checked reduction* whose two remaining obligations are carried as explicit named hypotheses.

## Citation audit (done 2026-09-13 against the primary sources)

* The number `[2, Theorem 1.9]` in `Nivat/Section8/External.lean` is **wrong** for the arXiv v4
  numbering.  In v4, Theorem 1.9 is *Kari and Moutot*'s result, and the statement matching the
  Lean axiom is Theorem 1.14.  (Not fixed here: that file is out of scope for this work.)
* Colle's Theorem 1.9 cites his reference `[11] = J. Kari, E. Moutot, "Decidability and
  Periodicity of Low Complexity Tilings", STACS 2020`; the journal version is his `[12]`,
  `Theory of Computing Systems 67 (2023) 125-148`, doi `10.1007/s00224-021-10063-8`.  In that
  journal version the matching statement is **Theorem 4**: *"Let `c` be a two-dimensional
  configuration that has a non-trivial annihilator.  Then `O(c)` contains a configuration `c'`
  such that `O(c')` has no direction of one-sided determinism."*  It is **not** Theorem 5
  (Theorem 5 is the low-complexity periodic-point theorem, a different statement).

## The shape of Colle's proof of Theorem 1.14 (verbatim structure, §3.1)

1. By contradiction `η` is not fully periodic; with the hypothesis and Proposition 1.8 this
   forces `η` non-periodic.
2. *"According to Theorem 1.9, there exists a configuration `x_per ∈ X_η` where, for every line
   `ℓ`, `−ℓ ∉ ONED(x_per)` whenever `ℓ ∉ ONED(x_per)`. … we get that all oriented lines through
   the origin are one-sided expansive directions on `Orb(x_per)‾`, which due to the Boyle-Lind
   Theorem means that `x_per` is fully periodic."*
   **This step is what `exists_doublyPeriodic_in_orbitClosure` below formalises**, with the two
   external inputs as hypotheses.
3. Claim 3.6, Lemma 3.5 (a maximal-set/compactness construction producing an `(ℓ, ℓ_J)`-region),
   Claim 3.7, then Proposition 2.12 and Boyle-Lind again.  **None of step 3 is formalised
   anywhere in this development.**

## Main results (all unconditional unless said otherwise)

* `Nivat.Colle.mem_orbitClosure_trans` — the orbit closure is transitive.
* `Nivat.Colle.ONED_subset_of_mem_orbitClosure` — `ONED(y) ⊆ ONED(η)` for `y ∈ X_η`.  This is
  used verbatim in the last line of Colle's §3.1 (*"… `∈ ONED(y_per) ⊂ ONED(η)`"*).
* `Nivat.Colle.mem_Per_of_mem_orbitClosure` — periods are inherited by the orbit closure.
* `Nivat.Colle.eq_of_agree_sideOf_of_mem_Per` — a common period pointing into the half-plane
  turns half-plane agreement into equality.
* `Nivat.Colle.not_mem_ONED_of_doublyPeriodic` — `DoublyPeriodic ξ → ONED ξ = ∅`.  This is the
  **easy direction** of Kari-Moutot Proposition 19 (*"A configuration `c` is two-periodic if and
  only if `O(c)` is deterministic in all directions"*), i.e. the easy half of the Boyle-Lind
  corollary.  The hard direction is *not* proved here.
* `Nivat.Colle.hONED_of_mem_orbitClosure` — the hypothesis of Theorem 1.14 passes to the orbit
  closure.
* `Nivat.Colle.boyleLind_holds` — the Boyle–Lind corollary **proved** (for configurations of
  finite range), by importing `Nivat.External.Colle.BoyleLind`.  An earlier revision of this
  file carried it as a hypothesis, and stated it *without* the finiteness hypothesis; in that
  form it is a **false** proposition (`Nivat.BL.boyleLindStatement_false`).
* `Nivat.Colle.exists_doublyPeriodic_in_orbitClosure` — step 2 above, **proved** since
  2026-09-14 (kernel closure `[propext, Classical.choice, Quot.sound]`); it used to be a
  reduction conditional on `KariMoutotTheorem4`.

## Status

**Corrected 2026-09-14 (a).**  This section used to read: *"No `sorry`.  Every theorem here is
proved outright; `KariMoutotTheorem4` is a `Prop`-valued definition used as an explicit
hypothesis, never as an axiom, so `#print axioms` on everything below shows only the Lean core
axioms."*  The last clause was **false**, and was measured false as soon as the gate was able to
see this file at all:

```
Nivat.Colle.exists_doublyPeriodic_in_orbitClosure depends on:
  [propext, sorryAx, Classical.choice, Quot.sound]
```

The claim was true of this file's *text* and false of its *kernel closure*, which is the
distinction the whole project turns on.  `exists_doublyPeriodic_in_orbitClosure` discharges
`KariMoutotTheorem4` by applying `Nivat.KM.kariMoutotTheorem4_of_prop18` to
`Nivat.KM18A.kmProp18`, and `kmProp18` used to call `Nivat.KM17.lemma17`, whose body is `sorry`.

Why it went unnoticed: `scripts/check_axioms.lean` and `scripts/blueprint_check.lean` both
loaded their environment with `importModules #[{module := `Nivat}]`, and the root reaches
exactly one module under `Nivat/External/Colle/`.  Nothing in this file was reachable, so
`collectAxioms` had never been run on any declaration in it.  Both scripts now import
`Nivat.All` (`scripts/gen_all.py`), and `scripts/gate.py` checks that file is complete.

**Update 2026-09-14 (b).**  `Nivat.KM18A.kmProp18` is now a complete proof (its body is
`Nivat.KM17.kmProp18`, which runs the paper's §4 route through Lemma 14, Corollary 15, the joint
limit of Lemma 16 and `KM17.lemma17_of_maximal_family`), so step 2 is closed.  Step 3 closed
as well, in `Theorem114Final.lean` (see the note at the end of this file).

Accurate status, measured:

| declaration | kernel closure |
|---|---|
| `not_mem_ONED_of_doublyPeriodic` | `[propext, Classical.choice, Quot.sound]` |
| `boyleLind_holds` | `[propext, Classical.choice, Quot.sound]` |
| `exists_doublyPeriodic_in_orbitClosure` | `[propext, Classical.choice, Quot.sound]` |
| `theorem114` | `[propext, Classical.choice, Quot.sound]` (measured 2026-09-17) |

So both of Colle's steps are finished, and `theorem114` is a complete proof (2026-09-17
measurement above).  The axiom `Nivat.colle_doublyPeriodic` is discharged in
`Nivat/Section8/ExternalDischarged.lean` via `exists_mem_ONED'`, not by this file.  See
`audit-2026-09-13/theorem114-dependency-tree.md`.
-/

namespace Nivat.Colle

variable {α : Type*}

/-! ### Leaf 5: the easy direction of the Boyle-Lind corollary -/

/-- **A doubly periodic configuration has no one-sided nonexpansive direction.**

This is the easy half of Kari-Moutot [journal version, `Theory Comput. Syst.` **67** (2023)]
Proposition 19: *"A configuration `c` is two-periodic if and only if `O(c)` is deterministic in
all directions."*  Kari-Moutot attribute the proposition to Boyle-Lind; only the **converse**
direction (`ONED = ∅ → DoublyPeriodic`) actually needs Boyle-Lind, and that converse is *not*
proved here — see `BoyleLindStatement`.

Proof: any `w ≠ 0` is non-orthogonal to one of two independent periods `u, v` of `ξ`; a
suitable sign `p ∈ {±u, ±v}` has `⟨p, w⟩ < 0`, and `p` is a period of every element of the
orbit closure, so `eq_of_agree_sideOf_of_mem_Per` applies. -/
theorem not_mem_ONED_of_doublyPeriodic {ξ : Config α} (h : DoublyPeriodic ξ) (w : ℝ × ℝ) :
    w ∉ ONED ξ := by
  rintro ⟨hw, x, hx, y, hy, hne, hagree⟩
  obtain ⟨u, hu, v, hv, hdet⟩ := h
  have hkey : inner2 w u ≠ 0 ∨ inner2 w v ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hdet (det_eq_zero_of_inner2_eq_zero hw hc.1 hc.2)
  obtain ⟨p, hpξ, hp⟩ : ∃ p : ℤ × ℤ, p ∈ Per ξ ∧ inner2 w p < 0 := by
    rcases hkey with h1 | h1
    · rcases h1.lt_or_gt with hlt | hgt
      · exact ⟨u, hu, hlt⟩
      · exact ⟨-u, neg_mem hu, by rw [inner2_neg]; linarith⟩
    · rcases h1.lt_or_gt with hlt | hgt
      · exact ⟨v, hv, hlt⟩
      · exact ⟨-v, neg_mem hv, by rw [inner2_neg]; linarith⟩
  exact hne (eq_of_agree_sideOf_of_mem_Per (mem_Per_of_mem_orbitClosure hpξ hx)
    (mem_Per_of_mem_orbitClosure hpξ hy) hp hagree)

/-- Restatement of `not_mem_ONED_of_doublyPeriodic` as emptiness of `ONED`. -/
theorem ONED_eq_empty_of_doublyPeriodic {ξ : Config α} (h : DoublyPeriodic ξ) :
    ONED ξ = (∅ : Set (ℝ × ℝ)) :=
  Set.eq_empty_iff_forall_notMem.mpr (not_mem_ONED_of_doublyPeriodic h)

/-! ### Leaf 6: the hypothesis of Theorem 1.14 passes to the orbit closure -/

/-! ### The two external inputs of step 2, as explicit statements

Neither of the two `Prop`s below is proved or assumed anywhere in this development.  They are
ordinary definitions, used as *hypotheses* of `exists_doublyPeriodic_in_orbitClosure`, so that
the reduction is machine-checked and the remaining obligation is exactly these two `Prop`s.
-/

/-- **Statement of the Boyle-Lind input** used twice in Colle's §3.1.

Colle: *"… we get that all oriented lines through the origin are one-sided expansive directions
on `Orb(x_per)‾`, which due to the Boyle-Lind Theorem means that `x_per` is fully periodic."*
The underlying theorem is M. Boyle, D. Lind, *Expansive Subdynamics*, Trans. Amer. Math. Soc.
**349** (1997) 55-102 (Colle's reference `[1]`); Kari-Moutot record the same consequence as
their Proposition 19, calling it *"a well-known corollary from a theorem of Boyle and Lind"*.

Note that only the direction stated here is the hard one; the converse is the proved
`not_mem_ONED_of_doublyPeriodic` above.

**Correction, 2026-09-13.**  An earlier revision of this file stated this `Prop` *without* the
finiteness hypothesis, i.e. `∀ x : Config ℤ, (∀ w ≠ 0, w ∉ ONED x) → DoublyPeriodic x`.  That
proposition is **false**: `Nivat.BL.boyleLindStatement_false` refutes it with `x (m, n) = m`,
whose orbit closure is `{z ↦ c + z.1}`, so that `ONED x = ∅` while `x` has only vertical
periods.  Carrying a false `Prop` as a hypothesis makes the reduction below vacuous, hence the
hypothesis `(Set.range x).Finite` below.

**Now proved**, in `Nivat.External.Colle.BoyleLind`
(`Nivat.BL.boyleLindStatement_of_finite`), by an elementary compactness argument rather than a
transcription of Boyle–Lind; see `boyleLind_holds` below.  Finiteness is available at the one
place Colle uses the corollary, and is inherited by the orbit closure
(`Nivat.BL.finite_range_of_mem_orbitClosure`). -/
def BoyleLindStatement : Prop :=
  ∀ x : Config ℤ, (Set.range x).Finite → (∀ w : ℝ × ℝ, w ≠ 0 → w ∉ ONED x) → DoublyPeriodic x

/-- **The Boyle–Lind input is no longer an assumption.**  Proved in
`Nivat.External.Colle.BoyleLind`. -/
theorem boyleLind_holds : BoyleLindStatement :=
  Nivat.BL.boyleLindStatement_of_finite

/-- **Statement of Kari-Moutot Theorem 4**, which is Colle's Theorem 1.9.

Journal version (Colle's reference `[12]`, `Theory Comput. Syst.` **67** (2023) 125-148,
doi `10.1007/s00224-021-10063-8`), §3, Theorem 4, verbatim: *"Let `c` be a two-dimensional
configuration that has a non-trivial annihilator.  Then `O(c)` contains a configuration `c'`
such that `O(c')` has no direction of one-sided determinism."*

Colle's phrasing of the same result (arXiv:1909.08195v4, Theorem 1.9), verbatim: *"Let
`η ∈ 𝒜^{ℤ²}`, with `𝒜 ⊂ ℤ`, be a configuration with a non-trivial annihilator.  Then there
exists a configuration `x ∈ X_η` such that, for every line `ℓ ⊂ ℝ²` through the origin,
`−ℓ ∉ ONED(x)` whenever `ℓ ∉ ONED(x)`."*

Kari-Moutot's "direction of one-sided determinism" is a `u` with `X` deterministic in direction
`u` but not in `−u`; "non-deterministic in direction `u`" is exactly `u ∈ ONED` in Colle's
notation, so "no direction of one-sided determinism" is "`w ∉ ONED(x) → −w ∉ ONED(x)`".

**Not proved in this development.** -/
def KariMoutotTheorem4 : Prop :=
  ∀ ξ : Config ℤ, HasNonzeroAnn ξ →
    ∃ x ∈ orbitClosure ξ, ∀ w : ℝ × ℝ, w ≠ 0 → w ∉ ONED x → -w ∉ ONED x

/-- **Step 2 of Colle's proof of Theorem 1.14, machine-checked.**

A configuration `ξ` with finite range, a non-trivial annihilator and no line `ℓ` with
`±ℓ ∈ ONED(ξ)` has a *doubly periodic element in its orbit closure* — Colle's `x_per`.

**Complete since 2026-09-14.**  The Boyle–Lind corollary is proved
(`Nivat.BL.boyleLindStatement_of_finite`), and Kari–Moutot's Theorem 4 is supplied by
`Nivat.KM.kariMoutotTheorem4_of_prop18` applied to `Nivat.KM18A.kmProp18`, which is now itself
proved (`Nivat.KM17.kmProp18`).  Measured closure:
`[propext, Classical.choice, Quot.sound]`.

**Correction (2026-09-14).**  The paragraph above previously read "**This is a reduction that
has been wired to an incomplete input, not a proof.** … `kmProp18` calls `Nivat.KM17.lemma17`,
whose body is `sorry`.  Measured closure: `[propext, sorryAx, Classical.choice, Quot.sound]`.
The single open leaf underneath is `KMLemma17.lean:1057`."  That was true until `kmProp18` was
rewired off `KM17.lemma17` and onto the paper's §4 route.  `KM17.lemma17` is still `sorry`, but
nothing depends on it; the reason it is not merely "unproved" but mis-stated is recorded in
Part 6 of `KMLemma17.lean`.

This is also **not** the conclusion of Theorem 1.14 (which asserts that `ξ` *itself* is fully
periodic).  Getting from `x_per` to `ξ` is `doublyPeriodic_of_orbitClosure_witness`, now proved in
`Theorem114Final.lean` (see the note at the end of this file) by a nearest-defect limit, not
by Colle §3.1's Lemma 3.5 / Claim 3.6 / Claim 3.7 route.
See `audit-2026-09-13/theorem114-dependency-tree.md`. -/
theorem exists_doublyPeriodic_in_orbitClosure
    {ξ : Config ℤ} (hA : (Set.range ξ).Finite) (hann : HasNonzeroAnn ξ)
    (hONED : ∀ w : ℝ × ℝ, w ≠ 0 → ¬ (w ∈ ONED ξ ∧ -w ∈ ONED ξ)) :
    ∃ x ∈ orbitClosure ξ, DoublyPeriodic x := by
  obtain ⟨x, hx, hxKM⟩ := Nivat.KM.kariMoutotTheorem4_of_prop18 Nivat.KM18A.kmProp18 hA hann
  refine ⟨x, hx, boyleLind_holds x (Nivat.BL.finite_range_of_mem_orbitClosure hA hx) ?_⟩
  intro w hw hmem
  have hx' := hONED_of_mem_orbitClosure hx hONED
  have hnegw : (-w : ℝ × ℝ) ≠ 0 := neg_ne_zero.mpr hw
  have h1 : -w ∉ ONED x := fun h2 => hx' w hw ⟨hmem, h2⟩
  have h3 : w ∉ ONED x := by
    have := hxKM (-w) hnegw h1
    rwa [neg_neg] at this
  exact h3 hmem

/-! ### Step 3 and Theorem 1.14 itself

`Nivat.Colle.doublyPeriodic_of_orbitClosure_witness` (step 3) and `Nivat.Colle.theorem114` used
to live here, the former with a `sorry` body.  **Step 3 is now proved**, in
`Nivat/External/Colle/Theorem114Final.lean`; both statements were moved there character for
character (same names, same namespace), because the proof needs
`Nivat.Colle3.doublyPeriodic_of_isPeriodic` from `Theorem114Step3.lean`, which imports this
file.  Nothing else about them changed. -/

end Nivat.Colle
