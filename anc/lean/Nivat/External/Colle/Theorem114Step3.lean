/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.Theorem114
import Nivat.External.Colle.KMBox
import Nivat.External.Colle.Lemma35
import Nivat.External.Colle.R2Orientation

open Nivat.R2 (inner2_neg_left)

/-!
# Colle Theorem 1.14, step 3: from `x_per` back to `η`

Companion to `Nivat/External/Colle/Theorem114.lean`.  That file formalises **step 2** of Colle's
proof (Kari–Moutot Theorem 4 plus Boyle–Lind produce a doubly periodic `x_per` in the orbit
closure).  This file attacks **step 3**: everything in Colle
(arXiv:1909.08195**v4**) §3.1 after the second paragraph, i.e. Claim 3.6, Lemma 3.5, Claim 3.7,
Proposition 2.12 and the closing appeal to Boyle–Lind and Proposition 1.8.

## Verbatim source (arXiv:1909.08195v4)

**Theorem 1.14.** *"Let `η ∈ 𝒜^{ℤ²}`, with `𝒜 ⊂ ℤ`, be a configuration with a non-trivial
annihilator. If `−ℓ ∉ ONED(η)` or `ℓ ∉ ONED(η)` for all lines `ℓ ⊂ ℝ²` through the origin, then
`η` is fully periodic."*

**Proposition 1.8 (Colle and Garibaldi [4]).** *"Let `η ∈ 𝒜^{ℤ²}` be a periodic configuration.
Then `ℓ ∈ NE(η)` if and only if the antiparallel oriented lines `−ℓ, ℓ ∈ ONED(η)`."*

(The paper writes `NE(η)` for the set of nonexpansive **lines**, and records just before
Proposition 1.8: *"We remark that `ℓ ∈ NE(η)` if and only if `−ℓ ∈ ONED(η)` or `ℓ ∈ ONED(η)`."*
So the content of Proposition 1.8 is: for a periodic `η`, one orientation of a line lying in
`ONED(η)` forces the other orientation to lie in `ONED(η)` as well.)

**§3.1, proof of Theorem 1.14, paragraph 1.** *"Suppose, by contradiction, that `η` is not fully
periodic. In particular, as `−ℓ ∉ ONED(η)` or `ℓ ∉ ONED(η)` for all lines `ℓ ⊂ ℝ²` through the
origin, Proposition 1.8 implies that `η` is non-periodic."*

**§3.1, paragraph 2.** *"According to Theorem 1.9, there exists a configuration `x_per ∈ X_η`
where, for every line `ℓ ⊂ ℝ²` through the origin, `−ℓ ∉ ONED(x_per)` whenever
`ℓ ∉ ONED(x_per)`. … which due to the Boyle-Lind Theorem means that `x_per` is fully
periodic."*  (Formalised in `Theorem114.lean` as `exists_doublyPeriodic_in_orbitClosure`.)

**Claim 3.6.** *"Given an `E(𝒮_φ)`-enveloped set `B ⊂ ℤ²`, there exists `u ∈ ℤ²` such that
`(T^u η)|B = x_per|B`, but `(T^u η)|St_B(ℓ_m) ≠ x_per|St_B(ℓ_m)`, where
`St_B(ℓ_m) := H_B(ℓ_m) ∪ H_B(−ℓ_m)` is the strip of `B` along of `ℓ_m`."*

**Lemma 3.5 (item (i)).** *"… then there exist an `(ℓ_ι, ℓ_J)`-region `Â_∞`, with
`ι+1 ≤ J ≤ ι+m−1`, a configuration `ϑ ∈ X_η` and `ε ∈ ℤ_+` such that
`ϑ|Â_∞^{(ε)} = x̂_per|Â_∞^{(ε)}`, but `ϑ|Â_∞^{(ε+1)} ≠ x̂_per|Â_∞^{(ε+1)}` …"*

**Claim 3.7.** *"The set `{T^{t v_{ℓ'}} ϑ : t ∈ ℤ_+}` does not have fully periodic accumulation
points."*

**§3.1, final paragraph.** *"To reach a contradiction and concludes the proof, we will show that
`−ℓ′, ℓ′ ∈ ONED(η)`. Since `x̂_per` is fully periodic, then `ϑ|Â_∞^{(ε)} = x̂_per|Â_∞^{(ε)}` is
periodic with period parallel to `ℓ′`. Hence, Proposition 2.12 implies that any accumulation
point `y_per` of `{T^{t v_{ℓ'}} ϑ : t ∈ ℤ_+}` is periodic with period parallel to `ℓ′`, but,
according to Claim 3.7, not fully periodic. Therefore, from Boyle-Lind Theorem and Proposition
1.8 result that `−ℓ′, ℓ′ ∈ ONED(y_per) ⊂ ONED(η)`, which is a contradiction."*

**Proposition 2.12 (Kari and Szabados [14]).** *"Let `η ∈ 𝒜^{ℤ²}` be a configuration and suppose
`η = η_1 + ⋯ + η_m` is a `R`-periodic decomposition, `h_i ∈ ℤ²` is a period for `η_i` and
`h_1, …, h_m ∈ ℤ²` vectors in pairwise distinct directions. If `η|ℋ(ℓ)` is periodic with period
parallel to some oriented line `ℓ ⊂ ℝ²`, then `η` is periodic with period parallel to `ℓ`."*

## What is proved here, and what is assumed

**Assumed** (as an explicit `Prop`-valued *hypothesis*, never as an `axiom` and never with
`sorry`):

* `Nivat.Colle3.ColleStep3Chain` — Claim 3.6 + Lemma 3.5 + Claim 3.7 + Proposition 2.12,
  packaged as: *for every non-periodic finite-range `η` with a non-trivial annihilator whose
  orbit closure contains a doubly periodic configuration, there are `ϑ ∈ X_η` and a nonzero
  direction `v` (Colle's `v_{ℓ'}`) such that every accumulation point of `{T^{tv} ϑ}` is
  periodic (Proposition 2.12) but none is doubly periodic (Claim 3.7).*  It is a `def … : Prop`,
  taken as a hypothesis of `colle114_step3` and `colle114_of`; see its docstring for the exact
  correspondence with the source and for what is lost.

**Proved outright** (no `sorry`, only Lean's core axioms):

* `Nivat.Colle3.doublyPeriodic_of_notMem_ONED_perp` — the analytic heart.  A configuration of
  finite range with a nonzero period `h` and **one** direction `w ⊥ h` that is *not* one-sided
  nonexpansive is already doubly periodic.  This is a *one-sided* strengthening of the
  Boyle–Lind corollary: `Nivat.BL.boyleLind` needs *every* direction to be expansive, here a
  single direction orthogonal to a known period suffices.  It is Colle–Garibaldi Prop. 3.13
  (the proof of the Proposition 1.8 quoted above); cf. Cyr–Kra Lemma 4.10.  The row-state
  determinism argument is in `doublyPeriodic_of_window`, the finite-range-to-finite-alphabet
  reduction in the wrapper; the finite determinism window comes from Kari–Moutot §2.2
  (`Nivat.KMBox.exists_window_of_notMem_ONED`).
* `Nivat.Colle3.prop_1_8` — **Proposition 1.8** in the form Colle uses it: for a periodic
  configuration of finite range, `w ∈ ONED` implies `-w ∈ ONED`.  Consequently
  `Nivat.Colle3.doublyPeriodic_of_isPeriodic`: under the hypothesis of Theorem 1.14, every
  *periodic* member of `X_η` is *doubly* periodic.  This single lemma discharges both uses of
  Proposition 1.8 in §3.1 (paragraph 1 and the final paragraph) **and** the final appeal to
  Boyle–Lind.
* `Nivat.Colle3.exists_accPointAlong` — the compactness step "let `y_per` be an accumulation
  point of `{T^{t v_{ℓ'}} ϑ}`", together with `mem_orbitClosure_of_accPointAlong`.
* `Nivat.Colle3.colle114_step3` — the assembly of step 3 from `ColleStep3Chain` (below).
* `Nivat.Colle3.colle114_of` — Theorem 1.14 itself, from the two remaining hypotheses
  `Nivat.Colle.KariMoutotTheorem4` and `ColleStep3Chain`.

## Status

**No `sorry` and no new `axiom` anywhere in this file**; every declaration depends only on
`[propext, Classical.choice, Quot.sound]`.  The remaining mathematical debt is entirely visible
in the *signatures* of `colle114_step3` / `colle114_of`, which take `ColleStep3Chain` (and
`KariMoutotTheorem4`) as hypotheses.  The axiom `Nivat.colle_doublyPeriodic` is therefore **not**
discharged yet: it needs a proof of `ColleStep3Chain`.

## Change log

Append-only.  Each entry records what changed, why, and what prompted it.

**2026-09-13 — `ColleStep3Chain` weakened by adding `hONED` to its antecedent.**

*What changed.*  Exactly two declarations, plus docstrings:
1. `ColleStep3Chain` gained the hypothesis `∀ w : ℝ × ℝ, w ≠ 0 → ¬ (w ∈ ONED η ∧ -w ∈ ONED η)`,
   inserted after `¬ IsPeriodic η →` and before `∀ xper ∈ orbitClosure η`.
2. `colle114_step3` passes its own `hONED` at the single point where `hChain` is *applied*.
   (`colle114_of` merely forwards `hChain` to `colle114_step3` unapplied, so it needed no
   edit.)  The statements of `colle114_step3` and `colle114_of` are **unchanged**, byte for
   byte, and their axiom dependencies are unchanged.

*Why this is a weakening, and why it is free.*  `ColleStep3Chain` is consumed only in
hypothesis position.  Narrowing its antecedent makes the `Prop` itself logically weaker, hence
every theorem taking it as a hypothesis logically **stronger**: `colle114_of` now concludes the
same thing from strictly less.  The cost at the use site is zero, because `hONED` is already a
hypothesis of `colle114_step3` about the very `ξ` handed to `hChain` — the change is one extra
argument at one application, no proof restructuring.

*What prompted it.*  An independent audit of `ColleStep3Chain` (recorded in
`audit-2026-09-13/ZERO-AXIOM-判据与进度.md`, item "`hONED` 的不对称") observed that
`colle114_of` assumes `hONED` while `ColleStep3Chain` universally quantified over *all*
non-periodic finite-range `η` with a non-trivial annihilator, including those Colle's §3
construction never touches: the construction lives inside the proof by contradiction and uses
the non-expansiveness hypothesis throughout.  The formalisation was therefore assuming a
statement strictly stronger than the paper proves — debt carried for nothing.  Note this fixes
the *scope* mismatch only; it does **not** address the separate, still-open question of whether
the black-boxed conclusion is a faithful packaging of Claims 3.6/3.7 + Lemma 3.5 + Prop. 2.12.

*Satisfiability.*  `ColleStep3Chain` still has no satisfiability witness, and after this change
a witness is even harder to come by (the antecedent is narrower).  Deliberately not pursued:
see §6 and the `ColleStep3Chain` docstring.
-/

namespace Nivat.Colle3

open Nivat Nivat.Colle

variable {α : Type*}

/-! ## §0.  Bilinearity of `det`, and a lattice basis adapted to a period

Nothing in this section is specific to Colle; it is the linear algebra needed to slice `ℤ²`
into the lines parallel to a period. -/

theorem det_add_right (u z z' : ℤ × ℤ) : det u (z + z') = det u z + det u z' := by
  simp only [det, Prod.fst_add, Prod.snd_add]; ring

theorem det_add_left (u u' z : ℤ × ℤ) : det (u + u') z = det u z + det u' z := by
  simp only [det, Prod.fst_add, Prod.snd_add]; ring

theorem det_zsmul_right (c : ℤ) (u z : ℤ × ℤ) : det u (c • z) = c * det u z := by
  simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

theorem det_zsmul_left (c : ℤ) (u z : ℤ × ℤ) : det (c • u) z = c * det u z := by
  simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

theorem det_neg_left (u z : ℤ × ℤ) : det (-u) z = -det u z := by
  simp only [det, Prod.fst_neg, Prod.snd_neg]; ring

/-- **A unimodular basis adapted to a nonzero lattice vector `h`.**  Write `h = d • h₀` with
`d = gcd(h₁, h₂) > 0` and `h₀` primitive, and let `q` complete `h₀` to a basis of `ℤ²`
(`det h₀ q = 1`).  Then `det h₀ ·` is the "row index" and `q` steps from one row to the next. -/
private theorem adapted_aux {d h1 h2 a₁ a₂ A B : ℤ} (hd : d ≠ 0)
    (e1 : h1 = d * a₁) (e2 : h2 = d * a₂) (hbez : d = h1 * A + h2 * B) :
    det (a₁, a₂) (-B, A) = 1 := by
  have hkey : d * (a₁ * A + a₂ * B) = d * 1 := by
    linear_combination hbez.symm - A * e1 - B * e2
  have h3 := mul_left_cancel₀ hd hkey
  simp only [det]
  linarith [h3]

theorem exists_adapted_basis {h : ℤ × ℤ} (hh : h ≠ 0) :
    ∃ (d : ℤ) (h₀ q : ℤ × ℤ), 0 < d ∧ h = d • h₀ ∧ det h₀ q = 1 := by
  have hdpos : 0 < (Int.gcd h.1 h.2 : ℤ) := by
    have : Int.gcd h.1 h.2 ≠ 0 := by
      intro hc
      rw [Int.gcd_eq_zero_iff] at hc
      exact hh (Prod.ext hc.1 hc.2)
    omega
  obtain ⟨a₁, ha₁⟩ : (Int.gcd h.1 h.2 : ℤ) ∣ h.1 := Int.gcd_dvd_left h.1 h.2
  obtain ⟨a₂, ha₂⟩ : (Int.gcd h.1 h.2 : ℤ) ∣ h.2 := Int.gcd_dvd_right h.1 h.2
  exact ⟨(Int.gcd h.1 h.2 : ℤ), (a₁, a₂), (-(Int.gcdB h.1 h.2), Int.gcdA h.1 h.2), hdpos,
    Prod.ext (by simpa using ha₁) (by simpa using ha₂),
    adapted_aux (ne_of_gt hdpos) ha₁ ha₂ (Int.gcd_eq_gcd_ab h.1 h.2)⟩

theorem det_sub_right (u z z' : ℤ × ℤ) : det u (z - z') = det u z - det u z' := by
  simp only [det, Prod.fst_sub, Prod.snd_sub]; ring

theorem det_self (u : ℤ × ℤ) : det u u = 0 := by
  simp only [det]; ring

/-- For any `h₀` and `k : ℤ`, we have `det h₀ (z + k • h₀) = det h₀ z`. -/
theorem det_add_zsmul_self (h₀ z : ℤ × ℤ) (k : ℤ) : det h₀ (z + k • h₀) = det h₀ z := by
  rw [det_add_right, det_zsmul_right, det_self, mul_zero, add_zero]

/-- The coordinates of `z` in the basis `(h₀, q)` of `exists_adapted_basis`. -/
theorem eq_add_of_det_eq_one {h₀ q : ℤ × ℤ} (hq : det h₀ q = 1) (z : ℤ × ℤ) :
    z = (det z q) • h₀ + (det h₀ z) • q := by
  have h1 : h₀.1 * q.2 - h₀.2 * q.1 = 1 := hq
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, det]
    linear_combination (z.1 : ℤ) * h1.symm
  · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, det]
    linear_combination (z.2 : ℤ) * h1.symm

/-! ## §1.  `ONED` in the presence of a period: transversality and the determinant form

Colle never spells these out; they are the routine content of the phrase *"period parallel to
`ℓ`"*.  The point is that a nonexpansive direction of a configuration with period `h` must be
**orthogonal** to `h` (`notMem_ONED_of_inner2_ne_zero`), and that for such a direction the
half-plane `sideOf w` is described by the sign of `det h ·` (`sideOf_eq_of_perp`). -/

/-- **Transversality.**  A direction not orthogonal to a period is one-sided *expansive*.

This is `eq_of_agree_sideOf_of_mem_Per` packaged as a statement about `ONED`: if `h ∈ Per y` and
`⟨w, h⟩ ≠ 0` then `w ∉ ONED y`, because one of `±h` points strictly into `sideOf w` and periods
of `y` are periods of every element of `X_y`. -/
theorem notMem_ONED_of_inner2_ne_zero {y : Config α} {h : ℤ × ℤ} (hh : h ∈ Per y)
    {w : ℝ × ℝ} (hw : inner2 w h ≠ 0) : w ∉ ONED y := by
  rintro ⟨-, x, hx, x', hx', hne, hagree⟩
  obtain ⟨p, hp, hpneg⟩ : ∃ p : ℤ × ℤ, p ∈ Per y ∧ inner2 w p < 0 := by
    rcases hw.lt_or_gt with hlt | hgt
    · exact ⟨h, hh, hlt⟩
    · exact ⟨-h, neg_mem hh, by rw [inner2_neg]; linarith⟩
  exact hne (eq_of_agree_sideOf_of_mem_Per (mem_Per_of_mem_orbitClosure hp hx)
    (mem_Per_of_mem_orbitClosure hp hx') hpneg hagree)

/-- A nonzero `w ∈ ℝ²` orthogonal to a nonzero `h ∈ ℤ²` is a nonzero real multiple of the
linear form `det h ·`. -/
theorem exists_scale_of_perp {h : ℤ × ℤ} (hh : h ≠ 0) {w : ℝ × ℝ} (hw : w ≠ 0)
    (hperp : inner2 w h = 0) :
    ∃ c : ℝ, c ≠ 0 ∧ ∀ z : ℤ × ℤ, inner2 w z = c * (det h z : ℤ) := by
  have hperp' : (h.1 : ℝ) * w.1 + (h.2 : ℝ) * w.2 = 0 := hperp
  have hh' : ¬ (h.1 = 0 ∧ h.2 = 0) := fun hc => hh (Prod.ext hc.1 hc.2)
  by_cases h1 : h.1 = 0
  · have h2 : h.2 ≠ 0 := fun hc => hh' ⟨h1, hc⟩
    have h2r : (h.2 : ℝ) ≠ 0 := Int.cast_ne_zero.mpr h2
    have hw2 : w.2 = 0 := by
      have : (h.2 : ℝ) * w.2 = 0 := by rw [h1] at hperp'; push_cast at hperp' ⊢; linarith
      exact (mul_eq_zero.mp this).resolve_left h2r
    have hw1 : w.1 ≠ 0 := fun hc => hw (Prod.ext hc hw2)
    refine ⟨-w.1 / (h.2 : ℝ), by simp [hw1, h2r], fun z => ?_⟩
    show (z.1 : ℝ) * w.1 + (z.2 : ℝ) * w.2 = _
    rw [hw2, det, h1]
    simp only [mul_zero, add_zero, zero_mul, zero_sub, Int.cast_neg, Int.cast_mul]
    field_simp [h2r]
  · have h1r : (h.1 : ℝ) ≠ 0 := Int.cast_ne_zero.mpr h1
    have hwe : w.1 = -((h.2 : ℝ) * w.2) / (h.1 : ℝ) := by field_simp; linarith
    have hw2 : w.2 ≠ 0 := by
      intro hc
      exact hw (Prod.ext (by rw [hwe, hc]; simp) hc)
    refine ⟨w.2 / (h.1 : ℝ), by simp [hw2, h1r], fun z => ?_⟩
    show (z.1 : ℝ) * w.1 + (z.2 : ℝ) * w.2 = _
    rw [hwe, det]
    push_cast
    field_simp
    ring

/-- For `w` orthogonal to `h` with positive scale `c`, `sideOf w` is `{z : det h z ≤ 0}`. -/
theorem sideOf_eq_of_scale {h : ℤ × ℤ} {w : ℝ × ℝ} {c : ℝ} (hc : 0 < c)
    (hcw : ∀ z : ℤ × ℤ, inner2 w z = c * (det h z : ℤ)) (z : ℤ × ℤ) :
    z ∈ sideOf w ↔ det h z ≤ 0 := by
  show inner2 w z ≤ 0 ↔ _
  rw [hcw z]
  constructor
  · intro hle
    by_contra hpos
    have : (0 : ℤ) < det h z := by omega
    have : (0 : ℝ) < ((det h z : ℤ) : ℝ) := by exact_mod_cast this
    nlinarith
  · intro hle
    have : ((det h z : ℤ) : ℝ) ≤ 0 := by exact_mod_cast hle
    nlinarith

/-! ## §2.  Accumulation points along a direction

The compactness step *"let `y_per` be an accumulation point of `{T^{t v} ϑ : t ∈ ℕ}`"* from
Colle §3.1. -/

/-- `y` is an accumulation point of the orbit of `ϑ` along direction `v`. -/
def IsAccPointAlong (v : ℤ × ℤ) (ϑ y : Config α) : Prop :=
  ∀ (W : Finset (ℤ × ℤ)) (M : ℕ), ∃ t : ℕ, M ≤ t ∧ ∀ z ∈ W, y z = T ((t : ℤ) • v) ϑ z

/-- **Existence of an accumulation point along any direction**, when the configuration has finite
range.  This is `Nivat.Colle35.exists_accumulationPoint` specialised to the sequence
`F t := T (t • v) ϑ`. -/
theorem exists_accPointAlong {ϑ : Config α} (hS : (Set.range ϑ).Finite) (v : ℤ × ℤ) :
    ∃ y : Config α, IsAccPointAlong v ϑ y :=
  Nivat.Colle35.exists_accumulationPoint hS (fun t => T ((t : ℤ) • v) ϑ)
    (fun _ _ => Set.mem_range_self _)

/-- An accumulation point of `{T^{tv} ϑ : t ∈ ℕ}` lies in the orbit closure of `ϑ`. -/
theorem mem_orbitClosure_of_accPointAlong {θ ϑ y : Config α} {v : ℤ × ℤ}
    (hϑ : ϑ ∈ orbitClosure θ) (hy : IsAccPointAlong v ϑ y) : y ∈ orbitClosure θ :=
  Nivat.Colle35.mem_orbitClosure_of_accumulationPoint
    (fun t => T_mem_of_mem_orbitClosure hϑ _) hy

/-! ## §3.  Proposition 1.8 and its consequence

**Proposition 1.8 (Colle and Garibaldi [4]).** *"Let `η ∈ 𝒜^{ℤ²}` be a periodic configuration.
Then `ℓ ∈ NE(η)` if and only if the antiparallel oriented lines `−ℓ, ℓ ∈ ONED(η)`."*

The hard content is: for a **periodic** configuration of finite range, one orientation in `ONED`
forces the other.  We prove the stronger result `doublyPeriodic_of_notMem_ONED_perp`: a single
direction `w` orthogonal to a period and *not* in `ONED` already forces double periodicity. -/

/-- Sign extraction: from `s * n < 0` over `ℝ` with `n : ℤ`, read off the sign of `n`. -/
private theorem int_sign_of_mul_neg {s : ℝ} {n : ℤ} (hsn : s * (n : ℝ) < 0) :
    (0 < s → n < 0) ∧ (s < 0 → 0 < n) := by
  refine ⟨fun hs => ?_, fun hs => ?_⟩
  · by_contra hcon
    push_neg at hcon
    have hn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hcon
    nlinarith
  · by_contra hcon
    push_neg at hcon
    have hn : (n : ℝ) ≤ 0 := by exact_mod_cast hcon
    nlinarith

/-- **The lattice core of one-sided Boyle–Lind**, with every real-number datum already converted
into lattice data.

Hypotheses: `h = d • h₀` (`d > 0`) is a period of `y`, `(h₀, q)` is a unimodular basis of `ℤ²`
(`det h₀ q = 1`), and `B` is a finite *determinism window* lying strictly below the line
`det h₀ · = 0` such that agreement on `B` pins down the cell `0` throughout `orbitClosure y` —
this last datum is exactly Kari–Moutot §2.2 (`Nivat.KMBox.exists_window_of_notMem_ONED`).
Conclusion: `y` is doubly periodic, with the transverse period a multiple of `q`.

The argument (Colle–Garibaldi Prop. 3.13 = Colle Prop. 1.8; cf. Cyr–Kra Lemma 4.10):
* `lev z := det h₀ z` is the row index; `h` is a period, so a *row state* `F b` — the restriction
  of `y` to the `d · N` points `r • h₀ + (b - 1 - j) • q` with `0 ≤ r < d`, `0 ≤ j < N` — carries
  all of `y` on the band `lev ∈ [b - N, b - 1]` (`hband`, using `hres`: every `z` is
  `r • h₀ + (lev z) • q` modulo the period `h`, with `0 ≤ r < d`).
* The window `B` fits inside the band below any row, so band agreement propagates one row upwards
  (`hrow`), whence the state sequence `F` is *forward deterministic*: `F b = F (b + k)` implies
  `F (b+1) = F (b+1+k)` (`hstep`, `hiter`).
* The state space is finite, so some state `s` recurs at levels going to `-∞` (`hrec`,
  pigeonhole on `Finset.univ.inf'`).  Two occurrences `n₁ < n₂` of `s` give `F` periodicity on
  `[n₁, ∞)`, and an occurrence below any given `m` propagates it to **all** of `ℤ` (`hall`).
  This is what replaces the naive pigeonhole, which only yields periodicity on an upper
  half-plane.
* Hence `u := (n₂ - n₁) • q ∈ Per y` (`huper`) and `det h u = (n₂ - n₁) * d ≠ 0`. -/
private theorem doublyPeriodic_of_window [Finite α] {y : Config α} {h : ℤ × ℤ} (hh : h ∈ Per y)
    {d : ℤ} {h₀ q : ℤ × ℤ} (hd : 0 < d) (hhd : h = d • h₀) (hq : det h₀ q = 1)
    (B : Finset (ℤ × ℤ)) (hBlev : ∀ z ∈ B, det h₀ z ≤ -1)
    (hBdet : ∀ p ∈ orbitClosure y, ∀ p' ∈ orbitClosure y,
      (∀ z ∈ B, p z = p' z) → p 0 = p' 0) :
    DoublyPeriodic y := by
  classical
  -- level of a point in normal form
  have hlevpt : ∀ r m : ℤ, det h₀ (r • h₀ + m • q) = m := by
    intro r m
    have h1 : det h₀ q = 1 := hq
    simp only [det, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul] at h1 ⊢
    linear_combination m * h1
  -- every point is `r • h₀ + (level) • q` modulo the period `h`, with `0 ≤ r < d`
  have hres : ∀ z : ℤ × ℤ, ∃ r k : ℤ, 0 ≤ r ∧ r < d ∧
      z = (r • h₀ + (det h₀ z) • q) + k • h := by
    intro z
    refine ⟨det z q % d, det z q / d, Int.emod_nonneg _ (ne_of_gt hd),
      Int.emod_lt_of_pos _ hd, ?_⟩
    have hz : z = (det z q) • h₀ + (det h₀ z) • q := eq_add_of_det_eq_one hq z
    have hA : det z q = d * (det z q / d) + det z q % d := (Int.mul_ediv_add_emod _ _).symm
    have key : (d * (det z q / d) + det z q % d) • h₀ + (det h₀ z) • q
        = ((det z q % d) • h₀ + (det h₀ z) • q) + (det z q / d) • (d • h₀) := by
      rw [smul_smul, mul_comm (det z q / d) d, add_smul]
      abel
    rw [← hA] at key
    rw [hhd]
    exact hz.trans key
  -- the depth of the determinism window
  obtain ⟨N, hNB⟩ : ∃ N : ℕ, ∀ z ∈ B, -(N : ℤ) ≤ det h₀ z :=
    ⟨B.sup (fun z => (- det h₀ z).toNat), fun z hz => by
      have h1 : (- det h₀ z).toNat ≤ B.sup (fun z => (- det h₀ z).toNat) :=
        Finset.le_sup (f := fun z => (- det h₀ z).toNat) hz
      omega⟩
  -- `F b` = the state of `y` on the `N` rows strictly below level `b`
  obtain ⟨F, hF⟩ : ∃ F : ℤ → (Fin d.toNat × Fin N → α), ∀ (b : ℤ) (p : Fin d.toNat × Fin N),
      F b p = y (((p.1 : ℕ) : ℤ) • h₀ + (b - 1 - ((p.2 : ℕ) : ℤ)) • q) :=
    ⟨_, fun _ _ => rfl⟩
  have hFto : ∀ b b' : ℤ, F b = F b' → ∀ r j : ℤ, 0 ≤ r → r < d → 0 ≤ j → j < (N : ℤ) →
      y (r • h₀ + (b - 1 - j) • q) = y (r • h₀ + (b' - 1 - j) • q) := by
    intro b b' hbb r j hr0 hrd hj0 hjN
    have hr' : r.toNat < d.toNat := by omega
    have hj' : j.toNat < N := by omega
    have hcong := congrFun hbb ((⟨r.toNat, hr'⟩ : Fin d.toNat), (⟨j.toNat, hj'⟩ : Fin N))
    rw [hF, hF] at hcong
    simpa [Int.toNat_of_nonneg hr0, Int.toNat_of_nonneg hj0] using hcong
  have hFof : ∀ b b' : ℤ, (∀ r j : ℤ, 0 ≤ r → r < d → 0 ≤ j → j < (N : ℤ) →
      y (r • h₀ + (b - 1 - j) • q) = y (r • h₀ + (b' - 1 - j) • q)) → F b = F b' := by
    intro b b' hpt
    funext p
    have h1 := p.1.isLt
    have h2 := p.2.isLt
    rw [hF, hF]
    exact hpt _ _ (by omega) (by omega) (by omega) (by omega)
  -- equal states at levels `b` and `b + k` ⟹ `y` and `T^{k q} y` agree on the whole band
  have hband : ∀ b k : ℤ, F b = F (b + k) →
      ∀ z : ℤ × ℤ, b - (N : ℤ) ≤ det h₀ z → det h₀ z ≤ b - 1 → y z = y (z + k • q) := by
    intro b k hbk z hz1 hz2
    obtain ⟨r, m, hr0, hrd, hzr⟩ := hres z
    obtain ⟨L, hL⟩ : ∃ L : ℤ, det h₀ z = L := ⟨_, rfl⟩
    rw [hL] at hzr hz1 hz2
    have hmem : m • h ∈ Per y := AddSubgroup.zsmul_mem _ hh m
    have hpt := hFto b (b + k) hbk r (b - 1 - L) hr0 hrd (by omega) (by omega)
    rw [show b - 1 - (b - 1 - L) = L from by ring,
      show b + k - 1 - (b - 1 - L) = L + k from by ring] at hpt
    rw [hzr]
    rw [show ((r • h₀ + L • q) + m • h) + k • q = (r • h₀ + (L + k) • q) + m • h from by
      rw [add_smul]; abel]
    rw [Per.apply hmem, Per.apply hmem]
    exact hpt
  -- band agreement propagates one row upwards: this is the determinism window at work
  have hrow : ∀ (u : ℤ × ℤ) (b : ℤ),
      (∀ z : ℤ × ℤ, b - (N : ℤ) ≤ det h₀ z → det h₀ z ≤ b - 1 → y z = y (z + u)) →
      ∀ v : ℤ × ℤ, det h₀ v = b → y v = y (v + u) := by
    intro u b hbb v hv
    have h3 : ∀ z ∈ B, T v y z = T (v + u) y z := by
      intro z hz
      have hl : det h₀ (z + v) = det h₀ z + b := by rw [det_add_right, hv]
      have h4 := hbb (z + v) (by rw [hl]; have := hNB z hz; omega)
        (by rw [hl]; have := hBlev z hz; omega)
      show y (z + v) = y (z + (v + u))
      rw [h4, show z + v + u = z + (v + u) from by abel]
    have h5 := hBdet _ (T_mem_orbitClosure y v) _ (T_mem_orbitClosure y (v + u)) h3
    show y v = y (v + u)
    have e1 : T v y 0 = y v := by show y (0 + v) = y v; rw [zero_add]
    have e2 : T (v + u) y 0 = y (v + u) := by show y (0 + (v + u)) = y (v + u); rw [zero_add]
    rw [← e1, ← e2]
    exact h5
  -- forward determinism of the state sequence
  have hstep : ∀ b k : ℤ, F b = F (b + k) → F (b + 1) = F (b + 1 + k) := by
    intro b k hbk
    have hb := hband b k hbk
    have hr := hrow (k • q) b hb
    have hb1 : ∀ z : ℤ × ℤ, (b + 1) - (N : ℤ) ≤ det h₀ z → det h₀ z ≤ (b + 1) - 1 →
        y z = y (z + k • q) := by
      intro z h1 h2
      rcases eq_or_lt_of_le h2 with heq | hlt
      · exact hr z (by omega)
      · exact hb z (by omega) (by omega)
    refine hFof _ _ ?_
    intro r j hr0 hrd hj0 hjN
    have hlev : det h₀ (r • h₀ + (b + 1 - 1 - j) • q) = b + 1 - 1 - j := hlevpt r _
    have h6 := hb1 (r • h₀ + (b + 1 - 1 - j) • q) (by rw [hlev]; omega) (by rw [hlev]; omega)
    rw [h6, show (r • h₀ + (b + 1 - 1 - j) • q) + k • q
      = r • h₀ + (b + 1 + k - 1 - j) • q from by
        rw [show b + 1 + k - 1 - j = (b + 1 - 1 - j) + k from by ring, add_smul]; abel]
  have hiter : ∀ b k : ℤ, F b = F (b + k) → ∀ n : ℤ, b ≤ n → F n = F (n + k) := by
    intro b k hbk n hn
    induction n, hn using Int.le_induction with
    | base => exact hbk
    | succ m _ ih => exact hstep m k ih
  -- some state recurs arbitrarily far down
  haveI : Nonempty α := ⟨y 0⟩
  haveI : Fintype (Fin d.toNat × Fin N → α) := Fintype.ofFinite _
  have hrec : ∃ s : Fin d.toNat × Fin N → α, ∀ M : ℤ, ∃ n : ℤ, n ≤ M ∧ F n = s := by
    by_contra hcon
    push_neg at hcon
    choose M hM using hcon
    have hne : (Finset.univ : Finset (Fin d.toNat × Fin N → α)).Nonempty := Finset.univ_nonempty
    have h1 : Finset.univ.inf' hne M ≤ M (F (Finset.univ.inf' hne M)) :=
      Finset.inf'_le M (Finset.mem_univ _)
    exact hM _ _ h1 rfl
  obtain ⟨s, hs⟩ := hrec
  obtain ⟨n₂, hn₂le, hn₂⟩ := hs 0
  obtain ⟨n₁, hn₁le, hn₁⟩ := hs (n₂ - 1)
  have hk : 0 < n₂ - n₁ := by omega
  have hper1 : ∀ n : ℤ, n₁ ≤ n → F n = F (n + (n₂ - n₁)) := by
    refine hiter n₁ (n₂ - n₁) ?_
    rw [hn₁, show n₁ + (n₂ - n₁) = n₂ from by ring, hn₂]
  -- hence the state sequence is periodic on all of `ℤ`, not just above `n₁`
  have hall : ∀ m : ℤ, F m = F (m + (n₂ - n₁)) := by
    intro m
    obtain ⟨n₀, hn₀le, hn₀⟩ := hs (min m n₁)
    have hle1 : n₀ ≤ m := le_trans hn₀le (min_le_left _ _)
    have hle2 : n₀ ≤ n₁ := le_trans hn₀le (min_le_right _ _)
    have hsame : ∀ n : ℤ, n₀ ≤ n → F n = F (n + (n₁ - n₀)) := by
      refine hiter n₀ (n₁ - n₀) ?_
      rw [hn₀, show n₀ + (n₁ - n₀) = n₁ from by ring, hn₁]
    have e1 : F m = F (m + (n₁ - n₀)) := hsame m hle1
    have e3 : F (m + (n₁ - n₀)) = F (m + (n₁ - n₀) + (n₂ - n₁)) := hper1 _ (by omega)
    have e2 : F (m + (n₂ - n₁)) = F (m + (n₂ - n₁) + (n₁ - n₀)) := hsame _ (by omega)
    rw [e1, e3, e2,
      show m + (n₁ - n₀) + (n₂ - n₁) = m + (n₂ - n₁) + (n₁ - n₀) from by ring]
  -- and `(n₂ - n₁) • q` is a second period, transverse to `h`
  have huper : ((n₂ - n₁) • q) ∈ Per y := by
    rw [mem_Per_iff]
    funext v
    show y (v + (n₂ - n₁) • q) = y v
    exact (hrow ((n₂ - n₁) • q) (det h₀ v)
      (hband (det h₀ v) (n₂ - n₁) (hall (det h₀ v))) v rfl).symm
  refine ⟨h, hh, (n₂ - n₁) • q, huper, ?_⟩
  have hdd : det h ((n₂ - n₁) • q) = (n₂ - n₁) * d := by
    rw [det_zsmul_right, hhd, det_zsmul_left, hq, mul_one]
  rw [hdd]
  exact mul_ne_zero (by omega) (by omega)

/-- `doublyPeriodic_of_notMem_ONED_perp` for a *finite alphabet*: the real direction `w` is
converted into the linear form `det h ·` by `exists_scale_of_perp`, the window `B` is produced by
Kari–Moutot §2.2 (`Nivat.KMBox.exists_window_of_notMem_ONED`), and the two possible signs of the
scale `c` are handled by running the lattice core on the basis `(h₀, q)` resp. `(-h₀, -q)` — i.e.
by reversing the orientation of the line so that the window always sits *below* it. -/
private theorem doublyPeriodic_of_notMem_ONED_perp_finite [Finite α] {y : Config α}
    {h : ℤ × ℤ} (hh : h ∈ Per y) (hh' : h ≠ 0)
    {w : ℝ × ℝ} (hw : w ≠ 0) (hperp : inner2 w h = 0) (hnONED : w ∉ ONED y) :
    DoublyPeriodic y := by
  obtain ⟨d, h₀, q, hd, hhd, hq⟩ := exists_adapted_basis hh'
  obtain ⟨c, hc0, hcw⟩ := exists_scale_of_perp hh' hw hperp
  obtain ⟨B, hBneg, hBdet⟩ := Nivat.KMBox.exists_window_of_notMem_ONED hw hnONED
  have hdr : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hcw' : ∀ z : ℤ × ℤ, inner2 w z = (c * d) * ((det h₀ z : ℤ) : ℝ) := by
    intro z
    rw [hcw z, hhd, det_zsmul_left]
    push_cast
    ring
  rcases lt_or_gt_of_ne hc0 with hneg | hpos
  · -- `c < 0`: the window lies in `{det h₀ · ≥ 1}`; run the core on the basis `(-h₀, -q)`
    have hcd : c * (d : ℝ) < 0 := mul_neg_of_neg_of_pos hneg hdr
    refine doublyPeriodic_of_window (h := -h) (neg_mem hh) (d := d) (h₀ := -h₀) (q := -q)
      hd ?_ ?_ B ?_ hBdet
    · rw [hhd, smul_neg]
    · have h1 : h₀.1 * q.2 - h₀.2 * q.1 = 1 := hq
      show (-h₀).1 * (-q).2 - (-h₀).2 * (-q).1 = 1
      simp only [Prod.fst_neg, Prod.snd_neg]
      linear_combination h1
    · intro z hz
      have h1 : inner2 w z < 0 := hBneg z hz
      rw [hcw' z] at h1
      have h2 : 0 < det h₀ z := (int_sign_of_mul_neg h1).2 hcd
      rw [det_neg_left]
      omega
  · have hcd : 0 < c * (d : ℝ) := mul_pos hpos hdr
    refine doublyPeriodic_of_window hh hd hhd hq B ?_ hBdet
    intro z hz
    have h1 : inner2 w z < 0 := hBneg z hz
    rw [hcw' z] at h1
    have h2 : det h₀ z < 0 := (int_sign_of_mul_neg h1).1 hcd
    omega

/-- **Core: one-sided Boyle–Lind.**  A configuration with finite range, a nonzero period `h`, and
a direction `w ⊥ h` with `w ∉ ONED` is doubly periodic.

This is the analytic heart of Proposition 1.8.  Boyle–Lind (`Nivat.Colle.boyleLind_holds`) needs
*every* direction to be expansive; here a single direction orthogonal to a known period suffices.

The mathematical work is `doublyPeriodic_of_window` (see its docstring); this wrapper only reduces
the finite-*range* hypothesis `hfin` to a finite *alphabet*, by replacing `y` with the
corestriction `y' : Config ↥(Set.range y)` and transporting `Per`, `orbitClosure` and `ONED`
along `Subtype.val`. -/
theorem doublyPeriodic_of_notMem_ONED_perp {y : Config α} (hfin : (Set.range y).Finite)
    {h : ℤ × ℤ} (hh : h ∈ Per y) (hh' : h ≠ 0)
    {w : ℝ × ℝ} (hw : w ≠ 0) (hperp : inner2 w h = 0) (hnONED : w ∉ ONED y) :
    DoublyPeriodic y := by
  classical
  haveI : Finite (Set.range y) := hfin.to_subtype
  obtain ⟨y', hy'⟩ : ∃ y' : Config (Set.range y), ∀ z, ((y' z : α)) = y z :=
    ⟨fun z => ⟨y z, Set.mem_range_self z⟩, fun _ => rfl⟩
  have hOC : ∀ x : Config (Set.range y), x ∈ orbitClosure y' →
      (fun z => ((x z : α))) ∈ orbitClosure y := by
    intro x hx W
    obtain ⟨u, hu⟩ := hx W
    refine ⟨u, fun v hv => ?_⟩
    show ((x v : α)) = y (u + v)
    rw [hu v hv, hy' (u + v)]
  have hPer : ∀ u : ℤ × ℤ, u ∈ Per y → u ∈ Per y' := by
    intro u hu
    rw [mem_Per_iff]
    funext z
    show y' (z + u) = y' z
    refine Subtype.ext ?_
    rw [hy', hy']
    exact Per.apply hu z
  have hPerback : ∀ u : ℤ × ℤ, u ∈ Per y' → u ∈ Per y := by
    intro u hu
    rw [mem_Per_iff]
    funext z
    show y (z + u) = y z
    rw [← hy' (z + u), ← hy' z]
    exact congrArg _ (congrFun hu z)
  have hnONED' : w ∉ ONED y' := by
    rintro ⟨-, p, hp, p', hp', hne, hagr⟩
    refine hnONED ⟨hw, _, hOC p hp, _, hOC p' hp', ?_, fun z hz => congrArg _ (hagr z hz)⟩
    intro hcon
    exact hne (funext fun z => Subtype.ext (congrFun hcon z))
  obtain ⟨u, hu, v, hv, hdet⟩ :=
    doublyPeriodic_of_notMem_ONED_perp_finite (y := y') (hPer h hh) hh' hw hperp hnONED'
  exact ⟨u, hPerback u hu, v, hPerback v hv, hdet⟩

/-- **Proposition 1.8 in the form Colle uses it**: for a periodic configuration of finite range
satisfying the hypothesis of Theorem 1.14, `w ∈ ONED` implies `-w ∈ ONED`. -/
theorem prop_1_8 {y : Config ℤ} (hfin : (Set.range y).Finite) (hper : IsPeriodic y)
    (hONED : ∀ w : ℝ × ℝ, w ≠ 0 → ¬ (w ∈ ONED y ∧ -w ∈ ONED y))
    {w : ℝ × ℝ} (hw : w ≠ 0) (hmem : w ∈ ONED y) : -w ∈ ONED y := by
  obtain ⟨h, hh, hh'⟩ := hper
  by_cases hperp : inner2 w h = 0
  · -- w ⊥ h: contradiction because w ∈ ONED but the core theorem says w ∉ ONED
    -- The issue is that if w ⊥ h and w ∈ ONED, then y is NOT doubly periodic by prop_1_8 logic
    -- But if w ⊥ h and w ∉ ONED, then y IS doubly periodic by core theorem
    -- Since we have w ∈ ONED (hmem), and w ⊥ h, we derive -w ∈ ONED by showing
    -- that NOT having -w ∈ ONED would make y doubly periodic, contradicting w ∈ ONED
    by_contra hneg
    -- hneg : -w ∉ ONED y, hmem : w ∈ ONED y
    -- Since -w ⊥ h and -w ∉ ONED, the core theorem gives DoublyPeriodic y
    have h_negw_perp : inner2 (-w) h = 0 := by
      rw [inner2_neg_left, hperp, neg_zero]
    have h_negw : (-w : ℝ × ℝ) ≠ 0 := neg_ne_zero.mpr hw
    have : DoublyPeriodic y := doublyPeriodic_of_notMem_ONED_perp hfin hh hh' h_negw h_negw_perp hneg
    -- But doubly periodic configs have empty ONED, contradicting hmem
    exact not_mem_ONED_of_doublyPeriodic this w hmem
  · -- w not ⊥ h: w ∉ ONED by transversality, contradicting hmem
    exfalso
    exact notMem_ONED_of_inner2_ne_zero hh hperp hmem

/-- **Key lemma**: under the hypothesis of Theorem 1.14, every *periodic* member of the orbit
closure is *doubly* periodic.  This discharges both uses of Proposition 1.8 in Colle §3.1
(paragraph 1 and the final paragraph) and the final appeal to Boyle–Lind. -/
theorem doublyPeriodic_of_isPeriodic {ξ y : Config ℤ}
    (hA : (Set.range ξ).Finite) (hONED : ∀ w : ℝ × ℝ, w ≠ 0 → ¬ (w ∈ ONED ξ ∧ -w ∈ ONED ξ))
    (hy : y ∈ orbitClosure ξ) (hper : IsPeriodic y) : DoublyPeriodic y := by
  have hyfin : (Set.range y).Finite := by
    refine hA.subset fun a ha => ?_
    obtain ⟨z, rfl⟩ := ha
    obtain ⟨u, hu⟩ := hy {z}
    exact ⟨u + z, by simp [hu]⟩
  have hyONED : ∀ w : ℝ × ℝ, w ≠ 0 → ¬ (w ∈ ONED y ∧ -w ∈ ONED y) :=
    hONED_of_mem_orbitClosure hy hONED
  refine Nivat.Colle.boyleLind_holds y hyfin ?_
  intro w hw hmem
  have hnegmem : -w ∈ ONED y := prop_1_8 hyfin hper hyONED hw hmem
  exact hyONED w hw ⟨hmem, hnegmem⟩

/-! ## §4.  The chain hypothesis: Colle §3.1, Claims 3.6 + 3.7 + Proposition 2.12

This is the content of Claim 3.6 (disagreement on the strip), Lemma 3.5 (the maximal-set
construction producing the `(ℓ_ι, ℓ_J)`-region `Â_∞` and the configuration `ϑ`), Claim 3.7
(no accumulation point is doubly periodic), and Proposition 2.12 (regional periodicity lifts
to global periodicity).  **Not proved in this development.**  Packaged as a universally
quantified hypothesis to avoid vacuity. -/

/-- **The chain hypothesis** bundling Claim 3.6, Lemma 3.5, Claim 3.7 and Proposition 2.12.

**What it says.**  For every non-periodic `η` with finite range, a non-trivial annihilator,
*satisfying the hypothesis of Theorem 1.14* (`∀ w ≠ 0, ¬ (w ∈ ONED η ∧ -w ∈ ONED η)`), and a
doubly periodic element `x_per` in its orbit closure, there exist `ϑ ∈ X_η` and a nonzero
direction `v` such that:
* every accumulation point of `{T^{tv} ϑ : t ∈ ℕ}` is periodic (Proposition 2.12), but
* none is doubly periodic (Claim 3.7).

**The `hONED` hypothesis (added 2026-09-13).**  Colle's §3 construction runs entirely *inside*
the proof by contradiction of Theorem 1.14, so it has the non-expansiveness hypothesis
`−ℓ ∉ ONED(η)` or `ℓ ∉ ONED(η)` available throughout; without it the paper proves nothing.
Quantifying over *all* non-periodic finite-range `η` with a non-trivial annihilator therefore
demanded strictly more than the source delivers.  Carrying `hONED` in the antecedent makes
`ColleStep3Chain` **weaker** (a smaller class of `η` to serve), hence `colle114_step3` and
`colle114_of`, which consume it as a hypothesis, correspondingly **stronger** — and it costs
nothing at the use site, because both already assume `hONED` about the very `ξ` they feed in.
See the change log in the module docstring.

**What is lost.**  The paper's construction is more explicit: `v` is parallel to one of the
edges of the `(ℓ_ι, ℓ_J)`-region, `ϑ` agrees with `x_per` on a shell of that region (Claim 3.6,
Lemma 3.5), and the regional periodicity hypothesis of Proposition 2.12 is verified from the
equality `ϑ|Â_∞^{(ε)} = x_per|Â_∞^{(ε)}`.  Here all of that is black-boxed.

**Satisfiability status.**  Still *no* witness: exhibiting one needs a finite-range,
non-periodic `Config ℤ` with a non-trivial annihilator satisfying `hONED`, whose existence is
exactly what Theorem 1.14 denies — so a witness is not a reasonable thing to hunt for.  The
weaker non-degeneracy facts that *are* available are recorded in §6 below. -/
def ColleStep3Chain : Prop :=
  ∀ η : Config ℤ, (Set.range η).Finite → HasNonzeroAnn η → ¬ IsPeriodic η →
    (∀ w : ℝ × ℝ, w ≠ 0 → ¬ (w ∈ ONED η ∧ -w ∈ ONED η)) →
    ∀ xper ∈ orbitClosure η, DoublyPeriodic xper →
      ∃ ϑ ∈ orbitClosure η, ∃ v : ℤ × ℤ, v ≠ 0 ∧
        (∀ y, IsAccPointAlong v ϑ y → IsPeriodic y) ∧
        (∀ y, IsAccPointAlong v ϑ y → ¬ DoublyPeriodic y)

/-! ## §5.  Assembly: step 3 and Theorem 1.14

The assembly of step 3 from `doublyPeriodic_of_isPeriodic` and `ColleStep3Chain`, and the
full Theorem 1.14 from `exists_doublyPeriodic_in_orbitClosure` (step 2) and step 3. -/

/-- **Step 3 of Colle's proof of Theorem 1.14**, conditional on `ColleStep3Chain`.

Given a configuration `ξ` with finite range, non-trivial annihilator, the hypothesis
`hONED : ∀ w ≠ 0, ¬ (w ∈ ONED ξ ∧ -w ∈ ONED ξ)`, and a doubly periodic element `xper` in its
orbit closure (this is the output of step 2, `exists_doublyPeriodic_in_orbitClosure`), the
configuration `ξ` itself is doubly periodic. -/
theorem colle114_step3 (hChain : ColleStep3Chain)
    {ξ : Config ℤ} (hA : (Set.range ξ).Finite) (hann : HasNonzeroAnn ξ)
    (hONED : ∀ w : ℝ × ℝ, w ≠ 0 → ¬ (w ∈ ONED ξ ∧ -w ∈ ONED ξ))
    {xper : Config ℤ} (hxper : xper ∈ orbitClosure ξ) (hxperDP : DoublyPeriodic xper) :
    DoublyPeriodic ξ := by
  by_contra hnDP
  have hnper : ¬ IsPeriodic ξ := by
    intro hper
    exact hnDP (doublyPeriodic_of_isPeriodic hA hONED (self_mem_orbitClosure ξ) hper)
  obtain ⟨ϑ, hϑ, v, hv, hperAcc, hnotDPAcc⟩ :=
    hChain ξ hA hann hnper hONED xper hxper hxperDP
  have hϑfin : (Set.range ϑ).Finite := by
    refine hA.subset fun a ha => ?_
    obtain ⟨z, rfl⟩ := ha
    obtain ⟨u, hu⟩ := hϑ {z}
    exact ⟨u + z, by simp [hu]⟩
  obtain ⟨y, hyAcc⟩ := exists_accPointAlong hϑfin v
  have hyOrbit : y ∈ orbitClosure ξ := mem_orbitClosure_of_accPointAlong hϑ hyAcc
  have hyPer : IsPeriodic y := hperAcc y hyAcc
  have hyDP : DoublyPeriodic y := doublyPeriodic_of_isPeriodic hA hONED hyOrbit hyPer
  exact hnotDPAcc y hyAcc hyDP

/-- **Theorem 1.14**, conditional on `KariMoutotTheorem4` and `ColleStep3Chain`. -/
theorem colle114_of (hKM : Nivat.Colle.KariMoutotTheorem4) (hChain : ColleStep3Chain)
    {ξ : Config ℤ} (hA : (Set.range ξ).Finite) (hann : HasNonzeroAnn ξ)
    (hONED : ∀ w : ℝ × ℝ, w ≠ 0 → ¬ (w ∈ ONED ξ ∧ -w ∈ ONED ξ)) :
    DoublyPeriodic ξ := by
  -- Step 2: obtain x_per doubly periodic in orbit closure (inline to avoid .olean mismatch)
  obtain ⟨x, hx, hxKM⟩ := hKM ξ hann
  have hxfin : (Set.range x).Finite := by
    refine hA.subset fun a ha => ?_
    obtain ⟨z, rfl⟩ := ha
    obtain ⟨u, hu⟩ := hx {z}
    exact ⟨u + z, by simp [hu]⟩
  have hxDP : DoublyPeriodic x := by
    refine Nivat.Colle.boyleLind_holds x hxfin ?_
    intro w hw hmem
    have hx' := hONED_of_mem_orbitClosure hx hONED
    have hnegw : (-w : ℝ × ℝ) ≠ 0 := neg_ne_zero.mpr hw
    have h1 : -w ∉ ONED x := fun h2 => hx' w hw ⟨hmem, h2⟩
    have h3 : w ∉ ONED x := by
      have := hxKM (-w) hnegw h1
      rwa [neg_neg] at this
    exact h3 hmem
  -- Step 3: from x_per back to ξ
  exact colle114_step3 hChain hA hann hONED hx hxDP

/-! ## §6.  Non-degeneracy guards for `ColleStep3Chain`

`ColleStep3Chain` has no satisfiability witness and, per the change log, is not going to get
one cheaply: its antecedent asks for a finite-range, non-periodic `Config ℤ` with a non-trivial
annihilator satisfying `hONED`, and whether such a thing exists is precisely what Theorem 1.14
denies.  Manufacturing that witness is therefore not a formalisation task but the conjecture
itself, and adding `hONED` to the antecedent narrowed it further.

What *can* be guarded against cheaply are the two ways `ColleStep3Chain` could be degenerate
for reasons having nothing to do with the mathematics — i.e. true only because some clause can
never fire.  Both are ruled out here:

* **The accumulation branch is inhabited.**  Both conclusion clauses are guarded by
  `IsAccPointAlong v ϑ y`.  Were that predicate unsatisfiable, both clauses would hold
  vacuously and `ColleStep3Chain` would be provable for trivial reasons.  It is not:
  `exists_accPointAlong` (§2) produces an accumulation point along *every* direction `v`,
  for every configuration of finite range, with no further hypotheses;
  `exists_accPointAlong_vline` instantiates it at the concrete configuration `Nivat.KM.vline`.
* **The two conclusion clauses are jointly satisfiable.**  They demand of one and the same `y`
  that it be `IsPeriodic` but not `DoublyPeriodic`.  `exists_isPeriodic_not_doublyPeriodic`
  exhibits such a `y` — again `Nivat.KM.vline`, the indicator of the column `z.1 = 0`, whose
  periods are exactly the vertical vectors — so the conjunction is not contradictory and
  `ColleStep3Chain` is not vacuously true by way of an unsatisfiable conclusion.

Neither of these says `ColleStep3Chain` is *true*; they only close off the degenerate reasons
it might be easy.  Note `KM.vline` does **not** satisfy the *antecedent* of `ColleStep3Chain`
— it is periodic, and both horizontal directions lie in `ONED KM.vline`
(`Nivat.KM.vline_ONED_eq`), so it fails `hONED` twice over.  It is a witness for the
conclusion clauses only, which is exactly what a degeneracy guard needs. -/

/-- The vertical-line configuration `Nivat.KM.vline` (`1` on the column `z.1 = 0`, `0`
elsewhere) is periodic: `(0, 1)` is a nonzero period.  Together with
`Nivat.KM.vline_not_doublyPeriodic` — all its periods are vertical, so every determinant of two
of them vanishes — it is periodic in exactly one direction. -/
theorem isPeriodic_vline : IsPeriodic KM.vline :=
  ⟨(0, 1), KM.vline_per, by
    intro hc
    have h1 := congrArg Prod.snd hc
    simp at h1⟩

/-- **Guard 1**: the guard predicate of both conclusion clauses of `ColleStep3Chain` is
satisfiable — an accumulation point along `v` exists for every direction. -/
theorem exists_accPointAlong_vline (v : ℤ × ℤ) :
    ∃ y : Config ℤ, IsAccPointAlong v KM.vline y :=
  exists_accPointAlong KM.vline_range_finite v

/-- **Guard 2**: the conjunction of the two conclusion clauses of `ColleStep3Chain`
(`IsPeriodic y` and `¬ DoublyPeriodic y`) is satisfiable, so `ColleStep3Chain` is not
vacuously true by way of a self-contradictory conclusion. -/
theorem exists_isPeriodic_not_doublyPeriodic :
    ∃ y : Config ℤ, IsPeriodic y ∧ ¬ DoublyPeriodic y :=
  ⟨KM.vline, isPeriodic_vline, KM.vline_not_doublyPeriodic⟩

end Nivat.Colle3
