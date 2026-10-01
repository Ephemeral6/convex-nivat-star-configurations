/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.OrbitClosureBasics
import Nivat.External.Colle.Interfaces
import Nivat.External.Colle.BoyleLind

/-!
# Kari–Moutot §4, "Removing One-sided Determinism"

Work towards **Kari–Moutot Theorem 4**, the last remaining external input of step 2 of Colle's
proof of Theorem 1.14 (`Nivat.Colle.exists_doublyPeriodic_in_orbitClosure`).

## Source and verbatim statements

All quotations are from the **journal version**

> J. Kari, E. Moutot, *Decidability and Periodicity of Low Complexity Tilings*,
> Theory of Computing Systems **67** (2023) 125–148, doi `10.1007/s00224-021-10063-8`
> (open access; the PDF used is the one at
> `https://link.springer.com/content/pdf/10.1007/s00224-021-10063-8.pdf`, 681173 bytes).

**Theorem 4** (§3, p. 133), verbatim:

> "Let `c` be a two-dimensional configuration that has a non-trivial annihilator.  Then `O(c)‾`
> contains a configuration `c′` such that `O(c′)‾` has no direction of one-sided determinism."

**Proposition 13** (§4, p. 135), verbatim:

> "Let `c` be a configuration annihilated by `φ₁ ⋯ φ_m` where each `φ_i` is of the form (1).  Let
> `u ∈ ℤ²` be a direction that is not perpendicular to `v_i` for any `i ∈ {1, …, m}`.  Then
> `X = O(c)‾` is deterministic in direction `u`."

(here (1) is `φ_i = x^{n_i} y^{m_i} − 1` for `v_i = (n_i, m_i) ∈ ℤ²`.)

**Proposition 18** (§4, p. 138), verbatim:

> "Let `c` be a configuration with a non-trivial annihilator.  If `u` is a one-sided direction of
> determinism in `O(c)‾` then there is a configuration `d ∈ O(c)‾` such that `u` is a two-sided
> direction of determinism in `O(d)‾`."

The intermediate steps of the proof of Proposition 18, quoted for the record (they are *not*
formalised here, and they are **not** separate assumptions — they are the internal steps of the
one assumption `KMProp18`):

* **Lemma 14** (p. 136): *"For any `d, e ∈ X` such that `φd = φe` holds:
  `d|_B = e|_B ⟹ d|_H = e|_H`."*
* **Corollary 15** (p. 136): *"Let `c₁, …, c_n ∈ X` be pairwise distinct.  If
  `φc₁ = ⋯ = φc_n` then `n ≤ |A|^{|B|}`."*
* **Lemma 16** (p. 137): *"Let `d₁, …, d_n` be defined as above.  Then (a) `φd₁ = ⋯ = φd_n`, and
  (b) Configurations `d_i` are pairwise different on translated discrete boxes `B′ = B − t` for
  all `t ∈ ℤ²`."*
* **Lemma 17** (p. 137): *"Subshift `Y` is deterministic in direction `−u`."*

## Dictionary (Kari–Moutot ↔ this development)

Kari–Moutot §2.2 (p. 130), verbatim: *"For a nonzero vector `u ∈ ℤ² ∖ {0}` we denote
`H_u = {x ∈ ℤ² | ⟨x, u⟩ < 0}` for the discrete half plane in direction `u`.  A subshift `X` is
deterministic in direction `u` if for all `c, c′ ∈ X` … `c|_{H_u} = c′|_{H_u} ⟹ c = c′`."*

The Lean vocabulary is Colle's: `Nivat.ONED ξ` is the set of non-zero `w : ℝ × ℝ` for which two
distinct elements of `orbitClosure ξ` agree on the **closed** half-plane
`sideOf w = {z | ⟨z, w⟩ ≤ 0}`.  Two differences, both handled here:

1. *open vs. closed half-plane*.  `notMem_ONED_iff_det` below proves the two notions of
   determinism agree, by translating strictly inside the half-plane.  This is the same trick as
   `Nivat.BL.eq_of_agree_openSide`.
2. *integer vs. real directions*.  Kari–Moutot quantify over `u ∈ ℤ² ∖ {0}`, Colle over real
   lines.  For a configuration with a non-trivial annihilator the two agree, because
   Proposition 13 confines `ONED` to the finitely many rational directions perpendicular to the
   `v_i` — this is `exists_ray` below, and it is the reason the descent argument works.

So Kari–Moutot's *"`u` is a direction of determinism of `O(c)‾`"* is `toReal u ∉ ONED c`, and
*"`u` is a direction of one-sided determinism"* is `toReal u ∉ ONED c ∧ -(toReal u) ∈ ONED c`.

## What this file proves, and what it assumes

**Proved, unconditionally:**

* `Nivat.KM.notMem_ONED_iff_det` — the open/closed half-plane dictionary.
* `Nivat.KM.mem_ONED_smul_iff` — `ONED` is a union of open rays.
* `Nivat.KM.prop13` — **Kari–Moutot Proposition 13**, in Kari–Moutot's own formulation.
* `Nivat.KM.exists_ray` — every one-sided nonexpansive direction of a configuration carrying a
  product annihilator is a *positive multiple of an integer vector* drawn from an explicit
  finite list.  (Not in Kari–Moutot; it is what replaces their appeal to Birkhoff's minimal
  subshift theorem, see below.)
* `Nivat.KM.kariMoutotTheorem4_of_prop18` — **Theorem 4 from Proposition 18 alone**.
* `Nivat.KM.exists_doublyPeriodic_in_orbitClosure` — step 2 of Colle §3.1, now resting on
  `KMProp18` as its single external input.

**Assumed:** exactly one `Prop`, `Nivat.KM.KMProp18`, a transcription of Kari–Moutot
Proposition 18.  It is a definition, never an `axiom`, and appears only as an explicit
hypothesis.

## Deviation from Kari–Moutot's own proof of Theorem 4

Kari–Moutot deduce Theorem 4 from Proposition 18 like this (p. 139, verbatim):

> "Let `c` be a two-dimensional configuration that has a non-trivial annihilator.  Every
> non-empty subshift contains a minimal subshift [4], and hence there is a uniformly recurrent
> configuration `c′ ∈ O(c)‾`.  If `O(c′)‾` has a one-sided direction of determinism `u`, we can
> apply Proposition 18 on `c′` and find `d ∈ O(c′)‾` such that `u` is a two-sided direction of
> determinism in `O(d)‾`.  But because `c′` is uniformly recurrent, `O(d)‾ = O(c′)‾`, a
> contradiction."

That route needs Birkhoff's theorem (a Zorn's-lemma argument on the lattice of subshifts), which
is not in this development.  The proof below replaces it by a **finite descent**:
Proposition 13 plus Kari–Szabados bound `ONED` of every member of the orbit closure inside a
fixed finite set of `2n` rays, `ONED` shrinks along the orbit closure, so a member of the orbit
closure minimising the (finite) number of occupied rays exists; Proposition 18 would strictly
decrease that number, so the minimiser has no one-sided determinism.  This is strictly cheaper —
no Zorn, no uniform recurrence — and it yields the same conclusion.  The one thing it needs that
Kari–Moutot's route does not is the finiteness of the alphabet, which is used to invoke
Kari–Szabados; the hypothesis `(Set.range ξ).Finite` is available where Colle uses Theorem 4.

## Status

No `sorry`.  Kari–Moutot Proposition 18 is **not proved**; Lemmas 14, 16, 17 and Corollary 15 of
§4 are **not formalised at all**, not even as statements, because stating them faithfully
requires the discrete boxes `B_u^k` and the compactness argument of §2.2 that produces `k`, and
a statement that is never used is not an assumption but decoration.
-/

namespace Nivat.KM

open Nivat

/-! ### Rays: `ONED` is invariant under positive rescaling of the direction -/

/-- `⟨z, c • w⟩ = c ⟨z, w⟩`. -/
theorem inner2_smul_left (c : ℝ) (w : ℝ × ℝ) (z : ℤ × ℤ) :
    inner2 (c • w) z = c * inner2 w z := by
  simp only [inner2, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- A positive rescaling does not change the closed half-plane. -/
theorem sideOf_smul {c : ℝ} (hc : 0 < c) (w : ℝ × ℝ) : sideOf (c • w) = sideOf w := by
  ext z
  show inner2 (c • w) z ≤ 0 ↔ inner2 w z ≤ 0
  rw [inner2_smul_left]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-- **`ONED` is a union of open rays**: it is invariant under positive rescaling. -/
theorem mem_ONED_smul_iff {α : Type*} {ξ : Config α} {c : ℝ} (hc : 0 < c) (w : ℝ × ℝ) :
    c • w ∈ ONED ξ ↔ w ∈ ONED ξ := by
  have hne : c • w ≠ 0 ↔ w ≠ 0 := by
    constructor
    · rintro h rfl; exact h (smul_zero c)
    · intro h hc0
      exact h ((smul_eq_zero.mp hc0).resolve_left hc.ne')
  constructor
  · rintro ⟨h0, x, hx, y, hy, hxy, hagr⟩
    exact ⟨hne.mp h0, x, hx, y, hy, hxy, by rwa [sideOf_smul hc] at hagr⟩
  · rintro ⟨h0, x, hx, y, hy, hxy, hagr⟩
    exact ⟨hne.mpr h0, x, hx, y, hy, hxy, by rwa [sideOf_smul hc]⟩

/-! ### Kari–Moutot's open half-plane versus Colle's closed half-plane -/

/-- **The dictionary between the two notions of determinism.**

Kari–Moutot §2.2 define `X` to be *deterministic in direction `u`* by
`c|_{H_u} = c′|_{H_u} ⟹ c = c′` with the **open** half-plane `H_u = {x | ⟨x, u⟩ < 0}`; Colle's
`ONED` uses the **closed** half-plane `sideOf w = {z | ⟨z, w⟩ ≤ 0}`.  The two agree.

The non-trivial direction translates a witness strictly into the half-plane, exactly as in
`Nivat.BL.eq_of_agree_openSide`. -/
theorem notMem_ONED_iff_det {α : Type*} {ξ : Config α} {w : ℝ × ℝ} (hw : w ≠ 0) :
    w ∉ ONED ξ ↔
      ∀ x ∈ orbitClosure ξ, ∀ y ∈ orbitClosure ξ,
        (∀ z : ℤ × ℤ, inner2 w z < 0 → x z = y z) → x = y := by
  constructor
  · intro hnot x hx y hy hagr
    obtain ⟨t, ht⟩ := BL.exists_lattice_inner2_neg hw
    by_contra hne
    refine hnot ⟨hw, T t x, T_mem_of_mem_orbitClosure hx t, T t y,
      T_mem_of_mem_orbitClosure hy t, ?_, ?_⟩
    · intro hTeq
      refine hne ?_
      have h2 : T (-t) (T t x) = T (-t) (T t y) := by rw [hTeq]
      rwa [← T_add, ← T_add, neg_add_cancel, T_zero, T_zero] at h2
    · intro z hz
      have hz0 : inner2 w z ≤ 0 := hz
      show x (z + t) = y (z + t)
      refine hagr _ ?_
      rw [inner2_add]
      linarith
  · rintro hdet ⟨-, x, hx, y, hy, hne, hagr⟩
    exact hne (hdet x hx y hy fun z hz => hagr z (le_of_lt hz))

/-! ### Perpendicular integer directions -/

/-- The lattice vector `(-h₂, h₁)`, orthogonal to `h`.  Kari–Moutot write `ũ` for it
(§2.2: *"we denote by `ũ` a vector that is orthogonal to `u` and has the same length as `u`,
e.g., `(n, m)~ = (m, −n)`"*). -/
def perpOf (h : ℤ × ℤ) : ℤ × ℤ := (-h.2, h.1)

theorem perpOf_ne_zero {h : ℤ × ℤ} (hh : h ≠ 0) : perpOf h ≠ 0 := by
  intro hc
  refine hh (Prod.ext ?_ ?_)
  · have := congrArg Prod.snd hc
    simpa [perpOf] using this
  · have := congrArg Prod.fst hc
    simp only [perpOf] at this
    simpa using neg_eq_zero.mp (by simpa using this)

theorem toReal_neg (q : ℤ × ℤ) : toReal (-q) = -(toReal q) := by
  refine Prod.ext ?_ ?_ <;> simp [toReal]

theorem toReal_ne_zero {q : ℤ × ℤ} (hq : q ≠ 0) : toReal q ≠ 0 := by
  intro hc
  refine hq (Prod.ext ?_ ?_)
  · have := congrArg Prod.fst hc
    simpa [toReal] using this
  · have := congrArg Prod.snd hc
    simpa [toReal] using this

/-- A non-zero real direction orthogonal to a non-zero lattice vector `h` is a non-zero real
multiple of `perpOf h`: the orthogonal complement of `h` in `ℝ²` is the line spanned by
`perpOf h`. -/
theorem exists_smul_perpOf {h : ℤ × ℤ} (hh : h ≠ 0) {w : ℝ × ℝ} (hw0 : inner2 w h = 0) :
    ∃ t : ℝ, w = t • toReal (perpOf h) := by
  set a : ℝ := (h.1 : ℝ) with ha
  set b : ℝ := (h.2 : ℝ) with hb
  have hab : a * w.1 + b * w.2 = 0 := hw0
  have hpos : a ^ 2 + b ^ 2 ≠ 0 := by
    have hor : h.1 ≠ 0 ∨ h.2 ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hh (Prod.ext hc.1 hc.2)
    rcases hor with h1 | h1
    · have : a ≠ 0 := by rw [ha]; exact_mod_cast h1
      positivity
    · have : b ≠ 0 := by rw [hb]; exact_mod_cast h1
      positivity
  refine ⟨(a * w.2 - b * w.1) / (a ^ 2 + b ^ 2), Prod.ext ?_ ?_⟩
  · show w.1 = ((a * w.2 - b * w.1) / (a ^ 2 + b ^ 2)) * ((((-h.2 : ℤ)) : ℝ))
    have hcast : (((-h.2 : ℤ)) : ℝ) = -b := by rw [hb]; push_cast; ring
    rw [hcast]
    field_simp
    linear_combination a * hab
  · show w.2 = ((a * w.2 - b * w.1) / (a ^ 2 + b ^ 2)) * (((h.1 : ℤ)) : ℝ)
    have hcast : (((h.1 : ℤ)) : ℝ) = a := by rw [ha]
    rw [hcast]
    field_simp
    linear_combination b * hab

/-! ### Kari–Moutot Proposition 13 -/

/-- **Kari–Moutot Proposition 13** (journal version, §4, p. 135), verbatim:

> "Let `c` be a configuration annihilated by `φ₁ ⋯ φ_m` where each `φ_i` is of the form (1).
> Let `u ∈ ℤ²` be a direction that is not perpendicular to `v_i` for any `i ∈ {1, …, m}`.  Then
> `X = O(c)‾` is deterministic in direction `u`."

Here (1) is `φ_i = x^{n_i} y^{m_i} − 1`, i.e. `mono (v i) - 1`, so `φ₁ ⋯ φ_m` is
`Nivat.prodShift v`; determinism in direction `u` is spelled out with Kari–Moutot's own **open**
half-plane `H_u = {x | ⟨x, u⟩ < 0}`, via `notMem_ONED_iff_det`.

**Proved**, not assumed: the underlying half-plane argument is
`Nivat.Colle.exists_tangent_of_mem_ONED` (already in this development), whose proof is the same
one Kari–Moutot give — peel off factors of the annihilator until the difference `d − e` becomes
`v_i`-periodic, then transport the zeros out of the half-plane.

**Deviation**: this Lean version additionally assumes the `v i` are *pairwise* non-parallel.
Kari–Moutot do not need that for Proposition 13 (they only record it as available, p. 135:
*"Moreover, vectors `v_i` can be chosen pairwise linearly independent"*); the hypothesis is
present only because the imported lemma takes it, and it is supplied for free by
`Nivat.kari_szabados_prodShift`.  This is a *strengthening of the hypotheses* of Prop. 13, i.e.
the Lean statement is weaker than the source; it is harmless because the only call site has it.
Kari–Moutot state it for `u ∈ ℤ²`; here `u : ℝ × ℝ`, which is more general. -/
theorem prop13 {ξ : Config ℤ} {n : ℕ} {v : Fin n → ℤ × ℤ}
    (hnp : Pairwise fun i j => det (v i) (v j) ≠ 0)
    (hann : act (prodShift v) ξ = 0) {u : ℝ × ℝ} (hu : u ≠ 0)
    (hperp : ∀ i, inner2 u (v i) ≠ 0) :
    ∀ x ∈ orbitClosure ξ, ∀ y ∈ orbitClosure ξ,
      (∀ z : ℤ × ℤ, inner2 u z < 0 → x z = y z) → x = y := by
  refine (notMem_ONED_iff_det hu).mp ?_
  intro hmem
  obtain ⟨i, hi⟩ := Nivat.Colle.exists_tangent_of_mem_ONED hnp hann hmem
  exact hperp i hi

/-! ### The finite list of candidate rays -/

/-- The `2n` candidate directions: `±perpOf (v i)`.  By `prop13`, every one-sided nonexpansive
direction of a configuration annihilated by `prodShift v` is a positive multiple of one of
them. -/
def rayOf {n : ℕ} (v : Fin n → ℤ × ℤ) (p : Fin n × Bool) : ℤ × ℤ :=
  cond p.2 (perpOf (v p.1)) (-(perpOf (v p.1)))

@[simp] theorem rayOf_true {n : ℕ} (v : Fin n → ℤ × ℤ) (i : Fin n) :
    rayOf v (i, true) = perpOf (v i) := rfl

@[simp] theorem rayOf_false {n : ℕ} (v : Fin n → ℤ × ℤ) (i : Fin n) :
    rayOf v (i, false) = -(perpOf (v i)) := rfl

/-- Flipping the orientation of a ray. -/
def flipRay {n : ℕ} (p : Fin n × Bool) : Fin n × Bool := (p.1, !p.2)

theorem rayOf_flip {n : ℕ} (v : Fin n → ℤ × ℤ) (p : Fin n × Bool) :
    rayOf v (flipRay p) = -(rayOf v p) := by
  cases p with
  | mk i s => cases s <;> simp [flipRay]

theorem rayOf_ne_zero {n : ℕ} {v : Fin n → ℤ × ℤ} (hv : ∀ i, v i ≠ 0) (p : Fin n × Bool) :
    rayOf v p ≠ 0 := by
  cases p with
  | mk i s =>
    cases s
    · simpa using perpOf_ne_zero (hv i)
    · simpa using perpOf_ne_zero (hv i)

/-- **Every one-sided nonexpansive direction is a positive multiple of one of the `2n` rays.**

This is the quantitative form of Proposition 13 that drives the descent.  In particular `ONED`
of such a configuration contains no irrational direction, which is why Colle's real-line
formulation and Kari–Moutot's integer-vector formulation of Theorem 4 coincide here. -/
theorem exists_ray {x : Config ℤ} {n : ℕ} {v : Fin n → ℤ × ℤ} (hvne : ∀ i, v i ≠ 0)
    (hnp : Pairwise fun i j => det (v i) (v j) ≠ 0) (hann : act (prodShift v) x = 0)
    {w : ℝ × ℝ} (hw : w ∈ ONED x) :
    ∃ p : Fin n × Bool, ∃ t : ℝ, 0 < t ∧ w = t • toReal (rayOf v p) := by
  obtain ⟨i, hi⟩ := Nivat.Colle.exists_tangent_of_mem_ONED hnp hann hw
  obtain ⟨t, ht⟩ := exists_smul_perpOf (hvne i) hi
  have hw0 : w ≠ 0 := hw.1
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact hw0 (by rw [ht, zero_smul])
  rcases ht0.lt_or_gt with hneg | hpos
  · refine ⟨(i, false), -t, by linarith, ?_⟩
    rw [rayOf_false, toReal_neg, smul_neg, neg_smul, neg_neg, ht]
  · exact ⟨(i, true), t, hpos, by rw [rayOf_true, ht]⟩

/-! ### Kari–Moutot Proposition 18, as the single external input -/

/-- **Kari–Moutot Proposition 18** (journal version, §4, p. 138), verbatim:

> "Let `c` be a configuration with a non-trivial annihilator.  If `u` is a one-sided direction
> of determinism in `O(c)‾` then there is a configuration `d ∈ O(c)‾` such that `u` is a
> two-sided direction of determinism in `O(d)‾`."

Dictionary: *"`u` is a direction of determinism in `O(c)‾`"* is `toReal u ∉ ONED c`
(`notMem_ONED_iff_det`), *"one-sided"* adds that `−u` is **not** a direction of determinism, and
the conclusion *"two-sided direction of determinism in `O(d)‾`"* is
`toReal u ∉ ONED d ∧ -(toReal u) ∉ ONED d`.

**Deviation from the source, stated loudly.**  The Lean statement carries the extra hypothesis
`(Set.range c).Finite`.  Kari–Moutot write §4 for *"a configuration `c` over alphabet `A ⊆ ℤ`"*
and their Corollary 15 concludes `n ≤ |A|^{|B|}`, which is vacuous unless `A` is finite; the
compactness extractions of Lemma 16 and Lemma 17 need it too.  So this is not a strengthening
of the mathematical content, it is a hypothesis the source leaves implicit in `|A|`.  It is
available at the only call site (`Nivat.Colle.exists_doublyPeriodic_in_orbitClosure` has it).

**This `Prop` is not proved here.**  It is an ordinary definition used as an explicit
hypothesis, never an `axiom`.  Its distance from the raw statement of Theorem 4 is exactly the
descent argument of `kariMoutotTheorem4_of_prop18`: Proposition 18 removes **one** direction of
one-sided determinism from **one** configuration, and says nothing about the other directions or
about what happens to `ONED` elsewhere; Theorem 4 needs a single configuration with **no**
direction of one-sided determinism at all. -/
def KMProp18 : Prop :=
  ∀ c : Config ℤ, (Set.range c).Finite → HasNonzeroAnn c →
    ∀ u : ℤ × ℤ, u ≠ 0 → toReal u ∉ ONED c → -(toReal u) ∈ ONED c →
      ∃ d ∈ orbitClosure c, toReal u ∉ ONED d ∧ -(toReal u) ∉ ONED d

/-- **What the descent actually consumes** — strictly less than Proposition 18.

Where Proposition 18 asks for a `d` in which the *given* direction `u` has become a **two-sided**
direction of determinism, the descent below only needs a `d` that loses **some** one-sided
nonexpansive direction, no matter which.  `ONED` never grows along the orbit closure
(`Nivat.Colle.ONED_subset_of_mem_orbitClosure`), so any such `d` strictly decreases the rank.

This is the minimal named assumption of this file: `kmWeakDescent_of_prop18` derives it from
`KMProp18`, and it is the only thing `kariMoutotTheorem4_of_weakDescent` uses.  Stating it
separately is what keeps the assumption honest: it makes visible that the descent does **not**
need the "same direction `u`" part of Proposition 18, which is where Lemmas 16 and 17 of §4 do
their work. -/
def KMWeakDescent : Prop :=
  ∀ c : Config ℤ, (Set.range c).Finite → HasNonzeroAnn c →
    ∀ u : ℤ × ℤ, u ≠ 0 → toReal u ∉ ONED c → -(toReal u) ∈ ONED c →
      ∃ d ∈ orbitClosure c, ∃ w ∈ ONED c, w ∉ ONED d

/-- Proposition 18 implies the weak descent property: the direction it hands back is `-u`, which
was in `ONED c` and is not in `ONED d`. -/
theorem kmWeakDescent_of_prop18 (hP18 : KMProp18) : KMWeakDescent := by
  intro c hA hann u hu hnot hmem
  obtain ⟨d, hd, -, hd2⟩ := hP18 c hA hann u hu hnot hmem
  exact ⟨d, hd, -(toReal u), hmem, hd2⟩

/-! ### Theorem 4 -/

/-- Non-trivial annihilators are inherited by the orbit closure. -/
theorem hasNonzeroAnn_of_mem_orbitClosure {ξ : Config ℤ} (hann : HasNonzeroAnn ξ)
    {x : Config ℤ} (hx : x ∈ orbitClosure ξ) : HasNonzeroAnn x := by
  obtain ⟨f, hf0, hf⟩ := hann
  exact ⟨f, hf0, act_eq_zero_of_mem_orbitClosure hf hx⟩

/-- **Kari–Moutot Theorem 4, reduced to Proposition 18.**

> "Let `c` be a two-dimensional configuration that has a non-trivial annihilator.  Then `O(c)‾`
> contains a configuration `c′` such that `O(c′)‾` has no direction of one-sided determinism."

The conclusion is stated in Colle's `ONED` vocabulary, in exactly the shape of
`Nivat.Colle.KariMoutotTheorem4`, plus the hypothesis `(Set.range ξ).Finite`.

The proof is **not** Kari–Moutot's (which invokes Birkhoff's minimal subshift theorem); it is
the finite descent described in the module docstring.  The three ingredients are

* `Nivat.kari_szabados_prodShift` (proved elsewhere in this development) — a product annihilator
  with pairwise non-parallel non-zero exponents;
* `exists_ray` above — `ONED` of every member of the orbit closure sits inside the finite set of
  `2n` rays `±perpOf (v i)`;
* `Nivat.Colle.ONED_subset_of_mem_orbitClosure` — `ONED` only shrinks along the orbit closure.

so the natural number `#{p | rayOf v p ∈ ONED x}` is a well-founded rank on `orbitClosure ξ`
which Proposition 18 strictly decreases. -/
theorem kariMoutotTheorem4_of_prop18 (hP18 : KMProp18) {ξ : Config ℤ}
    (hA : (Set.range ξ).Finite) (hann : HasNonzeroAnn ξ) :
    ∃ x ∈ orbitClosure ξ, ∀ w : ℝ × ℝ, w ≠ 0 → w ∉ ONED x → -w ∉ ONED x := by
  classical
  obtain ⟨n, v, -, hvne, hvnp, hvann⟩ := kari_szabados_prodShift hA hann
  set S : Config ℤ → Finset (Fin n × Bool) :=
    fun x => Finset.univ.filter (fun p => toReal (rayOf v p) ∈ ONED x) with hS
  have hSmem : ∀ (x : Config ℤ) (p : Fin n × Bool),
      p ∈ S x ↔ toReal (rayOf v p) ∈ ONED x := by
    intro x p
    simp [hS]
  have hmono : ∀ {x y : Config ℤ}, y ∈ orbitClosure x → S y ⊆ S x := by
    intro x y hy p hp
    exact (hSmem x p).mpr
      (Nivat.Colle.ONED_subset_of_mem_orbitClosure hy ((hSmem y p).mp hp))
  -- Pick a member of the orbit closure minimising the number of occupied rays.
  have hne : {k : ℕ | ∃ x ∈ orbitClosure ξ, (S x).card = k}.Nonempty :=
    ⟨(S ξ).card, ξ, self_mem_orbitClosure ξ, rfl⟩
  obtain ⟨x, hx, hxcard⟩ := Nat.sInf_mem hne
  refine ⟨x, hx, ?_⟩
  intro w hw hwnot hnw
  -- `x` inherits the alphabet and the annihilator.
  have hxA : (Set.range x).Finite := BL.finite_range_of_mem_orbitClosure hA hx
  have hxann : act (prodShift v) x = 0 := act_eq_zero_of_mem_orbitClosure hvann hx
  have hxann' : HasNonzeroAnn x := hasNonzeroAnn_of_mem_orbitClosure hann hx
  -- `-w` lies on one of the `2n` rays.
  obtain ⟨p, t, ht, hpt⟩ := exists_ray hvne hvnp hxann hnw
  have hpS : p ∈ S x := by
    refine (hSmem x p).mpr ?_
    rw [← mem_ONED_smul_iff ht (toReal (rayOf v p)), ← hpt]
    exact hnw
  -- The opposite ray is the direction Proposition 18 applies to.
  set q : Fin n × Bool := flipRay p with hq
  have hqray : toReal (rayOf v q) = -(toReal (rayOf v p)) := by
    rw [hq, rayOf_flip, toReal_neg]
  have hq0 : rayOf v q ≠ 0 := rayOf_ne_zero hvne q
  have hw_eq : w = t • toReal (rayOf v q) := by
    calc w = -(-w) := by simp
         _ = -(t • toReal (rayOf v p)) := by rw [← hpt]
         _ = t • (-(toReal (rayOf v p))) := by rw [smul_neg]
         _ = t • toReal (rayOf v q) := by rw [← hqray]
  have h1 : toReal (rayOf v q) ∉ ONED x := by
    intro hc
    exact hwnot (by rw [hw_eq]; exact (mem_ONED_smul_iff ht _).mpr hc)
  have h2 : -(toReal (rayOf v q)) ∈ ONED x := by
    rw [hqray, neg_neg]
    exact (hSmem x p).mp hpS
  obtain ⟨d, hd, -, hd2⟩ := hP18 x hxA hxann' (rayOf v q) hq0 h1 h2
  -- `d` occupies strictly fewer rays, contradicting minimality.
  have hpnd : p ∉ S d := by
    intro hc
    refine hd2 ?_
    rw [hqray, neg_neg]
    exact (hSmem d p).mp hc
  have hsub : S d ⊆ S x := hmono hd
  have hlt : (S d).card < (S x).card :=
    Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsub).mpr ⟨p, hpS, hpnd⟩)
  have hdξ : d ∈ orbitClosure ξ := Nivat.Colle.mem_orbitClosure_trans hx hd
  have hge : sInf {k : ℕ | ∃ y ∈ orbitClosure ξ, (S y).card = k} ≤ (S d).card :=
    Nat.sInf_le ⟨d, hdξ, rfl⟩
  omega

/-- **Step 2 of Colle's proof of Theorem 1.14, now resting on Kari–Moutot Proposition 18 alone.**

Same statement as `Nivat.Colle.exists_doublyPeriodic_in_orbitClosure`, but with the hypothesis
`Nivat.Colle.KariMoutotTheorem4` replaced by the strictly weaker (and strictly more elementary)
`KMProp18`.  The Boyle–Lind input is the proved `Nivat.BL.boyleLindStatement_of_finite`. -/
theorem exists_doublyPeriodic_in_orbitClosure (hP18 : KMProp18) {ξ : Config ℤ}
    (hA : (Set.range ξ).Finite) (hann : HasNonzeroAnn ξ)
    (hONED : ∀ w : ℝ × ℝ, w ≠ 0 → ¬ (w ∈ ONED ξ ∧ -w ∈ ONED ξ)) :
    ∃ x ∈ orbitClosure ξ, DoublyPeriodic x := by
  obtain ⟨x, hx, hxKM⟩ := kariMoutotTheorem4_of_prop18 hP18 hA hann
  refine ⟨x, hx, BL.boyleLindStatement_of_finite x
    (BL.finite_range_of_mem_orbitClosure hA hx) ?_⟩
  intro w hw hmem
  have hx' := Nivat.Colle.hONED_of_mem_orbitClosure hx hONED
  have hnegw : (-w : ℝ × ℝ) ≠ 0 := neg_ne_zero.mpr hw
  have h1 : -w ∉ ONED x := fun h2 => hx' w hw ⟨hmem, h2⟩
  have h3 : w ∉ ONED x := by
    have := hxKM (-w) hnegw h1
    rwa [neg_neg] at this
  exact h3 hmem

/-! ### Non-vacuity witnesses -/

/-- The vertical-line configuration: 1 on the `z.1 = 0` column, 0 elsewhere. -/
def vline : Config ℤ := fun z => if z.1 = 0 then 1 else 0

@[simp] theorem vline_apply (z : ℤ × ℤ) : vline z = if z.1 = 0 then 1 else 0 := rfl

theorem vline_range_finite : (Set.range vline).Finite := by
  refine Set.Finite.subset ((Set.finite_singleton (1 : ℤ)).insert 0) ?_
  rintro _ ⟨z, rfl⟩
  by_cases h : z.1 = 0
  · simp [h]
  · simp [h]

theorem vline_per : (0, 1) ∈ Per vline := by
  rw [mem_Per_iff]
  funext z
  simp [T]

theorem vline_hasNonzeroAnn : HasNonzeroAnn vline := by
  refine ⟨mono (0, 1) - 1, mono_sub_one_ne_zero (by decide), ?_⟩
  rw [act_mono_sub_one_eq_zero_iff]
  exact vline_per

theorem const0_mem_orbitClosure_vline : BL.const0 ∈ orbitClosure vline := by
  intro W
  obtain ⟨N, hN⟩ : ∃ N : ℤ, ∀ w ∈ W, w.1 < N := by
    refine ⟨(W.sum fun w => |w.1|) + 1, fun w hw => ?_⟩
    have h1 : |w.1| ≤ W.sum fun w : ℤ × ℤ => |w.1| :=
      Finset.single_le_sum (f := fun w : ℤ × ℤ => |w.1|) (fun i _ => abs_nonneg _) hw
    have h2 : w.1 ≤ |w.1| := le_abs_self _
    omega
  refine ⟨(-N, 0), fun w hw => ?_⟩
  show BL.const0 w = vline ((-N, 0) + w)
  have hlt := hN w hw
  have h3 : ¬ ((-N, 0) + w).1 = 0 := by
    show ¬ -N + w.1 = 0
    omega
  simp only [BL.const0, vline_apply, if_neg h3]

/-- On `sideOf (toReal (1,0))` the first coordinate is `≤ 0`. -/
theorem fst_nonpos_of_mem_sideOf_e1 {z : ℤ × ℤ} (hz : z ∈ sideOf (toReal (1, 0))) : z.1 ≤ 0 := by
  have h : inner2 (toReal (1, 0)) z ≤ 0 := hz
  simp only [inner2, toReal] at h
  norm_num at h
  exact_mod_cast h

/-- On `sideOf (toReal (-1,0))` the first coordinate is `≥ 0`. -/
theorem fst_nonneg_of_mem_sideOf_ne1 {z : ℤ × ℤ}
    (hz : z ∈ sideOf (toReal (-1, 0))) : 0 ≤ z.1 := by
  have h : inner2 (toReal (-1, 0)) z ≤ 0 := hz
  simp only [inner2, toReal] at h
  norm_num at h
  exact_mod_cast h

theorem vline_ONED_horizontal_pos : toReal (1, 0) ∈ ONED vline := by
  refine ⟨by simp [toReal, Prod.ext_iff], T (-5, 0) vline,
    T_mem_of_mem_orbitClosure (self_mem_orbitClosure vline) _,
    BL.const0, const0_mem_orbitClosure_vline, ?_, ?_⟩
  · intro heq
    have h0 : T (-5, 0) vline (5, 0) = BL.const0 (5, 0) := congrFun heq (5, 0)
    simp [T, BL.const0] at h0
  · intro z hz
    have hz1 := fst_nonpos_of_mem_sideOf_e1 hz
    show vline (z + (-5, 0)) = BL.const0 z
    have h3 : ¬ (z + (-5, 0)).1 = 0 := by show ¬ z.1 + -5 = 0; omega
    simp only [BL.const0, vline_apply, if_neg h3]

theorem vline_ONED_horizontal_neg : toReal (-1, 0) ∈ ONED vline := by
  refine ⟨by simp [toReal, Prod.ext_iff], T (5, 0) vline,
    T_mem_of_mem_orbitClosure (self_mem_orbitClosure vline) _,
    BL.const0, const0_mem_orbitClosure_vline, ?_, ?_⟩
  · intro heq
    have h0 : T (5, 0) vline (-5, 0) = BL.const0 (-5, 0) := congrFun heq (-5, 0)
    simp [T, BL.const0] at h0
  · intro z hz
    have hz1 := fst_nonneg_of_mem_sideOf_ne1 hz
    show vline (z + (5, 0)) = BL.const0 z
    have h3 : ¬ (z + (5, 0)).1 = 0 := by show ¬ z.1 + 5 = 0; omega
    simp only [BL.const0, vline_apply, if_neg h3]

theorem vline_not_ONED_vertical_pos : toReal (0, 1) ∉ ONED vline := by
  rintro ⟨-, x, hx, y, hy, hne, hagr⟩
  refine hne (Nivat.Colle.eq_of_agree_sideOf_of_mem_Per
    (p := (0, -1)) ?_ ?_ ?_ hagr)
  · exact Nivat.Colle.mem_Per_of_mem_orbitClosure (neg_mem vline_per) hx
  · exact Nivat.Colle.mem_Per_of_mem_orbitClosure (neg_mem vline_per) hy
  · show inner2 (toReal (0, 1)) ((0 : ℤ), (-1 : ℤ)) < 0
    simp only [inner2, toReal]
    norm_num

theorem vline_not_ONED_vertical_neg : toReal (0, -1) ∉ ONED vline := by
  rintro ⟨-, x, hx, y, hy, hne, hagr⟩
  refine hne (Nivat.Colle.eq_of_agree_sideOf_of_mem_Per
    (p := (0, 1)) ?_ ?_ ?_ hagr)
  · exact Nivat.Colle.mem_Per_of_mem_orbitClosure vline_per hx
  · exact Nivat.Colle.mem_Per_of_mem_orbitClosure vline_per hy
  · show inner2 (toReal (0, -1)) ((0 : ℤ), (1 : ℤ)) < 0
    simp only [inner2, toReal]
    norm_num

/-- The single-vector product annihilator of `vline`. -/
theorem vline_prodShift_ann : act (prodShift (fun _ : Fin 1 => ((0 : ℤ), (1 : ℤ)))) vline = 0 := by
  rw [prodShift, Fin.prod_univ_one]
  exact (act_mono_sub_one_eq_zero_iff _ _).mpr vline_per

/-- **`ONED vline` computed exactly**: the horizontal directions, and nothing else. -/
theorem vline_ONED_eq : ONED vline = {w : ℝ × ℝ | w.2 = 0 ∧ w ≠ 0} := by
  ext w
  constructor
  · intro hw
    have hpw : Pairwise fun i j : Fin 1 =>
        det ((fun _ : Fin 1 => ((0 : ℤ), (1 : ℤ))) i)
          ((fun _ : Fin 1 => ((0 : ℤ), (1 : ℤ))) j) ≠ 0 :=
      fun i j hij => absurd (Subsingleton.elim i j) hij
    obtain ⟨i, hi⟩ := Nivat.Colle.exists_tangent_of_mem_ONED hpw vline_prodShift_ann hw
    refine ⟨?_, hw.1⟩
    simp only [inner2] at hi
    push_cast at hi
    linarith
  · rintro ⟨hw2, hw0⟩
    have hw1 : w.1 ≠ 0 := fun h => hw0 (Prod.ext h hw2)
    rcases hw1.lt_or_gt with hn | hp
    · have hEq : w = (-w.1) • toReal (-1, 0) := by
        refine Prod.ext ?_ ?_ <;> simp [toReal, hw2]
      rw [hEq, mem_ONED_smul_iff (by linarith)]
      exact vline_ONED_horizontal_neg
    · have hEq : w = w.1 • toReal (1, 0) := by
        refine Prod.ext ?_ ?_ <;> simp [toReal, hw2]
      rw [hEq, mem_ONED_smul_iff hp]
      exact vline_ONED_horizontal_pos

/-- `vline` satisfies the Theorem 4 conclusion, **non-vacuously**: its `ONED` is neither empty
nor everything. -/
theorem vline_satisfies_KMTheorem4 :
    ∀ w : ℝ × ℝ, w ≠ 0 → w ∉ ONED vline → -w ∉ ONED vline := by
  intro w hw hwnot hnw
  rw [vline_ONED_eq] at hwnot hnw
  refine hwnot ⟨?_, hw⟩
  have h : (-w).2 = 0 := hnw.1
  have h2 : -(w.2) = 0 := h
  linarith

theorem vline_ONED_nonempty : (ONED vline).Nonempty :=
  ⟨toReal (1, 0), vline_ONED_horizontal_pos⟩

theorem vline_ONED_ne_univ : ONED vline ≠ Set.univ := fun h =>
  vline_not_ONED_vertical_pos (h ▸ Set.mem_univ _)

/-- Every period of `vline` is vertical. -/
theorem fst_eq_zero_of_mem_Per_vline {u : ℤ × ℤ} (hu : u ∈ Per vline) : u.1 = 0 := by
  by_contra h0
  have h1 : vline ((0, 0) + u) = vline (0, 0) := congrFun (mem_Per_iff.mp hu) (0, 0)
  have h2 : ((0 : ℤ), (0 : ℤ)) + u = u := zero_add u
  rw [h2] at h1
  simp [h0] at h1

/-- `vline` is **not** doubly periodic, so the conclusion of Theorem 4 is genuinely weaker than
`ONED = ∅`: `vline` already satisfies the conclusion while having non-empty `ONED`. -/
theorem vline_not_doublyPeriodic : ¬ DoublyPeriodic vline := by
  rintro ⟨u, hu, v, hv, hdet⟩
  refine hdet ?_
  show u.1 * v.2 - u.2 * v.1 = 0
  rw [fst_eq_zero_of_mem_Per_vline hu, fst_eq_zero_of_mem_Per_vline hv]
  ring

end Nivat.KM
