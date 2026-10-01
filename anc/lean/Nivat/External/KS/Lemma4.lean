/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.Laurent.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.GroupWithZero.Units.Lemmas

/-!
# Kari–Szabados, Lemma 4

Formalisation of Lemma 4 of J. Kari and M. Szabados, *An algebraic geometric approach to
Nivat's conjecture* (arXiv:1605.05929v1), specialised to `d = 2`.

## The source, verbatim

The notation is fixed just before the source's Lemma 3:

> Let us introduce additional notation: if `Z = (z₁, …, z_d) ∈ ℂ^d` is a complex vector, then
> it can be plugged into a polynomial.  In particular, plugging into a monomial `X^v` results
> in `Z^v = z₁^{v₁} ⋯ z_d^{v_d}`.  Recall that the notation `f(X^n)` for positive integers `n`
> was defined in section 2.

and, in section 2:

> For a polynomial `f(X) = ∑ a_v X^v` and a positive integer `n` define `f(X^n) = ∑ a_v X^{nv}`.

> **Lemma 3.**  Let `c(X)` be a finitary integral configuration and `f(X) ∈ Ann(c)` a non-zero
> integer polynomial.  Then there exists an integer `r` such that for every positive integer
> `n` relatively prime to `r` we have `f(X^n) ∈ Ann(c)`.

> Let us define the support of a Laurent polynomial `f = ∑ a_v X^v` as
> `supp(f) = { v ∈ ℤ^d | a_v ≠ 0 }`.

> **Lemma 4.**  Let `c` be a finitary integral configuration and `f = ∑ a_v X^v` a non-trivial
> integer polynomial annihilator.  Define
>
>     g(X) = x₁ ⋯ x_d ∏_{v ∈ supp(f), v ≠ v₀} (X^{rv} − X^{rv₀})
>
> where `r` is the integer from 3 and `v₀ ∈ supp(f)` arbitrary.  Then `g(Z) = 0` for any common
> root `Z ∈ ℂ^d` of `Ann(c)`.
>
> *Proof.*  Fix `Z`.  If any of its complex coordinates is zero then clearly `g(Z) = 0`.
> Assume therefore that all coordinates of `Z` are non-zero.
>
> Let us define for `α ∈ ℂ`
>
>     S_α    = { v ∈ supp(f) | Z^{rv} = α },
>     f_α(X) = ∑_{v ∈ S_α} a_v X^v.
>
> Because `supp(f)` is finite, there are only finitely many non-empty sets `S_{α₁}, …, S_{α_m}`
> and they form a partitioning of `supp(f)`.  In particular we have `f = f_{α₁} + … + f_{α_m}`.
>
> Numbers of the form `1 + ir` are relatively prime to `r` for all non-negative integers `i`,
> therefore by 3, `f(X^{1+ir}) ∈ Ann(c)`.  Plugging in `Z` we obtain `f(Z^{1+ir}) = 0`.  Now
> compute:
>
>     f_α(Z^{1+ir}) = ∑_{v ∈ S_α} a_v Z^{(1+ir)v} = ∑_{v ∈ S_α} a_v Z^v α^i = f_α(Z) α^i
>
> Summing over `α = α₁, …, α_m` gives
>
>     0 = f(Z^{1+ir}) = f_{α₁}(Z) α₁^i + … + f_{α_m}(Z) α_m^i
>
> Let us rewrite the last equation as a statement about orthogonality of two vectors in `ℂ^m`:
>
>     (conj f_{α₁}(Z), …, conj f_{α_m}(Z)) ⟂ (α₁^i, …, α_m^i)
>
> By Vandermode determinant, for `i ∈ {0, …, m−1}` the vectors on the right side span the whole
> `ℂ^m`.  Therefore the left side must be the zero vector, and especially for `α` such that
> `v₀ ∈ S_α` we have
>
>     0 = f_α(Z) = ∑_{v ∈ S_α} a_v Z^v.
>
> Because `Z` does not have zero coordinates, each term on the right hand side is non-zero.
> But the sum is zero, therefore there are at least two vectors `v₀, v ∈ S_α`.  From the
> definition of `S_α` we have `Z^{rv} = Z^{rv₀} = α`, so `Z` is a root of `X^{rv} − X^{rv₀}`. ∎

For orientation, the consumer of Lemma 4 in the source is

> **Theorem 3.1.**  Let `c` be a finitary integral configuration and `f = ∑ a_v X^v` a
> non-trivial integral polynomial annihilator.  Let `r` be the integer from 3 and
> `v₀ ∈ supp(f)` arbitrary.  Then the Laurent polynomial
>
>     ∏_{v ∈ supp(f), v ≠ v₀} (X^{rv} − X^{rv₀})
>
> annihilates the configuration.
>
> *Proof.*  Denote `g(X)` the polynomial in the statement.  By 4, `x₁ ⋯ x_d · g(X)` vanishes on
> all common roots of `Ann(c)`, therefore by Hilbert's nullstellensatz
> `x₁ ⋯ x_d · g(X) ∈ √(Ann(c))`.  There exists an integer `m` such that
> `x₁^m ⋯ x_d^m · g^m(X) ∈ Ann(c)`.  Then also `g^m(X)` is an annihilator and the proof is
> finished by 6. ∎

Theorem 3.1 itself is **not** proved here (it needs the Nullstellensatz and source Lemma 6).

## Definitions used in this file

The dimension is `d = 2`, so `ℤ^d = ℤ × ℤ` and `ℂ^d = ℂ × ℂ`; Laurent polynomials are
`Nivat.LaurentTwo R = AddMonoidAlgebra R (ℤ × ℤ)` and `Nivat.supp f = f.coeff.support`.

* `Nivat.KS4.scalePt n v = ((n : ℤ) * v.1, (n : ℤ) * v.2)` — the source's `v ↦ nv` on
  exponents.  Written out by hand rather than as `(n : ℤ) • v` to avoid the `SMul ℤ (ℤ × ℤ)`
  instance ambiguity (`Mul.toSMul` vs. `AddGroup.toIntSMul`).
* `Nivat.KS4.scaleExp n f = ofCoeff ((f.coeff).mapDomain (scalePt n))` — the source's
  `f(X) ↦ f(X^n)`.  **This is the definition A2's `scaleExp` has to be reconciled with**: it is
  `∑_v a_v X^v ↦ ∑_v a_v X^{nv}`, realised as a `Finsupp.mapDomain`.  For `n ≠ 0` the map
  `scalePt n` is injective (`scalePt_injective`), so no coefficients get merged and
  `supp (scaleExp n f) = (supp f).image (scalePt n)`; the only fact actually used downstream is
  `eval_scaleExp`.
* `Nivat.KS4.monoEval Z v = Z.1 ^ v.1 * Z.2 ^ v.2` (`zpow`) — the source's `Z^v`.
* `Nivat.KS4.eval φ Z f = ∑_{v ∈ supp f} φ (f.coeff v) * monoEval Z v` — the source's `f(Z)`.
  The ring hom `φ : R →+* ℂ` lets the same definition serve `R = ℤ` (`Int.castRingHom ℂ`, the
  case of the source, whose annihilators are integral) and `R = ℂ` (`RingHom.id ℂ`).

## What is proved, and what is assumed

Lemma 3 is **not** imported; its conclusion is taken as an explicit hypothesis

    hscale : ∀ n : ℕ, 0 < n → Nat.Coprime n r → act (scaleExp n f) ξ = 0

with `r : ℕ` (the source says "an integer `r`"; in its proof `r = s!`, and `Nat.Coprime`
forces the natural-number form.  Nothing below needs `r ≠ 0`).  "Z is a common root of
`Ann(c)`" is likewise an explicit hypothesis

    hroot : ∀ g : LaurentTwo R, act g ξ = 0 → eval φ Z g = 0.

Note that the finitary/integral hypotheses on `c` of the source enter only through Lemma 3, so
they do not appear here; what does appear, in their place, is the injectivity of `φ`, which is
what makes "each term `a_v Z^v` is non-zero" true.

## Main results

* `Nivat.KS4.dedekind_aux` — the Vandermonde step: if `∑_{α ∈ s} c α · α^i = 0` for every
  `i : ℕ` then `c` vanishes on `s`.  Proved by strong induction on `s` (divide out `(α − α₀)`),
  not via a Vandermonde determinant; the source only needs `i < m` but the hypothesis supplied
  by Lemma 3 holds for all `i`, so the weaker induction suffices.
* `Nivat.KS4.exists_ne_of_sums_vanish` — the combinatorial core, stated over an arbitrary
  index type.
* `Nivat.KS4.exists_ne_of_common_root` — the substance of Lemma 4: some `v ∈ supp f` with
  `v ≠ v₀` has `Z^{rv} = Z^{rv₀}`.
* `Nivat.KS4.prod_eq_zero_of_common_root` — the product form, for `Z ∈ (ℂ^*)²`.
* `Nivat.KS4.lemma4` — the source's statement verbatim, for arbitrary `Z ∈ ℂ²` (the factor
  `x₁x₂` handles the coordinates-vanish case).

## Status

Complete; **no `sorry`**.
-/

namespace Nivat.KS4

open Finset

/-! ### Evaluation at a point of `ℂ²` and scaling of exponents -/

/-- The source's `Z^v = z₁^{v₁} z₂^{v₂}`, with `zpow` (exponents may be negative). -/
noncomputable def monoEval (Z : ℂ × ℂ) (v : ℤ × ℤ) : ℂ := Z.1 ^ v.1 * Z.2 ^ v.2

/-- The source's `f(Z) = ∑ a_v Z^v`, with the coefficients pushed into `ℂ` along `φ`. -/
noncomputable def eval {R : Type*} [CommRing R] (φ : R →+* ℂ) (Z : ℂ × ℂ)
    (f : LaurentTwo R) : ℂ :=
  f.coeff.sum fun v c => φ c * monoEval Z v

theorem eval_eq_sum {R : Type*} [CommRing R] (φ : R →+* ℂ) (Z : ℂ × ℂ) (f : LaurentTwo R) :
    eval φ Z f = ∑ v ∈ supp f, φ (f.coeff v) * monoEval Z v := rfl

/-- Scaling of an exponent vector: the source's `v ↦ nv`. -/
def scalePt (n : ℕ) (v : ℤ × ℤ) : ℤ × ℤ := ((n : ℤ) * v.1, (n : ℤ) * v.2)

theorem scalePt_injective {n : ℕ} (hn : n ≠ 0) : Function.Injective (scalePt n) := by
  intro a b h
  have hn' : (n : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hn
  have h1 : (n : ℤ) * a.1 = (n : ℤ) * b.1 := congrArg Prod.fst h
  have h2 : (n : ℤ) * a.2 = (n : ℤ) * b.2 := congrArg Prod.snd h
  exact Prod.ext (mul_left_cancel₀ hn' h1) (mul_left_cancel₀ hn' h2)

/-- The source's `f(X) ↦ f(X^n)`: `∑ a_v X^v ↦ ∑ a_v X^{nv}`. -/
noncomputable def scaleExp {R : Type*} [CommRing R] (n : ℕ) (f : LaurentTwo R) :
    LaurentTwo R :=
  AddMonoidAlgebra.ofCoeff (f.coeff.mapDomain (scalePt n))

theorem monoEval_ne_zero {Z : ℂ × ℂ} (h1 : Z.1 ≠ 0) (h2 : Z.2 ≠ 0) (v : ℤ × ℤ) :
    monoEval Z v ≠ 0 :=
  mul_ne_zero (zpow_ne_zero _ h1) (zpow_ne_zero _ h2)

/-- `Z^{nv} = (Z^v)^n`.  No non-vanishing hypothesis is needed: `zpow_mul` and `mul_zpow` hold
unconditionally in a `CommGroupWithZero`. -/
theorem monoEval_scalePt (Z : ℂ × ℂ) (n : ℕ) (v : ℤ × ℤ) :
    monoEval Z (scalePt n v) = monoEval Z v ^ n := by
  unfold monoEval scalePt
  rw [mul_comm (n : ℤ) v.1, mul_comm (n : ℤ) v.2, zpow_mul, zpow_mul, zpow_natCast,
    zpow_natCast, ← mul_pow]

theorem eval_scaleExp {R : Type*} [CommRing R] (φ : R →+* ℂ) (Z : ℂ × ℂ) (f : LaurentTwo R)
    {n : ℕ} (hn : n ≠ 0) :
    eval φ Z (scaleExp n f) = ∑ v ∈ supp f, φ (f.coeff v) * monoEval Z (scalePt n v) := by
  rw [eval, scaleExp]
  show (Finsupp.mapDomain (scalePt n) f.coeff).sum (fun v c => φ c * monoEval Z v) = _
  rw [Finsupp.sum_mapDomain_index_inj (scalePt_injective hn)]
  rfl

/-! ### The Vandermonde step -/

/-- If `∑_{α ∈ s} c α · α^i = 0` for **every** `i : ℕ`, then `c` vanishes on `s`.

The source invokes the Vandermonde determinant for `i ∈ {0, …, m−1}`.  Here the hypothesis is
available for all `i`, which permits the cheaper argument: multiply the relation by `(α − α₀)`
to kill the `α₀` term and induct on `s`. -/
theorem dedekind_aux :
    ∀ (s : Finset ℂ) (c : ℂ → ℂ), (∀ i : ℕ, ∑ α ∈ s, c α * α ^ i = 0) → ∀ α₀ ∈ s, c α₀ = 0 := by
  classical
  intro s
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    intro c h α₀ hα₀
    have hsum' : ∀ i : ℕ, ∑ α ∈ s.erase α₀, c α * (α - α₀) * α ^ i = 0 := by
      intro i
      have hzero : c α₀ * (α₀ - α₀) * α₀ ^ i = 0 := by simp
      have hdrop : ∑ α ∈ s.erase α₀, c α * (α - α₀) * α ^ i
          = ∑ α ∈ s, c α * (α - α₀) * α ^ i := Finset.sum_erase s hzero
      rw [hdrop]
      have hsplit : ∑ α ∈ s, c α * (α - α₀) * α ^ i
          = (∑ α ∈ s, c α * α ^ (i + 1)) - α₀ * ∑ α ∈ s, c α * α ^ i := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun α _ => ?_
        simp only [pow_succ]
        ring
      rw [hsplit, h (i + 1), h i, mul_zero, sub_zero]
    have herase := ih (s.erase α₀) (Finset.erase_ssubset hα₀)
      (fun α => c α * (α - α₀)) hsum'
    have hczero : ∀ α ∈ s.erase α₀, c α = 0 := by
      intro α hα
      have h1 : c α * (α - α₀) = 0 := herase α hα
      exact (mul_eq_zero.mp h1).resolve_right (sub_ne_zero.mpr (Finset.ne_of_mem_erase hα))
    have h0 := h 0
    simp only [pow_zero, mul_one] at h0
    rw [← Finset.add_sum_erase s c hα₀, Finset.sum_eq_zero hczero, add_zero] at h0
    exact h0

/-! ### The combinatorial core of Lemma 4 -/

/-- Abstract form of Lemma 4.  `β` plays the role of `v ↦ Z^{rv}`, `a` of `v ↦ a_v` and `e` of
`v ↦ Z^v`.  The classes `S_α` of the source are the fibres of `β`. -/
theorem exists_ne_of_sums_vanish {ι : Type*} (S : Finset ι) (a e β : ι → ℂ)
    (hvan : ∀ i : ℕ, ∑ v ∈ S, a v * e v * β v ^ i = 0)
    {v₀ : ι} (hv₀ : v₀ ∈ S) (ha : a v₀ ≠ 0) (he : e v₀ ≠ 0) :
    ∃ v ∈ S, v ≠ v₀ ∧ β v = β v₀ := by
  classical
  have hcc : ∀ i : ℕ,
      ∑ α ∈ S.image β, (∑ v ∈ S with β v = α, a v * e v) * α ^ i = 0 := by
    intro i
    have hfib : ∀ α ∈ S.image β, (∑ v ∈ S with β v = α, a v * e v) * α ^ i
        = ∑ v ∈ S with β v = α, a v * e v * β v ^ i := by
      intro α _
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun v hv => ?_
      rw [(Finset.mem_filter.mp hv).2]
    rw [Finset.sum_congr rfl hfib,
      Finset.sum_fiberwise_of_maps_to (fun v hv => Finset.mem_image_of_mem β hv)]
    exact hvan i
  have hzero := dedekind_aux (S.image β) _ hcc (β v₀) (Finset.mem_image_of_mem β hv₀)
  by_contra hcon
  push Not at hcon
  have hfil : (S.filter (fun v => β v = β v₀)) = {v₀} := by
    refine Finset.eq_singleton_iff_unique_mem.mpr ⟨Finset.mem_filter.mpr ⟨hv₀, rfl⟩, ?_⟩
    intro v hv
    rcases Finset.mem_filter.mp hv with ⟨hvS, hvβ⟩
    by_contra hne
    exact hcon v hvS hne hvβ
  rw [hfil, Finset.sum_singleton] at hzero
  exact (mul_ne_zero ha he) hzero

/-! ### Lemma 4 -/

variable {R : Type*} [CommRing R]

/-- **Kari–Szabados, Lemma 4** (substance, for `Z` with non-zero coordinates).

`hscale` is the conclusion of source Lemma 3 (supplied as a hypothesis, not imported);
`hroot` says `Z` is a common root of `Ann(ξ)`; `hφ` is what makes each term `a_v Z^v`
non-zero (for `R = ℤ`, `φ = Int.castRingHom ℂ`). -/
theorem exists_ne_of_common_root (φ : R →+* ℂ) (hφ : Function.Injective φ)
    {ξ : Config R} {f : LaurentTwo R} {Z : ℂ × ℂ} {r : ℕ}
    (h1 : Z.1 ≠ 0) (h2 : Z.2 ≠ 0)
    (hroot : ∀ g : LaurentTwo R, act g ξ = 0 → eval φ Z g = 0)
    (hscale : ∀ n : ℕ, 0 < n → Nat.Coprime n r → act (scaleExp n f) ξ = 0)
    {v₀ : ℤ × ℤ} (hv₀ : v₀ ∈ supp f) :
    ∃ v ∈ supp f, v ≠ v₀ ∧ monoEval Z (scalePt r v) = monoEval Z (scalePt r v₀) := by
  classical
  have hvan : ∀ i : ℕ, ∑ v ∈ supp f,
      φ (f.coeff v) * monoEval Z v * monoEval Z (scalePt r v) ^ i = 0 := by
    intro i
    have hpos : 0 < 1 + i * r := lt_of_lt_of_le Nat.one_pos (Nat.le_add_right 1 (i * r))
    have hcop : Nat.Coprime (1 + i * r) r :=
      (Nat.coprime_add_mul_right_left 1 r i).mpr (Nat.coprime_one_left r)
    have h0 : eval φ Z (scaleExp (1 + i * r) f) = 0 := hroot _ (hscale _ hpos hcop)
    rw [eval_scaleExp φ Z f hpos.ne'] at h0
    rw [← h0]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [monoEval_scalePt, monoEval_scalePt]
    ring
  exact exists_ne_of_sums_vanish (supp f) (fun v => φ (f.coeff v)) (fun v => monoEval Z v)
    (fun v => monoEval Z (scalePt r v)) hvan hv₀
    ((map_ne_zero_iff φ hφ).mpr (mem_supp.mp hv₀)) (monoEval_ne_zero h1 h2 v₀)

/-- **Kari–Szabados, Lemma 4**, product form, for `Z ∈ (ℂ^*)²`. -/
theorem prod_eq_zero_of_common_root (φ : R →+* ℂ) (hφ : Function.Injective φ)
    {ξ : Config R} {f : LaurentTwo R} {Z : ℂ × ℂ} {r : ℕ}
    (h1 : Z.1 ≠ 0) (h2 : Z.2 ≠ 0)
    (hroot : ∀ g : LaurentTwo R, act g ξ = 0 → eval φ Z g = 0)
    (hscale : ∀ n : ℕ, 0 < n → Nat.Coprime n r → act (scaleExp n f) ξ = 0)
    {v₀ : ℤ × ℤ} (hv₀ : v₀ ∈ supp f) :
    ∏ v ∈ (supp f).erase v₀, (monoEval Z (scalePt r v) - monoEval Z (scalePt r v₀)) = 0 := by
  obtain ⟨v, hvS, hvne, hveq⟩ :=
    exists_ne_of_common_root φ hφ h1 h2 hroot hscale hv₀
  exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hvne, hvS⟩) (sub_eq_zero.mpr hveq)

/-- **Kari–Szabados, Lemma 4**, exactly as stated in the source (`d = 2`):

    g(X) = x₁ x₂ ∏_{v ∈ supp(f), v ≠ v₀} (X^{rv} − X^{rv₀})

vanishes at every common root `Z ∈ ℂ²` of `Ann(ξ)` — including those with a zero coordinate,
which the leading factor `x₁ x₂` disposes of. -/
theorem lemma4 (φ : R →+* ℂ) (hφ : Function.Injective φ)
    {ξ : Config R} {f : LaurentTwo R} (Z : ℂ × ℂ) {r : ℕ}
    (hroot : ∀ g : LaurentTwo R, act g ξ = 0 → eval φ Z g = 0)
    (hscale : ∀ n : ℕ, 0 < n → Nat.Coprime n r → act (scaleExp n f) ξ = 0)
    {v₀ : ℤ × ℤ} (hv₀ : v₀ ∈ supp f) :
    Z.1 * Z.2 * ∏ v ∈ (supp f).erase v₀,
        (monoEval Z (scalePt r v) - monoEval Z (scalePt r v₀)) = 0 := by
  by_cases h1 : Z.1 = 0
  · rw [h1, zero_mul, zero_mul]
  by_cases h2 : Z.2 = 0
  · rw [h2, mul_zero, zero_mul]
  rw [prod_eq_zero_of_common_root φ hφ h1 h2 hroot hscale hv₀, mul_zero]

end Nivat.KS4
