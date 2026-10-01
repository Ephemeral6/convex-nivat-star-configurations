/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.Laurent.Basic
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.FieldTheory.Finite.Basic

/-!
# Kari–Szabados, Lemma 3: expanding an annihilator

Formalisation of Lemma 3 of J. Kari and M. Szabados, *An algebraic geometric approach to
Nivat's conjecture* (arXiv:1605.05929v1), specialised to `d = 2`.

## The source, verbatim

The source's `\autoref{sec:basics}` defines, for `f(X) = ∑ a_v X^v` and a positive integer `n`,

> `f(X^n) = ∑ a_v X^{n v}`.  (See Figure 1.)  The following example, and the proof of
> Lemma 3, use the well known fact that for any integral polynomial `f` and prime number `p`,
> we have `f^p(X) ≡ f(X^p) (mod p)`.

and the lemma itself (`lem-expanding-annihilator` in the LaTeX source) reads, verbatim:

> **Lemma 3.**  Let `c(X)` be a finitary integral configuration and `f(X) ∈ Ann(c)` a non-zero
> integer polynomial.  Then there exists an integer `r` such that for every positive integer
> `n` relatively prime to `r` we have `f(X^n) ∈ Ann(c)`.
>
> *Proof.*  Denote `f(X) = ∑ a_v X^v` and let `m ∈ ℕ` be arbitrary.  We prove that if `f(X^m)`
> is an annihilator, then also `f(X^{pm})` is an annihilator for a large enough prime `p`.
>
> Let `p` be a prime.  Since `f^p(X) ≡ f(X^p) (mod p)` we especially have
> `f^p(X^m) ≡ f(X^{pm}) (mod p)`.  We assume that `f(X^m)` annihilates `c(X)`, therefore
> multiplying both sides by `c(X)` results in
>
>   `0 ≡ f(X^{pm}) c(X) (mod p)`.
>
> The coefficients in `f(X^{pm}) c(X)` are bounded in absolute value by
>
>   `s = c_max ∑ |a_v|`,
>
> where `c_max` is the maximum absolute value of coefficients in `c`.  Note that the bound is
> independent of `m`.  Therefore for any `m`, if `p > s` we have `f(X^{pm}) c(X) = 0`, which
> means `f(X^{pm}) ∈ Ann(c)`.
>
> To finish the proof, set `r = s!`.  Now every `n` relatively prime to `r` is of the form
> `p_1 ⋯ p_k` where each `p_i` is a prime greater than `s`.  Because `f(X)` is an annihilator
> now it follows easily by induction that also `f(X^{p_1 ⋯ p_k})` is an annihilator.  ∎

## What is formalised here

Everything above, with no `sorry`.  The main result is

* `Nivat.KS3.exists_scaling_ann` — Lemma 3 in the shape requested by the caller:
  ```
  theorem exists_scaling_ann (hbdd : ∃ M, ∀ z, |ξ z| ≤ M)
      {f : LaurentTwo ℤ} (_hf : f ≠ 0) (hann : act f ξ = 0) :
      ∃ r : ℕ, 0 < r ∧ ∀ n : ℕ, 0 < n → Nat.Coprime n r → act (scaleExp n f) ξ = 0
  ```

* `Nivat.KS3.exists_scaling_ann_of_finite` — the same with the source's own hypothesis
  `(Set.range ξ).Finite` ("finitary") in place of boundedness.

and the quantitative form it is derived from is

* `Nivat.KS3.act_scaleExp_of_primes` — if `|ξ| ≤ M` everywhere and `f` annihilates `ξ`, then
  `f(X^n)` annihilates `ξ` for every `n > 0` all of whose prime factors exceed `M · ∑_v |a_v|`.

Supporting pieces:

* `Nivat.KS3.scaleExp` — the substitution `X ↦ X^n`, i.e. `Finsupp.mapDomain (n • ·)` on
  exponents, packaged through `AddMonoidAlgebra.mapDomainRingHom`, hence a **ring
  homomorphism** for every `n` (no injectivity needed; injectivity of `n • ·` is used only for
  `ell_scaleExp`).
* `Nivat.KS3.pow_card_eq_scaleExp` — the Frobenius congruence, proved as an *equality*
  `g ^ p = g(X^p)` in `LaurentTwo (ZMod p)`, via `CharP (LaurentTwo (ZMod p)) p`
  (`Nivat.KS3.charP_laurent`), `sum_pow_char` and `ZMod.pow_card`.
* `Nivat.KS3.ell` — the source's `∑_v |a_v|`; `Nivat.KS3.ell_scaleExp` is the source's
  "*the bound is independent of `m`*".
* `Nivat.KS3.abs_act_le` — the source's coefficient bound `|f(X^{pm}) c| ≤ s`.

## Deviations from the source, stated loudly

1. **Hypothesis "finitary" is weakened to "bounded".**  The source assumes `c` finitary (finitely
   many distinct coefficients); the proof uses only that `|c_v| ≤ c_max` for some `c_max`.  The
   Lean hypothesis is therefore `∃ M, ∀ z, |ξ z| ≤ M`, which is implied by finitary
   (cf. `Nivat.KSC.bounded_of_range_finite`).  This is a *weaker* hypothesis, so a *stronger*
   statement.
2. **`f ≠ 0` is not used.**  The argument goes through verbatim for `f = 0` (then `ell f = 0`,
   `r = 0! = 1`).  The hypothesis is retained in the statement — named `_hf` — so that the Lean
   statement matches the source and the caller's requested signature exactly.
3. **`r` is produced as a `ℕ` with `0 < r`**, rather than "an integer `r`"; `Nat.Coprime n r` is
   the Lean spelling of "`n` relatively prime to `r`".  The witness is literally the source's
   `s!` with `s = M · ∑_v |a_v|` (truncated to `ℕ`; `s ≥ 0` always).
4. **`f(X^n)` is `scaleExp n f`**, i.e. `∑ a_v X^{n v}` — the source's Section 2 definition, read
   in the Laurent ring `ℤ[X₁^±, X₂^±]` rather than in `ℤ[X₁, X₂]`.  Nothing in the proof needs
   the exponents to be non-negative.
5. The source's induction is on `m` ("if `f(X^m)` is an annihilator then so is `f(X^{pm})`");
   the Lean induction is strong induction on `n`, peeling off `n.minFac`.  Same content.

## Status

**Complete; no `sorry`.**

Everything lives in the namespace `Nivat.KS3` to avoid collisions with concurrently developed
files; nothing outside this file is modified.
-/

namespace Nivat.KS3

open Finset

/-! ### The substitution `X ↦ X^n` -/

/-- `v ↦ n • v` on the exponent lattice `ℤ²`, as an additive monoid endomorphism. -/
def smulHom (n : ℕ) : (ℤ × ℤ) →+ (ℤ × ℤ) :=
  AddMonoidHom.mk' (fun v => n • v) (fun a b => smul_add n a b)

@[simp] theorem smulHom_apply (n : ℕ) (v : ℤ × ℤ) : smulHom n v = n • v := rfl

variable {R : Type*} [CommRing R]

/-- The source's `f(X^n) = ∑ a_v X^{n v}` (Section 2 of arXiv:1605.05929).

Realised as `AddMonoidAlgebra.mapDomainRingHom` along `v ↦ n • v`, so that it is a ring
homomorphism for every `n`. -/
noncomputable def scaleExp (n : ℕ) (f : LaurentTwo R) : LaurentTwo R :=
  AddMonoidAlgebra.mapDomainRingHom R (smulHom n) f

theorem coeff_scaleExp (n : ℕ) (f : LaurentTwo R) :
    (scaleExp n f).coeff = Finsupp.mapDomain (fun v : ℤ × ℤ => n • v) f.coeff := rfl

@[simp] theorem scaleExp_single (n : ℕ) (v : ℤ × ℤ) (c : R) :
    scaleExp n (AddMonoidAlgebra.single v c) = AddMonoidAlgebra.single (n • v) c :=
  AddMonoidAlgebra.mapDomain_single

theorem scaleExp_add (n : ℕ) (f g : LaurentTwo R) :
    scaleExp n (f + g) = scaleExp n f + scaleExp n g :=
  map_add (AddMonoidAlgebra.mapDomainRingHom R (smulHom n)) f g

theorem scaleExp_mul (n : ℕ) (f g : LaurentTwo R) :
    scaleExp n (f * g) = scaleExp n f * scaleExp n g :=
  map_mul (AddMonoidAlgebra.mapDomainRingHom R (smulHom n)) f g

theorem scaleExp_sum {ι : Type*} (n : ℕ) (s : Finset ι) (F : ι → LaurentTwo R) :
    scaleExp n (∑ i ∈ s, F i) = ∑ i ∈ s, scaleExp n (F i) :=
  map_sum (AddMonoidAlgebra.mapDomainRingHom R (smulHom n)) F s

@[simp] theorem scaleExp_one (f : LaurentTwo R) : scaleExp 1 f = f := by
  apply AddMonoidAlgebra.coeff_injective
  rw [coeff_scaleExp]
  simp only [one_smul]
  exact Finsupp.mapDomain_id

theorem scaleExp_scaleExp (m n : ℕ) (f : LaurentTwo R) :
    scaleExp m (scaleExp n f) = scaleExp (m * n) f := by
  apply AddMonoidAlgebra.coeff_injective
  rw [coeff_scaleExp, coeff_scaleExp, coeff_scaleExp, ← Finsupp.mapDomain_comp]
  congr 1
  funext v
  show m • (n • v) = (m * n) • v
  rw [smul_smul]

/-- `v ↦ n • v` is injective on `ℤ²` for `n ≠ 0`. -/
theorem smul_injective {n : ℕ} (hn : n ≠ 0) :
    Function.Injective (fun v : ℤ × ℤ => n • v) := by
  have hn' : (n : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  intro v w h
  have h1 : (n : ℤ) * v.1 = (n : ℤ) * w.1 := by
    have := congrArg Prod.fst h
    simpa [nsmul_eq_mul] using this
  have h2 : (n : ℤ) * v.2 = (n : ℤ) * w.2 := by
    have := congrArg Prod.snd h
    simpa [nsmul_eq_mul] using this
  exact Prod.ext (mul_left_cancel₀ hn' h1) (mul_left_cancel₀ hn' h2)

/-! ### The `ℓ¹` norm of the coefficient vector: the source's `∑_v |a_v|` -/

/-- The source's `∑_v |a_v|` for `f = ∑ a_v X^v`. -/
def ell (f : LaurentTwo ℤ) : ℤ := f.coeff.sum fun _ c => |c|

theorem ell_eq_sum (f : LaurentTwo ℤ) : ell f = ∑ u ∈ f.coeff.support, |f.coeff u| := rfl

theorem ell_nonneg (f : LaurentTwo ℤ) : 0 ≤ ell f := by
  rw [ell_eq_sum]
  exact Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- **"Note that the bound is independent of `m`."**  Scaling the exponents by a non-zero `n`
permutes the coefficients, hence does not change `∑_v |a_v|`. -/
theorem ell_scaleExp {n : ℕ} (hn : n ≠ 0) (f : LaurentTwo ℤ) : ell (scaleExp n f) = ell f := by
  classical
  have hinj := smul_injective hn
  rw [ell_eq_sum, ell_eq_sum, coeff_scaleExp,
    Finsupp.mapDomain_support_of_injective hinj]
  rw [Finset.sum_image (fun x _ y _ h => hinj h)]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finsupp.mapDomain_apply hinj]

/-! ### The coefficient bound of the source's proof -/

/-- The source's `|f(X^{pm}) c(X)| ≤ s = c_max ∑ |a_v|`, in operator form: if `|ξ| ≤ M`
pointwise then `|f(X) ξ| ≤ M · ∑_v |a_v|` pointwise. -/
theorem abs_act_le {ξ : Config ℤ} {M : ℤ} (hM : ∀ z, |ξ z| ≤ M) (f : LaurentTwo ℤ)
    (z : ℤ × ℤ) : |act f ξ z| ≤ M * ell f := by
  rw [act_apply, Finsupp.sum, ell_eq_sum, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun u _ => ?_)
  calc |f.coeff u * ξ (z + u)| = |f.coeff u| * |ξ (z + u)| := abs_mul _ _
    _ ≤ |f.coeff u| * M := mul_le_mul_of_nonneg_left (hM _) (abs_nonneg _)
    _ = M * |f.coeff u| := mul_comm _ _

/-- If every coefficient of `g` is divisible by `k`, so is every value of `g ξ`. -/
theorem dvd_act {k : ℤ} {g : LaurentTwo ℤ} (h : ∀ u, k ∣ g.coeff u) (ξ : Config ℤ)
    (z : ℤ × ℤ) : k ∣ act g ξ z := by
  rw [act_apply, Finsupp.sum]
  exact Finset.dvd_sum fun u _ => Dvd.dvd.mul_right (h u) _

/-- A power of an annihilator is an annihilator. -/
theorem act_pow_eq_zero {f : LaurentTwo ℤ} {ξ : Config ℤ} (h : act f ξ = 0) {k : ℕ}
    (hk : 0 < k) : act (f ^ k) ξ = 0 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [pow_succ, act_mul, h, act_zero_right]

/-! ### The Frobenius congruence `f(X)^p ≡ f(X^p) (mod p)` -/

/-- `ℤ/p [X₁^±, X₂^±]` has characteristic `p`. -/
theorem charP_laurent (p : ℕ) [NeZero p] : CharP (LaurentTwo (ZMod p)) p := by
  refine ⟨fun x => ?_⟩
  rw [AddMonoidAlgebra.natCast_def, AddMonoidAlgebra.single_eq_zero]
  exact CharP.cast_eq_zero_iff (ZMod p) p x

/-- **The Frobenius congruence, as an identity in characteristic `p`:** `g^p = g(X^p)` in
`ℤ/p [X₁^±, X₂^±]`.  This is the source's "*well known fact that for any integral polynomial
`f` and prime number `p`, we have `f^p(X) ≡ f(X^p) (mod p)`*". -/
theorem pow_card_eq_scaleExp (p : ℕ) [hp : Fact p.Prime] (g : LaurentTwo (ZMod p)) :
    g ^ p = scaleExp p g := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  have : CharP (LaurentTwo (ZMod p)) p := charP_laurent p
  have hg : ∑ v ∈ g.coeff.support, (AddMonoidAlgebra.single v (g.coeff v) :
      LaurentTwo (ZMod p)) = g := AddMonoidAlgebra.sum_coeff_single g
  calc g ^ p
      = (∑ v ∈ g.coeff.support, (AddMonoidAlgebra.single v (g.coeff v) :
          LaurentTwo (ZMod p))) ^ p := by rw [hg]
    _ = ∑ v ∈ g.coeff.support, (AddMonoidAlgebra.single v (g.coeff v) :
          LaurentTwo (ZMod p)) ^ p := sum_pow_char p _ _
    _ = ∑ v ∈ g.coeff.support, scaleExp p (AddMonoidAlgebra.single v (g.coeff v) :
          LaurentTwo (ZMod p)) := by
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [AddMonoidAlgebra.single_pow, scaleExp_single, ZMod.pow_card]
    _ = scaleExp p g := by rw [← scaleExp_sum, hg]

/-- Coefficient reduction commutes with `X ↦ X^n`. -/
theorem mapRingHom_scaleExp {S : Type*} [CommRing S] (ψ : R →+* S) (n : ℕ) (f : LaurentTwo R) :
    AddMonoidAlgebra.mapRingHom (ℤ × ℤ) ψ (scaleExp n f)
      = scaleExp n (AddMonoidAlgebra.mapRingHom (ℤ × ℤ) ψ f) :=
  RingHom.congr_fun (AddMonoidAlgebra.mapRingHom_comp_mapDomainRingHom ψ (smulHom n)) f

/-- The integral form of the Frobenius congruence: every coefficient of `f^p − f(X^p)` is
divisible by `p`. -/
theorem dvd_coeff_pow_sub_scaleExp (p : ℕ) [hp : Fact p.Prime] (f : LaurentTwo ℤ)
    (u : ℤ × ℤ) : (p : ℤ) ∣ (f ^ p - scaleExp p f).coeff u := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  set φ := AddMonoidAlgebra.mapRingHom (ℤ × ℤ) (Int.castRingHom (ZMod p)) with hφ
  have h : φ (f ^ p) = φ (scaleExp p f) := by
    rw [map_pow, pow_card_eq_scaleExp p (φ f), hφ, mapRingHom_scaleExp]
  have hz : φ (f ^ p - scaleExp p f) = 0 := by rw [map_sub, h, sub_self]
  have hc := congrArg (fun x : LaurentTwo (ZMod p) => x.coeff u) hz
  simp only [hφ, AddMonoidAlgebra.coeff_mapRingHom, AddMonoidAlgebra.coeff_zero,
    Finsupp.coe_zero, Pi.zero_apply, eq_intCast] at hc
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hc

/-! ### The inductive step of the source's proof -/

/-- **The inductive step.**  If `f` annihilates the bounded configuration `ξ` and `p` is a prime
exceeding `s = M · ∑_v |a_v|`, then `f(X^p)` annihilates `ξ`. -/
theorem step {ξ : Config ℤ} {M : ℤ} (hM : ∀ z, |ξ z| ≤ M) {f : LaurentTwo ℤ}
    (hann : act f ξ = 0) {p : ℕ} (hp : p.Prime) (hlt : M * ell f < (p : ℤ)) :
    act (scaleExp p f) ξ = 0 := by
  have : Fact p.Prime := ⟨hp⟩
  funext z
  show act (scaleExp p f) ξ z = 0
  have hpow : act (f ^ p) ξ = 0 := act_pow_eq_zero hann hp.pos
  have hdvd : (p : ℤ) ∣ act (scaleExp p f) ξ z := by
    have h1 : (p : ℤ) ∣ act (f ^ p - scaleExp p f) ξ z :=
      dvd_act (dvd_coeff_pow_sub_scaleExp p f) ξ z
    rwa [act_sub_left, Pi.sub_apply, hpow, Pi.zero_apply, zero_sub, dvd_neg] at h1
  have hbd : |act (scaleExp p f) ξ z| ≤ M * ell f := by
    have := abs_act_le hM (scaleExp p f) z
    rwa [ell_scaleExp hp.pos.ne' f] at this
  rcases eq_or_ne (act (scaleExp p f) ξ z) 0 with h | h
  · exact h
  · exact absurd (Int.le_of_dvd (abs_pos.mpr h) ((dvd_abs _ _).mpr hdvd)) (by linarith)

/-- **Lemma 3, quantitative form.**  If `|ξ| ≤ M` pointwise and `f` annihilates `ξ`, then
`f(X^n)` annihilates `ξ` for every positive `n` all of whose prime factors exceed
`s = M · ∑_v |a_v|`. -/
theorem act_scaleExp_of_primes {ξ : Config ℤ} {M : ℤ} (hM : ∀ z, |ξ z| ≤ M) {f : LaurentTwo ℤ}
    (hann : act f ξ = 0) :
    ∀ n : ℕ, 0 < n → (∀ q : ℕ, q.Prime → q ∣ n → M * ell f < (q : ℤ)) →
      act (scaleExp n f) ξ = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn hq
    rcases eq_or_ne n 1 with rfl | hne
    · rw [scaleExp_one]; exact hann
    · have h1 : 1 < n := by omega
      have hpp : (n.minFac).Prime := Nat.minFac_prime (by omega)
      obtain ⟨m, hm⟩ : n.minFac ∣ n := Nat.minFac_dvd n
      have hm0 : 0 < m := by
        rcases Nat.eq_zero_or_pos m with rfl | h
        · omega
        · exact h
      have hmlt : m < n := by
        have h2 : 1 < n.minFac := hpp.one_lt
        calc m = 1 * m := (one_mul m).symm
          _ < n.minFac * m := by exact Nat.mul_lt_mul_of_lt_of_le h2 (le_refl m) hm0
          _ = n := hm.symm
      have hmdvd : m ∣ n := ⟨n.minFac, by rw [Nat.mul_comm]; exact hm⟩
      have hmann : act (scaleExp m f) ξ = 0 :=
        ih m hmlt hm0 (fun q hqp hqd => hq q hqp (hqd.trans hmdvd))
      have hstep := step hM hmann hpp
        (by rw [ell_scaleExp hm0.ne' f]; exact hq n.minFac hpp (Nat.minFac_dvd n))
      rwa [scaleExp_scaleExp, ← hm] at hstep

/-! ### Lemma 3 -/

/-- **Kari–Szabados, Lemma 3.**  Let `ξ` be a bounded integral configuration and `f` a non-zero
integral annihilator of `ξ`.  Then there is `r > 0` such that `f(X^n)` annihilates `ξ` for every
positive `n` coprime to `r`.

The witness is the source's `r = s!` with `s = M · ∑_v |a_v|`.  The hypothesis `f ≠ 0` is not
used; it is kept to match the source's statement. -/
theorem exists_scaling_ann {ξ : Config ℤ} (hbdd : ∃ M, ∀ z, |ξ z| ≤ M)
    {f : LaurentTwo ℤ} (_hf : f ≠ 0) (hann : act f ξ = 0) :
    ∃ r : ℕ, 0 < r ∧ ∀ n : ℕ, 0 < n → Nat.Coprime n r → act (scaleExp n f) ξ = 0 := by
  obtain ⟨M, hM⟩ := hbdd
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  have hs0 : 0 ≤ M * ell f := mul_nonneg hM0 (ell_nonneg f)
  refine ⟨Nat.factorial (M * ell f).toNat, Nat.factorial_pos _, fun n hn hcop => ?_⟩
  refine act_scaleExp_of_primes hM hann n hn (fun q hq hqn => ?_)
  by_contra hle
  rw [not_lt] at hle
  have hq1 : q ≤ (M * ell f).toNat := by
    generalize M * ell f = t at hs0 hle
    omega
  have hfact : q ∣ Nat.factorial (M * ell f).toNat := Nat.dvd_factorial hq.pos hq1
  have hg : q ∣ Nat.gcd n (Nat.factorial (M * ell f).toNat) := Nat.dvd_gcd hqn hfact
  rw [Nat.Coprime] at hcop
  rw [hcop] at hg
  exact hq.one_lt.ne' (Nat.dvd_one.mp hg)

/-- **Kari–Szabados, Lemma 3, with the source's hypothesis verbatim.**  Here `ξ` is *finitary*
(it takes only finitely many values); boundedness, the only consequence used, is extracted on
the spot so that this file stays independent of `Nivat/External/KSCorollary.lean`. -/
theorem exists_scaling_ann_of_finite {ξ : Config ℤ} (hA : (Set.range ξ).Finite)
    {f : LaurentTwo ℤ} (hf : f ≠ 0) (hann : act f ξ = 0) :
    ∃ r : ℕ, 0 < r ∧ ∀ n : ℕ, 0 < n → Nat.Coprime n r → act (scaleExp n f) ξ = 0 := by
  obtain ⟨M, hM⟩ := (hA.image (fun x : ℤ => |x|)).bddAbove
  exact exists_scaling_ann ⟨M, fun z => hM ⟨ξ z, Set.mem_range_self z, rfl⟩⟩ hf hann

end Nivat.KS3
