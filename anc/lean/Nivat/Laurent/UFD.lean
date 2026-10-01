/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.Laurent.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.GroupTheory.MonoidLocalization.UniqueFactorization
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.BigOperators.Associated

/-!
# `ℂ[T₁^±, T₂^±]` is a unique factorisation domain

Formalisation of the two standard facts about the Laurent ring quoted in §0.3 of *The Convex
Nivat Conjecture* (Pan):

> The ring `ℂ[T₁^±, T₂^±]` is an integral domain and a unique factorisation domain, and its
> units are exactly the monomials `c T^u` with `c ∈ ℂ^×`.

The integral-domain half is already in `Nivat.Laurent.Basic` (Mathlib supplies it).  This file
covers the UFD half, which Lemma 2.4(d) uses to assemble `A | f` from the individual prime
divisibilities, and the description of the units, used to show that primes coming from
different directions are non-associate.

The route taken is the localisation route of the paper, but run through *one* variable at a
time, which lets Mathlib's `LaurentPolynomial` API do all the work:
`AddMonoidAlgebra.curryRingEquiv` identifies `ℂ[T₁^±, T₂^±] = ℂ[ℤ × ℤ]` with
`(ℂ[T^±])[T^±]` (`Nivat.curry`), `ℂ[T^±]` is the localisation of `ℂ[T]` at the powers of `T`
(`LaurentPolynomial.isLocalization`), a polynomial ring over a UFD is a UFD
(`Polynomial.uniqueFactorizationMonoid`) and a localisation of a UFD is a UFD
(`UniqueFactorizationMonoid.of_isLocalization`).  So the tower
`ℂ → ℂ[T] → ℂ[T^±] → (ℂ[T^±])[T] → (ℂ[T^±])[T^±] ≅ ℂ[T₁^±, T₂^±]`
stays inside UFDs throughout.

The same identification produces the primes: `T^v - λ` becomes `Polynomial.X - C λ` after the
unimodular substitution `Nivat.basisAddEquiv` that sends `(1, 0)` to `v`, and
`Polynomial.prime_X_sub_C` applies.

The units are computed from `TwoUniqueSums (ℤ × ℤ)`: if `f g = 1` then the product of the
cardinalities of the two supports cannot exceed `1`, because otherwise `f g` would have at
least two support points while `1` has exactly one.

## Main results

* `Nivat.instUniqueFactorizationMonoidLaurentTwo` — the UFD instance.
* `Nivat.isUnit_iff_mono` — the units are the non-zero monomials.

## Status

Complete; no `sorry`.
-/

namespace Nivat

open AddMonoidAlgebra

/-! ### The Laurent ring as a one-variable Laurent ring over a one-variable Laurent ring -/

/-- `R[T₁^±, T₂^±] ≃+* (R[T^±])[T^±]`, i.e. Mathlib's `AddMonoidAlgebra.curryRingEquiv` for the
lattice `ℤ × ℤ`.  This is the formal counterpart of "regard a two-variable Laurent polynomial
as a one-variable Laurent polynomial whose coefficients are Laurent polynomials".  Paper §0.3. -/
noncomputable def curry (R : Type*) [CommRing R] :
    LaurentTwo R ≃+* LaurentPolynomial (LaurentPolynomial R) :=
  AddMonoidAlgebra.curryRingEquiv

@[simp] theorem curry_single {R : Type*} [CommRing R] (m n : ℤ) (c : R) :
    curry R (AddMonoidAlgebra.single (m, n) c)
      = AddMonoidAlgebra.single m (AddMonoidAlgebra.single n c) :=
  AddMonoidAlgebra.curryRingEquiv_single m n c

/-! ### Unique factorisation -/

/-- `K[T^±]` is a unique factorisation domain for a field `K`: it is the localisation of `K[T]`
at the powers of `T`, and `K[T]` is a UFD.  Paper §0.3. -/
theorem uniqueFactorizationMonoid_laurentPolynomial (K : Type*) [Field K] :
    UniqueFactorizationMonoid (LaurentPolynomial K) :=
  UniqueFactorizationMonoid.of_isLocalization
    (Submonoid.powers (Polynomial.X : Polynomial K)) (LaurentPolynomial K)

/-- `ℂ[T₁^±, T₂^±]` is a unique factorisation domain.  Paper §0.3, used in Lemma 2.4(d). -/
noncomputable instance instUniqueFactorizationMonoidLaurentTwo :
    UniqueFactorizationMonoid (LaurentTwo ℂ) := by
  have h1 : UniqueFactorizationMonoid (LaurentPolynomial ℂ) :=
    uniqueFactorizationMonoid_laurentPolynomial ℂ
  have h2 : UniqueFactorizationMonoid (LaurentPolynomial (LaurentPolynomial ℂ)) :=
    UniqueFactorizationMonoid.of_isLocalization
      (Submonoid.powers (Polynomial.X : Polynomial (LaurentPolynomial ℂ)))
      (LaurentPolynomial (LaurentPolynomial ℂ))
  exact ((curry ℂ).symm : LaurentPolynomial (LaurentPolynomial ℂ) ≃+* LaurentTwo ℂ).toMulEquiv
    |>.uniqueFactorizationMonoid h2

/-! ### The units -/

variable {R : Type*} [CommRing R]

/-- Monomials are units of `R[T₁^±, T₂^±]`.  Paper §0.3. -/
theorem isUnit_mono (u : ℤ × ℤ) : IsUnit (mono u : LaurentTwo R) :=
  isUnit_iff_exists_inv.mpr ⟨mono (-u), by rw [mono_mul_mono, add_neg_cancel, mono_zero]⟩

/-- A non-zero monomial `c T^u` is a unit of `ℂ[T₁^±, T₂^±]`.  Paper §0.3. -/
theorem isUnit_single (u : ℤ × ℤ) {c : ℂ} (hc : c ≠ 0) :
    IsUnit (AddMonoidAlgebra.single u c : LaurentTwo ℂ) := by
  refine isUnit_iff_exists_inv.mpr ⟨AddMonoidAlgebra.single (-u) c⁻¹, ?_⟩
  rw [AddMonoidAlgebra.single_mul_single, add_neg_cancel, mul_inv_cancel₀ hc,
    ← AddMonoidAlgebra.one_def]

/-- The units of `ℂ[T₁^±, T₂^±]` are exactly the monomials `c T^u` with `c ≠ 0`.
Paper §0.3, used in Lemma 2.4(d) to compare supports. -/
theorem isUnit_iff_mono (f : LaurentTwo ℂ) :
    IsUnit f ↔ ∃ (c : ℂ) (u : ℤ × ℤ), c ≠ 0 ∧ f = AddMonoidAlgebra.single u c := by
  classical
  constructor
  · intro hf
    obtain ⟨g, hg⟩ := isUnit_iff_exists_inv.mp hf
    have hf0 : f ≠ 0 := by rintro rfl; rw [zero_mul] at hg; exact zero_ne_one hg
    have hg0 : g ≠ 0 := by rintro rfl; rw [mul_zero] at hg; exact zero_ne_one hg
    have hA : f.coeff.support.Nonempty :=
      Finsupp.support_nonempty_iff.mpr fun h => hf0 (AddMonoidAlgebra.coeff_eq_zero.mp h)
    have hB : g.coeff.support.Nonempty :=
      Finsupp.support_nonempty_iff.mpr fun h => hg0 (AddMonoidAlgebra.coeff_eq_zero.mp h)
    have hcard : f.coeff.support.card = 1 := by
      by_contra hne
      have hApos : 0 < f.coeff.support.card := Finset.card_pos.mpr hA
      have hBpos : 0 < g.coeff.support.card := Finset.card_pos.mpr hB
      have hlt : 1 < f.coeff.support.card * g.coeff.support.card := by
        have h2 : 2 ≤ f.coeff.support.card := by omega
        calc 1 < 2 * 1 := by norm_num
          _ ≤ f.coeff.support.card * g.coeff.support.card := Nat.mul_le_mul h2 hBpos
      obtain ⟨p₁, hp₁, p₂, hp₂, hne12, hu₁, hu₂⟩ :=
        TwoUniqueSums.uniqueAdd_of_one_lt_card hlt
      rw [Finset.mem_product] at hp₁ hp₂
      have hc₁ : (f * g).coeff (p₁.1 + p₁.2) ≠ 0 := by
        rw [AddMonoidAlgebra.coeff_mul_add_of_uniqueAdd hu₁]
        exact mul_ne_zero (Finsupp.mem_support_iff.mp hp₁.1) (Finsupp.mem_support_iff.mp hp₁.2)
      have hc₂ : (f * g).coeff (p₂.1 + p₂.2) ≠ 0 := by
        rw [AddMonoidAlgebra.coeff_mul_add_of_uniqueAdd hu₂]
        exact mul_ne_zero (Finsupp.mem_support_iff.mp hp₂.1) (Finsupp.mem_support_iff.mp hp₂.2)
      rw [hg] at hc₁ hc₂
      have e₁ : p₁.1 + p₁.2 = 0 := by
        by_contra hz
        exact hc₁ (by simp [AddMonoidAlgebra.one_def, Ne.symm hz])
      have e₂ : p₂.1 + p₂.2 = 0 := by
        by_contra hz
        exact hc₂ (by simp [AddMonoidAlgebra.one_def, Ne.symm hz])
      have heq := hu₁ hp₂.1 hp₂.2 (by rw [e₁, e₂])
      exact hne12 (Prod.ext heq.1 heq.2).symm
    obtain ⟨a, ha, hfa⟩ := Finsupp.card_support_eq_one.mp hcard
    exact ⟨f.coeff a, a, ha, AddMonoidAlgebra.coeff_injective hfa⟩
  · rintro ⟨c, u, hc, rfl⟩
    exact isUnit_single u hc

/-! ### Primes of the form `T^v - λ` -/

/-- The coefficient of `T^a - c` at `a`, for `a ≠ 0`. -/
private theorem coeff_mono_sub_const_self {a : ℤ × ℤ} (ha : a ≠ 0) (c : R) :
    (mono a - AddMonoidAlgebra.single (0 : ℤ × ℤ) c : LaurentTwo R).coeff a = 1 := by
  classical
  simp [mono, Ne.symm ha]

/-- The coefficient of `T^a - c` at `0`, for `a ≠ 0`. -/
private theorem coeff_mono_sub_const_zero {a : ℤ × ℤ} (ha : a ≠ 0) (c : R) :
    (mono a - AddMonoidAlgebra.single (0 : ℤ × ℤ) c : LaurentTwo R).coeff 0 = -c := by
  classical
  simp [mono, ha]

/-- `T^w - c` is not a unit when `w ≠ 0` and `c ≠ 0`: its support is `{w, 0}`, which has two
elements, whereas the units are the monomials (`isUnit_iff_mono`).  Paper Lemma 2.4(d). -/
theorem not_isUnit_mono_sub_const {w : ℤ × ℤ} (hw : w ≠ 0) {c : ℂ} (hc : c ≠ 0) :
    ¬ IsUnit (mono w - AddMonoidAlgebra.single (0 : ℤ × ℤ) c : LaurentTwo ℂ) := by
  classical
  rw [isUnit_iff_mono]
  rintro ⟨e, y, -, hy⟩
  have h1 : (mono w - AddMonoidAlgebra.single (0 : ℤ × ℤ) c : LaurentTwo ℂ).coeff w = 1 :=
    coeff_mono_sub_const_self hw c
  have h2 : (mono w - AddMonoidAlgebra.single (0 : ℤ × ℤ) c : LaurentTwo ℂ).coeff 0 = -c :=
    coeff_mono_sub_const_zero hw c
  rw [hy] at h1 h2
  have hyw : y = w := by
    by_contra hne
    rw [AddMonoidAlgebra.coeff_single, Finsupp.single_eq_of_ne' hne] at h1
    exact zero_ne_one h1
  have hy0 : y = 0 := by
    by_contra hne
    rw [AddMonoidAlgebra.coeff_single, Finsupp.single_eq_of_ne' hne] at h2
    exact hc (neg_eq_zero.mp h2.symm)
  exact hw (hyw.symm.trans hy0)

/-- The unimodular substitution attached to a basis `(v, u)` of `ℤ²` with `det v u = 1`:
`(s, t) ↦ s v + t u`.  Paper §2.1, §2.2. -/
def basisAddEquiv {v u : ℤ × ℤ} (h : det v u = 1) : (ℤ × ℤ) ≃+ (ℤ × ℤ) where
  toFun st := st.1 • v + st.2 • u
  invFun z := (det z u, det v z)
  left_inv st := by
    have h1 : det (st.1 • v + st.2 • u) u = st.1 := by
      simp only [det, Prod.smul_def, Prod.fst_add, Prod.snd_add, smul_eq_mul] at *
      linear_combination st.1 * h
    have h2 : det v (st.1 • v + st.2 • u) = st.2 := by
      simp only [det, Prod.smul_def, Prod.fst_add, Prod.snd_add, smul_eq_mul] at *
      linear_combination st.2 * h
    exact Prod.ext h1 h2
  right_inv z := (eq_smul_add_smul h z).symm
  map_add' st st' := by
    simp only [Prod.fst_add, Prod.snd_add, add_smul]
    abel

@[simp] theorem basisAddEquiv_apply {v u : ℤ × ℤ} (h : det v u = 1) (st : ℤ × ℤ) :
    basisAddEquiv h st = st.1 • v + st.2 • u := rfl

/-- A prime of `S[T]` stays prime in the Laurent ring `S[T^±]`, provided it does not become a
unit: `S[T^±]` is a localisation of `S[T]`.  (`Submonoid.LocalizationMap.map_prime`.) -/
private theorem prime_toLaurent {S : Type*} [CommRing S] [IsDomain S] {p : Polynomial S}
    (hp : Prime p) (hnu : ¬ IsUnit (Polynomial.toLaurent p : LaurentPolynomial S)) :
    Prime (Polynomial.toLaurent p : LaurentPolynomial S) := by
  have h0 : (Polynomial.toLaurent p : LaurentPolynomial S) ≠ 0 :=
    Polynomial.toLaurent_ne_zero.mpr hp.ne_zero
  exact (IsLocalization.toLocalizationMap
    (Submonoid.powers (Polynomial.X : Polynomial S)) (LaurentPolynomial S)).map_prime hp h0 hnu

/-- `T^{v} - λ` is prime for `λ ≠ 0` and `v ≠ 0` primitive: under the automorphism
`X = T^v`, `Y = T^u` of the Laurent ring one has `ℂ[X^±, Y^±]/(X - λ) ≅ ℂ[Y^±]`, an integral
domain.  Paper Lemma 2.4(d). -/
theorem prime_mono_sub_const {v : ℤ × ℤ} (hv : Primitive v) {lam : ℂ} (hlam : lam ≠ 0) :
    Prime (mono v - AddMonoidAlgebra.single (0 : ℤ × ℤ) lam) := by
  obtain ⟨u, hu⟩ := hv.exists_dual
  have h10 : ((1 : ℤ), (0 : ℤ)) ≠ (0 : ℤ × ℤ) := by
    intro hh; exact one_ne_zero (congrArg Prod.fst hh)
  -- the model prime `T₁ - λ`
  have hprime₀ : Prime (mono ((1 : ℤ), (0 : ℤ))
      - AddMonoidAlgebra.single (0 : ℤ × ℤ) lam : LaurentTwo ℂ) := by
    have hnu := not_isUnit_mono_sub_const h10 hlam
    have hc : curry ℂ (mono ((1 : ℤ), (0 : ℤ))
          - AddMonoidAlgebra.single (0 : ℤ × ℤ) lam)
        = Polynomial.toLaurent
            (Polynomial.X - Polynomial.C (LaurentPolynomial.C lam)) := by
      rw [map_sub, map_sub, Polynomial.toLaurent_X, Polynomial.toLaurent_C]
      congr 1
      · show curry ℂ (AddMonoidAlgebra.single ((1 : ℤ), (0 : ℤ)) (1 : ℂ)) = _
        rw [curry_single]; rfl
      · show curry ℂ (AddMonoidAlgebra.single ((0 : ℤ), (0 : ℤ)) lam) = _
        rw [curry_single]; rfl
    rw [← MulEquiv.prime_iff (curry ℂ), hc]
    refine prime_toLaurent (Polynomial.prime_X_sub_C _) ?_
    rw [← hc]
    intro hU
    exact hnu (by simpa using hU.map (curry ℂ).symm)
  -- transport along the unimodular substitution `(1, 0) ↦ v`
  have e1 : basisAddEquiv hu ((1 : ℤ), (0 : ℤ)) = v := by
    rw [basisAddEquiv_apply]; simp
  have e2 : basisAddEquiv hu (0 : ℤ × ℤ) = 0 := map_zero _
  have hmap : AddMonoidAlgebra.domCongr ℂ ℂ (basisAddEquiv hu)
      (mono ((1 : ℤ), (0 : ℤ)) - AddMonoidAlgebra.single (0 : ℤ × ℤ) lam)
      = mono v - AddMonoidAlgebra.single (0 : ℤ × ℤ) lam := by
    simp only [mono, map_sub, AddMonoidAlgebra.domCongr_single, e1, e2]
  rw [← hmap, MulEquiv.prime_iff]
  exact hprime₀

/-! ### Non-associate primes -/

/-- The coefficients of a difference of two monomials. -/
private theorem coeff_single_sub_single (a b : ℤ × ℤ) (c e : R) (z : ℤ × ℤ) :
    (AddMonoidAlgebra.single a c - AddMonoidAlgebra.single b e : LaurentTwo R).coeff z
      = (if a = z then c else 0) - (if b = z then e else 0) := by
  classical
  simp [Finsupp.single_apply]

/-- Comparing supports in `(T^v - λ) ε = T^w - μ` for a unit `ε`.  Paper Lemma 2.4(d): "being
associate would force `T^{v i} - λ = c T^u (T^{v k} - μ)`, and comparing supports gives
`{0, v i} = {u, u + v k}`".  Either `u = 0`, `w = v` and `λ = μ`, or `v + w = 0`. -/
private theorem associated_cases {v w : ℤ × ℤ} (hv : v ≠ 0) (hw : w ≠ 0) {lam mu : ℂ}
    (hlam : lam ≠ 0)
    (hass : Associated (mono v - AddMonoidAlgebra.single (0 : ℤ × ℤ) lam)
      (mono w - AddMonoidAlgebra.single (0 : ℤ × ℤ) mu)) :
    (w = v ∧ lam = mu) ∨ v + w = 0 := by
  classical
  obtain ⟨ε, he⟩ := hass
  obtain ⟨d, y, hd, hdy⟩ := (isUnit_iff_mono (ε : LaurentTwo ℂ)).mp ε.isUnit
  rw [hdy, sub_mul] at he
  simp only [mono, AddMonoidAlgebra.single_mul_single, one_mul, zero_add] at he
  -- `he : T^{v+y} d - T^y (λ d) = T^w - μ`
  have hvy : v + y ≠ y := by
    intro hh
    refine hv (add_right_cancel (b := y) ?_)
    rw [zero_add]; exact hh
  have key1 : (if w = y then (1 : ℂ) else 0) - (if (0 : ℤ × ℤ) = y then mu else 0)
      = -(lam * d) := by
    rw [← coeff_single_sub_single w (0 : ℤ × ℤ) (1 : ℂ) mu y, ← he,
      coeff_single_sub_single, if_neg hvy, if_pos rfl, zero_sub]
  have key2 : (if w = v + y then (1 : ℂ) else 0) - (if (0 : ℤ × ℤ) = v + y then mu else 0)
      = d := by
    rw [← coeff_single_sub_single w (0 : ℤ × ℤ) (1 : ℂ) mu (v + y), ← he,
      coeff_single_sub_single, if_pos rfl, if_neg (Ne.symm hvy), sub_zero]
  by_cases hy : (0 : ℤ × ℤ) = y
  · subst hy
    rw [if_neg hw, if_pos rfl, zero_sub] at key1
    rw [add_zero, if_neg (Ne.symm hv), sub_zero] at key2
    by_cases hwv : w = v
    · rw [if_pos hwv] at key2
      refine Or.inl ⟨hwv, ?_⟩
      rw [← key2, mul_one] at key1
      linear_combination key1
    · rw [if_neg hwv] at key2
      exact absurd key2.symm hd
  · rw [if_neg hy, sub_zero] at key1
    by_cases hwy : w = y
    · by_cases hwvy : w = v + y
      · exfalso
        refine hv (add_right_cancel (b := y) ?_)
        rw [zero_add]
        exact (hwy.symm.trans hwvy).symm
      · rw [if_neg hwvy] at key2
        by_cases hvy0 : (0 : ℤ × ℤ) = v + y
        · exact Or.inr (by rw [hwy]; exact hvy0.symm)
        · rw [if_neg hvy0, sub_zero] at key2
          exact absurd key2.symm hd
    · rw [if_neg hwy] at key1
      exact absurd (neg_eq_zero.mp key1.symm) (mul_ne_zero hlam hd)

set_option linter.unusedVariables false in
/-- Primes coming from non-parallel directions are non-associate.  Paper Lemma 2.4(d):
being associate would force `T^{v i} - λ = c T^u (T^{v k} - μ)`, and comparing supports gives
`{0, v i} = {u, u + v k}`, hence `v i = ± v k`. -/
theorem not_associated_of_det_ne_zero {v w : ℤ × ℤ} (hvw : det v w ≠ 0) {lam mu : ℂ}
    (hlam : lam ≠ 0) (hmu : mu ≠ 0) :
    ¬ Associated (mono v - AddMonoidAlgebra.single (0 : ℤ × ℤ) lam)
      (mono w - AddMonoidAlgebra.single (0 : ℤ × ℤ) mu) := by
  have hv : v ≠ 0 := by
    intro h
    refine hvw ?_
    rw [h]
    show (0 : ℤ) * w.2 - (0 : ℤ) * w.1 = 0
    ring
  have hw : w ≠ 0 := by
    intro h
    refine hvw ?_
    rw [h]
    show v.1 * (0 : ℤ) - v.2 * (0 : ℤ) = 0
    ring
  intro hass
  rcases associated_cases hv hw hlam hass with ⟨hwv, -⟩ | hvw0
  · rw [hwv] at hvw; exact hvw (det_self v)
  · have hwv : w = -v := by
      rw [eq_neg_iff_add_eq_zero, add_comm]; exact hvw0
    refine hvw ?_
    rw [hwv]
    show v.1 * (-v.2) - v.2 * (-v.1) = 0
    ring

set_option linter.unusedVariables false in
/-- Primes coming from the same direction with distinct eigenvalues are non-associate.
Paper Lemma 2.4(d). -/
theorem not_associated_of_ne {v : ℤ × ℤ} (hv : v ≠ 0) {lam mu : ℂ}
    (hlam : lam ≠ 0) (hmu : mu ≠ 0) (h : lam ≠ mu) :
    ¬ Associated (mono v - AddMonoidAlgebra.single (0 : ℤ × ℤ) lam)
      (mono v - AddMonoidAlgebra.single (0 : ℤ × ℤ) mu) := by
  intro hass
  rcases associated_cases hv hv hlam hass with ⟨-, hlm⟩ | hvv
  · exact h hlm
  · have h1 : v.1 + v.1 = 0 := congrArg Prod.fst hvv
    have h2 : v.2 + v.2 = 0 := congrArg Prod.snd hvv
    exact hv (Prod.ext (show v.1 = (0 : ℤ) by omega) (show v.2 = (0 : ℤ) by omega))

/-! ### Assembling divisibilities -/

/-- In a unique factorisation domain, pairwise non-associate primes each dividing `f` have
their product dividing `f`.  Paper Lemma 2.4(d), the "assembling" step. -/
theorem prod_dvd_of_pairwise_not_associated {ι : Type*} (s : Finset ι) (q : ι → LaurentTwo ℂ)
    (hq : ∀ i ∈ s, Prime (q i))
    (hpair : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ¬ Associated (q i) (q j))
    {f : LaurentTwo ℂ} (hdvd : ∀ i ∈ s, q i ∣ f) :
    (∏ i ∈ s, q i) ∣ f := by
  classical
  revert hq hpair hdvd
  induction s using Finset.induction with
  | empty => intro _ _ _; simp
  | insert a s ha ih =>
    intro hq hpair hdvd
    have hmem : ∀ i ∈ s, i ∈ insert a s := fun i hi => Finset.mem_insert_of_mem hi
    have ha' : a ∈ insert a s := Finset.mem_insert_self a s
    have hrest : (∏ i ∈ s, q i) ∣ f :=
      ih (fun i hi => hq i (hmem i hi))
        (fun i hi j hj hij => hpair i (hmem i hi) j (hmem j hj) hij)
        (fun i hi => hdvd i (hmem i hi))
    have hqa : Prime (q a) := hq a ha'
    have hnot : ¬ (q a ∣ ∏ i ∈ s, q i) := by
      intro hdd
      obtain ⟨i, hi, hqi⟩ := hqa.exists_mem_finset_dvd hdd
      refine hpair a ha' i (hmem i hi) (fun hh => ha (by rw [hh]; exact hi)) ?_
      exact hqa.associated_of_dvd (hq i (hmem i hi)) hqi
    have hrel : IsRelPrime (q a) (∏ i ∈ s, q i) := by
      rw [UniqueFactorizationMonoid.isRelPrime_iff_no_prime_factors hqa.ne_zero]
      intro d hda hdprod hdp
      exact hnot ((hdp.associated_of_dvd hqa hda).symm.dvd.trans hdprod)
    rw [Finset.prod_insert ha]
    exact hrel.mul_dvd (hdvd a ha') hrest

end Nivat
