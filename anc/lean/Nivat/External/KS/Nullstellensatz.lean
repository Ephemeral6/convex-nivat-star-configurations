/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.Laurent.Basic
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Hilbert's Nullstellensatz for the two-variable Laurent ring `ℂ[X₁^±, X₂^±]`

This file transports Mathlib's Nullstellensatz for `MvPolynomial` to the ring
`Nivat.LaurentTwo ℂ = AddMonoidAlgebra ℂ (ℤ × ℤ)`, with zero loci taken in the torus
`(ℂ^*)²` rather than in `ℂ²`.

## Why it is needed

This is the "Hilbert's Nullstellensatz" ingredient listed as **Not started** in the module
docstring of `Nivat/External/KSCorollary.lean`, i.e. the input to the proof of Theorem 3.1 of
J. Kari and M. Szabados, *An algebraic geometric approach to Nivat's conjecture*
(arXiv:1605.05929; Inform. and Comput. **271** (2020), 104481).  Kari–Szabados apply it to the
annihilator ideal `Ann(c) ⊆ ℂ[X₁^±, …, X_d^±]` of a configuration, in the form

> if `f` vanishes at every common zero `Z ∈ (ℂ^*)^d` of `Ann(c)`, then `f^n ∈ Ann(c)` for some
> `n ≥ 1`.

Mathlib has only the `MvPolynomial` version
(`MvPolynomial.vanishingIdeal_zeroLocus_eq_radical`), and no multivariate Laurent ring at all
(`Mathlib.Algebra.Polynomial.Laurent` is one variable only).

## The route taken

*Not* the localisation/ideal-correspondence route.  Instead, everything is done by hand with
the ring map `Nivat.KS.toLaurent : ℂ[X₁, X₂] → ℂ[X₁^±, X₂^±]` and the observation that every
Laurent polynomial becomes a genuine polynomial after multiplication by a high power of the
monomial `X₁X₂` (`Nivat.KS.exists_toLaurent_eq`).  Given an ideal `I ⊆ ℂ[X₁^±, X₂^±]`, put
`J = toLaurent⁻¹(I)`.  If `f` vanishes on the torus zero locus of `I`, write
`toLaurent F = (X₁X₂)^N f`; then `F · X₁ · X₂` vanishes on the *whole* of the affine zero locus
of `J` in `ℂ²` (at points with a vanishing coordinate because of the extra factor `X₁X₂`, at
points of the torus because such a point lies in the torus zero locus of `I`).  Mathlib's
Nullstellensatz gives `(F X₁ X₂)^n ∈ J`, and dividing out the monomial units yields `f^n ∈ I`.

## Main definitions

* `Nivat.KS.evalHom` — evaluation `ℂ[X₁^±, X₂^±] →ₐ[ℂ] ℂ` at a point `Z ∈ (ℂ^*)²`, the point
  being recorded as an element of `ℂˣ × ℂˣ`.
* `Nivat.KS.toLaurent` — the inclusion `ℂ[X₁, X₂] → ℂ[X₁^±, X₂^±]`.
* `Nivat.KS.torusZeroLocus`, `Nivat.KS.torusVanishingIdeal` — the Galois pair between ideals of
  `ℂ[X₁^±, X₂^±]` and subsets of `(ℂ^*)²`.
* `Nivat.KS.annIdeal` — the annihilator ideal `Ann(c) = {f | f(T) c = 0}` of a complex
  configuration.

## Main results

* `Nivat.KS.exists_pow_mem_of_vanishing` — the hard direction: vanishing on
  `torusZeroLocus I` implies `f ^ n ∈ I` for some `n ≥ 1`.
* `Nivat.KS.vanishing_of_exists_pow_mem` — the easy converse.
* `Nivat.KS.torusVanishingIdeal_torusZeroLocus` — the two combined:
  `torusVanishingIdeal (torusZeroLocus I) = I.radical`.
* `Nivat.KS.exists_pow_mem_annIdeal` — the shape actually used downstream, stated directly for
  the annihilator of a configuration.

## Status

**Complete; no `sorry`.**  Restricted to two variables (`d = 2`), which is all the Convex
Nivat formalisation needs; the argument is dimension-agnostic but the ring `LaurentTwo` in this
repository is two-variable.

What this file does *not* do: it says nothing about Kari–Szabados Lemma 3 (the Frobenius /
mod-`p` argument), Lemma 4 (the root partition), or Lemmas 5–6.  Those remain the other
missing ingredients of `Nivat.KSC.exists_prodList_ann`.
-/

namespace Nivat.KS

open AddMonoidAlgebra

/-! ### Evaluation at a point of the torus `(ℂ^*)²` -/

/-- The monoid homomorphism `ℤ² → ℂˣ`, `v ↦ Z₁^{v₁} Z₂^{v₂}`. -/
noncomputable def torusUnitHom (Z : ℂˣ × ℂˣ) : Multiplicative (ℤ × ℤ) →* ℂˣ where
  toFun v := Z.1 ^ (Multiplicative.toAdd v).1 * Z.2 ^ (Multiplicative.toAdd v).2
  map_one' := by simp
  map_mul' a b := by
    simp only [toAdd_mul, Prod.fst_add, Prod.snd_add, zpow_add]
    exact mul_mul_mul_comm _ _ _ _

/-- The monoid homomorphism `ℤ² → ℂ`, `v ↦ Z₁^{v₁} Z₂^{v₂}`. -/
noncomputable def torusHom (Z : ℂˣ × ℂˣ) : Multiplicative (ℤ × ℤ) →* ℂ :=
  (Units.coeHom ℂ).comp (torusUnitHom Z)

/-- Evaluation of a two-variable Laurent polynomial at a point of `(ℂ^*)²`. -/
noncomputable def evalHom (Z : ℂˣ × ℂˣ) : LaurentTwo ℂ →ₐ[ℂ] ℂ :=
  AddMonoidAlgebra.lift ℂ ℂ (ℤ × ℤ) (torusHom Z)

@[simp] theorem evalHom_single (Z : ℂˣ × ℂˣ) (v : ℤ × ℤ) (c : ℂ) :
    evalHom Z (AddMonoidAlgebra.single v c) = c * ((Z.1 : ℂ) ^ v.1 * (Z.2 : ℂ) ^ v.2) := by
  rw [evalHom, AddMonoidAlgebra.lift_single]
  simp [torusHom, torusUnitHom, smul_eq_mul]

@[simp] theorem evalHom_mono (Z : ℂˣ × ℂˣ) (v : ℤ × ℤ) :
    evalHom Z (mono v) = (Z.1 : ℂ) ^ v.1 * (Z.2 : ℂ) ^ v.2 := by
  rw [mono, evalHom_single, one_mul]

theorem evalHom_mono_ne_zero (Z : ℂˣ × ℂˣ) (v : ℤ × ℤ) : evalHom Z (mono v) ≠ 0 := by
  rw [evalHom_mono]
  exact mul_ne_zero (zpow_ne_zero _ (Units.ne_zero _)) (zpow_ne_zero _ (Units.ne_zero _))

/-! ### Monomials are units -/

theorem isUnit_mono (v : ℤ × ℤ) : IsUnit (mono v : LaurentTwo ℂ) :=
  isUnit_iff_exists_inv.mpr ⟨mono (-v), by rw [mono_mul_mono, add_neg_cancel, mono_zero]⟩

theorem mem_of_isUnit_mul {I : Ideal (LaurentTwo ℂ)} {u a : LaurentTwo ℂ} (hu : IsUnit u)
    (h : u * a ∈ I) : a ∈ I := by
  obtain ⟨w, rfl⟩ := hu
  have h2 := I.mul_mem_left (↑w⁻¹ : LaurentTwo ℂ) h
  rwa [← mul_assoc, Units.inv_mul, one_mul] at h2

theorem mono_pow (v : ℤ × ℤ) (n : ℕ) : (mono v : LaurentTwo ℂ) ^ n = mono ((n : ℤ) • v) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ih, mono_mul_mono]
      congr 1
      push_cast
      rw [add_smul, one_smul]

theorem single_zero_mul_mono (c : ℂ) (v : ℤ × ℤ) :
    (AddMonoidAlgebra.single (0 : ℤ × ℤ) c : LaurentTwo ℂ) * mono v
      = AddMonoidAlgebra.single v c := by
  rw [mono, AddMonoidAlgebra.single_mul_single, zero_add, mul_one]

/-! ### The polynomial ring inside the Laurent ring -/

/-- The standard basis `(1,0)`, `(0,1)` of `ℤ²`. -/
def gen : Fin 2 → ℤ × ℤ := ![(1, 0), (0, 1)]

/-- The inclusion `ℂ[X₁, X₂] → ℂ[X₁^±, X₂^±]`. -/
noncomputable def toLaurent : MvPolynomial (Fin 2) ℂ →ₐ[ℂ] LaurentTwo ℂ :=
  MvPolynomial.aeval (fun i => (mono (gen i) : LaurentTwo ℂ))

@[simp] theorem toLaurent_X (i : Fin 2) : toLaurent (MvPolynomial.X i) = mono (gen i) := by
  rw [toLaurent, MvPolynomial.aeval_X]

@[simp] theorem toLaurent_C (c : ℂ) :
    toLaurent (MvPolynomial.C c) = AddMonoidAlgebra.single (0 : ℤ × ℤ) c := by
  rw [toLaurent, MvPolynomial.aeval_C]
  rfl

/-- The point of `ℂ²` underlying a point of the torus. -/
noncomputable def pt (Z : ℂˣ × ℂˣ) : Fin 2 → ℂ := ![(Z.1 : ℂ), (Z.2 : ℂ)]

theorem evalHom_toLaurent (Z : ℂˣ × ℂˣ) (F : MvPolynomial (Fin 2) ℂ) :
    evalHom Z (toLaurent F) = MvPolynomial.aeval (pt Z) F := by
  have h : (evalHom Z).comp toLaurent = MvPolynomial.aeval (pt Z) := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [gen, pt]
  exact DFunLike.congr_fun h F

/-! ### Clearing denominators -/

/-- The "denominator" monomial `(X₁ X₂)^n` of `ℂ[X₁, X₂]`. -/
noncomputable def den (n : ℕ) : MvPolynomial (Fin 2) ℂ :=
  MvPolynomial.X 0 ^ n * MvPolynomial.X 1 ^ n

theorem toLaurent_den (n : ℕ) : toLaurent (den n) = mono ((n : ℤ), (n : ℤ)) := by
  rw [den, map_mul, map_pow, map_pow, toLaurent_X, toLaurent_X, mono_pow, mono_pow,
    mono_mul_mono]
  congr 1
  simp [gen]

/-- `toLaurent` of an honest monomial `c X₁^p X₂^q`. -/
theorem toLaurent_mvMono (p q : ℕ) (c : ℂ) :
    toLaurent (MvPolynomial.C c * MvPolynomial.X 0 ^ p * MvPolynomial.X 1 ^ q)
      = AddMonoidAlgebra.single ((p : ℤ), (q : ℤ)) c := by
  rw [map_mul, map_mul, map_pow, map_pow, toLaurent_C, toLaurent_X, toLaurent_X, mono_pow,
    mono_pow, mul_assoc, mono_mul_mono, single_zero_mul_mono]
  congr 1
  simp [gen]

/-- **Every Laurent polynomial becomes a polynomial after multiplying by a monomial.**
For `f ∈ ℂ[X₁^±, X₂^±]` there are `N : ℕ` and `F ∈ ℂ[X₁, X₂]` with `F = (X₁X₂)^N f`. -/
theorem exists_toLaurent_eq (f : LaurentTwo ℂ) :
    ∃ (N : ℕ) (F : MvPolynomial (Fin 2) ℂ),
      toLaurent F = mono ((N : ℤ), (N : ℤ)) * f := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => exact ⟨0, 0, by simp⟩
  | add f g hf hg =>
      obtain ⟨N₁, F₁, h₁⟩ := hf
      obtain ⟨N₂, F₂, h₂⟩ := hg
      refine ⟨N₁ + N₂, den N₂ * F₁ + den N₁ * F₂, ?_⟩
      rw [map_add, map_mul, map_mul, toLaurent_den, toLaurent_den, h₁, h₂,
        ← mul_assoc, ← mul_assoc, mono_mul_mono, mono_mul_mono, mul_add]
      have hsum : ((N₂ : ℤ), (N₂ : ℤ)) + ((N₁ : ℤ), (N₁ : ℤ))
          = (((N₁ + N₂ : ℕ) : ℤ), ((N₁ + N₂ : ℕ) : ℤ)) := by
        refine Prod.ext ?_ ?_ <;> simp only [Prod.fst_add, Prod.snd_add] <;> omega
      have hsum' : ((N₁ : ℤ), (N₁ : ℤ)) + ((N₂ : ℤ), (N₂ : ℤ))
          = (((N₁ + N₂ : ℕ) : ℤ), ((N₁ + N₂ : ℕ) : ℤ)) := by
        refine Prod.ext ?_ ?_ <;> simp only [Prod.fst_add, Prod.snd_add] <;> omega
      rw [hsum, hsum']
  | single v c =>
      classical
      refine ⟨(-v.1).toNat ⊔ (-v.2).toNat, ?_⟩
      set N : ℕ := (-v.1).toNat ⊔ (-v.2).toNat with hN
      have h1 : (0 : ℤ) ≤ (N : ℤ) + v.1 := by
        have : ((-v.1).toNat : ℤ) ≤ (N : ℤ) := by
          exact_mod_cast Nat.le_max_left _ _
        have h2 : -v.1 ≤ ((-v.1).toNat : ℤ) := Int.self_le_toNat _
        omega
      have h2 : (0 : ℤ) ≤ (N : ℤ) + v.2 := by
        have : ((-v.2).toNat : ℤ) ≤ (N : ℤ) := by
          exact_mod_cast Nat.le_max_right _ _
        have h3 : -v.2 ≤ ((-v.2).toNat : ℤ) := Int.self_le_toNat _
        omega
      refine ⟨MvPolynomial.C c * MvPolynomial.X 0 ^ ((N : ℤ) + v.1).toNat
        * MvPolynomial.X 1 ^ ((N : ℤ) + v.2).toNat, ?_⟩
      rw [toLaurent_mvMono, mono, AddMonoidAlgebra.single_mul_single, one_mul]
      congr 1
      refine Prod.ext ?_ ?_ <;> simp only [Prod.fst_add, Prod.snd_add] <;> omega

/-! ### Zero loci and vanishing ideals on the torus -/

/-- The common zero set in `(ℂ^*)²` of an ideal of `ℂ[X₁^±, X₂^±]`. -/
def torusZeroLocus (I : Ideal (LaurentTwo ℂ)) : Set (ℂˣ × ℂˣ) :=
  {Z | ∀ g ∈ I, evalHom Z g = 0}

@[simp] theorem mem_torusZeroLocus_iff {I : Ideal (LaurentTwo ℂ)} {Z : ℂˣ × ℂˣ} :
    Z ∈ torusZeroLocus I ↔ ∀ g ∈ I, evalHom Z g = 0 := Iff.rfl

/-- The ideal of Laurent polynomials vanishing on a subset of `(ℂ^*)²`. -/
def torusVanishingIdeal (V : Set (ℂˣ × ℂˣ)) : Ideal (LaurentTwo ℂ) where
  carrier := {f | ∀ Z ∈ V, evalHom Z f = 0}
  zero_mem' _ _ := map_zero _
  add_mem' {f g} hf hg Z hZ := by simp only [map_add, hf Z hZ, hg Z hZ, add_zero]
  smul_mem' f g hg Z hZ := by simp only [smul_eq_mul, map_mul, hg Z hZ, mul_zero]

@[simp] theorem mem_torusVanishingIdeal_iff {V : Set (ℂˣ × ℂˣ)} {f : LaurentTwo ℂ} :
    f ∈ torusVanishingIdeal V ↔ ∀ Z ∈ V, evalHom Z f = 0 := Iff.rfl

/-! ### The Nullstellensatz -/

/-- **The hard direction.**  If `f ∈ ℂ[X₁^±, X₂^±]` vanishes at every common zero in `(ℂ^*)²`
of the ideal `I`, then some positive power of `f` lies in `I`. -/
theorem exists_pow_mem_of_vanishing {I : Ideal (LaurentTwo ℂ)} {f : LaurentTwo ℂ}
    (hf : ∀ Z ∈ torusZeroLocus I, evalHom Z f = 0) :
    ∃ n : ℕ, 0 < n ∧ f ^ n ∈ I := by
  classical
  -- The pullback of `I` to the polynomial ring.
  set J : Ideal (MvPolynomial (Fin 2) ℂ) := Ideal.comap toLaurent.toRingHom I with hJ
  have hmemJ : ∀ G : MvPolynomial (Fin 2) ℂ, G ∈ J ↔ toLaurent G ∈ I := fun G => Iff.rfl
  obtain ⟨N, F, hF⟩ := exists_toLaurent_eq f
  -- `F · X₁ · X₂` vanishes on the whole of `zeroLocus J ⊆ ℂ²`.
  set G : MvPolynomial (Fin 2) ℂ := F * MvPolynomial.X 0 * MvPolynomial.X 1 with hG
  have hGvan : G ∈ MvPolynomial.vanishingIdeal ℂ (MvPolynomial.zeroLocus ℂ J) := by
    rw [MvPolynomial.mem_vanishingIdeal_iff]
    intro x hx
    by_cases h0 : x 0 = 0
    · simp [hG, h0]
    by_cases h1 : x 1 = 0
    · simp [hG, h1]
    -- Both coordinates non-zero: `x` is a point of the torus in `torusZeroLocus I`.
    set Z : ℂˣ × ℂˣ := (Units.mk0 (x 0) h0, Units.mk0 (x 1) h1) with hZ
    have hpt : pt Z = x := by
      funext i
      fin_cases i <;> simp [pt, hZ]
    have hZmem : Z ∈ torusZeroLocus I := by
      intro g hg
      obtain ⟨M, Gg, hGg⟩ := exists_toLaurent_eq g
      have hGgJ : Gg ∈ J := by
        rw [hmemJ, hGg]
        exact I.mul_mem_left _ hg
      have hval := hx Gg hGgJ
      rw [← hpt, ← evalHom_toLaurent, hGg, map_mul] at hval
      exact (mul_eq_zero.mp hval).resolve_left (evalHom_mono_ne_zero Z _)
    have hFz : MvPolynomial.aeval (pt Z) F = 0 := by
      rw [← evalHom_toLaurent, hF, map_mul, hf Z hZmem, mul_zero]
    rw [hpt] at hFz
    simp only [hG, map_mul, hFz, zero_mul]
  -- Nullstellensatz in the polynomial ring.
  rw [MvPolynomial.vanishingIdeal_zeroLocus_eq_radical] at hGvan
  obtain ⟨n, hn⟩ := hGvan
  rw [hmemJ, map_pow, hG, map_mul, map_mul, hF, toLaurent_X, toLaurent_X] at hn
  -- Strip the monomial factors, which are units.
  have hrewrite : (mono ((N : ℤ), (N : ℤ)) * f * mono (gen 0) * mono (gen 1) : LaurentTwo ℂ) ^ n
      = (mono ((N : ℤ), (N : ℤ)) * mono (gen 0) * mono (gen 1)) ^ n * f ^ n := by
    rw [← mul_pow]
    ring_nf
  rw [hrewrite] at hn
  refine ⟨n + 1, Nat.succ_pos n, ?_⟩
  rw [pow_succ]
  exact I.mul_mem_right f
    (mem_of_isUnit_mul
      ((((isUnit_mono _).mul (isUnit_mono _)).mul (isUnit_mono _)).pow n) hn)

/-- **The easy direction.**  If some positive power of `f` lies in `I`, then `f` vanishes at
every common zero of `I` in `(ℂ^*)²`. -/
theorem vanishing_of_exists_pow_mem {I : Ideal (LaurentTwo ℂ)} {f : LaurentTwo ℂ}
    (h : ∃ n : ℕ, 0 < n ∧ f ^ n ∈ I) : ∀ Z ∈ torusZeroLocus I, evalHom Z f = 0 := by
  rintro Z hZ
  obtain ⟨n, hn, hfn⟩ := h
  have hval := hZ _ hfn
  rw [map_pow] at hval
  exact pow_eq_zero_iff hn.ne' |>.mp hval

/-- **Hilbert's Nullstellensatz for `ℂ[X₁^±, X₂^±]`.**  For an ideal `I` of the two-variable
Laurent ring, the ideal of Laurent polynomials vanishing on the common zero set of `I` inside
the torus `(ℂ^*)²` is the radical of `I`. -/
theorem torusVanishingIdeal_torusZeroLocus (I : Ideal (LaurentTwo ℂ)) :
    torusVanishingIdeal (torusZeroLocus I) = I.radical := by
  ext f
  rw [mem_torusVanishingIdeal_iff, Ideal.mem_radical_iff]
  constructor
  · intro h
    obtain ⟨n, _, hn⟩ := exists_pow_mem_of_vanishing h
    exact ⟨n, hn⟩
  · rintro ⟨n, hn⟩
    exact vanishing_of_exists_pow_mem ⟨n + 1, Nat.succ_pos n, by
      rw [pow_succ]; exact I.mul_mem_right f hn⟩

/-! ### The form used downstream: the annihilator of a configuration

Kari–Szabados apply the Nullstellensatz to the annihilator ideal `Ann(c)` of a configuration
`c : ℤ² → ℂ`.  For an integral configuration `ξ : ℤ² → ℤ` the relevant ideal is
`annIdeal (fun z => (ξ z : ℂ))`. -/

/-- The annihilator ideal `Ann(c) = {f ∈ ℂ[X₁^±, X₂^±] | f(T) c = 0}` of a complex
configuration.  Kari–Szabados §3. -/
def annIdeal (c : Config ℂ) : Ideal (LaurentTwo ℂ) where
  carrier := {f | act f c = 0}
  zero_mem' := act_zero_left c
  add_mem' {f g} hf hg := by
    have hf' : act f c = 0 := hf
    have hg' : act g c = 0 := hg
    show act (f + g) c = 0
    rw [act_add_left, hf', hg', add_zero]
  smul_mem' g f hf := by
    have hf' : act f c = 0 := hf
    show act (g • f) c = 0
    rw [smul_eq_mul, act_mul, hf', act_zero_right]

@[simp] theorem mem_annIdeal_iff {c : Config ℂ} {f : LaurentTwo ℂ} :
    f ∈ annIdeal c ↔ act f c = 0 := Iff.rfl

/-- **The statement needed for Kari–Szabados Theorem 3.1.**  If `f ∈ ℂ[X₁^±, X₂^±]` vanishes at
every point of the torus `(ℂ^*)²` at which all of `Ann(c)` vanishes, then `f^n ∈ Ann(c)` for
some `n ≥ 1`, i.e. `f(T)^n c = 0`. -/
theorem exists_pow_mem_annIdeal {c : Config ℂ} {f : LaurentTwo ℂ}
    (hf : ∀ Z : ℂˣ × ℂˣ, (∀ g : LaurentTwo ℂ, act g c = 0 → evalHom Z g = 0) →
      evalHom Z f = 0) :
    ∃ n : ℕ, 0 < n ∧ act (f ^ n) c = 0 :=
  exists_pow_mem_of_vanishing (I := annIdeal c) (f := f) fun Z hZ => hf Z fun g hg => hZ g hg

/-- The converse of `exists_pow_mem_annIdeal`. -/
theorem vanishing_of_exists_pow_mem_annIdeal {c : Config ℂ} {f : LaurentTwo ℂ}
    (h : ∃ n : ℕ, 0 < n ∧ act (f ^ n) c = 0) :
    ∀ Z : ℂˣ × ℂˣ, (∀ g : LaurentTwo ℂ, act g c = 0 → evalHom Z g = 0) → evalHom Z f = 0 :=
  fun Z hZ => vanishing_of_exists_pow_mem (I := annIdeal c) h Z fun g hg => hZ g hg

end Nivat.KS
