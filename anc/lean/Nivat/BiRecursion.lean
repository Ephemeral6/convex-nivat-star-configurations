/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.Witness
import Nivat.Laurent.SublatticeBasis
import Nivat.Laurent.QuotientGlue
import Nivat.Laurent.MonoShift
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# §5. The bi-recursion and the quotient algebra

Formalisation of §5 of *The Convex Nivat Conjecture* (Pan).

The two-point function `J(d, z) = D_z(ψ(z) ψ(z + d))` satisfies two independent recursions
driven by `A` — one in `d` alone, one in `d` and `z` simultaneously (Lemma 5.1).  Transforming
in `z` turns these into the statement that the `K`-linear functional `L(Y^d) = Ĵ(d; X)` kills
the ideal `(a, c) ⊆ R = K[Y₁^±, Y₂^±]`, where `K = ℂ(X₁, X₂)`, `a = A(Y)` and `c = A(X/Y)`.
The quotient `R/(a, c)` is spanned by the monomials `Y^d` with `d ∈ (Z - Z) ∩ ℤ²`
(Lemma 5.2), so some such `d` has `J(d, ·) ≠ 0` (Proposition 5.3).

## Main definitions

* `Nivat.FF` — the field `K = ℂ(X₁, X₂)`.
* `Nivat.Xmono` — the monomial `X^u ∈ K`.
* `Nivat.StarConfig.aElt`, `Nivat.StarConfig.cElt` — `a = A(Y)` and `c = A(X/Y)` in
  `R = K[Y^±]`.
* `Nivat.StarConfig.Jhat` — the Laurent transform `Ĵ(d; X) = ∑_z J(d, z) X^{-z}`.

## Main results

* `Nivat.StarConfig.Aop_Jfun_shift`, `Nivat.StarConfig.Aop_Jfun_mixed` — **Lemma 5.1**.
* `Nivat.StarConfig.span_quotient` — **Lemma 5.2**.
* `Nivat.StarConfig.exists_witness` — **Proposition 5.3**.

## Status

Skeleton; proofs are line D.
-/

namespace Nivat

open Finset
open scoped Pointwise

/-- The field `K = ℂ(X₁, X₂)` of rational functions in two variables.  Paper §5.2. -/
abbrev FF : Type := FractionRing (MvPolynomial (Fin 2) ℂ)

/-- The image of `ℂ` in `K`. -/
noncomputable def cToFF : ℂ →+* FF :=
  (algebraMap (MvPolynomial (Fin 2) ℂ) FF).comp (MvPolynomial.C : ℂ →+* MvPolynomial (Fin 2) ℂ)

/-- The generators `X₁, X₂ ∈ K`. -/
noncomputable def Xgen (k : Fin 2) : FF :=
  algebraMap (MvPolynomial (Fin 2) ℂ) FF (MvPolynomial.X k)

/-- The monomial `X^u = X₁^{u₁} X₂^{u₂} ∈ K`, for `u ∈ ℤ²`.  Paper §5.2. -/
noncomputable def Xmono (u : ℤ × ℤ) : FF := Xgen 0 ^ u.1 * Xgen 1 ^ u.2

theorem Xgen_ne_zero (k : Fin 2) : Xgen k ≠ 0 := by
  rw [Xgen, Ne, IsFractionRing.to_map_eq_zero_iff]
  exact MvPolynomial.X_ne_zero k

theorem Xmono_ne_zero (u : ℤ × ℤ) : Xmono u ≠ 0 :=
  mul_ne_zero (zpow_ne_zero _ (Xgen_ne_zero 0)) (zpow_ne_zero _ (Xgen_ne_zero 1))

theorem Xmono_add (u w : ℤ × ℤ) : Xmono (u + w) = Xmono u * Xmono w := by
  simp only [Xmono, Prod.fst_add, Prod.snd_add, zpow_add₀ (Xgen_ne_zero 0),
    zpow_add₀ (Xgen_ne_zero 1)]
  ring

@[simp] theorem Xmono_zero : Xmono 0 = 1 := by simp [Xmono]

/-- `X^u` is transcendental over `ℂ` for `u ≠ 0`; equivalently, it is not in the image of `ℂ`.
This is the arithmetic input of Step 1 of Lemma 5.2. -/
theorem Xmono_not_mem_range {u : ℤ × ℤ} (hu : u ≠ 0) : Xmono u ∉ Set.range cToFF := by
  classical
  rintro ⟨c, hc⟩
  -- Clear denominators: pick nonneg naturals `a, b` and `n1, n2` with `n1 = u.1 + a`,
  -- `n2 = u.2 + b` as integers, so that multiplying the hypothesis by `X0^a * X1^b`
  -- turns the `zpow` equation into a genuine equation of Laurent-free polynomials.
  set a : ℕ := u.1.natAbs with ha_def
  set b : ℕ := u.2.natAbs with hb_def
  have hnn1 : (0 : ℤ) ≤ u.1 + (a : ℤ) := by rw [ha_def]; omega
  have hnn2 : (0 : ℤ) ≤ u.2 + (b : ℤ) := by rw [hb_def]; omega
  set n1 : ℕ := (u.1 + (a : ℤ)).toNat with hn1_def
  set n2 : ℕ := (u.2 + (b : ℤ)).toNat with hn2_def
  have hn1 : (n1 : ℤ) = u.1 + (a : ℤ) := Int.toNat_of_nonneg hnn1
  have hn2 : (n2 : ℤ) = u.2 + (b : ℤ) := Int.toNat_of_nonneg hnn2
  set ι : MvPolynomial (Fin 2) ℂ →+* FF := algebraMap (MvPolynomial (Fin 2) ℂ) FF with hι_def
  have hXgen : ∀ k, Xgen k = ι (MvPolynomial.X k) := fun _ => rfl
  have hcToFF : ∀ x : ℂ, cToFF x = ι (MvPolynomial.C x) := fun _ => rfl
  have hFF : ι (MvPolynomial.X 0) ^ n1 * ι (MvPolynomial.X 1) ^ n2
      = ι (MvPolynomial.C c) * ι (MvPolynomial.X 0) ^ a * ι (MvPolynomial.X 1) ^ b := by
    have e1 : Xgen 0 ^ n1 = Xgen 0 ^ u.1 * Xgen 0 ^ a := by
      rw [← zpow_natCast (Xgen 0) n1, hn1, zpow_add₀ (Xgen_ne_zero 0), zpow_natCast]
    have e2 : Xgen 1 ^ n2 = Xgen 1 ^ u.2 * Xgen 1 ^ b := by
      rw [← zpow_natCast (Xgen 1) n2, hn2, zpow_add₀ (Xgen_ne_zero 1), zpow_natCast]
    rw [← hXgen 0, ← hXgen 1, ← hcToFF c, hc, Xmono, e1, e2]
    ring
  simp only [← map_pow, ← map_mul] at hFF
  have hpoly : (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℂ) ^ n1 * MvPolynomial.X 1 ^ n2
      = MvPolynomial.C c * MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b :=
    IsFractionRing.injective (MvPolynomial (Fin 2) ℂ) FF hFF
  have hor : u.1 ≠ 0 ∨ u.2 ≠ 0 := by
    by_contra h
    push Not at h
    exact hu (Prod.ext h.1 h.2)
  rcases hor with h1 | h2
  · -- `n1 ≠ a`: evaluate `X1 ↦ 1`, `X0 ↦ Polynomial.X` and compare coefficients at `n1`.
    have hne_na : n1 ≠ a := by
      intro heq; rw [heq] at hn1; omega
    set φ : MvPolynomial (Fin 2) ℂ →+* Polynomial ℂ :=
      MvPolynomial.eval₂Hom (algebraMap ℂ (Polynomial ℂ))
        (fun i : Fin 2 => if i = 0 then Polynomial.X else 1) with hφ_def
    have hφ0 : φ (MvPolynomial.X 0) = Polynomial.X := by
      rw [hφ_def, MvPolynomial.eval₂Hom_X']; simp
    have hφ1 : φ (MvPolynomial.X 1) = 1 := by
      rw [hφ_def, MvPolynomial.eval₂Hom_X']; simp
    have hφC : φ (MvPolynomial.C c) = Polynomial.C c := by
      rw [hφ_def, MvPolynomial.eval₂Hom_C, ← Polynomial.algebraMap_eq]
    have h' := congrArg φ hpoly
    simp only [map_mul, map_pow, hφ0, hφ1, hφC, one_pow, mul_one] at h'
    have hcoeff := congrArg (fun p => Polynomial.coeff p n1) h'
    simp only [Polynomial.coeff_X_pow, Polynomial.coeff_C_mul] at hcoeff
    rw [if_neg hne_na, mul_zero] at hcoeff
    exact one_ne_zero hcoeff
  · -- symmetric case, `n2 ≠ b`: evaluate `X0 ↦ 1`, `X1 ↦ Polynomial.X`.
    have hne_nb : n2 ≠ b := by
      intro heq; rw [heq] at hn2; omega
    set φ : MvPolynomial (Fin 2) ℂ →+* Polynomial ℂ :=
      MvPolynomial.eval₂Hom (algebraMap ℂ (Polynomial ℂ))
        (fun i : Fin 2 => if i = 1 then Polynomial.X else 1) with hφ_def
    have hφ0 : φ (MvPolynomial.X 0) = 1 := by
      rw [hφ_def, MvPolynomial.eval₂Hom_X']; simp
    have hφ1 : φ (MvPolynomial.X 1) = Polynomial.X := by
      rw [hφ_def, MvPolynomial.eval₂Hom_X']; simp
    have hφC : φ (MvPolynomial.C c) = Polynomial.C c := by
      rw [hφ_def, MvPolynomial.eval₂Hom_C, ← Polynomial.algebraMap_eq]
    have h' := congrArg φ hpoly
    simp only [map_mul, map_pow, hφ0, hφ1, hφC, one_pow, mul_one, one_mul] at h'
    have hcoeff := congrArg (fun p => Polynomial.coeff p n2) h'
    simp only [Polynomial.coeff_X_pow, Polynomial.coeff_C_mul] at hcoeff
    rw [if_neg hne_nb, mul_zero] at hcoeff
    exact one_ne_zero hcoeff

/-- The base change `ℂ[T^±] → K[Y^±]` on coefficients. -/
noncomputable def toFF (f : LaurentTwo ℂ) : LaurentTwo FF :=
  AddMonoidAlgebra.ofCoeff (f.coeff.mapRange cToFF (map_zero _))

/-- The substitution `T^s ↦ X^s Y^{-s}`, sending `A(T)` to `c = A(X/Y)`.  Paper §5.2. -/
noncomputable def subXY (f : LaurentTwo ℂ) : LaurentTwo FF :=
  f.coeff.sum fun s A => AddMonoidAlgebra.single (-s) (cToFF A * Xmono s)

namespace StarConfig

variable {p m : ℕ} [Fact p.Prime] (S : StarConfig p m)

/-! ### §5.1 The bi-recursion -/

/-- Every `H_C = ∑_{i ∈ C} Hᵢ` is a period of the doubly periodic background `b_ψ`. -/
theorem sum_H_mem_Per_bpsi (C : Finset (Fin m)) : (∑ i ∈ C, S.H i) ∈ Per S.bpsi :=
  AddSubgroup.sum_mem _ fun i _ => S.H_mem_Per_bpsi i

/-- **Lemma 5.1, first identity.**  `A(T_d) J = 0`, i.e. `∑_s A_s J(d + s, z) = 0`.

Only the second observation point moves, so `A` acts on `ψ` there and turns it into `b_ψ`
(Proposition 3.3); `b_ψ` is invariant under every `H_C`, so it factors out of the expansion
(0.1) of `D`, leaving `b_ψ(z + d) · (D ψ)(z) = 0`. -/
theorem Aop_Jfun_shift (h11 : S.CaseTwo) (d z : ℤ × ℤ) :
    (S.Aop.coeff.sum fun s A => A * S.Jfun (d + s) z) = 0 := by
  classical
  -- Expand each `J(d + s, ·)` at `z` by (0.1).
  have hexp : (S.Aop.coeff.sum fun s A => A * S.Jfun (d + s) z)
      = ∑ s ∈ S.Aop.coeff.support, ∑ C ∈ univ.powerset,
          (-1 : ℂ) ^ (m - C.card) * S.psi (z + ∑ i ∈ C, S.H i)
            * (S.Aop.coeff s * S.psi (z + ∑ i ∈ C, S.H i + d + s)) := by
    rw [Finsupp.sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    have hJ : S.Jfun (d + s) z
        = ∑ C ∈ univ.powerset, (-1 : ℂ) ^ (m - C.card)
            * (S.psi (z + ∑ i ∈ C, S.H i) * S.psi (z + ∑ i ∈ C, S.H i + (d + s))) :=
      S.act_Dop_apply _ z
    rw [hJ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun C _ => ?_
    rw [show z + ∑ i ∈ C, S.H i + (d + s) = z + ∑ i ∈ C, S.H i + d + s by abel]
    ring
  rw [hexp, Finset.sum_comm]
  -- The inner sum is `(A ψ)(z + H_C + d) = b_ψ(z + H_C + d) = b_ψ(z + d)`.
  have hinner : ∀ C ∈ (univ : Finset (Fin m)).powerset,
      ∑ s ∈ S.Aop.coeff.support,
          (-1 : ℂ) ^ (m - C.card) * S.psi (z + ∑ i ∈ C, S.H i)
            * (S.Aop.coeff s * S.psi (z + ∑ i ∈ C, S.H i + d + s))
        = (-1 : ℂ) ^ (m - C.card) * S.psi (z + ∑ i ∈ C, S.H i) * S.bpsi (z + d) := by
    intro C _
    have h1 : ∑ s ∈ S.Aop.coeff.support,
        S.Aop.coeff s * S.psi (z + ∑ i ∈ C, S.H i + d + s)
          = S.bpsi (z + ∑ i ∈ C, S.H i + d) := congrFun (S.act_Aop_psi h11) _
    rw [← Finset.mul_sum, h1,
      show z + ∑ i ∈ C, S.H i + d = z + d + ∑ i ∈ C, S.H i by abel,
      Per.apply (S.sum_H_mem_Per_bpsi C) (z + d)]
  rw [Finset.sum_congr rfl hinner, ← Finset.sum_mul]
  -- What is left is `(D ψ)(z) · b_ψ(z + d)`, and `D ψ = 0` by (1.1).
  have hD : ∑ C ∈ (univ : Finset (Fin m)).powerset,
      (-1 : ℂ) ^ (m - C.card) * S.psi (z + ∑ i ∈ C, S.H i) = 0 := by
    have h0 : act S.Dop S.psi z = 0 := congrFun (S.act_Dop_psi h11) z
    rwa [S.act_Dop_apply S.psi z] at h0
  rw [hD, zero_mul]

/-- **Lemma 5.1, second identity.**  `A(T_z T_d^{-1}) J = 0`, i.e.
`∑_s A_s J(d - s, z + s) = 0`.

Here the *first* observation point moves and the second does not, so `A` turns the first `ψ`
into `b_ψ(z + H_C) = b_ψ(z)`, which factors out and leaves `b_ψ(z) · (D ψ)(z + d) = 0`. -/
theorem Aop_Jfun_mixed (h11 : S.CaseTwo) (d z : ℤ × ℤ) :
    (S.Aop.coeff.sum fun s A => A * S.Jfun (d - s) (z + s)) = 0 := by
  classical
  have hexp : (S.Aop.coeff.sum fun s A => A * S.Jfun (d - s) (z + s))
      = ∑ s ∈ S.Aop.coeff.support, ∑ C ∈ univ.powerset,
          (-1 : ℂ) ^ (m - C.card) * S.psi (z + ∑ i ∈ C, S.H i + d)
            * (S.Aop.coeff s * S.psi (z + ∑ i ∈ C, S.H i + s)) := by
    rw [Finsupp.sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    have hJ : S.Jfun (d - s) (z + s)
        = ∑ C ∈ univ.powerset, (-1 : ℂ) ^ (m - C.card)
            * (S.psi (z + s + ∑ i ∈ C, S.H i)
               * S.psi (z + s + ∑ i ∈ C, S.H i + (d - s))) :=
      S.act_Dop_apply _ (z + s)
    rw [hJ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun C _ => ?_
    rw [show z + s + ∑ i ∈ C, S.H i = z + ∑ i ∈ C, S.H i + s by abel,
      show z + ∑ i ∈ C, S.H i + s + (d - s) = z + ∑ i ∈ C, S.H i + d by abel]
    ring
  rw [hexp, Finset.sum_comm]
  have hinner : ∀ C ∈ (univ : Finset (Fin m)).powerset,
      ∑ s ∈ S.Aop.coeff.support,
          (-1 : ℂ) ^ (m - C.card) * S.psi (z + ∑ i ∈ C, S.H i + d)
            * (S.Aop.coeff s * S.psi (z + ∑ i ∈ C, S.H i + s))
        = S.bpsi z * ((-1 : ℂ) ^ (m - C.card) * S.psi (z + ∑ i ∈ C, S.H i + d)) := by
    intro C _
    have h1 : ∑ s ∈ S.Aop.coeff.support, S.Aop.coeff s * S.psi (z + ∑ i ∈ C, S.H i + s)
        = S.bpsi (z + ∑ i ∈ C, S.H i) := congrFun (S.act_Aop_psi h11) _
    rw [← Finset.mul_sum, h1, Per.apply (S.sum_H_mem_Per_bpsi C) z]
    ring
  rw [Finset.sum_congr rfl hinner, ← Finset.mul_sum]
  have hD : ∑ C ∈ (univ : Finset (Fin m)).powerset,
      (-1 : ℂ) ^ (m - C.card) * S.psi (z + ∑ i ∈ C, S.H i + d) = 0 := by
    have h0 : act S.Dop S.psi (z + d) = 0 := congrFun (S.act_Dop_psi h11) _
    rw [S.act_Dop_apply S.psi (z + d)] at h0
    refine Eq.trans (Finset.sum_congr rfl fun C _ => ?_) h0
    rw [show z + ∑ i ∈ C, S.H i + d = z + d + ∑ i ∈ C, S.H i by abel]
  rw [hD, mul_zero]

/-! ### §5.2 The quotient algebra -/

/-- `a = A(Y) ∈ R = K[Y₁^±, Y₂^±]`.  Paper §5.2. -/
noncomputable def aElt : LaurentTwo FF := toFF S.Aop

/-- `c = A(X/Y) ∈ R = K[Y₁^±, Y₂^±]`.  Paper §5.2. -/
noncomputable def cElt : LaurentTwo FF := subXY S.Aop

/-- `aᵢ = Aᵢ(Y^{vᵢ})`.  Paper §5.2. -/
noncomputable def aFac (i : Fin m) : LaurentTwo FF := toFF (S.Afac i)

/-- `cᵢ = Aᵢ(X^{vᵢ} Y^{-vᵢ})`.  Paper §5.2. -/
noncomputable def cFac (i : Fin m) : LaurentTwo FF := subXY (S.Afac i)

/-- The ideal `(a, c) ⊆ R`.  Paper §5.2. -/
noncomputable def acIdeal : Ideal (LaurentTwo FF) := Ideal.span {S.aElt, S.cElt}

/-- The base-change ring hom `K[Y^±] → F[Y^±]` induced by `cToFF`, agreeing with `toFF`.
Internal helper for Step 1 of Lemma 5.2. -/
private noncomputable def toFFHom : LaurentTwo ℂ →+* LaurentTwo FF :=
  AddMonoidAlgebra.mapRingHom (ℤ × ℤ) cToFF

private theorem toFFHom_apply (f : LaurentTwo ℂ) : toFFHom f = toFF f := by
  ext; simp [toFFHom, toFF, AddMonoidAlgebra.coeff_mapRingHom]

private theorem toFF_linFactor (v : ℤ × ℤ) (lam : ℂ) :
    toFF (linFactor v lam) = mono v - AddMonoidAlgebra.single (0 : ℤ × ℤ) (cToFF lam) := by
  rw [← toFFHom_apply]
  simp only [linFactor, mono, map_sub, toFFHom, AddMonoidAlgebra.mapRingHom_single, map_one]

/-- The character `Y^s ↦ X^{-s} Y^{-s}` used to build `subXY` as a bundled ring hom.
Internal helper for Step 1 of Lemma 5.2. -/
private noncomputable def subXYCharHom : Multiplicative (ℤ × ℤ) →* LaurentTwo FF where
  toFun s := AddMonoidAlgebra.single (-(Multiplicative.toAdd s)) (Xmono (Multiplicative.toAdd s))
  map_one' := by simp [AddMonoidAlgebra.one_def]
  map_mul' := by
    intro x y
    simp only [toAdd_mul]
    rw [AddMonoidAlgebra.single_mul_single, ← Xmono_add]
    congr 1
    abel

/-- `subXY` as a bundled ring hom `K[Y^±] → F[Y^±]`.  Internal helper for Step 1 of Lemma 5.2. -/
private noncomputable def subXYHom : LaurentTwo ℂ →+* LaurentTwo FF :=
  AddMonoidAlgebra.liftNCRingHom (RingHom.comp (algebraMap FF (LaurentTwo FF)) cToFF)
    subXYCharHom (fun _ _ => Commute.all _ _)

private theorem subXYHom_apply (f : LaurentTwo ℂ) : subXYHom f = subXY f := by
  rw [subXY]
  conv_lhs => rw [← AddMonoidAlgebra.sum_coeff_single f]
  rw [map_finsuppSum]
  refine Finsupp.sum_congr fun s _ => ?_
  show subXYHom (AddMonoidAlgebra.single s (f.coeff s)) = _
  rw [subXYHom, AddMonoidAlgebra.liftNCRingHom_single]
  show (AddMonoidAlgebra.single (0 : ℤ × ℤ) (cToFF (f.coeff s)) : LaurentTwo FF)
      * AddMonoidAlgebra.single (-s) (Xmono s) = _
  rw [AddMonoidAlgebra.single_mul_single, zero_add]

private theorem subXY_linFactor (v : ℤ × ℤ) (lam : ℂ) :
    subXY (linFactor v lam) =
      AddMonoidAlgebra.single (-v) (Xmono v) - AddMonoidAlgebra.single (0 : ℤ × ℤ) (cToFF lam) := by
  rw [← subXYHom_apply]
  simp only [linFactor, mono, map_sub, subXYHom]
  rw [AddMonoidAlgebra.liftNCRingHom_single, AddMonoidAlgebra.liftNCRingHom_single]
  congr 1
  · show (RingHom.comp (algebraMap FF (LaurentTwo FF)) cToFF) 1 * subXYCharHom (Multiplicative.ofAdd v) = _
    simp [subXYCharHom]
  · show (RingHom.comp (algebraMap FF (LaurentTwo FF)) cToFF) lam
        * subXYCharHom (Multiplicative.ofAdd (0 : ℤ × ℤ)) = _
    simp [subXYCharHom]

/-- Explicit Bezout witness: if `c = X^w - αβ ≠ 0` then the single-monomial linear factors
`Y^w - α` and `X^w Y^{-w} - β` are coprime.  Internal helper for Step 1 of Lemma 5.2. -/
private theorem isCoprime_linFactor_step {w : ℤ × ℤ} {α β c : FF} (hc : c = Xmono w - α * β)
    (hc0 : c ≠ 0) :
    IsCoprime (mono w - AddMonoidAlgebra.single (0 : ℤ × ℤ) α)
      (AddMonoidAlgebra.single (-w) (Xmono w) - AddMonoidAlgebra.single (0 : ℤ × ℤ) β) := by
  refine ⟨AddMonoidAlgebra.single 0 (c⁻¹ * β), AddMonoidAlgebra.single w c⁻¹, ?_⟩
  have e1 : (AddMonoidAlgebra.single (0 : ℤ × ℤ) (c⁻¹ * β) : LaurentTwo FF) * mono w
      = AddMonoidAlgebra.single w (c⁻¹ * β) := by
    rw [mono, AddMonoidAlgebra.single_mul_single, zero_add, mul_one]
  have e2 : (AddMonoidAlgebra.single (0 : ℤ × ℤ) (c⁻¹ * β) : LaurentTwo FF)
      * AddMonoidAlgebra.single (0 : ℤ × ℤ) α = AddMonoidAlgebra.single (0 : ℤ × ℤ) (c⁻¹ * β * α) := by
    rw [AddMonoidAlgebra.single_mul_single, zero_add]
  have e3 : (AddMonoidAlgebra.single w (c⁻¹ : FF) : LaurentTwo FF)
      * AddMonoidAlgebra.single (-w) (Xmono w) = AddMonoidAlgebra.single 0 (c⁻¹ * Xmono w) := by
    rw [AddMonoidAlgebra.single_mul_single, add_neg_cancel]
  have e4 : (AddMonoidAlgebra.single w (c⁻¹ : FF) : LaurentTwo FF)
      * AddMonoidAlgebra.single (0 : ℤ × ℤ) β = AddMonoidAlgebra.single w (c⁻¹ * β) := by
    rw [AddMonoidAlgebra.single_mul_single, add_zero]
  rw [mul_sub, mul_sub, e1, e2, e3, e4]
  rw [show (AddMonoidAlgebra.single w (c⁻¹ * β) : LaurentTwo FF)
        - AddMonoidAlgebra.single 0 (c⁻¹ * β * α)
        + (AddMonoidAlgebra.single 0 (c⁻¹ * Xmono w) - AddMonoidAlgebra.single w (c⁻¹ * β))
      = AddMonoidAlgebra.single (0 : ℤ × ℤ) (c⁻¹ * Xmono w)
        - AddMonoidAlgebra.single (0 : ℤ × ℤ) (c⁻¹ * β * α) by abel]
  rw [← AddMonoidAlgebra.single_sub]
  have hfin : c⁻¹ * Xmono w - c⁻¹ * β * α = 1 := by
    have hstep : c⁻¹ * Xmono w - c⁻¹ * β * α = c⁻¹ * c := by rw [hc]; ring
    rw [hstep, inv_mul_cancel₀ hc0]
  rw [hfin]
  simp [AddMonoidAlgebra.one_def]

/-- `Ideal.span {a, b} = ⊤` from `IsCoprime a b`.  Internal helper for Step 1 of Lemma 5.2. -/
private theorem span_pair_eq_top_of_isCoprime {a b : LaurentTwo FF} (h : IsCoprime a b) :
    Ideal.span {a, b} = ⊤ := by
  rw [show ({a, b} : Set (LaurentTwo FF)) = insert a {b} from rfl, Ideal.span_insert]
  exact (Ideal.sup_eq_top_iff_isCoprime a b).2 h

/-- Step 1 (i) of Lemma 5.2: `aᵢ` and `cᵢ` have no common zero, so `(aᵢ, cᵢ) = R`.

Explicit Bezout argument: `aᵢ` and `cᵢ` factor as products, over `λ ∈ Λᵢ`, of the
single-monomial linear factors `Y^{vᵢ} - λ` and `X^{vᵢ} Y^{-vᵢ} - λ`.  Any two such factors
(for `λ, μ ∈ Λᵢ`, possibly equal) are coprime because `X^{vᵢ} ≠ λμ` (as `vᵢ ≠ 0`, so
`X^{vᵢ} ∉ range cToFF` by `Xmono_not_mem_range`, while `λμ ∈ range cToFF`); coprimality of the
products then follows from `IsCoprime.prod_left`/`IsCoprime.prod_right`. -/
theorem aFac_cFac_span_top (i : Fin m) : Ideal.span {S.aFac i, S.cFac i} = ⊤ := by
  apply span_pair_eq_top_of_isCoprime
  have haFac : S.aFac i = ∏ lam ∈ S.Lam i,
      (mono (S.v i) - AddMonoidAlgebra.single (0 : ℤ × ℤ) (cToFF lam)) := by
    have h0 : S.aFac i = toFF (∏ lam ∈ S.Lam i, linFactor (S.v i) lam) := rfl
    rw [h0, ← toFFHom_apply, map_prod]
    exact Finset.prod_congr rfl fun lam _ => by rw [toFFHom_apply]; exact toFF_linFactor (S.v i) lam
  have hcFac : S.cFac i = ∏ lam ∈ S.Lam i,
      (AddMonoidAlgebra.single (-(S.v i)) (Xmono (S.v i))
        - AddMonoidAlgebra.single (0 : ℤ × ℤ) (cToFF lam)) := by
    have h0 : S.cFac i = subXY (∏ lam ∈ S.Lam i, linFactor (S.v i) lam) := rfl
    rw [h0, ← subXYHom_apply, map_prod]
    exact Finset.prod_congr rfl fun lam _ => by
      rw [subXYHom_apply]; exact subXY_linFactor (S.v i) lam
  rw [haFac, hcFac]
  apply IsCoprime.prod_left
  intro lam _
  apply IsCoprime.prod_right
  intro mu _
  refine isCoprime_linFactor_step (c := Xmono (S.v i) - cToFF lam * cToFF mu) rfl ?_
  intro hcontra
  have heq : Xmono (S.v i) = cToFF lam * cToFF mu := sub_eq_zero.mp hcontra
  exact Xmono_not_mem_range (S.primitive i).ne_zero ⟨lam * mu, by rw [map_mul, ← heq]⟩

/-- Two-ideal gluing: if `D1, D2` are comaximal and `x` is a unit mod each, then `x` is a
unit mod `D1 ⊓ D2`. -/
private theorem isUnit_mk_inf_of_isUnit_mk {D1 D2 : Ideal (LaurentTwo FF)} (hcop : D1 ⊔ D2 = ⊤)
    (x : LaurentTwo FF) (h1 : IsUnit (Ideal.Quotient.mk D1 x))
    (h2 : IsUnit (Ideal.Quotient.mk D2 x)) :
    IsUnit (Ideal.Quotient.mk (D1 ⊓ D2) x) := by
  have h1mem : (1 : LaurentTwo FF) ∈ D1 ⊔ D2 := hcop ▸ Submodule.mem_top
  obtain ⟨e1, he1, e2, he2, he12⟩ := Submodule.mem_sup.1 h1mem
  obtain ⟨y1, hy1⟩ := h1.exists_right_inv
  obtain ⟨y2, hy2⟩ := h2.exists_right_inv
  obtain ⟨y1', rfl⟩ := Ideal.Quotient.mk_surjective y1
  obtain ⟨y2', rfl⟩ := Ideal.Quotient.mk_surjective y2
  rw [← map_mul, show (1 : LaurentTwo FF ⧸ D1) = Ideal.Quotient.mk D1 1 from (map_one _).symm,
    Ideal.Quotient.mk_eq_mk_iff_sub_mem] at hy1
  rw [← map_mul, show (1 : LaurentTwo FF ⧸ D2) = Ideal.Quotient.mk D2 1 from (map_one _).symm,
    Ideal.Quotient.mk_eq_mk_iff_sub_mem] at hy2
  set y : LaurentTwo FF := e2 * y1' + e1 * y2' with hy
  have key : x * y - 1 ∈ D1 ⊓ D2 := by
    rw [Submodule.mem_inf]
    constructor
    · have heq : x * y - 1 = e1 * (x * y2' - 1) + (x * y1' - 1) * e2 + (e1 + e2 - 1) := by
        rw [hy]; ring
      rw [heq]
      have t1 : e1 * (x * y2' - 1) ∈ D1 := Ideal.mul_mem_right _ _ he1
      have t2 : (x * y1' - 1) * e2 ∈ D1 := Ideal.mul_mem_right _ _ hy1
      have t3 : e1 + e2 - 1 ∈ D1 := by rw [← he12]; simp
      exact D1.add_mem (D1.add_mem t1 t2) t3
    · have heq : x * y - 1 = e2 * (x * y1' - 1) + (x * y2' - 1) * e1 + (e1 + e2 - 1) := by
        rw [hy]; ring
      rw [heq]
      have t1 : e2 * (x * y1' - 1) ∈ D2 := Ideal.mul_mem_right _ _ he2
      have t2 : (x * y2' - 1) * e1 ∈ D2 := Ideal.mul_mem_right _ _ hy2
      have t3 : e1 + e2 - 1 ∈ D2 := by rw [← he12]; simp
      exact D2.add_mem (D2.add_mem t1 t2) t3
  have hkey : Ideal.Quotient.mk (D1 ⊓ D2) (x * y) = 1 := by
    have := Ideal.Quotient.eq_zero_iff_mem.2 key
    rwa [map_sub, map_one, sub_eq_zero] at this
  exact isUnit_iff_exists.2 ⟨Ideal.Quotient.mk (D1 ⊓ D2) y, hkey, by rw [← map_mul, mul_comm y x, hkey]⟩

/-- If `a, b` are coprime, `(a) + B` and `(b) + B` are comaximal, and their intersection is
`(ab) + B`. -/
private theorem span_sup_inf_span_sup {a b : LaurentTwo FF} (B : Ideal (LaurentTwo FF))
    (hab : IsCoprime a b) :
    (Ideal.span {a} ⊔ B) ⊓ (Ideal.span {b} ⊔ B) = Ideal.span {a * b} ⊔ B := by
  obtain ⟨p, q, hpq⟩ := hab
  apply le_antisymm
  · rintro z hz
    obtain ⟨hz1, hz2⟩ := Submodule.mem_inf.1 hz
    obtain ⟨u1, hu1, b1, hb1, e1⟩ := Submodule.mem_sup.1 hz1
    obtain ⟨u2, hu2, b2, hb2, e2⟩ := Submodule.mem_sup.1 hz2
    obtain ⟨r1, rfl⟩ := Ideal.mem_span_singleton.1 hu1
    obtain ⟨r2, rfl⟩ := Ideal.mem_span_singleton.1 hu2
    have hzeq : z = a * b * (p * r2 + q * r1) + (p * a * b2 + q * b * b1) := by
      have hexp : z = p * a * z + q * b * z := by rw [← add_mul, hpq, one_mul]
      have hz1' : p * a * z = p * a * (b * r2 + b2) := by rw [← e2]
      have hz2' : q * b * z = q * b * (a * r1 + b1) := by rw [← e1]
      rw [hexp, hz1', hz2']; ring
    rw [hzeq]
    refine Submodule.mem_sup.2 ⟨a * b * (p * r2 + q * r1), Ideal.mem_span_singleton.2 ⟨_, rfl⟩,
      p * a * b2 + q * b * b1, ?_, rfl⟩
    exact B.add_mem (Ideal.mul_mem_left B (p * a) hb2) (Ideal.mul_mem_left B (q * b) hb1)
  · apply sup_le
    · rw [Ideal.span_singleton_le_iff_mem]
      exact Submodule.mem_inf.2 ⟨Ideal.mem_sup_left (Ideal.mem_span_singleton.2 ⟨b, rfl⟩),
        Ideal.mem_sup_left (Ideal.mem_span_singleton.2 ⟨a, mul_comm a b⟩)⟩
    · exact le_inf le_sup_right le_sup_right

/-- Combine local units mod `(h a) + B` over a pairwise-coprime family `h` on a finset `T`
into a global unit mod `(∏ h) + B`. -/
private theorem isUnit_mk_span_prod_sup {ι : Type*} [DecidableEq ι] {T : Finset ι}
    {B : Ideal (LaurentTwo FF)} {h : ι → LaurentTwo FF} {x : LaurentTwo FF}
    (hcop : ∀ a ∈ T, ∀ b ∈ T, a ≠ b → IsCoprime (h a) (h b))
    (hu : ∀ a ∈ T, IsUnit (Ideal.Quotient.mk (Ideal.span {h a} ⊔ B) x)) :
    IsUnit (Ideal.Quotient.mk (Ideal.span {∏ a ∈ T, h a} ⊔ B) x) := by
  classical
  induction T using Finset.induction with
  | empty =>
    have heq : Ideal.span ({∏ a ∈ (∅ : Finset ι), h a} : Set (LaurentTwo FF)) ⊔ B = ⊤ := by
      rw [Finset.prod_empty, Ideal.span_singleton_one, top_sup_eq]
    rw [heq]
    have : Subsingleton (LaurentTwo FF ⧸ (⊤ : Ideal (LaurentTwo FF))) :=
      Ideal.Quotient.subsingleton_iff.2 rfl
    exact isUnit_of_subsingleton _
  | @insert a T' ha ih =>
    have hcop' : ∀ c ∈ T', ∀ d ∈ T', c ≠ d → IsCoprime (h c) (h d) := fun c hc d hd hcd =>
      hcop c (Finset.mem_insert_of_mem hc) d (Finset.mem_insert_of_mem hd) hcd
    have hu' : ∀ c ∈ T', IsUnit (Ideal.Quotient.mk (Ideal.span {h c} ⊔ B) x) := fun c hc =>
      hu c (Finset.mem_insert_of_mem hc)
    have ihT' := ih hcop' hu'
    have huA : IsUnit (Ideal.Quotient.mk (Ideal.span {h a} ⊔ B) x) := hu a (Finset.mem_insert_self a T')
    have hcopAT' : IsCoprime (h a) (∏ c ∈ T', h c) := by
      apply IsCoprime.prod_right
      intro c hc
      exact hcop a (Finset.mem_insert_self a T') c (Finset.mem_insert_of_mem hc)
        (fun heq => ha (heq ▸ hc))
    have hsup : (Ideal.span {h a} ⊔ B) ⊔ (Ideal.span {∏ c ∈ T', h c} ⊔ B) = ⊤ := by
      have : Ideal.span {h a} ⊔ Ideal.span {∏ c ∈ T', h c} = ⊤ :=
        (Ideal.sup_eq_top_iff_isCoprime _ _).2 hcopAT'
      have hle : Ideal.span ({h a} : Set (LaurentTwo FF)) ⊔ Ideal.span {∏ c ∈ T', h c} ≤
          (Ideal.span {h a} ⊔ B) ⊔ (Ideal.span {∏ c ∈ T', h c} ⊔ B) :=
        sup_le_sup le_sup_left le_sup_left
      rw [this] at hle
      exact top_le_iff.1 hle
    have hglue := isUnit_mk_inf_of_isUnit_mk hsup x huA ihT'
    rw [span_sup_inf_span_sup B hcopAT'] at hglue
    rwa [Finset.prod_insert ha]

/-! ### Step 2 core lemma infrastructure -/

/-- General CRT-style power lemma: if two units of a commutative ring agree mod an ideal,
so do their `n`-th powers for any `n : ℤ`. -/
private theorem zpow_sub_mem_of_sub_mem {R : Type*} [CommRing R] {J : Ideal R} {u w : Rˣ}
    (h : (u : R) - (w : R) ∈ J) (n : ℤ) :
    ((u ^ n : Rˣ) : R) - ((w ^ n : Rˣ) : R) ∈ J := by
  set φ := Ideal.Quotient.mk J
  have hφ : φ (u : R) = φ (w : R) := by
    rw [← sub_eq_zero, ← map_sub]; exact (Ideal.Quotient.eq_zero_iff_mem).2 h
  have heq : Units.map φ.toMonoidHom u = Units.map φ.toMonoidHom w := Units.ext (by simpa using hφ)
  have heqn : (Units.map φ.toMonoidHom u) ^ n = (Units.map φ.toMonoidHom w) ^ n := by rw [heq]
  have e1 : ((Units.map φ.toMonoidHom u) ^ n : (R ⧸ J)ˣ) = Units.map φ.toMonoidHom (u ^ n) :=
    (map_zpow _ u n).symm
  have e2 : ((Units.map φ.toMonoidHom w) ^ n : (R ⧸ J)ˣ) = Units.map φ.toMonoidHom (w ^ n) :=
    (map_zpow _ w n).symm
  rw [e1, e2] at heqn
  have : φ ((u ^ n : Rˣ) : R) = φ ((w ^ n : Rˣ) : R) := congrArg Units.val heqn
  rw [← sub_eq_zero, ← map_sub] at this
  exact (Ideal.Quotient.eq_zero_iff_mem).1 this

/-- `mono v` bundled as a unit of `LaurentTwo FF`. -/
private noncomputable def monoUnit (v : ℤ × ℤ) : (LaurentTwo FF)ˣ where
  val := mono v
  inv := mono (-v)
  val_inv := by rw [mono_mul_mono, add_neg_cancel, mono_zero]
  inv_val := by rw [mono_mul_mono, neg_add_cancel, mono_zero]

private noncomputable def monoUnitHom : Multiplicative (ℤ × ℤ) →* (LaurentTwo FF)ˣ where
  toFun s := monoUnit (Multiplicative.toAdd s)
  map_one' := by apply Units.ext; simp [monoUnit, mono_zero]
  map_mul' := by
    intro x y
    apply Units.ext
    show (mono (Multiplicative.toAdd (x * y)) : LaurentTwo FF)
      = mono (Multiplicative.toAdd x) * mono (Multiplicative.toAdd y)
    rw [toAdd_mul, mono_mul_mono]

private theorem monoUnit_zsmul (v : ℤ × ℤ) (n : ℤ) :
    ((monoUnit v ^ n : (LaurentTwo FF)ˣ) : LaurentTwo FF) = mono (n • v) := by
  have : monoUnit v ^ n = monoUnitHom (Multiplicative.ofAdd v ^ n) := by
    rw [map_zpow]; rfl
  rw [this, ← ofAdd_zsmul]
  rfl

/-- `single 0 a` (for `a ≠ 0`) bundled as a unit of `LaurentTwo FF`. -/
private noncomputable def single0Unit {a : FF} (ha : a ≠ 0) : (LaurentTwo FF)ˣ :=
  Units.map (AddMonoidAlgebra.singleZeroRingHom (R := FF) (M := ℤ × ℤ)).toMonoidHom
    (Units.mk0 a ha)

private theorem single0Unit_val {a : FF} (ha : a ≠ 0) :
    ((single0Unit ha : (LaurentTwo FF)ˣ) : LaurentTwo FF) = AddMonoidAlgebra.single (0 : ℤ × ℤ) a := by
  simp [single0Unit]

private theorem single0Unit_zpow {a : FF} (ha : a ≠ 0) (n : ℤ) :
    ((single0Unit ha ^ n : (LaurentTwo FF)ˣ) : LaurentTwo FF)
      = AddMonoidAlgebra.single (0 : ℤ × ℤ) (a ^ n) := by
  have key : single0Unit ha ^ n =
      Units.map (AddMonoidAlgebra.singleZeroRingHom (R := FF) (M := ℤ × ℤ)).toMonoidHom
        ((Units.mk0 a ha) ^ n) := by
    show (Units.map (AddMonoidAlgebra.singleZeroRingHom (R := FF) (M := ℤ × ℤ)).toMonoidHom
      (Units.mk0 a ha)) ^ n = _
    exact (map_zpow _ _ n).symm
  rw [key, Units.coe_map, Units.val_zpow_eq_zpow_val, Units.val_mk0]
  rfl

/-- Product-combination congruence: if `x₁ ≡ y₁` and `x₂ ≡ y₂` mod `J`, then `x₁x₂ ≡ y₁y₂`. -/
private theorem sub_mul_sub_mem {R : Type*} [CommRing R] {J : Ideal R} {x1 y1 x2 y2 : R}
    (h1 : x1 - y1 ∈ J) (h2 : x2 - y2 ∈ J) : x1 * x2 - y1 * y2 ∈ J := by
  have heq : x1 * x2 - y1 * y2 = x1 * (x2 - y2) + (x1 - y1) * y2 := by ring
  rw [heq]
  exact J.add_mem (Ideal.mul_mem_left J x1 h2) (Ideal.mul_mem_right y2 J h1)

/-- Two distinct linear factors `mono v - λ` and `mono v - λ'` (same `v`, `λ ≠ λ'`) are
coprime, via the explicit inverse `(λ' - λ)⁻¹`. -/
private theorem isCoprime_mono_sub_single0_of_ne {v : ℤ × ℤ} {lam lam' : FF} (h : lam ≠ lam') :
    IsCoprime (mono v - AddMonoidAlgebra.single (0 : ℤ × ℤ) lam)
      (mono v - AddMonoidAlgebra.single (0 : ℤ × ℤ) lam') := by
  have hne : lam' - lam ≠ 0 := sub_ne_zero.2 (Ne.symm h)
  refine ⟨AddMonoidAlgebra.single 0 (lam' - lam)⁻¹, -AddMonoidAlgebra.single 0 (lam' - lam)⁻¹, ?_⟩
  have heq : (AddMonoidAlgebra.single (0 : ℤ × ℤ) (lam' - lam)⁻¹ : LaurentTwo FF)
      * (mono v - AddMonoidAlgebra.single 0 lam)
      + -AddMonoidAlgebra.single (0 : ℤ × ℤ) (lam' - lam)⁻¹ * (mono v - AddMonoidAlgebra.single 0 lam')
      = AddMonoidAlgebra.single (0 : ℤ × ℤ) (lam' - lam)⁻¹
        * (AddMonoidAlgebra.single (0 : ℤ × ℤ) lam' - AddMonoidAlgebra.single (0 : ℤ × ℤ) lam) := by
    ring
  rw [heq, ← AddMonoidAlgebra.single_sub, AddMonoidAlgebra.single_mul_single, zero_add,
    inv_mul_cancel₀ hne]
  simp [AddMonoidAlgebra.one_def]

/-- Explicit Bezout witness (via the geometric-sum identity `∑ Wⁱcᴰ⁻¹⁻ⁱ · (W-c) = Wᴰ - cᴰ`):
if `W^D ≡ ν` mod `J` and `ν ≠ c^D`, then `W - c` is a unit mod `J`. -/
private theorem isUnit_mk_sub_single0_of_pow_sub_mem {J : Ideal (LaurentTwo FF)}
    {W : LaurentTwo FF} {c ν : FF} {D0 : ℕ} (_hD0 : 0 < D0)
    (hWD : W ^ D0 - AddMonoidAlgebra.single (0 : ℤ × ℤ) ν ∈ J) (hne : ν ≠ c ^ D0) :
    IsUnit (Ideal.Quotient.mk J (W - AddMonoidAlgebra.single (0 : ℤ × ℤ) c)) := by
  set Q : LaurentTwo FF :=
    ∑ i ∈ Finset.range D0, W ^ i * (AddMonoidAlgebra.single (0 : ℤ × ℤ) c) ^ (D0 - 1 - i) with hQ
  have hgeom : Q * (W - AddMonoidAlgebra.single (0 : ℤ × ℤ) c)
      = W ^ D0 - (AddMonoidAlgebra.single (0 : ℤ × ℤ) c) ^ D0 :=
    geom_sum₂_mul W (AddMonoidAlgebra.single (0 : ℤ × ℤ) c) D0
  have hcD : (AddMonoidAlgebra.single (0 : ℤ × ℤ) c : LaurentTwo FF) ^ D0
      = AddMonoidAlgebra.single (0 : ℤ × ℤ) (c ^ D0) := by
    have := map_pow (AddMonoidAlgebra.singleZeroRingHom (R := FF) (M := ℤ × ℤ)) c D0
    simp
  have he : ν - c ^ D0 ≠ 0 := sub_ne_zero.2 hne
  have key : Q * (W - AddMonoidAlgebra.single (0 : ℤ × ℤ) c)
      - AddMonoidAlgebra.single (0 : ℤ × ℤ) (ν - c ^ D0) ∈ J := by
    rw [hgeom, hcD, AddMonoidAlgebra.single_sub]
    have heq2 : W ^ D0 - AddMonoidAlgebra.single (0 : ℤ × ℤ) (c ^ D0)
        - (AddMonoidAlgebra.single (0 : ℤ × ℤ) ν - AddMonoidAlgebra.single (0 : ℤ × ℤ) (c ^ D0))
        = W ^ D0 - AddMonoidAlgebra.single (0 : ℤ × ℤ) ν := by ring
    rwa [heq2]
  have hmk : Ideal.Quotient.mk J (Q * (W - AddMonoidAlgebra.single (0 : ℤ × ℤ) c))
      = Ideal.Quotient.mk J (AddMonoidAlgebra.single (0 : ℤ × ℤ) (ν - c ^ D0)) := by
    have := Ideal.Quotient.eq_zero_iff_mem.2 key
    rwa [map_sub, sub_eq_zero] at this
  have hprod : Ideal.Quotient.mk J Q * Ideal.Quotient.mk J (W - AddMonoidAlgebra.single (0 : ℤ × ℤ) c)
      = Ideal.Quotient.mk J (AddMonoidAlgebra.single (0 : ℤ × ℤ) (ν - c ^ D0)) := by
    rw [← map_mul]; exact hmk
  have hunitRHS : IsUnit (Ideal.Quotient.mk J (AddMonoidAlgebra.single (0 : ℤ × ℤ) (ν - c ^ D0))) := by
    rw [← single0Unit_val he]
    exact (single0Unit he).isUnit.map (Ideal.Quotient.mk J)
  obtain ⟨u, hu⟩ := hunitRHS
  set a := Ideal.Quotient.mk J Q
  set b := Ideal.Quotient.mk J (W - AddMonoidAlgebra.single (0 : ℤ × ℤ) c)
  have hab : a * b = (u : LaurentTwo FF ⧸ J) := by rw [hprod, hu]
  refine isUnit_iff_exists.2 ⟨a * (↑u⁻¹ : LaurentTwo FF ⧸ J), ?_, ?_⟩
  · calc b * (a * (↑u⁻¹ : LaurentTwo FF ⧸ J)) = (a * b) * (↑u⁻¹ : LaurentTwo FF ⧸ J) := by ring
      _ = (u : LaurentTwo FF ⧸ J) * (↑u⁻¹ : LaurentTwo FF ⧸ J) := by rw [hab]
      _ = 1 := u.mul_inv
  · calc a * (↑u⁻¹ : LaurentTwo FF ⧸ J) * b = (a * b) * (↑u⁻¹ : LaurentTwo FF ⧸ J) := by ring
      _ = (u : LaurentTwo FF ⧸ J) * (↑u⁻¹ : LaurentTwo FF ⧸ J) := by rw [hab]
      _ = 1 := u.mul_inv

/-- Swap identity: `W - c = -(Wc) · (W⁻¹ - c⁻¹)` for a unit `W` and nonzero constant `c`. -/
private theorem sub_single0_eq_mul_inv_sub_single0_inv (Wu : (LaurentTwo FF)ˣ) {c : FF} (hc : c ≠ 0) :
    (Wu : LaurentTwo FF) - AddMonoidAlgebra.single (0 : ℤ × ℤ) c
      = (-((Wu : LaurentTwo FF) * AddMonoidAlgebra.single (0 : ℤ × ℤ) c)) *
          ((Wu⁻¹ : (LaurentTwo FF)ˣ) - AddMonoidAlgebra.single (0 : ℤ × ℤ) c⁻¹) := by
  have h1 : ((Wu : LaurentTwo FF) * (Wu⁻¹ : (LaurentTwo FF)ˣ) : LaurentTwo FF) = 1 := Wu.mul_inv
  have h2 : (AddMonoidAlgebra.single (0 : ℤ × ℤ) c : LaurentTwo FF)
      * AddMonoidAlgebra.single (0 : ℤ × ℤ) c⁻¹ = 1 := by
    rw [AddMonoidAlgebra.single_mul_single, zero_add, mul_inv_cancel₀ hc]
    simp [AddMonoidAlgebra.one_def]
  have expand : (-((Wu : LaurentTwo FF) * AddMonoidAlgebra.single (0 : ℤ × ℤ) c)) *
      ((Wu⁻¹ : (LaurentTwo FF)ˣ) - AddMonoidAlgebra.single (0 : ℤ × ℤ) c⁻¹)
      = -(AddMonoidAlgebra.single (0 : ℤ × ℤ) c) * ((Wu : LaurentTwo FF) * (Wu⁻¹ : (LaurentTwo FF)ˣ))
        + (Wu : LaurentTwo FF) * (AddMonoidAlgebra.single (0 : ℤ × ℤ) c
          * AddMonoidAlgebra.single (0 : ℤ × ℤ) c⁻¹) := by ring
  rw [expand, h1, h2]; ring

/-- Integer-power version: if `Wuᴰ ≡ ν` mod `J` (`D : ℤ`, `D ≠ 0`) and `ν ≠ cᴰ`, then `Wu - c` is
a unit mod `J`. Reduces to `isUnit_mk_sub_single0_of_pow_sub_mem` via `D.natAbs`, swapping to
`Wu⁻¹, c⁻¹` when `D < 0`. -/
private theorem isUnit_mk_sub_single0_of_zpow_sub_mem {J : Ideal (LaurentTwo FF)}
    (Wu : (LaurentTwo FF)ˣ) {c ν : FF} (hc : c ≠ 0) {D : ℤ} (hD : D ≠ 0)
    (hWD : ((Wu ^ D : (LaurentTwo FF)ˣ) : LaurentTwo FF) - AddMonoidAlgebra.single (0 : ℤ × ℤ) ν ∈ J)
    (hne : ν ≠ c ^ D) :
    IsUnit (Ideal.Quotient.mk J ((Wu : LaurentTwo FF) - AddMonoidAlgebra.single (0 : ℤ × ℤ) c)) := by
  rcases lt_or_gt_of_ne hD with hDneg | hDpos
  · set D0 : ℕ := (-D).toNat with hD0def
    have hD0 : (D0 : ℤ) = -D := Int.toNat_of_nonneg (by omega)
    have hDpos0 : 0 < D0 := by omega
    have hDeq : D = -(D0 : ℤ) := by omega
    have hWpow : ((Wu⁻¹ : (LaurentTwo FF)ˣ) ^ D0 : (LaurentTwo FF)ˣ) = (Wu ^ D : (LaurentTwo FF)ˣ) := by
      rw [hDeq, zpow_neg, zpow_natCast, inv_pow]
    have hne' : ν ≠ (c⁻¹) ^ D0 := by
      have hcD : c ^ D = (c⁻¹) ^ D0 := by rw [hDeq, zpow_neg, zpow_natCast, inv_pow]
      rwa [← hcD]
    have hWD' : ((Wu⁻¹ : (LaurentTwo FF)ˣ) : LaurentTwo FF) ^ D0
        - AddMonoidAlgebra.single (0 : ℤ × ℤ) ν ∈ J := by
      rw [← Units.val_pow_eq_pow_val, hWpow]; exact hWD
    have hunit := isUnit_mk_sub_single0_of_pow_sub_mem hDpos0 hWD' hne'
    rw [sub_single0_eq_mul_inv_sub_single0_inv Wu hc]
    have hγ : IsUnit ((Ideal.Quotient.mk J)
        (-((Wu : LaurentTwo FF) * AddMonoidAlgebra.single (0 : ℤ × ℤ) c))) :=
      (((Wu.isUnit).mul (single0Unit hc).isUnit).neg).map (Ideal.Quotient.mk J)
    rw [map_mul]
    exact hγ.mul hunit
  · set D0 : ℕ := D.toNat with hD0def
    have hD0 : (D0 : ℤ) = D := Int.toNat_of_nonneg (by omega)
    have hDpos0 : 0 < D0 := by omega
    have hne' : ν ≠ c ^ D0 := by rw [← zpow_natCast, hD0]; exact hne
    have hWD' : ((Wu : LaurentTwo FF)) ^ D0 - AddMonoidAlgebra.single (0 : ℤ × ℤ) ν ∈ J := by
      rw [← Units.val_pow_eq_pow_val, ← zpow_natCast, hD0]; exact hWD
    exact isUnit_mk_sub_single0_of_pow_sub_mem hDpos0 hWD' hne'

private theorem cToFF_ne_zero {x : ℂ} (hx : x ≠ 0) : cToFF x ≠ 0 := by
  rw [cToFF, RingHom.comp_apply, Ne, IsFractionRing.to_map_eq_zero_iff]
  exact fun h => hx ((MvPolynomial.C_injective (Fin 2) ℂ) (by rw [h]; simp))

private theorem det_smul_eq (v u z : ℤ × ℤ) : (det v u) • z = (det z u) • v + (det v z) • u := by
  have h1 : ((det v u) • z).1 = ((det z u) • v + (det v z) • u).1 := by
    show (det v u) * z.1 = (det z u) * v.1 + (det v z) * u.1
    simp only [det]; ring
  have h2 : ((det v u) • z).2 = ((det z u) • v + (det v z) • u).2 := by
    show (det v u) * z.2 = (det z u) * v.2 + (det v z) * u.2
    simp only [det]; ring
  exact Prod.ext h1 h2

/-- `X^{n • v} = (X^v)^n` for any `n : ℤ`. -/
private theorem Xmono_zsmul (v : ℤ × ℤ) (n : ℤ) : Xmono (n • v) = Xmono v ^ n := by
  simp only [Xmono, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, mul_comm n v.1, mul_comm n v.2,
    zpow_mul, mul_zpow]

/-- Core Step-2 factor lemma: for `v1, v2` non-parallel and `v3 ≠ 0`, the `X/Y`-type linear
factor of `v3` at `mu ≠ 0` is a unit modulo the ideal spanned by the `Y`-type linear factors of
`v1` at `lam1 ≠ 0` and of `v2` at `lam2 ≠ 0`.  Uses the Cramer identity
`det(v1,v2) • v3 = det(v3,v2) • v1 + det(v1,v3) • v2` to relate `mono v3 ^ det(v1,v2)` to
`single0 (lam1^{det(v3,v2)} * lam2^{det(v1,v3)})` mod the ideal, then the transcendence of
`Xmono v3` (via `Xmono_not_mem_range`) to separate it from this algebraic constant. -/
private theorem isUnit_mk_cFacFactor_of_nonparallel {v1 v2 v3 : ℤ × ℤ}
    (hd : det v1 v2 ≠ 0) (hv3 : v3 ≠ 0) {lam1 lam2 mu : ℂ}
    (h1 : lam1 ≠ 0) (h2 : lam2 ≠ 0) (h3 : mu ≠ 0) :
    IsUnit (Ideal.Quotient.mk
      (Ideal.span {mono v1 - AddMonoidAlgebra.single (0 : ℤ × ℤ) (cToFF lam1),
                   mono v2 - AddMonoidAlgebra.single (0 : ℤ × ℤ) (cToFF lam2)})
      (AddMonoidAlgebra.single (-v3) (Xmono v3) - AddMonoidAlgebra.single (0 : ℤ × ℤ) (cToFF mu))) := by
  set J : Ideal (LaurentTwo FF) :=
    Ideal.span {mono v1 - AddMonoidAlgebra.single (0 : ℤ × ℤ) (cToFF lam1),
                mono v2 - AddMonoidAlgebra.single (0 : ℤ × ℤ) (cToFF lam2)} with hJ
  set D : ℤ := det v1 v2 with hDdef
  set n1 : ℤ := det v3 v2 with hn1def
  set n2 : ℤ := det v1 v3 with hn2def
  have hcramer : D • v3 = n1 • v1 + n2 • v2 := det_smul_eq v1 v2 v3
  have hf1 : mono v1 - AddMonoidAlgebra.single (0 : ℤ × ℤ) (cToFF lam1) ∈ J := by
    rw [hJ]; exact Ideal.subset_span (by simp)
  have hf2 : mono v2 - AddMonoidAlgebra.single (0 : ℤ × ℤ) (cToFF lam2) ∈ J := by
    rw [hJ]; exact Ideal.subset_span (by simp)
  set u1 := monoUnit v1
  set u2 := monoUnit v2
  set a1 := single0Unit (cToFF_ne_zero h1)
  set a2 := single0Unit (cToFF_ne_zero h2)
  have hu1sub : (u1 : LaurentTwo FF) - (a1 : LaurentTwo FF) ∈ J := by
    rw [show ((a1 : LaurentTwo FF)) = AddMonoidAlgebra.single (0 : ℤ × ℤ) (cToFF lam1) from
      single0Unit_val _]
    exact hf1
  have hu2sub : (u2 : LaurentTwo FF) - (a2 : LaurentTwo FF) ∈ J := by
    rw [show ((a2 : LaurentTwo FF)) = AddMonoidAlgebra.single (0 : ℤ × ℤ) (cToFF lam2) from
      single0Unit_val _]
    exact hf2
  have hp1 : ((u1 ^ n1 : (LaurentTwo FF)ˣ) : LaurentTwo FF)
      - ((a1 ^ n1 : (LaurentTwo FF)ˣ) : LaurentTwo FF) ∈ J := zpow_sub_mem_of_sub_mem hu1sub n1
  have hp2 : ((u2 ^ n2 : (LaurentTwo FF)ˣ) : LaurentTwo FF)
      - ((a2 ^ n2 : (LaurentTwo FF)ˣ) : LaurentTwo FF) ∈ J := zpow_sub_mem_of_sub_mem hu2sub n2
  have hprodmem : ((u1 ^ n1 : (LaurentTwo FF)ˣ) : LaurentTwo FF)
        * ((u2 ^ n2 : (LaurentTwo FF)ˣ) : LaurentTwo FF)
      - ((a1 ^ n1 : (LaurentTwo FF)ˣ) : LaurentTwo FF)
        * ((a2 ^ n2 : (LaurentTwo FF)ˣ) : LaurentTwo FF) ∈ J := sub_mul_sub_mem hp1 hp2
  set nu : ℂ := lam1 ^ n1 * lam2 ^ n2 with hnu
  have ha1val : ((a1 ^ n1 : (LaurentTwo FF)ˣ) : LaurentTwo FF)
      = AddMonoidAlgebra.single (0 : ℤ × ℤ) (cToFF lam1 ^ n1) := single0Unit_zpow _ n1
  have ha2val : ((a2 ^ n2 : (LaurentTwo FF)ˣ) : LaurentTwo FF)
      = AddMonoidAlgebra.single (0 : ℤ × ℤ) (cToFF lam2 ^ n2) := single0Unit_zpow _ n2
  have hmulval : (AddMonoidAlgebra.single (0 : ℤ × ℤ) (cToFF lam1 ^ n1) : LaurentTwo FF)
      * AddMonoidAlgebra.single (0 : ℤ × ℤ) (cToFF lam2 ^ n2)
      = AddMonoidAlgebra.single (0 : ℤ × ℤ) (cToFF nu) := by
    rw [AddMonoidAlgebra.single_mul_single, zero_add, hnu, map_mul, map_zpow₀, map_zpow₀]
  have hu1val : ((u1 ^ n1 : (LaurentTwo FF)ˣ) : LaurentTwo FF) = mono (n1 • v1) :=
    monoUnit_zsmul v1 n1
  have hu2val : ((u2 ^ n2 : (LaurentTwo FF)ˣ) : LaurentTwo FF) = mono (n2 • v2) :=
    monoUnit_zsmul v2 n2
  have hmonoprod : (mono (n1 • v1) : LaurentTwo FF) * mono (n2 • v2) = mono (D • v3) := by
    rw [mono_mul_mono, ← hcramer]
  have huD : ((monoUnit v3 ^ D : (LaurentTwo FF)ˣ) : LaurentTwo FF) = mono (D • v3) :=
    monoUnit_zsmul v3 D
  have hDmem : ((monoUnit v3 ^ D : (LaurentTwo FF)ˣ) : LaurentTwo FF)
      - AddMonoidAlgebra.single (0 : ℤ × ℤ) (cToFF nu) ∈ J := by
    rw [huD, ← hmonoprod, ← hu1val, ← hu2val, ← hmulval, ← ha1val, ← ha2val]
    exact hprodmem
  have hmu0 : cToFF mu ≠ 0 := cToFF_ne_zero h3
  set β : FF := Xmono v3 * (cToFF mu)⁻¹ with hβdef
  have hβ0 : β ≠ 0 := mul_ne_zero (Xmono_ne_zero v3) (inv_ne_zero hmu0)
  have hDv3ne : D • v3 ≠ 0 := smul_ne_zero hd hv3
  have hne : cToFF nu ≠ β ^ D := by
    intro heq
    have hmuD0 : (cToFF mu) ^ D ≠ 0 := zpow_ne_zero D hmu0
    have hstep : cToFF nu * (cToFF mu) ^ D = Xmono v3 ^ D := by
      rw [heq, hβdef, mul_zpow, inv_zpow, inv_mul_cancel_right₀ hmuD0]
    have hcontra : Xmono (D • v3) ∈ Set.range cToFF :=
      ⟨nu * mu ^ D, by rw [map_mul, map_zpow₀, hstep, Xmono_zsmul]⟩
    exact Xmono_not_mem_range hDv3ne hcontra
  have hunit2 : IsUnit (Ideal.Quotient.mk J
      (mono v3 - AddMonoidAlgebra.single (0 : ℤ × ℤ) β)) :=
    isUnit_mk_sub_single0_of_zpow_sub_mem (monoUnit v3) hβ0 hd hDmem hne
  have hcβ : cToFF mu * β = Xmono v3 := by
    rw [hβdef, mul_comm (Xmono v3) (cToFF mu)⁻¹, ← mul_assoc, mul_inv_cancel₀ hmu0, one_mul]
  have e1 : (mono (-v3) : LaurentTwo FF) * mono v3 = 1 := by
    rw [mono_mul_mono, neg_add_cancel, mono_zero]
  have e2 : (mono (-v3) : LaurentTwo FF) * AddMonoidAlgebra.single (0 : ℤ × ℤ) (cToFF mu * β)
      = AddMonoidAlgebra.single (-v3) (Xmono v3) := by
    rw [mono, AddMonoidAlgebra.single_mul_single, add_zero, one_mul, hcβ]
  have e3 : (AddMonoidAlgebra.single (0 : ℤ × ℤ) (cToFF mu) : LaurentTwo FF)
      * AddMonoidAlgebra.single (0 : ℤ × ℤ) β = AddMonoidAlgebra.single (0 : ℤ × ℤ) (cToFF mu * β) := by
    rw [AddMonoidAlgebra.single_mul_single, zero_add]
  have hfactor : (AddMonoidAlgebra.single (-v3) (Xmono v3)
        - AddMonoidAlgebra.single (0 : ℤ × ℤ) (cToFF mu) : LaurentTwo FF)
      = (-(mono (-v3) * AddMonoidAlgebra.single (0 : ℤ × ℤ) (cToFF mu)))
          * (mono v3 - AddMonoidAlgebra.single (0 : ℤ × ℤ) β) := by
    have expand : (-(mono (-v3) * AddMonoidAlgebra.single (0 : ℤ × ℤ) (cToFF mu))) *
          (mono v3 - AddMonoidAlgebra.single (0 : ℤ × ℤ) β)
        = -(mono (-v3) * mono v3) * AddMonoidAlgebra.single (0 : ℤ × ℤ) (cToFF mu)
          + mono (-v3) * (AddMonoidAlgebra.single (0 : ℤ × ℤ) (cToFF mu)
            * AddMonoidAlgebra.single (0 : ℤ × ℤ) β) := by ring
    rw [expand, e1, e3, e2]
    ring
  have hIsUnitNegv3 : IsUnit (mono (-v3) : LaurentTwo FF) := (monoUnit (-v3)).isUnit
  have hIsUnitMu : IsUnit (AddMonoidAlgebra.single (0 : ℤ × ℤ) (cToFF mu) : LaurentTwo FF) := by
    rw [← single0Unit_val hmu0]; exact (single0Unit hmu0).isUnit
  have hunitL : IsUnit (Ideal.Quotient.mk J
      (-(mono (-v3) * AddMonoidAlgebra.single (0 : ℤ × ℤ) (cToFF mu)))) :=
    ((hIsUnitNegv3.mul hIsUnitMu).neg).map (Ideal.Quotient.mk J)
  rw [hfactor, map_mul]
  exact hunitL.mul hunit2

private theorem cToFF_injective : Function.Injective cToFF := by
  intro x y hxy
  rw [cToFF, RingHom.comp_apply, RingHom.comp_apply] at hxy
  exact MvPolynomial.C_injective (Fin 2) ℂ
    (IsFractionRing.injective (MvPolynomial (Fin 2) ℂ) FF hxy)

/-- `aᵢ` as a product of single-eigenvalue linear factors. -/
theorem aFac_eq_prod (i : Fin m) : S.aFac i = ∏ lam ∈ S.Lam i,
    (mono (S.v i) - AddMonoidAlgebra.single (0 : ℤ × ℤ) (cToFF lam)) := by
  have h0 : S.aFac i = toFF (∏ lam ∈ S.Lam i, linFactor (S.v i) lam) := rfl
  rw [h0, ← toFFHom_apply, map_prod]
  exact Finset.prod_congr rfl fun lam _ => by rw [toFFHom_apply]; exact toFF_linFactor (S.v i) lam

/-- `cᵢ` as a product of single-eigenvalue linear factors. -/
private theorem cFac_eq_prod (i : Fin m) : S.cFac i = ∏ lam ∈ S.Lam i,
    (AddMonoidAlgebra.single (-(S.v i)) (Xmono (S.v i))
      - AddMonoidAlgebra.single (0 : ℤ × ℤ) (cToFF lam)) := by
  have h0 : S.cFac i = subXY (∏ lam ∈ S.Lam i, linFactor (S.v i) lam) := rfl
  rw [h0, ← subXYHom_apply, map_prod]
  exact Finset.prod_congr rfl fun lam _ => by
    rw [subXYHom_apply]; exact subXY_linFactor (S.v i) lam

/-- `c = ∏ⱼ cⱼ`. -/
private theorem cElt_eq_prod : S.cElt = ∏ j, S.cFac j := by
  have h0 : S.cElt = subXY (∏ j, S.Afac j) := rfl
  rw [h0, ← subXYHom_apply, map_prod]
  exact Finset.prod_congr rfl fun j _ => by rw [subXYHom_apply]; rfl

/-- Step 1 (i), extracted: `aᵢ` and `cᵢ` are coprime. -/
private theorem isCoprime_aFac_cFac (i : Fin m) : IsCoprime (S.aFac i) (S.cFac i) := by
  rw [aFac_eq_prod, cFac_eq_prod]
  apply IsCoprime.prod_left
  intro lam _
  apply IsCoprime.prod_right
  intro mu _
  refine isCoprime_linFactor_step (c := Xmono (S.v i) - cToFF lam * cToFF mu) rfl ?_
  intro hcontra
  have heq : Xmono (S.v i) = cToFF lam * cToFF mu := sub_eq_zero.mp hcontra
  exact Xmono_not_mem_range (S.primitive i).ne_zero ⟨lam * mu, by rw [map_mul, ← heq]⟩

/-- If `a ∈ J` and `a, x` are coprime, `x` is a unit mod `J`. -/
private theorem isUnit_mk_of_isCoprime_mem {J : Ideal (LaurentTwo FF)} {a x : LaurentTwo FF}
    (hcop : IsCoprime a x) (ha : a ∈ J) : IsUnit (Ideal.Quotient.mk J x) := by
  obtain ⟨u, v, huv⟩ := hcop
  have hmem : x * v - 1 ∈ J := by
    have heq : x * v - 1 = -(u * a) := by rw [← huv]; ring
    rw [heq]; exact J.neg_mem (Ideal.mul_mem_left J u ha)
  have hxv : Ideal.Quotient.mk J (x * v) = 1 := by
    have := Ideal.Quotient.eq_zero_iff_mem.2 hmem
    rwa [map_sub, map_one, sub_eq_zero] at this
  refine isUnit_iff_exists.2 ⟨Ideal.Quotient.mk J v, ?_, ?_⟩
  · rw [← map_mul]; exact hxv
  · rw [mul_comm (Ideal.Quotient.mk J v) (Ideal.Quotient.mk J x), ← map_mul]; exact hxv

/-- If `x` is a unit mod `J`, then `span {x} ⊔ J = ⊤`. -/
private theorem span_sup_eq_top_of_isUnit_mk {J : Ideal (LaurentTwo FF)} {x : LaurentTwo FF}
    (h : IsUnit (Ideal.Quotient.mk J x)) : Ideal.span {x} ⊔ J = ⊤ := by
  obtain ⟨y, hy⟩ := h.exists_right_inv
  obtain ⟨y', rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [← map_mul, show (1 : LaurentTwo FF ⧸ J) = Ideal.Quotient.mk J 1 from (map_one _).symm,
    Ideal.Quotient.mk_eq_mk_iff_sub_mem] at hy
  have h1 : (1 : LaurentTwo FF) ∈ Ideal.span {x} ⊔ J := by
    have hmem : (1 : LaurentTwo FF) = x * y' - (x * y' - 1) := by ring
    rw [hmem]
    exact Submodule.sub_mem _ (Ideal.mem_sup_left (Ideal.mem_span_singleton.2 ⟨y', rfl⟩))
      (Ideal.mem_sup_right hy)
  exact (Ideal.eq_top_iff_one _).2 h1

/-- Products of units mod `J` are units mod `J`. -/
private theorem isUnit_mk_prod {ι : Type*} [DecidableEq ι] (T : Finset ι) (f : ι → LaurentTwo FF)
    {J : Ideal (LaurentTwo FF)} (hf : ∀ a ∈ T, IsUnit (Ideal.Quotient.mk J (f a))) :
    IsUnit (Ideal.Quotient.mk J (∏ a ∈ T, f a)) := by
  classical
  induction T using Finset.induction with
  | empty => simp
  | @insert a T' ha ih =>
    rw [Finset.prod_insert ha, map_mul]
    exact (hf a (Finset.mem_insert_self a T')).mul
      (ih fun b hb => hf b (Finset.mem_insert_of_mem hb))

/-- Step 1 (ii) of Lemma 5.2: for `i ≠ k` the ideal `(aᵢ, a_k, c)` is the unit ideal.

**Proof sketch.** Set `J = (aᵢ, a_k)`. Every `cⱼ` is a unit mod `J`: for `j = i, k` this is
`isCoprime_aFac_cFac` together with `aⱼ ∈ J`; for `j ∉ {i, k}` each single-eigenvalue factor
`X^{vⱼ} Y^{-vⱼ} - μ` of `cⱼ` is a unit mod `J` by `isUnit_mk_cFacFactor_of_nonparallel` (using
`det(vᵢ, v_k) ≠ 0`), and these combine over `Λᵢ`, `Λ_k` (CRT gluing) and then over `Λⱼ`
(products of units). Finally `c = ∏ⱼ cⱼ` is a unit mod `J`, so `(c) + J = ⊤`. -/
theorem aFac_aFac_cElt_span_top {i k : Fin m} (hik : i ≠ k) :
    Ideal.span {S.aFac i, S.aFac k, S.cElt} = ⊤ := by
  classical
  set J : Ideal (LaurentTwo FF) := Ideal.span {S.aFac i, S.aFac k} with hJ
  suffices h : IsUnit (Ideal.Quotient.mk J S.cElt) by
    have htop := span_sup_eq_top_of_isUnit_mk h
    have hJspan : J = Ideal.span {S.aFac i} ⊔ Ideal.span {S.aFac k} := by
      rw [hJ]; exact Ideal.span_insert (S.aFac i) {S.aFac k}
    rw [show ({S.aFac i, S.aFac k, S.cElt} : Set (LaurentTwo FF))
        = insert (S.aFac i) (insert (S.aFac k) {S.cElt}) from rfl,
      Ideal.span_insert, Ideal.span_insert, ← sup_assoc, ← hJspan, sup_comm]
    exact htop
  have haimem : S.aFac i ∈ J := Ideal.subset_span (by simp)
  have hakmem : S.aFac k ∈ J := Ideal.subset_span (by simp)
  -- `cⱼ` is a unit mod `J` for every `j`, hence so is their product `c = ∏ⱼ cⱼ`.
  have hcFacUnit : ∀ j : Fin m, IsUnit (Ideal.Quotient.mk J (S.cFac j)) := by
    intro j
    rcases eq_or_ne j i with rfl | hji
    · exact isUnit_mk_of_isCoprime_mem (S.isCoprime_aFac_cFac j) haimem
    rcases eq_or_ne j k with rfl | hjk
    · exact isUnit_mk_of_isCoprime_mem (S.isCoprime_aFac_cFac j) hakmem
    · -- `j ∉ {i, k}`: nonparallel `v i, v k`, so each linear factor of `v j` is a unit mod `J`.
      have hdik : det (S.v i) (S.v k) ≠ 0 := S.nonparallel i k hik
      have hmuUnit : ∀ mu ∈ S.Lam j, IsUnit (Ideal.Quotient.mk J
          (AddMonoidAlgebra.single (-(S.v j)) (Xmono (S.v j))
            - AddMonoidAlgebra.single (0 : ℤ × ℤ) (cToFF mu))) := by
        intro mu hmu
        have hmu0 : mu ≠ 0 := ne_zero_of_mem_rootsFinset (S.mem_Lam_iff.mp hmu).1
        -- combine over `lam2 ∈ Lam k` (fixing `lam1`), then over `lam1 ∈ Lam i`.
        have hstep2 : ∀ lam1 ∈ S.Lam i, IsUnit (Ideal.Quotient.mk
            (Ideal.span {mono (S.v i) - AddMonoidAlgebra.single (0 : ℤ × ℤ) (cToFF lam1)}
              ⊔ Ideal.span {S.aFac k})
            (AddMonoidAlgebra.single (-(S.v j)) (Xmono (S.v j))
              - AddMonoidAlgebra.single (0 : ℤ × ℤ) (cToFF mu))) := by
          intro lam1 hlam1
          have hlam10 : lam1 ≠ 0 := ne_zero_of_mem_rootsFinset (S.mem_Lam_iff.mp hlam1).1
          have hcop2 : ∀ a ∈ S.Lam k, ∀ b ∈ S.Lam k, a ≠ b →
              IsCoprime (mono (S.v k) - AddMonoidAlgebra.single (0 : ℤ × ℤ) (cToFF a))
                (mono (S.v k) - AddMonoidAlgebra.single (0 : ℤ × ℤ) (cToFF b)) :=
            fun a _ b _ hab => isCoprime_mono_sub_single0_of_ne (fun h => hab (cToFF_injective h))
          have hu2 : ∀ lam2 ∈ S.Lam k, IsUnit (Ideal.Quotient.mk
              (Ideal.span {mono (S.v k) - AddMonoidAlgebra.single (0 : ℤ × ℤ) (cToFF lam2)}
                ⊔ Ideal.span {mono (S.v i) - AddMonoidAlgebra.single (0 : ℤ × ℤ) (cToFF lam1)})
              (AddMonoidAlgebra.single (-(S.v j)) (Xmono (S.v j))
                - AddMonoidAlgebra.single (0 : ℤ × ℤ) (cToFF mu))) := by
            intro lam2 hlam2
            have hlam20 : lam2 ≠ 0 := ne_zero_of_mem_rootsFinset (S.mem_Lam_iff.mp hlam2).1
            have hunit := isUnit_mk_cFacFactor_of_nonparallel
              (v1 := S.v i) (v2 := S.v k) (v3 := S.v j) hdik (S.primitive j).ne_zero
              hlam10 hlam20 hmu0
            rwa [show ({mono (S.v i) - AddMonoidAlgebra.single (0 : ℤ × ℤ) (cToFF lam1),
                mono (S.v k) - AddMonoidAlgebra.single (0 : ℤ × ℤ) (cToFF lam2)} : Set (LaurentTwo FF))
                = insert (mono (S.v i) - AddMonoidAlgebra.single (0 : ℤ × ℤ) (cToFF lam1))
                    {mono (S.v k) - AddMonoidAlgebra.single (0 : ℤ × ℤ) (cToFF lam2)} from rfl,
              Ideal.span_insert, sup_comm] at hunit
          have hcomb := isUnit_mk_span_prod_sup hcop2 hu2
          rwa [← aFac_eq_prod, sup_comm] at hcomb
        have hcop1 : ∀ a ∈ S.Lam i, ∀ b ∈ S.Lam i, a ≠ b →
            IsCoprime (mono (S.v i) - AddMonoidAlgebra.single (0 : ℤ × ℤ) (cToFF a))
              (mono (S.v i) - AddMonoidAlgebra.single (0 : ℤ × ℤ) (cToFF b)) :=
          fun a _ b _ hab => isCoprime_mono_sub_single0_of_ne (fun h => hab (cToFF_injective h))
        have hcomb1 := isUnit_mk_span_prod_sup hcop1 hstep2
        have hJspan : Ideal.span {S.aFac i} ⊔ Ideal.span {S.aFac k} = J := by
          rw [hJ]; exact (Ideal.span_insert (S.aFac i) {S.aFac k}).symm
        rwa [← aFac_eq_prod, hJspan] at hcomb1
      have hprod := isUnit_mk_prod (S.Lam j)
        (fun mu => AddMonoidAlgebra.single (-(S.v j)) (Xmono (S.v j))
          - AddMonoidAlgebra.single (0 : ℤ × ℤ) (cToFF mu)) hmuUnit
      rwa [← cFac_eq_prod] at hprod
  have hfinal := isUnit_mk_prod (Finset.univ : Finset (Fin m)) S.cFac (fun j _ => hcFacUnit j)
  rwa [← cElt_eq_prod] at hfinal

/-- Two distinct `X/Y`-type linear factors sharing the same `v` are coprime (dual of
`isCoprime_mono_sub_single0_of_ne`). -/
private theorem isCoprime_cUnit_sub_single0_of_ne {v : ℤ × ℤ} {lam lam' : FF} (h : lam ≠ lam') :
    IsCoprime (AddMonoidAlgebra.single (-v) (Xmono v) - AddMonoidAlgebra.single (0 : ℤ × ℤ) lam)
      (AddMonoidAlgebra.single (-v) (Xmono v) - AddMonoidAlgebra.single (0 : ℤ × ℤ) lam') := by
  have hne : lam' - lam ≠ 0 := sub_ne_zero.2 (Ne.symm h)
  refine ⟨AddMonoidAlgebra.single 0 (lam' - lam)⁻¹, -AddMonoidAlgebra.single 0 (lam' - lam)⁻¹, ?_⟩
  have heq : (AddMonoidAlgebra.single (0 : ℤ × ℤ) (lam' - lam)⁻¹ : LaurentTwo FF)
      * (AddMonoidAlgebra.single (-v) (Xmono v) - AddMonoidAlgebra.single 0 lam)
      + -AddMonoidAlgebra.single (0 : ℤ × ℤ) (lam' - lam)⁻¹
        * (AddMonoidAlgebra.single (-v) (Xmono v) - AddMonoidAlgebra.single 0 lam')
      = AddMonoidAlgebra.single (0 : ℤ × ℤ) (lam' - lam)⁻¹
        * (AddMonoidAlgebra.single (0 : ℤ × ℤ) lam' - AddMonoidAlgebra.single (0 : ℤ × ℤ) lam) := by
    ring
  rw [heq, ← AddMonoidAlgebra.single_sub, AddMonoidAlgebra.single_mul_single, zero_add,
    inv_mul_cancel₀ hne]
  simp [AddMonoidAlgebra.one_def]

/-- `mono (-v)` twisted by the scalar `Xmono v` bundled as a unit; the `X/Y`-type analogue of
`monoUnit`. -/
private noncomputable def cUnit (v : ℤ × ℤ) : (LaurentTwo FF)ˣ :=
  monoUnit (-v) * single0Unit (Xmono_ne_zero v)

private theorem cUnit_val (v : ℤ × ℤ) :
    (cUnit v : LaurentTwo FF) = AddMonoidAlgebra.single (-v) (Xmono v) := by
  rw [cUnit, Units.val_mul, single0Unit_val]
  show (mono (-v) : LaurentTwo FF) * AddMonoidAlgebra.single (0 : ℤ × ℤ) (Xmono v)
      = AddMonoidAlgebra.single (-v) (Xmono v)
  rw [mono, AddMonoidAlgebra.single_mul_single, add_zero, one_mul]

private theorem cUnit_zsmul (v : ℤ × ℤ) (n : ℤ) :
    ((cUnit v ^ n : (LaurentTwo FF)ˣ) : LaurentTwo FF)
      = AddMonoidAlgebra.single (-(n • v)) (Xmono (n • v)) := by
  have hmul : (cUnit v ^ n : (LaurentTwo FF)ˣ)
      = (monoUnit (-v)) ^ n * (single0Unit (Xmono_ne_zero v)) ^ n := by
    rw [cUnit]
    exact (Commute.all (monoUnit (-v)) (single0Unit (Xmono_ne_zero v))).mul_zpow n
  rw [hmul, Units.val_mul, monoUnit_zsmul, single0Unit_zpow, smul_neg, ← Xmono_zsmul,
    mono, AddMonoidAlgebra.single_mul_single, add_zero, one_mul]

/-- `a` as a product over all `i` (dual of `cElt_eq_prod`). -/
private theorem aElt_eq_prod : S.aElt = ∏ i, S.aFac i := by
  have h0 : S.aElt = toFF (∏ i, S.Afac i) := rfl
  rw [h0, ← toFFHom_apply, map_prod]
  exact Finset.prod_congr rfl fun i _ => by rw [toFFHom_apply]; rfl

/-- Dual Step-2 factor lemma (relative to `isUnit_mk_cFacFactor_of_nonparallel`, with the roles of
the `Y`-type and `X/Y`-type factors swapped): for `v1, v2` non-parallel and `v3 ≠ 0`, the `Y`-type
linear factor of `v3` at `mu ≠ 0` is a unit modulo the ideal spanned by the `X/Y`-type linear
factors of `v1` at `lam1 ≠ 0` and of `v2` at `lam2 ≠ 0`.  Unlike the primal lemma the target here
carries no transcendental content, so no final swap/factor step is needed; instead the Cramer
congruence is multiplied by an auxiliary unit to relocate the transcendence of `Xmono (D • v3)`
into a fresh substitute `β2`. -/
private theorem isUnit_mk_aFacFactor_of_nonparallel {v1 v2 v3 : ℤ × ℤ}
    (hd : det v1 v2 ≠ 0) (hv3 : v3 ≠ 0) {lam1 lam2 mu : ℂ}
    (h1 : lam1 ≠ 0) (h2 : lam2 ≠ 0) (h3 : mu ≠ 0) :
    IsUnit (Ideal.Quotient.mk
      (Ideal.span {AddMonoidAlgebra.single (-v1) (Xmono v1)
                    - AddMonoidAlgebra.single (0 : ℤ × ℤ) (cToFF lam1),
                   AddMonoidAlgebra.single (-v2) (Xmono v2)
                    - AddMonoidAlgebra.single (0 : ℤ × ℤ) (cToFF lam2)})
      (mono v3 - AddMonoidAlgebra.single (0 : ℤ × ℤ) (cToFF mu))) := by
  set J : Ideal (LaurentTwo FF) :=
    Ideal.span {AddMonoidAlgebra.single (-v1) (Xmono v1)
                  - AddMonoidAlgebra.single (0 : ℤ × ℤ) (cToFF lam1),
                AddMonoidAlgebra.single (-v2) (Xmono v2)
                  - AddMonoidAlgebra.single (0 : ℤ × ℤ) (cToFF lam2)}
    with hJ
  set D : ℤ := det v1 v2 with hDdef
  set n1 : ℤ := det v3 v2 with hn1def
  set n2 : ℤ := det v1 v3 with hn2def
  have hcramer : D • v3 = n1 • v1 + n2 • v2 := det_smul_eq v1 v2 v3
  have hf1 : AddMonoidAlgebra.single (-v1) (Xmono v1)
      - AddMonoidAlgebra.single (0 : ℤ × ℤ) (cToFF lam1) ∈ J := by
    rw [hJ]; exact Ideal.subset_span (by simp)
  have hf2 : AddMonoidAlgebra.single (-v2) (Xmono v2)
      - AddMonoidAlgebra.single (0 : ℤ × ℤ) (cToFF lam2) ∈ J := by
    rw [hJ]; exact Ideal.subset_span (by simp)
  set c1 := cUnit v1
  set c2 := cUnit v2
  set a1 := single0Unit (cToFF_ne_zero h1)
  set a2 := single0Unit (cToFF_ne_zero h2)
  have hc1sub : (c1 : LaurentTwo FF) - (a1 : LaurentTwo FF) ∈ J := by
    rw [show ((c1 : LaurentTwo FF)) = AddMonoidAlgebra.single (-v1) (Xmono v1) from cUnit_val v1,
      show ((a1 : LaurentTwo FF)) = AddMonoidAlgebra.single (0 : ℤ × ℤ) (cToFF lam1) from
        single0Unit_val _]
    exact hf1
  have hc2sub : (c2 : LaurentTwo FF) - (a2 : LaurentTwo FF) ∈ J := by
    rw [show ((c2 : LaurentTwo FF)) = AddMonoidAlgebra.single (-v2) (Xmono v2) from cUnit_val v2,
      show ((a2 : LaurentTwo FF)) = AddMonoidAlgebra.single (0 : ℤ × ℤ) (cToFF lam2) from
        single0Unit_val _]
    exact hf2
  have hp1 : ((c1 ^ n1 : (LaurentTwo FF)ˣ) : LaurentTwo FF)
      - ((a1 ^ n1 : (LaurentTwo FF)ˣ) : LaurentTwo FF) ∈ J := zpow_sub_mem_of_sub_mem hc1sub n1
  have hp2 : ((c2 ^ n2 : (LaurentTwo FF)ˣ) : LaurentTwo FF)
      - ((a2 ^ n2 : (LaurentTwo FF)ˣ) : LaurentTwo FF) ∈ J := zpow_sub_mem_of_sub_mem hc2sub n2
  have hprodmem : ((c1 ^ n1 : (LaurentTwo FF)ˣ) : LaurentTwo FF)
        * ((c2 ^ n2 : (LaurentTwo FF)ˣ) : LaurentTwo FF)
      - ((a1 ^ n1 : (LaurentTwo FF)ˣ) : LaurentTwo FF)
        * ((a2 ^ n2 : (LaurentTwo FF)ˣ) : LaurentTwo FF) ∈ J := sub_mul_sub_mem hp1 hp2
  set nu : ℂ := lam1 ^ n1 * lam2 ^ n2 with hnu
  have ha1val : ((a1 ^ n1 : (LaurentTwo FF)ˣ) : LaurentTwo FF)
      = AddMonoidAlgebra.single (0 : ℤ × ℤ) (cToFF lam1 ^ n1) := single0Unit_zpow _ n1
  have ha2val : ((a2 ^ n2 : (LaurentTwo FF)ˣ) : LaurentTwo FF)
      = AddMonoidAlgebra.single (0 : ℤ × ℤ) (cToFF lam2 ^ n2) := single0Unit_zpow _ n2
  have hmulval : (AddMonoidAlgebra.single (0 : ℤ × ℤ) (cToFF lam1 ^ n1) : LaurentTwo FF)
      * AddMonoidAlgebra.single (0 : ℤ × ℤ) (cToFF lam2 ^ n2)
      = AddMonoidAlgebra.single (0 : ℤ × ℤ) (cToFF nu) := by
    rw [AddMonoidAlgebra.single_mul_single, zero_add, hnu, map_mul, map_zpow₀, map_zpow₀]
  have hc1val : ((c1 ^ n1 : (LaurentTwo FF)ˣ) : LaurentTwo FF)
      = AddMonoidAlgebra.single (-(n1 • v1)) (Xmono (n1 • v1)) := cUnit_zsmul v1 n1
  have hc2val : ((c2 ^ n2 : (LaurentTwo FF)ˣ) : LaurentTwo FF)
      = AddMonoidAlgebra.single (-(n2 • v2)) (Xmono (n2 • v2)) := cUnit_zsmul v2 n2
  have hcprod : (AddMonoidAlgebra.single (-(n1 • v1)) (Xmono (n1 • v1)) : LaurentTwo FF)
      * AddMonoidAlgebra.single (-(n2 • v2)) (Xmono (n2 • v2))
      = AddMonoidAlgebra.single (-(D • v3)) (Xmono (D • v3)) := by
    rw [AddMonoidAlgebra.single_mul_single, ← Xmono_add, ← neg_add, ← hcramer]
  have hDmem0 : (AddMonoidAlgebra.single (-(D • v3)) (Xmono (D • v3)) : LaurentTwo FF)
      - AddMonoidAlgebra.single (0 : ℤ × ℤ) (cToFF nu) ∈ J := by
    rw [← hcprod, ← hc1val, ← hc2val, ← hmulval, ← ha1val, ← ha2val]
    exact hprodmem
  have hnu0 : cToFF nu ≠ 0 :=
    cToFF_ne_zero (by rw [hnu]; exact mul_ne_zero (zpow_ne_zero _ h1) (zpow_ne_zero _ h2))
  set β2 : FF := Xmono (D • v3) * (cToFF nu)⁻¹ with hβ2def
  have hmultA : (mono (D • v3) : LaurentTwo FF) * AddMonoidAlgebra.single (0 : ℤ × ℤ) (cToFF nu)⁻¹
      * AddMonoidAlgebra.single (-(D • v3)) (Xmono (D • v3))
      = AddMonoidAlgebra.single (0 : ℤ × ℤ) β2 := by
    rw [mono, AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.single_mul_single, add_zero,
      add_neg_cancel, one_mul, hβ2def, mul_comm (cToFF nu)⁻¹ (Xmono (D • v3))]
  have hmultB : (mono (D • v3) : LaurentTwo FF) * AddMonoidAlgebra.single (0 : ℤ × ℤ) (cToFF nu)⁻¹
      * AddMonoidAlgebra.single (0 : ℤ × ℤ) (cToFF nu)
      = mono (D • v3) := by
    rw [mono, AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.single_mul_single, add_zero,
      add_zero, one_mul, inv_mul_cancel₀ hnu0]
  have hDmem : (mono (D • v3) : LaurentTwo FF) - AddMonoidAlgebra.single (0 : ℤ × ℤ) β2 ∈ J := by
    have hh := Ideal.mul_mem_left J
      (mono (D • v3) * AddMonoidAlgebra.single (0 : ℤ × ℤ) (cToFF nu)⁻¹) hDmem0
    rw [mul_sub, hmultA, hmultB] at hh
    have hneg := J.neg_mem hh
    rwa [neg_sub] at hneg
  have hDmem' : ((monoUnit v3 ^ D : (LaurentTwo FF)ˣ) : LaurentTwo FF)
      - AddMonoidAlgebra.single (0 : ℤ × ℤ) β2 ∈ J := by
    rw [monoUnit_zsmul]; exact hDmem
  have hDv3ne : D • v3 ≠ 0 := smul_ne_zero hd hv3
  have hne : β2 ≠ (cToFF mu) ^ D := by
    intro heq
    have hval : Xmono (D • v3) = β2 * cToFF nu := by
      rw [hβ2def, inv_mul_cancel_right₀ hnu0]
    have hstep : Xmono (D • v3) = cToFF mu ^ D * cToFF nu := by rw [hval, heq]
    have hcontra : Xmono (D • v3) ∈ Set.range cToFF :=
      ⟨mu ^ D * nu, by rw [map_mul, map_zpow₀]; exact hstep.symm⟩
    exact Xmono_not_mem_range hDv3ne hcontra
  have hmu0 : cToFF mu ≠ 0 := cToFF_ne_zero h3
  exact isUnit_mk_sub_single0_of_zpow_sub_mem (monoUnit v3) hmu0 hd hDmem' hne

/-- Step 1 (iii) of Lemma 5.2: for `j ≠ l` the ideal `(a, cⱼ, c_l)` is the unit ideal. -/
theorem aElt_cFac_cFac_span_top {j l : Fin m} (hjl : j ≠ l) :
    Ideal.span {S.aElt, S.cFac j, S.cFac l} = ⊤ := by
  classical
  set J : Ideal (LaurentTwo FF) := Ideal.span {S.cFac j, S.cFac l} with hJ
  have hjmem : S.cFac j ∈ J := by rw [hJ]; exact Ideal.subset_span (by simp)
  have hlmem : S.cFac l ∈ J := by rw [hJ]; exact Ideal.subset_span (by simp)
  have hdjl : det (S.v j) (S.v l) ≠ 0 := S.nonparallel j l hjl
  have haFacUnit : ∀ i : Fin m, IsUnit (Ideal.Quotient.mk J (S.aFac i)) := by
    intro i
    rcases eq_or_ne i j with rfl | hij
    · exact isUnit_mk_of_isCoprime_mem (S.isCoprime_aFac_cFac i).symm hjmem
    rcases eq_or_ne i l with rfl | hil
    · exact isUnit_mk_of_isCoprime_mem (S.isCoprime_aFac_cFac i).symm hlmem
    · have hivne : S.v i ≠ 0 := (S.primitive i).ne_zero
      have hlamUnit : ∀ lam ∈ S.Lam i, IsUnit (Ideal.Quotient.mk J
          (mono (S.v i) - AddMonoidAlgebra.single (0 : ℤ × ℤ) (cToFF lam))) := by
        intro lam hlam
        have hlam0 : lam ≠ 0 := ne_zero_of_mem_rootsFinset (S.mem_Lam_iff.mp hlam).1
        have hstep2 : ∀ mu1 ∈ S.Lam j, IsUnit (Ideal.Quotient.mk
            (Ideal.span {AddMonoidAlgebra.single (-(S.v j)) (Xmono (S.v j))
                - AddMonoidAlgebra.single (0 : ℤ × ℤ) (cToFF mu1)}
              ⊔ Ideal.span {S.cFac l})
            (mono (S.v i) - AddMonoidAlgebra.single (0 : ℤ × ℤ) (cToFF lam))) := by
          intro mu1 hmu1
          have hmu10 : mu1 ≠ 0 := ne_zero_of_mem_rootsFinset (S.mem_Lam_iff.mp hmu1).1
          have hu2 : ∀ mu2 ∈ S.Lam l, IsUnit (Ideal.Quotient.mk
              (Ideal.span {AddMonoidAlgebra.single (-(S.v l)) (Xmono (S.v l))
                  - AddMonoidAlgebra.single (0 : ℤ × ℤ) (cToFF mu2)}
                ⊔ Ideal.span {AddMonoidAlgebra.single (-(S.v j)) (Xmono (S.v j))
                  - AddMonoidAlgebra.single (0 : ℤ × ℤ) (cToFF mu1)})
              (mono (S.v i) - AddMonoidAlgebra.single (0 : ℤ × ℤ) (cToFF lam))) := by
            intro mu2 hmu2
            have hmu20 : mu2 ≠ 0 := ne_zero_of_mem_rootsFinset (S.mem_Lam_iff.mp hmu2).1
            have := isUnit_mk_aFacFactor_of_nonparallel hdjl hivne hmu10 hmu20 hlam0
            rwa [show ({AddMonoidAlgebra.single (-(S.v j)) (Xmono (S.v j))
                  - AddMonoidAlgebra.single (0 : ℤ × ℤ) (cToFF mu1),
                AddMonoidAlgebra.single (-(S.v l)) (Xmono (S.v l))
                  - AddMonoidAlgebra.single (0 : ℤ × ℤ) (cToFF mu2)} : Set (LaurentTwo FF))
                = insert (AddMonoidAlgebra.single (-(S.v j)) (Xmono (S.v j))
                    - AddMonoidAlgebra.single (0 : ℤ × ℤ) (cToFF mu1))
                    {AddMonoidAlgebra.single (-(S.v l)) (Xmono (S.v l))
                      - AddMonoidAlgebra.single (0 : ℤ × ℤ) (cToFF mu2)} from rfl,
              Ideal.span_insert, sup_comm] at this
          have hcopl : ∀ a ∈ S.Lam l, ∀ b ∈ S.Lam l, a ≠ b →
              IsCoprime (AddMonoidAlgebra.single (-(S.v l)) (Xmono (S.v l))
                  - AddMonoidAlgebra.single (0 : ℤ × ℤ) (cToFF a))
                (AddMonoidAlgebra.single (-(S.v l)) (Xmono (S.v l))
                  - AddMonoidAlgebra.single (0 : ℤ × ℤ) (cToFF b)) :=
            fun a _ b _ hab => isCoprime_cUnit_sub_single0_of_ne
              (fun heq => hab (cToFF_injective heq))
          have hcomb := isUnit_mk_span_prod_sup hcopl hu2
          have hprod : (∏ mu2 ∈ S.Lam l, (AddMonoidAlgebra.single (-(S.v l)) (Xmono (S.v l))
              - AddMonoidAlgebra.single (0 : ℤ × ℤ) (cToFF mu2))) = S.cFac l := by
            rw [cFac_eq_prod]
          rwa [hprod, sup_comm] at hcomb
        have hcopj : ∀ a ∈ S.Lam j, ∀ b ∈ S.Lam j, a ≠ b →
            IsCoprime (AddMonoidAlgebra.single (-(S.v j)) (Xmono (S.v j))
                - AddMonoidAlgebra.single (0 : ℤ × ℤ) (cToFF a))
              (AddMonoidAlgebra.single (-(S.v j)) (Xmono (S.v j))
                - AddMonoidAlgebra.single (0 : ℤ × ℤ) (cToFF b)) :=
          fun a _ b _ hab => isCoprime_cUnit_sub_single0_of_ne
            (fun heq => hab (cToFF_injective heq))
        have hcomb1 := isUnit_mk_span_prod_sup hcopj hstep2
        have hprod1 : (∏ mu1 ∈ S.Lam j, (AddMonoidAlgebra.single (-(S.v j)) (Xmono (S.v j))
            - AddMonoidAlgebra.single (0 : ℤ × ℤ) (cToFF mu1))) = S.cFac j := by
          rw [cFac_eq_prod]
        rw [hprod1] at hcomb1
        have hJspan : Ideal.span {S.cFac j} ⊔ Ideal.span {S.cFac l} = J := by
          rw [hJ]; exact (Ideal.span_insert (S.cFac j) {S.cFac l}).symm
        rwa [hJspan] at hcomb1
      have hprod := isUnit_mk_prod (S.Lam i)
        (fun lam => mono (S.v i) - AddMonoidAlgebra.single (0 : ℤ × ℤ) (cToFF lam)) hlamUnit
      rwa [← aFac_eq_prod] at hprod
  have hfinal := isUnit_mk_prod (Finset.univ : Finset (Fin m)) S.aFac (fun i _ => haFacUnit i)
  rw [← aElt_eq_prod] at hfinal
  have htop := span_sup_eq_top_of_isUnit_mk hfinal
  have hins : ({S.aElt, S.cFac j, S.cFac l} : Set (LaurentTwo FF))
      = insert S.aElt (insert (S.cFac j) {S.cFac l}) := rfl
  rw [hins, Ideal.span_insert (S.aElt) (insert (S.cFac j) {S.cFac l}), ← hJ]
  exact htop

/-- The parallelogram `P_{ij} = [0, dᵢ vᵢ] + [0, -dⱼ vⱼ]` containing the exponents of the
monomial spanning set of the factor `(i, j)`.  Paper (5.4). -/
noncomputable def Pij (i j : Fin m) : Set (ℝ × ℝ) :=
  latSegment (S.specDeg i) (S.v i) + latSegment (S.specDeg j) (-S.v j)

/-- The lattice points of `Z - Z`, the exponent set of Lemma 5.2. -/
noncomputable def ZsubZ : Set (ℤ × ℤ) := latticePts (S.Zono - S.Zono)

/-! ### `Pij i j ⊆ Zono - Zono` (Step (d) of Lemma 5.2) -/

/-- `toReal` sends `-w` to `-toReal w`. -/
private theorem toReal_neg' (w : ℤ × ℤ) : toReal (-w) = -toReal w := by
  simpa using toReal_sub 0 w

/-- The public description of `latSegment`, avoiding `Zonotope.lean`'s private
`mem_latSegment_iff`. -/
private theorem mem_latSegment_iff' {d : ℕ} {v : ℤ × ℤ} {x : ℝ × ℝ} :
    x ∈ latSegment d v ↔ ∃ c : ℝ, c ∈ Set.Icc (0 : ℝ) 1 ∧ c • toReal ((d : ℤ) • v) = x := by
  unfold latSegment
  rw [segment_eq_image']
  simp only [Set.mem_image, zero_add, sub_zero]

/-- The parallelogram `Pᵢⱼ` sits inside `Z - Z`: its points `a + b` (with `a` on the segment
`[0, dᵢ vᵢ]` and `b` on `[0, -dⱼ vⱼ]`) split as `z₁ - z₂` for `z₁, z₂ ∈ Z`, obtained from the
zonotope's defining sum by setting every coefficient to `0` except the one at index `i`
(resp. `j`). -/
private theorem Pij_subset_ZonoSubZono (i j : Fin m) : S.Pij i j ⊆ S.Zono - S.Zono := by
  rintro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_add.mp hx
  obtain ⟨ci, hci, rfl⟩ := mem_latSegment_iff'.mp ha
  obtain ⟨cj, hcj, rfl⟩ := mem_latSegment_iff'.mp hb
  classical
  have hb' : cj • toReal ((S.specDeg j : ℤ) • (-(S.v j)))
      = -(cj • toReal ((S.specDeg j : ℤ) • S.v j)) := by
    rw [smul_neg, toReal_neg', smul_neg]
  refine Set.mem_sub.mpr ⟨ci • toReal ((S.specDeg i : ℤ) • S.v i), ?_,
    cj • toReal ((S.specDeg j : ℤ) • S.v j), ?_, ?_⟩
  · exact mem_zonotope_iff.2 ⟨fun k => if k = i then ci else 0,
      fun k => by by_cases h : k = i <;> simp [h, hci],
      by simp⟩
  · exact mem_zonotope_iff.2 ⟨fun k => if k = j then cj else 0,
      fun k => by by_cases h : k = j <;> simp [h, hcj],
      by simp⟩
  · rw [hb']; abel

/-! ### Support bound: `supp (E aFac cFac i j) + latticePts (Pij i j) ⊆ ZsubZ`

The Minkowski-sum identity `Newt(E_ij) + P_ij = Z - Z` from the paper's Step 3, at the level of
lattice points.  `toReal_zsmul` is the `ℤ`-linearity of `toReal` (used freely by `SublatticeBasis`
under the same name, but `private` there); `exists_texp_of_supp_subset` turns a per-factor
line-support bound into an integer-coefficient decomposition of any exponent of a product;
`supp_aFac_subset`/`supp_cFac_subset` instantiate it via `Nivat.Sublattice.supp_prod_binomial_subset`
against `aFac_eq_prod`/`cFac_eq_prod`. -/

/-- `toReal` is `ℤ`-linear. -/
private theorem toReal_zsmul (n : ℤ) (z : ℤ × ℤ) : toReal (n • z) = (n : ℝ) • toReal z := by
  induction n using Int.induction_on with
  | zero => simp
  | succ k ih => rw [add_smul, one_smul, toReal_add, ih]; push_cast; module
  | pred k ih => rw [sub_smul, one_smul, toReal_sub, ih]; push_cast; module

/-- If every factor `f k` (`k ∈ T`) has support on the line `{t • w k : 0 ≤ t ≤ n k}`, then every
exponent of `∏ k ∈ T, f k` is `∑ k ∈ T, t k • w k` for some integers `t k ∈ [0, n k]`. -/
private theorem exists_texp_of_supp_subset {ι : Type*} [DecidableEq ι] (T : Finset ι)
    (f : ι → LaurentTwo FF) (w : ι → ℤ × ℤ) (n : ι → ℕ)
    (hsub : ∀ k, supp (f k) ⊆ (Finset.Icc (0 : ℤ) (n k : ℤ)).image (· • w k)) :
    ∀ e ∈ supp (∏ k ∈ T, f k), ∃ t : ι → ℤ, (∀ k ∈ T, t k ∈ Finset.Icc (0 : ℤ) (n k : ℤ)) ∧
      e = ∑ k ∈ T, t k • w k := by
  classical
  induction T using Finset.induction with
  | empty =>
    intro e he
    rw [Finset.prod_empty] at he
    have he0 : e = 0 := by
      have hmem : e ∈ ({0} : Finset (ℤ × ℤ)) := by
        simpa [supp, AddMonoidAlgebra.one_def] using he
      simpa using hmem
    exact ⟨fun _ => 0, by simp, by simp [he0]⟩
  | insert a T' ha ih =>
    intro e he
    rw [Finset.prod_insert ha] at he
    obtain ⟨e1, he1, e2, he2, rfl⟩ :=
      Finset.mem_add.mp (AddMonoidAlgebra.support_coeff_mul_subset _ _ he)
    obtain ⟨k1, hk1, hk1eq⟩ := Finset.mem_image.mp (hsub a he1)
    obtain ⟨t', ht'range, ht'eq⟩ := ih e2 he2
    refine ⟨Function.update t' a k1, ?_, ?_⟩
    · intro k hk
      rcases Finset.mem_insert.mp hk with rfl | hk'
      · simpa using hk1
      · rw [Function.update_of_ne (fun h => ha (by rw [h] at hk'; exact hk'))]
        exact ht'range k hk'
    · rw [Finset.sum_insert ha, Function.update_self]
      have hsum_eq : ∑ k ∈ T', Function.update t' a k1 k • w k = ∑ k ∈ T', t' k • w k := by
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [Function.update_of_ne (fun h => ha (by rw [h] at hk; exact hk))]
      rw [hsum_eq, ← ht'eq, ← hk1eq]

/-- `supp (aFac i)` lies on the line `{t • v i : 0 ≤ t ≤ specDeg i}`. -/
private theorem supp_aFac_subset (i : Fin m) :
    supp (S.aFac i) ⊆ (Finset.Icc (0 : ℤ) (S.specDeg i : ℤ)).image (· • S.v i) := by
  rw [S.aFac_eq_prod i]
  have h := Nivat.Sublattice.supp_prod_binomial_subset (K := FF) (v := S.v i)
    (S.primitive i).ne_zero (S.Lam i) (fun _ => (1 : FF)) cToFF
  simpa [mono, specDeg] using h

/-- `supp (cFac j)` lies on the line `{t • (-(v j)) : 0 ≤ t ≤ specDeg j}`. -/
private theorem supp_cFac_subset (j : Fin m) :
    supp (S.cFac j) ⊆ (Finset.Icc (0 : ℤ) (S.specDeg j : ℤ)).image (· • (-(S.v j))) := by
  rw [S.cFac_eq_prod j]
  have h := Nivat.Sublattice.supp_prod_binomial_subset (K := FF) (v := -(S.v j))
    (neg_ne_zero.mpr (S.primitive j).ne_zero) (S.Lam j) (fun _ => Xmono (S.v j)) cToFF
  simpa [specDeg] using h

/-- Turning a real coefficient `c ∈ [0, 1]` at index `k` and an integer `t ∈ [0, specDeg k]` at
every other index into a single zonotope-membership witness. -/
private theorem zono_mem_of_update (c : Fin m → ℝ) (hc : ∀ k, c k ∈ Set.Icc (0 : ℝ) 1) :
    ∑ k, c k • toReal ((S.specDeg k : ℤ) • S.v k) ∈ S.Zono :=
  mem_zonotope_iff.2 ⟨c, hc, rfl⟩

/-- **Support-containment lemma (Step 3(d) of Lemma 5.2)**: every exponent of `E_ij` shifted by a
lattice point of `Pij i j` lands in `ZsubZ`, i.e. `Newt(E_ij) + P_ij ⊆ Z - Z` at the lattice-point
level. -/
theorem supp_E_add_Pij_subset_ZsubZ (i j : Fin m) :
    ∀ e ∈ supp (Nivat.QuotientGlue.E S.aFac S.cFac i j), ∀ d ∈ latticePts (S.Pij i j),
      e + d ∈ S.ZsubZ := by
  classical
  intro e he d hd
  rw [Nivat.QuotientGlue.E] at he
  obtain ⟨eA, heA, eC, heC, rfl⟩ :=
    Finset.mem_add.mp (AddMonoidAlgebra.support_coeff_mul_subset _ _ he)
  obtain ⟨tA, htArange, htAeq⟩ :=
    exists_texp_of_supp_subset (Finset.univ.erase i) S.aFac S.v S.specDeg
      (fun k => S.supp_aFac_subset k) eA heA
  obtain ⟨tC, htCrange, htCeq⟩ :=
    exists_texp_of_supp_subset (Finset.univ.erase j) S.cFac (fun l => -(S.v l)) S.specDeg
      (fun l => S.supp_cFac_subset l) eC heC
  obtain ⟨ci, hci, cj, hcj, hd'⟩ := Set.mem_add.mp (mem_latticePts.mp hd)
  obtain ⟨ci', hci'range, hci'eq⟩ := mem_latSegment_iff'.mp hci
  obtain ⟨cj', hcj'range, hcj'eq⟩ := mem_latSegment_iff'.mp hcj
  -- Assemble the two zonotope coefficient vectors: `c1` collects the `A`-direction data
  -- (index `i` from `d`, every other index `k` from `eA`'s integer exponent `tA k`), `c2` the
  -- `C`-direction data (index `j` from `d`, every other index `l` from `eC`'s `tC l`).
  set c1 : Fin m → ℝ := fun k => if k = i then ci' else (tA k : ℝ) / (S.specDeg k : ℝ) with hc1def
  set c2 : Fin m → ℝ := fun k => if k = j then cj' else (tC k : ℝ) / (S.specDeg k : ℝ) with hc2def
  have hc1 : ∀ k, c1 k ∈ Set.Icc (0 : ℝ) 1 := by
    intro k
    by_cases h : k = i
    · simp [hc1def, h, hci'range]
    · have hk : k ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨h, Finset.mem_univ k⟩
      have hrange := Finset.mem_Icc.mp (htArange k hk)
      have hpos : (0 : ℝ) < (S.specDeg k : ℝ) := by exact_mod_cast S.specDeg_pos k
      have h0 : (0 : ℝ) ≤ (tA k : ℝ) := by exact_mod_cast hrange.1
      constructor
      · simp only [hc1def, if_neg h]
        positivity
      · simp only [hc1def, if_neg h]
        rw [div_le_one hpos]
        exact_mod_cast hrange.2
  have hc2 : ∀ k, c2 k ∈ Set.Icc (0 : ℝ) 1 := by
    intro k
    by_cases h : k = j
    · simp [hc2def, h, hcj'range]
    · have hk : k ∈ Finset.univ.erase j := Finset.mem_erase.mpr ⟨h, Finset.mem_univ k⟩
      have hrange := Finset.mem_Icc.mp (htCrange k hk)
      have hpos : (0 : ℝ) < (S.specDeg k : ℝ) := by exact_mod_cast S.specDeg_pos k
      have h0 : (0 : ℝ) ≤ (tC k : ℝ) := by exact_mod_cast hrange.1
      constructor
      · simp only [hc2def, if_neg h]
        positivity
      · simp only [hc2def, if_neg h]
        rw [div_le_one hpos]
        exact_mod_cast hrange.2
  have hz1 : ∑ k, c1 k • toReal ((S.specDeg k : ℤ) • S.v k) ∈ S.Zono :=
    S.zono_mem_of_update c1 hc1
  have hz2 : ∑ k, c2 k • toReal ((S.specDeg k : ℤ) • S.v k) ∈ S.Zono :=
    S.zono_mem_of_update c2 hc2
  have hstep1 : ∀ k ∈ Finset.univ.erase i,
      c1 k • toReal ((S.specDeg k : ℤ) • S.v k) = (tA k : ℝ) • toReal (S.v k) := by
    intro k hk
    have hne : k ≠ i := (Finset.mem_erase.mp hk).1
    have hpos : (S.specDeg k : ℝ) ≠ 0 := by
      have := S.specDeg_pos k; positivity
    rw [toReal_zsmul]
    simp only [hc1def, if_neg hne, smul_smul]
    congr 1
    push_cast
    field_simp
  have hstep2 : ∀ k ∈ Finset.univ.erase j,
      c2 k • toReal ((S.specDeg k : ℤ) • S.v k) = (tC k : ℝ) • toReal (S.v k) := by
    intro k hk
    have hne : k ≠ j := (Finset.mem_erase.mp hk).1
    have hpos : (S.specDeg k : ℝ) ≠ 0 := by
      have := S.specDeg_pos k; positivity
    rw [toReal_zsmul]
    simp only [hc2def, if_neg hne, smul_smul]
    congr 1
    push_cast
    field_simp
  have hz1' : ∑ k, c1 k • toReal ((S.specDeg k : ℤ) • S.v k)
      = ∑ k ∈ Finset.univ.erase i, (tA k : ℝ) • toReal (S.v k)
        + ci' • toReal ((S.specDeg i : ℤ) • S.v i) := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    congr 1
    · exact Finset.sum_congr rfl hstep1
    · simp [hc1def]
  have hz2' : ∑ k, c2 k • toReal ((S.specDeg k : ℤ) • S.v k)
      = ∑ l ∈ Finset.univ.erase j, (tC l : ℝ) • toReal (S.v l)
        + cj' • toReal ((S.specDeg j : ℤ) • S.v j) := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
    congr 1
    · exact Finset.sum_congr rfl hstep2
    · simp [hc2def]
  refine mem_latticePts.2 ?_
  rw [Set.mem_sub]
  refine ⟨_, hz1, _, hz2, ?_⟩
  rw [hz1', hz2']
  have hA : toReal (∑ k ∈ Finset.univ.erase i, tA k • S.v k)
      = ∑ k ∈ Finset.univ.erase i, (tA k : ℝ) • toReal (S.v k) := by
    rw [toReal_sum]
    exact Finset.sum_congr rfl fun k _ => toReal_zsmul (tA k) (S.v k)
  have hC : toReal (∑ l ∈ Finset.univ.erase j, tC l • (-(S.v l)))
      = -(∑ l ∈ Finset.univ.erase j, (tC l : ℝ) • toReal (S.v l)) := by
    rw [toReal_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [toReal_zsmul, toReal_neg', smul_neg]
  have hcicj : cj' • toReal ((S.specDeg j : ℤ) • (-(S.v j)))
      = -(cj' • toReal ((S.specDeg j : ℤ) • S.v j)) := by
    rw [smul_neg, toReal_neg', smul_neg]
  rw [toReal_add, toReal_add, htAeq, htCeq, hA, hC, ← hd', ← hci'eq, ← hcj'eq, hcicj]
  abel

/-! ### CRT decomposition of `R/(a, c)` over `Fin m × Fin m` (Step 2/3 of Lemma 5.2) -/

/-- `a ∈ (aᵢ)` for every `i`, since `a = ∏ᵢ aᵢ`. -/
private theorem aElt_mem_span_aFac (i : Fin m) :
    S.aElt ∈ Ideal.span ({S.aFac i} : Set (LaurentTwo FF)) := by
  rw [aElt_eq_prod]
  exact Ideal.mem_span_singleton.mpr (Finset.dvd_prod_of_mem S.aFac (Finset.mem_univ i))

/-- `c ∈ (cⱼ)` for every `j`, since `c = ∏ⱼ cⱼ`. -/
private theorem cElt_mem_span_cFac (j : Fin m) :
    S.cElt ∈ Ideal.span ({S.cFac j} : Set (LaurentTwo FF)) := by
  rw [cElt_eq_prod]
  exact Ideal.mem_span_singleton.mpr (Finset.dvd_prod_of_mem S.cFac (Finset.mem_univ j))

/-- `span {a, b} ⊔ span {c, d} = span {a, b, c, d}`. -/
private theorem span_pair_union_pair_eq (a b c d : LaurentTwo FF) :
    Ideal.span ({a, b} : Set (LaurentTwo FF)) ⊔ Ideal.span ({c, d} : Set (LaurentTwo FF))
      = Ideal.span ({a, b, c, d} : Set (LaurentTwo FF)) := by
  rw [← Ideal.span_union]
  congr 1
  ext x
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

/-- If `span {a, b, c, d} = ⊤` then `(a, b)` and `(c, d)` are coprime. -/
private theorem isCoprime_of_span_quad_eq_top {a b c d : LaurentTwo FF}
    (h : Ideal.span ({a, b, c, d} : Set (LaurentTwo FF)) = ⊤) :
    IsCoprime (Ideal.span ({a, b} : Set (LaurentTwo FF)))
      (Ideal.span ({c, d} : Set (LaurentTwo FF))) := by
  rw [Ideal.isCoprime_iff_sup_eq, span_pair_union_pair_eq]
  exact h

/-- The ideal `(aᵢ, cⱼ)`, indexed by pairs. -/
private noncomputable def Ifac (p : Fin m × Fin m) : Ideal (LaurentTwo FF) :=
  Ideal.span ({S.aFac p.1, S.cFac p.2} : Set (LaurentTwo FF))

/-- The diagonal factors are the unit ideal (Step 1 (i)). -/
private theorem Ifac_diag (i : Fin m) : S.Ifac (i, i) = ⊤ := S.aFac_cFac_span_top i

/-- **Step 1 of Lemma 5.2, assembled**: the family `(aᵢ, cⱼ)`, indexed by pairs `(i, j)`, is
pairwise coprime.  For `(i, j) ≠ (k, l)` either `i ≠ k` or `j ≠ l`; the first case is handled by
`aFac_aFac_cElt_span_top` (using `c ∈ (cₗ)`), the second by `aElt_cFac_cFac_span_top` (using
`a ∈ (aᵢ)`) — either fact alone gives the 4-generator unit ideal needed. -/
private theorem isCoprime_Ifac_of_ne {p q : Fin m × Fin m} (hpq : p ≠ q) :
    IsCoprime (S.Ifac p) (S.Ifac q) := by
  obtain ⟨i, j⟩ := p
  obtain ⟨k, l⟩ := q
  show IsCoprime (Ideal.span ({S.aFac i, S.cFac j} : Set (LaurentTwo FF)))
    (Ideal.span ({S.aFac k, S.cFac l} : Set (LaurentTwo FF)))
  by_cases hjl : j = l
  · have hik : i ≠ k := fun h => hpq (by rw [h, hjl])
    apply isCoprime_of_span_quad_eq_top
    have htop : Ideal.span ({S.aFac i, S.aFac k, S.cElt} : Set (LaurentTwo FF)) = ⊤ :=
      S.aFac_aFac_cElt_span_top hik
    have hsub : Ideal.span ({S.aFac i, S.aFac k, S.cElt} : Set (LaurentTwo FF))
        ≤ Ideal.span ({S.aFac i, S.cFac j, S.aFac k, S.cFac l} : Set (LaurentTwo FF)) := by
      rw [Ideal.span_le]
      rintro x (rfl | rfl | rfl)
      · exact Ideal.subset_span (by simp)
      · exact Ideal.subset_span (by simp)
      · exact Ideal.span_mono (Set.singleton_subset_iff.mpr (by simp))
          (S.cElt_mem_span_cFac l)
    exact top_le_iff.mp (htop ▸ hsub)
  · apply isCoprime_of_span_quad_eq_top
    have htop : Ideal.span ({S.aElt, S.cFac j, S.cFac l} : Set (LaurentTwo FF)) = ⊤ :=
      S.aElt_cFac_cFac_span_top hjl
    have hsub : Ideal.span ({S.aElt, S.cFac j, S.cFac l} : Set (LaurentTwo FF))
        ≤ Ideal.span ({S.aFac i, S.cFac j, S.aFac k, S.cFac l} : Set (LaurentTwo FF)) := by
      rw [Ideal.span_le]
      rintro x (rfl | rfl | rfl)
      · exact Ideal.span_mono (Set.singleton_subset_iff.mpr (by simp))
          (S.aElt_mem_span_aFac i)
      · exact Ideal.subset_span (by simp)
      · exact Ideal.subset_span (by simp)
    exact top_le_iff.mp (htop ▸ hsub)

/-- Step 1, packaged as a `Pairwise` fact over `Fin m × Fin m`, ready for
`Ideal.quotientInfRingEquivPiQuotient`/`Ideal.prod_eq_iInf_of_pairwise_isCoprime`. -/
private theorem pairwise_isCoprime_Ifac : Pairwise (Function.onFun IsCoprime S.Ifac) :=
  fun _ _ hpq => S.isCoprime_Ifac_of_ne hpq

/- **Lemma 5.2.**  As a `K`-vector space, `R/(a, c)` is spanned by the images of
`{Y^d : d ∈ (Z - Z) ∩ ℤ²}`.

Assembly plan (per lineA's pre-review; the previous naive "each factor of `∏ Ifac(i,j)` is
individually spanned by `Pij i j`'s monomials, hence so is the whole product" argument is
INVALID — spanning each factor of a product of quotient rings does not imply spanning the whole
product, see lineA's 1-D counterexample).  The paper's actual mechanism (Step 3) uses the
idempotent-like elements `E_ij := Nivat.QuotientGlue.E S.aFac S.cFac i j` (unit mod `Ifac (i,j)`
via `isCoprime_E_span_pair`, `≡ 0` mod every other `Ifac (k,l)` via `E_mem_span_pair_of_ne`):
(a) Ideal identity `⨅ (i,j), Ifac (i,j) = S.acIdeal`: via `Nivat.QuotientGlue.iInf_grid_eq_span_pair`
applied to `A := S.aFac`, `C := S.cFac` (using `haaC_of_coprime_with_prod`/
`hacc_of_coprime_with_prod` to convert `S.aFac_aFac_cElt_span_top`/`S.aElt_cFac_cFac_span_top`
into the per-factor hypotheses it needs), giving `⨅ i, ⨅ j, span{aFac i, cFac j} =
span{∏ aFac, ∏ cFac} = S.acIdeal` (via `aElt_eq_prod`/`cElt_eq_prod`); bridge the nested `⨅ i, ⨅ j`
to `⨅ p : Fin m × Fin m, Ifac p` with a small `iInf`-swap lemma.
(b) For `i ≠ j`: `Nivat.Sublattice.span_quotient_pair_of_prod` (Step 2, lineC, delivered) gives
that `R/Ifac(i,j)` is spanned by monomials `mono d`, `d ∈ latticePts (Pij i j)`; for `i = j`,
`Ifac (i,i) = ⊤` (`Ifac_diag`) so that factor is the zero ring and contributes nothing.
(c) "Spanning transport": `Nivat.QuotientGlue.span_transport` (generic, no coprimality needed) —
combine, for each `(i,j)`, the fact that
`span_K (mk Ifac(i,j) '' {E_ij * mono d : d ∈ latticePts (Pij i j)}) = ⊤` (from (b), transported
across the unit `E_ij` via `isCoprime_E_span_pair`/`IsUnit` scaling — a bijective linear map
preserves spanning sets) with `E_mem_span_pair_of_ne` (giving the "vanishes elsewhere" hypothesis)
to conclude `span_K (mk S.acIdeal '' (⋃ i j, {E_ij * mono d : d ∈ latticePts (Pij i j)})) = ⊤`.
(d) Final step: show this is `≤ span_K (mk S.acIdeal '' (mono '' S.ZsubZ))`, using that
`E_ij * mono d` is itself an `FF`-combination of monomials `mono (e + d)` for `e ∈ supp E_ij`
(since `E_ij` is a Laurent polynomial), and `supp E_ij + latticePts (Pij i j) ⊆ S.ZsubZ`
(the support-containment lemma `supp_E_add_Pij_subset_ZsubZ`, built directly in this file: via
`Nivat.Sublattice.supp_prod_binomial_subset` for the per-factor line-support bound, combined at
the real (`toReal`)/zonotope-coefficient level).
Combined with `Submodule.span_le`/`top_le_iff` this closes the goal. -/

/-- `det` is linear (up to sign) in its second argument under negation. -/
private theorem det_neg_right (u w : ℤ × ℤ) : det u (-w) = -det u w := by simp [det]; ring

omit [Fact (Nat.Prime p)] in
/-- The `A`-directions `v i`, `-(v j)` are still non-parallel for `i ≠ j` (negating one of a
non-parallel pair does not make it parallel to the other). -/
private theorem nonparallel_neg {i j : Fin m} (hij : i ≠ j) : det (S.v i) (-(S.v j)) ≠ 0 := by
  rw [det_neg_right]
  exact neg_ne_zero.mpr (S.nonparallel i j hij)

/-- Multiplication by a unit sends a spanning set to a spanning set. -/
private theorem span_mulLeft_of_isUnit {A : Type*} [CommRing A] [Algebra FF A]
    {T : Set A} (hT : Submodule.span FF T = ⊤) {u : A} (hu : IsUnit u) :
    Submodule.span FF ((fun x => u * x) '' T) = ⊤ := by
  have hbij : Function.Bijective (fun x : A => u * x) :=
    IsUnit.isUnit_iff_mulLeft_bijective.mp hu
  have hmap : Submodule.map (LinearMap.mulLeft FF u) (Submodule.span FF T)
      = Submodule.span FF ((fun x => u * x) '' T) := by
    rw [Submodule.map_span]
    congr 1
  rw [← hmap, hT, Submodule.map_top, LinearMap.range_eq_top.mpr hbij.2]

/-- `Ideal.Quotient.mk` is `FF`-linear. -/
private theorem mk_smul (I : Ideal (LaurentTwo FF)) (c : FF) (x : LaurentTwo FF) :
    Ideal.Quotient.mk I (c • x) = c • Ideal.Quotient.mk I x := by
  rw [← Ideal.Quotient.mkₐ_eq_mk FF I]
  exact map_smul (Ideal.Quotient.mkₐ FF I) c x

/-- Step 1's triple-coprimality hypotheses, in the per-factor shape needed by
`Nivat.QuotientGlue.iInf_grid_eq_span_pair`/`isCoprime_E_span_pair`. -/
private theorem haaC_all : ∀ i k, i ≠ k → ∀ j,
    Ideal.span ({S.aFac i, S.aFac k, S.cFac j} : Set (LaurentTwo FF)) = ⊤ :=
  Nivat.QuotientGlue.haaC_of_coprime_with_prod S.cElt
    (fun _i _k hik => S.aFac_aFac_cElt_span_top hik) (fun j => S.cElt_mem_span_cFac j)

private theorem hacc_all : ∀ i j l, j ≠ l →
    Ideal.span ({S.aFac i, S.cFac j, S.cFac l} : Set (LaurentTwo FF)) = ⊤ :=
  Nivat.QuotientGlue.hacc_of_coprime_with_prod S.aElt
    (fun _j _l hjl => S.aElt_cFac_cFac_span_top hjl) (fun i => S.aElt_mem_span_aFac i)

/-- Step (a): the grid infimum of the `Ifac`s is exactly `acIdeal`. -/
private theorem iInf_Ifac_eq_acIdeal : ⨅ p : Fin m × Fin m, S.Ifac p = S.acIdeal := by
  have hstep : (⨅ p : Fin m × Fin m, S.Ifac p)
      = ⨅ i, ⨅ j, Ideal.span ({S.aFac i, S.cFac j} : Set (LaurentTwo FF)) := by
    apply le_antisymm
    · exact le_iInf fun i => le_iInf fun j => iInf_le S.Ifac (i, j)
    · exact le_iInf fun p => (iInf_le _ p.1).trans (iInf_le _ p.2)
  rw [hstep, Nivat.QuotientGlue.iInf_grid_eq_span_pair S.haaC_all S.hacc_all,
    ← S.aElt_eq_prod, ← S.cElt_eq_prod]
  rfl

/-- Step (b): for `i ≠ j`, `R / Ifac(i,j)` is spanned by the monomials `mono d`,
`d ∈ latticePts (Pij i j)`. -/
private theorem hspan_off_diag {i j : Fin m} (hij : i ≠ j) :
    Submodule.span FF
        ((fun d : ℤ × ℤ => Ideal.Quotient.mk (S.Ifac (i, j)) (mono d)) ''
          latticePts (S.Pij i j)) = ⊤ := by
  have hlam_i : ∀ lam ∈ S.Lam i, cToFF lam ≠ 0 :=
    fun lam hlam => cToFF_ne_zero (ne_zero_of_mem_rootsFinset (S.mem_Lam_iff.mp hlam).1)
  have hlam_j : ∀ lam ∈ S.Lam j, cToFF lam ≠ 0 :=
    fun lam hlam => cToFF_ne_zero (ne_zero_of_mem_rootsFinset (S.mem_Lam_iff.mp hlam).1)
  have := Nivat.Sublattice.span_quotient_pair_of_prod (K := FF) (v := S.v i) (w := -(S.v j))
    (S.nonparallel_neg hij) (s := S.Lam i) (t := S.Lam j) (α := fun _ => (1 : FF)) (β := cToFF)
    (γ := fun _ => Xmono (S.v j)) (δ := cToFF)
    (fun _ _ => one_ne_zero) hlam_i (fun _ _ => Xmono_ne_zero (S.v j)) hlam_j
    (S.aFac_eq_prod i) (S.cFac_eq_prod j)
  exact this

theorem span_quotient :
    Submodule.span FF
        ((fun d : ℤ × ℤ => (Ideal.Quotient.mk S.acIdeal) (mono d)) '' S.ZsubZ) = ⊤ := by
  classical
  set T : Fin m × Fin m → Set (LaurentTwo FF) := fun p =>
    if p.1 = p.2 then (∅ : Set (LaurentTwo FF))
    else (fun d => Nivat.QuotientGlue.E S.aFac S.cFac p.1 p.2 * mono d) ''
      latticePts (S.Pij p.1 p.2) with hTdef
  have hspan : ∀ p : Fin m × Fin m,
      Submodule.span FF ((Ideal.Quotient.mk (S.Ifac p)) '' T p) = ⊤ := by
    rintro ⟨i, j⟩
    by_cases hij : i = j
    · subst hij
      have hdiag : S.Ifac (i, i) = ⊤ := S.Ifac_diag i
      have hsub : Subsingleton (LaurentTwo FF ⧸ S.Ifac (i, i)) := by
        rw [hdiag]; exact Ideal.Quotient.subsingleton_iff.mpr rfl
      exact Submodule.eq_top_iff'.mpr fun x => by
        rw [Subsingleton.elim x (0 : LaurentTwo FF ⧸ S.Ifac (i, i))]
        exact Submodule.zero_mem _
    · have hoff := S.hspan_off_diag hij
      have hcop : IsCoprime
          (Ideal.span ({Nivat.QuotientGlue.E S.aFac S.cFac i j} : Set (LaurentTwo FF)))
          (S.Ifac (i, j)) :=
        Nivat.QuotientGlue.isCoprime_E_span_pair
          (fun k hk => S.haaC_all i k hk.symm j) (fun l hl => S.hacc_all i j l hl.symm)
      obtain ⟨v, hv⟩ := Nivat.QuotientGlue.exists_inv_mod_of_isCoprime hcop
      have hu : IsUnit ((Ideal.Quotient.mk (S.Ifac (i, j)))
          (Nivat.QuotientGlue.E S.aFac S.cFac i j)) := by
        have h1 : (Ideal.Quotient.mk (S.Ifac (i, j))) (Nivat.QuotientGlue.E S.aFac S.cFac i j) *
            (Ideal.Quotient.mk (S.Ifac (i, j))) v = 1 := by
          have heq := Ideal.Quotient.eq_zero_iff_mem.mpr hv
          simpa [map_sub, map_mul, sub_eq_zero] using heq
        have h2 : (Ideal.Quotient.mk (S.Ifac (i, j))) v *
            (Ideal.Quotient.mk (S.Ifac (i, j))) (Nivat.QuotientGlue.E S.aFac S.cFac i j) = 1 := by
          rw [show (Ideal.Quotient.mk (S.Ifac (i, j))) v *
              (Ideal.Quotient.mk (S.Ifac (i, j))) (Nivat.QuotientGlue.E S.aFac S.cFac i j)
            = (Ideal.Quotient.mk (S.Ifac (i, j))) (Nivat.QuotientGlue.E S.aFac S.cFac i j) *
              (Ideal.Quotient.mk (S.Ifac (i, j))) v from by ring]
          exact h1
        exact ⟨⟨_, _, h1, h2⟩, rfl⟩
      have himg : (Ideal.Quotient.mk (S.Ifac (i, j))) '' T (i, j)
          = (fun x => (Ideal.Quotient.mk (S.Ifac (i, j)))
              (Nivat.QuotientGlue.E S.aFac S.cFac i j) * x) ''
            ((fun d => (Ideal.Quotient.mk (S.Ifac (i, j))) (mono d)) '' latticePts (S.Pij i j)) := by
        simp only [hTdef, if_neg hij, Set.image_image]
        congr 1
      rw [himg]
      exact span_mulLeft_of_isUnit (A := LaurentTwo FF ⧸ S.Ifac (i, j)) hoff hu
  have hvanish : ∀ p : Fin m × Fin m, ∀ t ∈ T p, ∀ q, q ≠ p → t ∈ S.Ifac q := by
    rintro ⟨i, j⟩ t ht ⟨k, l⟩ hqp
    by_cases hij : i = j
    · simp [hTdef, if_pos hij] at ht
    · simp only [hTdef, if_neg hij, Set.mem_image] at ht
      obtain ⟨d, _, rfl⟩ := ht
      have hne : (k, l) ≠ (i, j) := hqp
      exact Ideal.mul_mem_right _ _ (Nivat.QuotientGlue.E_mem_span_pair_of_ne hne)
  have hglue := Nivat.QuotientGlue.span_transport (K := FF) S.Ifac T hspan hvanish
  rw [S.iInf_Ifac_eq_acIdeal] at hglue
  refine top_le_iff.mp (hglue ▸ ?_)
  apply Submodule.span_le.mpr
  rintro x ⟨y, hy, rfl⟩
  obtain ⟨p, hp⟩ := Set.mem_iUnion.mp hy
  obtain ⟨i, j⟩ := p
  by_cases hij : i = j
  · subst hij; simp [hTdef, if_pos rfl] at hp
  · simp only [hTdef, if_neg hij, Set.mem_image] at hp
    obtain ⟨d, hd, rfl⟩ := hp
    have hexp : Nivat.QuotientGlue.E S.aFac S.cFac i j
        = ∑ e ∈ supp (Nivat.QuotientGlue.E S.aFac S.cFac i j),
          AddMonoidAlgebra.single e ((Nivat.QuotientGlue.E S.aFac S.cFac i j).coeff e) := by
      conv_lhs => rw [← AddMonoidAlgebra.sum_coeff_single
        (Nivat.QuotientGlue.E S.aFac S.cFac i j)]
      rfl
    have hsingle : ∀ e c, (AddMonoidAlgebra.single e c : LaurentTwo FF) = c • mono e := by
      intro e c; simp [mono]
    rw [show Nivat.QuotientGlue.E S.aFac S.cFac i j * mono d
        = ∑ e ∈ supp (Nivat.QuotientGlue.E S.aFac S.cFac i j),
          (Nivat.QuotientGlue.E S.aFac S.cFac i j).coeff e • mono (e + d) by
      conv_lhs => rw [hexp]
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun e _ => by
        rw [hsingle e, smul_mul_assoc, mono_mul_mono]]
    rw [map_sum]
    refine Submodule.sum_mem _ fun e he => ?_
    rw [mk_smul]
    refine Submodule.smul_mem _ _ ?_
    have hmem : e + d ∈ S.ZsubZ := S.supp_E_add_Pij_subset_ZsubZ i j e he d hd
    exact Submodule.subset_span ⟨e + d, hmem, rfl⟩

/-! ### §5.3 The witness lies in `Z - Z` -/

/-- The Laurent transform in `z`: `Ĵ(d; X) = ∑_z J(d, z) X^{-z} ∈ ℂ[X^±] ⊆ K`.  Paper §5.3. -/
noncomputable def Jhat (d : ℤ × ℤ) : FF :=
  ∑ z ∈ (S.Jfun_finite_support d).toFinset, cToFF (S.Jfun d z) * Xmono (-z)

theorem Jhat_eq_zero_iff (d : ℤ × ℤ) : S.Jhat d = 0 ↔ S.Jfun d = 0 := by
  classical
  set W := (S.Jfun_finite_support d).toFinset with hW_def
  set ι : MvPolynomial (Fin 2) ℂ →+* FF := algebraMap (MvPolynomial (Fin 2) ℂ) FF with hι_def
  have hXgen : ∀ k, Xgen k = ι (MvPolynomial.X k) := fun _ => rfl
  have hcToFF : ∀ x : ℂ, cToFF x = ι (MvPolynomial.C x) := fun _ => rfl
  constructor
  · intro hJhat
    funext z0
    show S.Jfun d z0 = 0
    by_cases hz0 : z0 ∈ W
    · by_contra hne
      set e1 : ℤ := W.sup' ⟨z0, hz0⟩ (fun z => z.1) with he1_def
      set e2 : ℤ := W.sup' ⟨z0, hz0⟩ (fun z => z.2) with he2_def
      have hle1 : ∀ z ∈ W, z.1 ≤ e1 := fun z hz => Finset.le_sup' _ hz
      have hle2 : ∀ z ∈ W, z.2 ≤ e2 := fun z hz => Finset.le_sup' _ hz
      set nfun : ℤ × ℤ → ℕ := fun z => (e1 - z.1).toNat with hnfun_def
      set mfun : ℤ × ℤ → ℕ := fun z => (e2 - z.2).toNat with hmfun_def
      have hn : ∀ z ∈ W, (nfun z : ℤ) = e1 - z.1 := fun z hz =>
        Int.toNat_of_nonneg (by have := hle1 z hz; omega)
      have hm : ∀ z ∈ W, (mfun z : ℤ) = e2 - z.2 := fun z hz =>
        Int.toNat_of_nonneg (by have := hle2 z hz; omega)
      have hkey : ∀ z ∈ W, Xmono (e1, e2) * Xmono (-z)
          = ι (MvPolynomial.X 0 ^ nfun z * MvPolynomial.X 1 ^ mfun z) := by
        intro z hz
        have hsum : (e1, e2) + -z = (e1 - z.1, e2 - z.2) := by
          ext <;> simp [sub_eq_add_neg]
        rw [← Xmono_add, hsum]
        show Xgen 0 ^ (e1 - z.1) * Xgen 1 ^ (e2 - z.2) = _
        rw [← hn z hz, ← hm z hz, zpow_natCast, zpow_natCast, hXgen 0, hXgen 1, ← map_pow,
          ← map_pow, ← map_mul]
      set expfun : ℤ × ℤ → Fin 2 →₀ ℕ :=
        fun z => Finsupp.single (0 : Fin 2) (nfun z) + Finsupp.single (1 : Fin 2) (mfun z)
        with hexpfun_def
      have hexp0 : ∀ z, expfun z 0 = nfun z := by
        intro z; simp [hexpfun_def]
      have hexp1 : ∀ z, expfun z 1 = mfun z := by
        intro z; simp [hexpfun_def]
      have hmono : ∀ z, (MvPolynomial.X 0 ^ nfun z * MvPolynomial.X 1 ^ mfun z :
          MvPolynomial (Fin 2) ℂ) = MvPolynomial.monomial (expfun z) 1 := by
        intro z
        rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.X_pow_eq_monomial,
          MvPolynomial.monomial_mul, mul_one, hexpfun_def]
      have hP : ι (∑ z ∈ W, MvPolynomial.C (S.Jfun d z)
          * (MvPolynomial.X 0 ^ nfun z * MvPolynomial.X 1 ^ mfun z)) = 0 := by
        rw [map_sum]
        calc ∑ z ∈ W, ι (MvPolynomial.C (S.Jfun d z)
              * (MvPolynomial.X 0 ^ nfun z * MvPolynomial.X 1 ^ mfun z))
            = ∑ z ∈ W, cToFF (S.Jfun d z) * (Xmono (e1, e2) * Xmono (-z)) := by
              refine Finset.sum_congr rfl fun z hz => ?_
              rw [hkey z hz, hcToFF, map_mul]
          _ = Xmono (e1, e2) * ∑ z ∈ W, cToFF (S.Jfun d z) * Xmono (-z) := by
              rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun z _ => by ring
          _ = Xmono (e1, e2) * S.Jhat d := rfl
          _ = 0 := by rw [hJhat, mul_zero]
      have hP0 : (∑ z ∈ W, MvPolynomial.C (S.Jfun d z)
          * (MvPolynomial.X 0 ^ nfun z * MvPolynomial.X 1 ^ mfun z) :
          MvPolynomial (Fin 2) ℂ) = 0 :=
        IsFractionRing.injective (MvPolynomial (Fin 2) ℂ) FF (hP.trans (map_zero ι).symm)
      have hcoeff0 := congrArg (MvPolynomial.coeff (expfun z0)) hP0
      rw [MvPolynomial.coeff_sum, MvPolynomial.coeff_zero] at hcoeff0
      have hterm : ∀ z ∈ W, z ≠ z0 → MvPolynomial.coeff (expfun z0)
          (MvPolynomial.C (S.Jfun d z)
            * (MvPolynomial.X 0 ^ nfun z * MvPolynomial.X 1 ^ mfun z)) = 0 := by
        intro z hz hzne
        rw [MvPolynomial.coeff_C_mul, hmono, MvPolynomial.coeff_monomial]
        have hne : expfun z ≠ expfun z0 := by
          intro heq
          apply hzne
          have h1 : nfun z = nfun z0 := by
            have := congrArg (fun f : Fin 2 →₀ ℕ => f 0) heq
            simpa [hexp0] using this
          have h2 : mfun z = mfun z0 := by
            have := congrArg (fun f : Fin 2 →₀ ℕ => f 1) heq
            simpa [hexp1] using this
          have hz1 : z.1 = z0.1 := by
            have e1z := hn z hz
            have e1z0 := hn z0 hz0
            rw [h1] at e1z
            omega
          have hz2 : z.2 = z0.2 := by
            have e2z := hm z hz
            have e2z0 := hm z0 hz0
            rw [h2] at e2z
            omega
          exact Prod.ext hz1 hz2
        rw [if_neg hne, mul_zero]
      rw [Finset.sum_eq_single_of_mem z0 hz0 hterm, MvPolynomial.coeff_C_mul, hmono,
        MvPolynomial.coeff_monomial, if_pos rfl, mul_one] at hcoeff0
      exact hne hcoeff0
    · simp only [hW_def, Set.Finite.mem_toFinset, Function.mem_support, not_not] at hz0
      exact hz0
  · intro h0
    show (∑ z ∈ W, cToFF (S.Jfun d z) * Xmono (-z)) = 0
    apply Finset.sum_eq_zero
    intro z _
    rw [h0]
    simp

/-- `Ĵ(d; X)` may be summed over any finite set containing the support of `J(d, ·)`; this is
what lets several `Ĵ(d + s; X)` be combined over one common index set. -/
theorem Jhat_eq_sum (d : ℤ × ℤ) {W : Finset (ℤ × ℤ)}
    (hW : (S.Jfun_finite_support d).toFinset ⊆ W) :
    S.Jhat d = ∑ z ∈ W, cToFF (S.Jfun d z) * Xmono (-z) :=
  Finset.sum_subset hW fun z _ hz => by
    have h0 : S.Jfun d z = 0 := by
      by_contra hne
      exact hz ((S.Jfun_finite_support d).mem_toFinset.mpr hne)
    rw [h0, map_zero, zero_mul]

/-- The shift rule `∑_z J(d, z + s) X^{-z} = X^s Ĵ(d; X)`, used to transform the second
identity of (5.1) in `z`.  Paper §5.3. -/
theorem Xmono_mul_Jhat (d s : ℤ × ℤ) {W : Finset (ℤ × ℤ)}
    (hW : ∀ z : ℤ × ℤ, S.Jfun d (z + s) ≠ 0 → z ∈ W) :
    Xmono s * S.Jhat d = ∑ z ∈ W, cToFF (S.Jfun d (z + s)) * Xmono (-z) := by
  classical
  have hsub : (S.Jfun_finite_support d).toFinset ⊆ W.image fun z => z + s := by
    intro y hy
    have hy' : S.Jfun d y ≠ 0 := (S.Jfun_finite_support d).mem_toFinset.mp hy
    refine Finset.mem_image.mpr ⟨y - s, hW (y - s) ?_, by abel⟩
    rwa [show y - s + s = y by abel]
  have hinj : Set.InjOn (fun z : ℤ × ℤ => z + s) W := fun a _ b _ h => by simpa using h
  rw [S.Jhat_eq_sum d hsub, Finset.mul_sum, Finset.sum_image hinj]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [show (-z : ℤ × ℤ) = s + -(z + s) by abel, Xmono_add]
  ring

/-- `L` kills `a`: the first identity of (5.1), transformed in `z`. -/
theorem Jhat_aElt (h11 : S.CaseTwo) (d : ℤ × ℤ) :
    (S.Aop.coeff.sum fun s A => cToFF A * S.Jhat (d + s)) = 0 := by
  classical
  obtain ⟨W, hsub⟩ : ∃ W : Finset (ℤ × ℤ), ∀ s ∈ S.Aop.coeff.support,
      (S.Jfun_finite_support (d + s)).toFinset ⊆ W :=
    ⟨S.Aop.coeff.support.biUnion fun s => (S.Jfun_finite_support (d + s)).toFinset,
      fun s hs => Finset.subset_biUnion_of_mem
        (fun s => (S.Jfun_finite_support (d + s)).toFinset) hs⟩
  rw [Finsupp.sum]
  have hstep : ∀ s ∈ S.Aop.coeff.support,
      cToFF (S.Aop.coeff s) * S.Jhat (d + s)
        = ∑ z ∈ W, cToFF (S.Aop.coeff s * S.Jfun (d + s) z) * Xmono (-z) := by
    intro s hs
    rw [S.Jhat_eq_sum (d + s) (hsub s hs), Finset.mul_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [map_mul]
    ring
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
  refine Finset.sum_eq_zero fun z _ => ?_
  rw [← Finset.sum_mul, ← map_sum]
  have h0 : ∑ s ∈ S.Aop.coeff.support, S.Aop.coeff s * S.Jfun (d + s) z = 0 :=
    S.Aop_Jfun_shift h11 d z
  rw [h0, map_zero, zero_mul]

/-- `L` kills `c`: the second identity of (5.1), transformed in `z`. -/
theorem Jhat_cElt (h11 : S.CaseTwo) (d : ℤ × ℤ) :
    (S.Aop.coeff.sum fun s A => cToFF A * Xmono s * S.Jhat (d - s)) = 0 := by
  classical
  obtain ⟨W, hsub⟩ : ∃ W : Finset (ℤ × ℤ), ∀ s ∈ S.Aop.coeff.support,
      ∀ z : ℤ × ℤ, S.Jfun (d - s) (z + s) ≠ 0 → z ∈ W := by
    refine ⟨S.Aop.coeff.support.biUnion fun s =>
      ((S.Jfun_finite_support (d - s)).toFinset.image fun y => y - s), fun s hs z hz => ?_⟩
    refine Finset.mem_biUnion.mpr ⟨s, hs, Finset.mem_image.mpr ⟨z + s, ?_, by abel⟩⟩
    exact (S.Jfun_finite_support (d - s)).mem_toFinset.mpr hz
  rw [Finsupp.sum]
  have hstep : ∀ s ∈ S.Aop.coeff.support,
      cToFF (S.Aop.coeff s) * Xmono s * S.Jhat (d - s)
        = ∑ z ∈ W, cToFF (S.Aop.coeff s * S.Jfun (d - s) (z + s)) * Xmono (-z) := by
    intro s hs
    rw [mul_assoc, S.Xmono_mul_Jhat (d - s) s (hsub s hs), Finset.mul_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [map_mul]
    ring
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
  refine Finset.sum_eq_zero fun z _ => ?_
  rw [← Finset.sum_mul, ← map_sum]
  have h0 : ∑ s ∈ S.Aop.coeff.support, S.Aop.coeff s * S.Jfun (d - s) (z + s) = 0 :=
    S.Aop_Jfun_mixed h11 d z
  rw [h0, map_zero, zero_mul]

/- **Proposition 5.3.**  There is `d ∈ (Z - Z) ∩ ℤ²` with `d ≠ 0` and `J(d, ·) ≠ 0`.

Plan: by contradiction, assume `S.Jfun d = 0` for every `d ∈ S.ZsubZ \ {0}`; combined with
`S.Jfun_zero h11 : S.Jfun 0 = 0`, `S.Jfun d = 0` for *every* `d ∈ S.ZsubZ`, hence (via
`Jhat_eq_zero_iff`) `S.Jhat d = 0` there too.  Build the `FF`-linear functional
`L : LaurentTwo FF →ₗ[FF] FF` extending `d ↦ S.Jhat d` on the basis `{mono d}`, via
`Finsupp.linearCombination FF S.Jhat` composed with the coefficient map (`LaurentTwo FF` is a
wrapper around `(ℤ × ℤ) →₀ FF`, not literally that Finsupp type, so the composition goes through
`coeffLinear`).  Show `L` kills `S.acIdeal`: unfold `aElt`/`cElt` (via `toFF`/`subXY`) into the
`Finsupp.sum`-of-shifted-singles shape handled by `Nivat.mono_mul_sum_single`, matching
`Jhat_aElt`/`Jhat_cElt` term-by-term to get `L (mono d * aElt) = 0` and `L (mono d * cElt) = 0`,
then extend by `FF`-linearity from these generators to the whole ideal.  So `L` factors through a
linear map `L'` on `LaurentTwo FF ⧸ S.acIdeal`; since `L'` is zero on the spanning set supplied by
`S.span_quotient`, `L' = 0`, i.e. `S.Jhat = 0` everywhere (via `L (mono d) = S.Jhat d`, for *every*
`d`, not just `d ∈ S.ZsubZ`), i.e. (via `Jhat_eq_zero_iff`) `S.Jfun = 0` everywhere, contradicting
`S.exists_Jfun_ne_zero h11`. -/

/-- `0 ∈ Z - Z` at the lattice-point level: `S.Zono` contains `0` (it is a zonotope), and
`Z - Z` (Minkowski difference) then contains `0 - 0 = 0`. -/
private theorem zero_mem_ZsubZ : (0 : ℤ × ℤ) ∈ S.ZsubZ := by
  show toReal (0 : ℤ × ℤ) ∈ S.Zono - S.Zono
  have h0 : (0 : ℝ × ℝ) ∈ S.Zono := zero_mem_zonotope S.specDeg S.v
  rw [toReal_zero]
  simpa using Set.sub_mem_sub h0 h0

/-- The `FF`-linear "coefficients" map `LaurentTwo FF →ₗ[FF] ((ℤ × ℤ) →₀ FF)`; `LaurentTwo FF` is
a wrapper structure around this `Finsupp` type, not the type itself, so this bridges the two. -/
private noncomputable def coeffLinear : LaurentTwo FF →ₗ[FF] ((ℤ × ℤ) →₀ FF) where
  toFun := AddMonoidAlgebra.coeff
  map_add' := AddMonoidAlgebra.coeff_add
  map_smul' := AddMonoidAlgebra.coeff_smul

private theorem coeffLinear_mono (d : ℤ × ℤ) :
    coeffLinear (mono d : LaurentTwo FF) = Finsupp.single d (1 : FF) :=
  AddMonoidAlgebra.coeff_ofCoeff _

/-- The `FF`-linear functional `Jlin(Y^d) = Ĵ(d;X)`.  Paper §5.3.

Named `Jlin`, not `L`, because `L` is already a field of the `StarConfig` structure. -/
noncomputable def Jlin : LaurentTwo FF →ₗ[FF] FF :=
  (Finsupp.linearCombination FF S.Jhat).comp coeffLinear

private theorem Jlin_mono (d : ℤ × ℤ) : S.Jlin (mono d) = S.Jhat d := by
  show Finsupp.linearCombination FF S.Jhat (coeffLinear (mono d)) = S.Jhat d
  rw [coeffLinear_mono]
  simp [Finsupp.linearCombination_single]

/-- `Jlin` distributes over `mono d *` a `Finsupp.sum` of shifted, rescaled monomials, matching
the shape both `aElt` (after unfolding `toFF`) and `cElt` (`subXY`'s definition already has this
form) are built from. -/
private theorem Jlin_mul_mono_sum {ι : Type*} (t : ι →₀ ℂ) (h : ι → ℤ × ℤ) (v : ι → ℂ → FF)
    (d : ℤ × ℤ) :
    S.Jlin (mono d * (t.sum fun s c => AddMonoidAlgebra.single (h s) (v s c)))
      = t.sum fun s c => v s c * S.Jhat (d + h s) := by
  rw [Nivat.mono_mul_sum_single, Finsupp.sum, Finsupp.sum, map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [map_smul, S.Jlin_mono, smul_eq_mul]

private theorem Jlin_mul_aElt (d : ℤ × ℤ) :
    S.Jlin (mono d * S.aElt) = S.Aop.coeff.sum fun s A => cToFF A * S.Jhat (d + s) := by
  have haElt_eq : S.aElt = S.Aop.coeff.sum fun s A => AddMonoidAlgebra.single s (cToFF A) := by
    show toFF S.Aop = _
    conv_lhs => rw [toFF, ← AddMonoidAlgebra.sum_coeff_single
      (AddMonoidAlgebra.ofCoeff (S.Aop.coeff.mapRange cToFF (map_zero _)))]
    rw [AddMonoidAlgebra.coeff_ofCoeff]
    exact Finsupp.sum_mapRange_index (fun a => by simp)
  rw [haElt_eq]
  exact S.Jlin_mul_mono_sum S.Aop.coeff id (fun _ => cToFF) d

private theorem Jlin_mul_cElt (d : ℤ × ℤ) :
    S.Jlin (mono d * S.cElt) = S.Aop.coeff.sum fun s A => cToFF A * Xmono s * S.Jhat (d - s) := by
  have hcElt_eq : S.cElt
      = S.Aop.coeff.sum fun s A => AddMonoidAlgebra.single (-s) (cToFF A * Xmono s) := rfl
  rw [hcElt_eq]
  have := S.Jlin_mul_mono_sum S.Aop.coeff Neg.neg (fun s A => cToFF A * Xmono s) d
  simpa [sub_eq_add_neg, mul_assoc] using this

private theorem Jlin_mul_aElt_zero (h11 : S.CaseTwo) (d : ℤ × ℤ) :
    S.Jlin (mono d * S.aElt) = 0 := by
  rw [S.Jlin_mul_aElt]; exact S.Jhat_aElt h11 d

private theorem Jlin_mul_cElt_zero (h11 : S.CaseTwo) (d : ℤ × ℤ) :
    S.Jlin (mono d * S.cElt) = 0 := by
  rw [S.Jlin_mul_cElt]; exact S.Jhat_cElt h11 d

private theorem Jlin_mul_aElt_zero_all (h11 : S.CaseTwo) (f : LaurentTwo FF) :
    S.Jlin (f * S.aElt) = 0 := by
  conv_lhs => rw [← AddMonoidAlgebra.sum_coeff_single f]
  rw [Finsupp.sum, Finset.sum_mul, map_sum]
  refine Finset.sum_eq_zero fun e _ => ?_
  have hsingle : (AddMonoidAlgebra.single e (f.coeff e) : LaurentTwo FF) = f.coeff e • mono e := by
    simp [mono]
  rw [hsingle, smul_mul_assoc, map_smul, S.Jlin_mul_aElt_zero h11, smul_zero]

private theorem Jlin_mul_cElt_zero_all (h11 : S.CaseTwo) (f : LaurentTwo FF) :
    S.Jlin (f * S.cElt) = 0 := by
  conv_lhs => rw [← AddMonoidAlgebra.sum_coeff_single f]
  rw [Finsupp.sum, Finset.sum_mul, map_sum]
  refine Finset.sum_eq_zero fun e _ => ?_
  have hsingle : (AddMonoidAlgebra.single e (f.coeff e) : LaurentTwo FF) = f.coeff e • mono e := by
    simp [mono]
  rw [hsingle, smul_mul_assoc, map_smul, S.Jlin_mul_cElt_zero h11, smul_zero]

private theorem Jlin_kills_acIdeal (h11 : S.CaseTwo) {x : LaurentTwo FF} (hx : x ∈ S.acIdeal) :
    S.Jlin x = 0 := by
  obtain ⟨p, q, rfl⟩ := Ideal.mem_span_pair.mp hx
  rw [map_add, S.Jlin_mul_aElt_zero_all h11, S.Jlin_mul_cElt_zero_all h11, add_zero]

private noncomputable def JlinQ (h11 : S.CaseTwo) : (LaurentTwo FF ⧸ S.acIdeal) →ₗ[FF] FF :=
  have hle : S.acIdeal.restrictScalars FF ≤ LinearMap.ker S.Jlin :=
    fun _x hx => LinearMap.mem_ker.mpr (S.Jlin_kills_acIdeal h11 hx)
  (S.acIdeal.restrictScalars FF).liftQ S.Jlin hle

private theorem JlinQ_mk (h11 : S.CaseTwo) (x : LaurentTwo FF) :
    S.JlinQ h11 (Ideal.Quotient.mk S.acIdeal x) = S.Jlin x :=
  Submodule.liftQ_apply _ _ _

theorem exists_witness (h11 : S.CaseTwo) :
    ∃ d : ℤ × ℤ, d ∈ S.ZsubZ ∧ d ≠ 0 ∧ S.Jfun d ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hall : ∀ d ∈ S.ZsubZ, S.Jfun d = 0 := by
    intro d hd
    by_cases h0 : d = 0
    · rw [h0]; exact S.Jfun_zero h11
    · exact hcon d hd h0
  have hJhat0 : ∀ d ∈ S.ZsubZ, S.Jhat d = 0 := fun d hd => (S.Jhat_eq_zero_iff d).mpr (hall d hd)
  have hJlinQ0 : S.JlinQ h11 = 0 := by
    have hsub : Submodule.span FF
          ((fun d : ℤ × ℤ => Ideal.Quotient.mk S.acIdeal (mono d)) '' S.ZsubZ)
        ≤ LinearMap.ker (S.JlinQ h11) := by
      apply Submodule.span_le.mpr
      rintro x ⟨d, hd, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, S.JlinQ_mk h11, S.Jlin_mono, hJhat0 d hd]
    rw [S.span_quotient] at hsub
    exact LinearMap.ker_eq_top.mp (top_le_iff.mp hsub)
  have hzero : ∀ d : ℤ × ℤ, S.Jhat d = 0 := by
    intro d
    have h1 : S.JlinQ h11 (Ideal.Quotient.mk S.acIdeal (mono d)) = 0 := by simp [hJlinQ0]
    rwa [S.JlinQ_mk h11, S.Jlin_mono] at h1
  obtain ⟨d0, hd0⟩ := S.exists_Jfun_ne_zero h11
  exact hd0 ((S.Jhat_eq_zero_iff d0).mp (hzero d0))


end StarConfig

end Nivat
