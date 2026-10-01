/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.Defs.Config
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Data.Complex.Basic

/-!
# Laurent polynomials in two variables and their action on configurations

Formalisation of the ring `ℂ[T₁^±, T₂^±]` of §0.3 of *The Convex Nivat Conjecture*
(Pan), together with the action `f(T)` on configurations and **Lemma 1.2**.

The ring is realised as the additive monoid algebra `R[ℤ × ℤ]`.  Everything is stated over a
general commutative ring `R`, because §8 needs annihilators over `ℤ` and over `𝔽_p` while
§§1–7 work over `ℂ`.  Mathlib supplies that `ℂ[ℤ × ℤ]` is an integral domain: `ℤ × ℤ` has
`UniqueSums`, which gives `NoZeroDivisors` for the monoid algebra.

The paper's generating function `Ĵ(X) = ∑_z J(z) X^{-z}` appears here as `toConfig` read
backwards: `toConfig J` is the configuration `z ↦ J.coeff (-z)`.  With that convention the
action of `f(T)` becomes plain multiplication in the ring (`act_toConfig`), which is exactly
the computation in the proof of Lemma 1.2.

## Main results

* `Nivat.LaurentTwo` — the ring `R[T₁^±, T₂^±]`.
* `Nivat.act` — the action `(f(T) g)(z) = ∑_u c_u g(z + u)`.
* `Nivat.act_toConfig` — `f(T)` on configurations is multiplication in the ring.
* `Nivat.act_ne_zero` — **Lemma 1.2**: a non-zero Laurent polynomial applied to a non-zero
  function of finite support is non-zero.

## Status

Complete; no `sorry`.  Lemma 1.2, the transform and the operator calculus (`act_mul`, `act_T`,
`act_finite_support`, `act_mem_Per`, `act_mono_sub_one_eq_zero_iff`, `act_prod_mono_sub_one`)
are all proved.
-/

namespace Nivat

open AddMonoidAlgebra

/-- The ring `R[T₁^±, T₂^±]` of Laurent polynomials in two variables, realised as the
additive monoid algebra of the lattice `ℤ × ℤ`.  Paper §0.3. -/
abbrev LaurentTwo (R : Type*) [Semiring R] := AddMonoidAlgebra R (ℤ × ℤ)

/-- `ℂ[T₁^±, T₂^±]` has no zero divisors.  Paper §0.3 ("the ring is an integral domain"). -/
example : NoZeroDivisors (LaurentTwo ℂ) := inferInstance

/-- `ℂ[T₁^±, T₂^±]` is an integral domain.  Paper §0.3. -/
example : IsDomain (LaurentTwo ℂ) := inferInstance

variable {R : Type*} [CommRing R]

/-- The support of a Laurent polynomial.  Paper §0.3. -/
def supp (f : LaurentTwo R) : Finset (ℤ × ℤ) := f.coeff.support

@[simp] theorem mem_supp {f : LaurentTwo R} {u : ℤ × ℤ} : u ∈ supp f ↔ f.coeff u ≠ 0 :=
  Finsupp.mem_support_iff

/-- The configuration attached to a Laurent polynomial: `toConfig J = fun z => J.coeff (-z)`.

This is the paper's transform `Ĵ(X) = ∑_z J(z) X^{-z}` of Lemma 1.2, read as a bijection
between Laurent polynomials and finitely supported configurations. -/
def toConfig (J : LaurentTwo R) : Config R := fun z => J.coeff (-z)

@[simp] theorem toConfig_apply (J : LaurentTwo R) (z : ℤ × ℤ) :
    toConfig J z = J.coeff (-z) := rfl

theorem toConfig_eq_zero_iff (J : LaurentTwo R) : toConfig J = 0 ↔ J = 0 := by
  constructor
  · intro h
    have hc : J.coeff = 0 := by
      ext w
      have := congrFun h (-w)
      simpa using this
    exact AddMonoidAlgebra.coeff_injective (by simpa using hc)
  · rintro rfl
    funext z
    simp [toConfig]

/-- Every configuration of finite support arises as `toConfig` of a Laurent polynomial. -/
theorem exists_toConfig {g : Config R} (hg : (Function.support g).Finite) :
    ∃ J : LaurentTwo R, toConfig J = g := by
  classical
  refine ⟨AddMonoidAlgebra.ofCoeff
    (Finsupp.onFinset (hg.toFinset.image (fun w => -w)) (fun u => g (-u)) ?_), ?_⟩
  · intro u hu
    refine Finset.mem_image.mpr ⟨-u, ?_, by abel⟩
    exact hg.mem_toFinset.mpr hu
  · funext z
    simp [toConfig]

/-- The action of a Laurent polynomial on a configuration: `(f(T) g)(z) = ∑_u c_u g(z + u)`,
where `f = ∑_u c_u T^u`.  Paper §0.3. -/
def act (f : LaurentTwo R) (g : Config R) : Config R :=
  fun z => f.coeff.sum fun u c => c * g (z + u)

@[simp] theorem act_apply (f : LaurentTwo R) (g : Config R) (z : ℤ × ℤ) :
    act f g z = f.coeff.sum fun u c => c * g (z + u) := rfl

/-- Under the transform `toConfig`, the action of `f(T)` is multiplication by `f` in
`R[T₁^±, T₂^±]`.  This is the identity
`∑_z (f(T)J)(z) X^{-z} = (∑_u c_u X^u) Ĵ(X)` from the proof of Lemma 1.2. -/
theorem act_toConfig (f J : LaurentTwo R) : act f (toConfig J) = toConfig (f * J) := by
  funext z
  simp only [act_apply, toConfig_apply, AddMonoidAlgebra.coeff_mul_apply_left]
  refine Finsupp.sum_congr fun u _ => ?_
  congr 2
  abel

/-- **Lemma 1.2.**  Let `g : ℤ² → R` be non-zero with finite support, `R` a domain, and let `f`
be a non-zero Laurent polynomial.  Then `f(T) g ≠ 0`. -/
theorem act_ne_zero [NoZeroDivisors R] {f : LaurentTwo R} {g : Config R} (hf : f ≠ 0)
    (hgfin : (Function.support g).Finite) (hg : g ≠ 0) : act f g ≠ 0 := by
  obtain ⟨J, rfl⟩ := exists_toConfig hgfin
  rw [act_toConfig, Ne, toConfig_eq_zero_iff]
  have hJ : J ≠ 0 := by rwa [Ne, ← toConfig_eq_zero_iff]
  exact mul_ne_zero hf hJ

/-! ### The operator calculus

`f ↦ act f` is a ring map from `R[T₁^±, T₂^±]` to operators on configurations.  Paper §0.3
uses this silently throughout (`D = (T^{H i} - 1) Q i`, `A(T) e`, …). -/

/-- The monomial `T^u` as an element of `R[T₁^±, T₂^±]`. -/
noncomputable def mono (u : ℤ × ℤ) : LaurentTwo R := AddMonoidAlgebra.single u 1

@[simp] theorem coeff_mono (u : ℤ × ℤ) :
    (mono u : LaurentTwo R).coeff = Finsupp.single u 1 := rfl

theorem mono_mul_mono (u v : ℤ × ℤ) : (mono u : LaurentTwo R) * mono v = mono (u + v) := by
  simp [mono, AddMonoidAlgebra.single_mul_single]

@[simp] theorem mono_zero : (mono 0 : LaurentTwo R) = 1 := by
  simp [mono, AddMonoidAlgebra.one_def]

theorem mono_ne_zero [Nontrivial R] (u : ℤ × ℤ) : (mono u : LaurentTwo R) ≠ 0 := by
  simp [mono, AddMonoidAlgebra.single_eq_zero]

@[simp] theorem act_zero_left (g : Config R) : act (0 : LaurentTwo R) g = 0 := by
  funext z; simp [act, AddMonoidAlgebra.coeff_zero]

@[simp] theorem act_zero_right (f : LaurentTwo R) : act f (0 : Config R) = 0 := by
  funext z; simp [act]

theorem act_add_left (f₁ f₂ : LaurentTwo R) (g : Config R) :
    act (f₁ + f₂) g = act f₁ g + act f₂ g := by
  funext z
  simp only [act_apply, AddMonoidAlgebra.coeff_add, Pi.add_apply]
  rw [Finsupp.sum_add_index'] <;> intros <;> ring_nf

theorem act_add_right (f : LaurentTwo R) (g₁ g₂ : Config R) :
    act f (g₁ + g₂) = act f g₁ + act f g₂ := by
  funext z
  simp only [act_apply, Pi.add_apply, mul_add, Finsupp.sum]
  exact Finset.sum_add_distrib

theorem act_sub_right (f : LaurentTwo R) (g₁ g₂ : Config R) :
    act f (g₁ - g₂) = act f g₁ - act f g₂ := by
  funext z
  simp only [act_apply, Pi.sub_apply, mul_sub, Finsupp.sum, Finset.sum_sub_distrib]

/-- `f(T)` commutes with multiplication by a constant. -/
theorem act_const_mul (f : LaurentTwo R) (c : R) (g : Config R) :
    act f (fun z => c * g z) = fun z => c * act f g z := by
  funext z
  simp only [act_apply, Finsupp.sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun u _ => by ring

@[simp] theorem act_mono (u : ℤ × ℤ) (g : Config R) : act (mono u) g = T u g := by
  funext z
  simp [act, mono, Finsupp.sum_single_index]

@[simp] theorem act_one (g : Config R) : act (1 : LaurentTwo R) g = g := by
  rw [← mono_zero, act_mono, T_zero]

/-- Evaluation of the action at a single point, packaged as an additive map in the Laurent
polynomial.  This is the additivity of `f ↦ act f g` in usable form; it powers `act_mul` and
`act_sub_left`. -/
private noncomputable def actAt (g : Config R) (z : ℤ × ℤ) : LaurentTwo R →+ R :=
  AddMonoidHom.mk' (fun f => act f g z) fun f₁ f₂ => congrFun (act_add_left f₁ f₂ g) z

private theorem actAt_apply (g : Config R) (z : ℤ × ℤ) (f : LaurentTwo R) :
    actAt g z f = act f g z := rfl

private theorem actAt_single (g : Config R) (z u : ℤ × ℤ) (c : R) :
    actAt g z (AddMonoidAlgebra.single u c) = c * g (z + u) := by
  simp [actAt, act, AddMonoidAlgebra.coeff_single, Finsupp.sum_single_index]

theorem act_neg_left (f : LaurentTwo R) (g : Config R) : act (-f) g = -act f g := by
  funext z; exact map_neg (actAt g z) f

theorem act_sub_left (f₁ f₂ : LaurentTwo R) (g : Config R) :
    act (f₁ - f₂) g = act f₁ g - act f₂ g := by
  funext z; exact map_sub (actAt g z) f₁ f₂

/-- `act` is multiplicative: applying a product of Laurent polynomials is composing. -/
theorem act_mul (f₁ f₂ : LaurentTwo R) (g : Config R) :
    act (f₁ * f₂) g = act f₁ (act f₂ g) := by
  classical
  funext z
  show actAt g z (f₁ * f₂) = _
  rw [AddMonoidAlgebra.mul_def]
  simp only [map_finsuppSum, actAt_single]
  refine Finsupp.sum_congr fun u _ => ?_
  rw [act_apply, Finsupp.mul_sum]
  refine Finsupp.sum_congr fun w _ => ?_
  rw [mul_assoc, show z + u + w = z + (u + w) from by abel]

/-- Laurent operators commute with translations. -/
theorem act_T (f : LaurentTwo R) (u : ℤ × ℤ) (g : Config R) :
    act f (T u g) = T u (act f g) := by
  funext z
  simp only [act_apply, T_apply]
  refine Finsupp.sum_congr fun w _ => ?_
  rw [show z + u + w = z + w + u from by abel]

/-- A Laurent operator applied to a configuration of finite support again has finite
support. -/
theorem act_finite_support {f : LaurentTwo R} {g : Config R}
    (hg : (Function.support g).Finite) : (Function.support (act f g)).Finite := by
  classical
  have hsub : Function.support (act f g) ⊆
      ⋃ u ∈ (f.coeff.support : Set (ℤ × ℤ)), (fun w => w - u) '' Function.support g := by
    intro z hz
    simp only [Function.mem_support, act_apply, Finsupp.sum] at hz
    obtain ⟨u, hu, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hz
    exact Set.mem_biUnion (Finset.mem_coe.mpr hu)
      ⟨z + u, right_ne_zero_of_mul hne, by simp⟩
  exact (Set.Finite.biUnion f.coeff.support.finite_toSet fun u _ => hg.image _).subset hsub

/-- A Laurent operator preserves every period of its argument. -/
theorem act_mem_Per {f : LaurentTwo R} {g : Config R} {u : ℤ × ℤ} (hu : u ∈ Per g) :
    u ∈ Per (act f g) := by
  rw [mem_Per_iff, ← act_T, mem_Per_iff.mp hu]

/-- `T^u - 1` kills exactly the configurations having `u` as a period. -/
theorem act_mono_sub_one_eq_zero_iff (u : ℤ × ℤ) (g : Config R) :
    act (mono u - 1) g = 0 ↔ u ∈ Per g := by
  rw [act_sub_left, act_mono, act_one, sub_eq_zero, mem_Per_iff]

/-- The formal expansion (0.1):
`∏_{i ∈ s} (T^{H i} - 1) g (z) = ∑_{C ⊆ s} (-1)^{|s| - |C|} g (z + H_C)`,
valid as an operator identity irrespective of coincidences among the points `H_C`. -/
theorem act_prod_mono_sub_one {ι : Type*} [DecidableEq ι] (s : Finset ι) (H : ι → ℤ × ℤ)
    (g : Config R) (z : ℤ × ℤ) :
    act (∏ i ∈ s, (mono (H i) - 1)) g z
      = ∑ C ∈ s.powerset, (-1 : R) ^ (s.card - C.card) * g (z + ∑ i ∈ C, H i) := by
  classical
  induction s using Finset.induction generalizing z with
  | empty => rw [Finset.prod_empty, act_one, Finset.powerset_empty]; simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, act_mul, act_sub_left, act_mono, act_one, Pi.sub_apply, T_apply,
      ih, ih, Finset.sum_powerset_insert ha, Finset.card_insert_of_notMem ha]
    have h1 : ∑ C ∈ s.powerset, (-1 : R) ^ (s.card + 1 - C.card) * g (z + ∑ i ∈ C, H i)
        = -∑ C ∈ s.powerset, (-1 : R) ^ (s.card - C.card) * g (z + ∑ i ∈ C, H i) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun C hC => ?_
      have hcard : C.card ≤ s.card := Finset.card_le_card (Finset.mem_powerset.mp hC)
      rw [show s.card + 1 - C.card = (s.card - C.card) + 1 by omega, pow_succ]
      ring
    have h2 : ∑ C ∈ s.powerset,
          (-1 : R) ^ (s.card + 1 - (insert a C).card) * g (z + ∑ i ∈ insert a C, H i)
        = ∑ C ∈ s.powerset, (-1 : R) ^ (s.card - C.card) * g (z + H a + ∑ i ∈ C, H i) := by
      refine Finset.sum_congr rfl fun C hC => ?_
      have haC : a ∉ C := fun h => ha (Finset.mem_powerset.mp hC h)
      rw [Finset.card_insert_of_notMem haC, Finset.sum_insert haC,
        show s.card + 1 - (C.card + 1) = s.card - C.card by omega,
        show z + (H a + ∑ i ∈ C, H i) = z + H a + ∑ i ∈ C, H i by abel]
    rw [h1, h2]
    abel

end Nivat
