/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# Configurations on the integer lattice

Formalisation of §0.1 and §0.3 of *The Convex Nivat Conjecture* (Pan).

A *configuration* is a function `ℤ × ℤ → α`.  This file sets up the translation action
`T u`, the period group `Per f`, double periodicity, primitivity of a lattice vector, and
the linear forms `π v z = det v z` used throughout the paper.

## Main definitions

* `Nivat.Config` — a configuration `ℤ × ℤ → α`.
* `Nivat.T` — translation, `(T u f) z = f (z + u)`.
* `Nivat.Per` — the period group, as an `AddSubgroup (ℤ × ℤ)`.
* `Nivat.DoublyPeriodic` — `Per f` contains two linearly independent vectors.
* `Nivat.Primitive` — a lattice vector with coprime coordinates.
* `Nivat.pi` — the surjective linear form `π v`.

## Status

Complete; no `sorry`.
-/

namespace Nivat

/-- A configuration on the integer lattice with values in `α`. -/
abbrev Config (α : Type*) : Type _ := ℤ × ℤ → α

/-- The determinant of two lattice vectors: `det (a, b) (c, d) = a * d - b * c`.

Two lattice vectors are parallel exactly when this vanishes. -/
def det (u v : ℤ × ℤ) : ℤ := u.1 * v.2 - u.2 * v.1

@[simp] theorem det_self (u : ℤ × ℤ) : det u u = 0 := by simp [det]; ring

theorem det_comm (u v : ℤ × ℤ) : det u v = -det v u := by simp [det]; ring

/-- Translation of configurations: `(T u f) z = f (z + u)`.  Paper §0.3. -/
def T {α : Type*} (u : ℤ × ℤ) (f : Config α) : Config α := fun z => f (z + u)

@[simp] theorem T_apply {α : Type*} (u : ℤ × ℤ) (f : Config α) (z : ℤ × ℤ) :
    T u f z = f (z + u) := rfl

@[simp] theorem T_zero {α : Type*} (f : Config α) : T 0 f = f := by
  funext z; simp [T]

theorem T_add {α : Type*} (u v : ℤ × ℤ) (f : Config α) : T (u + v) f = T u (T v f) := by
  funext z; simp only [T_apply]; congr 1; abel

/-- The period group of a configuration: the set of `u` with `T u f = f`.  Paper §0.1. -/
def Per {α : Type*} (f : Config α) : AddSubgroup (ℤ × ℤ) where
  carrier := {u | T u f = f}
  add_mem' := by
    intro u v hu hv
    simp only [Set.mem_ofPred_eq, T, funext_iff] at *
    intro z
    rw [show z + (u + v) = z + v + u by abel, hu (z + v), hv z]
  zero_mem' := by simp
  neg_mem' := by
    intro u hu
    simp only [Set.mem_ofPred_eq, T, funext_iff] at *
    intro z
    have h := hu (z + -u)
    rw [show z + -u + u = z by abel] at h
    exact h.symm

theorem mem_Per_iff {α : Type*} {f : Config α} {u : ℤ × ℤ} :
    u ∈ Per f ↔ T u f = f := Iff.rfl

theorem Per.apply {α : Type*} {f : Config α} {u : ℤ × ℤ} (hu : u ∈ Per f) (z : ℤ × ℤ) :
    f (z + u) = f z := congrFun hu z

/-- Post-composing a configuration with any map preserves periods. -/
theorem mem_Per_comp {α β : Type*} {f : Config α} {u : ℤ × ℤ} (hu : u ∈ Per f) (g : α → β) :
    u ∈ Per (fun z => g (f z)) := by
  rw [mem_Per_iff]
  funext z
  show g (f (z + u)) = g (f z)
  rw [Per.apply hu z]

/-- A configuration is *doubly periodic* if its period group contains two linearly
independent vectors.  Paper §0.1. -/
def DoublyPeriodic {α : Type*} (f : Config α) : Prop :=
  ∃ u ∈ Per f, ∃ v ∈ Per f, det u v ≠ 0

/-- If `f` is doubly periodic then some non-zero multiple of the whole lattice consists of
periods: there is `N ≠ 0` with `N • z ∈ Per f` for every `z`.

This is the elementary substitute for "`Per f` has finite index" used in §0.3 to produce the
common period lattice `Γ`; the proof is Cramer's rule, `det u v • e₁ = v.2 • u - u.2 • v`. -/
theorem DoublyPeriodic.exists_smul_mem {α : Type*} {f : Config α} (h : DoublyPeriodic f) :
    ∃ N : ℤ, N ≠ 0 ∧ ∀ z : ℤ × ℤ, N • z ∈ Per f := by
  obtain ⟨u, hu, v, hv, hdet⟩ := h
  refine ⟨det u v, hdet, fun z => ?_⟩
  -- `det u v • z = (v.2 * z.1 - v.1 * z.2) • u + (u.1 * z.2 - u.2 * z.1) • v`
  have key : det u v • z = (v.2 * z.1 - v.1 * z.2) • u + (u.1 * z.2 - u.2 * z.1) • v := by
    have h1 : (det u v • z).1 = ((v.2 * z.1 - v.1 * z.2) • u + (u.1 * z.2 - u.2 * z.1) • v).1 := by
      simp [det, Prod.smul_def]; ring
    have h2 : (det u v • z).2 = ((v.2 * z.1 - v.1 * z.2) • u + (u.1 * z.2 - u.2 * z.1) • v).2 := by
      simp [det, Prod.smul_def]; ring
    exact Prod.ext h1 h2
  rw [key]
  exact AddSubgroup.add_mem _ (AddSubgroup.zsmul_mem _ hu _) (AddSubgroup.zsmul_mem _ hv _)

/-- A configuration is *periodic* if its period group contains a non-zero vector.  This is the
conclusion of Nivat's conjecture (Corollary 8.19), of the convex Nivat conjecture
(Theorem 8.18) and of Theorem D.1. -/
def IsPeriodic {α : Type*} (f : Config α) : Prop := ∃ u ∈ Per f, u ≠ 0

theorem DoublyPeriodic.isPeriodic {α : Type*} {f : Config α} (h : DoublyPeriodic f) :
    IsPeriodic f := by
  obtain ⟨u, hu, v, hv, hdet⟩ := h
  rcases eq_or_ne u 0 with rfl | h0
  · exact absurd (by simp [det] : det (0 : ℤ × ℤ) v = 0) hdet
  · exact ⟨u, hu, h0⟩

/-- A doubly periodic configuration has a period non-parallel to any given non-zero `w`.

This is the content of Collé's step (a) in the proof of Lemma 4.4 (`b3_colle2.txt:721-723`):
a fully periodic accumulation point admits a period `h` with `h ∦ h_ι`.  The proof is Cramer:
`w.1 • det u v = v.1 • det u w - u.1 • det v w` and its `w.2` counterpart, so if both `u` and
`v` were parallel to a non-zero `w` then `det u v = 0`, contradicting `DoublyPeriodic`. -/
theorem DoublyPeriodic.exists_period_nonparallel {α : Type*} {x : Config α}
    (h : DoublyPeriodic x) {w : ℤ × ℤ} (hw : w ≠ 0) :
    ∃ p ∈ Per x, det p w ≠ 0 := by
  obtain ⟨u, hu, v, hv, hdet⟩ := h
  by_cases huw : det u w = 0
  · by_cases hvw : det v w = 0
    · refine absurd ?_ hdet
      have h1 : w.1 * det u v = v.1 * det u w - u.1 * det v w := by
        simp only [det]; ring
      have h2 : w.2 * det u v = v.2 * det u w - u.2 * det v w := by
        simp only [det]; ring
      rw [huw, hvw] at h1 h2
      simp only [mul_zero, sub_zero] at h1 h2
      rcases eq_or_ne w.1 0 with hw1 | hw1
      · rcases eq_or_ne w.2 0 with hw2 | hw2
        · exact absurd (Prod.ext hw1 hw2) hw
        · exact (mul_eq_zero.mp h2).resolve_left hw2
      · exact (mul_eq_zero.mp h1).resolve_left hw1
    · exact ⟨v, hv, hvw⟩
  · exact ⟨u, hu, huw⟩

/-- A lattice vector is *primitive* if its coordinates are coprime.  Paper §0.1. -/
def Primitive (v : ℤ × ℤ) : Prop := IsCoprime v.1 v.2

theorem Primitive.ne_zero {v : ℤ × ℤ} (hv : Primitive v) : v ≠ 0 := by
  rintro rfl
  exact not_isCoprime_zero_zero hv

/-- A primitive vector extends to a unimodular basis: there is `u` with `det v u = 1`.
Paper §2.1, §2.2: "take `(v i, u i)` a basis of `ℤ²` with `det (v i, u i) = 1`". -/
theorem Primitive.exists_dual {v : ℤ × ℤ} (hv : Primitive v) : ∃ u : ℤ × ℤ, det v u = 1 := by
  obtain ⟨a, b, hab⟩ := hv
  refine ⟨(-b, a), ?_⟩
  simp only [det]
  linear_combination hab

/-- The coordinates of `z` in a unimodular basis `(v, u)`: `z = det z u • v + det v z • u`.
Paper §2.2: "write `z = s v i + t u i`; then `π i z = t` and `s = det (z, u i)`". -/
theorem eq_smul_add_smul {v u : ℤ × ℤ} (h : det v u = 1) (z : ℤ × ℤ) :
    z = (det z u) • v + (det v z) • u := by
  have h1 : z.1 = ((det z u) • v + (det v z) • u).1 := by
    show z.1 = (det z u) * v.1 + (det v z) * u.1
    simp only [det] at h ⊢
    linear_combination (-z.1) * h
  have h2 : z.2 = ((det z u) • v + (det v z) • u).2 := by
    show z.2 = (det z u) * v.2 + (det v z) * u.2
    simp only [det] at h ⊢
    linear_combination (-z.2) * h
  exact Prod.ext h1 h2

/-- The linear form `π v z = det v z`, surjective onto `ℤ` when `v` is primitive.
Paper §0.1 writes this `π_i` for `v = v_i`. -/
def pi (v : ℤ × ℤ) (z : ℤ × ℤ) : ℤ := det v z

@[simp] theorem pi_apply (v z : ℤ × ℤ) : pi v z = v.1 * z.2 - v.2 * z.1 := rfl

theorem pi_add (v z w : ℤ × ℤ) : pi v (z + w) = pi v z + pi v w := by
  simp [pi, det]; ring

theorem pi_smul (v : ℤ × ℤ) (c : ℤ) (z : ℤ × ℤ) : pi v (c • z) = c * pi v z := by
  simp [pi, det, Prod.smul_def]; ring

theorem pi_sub (v z w : ℤ × ℤ) : pi v (z - w) = pi v z - pi v w := by
  simp only [pi_apply, Prod.fst_sub, Prod.snd_sub]; ring

theorem pi_sum {ι : Type*} (v : ℤ × ℤ) (s : Finset ι) (f : ι → ℤ × ℤ) :
    pi v (∑ j ∈ s, f j) = ∑ j ∈ s, pi v (f j) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp [pi, det]
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, pi_add, ih]

/-- In a unimodular basis `(v, u)`, the linear form `π v` reads off the `u`-coordinate.
Paper §2.2: "write `z = s v i + t u i`; then `π i z = t`". -/
theorem pi_smul_add_smul {v u : ℤ × ℤ} (h : det v u = 1) (s t : ℤ) :
    pi v (s • v + t • u) = t := by
  rw [pi_add, pi_smul, pi_smul]
  simp only [pi, det_self, h, mul_zero, mul_one, zero_add]

/-- `π v` is surjective when `v` is primitive.  Paper §0.1. -/
theorem pi_surjective {v : ℤ × ℤ} (hv : Primitive v) : Function.Surjective (pi v) := by
  intro n
  obtain ⟨a, b, hab⟩ := hv
  refine ⟨(-(b * n), a * n), ?_⟩
  have h : v.1 * (a * n) - v.2 * -(b * n) = (a * v.1 + b * v.2) * n := by ring
  simp only [pi_apply]
  rw [h, hab, one_mul]

end Nivat
