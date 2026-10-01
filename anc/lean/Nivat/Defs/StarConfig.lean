/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.Defs.Config
import Nivat.Defs.Complexity
import Mathlib.Data.ZMod.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Finset

/-!
# Star configurations

Formalisation of §0.1 and §0.3 of *The Convex Nivat Conjecture* (Pan).

A *star configuration* is a sum `θ = ∑ i, F i` of `m ≥ 2` fields `F i : ℤ² → 𝔽_p`, each
periodic in a primitive direction `v i`, none doubly periodic, each agreeing with doubly
periodic fields on two half-planes `{π i < ℓ i}` and `{π i > r i}` (axioms (S1)–(S3)).

This file also builds the derived data of §0.3: the common period lattice `Γ`, the integers
`κ i` and the vectors `H i = κ i • v i`, which preserve `F i` and every tail field.

## Main definitions

* `Nivat.StarConfig` — the structure packaging (S1)–(S3).
* `Nivat.StarConfig.θ` — the sum `∑ i, F i`.
* `Nivat.StarConfig.Gamma` — `Γ = ⋂ j (Per (L j) ∩ Per (R j))`.
* `Nivat.StarConfig.kappa`, `Nivat.StarConfig.H` — the integers `κ i` and vectors `H i`.

## Status

Complete; no `sorry`.
-/

namespace Nivat

/-- A **star configuration**: `m ≥ 2` one-dimensionally periodic fields in pairwise
non-parallel primitive directions, none doubly periodic, each doubly periodic outside a
strip.  Paper §0.1, axioms (S1)–(S3). -/
structure StarConfig (p : ℕ) (m : ℕ) where
  /-- The primitive directions `v 1, …, v m`. -/
  v : Fin m → ℤ × ℤ
  /-- The components `F 1, …, F m`. -/
  F : Fin m → Config (ZMod p)
  /-- The tangential periods: `F i` has period `k i • v i`. -/
  k : Fin m → ℕ
  /-- The left tail fields. -/
  L : Fin m → Config (ZMod p)
  /-- The right tail fields. -/
  R : Fin m → Config (ZMod p)
  /-- The left edge of the transition strip of component `i`. -/
  ell : Fin m → ℤ
  /-- The right edge of the transition strip of component `i`. -/
  r : Fin m → ℤ
  two_le : 2 ≤ m
  primitive : ∀ i, Primitive (v i)
  nonparallel : ∀ i j, i ≠ j → det (v i) (v j) ≠ 0
  k_pos : ∀ i, 0 < k i
  /-- (S1): `F i` has period `k i • v i`. -/
  S1 : ∀ i, ((k i : ℤ) • v i) ∈ Per (F i)
  /-- (S2): `F i` is not doubly periodic. -/
  S2 : ∀ i, ¬ DoublyPeriodic (F i)
  /-- (S3): the tails are doubly periodic. -/
  S3_L_periodic : ∀ i, DoublyPeriodic (L i)
  /-- (S3): the tails are doubly periodic. -/
  S3_R_periodic : ∀ i, DoublyPeriodic (R i)
  /-- (S3): the transition strip is well formed, `ℓ i ≤ r i + 1`. -/
  S3_le : ∀ i, ell i ≤ r i + 1
  /-- (S3): `F i = L i` on the left tail region `{π i < ℓ i}`. -/
  S3_L : ∀ i z, pi (v i) z < ell i → F i z = L i z
  /-- (S3): `F i = R i` on the right tail region `{π i > r i}`. -/
  S3_R : ∀ i z, r i < pi (v i) z → F i z = R i z

namespace StarConfig

variable {p m : ℕ} (S : StarConfig p m)

/-- The star configuration itself, `θ = ∑ i, F i`.  Paper §0.1. -/
def θ : Config (ZMod p) := fun z => ∑ i, S.F i z

@[simp] theorem θ_apply (z : ℤ × ℤ) : S.θ z = ∑ i, S.F i z := rfl

/-- The left tail region `{π i < ℓ i}` of component `i`.  Paper §0.1. -/
def leftTail (i : Fin m) : Set (ℤ × ℤ) := {z | pi (S.v i) z < S.ell i}

/-- The right tail region `{π i > r i}` of component `i`.  Paper §0.1. -/
def rightTail (i : Fin m) : Set (ℤ × ℤ) := {z | S.r i < pi (S.v i) z}

/-- The common period lattice `Γ = ⋂ j (Per (L j) ∩ Per (R j))`.  Paper §0.3. -/
def Gamma : AddSubgroup (ℤ × ℤ) := ⨅ j, (Per (S.L j) ⊓ Per (S.R j))

theorem mem_Gamma_iff {u : ℤ × ℤ} :
    u ∈ S.Gamma ↔ ∀ j, u ∈ Per (S.L j) ∧ u ∈ Per (S.R j) := by
  simp [Gamma, AddSubgroup.mem_iInf, AddSubgroup.mem_inf]

/-- `Γ` contains a non-zero multiple of the whole lattice.  This is the elementary form of
"`Γ` has finite index" used in §0.3 to choose `N ∈ ℤ_{>0}` with `N ℤ² ⊆ Γ`. -/
theorem exists_smul_mem_Gamma : ∃ N : ℤ, N ≠ 0 ∧ ∀ z : ℤ × ℤ, N • z ∈ S.Gamma := by
  -- For each `j` pick non-zero `a j`, `b j` scaling the lattice into `Per (L j)`, `Per (R j)`.
  choose a ha ha' using fun j => (S.S3_L_periodic j).exists_smul_mem
  choose b hb hb' using fun j => (S.S3_R_periodic j).exists_smul_mem
  refine ⟨∏ j, a j * b j, Finset.prod_ne_zero_iff.mpr fun j _ => mul_ne_zero (ha j) (hb j),
    fun z => ?_⟩
  rw [mem_Gamma_iff]
  intro j
  have hdvd : a j * b j ∣ ∏ j', a j' * b j' := Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
  obtain ⟨c, hc⟩ := hdvd
  constructor
  · have : (∏ j', a j' * b j') • z = a j • ((b j * c) • z) := by
      rw [hc, ← mul_smul]; congr 1; ring
    rw [this]; exact ha' j _
  · have : (∏ j', a j' * b j') • z = b j • ((a j * c) • z) := by
      rw [hc, ← mul_smul]; congr 1; ring
    rw [this]; exact hb' j _

/-- The set of admissible tangential scalings for direction `i`: positive multiples of `k i`
whose product with `v i` lies in `Γ`.  Paper §0.3. -/
def kappaSet (i : Fin m) : Set ℕ :=
  {κ : ℕ | 0 < κ ∧ S.k i ∣ κ ∧ ((κ : ℤ) • S.v i) ∈ S.Gamma}

theorem kappaSet_nonempty (i : Fin m) : (S.kappaSet i).Nonempty := by
  obtain ⟨N, hN, hNmem⟩ := S.exists_smul_mem_Gamma
  refine ⟨N.natAbs * S.k i, ?_, dvd_mul_left _ _, ?_⟩
  · exact Nat.mul_pos (Int.natAbs_pos.mpr hN) (S.k_pos i)
  · have hcast : ((N.natAbs * S.k i : ℕ) : ℤ) • S.v i
        = (N.natAbs : ℤ) • ((S.k i : ℤ) • S.v i) := by
      rw [← mul_smul, Nat.cast_mul]
    rw [hcast]
    rcases Int.natAbs_eq N with h | h
    · rw [← h]; exact hNmem _
    · have hne : ((N.natAbs : ℤ)) = -N := by omega
      rw [hne, neg_smul]
      exact AddSubgroup.neg_mem _ (hNmem _)

/-- `κ i = min {κ ∈ k i ℤ_{>0} : κ v i ∈ Γ}`.  Paper §0.3. -/
noncomputable def kappa (i : Fin m) : ℕ := sInf (S.kappaSet i)

theorem kappa_mem (i : Fin m) : S.kappa i ∈ S.kappaSet i :=
  Nat.sInf_mem (S.kappaSet_nonempty i)

theorem kappa_pos (i : Fin m) : 0 < S.kappa i := (S.kappa_mem i).1

theorem k_dvd_kappa (i : Fin m) : S.k i ∣ S.kappa i := (S.kappa_mem i).2.1

/-- `H i = κ i • v i`.  Paper §0.3. -/
noncomputable def H (i : Fin m) : ℤ × ℤ := (S.kappa i : ℤ) • S.v i

theorem H_mem_Gamma (i : Fin m) : S.H i ∈ S.Gamma := (S.kappa_mem i).2.2

/-- `H i` preserves the component `F i`.  Paper §0.3 ("`H i` preserves `F i` by (S1)"). -/
theorem H_mem_Per_F (i : Fin m) : S.H i ∈ Per (S.F i) := by
  obtain ⟨c, hc⟩ := S.k_dvd_kappa i
  have hH : S.H i = (c : ℤ) • ((S.k i : ℤ) • S.v i) := by
    rw [H, hc, ← mul_smul]; congr 1; push_cast; ring
  rw [hH]
  exact AddSubgroup.zsmul_mem _ (S.S1 i) (c : ℤ)

/-- `H i` preserves every left tail field.  Paper §0.3. -/
theorem H_mem_Per_L (i j : Fin m) : S.H i ∈ Per (S.L j) :=
  ((S.mem_Gamma_iff).mp (S.H_mem_Gamma i) j).1

/-- `H i` preserves every right tail field.  Paper §0.3. -/
theorem H_mem_Per_R (i j : Fin m) : S.H i ∈ Per (S.R j) :=
  ((S.mem_Gamma_iff).mp (S.H_mem_Gamma i) j).2

/-- `H i` is a non-zero multiple of `v i`; in particular `H i ≠ 0` when `v i ≠ 0`. -/
theorem H_eq (i : Fin m) : S.H i = (S.kappa i : ℤ) • S.v i := rfl

end StarConfig

end Nivat
