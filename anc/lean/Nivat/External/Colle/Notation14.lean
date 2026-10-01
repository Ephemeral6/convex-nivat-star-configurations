/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.Lemma45
import Nivat.External.Colle.OrbitClosureBasics

/-!
# Collé Notation 1.4: Aperiodicity of configurations with two nonexpansive lines

Formalization of Collé's `b3_colle2.txt:90`, a sentence buried in "Notation 1.4":

> "any configuration η ∈ A^(ℤ²) where NEXPL(η) has at least two elements can not be periodic."

This is the closing step of Claim 4.14 (`b3_colle2.txt:918-922`), which is the missing piece
blocking the axiom `Nivat.colle_region`.

## Main results

* `notMem_NonExpansiveLine_of_dot_ne_zero` (Lemma A) — if `h ∈ Per η` and `dot v h ≠ 0`,
  then `v ∉ NonExpansiveLine η`. This is expansiveness transverse to a period.
* `not_isPeriodic_of_two_nonexpansive_lines` (Lemma B = Collé `:90`) — if
  `v, v' ∈ NonExpansiveLine η` with `det v v' ≠ 0`, then `¬ IsPeriodic η`.

## Mathematical content

The key observation is that periods are inherited by orbit-closure elements
(`mem_Per_of_mem_orbitClosure`), and the definition of `NonExpansiveLine` provides
witnesses `x ≠ y` in `orbitClosure η` agreeing on a half-plane. A transverse period
extends this agreement to the entire space, forcing `x = y` — contradiction.

Two linearly independent primitive normals (`det v v' ≠ 0`) force any common period
to satisfy `dot v h = 0` and `dot v' h = 0`, which forces `h = 0`.
-/

namespace Nivat.Colle.Notation14

open Nivat Nivat.Colle Nivat.Colle45 Nivat.LE2

variable {A : Type*}

/-- `dot` is linear in the right argument under `zsmul`.  Proved locally so that this
module needs only `Lemma45` / `OrbitClosureBasics` (the same statement lives at
`Claim36.lean:347`, but importing `Claim36` here would be a heavy dependency). -/
private theorem dot_zsmul_right' (n : ℤ × ℤ) (k : ℤ) (v : ℤ × ℤ) :
    dot n (k • v) = k * dot n v := by
  simp only [dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

/-- `dot` negates in the right argument. -/
private theorem dot_neg_right' (n v : ℤ × ℤ) : dot n (-v) = -dot n v := by
  simp only [dot, Prod.fst_neg, Prod.snd_neg]; ring

/-! ## §1. Lemma A: Expansiveness transverse to a period -/

/-- **Lemma A (expansiveness transverse to a period).**
If `h ∈ Per η` and `dot v h ≠ 0`, then `v ∉ NonExpansiveLine η`.

**Proof sketch:** Take the witnesses `x ≠ y` in `orbitClosure η` agreeing on
`halfPlaneLE v 0 = {z | dot v z ≤ 0}`. Periods are inherited by orbit-closure elements,
so `h ∈ Per x` and `h ∈ Per y`. WLOG `dot v h < 0` (else use `-h`). For any `z`, pick
`k : ℕ` large enough that `dot v (z + k • h) ≤ 0` — possible because
`dot v (z + k•h) = dot v z + k * dot v h` and `dot v h < 0`. Then
`x z = x (z + k•h) = y (z + k•h) = y z`. Hence `x = y`, contradicting `x ≠ y`. -/
theorem notMem_NonExpansiveLine_of_dot_ne_zero {η : Config A} {h : ℤ × ℤ}
    (hh : h ∈ Per η) {v : ℤ × ℤ} (hv : dot v h ≠ 0) :
    v ∉ NonExpansiveLine η := by
  rintro ⟨-, x, y, hx, hy, hne, hagree⟩
  -- Periods are inherited by orbit-closure elements
  have hpx : h ∈ Per x := mem_Per_of_mem_orbitClosure hh hx
  have hpy : h ∈ Per y := mem_Per_of_mem_orbitClosure hh hy
  -- WLOG dot v h < 0 (else use -h)
  obtain ⟨p, hpp, hpy', hpneg⟩ : ∃ p : ℤ × ℤ, p ∈ Per x ∧ p ∈ Per y ∧ dot v p < 0 := by
    rcases hv.lt_or_gt with hlt | hgt
    · exact ⟨h, hpx, hpy, hlt⟩
    · have hneg : -h ∈ Per x := AddSubgroup.neg_mem (Per x) hpx
      have hnegy : -h ∈ Per y := AddSubgroup.neg_mem (Per y) hpy
      have hdot : dot v (-h) < 0 := by
        rw [dot_neg_right']; linarith
      exact ⟨-h, hneg, hnegy, hdot⟩
  -- For any z, pick k large enough that z + k•p ∈ halfPlaneLE v 0
  have hall : ∀ z : ℤ × ℤ, x z = y z := by
    intro z
    -- Need `k : ℕ` with `dot v (z + k•p) = dot v z + k * dot v p ≤ 0`.
    -- Since `dot v p ≤ -1`, `k := (dot v z).toNat` works: if `dot v z ≤ 0` then `k = 0`
    -- and the bound is immediate; otherwise `k = dot v z` and `k * dot v p ≤ -k`.
    obtain ⟨k, hmem⟩ : ∃ k : ℕ, z + (k : ℤ) • p ∈ halfPlaneLE v 0 := by
      refine ⟨(dot v z).toNat, ?_⟩
      show dot v (z + ((dot v z).toNat : ℤ) • p) ≤ 0
      rw [dot_add, dot_zsmul_right']
      by_cases hm : dot v z ≤ 0
      · have h0 : ((dot v z).toNat : ℤ) = 0 := by omega
        rw [h0]; simpa using hm
      · have hm' : 0 < dot v z := by omega
        have hk : ((dot v z).toNat : ℤ) = dot v z := Int.toNat_of_nonneg hm'.le
        rw [hk]; nlinarith
    have hkx : ((k : ℤ)) • p ∈ Per x := AddSubgroup.zsmul_mem (Per x) hpp _
    have hky : ((k : ℤ)) • p ∈ Per y := AddSubgroup.zsmul_mem (Per y) hpy' _
    calc x z
        = x (z + (k : ℤ) • p) := (Per.apply hkx z).symm
      _ = y (z + (k : ℤ) • p) := hagree _ hmem
      _ = y z := Per.apply hky z
  exact hne (funext hall)

/-! ## §2. Lemma B: Collé Notation 1.4 `:90` -/

/-- **Lemma B (= Collé Notation 1.4 `:90`).**
If `v, v' ∈ NonExpansiveLine η` with `det v v' ≠ 0`, then `¬ IsPeriodic η`.

**Proof sketch:** Suppose `h ∈ Per η` with `h ≠ 0`. Lemma A forces `dot v h = 0` and
`dot v' h = 0`. Two linearly independent normals (`det v v' ≠ 0`) annihilating `h`
force `h = 0`. Contradiction. -/
theorem not_isPeriodic_of_two_nonexpansive_lines {η : Config A}
    {v v' : ℤ × ℤ} (hv : v ∈ NonExpansiveLine η) (hv' : v' ∈ NonExpansiveLine η)
    (hdet : det v v' ≠ 0) :
    ¬ IsPeriodic η := by
  rintro ⟨h, hh, hne⟩
  -- Lemma A forces dot v h = 0
  have hdot : dot v h = 0 := by
    by_contra hc
    exact notMem_NonExpansiveLine_of_dot_ne_zero hh hc hv
  -- Lemma A forces dot v' h = 0
  have hdot' : dot v' h = 0 := by
    by_contra hc
    exact notMem_NonExpansiveLine_of_dot_ne_zero hh hc hv'
  -- Two linearly independent normals annihilating h force h = 0
  have : h = 0 := by
    -- If h ≠ 0, then det_eq_zero_of_dot_eq_zero gives det v v' = 0, contradicting hdet
    by_contra hnz
    have : det v v' = 0 :=
      det_eq_zero_of_dot_eq_zero hnz (by rw [dot_comm]; exact hdot)
        (by rw [dot_comm]; exact hdot')
    exact hdet this
  exact hne this


end Nivat.Colle.Notation14
