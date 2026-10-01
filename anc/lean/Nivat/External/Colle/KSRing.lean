/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.KSDecomposition
import Mathlib.Data.ZMod.Basic

/-!
# Kari–Szabados, Lemma 8, over an arbitrary commutative ring of coefficients

`Nivat/External/KSDecomposition.lean` proves Kari–Szabados' Lemma 8 (periodic decomposition)
only for `Config ℤ`.  This file is the generalisation to `Config R` for any `CommRing R`,
including `R = ZMod p`.

## Why this generalizes mechanically (audited 2026-09-19, confirmed here by compiling)

Two kinds of `ℤ` occur in `KSDecomposition.lean`, and only one of them needs to change:

* **lattice positions** `z, p, q, h i : ℤ × ℤ` — these index *sites* of the plane, not
  coefficient values.  `det`, `Config.T`, `Per`, `kcoord`, `basept`, `Int.ediv`/`toNat` all
  operate on this `ℤ × ℤ` and are untouched here, exactly as instructed.
* **configuration values / Laurent coefficients** `c z, η z : ℤ`, and `LaurentTwo ℤ` — this is
  the `ℤ` that becomes a generic `R`.  `Nivat.Laurent.Basic`'s `act`, `mono`, `act_mono`,
  `act_sub_left`, `act_mono_sub_one_eq_zero_iff` etc. are already stated for
  `variable {R : Type*} [CommRing R]` (`Laurent/Basic.lean:56`), so no change is needed there
  at all.  `Nivat.Defs.Config`'s `Config`, `T`, `Per`, `mem_Per_iff`, `Per.apply` are already
  generic over any type `α` (`Defs/Config.lean`), so no change is needed there either.

The only place `ℤ`-as-coefficient actually appears inside `KSDecomposition.lean`'s own code is
`antidiff : (ℤ → ℤ) → ℤ → ℤ` and everything built on it (`solve`, `act_solve`,
`solve_mem_Per`, `decomp_aux`, `kari_szabados_decomp'`).  No proof in the file uses
`NoZeroDivisors`, order, or characteristic; the recurrence is monic with constant term `-1`
(`X^q - 1`), so it inverts over *any* commutative ring, not just an integral domain.  This file
re-proves exactly the same lemmas with `a : ℤ → R`, `Config ℤ ↦ Config R`,
`LaurentTwo ℤ ↦ LaurentTwo R`, and every proof step is verbatim (`ring`/`abel`/`omega` all still
close the generalised goals, since none of them used `ℤ`-specific facts).

## Main results

* `Nivat.KSRing.exists_solve` — Lemma 7 for `f = X^q - 1`, over `Config R`.
* `Nivat.KSRing.exists_preimage_prod` — Lemma 7 iterated over a finite family.
* `Nivat.kari_szabados_decomp_ring` — Lemma 8, over `Config R`.
* `Nivat.kari_szabados_decomp_zmod` — the `R := ZMod p` instance.

## Status

Complete; no `sorry`.  Did not touch `KSDecomposition.lean` (on-chain, not this file's).
-/

namespace Nivat.KSRing

open Finset

variable {R : Type*} [CommRing R]

/-! ### The two-sided antidifference, now valued in `R` -/

/-- The two-sided antidifference of `a : ℤ → R`: `antidiff a n = ∑_{0 ≤ j < n} a j` for
`n ≥ 0`, and `antidiff a n = -∑_{n ≤ j < 0} a j` for `n < 0`. -/
def antidiff (a : ℤ → R) (n : ℤ) : R :=
  (∑ j ∈ Finset.range n.toNat, a (j : ℤ)) - ∑ j ∈ Finset.range (-n).toNat, a (-(j : ℤ) - 1)

@[simp] theorem antidiff_zero (a : ℤ → R) : antidiff a 0 = 0 := by simp [antidiff]

/-- The defining recurrence: `antidiff a` has forward difference `a`. -/
theorem antidiff_add_one (a : ℤ → R) (n : ℤ) : antidiff a (n + 1) = antidiff a n + a n := by
  by_cases hn : 0 ≤ n
  · obtain ⟨N, rfl⟩ : ∃ N : ℕ, n = (N : ℤ) := ⟨n.toNat, by omega⟩
    have h1 : ((N : ℤ) + 1).toNat = N + 1 := by omega
    have h2 : ((N : ℤ)).toNat = N := by omega
    have h3 : (-((N : ℤ) + 1)).toNat = 0 := by omega
    have h4 : (-(N : ℤ)).toNat = 0 := by omega
    simp only [antidiff, h1, h2, h3, h4, Finset.range_zero, Finset.sum_empty, sub_zero,
      Finset.sum_range_succ]
  · obtain ⟨M, rfl⟩ : ∃ M : ℕ, n = -(M : ℤ) - 1 := ⟨(-n - 1).toNat, by omega⟩
    have h1 : (-(M : ℤ) - 1 + 1).toNat = 0 := by omega
    have h2 : (-(M : ℤ) - 1).toNat = 0 := by omega
    have h3 : (-(-(M : ℤ) - 1 + 1)).toNat = M := by omega
    have h4 : (-(-(M : ℤ) - 1)).toNat = M + 1 := by omega
    simp only [antidiff, h1, h2, h3, h4, Finset.range_zero, Finset.sum_empty, zero_sub,
      Finset.sum_range_succ]
    ring

/-! ### Lemma 7 for `f = X^q - 1`, over `Config R`

`kcoord`/`basept` are pure lattice-position bookkeeping and are reused unchanged from
`Nivat.KS` (`KSDecomposition.lean:134,137`) — no need to reprove them here. -/

variable (p q : ℤ × ℤ)

open Nivat.KS (kcoord basept kcoord_add_q kcoord_add_p basept_add_q basept_add_p
  basept_add_kcoord_smul)

/-- The solution of the (degenerate) recurrence `(3)` of the source, over `Config R`: on each
`⟨q⟩`-orbit, telescope the values of `c` starting from the base point of the orbit. -/
def solve (p q : ℤ × ℤ) (c : Config R) : Config R :=
  fun z => antidiff (fun j => c (basept p q z + j • q)) (kcoord p q z)

/-- **Lemma 7 (source), second half**: the solution keeps the period `p`. -/
theorem solve_mem_Per {c : Config R} (hp : p ∈ Per c) : p ∈ Per (solve p q c) := by
  rw [mem_Per_iff]
  funext z
  rw [T_apply]
  simp only [solve, basept_add_p, kcoord_add_p]
  congr 1
  funext j
  rw [show basept p q z + p + j • q = basept p q z + j • q + p by abel]
  exact Per.apply hp _

/-- **Lemma 7 (source), first half**: the solution really is a preimage under `X^q - 1`. -/
theorem act_solve (hd : det p q ≠ 0) (c : Config R) :
    act (mono q - 1 : LaurentTwo R) (solve p q c) = c := by
  rw [act_sub_left, act_mono, act_one]
  funext z
  rw [Pi.sub_apply, T_apply]
  simp only [solve, basept_add_q hd, kcoord_add_q hd, antidiff_add_one]
  rw [basept_add_kcoord_smul]
  ring

variable {p q}

/-- **Lemma 7** of Kari–Szabados, specialised to `f = X^q - 1`, over `Config R`. -/
theorem exists_solve (hd : det p q ≠ 0) {c : Config R} (hp : p ∈ Per c) :
    ∃ c' : Config R, p ∈ Per c' ∧ act (mono q - 1 : LaurentTwo R) c' = c :=
  ⟨solve p q c, solve_mem_Per p q hp, act_solve p q hd c⟩

/-- Lemma 7 iterated: a `p`-periodic configuration in `Config R` is `∏_{i ∈ s} (X^{H i} - 1)`
applied to some `p`-periodic configuration, as soon as every `H i` is non-parallel to `p`. -/
theorem exists_preimage_prod {ι : Type*} [DecidableEq ι] {p : ℤ × ℤ} {H : ι → ℤ × ℤ}
    (hd : ∀ i, det p (H i) ≠ 0) {c : Config R} (hp : p ∈ Per c) (s : Finset ι) :
    ∃ c' : Config R, p ∈ Per c' ∧
      act (∏ i ∈ s, (mono (H i) - 1) : LaurentTwo R) c' = c := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨c, hp, by simp⟩
  | insert a s ha ih =>
      obtain ⟨c₁, hc₁p, hc₁⟩ := ih
      obtain ⟨c', hc'p, hc'⟩ := exists_solve (hd a) hc₁p
      refine ⟨c', hc'p, ?_⟩
      rw [Finset.prod_insert ha, mul_comm, act_mul, hc', hc₁]

/-! ### Lemma 8, over `Config R` -/

/-- **Lemma 8** of Kari–Szabados, specialised to `fᵢ = X^{hᵢ} - 1`, over `Config R`, by
induction on the number of factors. -/
theorem decomp_aux : ∀ (n : ℕ) (h : Fin n → ℤ × ℤ),
    (Pairwise fun i j => det (h i) (h j) ≠ 0) → ∀ η : Config R,
    act (∏ i, (mono (h i) - 1) : LaurentTwo R) η = 0 →
    ∃ f : Fin n → Config R, (∀ i, h i ∈ Per (f i)) ∧ ∀ z, η z = ∑ i, f i z := by
  intro n
  induction n with
  | zero =>
      intro h _ η hann
      have h1 : (∏ i, (mono (h i) - 1) : LaurentTwo R) = 1 := by simp
      rw [h1, act_one] at hann
      refine ⟨fun i => i.elim0, fun i => i.elim0, fun z => ?_⟩
      rw [hann]
      simp
  | succ n ih =>
      intro h hnp η hann
      -- split off the first factor
      have hsplit : (∏ i, (mono (h i) - 1) : LaurentTwo R)
          = (mono (h 0) - 1) * ∏ i : Fin n, (mono (h i.succ) - 1) := Fin.prod_univ_succ _
      have hd : ∀ i : Fin n, det (h 0) (h i.succ) ≠ 0 := fun i =>
        hnp (Ne.symm (Fin.succ_ne_zero i))
      -- `c`, the image of `η` under the remaining factors, has period `h 0`
      have hcp : h 0 ∈ Per (act (∏ i : Fin n, (mono (h i.succ) - 1) : LaurentTwo R) η) := by
        rw [← act_mono_sub_one_eq_zero_iff, ← act_mul, ← hsplit]
        exact hann
      obtain ⟨η₀, hη₀p, hη₀⟩ := exists_preimage_prod hd hcp Finset.univ
      have hzero : act (∏ i : Fin n, (mono (h i.succ) - 1) : LaurentTwo R) (η - η₀) = 0 := by
        rw [act_sub_right, hη₀, sub_self]
      have hnp' : Pairwise fun i j : Fin n => det (h i.succ) (h j.succ) ≠ 0 := by
        intro i j hij
        exact hnp fun hcon => hij (Fin.succ_injective n hcon)
      obtain ⟨f', hf'p, hf'sum⟩ := ih (fun i => h i.succ) hnp' (η - η₀) hzero
      refine ⟨Fin.cons η₀ f', ?_, ?_⟩
      · intro i
        induction i using Fin.cases with
        | zero => simpa using hη₀p
        | succ i => simpa using hf'p i
      · intro z
        rw [Fin.sum_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ]
        have h2 := hf'sum z
        simp only [Pi.sub_apply] at h2
        rw [← h2]
        ring

end Nivat.KSRing

namespace Nivat

/-- **Kari–Szabados, Lemma 8** (specialised form), over `Config R` for any `CommRing R`.
Every `η : ℤ² → R` annihilated by `Δ = ∏ᵢ (X^{hᵢ} - 1)`, with the `hᵢ` pairwise non-parallel,
decomposes as `η = ∑ᵢ ηᵢ` with `ηᵢ` of period `hᵢ`.  Same statement as
`Nivat.kari_szabados_decomp'` (`KSDecomposition.lean:271`), with `ℤ` replaced by `R`. -/
theorem kari_szabados_decomp_ring {R : Type*} [CommRing R] {n : ℕ} {h : Fin n → ℤ × ℤ}
    (_hne : ∀ i, h i ≠ 0) (hnp : Pairwise fun i j => det (h i) (h j) ≠ 0) {η : Config R}
    (hann : act (∏ i, (mono (h i) - 1) : LaurentTwo R) η = 0) :
    ∃ f : Fin n → Config R, (∀ i, h i ∈ Per (f i)) ∧ ∀ z, η z = ∑ i, f i z :=
  KSRing.decomp_aux n h hnp η hann

/-- The `R := ZMod p` instance of `kari_szabados_decomp_ring`, for any `p : ℕ` — including
`p` non-prime, since nothing above used an integral domain. -/
theorem kari_szabados_decomp_zmod {p : ℕ} {n : ℕ} {h : Fin n → ℤ × ℤ}
    (hne : ∀ i, h i ≠ 0) (hnp : Pairwise fun i j => det (h i) (h j) ≠ 0) {η : Config (ZMod p)}
    (hann : act (∏ i, (mono (h i) - 1) : LaurentTwo (ZMod p)) η = 0) :
    ∃ f : Fin n → Config (ZMod p), (∀ i, h i ∈ Per (f i)) ∧ ∀ z, η z = ∑ i, f i z :=
  kari_szabados_decomp_ring hne hnp hann

end Nivat
