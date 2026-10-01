/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.Laurent.Basic
import Nivat.Lattice.Zonotope
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Gluing the per-factor spanning results (Lemma 5.2, Step 3)

This file supplies **Step 3** of the proof of `Nivat.StarConfig.span_quotient` (Lemma 5.2):
given the pairwise coprimality facts of Step 1 and the per-factor spanning results of Step 2
(`Nivat.Sublattice.span_quotient_pair`), it glues them via two nested applications of the
Chinese Remainder Theorem into the global spanning statement.

Everything here is stated abstractly, over an arbitrary indexing type `Fin m`, directions
`v : Fin m → ℤ × ℤ`, degrees `d : Fin m → ℕ` and elements `A C : Fin m → LaurentTwo K` playing
the role of `S.aFac`/`S.cFac`.  The caller (`Nivat.StarConfig.span_quotient` in
`Nivat.BiRecursion`) is responsible for instantiating this against the concrete `StarConfig`
data and its Step 1 coprimality facts.

## Status

Under construction.
-/

namespace Nivat
namespace QuotientGlue

open scoped Classical

variable {K : Type*} [Field K]

/-! ### Ideal-arithmetic helpers -/

section IdealArith

variable {R : Type*} [CommRing R]

/-- If `x` is a unit modulo `a` (witnessed by `IsCoprime a x`, i.e. `Ideal.span {a,x} = ⊤`),
multiplying a second generator `y` by `x` does not change the ideal generated together with
`a`.  (Used to absorb the "already invertible" factor `C i` out of `c = ∏ l, C l` when passing
from `(A i, c)` to `(A i, ∏_{l ≠ i} C l)`.) -/
theorem span_pair_mul_of_isCoprime_left {a x y : R} (h : IsCoprime a x) :
    Ideal.span ({a, x * y} : Set R) = Ideal.span ({a, y} : Set R) := by
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro z (rfl | rfl)
    · exact Ideal.subset_span (by simp)
    · exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
  · rw [Ideal.span_le]
    rintro z hz
    rcases hz with hz | hz
    · rw [hz]; exact Ideal.subset_span (by simp)
    · simp only [Set.mem_singleton_iff] at hz
      rw [hz]
      obtain ⟨u, w, huv⟩ := h
      -- `u * a + w * x = 1`, so `y = (u * y) * a + w * (x * y)`.
      have hy : y = (u * y) * a + w * (x * y) := by
        have h2 : u * a * y + w * x * y = y := by
          have := congrArg (· * y) huv
          simp only [add_mul, one_mul] at this
          exact this
        exact h2.symm.trans (by ring)
      exact Ideal.mem_span_pair.mpr ⟨u * y, w, hy.symm⟩

/-- Expanding a product of ideals each shifted by a common ideal `J`: every cross term that
picks up a copy of `J` from some factor is absorbed into `J`, so the product lands inside
`(∏ I i) ⊔ J`.  This is the "unconditional" half of the two-ideal CRT identity (no coprimality
needed here; coprimality is only used to identify `∏` with `⨅`). -/
theorem prod_sup_le {ι : Type*} [DecidableEq ι] (I : ι → Ideal R) (J : Ideal R) (s : Finset ι) :
    ∏ i ∈ s, (I i ⊔ J) ≤ (∏ i ∈ s, I i) ⊔ J := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a₀ s' ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    calc (I a₀ ⊔ J) * ∏ i ∈ s', (I i ⊔ J)
        ≤ (I a₀ ⊔ J) * ((∏ i ∈ s', I i) ⊔ J) := Ideal.mul_mono_right ih
      _ = I a₀ * (∏ i ∈ s', I i) ⊔ I a₀ * J ⊔ (J * (∏ i ∈ s', I i) ⊔ J * J) := by
          rw [Ideal.sup_mul, Ideal.mul_sup, Ideal.mul_sup]
      _ ≤ I a₀ * (∏ i ∈ s', I i) ⊔ J := by
          refine sup_le (sup_le le_sup_left ?_) (sup_le ?_ ?_)
          · exact (Ideal.mul_le_right : I a₀ * J ≤ J).trans le_sup_right
          · exact (Ideal.mul_le_left : J * (∏ i ∈ s', I i) ≤ J).trans le_sup_right
          · exact (Ideal.mul_le_right : J * J ≤ J).trans le_sup_right

/-- The key ideal identity behind Stage 1 of the CRT gluing: if the ideals `(A i, c)` are
pairwise coprime, then their infimum is exactly `(∏ A i, c)`. Only the "easy" containments from
`prod_sup_le` and `∏ A i ∈ span {A i}` are needed on top of the coprimality hypothesis, which is
only used through `Ideal.prod_eq_iInf_of_pairwise_isCoprime` to turn the infimum into a
product. -/
theorem iInf_span_pair_eq_of_pairwise_isCoprime {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → R) (c : R)
    (hcop : Pairwise (fun i k => IsCoprime (Ideal.span ({A i, c} : Set R))
      (Ideal.span ({A k, c} : Set R)))) :
    ⨅ i, Ideal.span ({A i, c} : Set R) = Ideal.span ({∏ i, A i, c} : Set R) := by
  classical
  set f : ι → Ideal R := fun i => Ideal.span ({A i, c} : Set R) with hf
  have hspan : ∀ i, f i = Ideal.span ({A i} : Set R) ⊔ Ideal.span ({c} : Set R) := by
    intro i; simp [hf, Ideal.span_insert]
  have hiInf : (⨅ i, f i) = ⨅ i ∈ (Finset.univ : Finset ι), f i := by
    simp
  have hprod_eq_inf : ∏ i ∈ (Finset.univ : Finset ι), f i = ⨅ i ∈ (Finset.univ : Finset ι), f i :=
    Ideal.prod_eq_iInf_of_pairwise_isCoprime (hcop.set_pairwise _)
  apply le_antisymm
  · -- `⨅ i, f i ≤ span {∏ A i, c}`
    rw [hiInf, ← hprod_eq_inf]
    calc ∏ i ∈ (Finset.univ : Finset ι), f i
        = ∏ i ∈ (Finset.univ : Finset ι),
            (Ideal.span ({A i} : Set R) ⊔ Ideal.span ({c} : Set R)) := by
          exact Finset.prod_congr rfl fun i _ => hspan i
      _ ≤ (∏ i ∈ (Finset.univ : Finset ι), Ideal.span ({A i} : Set R)) ⊔
            Ideal.span ({c} : Set R) := prod_sup_le _ _ _
      _ = Ideal.span ({∏ i, A i} : Set R) ⊔ Ideal.span ({c} : Set R) := by
          rw [Ideal.prod_span_singleton]
      _ = Ideal.span ({∏ i, A i, c} : Set R) := by
          rw [← Ideal.span_insert]
  · -- `span {∏ A i, c} ≤ ⨅ i, f i`
    refine le_iInf fun i => ?_
    rw [hf]
    rw [Ideal.span_le]
    rintro z hz
    rcases hz with hz | hz
    · subst hz
      have hdvd : A i ∣ ∏ i, A i := Finset.dvd_prod_of_mem A (Finset.mem_univ i)
      have : (∏ i, A i) ∈ Ideal.span ({A i} : Set R) := Ideal.mem_span_singleton.mpr hdvd
      exact Ideal.span_mono (Set.singleton_subset_iff.mpr (Set.mem_insert _ _)) this
    · simp only [Set.mem_singleton_iff] at hz
      subst hz
      exact Ideal.subset_span (Or.inr rfl)

/-- `span {x, y, z} = span {x, y} ⊔ span {z}`: splitting off the last generator of a triple
span as a separate summand. -/
theorem span_triple_eq_pair_sup_singleton (x y z : R) :
    Ideal.span ({x, y, z} : Set R) = Ideal.span ({x, y} : Set R) ⊔ Ideal.span ({z} : Set R) := by
  simp only [Ideal.span_insert, sup_assoc]

/-- If `span {x, y, C j} = ⊤` for every `j` in a finite index set, then `span {x, y, ∏ j, C j} = ⊤`
too. This is the "coprime with a product" step needed to promote a per-factor coprimality fact
(Step 1's hypothesis, instantiated at each `j`) to coprimality with the shared element `c = ∏ C j`
used to build the Stage 1/Stage 2 CRT families. -/
theorem span_triple_prod_eq_top_of_forall {ι : Type*} (x y : R) (C : ι → R) (s : Finset ι)
    (h : ∀ j ∈ s, Ideal.span ({x, y, C j} : Set R) = ⊤) :
    Ideal.span ({x, y, ∏ j ∈ s, C j} : Set R) = ⊤ := by
  have hI0 : ∀ j ∈ s, IsCoprime (Ideal.span ({x, y} : Set R)) (Ideal.span ({C j} : Set R)) := by
    intro j hj
    have := h j hj
    rw [span_triple_eq_pair_sup_singleton] at this
    exact Ideal.isCoprime_iff_sup_eq.mpr this
  have hprod : IsCoprime (Ideal.span ({x, y} : Set R))
      (∏ j ∈ s, Ideal.span ({C j} : Set R)) := IsCoprime.prod_right hI0
  rw [Ideal.prod_span_singleton] at hprod
  rw [span_triple_eq_pair_sup_singleton]
  exact Ideal.isCoprime_iff_sup_eq.mp hprod

/-- If `x` is coprime to an ideal `I` (i.e. `span {x} ⊔ I = ⊤`), it has an inverse modulo `I`:
some `v` with `x * v ≡ 1 (mod I)`. -/
theorem exists_inv_mod_of_isCoprime {x : R} {I : Ideal R}
    (h : IsCoprime (Ideal.span ({x} : Set R)) I) : ∃ v : R, x * v - 1 ∈ I := by
  rw [Ideal.isCoprime_iff_sup_eq] at h
  have h1 : (1 : R) ∈ Ideal.span ({x} : Set R) ⊔ I := h ▸ Submodule.mem_top
  obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.mp h1
  obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.mp hp
  refine ⟨v, ?_⟩
  have : x * v - 1 = -q := by
    linear_combination hv + hpq
  rw [this]
  exact I.neg_mem hq

/-- Finite products of elements individually coprime to an ideal `I` have a joint inverse
modulo `I`. Used to normalise `E i j = (∏_{k≠i} A k) * (∏_{l≠j} C l)` into a genuine idempotent
(`≡ 1`, not merely a unit) modulo `Ideal.span {A i, C j}`. -/
theorem exists_inv_mod_of_forall_isCoprime {ι : Type*} {I : Ideal R} (f : ι → R) (s : Finset ι)
    (h : ∀ k ∈ s, IsCoprime (Ideal.span ({f k} : Set R)) I) :
    ∃ v : R, (∏ k ∈ s, f k) * v - 1 ∈ I := by
  classical
  induction s using Finset.induction with
  | empty => exact ⟨1, by simp⟩
  | insert a s' ha ih =>
    obtain ⟨v0, hv0⟩ := exists_inv_mod_of_isCoprime (h a (Finset.mem_insert_self a s'))
    obtain ⟨v1, hv1⟩ := ih fun k hk => h k (Finset.mem_insert_of_mem hk)
    refine ⟨v0 * v1, ?_⟩
    rw [Finset.prod_insert ha]
    -- `(f a * ∏ f) * (v0 * v1) - 1 = (f a * v0 - 1) * (∏f * v1) + ((∏f)*v1 - 1)`, both summands ∈ I.
    have key : f a * (∏ k ∈ s', f k) * (v0 * v1) - 1 =
        (f a * v0 - 1) * ((∏ k ∈ s', f k) * v1) + ((∏ k ∈ s', f k) * v1 - 1) := by ring
    rw [key]
    exact I.add_mem (I.mul_mem_right _ hv0) hv1

end IdealArith

/-! ### The two-index CRT family

This section builds, from the "triple" coprimality hypotheses supplied by Step 1
(`haaC`, `hacc` below), the normalised idempotent-like elements `Ê i j` used to glue the
per-factor spanning results of Step 2 together. -/

section CRTFamily

variable {R : Type*} [CommRing R]

/-- `span {x, y, z} = span {x} ⊔ span {y} ⊔ span {z}`, splitting a triple span into three
singleton summands (associated to the left), so that reordering the three summands only needs
`⊔`-commutativity/associativity, not `Set`-literal manipulation. -/
theorem span_triple_eq_sup (x y z : R) :
    Ideal.span ({x, y, z} : Set R) = Ideal.span ({x} : Set R) ⊔ Ideal.span ({y} : Set R) ⊔
      Ideal.span ({z} : Set R) := by
  rw [Ideal.span_insert, Ideal.span_insert, sup_assoc]

/-- From `span {x, y, z} = ⊤`, the middle generator `y` is coprime to the ideal spanned by the
other two. -/
theorem coprime_middle_of_span_triple_top {x y z : R}
    (h : Ideal.span ({x, y, z} : Set R) = ⊤) :
    IsCoprime (Ideal.span ({y} : Set R)) (Ideal.span ({x, z} : Set R)) := by
  rw [Ideal.isCoprime_iff_sup_eq, Ideal.span_insert]
  rw [span_triple_eq_sup] at h
  rw [show Ideal.span ({y} : Set R) ⊔ (Ideal.span ({x} : Set R) ⊔ Ideal.span ({z} : Set R)) =
      Ideal.span ({x} : Set R) ⊔ Ideal.span ({y} : Set R) ⊔ Ideal.span ({z} : Set R) by
    ac_rfl]
  exact h

/-- From `span {x, y, z} = ⊤`, the last generator `z` is coprime to the ideal spanned by the
other two. -/
theorem coprime_last_of_span_triple_top {x y z : R}
    (h : Ideal.span ({x, y, z} : Set R) = ⊤) :
    IsCoprime (Ideal.span ({z} : Set R)) (Ideal.span ({x, y} : Set R)) := by
  rw [Ideal.isCoprime_iff_sup_eq, Ideal.span_insert]
  rw [span_triple_eq_sup] at h
  rw [show Ideal.span ({z} : Set R) ⊔ (Ideal.span ({x} : Set R) ⊔ Ideal.span ({y} : Set R)) =
      Ideal.span ({x} : Set R) ⊔ Ideal.span ({y} : Set R) ⊔ Ideal.span ({z} : Set R) by
    ac_rfl]
  exact h

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The "off-diagonal" cross term at position `(i, j)`: the product of every `A k` with `k ≠ i`
and every `C l` with `l ≠ j`. This is the raw (not yet normalised) idempotent-like element used
in the two-index CRT gluing. -/
def E (A C : ι → R) (i j : ι) : R :=
  (∏ k ∈ Finset.univ.erase i, A k) * (∏ l ∈ Finset.univ.erase j, C l)

/-- **Off-diagonal vanishing**: if `(k, l) ≠ (i, j)`, then `E A C i j` lies in
`Ideal.span {A k, C l}` (it literally picks up a factor of `A k`, when `k ≠ i`, or of `C l`, when
`l ≠ j`). No coprimality is needed for this direction. -/
theorem E_mem_span_pair_of_ne {A C : ι → R} {i j k l : ι} (hne : (k, l) ≠ (i, j)) :
    E A C i j ∈ Ideal.span ({A k, C l} : Set R) := by
  rw [E]
  rcases eq_or_ne k i with hki | hki
  · -- then l ≠ j, so `C l` divides the second factor.
    have hlj : l ≠ j := by rintro rfl; exact hne (by rw [hki])
    have hdvd : C l ∣ ∏ l' ∈ Finset.univ.erase j, C l' :=
      Finset.dvd_prod_of_mem C (Finset.mem_erase.mpr ⟨hlj, Finset.mem_univ l⟩)
    have hmem : (∏ l' ∈ Finset.univ.erase j, C l') ∈ Ideal.span ({A k, C l} : Set R) :=
      Ideal.span_mono (Set.singleton_subset_iff.mpr (by simp))
        (Ideal.mem_span_singleton.mpr hdvd)
    exact Ideal.mul_mem_left _ _ hmem
  · -- k ≠ i, so `A k` divides the first factor.
    have hdvd : A k ∣ ∏ k' ∈ Finset.univ.erase i, A k' :=
      Finset.dvd_prod_of_mem A (Finset.mem_erase.mpr ⟨hki, Finset.mem_univ k⟩)
    have hmem : (∏ k' ∈ Finset.univ.erase i, A k') ∈ Ideal.span ({A k, C l} : Set R) :=
      Ideal.span_mono (Set.singleton_subset_iff.mpr (by simp))
        (Ideal.mem_span_singleton.mpr hdvd)
    exact Ideal.mul_mem_right _ _ hmem

/-- **Unit on the diagonal**: `E A C i j` is coprime to `Ideal.span {A i, C j}`, i.e. it is a
unit modulo that ideal. This is where Step 1's triple coprimality hypotheses (`haaC`, `hacc`)
are used: every factor of `E A C i j` is, individually, coprime to `Ideal.span {A i, C j}`. -/
theorem isCoprime_E_span_pair {A C : ι → R} {i j : ι}
    (haaC : ∀ k, k ≠ i → Ideal.span ({A i, A k, C j} : Set R) = ⊤)
    (hacc : ∀ l, l ≠ j → Ideal.span ({A i, C j, C l} : Set R) = ⊤) :
    IsCoprime (Ideal.span ({E A C i j} : Set R)) (Ideal.span ({A i, C j} : Set R)) := by
  rw [E]
  have hA : ∀ k ∈ Finset.univ.erase i,
      IsCoprime (Ideal.span ({A k} : Set R)) (Ideal.span ({A i, C j} : Set R)) := by
    intro k hk
    exact coprime_middle_of_span_triple_top (haaC k (Finset.mem_erase.mp hk).1)
  have hC : ∀ l ∈ Finset.univ.erase j,
      IsCoprime (Ideal.span ({C l} : Set R)) (Ideal.span ({A i, C j} : Set R)) := by
    intro l hl
    exact coprime_last_of_span_triple_top (hacc l (Finset.mem_erase.mp hl).1)
  have hAprod : IsCoprime (Ideal.span ({∏ k ∈ Finset.univ.erase i, A k} : Set R))
      (Ideal.span ({A i, C j} : Set R)) := by
    rw [← Ideal.prod_span_singleton]
    exact IsCoprime.prod_left hA
  have hCprod : IsCoprime (Ideal.span ({∏ l ∈ Finset.univ.erase j, C l} : Set R))
      (Ideal.span ({A i, C j} : Set R)) := by
    rw [← Ideal.prod_span_singleton]
    exact IsCoprime.prod_left hC
  have := IsCoprime.mul_left hAprod hCprod
  rwa [Ideal.span_singleton_mul_span_singleton] at this

/-- `span {x, y} ⊔ span {x, z}` collapses to `span {x, y, z}` (the shared generator `x` is not
duplicated). Used to reduce the "coprime for fixed `i`, varying `j`" pairwise hypothesis to a
single triple-span hypothesis. -/
theorem coprime_pair_of_span_triple_top {x y z : R} (h : Ideal.span ({x, y, z} : Set R) = ⊤) :
    IsCoprime (Ideal.span ({x, y} : Set R)) (Ideal.span ({x, z} : Set R)) := by
  rw [Ideal.isCoprime_iff_sup_eq, Ideal.span_insert, Ideal.span_insert]
  rw [span_triple_eq_sup] at h
  rw [← h]
  simp [sup_assoc, sup_left_comm]

/-- `span {x, z} ⊔ span {y, z}` collapses to `span {x, y, z}` (the shared generator `z` is not
duplicated). Used for pairwise coprimality of the `A`-family relative to a common `c`. -/
theorem coprime_pair_right_of_span_triple_top {x y z : R} (h : Ideal.span ({x, y, z} : Set R) = ⊤) :
    IsCoprime (Ideal.span ({x, z} : Set R)) (Ideal.span ({y, z} : Set R)) := by
  rw [Ideal.isCoprime_iff_sup_eq, Ideal.span_insert, Ideal.span_insert]
  rw [span_triple_eq_sup] at h
  rw [← h]
  simp [sup_assoc, sup_left_comm]

/-- `span {x, y} = span {y, x}`: the two-element span does not depend on the order of its
generators. -/
theorem span_pair_comm (x y : R) : Ideal.span ({x, y} : Set R) = Ideal.span ({y, x} : Set R) := by
  rw [show ({x, y} : Set R) = {y, x} from Set.pair_comm x y]

/-- Variant of `iInf_span_pair_eq_of_pairwise_isCoprime` with the shared generator `c` written
first in each pair, matching the order needed when `c` plays the role of a fixed `A i`. -/
theorem iInf_span_pair_eq_of_pairwise_isCoprime_left (c : R) (A : ι → R)
    (hcop : Pairwise (fun i k => IsCoprime (Ideal.span ({c, A i} : Set R))
      (Ideal.span ({c, A k} : Set R)))) :
    ⨅ i, Ideal.span ({c, A i} : Set R) = Ideal.span ({c, ∏ i, A i} : Set R) := by
  have hcop' : Pairwise (fun i k => IsCoprime (Ideal.span ({A i, c} : Set R))
      (Ideal.span ({A k, c} : Set R))) := by
    intro i k hik
    have := hcop hik
    dsimp only at this
    rwa [span_pair_comm c (A i), span_pair_comm c (A k)] at this
  have h := iInf_span_pair_eq_of_pairwise_isCoprime A c hcop'
  rw [show (⨅ i, Ideal.span ({c, A i} : Set R)) = ⨅ i, Ideal.span ({A i, c} : Set R) from
      iInf_congr fun i => span_pair_comm c (A i)]
  rw [h, span_pair_comm (∏ i, A i) c]

/-- **The nested CRT identity**: over the full `ι × ι` grid, the infimum of all the "cross"
ideals `span {A i, C j}` equals `span {a, c}` where `a = ∏ A i` and `c = ∏ C j`. This is proved
by nesting two one-dimensional CRT identities (`iInf_span_pair_eq_of_pairwise_isCoprime`,
applied first to the `C`-family for fixed `i`, then to the `A`-family), so it needs no extra
coprimality data beyond `haaC`/`hacc`. -/
theorem iInf_grid_eq_span_pair {A C : ι → R}
    (haaC : ∀ i k, i ≠ k → ∀ j, Ideal.span ({A i, A k, C j} : Set R) = ⊤)
    (hacc : ∀ i j l, j ≠ l → Ideal.span ({A i, C j, C l} : Set R) = ⊤) :
    ⨅ i, ⨅ j, Ideal.span ({A i, C j} : Set R) =
      Ideal.span ({∏ i, A i, ∏ j, C j} : Set R) := by
  have hstep2 : ∀ i, ⨅ j, Ideal.span ({A i, C j} : Set R) = Ideal.span ({A i, ∏ j, C j} : Set R) :=
    fun i => iInf_span_pair_eq_of_pairwise_isCoprime_left (A i) C
      (fun j l hjl => coprime_pair_of_span_triple_top (hacc i j l hjl))
  simp_rw [hstep2]
  have hstep1 : Pairwise (fun i k => IsCoprime (Ideal.span ({A i, ∏ j, C j} : Set R))
      (Ideal.span ({A k, ∏ j, C j} : Set R))) := fun i k hik =>
    coprime_pair_right_of_span_triple_top
      (span_triple_prod_eq_top_of_forall (A i) (A k) C Finset.univ (fun j _ => haaC i k hik j))
  exact iInf_span_pair_eq_of_pairwise_isCoprime A (∏ j, C j) hstep1

omit [Fintype ι] [DecidableEq ι] in
/-- **Adapter matching `Nivat.BiRecursion`'s existing API.** `Nivat.StarConfig` already proves
coprimality against the *full* products `aElt`/`cElt` (`aFac_aFac_cElt_span_top`), not against
individual factors. Since `c = ∏ j, C j` lies in `span {C j}` for every `j`
(`cElt_mem_span_cFac`), a triple `span {A i, A k, c} = ⊤` forces `span {A i, A k, C j} = ⊤` too
— it is a bigger ideal containing an already-top one. This turns the `aElt`/`cElt`-level facts
into the per-factor `haaC` hypothesis expected by `iInf_grid_eq_span_pair`. -/
theorem haaC_of_coprime_with_prod {A C : ι → R} (c : R)
    (haaC' : ∀ i k, i ≠ k → Ideal.span ({A i, A k, c} : Set R) = ⊤)
    (hcmem : ∀ j, c ∈ Ideal.span ({C j} : Set R)) :
    ∀ i k, i ≠ k → ∀ j, Ideal.span ({A i, A k, C j} : Set R) = ⊤ := by
  intro i k hik j
  have htop := haaC' i k hik
  have hsub : Ideal.span ({A i, A k, c} : Set R) ≤ Ideal.span ({A i, A k, C j} : Set R) := by
    rw [Ideal.span_le]
    rintro x (rfl | rfl | rfl)
    · exact Ideal.subset_span (by simp)
    · exact Ideal.subset_span (by simp)
    · exact Ideal.span_mono (Set.singleton_subset_iff.mpr (by simp)) (hcmem j)
  exact top_le_iff.mp (htop ▸ hsub)

omit [Fintype ι] [DecidableEq ι] in
/-- Dual of `haaC_of_coprime_with_prod`: turns `aElt_cFac_cFac_span_top`-style facts (coprimality
against the full `aElt`) into the per-factor `hacc` hypothesis. -/
theorem hacc_of_coprime_with_prod {A C : ι → R} (a : R)
    (hacc' : ∀ j l, j ≠ l → Ideal.span ({a, C j, C l} : Set R) = ⊤)
    (hamem : ∀ i, a ∈ Ideal.span ({A i} : Set R)) :
    ∀ i j l, j ≠ l → Ideal.span ({A i, C j, C l} : Set R) = ⊤ := by
  intro i j l hjl
  have htop := hacc' j l hjl
  have hsub : Ideal.span ({a, C j, C l} : Set R) ≤ Ideal.span ({A i, C j, C l} : Set R) := by
    rw [Ideal.span_le]
    rintro x (rfl | rfl | rfl)
    · exact Ideal.span_mono (Set.singleton_subset_iff.mpr (by simp)) (hamem i)
    · exact Ideal.subset_span (by simp)
    · exact Ideal.subset_span (by simp)
  exact top_le_iff.mp (htop ▸ hsub)

/-- If `f k l ≡ 1` and every other `f i j ≡ 0` modulo an ideal `I`, then the full double sum of
`f` is `≡ 1` modulo `I`. Pure "partition of unity" bookkeeping, no ring-theoretic content beyond
`Submodule.sum_mem`. -/
theorem sum_sum_sub_one_mem_of_diag {I : Ideal R} (f : ι → ι → R) {k l : ι}
    (hd : f k l - 1 ∈ I) (ho : ∀ i j, (i, j) ≠ (k, l) → f i j ∈ I) :
    (∑ i, ∑ j, f i j) - 1 ∈ I := by
  classical
  have hprod : (∑ i, ∑ j, f i j) = ∑ p ∈ (Finset.univ : Finset (ι × ι)), f p.1 p.2 := by
    rw [← Finset.univ_product_univ, Finset.sum_product']
  rw [hprod]
  rw [← Finset.add_sum_erase _ (fun p : ι × ι => f p.1 p.2) (Finset.mem_univ (k, l))]
  have hrest : (∑ p ∈ (Finset.univ : Finset (ι × ι)).erase (k, l), f p.1 p.2) ∈ I :=
    Submodule.sum_mem _ fun p hp => by
      obtain ⟨p1, p2⟩ := p
      exact ho p1 p2 (Finset.ne_of_mem_erase hp)
  have : f k l + (∑ p ∈ (Finset.univ : Finset (ι × ι)).erase (k, l), f p.1 p.2) - 1 =
      (f k l - 1) + ∑ p ∈ (Finset.univ : Finset (ι × ι)).erase (k, l), f p.1 p.2 := by ring
  rw [this]
  exact I.add_mem hd hrest

/-- **Existence of a two-index partition of unity**: given the triple coprimality hypotheses of
Step 1, there is a family `e : ι → ι → R` with `e i j ≡ 1 (mod span {A i, C j})` on the
"diagonal" `(i, j)` and `e i j ∈ span {A k, C l}` for every other `(k, l)` — and consequently
`∑ i, ∑ j, e i j ≡ 1 (mod span {a, c})` where `a = ∏ A i`, `c = ∏ C j`. -/
theorem exists_partition_of_unity {A C : ι → R}
    (haaC : ∀ i k, i ≠ k → ∀ j, Ideal.span ({A i, A k, C j} : Set R) = ⊤)
    (hacc : ∀ i j l, j ≠ l → Ideal.span ({A i, C j, C l} : Set R) = ⊤) :
    ∃ e : ι → ι → R,
      (∀ i j, e i j - 1 ∈ Ideal.span ({A i, C j} : Set R)) ∧
      (∀ i j k l, (k, l) ≠ (i, j) → e i j ∈ Ideal.span ({A k, C l} : Set R)) ∧
      (∀ k l, (∑ i, ∑ j, e i j) - 1 ∈ Ideal.span ({A k, C l} : Set R)) := by
  classical
  have hV : ∀ i j, ∃ v : R, E A C i j * v - 1 ∈ Ideal.span ({A i, C j} : Set R) := fun i j =>
    exists_inv_mod_of_isCoprime (isCoprime_E_span_pair
      (fun k hk => haaC i k hk.symm j) (fun l hl => hacc i j l hl.symm))
  choose V hV using hV
  refine ⟨fun i j => E A C i j * V i j, fun i j => hV i j, ?_, ?_⟩
  · intro i j k l hne
    exact Ideal.mul_mem_right _ _ (E_mem_span_pair_of_ne hne)
  · intro k l
    refine sum_sum_sub_one_mem_of_diag (fun i j => E A C i j * V i j) (hV k l) ?_
    intro i j hij
    exact Ideal.mul_mem_right _ _ (E_mem_span_pair_of_ne (Ne.symm hij))

end CRTFamily

/-! ### Transporting per-factor spanning across a finite CRT-shaped ideal family

This is the piece needed to turn the ideal identity `⨅ i, I i = Ideal.span {a, c}` (established
above by `iInf_grid_eq_span_pair`) into an actual `Submodule.span`-level statement: no
coprimality of the `I i` is used here, only that each `I i` already has an explicit spanning set
`T i` whose *other*-indexed vanishing is known. -/

section SpanTransport

variable {R : Type*} [CommRing R] [Algebra K R]

/-- If a finite family of ideals `I i` each have a subset `T i` of `R` whose quotient images
span `R ⧸ I i` over `K`, and every element of `T i` vanishes mod every *other* `I k` (`k ≠ i`),
then the images of `⋃ i, T i` span `R ⧸ ⨅ i, I i` over `K`. No coprimality of the `I i` is
needed — this is a direct construction: given `r`, pull each `mk (I i) r` back to a
`K`-combination of `T i`, sum these combinations over `i`, and check the result agrees with `r`
modulo every `I i` (the "own" terms match by construction, the "foreign" terms vanish by
`hvanish`). -/
theorem span_transport {ι : Type*} [Fintype ι] (I : ι → Ideal R) (T : ι → Set R)
    (hspan : ∀ i, Submodule.span K ((Ideal.Quotient.mk (I i)) '' T i) = ⊤)
    (hvanish : ∀ i, ∀ t ∈ T i, ∀ k, k ≠ i → t ∈ I k) :
    Submodule.span K ((Ideal.Quotient.mk (⨅ i, I i)) '' (⋃ i, T i)) = ⊤ := by
  classical
  have hmk_smul : ∀ (J : Ideal R) (c : K) (x : R),
      Ideal.Quotient.mk J (c • x) = c • Ideal.Quotient.mk J x := by
    intro J c x
    rw [← Ideal.Quotient.mkₐ_eq_mk K J]
    exact map_smul (Ideal.Quotient.mkₐ K J) c x
  refine Submodule.eq_top_iff'.mpr fun x => ?_
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  -- for each `i`, write `mk (I i) r` as an explicit finite `K`-combination of elements of `T i`
  have hchoice : ∀ i, ∃ (n : ℕ) (f : Fin n → K) (t : Fin n → R),
      (∀ k, t k ∈ T i) ∧
        ∑ k, f k • Ideal.Quotient.mk (I i) (t k) = Ideal.Quotient.mk (I i) r := by
    intro i
    have hmem : Ideal.Quotient.mk (I i) r ∈
        Submodule.span K ((Ideal.Quotient.mk (I i)) '' T i) := by
      rw [hspan i]; exact Submodule.mem_top
    obtain ⟨n, f, g, hsum⟩ := Submodule.mem_span_set'.mp hmem
    choose t ht het using fun k => (g k).2
    exact ⟨n, f, t, ht, by rw [← hsum]; exact Finset.sum_congr rfl fun k _ => by rw [het k]⟩
  choose n f t ht heq using hchoice
  -- glue the per-`i` combinations into a single `y`, a `K`-combination of `⋃ i, T i`
  set y : R := ∑ i, ∑ k, f i k • t i k with hy_def
  have hy_mem : Ideal.Quotient.mk (⨅ i, I i) y ∈
      Submodule.span K ((Ideal.Quotient.mk (⨅ i, I i)) '' (⋃ i, T i)) := by
    rw [hy_def, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_sum]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [hmk_smul]
    exact Submodule.smul_mem _ _
      (Submodule.subset_span ⟨t i k, Set.mem_iUnion.mpr ⟨i, ht i k⟩, rfl⟩)
  -- `y ≡ r (mod I i)` for every `i`: the `i`-th summand matches by construction, every other
  -- summand's terms lie in `T l` (`l ≠ i`) and so vanish mod `I i` by `hvanish`.
  have hall : ∀ i, Ideal.Quotient.mk (I i) y = Ideal.Quotient.mk (I i) r := by
    intro i
    have hzero : ∀ l ∈ (Finset.univ : Finset ι), l ≠ i →
        Ideal.Quotient.mk (I i) (∑ k, f l k • t l k) = 0 := by
      intro l _ hli
      rw [map_sum]
      refine Finset.sum_eq_zero fun k _ => ?_
      have htmem : t l k ∈ I i := hvanish l (t l k) (ht l k) i (Ne.symm hli)
      rw [hmk_smul, Ideal.Quotient.eq_zero_iff_mem.mpr htmem, smul_zero]
    calc Ideal.Quotient.mk (I i) y
        = ∑ l, Ideal.Quotient.mk (I i) (∑ k, f l k • t l k) := by rw [hy_def, map_sum]
      _ = Ideal.Quotient.mk (I i) (∑ k, f i k • t i k) :=
          Finset.sum_eq_single i hzero (fun h => absurd (Finset.mem_univ i) h)
      _ = ∑ k, f i k • Ideal.Quotient.mk (I i) (t i k) := by
          rw [map_sum]; exact Finset.sum_congr rfl fun k _ => hmk_smul (I i) (f i k) (t i k)
      _ = Ideal.Quotient.mk (I i) r := heq i
  have hy_eq : Ideal.Quotient.mk (⨅ i, I i) y = Ideal.Quotient.mk (⨅ i, I i) r := by
    refine (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr ?_
    rw [Submodule.mem_iInf]
    intro i
    exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp (hall i)
  rw [← hy_eq]
  exact hy_mem

end SpanTransport

end QuotientGlue
end Nivat
