/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.Words
import Nivat.Lattice.Primitive
import Nivat.Section8.External
import Nivat.Section8.ExternalDischarged
import Nivat.Section8.ConeGeom

/-!
# §8.3. The first half-plane

Formalisation of §8.3 of *The Convex Nivat Conjecture* (Pan); this subsection
proves Theorem 8.1(i).  The only tools are Lemma 8.2, the difference operators `Q_i` of (0.2),
and the finite-state argument of step (6) of Lemma D.7.

Lemma 8.8 is the one-sided finite-state lemma: if a product of difference operators kills a
`kv`-periodic field on a half-plane `{t ≥ c}` whose boundary is transverse to all the shifts,
then the field is purely periodic in the `u` direction slightly inside that half-plane.
Proposition 8.9 differences `ζ` by `Q_i` on the region `R` of Theorem 8.7, saturates along
`h_i`, and feeds the result to Lemma 8.8.  Corollary 8.10 absorbs the doubly periodic
components and packages the output as `Nivat.FirstHalfPlane`.

## Main results

* `Nivat.exists_period_of_ann_halfPlane` — **Lemma 8.8**, half-plane case.
* `Nivat.doublyPeriodic_of_ann` — **Lemma 8.8**, whole-plane case.
* `Nivat.first_half_plane_dichotomy` — **Proposition 8.9(b)**.
* `Nivat.FirstHalfPlane` and `Nivat.exists_firstHalfPlane` — **Corollary 8.10 = Theorem 8.1(i)**.

## Status

Skeleton; proofs are line D.
-/

namespace Nivat

open Finset

/-! ### Lemma 8.8 -/

/-- `τ_- = ∑_{τ_j < 0} τ_j`, where `τ_j = t(H_j) = π_v (H_j)`.  Paper Lemma 8.8. -/
def tauMinus {r : ℕ} (v : ℤ × ℤ) (H : Fin r → ℤ × ℤ) : ℤ := ∑ j, min (pi v (H j)) 0

/-- `τ_+ = ∑_{τ_j > 0} τ_j`.  Paper Lemma 8.8. -/
def tauPlus {r : ℕ} (v : ℤ × ℤ) (H : Fin r → ℤ × ℤ) : ℤ := ∑ j, max (pi v (H j)) 0

theorem tauMinus_nonpos {r : ℕ} (v : ℤ × ℤ) (H : Fin r → ℤ × ℤ) : tauMinus v H ≤ 0 :=
  Finset.sum_nonpos fun _ _ => min_le_right _ _

theorem tauPlus_nonneg {r : ℕ} (v : ℤ × ℤ) (H : Fin r → ℤ × ℤ) : 0 ≤ tauPlus v H :=
  Finset.sum_nonneg fun _ _ => le_max_right _ _

/-- Combinatorial core of Lemma 8.8's finite-state argument: the set `C₊ = {j : 0 < τ j}` is the
*strict* maximiser of `C ↦ ∑_{j ∈ C} τ j` among all `C ⊆ univ`, when every `τ j ≠ 0`.  Dually
(apply to `-τ`), `C₋ = {j : τ j < 0}` is the strict minimiser. -/
private theorem sum_lt_sum_filter_pos {r : ℕ} (τ : Fin r → ℤ) (hτ : ∀ j, τ j ≠ 0)
    {C : Finset (Fin r)} (hC : C ≠ Finset.univ.filter (fun j => 0 < τ j)) :
    ∑ j ∈ C, τ j < ∑ j ∈ Finset.univ.filter (fun j => 0 < τ j), τ j := by
  classical
  set Cp := Finset.univ.filter (fun j => 0 < τ j) with hCpdef
  set δ : Fin r → ℤ := fun j => (if j ∈ Cp then τ j else 0) - (if j ∈ C then τ j else 0) with hδdef
  have hCpeq : ∑ j ∈ Cp, τ j = ∑ j : Fin r, if j ∈ Cp then τ j else 0 := by
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  have hCeq : ∑ j ∈ C, τ j = ∑ j : Fin r, if j ∈ C then τ j else 0 := by
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  have hdiff : ∑ j ∈ Cp, τ j - ∑ j ∈ C, τ j = ∑ j : Fin r, δ j := by
    rw [hCpeq, hCeq, hδdef, Finset.sum_sub_distrib]
  have hnonneg : ∀ j ∈ (Finset.univ : Finset (Fin r)), 0 ≤ δ j := by
    intro j _
    simp only [hδdef]
    by_cases hjCp : j ∈ Cp <;> by_cases hjC : j ∈ C <;> simp only [hjCp, hjC, if_true, if_false]
    · linarith
    · have : 0 < τ j := (Finset.mem_filter.mp hjCp).2
      linarith
    · have hjCp' : ¬ (0 < τ j) := fun h => hjCp (Finset.mem_filter.mpr ⟨Finset.mem_univ j, h⟩)
      have : τ j < 0 := lt_of_le_of_ne (not_lt.mp hjCp') (hτ j)
      linarith
    · linarith
  have hex : ∃ j ∈ (Finset.univ : Finset (Fin r)), 0 < δ j := by
    have hne : ∃ j, ¬ (j ∈ C ↔ j ∈ Cp) := by
      by_contra hcon
      push Not at hcon
      exact hC (Finset.ext hcon)
    obtain ⟨j, hj⟩ := hne
    refine ⟨j, Finset.mem_univ j, ?_⟩
    simp only [hδdef]
    by_cases hjCp : j ∈ Cp <;> by_cases hjC : j ∈ C <;>
      simp only [hjCp, hjC, if_true, if_false]
    · exact absurd (Iff.intro (fun _ => hjCp) (fun _ => hjC)) hj
    · have : 0 < τ j := (Finset.mem_filter.mp hjCp).2
      linarith
    · have hjCp' : ¬ (0 < τ j) := fun h => hjCp (Finset.mem_filter.mpr ⟨Finset.mem_univ j, h⟩)
      have : τ j < 0 := lt_of_le_of_ne (not_lt.mp hjCp') (hτ j)
      linarith
    · exact absurd (Iff.intro (fun h => absurd h hjC) (fun h => absurd h hjCp)) hj
  have hpos : 0 < ∑ j : Fin r, δ j := Finset.sum_pos' hnonneg hex
  linarith [hdiff ▸ hpos]

/-- **Lemma 8.8 (One-sided finite-state lemma).**  Let `G : ℤ² → 𝔽_p` have period `kv` with `v`
primitive and `k ≥ 1`, let `(v, u)` be a unimodular basis, so that the row coordinate of `z` is
`t(z) = π_v z`.  Let `H₁, …, H_r` with `r ≥ 1` satisfy `τ_j = t(H_j) ≠ 0`.  If
`Δ = ∏_j (T^{H_j} − 1)` applied to `G` vanishes on the half-plane `{t ≥ c}`, then there is
`q ≥ 1` with `G(z + qu) = G(z)` for all `z` with `t(z) ≥ c + τ_-`; in particular `G` is fully
periodic on `{t ≥ c + τ_-}`, with the periods `kv` and `qu`, neither of which leaves that
half-plane. -/
-- The proof reuses the `idx`/`row`/`hrow_eq`/`hkey` machinery of `doublyPeriodic_of_ann` below,
-- with every step that used `hexpand`/`hiso` now guarded by the side condition that the *base
-- point* `t0` of the window lies in `{t0 ≥ c}` (where `hvan` is available), and closes with the
-- one-sided finite-state lemma `Nivat.periodic_of_one_sided_determinacy` (`Nivat.Words`) instead
-- of `Nivat.periodic_of_two_sided_determinacy`.
theorem exists_period_of_ann_halfPlane {p : ℕ} [Fact p.Prime] {G : Config (ZMod p)}
    {v u : ℤ × ℤ} (hvu : det v u = 1) {k : ℕ} (hk : 0 < k) (hper : ((k : ℤ) • v) ∈ Per G)
    {r : ℕ} (hr : 0 < r) {H : Fin r → ℤ × ℤ} (hH : ∀ j, pi v (H j) ≠ 0) {c : ℤ}
    (hvan : ∀ z, c ≤ pi v z → act (prodShift H) G z = 0) :
    ∃ q : ℕ, 0 < q ∧ (∀ z, c + tauMinus v H ≤ pi v z → G (z + (q : ℤ) • u) = G z) ∧
      FullyPeriodicOn G (latHalfPlane true v (c + tauMinus v H)) := by
  classical
  have hkZ : (k : ℤ) ≠ 0 := by exact_mod_cast hk.ne'
  have hshift : ∀ (n : ℤ) (z : ℤ × ℤ), G (z + n • ((k : ℤ) • v)) = G z :=
    fun n z => Per.apply (AddSubgroup.zsmul_mem _ hper n) z
  have hpivv : pi v v = 0 := by simp [pi, det]; ring
  have hpivu : pi v u = 1 := hvu
  let idx : ℤ → Fin k := fun s => ⟨(s % (k : ℤ)).toNat, by
    have h1 : 0 ≤ s % (k : ℤ) := Int.emod_nonneg s hkZ
    have h2 : s % (k : ℤ) < (k : ℤ) := Int.emod_lt_of_pos s (by exact_mod_cast hk)
    omega⟩
  let row : ℤ → (Fin k → ZMod p) := fun t s => G ((s.val : ℤ) • v + t • u)
  have hidx_val : ∀ m : Fin k, idx (m.val : ℤ) = m := by
    intro m
    have h1 : (0 : ℤ) ≤ (m.val : ℤ) := Int.natCast_nonneg _
    have h2 : (m.val : ℤ) < (k : ℤ) := by exact_mod_cast m.isLt
    apply Fin.ext
    show ((m.val : ℤ) % (k : ℤ)).toNat = m.val
    rw [Int.emod_eq_of_lt h1 h2, Int.toNat_natCast]
  have hrow_eq : ∀ s t : ℤ, G (s • v + t • u) = row t (idx s) := by
    intro s t
    have h1 : 0 ≤ s % (k : ℤ) := Int.emod_nonneg s hkZ
    have hval : ((idx s).val : ℤ) = s % (k : ℤ) := Int.toNat_of_nonneg h1
    have heuc : s % (k : ℤ) + s / (k : ℤ) * (k : ℤ) = s := by
      have h := Int.mul_ediv_add_emod s (k : ℤ)
      linarith [h, mul_comm (k : ℤ) (s / (k : ℤ))]
    have hsplit : (s % (k : ℤ)) • v + (s / (k : ℤ)) • ((k : ℤ) • v) = s • v := by
      rw [show (s / (k : ℤ)) • ((k : ℤ) • v) = ((s / (k : ℤ)) * (k : ℤ)) • v from
        (mul_smul _ _ _).symm, ← add_smul, heuc]
    have heq : s • v + t • u
        = (((idx s).val : ℤ) • v + t • u) + (s / (k : ℤ)) • ((k : ℤ) • v) := by
      rw [hval, ← hsplit]; abel
    calc G (s • v + t • u)
        = G ((((idx s).val : ℤ) • v + t • u) + (s / (k : ℤ)) • ((k : ℤ) • v)) := by rw [heq]
      _ = G (((idx s).val : ℤ) • v + t • u) := hshift _ _
      _ = row t (idx s) := rfl
  have hpiz : ∀ s t : ℤ, pi v (s • v + t • u) = t := by
    intro s t
    rw [pi_add, pi_smul, pi_smul, hpivv, hpivu, mul_zero, zero_add, mul_one]
  have haj : ∀ j : Fin r, H j = (det (H j) u) • v + (pi v (H j)) • u :=
    fun j => eq_smul_add_smul hvu (H j)
  have hHC_eq : ∀ C : Finset (Fin r), ∑ j ∈ C, H j
      = (∑ j ∈ C, det (H j) u) • v + (∑ j ∈ C, pi v (H j)) • u := by
    intro C
    have step1 : ∑ j ∈ C, H j = ∑ j ∈ C, ((det (H j) u) • v + (pi v (H j)) • u) :=
      Finset.sum_congr rfl fun j _ => haj j
    rw [step1, Finset.sum_add_distrib, ← Finset.sum_smul, ← Finset.sum_smul]
  have hzHC : ∀ (s t0 : ℤ) (C : Finset (Fin r)),
      s • v + t0 • u + ∑ j ∈ C, H j
        = (s + ∑ j ∈ C, det (H j) u) • v + (t0 + ∑ j ∈ C, pi v (H j)) • u := by
    intro s t0 C
    rw [hHC_eq C, add_smul, add_smul]
    abel
  -- `hexpand`/`hiso`/`hkey` now guarded by `c ≤ t0`, the domain where `hvan` is available.
  have hexpand : ∀ z : ℤ × ℤ, c ≤ pi v z →
      (0 : ZMod p) = ∑ C ∈ (Finset.univ : Finset (Fin r)).powerset,
        (-1 : ZMod p) ^ (r - C.card) * G (z + ∑ j ∈ C, H j) := by
    intro z hz
    have h1 := act_prod_mono_sub_one (Finset.univ : Finset (Fin r)) H G z
    rw [Finset.card_univ, Fintype.card_fin] at h1
    calc (0 : ZMod p) = act (prodShift H) G z := (hvan z hz).symm
      _ = act (∏ i ∈ (Finset.univ : Finset (Fin r)), (mono (H i) - 1)) G z := rfl
      _ = _ := h1
  have hiso : ∀ (Cext : Finset (Fin r)) (z : ℤ × ℤ), c ≤ pi v z →
      G (z + ∑ j ∈ Cext, H j)
        = - ∑ C ∈ (Finset.univ : Finset (Fin r)).powerset.erase Cext,
            ((-1 : ZMod p) ^ (r - Cext.card) * (-1 : ZMod p) ^ (r - C.card))
              * G (z + ∑ j ∈ C, H j) := by
    intro Cext z hz
    have hmem : Cext ∈ (Finset.univ : Finset (Fin r)).powerset :=
      Finset.mem_powerset.mpr (Finset.subset_univ _)
    have hsplit := Finset.sum_erase_add (Finset.univ : Finset (Fin r)).powerset
      (fun C => (-1 : ZMod p) ^ (r - C.card) * G (z + ∑ j ∈ C, H j)) hmem
    rw [← hexpand z hz] at hsplit
    have hgCext : (-1 : ZMod p) ^ (r - Cext.card) * G (z + ∑ j ∈ Cext, H j)
        = - ∑ C ∈ (Finset.univ : Finset (Fin r)).powerset.erase Cext,
            (-1 : ZMod p) ^ (r - C.card) * G (z + ∑ j ∈ C, H j) := by
      linear_combination hsplit
    have he2 : (-1 : ZMod p) ^ (r - Cext.card) * (-1 : ZMod p) ^ (r - Cext.card) = 1 := by
      rw [← pow_add, show r - Cext.card + (r - Cext.card) = 2 * (r - Cext.card) by ring, pow_mul]
      norm_num
    have hmul := congrArg (fun x => (-1 : ZMod p) ^ (r - Cext.card) * x) hgCext
    rw [← mul_assoc, he2, one_mul, mul_neg, Finset.mul_sum] at hmul
    rw [hmul]
    congr 1
    refine Finset.sum_congr rfl fun C _ => ?_
    ring
  have hkey : ∀ (Cext : Finset (Fin r)) (s t0 : ℤ), c ≤ t0 →
      row (t0 + ∑ j ∈ Cext, pi v (H j)) (idx (s + ∑ j ∈ Cext, det (H j) u))
        = - ∑ C ∈ (Finset.univ : Finset (Fin r)).powerset.erase Cext,
            ((-1 : ZMod p) ^ (r - Cext.card) * (-1 : ZMod p) ^ (r - C.card))
              * row (t0 + ∑ j ∈ C, pi v (H j)) (idx (s + ∑ j ∈ C, det (H j) u)) := by
    intro Cext s t0 ht0
    have h1 := hiso Cext (s • v + t0 • u) (by rw [hpiz s t0]; exact ht0)
    rw [hzHC s t0 Cext] at h1
    rw [hrow_eq (s + ∑ j ∈ Cext, det (H j) u) (t0 + ∑ j ∈ Cext, pi v (H j))] at h1
    rw [h1]
    congr 1
    refine Finset.sum_congr rfl fun C _ => ?_
    rw [hzHC s t0 C, hrow_eq]
  -- The two extremal subsets and the facts that `tauPlus`/`tauMinus` are their sums; unchanged
  -- from `doublyPeriodic_of_ann` since it is all about the values `pi v (H j)`, not `hvan`.
  have hCp_eq_tauPlus :
      ∑ j ∈ Finset.univ.filter (fun j => 0 < pi v (H j)), pi v (H j) = tauPlus v H := by
    show ∑ j ∈ Finset.univ.filter (fun j => 0 < pi v (H j)), pi v (H j)
        = ∑ j, max (pi v (H j)) 0
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : 0 < pi v (H j)
    · rw [if_pos h, max_eq_left h.le]
    · rw [if_neg h, max_eq_right (not_lt.mp h)]
  have hCm_eq_tauMinus :
      ∑ j ∈ Finset.univ.filter (fun j => pi v (H j) < 0), pi v (H j) = tauMinus v H := by
    show ∑ j ∈ Finset.univ.filter (fun j => pi v (H j) < 0), pi v (H j)
        = ∑ j, min (pi v (H j)) 0
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : pi v (H j) < 0
    · rw [if_pos h, min_eq_left h.le]
    · rw [if_neg h, min_eq_right (not_lt.mp h)]
  have hCp_max : ∀ C : Finset (Fin r), C ≠ Finset.univ.filter (fun j => 0 < pi v (H j)) →
      ∑ j ∈ C, pi v (H j) < tauPlus v H := by
    intro C hC
    have h := sum_lt_sum_filter_pos (fun j => pi v (H j)) hH hC
    rwa [hCp_eq_tauPlus] at h
  have hCm_min : ∀ C : Finset (Fin r), C ≠ Finset.univ.filter (fun j => pi v (H j) < 0) →
      tauMinus v H < ∑ j ∈ C, pi v (H j) := by
    intro C hC
    have hCm_eq : Finset.univ.filter (fun j => pi v (H j) < 0)
        = Finset.univ.filter (fun j => 0 < -pi v (H j)) := by
      apply Finset.filter_congr
      intro j _
      constructor <;> intro h <;> linarith
    have hne : ∀ j, -pi v (H j) ≠ 0 := fun j h => hH j (by linarith)
    have hC' : C ≠ Finset.univ.filter (fun j => 0 < -pi v (H j)) := hCm_eq ▸ hC
    have hlt := sum_lt_sum_filter_pos (fun j => -pi v (H j)) hne hC'
    rw [Finset.sum_neg_distrib] at hlt
    rw [← hCm_eq] at hlt
    rw [Finset.sum_neg_distrib] at hlt
    rw [hCm_eq_tauMinus] at hlt
    linarith
  have hub : ∀ C : Finset (Fin r), ∑ j ∈ C, pi v (H j) ≤ tauPlus v H := by
    intro C
    by_cases h : C = Finset.univ.filter (fun j => 0 < pi v (H j))
    · rw [h, hCp_eq_tauPlus]
    · exact (hCp_max C h).le
  have hlb : ∀ C : Finset (Fin r), tauMinus v H ≤ ∑ j ∈ C, pi v (H j) := by
    intro C
    by_cases h : C = Finset.univ.filter (fun j => pi v (H j) < 0)
    · rw [h, hCm_eq_tauMinus]
    · exact (hCm_min C h).le
  let j0 : Fin r := ⟨0, hr⟩
  have hj0ne := hH j0
  have hlbj : tauMinus v H ≤ pi v (H j0) := by
    have h := hlb {j0}; rwa [Finset.sum_singleton] at h
  have hubj : pi v (H j0) ≤ tauPlus v H := by
    have h := hub {j0}; rwa [Finset.sum_singleton] at h
  have hstrict : tauMinus v H < tauPlus v H := by
    rcases lt_or_gt_of_ne hj0ne with h | h
    · have h1 : tauMinus v H < 0 := lt_of_le_of_lt hlbj h
      linarith [tauPlus_nonneg v H]
    · have h1 : (0 : ℤ) < tauPlus v H := lt_of_lt_of_le h hubj
      linarith [tauMinus_nonpos v H]
  set L : ℕ := (tauPlus v H - tauMinus v H).toNat with hLdef
  have hLZ : (L : ℤ) = tauPlus v H - tauMinus v H := by
    rw [hLdef]; exact Int.toNat_of_nonneg (by omega)
  have hL_pos : 0 < L := by
    have h : (0 : ℤ) < (L : ℤ) := by rw [hLZ]; omega
    exact_mod_cast h
  have hkeyCp : ∀ s t0 : ℤ, c ≤ t0 →
      row (t0 + tauPlus v H)
          (idx (s + ∑ j ∈ Finset.univ.filter (fun j => 0 < pi v (H j)), det (H j) u))
        = - ∑ C ∈ (Finset.univ : Finset (Fin r)).powerset.erase
              (Finset.univ.filter (fun j => 0 < pi v (H j))),
            ((-1 : ZMod p) ^ (r - (Finset.univ.filter (fun j => 0 < pi v (H j))).card)
                * (-1 : ZMod p) ^ (r - C.card))
              * row (t0 + ∑ j ∈ C, pi v (H j)) (idx (s + ∑ j ∈ C, det (H j) u)) := by
    intro s t0 ht0
    have h := hkey (Finset.univ.filter (fun j => 0 < pi v (H j))) s t0 ht0
    rwa [hCp_eq_tauPlus] at h
  have hkeyCm : ∀ s t0 : ℤ, c ≤ t0 →
      row (t0 + tauMinus v H)
          (idx (s + ∑ j ∈ Finset.univ.filter (fun j => pi v (H j) < 0), det (H j) u))
        = - ∑ C ∈ (Finset.univ : Finset (Fin r)).powerset.erase
              (Finset.univ.filter (fun j => pi v (H j) < 0)),
            ((-1 : ZMod p) ^ (r - (Finset.univ.filter (fun j => pi v (H j) < 0)).card)
                * (-1 : ZMod p) ^ (r - C.card))
              * row (t0 + ∑ j ∈ C, pi v (H j)) (idx (s + ∑ j ∈ C, det (H j) u)) := by
    intro s t0 ht0
    have h := hkey (Finset.univ.filter (fun j => pi v (H j) < 0)) s t0 ht0
    rwa [hCm_eq_tauMinus] at h
  set cm : ℤ := c + tauMinus v H with hcmdef
  have hfwd : ∀ i j : ℤ, cm ≤ i → cm ≤ j →
      (∀ l : ℕ, l < L → row (i + l) = row (j + l)) → row (i + L) = row (j + L) := by
    intro i j hi hj hwin
    set t0 := i - tauMinus v H with ht0
    set t0' := j - tauMinus v H with ht0'
    have hct0 : c ≤ t0 := by rw [ht0, hcmdef] at *; linarith
    have hct0' : c ≤ t0' := by rw [ht0', hcmdef] at *; linarith
    have hiL : i + (L : ℤ) = t0 + tauPlus v H := by rw [ht0, hLZ]; ring
    have hjL : j + (L : ℤ) = t0' + tauPlus v H := by rw [ht0', hLZ]; ring
    have hCmatch : ∀ C ∈ (Finset.univ : Finset (Fin r)).powerset.erase
        (Finset.univ.filter (fun j => 0 < pi v (H j))),
        row (t0 + ∑ j ∈ C, pi v (H j)) = row (t0' + ∑ j ∈ C, pi v (H j)) := by
      intro C hCmem
      have hCne : C ≠ Finset.univ.filter (fun j => 0 < pi v (H j)) :=
        (Finset.mem_erase.mp hCmem).1
      have hwC_lt : ∑ j ∈ C, pi v (H j) < tauPlus v H := hCp_max C hCne
      have hwC_ge : tauMinus v H ≤ ∑ j ∈ C, pi v (H j) := hlb C
      set l : ℤ := ∑ j ∈ C, pi v (H j) - tauMinus v H with hldef
      have hl0 : 0 ≤ l := by rw [hldef]; linarith
      have hlL : l < (L : ℤ) := by rw [hldef, hLZ]; linarith
      have heq1 : t0 + ∑ j ∈ C, pi v (H j) = i + l := by rw [ht0, hldef]; ring
      have heq2 : t0' + ∑ j ∈ C, pi v (H j) = j + l := by rw [ht0', hldef]; ring
      have hlnat : (l.toNat : ℤ) = l := Int.toNat_of_nonneg hl0
      have hwin' := hwin l.toNat (by
        have hh : (l.toNat : ℤ) < (L : ℤ) := by rw [hlnat]; exact hlL
        exact_mod_cast hh)
      rw [heq1, heq2, ← hlnat]
      exact hwin'
    have hpointwise : ∀ m : Fin k, row (t0 + tauPlus v H) m = row (t0' + tauPlus v H) m := by
      intro m
      set s : ℤ := (m.val : ℤ) - ∑ j ∈ Finset.univ.filter (fun j => 0 < pi v (H j)), det (H j) u
        with hsdef
      have hidxs :
          idx (s + ∑ j ∈ Finset.univ.filter (fun j => 0 < pi v (H j)), det (H j) u) = m := by
        have hh : s + ∑ j ∈ Finset.univ.filter (fun j => 0 < pi v (H j)), det (H j) u
            = (m.val : ℤ) := by rw [hsdef]; ring
        rw [hh, hidx_val]
      have h1 := hkeyCp s t0 hct0
      have h2 := hkeyCp s t0' hct0'
      rw [hidxs] at h1 h2
      rw [h1, h2]
      congr 1
      refine Finset.sum_congr rfl fun C hC => ?_
      rw [congrFun (hCmatch C hC) (idx (s + ∑ j ∈ C, det (H j) u))]
    have hfinal : row (t0 + tauPlus v H) = row (t0' + tauPlus v H) := funext hpointwise
    rw [hiL, hjL]
    exact hfinal
  have hbwd : ∀ i j : ℤ, cm + 1 ≤ i → cm + 1 ≤ j →
      (∀ l : ℕ, l < L → row (i + l) = row (j + l)) → row (i - 1) = row (j - 1) := by
    intro i j hi hj hwin
    set t0 := i - 1 - tauMinus v H with ht0
    set t0' := j - 1 - tauMinus v H with ht0'
    have hct0 : c ≤ t0 := by rw [ht0, hcmdef] at *; linarith
    have hct0' : c ≤ t0' := by rw [ht0', hcmdef] at *; linarith
    have hi1 : i - 1 = t0 + tauMinus v H := by rw [ht0]; ring
    have hj1 : j - 1 = t0' + tauMinus v H := by rw [ht0']; ring
    have hCmatch : ∀ C ∈ (Finset.univ : Finset (Fin r)).powerset.erase
        (Finset.univ.filter (fun j => pi v (H j) < 0)),
        row (t0 + ∑ j ∈ C, pi v (H j)) = row (t0' + ∑ j ∈ C, pi v (H j)) := by
      intro C hCmem
      have hCne : C ≠ Finset.univ.filter (fun j => pi v (H j) < 0) :=
        (Finset.mem_erase.mp hCmem).1
      have hwC_gt : tauMinus v H < ∑ j ∈ C, pi v (H j) := hCm_min C hCne
      have hwC_le : ∑ j ∈ C, pi v (H j) ≤ tauPlus v H := hub C
      set l : ℤ := ∑ j ∈ C, pi v (H j) - tauMinus v H - 1 with hldef
      have hl0 : 0 ≤ l := by rw [hldef]; linarith
      have hlL : l < (L : ℤ) := by rw [hldef, hLZ]; linarith
      have heq1 : t0 + ∑ j ∈ C, pi v (H j) = i + l := by rw [ht0, hldef]; ring
      have heq2 : t0' + ∑ j ∈ C, pi v (H j) = j + l := by rw [ht0', hldef]; ring
      have hlnat : (l.toNat : ℤ) = l := Int.toNat_of_nonneg hl0
      have hwin' := hwin l.toNat (by
        have hh : (l.toNat : ℤ) < (L : ℤ) := by rw [hlnat]; exact hlL
        exact_mod_cast hh)
      rw [heq1, heq2, ← hlnat]
      exact hwin'
    have hpointwise : ∀ m : Fin k, row (t0 + tauMinus v H) m = row (t0' + tauMinus v H) m := by
      intro m
      set s : ℤ := (m.val : ℤ) - ∑ j ∈ Finset.univ.filter (fun j => pi v (H j) < 0), det (H j) u
        with hsdef
      have hidxs :
          idx (s + ∑ j ∈ Finset.univ.filter (fun j => pi v (H j) < 0), det (H j) u) = m := by
        have hh : s + ∑ j ∈ Finset.univ.filter (fun j => pi v (H j) < 0), det (H j) u
            = (m.val : ℤ) := by rw [hsdef]; ring
        rw [hh, hidx_val]
      have h1 := hkeyCm s t0 hct0
      have h2 := hkeyCm s t0' hct0'
      rw [hidxs] at h1 h2
      rw [h1, h2]
      congr 1
      refine Finset.sum_congr rfl fun C hC => ?_
      rw [congrFun (hCmatch C hC) (idx (s + ∑ j ∈ C, det (H j) u))]
    have hfinal : row (t0 + tauMinus v H) = row (t0' + tauMinus v H) := funext hpointwise
    rw [hi1, hj1]
    exact hfinal
  obtain ⟨q, hqpos, hqper⟩ := periodic_of_one_sided_determinacy hL_pos row cm hfwd hbwd
  have hqG : ∀ z, cm ≤ pi v z → G (z + (q : ℤ) • u) = G z := by
    intro z hz
    set s0 := det z u with hs0
    set t0 := pi v z with ht0
    have hzeq : z = s0 • v + t0 • u := eq_smul_add_smul hvu z
    have hzeq' : z + (q : ℤ) • u = s0 • v + (t0 + (q : ℤ)) • u := by
      rw [hzeq, add_smul]; abel
    rw [hzeq', hzeq, hrow_eq, hrow_eq]
    exact congrFun (hqper t0 hz) (idx s0)
  refine ⟨q, hqpos, hqG, ?_⟩
  refine ⟨(k : ℤ) • v, (q : ℤ) • u, ?_, ?_, ?_, ?_, ?_⟩
  · have heq : det ((k : ℤ) • v) ((q : ℤ) • u) = (k : ℤ) * (q : ℤ) * det v u := by
      simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
    rw [heq, hvu, mul_one]
    have hqZ : (q : ℤ) ≠ 0 := by exact_mod_cast hqpos.ne'
    exact mul_ne_zero hkZ hqZ
  · intro z hzU
    simp only [latHalfPlane, Set.mem_ofPred_eq, piE, if_true] at hzU ⊢
    have : pi v (z + (k : ℤ) • v) = pi v z := by
      rw [pi_add, pi_smul, hpivv, mul_zero, add_zero]
    rw [this]; exact hzU
  · intro z hzU
    simp only [latHalfPlane, Set.mem_ofPred_eq, piE, if_true] at hzU ⊢
    have : pi v (z + (q : ℤ) • u) = pi v z + (q : ℤ) := by
      rw [pi_add, pi_smul, hpivu, mul_one]
    rw [this]
    have hqnn : (0 : ℤ) ≤ (q : ℤ) := Int.natCast_nonneg _
    linarith
  · intro z hzU
    simp only [latHalfPlane, Set.mem_ofPred_eq, piE, if_true] at hzU
    exact Per.apply hper z
  · intro z hzU
    simp only [latHalfPlane, Set.mem_ofPred_eq, piE, if_true] at hzU
    exact hqG z hzU

/-- **Lemma 8.8**, whole-plane case: if `Δ G ≡ 0` then `G` is doubly periodic. -/
-- TODO(lineM): unproved; identical combinatorial core to `exists_period_of_ann_halfPlane` above
-- (the `fwd`/`bwd` derivation from `hvan` via `sum_lt_sum_filter_pos`), but since `hvan` holds
-- everywhere the domain restriction there disappears, so `periodic_of_two_sided_determinacy`
-- (already stated in `Nivat/AppendixD.lean`, with `Q := 1` so the phase hypothesis
-- `(i : ZMod 1) = (j : ZMod 1)` is vacuous) applies *directly* to `y := row : ℤ → (Fin k → ZMod
-- p)`, `K := L`, to produce `q > 0` with `row (t + q) = row t` for all `t : ℤ` (no need for the
-- one-sided bijection argument sketched above — this is the easier of the two).  From `q • u ∈
-- Per G` (unwinding `hrow_eq`) and `hper : (k:ℤ) • v ∈ Per G`, `DoublyPeriodic G` follows from
-- `det ((k:ℤ) • v) ((q:ℤ) • u) = k * q * det v u = k * q ≠ 0` (`hvu`, `hk`, `q > 0`).
theorem doublyPeriodic_of_ann {p : ℕ} [Fact p.Prime] {G : Config (ZMod p)}
    {v u : ℤ × ℤ} (hvu : det v u = 1) {k : ℕ} (hk : 0 < k) (hper : ((k : ℤ) • v) ∈ Per G)
    {r : ℕ} (hr : 0 < r) {H : Fin r → ℤ × ℤ} (hH : ∀ j, pi v (H j) ≠ 0)
    (hvan : act (prodShift H) G = 0) : DoublyPeriodic G := by
  classical
  have hkZ : (k : ℤ) ≠ 0 := by exact_mod_cast hk.ne'
  have hshift : ∀ (n : ℤ) (z : ℤ × ℤ), G (z + n • ((k : ℤ) • v)) = G z :=
    fun n z => Per.apply (AddSubgroup.zsmul_mem _ hper n) z
  -- `idx s : Fin k` is `s` reduced mod `k`; `row t s := G (s • v + t • u)` is the finite-state
  -- "row" of §D.1's finite-state argument, one row per value of the `u`-coordinate `t`.
  let idx : ℤ → Fin k := fun s => ⟨(s % (k : ℤ)).toNat, by
    have h1 : 0 ≤ s % (k : ℤ) := Int.emod_nonneg s hkZ
    have h2 : s % (k : ℤ) < (k : ℤ) := Int.emod_lt_of_pos s (by exact_mod_cast hk)
    omega⟩
  let row : ℤ → (Fin k → ZMod p) := fun t s => G ((s.val : ℤ) • v + t • u)
  have hidx_val : ∀ m : Fin k, idx (m.val : ℤ) = m := by
    intro m
    have h1 : (0 : ℤ) ≤ (m.val : ℤ) := Int.natCast_nonneg _
    have h2 : (m.val : ℤ) < (k : ℤ) := by exact_mod_cast m.isLt
    apply Fin.ext
    show ((m.val : ℤ) % (k : ℤ)).toNat = m.val
    rw [Int.emod_eq_of_lt h1 h2, Int.toNat_natCast]
  have hrow_eq : ∀ s t : ℤ, G (s • v + t • u) = row t (idx s) := by
    intro s t
    have h1 : 0 ≤ s % (k : ℤ) := Int.emod_nonneg s hkZ
    have hval : ((idx s).val : ℤ) = s % (k : ℤ) := Int.toNat_of_nonneg h1
    have heuc : s % (k : ℤ) + s / (k : ℤ) * (k : ℤ) = s := by
      have h := Int.mul_ediv_add_emod s (k : ℤ)
      linarith [h, mul_comm (k : ℤ) (s / (k : ℤ))]
    have hsplit : (s % (k : ℤ)) • v + (s / (k : ℤ)) • ((k : ℤ) • v) = s • v := by
      rw [show (s / (k : ℤ)) • ((k : ℤ) • v) = ((s / (k : ℤ)) * (k : ℤ)) • v from
        (mul_smul _ _ _).symm, ← add_smul, heuc]
    have heq : s • v + t • u
        = (((idx s).val : ℤ) • v + t • u) + (s / (k : ℤ)) • ((k : ℤ) • v) := by
      rw [hval, ← hsplit]; abel
    calc G (s • v + t • u)
        = G ((((idx s).val : ℤ) • v + t • u) + (s / (k : ℤ)) • ((k : ℤ) • v)) := by rw [heq]
      _ = G (((idx s).val : ℤ) • v + t • u) := hshift _ _
      _ = row t (idx s) := rfl
  -- The linear-algebra bookkeeping: `H j = (det (H j) u) • v + (pi v (H j)) • u`, so a subsum
  -- `H_C = ∑_{j ∈ C} H j` shifts the `(v, u)`-coordinates by `(∑_{j∈C} det (H j) u, ∑_{j∈C} pi v
  -- (H j))`.
  have haj : ∀ j : Fin r, H j = (det (H j) u) • v + (pi v (H j)) • u :=
    fun j => eq_smul_add_smul hvu (H j)
  have hHC_eq : ∀ C : Finset (Fin r), ∑ j ∈ C, H j
      = (∑ j ∈ C, det (H j) u) • v + (∑ j ∈ C, pi v (H j)) • u := by
    intro C
    have step1 : ∑ j ∈ C, H j = ∑ j ∈ C, ((det (H j) u) • v + (pi v (H j)) • u) :=
      Finset.sum_congr rfl fun j _ => haj j
    rw [step1, Finset.sum_add_distrib, ← Finset.sum_smul, ← Finset.sum_smul]
  have hzHC : ∀ (s t0 : ℤ) (C : Finset (Fin r)),
      s • v + t0 • u + ∑ j ∈ C, H j
        = (s + ∑ j ∈ C, det (H j) u) • v + (t0 + ∑ j ∈ C, pi v (H j)) • u := by
    intro s t0 C
    rw [hHC_eq C, add_smul, add_smul]
    abel
  -- Expand `hvan` via `act_prod_mono_sub_one`.
  have hexpand : ∀ z : ℤ × ℤ,
      (0 : ZMod p) = ∑ C ∈ (Finset.univ : Finset (Fin r)).powerset,
        (-1 : ZMod p) ^ (r - C.card) * G (z + ∑ j ∈ C, H j) := by
    intro z
    have h1 := act_prod_mono_sub_one (Finset.univ : Finset (Fin r)) H G z
    rw [Finset.card_univ, Fintype.card_fin] at h1
    calc (0 : ZMod p) = act (prodShift H) G z := (congrFun hvan z).symm
      _ = act (∏ i ∈ (Finset.univ : Finset (Fin r)), (mono (H i) - 1)) G z := rfl
      _ = _ := h1
  -- Isolating the `Cext` term from the vanishing sum: a purely algebraic identity, valid for
  -- *any* `Cext ⊆ univ`.  The combinatorial content (which `Cext` to use, and why the other
  -- terms lie in the right window) comes later.
  have hiso : ∀ (Cext : Finset (Fin r)) (z : ℤ × ℤ),
      G (z + ∑ j ∈ Cext, H j)
        = - ∑ C ∈ (Finset.univ : Finset (Fin r)).powerset.erase Cext,
            ((-1 : ZMod p) ^ (r - Cext.card) * (-1 : ZMod p) ^ (r - C.card))
              * G (z + ∑ j ∈ C, H j) := by
    intro Cext z
    have hmem : Cext ∈ (Finset.univ : Finset (Fin r)).powerset :=
      Finset.mem_powerset.mpr (Finset.subset_univ _)
    have hsplit := Finset.sum_erase_add (Finset.univ : Finset (Fin r)).powerset
      (fun C => (-1 : ZMod p) ^ (r - C.card) * G (z + ∑ j ∈ C, H j)) hmem
    rw [← hexpand z] at hsplit
    have hgCext : (-1 : ZMod p) ^ (r - Cext.card) * G (z + ∑ j ∈ Cext, H j)
        = - ∑ C ∈ (Finset.univ : Finset (Fin r)).powerset.erase Cext,
            (-1 : ZMod p) ^ (r - C.card) * G (z + ∑ j ∈ C, H j) := by
      linear_combination hsplit
    have he2 : (-1 : ZMod p) ^ (r - Cext.card) * (-1 : ZMod p) ^ (r - Cext.card) = 1 := by
      rw [← pow_add, show r - Cext.card + (r - Cext.card) = 2 * (r - Cext.card) by ring, pow_mul]
      norm_num
    have hmul := congrArg (fun x => (-1 : ZMod p) ^ (r - Cext.card) * x) hgCext
    rw [← mul_assoc, he2, one_mul, mul_neg, Finset.mul_sum] at hmul
    rw [hmul]
    congr 1
    refine Finset.sum_congr rfl fun C _ => ?_
    ring
  -- Combine `hiso` with `hrow_eq`/`hzHC`: the "one-formula" identity, generic in `Cext`.
  have hkey : ∀ (Cext : Finset (Fin r)) (s t0 : ℤ),
      row (t0 + ∑ j ∈ Cext, pi v (H j)) (idx (s + ∑ j ∈ Cext, det (H j) u))
        = - ∑ C ∈ (Finset.univ : Finset (Fin r)).powerset.erase Cext,
            ((-1 : ZMod p) ^ (r - Cext.card) * (-1 : ZMod p) ^ (r - C.card))
              * row (t0 + ∑ j ∈ C, pi v (H j)) (idx (s + ∑ j ∈ C, det (H j) u)) := by
    intro Cext s t0
    have h1 := hiso Cext (s • v + t0 • u)
    rw [hzHC s t0 Cext] at h1
    rw [hrow_eq (s + ∑ j ∈ Cext, det (H j) u) (t0 + ∑ j ∈ Cext, pi v (H j))] at h1
    rw [h1]
    congr 1
    refine Finset.sum_congr rfl fun C _ => ?_
    rw [hzHC s t0 C, hrow_eq]
  -- The two extremal subsets and the facts that `tauPlus`/`tauMinus` are their sums.
  have hCp_eq_tauPlus :
      ∑ j ∈ Finset.univ.filter (fun j => 0 < pi v (H j)), pi v (H j) = tauPlus v H := by
    show ∑ j ∈ Finset.univ.filter (fun j => 0 < pi v (H j)), pi v (H j)
        = ∑ j, max (pi v (H j)) 0
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : 0 < pi v (H j)
    · rw [if_pos h, max_eq_left h.le]
    · rw [if_neg h, max_eq_right (not_lt.mp h)]
  have hCm_eq_tauMinus :
      ∑ j ∈ Finset.univ.filter (fun j => pi v (H j) < 0), pi v (H j) = tauMinus v H := by
    show ∑ j ∈ Finset.univ.filter (fun j => pi v (H j) < 0), pi v (H j)
        = ∑ j, min (pi v (H j)) 0
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : pi v (H j) < 0
    · rw [if_pos h, min_eq_left h.le]
    · rw [if_neg h, min_eq_right (not_lt.mp h)]
  have hCp_max : ∀ C : Finset (Fin r), C ≠ Finset.univ.filter (fun j => 0 < pi v (H j)) →
      ∑ j ∈ C, pi v (H j) < tauPlus v H := by
    intro C hC
    have h := sum_lt_sum_filter_pos (fun j => pi v (H j)) hH hC
    rwa [hCp_eq_tauPlus] at h
  have hCm_min : ∀ C : Finset (Fin r), C ≠ Finset.univ.filter (fun j => pi v (H j) < 0) →
      tauMinus v H < ∑ j ∈ C, pi v (H j) := by
    intro C hC
    have hCm_eq : Finset.univ.filter (fun j => pi v (H j) < 0)
        = Finset.univ.filter (fun j => 0 < -pi v (H j)) := by
      apply Finset.filter_congr
      intro j _
      constructor <;> intro h <;> linarith
    have hne : ∀ j, -pi v (H j) ≠ 0 := fun j h => hH j (by linarith)
    have hC' : C ≠ Finset.univ.filter (fun j => 0 < -pi v (H j)) := hCm_eq ▸ hC
    have hlt := sum_lt_sum_filter_pos (fun j => -pi v (H j)) hne hC'
    rw [Finset.sum_neg_distrib] at hlt
    rw [← hCm_eq] at hlt
    rw [Finset.sum_neg_distrib] at hlt
    rw [hCm_eq_tauMinus] at hlt
    linarith
  have hub : ∀ C : Finset (Fin r), ∑ j ∈ C, pi v (H j) ≤ tauPlus v H := by
    intro C
    by_cases h : C = Finset.univ.filter (fun j => 0 < pi v (H j))
    · rw [h, hCp_eq_tauPlus]
    · exact (hCp_max C h).le
  have hlb : ∀ C : Finset (Fin r), tauMinus v H ≤ ∑ j ∈ C, pi v (H j) := by
    intro C
    by_cases h : C = Finset.univ.filter (fun j => pi v (H j) < 0)
    · rw [h, hCm_eq_tauMinus]
    · exact (hCm_min C h).le
  -- `tauMinus < tauPlus`, using some `j₀` with `pi v (H j₀) ≠ 0`.
  let j0 : Fin r := ⟨0, hr⟩
  have hj0ne := hH j0
  have hlbj : tauMinus v H ≤ pi v (H j0) := by
    have h := hlb {j0}; rwa [Finset.sum_singleton] at h
  have hubj : pi v (H j0) ≤ tauPlus v H := by
    have h := hub {j0}; rwa [Finset.sum_singleton] at h
  have hstrict : tauMinus v H < tauPlus v H := by
    rcases lt_or_gt_of_ne hj0ne with h | h
    · have h1 : tauMinus v H < 0 := lt_of_le_of_lt hlbj h
      linarith [tauPlus_nonneg v H]
    · have h1 : (0 : ℤ) < tauPlus v H := lt_of_lt_of_le h hubj
      linarith [tauMinus_nonpos v H]
  set L : ℕ := (tauPlus v H - tauMinus v H).toNat with hLdef
  have hLZ : (L : ℤ) = tauPlus v H - tauMinus v H := by
    rw [hLdef]; exact Int.toNat_of_nonneg (by omega)
  have hL_pos : 0 < L := by
    have h : (0 : ℤ) < (L : ℤ) := by rw [hLZ]; omega
    exact_mod_cast h
  -- The two specialisations of `hkey` that will feed `fwd`/`bwd`.
  have hkeyCp : ∀ s t0 : ℤ,
      row (t0 + tauPlus v H)
          (idx (s + ∑ j ∈ Finset.univ.filter (fun j => 0 < pi v (H j)), det (H j) u))
        = - ∑ C ∈ (Finset.univ : Finset (Fin r)).powerset.erase
              (Finset.univ.filter (fun j => 0 < pi v (H j))),
            ((-1 : ZMod p) ^ (r - (Finset.univ.filter (fun j => 0 < pi v (H j))).card)
                * (-1 : ZMod p) ^ (r - C.card))
              * row (t0 + ∑ j ∈ C, pi v (H j)) (idx (s + ∑ j ∈ C, det (H j) u)) := by
    intro s t0
    have h := hkey (Finset.univ.filter (fun j => 0 < pi v (H j))) s t0
    rwa [hCp_eq_tauPlus] at h
  have hkeyCm : ∀ s t0 : ℤ,
      row (t0 + tauMinus v H)
          (idx (s + ∑ j ∈ Finset.univ.filter (fun j => pi v (H j) < 0), det (H j) u))
        = - ∑ C ∈ (Finset.univ : Finset (Fin r)).powerset.erase
              (Finset.univ.filter (fun j => pi v (H j) < 0)),
            ((-1 : ZMod p) ^ (r - (Finset.univ.filter (fun j => pi v (H j) < 0)).card)
                * (-1 : ZMod p) ^ (r - C.card))
              * row (t0 + ∑ j ∈ C, pi v (H j)) (idx (s + ∑ j ∈ C, det (H j) u)) := by
    intro s t0
    have h := hkey (Finset.univ.filter (fun j => pi v (H j) < 0)) s t0
    rwa [hCm_eq_tauMinus] at h
  have hfwd : ∀ i j : ℤ, (i : ZMod 1) = (j : ZMod 1) →
      (∀ l : ℕ, l < L → row (i + l) = row (j + l)) → row (i + L) = row (j + L) := by
    intro i j _ hwin
    set t0 := i - tauMinus v H with ht0
    set t0' := j - tauMinus v H with ht0'
    have hiL : i + (L : ℤ) = t0 + tauPlus v H := by rw [ht0, hLZ]; ring
    have hjL : j + (L : ℤ) = t0' + tauPlus v H := by rw [ht0', hLZ]; ring
    have hCmatch : ∀ C ∈ (Finset.univ : Finset (Fin r)).powerset.erase
        (Finset.univ.filter (fun j => 0 < pi v (H j))),
        row (t0 + ∑ j ∈ C, pi v (H j)) = row (t0' + ∑ j ∈ C, pi v (H j)) := by
      intro C hCmem
      have hCne : C ≠ Finset.univ.filter (fun j => 0 < pi v (H j)) :=
        (Finset.mem_erase.mp hCmem).1
      have hwC_lt : ∑ j ∈ C, pi v (H j) < tauPlus v H := hCp_max C hCne
      have hwC_ge : tauMinus v H ≤ ∑ j ∈ C, pi v (H j) := hlb C
      set l : ℤ := ∑ j ∈ C, pi v (H j) - tauMinus v H with hldef
      have hl0 : 0 ≤ l := by rw [hldef]; linarith
      have hlL : l < (L : ℤ) := by rw [hldef, hLZ]; linarith
      have heq1 : t0 + ∑ j ∈ C, pi v (H j) = i + l := by rw [ht0, hldef]; ring
      have heq2 : t0' + ∑ j ∈ C, pi v (H j) = j + l := by rw [ht0', hldef]; ring
      have hlnat : (l.toNat : ℤ) = l := Int.toNat_of_nonneg hl0
      have hwin' := hwin l.toNat (by
        have hh : (l.toNat : ℤ) < (L : ℤ) := by rw [hlnat]; exact hlL
        exact_mod_cast hh)
      rw [heq1, heq2, ← hlnat]
      exact hwin'
    have hpointwise : ∀ m : Fin k, row (t0 + tauPlus v H) m = row (t0' + tauPlus v H) m := by
      intro m
      set s : ℤ := (m.val : ℤ) - ∑ j ∈ Finset.univ.filter (fun j => 0 < pi v (H j)), det (H j) u
        with hsdef
      have hidxs :
          idx (s + ∑ j ∈ Finset.univ.filter (fun j => 0 < pi v (H j)), det (H j) u) = m := by
        have hh : s + ∑ j ∈ Finset.univ.filter (fun j => 0 < pi v (H j)), det (H j) u
            = (m.val : ℤ) := by rw [hsdef]; ring
        rw [hh, hidx_val]
      have h1 := hkeyCp s t0
      have h2 := hkeyCp s t0'
      rw [hidxs] at h1 h2
      rw [h1, h2]
      congr 1
      refine Finset.sum_congr rfl fun C hC => ?_
      rw [congrFun (hCmatch C hC) (idx (s + ∑ j ∈ C, det (H j) u))]
    have hfinal : row (t0 + tauPlus v H) = row (t0' + tauPlus v H) := funext hpointwise
    rw [hiL, hjL]
    exact hfinal
  have hbwd : ∀ i j : ℤ, (i : ZMod 1) = (j : ZMod 1) →
      (∀ l : ℕ, l < L → row (i + l) = row (j + l)) → row (i - 1) = row (j - 1) := by
    intro i j _ hwin
    set t0 := i - 1 - tauMinus v H with ht0
    set t0' := j - 1 - tauMinus v H with ht0'
    have hi1 : i - 1 = t0 + tauMinus v H := by rw [ht0]; ring
    have hj1 : j - 1 = t0' + tauMinus v H := by rw [ht0']; ring
    have hCmatch : ∀ C ∈ (Finset.univ : Finset (Fin r)).powerset.erase
        (Finset.univ.filter (fun j => pi v (H j) < 0)),
        row (t0 + ∑ j ∈ C, pi v (H j)) = row (t0' + ∑ j ∈ C, pi v (H j)) := by
      intro C hCmem
      have hCne : C ≠ Finset.univ.filter (fun j => pi v (H j) < 0) :=
        (Finset.mem_erase.mp hCmem).1
      have hwC_gt : tauMinus v H < ∑ j ∈ C, pi v (H j) := hCm_min C hCne
      have hwC_le : ∑ j ∈ C, pi v (H j) ≤ tauPlus v H := hub C
      set l : ℤ := ∑ j ∈ C, pi v (H j) - tauMinus v H - 1 with hldef
      have hl0 : 0 ≤ l := by rw [hldef]; linarith
      have hlL : l < (L : ℤ) := by rw [hldef, hLZ]; linarith
      have heq1 : t0 + ∑ j ∈ C, pi v (H j) = i + l := by rw [ht0, hldef]; ring
      have heq2 : t0' + ∑ j ∈ C, pi v (H j) = j + l := by rw [ht0', hldef]; ring
      have hlnat : (l.toNat : ℤ) = l := Int.toNat_of_nonneg hl0
      have hwin' := hwin l.toNat (by
        have hh : (l.toNat : ℤ) < (L : ℤ) := by rw [hlnat]; exact hlL
        exact_mod_cast hh)
      rw [heq1, heq2, ← hlnat]
      exact hwin'
    have hpointwise : ∀ m : Fin k, row (t0 + tauMinus v H) m = row (t0' + tauMinus v H) m := by
      intro m
      set s : ℤ := (m.val : ℤ) - ∑ j ∈ Finset.univ.filter (fun j => pi v (H j) < 0), det (H j) u
        with hsdef
      have hidxs :
          idx (s + ∑ j ∈ Finset.univ.filter (fun j => pi v (H j) < 0), det (H j) u) = m := by
        have hh : s + ∑ j ∈ Finset.univ.filter (fun j => pi v (H j) < 0), det (H j) u
            = (m.val : ℤ) := by rw [hsdef]; ring
        rw [hh, hidx_val]
      have h1 := hkeyCm s t0
      have h2 := hkeyCm s t0'
      rw [hidxs] at h1 h2
      rw [h1, h2]
      congr 1
      refine Finset.sum_congr rfl fun C hC => ?_
      rw [congrFun (hCmatch C hC) (idx (s + ∑ j ∈ C, det (H j) u))]
    have hfinal : row (t0 + tauMinus v H) = row (t0' + tauMinus v H) := funext hpointwise
    rw [hi1, hj1]
    exact hfinal
  obtain ⟨Q', hQ'pos, -, hQ'per⟩ :=
    periodic_of_two_sided_determinacy (Q := 1) (K := L) Nat.one_pos hL_pos row hfwd hbwd
  have hGper : ((Q' : ℤ) • u) ∈ Per G := by
    rw [mem_Per_iff]
    funext z
    show G (z + (Q' : ℤ) • u) = G z
    set s0 := det z u with hs0
    set t0 := pi v z with ht0
    have hz : z = s0 • v + t0 • u := eq_smul_add_smul hvu z
    have hz' : z + (Q' : ℤ) • u = s0 • v + (t0 + (Q' : ℤ)) • u := by
      rw [hz, add_smul]; abel
    rw [hz', hz, hrow_eq, hrow_eq]
    exact congrFun (hQ'per t0) (idx s0)
  have hdetkq : det ((k : ℤ) • v) ((Q' : ℤ) • u) ≠ 0 := by
    have heq : det ((k : ℤ) • v) ((Q' : ℤ) • u) = (k : ℤ) * (Q' : ℤ) * det v u := by
      simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
    rw [heq, hvu, mul_one]
    have hQ'Z : (Q' : ℤ) ≠ 0 := by exact_mod_cast hQ'pos.ne'
    exact mul_ne_zero hkZ hQ'Z
  exact ⟨(k : ℤ) • v, hper, (Q' : ℤ) • u, hGper, hdetkq⟩

/-! ### Proposition 8.9 -/

/-- A *closed sector of opening strictly between `0` and `π`*: the set of non-negative
combinations of two linearly independent vectors.  Paper Proposition 8.9(c). -/
def IsSector (K : Set (ℝ × ℝ)) : Prop :=
  ∃ w₁ w₂ : ℝ × ℝ, w₁.1 * w₂.2 - w₁.2 * w₂.1 ≠ 0 ∧
    K = {y | ∃ s t : ℝ, 0 ≤ s ∧ 0 ≤ t ∧ y = s • w₁ + t • w₂}

section Prop89

variable {p : ℕ} [Fact p.Prime] {m : ℕ} {zeta : Config (ZMod p)} {G : Fin m → Config (ZMod p)}
  {v : Fin m → ℤ × ℤ} {k : Fin m → ℕ} {R : Set (ℤ × ℤ)} {a b : ℤ × ℤ}
  (hm : 2 ≤ m) (hsum : ∀ z, zeta z = ∑ i, G i z) (hv : ∀ i, Primitive (v i))
  (hk : ∀ i, 0 < k i) (hper : ∀ i, ((k i : ℤ) • v i) ∈ Per (G i))
  (hnp : Pairwise fun i j => det (v i) (v j) ≠ 0)
  (hR : IsLatticeConvexRegion R) (hRne : R.Nonempty)
  (hfp : FullyPeriodicOnWith zeta R a b)

omit [Fact p.Prime] in
include hR hRne hfp in
/-- **Proposition 8.9(a).**  `a, b ∈ K` and `dim K = 2`. -/
theorem mem_recCone_of_fullyPeriodic :
    toReal a ∈ recCone R ∧ toReal b ∈ recCone R ∧ SpansPlane (recCone R) := by
  have := mem_interior_recCone hR hRne hfp
  exact ⟨this.1, this.2.1, this.2.2.2⟩

/-- `recCone R` absorbs positive scaling of its interior: a cone's interior is itself invariant
under scaling by a positive real, since scaling by `c ≠ 0` is a homeomorphism carrying the cone
into itself.  Elementary convex-geometry fact, proved locally (no dependence on `HalfPlane.lean`
beyond the already-public `smul_mem_recCone`) since it is needed both for the whole-plane branch
of `first_half_plane_dichotomy_of_sep` below and would otherwise duplicate work `ConeGeom.lean` is
not chartered to provide. -/
private theorem smul_interior_recCone_subset {R : Set (ℤ × ℤ)} {c : ℝ} (hc : 0 < c) :
    ∀ y ∈ interior (recCone R), c • y ∈ interior (recCone R) := by
  have hmapsto : Set.MapsTo (fun y : ℝ × ℝ => c • y) (recCone R) (recCone R) :=
    fun y hy => smul_mem_recCone hc.le hy
  have hopen : IsOpenMap (fun y : ℝ × ℝ => c • y) := isOpenMap_smul₀ hc.ne'
  exact hopen.mapsTo_interior hmapsto

/-- If the line `ℝv` meets the interior of the cone `recCone R`, then `v` or `-v` itself already
lies in the interior: scale the meeting point back to `v`'s ray by `smul_interior_recCone_subset`
if the meeting point is a positive (resp. negative) multiple of `v`, and if it is the zero vector
(so `0 ∈ interior (recCone R)`), rescale a small ball around `0` instead. -/
private theorem toReal_or_neg_mem_interior_recCone_of_lineR_inter {R : Set (ℤ × ℤ)} {v : ℤ × ℤ}
    (hv : v ≠ 0) (hne : (lineR v ∩ interior (recCone R)).Nonempty) :
    toReal v ∈ interior (recCone R) ∨ toReal (-v) ∈ interior (recCone R) := by
  obtain ⟨y, ⟨c, hc⟩, hyK⟩ := hne
  have htv : toReal (-v) = -toReal v := by
    apply Prod.ext <;> simp only [toReal, Prod.fst_neg, Prod.snd_neg] <;> push_cast <;> ring
  rcases lt_trichotomy c 0 with hcneg | hc0 | hcpos
  · right
    have hcpos' : (0:ℝ) < -c := by linarith
    have heq : toReal (-v) = (-c)⁻¹ • y := by
      rw [htv, hc, smul_smul]
      have hinv : (-c)⁻¹ * c = -1 := by
        rw [inv_neg, neg_mul, inv_mul_cancel₀ (ne_of_lt hcneg)]
      rw [hinv, neg_one_smul]
    rw [heq]
    exact smul_interior_recCone_subset (inv_pos.mpr hcpos') y hyK
  · -- `c = 0`, so `y = 0 ∈ interior (recCone R)`; rescale a ball around `0` up to `toReal v`.
    left
    have hy0 : y = 0 := by rw [hc, hc0]; simp
    have hv' : toReal v ≠ 0 := by
      simp only [toReal, Ne, Prod.ext_iff, Prod.fst_zero, Prod.snd_zero]
      intro ⟨h1, h2⟩
      exact hv (Prod.ext (by exact_mod_cast h1) (by exact_mod_cast h2))
    have hynorm : (0:ℝ) < ‖toReal v‖ := norm_pos_iff.mpr hv'
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior (0 : ℝ × ℝ) (hy0 ▸ hyK)
    set p : ℝ × ℝ := (ε / (2 * ‖toReal v‖)) • toReal v with hpdef
    have hppos : (0:ℝ) < ε / (2 * ‖toReal v‖) := by positivity
    have hpball : p ∈ Metric.ball (0 : ℝ × ℝ) ε := by
      rw [Metric.mem_ball, dist_eq_norm, sub_zero, hpdef, norm_smul, Real.norm_eq_abs,
        abs_of_pos hppos]
      have heq : ε / (2 * ‖toReal v‖) * ‖toReal v‖ = ε / 2 := by
        field_simp [ne_of_gt hynorm]
      rw [heq]
      linarith
    have hpK : p ∈ interior (recCone R) := hball hpball
    have hcc : (2 * ‖toReal v‖ / ε) • p = toReal v := by
      rw [hpdef, smul_smul]
      have heq : 2 * ‖toReal v‖ / ε * (ε / (2 * ‖toReal v‖)) = 1 := by
        field_simp [ne_of_gt hε, ne_of_gt hynorm]
      rw [heq, one_smul]
    rw [← hcc]
    exact smul_interior_recCone_subset (by positivity : (0:ℝ) < 2 * ‖toReal v‖ / ε) p hpK
  · left
    have heq : toReal v = c⁻¹ • y := by
      rw [hc, smul_smul, inv_mul_cancel₀ (ne_of_gt hcpos), one_smul]
    rw [heq]
    exact smul_interior_recCone_subset (inv_pos.mpr hcpos) y hyK

/-- If `toReal w` lies in the interior of the recession cone of a non-empty lattice-convex
region `R`, then every point of `ℤ²` is eventually translated into `R` along `w`.  This is the
same argument as the "Part 1" step of `exists_global_extension` (`Nivat.HalfPlane`), generalised
from the specific direction `g = h + h'` to an arbitrary `w`; reproved locally, using only the
public API of `Nivat.HalfPlane` (`recCone`, `convHullOf`, `eq_preimage_convHullOf`,
`smul_mem_recCone`), to avoid touching that file. -/
private theorem exists_eventual_mem_of_mem_interior_recCone {R : Set (ℤ × ℤ)}
    (hR : IsLatticeConvexRegion R) (hne : R.Nonempty) {w : ℤ × ℤ}
    (hw : toReal w ∈ interior (recCone R)) (z : ℤ × ℤ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → z + (N : ℤ) • w ∈ R := by
  obtain ⟨x0, hx0⟩ := hne
  have hx0' : toReal x0 ∈ convHullOf R :=
    subset_closure (subset_convexHull ℝ _ ⟨x0, hx0, rfl⟩)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior (toReal w) hw
  set d : ℝ := ‖toReal z - toReal x0‖ with hddef
  obtain ⟨N₁, hN₁⟩ := exists_nat_gt (d / ε)
  refine ⟨N₁ + 1, fun N hN => ?_⟩
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have : (0 : ℕ) < N := by omega
    exact_mod_cast this
  have hNgt : d / ε < (N : ℝ) := by
    have hlt : (N₁ : ℝ) < (N : ℝ) := by exact_mod_cast (show N₁ < N by omega)
    linarith
  have hdlt : d < ε * (N : ℝ) := by
    have := (div_lt_iff₀ hε).mp hNgt
    linarith [this]
  set vv : ℝ × ℝ := toReal w + (N : ℝ)⁻¹ • (toReal z - toReal x0) with hvdef
  have hvball : vv ∈ Metric.ball (toReal w) ε := by
    rw [Metric.mem_ball, hvdef, dist_eq_norm]
    have heq2 : toReal w + (N : ℝ)⁻¹ • (toReal z - toReal x0) - toReal w
        = (N : ℝ)⁻¹ • (toReal z - toReal x0) := by abel
    rw [heq2, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hNpos), ← hddef]
    rw [inv_mul_lt_iff₀ hNpos]
    linarith [hdlt]
  have hvrec : vv ∈ recCone R := interior_subset (hball hvball)
  have hscaled : (N : ℝ) • vv ∈ recCone R := smul_mem_recCone hNpos.le hvrec
  have hmemC : toReal x0 + (N : ℝ) • vv ∈ convHullOf R := hscaled _ hx0'
  have heq : toReal x0 + (N : ℝ) • vv = toReal (z + (N : ℤ) • w) := by
    have hrhs : toReal (z + (N : ℤ) • w) = toReal z + (N : ℝ) • toReal w := by
      rw [toReal_add, toReal_zsmul]
      norm_cast
    rw [hrhs, hvdef, smul_add, smul_smul, mul_inv_cancel₀ (ne_of_gt hNpos), one_smul]
    abel
  rw [eq_preimage_convHullOf hR]
  show toReal (z + (N : ℤ) • w) ∈ convHullOf R
  rw [← heq]
  exact hmemC

/-- Linearity of `act f` in its configuration argument over a finite sum, pointwise.  A
finite-sum generalisation of `act_add_right`, needed to split `act Qi zeta` along `hsum`'s
`zeta = ∑ i, G i`. -/
private theorem act_sum_right_finset {S : Type*} [CommRing S] {ι : Type*} [DecidableEq ι]
    (f : LaurentTwo S) (s : Finset ι) (g : ι → Config S) (z : ℤ × ℤ) :
    act f (fun w => ∑ j ∈ s, g j w) z = ∑ j ∈ s, act f (g j) z := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    have heq : (fun w => ∑ j ∈ insert a s, g j w) = g a + fun w => ∑ j ∈ s, g j w := by
      funext w
      show ∑ j ∈ insert a s, g j w = g a w + ∑ j ∈ s, g j w
      rw [Finset.sum_insert ha]
    rw [heq, act_add_right]
    show act f (g a) z + act f (fun w => ∑ j ∈ s, g j w) z = ∑ j ∈ insert a s, act f (g j) z
    rw [ih, Finset.sum_insert ha]

include hm hsum hv hk hper hnp hR hRne hfp in
/-- **Steps 1-2 of Proposition 8.9(b)'s proof.**  For a fixed index `i`, construct the
differencing family `H : Fin m' → ℤ × ℤ` (indexed by the other `m' = m - 1` indices via
`i.succAbove`) such that: `H j` is not parallel to `v i` (needed later to invoke
`doublyPeriodic_of_ann`/`exists_period_of_ann_halfPlane` with basis `v i`), and the differenced
configuration `Di := act (prodShift H) (G i)` vanishes on every point `z` all of whose finite
translates `z + ∑_{l ∈ C} H l` (`C` ranging over subsets of `Fin m'`) still lie in `R`, and `Di`
has period `(k i : ℤ) • v i`.  This packages paper Steps 1-2 (`nivat.txt` lines ~1482-1533): the
global extension `zeta'` of `zeta|_R` (via `exists_global_extension`), a common period multiple
`N₀` of `zeta'` (via `DoublyPeriodic.exists_smul_mem`), `H j := N₀ • ((k (i.succAbove j) : ℤ) •
v (i.succAbove j))`, and the differencing identity `Qi (G i) = Qi zeta = Qi zeta'` (since every
other summand `Qi (G j)`, `j ≠ i`, and `Qi zeta'` vanish identically, `Qi := prodShift H`). -/
private theorem exists_component_ann (i : Fin m) :
    ∃ (m' : ℕ), 0 < m' ∧ ∃ H : Fin m' → ℤ × ℤ, (∀ j, pi (v i) (H j) ≠ 0) ∧
      (∀ z : ℤ × ℤ, (∀ C : Finset (Fin m'), z + ∑ l ∈ C, H l ∈ R) →
        act (prodShift H) (G i) z = 0) ∧
      ((k i : ℤ) • v i) ∈ Per (act (prodShift H) (G i)) := by
  classical
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hm'pos : 0 < m' := by omega
  obtain ⟨-, zeta', hzeta'a, hzeta'b, hzeta'dp, hzeta'eq⟩ :=
    exists_global_extension (Or.inl hR) hRne hfp
  obtain ⟨N₀, hN₀ne, hN₀per⟩ := hzeta'dp.exists_smul_mem
  set H : Fin m' → ℤ × ℤ :=
    fun j => N₀ • ((k (i.succAbove j) : ℤ) • v (i.succAbove j)) with hHdef
  have hHperG : ∀ j : Fin m', H j ∈ Per (G (i.succAbove j)) :=
    fun j => AddSubgroup.zsmul_mem _ (hper (i.succAbove j)) N₀
  have hHperzeta' : ∀ j : Fin m', H j ∈ Per zeta' :=
    fun j => hN₀per ((k (i.succAbove j) : ℤ) • v (i.succAbove j))
  have hQother : ∀ j : Fin m', act (prodShift H) (G (i.succAbove j)) = 0 := by
    intro j
    have hfac : (mono (H j) - 1 : LaurentTwo (ZMod p)) *
          ∏ l ∈ Finset.univ.erase j, (mono (H l) - 1) = prodShift H :=
      Finset.mul_prod_erase Finset.univ (fun l => mono (H l) - 1) (Finset.mem_univ j)
    rw [← hfac, act_mul]
    exact (act_mono_sub_one_eq_zero_iff (H j) _).mpr (act_mem_Per (hHperG j))
  have hQzeta' : act (prodShift H) zeta' = 0 := by
    set j0 : Fin m' := ⟨0, hm'pos⟩ with hj0
    have hfac : (mono (H j0) - 1 : LaurentTwo (ZMod p)) *
          ∏ l ∈ Finset.univ.erase j0, (mono (H l) - 1) = prodShift H :=
      Finset.mul_prod_erase Finset.univ (fun l => mono (H l) - 1) (Finset.mem_univ j0)
    rw [← hfac, act_mul]
    exact (act_mono_sub_one_eq_zero_iff (H j0) _).mpr (act_mem_Per (hHperzeta' j0))
  refine ⟨m', hm'pos, H, ?_, ?_, ?_⟩
  · intro j
    have hne : i ≠ i.succAbove j := Fin.ne_succAbove i j
    have hd : det (v i) (v (i.succAbove j)) ≠ 0 := hnp hne
    have hkne : (k (i.succAbove j) : ℤ) ≠ 0 := by exact_mod_cast (hk (i.succAbove j)).ne'
    show pi (v i) (N₀ • ((k (i.succAbove j) : ℤ) • v (i.succAbove j))) ≠ 0
    rw [pi_smul, pi_smul]
    exact mul_ne_zero hN₀ne (mul_ne_zero hkne hd)
  · intro z hz
    have heq1 : zeta = G i + fun w => ∑ j : Fin m', G (i.succAbove j) w := by
      funext w
      show zeta w = G i w + ∑ j : Fin m', G (i.succAbove j) w
      rw [hsum w]
      exact Fin.sum_univ_succAbove (fun l => G l w) i
    have hkey : act (prodShift H) zeta z = act (prodShift H) (G i) z := by
      rw [heq1, act_add_right]
      show act (prodShift H) (G i) z + act (prodShift H) (fun w => ∑ j : Fin m', G (i.succAbove j) w) z
          = act (prodShift H) (G i) z
      rw [act_sum_right_finset (prodShift H) Finset.univ (fun j => G (i.succAbove j)) z]
      have hzero : ∑ j : Fin m', act (prodShift H) (G (i.succAbove j)) z = 0 :=
        Finset.sum_eq_zero (fun j _ => congrFun (hQother j) z)
      rw [hzero, add_zero]
    have hexpand : act (prodShift H) zeta z
        = ∑ C ∈ (Finset.univ : Finset (Fin m')).powerset,
            (-1 : ZMod p) ^ (m' - C.card) * zeta (z + ∑ l ∈ C, H l) := by
      show act (∏ i, (mono (H i) - 1)) zeta z = _
      have h := act_prod_mono_sub_one (Finset.univ : Finset (Fin m')) H zeta z
      simpa only [Finset.card_univ, Fintype.card_fin] using h
    have hexpand' : act (prodShift H) zeta' z
        = ∑ C ∈ (Finset.univ : Finset (Fin m')).powerset,
            (-1 : ZMod p) ^ (m' - C.card) * zeta' (z + ∑ l ∈ C, H l) := by
      show act (∏ i, (mono (H i) - 1)) zeta' z = _
      have h := act_prod_mono_sub_one (Finset.univ : Finset (Fin m')) H zeta' z
      simpa only [Finset.card_univ, Fintype.card_fin] using h
    have hcongr : (∑ C ∈ (Finset.univ : Finset (Fin m')).powerset,
          (-1 : ZMod p) ^ (m' - C.card) * zeta (z + ∑ l ∈ C, H l))
        = ∑ C ∈ (Finset.univ : Finset (Fin m')).powerset,
          (-1 : ZMod p) ^ (m' - C.card) * zeta' (z + ∑ l ∈ C, H l) := by
      refine Finset.sum_congr rfl fun C _ => ?_
      rw [hzeta'eq _ (hz C)]
    have hzeta'z0 : act (prodShift H) zeta' z = 0 := congrFun hQzeta' z
    rw [← hkey, hexpand, hcongr, ← hexpand']
    exact hzeta'z0
  · exact act_mem_Per (hper i)

/-- `det` is invariant under negating both arguments. -/
private theorem det_neg_neg (v u : ℤ × ℤ) : det (-v) (-u) = det v u := by
  simp only [det, Prod.fst_neg, Prod.snd_neg]; ring

include hm hsum hv hk hper hnp hR hRne hfp in
/-- **Proposition 8.9(b), parametrised over the separation lemma.** Takes
`Nivat.exists_side_of_line_not_mem_interior_of_nonempty_interior`'s statement as an explicit
hypothesis `hsep` (its exact frozen signature, copied verbatim so that `first_half_plane_dichotomy`
becomes a one-line call by supplying the real lemma from `Nivat.Section8.ConeGeom`). Case (α) (the
line meets the interior) is proved in full below via `exists_component_ann` +
`doublyPeriodic_of_ann`. Case (β) (the line misses the interior) is proved in full below via
`exists_component_ann`, the recession-cone growth fact
`exists_forall_ge_piE_exists_zsmul_add_mem` (`Nivat.Section8.ConeGeom`, agent lineA) and the
basis-flip reduction to `exists_period_of_ann_halfPlane`. -/
private theorem first_half_plane_dichotomy_of_sep
    (hsep : ∀ {K : Set (ℝ × ℝ)}, Convex ℝ K → (∀ c : ℝ, 0 ≤ c → ∀ y ∈ K, c • y ∈ K) →
      ∀ {v : ℤ × ℤ}, v ≠ 0 → (interior K).Nonempty → ¬ (lineR v ∩ interior K).Nonempty →
        ∃ ε : Bool, ∀ y ∈ K, 0 ≤ piER ε v y)
    (i : Fin m) :
    ((lineR (v i) ∩ interior (recCone R)).Nonempty ∧ DoublyPeriodic (G i)) ∨
      (¬ (lineR (v i) ∩ interior (recCone R)).Nonempty ∧ ∃ (ε : Bool) (t : ℤ),
        (∀ y ∈ recCone R, 0 ≤ piER ε (v i) y) ∧
          FullyPeriodicOn (G i) (latHalfPlane ε (v i) t)) := by
  classical
  obtain ⟨m', hm'pos, H, hHnp, hHvanish, hHper⟩ :=
    exists_component_ann hm hsum hv hk hper hnp hR hRne hfp i
  have hviZero : v i ≠ 0 := (hv i).ne_zero
  by_cases hcase : (lineR (v i) ∩ interior (recCone R)).Nonempty
  · -- Case (α): the line meets the interior, so `v i` (or `-v i`) already lies in it, and
    -- every point of the plane eventually re-enters `Ri` along that direction; `Di` vanishes
    -- everywhere, so `G i` is doubly periodic.
    left
    refine ⟨hcase, ?_⟩
    have hDi0general : ∀ z : ℤ × ℤ, act (prodShift H) (G i) z = 0 := by
      intro z
      rcases toReal_or_neg_mem_interior_recCone_of_lineR_inter hviZero hcase with hw | hw
      · have hbound : ∀ C : Finset (Fin m'), ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
            z + ∑ l ∈ C, H l + (N : ℤ) • (v i) ∈ R :=
          fun C => exists_eventual_mem_of_mem_interior_recCone hR hRne hw (z + ∑ l ∈ C, H l)
        set Nb : ℕ := Finset.univ.sup (fun C : Finset (Fin m') => (hbound C).choose) with hNbdef
        set N : ℕ := Nb * k i with hNdef
        have hNC : ∀ C : Finset (Fin m'), z + (N : ℤ) • (v i) + ∑ l ∈ C, H l ∈ R := by
          intro C
          have hle : (hbound C).choose ≤ N := by
            calc (hbound C).choose
                ≤ Nb := by
                  rw [hNbdef]
                  exact Finset.le_sup (f := fun C : Finset (Fin m') => (hbound C).choose)
                    (Finset.mem_univ C)
              _ ≤ N := by rw [hNdef]; exact Nat.le_mul_of_pos_right Nb (hk i)
          have hmem := (hbound C).choose_spec N hle
          have heq : z + ∑ l ∈ C, H l + (N : ℤ) • (v i)
              = z + (N : ℤ) • (v i) + ∑ l ∈ C, H l := by abel
          rwa [heq] at hmem
        have hzN : act (prodShift H) (G i) (z + (N : ℤ) • (v i)) = 0 := hHvanish _ hNC
        have hcast : (N : ℤ) = (Nb : ℤ) * (k i : ℤ) := by rw [hNdef]; push_cast; ring
        have hteq : (N : ℤ) • (v i) = (Nb : ℤ) • ((k i : ℤ) • v i) := by rw [hcast, mul_smul]
        have hper' : (Nb : ℤ) • ((k i : ℤ) • v i) ∈ Per (act (prodShift H) (G i)) :=
          AddSubgroup.zsmul_mem _ hHper (Nb : ℤ)
        have hshift := Per.apply hper' z
        rw [← hteq] at hshift
        rw [hzN] at hshift
        exact hshift.symm
      · have hbound : ∀ C : Finset (Fin m'), ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
            z + ∑ l ∈ C, H l + (N : ℤ) • (-(v i)) ∈ R :=
          fun C => exists_eventual_mem_of_mem_interior_recCone hR hRne hw (z + ∑ l ∈ C, H l)
        set Nb : ℕ := Finset.univ.sup (fun C : Finset (Fin m') => (hbound C).choose) with hNbdef
        set N : ℕ := Nb * k i with hNdef
        have hNC : ∀ C : Finset (Fin m'), z + (N : ℤ) • (-(v i)) + ∑ l ∈ C, H l ∈ R := by
          intro C
          have hle : (hbound C).choose ≤ N := by
            calc (hbound C).choose
                ≤ Nb := by
                  rw [hNbdef]
                  exact Finset.le_sup (f := fun C : Finset (Fin m') => (hbound C).choose)
                    (Finset.mem_univ C)
              _ ≤ N := by rw [hNdef]; exact Nat.le_mul_of_pos_right Nb (hk i)
          have hmem := (hbound C).choose_spec N hle
          have heq : z + ∑ l ∈ C, H l + (N : ℤ) • (-(v i))
              = z + (N : ℤ) • (-(v i)) + ∑ l ∈ C, H l := by abel
          rwa [heq] at hmem
        have hzN : act (prodShift H) (G i) (z + (N : ℤ) • (-(v i))) = 0 := hHvanish _ hNC
        have hcast : (N : ℤ) = (Nb : ℤ) * (k i : ℤ) := by rw [hNdef]; push_cast; ring
        have hteq : (N : ℤ) • (-(v i)) = (-(Nb : ℤ)) • ((k i : ℤ) • v i) := by
          rw [hcast, smul_neg, ← neg_smul,
            show -((Nb : ℤ) * (k i : ℤ)) = (-(Nb : ℤ)) * (k i : ℤ) by ring, mul_smul]
        have hper' : (-(Nb : ℤ)) • ((k i : ℤ) • v i) ∈ Per (act (prodShift H) (G i)) :=
          AddSubgroup.zsmul_mem _ hHper (-(Nb : ℤ))
        have hshift := Per.apply hper' z
        rw [← hteq] at hshift
        rw [hzN] at hshift
        exact hshift.symm
    have hDi0 : act (prodShift H) (G i) = 0 := funext hDi0general
    obtain ⟨u, hvu⟩ := (hv i).exists_dual
    exact doublyPeriodic_of_ann hvu (hk i) (hper i) hm'pos hHnp hDi0
  · -- Case (β): the line misses the interior.  `hsep` separates `recCone R` from it, giving a
    -- sign `ε` with `recCone R ⊆ {piER ε (v i) ≥ 0}`.
    right
    refine ⟨hcase, ?_⟩
    have hint : (interior (recCone R)).Nonempty :=
      ⟨toReal (a + b), (mem_interior_recCone hR hRne hfp).2.2.1⟩
    have hconv : Convex ℝ (recCone R) := convex_recCone R
    have hcone : ∀ c : ℝ, 0 ≤ c → ∀ y ∈ recCone R, c • y ∈ recCone R :=
      fun c hc y hy => smul_mem_recCone hc hy
    obtain ⟨ε, hε⟩ := hsep hconv hcone hviZero hint hcase
    obtain ⟨t, ht⟩ := exists_forall_ge_piE_exists_zsmul_add_mem hR hRne hint hviZero hε
        (k := (k i : ℤ)) (by exact_mod_cast hk i) (fun C : Finset (Fin m') => ∑ l ∈ C, H l)
    have hvan : ∀ z : ℤ × ℤ, t ≤ piE ε (v i) z → act (prodShift H) (G i) z = 0 := by
      intro z hz
      obtain ⟨N, hN⟩ := ht z hz
      have hzN : act (prodShift H) (G i) (z + N • ((k i : ℤ) • v i)) = 0 := hHvanish _ hN
      have hshift := Per.apply (AddSubgroup.zsmul_mem _ hHper N) z
      rw [hzN] at hshift
      exact hshift.symm
    obtain ⟨u, hvu⟩ := (hv i).exists_dual
    cases ε with
    | false =>
      have hv'u' : det (-(v i)) (-u) = 1 := (det_neg_neg (v i) u).trans hvu
      have hper' : ((k i : ℤ) • (-(v i))) ∈ Per (G i) := by
        rw [smul_neg]; exact (Per (G i)).neg_mem (hper i)
      have hHnp' : ∀ j, pi (-(v i)) (H j) ≠ 0 := fun j => by
        rw [pi_neg_left]; exact neg_ne_zero.mpr (hHnp j)
      have hvan' : ∀ z : ℤ × ℤ, t ≤ pi (-(v i)) z → act (prodShift H) (G i) z = 0 := by
        intro z hz; rw [pi_neg_left] at hz; exact hvan z hz
      obtain ⟨q, hqpos, hqper, hfull⟩ :=
        exists_period_of_ann_halfPlane hv'u' (hk i) hper' hm'pos hHnp' hvan'
      have hset_eq : latHalfPlane true (-(v i)) (t + tauMinus (-(v i)) H)
          = latHalfPlane false (v i) (t + tauMinus (-(v i)) H) := by
        ext z
        show (t + tauMinus (-(v i)) H ≤ pi (-(v i)) z) ↔
          (t + tauMinus (-(v i)) H ≤ piE false (v i) z)
        rw [pi_neg_left]; rfl
      exact ⟨false, t + tauMinus (-(v i)) H, hε, hset_eq ▸ hfull⟩
    | true =>
      have hper' : ((k i : ℤ) • (v i)) ∈ Per (G i) := hper i
      have hvan' : ∀ z : ℤ × ℤ, t ≤ pi (v i) z → act (prodShift H) (G i) z = 0 := hvan
      obtain ⟨q, hqpos, hqper, hfull⟩ :=
        exists_period_of_ann_halfPlane hvu (hk i) hper' hm'pos hHnp hvan'
      exact ⟨true, t + tauMinus (v i) H, hε, hfull⟩

include hm hsum hv hk hper hnp hR hRne hfp in
/-- **Proposition 8.9(b).**  For each `i` exactly one of the following holds.

(α) The line `ℝv_i` meets `int K`, and then `G_i` is doubly periodic.

(β) Otherwise there are `ε_i ∈ {+, −}` and `t_i ∈ ℤ` with `K ⊆ {ε_i π_i ≥ 0}` and `G_i` fully
periodic on the half-plane `U_i = {ε_i π_i ≥ t_i}`.

Neither the non-periodicity of `ζ` nor the minimality of the decomposition is required
(Remark 8.11(2)). -/
-- (lineM): both cases of `first_half_plane_dichotomy_of_sep` are fully proved above (zero
-- sorry, zero warning), including case (β)'s recession-cone growth step via
-- `exists_forall_ge_piE_exists_zsmul_add_mem` (`ConeGeom.lean`, lineA); this is a one-line call.
theorem first_half_plane_dichotomy (i : Fin m) :
    ((lineR (v i) ∩ interior (recCone R)).Nonempty ∧ DoublyPeriodic (G i)) ∨
      (¬ (lineR (v i) ∩ interior (recCone R)).Nonempty ∧ ∃ (ε : Bool) (t : ℤ),
        (∀ y ∈ recCone R, 0 ≤ piER ε (v i) y) ∧
          FullyPeriodicOn (G i) (latHalfPlane ε (v i) t)) :=
  first_half_plane_dichotomy_of_sep hm hsum hv hk hper hnp hR hRne hfp
    (@exists_side_of_line_not_mem_interior_of_nonempty_interior) i

/-- `recCone R` is a closed subset of `ℝ²`: it is the intersection, over `x ∈ convHullOf R`, of
the preimages of the closed set `convHullOf R` under the continuous translation `w ↦ x + w`.
Needed for `cone_trichotomy`'s `hclosed` hypothesis; not otherwise available in `HalfPlane.lean`
(which only proves `convex_recCone`), and not `ConeGeom.lean`'s job to supply since it is specific
to the `recCone` definition. -/
private theorem isClosed_recCone (R : Set (ℤ × ℤ)) : IsClosed (recCone R) := by
  have hCclosed : IsClosed (convHullOf R) := isClosed_closure
  have heq : recCone R = ⋂ x ∈ convHullOf R, (fun w : ℝ × ℝ => x + w) ⁻¹' convHullOf R := by
    ext w
    simp only [recCone, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage]
  rw [heq]
  exact isClosed_biInter fun x _ =>
    hCclosed.preimage (continuous_const.add continuous_id)

/-- If two integer vectors are both orthogonal (as reals) to a nonzero real vector `n`, they are
parallel: `det x y = 0`.  Used to show at most one direction `v i` can lie on the boundary line of
a half-plane. -/
private theorem det_eq_zero_of_orthogonal {n : ℝ × ℝ} (hn : n ≠ 0) {x y : ℤ × ℤ}
    (hx : n.1 * (x.1 : ℝ) + n.2 * (x.2 : ℝ) = 0) (hy : n.1 * (y.1 : ℝ) + n.2 * (y.2 : ℝ) = 0) :
    det x y = 0 := by
  have hn' : n.1 ≠ 0 ∨ n.2 ≠ 0 := by
    by_contra h
    rw [not_or, not_not, not_not] at h
    exact hn (Prod.ext h.1 h.2)
  have key1 : n.1 * ((x.1 : ℝ) * y.2 - x.2 * y.1) = 0 := by linear_combination y.2 * hx - x.2 * hy
  have key2 : n.2 * ((x.1 : ℝ) * y.2 - x.2 * y.1) = 0 := by linear_combination x.1 * hy - y.1 * hx
  have hzero : (x.1 : ℝ) * y.2 - x.2 * y.1 = 0 := by
    rcases hn' with h1 | h2
    · exact (mul_eq_zero.mp key1).resolve_left h1
    · exact (mul_eq_zero.mp key2).resolve_left h2
  have : ((det x y : ℤ) : ℝ) = 0 := by simp only [det]; push_cast; linarith [hzero]
  exact_mod_cast this

omit [Fact p.Prime] in
include hm hnp in
/-- Among `m ≥ 2` pairwise non-parallel directions, at most one can be orthogonal to a fixed
nonzero `n`; since `m ≥ 2` there is always one that is not. -/
private theorem exists_nonorthogonal_of_pairwise_nonparallel {n : ℝ × ℝ} (hn : n ≠ 0) :
    ∃ i : Fin m, n.1 * ((v i).1 : ℝ) + n.2 * ((v i).2 : ℝ) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hi0 : (0 : ℕ) < m := by omega
  have hi1 : (1 : ℕ) < m := by omega
  have hd : det (v ⟨0, hi0⟩) (v ⟨1, hi1⟩) = 0 :=
    det_eq_zero_of_orthogonal hn (hcon ⟨0, hi0⟩) (hcon ⟨1, hi1⟩)
  have hne : (⟨0, hi0⟩ : Fin m) ≠ ⟨1, hi1⟩ := by simp
  exact (hnp hne) hd

include hm hsum hv hk hper hnp hR hRne hfp in
set_option linter.unusedVariables false in
/-- Conditional version of Proposition 8.9(c): given `cone_trichotomy` (agent lineA,
`Nivat.Section8.ConeGeom`) and the same `hsep` used by `first_half_plane_dichotomy_of_sep`, the
classification of `recCone R` follows.  Every `i` falls in case (β) of `first_half_plane_dichotomy`
(since `hnd i` rules out case (α)'s `DoublyPeriodic (G i)`), which gives the second conjunct
directly; `cone_trichotomy` classifies `recCone R` into whole-plane / half-plane / sector, and the
first two are excluded because `hm`/`hnp` supply two non-parallel directions, at least one of which
is not on the boundary of a would-be half-plane (or trivially meets the interior of the whole
plane), contradicting the second conjunct via `ConeGeom.lean`'s
`line_inter_interior_of_univ`/`line_inter_interior_of_halfPlane`. -/
private theorem isSector_recCone_of_trichotomy
    (hsep : ∀ {K : Set (ℝ × ℝ)}, Convex ℝ K → (∀ c : ℝ, 0 ≤ c → ∀ y ∈ K, c • y ∈ K) →
      ∀ {v : ℤ × ℤ}, v ≠ 0 → (interior K).Nonempty → ¬ (lineR v ∩ interior K).Nonempty →
        ∃ ε : Bool, ∀ y ∈ K, 0 ≤ piER ε v y)
    (htri : ∀ {K : Set (ℝ × ℝ)}, Convex ℝ K → IsClosed K →
      (∀ c : ℝ, 0 ≤ c → ∀ y ∈ K, c • y ∈ K) → SpansPlane K →
        K = Set.univ
        ∨ (∃ n : ℝ × ℝ, n ≠ 0 ∧ K = {y | 0 ≤ n.1 * y.1 + n.2 * y.2})
        ∨ (∃ w₁ w₂ : ℝ × ℝ, w₁.1 * w₂.2 - w₁.2 * w₂.1 ≠ 0 ∧
            K = {y | ∃ s t : ℝ, 0 ≤ s ∧ 0 ≤ t ∧ y = s • w₁ + t • w₂}))
    (hunivline : ∀ {v : ℤ × ℤ}, v ≠ 0 → (lineR v ∩ interior (Set.univ : Set (ℝ × ℝ))).Nonempty)
    (hhalfline : ∀ {n : ℝ × ℝ}, n ≠ 0 → ∀ {v : ℤ × ℤ}, v ≠ 0 →
      n.1 * (v.1 : ℝ) + n.2 * (v.2 : ℝ) ≠ 0 →
      (lineR v ∩ interior {y : ℝ × ℝ | 0 ≤ n.1 * y.1 + n.2 * y.2}).Nonempty)
    (hnper : ¬ IsPeriodic zeta) (hnd : ∀ i, ¬ DoublyPeriodic (G i)) :
    IsSector (recCone R) ∧ ∀ i, ¬ (lineR (v i) ∩ interior (recCone R)).Nonempty := by
  classical
  have hnotcase : ∀ i, ¬ (lineR (v i) ∩ interior (recCone R)).Nonempty := by
    intro i
    rcases first_half_plane_dichotomy_of_sep hm hsum hv hk hper hnp hR hRne hfp hsep i with
      ⟨_, hD⟩ | ⟨hnA, _⟩
    · exact absurd hD (hnd i)
    · exact hnA
  refine ⟨?_, hnotcase⟩
  have hconv : Convex ℝ (recCone R) := convex_recCone R
  have hclosed : IsClosed (recCone R) := isClosed_recCone R
  have hcone : ∀ c : ℝ, 0 ≤ c → ∀ y ∈ recCone R, c • y ∈ recCone R :=
    fun c hc y hy => smul_mem_recCone hc hy
  have hspan : SpansPlane (recCone R) := (mem_recCone_of_fullyPeriodic hR hRne hfp).2.2
  rcases htri hconv hclosed hcone hspan with huniv | ⟨n, hn, hKn⟩ | hsector
  · exact absurd (by rw [huniv]; exact hunivline (hv ⟨0, by omega⟩).ne_zero)
      (hnotcase ⟨0, by omega⟩)
  · obtain ⟨i, hi⟩ := exists_nonorthogonal_of_pairwise_nonparallel hm hnp hn
    exact absurd (by rw [hKn]; exact hhalfline hn (hv i).ne_zero hi)
      (hnotcase i)
  · exact hsector

include hm hsum hv hk hper hnp hR hRne hfp in
/-- **Proposition 8.9(c).**  If `ζ` is non-periodic and no component is doubly periodic, then
`K` is a closed sector of opening strictly between `0` and `π`, and its interior contains no
`±v_j`.  In particular `K` cannot be a half-plane. -/
-- (lineM): fully proved via `isSector_recCone_of_trichotomy` above (zero sorry, zero warning),
-- now that case (β) of `first_half_plane_dichotomy_of_sep` is complete.
theorem isSector_recCone (hnper : ¬ IsPeriodic zeta) (hnd : ∀ i, ¬ DoublyPeriodic (G i)) :
    IsSector (recCone R) ∧ ∀ i, ¬ (lineR (v i) ∩ interior (recCone R)).Nonempty :=
  isSector_recCone_of_trichotomy hm hsum hv hk hper hnp hR hRne hfp
    (@exists_side_of_line_not_mem_interior_of_nonempty_interior)
    (fun hconv hclosed hcone hspan => cone_trichotomy hconv hclosed hcone hspan)
    line_inter_interior_of_univ line_inter_interior_of_halfPlane hnper hnd

end Prop89

/-! ### Corollary 8.10 -/

/-- The output of **Corollary 8.10 = Theorem 8.1(i)**: a non-periodic `𝔽_p`-valued `ζ` written
as a sum of `n ≥ 2` components with pairwise non-parallel non-zero periods `hᵢ = kᵢvᵢ`, none
doubly periodic, each fully periodic on a half-plane `Uᵢ = {εᵢπᵢ ≥ tᵢ}` whose boundary is
parallel to `hᵢ`; together with the recession cone `K` of the region of Theorem 8.7, a closed
sector of opening `< π` contained in every `{εᵢπᵢ ≥ 0}` and meeting no line `ℝvᵢ` in its
interior. -/
structure FirstHalfPlane (p : ℕ) (n : ℕ) where
  /-- The non-periodic configuration being decomposed. -/
  zeta : Config (ZMod p)
  /-- The components. -/
  G : Fin n → Config (ZMod p)
  /-- The primitive period directions. -/
  v : Fin n → ℤ × ℤ
  /-- The period multiples, `hᵢ = kᵢvᵢ`. -/
  k : Fin n → ℕ
  /-- The side on which the first half-plane lies. -/
  eps : Fin n → Bool
  /-- The threshold of the first half-plane. -/
  t : Fin n → ℤ
  /-- The recession cone `K_R` of the region of Theorem 8.7. -/
  K : Set (ℝ × ℝ)
  two_le : 2 ≤ n
  primitive : ∀ i, Primitive (v i)
  k_pos : ∀ i, 0 < k i
  nonparallel : Pairwise fun i j => det (v i) (v j) ≠ 0
  sum_eq : ∀ z, zeta z = ∑ i, G i z
  period : ∀ i, ((k i : ℤ) • v i) ∈ Per (G i)
  not_doublyPeriodic : ∀ i, ¬ DoublyPeriodic (G i)
  zeta_not_periodic : ¬ IsPeriodic zeta
  fullyPeriodic_U : ∀ i, FullyPeriodicOn (G i) (latHalfPlane (eps i) (v i) (t i))
  K_sector : IsSector K
  K_side : ∀ i, ∀ y ∈ K, 0 ≤ piER (eps i) (v i) y
  K_interior : ∀ i, ¬ (lineR (v i) ∩ interior K).Nonempty

namespace FirstHalfPlane

variable {p n : ℕ} (D : FirstHalfPlane p n)

/-- The period `hᵢ = kᵢvᵢ` of the `i`-th component. -/
def h (i : Fin n) : ℤ × ℤ := (D.k i : ℤ) • D.v i

/-- The first half-plane `Uᵢ = {εᵢπᵢ ≥ tᵢ}`, whose boundary is parallel to `hᵢ`. -/
def U (i : Fin n) : Set (ℤ × ℤ) := latHalfPlane (D.eps i) (D.v i) (D.t i)

theorem h_ne_zero (i : Fin n) : D.h i ≠ 0 := by
  have hv : D.v i ≠ 0 := (D.primitive i).ne_zero
  have hk : (D.k i : ℤ) ≠ 0 := by exact_mod_cast (D.k_pos i).ne'
  exact smul_ne_zero hk hv

theorem h_mem_Per (i : Fin n) : D.h i ∈ Per (D.G i) := D.period i

theorem fullyPeriodicOn_U (i : Fin n) : FullyPeriodicOn (D.G i) (D.U i) := D.fullyPeriodic_U i

end FirstHalfPlane

/-- **Corollary 8.10 (Theorem 8.1(i)).**  Let `ξ` be a counterexample of minimal order and let
`p > max A` be prime.  Take `ξ'` and `R` as in Theorem 8.7 and `ξ' mod p = ∑ᵢ Ḡᵢ` as in
Lemma 8.5.  Since `exists_modP_decomp` already discards all doubly periodic components, every
`i : Fin n'` falls in case (β) of `first_half_plane_dichotomy` directly, giving the half-plane
`Uᵢ`; unlike the paper's phrasing, no separate absorption step for a doubly periodic remainder
`B` is needed. -/
theorem exists_firstHalfPlane {ξ : Config ℤ} (hξ : IsMinimalCounterexample ξ) {p : ℕ}
    [Fact p.Prime] (hlt : ∀ z, ξ z < p) :
    ∃ (n : ℕ) (D : FirstHalfPlane p n) (ζ : Config ℤ),
      ζ ∈ orbitClosure ξ ∧ ¬ IsPeriodic ζ ∧ D.zeta = modP p ζ := by
  classical
  -- Theorems 8.6/8.7: a non-periodic `ξ'` in the orbit closure, fully periodic on a
  -- lattice-convex region `R`.  The primed version is the one proved in
  -- `Nivat.Section8.ExternalDischarged`, where Theorem 8.6's external input is discharged by
  -- `Nivat.Colle.theorem114` rather than assumed.  Statement-identical to the unprimed version
  -- in `External.lean`; the difference is one fewer axiom in this theorem's closure.
  obtain ⟨ξ', hζorbit, hξ'np, R, hR, hRne, hfpOn⟩ := exists_fullyPeriodic_region' hξ
  obtain ⟨a, b, hfp⟩ := hfpOn
  -- `ξ'` is again a counterexample of the same (minimal) order (Remark 8.3), so it has its own
  -- alphabet bound `[[p]]`, transported from `ξ`'s via membership in the orbit closure.
  obtain ⟨hξ'min, -⟩ := IsMinimalCounterexample.of_mem_orbitClosure hξ hζorbit hξ'np
  obtain ⟨-, hξ'pos, -, -⟩ := hξ'min.1
  have hξ'lt : ∀ z, ξ' z < p := by
    intro z
    obtain ⟨u, hu⟩ := hζorbit {z}
    rw [hu z (Finset.mem_singleton_self z)]
    exact hlt _
  -- Theorem 8.4: a non-zero annihilator of `ξ` with pairwise non-parallel directions.
  obtain ⟨hA, hpos, -, S, hSne, hSconv, hSP⟩ := hξ.1
  obtain ⟨n, h, -, hne, hnp, hann, -⟩ :=
    exists_prodShift_ann hA (hasNonzeroAnn_of_low_complexity hA hSne hSP)
  -- Lemma 8.5: the `𝔽_p`-decomposition of `ξ'` into `n' ≥ 2` components, none doubly periodic.
  obtain ⟨n', h', G, hn'2, hh'ne, hh'np, hh'per, hh'ndp, hh'sum⟩ :=
    exists_modP_decomp hA hpos hne hnp hann hζorbit hξ'np hlt
  -- Extract a primitive direction `v i` and multiplicity `k i` from each period `h' i`.
  choose v k hvprim hkpos hheq using fun i => exists_primitive_nsmul_eq (hh'ne i)
  have hper' : ∀ i, ((k i : ℤ) • v i) ∈ Per (G i) := fun i => hheq i ▸ hh'per i
  have hnp' : Pairwise fun i j => det (v i) (v j) ≠ 0 := by
    intro i j hij
    have hd : det (h' i) (h' j) ≠ 0 := hh'np hij
    rw [hheq i, hheq j, det_zsmul_zsmul] at hd
    exact right_ne_zero_of_mul hd
  -- `ξ'` is again non-periodic after reduction mod `p` (Lemma 8.5(b)).
  have hzetanp : ¬ IsPeriodic (modP p ξ') :=
    (isPeriodic_modP_iff hξ'pos hξ'lt).not.mpr hξ'np
  -- Full periodicity on `R` transfers unchanged from `ξ'` to `modP p ξ'`: the vectors `a, b`
  -- and the region-preservation clauses don't mention the config, and the value equalities
  -- transfer along the ring homomorphism `ℤ → ZMod p`.
  have hfp' : FullyPeriodicOnWith (modP p ξ') R a b :=
    ⟨hfp.1, hfp.2.1, hfp.2.2.1, fun z hz => congrArg (fun x : ℤ => (x : ZMod p)) (hfp.2.2.2.1 z hz),
      fun z hz => congrArg (fun x : ℤ => (x : ZMod p)) (hfp.2.2.2.2 z hz)⟩
  -- Proposition 8.9(b): every component falls in case (β), since case (α) would force
  -- `DoublyPeriodic (G i)`, contradicting `hh'ndp`.
  have hcase : ∀ i, ∃ (ε : Bool) (t : ℤ), (∀ y ∈ recCone R, 0 ≤ piER ε (v i) y) ∧
      FullyPeriodicOn (G i) (latHalfPlane ε (v i) t) := by
    intro i
    rcases first_half_plane_dichotomy hn'2 hh'sum hvprim hkpos hper' hnp' hR hRne hfp' i with
      ⟨-, hDip⟩ | ⟨-, hex⟩
    · exact absurd hDip (hh'ndp i)
    · exact hex
  choose eps t hKside hFPU using hcase
  -- Proposition 8.9(c): `recCone R` is a sector, meeting no `ℝ v i` in its interior.
  obtain ⟨hKsector, hKinterior⟩ :=
    isSector_recCone hn'2 hh'sum hvprim hkpos hper' hnp' hR hRne hfp' hzetanp hh'ndp
  refine ⟨n', ⟨modP p ξ', G, v, k, eps, t, recCone R, hn'2, hvprim, hkpos, hnp', hh'sum, hper',
    hh'ndp, hzetanp, hFPU, hKsector, hKside, hKinterior⟩, ξ', hζorbit, hξ'np, rfl⟩

/-!
**Remark 8.11.**  (1) Proposition 8.9 is the one-sided version of Lemma 4.1 of §4 — the support
of `f_i = Q_i ψ` lies in a strip, `Nivat.StarConfig.ffield_support_strip` — and Lemma 8.8 is the
general form of step (6) of Lemma D.7, `Nivat.periodic_of_two_sided_determinacy`.
(2) In Proposition 8.9(b) neither the non-periodicity of `ζ` nor the minimality of the
decomposition is required.  The corollary absorbs all doubly periodic components, including any
that fall into case (α).
-/

end Nivat
