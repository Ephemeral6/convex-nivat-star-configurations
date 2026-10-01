/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.Background

/-!
# §4. At least one two-point difference is non-zero

Formalisation of §4 of *The Convex Nivat Conjecture* (Pan).

Writing `Qᵢ = ∏_{j ≠ i} (T^{H j} - 1)` and `fᵢ = Qᵢ ψ`, the hypothesis (1.1) gives
`(T^{Hᵢ} - 1) fᵢ = D ψ = 0`, so `fᵢ` has period `Hᵢ`.  Passing to the one-sided limit `σᵢ^+`
identifies `fᵢ` with `Qᵢ δᵢ` for the scalar difference field `δᵢ`, which vanishes off a strip;
a leading-term argument on the unique minimal `πᵢ(H_C)` shows `fᵢ ≠ 0` (Lemma 4.1).
Multiplying two such witnesses in non-parallel directions produces a finitely supported
non-zero function killed by `D`, so some two-point difference `J(d, ·) = D_z(ψ(z) ψ(z + d))`
is non-zero (Lemma 4.2).

## Main definitions

* `Nivat.StarConfig.ffield` — `fᵢ = Qᵢ ψ`.
* `Nivat.StarConfig.Jfun` — the two-point difference `J(d, ·) = D_z(ψ(z) ψ(z + d))`.

## Main results

* `Nivat.StarConfig.ffield_ne_zero`, `Nivat.StarConfig.ffield_support_strip` — **Lemma 4.1**.
* `Nivat.StarConfig.Jfun_finite_support`, `Nivat.StarConfig.exists_Jfun_ne_zero` —
  **Lemma 4.2**.

## Status

Complete; no `sorry`.
-/

namespace Nivat

open Finset

/-- The combinatorial core of Lemma 4.1 (c): among the subsets of a finite set `s` on which an
integer weight `g` never vanishes, the set of indices of negative weight is the *unique*
minimiser of `∑_{j ∈ C} g j`. -/
private theorem sum_lt_sum_of_filter_neg {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (g : ι → ℤ) (hg : ∀ j ∈ s, g j ≠ 0) {C : Finset ι} (hC : C ⊆ s)
    (hne : C ≠ s.filter fun j => g j < 0) :
    ∑ j ∈ s.filter (fun j => g j < 0), g j < ∑ j ∈ C, g j := by
  set M : Finset ι := s.filter (fun j => g j < 0) with hM
  have hsplitC : (∑ j ∈ C ∩ M, g j) + ∑ j ∈ C \ M, g j = ∑ j ∈ C, g j :=
    Finset.sum_inter_add_sum_sdiff C M g
  have hsplitM : (∑ j ∈ M ∩ C, g j) + ∑ j ∈ M \ C, g j = ∑ j ∈ M, g j :=
    Finset.sum_inter_add_sum_sdiff M C g
  have hcomm : ∑ j ∈ C ∩ M, g j = ∑ j ∈ M ∩ C, g j := by rw [Finset.inter_comm]
  have hpos : ∀ j ∈ C \ M, 0 < g j := by
    intro j hj
    obtain ⟨hjC, hjM⟩ := Finset.mem_sdiff.mp hj
    have hjs : j ∈ s := hC hjC
    have hnn : ¬ g j < 0 := fun h => hjM (by rw [hM]; exact Finset.mem_filter.mpr ⟨hjs, h⟩)
    exact lt_of_le_of_ne (not_lt.mp hnn) (Ne.symm (hg j hjs))
  have hneg : ∀ j ∈ M \ C, g j < 0 := by
    intro j hj
    have hjM := (Finset.mem_sdiff.mp hj).1
    rw [hM] at hjM
    exact (Finset.mem_filter.mp hjM).2
  have hA : 0 ≤ ∑ j ∈ C \ M, g j := Finset.sum_nonneg fun j hj => (hpos j hj).le
  have hB : 0 ≤ ∑ j ∈ M \ C, -g j := Finset.sum_nonneg fun j hj => by linarith [hneg j hj]
  rw [Finset.sum_neg_distrib] at hB
  rcases Finset.eq_empty_or_nonempty (C \ M) with h1 | h1
  · have hsub : C ⊆ M := Finset.sdiff_eq_empty_iff_subset.mp h1
    have h2 : (M \ C).Nonempty :=
      Finset.sdiff_nonempty.mpr fun hh => hne (Finset.Subset.antisymm hsub hh)
    have h3 : 0 < ∑ j ∈ M \ C, -g j := Finset.sum_pos (fun j hj => by linarith [hneg j hj]) h2
    rw [Finset.sum_neg_distrib] at h3
    linarith
  · have h3 : 0 < ∑ j ∈ C \ M, g j := Finset.sum_pos hpos h1
    linarith

namespace StarConfig

variable {p m : ℕ} [Fact p.Prime] (S : StarConfig p m)

/-- `fᵢ = Qᵢ ψ`.  Paper §4. -/
noncomputable def ffield (i : Fin m) : Config ℂ := act (S.Qop i) S.psi

/-- From `D = (T^{Hᵢ} - 1) Qᵢ` and `D ψ = 0`: `fᵢ` has period `Hᵢ`.  Paper §4. -/
theorem H_mem_Per_ffield (h11 : S.CaseTwo) (i : Fin m) : S.H i ∈ Per (S.ffield i) := by
  rw [← act_mono_sub_one_eq_zero_iff]
  show act (mono (S.H i) - 1) (act (S.Qop i) S.psi) = 0
  rw [← act_mul, ← S.Dop_eq_mul i]
  exact S.act_Dop_psi h11

/-- **(4.1).**  `fᵢ = Qᵢ w(σᵢ^+)`: letting `n → +∞` in `fᵢ = T^{n Hᵢ} fᵢ`.

The limit is taken along multiples of `Hᵢ` (`exists_zsmul_H_sigma`), which is exactly what
makes it compatible with the only periodicity of `fᵢ` available at this point. -/
theorem ffield_eq_sigma (h11 : S.CaseTwo) (i : Fin m) :
    S.ffield i = act (S.Qop i) (fun z => (S.enc (S.sigma i true z) : ℂ)) := by
  classical
  funext z
  obtain ⟨t, ht⟩ := S.exists_zsmul_H_sigma i true ((S.Ecomp i).image fun e => z + e)
  have hper : S.ffield i (z + t • S.H i) = S.ffield i z :=
    Per.apply (AddSubgroup.zsmul_mem _ (S.H_mem_Per_ffield h11 i) t) z
  rw [← hper]
  show act (S.Qop i) S.psi (z + t • S.H i) = act (S.Qop i) _ z
  rw [act_Qop_apply, act_Qop_apply]
  refine Finset.sum_congr rfl fun C hC => ?_
  have hmem : z + ∑ j ∈ C, S.H j ∈ (S.Ecomp i).image (fun e => z + e) :=
    Finset.mem_image.mpr ⟨∑ j ∈ C, S.H j, Finset.mem_image.mpr ⟨C, hC, rfl⟩, rfl⟩
  have hs := ht _ hmem
  have harg : z + t • S.H i + ∑ j ∈ C, S.H j = t • S.H i + (z + ∑ j ∈ C, S.H j) := by abel
  simp only [psi, hs, harg]

/-- **(4.2).**  `fᵢ = Qᵢ δᵢ` with `δᵢ = w(σᵢ^+) - w(Gᵢ^{+,R})`: each factor `T^{H j} - 1`
with `j ≠ i` annihilates the pure-tail field `w(Gᵢ^{+,R})`. -/
theorem ffield_eq_scalarDiff (h11 : S.CaseTwo) (i : Fin m) (δ : Bool) :
    S.ffield i = act (S.Qop i) (S.scalarDiff S.enc i true δ) := by
  classical
  -- `m ≥ 2`, so the product `Qᵢ` has at least one factor.
  obtain ⟨j, hj⟩ : (univ.erase i).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
      Fintype.card_fin]
    have := S.two_le
    omega
  -- That factor already kills the encoded pure-tail background.
  have hG : act (S.Qop i) (fun z => ((S.enc (S.Gfield i true δ z) : ℤ) : ℂ)) = 0 := by
    have hper : S.H j ∈ Per (fun z => ((S.enc (S.Gfield i true δ z) : ℤ) : ℂ)) :=
      mem_Per_comp (S.H_mem_Per_Gfield i j true δ) fun a => ((S.enc a : ℤ) : ℂ)
    rw [Qop, ← Finset.prod_erase_mul _ _ hj, act_mul,
      (act_mono_sub_one_eq_zero_iff _ _).mpr hper, act_zero_right]
  have hsplit : S.scalarDiff S.enc i true δ
      = (fun z => ((S.enc (S.sigma i true z) : ℤ) : ℂ))
        - fun z => ((S.enc (S.Gfield i true δ z) : ℤ) : ℂ) := rfl
  rw [S.ffield_eq_sigma h11 i, hsplit, act_sub_right, hG, sub_zero]

/-- **Lemma 4.1 (b).**  The support of `fᵢ` lies in a strip of bounded width in the direction
`vᵢ`: the right tail is cut off by `δᵢ^{+,R}`, the left tail by `δᵢ^{+,L}`. -/
theorem ffield_support_strip (h11 : S.CaseTwo) (i : Fin m) :
    ∃ c : ℤ, ∀ z, S.ffield i z ≠ 0 →
      S.ell i - c ≤ pi (S.v i) z ∧ pi (S.v i) z ≤ S.r i + c := by
  classical
  refine ⟨∑ e ∈ S.Ecomp i, |pi (S.v i) e|, fun z hz => ?_⟩
  have hbound : ∀ C ∈ (univ.erase i).powerset,
      |pi (S.v i) (∑ j ∈ C, S.H j)| ≤ ∑ e ∈ S.Ecomp i, |pi (S.v i) e| := fun C hC =>
    Finset.single_le_sum (f := fun e => |pi (S.v i) e|) (fun _ _ => abs_nonneg _)
      (Finset.mem_image.mpr ⟨C, hC, rfl⟩)
  constructor
  · by_contra hlt
    rw [not_le] at hlt
    refine hz ?_
    rw [S.ffield_eq_scalarDiff h11 i false, act_Qop_apply]
    refine Finset.sum_eq_zero fun C hC => ?_
    have hb := abs_le.mp (hbound C hC)
    have hsmall : pi (S.v i) (z + ∑ j ∈ C, S.H j) < S.ell i := by
      rw [pi_add]; linarith [hb.1, hb.2]
    rw [S.scalarDiff_eq_zero_left S.enc i true hsmall, mul_zero]
  · by_contra hgt
    rw [not_le] at hgt
    refine hz ?_
    rw [S.ffield_eq_scalarDiff h11 i true, act_Qop_apply]
    refine Finset.sum_eq_zero fun C hC => ?_
    have hb := abs_le.mp (hbound C hC)
    have hbig : S.r i < pi (S.v i) (z + ∑ j ∈ C, S.H j) := by
      rw [pi_add]; linarith [hb.1, hb.2]
    rw [S.scalarDiff_eq_zero_right S.enc i true hbig, mul_zero]

/-- Step (c) of Lemma 4.1: `δᵢ ≠ 0`, since `w` is injective and `Fᵢ = Rᵢ` would contradict
(S2). -/
theorem scalarDiff_ne_zero (i : Fin m) (δ : Bool) : S.scalarDiff S.enc i true δ ≠ 0 := by
  intro h
  -- Injectivity of the encoding turns `δᵢ = 0` into `σᵢ^+ = Gᵢ^{+,δ}`.
  have hcol : ∀ z, S.sigma i true z = S.Gfield i true δ z := by
    intro z
    have hz : (S.enc (S.sigma i true z) : ℂ) - (S.enc (S.Gfield i true δ z) : ℂ) = 0 :=
      congrFun h z
    have hint : (S.enc (S.sigma i true z) : ℤ) = S.enc (S.Gfield i true δ z) := by
      exact_mod_cast sub_eq_zero.mp hz
    exact S.enc_injective hint
  -- Cancelling the common background leaves `Fᵢ` equal to one of its own tails.
  have hF : S.F i = fun z => if δ then S.R i z else S.L i z := by
    funext z
    have h2 : S.F i z + S.bg i true z = (if δ then S.R i z else S.L i z) + S.bg i true z :=
      hcol z
    exact add_right_cancel h2
  refine S.S2 i ?_
  rw [hF]
  refine S.doublyPeriodic_of_Gamma_le fun u hu => ?_
  cases δ with
  | true => simpa using (S.mem_Gamma_iff.mp hu i).2
  | false => simpa using (S.mem_Gamma_iff.mp hu i).1

/-- The subset `C_min = {j ≠ i : πᵢ(H j) < 0}` realising the unique minimum of `πᵢ(H_C)`
over `C ⊆ [m] \ {i}`.  Paper Lemma 4.1 (c). -/
noncomputable def Cmin (i : Fin m) : Finset (Fin m) :=
  (univ.erase i).filter fun j => pi (S.v i) (S.H j) < 0

omit [Fact p.Prime] in
/-- `πᵢ(H_{C_min})` is the strict minimum of `πᵢ(H_C)` over `C ⊆ [m] \ {i}`.  This is a
statement about the `πᵢ`-projections and is unaffected by coincidences among the `H_C`.
Paper Lemma 4.1 (c). -/
theorem pi_Cmin_lt (i : Fin m) {C : Finset (Fin m)} (hC : C ⊆ univ.erase i)
    (hne : C ≠ S.Cmin i) :
    pi (S.v i) (∑ j ∈ S.Cmin i, S.H j) < pi (S.v i) (∑ j ∈ C, S.H j) := by
  have hg : ∀ j ∈ univ.erase i, pi (S.v i) (S.H j) ≠ 0 := by
    intro j hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    rw [H_eq, pi_smul]
    exact mul_ne_zero (by exact_mod_cast (S.kappa_pos j).ne')
      (S.nonparallel i j (Ne.symm hji))
  simp only [Cmin, pi_sum] at hne ⊢
  exact sum_lt_sum_of_filter_neg _ _ hg hC hne

/-- **Lemma 4.1 (c).**  `fᵢ ≠ 0`: evaluate `Qᵢ δᵢ` at `z₀ - H_{C_min}`, where `z₀` realises the
largest value of `πᵢ` on the support of `δᵢ`; only the term `C = C_min` survives. -/
theorem ffield_ne_zero (h11 : S.CaseTwo) (i : Fin m) : S.ffield i ≠ 0 := by
  classical
  obtain ⟨z₁, hz₁⟩ := Function.ne_iff.mp (S.scalarDiff_ne_zero i true)
  -- The largest `πᵢ`-level attained on the support of `δᵢ^{+,R}`.
  obtain ⟨μ, ⟨z₀, hz₀ne, hz₀pi⟩, hmax⟩ := Int.exists_greatest_of_bdd
    (P := fun n : ℤ => ∃ z : ℤ × ℤ, S.scalarDiff S.enc i true true z ≠ 0 ∧ pi (S.v i) z = n)
    ⟨S.r i, by
      rintro n ⟨z, hzne, rfl⟩
      by_contra hgt
      rw [not_le] at hgt
      exact hzne (S.scalarDiff_eq_zero_right S.enc i true hgt)⟩
    ⟨pi (S.v i) z₁, z₁, hz₁, rfl⟩
  intro hf
  have hmemC : S.Cmin i ∈ (univ.erase i).powerset :=
    Finset.mem_powerset.mpr (Finset.filter_subset _ _)
  set z : ℤ × ℤ := z₀ - ∑ j ∈ S.Cmin i, S.H j with hzdef
  -- Every other subset pushes the argument strictly above the maximal level `μ`.
  have hvanish : ∀ C ∈ (univ.erase i).powerset, C ≠ S.Cmin i →
      (-1 : ℂ) ^ (m - 1 - C.card)
        * S.scalarDiff S.enc i true true (z + ∑ j ∈ C, S.H j) = 0 := by
    intro C hC hCne
    have hlt := S.pi_Cmin_lt i (Finset.mem_powerset.mp hC) hCne
    have hpi : pi (S.v i) (z + ∑ j ∈ C, S.H j)
        = μ - pi (S.v i) (∑ j ∈ S.Cmin i, S.H j) + pi (S.v i) (∑ j ∈ C, S.H j) := by
      rw [hzdef, pi_add, pi_sub, hz₀pi]
    have hzero : S.scalarDiff S.enc i true true (z + ∑ j ∈ C, S.H j) = 0 := by
      by_contra hne
      have hle := hmax _ ⟨_, hne, rfl⟩
      rw [hpi] at hle
      linarith
    rw [hzero, mul_zero]
  have key : S.ffield i z = 0 := congrFun hf z
  rw [S.ffield_eq_scalarDiff h11 i true, act_Qop_apply,
    Finset.sum_eq_single_of_mem (S.Cmin i) hmemC hvanish,
    show z + ∑ j ∈ S.Cmin i, S.H j = z₀ by rw [hzdef]; abel] at key
  rcases mul_eq_zero.mp key with h | h
  · exact pow_ne_zero _ (by norm_num : (-1 : ℂ) ≠ 0) h
  · exact hz₀ne h

/-! ### §4.2 Two-point differences -/

/-- The two-point difference `J(d, ·) = D_z (ψ(z) ψ(z + d))`.  Paper §4, §5. -/
noncomputable def Jfun (d : ℤ × ℤ) : Config ℂ :=
  act S.Dop fun z => S.psi z * S.psi (z + d)

/-- **Lemma 4.2.**  `J(d, ·)` has finite support: `z ↦ ψ(z) ψ(z + d)` is a local function of
`θ` with window `{0, d}`, so Lemma 1.1 applies. -/
theorem Jfun_finite_support (d : ℤ × ℤ) : (Function.support (S.Jfun d)).Finite := by
  classical
  have hloc : IsLocal S.θ ({0, d} : Finset (ℤ × ℤ)) (fun z => S.psi z * S.psi (z + d)) := by
    refine ⟨fun g => ((S.enc (g ⟨0, by simp⟩) : ℤ) : ℂ) * ((S.enc (g ⟨d, by simp⟩) : ℤ) : ℂ),
      fun z => ?_⟩
    show ((S.enc (S.θ z) : ℤ) : ℂ) * ((S.enc (S.θ (z + d)) : ℤ) : ℂ)
        = ((S.enc (S.θ (z + (0 : ℤ × ℤ))) : ℤ) : ℂ) * ((S.enc (S.θ (z + d)) : ℤ) : ℂ)
    rw [add_zero]
  exact S.Dop_finite_support hloc

/-- The product witness `C(z) = fᵢ(z) fⱼ(z + d₀)` of the proof of Lemma 4.2: its support is
bounded, being the intersection of two strips in non-parallel directions. -/
theorem finite_support_ffield_mul (h11 : S.CaseTwo) {i j : Fin m} (hij : i ≠ j)
    (d₀ : ℤ × ℤ) :
    (Function.support fun z => S.ffield i z * S.ffield j (z + d₀)).Finite := by
  obtain ⟨ci, hci⟩ := S.ffield_support_strip h11 i
  obtain ⟨cj, hcj⟩ := S.ffield_support_strip h11 j
  refine (S.widenedStrip_inter_finite hij (max ci (cj + |pi (S.v j) d₀|))).subset ?_
  intro z hz
  have hz' : S.ffield i z * S.ffield j (z + d₀) ≠ 0 := hz
  have h1 := hci z (left_ne_zero_of_mul hz')
  have h2 := hcj (z + d₀) (right_ne_zero_of_mul hz')
  rw [pi_add] at h2
  have e1 : ci ≤ max ci (cj + |pi (S.v j) d₀|) := le_max_left _ _
  have e2 : cj + |pi (S.v j) d₀| ≤ max ci (cj + |pi (S.v j) d₀|) := le_max_right _ _
  have e3 := le_abs_self (pi (S.v j) d₀)
  have e4 := neg_abs_le (pi (S.v j) d₀)
  simp only [widenedStrip, Set.mem_inter_iff, Set.mem_ofPred_eq]
  exact ⟨⟨by linarith [h1.1], by linarith [h1.2]⟩,
    by linarith [h2.1], by linarith [h2.2]⟩

/-- The expansion `D C = ∑_{C₁, C₂} ± T^{H_{C₁}} J(d₀ + H_{C₂} - H_{C₁}, ·)` of the proof of
Lemma 4.2: if every two-point difference vanishes, so does `D` applied to the product
witness. -/
private theorem act_Dop_ffield_mul (hJ : ∀ d : ℤ × ℤ, S.Jfun d = 0) (i j : Fin m)
    (d₀ : ℤ × ℤ) :
    act S.Dop (fun z => S.ffield i z * S.ffield j (z + d₀)) = 0 := by
  classical
  have hzero : ∀ u₁ d : ℤ × ℤ,
      act S.Dop (fun z => S.psi (z + u₁) * S.psi (z + u₁ + d)) = 0 := by
    intro u₁ d
    have he : (fun z => S.psi (z + u₁) * S.psi (z + u₁ + d))
        = T u₁ (fun y => S.psi y * S.psi (y + d)) := rfl
    rw [he, act_T]
    show T u₁ (S.Jfun d) = 0
    rw [hJ d]
    funext z
    rfl
  have hexp : (fun z : ℤ × ℤ => S.ffield i z * S.ffield j (z + d₀))
      = ∑ C₁ ∈ (univ.erase i).powerset, ∑ C₂ ∈ (univ.erase j).powerset,
          fun z : ℤ × ℤ =>
            ((-1 : ℂ) ^ (m - 1 - C₁.card) * (-1 : ℂ) ^ (m - 1 - C₂.card))
              * (S.psi (z + ∑ k ∈ C₁, S.H k)
                 * S.psi (z + ∑ k ∈ C₁, S.H k
                     + (d₀ + ∑ k ∈ C₂, S.H k - ∑ k ∈ C₁, S.H k))) := by
    funext z
    simp only [Finset.sum_apply]
    show act (S.Qop i) S.psi z * act (S.Qop j) S.psi (z + d₀) = _
    rw [act_Qop_apply, act_Qop_apply, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun C₁ _ => Finset.sum_congr rfl fun C₂ _ => ?_
    rw [show z + ∑ k ∈ C₁, S.H k + (d₀ + ∑ k ∈ C₂, S.H k - ∑ k ∈ C₁, S.H k)
        = z + d₀ + ∑ k ∈ C₂, S.H k by abel]
    ring
  rw [hexp, act_sum_right]
  refine Finset.sum_eq_zero fun C₁ _ => ?_
  rw [act_sum_right]
  refine Finset.sum_eq_zero fun C₂ _ => ?_
  rw [act_const_mul, hzero]
  funext y
  simp

/-- **Lemma 4.2.**  There exists `d` with `J(d, ·) ≠ 0`: otherwise `D` would kill the finitely
supported non-zero product witness, contradicting Lemma 1.2. -/
theorem exists_Jfun_ne_zero (h11 : S.CaseTwo) : ∃ d : ℤ × ℤ, S.Jfun d ≠ 0 := by
  classical
  by_contra hcon
  have hJ : ∀ d : ℤ × ℤ, S.Jfun d = 0 := fun d => by
    by_contra hd
    exact hcon ⟨d, hd⟩
  obtain ⟨xi, hxi⟩ := Function.ne_iff.mp (S.ffield_ne_zero h11 S.idx₀)
  obtain ⟨xj, hxj⟩ := Function.ne_iff.mp (S.ffield_ne_zero h11 S.idx₁)
  have hCne : (fun z => S.ffield S.idx₀ z * S.ffield S.idx₁ (z + (xj - xi))) ≠ 0 := by
    intro hz
    have h0 : S.ffield S.idx₀ xi * S.ffield S.idx₁ (xi + (xj - xi)) = 0 := congrFun hz xi
    rw [show xi + (xj - xi) = xj by abel] at h0
    exact mul_ne_zero hxi hxj h0
  exact act_ne_zero S.Dop_ne_zero
    (S.finite_support_ffield_mul h11 S.idx₀_ne_idx₁ (xj - xi)) hCne
    (S.act_Dop_ffield_mul hJ S.idx₀ S.idx₁ (xj - xi))

/-- `J(0, ·) = 0`: `ψ² = w'(θ)` with `w'(a) = w(a)²` is a single-site colour function, killed
by `D` under (1.1).  Paper Proposition 5.3. -/
theorem Jfun_zero (h11 : S.CaseTwo) : S.Jfun 0 = 0 := by
  have h : (fun z => S.psi z * S.psi (z + 0))
      = fun z => ((S.enc (S.θ z) ^ 2 : ℤ) : ℂ) := by
    funext z
    show ((S.enc (S.θ z) : ℤ) : ℂ) * ((S.enc (S.θ (z + 0)) : ℤ) : ℂ) = _
    rw [add_zero]
    push_cast
    ring
  rw [Jfun, h]
  exact S.Dop_encoding_eq_zero h11 fun a => S.enc a ^ 2

end StarConfig

end Nivat
