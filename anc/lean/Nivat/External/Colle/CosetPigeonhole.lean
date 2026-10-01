import Nivat.External.Colle.Theorem114Step3
import Nivat.Defs.Orbit

set_option autoImplicit false

namespace Nivat.CosetPigeonhole

open Nivat

noncomputable def exhaustion : ℕ → Finset (ℤ × ℤ) :=
  fun n => (Finset.Icc (-(n:ℤ)) n) ×ˢ (Finset.Icc (-(n:ℤ)) n)

theorem exhaustion_mono : Monotone exhaustion := by
  intro m n hmn
  unfold exhaustion
  apply Finset.product_subset_product <;>
    exact Finset.Icc_subset_Icc (by omega) (by exact_mod_cast hmn)

theorem exhaustion_covers (W : Finset (ℤ × ℤ)) : ∃ n, W ⊆ exhaustion n := by
  classical
  rcases W.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, Finset.empty_subset _⟩
  · obtain ⟨M, hM⟩ := (W.image (fun z => max z.1.natAbs z.2.natAbs)).exists_le
    refine ⟨M, fun z hz => ?_⟩
    have hmem : max z.1.natAbs z.2.natAbs ∈ W.image (fun z => max z.1.natAbs z.2.natAbs) :=
      Finset.mem_image_of_mem _ hz
    have h1 : max z.1.natAbs z.2.natAbs ≤ M := hM _ hmem
    have h1a : z.1.natAbs ≤ M := le_trans (le_max_left _ _) h1
    have h2a : z.2.natAbs ≤ M := le_trans (le_max_right _ _) h1
    have e1 : |z.1| = (z.1.natAbs : ℤ) := (Int.abs_eq_natAbs z.1)
    have e2 : |z.2| = (z.2.natAbs : ℤ) := (Int.abs_eq_natAbs z.2)
    unfold exhaustion
    simp only [Finset.mem_product, Finset.mem_Icc]
    refine ⟨?_, ?_⟩
    · rw [← abs_le, e1]; exact_mod_cast h1a
    · rw [← abs_le, e2]; exact_mod_cast h2a

theorem exists_infinite_fiber {k : ℕ} (hk : 0 < k) (f : ℕ → Fin k) :
    ∃ j : Fin k, {n : ℕ | f n = j}.Infinite := by
  have _ : NeZero k := ⟨hk.ne'⟩
  obtain ⟨j, hj⟩ := Finite.exists_infinite_fiber f
  refine ⟨j, ?_⟩
  have heq : f ⁻¹' {j} = {n : ℕ | f n = j} := by
    ext n; simp [Set.mem_preimage, Set.mem_singleton_iff]
  rwa [heq, Set.infinite_coe_iff] at hj

theorem acc_point_in_finite_coset
    {ξ' y : Config ℤ} {u' : ℤ × ℤ} {k : ℕ} (hk : 0 < k)
    (hacc : ∀ (W : Finset (ℤ × ℤ)) (M : ℕ), ∃ t : ℕ, M ≤ t ∧
              ∀ z ∈ W, y z = T ((t : ℤ) • u') ξ' z) :
    ∃ j : Fin k, ∀ (W : Finset (ℤ × ℤ)) (M : ℕ), ∃ s : ℕ, M ≤ s ∧
      ∀ z ∈ W, y z = T ((s : ℤ) • ((k : ℤ) • u')) (T ((j : ℤ) • u') ξ') z := by
  classical
  choose t ht using fun n => hacc (exhaustion n) n
  have ht_ge : ∀ n, n ≤ t n := fun n => (ht n).1
  let f : ℕ → Fin k := fun n => ⟨(t n) % k, Nat.mod_lt (t n) hk⟩
  obtain ⟨j, hj_inf⟩ := exists_infinite_fiber hk f
  refine ⟨j, fun W_goal M_goal => ?_⟩
  obtain ⟨n_cover, hn_cover⟩ := exhaustion_covers W_goal
  set C : ℕ := max n_cover (k * M_goal + (j : ℕ)) with hC_def
  have hbig : ∃ n, f n = j ∧ n ≥ n_cover ∧ t n ≥ k * M_goal + (j:ℕ) := by
    by_contra hcon
    push Not at hcon
    have hsub : {n : ℕ | f n = j} ⊆ {n : ℕ | n < C} := by
      intro n hn
      simp only [Set.mem_setOf_eq] at hn
      rcases lt_or_ge n C with hlt | hge
      · exact hlt
      · exfalso
        have hn_cover' : n ≥ n_cover := le_trans (le_max_left _ _) hge
        have hn_big : n ≥ k * M_goal + (j:ℕ) := le_trans (le_max_right _ _) hge
        have htn_big : t n ≥ k * M_goal + (j:ℕ) := le_trans hn_big (ht_ge n)
        exact absurd htn_big (not_le.mpr (hcon n hn hn_cover'))
    exact hj_inf (Set.Finite.subset (Set.finite_Iio C) hsub)
  obtain ⟨n, hfn, hn_ge, htn_ge⟩ := hbig
  have hmod : t n % k = (j : ℕ) := by
    have hfn' := hfn
    unfold f at hfn'
    exact Fin.mk.inj_iff.mp hfn'
  set s := t n / k with hs_def
  have hdivmod : t n = k * s + (j:ℕ) := by
    have h1 : t n = k * (t n / k) + t n % k := (Nat.div_add_mod (t n) k).symm
    rw [hmod] at h1
    exact h1
  have hs_ge : M_goal ≤ s := by
    by_contra hcon
    push Not at hcon
    have hbound : s ≤ M_goal - 1 := by omega
    have h3 : t n < k * M_goal := by
      calc t n = k * s + (j:ℕ) := hdivmod
      _ < k * s + k := by omega
      _ = k * (s + 1) := by ring
      _ ≤ k * M_goal := Nat.mul_le_mul_left k (by omega)
    omega
  refine ⟨s, hs_ge, fun z hz => ?_⟩
  have hz_Wn : z ∈ exhaustion n := exhaustion_mono hn_ge (hn_cover hz)
  have heq := (ht n).2 z hz_Wn
  rw [heq]
  have htn_eq : (t n : ℤ) • u' = (s : ℤ) • ((k : ℤ) • u') + (j : ℤ) • u' := by
    have h2 : (t n : ℤ) = (k:ℤ) * (s : ℤ) + (j : ℤ) := by exact_mod_cast hdivmod
    rw [h2]
    module
  rw [htn_eq]
  rw [T_add]


end Nivat.CosetPigeonhole
