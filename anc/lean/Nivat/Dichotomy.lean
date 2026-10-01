/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.Defs.StarConfig
import Nivat.Defs.Orbit
import Nivat.Laurent.Basic
import Mathlib.Algebra.MonoidAlgebra.Support
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Data.Int.Interval
import Mathlib.Data.Set.Finite.Lattice

/-!
# §1. Finite differences and the first case

Formalisation of §0.3 (the difference operator) and §1 of *The Convex Nivat Conjecture*
(Pan).

The difference operator `D = ∏ᵢ (T^{H i} - 1)` turns a local function of a star configuration
into one of finite support (Lemma 1.1).  Since `ℂ[T₁^±, T₂^±]` is an integral domain, a
non-zero Laurent polynomial cannot kill such a function (Lemma 1.2, proved in
`Nivat.Laurent.Basic`).  Together these settle the case `D I_a ≠ 0` outright (Proposition 1.3),
leaving the standing hypothesis (1.1) for §§2–7.

## Main definitions

* `Nivat.StarConfig.Dop` — `D = ∏ᵢ (T^{H i} - 1)`.
* `Nivat.StarConfig.Qop` — `Q i = ∏_{j ≠ i} (T^{H j} - 1)`.
* `Nivat.ind` — the colour indicator `I_a = [θ = a]`, valued in `{0, 1} ⊆ ℂ`.
* `Nivat.StarConfig.CaseTwo` — the standing hypothesis (1.1).

## Main results

* `Nivat.StarConfig.Dop_ne_zero` — `D ≠ 0`.
* `Nivat.StarConfig.Dop_finite_support` — **Lemma 1.1**.
* `Nivat.StarConfig.P_ge_of_Dop_ind_ne_zero` — **Proposition 1.3**.

## Status

Complete; no `sorry`.
-/

namespace Nivat

open Finset

open scoped Pointwise

/-! ### Two facts about monomials

These belong morally to `Nivat.Laurent.Basic`; they are collected here because they are first
needed for `D ≠ 0`. -/

/-- A monomial is the unit of the ring only for the exponent `0`. -/
theorem mono_eq_one_iff {R : Type*} [CommRing R] [Nontrivial R] {u : ℤ × ℤ} :
    (mono u : LaurentTwo R) = 1 ↔ u = 0 := by
  rw [← mono_zero]
  simp only [mono]
  exact AddMonoidAlgebra.single_left_inj one_ne_zero

/-- `T^u - 1` is non-zero as soon as `u ≠ 0`.  Paper §0.3: "each factor is non-zero". -/
theorem mono_sub_one_ne_zero {R : Type*} [CommRing R] [Nontrivial R] {u : ℤ × ℤ} (hu : u ≠ 0) :
    (mono u - 1 : LaurentTwo R) ≠ 0 := by
  rw [sub_ne_zero]
  exact fun h => hu (mono_eq_one_iff.mp h)

/-- `T^{n u} = (T^u)^n`. -/
theorem mono_pow {R : Type*} [CommRing R] (u : ℤ × ℤ) (k : ℕ) :
    (mono u : LaurentTwo R) ^ k = mono ((k : ℤ) • u) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, mono_mul_mono]
    congr 1
    push_cast
    rw [add_smul, one_smul]

open Classical in
/-- The colour indicator `I_a = [θ = a]`, valued in `{0, 1} ⊆ ℂ`.  Paper §0.3: "colour
indicators … take place in characteristic zero". -/
noncomputable def ind {α : Type*} (θ : Config α) (a : α) : Config ℂ :=
  fun z => if θ z = a then 1 else 0

theorem isLocal_ind {α : Type*} (θ : Config α) (a : α) :
    IsLocal θ {0} (ind θ a) :=
  ⟨fun g => ind (fun _ : ℤ × ℤ => g ⟨0, Finset.mem_singleton_self 0⟩) a 0, fun z => by
    show (ind θ a) z = ind (fun _ : ℤ × ℤ => θ (z + (0 : ℤ × ℤ))) a 0
    rw [add_zero]
    rfl⟩

/-- `I_a` takes the value `1` at the points of colour `a`. -/
theorem ind_self {α : Type*} (θ : Config α) (z : ℤ × ℤ) : ind θ (θ z) z = 1 := if_pos rfl

/-- `I_a` takes the value `0` at the points of any other colour. -/
theorem ind_eq_zero {α : Type*} {θ : Config α} {a : α} {z : ℤ × ℤ} (h : θ z ≠ a) :
    ind θ a z = 0 := if_neg h

namespace StarConfig

variable {p m : ℕ} (S : StarConfig p m)

/-! ### The difference operator (§0.3) -/

/-- The difference operator `D = ∏ᵢ (T^{H i} - 1) ∈ ℂ[T₁^±, T₂^±]`.  Paper §0.3. -/
noncomputable def Dop : LaurentTwo ℂ := ∏ i, (mono (S.H i) - 1)

/-- `Q i = ∏_{j ≠ i} (T^{H j} - 1)`.  Paper (0.2). -/
noncomputable def Qop (i : Fin m) : LaurentTwo ℂ :=
  ∏ j ∈ univ.erase i, (mono (S.H j) - 1)

/-- `H i` is a non-zero lattice vector: it is a positive multiple of the primitive `v i`. -/
theorem H_ne_zero (i : Fin m) : S.H i ≠ 0 := by
  rw [H_eq]
  refine smul_ne_zero ?_ (S.primitive i).ne_zero
  exact_mod_cast (S.kappa_pos i).ne'

/-- `D = (T^{H i} - 1) Q i`.  Paper §0.3. -/
theorem Dop_eq_mul (i : Fin m) : S.Dop = (mono (S.H i) - 1) * S.Qop i := by
  classical
  simp only [Dop, Qop]
  exact (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm

/-- `D ≠ 0`: each factor is non-zero and `ℂ[T^±]` is an integral domain.  Paper §0.3. -/
theorem Dop_ne_zero : S.Dop ≠ 0 := by
  simp only [Dop]
  exact Finset.prod_ne_zero_iff.mpr fun i _ => mono_sub_one_ne_zero (S.H_ne_zero i)

theorem Qop_ne_zero (i : Fin m) : S.Qop i ≠ 0 := by
  classical
  simp only [Qop]
  exact Finset.prod_ne_zero_iff.mpr fun j _ => mono_sub_one_ne_zero (S.H_ne_zero j)

/-- The formal exponent set `E = {H_C : C ⊆ [m]}`.  Paper §0.3. -/
noncomputable def E : Finset (ℤ × ℤ) :=
  (univ : Finset (Fin m)).powerset.image fun C => ∑ i ∈ C, S.H i

/-- The formal exponent set `E i = {H_C : C ⊆ [m] \ {i}}`.  Paper §0.3. -/
noncomputable def Ecomp (i : Fin m) : Finset (ℤ × ℤ) :=
  (univ.erase i).powerset.image fun C => ∑ j ∈ C, S.H j

theorem sum_mem_E (C : Finset (Fin m)) : (∑ i ∈ C, S.H i) ∈ S.E :=
  Finset.mem_image.mpr ⟨C, Finset.mem_powerset.mpr (Finset.subset_univ C), rfl⟩

/-- The support of `T^u - 1` consists of `u` and `0`. -/
private theorem supp_mono_sub_one_subset (u : ℤ × ℤ) :
    supp (mono u - 1 : LaurentTwo ℂ) ⊆ {u, 0} := by
  classical
  intro t ht
  rw [mem_supp] at ht
  by_contra hn
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
  exact ht (by
    simp [mono, AddMonoidAlgebra.one_def, Ne.symm hn.1, Ne.symm hn.2])

theorem supp_Dop_subset : supp S.Dop ⊆ S.E := by
  classical
  have key : ∀ s : Finset (Fin m),
      supp (∏ i ∈ s, (mono (S.H i) - 1) : LaurentTwo ℂ)
        ⊆ s.powerset.image fun C => ∑ i ∈ C, S.H i := by
    intro s
    induction s using Finset.induction with
    | empty =>
      intro u hu
      rw [Finset.prod_empty, mem_supp] at hu
      have hu0 : u = 0 := by
        by_contra hn
        exact hu (by simp [AddMonoidAlgebra.one_def, Ne.symm hn])
      simp [hu0]
    | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      intro u hu
      have hmul := AddMonoidAlgebra.support_coeff_mul_subset
        (mono (S.H a) - 1 : LaurentTwo ℂ) (∏ i ∈ s, (mono (S.H i) - 1))
      obtain ⟨y, hy, z, hz, hyz⟩ := Finset.mem_add.mp (hmul hu)
      have hy' := supp_mono_sub_one_subset (S.H a) hy
      obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp (ih hz)
      have hCs : C ⊆ s := Finset.mem_powerset.mp hC
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy'
      rcases hy' with rfl | rfl
      · refine Finset.mem_image.mpr ⟨insert a C, Finset.mem_powerset.mpr ?_, ?_⟩
        · exact Finset.insert_subset_insert a hCs
        · rw [Finset.sum_insert fun h => ha (hCs h)]
          exact hyz
      · refine Finset.mem_image.mpr ⟨C, Finset.mem_powerset.mpr ?_, ?_⟩
        · exact hCs.trans (Finset.subset_insert a s)
        · rw [← hyz]; abel
  simpa only [Dop, E] using key univ

/-- The formal expansion (0.1). -/
theorem act_Dop_apply (g : Config ℂ) (z : ℤ × ℤ) :
    act S.Dop g z
      = ∑ C ∈ (univ : Finset (Fin m)).powerset, (-1 : ℂ) ^ (m - C.card) * g (z + ∑ i ∈ C, S.H i) := by
  classical
  simp only [Dop]
  rw [act_prod_mono_sub_one]
  simp

/-- The formal expansion (0.2). -/
theorem act_Qop_apply (i : Fin m) (g : Config ℂ) (z : ℤ × ℤ) :
    act (S.Qop i) g z
      = ∑ C ∈ (univ.erase i).powerset,
          (-1 : ℂ) ^ (m - 1 - C.card) * g (z + ∑ j ∈ C, S.H j) := by
  classical
  simp only [Qop]
  rw [act_prod_mono_sub_one]
  simp [Finset.card_erase_of_mem]

/-! ### §1.1 Differencing turns a local function into one of finite support -/

/-- The widened strip in direction `i` used in the proof of Lemma 1.1: outside it, the field
`F i` is identically one pure tail on the whole window. -/
def widenedStrip (i : Fin m) (c : ℤ) : Set (ℤ × ℤ) :=
  {z | S.ell i - c ≤ pi (S.v i) z ∧ pi (S.v i) z ≤ S.r i + c}

/-- The intersection of two widened strips in non-parallel directions is finite: "the
intersection of two strips of bounded width in non-parallel directions is bounded". -/
theorem widenedStrip_inter_finite {i j : Fin m} (hij : i ≠ j) (c : ℤ) :
    (S.widenedStrip i c ∩ S.widenedStrip j c).Finite := by
  classical
  have hd : det (S.v i) (S.v j) ≠ 0 := S.nonparallel i j hij
  set φ : ℤ × ℤ → ℤ × ℤ := fun z => (pi (S.v i) z, pi (S.v j) z) with hφ
  have hinj : Function.Injective φ := by
    intro z w hzw
    have h1 : pi (S.v i) z = pi (S.v i) w := congrArg Prod.fst hzw
    have h2 : pi (S.v j) z = pi (S.v j) w := congrArg Prod.snd hzw
    simp only [pi_apply] at h1 h2
    have e1 : det (S.v i) (S.v j) * (z.1 - w.1) = 0 := by
      simp only [det]
      linear_combination (S.v j).1 * h1 - (S.v i).1 * h2
    have e2 : det (S.v i) (S.v j) * (z.2 - w.2) = 0 := by
      simp only [det]
      linear_combination (S.v j).2 * h1 - (S.v i).2 * h2
    have z1 : z.1 = w.1 := by
      rcases mul_eq_zero.mp e1 with h | h
      · exact absurd h hd
      · omega
    have z2 : z.2 = w.2 := by
      rcases mul_eq_zero.mp e2 with h | h
      · exact absurd h hd
      · omega
    exact Prod.ext z1 z2
  have himg : φ '' (S.widenedStrip i c ∩ S.widenedStrip j c) ⊆
      Set.Icc (S.ell i - c) (S.r i + c) ×ˢ Set.Icc (S.ell j - c) (S.r j + c) := by
    rintro _ ⟨z, hz, rfl⟩
    simp only [widenedStrip, Set.mem_inter_iff, Set.mem_ofPred_eq] at hz
    exact ⟨⟨hz.1.1, hz.1.2⟩, ⟨hz.2.1, hz.2.2⟩⟩
  exact Set.Finite.of_finite_image
    (((Set.finite_Icc _ _).prod (Set.finite_Icc _ _)).subset himg) hinj.injOn

/-- **Lemma 1.1.**  Let `h(z) = θ|_{z+W}` with `W ⊆ ℤ²` finite.  Then `D h` has finite
support. -/
theorem Dop_finite_support {W : Finset (ℤ × ℤ)} {h : Config ℂ} (hh : IsLocal S.θ W h) :
    (Function.support (act S.Dop h)).Finite := by
  classical
  obtain ⟨Fh, hFh⟩ := hh
  -- the enlarged window `M = E + W` of the paper, and a uniform width for the strips
  set M : Finset (ℤ × ℤ) := S.E + W with hMdef
  set c : ℤ := ∑ j : Fin m, ∑ s ∈ M, |pi (S.v j) s| with hcdef
  have hbound : ∀ (j : Fin m), ∀ s ∈ M, |pi (S.v j) s| ≤ c := by
    intro j s hs
    have h1 : |pi (S.v j) s| ≤ ∑ t ∈ M, |pi (S.v j) t| :=
      Finset.single_le_sum (f := fun t => |pi (S.v j) t|) (fun _ _ => abs_nonneg _) hs
    have h2 : (∑ t ∈ M, |pi (S.v j) t|) ≤ c :=
      Finset.single_le_sum (f := fun k : Fin m => ∑ t ∈ M, |pi (S.v k) t|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ j)
    exact h1.trans h2
  -- if direction `j` is inactive at `z`, the whole of `z + M` sits in one tail of direction `j`
  have tail : ∀ (z : ℤ × ℤ) (j l : Fin m), z ∉ S.widenedStrip j c →
      ∀ s ∈ M, s + S.H l ∈ M → S.F j (z + (s + S.H l)) = S.F j (z + s) := by
    intro z j l hz s hs hs'
    simp only [widenedStrip, Set.mem_ofPred_eq, not_and_or, not_le] at hz
    have hassoc : z + (s + S.H l) = z + s + S.H l := by abel
    rcases hz with hz | hz
    · have hL : ∀ t ∈ M, S.F j (z + t) = S.L j (z + t) := by
        intro t ht
        refine S.S3_L j _ ?_
        have hb := (abs_le.mp (hbound j t ht)).2
        rw [pi_add]
        omega
      rw [hL _ hs', hL _ hs, hassoc]
      exact Per.apply (S.H_mem_Per_L l j) (z + s)
    · have hR : ∀ t ∈ M, S.F j (z + t) = S.R j (z + t) := by
        intro t ht
        refine S.S3_R j _ ?_
        have hb := (abs_le.mp (hbound j t ht)).1
        rw [pi_add]
        omega
      rw [hR _ hs', hR _ hs, hassoc]
      exact Per.apply (S.H_mem_Per_R l j) (z + s)
  -- hence `θ` itself is `H j₀`-invariant on `z + M` when every other direction is inactive
  have theta : ∀ (z : ℤ × ℤ) (j₀ : Fin m), (∀ j, j ≠ j₀ → z ∉ S.widenedStrip j c) →
      ∀ s ∈ M, s + S.H j₀ ∈ M → S.θ (z + (s + S.H j₀)) = S.θ (z + s) := by
    intro z j₀ hact s hs hs'
    simp only [θ_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : j = j₀
    · subst hj
      rw [show z + (s + S.H j) = z + s + S.H j by abel]
      exact Per.apply (S.H_mem_Per_F j) (z + s)
    · exact tail z j j₀ (hact j hj) s hs hs'
  -- the paper's Claim: at most one active direction forces `D h (z) = 0`
  have claim : ∀ (z : ℤ × ℤ) (j₀ : Fin m), (∀ j, j ≠ j₀ → z ∉ S.widenedStrip j c) →
      act S.Dop h z = 0 := by
    intro z j₀ hact
    rw [S.Dop_eq_mul j₀, act_mul, act_sub_left, act_mono, act_one, Pi.sub_apply, T_apply,
      sub_eq_zero, act_Qop_apply, act_Qop_apply]
    refine Finset.sum_congr rfl fun C hC => ?_
    congr 1
    have hCs : C ⊆ univ.erase j₀ := Finset.mem_powerset.mp hC
    have hj₀C : j₀ ∉ C := fun hmem => (Finset.mem_erase.mp (hCs hmem)).1 rfl
    rw [hFh, hFh]
    congr 1
    funext w
    have hs : (∑ j ∈ C, S.H j) + (w : ℤ × ℤ) ∈ M :=
      Finset.add_mem_add (S.sum_mem_E C) w.2
    have hs' : ((∑ j ∈ C, S.H j) + (w : ℤ × ℤ)) + S.H j₀ ∈ M := by
      rw [show ((∑ j ∈ C, S.H j) + (w : ℤ × ℤ)) + S.H j₀
          = (∑ j ∈ insert j₀ C, S.H j) + (w : ℤ × ℤ) by
        rw [Finset.sum_insert hj₀C]; abel]
      exact Finset.add_mem_add (S.sum_mem_E _) w.2
    have hkey := theta z j₀ hact _ hs hs'
    show S.θ (z + S.H j₀ + (∑ j ∈ C, S.H j) + (w : ℤ × ℤ))
        = S.θ (z + (∑ j ∈ C, S.H j) + (w : ℤ × ℤ))
    calc S.θ (z + S.H j₀ + (∑ j ∈ C, S.H j) + (w : ℤ × ℤ))
        = S.θ (z + (((∑ j ∈ C, S.H j) + (w : ℤ × ℤ)) + S.H j₀)) := by congr 1; abel
      _ = S.θ (z + ((∑ j ∈ C, S.H j) + (w : ℤ × ℤ))) := hkey
      _ = S.θ (z + (∑ j ∈ C, S.H j) + (w : ℤ × ℤ)) := by congr 1; abel
  -- conclusion: the support meets two non-parallel strips
  have hm : 0 < m := lt_of_lt_of_le (by norm_num) S.two_le
  have hsub : Function.support (act S.Dop h) ⊆
      ⋃ q ∈ {q : Fin m × Fin m | q.1 ≠ q.2},
        (S.widenedStrip q.1 c ∩ S.widenedStrip q.2 c) := by
    intro z hz
    have step : ∀ j₀ : Fin m, ∃ j, j ≠ j₀ ∧ z ∈ S.widenedStrip j c := by
      intro j₀
      by_contra hcon
      push Not at hcon
      exact hz (claim z j₀ fun j hj => hcon j hj)
    obtain ⟨j₁, -, hj₁⟩ := step ⟨0, hm⟩
    obtain ⟨j₂, hne, hj₂⟩ := step j₁
    exact Set.mem_biUnion
      (show (j₂, j₁) ∈ {q : Fin m × Fin m | q.1 ≠ q.2} from hne) ⟨hj₂, hj₁⟩
  exact (Set.Finite.biUnion (Set.toFinite _)
    (fun q hq => S.widenedStrip_inter_finite hq c)).subset hsub

/-! ### §1.3 The first case -/

/-- `D` kills constant functions: a constant has every vector as a period. -/
theorem act_Dop_const (k : ℂ) : act S.Dop (fun _ => k) = 0 := by
  have hm : 0 < m := lt_of_lt_of_le (by norm_num) S.two_le
  set j : Fin m := ⟨0, hm⟩ with hj
  have hcomm : S.Dop = S.Qop j * (mono (S.H j) - 1) := by
    rw [S.Dop_eq_mul j]; ring
  rw [hcomm, act_mul,
    show act (mono (S.H j) - 1) (fun _ => k) = 0 from
      (act_mono_sub_one_eq_zero_iff _ _).mpr (by rw [mem_Per_iff]; rfl),
    act_zero_right]

/-- **Proposition 1.3.**  If `D I_a ≠ 0` for some `a ∈ 𝔽_p`, then `P_θ(S') ≥ |S'| + 1` for
every non-empty finite `S' ⊆ ℤ²`; no convexity is needed. -/
theorem P_ge_of_Dop_ind_ne_zero [NeZero p] {a : ZMod p} (ha : act S.Dop (ind S.θ a) ≠ 0)
    {W : Finset (ℤ × ℤ)} (_hW : W.Nonempty) : W.card + 1 ≤ P S.θ W := by
  classical
  by_contra hcon
  push Not at hcon
  have hle : P S.θ W ≤ W.card := by omega
  have : Fintype ↥(patterns S.θ W) := (patterns_finite S.θ W).fintype
  have hcard : Fintype.card ↥(patterns S.θ W) = P S.θ W := by
    rw [P, ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  -- the `|W| + 1` functions `1` and `ρ ↦ [ρ(s) = a]` on the finite set of patterns
  set gfam : Option { x // x ∈ W } → (↥(patterns S.θ W) → ℂ) := fun i ρ =>
    i.elim 1 fun s => ind (fun _ : ℤ × ℤ => ρ.1 s) a 0
  have hgnone : ∀ ρ, gfam none ρ = 1 := fun _ => rfl
  have hgsome : ∀ (s : { x // x ∈ W }) (y : ℤ × ℤ) (h : pattern S.θ W y ∈ patterns S.θ W),
      gfam (some s) ⟨pattern S.θ W y, h⟩ = ind S.θ a (y + (s : ℤ × ℤ)) := fun _ _ _ => rfl
  have hdep : ¬ LinearIndependent ℂ gfam := by
    intro hli
    have hcle := hli.fintype_card_le_finrank
    rw [Module.finrank_pi ℂ, hcard, Fintype.card_option, Fintype.card_coe] at hcle
    omega
  obtain ⟨cc, hrel, i₀, hi₀⟩ := Fintype.not_linearIndependent_iff.mp hdep
  -- the relation, read at the pattern anchored at `z`
  have heval : ∀ z : ℤ × ℤ,
      cc none + ∑ s : { x // x ∈ W }, cc (some s) * ind S.θ a (z + (s : ℤ × ℤ)) = 0 := by
    intro z
    have hmem : pattern S.θ W z ∈ patterns S.θ W := ⟨z, rfl⟩
    have hr := congrFun hrel ⟨pattern S.θ W z, hmem⟩
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hr
    rw [Fintype.sum_option, hgnone, mul_one] at hr
    simpa only [hgsome] using hr
  -- the Laurent polynomial `q = ∑_{s ∈ W} c_s T^s`
  set cf : ℤ × ℤ → ℂ := fun t => if ht : t ∈ W then cc (some ⟨t, ht⟩) else 0 with hcf
  have hcfsupp : ∀ t : ℤ × ℤ, cf t ≠ 0 → t ∈ W := by
    intro t ht
    by_contra hn
    exact ht (by simp [hcf, hn])
  set q : LaurentTwo ℂ := AddMonoidAlgebra.ofCoeff (Finsupp.onFinset W cf hcfsupp) with hq
  have hactq : ∀ (g : Config ℂ) (z : ℤ × ℤ), act q g z = ∑ t ∈ W, cf t * g (z + t) := by
    intro g z
    rw [act_apply]
    rw [show q.coeff = Finsupp.onFinset W cf hcfsupp from rfl,
      Finsupp.sum_of_support_subset _ Finsupp.support_onFinset_subset _ (by intro i _; ring)]
    simp [Finsupp.onFinset_apply]
  have hconst : ∀ z : ℤ × ℤ, act q (ind S.θ a) z = -cc none := by
    intro z
    rw [hactq]
    have hsum : ∑ t ∈ W, cf t * ind S.θ a (z + t)
        = ∑ s : { x // x ∈ W }, cc (some s) * ind S.θ a (z + (s : ℤ × ℤ)) := by
      rw [← Finset.sum_attach W fun t => cf t * ind S.θ a (z + t)]
      exact Finset.sum_congr rfl fun s _ => by simp [hcf, s.2]
    rw [hsum]
    linear_combination heval z
  have hqne : q ≠ 0 := by
    intro h0
    have hall : ∀ s : { x // x ∈ W }, cc (some s) = 0 := by
      intro s
      have hcz : q.coeff (s : ℤ × ℤ) = 0 := by rw [h0]; simp
      rw [show q.coeff = Finsupp.onFinset W cf hcfsupp from rfl, Finsupp.onFinset_apply] at hcz
      simpa [hcf, s.2] using hcz
    have hnone : cc none = 0 := by
      have hz := heval 0
      simp only [hall, zero_mul, Finset.sum_const_zero, add_zero] at hz
      exact hz
    rcases i₀ with _ | s
    · exact hi₀ hnone
    · exact hi₀ (hall s)
  -- `D q I_a = 0` since `q I_a` is constant, but `q (D I_a) ≠ 0` by Lemma 1.2
  have h1 : act q (act S.Dop (ind S.θ a)) = 0 := by
    rw [← act_mul, mul_comm, act_mul, show act q (ind S.θ a) = fun _ => -cc none from
      funext hconst, S.act_Dop_const]
  exact act_ne_zero hqne (S.Dop_finite_support (isLocal_ind S.θ a)) ha h1

/-- The standing hypothesis (1.1) of §§2–7: `D I_a = 0` for every colour `a`. -/
def CaseTwo : Prop := ∀ a : ZMod p, act S.Dop (ind S.θ a) = 0

/-- Consequence of (1.1): `D w(θ) = 0` for every `w : 𝔽_p → ℤ`.  Paper §1.3. -/
theorem Dop_encoding_eq_zero (h11 : S.CaseTwo) (w : ZMod p → ℤ) :
    act S.Dop (fun z => (w (S.θ z) : ℂ)) = 0 := by
  classical
  funext z
  have key : ∀ a : ZMod p, act S.Dop (ind S.θ a) z = 0 := fun a => congrFun (h11 a) z
  set F : Finset (ℤ × ℤ) := S.Dop.coeff.support with hF
  set A : Finset (ZMod p) := F.image fun u => S.θ (z + u) with hA
  have step : ∀ u ∈ F, (w (S.θ (z + u)) : ℂ)
      = ∑ b ∈ A, (w b : ℂ) * ind S.θ b (z + u) := by
    intro u hu
    have hmem : S.θ (z + u) ∈ A := Finset.mem_image_of_mem (fun t => S.θ (z + t)) hu
    rw [Finset.sum_eq_single_of_mem (S.θ (z + u)) hmem
      (fun b _ hb => by rw [ind_eq_zero (Ne.symm hb), mul_zero])]
    rw [ind_self, mul_one]
  simp only [act_apply, Finsupp.sum, Pi.zero_apply]
  calc ∑ u ∈ F, S.Dop.coeff u * (w (S.θ (z + u)) : ℂ)
      = ∑ u ∈ F, ∑ b ∈ A, S.Dop.coeff u * ((w b : ℂ) * ind S.θ b (z + u)) := by
        refine Finset.sum_congr rfl fun u hu => ?_
        rw [step u hu, Finset.mul_sum]
    _ = ∑ b ∈ A, ∑ u ∈ F, S.Dop.coeff u * ((w b : ℂ) * ind S.θ b (z + u)) := Finset.sum_comm
    _ = ∑ b ∈ A, (w b : ℂ) * ∑ u ∈ F, S.Dop.coeff u * ind S.θ b (z + u) := by
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun u _ => by ring
    _ = 0 := by
        refine Finset.sum_eq_zero fun b _ => ?_
        have := key b
        simp only [act_apply, Finsupp.sum] at this
        rw [this, mul_zero]

/-- **Remark 1.4.**  The dichotomy does not depend on the choice of the `H i`: replacing `H i`
by a positive multiple `n i • H i` gives an operator `D'` that is a multiple of `D`, and
`D' I_a = 0` iff `D I_a = 0`. -/
theorem caseTwo_of_multiple (n : Fin m → ℕ) (hn : ∀ i, 0 < n i) (a : ZMod p) :
    act (∏ i, (mono ((n i : ℤ) • S.H i) - 1)) (ind S.θ a) = 0 ↔
      act S.Dop (ind S.θ a) = 0 := by
  classical
  set G : LaurentTwo ℂ := ∏ i, ∑ k ∈ Finset.range (n i), (mono (S.H i) : LaurentTwo ℂ) ^ k
    with hG
  have hfactor : (∏ i, (mono ((n i : ℤ) • S.H i) - 1) : LaurentTwo ℂ) = G * S.Dop := by
    simp only [hG, Dop]
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => by rw [geom_sum_mul, mono_pow]
  have hGne : G ≠ 0 := by
    simp only [hG]
    refine Finset.prod_ne_zero_iff.mpr fun i _ => fun h0 => ?_
    have hx : (mono (S.H i) : LaurentTwo ℂ) ^ n i - 1 = 0 := by
      rw [← geom_sum_mul, h0, zero_mul]
    rw [sub_eq_zero, mono_pow] at hx
    rcases smul_eq_zero.mp (mono_eq_one_iff.mp hx) with h | h
    · exact (hn i).ne' (by exact_mod_cast h)
    · exact S.H_ne_zero i h
  constructor
  · intro h
    rw [hfactor, act_mul] at h
    by_contra hne
    exact act_ne_zero hGne (S.Dop_finite_support (isLocal_ind S.θ a)) hne h
  · intro h
    rw [hfactor, act_mul, h, act_zero_right]

end StarConfig

end Nivat
