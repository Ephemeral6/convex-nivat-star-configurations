import Nivat.External.Colle.LatticeEdges
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.SpecificLimits.Basic

/-! Counterexample to the un-finite-ified `isLatticeConvexRegion_iUnion_of_mono_fixedEdges`
(dropped `hfin`; the surviving, `hfin`-carrying statement is
`Nivat.LE2.isLatticeConvexRegion_iUnion_of_mono_fixedEdges_finite`, `LatticeEdges.lean:709`):
cones `T i = ℤ² ∩ {y ≥ α_i |x|}`, `α_i = 1 + √2/(i+1)`, `S = ∅` — every `T i` is infinite.
Every `E (T i)` is empty (irrationality of `α_i`), so `hedge` is vacuous; the union misses
`(1,1)`, which every closed convex superset contains. -/

namespace Nivat.LE2.ConeCounterexample

open Nivat Nivat.LE2 Filter Topology

noncomputable section

def α (i : ℕ) : ℝ := 1 + Real.sqrt 2 / ((i : ℝ) + 1)

theorem sqrt2_lt_two : Real.sqrt 2 < 2 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have h0 := Real.sqrt_nonneg 2
  nlinarith

theorem α_gt_one (i : ℕ) : 1 < α i := by
  unfold α
  have : 0 < Real.sqrt 2 / ((i : ℝ) + 1) :=
    div_pos (Real.sqrt_pos.mpr (by norm_num)) (by positivity)
  linarith

theorem α_lt_three (i : ℕ) : α i < 3 := by
  unfold α
  have h1 : Real.sqrt 2 / ((i : ℝ) + 1) ≤ Real.sqrt 2 :=
    div_le_self (Real.sqrt_nonneg 2) (by linarith [Nat.cast_nonneg (α := ℝ) i])
  linarith [sqrt2_lt_two]

theorem α_anti {i j : ℕ} (hij : i ≤ j) : α j ≤ α i := by
  unfold α
  have hij' : (i : ℝ) ≤ j := by exact_mod_cast hij
  have := div_le_div_of_nonneg_left (Real.sqrt_nonneg 2)
    (by positivity : (0 : ℝ) < (i : ℝ) + 1) (by linarith : (i : ℝ) + 1 ≤ (j : ℝ) + 1)
  linarith

/-- `α i` is not a rational number `a / b`. -/
theorem α_ne_rat (i : ℕ) (a b : ℤ) (hb : b ≠ 0) : α i ≠ (a : ℝ) / b := by
  intro h
  have hi : ((i : ℝ) + 1) ≠ 0 := by positivity
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb
  apply irrational_sqrt_two.ne_rational ((a - b) * ((i : ℤ) + 1)) b
  have h1 : Real.sqrt 2 / ((i : ℝ) + 1) = (a : ℝ) / b - 1 := by unfold α at h; linarith
  have h2 : Real.sqrt 2 = ((a : ℝ) / b - 1) * ((i : ℝ) + 1) := (div_eq_iff hi).mp h1
  have h3 : ((a : ℝ) / b - 1) * b = a - b := by
    rw [sub_mul, div_mul_cancel₀ (a : ℝ) hbR, one_mul]
  rw [eq_div_iff hbR, h2]
  push_cast
  calc ((a : ℝ) / b - 1) * ((i : ℝ) + 1) * b
      = (((a : ℝ) / b - 1) * b) * ((i : ℝ) + 1) := by ring
    _ = ((a : ℝ) - b) * ((i : ℝ) + 1) := by rw [h3]

/-! ## The cones -/

def Cset (i : ℕ) : Set (ℝ × ℝ) := {p | α i * |p.1| ≤ p.2}

def Tset (i : ℕ) : Set (ℤ × ℤ) := toReal ⁻¹' Cset i

theorem mem_Tset {i : ℕ} {z : ℤ × ℤ} :
    z ∈ Tset i ↔ α i * |(z.1 : ℝ)| ≤ (z.2 : ℝ) := Iff.rfl

theorem Tset_mono : ∀ i j, i ≤ j → Tset i ⊆ Tset j := by
  intro i j hij z hz
  rw [mem_Tset] at hz ⊢
  have h := α_anti hij
  have h0 : (0 : ℝ) ≤ |(z.1 : ℝ)| := abs_nonneg _
  nlinarith [mul_le_mul_of_nonneg_right h h0]

theorem Cset_convex (i : ℕ) : Convex ℝ (Cset i) := by
  intro p hp q hq a b ha hb hab
  have hp' : α i * |p.1| ≤ p.2 := hp
  have hq' : α i * |q.1| ≤ q.2 := hq
  show α i * |(a • p + b • q).1| ≤ (a • p + b • q).2
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  have h1 : |a * p.1 + b * q.1| ≤ a * |p.1| + b * |q.1| := by
    calc |a * p.1 + b * q.1| ≤ |a * p.1| + |b * q.1| := abs_add_le _ _
      _ = a * |p.1| + b * |q.1| := by
        rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
  have hα : 0 ≤ α i := by linarith [α_gt_one i]
  nlinarith [mul_le_mul_of_nonneg_left h1 hα, mul_le_mul_of_nonneg_left hp' ha,
    mul_le_mul_of_nonneg_left hq' hb]

theorem Cset_closed (i : ℕ) : IsClosed (Cset i) :=
  isClosed_le (by fun_prop) continuous_snd

theorem Tset_conv (i : ℕ) : IsLatticeConvexRegion (Tset i) :=
  ⟨Cset i, Cset_convex i, Cset_closed i, rfl⟩

/-! ## `E (Tset i) = ∅` -/

theorem zero_mem (i : ℕ) : ((0 : ℤ), (0 : ℤ)) ∈ Tset i := by
  rw [mem_Tset]; simp

theorem double_mem {i : ℕ} {z : ℤ × ℤ} (hz : z ∈ Tset i) : z + z ∈ Tset i := by
  rw [mem_Tset] at hz ⊢
  simp only [Prod.fst_add, Prod.snd_add, Int.cast_add]
  rw [← two_mul, ← two_mul, abs_mul, abs_two]
  linarith

/-- Every point of a face has pairing `0`: squeeze between the origin and the double. -/
theorem dot_eq_zero_of_mem_face {i : ℕ} {n x : ℤ × ℤ} (hx : x ∈ face (Tset i) n) :
    dot n x = 0 := by
  have h0 := hx.2 _ (zero_mem i)
  have h2 := hx.2 _ (double_mem hx.1)
  rw [dot_add] at h2
  have : dot n ((0 : ℤ), (0 : ℤ)) = 0 := by simp [dot]
  omega

theorem E_Tset (i : ℕ) : E (Tset i) = ∅ := by
  ext n
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨hprim, x, hx, y, hy, hxy⟩
  have hα1 := α_gt_one i
  have hα3 := α_lt_three i
  obtain ⟨w, hw, hw0⟩ : ∃ w ∈ face (Tset i) n, w ≠ 0 := by
    by_cases hx0 : x = 0
    · exact ⟨y, hy, fun h => hxy (hx0.trans h.symm)⟩
    · exact ⟨x, hx, hx0⟩
  have hmax : ∀ t ∈ Tset i, dot n t ≤ 0 := fun t ht => by
    have := hw.2 t ht
    rwa [dot_eq_zero_of_mem_face hw] at this
  have hw_dot : dot n w = 0 := dot_eq_zero_of_mem_face hw
  have hwR : α i * |(w.1 : ℝ)| ≤ (w.2 : ℝ) := hw.1
  -- `n.2 ≤ 0` from the test point `w + (0,1)`
  have hb : n.2 ≤ 0 := by
    have hmem : w + ((0 : ℤ), (1 : ℤ)) ∈ Tset i := by
      rw [mem_Tset]
      simp only [Prod.fst_add, Prod.snd_add, add_zero, Int.cast_add, Int.cast_one]
      linarith
    have h1 := hmax _ hmem
    rw [dot_add] at h1
    have h2 : dot n ((0 : ℤ), (1 : ℤ)) = n.2 := by simp [dot]
    omega
  rcases eq_or_ne w.1 0 with hw1 | hw1
  · -- `w = (0, w.2)`, `w.2 > 0` ⇒ `n.2 = 0` ⇒ `n.1 ≠ 0`; test point `(n.1, 3|n.1|)`
    have hw2 : 0 < w.2 := by
      have hne : w.2 ≠ 0 := fun h => hw0 (Prod.ext hw1 h)
      have hR : (0 : ℝ) ≤ (w.2 : ℝ) := by
        have := hwR; rw [hw1] at this; simpa using this
      have : (0 : ℤ) ≤ w.2 := by exact_mod_cast hR
      omega
    have hn2 : n.2 = 0 := by
      have : n.1 * w.1 + n.2 * w.2 = 0 := hw_dot
      rw [hw1, mul_zero, zero_add] at this
      rcases mul_eq_zero.mp this with h | h
      · exact h
      · omega
    have hn1 : n.1 ≠ 0 := fun h => hprim.ne_zero (Prod.ext h hn2)
    have hmem : (n.1, 3 * |n.1|) ∈ Tset i := by
      show α i * |(n.1 : ℝ)| ≤ ((3 * |n.1| : ℤ) : ℝ)
      push_cast
      have : (0 : ℝ) ≤ |(n.1 : ℝ)| := abs_nonneg _
      nlinarith
    have h1 := hmax _ hmem
    have h2 : dot n (n.1, 3 * |n.1|) = n.1 * n.1 := by simp [dot, hn2]
    have h3 : 0 < n.1 * n.1 := mul_self_pos.mpr hn1
    omega
  · -- `w.1 ≠ 0`
    have hw1R : (0 : ℝ) < |(w.1 : ℝ)| := abs_pos.mpr (by exact_mod_cast hw1)
    have hb' : n.2 < 0 := by
      rcases lt_or_eq_of_le hb with h | h
      · exact h
      · exfalso
        have : n.1 * w.1 + n.2 * w.2 = 0 := hw_dot
        rw [h, zero_mul, add_zero] at this
        rcases mul_eq_zero.mp this with h1 | h1
        · exact hprim.ne_zero (Prod.ext h1 h)
        · exact hw1 h1
    set c : ℤ := -n.2 with hc
    have hcpos : 0 < c := by omega
    have hcR : (0 : ℝ) < c := by exact_mod_cast hcpos
    have h1 : (n.1 : ℝ) * w.1 = c * w.2 := by
      have : n.1 * w.1 = c * w.2 := by
        have := hw_dot; simp only [dot] at this; rw [hc]; linear_combination this
      exact_mod_cast this
    -- `c α ≤ |n.1|`
    have hkey : (c : ℝ) * α i ≤ |(n.1 : ℝ)| := by
      have h2 : (n.1 : ℝ) * w.1 ≤ |(n.1 : ℝ)| * |(w.1 : ℝ)| := by
        rw [← abs_mul]; exact le_abs_self _
      have h3 : (c : ℝ) * (α i * |(w.1 : ℝ)|) ≤ c * w.2 :=
        mul_le_mul_of_nonneg_left hwR hcR.le
      have h4 : (c : ℝ) * α i * |(w.1 : ℝ)| ≤ |(n.1 : ℝ)| * |(w.1 : ℝ)| := by
        rw [mul_assoc]; linarith
      exact le_of_mul_le_mul_right h4 hw1R
    -- irrationality excludes equality
    have hne : (c : ℝ) * α i ≠ |(n.1 : ℝ)| := by
      intro h
      apply α_ne_rat i |n.1| c hcpos.ne'
      rw [eq_div_iff hcR.ne']
      push_cast
      linarith
    have hgap : (0 : ℝ) < |(n.1 : ℝ)| - c * α i := by
      have := lt_of_le_of_ne hkey hne; linarith
    obtain ⟨k, hk⟩ := exists_nat_gt ((c : ℝ) / (|(n.1 : ℝ)| - c * α i))
    have hk' : (c : ℝ) < k * (|(n.1 : ℝ)| - c * α i) := (div_lt_iff₀ hgap).mp hk
    set m : ℤ := ⌈α i * k⌉ with hm
    have hm1 : α i * k ≤ (m : ℝ) := Int.le_ceil _
    have hm2 : (m : ℝ) < α i * k + 1 := Int.ceil_lt_add_one _
    set s : ℤ := if 0 ≤ n.1 then 1 else -1 with hs
    have hs_abs : n.1 * s = |n.1| := by
      rw [hs]; split_ifs with h
      · rw [mul_one, abs_of_nonneg h]
      · rw [mul_neg_one, abs_of_neg (lt_of_not_ge h)]
    have hs1 : |s| = 1 := by rw [hs]; split_ifs <;> simp
    -- test point `(s k, ⌈α k⌉)`
    have hmem : (s * (k : ℤ), m) ∈ Tset i := by
      show α i * |((s * (k : ℤ) : ℤ) : ℝ)| ≤ (m : ℝ)
      push_cast
      rw [abs_mul]
      have hsk : |(s : ℝ)| = 1 := by rw [← Int.cast_abs, hs1]; simp
      have hkR : |(k : ℝ)| = k := abs_of_nonneg (Nat.cast_nonneg k)
      rw [hsk, hkR, one_mul]
      exact hm1
    have h5 := hmax _ hmem
    have h6 : dot n (s * (k : ℤ), m) = n.1 * (s * k) + n.2 * m := rfl
    rw [h6] at h5
    have h5R : (n.1 : ℝ) * (s * k) + n.2 * m ≤ 0 := by exact_mod_cast h5
    have e1 : (n.1 : ℝ) * (s * k) = |(n.1 : ℝ)| * k := by
      rw [← mul_assoc]
      have : ((n.1 * s : ℤ) : ℝ) = |(n.1 : ℝ)| := by rw [hs_abs, Int.cast_abs]
      push_cast at this
      rw [this]
    have e2 : (n.2 : ℝ) = -c := by rw [hc]; push_cast; ring
    rw [e1, e2] at h5R
    have h7 : (c : ℝ) * m < c * (α i * k + 1) := mul_lt_mul_of_pos_left hm2 hcR
    nlinarith

theorem E_empty : E (∅ : Set (ℤ × ℤ)) = ∅ := by
  ext n
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨-, x, hx, -, -, -⟩
  exact hx.1

/-! ## The union is not lattice-convex -/

theorem diag_mem (n : ℕ) : (((n : ℕ) : ℤ), ((n : ℕ) : ℤ) + 1) ∈ Tset (2 * n) := by
  show α (2 * n) * |(((n : ℕ) : ℤ) : ℝ)| ≤ ((((n : ℕ) : ℤ) + 1 : ℤ) : ℝ)
  push_cast
  rw [abs_of_nonneg (Nat.cast_nonneg n)]
  unfold α
  push_cast
  have hpos : (0 : ℝ) < 2 * (n : ℝ) + 1 := by positivity
  have h1 : Real.sqrt 2 / (2 * (n : ℝ) + 1) * n ≤ 1 := by
    rw [div_mul_eq_mul_div, div_le_one hpos]
    nlinarith [Real.sqrt_nonneg 2, sqrt2_lt_two, Nat.cast_nonneg (α := ℝ) n]
  nlinarith

theorem not_isLatticeConvexRegion_iUnion_Tset : ¬ IsLatticeConvexRegion (⋃ i, Tset i) := by
  rintro ⟨C, hCconv, hCclosed, hTeq⟩
  have hmemC : ∀ z : ℤ × ℤ, (∃ i, z ∈ Tset i) → toReal z ∈ C := by
    intro z hz
    have : z ∈ ⋃ i, Tset i := Set.mem_iUnion.mpr hz
    rwa [hTeq] at this
  have h0 : toReal ((0 : ℤ), (0 : ℤ)) ∈ C := hmemC _ ⟨0, zero_mem 0⟩
  -- `(1, 1 + 1/(n+1)) ∈ C`: convex combination of the origin and `(n+1, n+2)`
  have hw : ∀ n : ℕ, (((1 : ℝ), 1 + 1 / ((n : ℝ) + 1)) : ℝ × ℝ) ∈ C := by
    intro n
    have hA := hmemC _ ⟨_, diag_mem (n + 1)⟩
    have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    set t : ℝ := 1 / ((n : ℝ) + 1) with ht
    have ht0 : 0 ≤ t := by positivity
    have ht1 : t ≤ 1 := by rw [ht, div_le_one hn1]; linarith [Nat.cast_nonneg (α := ℝ) n]
    have htn : t * ((n : ℝ) + 1) = 1 := by rw [ht]; field_simp
    have hcomb := hCconv h0 hA (by linarith : (0 : ℝ) ≤ 1 - t) ht0 (by ring)
    have heq : (1 - t) • toReal ((0 : ℤ), (0 : ℤ))
        + t • toReal (((n + 1 : ℕ) : ℤ), ((n + 1 : ℕ) : ℤ) + 1) = ((1 : ℝ), 1 + t) := by
      simp only [toReal, Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk]
      push_cast
      refine Prod.ext ?_ ?_
      · show (1 - t) * 0 + t * ((n : ℝ) + 1) = 1
        rw [htn]; ring
      · show (1 - t) * 0 + t * ((n : ℝ) + 1 + 1) = 1 + t
        linear_combination htn
    rw [heq] at hcomb
    exact hcomb
  have hlim : Tendsto (fun n : ℕ => (((1 : ℝ), 1 + 1 / ((n : ℝ) + 1)) : ℝ × ℝ)) atTop
      (𝓝 (((1 : ℝ), (1 : ℝ)) : ℝ × ℝ)) := by
    refine Tendsto.prodMk_nhds tendsto_const_nhds ?_
    have := (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop (α := ℕ))).add
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa using this
  have h11 : (((1 : ℝ), (1 : ℝ)) : ℝ × ℝ) ∈ C :=
    hCclosed.mem_of_tendsto hlim (Eventually.of_forall hw)
  have h11' : ((1 : ℤ), (1 : ℤ)) ∈ ⋃ i, Tset i := by
    rw [hTeq]
    show toReal ((1 : ℤ), (1 : ℤ)) ∈ C
    simpa [toReal] using h11
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp h11'
  have hi' : α i * |((1 : ℤ) : ℝ)| ≤ ((1 : ℤ) : ℝ) := hi
  simp only [Int.cast_one, abs_one, mul_one] at hi'
  linarith [α_gt_one i]

/-- **`LatticeEdges.lean:698` is false.** -/
theorem not_iUnion_of_mono_fixedEdges :
    ¬ ∀ (T : ℕ → Set (ℤ × ℤ)) (S : Set (ℤ × ℤ)),
      (∀ i j, i ≤ j → T i ⊆ T j) → (∀ i, IsLatticeConvexRegion (T i)) →
      (∀ i, E (T i) = E S) → IsLatticeConvexRegion (⋃ i, T i) :=
  fun h => not_isLatticeConvexRegion_iUnion_Tset
    (h Tset ∅ Tset_mono Tset_conv (fun i => by rw [E_Tset, E_empty]))

/-- Strengthening `hedge` to `Enveloped S (T i)` does not help: the same family is
`E(∅)`-enveloped. -/
theorem enveloped_empty_Tset (i : ℕ) : Enveloped (∅ : Set (ℤ × ℤ)) (Tset i) :=
  ⟨⟨Tset_conv i, fun n hn => by rw [E_Tset] at hn; exact hn.elim⟩, by rw [E_Tset, E_empty]⟩

end

end Nivat.LE2.ConeCounterexample
