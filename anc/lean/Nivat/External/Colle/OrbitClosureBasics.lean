/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.Section8.External
import Nivat.External.Colle.HalfPlanePeriodicity

/-!
# Basic properties of orbit closures

Elementary facts about orbit closures, periods, and ONED monotonicity.
Extracted from `Theorem114.lean` to break the dependency cycle.
-/

namespace Nivat.Colle

variable {α : Type*}

/-- The orbit closure is transitive: `X_y ⊆ X_ξ` whenever `y ∈ X_ξ`. -/
theorem mem_orbitClosure_trans {ξ y x : Config α}
    (hy : y ∈ orbitClosure ξ) (hx : x ∈ orbitClosure y) : x ∈ orbitClosure ξ := by
  classical
  intro W
  obtain ⟨a, ha⟩ := hx W
  obtain ⟨b, hb⟩ := hy (W.image fun w => a + w)
  refine ⟨b + a, fun w hw => ?_⟩
  have hmem : a + w ∈ W.image fun w => a + w := Finset.mem_image.mpr ⟨w, hw, rfl⟩
  rw [ha w hw, hb _ hmem, add_assoc]

/-- `orbitClosure` is monotone: `y ∈ X_ξ → X_y ⊆ X_ξ`. -/
theorem orbitClosure_subset_of_mem {ξ y : Config α} (hy : y ∈ orbitClosure ξ) :
    orbitClosure y ⊆ orbitClosure ξ := fun _ hx => mem_orbitClosure_trans hy hx

/-- `ONED(y) ⊆ ONED(η)` for every `y` in the orbit closure of `η`. -/
theorem ONED_subset_of_mem_orbitClosure {ξ y : Config α} (hy : y ∈ orbitClosure ξ) :
    ONED y ⊆ ONED ξ := by
  rintro w ⟨hw, x, hx, x', hx', hne, hagree⟩
  exact ⟨hw, x, mem_orbitClosure_trans hy hx, x', mem_orbitClosure_trans hy hx', hne, hagree⟩

/-- Every period of `ξ` is a period of every element of its orbit closure. -/
theorem mem_Per_of_mem_orbitClosure {ξ x : Config α} {u : ℤ × ℤ}
    (hu : u ∈ Per ξ) (hx : x ∈ orbitClosure ξ) : u ∈ Per x := by
  classical
  rw [mem_Per_iff]
  funext z
  show x (z + u) = x z
  obtain ⟨a, ha⟩ := hx {z + u, z}
  have h1 : x (z + u) = ξ (a + (z + u)) := ha _ (by simp)
  have h2 : x z = ξ (a + z) := ha _ (by simp)
  rw [h1, h2, show a + (z + u) = (a + z) + u by abel]
  exact Per.apply hu (a + z)

/-- Half-plane agreement with transverse period implies equality. -/
theorem eq_of_agree_sideOf_of_mem_Per {x y : Config α} {w : ℝ × ℝ} {p : ℤ × ℤ}
    (hpx : p ∈ Per x) (hpy : p ∈ Per y) (hp : inner2 w p < 0)
    (hagree : ∀ z ∈ sideOf w, x z = y z) : x = y := by
  funext z
  obtain ⟨N, hN⟩ := exists_nat_gt (inner2 w z / (-inner2 w p))
  have hpos : (0 : ℝ) < -inner2 w p := by linarith
  have hlt : inner2 w z < (N : ℝ) * -inner2 w p := (div_lt_iff₀ hpos).mp hN
  rw [mul_neg] at hlt
  have hmem : z + (N : ℤ) • p ∈ sideOf w := by
    show inner2 w (z + (N : ℤ) • p) ≤ 0
    rw [inner2_add, inner2_zsmul]
    push_cast
    linarith
  have hx := Per.apply (AddSubgroup.zsmul_mem (Per x) hpx (N : ℤ)) z
  have hy := Per.apply (AddSubgroup.zsmul_mem (Per y) hpy (N : ℤ)) z
  rw [← hx, ← hy]
  exact hagree _ hmem

/-- The hypothesis of Theorem 1.14 passes to the orbit closure. -/
theorem hONED_of_mem_orbitClosure {ξ y : Config α} (hy : y ∈ orbitClosure ξ)
    (hONED : ∀ w : ℝ × ℝ, w ≠ 0 → ¬ (w ∈ ONED ξ ∧ -w ∈ ONED ξ)) :
    ∀ w : ℝ × ℝ, w ≠ 0 → ¬ (w ∈ ONED y ∧ -w ∈ ONED y) := by
  intro w hw hmem
  exact hONED w hw ⟨ONED_subset_of_mem_orbitClosure hy hmem.1,
    ONED_subset_of_mem_orbitClosure hy hmem.2⟩

end Nivat.Colle
