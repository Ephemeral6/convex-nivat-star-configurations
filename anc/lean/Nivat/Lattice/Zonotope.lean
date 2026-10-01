/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.Defs.Complexity
import Mathlib.Analysis.Convex.Segment
import Mathlib.Algebra.Group.Pointwise.Set.BigOperators
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Linarith

/-!
# Zonotopes and the reachable set `R_Z(S)`

Formalisation of the zonotope `Z = ∑ᵢ [0, dᵢ vᵢ]` of (2.2) and of the set
`R_Z(S) = {r ∈ ℤ² : r + Z ⊆ Conv(S)}` of §2.6 of *The Convex Nivat Conjecture*
(Pan).

Mathlib has no zonotopes, so they are built here from `segment ℝ 0 x` and pointwise addition
of sets.

## Main definitions

* `Nivat.zonotope` — `Z = ∑ᵢ [0, dᵢ vᵢ] ⊆ ℝ²`.
* `Nivat.RZ` — `R_Z(S) = {r : r + Z ⊆ Conv(S)}`.
* `Nivat.latticePts` — `Z ∩ ℤ²`, as a set of lattice points.

## Main results

* `Nivat.mem_zonotope_iff` — `x ∈ Z ↔ x = ∑ᵢ cᵢ dᵢ vᵢ` with all `cᵢ ∈ [0, 1]`.  This is the
  working description of `Z` used everywhere below.

## Status

Complete; no `sorry`.
-/

namespace Nivat

open scoped Pointwise

variable {m : ℕ}

/-- The segment `[0, d v] ⊆ ℝ²` spanned by a positive multiple of a lattice vector. -/
def latSegment (d : ℕ) (v : ℤ × ℤ) : Set (ℝ × ℝ) :=
  segment ℝ 0 (toReal ((d : ℤ) • v))

/-- The zonotope `Z = ∑ᵢ [0, dᵢ vᵢ]`.  Paper (2.2). -/
def zonotope (d : Fin m → ℕ) (v : Fin m → ℤ × ℤ) : Set (ℝ × ℝ) :=
  ∑ i, latSegment (d i) (v i)

/-- The lattice points of a subset of the plane. -/
def latticePts (Z : Set (ℝ × ℝ)) : Set (ℤ × ℤ) := {z | toReal z ∈ Z}

@[simp] theorem mem_latticePts {Z : Set (ℝ × ℝ)} {z : ℤ × ℤ} :
    z ∈ latticePts Z ↔ toReal z ∈ Z := Iff.rfl

/-- `R_Z(S) = {r ∈ ℤ² : r + Z ⊆ Conv(S)}`.  Paper §2.6. -/
def RZ (Z : Set (ℝ × ℝ)) (S : Finset (ℤ × ℤ)) : Set (ℤ × ℤ) :=
  {r : ℤ × ℤ | ∀ x ∈ Z, toReal r + x ∈ Conv S}

theorem mem_RZ_iff {Z : Set (ℝ × ℝ)} {S : Finset (ℤ × ℤ)} {r : ℤ × ℤ} :
    r ∈ RZ Z S ↔ ∀ x ∈ Z, toReal r + x ∈ Conv S := Iff.rfl

/-! ### Additivity of the embedding `toReal`

These are the arithmetic facts about `Nivat.toReal` needed to move sums of lattice vectors
across the embedding. -/

@[simp] theorem toReal_zero : toReal 0 = 0 := by
  simp [toReal]

theorem toReal_add (z w : ℤ × ℤ) : toReal (z + w) = toReal z + toReal w := by
  simp [toReal]

theorem toReal_sub (z w : ℤ × ℤ) : toReal (z - w) = toReal z - toReal w := by
  simp [toReal]

theorem toReal_sum {ι : Type*} (s : Finset ι) (f : ι → ℤ × ℤ) :
    toReal (∑ i ∈ s, f i) = ∑ i ∈ s, toReal (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, toReal_add, ih]

/-! ### Membership in a zonotope -/

private theorem mem_latSegment_iff {d : ℕ} {v : ℤ × ℤ} {x : ℝ × ℝ} :
    x ∈ latSegment d v ↔ ∃ c : ℝ, 0 ≤ c ∧ c ≤ 1 ∧ c • toReal ((d : ℤ) • v) = x := by
  constructor
  · rintro ⟨a, b, ha, hb, hab, heq⟩
    exact ⟨b, hb, by linarith, by simpa using heq⟩
  · rintro ⟨c, hc0, hc1, rfl⟩
    exact ⟨1 - c, c, by linarith, hc0, by ring, by simp⟩

/-- The working description of the zonotope (2.2): its points are exactly the combinations
`∑ᵢ cᵢ dᵢ vᵢ` with coefficients `cᵢ ∈ [0, 1]`. -/
theorem mem_zonotope_iff {d : Fin m → ℕ} {v : Fin m → ℤ × ℤ} {x : ℝ × ℝ} :
    x ∈ zonotope d v ↔ ∃ c : Fin m → ℝ, (∀ i, c i ∈ Set.Icc (0 : ℝ) 1) ∧
      ∑ i, c i • toReal ((d i : ℤ) • v i) = x := by
  rw [zonotope, Set.mem_fintype_sum]
  constructor
  · rintro ⟨g, hg, rfl⟩
    choose c hc0 hc1 hc2 using fun i => mem_latSegment_iff.1 (hg i)
    exact ⟨c, fun i => Set.mem_Icc.2 ⟨hc0 i, hc1 i⟩, Finset.sum_congr rfl fun i _ => hc2 i⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨fun i => c i • toReal ((d i : ℤ) • v i),
      fun i => mem_latSegment_iff.2 ⟨c i, (hc i).1, (hc i).2, rfl⟩, rfl⟩

/-- Each generator `dᵢ vᵢ` is itself a point of the zonotope. -/
theorem gen_mem_zonotope (d : Fin m → ℕ) (v : Fin m → ℤ × ℤ) (k : Fin m) :
    toReal ((d k : ℤ) • v k) ∈ zonotope d v := by
  classical
  refine mem_zonotope_iff.2 ⟨fun l => if l = k then 1 else 0, fun l => ?_, ?_⟩
  · by_cases h : l = k <;> simp [h]
  · simp

/-- A convex combination of two numbers bounded by `C` in absolute value is again bounded
by `C`. -/
private theorem abs_combo_le {C a b p q : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hp : |p| ≤ C) (hq : |q| ≤ C) : |a * p + b * q| ≤ C := by
  have h1 : a * |p| ≤ a * C := mul_le_mul_of_nonneg_left hp ha
  have h2 : b * |q| ≤ b * C := mul_le_mul_of_nonneg_left hq hb
  calc |a * p + b * q| ≤ |a * p| + |b * q| := abs_add_le _ _
    _ = a * |p| + b * |q| := by
        rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ a * C + b * C := by linarith
    _ = C := by rw [← add_mul, hab, one_mul]

/-- `Conv S` is contained in the box of radius `N` as soon as all points of `S` are. -/
private theorem Conv_subset_box {S : Finset (ℤ × ℤ)} {C : ℝ}
    (h : ∀ z ∈ S, |(z.1 : ℝ)| ≤ C ∧ |(z.2 : ℝ)| ≤ C) :
    Conv S ⊆ {x : ℝ × ℝ | |x.1| ≤ C ∧ |x.2| ≤ C} := by
  refine convexHull_min ?_ ?_
  · rintro x ⟨z, hz, rfl⟩
    exact h z hz
  · intro x hx y hy a b ha hb hab
    refine ⟨?_, ?_⟩
    · simpa using abs_combo_le ha hb hab hx.1 hy.1
    · simpa using abs_combo_le ha hb hab hx.2 hy.2

/-- `R_Z(S)` is finite: it is contained in the lattice points of `Conv S`, since `0 ∈ Z`. -/
theorem RZ_finite (Z : Set (ℝ × ℝ)) (hZ : (0 : ℝ × ℝ) ∈ Z) (S : Finset (ℤ × ℤ)) :
    (RZ Z S).Finite := by
  classical
  set N : ℕ := S.sup fun z => max z.1.natAbs z.2.natAbs with hN
  have hbox : Conv S ⊆ {x : ℝ × ℝ | |x.1| ≤ (N : ℝ) ∧ |x.2| ≤ (N : ℝ)} := by
    refine Conv_subset_box fun z hz => ?_
    have hle := Finset.le_sup (f := fun z : ℤ × ℤ => max z.1.natAbs z.2.natAbs) hz
    rw [← hN] at hle
    constructor
    · have : (z.1.natAbs : ℝ) ≤ (N : ℝ) :=
        Nat.cast_le.2 (le_trans (le_max_left _ _) hle)
      simpa [Nat.cast_natAbs] using this
    · have : (z.2.natAbs : ℝ) ≤ (N : ℝ) :=
        Nat.cast_le.2 (le_trans (le_max_right _ _) hle)
      simpa [Nat.cast_natAbs] using this
  have hsub : RZ Z S ⊆ Set.Icc (-(N : ℤ)) (N : ℤ) ×ˢ Set.Icc (-(N : ℤ)) (N : ℤ) := by
    intro r hr
    have h0 : toReal r ∈ Conv S := by simpa using hr (0 : ℝ × ℝ) hZ
    obtain ⟨h1, h2⟩ := hbox h0
    rw [show (toReal r).1 = (r.1 : ℝ) from rfl] at h1
    rw [show (toReal r).2 = (r.2 : ℝ) from rfl] at h2
    rw [abs_le] at h1 h2
    refine ⟨Set.mem_Icc.2 ⟨?_, ?_⟩, Set.mem_Icc.2 ⟨?_, ?_⟩⟩
    · exact_mod_cast h1.1
    · exact_mod_cast h1.2
    · exact_mod_cast h2.1
    · exact_mod_cast h2.2
  exact Set.Finite.subset ((Set.finite_Icc _ _).prod (Set.finite_Icc _ _)) hsub

theorem zero_mem_zonotope (d : Fin m → ℕ) (v : Fin m → ℤ × ℤ) :
    (0 : ℝ × ℝ) ∈ zonotope d v := by
  refine mem_zonotope_iff.2 ⟨fun _ => 0, fun i => Set.mem_Icc.2 ⟨le_rfl, zero_le_one⟩, ?_⟩
  simp

theorem zonotope_convex (d : Fin m → ℕ) (v : Fin m → ℤ × ℤ) :
    Convex ℝ (zonotope d v) := by
  rw [zonotope]
  apply convex_sum
  intro i _
  exact convex_segment _ _

/-- **Remark 2.6.**  For lattice-convex `S`, a point of `R_Z(S)` translated by a lattice point
of `Z` lands in `S`. -/
theorem mem_of_mem_RZ {Z : Set (ℝ × ℝ)} {S : Finset (ℤ × ℤ)} (hS : LatticeConvex S)
    {r : ℤ × ℤ} (hr : r ∈ RZ Z S) {q : ℤ × ℤ} (hq : q ∈ latticePts Z) : r + q ∈ S := by
  refine hS (r + q) ?_
  rw [toReal_add]
  exact hr _ hq

/-- The zonotope is two-dimensional once two of its generating directions are non-parallel.
Paper Remark 2.6 ("`Z` has non-empty interior since `m ≥ 2` and `v₁ ∦ v₂`"). -/
theorem zonotope_two_dim {d : Fin m → ℕ} {v : Fin m → ℤ × ℤ}
    (hd : ∀ i, 0 < d i) {i j : Fin m} (hij : det (v i) (v j) ≠ 0) :
    ∃ x y : ℝ × ℝ, x ∈ zonotope d v ∧ y ∈ zonotope d v ∧ x.1 * y.2 - x.2 * y.1 ≠ 0 := by
  refine ⟨_, _, gen_mem_zonotope d v i, gen_mem_zonotope d v j, ?_⟩
  have hcast : (toReal ((d i : ℤ) • v i)).1 * (toReal ((d j : ℤ) • v j)).2
      - (toReal ((d i : ℤ) • v i)).2 * (toReal ((d j : ℤ) • v j)).1
      = (((d i : ℤ) * (d j : ℤ) * det (v i) (v j) : ℤ) : ℝ) := by
    simp only [toReal, det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    push_cast
    ring
  rw [hcast, ne_eq, Int.cast_eq_zero]
  refine mul_ne_zero (mul_ne_zero ?_ ?_) hij
  · exact_mod_cast (hd i).ne'
  · exact_mod_cast (hd j).ne'

end Nivat
