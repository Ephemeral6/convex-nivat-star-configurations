/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.Defs.Config
import Mathlib.Analysis.Convex.Hull
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card

/-!
# Pattern complexity and lattice convexity

Formalisation of §0.2 of *The Convex Nivat Conjecture* (Pan).

For a finite window `Q ⊂ ℤ²` the paper writes `θ|_{u+Q}` for the function `q ↦ θ (u + q)` and
`P_θ(Q)` for the number of distinct such patterns.  A finite `S ⊂ ℤ²` is *lattice-convex* if
`S = Conv(S) ∩ ℤ²`.

## Main definitions

* `Nivat.patterns` — the set of patterns of `θ` on a window.
* `Nivat.P` — the pattern complexity `P_θ(Q)`.
* `Nivat.Conv` — the convex hull in `ℝ²` of a set of lattice points.
* `Nivat.LatticeConvex` — `S = Conv(S) ∩ ℤ²`.

## Status

Complete; no `sorry`.
-/

namespace Nivat

open scoped Convex

variable {α : Type*}

/-- The pattern of `θ` in the window `Q` anchored at `u`: the function `q ↦ θ (u + q)`.
Paper §0.2 writes this `θ|_{u+Q}`. -/
def pattern (θ : Config α) (Q : Finset (ℤ × ℤ)) (u : ℤ × ℤ) : Q → α :=
  fun q => θ (u + (q : ℤ × ℤ))

/-- The set of all patterns of `θ` in the window `Q`. -/
def patterns (θ : Config α) (Q : Finset (ℤ × ℤ)) : Set (Q → α) :=
  Set.range (pattern θ Q)

/-- The pattern complexity `P_θ(Q) = #{θ|_{u+Q} : u ∈ ℤ²}`.  Paper §0.2. -/
noncomputable def P (θ : Config α) (Q : Finset (ℤ × ℤ)) : ℕ :=
  (patterns θ Q).ncard

/-- Over a finite alphabet there are only finitely many patterns in a finite window. -/
theorem patterns_finite [Finite α] (θ : Config α) (Q : Finset (ℤ × ℤ)) :
    (patterns θ Q).Finite := Set.toFinite _

/-- A configuration of finite range has finitely many patterns in a finite window, even if its
alphabet is infinite.  This is the form needed in §8, where the configuration takes finitely
many values inside `ℤ`. -/
theorem patterns_finite_of_range_finite {θ : Config α} (h : (Set.range θ).Finite)
    (Q : Finset (ℤ × ℤ)) : (patterns θ Q).Finite := by
  have hsub : patterns θ Q ⊆ Set.pi Set.univ fun _ : Q => Set.range θ := by
    rintro _ ⟨u, rfl⟩ q -
    exact Set.mem_range_self _
  exact (Set.Finite.pi fun _ => h).subset hsub

/-- `P_θ(∅) = 1`: the empty window carries exactly one pattern.  Paper §D.1. -/
theorem P_empty (θ : Config α) : P θ ∅ = 1 := by
  have h : patterns θ ∅ = {pattern θ ∅ 0} := by
    refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨0, rfl⟩, ?_⟩
    rintro x ⟨u, rfl⟩
    funext q
    exact absurd q.2 (Finset.notMem_empty _)
  rw [P, h, Set.ncard_singleton]

/-- Complexity is monotone in the window: restriction maps patterns onto patterns. -/
theorem P_mono [Finite α] {θ : Config α} {Q Q' : Finset (ℤ × ℤ)} (h : Q ⊆ Q') :
    P θ Q ≤ P θ Q' := by
  have himg : patterns θ Q =
      (fun g : Q' → α => fun q : Q => g ⟨(q : ℤ × ℤ), h q.2⟩) '' patterns θ Q' := by
    ext x
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨pattern θ Q' u, ⟨u, rfl⟩, rfl⟩
    · rintro ⟨g, ⟨u, rfl⟩, rfl⟩
      exact ⟨u, rfl⟩
  rw [P, P, himg]
  exact Set.ncard_image_le (patterns_finite θ Q')

/-- The embedding of the integer lattice into the real plane. -/
def toReal (z : ℤ × ℤ) : ℝ × ℝ := ((z.1 : ℝ), (z.2 : ℝ))

theorem toReal_injective : Function.Injective toReal := by
  intro z w h
  have h1 : (z.1 : ℝ) = (w.1 : ℝ) := congrArg Prod.fst h
  have h2 : (z.2 : ℝ) = (w.2 : ℝ) := congrArg Prod.snd h
  exact Prod.ext (by exact_mod_cast h1) (by exact_mod_cast h2)

/-- `Conv S` is the convex hull in `ℝ²` of the lattice set `S`.  Paper §0.2. -/
def Conv (S : Finset (ℤ × ℤ)) : Set (ℝ × ℝ) := convexHull ℝ (toReal '' (S : Set (ℤ × ℤ)))

theorem subset_Conv {S : Finset (ℤ × ℤ)} {z : ℤ × ℤ} (hz : z ∈ S) : toReal z ∈ Conv S :=
  subset_convexHull ℝ _ ⟨z, hz, rfl⟩

/-- A finite set of lattice points is *lattice-convex* if it contains every lattice point of
its own convex hull, i.e. `S = Conv(S) ∩ ℤ²`.  Paper §0.2.

Only this inclusion is stated: the reverse one, `S ⊆ Conv(S) ∩ ℤ²`, is `subset_Conv` and
holds always. -/
def LatticeConvex (S : Finset (ℤ × ℤ)) : Prop :=
  ∀ z : ℤ × ℤ, toReal z ∈ Conv S → z ∈ S

/-- For a lattice-convex `S`, membership in `S` is exactly membership in `Conv S`. -/
theorem LatticeConvex.mem_iff {S : Finset (ℤ × ℤ)} (hS : LatticeConvex S) (z : ℤ × ℤ) :
    z ∈ S ↔ toReal z ∈ Conv S :=
  ⟨subset_Conv, hS z⟩

/-- `θ` has *low convex complexity* if `P_θ(S) ≤ |S|` for some non-empty finite lattice-convex
window `S`.  Paper §8, Remark 8.3, Corollary D.2. -/
def LowConvexComplexity (θ : Config α) : Prop :=
  ∃ S : Finset (ℤ × ℤ), S.Nonempty ∧ LatticeConvex S ∧ P θ S ≤ S.card

end Nivat
