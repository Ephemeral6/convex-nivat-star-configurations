import Nivat.External.Colle.LowComplexityWindow
import Nivat.External.Colle.GeneratingPatterns

/-!
# Colle Lemma 2.4: low complexity supplies a generating set

Finite descent yields a window with strict complexity deficit. Deleting
a vertex preserves convexity by Colle's definition; monotonicity forces equality
of the two pattern counts. Deleting a supporting face gives the required
boundary deficit, for real normals including irrational ones.
-/

namespace Nivat.Colle

/-- A low-convex-complexity configuration of finite range has a generating
set with strict deficit against every proper convex subwindow. -/
theorem exists_generatingSet_with_strict_deficit {A : Type*} {ξ : Config A}
    (hfin : (Set.range ξ).Finite) (hlow : LowConvexComplexity ξ) :
    ∃ S : Finset (ℤ × ℤ), IsGeneratingSet ξ S ∧ P ξ S ≤ S.card ∧
      ∀ U : Finset (ℤ × ℤ), U ⊂ S → LatticeConvex U →
        P ξ S < P ξ U + (S.card - U.card) := by
  obtain ⟨F, hFne, hFc, hFlow⟩ := hlow
  obtain ⟨S, _, hSne, hSc, hSlow, hdef⟩ :=
    exists_window_with_strict_deficit ξ F hFne hFc hFlow
  refine ⟨S, ⟨hSne, hSc, ?_⟩, hSlow, hdef⟩
  intro a haS hdel
  apply generatesAt_of_P_eq hfin haS
  have hstrict := hdef (S.erase a) (Finset.erase_ssubset haS) hdel
  have hcard := Finset.card_erase_of_mem haS
  have hmono := P_mono_of_range_finite hfin (Finset.erase_subset a S)
  have hpos : 0 < S.card := Finset.card_pos.mpr hSne
  omega

/-- Strict deficit for convex subwindows gives the exact boundary budget
used in Colle Lemma 2.4 at any nonempty supporting face. -/
theorem support_face_deficit_of_strict_deficit {A : Type*} {ξ : Config A}
    {S : Finset (ℤ × ℤ)} (hSc : LatticeConvex S)
    (hdef : ∀ U : Finset (ℤ × ℤ), U ⊂ S → LatticeConvex U →
      P ξ S < P ξ U + (S.card - U.card))
    (w : ℝ × ℝ) (c : ℝ) (hmax : ∀ z ∈ S, inner2 w z ≤ c)
    (hface : (S.filter fun z => inner2 w z = c).Nonempty) :
    P ξ S - P ξ (S.filter fun z => inner2 w z < c) ≤
      (S.filter fun z => inner2 w z = c).card - 1 := by
  classical
  let U := S.filter fun z => inner2 w z < c
  let E := S.filter fun z => inner2 w z = c
  have hUS : U ⊆ S := Finset.filter_subset _ _
  have hproper : U ⊂ S := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨hUS, ?_⟩
    intro heq
    obtain ⟨a, ha⟩ := hface
    have haS : a ∈ S := (Finset.mem_filter.mp ha).1
    have haU : a ∈ U := heq ▸ haS
    have hlt := (Finset.mem_filter.mp haU).2
    have he := (Finset.mem_filter.mp ha).2
    exact (ne_of_lt hlt) he
  have hpart : S \ U = E := by
    ext z
    constructor
    · intro hz
      obtain ⟨hzS, hzU⟩ := Finset.mem_sdiff.mp hz
      have hnlt : ¬ inner2 w z < c := by
        intro h
        exact hzU (Finset.mem_filter.mpr ⟨hzS, h⟩)
      exact Finset.mem_filter.mpr ⟨hzS, le_antisymm (hmax z hzS) (not_lt.mp hnlt)⟩
    · intro hz
      obtain ⟨hzS, heq⟩ := Finset.mem_filter.mp hz
      refine Finset.mem_sdiff.mpr ⟨hzS, ?_⟩
      intro hU
      exact (ne_of_lt (Finset.mem_filter.mp hU).2) heq
  have hcard : E.card = S.card - U.card := by
    rw [← hpart, Finset.card_sdiff_of_subset hUS]
  have hEpos : 0 < E.card := Finset.card_pos.mpr hface
  have hstrict := hdef U hproper (latticeConvex_filter_inner2_lt hSc w c)
  change P ξ S - P ξ U ≤ E.card - 1
  omega

/-- Colle Lemma 2.4: a low-convex-complexity configuration admits a
generating set with the boundary complexity bound at every support line.
The exposed face may be a vertex or an edge. -/
theorem exists_generatingSet_with_boundary_deficit {A : Type*} {ξ : Config A}
    (hfin : (Set.range ξ).Finite) (hlow : LowConvexComplexity ξ) :
    ∃ S : Finset (ℤ × ℤ), IsGeneratingSet ξ S ∧ P ξ S ≤ S.card ∧
      ∀ (w : ℝ × ℝ) (c : ℝ), (∀ z ∈ S, inner2 w z ≤ c) →
        (S.filter fun z => inner2 w z = c).Nonempty →
        P ξ S - P ξ (S.filter fun z => inner2 w z < c) ≤
          (S.filter fun z => inner2 w z = c).card - 1 := by
  obtain ⟨S, hgen, hlowS, hdef⟩ := exists_generatingSet_with_strict_deficit hfin hlow
  exact ⟨S, hgen, hlowS, support_face_deficit_of_strict_deficit hgen.2.1 hdef⟩

end Nivat.Colle
