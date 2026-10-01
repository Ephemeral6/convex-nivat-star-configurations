import Nivat.External.Colle.Generating

/-!
# Strict complexity deficit for a convex window

The finite descent behind Colle Lemma 2.4. If a proper convex subwindow
does not give the strict deficit, descend to it. Low complexity is
preserved and the cardinality decreases.
-/

namespace Nivat.Colle

/-- A low-complexity convex window contains a low-complexity convex
subwindow with strict deficit against every proper convex subwindow.
The empty subwindow is allowed in the final inequality. -/
theorem exists_window_with_strict_deficit {A : Type*} (ξ : Config A)
    (S : Finset (ℤ × ℤ)) (hne : S.Nonempty) (hconv : LatticeConvex S)
    (hlow : P ξ S ≤ S.card) :
    ∃ B : Finset (ℤ × ℤ), B ⊆ S ∧ B.Nonempty ∧ LatticeConvex B ∧
      P ξ B ≤ B.card ∧ ∀ U : Finset (ℤ × ℤ), U ⊂ B → LatticeConvex U →
        P ξ B < P ξ U + (B.card - U.card) := by
  classical
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    by_cases hgood : ∀ U : Finset (ℤ × ℤ), U ⊂ S → LatticeConvex U →
        P ξ S < P ξ U + (S.card - U.card)
    · exact ⟨S, Finset.Subset.refl S, hne, hconv, hlow, hgood⟩
    · push Not at hgood
      obtain ⟨U, hUS, hUc, hbad⟩ := hgood
      have hcard : U.card ≤ S.card := Finset.card_le_card hUS.1
      have hUlow : P ξ U ≤ U.card := by omega
      have hUne : U.Nonempty := by
        by_contra h
        have hU : U = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
        rw [hU, P_empty, Finset.card_empty] at hUlow
        omega
      obtain ⟨B, hBU, hBne, hBc, hBlow, hBdef⟩ := ih U hUS hUne hUc hUlow
      exact ⟨B, hBU.trans hUS.1, hBne, hBc, hBlow, hBdef⟩

/-- Removing an extreme point preserves lattice convexity. -/
theorem latticeConvex_erase_of_extremePoint {S : Finset (ℤ × ℤ)}
    (hS : LatticeConvex S) {a : ℤ × ℤ}
    (ha : toReal a ∈ (Conv S).extremePoints ℝ) : LatticeConvex (S.erase a) := by
  have hconv : Convex ℝ (Conv S \ {toReal a}) :=
    ((convex_convexHull ℝ _).mem_extremePoints_iff_convex_sdiff.mp ha).2
  have hsub : Conv (S.erase a) ⊆ Conv S \ {toReal a} := by
    apply convexHull_min _ hconv
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨hza, hzS⟩ := Finset.mem_erase.mp hz
    refine ⟨subset_Conv hzS, ?_⟩
    intro heq
    exact hza (toReal_injective (Set.mem_singleton_iff.mp heq))
  intro z hz
  obtain ⟨hzS, hza⟩ := hsub hz
  refine Finset.mem_erase.mpr ⟨?_, hS z hzS⟩
  intro heq
  exact hza (by simp only [heq, Set.mem_singleton_iff])

/-- Cutting a lattice-convex window by a strict real half-plane preserves
lattice convexity. The normal may have irrational coordinates. -/
theorem latticeConvex_filter_inner2_lt {S : Finset (ℤ × ℤ)}
    (hS : LatticeConvex S) (w : ℝ × ℝ) (c : ℝ) :
    LatticeConvex (S.filter fun z => inner2 w z < c) := by
  have hlinear : IsLinearMap ℝ (fun x : ℝ × ℝ => x.1 * w.1 + x.2 * w.2) := by
    constructor
    · intro x y
      simp only [Prod.fst_add, Prod.snd_add]
      ring
    · intro a x
      simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      ring
  have hsub : Conv (S.filter fun z => inner2 w z < c) ⊆
      {x : ℝ × ℝ | x.1 * w.1 + x.2 * w.2 < c} := by
    apply convexHull_min _ (convex_halfSpace_lt hlinear c)
    rintro _ ⟨z, hz, rfl⟩
    exact (Finset.mem_filter.mp hz).2
  intro z hz
  refine Finset.mem_filter.mpr ⟨?_, hsub hz⟩
  apply hS z
  apply convexHull_mono (Set.image_mono ?_) hz
  exact_mod_cast Finset.filter_subset (fun z => inner2 w z < c) S

end Nivat.Colle
