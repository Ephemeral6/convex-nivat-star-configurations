import Nivat.External.Colle.Generating
import Nivat.External.Colle.AmbiguousCounting

/-!
# Agreement-based generation and pattern complexity

This connects `GeneratesAt` to the literal equality of pattern counts
in Colle Definition 2.2, with finite range explicitly required.
-/

namespace Nivat.Colle

/-- Equality of the two pattern counts makes a site uniquely generated
throughout the orbit closure. -/
theorem generatesAt_of_P_eq {A : Type*} {ξ : Config A}
    (hfin : (Set.range ξ).Finite) {S : Finset (ℤ × ℤ)} {a : ℤ × ℤ}
    (ha : a ∈ S) (hP : P ξ (S.erase a) = P ξ S) : GeneratesAt ξ S a := by
  refine ⟨ha, ?_⟩
  intro x hx y hy hagree
  let px : patterns ξ S := ⟨pattern x S 0,
    patterns_subset_of_mem_orbitClosure hx S ⟨0, rfl⟩⟩
  let py : patterns ξ S := ⟨pattern y S 0,
    patterns_subset_of_mem_orbitClosure hy S ⟨0, rfl⟩⟩
  have hres : restrict_occurring_pattern ξ (Finset.erase_subset a S) px =
      restrict_occurring_pattern ξ (Finset.erase_subset a S) py := by
    apply Subtype.ext
    funext z
    change x (0 + z.1) = y (0 + z.1)
    simpa only [zero_add] using hagree z.1 z.2
  have heq := restrict_occurring_pattern_injective_of_P_eq hfin
    (Finset.erase_subset a S) hP hres
  have hz := congrArg (fun p : patterns ξ S => p.1 ⟨a, ha⟩) heq
  simpa only [px, py, pattern, zero_add] using hz

/-- A uniquely generated site has exactly one extension of each occurring
pattern on the remaining window, so the two complexities agree. -/
theorem P_eq_of_generatesAt {A : Type*} {ξ : Config A}
    (hfin : (Set.range ξ).Finite) {S : Finset (ℤ × ℤ)} {a : ℤ × ℤ}
    (hgen : GeneratesAt ξ S a) : P ξ (S.erase a) = P ξ S := by
  apply P_eq_of_restrict_occurring_pattern_injective hfin (Finset.erase_subset a S)
  intro p q hres
  obtain ⟨u, hu⟩ := p.2
  obtain ⟨v, hv⟩ := q.2
  have hxy : ∀ z ∈ S.erase a, T u ξ z = T v ξ z := by
    intro z hz
    have h := congrArg (fun r : patterns ξ (S.erase a) => r.1 ⟨z, hz⟩) hres
    change p.1 ⟨z, (Finset.erase_subset a S) hz⟩ =
      q.1 ⟨z, (Finset.erase_subset a S) hz⟩ at h
    rw [← hu, ← hv] at h
    simpa only [pattern, T_apply, add_comm] using h
  have ha := hgen.2 (T u ξ) (T_mem_orbitClosure ξ u)
    (T v ξ) (T_mem_orbitClosure ξ v) hxy
  apply Subtype.ext
  rw [← hu, ← hv]
  funext z
  by_cases hza : z.1 = a
  · simpa only [pattern, hza, T_apply, add_comm] using ha
  · have hz := hxy z.1 (Finset.mem_erase.mpr ⟨hza, z.2⟩)
    simpa only [pattern, T_apply, add_comm] using hz

/-- Agreement-based generation is equivalent to Colle's pattern-count
definition when the alphabet actually used by the configuration is finite. -/
theorem generatesAt_iff_P_eq {A : Type*} {ξ : Config A}
    (hfin : (Set.range ξ).Finite) {S : Finset (ℤ × ℤ)} {a : ℤ × ℤ} (ha : a ∈ S) :
    GeneratesAt ξ S a ↔ P ξ (S.erase a) = P ξ S :=
  ⟨P_eq_of_generatesAt hfin, generatesAt_of_P_eq hfin ha⟩

end Nivat.Colle
