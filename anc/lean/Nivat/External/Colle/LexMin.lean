/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.LatticeEdges
import Nivat.External.Colle.EnvSuperset

set_option autoImplicit false

namespace Nivat.ColleReg
open Nivat Nivat.LE2
open scoped Pointwise

/-! # Lexicographic minimum

API for the `(nℓ, m)`-lexicographic minimum used in `RegionSteps.lean` hole 6.
The anchor point `g` is produced by `Nivat.StripDescend.exists_bottom_left`:
it minimizes `dot nℓ`, and among those, minimizes `dot m`.

**原文对应：** b3_colle2.txt:790-794 — "the lowest line contains exactly one point"
identifies the lex-min corner of the window, which becomes the anchor for the translate.
-/

/-- **`g` is the `(nℓ, m)`-lexicographic minimum of `T`.**

First minimize `⟪nℓ, ·⟫`, then among those, minimize `⟪m, ·⟫`. -/
def IsLexMin (nl m : ℤ × ℤ) (T : Set (ℤ × ℤ)) (g : ℤ × ℤ) : Prop :=
  g ∈ T ∧ ∀ z ∈ T, dot nl g < dot nl z ∨ (dot nl g = dot nl z ∧ dot m g ≤ dot m z)

theorem exists_isLexMin {T : Set (ℤ × ℤ)} (hfin : T.Finite) (hne : T.Nonempty)
    (nl m : ℤ × ℤ) : ∃ g, IsLexMin nl m T g := by
  -- Convert to Finset for easier manipulation
  have ⟨S, hS⟩ := hfin.exists_finset_coe
  have hS_ne : S.Nonempty := by rw [← hS] at hne; simpa using hne
  -- First minimize dot nl using min'
  let c₁ := S.image (dot nl)
  have hc₁_ne : c₁.Nonempty := hS_ne.image _
  let min_nl := c₁.min' hc₁_ne
  have hmin_nl_mem : min_nl ∈ c₁ := Finset.min'_mem c₁ hc₁_ne
  obtain ⟨g₁, hg₁_mem, hg₁_eq⟩ := Finset.mem_image.mp hmin_nl_mem
  have hg₁_min : ∀ z ∈ S, min_nl ≤ dot nl z := by
    intro z hz
    have : dot nl z ∈ c₁ := Finset.mem_image.mpr ⟨z, hz, rfl⟩
    exact Finset.min'_le _ _ this
  -- Define the subset where dot nl is minimal
  let S' := S.filter (fun z => dot nl z = min_nl)
  have hS'_ne : S'.Nonempty := by
    use g₁
    simp [S']
    exact ⟨hg₁_mem, hg₁_eq⟩
  -- Now minimize dot m on S'
  let c₂ := S'.image (dot m)
  have hc₂_ne : c₂.Nonempty := hS'_ne.image _
  let min_m := c₂.min' hc₂_ne
  have hmin_m_mem : min_m ∈ c₂ := Finset.min'_mem c₂ hc₂_ne
  obtain ⟨g, hg_mem, hg_eq⟩ := Finset.mem_image.mp hmin_m_mem
  have hg_min : ∀ z ∈ S', min_m ≤ dot m z := by
    intro z hz
    have : dot m z ∈ c₂ := Finset.mem_image.mpr ⟨z, hz, rfl⟩
    exact Finset.min'_le _ _ this
  simp [S'] at hg_mem
  refine ⟨g, ?_, fun z hz => ?_⟩
  · rw [← hS]; exact hg_mem.1
  · have hz_S : z ∈ S := by rw [← hS] at hz; exact hz
    by_cases h : dot nl z = min_nl
    · right
      constructor
      · have : dot nl g = min_nl := hg_mem.2
        omega
      · have hz' : z ∈ S' := by simp [S']; exact ⟨hz_S, h⟩
        have : min_m ≤ dot m z := hg_min z hz'
        omega
    · left
      have : min_nl ≤ dot nl z := hg₁_min z hz_S
      have : dot nl g = min_nl := hg_mem.2
      omega

/-- **Shrinking the set keeps the same lex-minimum as long as it survives.** -/
theorem IsLexMin.mono {nl m : ℤ × ℤ} {T T' : Set (ℤ × ℤ)} {g : ℤ × ℤ}
    (h : IsLexMin nl m T g) (hsub : T' ⊆ T) (hg : g ∈ T') : IsLexMin nl m T' g := by
  constructor
  · exact hg
  · intro z hz
    exact h.2 z (hsub hz)

/-- **Lex-min is additive over Minkowski sums.**

When `A + B = {a + b | a ∈ A, b ∈ B}`, if `a` is the lex-min of `A` and `b` is
the lex-min of `B`, then `a + b` is the lex-min of `A + B`. -/
theorem IsLexMin.add {nl m : ℤ × ℤ} {A B : Set (ℤ × ℤ)} {a b : ℤ × ℤ}
    (ha : IsLexMin nl m A a) (hb : IsLexMin nl m B b) :
    IsLexMin nl m (A + B) (a + b) := by
  constructor
  · exact Set.add_mem_add ha.1 hb.1
  · intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := hz
    have hax := ha.2 x hx
    have hby := hb.2 y hy
    rw [dot_add, dot_add, dot_add, dot_add]
    cases hax with
    | inl h1 =>
        left
        calc dot nl a + dot nl b
          _ < dot nl x + dot nl b := Int.add_lt_add_right h1 _
          _ ≤ dot nl x + dot nl y := by
              cases hby with
              | inl h => exact Int.add_lt_add_left h _ |>.le
              | inr h => exact Int.add_le_add_left h.1.le _
    | inr h1 =>
        cases hby with
        | inl h2 =>
            left
            calc dot nl a + dot nl b
              _ = dot nl x + dot nl b := by rw [h1.1]
              _ < dot nl x + dot nl y := Int.add_lt_add_left h2 _
        | inr h2 =>
            right
            constructor
            · calc dot nl a + dot nl b
                _ = dot nl x + dot nl b := by rw [h1.1]
                _ = dot nl x + dot nl y := by rw [h2.1]
            · calc dot m a + dot m b
                _ ≤ dot m x + dot m b := Int.add_le_add_right h1.2 _
                _ ≤ dot m x + dot m y := Int.add_le_add_left h2.2 _

end Nivat.ColleReg

#print axioms Nivat.ColleReg.exists_isLexMin
#print axioms Nivat.ColleReg.IsLexMin.mono
#print axioms Nivat.ColleReg.IsLexMin.add
