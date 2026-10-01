/-
Copyright (c) 2026 Nivat formalisation project. All rights reserved.
-/
import Nivat.Section8.ExternalDefs
import Nivat.External.Colle.Lemma35
import Nivat.External.Colle.Lemma45
import Nivat.External.Colle.LatticeEdges
import Nivat.External.Colle.Step_BiONED
import Nivat.External.Colle.Step_Nonempty
import Nivat.External.Colle.ChainGeom
import Nivat.External.Colle.Prop210
import Nivat.External.Colle.DecompData
import Nivat.External.Colle.Lemma41
import Nivat.External.Colle.PeriodTransport
import Nivat.External.Colle.Claim47Core

/-!
# L1 — the cut derived from `u'`, and the maximal baseline (definitions only)

Split out of `L1Assemble.lean` on 2026-09-19 (integrator's ruling) so that `L1Data.lean` can
*name* `maxB`, `derivedQ` and `topFace` in a field without importing `L1Assemble`
(`L1Assemble` imports `L1Data`; the reverse edge would be a cycle).  Everything here was moved
**verbatim** from `L1Assemble.lean` (`section DerivedCut`, `:745-811`, and the head of
`section MaxB`, `:973-992`), in the same namespace `Nivat.ColleReg.L1Data`, so every full name
is unchanged — `L3Band.lean` references (`min_Wrow_eq_min_card_face`, `hasBlock_maxB`) and
`RegionSteps.lean:956` keep compiling.

The imports are exactly `L1Data.lean`'s own list (the definitions use only `perp`, `toReal`,
`inner2`, `Nivat.R2.face` and `Finset.sup'`/`inf'`); checked in `tmp/l1asm_L1Cut_draft.lean`
before the move.

Contents: `cutNormal`, `levelMax`, `levelMin`, `derivedQ`, `topFace`, `bottomFace` and their
small lemmas; `maxB`, `mem_maxB`, `maxB_hBQ`.  No theorem of substance lives here.
-/

set_option autoImplicit false

namespace Nivat.ColleReg

open Nivat Nivat.Colle35

namespace L1Data

section DerivedCut

/-- The cut normal determined by `u'` and a side: `perp u'` for `ε = true`, `-perp u'`
otherwise. -/
noncomputable def cutNormal (ε : Bool) (u' : ℤ × ℤ) : ℝ × ℝ :=
  toReal (if ε then perp u' else -perp u')

theorem inner2_cutNormal (ε : Bool) (u' : ℤ × ℤ) : inner2 (cutNormal ε u') u' = 0 := by
  unfold cutNormal
  cases ε <;> simp [Nivat.LE2.inner2_toReal, Nivat.LE2.dot_neg_left, dot_perp]

theorem perp_ne_zero {u' : ℤ × ℤ} (h : u' ≠ 0) : perp u' ≠ 0 := by
  intro hc
  apply h
  have h1 := congrArg Prod.fst hc
  have h2 := congrArg Prod.snd hc
  simp only [perp, Prod.fst_zero, Prod.snd_zero, neg_eq_zero] at h1 h2
  exact Prod.ext h2 h1

theorem cutNormal_ne_zero (ε : Bool) {u' : ℤ × ℤ} (h : u' ≠ 0) : cutNormal ε u' ≠ 0 := by
  unfold cutNormal
  apply Nivat.KM.toReal_ne_zero
  cases ε <;> simpa using perp_ne_zero h

/-- The top level of `S₁` in direction `n` (`0` on the empty set, which never occurs). -/
noncomputable def levelMax (S₁ : Finset (ℤ × ℤ)) (n : ℝ × ℝ) : ℝ :=
  if h : S₁.Nonempty then S₁.sup' h (fun z => inner2 n z) else 0

/-- The bottom level. -/
noncomputable def levelMin (S₁ : Finset (ℤ × ℤ)) (n : ℝ × ℝ) : ℝ :=
  if h : S₁.Nonempty then S₁.inf' h (fun z => inner2 n z) else 0

theorem le_levelMax {S₁ : Finset (ℤ × ℤ)} {n : ℝ × ℝ} (hne : S₁.Nonempty) :
    ∀ z ∈ S₁, inner2 n z ≤ levelMax S₁ n := by
  intro z hz
  unfold levelMax
  rw [dif_pos hne]
  exact Finset.le_sup' (fun z => inner2 n z) hz

theorem face_levelMax_nonempty {S₁ : Finset (ℤ × ℤ)} {n : ℝ × ℝ} (hne : S₁.Nonempty) :
    (Nivat.R2.face S₁ n (levelMax S₁ n)).Nonempty := by
  unfold levelMax
  rw [dif_pos hne]
  obtain ⟨z, hz, hz'⟩ := Finset.exists_mem_eq_sup' hne (fun z => inner2 n z)
  exact ⟨z, Nivat.R2.mem_face.mpr ⟨hz, hz'.symm⟩⟩

theorem face_levelMin_nonempty {S₁ : Finset (ℤ × ℤ)} {n : ℝ × ℝ} (hne : S₁.Nonempty) :
    (Nivat.R2.face S₁ n (levelMin S₁ n)).Nonempty := by
  unfold levelMin
  rw [dif_pos hne]
  obtain ⟨z, hz, hz'⟩ := Finset.exists_mem_eq_inf' hne (fun z => inner2 n z)
  exact ⟨z, Nivat.R2.mem_face.mpr ⟨hz, hz'.symm⟩⟩

/-- `Q` with the cut derived: the points of `S₁` strictly below the top level. -/
noncomputable def derivedQ (ε : Bool) (u' : ℤ × ℤ) (S₁ : Finset (ℤ × ℤ)) : Finset (ℤ × ℤ) :=
  S₁.filter fun z => inner2 (cutNormal ε u') z < levelMax S₁ (cutNormal ε u')

/-- The top face (`S₁ ∖ Q`, the edge parallel to `u'`). -/
noncomputable def topFace (ε : Bool) (u' : ℤ × ℤ) (S₁ : Finset (ℤ × ℤ)) : Finset (ℤ × ℤ) :=
  Nivat.R2.face S₁ (cutNormal ε u') (levelMax S₁ (cutNormal ε u'))

/-- The bottom face, where conjunct 8's run and conjunct 16's base points live. -/
noncomputable def bottomFace (ε : Bool) (u' : ℤ × ℤ) (S₁ : Finset (ℤ × ℤ)) :
    Finset (ℤ × ℤ) :=
  Nivat.R2.face S₁ (cutNormal ε u') (levelMin S₁ (cutNormal ε u'))

end DerivedCut

section MaxB

open Classical in
/-- The largest baseline conjunct 8 allows. -/
noncomputable def maxB (Q : Finset (ℤ × ℤ)) (u' : ℤ × ℤ) (pw : ℕ) : Finset (ℤ × ℤ) :=
  Q.filter fun g => ∀ i : ℕ, i < pw → g + (i : ℤ) • u' ∈ Q

open Classical in
theorem mem_maxB {Q : Finset (ℤ × ℤ)} {u' : ℤ × ℤ} {pw : ℕ} {g : ℤ × ℤ} :
    g ∈ maxB Q u' pw ↔ g ∈ Q ∧ ∀ i : ℕ, i < pw → g + (i : ℤ) • u' ∈ Q := by
  unfold maxB
  exact Finset.mem_filter

/-- Conjunct 8 for `maxB`, by construction. -/
theorem maxB_hBQ (Q : Finset (ℤ × ℤ)) (u' : ℤ × ℤ) (pw : ℕ) :
    ∀ g ∈ maxB Q u' pw, ∀ i : ℕ, i < pw → g + (i : ℤ) • u' ∈ Q :=
  fun _ hg => (mem_maxB.mp hg).2

end MaxB

end L1Data

end Nivat.ColleReg
