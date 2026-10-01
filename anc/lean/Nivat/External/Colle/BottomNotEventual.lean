/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.ShellLine

/-!
# `ChainDataGeom.bottom` is not a level-line property

A compiled `¬P`, kept so the reduction is not attempted again (2026-09-17).

⚠ **Status 2026-09-19: `BottomShape` below is the *retired* five-conjunct shape of `bottom`.**
The live field `ChainDataGeom.bottom` (`ChainGeom.lean`) has **four** conjuncts: conjunct (iv)
— the `b - a'` translate — was **deleted outright** on 2026-09-19.  The unguarded five-conjunct
shape survives as the explicit hypothesis `Nivat.ShellMink.ChainDataGeom.RetiredBottom`
(`ShellMink.lean`), and `cgwA` there is a `ChainDataGeom` with `a ≠ a'` that fails it.  This
file is refutation archive and is *meant* to talk about the old shape: the declarations are
kept verbatim, not restated.  Note that `not_bottomShape_quad` reads only conjuncts (iii) and
(v) (`habs`, the `b - a` translate at an off-face `b`, and `hsplit`), both of which are still in
the live field — so the refutation of the level-line reduction is not weakened by the
deletion, it just now refutes the reduction to a shape one conjunct stronger than the live
field.

*Retracted reading (kept per §14, do not delete):* the 07:06 version of this paragraph said
"`ChainGeom.lean` now guards conjunct (iv) by `1 ≤ dot nJ (b - a')` (OPEN #7 ruling: restrict,
don't delete)".  That was the 06:43 repair; it was withdrawn at 07:4x because the guard is
insufficient — the defect is in `k`, not in `b`: `not_guardedIV_quad_sq1`
(`tmp/Abottom_noIV.lean`, kernel-clean, in `tmp/`) shows the *guarded* (iv) is still
incompatible with (v) on the quadrant / unit-square data at every `ε`, and the failing point
`b = (0,1)` *passes* the guard.  Since (iv) at `(b,k)` is (iii) at `(b, k - j)` by
`run_of_face` (`a' = a + j • vJ`, `j ≤ r`) and the consumer `genLayers` only reads `k > L + r`,
the conjunct was redundant where read and false where not, and was deleted.  The `a'` field
itself stays.

`Nivat.Colle35.ChainDataGeom.bottom` (`ChainGeom.lean:97`) is the one field of the bundle
that looks like it should follow from the geometry of `Â_∞` alone.  The natural candidate is
`LevelHalfLine` below: "`reachSet Â_∞ v_{J-1}` meets each line `⟪n_J,·⟫ = c_J-ε-1` in a
`v_J`-half-line, and every offset `w` with `⟪n_J,w⟫ ≥ 0` is absorbed *eventually* along it".
`not_bottom_of_levelHalfLine` shows this does **not** imply `bottom`, even with the window
hypotheses `0 ≤ ⟪n_J, b - a⟫` that `ChainDataGeom.edge`/`edge'` provide.

Why: `bottom`'s conjunct (v) pins the half-line `{z₀ + k•vJ : L ≤ k}` to be *all* of
`reachSet A v ∩ {⟪n,·⟫ = c-ε-1}` (the layer `shell ε` and that line are disjoint), so
conjuncts (iii)/(iv) demand absorption of `b - a` at *every* point of the slice, including
its start.  With `A` the closed quadrant the slice starts at `x = 0` and the offset
`b - a = (-1, 1)` pushes the start point out of the swept set.

What this means for `exists_chainData`: absorption at the corner is a consequence of
`E(S_φ)`-envelopedness (each edge of `Â_∞` is parallel to, and carries at least as many
lattice points as, an edge of `S_φ` — `b3_colle2.txt:402`, Definition 3.2) together with
lattice convexity, not of the shape of the
level line.  `bottom` therefore stays as stated and is discharged from `EnvOf ↑S` inside the
construction.
-/

namespace Nivat.MaxEnv
open Nivat Nivat.LE2

def LevelHalfLine (A : Set (ℤ × ℤ)) (v n vJ : ℤ × ℤ) (c : ℤ) : Prop :=
  ∀ ε : ℕ, ∃ (z₀ : ℤ × ℤ) (L : ℤ),
    dot n z₀ = c - (ε : ℤ) - 1 ∧
    (∀ k : ℤ, L ≤ k → z₀ + k • vJ ∈ reachSet A v) ∧
    (∀ z ∈ reachSet A v, dot n z = c - (ε : ℤ) - 1 → ∃ k : ℤ, L ≤ k ∧ z = z₀ + k • vJ) ∧
    (∀ w : ℤ × ℤ, 0 ≤ dot n w →
      ∃ L' : ℤ, ∀ k : ℤ, L' ≤ k → z₀ + k • vJ + w ∈ reachSet A v)

/-- The five conjuncts of `ChainDataGeom.bottom`, with the bundle's parameters made explicit.

(Status: archival, retired shape since 2026-09-19.)  Conjunct (iv) here — the `b - a'`
translate — is the one **deleted** from the live field on 2026-09-19; the live
`ChainDataGeom.bottom` has four conjuncts.  Same shape as `ShellMink.ChainDataGeom.RetiredBottom`,
with the bundle's fields replaced by free parameters.
*Retracted reading (§14):* this docstring said until 07:06 that "the live field carries
`1 ≤ dot n (b - a') →`"; that guard was itself refuted (`not_guardedIV_quad_sq1`) and never
survived to the current tree — see the module docstring. -/
def BottomShape (A : Set (ℤ × ℤ)) (v n vJ : ℤ × ℤ) (c : ℤ) (S : Finset (ℤ × ℤ))
    (a a' : ℤ × ℤ) : Prop :=
  ∀ ε : ℕ, ∃ (z₀ : ℤ × ℤ) (L : ℤ),
    dot n z₀ = c - (ε : ℤ) - 1 ∧
    (∀ k : ℤ, L ≤ k → z₀ + k • vJ ∈ reachSet A v) ∧
    (∀ b ∈ S, ∀ k : ℤ, L ≤ k → z₀ + k • vJ + (b - a) ∈ reachSet A v) ∧
    (∀ b ∈ S, ∀ k : ℤ, L ≤ k → z₀ + k • vJ + (b - a') ∈ reachSet A v) ∧
    (∀ z ∈ shell A v n c (ε + 1),
      z ∈ shell A v n c ε ∨ ∃ k : ℤ, L ≤ k ∧ z = z₀ + k • vJ)

/-- The closed quadrant. -/
def quad : Set (ℤ × ℤ) := {z | 0 ≤ z.1 ∧ 0 ≤ z.2}

theorem mem_reach_quad {z : ℤ × ℤ} :
    z ∈ reachSet quad ((0 : ℤ), (-1 : ℤ)) ↔ 0 ≤ z.1 := by
  constructor
  · rintro ⟨g, ⟨hg1, _⟩, t, rfl⟩
    simpa using hg1
  · intro h
    refine ⟨(z.1, z.2 + (z.2.natAbs : ℤ)), ⟨h, by omega⟩, z.2.natAbs, ?_⟩
    ext <;> simp

theorem levelHalfLine_quad :
    LevelHalfLine quad ((0 : ℤ), (-1 : ℤ)) ((0 : ℤ), (1 : ℤ)) ((1 : ℤ), (0 : ℤ)) 0 := by
  intro ε
  refine ⟨((0 : ℤ), -(ε : ℤ) - 1), 0, ?_, ?_, ?_, ?_⟩
  · simp [dot]
  · intro k hk
    rw [mem_reach_quad]; simpa using hk
  · intro z hz hd
    rw [mem_reach_quad] at hz
    refine ⟨z.1, hz, ?_⟩
    simp only [dot] at hd
    ext
    · simp
    · simp; omega
  · intro w hw
    refine ⟨-w.1, fun k hk => ?_⟩
    rw [mem_reach_quad]; simp; omega

theorem not_bottomShape_quad :
    ¬ BottomShape quad ((0 : ℤ), (-1 : ℤ)) ((0 : ℤ), (1 : ℤ)) ((1 : ℤ), (0 : ℤ)) 0
      {((0 : ℤ), (0 : ℤ)), ((-1 : ℤ), (1 : ℤ))} ((0 : ℤ), (0 : ℤ)) ((0 : ℤ), (0 : ℤ)) := by
  intro h
  obtain ⟨z₀, L, -, -, habs, -, hsplit⟩ := h 0
  have hz : ((0 : ℤ), (-1 : ℤ)) ∈ shell quad ((0 : ℤ), (-1 : ℤ)) ((0 : ℤ), (1 : ℤ)) 0 (0 + 1) := by
    rw [shell_eq_reach_inter, Set.mem_inter_iff, mem_reach_quad]
    simp [dot]
  rcases hsplit _ hz with hs | ⟨k, hk, hzk⟩
  · rw [shell_eq_reach_inter, Set.mem_inter_iff] at hs
    simp [dot] at hs
  · have := habs ((-1 : ℤ), (1 : ℤ)) (by simp) k hk
    rw [mem_reach_quad, ← hzk] at this
    simp at this

/-- **The reduction is false**: `LevelHalfLine` together with the window hypotheses of
`bottom_of_levelHalfLine` does not imply the five conjuncts of `ChainDataGeom.bottom`.

(Status: archival, retired shape since 2026-09-19 — `BottomShape` still carries conjunct (iv),
which the live field no longer has.  The witness `not_bottomShape_quad` only uses conjuncts
(iii) and (v), both still in the live four-conjunct field, so the same argument refutes the
reduction to the live shape too; that restatement is not written, by design — this file is
archive.  *Retracted reading (§14):* until 07:06 this said "refutes the reduction to the
guarded shape too"; there is no guarded shape in the tree, (iv) was deleted, not guarded.) -/
theorem not_bottom_of_levelHalfLine :
    ¬ ∀ (A : Set (ℤ × ℤ)) (v n vJ : ℤ × ℤ) (c : ℤ) (S : Finset (ℤ × ℤ)) (a a' : ℤ × ℤ),
      LevelHalfLine A v n vJ c →
      (∀ b ∈ S, 0 ≤ dot n (b - a)) → (∀ b ∈ S, 0 ≤ dot n (b - a')) →
      BottomShape A v n vJ c S a a' := by
  intro h
  refine not_bottomShape_quad (h _ _ _ _ _ _ _ _ levelHalfLine_quad ?_ ?_) <;>
  · intro b hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with rfl | rfl <;> simp [dot]

end Nivat.MaxEnv

