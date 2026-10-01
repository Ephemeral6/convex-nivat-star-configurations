/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.L1Assemble

/-!
# `L1Residual` — a refutation probe on `MaxBResidual` (leaf L1)

`exists_L1MaxBResidual` (`RegionSteps.lean:844-875`) is one of the project's two remaining
`sorry`s.  Its conclusion, after peeling the existentials, is
`Nivat.ColleReg.L1Data.MaxBResidual ε u u' c τ S₁ F` (`L1Assemble.lean:924-942`), six fields:
`det'`, `prim`, `c0`, `line0`, `base0`, `straddle`.

Following the method that closed leaf C (`RunSide.lean`): before anyone writes a body for this
`sorry`, ask what the six fields fail to forbid.  This file finds a genuine one: **`base0` is
unsatisfiable whenever `S₁` is a singleton, for every choice of `ε`, `u`, `u'`, `c`, `τ`, `F`,
with no side condition at all.**

## The mechanism

`base0` (`L1Assemble.lean:959`, the first conjunct of the weak form) asks for
`b ∈ maxB (derivedQ ε u' S₁) u' pw`, with `maxB` at `L1Cut.lean:116`.
⚠ **锚订正（第 218 轮，OUTFILE 闸门命中）**：旧写的是 `L1Cut.lean` 的第 936–938 行，而
`L1Cut.lean` 只有 134 行（撤回的锚**故意不写成可解析的 `文件.lean:行号` 形式**，理由见
`AItemTwoParts.lean` 同一轮的那条订正）。病因可追：`maxB`/`mem_maxB`/`maxB_hBQ` 2026-09-19
从 `L1Assemble.lean` **原样搬到** `L1Cut.lean`，搬家记录就在 `L1Assemble.lean:937-938`，
**正好压在被引的那三行上** ⟹ 当时文件名跟着搬家改了、行号没改。三个对象都还在，
属 `PROTOCOL.md` §57 的 B 类。
`derivedQ`
(`L1Cut.lean:98-99`) is `S₁.filter (fun z => inner2 (cutNormal ε u') z < levelMax S₁ (cutNormal
ε u'))` — the points *strictly below* the top level.  When `S₁ = {a}` there is exactly one
level, so the filter predicate is `inner2 n a < inner2 n a`, which is `False` for every `n`:
`derivedQ` is `∅` **regardless of `ε` or `u'`**.  `maxB` of `∅` is `∅` (`Finset.filter_empty`),
so `base0`'s witness set is empty and the field cannot be discharged — not because of a bad
choice of `F`, but because the Finset-level scaffolding is empty before `F` is ever consulted.

## What this does and does not refute

🔴 **2026-09-19, correction (L1asm caught this, team-lead relayed it): the paragraph originally
here overclaimed and was wrong.** It said the leaf's binders do not exclude `S.card = 1`. They
do: `two_le_min_faces_of_nel hgen hℓ_nel hℓ_neg hvl_prim hdet_ℓ` (`L1Assemble.lean:1766`, Collé
Lemma 2.3) gives `2 ≤ min (topFace true vl S₁).card (bottomFace true vl S₁).card`, which is
`2 ≤ 1` — a contradiction — the moment `S₁` is a singleton, and **all five of those binders
(`hgen`, `hℓ_nel`, `hℓ_neg`, `hvl_prim`, `hdet_ℓ`) are already on `exists_L1MaxBResidual`**. So
a singleton `S` is excluded upstream, by hypotheses the leaf already carries.

**So the finding is not a live gap in `exists_L1MaxBResidual` as it stands.** It *is* a genuine
refutation of the **unthreaded** closure — `MaxBResidual ε u u' c τ S₁ F` alone, without the
five orientation binders in scope — and it is retained (§14: retracted judgments stay, status
changes, nothing is deleted) precisely because that is the same pattern as
`RunSide.not_exists_case2_run` versus `exists_case2_run`: a compiled `¬P` and a compiled proof
of the (differently-binder-equipped) live theorem can coexist validly in one green build,
because they are not the same closure. Read `not_maxBResidual_of_singleton`'s docstring above
for the corrected framing; do not conclude from this file that leaf L1 has an open gap here.

## Guard against the "unthreaded signature" misfire

Read `L1Assemble.lean` (mtime 2026-09-19 11:15, post the six-orientation-binder change already
in `exists_L1MaxBResidual`) and `RegionSteps.lean:844-875` (mtime 10:57, unchanged since) fresh
before writing this, specifically to check L1asm's in-flight edits had not altered
`MaxBResidual`'s six fields since the last read — they had not; `det'/prim/c0/line0/base0/
straddle` are byte-identical to the version this file targets.

Unlike `RunSide.lean`'s `ExistsCase2RunStatement` (a hand-transcribed `def ... : Prop`, which is
exactly how that file's first two lanes drifted from the post-threading signature),
`not_maxBResidual_of_singleton` below takes `H : Nivat.ColleReg.L1Data.MaxBResidual ...` as a
literal hypothesis of the real structure imported from `L1Assemble.lean`, and destructs the
real `H.base0` field projection — there is no separate transcribed copy of the closure to drift
out of sync, so the "prove a `False` guard by applying the real theorem" pattern is structurally
automatic here: if `MaxBResidual`'s field names or the shape of `base0` change upstream, this
file fails to compile rather than silently refuting a lookalike. -/

set_option autoImplicit false

namespace Nivat.L1Residual

open Nivat Nivat.ColleReg.L1Data

theorem levelMax_singleton (a : ℤ × ℤ) (n : ℝ × ℝ) :
    levelMax ({a} : Finset (ℤ × ℤ)) n = inner2 n a := by
  unfold levelMax
  rw [dif_pos (Finset.singleton_nonempty a)]
  exact Finset.sup'_singleton _

theorem derivedQ_singleton (ε : Bool) (u' a : ℤ × ℤ) :
    derivedQ ε u' ({a} : Finset (ℤ × ℤ)) = ∅ := by
  unfold derivedQ
  rw [levelMax_singleton]
  simp

theorem maxB_derivedQ_singleton (ε : Bool) (u' a : ℤ × ℤ) (pw : ℕ) :
    maxB (derivedQ ε u' ({a} : Finset (ℤ × ℤ))) u' pw = ∅ := by
  rw [derivedQ_singleton]
  classical
  unfold maxB
  simp

/-- **The refutation.**  `MaxBResidual` cannot hold on a singleton `S₁`, for *any* `ε`, `u`,
`u'`, `c`, `τ`, `F` — `base0` alone kills it, before `det'`/`prim`/`c0`/`line0`/`straddle` are
even inspected.

⚠ **This refutes the signature *without* the five orientation binders threaded, not the leaf
`exists_L1MaxBResidual` as it stands.**  `two_le_min_faces_of_nel hgen hℓ_nel hℓ_neg hvl_prim
hdet_ℓ` (`L1Assemble.lean:1766`) gives `2 ≤ min (topFace true vl S₁).card
(bottomFace true vl S₁).card`, which forces `2 ≤ 1` on a singleton `S₁` — a contradiction — and
all five of those (`hgen`, `hℓ_nel`, `hℓ_neg`, `hvl_prim`, `hdet_ℓ`) are already binders on
`exists_L1MaxBResidual`.  So a singleton `S` is excluded upstream; this theorem is genuine
evidence about the *unthreaded* closure (parallel to `RunSide.not_exists_case2_run`, which
refuted `exists_case2_run` before its six binders were threaded and coexists validly, in one
green build, with the threaded theorem's proof), not a live gap in the leaf as it stands. -/
theorem not_maxBResidual_of_singleton {ξ : Config ℤ} {e : ℤ × ℤ} (a : ℤ × ℤ)
    (ε : Bool) (u u' : ℤ × ℤ) (c τ : ℤ)
    (F : Nivat.L1Region.RegionFamily (Nivat.T e ξ) u u' c) :
    ¬ Nivat.ColleReg.L1Data.MaxBResidual (ξ := ξ) ε u u' c τ ({a} : Finset (ℤ × ℤ)) F := by
  intro H
  obtain ⟨⟨b, hb⟩, -⟩ := H.base0
  rw [maxB_derivedQ_singleton] at hb
  simp at hb

/-! ## `derivedQ`'s nonemptiness, characterized in general (2026-09-19, dispatched)

The singleton example above is the extreme case of a general fact about `S₁`/`u'`/`ε` alone:
`derivedQ ε u' S₁` and `topFace ε u' S₁` partition `S₁` by strict/non-strict inequality against
the top `cutNormal ε u'`-level, so `derivedQ` is nonempty **exactly when `S₁` is not flat under
the cut** — i.e. `levelMin < levelMax`. This is measured, not assumed: the guess that it
coincides with the `2 ≤ min (topFace true u ...) (bottomFace true u ...)` guard
(`maxB_nonempty_of_two_le_faces`, `L1Assemble.lean:1787`) is **false as an iff** — that guard is
stated in the *`u`*-direction (the period axis) and is a strictly stronger, genuinely
geometric fact (Lemma 2.3, routed through `maxB_wide`'s chord argument) needed for `maxB`, not
for `derivedQ`. `derivedQ_nonempty_iff` below needs no `u`, no `LatticeConvex`, no `Primitive`,
no `det ≠ 0` — only `S₁.Nonempty`. -/

theorem derivedQ_nonempty_iff {S₁ : Finset (ℤ × ℤ)} (ε : Bool) (u' : ℤ × ℤ)
    (hne : S₁.Nonempty) :
    (derivedQ ε u' S₁).Nonempty ↔
      levelMin S₁ (cutNormal ε u') < levelMax S₁ (cutNormal ε u') := by
  unfold derivedQ
  constructor
  · rintro ⟨z, hz⟩
    rw [Finset.mem_filter] at hz
    have h1 := levelMin_le (n := cutNormal ε u') hne z hz.1
    linarith [hz.2]
  · intro h
    obtain ⟨z, hz⟩ := face_levelMin_nonempty (S₁ := S₁) (n := cutNormal ε u') hne
    rw [Nivat.R2.mem_face] at hz
    exact ⟨z, Finset.mem_filter.mpr ⟨hz.1, hz.2 ▸ h⟩⟩

/-- Equivalent restatement in the shape `topFace`/`base0` actually use: `derivedQ` is nonempty
iff `topFace` is a proper subset of `S₁`, i.e. some point of `S₁` sits strictly below the top
level. Immediate from `derivedQ_nonempty_iff` plus `topFace`'s definition, recorded separately
because `base0`'s `pw := (topFace ε u' S₁).card - 1` is stated in terms of `topFace`, not
`levelMin`/`levelMax` directly. -/
theorem derivedQ_nonempty_iff_topFace_ssubset {S₁ : Finset (ℤ × ℤ)} (ε : Bool) (u' : ℤ × ℤ)
    (hne : S₁.Nonempty) :
    (derivedQ ε u' S₁).Nonempty ↔ topFace ε u' S₁ ⊂ S₁ := by
  rw [derivedQ_nonempty_iff ε u' hne]
  unfold topFace
  constructor
  · intro h
    refine ⟨Nivat.R2.face_subset _ _ _, fun hsub => ?_⟩
    obtain ⟨z, hz⟩ := face_levelMin_nonempty (S₁ := S₁) (n := cutNormal ε u') hne
    rw [Nivat.R2.mem_face] at hz
    have := hsub hz.1
    rw [Nivat.R2.mem_face] at this
    linarith [this.2, hz.2]
  · rintro ⟨-, hne'⟩
    by_contra hle
    push Not at hle
    apply hne'
    intro z hz
    rw [Nivat.R2.mem_face]
    refine ⟨hz, le_antisymm (le_levelMax (n := cutNormal ε u') hne z hz) ?_⟩
    linarith [levelMin_le (n := cutNormal ε u') hne z hz]

/-- **The corollary `base0`/`line0`'s producers actually need**: the `u`-direction Lemma 2.3
guard already bound on `exists_L1MaxBResidual` (via `two_le_min_faces_of_nel`,
`L1Assemble.lean:1766`) is *stronger* than what `derivedQ_nonempty_iff` asks for — it gives the
whole `maxB` nonempty, of which `derivedQ` nonemptiness is a free corollary (`maxB ⊆ derivedQ`
by `Finset.filter_subset`). So no new premise beyond what `maxB_nonempty_of_two_le_faces`
already assembles is needed for `derivedQ`; this lemma just repackages that fact in the
`derivedQ`-only shape so `line0`'s producer (which only ever needs a point of `derivedQ`, not a
run) does not have to unfold `maxB`. -/
theorem derivedQ_nonempty_of_two_le_faces {S₁ : Finset (ℤ × ℤ)} (hS : Nivat.LatticeConvex S₁)
    (hne : S₁.Nonempty) {u u' : ℤ × ℤ} (hu : Primitive u) (hu' : Primitive u')
    (hdet : det u u' ≠ 0) (ε : Bool)
    (h2 : 2 ≤ min (topFace true u S₁).card (bottomFace true u S₁).card) :
    (derivedQ ε u' S₁).Nonempty :=
  (maxB_nonempty_of_two_le_faces hS hne hu hu' hdet ε h2).mono
    (Finset.filter_subset _ _)

/-! ## On the "second gap" question (already resolved upstream, not new here)

Team-lead's item 3 asked: can `derivedQ` be nonempty while `maxB (derivedQ ε u' S₁) u' pw`
(`pw := (topFace ε u' S₁).card - 1`) is still empty? **Yes, and this is not a new finding** —
it is exactly the reason `maxB_nonempty_of_two_le_faces` needs the Lemma 2.3 guard `h2` at all
(`L1Assemble.lean:1783-1786`, docstring: "without it the width of `maxB_wide` is `0` and `maxB`
may be empty (`no_nonempty_B_run_943`'s triangle)"). Without `h2`, a triangle-shaped `S₁` can
have a single-point `u`-bottom-face against a wide `u`-top-face, so `derivedQ` (built from the
*other*, `u'`, direction) is nonempty but too short to host a `pw`-run. So: `derivedQ`
nonempty is a purely combinatorial (`S₁`/`u'`/`ε`-only) fact; `maxB (derivedQ ...)` nonempty is
strictly stronger and needs the genuinely geometric `u`-direction Lemma 2.3 guard, already
identified and already discharged in `L1Assemble.lean`. Nothing here changes `base0`'s proof
obligation beyond what `maxB_nonempty_of_two_le_faces` already supplies. -/

end Nivat.L1Residual

#print axioms Nivat.L1Residual.levelMax_singleton
#print axioms Nivat.L1Residual.derivedQ_singleton
#print axioms Nivat.L1Residual.maxB_derivedQ_singleton
#print axioms Nivat.L1Residual.not_maxBResidual_of_singleton
#print axioms Nivat.L1Residual.derivedQ_nonempty_iff
#print axioms Nivat.L1Residual.derivedQ_nonempty_iff_topFace_ssubset
#print axioms Nivat.L1Residual.derivedQ_nonempty_of_two_le_faces
