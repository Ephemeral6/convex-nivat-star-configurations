/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.ItemII
import Nivat.External.Colle.ChainMax
import Nivat.External.Colle.PolyChainSum

/-!
# Walls of `⋃ j, Â_j`: which normals can be bounded above, and which cannot

Lane `lane-tower-hbase`, round 166.  General lemmas only; the one-off numeric witnesses that
motivated them stay in `tmp/wip/` (`lane-tower-hbase-substrip.lean` §§10–14, §26,
`lane-tower-hbase-oct8.lean`).

## What this file says

`b3_colle2.txt:939-947` (item (ii) of the chain data) says that the family `B` eventually
covers every lattice point of the half plane `ℋ(ℓ^(−)) = {z | cz ≤ ⟪ν_ℓ, z⟫}`: for each `j`,
every `z` in that half plane with `|z.1| < j` and `|z.2| < j` already lies in `B j`.
`Nivat.Colle35.ItemII B nℓ cz` (`ItemII.lean:80`) is that statement verbatim.

Combined with `subBA : ∀ i, B i ⊆ A i` (`ChainExhaustInter.lean`) and
`hperp : ⟪ν_ℓ, v⃗_ℓ⟫ = 0` (`ChainExhaustInter.lean`), it forces a sign law on the normals
of the union of the
normalised layers `Â_j = hatOf A kk vl j` (`ChainMax.lean:87`):

> a normal `ν` with `⟪ν, v⃗_ℓ⟫ < 0` is **unbounded above** on `⋃ j, Â_j`.

Reason, in one line: translating a point of `ℋ(ℓ^(−))` by `-t v⃗_ℓ` keeps it in `ℋ(ℓ^(−))`
(that is `hperp`) while raising `⟪ν, ·⟫` by `t·(-⟪ν, v⃗_ℓ⟫) > 0`; item (ii) then captures the
translate in some `B j ⊆ A j`, and the normalisation `-k_j v⃗_ℓ` can only raise `⟪ν, ·⟫` further.

Three consequences are recorded: the unboundedness itself (`exists_mem_iUnion_hatOf_dot_gt`),
its `¬ BddAbove` form (`not_bddAbove_dot_of_strict_wall`), and the contrapositive in the shape
other lanes consume it — a **nonempty** face pins the sign (`dot_vl_nonneg_of_face_nonempty`).

## Warning about the `Finite` variant

`(face (⋃ j, Â_j) ν).Finite → 0 ≤ ⟪ν, v⃗_ℓ⟫` is **false**: when `⟪ν, ·⟫` is unbounded above the
face is *empty*, hence finite, so the hypothesis holds for exactly the normals the conclusion is
meant to exclude.  `dot_vl_nonneg_of_face_finite_nonempty` is the repaired form, carrying the
nonemptiness explicitly.

## Scope

Nothing here mentions the sweep direction `w`, the shell, or any envelopedness guard.  The two
`w`-side lemmas kept here are purely arithmetic degeneracy checks (§3) used to certify that an
instance is *not* a legal one, so that no proof is mistakenly built on a vacuous premise.
-/

set_option autoImplicit false

namespace Nivat.WallBound

open Nivat Nivat.LE2

/-! ## §1.  Item (ii) makes every strict wall unbounded on `⋃ j, Â_j` -/

/-- **Item (ii) makes every strict wall unbounded on `Â_∞`.**  `⟪ν, ·⟫` exceeds any prescribed
`c` somewhere in `⋃ j, Â_j`, as soon as `⟪ν, v⃗_ℓ⟫ < 0` and `⟪ν_ℓ, v⃗_ℓ⟫ = 0`.

Binders, and where each is free at the call site
(`Nivat.Colle35.ChainDataGeom.ofPartsExhaustsInter`, `ChainExhaustInter.lean`):
* `hitem : ItemII B nℓ cz` — item (ii) of the chain data, `b3_colle2.txt:939-947`
  (`ItemII.lean:80`);
* `hsubBA : ∀ i, B i ⊆ A i` — the binder `subBA` (`ChainExhaustInter.lean`);
* `hperp : dot nℓ vl = 0` — the binder `hperp` (`ChainExhaustInter.lean`), `b3_colle2.txt:497`;
* `hνvl : dot ν vl < 0` — the *strict* wall condition;
* `hz₀ : cz ≤ dot nℓ z₀` — any point of `ℋ(ℓ^(−))`, e.g. any point of `B 0` under item (i).

The non-strict walls `dot ν vl = 0` are excluded on purpose: those are exactly the normals a
level bound can block, and they are `±ν_ℓ` up to positive scaling when `ν_ℓ` is primitive. -/
theorem exists_mem_iUnion_hatOf_dot_gt {A B : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ}
    {nℓ vl ν : ℤ × ℤ} {cz : ℤ}
    (hitem : Nivat.Colle35.ItemII B nℓ cz) (hsubBA : ∀ i, B i ⊆ A i)
    (hperp : dot nℓ vl = 0) (hνvl : dot ν vl < 0)
    {z₀ : ℤ × ℤ} (hz₀ : cz ≤ dot nℓ z₀) (c : ℤ) :
    ∃ z ∈ ⋃ j, Nivat.Colle35.hatOf A kk vl j, c < dot ν z := by
  classical
  set t : ℤ := ((c - dot ν z₀ + 1).toNat : ℤ) with ht_def
  have ht0 : (0 : ℤ) ≤ t := Int.natCast_nonneg _
  have ht1 : c - dot ν z₀ + 1 ≤ t := Int.self_le_toNat _
  set y : ℤ × ℤ := z₀ + (-t) • vl with hy_def
  have hylev : cz ≤ dot nℓ y := by
    rw [hy_def, Nivat.Colle35.dot_add_zsmul_of_perp hperp]; exact hz₀
  have hydot : dot ν y = dot ν z₀ + (-t) * dot ν vl := by
    rw [hy_def, dot_add, Nivat.PolyChainSum.dot_zsmul_right]
  have hyc : c < dot ν y := by
    have : t ≤ t * (-(dot ν vl)) := le_mul_of_one_le_right ht0 (by omega)
    rw [hydot]; nlinarith
  -- item (ii) captures `y` in some `B j`
  set j : ℕ := (|y.1| + |y.2| + 1).toNat with hj_def
  have hjcast : (j : ℤ) = |y.1| + |y.2| + 1 := by
    rw [hj_def]; exact Int.toNat_of_nonneg (by positivity)
  have hyB : y ∈ B j :=
    hitem j y (by rw [hjcast]; linarith [abs_nonneg y.2])
      (by rw [hjcast]; linarith [abs_nonneg y.1]) hylev
  refine ⟨y + (-(kk j : ℤ)) • vl, Set.mem_iUnion.mpr ⟨j, ?_⟩, ?_⟩
  · show y + (-(kk j : ℤ)) • vl + ((kk j : ℤ)) • vl ∈ A j
    have : y + (-(kk j : ℤ)) • vl + ((kk j : ℤ)) • vl = y := by
      rw [neg_smul]; abel
    rw [this]; exact hsubBA j hyB
  · rw [dot_add, Nivat.PolyChainSum.dot_zsmul_right]
    have hk : (0 : ℤ) ≤ (kk j : ℤ) := Int.natCast_nonneg _
    nlinarith

/-- **No upper bound exists on a strict wall.**  The `¬ BddAbove` form of
`exists_mem_iUnion_hatOf_dot_gt`, which is what a blocking argument would have had to supply. -/
theorem not_bddAbove_dot_of_strict_wall {A B : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ}
    {nℓ vl ν : ℤ × ℤ} {cz : ℤ}
    (hitem : Nivat.Colle35.ItemII B nℓ cz) (hsubBA : ∀ i, B i ⊆ A i)
    (hperp : dot nℓ vl = 0) (hνvl : dot ν vl < 0)
    {z₀ : ℤ × ℤ} (hz₀ : cz ≤ dot nℓ z₀) :
    ¬ ∃ c : ℤ, ∀ g ∈ ⋃ j, Nivat.Colle35.hatOf A kk vl j, dot ν g ≤ c := by
  rintro ⟨c, hc⟩
  obtain ⟨z, hz, hzc⟩ :=
    exists_mem_iUnion_hatOf_dot_gt (kk := kk) hitem hsubBA hperp hνvl hz₀ c
  exact absurd (hc z hz) (not_le.mpr hzc)

/-! ## §2.  The contrapositive: a nonempty face pins the sign -/

/-- **A nonempty face of `⋃ j, Â_j` in direction `ν` forces `0 ≤ ⟪ν, v⃗_ℓ⟫`.**  A nonempty face
is exactly an *attained* upper bound for `⟪ν, ·⟫`, which `not_bddAbove_dot_of_strict_wall`
forbids when `⟪ν, v⃗_ℓ⟫ < 0`.  Same binders as §1, plus the face. -/
theorem dot_vl_nonneg_of_face_nonempty {A B : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ}
    {nℓ vl ν : ℤ × ℤ} {cz : ℤ}
    (hitem : Nivat.Colle35.ItemII B nℓ cz) (hsubBA : ∀ i, B i ⊆ A i)
    (hperp : dot nℓ vl = 0)
    {z₀ : ℤ × ℤ} (hz₀ : cz ≤ dot nℓ z₀)
    (hface : (face (⋃ j, Nivat.Colle35.hatOf A kk vl j) ν).Nonempty) :
    0 ≤ dot ν vl := by
  obtain ⟨z, hzmem, hzmax⟩ := hface
  rcases le_or_gt 0 (dot ν vl) with h | h
  · exact h
  · exact absurd ⟨dot ν z, hzmax⟩
      (not_bddAbove_dot_of_strict_wall (kk := kk) hitem hsubBA hperp h hz₀)

/-- **The `Finite` shape, with the repair made explicit.**  `Finite` alone does **not** suffice:
the empty face is finite, and the face is empty at exactly the normals §1 makes unbounded.  The
nonemptiness has to be carried, so it is a binder here.  (`collar_finite` in
`tmp/wip/lane-leafa-gen-fillcover-depth.lean` already carries `hfne`, so nothing is lost.) -/
theorem dot_vl_nonneg_of_face_finite_nonempty {A B : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ}
    {nℓ vl ν : ℤ × ℤ} {cz : ℤ}
    (hitem : Nivat.Colle35.ItemII B nℓ cz) (hsubBA : ∀ i, B i ⊆ A i)
    (hperp : dot nℓ vl = 0)
    {z₀ : ℤ × ℤ} (hz₀ : cz ≤ dot nℓ z₀)
    (hfne : (face (⋃ j, Nivat.Colle35.hatOf A kk vl j) ν).Nonempty)
    (_hffin : (face (⋃ j, Nivat.Colle35.hatOf A kk vl j) ν).Finite) :
    0 ≤ dot ν vl :=
  dot_vl_nonneg_of_face_nonempty (kk := kk) hitem hsubBA hperp hz₀ hfne

/-! ## §3.  Degeneracy checks on the sweep direction

Two arithmetic facts whose only job is to certify that a proposed counterexample instance is
**illegal**, so that no conclusion is drawn from a vacuous premise.  `b3_colle2.txt:497` gives
`v⃗_ℓ = dir(-ν_ℓ)` and `:517` gives `w = -v⃗_{ℓ_{J+1}} = -dir(ν_{J+1})`; when those two coincide
the escaping-wall condition `⟪ν, v⃗_ℓ⟫ ≤ 0 ∧ 0 < ⟪ν, w⟫` is unsatisfiable. -/

/-- **When `w = v⃗_ℓ` the escaping-wall condition is empty.** -/
theorem wall_key_vacuous_of_w_eq_vl {vl w ν : ℤ × ℤ} (hwvl : w = vl)
    (h1 : dot ν vl ≤ 0) (h2 : 0 < dot ν w) : False := by
  rw [hwvl] at h2; omega

/-- **The degenerate branch at `ν_ℓ = (1,-1)`.**  There `v⃗_ℓ = dir(-ν_ℓ) = (-1,-1)`, the only
`ν_{J+1}` with `w = -dir(ν_{J+1}) = (-1,-1)` is `ν_{J+1} = ν_ℓ`, and then `0 < det ν_{J+1} ν_ℓ`
is false — so an instance built on those vectors satisfies neither the fan side conditions nor
(by `wall_key_vacuous_of_w_eq_vl`) the escaping-wall premise. -/
theorem degenerate_at_one_neg_one :
    dir (-((1 : ℤ), (-1 : ℤ))) = ((-1 : ℤ), (-1 : ℤ)) ∧
    -(dir ((1 : ℤ), (-1 : ℤ))) = ((-1 : ℤ), (-1 : ℤ)) ∧
    ¬ ((0 : ℤ) < det ((1 : ℤ), (-1 : ℤ)) ((1 : ℤ), (-1 : ℤ))) := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [dir]
  · norm_num [dir]
  · simp only [det]; omega

end Nivat.WallBound

/-! ## 公理收据（集成者，第 168 轮） -/

#print axioms Nivat.WallBound.exists_mem_iUnion_hatOf_dot_gt
#print axioms Nivat.WallBound.not_bddAbove_dot_of_strict_wall
#print axioms Nivat.WallBound.dot_vl_nonneg_of_face_nonempty
#print axioms Nivat.WallBound.dot_vl_nonneg_of_face_finite_nonempty
#print axioms Nivat.WallBound.wall_key_vacuous_of_w_eq_vl
#print axioms Nivat.WallBound.degenerate_at_one_neg_one
