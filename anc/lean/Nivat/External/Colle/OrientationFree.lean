/-
Copyright (c) 2026. Released under Apache 2.0 license.
Authors: integrator
-/
import Nivat.External.Colle.Lemma45

/-!
# The orientation bit of `exists_preamble` is genuinely free

Integrator adjudication, 2026-09-24, of the three-way lane disagreement about the sign of
`det nℓ vl` (equivalently: whether `dir (-nℓ) = vl` (ccw) or `= -vl` (cw), the fork named
verbatim at `LeafAFaceRev.lean:25-30`).

## What the producer actually does

`ColleReg.exists_preamble` (`RegionSteps.lean:593`) and `exists_preamble_pair` (`:785`):

* `:629` `set v₀ : ℤ × ℤ := (-ℓ.2, ℓ.1)` — this is `LE2.dir ℓ`, and it is the exported `vl`
  **unconditionally**, in both branches (`:727`, `:760`).
* `:723` `by_cases hle : (S.filter fun z => inner2 w₀ z = cmin).card ≤ (… = cmax).card`
  chooses only the *partner normal* `nℓ`: `:728` instantiates `nℓ := ℓ`, `:761` `nℓ := -ℓ`.

So the cw/ccw fork **is** the `hle` fork, and `hle` is a cardinality comparison between the two
extreme faces of the Lemma 2.4 generating set `S` — undischarged, and deliberately not
exported (`:587-589` verbatim: "the inequality is not exported"; `:554-557`: "Exporting
instead an inequality relating the agreement half plane to `ℓ` would be exactly the mistake
this paragraph forbids").

`branch_one_det_pos` / `branch_two_det_neg` below pin the sign in each branch, so the fork is
now kernel-visible rather than argued: `0 < det nℓ vl` in branch 1, `det nℓ vl < 0` in branch 2.

## Why it cannot be derived (two independent reasons)

1. **The input package is `ℓ ↦ -ℓ` symmetric** (`preamble_input_symm`).  `NonExpansiveLine ξ`
   (`Lemma45.lean:85`) is `Primitive v ∧ (the body of `IsOneSidedNonexpansive`)`, and
   `Primitive = IsCoprime` (`Config.lean:156`) is `±`-invariant, so `exists_preamble`'s
   hypotheses amount to `Primitive ℓ ∧ IOSN ξ ℓ ∧ IOSN ξ (-ℓ)` — invariant under `ℓ ↦ -ℓ`
   (`hw`/`hw₁`/`hw₂` do not mention `ℓ` at all).  Feeding `-ℓ` instead of `ℓ` swaps `cmin`/`cmax`,
   hence flips `hle`, hence flips the branch, while negating `v₀`; so the *same* `ξ` yields both
   signs depending only on which of the two equally-admissible inputs the caller supplies.
   A sign that is not a function of `ξ` cannot be derived from `ξ`.

2. **The exported conclusion is `vl ↦ -vl` symmetric** (`preamble_output_vl_neg`).  Every
   conjunct of `exists_preamble`'s conclusion that mentions `vl` — `vl ≠ 0`, `Primitive vl`,
   `det p vl = 0`, `dot ℓ vl = 0`, and the partner block's `nℓ ≠ 0 ∧ dot nℓ vl = 0` — survives
   `vl ↦ -vl` unchanged, while `det nℓ vl` flips.  So no *consumer* can recover the sign from
   the interface either, independently of how the producer is implemented.

## Where the "it is derivable" argument goes wrong

The refuted argument reads Collé's `ℋ(ℓ)` at `b3_colle2.txt:98`:

> `ℋ(ℓ) := {g ∈ ℤ² : ⟨g,(-u₂,u₁)⟩ ≥ 0}`, where `(u₁,u₂)` is a non-zero vector **parallel to
> `ℓ`** … following the orientation of `ℓ`, the interior of `ℋ(ℓ)` is on the left.

There `ℓ` is an **oriented line** and `u` is its *tangent*, so the paper's inner normal is
`dir u`.  The Lean `ℓ` is a **normal** throughout (`RegionSteps.lean:566` verbatim), and the
Lean tangent is `vl`; hence the paper's normal reads `dir vl = dir (dir ℓ) = -ℓ`
(`dir_dir_eq_neg` below).  That is a consistent dictionary — but it converts the paper's *orientation
of the line* into the sign of the Lean `ℓ`, and that datum is exactly what the Lean hypotheses
drop: `hℓ_pos`/`hℓ_neg` assert one-sided nonexpansiveness at `ℓ` **and** at `-ℓ`, the
un-oriented statement.  `preamble_input_symm` is that observation, compiled.

## Consequence for the consumer

**None — the bit is pinned at the producer instead.** (Corrected 2026-09-24, same day, after
lane-tower-hbase refuted the integrator's first reading of this file.)

What §3–§4 prove is that the sign is not exported by the interface *as it stood*.  The
integrator first read that as "so the consumer must be branch-agnostic".  That inference is
wrong, and `preamble_output_vl_neg` below is itself the reason: because every `vl`-mentioning
conjunct survives `vl ↦ -vl`, the `¬hle` branch of `exists_preamble` may hand `-v₀` instead of
`v₀` **at zero proof cost**.  Doing so makes `vl = dir nℓ` in both branches, so
`det nℓ vl = ‖nℓ‖² > 0` unconditionally — by `det_self_dir_pos` below, the same lemma on both
sides.  That normalisation landed in `RegionSteps.lean` (see its "the ⚠ above has now fired"
section) and `exists_preamble` / `exists_preamble_pair` / `exists_chainData`'s `hpartner` now
carry `0 < det nℓ vl`.

It had to be pinned rather than left free because several downstream facts are *signed* in this
datum, and the interface as it stood could not supply any of them:

* `dir vl = -nℓ` — the normal/tangent dictionary, pinned rather than up to sign
  (`LaneTowerPkgRegion.dir_vl_eq_neg_nl`).
* `0 < det vl w` — from the prefix-free identity
  `det nℓ vl * det vl w + dot nℓ w * ‖vl‖² = dot nℓ vl * dot vl w` plus `dot nℓ vl = 0` and the
  tower package's `dot nℓ w < 0` (`hwneg`, in the `obtain` at `RegionSteps.lean:1949`).  This is `LE2.IsRegion`'s `detPos`
  (`LatticeEdges.lean:2300`) in the orientation `(vl, w)`.
* `det u' vl = -1` — `dot nℓ vl = 0` with `Primitive vl` forces `nℓ = k • dir vl`, then
  `hnu : dot nℓ u' = -1` (`exists_cutResidualR_of_claim46`'s binder, `RegionSteps.lean:1920`)
  gives `k * det u' vl = 1` and this sign gives
  `k = -1`, killing the other disjunct of `hunimod` (same binder table, `:1904`).

⚠ **Corrected 2026-09-24, same day.**  The first version of this section instead named
`Hole3Room.nlmax_of_wadj`'s `hmvl : 0 < dot m vl` (`Hole3Room.lean:321`) as the consumer.  That
is a *different vector*: `m` is the cut normal (`dot m w = 0`), not `nℓ` (`dot nℓ vl = 0`), and
`hmvl` is already discharged by the tower package — it is a component of the `obtain` at
`RegionSteps.lean:1949`.  The `ha_min`
min→max remark that accompanied it was about the same mistaken reading and is withdrawn.

⚠ The chain's `0 < det vl w` is **our** convention, not the paper's: lane-towerpkg's rig reads
the paper side as `det vl w = -1 < 0`.  Until "chain `vl` = paper `v⃗_{ℓ_ι}`" is proved, signed
paper-side facts about `det vl w` must not be imported into the chain.

⟹ The general rule, recorded as `PROTOCOL.md` §54: "we found no source for this datum" proves
only that the *current* interface drops it.  Ask whether the producer can normalise before
concluding the consumer must live without it.  `Colle35.FaceBlock.reverse`
(`LeafAFaceRev.lean:69`) remains available if a genuinely two-sided consumer ever appears, but
it is not needed here.
-/

set_option autoImplicit false

namespace Nivat.ColleOrient

open Nivat Nivat.LE2

/-! ## §1  `dir` algebra -/

/-- `dir ∘ dir = -id`.  Used above to translate `b3_colle2.txt:98`'s tangent-built normal
`(-u₂,u₁)` back to the Lean normal: at `vl = dir ℓ` it reads `-ℓ`, not `ℓ`. -/
theorem dir_dir_eq_neg (n : ℤ × ℤ) : dir (dir n) = -n := by
  obtain ⟨a, b⟩ := n
  simp [dir]

/-- The exported `vl` of `exists_preamble` (`RegionSteps.lean:629`, `set v₀ := (-ℓ.2, ℓ.1)`)
is `dir ℓ` on the nose. -/
theorem v0_eq_dir (l : ℤ × ℤ) : ((-l.2, l.1) : ℤ × ℤ) = dir l := rfl

theorem det_self_dir (n : ℤ × ℤ) : det n (dir n) = n.1 * n.1 + n.2 * n.2 := by
  simp only [det, dir]; ring

theorem ne_zero_cases {n : ℤ × ℤ} (h : n ≠ 0) : n.1 ≠ 0 ∨ n.2 ≠ 0 := by
  by_contra hc
  push_neg at hc
  exact h (Prod.ext hc.1 hc.2)

/-- `det n (dir n) = ‖n‖² > 0`. -/
theorem det_self_dir_pos {n : ℤ × ℤ} (h : n ≠ 0) : 0 < det n (dir n) := by
  rw [det_self_dir]
  rcases ne_zero_cases h with h1 | h2
  · nlinarith [mul_self_nonneg n.2, mul_self_pos.mpr h1]
  · nlinarith [mul_self_nonneg n.1, mul_self_pos.mpr h2]

/-! ## §2  The two branches of `exists_preamble`'s `by_cases hle` (`RegionSteps.lean:723`) -/

/-- **Branch 1** (`hle` true, `RegionSteps.lean:727-729`): the producer returns `nℓ := ℓ` and
`vl := dir ℓ`, so `0 < det nℓ vl`, i.e. `dir (-nℓ) = -vl` — the **cw** row of
`LeafAFaceRev.lean:28-30`. -/
theorem branch_one_det_pos {l nl vl : ℤ × ℤ} (h : l ≠ 0) (hnl : nl = l) (hvl : vl = dir l) :
    0 < det nl vl := by
  subst hnl; subst hvl; exact det_self_dir_pos h

/-- **Branch 2** (`hle` false, `RegionSteps.lean:760-763`): the producer returns `nℓ := -ℓ` and
the *same* `vl := dir ℓ`, so `det nℓ vl < 0`, i.e. `dir (-nℓ) = vl` — the **ccw** row of
`LeafAFaceRev.lean:25-27`. -/
theorem branch_two_det_neg {l nl vl : ℤ × ℤ} (h : l ≠ 0) (hnl : nl = -l) (hvl : vl = dir l) :
    det nl vl < 0 := by
  subst hnl; subst hvl
  have hpos := det_self_dir_pos h
  have hflip : det (-l) (dir l) = -det l (dir l) := by
    simp only [det, dir, Prod.fst_neg, Prod.snd_neg]; ring
  omega

/-- The two branches are genuinely opposite: no single sign covers both. -/
theorem branches_disagree {l : ℤ × ℤ} (h : l ≠ 0) :
    0 < det l (dir l) ∧ det (-l) (dir l) < 0 :=
  ⟨det_self_dir_pos h, branch_two_det_neg h rfl rfl⟩

/-! ## §3  Reason 1: the input package is `ℓ ↦ -ℓ` symmetric -/

theorem primitive_neg_iff {v : ℤ × ℤ} : Primitive (-v) ↔ Primitive v := by
  unfold Primitive
  simp only [Prod.fst_neg, Prod.snd_neg]
  constructor
  · intro h; simpa only [neg_neg] using h.neg_neg
  · intro h; exact h.neg_neg

/-- `NonExpansiveLine` (`Lemma45.lean:85`) is `Primitive` together with the body of
`IsOneSidedNonexpansive` (`Lemma45.lean:95`); `halfPlaneLE v 0` unfolds to `dot v · ≤ 0`. -/
theorem mem_nel_iff (ξ : Config ℤ) (l : ℤ × ℤ) :
    l ∈ Colle45.NonExpansiveLine ξ ↔ Primitive l ∧ Colle45.IsOneSidedNonexpansive ξ l :=
  Iff.rfl

/-- **The hypothesis package of `exists_preamble` is invariant under `ℓ ↦ -ℓ`.**  `hw`, `hw₁`,
`hw₂` do not mention `ℓ`; the remaining three hypotheses are exactly this conjunction. -/
theorem preamble_input_symm (ξ : Config ℤ) (l : ℤ × ℤ) :
    (l ∈ Colle45.NonExpansiveLine ξ ∧ Colle45.IsOneSidedNonexpansive ξ l ∧
      Colle45.IsOneSidedNonexpansive ξ (-l)) ↔
    ((-l) ∈ Colle45.NonExpansiveLine ξ ∧ Colle45.IsOneSidedNonexpansive ξ (-l) ∧
      Colle45.IsOneSidedNonexpansive ξ (-(-l))) := by
  rw [mem_nel_iff, mem_nel_iff, primitive_neg_iff, neg_neg]
  constructor
  · rintro ⟨⟨hp, h1⟩, -, h2⟩; exact ⟨⟨hp, h2⟩, h2, h1⟩
  · rintro ⟨⟨hp, h2⟩, -, h1⟩; exact ⟨⟨hp, h1⟩, h1, h2⟩

/-! ## §4  Reason 2: the exported conclusion is `vl ↦ -vl` symmetric -/

/-- **Every `vl`-mentioning conjunct of `exists_preamble`'s conclusion survives `vl ↦ -vl`,
while `det nℓ vl` flips.**  So a consumer of the interface cannot recover the sign either,
whatever the producer does internally. -/
theorem preamble_output_vl_neg {l p nl vl : ℤ × ℤ}
    (h0 : vl ≠ 0) (hprim : Primitive vl) (hdp : det p vl = 0) (hdl : dot l vl = 0)
    (hn0 : nl ≠ 0) (hnv : dot nl vl = 0) :
    ((-vl) ≠ 0 ∧ Primitive (-vl) ∧ det p (-vl) = 0 ∧ dot l (-vl) = 0 ∧
      nl ≠ 0 ∧ dot nl (-vl) = 0) ∧ det nl (-vl) = -det nl vl := by
  refine ⟨⟨neg_ne_zero.mpr h0, primitive_neg_iff.mpr hprim, ?_, ?_, hn0, ?_⟩, ?_⟩
  · simp only [det, Prod.fst_neg, Prod.snd_neg] at hdp ⊢; linarith
  · simp only [dot, Prod.fst_neg, Prod.snd_neg] at hdl ⊢; linarith
  · simp only [dot, Prod.fst_neg, Prod.snd_neg] at hnv ⊢; linarith
  · simp only [det, Prod.fst_neg, Prod.snd_neg]; ring

/-- The sign of `det nℓ vl` is not determined by the exported data: the flipped datum satisfies
the identical conjuncts with the opposite sign. -/
theorem det_nl_vl_sign_free {nl vl : ℤ × ℤ} (h : det nl vl ≠ 0) :
    (0 < det nl vl ∧ det nl (-vl) < 0) ∨ (det nl vl < 0 ∧ 0 < det nl (-vl)) := by
  have hflip : det nl (-vl) = -det nl vl := by simp only [det, Prod.fst_neg, Prod.snd_neg]; ring
  rcases lt_or_gt_of_ne h with hneg | hpos
  · exact Or.inr ⟨hneg, by omega⟩
  · exact Or.inl ⟨hpos, by omega⟩

end Nivat.ColleOrient

#print axioms Nivat.ColleOrient.dir_dir_eq_neg
#print axioms Nivat.ColleOrient.v0_eq_dir
#print axioms Nivat.ColleOrient.det_self_dir_pos
#print axioms Nivat.ColleOrient.branch_one_det_pos
#print axioms Nivat.ColleOrient.branch_two_det_neg
#print axioms Nivat.ColleOrient.branches_disagree
#print axioms Nivat.ColleOrient.primitive_neg_iff
#print axioms Nivat.ColleOrient.mem_nel_iff
#print axioms Nivat.ColleOrient.preamble_input_symm
#print axioms Nivat.ColleOrient.preamble_output_vl_neg
#print axioms Nivat.ColleOrient.det_nl_vl_sign_free
