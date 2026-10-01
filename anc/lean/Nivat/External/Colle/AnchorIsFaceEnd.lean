/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.LeafAWire
import Nivat.External.Colle.PolyChain

/-!
# `anchor_is_face_end` — pinning `hg₁` via `LeafAWire.anchorPoint`

Team-lead's 2026-09-22 instruction (to lane-leafa): close the `hg₁` gap in
`tmp/wip/LeafAAssemble.lean` (line 227) using `g₁ := LeafAWire.anchorPoint`.

The unconditional fact, from `kkOf_max`/`kkOf_mem` (`LeafAWire.lean:203-233`): `g₁ := anchorPoint`
lies in `hatOf (chA c s₀) (kkOf …) vl i` for *every* `i` (`g₁_mem_hatOf`), and `g₁ + vl` does
*not* (else `kkOf_max` would force `kkOf i + 1 ≤ kkOf i`). I.e. `g₁` is exactly the point of
`hatOf … i` that cannot be extended one more step along `vl` — for every `i` uniformly.

**Sign dependency (flagged to team-lead, confirmed genuinely necessary, not a free case split;
same shape as `HsuppCaseCW.g_eq_faceStart_or_faceEnd`'s `det u' vl = ±1` fork).** Whether `g₁`
equals `faceStart (hatOf … i) (−nℓ)` (the `cw`/`exists_gJ_pinned_cw` shape) or
`faceStart (hatOf … i) (−nℓ) + faceLen (hatOf … i) (−nℓ) • dir (−nℓ)` (the `ccw`/
`exists_gJ_pinned_ccw` shape) depends on whether `dir (−nℓ) = −vl` or `dir (−nℓ) = vl`
(`ShellRegionJ.dir_nℓ_eq_or_neg_vl`). This file proves the `dir (−nℓ) = −vl` branch in full
(`anchor_is_faceStart`).

**Update (lane-chaindata-lead, 2026-09-22): the mirror branch is now proved too.**  The
`dir (−nℓ) = vl` case (giving the `ccw`/`+faceLen•dir` shape that `exists_gJ_pinned_ccw` wants)
is `anchor_is_faceEnd` at the bottom of this file, via the abstract
`faceEnd_eq_of_add_dir_not_mem`.  This file's earlier note that it "would need the *upper*
bound `t ≤ faceLen` from `face_eq_segment`" was exactly right — that is the one extra ingredient,
and `PolyChain.face_eq_segment` supplies it, so the mirror is four lines rather than a new
argument.  Neither branch is a `sorry` any more.

Both directions additionally need `g₁ ∈ face (hatOf … i) (−nℓ)` and `−nℓ ∈ E (hatOf … i)` as
hypotheses — these are the "bottom face is the level-`cz` row" facts team-lead cites; NOT
discharged here (this file only supplies the `mem_of_between`/`kkOf_max` algebra once those are
in hand), left as explicit hypotheses `hEdge`/`hmemFace` for the call site in `LeafAAssemble.lean`
to supply.
-/

namespace Nivat.LeafAWire

open Nivat Nivat.LE2 Nivat.Colle35 Nivat.PolyChain

variable {ξ xper : Config ℤ} {S : Finset (ℤ × ℤ)} {vl nℓ : ℤ × ℤ} {cz : ℤ}
variable (c : AenvfixProbe.Ctx ξ xper S vl nℓ) (s₀ : AenvfixProbe.St ξ xper S nℓ cz)
variable (hvl : vl ≠ 0) (hperp : dot nℓ vl = 0)
variable (hne : (AenvfixProbe.chA c s₀ 0).Nonempty)

/-- `g₁ + vl` is never in `hatOf … i`: the unconditional half of `anchor_is_faceStart`,
extracted since it is also what the mirror (`ccw`) branch will need. -/
theorem anchorPoint_add_vl_not_mem (i : ℕ) :
    anchorPoint c s₀ hne + vl ∉ hatOf (AenvfixProbe.chA c s₀) (kkOf c s₀ hvl hperp hne) vl i := by
  intro hmem
  rw [hatOf_eq, Set.mem_ofPred_eq] at hmem
  have hcast : anchorPoint c s₀ hne
      + ((kkOf c s₀ hvl hperp hne i + 1 : ℕ) : ℤ) • vl ∈ AenvfixProbe.chA c s₀ i := by
    push_cast
    have : anchorPoint c s₀ hne + vl + (kkOf c s₀ hvl hperp hne i : ℤ) • vl
        = anchorPoint c s₀ hne
          + ((kkOf c s₀ hvl hperp hne i : ℤ) + 1) • vl := by
      rw [add_smul, one_smul]; abel
    rwa [this] at hmem
  have := kkOf_max c s₀ hvl hperp hne i (kkOf c s₀ hvl hperp hne i + 1) hcast
  omega

/-- The `cw` branch: if `dir (−nℓ) = −vl`, `g₁ := anchorPoint` is exactly `faceStart` of the
`−nℓ`-face of `hatOf … i`, for every `i` — the `hg₁` hypothesis `exists_gJ_pinned_cw` wants. -/
theorem anchor_is_faceStart (i : ℕ)
    (hEdge : (-nℓ) ∈ Nivat.LE2.E
      (hatOf (AenvfixProbe.chA c s₀) (kkOf c s₀ hvl hperp hne) vl i))
    (hmemFace : anchorPoint c s₀ hne ∈ Nivat.LE2.face
      (hatOf (AenvfixProbe.chA c s₀) (kkOf c s₀ hvl hperp hne) vl i) (-nℓ))
    (hdir : Nivat.LE2.dir (-nℓ) = -vl)
    (hfin : (hatOf (AenvfixProbe.chA c s₀) (kkOf c s₀ hvl hperp hne) vl i).Finite)
    (hlc : IsLatticeConvexRegion
      (hatOf (AenvfixProbe.chA c s₀) (kkOf c s₀ hvl hperp hne) vl i)) :
    Nivat.PolyChain.faceStart
      (hatOf (AenvfixProbe.chA c s₀) (kkOf c s₀ hvl hperp hne) vl i) (-nℓ)
      = anchorPoint c s₀ hne := by
  set T := hatOf (AenvfixProbe.chA c s₀) (kkOf c s₀ hvl hperp hne) vl i with hT_def
  obtain ⟨t, ht⟩ := Nivat.PolyChain.exists_nat_shift_of_mem_face hfin hEdge hmemFace
  -- `ht : anchorPoint = faceStart T (-nℓ) + (t : ℤ) • dir (-nℓ)`
  rw [hdir] at ht
  have hfs : Nivat.PolyChain.faceStart T (-nℓ) = anchorPoint c s₀ hne + (t : ℤ) • vl := by
    have h2 : anchorPoint c s₀ hne - (t : ℤ) • (-vl) = Nivat.PolyChain.faceStart T (-nℓ) := by
      rw [ht]; abel
    rw [smul_neg, sub_neg_eq_add] at h2
    exact h2.symm
  have ht0 : t = 0 := by
    by_contra ht0
    have ht1 : 1 ≤ t := Nat.one_le_iff_ne_zero.mpr ht0
    have hs : anchorPoint c s₀ hne + (0 : ℤ) • vl ∈ T := by
      simpa using g₁_mem_hatOf c s₀ hvl hperp hne i
    have hu : anchorPoint c s₀ hne + (t : ℤ) • vl ∈ T := by
      rw [← hfs]
      exact Nivat.LE2.face_subset T (-nℓ) (Nivat.PolyChain.faceStart_mem hfin hEdge)
    have h1le : (0 : ℤ) ≤ 1 := by norm_num
    have h2le : (1 : ℤ) ≤ (t : ℤ) := by exact_mod_cast ht1
    have := Nivat.LE2.mem_of_between hlc hs hu h1le h2le
    exact anchorPoint_add_vl_not_mem c s₀ hvl hperp hne i (by simpa using this)
  rw [hfs, ht0]; simp

/-! ## The `ccw` mirror (lane-chaindata-lead, 2026-09-22)

`exists_gJ_pinned_ccw` (`LeafAJSelect.lean:488`) wants its pinned vertex in the shape
`faceStart T ν + faceLen T ν • dir ν` — the ccw *end* of the `ν`-face — where
`anchor_is_faceStart` above delivers the ccw *start*.  Which of the two `anchorPoint` is
depends only on the sign `dir ν = ±vl`; this section does the `dir ν = vl` half.

The argument is not about `anchorPoint` at all, so it is stated abstractly first: on a finite
lattice-convex `T`, a point of `face T ν` that cannot be pushed one more step along `dir ν`
without leaving `T` *is* the far endpoint of that face.  `face_eq_segment` is what makes this
work — it gives the upper bound `t ≤ faceLen T ν` that `exists_nat_shift_of_mem_face` alone
does not. -/

section CcwMirror

/-- **A point of an edge face that cannot advance along `dir ν` is the face's far endpoint.**
`face T ν` is exactly the lattice segment `faceStart + [0, faceLen] • dir ν`
(`PolyChain.face_eq_segment`), so a member sitting at parameter `t < faceLen` has its successor
`faceStart + (t+1) • dir ν` still inside the face, hence inside `T`.  Contrapositive: if the
successor is outside `T`, then `t = faceLen`. -/
theorem faceEnd_eq_of_add_dir_not_mem {T : Set (ℤ × ℤ)} {ν a : ℤ × ℤ}
    (hlc : IsLatticeConvexRegion T) (hfin : T.Finite) (hν : ν ∈ Nivat.LE2.E T)
    (ha : a ∈ Nivat.LE2.face T ν) (hstop : a + dir ν ∉ T) :
    Nivat.PolyChain.faceStart T ν + (Nivat.PolyChain.faceLen T ν : ℤ) • dir ν = a := by
  obtain ⟨t, htle, ht⟩ := by
    rw [Nivat.PolyChain.face_eq_segment hlc hfin hν] at ha; exact ha
  have hteq : t = Nivat.PolyChain.faceLen T ν := by
    by_contra hne'
    have hlt : t + 1 ≤ Nivat.PolyChain.faceLen T ν := by omega
    have hsucc : a + dir ν ∈ Nivat.LE2.face T ν := by
      rw [Nivat.PolyChain.face_eq_segment hlc hfin hν]
      refine ⟨t + 1, hlt, ?_⟩
      rw [ht]
      push_cast
      rw [add_smul, one_smul]
      abel
    exact hstop (Nivat.LE2.face_subset T ν hsucc)
  rw [ht, hteq]

end CcwMirror

section AnchorCcw

variable {ξ xper : Config ℤ} {S : Finset (ℤ × ℤ)} {vl nℓ : ℤ × ℤ} {cz : ℤ}
variable (c : AenvfixProbe.Ctx ξ xper S vl nℓ) (s₀ : AenvfixProbe.St ξ xper S nℓ cz)
variable (hvl : vl ≠ 0) (hperp : dot nℓ vl = 0)
variable (hne : (AenvfixProbe.chA c s₀ 0).Nonempty)

/-- **The `ccw` branch**: if `dir (−nℓ) = vl`, then `g₁ := anchorPoint` is the ccw *end* of the
`−nℓ`-face of `hatOf … i`, for every `i` — exactly the `hg₁` hypothesis
`LeafAJSelect.exists_gJ_pinned_ccw` takes at `ℓ := −nℓ`.

`hstop` is `anchorPoint_add_vl_not_mem` transported across `hdir`; everything else is
`faceEnd_eq_of_add_dir_not_mem`.  The two hypotheses `hEdge` / `hmemFace` are the same ones
`anchor_is_faceStart` leaves to its call site (`−nℓ ∈ E (hatOf … i)` is
`AhatEnv.E_eq_of_enveloped` plus `−nℓ ∈ E ↑S`; membership of the bottom face is
`anchorPoint_level` plus `Exhausts`). -/
theorem anchor_is_faceEnd (i : ℕ)
    (hEdge : (-nℓ) ∈ Nivat.LE2.E
      (hatOf (AenvfixProbe.chA c s₀) (kkOf c s₀ hvl hperp hne) vl i))
    (hmemFace : anchorPoint c s₀ hne ∈ Nivat.LE2.face
      (hatOf (AenvfixProbe.chA c s₀) (kkOf c s₀ hvl hperp hne) vl i) (-nℓ))
    (hdir : Nivat.LE2.dir (-nℓ) = vl)
    (hfin : (hatOf (AenvfixProbe.chA c s₀) (kkOf c s₀ hvl hperp hne) vl i).Finite)
    (hlc : IsLatticeConvexRegion
      (hatOf (AenvfixProbe.chA c s₀) (kkOf c s₀ hvl hperp hne) vl i)) :
    Nivat.PolyChain.faceStart
      (hatOf (AenvfixProbe.chA c s₀) (kkOf c s₀ hvl hperp hne) vl i) (-nℓ)
      + (Nivat.PolyChain.faceLen
          (hatOf (AenvfixProbe.chA c s₀) (kkOf c s₀ hvl hperp hne) vl i) (-nℓ) : ℤ)
        • Nivat.LE2.dir (-nℓ)
      = anchorPoint c s₀ hne := by
  refine faceEnd_eq_of_add_dir_not_mem hlc hfin hEdge hmemFace ?_
  rw [hdir]
  exact anchorPoint_add_vl_not_mem c s₀ hvl hperp hne i

end AnchorCcw

end Nivat.LeafAWire

#print axioms Nivat.LeafAWire.anchorPoint_add_vl_not_mem
#print axioms Nivat.LeafAWire.anchor_is_faceStart
#print axioms Nivat.LeafAWire.faceEnd_eq_of_add_dir_not_mem
#print axioms Nivat.LeafAWire.anchor_is_faceEnd
