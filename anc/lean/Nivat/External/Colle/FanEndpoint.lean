/-
Copyright (c) 2026. Released under Apache 2.0 license.
Authors: lane-cd-substrip (§1), lane-chaindata-lead (§2)
-/
import Nivat.External.Colle.PolyChain
import Nivat.External.Colle.ANormal

/-!
# Fan-adjacent endpoints: the shared vertex of two adjacent faces, and `hSnp`

Consumer: the `hSnp` hypothesis of `hseedS_of_parts` (`tmp/wip/lane-cd-bottom.lean`), which
discharges the `hseedS` half of the `bottom` binder of
`Nivat.Colle35.ChainDataGeom.ofPartsExhaustsInter` (`ChainExhaustInter.lean`), consumed at
`tmp/wip/LeafAAssemble.lean`'s `(bottom := by sorry)`.

## §1 vs §2

§1 is the geometry, extracted verbatim from `tmp/wip/lane-cd-substrip.lean` §11 (lane
`lane-cd-substrip`, 2026-09-23, verified EXIT=0 and axiom-clean there and again here): two
fan-adjacent edge normals of a finite lattice-convex region share a vertex, and under
`dot nprev vJ < 0` that vertex is the endpoint `a` from which the `nJ`-face is parametrised.
Nothing in §1 mentions `FaceBlock`.

§2 is the bridge to the chain's own objects.  It is the piece that makes §1 usable: it turns
the two abstract hypotheses `ha` (`a` is on the `nJ`-face) and `hfaceparam` (the `nJ`-face is
`a + ℕ • vJ`) into projections of a `FaceBlock`, and packages the two orientations so the
caller splits its `hadj_or` disjunction once, here, instead of at every use site.

## The sign trap this file is built around (硬规矩 6)

`FaceBlock S n v` (`ANormal.lean:584-610`) has `lex` maximising `dot (-n)` at `a`.  At the
assembly's call site the prescribed normal is `n := nJ = -J`, so `-n = J` and **`F.a` lies on
the `J`-face, not on the `nJ`-face**.  Every §2 statement below is therefore phrased with `J`,
and `F : FaceBlock S (-J) vJ`.  Feeding `nJ` where `J` belongs silently reverses two
determinants at once and still typechecks; that is the whole reason §2 exists as a lemma
rather than as inline `have`s.

Worked instance, by hand, before any Lean was written.  Take `S = ApexUnique.Shex`
(`= ShellSweep.hexShape 2 2 1 1 0`, a genuine reachable window: `E ↑Sphi` is negation-closed by
`Colle35.Sphi_negSymm` (`DecompData.lean:417`), so odd-normal windows such as triangles are
unreachable and a hexagon is the smallest honest test).  Take `J = (0,1)`, so `nJ = -J =
(0,-1)`; `F.a` is then the `dot (0,1)`-maximal, `vJ`-minimal point of `S`, namely `(1,2)` with
`vJ = (1,0)` — and indeed `dot (0,1) (1,2) = 2` is the maximum of `dot (0,1)` over `Shex`,
attained also at `(2,2)= F.a + 1 • vJ`.  Take `nprev = (-1,1)`: `det nprev J = det((-1,1),(0,1))
= (-1)·1 - 1·0 = -1 < 0`, so the **ccw** branch does *not* apply, while `det J nprev =
det((0,1),(-1,1)) = 0·1 - 1·(-1) = 1 > 0`, so the **cw** branch does.  Its sign condition
`dot nprev vJ = dot((-1,1),(1,0)) = -1 < 0` holds.  Conclusion: `F.a = (1,2)` maximises
`dot (-1,1)` over `Shex` — check: `dot (-1,1)` takes values `0,1,-1,0,1,-1,0` at
`(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2)`, maximum `1`, attained at `(0,1)` and `(1,2)`.  So
`F.a` does attain it.  Had we mistakenly used `nJ = (0,-1)` in place of `J`, the far endpoint
`(1,0)` would have come out instead, where `dot (-1,1) (1,0) = -1` is the *minimum* — the error
would have been a sign flip, not a type error.
-/

set_option autoImplicit false

namespace Nivat.FanEndpoint

open Nivat Nivat.LE2

/-! ## §1.  The shared vertex (from `lane-cd-substrip.lean` §11, verbatim)

**Why `hdet` is load-bearing (not decorative).**  Without it the statement is FALSE: with
`nJ = (0,-1)`, `nprev = (3,-1)` inside the ccw-primitive octagon fan
`(2,1),(1,3),(0,1),(-3,-1),(-1,-3),(0,-1),(1,-1),(3,-1)` (angles `26.6°,71.6°,90°,198.4°,
251.6°,270°,315°,341.6°`, all listed normals primitive), one has `det nprev nJ =
det((3,-1),(0,-1)) = 3·(-1) - (-1)·0 = -3 < 0` — i.e. `hdet` FAILS for this `(nprev,nJ)` pair —
while every other hypothesis of the uncorrected (no-`hdet`) statement holds: `hadj` is vacuous
(needs some listed `μ` with `3μ.2+μ.1>0` and `μ.1<0` simultaneously; none of the eight normals
satisfies both), `hfaceparam` holds by taking `vJ = -dir nJ = (-1,0)` (the *end*-branch: `a` is
the `dir nJ`-maximal endpoint of `face T nJ`, not the minimal one), and `hnpvJ = dot((3,-1),
(-1,0)) = -3 < 0`.  But the true ccw successor of `nJ = (0,-1)` in this fan is `(1,-1)` at
315°, not `nprev = (3,-1)` at 341.6°, so the conclusion `a ∈ face T nprev` is false.

The pairing rule for callers: `hdet` and `hadj`'s determinant order must always agree
(`0 < det nprev nJ` with `hadj`'s `nprev`-then-`nJ` clause order for ccw; `0 < det nJ nprev`
with the swapped clause order for cw) — mixing them reopens exactly this hole.  §2's
`hadj_or` hypothesis bundles the two orientations so that a caller cannot mix them. -/

/-- Core lemma, `ccw` orientation: both conclusions in one pass. -/
theorem mem_face_of_adjacent_endpoint_ccw_core {T : Set (ℤ × ℤ)} (hfin : T.Finite)
    (hlc : IsLatticeConvexRegion T) {nJ nprev vJ a : ℤ × ℤ}
    (hnJE : nJ ∈ Nivat.LE2.E T) (hnprevE : nprev ∈ Nivat.LE2.E T)
    (hdet : 0 < det nprev nJ)
    (ha : a ∈ Nivat.LE2.face T nJ)
    (hfaceparam : ∀ b ∈ Nivat.LE2.face T nJ, ∃ j : ℕ, b = a + (j : ℤ) • vJ)
    (hnpvJ : dot nprev vJ < 0)
    (hadj : ∀ μ ∈ Nivat.LE2.E T, ¬(0 < det nprev μ ∧ 0 < det μ nJ)) :
    a ∈ Nivat.LE2.face T nprev ∧ a = Nivat.PolyChain.faceStart T nJ := by
  set Q : ℤ × ℤ := Nivat.PolyChain.faceStart T nprev
      + (Nivat.PolyChain.faceLen T nprev : ℤ) • Nivat.LE2.dir nprev with hQdef
  have hshared : Q = Nivat.PolyChain.faceStart T nJ :=
    Nivat.PolyChain.adjacent_shared_vertex hfin hlc hnprevE hnJE hdet hadj
  have hQprev : Q ∈ face T nprev := Nivat.PolyChain.faceEnd_mem hlc hfin hnprevE
  have hQnJ : Q ∈ face T nJ := by
    rw [hshared]
    have h0 : Nivat.PolyChain.faceStart T nJ
        = Nivat.PolyChain.faceStart T nJ + ((0 : ℕ) : ℤ) • Nivat.LE2.dir nJ := by simp
    rw [h0, Nivat.PolyChain.face_eq_segment hlc hfin hnJE]
    exact ⟨0, Nat.zero_le _, rfl⟩
  obtain ⟨j, hj⟩ := hfaceparam Q hQnJ
  have haT : a ∈ T := Nivat.LE2.face_subset T nJ ha
  have hQmax : dot nprev a ≤ dot nprev Q := (Nivat.LE2.mem_face_iff.mp hQprev).2 a haT
  have hexpand : dot nprev Q = dot nprev a + (j : ℤ) * dot nprev vJ := by
    rw [hj]
    simp only [dot, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  have hj0 : (j : ℤ) = 0 := by
    rcases Nat.eq_zero_or_pos j with hz | hpos
    · exact_mod_cast hz
    · exfalso
      have hjpos : (0:ℤ) < (j : ℤ) := by exact_mod_cast hpos
      nlinarith [mul_pos hjpos (neg_pos.mpr hnpvJ)]
  have hQeqa : Q = a := by rw [hj, hj0]; simp
  refine ⟨hQeqa ▸ hQprev, ?_⟩
  rw [← hQeqa, hshared]

/-- **`mem_face_of_adjacent_endpoint`, `ccw` orientation.** -/
theorem mem_face_of_adjacent_endpoint_ccw {T : Set (ℤ × ℤ)} (hfin : T.Finite)
    (hlc : IsLatticeConvexRegion T) {nJ nprev vJ a : ℤ × ℤ}
    (hnJE : nJ ∈ Nivat.LE2.E T) (hnprevE : nprev ∈ Nivat.LE2.E T)
    (hdet : 0 < det nprev nJ)
    (ha : a ∈ Nivat.LE2.face T nJ)
    (hfaceparam : ∀ b ∈ Nivat.LE2.face T nJ, ∃ j : ℕ, b = a + (j : ℤ) • vJ)
    (hnpvJ : dot nprev vJ < 0)
    (hadj : ∀ μ ∈ Nivat.LE2.E T, ¬(0 < det nprev μ ∧ 0 < det μ nJ)) :
    a ∈ Nivat.LE2.face T nprev :=
  (mem_face_of_adjacent_endpoint_ccw_core hfin hlc hnJE hnprevE hdet ha hfaceparam hnpvJ hadj).1

/-- **Companion corollary**: under the same hypotheses, `a` is exactly `faceStart T nJ`. -/
theorem mem_face_of_adjacent_endpoint_ccw_eq {T : Set (ℤ × ℤ)} (hfin : T.Finite)
    (hlc : IsLatticeConvexRegion T) {nJ nprev vJ a : ℤ × ℤ}
    (hnJE : nJ ∈ Nivat.LE2.E T) (hnprevE : nprev ∈ Nivat.LE2.E T)
    (hdet : 0 < det nprev nJ)
    (ha : a ∈ Nivat.LE2.face T nJ)
    (hfaceparam : ∀ b ∈ Nivat.LE2.face T nJ, ∃ j : ℕ, b = a + (j : ℤ) • vJ)
    (hnpvJ : dot nprev vJ < 0)
    (hadj : ∀ μ ∈ Nivat.LE2.E T, ¬(0 < det nprev μ ∧ 0 < det μ nJ)) :
    a = Nivat.PolyChain.faceStart T nJ :=
  (mem_face_of_adjacent_endpoint_ccw_core hfin hlc hnJE hnprevE hdet ha hfaceparam hnpvJ hadj).2

/-- Core lemma, `cw` orientation: mirror of the `ccw` case with the two normals swapped in
`adjacent_shared_vertex`. -/
theorem mem_face_of_adjacent_endpoint_cw_core {T : Set (ℤ × ℤ)} (hfin : T.Finite)
    (hlc : IsLatticeConvexRegion T) {nJ nprev vJ a : ℤ × ℤ}
    (hnJE : nJ ∈ Nivat.LE2.E T) (hnprevE : nprev ∈ Nivat.LE2.E T)
    (hdet : 0 < det nJ nprev)
    (ha : a ∈ Nivat.LE2.face T nJ)
    (hfaceparam : ∀ b ∈ Nivat.LE2.face T nJ, ∃ j : ℕ, b = a + (j : ℤ) • vJ)
    (hnpvJ : dot nprev vJ < 0)
    (hadj : ∀ μ ∈ Nivat.LE2.E T, ¬(0 < det nJ μ ∧ 0 < det μ nprev)) :
    a ∈ Nivat.LE2.face T nprev ∧
      a = Nivat.PolyChain.faceStart T nJ + (Nivat.PolyChain.faceLen T nJ : ℤ) • Nivat.LE2.dir nJ := by
  set Q : ℤ × ℤ := Nivat.PolyChain.faceStart T nprev with hQdef
  have hshared : Nivat.PolyChain.faceStart T nJ
      + (Nivat.PolyChain.faceLen T nJ : ℤ) • Nivat.LE2.dir nJ = Q :=
    Nivat.PolyChain.adjacent_shared_vertex hfin hlc hnJE hnprevE hdet hadj
  have hQprev : Q ∈ face T nprev := Nivat.PolyChain.faceStart_mem hfin hnprevE
  have hQnJ : Q ∈ face T nJ := by
    rw [← hshared]; exact Nivat.PolyChain.faceEnd_mem hlc hfin hnJE
  obtain ⟨j, hj⟩ := hfaceparam Q hQnJ
  have haT : a ∈ T := Nivat.LE2.face_subset T nJ ha
  have hQmax : dot nprev a ≤ dot nprev Q := (Nivat.LE2.mem_face_iff.mp hQprev).2 a haT
  have hexpand : dot nprev Q = dot nprev a + (j : ℤ) * dot nprev vJ := by
    rw [hj]
    simp only [dot, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  have hj0 : (j : ℤ) = 0 := by
    rcases Nat.eq_zero_or_pos j with hz | hpos
    · exact_mod_cast hz
    · exfalso
      have hjpos : (0:ℤ) < (j : ℤ) := by exact_mod_cast hpos
      nlinarith [mul_pos hjpos (neg_pos.mpr hnpvJ)]
  have hQeqa : Q = a := by rw [hj, hj0]; simp
  exact ⟨hQeqa ▸ hQprev, by rw [← hQeqa, hshared]⟩

/-- **`mem_face_of_adjacent_endpoint`, `cw` orientation.** -/
theorem mem_face_of_adjacent_endpoint_cw {T : Set (ℤ × ℤ)} (hfin : T.Finite)
    (hlc : IsLatticeConvexRegion T) {nJ nprev vJ a : ℤ × ℤ}
    (hnJE : nJ ∈ Nivat.LE2.E T) (hnprevE : nprev ∈ Nivat.LE2.E T)
    (hdet : 0 < det nJ nprev)
    (ha : a ∈ Nivat.LE2.face T nJ)
    (hfaceparam : ∀ b ∈ Nivat.LE2.face T nJ, ∃ j : ℕ, b = a + (j : ℤ) • vJ)
    (hnpvJ : dot nprev vJ < 0)
    (hadj : ∀ μ ∈ Nivat.LE2.E T, ¬(0 < det nJ μ ∧ 0 < det μ nprev)) :
    a ∈ Nivat.LE2.face T nprev :=
  (mem_face_of_adjacent_endpoint_cw_core hfin hlc hnJE hnprevE hdet ha hfaceparam hnpvJ hadj).1

/-- **Companion corollary**, `cw`: `a` is the `nJ`-face's far endpoint. -/
theorem mem_face_of_adjacent_endpoint_cw_eq {T : Set (ℤ × ℤ)} (hfin : T.Finite)
    (hlc : IsLatticeConvexRegion T) {nJ nprev vJ a : ℤ × ℤ}
    (hnJE : nJ ∈ Nivat.LE2.E T) (hnprevE : nprev ∈ Nivat.LE2.E T)
    (hdet : 0 < det nJ nprev)
    (ha : a ∈ Nivat.LE2.face T nJ)
    (hfaceparam : ∀ b ∈ Nivat.LE2.face T nJ, ∃ j : ℕ, b = a + (j : ℤ) • vJ)
    (hnpvJ : dot nprev vJ < 0)
    (hadj : ∀ μ ∈ Nivat.LE2.E T, ¬(0 < det nJ μ ∧ 0 < det μ nprev)) :
    a = Nivat.PolyChain.faceStart T nJ + (Nivat.PolyChain.faceLen T nJ : ℤ) • Nivat.LE2.dir nJ :=
  (mem_face_of_adjacent_endpoint_cw_core hfin hlc hnJE hnprevE hdet ha hfaceparam hnpvJ hadj).2

/-! ## §2.  The `FaceBlock` bridge

The two abstract hypotheses of §1 are projections of a `FaceBlock S (-J) vJ`:

* `ha` is `lex` (plus `a_mem`): `lex` maximises `dot (-(-J)) = dot J`, so `F.a ∈ face ↑S J`.
* `hfaceparam` is `edge`: off the `+ℕ•vJ` run, `edge` gives `1 ≤ dot (-J) (b - F.a)`, which
  contradicts `b` being on the `J`-face (there `dot (-J) (b - F.a) = 0`).

Neither uses `r`, `a'`, `lex'`, `edge'` or `dot_nJ_vJ`. -/

/-- `F.a` is the `J`-maximal point of the window: `FaceBlock.lex` at `n := -J`. -/
theorem faceBlock_a_mem_face {S : Finset (ℤ × ℤ)} {J vJ : ℤ × ℤ}
    (F : Nivat.Colle35.FaceBlock S (-J) vJ) :
    F.a ∈ Nivat.LE2.face (↑S : Set (ℤ × ℤ)) J := by
  refine ⟨Finset.mem_coe.mpr F.a_mem, ?_⟩
  intro y hy
  by_cases hya : y = F.a
  · rw [hya]
  · have hy' : y ∈ S.erase F.a := Finset.mem_erase.mpr ⟨hya, Finset.mem_coe.mp hy⟩
    rcases F.lex y hy' with h | ⟨h, -⟩ <;> rw [neg_neg] at h <;> omega

/-- The `J`-face of the window is the `+ℕ•vJ` run out of `F.a`: `FaceBlock.edge` at `n := -J`,
with the second disjunct killed by the face's own level equation. -/
theorem faceBlock_faceparam {S : Finset (ℤ × ℤ)} {J vJ : ℤ × ℤ}
    (F : Nivat.Colle35.FaceBlock S (-J) vJ) :
    ∀ b ∈ Nivat.LE2.face (↑S : Set (ℤ × ℤ)) J, ∃ j : ℕ, b = F.a + (j : ℤ) • vJ := by
  intro b hb
  by_cases hba : b = F.a
  · exact ⟨0, by rw [hba]; simp⟩
  · have hbS : b ∈ S := Finset.mem_coe.mp hb.1
    have hb' : b ∈ S.erase F.a := Finset.mem_erase.mpr ⟨hba, hbS⟩
    rcases F.edge b hb' with ⟨j, -, -, hj⟩ | hge
    · exact ⟨j, hj⟩
    · exfalso
      have h1 : dot J b ≤ dot J F.a := (faceBlock_a_mem_face F).2 b hb.1
      have h2 : dot J F.a ≤ dot J b := hb.2 F.a (Finset.mem_coe.mpr F.a_mem)
      have e : dot (-J) (b - F.a) = dot J F.a - dot J b := by
        simp only [dot, Prod.fst_neg, Prod.snd_neg, Prod.fst_sub, Prod.snd_sub]
        ring
      rw [e] at hge
      omega

/-- **`hSnp`.**  `F.a` maximises `dot nprev` over the whole window `S`, where `nprev` is the
edge normal fan-adjacent to `J` in either orientation.

This is the hypothesis `hseedS_of_parts` (`tmp/wip/lane-cd-bottom.lean`) takes as
`hSnp : ∀ b ∈ S, dot n_prev b ≤ dot n_prev a` with `a := F.a`; `bottom`'s third conjunct
(`ChainExhaustInter.lean`) is stated at `F.a`, not at the chain's `gen = F.a'`.

The `hadj_or` disjunction is exactly what the assembly's `J`-package exports.  Both branches
land on the same conclusion, so the caller never has to know which orientation it is in — and,
more to the point, cannot pair `hdet` with the wrong `hadj` clause order, since each branch
carries its own matched pair. -/
theorem dot_le_of_faceBlock_fan_adjacent {S : Finset (ℤ × ℤ)} {J nprev vJ : ℤ × ℤ}
    (hlc : IsLatticeConvexRegion (↑S : Set (ℤ × ℤ)))
    (hJE : J ∈ Nivat.LE2.E (↑S : Set (ℤ × ℤ)))
    (hnprevE : nprev ∈ Nivat.LE2.E (↑S : Set (ℤ × ℤ)))
    (F : Nivat.Colle35.FaceBlock S (-J) vJ)
    (hnpvJ : dot nprev vJ < 0)
    (hadj_or :
      (0 < det nprev J ∧ ∀ μ ∈ Nivat.LE2.E (↑S : Set (ℤ × ℤ)),
          ¬ (0 < det nprev μ ∧ 0 < det μ J)) ∨
      (0 < det J nprev ∧ ∀ μ ∈ Nivat.LE2.E (↑S : Set (ℤ × ℤ)),
          ¬ (0 < det J μ ∧ 0 < det μ nprev))) :
    ∀ b ∈ S, dot nprev b ≤ dot nprev F.a := by
  have hfin : (↑S : Set (ℤ × ℤ)).Finite := S.finite_toSet
  have ha := faceBlock_a_mem_face F
  have hfp := faceBlock_faceparam F
  have hface : F.a ∈ Nivat.LE2.face (↑S : Set (ℤ × ℤ)) nprev := by
    rcases hadj_or with ⟨hdet, hadj⟩ | ⟨hdet, hadj⟩
    · exact mem_face_of_adjacent_endpoint_ccw hfin hlc hJE hnprevE hdet ha hfp hnpvJ hadj
    · exact mem_face_of_adjacent_endpoint_cw hfin hlc hJE hnprevE hdet ha hfp hnpvJ hadj
  exact fun b hb => hface.2 b (Finset.mem_coe.mpr hb)

/-- **`hedge`.**  `hseedS_of_parts` takes the run bound `j ≤ r` off `FaceBlock.edge`, since its
seed argument slides along `vJ` without reference to the face's length.  Stated here so the
call site does not have to destructure a four-field conjunction inline. -/
theorem faceBlock_edge_forget_len {S : Finset (ℤ × ℤ)} {nJ vJ : ℤ × ℤ}
    (F : Nivat.Colle35.FaceBlock S nJ vJ) :
    ∀ b ∈ S.erase F.a,
      (∃ j : ℕ, 1 ≤ j ∧ b = F.a + (j : ℤ) • vJ) ∨ 1 ≤ dot nJ (b - F.a) :=
  fun b hb => (F.edge b hb).imp (fun ⟨j, h1, _, h3⟩ => ⟨j, h1, h3⟩) id

end Nivat.FanEndpoint

#print axioms Nivat.FanEndpoint.mem_face_of_adjacent_endpoint_ccw
#print axioms Nivat.FanEndpoint.mem_face_of_adjacent_endpoint_ccw_eq
#print axioms Nivat.FanEndpoint.mem_face_of_adjacent_endpoint_cw
#print axioms Nivat.FanEndpoint.mem_face_of_adjacent_endpoint_cw_eq
#print axioms Nivat.FanEndpoint.faceBlock_a_mem_face
#print axioms Nivat.FanEndpoint.faceBlock_faceparam
#print axioms Nivat.FanEndpoint.dot_le_of_faceBlock_fan_adjacent
#print axioms Nivat.FanEndpoint.faceBlock_edge_forget_len
