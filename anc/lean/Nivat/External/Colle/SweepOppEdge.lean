/-
Copyright (c) 2026. Released under Apache 2.0 license.
Authors: lane-chaindata-lead
-/
import Nivat.External.Colle.SweepCriterion
import Nivat.External.Colle.ShellLine

/-!
# `hlcT`'s first factor, produced: `IsLatticeConvexRegion (reachSet Â_i w)` from enveloped

`ShellSubStrip.lean` §25 splits `hlcT` into `IsLatticeConvexRegion (reachSet Â_i w)` and the
band; §34/§36 (`LaneCdReachGap`, `LaneCdBoxGrow`) refute the first factor under every abstract
property the split could see — full-dimensionality, `w` an edge direction, and containment of
Collé's item (ii) box at unbounded size.

**All three refutations share one feature**: `w` is parallel to an edge at *one* extreme of
`det w` only; at the other extreme the exposed face is a single vertex.  That is exactly the
hypothesis `Nivat.SweepCrit.unitCovered_of_opposite_segments` (`SweepCriterion.lean:305`)
requires, and the machinery to exploit it is already in the main tree — it had only ever been
composed into the row-descent conclusion (`hrow_of_enveloped_segments`, `:687`), never into
lattice-convexity of the swept set.  This file composes it.

`Nivat.LE2.halfStrip` (`LatticeEdges.lean:1810`) and `Nivat.MaxEnv.reachSet`
(`ShellLine.lean:35`) are character-for-character the same definition, so the bridge is `rfl`.

## Why `Enveloped` is exactly the right hypothesis

`n ∈ E U` unfolds to `Prim n ∧ (face U n).Nontrivial`, so `n ∈ E U` and `-n ∈ E U` already say
`U` has two lattice points on each of its `±n` faces.  `Enveloped U B` (Definition 3.2,
`b3_colle2.txt:402`) transports both counts to `B`, `exists_unit_step_in_face`
(`SweepCriterion.lean:370`) turns "two points on a face" into "an adjacent pair", and the two
adjacent pairs are the two opposite unit segments.  Nothing else is needed.

For the target, `Â_i` is `Enveloped ↑𝒮_φ`-bounded by construction, and
`LaneCdFaceFree.E_hatOf_eq` (`ShellSubStrip.lean:2723`) gives `E Â_i = E ↑𝒮_φ` for **every**
`i` — so the hypothesis is `i`-independent, as it must be.

## The one remaining obligation this hands back

`±n ∈ E ↑𝒮_φ` — an **antipodal pair** of edge normals — plus `w := dir n` with
`dot nJ w < 0` for the sign.  `w` is a free parameter of `ChainDataGeom.ofPartsExhaustsInter`
(`ChainExhaustInter.lean`), so this is a constraint on the producer's *choice*, not a fact
about a given `w`.

The antipodal half is **free**: `Nivat.Colle35.Sphi_negSymm` (`DecompData.lean:417`) proves
`n ∈ E ↑d.Sphi ↔ -n ∈ E ↑d.Sphi`, because `𝒮_φ` is the zonotope of `φ = ∏(X^{h_i} − 1)` and a
zonotope's edges come in `±` pairs.  So *any* edge normal of `𝒮_φ` supplies the pair.

What is **not** free is the sign: `hsweepW : dot nJ w < 0` has to be arranged by choosing which
edge `n`, and which of `±n`; an `n` with `dot nJ (dir n) = 0` is unusable.  That such an `n`
always exists is `exists_edge_sweep_direction` below — if every edge normal had
`dot nJ (dir n) = 0` then every edge direction would be parallel to `dir nJ` and `U` would be a
segment, contradicting `PosArea U`.  `exists_sweep_dir_of_enveloped` packages both halves.

## Numeric instances (硬规矩 6, worked before the Lean)

* **Positive.**  `B := {0,1}²` (unit square), `n := (0,1)`, `v := dir n = (-1,0)`.
  `face B (0,1) = {(0,1),(1,1)}` and `face B (0,-1) = {(0,0),(1,0)}`, both with two points, one
  `v`-step apart.  Criterion applies; `reachSet B (-1,0) = {z | 0 ≤ z.2 ≤ 1}` is lattice convex.
* **Negative, `LaneCdReachGap.Tri`.**  `w = (1,-1)`, `dir w = (1,1) ∈ E Tri` (the long edge),
  but `-(1,1) ∉ E Tri`: `face Tri (-1,-1) = {(0,0)}`, a singleton.  One-sided only — criterion
  correctly does not apply, and §34 shows the conclusion is genuinely false.
* **Negative, `LaneCdBoxGrow.ConeK k`.**  Same picture at the apex `(-10k,-15k)`, for every `k`:
  the `-(1,1)` face is the apex alone.  Criterion correctly does not apply.

So the criterion separates all the known instances, in both directions.
-/

set_option autoImplicit false

namespace Nivat.LaneCdOppEdge

open Nivat Nivat.LE2 Nivat.MaxEnv Nivat.SweepCrit

/-- `reachSet` and `halfStrip` are the same definition. -/
theorem reachSet_eq_halfStrip (B : Set (ℤ × ℤ)) (v : ℤ × ℤ) :
    reachSet B v = Nivat.LE2.halfStrip B v := rfl

/-- A lattice-convex set is cut out by its own closed convex hull. -/
theorem eq_preimage_convHullOf {B : Set (ℤ × ℤ)} (hlc : IsLatticeConvexRegion B) :
    B = toReal ⁻¹' Nivat.convHullOf B := by
  obtain ⟨C, hconvC, hclosedC, heq⟩ := hlc
  refine Set.Subset.antisymm (fun b hb => toReal_mem_convHullOf hb) (fun z hz => ?_)
  have himg : toReal '' B ⊆ C := by
    rintro x ⟨b, hb, rfl⟩
    rw [heq] at hb
    exact hb
  have hhull : Nivat.convHullOf B ⊆ C :=
    closure_minimal (convexHull_min himg hconvC) hclosedC
  rw [heq]
  exact hhull hz

/-- **The producer.**  Two opposite edges of `U`, transported to `B` by `Enveloped`, make the
sweep of `B` along their common direction lattice convex.

Every hypothesis is either a standing binder at the call site or a consequence of
`Enveloped ↑𝒮_φ Â_i`; the only genuine input is that `n` **and** `-n` are both edge normals. -/
theorem isLatticeConvexRegion_reachSet_of_opposite_edges
    {U B : Set (ℤ × ℤ)} {n v : ℤ × ℤ}
    (hUE : (E U).Finite)
    (hBfin : B.Finite) (hBne : B.Nonempty)
    (harea : PosArea B) (hlc : IsLatticeConvexRegion B)
    (henv : Enveloped U B)
    (hn : n ≠ 0) (hvp : Primitive v) (hv : v ≠ 0) (hperp : dot n v = 0)
    (hnU : n ∈ E U) (h_nU : -n ∈ E U) :
    IsLatticeConvexRegion (reachSet B v) := by
  have htwoPos : ∃ a b, a ∈ face U n ∧ b ∈ face U n ∧ a ≠ b := by
    obtain ⟨a, ha, b, hb, hab⟩ := (mem_E_iff.mp hnU).2
    exact ⟨a, b, ha, hb, hab⟩
  have htwoNeg : ∃ a b, a ∈ face U (-n) ∧ b ∈ face U (-n) ∧ a ≠ b := by
    obtain ⟨a, ha, b, hb, hab⟩ := (mem_E_iff.mp h_nU).2
    exact ⟨a, b, ha, hb, hab⟩
  obtain ⟨a1, a2, ha1, ha2, ha12⟩ := exists_two_in_face_of_enveloped hUE henv hnU htwoPos
  obtain ⟨b1, b2, hb1, hb2, hb12⟩ := exists_two_in_face_of_enveloped hUE henv h_nU htwoNeg
  obtain ⟨ca, hca, hcaw⟩ :=
    exists_unit_step_in_face hBfin hBne harea hlc hn hvp hperp ha1 ha2 ha12
  have hnneg : (-n) ≠ 0 := by simpa using hn
  have hperp' : dot (-n) v = 0 := by
    unfold Nivat.LE2.dot at hperp ⊢
    simp only [Prod.fst_neg, Prod.snd_neg]
    linarith
  obtain ⟨cb, hcb, hcbw⟩ :=
    exists_unit_step_in_face hBfin hBne harea hlc hnneg hvp hperp' hb1 hb2 hb12
  have hUC : UnitCovered (Nivat.convHullOf B) v :=
    unitCovered_convHullOf_of_faces hBfin hBne hn hv hperp hca hcaw hcb hcbw
  have hclosed : IsClosed (sweepHull (Nivat.convHullOf B) v) :=
    isClosed_sweepHull_of_isCompact (isCompact_convHullOf_of_finite hBfin) v
  rw [reachSet_eq_halfStrip]
  exact isLatticeConvexRegion_halfStrip_of_unitCovered (convex_convHullOf B)
    (eq_preimage_convHullOf hlc) hclosed hUC

/-- `dir n` is primitive whenever `n` is. -/
theorem prim_dir {n : ℤ × ℤ} (hn : Prim n) : Prim (dir n) := by
  show Int.gcd (-n.2) n.1 = 1
  rw [Int.neg_gcd, Int.gcd_comm]
  exact hn

/-- **The form the producer uses.**  At `v := dir n` the three vector side conditions are
automatic, so the whole criterion is "`n` and `-n` are both edge normals of `U`".

On the chain `U := ↑𝒮_φ`, and `-n ∈ E ↑𝒮_φ` is free from `n ∈ E ↑𝒮_φ` by
`Nivat.Colle35.Sphi_negSymm` (`DecompData.lean:417`, zonotope `±`-symmetry).  What is *not*
free is the sign condition `dot nJ (dir n) < 0` that `ofPartsExhaustsInter`'s `hsweepW`
demands: it must be arranged by choosing which edge `n` and which of `±n`, and fails outright
for any `n` with `dot nJ (dir n) = 0`. -/
theorem isLatticeConvexRegion_reachSet_dir_of_mem_E
    {U B : Set (ℤ × ℤ)} {n : ℤ × ℤ}
    (hUE : (E U).Finite)
    (hBfin : B.Finite) (hBne : B.Nonempty)
    (harea : PosArea B) (hlc : IsLatticeConvexRegion B)
    (henv : Enveloped U B)
    (hnU : n ∈ E U) (h_nU : -n ∈ E U) :
    IsLatticeConvexRegion (reachSet B (dir n)) := by
  have hprim : Prim n := (mem_E_iff.mp hnU).1
  have hn0 : n ≠ 0 := hprim.ne_zero
  have hdprim : Prim (dir n) := prim_dir hprim
  exact isLatticeConvexRegion_reachSet_of_opposite_edges hUE hBfin hBne harea hlc henv
    hn0 (prim_iff_primitive.mp hdprim) hdprim.ne_zero (dot_dir n) hnU h_nU

/-! ## The sign obligation

`ofPartsExhaustsInter` also demands `hsweepW : dot nJ w < 0` (`ChainExhaustInter.lean`).
With `w := dir n` this is a constraint on *which* edge normal is chosen, and it is the only
part of the criterion that is not free.  It is nevertheless satisfiable whenever `U` has
positive area: if every edge normal had `dot nJ (dir n) = 0`, all edge directions would be
parallel to `dir nJ` and `U` would be a segment. -/

/-- `dir` is odd. -/
theorem dir_neg (n : ℤ × ℤ) : dir (-n) = -(dir n) := by
  simp only [dir, Prod.fst_neg, Prod.snd_neg, Prod.neg_mk, neg_neg]

/-- The two ways of pairing `nJ` against `n` through `dir` differ by a sign. -/
theorem dot_dir_swap (nJ n : ℤ × ℤ) : dot nJ (dir n) = - dot n (dir nJ) := by
  simp only [dot, dir]
  ring

/-- **The sign obligation is satisfiable.**  A positive-area `U` whose edge-normal set is
closed under negation has an edge normal `n` with `-n` also an edge normal and
`dot nJ (dir n) < 0`, for any `nJ ≠ 0`.

On the chain `hsym` is `Nivat.Colle35.Sphi_negSymm` (`DecompData.lean:417`) and `hUarea` is
`Nivat.AhatMono.posArea_Sphi` (`AhatMono.lean:3175`), both free. -/
theorem exists_edge_sweep_direction {U : Set (ℤ × ℤ)} {nJ : ℤ × ℤ}
    (hUfin : U.Finite) (hUne : U.Nonempty) (hUarea : PosArea U) (hnJ : nJ ≠ 0)
    (hsym : ∀ n : ℤ × ℤ, n ∈ E U → -n ∈ E U) :
    ∃ n ∈ E U, -n ∈ E U ∧ dot nJ (dir n) < 0 := by
  have hdnJ : dir nJ ≠ 0 := by
    intro h
    apply hnJ
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only [dir] at h1 h2
    exact Prod.ext (by simpa using h2) (by simpa using neg_eq_zero.mp h1)
  obtain ⟨m, hmU, hm⟩ := exists_mem_E_dot_ne_zero hUfin hUne hUarea hdnJ
  have hkey : dot nJ (dir m) ≠ 0 := by
    rw [dot_dir_swap]
    simpa using hm
  rcases lt_or_gt_of_ne hkey with hlt | hgt
  · exact ⟨m, hmU, hsym m hmU, hlt⟩
  · refine ⟨-m, hsym m hmU, ?_, ?_⟩
    · simpa using hmU
    · have hEq : dot nJ (dir (-m)) = - dot nJ (dir m) := by
        simp only [dot, dir, Prod.fst_neg, Prod.snd_neg]
        ring
      omega

/-- **Everything packaged**: from `Enveloped U B` with `U` of positive area and `±`-symmetric
edge normals, a sweep direction exists that satisfies both `hsweepW` and §25's first factor.

`hBarea` is discharged on the chain by `Nivat.AhatMono.posArea_of_enveloped`
(`AhatMono.lean:3020`) applied to `posArea_Sphi`; it is a hypothesis here only so that this
file stays upstream of `AhatMono`. -/
theorem exists_sweep_dir_of_enveloped
    {U B : Set (ℤ × ℤ)} {nJ : ℤ × ℤ}
    (hUfin : U.Finite) (hUne : U.Nonempty) (hUarea : PosArea U) (hnJ : nJ ≠ 0)
    (hsym : ∀ n : ℤ × ℤ, n ∈ E U → -n ∈ E U)
    (hBfin : B.Finite) (hBarea : PosArea B) (henv : Enveloped U B) :
    ∃ w : ℤ × ℤ, Primitive w ∧ dot nJ w < 0 ∧ IsLatticeConvexRegion (reachSet B w) := by
  obtain ⟨n, hnU, h_nU, hsign⟩ := exists_edge_sweep_direction hUfin hUne hUarea hnJ hsym
  have hBne : B.Nonempty := by obtain ⟨p, hp, -⟩ := hBarea; exact ⟨p, hp⟩
  refine ⟨dir n, prim_iff_primitive.mp (prim_dir (mem_E_iff.mp hnU).1), hsign, ?_⟩
  exact isLatticeConvexRegion_reachSet_dir_of_mem_E (finite_E_of_finite hUfin) hBfin hBne
    hBarea henv.1.latticeConvex henv hnU h_nU

end Nivat.LaneCdOppEdge

#print axioms Nivat.LaneCdOppEdge.reachSet_eq_halfStrip
#print axioms Nivat.LaneCdOppEdge.eq_preimage_convHullOf
#print axioms Nivat.LaneCdOppEdge.isLatticeConvexRegion_reachSet_of_opposite_edges
#print axioms Nivat.LaneCdOppEdge.prim_dir
#print axioms Nivat.LaneCdOppEdge.isLatticeConvexRegion_reachSet_dir_of_mem_E
#print axioms Nivat.LaneCdOppEdge.exists_edge_sweep_direction
#print axioms Nivat.LaneCdOppEdge.exists_sweep_dir_of_enveloped
