/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.L3Band
import Nivat.External.Colle.Generating
import Nivat.External.Colle.L1StraddleWedge
import Nivat.External.Colle.MaxIndexProbe
import Nivat.External.Colle.L1SweepBridge

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# `hbase`'s corner-vertex route (`OPEN.md #13`): does a witness `a` exist?

`Nivat.L3Band.chainFull_succ_subset_genClosure_iff_of_ahead` (`L3Band.lean:4074`) pins the
vertex condition needed to extend `chainFull` under `hahead` to an **iff**: the corner `a` must
be a **double minimum** of `S` for `(expNormal u' vl, expDual u' vl)` simultaneously,

```
(∀ b ∈ S, dot (expNormal u' vl) a ≤ dot (expNormal u' vl) b) ∧
(∀ b ∈ S, dot (expDual u' vl) a ≤ dot (expDual u' vl) b)
```

This file answers, for the two readings of "does a witness `a` exist", the question the
team-lead posed for the *corner-vertex* half of `OPEN.md #13`.

## §1  `a` required to be a genuine vertex of `S` (the real reading): **dead, already landed**

`Nivat.L3Band.no_corner_vertex_parallelogram` (`L3Band.lean:3826`) is *already on the main tree*
and is exactly this refutation: the parallelogram `{(0,1),(0,2),(1,0),(1,1)}` — Lemma 2.3's own
shape — under `u' = (1,0)`, `vl = (0,1)` has its `expNormal`-argmin at `(1,0)` alone and its
`expDual`-argmin on `{(0,1),(0,2)}`; the two never meet.  §1 below reconfirms the phenomenon with
an even smaller (2-point, still `LatticeConvex`) witness, and — the part that was not yet
checked — nails down **why `a` is forced to range over `S` on the real chain**: `GeneratesAt`
(`Generating.lean:16`), which every consumer of `hgen`/`IsGeneratingSet` needs, has `a ∈ S` as
its *first conjunct by definition*.  So the free-standing iff lemma's bare `a : ℤ × ℤ` binder is
never actually free once the corner is asked to also generate — `a ∈ S` is not an extra
hypothesis to add, it is already there via `GeneratesAt`.  **Conclusion: the corner-vertex route
has no producer for general `S`, and this is not an artifact of an under-specified binder.**

## §2  `a` literally unconstrained by `S`-membership (what the bare iff's binders say): trivial,
and irrelevant to the chain

Read completely literally, `chainFull_succ_subset_genClosure_iff_of_ahead`'s `a : ℤ × ℤ` carries
no `a ∈ S` hypothesis.  Since `u' vl` unimodular makes `z ↦ (dot (expDual u' vl) z,
dot (expNormal u' vl) z)` a ℤ-linear bijection with **inverse** `(p, q) ↦ p • u' + q • vl`
(`dot_expDual_u'`/`dot_expDual_vl`/`dot_expNormal_u'`/`dot_expNormal_vl`), the pair of target
values `(inf over S of expDual, inf over S of expNormal)` is always *hit* by some `a` — never an
obstruction.  `exists_doublyMinimal_free` below constructs it.  **This does not rescue the
route**: by §1, the `a` that actually appears in the assembly (`WedgeResidualR`, `ChainDataGeom`,
`hgen`) is tied to `GeneratesAt`, which forces `a ∈ S`.  §2 is kept because it closes off the
"maybe the Lean binder is looser than the math" escape hatch explicitly, rather than leaving it
untested.

## Reading for `OPEN.md #13`

The corner-vertex half of `hbase`'s two walls is **closed, negatively, with no new axiom or
`sorry`**: no producer exists for general `S`, and the one route that could have side-stepped
this (an unconstrained `a`) is unavailable because the real consumer (`GeneratesAt`) already
pins `a ∈ S`.  Nothing here touches the flat-`hwin` wall (`HbaseBridge.not_cutBand_subset_
wedgeFull_iff`), which is a separate, already-settled iff.
-/

namespace Nivat.HbaseVertexSeed

open Nivat Nivat.L3Band Nivat.ColleReg Nivat.Colle
open Nivat.LE2 (dot)

/-! ## §1  No common vertex, minimal witness: `S = {(0,1),(1,0)}` -/

/-- The simplest unimodular pair: `u' = (1,0)`, `vl = (0,1)`, `det u' vl = 1`. -/
theorem hunimod_seed : det ((1 : ℤ), (0 : ℤ)) ((0 : ℤ), (1 : ℤ)) = 1 := by decide

/-- Under this pair, `expNormal u' vl = (0,1)`, so `dot expNormal` reads off the
`y`-coordinate. -/
theorem expNormal_seed_eq : expNormal ((1 : ℤ), (0 : ℤ)) ((0 : ℤ), (1 : ℤ)) = (0, 1) := by
  simp [expNormal, det]

/-- Under the same pair, `expDual u' vl = (1,0)`, so `dot expDual` reads off the
`x`-coordinate. -/
theorem expDual_seed_eq : expDual ((1 : ℤ), (0 : ℤ)) ((0 : ℤ), (1 : ℤ)) = (1, 0) := by
  simp [expDual, det]

/-- **No point of the 2-point set `S = {(0,1),(1,0)}` is a double minimum.**  `(0,1)` minimizes
`expDual` (`x`-coordinate, value `0`) but loses `expNormal` (`y`-coordinate) to `(1,0)`
(`1 ≰ 0`); `(1,0)` minimizes `expNormal` but loses `expDual` to `(0,1)`.  `S` is itself
`LatticeConvex` (no interior lattice points on the segment, `gcd 1 1 = 1`), so this is a
legitimate — if degenerate — generating-set shape, not an artificial finite set.  Pure finite
arithmetic, `decide`-checked; no `hξ`, no `IsMinimalCounterexample`. -/
theorem not_doublyMinimal_of_two_points :
    ¬ ∃ a ∈ ({((0 : ℤ), (1 : ℤ)), (1, 0)} : Finset (ℤ × ℤ)),
      (∀ b ∈ ({((0 : ℤ), (1 : ℤ)), (1, 0)} : Finset (ℤ × ℤ)),
        dot (expNormal ((1 : ℤ), (0 : ℤ)) ((0 : ℤ), (1 : ℤ))) a ≤
          dot (expNormal ((1 : ℤ), (0 : ℤ)) ((0 : ℤ), (1 : ℤ))) b) ∧
      (∀ b ∈ ({((0 : ℤ), (1 : ℤ)), (1, 0)} : Finset (ℤ × ℤ)),
        dot (expDual ((1 : ℤ), (0 : ℤ)) ((0 : ℤ), (1 : ℤ))) a ≤
          dot (expDual ((1 : ℤ), (0 : ℤ)) ((0 : ℤ), (1 : ℤ))) b) := by
  simp only [expNormal_seed_eq, expDual_seed_eq]
  decide

/-! ## §1'  Why `a` cannot be quietly taken outside `S` on the real chain: `GeneratesAt` pins it

`GeneratesAt` (`Nivat.Colle.GeneratesAt`, `Generating.lean:16`) is `a ∈ S ∧ ∀ x ∈ orbitClosure …`
— membership is its *first conjunct*, definitionally, not a side condition bolted on later. -/
theorem mem_of_generatesAt {A : Type*} {ξ : Config A} {S : Finset (ℤ × ℤ)} {a : ℤ × ℤ}
    (h : GeneratesAt ξ S a) : a ∈ S := h.1

/-! ## §2  Read literally, the bare iff's `a` is unconstrained by `S` — and that reading is
trivial (never an obstruction), via the `(expDual, expNormal)` coordinate inverse -/

/-- **A doubly-minimal `a` always exists if `a` is not required to lie in `S`.**  Explicit
witness `a := p • u' + q • vl`, where `p`/`q` are the `S`-infima of `expDual`/`expNormal`.  This
is the converse fact to §1: the obstruction in §1 is entirely about `a ∈ S`, not about the
`(expNormal, expDual)` coordinate system being somehow deficient. -/
theorem exists_doublyMinimal_free {u' vl : ℤ × ℤ} (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    {S : Finset (ℤ × ℤ)} (hne : S.Nonempty) :
    ∃ a : ℤ × ℤ,
      (∀ b ∈ S, dot (expNormal u' vl) a ≤ dot (expNormal u' vl) b) ∧
      (∀ b ∈ S, dot (expDual u' vl) a ≤ dot (expDual u' vl) b) := by
  classical
  set p : ℤ := S.inf' hne (fun z => dot (expDual u' vl) z) with hp
  set q : ℤ := S.inf' hne (fun z => dot (expNormal u' vl) z) with hq
  refine ⟨p • u' + q • vl, ?_, ?_⟩
  · have hval : dot (expNormal u' vl) (p • u' + q • vl) = q := by
      simp only [Nivat.LE2.dot_add, dot_zsmul', dot_expNormal_u', dot_expNormal_vl hunimod]
      ring
    rw [hval]
    exact fun b hb => Finset.inf'_le (fun z => dot (expNormal u' vl) z) hb
  · have hval : dot (expDual u' vl) (p • u' + q • vl) = p := by
      simp only [Nivat.LE2.dot_add, dot_zsmul', dot_expDual_u' hunimod, dot_expDual_vl]
      ring
    rw [hval]
    exact fun b hb => Finset.inf'_le (fun z => dot (expDual u' vl) z) hb

/-! ## §3  The exact consumer's `hcorner` shape (`L1StraddleWedge.lean:346`)

Team-lead's dispatch (2026-09-19, off the integrator's `#print axioms` on
`Nivat.L1StraddleWedge.exists_L1MaxBResidual_of_corner`): that theorem's `hcorner` binder is

```
hcorner : ∀ b ∈ d.Sphi, 0 ≤ dot (expNormal u' vl) (b - a) ∧ 0 ≤ Nivat.L1Line0.uCoord u' vl a b
```

which is the same double-minimum condition as §1, with `expDual u' vl` written as
`uCoord u' vl a ·` (`uCoord u' vl a b = -(det u' vl) * det vl (b - a)`, which unfolds to
`dot (expDual u' vl) (b - a)` — not reproved here, just used through the concrete values below
so the exact syntax matches the consumer, not a restatement).

Two questions, kept separate per team-lead's instruction: (a) does *every* finite nonempty `S`
admit an `hcorner`-witness — refuted below, same mechanism as §1; (b) does the *generating set*
`d.Sphi` (always a translate of a lattice-convex completion of a **zonotope**
`zonoF s d.h`, `DecompData.lean:106/158`, `Sphi_eq`) admit one — **not settled here**, see the
discussion after §4. -/

/-- **(a) refuted, in the consumer's exact syntax.**  Same witness as §1
(`{(0,1),(1,0)}`, `u' = (1,0)`, `vl = (0,1)`), restated with `uCoord` literally (not `expDual`)
so this is provably the closure of `hcorner`'s own binder, not a look-alike. -/
theorem not_hcorner_of_two_points :
    ¬ ∃ a ∈ ({((0 : ℤ), (1 : ℤ)), (1, 0)} : Finset (ℤ × ℤ)),
      ∀ b ∈ ({((0 : ℤ), (1 : ℤ)), (1, 0)} : Finset (ℤ × ℤ)),
        0 ≤ dot (expNormal ((1 : ℤ), (0 : ℤ)) ((0 : ℤ), (1 : ℤ))) (b - a) ∧
          0 ≤ Nivat.L1Line0.uCoord ((1 : ℤ), (0 : ℤ)) ((0 : ℤ), (1 : ℤ)) a b := by
  rintro ⟨a, ha, h⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha
  have e1 := h (1, 0) (by simp)
  have e2 := h (0, 1) (by simp)
  simp only [expNormal, Nivat.L1Line0.uCoord, dot, det, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul, Prod.fst_sub, Prod.snd_sub] at e1 e2
  rcases ha with rfl | rfl <;> omega

/-! ## §4  `hcorner`'s counterexample is a genuine zonotope shape, not an artificial set

`S := zonoF {0,1} h` with `h 0 = (-1,1)`, `h 1 = (0,1)` — a real 2-generator zonotope, the exact
combinatorial shape `Sphi_eq` forces on any `m = 2` decomposition — is, up to translation, the
same parallelogram as `no_corner_vertex_parallelogram`'s witness (`L3Band.lean:3826`) and fails
`hcorner` at `u' = (1,0)`, `vl = (0,1)` by the identical mechanism: the `expNormal`-argmin
`(0,0)` and the `uCoord`-argmin `(-1,1)`/`(-1,2)` are disjoint sets. -/

theorem zonoF_seed_eq :
    Nivat.LE2.zonoF (Finset.univ : Finset (Fin 2))
        (fun i => (![((-1 : ℤ), (1 : ℤ)), ((0 : ℤ), (1 : ℤ))] : Fin 2 → ℤ × ℤ) i) =
      ({(0, 0), (0, 1), (-1, 1), (-1, 2)} : Finset (ℤ × ℤ)) := by decide

/-- **(a) refuted again, on an actual `m = 2` zonotope** (not merely a finite set with the right
shape by coincidence): no `a` in the zonotope satisfies `hcorner` at `u' = (1,0)`, `vl = (0,1)`.
`decide`-checked once `zonoF_seed_eq` reduces the zonotope to an explicit `Finset`. -/
theorem not_hcorner_of_zonoF_two_generators :
    ¬ ∃ a ∈ Nivat.LE2.zonoF (Finset.univ : Finset (Fin 2))
        (fun i => (![((-1 : ℤ), (1 : ℤ)), ((0 : ℤ), (1 : ℤ))] : Fin 2 → ℤ × ℤ) i),
      ∀ b ∈ Nivat.LE2.zonoF (Finset.univ : Finset (Fin 2))
          (fun i => (![((-1 : ℤ), (1 : ℤ)), ((0 : ℤ), (1 : ℤ))] : Fin 2 → ℤ × ℤ) i),
        0 ≤ dot (expNormal ((1 : ℤ), (0 : ℤ)) ((0 : ℤ), (1 : ℤ))) (b - a) ∧
          0 ≤ Nivat.L1Line0.uCoord ((1 : ℤ), (0 : ℤ)) ((0 : ℤ), (1 : ℤ)) a b := by
  rw [zonoF_seed_eq]
  rintro ⟨a, ha, h⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha
  have e1 := h (0, 0) (by simp)
  have e2 := h (-1, 1) (by simp)
  have e3 := h (-1, 2) (by simp)
  simp only [expNormal, Nivat.L1Line0.uCoord, dot, det, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul, Prod.fst_sub, Prod.snd_sub] at e1 e2 e3
  rcases ha with rfl | rfl | rfl | rfl <;> omega

/-!
**Reading (b), honestly unsettled here — not claimed dead.**  §4 shows the *shape* that kills
`hcorner` is exactly a shape `Sphi` is allowed to have (a genuine `m = 2` zonotope up to
translation and unimodular relabelling).  It does **not** show `d.Sphi` for a real
`DecompDataZ ξ` (`hξ : IsMinimalCounterexample ξ`) realises this shape *at the specific `u'`
that `hbase`/`hlev`/`hmin` also need* — that requires either (i) an actual periodic witness
config with `m = 2` producing this `Sphi` and this `u'`, which is a materially heavier
construction than anything in this file, or (ii) a fact — not found anywhere on the tree in the
time available — tying the chosen `u'` to `d.h` so that `(expNormal u' vl, uCoord u' vl a ·)`
is forced into alignment with a single vertex's normal cone.  `L1StraddleWedge.lean`'s own
`exists_corner_shear` (`:420`) is the closest existing fact and is explicit that it only
produces `hcorner` after **shearing** `u'` by a multiple of `vl` — the docstring there already
flags "whether the `u'` that `hbase`/`hlev`/`hmin` want survives that shear" as open, which is
question (b) in different words.  **This file leaves (b) open; it narrows it from "unexamined"
to "the failing shape is realisable by `Sphi`, and the only existing producer needs a shear that
is not known to be compatible with the rest of the chain."** -/

/-! ## §5  `chainFull`'s shear-covariance (new task): the level cut genuinely tilts

Both existing `hbase` producers (`HbaseBridge.exists_shear_hlt_and_doubly_lower`,
`L1StraddleWedge.exists_corner_shear`) only work after shearing `u'` by a multiple of `vl`, and
both flag — without settling — whether that shear is compatible with the rest of
`MaxBResidual`'s data, all stated at the *original* `u'`.  `wedgeFull` itself is shear-invariant
(`Nivat.L1StraddleWedge.wedgeFull_shear`) and unimodularity survives (`det_shear`), but
`chainFull` further cuts `wedgeFull` by a level condition through `expNormal`, and `expNormal`
is **not** shear-invariant (`Nivat.L1StraddleWedge.dot_expNormal_shear`): the cut plane tilts by
`K * uCoord u' vl 0 w`, a term that is *not* constant on `wedgeFull` — it is literally the
transverse coordinate the wedge is built out of.

This section settles step (1) of the task: **outcome (iii) — neither inclusion nor
equality-after-reindexing holds in general.**  On the minimal witness below, no fixed level
`n'` of the *original* chain contains even the *base* (`n = 0`) slice of the `K = 1`-sheared
chain: as `n'` grows, the counterexample point simply moves further out along the tilted cut.
No `hξ`, no `IsMinimalCounterexample`; pure integer arithmetic on an explicit, unbounded family
of witnesses (`decide` cannot certify an unbounded statement, so this is checked by `omega`
instead). -/

section ChainFullShear

/-- Witness data: `B = {(0,0)}`, `vl = (0,1)`, `u' = (1,0)` — the same unimodular pair as §1 —
sheared by `K = 1` to `u'' = (1,-1)`. -/
abbrev seedB : Set (ℤ × ℤ) := {((0 : ℤ), (0 : ℤ))}

abbrev seedVl : ℤ × ℤ := ((0 : ℤ), (1 : ℤ))

abbrev seedU' : ℤ × ℤ := ((1 : ℤ), (0 : ℤ))

/-- The rising family `z m := (m, -m)` lies in `wedgeFull seedB seedVl seedU'` for every `m`. -/
theorem mem_wedgeFull_seed (m : ℕ) :
    ((m : ℤ), -(m : ℤ)) ∈ wedgeFull seedB seedVl seedU' := by
  unfold wedgeFull
  rw [Nivat.RegionSweep.mem_sweep]
  refine ⟨((0 : ℤ), -(m : ℤ)), ?_, m, ?_⟩
  · exact mem_fullSweep_iff.mpr ⟨(0, 0), rfl, -(m : ℤ), by
      simp [seedVl]⟩
  · simp [seedU']

theorem dot_expNormal_seed (z : ℤ × ℤ) : dot (expNormal seedU' seedVl) z = z.2 := by
  rw [expNormal_seed_eq]; simp [dot]

theorem uCoord_seed_zero (z : ℤ × ℤ) :
    Nivat.L1Line0.uCoord seedU' seedVl 0 z = z.1 := by
  simp [Nivat.L1Line0.uCoord, det]

/-- **The counterexample.**  For every level `n'` of the un-sheared chain, the base slice of the
`K = 1`-sheared chain is not contained in it: take the witness point at `m := n' + 1`. -/
theorem not_subset_chainFull_seed (n' : ℕ) :
    ¬ chainFull seedB seedVl (seedU' - (1 : ℤ) • seedVl) ((0 : ℤ), (0 : ℤ)) 0 ⊆
        chainFull seedB seedVl seedU' ((0 : ℤ), (0 : ℤ)) n' := by
  intro hsub
  have hzw : ((((n' + 1 : ℕ) : ℤ), -((n' + 1 : ℕ) : ℤ))) ∈ wedgeFull seedB seedVl seedU' :=
    mem_wedgeFull_seed (n' + 1)
  have hzw'' : ((((n' + 1 : ℕ) : ℤ), -((n' + 1 : ℕ) : ℤ))) ∈
      wedgeFull seedB seedVl (seedU' - (1 : ℤ) • seedVl) := by
    rw [Nivat.L1StraddleWedge.wedgeFull_shear]; exact hzw
  have hdz := Nivat.L1StraddleWedge.dot_expNormal_shear (u' := seedU') (vl := seedVl) 1
    (((n' + 1 : ℕ) : ℤ), -((n' + 1 : ℕ) : ℤ))
  have hdb := Nivat.L1StraddleWedge.dot_expNormal_shear (u' := seedU') (vl := seedVl) 1
    ((0 : ℤ), (0 : ℤ))
  have hlevel'' : expLevel (seedU' - (1 : ℤ) • seedVl) seedVl ((0 : ℤ), (0 : ℤ)) 0 ≤
      dot (expNormal (seedU' - (1 : ℤ) • seedVl) seedVl)
        (((n' + 1 : ℕ) : ℤ), -((n' + 1 : ℕ) : ℤ)) := by
    simp only [expLevel]
    rw [hdb, hdz, dot_expNormal_seed, dot_expNormal_seed, uCoord_seed_zero, uCoord_seed_zero]
    simp only [Nat.cast_zero]
    push_cast
    omega
  have hmem'' : ((((n' + 1 : ℕ) : ℤ), -((n' + 1 : ℕ) : ℤ))) ∈
      chainFull seedB seedVl (seedU' - (1 : ℤ) • seedVl) ((0 : ℤ), (0 : ℤ)) 0 :=
    Nivat.L1Line0.mem_chainFull_iff.mpr ⟨hzw'', hlevel''⟩
  have hmem' := hsub hmem''
  have hlevel' := (Nivat.L1Line0.mem_chainFull_iff.mp hmem').2
  simp only [expLevel] at hlevel'
  rw [dot_expNormal_seed, dot_expNormal_seed] at hlevel'
  push_cast at hlevel'
  omega

/-- **The obstruction, named as a standalone `Prop`** (per the task's third outcome): no fixed
level of the un-sheared chain absorbs the base level of the sheared chain. -/
def ChainFullShearUnbounded (B : Set (ℤ × ℤ)) (vl u' : ℤ × ℤ) (K : ℤ) (b₀ : ℤ × ℤ) : Prop :=
  ∀ n' : ℕ, ¬ chainFull B vl (u' - K • vl) b₀ 0 ⊆ chainFull B vl u' b₀ n'

/-- The witness instantiates the obstruction: `hbase`-style transport of `chainFull` along a
shear does **not** hold in general, not even as a subset relation with a shifted level. -/
theorem chainFullShearUnbounded_seed :
    ChainFullShearUnbounded seedB seedVl seedU' 1 ((0 : ℤ), (0 : ℤ)) :=
  not_subset_chainFull_seed

/-!
**Reading.**  This closes step (1) of the `chainFull`-shear task with outcome **(iii)**: no
name-level reindexing `k ↦ k'` makes `chainFull B vl (u' - T•vl) b₀ k ⊆ chainFull B vl u' b₀ k'`
hold in general — `ChainFullShearUnbounded` is a genuine, kernel-checked obstruction, not a
`sorry`.  Consequently step (2) (does `hbase` transport along the shear) is answered **no** by
the same witness: `hbase` is a periodicity statement *on* `chainFull B vl u' b₀ k`, and since
the sheared family's slices are not eventually absorbed into the original family's slices at any
matching level, there is no general argument transporting a periodicity fact proved on one side
to the other purely from `wedgeFull_shear` + `det_shear`.  This does **not** by itself kill the
two producers (`exists_corner_shear`, `exists_shear_hlt_and_doubly_lower`): both produce `hbase`
*directly at the sheared `u'`*, they do not transport a fact proved at the original `u'`.  What
this section shows is that the "prove at `u'`, transport to `u' - K•vl`" strategy is unavailable
in general — the two producers' own routes (proving the needed fact from scratch at the sheared
direction) remain the only live ones, and whether *they* individually cohere with `hlev`/`hmin`
(also stated at `u'`, not `u' - K•vl`) is still the open half of `OPEN.md #13`, unchanged by this
section. -/

end ChainFullShear

/-! ## §6  `HwinHoleE`'s `hamin` (`L1SweepBridge.lean:588`): a different, easier question

Team-lead's dispatch (2026-09-19, post-freeze): leaf L1's live `sorry` is now
`Nivat.L1SweepBridge.HwinHoleE ξ S vl` (`RegionSteps.lean:1122`), reached via
`wedgeResidualR_of_hwinHoleE` (`L1SweepBridge.lean:615`).  `HwinHoleE`'s body is

```
∃ u', (det u' vl = 1 ∨ det u' vl = -1) ∧
  ∀ B u c a K, a ∈ S → LatticeConvex (S.erase a) → 0 < c → B.Finite →
    (∀ b ∈ S, dot (expNormal (u' - K • vl) vl) a ≤ dot (expNormal (u' - K • vl) vl) b) →  -- hamin
    (∀ z ∈ halfStrip B vl, T u ξ z = T (c•vl) (T u ξ) z) →                                -- hD
    ∃ b₀ ∈ B, ∃ enum, hwin ∧ hK
```

Two questions, per the dispatch, answered separately.

### (1) Does `ChainFullShearUnbounded` (§5) bite here?  **No — reading confirmed.**

`§5`'s obstruction is specifically about *transporting* a fact proved at `chainFull B vl u' b₀ k`
to `chainFull B vl (u' - K•vl) b₀ k'` (or back).  `HwinHoleE`'s own statement never mentions
`chainFull B vl u' …` — every occurrence of `chainFull`/`wedgeFull`/`expNormal` inside it is
already written at the sheared direction `u' - K • vl` (see `hK` above, and `hamin`'s
`expNormal (u' - K • vl) vl`).  Checked directly against `wedgeResidualR_of_hwinHoleE`'s proof
(`L1SweepBridge.lean:615-672`): `K` and `a₁`/`hcorner` come from
`Nivat.L1StraddleWedge.exists_corner_shear`, `hunimod'`/`hw0`/`hconv` are obtained from
`u' - K • vl` via `det_shear`/`isLatticeConvexRegion_wedgeFull_of_unimod'` (shear-*invariance*
facts, not shear-*transport* facts — nothing there compares a `chainFull` at `u'` to a
`chainFull` at `u' - K • vl` the way `ChainFullShearUnbounded` forbids), and `hbase0`,
`N₀`/`hmin`/`hattain` are all built by calling generic lemmas with `u' - K • vl` substituted in
from the start, never by transporting a `u'`-stated fact.  **§5 does not touch this route.**

### (2) Is a single `u'` enough for `hamin`?  **Yes — pre-existing lemma, not the `hcorner` question.**

`hamin` asks for `a` minimizing **one** linear functional (`dot (expNormal (u' - K • vl) vl)`)
over `S` — it has no second (`uCoord`) conjunct.  This is *not* the doubly-minimal `hcorner`
condition from §§1–4 (which needs a common minimizer of *two* functionals simultaneously, and
is refuted for general `S` there); it is the strictly weaker single-functional minimum, which a
nonempty finite `S` always has, for **every** nonzero direction and **every** `u'`/`K`.  This is
already on the tree, unconditionally, as `Nivat.ColleReg.exists_vertex_of_generating_dir`
(`MaxIndexProbe.lean:547`, binders: `{w ≠ 0} → IsGeneratingSet ξ S → ∃ a ∈ S, (∀ b ∈ S,
dot w a ≤ dot w b) ∧ LatticeConvex (S.erase a) ∧ GeneratesAt ξ S a`) — PROTOCOL §20 scan turned this up before writing
anything new, so §6 below only *instantiates* it at `w := expNormal (u' - K • vl) vl`, it does
not re-derive it.  My four §§1–4 counterexamples are about a strictly harder question and are
**not** an obstruction to `hamin`; they should not be cited against this route.  The one
remaining condition to discharge per call is `w ≠ 0`, which the existing proof already supplies
(`hw0` in `wedgeResidualR_of_hwinHoleE`, from `dot_expNormal_vl` at a unimodular pair) — captured
below as `expNormal_shear_ne_zero_of_unimod`, so `hamin`'s witness is available for *every*
`u'`, not merely the one the real proof happens to pick.  **No incompatibility between different
`K`'s witnesses can arise, because `HwinHoleE`'s `∀ a` already lets a different call supply a
different `a` for each `K` — nothing downstream requires the same `a` to work across two `K`'s.**
The actual remaining content of `HwinHoleE` is the `∃ b₀ ∈ B, ∃ enum, hwin ∧ hK` conclusion
(covering `chainFull` by the enumeration), which §6 does not touch. -/

section HwinHoleEVertex

/-- The direction `HwinHoleE`'s `hamin` minimizes is always nonzero at a unimodular sheared
pair — the one side condition `exists_vertex_of_generating_dir` needs. -/
theorem expNormal_shear_ne_zero_of_unimod {u' vl : ℤ × ℤ} (K : ℤ)
    (hunimod : det (u' - K • vl) vl = 1 ∨ det (u' - K • vl) vl = -1) :
    expNormal (u' - K • vl) vl ≠ 0 := by
  intro h
  have := dot_expNormal_vl hunimod
  rw [h] at this
  simp [Nivat.LE2.dot] at this

/-- **`hamin` is satisfiable for every `u'`, `K` (unimodular), and nonempty generating `S`.**
Pure instantiation of `Nivat.MaxIndexProbe.exists_vertex_of_generating_dir` at
`w := expNormal (u' - K • vl) vl` — the single-functional minimum §6(2) shows is the real
content of `hamin`, as opposed to §§1–4's (irrelevant here) doubly-minimal `hcorner`. -/
theorem exists_hamin_witness {A : Type*} {ξ : Config A} {S : Finset (ℤ × ℤ)} {u' vl : ℤ × ℤ}
    (K : ℤ) (hunimod : det (u' - K • vl) vl = 1 ∨ det (u' - K • vl) vl = -1)
    (hgen : IsGeneratingSet ξ S) :
    ∃ a ∈ S, (∀ b ∈ S, dot (expNormal (u' - K • vl) vl) a ≤
        dot (expNormal (u' - K • vl) vl) b) ∧
      Nivat.LatticeConvex (S.erase a) ∧ GeneratesAt ξ S a :=
  Nivat.ColleReg.exists_vertex_of_generating_dir
    (expNormal_shear_ne_zero_of_unimod K hunimod) hgen

end HwinHoleEVertex

/-! ## §18  Axiom receipts

Deletable block (`section AxiomReceipts` … `end AxiomReceipts`), hard rule 3: every headline
claim of this file, checked by the kernel at build time. -/

section AxiomReceipts

#print axioms hunimod_seed
#print axioms expNormal_seed_eq
#print axioms expDual_seed_eq
#print axioms not_doublyMinimal_of_two_points
#print axioms mem_of_generatesAt
#print axioms exists_doublyMinimal_free
#print axioms not_hcorner_of_two_points
#print axioms zonoF_seed_eq
#print axioms not_hcorner_of_zonoF_two_generators
#print axioms mem_wedgeFull_seed
#print axioms dot_expNormal_seed
#print axioms uCoord_seed_zero
#print axioms not_subset_chainFull_seed
#print axioms chainFullShearUnbounded_seed
#print axioms expNormal_shear_ne_zero_of_unimod
#print axioms exists_hamin_witness

end AxiomReceipts

end Nivat.HbaseVertexSeed
