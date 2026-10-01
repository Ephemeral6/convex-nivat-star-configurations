/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.ChainAssemble
import Nivat.External.Colle.LeafAWire
import Nivat.External.Colle.PolyChainSum
import Nivat.External.Colle.LeafAPigeonhole
import Nivat.External.Colle.AhatEnv
import Nivat.External.Colle.LeafAEdgeUnbounded
import Nivat.External.Colle.AGlue

/-!
# `LeafAJSelect` — the `:498-506` `J`-selection package (lane-recp, 2026-09-22)

Consolidates four `sorry`s in `tmp/wip/LeafAAssemble.lean` that all bottleneck on one
piece of unbuilt geometry (`blueprint/LEAF-A.md`, "`bottom`：定位到共享瓶颈 `hgrow`" and
"J-selection 接管" sections): `vJ1`, `hsweep`, `hhp`, `bottom`.

Paper: `scratch/b3_colle2.txt:498-506`.  Team-lead's interface (verbatim, this round):
post-σ `AhatMono : ∀ i j, i ≤ j → Ahat i ⊆ Ahat j` on `Ahat := hatOf (A∘σ) (kk∘σ) vl`;
`Enveloped ↑Sphi (Ahat i)` from `envA_of_max maxA` + `hatOf_eq_shift` +
`isLatticeConvexRegion_shift`/`envOf_shift_mem` (`ChainAssemble.lean:320-324`'s recipe);
`g₁ := LeafAWire.anchorPoint` with `kkOf_mem`/`kkOf_max`.

## Status (2026-09-22, round 19): 0 `sorry`, landed in `Nivat/`

The file is fully sorry-free (`check1.sh` EXIT=0, every `#print axioms` line clean:
`[propext, Classical.choice, Quot.sound]`). `product_pigeonhole` landed 0-sorry
(`LeafAPigeonhole.lean:79`) and is imported directly. `exists_eventually_const_before` and
the whole `J`-selection, both orientations (`Arc_subset_of_mem_Arc`/`_cw`,
`ord_lt_of_mem_Arc`/`_cw`, `exists_J_stable`/`_cw`), are sorry-free. `g_J` pinning is done
both ways (`exists_gJ_pinned_ccw`/`_cw`, via `PolyChainSum.chain_ccw_final`/`chain_cw_final`)
— per team-lead's 2026-09-22 ruling the `hℓbdd` hypothesis from an earlier round was
dropped (false and unneeded: `ℓ`'s own face is `Â_∞`'s unbounded semi-infinite edge, and
its `faceLen` cancels algebraically once `g₁` is read as the *pinned end/start* of `ℓ`'s
face rather than `faceStart ℓ` alone). `hgrow` is done, **both orientations**, sorry-free:
`faceLen_mono_of_suppVal_eq` (encard-monotonicity when `suppVal` matches, via
`Set.encard_mono` + `ENat.toNat_le_toNat`, orientation-agnostic, shared by both) plus
`hgrow_of_pinned_ccw`/`hgrow_of_pinned_cw` (the "sandwich" argument pinning
`suppVal (Ahat j) J = dot J g_J` for every `j ≥ σ i₀`, then reading off unboundedness of
`faceLen` along `σ`, then `face_eq_segment`/`faceEnd_mem` for membership — ccw walks
`g_J + t•dir J` forward from the pinned start, cw walks `g_J − t•dir J` backward from the
pinned end) — matches `ray_of_pinned_growth`'s consumer shape (`ItemII.lean:786`) exactly.
Finally, `exists_J_of_edge_unbounded` (new this round) closes the last gap: it imports
`Nivat.LeafAEdgeUnbounded.exists_edge_unbounded` (`LeafAEdgeUnbounded.lean:165`, lane-leafa,
landed 0-sorry, axiom-clean) and `rcases`es its two-disjunct conclusion — which now exports
the exact sign tag (`0 < det nℓ ν` vs. `0 < det ν nℓ`) that `exists_J_stable`/`_cw` need —
into `Or.inl (exists_J_stable ...)` / `Or.inr (exists_J_stable_cw ...)`. The `J`-selection
package is now complete on both orientations, with no remaining `sorry` anywhere in this
file. `hhp`/`hsweep`/`vJ1` assembly (the four sorries in `tmp/wip/LeafAAssemble.lean`) is
lane-shell's scope, consuming this file's `hgrow`/`g_J` primitives (`blueprint/LEAF-A.md`,
"`g_J` 钉住" section, has the full writeup) — **not itself closed by this file landing**,
only unblocked by it.

**§3b (`dot_J_p_ne_zero`) and §4 (`nprevJ`/`vJ1`/`hsupp_prev`/`hgJ_level`, both 2026-09-22,
team-lead's fork ruling and follow-up delivery request)**: `dot_J_p_ne_zero` discharges
`ChainDataGeomParts.dot_nJ_p` taking `nJ := J`. §4 supplies lane-chain's `bottom`
(`LeafABottom.lean`) inputs: `exists_fan_pred`/`exists_nprevJ_vJ1` produce `nprevJ`
(the fan-adjacent predecessor of `J`, or `ℓ` itself when `Arc ℓ J = ∅`) and
`vJ1 := dir nprevJ` with its two defining identities; `hsupp_prev` gives the `nprevJ`-support
bound on all of `⋃ Ahat (σ ·)` (not just `i ≥ i₀`); `hgJ_level` is the trivial `rfl` once
`cJ := dot (-J) g_J` — that assignment is PROVEN (not guessed) by
`ShellRegionJ.hhp_of_faceStart_pinned` (team-lead, 2026-09-22). All sorry-free, `check1.sh`
EXIT=0, every new `#print axioms` line clean.

**Note for the integrator**: this file was moved from `tmp/wip/LeafAJSelect.lean` to
`Nivat/External/Colle/LeafAJSelect.lean` by lane-recp under §30 self-integration authority.
`check1.sh` on the new path is EXIT=0 and every `#print axioms` line is clean, but lane-recp
has not run (and is not permitted to run) `gen_all.py` / `lake build` / `gate.py`. Those are
the integrator's pass.

## §1. Numeric instance (hand-computed in `blueprint/LEAF-A.md`, Lean-checked here)

Pentagon family `A_i` (`i ≥ 1`), ccw vertices `(0,0),(1,0),(2,1),(2,i+1),(0,i+1)`.
Confirms: two pinned edges (`(0,0)-(1,0)` dir `(1,0)=vl`, `(1,0)-(2,1)` dir `(1,1)`) chain
to a fixed `g_J := (2,1)`, and the third edge (`(2,1)-(2,i+1)`, dir `(0,1) = vJ`) grows
without bound and starts exactly at `g_J` for every `i`. This is the shape `hgrow` needs.
-/

set_option autoImplicit false

namespace Nivat.LeafAJSelect

open Nivat Nivat.LE2 Nivat.MaxEnv Nivat.PolyChain Nivat.PolyChainSum

/-! ### §1. Numeric instance -/

namespace PentagonNumeric

/-- The pentagon `A_i`, described directly as a lattice-point predicate: `0 ≤ x ≤ 2`,
`0 ≤ y ≤ i+1`, `y ≥ x - 1`. The last constraint is the two pinned bottom edges
`(0,0)-(1,0)` (`x ≤ 1`, forced by `y ≥ 0`) and `(1,0)-(2,1)` (`x ∈ [1,2]`, the binding
case of `y ≥ x-1`) collapsed into one inequality since `x - 1 ≤ 0 ≤ y` is automatic for
`x ≤ 1`. Matches the ccw vertex list `(0,0),(1,0),(2,1),(2,i+1),(0,i+1)`. -/
def A (i : ℕ) : Set (ℤ × ℤ) :=
  {z : ℤ × ℤ | 0 ≤ z.1 ∧ z.1 ≤ 2 ∧ 0 ≤ z.2 ∧ z.2 ≤ (i : ℤ) + 1 ∧ z.1 - 1 ≤ z.2}

def gJ : ℤ × ℤ := (2, 1)
def vJ : ℤ × ℤ := (0, 1)
def g₁ : ℤ × ℤ := (0, 0)

/-- The normal of `J`'s own face (the growing right edge `(2,1)-(2,i+1)`, direction `vJ`):
`dir nJ = vJ` forces `nJ = (1,0)`. -/
def nJ : ℤ × ℤ := (1, 0)

/-- `nprevJ`, the normal of the fan-predecessor edge `(1,0)-(2,1)` (direction `(1,1)`):
`dir nprevJ = (1,1)` forces `nprevJ = (1,-1)`. -/
def nprevJ : ℤ × ℤ := (1, -1)

/-- `vJ1 := dir nprevJ`, matching `exists_nprevJ_vJ1`'s output. -/
def vJ1 : ℤ × ℤ := (1, 1)

/-- §4 sanity check on the pentagon instance: `0 < det nprevJ nJ` (`exists_fan_pred`'s output
shape), `dot nprevJ vJ1 = 0`, and `dot (-nJ) vJ1 < 0` — exactly the three facts
`exists_nprevJ_vJ1` proves in general. -/
theorem nprevJ_instance :
    0 < Nivat.det nprevJ nJ ∧ Nivat.LE2.dot nprevJ vJ1 = 0 ∧
      Nivat.LE2.dot (-nJ) vJ1 < 0 := by
  refine ⟨by decide, by decide, by decide⟩

/-- `g_J` is pinned: it lies in every `A i`, independent of `i`. -/
theorem gJ_mem (i : ℕ) : gJ ∈ A i := by
  simp only [A, gJ, Set.mem_setOf_eq]
  refine ⟨by norm_num, le_refl _, by norm_num, ?_, by norm_num⟩
  omega

/-- `hgrow`'s shape on the pentagon instance: for every `N`, some `A i` contains the
whole segment `g_J, g_J+vJ, …, g_J+N•vJ`. -/
theorem hgrow_instance : ∀ N : ℕ, ∃ i : ℕ, ∀ t : ℕ, t ≤ N →
    gJ + (t : ℤ) • vJ ∈ A i := by
  intro N
  refine ⟨N, fun t ht => ?_⟩
  have ht' : (t : ℤ) ≤ (N : ℤ) := by exact_mod_cast ht
  simp only [A, gJ, vJ, Set.mem_setOf_eq, Prod.smul_mk, smul_eq_mul, mul_zero, mul_one,
    Prod.mk_add_mk, add_zero]
  refine ⟨by norm_num, by norm_num, by positivity, by omega, by omega⟩

/-- Sanity: the growing edge really is unbounded — no single `i` bounds `t`. -/
theorem not_uniformly_bounded : ¬ ∃ i : ℕ, ∀ t : ℕ, gJ + (t : ℤ) • vJ ∈ A i := by
  rintro ⟨i, hi⟩
  have h := hi (i + 1)
  simp only [A, gJ, vJ, Set.mem_setOf_eq, Prod.smul_mk, smul_eq_mul, mul_zero, mul_one,
    Prod.mk_add_mk, add_zero] at h
  obtain ⟨-, -, -, h4, -⟩ := h
  push_cast at h4
  omega

/-- §4b sanity check, `cw` mirror: the pentagon's edge *after* `J` in ccw order
(`(2,i+1)-(0,i+1)`, direction `(-2,0)`, primitive `(-1,0)`) is `nJ`'s `cw`-side fan-neighbour
— `dir nprevJcw = (-1,0)` forces `nprevJcw = (0,1)`, and `vJ1cw := -dir nprevJcw = (1,0)`. -/
def nprevJcw : ℤ × ℤ := (0, 1)

def vJ1cw : ℤ × ℤ := (1, 0)

theorem nprevJcw_instance :
    0 < Nivat.det nJ nprevJcw ∧ Nivat.LE2.dot nprevJcw vJ1cw = 0 ∧
      Nivat.LE2.dot (-nJ) vJ1cw < 0 := by
  refine ⟨by decide, by decide, by decide⟩

end PentagonNumeric

/-! ### §2. The two geometric sub-lemmas (the actual content of `:498-506`)

⚠ **2026-09-26 订正（lane-tower-hlev 发现，集成者复核）**：本标题原写「(`sorry`, ...)」，
**已为假**——本文件 0 `sorry`（`sorries.sh` 只报链上两条，都不在这里；`grep` 到的 15 处
`sorry` 全在散文里）。`exists_J_of_edge_unbounded`（`:321`）以下整条链都是 sorry-free。
这行烂注释曾让下游误以为 `:498-506` 还没落地。 -/

variable {Ahat : ℕ → Set (ℤ × ℤ)} {Sphi : Finset (ℤ × ℤ)}

/-! ### §2b. Cyclic-order transitivity (sorry-free, closes the gap found this round)

`blueprint/LEAF-HSUPP.md` §2(C) ("半平面上的行列式序") sketches this but I couldn't find it
landed as a reusable lemma; `chain_ccw_aux` (`PolyChainSum.lean:145,190`) uses the identical
`e := dir ν₀` / `e := -dir n` witnesses inline, which is the pattern below makes exportable:
if `μ` is strictly between `ℓ` and `J` (`μ ∈ Arc ℓ J`), then everything strictly between `ℓ`
and `μ` is also strictly between `ℓ` and `J` — witness `e := dir ℓ`, since `dot (dir ℓ) x =
det ℓ x` (`dot_dir_left`) turns `0 < det ℓ ν`, `0 < det ℓ μ`, `0 < det ℓ J` into the three
`dot e · > 0` hypotheses `PolyChain.det_pos_trans` needs. -/

theorem Arc_subset_of_mem_Arc {T : Set (ℤ × ℤ)} (hfin : T.Finite) {ℓ μ J : ℤ × ℤ}
    (hℓJ : 0 < det ℓ J) (hμ : μ ∈ Nivat.PolyChainSum.Arc hfin ℓ J) :
    Nivat.PolyChainSum.Arc hfin ℓ μ ⊆ Nivat.PolyChainSum.Arc hfin ℓ J := by
  intro ν hν
  obtain ⟨hνE, hℓν, hνμ⟩ := Nivat.PolyChainSum.mem_Arc.mp hν
  refine Nivat.PolyChainSum.mem_Arc.mpr ⟨hνE, hℓν, ?_⟩
  obtain ⟨_, hℓμ, hμJ⟩ := Nivat.PolyChainSum.mem_Arc.mp hμ
  exact Nivat.PolyChain.det_pos_trans (e := dir ℓ)
    (by rw [Nivat.PolyChainSum.dot_dir_left]; exact hℓν)
    (by rw [Nivat.PolyChainSum.dot_dir_left]; exact hℓμ)
    (by rw [Nivat.PolyChainSum.dot_dir_left]; exact hℓJ) hνμ hμJ

/-- `ord := |Arc ℓ ·|` strictly decreases moving from `J` to any `μ` strictly between `ℓ`
and `J` — the fact that turns "`J` has minimal `ord` among unbounded edges" into "every
edge strictly between `ℓ` and `J` is bounded", which is exactly the finite index set
`exists_eventually_const_before`/`product_pigeonhole` needs to stabilise. -/
theorem ord_lt_of_mem_Arc {T : Set (ℤ × ℤ)} (hfin : T.Finite) {ℓ μ J : ℤ × ℤ}
    (hℓJ : 0 < det ℓ J) (hμ : μ ∈ Nivat.PolyChainSum.Arc hfin ℓ J) :
    (Nivat.PolyChainSum.Arc hfin ℓ μ).card < (Nivat.PolyChainSum.Arc hfin ℓ J).card := by
  have hsub := Arc_subset_of_mem_Arc hfin hℓJ hμ
  have hnotmem : μ ∉ Nivat.PolyChainSum.Arc hfin ℓ μ := by
    intro hmem
    have hself := (Nivat.PolyChainSum.mem_Arc.mp hmem).2.2
    rw [Nivat.LE2.det_self] at hself
    exact absurd hself (lt_irrefl 0)
  exact Finset.card_lt_card ⟨hsub, fun hcon => hnotmem (hcon hμ)⟩

/-- **`J`-selection, sorry-free.** Among the edges strictly ccw of `ℓ` with unbounded
`faceLen`, pick the one minimizing `ord ν := |Arc ℓ ν|` (exists: `E Sphi` is finite,
`Finset.exists_min_image`). Minimality + `ord_lt_of_mem_Arc` then forces every edge
strictly between `ℓ` and `J` to be bounded — free once `ord_lt_of_mem_Arc` is in hand,
no further geometry. This is the wiring step that turns `exists_edge_unbounded`'s raw
existential into the actual paper object `J` (`scratch/b3_colle2.txt:498-506`). -/
theorem exists_J_stable
    {A : ℕ → Set (ℤ × ℤ)} {ℓ : ℤ × ℤ}
    (hunb : ∃ ν ∈ E (↑Sphi : Set (ℤ × ℤ)), 0 < det ℓ ν ∧
      ¬ ∃ L : ℕ, ∀ i, faceLen (A i) ν ≤ L) :
    ∃ J ∈ E (↑Sphi : Set (ℤ × ℤ)), 0 < det ℓ J ∧
      (¬ ∃ L : ℕ, ∀ i, faceLen (A i) J ≤ L) ∧
      ∀ μ ∈ Nivat.PolyChainSum.Arc (Sphi.finite_toSet) ℓ J,
        ∃ L : ℕ, ∀ i, faceLen (A i) μ ≤ L := by
  classical
  set ord : ℤ × ℤ → ℕ := fun ν => (Nivat.PolyChainSum.Arc (Sphi.finite_toSet) ℓ ν).card
    with hord_def
  set U : Finset (ℤ × ℤ) :=
    (finite_E_of_finite (Sphi.finite_toSet)).toFinset.filter
      (fun ν => 0 < det ℓ ν ∧ ¬ ∃ L : ℕ, ∀ i, faceLen (A i) ν ≤ L)
    with hU_def
  have hUne : U.Nonempty := by
    obtain ⟨ν, hνE, hℓν, hνunb⟩ := hunb
    refine ⟨ν, ?_⟩
    rw [hU_def, Finset.mem_filter, (finite_E_of_finite (Sphi.finite_toSet)).mem_toFinset]
    exact ⟨hνE, hℓν, hνunb⟩
  obtain ⟨J, hJU, hJmin⟩ := Finset.exists_min_image U ord hUne
  rw [hU_def, Finset.mem_filter, (finite_E_of_finite (Sphi.finite_toSet)).mem_toFinset] at hJU
  obtain ⟨hJE, hℓJ, hJunb⟩ := hJU
  refine ⟨J, hJE, hℓJ, hJunb, fun μ hμ => ?_⟩
  by_contra hμunb
  have hμU : μ ∈ U := by
    obtain ⟨_, hℓμ, _⟩ := Nivat.PolyChainSum.mem_Arc.mp hμ
    rw [hU_def, Finset.mem_filter, (finite_E_of_finite (Sphi.finite_toSet)).mem_toFinset]
    exact ⟨(Nivat.PolyChainSum.mem_Arc.mp hμ).1, hℓμ, hμunb⟩
  have hle := hJmin μ hμU
  have hlt := ord_lt_of_mem_Arc (Sphi.finite_toSet) hℓJ hμ
  simp only [hord_def] at hle
  omega

/-! ### §2c. `cw` mirror (team-lead's instruction #2, 2026-09-22)

`chain_cw_final`'s raw filter is `fun ν => 0 < det ν ν₀ ∧ 0 < det n ν`, i.e. (with `ν₀ := ℓ`,
`n := J`) exactly `Arc J ℓ` (`Arc a b := filter (fun ν => 0 < det a ν ∧ 0 < det ν b)`, so
`Arc J ℓ`'s raw filter is `0 < det J ν ∧ 0 < det ν ℓ` — matches after `Finset.mem_filter`
unfolding, no `and_comm` needed since `Arc`'s own argument order already has the fixed point
`ℓ` in the second slot). The subset/order lemmas below are the *fixed-second-argument*
mirrors of `Arc_subset_of_mem_Arc`/`ord_lt_of_mem_Arc`, using witness `e := -dir ℓ` and
`dot_neg_dir : dot (-dir n) x = det x n` in place of `e := dir ℓ`/`dot_dir_left`. -/

theorem Arc_subset_of_mem_Arc_cw {T : Set (ℤ × ℤ)} (hfin : T.Finite) {ℓ μ J : ℤ × ℤ}
    (hJℓ : 0 < det J ℓ) (hμ : μ ∈ Nivat.PolyChainSum.Arc hfin J ℓ) :
    Nivat.PolyChainSum.Arc hfin μ ℓ ⊆ Nivat.PolyChainSum.Arc hfin J ℓ := by
  intro ν hν
  obtain ⟨hνE, hμν, hνℓ⟩ := Nivat.PolyChainSum.mem_Arc.mp hν
  refine Nivat.PolyChainSum.mem_Arc.mpr ⟨hνE, ?_, hνℓ⟩
  obtain ⟨_, hJμ, hμℓ⟩ := Nivat.PolyChainSum.mem_Arc.mp hμ
  exact Nivat.PolyChain.det_pos_trans (e := -dir ℓ)
    (by rw [Nivat.PolyChainSum.dot_neg_dir]; exact hJℓ)
    (by rw [Nivat.PolyChainSum.dot_neg_dir]; exact hμℓ)
    (by rw [Nivat.PolyChainSum.dot_neg_dir]; exact hνℓ)
    hJμ hμν

theorem ord_lt_of_mem_Arc_cw {T : Set (ℤ × ℤ)} (hfin : T.Finite) {ℓ μ J : ℤ × ℤ}
    (hJℓ : 0 < det J ℓ) (hμ : μ ∈ Nivat.PolyChainSum.Arc hfin J ℓ) :
    (Nivat.PolyChainSum.Arc hfin μ ℓ).card < (Nivat.PolyChainSum.Arc hfin J ℓ).card := by
  have hsub := Arc_subset_of_mem_Arc_cw hfin hJℓ hμ
  have hnotmem : μ ∉ Nivat.PolyChainSum.Arc hfin μ ℓ := by
    intro hmem
    have hself := (Nivat.PolyChainSum.mem_Arc.mp hmem).2.1
    rw [Nivat.LE2.det_self] at hself
    exact absurd hself (lt_irrefl 0)
  exact Finset.card_lt_card ⟨hsub, fun hcon => hnotmem (hcon hμ)⟩

/-- **`J`-selection, `cw` mirror, sorry-free.** Among the edges strictly cw of `ℓ` (i.e.
`0 < det ν ℓ`) with unbounded `faceLen`, pick the one minimizing `ord' ν := |Arc ν ℓ|`.
Same proof as `exists_J_stable` with the fixed argument moved from the first to the second
slot of `Arc`, per team-lead's "same proof with `det` arguments swapped". -/
theorem exists_J_stable_cw
    {A : ℕ → Set (ℤ × ℤ)} {ℓ : ℤ × ℤ}
    (hunb : ∃ ν ∈ E (↑Sphi : Set (ℤ × ℤ)), 0 < det ν ℓ ∧
      ¬ ∃ L : ℕ, ∀ i, faceLen (A i) ν ≤ L) :
    ∃ J ∈ E (↑Sphi : Set (ℤ × ℤ)), 0 < det J ℓ ∧
      (¬ ∃ L : ℕ, ∀ i, faceLen (A i) J ≤ L) ∧
      ∀ μ ∈ Nivat.PolyChainSum.Arc (Sphi.finite_toSet) J ℓ,
        ∃ L : ℕ, ∀ i, faceLen (A i) μ ≤ L := by
  classical
  set ord : ℤ × ℤ → ℕ := fun ν => (Nivat.PolyChainSum.Arc (Sphi.finite_toSet) ν ℓ).card
    with hord_def
  set U : Finset (ℤ × ℤ) :=
    (finite_E_of_finite (Sphi.finite_toSet)).toFinset.filter
      (fun ν => 0 < det ν ℓ ∧ ¬ ∃ L : ℕ, ∀ i, faceLen (A i) ν ≤ L)
    with hU_def
  have hUne : U.Nonempty := by
    obtain ⟨ν, hνE, hνℓ, hνunb⟩ := hunb
    refine ⟨ν, ?_⟩
    rw [hU_def, Finset.mem_filter, (finite_E_of_finite (Sphi.finite_toSet)).mem_toFinset]
    exact ⟨hνE, hνℓ, hνunb⟩
  obtain ⟨J, hJU, hJmin⟩ := Finset.exists_min_image U ord hUne
  rw [hU_def, Finset.mem_filter, (finite_E_of_finite (Sphi.finite_toSet)).mem_toFinset] at hJU
  obtain ⟨hJE, hJℓ, hJunb⟩ := hJU
  refine ⟨J, hJE, hJℓ, hJunb, fun μ hμ => ?_⟩
  by_contra hμunb
  have hμU : μ ∈ U := by
    obtain ⟨hμE, _, hμℓ⟩ := Nivat.PolyChainSum.mem_Arc.mp hμ
    rw [hU_def, Finset.mem_filter, (finite_E_of_finite (Sphi.finite_toSet)).mem_toFinset]
    exact ⟨hμE, hμℓ, hμunb⟩
  have hle := hJmin μ hμU
  have hlt := ord_lt_of_mem_Arc_cw (Sphi.finite_toSet) hJℓ hμ
  simp only [hord_def] at hle
  omega

/-- **`exists_edge_unbounded`** — closed this round: `lane-leafa`'s
`Nivat.LeafAEdgeUnbounded.exists_edge_unbounded` (`LeafAEdgeUnbounded.lean:165`) now exports
the sign tag `exists_J_stable`/`_cw`'s `hunb` needs, as a disjunction whose two disjuncts are
literally those two `hunb` shapes. This corollary just `rcases`es the disjunction and
dispatches to whichever `exists_J_stable` variant matches, producing a single `J` selection
result tagged by which orientation held. -/
theorem exists_J_of_edge_unbounded
    {A B : ℕ → Set (ℤ × ℤ)} {nℓ : ℤ × ℤ} {cz : ℤ} (hnℓ : nℓ ≠ 0)
    (hItemII : Nivat.Colle35.ItemII B nℓ cz) (hsubBA : ∀ i, B i ⊆ A i)
    (hfin : ∀ i, (A i).Finite)
    (henv : ∀ i, Enveloped (↑Sphi : Set (ℤ × ℤ)) (A i))
    (hnℓE : nℓ ∈ E (↑Sphi : Set (ℤ × ℤ)))
    (hnegnℓE : (-nℓ) ∈ E (↑Sphi : Set (ℤ × ℤ))) :
    (∃ J ∈ E ↑Sphi, 0 < det nℓ J ∧ (¬ ∃ L : ℕ, ∀ i, faceLen (A i) J ≤ L) ∧
      ∀ μ ∈ Nivat.PolyChainSum.Arc (Sphi.finite_toSet) nℓ J,
        ∃ L : ℕ, ∀ i, faceLen (A i) μ ≤ L) ∨
    (∃ J ∈ E ↑Sphi, 0 < det J nℓ ∧ (¬ ∃ L : ℕ, ∀ i, faceLen (A i) J ≤ L) ∧
      ∀ μ ∈ Nivat.PolyChainSum.Arc (Sphi.finite_toSet) J nℓ,
        ∃ L : ℕ, ∀ i, faceLen (A i) μ ≤ L) := by
  rcases Nivat.LeafAEdgeUnbounded.exists_edge_unbounded hnℓ hItemII hsubBA hfin henv hnℓE
      hnegnℓE with hunb | hunb
  · exact Or.inl (exists_J_stable (A := A) (ℓ := nℓ) hunb)
  · exact Or.inr (exists_J_stable_cw (A := A) (ℓ := nℓ) hunb)

/-- team-lead 2026-09-22 ruling, "(a) derive everything from `J`": since `0 < det nℓ J`
(the ccw disjunct's tag from `exists_J_stable`), `J` cannot equal `nℓ` or `-nℓ`
(`det nℓ nℓ = 0` resp. `det nℓ (-nℓ) = -det nℓ nℓ = 0`, contradicting strict positivity). -/
theorem ne_and_ne_neg_of_det_pos_ccw {nℓ J : ℤ × ℤ} (h : 0 < det nℓ J) :
    J ≠ nℓ ∧ J ≠ -nℓ := by
  refine ⟨fun he => ?_, fun he => ?_⟩
  · rw [he, det_self] at h; exact lt_irrefl 0 h
  · rw [he, det_neg_right, det_self] at h; omega

/-- Mirror of `ne_and_ne_neg_of_det_pos_ccw` for the cw disjunct's tag `0 < det J nℓ`. -/
theorem ne_and_ne_neg_of_det_pos_cw {nℓ J : ℤ × ℤ} (h : 0 < det J nℓ) :
    J ≠ nℓ ∧ J ≠ -nℓ := by
  refine ⟨fun he => ?_, fun he => ?_⟩
  · rw [he, det_self] at h; exact lt_irrefl 0 h
  · rw [he, det_neg_left, det_self] at h; omega

/-- If `J` is primitive and distinct from `±nℓ` (both primitive), and `nℓ ⟂ vl`, then
`J` is not `⟂ vl`: two distinct (up to sign) primitive vectors cannot share the same
perpendicular direction (`Nivat.AGlue.eq_or_neg_of_primitive_of_perp`). -/
theorem dot_J_vl_ne_zero {J nℓ vl : ℤ × ℤ}
    (hJprim : Primitive J) (hnℓprim : Primitive nℓ) (hvl : vl ≠ 0)
    (hperp : dot nℓ vl = 0) (hJne : J ≠ nℓ ∧ J ≠ -nℓ) : dot J vl ≠ 0 := by
  intro hcontra
  rcases Nivat.AGlue.eq_or_neg_of_primitive_of_perp hvl hJprim hnℓprim hcontra hperp with h | h
  · exact hJne.1 h
  · exact hJne.2 h

/-- **Consumer target for `LeafAAssemble.lean`'s `dot_nJ_p` obligation.** If `p` is a nonzero
integer multiple of `vl` (`p = k • vl`, `k ≠ 0`), and `J ≠ ±nℓ` with `nℓ ⟂ vl`, then `J ⟂̸ p`. -/
theorem dot_J_p_ne_zero {J nℓ vl p : ℤ × ℤ} {k : ℤ}
    (hJprim : Primitive J) (hnℓprim : Primitive nℓ) (hvl : vl ≠ 0)
    (hperp : dot nℓ vl = 0) (hJne : J ≠ nℓ ∧ J ≠ -nℓ)
    (hk : k ≠ 0) (hp : p = k • vl) : dot J p ≠ 0 := by
  have hvlne : dot J vl ≠ 0 := dot_J_vl_ne_zero hJprim hnℓprim hvl hperp hJne
  rw [hp, dot_comm J (k • vl), dot_smul, dot_comm vl J]
  exact mul_ne_zero hk hvlne

#print axioms ne_and_ne_neg_of_det_pos_ccw
#print axioms ne_and_ne_neg_of_det_pos_cw
#print axioms dot_J_p_ne_zero

/-- **Generic helper, sorry-free**: if every `Ahat i` sits inside the same fixed box around
`g₁` (uniformly in `i`), the union is finite. Not needed by `exists_edge_unbounded`'s final
shape (team-lead's `ItemII`-diameter argument bypasses the union), kept as a standalone
fact in case a later step wants it. -/
theorem not_finite_of_forall_mem_box {Ahat : ℕ → Set (ℤ × ℤ)}
    {g₁ : ℤ × ℤ} {C : ℤ}
    (hbox : ∀ i, ∀ z ∈ Ahat i, |z.1 - g₁.1| ≤ C ∧ |z.2 - g₁.2| ≤ C) :
    (⋃ i, Ahat i).Finite := by
  apply ((Finset.Icc (g₁.1 - C) (g₁.1 + C) ×ˢ Finset.Icc (g₁.2 - C) (g₁.2 + C)).finite_toSet).subset
  rintro z hz
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
  obtain ⟨h1, h2⟩ := hbox i z hi
  rw [abs_le] at h1 h2
  simp only [Finset.coe_product, Finset.coe_Icc, Set.mem_prod, Set.mem_Icc]
  omega

/-- **Edges before the first-unbounded one eventually stabilise** — now a free
consequence of `Nivat.product_pigeonhole` (landed 0-sorry by lane-leafa,
`LeafAPigeonhole.lean:79`), applied to `f i j := faceLen (Ahat i) (e.symm j)` for the
canonical `Finset.equivFin`-style enumeration `e : {x // x ∈ T} ≃ Fin T.card`. Kept as
its own named lemma since callers want the `Finset`-indexed shape, not the raw `Fin k`
one. -/
theorem exists_eventually_const_before
    (T : Finset (ℤ × ℤ)) (hfin : ∀ i, (Ahat i).Finite)
    (hbound : ∀ ν ∈ T, ∃ L : ℕ, ∀ i, faceLen (Ahat i) ν ≤ L) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∃ i₀ : ℕ, ∀ ν ∈ T, ∀ i ≥ i₀, faceLen (Ahat (σ i)) ν = faceLen (Ahat (σ i₀)) ν := by
  classical
  choose Lf hLf using hbound
  set e : {x // x ∈ T} ≃ Fin T.card :=
    (Fintype.equivFin {x // x ∈ T}).trans (finCongr (Fintype.card_coe T)) with he_def
  set M : ℕ := Finset.univ.sup (fun ν : {x // x ∈ T} => Lf (ν : ℤ × ℤ) ν.2) with hM_def
  set f : ℕ → Fin T.card → ℕ := fun i j => faceLen (Ahat i) ((e.symm j : {x // x ∈ T}) : ℤ × ℤ)
    with hf_def
  have hbdd : ∀ i j, f i j ≤ M := by
    intro i j
    rw [hf_def, hM_def]
    exact le_trans (hLf _ (e.symm j).2 i)
      (Finset.le_sup (f := fun ν : {x // x ∈ T} => Lf (ν : ℤ × ℤ) ν.2) (Finset.mem_univ (e.symm j)))
  obtain ⟨σ, hσmono, i₀, hr⟩ := Nivat.product_pigeonhole f hbdd
  refine ⟨σ, hσmono, i₀, fun ν hν i hi => ?_⟩
  have := hr (e ⟨ν, hν⟩) i hi
  simp only [hf_def, Equiv.symm_apply_apply] at this
  exact this

/-! ### §3. Downstream assembly — status note (2026-09-22, superseded by the landed proofs above;
    updated 2026-09-22 per team-lead's fork ruling)

**This subsection is historical planning prose from an earlier round; it is not a spec.**
`g_J` pinning (`exists_gJ_pinned_ccw`/`_cw`) and `hgrow` (`hgrow_of_pinned_ccw`/`_cw`) are
now landed above exactly as `ray_of_pinned_growth` (`ItemII.lean:786`) needs them.

**team-lead's ruling (2026-09-22) settles the `nJ` fork as "(a): everything is derived from
`J`"** — `nJ := ±J`, `vJ := ±dir J`/`vJ1 := ±dir J`, `F : FaceBlock S nJ vJ` must all trace
back to *this file's* `J` (from `exists_J_stable`/`exists_J_of_edge_unbounded`), not to an
independent witness. In particular **`Nivat.HsweepFeed.exists_hsweep_witness`
(`HsweepFeed.lean:76`, witness `nJ := -vJ1` for an arbitrary nonzero `vJ1`) must NOT be used**
to discharge `hsweep` in this assembly: its `nJ` is defined purely in terms of its own `vJ1`
and has no relationship to `J`, so plugging it in would make `ChainDataGeomParts`'s `nJ`/`vJ`/
`vJ1`/`F` fields refer to inconsistent objects even though the types line up. See
`blueprint/LEAF-A.md` (§ "team-lead 2026-09-22 裁决") for the full record. The correct route
for `hsweep` is `hsweepW_of_fan_adjacent`-style derivation from `J`'s fan-adjacency (lane-shell,
same blueprint section), not `HsweepFeed`.

`dot_nJ_p : dot nJ p ≠ 0` (the `ChainDataGeomParts` field, `ChainPartsFeed.lean:195-199`) now
HAS a landed candidate proof in this file: `dot_J_p_ne_zero` (below `exists_J_of_edge_unbounded`),
taking `nJ := J`, using `J ≠ ±nℓ` (from `ne_and_ne_neg_of_det_pos_ccw`/`_cw`) and `p ∥ vl`. -/



#print axioms Nivat.LeafAJSelect.PentagonNumeric.gJ_mem
#print axioms Nivat.LeafAJSelect.PentagonNumeric.hgrow_instance
#print axioms Nivat.LeafAJSelect.PentagonNumeric.not_uniformly_bounded
#print axioms Nivat.LeafAJSelect.PentagonNumeric.nprevJ_instance
#print axioms Nivat.LeafAJSelect.PentagonNumeric.nprevJcw_instance

#print axioms Nivat.LeafAJSelect.Arc_subset_of_mem_Arc
#print axioms Nivat.LeafAJSelect.ord_lt_of_mem_Arc
#print axioms Nivat.LeafAJSelect.exists_J_stable
#print axioms Nivat.LeafAJSelect.exists_J_of_edge_unbounded

#print axioms Nivat.LeafAJSelect.exists_eventually_const_before

/-! ### §3a. Bridging `E (Ahat i) = E Sphi` and `g_J` pinning -/

/-- **`Arc` is invariant under `Enveloped ↑Sphi ·`**: the ccw/cw chain-sum index set for any
`T` enveloped by `Sphi` coincides with the fixed `Arc` computed against `Sphi` itself. This is
what lets `chain_ccw_final`/`chain_cw_final` (stated per-`T`, i.e. per-`Ahat i`) be combined
with `exists_J_stable`/`exists_eventually_const_before` (stated against the fixed ambient
`E ↑Sphi`). 原文：Definition 3.2 (`b3_colle2.txt:402`), `E(𝒯) ⊆ E(𝒰)` with equal cardinality. -/
theorem Arc_eq_of_enveloped {T : Set (ℤ × ℤ)} (hTfin : T.Finite)
    (hSfin : (E (↑Sphi : Set (ℤ × ℤ))).Finite) (hSarea : PosArea (↑Sphi : Set (ℤ × ℤ)))
    (henv : Enveloped (↑Sphi : Set (ℤ × ℤ)) T) (ν₀ n : ℤ × ℤ) :
    Nivat.PolyChainSum.Arc hTfin ν₀ n = Nivat.PolyChainSum.Arc (Sphi.finite_toSet) ν₀ n := by
  have hE : E T = E (↑Sphi : Set (ℤ × ℤ)) := Nivat.AhatEnv.E_eq_of_enveloped hSfin hSarea henv
  apply Finset.ext
  intro ν
  rw [Nivat.PolyChainSum.mem_Arc, Nivat.PolyChainSum.mem_Arc, hE]

/-- **`g_J` is pinned along a stabilising subsequence** (paper `:498-506`, ccw case: `g₁` is
the *pinned end* of `ℓ`'s face, `g₁ = faceStart (Ahat i) ℓ + faceLen (Ahat i) ℓ • dir ℓ`,
team-lead's 2026-09-22 correction — `ℓ`'s own face length is `-nℓ`'s unbounded semi-infinite
edge and is *not* assumed bounded; it cancels algebraically against the `faceLen ν₀ • dir ν₀`
term of `chain_ccw_final`, so no `hℓbdd` hypothesis is needed). Combines
`exists_eventually_const_before` (uniform eventual constancy of every `faceLen` appearing in
the `Arc ℓ J` chain sum) with `chain_ccw_final` (transported from `E (Ahat i)` to the fixed
`E ↑Sphi` via `Arc_eq_of_enveloped`) to pin `faceStart (Ahat (σ i)) J` to a single value `g_J`
for all `i ≥ i₀`. -/
theorem exists_gJ_pinned_ccw
    {Ahat : ℕ → Set (ℤ × ℤ)} {ℓ J g₁ : ℤ × ℤ}
    (hfin : ∀ i, (Ahat i).Finite) (hlc : ∀ i, IsLatticeConvexRegion (Ahat i))
    (henv : ∀ i, Enveloped (↑Sphi : Set (ℤ × ℤ)) (Ahat i))
    (hSfin : (E (↑Sphi : Set (ℤ × ℤ))).Finite) (hSarea : PosArea (↑Sphi : Set (ℤ × ℤ)))
    (hℓE : ℓ ∈ E (↑Sphi : Set (ℤ × ℤ))) (hJE : J ∈ E (↑Sphi : Set (ℤ × ℤ)))
    (hℓJ : 0 < det ℓ J)
    (hg₁ : ∀ i, Nivat.PolyChain.faceStart (Ahat i) ℓ
        + (Nivat.PolyChain.faceLen (Ahat i) ℓ : ℤ) • dir ℓ = g₁)
    (hArcbdd : ∀ μ ∈ Nivat.PolyChainSum.Arc (Sphi.finite_toSet) ℓ J,
      ∃ L : ℕ, ∀ i, Nivat.PolyChain.faceLen (Ahat i) μ ≤ L) :
    ∃ g_J : ℤ × ℤ, ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∃ i₀ : ℕ, ∀ i ≥ i₀, Nivat.PolyChain.faceStart (Ahat (σ i)) J = g_J := by
  classical
  set T : Finset (ℤ × ℤ) := Nivat.PolyChainSum.Arc (Sphi.finite_toSet) ℓ J with hT_def
  obtain ⟨σ, hσmono, i₀, hr⟩ := exists_eventually_const_before (Ahat := Ahat) T hfin hArcbdd
  refine ⟨Nivat.PolyChain.faceStart (Ahat (σ i₀)) J, σ, hσmono, i₀, fun i hi => ?_⟩
  have hpin : ∀ k, Nivat.PolyChain.faceStart (Ahat k) J - g₁
      = ∑ ν ∈ Nivat.PolyChainSum.Arc (Sphi.finite_toSet) ℓ J,
        (Nivat.PolyChain.faceLen (Ahat k) ν : ℤ) • dir ν := by
    intro k
    have hEν₀ : ℓ ∈ E (Ahat k) := by
      rw [Nivat.AhatEnv.E_eq_of_enveloped hSfin hSarea (henv k)]; exact hℓE
    have hEn : J ∈ E (Ahat k) := by
      rw [Nivat.AhatEnv.E_eq_of_enveloped hSfin hSarea (henv k)]; exact hJE
    have hchain := Nivat.PolyChainSum.chain_ccw_final (hfin k) (hlc k) hEν₀ hEn hℓJ
    have hArc : (finite_E_of_finite (hfin k)).toFinset.filter
          (fun ν => 0 < det ℓ ν ∧ 0 < det ν J)
        = Nivat.PolyChainSum.Arc (Sphi.finite_toSet) ℓ J :=
      Arc_eq_of_enveloped (hfin k) hSfin hSarea (henv k) ℓ J
    rw [hArc] at hchain
    have hsub : g₁ = Nivat.PolyChain.faceStart (Ahat k) ℓ
        + (Nivat.PolyChain.faceLen (Ahat k) ℓ : ℤ) • dir ℓ := (hg₁ k).symm
    have hrearr : Nivat.PolyChain.faceStart (Ahat k) J
        - (Nivat.PolyChain.faceStart (Ahat k) ℓ
          + (Nivat.PolyChain.faceLen (Ahat k) ℓ : ℤ) • dir ℓ)
        = (Nivat.PolyChain.faceStart (Ahat k) J - Nivat.PolyChain.faceStart (Ahat k) ℓ)
          - (Nivat.PolyChain.faceLen (Ahat k) ℓ : ℤ) • dir ℓ := by abel
    rw [hsub, hrearr, hchain]
    abel
  have hsum_eq : ∑ ν ∈ Nivat.PolyChainSum.Arc (Sphi.finite_toSet) ℓ J,
        (Nivat.PolyChain.faceLen (Ahat (σ i)) ν : ℤ) • dir ν
      = ∑ ν ∈ Nivat.PolyChainSum.Arc (Sphi.finite_toSet) ℓ J,
        (Nivat.PolyChain.faceLen (Ahat (σ i₀)) ν : ℤ) • dir ν := by
    apply Finset.sum_congr rfl
    intro ν hν
    rw [hr ν hν i hi]
  have heq : Nivat.PolyChain.faceStart (Ahat (σ i)) J - g₁
      = Nivat.PolyChain.faceStart (Ahat (σ i₀)) J - g₁ :=
    (hpin (σ i)).trans (hsum_eq.trans (hpin (σ i₀)).symm)
  exact sub_left_inj.mp heq

/-- **The `σ`-reindexed, `i₀`-shifted tower.**  `exists_gJ_pinned_ccw`/`_cw` only pin
`faceStart (Ahat (σ i)) J` for `i ≥ i₀`; every downstream consumer that wants an
unconditional `∀ i` statement (e.g. `ConeHhpFeed.hhp_of_pinned_ccw`) reindexes once via
`fun i => Ahat (σ (i + i₀))`.  Named here so producers of `hlcT`/`hswept` share one
definitional unfolding instead of each re-deriving the shift. -/
def reindexedTower (Ahat : ℕ → Set (ℤ × ℤ)) (σ : ℕ → ℕ) (i₀ : ℕ) : ℕ → Set (ℤ × ℤ) :=
  fun i => Ahat (σ (i + i₀))

@[simp] theorem reindexedTower_apply (Ahat : ℕ → Set (ℤ × ℤ)) (σ : ℕ → ℕ) (i₀ i : ℕ) :
    reindexedTower Ahat σ i₀ i = Ahat (σ (i + i₀)) := rfl

/-- **`g_J` is pinned along a stabilising subsequence, `cw` case** (paper `:498-506`, `cw`
orientation: `g₁` is the *pinned start* of `ℓ`'s face, `g₁ = faceStart (Ahat i) ℓ`, per
team-lead's 2026-09-22 ruling — `chain_cw_final` walks from `ℓ` backwards through the `cw`
arc without ever touching `ℓ`'s own `faceLen`, so again no boundedness hypothesis on `ℓ`'s
face is needed). Mirrors `exists_gJ_pinned_ccw` using `chain_cw_final` and
`exists_J_stable_cw`'s reversed-order `Arc J ℓ`. -/
theorem exists_gJ_pinned_cw
    {Ahat : ℕ → Set (ℤ × ℤ)} {ℓ J g₁ : ℤ × ℤ}
    (hfin : ∀ i, (Ahat i).Finite) (hlc : ∀ i, IsLatticeConvexRegion (Ahat i))
    (henv : ∀ i, Enveloped (↑Sphi : Set (ℤ × ℤ)) (Ahat i))
    (hSfin : (E (↑Sphi : Set (ℤ × ℤ))).Finite) (hSarea : PosArea (↑Sphi : Set (ℤ × ℤ)))
    (hℓE : ℓ ∈ E (↑Sphi : Set (ℤ × ℤ))) (hJE : J ∈ E (↑Sphi : Set (ℤ × ℤ)))
    (hJℓ : 0 < det J ℓ)
    (hg₁ : ∀ i, Nivat.PolyChain.faceStart (Ahat i) ℓ = g₁)
    (hArcbdd : ∀ μ ∈ Nivat.PolyChainSum.Arc (Sphi.finite_toSet) J ℓ,
      ∃ L : ℕ, ∀ i, Nivat.PolyChain.faceLen (Ahat i) μ ≤ L) :
    ∃ g_J : ℤ × ℤ, ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∃ i₀ : ℕ, ∀ i ≥ i₀, Nivat.PolyChain.faceStart (Ahat (σ i)) J
        + (Nivat.PolyChain.faceLen (Ahat (σ i)) J : ℤ) • dir J = g_J := by
  classical
  set T : Finset (ℤ × ℤ) := Nivat.PolyChainSum.Arc (Sphi.finite_toSet) J ℓ with hT_def
  obtain ⟨σ, hσmono, i₀, hr⟩ := exists_eventually_const_before (Ahat := Ahat) T hfin hArcbdd
  refine ⟨Nivat.PolyChain.faceStart (Ahat (σ i₀)) J
      + (Nivat.PolyChain.faceLen (Ahat (σ i₀)) J : ℤ) • dir J, σ, hσmono, i₀, fun i hi => ?_⟩
  have hpin : ∀ k, g₁ - (Nivat.PolyChain.faceStart (Ahat k) J
        + (Nivat.PolyChain.faceLen (Ahat k) J : ℤ) • dir J)
      = ∑ ν ∈ Nivat.PolyChainSum.Arc (Sphi.finite_toSet) J ℓ,
        (Nivat.PolyChain.faceLen (Ahat k) ν : ℤ) • dir ν := by
    intro k
    have hEν₀ : ℓ ∈ E (Ahat k) := by
      rw [Nivat.AhatEnv.E_eq_of_enveloped hSfin hSarea (henv k)]; exact hℓE
    have hEn : J ∈ E (Ahat k) := by
      rw [Nivat.AhatEnv.E_eq_of_enveloped hSfin hSarea (henv k)]; exact hJE
    have hchain := Nivat.PolyChainSum.chain_cw_final (hfin k) (hlc k) hEν₀ hEn hJℓ
    have hArc : (finite_E_of_finite (hfin k)).toFinset.filter
          (fun ν => 0 < det ν ℓ ∧ 0 < det J ν)
        = Nivat.PolyChainSum.Arc (Sphi.finite_toSet) J ℓ := by
      have hE : E (Ahat k) = E (↑Sphi : Set (ℤ × ℤ)) :=
        Nivat.AhatEnv.E_eq_of_enveloped hSfin hSarea (henv k)
      apply Finset.ext
      intro ν
      rw [Finset.mem_filter, (finite_E_of_finite (hfin k)).mem_toFinset, hE,
        Nivat.PolyChainSum.mem_Arc]
      tauto
    rw [hArc, hg₁ k] at hchain
    exact hchain
  have hsum_eq : ∑ ν ∈ Nivat.PolyChainSum.Arc (Sphi.finite_toSet) J ℓ,
        (Nivat.PolyChain.faceLen (Ahat (σ i)) ν : ℤ) • dir ν
      = ∑ ν ∈ Nivat.PolyChainSum.Arc (Sphi.finite_toSet) J ℓ,
        (Nivat.PolyChain.faceLen (Ahat (σ i₀)) ν : ℤ) • dir ν := by
    apply Finset.sum_congr rfl
    intro ν hν
    rw [hr ν hν i hi]
  have heq : g₁ - (Nivat.PolyChain.faceStart (Ahat (σ i)) J
        + (Nivat.PolyChain.faceLen (Ahat (σ i)) J : ℤ) • dir J)
      = g₁ - (Nivat.PolyChain.faceStart (Ahat (σ i₀)) J
        + (Nivat.PolyChain.faceLen (Ahat (σ i₀)) J : ℤ) • dir J) :=
    (hpin (σ i)).trans (hsum_eq.trans (hpin (σ i₀)).symm)
  exact sub_right_inj.mp heq

/-- If `T ⊆ T'` (both finite) and `n`'s support value agrees on both, `T`'s face on `n` is
literally a subset of `T'`'s, hence `faceLen T n ≤ faceLen T' n` (`ℕ`-valued, via
`ENat.toNat_le_toNat`). Team-lead's 2026-09-22 `hgrow` recipe step 1 building block: no paper
line, pure order theory used to compare `faceLen` across the `Ahat`-tower. -/
theorem faceLen_mono_of_suppVal_eq
    {T T' : Set (ℤ × ℤ)} (hfin : T.Finite) (hfin' : T'.Finite)
    (hne : T.Nonempty) (hne' : T'.Nonempty) {ν : ℤ × ℤ}
    (hsupp_eq : suppVal T ν = suppVal T' ν) (hsub : T ⊆ T') :
    Nivat.PolyChain.faceLen T ν ≤ Nivat.PolyChain.faceLen T' ν := by
  have hfaceSub : face T ν ⊆ face T' ν := by
    intro z hz
    have hzT' : z ∈ T' := hsub hz.1
    have hzval : suppVal T ν = dot ν z := suppVal_eq hz
    refine ⟨hzT', fun y hy => ?_⟩
    calc dot ν y ≤ suppVal T' ν := le_suppVal hfin' hne' hy
      _ = suppVal T ν := hsupp_eq.symm
      _ = dot ν z := hzval
  have hcard : (face T ν).encard ≤ (face T' ν).encard := Set.encard_mono hfaceSub
  have hlt' : (face T' ν).encard ≠ ⊤ :=
    ((hfin'.subset (face_subset T' ν)).encard_lt_top).ne
  have htn : (face T ν).encard.toNat ≤ (face T' ν).encard.toNat :=
    ENat.toNat_le_toNat hcard hlt'
  unfold Nivat.PolyChain.faceLen
  omega

/-- **`hgrow`, ccw case** (team-lead's 2026-09-22 recipe). Consumes the `Ahat`-tower's global
monotonicity (`AhatMono`, unconditional on the index — the `Ahat` sequence entering this file
is already the post-reindexing monotone one, per `blueprint/LEAF-A.md`) together with
`exists_J_stable`'s unboundedness witness and `exists_gJ_pinned_ccw`'s pinning, to produce the
exact shape `ray_of_pinned_growth` (`ItemII.lean:786`) consumes:
`∀ N, ∃ i, ∀ t ≤ N, g_J + t • dir J ∈ Ahat (σ i)`. -/
theorem hgrow_of_pinned_ccw
    {Ahat : ℕ → Set (ℤ × ℤ)} {J g_J : ℤ × ℤ}
    (AhatMono : ∀ i j, i ≤ j → Ahat i ⊆ Ahat j)
    (hfin : ∀ i, (Ahat i).Finite) (hne : ∀ i, (Ahat i).Nonempty)
    (hlc : ∀ i, IsLatticeConvexRegion (Ahat i))
    (hJEall : ∀ i, J ∈ E (Ahat i))
    (hJunb : ¬ ∃ L : ℕ, ∀ i, Nivat.PolyChain.faceLen (Ahat i) J ≤ L)
    {σ : ℕ → ℕ} (hσmono : StrictMono σ) {i₀ : ℕ}
    (hg : ∀ i ≥ i₀, Nivat.PolyChain.faceStart (Ahat (σ i)) J = g_J) :
    ∀ N : ℕ, ∃ i : ℕ, ∀ t : ℕ, t ≤ N → g_J + (t : ℤ) • dir J ∈ Ahat (σ i) := by
  classical
  -- Step 1: `suppVal (Ahat j) J = dot J g_J` for every original index `j ≥ σ i₀` (sandwich).
  have hsuppPin : ∀ j, σ i₀ ≤ j → suppVal (Ahat j) J = dot J g_J := by
    intro j hj
    have hsuppσi0 : suppVal (Ahat (σ i₀)) J = dot J g_J := by
      rw [suppVal_eq (hg i₀ le_rfl ▸ Nivat.PolyChain.faceStart_mem (hfin (σ i₀)) (hJEall (σ i₀)))]
    obtain ⟨i, hi1, hi2⟩ : ∃ i, i₀ ≤ i ∧ j ≤ σ i :=
      ⟨max i₀ j, le_max_left _ _, le_trans (le_max_right _ _) hσmono.le_apply⟩
    have hsuppσi : suppVal (Ahat (σ i)) J = dot J g_J := by
      rw [suppVal_eq (hg i hi1 ▸ Nivat.PolyChain.faceStart_mem (hfin (σ i)) (hJEall (σ i)))]
    have hle1 : suppVal (Ahat j) J ≤ dot J g_J :=
      hsuppσi ▸ suppVal_mono (hfin j) (hne j) (hfin (σ i)) (hne (σ i)) (AhatMono j (σ i) hi2) J
    have hle2 : dot J g_J ≤ suppVal (Ahat j) J :=
      hsuppσi0 ▸ suppVal_mono (hfin (σ i₀)) (hne (σ i₀)) (hfin j) (hne j) (AhatMono (σ i₀) j hj) J
    exact le_antisymm hle1 hle2
  intro N
  -- Step 2: `faceLen (Ahat (σ ·)) J` is unbounded on `i ≥ i₀`.
  have hunbσ : ¬ ∃ L : ℕ, ∀ i ≥ i₀, Nivat.PolyChain.faceLen (Ahat (σ i)) J ≤ L := by
    rintro ⟨L, hL⟩
    apply hJunb
    set M : ℕ := (Finset.range (σ i₀)).sup (fun k => Nivat.PolyChain.faceLen (Ahat k) J) with hM_def
    refine ⟨max L M, fun k => ?_⟩
    rcases lt_or_ge k (σ i₀) with hk | hk
    · exact le_trans (Finset.le_sup (f := fun k => Nivat.PolyChain.faceLen (Ahat k) J)
        (Finset.mem_range.mpr hk)) (le_max_right _ _)
    · obtain ⟨i, hi1, hi2⟩ : ∃ i, i₀ ≤ i ∧ k ≤ σ i :=
        ⟨max i₀ k, le_max_left _ _, le_trans (le_max_right _ _) hσmono.le_apply⟩
      have hmono : Nivat.PolyChain.faceLen (Ahat k) J ≤ Nivat.PolyChain.faceLen (Ahat (σ i)) J :=
        faceLen_mono_of_suppVal_eq (hfin k) (hfin (σ i)) (hne k) (hne (σ i))
          ((hsuppPin k hk).trans (hsuppPin (σ i)
            (le_trans hk hi2)).symm) (AhatMono k (σ i) hi2)
      exact le_trans (le_trans hmono (hL i hi1)) (le_max_left _ _)
  -- Step 3: extract a witness index `i ≥ i₀` with `faceLen (Ahat (σ i)) J > N`.
  rw [not_exists] at hunbσ
  have hex : ∃ i ≥ i₀, N < Nivat.PolyChain.faceLen (Ahat (σ i)) J := by
    by_contra hcon
    push_neg at hcon
    exact hunbσ N hcon
  obtain ⟨i, hi1, hi2⟩ := hex
  refine ⟨i, fun t ht => ?_⟩
  have hseg := Nivat.PolyChain.face_eq_segment (hlc (σ i)) (hfin (σ i)) (hJEall (σ i))
  have hmemface : Nivat.PolyChain.faceStart (Ahat (σ i)) J + (t : ℤ) • dir J ∈ face (Ahat (σ i)) J := by
    rw [hseg]
    exact ⟨t, le_trans ht hi2.le, rfl⟩
  rw [hg i hi1] at hmemface
  exact face_subset (Ahat (σ i)) J hmemface

/-- **`hgrow`, cw case** — mirror of `hgrow_of_pinned_ccw`. Here `g_J` pins the *end* of
`J`'s face (`exists_gJ_pinned_cw`'s conclusion shape), so the face is swept walking
*backwards* from `g_J` along `-dir J`; `faceLen_mono_of_suppVal_eq` is orientation-agnostic
and reused verbatim, only `faceEnd_mem` replaces `faceStart_mem` in the sandwich, and the
final segment-membership step subtracts instead of adds. -/
theorem hgrow_of_pinned_cw
    {Ahat : ℕ → Set (ℤ × ℤ)} {J g_J : ℤ × ℤ}
    (AhatMono : ∀ i j, i ≤ j → Ahat i ⊆ Ahat j)
    (hfin : ∀ i, (Ahat i).Finite) (hne : ∀ i, (Ahat i).Nonempty)
    (hlc : ∀ i, IsLatticeConvexRegion (Ahat i))
    (hJEall : ∀ i, J ∈ E (Ahat i))
    (hJunb : ¬ ∃ L : ℕ, ∀ i, Nivat.PolyChain.faceLen (Ahat i) J ≤ L)
    {σ : ℕ → ℕ} (hσmono : StrictMono σ) {i₀ : ℕ}
    (hg : ∀ i ≥ i₀, Nivat.PolyChain.faceStart (Ahat (σ i)) J
      + (Nivat.PolyChain.faceLen (Ahat (σ i)) J : ℤ) • dir J = g_J) :
    ∀ N : ℕ, ∃ i : ℕ, ∀ t : ℕ, t ≤ N → g_J - (t : ℤ) • dir J ∈ Ahat (σ i) := by
  classical
  have hsuppPin : ∀ j, σ i₀ ≤ j → suppVal (Ahat j) J = dot J g_J := by
    intro j hj
    have hsuppσi0 : suppVal (Ahat (σ i₀)) J = dot J g_J := by
      rw [suppVal_eq (hg i₀ le_rfl ▸ Nivat.PolyChain.faceEnd_mem (hlc (σ i₀)) (hfin (σ i₀)) (hJEall (σ i₀)))]
    obtain ⟨i, hi1, hi2⟩ : ∃ i, i₀ ≤ i ∧ j ≤ σ i :=
      ⟨max i₀ j, le_max_left _ _, le_trans (le_max_right _ _) hσmono.le_apply⟩
    have hsuppσi : suppVal (Ahat (σ i)) J = dot J g_J := by
      rw [suppVal_eq (hg i hi1 ▸ Nivat.PolyChain.faceEnd_mem (hlc (σ i)) (hfin (σ i)) (hJEall (σ i)))]
    have hle1 : suppVal (Ahat j) J ≤ dot J g_J :=
      hsuppσi ▸ suppVal_mono (hfin j) (hne j) (hfin (σ i)) (hne (σ i)) (AhatMono j (σ i) hi2) J
    have hle2 : dot J g_J ≤ suppVal (Ahat j) J :=
      hsuppσi0 ▸ suppVal_mono (hfin (σ i₀)) (hne (σ i₀)) (hfin j) (hne j) (AhatMono (σ i₀) j hj) J
    exact le_antisymm hle1 hle2
  intro N
  have hunbσ : ¬ ∃ L : ℕ, ∀ i ≥ i₀, Nivat.PolyChain.faceLen (Ahat (σ i)) J ≤ L := by
    rintro ⟨L, hL⟩
    apply hJunb
    set M : ℕ := (Finset.range (σ i₀)).sup (fun k => Nivat.PolyChain.faceLen (Ahat k) J) with hM_def
    refine ⟨max L M, fun k => ?_⟩
    rcases lt_or_ge k (σ i₀) with hk | hk
    · exact le_trans (Finset.le_sup (f := fun k => Nivat.PolyChain.faceLen (Ahat k) J)
        (Finset.mem_range.mpr hk)) (le_max_right _ _)
    · obtain ⟨i, hi1, hi2⟩ : ∃ i, i₀ ≤ i ∧ k ≤ σ i :=
        ⟨max i₀ k, le_max_left _ _, le_trans (le_max_right _ _) hσmono.le_apply⟩
      have hmono : Nivat.PolyChain.faceLen (Ahat k) J ≤ Nivat.PolyChain.faceLen (Ahat (σ i)) J :=
        faceLen_mono_of_suppVal_eq (hfin k) (hfin (σ i)) (hne k) (hne (σ i))
          ((hsuppPin k hk).trans (hsuppPin (σ i)
            (le_trans hk hi2)).symm) (AhatMono k (σ i) hi2)
      exact le_trans (le_trans hmono (hL i hi1)) (le_max_left _ _)
  rw [not_exists] at hunbσ
  have hex : ∃ i ≥ i₀, N < Nivat.PolyChain.faceLen (Ahat (σ i)) J := by
    by_contra hcon
    push_neg at hcon
    exact hunbσ N hcon
  obtain ⟨i, hi1, hi2⟩ := hex
  refine ⟨i, fun t ht => ?_⟩
  have hseg := Nivat.PolyChain.face_eq_segment (hlc (σ i)) (hfin (σ i)) (hJEall (σ i))
  have htle : t ≤ Nivat.PolyChain.faceLen (Ahat (σ i)) J := le_trans ht hi2.le
  have hmemface : Nivat.PolyChain.faceStart (Ahat (σ i)) J
      + ((Nivat.PolyChain.faceLen (Ahat (σ i)) J - t : ℕ) : ℤ) • dir J ∈ face (Ahat (σ i)) J := by
    rw [hseg]
    exact ⟨Nivat.PolyChain.faceLen (Ahat (σ i)) J - t, Nat.sub_le _ _, rfl⟩
  have hcast : ((Nivat.PolyChain.faceLen (Ahat (σ i)) J - t : ℕ) : ℤ)
      = (Nivat.PolyChain.faceLen (Ahat (σ i)) J : ℤ) - (t : ℤ) := Nat.cast_sub htle
  rw [hcast] at hmemface
  have hrearr : Nivat.PolyChain.faceStart (Ahat (σ i)) J
      + ((Nivat.PolyChain.faceLen (Ahat (σ i)) J : ℤ) - (t : ℤ)) • dir J
      = g_J - (t : ℤ) • dir J := by
    rw [sub_smul, ← hg i hi1]; abel
  rw [hrearr] at hmemface
  exact face_subset (Ahat (σ i)) J hmemface

/-! ### §4. `nprevJ`, `vJ1`, `hsupp_prev`, `hgJ_level` (team-lead, 2026-09-22)

Paper: `scratch/b3_colle2.txt:440` (`v_{ℓ_{J-1}}`). Consumer: lane-chain's
`tmp/wip/LeafABottom.lean` (`hsupp_prev`/`hnpvJ1`/`hgJ_level` binder names, chosen there to
match this section) and `bottom_of_seed` (`ANormal.lean:776`). `ℓ` below is instantiated by
the caller as `-nℓ` (`blueprint/LEAF-HSUPP.md` §2(E)'s `ν₀ := −nℓ`); stated generically since
nothing here depends on that choice. -/

/-- **Right-anchor mirror of `Arc_subset_of_mem_Arc`**: if `b` lies strictly between `a` and
the *fixed* `J` (`b ∈ Arc a J`), then everything strictly between `b` and `J` is also strictly
between `a` and `J`. Same shape as `Arc_subset_of_mem_Arc` but the fixed endpoint moves from
the first to the second slot, so the witness for `det_pos_trans` moves from `e := dir ℓ` to
`e := -dir J` (`dot_neg_dir n x : dot (-dir n) x = det x n`) and the three points it certifies
are `a`, `b`, `μ` (all strictly before `J`) rather than `ν`, `μ`, `J` (all strictly after `ℓ`). -/
theorem Arc_subset_of_mem_Arc_right {T : Set (ℤ × ℤ)} (hfin : T.Finite) {a b J : ℤ × ℤ}
    (haJ : 0 < det a J) (hb : b ∈ Nivat.PolyChainSum.Arc hfin a J) :
    Nivat.PolyChainSum.Arc hfin b J ⊆ Nivat.PolyChainSum.Arc hfin a J := by
  intro μ hμ
  obtain ⟨hμE, hbμ, hμJ⟩ := Nivat.PolyChainSum.mem_Arc.mp hμ
  obtain ⟨_, haB, hbJ⟩ := Nivat.PolyChainSum.mem_Arc.mp hb
  refine Nivat.PolyChainSum.mem_Arc.mpr ⟨hμE, ?_, hμJ⟩
  exact Nivat.PolyChain.det_pos_trans (e := -dir J)
    (by rw [Nivat.PolyChainSum.dot_neg_dir]; exact haJ)
    (by rw [Nivat.PolyChainSum.dot_neg_dir]; exact hbJ)
    (by rw [Nivat.PolyChainSum.dot_neg_dir]; exact hμJ) haB hbμ

/-- Right-anchor mirror of `ord_lt_of_mem_Arc`: the `Arc · J`-cardinality strictly decreases
moving from `a` to any `b` strictly between `a` and `J`. -/
theorem ord_lt_of_mem_Arc_right {T : Set (ℤ × ℤ)} (hfin : T.Finite) {a b J : ℤ × ℤ}
    (haJ : 0 < det a J) (hb : b ∈ Nivat.PolyChainSum.Arc hfin a J) :
    (Nivat.PolyChainSum.Arc hfin b J).card < (Nivat.PolyChainSum.Arc hfin a J).card := by
  have hsub := Arc_subset_of_mem_Arc_right hfin haJ hb
  have hnotmem : b ∉ Nivat.PolyChainSum.Arc hfin b J := by
    intro hmem
    have hself := (Nivat.PolyChainSum.mem_Arc.mp hmem).2.1
    rw [Nivat.LE2.det_self] at hself
    exact absurd hself (lt_irrefl 0)
  exact Finset.card_lt_card ⟨hsub, fun hcon => hnotmem (hcon hb)⟩

/-- **`nprevJ` exists**: the fan-adjacent predecessor of `J` inside `Arc ℓ J` (minimising
`ord2 ν := (Arc ν J).card` over that finite set, exactly as `exists_J_stable` minimises `ord`
over its unboundedness filter), or `ℓ` itself when `Arc ℓ J = ∅` (team-lead's stated
degenerate case). Minimality forces `Arc nprevJ J = ∅` (fan-adjacency): any `μ` strictly
between `nprevJ` and `J` would, by `Arc_subset_of_mem_Arc_right`, also lie in `Arc ℓ J`, and by
`ord_lt_of_mem_Arc_right` have strictly smaller `ord2` than `nprevJ` — contradicting
`nprevJ`'s minimality. -/
theorem exists_fan_pred {ℓ J : ℤ × ℤ}
    (hℓE : ℓ ∈ E (↑Sphi : Set (ℤ × ℤ))) (hJE : J ∈ E (↑Sphi : Set (ℤ × ℤ)))
    (hℓJ : 0 < det ℓ J) :
    ∃ nprevJ, nprevJ ∈ E (↑Sphi : Set (ℤ × ℤ)) ∧ 0 < det nprevJ J ∧
      Nivat.PolyChainSum.Arc (Sphi.finite_toSet) nprevJ J = ∅ ∧
      (nprevJ = ℓ ∨ nprevJ ∈ Nivat.PolyChainSum.Arc (Sphi.finite_toSet) ℓ J) := by
  classical
  rcases (Nivat.PolyChainSum.Arc (Sphi.finite_toSet) ℓ J).eq_empty_or_nonempty with hTe | hTne
  · exact ⟨ℓ, hℓE, hℓJ, hTe, Or.inl rfl⟩
  · set ord2 : ℤ × ℤ → ℕ := fun ν => (Nivat.PolyChainSum.Arc (Sphi.finite_toSet) ν J).card
      with hord2_def
    obtain ⟨nprevJ, hnprevT, hmin⟩ :=
      Finset.exists_min_image (Nivat.PolyChainSum.Arc (Sphi.finite_toSet) ℓ J) ord2 hTne
    obtain ⟨hnprevE, _, hnprevJ⟩ := Nivat.PolyChainSum.mem_Arc.mp hnprevT
    refine ⟨nprevJ, hnprevE, hnprevJ, ?_, Or.inr hnprevT⟩
    by_contra hne
    obtain ⟨μ, hμmem⟩ :=
      Finset.nonempty_iff_ne_empty.mpr hne
    have hsub := Arc_subset_of_mem_Arc_right (Sphi.finite_toSet) hℓJ hnprevT
    have hμT : μ ∈ Nivat.PolyChainSum.Arc (Sphi.finite_toSet) ℓ J := hsub hμmem
    have hlt := ord_lt_of_mem_Arc_right (Sphi.finite_toSet) hnprevJ hμmem
    have hle := hmin μ hμT
    simp only [hord2_def] at hle
    omega

/-- **`nprevJ`, `vJ1 := dir nprevJ` and its defining identities.** No sign flip is needed:
`dot nprevJ vJ1 = 0` is `dot_dir_left`/`det_self` after `dot_comm`, and `dot (-J) vJ1 < 0` is
immediate from `0 < det nprevJ J` (`exists_fan_pred`'s output) since
`dot (-J) (dir nprevJ) = -dot J (dir nprevJ) = -dot (dir nprevJ) J = -det nprevJ J`. This
`vJ1` is the paper's `v_{ℓ_{J-1}}` (`:440`). -/
theorem exists_nprevJ_vJ1 {ℓ J : ℤ × ℤ}
    (hℓE : ℓ ∈ E (↑Sphi : Set (ℤ × ℤ))) (hJE : J ∈ E (↑Sphi : Set (ℤ × ℤ)))
    (hℓJ : 0 < det ℓ J) :
    ∃ nprevJ vJ1, nprevJ ∈ E (↑Sphi : Set (ℤ × ℤ)) ∧ 0 < det nprevJ J ∧
      Nivat.PolyChainSum.Arc (Sphi.finite_toSet) nprevJ J = ∅ ∧
      (nprevJ = ℓ ∨ nprevJ ∈ Nivat.PolyChainSum.Arc (Sphi.finite_toSet) ℓ J) ∧
      vJ1 = dir nprevJ ∧ dot nprevJ vJ1 = 0 ∧ dot (-J) vJ1 < 0 := by
  obtain ⟨nprevJ, hE, hdet, hempty, hor⟩ := exists_fan_pred hℓE hJE hℓJ
  refine ⟨nprevJ, dir nprevJ, hE, hdet, hempty, hor, rfl, ?_, ?_⟩
  · have := (Nivat.PolyChainSum.dot_dir_left nprevJ nprevJ)
    rw [dot_comm nprevJ (dir nprevJ), this, det_self]
  · have hc : dot J (dir nprevJ) = det nprevJ J :=
      (dot_comm J (dir nprevJ)).trans (Nivat.PolyChainSum.dot_dir_left nprevJ J)
    have heq : dot (-J) (dir nprevJ) = -det nprevJ J := by rw [dot_neg_left, hc]
    rw [heq]; omega

/-- **`hsupp_prev`**: every point of `Ahat (σ i)` (for *every* `i`, not just `i ≥ i₀`) sits
on the `nprevJ`-negative side of `g_J`. Mechanism: for `i ≥ i₀`, `adjacent_shared_vertex`
(fed the emptiness of `Arc nprevJ J` from `exists_fan_pred`, transported from `E ↑Sphi` to
`E (Ahat (σ i))` via `AhatEnv.E_eq_of_enveloped`) pins the *end* of `nprevJ`'s face to
`faceStart (Ahat (σ i)) J`, which `hg` (the `exists_gJ_pinned_ccw` output) identifies with
`g_J`; `suppVal_eq` then reads off `suppVal (Ahat (σ i)) nprevJ = dot nprevJ g_J`, and
`le_suppVal` closes the bound. For general `i`, take `j := max i i₀ ≥ i₀`, push `z` up to
`Ahat (σ j)` via `AhatMono` (`σ` monotone), and apply the `i ≥ i₀` case at `j`. Degenerate case
(`nprevJ = ℓ`, `Arc ℓ J = ∅`): unchanged, `adjacent_shared_vertex` is applied directly at
`(ℓ, J)`, matching team-lead's "`nprevJ = −nℓ`, `g_J = g₁`" instance when `ℓ := -nℓ`. -/
theorem hsupp_prev
    {Ahat : ℕ → Set (ℤ × ℤ)} {J nprevJ g_J : ℤ × ℤ}
    (hfin : ∀ i, (Ahat i).Finite) (hne : ∀ i, (Ahat i).Nonempty)
    (hlc : ∀ i, IsLatticeConvexRegion (Ahat i))
    (henv : ∀ i, Enveloped (↑Sphi : Set (ℤ × ℤ)) (Ahat i))
    (hSfin : (E (↑Sphi : Set (ℤ × ℤ))).Finite) (hSarea : PosArea (↑Sphi : Set (ℤ × ℤ)))
    (AhatMono : ∀ i j, i ≤ j → Ahat i ⊆ Ahat j)
    (hnprevE : nprevJ ∈ E (↑Sphi : Set (ℤ × ℤ))) (hJE : J ∈ E (↑Sphi : Set (ℤ × ℤ)))
    (hdet : 0 < det nprevJ J)
    (hempty : Nivat.PolyChainSum.Arc (Sphi.finite_toSet) nprevJ J = ∅)
    {σ : ℕ → ℕ} (hσmono : StrictMono σ) {i₀ : ℕ}
    (hg : ∀ i ≥ i₀, Nivat.PolyChain.faceStart (Ahat (σ i)) J = g_J) :
    ∀ i, ∀ z ∈ Ahat (σ i), dot nprevJ z ≤ dot nprevJ g_J := by
  have hcase : ∀ i ≥ i₀, suppVal (Ahat (σ i)) nprevJ = dot nprevJ g_J := by
    intro i hi
    have hEnp : nprevJ ∈ E (Ahat (σ i)) := by
      rw [Nivat.AhatEnv.E_eq_of_enveloped hSfin hSarea (henv (σ i))]; exact hnprevE
    have hEJ : J ∈ E (Ahat (σ i)) := by
      rw [Nivat.AhatEnv.E_eq_of_enveloped hSfin hSarea (henv (σ i))]; exact hJE
    have hadj : ∀ μ ∈ E (Ahat (σ i)), ¬ (0 < det nprevJ μ ∧ 0 < det μ J) := by
      intro μ hμ hcon
      have hμE : μ ∈ E (↑Sphi : Set (ℤ × ℤ)) := by
        rw [← Nivat.AhatEnv.E_eq_of_enveloped hSfin hSarea (henv (σ i))]; exact hμ
      have hμmem : μ ∈ Nivat.PolyChainSum.Arc (Sphi.finite_toSet) nprevJ J :=
        Nivat.PolyChainSum.mem_Arc.mpr ⟨hμE, hcon.1, hcon.2⟩
      rw [hempty] at hμmem
      exact absurd hμmem (by simp)
    have hshared := Nivat.PolyChain.adjacent_shared_vertex (hfin (σ i)) (hlc (σ i))
      hEnp hEJ hdet hadj
    rw [hg i hi] at hshared
    have hmem : g_J ∈ face (Ahat (σ i)) nprevJ := hshared ▸
      Nivat.PolyChain.faceEnd_mem (hlc (σ i)) (hfin (σ i)) hEnp
    exact suppVal_eq hmem
  intro i z hz
  set j : ℕ := max i i₀ with hj_def
  have hij : i ≤ j := le_max_left _ _
  have hi0j : i₀ ≤ j := le_max_right _ _
  have hzj : z ∈ Ahat (σ j) := AhatMono (σ i) (σ j) (hσmono.monotone hij) hz
  have hsupp := hcase j hi0j
  calc dot nprevJ z ≤ suppVal (Ahat (σ j)) nprevJ := le_suppVal (hfin (σ j)) (hne (σ j)) hzj
    _ = dot nprevJ g_J := hsupp

/-- **`hgJ_level`**: purely definitional once `cJ` is taken to be `dot (-J) g_J`
(`ChainDataGeomParts.cJ`, `ChainPartsFeed.lean:195-199`) — no separate proof obligation here.
**Status update (team-lead, 2026-09-22): `cJ := dot (-J) g_J` is no longer a guessed
assignment awaiting justification — it is PROVEN by `ShellRegionJ.hhp_of_faceStart_pinned`.**
This theorem only records that the (now-justified) assignment is a valid discharge of the
field; it is not itself the proof that the assignment is correct. -/
theorem hgJ_level (J g_J : ℤ × ℤ) : dot (-J) g_J = dot (-J) g_J := rfl

/-- **`hnJvJ`** (lane-chain's naming, `nJ := -J`, `vJ := dir J`): `J`'s own face direction is
perpendicular to `-J`, same computation as `dot nprevJ vJ1 = 0` in `exists_nprevJ_vJ1`. -/
theorem dot_negJ_dirJ_zero (J : ℤ × ℤ) : dot (-J) (dir J) = 0 := by
  have hc : dot J (dir J) = det J J :=
    (dot_comm J (dir J)).trans (Nivat.PolyChainSum.dot_dir_left J J)
  rw [dot_neg_left, hc, det_self]; ring

/-- **`hnpvJ`** (lane-chain's naming): `nprevJ` sits on the `dir J`-negative side, mirror of
`exists_nprevJ_vJ1`'s `dot (-J) vJ1 < 0` with the roles of `nprevJ`/`J` swapped. -/
theorem dot_nprevJ_vJ_neg {nprevJ J : ℤ × ℤ} (hdet : 0 < det nprevJ J) :
    dot nprevJ (dir J) < 0 := by
  have h1 : dot (-dir J) nprevJ = det nprevJ J := Nivat.PolyChainSum.dot_neg_dir J nprevJ
  have h2 : dot (dir J) nprevJ = -det nprevJ J := by
    have h2' : dot (-dir J) nprevJ = -dot (dir J) nprevJ := dot_neg_left (dir J) nprevJ
    linarith [h1, h2']
  rw [dot_comm nprevJ (dir J), h2]
  omega

/-! ### §4b. `cw` mirrors of `exists_nprevJ_vJ1`/`hsupp_prev` (team-lead, 2026-09-22)

`chain_cw_final`'s `g_J` is the pinned *end* of `J`'s face (`exists_gJ_pinned_cw`), not its
start, and its chain sum runs over `Arc J ℓ` (`ℓ` fixed in the second slot). The fan-adjacent
neighbour of `J` on this side is found by the *first-argument-fixed* mirror
(`Arc_subset_of_mem_Arc`/`ord_lt_of_mem_Arc`, already landed, `§2b`) instantiated with the
roles of the two arguments swapped — `ℓ := J`, `J := ℓ` in those lemmas' own variable names —
rather than the `_right` pair from `§4`; no new subset/order lemmas are needed. The resulting
positivity is `0 < det J nprevJ` (not `0 < det nprevJ J`), which flips the sign in `vJ1`:
`vJ1 := -dir nprevJ` (not `dir nprevJ`) is what gives `dot (-J) vJ1 < 0` here. -/

/-- **`nprevJ` exists, `cw` mirror.** The fan-adjacent neighbour of `J` inside `Arc J ℓ`
(minimising `ord2 ν := (Arc J ν).card`), or `ℓ` itself when `Arc J ℓ = ∅`. Minimality forces
`Arc J nprevJ = ∅`. Proof is `exists_fan_pred`'s proof verbatim with the two `Arc` argument
slots swapped throughout (`Arc_subset_of_mem_Arc`/`ord_lt_of_mem_Arc` in place of the `_right`
pair). -/
theorem exists_fan_pred_cw {ℓ J : ℤ × ℤ}
    (hℓE : ℓ ∈ E (↑Sphi : Set (ℤ × ℤ))) (hJE : J ∈ E (↑Sphi : Set (ℤ × ℤ)))
    (hJℓ : 0 < det J ℓ) :
    ∃ nprevJ, nprevJ ∈ E (↑Sphi : Set (ℤ × ℤ)) ∧ 0 < det J nprevJ ∧
      Nivat.PolyChainSum.Arc (Sphi.finite_toSet) J nprevJ = ∅ ∧
      (nprevJ = ℓ ∨ nprevJ ∈ Nivat.PolyChainSum.Arc (Sphi.finite_toSet) J ℓ) := by
  classical
  rcases (Nivat.PolyChainSum.Arc (Sphi.finite_toSet) J ℓ).eq_empty_or_nonempty with hTe | hTne
  · exact ⟨ℓ, hℓE, hJℓ, hTe, Or.inl rfl⟩
  · set ord2 : ℤ × ℤ → ℕ := fun ν => (Nivat.PolyChainSum.Arc (Sphi.finite_toSet) J ν).card
      with hord2_def
    obtain ⟨nprevJ, hnprevT, hmin⟩ :=
      Finset.exists_min_image (Nivat.PolyChainSum.Arc (Sphi.finite_toSet) J ℓ) ord2 hTne
    obtain ⟨hnprevE, hJnprev, _⟩ := Nivat.PolyChainSum.mem_Arc.mp hnprevT
    refine ⟨nprevJ, hnprevE, hJnprev, ?_, Or.inr hnprevT⟩
    by_contra hne
    obtain ⟨μ, hμmem⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    have hsub := Arc_subset_of_mem_Arc (Sphi.finite_toSet) hJℓ hnprevT
    have hμT : μ ∈ Nivat.PolyChainSum.Arc (Sphi.finite_toSet) J ℓ := hsub hμmem
    have hlt := ord_lt_of_mem_Arc (Sphi.finite_toSet) hJnprev hμmem
    have hle := hmin μ hμT
    simp only [hord2_def] at hle
    omega

/-- **`nprevJ`, `vJ1 := -dir nprevJ` and its defining identities, `cw` mirror.** Orthogonality
is sign-independent (`dot nprevJ (dir nprevJ) = 0`, negate both sides). The `dot (-J) vJ1 < 0`
computation: `dot (-J) (-dir nprevJ) = dot J (dir nprevJ) = det nprevJ J = -det J nprevJ < 0`
using `0 < det J nprevJ` from `exists_fan_pred_cw`. -/
theorem exists_nprevJ_vJ1_cw {ℓ J : ℤ × ℤ}
    (hℓE : ℓ ∈ E (↑Sphi : Set (ℤ × ℤ))) (hJE : J ∈ E (↑Sphi : Set (ℤ × ℤ)))
    (hJℓ : 0 < det J ℓ) :
    ∃ nprevJ vJ1, nprevJ ∈ E (↑Sphi : Set (ℤ × ℤ)) ∧ 0 < det J nprevJ ∧
      Nivat.PolyChainSum.Arc (Sphi.finite_toSet) J nprevJ = ∅ ∧
      (nprevJ = ℓ ∨ nprevJ ∈ Nivat.PolyChainSum.Arc (Sphi.finite_toSet) J ℓ) ∧
      vJ1 = -dir nprevJ ∧ dot nprevJ vJ1 = 0 ∧ dot (-J) vJ1 < 0 := by
  obtain ⟨nprevJ, hE, hdet, hempty, hor⟩ := exists_fan_pred_cw hℓE hJE hJℓ
  refine ⟨nprevJ, -dir nprevJ, hE, hdet, hempty, hor, rfl, ?_, ?_⟩
  · have h0 : dot nprevJ (dir nprevJ) = 0 := by
      rw [dot_comm nprevJ (dir nprevJ), Nivat.PolyChainSum.dot_dir_left, det_self]
    have h1 : dot nprevJ (-dir nprevJ) = -dot nprevJ (dir nprevJ) := by
      rw [dot_comm nprevJ (-dir nprevJ), dot_neg_left, dot_comm]
    rw [h1, h0]; ring
  · have hc : dot J (dir nprevJ) = det nprevJ J :=
      (dot_comm J (dir nprevJ)).trans (Nivat.PolyChainSum.dot_dir_left nprevJ J)
    have hskew : det nprevJ J = -det J nprevJ := det_skew nprevJ J
    have heq1 : dot (-J) (dir nprevJ) = -det nprevJ J := by rw [dot_neg_left, hc]
    have heq2 : dot (-J) (-dir nprevJ) = -dot (-J) (dir nprevJ) := by
      rw [dot_comm (-J) (-dir nprevJ), dot_neg_left, dot_comm]
    rw [heq2, heq1, hskew]
    omega

/-- **`hsupp_prev`, `cw` mirror.** Every point of `Ahat (σ i)` (all `i`) sits on the
`nprevJ`-negative side of `g_J`. Mechanism: for `i ≥ i₀`, `adjacent_shared_vertex` at the pair
`(J, nprevJ)` (fed `Arc J nprevJ = ∅` from `exists_fan_pred_cw`) pins `faceStart (Ahat (σ i))
nprevJ` to `faceStart (Ahat (σ i)) J + faceLen (Ahat (σ i)) J • dir J`, which `hg`
(`exists_gJ_pinned_cw`'s pinned-*end* output) identifies with `g_J`; `suppVal_eq` (via
`faceStart_mem`, not `faceEnd_mem` — the pinned point is `nprevJ`'s face *start* here) then
reads off `suppVal (Ahat (σ i)) nprevJ = dot nprevJ g_J`, and `le_suppVal` closes the bound.
General `i` reduces to `i ≥ i₀` via `AhatMono` exactly as in the ccw case. -/
theorem hsupp_prev_cw
    {Ahat : ℕ → Set (ℤ × ℤ)} {J nprevJ g_J : ℤ × ℤ}
    (hfin : ∀ i, (Ahat i).Finite) (hne : ∀ i, (Ahat i).Nonempty)
    (hlc : ∀ i, IsLatticeConvexRegion (Ahat i))
    (henv : ∀ i, Enveloped (↑Sphi : Set (ℤ × ℤ)) (Ahat i))
    (hSfin : (E (↑Sphi : Set (ℤ × ℤ))).Finite) (hSarea : PosArea (↑Sphi : Set (ℤ × ℤ)))
    (AhatMono : ∀ i j, i ≤ j → Ahat i ⊆ Ahat j)
    (hnprevE : nprevJ ∈ E (↑Sphi : Set (ℤ × ℤ))) (hJE : J ∈ E (↑Sphi : Set (ℤ × ℤ)))
    (hdet : 0 < det J nprevJ)
    (hempty : Nivat.PolyChainSum.Arc (Sphi.finite_toSet) J nprevJ = ∅)
    {σ : ℕ → ℕ} (hσmono : StrictMono σ) {i₀ : ℕ}
    (hg : ∀ i ≥ i₀, Nivat.PolyChain.faceStart (Ahat (σ i)) J
        + (Nivat.PolyChain.faceLen (Ahat (σ i)) J : ℤ) • dir J = g_J) :
    ∀ i, ∀ z ∈ Ahat (σ i), dot nprevJ z ≤ dot nprevJ g_J := by
  have hcase : ∀ i ≥ i₀, suppVal (Ahat (σ i)) nprevJ = dot nprevJ g_J := by
    intro i hi
    have hEnp : nprevJ ∈ E (Ahat (σ i)) := by
      rw [Nivat.AhatEnv.E_eq_of_enveloped hSfin hSarea (henv (σ i))]; exact hnprevE
    have hEJ : J ∈ E (Ahat (σ i)) := by
      rw [Nivat.AhatEnv.E_eq_of_enveloped hSfin hSarea (henv (σ i))]; exact hJE
    have hadj : ∀ μ ∈ E (Ahat (σ i)), ¬ (0 < det J μ ∧ 0 < det μ nprevJ) := by
      intro μ hμ hcon
      have hμE : μ ∈ E (↑Sphi : Set (ℤ × ℤ)) := by
        rw [← Nivat.AhatEnv.E_eq_of_enveloped hSfin hSarea (henv (σ i))]; exact hμ
      have hμmem : μ ∈ Nivat.PolyChainSum.Arc (Sphi.finite_toSet) J nprevJ :=
        Nivat.PolyChainSum.mem_Arc.mpr ⟨hμE, hcon.1, hcon.2⟩
      rw [hempty] at hμmem
      exact absurd hμmem (by simp)
    have hshared := Nivat.PolyChain.adjacent_shared_vertex (hfin (σ i)) (hlc (σ i))
      hEJ hEnp hdet hadj
    rw [hg i hi] at hshared
    have hmem : g_J ∈ face (Ahat (σ i)) nprevJ :=
      hshared.symm ▸ Nivat.PolyChain.faceStart_mem (hfin (σ i)) hEnp
    exact suppVal_eq hmem
  intro i z hz
  set j : ℕ := max i i₀ with hj_def
  have hij : i ≤ j := le_max_left _ _
  have hi0j : i₀ ≤ j := le_max_right _ _
  have hzj : z ∈ Ahat (σ j) := AhatMono (σ i) (σ j) (hσmono.monotone hij) hz
  have hsupp := hcase j hi0j
  calc dot nprevJ z ≤ suppVal (Ahat (σ j)) nprevJ := le_suppVal (hfin (σ j)) (hne (σ j)) hzj
    _ = dot nprevJ g_J := hsupp

#print axioms Arc_subset_of_mem_Arc_right
#print axioms ord_lt_of_mem_Arc_right
#print axioms exists_fan_pred
#print axioms exists_nprevJ_vJ1
#print axioms hsupp_prev
#print axioms hgJ_level
#print axioms dot_negJ_dirJ_zero
#print axioms dot_nprevJ_vJ_neg
#print axioms exists_fan_pred_cw
#print axioms exists_nprevJ_vJ1_cw
#print axioms hsupp_prev_cw

end Nivat.LeafAJSelect

#print axioms Nivat.LeafAJSelect.Arc_eq_of_enveloped
#print axioms Nivat.LeafAJSelect.exists_gJ_pinned_ccw
#print axioms Nivat.LeafAJSelect.Arc_subset_of_mem_Arc_cw
#print axioms Nivat.LeafAJSelect.ord_lt_of_mem_Arc_cw
#print axioms Nivat.LeafAJSelect.exists_J_stable_cw
#print axioms Nivat.LeafAJSelect.exists_gJ_pinned_cw
#print axioms Nivat.LeafAJSelect.faceLen_mono_of_suppVal_eq
#print axioms Nivat.LeafAJSelect.hgrow_of_pinned_ccw
#print axioms Nivat.LeafAJSelect.hgrow_of_pinned_cw
