/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.TowerSeedConvex
import Nivat.External.Colle.TowerConstruct
import Nivat.External.Colle.EnvNegSymm

/-!
# `LevelInterval B v` for **every** generator direction `v ∥ d.h k` (lane-tower-hlev)

Consumer: the tower-package `obtain` at `RegionSteps.lean:1759`, 6th conjunct
(`hconv : IsLatticeConvexRegion Rinf`), 原文 `scratch/b3_colle2.txt:806-820`.

This file is the `k`-generic bridge lane-tower-hbase asked for.  Everything it needs already
existed; what was missing was the observation that **no `hdoth` is involved once `k` is free**.

## Why the bridge is cheaper for a general `k` than for `k = i`

`TowerConstruct.genPerp'_mem_E_B` (`TowerConstruct.lean:64`) gives, for **every** `k : Fin d.m`
and with no hypothesis beyond `henv : EnvOf ↑d.Sphi B`, that both `genPerp' (d.h k)` and its
negation lie in `E B`.  The one thing the level-interval engine needs on top of `n ∈ E B` is
`hperp : dot n v = 0`, i.e. that the sweep direction is perpendicular to the edge normal.

* For `k = i` and `v := vl` that perpendicularity is **not** free: it is exactly
  `hdoth : dot nℓ (d.h i) = 0` together with `hperp : dot nℓ vl = 0`, which jointly say
  `d.h i ∥ vl`.  (lane-towerpkg's `EnvNegSymm.nl_mem_E_B_of_hdoth` (`EnvNegSymm.lean:199`) is the
  `k = i` route, and it does consume `hdoth`.  That binder stays on the consumer's list.)
* For a general `k` and `v ∥ d.h k` it **is** free: `dot (genPerp' (d.h k)) (d.h k) = 0`
  (`ZonoEdgeGen.dot_genPerp'`, `ZonoEdgeGen.lean:66`) plus `d.h k = c • v` with `c ≠ 0` gives
  `dot (genPerp' (d.h k)) v = 0` by cancelling `c`.  Nothing about `nℓ`, `vl`, `i` or `hdoth`
  appears **in the statements below**.

⚠ **But the instantiation is not `hdoth`-free — do not read the previous bullet as more than it
says.**  The two facts that put `v := wgen d nℓ j` into the hypotheses here,

* `TowerConstruct.wgen_prim` (`TowerConstruct.lean:147`) → `hv : Primitive (wgen d nℓ j)`, and
* `TowerConstruct.det_wgen_h_eq_zero` (`TowerConstruct.lean:623`) → `hpar : det (wgen d nℓ j)
  (d.h j) = 0`,

**both** carry the binder group `hvl_prim / hprim / hperp / i / hdoth / hij : j ≠ i`.  So
instantiating at a chain direction drags `hdoth` back in.  What is gained is *not* the
elimination of `hdoth` but the elimination of the **`k = i` restriction**: the level-interval
engine now runs at every chain direction, not only at the `vl`-parallel one.  No **new** binder
is introduced — `hdoth` is already a consumer binder (`RegionSteps.lean:1711-1730`) and
`hij : j ≠ i` holds for every candidate because `candSet` erases `i` (`TowerConstruct.lean:246`).
(This is the `d : DecompData ξ` failure mode recorded in `OPEN.md #10e-撤回`: a lemma's own
statement being free of a hypothesis says nothing about what its instantiation costs.)

So the theorems below hold for each chain direction `wtower d nℓ vl u' i k`, because
`wgen d nℓ k = primPart (orientGen d nℓ k)` is by construction primitive and parallel to
`d.h k` — and that is what makes lane-tower-hbase's `n ≥ 1` argument run on `B` with direction
`w_k` rather than on the tower layer itself.

## What `henv` is actually being spent on

`Enveloped` (`LatticeEdges.lean:628`) bundles three things; this file uses two of them:
lattice convexity of `B` (via `EnvNegSymm.latticeConvex_of_envOf`, `EnvNegSymm.lean:190`) and
`E B = E ↑d.Sphi` (inside `genPerp'_mem_E_B`).  The **edge-length** clause
(`(face U n).encard ≤ (face B n).encard`) is not invoked here: `E B`'s own definition
(`LatticeEdges.lean:217`) already carries `(face B n).Nontrivial` as its second component, which
is all the unit-step extraction needs.

⚠ **Scope** (`PROTOCOL.md §40`).  Nothing below asserts that any particular `v` *is* a chain
direction, nor that the chain-order signs come out one way rather than the other.  The statements
are: given a primitive `v` parallel to *some* generator, `B` has a unit `v`-step at both its
`det v`-extremes, hence `LevelInterval B v`.  Whether `wtower` actually enumerates generators in
the order the tower induction needs is lane-tower-hbase's question and is untouched here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Nivat.LaneTowerHlevGen

open Nivat Nivat.LE2 Nivat.RegionSweep Nivat.ColleReg

variable {ξ : Nivat.Config ℤ}

/-- **Perpendicularity is free for a generator-parallel direction.**  If `v` is primitive and
`det v (d.h k) = 0` (i.e. `v ∥ d.h k`), then `genPerp' (d.h k)` is orthogonal to `v`.

This is the step that consumes no `hdoth`: the edge normal and the sweep direction are attached
to the *same* generator, so their orthogonality is `ZonoEdgeGen.dot_genPerp'` after cancelling
the nonzero integer `c` in `d.h k = c • v`. -/
theorem dot_genPerp'_eq_zero_of_par (d : Nivat.Colle35.DecompData ξ) (k : Fin d.m) {v : ℤ × ℤ}
    (hv : Primitive v) (hpar : det v (d.h k) = 0) :
    dot (Nivat.LE2.genPerp' (d.h k)) v = 0 := by
  have hhne : d.h k ≠ 0 := d.h_ne k
  obtain ⟨c, hc⟩ := Nivat.eq_zsmul_of_det_eq_zero hv hpar
  have hc0 : c ≠ 0 := by
    intro h0
    apply hhne
    rw [hc, h0, zero_smul]
  have h1 : dot (Nivat.LE2.genPerp' (d.h k)) (d.h k) = 0 := by
    rw [Nivat.LE2.dot_comm]
    exact Nivat.LE2.dot_genPerp' hhne
  have h2 : dot (Nivat.LE2.genPerp' (d.h k)) ((c : ℤ) • v) = 0 := by
    rw [← hc]; exact h1
  rw [Nivat.ConeRegion.dot_zsmul] at h2
  rcases mul_eq_zero.mp h2 with h | h
  · exact absurd h hc0
  · exact h

/-- **Both `det v`-extreme faces of `B` carry a unit `v`-step**, for any primitive `v` parallel
to a generator `d.h k`.

原文 `:806-820`: the tower's sweep directions are the generator directions of `𝒮_φ`, and the
zonotope is centrally symmetric (`DecompData.Sphi_eq`, `DecompData.lean:108`), so `B` — being
enveloped by it — has a `v`-parallel edge with at least two lattice points on **each** side.
That is exactly a unit `v`-step at the `det v`-maximum and one at the `det v`-minimum. -/
theorem exists_gen_unit_steps {B : Set (ℤ × ℤ)} (d : Nivat.Colle35.DecompData ξ)
    (henv : Nivat.LE2.EnvOf (↑d.Sphi : Set (ℤ × ℤ)) B) (k : Fin d.m) {v : ℤ × ℤ}
    (hv : Primitive v) (hpar : det v (d.h k) = 0) :
    (∃ c ∈ B, (∀ z ∈ B, det v z ≤ det v c) ∧ c + v ∈ B) ∧
    (∃ e ∈ B, (∀ z ∈ B, det v e ≤ det v z) ∧ e + v ∈ B) := by
  obtain ⟨hpos, hneg⟩ := Nivat.ColleReg.genPerp'_mem_E_B d henv k
  exact Nivat.LaneTowerHlevConv.exists_det_extreme_unit_steps
    (Nivat.LaneTowerPkgEnvSymm.latticeConvex_of_envOf henv) hv
    (Nivat.LE2.genPerp'_prim (d.h_ne k)) (dot_genPerp'_eq_zero_of_par d k hv hpar) hpos hneg

/-- **`hstep` for `levelInterval_tower_of_cone_closure`**: the unit `v`-step at the
`det v`-minimum of the seed.  This is the `.2` half of `exists_gen_unit_steps`, named separately
because it is the shape that `TowerSeedConvex.exists_min_unit_step_of_seed` consumes. -/
theorem exists_gen_min_unit_step {B : Set (ℤ × ℤ)} (d : Nivat.Colle35.DecompData ξ)
    (henv : Nivat.LE2.EnvOf (↑d.Sphi : Set (ℤ × ℤ)) B) (k : Fin d.m) {v : ℤ × ℤ}
    (hv : Primitive v) (hpar : det v (d.h k) = 0) :
    ∃ e ∈ B, (∀ z ∈ B, det v e ≤ det v z) ∧ e + v ∈ B :=
  (exists_gen_unit_steps d henv k hv hpar).2

/-- **`LevelInterval B v` for every generator-parallel primitive `v`.**

This is lane-tower-hbase's requested `(n, v)`-generic form, already instantiated at the only
family of directions the tower uses.  Note that `vl` never appears: the direction is `v`, and
`v := wgen d nℓ k` for any `k` is a legal instance. -/
theorem levelInterval_of_gen {B : Set (ℤ × ℤ)} (d : Nivat.Colle35.DecompData ξ)
    (henv : Nivat.LE2.EnvOf (↑d.Sphi : Set (ℤ × ℤ)) B) (k : Fin d.m) {v : ℤ × ℤ}
    (hv : Primitive v) (hpar : det v (d.h k) = 0) :
    LevelInterval B v := by
  obtain ⟨hpos, hneg⟩ := Nivat.ColleReg.genPerp'_mem_E_B d henv k
  exact Nivat.LaneTowerHlevConv.levelInterval_of_edges
    (Nivat.LaneTowerPkgEnvSymm.latticeConvex_of_envOf henv) hv
    (Nivat.LE2.genPerp'_prim (d.h_ne k)) (dot_genPerp'_eq_zero_of_par d k hv hpar) hpos hneg

/-! ## §2. Instantiating at the actual chain directions: `∀ k, LevelInterval B (wtower … k)`

This is the `hlevB` binder of `TowerHBaseMin.isLatticeConvexRegion_tower_of_seed` and the `hlev`
binder of `lane-towerpkg`'s `hconv_of_levelInterval`, delivered for **every** `k` with no index
restriction.  Two cases, matching `wtower`'s own `dite` (`TowerConstruct.lean:383`):

* `k < (sortedCand …).length`: `wtower … k ∈ candSet` (`mem_candSet_wtower`,
  `TowerConstruct.lean:402`), and `candSet` is by definition an image of `wgen d nℓ ·` over
  `j ≠ i`, so §1 applies at that `j`.
* `k ≥ (sortedCand …).length`: `wtower … k = -vl`, and `LevelInterval B (-vl)` follows from
  `LevelInterval B vl` by the free `w ↦ -w` symmetry.  `LevelInterval B vl` is §1 at `k := i`,
  whose `hpar : det vl (d.h i) = 0` is `det_eq_zero_of_dot_eq_zero` (`LatticeEdges.lean:110`)
  applied to `hperp` and `hdoth` — the two vectors orthogonal to the same nonzero `nℓ`.

⚠ So the `k ≥ length` tail is **not** a gap: lane-tower-hbase offered to handle it separately
(`wtower_last`, `det (wt n) vl = 0` there), but it costs nothing here. -/

/-- `det (-w) x = -det w x`. -/
theorem det_neg_left' (w x : ℤ × ℤ) : det (-w) x = -det w x := by
  simp only [det, Prod.fst_neg, Prod.snd_neg]
  ring

/-- **`LevelInterval` is invariant under negating the direction.**  (Same statement as
`L1RegionBuild.levelInterval_neg_of_levelInterval` (`L1RegionBuild.lean:203`) and as
`lane-tower-hlev-dom`'s `levelInterval_neg`; re-proved here in three lines to keep this file's
import list down to `TowerSeedConvex` / `TowerConstruct` / `EnvNegSymm`.  The integrator should
keep one copy when these land.) -/
theorem levelInterval_neg {C : Set (ℤ × ℤ)} {w : ℤ × ℤ} (h : LevelInterval C w) :
    LevelInterval C (-w) := by
  intro a ha b hb m hma hmb
  rw [det_neg_left'] at hma
  rw [det_neg_left'] at hmb
  obtain ⟨c, hc, hcm⟩ := h b hb a ha (-m) (by linarith) (by linarith)
  exact ⟨c, hc, by rw [det_neg_left', hcm]; ring⟩

/-- **Every candidate direction is generator-parallel**, so §1 gives it a level interval.
`candSet d nℓ u' i = ((univ.erase i).image (wgen d nℓ)).erase u'` (`TowerConstruct.lean:246`),
so membership hands us the `j ≠ i` that `wgen_prim` / `det_wgen_h_eq_zero` need. -/
theorem levelInterval_of_mem_candSet {B : Set (ℤ × ℤ)} (d : Nivat.Colle35.DecompData ξ)
    (henv : Nivat.LE2.EnvOf (↑d.Sphi : Set (ℤ × ℤ)) B)
    {vl nℓ u' : ℤ × ℤ} (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0)
    {v : ℤ × ℤ} (hv : v ∈ candSet d nℓ u' i) :
    LevelInterval B v := by
  obtain ⟨_, hv_img⟩ := Finset.mem_erase.mp hv
  obtain ⟨j, hj_mem, hj⟩ := Finset.mem_image.mp hv_img
  have hij : j ≠ i := (Finset.mem_erase.mp hj_mem).1
  subst hj
  exact levelInterval_of_gen d henv j (wgen_prim d hvl_prim hprim hperp i hdoth hij)
    (det_wgen_h_eq_zero d hvl_prim hprim hperp i hdoth hij)

/-- `vl` is parallel to `d.h i`: both are orthogonal to the nonzero `nℓ` (`hperp` and `hdoth`). -/
theorem det_vl_h_i_eq_zero (d : Nivat.Colle35.DecompData ξ) {vl nℓ : ℤ × ℤ} (hprim : Prim nℓ)
    (hperp : dot nℓ vl = 0) (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0) :
    det vl (d.h i) = 0 :=
  Nivat.LE2.det_eq_zero_of_dot_eq_zero hprim.ne_zero hperp hdoth

/-- **`LevelInterval B vl`** — §1 at the `vl`-parallel generator `d.h i`.  This is the one place
`hdoth` is genuinely spent. -/
theorem levelInterval_vl {B : Set (ℤ × ℤ)} (d : Nivat.Colle35.DecompData ξ)
    (henv : Nivat.LE2.EnvOf (↑d.Sphi : Set (ℤ × ℤ)) B)
    {vl nℓ : ℤ × ℤ} (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0) :
    LevelInterval B vl :=
  levelInterval_of_gen d henv i hvl_prim (det_vl_h_i_eq_zero d hprim hperp i hdoth)

/-- **`hstepB : ∃ a ∈ B, a + vl ∈ B`** — the weakest shape lane-tower-hbase asked for
(`isLatticeConvexRegion_tower_wtower`, `TowerHBaseMin.lean:1536`).  It is the `det vl`-maximal
half of `exists_gen_unit_steps` at `k := i`, with the maximality clause discarded. -/
theorem exists_vl_step {B : Set (ℤ × ℤ)} (d : Nivat.Colle35.DecompData ξ)
    (henv : Nivat.LE2.EnvOf (↑d.Sphi : Set (ℤ × ℤ)) B)
    {vl nℓ : ℤ × ℤ} (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0) :
    ∃ a ∈ B, a + vl ∈ B := by
  obtain ⟨c, hc, _, hcs⟩ :=
    (exists_gen_unit_steps d henv i hvl_prim
      (det_vl_h_i_eq_zero d hprim hperp i hdoth)).1
  exact ⟨c, hc, hcs⟩

/-- **`hlevB : ∀ k, LevelInterval B (wtower d nℓ vl u' i k)`** — the binder of
`TowerHBaseMin.isLatticeConvexRegion_tower_of_seed` (`TowerHBaseMin.lean:1222`) and of
`lane-towerpkg`'s `hconv_of_levelInterval`.  Uniform in `k`: no upper bound, the `-vl` tail
included.

原文 `:806-820`: the tower's sweep directions are exactly the generator directions of `𝒮_φ`
(plus the closing `-vl`), and `B` is enveloped by `𝒮_φ`, so each of them is parallel to an edge
of `B` on both sides. -/
theorem levelInterval_wtower {B : Set (ℤ × ℤ)} (d : Nivat.Colle35.DecompData ξ)
    (henv : Nivat.LE2.EnvOf (↑d.Sphi : Set (ℤ × ℤ)) B)
    {vl nℓ : ℤ × ℤ} (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0) (u' : ℤ × ℤ) (k : ℕ) :
    LevelInterval B (wtower d nℓ vl u' i k) := by
  by_cases hk : k < (sortedCand d nℓ u' i).length
  · exact levelInterval_of_mem_candSet d henv hvl_prim hprim hperp i hdoth
      (mem_candSet_wtower hk)
  · have hlast : wtower d nℓ vl u' i k = -vl := by
      unfold wtower; simp [hk]
    rw [hlast]
    exact levelInterval_neg (levelInterval_vl d henv hvl_prim hprim hperp i hdoth)

/-- **The seed's lattice convexity itself**, restated here so callers need not chase
`Enveloped`'s first projection.  (Thin wrapper over `EnvNegSymm.latticeConvex_of_envOf`.) -/
theorem latticeConvex_seed {U B : Set (ℤ × ℤ)} (henv : Nivat.LE2.EnvOf U B) :
    IsLatticeConvexRegion B :=
  Nivat.LaneTowerPkgEnvSymm.latticeConvex_of_envOf henv

/-! ## §3  `hR₀` packaged at `henv`

`TowerSeedConvex.isLatticeConvexRegion_coneRegion_of_faces` (`TowerSeedConvex.lean:421`) asks for
`hface`/`hfaceneg` at an edge normal `n ⟂ vl`.  lane-tower-hbase should not have to produce those:
§1 already gives `LevelInterval B vl` straight from `henv` (`levelInterval_vl`), and that is the
only thing the face hypotheses were ever used for inside that proof.  So the version below takes
exactly the consumer's binders (`RegionSteps.lean:1711-1730`) plus `hunimod`.

原文 `b3_colle2.txt:780`: the seed region `𝓡_I` is the cone `B + ℕ·vl + ℕ·u'`.

⚠ `hunimod : det u' vl = ±1` is **not** derived here; it is a free data constraint at
`L1Claim.lean:195-225` (`Primitive.exists_dual`).  Both signs are allowed, matching
lane-tower-hbase's two orientations (`isLatticeConvexRegion_tower_of_seed` /
`…_of_seed_pos`). -/
theorem latticeConvex_coneRegion_of_envOf {B : Set (ℤ × ℤ)} (d : Nivat.Colle35.DecompData ξ)
    (henv : Nivat.LE2.EnvOf (↑d.Sphi : Set (ℤ × ℤ)) B)
    {vl nℓ u' : ℤ × ℤ} (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0)
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) :
    IsLatticeConvexRegion (Nivat.ConeRegion.coneRegion B vl u') := by
  have hB : IsLatticeConvexRegion B := latticeConvex_seed henv
  have hlev : LevelInterval B vl := levelInterval_vl d henv hvl_prim hprim hperp i hdoth
  have h1 : IsLatticeConvexRegion (sweep B vl) := isLatticeConvexRegion_sweep hB hvl_prim hlev
  have hstep : ∀ g ∈ sweep B vl, g + vl ∈ sweep B vl :=
    Nivat.LaneTowerHlevConv.add_mem_sweep_self
  have hlev2 : LevelInterval (sweep B vl) u' := by
    rcases hunimod with h | h
    · exact Nivat.LaneTowerHlev.levelInterval_of_step_det_one hstep h
    · exact Nivat.LaneTowerHlev.levelInterval_of_step_det_neg_one hstep h
  show IsLatticeConvexRegion (sweep (sweep B vl) u')
  exact isLatticeConvexRegion_sweep h1
    (Nivat.LaneTowerHlevConv.primitive_of_det_eq_pm_one hunimod) hlev2

/-- The same in `tower` vocabulary: the `n = 0` layer of the tower over the cone seed. -/
theorem tower_zero_latticeConvex_of_envOf {B : Set (ℤ × ℤ)} (d : Nivat.Colle35.DecompData ξ)
    (henv : Nivat.LE2.EnvOf (↑d.Sphi : Set (ℤ × ℤ)) B)
    {vl nℓ u' : ℤ × ℤ} {wf : ℕ → ℤ × ℤ}
    (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0)
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) :
    IsLatticeConvexRegion (tower (Nivat.ConeRegion.coneRegion B vl u') wf 0) := by
  have h := latticeConvex_coneRegion_of_envOf d henv hvl_prim hprim hperp i hdoth hunimod
  simpa [tower] using h

end Nivat.LaneTowerHlevGen

#print axioms Nivat.LaneTowerHlevGen.dot_genPerp'_eq_zero_of_par
#print axioms Nivat.LaneTowerHlevGen.exists_gen_unit_steps
#print axioms Nivat.LaneTowerHlevGen.exists_gen_min_unit_step
#print axioms Nivat.LaneTowerHlevGen.levelInterval_of_gen
#print axioms Nivat.LaneTowerHlevGen.det_neg_left'
#print axioms Nivat.LaneTowerHlevGen.levelInterval_neg
#print axioms Nivat.LaneTowerHlevGen.levelInterval_of_mem_candSet
#print axioms Nivat.LaneTowerHlevGen.det_vl_h_i_eq_zero
#print axioms Nivat.LaneTowerHlevGen.levelInterval_vl
#print axioms Nivat.LaneTowerHlevGen.exists_vl_step
#print axioms Nivat.LaneTowerHlevGen.levelInterval_wtower
#print axioms Nivat.LaneTowerHlevGen.latticeConvex_seed
#print axioms Nivat.LaneTowerHlevGen.latticeConvex_coneRegion_of_envOf
#print axioms Nivat.LaneTowerHlevGen.tower_zero_latticeConvex_of_envOf
