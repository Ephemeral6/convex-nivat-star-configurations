/-
Copyright (c) 2026 Nivat Formalization Contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lane-towerpkg
-/
import Nivat.External.Colle.TowerPackage
import Nivat.External.Colle.TowerConstruct
import Nivat.External.Colle.TowerHBaseMin
import Nivat.External.Colle.TowerPkgParts
import Nivat.External.Colle.TowerUnb
import Nivat.External.Colle.TowerSeedConvex
import Nivat.External.Colle.EnvNegSymm
import Nivat.External.Colle.TowerGenBridge
import Nivat.External.Colle.HsuppTowerGeneral
import Nivat.External.Colle.HalfPlaneNotPeriodOn
import Nivat.External.Colle.L1Region
import Nivat.External.Colle.Lemma41
import Nivat.External.Colle.DecompData
import Nivat.Defs.Config

/-!
# lane-towerpkg: the tower package of `exists_cutResidualR_of_claim46` (0 sorry)

Target consumer: the type-ascribed `obtain` inside `exists_cutResidualR_of_claim46`
(`RegionSteps.lean`; 第 157 轮起已不是 `sorry`). Original text `scratch/b3_colle2.txt:806-820`.

## The choice of `w` (correcting the earlier `w := u'` guess)

`:816` names the composite's second cone direction `ℓ' := ℓ_I`, where `I` is the **smallest**
index with `(T^u η)|𝓡_I` periodic, and `Rinf := 𝓡_{I−1}`. Paper indices count **down** while
`ColleReg.tower` counts **up**, so with `Ilean` the index produced by
`ColleReg.exists_tower_index` (`TowerPackage.lean:308`):

* `𝓡_I   = tower (coneRegion B vl u') wtower Ilean`      (periodic, `hper`)
* `𝓡_{I−1} = tower (coneRegion B vl u') wtower (Ilean+1)` (not periodic, `hnper`) `=: Rinf`
* `v⃗_{ℓ_{I−1}} = wtower Ilean` is the sweep direction that builds `Rinf` from `𝓡_I`
* `v⃗_{ℓ_I} = ℓ' = ` the sweep direction that built `𝓡_I` from `𝓡_{I+1}`, i.e. the **previous**
  chain entry `extChain Ilean` (`= u'` at `Ilean = 0`, `= wtower (Ilean−1)` otherwise).

So `w := extChain d nℓ vl u' i Ilean` (`TowerConstruct.lean:906`), **not** `u'`.
`tmp/wip/lane-towerpkg2-boundary-hpackage.lean`'s `w := u'` is only the `Ilean = 0` instance.

With `m := expNormal w vl` (`L1RegionBuild.lean:284`; `dot m w = 0`, `0 < dot m vl` are
`TowerPkgParts.lean:61/70`'s two facts) the half-turn lemma `det_pos_extChain`
(`TowerConstruct.lean:1009`) fixes every sign the package needs, uniformly in `hunimod`'s branch:

* `dot m (extChain k) ≥ 0` for every `k ≤ Ilean` (`dot_m_extChain_nonneg`) — `𝓡_I` lies on one
  side of its own `ℓ'`-support line;
* `dot m (wtower Ilean) < 0` (`dot_m_step_neg`) — the step that builds `Rinf` crosses it;
* `dot nℓ w < 0` (`dot_extChain_neg`, `TowerConstruct.lean:910`).

## What is closed here

`lane_towerpkg_package` proves the 11-conjunct existential of the type-ascribed `obtain` in
`exists_cutResidualR_of_claim46` (`RegionSteps.lean`)
**with no residual and no sorry** (第 155 轮).  `lane_towerpkg_reduce` is the same statement with
the seed-side level condition

* `hlevB : ∀ n, n < (sortedCand d nℓ u' i).length →
    LevelInterval B (wtower d nℓ vl u' i n)`

still a binder; `lane_towerpkg_package` discharges it with
`LaneTowerHlevGen.levelInterval_wtower` (`TowerGenBridge.lean`, lane-tower-hlev), whose `∀ k` is
unbounded.  Binders are exactly `exists_cutResidualR_of_claim46`'s (`RegionSteps.lean`)
minus the ones the tower package does not use (`hgen`, `S`, `gen`); nothing was added.

The tower-side convexity `hconv` — every layer `𝓡_i` is a `(−ℓ, ℓ_i)`-region, 原文 `:808` — is
**not** a binder any more.  `hconv_of_levelB` (§2e) gets it from lane-tower-hbase's
`TowerHBaseMin.isLatticeConvexRegion_tower_wtower` (`:1541`, `det u' vl = -1`) and `_pos`
(`:1601`, `= 1`), which cover both branches of `hunimod` and include the `-vl` tail of the chain
(there the level condition is free, `levelInterval_tower_unit` `:1304`).  Their two remaining
inputs are paid for out of `henv`: `hR₀` by `latticeConvex_of_envOf` + `nl_mem_E_B_of_hdoth`
(`EnvNegSymm.lean:190`/`:199`) + `isLatticeConvexRegion_coneRegion` (`TowerSeedConvex.lean:438`),
and `hstepB : ∃ a ∈ B, a + vl ∈ B` by `exists_unit_step_of_face` (`TowerSeedConvex.lean:134`) at
the `nℓ`-face of `B`.

Everything else is discharged here: `det vl w ≠ 0`, `Primitive w`, `dot m w = 0`, `0 < dot m vl`,
both rays of `Colle41.IsRegion Rinf vl w`, `h0`, `hunb`, `hbase`, `hinf`, `dot nℓ w < 0`, `htop`.

In particular `hbase` (and with it `h0`) is **no longer an independent obligation**:
`hcut_of_latticeConvex` derives the paper's `:818` cut identity from lattice convexity alone —
`b₀` is taken to be the `dot m`-maximum over the finite seed `B`, `cone_coords_of_mem_tower`
puts every point of `𝓡_I` inside `b + cone(vl, w)` for some `b ∈ B`, the cut hypothesis restores
the `w`-side inequality for the swept point, and `mem_of_nsmul_cone` divides the Cramer identity
`det vl w • x = (- det w x) • vl + (det vl x) • w` back down using lattice convexity.  (The
version actually called is lane-tower-hbase's `TowerHBaseMin.hcut_tower` (`:637`); the one below
is this lane's independent proof, kept as a cross-check.)

⚠ Do **not** reinstate the decomposition of `hconv` into `hR₀ + hlev` *as stated in terms of bare
`B`*: all three routes are kernel-refuted (`tmp/wip/lane-towerpkg-hR0-finiteB-refuted.lean:85`,
`tmp/wip/lane-towerpkg-levelinterval-refuted.lean:43`,
`tmp/wip/lane-towerpkg-hlev-counterexample.lean:42`).  What made the chain close instead is that
`levelInterval_of_descent` (`TowerHBaseMin.lean:1186`) never needs the tower layer's own
convexity, so the seed-side condition alone suffices.

## Two facts worth not re-deriving

* `TowerHBase.hbase_of_prev_level_periodOn`'s `hmax : ∀ z ∈ C, dot m z ≤ b₀` is identically
  false on tower levels once `0 < dot m vl`
  (`tmp/wip/lane-towerpkg-interior-hbase-obstruction.lean:43`). The route taken here never uses
  an upper bound on `dot m` over a tower level.
* The cut level `b₀` must sit at or **above the whole seed** `B`, not merely at `𝓡_I`'s own
  `dot m`-support level: at the support level the cut identity is FALSE
  (`hcut_support_level_false` below, kernel counterexample) — `B` may protrude across `𝓡_I`'s
  `ℓ'`-edge line in the `-w` direction, and one `wtower I`-step from such a protruding point
  lands back on that line outside `𝓡_I`.
-/

set_option autoImplicit false

open Nivat Nivat.LE2 Nivat.Colle41 Nivat.L1Region Nivat.ColleReg Nivat.ConeRegion
  Nivat.RegionSweep Nivat.Colle35

namespace Nivat.LaneTowerPkgMain

variable {ξ : Config ℤ}

/-! ## §1  Sign arithmetic for `m := expNormal w vl` along the tower chain -/

/-- `dot (expNormal a b) z = det a b * det a z`, unfolding `expNormal a b := det a b • perp a`
(`L1RegionBuild.lean:284`). -/
theorem dot_expNormal_eq (a b z : ℤ × ℤ) :
    dot (expNormal a b) z = det a b * det a z := by
  simp only [expNormal, dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, det]
  ring

/-- `det v (-w) = - det v w`. -/
theorem det_neg_right (v w : ℤ × ℤ) : det v (-w) = - det v w := by
  simp only [det, Prod.fst_neg, Prod.snd_neg]; ring

/-- `dot n (-v) = - dot n v` (local copy: the name is ambiguous across the opened namespaces). -/
theorem dot_neg_right_loc (n v : ℤ × ℤ) : dot n (-v) = - dot n v := by
  simp only [dot, Prod.fst_neg, Prod.snd_neg]; ring

/-- **The chain entry at index `I` sees `-vl` on the same side as `u'` does.**
`extChain _ 0 = u'` makes `I = 0` trivial; for `I = J + 1` the entry is the genuine `candSet`
member `wtower _ J` and this is `det_w_negvl_sign_eq` (`TowerConstruct.lean:462`). -/
theorem det_extChain_negvl_sign_eq (d : DecompData ξ) {vl nℓ u' : ℤ × ℤ}
    (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0) (hnu : dot nℓ u' < 0)
    {I : ℕ} (hI : I ≤ (sortedCand d nℓ u' i).length) :
    (0 < det (extChain d nℓ vl u' i I) (-vl)) ↔ (0 < det u' (-vl)) := by
  cases I with
  | zero => simp only [extChain]
  | succ J =>
    have hJ : J < (sortedCand d nℓ u' i).length := by omega
    simp only [extChain]
    exact det_w_negvl_sign_eq d hvl_prim hprim hperp i hdoth hnu (mem_candSet_wtower hJ)

/-- **One chain step, including the `-vl` boundary step.** `det_extChain_consec`
(`TowerConstruct.lean:935`) only covers `t < len`; at `t = len` the next entry is
`wtower _ len = -vl` (`wtower_last`) and the sign comes from `det_extChain_negvl_sign_eq`. -/
theorem det_extChain_step_sign {B : Set (ℤ × ℤ)} (d : DecompData ξ) {vl nℓ u' : ℤ × ℤ}
    (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (henv : Nivat.LE2.EnvOf (↑d.Sphi : Set (ℤ × ℤ)) B)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0)
    (hadjB : ∀ n ∈ E B, ¬ (dot n vl < 0 ∧ 0 < dot n u'))
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) (hnu : dot nℓ u' < 0) (hnℓ_ne : nℓ ≠ 0)
    {I : ℕ} (hI : I ≤ (sortedCand d nℓ u' i).length) :
    ((0 < det (extChain d nℓ vl u' i I) (wtower d nℓ vl u' i I)) ↔ (0 < det u' (-vl))) ∧
      det (extChain d nℓ vl u' i I) (wtower d nℓ vl u' i I) ≠ 0 := by
  rcases lt_or_eq_of_le hI with hlt | heq
  · exact det_extChain_consec d hvl_prim hprim hperp henv i hdoth hadjB hunimod hnu hnℓ_ne hlt
  · subst heq
    rw [wtower_last]
    refine ⟨det_extChain_negvl_sign_eq d hvl_prim hprim hperp i hdoth hnu le_rfl, ?_⟩
    have hwn : dot nℓ (extChain d nℓ vl u' i (sortedCand d nℓ u' i).length) < 0 :=
      dot_extChain_neg d hvl_prim hprim hperp i hdoth hnu le_rfl
    have hne : det (extChain d nℓ vl u' i (sortedCand d nℓ u' i).length) vl ≠ 0 :=
      det_ne_zero_of_dot_nl_neg hvl_prim hperp hwn
    rw [det_neg_right]
    omega

/-- **The sweep direction that builds `Rinf` strictly lowers `dot m`.**

`m := expNormal w vl` with `w := extChain _ I`, so `dot m z = det w vl * det w z`.  The two
factors at `z := wtower _ I` have *opposite* signs, both pinned to `sign (det u' (-vl))` by
`det_extChain_negvl_sign_eq` / `det_extChain_step_sign` — hence the product is negative in both
branches of `hunimod`.  This is the `:808` sweep direction `v⃗_{ℓ_{I−1}}` pointing out of `𝓡_I`
across its `ℓ'`-edge. -/
theorem dot_m_step_neg {B : Set (ℤ × ℤ)} (d : DecompData ξ) {vl nℓ u' : ℤ × ℤ}
    (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (henv : Nivat.LE2.EnvOf (↑d.Sphi : Set (ℤ × ℤ)) B)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0)
    (hadjB : ∀ n ∈ E B, ¬ (dot n vl < 0 ∧ 0 < dot n u'))
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) (hnu : dot nℓ u' < 0) (hnℓ_ne : nℓ ≠ 0)
    {I : ℕ} (hI : I ≤ (sortedCand d nℓ u' i).length) :
    dot (expNormal (extChain d nℓ vl u' i I) vl) (wtower d nℓ vl u' i I) < 0 := by
  -- `det w vl ≠ 0`, from `dot nℓ w < 0`.
  have hwn : dot nℓ (extChain d nℓ vl u' i I) < 0 :=
    dot_extChain_neg d hvl_prim hprim hperp i hdoth hnu hI
  have hwvl_ne : det (extChain d nℓ vl u' i I) vl ≠ 0 :=
    det_ne_zero_of_dot_nl_neg hvl_prim hperp hwn
  -- `det u' vl ≠ 0`, so `det u' (-vl) ≠ 0`.
  have huvl_ne : det u' vl ≠ 0 := det_ne_zero_of_dot_nl_neg hvl_prim hperp hnu
  have hunegvl : det u' (-vl) = - det u' vl := det_neg_right u' vl
  have hwnegvl : det (extChain d nℓ vl u' i I) (-vl) = - det (extChain d nℓ vl u' i I) vl :=
    det_neg_right _ _
  have hsign1 := det_extChain_negvl_sign_eq d hvl_prim hprim hperp i hdoth hnu hI
  obtain ⟨hsign2, hne2⟩ := det_extChain_step_sign d hvl_prim hprim hperp henv i hdoth hadjB
    hunimod hnu hnℓ_ne hI
  rw [dot_expNormal_eq]
  set w := extChain d nℓ vl u' i I with hw_def
  set s := wtower d nℓ vl u' i I with hs_def
  rcases lt_or_gt_of_ne huvl_ne with hu | hu
  · -- `det u' vl < 0`, i.e. `0 < det u' (-vl)`: `det w vl < 0` and `0 < det w s`.
    have hpos : 0 < det u' (-vl) := by omega
    have h1 : det w vl < 0 := by
      have := hsign1.mpr hpos
      omega
    have h2 : 0 < det w s := hsign2.mpr hpos
    exact mul_neg_of_neg_of_pos h1 h2
  · -- `0 < det u' vl`, i.e. `det u' (-vl) < 0`: `0 < det w vl` and `det w s < 0`.
    have hneg : det u' (-vl) < 0 := by omega
    have h1 : 0 < det w vl := by
      have hnot : ¬ (0 < det w (-vl)) := fun h => absurd (hsign1.mp h) (by omega)
      omega
    have h2 : det w s < 0 := by
      have hnot : ¬ (0 < det w s) := fun h => absurd (hsign2.mp h) (by omega)
      omega
    exact mul_neg_of_pos_of_neg h1 h2

/-! ## §2  Rays inside the tower (the easy half of `Colle41.IsRegion Rinf vl w`) -/

/-- Every tower level carries a `vl`-ray from each of its points: iterate
`ColleReg.tower_add_vl_mem` (`TowerPackage.lean:47`). -/
theorem rayIn_tower_vl {B : Set (ℤ × ℤ)} {vl u' : ℤ × ℤ} (wt : ℕ → ℤ × ℤ) (n : ℕ)
    {z : ℤ × ℤ} (hz : z ∈ tower (coneRegion B vl u') wt n) :
    Colle41.RayIn (tower (coneRegion B vl u') wt n) z vl := by
  intro k
  induction k with
  | zero => simpa using hz
  | succ j ih =>
    have hstep := tower_add_vl_mem wt n ih
    have heq : z + (j : ℤ) • vl + vl = z + ((j + 1 : ℕ) : ℤ) • vl := by push_cast; module
    rwa [heq] at hstep

/-- Every tower level of index `J + 1` carries a `extChain _ J`-ray from each point of the seed
cone.  Two cases, matching `extChain`'s own two cases: at `J = 0` the direction is `u'` and the
ray already lies in the seed `coneRegion`; at `J = J' + 1` the direction is `wtower _ J'`, the
very direction `tower _ (J' + 1)` is swept by, so the ray is `RegionSweep.add_nsmul_mem_sweep`. -/
theorem rayIn_tower_extChain {B : Set (ℤ × ℤ)} (d : DecompData ξ) {vl nℓ u' : ℤ × ℤ}
    (i : Fin d.m) (J : ℕ) {z : ℤ × ℤ} (hz : z ∈ coneRegion B vl u') :
    Colle41.RayIn (tower (coneRegion B vl u') (wtower d nℓ vl u' i) (J + 1)) z
      (extChain d nℓ vl u' i J) := by
  intro k
  cases J with
  | zero =>
    have hmem : z + (k : ℤ) • u' ∈ coneRegion B vl u' := by
      rw [mem_coneRegion_iff] at hz ⊢
      obtain ⟨b, hb, s, t, rfl⟩ := hz
      exact ⟨b, hb, s, t + k, by push_cast; rw [add_smul]; abel⟩
    have h0 : z + (k : ℤ) • u' ∈ tower (coneRegion B vl u') (wtower d nℓ vl u' i) 0 := hmem
    exact tower_subset_succ _ _ 0 h0
  | succ J' =>
    have hz0 : z ∈ tower (coneRegion B vl u') (wtower d nℓ vl u' i) J' :=
      tower_monotone _ _ (Nat.zero_le J') hz
    have hstep : z + (k : ℤ) • (wtower d nℓ vl u' i J') ∈
        tower (coneRegion B vl u') (wtower d nℓ vl u' i) (J' + 1) :=
      add_nsmul_mem_sweep hz0 k
    exact tower_subset_succ _ _ _ hstep

/-! ## §2b  `dot m` is bounded below on `𝓡_I`, with the bound attained

This is the half of the paper's `d_0 = 0` datum (`:818`) that does *not* need any convexity:
`𝓡_I`'s support level in the direction `m ⊥ ℓ'` exists and is attained on the seed `B`.
-/

/-- **Every chain direction at or before index `I` has `dot m ≥ 0`, for `m := expNormal
(extChain _ I) vl`.**

At `j = I` the value is `0` (that is `dot m w = 0`, `hmw`).  For `j < I` the half-turn lemma
`det_pos_extChain` (`TowerConstruct.lean:1009`) puts `det (extChain I) (extChain j)` and
`det (extChain I) vl` on the *same* side of `0` — both are pinned to the opposite sign from
`det u' (-vl)` — so their product `dot m (extChain j)` is strictly positive.

Geometrically: the whole tower is built by sweeping in directions that rotate monotonically
(`:808`'s cyclic order), and `m` is the inward normal at the `ℓ'`-edge, so every *earlier*
direction points into the `m`-increasing half-plane.  This is why `𝓡_I` sits above its own
`ℓ'`-support line, which is what `hcut` below cuts along. -/
theorem dot_m_extChain_nonneg {B : Set (ℤ × ℤ)} (d : DecompData ξ) {vl nℓ u' : ℤ × ℤ}
    (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (henv : Nivat.LE2.EnvOf (↑d.Sphi : Set (ℤ × ℤ)) B)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0)
    (hadjB : ∀ n ∈ E B, ¬ (dot n vl < 0 ∧ 0 < dot n u'))
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) (hnu : dot nℓ u' < 0) (hnℓ_ne : nℓ ≠ 0)
    {I j : ℕ} (hI : I ≤ (sortedCand d nℓ u' i).length) (hj : j ≤ I) :
    0 ≤ dot (expNormal (extChain d nℓ vl u' i I) vl) (extChain d nℓ vl u' i j) := by
  rw [dot_expNormal_eq]
  rcases eq_or_lt_of_le hj with heq | hlt
  · subst heq
    rw [det_self]
    simp
  · have hkey := det_pos_extChain d hvl_prim hprim hperp henv i hdoth hadjB hunimod hnu hnℓ_ne
      hlt hI
    have hsign1 := det_extChain_negvl_sign_eq d hvl_prim hprim hperp i hdoth hnu hI
    have hwn : dot nℓ (extChain d nℓ vl u' i I) < 0 :=
      dot_extChain_neg d hvl_prim hprim hperp i hdoth hnu hI
    have hwvl_ne : det (extChain d nℓ vl u' i I) vl ≠ 0 :=
      det_ne_zero_of_dot_nl_neg hvl_prim hperp hwn
    have huvl_ne : det u' vl ≠ 0 := det_ne_zero_of_dot_nl_neg hvl_prim hperp hnu
    have hunegvl : det u' (-vl) = - det u' vl := det_neg_right u' vl
    have hwnegvl : det (extChain d nℓ vl u' i I) (-vl) = - det (extChain d nℓ vl u' i I) vl :=
      det_neg_right _ _
    have hsk : det (extChain d nℓ vl u' i I) (extChain d nℓ vl u' i j)
        = - det (extChain d nℓ vl u' i j) (extChain d nℓ vl u' i I) :=
      det_skew _ _
    have hjI_ne : det (extChain d nℓ vl u' i j) (extChain d nℓ vl u' i I) ≠ 0 := by
      intro h0; rw [h0] at hkey; simp at hkey
    rcases lt_or_gt_of_ne huvl_ne with hu | hu
    · -- `det u' vl < 0`, i.e. `0 < det u' (-vl)`.
      have hpos : 0 < det u' (-vl) := by omega
      have hA : det (extChain d nℓ vl u' i I) vl < 0 := by
        have := hsign1.mpr hpos; omega
      have hjI : 0 < det (extChain d nℓ vl u' i j) (extChain d nℓ vl u' i I) :=
        (iff_pos_of_mul_pos hkey).mpr hpos
      have hBb : det (extChain d nℓ vl u' i I) (extChain d nℓ vl u' i j) < 0 := by omega
      exact le_of_lt (mul_pos_of_neg_of_neg hA hBb)
    · -- `0 < det u' vl`, i.e. `det u' (-vl) < 0`.
      have hneg : det u' (-vl) < 0 := by omega
      have hA : 0 < det (extChain d nℓ vl u' i I) vl := by
        have hnot : ¬ (0 < det (extChain d nℓ vl u' i I) (-vl)) :=
          fun h => absurd (hsign1.mp h) (by omega)
        omega
      have hjI : ¬ (0 < det (extChain d nℓ vl u' i j) (extChain d nℓ vl u' i I)) :=
        fun h => absurd ((iff_pos_of_mul_pos hkey).mp h) (by omega)
      have hBb : 0 < det (extChain d nℓ vl u' i I) (extChain d nℓ vl u' i j) := by omega
      exact le_of_lt (mul_pos hA hBb)

/-- **Lower bound transport through the tower.**  A bound `b₀ ≤ dot m ·` valid on the seed `B`
survives every sweep whose direction has `0 ≤ dot m ·`.  (Mirror image of
`HsuppTowerBase.dot_le_of_mem_tower_bounded`, but keeping the *given* bound rather than an
existentially quantified one — the package needs the bound to be the one attained at a point of
`B`, so that `h0` holds for the same `b₀`.) -/
theorem dot_ge_of_mem_tower {B : Set (ℤ × ℤ)} {vl u' m : ℤ × ℤ}
    (hvl : 0 ≤ dot m vl) (hu' : 0 ≤ dot m u') (wt : ℕ → ℤ × ℤ) (n : ℕ)
    (hw : ∀ k, k < n → 0 ≤ dot m (wt k)) {b₀ : ℤ} (hB : ∀ b ∈ B, b₀ ≤ dot m b) :
    ∀ z ∈ tower (coneRegion B vl u') wt n, b₀ ≤ dot m z := by
  induction n with
  | zero =>
    intro z hz
    simp only [tower] at hz
    rw [mem_coneRegion_iff] at hz
    obtain ⟨b, hb, s, t, rfl⟩ := hz
    have heq : dot m (b + (s : ℤ) • vl + (t : ℤ) • u')
        = dot m b + (s : ℤ) * dot m vl + (t : ℤ) * dot m u' := by
      rw [dot_add, dot_add]
      congr 2
      · cases m; cases vl; simp only [dot, Prod.smul_mk, smul_eq_mul]; ring
      · cases m; cases u'; simp only [dot, Prod.smul_mk, smul_eq_mul]; ring
    rw [heq]
    have hs : (0 : ℤ) ≤ (s : ℤ) := Int.natCast_nonneg s
    have ht : (0 : ℤ) ≤ (t : ℤ) := Int.natCast_nonneg t
    nlinarith [hB b hb]
  | succ k ih =>
    intro z hz
    simp only [tower] at hz
    rw [Nivat.RegionSweep.mem_sweep] at hz
    obtain ⟨g, hg, t, rfl⟩ := hz
    have hgge := ih (fun j hj => hw j (Nat.lt_succ_of_lt hj)) g hg
    have heq : dot m (g + (t : ℤ) • wt k) = dot m g + (t : ℤ) * dot m (wt k) := by
      rw [dot_add]
      congr 1
      cases m; cases (wt k); simp only [dot, Prod.smul_mk, smul_eq_mul]; ring
    rw [heq]
    have ht : (0 : ℤ) ≤ (t : ℤ) := Int.natCast_nonneg t
    nlinarith [hw k (Nat.lt_succ_self k), hgge]

/-! ## §2c  Why `b₀` must be below the whole seed `B`, not just below `𝓡_I`'s support line

Kernel counterexample.  Everything about this instance is faithful to the real configuration —
`det u' vl = -1` (unimodular), `dot m u' = 0`, `0 < dot m vl`, `dot m wI < 0`, and `wI` sits
strictly outside `cone(vl, u')` on the correct side (`0 < det vl wI`, `0 < det u' wI`), which is
exactly where the half-turn lemma puts `wtower I` relative to `extChain I = u'`.  Only the
*seed* is chosen adversarially: `B` protrudes in the `-u'` direction one level below its own
`dot m`-minimum.
-/

/-- **Cutting at `𝓡_I`'s own `m`-support level does not land back inside `𝓡_I`.**

`B := {(0,0), (-5,-1)}`, `vl := (0,-1)`, `u' := (1,0)`, `m := (0,-1)`, `wI := (1,1)`.
`b₀ := 0` is the `dot m`-support level of `𝓡_I := coneRegion B vl u'` (attained at `(0,0)`),
yet `(-4,0) = (-5,-1) + wI` lies in `sweep 𝓡_I wI` at exactly that level and outside `𝓡_I`.

Consequence for `lane_towerpkg_reduce`'s `hcut`: its level hypothesis has to be
"`b₀` is at or above every point of the seed `B`" (which forces `b₀ ≥ 1` here), **not**
"`b₀` bounds `dot m` below on `𝓡_I`" (which allows `b₀ = 0`). -/
theorem hcut_support_level_false :
    -- the configuration is faithful: unimodular, `m ⊥ u'`, `0 < dot m vl`, `dot m wI < 0`,
    -- and `wI` on the far side of both cone edges.
    det ((1 : ℤ), (0 : ℤ)) ((0 : ℤ), (-1 : ℤ)) = -1 ∧
    dot ((0 : ℤ), (-1 : ℤ)) ((1 : ℤ), (0 : ℤ)) = 0 ∧
    0 < dot ((0 : ℤ), (-1 : ℤ)) ((0 : ℤ), (-1 : ℤ)) ∧
    dot ((0 : ℤ), (-1 : ℤ)) ((1 : ℤ), (1 : ℤ)) < 0 ∧
    0 < det ((0 : ℤ), (-1 : ℤ)) ((1 : ℤ), (1 : ℤ)) ∧
    0 < det ((1 : ℤ), (0 : ℤ)) ((1 : ℤ), (1 : ℤ)) ∧
    -- `b₀ = 0` really is a lower bound for `dot m` on `𝓡_I`, attained there,
    (∀ z ∈ coneRegion ({((0 : ℤ), (0 : ℤ)), ((-5 : ℤ), (-1 : ℤ))} : Set (ℤ × ℤ))
        ((0 : ℤ), (-1 : ℤ)) ((1 : ℤ), (0 : ℤ)), (0 : ℤ) ≤ dot ((0 : ℤ), (-1 : ℤ)) z) ∧
    -- yet the level-`0` cut of `sweep 𝓡_I wI` escapes `𝓡_I`.
    ((-4 : ℤ), (0 : ℤ)) ∈ sweep (coneRegion ({((0 : ℤ), (0 : ℤ)), ((-5 : ℤ), (-1 : ℤ))} :
        Set (ℤ × ℤ)) ((0 : ℤ), (-1 : ℤ)) ((1 : ℤ), (0 : ℤ))) ((1 : ℤ), (1 : ℤ)) ∧
    (0 : ℤ) ≤ dot ((0 : ℤ), (-1 : ℤ)) ((-4 : ℤ), (0 : ℤ)) ∧
    ((-4 : ℤ), (0 : ℤ)) ∉ coneRegion ({((0 : ℤ), (0 : ℤ)), ((-5 : ℤ), (-1 : ℤ))} :
        Set (ℤ × ℤ)) ((0 : ℤ), (-1 : ℤ)) ((1 : ℤ), (0 : ℤ)) := by
  refine ⟨by simp [det], by simp [dot], by norm_num [dot], by norm_num [dot], by norm_num [det],
    by norm_num [det], ?_, ?_, by norm_num [dot], ?_⟩
  · intro z hz
    rw [mem_coneRegion_iff] at hz
    obtain ⟨p, hp, sc, tc, rfl⟩ := hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    have hs : (0 : ℤ) ≤ (sc : ℤ) := Int.natCast_nonneg sc
    rcases hp with rfl | rfl <;>
      · simp only [dot, Prod.mk_add_mk, Prod.smul_mk, smul_eq_mul, mul_zero, mul_one]
        omega
  · refine ⟨((-5 : ℤ), (-1 : ℤ)), ?_, 1, by norm_num⟩
    rw [mem_coneRegion_iff]
    exact ⟨((-5 : ℤ), (-1 : ℤ)), by simp, 0, 0, by simp⟩
  · intro hmem
    rw [mem_coneRegion_iff] at hmem
    obtain ⟨p, hp, sc, tc, heq⟩ := hmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    have hs : (0 : ℤ) ≤ (sc : ℤ) := Int.natCast_nonneg sc
    have ht : (0 : ℤ) ≤ (tc : ℤ) := Int.natCast_nonneg tc
    rcases hp with rfl | rfl <;>
      · simp only [Prod.mk_add_mk, Prod.smul_mk, smul_eq_mul, mul_zero, mul_one, add_zero,
          zero_add, Prod.mk.injEq] at heq
        omega

/-! ## §2d  `hcut` follows from lattice convexity alone

The paper's cut identity is not an extra geometric input: once `𝓡_I` is known to be lattice
convex, `hcut` is forced.  The argument is the `(vl, w)`-coordinate computation behind `:818`:

* every direction the tower sweeps by, up to and including `w = v⃗_{ℓ_I}`, lies in the real cone
  `cone(vl, w)` (half-turn lemma), so every `g ∈ 𝓡_I` satisfies the two cone inequalities
  against some seed point `b ∈ B`;
* the extra step `t • wtower I` that produces `𝓡_{I−1}` keeps the `vl`-side inequality (it
  rotates further away from `vl`) and breaks only the `w`-side one — and *that* is exactly the
  inequality the cut hypothesis `b₀ ≤ dot m z` restores, because `dot m · = - det vl w * det w ·`;
* so `z - b` is a nonnegative **rational** combination of `vl` and `w`; clearing the denominator
  `|det vl w|` puts `b + |det vl w| • (z - b)` into `𝓡_I` on the nose, and `z` is the point of
  the segment from `b` to it at parameter `1/|det vl w|`.  Lattice convexity closes the gap.
-/

/-- Iterated closure under `+ v`. -/
theorem add_nsmul_mem_of_closed {K : Set (ℤ × ℤ)} {v : ℤ × ℤ}
    (hcl : ∀ x ∈ K, x + v ∈ K) {x : ℤ × ℤ} (hx : x ∈ K) (n : ℕ) : x + (n : ℤ) • v ∈ K := by
  induction n with
  | zero => simpa using hx
  | succ j ih =>
    have hstep := hcl _ ih
    have heq : x + (j : ℤ) • v + v = x + ((j + 1 : ℕ) : ℤ) • v := by push_cast; module
    rwa [heq] at hstep

/-- **Clearing the denominator inside a lattice-convex region.**  If `K` is lattice convex,
contains `b`, is closed under `+ vl` and `+ w`, and `N • (z - b)` is a nonnegative integer
combination of `vl` and `w` for some `N ≥ 1`, then `z ∈ K` — `z` is the parameter-`1/N` point of
the segment from `b` to `b + N • (z - b)`, both of which lie in `K`. -/
theorem mem_of_nsmul_cone {K : Set (ℤ × ℤ)} (hK : IsLatticeConvexRegion K)
    {b z vl w : ℤ × ℤ} (hb : b ∈ K)
    (hvlK : ∀ x ∈ K, x + vl ∈ K) (hwK : ∀ x ∈ K, x + w ∈ K)
    {N A C : ℤ} (hN : 1 ≤ N) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (heq : N • (z - b) = A • vl + C • w) : z ∈ K := by
  obtain ⟨Cs, hconvex, hclosed, hKeq⟩ := hK
  -- the far endpoint `b + A • vl + C • w = b + N • (z - b)` is in `K`.
  have hyK : b + A • vl + C • w ∈ K := by
    have h1 := add_nsmul_mem_of_closed hvlK hb A.toNat
    rw [Int.toNat_of_nonneg hA] at h1
    have h2 := add_nsmul_mem_of_closed hwK h1 C.toNat
    rw [Int.toNat_of_nonneg hC] at h2
    exact h2
  have heq1 : N * (z.1 - b.1) = A * vl.1 + C * w.1 := by
    have h := congrArg Prod.fst heq
    simpa using h
  have heq2 : N * (z.2 - b.2) = A * vl.2 + C * w.2 := by
    have h := congrArg Prod.snd heq
    simpa using h
  have hbC : toReal b ∈ Cs := by rw [hKeq] at hb; exact hb
  have hyC : toReal (b + A • vl + C • w) ∈ Cs := by rw [hKeq] at hyK; exact hyK
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : (0 : ℤ) < N)
  have heq1R : (N : ℝ) * ((z.1 : ℝ) - (b.1 : ℝ)) = (A : ℝ) * (vl.1 : ℝ) + (C : ℝ) * (w.1 : ℝ) := by
    exact_mod_cast heq1
  have heq2R : (N : ℝ) * ((z.2 : ℝ) - (b.2 : ℝ)) = (A : ℝ) * (vl.2 : ℝ) + (C : ℝ) * (w.2 : ℝ) := by
    exact_mod_cast heq2
  have hcomb : toReal z
      = (1 - 1 / (N : ℝ)) • toReal b + (1 / (N : ℝ)) • toReal (b + A • vl + C • w) := by
    refine Prod.ext ?_ ?_ <;>
      simp only [toReal, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
        Prod.smul_mk, Prod.mk_add_mk] <;>
      push_cast <;> field_simp
    · linear_combination heq1R
    · linear_combination heq2R
  rw [hKeq, Set.mem_preimage, hcomb]
  refine hconvex hbC hyC ?_ (by positivity) (by ring)
  have h1 : 1 / (N : ℝ) ≤ 1 := by
    rw [div_le_one hNR]
    exact_mod_cast hN
  linarith

/-- `det u (x + y) = det u x + det u y` (local copy: the library one is `private`). -/
theorem det_add_right' (u x y : ℤ × ℤ) : det u (x + y) = det u x + det u y := by
  simp only [det, Prod.fst_add, Prod.snd_add]; ring

/-- `det vl x = det x (-vl)`. -/
theorem det_vl_eq_det_negvl (vl x : ℤ × ℤ) : det vl x = det x (-vl) := by
  simp only [det, Prod.fst_neg, Prod.snd_neg]; ring

/-- **Any two chain entries see `vl` on the same side.**  Both `det vl (extChain k)` and
`det vl (extChain I)` equal `det (extChain ·) (-vl)`, whose sign is pinned to `det u' (-vl)` by
`det_extChain_negvl_sign_eq`; so their product is (strictly) positive. -/
theorem det_vl_extChain_mul_pos (d : DecompData ξ) {vl nℓ u' : ℤ × ℤ}
    (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0) (hnu : dot nℓ u' < 0)
    {k I : ℕ} (hk : k ≤ (sortedCand d nℓ u' i).length)
    (hI : I ≤ (sortedCand d nℓ u' i).length) :
    0 < det vl (extChain d nℓ vl u' i k) * det vl (extChain d nℓ vl u' i I) := by
  have hsk := det_extChain_negvl_sign_eq d hvl_prim hprim hperp i hdoth hnu hk
  have hsI := det_extChain_negvl_sign_eq d hvl_prim hprim hperp i hdoth hnu hI
  have hnk : det (extChain d nℓ vl u' i k) vl ≠ 0 :=
    det_ne_zero_of_dot_nl_neg hvl_prim hperp
      (dot_extChain_neg d hvl_prim hprim hperp i hdoth hnu hk)
  have hnI : det (extChain d nℓ vl u' i I) vl ≠ 0 :=
    det_ne_zero_of_dot_nl_neg hvl_prim hperp
      (dot_extChain_neg d hvl_prim hprim hperp i hdoth hnu hI)
  have hek : det (extChain d nℓ vl u' i k) (-vl) = - det (extChain d nℓ vl u' i k) vl :=
    det_neg_right _ _
  have heI : det (extChain d nℓ vl u' i I) (-vl) = - det (extChain d nℓ vl u' i I) vl :=
    det_neg_right _ _
  rw [det_vl_eq_det_negvl vl (extChain d nℓ vl u' i k),
    det_vl_eq_det_negvl vl (extChain d nℓ vl u' i I)]
  by_cases hpos : 0 < det u' (-vl)
  · exact mul_pos (hsk.mpr hpos) (hsI.mpr hpos)
  · have hk2 : det (extChain d nℓ vl u' i k) (-vl) < 0 := by
      have hc := fun h => hpos (hsk.mp h)
      omega
    have hI2 : det (extChain d nℓ vl u' i I) (-vl) < 0 := by
      have hc := fun h => hpos (hsI.mp h)
      omega
    exact mul_pos_of_neg_of_neg hk2 hI2

/-- **The cone-coordinate invariant of a tower level.**  Every point of `tower _ n` (`n ≤ I`)
differs from some seed point `b ∈ B` by a vector lying in the real cone `cone(vl, w)`, expressed
integrally as the two sign conditions `0 ≤ det vl (g - b) * det vl w` and `0 ≤ dot m (g - b)`
(the latter is the `w`-side inequality, since `dot m x = - det vl w * det w x`). -/
theorem cone_coords_of_mem_tower {B : Set (ℤ × ℤ)} (d : DecompData ξ) {vl nℓ u' : ℤ × ℤ}
    (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (henv : Nivat.LE2.EnvOf (↑d.Sphi : Set (ℤ × ℤ)) B)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0)
    (hadjB : ∀ n ∈ E B, ¬ (dot n vl < 0 ∧ 0 < dot n u'))
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) (hnu : dot nℓ u' < 0) (hnℓ_ne : nℓ ≠ 0)
    {I : ℕ} (hI : I ≤ (sortedCand d nℓ u' i).length) :
    ∀ n : ℕ, n ≤ I → ∀ g ∈ tower (coneRegion B vl u') (wtower d nℓ vl u' i) n,
      ∃ b ∈ B, 0 ≤ det vl (g - b) * det vl (extChain d nℓ vl u' i I) ∧
        0 ≤ dot (expNormal (extChain d nℓ vl u' i I) vl) (g - b) := by
  intro n
  induction n with
  | zero =>
    intro _ g hg
    simp only [tower] at hg
    rw [mem_coneRegion_iff] at hg
    obtain ⟨b, hb, sc, tc, rfl⟩ := hg
    have hsub : b + (sc : ℤ) • vl + (tc : ℤ) • u' - b = (sc : ℤ) • vl + (tc : ℤ) • u' := by
      abel
    have hs : (0 : ℤ) ≤ (sc : ℤ) := Int.natCast_nonneg sc
    have ht : (0 : ℤ) ≤ (tc : ℤ) := Int.natCast_nonneg tc
    refine ⟨b, hb, ?_, ?_⟩
    · rw [hsub, det_add_right', det_smul_right, det_smul_right, det_self]
      have hu'0 : (0 : ℤ) < det vl u' * det vl (extChain d nℓ vl u' i I) :=
        det_vl_extChain_mul_pos d hvl_prim hprim hperp i hdoth hnu (k := 0) (Nat.zero_le _) hI
      nlinarith
    · rw [hsub, dot_add, dot_smul_right, dot_smul_right]
      have hvl0 : 0 ≤ dot (expNormal (extChain d nℓ vl u' i I) vl) vl :=
        le_of_lt (Nivat.LaneTowerPkg.dot_expNormal_pos
          (det_ne_zero_of_dot_nl_neg hvl_prim hperp
            (dot_extChain_neg d hvl_prim hprim hperp i hdoth hnu hI)))
      have hu0 : 0 ≤ dot (expNormal (extChain d nℓ vl u' i I) vl) u' :=
        dot_m_extChain_nonneg d hvl_prim hprim hperp henv i hdoth hadjB hunimod hnu hnℓ_ne hI
          (Nat.zero_le I)
      nlinarith
  | succ k ih =>
    intro hkI g hg
    simp only [tower] at hg
    rw [Nivat.RegionSweep.mem_sweep] at hg
    obtain ⟨g', hg', tc, rfl⟩ := hg
    obtain ⟨b, hb, h1, h2⟩ := ih (by omega) g' hg'
    have hk1 : k + 1 ≤ (sortedCand d nℓ u' i).length := by omega
    have ht : (0 : ℤ) ≤ (tc : ℤ) := Int.natCast_nonneg tc
    have hsub : g' + (tc : ℤ) • wtower d nℓ vl u' i k - b
        = (g' - b) + (tc : ℤ) • extChain d nℓ vl u' i (k + 1) := by
      simp only [extChain]
      abel
    refine ⟨b, hb, ?_, ?_⟩
    · rw [hsub, det_add_right', det_smul_right]
      have hstep : (0 : ℤ) < det vl (extChain d nℓ vl u' i (k + 1)) *
          det vl (extChain d nℓ vl u' i I) :=
        det_vl_extChain_mul_pos d hvl_prim hprim hperp i hdoth hnu hk1 hI
      nlinarith
    · rw [hsub, dot_add, dot_smul_right]
      have hstep : 0 ≤ dot (expNormal (extChain d nℓ vl u' i I) vl)
          (extChain d nℓ vl u' i (k + 1)) :=
        dot_m_extChain_nonneg d hvl_prim hprim hperp henv i hdoth hadjB hunimod hnu hnℓ_ne hI
          (by omega : k + 1 ≤ I)
      nlinarith

/-- Every tower level is closed under `+ extChain _ I` at its own index `I`: at `I = 0` that is
`+ u'` (`ColleReg.tower_add_u'_mem`), at `I = J + 1` it is the very direction `tower _ (J+1)` is
swept by (`RegionSweep.add_mem_sweep`). -/
theorem tower_add_extChain_mem {B : Set (ℤ × ℤ)} (d : DecompData ξ) {vl nℓ u' : ℤ × ℤ}
    (i : Fin d.m) (I : ℕ) {x : ℤ × ℤ}
    (hx : x ∈ tower (coneRegion B vl u') (wtower d nℓ vl u' i) I) :
    x + extChain d nℓ vl u' i I ∈ tower (coneRegion B vl u') (wtower d nℓ vl u' i) I := by
  cases I with
  | zero =>
    simp only [extChain]
    exact tower_add_u'_mem (wtower d nℓ vl u' i) 0 hx
  | succ J =>
    simp only [extChain, tower] at hx ⊢
    exact add_mem_sweep hx

/-- The two-dimensional Cramer identity `det vl w • x = (- det w x) • vl + (det vl x) • w`. -/
theorem cramer_smul (vl w x : ℤ × ℤ) :
    (det vl w) • x = (- det w x) • vl + (det vl x) • w := by
  refine Prod.ext ?_ ?_ <;>
    simp only [det, Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add, smul_eq_mul,
      Prod.fst_neg, Prod.snd_neg] <;> ring

/-- **`hcut` from lattice convexity of `𝓡_I` alone.**

原文：`scratch/b3_colle2.txt:818`.  `z ∈ 𝓡_{I−1}` at a `dot m`-level at or below the whole seed
`B` already lies in `𝓡_I`.  Proof: pick the seed point `b` supplied by `cone_coords_of_mem_tower`
for the `𝓡_I`-part `g` of `z = g + t • wtower I`.  Both cone inequalities then hold for `z - b`
— the `vl`-side because `wtower I` rotates away from `vl`, the `w`-side because it is literally
the cut hypothesis (`dot m · = - det vl w * det w ·`).  Cramer's identity turns this into
`|det vl w| • (z - b) = A • vl + C • w` with `A, C ≥ 0`, and `mem_of_nsmul_cone` divides back. -/
theorem hcut_of_latticeConvex {B : Set (ℤ × ℤ)} (d : DecompData ξ) {vl nℓ u' : ℤ × ℤ}
    (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (henv : Nivat.LE2.EnvOf (↑d.Sphi : Set (ℤ × ℤ)) B)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0)
    (hadjB : ∀ n ∈ E B, ¬ (dot n vl < 0 ∧ 0 < dot n u'))
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) (hnu : dot nℓ u' < 0) (hnℓ_ne : nℓ ≠ 0)
    {I : ℕ} (hI : I ≤ (sortedCand d nℓ u' i).length)
    (hconvI : IsLatticeConvexRegion (tower (coneRegion B vl u') (wtower d nℓ vl u' i) I))
    (b₀ : ℤ)
    (hseed : ∀ b ∈ B, dot (expNormal (extChain d nℓ vl u' i I) vl) b ≤ b₀) :
    ∀ z ∈ tower (coneRegion B vl u') (wtower d nℓ vl u' i) (I + 1),
      b₀ ≤ dot (expNormal (extChain d nℓ vl u' i I) vl) z →
      z ∈ tower (coneRegion B vl u') (wtower d nℓ vl u' i) I := by
  intro z hz hzlev
  -- `dot m x = - det vl w * det w x`.
  have hdotm : ∀ x : ℤ × ℤ,
      dot (expNormal (extChain d nℓ vl u' i I) vl) x
        = - det vl (extChain d nℓ vl u' i I) * det (extChain d nℓ vl u' i I) x := by
    intro x
    rw [dot_expNormal_eq]
    have := det_skew vl (extChain d nℓ vl u' i I)
    rw [this]
    ring
  have hDne : det vl (extChain d nℓ vl u' i I) ≠ 0 := by
    have hwn : dot nℓ (extChain d nℓ vl u' i I) < 0 :=
      dot_extChain_neg d hvl_prim hprim hperp i hdoth hnu hI
    have h := det_ne_zero_of_dot_nl_neg hvl_prim hperp hwn
    have hsk := det_skew vl (extChain d nℓ vl u' i I)
    omega
  -- unpack `z = g + t • wtower I`.
  simp only [tower] at hz
  rw [Nivat.RegionSweep.mem_sweep] at hz
  obtain ⟨g, hg, t, rfl⟩ := hz
  obtain ⟨b, hbB, hcone1, hcone2⟩ :=
    cone_coords_of_mem_tower d hvl_prim hprim hperp henv i hdoth hadjB hunimod hnu hnℓ_ne hI
      I le_rfl g hg
  have ht : (0 : ℤ) ≤ (t : ℤ) := Int.natCast_nonneg t
  have hsub : g + (t : ℤ) • wtower d nℓ vl u' i I - b
      = (g - b) + (t : ℤ) • wtower d nℓ vl u' i I := by abel
  -- (1) the `vl`-side cone inequality survives the extra sweep step.
  have hstepD : 0 ≤ det vl (wtower d nℓ vl u' i I) * det vl (extChain d nℓ vl u' i I) := by
    rcases lt_or_eq_of_le hI with hlt | heq
    · have h := det_vl_extChain_mul_pos d hvl_prim hprim hperp i hdoth hnu
        (k := I + 1) (by omega) hI
      simpa [extChain] using le_of_lt h
    · rw [heq, wtower_last]
      have : det vl (-vl) = 0 := by simp only [det, Prod.fst_neg, Prod.snd_neg]; ring
      rw [this]; simp
  have hz1 : 0 ≤ det vl (g + (t : ℤ) • wtower d nℓ vl u' i I - b) *
      det vl (extChain d nℓ vl u' i I) := by
    rw [hsub, det_add_right', det_smul_right]
    nlinarith
  -- (2) the `w`-side cone inequality is exactly the cut hypothesis.
  have hz2 : 0 ≤ dot (expNormal (extChain d nℓ vl u' i I) vl)
      (g + (t : ℤ) • wtower d nℓ vl u' i I - b) := by
    have hlin : dot (expNormal (extChain d nℓ vl u' i I) vl)
        (g + (t : ℤ) • wtower d nℓ vl u' i I - b)
        = dot (expNormal (extChain d nℓ vl u' i I) vl) (g + (t : ℤ) • wtower d nℓ vl u' i I)
          - dot (expNormal (extChain d nℓ vl u' i I) vl) b := by
      simp only [dot, Prod.fst_sub, Prod.snd_sub]; ring
    rw [hlin]
    have := hseed b hbB
    omega
  -- Cramer, then divide by `|det vl w|`.
  have hbK : b ∈ tower (coneRegion B vl u') (wtower d nℓ vl u' i) I :=
    tower_monotone _ _ (Nat.zero_le I)
      (mem_coneRegion_iff.mpr ⟨b, hbB, 0, 0, by simp⟩)
  have hvlK : ∀ x ∈ tower (coneRegion B vl u') (wtower d nℓ vl u' i) I,
      x + vl ∈ tower (coneRegion B vl u') (wtower d nℓ vl u' i) I :=
    fun x hx => tower_add_vl_mem (wtower d nℓ vl u' i) I hx
  have hwK : ∀ x ∈ tower (coneRegion B vl u') (wtower d nℓ vl u' i) I,
      x + extChain d nℓ vl u' i I ∈ tower (coneRegion B vl u') (wtower d nℓ vl u' i) I :=
    fun x hx => tower_add_extChain_mem d i I hx
  have hcr := cramer_smul vl (extChain d nℓ vl u' i I)
    (g + (t : ℤ) • wtower d nℓ vl u' i I - b)
  have hAD : - det (extChain d nℓ vl u' i I) (g + (t : ℤ) • wtower d nℓ vl u' i I - b) *
      det vl (extChain d nℓ vl u' i I)
      = dot (expNormal (extChain d nℓ vl u' i I) vl)
        (g + (t : ℤ) • wtower d nℓ vl u' i I - b) := by
    rw [hdotm]; ring
  rcases lt_or_gt_of_ne hDne with hDneg | hDpos
  · -- `det vl w < 0`: clear the denominator with `- det vl w`.
    refine mem_of_nsmul_cone hconvI hbK hvlK hwK (N := - det vl (extChain d nℓ vl u' i I))
      (A := det (extChain d nℓ vl u' i I) (g + (t : ℤ) • wtower d nℓ vl u' i I - b))
      (C := - det vl (g + (t : ℤ) • wtower d nℓ vl u' i I - b))
      (by omega) (by nlinarith) (by nlinarith) ?_
    rw [neg_smul, hcr]
    module
  · -- `det vl w > 0`: clear the denominator with `det vl w`.
    refine mem_of_nsmul_cone hconvI hbK hvlK hwK (N := det vl (extChain d nℓ vl u' i I))
      (A := - det (extChain d nℓ vl u' i I) (g + (t : ℤ) • wtower d nℓ vl u' i I - b))
      (C := det vl (g + (t : ℤ) • wtower d nℓ vl u' i I - b))
      (by omega) (by nlinarith) (by nlinarith) hcr

/-! ## §2e  `hconv` from a per-layer level condition (the interface to lane-tower-hlev)

原文：`scratch/b3_colle2.txt:808`（每个 `𝓡_i` 都是 `(−ℓ, ℓ_i)`-区域）。

`RegionSweep.isLatticeConvexRegion_sweep` (`RegionSweep.lean:213`) turns lattice convexity of
layer `n` into lattice convexity of layer `n + 1` **given** `LevelInterval (tower … n)
(wtower … n)`.

⚠ **2026-09-23（第一百五十七轮，集成者改）：本节以下两条不在链上，且此处原先的理由是假的。**
原文写着「lane-tower-hlev 的 `levelInterval_tower_of_cone_closure` 要层自己的凸性 `hK`，所以
无条件形状 `∀ j < N, LevelInterval (tower … j) (wf j)` **不可生产**，凸性归纳与层条件必须交错」。
**不可生产这句为假**：`TowerHBaseMin.levelInterval_tower_wtower` 就是无条件形状的生产者，它用
纯算术算出层的 `LevelInterval`，根本不吃层的凸性（顶格 `n ≥ length` 走
`levelInterval_tower_unit`）。作者本人已口头撤回该断言，撤回没跟进文件，由 lane-tower-hlev 发现。
`tmp/wip/lane-tower-hlev-dom.lean` 本身也已移入 `tmp/wip/parked/`（原路径失效）。

链上实际走的是 `hconv_of_levelB`（下方 §2e 末尾），经 `TowerHBaseMin.isLatticeConvexRegion_tower_wtower`
/ `_pos`。本节的 `latticeConvex_tower_of_levelStep` / `hconv_of_levelStep` **保留**：它们 0 sorry、
公理干净，作为「交错归纳其实不必要」这条结论的独立复核件，但**不得**再被引用为「另一条路不可行」
的证据。按 `PROTOCOL.md §40` 记一笔——这次是反向：不是死路线伪装成活路，是活路线被文件里的
一句话判了死。

§2e 的交错版做的是一次性交错，`hR₀` 和每个扫掠方向的本原性都就地从
`henv`/`hvl_prim`/`hprim`/`hperp`/`hdoth`/`hunimod` 付掉，**不新增 binder**。 -/

/-- **The interleaved induction.**  Layer `j + 1` is swept by `wf j`, so the hypotheses range
over `j < N` and the conclusion over `n ≤ N` (`blueprint/NOTATION.md`, 「`w` vs `wtower`：永远差
一格下标」).  The level condition may consume the layer's convexity, which at that point is the
induction hypothesis. -/
theorem latticeConvex_tower_of_levelStep {R₀ : Set (ℤ × ℤ)} {wf : ℕ → ℤ × ℤ} {N : ℕ}
    (hR₀ : IsLatticeConvexRegion R₀)
    (hwprim : ∀ j, j < N → Primitive (wf j))
    (hstep : ∀ j, j < N → IsLatticeConvexRegion (tower R₀ wf j) →
      Nivat.RegionSweep.LevelInterval (tower R₀ wf j) (wf j)) :
    ∀ n, n ≤ N → IsLatticeConvexRegion (tower R₀ wf n) := by
  intro n
  induction n with
  | zero =>
      intro _
      simpa [tower] using hR₀
  | succ k ih =>
      intro hn
      have hk : k < N := Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hn
      have hK := ih (le_of_lt hk)
      simp only [tower]
      exact Nivat.RegionSweep.isLatticeConvexRegion_sweep hK (hwprim k hk) (hstep k hk hK)

/-- **`lane_towerpkg_reduce`'s `hconv` binder, from the per-layer level condition alone.**

⚠ **不在链上**（第 157 轮）：链上走的是下方 `hconv_of_levelB`。保留作独立复核件，见本节节头。

The hypothesis `hstep` is the interleaved shape (the layer's own convexity is available as its
second argument).  Note this shape is **not** forced: `TowerHBaseMin.levelInterval_tower_wtower`
produces the unconditional form without any convexity input.

Everything else is paid for out of `lane_towerpkg_reduce`'s own binders:
* `hR₀`: `EnvOf` carries `IsLatticeConvexRegion B` (Definition 3.2's first clause,
  `LatticeEdges.lean:624`) via `LaneTowerPkgEnvSymm.latticeConvex_of_envOf`
  (`EnvNegSymm.lean:190`), and `hdoth` gives both signs of `nℓ` as edge normals of `B`
  (`nl_mem_E_B_of_hdoth`, `EnvNegSymm.lean:199`); `isLatticeConvexRegion_coneRegion`
  (`TowerSeedConvex.lean:438`) does the rest.
* primitivity of `wtower … j` for every `j < len + 1`: `prim_of_mem_candSet`
  (`TowerConstruct.lean:298`) below `len`, and `wtower … len = -vl` (`TowerConstruct.lean:383`'s
  `dif_neg` branch) at the top index. -/
theorem hconv_of_levelStep {B : Set (ℤ × ℤ)} (d : DecompData ξ) {vl nℓ u' : ℤ × ℤ}
    (henv : Nivat.LE2.EnvOf (↑d.Sphi : Set (ℤ × ℤ)) B)
    (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hvl_prim : Primitive vl) (hperp : dot nℓ vl = 0)
    (hprim : Prim nℓ) (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0)
    (hstep : ∀ j, j < (sortedCand d nℓ u' i).length + 1 →
      IsLatticeConvexRegion (tower (coneRegion B vl u') (wtower d nℓ vl u' i) j) →
      Nivat.RegionSweep.LevelInterval (tower (coneRegion B vl u') (wtower d nℓ vl u' i) j)
        (wtower d nℓ vl u' i j)) :
    ∀ n : ℕ, 1 ≤ n → n ≤ (sortedCand d nℓ u' i).length + 1 →
      IsLatticeConvexRegion (tower (coneRegion B vl u') (wtower d nℓ vl u' i) n) := by
  have hnlE := Nivat.LaneTowerPkgEnvSymm.nl_mem_E_B_of_hdoth d henv hprim i hdoth
  have hR₀ : IsLatticeConvexRegion (coneRegion B vl u') :=
    Nivat.LaneTowerHlevConv.isLatticeConvexRegion_coneRegion
      (Nivat.LaneTowerPkgEnvSymm.latticeConvex_of_envOf henv) hvl_prim hprim hperp
      hnlE.1 hnlE.2 hunimod
  have hvl_neg_prim : Primitive (-vl) := by
    obtain ⟨a, b, hab⟩ := hvl_prim
    exact ⟨-a, -b, by simp only [Prod.fst_neg, Prod.snd_neg]; linear_combination hab⟩
  have hwprim : ∀ j, j < (sortedCand d nℓ u' i).length + 1 →
      Primitive (wtower d nℓ vl u' i j) := by
    intro j _
    by_cases hj : j < (sortedCand d nℓ u' i).length
    · exact prim_of_mem_candSet d hvl_prim hprim hperp i hdoth (mem_candSet_wtower hj)
    · have heq : wtower d nℓ vl u' i j = -vl := by simp only [wtower]; rw [dif_neg hj]
      rw [heq]; exact hvl_neg_prim
  exact fun n _ hn => latticeConvex_tower_of_levelStep hR₀ hwprim hstep n hn

/-- **`hconv` on the actual chain, from a seed-side level condition alone.**

This is the route actually taken (第 155 轮).  `lane-tower-hbase`'s §11
`isLatticeConvexRegion_tower_wtower` / `_pos` (`TowerHBaseMin.lean:1579`/`:1639`) run the whole
convexity induction on the real `wtower` chain — including the `-vl` tail, where the level
condition is free (`levelInterval_tower_unit`, `:1304`) — and reduce it to `LevelInterval B (wtower … n)`
on the **seed** for `n < length`.  Note this is *not* routed through
`latticeConvex_tower_of_levelStep` above: the descent (`levelInterval_of_descent`,
`TowerHBaseMin.lean:1186`) produces the tower-layer level condition without ever consuming the
layer's convexity, so the unconditional form is producible after all and no interleaving is
needed.

Everything but `hlevB` is paid for out of `lane_towerpkg_reduce`'s own binders:
* `hB`/`hR₀`: `latticeConvex_of_envOf` + `nl_mem_E_B_of_hdoth` (`EnvNegSymm.lean:190`/`:199`)
  + `isLatticeConvexRegion_coneRegion` (`TowerSeedConvex.lean:438`);
* `hstepB : ∃ a ∈ B, a + vl ∈ B`: `exists_unit_step_of_face` (`TowerSeedConvex.lean:134`) at
  the `nℓ`-face of `B`, which is nontrivial because `nℓ ∈ E B`;
* both branches of `hunimod` are covered, `= -1` by `isLatticeConvexRegion_tower_wtower` and
  `= 1` by its mirror.

原文：`scratch/b3_colle2.txt:808`. -/
theorem hconv_of_levelB {B : Set (ℤ × ℤ)} (d : DecompData ξ) {vl nℓ u' : ℤ × ℤ}
    (henv : Nivat.LE2.EnvOf (↑d.Sphi : Set (ℤ × ℤ)) B)
    (hBfin : B.Finite) (hBne : B.Nonempty)
    (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hvl_prim : Primitive vl) (hperp : dot nℓ vl = 0) (hnu : dot nℓ u' < 0)
    (hprim : Prim nℓ) (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0)
    (hadjB : ∀ nn ∈ E B, ¬ (dot nn vl < 0 ∧ 0 < dot nn u'))
    (hlevB : ∀ n, n < (sortedCand d nℓ u' i).length →
      Nivat.RegionSweep.LevelInterval B (wtower d nℓ vl u' i n)) :
    ∀ n, IsLatticeConvexRegion (tower (coneRegion B vl u') (wtower d nℓ vl u' i) n) := by
  have hnlE := Nivat.LaneTowerPkgEnvSymm.nl_mem_E_B_of_hdoth d henv hprim i hdoth
  have hB : IsLatticeConvexRegion B := Nivat.LaneTowerPkgEnvSymm.latticeConvex_of_envOf henv
  have hR₀ : IsLatticeConvexRegion (coneRegion B vl u') :=
    Nivat.LaneTowerHlevConv.isLatticeConvexRegion_coneRegion hB hvl_prim hprim hperp
      hnlE.1 hnlE.2 hunimod
  have hstepB : ∃ a ∈ B, a + vl ∈ B := by
    obtain ⟨c, hcB, -, hcvl⟩ :=
      Nivat.LaneTowerHlevConv.exists_unit_step_of_face hB hvl_prim hprim hperp hnlE.1.2
    exact ⟨c, hcB, hcvl⟩
  rcases hunimod with hE | hE
  · exact Nivat.TowerHBaseMin.isLatticeConvexRegion_tower_wtower_pos d hvl_prim hprim hperp
      henv i hdoth hadjB hE hnu hprim.ne_zero hBfin hBne hstepB hR₀ hlevB
  · exact Nivat.TowerHBaseMin.isLatticeConvexRegion_tower_wtower d hvl_prim hprim hperp
      henv i hdoth hadjB hE hnu hprim.ne_zero hBfin hBne hstepB hR₀ hlevB

/-! ## §3  The reduction: 11 conjuncts from 2 geometric residuals -/

/-- **The tower package at a fixed index `I`, with the geometric residual as one binder.**

⚠ **本条不吃 `hξ`，也不吃 `hbase₁`。** 两者在重构前只被 `exists_tower_index`
（`TowerPackage.lean:308`）那一步用到，而那一步整个上移到了装配层 `lane_towerpkg_reduce`；
剩下的 binder 表里没有任何 minimal-counterexample 假设。后果（第 193 轮记）：⭐ 几何半边
`hgoodI` 是 `hξ`-free 的，**PROTOCOL §41 的「带 `hξ` 故空真、不派证伪」在这里不适用**，
它可以直接在台架上逐点求值。

binders `d … hadj` 是 `exists_cutResidualR_of_claim46`（`RegionSteps.lean`）的
那一套，减去塔包用不到的（`hgen`、`S`、`gen`），再减去上移的 `hξ` / `hbase₁`；新增的是
`hlevB`、三条 `I`-事实（`I` / `hIM` / `hper` / `hnper`）和 `hgoodI`。

Per-quantifier correspondence with `scratch/b3_colle2.txt:806-820`:
* `Rinf = 𝓡_{I−1}` (`:808`, `:816`), `w = v⃗_{ℓ_I} = ℓ'` (`:816`), `m ⟂ w` (`:818`'s `dist` to
  `ℓ'_{𝓡_I}`), `b₀ = d_0 = 0`'s level (`:818`).
* 格凸性（`𝓡_i` "is a `(−ℓ, ℓ_i)`-region"，`:808` 的凸性半边）**不是** binder：它由
  `hconv_of_levelB`（本文件）从种子侧的 `hlevB` 导出。
* The cut statement `⋃_n 𝓡_I^n = 𝓡_{I−1}` with `d_0 = 0` (`:818`) is **not** a binder either:
  it is discharged inside the proof by `Nivat.TowerHBaseMin.hcut_tower`
  (`TowerHBaseMin.lean:637`, lane-tower-hbase) from that same convexity, with the level `b₀`
  taken to be the `dot m`-maximum over the finite seed `B` (see `hcut_support_level_false`
  (本文件), kernel counterexample, for why no smaller level works).  `hcut_of_latticeConvex`
  (本文件) is this lane's independent proof of the same step; it is kept as a cross-check but
  no longer on the critical path.
* ⛔ 第 12 条合取项 `∀ j, det (d.h j) vl * det (d.h j) w ≤ 0` **本文件零贡献**，整条由
  `hgoodI` 兑现。⚠ 它是**定向敏感**的（`vl ↦ -vl` 或 `w ↦ -w` 都把 `≤ 0` 翻成 `≥ 0`），
  所以在「链上 `vl` ＝ 原文 `v⃗_{ℓ_ι}`」证出来之前，它**双向都不许**在链侧与原文侧之间搬运
  （team-lead 第 179 轮，`NOTATION.md`）。
  ⚠ 2026-09-24（第 195 轮）：**别把这条与下面 `hgoodI` 处的反驳混为一谈。** 本行说的是
  **判据本身**定向敏感（这仍然成立）；而否掉 `I = 0` 实例的那条反驳
  （`crit_at_u'_false_bothsign`）**不吃 `hdetpos`、两个定向分支同时否**，因此**不**受
  上面这条搬运禁令的限制。两件事是独立的。 -/
theorem lane_towerpkg_reduce_at_core
    {e : ℤ × ℤ} (d : DecompData ξ)
    {B : Set (ℤ × ℤ)} {u' nℓ vl : ℤ × ℤ} {c : ℤ}
    (henv : Nivat.LE2.EnvOf (↑d.Sphi : Set (ℤ × ℤ)) B)
    (hBfin : B.Finite) (hBne : B.Nonempty)
    (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hvl_prim : Primitive vl)
    (hperp : dot nℓ vl = 0) (hnu : dot nℓ u' = -1)
    (hprim : Prim nℓ) (i : Fin d.m)
    (hdoth : dot nℓ (d.h i) = 0)
    (hadj : ∀ n ∈ E (↑d.Sphi : Set (ℤ × ℤ)),
      ¬ (dot n vl < 0 ∧ 0 < dot n u'))
    (hlevB : ∀ n, n < (sortedCand d nℓ u' i).length →
      Nivat.RegionSweep.LevelInterval B (wtower d nℓ vl u' i n))
    -- **`I` 显式化**（team-lead 第 193 轮裁决 2）。三条 `I`-事实逐字符就是
    -- `exists_tower_index`（`TowerPackage.lean:308`）结论的三个分量，在这里当 binder 收。
    (I : ℕ) (hIM : I < Mtower d nℓ u' i)
    (hper : PeriodOn (T e ξ)
      (tower (coneRegion B vl u') (wtower d nℓ vl u' i) I) (c • vl))
    (hnper : ¬ PeriodOn (T e ξ)
      (tower (coneRegion B vl u') (wtower d nℓ vl u' i) (I + 1)) (c • vl)) :
    ∃ (Rinf : Set (ℤ × ℤ)) (w : ℤ × ℤ), det vl w ≠ 0 ∧ Primitive w ∧
      ∃ (m : ℤ × ℤ), Nivat.LE2.dot m w = 0 ∧ 0 < Nivat.LE2.dot m vl ∧
      ∃ (b₀ : ℤ), Colle41.IsRegion Rinf vl w ∧
      (∃ z ∈ Rinf, Nivat.LE2.dot m z = b₀) ∧
      (∀ b : ℤ, ∃ z ∈ Rinf, Nivat.LE2.dot m z < b) ∧
      (∀ lev : ℕ → ℤ, lev 0 = b₀ →
        Nivat.Colle41.PeriodOn (T e ξ) (Nivat.L1Region.cut Rinf m lev 0) (c • vl)) ∧
      ¬ Nivat.Colle41.PeriodOn (T e ξ) Rinf (c • vl) ∧
      Nivat.LE2.dot nℓ w < 0 ∧ (∃ top : ℤ, ∀ z ∈ Rinf, Nivat.LE2.dot nℓ z ≤ top) ∧
      -- ⭐ 第 12 条合取：**`w` 的身份**。`set w := extChain … I`（体内）本来就有这条
      -- `hw_def`，原先被 `∃ w` 吞掉了，这里把它导出来。
      -- **定向无关**：不论 Claim 4.10 最终把端点钉在 `0` 还是 `len`，这条都成立且都必需。
      w = extChain d nℓ vl u' i I := by
  have hnu' : dot nℓ u' < 0 := by omega
  have hnℓ_ne : nℓ ≠ 0 := hprim.ne_zero
  have hadjB : ∀ n ∈ E B, ¬ (dot n vl < 0 ∧ 0 < dot n u') := hadjB_of_hadj d henv hadj
  have hconvAll : ∀ n : ℕ, n ≤ (sortedCand d nℓ u' i).length + 1 →
      IsLatticeConvexRegion (tower (coneRegion B vl u') (wtower d nℓ vl u' i) n) :=
    fun n _ => hconv_of_levelB d henv hBfin hBne hunimod hvl_prim hperp hnu' hprim i hdoth
      hadjB hlevB n
  set wt := wtower d nℓ vl u' i with hwt_def
  set len := (sortedCand d nℓ u' i).length with hlen_def
  have hu'_prim : Primitive u' := Nivat.LE2.prim_iff_primitive.mp (prim_u'_of_hunimod hunimod)
  have hvl_neg_prim : Primitive (-vl) := by
    obtain ⟨a, b, hab⟩ := hvl_prim
    exact ⟨-a, -b, by simp only [Prod.fst_neg, Prod.snd_neg]; linear_combination hab⟩
  have hw_prim_all : ∀ k, Primitive (wt k) := by
    intro k
    by_cases hk : k < len
    · exact prim_of_mem_candSet d hvl_prim hprim hperp i hdoth (mem_candSet_wtower hk)
    · have heq : wt k = -vl := by simp only [hwt_def, wtower]; rw [dif_neg hk]
      rw [heq]; exact hvl_neg_prim
  have hIlen : I ≤ len := by simp only [Mtower] at hIM; omega
  set w := extChain d nℓ vl u' i I with hw_def
  set m := expNormal w vl with hm_def
  set Rinf := tower (coneRegion B vl u') wt (I + 1) with hRinf_def
  -- `dot nℓ w < 0` (conjunct 10).
  have hwneg : dot nℓ w < 0 :=
    dot_extChain_neg d hvl_prim hprim hperp i hdoth hnu' hIlen
  -- `det vl w ≠ 0` (conjunct 1).
  have hwvl_ne : det w vl ≠ 0 := det_ne_zero_of_dot_nl_neg hvl_prim hperp hwneg
  have hdet : det vl w ≠ 0 := by
    intro h0
    apply hwvl_ne
    have hskew := det_skew w vl
    omega
  -- `Primitive w` (conjunct 2).
  have hw_prim : Primitive w := by
    cases hI : I with
    | zero => rw [hw_def, hI]; exact hu'_prim
    | succ J => rw [hw_def, hI]; exact hw_prim_all J
  -- `dot m w = 0`, `0 < dot m vl` (conjuncts 3, 4).
  have hmw : dot m w = 0 := dot_expNormal_u'
  have hmvl : 0 < dot m vl := Nivat.LaneTowerPkg.dot_expNormal_pos hwvl_ne
  -- a base point of the tower.
  obtain ⟨b, hb⟩ := hBne
  have hb_cone : b ∈ coneRegion B vl u' := by
    rw [mem_coneRegion_iff]; exact ⟨b, hb, 0, 0, by simp⟩
  have hb_I : b ∈ tower (coneRegion B vl u') wt I := tower_monotone _ _ (Nat.zero_le I) hb_cone
  have hb_Rinf : b ∈ Rinf := tower_subset_succ _ _ I hb_I
  -- `hunb` (conjunct 8): the sweep direction lowers `dot m` without bound.
  have hstep_neg : dot m (wt I) < 0 :=
    dot_m_step_neg d hvl_prim hprim hperp henv i hdoth hadjB hunimod hnu' hnℓ_ne hIlen
  have hunb : ∀ bb : ℤ, ∃ z ∈ Rinf, dot m z < bb := by
    intro bb
    exact hunb_of_sweep_neg hb_I hstep_neg bb
  -- `htop` (conjunct 11).
  have htop : ∃ top : ℤ, ∀ z ∈ Rinf, dot nℓ z ≤ top := by
    refine Nivat.HsuppTowerBase.dot_le_of_mem_tower_bounded hBfin (le_of_eq hperp) (by omega) wt (I + 1) ?_
    intro k hk
    by_cases hklen : k < len
    · exact le_of_lt (dot_of_mem_candSet d hvl_prim hprim hperp i hdoth (mem_candSet_wtower hklen))
    · have heq : wt k = -vl := by simp only [hwt_def, wtower]; rw [dif_neg hklen]
      rw [heq, dot_neg_right_loc, hperp]
      norm_num
  -- `hR` (conjunct 5): convexity is the residual, both rays are discharged here.
  have hR : Colle41.IsRegion Rinf vl w := by
    refine ⟨hconvAll (I + 1) (by omega), ⟨b, rayIn_tower_vl wt (I + 1) hb_Rinf⟩, ⟨b, ?_⟩⟩
    exact rayIn_tower_extChain d i I hb_cone
  -- `b₀` := the `dot m`-maximum over the finite seed `B`; attained, so `h0` is free.
  classical
  have hFne : (hBfin.toFinset).Nonempty := ⟨b, hBfin.mem_toFinset.mpr hb⟩
  obtain ⟨bmax, hbmaxF, hbmax_ge⟩ := hBfin.toFinset.exists_max_image (fun x => dot m x) hFne
  have hbmax_B : bmax ∈ B := hBfin.mem_toFinset.mp hbmaxF
  have hbmax_cone : bmax ∈ coneRegion B vl u' := by
    rw [mem_coneRegion_iff]; exact ⟨bmax, hbmax_B, 0, 0, by simp⟩
  have hbmax_I : bmax ∈ tower (coneRegion B vl u') wt I :=
    tower_monotone _ _ (Nat.zero_le I) hbmax_cone
  have hseed : ∀ b' ∈ B, dot m b' ≤ dot m bmax :=
    fun b' hb' => hbmax_ge b' (hBfin.mem_toFinset.mpr hb')
  -- `h0` (conjunct 6) and `hbase` (conjunct 7).
  refine ⟨Rinf, w, hdet, hw_prim, m, hmw, hmvl, dot m bmax, hR,
    ⟨bmax, tower_subset_succ _ _ I hbmax_I, rfl⟩, hunb, ?_, hnper, hwneg, htop, hw_def⟩
  · intro lev hlev0
    refine PeriodOn.mono ?_ hper
    intro z hz
    -- the `:818` cut identity, taken from `lane-tower-hbase`'s `TowerHBaseMin.hcut_tower`
    -- (`TowerHBaseMin.lean:637`); its `hseed` is the *maximum* reading, matching `hbmax_ge`.
    have hstepAll : ∀ J : ℕ, J ≤ len →
        dot (expNormal (extChain d nℓ vl u' i J) vl) (wtower d nℓ vl u' i J) < 0 :=
      fun J hJ => dot_m_step_neg d hvl_prim hprim hperp henv i hdoth hadjB hunimod hnu' hnℓ_ne hJ
    exact Nivat.TowerHBaseMin.hcut_tower d hBfin ⟨b, hb⟩ hvl_prim hprim hperp i hdoth hnu hconvAll
      hstepAll I hIlen (dot m bmax) hseed z hz.1 (by rw [← hlev0]; exact hz.2)

/-- **`lane_towerpkg_reduce_at`（旧签名，逐字符不变）＝ core ＋ `hgoodI`。**
core 导出的 `w = extChain d nℓ vl u' i I` 把 `hgoodI` 的 `extChain …` 改写成 `w`，
第 12 条合取由此兑现。本条对几何内容仍是零贡献。 -/
theorem lane_towerpkg_reduce_at
    {e : ℤ × ℤ} (d : DecompData ξ)
    {B : Set (ℤ × ℤ)} {u' nℓ vl : ℤ × ℤ} {c : ℤ}
    (henv : Nivat.LE2.EnvOf (↑d.Sphi : Set (ℤ × ℤ)) B)
    (hBfin : B.Finite) (hBne : B.Nonempty)
    (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hvl_prim : Primitive vl)
    (hperp : dot nℓ vl = 0) (hnu : dot nℓ u' = -1)
    (hprim : Prim nℓ) (i : Fin d.m)
    (hdoth : dot nℓ (d.h i) = 0)
    (hadj : ∀ n ∈ E (↑d.Sphi : Set (ℤ × ℤ)),
      ¬ (dot n vl < 0 ∧ 0 < dot n u'))
    (hlevB : ∀ n, n < (sortedCand d nℓ u' i).length →
      Nivat.RegionSweep.LevelInterval B (wtower d nℓ vl u' i n))
    (I : ℕ) (hIM : I < Mtower d nℓ u' i)
    (hper : PeriodOn (T e ξ)
      (tower (coneRegion B vl u') (wtower d nℓ vl u' i) I) (c • vl))
    (hnper : ¬ PeriodOn (T e ξ)
      (tower (coneRegion B vl u') (wtower d nℓ vl u' i) (I + 1)) (c • vl))
    -- ⛔ **洞 3 的几何半边，最小形式**：只对**这一个** `I` 要求，不带任何 `∀ I`。
    --
    -- ── 2026-09-24（第 195 轮，lane-towerpkg，team-lead 裁决 1 授权；**只加注释**）──
    --
    -- **(1) `I = 0` 实例空真。** `extChain d nℓ vl u' i 0 = u'` 是 `def` 展开
    --   （`TowerConstruct.lean:906`）。在本声明**已有**的 binder
    --   （`hvl_prim` / `hperp` / `hnu` / `hprim` / `i` / `hdoth` / `hadj`）
    --   ＋ `3 ≤ d.m`（`Nivat.OrderThree.three_le_m`，`OrderThree.lean:292`）之下，
    --   `hgoodI` 取 `I := 0` 蕴含 `False`：见 lane-tower-hbase 的
    --   `Nivat.LaneTowerHbaseIdxDict.crit_at_u'_false_bothsign`
    --   （`tmp/wip/lane-tower-hbase-idxdict.lean`）。**两个定向分支都否、不吃 `hdetpos`**，
    --   故不受 `NOTATION.md` 第 179 轮「在『链上 `vl` ＝ 原文 `v⃗_{ℓ_ι}`』证出来之前，
    --   带符号的 `det vl w` 结论双向都不许搬」那条禁令的限制。
    --   机制（**转引，本 lane 未复核内核**）：`hadj` 把 `u'` 钉在 `det (wgen j) u' ≤ 0`，
    --   判据要的是 `0 ≤ det (wgen j) w`，两边夹成 `= 0` ⟹ 任意两个 `wgen` 平行 ⟹ 撞 `d.h_dir`。
    --
    -- **(2) 本声明本身没错。** 第 193 轮的收据仍成立（`check1.sh` EXIT=0、
    --   `#print axioms` 只有 `[propext, Classical.choice, Quot.sound]`，见文件末的 `#print axioms`）。
    --   作废的是「它在 `I = 0` 上可用」这个**预期**，不是这条定理。
    --
    -- **(3) ⛔ 整条判据路线已于第 195 轮关门，本声明不再有消费者。**
    --   ⚠ 关门的理由**不是**「内核证明判据在链上为假」——team-lead 第 195 轮就这句
    --   自行订正过一次。正确形式是三条腿，按 `PROTOCOL.md §50` 逐条标来源口径：
    --   **L1（亲读**，team-lead 与 lane-tower-hbase 各自独立亲读，本 lane 亦当轮亲读**）**：
    --       `Nivat.LaneTowerHlevFanOrder.hstrict_iff_det_gen_native`（`FanOrderCriterion.lean`）
    --       是 **`↔`**，不是单向充分条件；`hstrict_of_det_gen_onsite` 就是它的 `.mpr`。
    --       它的 binder 表（`hvlp hwp hperp hdetpos hnu hwneg hmw hmvl ha ha_min ha_end`）
    --       逐条是 `exists_cutResidualR_of_claim46`（`RegionSteps.lean`）现场的原生 binder，
    --       且现场有 `hdetpos` ⟹ 等价在链上实例处适用。**⟹ 否掉判据就是否掉 `hstrict`，
    --       `hstrict` 没有第二条来路**（lane-tower-hbase 第 195 轮撤回了他原先「判据只是充分
    --       路线」的射程保留，并给出 `hstrict_false_at_u'` / `w_ne_u'_of_hstrict`，公理全白）。
    --   **L2（转引**，本 lane 未复核 hbase 的内核**）**：判据在 `extChain … I` 处
    --       **对每一档 `0 ≤ I < len` 都可证为假**（不只是 `I = 0`）：
    --       `Nivat.LaneTowerHbaseIdxDict.crit_false_below_top`
    --       （`tmp/wip/lane-tower-hbase-idxdict.lean`，公理全白）。
    --       它**不吃** `hlast`，吃的是 `henv` / `hunimod` / `hdetpos` / `hnu` ＋ `I < K ≤ len`；
    --       要取出 `I = 0` 这一档还须 `0 < len`，这条主仓已付：
    --       `Nivat.OrderThree.three_le_m`（`OrderThree.lean:292`）
    --       ⟹ `Nivat.TowerGoodW.sortedCand_length_pos`（`TowerGoodW.lean:300`）。
    --       上面 (1) 的 `crit_at_u'_false_bothsign` 是**并列**的第二条入口（只覆盖 `I = 0`，
    --       但不吃 `henv` / `hunimod` / `hdetpos`），两条不是强弱关系。
    --       在 `extChain … len` 处判据**无条件成立**
    --       （`tmp/wip/lane-towerpkg-critprobe.lean` 的 `hlast_good_discharge`，本 lane 的收据，
    --       EXIT=0、公理全白）。两端合起来即
    --       `Nivat.LaneTowerHbaseIdxDict.crit_iff_eq_top`：**判据 ⟺ `I = len`**
    --       （`hlast` 在那条里是形参，由本 lane 的收据无条件供给）。
    --       ⟹ **判据路线死于「它要的那一档，链上可证不是原文给的那一档」**（哪一档见 L3）。
    --   ⚠ **这不蕴含 `hroom` 不可证——别把 L2 读成替下一格判死。** 同为**转引**
    --       （lane-tower-hbase 的 `crit_iff_cone` / `cone_fst_free` / `cone_not_necessary`，
    --       `tmp/wip/lane-tower-hbase-conecrit.lean`，公理全白，本 lane 未复核内核）：
    --       判据 ⟺ `Nivat.RecessionCone.room_of_cone`（`ConeRecession.lean`）的锥条件 `hcone`，
    --       且锥条件第一分量在 `hmw` ＋ `hmvl` 下白送 ⟹ 全部内容在第二分量；
    --       而 `nℓ = -dir vl` ⟹ `dot nℓ x = -det vl x` ⟹ 第二分量**就是半平面条件**
    --       `dot nℓ (b-a) ≤ 0`（`w` 在里面不出现；team-lead 第 196 轮当轮亲算，**转引**）。
    --       该条件对 **`∀ q ∈ Rinf` 版**的 `hroom` 是**充要**的——必要性取 `dot nℓ` 的最大点，
    --       用消费者 `exists_cutResidualR_of_claim46`（`RegionSteps.lean`）现场的 `htop`——
    --       但 `hroom` 现场只需要 gap 行上**那一个** `P`。
    --       ⟹ 债全部落在 **`q`-收窄**这一格，不在判据这一格。
    --   **L3（亲读 ＋ 裁决）**：生产者（本文件 `lane_towerpkg_package_wid`）只导出
    --       `∃ I ≤ len, w = extChain … I`，**链上不钉 `I` 的值**——它来自
    --       `ColleReg.exists_tower_index`（`TowerPackage.lean:308`，team-lead 当轮亲读）
    --       的**断裂点存在量词**。⟹ 要走通判据路线，必须先证 `I = len`。
    --       而**原文侧 `I` 是钉死的，钉在另一端**：Claim 4.10
    --       （`scratch/b3_colle2.txt:876-878`）给 `I_paper = ι−1`；按索引字典
    --       `I_paper = ι−1 − I_lean`（上端锚 `tower … 0 = coneRegion B vl u'` 是 defeq，
    --       本文件开头的字典段）即 **`I_lean = 0`** ＝ 沿后继序走**零**步 ＝ **近**端。
    --       〔证据级：**原文 ＋ 裁决，未形式化**。Claim 4.10 在链上没有对应定理，
    --       按 `PROTOCOL.md §50` **不得**当内核事实引用；原文读法来自 cone 的逐字转写。〕
    --       ⟹ 两种情形都堵死：Claim 4.10 为真则 `I_lean = 0`，而判据要 `I_lean = len`
    --       且 `0 < len` 已证（见 L2）⟹ 两者可证互斥 ⟹ 判据为假；
    --       Claim 4.10 为假也仍须另证 `I = len`，而那条线（`hper_len`）已因
    --       `hbase₁` 脱落判红。
    --
    -- ⚠ 这三条不是同一种证据，**别把 (3) 整体当成内核事实引用**。特别是：
    --   `lane_towerpkg_package_wid` 至今**不承诺 `I` 等于几**（消费者 `RegionSteps.lean`
    --   的注释同此口径），所以「判据在链上为假」**不成立**；L2 否掉的是 `0 ≤ I < len`
    --   **全档**，而 `I = len` 那一档判据恰好成立——缺口正是生产者不钉 `I`。
    -- ⚠ **Claim 4.10 因此回到桌面**：team-lead 第 195 轮撤回了它此前的「作废」，
    --   它现在是这一格**唯一**的决定性问题。本 binder 的命运随它。
    -- ⚠ 顺带堵掉一条看似的出路：「让 `w` 管前十一条、另取 `w★ = extChain … len` 管判据」
    --   **做不到**。`hmw` / `Primitive w` / `hwneg` 三条已经把 `w` 唯一钉死
    --   （lane-tower-hbase 的 `w_unique_of_side_conditions`，`tmp/wip/lane-tower-hbase-idxdict.lean`，
    --   公理全白，**转引**）⟹ `w★` 若满足侧条件就**等于** `w`，否则根本喂不进那条 `↔`。
    --
    -- 无消费者实测（2026-09-24 当轮）：`lane_towerpkg_reduce_at` 的裸名全树 grep 在 `Nivat/`
    --   内只命中本条声明头、本段上方的 docstring、以及文件末的 `#print axioms`，无调用点。
    (hgoodI : ∀ j : Fin d.m,
      det (d.h j) vl * det (d.h j) (extChain d nℓ vl u' i I) ≤ 0) :
    ∃ (Rinf : Set (ℤ × ℤ)) (w : ℤ × ℤ), det vl w ≠ 0 ∧ Primitive w ∧
      ∃ (m : ℤ × ℤ), Nivat.LE2.dot m w = 0 ∧ 0 < Nivat.LE2.dot m vl ∧
      ∃ (b₀ : ℤ), Colle41.IsRegion Rinf vl w ∧
      (∃ z ∈ Rinf, Nivat.LE2.dot m z = b₀) ∧
      (∀ b : ℤ, ∃ z ∈ Rinf, Nivat.LE2.dot m z < b) ∧
      (∀ lev : ℕ → ℤ, lev 0 = b₀ →
        Nivat.Colle41.PeriodOn (T e ξ) (Nivat.L1Region.cut Rinf m lev 0) (c • vl)) ∧
      ¬ Nivat.Colle41.PeriodOn (T e ξ) Rinf (c • vl) ∧
      Nivat.LE2.dot nℓ w < 0 ∧ (∃ top : ℤ, ∀ z ∈ Rinf, Nivat.LE2.dot nℓ z ≤ top) ∧
      (∀ j : Fin d.m, det (d.h j) vl * det (d.h j) w ≤ 0) := by
  obtain ⟨Rinf, w, h1, h2, m, h3, h4, b₀, h5, h6, h7, h8, h9, h10, h11, hwid⟩ :=
    lane_towerpkg_reduce_at_core d henv hBfin hBne hunimod hvl_prim hperp hnu hprim i hdoth
      hadj hlevB I hIM hper hnper
  exact ⟨Rinf, w, h1, h2, m, h3, h4, b₀, h5, h6, h7, h8, h9, h10, h11, by
    rw [hwid]; exact hgoodI⟩

/-- **装配层的 `w` 身份导出。** 结论 = `lane_towerpkg_reduce` 原来那十一条合取
（即 `exists_cutResidualR_of_claim46`（`RegionSteps.lean`）那条类型标注 `obtain` 逐字符）＋ 第 12 条

```
∃ I, I ≤ (sortedCand d nℓ u' i).length ∧ w = extChain d nℓ vl u' i I
```

binder 表与本文件 `lane_towerpkg_reduce` **逐字符相同**，
一条不多一条不少：`hIlen_eq` / `hlast_good` 都不吃。

`I ≤ len` 的来源：`exists_tower_index` 给 `hIM : I < Mtower d nℓ u' i`，
而 `Mtower d nℓ u' i = (sortedCand d nℓ u' i).length + 1` 是 `def` 展开
（`TowerConstruct.lean:389`）。 -/
theorem lane_towerpkg_reduce_wid
    {e : ℤ × ℤ} (hξ : IsMinimalCounterexample ξ) (d : DecompData ξ)
    {B : Set (ℤ × ℤ)} {u' nℓ vl : ℤ × ℤ} {c : ℤ}
    (henv : Nivat.LE2.EnvOf (↑d.Sphi : Set (ℤ × ℤ)) B)
    (hBfin : B.Finite) (hBne : B.Nonempty)
    (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hvl_prim : Primitive vl) (hc : 0 < c)
    (hperp : dot nℓ vl = 0) (hnu : dot nℓ u' = -1)
    (hbase₁ : PeriodOn (T e ξ) (coneRegion B vl u') (c • vl))
    (hprim : Prim nℓ) (i : Fin d.m)
    (hdoth : dot nℓ (d.h i) = 0)
    (hadj : ∀ n ∈ E (↑d.Sphi : Set (ℤ × ℤ)),
      ¬ (dot n vl < 0 ∧ 0 < dot n u'))
    (hlevB : ∀ n, n < (sortedCand d nℓ u' i).length →
      Nivat.RegionSweep.LevelInterval B (wtower d nℓ vl u' i n)) :
    ∃ (Rinf : Set (ℤ × ℤ)) (w : ℤ × ℤ), det vl w ≠ 0 ∧ Primitive w ∧
      ∃ (m : ℤ × ℤ), Nivat.LE2.dot m w = 0 ∧ 0 < Nivat.LE2.dot m vl ∧
      ∃ (b₀ : ℤ), Colle41.IsRegion Rinf vl w ∧
      (∃ z ∈ Rinf, Nivat.LE2.dot m z = b₀) ∧
      (∀ b : ℤ, ∃ z ∈ Rinf, Nivat.LE2.dot m z < b) ∧
      (∀ lev : ℕ → ℤ, lev 0 = b₀ →
        Nivat.Colle41.PeriodOn (T e ξ) (Nivat.L1Region.cut Rinf m lev 0) (c • vl)) ∧
      ¬ Nivat.Colle41.PeriodOn (T e ξ) Rinf (c • vl) ∧
      Nivat.LE2.dot nℓ w < 0 ∧ (∃ top : ℤ, ∀ z ∈ Rinf, Nivat.LE2.dot nℓ z ≤ top) ∧
      (∃ I : ℕ, I ≤ (sortedCand d nℓ u' i).length ∧ w = extChain d nℓ vl u' i I) := by
  have hu'_prim : Primitive u' := Nivat.LE2.prim_iff_primitive.mp (prim_u'_of_hunimod hunimod)
  have hvl_neg_prim : Primitive (-vl) := by
    obtain ⟨a, b, hab⟩ := hvl_prim
    exact ⟨-a, -b, by simp only [Prod.fst_neg, Prod.snd_neg]; linear_combination hab⟩
  have hw_prim_all : ∀ k, Primitive (wtower d nℓ vl u' i k) := by
    intro k
    by_cases hk : k < (sortedCand d nℓ u' i).length
    · exact prim_of_mem_candSet d hvl_prim hprim hperp i hdoth (mem_candSet_wtower hk)
    · have heq : wtower d nℓ vl u' i k = -vl := by simp only [wtower]; rw [dif_neg hk]
      rw [heq]; exact hvl_neg_prim
  have h_last : wtower d nℓ vl u' i (Mtower d nℓ u' i - 1) = -vl := by
    have hMeq : Mtower d nℓ u' i - 1 = (sortedCand d nℓ u' i).length := by
      simp only [Mtower]; omega
    rw [hMeq]; exact wtower_last d nℓ vl u' i
  have hM_pos : Mtower d nℓ u' i > 0 := by simp only [Mtower]; omega
  have hcvl_ne : c • vl ≠ 0 := smul_ne_zero (by omega) hvl_prim.ne_zero
  have htopHP : ∀ R w' c'', w' ≠ 0 → dot w' (c • vl) = 0 →
      {z | c'' ≤ dot w' z} ⊆ R → ¬ PeriodOn (T e ξ) R (c • vl) := by
    intro R w' c'' hw'0 hw'cvl hsub
    exact Nivat.HalfPlaneNotPeriodOn.not_periodOn_of_halfPlane_subset hξ e hw'0 hcvl_ne hw'cvl
      hsub
  obtain ⟨I, hIM, hper, hnper⟩ :=
    exists_tower_index hBfin hBne hvl_prim hu'_prim hunimod (wtower d nℓ vl u' i) hw_prim_all
      hM_pos h_last hbase₁ htopHP
  obtain ⟨Rinf, w, h1, h2, m, h3, h4, b₀, h5, h6, h7, h8, h9, h10, h11, hwid⟩ :=
    lane_towerpkg_reduce_at_core d henv hBfin hBne hunimod hvl_prim hperp hnu hprim i hdoth
      hadj hlevB I hIM hper hnper
  refine ⟨Rinf, w, h1, h2, m, h3, h4, b₀, h5, h6, h7, h8, h9, h10, h11, I, ?_, hwid⟩
  simp only [Mtower] at hIM
  omega

/-- **The tower package, reduced to the single residual `hconv`.**

Binders `hξ … hadj` are exactly `exists_cutResidualR_of_claim46`'s
(`RegionSteps.lean`), minus the ones the tower package does not use (`hgen`, `S`,
`gen`); `hconv` is the only added binder.

Per-quantifier correspondence with `scratch/b3_colle2.txt:806-820`:
* `Rinf = 𝓡_{I−1}` (`:808`, `:816`), `w = v⃗_{ℓ_I} = ℓ'` (`:816`), `m ⟂ w` (`:818`'s `dist` to
  `ℓ'_{𝓡_I}`), `b₀ = d_0 = 0`'s level (`:818`).
* `hconv` — `𝓡_i` "is a `(−ℓ, ℓ_i)`-region" (`:808`), lattice-convexity half.
* The cut statement `⋃_n 𝓡_I^n = 𝓡_{I−1}` with `d_0 = 0` (`:818`) is **not** a binder: it is
  discharged inside the proof by `Nivat.TowerHBaseMin.hcut_tower` (`TowerHBaseMin.lean:637`,
  lane-tower-hbase) from the same `hconv`, with the level `b₀` taken to be the `dot m`-maximum
  over the finite seed `B` (see `hcut_support_level_false` (`:367`) for why no smaller level
  works).  `hcut_of_latticeConvex` (`:615`) below is this lane's independent proof of the same
  step; it is kept as a cross-check but no longer on the critical path. -/
theorem lane_towerpkg_reduce
    {e : ℤ × ℤ} (hξ : IsMinimalCounterexample ξ) (d : DecompData ξ)
    {B : Set (ℤ × ℤ)} {u' nℓ vl : ℤ × ℤ} {c : ℤ}
    (henv : Nivat.LE2.EnvOf (↑d.Sphi : Set (ℤ × ℤ)) B)
    (hBfin : B.Finite) (hBne : B.Nonempty)
    (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hvl_prim : Primitive vl) (hc : 0 < c)
    (hperp : dot nℓ vl = 0) (hnu : dot nℓ u' = -1)
    (hbase₁ : PeriodOn (T e ξ) (coneRegion B vl u') (c • vl))
    (hprim : Prim nℓ) (i : Fin d.m)
    (hdoth : dot nℓ (d.h i) = 0)
    (hadj : ∀ n ∈ E (↑d.Sphi : Set (ℤ × ℤ)),
      ¬ (dot n vl < 0 ∧ 0 < dot n u'))
    -- the only residual (owner: lane-tower-hlev, `levelInterval_wtower`).  It is a statement
    -- about the **seed** `B` only: no tower, no convexity, no sign.  Everything tower-side is
    -- discharged by `hconv_of_levelB` (§2e) out of `lane-tower-hbase`'s
    -- `isLatticeConvexRegion_tower_wtower` (`TowerHBaseMin.lean:1579`) and its mirror.
    (hlevB : ∀ n, n < (sortedCand d nℓ u' i).length →
      Nivat.RegionSweep.LevelInterval B (wtower d nℓ vl u' i n)) :
    ∃ (Rinf : Set (ℤ × ℤ)) (w : ℤ × ℤ), det vl w ≠ 0 ∧ Primitive w ∧
      ∃ (m : ℤ × ℤ), Nivat.LE2.dot m w = 0 ∧ 0 < Nivat.LE2.dot m vl ∧
      ∃ (b₀ : ℤ), Colle41.IsRegion Rinf vl w ∧
      (∃ z ∈ Rinf, Nivat.LE2.dot m z = b₀) ∧
      (∀ b : ℤ, ∃ z ∈ Rinf, Nivat.LE2.dot m z < b) ∧
      (∀ lev : ℕ → ℤ, lev 0 = b₀ →
        Nivat.Colle41.PeriodOn (T e ξ) (Nivat.L1Region.cut Rinf m lev 0) (c • vl)) ∧
      ¬ Nivat.Colle41.PeriodOn (T e ξ) Rinf (c • vl) ∧
      Nivat.LE2.dot nℓ w < 0 ∧ (∃ top : ℤ, ∀ z ∈ Rinf, Nivat.LE2.dot nℓ z ≤ top) := by
  -- 2026-09-24（第 193 轮，lane-towerpkg）：**实现替换，签名逐字符未动。**
  -- 原来内联在这里的那一百行塔上装配已经外提成 `lane_towerpkg_reduce_at_core`（本文件），
  -- 本条现在是 `lane_towerpkg_reduce_wid`（本文件）的投影：丢掉第 12 条 `w` 身份合取。
  -- 结论与改动前逐字符相同，所以下游（`lane_towerpkg_package`、`RegionSteps`）一字不改。
  obtain ⟨Rinf, w, h1, h2, mm, h3, h4, b₀, h5, h6, h7, h8, h9, h10, h11, _⟩ :=
    lane_towerpkg_reduce_wid hξ d henv hBfin hBne hunimod hvl_prim hc hperp hnu hbase₁ hprim i
      hdoth hadj hlevB
  exact ⟨Rinf, w, h1, h2, mm, h3, h4, b₀, h5, h6, h7, h8, h9, h10, h11⟩

/-- **The consumer statement, character for character** (the type-ascribed `obtain` in
`exists_cutResidualR_of_claim46`, `RegionSteps.lean`), with
**no residual**: the last binder of `lane_towerpkg_reduce` (`hlevB`, the seed-side level
condition) is `LaneTowerHlevGen.levelInterval_wtower` (`TowerGenBridge.lean:231`, lane-tower-hlev),
whose `∀ k` is unbounded, so the `n < length` bound is simply dropped. -/
theorem lane_towerpkg_package
    {e : ℤ × ℤ} (hξ : IsMinimalCounterexample ξ) (d : DecompDataZ ξ)
    {B : Set (ℤ × ℤ)} {u' nℓ vl : ℤ × ℤ} {c : ℤ}
    (henv : Nivat.LE2.EnvOf (↑d.toDecompData.Sphi : Set (ℤ × ℤ)) B)
    (hBfin : B.Finite) (hBne : B.Nonempty)
    (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hvl_prim : Primitive vl) (hc : 0 < c)
    (hperp : Nivat.LE2.dot nℓ vl = 0) (hnu : Nivat.LE2.dot nℓ u' = -1)
    (hbase₁ : Nivat.Colle41.PeriodOn (T e ξ)
      (Nivat.ConeRegion.coneRegion B vl u') (c • vl))
    (hprim : Nivat.LE2.Prim nℓ) (i : Fin d.toDecompData.m)
    (hdoth : Nivat.LE2.dot nℓ (d.toDecompData.h i) = 0)
    (hadj : ∀ n ∈ Nivat.LE2.E (↑d.toDecompData.Sphi : Set (ℤ × ℤ)),
      ¬ (Nivat.LE2.dot n vl < 0 ∧ 0 < Nivat.LE2.dot n u')) :
    ∃ (Rinf : Set (ℤ × ℤ)) (w : ℤ × ℤ), det vl w ≠ 0 ∧ Primitive w ∧
      ∃ (m : ℤ × ℤ), Nivat.LE2.dot m w = 0 ∧ 0 < Nivat.LE2.dot m vl ∧
      ∃ (b₀ : ℤ), Colle41.IsRegion Rinf vl w ∧
      (∃ z ∈ Rinf, Nivat.LE2.dot m z = b₀) ∧
      (∀ b : ℤ, ∃ z ∈ Rinf, Nivat.LE2.dot m z < b) ∧
      (∀ lev : ℕ → ℤ, lev 0 = b₀ →
        Nivat.Colle41.PeriodOn (T e ξ) (Nivat.L1Region.cut Rinf m lev 0) (c • vl)) ∧
      ¬ Nivat.Colle41.PeriodOn (T e ξ) Rinf (c • vl) ∧
      Nivat.LE2.dot nℓ w < 0 ∧ (∃ top : ℤ, ∀ z ∈ Rinf, Nivat.LE2.dot nℓ z ≤ top) :=
  lane_towerpkg_reduce hξ d.toDecompData henv hBfin hBne hunimod hvl_prim hc hperp hnu hbase₁
    hprim i hdoth hadj
    (fun n _ => Nivat.LaneTowerHlevGen.levelInterval_wtower d.toDecompData henv hvl_prim hprim
      hperp i hdoth u' n)

/-- **包层的 `w` 身份导出**（`DecompDataZ`，binder 表与本文件 `lane_towerpkg_package`
**逐字符相同**）。这是打算交给集成者接进
`exists_cutResidualR_of_claim46`（`RegionSteps.lean`）的那一条。

⚠ 本条**不吃** `hdetpos`：`w` 的身份与 `nℓ` 的定向无关，所以接线补丁 v2 §2b 那条新插的
`hdetpos` 在本条上**不需要**。（v2 的 `hdetpos` 是为几何判据插的，端点定了再说。） -/
theorem lane_towerpkg_package_wid
    {e : ℤ × ℤ} (hξ : IsMinimalCounterexample ξ) (d : DecompDataZ ξ)
    {B : Set (ℤ × ℤ)} {u' nℓ vl : ℤ × ℤ} {c : ℤ}
    (henv : Nivat.LE2.EnvOf (↑d.toDecompData.Sphi : Set (ℤ × ℤ)) B)
    (hBfin : B.Finite) (hBne : B.Nonempty)
    (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hvl_prim : Primitive vl) (hc : 0 < c)
    (hperp : Nivat.LE2.dot nℓ vl = 0) (hnu : Nivat.LE2.dot nℓ u' = -1)
    (hbase₁ : Nivat.Colle41.PeriodOn (T e ξ)
      (Nivat.ConeRegion.coneRegion B vl u') (c • vl))
    (hprim : Nivat.LE2.Prim nℓ) (i : Fin d.toDecompData.m)
    (hdoth : Nivat.LE2.dot nℓ (d.toDecompData.h i) = 0)
    (hadj : ∀ n ∈ Nivat.LE2.E (↑d.toDecompData.Sphi : Set (ℤ × ℤ)),
      ¬ (Nivat.LE2.dot n vl < 0 ∧ 0 < Nivat.LE2.dot n u')) :
    ∃ (Rinf : Set (ℤ × ℤ)) (w : ℤ × ℤ), det vl w ≠ 0 ∧ Primitive w ∧
      ∃ (m : ℤ × ℤ), Nivat.LE2.dot m w = 0 ∧ 0 < Nivat.LE2.dot m vl ∧
      ∃ (b₀ : ℤ), Colle41.IsRegion Rinf vl w ∧
      (∃ z ∈ Rinf, Nivat.LE2.dot m z = b₀) ∧
      (∀ b : ℤ, ∃ z ∈ Rinf, Nivat.LE2.dot m z < b) ∧
      (∀ lev : ℕ → ℤ, lev 0 = b₀ →
        Nivat.Colle41.PeriodOn (T e ξ) (Nivat.L1Region.cut Rinf m lev 0) (c • vl)) ∧
      ¬ Nivat.Colle41.PeriodOn (T e ξ) Rinf (c • vl) ∧
      Nivat.LE2.dot nℓ w < 0 ∧ (∃ top : ℤ, ∀ z ∈ Rinf, Nivat.LE2.dot nℓ z ≤ top) ∧
      (∃ I : ℕ, I ≤ (sortedCand d.toDecompData nℓ u' i).length ∧
        w = extChain d.toDecompData nℓ vl u' i I) :=
  lane_towerpkg_reduce_wid hξ d.toDecompData henv hBfin hBne hunimod hvl_prim hc hperp hnu
    hbase₁ hprim i hdoth hadj
    (fun n _ => Nivat.LaneTowerHlevGen.levelInterval_wtower d.toDecompData henv hvl_prim hprim
      hperp i hdoth u' n)

/-- **向后兼容收据**：第 12 条合取是**追加**，消费者
（`exists_cutResidualR_of_claim46`（`RegionSteps.lean`）的 `obtain`，逐字符）现有的十一条模式仍然合法。
⟹ 接线时 `RegionSteps` 那个 `obtain` 只需在模式尾部加一个名字，其余一字不改。 -/
theorem lane_towerpkg_package_wid_projects_to_old
    {e : ℤ × ℤ} (hξ : IsMinimalCounterexample ξ) (d : DecompDataZ ξ)
    {B : Set (ℤ × ℤ)} {u' nℓ vl : ℤ × ℤ} {c : ℤ}
    (henv : Nivat.LE2.EnvOf (↑d.toDecompData.Sphi : Set (ℤ × ℤ)) B)
    (hBfin : B.Finite) (hBne : B.Nonempty)
    (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hvl_prim : Primitive vl) (hc : 0 < c)
    (hperp : Nivat.LE2.dot nℓ vl = 0) (hnu : Nivat.LE2.dot nℓ u' = -1)
    (hbase₁ : Nivat.Colle41.PeriodOn (T e ξ)
      (Nivat.ConeRegion.coneRegion B vl u') (c • vl))
    (hprim : Nivat.LE2.Prim nℓ) (i : Fin d.toDecompData.m)
    (hdoth : Nivat.LE2.dot nℓ (d.toDecompData.h i) = 0)
    (hadj : ∀ n ∈ Nivat.LE2.E (↑d.toDecompData.Sphi : Set (ℤ × ℤ)),
      ¬ (Nivat.LE2.dot n vl < 0 ∧ 0 < Nivat.LE2.dot n u')) :
    ∃ (Rinf : Set (ℤ × ℤ)) (w : ℤ × ℤ), det vl w ≠ 0 ∧ Primitive w ∧
      ∃ (m : ℤ × ℤ), Nivat.LE2.dot m w = 0 ∧ 0 < Nivat.LE2.dot m vl ∧
      ∃ (b₀ : ℤ), Colle41.IsRegion Rinf vl w ∧
      (∃ z ∈ Rinf, Nivat.LE2.dot m z = b₀) ∧
      (∀ b : ℤ, ∃ z ∈ Rinf, Nivat.LE2.dot m z < b) ∧
      (∀ lev : ℕ → ℤ, lev 0 = b₀ →
        Nivat.Colle41.PeriodOn (T e ξ) (Nivat.L1Region.cut Rinf m lev 0) (c • vl)) ∧
      ¬ Nivat.Colle41.PeriodOn (T e ξ) Rinf (c • vl) ∧
      Nivat.LE2.dot nℓ w < 0 ∧ (∃ top : ℤ, ∀ z ∈ Rinf, Nivat.LE2.dot nℓ z ≤ top) := by
  obtain ⟨Rinf, w, h1, h2, m, h3, h4, b₀, h5, h6, h7, h8, h9, h10, h11, _⟩ :=
    lane_towerpkg_package_wid hξ d henv hBfin hBne hunimod hvl_prim hc hperp hnu hbase₁ hprim i
      hdoth hadj
  exact ⟨Rinf, w, h1, h2, m, h3, h4, b₀, h5, h6, h7, h8, h9, h10, h11⟩

end Nivat.LaneTowerPkgMain

#print axioms Nivat.LaneTowerPkgMain.dot_expNormal_eq
#print axioms Nivat.LaneTowerPkgMain.det_extChain_negvl_sign_eq
#print axioms Nivat.LaneTowerPkgMain.det_extChain_step_sign
#print axioms Nivat.LaneTowerPkgMain.dot_m_step_neg
#print axioms Nivat.LaneTowerPkgMain.rayIn_tower_vl
#print axioms Nivat.LaneTowerPkgMain.rayIn_tower_extChain
#print axioms Nivat.LaneTowerPkgMain.dot_m_extChain_nonneg
#print axioms Nivat.LaneTowerPkgMain.dot_ge_of_mem_tower
#print axioms Nivat.LaneTowerPkgMain.hcut_support_level_false
#print axioms Nivat.LaneTowerPkgMain.add_nsmul_mem_of_closed
#print axioms Nivat.LaneTowerPkgMain.mem_of_nsmul_cone
#print axioms Nivat.LaneTowerPkgMain.det_vl_extChain_mul_pos
#print axioms Nivat.LaneTowerPkgMain.cone_coords_of_mem_tower
#print axioms Nivat.LaneTowerPkgMain.tower_add_extChain_mem
#print axioms Nivat.LaneTowerPkgMain.cramer_smul
#print axioms Nivat.LaneTowerPkgMain.hcut_of_latticeConvex
#print axioms Nivat.LaneTowerPkgMain.latticeConvex_tower_of_levelStep
#print axioms Nivat.LaneTowerPkgMain.hconv_of_levelStep
#print axioms Nivat.LaneTowerPkgMain.hconv_of_levelB
#print axioms Nivat.LaneTowerPkgMain.lane_towerpkg_reduce
#print axioms Nivat.LaneTowerPkgMain.lane_towerpkg_package
#print axioms Nivat.LaneTowerPkgMain.lane_towerpkg_reduce_at_core
#print axioms Nivat.LaneTowerPkgMain.lane_towerpkg_reduce_at
#print axioms Nivat.LaneTowerPkgMain.lane_towerpkg_reduce_wid
#print axioms Nivat.LaneTowerPkgMain.lane_towerpkg_package_wid
#print axioms Nivat.LaneTowerPkgMain.lane_towerpkg_package_wid_projects_to_old
