/-
Copyright (c) 2026 Nivat Formalization Contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lane-tower
-/
import Nivat.External.Colle.TowerBuild
import Nivat.External.Colle.TowerIndex
import Nivat.External.Colle.TowerClimb
import Nivat.External.Colle.ConeRegion
import Nivat.External.Colle.L1Region
import Nivat.External.Colle.RegionCutGE
import Nivat.External.Colle.Claim47Core
import Nivat.External.Colle.HalfPlaneTowerTop
import Nivat.External.Colle.PolyChain
import Nivat.External.Colle.CutRecConvex
import Nivat.Defs.Config

open Nivat Nivat.LE2 Nivat.Colle Nivat.Colle41 Nivat.L1Region Nivat.HalfPlaneTowerTop

/-!
# Tower package pieces, salvaged from `tmp/wip/TowerPackage2.lean` (lane-tower's earlier draft)

原文：b3_colle2.txt:806-820

Six 0-sorry lemmas salvaged for reuse by `tmp/wip/tower_hbase.lean`'s assembly of the
`exists_cutResidualR_of_claim46` tower package (`RegionSteps.lean:1738-1755`). The full
assembly theorem `exists_tower_package` from the source draft is NOT included here — it had
sorries (arbitrary `b_base` instead of the `m`-minimiser of `B`) and is being rebuilt fresh.

## Main declarations

* `tower_add_vl_mem`, `tower_add_u'_mem` — tower closure under the cone generators
* `tower_top_contains_halfPlane` — the tower top contains a half-plane (`:810`)
* `exists_tower_index` — the index where periodicity breaks (`:814`)
* `dot_m_next_neg` — orientation-free descent step (team-lead ruling 2026-09-22)
* `dot_nl_le_of_mem_tower` — the tower stays bounded above against `nℓ ⊥ vl`
-/

set_option autoImplicit false

namespace Nivat.ColleReg

open Nivat Nivat.Colle41 Nivat.LE2 Nivat.ConeRegion Nivat.TowerIndex

variable {ξ : Config ℤ} {e : ℤ × ℤ}

theorem tower_add_vl_mem {B : Set (ℤ × ℤ)} {vl u' : ℤ × ℤ} (w : ℕ → ℤ × ℤ) (n : ℕ)
    {z : ℤ × ℤ} (hz : z ∈ tower (coneRegion B vl u') w n) :
    z + vl ∈ tower (coneRegion B vl u') w n := by
  induction n generalizing z with
  | zero =>
    simp only [tower] at hz ⊢
    exact ConeRegion.add_vl_mem hz
  | succ k ih =>
    simp only [tower] at hz ⊢
    obtain ⟨g, hg, t, rfl⟩ := hz
    refine ⟨g + vl, ih hg, t, ?_⟩
    module

/-- **Tower closure under adding u'** (from the cone base).

原文：b3_colle2.txt:780, :808

The base `coneRegion B vl u'` includes `ℕ·u'` (`:780`), and tower sweeps preserve
or enlarge this property. -/
theorem tower_add_u'_mem {B : Set (ℤ × ℤ)} {vl u' : ℤ × ℤ} (w : ℕ → ℤ × ℤ) (n : ℕ)
    {z : ℤ × ℤ} (hz : z ∈ tower (coneRegion B vl u') w n) :
    z + u' ∈ tower (coneRegion B vl u') w n := by
  induction n generalizing z with
  | zero =>
    simp only [tower] at hz ⊢
    exact ConeRegion.add_u'_mem hz
  | succ k ih =>
    simp only [tower] at hz ⊢
    obtain ⟨g, hg, t, rfl⟩ := hz
    refine ⟨g + u', ih hg, t, ?_⟩
    module

/-- **Step 1: The tower top contains a half-plane** (`:810`).

原文：b3_colle2.txt:810 — "Note that $(T^u η)|_{\mathcal{H}(\boldsymbol{\ell}_{\iota-m})}$
does not have a period..."

**Key insight from `:810`**: `ℓ_{ι-m} = −ℓ` (the final tower step sweeps by `−vl`).

After sweeping through edge directions cyclically, the final step adds `−vl` itself.
Since `coneRegion B vl u'` already contains `+vl` and `+u'`, adding `−vl` gives
closure under `ℤ•vl`, making the tower top contain the half-plane `{z | dot nℓ z ≤ c}`
for any threshold `c`.

Quantifiers:
- `wtower : ℕ → ℤ × ℤ` — edge direction sequence
- `M : ℕ` — number of steps
- `h_last : wtower (M - 1) = -vl` — **final step is −vl** (`:810` ℓ_{ι-m} = −ℓ)
- `nℓ : ℤ × ℤ` — the half-plane normal (perpendicular to `vl`, with `dot nℓ u' = -1`)

Conclusion: `∃ b c, {z | dot nℓ z ≤ c} ⊆ tower R₀ wtower M`

This is `halfPlane_subset_of_zsmul_vl` applied after verifying that the tower top
has `ℤ•vl` closure via the final `−vl` step. -/
theorem tower_top_contains_halfPlane
    {B : Set (ℤ × ℤ)} (hBfin : B.Finite) (hBne : B.Nonempty)
    {vl u' : ℤ × ℤ} (hvl : Primitive vl) (hu' : Primitive u')
    (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (wtower : ℕ → ℤ × ℤ) (hw_prim : ∀ i, Primitive (wtower i))
    {M : ℕ} (hM : M > 0) (h_last : wtower (M - 1) = -vl) :
    ∃ (nℓ : ℤ × ℤ) (b : ℤ × ℤ) (c : ℤ), nℓ ≠ 0 ∧ dot nℓ vl = 0 ∧
      {z | dot nℓ z ≤ c} ⊆ tower (coneRegion B vl u') wtower M := by
  -- Construct nℓ perpendicular to vl with dot nℓ u' = -1
  -- Use perp vl, which satisfies dot (perp vl) vl = 0
  -- and dot (perp vl) u' = det vl u' = -det u' vl
  set nℓ_cand := perp vl with hnℓ_def

  -- Check the sign of dot nℓ_cand u'
  -- dot (perp vl) u' = det vl u' = -det u' vl
  have hdot_cand : dot nℓ_cand u' = -det u' vl := by
    rw [hnℓ_def, dot_perp]
    -- det vl u' = -det u' vl
    simp only [det]
    ring

  by_cases hsign : det u' vl = 1
  · -- det u' vl = 1, so dot nℓ_cand u' = -1, use nℓ_cand directly
    set nℓ := nℓ_cand with hnℓ'
    obtain ⟨b, hb⟩ := hBne
    refine ⟨nℓ, b, dot nℓ b, ?hne, ?hperp, ?hsubset⟩

    case hne =>
      -- nℓ = perp vl ≠ 0 when vl ≠ 0
      simp only [nℓ, nℓ_cand, perp]
      intro h
      have hvl_zero : vl = 0 := by
        ext
        · simpa using congr_arg Prod.snd h
        · simpa using congr_arg Prod.fst h
      exact hvl.ne_zero hvl_zero

    case hperp =>
      -- dot nℓ vl = dot (perp vl) vl = 0
      rw [hnℓ']
      unfold nℓ_cand
      rw [dot_perp, det_self]

    case hsubset =>
      -- Apply halfPlane_subset_of_zsmul_vl to tower M
      -- Need: B ⊆ tower M, tower M has ℤ•vl and +u' closure
      set R := tower (coneRegion B vl u') wtower M

      -- We have: nℓ = perp vl, dot nℓ u' = -1 (from hdot_cand and hsign)
      have hnu : dot nℓ u' = -1 := by
        rw [hnℓ']
        unfold nℓ_cand
        rw [hdot_cand, hsign]

      -- B ⊆ coneRegion B vl u' ⊆ tower 0 ⊆ tower M
      have hBR : B ⊆ R := by
        intro z hz
        have : z ∈ coneRegion B vl u' := mem_coneRegion_iff.mpr ⟨z, hz, 0, 0, by simp⟩
        clear * - this
        change z ∈ tower (coneRegion B vl u') wtower M
        induction M with
        | zero => exact this
        | succ m ih =>
          unfold tower
          exact ⟨z, ih, 0, by simp⟩

      -- Tower is closed under +vl
      have hvl_mem : ∀ z ∈ R, z + vl ∈ R := fun z hz => tower_add_vl_mem wtower M hz

      -- Tower is closed under -vl
      have hvl'_mem : ∀ z ∈ R, z - vl ∈ R := by
        intro z hz
        have hM_succ : ∃ k, M = k + 1 := by
          obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt hM
          use k
          omega
        obtain ⟨k, hk⟩ := hM_succ
        subst hk
        have hwk : wtower k = -vl := h_last
        obtain ⟨g, hg, t, hz_eq⟩ := hz
        refine ⟨g, hg, t + 1, ?_⟩
        rw [hz_eq, hwk]
        push_cast
        module

      -- Tower is closed under +u'
      have hu'_mem : ∀ z ∈ R, z + u' ∈ R := fun z hz => tower_add_u'_mem wtower M hz

      -- nℓ is perpendicular to vl
      have hperp : dot nℓ vl = 0 := by
        simp only [nℓ, hnℓ', hnℓ_def]
        rw [dot_perp]
        exact det_self vl

      exact Nivat.HalfPlaneTowerTop.halfPlane_subset_of_zsmul_vl hb hBR hvl_mem hvl'_mem hu'_mem hunimod hperp hnu

  · -- det u' vl = -1, so dot nℓ_cand u' = 1, negate to get -1
    have hdet_neg : det u' vl = -1 := by
      cases hunimod with
      | inl h => contradiction
      | inr h => exact h
    set nℓ := -nℓ_cand with hnℓ'
    obtain ⟨b, hb⟩ := hBne
    refine ⟨nℓ, b, dot nℓ b, ?hne, ?hperp, ?hsubset⟩

    case hne =>
      simp only [nℓ, nℓ_cand, perp, neg_eq_zero]
      intro h
      have hvl_zero : vl = 0 := by
        ext
        · have : -vl.1 = (-(-vl.2, vl.1) : ℤ × ℤ).2 := rfl
          rw [h] at this
          simp at this; exact this
        · have : -(-vl.2) = (-(-vl.2, vl.1) : ℤ × ℤ).1 := rfl
          rw [h] at this
          simp at this; exact this
      exact hvl.ne_zero hvl_zero

    case hperp =>
      rw [hnℓ', dot_neg_left]
      unfold nℓ_cand
      rw [dot_perp, det_self]
      ring

    case hsubset =>
      -- Apply halfPlane_subset_of_zsmul_vl to tower M
      -- Similar to the first case, but nℓ = -perp vl
      set R := tower (coneRegion B vl u') wtower M

      -- We have: nℓ = -perp vl, so dot nℓ u' = -dot (perp vl) u' = -(-det u' vl) = det u' vl = -1
      have hnu : dot nℓ u' = -1 := by
        rw [hnℓ', dot_neg_left]
        unfold nℓ_cand
        rw [hdot_cand, hdet_neg]
        ring

      -- B ⊆ coneRegion B vl u' ⊆ tower 0 ⊆ tower M
      have hBR : B ⊆ R := by
        intro z hz
        have : z ∈ coneRegion B vl u' := mem_coneRegion_iff.mpr ⟨z, hz, 0, 0, by simp⟩
        clear * - this
        change z ∈ tower (coneRegion B vl u') wtower M
        induction M with
        | zero => exact this
        | succ m ih =>
          unfold tower
          exact ⟨z, ih, 0, by simp⟩

      -- Tower is closed under +vl
      have hvl_mem : ∀ z ∈ R, z + vl ∈ R := fun z hz => tower_add_vl_mem wtower M hz

      -- Tower is closed under -vl
      have hvl'_mem : ∀ z ∈ R, z - vl ∈ R := by
        intro z hz
        have hM_succ : ∃ k, M = k + 1 := by
          obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt hM
          use k
          omega
        obtain ⟨k, hk⟩ := hM_succ
        subst hk
        have hwk : wtower k = -vl := h_last
        obtain ⟨g, hg, t, hz_eq⟩ := hz
        refine ⟨g, hg, t + 1, ?_⟩
        rw [hz_eq, hwk]
        push_cast
        module

      -- Tower is closed under +u'
      have hu'_mem : ∀ z ∈ R, z + u' ∈ R := fun z hz => tower_add_u'_mem wtower M hz

      -- nℓ is perpendicular to vl
      have hperp : dot nℓ vl = 0 := by
        simp only [nℓ, hnℓ']
        rw [dot_neg_left, hnℓ_def]
        simp [dot_perp]

      exact Nivat.HalfPlaneTowerTop.halfPlane_subset_of_zsmul_vl hb hBR hvl_mem hvl'_mem hu'_mem hunimod hperp hnu

/-- **Step 2: The index where periodicity breaks** (`:814`).

原文：b3_colle2.txt:812-814 — "Hence ... we may consider the smallest integer
`ι−m+1 ≤ I ≤ ι−1` such that `(T^u η)|_{𝓡_I}` is periodic of period `h`."

Given:
- Base `R₀ = coneRegion B vl u'` is periodic (`:804`, Claim 4.6)
- Tower top `tower R₀ w M` contains a half-plane and is NOT periodic (`:810` + `htop`)

Then there exists an index `I < M` where `tower R₀ w I` is periodic but
`tower R₀ w (I+1)` is not.

Quantifiers:
- All from `tower_top_contains_halfPlane`
- `c : ℤ` — the period multiple (`:806`, `h = c • vl`)
- `hbase₁ : PeriodOn (T e ξ) (coneRegion B vl u') (c • vl)` — base periodicity (`:804`)
- `htop` — the half-plane non-periodicity axiom
- Conclusion: `∃ I < M, PeriodOn (tower I) ∧ ¬ PeriodOn (tower (I+1))`

**Integration note**: Once `HalfPlaneNotPeriodOn` is in the build, replace `htop` parameter with
`hξ : IsMinimalCounterexample ξ` and instantiate `htop` via:
```
htop := λ R w' c'' hw' hu' hwu' hR =>
  HalfPlaneNotPeriodOn.not_periodOn_of_halfPlane_subset hξ e hw' hu' hwu' hR
```
where `hu'` is `c • vl ≠ 0` (needs proof from `hvl : Primitive vl` and `c ≠ 0`).

This is `TowerIndex.exists_last_periodOn_finite` applied after establishing that the
tower top is not periodic via `htop`. -/
theorem exists_tower_index
    {B : Set (ℤ × ℤ)} (hBfin : B.Finite) (hBne : B.Nonempty)
    {vl u' : ℤ × ℤ} (hvl : Primitive vl) (hu' : Primitive u')
    (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (w : ℕ → ℤ × ℤ) (hw : ∀ i, Primitive (w i))
    {M : ℕ} (hM : M > 0) (h_last : w (M - 1) = -vl)
    {c : ℤ}
    (hbase₁ : PeriodOn (T e ξ) (coneRegion B vl u') (c • vl))
    (htop : ∀ R w' c'', w' ≠ 0 → dot w' (c • vl) = 0 →
      {z | c'' ≤ dot w' z} ⊆ R → ¬ PeriodOn (T e ξ) R (c • vl)) :
    ∃ I : ℕ, I < M ∧
      PeriodOn (T e ξ) (tower (coneRegion B vl u') w I) (c • vl) ∧
      ¬ PeriodOn (T e ξ) (tower (coneRegion B vl u') w (I + 1)) (c • vl) := by
  -- Apply tower_top_contains_halfPlane to get the half-plane witness
  obtain ⟨nℓ, b, c', hnℓ_ne, hnℓ_perp, hsubset⟩ :=
    tower_top_contains_halfPlane hBfin hBne hvl hu' hunimod w hw hM h_last
  -- Flip the direction: use -nℓ to get {z | -c' ≤ dot (-nℓ) z} ⊆ tower M
  set w₀ := -nℓ with hw₀_def
  have hw₀_ne : w₀ ≠ 0 := by simp [w₀]; exact hnℓ_ne
  have hw₀_perp : dot w₀ vl = 0 := by
    simp only [w₀, dot_neg_left, hnℓ_perp, neg_zero]
  have hsubset' : {z | -c' ≤ dot w₀ z} ⊆ tower (coneRegion B vl u') w M := by
    intro z hz
    simp only [Set.mem_setOf_eq, w₀, dot_neg_left] at hz
    have : dot nℓ z ≤ c' := by linarith
    exact hsubset this
  -- hw₀_perp gives us `dot w₀ vl = 0`, so `dot w₀ (c • vl) = 0`
  have hw₀_cvl : dot w₀ (c • vl) = 0 := by
    calc dot w₀ (c • vl)
        = (c : ℤ) * dot w₀ vl := by
          simp only [dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
      _ = (c : ℤ) * 0 := by rw [hw₀_perp]
      _ = 0 := by ring
  -- The tower top is not periodic (by htop)
  have hM : ¬ PeriodOn (T e ξ) (tower (coneRegion B vl u') w M) (c • vl) :=
    htop (tower (coneRegion B vl u') w M) w₀ (-c') hw₀_ne hw₀_cvl hsubset'
  -- Apply exists_last_periodOn_finite
  exact exists_last_periodOn_finite hbase₁ hM

/-- **Orientation-free descent step** (team-lead ruling 2026-09-22, `:766`/`:810`).

If `m` is perpendicular to `w` with `dot m vl > 0`, and the next tower edge direction `w'`
sits on the correct side of `w` relative to `-vl` (encoded by `hside`, an orientation-free
determinant-sign condition that holds regardless of which of `±perp w` was chosen as `m`),
then `dot m w' < 0`. This lets `hunb` be discharged identically in both sign branches of
`exists_tower_package`, without needing a case split on which of `m_cand`/`-m_cand` is `m`.

Proof sketch: `dot m w = 0` forces `m = lam • perp w` for some `lam : ℤ` (via
`eq_zsmul_of_det_eq_zero` applied to the primitive vector `perp w`). Then
`dot m vl = lam * det w vl` and `dot m w' = lam * det w w'` (via `dot_perp`). The hypothesis
`hside` rewrites to `det w w' * det w vl < 0`, i.e. `det w w'` and `det w vl` have opposite
signs; combined with `dot m vl = lam * det w vl > 0` (so `lam`, `det w vl` have the same
sign), we get `lam` and `det w w'` have opposite signs, hence `dot m w' = lam * det w w' < 0`. -/
theorem dot_m_next_neg {m w w' vl : ℤ × ℤ} (hw_prim : Primitive w)
    (hmw : dot m w = 0) (hmvl : 0 < dot m vl)
    (hside : 0 < det w w' * det w (-vl)) : dot m w' < 0 := by
  have hdpm : det (perp w) m = 0 := by
    have heq : det (perp w) m = - dot m w := by
      obtain ⟨w1, w2⟩ := w
      obtain ⟨m1, m2⟩ := m
      simp only [perp, det, dot]
      ring
    rw [heq, hmw]; ring
  obtain ⟨lam, hlam⟩ := eq_zsmul_of_det_eq_zero (primitive_perp hw_prim) hdpm
  have hmvl_eq : dot m vl = lam * det w vl := by
    rw [hlam]
    have hexp : dot ((lam : ℤ) • perp w) vl = lam * dot (perp w) vl := by
      obtain ⟨n1, n2⟩ := perp w
      obtain ⟨v1, v2⟩ := vl
      simp only [dot, Prod.smul_mk, smul_eq_mul]
      ring
    rw [hexp, dot_perp]
  have hmw'_eq : dot m w' = lam * det w w' := by
    rw [hlam]
    have hexp : dot ((lam : ℤ) • perp w) w' = lam * dot (perp w) w' := by
      obtain ⟨n1, n2⟩ := perp w
      obtain ⟨p1, p2⟩ := w'
      simp only [dot, Prod.smul_mk, smul_eq_mul]
      ring
    rw [hexp, dot_perp]
  have hdneg : det w (-vl) = - det w vl := by
    obtain ⟨v1, v2⟩ := vl
    simp only [det, Prod.neg_mk]
    ring
  rw [hdneg] at hside
  have hprod : det w w' * det w vl < 0 := by nlinarith
  rw [hmvl_eq] at hmvl
  rw [hmw'_eq]
  rcases mul_pos_iff.mp hmvl with ⟨hlam_pos, hd_pos⟩ | ⟨hlam_neg, hd_neg⟩
  · have hw'_neg : det w w' < 0 := by
      rcases mul_neg_iff.mp hprod with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · linarith
      · exact h1
    exact mul_neg_of_pos_of_neg hlam_pos hw'_neg
  · have hw'_pos : 0 < det w w' := by
      rcases mul_neg_iff.mp hprod with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact h1
      · linarith
    exact mul_neg_of_neg_of_pos hlam_neg hw'_pos

/-- **The tower stays bounded above against a fixed normal `nℓ` orthogonal to `vl`.**

原文：`:386-400` — a `(−ℓ,ℓ')`-region has two semi-infinite edges; the `−ℓ` edge is exactly
the upper bound in the `nℓ`-direction (team-lead ruling 2026-09-22). `nℓ ⊥ vl` (`hperp`) means
sweeping by `vl` never changes the `nℓ`-value, so only `u'` and the tower directions `wtower i`
(all strictly `nℓ`-decreasing, `hnu`/`hwlow`) can lower it below the maximum already attained
on the finite seed `B`. -/
theorem dot_nl_le_of_mem_tower {B : Set (ℤ × ℤ)} (hBfin : B.Finite) (hBne : B.Nonempty)
    {vl u' nℓ : ℤ × ℤ} (hperp : dot nℓ vl = 0) (hnu : dot nℓ u' = -1)
    (wtower : ℕ → ℤ × ℤ) (hwlow : ∀ i, dot nℓ (wtower i) < 0) (n : ℕ) :
    ∃ top : ℤ, ∀ z ∈ tower (coneRegion B vl u') wtower n, dot nℓ z ≤ top := by
  obtain ⟨top, htop⟩ : ∃ top : ℤ, ∀ b ∈ B, dot nℓ b ≤ top := by
    have hfin : (dot nℓ '' B).Finite := hBfin.image _
    obtain ⟨top, htop⟩ := hfin.bddAbove
    exact ⟨top, fun b hb => htop ⟨b, hb, rfl⟩⟩
  refine ⟨top, ?_⟩
  induction n with
  | zero =>
    intro z hz
    simp only [tower] at hz
    rw [mem_coneRegion_iff] at hz
    obtain ⟨b, hb, s, t, rfl⟩ := hz
    have heq : dot nℓ (b + (s : ℤ) • vl + (t : ℤ) • u')
        = dot nℓ b + (s : ℤ) * dot nℓ vl + (t : ℤ) * dot nℓ u' := by
      rw [dot_add, dot_add]
      congr 2
      · cases nℓ; cases vl; simp only [dot, Prod.smul_mk, smul_eq_mul]; ring
      · cases nℓ; cases u'; simp only [dot, Prod.smul_mk, smul_eq_mul]; ring
    rw [heq, hperp, hnu]
    have ht : (0 : ℤ) ≤ (t : ℤ) := by positivity
    nlinarith [htop b hb]
  | succ k ih =>
    intro z hz
    simp only [tower] at hz
    rw [Nivat.RegionSweep.mem_sweep] at hz
    obtain ⟨g, hg, t, rfl⟩ := hz
    have hgle := ih g hg
    have heq : dot nℓ (g + (t : ℤ) • wtower k) = dot nℓ g + (t : ℤ) * dot nℓ (wtower k) := by
      rw [dot_add]
      congr 1
      cases nℓ; cases (wtower k); simp only [dot, Prod.smul_mk, smul_eq_mul]; ring
    rw [heq]
    have ht : (0 : ℤ) ≤ (t : ℤ) := by positivity
    nlinarith [hwlow k, hgle]


end Nivat.ColleReg

#print axioms Nivat.ColleReg.tower_add_vl_mem
#print axioms Nivat.ColleReg.tower_add_u'_mem
#print axioms Nivat.ColleReg.tower_top_contains_halfPlane
#print axioms Nivat.ColleReg.exists_tower_index
#print axioms Nivat.ColleReg.dot_m_next_neg
#print axioms Nivat.ColleReg.dot_nl_le_of_mem_tower
