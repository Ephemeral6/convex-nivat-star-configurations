/-
Copyright (c) 2026 Nivat Formalization Contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lane-tower-hlev
-/
import Nivat.External.Colle.TowerBuild
import Nivat.External.Colle.ConeRegion

/-! # lane-tower-hlev: `hlev` replaced by a one-step determinant condition

原文：b3_colle2.txt:806-820（塔），:808（`𝓡_{i−1} := {g + t·v⃗_{ℓ_i} : g ∈ 𝓡_i, t ∈ ℤ₊}`）。

## What this file delivers

`Nivat.ColleReg.isRegion_tower` (`TowerBuild.lean:91`) needs
`hlev : ∀ i, LevelInterval (tower R₀ w i) (w i)`, and `LevelInterval` in the unrestricted form is
false (`tmp/wip/lane-towerpkg-hlev-counterexample.lean:42`).  This file proves that `LevelInterval`
is *implied* by a much cheaper condition, purely about the two ray directions the seed is already
closed under:

* `levelInterval_of_step_det_one` / `_neg_one`: if `C` is closed under `+ v` for a **single**
  vector `v` with `det w v = ±1`, then `LevelInterval C w` — no hypothesis on `C` beyond that
  closure.  (Reason: from any `a ∈ C` the points `a + N•v` walk the level functional `det w ·`
  through *every* integer step, so no level between two attained ones can be missed.)
* `levelInterval_of_two_steps`: the useful packaging — `C` closed under `+ v₁` and `+ v₂`
  (for the tower: `v₁ = vl`, `v₂ = u'`, both free because `𝓡_I = coneRegion B vl u'`), and
  `∃ a b : ℕ, a * det w v₁ + b * det w v₂ = ±1`.
* `isRegion_tower_of_steps`: the drop-in replacement for `isRegion_tower`, with `hlev` replaced by
  that arithmetic side condition on the two seed ray directions.

## How `lane-towerpkg` discharges the new hypothesis

In the consumer's scope (`RegionSteps.lean:1711-1730`) `hunimod : det u' vl = 1 ∨ det u' vl = -1`
makes `(vl, u')` a ℤ-basis, so every tower direction is `w = p•vl + q•u'` with
`det w vl = q * det u' vl` and `det w u' = -p * det u' vl`.  `hnu : dot nℓ u' = -1` and
`hperp : dot nℓ vl = 0` turn `TowerConstruct.dot_wgen_neg`'s `dot nℓ (w i) < 0` into `q > 0`.
So, writing `A := det (w i) vl` and `Bq := det (w i) u'`:

* `q = 1` (i.e. `|A| = 1`) → take `a = 1, b = 0`;
* `|p| = 1` (i.e. `|Bq| = 1`) → take `a = 0, b = 1`;
* `p ≥ 1` → `A` and `Bq` have **opposite** signs and are coprime (primitivity of `w i` in the
  basis), so Bézout has a ℕ-solution;
* `p = 0` → `q = 1` by primitivity, first case.

The one residual case is `p ≤ -2` together with `q ≥ 2`, and that case is **genuinely false**, not
merely unproved: `sweep_cone_not_isLatticeConvexRegion` at the bottom of this file is a kernel
witness that the very first tower level already fails `IsRegion` there, with a `w` that passes
every local filter (`Primitive w`, `dot nℓ w < 0`, `det u' vl = -1`).  So `H` cannot be dropped;
`lane-towerpkg` has to show the actual `wtower` directions avoid `p ≤ -2 ∧ q ≥ 2`.
-/

set_option autoImplicit false

namespace Nivat.LaneTowerHlev

open Nivat Nivat.RegionSweep Nivat.Colle41 Nivat.ColleReg

/-! ## §1  Walking a translation-closed set -/

/-- Closure under `+ v` iterates: `g + N•v ∈ C` for every `N : ℕ`. -/
theorem add_nsmul_mem_of_step {C : Set (ℤ × ℤ)} {v : ℤ × ℤ} (hv : ∀ g ∈ C, g + v ∈ C)
    {g : ℤ × ℤ} (hg : g ∈ C) : ∀ N : ℕ, g + (N : ℤ) • v ∈ C := by
  intro N
  induction N with
  | zero => simpa using hg
  | succ k ih =>
      have h := hv _ ih
      have e : g + ((k + 1 : ℕ) : ℤ) • v = g + (k : ℤ) • v + v := by
        push_cast
        rw [add_smul, one_smul, add_assoc]
      rw [e]
      exact h

/-- The level functional `det w ·` is affine along `v`: `det w (g + N•v) = det w g + N * det w v`. -/
theorem det_add_zsmul (w g v : ℤ × ℤ) (N : ℤ) :
    det w (g + N • v) = det w g + N * det w v := by
  simp only [det, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-! ## §2  The one-step level criterion

原文：b3_colle2.txt:808.  `LevelInterval C w` (`RegionSweep.lean:174`) is exactly the hypothesis
`isLatticeConvexRegion_sweep` needs; these two lemmas show it is free as soon as `C` is closed
under a translation whose level step is `±1`. -/

/-- **`LevelInterval` from a single unit-step closure direction (`det w v = 1`).**

原文：b3_colle2.txt:808.  Every level `m` with `det w a ≤ m ≤ det w b` is attained at
`a + (m - det w a)•v`, which lies in `C` because `C` is `+v`-closed. -/
theorem levelInterval_of_step_det_one {C : Set (ℤ × ℤ)} {w v : ℤ × ℤ}
    (hv : ∀ g ∈ C, g + v ∈ C) (hdet : det w v = 1) : LevelInterval C w := by
  intro a ha b _ m hma _
  refine ⟨a + ((m - det w a).toNat : ℤ) • v, add_nsmul_mem_of_step hv ha _, ?_⟩
  have e : (((m - det w a).toNat : ℕ) : ℤ) = m - det w a := Int.toNat_of_nonneg (by omega)
  rw [det_add_zsmul, e, hdet]
  ring

/-- **`LevelInterval` from a single unit-step closure direction (`det w v = -1`).**

原文：b3_colle2.txt:808.  Mirror image of `levelInterval_of_step_det_one`: walk **down** from the
upper endpoint `b` instead of up from `a`. -/
theorem levelInterval_of_step_det_neg_one {C : Set (ℤ × ℤ)} {w v : ℤ × ℤ}
    (hv : ∀ g ∈ C, g + v ∈ C) (hdet : det w v = -1) : LevelInterval C w := by
  intro a _ b hb m _ hmb
  refine ⟨b + ((det w b - m).toNat : ℤ) • v, add_nsmul_mem_of_step hv hb _, ?_⟩
  have e : (((det w b - m).toNat : ℕ) : ℤ) = det w b - m := Int.toNat_of_nonneg (by omega)
  rw [det_add_zsmul, e, hdet]
  ring

/-- **`LevelInterval` from two closure directions and a ℕ-Bézout relation.**

原文：b3_colle2.txt:808.  For the tower, `v₁ = vl` and `v₂ = u'` are the two ray directions the
seed `𝓡_I = coneRegion B vl u'` is closed under (`:780`), and the hypothesis is the arithmetic
condition `∃ a b : ℕ, a * det w vl + b * det w u' = ±1`. -/
theorem levelInterval_of_two_steps {C : Set (ℤ × ℤ)} {w v₁ v₂ : ℤ × ℤ}
    (h₁ : ∀ g ∈ C, g + v₁ ∈ C) (h₂ : ∀ g ∈ C, g + v₂ ∈ C) (a b : ℕ)
    (h : (a : ℤ) * det w v₁ + (b : ℤ) * det w v₂ = 1 ∨
         (a : ℤ) * det w v₁ + (b : ℤ) * det w v₂ = -1) :
    LevelInterval C w := by
  -- the combined step vector
  set v : ℤ × ℤ := (a : ℤ) • v₁ + (b : ℤ) • v₂ with hvdef
  have hstep : ∀ g ∈ C, g + v ∈ C := by
    intro g hg
    have h1 : g + (a : ℤ) • v₁ ∈ C := add_nsmul_mem_of_step h₁ hg a
    have h2 : g + (a : ℤ) • v₁ + (b : ℤ) • v₂ ∈ C := add_nsmul_mem_of_step h₂ h1 b
    have e : g + v = g + (a : ℤ) • v₁ + (b : ℤ) • v₂ := by rw [hvdef]; abel
    rw [e]
    exact h2
  have hdv : det w v = (a : ℤ) * det w v₁ + (b : ℤ) * det w v₂ := by
    rw [hvdef]
    simp only [det, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  rcases h with h | h
  · exact levelInterval_of_step_det_one hstep (by rw [hdv, h])
  · exact levelInterval_of_step_det_neg_one hstep (by rw [hdv, h])

/-! ## §3  Closure directions survive the tower -/

/-- `sweep` preserves closure under `+ v`. -/
theorem step_sweep {C : Set (ℤ × ℤ)} {v w : ℤ × ℤ} (hv : ∀ g ∈ C, g + v ∈ C) :
    ∀ g ∈ sweep C w, g + v ∈ sweep C w := by
  rintro _ ⟨g, hg, t, rfl⟩
  exact ⟨g + v, hv g hg, t, by abel⟩

/-- Every tower level inherits the seed's closure directions.

原文：b3_colle2.txt:808. -/
theorem step_tower {R₀ : Set (ℤ × ℤ)} {w : ℕ → ℤ × ℤ} {v : ℤ × ℤ}
    (hv : ∀ g ∈ R₀, g + v ∈ R₀) :
    ∀ n, ∀ g ∈ tower R₀ w n, g + v ∈ tower R₀ w n := by
  intro n
  induction n with
  | zero => exact hv
  | succ k ih => exact step_sweep ih

/-! ## §4  The replacement for `isRegion_tower` -/

/-- **`isRegion_tower` with `hlev` replaced by a ℕ-Bézout condition on the two seed rays.**

原文：b3_colle2.txt:806-820.  Same conclusion as `Nivat.ColleReg.isRegion_tower`
(`TowerBuild.lean:91`), but the per-level hypothesis `LevelInterval (tower R₀ w i) (w i)` — false
in the unrestricted form (`tmp/wip/lane-towerpkg-hlev-counterexample.lean:42`) — is replaced by

* `h₁`, `h₂`: the seed is closed under its two ray directions `v₁`, `v₂` (for
  `R₀ = coneRegion B vl u'` these are `coneRegion_add_vl` / `coneRegion_add_u'`, free);
* `H`: for each sweep direction, `det (w i) ·` takes the value `±1` on some ℕ-combination of
  `v₁` and `v₂`.

`H` is strictly weaker than `hlev`: it mentions only the two fixed vectors `v₁, v₂` and the
sweep directions, never the tower levels themselves. -/
theorem isRegion_tower_of_steps {R₀ : Set (ℤ × ℤ)} {u u' v₁ v₂ : ℤ × ℤ} {w : ℕ → ℤ × ℤ}
    (hR₀ : IsRegion R₀ u u')
    (h₁ : ∀ g ∈ R₀, g + v₁ ∈ R₀) (h₂ : ∀ g ∈ R₀, g + v₂ ∈ R₀)
    (hw : ∀ i, Primitive (w i))
    (H : ∀ i, ∃ a b : ℕ,
      (a : ℤ) * det (w i) v₁ + (b : ℤ) * det (w i) v₂ = 1 ∨
      (a : ℤ) * det (w i) v₁ + (b : ℤ) * det (w i) v₂ = -1) :
    ∀ n, IsRegion (tower R₀ w n) u u' := by
  refine isRegion_tower hR₀ hw (fun i => ?_)
  obtain ⟨a, b, hab⟩ := H i
  exact levelInterval_of_two_steps (step_tower h₁ i) (step_tower h₂ i) a b hab

/-! ## §5  The cone seed: both closure hypotheses are free -/

theorem step_coneRegion_vl {B : Set (ℤ × ℤ)} {vl u' : ℤ × ℤ} :
    ∀ g ∈ Nivat.ConeRegion.coneRegion B vl u', g + vl ∈ Nivat.ConeRegion.coneRegion B vl u' := by
  intro g hg
  rw [Nivat.ConeRegion.mem_coneRegion_iff] at hg ⊢
  obtain ⟨b, hb, s, t, rfl⟩ := hg
  refine ⟨b, hb, s + 1, t, ?_⟩
  push_cast
  rw [add_smul, one_smul]
  abel

theorem step_coneRegion_u' {B : Set (ℤ × ℤ)} {vl u' : ℤ × ℤ} :
    ∀ g ∈ Nivat.ConeRegion.coneRegion B vl u', g + u' ∈ Nivat.ConeRegion.coneRegion B vl u' := by
  intro g hg
  rw [Nivat.ConeRegion.mem_coneRegion_iff] at hg ⊢
  obtain ⟨b, hb, s, t, rfl⟩ := hg
  refine ⟨b, hb, s, t + 1, ?_⟩
  push_cast
  rw [add_smul, one_smul]
  abel

/-- **The packaged form for `lane-towerpkg`.**  Seed `R₀ = coneRegion B vl u'` (`:780`), so the
two closure hypotheses of `isRegion_tower_of_steps` are discharged on the spot and the only
remaining obligation is the arithmetic one. -/
theorem isRegion_tower_coneRegion {B : Set (ℤ × ℤ)} {vl u' u₁ u₂ : ℤ × ℤ} {w : ℕ → ℤ × ℤ}
    (hR₀ : IsRegion (Nivat.ConeRegion.coneRegion B vl u') u₁ u₂)
    (hw : ∀ i, Primitive (w i))
    (H : ∀ i, ∃ a b : ℕ,
      (a : ℤ) * det (w i) vl + (b : ℤ) * det (w i) u' = 1 ∨
      (a : ℤ) * det (w i) vl + (b : ℤ) * det (w i) u' = -1) :
    ∀ n, IsRegion (tower (Nivat.ConeRegion.coneRegion B vl u') w n) u₁ u₂ :=
  isRegion_tower_of_steps hR₀ step_coneRegion_vl step_coneRegion_u' hw H

/-! ## §6  Discharging `H` from determinant data alone

原文：b3_colle2.txt:808.  In the consumer's scope the only facts available about a sweep direction
are `Primitive (w i)`, `hunimod : det u' vl = ±1`, and sign information on `det (w i) vl`,
`det (w i) u'`.  This section turns exactly that into the `H` of §4. -/

/-- **Coprimality of the two level steps.**  If `w` is primitive and `(vl, u')` is unimodular,
then `det w vl` and `det w u'` are coprime — they are (up to the unit `det u' vl`) the two
coordinates of `w` in the basis `(vl, u')`. -/
theorem isCoprime_det_of_primitive {w vl u' : ℤ × ℤ} (hw : Primitive w)
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) :
    IsCoprime (det w vl) (det w u') := by
  obtain ⟨x, y, hxy⟩ := hw
  have hε : det u' vl * det u' vl = 1 := by
    rcases hunimod with h | h <;> rw [h] <;> norm_num
  refine ⟨det u' vl * (x * u'.1 + y * u'.2), -(det u' vl) * (x * vl.1 + y * vl.2), ?_⟩
  simp only [det] at hε ⊢
  linear_combination ((u'.1 * vl.2 - u'.2 * vl.1) ^ 2) * hxy + hε

/-- **ℕ-Bézout from opposite signs.**  Coprime integers of opposite signs admit a Bézout relation
with **non-negative** coefficients: shift `(x, y)` by a multiple of `(-B, A)`, which moves both
coefficients upward. -/
theorem exists_bezout_nat {A Bd : ℤ} (hco : IsCoprime A Bd) (hA : 0 < A) (hB : Bd < 0) :
    ∃ a b : ℕ, (a : ℤ) * A + (b : ℤ) * Bd = 1 := by
  obtain ⟨x, y, hxy⟩ := hco
  set t : ℤ := |x| + |y| with ht
  have htx : |x| ≤ t := by have := abs_nonneg y; omega
  have hty : |y| ≤ t := by have := abs_nonneg x; omega
  have ht0 : 0 ≤ t := le_trans (abs_nonneg x) htx
  have hx1 : 0 ≤ x - t * Bd := by
    have h1 : t ≤ t * (-Bd) := by nlinarith
    have h2 : -|x| ≤ x := neg_abs_le x
    nlinarith
  have hy1 : 0 ≤ y + t * A := by
    have h1 : t ≤ t * A := by nlinarith
    have h2 : -|y| ≤ y := neg_abs_le y
    nlinarith
  refine ⟨(x - t * Bd).toNat, (y + t * A).toNat, ?_⟩
  rw [Int.toNat_of_nonneg hx1, Int.toNat_of_nonneg hy1]
  linear_combination hxy

/-- **The `H` of §4 from determinant data.**  Each of the five listed cases produces the required
ℕ-Bézout pair.  In the `(vl, u')` basis (`w = p•vl + q•u'`, `ε := det u' vl`) they read
`|q| = 1`, `|p| = 1`, and `p·q > 0`; the omitted case is `|p| ≥ 2 ∧ |q| ≥ 2` with `p·q < 0`,
which §7 shows is genuinely fatal. -/
theorem exists_bezout_of_det_cases {w vl u' : ℤ × ℤ} (hw : Primitive w)
    (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hcase : det w vl = 1 ∨ det w vl = -1 ∨ det w u' = 1 ∨ det w u' = -1 ∨
      det w vl * det w u' < 0) :
    ∃ a b : ℕ,
      (a : ℤ) * det w vl + (b : ℤ) * det w u' = 1 ∨
      (a : ℤ) * det w vl + (b : ℤ) * det w u' = -1 := by
  rcases hcase with h | h | h | h | h
  · exact ⟨1, 0, Or.inl (by rw [h]; ring)⟩
  · exact ⟨1, 0, Or.inr (by rw [h]; ring)⟩
  · exact ⟨0, 1, Or.inl (by rw [h]; ring)⟩
  · exact ⟨0, 1, Or.inr (by rw [h]; ring)⟩
  · have hco := isCoprime_det_of_primitive hw hunimod
    rcases lt_trichotomy (det w vl) 0 with hA | hA | hA
    · have hB : 0 < det w u' := by nlinarith
      obtain ⟨b, a, hba⟩ := exists_bezout_nat hco.symm hB hA
      exact ⟨a, b, Or.inl (by linarith [hba])⟩
    · rw [hA] at h; simp at h
    · have hB : det w u' < 0 := by nlinarith
      obtain ⟨a, b, hab⟩ := exists_bezout_nat hco hA hB
      exact ⟨a, b, Or.inl hab⟩

/-- **The end-to-end statement for `lane-towerpkg`.**

原文：b3_colle2.txt:806-820.  Seed `𝓡_I = coneRegion B vl u'` (`:780`), sweep directions `w`
(`:808`).  The only obligation left beyond what `isRegion_tower` already needed (`hR₀`, `hw`) is
the **determinant case split** `hcase`, which mentions no tower level at all. -/
theorem isRegion_tower_coneRegion_of_det_cases {B : Set (ℤ × ℤ)} {vl u' u₁ u₂ : ℤ × ℤ}
    {w : ℕ → ℤ × ℤ}
    (hR₀ : IsRegion (Nivat.ConeRegion.coneRegion B vl u') u₁ u₂)
    (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hw : ∀ i, Primitive (w i))
    (hcase : ∀ i, det (w i) vl = 1 ∨ det (w i) vl = -1 ∨ det (w i) u' = 1 ∨ det (w i) u' = -1 ∨
      det (w i) vl * det (w i) u' < 0) :
    ∀ n, IsRegion (tower (Nivat.ConeRegion.coneRegion B vl u') w n) u₁ u₂ :=
  isRegion_tower_coneRegion hR₀ hw
    (fun i => exists_bezout_of_det_cases (hw i) hunimod (hcase i))

/-- **The convexity-only half**, i.e. the exact shape of `lane-towerpkg`'s `hconv` binder
(`tmp/wip/lane-towerpkg-main.lean`, the `hconv` of `lane_towerpkg_reduce`).

原文：b3_colle2.txt:806-820.  `lane-towerpkg` already owns both rays of `Colle41.IsRegion Rinf vl w`
(`rayIn_tower_vl` / `ray_mem_tower_extChain`, `TowerHBaseMin.lean:452`), and its `w : ℤ × ℤ` is a
**single** direction `extChain d nℓ vl u' I`, not the per-layer sequence `w : ℕ → ℤ × ℤ` swept
here; so the only part of `isRegion_tower_coneRegion_of_det_cases` it can consume is the
`IsLatticeConvexRegion` projection, which is `m`-free and ray-free. -/
theorem latticeConvexRegion_tower_coneRegion_of_det_cases {B : Set (ℤ × ℤ)} {vl u' u₁ u₂ : ℤ × ℤ}
    {w : ℕ → ℤ × ℤ}
    (hR₀ : IsRegion (Nivat.ConeRegion.coneRegion B vl u') u₁ u₂)
    (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hw : ∀ i, Primitive (w i))
    (hcase : ∀ i, det (w i) vl = 1 ∨ det (w i) vl = -1 ∨ det (w i) u' = 1 ∨ det (w i) u' = -1 ∨
      det (w i) vl * det (w i) u' < 0) :
    ∀ n, IsLatticeConvexRegion (tower (Nivat.ConeRegion.coneRegion B vl u') w n) :=
  fun n => (isRegion_tower_coneRegion_of_det_cases hR₀ hunimod hw hcase n).1

/-- The final tower direction is `-vl` (`TowerConstruct.wtower_last`, 原文 `:810`), and it always
satisfies `hcase`: `det (-vl) u' = det u' vl = ±1`. -/
theorem det_cases_neg_vl {vl u' : ℤ × ℤ} (hunimod : det u' vl = 1 ∨ det u' vl = -1) :
    det (-vl) vl = 1 ∨ det (-vl) vl = -1 ∨ det (-vl) u' = 1 ∨ det (-vl) u' = -1 ∨
      det (-vl) vl * det (-vl) u' < 0 := by
  rcases hunimod with h | h
  · refine Or.inr (Or.inr (Or.inl ?_))
    simp only [det, Prod.fst_neg, Prod.snd_neg] at h ⊢
    linarith
  · refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
    simp only [det, Prod.fst_neg, Prod.snd_neg] at h ⊢
    linarith

/-! ## §7  Sharpness: `H` cannot be dropped

Kernel witness that the residual case (`w = p•vl + q•u'` with `p ≤ -2` and `q ≥ 2`) really breaks
the tower, so no hypothesis-free version of §4 exists.  Data: `B = {(0,0)}`, `vl = (1,0)`,
`u' = (0,1)`, `nℓ = (0,-1)`, `w = (-2,3) = -2•vl + 3•u'`.  This `w` passes every filter the
construction imposes on a `candSet` element:

* `Primitive w` (`gcd 2 3 = 1`);
* `dot nℓ w = -3 < 0` (`TowerConstruct.dot_wgen_neg`), the same open half-plane as
  `u'` (`dot nℓ u' = -1`), with `dot nℓ vl = 0`;
* `det u' vl = -1`, i.e. `hunimod` holds.

Yet `tower (coneRegion B vl u') (fun _ => w) 1 = sweep (coneRegion B vl u') w` is not
lattice-convex: it contains `(0,1) = (0,0) + 1•u'` and `(-2,3) = (0,0) + 1•w`, whose midpoint
`(-1,2)` is a lattice point that is **not** of the form `(s,t) + k•(-2,3)` with `s,t,k : ℕ`
(`k = 0` forces `s = -1`, and `k ≥ 1` forces `t = 2 - 3k < 0`).

⚠ **Scope caveat — do not quote these lemmas against the `henv` version of `hconv`.**
The seed used here is `B = {(0,0)}`, which is **not** a legal seed in the construction:
`E {(0,0)} = ∅`, whereas a real seed satisfies `henv : EnvOf ↑d.Sphi B`.  This is now a kernel
fact, not prose — `LaneTowerPkgEnvSymm.not_envOf_Sphi_of_subsingleton`
(`EnvNegSymm.lean:152`) shows **no** subsingleton `B` admits `EnvOf ↑d.Sphi B`, so the lemmas
below are true but *uninstantiable* at a legal seed.

Why a legal seed closes the gap: `DecompData.Sphi_eq` (`DecompData.lean:108`) pins `Conv d.Sphi`
to a zonotope, hence centrally
symmetric; `TowerConstruct.genPerp'_mem_E_B` (`TowerConstruct.lean:64`) then puts **both**
`genPerp' (d.h j)` and its negation in `E B`, so every candidate direction carries a *pair* of
antipodal edges of `B` with `Nontrivial` faces.  Under that hypothesis the gap `(-1,2)` is
supplied by the seed (it is an interior point of the zonotope on generators `(1,0)`, `(0,1)`,
`(-2,3)`, with coefficients `1/3, 0, 2/3`).

So §7 says exactly one thing: **the sweep directions alone do not determine lattice convexity**,
i.e. any hypothesis-free version of §4 is false.  It says nothing about `hconv` as stated with
`henv` in scope.  (The same caveat applies to `tmp/wip/lane-tower-hlev-hconv-refuted.lean`,
which this lane has **withdrawn** for the same reason: its `B` had a vertex, not an edge, on the
`nℓ` side.) -/

theorem primitive_neg_two_three : Primitive ((-2 : ℤ), (3 : ℤ)) := ⟨1, 1, by norm_num⟩

theorem det_u'_vl_eq_neg_one : det ((0 : ℤ), (1 : ℤ)) ((1 : ℤ), (0 : ℤ)) = -1 := by
  simp [det]

theorem dot_nl_neg_two_three : Nivat.LE2.dot ((0 : ℤ), (-1 : ℤ)) ((-2 : ℤ), (3 : ℤ)) = -3 := by
  simp [Nivat.LE2.dot]

/-- The midpoint `(-1,2)` is missing from the first tower level. -/
theorem mid_not_mem :
    ((-1 : ℤ), (2 : ℤ)) ∉
      sweep (Nivat.ConeRegion.coneRegion ({((0 : ℤ), (0 : ℤ))} : Set (ℤ × ℤ)) (1, 0) (0, 1))
        ((-2 : ℤ), (3 : ℤ)) := by
  rintro ⟨g, hg, k, hk⟩
  rw [Nivat.ConeRegion.mem_coneRegion_iff] at hg
  obtain ⟨b, hb, s, t, rfl⟩ := hg
  rw [Set.mem_singleton_iff] at hb
  subst hb
  have h1 := congrArg Prod.fst hk
  have h2 := congrArg Prod.snd hk
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
    zero_add, mul_zero, mul_one, add_zero] at h1 h2
  omega

/-- **Sharpness.**  With `B = {(0,0)}`, `vl = (1,0)`, `u' = (0,1)` (so `det u' vl = -1`) and the
primitive direction `w = (-2,3)` in the half-plane `dot (0,-1) w < 0`, the first tower level is
not lattice-convex — hence not a `Colle41.IsRegion` for any pair of directions.

⚠ `B = {(0,0)}` is not a legal seed (`E B = ∅`, no `EnvOf ↑d.Sphi B` — kernel-excluded by
`LaneTowerPkgEnvSymm.not_envOf_Sphi_of_subsingleton`, `EnvNegSymm.lean:152`); see the §7
caveat. -/
theorem sweep_cone_not_isLatticeConvexRegion :
    ¬ IsLatticeConvexRegion
      (sweep (Nivat.ConeRegion.coneRegion ({((0 : ℤ), (0 : ℤ))} : Set (ℤ × ℤ)) (1, 0) (0, 1))
        ((-2 : ℤ), (3 : ℤ))) := by
  intro hK
  have h0 : ((0 : ℤ), (1 : ℤ)) ∈
      sweep (Nivat.ConeRegion.coneRegion ({((0 : ℤ), (0 : ℤ))} : Set (ℤ × ℤ)) (1, 0) (0, 1))
        ((-2 : ℤ), (3 : ℤ)) := by
    refine ⟨(0, 1), ?_, 0, by simp⟩
    rw [Nivat.ConeRegion.mem_coneRegion_iff]
    exact ⟨(0, 0), rfl, 0, 1, by norm_num⟩
  have h2 : ((-2 : ℤ), (3 : ℤ)) ∈
      sweep (Nivat.ConeRegion.coneRegion ({((0 : ℤ), (0 : ℤ))} : Set (ℤ × ℤ)) (1, 0) (0, 1))
        ((-2 : ℤ), (3 : ℤ)) := by
    refine ⟨(0, 0), ?_, 1, by norm_num⟩
    rw [Nivat.ConeRegion.mem_coneRegion_iff]
    exact ⟨(0, 0), rfl, 0, 0, by norm_num⟩
  refine mid_not_mem (Colle43.latticeConvexRegion_midpoint hK h0 h2 ?_)
  rw [Prod.ext_iff]
  norm_num

/-- The same data, as a single statement: all the local filters hold, and the tower level fails.

⚠ `B = {(0,0)}` is not a legal seed (kernel-excluded by
`LaneTowerPkgEnvSymm.not_envOf_Sphi_of_subsingleton`, `EnvNegSymm.lean:152`); see the §7
caveat.  This refutes the hypothesis-free `isRegion_tower_of_steps` route, **not** `hconv`
with `henv` in scope. -/
theorem tower_level_one_not_isRegion :
    Primitive ((-2 : ℤ), (3 : ℤ)) ∧
    det ((0 : ℤ), (1 : ℤ)) ((1 : ℤ), (0 : ℤ)) = -1 ∧
    Nivat.LE2.dot ((0 : ℤ), (-1 : ℤ)) ((-2 : ℤ), (3 : ℤ)) < 0 ∧
    Nivat.LE2.dot ((0 : ℤ), (-1 : ℤ)) ((1 : ℤ), (0 : ℤ)) = 0 ∧
    (∀ u₁ u₂ : ℤ × ℤ, ¬ IsRegion
      (tower (Nivat.ConeRegion.coneRegion ({((0 : ℤ), (0 : ℤ))} : Set (ℤ × ℤ)) (1, 0) (0, 1))
        (fun _ => ((-2 : ℤ), (3 : ℤ))) 1) u₁ u₂) := by
  refine ⟨primitive_neg_two_three, det_u'_vl_eq_neg_one, by rw [dot_nl_neg_two_three]; norm_num,
    by simp [Nivat.LE2.dot], fun u₁ u₂ hR => ?_⟩
  exact sweep_cone_not_isLatticeConvexRegion (by simpa [tower] using hR.1)

end Nivat.LaneTowerHlev

#print axioms Nivat.LaneTowerHlev.levelInterval_of_step_det_one
#print axioms Nivat.LaneTowerHlev.levelInterval_of_step_det_neg_one
#print axioms Nivat.LaneTowerHlev.levelInterval_of_two_steps
#print axioms Nivat.LaneTowerHlev.isRegion_tower_of_steps
#print axioms Nivat.LaneTowerHlev.isRegion_tower_coneRegion
#print axioms Nivat.LaneTowerHlev.sweep_cone_not_isLatticeConvexRegion
#print axioms Nivat.LaneTowerHlev.tower_level_one_not_isRegion
#print axioms Nivat.LaneTowerHlev.isCoprime_det_of_primitive
#print axioms Nivat.LaneTowerHlev.exists_bezout_nat
#print axioms Nivat.LaneTowerHlev.exists_bezout_of_det_cases
#print axioms Nivat.LaneTowerHlev.isRegion_tower_coneRegion_of_det_cases
#print axioms Nivat.LaneTowerHlev.latticeConvexRegion_tower_coneRegion_of_det_cases
#print axioms Nivat.LaneTowerHlev.det_cases_neg_vl
