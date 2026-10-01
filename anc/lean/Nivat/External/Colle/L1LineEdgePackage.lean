/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.L1LinePackage
import Nivat.External.Colle.L1EdgeFace

/-!
# L1 Line + Edge Package (Claim 4.7 window placement, `hline ∧ hedge`)

Lane: lane-place (2026-09-22)

Extends `Nivat.L1LinePackage.exists_line_package` (which only produces `hline`) to also
produce `hedge` (`RegionSteps.lean:1769-1774`), using `hconsec` (free from
`CutLevels.exists_lev_consecutive`) and the argmin-face structure of `L1EdgeFace.lean`.

## Construction (team-lead ruling, 2026-09-22)

`z_min := S`'s own `dot m`-minimum.  `z_gap ∈ Rinf` from `hgap N₀` combined with `hconsec N₀`
lands EXACTLY at `dot m z_gap = lev (N₀+1)` (not just in the range `hgap` alone gives).
`Rinf` is closed under `+vl` and under `+w` (both via `recession_of_ray`, applied to ANY point
of `Rinf`, not just the ray's own basepoint) — so both rays anchor at `z_gap` itself.

Writing `s - z_min = α(s) • vl + β(s) • w` over `ℝ` (valid since `det vl w ≠ 0`): `α(s) ≥ 0`
(from `dot m`-minimality of `z_min` and `dot m vl > 0`), `β(s)` is bounded below over the
finite `S`.  Pick `t : ℕ` with `t + β(s) ≥ 0` for all `s ∈ S`; set `v := z_gap + t • w - z_min`.
Then `s + v = z_gap + α(s) • vl + (β(s) + t) • w` lies in the real cone with apex `z_gap` and
nonnegative coefficients, hence (`lattice_pt_of_cone_mem`) in `Rinf`.

`dot m (s + v) = lev (N₀+1) + α(s) * dot m vl ≥ lev (N₀+1)`, with equality iff `s` achieves
`S`'s `dot m`-minimum.  The correct `ε` (from the sign of `lam` in `m = lam • perp w`) makes
`topFace ε w (S.image (·+v))` exactly the `dot m`-argmin face (`L1EdgeFace.lean`), so:
* non-top-face points have `dot m (s+v) > lev (N₀+1)`, hence (via `hconsec`) `≥ lev N₀` — `hline`.
* top-face points have `dot m (s+v) = lev (N₀+1) < lev N₀` exactly — `hedge`.

`τ := 0` throughout (no `w`-shift needed at the "read out" step; the shift is folded into `v`).
-/

set_option autoImplicit false

namespace Nivat.L1LinePackage

open Nivat Nivat.Colle41 Nivat.ColleReg Nivat.ColleReg.L1Data Nivat.L1Region Nivat.LE2

variable {ξ : Config ℤ} {vl : ℤ × ℤ}

/-! ## Planar decomposition -/

/-- Pure Cramer decomposition of `z` in the basis `(vl, w)`, no `dot` involved. -/
theorem cramer_decomp {vl w : ℤ × ℤ} (hdet : det vl w ≠ 0) (z : ℤ × ℤ) :
    toReal z = ((det z w : ℝ) / (det vl w : ℝ)) • toReal vl
        + ((det vl z : ℝ) / (det vl w : ℝ)) • toReal w := by
  have hD : (det vl w : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hdet
  apply Prod.ext
  · show (z.1 : ℝ) = _
    simp only [Prod.smul_fst, Prod.fst_add, smul_eq_mul, toReal]
    field_simp
    simp only [det]
    push_cast
    ring
  · show (z.2 : ℝ) = _
    simp only [Prod.smul_snd, Prod.snd_add, smul_eq_mul, toReal]
    field_simp
    simp only [det]
    push_cast
    ring

/-- The `vl`-coefficient in the Cramer decomposition agrees with the `dot m` ratio, via
`m = lam • perp w` (integer identity, then cast). -/
theorem detz_mul_dotvl_eq {vl w m : ℤ × ℤ} (hw_prim : Primitive w) (hmw : dot m w = 0)
    (z : ℤ × ℤ) : det z w * dot m vl = det vl w * dot m z := by
  obtain ⟨lam, hlam⟩ := Nivat.ColleReg.exists_lam_of_perp hw_prim hmw
  have h1 : dot m z = lam * det w z := Nivat.ColleReg.dot_eq_lam_mul_det hlam z
  have h2 : dot m vl = lam * det w vl := Nivat.ColleReg.dot_eq_lam_mul_det hlam vl
  have hzw : det w z = - det z w := by have := Nivat.LE2.det_skew z w; omega
  have hvlw : det w vl = - det vl w := by have := Nivat.LE2.det_skew vl w; omega
  rw [h1, h2, hzw, hvlw]; ring

theorem coeffA_eq_dot_ratio {vl w m : ℤ × ℤ} (hdet : det vl w ≠ 0) (hw_prim : Primitive w)
    (hmw : dot m w = 0) (hmvl0 : dot m vl ≠ 0) (z : ℤ × ℤ) :
    (det z w : ℝ) / (det vl w : ℝ) = (dot m z : ℝ) / (dot m vl : ℝ) := by
  have hD : (det vl w : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hdet
  have hDm : (dot m vl : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hmvl0
  have hint : det z w * dot m vl = dot m z * det vl w := by
    have := detz_mul_dotvl_eq (vl := vl) hw_prim hmw z
    rw [this]; ring
  rw [div_eq_div_iff hD hDm]
  exact_mod_cast hint

/-- `z` decomposes as `(dot m z / dot m vl) • vl + β(z) • w`, `β(z) := det vl z / det vl w`. -/
theorem decomp_dot_ratio {vl w m : ℤ × ℤ} (hdet : det vl w ≠ 0) (hw_prim : Primitive w)
    (hmw : dot m w = 0) (hmvl0 : dot m vl ≠ 0) (z : ℤ × ℤ) :
    toReal z = ((dot m z : ℝ) / (dot m vl : ℝ)) • toReal vl
        + ((det vl z : ℝ) / (det vl w : ℝ)) • toReal w := by
  rw [← coeffA_eq_dot_ratio hdet hw_prim hmw hmvl0 z]
  exact cramer_decomp hdet z

/-! ## `derivedQ` / `topFace` complement -/

theorem notDerivedQ_iff_topFace {ε : Bool} {w : ℤ × ℤ} {S₁ : Finset (ℤ × ℤ)} {z : ℤ × ℤ}
    (hz : z ∈ S₁) (hne : S₁.Nonempty) :
    z ∉ L1Data.derivedQ ε w S₁ ↔ z ∈ L1Data.topFace ε w S₁ := by
  unfold L1Data.derivedQ L1Data.topFace
  rw [Finset.mem_filter, Nivat.R2.mem_face]
  have hle := L1Data.le_levelMax (n := L1Data.cutNormal ε w) hne z hz
  constructor
  · intro h
    exact ⟨hz, le_antisymm hle (not_lt.mp (fun hc => h ⟨hz, hc⟩))⟩
  · rintro ⟨-, heq⟩
    exact fun ⟨_, hlt⟩ => absurd heq (ne_of_lt hlt)

theorem derivedQ_iff_not_topFace {ε : Bool} {w : ℤ × ℤ} {S₁ : Finset (ℤ × ℤ)} {z : ℤ × ℤ}
    (hz : z ∈ S₁) (hne : S₁.Nonempty) :
    z ∈ L1Data.derivedQ ε w S₁ ↔ z ∉ L1Data.topFace ε w S₁ := by
  have h := notDerivedQ_iff_topFace (ε := ε) (w := w) (S₁ := S₁) (z := z) hz hne
  tauto

/-! ## Core construction, `ε` fixed -/

theorem exists_line_package_core
    {e : ℤ × ℤ} {c : ℤ} {S : Finset (ℤ × ℤ)} {Rinf : Set (ℤ × ℤ)} {w m : ℤ × ℤ}
    {lev : ℕ → ℤ} {b₀ : ℤ} (ε : Bool)
    (hw_det : det vl w ≠ 0) (hw_prim : Primitive w)
    (hmw : LE2.dot m w = 0) (hmvl : 0 < LE2.dot m vl)
    (hlev0 : lev 0 = b₀) (hlev : Antitone lev)
    (hexh : ∀ b : ℤ, ∃ n : ℕ, lev n ≤ b)
    (hgap : ∀ n : ℕ, ∃ z ∈ Rinf, lev (n + 1) ≤ LE2.dot m z ∧ LE2.dot m z < lev n)
    (hconsec : ∀ n : ℕ, ∀ z ∈ Rinf, LE2.dot m z < lev n → LE2.dot m z ≤ lev (n + 1))
    (hR : Nivat.Colle41.IsRegion Rinf vl w)
    (hc : 0 < c) (hvl_prim : Primitive vl)
    (hinf : ¬ PeriodOn (T e ξ) Rinf (c • vl))
    (hS : S.Nonempty)
    (htop_iff : ∀ {S₁ : Finset (ℤ × ℤ)} {z : ℤ × ℤ}, z ∈ L1Data.topFace ε w S₁ ↔
      z ∈ S₁ ∧ ∀ y ∈ S₁, LE2.dot m z ≤ LE2.dot m y) :
    ∃ v : ℤ × ℤ, ∀ (N : ℕ),
      PeriodOn (T e ξ) (L1Region.cut Rinf m lev N) (c • vl) →
      ¬ PeriodOn (T e ξ) (L1Region.cut Rinf m lev (N + 1)) (c • vl) →
      (∀ z ∈ L1Data.derivedQ ε w (S.image (· + v)),
        (0 : ℤ) • w + z ∈ L1Region.cut Rinf m lev N ∧
        (0 : ℤ) • w + z + c • vl ∈ L1Region.cut Rinf m lev N) ∧
      (∀ z ∈ S.image (· + v), z ∉ L1Data.derivedQ ε w (S.image (· + v)) →
        (0 : ℤ) • w + z ∈ L1Region.cut Rinf m lev (N + 1) ∧
        (0 : ℤ) • w + z ∉ L1Region.cut Rinf m lev N) := by
  obtain ⟨hRconv, ⟨z₀, hz₀⟩, ⟨z₀', hz₀'⟩⟩ := hR
  have hmvl0 : LE2.dot m vl ≠ 0 := ne_of_gt hmvl
  have hstep_vl : ∀ z ∈ Rinf, z + vl ∈ Rinf := Nivat.RecessionCone.recession_of_ray hRconv hz₀
  have hstep_w : ∀ z ∈ Rinf, z + w ∈ Rinf := Nivat.RecessionCone.recession_of_ray hRconv hz₀'
  have hpush_vl : ∀ z ∈ Rinf, ∀ k : ℕ, z + (k : ℤ) • vl ∈ Rinf := by
    intro z hz k
    induction k with
    | zero => simpa using hz
    | succ k ih =>
        have heq : z + ((k + 1 : ℕ) : ℤ) • vl = z + (k : ℤ) • vl + vl := by
          push_cast; rw [add_smul, one_smul]; abel
        rw [heq]; exact hstep_vl _ ih
  have hpush_w : ∀ z ∈ Rinf, ∀ k : ℕ, z + (k : ℤ) • w ∈ Rinf := by
    intro z hz k
    induction k with
    | zero => simpa using hz
    | succ k ih =>
        have heq : z + ((k + 1 : ℕ) : ℤ) • w = z + (k : ℤ) • w + w := by
          push_cast; rw [add_smul, one_smul]; abel
        rw [heq]; exact hstep_w _ ih
  by_cases hexists : ∃ N : ℕ, PeriodOn (T e ξ) (L1Region.cut Rinf m lev N) (c • vl) ∧
      ¬ PeriodOn (T e ξ) (L1Region.cut Rinf m lev (N + 1)) (c • vl)
  · obtain ⟨N₀, hN₀_per, hN₀_not⟩ := hexists
    obtain ⟨z_min, hz_min, hmin⟩ := Finset.exists_min_image S (LE2.dot m) hS
    obtain ⟨z_gap, hz_gap, hgap1, hgap2⟩ := hgap N₀
    have hgap_le : LE2.dot m z_gap ≤ lev (N₀ + 1) := hconsec N₀ z_gap hz_gap hgap2
    have hzgap_eq : LE2.dot m z_gap = lev (N₀ + 1) := le_antisymm hgap_le hgap1
    have hlevlt : lev (N₀ + 1) < lev N₀ := lt_of_le_of_lt hgap1 hgap2
    set g : (ℤ × ℤ) → ℝ := fun s => (det vl (s - z_min) : ℝ) / (det vl w : ℝ) with hgdef
    obtain ⟨t, ht⟩ : ∃ t : ℕ, ∀ s ∈ S, 0 ≤ g s + (t : ℝ) := by
      obtain ⟨t, ht⟩ := exists_nat_ge (S.sup' hS (fun s => -g s))
      refine ⟨t, fun s hs => ?_⟩
      have hle := Finset.le_sup' (fun s => -g s) hs
      linarith
    set v : ℤ × ℤ := z_gap + (t : ℤ) • w - z_min with hvdef
    have hzgap_mem : z_gap ∈ Rinf := hz_gap
    have hrvl : RayIn Rinf z_gap vl := fun k => hpush_vl z_gap hzgap_mem k
    have hrw : RayIn Rinf z_gap w := fun k => hpush_w z_gap hzgap_mem k
    have hmemS : ∀ s ∈ S, s + v ∈ Rinf := by
      intro s hs
      have hdec := decomp_dot_ratio hw_det hw_prim hmw hmvl0 (s - z_min)
      have hnn : (0 : ℤ) ≤ LE2.dot m s - LE2.dot m z_min := by linarith [hmin s hs]
      have h2 : LE2.dot m (s - z_min) = LE2.dot m s - LE2.dot m z_min := LE2.dot_sub m s z_min
      have hmvlR : (0 : ℝ) ≤ (LE2.dot m vl : ℝ) := by exact_mod_cast hmvl.le
      have hp0 : 0 ≤ (LE2.dot m (s - z_min) : ℝ) / (LE2.dot m vl : ℝ) := by
        rw [h2]; exact div_nonneg (by exact_mod_cast hnn) hmvlR
      have hq0 : 0 ≤ g s + (t : ℝ) := ht s hs
      have hintid : s + v = (s - z_min) + z_gap + (t : ℤ) • w := by rw [hvdef]; abel
      have htoReal : toReal (s + v) =
          (2 : ℝ)⁻¹ • toReal z_gap + (2 : ℝ)⁻¹ • toReal z_gap +
            ((LE2.dot m (s - z_min) : ℝ) / (LE2.dot m vl : ℝ)) • toReal vl +
            (g s + (t : ℝ)) • toReal w := by
        rw [hintid, toReal_add, toReal_add, toReal_zsmul, hdec]
        have h1 : (2 : ℝ)⁻¹ • toReal z_gap + (2 : ℝ)⁻¹ • toReal z_gap = toReal z_gap := by
          rw [← add_smul]; norm_num
        rw [← h1]
        push_cast
        module
      exact Nivat.ColleReg.lattice_pt_of_cone_mem hRconv hrvl hrw hp0 hq0 htoReal
    have hv_dot : LE2.dot m v = lev (N₀ + 1) - LE2.dot m z_min := by
      rw [hvdef, LE2.dot_sub, LE2.dot_add, dot_zsmul_right, hzgap_eq, hmw]; ring
    have hlevS₁ : ∀ s ∈ S, lev (N₀ + 1) ≤ LE2.dot m (s + v) := by
      intro s hs
      rw [LE2.dot_add, hv_dot]
      linarith [hmin s hs]
    have hz_min_v_lev : LE2.dot m (z_min + v) = lev (N₀ + 1) := by
      rw [LE2.dot_add, hv_dot]; ring
    have hSne : (S.image (· + v)).Nonempty := Finset.image_nonempty.mpr hS
    have htopLev : ∀ s ∈ S, ((s + v) ∈ L1Data.topFace ε w (S.image (· + v)) ↔
        LE2.dot m (s + v) = lev (N₀ + 1)) := by
      intro s hs
      rw [htop_iff]
      constructor
      · rintro ⟨-, hmax⟩
        have h1 := hmax (z_min + v) (Finset.mem_image_of_mem _ hz_min)
        rw [hz_min_v_lev] at h1
        exact le_antisymm h1 (hlevS₁ s hs)
      · intro heq
        refine ⟨Finset.mem_image_of_mem _ hs, fun y hy => ?_⟩
        rw [Finset.mem_image] at hy
        obtain ⟨s', hs', rfl⟩ := hy
        rw [heq]; exact hlevS₁ s' hs'
    refine ⟨v, fun N hper_N hnotper_N1 => ?_⟩
    have hN_eq : N = N₀ := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hsub : L1Region.cut Rinf m lev (N + 1) ⊆ L1Region.cut Rinf m lev N₀ :=
          L1Region.cut_mono hlev (by omega : N + 1 ≤ N₀)
        exact hnotper_N1 (PeriodOn.mono hsub hN₀_per)
      · have hsub : L1Region.cut Rinf m lev (N₀ + 1) ⊆ L1Region.cut Rinf m lev N :=
          L1Region.cut_mono hlev (by omega : N₀ + 1 ≤ N)
        exact hN₀_not (PeriodOn.mono hsub hper_N)
    subst hN_eq
    refine ⟨?_, ?_⟩
    · intro z hz
      simp only [zero_smul, zero_add]
      have hzS₁ : z ∈ S.image (· + v) := derivedQ_subset ε w _ hz
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hzS₁
      have hmemR : s + v ∈ Rinf := hmemS s hs
      have hnotTop : (s + v) ∉ L1Data.topFace ε w (S.image (· + v)) :=
        (derivedQ_iff_not_topFace hzS₁ hSne).mp hz
      have hne_lev : LE2.dot m (s + v) ≠ lev (N + 1) :=
        fun heq => hnotTop ((htopLev s hs).mpr heq)
      have hge_lev : lev (N + 1) ≤ LE2.dot m (s + v) := hlevS₁ s hs
      have hlt_lev : lev (N + 1) < LE2.dot m (s + v) := lt_of_le_of_ne hge_lev (Ne.symm hne_lev)
      have hge_N0 : lev N ≤ LE2.dot m (s + v) := by
        by_contra hcon
        push_neg at hcon
        have := hconsec N (s + v) hmemR hcon
        omega
      have hmemR2 : s + v + c • vl ∈ Rinf := by
        have hcnn : (0 : ℤ) ≤ c := hc.le
        have hcc : ((c.toNat : ℕ) : ℤ) • vl = c • vl := by
          rw [Int.toNat_of_nonneg hcnn]
        rw [← hcc]
        exact hpush_vl (s + v) hmemR c.toNat
      have hlev2 : lev N ≤ LE2.dot m (s + v + c • vl) := by
        rw [LE2.dot_add, dot_zsmul_right]
        nlinarith [hge_N0, hmvl]
      exact ⟨⟨hmemR, hge_N0⟩, ⟨hmemR2, hlev2⟩⟩
    · intro z hz hnotQ
      simp only [zero_smul, zero_add]
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hz
      have hmemR : s + v ∈ Rinf := hmemS s hs
      have hTop : (s + v) ∈ L1Data.topFace ε w (S.image (· + v)) :=
        (notDerivedQ_iff_topFace hz hSne).mp hnotQ
      have heqlev : LE2.dot m (s + v) = lev (N + 1) := (htopLev s hs).mp hTop
      refine ⟨⟨hmemR, le_of_eq heqlev.symm⟩, ?_⟩
      intro hcontra
      obtain ⟨-, hge⟩ := hcontra
      simp only [LE2.halfPlaneGE, Set.mem_setOf_eq] at hge
      rw [heqlev] at hge
      omega
  · refine ⟨0, fun N hper_N hnotper_N1 => absurd ⟨N, hper_N, hnotper_N1⟩ hexists⟩

/-! ## `ε` selection -/

/-- Claim 4.7, extended: line package `hline` together with the top-face "edge" fact `hedge`
(`RegionSteps.lean:1769-1774`), in one placement `v τ ε`. -/
theorem exists_line_package'
    {e : ℤ × ℤ} {c : ℤ} {S : Finset (ℤ × ℤ)}
    (Rinf : Set (ℤ × ℤ))
    (w : ℤ × ℤ) (hw_det : det vl w ≠ 0) (hw_prim : Primitive w)
    (m : ℤ × ℤ) (hmw : LE2.dot m w = 0) (hmvl : 0 < LE2.dot m vl)
    (lev : ℕ → ℤ) (b₀ : ℤ)
    (hlev0 : lev 0 = b₀)
    (hlev : Antitone lev)
    (hexh : ∀ b : ℤ, ∃ n : ℕ, lev n ≤ b)
    (hgap : ∀ n : ℕ, ∃ z ∈ Rinf, lev (n + 1) ≤ LE2.dot m z ∧ LE2.dot m z < lev n)
    (hconsec : ∀ n : ℕ, ∀ z ∈ Rinf, LE2.dot m z < lev n → LE2.dot m z ≤ lev (n + 1))
    (hR : Nivat.Colle41.IsRegion Rinf vl w)
    (hc : 0 < c)
    (hvl_prim : Primitive vl)
    (hinf : ¬ PeriodOn (T e ξ) Rinf (c • vl)) :
    ∃ (v : ℤ × ℤ) (τ : ℤ) (ε : Bool), ∀ (N : ℕ),
      PeriodOn (T e ξ) (L1Region.cut Rinf m lev N) (c • vl) →
      ¬ PeriodOn (T e ξ) (L1Region.cut Rinf m lev (N + 1)) (c • vl) →
      (∀ z ∈ L1Data.derivedQ ε w (S.image (· + v)),
        τ • w + z ∈ L1Region.cut Rinf m lev N ∧
        τ • w + z + c • vl ∈ L1Region.cut Rinf m lev N) ∧
      (∀ z ∈ S.image (· + v), z ∉ L1Data.derivedQ ε w (S.image (· + v)) →
        τ • w + z ∈ L1Region.cut Rinf m lev (N + 1) ∧
        τ • w + z ∉ L1Region.cut Rinf m lev N) := by
  by_cases hS : S.Nonempty
  · obtain ⟨lam, hlam⟩ := Nivat.ColleReg.exists_lam_of_perp hw_prim hmw
    have hmvl0 : LE2.dot m vl ≠ 0 := ne_of_gt hmvl
    have hlam_ne : lam ≠ 0 := by
      intro h0
      apply hmvl0
      have := Nivat.ColleReg.dot_eq_lam_mul_det hlam vl
      rw [this, h0]; ring
    rcases lt_or_gt_of_ne hlam_ne with hlam_neg | hlam_pos
    · obtain ⟨v, hv⟩ := exists_line_package_core (S := S) true hw_det hw_prim hmw hmvl hlev0 hlev
        hexh hgap hconsec hR hc hvl_prim hinf hS
        (fun {S₁ z} => Nivat.ColleReg.topFace_true_eq_argmin hlam hlam_neg (S := S₁) (z := z))
      exact ⟨v, 0, true, fun N h1 h2 => by simpa using hv N h1 h2⟩
    · obtain ⟨v, hv⟩ := exists_line_package_core (S := S) false hw_det hw_prim hmw hmvl hlev0 hlev
        hexh hgap hconsec hR hc hvl_prim hinf hS
        (fun {S₁ z} => Nivat.ColleReg.topFace_false_eq_argmin hlam hlam_pos (S := S₁) (z := z))
      exact ⟨v, 0, false, fun N h1 h2 => by simpa using hv N h1 h2⟩
  · refine ⟨0, 0, true, fun N _ _ => ⟨?_, ?_⟩⟩
    · intro z hz
      exfalso; apply hS
      have himg : (S.image (· + 0) : Finset (ℤ × ℤ)).Nonempty := ⟨z, derivedQ_subset true w _ hz⟩
      rwa [Finset.image_nonempty] at himg
    · intro z hz _
      exfalso; apply hS
      rw [Finset.mem_image] at hz
      obtain ⟨s, hs, -⟩ := hz
      exact ⟨s, hs⟩

end Nivat.L1LinePackage

#print axioms Nivat.L1LinePackage.cramer_decomp
#print axioms Nivat.L1LinePackage.decomp_dot_ratio
#print axioms Nivat.L1LinePackage.notDerivedQ_iff_topFace
#print axioms Nivat.L1LinePackage.exists_line_package_core
#print axioms Nivat.L1LinePackage.exists_line_package'
