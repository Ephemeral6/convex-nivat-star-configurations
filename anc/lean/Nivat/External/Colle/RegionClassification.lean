/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.Lemma35
import Nivat.External.Colle.Lemma41
import Nivat.External.Colle.MaximalEnveloped
import Nivat.Lattice.Primitive
import Nivat.Section8.RegionUpgrade

/-!
# Region classification for Lemma 3.5
-/

namespace Nivat.ColleReg

open Nivat Nivat.Colle Nivat.Colle35 Nivat.LE2 Nivat.Colle41

-- `chainData_yields_region` withdrawn 2026-09-16 (dead code, dimension degeneration):
-- when `PosArea S` fails (e.g. `S = {(0,0)}`), the chain construction degenerates to 1D
-- or 0D, violating the 2D region requirement in `IsRegion`. Confirmed false as stated
-- (witness: `S = {(0,0),(1,0)}`, `B = A = Ahat = box (0,0) (1+i,0)`, a legal `ChainData`
-- whose union lies entirely on `y = 0`, so no `u'` with `det vl u' ≠ 0` can start a ray
-- inside it). Zero term-level consumers (`ExternalDischarged.lean:67`,
-- `RegionSteps.lean:194` both note it is not on the critical path). See
-- `blueprint/NOTE.md` ("撤下 chainData_yields_region", 2026-09-16) for the full analysis.

/-- `det` is linear in its second argument for integer scalars. -/
private theorem det_zsmul_right' (a : ℤ) (v w : ℤ × ℤ) :
    det v (a • w) = a * det v w := by
  simp only [det, Prod.smul_def, smul_eq_mul]; ring

/-- **Ray transfer.**  If `R` is a lattice-convex region and `toReal h` lies in its recession
cone, then any point of `R` starts a forward `h`-ray inside `R`. -/
private theorem ray_of_mem_recCone {R : Set (ℤ × ℤ)} (hR : IsLatticeConvexRegion R)
    {z₀ h : ℤ × ℤ} (hz₀ : z₀ ∈ R) (hrec : toReal h ∈ recCone R) :
    ∀ k : ℕ, z₀ + (k : ℤ) • h ∈ R := by
  intro k
  induction k with
  | zero => simpa using hz₀
  | succ k ih =>
    have heq : z₀ + ((k + 1 : ℕ) : ℤ) • h = (z₀ + (k : ℤ) • h) + h := by
      push_cast [add_smul]; abel
    rw [heq]
    exact add_mem_of_mem_recCone hR hrec ih

/-- **Positive parallel rescaling stays in the recession cone.**  If `R` carries a forward
`u`-ray with `u = d • v` (`d > 0`) and `h = e • v` with `e > 0`, then `toReal h ∈ K_R`.
This is where `smul_mem_recCone` does the work that would otherwise need an explicit
convex-combination argument: `h = (e/d) • u` with `e/d > 0` a *real* scalar. -/
private theorem rec_of_pos_parallel {R : Set (ℤ × ℤ)} {z₀ u v h : ℤ × ℤ} {e : ℤ} {d : ℕ}
    (hray : ∀ k : ℕ, z₀ + (k : ℤ) • u ∈ R)
    (hd : 0 < d) (hu : u = (d : ℤ) • v) (hh : h = e • v) (he : 0 < e) :
    toReal h ∈ recCone R := by
  have hu_rec : toReal u ∈ recCone R := toReal_mem_recCone_of_nat_ray hray
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have ht : (0 : ℝ) ≤ (e : ℝ) / (d : ℝ) :=
    le_of_lt (div_pos (by exact_mod_cast he) hdR)
  have hmem := smul_mem_recCone ht hu_rec
  have hcd : ((e : ℝ) / (d : ℝ)) * ((d : ℤ) : ℝ) = (e : ℝ) := by
    push_cast; field_simp
  rw [hu, toReal_zsmul, smul_smul, hcd] at hmem
  rw [hh, toReal_zsmul]
  exact hmem

theorem region_yields_two_periods {A : Type*} {ϑ xper : Config A}
    {R : Set (ℤ × ℤ)} {u u' : ℤ × ℤ}
    (hR : Colle41.IsRegion R u u')
    (hdet : det u u' ≠ 0)
    (hagree : ∀ z ∈ R, ϑ z = xper z)
    (hper_u : ∃ h : ℤ × ℤ, h ≠ 0 ∧ det h u = 0 ∧ h ∈ Per xper)
    (hper_u' : ∃ h' : ℤ × ℤ, h' ≠ 0 ∧ det h' u' = 0 ∧ h' ∈ Per xper) :
    ∃ h h' z₀ z₀' : ℤ × ℤ, det h h' ≠ 0 ∧
      (∀ k : ℕ, z₀ + (k : ℤ) • h ∈ R) ∧
      (∀ k : ℕ, z₀' + (k : ℤ) • h' ∈ R) ∧
      (∀ z ∈ R, z + h ∈ R → ϑ (z + h) = ϑ z) ∧
      (∀ z ∈ R, z + h' ∈ R → ϑ (z + h') = ϑ z) := by
  obtain ⟨hRconv, ⟨z₀_u, hray_u⟩, ⟨z₀_u', hray_u'⟩⟩ := hR
  obtain ⟨h_raw, hh_ne, hdet_h_u, hh_per⟩ := hper_u
  obtain ⟨h'_raw, hh'_ne, hdet_h'_u', hh'_per⟩ := hper_u'
  have hu_ne : u ≠ 0 := by rintro rfl; simp [det] at hdet
  have hu'_ne : u' ≠ 0 := by rintro rfl; simp [det] at hdet
  obtain ⟨v_u, d_u, hv_u_prim, hd_u_pos, hu_eq⟩ := exists_primitive_nsmul_eq hu_ne
  obtain ⟨v_u', d_u', hv_u'_prim, hd_u'_pos, hu'_eq⟩ := exists_primitive_nsmul_eq hu'_ne
  -- `h_raw = c_u • v_u`.
  have hdet_h_v_u : det v_u h_raw = 0 := by
    have h1 : det h_raw ((d_u : ℤ) • v_u) = 0 := by rw [← hu_eq]; exact hdet_h_u
    rw [det_zsmul_right'] at h1
    have hd : (d_u : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hd_u_pos.ne'
    have := (mul_eq_zero.mp h1).resolve_left hd
    rw [det_comm]; simp [this]
  obtain ⟨c_u, hh_eq⟩ := eq_zsmul_of_det_eq_zero hv_u_prim hdet_h_v_u
  have hdet_h'_v_u' : det v_u' h'_raw = 0 := by
    have h1 : det h'_raw ((d_u' : ℤ) • v_u') = 0 := by rw [← hu'_eq]; exact hdet_h'_u'
    rw [det_zsmul_right'] at h1
    have hd : (d_u' : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hd_u'_pos.ne'
    have := (mul_eq_zero.mp h1).resolve_left hd
    rw [det_comm]; simp [this]
  obtain ⟨c_u', hh'_eq⟩ := eq_zsmul_of_det_eq_zero hv_u'_prim hdet_h'_v_u'
  have hc_u_ne : c_u ≠ 0 := by rintro rfl; rw [zero_smul] at hh_eq; exact hh_ne hh_eq
  have hc_u'_ne : c_u' ≠ 0 := by rintro rfl; rw [zero_smul] at hh'_eq; exact hh'_ne hh'_eq
  -- Orient both periods *forwards*: `Per` is an `AddSubgroup`, so `-h ∈ Per` for free.
  -- This replaces the four-branch sign analysis with one `|c|`.
  set hs : ℤ × ℤ := if 0 < c_u then h_raw else -h_raw with hsdef
  set hs' : ℤ × ℤ := if 0 < c_u' then h'_raw else -h'_raw with hs'def
  have hs_eq : hs = |c_u| • v_u := by
    rcases lt_or_gt_of_ne hc_u_ne with hneg | hpos
    · rw [hsdef, if_neg (by omega), hh_eq, abs_of_neg hneg, neg_smul]
    · rw [hsdef, if_pos hpos, hh_eq, abs_of_pos hpos]
  have hs'_eq : hs' = |c_u'| • v_u' := by
    rcases lt_or_gt_of_ne hc_u'_ne with hneg | hpos
    · rw [hs'def, if_neg (by omega), hh'_eq, abs_of_neg hneg, neg_smul]
    · rw [hs'def, if_pos hpos, hh'_eq, abs_of_pos hpos]
  have hs_per : hs ∈ Per xper := by
    rw [hsdef]; split
    · exact hh_per
    · exact neg_mem hh_per
  have hs'_per : hs' ∈ Per xper := by
    rw [hs'def]; split
    · exact hh'_per
    · exact neg_mem hh'_per
  have habs : 0 < |c_u| := abs_pos.mpr hc_u_ne
  have habs' : 0 < |c_u'| := abs_pos.mpr hc_u'_ne
  -- The two base points lie in `R` (take `k = 0` in the rays).
  have hz₀ : z₀_u ∈ R := by simpa using hray_u 0
  have hz₀' : z₀_u' ∈ R := by simpa using hray_u' 0
  -- Recession-cone membership, hence the two forward rays.
  have hrec : toReal hs ∈ recCone R :=
    rec_of_pos_parallel hray_u hd_u_pos hu_eq hs_eq habs
  have hrec' : toReal hs' ∈ recCone R :=
    rec_of_pos_parallel hray_u' hd_u'_pos hu'_eq hs'_eq habs'
  refine ⟨hs, hs', z₀_u, z₀_u', ?_, ray_of_mem_recCone hRconv hz₀ hrec,
    ray_of_mem_recCone hRconv hz₀' hrec', ?_, ?_⟩
  · -- `det hs hs' = |c_u| * |c_u'| * det v_u v_u' ≠ 0`, since `det u u' ≠ 0`.
    have hvv : det v_u v_u' ≠ 0 := by
      intro h0
      apply hdet
      rw [hu_eq, hu'_eq, det_zsmul_zsmul, h0, mul_zero]
    rw [hs_eq, hs'_eq, det_zsmul_zsmul]
    exact mul_ne_zero (mul_ne_zero habs.ne' habs'.ne') hvv
  · intro z hz hzs
    rw [hagree _ hzs, hagree _ hz]
    exact Per.apply hs_per z
  · intro z hz hzs
    rw [hagree _ hzs, hagree _ hz]
    exact Per.apply hs'_per z

end Nivat.ColleReg
