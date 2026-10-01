/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.Section8.RegionUpgrade
import Nivat.External.Colle.ChainGeom
import Nivat.External.Colle.Theorem114Step3
import Nivat.External.Colle.Lemma45
import Nivat.External.Colle.Interfaces
import Nivat.External.Colle.BoyleLind
import Nivat.External.Colle.Claim414Ell
import Nivat.External.Colle.RecessionCone

set_option autoImplicit false

/-!
# Collé Claim 4.14, the `ℓ′`-half (`delivery/scratch/b3_colle2.txt:912-922`)

`b3_colle2.txt:922` closes with "Therefore, from Claim 4.13 we conclude that
`ℓ, ℓ′ ∈ nexpl(ϑ)`", so the `ℓ′`-half of Claim 4.14 is Claim 4.13 (`:912-916`) read in
`nexpl` instead of `nexpd`.  Blocks 0′, 2′, 2″, 7 here are the parts not covered by the
`ℓ`-half file; block 5′ (assembly) additionally reuses blocks 1, 3, 4 and the monotonicity
lemma of `Claim414Ell.lean`.  Nothing here touches `Nivat/`.
-/

open Nivat

namespace Nivat.Claim414

/-! ## Block 0′: a lattice ray in a lattice-convex region is a recession direction

Lemma 4.1 (`b3_colle2.txt:904`, Lean `Colle41.lemma41_colle_region_shape`) hands over the
`(ℓ,ℓ′)`-region `𝒦` with its two semi-infinite edges as *rays* `∀ k, z₀ + k • d ∈ 𝒦`;
block 1 consumes recession directions `∀ g ∈ 𝒦, g + d ∈ 𝒦`.  For a lattice-convex region the
two are the same. -/

/-- **A lattice ray in a lattice-convex region is a recession direction.**

⭐ **2026-09-26 去重（lane-tower-hlev，集成者派工）：本条现在是转发，正本是
`Nivat.RecessionCone.recession_of_ray`（`RecessionCone.lean`）。**保留本名、**不删**
（盲区 3）。正本的选择理由与 import 代价见 `Nivat.Colle35.rec_of_ray`（`ItemII.lean`）的
docstring；一句话：`RecessionCone` 那份是链上被 `RegionSteps` 直接消费的那份、且最上游，
转发过来只多 1 个模块。

⚠ **一名多物**：`RecessionCone.lean` 与被禁读的 `ConeRecession.lean` 是两个不同文件。 -/
theorem rec_of_rayIn {R : Set (ℤ × ℤ)} (hR : IsLatticeConvexRegion R)
    {z₀ d : ℤ × ℤ} (hray : ∀ k : ℕ, z₀ + (k : ℤ) • d ∈ R) :
    ∀ g ∈ R, g + d ∈ R :=
  Nivat.RecessionCone.recession_of_ray hR hray


/-! ## Block 2′: an accumulation point along `v` inherits a Definition 2.11 period of `ϑ|𝒦`
on the half-plane

Paper (`b3_colle2.txt:916`, second sentence): "Since `ϑ|𝒦` is periodic with period parallel
to `ℓ′`, then `z′_per|ℋ(ℓ′_𝒦)` is periodic with period parallel to `ℓ′`."  The period `h`
of `ϑ|𝒦` is in the Definition 2.11 sense (`b3_colle2.txt:367-369`: `ϑ_{g+h} = ϑ_g` for all
`g ∈ 𝒦 ∩ (𝒦 − h)`), which is `Colle41.PeriodOn` unfolded.  `hexh` (block 1) says the
half-plane `{c ≤ dot n ·}` is swallowed by `R = 𝒦` along the orbit direction `v`, and
`dot n h = 0` keeps `z + h` in the half-plane. -/

theorem accPointAlong_periodOn_halfPlane
    {ϑ y : Config ℤ} {R : Set (ℤ × ℤ)} {v n h : ℤ × ℤ} {c : ℤ}
    (hrec : ∀ g ∈ R, g + v ∈ R)
    (hexh : ∀ z, c ≤ LE2.dot n z → ∃ t : ℕ, z + (t : ℤ) • v ∈ R)
    (hnh : LE2.dot n h = 0)
    (hper : ∀ z ∈ R, z + h ∈ R → ϑ (z + h) = ϑ z)
    (hy : Colle3.IsAccPointAlong v ϑ y) :
    ∀ z, c ≤ LE2.dot n z → y (z + h) = y z := by
  classical
  intro z hz
  have hzh : c ≤ LE2.dot n (z + h) := by rw [LE2.dot_add, hnh, add_zero]; exact hz
  obtain ⟨t₁, ht₁⟩ := hexh z hz
  obtain ⟨t₂, ht₂⟩ := hexh (z + h) hzh
  obtain ⟨t, ht, hW⟩ := hy {z, z + h} (max t₁ t₂)
  have hyz : y z = ϑ (z + (t : ℤ) • v) := hW z (Finset.mem_insert_self _ _)
  have hyzh : y (z + h) = ϑ (z + h + (t : ℤ) • v) :=
    hW (z + h) (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  -- both `z + t • v` and `z + h + t • v` lie in `R`
  have hmem : ∀ {w : ℤ × ℤ} {t₀ : ℕ}, w + (t₀ : ℤ) • v ∈ R → t₀ ≤ t → w + (t : ℤ) • v ∈ R := by
    intro w t₀ hw ht₀
    have h := ColleReg.ray_of_recession hrec hw (t - t₀)
    have hcast : (((t - t₀ : ℕ) : ℤ)) = (t : ℤ) - (t₀ : ℤ) := Nat.cast_sub ht₀
    rw [hcast, sub_smul, add_assoc, add_sub_cancel] at h
    exact h
  have h1 : z + (t : ℤ) • v ∈ R := hmem ht₁ (le_trans (Nat.le_max_left _ _) ht)
  have h2 : z + h + (t : ℤ) • v ∈ R := hmem ht₂ (le_trans (Nat.le_max_right _ _) ht)
  rw [hyz, hyzh]
  have e : z + h + (t : ℤ) • v = z + (t : ℤ) • v + h := by abel
  rw [e]
  exact hper _ h1 (e ▸ h2)


/-! ## Block 2″: Claim 4.12 forbids a doubly periodic accumulation point

Paper (`b3_colle2.txt:906-910`, Claim 4.12): "The set `{T^{t v_ℓ′} ϑ : t ∈ ℤ₊}` does not
have fully periodic accumulation points."  The Lean form is the conclusion of
`ColleReg.region_not_periodic` (`RegionSteps.lean:1204-1219`), whose inner clause is
verbatim `Colle3.IsAccPointAlong v ϑ y` and whose `Colle45.IsFullyPeriodic` is
`DoublyPeriodic` by definition. -/

theorem not_doublyPeriodic_of_no_fullyPeriodic_accPoint
    {ϑ y : Config ℤ} {v : ℤ × ℤ}
    (hno : ¬ ∃ y : Config ℤ, Colle45.IsFullyPeriodic y ∧
      ∀ (W : Finset (ℤ × ℤ)) (M : ℕ), ∃ t : ℕ, M ≤ t ∧ ∀ z ∈ W, y z = T ((t : ℤ) • v) ϑ z)
    (hy : Colle3.IsAccPointAlong v ϑ y) : ¬ DoublyPeriodic y :=
  fun hdp => hno ⟨y, hdp, hy⟩


/-! ## Block 7: independent lines have independent normals

Feeds block 6 (`b3_colle2.txt:90`): `ℓ` and `ℓ′` are distinct lines, i.e. their direction
vectors `vl ∥ ℓ`, `vJ ∥ ℓ′` are independent; the normals `ℓ ⊥ vl`, `ℓ′ ⊥ vJ` are then
independent too. -/

theorem det_ne_zero_of_normals {ℓ ℓ' vl vJ : ℤ × ℤ} (hℓ : ℓ ≠ 0) (hℓ' : ℓ' ≠ 0)
    (h1 : LE2.dot ℓ vl = 0) (h2 : LE2.dot ℓ' vJ = 0) (hdet : det vl vJ ≠ 0) :
    det ℓ ℓ' ≠ 0 := by
  intro h0
  -- `ℓ' ∥ ℓ`: `det ℓ ℓ' = 0` with `ℓ ≠ 0` gives `ℓ' ⊥ vl` as well, so `vl ∥ vJ`
  have hℓ'vl : LE2.dot ℓ' vl = 0 := by
    simp only [det, LE2.dot] at h0 h1 ⊢
    -- `ℓ.1 * (ℓ'.1 * vl.1 + ℓ'.2 * vl.2) = ℓ'.1 * (…) + vl.2 * det`, similarly for `ℓ.2`
    have e1 : ℓ.1 * (ℓ'.1 * vl.1 + ℓ'.2 * vl.2) = 0 := by
      linear_combination ℓ'.1 * h1 + vl.2 * h0
    have e2 : ℓ.2 * (ℓ'.1 * vl.1 + ℓ'.2 * vl.2) = 0 := by
      linear_combination ℓ'.2 * h1 - vl.1 * h0
    rcases mul_eq_zero.mp e1 with hl1 | hz
    · rcases mul_eq_zero.mp e2 with hl2 | hz
      · exact absurd (Prod.ext hl1 hl2) hℓ
      · exact hz
    · exact hz
  -- `ℓ' ⊥ vl` and `ℓ' ⊥ vJ` with `ℓ' ≠ 0` force `det vl vJ = 0`
  apply hdet
  simp only [det, LE2.dot] at hℓ'vl h2 ⊢
  have f1 : ℓ'.1 * (vl.1 * vJ.2 - vl.2 * vJ.1) = 0 := by
    linear_combination vJ.2 * hℓ'vl - vl.2 * h2
  have f2 : ℓ'.2 * (vl.1 * vJ.2 - vl.2 * vJ.1) = 0 := by
    linear_combination vl.1 * h2 - vJ.1 * hℓ'vl
  rcases mul_eq_zero.mp f1 with hl1 | hz
  · rcases mul_eq_zero.mp f2 with hl2 | hz
    · exact absurd (Prod.ext hl1 hl2) hℓ'
    · exact hz
  · exact hz


/-! ## Block 5′: Claim 4.13 read in `nexpl`, i.e. the `ℓ′`-half of Claim 4.14

Verbatim (`b3_colle2.txt:916`): "Indeed, let `z′_per` be an accumulation point of
`{T^{t v_ℓ′} ϑ : t ∈ ℤ₊}`.  Since `ϑ|𝒦` is periodic with period parallel to `ℓ′`, then
`z′_per|ℋ(ℓ′_𝒦)` is periodic with period parallel to `ℓ′`.  Thus, Proposition 2.12 implies
that `z′_per` is periodic with period parallel to `ℓ′`, but, according to Claim 4.12, not
fully periodic.  Therefore, from Boyle–Lind Theorem and Proposition 1.8 result that
`−ℓ′, ℓ′ ∈ nexpd(z′_per) ⊂ nexpd(ϑ)`, which proves the claim."  And `b3_colle2.txt:922`,
last sentence: "Therefore, from Claim 4.13 we conclude that `ℓ, ℓ′ ∈ nexpl(ϑ)`."

Dictionary.  `𝒦` is the `(ℓ,ℓ′)`-region of `b3_colle2.txt:904` ("Due to Claim 4.11 and
Lemma 4.1, there exists an `(ℓ,ℓ′)`-region `𝒦 ⊂ Â^(ε)_∞` such that `ϑ|𝒦` is fully periodic
with a period parallel to `ℓ` and another one parallel to `ℓ′`"), given in the shape of
`Colle41.lemma41_colle_region_shape`: lattice-convex, nonempty, a ray along `q ∥ ℓ`
(`hrayq`) and a ray along `vJ ∥ ℓ′` (`hrayv`), and a Definition 2.11 period `h′ ∥ ℓ′` of
`ϑ|𝒦` (`hper'`).  The orbit direction is `vJ = v_ℓ′`, matching the paper's sign.  The line
`ℓ′` is recorded by a primitive normal `ℓ'` (`dot ℓ' vJ = 0`).  The support line `ℓ′_𝒦` is
`dot n′ · = c` with `n′ := det vJ q • (-vJ.2, vJ.1)` and `c := dot n′ z₀'`; only the
half-plane on the `𝒦` side of a line parallel to `ℓ′` through a point of `𝒦` is needed, so
no separate support-line hypothesis is taken.  `hno_fp` is Claim 4.12 (`b3_colle2.txt:906-910`)
in the verbatim shape of the conclusion of `ColleReg.region_not_periodic`
(`RegionSteps.lean:1204-1219`).  The conclusion `ℓ′ ∈ nexpl(ϑ)` is `Colle45.NonExpansiveLine`
(placeholder semantics, `Lemma45.lean:85`). -/

theorem claim414_ellprime {ξ ϑ : Config ℤ} {vJ q ℓ' : ℤ × ℤ} {𝒦 : Set (ℤ × ℤ)}
    (hξ : IsMinimalCounterexample ξ) (hϑ_mem : ϑ ∈ orbitClosure ξ)
    (hK : IsLatticeConvexRegion 𝒦)
    {z₀ z₀' : ℤ × ℤ} (hrayq : ∀ k : ℕ, z₀ + (k : ℤ) • q ∈ 𝒦)
    (hrayv : ∀ k : ℕ, z₀' + (k : ℤ) • vJ ∈ 𝒦)
    (hvJ_ne : vJ ≠ 0) (hdet_qv : det vJ q ≠ 0)
    {h' : ℤ × ℤ} (hh'_ne : h' ≠ 0) (hh'_par : det h' vJ = 0)
    (hper' : ∀ z ∈ 𝒦, z + h' ∈ 𝒦 → ϑ (z + h') = ϑ z)
    (hℓ' : Primitive ℓ') (hℓ'_vJ : LE2.dot ℓ' vJ = 0)
    (hno_fp : ¬ ∃ y : Config ℤ, Colle45.IsFullyPeriodic y ∧
      ∀ (W : Finset (ℤ × ℤ)) (M : ℕ), ∃ t : ℕ, M ≤ t ∧ ∀ z ∈ W, y z = T ((t : ℤ) • vJ) ϑ z) :
    ℓ' ∈ Colle45.NonExpansiveLine ϑ := by
  -- block 0′: rays ⟹ recession directions
  have hrec_q : ∀ g ∈ 𝒦, g + q ∈ 𝒦 := rec_of_rayIn hK hrayq
  have hrec_v : ∀ g ∈ 𝒦, g + vJ ∈ 𝒦 := rec_of_rayIn hK hrayv
  have hz₀' : z₀' ∈ 𝒦 := by simpa using hrayv 0
  -- the normal of the `ℓ′`-support line
  set n' : ℤ × ℤ := det vJ q • (-vJ.2, vJ.1) with hn'
  have hnv : LE2.dot n' vJ = 0 := by
    simp only [hn', LE2.dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
  have hnq : 0 < LE2.dot n' q := by
    have : LE2.dot n' q = det vJ q * det vJ q := by
      simp only [hn', LE2.dot, det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
    rw [this]; exact mul_self_pos.mpr hdet_qv
  have hn'0 : n' ≠ 0 := by
    intro h0
    have h1 : LE2.dot n' q = 0 := by rw [h0]; simp [LE2.dot]
    exact hnq.ne' h1
  have hnh' : LE2.dot n' h' = 0 := by
    have : LE2.dot n' h' = det vJ q * det vJ h' := by
      simp only [hn', LE2.dot, det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
    have e : det vJ h' = 0 := by
      simp only [det] at hh'_par ⊢; linear_combination -hh'_par
    rw [this, e, mul_zero]
  -- block 1 with `(p, v) := (vJ, q)`
  have hexh : ∀ z, LE2.dot n' z₀' ≤ LE2.dot n' z → ∃ t : ℕ, z + (t : ℤ) • vJ ∈ 𝒦 :=
    exists_nat_smul_add_mem_of_dot_le hK hz₀' hvJ_ne hrec_v hrec_q hnv hnq
  -- accumulation point `z′_per` of `{T^{t vJ} ϑ}`
  have hϑfin : (Set.range ϑ).Finite := BL.finite_range_of_mem_orbitClosure hξ.1.1 hϑ_mem
  obtain ⟨y, hy⟩ := Colle3.exists_accPointAlong hϑfin vJ
  have hy_memξ : y ∈ orbitClosure ξ := Colle3.mem_orbitClosure_of_accPointAlong hϑ_mem hy
  have hy_memϑ : y ∈ orbitClosure ϑ :=
    Colle3.mem_orbitClosure_of_accPointAlong (self_mem_orbitClosure ϑ) hy
  -- block 2′: `z′_per|ℋ(ℓ′_𝒦)` has period `h′`
  have hlocal : ∀ z, LE2.dot n' z₀' ≤ LE2.dot n' z → y (z + h') = y z :=
    accPointAlong_periodOn_halfPlane hrec_v hexh hnh' hper' hy
  -- block 2″: Claim 4.12 ⟹ not fully periodic
  have hy_nd : ¬ DoublyPeriodic y := not_doublyPeriodic_of_no_fullyPeriodic_accPoint hno_fp hy
  -- block 3: Proposition 2.12
  obtain ⟨k, hk0, hkh⟩ := exists_zsmul_mem_Per_of_halfPlane_period hξ hy_memξ hn'0 hh'_ne
    hnh' hlocal
  -- `ℓ' ⊥ h'` from `ℓ' ⊥ vJ` and `h' ∥ vJ`
  have hℓ'h' : LE2.dot ℓ' h' = 0 := by
    obtain ⟨k', l, hk', hkl⟩ :=
      Colle.exists_common_multiple_of_det_eq_zero hh'_ne hvJ_ne hh'_par
    have h1 : LE2.dot ℓ' (k' • h') = LE2.dot ℓ' (l • vJ) := by rw [hkl]
    have h2 : LE2.dot ℓ' (k' • h') = k' * LE2.dot ℓ' h' := by
      simp only [LE2.dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
    have h3 : LE2.dot ℓ' (l • vJ) = l * LE2.dot ℓ' vJ := by
      simp only [LE2.dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
    rw [h2, h3, hℓ'_vJ, mul_zero] at h1
    exact (mul_eq_zero.mp h1).resolve_left hk'
  have hperp : LE2.dot ℓ' (k • h') = 0 := by
    have : LE2.dot ℓ' (k • h') = k * LE2.dot ℓ' h' := by
      simp only [LE2.dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
    rw [this, hℓ'h', mul_zero]
  have hkh0 : k • h' ≠ 0 := smul_ne_zero hk0 hh'_ne
  -- block 4 + monotonicity
  have hyfin : (Set.range y).Finite := BL.finite_range_of_mem_orbitClosure hξ.1.1 hy_memξ
  obtain ⟨hℓy, -, -⟩ := mem_nonExpansiveLine_of_period_of_not_doublyPeriodic hyfin hℓ'
    hkh hkh0 hperp hy_nd
  exact nonExpansiveLine_mono_of_mem_orbitClosure hy_memϑ hℓy


end Nivat.Claim414

/-! ## 取证（2026-09-26 去重轮追加，lane-tower-hlev） -/
#print axioms Nivat.Claim414.rec_of_rayIn
