/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.DecompData
import Nivat.External.Colle.HalfPlaneShells
import Nivat.External.Colle.LatticeEdges

/-!
# Figure 11(B) generator package

原文：b3_colle2.txt:848 "by using that `𝒮_φ` is `η`-generating" and `:856`
"Since `Ŝ_φ` is `η`-generating".

消费者：`RegionSteps.lean` 的 `exists_cutResidualR_of_claim46`（`Sφ a hgen` 三个 binder）。
产自 lane-l1-cover（2026-09-22），集成者复验后落地。
-/

namespace Nivat.L1GenPackage

open Nivat Nivat.LE2 Nivat.Colle

variable {ξ : Config ℤ}

/-- **Figure 11(B) generator package exists.**

原文：b3_colle2.txt:848, :856。`DecompDataZ.isGeneratingSet`（`DecompData.lean`）给出
`𝒮_φ` 是 `η`-generating，`Nivat.Colle.exists_vertex_of_generating`（`HalfPlaneShells.lean`）
在某个顶点 `a` 上给出 `GeneratesAt ξ 𝒮_φ a`。 -/
theorem exists_gen_package (d : Nivat.Colle35.DecompDataZ ξ) :
    ∃ (Sφ : Finset (ℤ × ℤ)) (a : ℤ × ℤ), Nivat.Colle.GeneratesAt ξ Sφ a := by
  have hgen_set : Nivat.Colle.IsGeneratingSet ξ d.toDecompData.Sphi := d.isGeneratingSet
  obtain ⟨a, _, _, hgen_a⟩ := Nivat.Colle.exists_vertex_of_generating hgen_set
  exact ⟨d.toDecompData.Sphi, a, hgen_a⟩

/-- **Sharper generator package pinning `a` at the `-w` end of the `m`-minimal face.**

原文 `:856`：the anchor is the `−w` end of `𝒮_φ`'s lowest face w.r.t. `ℓ'`.
消费者：`RegionSteps.lean:1739-1749`（`exists_cutResidualR_of_claim46` 里的
`obtain ⟨Sφ, a, hgenφ, hSφ, ha_min, ha_end⟩`）。

证法：取字典序极值 `g z = N * dot m z + dot w z`（`N` 足够大以压过 `dot w` 在 `Sφ` 上的
跨度），仿 `exists_vertex_of_generating` 的严格极值不在凸包内的技巧，但换成极小值并用
`m`/`w` 组合的线性泛函；`dot m` 同层的两点相差 `w` 的整数倍，直接由
`det_eq_zero_of_dot_eq_zero` + `exists_smul_of_det_eq_zero`（两个都与同一个非零 `m`
正交则平行）得出，不需要 `RegionCut.lean` 的 `dir`/`face` 机制。 -/
theorem exists_gen_package' (d : Nivat.Colle35.DecompDataZ ξ) {m w vl : ℤ × ℤ}
    (hmw : dot m w = 0) (hwprim : Primitive w) (hmvl : 0 < dot m vl) :
    ∃ (Sφ : Finset (ℤ × ℤ)) (a : ℤ × ℤ), GeneratesAt ξ Sφ a ∧
      Sφ = d.toDecompData.Sphi ∧
      (∀ b ∈ Sφ, dot m a ≤ dot m b) ∧
      (∀ b ∈ Sφ, dot m b = dot m a → ∃ t : ℕ, b = a + (t : ℤ) • w) := by
  classical
  set S : Finset (ℤ × ℤ) := d.toDecompData.Sphi with hSdef
  have hgen_set : Nivat.Colle.IsGeneratingSet ξ S := d.isGeneratingSet
  obtain ⟨hne, hconv, hvert⟩ := hgen_set
  have hwprim' : Prim w := prim_iff_primitive.mpr hwprim
  have hw0 : w ≠ 0 := hwprim'.ne_zero
  have hne' : w.1 ≠ 0 ∨ w.2 ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hw0 (Prod.ext hc.1 hc.2)
  have hww : 0 < dot w w := by
    simp only [dot]
    rcases hne' with h1 | h2
    · have := mul_self_pos.mpr h1
      nlinarith [mul_self_nonneg w.2]
    · have := mul_self_pos.mpr h2
      nlinarith [mul_self_nonneg w.1]
  have hm0 : m ≠ 0 := by
    intro h; rw [h] at hmvl; simp [dot] at hmvl
  have hsamelevel : ∀ p q : ℤ × ℤ, dot m p = dot m q → ∃ t : ℤ, p = q + t • w := by
    intro p q hpq
    have hdotmpq : dot m (p - q) = 0 := by
      simp only [dot, Prod.fst_sub, Prod.snd_sub] at hpq ⊢; linarith [hpq]
    have hdetwpq : det w (p - q) = 0 := det_eq_zero_of_dot_eq_zero hm0 hmw hdotmpq
    obtain ⟨t, ht⟩ := exists_smul_of_det_eq_zero hwprim' hdetwpq
    refine ⟨t, ?_⟩
    have hpq' : p - q = t • w := by
      rw [ht]; exact Prod.ext (by simp) (by simp)
    exact sub_eq_iff_eq_add'.mp hpq'
  have hSney : (S.image (fun z => dot w z)).Nonempty := hne.image _
  set D : ℤ := (S.image (fun z => dot w z)).sup' hSney id -
      (S.image (fun z => dot w z)).inf' hSney id with hD
  set N : ℤ := D + 1 with hN
  obtain ⟨z0, hz0⟩ := id hne
  have hDnn : (0 : ℤ) ≤ D := by
    have h1 := Finset.inf'_le (s := S.image (fun z => dot w z)) (f := id)
      (Finset.mem_image_of_mem (fun z => dot w z) hz0)
    have h2 := Finset.le_sup' (s := S.image (fun z => dot w z)) (f := id)
      (Finset.mem_image_of_mem (fun z => dot w z) hz0)
    rw [hD]; linarith
  have hNpos : (0 : ℤ) < N := by omega
  set g : ℤ × ℤ → ℤ := fun z => N * dot m z + dot w z with hgdef
  have hbnd_of_mem : ∀ p ∈ S, ∀ q ∈ S, |dot w p - dot w q| ≤ D := by
    intro p hp q hq
    have h1 : (S.image (fun z => dot w z)).inf' hSney id ≤ dot w p :=
      Finset.inf'_le (f := id) (Finset.mem_image_of_mem (fun z => dot w z) hp)
    have h2 : dot w p ≤ (S.image (fun z => dot w z)).sup' hSney id :=
      Finset.le_sup' (f := id) (Finset.mem_image_of_mem (fun z => dot w z) hp)
    have h3 : (S.image (fun z => dot w z)).inf' hSney id ≤ dot w q :=
      Finset.inf'_le (f := id) (Finset.mem_image_of_mem (fun z => dot w z) hq)
    have h4 : dot w q ≤ (S.image (fun z => dot w z)).sup' hSney id :=
      Finset.le_sup' (f := id) (Finset.mem_image_of_mem (fun z => dot w z) hq)
    rw [abs_le]; rw [hD]; constructor <;> linarith
  have hginj : ∀ p ∈ S, ∀ q ∈ S, g p = g q → p = q := by
    intro p hp q hq heq
    by_contra hnepq
    by_cases hmeq : dot m p = dot m q
    · have hweq : dot w p = dot w q := by simp only [hgdef, hmeq] at heq; linarith
      obtain ⟨t, ht⟩ := hsamelevel p q hmeq
      have hpqw : p - q = t • w := by rw [ht]; abel
      have hdw0 : dot w (p - q) = 0 := by
        simp only [dot, Prod.fst_sub, Prod.snd_sub]; simp only [dot] at hweq; linarith
      rw [hpqw] at hdw0
      have ht0 : t = 0 := by
        have hteq : t * dot w w = 0 := by
          simp only [dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at hdw0 ⊢
          nlinarith [hdw0]
        rcases mul_eq_zero.mp hteq with h | h
        · exact h
        · exact absurd h (by linarith)
      apply hnepq
      rw [ht, ht0]; simp
    · have hbound : |dot w q - dot w p| ≤ D := hbnd_of_mem q hq p hp
      have heq' : N * (dot m p - dot m q) = dot w q - dot w p := by
        simp only [hgdef] at heq; linarith
      have hd1 : (1 : ℤ) ≤ |dot m p - dot m q| := Int.one_le_abs (sub_ne_zero.mpr hmeq)
      have hNle : N ≤ |N * (dot m p - dot m q)| := by
        rw [abs_mul, abs_of_pos hNpos]
        calc N = N * 1 := (mul_one N).symm
        _ ≤ N * |dot m p - dot m q| := mul_le_mul_of_nonneg_left hd1 (le_of_lt hNpos)
      rw [heq'] at hNle
      omega
  obtain ⟨a, ha, hmin⟩ := Finset.exists_min_image S g hne
  have ha_min : ∀ b ∈ S, dot m a ≤ dot m b := by
    intro b hb
    by_contra hlt
    push_neg at hlt
    have hge1 : (1 : ℤ) ≤ dot m a - dot m b := by omega
    have hbnd := hbnd_of_mem a ha b hb
    have hgab : g a - g b = N * (dot m a - dot m b) + (dot w a - dot w b) := by
      simp only [hgdef]; ring
    have hcontra : g b < g a := by
      have h5 := (abs_le.mp hbnd).1
      nlinarith [hgab, hge1]
    exact absurd (hmin b hb) (by omega)
  refine ⟨S, a, ?_, hSdef.symm, ha_min, ?_⟩
  · refine hvert a ha ?_
    have hstrict : ∀ b ∈ S.erase a, g a < g b := by
      intro b hb
      obtain ⟨hba, hbS⟩ := Finset.mem_erase.mp hb
      refine lt_of_le_of_ne (hmin b hbS) (fun h => hba ?_)
      exact (hginj a ha b hbS h).symm
    set G : (ℝ × ℝ) →ₗ[ℝ] ℝ :=
      (N : ℝ) • ((m.1 : ℝ) • LinearMap.fst ℝ ℝ ℝ + (m.2 : ℝ) • LinearMap.snd ℝ ℝ ℝ) +
        ((w.1 : ℝ) • LinearMap.fst ℝ ℝ ℝ + (w.2 : ℝ) • LinearMap.snd ℝ ℝ ℝ) with hGdef
    have hGtoReal : ∀ z : ℤ × ℤ, G (toReal z) = (g z : ℝ) := by
      intro z
      simp only [hGdef, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.fst_apply,
        LinearMap.snd_apply, smul_eq_mul, toReal, hgdef, dot]
      push_cast; ring
    have haux : toReal a ∉ Conv (S.erase a) := by
      intro hmem
      have himg : Conv (S.erase a) =
          convexHull ℝ (((S.erase a).image toReal : Finset (ℝ × ℝ)) : Set (ℝ × ℝ)) := by
        rw [Conv, Finset.coe_image]
      rw [himg] at hmem
      obtain ⟨wt, hwt0, hwt1, hwtsum⟩ := Finset.mem_convexHull'.mp hmem
      have hwt1' : ∑ b ∈ S.erase a, wt (toReal b) = 1 := by
        rwa [Finset.sum_image (fun x _ y _ h => toReal_injective h)] at hwt1
      have hwtsum' : ∑ b ∈ S.erase a, wt (toReal b) • toReal b = toReal a := by
        rwa [Finset.sum_image (fun x _ y _ h => toReal_injective h)] at hwtsum
      have hGsum : ∑ b ∈ S.erase a, wt (toReal b) * G (toReal b) = G (toReal a) := by
        rw [← hwtsum', map_sum]
        refine Finset.sum_congr rfl (fun b _ => ?_)
        rw [map_smul, smul_eq_mul]
      have hge : ∀ b ∈ S.erase a, wt (toReal b) * G (toReal a) ≤ wt (toReal b) * G (toReal b) := by
        intro b hb
        have hGb : G (toReal a) ≤ G (toReal b) := by
          rw [hGtoReal, hGtoReal]; exact_mod_cast (hstrict b hb).le
        exact mul_le_mul_of_nonneg_left hGb (hwt0 (toReal b) (Finset.mem_image_of_mem _ hb))
      have hex : ∃ b ∈ S.erase a, 0 < wt (toReal b) := by
        by_contra hcon
        push_neg at hcon
        have hall0 : ∀ b ∈ S.erase a, wt (toReal b) = 0 := fun b hb =>
          le_antisymm (hcon b hb) (hwt0 (toReal b) (Finset.mem_image_of_mem _ hb))
        rw [Finset.sum_congr rfl hall0] at hwt1'
        simp at hwt1'
      have hgt : ∃ b ∈ S.erase a, wt (toReal b) * G (toReal a) < wt (toReal b) * G (toReal b) := by
        obtain ⟨b0, hb0, hb0pos⟩ := hex
        refine ⟨b0, hb0, ?_⟩
        have hGb0 : G (toReal a) < G (toReal b0) := by
          rw [hGtoReal, hGtoReal]; exact_mod_cast hstrict b0 hb0
        exact mul_lt_mul_of_pos_left hGb0 hb0pos
      have hcontra : G (toReal a) < G (toReal a) := by
        calc G (toReal a) = ∑ b ∈ S.erase a, wt (toReal b) * G (toReal a) := by
              rw [← Finset.sum_mul, hwt1', one_mul]
        _ < ∑ b ∈ S.erase a, wt (toReal b) * G (toReal b) := Finset.sum_lt_sum hge hgt
        _ = G (toReal a) := hGsum
      exact lt_irrefl _ hcontra
    intro z hz
    have hzS : z ∈ S :=
      hconv z (convexHull_mono (Set.image_mono (S.erase_subset a)) hz)
    have hzne : z ≠ a := by
      intro h; subst h; exact haux hz
    exact Finset.mem_erase.mpr ⟨hzne, hzS⟩
  · intro b hb hmb
    obtain ⟨t, ht⟩ := hsamelevel b a hmb
    have hweq : dot w b - dot w a = t * dot w w := by
      have hdw : dot w (b - a) = dot w (t • w) := by
        rw [show b - a = t • w by rw [ht]; abel]
      simp only [dot, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd,
        smul_eq_mul] at hdw
      simp only [dot] at hdw ⊢
      linarith [hdw]
    have hge : g a ≤ g b := hmin b hb
    have hwge : dot w a ≤ dot w b := by
      simp only [hgdef, hmb] at hge
      linarith
    have ht0 : 0 ≤ t := by
      by_contra hlt
      push_neg at hlt
      have hneg : t * dot w w < 0 := mul_neg_of_neg_of_pos hlt hww
      linarith [hweq, hwge]
    exact ⟨t.toNat, by rw [ht, Int.toNat_of_nonneg ht0]⟩

end Nivat.L1GenPackage

#print axioms Nivat.L1GenPackage.exists_gen_package
#print axioms Nivat.L1GenPackage.exists_gen_package'
