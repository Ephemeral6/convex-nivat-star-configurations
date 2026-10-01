/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.L1CoverStep
import Nivat.External.Colle.L1Data
import Nivat.External.Colle.L1Cut

/-!
# Bridge: `hedge` occupant → `hcover`'s clamped enumeration

原文：`b3_colle2.txt:824/848-856`；消费者 `RegionSteps.lean` 里 `exists_cutResidualR_of_claim46`
的 `hcover := sorry`（`:1786-1793`）。

**Team-lead 2026-09-22 的桥接方案**：`hedge` 只给出 `τ•w+g` 在 gap 行上（`τ`，放置阶段选定的
下界），而 `hcover` 的射线起点是 `t₀ ≥ τ`（调用者给定，可能严格大于 `τ`）。桥接点：
`K := max τ (t₀-1)`——因为 `K ≥ τ`，从 `τ•w+g`（已知在 `Rinf` 上，`hedge` 给）沿 `+w`
再走 `K-τ`（自然数）步、用区域对 `+w` 封闭（`Colle41.IsRegion` 的第三分量 `RayIn Rinf z₀' w`
经 `RecessionCone.recession_of_ray` 得到 `∀z∈Rinf,z+w∈Rinf`），落到 `g+K•w`，且
`dot m w=0` 保持 `cut`-层不变，故它也在 gap 行上；又 `K≥t₀-1`，满足
`exists_clamped_gap_enumeration_of_occupant` 的 `hKt₀` 前提。

`hstep`（Figure 11(B) 的真正几何内容——`Sφ.erase a` 的窗口步进）本桥接**不产生**，作为
显式参数留给调用者按 `L`（截断距离，存在但值依赖 `g/t₀/τ`）逐一提供。
-/

set_option autoImplicit false

namespace Nivat.L1CoverPackage

open Nivat Nivat.LE2 Nivat.L1Region Nivat.ConeRegion Nivat.Colle35 Nivat.Colle41 Nivat.MaxEnv
  Nivat.L1StraddleMax Nivat.ColleReg

/-- **Bridge lemma.** From `hedge`'s occupant fact (`τ•w+g` on the gap row) plus the region's
`+w`-closure and `nℓ`-boundedness (needed by `hbdd_of_bounded` to get a finite row), produces
`hcover`'s Figure 11(B) cover conclusion for a single `N`, given the remaining geometric content
`hstep_all` (quantified over the eventual clamp bound `L`, since `L` is only fixed once the
occupant is pushed to `K := max τ (t₀-1)` and the row-start distance is computed). -/
theorem hcover_of_hedge
    {Rinf : Set (ℤ × ℤ)} {vl w m nℓ : ℤ × ℤ} {c : ℤ}
    {lev : ℕ → ℤ} {N : ℕ}
    {S : Finset (ℤ × ℤ)} {v : ℤ × ℤ} {ε : Bool} {τ : ℤ}
    {Sφ : Finset (ℤ × ℤ)} {a : ℤ × ℤ}
    (hR : Colle41.IsRegion Rinf vl w)
    (hm0 : m ≠ 0) (hmw : dot m w = 0) (hmvl : 0 < dot m vl) (hc : 0 < c)
    (hw_prim : Prim w)
    (hwneg : dot nℓ w < 0) (htop : ∃ top : ℤ, ∀ z ∈ Rinf, dot nℓ z ≤ top)
    (hconsec : ∀ n : ℕ, ∀ z ∈ Rinf, dot m z < lev n → dot m z ≤ lev (n + 1))
    (hlev_mono : lev (N + 1) < lev N)
    (hRinf : ∀ z ∈ Rinf, z + c • vl ∈ Rinf)
    (hedge : ∀ z ∈ S.image (· + v), z ∉ L1Data.derivedQ ε w (S.image (· + v)) →
      τ • w + z ∈ cut Rinf m lev (N + 1) ∧ τ • w + z ∉ cut Rinf m lev N)
    (g : ℤ × ℤ) (hgS : g ∈ S.image (· + v))
    (hgD : g ∉ L1Data.derivedQ ε w (S.image (· + v)))
    (t₀ : ℤ) (_hτt₀ : τ ≤ t₀)
    (hstep_all : ∀ L : ℕ,
      (∀ j : ℕ, (g + (max τ (t₀ - 1)) • w) - (min j L : ℤ) • w ∈ cut Rinf m lev (N + 1)) →
      (∀ j : ℕ, (g + (max τ (t₀ - 1)) • w) - (min j L : ℤ) • w ∉ cut Rinf m lev N) →
      ∀ j : ℕ,
        (g + (max τ (t₀ - 1)) • w) - (min j L : ℤ) • w ∈ cut Rinf m lev (N + 1) →
        (g + (max τ (t₀ - 1)) • w) - (min j L : ℤ) • w ∉ cut Rinf m lev N →
        ∀ b ∈ Sφ.erase a,
          b + ((g + (max τ (t₀ - 1)) • w) - (min j L : ℤ) • w - a) ∈
            overlap (cut Rinf m lev N) (c • vl) ∪ ray g w t₀ ∨
            ∃ j' : ℕ, j' < j ∧
              b + ((g + (max τ (t₀ - 1)) • w) - (min j L : ℤ) • w - a) =
                (g + (max τ (t₀ - 1)) • w) - (min j' L : ℤ) • w) :
    overlap (cut Rinf m lev (N + 1)) (c • vl) ⊆
      genClosure Sφ a (overlap (cut Rinf m lev N) (c • vl) ∪ ray g w t₀) := by
  set K : ℤ := max τ (t₀ - 1) with hK_def
  have hτK : τ ≤ K := le_max_left _ _
  have hKt₀ : t₀ ≤ K + 1 := by
    have : t₀ - 1 ≤ K := le_max_right _ _
    omega
  -- `+w`-closure of the whole region, from the second ray of `Colle41.IsRegion`.
  obtain ⟨z₀', hrayw⟩ := hR.2.2
  have hray : ∀ z ∈ Rinf, z + w ∈ Rinf :=
    Nivat.RecessionCone.recession_of_ray hR.1 hrayw
  -- The `hedge` occupant, pushed forward from `τ` to `K`.
  obtain ⟨hτg_cut, hτg_gap⟩ := hedge g hgS hgD
  obtain ⟨n, hn⟩ : ∃ n : ℕ, K - τ = (n : ℤ) := ⟨(K - τ).toNat, by omega⟩
  have hpush_mem : (τ • w + g) + (n : ℤ) • w ∈ Rinf :=
    add_nsmul_mem hray (τ • w + g) hτg_cut.1 n
  have heqK : g + K • w = (τ • w + g) + (n : ℤ) • w := by
    have hKeq : K = τ + (n : ℤ) := by omega
    rw [hKeq]; module
  have hdot_g_K : dot m (g + K • w) = dot m g := by
    rw [dot_add, dot_zsmul_right, hmw, mul_zero, add_zero]
  have hdot_g_τ : dot m (τ • w + g) = dot m g := by
    rw [dot_add, dot_zsmul_right, hmw, mul_zero, zero_add]
  have heqdot : dot m (g + K • w) = dot m (τ • w + g) := by rw [hdot_g_K, hdot_g_τ]
  have hocc_cut : g + K • w ∈ cut Rinf m lev (N + 1) := by
    refine ⟨?_, ?_⟩
    · rw [heqK]; exact hpush_mem
    · show lev (N + 1) ≤ dot m (g + K • w)
      rw [heqdot]; exact hτg_cut.2
  have hocc_gap : g + K • w ∉ cut Rinf m lev N := by
    intro hcontra
    have hge : lev N ≤ dot m (τ • w + g) := by rw [← heqdot]; exact hcontra.2
    exact hτg_gap ⟨hτg_cut.1, hge⟩
  have hbdd : ∀ z ∈ Rinf, ∃ p ∈ Rinf, ∃ j : ℕ, z = p + (j : ℤ) • w ∧ p - w ∉ Rinf :=
    hbdd_of_bounded hray hwneg htop
  obtain ⟨L, henum_covers, henum_in_cut, henum_gap_only⟩ :=
    exists_clamped_gap_enumeration_of_occupant hray hbdd hm0 hmw hw_prim hlev_mono hconsec
      g t₀ K hKt₀ hocc_cut hocc_gap
  exact cover_of_fig11B_of_rows'' lev N g t₀ K hmvl hc hRinf L henum_covers henum_in_cut
    henum_gap_only (hstep_all L henum_in_cut henum_gap_only)

end Nivat.L1CoverPackage

#print axioms Nivat.L1CoverPackage.hcover_of_hedge
