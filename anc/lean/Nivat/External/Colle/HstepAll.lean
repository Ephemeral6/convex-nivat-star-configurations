/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.L1CoverStep

/-!
# Figure 11(B) window step, from an abstract "room" fact

原文：`b3_colle2.txt:856`。消费者：`L1CoverBridge.lean` 的 `hcover_of_hedge` 的 `hstep_all` 参数，
最终目标是 `RegionSteps.lean` 里 `hcover` 构造中留下的 `(by sorry)`。

**`hroom`（lane-tower 供给，2026-09-22 协商中）**：行上任意一点（在 `Rinf` 里、`dot m` 层恰为
`lev(N+1)`）加上 `Sφ − a` 里任意一个 `dot m`-方向严格为正的向量，仍落在 `Rinf` 里。这是
Figure 11(B) 里 `Sφ` 在顶点 `a` 处的扇形锥（`w` 与相邻边方向）跟 `Rinf` 在行首附近的切锥重合
这一几何事实的抽象化。

给定 `hroom`，`hstep_all` 的证明纯是代数：对 `b ∈ Sφ.erase a`，令 `u := b − a`。
* `dot m u = 0`：`ha_end` 给 `u = t•w`（`t ≥ 1`，因为 `b ≠ a`），纯 `w`-移位；按 `t` 与
  `min j L` 的大小分两支——要么落在更早的枚举点，要么落进 `ray g w t₀`。
* `dot m u > 0`：`hroom` 直接给 `p + u ∈ Rinf`；配合 `hconsec` 把 `dot m` 层顶到 `≥ lev N`，
  加上 `hRinf'`（`c•vl`-封闭）把 `p+u+c•vl` 也顶进 `cut N`，落进 `overlap`。
-/

set_option autoImplicit false

namespace Nivat.L1CoverPackage

open Nivat Nivat.LE2 Nivat.L1Region Nivat.ConeRegion Nivat.Colle35 Nivat.Colle41 Nivat.MaxEnv
  Nivat.L1StraddleMax

variable {Rinf : Set (ℤ × ℤ)} {vl w m : ℤ × ℤ} {c : ℤ} {lev : ℕ → ℤ} {N : ℕ}
  {Sφ : Finset (ℤ × ℤ)} {a : ℤ × ℤ}

/-- **Figure 11(B) window step**, from an abstract "room" fact `hroom` (lane-tower). -/
theorem step_all_of_hroom
    (_hmw : dot m w = 0) (hmvl : 0 < dot m vl) (hc : 0 < c)
    (hconsec : ∀ n : ℕ, ∀ z ∈ Rinf, dot m z < lev n → dot m z ≤ lev (n + 1))
    (hRinf' : ∀ z ∈ Rinf, z + c • vl ∈ Rinf)
    (ha_min : ∀ b ∈ Sφ, dot m a ≤ dot m b)
    (ha_end : ∀ b ∈ Sφ, dot m b = dot m a → ∃ t : ℕ, b = a + (t : ℤ) • w)
    (g : ℤ × ℤ) (τ t₀ : ℤ)
    -- Round 149: was `∀ p ∈ Rinf, dot m p = lev (N+1) → …`, i.e. over the whole row.  The proof
    -- uses it at one shape only, `(g + K • w) - (k : ℤ) • w`, so the row-wide quantifier was ours,
    -- not Collé's (`:826` is a *selection* condition on placements).  `OPEN.md` #13.
    (hroom : ∀ k : ℤ, 0 ≤ k →
      (g + (max τ (t₀ - 1)) • w) - k • w ∈ Rinf →
      dot m ((g + (max τ (t₀ - 1)) • w) - k • w) = lev (N + 1) →
      ∀ b ∈ Sφ, 0 < dot m (b - a) →
        ((g + (max τ (t₀ - 1)) • w) - k • w) + (b - a) ∈ Rinf) :
    ∀ L : ℕ,
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
                (g + (max τ (t₀ - 1)) • w) - (min j' L : ℤ) • w := by
  intro L hcutN1 hgap j hcutN1_j hgap_j b hb_erase
  set K : ℤ := max τ (t₀ - 1) with hK_def
  have hb : b ∈ Sφ := Finset.mem_of_mem_erase hb_erase
  have hb_ne : b ≠ a := Finset.ne_of_mem_erase hb_erase
  set p : ℤ × ℤ := (g + K • w) - (min j L : ℤ) • w with hp_def
  have hp_mem : p ∈ Rinf := hcutN1_j.1
  have hp_lev : dot m p = lev (N + 1) := by
    have hgapband : lev (N + 1) ≤ dot m p ∧ dot m p < lev N := by
      refine ⟨hcutN1_j.2, ?_⟩
      by_contra hcon
      push_neg at hcon
      exact hgap_j ⟨hp_mem, hcon⟩
    exact le_antisymm (hconsec N p hp_mem hgapband.2) hgapband.1
  set u : ℤ × ℤ := b - a with hu_def
  have hu_nonneg : 0 ≤ dot m u := by
    have hle := ha_min b hb
    have hsub : dot m u = dot m b - dot m a := by rw [hu_def, dot_sub]
    omega
  rcases eq_or_lt_of_le hu_nonneg with heq | hpos
  · -- `dot m u = 0`: pure `w`-arithmetic.
    have hdba : dot m b = dot m a := by
      have hsub : dot m u = dot m b - dot m a := by rw [hu_def, dot_sub]
      omega
    obtain ⟨t, ht⟩ := ha_end b hb hdba
    have hu_eq : u = (t : ℤ) • w := by rw [hu_def, ht]; module
    have ht_pos : 1 ≤ t := by
      rcases Nat.eq_zero_or_pos t with h0 | hpos'
      · exact absurd (by rw [ht, h0]; simp) hb_ne
      · exact hpos'
    by_cases hcase : (t : ℤ) ≤ (min j L : ℤ)
    · -- earlier in the enumeration.
      right
      have htL : t ≤ min j L := by exact_mod_cast hcase
      refine ⟨min j L - t, ?_, ?_⟩
      · have hle : min j L ≤ j := min_le_left _ _
        omega
      · have hval : (min ((min j L - t : ℕ) : ℤ) (L : ℤ)) = (min j L : ℤ) - (t : ℤ) := by omega
        rw [hval, hp_def]
        have hexpand : b + ((g + K • w) - (min j L : ℤ) • w - a)
            = (g + K • w) + (u - (min j L : ℤ) • w) := by rw [hu_def]; module
        rw [hexpand, hu_eq]
        module
    · -- ahead of `base0`: lands in the ray.
      left; right
      push_neg at hcase
      have htL' : (min j L : ℤ) < (t : ℤ) := hcase
      refine ⟨K + (t : ℤ) - (min j L : ℤ), ?_, ?_⟩
      · have hKt₀ : t₀ - 1 ≤ K := le_max_right _ _
        omega
      · show b + ((g + K • w) - (min j L : ℤ) • w - a) = (K + (t : ℤ) - (min j L : ℤ)) • w + g
        have hexpand : b + ((g + K • w) - (min j L : ℤ) • w - a)
            = (g + K • w) + (u - (min j L : ℤ) • w) := by rw [hu_def]; module
        rw [hexpand, hu_eq]
        module
  · -- `dot m u > 0`: room.
    left; left
    have hp_mem' : (g + K • w) - (min j L : ℤ) • w ∈ Rinf := by rw [← hp_def]; exact hp_mem
    have hp_lev' : dot m ((g + K • w) - (min j L : ℤ) • w) = lev (N + 1) := by
      rw [← hp_def]; exact hp_lev
    have hp_mem_u : p + u ∈ Rinf := by
      rw [hp_def]
      exact hroom (min j L : ℤ) (le_min (Int.natCast_nonneg j) (Int.natCast_nonneg L))
        hp_mem' hp_lev' b hb hpos
    have hdot_gt : lev (N + 1) < dot m (p + u) := by
      have : dot m (p + u) = dot m p + dot m u := dot_add m p u
      omega
    have hdot_geN : lev N ≤ dot m (p + u) := by
      by_contra hcon
      push_neg at hcon
      have hle := hconsec N (p + u) hp_mem_u hcon
      omega
    have hcutN_mem : p + u ∈ cut Rinf m lev N := ⟨hp_mem_u, hdot_geN⟩
    have hshift_mem : p + u + c • vl ∈ Rinf := hRinf' (p + u) hp_mem_u
    have hdot_shift_eq : dot m (p + u + c • vl) = dot m (p + u) + c * dot m vl := by
      rw [dot_add, dot_zsmul_right]
    have hdot_shift_pos : 0 < c * dot m vl := mul_pos hc hmvl
    have hcutN_mem2 : p + u + c • vl ∈ cut Rinf m lev N := by
      refine ⟨hshift_mem, ?_⟩
      show lev N ≤ dot m (p + u + c • vl)
      rw [hdot_shift_eq]
      linarith [hdot_geN, hdot_shift_pos]
    have hb_target : b + (p - a) = p + u := by rw [hu_def]; module
    show b + ((g + K • w) - (min j L : ℤ) • w - a) ∈ overlap (cut Rinf m lev N) (c • vl)
    rw [← hp_def, hb_target]
    exact ⟨hcutN_mem, hcutN_mem2⟩

end Nivat.L1CoverPackage

#print axioms Nivat.L1CoverPackage.step_all_of_hroom
