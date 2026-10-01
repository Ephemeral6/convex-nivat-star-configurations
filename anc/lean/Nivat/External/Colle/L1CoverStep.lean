/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.L1CoverPackage
import Nivat.External.Colle.L1CoverEnum
import Nivat.External.Colle.RecessionCone

/-!
# Figure 11(B) cover theorem, clamped enumeration for a single bounded-backward row

原文：同 `L1CoverPackage.cover_of_fig11B_of_rows'`（`b3_colle2.txt:856`）。

**问题（lane-chain, 2026-09-22）**：`cover_of_fig11B_of_rows'` 的 `enum i j := base i −
(j:ℤ)•w` 要求 `henum_in_cut`/`henum_gap_only` 对**所有** `j : ℕ` 成立；但 `dot m w = 0` 使
`dot m (base i − j•w)` 与 `j` 无关，配合 gap 恰一行（`gap_height_eq_of_consec`）把它钉死在
`lev(N+1)`，于是这两条合起来要求 `base i − j•w` 对一切 `j` 都留在 `Rinf` 里——但
`hbdd_of_bounded`（同一行的「行首」事实）恰恰说这条 `w`-行只在 `+w` 方向无界、`−w` 方向在
行首 `p` 被挡住（`p − w ∉ Rinf`）。固定的 `base i` 沿 `−w` 无限后退必然在有限步内越过 `p`，
矛盾。

**修法（team-lead, 2026-09-22）**：把位移量截断在行首距离 `L`：
`enum j := base0 − (min j L : ℤ) • w`，`j ≥ L` 时钉在行首 `p`（仍是 gap 点，因为整条行都在
gap 里），不再需要 `j` 无界成立。`base0 := g + (t₀ − 1)•w`——恰好在 `ray g w t₀` 之前一步，
所以行上「`base0` 及其后」的部分已经由 `ray g w t₀ ⊆ D` 直接覆盖，只需要枚举「`base0` 之前」
到行首 `p` 的有限段。

本文件：
1. `m ≠ 0`（免于要求 `Prim m`）版本的 `same_level_iff_on_wline` / `at_most_one_row_start_per_level`
   （`L1CoverEnum.lean` 的版本要 `Prim m`，`RegionSteps.lean` 的塔包 `obtain` 没有提供这条，
   只有 `0 < dot m vl` ⟹ `m ≠ 0`）。
2. `exists_clamped_gap_enumeration_of_occupant`：从一个已知的行上占位点（`hedge` 将来提供）
   构造 `L` 与截断枚举的三条性质。
3. `cover_of_fig11B_of_rows''`：截断版 Figure 11(B) 覆盖定理，`henum_covers` 额外排除
   `ray g w t₀`（该部分已经在 `D` 里，不需要 `base0` 侧的枚举来源）。
-/

set_option autoImplicit false

namespace Nivat.L1CoverPackage

open Nivat Nivat.LE2 Nivat.L1Region Nivat.ConeRegion Nivat.Colle35 Nivat.Colle41 Nivat.MaxEnv
  Nivat.L1StraddleMax

variable {Rinf : Set (ℤ × ℤ)} {m w : ℤ × ℤ} {lev : ℕ → ℤ} {N : ℕ}

/-! ## §1. `m ≠ 0` variants (no `Prim m` needed) -/

/-- `same_level_iff_on_wline`, but only assuming `m ≠ 0` (not full `Prim m`) — `det_eq_zero_of_dot_eq_zero`
only ever needed `m ≠ 0`, `Prim m` was only used for `.ne_zero`. -/
theorem same_level_iff_on_wline_of_ne_zero
    (hm0 : m ≠ 0) (hmw : dot m w = 0) (hw_prim : Prim w)
    {z z' : ℤ × ℤ} (hlev : dot m z = dot m z') :
    ∃ k : ℤ, z' = z + k • w := by
  have hdot : dot m (z' - z) = 0 := by
    rw [dot_sub, hlev]; ring
  have hdet : det w (z' - z) = 0 :=
    det_eq_zero_of_dot_eq_zero hm0 hmw hdot
  obtain ⟨k, hk⟩ := exists_smul_of_det_eq_zero hw_prim hdet
  refine ⟨k, ?_⟩
  have hk' : z' - z = k • w := hk
  rw [← hk']; ring

/-- `at_most_one_row_start_per_level`, `m ≠ 0` variant. -/
theorem at_most_one_row_start_per_level_of_ne_zero
    (hm0 : m ≠ 0) (hmw : dot m w = 0) (hw_prim : Prim w)
    (hray : ∀ z ∈ Rinf, z + w ∈ Rinf)
    {p p' : ℤ × ℤ}
    (hp : p ∈ Rinf) (hp_start : p - w ∉ Rinf)
    (hp' : p' ∈ Rinf) (hp'_start : p' - w ∉ Rinf)
    (hlev : dot m p = dot m p') :
    p = p' := by
  obtain ⟨k, hk⟩ := same_level_iff_on_wline_of_ne_zero hm0 hmw hw_prim hlev
  by_cases hk_zero : k = 0
  · rw [hk_zero, zero_smul, add_zero] at hk
    exact hk.symm
  · by_cases hk_pos : 0 < k
    · have hk_nat : ∃ n : ℕ, 1 ≤ n ∧ k = (n : ℤ) := ⟨k.toNat, by omega, by omega⟩
      obtain ⟨n, hn_ge, hk_eq⟩ := hk_nat
      have hcast : (n : ℤ) - 1 = ((n - 1 : ℕ) : ℤ) := by omega
      have heq0 : p' - w = p + ((n : ℤ) - 1) • w := by rw [hk, hk_eq]; ring
      have heq : p' - w = p + ((n - 1 : ℕ) : ℤ) • w := by rw [heq0, hcast]
      have hp'_w : p' - w ∈ Rinf := by rw [heq]; exact add_nsmul_mem hray p hp (n - 1)
      exact absurd hp'_w hp'_start
    · have hk_nat : ∃ n : ℕ, 1 ≤ n ∧ -k = (n : ℤ) := ⟨(-k).toNat, by omega, by omega⟩
      obtain ⟨n, hn_ge, hkeq⟩ := hk_nat
      have hcast : (n : ℤ) - 1 = ((n - 1 : ℕ) : ℤ) := by omega
      have hp_eq : p = p' + (-k) • w := by rw [hk]; ring
      have heq0 : p - w = p' + ((n : ℤ) - 1) • w := by rw [hp_eq, hkeq]; ring
      have heq : p - w = p' + ((n - 1 : ℕ) : ℤ) • w := by rw [heq0, hcast]
      have hp_w : p - w ∈ Rinf := by rw [heq]; exact add_nsmul_mem hray p' hp' (n - 1)
      exact absurd hp_w hp_start

/-! ## §2. Clamped enumeration from one occupant point -/

/-- **Clamped gap enumeration from a single known occupant point.**

Given `base0 := g + K•w`, already known to be on the gap row (`hocc_cut`/`hocc_gap`), where
`K` is only required to reach at least as far as `t₀ - 1` (`hKt₀`, so the known occupant is not
strictly behind where `ray g w t₀` starts), every gap point NOT already in `ray g w t₀` is
`base0 - (min j L : ℤ) • w` for some `j : ℕ` and a fixed `L : ℕ` (the distance from `base0`
back to the row start), and every such clamped point stays a genuine gap point (for all `j`,
including `j ≥ L` where it is pinned at the row start). -/
theorem exists_clamped_gap_enumeration_of_occupant
    (hray : ∀ z ∈ Rinf, z + w ∈ Rinf)
    (hbdd : ∀ z ∈ Rinf, ∃ p ∈ Rinf, ∃ j : ℕ, z = p + (j : ℤ) • w ∧ p - w ∉ Rinf)
    (hm0 : m ≠ 0) (hmw : dot m w = 0) (hw_prim : Prim w)
    (hlev_mono : lev (N + 1) < lev N)
    (hconsec : ∀ n : ℕ, ∀ z ∈ Rinf, dot m z < lev n → dot m z ≤ lev (n + 1))
    (g : ℤ × ℤ) (t₀ K : ℤ) (hKt₀ : t₀ ≤ K + 1)
    (hocc_cut : g + K • w ∈ cut Rinf m lev (N + 1))
    (hocc_gap : g + K • w ∉ cut Rinf m lev N) :
    ∃ L : ℕ,
      (∀ z ∈ cut Rinf m lev (N + 1), z ∉ cut Rinf m lev N → z ∉ ray g w t₀ →
        ∃ j : ℕ, z = (g + K • w) - (min j L : ℤ) • w) ∧
      (∀ j : ℕ, (g + K • w) - (min j L : ℤ) • w ∈ cut Rinf m lev (N + 1)) ∧
      (∀ j : ℕ, (g + K • w) - (min j L : ℤ) • w ∉ cut Rinf m lev N) := by
  set base0 : ℤ × ℤ := g + K • w with hbase0_def
  have hbase0_mem : base0 ∈ Rinf := hocc_cut.1
  obtain ⟨p, hp_mem, L, hbase0_eq, hp_start⟩ := hbdd base0 hbase0_mem
  have hbase0_lev : dot m base0 = lev (N + 1) :=
    gap_height_eq_of_consec hconsec hbase0_mem hocc_cut.2
      (by
        by_contra hcon
        push Not at hcon
        exact hocc_gap ⟨hbase0_mem, hcon⟩)
  have hp_lev : dot m p = lev (N + 1) := by
    have : dot m p = dot m base0 := by
      rw [hbase0_eq, dot_add, dot_zsmul_right, hmw, mul_zero, add_zero]
    rw [this, hbase0_lev]
  refine ⟨L, ?_, ?_, ?_⟩
  · -- coverage
    intro z hz_cutN1 hz_gap hz_nray
    have hz_mem : z ∈ Rinf := hz_cutN1.1
    obtain ⟨pz, hpz_mem, jz, hz_eq, hpz_start⟩ := hbdd z hz_mem
    have hz_lev : dot m z = lev (N + 1) :=
      gap_height_eq_of_consec hconsec hz_mem hz_cutN1.2
        (by
          by_contra hcon
          push Not at hcon
          exact hz_gap ⟨hz_mem, hcon⟩)
    have hpz_lev : dot m pz = lev (N + 1) := by
      have : dot m pz = dot m z := by
        rw [hz_eq, dot_add, dot_zsmul_right, hmw, mul_zero, add_zero]
      rw [this, hz_lev]
    have hpz_eq_p : pz = p :=
      at_most_one_row_start_per_level_of_ne_zero hm0 hmw hw_prim hray hpz_mem hpz_start hp_mem
        hp_start (by rw [hpz_lev, hp_lev])
    -- z = p + jz • w = base0 - L•w + jz•w
    have hz_eq' : z = base0 + ((jz : ℤ) - (L : ℤ)) • w := by
      have e1 : z = p + (jz : ℤ) • w := by rw [← hpz_eq_p]; exact hz_eq
      have e2 : base0 = p + (L : ℤ) • w := hbase0_eq
      rw [e1, e2]; ring
    by_cases hle : jz ≤ L
    · refine ⟨L - jz, ?_⟩
      have hmin : (min ((L - jz : ℕ) : ℤ) (L : ℤ)) = (L : ℤ) - (jz : ℤ) := by omega
      rw [hz_eq', hmin]
      module
    · exfalso
      apply hz_nray
      refine ⟨K + (jz : ℤ) - (L : ℤ), by omega, ?_⟩
      show z = (K + (jz : ℤ) - (L : ℤ)) • w + g
      rw [hz_eq', hbase0_def]
      module
  · -- henum_in_cut
    intro j
    have hmem : base0 - (min j L : ℤ) • w ∈ Rinf := by
      have heq : base0 - (min (j : ℕ) L : ℤ) • w
          = p + ((L - min j L : ℕ) : ℤ) • w := by
        have hle : min j L ≤ L := min_le_right _ _
        have hcast : (L : ℤ) - (min j L : ℤ) = ((L - min j L : ℕ) : ℤ) := by omega
        rw [hbase0_eq, ← hcast]
        module
      rw [heq]
      exact add_nsmul_mem hray p hp_mem (L - min j L)
    refine ⟨hmem, ?_⟩
    have heq : dot m (base0 - (min j L : ℤ) • w) = dot m base0 := by
      rw [dot_sub, dot_zsmul_right, hmw, mul_zero, sub_zero]
    show lev (N + 1) ≤ dot m (base0 - (min j L : ℤ) • w)
    rw [heq, hbase0_lev]
  · -- henum_gap_only
    intro j hcontra
    have heq : dot m (base0 - (min j L : ℤ) • w) = dot m base0 := by
      rw [dot_sub, dot_zsmul_right, hmw, mul_zero, sub_zero]
    have hge : lev N ≤ dot m base0 := by
      rw [← heq]
      exact hcontra.2
    rw [hbase0_lev] at hge
    omega

/-! ## §3. Clamped Figure 11(B) cover theorem -/

/-- **Figure 11(B) cover theorem, clamped leftward enumeration.**

Same conclusion as `cover_of_fig11B_of_rows'`, but the enumeration is a single row anchored at
`base0 := g + (t₀-1)•w` (one step before `ray g w t₀`) and clamped at distance `L` from the row
start; `henum_covers` only needs to place gap points *not already in* `ray g w t₀`, since those
are covered by `D` directly. -/
theorem cover_of_fig11B_of_rows''
    {Sφ : Finset (ℤ × ℤ)} {a : ℤ × ℤ}
    {Rinf : Set (ℤ × ℤ)} {w vl : ℤ × ℤ} {c : ℤ}
    {m : ℤ × ℤ}
    (lev : ℕ → ℤ) (N : ℕ)
    (g : ℤ × ℤ) (t₀ K : ℤ)
    (hmvl : 0 < dot m vl) (hc : 0 < c)
    (hRinf : ∀ z ∈ Rinf, z + c • vl ∈ Rinf)
    (L : ℕ)
    (henum_covers : ∀ z ∈ cut Rinf m lev (N + 1), z ∉ cut Rinf m lev N → z ∉ ray g w t₀ →
      ∃ j : ℕ, z = (g + K • w) - (min j L : ℤ) • w)
    (henum_in_cut : ∀ j : ℕ,
      (g + K • w) - (min j L : ℤ) • w ∈ cut Rinf m lev (N + 1))
    (henum_gap_only : ∀ j : ℕ,
      (g + K • w) - (min j L : ℤ) • w ∉ cut Rinf m lev N)
    (hstep : ∀ j : ℕ,
      (g + K • w) - (min j L : ℤ) • w ∈ cut Rinf m lev (N + 1) →
      (g + K • w) - (min j L : ℤ) • w ∉ cut Rinf m lev N →
      ∀ b ∈ Sφ.erase a,
        b + ((g + K • w) - (min j L : ℤ) • w - a) ∈
          overlap (cut Rinf m lev N) (c • vl) ∪ ray g w t₀ ∨
          ∃ j' : ℕ, j' < j ∧
            b + ((g + K • w) - (min j L : ℤ) • w - a) =
              (g + K • w) - (min j' L : ℤ) • w) :
    overlap (cut Rinf m lev (N + 1)) (c • vl) ⊆
      genClosure Sφ a (overlap (cut Rinf m lev N) (c • vl) ∪ ray g w t₀) := by
  set D := overlap (cut Rinf m lev N) (c • vl) ∪ ray g w t₀
  set K' := overlap (cut Rinf m lev (N + 1)) (c • vl)
  set enum : ℕ → ℕ → ℤ × ℤ := fun _ j => (g + K • w) - (min j L : ℤ) • w with henum_def

  have hoverlap_lift : ∀ z, z ∈ cut Rinf m lev N →
      z ∈ overlap (cut Rinf m lev (N + 1)) (c • vl) →
      z ∈ overlap (cut Rinf m lev N) (c • vl) :=
    overlap_lift_of_pos lev N hmvl hc hRinf

  have hwindow : ∀ i j : ℕ, ∀ z ∈ Sφ.erase a,
      z + (enum i j - a) ∈
        D ∪ (⋃ i' ∈ {i' : ℕ | i' < i}, Set.range (enum i'))
          ∪ (enum i '' {j' : ℕ | j' < j}) := by
    intro i j z hz
    show z + (enum i j - a) ∈
        D ∪ (⋃ i' ∈ {i' : ℕ | i' < i}, Set.range (enum i'))
          ∪ (enum i '' {j' : ℕ | j' < j})
    by_cases hcut : enum i j ∈ cut Rinf m lev N
    · exfalso
      exact henum_gap_only j hcut
    · have hcutN1 := henum_in_cut j
      have hstep_ij := hstep j hcutN1 hcut z hz
      rcases hstep_ij with h1 | ⟨j', hj', heq⟩
      · left; left; exact h1
      · right
        simp only [Set.mem_image, Set.mem_ofPred_eq]
        exact ⟨j', hj', heq.symm⟩

  have hcovers : K' ⊆ D ∪ (⋃ i, Set.range (enum i)) := by
    intro z hz
    have hz_cutN1 : z ∈ cut Rinf m lev (N + 1) := hz.1
    by_cases hzN : z ∈ cut Rinf m lev N
    · left; left
      exact hoverlap_lift z hzN hz
    · by_cases hzray : z ∈ ray g w t₀
      · left; right; exact hzray
      · obtain ⟨j, heq⟩ := henum_covers z hz_cutN1 hzN hzray
        right
        simp only [Set.mem_iUnion, Set.mem_range]
        exact ⟨0, j, heq.symm⟩

  exact Nivat.L3Cover.subset_genClosure_of_window_of_covers hwindow hcovers

end Nivat.L1CoverPackage

#print axioms Nivat.L1CoverPackage.same_level_iff_on_wline_of_ne_zero
#print axioms Nivat.L1CoverPackage.at_most_one_row_start_per_level_of_ne_zero
#print axioms Nivat.L1CoverPackage.exists_clamped_gap_enumeration_of_occupant
#print axioms Nivat.L1CoverPackage.cover_of_fig11B_of_rows''
