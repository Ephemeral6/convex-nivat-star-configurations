/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.NormalCycle

/-!
# 指标认同的**可证半边**：环覆盖 `N`，且相邻对的下标差必为 `1`（lane-env-refute）

## §0 这个文件补的是哪个缺口

`NormalCycleExists.lean` §0.2 与 `NormalCycleSphi.lean` §0.3 都写着
⛔「**不供指标认同**：环存在 ⇏ 链上某一对向量是这条环上的相邻对」。本文件把这句话
**拆成两半**，并把其中**可证的那半**证掉：

| 半边 | 内容 | 状态 |
|---|---|---|
| (A) **覆盖** | `N` 的每个元素都出现在环上：`∀ y ∈ N, ∃ k, C.nu k = y` | ✅ 本文件 `exists_index_of_mem` |
| (B) **相邻 ⟹ 下标相继** | 若 `ν_k` 与 `ν_{k+s}` 之间没有第三条边法向且 `0 < det`，则 `s = 1` | ✅ 本文件 `shift_eq_one_of_adjacent` |

⚠ **这两条合起来仍然不是原来那句 ⛔ 的反驳。** 原来那句否掉的是**另一对**向量：
lane-tower-hbase 的 `oct_chain_pair_not_cycle_adjacent`
（`tmp/wip/lane-tower-hbase-sortdir.lean:1878`，内核见证，我本轮亲读其陈述、**未**亲跑其
`decide`）针对的是 `(dir wOct90, nlOct)`——缺口三的 `hwadj` 那一对，它**真的**在某个 `y` 的
两侧同时为正，所以它不可能相继。本文件的 (A)(B) 说的是：**凡是满足「`0 < det` ＋ 弧空」
的那种对，下标必相继**；hbase 的那一对**不满足弧空**，两条不矛盾。

⟹ 正确读法：`ν_{J-1}`/`ν_J` 这一对（链上带 `Arc nprevJ nJ = ∅`）可以认同；
`(dir wOct90, nlOct)` 那一对不能。**「指标认同」不是一个命题，是一族命题，逐对判定。**

## §1 (A) 的证明是一条离散介值定理

设 `g k := σ * det (ν_k) y`。若 `y` 与每条 `ν_k` 都不平行，则 `g` 处处非零；
`anti` 给 `g (k+m) = -g k`，于是 `g` 在 `[0, 2m]` 上必有一次「正→负」的相邻变号，
那一步正是 `hnoArc` 明文禁止的合取。⟹ 必有 `det (ν_k) y = 0`，再由 `hpar` 得
`y = ν_k` 或 `y = -ν_k = ν_{k+m}`。

`hpar`（「平行 ⟹ 相等或相反」）**不是** `NormalCycle` 的字段，故取作前提。它在链上白送：
`NormalCycleSphi.ang_E_Sphi_par`（`NormalCycleSphi.lean:67`）对 `E ↑d.Sphi` 无条件给出。

## §2 不主张什么

⛔ 不主张 `m = d.m`（`:319` 的计数本文件没证也没用）。
⛔ 不主张 `E B = E ↑d.Sphi`（`DecompData.lean:115-123` 的 Agreement 字段已删）。
⛔ 不主张任何关于 `hadj` 的东西——恰恰相反，`CyclicOrderAdjRefute.lean` 证明**即使**
   认同成功，环序也给不出 `det vJ vJ1 = ±1`。本文件与那条**没有**互相救援的关系。
⛔ 整体在**法向侧**（`E` 的成员是边法向）；方向侧差一个 `dir`。
-/

set_option autoImplicit false

namespace Nivat.CyclicOrderIndex

open Nivat Nivat.LE2 Nivat.LaneTowerHlevNormalCycle

variable {N : Set (ℤ × ℤ)} {m : ℕ} {σ : ℤ}

/-! ## §3  离散介值定理 -/

/-- **离散介值定理**：处处非零的 `ℤ`-序列若在 `a` 处为正、在 `a + n` 处为负，
则中间必有一步「正→负」的相邻变号。 -/
theorem exists_sign_flip {g : ℕ → ℤ} (hne : ∀ k, g k ≠ 0) (a : ℕ) (hpos : 0 < g a) :
    ∀ n : ℕ, g (a + n) < 0 → ∃ k, 0 < g k ∧ g (k + 1) < 0 := by
  intro n
  induction n with
  | zero => intro h; rw [Nat.add_zero] at h; omega
  | succ t ih =>
    intro h
    rcases lt_trichotomy (g (a + t)) 0 with hlt | heq | hgt
    · exact ih hlt
    · exact absurd heq (hne _)
    · refine ⟨a + t, hgt, ?_⟩
      rwa [← Nat.add_assoc] at h

/-! ## §4  (A) 覆盖 -/

/-- `det (-a) b = -det a b`。 -/
theorem det_neg_left (a b : ℤ × ℤ) : det (-a) b = -det a b := by
  simp only [det, Prod.fst_neg, Prod.snd_neg]; ring

/-- `det a b = -det b a`。 -/
theorem det_swap (a b : ℤ × ℤ) : det a b = -det b a := by
  simp only [det]; ring

/-- **每个 `y ∈ N` 都与环上某一条平行。**  纯粹由 `anti` ＋ `hnoArc` ＋ `hsigma` 推出，
不用 `hpar`、不用有限性。 -/
theorem exists_det_eq_zero_of_mem (C : NormalCycle N m σ) {y : ℤ × ℤ} (hy : y ∈ N) :
    ∃ k, det (C.nu k) y = 0 := by
  by_contra hcon
  have hnz : ∀ k, det (C.nu k) y ≠ 0 := fun k h => hcon ⟨k, h⟩
  set g : ℕ → ℤ := fun k => σ * det (C.nu k) y with hg
  have hne : ∀ k, g k ≠ 0 := fun k => C.sigma_mul_ne_zero (hnz k)
  have hanti : ∀ k, g (k + m) = -g k := by
    intro k
    simp only [hg, C.anti k, det_neg_left]
    ring
  -- 找一个「正→负」的相邻变号
  have hflip : ∃ k, 0 < g k ∧ g (k + 1) < 0 := by
    rcases lt_trichotomy (g 0) 0 with hlt | heq | hgt
    · -- `g 0 < 0` ⟹ `g m > 0`，在 `[m, 2m]` 上找
      have hm0 : 0 < g m := by have := hanti 0; simp only [Nat.zero_add] at this; omega
      have h2m : g (m + m) < 0 := by have := hanti m; omega
      exact exists_sign_flip hne m hm0 m h2m
    · exact absurd heq (hne 0)
    · have hm0 : g (0 + m) < 0 := by have := hanti 0; omega
      exact exists_sign_flip hne 0 hgt m hm0
  obtain ⟨k, hk1, hk2⟩ := hflip
  refine C.hnoArc k y hy ⟨hk1, ?_⟩
  have hsw : det y (C.nu (k + 1)) = -det (C.nu (k + 1)) y := det_swap _ _
  have : σ * det y (C.nu (k + 1)) = -g (k + 1) := by
    simp only [hg, hsw]; ring
  omega

/-- ⭐ **(A) 覆盖**：`N` 的每个元素都出现在环上。

`hpar`（平行 ⟹ ±相等）是前提，不是字段；链上由 `NormalCycleSphi.ang_E_Sphi_par`
（`NormalCycleSphi.lean:67`）无条件供给。 -/
theorem exists_index_of_mem (C : NormalCycle N m σ)
    (hpar : ∀ n ∈ N, ∀ n' ∈ N, det n n' = 0 → n' = n ∨ n' = -n)
    {y : ℤ × ℤ} (hy : y ∈ N) : ∃ k, C.nu k = y := by
  obtain ⟨k, hk⟩ := exists_det_eq_zero_of_mem C hy
  rcases hpar (C.nu k) (C.mem k) y hy hk with h | h
  · exact ⟨k, h.symm⟩
  · exact ⟨k + m, by rw [C.anti k, ← h]⟩

/-! ## §5  (B) 相邻 ⟹ 下标相继 -/

/-- ⭐ **(B)**：在逆时针环上，若 `ν_k` 与 `ν_{k+s}` 之间（严格地）没有第三条边法向、
且 `0 < det ν_k ν_{k+s}`，则 `s = 1`。

`hempty` 的形状逐字是链上 `Arc nprevJ nJ = ∅`（`DNonnegWindow.lean:54`，经
`PolyChainSum.mem_Arc` 展开）在环序里的对应物。`hs : s < 2 * m` 是「同一圈内」，
由 `periodic`（`NormalCycle.lean:245`）可把任意下标归约到这个区间。 -/
theorem shift_eq_one_of_adjacent (C : NormalCycleCcw N m) (k s : ℕ) (hs : s < 2 * m)
    (hpos : 0 < det (C.nu k) (C.nu (k + s)))
    (hempty : ∀ y ∈ N, ¬ (0 < det (C.nu k) y ∧ 0 < det y (C.nu (k + s)))) :
    s = 1 := by
  have hm := C.hm
  by_contra hne
  rcases Nat.lt_or_ge s m with hlt | hge
  · -- `s < m`：`s = 0` 被 `hpos` 排掉；`2 ≤ s` 时 `ν_{k+1}` 就夹在中间
    rcases Nat.eq_zero_or_pos s with rfl | hs1
    · rw [Nat.add_zero, ncy_det_self] at hpos; omega
    have hs2 : 2 ≤ s := by omega
    refine hempty (C.nu (k + 1)) (C.mem _) ⟨C.window_pos_ccw k 1 (by omega) (by omega), ?_⟩
    have h := C.window_pos_ccw (k + 1) (s - 1) (by omega) (by omega)
    have heq : (k + 1) + (s - 1) = k + s := by omega
    rwa [heq] at h
  · -- `m ≤ s < 2m`：`s = m` 给 `det = 0`，`m < s` 给 `det < 0`
    rcases Nat.eq_or_lt_of_le hge with heq | hgt
    · rw [← heq, C.det_at_m] at hpos; omega
    · set t : ℕ := s - m with ht
      have ht1 : 1 ≤ t := by omega
      have htm : t < m := by omega
      have hidx : k + s = (k + t) + m := by omega
      have h := C.window_pos_ccw k t ht1 htm
      rw [hidx, C.anti (k + t), ncy_det_neg_right] at hpos
      omega

/-- **(A) ＋ (B) 的合成形**：若 `y`、`z ∈ N`、`0 < det y z`、两者之间无第三条边法向，
且消费者能把 `z` 写成 `y` 的同圈后继（`z = C.nu (k + s)`，`s < 2m`），则 `z = C.nu (k+1)`。

⚠ 「同圈后继」这个前提**不是白送的**：它要 `periodic` 的模 `2m` 归约，本文件不做
（不是难，是它属于消费者的下标簿记，形状因消费者而异）。 -/
theorem next_of_adjacent (C : NormalCycleCcw N m) (k s : ℕ) (hs : s < 2 * m)
    (hpos : 0 < det (C.nu k) (C.nu (k + s)))
    (hempty : ∀ y ∈ N, ¬ (0 < det (C.nu k) y ∧ 0 < det y (C.nu (k + s)))) :
    C.nu (k + s) = C.nu (k + 1) := by
  rw [shift_eq_one_of_adjacent C k s hs hpos hempty]

end Nivat.CyclicOrderIndex

#print axioms Nivat.CyclicOrderIndex.exists_sign_flip
#print axioms Nivat.CyclicOrderIndex.det_neg_left
#print axioms Nivat.CyclicOrderIndex.det_swap
#print axioms Nivat.CyclicOrderIndex.exists_det_eq_zero_of_mem
#print axioms Nivat.CyclicOrderIndex.exists_index_of_mem
#print axioms Nivat.CyclicOrderIndex.shift_eq_one_of_adjacent
#print axioms Nivat.CyclicOrderIndex.next_of_adjacent
