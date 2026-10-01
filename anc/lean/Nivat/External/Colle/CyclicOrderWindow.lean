/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.NormalCycle

/-!
# `b3_colle2.txt:424` 的环序 → 窗口内的**索引条件**（lane-env-refute）

## §0  这是什么

`NormalCycle`（`NormalCycle.lean:172`，lane-tower-hlev）已经把 `:424` 的 successor 环序
转录成 `det` 的号（`step` / `hnoArc` / `indep` / `anti`），并给出窗口内的正号
（`window_pos`（`NormalCycle.lean:426`）：`1 ≤ s < m ⟹ 0 < σ * det ν_i ν_{i+s}`）。

**本文件补的是反方向：从 `det = 0` 反推下标。** 环序把「`det` 为零」这件事
限死在下标差 `≡ 0 (mod m)` 上，于是窗口 `ι+1 ≤ J ≤ ι+m-1`（`b3_colle2.txt:432`）里
只剩两个下标能让某条 `det` 归零——两个端点。这正是链上两条共线/横截前提的内容。

原文逐字（`b3_colle2.txt:424`，Lemma 3.5 的假设段）：

> Suppose `ℓ_1, …, ℓ_{2m} ⊂ ℝ²` is an enumeration of the oriented lines through the origin
> parallels to the edges of `𝒮_φ` where the edge parallel to `ℓ_{i+1}` is a successor of the
> edge parallel to `ℓ_i` and indices are taken modulo `2m`.

同一句在 `b3_colle2.txt:764`（Theorem 1.15 的证明开头）逐字重复，那里还追加
「Renaming the vectors `h_1, …, h_m` if necessary, we may assume that each `h_i`,
with `1 ≤ i ≤ m`, is either parallel or antiparallel to `ℓ_i`」。
窗口本身在 `b3_colle2.txt:432`：「with `ι+1 ≤ J ≤ ι+m-1`」。

## §0.1  ⚠ 一名多物：`vJ1` 是 `v_{ℓ_{J−1}}`，不是 `v_{ℓ_{J+1}}`

主仓约定（`LeafAJSelect.lean:832`「`vJ1` is the paper's `v_{ℓ_{J-1}}` (`:440`)」，
同见 `ANormal.lean:685`、`OrderThree.lean:115`、`LeafASwept.lean:24`）：

| 记号 | 原文 | 下标 |
|---|---|---|
| `vl` | `v⃗_ℓ = v⃗_{ℓ_ι}` | `ι` |
| `vJ1` | `v⃗_{ℓ_{J−1}}` | `J − 1` |
| `w` | `−v⃗_{ℓ_{J+1}}`（`ChainPartsFeed.lean:224`） | `J + 1` |

⟹ 本文件的两条端点定理，一条管 `J−1`（下端点）、一条管 `J+1`（上端点），**不是同一条**。
⚠ 这个 90°/一格的区别正是 `NOTATION.md` 要对的那一格：`det vl vJ1 = 0` 读成
「`ℓ_{J−1} ∥ ℓ_ι`」，`det vl w = 0` 读成「`ℓ_{J+1} ∥ ℓ_ι`」，两者推出的下标相反。

## §0.2  不押朝向

全部结论以 `NormalCycle N m σ`（`σ` 为朝向规范位）陈述，不假设 `σ = 1`；
`det = 0` 与 `σ` 无关（`σ ≠ 0`），故两支逐字同一条定理。
只有引用 `D_pos_ccw` 的推论用 ccw 形，另行标注。

## §0.3  本文件**不**主张的

⛔ 不主张 `dot nJ w = -1`、不主张 `det J ν_{J+1} = 1`、不主张任何带号的 `det vl w`；
本文件对 `w` 只用 `det vl w ≠ 0`（**无号**）这一条，且它是**前提**不是结论。
-/

set_option autoImplicit false

namespace Nivat.CyclicOrderWindow

open Nivat Nivat.LE2 Nivat.LaneTowerHlevNormalCycle

variable {N : Set (ℤ × ℤ)} {m : ℕ} {σ : ℤ}

/-! ## §1  索引恢复：半周之内，`det` 归零只发生在下标差 `0` 和 `m` -/

/-- **`det ν_i ν_{i+s} = 0 ↔ s = 0 ∨ s = m`，对 `s < 2m`。**

这是 `:424` 环序的全部可判定内容的反方向：`indep`（`NormalCycle.lean:230`）说
`1 ≤ s < m` 时不为零，`anti`（`:206`）把 `m ≤ s < 2m` 的一半翻成前一半再用一次 `indep`，
而 `s = 0` / `s = m` 两处恰好为零（`ncy_det_self` / `det_at_m`）。

逐量词：`s < 2m` 对应原文「indices are taken modulo `2m`」的一个周期；
超出一个周期的情形由 `periodic`（`NormalCycle.lean:245`）平移回来，不在本条里重复。 -/
theorem det_eq_zero_iff_of_lt_two_mul (C : NormalCycle N m σ) (i s : ℕ) (hs : s < 2 * m) :
    det (C.nu i) (C.nu (i + s)) = 0 ↔ (s = 0 ∨ s = m) := by
  constructor
  · intro h0
    by_contra hcon
    have hs0 : s ≠ 0 := fun h => hcon (Or.inl h)
    have hsm : s ≠ m := fun h => hcon (Or.inr h)
    rcases lt_or_gt_of_ne hsm with hlt | hgt
    · exact C.indep i s (by omega) hlt h0
    · -- `m < s < 2m`：写 `s = t + m`，`1 ≤ t < m`
      set t : ℕ := s - m with ht_def
      have ht1 : 1 ≤ t := by omega
      have htm : t < m := by omega
      have hidx : i + s = (i + t) + m := by omega
      rw [hidx, C.anti (i + t), ncy_det_neg_right] at h0
      exact C.indep i t ht1 htm (by omega)
  · rintro (rfl | rfl)
    · rw [Nat.add_zero]; exact ncy_det_self _
    · exact C.det_at_m i

/-! ## §2  窗口的两个端点

窗口 `ι+1 ≤ J ≤ ι+m-1`（`b3_colle2.txt:432`）在 Lean 里写成 `J = i + t + 1` 且 `t + 1 < m`，
与 `dot_prev_p_nonpos`（`NormalCycle.lean:472`）同一套下标约定：`t` 跑 `0 … m-2`。 -/

/-- **下端点：`ℓ_{J−1} ∥ ℓ_ι` ⟹ `J = ι + 1`。**

链上形态：`det vl vJ1 = 0`（`FillCoverWitness.lean:51` 的「`J = ι + 1` configuration
(`v_ℓ = v_{ℓ_{J-1}}`, `det vl vJ1 = 0`)」）。本条把那句注释变成定理：
在窗口里，`vJ1` 与 `vl` 共线**只能**是因为 `J − 1 = ι`，而不是别的下标碰巧对齐。 -/
theorem window_bot_of_det_prev_eq_zero (C : NormalCycle N m σ) (i t : ℕ) (ht : t + 1 < m)
    (h0 : det (C.nu i) (C.nu (i + t)) = 0) : t = 0 := by
  have h := (det_eq_zero_iff_of_lt_two_mul C i t (by omega)).mp h0
  rcases h with h | h
  · exact h
  · omega

/-- **下端点，加强形：共线不只给下标，给的是 `ν_{J−1} = ν_ι` 本身。**

⟹ 链上 `vJ1 = vl` 是**推论**，不必当前提假设（集成者 2026-09-25 派工里把它列为
「可以当前提用的数据」，本条说明它在环序下是免费的）。 -/
theorem nu_prev_eq_of_det_prev_eq_zero (C : NormalCycle N m σ) (i t : ℕ) (ht : t + 1 < m)
    (h0 : det (C.nu i) (C.nu (i + t)) = 0) : C.nu (i + t) = C.nu i := by
  rw [window_bot_of_det_prev_eq_zero C i t ht h0, Nat.add_zero]

/-- **上端点：`ℓ_{J+1} ∥ ℓ_ι` ⟹ `J = ι + m − 1`。**

链上形态是它的**否定**：`det vl w ≠ 0`（`w = −v_{ℓ_{J+1}}`，集成者 2026-09-25 裁决，
依据 `ShellMink.lean:588` ＋ `FillCoverWitness.lean` §1 合成的内核反例）
⟹ `J ≠ ι + m − 1`，即窗口的上端点被排除。见 `§3`。 -/
theorem window_top_of_det_next_eq_zero (C : NormalCycle N m σ) (i t : ℕ) (ht : t + 1 < m)
    (h0 : det (C.nu i) (C.nu (i + (t + 2))) = 0) : t + 2 = m := by
  have h := (det_eq_zero_iff_of_lt_two_mul C i (t + 2) (by omega)).mp h0
  rcases h with h | h
  · omega
  · exact h

/-! ## §3  ⭐ 两条端点前提合起来逼出 `3 ≤ m` -/

/-- **`det vl vJ1 = 0` ＋ `det vl w ≠ 0` ＋ 窗口 ⟹ `3 ≤ m`。**

下端点前提把 `J` 钉在 `ι+1`；上端点前提把 `J` 赶出 `ι+m−1`。两者同时成立要求
`ι+1 ≠ ι+m−1`，即 `m ≠ 2`；与 `hm : 2 ≤ m`（`:424`「with `m ≥ 2`」）合起来给 `3 ≤ m`。

⚠ 这与「`m = 1`」相反，也与「`m = 2`」相反。`m = 1` 在 `:424` 下**不可能**
（`hm : 2 ≤ m` 是结构字段），而且 `m = 1` 时窗口 `ι+1 ≤ J ≤ ι+m−1` 是空的，
Lemma 3.5(i) 的结论根本给不出 `J`。 -/
theorem three_le_m_of_window_endpoints (C : NormalCycle N m σ) (i t : ℕ) (ht : t + 1 < m)
    (hprev : det (C.nu i) (C.nu (i + t)) = 0)
    (hnext : det (C.nu i) (C.nu (i + (t + 2))) ≠ 0) : 3 ≤ m := by
  have ht0 : t = 0 := window_bot_of_det_prev_eq_zero C i t ht hprev
  subst ht0
  have hm2 : ¬ (0 + 2 = m) := fun h => hnext (by
    exact (det_eq_zero_iff_of_lt_two_mul C i (0 + 2) (by omega)).mpr (Or.inr h))
  have := C.hm
  omega

/-! ## §4  接口：`0 < D` 在该构型下无条件可用（ccw 形）

`D_pos_ccw`（`NormalCycle.lean:766`）要 `3 ≤ m`；`§3` 恰好产出它。
在 `J = ι+1` 构型里 `ν_{J−1} = ν_ι`、`ν_{J+1} = ν_{ι+2}`，故 `D = det ν_ι ν_{ι+2}`。 -/

/-- **`0 < D`，在「`vJ1` 共线 ＋ `w` 横截」的窗口构型下，不再需要外挂 `3 ≤ m`。**

消费者形状：lane-hole3-nlmax 的 `D_nonneg_of_window`（`DNonnegWindow.lean:52`）要的是
`0 ≤ det nprevJ νJ1`；本条给出严格正的那一半，且把 `3 ≤ m` 这条边界条件
从「假设」降级成「由两条共线/横截前提推出」。 -/
theorem D_pos_of_window_endpoints (C : NormalCycleCcw N m) (i t : ℕ) (ht : t + 1 < m)
    (hprev : det (C.nu i) (C.nu (i + t)) = 0)
    (hnext : det (C.nu i) (C.nu (i + (t + 2))) ≠ 0) :
    0 < det (C.nu (i + t)) (C.nu (i + (t + 2))) := by
  have hm3 : 3 ≤ m := three_le_m_of_window_endpoints C i t ht hprev hnext
  have ht0 : t = 0 := window_bot_of_det_prev_eq_zero C i t ht hprev
  subst ht0
  have h := C.D_pos_ccw hm3 i
  have e1 : i + 0 = i := by omega
  have e2 : i + (0 + 2) = i + 2 := by omega
  rw [e1, e2]
  exact h

/-! ## §5  链上写法的桥：方向侧 ＋ `w = −v⃗_{ℓ_{J+1}}`

链上的三个量是**方向**不是法向，且 `w` 带一个负号。`det` 对同时旋转 90° 是瞎的
（`ncy_det_dir_dir`（`NormalCycle.lean:149`）），对取负只翻号（`ncy_det_neg_right`（`:158`）），
所以两条前提逐字搬得过来，`= 0` / `≠ 0` 两边都不受影响。 -/

/-- **`3 ≤ m`，链上逐字形。**`vl = v⃗_{ℓ_ι}`、`vJ1 = v⃗_{ℓ_{J−1}}`、`w = −v⃗_{ℓ_{J+1}}`，
即 `vl = dir ν_ι`、`vJ1 = dir ν_{ι+t}`、`w = -(dir ν_{ι+t+2})`（`J = ι+t+1`）。

⚠ 本条对 `w` 只用 `det vl w ≠ 0`，**不取号**（§0.3）。 -/
theorem three_le_m_of_chain_shape (C : NormalCycle N m σ) (i t : ℕ) (ht : t + 1 < m)
    (hprev : det (dir (C.nu i)) (dir (C.nu (i + t))) = 0)
    (hnext : det (dir (C.nu i)) (-(dir (C.nu (i + (t + 2))))) ≠ 0) : 3 ≤ m := by
  refine three_le_m_of_window_endpoints C i t ht ?_ ?_
  · rwa [ncy_det_dir_dir] at hprev
  · rw [ncy_det_neg_right, ncy_det_dir_dir] at hnext
    exact fun h => hnext (by rw [h]; simp)

/-- **下端点，链上逐字形**：`det vl vJ1 = 0` ⟹ `vJ1 = vl`（`J = ι+1`）。 -/
theorem vJ1_eq_vl_of_chain_shape (C : NormalCycle N m σ) (i t : ℕ) (ht : t + 1 < m)
    (hprev : det (dir (C.nu i)) (dir (C.nu (i + t))) = 0) :
    dir (C.nu (i + t)) = dir (C.nu i) := by
  rw [nu_prev_eq_of_det_prev_eq_zero C i t ht (by rwa [ncy_det_dir_dir] at hprev)]

end Nivat.CyclicOrderWindow

open Nivat.CyclicOrderWindow in
#print axioms Nivat.CyclicOrderWindow.det_eq_zero_iff_of_lt_two_mul
open Nivat.CyclicOrderWindow in
#print axioms Nivat.CyclicOrderWindow.window_bot_of_det_prev_eq_zero
open Nivat.CyclicOrderWindow in
#print axioms Nivat.CyclicOrderWindow.nu_prev_eq_of_det_prev_eq_zero
open Nivat.CyclicOrderWindow in
#print axioms Nivat.CyclicOrderWindow.window_top_of_det_next_eq_zero
open Nivat.CyclicOrderWindow in
#print axioms Nivat.CyclicOrderWindow.three_le_m_of_window_endpoints
open Nivat.CyclicOrderWindow in
#print axioms Nivat.CyclicOrderWindow.D_pos_of_window_endpoints
open Nivat.CyclicOrderWindow in
#print axioms Nivat.CyclicOrderWindow.three_le_m_of_chain_shape
open Nivat.CyclicOrderWindow in
#print axioms Nivat.CyclicOrderWindow.vJ1_eq_vl_of_chain_shape
