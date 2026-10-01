/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.NormalCycleSphi
import Nivat.External.Colle.CyclicOrderIndex
import Nivat.External.Colle.CyclicOrderWindow
import Nivat.External.Colle.CyclicOrderDPos
-- §6 的两个空弧产者（lane-hole3-nlmax 2026-09-25 指路）。⚠ 两者的上游闭包与
-- `{RegionSteps, ColleRegion, Case2WindowProbe, NfpLPreamble}` 的交集实测为空。
import Nivat.External.Colle.LeafAJSelect
import Nivat.External.Colle.LeafAShellNNext

/-!
# 把 `NormalCycle` 实例化到链上的 `E (↑d.Sphi)`（lane-env-refute）

## §0  这个文件回答的是哪句批评

team-lead 第 228 轮：「你现在两个正面结论（`3 ≤ m`、`0 < D`）和一个反例全都陈述在抽象
`NormalCycle N m σ` 上，**没有一条接到链上任何 `sorry`**。」

这句话对 `CyclicOrderWindow.lean`（`three_le_m_of_window_endpoints`、
`D_pos_of_window_endpoints`）**成立**，本文件把那两条搬到 `E (↑d.Sphi)` 上。

⚠ **但这句话对 `CyclicOrderDPos.lean` 不成立，那条不需要实例化。**
`Nivat.CyclicOrderDPos.D_pos_of_window_of_transversal` 的签名里**一个 `NormalCycle` 都没有**
（`grep -c NormalCycle Nivat/External/Colle/CyclicOrderDPos.lean` 命中 3 处，全在 docstring
的对照说明里，无一处在任何签名或证明里）：它的量词只有 `E (↑Sphi : Set (ℤ × ℤ))`、
`Nivat.PolyChainSum.Arc (Sphi.finite_toSet) · ·` 和 `det`，即 shell 与 nlmax 已经在用的语言。
⟹ shell 逐字核 `D` 的那件事**现在就可以做**，不等本文件。

## §0.1  本文件的三层

| 层 | 内容 | 出口 |
|---|---|---|
| §2 模 `2m` 归约 | `C.nu` 的下标可归约到 `[0, 2m)`，任意两个下标可写成 `r` 与 `r + t`，`t < 2m` | `nu_mod` / `exists_shift_lt` |
| §3 指标认同（链上形） | `Arc y z = ∅` ＋ `0 < det y z` ⟹ `y = ν_k`、`z = ν_{k+1}` | `adjacent_index_of_arc_empty` |
| §4 `3 ≤ m`（链上形） | 窗口数据给出三条两两不平行的边法向 ⟹ 环的 `m ≥ 3` | `exists_ncy_three_le_m_of_window` |

§2 正是我第 227 轮报告里自己记的欠账（`next_of_adjacent` 要消费者把 `z` 写成
`C.nu (k+s)`、`s < 2m`）。本文件把它补上，因此 §3 的前提里**不再有下标**——
入口全是 `E`/`Arc`/`det`，出口才出现下标。

## §0.2  为什么 `3 ≤ m` 这条必须经过环、而 `0 < D` 不必

`m` 是**环的边数**（`NormalCycle N m σ` 的参数），链上没有任何对象叫这个名字；
所以「`3 ≤ m`」这句话只有在给定一条环之后才有意义，实例化不可跳过。
`D = det nprevJ νJ1` 反过来是**链上本来就有的表达式**，环只是证明它为正的一条可能路线，
而 `CyclicOrderDPos` 走的是另一条（三项 Plücker 恒等式），所以那条绕开了环。

## §0.3  ⛔ 本文件不主张的

1. ⛔ **不主张 `m = d.m`。**`:319` 的计数 `|E(𝒮_φ)| = 2m` 本文件没证也没用
   （照抄 `NormalCycleSphi.lean` §0.3(1) 的限制，它在这里同样有效）。
2. ⛔ **不主张 `E B = E ↑d.Sphi`。**`DecompData.lean:115-123` 的 Agreement 字段 2026-09-17 已删。
3. ⛔ **不主张 `hadj`／`dot nJ vJ1 = -1`。**恰恰相反：`CyclicOrderAdjRefute.lean` 的内核反例
   说明即使 §3 的认同成功，环序也给不出这两条。§3 与那个反例**没有**互相救援的关系。
4. ⛔ **整体在法向侧。**`E` 的成员是边法向；链上的 `vl`/`vJ1`/`w` 是**方向**，差一个 `dir`。
   本文件不做 `dir` 转写（`CyclicOrderWindow.lean` §5 已有那一层）。
5. ⛔ **§4 的 `3 ≤ m` 不蕴含窗口里 `J` 的下标是什么。**它只说环够长；把 `J` 钉到
   `ι+1` 是 `CyclicOrderWindow.window_bot_of_det_prev_eq_zero` 的事，要额外前提。

## §0.4  原文出处

环序枚举句：`scratch/b3_colle2.txt:424`（Lemma 3.5 假设段），同句在 `:764` 重复。
窗口 `ι+1 ≤ J ≤ ι+m-1`：`:432`。`𝒮_φ` 的边法向集合与 `2m` 计数：`:319`。
`m ≥ 2` 是 `:424` 的字面（`NormalCycle.hm`）；`3 ≤ m` 不是原文的量词，是从两条链上前提
推出来的（见 §4 与 `CyclicOrderWindow.lean` §3）。
-/

set_option autoImplicit false

namespace Nivat.CyclicOrderSphiInst

open Nivat Nivat.LE2 Nivat.LaneTowerHlevNormalCycle

variable {N : Set (ℤ × ℤ)} {m : ℕ} {σ : ℤ}

/-! ## §1  `Arc = ∅` 的展开

链上的空弧条件写成 `Finset` 的 `= ∅`（`DNonnegWindow.lean:54`、`PolyChainSum.lean:104`），
环序那边要的是 `∀ μ ∈ E T, ¬(…)`。这一步只是 `Finset.eq_empty_iff_forall_not_mem` ＋
`PolyChainSum.mem_Arc`，但它是两套语言之间唯一的接缝，所以单独命名。 -/

theorem not_between_of_arc_empty {T : Set (ℤ × ℤ)} {hfin : T.Finite} {ν₀ n : ℤ × ℤ}
    (h : Nivat.PolyChainSum.Arc hfin ν₀ n = ∅) :
    ∀ μ ∈ E T, ¬ (0 < det ν₀ μ ∧ 0 < det μ n) := by
  intro μ hμ hbet
  have : μ ∈ Nivat.PolyChainSum.Arc hfin ν₀ n :=
    Nivat.PolyChainSum.mem_Arc.mpr ⟨hμ, hbet.1, hbet.2⟩
  rw [h] at this
  simp at this

/-! ## §2  模 `2m` 归约

第 227 轮我自己记的欠账。`periodic`（`NormalCycle.lean:245`）给周期 `2m`，
下面三条把它变成「下标可以任意搬到同一圈内」。

⚠ `exists_shift_lt` **不用 `%`**：`omega` 只认字面模数，而这里的模数是 `2 * m`（变量）。
两支分别是 `r ≤ s`（取 `t = s - r`）与 `s < r`（取 `t = s + 2m - r`，再用一次 `periodic`）。 -/

/-- 周期 `2m` 的 `j` 次迭代。 -/
theorem nu_add_two_mul (C : NormalCycle N m σ) (k j : ℕ) :
    C.nu (k + j * (2 * m)) = C.nu k := by
  induction j with
  | zero => simp
  | succ t ih =>
    have h : k + (t + 1) * (2 * m) = (k + t * (2 * m)) + 2 * m := by ring
    rw [h, C.periodic]
    exact ih

/-- 下标可归约到 `[0, 2m)`。 -/
theorem nu_mod (C : NormalCycle N m σ) (k : ℕ) : C.nu (k % (2 * m)) = C.nu k := by
  have h := nu_add_two_mul C (k % (2 * m)) (k / (2 * m))
  rw [Nat.mod_add_div'] at h
  exact h.symm

/-- **覆盖的「同圈」形**：每个 `y ∈ N` 都是某个 `ν_r`，且可取 `r < 2m`。

`hpar` 不是 `NormalCycle` 的字段（见 `CyclicOrderIndex.lean` §1），链上由
`NormalCycleSphi.ang_E_Sphi_par`（`NormalCycleSphi.lean:67`）无条件供给。 -/
theorem exists_index_lt (C : NormalCycle N m σ)
    (hpar : ∀ n ∈ N, ∀ n' ∈ N, det n n' = 0 → n' = n ∨ n' = -n)
    {y : ℤ × ℤ} (hy : y ∈ N) : ∃ r, r < 2 * m ∧ C.nu r = y := by
  obtain ⟨k, hk⟩ := Nivat.CyclicOrderIndex.exists_index_of_mem C hpar hy
  have hm := C.hm
  have hpos : 0 < 2 * m := by omega
  refine ⟨k % (2 * m), Nat.mod_lt _ hpos, ?_⟩
  rw [nu_mod C k]
  exact hk

/-- **任意两个同圈下标之间的位移可取在 `[0, 2m)` 内。**
这正是 `CyclicOrderIndex.next_of_adjacent` 欠的那一格。 -/
theorem exists_shift_lt (C : NormalCycle N m σ) (r s : ℕ) (hr : r < 2 * m) (hs : s < 2 * m) :
    ∃ t, t < 2 * m ∧ C.nu (r + t) = C.nu s := by
  rcases Nat.lt_or_ge s r with hlt | hge
  · refine ⟨s + 2 * m - r, by omega, ?_⟩
    have he : r + (s + 2 * m - r) = s + 2 * m := by omega
    rw [he]
    exact C.periodic s
  · refine ⟨s - r, by omega, ?_⟩
    have he : r + (s - r) = s := by omega
    rw [he]

/-- ⭐ **lane-tower-hlev 点的那个形状**：下标**不必**先落在 `[0, 2m)` 里。

他的理由（2026-09-25，他直接来信）：消费者手上的两个下标来自
`CyclicOrderIndex.exists_index_of_mem`，那条给的是裸 `∃ k`，两个元素各一个 `k`，
**彼此没有大小关系**，也不保证 `< 2m`。`exists_shift_lt` 要求两个入参都已归约，
于是每个消费者都得自己碰一次 `%` 和一次 ℕ 减法——那是他明确不想要的。
这条把归约吞在里面，消费者只需要 `exists_index_of_mem` 的两个裸 `k`。

⟹ 他要的方向也照抄了：结论是 `C.nu b = C.nu (a + s)`（`b` 在左），这样
`next_of_adjacent` 可以直接吃。

⚠ 内部仍然绕开 `omega` 的模数：`%` 只出现在 `Nat.mod_lt` / `Nat.mod_add_div` 这两个
**库引理**里，算式重排交给 `ring`（ℕ 是交换半环）。`omega` 只认字面模数，这里模数是
`2 * m`，是变量。 -/
theorem exists_shift (C : NormalCycle N m σ) (a b : ℕ) :
    ∃ s, s < 2 * m ∧ C.nu b = C.nu (a + s) := by
  have hm := C.hm
  have hpos : 0 < 2 * m := by omega
  obtain ⟨s, hslt, hs⟩ :=
    exists_shift_lt C (a % (2 * m)) (b % (2 * m)) (Nat.mod_lt _ hpos) (Nat.mod_lt _ hpos)
  refine ⟨s, hslt, ?_⟩
  have hmd : a % (2 * m) + 2 * m * (a / (2 * m)) = a := Nat.mod_add_div a (2 * m)
  have hkey : C.nu (a + s) = C.nu (a % (2 * m) + s) := by
    have he : a + s = (a % (2 * m) + s) + (a / (2 * m)) * (2 * m) := by
      -- ⚠ 必须 `conv_lhs`：裸 `rw [← hmd]` 会把 `a % (2*m)` / `a / (2*m)` 里面的 `a`
      -- 一起改掉，goal 变成带嵌套 `%` 的一团，`ring` 接不住（2026-09-25 实测）。
      conv_lhs => rw [← hmd]
      ring
    rw [he, nu_add_two_mul]
  rw [hkey, hs, nu_mod C b]

/-! ## §3  ⭐ 指标认同，链上形

入口只有 `E`/`Arc`/`det`，没有下标；出口给出下标并且相继。

⚠ 这**不是**对 `NormalCycleExists.lean` §0.2(2) 那条 ⛔ 的反驳。那条否掉的是
lane-tower-hbase 的 `(dir wOct90, nlOct)`，那一对**不满足**弧空条件
（`tmp/wip/lane-tower-hbase-sortdir.lean:1878`，我读过其陈述、未亲跑其 `decide`）。
「指标认同」是一族命题，逐对判定；本条判的是带弧空条件的那一族。 -/

theorem adjacent_index_of_empty (C : NormalCycleCcw N m)
    (hpar : ∀ n ∈ N, ∀ n' ∈ N, det n n' = 0 → n' = n ∨ n' = -n)
    {y z : ℤ × ℤ} (hy : y ∈ N) (hz : z ∈ N) (hpos : 0 < det y z)
    (hempty : ∀ μ ∈ N, ¬ (0 < det y μ ∧ 0 < det μ z)) :
    ∃ k, C.nu k = y ∧ C.nu (k + 1) = z := by
  obtain ⟨r, hrlt, hr⟩ := exists_index_lt C hpar hy
  obtain ⟨s, hslt, hs⟩ := exists_index_lt C hpar hz
  obtain ⟨t, htlt, ht⟩ := exists_shift_lt C r s hrlt hslt
  have hzz : C.nu (r + t) = z := by rw [ht, hs]
  have h1 : 0 < det (C.nu r) (C.nu (r + t)) := by rw [hr, hzz]; exact hpos
  have h2 : ∀ μ ∈ N, ¬ (0 < det (C.nu r) μ ∧ 0 < det μ (C.nu (r + t))) := by
    intro μ hμ
    rw [hr, hzz]
    exact hempty μ hμ
  have ht1 : t = 1 := Nivat.CyclicOrderIndex.shift_eq_one_of_adjacent C r t htlt h1 h2
  exact ⟨r, hr, by rw [← ht1]; exact hzz⟩

/-! ## §4  `3 ≤ m`：三条两两不平行的边法向就够

`CyclicOrderWindow.three_le_m_of_window_endpoints` 走的是下标（要先认同）。
本节换一条**不要下标**的路：`m = 2` 时环只有 `ν₀, ν₁, -ν₀, -ν₁` 四项，
任何三个元素里必有一对平行；所以只要链上给出三条两两不平行的边法向，就有 `3 ≤ m`。 -/

/-- 下标差为 `0` 或 `m` 时 `det` 归零（`CyclicOrderWindow.det_eq_zero_iff_of_lt_two_mul`
的减法形）。 -/
theorem det_eq_zero_of_diff (C : NormalCycle N m σ) (a b : ℕ) (hab : a ≤ b)
    (hlt : b - a < 2 * m) (hs : b - a = 0 ∨ b - a = m) :
    det (C.nu a) (C.nu b) = 0 := by
  have he : a + (b - a) = b := by omega
  rw [← he]
  exact (Nivat.CyclicOrderWindow.det_eq_zero_iff_of_lt_two_mul C a (b - a) hlt).mpr hs

/-- `m = 2` 时，`[0,4)` 内同奇偶的两个下标给出平行的一对。 -/
theorem det_eq_zero_of_same_parity (C : NormalCycle N 2 σ) (a b : ℕ)
    (ha : a < 4) (hb : b < 4) (hp : a % 2 = b % 2) :
    det (C.nu a) (C.nu b) = 0 := by
  rcases Nat.le_total a b with h | h
  · exact det_eq_zero_of_diff C a b h (by omega) (by omega)
  · have hba : det (C.nu b) (C.nu a) = 0 :=
      det_eq_zero_of_diff C b a h (by omega) (by omega)
    rw [Nivat.CyclicOrderIndex.det_swap, hba, neg_zero]

/-- ⭐ **三条两两不平行的元素 ⟹ `3 ≤ m`。**

`m = 2` 时下标只有 `[0,4)` 四个，鸽笼给出同奇偶的一对，而同奇偶 ⟹ 下标差 `0` 或 `2 = m`
⟹ `det = 0`，与两两不平行矛盾。 -/
theorem three_le_m_of_three_indep (C : NormalCycle N m σ)
    (hpar : ∀ n ∈ N, ∀ n' ∈ N, det n n' = 0 → n' = n ∨ n' = -n)
    {y₁ y₂ y₃ : ℤ × ℤ} (h₁ : y₁ ∈ N) (h₂ : y₂ ∈ N) (h₃ : y₃ ∈ N)
    (d₁₂ : det y₁ y₂ ≠ 0) (d₁₃ : det y₁ y₃ ≠ 0) (d₂₃ : det y₂ y₃ ≠ 0) :
    3 ≤ m := by
  rcases Nat.lt_or_ge m 3 with hlt | hge
  · exfalso
    have hm := C.hm
    have hm2 : m = 2 := by omega
    subst hm2
    obtain ⟨r₁, hr₁lt, hr₁⟩ := exists_index_lt C hpar h₁
    obtain ⟨r₂, hr₂lt, hr₂⟩ := exists_index_lt C hpar h₂
    obtain ⟨r₃, hr₃lt, hr₃⟩ := exists_index_lt C hpar h₃
    by_cases e₁₂ : r₁ % 2 = r₂ % 2
    · refine d₁₂ ?_
      rw [← hr₁, ← hr₂]
      exact det_eq_zero_of_same_parity C r₁ r₂ (by omega) (by omega) e₁₂
    · by_cases e₁₃ : r₁ % 2 = r₃ % 2
      · refine d₁₃ ?_
        rw [← hr₁, ← hr₃]
        exact det_eq_zero_of_same_parity C r₁ r₃ (by omega) (by omega) e₁₃
      · have e₂₃ : r₂ % 2 = r₃ % 2 := by omega
        refine d₂₃ ?_
        rw [← hr₂, ← hr₃]
        exact det_eq_zero_of_same_parity C r₂ r₃ (by omega) (by omega) e₂₃
  · exact hge

/-! ## §5  ⭐⭐ 落到 `E (↑d.Sphi)`：`hpar` 在链上白送

`NormalCycleSphi.ang_E_Sphi_par`（`NormalCycleSphi.lean:67`）对**任意** `DecompData`
无条件给出 `hpar`，所以 §3/§4 的那个前提在链上不留残债。 -/

section Sphi

variable {α : Type*} [AddCommMonoid α] {η : Config α}

/-- `E ↑d.Sphi` 上的 `hpar`，供 §3/§4 用。 -/
theorem par_E_Sphi (d : Nivat.Colle35.DecompData η) :
    ∀ n ∈ E (↑d.Sphi : Set (ℤ × ℤ)), ∀ n' ∈ E (↑d.Sphi : Set (ℤ × ℤ)),
      det n n' = 0 → n' = n ∨ n' = -n :=
  fun _ hn _ hn' h0 => Nivat.NormalCycleSphi.ang_E_Sphi_par d hn hn' h0

/-- **§3 在链上**：`Arc = ∅` 的一对边法向在环上下标相继。入口逐字是 nlmax 的
`D_nonneg_of_window`（`DNonnegWindow.lean:49`）那两条空弧前提的形状。 -/
theorem adjacent_index_E_Sphi (d : Nivat.Colle35.DecompData η) {mm : ℕ}
    (C : NormalCycleCcw (E (↑d.Sphi : Set (ℤ × ℤ))) mm)
    {y z : ℤ × ℤ} (hy : y ∈ E (↑d.Sphi : Set (ℤ × ℤ)))
    (hz : z ∈ E (↑d.Sphi : Set (ℤ × ℤ))) (hpos : 0 < det y z)
    (hempty : Nivat.PolyChainSum.Arc (d.Sphi.finite_toSet) y z = ∅) :
    ∃ k, C.nu k = y ∧ C.nu (k + 1) = z :=
  adjacent_index_of_empty C (par_E_Sphi d) hy hz hpos (not_between_of_arc_empty hempty)

/-- **§4 在链上**。 -/
theorem three_le_m_E_Sphi (d : Nivat.Colle35.DecompData η) {mm : ℕ}
    (C : NormalCycleCcw (E (↑d.Sphi : Set (ℤ × ℤ))) mm)
    {y₁ y₂ y₃ : ℤ × ℤ} (h₁ : y₁ ∈ E (↑d.Sphi : Set (ℤ × ℤ)))
    (h₂ : y₂ ∈ E (↑d.Sphi : Set (ℤ × ℤ))) (h₃ : y₃ ∈ E (↑d.Sphi : Set (ℤ × ℤ)))
    (d₁₂ : det y₁ y₂ ≠ 0) (d₁₃ : det y₁ y₃ ≠ 0) (d₂₃ : det y₂ y₃ ≠ 0) :
    3 ≤ mm :=
  three_le_m_of_three_indep C (par_E_Sphi d) h₁ h₂ h₃ d₁₂ d₁₃ d₂₃

/-! ### §5.1  窗口数据自带第三条方向

`D_pos_of_window` 的十二条前提里，`hnprevor`／`hνJ1or` 两条析取加上非退化条件 `hnd`
已经蕴含「至少有三条两两不平行的边法向」：`nprevJ ≠ ℓ` 那支给 `(ℓ, nprevJ, J)`，
`νJ1 ≠ -ℓ` 那支给 `(ℓ, J, νJ1)`。两支都用 `CyclicOrderDPos` 的端点严格性。

⚠ `hnd` **不是定理**（`CyclicOrderDPos.lean` §3）：`m = 2` 的正方形确实出现，
那时两个端点同时退化。它在链上由横截性 `det ℓ w ≠ 0` 兑现
（`CyclicOrderDPos.D_pos_of_window_of_transversal`）。 -/

theorem three_indep_of_window (d : Nivat.Colle35.DecompData η) {ℓ J nprevJ νJ1 : ℤ × ℤ}
    (hℓE : ℓ ∈ E (↑d.Sphi : Set (ℤ × ℤ))) (hJE : J ∈ E (↑d.Sphi : Set (ℤ × ℤ)))
    (hℓJ : 0 < det ℓ J)
    (hnprevor : nprevJ = ℓ ∨
      nprevJ ∈ Nivat.PolyChainSum.Arc (d.Sphi.finite_toSet) ℓ J)
    (hνJ1or : νJ1 = -ℓ ∨
      νJ1 ∈ Nivat.PolyChainSum.Arc (d.Sphi.finite_toSet) J (-ℓ))
    (hnd : ¬ (nprevJ = ℓ ∧ νJ1 = -ℓ)) :
    ∃ y₁ ∈ E (↑d.Sphi : Set (ℤ × ℤ)), ∃ y₂ ∈ E (↑d.Sphi : Set (ℤ × ℤ)),
      ∃ y₃ ∈ E (↑d.Sphi : Set (ℤ × ℤ)),
        det y₁ y₂ ≠ 0 ∧ det y₁ y₃ ≠ 0 ∧ det y₂ y₃ ≠ 0 := by
  by_cases hp : nprevJ = ℓ
  · -- 退化在下端点 ⟹ 上端点非退化，取 `(ℓ, J, νJ1)`
    have hq : νJ1 ≠ -ℓ := fun h => hnd ⟨hp, h⟩
    have hmem : νJ1 ∈ Nivat.PolyChainSum.Arc (d.Sphi.finite_toSet) J (-ℓ) := by
      rcases hνJ1or with h | h
      · exact absurd h hq
      · exact h
    have hνE : νJ1 ∈ E (↑d.Sphi : Set (ℤ × ℤ)) := (Nivat.PolyChainSum.mem_Arc.mp hmem).1
    have hJν : 0 < det J νJ1 := (Nivat.PolyChainSum.mem_Arc.mp hmem).2.1
    have hℓν : 0 < det ℓ νJ1 :=
      Nivat.CyclicOrderDPos.det_hi_pos_of_ne (Sphi := d.Sphi) (J := J) hνJ1or hq
    exact ⟨ℓ, hℓE, J, hJE, νJ1, hνE, by omega, by omega, by omega⟩
  · -- 下端点非退化，取 `(ℓ, nprevJ, J)`
    have hmem : nprevJ ∈ Nivat.PolyChainSum.Arc (d.Sphi.finite_toSet) ℓ J := by
      rcases hnprevor with h | h
      · exact absurd h hp
      · exact h
    have hnE : nprevJ ∈ E (↑d.Sphi : Set (ℤ × ℤ)) := (Nivat.PolyChainSum.mem_Arc.mp hmem).1
    have hℓn : 0 < det ℓ nprevJ := (Nivat.PolyChainSum.mem_Arc.mp hmem).2.1
    have hnJ : 0 < det nprevJ J := (Nivat.PolyChainSum.mem_Arc.mp hmem).2.2
    exact ⟨ℓ, hℓE, nprevJ, hnE, J, hJE, by omega, by omega, by omega⟩

/-- ⭐⭐⭐ **本文件的终点**：链上的窗口数据既给出环，又给出 `3 ≤ m`。

前提表与 `Nivat.CyclicOrderDPos.D_pos_of_window` 的对应七条**逐字符相同**
（`hℓE` / `hJE` / `hℓJ` / `hnprevor` / `hνJ1or` / `hnd`，外加 `DecompData`），
所以同一组 `obtain` 的输出可以同时喂这两条，不必各配一套。

⚠ `2 ≤ m` 是 `:424` 的字面（`NormalCycle.hm`）；这里的 `3 ≤ m` **不是原文的量词**，
是 `hnd` 推出来的，而 `hnd` 本身来自 2026-09-25 的横截裁决。硬规矩 5 的记账：
`3 ≤ m` 记在我方，出处是裁决，不是 `:424`。 -/
theorem exists_ncy_three_le_m_of_window (d : Nivat.Colle35.DecompData η)
    {ℓ J nprevJ νJ1 : ℤ × ℤ}
    (hℓE : ℓ ∈ E (↑d.Sphi : Set (ℤ × ℤ))) (hJE : J ∈ E (↑d.Sphi : Set (ℤ × ℤ)))
    (hℓJ : 0 < det ℓ J)
    (hnprevor : nprevJ = ℓ ∨
      nprevJ ∈ Nivat.PolyChainSum.Arc (d.Sphi.finite_toSet) ℓ J)
    (hνJ1or : νJ1 = -ℓ ∨
      νJ1 ∈ Nivat.PolyChainSum.Arc (d.Sphi.finite_toSet) J (-ℓ))
    (hnd : ¬ (nprevJ = ℓ ∧ νJ1 = -ℓ)) :
    ∃ mm, 3 ≤ mm ∧ Nonempty (NormalCycleCcw (E (↑d.Sphi : Set (ℤ × ℤ))) mm) := by
  obtain ⟨mm, -, ⟨C⟩⟩ := Nivat.NormalCycleSphi.exists_ncy_E_Sphi d
  obtain ⟨y₁, h₁, y₂, h₂, y₃, h₃, d₁₂, d₁₃, d₂₃⟩ :=
    three_indep_of_window d hℓE hJE hℓJ hnprevor hνJ1or hnd
  exact ⟨mm, three_le_m_E_Sphi d C h₁ h₂ h₃ d₁₂ d₁₃ d₂₃, ⟨C⟩⟩

/-- **横截形**：把 `hnd` 换成 2026-09-25 裁决实际提供的 `det ℓ w ≠ 0`（`w = -νJ1`）。
与 `CyclicOrderDPos.D_pos_of_window_of_transversal` 同一个入口。 -/
theorem exists_ncy_three_le_m_of_transversal (d : Nivat.Colle35.DecompData η)
    {ℓ J nprevJ νJ1 w : ℤ × ℤ}
    (hℓE : ℓ ∈ E (↑d.Sphi : Set (ℤ × ℤ))) (hJE : J ∈ E (↑d.Sphi : Set (ℤ × ℤ)))
    (hℓJ : 0 < det ℓ J)
    (hnprevor : nprevJ = ℓ ∨
      nprevJ ∈ Nivat.PolyChainSum.Arc (d.Sphi.finite_toSet) ℓ J)
    (hνJ1or : νJ1 = -ℓ ∨
      νJ1 ∈ Nivat.PolyChainSum.Arc (d.Sphi.finite_toSet) J (-ℓ))
    (hwdef : w = -νJ1) (hw : det ℓ w ≠ 0) :
    ∃ mm, 3 ≤ mm ∧ Nonempty (NormalCycleCcw (E (↑d.Sphi : Set (ℤ × ℤ))) mm) := by
  refine exists_ncy_three_le_m_of_window d hℓE hJE hℓJ hnprevor hνJ1or ?_
  rintro ⟨-, rfl⟩
  refine hw ?_
  subst hwdef
  simp only [neg_neg, det]
  ring

/-! ## §6  ⭐ 空弧的产者接上了：`Arc = ∅` 不再是 binder

第 228–229 轮我两次报「`Arc (d.Sphi.finite_toSet) y z = ∅` 全树零产者」。**那是错的**，
lane-hole3-nlmax 2026-09-25 直接读码找到了两条，都是主仓里的定理：

* `Nivat.LeafAJSelect.exists_fan_pred`（`LeafAJSelect.lean:814`）产 `Arc nprevJ J = ∅`；
  机制是对 `ord2 ν := (Arc ν J).card` 在 `Arc ℓ J` 上取极小（`Finset.exists_min_image`），
  再用 `ord_lt_of_mem_Arc_right` 反证：`Arc nprevJ J` 非空会给出 card 更小的元素。
  ⟹ 它是**扇相邻性的良基终止**，不是假设。
* `Nivat.LeafAShellNNext.exists_nnextJ`（`LeafAShellNNext.lean:37`）产 `Arc J νJ1 = ∅`，
  是同一条 `exists_fan_pred_cw` 在 `-ℓ` 槽位上的实例。

我亲读了 `exists_fan_pred` 的**证明体**和 `exists_nnextJ` 的**证明体**（都是两三行的转写）。
⚠ 我没跑这两个文件的 `check1.sh`，也没看它们的公理（§55）——它们在 `All.lean` 里、
由集成者的全量 build 覆盖。

⚠ 两条都只要 `hℓE` / `hnegℓE` / `hJE` / `hℓJ`，**没有**额外 binder。
⟹ 本节以下全部是无 binder 的链上结论。 -/

/-- ⭐⭐ **窗口两端的下标认同，无 binder。**

把 nlmax 指的两个产者接进 `adjacent_index_E_Sphi`：只要 `ℓ`、`-ℓ`、`J` 在 `E ↑d.Sphi` 里
且 `0 < det ℓ J`，就能同时拿到 `J` 的**前驱**和**后继**，并且两者在环上都与 `J` 下标相继。

⚠ `k1` 与 `k2` **不保证相等**（`C.nu` 的下标只到模 `2m`，`J` 本身有无穷多个下标）。
本条只说「存在这样的下标」，⛔ 不主张 `k1 + 1 = k2`。要把 `J` 钉到唯一下标还需要别的输入，
那一格没做。 -/
theorem exists_window_indices (d : Nivat.Colle35.DecompData η) {mm : ℕ}
    (C : NormalCycleCcw (E (↑d.Sphi : Set (ℤ × ℤ))) mm) {ℓ J : ℤ × ℤ}
    (hℓE : ℓ ∈ E (↑d.Sphi : Set (ℤ × ℤ)))
    (hnegℓE : (-ℓ) ∈ E (↑d.Sphi : Set (ℤ × ℤ)))
    (hJE : J ∈ E (↑d.Sphi : Set (ℤ × ℤ))) (hℓJ : 0 < det ℓ J) :
    ∃ nprevJ νJ1 : ℤ × ℤ, ∃ k1 k2 : ℕ,
      nprevJ ∈ E (↑d.Sphi : Set (ℤ × ℤ)) ∧ νJ1 ∈ E (↑d.Sphi : Set (ℤ × ℤ)) ∧
      0 < det nprevJ J ∧ 0 < det J νJ1 ∧
      C.nu k1 = nprevJ ∧ C.nu (k1 + 1) = J ∧
      C.nu k2 = J ∧ C.nu (k2 + 1) = νJ1 := by
  obtain ⟨nprevJ, hnE, hndet, hnempty, -⟩ :=
    Nivat.LeafAJSelect.exists_fan_pred (Sphi := d.Sphi) hℓE hJE hℓJ
  obtain ⟨νJ1, hvE, hvdet, hvempty, -⟩ :=
    Nivat.LeafAShellNNext.exists_nnextJ (Sphi := d.Sphi) hnegℓE hJE hℓJ
  obtain ⟨k1, hk1a, hk1b⟩ := adjacent_index_E_Sphi d C hnE hJE hndet hnempty
  obtain ⟨k2, hk2a, hk2b⟩ := adjacent_index_E_Sphi d C hJE hvE hvdet hvempty
  exact ⟨nprevJ, νJ1, k1, k2, hnE, hvE, hndet, hvdet, hk1a, hk1b, hk2a, hk2b⟩

/-- ⭐⭐ **`3 ≤ m` 从扇数据直接落地**，`hnprevor` / `hνJ1or` 两条析取由产者免费给出。

唯一额外要的是 `Arc ℓ J ≠ ∅`，它排掉下端点退化：`exists_fan_pred` 同时输出
`Arc nprevJ J = ∅`，若 `nprevJ = ℓ` 则那正是 `Arc ℓ J = ∅`，与前提矛盾。

⚠ 这条**不**取代 `exists_ncy_three_le_m_of_transversal`：横截形要的是 `det ℓ w ≠ 0`，
这条要的是 `Arc ℓ J ≠ ∅`，两者都是「非退化」的写法但不是同一条件，谁在链上先到手就用谁。
⛔ 不主张两者等价。 -/
theorem exists_ncy_three_le_m_of_fan (d : Nivat.Colle35.DecompData η) {ℓ J : ℤ × ℤ}
    (hℓE : ℓ ∈ E (↑d.Sphi : Set (ℤ × ℤ)))
    (hnegℓE : (-ℓ) ∈ E (↑d.Sphi : Set (ℤ × ℤ)))
    (hJE : J ∈ E (↑d.Sphi : Set (ℤ × ℤ))) (hℓJ : 0 < det ℓ J)
    (harc : Nivat.PolyChainSum.Arc (d.Sphi.finite_toSet) ℓ J ≠ ∅) :
    ∃ mm, 3 ≤ mm ∧ Nonempty (NormalCycleCcw (E (↑d.Sphi : Set (ℤ × ℤ))) mm) := by
  obtain ⟨nprevJ, -, -, hnempty, hnor⟩ :=
    Nivat.LeafAJSelect.exists_fan_pred (Sphi := d.Sphi) hℓE hJE hℓJ
  obtain ⟨νJ1, -, -, -, hvor⟩ :=
    Nivat.LeafAShellNNext.exists_nnextJ (Sphi := d.Sphi) hnegℓE hJE hℓJ
  refine exists_ncy_three_le_m_of_window d hℓE hJE hℓJ hnor hvor ?_
  rintro ⟨rfl, -⟩
  exact harc hnempty

end Sphi

end Nivat.CyclicOrderSphiInst

#print axioms Nivat.CyclicOrderSphiInst.not_between_of_arc_empty
#print axioms Nivat.CyclicOrderSphiInst.nu_add_two_mul
#print axioms Nivat.CyclicOrderSphiInst.nu_mod
#print axioms Nivat.CyclicOrderSphiInst.exists_index_lt
#print axioms Nivat.CyclicOrderSphiInst.exists_shift_lt
#print axioms Nivat.CyclicOrderSphiInst.exists_shift
#print axioms Nivat.CyclicOrderSphiInst.adjacent_index_of_empty
#print axioms Nivat.CyclicOrderSphiInst.det_eq_zero_of_diff
#print axioms Nivat.CyclicOrderSphiInst.det_eq_zero_of_same_parity
#print axioms Nivat.CyclicOrderSphiInst.three_le_m_of_three_indep
#print axioms Nivat.CyclicOrderSphiInst.par_E_Sphi
#print axioms Nivat.CyclicOrderSphiInst.adjacent_index_E_Sphi
#print axioms Nivat.CyclicOrderSphiInst.three_le_m_E_Sphi
#print axioms Nivat.CyclicOrderSphiInst.three_indep_of_window
#print axioms Nivat.CyclicOrderSphiInst.exists_ncy_three_le_m_of_window
#print axioms Nivat.CyclicOrderSphiInst.exists_ncy_three_le_m_of_transversal
#print axioms Nivat.CyclicOrderSphiInst.exists_window_indices
#print axioms Nivat.CyclicOrderSphiInst.exists_ncy_three_le_m_of_fan
