/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.DNonnegWindow

/-!
# `0 < D`：`D_nonneg_of_window` 的严格化，及其边界的精确刻画（lane-env-refute）

## §0 这个文件回答的问题

主仓已有 `Nivat.LaneHole3Nlmax.D_nonneg_of_window`（`DNonnegWindow.lean:49`），结论是
**非严格**的 `0 ≤ det nprevJ νJ1`。本文件回答「什么时候严格」，并证明答案是**充要**的：

> `0 < det nprevJ νJ1` ⟺ ¬(`nprevJ = ℓ` ∧ `νJ1 = -ℓ`)。

即：`D_nonneg_of_window` 的下界**紧**，且唯一取等的构型是两端同时退化——`nprevJ` 落在窗口
下端点 `ℓ` 上、`νJ1` 落在上端点 `-ℓ` 上。用 `b3_colle2.txt:424` 的环序语言说，这正是
`m = 2` 的构型（`ν_ι` 与 `ν_{ι+1} = -ν_ι` 之间没有别的面）。

## §1 原文对应

- `:424`（Lemma 3.5 的假设句）／`:764`（§4.2 重复同一句）：面法向的环序。本文件用到的
  只是它的一个推论——`Arc` 成员的 `det` 严格为正（`PolyChainSum.mem_Arc`），退化到端点时
  为零。**不新增任何 `Prop`**。
- `:432`：窗口 `ι+1 ≤ J ≤ ι+m-1`。`hnprevor` 的左支 `nprevJ = ℓ` 是下端点 `J = ι+1`，
  `hνJ1or` 的左支 `νJ1 = -ℓ` 是上端点 `J = ι+m-1`。
- `:506`：`J`-选取；由 `exists_fan_pred` / `exists_nnextJ` 转写，前提逐字沿用
  `D_nonneg_of_window` 的签名，不增不减。

## §2 一名多物警告（⚠ 接线前必读）

- 本文件的 `νJ1` 与 `D_nonneg_of_window` 的 `νJ1` 同物，都是 **`ν_{J+1}`**（`hνJ1pos :
  0 < det J νJ1` 把它钉在 `J` 的**上**侧）。
- 链上另有一个 `vJ1`（`LeafAJSelect.lean:832`、`ANormal.lean:685`、`OrderThree.lean:115`、
  `LeafASwept.lean:24`），它是 **`v_{ℓ_{J-1}}`**，在 `J` 的**下**侧，对应本文件的 `nprevJ`。
  两个名字只差大小写，接错不会有类型错误，只会变成符号错误。
- team-lead 给的 `w`（原文 `-v_{ℓ_{J+1}}`）满足 `w = -νJ1` 方向，故
  `det ℓ w ≠ 0 ↔ det ℓ νJ1 ≠ 0`（`det_neg_right'`）；这就是 `D_pos_of_window_of_det_ne`
  的前提形状。

## §3 不主张什么

⛔ 本文件不主张 `dot nJ w = -1`，不主张 `det J ν_{J+1} = 1`，不主张任何**带号**的
`det ℓ w`（只用 `≠ 0`）。窗口两端的退化与否是本文件唯一使用的方向信息。

⛔ **`hnd` / `hw` 不是定理，不许当无条件 binder 派工。** 退化构型在扇上**真会发生**：
正方形（`2m = 4`，即 `m = 2`）取 `ν_{J-1} = (1,0)`、`ν_J = (0,1)`、`ν_{J+1} = (-1,0)`，
三条扇 binder 全满足而 `D = 0`（lane-leafa-shell 的 `square_D_eq_zero`，
`tmp/wip/lane-leafa-shell-shellenv.lean` §35.0）。本文件的贡献是把「什么时候 `D = 0`」
从「未知的第三支」变成**一条可判定的等式**（`D_pos_iff_nondegenerate`），
供给这条侧条件仍是消费者的义务。

## §4 与已有结果的关系（接线前对量纲）

- lane-leafa-shell `nu_next_eq_neg_prev_of_D_eq_zero`（`shellenv.lean:3229`）：由 `Prim`
  两条 ＋ `0 < d` ＋ `0 < e` 推 `nu = -nprevJ`。本文件 `degenerate_of_D_eq_zero` 改从
  窗口前提推，结论多钉一半（`nprevJ = ℓ`）。两条**相容**，互为独立复核。
- lane-tower-hlev `NormalCycle.D_pos`（`NormalCycle.lean`，外挂前提 `3 ≤ m`）：同一事实的
  环序语言版。本文件 `CyclicOrderWindow.three_le_m_of_window_endpoints` 把 `3 ≤ m` 从
  `det vl w ≠ 0` 推出来；本文件则整条绕开 `NormalCycle`，直接在 `E`/`Arc` 语言里做，
  **不需要把链的 `E ↑𝒮_φ` 实例化成 `NormalCycle`**。
-/

set_option autoImplicit false

namespace Nivat.CyclicOrderDPos

open Nivat Nivat.LE2 Nivat.PolyChainSum

variable {Sphi : Finset (ℤ × ℤ)}

/-- 三项 Plücker 恒等式：`det ℓ J * det n v = det ℓ n * det J v + det ℓ v * det n J`。
纯代数，`det` 展开后 `ring`。 -/
theorem det_plucker (ℓ J n v : ℤ × ℤ) :
    det ℓ J * det n v = det ℓ n * det J v + det ℓ v * det n J := by
  simp only [det]; ring

/-- 窗口下端：`nprevJ` 若不等于 `ℓ`，则 `hnprevor` 的右支给出**严格**的 `0 < det ℓ nprevJ`。
（`D_nonneg_of_window` 内部只取了它的 `.le`。） -/
theorem det_lo_pos_of_ne {ℓ J nprevJ : ℤ × ℤ}
    (hnprevor : nprevJ = ℓ ∨ nprevJ ∈ Nivat.PolyChainSum.Arc (Sphi.finite_toSet) ℓ J)
    (hne : nprevJ ≠ ℓ) : 0 < det ℓ nprevJ := by
  rcases hnprevor with rfl | hmem
  · exact absurd rfl hne
  · exact (mem_Arc.mp hmem).2.1

/-- 窗口上端：`νJ1` 若不等于 `-ℓ`，则 `hνJ1or` 的右支给出**严格**的 `0 < det ℓ νJ1`。 -/
theorem det_hi_pos_of_ne {ℓ J νJ1 : ℤ × ℤ}
    (hνJ1or : νJ1 = -ℓ ∨ νJ1 ∈ Nivat.PolyChainSum.Arc (Sphi.finite_toSet) J (-ℓ))
    (hne : νJ1 ≠ -ℓ) : 0 < det ℓ νJ1 := by
  rcases hνJ1or with rfl | hmem
  · exact absurd rfl hne
  · have h2 : 0 < det νJ1 (-ℓ) := (mem_Arc.mp hmem).2.2
    have h3 : det νJ1 (-ℓ) = -det νJ1 ℓ := Nivat.LaneHole3Nlmax.det_neg_right' νJ1 ℓ
    have h4 : det νJ1 ℓ = -det ℓ νJ1 := det_skew νJ1 ℓ
    omega

/-- 窗口下端非严格形（`nprevJ = ℓ` 时取等）。 -/
theorem det_lo_nonneg {ℓ J nprevJ : ℤ × ℤ}
    (hnprevor : nprevJ = ℓ ∨ nprevJ ∈ Nivat.PolyChainSum.Arc (Sphi.finite_toSet) ℓ J) :
    0 ≤ det ℓ nprevJ := by
  rcases hnprevor with rfl | hmem
  · simp [det_self]
  · exact (mem_Arc.mp hmem).2.1.le

/-- 窗口上端非严格形（`νJ1 = -ℓ` 时取等）。 -/
theorem det_hi_nonneg {ℓ J νJ1 : ℤ × ℤ}
    (hνJ1or : νJ1 = -ℓ ∨ νJ1 ∈ Nivat.PolyChainSum.Arc (Sphi.finite_toSet) J (-ℓ)) :
    0 ≤ det ℓ νJ1 := by
  rcases hνJ1or with rfl | hmem
  · have h : det ℓ (-ℓ) = -det ℓ ℓ := Nivat.LaneHole3Nlmax.det_neg_right' ℓ ℓ
    simp [det_self] at h; omega
  · exact (det_hi_pos_of_ne (Sphi := Sphi) (J := J) (Or.inr hmem)
      (fun hEq => by
        have h2 : 0 < det νJ1 (-ℓ) := (mem_Arc.mp hmem).2.2
        rw [hEq] at h2
        have h3 : det (-ℓ) (-ℓ) = 0 := det_self (-ℓ)
        omega)).le

set_option linter.unusedVariables false in
/-- **`0 < D`，严格形。**  前提与 `D_nonneg_of_window`（`DNonnegWindow.lean:49`）**逐字相同**，
只多一条侧条件 `hnd`：窗口两端不同时退化。

⚠ 七条前提（`hℓE` / `hnegℓE` / `hJE` / `hnprevE` / `hnprevempty` / `hνJ1E` / `hνJ1empty`）
**接受但不用**，与 `D_nonneg_of_window` 同样处理：消费者手上本来就有，保留是为了让两条定理
的实参表逐位对齐，换用时不必改调用点。故此处关掉 unusedVariables linter。 -/
theorem D_pos_of_window {ℓ J nprevJ νJ1 : ℤ × ℤ}
    (hℓE : ℓ ∈ E (↑Sphi : Set (ℤ × ℤ))) (hnegℓE : (-ℓ) ∈ E (↑Sphi : Set (ℤ × ℤ)))
    (hJE : J ∈ E (↑Sphi : Set (ℤ × ℤ))) (hℓJ : 0 < det ℓ J)
    (hnprevE : nprevJ ∈ E (↑Sphi : Set (ℤ × ℤ)))
    (hnprevdet : 0 < det nprevJ J)
    (hnprevempty : Nivat.PolyChainSum.Arc (Sphi.finite_toSet) nprevJ J = ∅)
    (hnprevor : nprevJ = ℓ ∨ nprevJ ∈ Nivat.PolyChainSum.Arc (Sphi.finite_toSet) ℓ J)
    (hνJ1E : νJ1 ∈ E (↑Sphi : Set (ℤ × ℤ)))
    (hνJ1pos : 0 < det J νJ1)
    (hνJ1empty : Nivat.PolyChainSum.Arc (Sphi.finite_toSet) J νJ1 = ∅)
    (hνJ1or : νJ1 = -ℓ ∨ νJ1 ∈ Nivat.PolyChainSum.Arc (Sphi.finite_toSet) J (-ℓ))
    (hnd : ¬ (nprevJ = ℓ ∧ νJ1 = -ℓ)) :
    0 < det nprevJ νJ1 := by
  have hlo : 0 ≤ det ℓ nprevJ := det_lo_nonneg (Sphi := Sphi) (J := J) hnprevor
  have hhi : 0 ≤ det ℓ νJ1 := det_hi_nonneg (Sphi := Sphi) (J := J) hνJ1or
  have hid : det ℓ J * det nprevJ νJ1
      = det ℓ nprevJ * det J νJ1 + det ℓ νJ1 * det nprevJ J := det_plucker ℓ J nprevJ νJ1
  have hrhs : 0 < det ℓ nprevJ * det J νJ1 + det ℓ νJ1 * det nprevJ J := by
    by_cases hp : nprevJ = ℓ
    · have hq : νJ1 ≠ -ℓ := fun h => hnd ⟨hp, h⟩
      have hhi' : 0 < det ℓ νJ1 := det_hi_pos_of_ne (Sphi := Sphi) (J := J) hνJ1or hq
      nlinarith [mul_nonneg hlo hνJ1pos.le, mul_pos hhi' hnprevdet]
    · have hlo' : 0 < det ℓ nprevJ := det_lo_pos_of_ne (Sphi := Sphi) (J := J) hnprevor hp
      nlinarith [mul_pos hlo' hνJ1pos, mul_nonneg hhi hnprevdet.le]
  by_cases hpos : 0 < det nprevJ νJ1
  · exact hpos
  · have hcon : det nprevJ νJ1 ≤ 0 := not_lt.mp hpos
    linarith [mul_nonpos_of_nonneg_of_nonpos hℓJ.le hcon]

/-- **边界取等**：两端同时退化时 `D` **恰为** `0`，故 `D_nonneg_of_window` 的下界是紧的，
且 `D_pos_of_window` 的侧条件 `hnd` **不可去**。 -/
theorem D_eq_zero_of_degenerate {ℓ nprevJ νJ1 : ℤ × ℤ}
    (hp : nprevJ = ℓ) (hq : νJ1 = -ℓ) : det nprevJ νJ1 = 0 := by
  subst hp; subst hq
  have h : det nprevJ (-nprevJ) = -det nprevJ nprevJ :=
    Nivat.LaneHole3Nlmax.det_neg_right' nprevJ nprevJ
  have h2 : det nprevJ nprevJ = 0 := det_self nprevJ
  omega

/-- **充要刻画**：在 `D_nonneg_of_window` 的全部前提下，`0 < D` 当且仅当窗口两端不同时退化。 -/
theorem D_pos_iff_nondegenerate {ℓ J nprevJ νJ1 : ℤ × ℤ}
    (hℓE : ℓ ∈ E (↑Sphi : Set (ℤ × ℤ))) (hnegℓE : (-ℓ) ∈ E (↑Sphi : Set (ℤ × ℤ)))
    (hJE : J ∈ E (↑Sphi : Set (ℤ × ℤ))) (hℓJ : 0 < det ℓ J)
    (hnprevE : nprevJ ∈ E (↑Sphi : Set (ℤ × ℤ)))
    (hnprevdet : 0 < det nprevJ J)
    (hnprevempty : Nivat.PolyChainSum.Arc (Sphi.finite_toSet) nprevJ J = ∅)
    (hnprevor : nprevJ = ℓ ∨ nprevJ ∈ Nivat.PolyChainSum.Arc (Sphi.finite_toSet) ℓ J)
    (hνJ1E : νJ1 ∈ E (↑Sphi : Set (ℤ × ℤ)))
    (hνJ1pos : 0 < det J νJ1)
    (hνJ1empty : Nivat.PolyChainSum.Arc (Sphi.finite_toSet) J νJ1 = ∅)
    (hνJ1or : νJ1 = -ℓ ∨ νJ1 ∈ Nivat.PolyChainSum.Arc (Sphi.finite_toSet) J (-ℓ)) :
    0 < det nprevJ νJ1 ↔ ¬ (nprevJ = ℓ ∧ νJ1 = -ℓ) := by
  constructor
  · intro hpos hdeg
    have := D_eq_zero_of_degenerate hdeg.1 hdeg.2
    omega
  · intro hnd
    exact D_pos_of_window hℓE hnegℓE hJE hℓJ hnprevE hnprevdet hnprevempty hnprevor
      hνJ1E hνJ1pos hνJ1empty hνJ1or hnd

/-- **消费者形**：侧条件由 `det ℓ νJ1 ≠ 0` 供给。这正是 team-lead 给的内核见证数据
（`ShellMink.lean:588` ＋ `FillCoverWitness.lean` §1 合成的「`w` 横截于 `vl`」，
`w = -ν_{J+1}` 故 `det ℓ w ≠ 0 ↔ det ℓ νJ1 ≠ 0`）。**只用 `≠ 0`，不用符号。** -/
theorem D_pos_of_window_of_det_ne {ℓ J nprevJ νJ1 : ℤ × ℤ}
    (hℓE : ℓ ∈ E (↑Sphi : Set (ℤ × ℤ))) (hnegℓE : (-ℓ) ∈ E (↑Sphi : Set (ℤ × ℤ)))
    (hJE : J ∈ E (↑Sphi : Set (ℤ × ℤ))) (hℓJ : 0 < det ℓ J)
    (hnprevE : nprevJ ∈ E (↑Sphi : Set (ℤ × ℤ)))
    (hnprevdet : 0 < det nprevJ J)
    (hnprevempty : Nivat.PolyChainSum.Arc (Sphi.finite_toSet) nprevJ J = ∅)
    (hnprevor : nprevJ = ℓ ∨ nprevJ ∈ Nivat.PolyChainSum.Arc (Sphi.finite_toSet) ℓ J)
    (hνJ1E : νJ1 ∈ E (↑Sphi : Set (ℤ × ℤ)))
    (hνJ1pos : 0 < det J νJ1)
    (hνJ1empty : Nivat.PolyChainSum.Arc (Sphi.finite_toSet) J νJ1 = ∅)
    (hνJ1or : νJ1 = -ℓ ∨ νJ1 ∈ Nivat.PolyChainSum.Arc (Sphi.finite_toSet) J (-ℓ))
    (hw : det ℓ νJ1 ≠ 0) :
    0 < det nprevJ νJ1 := by
  refine D_pos_of_window hℓE hnegℓE hJE hℓJ hnprevE hnprevdet hnprevempty hnprevor
    hνJ1E hνJ1pos hνJ1empty hνJ1or ?_
  rintro ⟨-, rfl⟩
  exact hw (by
    have h : det ℓ (-ℓ) = -det ℓ ℓ := Nivat.LaneHole3Nlmax.det_neg_right' ℓ ℓ
    have h2 : det ℓ ℓ = 0 := det_self ℓ
    omega)

/-- **`w`-形**：侧条件写成 team-lead 原始的 `det ℓ w ≠ 0`，其中 `w = -νJ1`。 -/
theorem D_pos_of_window_of_transversal {ℓ J nprevJ νJ1 w : ℤ × ℤ}
    (hℓE : ℓ ∈ E (↑Sphi : Set (ℤ × ℤ))) (hnegℓE : (-ℓ) ∈ E (↑Sphi : Set (ℤ × ℤ)))
    (hJE : J ∈ E (↑Sphi : Set (ℤ × ℤ))) (hℓJ : 0 < det ℓ J)
    (hnprevE : nprevJ ∈ E (↑Sphi : Set (ℤ × ℤ)))
    (hnprevdet : 0 < det nprevJ J)
    (hnprevempty : Nivat.PolyChainSum.Arc (Sphi.finite_toSet) nprevJ J = ∅)
    (hnprevor : nprevJ = ℓ ∨ nprevJ ∈ Nivat.PolyChainSum.Arc (Sphi.finite_toSet) ℓ J)
    (hνJ1E : νJ1 ∈ E (↑Sphi : Set (ℤ × ℤ)))
    (hνJ1pos : 0 < det J νJ1)
    (hνJ1empty : Nivat.PolyChainSum.Arc (Sphi.finite_toSet) J νJ1 = ∅)
    (hνJ1or : νJ1 = -ℓ ∨ νJ1 ∈ Nivat.PolyChainSum.Arc (Sphi.finite_toSet) J (-ℓ))
    (hwdef : w = -νJ1) (hw : det ℓ w ≠ 0) :
    0 < det nprevJ νJ1 := by
  refine D_pos_of_window_of_det_ne hℓE hnegℓE hJE hℓJ hnprevE hnprevdet hnprevempty hnprevor
    hνJ1E hνJ1pos hνJ1empty hνJ1or ?_
  intro h0
  apply hw
  rw [hwdef]
  have := Nivat.LaneHole3Nlmax.det_neg_right' ℓ νJ1
  omega

/-- **窗口上端的 `det` 判据**：在 `hνJ1or` 之下，`det ℓ νJ1 = 0` **当且仅当** `νJ1 = -ℓ`。
（`Arc` 成员给严格正，端点给零；没有第三种。） -/
theorem det_hi_eq_zero_iff {ℓ J νJ1 : ℤ × ℤ}
    (hνJ1or : νJ1 = -ℓ ∨ νJ1 ∈ Nivat.PolyChainSum.Arc (Sphi.finite_toSet) J (-ℓ)) :
    det ℓ νJ1 = 0 ↔ νJ1 = -ℓ := by
  constructor
  · intro h0
    by_contra hne
    have := det_hi_pos_of_ne (Sphi := Sphi) (J := J) hνJ1or hne
    omega
  · rintro rfl
    have h : det ℓ (-ℓ) = -det ℓ ℓ := Nivat.LaneHole3Nlmax.det_neg_right' ℓ ℓ
    have h2 : det ℓ ℓ = 0 := det_self ℓ
    omega

set_option linter.unusedVariables false in
/-- **辨识退化构型**：在 `D_nonneg_of_window` 的全部前提下，`D = 0` **强制**两端同时退化。
这比 lane-leafa-shell 的 `nu_next_eq_neg_prev_of_D_eq_zero`
（`tmp/wip/lane-leafa-shell-shellenv.lean:3229`，由 `Prim` 推 `nu = -nprevJ`）多给一半：
它还钉住 `nprevJ = ℓ`，即 `J` 落在窗口**下**端点 `ι+1` 上。两条结论相容——本条的
`nprevJ = ℓ ∧ νJ1 = -ℓ` 蕴含 `νJ1 = -nprevJ`。 -/
theorem degenerate_of_D_eq_zero {ℓ J nprevJ νJ1 : ℤ × ℤ}
    (hℓE : ℓ ∈ E (↑Sphi : Set (ℤ × ℤ))) (hnegℓE : (-ℓ) ∈ E (↑Sphi : Set (ℤ × ℤ)))
    (hJE : J ∈ E (↑Sphi : Set (ℤ × ℤ))) (hℓJ : 0 < det ℓ J)
    (hnprevE : nprevJ ∈ E (↑Sphi : Set (ℤ × ℤ)))
    (hnprevdet : 0 < det nprevJ J)
    (hnprevempty : Nivat.PolyChainSum.Arc (Sphi.finite_toSet) nprevJ J = ∅)
    (hnprevor : nprevJ = ℓ ∨ nprevJ ∈ Nivat.PolyChainSum.Arc (Sphi.finite_toSet) ℓ J)
    (hνJ1E : νJ1 ∈ E (↑Sphi : Set (ℤ × ℤ)))
    (hνJ1pos : 0 < det J νJ1)
    (hνJ1empty : Nivat.PolyChainSum.Arc (Sphi.finite_toSet) J νJ1 = ∅)
    (hνJ1or : νJ1 = -ℓ ∨ νJ1 ∈ Nivat.PolyChainSum.Arc (Sphi.finite_toSet) J (-ℓ))
    (h0 : det nprevJ νJ1 = 0) :
    nprevJ = ℓ ∧ νJ1 = -ℓ := by
  by_contra hnd
  have := D_pos_of_window hℓE hnegℓE hJE hℓJ hnprevE hnprevdet hnprevempty hnprevor
    hνJ1E hνJ1pos hνJ1empty hνJ1or hnd
  omega

end Nivat.CyclicOrderDPos

#print axioms Nivat.CyclicOrderDPos.det_plucker
#print axioms Nivat.CyclicOrderDPos.det_lo_pos_of_ne
#print axioms Nivat.CyclicOrderDPos.det_hi_pos_of_ne
#print axioms Nivat.CyclicOrderDPos.det_lo_nonneg
#print axioms Nivat.CyclicOrderDPos.det_hi_nonneg
#print axioms Nivat.CyclicOrderDPos.D_pos_of_window
#print axioms Nivat.CyclicOrderDPos.D_eq_zero_of_degenerate
#print axioms Nivat.CyclicOrderDPos.D_pos_iff_nondegenerate
#print axioms Nivat.CyclicOrderDPos.D_pos_of_window_of_det_ne
#print axioms Nivat.CyclicOrderDPos.D_pos_of_window_of_transversal
#print axioms Nivat.CyclicOrderDPos.det_hi_eq_zero_iff
#print axioms Nivat.CyclicOrderDPos.degenerate_of_D_eq_zero
