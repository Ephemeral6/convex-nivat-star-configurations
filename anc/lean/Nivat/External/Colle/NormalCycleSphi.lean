/-
# `E (↑d.Sphi)` 承载一条法向环：`NormalCycleExists` 在链上对象的实例化

lane-tower-hlev，2026-09-24（第 187 轮）。team-lead 第 187 轮裁决 1 批准落主仓，
拆自 `tmp/wip/lane-tower-hlev-periodmatch.lean` 的 §7。

**本文件的 `import` 表（`grep -n "^import"` 可核对，一条）**：
`Nivat.External.Colle.NormalCycleExists`。⚠ 文件头自报的 import 表**也会腐烂**，
改 import 的人负责同步这一段。

## §0.1  这是什么

`Nivat.NormalCycleExists.exists_ncy_of_set'` 的输入是抽象 `Set (ℤ × ℤ)`。本文件把它喂给链上
真正的对象 `E (↑d.Sphi)`，对**任意** `DecompData d` **无条件**成立——不带 `hξ`、不带 `hgen`、
不挑 `d`。终点是

```
theorem exists_ncy_E_Sphi (d : Nivat.Colle35.DecompData η) :
    ∃ m, 2 ≤ m ∧ Nonempty (NormalCycleCcw (E (↑d.Sphi : Set (ℤ × ℤ))) m)
```

## §0.2  五条输入的付款人（本轮主仓亲读，`PROTOCOL.md §42`）

| 输入 | 付款人 | 是不是我们加的量词 |
|---|---|---|
| `S.Finite` | `Nivat.LE2.finite_E_of_finite`（`LatticeEdges.lean:391`）＋ `Finset.finite_toSet` | 否 |
| `0 ∉ S` | `mem_E_iff`（`LatticeEdges.lean:219`）给 `Prim ν`，`Prim.ne_zero`（`:101`） | 否，`E` 的定义 |
| ± 闭 | `Nivat.Colle35.Sphi_negSymm`（`DecompData.lean:417`），**无条件** | **否** |
| 平行 ⟹ ±相等 | `eq_or_neg_of_prim_of_det_eq_zero`（`LatticeEdges.lean:133`）＋ 两侧的 `Prim` | 否，`Prim` 是 `E` 自带的 |
| 存在一对不平行 | `d.h_dir`（`DecompData.lean:104`）＋ `d.hm : 2 ≤ d.m` | 否，`:424`「pairwise distinct directions」的字面 |

## §0.3  ⛔ 口径限制（照抄 `NormalCycleExists.lean` §0.2，因为它们在这里同样有效）

1. ⛔ **`m` 尚未证明等于 `d.m`。** 这里的 `m` 是「上半圈的基数」；`:319` 的计数
   `|E(𝒮_φ)| = 2m` 本文件**没证也没用**。**别把 `∃ m` 读成 `m = d.m`。**
2. ⛔ **不供「指标认同」。** 环存在 ⇏ 链上某一对向量是这条环上的相邻对
   ⟹ **本文件不是缺口三的解。**
   ⚠ 被反驳的是什么，分两层，**别压成一句**（完整版见 `NormalCycleExists.lean` §0.2 第 1 条
   的 (1a) / (1b)）：
   * **一族逐对命题**——按具体 `N` 与具体有序对 `(x, y)` 逐点陈述。lane-tower-hbase 的
     `oct_chain_pair_not_cycle_adjacent`（`tmp/wip/lane-tower-hbase-sortdir.lean` §20，
     内核见证；该文件不在 build 里，**按名字 `grep`，不要按行号找**）否掉的是这一族里的
     **一个成员**：`N = oct`、配对 `(dir wOct90, nlOct)`。该反例**非空真**：
     `oct_chain_pair_satisfies_mem_and_nz`（同文件 §20）证出被否的只有 `hnoArc` 一条，
     `mem` / `ne_zero` 两条都真被满足。
   * **合成一条**——对所有 `N` 与所有配对的全称式。它被上面那**一个**成员否掉。
   ⛔ 两层不许互换。链上真正要的是（`N = E ↑d.Sphi`、链上那一对）这**另一个**成员
   （`sortdir` §21 把配对订正成 `(νJ1, +nℓ)`）；本文件与上述反例对它**都不表态**，
   按 `PROTOCOL.md §71`(i) 记「**未定**」，不记「为假」。
3. ⛔ **`E B` 与 `E ↑d.Sphi` 不得默认同集。** `DecompData.lean:115-123` 明写 Agreement
   字段 2026-09-17 已删，原文从未断言 `decomp.Sphi = S`。唯一合法通道是
   `Nivat.LE2.Enveloped.E_eq`，要 `EnvOf (↑d.Sphi) B` ＋ `(E ↑d.Sphi).Finite`。
4. ⛔ **整体在法向侧。** `E` 的成员是**边法向**（`genPerp' (h j) ⊥ h j`）；原文 `:319` 的
   「`w` 平行于某个 `h_i`」是**方向侧**，差一个 `dir`。引用时必须标明是哪一侧。
-/

import Nivat.External.Colle.NormalCycleExists

set_option autoImplicit false

namespace Nivat.NormalCycleSphi

open Nivat Nivat.LE2 Nivat.LaneTowerHlevNormalCycle Nivat.NormalCycleExists


section SphiInstance

variable {α : Type*} [AddCommMonoid α] {η : Config α}

/-- `E` 的元素是 `Prim`，故非零。 -/
theorem ang_E_Sphi_ne_zero (d : Nivat.Colle35.DecompData η) {ν : ℤ × ℤ}
    (hν : ν ∈ E (↑d.Sphi : Set (ℤ × ℤ))) : ν ≠ 0 :=
  (mem_E_iff.mp hν).1.ne_zero

/-- `E` 里两条平行的边法向只能相等或相反：两侧都是 `Prim`。 -/
theorem ang_E_Sphi_par (d : Nivat.Colle35.DecompData η) {n n' : ℤ × ℤ}
    (hn : n ∈ E (↑d.Sphi : Set (ℤ × ℤ))) (hn' : n' ∈ E (↑d.Sphi : Set (ℤ × ℤ)))
    (h0 : det n n' = 0) : n' = n ∨ n' = -n :=
  eq_or_neg_of_prim_of_det_eq_zero (mem_E_iff.mp hn).1 (mem_E_iff.mp hn').1 h0

/-- 主仓 `Nivat.ColleReg.E_Sphi_eq_E_zonoF`（`TowerConstruct.lean:48`）的 `Config α` 推广。
⚠ 主仓那条把 `ξ : Config ℤ` 钉死（`TowerConstruct.lean:39` 的 section variable），
本节的对象是任意 `Config α`，所以不能直接引；证明逐字相同
（`conv_Sphi_eq_conv_zonoF`，`TowerConstruct.lean:43`）。 -/
theorem ang_E_Sphi_eq_zonoF (d : Nivat.Colle35.DecompData η) :
    E (↑d.Sphi : Set (ℤ × ℤ)) = E (↑(zonoF Finset.univ d.h) : Set (ℤ × ℤ)) := by
  have hconv : Conv d.Sphi = Conv (zonoF Finset.univ d.h) := by
    rw [d.Sphi_eq, Conv_supp_prod_eq_Conv_zonoF Finset.univ d.h (fun i _ => d.h_ne i)]
  exact E_congr_of_Conv_eq hconv

/-- **`b3_colle2.txt:319` 的枚举形**，搬到 `E ↑d.Sphi` 上。
⚠ 与主仓 `Nivat.Colle35.DecompData.mem_E_Sphi_iff`（`ANormal.lean:320`）**不是同一条**：
那条是 `Prim n ∧ ∃ i, dot n (d.h i) = 0` 的 `dot` 形，这条是 `± genPerp'` 的**枚举**形
（`E` 可穷举，`hnoArc` 的 `∀` 靠它收成有限检查）。名字已避开。 -/
theorem ang_mem_E_Sphi_genPerp_iff (d : Nivat.Colle35.DecompData η) (ν : ℤ × ℤ) :
    ν ∈ E (↑d.Sphi : Set (ℤ × ℤ)) ↔
      ∃ j : Fin d.m, ν = genPerp' (d.h j) ∨ ν = -genPerp' (d.h j) := by
  rw [ang_E_Sphi_eq_zonoF d]
  exact E_zonoF_eq_genPerp_set d.h d.h_ne d.h_dir ν

/-- 非退化：`d.hm : 2 ≤ d.m` 配 `d.h_dir` 给出两条不平行的边法向。 -/
theorem ang_E_Sphi_nondeg (d : Nivat.Colle35.DecompData η) :
    ∃ a ∈ E (↑d.Sphi : Set (ℤ × ℤ)), ∃ b ∈ E (↑d.Sphi : Set (ℤ × ℤ)), det a b ≠ 0 := by
  have hm := d.hm
  have h0 : (0 : ℕ) < d.m := by omega
  have h1 : (1 : ℕ) < d.m := by omega
  refine ⟨genPerp' (d.h ⟨0, h0⟩),
    (ang_mem_E_Sphi_genPerp_iff d _).mpr ⟨⟨0, h0⟩, Or.inl rfl⟩,
    genPerp' (d.h ⟨1, h1⟩),
    (ang_mem_E_Sphi_genPerp_iff d _).mpr ⟨⟨1, h1⟩, Or.inl rfl⟩, ?_⟩
  intro hz
  refine d.h_dir ⟨0, h0⟩ ⟨1, h1⟩ (by simp [Fin.ext_iff]) ?_
  have hne0 : genPerp' (d.h ⟨0, h0⟩) ≠ 0 := (genPerp'_prim (d.h_ne _)).ne_zero
  have hne1 : genPerp' (d.h ⟨1, h1⟩) ≠ 0 := (genPerp'_prim (d.h_ne _)).ne_zero
  have hd0 : dot (genPerp' (d.h ⟨0, h0⟩)) (d.h ⟨0, h0⟩) = 0 := by
    rw [dot_comm]; exact dot_genPerp' (d.h_ne _)
  have hd1 : dot (genPerp' (d.h ⟨1, h1⟩)) (d.h ⟨1, h1⟩) = 0 := by
    rw [dot_comm]; exact dot_genPerp' (d.h_ne _)
  have hd1' : dot (genPerp' (d.h ⟨1, h1⟩)) (d.h ⟨0, h0⟩) = 0 :=
    pm_dot_of_par hne0 hz hd0
  exact pm_det_eq_zero_of_perp hne1 hd1' hd1

/-- **本文件的终点**：对**任意** `DecompData`，`E ↑𝒮_φ` 上存在一条 `σ = 1` 的法向环。
即 `b3_colle2.txt:424` 的枚举句在链上真有见证对象，`anti` 不再是障碍。
有限性直接用主仓现货 `finite_E_of_finite`（`LatticeEdges.lean:391`）＋ `Finset.finite_toSet`。 -/
theorem exists_ncy_E_Sphi (d : Nivat.Colle35.DecompData η) :
    ∃ m, 2 ≤ m ∧ Nonempty (NormalCycleCcw (E (↑d.Sphi : Set (ℤ × ℤ))) m) :=
  exists_ncy_of_set' (finite_E_of_finite d.Sphi.finite_toSet)
    (fun _ hn => ang_E_Sphi_ne_zero d hn)
    (fun n hn => (Nivat.Colle35.Sphi_negSymm d n).mp hn)
    (fun _ hn _ hn' h0 => ang_E_Sphi_par d hn hn' h0)
    (ang_E_Sphi_nondeg d)

end SphiInstance

end Nivat.NormalCycleSphi

/-! ## 公理审计（分母＝本文件声明数 6，含 private；由
`tmp/_hlev_audit233.py` 生成，一条声明一行——短块照样打出干净列表，
却会留下未审计的声明）。 -/

#print axioms Nivat.NormalCycleSphi.ang_E_Sphi_ne_zero
#print axioms Nivat.NormalCycleSphi.ang_E_Sphi_par
#print axioms Nivat.NormalCycleSphi.ang_E_Sphi_eq_zonoF
#print axioms Nivat.NormalCycleSphi.ang_mem_E_Sphi_genPerp_iff
#print axioms Nivat.NormalCycleSphi.ang_E_Sphi_nondeg
#print axioms Nivat.NormalCycleSphi.exists_ncy_E_Sphi
