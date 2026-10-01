/-
Copyright (c) 2026. Released under Apache 2.0 license.
Authors: lane-tower-hbase
-/
import Nivat.External.Colle.ShellMink

/-!
# `escapeW` 的结论 ⟸ 落在 `shellInter` 里的任何集合对 `A` 严格

**一条引理一个模块**，这是 team-lead 第 216 轮的裁决（我提的拆分理由他复核后采纳）：
本文件的最终消费者是 `Nivat/External/Colle/RegionSteps.lean` 的 `escapeW` binder，
**那一侧不该认识 `Ax` / `KK` 这些八边形台架常量**。若与台架结论同模块，任何链侧文件
要用这条就得把整座台架拖进传递闭包——与工具盲区 2（加一条 import 炸掉从没听说过你的文件）
同源的闭包污染。

⟹ 本文件的 `import` 只有 `Nivat.External.Colle.ShellMink` 一条，
**不许** import `Nivat.External.Colle.Oct8Bench`，也不许 import 四个消费者
（`RegionSteps` / `ColleRegion` / `Case2WindowProbe` / `NfpLPreamble`）。

台架侧（`cutX` 及其全部结论）在 `Nivat/External/Colle/TowerHbaseCut.lean`，它 import 本文件。
（模块名以 team-lead 第 218 轮「`TowerHbaseCut.lean` 改成 import 新模块，其余原样留着」
为准；他第 216 轮裁决里写的 `Oct8Cut.lean` 是同一次拆分的早期命名。）

## 这条在链上是什么

`ChainExhaustInter.lean` 的 `escapeW` binder（**按标识符名定位，不写行号**——该文件的
docstring 长度反复变动，历史上的数字锚点已大面积作废）结论是**存在**式：

```
∃ g ∈ hatOf A kk vl i, ∃ t : ℕ,
  g + (t : ℤ) • w ∈ MaxEnv.shell (⋃ i, hatOf A kk vl i) vJ1 nJ cJ ε ∧
  g + (t : ℤ) • w ∉ hatOf A kk vl i
```

逐字等于「`reachSet Â_i w ∩ Ainf` 有一个点不在 `Â_i` 里」，即
`¬ (ShellMink.shellInter Â_i Ainf w ⊆ Â_i)`。本引理把它进一步归约：**任何**
`C ⊆ shellInter A Ainf w` 的严格性都蕴含它。⟹ `escapeW` 不是独立义务，
它是「某个落在壳里的集合真比 `A` 大」的推论。

⚠ 辖域（§54）：本文件**不**主张链上 `escapeW` 成立。它只把一条 binder 归约到另一条；
前件（存在这样一个严格的 `C`）仍然欠着，在台架上由 `Oct8Cut.lean` 的 `cutX` 兑现（`ε = 1` 一格）。
-/

set_option autoImplicit false

namespace Nivat.LaneTowerHbaseCut

open Nivat

/-- ⭐ **泛型**：`escapeW` 的结论 ⟸ 任何落在 `shellInter` 里的集合对 `A` 严格。
签名里**一个台架常量都没有**——只有 `ShellMink.shellInter` 与 `Set.not_subset`；
`A` / `Ainf` / `w` / `C` 全部任意。 -/
theorem escapeW_of_not_subset {A Ainf C : Set (ℤ × ℤ)} {w : ℤ × ℤ}
    (hC : C ⊆ ShellMink.shellInter A Ainf w) (hns : ¬ C ⊆ A) :
    ∃ g ∈ A, ∃ t : ℕ, g + (t : ℤ) • w ∈ Ainf ∧ g + (t : ℤ) • w ∉ A := by
  obtain ⟨z, hzC, hzA⟩ := Set.not_subset.mp hns
  obtain ⟨hzr, hzi⟩ := hC hzC
  obtain ⟨g, hg, t, hzeq⟩ := hzr
  refine ⟨g, hg, t, ?_, ?_⟩
  · rw [← hzeq]; exact hzi
  · rw [← hzeq]; exact hzA

end Nivat.LaneTowerHbaseCut

#print axioms Nivat.LaneTowerHbaseCut.escapeW_of_not_subset
