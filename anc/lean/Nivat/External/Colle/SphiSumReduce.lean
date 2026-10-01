/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.NlmaxReduce
import Nivat.External.Colle.SphiSumCrit
import Nivat.External.Colle.FanOrderCriterion

/-!
# `hstrict` 的第三条等价刻画：求和判据

lane-hole3-nlmax，2026-09-24。派工（team-lead 第 192 轮）：把
`Nivat.NlmaxReduce.hstrict_iff_nlmax`（`NlmaxReduce.lean`，`hstrict ↔ ∀ b ∈ Sφ, dot nl b ≤ dot nl a`）
与 `Nivat.LaneTowerPkgNlmaxSum.max_at_Sphi_iff_sum`（`SphiSumCrit.lean`，
`(∀ b ∈ d.Sphi, dot q b ≤ dot q a) ↔ ∑ j : Fin d.m, max 0 (dot q (d.h j)) ≤ dot q a`）
在 `q := nl` 上串起来。

## 为什么另开文件，不改 `NlmaxReduce.lean`

`NlmaxReduce.lean` **在主定理闭包里**：`RegionSteps.lean` 与 `FanOrderCriterion.lean`
（lane-tower-hlev）都直接 `import` 它。往它加 `import Nivat.External.Colle.SphiSumCrit`
会把 `SphiSumCrit` 的整份闭包（15 条声明）注入 `RegionSteps`/`Main`；为一条打包引理换取
这样的闭包扩张不值得（工具盲区 2）。本文件单向依赖 `NlmaxReduce` ＋ `SphiSumCrit`，
`RegionSteps` 目前不 import 它，`NlmaxReduce.lean` 一个字不动。

## 消费者接口（逐字，不引用行号，标识符跨轮不动）

`RegionSteps.lean`（`exists_cutResidualR_of_claim46` 体内）`have hstrict` 的目标：
`∀ b ∈ Sφ, dot m a < dot m b → dot nℓ b ≤ dot nℓ a`，`Sφ = d.toDecompData.Sphi`。
本文件把它换成 `d`-参数形（`Sφ := d.Sphi`），与 `max_at_Sphi_iff_sum` 的参数形状对齐——
若坚持抽象 `Sφ` 会逼出一条多余的 `Sφ = d.Sphi` 桥 binder，是白债（team-lead 第 193 轮裁定）。

## 与另外两条等价刻画的关系（⚠ 右边不是同一个东西，不是重复造轮子）

`hstrict` 目前在主仓有三条等价刻画排队：

1. **本文件 `hstrict_iff_sum`（求和形）**：右边 `∑ j : Fin d.m, max 0 (dot nl (d.h j)) ≤ dot nl a`，
   说的是「`nℓ` 落在 `𝒮_φ` 在 `a` 处法锥里」，用生成元正部之和刻画。
2. **`Nivat.NlmaxReduce.hstrict_iff_nlmax`（点侧形）**：右边 `∀ b ∈ Sφ, dot nl b ≤ dot nl a`，
   纯 `dot`-算术打包，不涉及生成元 `d.h`。本文件的求和形是在它之上再套一层
   `max_at_Sphi_iff_sum`，**不是**独立证明同一件事两遍。
3. **`Nivat.LaneTowerHlevFanOrder.hstrict_iff_wadj` / `hstrict_iff_det_gen`（生成元/扇序形，
   lane-tower-hlev, `FanOrderCriterion.lean`）**：右边分别是 `Hole3Room.lean` 的 `hwadj` body（扇区不含 `E ↑d.Sphi`
   的元素）与 `∀ j, det (d.h j) vl * det (d.h j) w ≤ 0`（带方向的 `det` 判据）。
   与本文件的求和判据是**不同的量**（一个按符号对分类，一个按正部求和），只是两者
   都以 `hstrict_iff_nlmax` 为共同上游，右边彼此不必逐字相等，也未证明互推。

⚠ **三条都不是洞 3 的兑现**。右边的不等式/判据本身都还没有从链上现成 binder 证出——
`SphiSumCrit.lean` §D 的原话保留：本文件右边那条求和不等式说「`nℓ` 落在 `𝒮_φ` 在 `a`
处法锥里」，链上现成的 binder 只把 `-m`/`nℓ` 钉在 `(vl,w)` 对偶基的坐标轴上，**没有**
把每个 `h_j` 钉进同一象限，仍是显式欠账。
-/

set_option autoImplicit false

namespace Nivat.SphiSumReduce

open Nivat Nivat.LE2 Nivat.Colle35
open scoped Pointwise

variable {α : Type*} [AddCommMonoid α]

/-- **求和判据版的 `hstrict` 归约**：`hstrict_iff_nlmax`（`NlmaxReduce.lean`）
接 `max_at_Sphi_iff_sum`（`SphiSumCrit.lean`），在 `q := nl` 上串起来。中项
（`hstrict_iff_nlmax` 的 RHS 与 `max_at_Sphi_iff_sum` 的 LHS）由 `.trans` 的类型检查
逐字符核验为同一个 `Prop`（§58），未插入任何 `simp`/`show` 去凑。 -/
theorem hstrict_iff_sum {η : Config α} (d : DecompData η) {m w nl a : ℤ × ℤ}
    (hwneg : dot nl w < 0)
    (ha_min : ∀ b ∈ d.Sphi, dot m a ≤ dot m b)
    (ha_end : ∀ b ∈ d.Sphi, dot m b = dot m a → ∃ t : ℕ, b = a + (t : ℤ) • w) :
    (∀ b ∈ d.Sphi, dot m a < dot m b → dot nl b ≤ dot nl a) ↔
      ∑ j : Fin d.m, max 0 (dot nl (d.h j)) ≤ dot nl a :=
  (Nivat.NlmaxReduce.hstrict_iff_nlmax hwneg ha_min ha_end).trans
    (Nivat.LaneTowerPkgNlmaxSum.max_at_Sphi_iff_sum d nl a)

/-- **第四条：`sum` 判据与 `det` 判据的桥接**（team-lead 派工，本轮）。

硬规矩 6 数值实例（`tmp/wip/lane-hole3-nlmax-sumdet.lean` 手算，本条落地时用 `decide`
在 `dGZ` 台架上重放）：`hGZ = ![(0,1),(-1,1),(-1,0),(-1,-1)]`、`nlGZ=(1,0)`、`vlGZ=(0,1)`——
坏 `w=(-1,0)`（`a=(-1,-1)`）：求和判据 `0 ≤ -1` 假，det 判据在 `j=3` 处 `1 ≤ 0` 假，同假；
好 `w=(-1,-1)`（`a=(0,0)`）：求和判据 `0 ≤ 0` 真，det 判据逐项 `0,-2,-1,0` 全 `≤0` 真，同真。
两条判据在这张台架上确实分得开，桥接有意义。

证法：`hstrict_iff_sum`（本文件）与 `Nivat.LaneTowerHlevFanOrder.hstrict_iff_det_gen_native`
（`FanOrderCriterion.lean`）左边逐字都是同一个 `hstrict`（`d.toDecompData` 侧的
`∀ b ∈ Sphi, dot mv a < dot mv b → dot nl b ≤ dot nl a`），`.symm.trans` 直接拼出
`sum ↔ det`，前提表原样复用 `hstrict_iff_det_gen_native` 的十一条链上原生 binder。

**前提表对齐**（team-lead 要求逐条核对，不只看 `.trans` 编过）：`hstrict_iff_sum` 的三条
前提 `hwneg` / `ha_min` / `ha_end` 是 `hstrict_iff_det_gen_native` 十一条
（`hvlp` / `hwp` / `hperp` / `hdetpos` / `hnu` / `hwneg` / `hmw` / `hmvl` / `ha` /
`ha_min` / `ha_end`）里现成的三条，**不是外加的**——下面签名的三个变量名
`hwneg`/`ha_min`/`ha_end` 同时喂给两次调用，Lean 只认一份。⟹ 合并后总数仍是 **11**，
不是 `3+11=14`；新增的八条（`hvlp`/`hwp`/`hperp`/`hdetpos`/`hnu`/`hmw`/`hmvl`/`ha`）
全部来自 det 侧，sum 侧没有任何 `hstrict_iff_sum`.独有而 det 侧没有的前提。

⚠ **`decide` 重放已补**：`bad_w_both_false` / `good_w_both_true`（下方）把上面这段手算换成
内核可验证的 `decide`，与 lane-tower-hbase 独立的 `hlev_iff_crosscheck_GZ` 互相佐证。

⛔ 仍不是洞 3 兑现：`sum`/`det` 两条判据本身都还没有从链上现成 binder 单独证出，
只是给判据侧多了一条互相佐证、互相兑现的路。 -/
theorem sum_iff_det_gen_native {ξ : Config ℤ} (d : DecompDataZ ξ)
    {mv nl vl w u' a : ℤ × ℤ}
    (hvlp : Primitive vl) (hwp : Primitive w)
    (hperp : dot nl vl = 0) (hdetpos : 0 < det nl vl)
    (hnu : dot nl u' = -1) (hwneg : dot nl w < 0)
    (hmw : dot mv w = 0) (hmvl : 0 < dot mv vl)
    (ha : a ∈ d.toDecompData.Sphi)
    (ha_min : ∀ b ∈ d.toDecompData.Sphi, dot mv a ≤ dot mv b)
    (ha_end : ∀ b ∈ d.toDecompData.Sphi, dot mv b = dot mv a →
      ∃ t : ℕ, b = a + (t : ℤ) • w) :
    (∑ j : Fin d.toDecompData.m, max 0 (dot nl (d.toDecompData.h j)) ≤ dot nl a) ↔
      (∀ j : Fin d.toDecompData.m,
        det (d.toDecompData.h j) vl * det (d.toDecompData.h j) w ≤ 0) :=
  (hstrict_iff_sum d.toDecompData hwneg ha_min ha_end).symm.trans
    (Nivat.LaneTowerHlevFanOrder.hstrict_iff_det_gen_native d hvlp hwp hperp hdetpos hnu
      hwneg hmw hmvl ha ha_min ha_end)

/-! ## 硬规矩 6 `decide` 重放

台架数据抄自 `lane-tower-hbase-sortdir.lean`（`dGZ`/`hGZ`/`nlGZ`/`vlGZ`/`wGZN`/`wGZW`/
`aGZN`/`aGZW`，标识符不认行号），只取纯 `ℤ×ℤ` 数值部分，不 import 该 `tmp/wip/` 文件
（协议 §16）。内核确认：坏 `w` 两判据同假，好 `w` 两判据同真——`sum_iff_det_gen_native`
的两边在这张台架上确实分得开，不是空真的桥接。 -/

private def hGZDecide : Fin 4 → ℤ × ℤ := ![(0, 1), (-1, 1), (-1, 0), (-1, -1)]
private def nlGZDecide : ℤ × ℤ := (1, 0)
private def vlGZDecide : ℤ × ℤ := (0, 1)
private def wGZNDecide : ℤ × ℤ := (-1, 0)
private def wGZWDecide : ℤ × ℤ := (-1, -1)
private def aGZNDecide : ℤ × ℤ := (-1, -1)
private def aGZWDecide : ℤ × ℤ := (0, 0)

/-- 坏 `w`：求和判据与 det 判据同假。 -/
theorem bad_w_both_false :
    ¬ (∑ j : Fin 4, max 0 (dot nlGZDecide (hGZDecide j)) ≤ dot nlGZDecide aGZNDecide) ∧
      ¬ (∀ j : Fin 4, det (hGZDecide j) vlGZDecide * det (hGZDecide j) wGZNDecide ≤ 0) :=
  ⟨by decide, by decide⟩

/-- 好 `w`：求和判据与 det 判据同真。 -/
theorem good_w_both_true :
    (∑ j : Fin 4, max 0 (dot nlGZDecide (hGZDecide j)) ≤ dot nlGZDecide aGZWDecide) ∧
      (∀ j : Fin 4, det (hGZDecide j) vlGZDecide * det (hGZDecide j) wGZWDecide ≤ 0) :=
  ⟨by decide, by decide⟩

end Nivat.SphiSumReduce

#print axioms Nivat.SphiSumReduce.hstrict_iff_sum
#print axioms Nivat.SphiSumReduce.sum_iff_det_gen_native
#print axioms Nivat.SphiSumReduce.bad_w_both_false
#print axioms Nivat.SphiSumReduce.good_w_both_true
