/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.TowerEHelp
import Nivat.External.Colle.ANormal
import Nivat.ColleReg.ZonoSum

/-!
# `hstrict` 的求和判据：`𝒮_φ` 上的线性极大值是生成元正部之和

lane-towerpkg，第 189 轮写就，第 192 轮经 team-lead 批准整份搬进主仓（原
`tmp/wip/lane-towerpkg-nlmax-sum.lean`，已不存在）。派工（team-lead）：把 `hstrict`
化归成一条可检查的判据，交一条结论逐字符就是 `hstrict` 的定理。消费者：
`RegionSteps.lean:2209` 的 `hstrict`（`sorry` 在 `:2214`，第 191 轮亲读；该位置随
team-lead 的编辑上下浮动，认标识符不认行号）。

⚠ **分工**：lane-hole3-nlmax 的 `NlmaxReduce.lean` 原打算抄一份 `max_at_Sphi_iff_sum`；
本文件进主仓后那份抄件多余，改成直接 `import Nivat.External.Colle.SphiSumCrit`
（team-lead 第 192 轮裁定）。import 由 team-lead 加，本 lane 不跑 `gen_all.py`。

⚠ **派工原话给的那一版裸方向对 `det` 式 RHS 为假**（签名里没有 `ha_min` / `ha_end`），
§A 是反驳与**射程界定**。⛔ 这**不是**「`det` 形判据已证伪」——带全套前提的 `det` 形另有
单向内核结果（lane-env-refute `hstrict_imp_crit`）。team-lead 第 191 轮裁定：采纳求和形、
`det` 形不再派工、也不记为已证伪。lane-leafa-gen 的 121 个 `q` × 17 构型扫描**区分不开**
求和形与 `det` 形（逐个同真同假），所以 §A 那段量词换侧的论证 ＋ 实例 A/B ＋ 「实例没钉
`ha_end`」那一段是**唯一**的证据，不得删节。

## §A 形状：为什么不是**裸方向对**的 `det` 式，也不是符号式

⚠ **射程先说清楚**（team-lead 第 191 轮订正，此前写宽过）：本节否掉的是**集成者第 186 轮
派工里那一版裸方向对 RHS**——它的签名里**没有** `ha_min` / `ha_end`。本节**不是**在说
「`det` 形判据为假」。带全套前提的 `det` 形是另一回事：lane-env-refute 本轮落地了
`hstrict_imp_crit`（`det` 形、带全套前提、单向），与本节**不冲突**。
这就是 `PROTOCOL.md §57` 的 A 类／B 类之分，记账时不得混。

派工给的 RHS 是 `… ↔ ∀ j, det (d.h j) p * det (d.h j) q ≤ 0`。**那一版为假**，原因是
量词换了侧：

- 旧判据（`ZonoWadjCrit.lean:123` `hwadj_iff_det_sep`）的左边跑 `n ∈ E ↑Sφ`，即**边法向**。
  `E` 被 `E_zonoF_eq_genPerp_set`（`TowerEHelp.lean:31`）穷举成 `{±genPerp' (h j)}`，
  所以 `dot n vl` 塌成 `det (h j) vl`。`det` 是「测法向」时才出现的，换边处是
  `dot_genPerp_eq_det`（`ZonoWadjCrit.lean:82`）。
- 本文件的左边跑 `b ∈ ↑Sφ`，即**点**。`dot q` 直接作用在点上，`genPerp` 那一步根本不发生。

两个数值实例（§4 的内核收据）把三个候选分开：`h = ((1,0),(0,1))`（`zonoF univ h` 是单位
正方形，`h_ne` / `h_dir` 都合规）。

| 实例 | `p` | `q` | `a` | 左边（`a` 极大化 `dot q`） | 派工的 `det` 式 | 符号式 `0 ≤ dot p (h j) * dot q (h j)` | 本文件的求和式 |
|---|---|---|---|---|---|---|---|
| A | `(1,1)` | `(1,0)` | `(1,1)` | **真** | **假** | 真 | **真** |
| B | `(1,0)` | `(0,1)` | `(1,0)` | **假** | 真 | 真 | **假** |

A 否掉 `det` 式的 `→`，B 否掉它的 `←`；B 同时否掉符号式（退化指标 `dot p (h j) = 0` 处
`p`-极大面是整条边，`a` 落在错的那一端）。求和式两个实例都算对，且**无退化例外**。

⚠ **两个实例都没有钉 `ha_end`**：实例里根本**没给 `w`**，`ha_end`（`a` 是极小层沿 `w` 的
端点）无从谈起。实例 A 里 `dot q` 在 `Sφ = {(0,0),(1,0),(0,1),(1,1)}` 上取 `{0,1,0,1}`，
极大值 `1` 由 `(1,0)` 与 `(1,1)` **两点**同时取到，`a = (1,1)` 落在**两点极大层**上。
⟹ 这两个实例**只**否掉不带 `ha_end` 的那一版签名。lane-leafa-gen 第 191 轮的
`endpoint_is_load_bearing`（台架 3，`|Sφ| = 7`）另证承重的恰是 `ha_end` 里的 `t : ℕ`：
全套前提下 322 560 组构型两个方向零反例，只把 `a` 从端点放松成极小层任意点，
反例立刻 39 104 个。

⟹ **本文件走求和形，理由不是「`det` 形错」**，而是求和形这一侧已经有两个可合成的 `↔`
（见 §E）。`det` 形按 team-lead 第 191 轮裁定不再派工，也不记为已证伪。

## §B 原文依据

`b3_colle2.txt:317`（本轮亲读，Lemma 2.7 的证明内部）逐字：

> `supp(φ) = {(0,0)} ∪ {h_{i₁} + ⋯ + h_{i_r} : 1 ≤ i₁ < ⋯ < i_r ≤ m, 1 ≤ r ≤ m}`

—— 即 `supp(φ)` **逐字就是**生成元 `h_1,…,h_m` 的全部子集和。本文件的求和式只是这句话的
直接推论：线性泛函在「全部子集和」上的极大值 ＝ 各项正部之和。链上的对应物是
`zonoF s h = ∑ i ∈ s, {0, h i}`（`NewtonZonotope.lean:134`），点集逐字相同。

`:298`：`𝒮_φ := conv(-supp(φ)) ∩ ℤ²`（**反射**凸支撑）。
`:319`：`|E(𝒮_φ)| = 2m`，每个 `w ∈ E(𝒮_φ)` 平行或反平行于某个 `h_i`。

⚠ **一名两物的提醒，本文件不处理**：原文 `:298` 的 `𝒮_φ` 带**负号**（`conv(-supp φ)`），
而链上 `DecompData.Sphi_eq`（`DecompData.lean:108`）给的是
`Conv Sphi = Conv (supp (∏ i, (mono (h i) - 1)))`，**没有负号**。本文件全程只对**链上**的
`d.Sphi` 陈述（`hstrict` 的 `Sφ` 也是链上的 `d.toDecompData.Sphi`），两边都不搬运，
所以不受影响；但谁要把结论读回原文，必须先解决这个负号。这是 team-lead 的字典债，
本文件只记录不动用。

## §C ⚠ 转运在**值**级合法，在 `face` 级仍然 BLOCKED

`ANormal.lean:278-282`（本轮亲读）明写这条链「never touches the pointwise structure of
`face`」，并说 `FaceData` 的 Step C 被标 **BLOCKED**，理由是
「`Conv d.Sphi = Conv (zonoF …)` is an equality of hulls, not of sets」。

**本文件不撞这条闸。** 需要的是 `max_{Sφ} dot q` 这个**数值**，不是「哪些点达到它」这个
**集合**：支撑函数只依赖凸包，所以

    (∀ b ∈ ↑d.Sphi, dot q b ≤ c) ↔ (∀ z ∈ ↑(zonoF univ d.h), dot q z ≤ c)

只用 `Sphi_eq` 的 `Conv` 相等就够（`le_iff_forall_mem_Conv` + `convexHull_min` + 半平面凸）。
⛔ **这条不解封 Step C**：极大点**集合**的转运照旧没有，`face ↑d.Sphi q` 与
`face ↑(zonoF …) q` 仍然不可互换。以后不许把本文件引成「Step C 已通」。

## §D 交付与欠账

交付：`le_Sphi_iff_sum`（一般 `q`、一般 `c`）与 `hstrict_of_sum`（结论逐字符是 `hstrict`）。

📌 **显式欠账，不含混**：`hstrict_of_sum` 的前件

    ∑ j : Fin d.m, max 0 (dot nl (d.h j)) ≤ dot nl a

**不是白送的**。它说「`nℓ` 落在 `𝒮_φ` 在 `a` 处的法锥里」。链上现成的只有
`hperp : dot nℓ vl = 0`、`hnu : dot nℓ u' = -1`、`hwneg : dot nℓ w < 0`
（`RegionSteps.lean:1842`）与 `hmw : dot m w = 0`、`hmvl : 0 < dot m vl`（`:1857`）——
它们把 `-m` 与 `nℓ` 钉在 `(vl, w)` 对偶基的两条坐标轴上，但**没有**把每个 `h_j` 钉在同一
象限。本文件把 `hstrict` 从「`Sφ` 上的量化命题」化归成一条**纯有限**不等式
（只含 `d.h` / `nl` / `a`，不含 `Rinf`、不含凸性、不含相邻性），**没有**把它证掉。

## §E 与已落主仓的另一半的接法

`NlmaxReduce.hstrict_iff_nlmax`（`Nivat/External/Colle/NlmaxReduce.lean`，lane-hole3-nlmax
第 190 轮落地，前提 `hwneg` / `ha_min` / `ha_end`）给

    hstrict ↔ (∀ b ∈ Sφ, dot nℓ b ≤ dot nℓ a)

它的右边逐字符就是本文件 `max_at_Sphi_iff_sum` 的左边（取 `q := nℓ`、`a := a`），所以

    hstrict_iff_nlmax.trans (max_at_Sphi_iff_sum d nl a)

是一条完整的 `hstrict ↔ ∑ j, max 0 (dot nℓ (d.h j)) ≤ dot nℓ a`。**两个 `↔` 都是真等价。**

⚠ **求和式不受「退化边」反例影响。** lane-tower-hlev 第 190 轮内核反例
（`Nivat/External/Colle/FanOrderCriterion.lean` 的 `sign_agree_alone_insufficient`。
⚠ **本条**故意**不写行号**：该文件本轮内已改三次行号（`:517` → `:545` → `:553`），
按 lane-tower-hlev 第 193 轮的建议，引它一律只写「文件名 ＋ 标识符名」，口径待 team-lead
裁决；硬规矩 8 禁的是光秃秃的 `:NNN`，不是「标识符必须配行号」。第 193 轮实测现值 `:553`。
反例数据：`h = ![(1,0),(0,1)]`、`p = (-1,0)`、`q = (0,-1)`、`a = (0,1)`，符号条件成立而 `a`
不极大化 `dot q`）否掉的是**符号式**，不是求和式：同一组数据代进求和式是
`∑ j max 0 (dot q (h j)) = 0` 对 `dot q a = -1`，`0 ≤ -1` **假**，与「`a` 不极大化 `dot q`」
一致。`le_Sphi_iff_sum` 是 `↔`，本来就没有退化例外（这正是 §A 表里第三列与第四列分开的原因）。
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Nivat.LaneTowerPkgNlmaxSum

open Nivat Nivat.LE2 Nivat.Colle35
open scoped Pointwise

variable {α : Type*} [AddCommMonoid α]

/-! ## §1. 值级转运：只吃 `Conv` 相等 -/

/-- 半平面 `{x | q · x ≤ c}` 是凸的。 -/
private theorem convex_halfspace_dot (q : ℤ × ℤ) (c : ℤ) :
    Convex ℝ {x : ℝ × ℝ | (q.1 : ℝ) * x.1 + (q.2 : ℝ) * x.2 ≤ (c : ℝ)} := by
  intro x hx y hy s t hs ht hst
  simp only [Set.mem_ofPred_eq] at hx hy ⊢
  have hfst : (s • x + t • y).1 = s * x.1 + t * y.1 := by
    simp [Prod.smul_fst, smul_eq_mul]
  have hsnd : (s • x + t • y).2 = s * x.2 + t * y.2 := by
    simp [Prod.smul_snd, smul_eq_mul]
  rw [hfst, hsnd]
  have hc : s * (c : ℝ) + t * (c : ℝ) = (c : ℝ) := by rw [← add_mul, hst, one_mul]
  nlinarith [mul_le_mul_of_nonneg_left hx hs, mul_le_mul_of_nonneg_left hy ht]

/-- **点侧的不等式等价于它在凸包上的实版本。**
`Conv S = convexHull ℝ (toReal '' S)`（`Defs/Complexity.lean:96`）。 -/
theorem le_iff_forall_mem_Conv (S : Finset (ℤ × ℤ)) (q : ℤ × ℤ) (c : ℤ) :
    (∀ b ∈ S, dot q b ≤ c) ↔
      ∀ x ∈ Conv S, (q.1 : ℝ) * x.1 + (q.2 : ℝ) * x.2 ≤ (c : ℝ) := by
  constructor
  · intro hall
    refine convexHull_min ?_ (convex_halfspace_dot q c)
    rintro _ ⟨b, hb, rfl⟩
    have hb' : dot q b ≤ c := hall b hb
    have hcast : (q.1 : ℝ) * (b.1 : ℝ) + (q.2 : ℝ) * (b.2 : ℝ) ≤ (c : ℝ) := by
      have hz : ((dot q b : ℤ) : ℝ) ≤ ((c : ℤ) : ℝ) := by exact_mod_cast hb'
      simpa [dot] using hz
    exact hcast
  · intro hall b hb
    have hmem : toReal b ∈ Conv S :=
      subset_convexHull ℝ _ ⟨b, hb, rfl⟩
    have := hall _ hmem
    simp only [toReal] at this
    have hcast : ((dot q b : ℤ) : ℝ) ≤ ((c : ℤ) : ℝ) := by
      simpa [dot] using this
    exact_mod_cast hcast

/-- **转运**：凸包相等的两个有限集，对每个方向的上界完全一样。 -/
theorem forall_le_of_Conv_eq {S T : Finset (ℤ × ℤ)} (hconv : Conv S = Conv T)
    (q : ℤ × ℤ) (c : ℤ) :
    (∀ b ∈ S, dot q b ≤ c) ↔ (∀ b ∈ T, dot q b ≤ c) := by
  rw [le_iff_forall_mem_Conv, le_iff_forall_mem_Conv, hconv]

/-! ## §2. zonotope 侧：极大值 ＝ 正部之和（`b3_colle2.txt:317` 的逐字推论）

点集那一步不自己归纳：`Nivat.ColleReg.exists_subset_sum_of_mem_zonoF` /
`sum_mem_zonoF`（`ColleReg/ZonoSum.lean:64` / `:18`）已经把
「`zonoF s h` 的点 ＝ 生成元的子集和」两个方向都给了，本节只做线性泛函那一层。
（本轮算过传递闭包：`ZonoSum` + `TowerEHelp` + `ANormal` 共 188 个模块，
四个禁项 `RegionSteps` / `ColleRegion` / `Case2WindowProbe` / `NfpLPreamble` 命中数 0。） -/

private theorem dot_sum {ι : Type*} (q : ℤ × ℤ) (h : ι → ℤ × ℤ) (S : Finset ι) :
    dot q (∑ i ∈ S, h i) = ∑ i ∈ S, dot q (h i) := by
  classical
  induction S using Finset.induction with
  | empty => simp [dot]
  | insert a t ha iht => rw [Finset.sum_insert ha, dot_add, iht, Finset.sum_insert ha]

/-- 上界：`zonoF s h` 的每个点的 `dot q` 都不超过各项正部之和。 -/
theorem dot_le_sum_max {ι : Type*} [DecidableEq ι] (h : ι → ℤ × ℤ) (q : ℤ × ℤ)
    (s : Finset ι) : ∀ z ∈ zonoF s h, dot q z ≤ ∑ i ∈ s, max 0 (dot q (h i)) := by
  classical
  intro z hz
  obtain ⟨S, hS, rfl⟩ := Nivat.ColleReg.exists_subset_sum_of_mem_zonoF s h hz
  rw [dot_sum]
  calc ∑ i ∈ S, dot q (h i)
      ≤ ∑ i ∈ S, max 0 (dot q (h i)) :=
        Finset.sum_le_sum (fun i _ => le_max_right _ _)
    _ ≤ ∑ i ∈ s, max 0 (dot q (h i)) :=
        Finset.sum_le_sum_of_subset_of_nonneg hS (fun i _ _ => le_max_left _ _)

/-- 达到：正部之和确实被 `zonoF s h` 的某个点取到——取「`dot q` 非负」的那些生成元之和。 -/
theorem exists_dot_eq_sum_max {ι : Type*} [DecidableEq ι] (h : ι → ℤ × ℤ) (q : ℤ × ℤ)
    (s : Finset ι) : ∃ z ∈ zonoF s h, dot q z = ∑ i ∈ s, max 0 (dot q (h i)) := by
  classical
  refine ⟨(∑ i ∈ s.filter (fun i => 0 ≤ dot q (h i)), h i),
    Nivat.ColleReg.sum_mem_zonoF s h (Finset.filter_subset _ _), ?_⟩
  rw [dot_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases hp : 0 ≤ dot q (h i)
  · rw [if_pos hp, max_eq_right hp]
  · rw [if_neg hp, max_eq_left (not_le.mp hp).le]

/-- **zonotope 侧的判据**：全体点的上界 ⟺ 正部之和的上界。 -/
theorem le_zonoF_iff_sum {ι : Type*} [DecidableEq ι] (h : ι → ℤ × ℤ) (q : ℤ × ℤ) (c : ℤ)
    (s : Finset ι) :
    (∀ z ∈ zonoF s h, dot q z ≤ c) ↔ ∑ i ∈ s, max 0 (dot q (h i)) ≤ c := by
  constructor
  · intro hall
    obtain ⟨z, hz, hzeq⟩ := exists_dot_eq_sum_max h q s
    rw [← hzeq]
    exact hall z hz
  · intro hsum z hz
    exact le_trans (dot_le_sum_max h q s z hz) hsum

/-! ## §3. 合成：链上形状 -/

/-- `Conv d.Sphi = Conv (zonoF univ d.h)`。`ANormal.lean:294-296` 的
`E_Sphi_eq_zonoF` 在**证明内部**有这一步但没有导出，这里按 `Sphi_eq`
（`DecompData.lean:108`）＋ `Conv_supp_prod_eq_Conv_zonoF`（`NewtonZonotope.lean:181`）
逐字重放，不 import 任何 lane 的 `tmp/wip`（协议 §16）。 -/
theorem Conv_Sphi_eq_zonoF {η : Config α} (d : DecompData η) :
    Conv d.Sphi = Conv (zonoF Finset.univ d.h) := by
  rw [d.Sphi_eq, Conv_supp_prod_eq_Conv_zonoF Finset.univ d.h (fun i _ => d.h_ne i)]

/-- **⭐ 主判据（一般方向 `q`、一般界 `c`）**：`𝒮_φ` 上 `dot q` 的上界，逐字等于
生成元正部之和的上界。派工要的「一般化成任意方向对」就是这一条——它**只**带一个方向 `q`，
因为点侧的极大值本来就不需要第二个方向（第二个方向是法向侧判据的产物，见 §A）。 -/
theorem le_Sphi_iff_sum {η : Config α} (d : DecompData η) (q : ℤ × ℤ) (c : ℤ) :
    (∀ b ∈ d.Sphi, dot q b ≤ c) ↔ ∑ j : Fin d.m, max 0 (dot q (d.h j)) ≤ c := by
  rw [forall_le_of_Conv_eq (Conv_Sphi_eq_zonoF d) q c]
  exact le_zonoF_iff_sum d.h q c Finset.univ

/-- **`a` 全局极大化 `dot q` 的判据**（`c := dot q a` 的实例）。 -/
theorem max_at_Sphi_iff_sum {η : Config α} (d : DecompData η) (q a : ℤ × ℤ) :
    (∀ b ∈ d.Sphi, dot q b ≤ dot q a) ↔
      ∑ j : Fin d.m, max 0 (dot q (d.h j)) ≤ dot q a :=
  le_Sphi_iff_sum d q (dot q a)

/-- **结论逐字符是 `hstrict`**（`RegionSteps.lean:2209`，第 191 轮亲读；认标识符不认行号）：

```
hstrict : ∀ b ∈ Sφ, Nivat.LE2.dot m a < Nivat.LE2.dot m b →
    Nivat.LE2.dot nℓ b ≤ Nivat.LE2.dot nℓ a
```

`mvec` 对应消费者处的 `m`（此处不能叫 `m`，`d.m` 已占名）。前件 `dot mvec a < dot mvec b`
**用不上**——求和判据给的是全局极大，比 `hstrict` 强。⟹ 这既是好事（不必再谈层），
也是欠账的所在（§D）。 -/
theorem hstrict_of_sum {η : Config α} (d : DecompData η) (mvec nl a : ℤ × ℤ)
    (hq : ∑ j : Fin d.m, max 0 (dot nl (d.h j)) ≤ dot nl a) :
    ∀ b ∈ d.Sphi, dot mvec a < dot mvec b → dot nl b ≤ dot nl a := by
  intro b hb _
  exact (max_at_Sphi_iff_sum d nl a).mpr hq b hb

/-! ## §4. 内核收据：§A 表格里的两个数值实例

`hA : Fin 2 → ℤ × ℤ` 取 `((1,0), (0,1))`，`zonoF univ hA` 是单位正方形。
下面不去展开 `zonoF`（`decide` 在 `Finset (ℤ × ℤ)` 上代价不可控），
而是**直接对求和式与两个候选式求值**，这已经足以把三个候选分开。 -/

/-- 实例 A/B 共用的生成元 `h₀ = (1,0)`、`h₁ = (0,1)`。
`h_ne` 合规（`instA_h_ne`），`h_dir` 合规（`det (hA 0) (hA 1) = 1 ≠ 0`，`instA_h_dir`）。 -/
def hA : Fin 2 → ℤ × ℤ := ![((1 : ℤ), (0 : ℤ)), ((0 : ℤ), (1 : ℤ))]

theorem instA_h_ne : ∀ j : Fin 2, hA j ≠ 0 := by
  intro j
  fin_cases j <;> simp [hA, Prod.ext_iff]

theorem instA_h_dir : det (hA 0) (hA 1) = 1 := by
  simp [hA, det]

/-- **实例 A**：`q = (1,0)`、`a = (1,1)`。求和式为**真**（`∑ = 1 ≤ 1 = dot q a`）。 -/
theorem instA_sum : ∑ j : Fin 2, max 0 (dot ((1 : ℤ), (0 : ℤ)) (hA j))
    ≤ dot ((1 : ℤ), (0 : ℤ)) ((1 : ℤ), (1 : ℤ)) := by
  norm_num [Fin.sum_univ_two, hA, dot]

/-- **实例 A**：派工的 `det` 式在 `j = 1` 处为**假**（乘积 `= 1 > 0`），
而上面的求和式为真 ⟹ 那个 `↔` 的 `→` 方向被否。 -/
theorem instA_det_fails :
    ¬ (det (hA 1) ((1 : ℤ), (1 : ℤ)) * det (hA 1) ((1 : ℤ), (0 : ℤ)) ≤ 0) := by
  norm_num [hA, det]

/-- **实例 B**：`p = (1,0)`、`q = (0,1)`、`a = (1,0)`。求和式为**假**
（`∑ = 1 > 0 = dot q a`），与左边同为假 ⟹ 求和式在退化指标上也算对。 -/
theorem instB_sum_fails :
    ¬ (∑ j : Fin 2, max 0 (dot ((0 : ℤ), (1 : ℤ)) (hA j))
        ≤ dot ((0 : ℤ), (1 : ℤ)) ((1 : ℤ), (0 : ℤ))) := by
  norm_num [Fin.sum_univ_two, hA, dot]

/-- **实例 B**：纯符号式 `∀ j, 0 ≤ dot p (hA j) * dot q (hA j)` 在这里为**真**，
而左边为假 ⟹ 符号式不是充分条件（退化指标 `dot p (hA 1) = 0` 处 `p`-极大面是整条边）。 -/
theorem instB_sign_holds : ∀ j : Fin 2,
    0 ≤ dot ((1 : ℤ), (0 : ℤ)) (hA j) * dot ((0 : ℤ), (1 : ℤ)) (hA j) := by
  intro j
  fin_cases j <;> norm_num [hA, dot]

end Nivat.LaneTowerPkgNlmaxSum

#print axioms Nivat.LaneTowerPkgNlmaxSum.le_iff_forall_mem_Conv
#print axioms Nivat.LaneTowerPkgNlmaxSum.forall_le_of_Conv_eq
#print axioms Nivat.LaneTowerPkgNlmaxSum.dot_le_sum_max
#print axioms Nivat.LaneTowerPkgNlmaxSum.exists_dot_eq_sum_max
#print axioms Nivat.LaneTowerPkgNlmaxSum.le_zonoF_iff_sum
#print axioms Nivat.LaneTowerPkgNlmaxSum.Conv_Sphi_eq_zonoF
#print axioms Nivat.LaneTowerPkgNlmaxSum.le_Sphi_iff_sum
#print axioms Nivat.LaneTowerPkgNlmaxSum.max_at_Sphi_iff_sum
#print axioms Nivat.LaneTowerPkgNlmaxSum.hstrict_of_sum
#print axioms Nivat.LaneTowerPkgNlmaxSum.instA_h_ne
#print axioms Nivat.LaneTowerPkgNlmaxSum.instA_h_dir
#print axioms Nivat.LaneTowerPkgNlmaxSum.instA_sum
#print axioms Nivat.LaneTowerPkgNlmaxSum.instA_det_fails
#print axioms Nivat.LaneTowerPkgNlmaxSum.instB_sum_fails
#print axioms Nivat.LaneTowerPkgNlmaxSum.instB_sign_holds
