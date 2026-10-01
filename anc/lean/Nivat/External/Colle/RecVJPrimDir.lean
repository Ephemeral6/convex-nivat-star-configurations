/-
# `rec_vJ` 的侧条件可以换到**本原方向** `-vl` 上——整除那一半随之免费

**为什么有这个文件。** lane-env-refute 2026-09-26 给出内核反例
`orient_not_enough_without_prim_p`（`EnvRefuteOrient.lean`）：在
`hcomb : vJ = (a:ℤ) • p + (t:ℤ) • vJ1`（`a t : ℕ`）里，若只加「定向」谓词而不加整除，
`c ≥ 2` 时 `hcomb` 仍可为假（他们的数据 `c = 2`、`α = 2`、`β = 1`，死在 `2 ∤ 1`）。
他们同时证了：**`Primitive p` 时整除由 Bezout 免费**（`hcomb_iff_ray`），
但 `p = -(c:ℤ) • vl` 只有 `c = 1` 才本原，而 `Primitive p` 全树命中 0
（集成者复核：`RegionSteps.exists_neg_multiple_of_perp`（`RegionSteps.lean:1168`）只把符号规范化、
`c := |k|` 原样传下，**不强制 `c = 1`**；`c = 1 ⟺ vl ∈ Per xper`，链上无此条）。
⟹ 整除那一半看起来是真欠账。

## ⭐ 但瓶颈在 `p`，不在命题：把方向换成 `-vl` 即可

两条已在主仓的事实凑起来就够：

**(1) `rec_of_comb`（`RecVJComb.lean:137`）里的 `p` 是自由变量**，全部用法只有一条
`hrec_p : ∀ g ∈ U, g + p ∈ U`（证明体 `:147` 的 `iter_rec hrec_p a g hg`）。
⟹ 它对**任何**具备正向递归的方向都成立，`p` 是不是那个周期无关紧要。

**(2) 帽子并集本来就对 `-vl` 封闭，而且是白给的。**
`LaneLeafAGenRecP.rec_p_free`（`LeafAGenRecP.lean:184`）给出

    ∀ g ∈ ⋃ i, hatOf A kk vl i, g + (-vl) ∈ ⋃ i, hatOf A kk vl i

且**零链外假设**——它的 binder 逐条是 `ChainKK.exists_normalised_chain`（`ChainKK.lean:92`）
输出的合取项 4/5/6/7/8/11/12/13，`hperp` 是构造器常设假设（该文件 §4 自述，集成者本轮复读签名确认）。
这也正是 `rec_p` 本身的来历：`RegionSteps.lean:1162` 记着 leaf A 的装配体是「用 `hstep`
（帽子并集对 `-vl` 封闭）**迭代 `c` 次**来证 `rec_p`」——⟹ `-vl` 封闭是**更原始**的事实，
`rec_p` 是它的推论，本文件只是不再把它迭代掉。

⟹ 把 `rec_of_comb` 的 `p` 取成 `-vl`，侧条件变成

    hcomb_negvl : vJ = (a:ℤ) • (-vl) + (t:ℤ) • vJ1        (a t : ℕ)

而 **`Primitive (-vl)` 在链上是现货**（`Primitive vl` 是 `exists_chainData` 的 binder，
env-refute 实测在 `RegionSteps` 命中 30 次）。⟹ env-refute 的 `hcomb_iff_ray` 的
`Primitive p` 前提**就地兑现**，整除由 Bezout 免费。**缺失字段回到一条：纯定向。**

## 严格更弱，不是换个说法

`comb_negvl_of_comb`：`p = -(c:ℤ) • vl` 时，旧侧条件 ⟹ 新侧条件（取 `a := a*c`）。
反向不真：旧的 `a • p = -(a c) • vl` 只扫到 `vl` 的 `c` 的倍数，新的 `a • (-vl)` 扫到全部。
⟹ `c ≥ 2` 时新条件**严格更弱**，而这正是 env-refute 反例所在的区间。
⭐ 于是那个反例**不是** `rec_vJ` 的障碍，只是「把方向记成 `p`」这个记法的障碍。

## ⛔ 射程自限（PROTOCOL §15 / §51）

1. 本文件**没有**证 `hcomb_negvl`。欠的仍是一条定向字段，只是现在**不再附带整除**。
2. `rec_vJ_free_of_comb_negvl` 的 `hhp` / `hswept` / `hperp` 三条我按 `ChainDataGeomParts`
   的字段名写成 binder（对应 `union_hhp c` / `c.hswept` / `c.F.dot_nJ_vJ`，见
   `RecVJComb.parts_rec_vJ`（`RecVJComb.lean:188`）的实参表），**但本文件不构造那个结构实例**，
   所以「这三条在链上是字段」是对位读法，不是本文件的内核内容。
3. 关于 `c = 1 ⟺ vl ∈ Per xper`、`Primitive p` 全树命中 0 这两句，前者是我读
   `exists_neg_multiple_of_perp` 证明体得到的，后者取自 env-refute 的报告，**我未复跑那个 grep**。
   两句都不承重：本文件的结论不依赖 `c` 的取值。
4. 原文 `b3_colle2.txt` 本轮未亲读；`:506` / `:1162` 两处引文转自 `RecVJComb.lean` 与
   `RegionSteps.lean` 的既有批注。
-/
import Nivat.External.Colle.RecVJComb
import Nivat.External.Colle.LeafAGenRecP

namespace Nivat.RecVJPrimDir

open Nivat Nivat.LE2 Nivat.MaxEnv Nivat.Colle35 Nivat.ChainAsm

variable {α : Type*}

/-- ⭐ **抽象形：把 `rec_of_comb` 的方向取成 `-vl`。**

`rec_of_comb`（`RecVJComb.lean:137`）的 `p` 只经 `hrec_p` 使用，故可取任何递归方向。 -/
theorem rec_vJ_of_comb_negvl {U : Set (ℤ × ℤ)} {vl vJ vJ1 nJ : ℤ × ℤ} {cJ : ℤ}
    (hhp : ∀ g ∈ U, cJ ≤ dot nJ g)
    (hswept : SweptClosed U vJ1 nJ cJ)
    (hrec : ∀ g ∈ U, g + (-vl) ∈ U)
    (hperp : dot nJ vJ = 0)
    {a t : ℕ} (hcomb : vJ = (a : ℤ) • (-vl) + (t : ℤ) • vJ1) :
    ∀ g ∈ U, g + vJ ∈ U :=
  Nivat.LaneTowerHbaseRecVJ.rec_of_comb hhp hswept hrec hperp hcomb

/-- ⭐ **新侧条件比旧的弱**：`p = -(c:ℤ) • vl` 时旧 ⟹ 新，取 `a := a * c`。

反向不真（`c ≥ 2` 时 `a • p` 只扫 `vl` 的 `c` 的倍数）⟹ 严格更弱。 -/
theorem comb_negvl_of_comb {vl p vJ vJ1 : ℤ × ℤ} {c : ℕ} (hp : p = -(c : ℤ) • vl)
    {a t : ℕ} (hcomb : vJ = (a : ℤ) • p + (t : ℤ) • vJ1) :
    vJ = ((a * c : ℕ) : ℤ) • (-vl) + (t : ℤ) • vJ1 := by
  subst hp
  rw [hcomb]
  push_cast
  ext <;> simp [Prod.smul_def] <;> ring

/-- ⭐⭐ **端到端：`rec_vJ` 的唯一链外输入是本原方向上的侧条件。**

`hrec` 那一格由 `LaneLeafAGenRecP.rec_p_free`（`LeafAGenRecP.lean:184`，零链外假设）兑现，
其 binder 逐条是 `ChainKK.exists_normalised_chain` 的输出合取项。
⟹ 与 `RecVJComb.parts_rec_vJ` 相比，`p` 上的整除障碍（env-refute 的
`orient_not_enough_without_prim_p`）**不再出现**，因为 `-vl` 本原。 -/
theorem rec_vJ_free_of_comb_negvl (η xper : Config α) (vl : ℤ × ℤ) (S : Finset (ℤ × ℤ))
    {B A : ℕ → Set (ℤ × ℤ)} {u : ℕ → ℤ × ℤ} {kk : ℕ → ℕ} {g₁ nℓ : ℤ × ℤ} {cz : ℤ}
    (hperp_vl : dot nℓ vl = 0)
    (maxA : ∀ i, IsMaxEnvIn (EnvOf (↑S : Set (ℤ × ℤ))) (canonA η xper vl B u i) (A i))
    (subBA : ∀ i, B i ⊆ A i)
    (subAB : ∀ i, A i ⊆ B (i + 1))
    (hAfin : ∀ i, (A i).Finite)
    (hII : ItemII B nℓ cz)
    (hg₁cz : dot nℓ g₁ = cz)
    (halign : ∀ i, IsGreatest
      {t : ℤ | g₁ + t • vl ∈ hatOf A kk vl i ∧ dot nℓ (g₁ + t • vl) = cz} 0)
    (AhatMono : ∀ i j, i ≤ j → hatOf A kk vl i ⊆ hatOf A kk vl j)
    {vJ vJ1 nJ : ℤ × ℤ} {cJ : ℤ}
    (hhp : ∀ g ∈ ⋃ i, hatOf A kk vl i, cJ ≤ dot nJ g)
    (hswept : SweptClosed (⋃ i, hatOf A kk vl i) vJ1 nJ cJ)
    (hperp : dot nJ vJ = 0)
    {a t : ℕ} (hcomb : vJ = (a : ℤ) • (-vl) + (t : ℤ) • vJ1) :
    ∀ g ∈ ⋃ i, hatOf A kk vl i, g + vJ ∈ ⋃ i, hatOf A kk vl i :=
  rec_vJ_of_comb_negvl hhp hswept
    (Nivat.LaneLeafAGenRecP.rec_p_free η xper vl S hperp_vl maxA subBA subAB hAfin hII
      hg₁cz halign AhatMono)
    hperp hcomb

#print axioms Nivat.RecVJPrimDir.rec_vJ_of_comb_negvl
#print axioms Nivat.RecVJPrimDir.comb_negvl_of_comb
#print axioms Nivat.RecVJPrimDir.rec_vJ_free_of_comb_negvl

/-! ## §2 ⭐⭐ 换方向后 env-refute 的**两条**整除欠账合成**一条**

lane-env-refute 2026-09-26 的 §19／§20（`EnvRefuteOrient.lean`，集成者读证明体复核）把
`hOrient` 的欠账缩成两条：

    (i)  det p c.vJ1 ∣ det p c.vJ      （外加 det p c.vJ1 ≠ 0）
    (ii) dot nJ p ∣ t * (- dot nJ vJ1)  ——`Primitive p` 时由 Bezout 免费，`c ≥ 2` 时不免费

本节证：把方向从 `p` 换成 `-vl` 之后，**(ii) 消失**（`-vl` 本原，见 §1），而 **(i) 逐字不变**
——因为 `det p x = (c:ℤ) * det (-vl) x`，两边同乘 `c` 不改变整除关系（`c > 0`）。

⟹ **洞 1 的 `rec_vJ` 一格，欠账是一条整除：`det vl c.vJ1 ∣ det vl c.vJ`。**
这就是可以拿去和原文对账的最终形状。 -/

/-- `p = -(c:ℤ) • vl` 时，`det p ·` 就是 `det (-vl) ·` 的 `c` 倍。 -/
theorem det_p_eq_smul {vl p : ℤ × ℤ} {c : ℕ} (hp : p = -(c : ℤ) • vl) (x : ℤ × ℤ) :
    det p x = (c : ℤ) * det (-vl) x := by
  subst hp
  simp only [det, Prod.smul_fst, Prod.smul_snd, Prod.fst_neg, Prod.snd_neg, smul_eq_mul]
  ring

/-- ⭐ **欠账 (i) 在换方向下逐字不变。** `c > 0` ⟹ 同乘 `c` 不改整除关系。 -/
theorem dvd_det_iff_negvl {vl p vJ vJ1 : ℤ × ℤ} {c : ℕ} (hc : 0 < c)
    (hp : p = -(c : ℤ) • vl) :
    (det p vJ1 ∣ det p vJ) ↔ (det (-vl) vJ1 ∣ det (-vl) vJ) := by
  rw [det_p_eq_smul hp, det_p_eq_smul hp]
  exact mul_dvd_mul_iff_left (by exact_mod_cast hc.ne' : (c : ℤ) ≠ 0)

/-- ⭐ **`0 < dot nJ p` 传给本原方向。** 字段给的是 `p` 上的符号；`c > 0` 把它降到 `-vl` 上，
这样 env-refute 的 §19／§20 机器（`no_lower_bound_of_swept` 要 `0 < dot nJ ·`）
可以整体改挂在 `-vl` 上跑。 -/
theorem dot_nJ_negvl_pos {nJ vl p : ℤ × ℤ} {c : ℕ} (hc : 0 < c) (hp : p = -(c : ℤ) • vl)
    (hpos : 0 < dot nJ p) : 0 < dot nJ (-vl) := by
  subst hp
  have hexp : dot nJ (-(c : ℤ) • vl) = (c : ℤ) * dot nJ (-vl) := by
    simp only [dot, Prod.smul_fst, Prod.smul_snd, Prod.fst_neg, Prod.snd_neg, smul_eq_mul]
    ring
  rw [hexp] at hpos
  have hc' : (0 : ℤ) < (c : ℤ) := by exact_mod_cast hc
  rcases lt_or_ge 0 (dot nJ (-vl)) with h | h
  · exact h
  · nlinarith

#print axioms Nivat.RecVJPrimDir.det_p_eq_smul
#print axioms Nivat.RecVJPrimDir.dvd_det_iff_negvl
#print axioms Nivat.RecVJPrimDir.dot_nJ_negvl_pos

/-! ## §3 ⭐⭐ 对 env-refute §22 的 Cramer 三条：换方向**严格削弱最难的第 3 条**

lane-env-refute 2026-09-26 §22（`EnvRefuteOrient.hcomb_iff_cramer`，是 `↔`）把 `hcomb`
精确刻画成三条（`det p vJ1 ≠ 0` 下）：

    (1) det p c.vJ1 ≠ 0                              —— 横截，显式 binder
    (2) ∃ t : ℕ, det p c.vJ  = det p c.vJ1 * t       —— 符号免费（§19 同号筛），只欠整除
    (3) ∃ a : ℕ, det c.vJ c.vJ1 = det p c.vJ1 * a    —— 整除**和**符号都无产者（最难那条）

把方向换成 `-vl`（§1 已证换得动）之后，逐条比较（`det p x = (c:ℤ) * det (-vl) x`，§2）：

    (1) 不变：`det p vJ1 ≠ 0 ⟺ det (-vl) vJ1 ≠ 0`（`c > 0`）
    (2) 不变：`dvd_det_iff_negvl`（§2）是 `↔`
    (3) ⭐ **严格变弱**：`p`-版要 `c * det (-vl) vJ1 ∣ det vJ vJ1`，
        `-vl`-版只要 `det (-vl) vJ1 ∣ det vJ vJ1` —— 少一个因子 `c`

`cramer3_negvl_of_cramer3` 把「旧 ⟹ 新」钉成内核事实（取 `a' := c * a`）；反向在 `c ≥ 2` 时不真。
⟹ **洞 1 `rec_vJ` 的欠账，最紧形状是 `-vl` 版的三条**，其中第 3 条比 env-refute 报的少一个 `c`。 -/

/-- ⭐ **Cramer 第 3 条在换方向下严格变弱。** 取 `a' := c * a`。 -/
theorem cramer3_negvl_of_cramer3 {vl p vJ vJ1 : ℤ × ℤ} {c : ℕ} (hp : p = -(c : ℤ) • vl)
    {a : ℕ} (h : det vJ vJ1 = det p vJ1 * (a : ℤ)) :
    det vJ vJ1 = det (-vl) vJ1 * ((c * a : ℕ) : ℤ) := by
  rw [h, det_p_eq_smul hp]
  push_cast
  ring

#print axioms Nivat.RecVJPrimDir.cramer3_negvl_of_cramer3

end Nivat.RecVJPrimDir
