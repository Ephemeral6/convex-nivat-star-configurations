/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.HsuppLengthBound
import Nivat.External.Colle.VertexFromEdge
import Nivat.External.Colle.TowerEHelp
import Nivat.External.Colle.NormalCycleSphi
import Nivat.External.Colle.NlmaxReduce
import Nivat.External.Colle.RegionNlDict
import Nivat.External.Colle.ZonoNormalPair

/-!
# 扇序判据：`hstrict` ⟺ 「`-m` 与 `nℓ` 之间的开扇区里没有 `E ↑d.Sphi` 的元素」

lane-tower-hlev，2026-09-24。集成者当轮派工（「⭐ 你的新靶」）：

> 对任意非零 `p q`（`det p q ≠ 0`），
> `(∀ b ∈ ↑d.Sphi, dot q b ≤ dot q a)` ↔ 「`p` 与 `q` 之间的开扇区里没有 `E ↑d.Sphi` 的元素」
> 然后在 `(p,q) := (-m, nℓ)` 上把它接到 `hstrict`。

## 消费者

`RegionSteps.lean` 的 `hstrict`（`exists_cutResidualR_of_claim46` 体内的 `have hstrict`，
`sorry` 紧跟其后；**认标识符不认行号**）：
`∀ b ∈ Sφ, dot m a < dot m b → dot nℓ b ≤ dot nℓ a`（`Sφ = d.toDecompData.Sphi`）。
本文件不 import `RegionSteps`（也不 import 它的任何下游），接口按它那几条 binder 的**逐字形状**
复述：`ha_min` / `ha_end`（`exists_cutResidualR_of_claim46` 体内 `obtain ⟨Sφ, a, hgenφ, hSφ,
ha_min, ha_end⟩`）、`hwneg`（塔包 `obtain`＝`Nivat.LaneTowerPkgMain.lane_towerpkg_package`
的输出，末位分量）、`a ∈ Sφ`（由 `hgenφ : GeneratesAt ξ Sφ a` 的第一个合取给出，
`Generating.lean:19`）。§9 另用四条原生 binder：`hvl_prim` / `hperp` / `hdetpos` / `hnu`
（均为 `exists_cutResidualR_of_claim46` 的签名 binder）。
⚠ 2026-09-24 第 193 轮**删掉了本段原有的 `RegionSteps.lean` 行号**：一轮之内
`hstrict` 从 `:2209` 漂到 `:2213`、生成包 `obtain` 从 `:1979` 漂到 `:1983`、
原生 binder 从 `:1907/:1908/:1928` 漂到 `:1911/:1912/:1932`（`PROTOCOL.md §57` B 类腐烂，
当场订正）。这些位置**每轮都会漂**，一律用标识符锚。
最后一步用主仓现成的 `Nivat.NlmaxReduce.hstrict_iff_nlmax`（`NlmaxReduce.lean:96`）。

## 九条结果（§3/§4/§6/§8/§9/§10/§11/§12/§13）

设 `p q : ℤ × ℤ`，`A i := dot p (d.h i)`，`B i := dot q (d.h i)`。

1. **充分**（`nlmax_of_sign_agree`）：`∀ i, 0 ≤ A i * B i` ＋ `a` 在 `Sφ` 上极大化 `dot p`
   ＋ 极大层逐字是 `a + ℕ•w` ＋ `dot q w ≤ 0` ⟹ `a` 在 `Sφ` 上极大化 `dot q`。
2. **必要**（`sign_agree_of_nlmax`）：`a` 同时极大化 `dot p` 与 `dot q` ⟹ `∀ i, 0 ≤ A i * B i`。
3. **扇序翻译**（`sector_empty_iff_sign_agree`）：`∀ i, 0 ≤ A i * B i` ⟺
   `∀ y ∈ E ↑d.Sphi, ¬ InOpenSector σ p q y`。
4. **§8（当轮新增）：塌回 `hwadj`**。在 lane-tower-hbase 的两条方向字典
   （`hpar`/`hpos` = 他的 `negm_pos_mul_dir_w` 结论对，`hnl : nl = -dir vl`）下，
   `(p,q) := (-m, nℓ)` 的扇序条件**逐字**就是 `hwadj` 的 body
   `∀ n ∈ E ↑d.Sphi, ¬(dot n vl < 0 ∧ dot n w < 0)`（`Hole3Room.lean:324` 的形参），
   于是 `hstrict ⟺ hwadj`（`hstrict_iff_wadj`），再展成
   `∀ j, det (d.h j) vl * det (d.h j) w ≤ 0`（`wadj_iff_det_gen` / `hstrict_iff_det_gen`）。
   ⚠ 两条方向字典是形参，不是我证的；见 §8 抬头。
5. **§9（当轮新增）：`hnl` 的链上兑现 ＋ 符号对账**。`hnl` 由主仓
   `Nivat.RegionNlDict.nl_eq_neg_dir_vl_and_det_u'` 从四条原生 binder 免费给出
   （`hstrict_iff_wadj_chain` / `hstrict_iff_det_gen_chain`）；另把「`(-m, nℓ)` 要不要取反」
   这场争议内核结清：**不用取反**，四条读法逐字同真（`fo_sign_pair_swap` /
   `fo_sign_pair_comm_le` / `fo_sign_pair_both_neg`）。
6. **§10（当轮新增）：全原生**。`hpar` 由 `hmw` 一行给出（`fo_det_negm_dir_w_zero`），
   `hpos` 由 lane-towerpkg 的 `LaneTowerPkgNormalPair.negm_pos_dot_dir_w_of_chain`
   （主仓 `ZonoNormalPair.lean`）从链上原生 binder 给出 ⟹
   `hstrict_iff_wadj_native` / `hstrict_iff_det_gen_native` 的**前提表里再没有任何外部生产者**。
7. **§11（当轮新增）：消费者现场形态**。`hstrict_of_det_gen_onsite` /
   `hstrict_of_wadj_onsite` 的前提逐条是 `RegionSteps.lean` 的塔包 `obtain` 与生成包 `obtain`
   的分量 ＋ 原生 binder，结论与那条 `have hstrict` 的目标**逐字符同形**。
   ⚠ `hstrict_iff_det_gen_native` 已由集成者接到该消费点（第 193 轮），行号随 build 漂移，
   引用请用标识符 `hstrict`／`hstrict_iff_det_gen_native`，不要挂行号。
8. **§12（当轮新增）：扇序相邻形态**。`hwadj` ⟺「`dir w` 与 `nℓ` 之间的开弧里没有
   `E ↑d.Sphi` 的点」（`wadj_iff_no_E_between`），于是判据本身可由「相邻」一步产出
   （`hcrit_of_no_E_between_native`，结论逐字符是消费点那条 `sorry` 的目标），
   消费者现场形态是 `hstrict_of_no_E_between_onsite`。
   ⛔ 配对是 `(dir w, nℓ)`，**不是** `(-(dir w), nℓ)`——后者被
   `fo_adjacency_tracks_crit` 第 5 项内核否掉；详见 §12 抬头的符号订正。
9. **§13（当轮新增）：判据的 `dot` 形态**。`det` 形 ⟺ `∀ j, dot m (h j) * dot nℓ (h j) ≤ 0`
   （`hcrit_iff_dot_form`），消费者现场形态是 `hstrict_of_dot_form_onsite`。
   纯导出：前提表与 `hstrict_iff_det_gen_native` 逐字相同，无新 binder，不碰 `hcrit` 本身。
   ⛔ 两边**都在链侧**，都不许被读成「原文那条判据」；定向口径见 §13 抬头。

⚠ **(4)(5)(6)(7)(8)(9) 不等于洞 3 已兑现**。lane-tower-hbase 本轮把 `gZL` 台架抬成了真的 `DecompDataZ`：
**同一个 `d` / `Sφ` / `vl` / `nℓ` / `u'`，只换 `w`**，就把 `hstrict` 从假翻成真
（他的 `hstrict_GZ_N_fails` / `hstrict_GZ_W_holds`）。
⚠ 口径按他 2026-09-24 的订正（`only_w_is_free_N_vs_W`）：`m` 与 `a` **不是**另外两个自由参数，
而是随 `w` 被唯一确定——`-m = dir w` 逐字，`a` 由 `ha_min ∧ ha_end ∧ w ≠ 0` 唯一
（主仓 `Nivat.ANormalPin.a_unique_of_min_and_end`）。⟹ 翻转 `hstrict` 真假的**自由度只有一个**，
结论因此更强：`hstrict` 不可能从几何 binder 单独推出。
本文件给的是**等价变形**，剩下的那一格是「区域侧逼出好 `w`」，不在本文件里。

⚠ **(1) 的第三、四条前提不是装饰**。只有 `∀ i, 0 ≤ A i * B i`（开扇区为空）时，
`a` 未必极大化 `dot q`：若某个 `A i₀ = 0`（即 `p` 自己就平行于一条棱法向，`p ⊥ h i₀`）
而 `B i₀ ≠ 0`，则 `dot p` 的极大面是一条线段，`a` 落在它的**哪一端**由 `E` 决定不了。
单位正方形就是见证（§7，内核，`sign_agree_alone_insufficient`）：`h = ![(1,0),(0,1)]`、
`p = (-1,0)`、`q = (0,-1)`，`dot p` 的极大面是线段 `{(0,0),(0,1)}`，两端给出相反答案。
补上这一条的正是消费者手里的 `ha_end`＋`hwneg`（`a` 是极小层的 `w`-起点，而 `dot nℓ w < 0`
使这一端恰好是 `dot nℓ` 大的那端）——**所以这条判据在链上是紧的，在抽象签名上不是**。
证明里这一步是 `hend` 那一次调用，没有别的用处。

## 与 lane-towerpkg 的 `det` 形式的对接（⚠ 本节 2026-09-24 当轮订正过一次）

🔴 **原先写在这里的话是错的，已删除并订正**（`PROTOCOL.md §57`：B 类引用腐烂当场订正）。
原文如下、现作废：「`dot p (h i) * dot q (h i)` 与 `det (h i) p * det (h i) q` 只差一个正因子和
一次 `det_skew` 的双重变号 ⟹ 两个符号条件逐字等价」。**假**——`fo_genPerp'_scale` 给的是
`dot p v = g * det p (genPerp' v)`，右槽里躺的是 `h i` 的**垂线** `genPerp' (h i)`，
不是 `h i` 自己；把它读成 `det (h i) p` 中间丢了一次 `dir`。lane-towerpkg 用
`h = ((1,0),(0,1))`、`p = (1,1)`、`q = (1,0)`、`a = (1,1)` 给了数值反例（`j = 1` 处
`(-1)·(-1) = 1 > 0`），我在 `det_form_needs_dir`（§8）里把它内核化了。

**正确的 `det` 形式见 §8 的 `wadj_iff_det_gen`**：槽位里必须放泛函在 `dir` 下的**原像**
`w` / `vl`，不是泛函 `-m` / `nl` 自己，结论是 `∀ j, det (d.h j) vl * det (d.h j) w ≤ 0`。

## ⛔ 本文件**不**提供

- `hstrict` 本身。本文件把它**等价变形**成一条关于 `E ↑d.Sphi` 的条件，
  没有证明那条件成立。`exists_cutResidualR_of_claim46`（`RegionSteps.lean` 该声明上方的注释块）记着三条内核反例说明
  「`a` 同时极大化 `dot nℓ`」在抽象签名下为假；本文件与那三条不冲突——
  它给的是**等价刻画**，不是存在性。
- 任何 `Arc` / 环序 / 相邻性的复活：`InOpenSector` 只是 `NormalCycle.hnoArc`
  （`NormalCycle.lean:176`）的**同形谓词**（`0 < σ * det _ y ∧ 0 < σ * det y _`），
  这里没有环、没有指标、没有后继，两个端点 `p q` 是外部给定的任意向量。
  ⚠ §12 用「相邻」一词指的**只是**「开弧里没有 `E` 的点」这条 `∀`，两个端点
  `dir w` / `nℓ` 仍是外部给定的向量，**不含** `dir w ∈ E`、`nℓ ∈ E` 的 membership，
  也没有引入环序结构——它不是 `Arc` 的复活，也不依赖 `Arc` 的任何声明。
  ⚠ 口径订正：§8 确实证出 `hstrict ⟺ hwadj` 的 body，但**那不是「`hwadj` 复活」**——
  `hwadj` 从来没被判为假，被判掉的是「`hwadj` ⟺ `vl` 与 `w` 扇相邻」那个读法
  （`Hole3Room.lean:109`，内核反证）。§8 不碰相邻性，只做代数重写。
- `m = d.m` / `|E ↑d.Sphi| = 2 d.m` 的消费。⚠ 直说：本文件**没有**用到
  `NormalCycleSphi.exists_ncy_E_Sphi` 或 `tmp/wip/lane-tower-hlev-cardm.lean` 的
  `ncy_E_Sphi_dm`／`E_Sphi_toFinset_card`。它只用了 `NormalCycleSphi` 里那条
  `ang_mem_E_Sphi_genPerp_iff`（`E ↑d.Sphi = {±genPerp' (d.h j)}` 的 `iff`，
  本身是 `E_Sphi_eq_zonoF` ＋ `E_zonoF_eq_genPerp_set` 的两行组合）。
  判据用的是 `E` 的**穷举**，不是它的**基数**，更不是环序。

## `InOpenSector` 的原文对应

**无**。它不是转写：`b3_colle2.txt` 没有「扇区」这个对象。它是判据侧的辅助谓词，
用来把消费者已有的目标 `hstrict` 改写成关于 `E ↑d.Sphi` 的等价条件；
形状照抄 `NormalCycle.hnoArc`（`NormalCycle.lean:176`）以便两边读者对得上。
它不作为任何链上声明的**前提**出现——链上只出现 `hstrict` 本身（`RegionSteps.lean` 的 `have hstrict`）。

## import 表（与 `grep -n "^import"` 一致，共 7 条）

`HsuppLengthBound`（`zonoF_sub_Sphi`，`:77`）、`VertexFromEdge`（`mem_zonoF_iff` `:421`、
`dot_finset_sum` `:410`）、`TowerEHelp`（`E_zonoF_eq_genPerp_set` `:31`，经 `NormalCycleSphi`
间接也有）、`NormalCycleSphi`（`ang_mem_E_Sphi_genPerp_iff`）、`NlmaxReduce`
（`hstrict_iff_nlmax` `:93`）、`RegionNlDict`（`nl_eq_neg_dir_vl_and_det_u'` `:87`，§9 用；
该模块自身只 import `LatticeEdges`）、`ZonoNormalPair`（`negm_pos_dot_dir_w_of_chain`，§10 用）。四条禁 import（`RegionSteps` / `ColleRegion` /
`Case2WindowProbe` / `NfpLPreamble`）在传递闭包里命中 0 次（当轮实测）。
-/

namespace Nivat.LaneTowerHlevFanOrder

open Nivat Nivat.LE2 Nivat.Colle35

/-! ## §0. 小工具（本文件专用，一律带 `fo_` 前缀以免撞名） -/

theorem fo_dot_neg_left (n z : ℤ × ℤ) : dot (-n) z = - dot n z := by
  show (-n.1) * z.1 + (-n.2) * z.2 = -(n.1 * z.1 + n.2 * z.2)
  ring

theorem fo_dot_add_left (p q z : ℤ × ℤ) : dot (p + q) z = dot p z + dot q z := by
  show (p.1 + q.1) * z.1 + (p.2 + q.2) * z.2 = (p.1 * z.1 + p.2 * z.2) + (q.1 * z.1 + q.2 * z.2)
  ring

theorem fo_det_neg_right (p y : ℤ × ℤ) : det p (-y) = - det p y := by
  show p.1 * (-y.2) - p.2 * (-y.1) = -(p.1 * y.2 - p.2 * y.1)
  ring

theorem fo_det_neg_left (y q : ℤ × ℤ) : det (-y) q = - det y q := by
  show (-y.1) * q.2 - (-y.2) * q.1 = -(y.1 * q.2 - y.2 * q.1)
  ring

theorem fo_det_zsmul_right (p x : ℤ × ℤ) (g : ℤ) : det p (g • x) = g * det p x := by
  show p.1 * (g * x.2) - p.2 * (g * x.1) = g * (p.1 * x.2 - p.2 * x.1)
  ring

/-- 符号三分：乘积为负 ⟹ 两个因子严格异号。 -/
theorem fo_sign_cases {A B : ℤ} (h : A * B < 0) : (0 < A ∧ B < 0) ∨ (A < 0 ∧ 0 < B) := by
  rcases lt_trichotomy A 0 with hA | hA | hA
  · refine Or.inr ⟨hA, ?_⟩; nlinarith
  · exfalso; rw [hA] at h; simp at h
  · refine Or.inl ⟨hA, ?_⟩; nlinarith

theorem fo_max_add_le (A B : ℤ) : max 0 (A + B) ≤ max 0 A + max 0 B := by
  rw [max_def, max_def, max_def]; split_ifs <;> omega

/-! ## §1. 带状支撑函数：`dot n` 在格拉链 `zonoF univ h` 上的最大值

`zonoF univ h = ∑ i, {0, h i}`（`NewtonZonotope.lean:134`），所以 `dot n` 的最大值就是
逐生成元取正部之和。这一节纯算术，不涉及 `Sphi`。 -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `dot n` 在 `zonoF univ h` 上的最大值 `∑ i, max 0 (dot n (h i))`。 -/
def suppZ (h : ι → ℤ × ℤ) (n : ℤ × ℤ) : ℤ := ∑ i, max 0 (dot n (h i))

/-- 按谓词 `P` 挑生成元得到的格拉链元素。 -/
def zSel (h : ι → ℤ × ℤ) (P : ι → Prop) [DecidablePred P] : ℤ × ℤ :=
  ∑ i, if P i then h i else 0

theorem zSel_mem (h : ι → ℤ × ℤ) (P : ι → Prop) [DecidablePred P] :
    zSel h P ∈ zonoF (Finset.univ : Finset ι) h :=
  (Nivat.VertexFromEdge.mem_zonoF_iff h _).mpr
    ⟨fun i => if P i then h i else 0, fun i => by by_cases hp : P i <;> simp [hp], rfl⟩

omit [DecidableEq ι] in
theorem dot_zSel (h : ι → ℤ × ℤ) (P : ι → Prop) [DecidablePred P] (n : ℤ × ℤ) :
    dot n (zSel h P) = ∑ i, if P i then dot n (h i) else 0 := by
  rw [zSel, Nivat.VertexFromEdge.dot_finset_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hp : P i
  · rw [if_pos hp, if_pos hp]
  · rw [if_neg hp, if_neg hp, dot_zero_right]

omit [DecidableEq ι] in
/-- `zSel h P` 达到支撑值，只要 `P` 收下了所有 `dot n` 为正的生成元、且收下的都非负。 -/
theorem dot_zSel_eq_suppZ (h : ι → ℤ × ℤ) (n : ℤ × ℤ) (P : ι → Prop) [DecidablePred P]
    (h1 : ∀ i, 0 < dot n (h i) → P i) (h2 : ∀ i, P i → 0 ≤ dot n (h i)) :
    dot n (zSel h P) = suppZ h n := by
  rw [dot_zSel, suppZ]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hp : P i
  · rw [if_pos hp, max_eq_right (h2 i hp)]
  · rw [if_neg hp]
    have hle : dot n (h i) ≤ 0 := by
      by_contra hc
      exact hp (h1 i (by omega))
    rw [max_eq_left hle]

theorem dot_le_suppZ (h : ι → ℤ × ℤ) (n : ℤ × ℤ) {z : ℤ × ℤ}
    (hz : z ∈ zonoF (Finset.univ : Finset ι) h) : dot n z ≤ suppZ h n := by
  obtain ⟨g, hg, rfl⟩ := (Nivat.VertexFromEdge.mem_zonoF_iff h z).mp hz
  rw [Nivat.VertexFromEdge.dot_finset_sum, suppZ]
  refine Finset.sum_le_sum fun i _ => ?_
  rcases hg i with h0 | h0 <;> rw [h0]
  · rw [dot_zero_right]; exact le_max_left 0 _
  · exact le_max_right 0 _

/-! ## §2. `Sphi` ↔ `zonoF` 的半平面桥

`Conv d.Sphi = Conv (zonoF univ d.h)`（`Sphi_eq` ＋ `Conv_supp_prod_eq_Conv_zonoF`），
所以一条线性泛函的上界在两个集合上**互相转移**。这正是 `HsuppLengthBound.lean:90`
`mem_face_Sphi_of_mem_face_zonoF` 用的那两条引理，这里只把它做成双向的界转移。 -/

variable {α : Type*} [AddCommMonoid α] {η : Config α}

theorem fo_conv_Sphi_eq (d : DecompData η) :
    Conv d.Sphi = Conv (zonoF Finset.univ d.h) := by
  rw [d.Sphi_eq, Conv_supp_prod_eq_Conv_zonoF Finset.univ d.h (fun i _ => d.h_ne i)]

theorem bound_Z_of_Sphi (d : DecompData η) {n : ℤ × ℤ} {c : ℤ}
    (hS : ∀ b ∈ d.Sphi, dot n b ≤ c) : ∀ b ∈ zonoF Finset.univ d.h, dot n b ≤ c := by
  intro b hb
  have hhalf := Conv_subset_halfSpace hS
  have hmem : toReal b ∈ Conv d.Sphi := by
    rw [fo_conv_Sphi_eq d]; exact subset_Conv hb
  have hcast := hhalf (toReal b) hmem
  rw [rdot_toReal] at hcast
  exact_mod_cast hcast

theorem bound_Sphi_of_Z (d : DecompData η) {n : ℤ × ℤ} {c : ℤ}
    (hZ : ∀ b ∈ zonoF Finset.univ d.h, dot n b ≤ c) : ∀ b ∈ d.Sphi, dot n b ≤ c := by
  intro b hb
  have hhalf := Conv_subset_halfSpace hZ
  have hmem : toReal b ∈ Conv (zonoF Finset.univ d.h) := by
    rw [← fo_conv_Sphi_eq d]; exact subset_Conv hb
  have hcast := hhalf (toReal b) hmem
  rw [rdot_toReal] at hcast
  exact_mod_cast hcast

/-- `dot n` 在 `d.Sphi` 上不超过支撑值。 -/
theorem dot_le_suppZ_Sphi (d : DecompData η) (n : ℤ × ℤ) :
    ∀ b ∈ d.Sphi, dot n b ≤ suppZ d.h n :=
  bound_Sphi_of_Z d (fun _ hb => dot_le_suppZ d.h n hb)

/-- `a` 在 `Sphi` 上极大化 `dot p` ⟹ `dot p a` **就是**支撑值。
`≤` 由 `a ∈ Sphi` 给出，`≥` 由正则极大者 `zSel` 落在 `zonoF` 里（再经界转移）给出——
这一半**不**需要 `zonoF ⊆ Sphi`。 -/
theorem dot_eq_suppZ_of_max (d : DecompData η) {p a : ℤ × ℤ} (ha : a ∈ d.Sphi)
    (hamax : ∀ b ∈ d.Sphi, dot p b ≤ dot p a) : dot p a = suppZ d.h p := by
  classical
  refine le_antisymm (dot_le_suppZ_Sphi d p a ha) ?_
  have hsel : dot p (zSel d.h (fun i => 0 < dot p (d.h i))) = suppZ d.h p :=
    dot_zSel_eq_suppZ d.h p _ (fun _ hi => hi) (fun _ hi => le_of_lt hi)
  have := bound_Z_of_Sphi d hamax _ (zSel_mem d.h (fun i => 0 < dot p (d.h i)))
  omega

/-! ## §3. 充分方向 -/

/-- **充分**：符号一致（＝开扇区为空，见 §5）加上极大层的端点信息，
就把「`a` 极大化 `dot p`」升级成「`a` 极大化 `dot q`」。

证明的全部内容是一个**共同极大者**
`x := zSel h (fun i => 0 < B i ∨ (B i = 0 ∧ 0 < A i))`：
符号一致使它同时达到 `suppZ h p` 与 `suppZ h q`；前者说明它与 `a` 同层；
`hend` 于是给出 `x = a + t•w`（`t : ℕ`），`hqw` 把 `dot q x ≤ dot q a` 读出来。
`t : ℕ` 的非负性承重（与 `NlmaxReduce.nlmax_on_min_level` 同一处承重）。

⚠ `x ∈ d.Sphi` 用的是 `HsuppLengthBound.zonoF_sub_Sphi`（`:77`），需要
`DecompDataZ`（它的 `Sphi_conv` 字段），所以这一条比 §4 多要一个 `ℤ` 系数。 -/
theorem nlmax_of_sign_agree {ξ : Config ℤ} (d : DecompDataZ ξ) {p q w a : ℤ × ℤ}
    (hsign : ∀ i, 0 ≤ dot p (d.toDecompData.h i) * dot q (d.toDecompData.h i))
    (ha : a ∈ d.toDecompData.Sphi)
    (hamax : ∀ b ∈ d.toDecompData.Sphi, dot p b ≤ dot p a)
    (hend : ∀ b ∈ d.toDecompData.Sphi, dot p b = dot p a → ∃ t : ℕ, b = a + (t : ℤ) • w)
    (hqw : dot q w ≤ 0) :
    ∀ b ∈ d.toDecompData.Sphi, dot q b ≤ dot q a := by
  classical
  have hpa : dot p a = suppZ d.toDecompData.h p := dot_eq_suppZ_of_max d.toDecompData ha hamax
  set P : Fin d.toDecompData.m → Prop :=
    fun i => 0 < dot q (d.toDecompData.h i) ∨
      (dot q (d.toDecompData.h i) = 0 ∧ 0 < dot p (d.toDecompData.h i)) with hP
  have hq' : dot q (zSel d.toDecompData.h P) = suppZ d.toDecompData.h q := by
    refine dot_zSel_eq_suppZ d.toDecompData.h q P (fun i hi => Or.inl hi) (fun i hi => ?_)
    rcases hi with hi | hi
    · exact le_of_lt hi
    · exact le_of_eq hi.1.symm
  have hp' : dot p (zSel d.toDecompData.h P) = suppZ d.toDecompData.h p := by
    refine dot_zSel_eq_suppZ d.toDecompData.h p P (fun i hi => ?_) (fun i hi => ?_)
    · have hs := hsign i
      rcases lt_trichotomy (dot q (d.toDecompData.h i)) 0 with hq0 | hq0 | hq0
      · exfalso; nlinarith
      · exact Or.inr ⟨hq0, hi⟩
      · exact Or.inl hq0
    · rcases hi with hi | hi
      · have hs := hsign i
        nlinarith
      · exact le_of_lt hi.2
  have hmemS : zSel d.toDecompData.h P ∈ d.toDecompData.Sphi :=
    Nivat.HsuppLengthBound.zonoF_sub_Sphi d (zSel_mem d.toDecompData.h P)
  have hlev : dot p (zSel d.toDecompData.h P) = dot p a := by rw [hp', hpa]
  obtain ⟨t, ht⟩ := hend _ hmemS hlev
  have hqx : dot q (zSel d.toDecompData.h P) ≤ dot q a := by
    rw [ht, dot_add, dot_zsmul_right']
    have ht0 : (0 : ℤ) ≤ (t : ℤ) := Int.natCast_nonneg t
    nlinarith
  intro b hb
  have h1 : dot q b ≤ suppZ d.toDecompData.h q := dot_le_suppZ_Sphi d.toDecompData q b hb
  omega

/-! ## §4. 必要方向 -/

/-- **必要**：`a` 同时极大化 `dot p` 与 `dot q` ⟹ 每个生成元上两者符号一致。

用的是支撑函数的次可加性：`suppZ (p+q) ≤ suppZ p + suppZ q`，且在某个生成元上严格异号时
**严格**小于；而 `dot (p+q) a = suppZ p + suppZ q ≤ suppZ (p+q)`，矛盾。
这一半只要 `DecompData`（不需要 `zonoF ⊆ Sphi`）。 -/
theorem sign_agree_of_nlmax (d : DecompData η) {p q a : ℤ × ℤ} (ha : a ∈ d.Sphi)
    (hpmax : ∀ b ∈ d.Sphi, dot p b ≤ dot p a)
    (hqmax : ∀ b ∈ d.Sphi, dot q b ≤ dot q a) :
    ∀ i, 0 ≤ dot p (d.h i) * dot q (d.h i) := by
  classical
  intro i₀
  by_contra hc
  rw [not_le] at hc
  have hpa : dot p a = suppZ d.h p := dot_eq_suppZ_of_max d ha hpmax
  have hqa : dot q a = suppZ d.h q := dot_eq_suppZ_of_max d ha hqmax
  have hsum : dot (p + q) a ≤ suppZ d.h (p + q) := dot_le_suppZ_Sphi d (p + q) a ha
  rw [fo_dot_add_left, hpa, hqa] at hsum
  have hlt : suppZ d.h (p + q) < suppZ d.h p + suppZ d.h q := by
    have hrw : suppZ d.h p + suppZ d.h q =
        ∑ i, (max 0 (dot p (d.h i)) + max 0 (dot q (d.h i))) := by
      rw [suppZ, suppZ, ← Finset.sum_add_distrib]
    rw [suppZ, hrw]
    refine Finset.sum_lt_sum (fun i _ => ?_) ⟨i₀, Finset.mem_univ i₀, ?_⟩
    · rw [fo_dot_add_left]; exact fo_max_add_le _ _
    · rw [fo_dot_add_left]
      rcases fo_sign_cases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
        · rw [max_def, max_def, max_def]; split_ifs <;> omega
  omega

/-! ## §5. 扇序翻译：从 `E ↑d.Sphi` 到逐生成元的符号条件 -/

/-- `det p (genPerp v) = dot p v`：`genPerp = dir`（`ZonoEdgeGen.lean:43`，
`dir n = (-n.2, n.1)`，`LatticeEdges.lean:248`），逆时针转 90° 把 `det` 变成 `dot`。 -/
theorem fo_det_genPerp (p v : ℤ × ℤ) : det p (genPerp v) = dot p v := by
  show p.1 * v.1 - p.2 * (-v.2) = p.1 * v.1 + p.2 * v.2
  ring

/-- 一个**对所有 `p` 共用**的正因子 `g`（`v` 的垂线的 gcd），把 `dot p v` 与
`det p (genPerp' v)` 联系起来。共用是承重的：两个不同的 `p` 必须拿到同一个 `g`，
否则下面的符号比较不成立。 -/
theorem fo_genPerp'_scale {v : ℤ × ℤ} (hv : v ≠ 0) :
    ∃ g : ℤ, 0 < g ∧ ∀ p : ℤ × ℤ, dot p v = g * det p (genPerp' v) := by
  obtain ⟨-, g, hg, heq⟩ := primPart_spec (genPerp_ne_zero hv)
  refine ⟨g, hg, fun p => ?_⟩
  rw [← fo_det_genPerp p v]
  conv_lhs => rw [heq]
  rw [fo_det_zsmul_right]
  rfl

theorem fo_det_mul_nonneg_of_dot {p q v : ℤ × ℤ} (hv : v ≠ 0)
    (h : 0 ≤ dot p v * dot q v) : 0 ≤ det p (genPerp' v) * det q (genPerp' v) := by
  obtain ⟨g, hg, hall⟩ := fo_genPerp'_scale hv
  rw [hall p, hall q] at h
  nlinarith [h, mul_pos hg hg]

theorem fo_det_mul_neg_of_dot {p q v : ℤ × ℤ} (hv : v ≠ 0)
    (h : dot p v * dot q v < 0) : det p (genPerp' v) * det q (genPerp' v) < 0 := by
  obtain ⟨g, hg, hall⟩ := fo_genPerp'_scale hv
  rw [hall p, hall q] at h
  nlinarith [h, mul_pos hg hg]

/-- **`y` 落在 `p` 与 `q` 张成的开扇区里**（定向 `σ ∈ {1,-1}`）。

⚠ 无原文对应物，不是转写；形状照抄 `NormalCycle.hnoArc`（`NormalCycle.lean:176`）的
`0 < σ * det (nu k) y ∧ 0 < σ * det y (nu (k+1))`，把那里的一对相邻法向换成外部给定的
`p q`。这里**没有**环、没有指标、没有后继。 -/
def InOpenSector (σ : ℤ) (p q y : ℤ × ℤ) : Prop :=
  0 < σ * det p y ∧ 0 < σ * det y q

theorem not_inOpenSector_of_mul_nonneg {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) {p q y : ℤ × ℤ}
    (h : 0 ≤ det p y * det q y) : ¬ InOpenSector σ p q y := by
  rintro ⟨h1, h2⟩
  rw [det_skew y q] at h2
  rcases hσ with rfl | rfl <;> nlinarith

/-- 乘积为负 ⟹ `y` 或 `-y` 落在开扇区里。`E` 对取负封闭，所以下面只要两者之一。 -/
theorem inOpenSector_of_mul_neg {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) {p q y : ℤ × ℤ}
    (h : det p y * det q y < 0) :
    InOpenSector σ p q y ∨ InOpenSector σ p q (-y) := by
  have hsk : det y q = - det q y := det_skew y q
  simp only [InOpenSector, fo_det_neg_right, fo_det_neg_left, hsk]
  rcases hσ with rfl | rfl <;> rcases fo_sign_cases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    first
      | exact Or.inl ⟨by omega, by omega⟩
      | exact Or.inr ⟨by omega, by omega⟩

/-- `E ↑d.Sphi` 的穷举（`NormalCycleSphi.ang_mem_E_Sphi_genPerp_iff`，
本身 = `E_Sphi_eq_zonoF` ＋ `E_zonoF_eq_genPerp_set`）。 -/
theorem fo_mem_E_Sphi_iff (d : DecompData η) (ν : ℤ × ℤ) :
    ν ∈ E (↑d.Sphi : Set (ℤ × ℤ)) ↔
      ∃ j : Fin d.m, ν = genPerp' (d.h j) ∨ ν = -genPerp' (d.h j) :=
  Nivat.NormalCycleSphi.ang_mem_E_Sphi_genPerp_iff d ν

/-- **扇序翻译**：开扇区为空 ⟺ 逐生成元符号一致。

⚠ 右边与 `σ` 无关，左边表面上依赖 `σ`——这不是漏写前提：`E ↑d.Sphi` 对取负封闭
（`Sphi_negSymm`，这里经穷举直接可见），所以 `σ = 1` 与 `σ = -1` 的两个开扇区
（互为相反区）含的 `E` 元素个数同时为零。因此本引理**不需要** `det p q ≠ 0`，
也不需要 `σ` 与 `det p q` 的符号挂钩；消费者若要几何读法，取 `σ = sign (det p q)` 即可。 -/
theorem sector_empty_iff_sign_agree (d : DecompData η) {σ : ℤ} (hσ : σ = 1 ∨ σ = -1)
    (p q : ℤ × ℤ) :
    (∀ y ∈ E (↑d.Sphi : Set (ℤ × ℤ)), ¬ InOpenSector σ p q y) ↔
      ∀ i, 0 ≤ dot p (d.h i) * dot q (d.h i) := by
  constructor
  · intro hE i
    by_contra hc
    rw [not_le] at hc
    rcases inOpenSector_of_mul_neg hσ (fo_det_mul_neg_of_dot (d.h_ne i) hc) with hin | hin
    · exact hE _ ((fo_mem_E_Sphi_iff d _).mpr ⟨i, Or.inl rfl⟩) hin
    · exact hE _ ((fo_mem_E_Sphi_iff d _).mpr ⟨i, Or.inr rfl⟩) hin
  · intro hsign y hy
    obtain ⟨j, rfl | rfl⟩ := (fo_mem_E_Sphi_iff d y).mp hy
    · exact not_inOpenSector_of_mul_nonneg hσ (fo_det_mul_nonneg_of_dot (d.h_ne j) (hsign j))
    · refine not_inOpenSector_of_mul_nonneg hσ ?_
      have hbase := fo_det_mul_nonneg_of_dot (d.h_ne j) (hsign j)
      rw [fo_det_neg_right, fo_det_neg_right]
      nlinarith

/-! ## §6. 接到 `RegionSteps.lean` 的 `hstrict` -/

/-- **全局极大版**：开扇区（`p := -m`，`q := nℓ`）为空 ⟹ `a` 在 `𝒮_φ` 上极大化 `dot nℓ`。

前提逐字对应消费者：`ha`（`hgenφ.1`）、`ha_min` / `ha_end`（生成包 `obtain`）、`hwneg`（塔包 `obtain`）。 -/
theorem nlmax_of_sector_empty {ξ : Config ℤ} (d : DecompDataZ ξ) {σ : ℤ}
    (hσ : σ = 1 ∨ σ = -1) {mv nl w a : ℤ × ℤ}
    (ha : a ∈ d.toDecompData.Sphi)
    (ha_min : ∀ b ∈ d.toDecompData.Sphi, dot mv a ≤ dot mv b)
    (ha_end : ∀ b ∈ d.toDecompData.Sphi, dot mv b = dot mv a → ∃ t : ℕ, b = a + (t : ℤ) • w)
    (hwneg : dot nl w < 0)
    (hsec : ∀ y ∈ E (↑d.toDecompData.Sphi : Set (ℤ × ℤ)), ¬ InOpenSector σ (-mv) nl y) :
    ∀ b ∈ d.toDecompData.Sphi, dot nl b ≤ dot nl a := by
  have hsign := (sector_empty_iff_sign_agree d.toDecompData hσ (-mv) nl).mp hsec
  refine nlmax_of_sign_agree d hsign ha ?_ ?_ (le_of_lt hwneg)
  · intro b hb
    have := ha_min b hb
    rw [fo_dot_neg_left, fo_dot_neg_left]
    omega
  · intro b hb hlev
    rw [fo_dot_neg_left, fo_dot_neg_left] at hlev
    exact ha_end b hb (by omega)

/-- **`hstrict` 的扇序判据，两个方向。**

左边**逐字符**是 `RegionSteps.lean` 里 `have hstrict` 那条 `sorry` 的目标（`Sφ = d.toDecompData.Sphi`，
`m := mv`，`nℓ := nl`）。⟸ 是 §3＋§5，⟹ 是 `NlmaxReduce.nlmax_of_strict` ＋ §4＋§5。 -/
theorem hstrict_iff_sector_empty {ξ : Config ℤ} (d : DecompDataZ ξ) {σ : ℤ}
    (hσ : σ = 1 ∨ σ = -1) {mv nl w a : ℤ × ℤ}
    (ha : a ∈ d.toDecompData.Sphi)
    (ha_min : ∀ b ∈ d.toDecompData.Sphi, dot mv a ≤ dot mv b)
    (ha_end : ∀ b ∈ d.toDecompData.Sphi, dot mv b = dot mv a → ∃ t : ℕ, b = a + (t : ℤ) • w)
    (hwneg : dot nl w < 0) :
    (∀ b ∈ d.toDecompData.Sphi, dot mv a < dot mv b → dot nl b ≤ dot nl a) ↔
      (∀ y ∈ E (↑d.toDecompData.Sphi : Set (ℤ × ℤ)), ¬ InOpenSector σ (-mv) nl y) := by
  constructor
  · intro hstrict
    have hnlmax : ∀ b ∈ d.toDecompData.Sphi, dot nl b ≤ dot nl a :=
      Nivat.NlmaxReduce.nlmax_of_strict hwneg ha_min ha_end hstrict
    refine (sector_empty_iff_sign_agree d.toDecompData hσ (-mv) nl).mpr ?_
    refine sign_agree_of_nlmax d.toDecompData ha ?_ hnlmax
    intro b hb
    have := ha_min b hb
    rw [fo_dot_neg_left, fo_dot_neg_left]
    omega
  · intro hsec
    exact Nivat.NlmaxReduce.strict_of_nlmax
      (nlmax_of_sector_empty d hσ ha ha_min ha_end hwneg hsec)

/-- 直接可喂给消费者的那一半（`.mpr` 的别名）。 -/
theorem hstrict_of_sector_empty {ξ : Config ℤ} (d : DecompDataZ ξ) {σ : ℤ}
    (hσ : σ = 1 ∨ σ = -1) {mv nl w a : ℤ × ℤ}
    (ha : a ∈ d.toDecompData.Sphi)
    (ha_min : ∀ b ∈ d.toDecompData.Sphi, dot mv a ≤ dot mv b)
    (ha_end : ∀ b ∈ d.toDecompData.Sphi, dot mv b = dot mv a → ∃ t : ℕ, b = a + (t : ℤ) • w)
    (hwneg : dot nl w < 0)
    (hsec : ∀ y ∈ E (↑d.toDecompData.Sphi : Set (ℤ × ℤ)), ¬ InOpenSector σ (-mv) nl y) :
    ∀ b ∈ d.toDecompData.Sphi, dot mv a < dot mv b → dot nl b ≤ dot nl a :=
  (hstrict_iff_sector_empty d hσ ha ha_min ha_end hwneg).mpr hsec

/-! ## §7. `ha_end` / `hwneg` 不可删：单位正方形的内核见证

§3 的前提里，`hsign`（＝开扇区为空）**单独不够**。见证取单位正方形
`h = ![(1,0),(0,1)]`、`p = (-1,0)`、`q = (0,-1)`、`a = (0,1)`：

- `A = (dot p (h 0), dot p (h 1)) = (-1, 0)`，`B = (0, -1)` ⟹ 两个乘积都是 `0`，符号一致成立；
- `a` 在格拉链上极大化 `dot p`（`dot p` 的极大值 `0`，面是 `{(0,0),(0,1)}` 这条线段）；
- 但 `a` **不**极大化 `dot q`：`dot q (0,0) = 0 > -1 = dot q a`。

退化的正是 `A 1 = 0`，即 `p ⊥ h 1`——`p` 自己平行于一条棱法向，`dot p` 的极大面是线段而不是
顶点，`a` 落在线段的哪一端 `E ↑d.Sphi` 决定不了。链上补上这一条的是 `ha_end` ＋ `hwneg`：
本例里 `ha_end` 逼出 `w = (0,-1)`，而 `dot q w = 1 > 0` 违反 `hwneg`，⟹ **`hwneg` 恰好排除
了这一端**。

⚠ 口径：本收据在 **`zonoF` 级**，不是 `Sphi` 级——本文件不构造 `h = sqH` 的 `DecompDataZ`
实例。若谁给出这样一个实例，同一对见证立即搬到 `Sphi` 上：`zonoF ⊆ Sphi`
（`HsuppLengthBound.zonoF_sub_Sphi`）使反例点仍在 `Sphi` 里，`bound_Z_of_Sphi` 使
`p`-极大性从 `Sphi` 传到 `zonoF`。 -/

/-- 单位正方形的两个生成元。 -/
def sqH : Fin 2 → ℤ × ℤ := ![((1 : ℤ), (0 : ℤ)), ((0 : ℤ), (1 : ℤ))]

theorem sq_zero_mem : ((0 : ℤ), (0 : ℤ)) ∈ zonoF (Finset.univ : Finset (Fin 2)) sqH :=
  (Nivat.VertexFromEdge.mem_zonoF_iff sqH _).mpr ⟨fun _ => 0, fun _ => Or.inl rfl, by simp⟩

theorem sq_a_mem : ((0 : ℤ), (1 : ℤ)) ∈ zonoF (Finset.univ : Finset (Fin 2)) sqH := by
  refine (Nivat.VertexFromEdge.mem_zonoF_iff sqH _).mpr
    ⟨![(0 : ℤ × ℤ), ((0 : ℤ), (1 : ℤ))], fun i => ?_, by simp [Fin.sum_univ_two]⟩
  fin_cases i
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem sq_sign_agree :
    ∀ i, 0 ≤ dot ((-1 : ℤ), (0 : ℤ)) (sqH i) * dot ((0 : ℤ), (-1 : ℤ)) (sqH i) := by
  intro i
  fin_cases i <;> simp only [sqH] <;> decide

theorem sq_p_max : ∀ b ∈ zonoF (Finset.univ : Finset (Fin 2)) sqH,
    dot ((-1 : ℤ), (0 : ℤ)) b ≤ dot ((-1 : ℤ), (0 : ℤ)) ((0 : ℤ), (1 : ℤ)) := by
  intro b hb
  have h1 := dot_le_suppZ sqH ((-1 : ℤ), (0 : ℤ)) hb
  have h2 : suppZ sqH ((-1 : ℤ), (0 : ℤ)) = 0 := by
    rw [suppZ, Fin.sum_univ_two]
    simp only [sqH]
    decide
  have h3 : dot ((-1 : ℤ), (0 : ℤ)) ((0 : ℤ), (1 : ℤ)) = 0 := by decide
  omega

theorem sq_q_not_max : ¬ (∀ b ∈ zonoF (Finset.univ : Finset (Fin 2)) sqH,
    dot ((0 : ℤ), (-1 : ℤ)) b ≤ dot ((0 : ℤ), (-1 : ℤ)) ((0 : ℤ), (1 : ℤ))) := by
  intro h
  have hc := h _ sq_zero_mem
  revert hc
  decide

/-- **打包**：符号一致 ＋ `p`-极大 **推不出** `q`-极大。
即 `nlmax_of_sign_agree` 的 `hend` / `hqw` 两条前提不可删。 -/
theorem sign_agree_alone_insufficient :
    (∀ i, 0 ≤ dot ((-1 : ℤ), (0 : ℤ)) (sqH i) * dot ((0 : ℤ), (-1 : ℤ)) (sqH i)) ∧
    ((0 : ℤ), (1 : ℤ)) ∈ zonoF (Finset.univ : Finset (Fin 2)) sqH ∧
    (∀ b ∈ zonoF (Finset.univ : Finset (Fin 2)) sqH,
        dot ((-1 : ℤ), (0 : ℤ)) b ≤ dot ((-1 : ℤ), (0 : ℤ)) ((0 : ℤ), (1 : ℤ))) ∧
    ¬ (∀ b ∈ zonoF (Finset.univ : Finset (Fin 2)) sqH,
        dot ((0 : ℤ), (-1 : ℤ)) b ≤ dot ((0 : ℤ), (-1 : ℤ)) ((0 : ℤ), (1 : ℤ))) :=
  ⟨sq_sign_agree, sq_a_mem, sq_p_max, sq_q_not_max⟩

/-! ## §8. 扇序条件塌回 `hwadj` 的 body：`dir` 字典

本节合成 `CORE-HOLES.md`「洞 3 的双向刻画打通」一节点名要的那一条
（「合成派 lane-tower-hlev」）。结论：集成者那条**未经内核**的猜测（「扇序条件可能塌回
`∀ j, det (d.h j) vl * det (d.h j) w ≤ 0`，即 `hwadj` 本身」）**成立**，下面全是内核项。

⚠ 本节的两条方向前提**不是我证的**，只当 binder 收，且**逐字取自 lane-tower-hbase 的
既有结论**（`tmp/wip/lane-tower-hbase-sortdir.lean` §24，他自报 EXIT=0、公理干净）：

* `hpar` ＋ `hpos` —— 就是他 `negm_pos_mul_dir_w` 的结论对
  `det (-m) (dir w) = 0 ∧ 0 < dot (-m) (dir w)`，**一个字不改**。
  ⚠ 我原打算写成 `-m = c • dir w`（`0 < c`）；那**比他手上的强**，要额外的
  `Primitive w` 才能把「平行」升级成「整数倍」。改用平行 ＋ 同向这一对之后，
  本节**不需要** `hw_prim`，与他 §24 的「不需要 `hw_prim`」口径一致。
* `hnl : nl = -dir vl` —— 他 §24 的归一化，链上出处见 `RegionSteps.lean:587`
  （`exists_cutResidualR` 的 `dir vl = −nℓ` 段；`:693` 同句）的「`dir vl = −nℓ`」。

两条都在 `tmp/` 里，按 `PROTOCOL.md §16`（`tmp/` 之间不许互 import）我不能引，
故留作形参。⟹ **本节交付的是蕴含，不是无条件等价**；谁要合成，把他那两条的实例喂进来。

📌 与 lane-towerpkg 的对账：他用 `h = ((1,0),(0,1))`、`p = (1,1)`、`q = (1,0)`、`a = (1,1)`
否掉的是**把泛函自己塞进 `det` 槽位**的那版（`det (h j) p * det (h j) q ≤ 0`）。
差的正好是一次 `dir`：正确的 `det` 形式里躺在槽位里的是泛函在 `dir` 下的**原像**
`w` / `vl`，不是泛函 `-m` / `nl`。同一组数值在正确形式下为真，见 `det_form_needs_dir`。 -/

/-- 2D Plücker（`det` 版），无前提：`det u y * ‖v‖² = dot u v * det v y + det u v * dot v y`。 -/
theorem fo_plucker_det (u v y : ℤ × ℤ) :
    det u y * dot v v = dot u v * det v y + det u v * dot v y := by
  simp only [det, dot]
  ring

/-- 2D Plücker（`dot` 版），无前提：`dot u y * ‖v‖² = dot u v * dot v y - det u v * det v y`。 -/
theorem fo_plucker_dot (u v y : ℤ × ℤ) :
    dot u y * dot v v = dot u v * dot v y - det u v * det v y := by
  simp only [det, dot]
  ring

theorem fo_dot_self_pos {v : ℤ × ℤ} (hv : v ≠ (0, 0)) : 0 < dot v v := by
  have h : v.1 ≠ 0 ∨ v.2 ≠ 0 := by
    by_cases h1 : v.1 = 0
    · exact Or.inr fun h2 => hv (Prod.ext h1 h2)
    · exact Or.inl h1
  simp only [dot]
  rcases h with h | h
  · nlinarith [mul_self_nonneg v.2, mul_self_pos.mpr h]
  · nlinarith [mul_self_nonneg v.1, mul_self_pos.mpr h]

theorem fo_dir_ne_zero {w : ℤ × ℤ} (hw : w ≠ (0, 0)) : dir w ≠ (0, 0) := by
  intro hc
  simp only [dir, Prod.mk.injEq] at hc
  exact hw (Prod.ext hc.2 (by omega))

/-- **平行 ＋ 同向 ⟹ `det _ y` 逐 `y` 同号。** `u` 与 `v` 只差一个**正有理数**倍，
不必是整数倍；`fo_plucker_det` 在 `det u v = 0` 下把它化成一条乘法不等式。
这正是绕开 `Primitive w` 的那一步。 -/
theorem fo_det_sign_transfer {u v y : ℤ × ℤ} (hv : v ≠ (0, 0))
    (hpar : det u v = 0) (hpos : 0 < dot u v) :
    (0 < det u y ↔ 0 < det v y) := by
  have hN := fo_dot_self_pos hv
  have hid := fo_plucker_det u v y
  rw [hpar, zero_mul, add_zero] at hid
  constructor
  · intro h
    nlinarith [hid, mul_pos h hN, hpos]
  · intro h
    nlinarith [hid, mul_pos hpos h, hN]

/-- `-dir v = (v.2, -v.1)`：把 `nl = -dir vl` 里的取负推到分量上，好让 `ring` 接手。 -/
theorem fo_neg_dir (v : ℤ × ℤ) : -dir v = (v.2, -v.1) := by
  show ((-(-v.2) : ℤ), (-v.1 : ℤ)) = (v.2, -v.1)
  rw [neg_neg]

theorem fo_det_dir_left_eq (w y : ℤ × ℤ) : det (dir w) y = - dot y w := by
  simp only [det, dot, dir]
  ring

theorem fo_det_right_neg_dir (y vl : ℤ × ℤ) : det y (-dir vl) = - dot y vl := by
  rw [fo_neg_dir]
  simp only [det, dot]
  ring

theorem fo_dot_neg_dir (z vl : ℤ × ℤ) : dot (-dir vl) z = det z vl := by
  rw [fo_neg_dir]
  simp only [det, dot]
  ring

/-- **`InOpenSector 1 (-mv) nl y` 逐字就是 `hwadj` 禁的那个开锥。**

右边与 `Hole3Room.nlmax_of_wadj` 的 `hwadj` 形参（`Hole3Room.lean:324`）的 body
`dot n vl < 0 ∧ dot n w < 0` 逐字符一致。 -/
theorem inOpenSector_iff_wadj_body {mv nl vl w y : ℤ × ℤ} (hw : w ≠ (0, 0))
    (hpar : det (-mv) (dir w) = 0) (hpos : 0 < dot (-mv) (dir w))
    (hnl : nl = -dir vl) :
    InOpenSector 1 (-mv) nl y ↔ (dot y vl < 0 ∧ dot y w < 0) := by
  have hsig := fo_det_sign_transfer (y := y) (fo_dir_ne_zero hw) hpar hpos
  have h2 : det y nl = - dot y vl := by rw [hnl]; exact fo_det_right_neg_dir y vl
  simp only [InOpenSector, one_mul, h2, hsig, fo_det_dir_left_eq]
  constructor
  · rintro ⟨ha, hb⟩
    exact ⟨by omega, by omega⟩
  · rintro ⟨ha, hb⟩
    exact ⟨by omega, by omega⟩

/-- ⭐ **合成：`hstrict ⟺ hwadj`。**

`Hole3Room.nlmax_of_wadj`（`Hole3Room.lean:324`）给的是 `hwadj ⟹ hnlmax` 一个方向。
这里给出**反方向**：在链上已有的 `ha` / `ha_min` / `ha_end` / `hwneg` ＋ 上面两条方向字典下，
消费者处的 `hstrict`（`RegionSteps.lean` 的 `have hstrict`）与 `hwadj` 的 body **等价**。

⟹ 两条推论，都不是修辞：
1. 针对 `hstrict` 造出的内核反例**逐字也是 `hwadj` 的反例**，反之亦然；
2. 任何 ξ 侧的生产者，要么两条一起产出，要么一条都产不出。 -/
theorem hstrict_iff_wadj {ξ : Config ℤ} (d : DecompDataZ ξ)
    {mv nl vl w a : ℤ × ℤ} (hw : w ≠ (0, 0))
    (hpar : det (-mv) (dir w) = 0) (hpos : 0 < dot (-mv) (dir w))
    (hnl : nl = -dir vl)
    (ha : a ∈ d.toDecompData.Sphi)
    (ha_min : ∀ b ∈ d.toDecompData.Sphi, dot mv a ≤ dot mv b)
    (ha_end : ∀ b ∈ d.toDecompData.Sphi, dot mv b = dot mv a →
      ∃ t : ℕ, b = a + (t : ℤ) • w)
    (hwneg : dot nl w < 0) :
    (∀ b ∈ d.toDecompData.Sphi, dot mv a < dot mv b → dot nl b ≤ dot nl a) ↔
      (∀ n ∈ E (↑d.toDecompData.Sphi : Set (ℤ × ℤ)),
        ¬ (dot n vl < 0 ∧ dot n w < 0)) := by
  rw [hstrict_iff_sector_empty d (Or.inl rfl) ha ha_min ha_end hwneg]
  constructor
  · intro h n hn hcon
    exact h n hn ((inOpenSector_iff_wadj_body hw hpar hpos hnl).mpr hcon)
  · intro h y hy hin
    exact h y hy ((inOpenSector_iff_wadj_body hw hpar hpos hnl).mp hin)

/-- **`det` 形式**：`hwadj` 的 body 在被完全穷举的 `E ↑d.Sphi` 上就是逐生成元的
两个 `det` 反号。这正是集成者猜的那条。 -/
theorem wadj_iff_det_gen {ξ : Config ℤ} (d : DecompDataZ ξ)
    {mv nl vl w : ℤ × ℤ} (hw : w ≠ (0, 0))
    (hpar : det (-mv) (dir w) = 0) (hpos : 0 < dot (-mv) (dir w))
    (hnl : nl = -dir vl) :
    (∀ n ∈ E (↑d.toDecompData.Sphi : Set (ℤ × ℤ)),
        ¬ (dot n vl < 0 ∧ dot n w < 0)) ↔
      ∀ j : Fin d.toDecompData.m,
        det (d.toDecompData.h j) vl * det (d.toDecompData.h j) w ≤ 0 := by
  have hN := fo_dot_self_pos (fo_dir_ne_zero hw)
  -- `dot (-mv) z` 与 `dot (dir w) z = -det z w` 逐 `z` 同号（`dot` 版 Plücker）。
  have hkey : ∀ z : ℤ × ℤ,
      (dot (-mv) z * dot nl z) * dot (dir w) (dir w)
        = -(dot (-mv) (dir w) * (det z vl * det z w)) := by
    intro z
    have hid := fo_plucker_dot (-mv) (dir w) z
    rw [hpar, zero_mul, sub_zero] at hid
    have hz : dot nl z = det z vl := by rw [hnl]; exact fo_dot_neg_dir z vl
    have hdw : dot (dir w) z = - det z w := by simp only [dot, dir, det]; ring
    calc (dot (-mv) z * dot nl z) * dot (dir w) (dir w)
        = (dot (-mv) z * dot (dir w) (dir w)) * dot nl z := by ring
      _ = (dot (-mv) (dir w) * dot (dir w) z) * dot nl z := by rw [hid]
      _ = -(dot (-mv) (dir w) * (det z vl * det z w)) := by rw [hz, hdw]; ring
  have h1 := sector_empty_iff_sign_agree d.toDecompData (σ := 1) (Or.inl rfl) (-mv) nl
  constructor
  · intro h j
    have hs : ∀ y ∈ E (↑d.toDecompData.Sphi : Set (ℤ × ℤ)),
        ¬ InOpenSector 1 (-mv) nl y := fun y hy hin =>
      h y hy ((inOpenSector_iff_wadj_body hw hpar hpos hnl).mp hin)
    have hj := h1.mp hs j
    nlinarith [hkey (d.toDecompData.h j), hj, hN, hpos]
  · intro h y hy hin
    refine h1.mpr (fun i => ?_) y hy ((inOpenSector_iff_wadj_body hw hpar hpos hnl).mpr hin)
    nlinarith [hkey (d.toDecompData.h i), h i, hN, hpos]

/-- **合成**：`hstrict` ⟺ 逐生成元 `det` 反号。 -/
theorem hstrict_iff_det_gen {ξ : Config ℤ} (d : DecompDataZ ξ)
    {mv nl vl w a : ℤ × ℤ} (hw : w ≠ (0, 0))
    (hpar : det (-mv) (dir w) = 0) (hpos : 0 < dot (-mv) (dir w))
    (hnl : nl = -dir vl)
    (ha : a ∈ d.toDecompData.Sphi)
    (ha_min : ∀ b ∈ d.toDecompData.Sphi, dot mv a ≤ dot mv b)
    (ha_end : ∀ b ∈ d.toDecompData.Sphi, dot mv b = dot mv a →
      ∃ t : ℕ, b = a + (t : ℤ) • w)
    (hwneg : dot nl w < 0) :
    (∀ b ∈ d.toDecompData.Sphi, dot mv a < dot mv b → dot nl b ≤ dot nl a) ↔
      ∀ j : Fin d.toDecompData.m,
        det (d.toDecompData.h j) vl * det (d.toDecompData.h j) w ≤ 0 :=
  (hstrict_iff_wadj d hw hpar hpos hnl ha ha_min ha_end hwneg).trans
    (wadj_iff_det_gen d hw hpar hpos hnl)

/-- **对账收据**（lane-towerpkg 2026-09-24 的数值实例，这里内核化）。

同一组数据 `h = sqH`、泛函 `p = (1,1)`、`q = (1,0)`：
1. 符号一致（本文件判据的右边）**真**；
2. 把**泛函自己**塞进 `det` 槽位的那版 `det (h j) p * det (h j) q ≤ 0` **假**
   （`j = 1` 处取 `(-1)·(-1) = 1 > 0`）；
3. 换成泛函在 `dir` 下的**原像** `vl = (0,1)`、`w = (1,-1)` 之后，`det` 形式**真**；
4. 这组数据确实满足本节的两条方向前提（`hpar`/`hpos` 以 `mv = (-1,-1)` 取到，
   `hnl` 以 `vl = (0,1)` 取到）。

⟹ 他否掉的不是本文件的判据，是少了一次 `dir` 的那一版。 -/
theorem det_form_needs_dir :
    (∀ i, 0 ≤ dot ((1 : ℤ), (1 : ℤ)) (sqH i) * dot ((1 : ℤ), (0 : ℤ)) (sqH i)) ∧
    ¬ (∀ i, det (sqH i) ((1 : ℤ), (1 : ℤ)) * det (sqH i) ((1 : ℤ), (0 : ℤ)) ≤ 0) ∧
    (∀ i, det (sqH i) ((0 : ℤ), (1 : ℤ)) * det (sqH i) ((1 : ℤ), (-1 : ℤ)) ≤ 0) ∧
    det (-((-1 : ℤ), (-1 : ℤ))) (dir ((1 : ℤ), (-1 : ℤ))) = 0 ∧
    0 < dot (-((-1 : ℤ), (-1 : ℤ))) (dir ((1 : ℤ), (-1 : ℤ))) ∧
    ((1 : ℤ), (0 : ℤ)) = -dir ((0 : ℤ), (1 : ℤ)) := by
  refine ⟨fun i => ?_, ?_, fun i => ?_, ?_, ?_, ?_⟩
  · fin_cases i <;> simp only [sqH] <;> decide
  · intro h
    have hb := h 1
    revert hb
    simp only [sqH]
    decide
  · fin_cases i <;> simp only [sqH] <;> decide
  · decide
  · decide
  · decide

#print axioms Nivat.LaneTowerHlevFanOrder.dot_zSel_eq_suppZ
#print axioms Nivat.LaneTowerHlevFanOrder.dot_le_suppZ
#print axioms Nivat.LaneTowerHlevFanOrder.bound_Z_of_Sphi
#print axioms Nivat.LaneTowerHlevFanOrder.bound_Sphi_of_Z
#print axioms Nivat.LaneTowerHlevFanOrder.dot_eq_suppZ_of_max
#print axioms Nivat.LaneTowerHlevFanOrder.nlmax_of_sign_agree
#print axioms Nivat.LaneTowerHlevFanOrder.sign_agree_of_nlmax
#print axioms Nivat.LaneTowerHlevFanOrder.fo_genPerp'_scale
#print axioms Nivat.LaneTowerHlevFanOrder.inOpenSector_of_mul_neg
#print axioms Nivat.LaneTowerHlevFanOrder.sector_empty_iff_sign_agree
#print axioms Nivat.LaneTowerHlevFanOrder.nlmax_of_sector_empty
#print axioms Nivat.LaneTowerHlevFanOrder.hstrict_iff_sector_empty
#print axioms Nivat.LaneTowerHlevFanOrder.hstrict_of_sector_empty
#print axioms Nivat.LaneTowerHlevFanOrder.sign_agree_alone_insufficient
#print axioms Nivat.LaneTowerHlevFanOrder.fo_det_sign_transfer
#print axioms Nivat.LaneTowerHlevFanOrder.inOpenSector_iff_wadj_body
#print axioms Nivat.LaneTowerHlevFanOrder.hstrict_iff_wadj
#print axioms Nivat.LaneTowerHlevFanOrder.wadj_iff_det_gen
#print axioms Nivat.LaneTowerHlevFanOrder.hstrict_iff_det_gen
#print axioms Nivat.LaneTowerHlevFanOrder.det_form_needs_dir

/-! ## §9. 符号对账与 `hnl` 的链上兑现（2026-09-24 追加）

### §9.1 四条读法逐字同真——**谁都不用取反**

集成者与 lane-towerpkg 对「`(-m, nℓ)` 这一对要不要取一次反」意见相左。下面把四条读法
在**同一个 `z`** 上内核对账，结论是集成者对：判据本身只有一条，四种写法逐字同真。

| 出处 | 判据（固定 `z`） |
|---|---|
| 本文件 `sector_empty_iff_sign_agree`，实例化在 `(p,q) := (-m, nℓ)` | `0 ≤ dot (-m) z * dot nℓ z` |
| lane-towerpkg 建议改用的 `(-nℓ, m)` | `0 ≤ dot (-nℓ) z * dot m z` |
| `ZonoNormalPair.hwadj_iff_no_gen_normal_between_chain` 按 `SepsLine` 展开 | `dot z nℓ * dot z m ≤ 0` |
| `hwadj_iff_dot_normal_pair` 在 `(p,q) := (-nℓ, -m)` 上的实例 | `dot (-nℓ) z * dot (-m) z ≤ 0` |

算术很短：**同时翻两个参数的符号 ⟹ 乘积不变**（第 1 条与第 2 条、第 3 条与第 4 条各是这样），
**只翻一个参数 ⟹ 乘积变号、判据方向跟着翻**（第 1 条与第 3 条是这样）。
lane-towerpkg 的警报来自把「翻一个」和「翻两个」并作一次比较：他自己用的 `(-nℓ, -m)` 与
我的 `(-m, nℓ)` 之间是「翻两个再交换」，本来就同真，不需要补任何符号。

⟹ **合成里不许给任何参数补负号**（补了就变成互补锥，`⟸` 当场塌）。 -/

theorem fo_sign_pair_swap (mv nl z : ℤ × ℤ) :
    (0 ≤ dot (-mv) z * dot nl z) ↔ (0 ≤ dot (-nl) z * dot mv z) := by
  have h : dot (-nl) z * dot mv z = dot (-mv) z * dot nl z := by
    simp only [fo_dot_neg_left]; ring
  rw [h]

theorem fo_sign_pair_comm_le (mv nl z : ℤ × ℤ) :
    (0 ≤ dot (-mv) z * dot nl z) ↔ (dot z nl * dot z mv ≤ 0) := by
  have h : dot z nl * dot z mv = -(dot (-mv) z * dot nl z) := by
    rw [fo_dot_neg_left]; simp only [dot]; ring
  rw [h]
  constructor <;> intro hh <;> linarith

theorem fo_sign_pair_both_neg (mv nl z : ℤ × ℤ) :
    (0 ≤ dot (-mv) z * dot nl z) ↔ (dot (-nl) z * dot (-mv) z ≤ 0) := by
  have h : dot (-nl) z * dot (-mv) z = -(dot (-mv) z * dot nl z) := by
    simp only [fo_dot_neg_left]; ring
  rw [h]
  constructor <;> intro hh <;> linarith

/-! ### §9.2 `hnl` 不是新债

`hstrict_iff_wadj` 的 `hnl : nl = -dir vl` 在链上由主仓现成的
`Nivat.RegionNlDict.nl_eq_neg_dir_vl_and_det_u'` 兑现，它的四条前提
`Primitive vl` / `dot nℓ vl = 0` / `0 < det nℓ vl` / `dot nℓ u' = -1` 逐条是
`exists_cutResidualR_of_claim46` 的原生 binder（`hvl_prim` / `hperp` / `hdetpos` / `hnu`）。
下面两条把 `hnl` 换成那四条，交给消费者时不必再自己拆字典。

⚠ `hpar` / `hpos` 仍是形参，它们是 lane-tower-hbase 的
`tmp/wip/lane-tower-hbase-sortdir.lean` §24 `negm_pos_mul_dir_w` 的结论对，不是我证的。 -/

/-- ⭐ `hstrict ⟺ hwadj`，`hnl` 已换成链上四条原生 binder。 -/
theorem hstrict_iff_wadj_chain {ξ : Config ℤ} (d : DecompDataZ ξ)
    {mv nl vl w u' a : ℤ × ℤ} (hw : w ≠ (0, 0))
    (hpar : det (-mv) (dir w) = 0) (hpos : 0 < dot (-mv) (dir w))
    (hvlp : Primitive vl) (hperp : dot nl vl = 0) (hdetpos : 0 < det nl vl)
    (hnu : dot nl u' = -1)
    (ha : a ∈ d.toDecompData.Sphi)
    (ha_min : ∀ b ∈ d.toDecompData.Sphi, dot mv a ≤ dot mv b)
    (ha_end : ∀ b ∈ d.toDecompData.Sphi, dot mv b = dot mv a →
      ∃ t : ℕ, b = a + (t : ℤ) • w)
    (hwneg : dot nl w < 0) :
    (∀ b ∈ d.toDecompData.Sphi, dot mv a < dot mv b → dot nl b ≤ dot nl a) ↔
      (∀ n ∈ E (↑d.toDecompData.Sphi : Set (ℤ × ℤ)),
        ¬ (dot n vl < 0 ∧ dot n w < 0)) :=
  hstrict_iff_wadj d hw hpar hpos
    (Nivat.RegionNlDict.nl_eq_neg_dir_vl_and_det_u' hvlp hperp hdetpos hnu).1
    ha ha_min ha_end hwneg

/-- `det` 形式，同样换成链上四条原生 binder。 -/
theorem hstrict_iff_det_gen_chain {ξ : Config ℤ} (d : DecompDataZ ξ)
    {mv nl vl w u' a : ℤ × ℤ} (hw : w ≠ (0, 0))
    (hpar : det (-mv) (dir w) = 0) (hpos : 0 < dot (-mv) (dir w))
    (hvlp : Primitive vl) (hperp : dot nl vl = 0) (hdetpos : 0 < det nl vl)
    (hnu : dot nl u' = -1)
    (ha : a ∈ d.toDecompData.Sphi)
    (ha_min : ∀ b ∈ d.toDecompData.Sphi, dot mv a ≤ dot mv b)
    (ha_end : ∀ b ∈ d.toDecompData.Sphi, dot mv b = dot mv a →
      ∃ t : ℕ, b = a + (t : ℤ) • w)
    (hwneg : dot nl w < 0) :
    (∀ b ∈ d.toDecompData.Sphi, dot mv a < dot mv b → dot nl b ≤ dot nl a) ↔
      ∀ j : Fin d.toDecompData.m,
        det (d.toDecompData.h j) vl * det (d.toDecompData.h j) w ≤ 0 :=
  hstrict_iff_det_gen d hw hpar hpos
    (Nivat.RegionNlDict.nl_eq_neg_dir_vl_and_det_u' hvlp hperp hdetpos hnu).1
    ha ha_min ha_end hwneg

#print axioms fo_sign_pair_swap
#print axioms fo_sign_pair_comm_le
#print axioms fo_sign_pair_both_neg
#print axioms hstrict_iff_wadj_chain
#print axioms hstrict_iff_det_gen_chain

/-! ## §10. 全原生版本（2026-09-24 追加）

`hstrict_iff_wadj` 的三条方向形参本轮全部被主仓兑现，**一条外部生产者都不剩**：

| 形参 | 兑现者 | 兑现者的前提 |
|---|---|---|
| `hnl : nl = -(dir vl)` | `Nivat.RegionNlDict.nl_eq_neg_dir_vl_and_det_u'` | `hvl_prim` / `hperp` / `hdetpos` / `hnu` |
| `hpar : det (-mv) (dir w) = 0` | `fo_det_negm_dir_w_zero`（本节；同命题另有 `LaneTowerPkgNormalPair.det_negm_dir_w_eq_zero`） | `hmw` |
| `hpos : 0 < dot (-mv) (dir w)` | `LaneTowerPkgNormalPair.negm_pos_dot_dir_w_of_chain` | 上面四条 ＋ `hwneg` / `hmw` / `hmvl` / `w ≠ 0` |

于是下面两条的前提表逐条是 `exists_cutResidualR_of_claim46`（`RegionSteps.lean`，
**认标识符不认行号**）的原生 binder：`hvl_prim` / `hperp` / `hdetpos` / `hnu` 在签名里；
`hw_prim` / `hwneg` / `hmw` / `hmvl` 是体内那条塔包 `obtain` 的分量；
`ha` / `ha_min` / `ha_end` 是体内 `obtain ⟨Sφ, a, hgenφ, hSφ, ha_min, ha_end⟩` 的分量
（`ha` 取 `hgenφ` 的第一个合取）。

⚠ **仍然不供 `hstrict` 本身**：下面是 `↔`，右边那条 `hwadj` 照旧欠着，
而按 lane-tower-hbase 的 `gZL` 台架它不可能从几何 binder 单独推出（见本文件抬头）。 -/

/-- `hpar` 的独立形态：`dot mv w = 0` 逐字就是 `det (-mv) (dir w) = 0`
（`det (-mv) (dir w) = -(dot mv w)`）。

⚠ **同命题的 `LaneTowerPkgNormalPair.det_negm_dir_w_eq_zero` 也在主仓**（lane-towerpkg
当轮专为本节加的）。这里本地再证一条，只因为写本节时那条还没进 olean；两条都在，
取哪条都行，不是分歧。 -/
theorem fo_det_negm_dir_w_zero {mv w : ℤ × ℤ} (hmw : dot mv w = 0) :
    det (-mv) (dir w) = 0 := by
  have h : det (-mv) (dir w) = - dot mv w := by
    show (-mv.1) * w.1 - (-mv.2) * (-w.2) = -(mv.1 * w.1 + mv.2 * w.2)
    ring
  rw [h, hmw, neg_zero]

/-- ⭐⭐ **全原生**：`hstrict ⟺ hwadj`，前提表里再没有任何外部生产者。 -/
theorem hstrict_iff_wadj_native {ξ : Config ℤ} (d : DecompDataZ ξ)
    {mv nl vl w u' a : ℤ × ℤ}
    (hvlp : Primitive vl) (hwp : Primitive w)
    (hperp : dot nl vl = 0) (hdetpos : 0 < det nl vl)
    (hnu : dot nl u' = -1) (hwneg : dot nl w < 0)
    (hmw : dot mv w = 0) (hmvl : 0 < dot mv vl)
    (ha : a ∈ d.toDecompData.Sphi)
    (ha_min : ∀ b ∈ d.toDecompData.Sphi, dot mv a ≤ dot mv b)
    (ha_end : ∀ b ∈ d.toDecompData.Sphi, dot mv b = dot mv a →
      ∃ t : ℕ, b = a + (t : ℤ) • w) :
    (∀ b ∈ d.toDecompData.Sphi, dot mv a < dot mv b → dot nl b ≤ dot nl a) ↔
      (∀ n ∈ E (↑d.toDecompData.Sphi : Set (ℤ × ℤ)),
        ¬ (dot n vl < 0 ∧ dot n w < 0)) := by
  have hw : w ≠ 0 := (prim_iff_primitive.mpr hwp).ne_zero
  have hw0 : w ≠ ((0 : ℤ), (0 : ℤ)) := fun h => hw (by rw [h]; rfl)
  exact hstrict_iff_wadj d hw0
    (fo_det_negm_dir_w_zero hmw)
    (Nivat.LaneTowerPkgNormalPair.negm_pos_dot_dir_w_of_chain hw hvlp hperp hdetpos hnu
      hwneg hmw hmvl)
    (Nivat.RegionNlDict.nl_eq_neg_dir_vl_and_det_u' hvlp hperp hdetpos hnu).1
    ha ha_min ha_end hwneg

/-- **全原生的 `det` 形式。**  槽位里放的是泛函在 `dir` 下的**原像** `vl` / `w`，
不是泛函 `-m` / `nℓ` 自己——丢掉这一次 `dir` 的那一版为假，见 `det_form_needs_dir`。 -/
theorem hstrict_iff_det_gen_native {ξ : Config ℤ} (d : DecompDataZ ξ)
    {mv nl vl w u' a : ℤ × ℤ}
    (hvlp : Primitive vl) (hwp : Primitive w)
    (hperp : dot nl vl = 0) (hdetpos : 0 < det nl vl)
    (hnu : dot nl u' = -1) (hwneg : dot nl w < 0)
    (hmw : dot mv w = 0) (hmvl : 0 < dot mv vl)
    (ha : a ∈ d.toDecompData.Sphi)
    (ha_min : ∀ b ∈ d.toDecompData.Sphi, dot mv a ≤ dot mv b)
    (ha_end : ∀ b ∈ d.toDecompData.Sphi, dot mv b = dot mv a →
      ∃ t : ℕ, b = a + (t : ℤ) • w) :
    (∀ b ∈ d.toDecompData.Sphi, dot mv a < dot mv b → dot nl b ≤ dot nl a) ↔
      ∀ j : Fin d.toDecompData.m,
        det (d.toDecompData.h j) vl * det (d.toDecompData.h j) w ≤ 0 := by
  have hw : w ≠ 0 := (prim_iff_primitive.mpr hwp).ne_zero
  have hw0 : w ≠ ((0 : ℤ), (0 : ℤ)) := fun h => hw (by rw [h]; rfl)
  exact hstrict_iff_det_gen d hw0
    (fo_det_negm_dir_w_zero hmw)
    (Nivat.LaneTowerPkgNormalPair.negm_pos_dot_dir_w_of_chain hw hvlp hperp hdetpos hnu
      hwneg hmw hmvl)
    (Nivat.RegionNlDict.nl_eq_neg_dir_vl_and_det_u' hvlp hperp hdetpos hnu).1
    ha ha_min ha_end hwneg

#print axioms hstrict_iff_wadj_native
#print axioms hstrict_iff_det_gen_native

/-! ## §11. 消费者现场形态（2026-09-24 追加）

集成者亲读 `RegionSteps.lean` 的塔包 `obtain`（`lane_towerpkg_package` 的输出）与生成包 `obtain` 后的派工：把 §10 改写成
**消费者 `have hstrict`（`exists_cutResidualR_of_claim46` 体内）现场就能直接 `exact` 的形状**，
前提表**只许**出现那两条 `obtain` 的分量 ＋ `exists_cutResidualR_of_claim46` 的原生 binder。

逐条对账（`RegionSteps.lean`，当轮亲读；认标识符不认行号）：

| 本节形参 | 现场来源 |
|---|---|
| `hvlp : Primitive vl` | 原生 binder `hvl_prim`（`:1907`） |
| `hperp : dot nl vl = 0` | 原生 binder `hperp`（`:1908`） |
| `hdetpos : 0 < det nl vl` | 原生 binder `hdetpos`（`:1928`） |
| `hnu : dot nl u' = -1` | 原生 binder `hnu`（`:1928`，与 `hdetpos` 同行） |
| `hwp : Primitive w` | 塔包 `obtain` 的 `hw_prim`（`:1957`） |
| `hmw : dot m w = 0` | 塔包 `obtain` 的 `hmw`（`:1957`） |
| `hmvl : 0 < dot m vl` | 塔包 `obtain` 的 `hmvl`（`:1957`） |
| `hwneg : dot nl w < 0` | 塔包 `obtain` 的 `hwneg`（`:1957`） |
| `hgenφ` / `hSφ` / `ha_min` / `ha_end` | 生成包 `obtain ⟨Sφ, a, hgenφ, hSφ, ha_min, ha_end⟩`（`:1979`） |

⚠ **三件当轮亲自核过的，不是照抄派工单**：

1. **`a ∈ Sφ` 不需要新 binder。** `Nivat.Colle.GeneratesAt ξ S a` 的定义
   （`Generating.lean:17`）第一个合取**逐字**就是 `a ∈ S`：
   `GeneratesAt ξ S a := a ∈ S ∧ ∀ x ∈ orbitClosure ξ, …`。故 `hgenφ.1` 即可，
   集成者「不蕴含就报我，别自己加 binder」的分支没有发生。
2. **`m` 与 `mv` 是逐字符同一个**。本文件别处的形参名叫 `mv`，这里改叫 `m` 与现场一致；
   `-mv` **只出现在 §8/§10 的证明体内**（`hpar` / `hpos` 那两步），
   **不出现在本节任何语句里**，所以没有需要对的符号。
3. **`ha_min` / `ha_end` 在现场是对 `Sφ` 说的，不是对 `d.toDecompData.Sphi`**；
   两者由 `hSφ` 相等。本节保留 `Sφ` 与 `hSφ` 两个形参、结论也对 `Sφ` 说，
   于是与 `:2209` 那条 `have hstrict` 的目标**逐字符同形**，现场不必再 `rw`。

⚠ 仍然**不供** `hcrit` 本身。本节是 `←` 单向：判据 ⟹ `hstrict`。判据要从
`lane_towerpkg_package`（`:1969`）那一侧多产一条合取，不在本文件。 -/

/-- ⭐⭐⭐ **消费者现场形态**：生成元判据 ⟹ `hstrict`，前提逐条是现场作用域里已有的东西。

结论与 `exists_cutResidualR_of_claim46` 体内 `have hstrict`（`RegionSteps.lean`）
的目标逐字符同形。 -/
theorem hstrict_of_det_gen_onsite {ξ : Config ℤ} (d : DecompDataZ ξ)
    {m nl vl w u' a : ℤ × ℤ} {Sφ : Finset (ℤ × ℤ)}
    (hvlp : Primitive vl) (hwp : Primitive w)
    (hperp : dot nl vl = 0) (hdetpos : 0 < det nl vl)
    (hnu : dot nl u' = -1) (hwneg : dot nl w < 0)
    (hmw : dot m w = 0) (hmvl : 0 < dot m vl)
    (hgenφ : Nivat.Colle.GeneratesAt ξ Sφ a)
    (hSφ : Sφ = d.toDecompData.Sphi)
    (ha_min : ∀ b ∈ Sφ, dot m a ≤ dot m b)
    (ha_end : ∀ b ∈ Sφ, dot m b = dot m a → ∃ t : ℕ, b = a + (t : ℤ) • w)
    (hcrit : ∀ j : Fin d.toDecompData.m,
      det (d.toDecompData.h j) vl * det (d.toDecompData.h j) w ≤ 0) :
    ∀ b ∈ Sφ, dot m a < dot m b → dot nl b ≤ dot nl a := by
  subst hSφ
  exact (hstrict_iff_det_gen_native d hvlp hwp hperp hdetpos hnu hwneg hmw hmvl
    hgenφ.1 ha_min ha_end).mpr hcrit

/-- 同一条的 `hwadj` 形态（右边换成边法向条件，其余逐字相同）。 -/
theorem hstrict_of_wadj_onsite {ξ : Config ℤ} (d : DecompDataZ ξ)
    {m nl vl w u' a : ℤ × ℤ} {Sφ : Finset (ℤ × ℤ)}
    (hvlp : Primitive vl) (hwp : Primitive w)
    (hperp : dot nl vl = 0) (hdetpos : 0 < det nl vl)
    (hnu : dot nl u' = -1) (hwneg : dot nl w < 0)
    (hmw : dot m w = 0) (hmvl : 0 < dot m vl)
    (hgenφ : Nivat.Colle.GeneratesAt ξ Sφ a)
    (hSφ : Sφ = d.toDecompData.Sphi)
    (ha_min : ∀ b ∈ Sφ, dot m a ≤ dot m b)
    (ha_end : ∀ b ∈ Sφ, dot m b = dot m a → ∃ t : ℕ, b = a + (t : ℤ) • w)
    (hwadj : ∀ n ∈ E (↑d.toDecompData.Sphi : Set (ℤ × ℤ)),
      ¬ (dot n vl < 0 ∧ dot n w < 0)) :
    ∀ b ∈ Sφ, dot m a < dot m b → dot nl b ≤ dot nl a := by
  subst hSφ
  exact (hstrict_iff_wadj_native d hvlp hwp hperp hdetpos hnu hwneg hmw hmvl
    hgenφ.1 ha_min ha_end).mpr hwadj

#print axioms hstrict_of_det_gen_onsite
#print axioms hstrict_of_wadj_onsite

/-! ## §12. 判据的「扇序相邻」形态（2026-09-24 追加）

集成者第 193 轮点名要的重述：`RegionSteps.lean` 里 `hstrict_iff_det_gen_native` 之后
留下的那条判据 `∀ j, det (h j) vl * det (h j) w ≤ 0`，能不能写成
「`E ↑Sφ` 的循环序里 `nℓ` 与 `dir w` 相邻」。**能**，而且不是近似：
`InOpenSector 1 (dir w) nl` 逐字就是 §4 那个开扇区，判据就是它在 `E ↑Sφ` 上为空。

⛔ **符号订正（内核见证，见 `fo_adjacency_tracks_crit`）**：集成者信里写的是
「`nℓ` 与 `-(dir w)` 相邻」，**差一个负号**。正确的配对是 `(dir w, nℓ)`，等价地
`(-m, nℓ)`（链上 `-m` 与 `dir w` 正倍数同向，即 `hpar` ＋ `hpos`）。`E` 对取负封闭，
所以另一个真配对是 `(-(dir w), -nℓ)`——**两个负号一起翻**；只翻一个得到的
`(-(dir w), nℓ)` 既不是这个也不是那个。八边形台架上好 `w = (-1,-1)` 判据为真，而
`(-(dir w), nℓ)` 的开弧里坐着 `(-1,-1)`，⟹ 那一版被内核否掉。
（同一族失误见 §8 `det_form_needs_dir`：翻一个 vs 翻两个。）

⚠ 本节**不新造 `Prop`**：右边用的是 §4 已有的 `InOpenSector`，那条 `def` 的 docstring
已注明「无原文对应物，形状照抄 `NormalCycle.hnoArc`（`NormalCycle.lean:176`）」。
⟹ 本节交付的是恒等重述，不引入新债，也不碰 `Arc` / `NormalCycle` 本身。

⚠ 射程：「相邻」的严格含义是**开弧里没有 `E` 的点**，**不含**「`dir w ∈ E`、`nℓ ∈ E`」
这两条 membership。构造方若能同时给出 membership，那就是通常意义的「循环序里相邻」；
给不出的话本节形式照样成立、照样够用。⛔ **不要**把本节读成「洞 3 已兑现」：判据仍然
必须由塔包挑 `w` 的方式兑现（lane-tower-hbase 的 `hstrict_GZ_N_fails` /
`hstrict_GZ_W_holds`：同一个 `d`/`Sφ`/`vl`/`nℓ`/`u'`，只换 `w`，判据真假翻转）。 -/

/-- 把 `-m` 换成 `dir w`：两者只差一个**正有理数**倍（`hpar` ＋ `hpos`），
而 `InOpenSector` 的第一格只看 `det _ y` 的符号，所以开扇区逐点不变。
这一步用的是 §8 的 `fo_det_sign_transfer`，**不需要** `Primitive w`。 -/
theorem fo_inOpenSector_transfer {mv nl w : ℤ × ℤ} (hw : w ≠ ((0 : ℤ), (0 : ℤ)))
    (hpar : det (-mv) (dir w) = 0) (hpos : 0 < dot (-mv) (dir w)) (y : ℤ × ℤ) :
    InOpenSector 1 (-mv) nl y ↔ InOpenSector 1 (dir w) nl y := by
  have h := fo_det_sign_transfer (u := -mv) (v := dir w) (y := y)
    (fo_dir_ne_zero hw) hpar hpos
  simp only [InOpenSector, one_mul, h]

/-- ⭐ **判据的扇序相邻形态。** `hwadj` 的 body 在 `E ↑d.Sphi` 上为空
⟺ `dir w` 与 `nℓ` 之间的开弧里没有 `E` 的点。

前提与 §8 的 `wadj_iff_det_gen` 逐字相同（`hw` / `hpar` / `hpos` / `hnl`），
没有任何新增 binder。 -/
theorem wadj_iff_no_E_between {ξ : Config ℤ} (d : DecompDataZ ξ)
    {mv nl vl w : ℤ × ℤ} (hw : w ≠ ((0 : ℤ), (0 : ℤ)))
    (hpar : det (-mv) (dir w) = 0) (hpos : 0 < dot (-mv) (dir w))
    (hnl : nl = -dir vl) :
    (∀ n ∈ E (↑d.toDecompData.Sphi : Set (ℤ × ℤ)),
        ¬ (dot n vl < 0 ∧ dot n w < 0)) ↔
      (∀ y ∈ E (↑d.toDecompData.Sphi : Set (ℤ × ℤ)),
        ¬ InOpenSector 1 (dir w) nl y) := by
  constructor
  · intro h y hy hin
    exact h y hy ((inOpenSector_iff_wadj_body hw hpar hpos hnl).mp
      ((fo_inOpenSector_transfer hw hpar hpos y).mpr hin))
  · intro h n hn hcon
    exact h n hn ((fo_inOpenSector_transfer hw hpar hpos n).mp
      ((inOpenSector_iff_wadj_body hw hpar hpos hnl).mpr hcon))

/-- ⭐ **直接产出 `RegionSteps.lean` 里 `hstrict_iff_det_gen_native` 之后那条 `sorry`。**

结论逐字符是那条 `sorry` 的目标；前提表与 §10 的 `hstrict_iff_det_gen_native`
**完全一致**（全部来自 `RegionSteps.lean` 的原生 binder ＋ 塔包 `obtain`），
唯一的新输入是 `hadj`——「`dir w` 与 `nℓ` 之间的开弧里没有 `E ↑Sφ` 的点」。

⟹ 前驱构造若**定义上**把 `dir w` 挑成 `nℓ` 在角序里的紧邻，`hadj` 就是构造的直接读出。 -/
theorem hcrit_of_no_E_between_native {ξ : Config ℤ} (d : DecompDataZ ξ)
    {m nl vl w u' : ℤ × ℤ}
    (hvlp : Primitive vl) (hwp : Primitive w)
    (hperp : dot nl vl = 0) (hdetpos : 0 < det nl vl)
    (hnu : dot nl u' = -1) (hwneg : dot nl w < 0)
    (hmw : dot m w = 0) (hmvl : 0 < dot m vl)
    (hadj : ∀ y ∈ E (↑d.toDecompData.Sphi : Set (ℤ × ℤ)),
      ¬ InOpenSector 1 (dir w) nl y) :
    ∀ j : Fin d.toDecompData.m,
      det (d.toDecompData.h j) vl * det (d.toDecompData.h j) w ≤ 0 := by
  have hw : w ≠ 0 := (prim_iff_primitive.mpr hwp).ne_zero
  have hw0 : w ≠ ((0 : ℤ), (0 : ℤ)) := fun h => hw (by rw [h]; rfl)
  have hpos := Nivat.LaneTowerPkgNormalPair.negm_pos_dot_dir_w_of_chain hw hvlp hperp
    hdetpos hnu hwneg hmw hmvl
  have hnl := (Nivat.RegionNlDict.nl_eq_neg_dir_vl_and_det_u' hvlp hperp hdetpos hnu).1
  exact (wadj_iff_det_gen d hw0 (fo_det_negm_dir_w_zero hmw) hpos hnl).mp
    ((wadj_iff_no_E_between d hw0 (fo_det_negm_dir_w_zero hmw) hpos hnl).mpr hadj)

/-- **消费者现场形态**：从「扇序相邻」一步到 `RegionSteps.lean` 那条 `have hstrict` 的目标。
前提表 ＝ `hstrict_of_det_gen_onsite` 的前提表，只把 `hcrit` 换成 `hadj`。 -/
theorem hstrict_of_no_E_between_onsite {ξ : Config ℤ} (d : DecompDataZ ξ)
    {m nl vl w u' a : ℤ × ℤ} {Sφ : Finset (ℤ × ℤ)}
    (hvlp : Primitive vl) (hwp : Primitive w)
    (hperp : dot nl vl = 0) (hdetpos : 0 < det nl vl)
    (hnu : dot nl u' = -1) (hwneg : dot nl w < 0)
    (hmw : dot m w = 0) (hmvl : 0 < dot m vl)
    (hgenφ : Nivat.Colle.GeneratesAt ξ Sφ a)
    (hSφ : Sφ = d.toDecompData.Sphi)
    (ha_min : ∀ b ∈ Sφ, dot m a ≤ dot m b)
    (ha_end : ∀ b ∈ Sφ, dot m b = dot m a → ∃ t : ℕ, b = a + (t : ℤ) • w)
    (hadj : ∀ y ∈ E (↑d.toDecompData.Sphi : Set (ℤ × ℤ)),
      ¬ InOpenSector 1 (dir w) nl y) :
    ∀ b ∈ Sφ, dot m a < dot m b → dot nl b ≤ dot nl a :=
  hstrict_of_det_gen_onsite d hvlp hwp hperp hdetpos hnu hwneg hmw hmvl hgenφ hSφ
    ha_min ha_end
    (hcrit_of_no_E_between_native d hvlp hwp hperp hdetpos hnu hwneg hmw hmvl hadj)

/-- 八边形台架的 8 个边法向 `(±1,0)` / `(0,±1)` / `(±1,±1)`。

⚠ 这是**数值台架，不是转写**，无原文对应物。数值与 lane-tower-hbase 的 `octGZ`
（`tmp/wip/lane-tower-hbase-sortdir.lean` §27，按 `PROTOCOL.md §53` 不写行号）对得上：
他报的三个 `n.2 < 0` 法向 `(-1,-1)` / `(0,-1)` / `(1,-1)` 及其 `dot n wGZW = 2 / 1 / 0`
我独立重算一致。本文件**不 import 他的文件**，此处独立重列。排序无关：
下面的陈述全是 `∀ i` / `∃ i`。 -/
def foOct : Fin 8 → ℤ × ℤ :=
  ![((1 : ℤ), (0 : ℤ)), ((1 : ℤ), (1 : ℤ)), ((0 : ℤ), (1 : ℤ)), ((-1 : ℤ), (1 : ℤ)),
    ((-1 : ℤ), (0 : ℤ)), ((-1 : ℤ), (-1 : ℤ)), ((0 : ℤ), (-1 : ℤ)), ((1 : ℤ), (-1 : ℤ))]

/-- ⭐ **硬规矩 6 的数值实例：「相邻」与「判据」在两个 `w` 上同步分开。**

台架：`vl = (0,1)`、`nℓ = (1,0)`（`= -dir vl`），法向表 `foOct`。两行只换 `w`：

| 行 | `w` | `dir w` | 判据 `hwadj` | 相邻 `(dir w, nℓ)` |
|---|---|---|---|---|
| N（坏） | `(-1,0)` | `(0,-1)` | **假**，见证 `(1,-1)` | **假**，同一点 `(1,-1)` |
| W（好） | `(-1,-1)` | `(1,-1)` | **真** | **真** |

⟹ 两边在这两个 `w` 上**同步分开**，且 N 行两边的见证是同一个点。

第 5 项是**符号订正的见证**：集成者写的 `(-(dir w), nℓ)` 那版在好 `w` 上为假
（开弧里坐着 `(-1,-1)`），而判据为真 ⟹ 那一版不是本判据的重述。
第 6、7 项确认本节的方向前提 `hpar` / `hpos` 在两行上都成立（`-m = dir w` 逐字取等），
第 8 项确认 `hnl`。

⚠ 口径：本收据在**法向表级**，不构造 `DecompDataZ` 实例；它排除的是「重述与判据脱钩」，
**不是**洞 3 的兑现。 -/
theorem fo_adjacency_tracks_crit :
    (¬ ∀ i, ¬ (dot (foOct i) ((0 : ℤ), (1 : ℤ)) < 0 ∧
        dot (foOct i) ((-1 : ℤ), (0 : ℤ)) < 0)) ∧
    (¬ ∀ i, ¬ InOpenSector 1 (dir ((-1 : ℤ), (0 : ℤ))) ((1 : ℤ), (0 : ℤ)) (foOct i)) ∧
    (∀ i, ¬ (dot (foOct i) ((0 : ℤ), (1 : ℤ)) < 0 ∧
        dot (foOct i) ((-1 : ℤ), (-1 : ℤ)) < 0)) ∧
    (∀ i, ¬ InOpenSector 1 (dir ((-1 : ℤ), (-1 : ℤ))) ((1 : ℤ), (0 : ℤ)) (foOct i)) ∧
    (¬ ∀ i, ¬ InOpenSector 1 (-(dir ((-1 : ℤ), (-1 : ℤ)))) ((1 : ℤ), (0 : ℤ)) (foOct i)) ∧
    (det (-((0 : ℤ), (1 : ℤ))) (dir ((-1 : ℤ), (0 : ℤ))) = 0 ∧
      0 < dot (-((0 : ℤ), (1 : ℤ))) (dir ((-1 : ℤ), (0 : ℤ)))) ∧
    (det (-((-1 : ℤ), (1 : ℤ))) (dir ((-1 : ℤ), (-1 : ℤ))) = 0 ∧
      0 < dot (-((-1 : ℤ), (1 : ℤ))) (dir ((-1 : ℤ), (-1 : ℤ)))) ∧
    ((1 : ℤ), (0 : ℤ)) = -dir ((0 : ℤ), (1 : ℤ)) := by
  refine ⟨?_, ?_, fun i => ?_, fun i => ?_, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · intro h
    have hb := h 7
    revert hb
    simp only [foOct]
    decide
  · intro h
    have hb := h 7
    revert hb
    simp only [foOct, InOpenSector]
    decide
  · fin_cases i <;> simp only [foOct] <;> decide
  · fin_cases i <;> simp only [foOct, InOpenSector] <;> decide
  · intro h
    have hb := h 5
    revert hb
    simp only [foOct, InOpenSector]
    decide
  · decide
  · decide
  · decide
  · decide
  · decide

#print axioms fo_inOpenSector_transfer
#print axioms wadj_iff_no_E_between
#print axioms hcrit_of_no_E_between_native
#print axioms hstrict_of_no_E_between_onsite
#print axioms fo_adjacency_tracks_crit

/-! ## §13. 判据的 `dot` 形态（导出）

`hstrict_iff_det_gen_native` 之后留在 `RegionSteps.lean` 的那条判据是 `det` 形的：
`∀ j, det (h j) vl * det (h j) w ≤ 0`。本节把它导出成等价的 `dot` 形：
`∀ j, dot m (h j) * dot nℓ (h j) ≤ 0`，即**每个生成元上 `dot m` 与 `dot nℓ` 不同号**。

这条等价此前只活在 `wadj_iff_det_gen` 的证明内部（那里的 `hkey`，一条无前提的
2D Plücker 恒等式 ＋ `hpos` ＋ `0 < ‖dir w‖²`）。本节把它提成可引用的 API。

派工出处：集成者 2026-09-24 第 193 轮四条裁决的第 1 条——「导出 `hcrit_iff_dot_form`：做。
只做导出，不碰 `hcrit` 本身」。需求方：lane-towerpkg（塔包手上是 `dot` 型事实，`det` 型
对他们是外语）＋ lane-tower-hbase（前驱构造可直接产 `dot` 形）。

⚠ 这**不是**新的数学内容，是同一条**链侧**判据换一副**链侧**坐标。⛔ 与 §12 同一条口径：
它不减洞 3 一分债——lane-tower-hbase 的 `gZL` 台架上换一个 `w`，两边一起翻。

⛔ **定向口径（lane-towerpkg 2026-09-24 提出，本节采纳并加强）。**
判据 `∀ j, det (h j) vl * det (h j) w ≤ 0` **不是定向无关的**：
`vl ↦ -vl` 或 `w ↦ -w` **单独**翻，整条变成 `≥ 0`；`vl` 与 `w` **一起**翻则原样不变
（翻一个 vs 翻两个——与 §8 `det_form_needs_dir` 同一条规则）。
⟹ 本节那个 `↔` 的**两边都在链侧**（`m` 同时吃 `w` 与 `vl` 的定向），所以 iff 本身安全；
但两边**都不许**被读成「原文那条判据」。§12 的 `hadj` 同理，是**两副链侧坐标**，
不是「与原文同一条」——那需要一条「链上 `vl` ＝ 原文 `v⃗_{ℓ_ι}`」的定向字典，
而那条正是没证的（集成者第 179 轮红线）。本文件与 §12 均**不**依赖该字典：
`InOpenSector` 的 docstring 已逐字注明「无原文对应物」。

⚠ 前提表与 `hstrict_iff_det_gen_native` / `hcrit_of_no_E_between_native` 逐字相同，
没有任何新 binder。

📌 lane-tower-hbase 2026-09-24 报的那条恒等式「`dot nℓ x = det x vl`（在 `nℓ = -(dir vl)` 下）」
本文件**早已内核化**，就是 `fo_dot_neg_dir`（§8）；下面的证明走的是同一条。
他另提的「`j = i` 那格由 `hdoth : dot nℓ (h i) = 0` 白送、量词可缩到 `j ≠ i`」**本节不做**：
`hdoth` 不是 `exists_cutResidualR_of_claim46` 的 binder，拿它当前提会给判据加一条
原文没有的假设（硬规矩 5：比原文强 = 债）。要缩量词请在**有 `hdoth` 的那个消费点**做。 -/

/-- ⭐ **判据的 `dot` 形态。** `det` 形 ⟺ 「每个生成元上 `dot m` 与 `dot nℓ` 不同号」。

左边逐字符是 `RegionSteps.lean` 里 `hstrict_iff_det_gen_native` 之后那条 `sorry` 的目标
（认标识符不认行号）。前提表与 `hstrict_iff_det_gen_native` 完全一致，无新 binder。 -/
theorem hcrit_iff_dot_form {ξ : Config ℤ} (d : DecompDataZ ξ)
    {m nl vl w u' : ℤ × ℤ}
    (hvlp : Primitive vl) (hwp : Primitive w)
    (hperp : dot nl vl = 0) (hdetpos : 0 < det nl vl)
    (hnu : dot nl u' = -1) (hwneg : dot nl w < 0)
    (hmw : dot m w = 0) (hmvl : 0 < dot m vl) :
    (∀ j : Fin d.toDecompData.m,
        det (d.toDecompData.h j) vl * det (d.toDecompData.h j) w ≤ 0) ↔
      (∀ j : Fin d.toDecompData.m,
        dot m (d.toDecompData.h j) * dot nl (d.toDecompData.h j) ≤ 0) := by
  have hw : w ≠ 0 := (prim_iff_primitive.mpr hwp).ne_zero
  have hw0 : w ≠ ((0 : ℤ), (0 : ℤ)) := fun h => hw (by rw [h]; rfl)
  have hpar : det (-m) (dir w) = 0 := fo_det_negm_dir_w_zero hmw
  have hpos := Nivat.LaneTowerPkgNormalPair.negm_pos_dot_dir_w_of_chain hw hvlp hperp
    hdetpos hnu hwneg hmw hmvl
  have hnl := (Nivat.RegionNlDict.nl_eq_neg_dir_vl_and_det_u' hvlp hperp hdetpos hnu).1
  -- `det` 形 ⟺ `hwadj`（§8）
  have h1 := (wadj_iff_det_gen d hw0 hpar hpos hnl).symm
  -- `hwadj` ⟺ 开扇区为空（§8 的 `inOpenSector_iff_wadj_body`，逐点）
  have h2 : (∀ n ∈ E (↑d.toDecompData.Sphi : Set (ℤ × ℤ)),
        ¬ (dot n vl < 0 ∧ dot n w < 0)) ↔
      (∀ y ∈ E (↑d.toDecompData.Sphi : Set (ℤ × ℤ)),
        ¬ InOpenSector 1 (-m) nl y) := by
    constructor
    · intro h y hy hin
      exact h y hy ((inOpenSector_iff_wadj_body hw0 hpar hpos hnl).mp hin)
    · intro h n hn hcon
      exact h n hn ((inOpenSector_iff_wadj_body hw0 hpar hpos hnl).mpr hcon)
  -- 开扇区为空 ⟺ 逐生成元符号一致（§5）
  have h3 := sector_empty_iff_sign_agree d.toDecompData (σ := 1) (Or.inl rfl) (-m) nl
  -- 符号一致 ⟺ `dot` 形（只是把 `-m` 的负号推出来）
  have hneg : ∀ k : Fin d.toDecompData.m,
      dot (-m) (d.toDecompData.h k) * dot nl (d.toDecompData.h k)
        = -(dot m (d.toDecompData.h k) * dot nl (d.toDecompData.h k)) := by
    intro k
    rw [fo_dot_neg_left]
    ring
  constructor
  · intro h j
    have hj := (h3.mp (h2.mp (h1.mp h))) j
    rw [hneg j] at hj
    linarith
  · intro h j
    refine h1.mpr (h2.mpr (h3.mpr ?_)) j
    intro k
    rw [hneg k]
    linarith [h k]

/-- 消费者现场形态的 `dot` 版：前提表 ＝ `hstrict_of_det_gen_onsite` 的，
只把 `hcrit` 换成它的 `dot` 形态。 -/
theorem hstrict_of_dot_form_onsite {ξ : Config ℤ} (d : DecompDataZ ξ)
    {m nl vl w u' a : ℤ × ℤ} {Sφ : Finset (ℤ × ℤ)}
    (hvlp : Primitive vl) (hwp : Primitive w)
    (hperp : dot nl vl = 0) (hdetpos : 0 < det nl vl)
    (hnu : dot nl u' = -1) (hwneg : dot nl w < 0)
    (hmw : dot m w = 0) (hmvl : 0 < dot m vl)
    (hgenφ : Nivat.Colle.GeneratesAt ξ Sφ a)
    (hSφ : Sφ = d.toDecompData.Sphi)
    (ha_min : ∀ b ∈ Sφ, dot m a ≤ dot m b)
    (ha_end : ∀ b ∈ Sφ, dot m b = dot m a → ∃ t : ℕ, b = a + (t : ℤ) • w)
    (hdotcrit : ∀ j : Fin d.toDecompData.m,
      dot m (d.toDecompData.h j) * dot nl (d.toDecompData.h j) ≤ 0) :
    ∀ b ∈ Sφ, dot m a < dot m b → dot nl b ≤ dot nl a :=
  hstrict_of_det_gen_onsite d hvlp hwp hperp hdetpos hnu hwneg hmw hmvl hgenφ hSφ
    ha_min ha_end
    ((hcrit_iff_dot_form d hvlp hwp hperp hdetpos hnu hwneg hmw hmvl).mpr hdotcrit)

#print axioms hcrit_iff_dot_form
#print axioms hstrict_of_dot_form_onsite

end Nivat.LaneTowerHlevFanOrder
