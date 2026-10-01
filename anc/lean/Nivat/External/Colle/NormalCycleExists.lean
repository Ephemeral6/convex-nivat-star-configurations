/-
# `NormalCycleCcw` 的存在性引擎：从「有限 + ±闭 + 两两不平行」造出法向环

lane-tower-hlev，2026-09-24（第 187 轮）。team-lead 第 187 轮裁决 1 批准落主仓，
拆自 `tmp/wip/lane-tower-hlev-periodmatch.lean` 的 §1 / §5.1–§5.2 / §6。

**本文件的 `import` 表（`grep -n "^import"` 可核对，两条）**：
`Nivat.External.Colle.NormalCycle`、`Nivat.External.Colle.TowerConstruct`。
⚠ 文件头自报的 import 表**也会腐烂**（`NormalCycle.lean:4` 本轮刚因此被订正）。
改 import 的人负责同步这一段；照这段读回来的东西必须与 `grep` 一致。

## §0.1  这是什么

`Nivat.LaneTowerHlevNormalCycle.NormalCycle`（`NormalCycle.lean:152`）是 `b3_colle2.txt:319`
＋ `:424` 的索引族转录。它此前**只有台架实例**（正八边形 `ncyOctCycleCcw`）。本文件给出
**一般构造**：任何有限、不含 `0`、对取负封闭、「平行 ⟹ 相等或相反」、且含一对不平行元素的
`N ⊆ ℤ²`，都承载一条 `NormalCycleCcw N m`（`σ = 1`，即逆时针）。

终点是 `exists_ncy_of_set'`（§6.8）：

```
theorem exists_ncy_of_set' {S : Set (ℤ × ℤ)} (hfin : S.Finite)
    (hzero : ∀ n ∈ S, n ≠ 0) (hneg : ∀ n ∈ S, -n ∈ S)
    (hpar : ∀ n ∈ S, ∀ n' ∈ S, det n n' = 0 → n' = n ∨ n' = -n)
    (hnd : ∃ a ∈ S, ∃ b ∈ S, det a b ≠ 0) :
    ∃ m, 2 ≤ m ∧ Nonempty (NormalCycleCcw S m)
```

**不要求消费者给一般位置向量 `e`，不要求消费者排序，不要求 `|S| = 2m`。**

## §0.2  ⛔ 它**不**供什么（team-lead 第 187 轮裁决 1 明文要求写在这里）

1. ⛔ **不供「指标认同」。**「环存在」**不等于**「链上某一对向量是这条环上的相邻对」。
   被反驳的究竟是什么，必须分两层写（`PROTOCOL.md §42` 推论 2：别让文件里的一句话把活路线判死）。

   **(1a) 一族逐对命题。** 对每个具体的 `N` 和每个具体的有序对 `(x, y)`，有**一条**命题：
   「存在 `m` 与 `k`，使某个 `NormalCycleCcw N m` 满足 `(nu k, nu (k+1)) = (x, y)`」。
   lane-tower-hbase 的 `oct_chain_pair_not_cycle_adjacent`
   （`tmp/wip/lane-tower-hbase-sortdir.lean` §20；该文件不在 build 里、每轮加节，
   **一律按名字 `grep`，不要按行号找**）否掉的是这一族里的**一个成员**：`N = oct`、
   `(x, y) = (dir wOct90, nlOct)`。机制是 `(1,-1) ∈ oct` 严格落在那条逆时针开弧里，于是
   `hnoArc`（`NormalCycle.lean:176`）在该 `k` 处为假；这个否证对 `m` 和 `k` 都是全称的。
   该反例**非空真**：`oct_chain_pair_satisfies_mem_and_nz`（同文件 §20）证出被否的只有
   `hnoArc` 一条，`mem` / `ne_zero` 两条前提都真被满足。

   **(1b) 合成一条。** 把 (1a) 那一族对所有 `N` 与所有配对全称量化，得到「指标认同一般成立」。
   (1a) 的一个成员为假**足以**否掉这条全称式 ⟹ **本文件不供它**；谁把本文件读成
   「缺口三的 `hwadj` 有了」，那是读错了。

   ⛔ **(1a) 与 (1b) 不许互相代替。** 特别地，(1a) 那个成员为假**不**等于「指标认同这条路线死了」：
   `oct` 是一座具体八边形、不是链上的 `E ↑d.Sphi`；被否的配对是 `(dir wOct90, nlOct)`，而
   `sortdir` §21 把订正后的配对写成 `(νJ1, +nℓ)`，那是**另一个**成员；「先判定哪一对相邻、
   再用那一对」这条读法本条一个字都没碰。⟹ 链上真正需要的成员
   （`N = E ↑d.Sphi`、链上那一对）本文件与上述反例**都不表态**，按 `PROTOCOL.md §71`(i)
   记「**未定**」，**不记「为假」，也不记「零贡献」**。
2. ⛔ **不供 `m = d.m`。** 这里的 `m` 是「上半圈的基数」，`:319` 的计数 `|E(𝒮_φ)| = 2m`
   **没有**被证明，也**没有**被使用（见 §0.3）。
3. ⛔ **不供 `E B = E ↑d.Sphi`。** 本文件输入是抽象 `Set` / `Finset`，对链上洞 3 的
   「`Sφ` 是不是 `d.Sphi`」不表态。`DecompData.lean:115-123` 明写 Agreement 字段
   2026-09-17 已删 ⟹ `E B` 与 `E ↑d.Sphi` **不得默认同集**；唯一合法通道是
   `Nivat.LE2.Enveloped.E_eq`，要 `EnvOf (↑d.Sphi) B` ＋ `(E ↑d.Sphi).Finite`
   （后者由 `Nivat.LE2.finite_E_of_finite d.Sphi.finite_toSet` 白送）。

## §0.3  `anti` 的债：±-闭包不是我们加的量词

按硬规矩 5 问「哪个量词是我们加的」：

* **±-闭包不是。** `Nivat.Colle35.Sphi_negSymm`（`DecompData.lean:417`）是**无条件** `↔`，
  docstring 逐字「only the field `h_ne` is used」。
* **我们加的是「对径映射恰好是下标平移 `m`」**（`NormalCycle.lean` 的转录债表已登记）。
  本文件把这条债**还掉**：`angCyc_anti`（§6.7）不靠任何几何输入，是 `angCyc` 定义分支的
  直接推论。

⭐ 另有一条口径收窄：`two_le_angUpper_card`（§6.5）表明 `2 ≤ m` **只需要**「存在一对不平行
元素」，**不需要** `|E(𝒮_φ)| = 2m`。⟹ `:319` 的计数在这条线上整个被摘掉了。

## §0.4  为什么不需要「整圈排序引擎」

主仓两台排序引擎的定义域都 < 180°（`dot_of_mem_candSet`，`TowerConstruct.lean:287`；
`LeafAJSelect.exists_fan_pred_cw`，`:943`），「造不出整圈序」曾被当成拦路虎。本文件的办法是
**不需要整圈序**：取一个与 `N` 中每个向量都不垂直的 `e`（`exists_gen_position`，§6.8，纯
ℤ-算术鸽笼，不用几何），`N` 按 `dot e ·` 的号一分为二，两半互为相反数；**只排
`dot e · > 0` 的那半**——那正是 `Nivat.ColleReg.keyOf e`（`TowerConstruct.lean:183`）合法且
与 `det` 单调的开半平面（`det_pos_iff_key_lt`，`:191`）。另一半用 `anti` 复制过去，于是
`nu (k+m) = -(nu k)` **按定义**成立。

⚠ 本文件**复用**主仓的 `keyOf` / `det_pos_iff_key_lt`，不重造。

## §0.5  `hnoArc` 是排序的副产品

`hnoArc` 在这里不是额外输入：`N` 可穷举 ⟹ 任意 `y ∈ N` 都等于某个 `angAt t` 或
`-(angAt t)`，于是「`y` 落在相邻两条之间」化成一条 `ℕ` 下标的不等式矛盾
（`angCyc_noArc_lt`，§6.7）。两条弧都自己算，不从扇的任何一侧借，故不受
「互补弧 `Arc J νJ1 = ∅`」那个负号陷阱影响。

## §0.6  法向侧 / 方向侧（team-lead 第 187 轮裁决 3）

本文件**整体在法向侧**：`N` 的元素是**边法向**（主仓 `LatticeEdges.lean:217` 的 `E` 口径，
`genPerp' (h j) ⊥ h j`）。原文 `:319` 的「`w` 平行于某个 `h_i`」说的是**方向侧**，差一个
`dir`（逆时针 90°）。⟹ 引用本文件时必须标明是哪一侧；方向侧的对应物本文件**不供**。

## §0.7  台架（硬规矩 6）

§6.9 在 `N = {±(1,0), ±(0,1)}`、`m = 2` 上把四条前提全部内核 `decide`，说明
`exists_ncy_of_finset` 的前提包**不是空真**。
-/

import Nivat.External.Colle.NormalCycle
import Nivat.External.Colle.TowerConstruct

set_option autoImplicit false

namespace Nivat.NormalCycleExists

open Nivat Nivat.LE2 Nivat.LaneTowerHlevNormalCycle


/-! ## §1  二维平行性的整数算术

三条纯代数引理，都由一个**无条件的**多项式恒等式加 `ring` 得到，不用 `nlinarith`、
不用素性、不用 `Primitive`。 -/

/-- `n ≠ 0` 拆成坐标。 -/
theorem pm_ne_zero_cases {n : ℤ × ℤ} (h : n ≠ 0) : n.1 ≠ 0 ∨ n.2 ≠ 0 := by
  by_contra hc
  simp only [not_or, not_not] at hc
  exact h (Prod.ext hc.1 hc.2)

/-- **同垂直于一个非零向量的两个向量平行。**

恒等式（无条件）：
`(n.1² + n.2²) * det x y = (dot n x) * (n.1*y.2 − n.2*y.1) − (dot n y) * (n.1*x.2 − n.2*x.1)`。 -/
theorem pm_det_eq_zero_of_perp {n x y : ℤ × ℤ} (hn : n ≠ 0)
    (hx : dot n x = 0) (hy : dot n y = 0) : det x y = 0 := by
  have key : (n.1 * n.1 + n.2 * n.2) * det x y =
      (dot n x) * (n.1 * y.2 - n.2 * y.1) - (dot n y) * (n.1 * x.2 - n.2 * x.1) := by
    simp only [dot, det]; ring
  rw [hx, hy] at key
  simp only [zero_mul, sub_self] at key
  have hpos : 0 < n.1 * n.1 + n.2 * n.2 := by
    rcases pm_ne_zero_cases hn with h | h
    · nlinarith [mul_self_nonneg n.2, mul_self_pos.mpr h]
    · nlinarith [mul_self_nonneg n.1, mul_self_pos.mpr h]
  rcases mul_eq_zero.mp key with h | h
  · exact absurd h (ne_of_gt hpos)
  · exact h

/-- **垂直关系沿平行方向传递。**

恒等式（无条件）：
`n.1 * dot n' x = n'.1 * dot n x + x.2 * det n n'`，
`n.2 * dot n' x = n'.2 * dot n x − x.1 * det n n'`。 -/
theorem pm_dot_of_par {n n' x : ℤ × ℤ} (hn : n ≠ 0) (hpar : det n n' = 0)
    (hx : dot n x = 0) : dot n' x = 0 := by
  have k1 : n.1 * dot n' x = n'.1 * dot n x + x.2 * det n n' := by
    simp only [dot, det]; ring
  have k2 : n.2 * dot n' x = n'.2 * dot n x - x.1 * det n n' := by
    simp only [dot, det]; ring
  rw [hx, hpar] at k1 k2
  simp only [mul_zero, add_zero, sub_self] at k1 k2
  rcases pm_ne_zero_cases hn with h | h
  · exact (mul_eq_zero.mp k1).resolve_left h
  · exact (mul_eq_zero.mp k2).resolve_left h

/-! ## §5  `indep` 的下标归约与 smart constructor

把 `NormalCycle.indep`（量化全体 `k`）换成 `hpair`（只量化 `1 ≤ i,j ≤ m`），
后者正是原文 `:424` / `:764` 的字面范围。 -/

section SmartCtorCore

variable {nu : ℕ → ℤ × ℤ} {M : ℕ}

theorem pm_det_neg_neg (a b : ℤ × ℤ) : det (-a) (-b) = det a b := by
  rw [ncy_det_neg_left, ncy_det_neg_right, neg_neg]

/-- **把两个下标同时推进一个周期 `m`，`det` 不变**：两边各变一次号，正好抵消。
这一条是全部归约的唯一引擎，只用 `anti`。 -/
theorem pm_det_shift (anti : ∀ k, nu (k + M) = -(nu k)) (k s : ℕ) :
    det (nu (k + M)) (nu (k + M + s)) = det (nu k) (nu (k + s)) := by
  have he : k + M + s = (k + s) + M := by omega
  rw [he, anti k, anti (k + s), pm_det_neg_neg]

/-- **`[1,m]` 区间上的 `indep`**：把 `(r, r+s)` 拆成两种情形。

* `r + s ≤ m`：两个下标都已在 `[1,m]`，直接用假设；
* `r + s > m`：令 `u := r+s-m`，由 `anti` 得 `nu (r+s) = -(nu u)`，`det` 变号但不变零性，
  而 `u ∈ [1,m]`。`r ≠ u` 恰好等价于 `s ≠ m`——**这就是 `indep` 的上界 `s < m` 在
  归约里真正被用到的地方**，也正是 `det_at_m`（`NormalCycle.lean:195`）那条边界的另一面。 -/
theorem pm_indep_range (anti : ∀ k, nu (k + M) = -(nu k))
    (hpair : ∀ i j, 1 ≤ i → i ≤ M → 1 ≤ j → j ≤ M → i ≠ j → det (nu i) (nu j) ≠ 0)
    (r s : ℕ) (hr1 : 1 ≤ r) (hrm : r ≤ M) (hs1 : 1 ≤ s) (hsm : s < M) :
    det (nu r) (nu (r + s)) ≠ 0 := by
  by_cases hle : r + s ≤ M
  · exact hpair r (r + s) hr1 hrm (by omega) hle (by omega)
  · obtain ⟨u, hu⟩ : ∃ u, r + s = u + M := ⟨r + s - M, by omega⟩
    rw [hu, anti u, ncy_det_neg_right, ne_eq, neg_eq_zero]
    exact hpair r u hr1 hrm (by omega) (by omega) (by omega)

/-- **全指标 `indep`**，由 `[1,m]` 上的配对推出。对 `k` 强归纳：

* `k > m`：写 `k = j + m`，`pm_det_shift` 把它降到 `j < k`，用归纳假设；
* `1 ≤ k ≤ m`：直接是 `pm_indep_range`；
* `k = 0`：`pm_det_shift` 反着用一次，换成 `r := m`（`m ∈ [1,m]`），再用 `pm_indep_range`。

⚠ 全程**没有除法、没有 `%`**，所以不碰「`omega` 看不穿变量模数」那个坑。 -/
theorem pm_indep_full (hm : 2 ≤ M) (anti : ∀ k, nu (k + M) = -(nu k))
    (hpair : ∀ i j, 1 ≤ i → i ≤ M → 1 ≤ j → j ≤ M → i ≠ j → det (nu i) (nu j) ≠ 0)
    (k s : ℕ) (hs1 : 1 ≤ s) (hsm : s < M) :
    det (nu k) (nu (k + s)) ≠ 0 := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    by_cases hle : k ≤ M
    · rcases Nat.eq_zero_or_pos k with rfl | hpos
      · have h0 := pm_det_shift anti 0 s
        simp only [Nat.zero_add] at h0 ⊢
        rw [← h0]
        exact pm_indep_range anti hpair M s (by omega) (le_refl M) hs1 hsm
      · exact pm_indep_range anti hpair k s hpos hle hs1 hsm
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + M := ⟨k - M, by omega⟩
      rw [pm_det_shift anti]
      exact ih j (by omega)

/-! ### §5.2  构造器 -/

/-- **`NormalCycleCcw` 的 smart constructor：`indep` 不用外部提供。**

⚠ **与「锁死债表」不冲突**：主仓 `NormalCycle.lean` 未改，`indep` 仍是字段、债表原样。
本条只是多一条造法——把 `indep`（量化全体 `k`）换成 `hpair`（只量化 `1 ≤ i,j ≤ m`），
后者正是原文 `:424`/`:764` 的字面范围。

⚠ **`hnoArc` 仍要外部提供，这是本构造器的真正缺口**；§6 的 `ncyOfAngDataCard` 把它补上
（`angCyc_noArc`），代价是那条环必须由本文件的排序造出来，不能是外来的 `nu`。 -/
def ncyCcwOfPair {N : Set (ℤ × ℤ)} (nu : ℕ → ℤ × ℤ) (M : ℕ)
    (hm : 2 ≤ M)
    (mem : ∀ k, nu k ∈ N)
    (ne_zero : ∀ k, nu k ≠ 0)
    (anti : ∀ k, nu (k + M) = -(nu k))
    (step : ∀ k, 0 < det (nu k) (nu (k + 1)))
    (hnoArc : ∀ k, ∀ y ∈ N, ¬ (0 < det (nu k) y ∧ 0 < det y (nu (k + 1))))
    (hpair : ∀ i j, 1 ≤ i → i ≤ M → 1 ≤ j → j ≤ M → i ≠ j → det (nu i) (nu j) ≠ 0) :
    NormalCycleCcw N M where
  hm := hm
  hsigma := Or.inl rfl
  nu := nu
  mem := mem
  ne_zero := ne_zero
  anti := anti
  step := fun k => by rw [one_mul]; exact step k
  hnoArc := fun k y hy => by simpa only [one_mul] using hnoArc k y hy
  indep := fun k s hs1 hsm => pm_indep_full hm anti hpair k s hs1 hsm

end SmartCtorCore

section AngBuild

variable {N : Finset (ℤ × ℤ)} {e : ℤ × ℤ}

/-! ### §6.5  角序比较器与半平面 -/

/-- 角序布尔比较器：按主仓的 `Nivat.ColleReg.keyOf e`（`TowerConstruct.lean:183`）升序。
`≤` 在 `ℚ` 上无条件传递且全序，所以 `mergeSort` 的两条假设是现成的（与
`TowerConstruct.lean:231-237` 的 `leKey` 同一套路；那条按 `keyOf (-nℓ)` 排，这条按 `keyOf e` 排，
故不能直接复用）。 -/
noncomputable def leAng (e a b : ℤ × ℤ) : Bool :=
  decide (Nivat.ColleReg.keyOf e a ≤ Nivat.ColleReg.keyOf e b)

theorem leAng_trans (e : ℤ × ℤ) : ∀ a b c, leAng e a b → leAng e b c → leAng e a c := by
  intro a b c hab hbc
  simp only [leAng, decide_eq_true_eq] at hab hbc ⊢
  exact le_trans hab hbc

theorem leAng_total (e : ℤ × ℤ) : ∀ a b, leAng e a b || leAng e b a := by
  intro a b
  simp only [leAng, decide_eq_true_eq, Bool.or_eq_true]
  exact le_total _ _

/-- 造环的全部输入。**四条都不是几何假设**：`he`/`hgen` 只说 `e` 与 `N` 处于一般位置
（`exists_gen_position` 无条件给得出），`hneg` 是 `:319` 的 ±-对称（`Sphi_negSymm` 无条件），
`hpar` 是 `:424`「pairwise distinct directions」＋ `:319`「`2m` 条边恰是 `m` 对 `±`」。 -/
structure AngData (N : Finset (ℤ × ℤ)) (e : ℤ × ℤ) : Prop where
  /-- `e` 非零：`keyOf e` 与 `det` 单调所需（`det_pos_iff_key_lt` 的第一个前提）。 -/
  he : e ≠ 0
  /-- 一般位置：`N` 里没有与 `e` 垂直的向量。由 `exists_gen_position` 提供。 -/
  hgen : ∀ n ∈ N, dot e n ≠ 0
  /-- `b3_colle2.txt:319`「`|E(𝒮_φ)| = 2m`，每个 `w` 平行或反平行于某个 `h_i`」的 ± 那半。 -/
  hneg : ∀ n ∈ N, -n ∈ N
  /-- `b3_colle2.txt:424`「pairwise distinct directions」：`N` 里平行只能是相等或相反。 -/
  hpar : ∀ n ∈ N, ∀ n' ∈ N, det n n' = 0 → n' = n ∨ n' = -n

theorem ang_dot_neg (a b : ℤ × ℤ) : dot a (-b) = - dot a b := by
  simp only [dot, Prod.fst_neg, Prod.snd_neg]; ring

theorem ang_ne_zero (A : AngData N e) {n : ℤ × ℤ} (hn : n ∈ N) : n ≠ 0 := by
  rintro rfl
  exact A.hgen 0 hn (by simp [dot])

/-- `dot e · > 0` 的那一半。只排这半圈——`keyOf e` 的合法定义域。 -/
noncomputable def angUpper (N : Finset (ℤ × ℤ)) (e : ℤ × ℤ) : Finset (ℤ × ℤ) :=
  N.filter (fun n => 0 < dot e n)

theorem mem_angUpper {v : ℤ × ℤ} : v ∈ angUpper N e ↔ v ∈ N ∧ 0 < dot e v :=
  Finset.mem_filter

/-- 另一半。 -/
noncomputable def angLower (N : Finset (ℤ × ℤ)) (e : ℤ × ℤ) : Finset (ℤ × ℤ) :=
  N.filter (fun n => dot e n < 0)

theorem angLower_eq_image (A : AngData N e) :
    angLower N e = (angUpper N e).image (fun n => -n) := by
  ext x
  simp only [angLower, angUpper, Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨hx, hlt⟩
    refine ⟨-x, ⟨A.hneg x hx, ?_⟩, neg_neg x⟩
    rw [ang_dot_neg]; omega
  · rintro ⟨y, ⟨hy, hpos⟩, rfl⟩
    refine ⟨A.hneg y hy, ?_⟩
    rw [ang_dot_neg]; omega

/-- **`:319` 的「一半」形式**：`|N| = 2 · |上半|`。消费者据此把 `|N| = 2m` 换成 `|上半| = m`。 -/
theorem angN_card (A : AngData N e) : N.card = 2 * (angUpper N e).card := by
  have hdisj : Disjoint (angUpper N e) (angLower N e) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    rw [angUpper, Finset.mem_filter] at ha
    rw [angLower, Finset.mem_filter] at hb
    omega
  have hunion : angUpper N e ∪ angLower N e = N := by
    ext x
    simp only [Finset.mem_union, angUpper, angLower, Finset.mem_filter]
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · intro hx
      have hne := A.hgen x hx
      rcases lt_trichotomy (dot e x) 0 with h | h | h
      · exact Or.inr ⟨hx, h⟩
      · exact absurd h hne
      · exact Or.inl ⟨hx, h⟩
  have hsum : (angUpper N e ∪ angLower N e).card
      = (angUpper N e).card + (angLower N e).card :=
    Finset.card_union_of_disjoint hdisj
  have hlow : (angLower N e).card = (angUpper N e).card := by
    rw [angLower_eq_image A, Finset.card_image_of_injective _ neg_injective]
  have hfin : N.card = (angUpper N e).card + (angLower N e).card := by
    rw [← hsum, hunion]
  omega

/-- 每个 `n ∈ N` 都有唯一代表落在上半圈。 -/
theorem angUpper_mem_of_mem (A : AngData N e) {a : ℤ × ℤ} (ha : a ∈ N) :
    (if 0 < dot e a then a else -a) ∈ angUpper N e := by
  by_cases h : 0 < dot e a
  · rw [if_pos h]; exact mem_angUpper.mpr ⟨ha, h⟩
  · rw [if_neg h]
    refine mem_angUpper.mpr ⟨A.hneg a ha, ?_⟩
    have hne := A.hgen a ha
    rw [ang_dot_neg]; omega

/-- **`2 ≤ m` 不需要 `:319` 的计数**：`N` 里只要有一对不平行的元素就够了。
⟹ 整台引擎对「`|E(𝒮_φ)| = 2m`」**零依赖**（那条仅用于给 `m` 起名，见 §6.8 的
`exists_ncy_of_set'`）。 -/
theorem two_le_angUpper_card (A : AngData N e) {a b : ℤ × ℤ} (ha : a ∈ N) (hb : b ∈ N)
    (hab : det a b ≠ 0) : 2 ≤ (angUpper N e).card := by
  have hA := angUpper_mem_of_mem A ha
  have hB := angUpper_mem_of_mem A hb
  have hne : (if 0 < dot e a then a else -a) ≠ (if 0 < dot e b then b else -b) := by
    intro hcon
    refine hab ?_
    by_cases h1 : 0 < dot e a <;> by_cases h2 : 0 < dot e b
    · rw [if_pos h1, if_pos h2] at hcon
      rw [hcon, ncy_det_self]
    · rw [if_pos h1, if_neg h2] at hcon
      rw [hcon, ncy_det_neg_left, ncy_det_self, neg_zero]
    · rw [if_neg h1, if_pos h2] at hcon
      rw [← hcon, ncy_det_neg_right, ncy_det_self, neg_zero]
    · rw [if_neg h1, if_neg h2] at hcon
      rw [neg_injective hcon, ncy_det_self]
  exact Finset.one_lt_card.mpr ⟨_, hA, _, hB, hne⟩

/-! ### §6.6  半圈排序 -/
/-- 上半圈按角序排好的表。 -/
noncomputable def angList (N : Finset (ℤ × ℤ)) (e : ℤ × ℤ) : List (ℤ × ℤ) :=
  (angUpper N e).toList.mergeSort (leAng e)

theorem angList_length : (angList N e).length = (angUpper N e).card := by
  simp only [angList, List.length_mergeSort, Finset.length_toList]

theorem mem_angList {v : ℤ × ℤ} : v ∈ angList N e ↔ v ∈ angUpper N e := by
  rw [← Finset.mem_toList]
  exact (List.mergeSort_perm _ _).mem_iff

theorem angList_nodup : (angList N e).Nodup :=
  (List.mergeSort_perm _ _).nodup_iff.mpr (Finset.nodup_toList _)

theorem angList_pairwise : (angList N e).Pairwise (fun a b => leAng e a b = true) := by
  have h := List.pairwise_mergeSort (le := leAng e) (leAng_trans e) (leAng_total e)
    ((angUpper N e).toList)
  simpa [angList] using h

/-- 第 `k` 项（越界给垃圾值 `0`，下面所有引理都带 `k < |上半|`）。 -/
noncomputable def angAt (N : Finset (ℤ × ℤ)) (e : ℤ × ℤ) (k : ℕ) : ℤ × ℤ :=
  (angList N e).getD k 0

theorem angAt_eq_getElem {k : ℕ} (hk : k < (angUpper N e).card) :
    angAt N e k = (angList N e)[k]'(by rw [angList_length]; exact hk) := by
  have hk' : k < (angList N e).length := by rw [angList_length]; exact hk
  simp [angAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk']

theorem angAt_mem {k : ℕ} (hk : k < (angUpper N e).card) : angAt N e k ∈ angUpper N e := by
  rw [angAt_eq_getElem hk]
  exact mem_angList.mp (List.getElem_mem _)

theorem angAt_memN {k : ℕ} (hk : k < (angUpper N e).card) : angAt N e k ∈ N :=
  (mem_angUpper.mp (angAt_mem hk)).1

theorem angAt_dot_pos {k : ℕ} (hk : k < (angUpper N e).card) : 0 < dot e (angAt N e k) :=
  (mem_angUpper.mp (angAt_mem hk)).2

theorem angAt_key_le {r s : ℕ} (hrs : r < s) (hs : s < (angUpper N e).card) :
    Nivat.ColleReg.keyOf e (angAt N e r) ≤ Nivat.ColleReg.keyOf e (angAt N e s) := by
  have hr : r < (angUpper N e).card := lt_trans hrs hs
  have hr' : r < (angList N e).length := by rw [angList_length]; exact hr
  have hs' : s < (angList N e).length := by rw [angList_length]; exact hs
  have h := List.pairwise_iff_getElem.mp (angList_pairwise (N := N) (e := e)) r s hr' hs' hrs
  rw [angAt_eq_getElem hr, angAt_eq_getElem hs]
  simpa [leAng] using h

theorem angAt_ne {r s : ℕ} (hr : r < (angUpper N e).card) (hs : s < (angUpper N e).card)
    (hrs : r ≠ s) : angAt N e r ≠ angAt N e s := by
  have hr' : r < (angList N e).length := by rw [angList_length]; exact hr
  have hs' : s < (angList N e).length := by rw [angList_length]; exact hs
  intro hcon
  exact hrs ((List.getD_inj hr' hs' (angList_nodup (N := N) (e := e))).mp hcon)

/-- 上半圈内两两不平行：`hpar` 的另一支（`n' = -n`）被 `dot e ·` 的号排除。 -/
theorem angAt_det_ne_zero (A : AngData N e) {r s : ℕ} (hr : r < (angUpper N e).card)
    (hs : s < (angUpper N e).card) (hrs : r ≠ s) : det (angAt N e r) (angAt N e s) ≠ 0 := by
  intro h0
  rcases A.hpar _ (angAt_memN hr) _ (angAt_memN hs) h0 with h | h
  · exact angAt_ne hr hs hrs h.symm
  · have h1 := angAt_dot_pos (N := N) (e := e) hr
    have h2 := angAt_dot_pos (N := N) (e := e) hs
    rw [h, ang_dot_neg] at h2
    omega

/-- **排序的几何内容**：下标序 ⟹ `det` 正。 -/
theorem angAt_det_pos (A : AngData N e) {r s : ℕ} (hrs : r < s)
    (hs : s < (angUpper N e).card) : 0 < det (angAt N e r) (angAt N e s) := by
  have hr : r < (angUpper N e).card := lt_trans hrs hs
  have hne := angAt_det_ne_zero A hr hs (by omega)
  rcases lt_trichotomy (det (angAt N e r) (angAt N e s)) 0 with h | h | h
  · exfalso
    have hsk : det (angAt N e s) (angAt N e r) = - det (angAt N e r) (angAt N e s) := by
      simp only [det]; ring
    have hpos : 0 < det (angAt N e s) (angAt N e r) := by omega
    have hlt := (Nivat.ColleReg.det_pos_iff_key_lt A.he (angAt_dot_pos hs)
      (angAt_dot_pos hr)).mp hpos
    exact absurd (angAt_key_le (N := N) (e := e) hrs hs) (not_le.mpr hlt)
  · exact absurd h hne
  · exact h

/-- 反过来也成立：`det` 正 ⟺ 下标序。整节的下标记账全靠这条。 -/
theorem angAt_det_pos_iff (A : AngData N e) {r s : ℕ} (hr : r < (angUpper N e).card)
    (hs : s < (angUpper N e).card) :
    0 < det (angAt N e r) (angAt N e s) ↔ r < s := by
  constructor
  · intro h
    rcases lt_trichotomy r s with h1 | h1 | h1
    · exact h1
    · exfalso; rw [h1, ncy_det_self] at h; omega
    · exfalso
      have hp := angAt_det_pos A h1 hr
      have hsk : det (angAt N e s) (angAt N e r) = - det (angAt N e r) (angAt N e s) := by
        simp only [det]; ring
      omega
  · intro h; exact angAt_det_pos A h hs

/-- 上半圈的枚举是满的：`hnoArc` 把 `∀ y ∈ N` 收成有限下标检查，全靠这条。 -/
theorem angAt_surj {n : ℤ × ℤ} (hn : n ∈ angUpper N e) :
    ∃ k, k < (angUpper N e).card ∧ angAt N e k = n := by
  obtain ⟨k, hk, hkn⟩ := List.getElem_of_mem (mem_angList.mpr hn)
  have hk' : k < (angUpper N e).card := by rw [← angList_length]; exact hk
  exact ⟨k, hk', by rw [angAt_eq_getElem hk']; exact hkn⟩

/-! ### §6.7  整圈：下半圈由 `anti` 复制 -/

/-- 整圈枚举。前 `m` 项是排好序的上半圈，后 `m` 项是它们的相反数，下标模 `2m`。
⚠ **`anti` 在这里是定义的分支结构，不是新假设**——这正是 §6.1 要还的那条债。 -/
noncomputable def angCyc (N : Finset (ℤ × ℤ)) (e : ℤ × ℤ) (k : ℕ) : ℤ × ℤ :=
  if k % (2 * (angUpper N e).card) < (angUpper N e).card
  then angAt N e (k % (2 * (angUpper N e).card))
  else -(angAt N e (k % (2 * (angUpper N e).card) - (angUpper N e).card))

theorem angCyc_lt {r : ℕ} (hr : r < (angUpper N e).card) : angCyc N e r = angAt N e r := by
  have hlt : r < 2 * (angUpper N e).card := by omega
  simp only [angCyc, Nat.mod_eq_of_lt hlt]
  rw [if_pos hr]

theorem angCyc_ge {r : ℕ} (h1 : (angUpper N e).card ≤ r) (h2 : r < 2 * (angUpper N e).card) :
    angCyc N e r = -(angAt N e (r - (angUpper N e).card)) := by
  simp only [angCyc, Nat.mod_eq_of_lt h2]
  rw [if_neg (by omega : ¬ r < (angUpper N e).card)]

theorem angCyc_period (k : ℕ) :
    angCyc N e (k + 2 * (angUpper N e).card) = angCyc N e k := by
  simp only [angCyc, Nat.add_mod_right]

theorem angCyc_memN (A : AngData N e) (hm : 2 ≤ (angUpper N e).card) (k : ℕ) :
    angCyc N e k ∈ N := by
  have hpos : 0 < 2 * (angUpper N e).card := by omega
  have hr : k % (2 * (angUpper N e).card) < 2 * (angUpper N e).card := Nat.mod_lt _ hpos
  by_cases h : k % (2 * (angUpper N e).card) < (angUpper N e).card
  · rw [show angCyc N e k = angAt N e (k % (2 * (angUpper N e).card)) by
      simp only [angCyc]; rw [if_pos h]]
    exact angAt_memN h
  · rw [show angCyc N e k
        = -(angAt N e (k % (2 * (angUpper N e).card) - (angUpper N e).card)) by
      simp only [angCyc]; rw [if_neg h]]
    exact A.hneg _ (angAt_memN (by omega))

theorem angCyc_ne_zero (A : AngData N e) (hm : 2 ≤ (angUpper N e).card) (k : ℕ) :
    angCyc N e k ≠ 0 :=
  ang_ne_zero A (angCyc_memN A hm k)

/-- **`anti`**：对径 ＝ 下标平移 `m`。纯 `ℕ` 取模算术，不用任何几何输入。 -/
theorem angCyc_anti (hm : 2 ≤ (angUpper N e).card) (k : ℕ) :
    angCyc N e (k + (angUpper N e).card) = -(angCyc N e k) := by
  have hpos : 0 < 2 * (angUpper N e).card := by omega
  have hr : k % (2 * (angUpper N e).card) < 2 * (angUpper N e).card := Nat.mod_lt _ hpos
  have hkey : (k + (angUpper N e).card) % (2 * (angUpper N e).card)
      = (k % (2 * (angUpper N e).card) + (angUpper N e).card)
        % (2 * (angUpper N e).card) := by
    rw [Nat.add_mod k (angUpper N e).card,
      Nat.mod_eq_of_lt (by omega : (angUpper N e).card < 2 * (angUpper N e).card)]
  have hmodk : angCyc N e k = angCyc N e (k % (2 * (angUpper N e).card)) := by
    simp only [angCyc, Nat.mod_mod_of_dvd k (dvd_refl (2 * (angUpper N e).card))]
  have hmodk2 : angCyc N e (k + (angUpper N e).card)
      = angCyc N e ((k % (2 * (angUpper N e).card) + (angUpper N e).card)
        % (2 * (angUpper N e).card)) := by
    simp only [angCyc, ← hkey,
      Nat.mod_mod_of_dvd (k + (angUpper N e).card) (dvd_refl (2 * (angUpper N e).card))]
  rw [hmodk, hmodk2]
  obtain ⟨r, hrdef⟩ : ∃ r, k % (2 * (angUpper N e).card) = r := ⟨_, rfl⟩
  rw [hrdef] at hr ⊢
  by_cases h : r < (angUpper N e).card
  · rw [Nat.mod_eq_of_lt (by omega : r + (angUpper N e).card < 2 * (angUpper N e).card),
      angCyc_ge (by omega) (by omega), angCyc_lt h, Nat.add_sub_cancel]
  · rw [show r + (angUpper N e).card
        = (r - (angUpper N e).card) + 2 * (angUpper N e).card by omega,
      Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega : r - (angUpper N e).card < 2 * (angUpper N e).card),
      angCyc_lt (by omega : r - (angUpper N e).card < (angUpper N e).card),
      angCyc_ge (by omega) hr, neg_neg]

/-- **`step`** 在前半圈。两支：内部相邻由排序给，`r + 1 = m` 的接缝由 `anti` 给。 -/
theorem angCyc_step_lt (A : AngData N e) (hm : 2 ≤ (angUpper N e).card)
    {r : ℕ} (hr : r < (angUpper N e).card) :
    0 < det (angCyc N e r) (angCyc N e (r + 1)) := by
  by_cases h : r + 1 < (angUpper N e).card
  · rw [angCyc_lt hr, angCyc_lt h]
    exact angAt_det_pos A (by omega) h
  · have hrM : r + 1 = (angUpper N e).card := by omega
    rw [angCyc_lt hr, hrM, angCyc_ge (le_refl _) (by omega), Nat.sub_self, ncy_det_neg_right]
    have h0 : 0 < det (angAt N e 0) (angAt N e r) := angAt_det_pos A (by omega) hr
    have hsk : det (angAt N e 0) (angAt N e r) = - det (angAt N e r) (angAt N e 0) := by
      simp only [det]; ring
    omega

/-- **`step`**，全体 `k`：周期 `2m` 降一次，`anti` 降一次，剩下就是 `angCyc_step_lt`。 -/
theorem angCyc_step (A : AngData N e) (hm : 2 ≤ (angUpper N e).card) (k : ℕ) :
    0 < det (angCyc N e k) (angCyc N e (k + 1)) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    by_cases h2 : 2 * (angUpper N e).card ≤ k
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 * (angUpper N e).card :=
        ⟨k - 2 * (angUpper N e).card, by omega⟩
      have e2 : angCyc N e (j + 2 * (angUpper N e).card + 1) = angCyc N e (j + 1) := by
        rw [show j + 2 * (angUpper N e).card + 1 = (j + 1) + 2 * (angUpper N e).card by omega,
          angCyc_period]
      rw [angCyc_period j, e2]
      exact ih j (by omega)
    · by_cases h1 : k < (angUpper N e).card
      · exact angCyc_step_lt A hm h1
      · obtain ⟨j, rfl⟩ : ∃ j, k = j + (angUpper N e).card :=
          ⟨k - (angUpper N e).card, by omega⟩
        have e2 : angCyc N e (j + (angUpper N e).card + 1) = -(angCyc N e (j + 1)) := by
          rw [show j + (angUpper N e).card + 1 = (j + 1) + (angUpper N e).card by omega,
            angCyc_anti hm]
        rw [angCyc_anti hm j, e2, pm_det_neg_neg]
        exact angCyc_step_lt A hm (by omega)

/-- **`hnoArc`** 在前半圈。`y` 先被 `angAt_surj` 分成 `angAt t` / `-(angAt t)` 两型，
再由 `angAt_det_pos_iff` 化成 `ℕ` 下标的不等式矛盾。 -/
theorem angCyc_noArc_lt (A : AngData N e) (hm : 2 ≤ (angUpper N e).card)
    {r : ℕ} (hr : r < (angUpper N e).card) :
    ∀ y ∈ N, ¬ (0 < det (angCyc N e r) y ∧ 0 < det y (angCyc N e (r + 1))) := by
  rintro y hy ⟨hy1, hy2⟩
  have hyne : dot e y ≠ 0 := A.hgen y hy
  obtain ⟨t, ht, hyt⟩ :
      ∃ t, t < (angUpper N e).card ∧ (y = angAt N e t ∨ y = -(angAt N e t)) := by
    rcases lt_trichotomy (dot e y) 0 with h | h | h
    · obtain ⟨t, ht, hty⟩ :=
        angAt_surj ((mem_angUpper (N := N) (e := e)).mpr
          ⟨A.hneg y hy, by rw [ang_dot_neg]; omega⟩)
      exact ⟨t, ht, Or.inr (by rw [hty, neg_neg])⟩
    · exact absurd h hyne
    · obtain ⟨t, ht, hty⟩ := angAt_surj ((mem_angUpper (N := N) (e := e)).mpr ⟨hy, h⟩)
      exact ⟨t, ht, Or.inl hty.symm⟩
  rw [angCyc_lt hr] at hy1
  by_cases hrM : r + 1 < (angUpper N e).card
  · rw [angCyc_lt hrM] at hy2
    rcases hyt with rfl | rfl
    · have i1 : r < t := (angAt_det_pos_iff A hr ht).mp hy1
      have i2 : t < r + 1 := (angAt_det_pos_iff A ht hrM).mp hy2
      omega
    · rw [ncy_det_neg_right] at hy1
      rw [ncy_det_neg_left] at hy2
      have hsk1 : det (angAt N e t) (angAt N e r) = - det (angAt N e r) (angAt N e t) := by
        simp only [det]; ring
      have hsk2 : det (angAt N e (r + 1)) (angAt N e t)
          = - det (angAt N e t) (angAt N e (r + 1)) := by
        simp only [det]; ring
      have i1 : t < r := (angAt_det_pos_iff A ht hr).mp (by omega)
      have i2 : r + 1 < t := (angAt_det_pos_iff A hrM ht).mp (by omega)
      omega
  · have hrM' : r + 1 = (angUpper N e).card := by omega
    rw [hrM', angCyc_ge (le_refl _) (by omega), Nat.sub_self] at hy2
    rcases hyt with rfl | rfl
    · have i1 : r < t := (angAt_det_pos_iff A hr ht).mp hy1
      omega
    · rw [ncy_det_neg_right] at hy1
      rw [pm_det_neg_neg] at hy2
      have hsk1 : det (angAt N e t) (angAt N e r) = - det (angAt N e r) (angAt N e t) := by
        simp only [det]; ring
      have i1 : t < r := (angAt_det_pos_iff A ht hr).mp (by omega)
      have i2 : t < 0 := (angAt_det_pos_iff A ht (by omega)).mp hy2
      omega

/-- **`hnoArc`**，全体 `k`。后半圈那一步把 `y` 换成 `-y`（`N` 对取负闭，`hneg`）。 -/
theorem angCyc_noArc (A : AngData N e) (hm : 2 ≤ (angUpper N e).card) :
    ∀ k, ∀ y ∈ N, ¬ (0 < det (angCyc N e k) y ∧ 0 < det y (angCyc N e (k + 1))) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    by_cases h2 : 2 * (angUpper N e).card ≤ k
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 * (angUpper N e).card :=
        ⟨k - 2 * (angUpper N e).card, by omega⟩
      intro y hy
      have e2 : angCyc N e (j + 2 * (angUpper N e).card + 1) = angCyc N e (j + 1) := by
        rw [show j + 2 * (angUpper N e).card + 1 = (j + 1) + 2 * (angUpper N e).card by omega,
          angCyc_period]
      rw [angCyc_period j, e2]
      exact ih j (by omega) y hy
    · by_cases h1 : k < (angUpper N e).card
      · exact angCyc_noArc_lt A hm h1
      · obtain ⟨j, rfl⟩ : ∃ j, k = j + (angUpper N e).card :=
          ⟨k - (angUpper N e).card, by omega⟩
        intro y hy hcon
        obtain ⟨hy1, hy2⟩ := hcon
        rw [angCyc_anti hm j, ncy_det_neg_left] at hy1
        rw [show j + (angUpper N e).card + 1 = (j + 1) + (angUpper N e).card by omega,
          angCyc_anti hm (j + 1), ncy_det_neg_right] at hy2
        refine angCyc_noArc_lt A hm (by omega : j < (angUpper N e).card) (-y)
          (A.hneg y hy) ⟨?_, ?_⟩
        · rw [ncy_det_neg_right]; omega
        · rw [ncy_det_neg_left]; omega

/-- `ncyCcwOfPair` 要的 `hpair`（`[1,m]` 上两两不平行）。下标 `m` 那一格是 `-(angAt 0)`。 -/
theorem angCyc_pair (A : AngData N e) (hm : 2 ≤ (angUpper N e).card) :
    ∀ i j, 1 ≤ i → i ≤ (angUpper N e).card → 1 ≤ j → j ≤ (angUpper N e).card → i ≠ j →
      det (angCyc N e i) (angCyc N e j) ≠ 0 := by
  intro i j hi1 hi2 hj1 hj2 hij
  rcases eq_or_lt_of_le hi2 with hiM | hiM
  · rcases eq_or_lt_of_le hj2 with hjM | hjM
    · exact absurd (hiM.trans hjM.symm) hij
    · rw [hiM, angCyc_ge (le_refl _) (by omega), Nat.sub_self, angCyc_lt hjM,
        ncy_det_neg_left, ne_eq, neg_eq_zero]
      exact angAt_det_ne_zero A (by omega) hjM (by omega)
  · rcases eq_or_lt_of_le hj2 with hjM | hjM
    · rw [angCyc_lt hiM, hjM, angCyc_ge (le_refl _) (by omega), Nat.sub_self,
        ncy_det_neg_right, ne_eq, neg_eq_zero]
      exact angAt_det_ne_zero A hiM (by omega) (by omega)
    · rw [angCyc_lt hiM, angCyc_lt hjM]
      exact angAt_det_ne_zero A hiM hjM hij

/-- **本节的主构造**（`m` ＝ 上半圈的基数形态）。 -/
noncomputable def ncyOfAngDataCard (A : AngData N e) (hm : 2 ≤ (angUpper N e).card) :
    NormalCycleCcw (↑N : Set (ℤ × ℤ)) (angUpper N e).card :=
  ncyCcwOfPair (angCyc N e) (angUpper N e).card hm
    (fun k => Finset.mem_coe.mpr (angCyc_memN A hm k))
    (fun k => angCyc_ne_zero A hm k)
    (fun k => angCyc_anti hm k)
    (fun k => angCyc_step A hm k)
    (fun k y hy => angCyc_noArc A hm k y (Finset.mem_coe.mp hy))
    (angCyc_pair A hm)

/-- 同上，`m` 由消费者给。 -/
noncomputable def ncyOfAngData (A : AngData N e) (m : ℕ)
    (hcard : (angUpper N e).card = m) (hm : 2 ≤ m) :
    NormalCycleCcw (↑N : Set (ℤ × ℤ)) m := by
  subst hcard; exact ncyOfAngDataCard A hm

/-! ### §6.8  一般位置 + 消费者接口 -/

/-- **一般位置引理**：任何不含 `0` 的有限集，都存在与它每个元素都不垂直的 `e`。
纯 ℤ-算术鸽笼：`e = (1, t)`，坏的 `t` 至多 `|N|` 个（`n₂ ≠ 0` 时唯一，`n₂ = 0` 时没有），
而候选有 `|N| + 1` 个。**不用任何几何输入，也不要求消费者选 `e`。** -/
theorem exists_gen_position (N : Finset (ℤ × ℤ)) (h0 : ∀ n ∈ N, n ≠ 0) :
    ∃ e : ℤ × ℤ, e ≠ 0 ∧ ∀ n ∈ N, dot e n ≠ 0 := by
  classical
  set bad : Finset ℤ := N.image (fun n => if n.2 = 0 then 0 else (-n.1) / n.2) with hbad
  set cand : Finset ℤ := (Finset.range (N.card + 1)).image (fun i : ℕ => (i : ℤ)) with hcand
  have hbadcard : bad.card ≤ N.card := Finset.card_image_le
  have hcandcard : cand.card = N.card + 1 := by
    rw [hcand, Finset.card_image_of_injective _ (fun a b hab => by exact_mod_cast hab),
      Finset.card_range]
  have hnsub : ¬ cand ⊆ bad := by
    intro hsub
    have := Finset.card_le_card hsub
    omega
  obtain ⟨t, _, htbad⟩ := Finset.not_subset.mp hnsub
  refine ⟨(1, t), ?_, ?_⟩
  · intro hc
    have : (1 : ℤ) = 0 := congrArg Prod.fst hc
    omega
  · intro n hn hdot
    have hdot' : n.1 + t * n.2 = 0 := by
      simpa only [dot, one_mul] using hdot
    by_cases hn2 : n.2 = 0
    · exact h0 n hn (Prod.ext (by rw [hn2] at hdot'; simpa using hdot') hn2)
    · refine htbad ?_
      rw [hbad, Finset.mem_image]
      refine ⟨n, hn, ?_⟩
      rw [if_neg hn2]
      have hmul : -n.1 = t * n.2 := by omega
      rw [hmul, Int.mul_ediv_cancel _ hn2]

/-- **消费者接口**。`hcard` 就是 `b3_colle2.txt:319` 的 `|E(𝒮_φ)| = 2m`，
`hneg` 就是它的 ± 那半，`hpar` 就是 `:424` 的 pairwise distinct directions。
产出的是 `:424` 的整条环序枚举，`σ = 1`。 -/
theorem exists_ncy_of_finset (N : Finset (ℤ × ℤ)) (m : ℕ) (hm : 2 ≤ m)
    (hzero : ∀ n ∈ N, n ≠ 0)
    (hneg : ∀ n ∈ N, -n ∈ N)
    (hpar : ∀ n ∈ N, ∀ n' ∈ N, det n n' = 0 → n' = n ∨ n' = -n)
    (hcard : N.card = 2 * m) :
    Nonempty (NormalCycleCcw (↑N : Set (ℤ × ℤ)) m) := by
  obtain ⟨e, he, hgen⟩ := exists_gen_position N hzero
  have A : AngData N e := ⟨he, hgen, hneg, hpar⟩
  have hup : (angUpper N e).card = m := by
    have := angN_card A
    omega
  exact ⟨ncyOfAngData A m hup hm⟩

/-- **消费者接口，`Set` 形**。`NormalCycle` 的 `N` 是 `Set`，而链上的 `E ↑𝒮_φ` 也是 `Set`，
所以这条才是真正对接用的那个：只多要一条 `S.Finite`。 -/
theorem exists_ncy_of_set {S : Set (ℤ × ℤ)} (hfin : S.Finite) (m : ℕ) (hm : 2 ≤ m)
    (hzero : ∀ n ∈ S, n ≠ 0)
    (hneg : ∀ n ∈ S, -n ∈ S)
    (hpar : ∀ n ∈ S, ∀ n' ∈ S, det n n' = 0 → n' = n ∨ n' = -n)
    (hcard : hfin.toFinset.card = 2 * m) :
    Nonempty (NormalCycleCcw S m) := by
  have h := exists_ncy_of_finset hfin.toFinset m hm
    (by intro n hn; rw [Set.Finite.mem_toFinset] at hn; exact hzero n hn)
    (by intro n hn; rw [Set.Finite.mem_toFinset] at hn ⊢; exact hneg n hn)
    (by
      intro n hn n' hn' h0
      rw [Set.Finite.mem_toFinset] at hn hn'
      exact hpar n hn n' hn' h0)
    hcard
  rwa [hfin.coe_toFinset] at h

/-- **最强形（本节的主结论）：连 `|E(𝒮_φ)| = 2m` 都不要。**
输入只有：有限、`0 ∉ S`、± 闭、「平行 ⟹ 相等或相反」、**存在一对不平行元素**。
产出一个 `m ≥ 2` 和一条 `σ = 1` 的 `NormalCycle`。

⟹ 集成者第 182 轮的硬子问题「`anti` 是否要对整个 `E(𝒮_φ)` 做 ±-闭包」的完整回答：
要，但那是 `:319` 的字面内容、主仓 `DecompData.Sphi_negSymm`（`DecompData.lean:417`）无条件
已有，**不是我们加的量词**；而我们原本登记的那条「对径 ＝ 下标平移 `m`」的转录债，在这里被
`angCyc_anti` 还清（定义的分支结构，零几何输入）。 -/
theorem exists_ncy_of_set' {S : Set (ℤ × ℤ)} (hfin : S.Finite)
    (hzero : ∀ n ∈ S, n ≠ 0)
    (hneg : ∀ n ∈ S, -n ∈ S)
    (hpar : ∀ n ∈ S, ∀ n' ∈ S, det n n' = 0 → n' = n ∨ n' = -n)
    (hnondeg : ∃ a ∈ S, ∃ b ∈ S, det a b ≠ 0) :
    ∃ m, 2 ≤ m ∧ Nonempty (NormalCycleCcw S m) := by
  obtain ⟨a, haS, b, hbS, hab⟩ := hnondeg
  obtain ⟨e, he, hgen⟩ := exists_gen_position hfin.toFinset
    (by intro n hn; rw [Set.Finite.mem_toFinset] at hn; exact hzero n hn)
  have A : AngData hfin.toFinset e :=
    ⟨he, hgen,
      by intro n hn; rw [Set.Finite.mem_toFinset] at hn ⊢; exact hneg n hn,
      by
        intro n hn n' hn' h0
        rw [Set.Finite.mem_toFinset] at hn hn'
        exact hpar n hn n' hn' h0⟩
  have hm : 2 ≤ (angUpper hfin.toFinset e).card :=
    two_le_angUpper_card A (hfin.mem_toFinset.mpr haS) (hfin.mem_toFinset.mpr hbS) hab
  refine ⟨(angUpper hfin.toFinset e).card, hm, ?_⟩
  have h := ncyOfAngDataCard A hm
  rw [hfin.coe_toFinset] at h
  exact ⟨h⟩

/-! ### §6.9  数值台架（硬规矩 6：派几何义务前先算一个实例）

`N = {±(1,0), ±(0,1)}`，`m = 2`。四条前提全部**内核判定**，说明 `exists_ncy_of_finset`
的前提包**不是空真**。 -/

/-- 四元法向集。 -/
def exAngN : Finset (ℤ × ℤ) := {(1, 0), (0, 1), (-1, 0), (0, -1)}

theorem exAng_card : exAngN.card = 2 * 2 := by decide

theorem exAng_zero : ∀ n ∈ exAngN, n ≠ 0 := by decide

theorem exAng_neg : ∀ n ∈ exAngN, -n ∈ exAngN := by decide

theorem exAng_par : ∀ n ∈ exAngN, ∀ n' ∈ exAngN, det n n' = 0 → n' = n ∨ n' = -n := by decide

/-- 台架上真造得出环。 -/
theorem exAng_cycle : Nonempty (NormalCycleCcw (↑exAngN : Set (ℤ × ℤ)) 2) :=
  exists_ncy_of_finset exAngN 2 (by omega) exAng_zero exAng_neg exAng_par exAng_card

end AngBuild

end Nivat.NormalCycleExists

/-! ## 公理审计（分母＝本文件声明数 61，含 private；由
`tmp/_hlev_audit233.py` 生成，一条声明一行——短块照样打出干净列表，
却会留下未审计的声明）。 -/

#print axioms Nivat.NormalCycleExists.pm_ne_zero_cases
#print axioms Nivat.NormalCycleExists.pm_det_eq_zero_of_perp
#print axioms Nivat.NormalCycleExists.pm_dot_of_par
#print axioms Nivat.NormalCycleExists.pm_det_neg_neg
#print axioms Nivat.NormalCycleExists.pm_det_shift
#print axioms Nivat.NormalCycleExists.pm_indep_range
#print axioms Nivat.NormalCycleExists.pm_indep_full
#print axioms Nivat.NormalCycleExists.ncyCcwOfPair
#print axioms Nivat.NormalCycleExists.leAng
#print axioms Nivat.NormalCycleExists.leAng_trans
#print axioms Nivat.NormalCycleExists.leAng_total
#print axioms Nivat.NormalCycleExists.AngData
#print axioms Nivat.NormalCycleExists.ang_dot_neg
#print axioms Nivat.NormalCycleExists.ang_ne_zero
#print axioms Nivat.NormalCycleExists.angUpper
#print axioms Nivat.NormalCycleExists.mem_angUpper
#print axioms Nivat.NormalCycleExists.angLower
#print axioms Nivat.NormalCycleExists.angLower_eq_image
#print axioms Nivat.NormalCycleExists.angN_card
#print axioms Nivat.NormalCycleExists.angUpper_mem_of_mem
#print axioms Nivat.NormalCycleExists.two_le_angUpper_card
#print axioms Nivat.NormalCycleExists.angList
#print axioms Nivat.NormalCycleExists.angList_length
#print axioms Nivat.NormalCycleExists.mem_angList
#print axioms Nivat.NormalCycleExists.angList_nodup
#print axioms Nivat.NormalCycleExists.angList_pairwise
#print axioms Nivat.NormalCycleExists.angAt
#print axioms Nivat.NormalCycleExists.angAt_eq_getElem
#print axioms Nivat.NormalCycleExists.angAt_mem
#print axioms Nivat.NormalCycleExists.angAt_memN
#print axioms Nivat.NormalCycleExists.angAt_dot_pos
#print axioms Nivat.NormalCycleExists.angAt_key_le
#print axioms Nivat.NormalCycleExists.angAt_ne
#print axioms Nivat.NormalCycleExists.angAt_det_ne_zero
#print axioms Nivat.NormalCycleExists.angAt_det_pos
#print axioms Nivat.NormalCycleExists.angAt_det_pos_iff
#print axioms Nivat.NormalCycleExists.angAt_surj
#print axioms Nivat.NormalCycleExists.angCyc
#print axioms Nivat.NormalCycleExists.angCyc_lt
#print axioms Nivat.NormalCycleExists.angCyc_ge
#print axioms Nivat.NormalCycleExists.angCyc_period
#print axioms Nivat.NormalCycleExists.angCyc_memN
#print axioms Nivat.NormalCycleExists.angCyc_ne_zero
#print axioms Nivat.NormalCycleExists.angCyc_anti
#print axioms Nivat.NormalCycleExists.angCyc_step_lt
#print axioms Nivat.NormalCycleExists.angCyc_step
#print axioms Nivat.NormalCycleExists.angCyc_noArc_lt
#print axioms Nivat.NormalCycleExists.angCyc_noArc
#print axioms Nivat.NormalCycleExists.angCyc_pair
#print axioms Nivat.NormalCycleExists.ncyOfAngDataCard
#print axioms Nivat.NormalCycleExists.ncyOfAngData
#print axioms Nivat.NormalCycleExists.exists_gen_position
#print axioms Nivat.NormalCycleExists.exists_ncy_of_finset
#print axioms Nivat.NormalCycleExists.exists_ncy_of_set
#print axioms Nivat.NormalCycleExists.exists_ncy_of_set'
#print axioms Nivat.NormalCycleExists.exAngN
#print axioms Nivat.NormalCycleExists.exAng_card
#print axioms Nivat.NormalCycleExists.exAng_zero
#print axioms Nivat.NormalCycleExists.exAng_neg
#print axioms Nivat.NormalCycleExists.exAng_par
#print axioms Nivat.NormalCycleExists.exAng_cycle
