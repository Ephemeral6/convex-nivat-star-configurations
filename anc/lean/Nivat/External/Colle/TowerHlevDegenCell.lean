/-
# 退化格（`det p vJ1 = 0`）判定 —— lane-tower-hlev，集成者 2026-09-26 派工 ④

## §0  这是什么

消费者是 `RecVJTransverse.rec_vJ_of_parts_transverse` 的 binder
`hdet : det p c.vJ1 ≠ 0`（横截格）。本文件做**它的补集**那一格，全部以
`ChainDataGeomParts`（`ChainPartsFeed.lean` 的 `Nivat.ChainAsm.Aparts.ChainDataGeomParts`）
为载体：

| § | 声明 | 非字段前提 |
|---|---|---|
| §1 | `not_hcomb_of_degenerate` / `not_hcomb_nat_of_degenerate` | `det p vJ1 = 0` 一条 |
| §2 | `p_ne_zero_of_parts` | **零** |
| §3 | `window_bot_of_degenerate_of_dict` | `hp_neg` 两条 ＋ **环序索引字典**（⚠ 不是字段） |
| §4 | 两条 `m = 4` 台架 | — |

## §0.1  去重（落地前按 `scripts/declscan.py --file` 扫过，`PROTOCOL §75`）

⭐ **本文件刻意不造以下两条的第二份**，它们本轮已在主仓：

* `EnvRefuteOrient.det_p_vJ_ne_zero_of_parts` —— `det p c.vJ ≠ 0`，零前提。
  我独立推出过同一条（`vJ_prim.ne_zero` ＋ `F.dot_nJ_vJ` ＋ `dot_nJ_p_pos_of_parts`），
  扫出撞名后**弃用我的、改引它**（同 `rec_of_ray` 去重的办法，盲区 3：不删旧名）。
* `TowerHbase.hb_det_p_vJ1_eq_zero_iff_collinear` —— `det p vJ1 = 0 ↔ ∃ m, vJ1 = m • vl`
  （带 `Primitive vl`）。§3 需要的是它的 `Primitive`-free 半边（`det vl vJ1 = 0`），
  只在 §3 的证明体里**内联三行**，**不导出**第二个声明。

## §0.2  ⚠ 本文件**不**主张的

⛔ 不主张链上 `det p vJ1 = 0` 成立，也不主张它不成立。§1/§3 全部以它为**假设**
（`PROTOCOL §40`：条件形式照样编译、照样公理干净，caveat 只在 docstring 里）。
⛔ 不主张 `vl = dir ν_ι`、`vJ1 = dir ν_{J−1}` 这条字典在链上成立 —— §3 把它收成 binder，
`ChainPartsFeed.lean` 的 `vJ1` 字段 docstring 自记「链上**不钉**这一格」。
⛔ 不碰任何带号的判据：本文件对 `det` 只用 `= 0` / `≠ 0`，与 `σ`（旋向）无关
（同 `CyclicOrderWindow.lean` §0.2），故第 179 轮红线在这里不触发。

## §0.3  原文侧（②，亲读 `scratch/b3_colle2.txt`，非内核见证）

`b3_colle2.txt:498` 逐字：「let `ι+1 ≤ J ≤ ι+m-1` be the **smallest** integer such that
`|Â_i ∩ w_i(J)| < |Â_{i+1} ∩ w_{i+1}(J)|` for infinity many `i`」；
`b3_colle2.txt:502` 逐字（同段下一句）：「**If `J > ι+1`**, we also may assume that …」。

⟹ 原文自己按 `J = ι+1` / `J > ι+1` 分叉，且在 `J = ι+1` 支上不追加任何假设
⟹ **`J = ι+1` 没有被原文排除**。
⚠ 这只说明原文不排除，**不等于**链上一定出现；后者要一个 `ChainDataGeomParts` 的居民，
本文件没有造。
⚠ 同一读数 lane-tower-hbase 本轮独立给出（`TowerHbaseRecP.lean` §22.1，亲读同六行），
两边**不是**互相转述：我先读 `:498`/`:502` 再扫到他的 §22。按 `PROTOCOL §91` 记作
两张独立的 ②，不合成、不升级。

## §0.4  import 表（与 `grep -n "^import"` 一致，`PROTOCOL §57`）

* `Nivat.External.Colle.EnvRefuteOrient` —— `det_p_vJ_ne_zero_of_parts` / `dot_nJ_p_pos_of_parts`，
  并传递地带来 `ChainDataGeomParts` / `LatticeEdges` / `ANormal`。
* `Nivat.External.Colle.CyclicOrderWindow` —— `window_bot_of_det_prev_eq_zero`（§3）。

四个禁区模块（`RegionSteps` / `ColleRegion` / `Case2WindowProbe` / `NfpLPreamble`）**未 import**。
-/
import Nivat.External.Colle.EnvRefuteOrient
import Nivat.External.Colle.CyclicOrderWindow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Nivat.TowerHlevDegenCell

open Nivat Nivat.LE2 Nivat.Colle35 Nivat.ChainAsm.Aparts Nivat.LaneTowerHlevNormalCycle

/-! ## §1  退化格里 `hcomb` 为假 -/

/-- ⭐ **`det p vJ1 = 0` ⟹ `vJ` 不在 `⟨p, vJ1⟩` 里**（整系数、实系数的整点形都不在）。

`det p (a•p + t•vJ1) = t * det p vJ1 = 0`，与 `EnvRefuteOrient.det_p_vJ_ne_zero_of_parts`
（`det p c.vJ ≠ 0`，零前提）冲突。

⟹ 退化格里 `⟨p,vJ1⟩`-锥这条路**不是「还没做」而是「做不成」**：
`RecVJTransverse.rec_vJ_of_parts_transverse` 的 `hdet` 不是技术性 binder，
而是该证法的**边界**。

⚠ 与 `LaneLeafAShellLsideFork.not_W₀_pos_multiple_of_collinear_lside` 是**两条不同的命题**：
那条否的是 `∃ d > 0, W₀ = d • vJ`，本条否的是 `∃ a t, vJ = a•p + t•vJ1`（`hcomb` 形）。
两条结论同向，证法与陈述都不同，故不是重复。 -/
theorem not_hcomb_of_degenerate {α : Type*} {η xper : Config α} {vl p gen : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} (c : ChainDataGeomParts η xper vl p S gen)
    (hdeg : det p c.vJ1 = 0) :
    ¬ ∃ a t : ℤ, c.vJ = a • p + t • c.vJ1 := by
  rintro ⟨a, t, hc⟩
  refine Nivat.EnvRefuteOrient.det_p_vJ_ne_zero_of_parts c ?_
  have hexp : det p c.vJ = t * det p c.vJ1 := by
    rw [hc]
    simp only [det, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  rw [hexp, hdeg, mul_zero]

/-- §1 的 `ℕ` 形，逐字对上链上 `hcomb` 的 `∃ a t : ℕ`。 -/
theorem not_hcomb_nat_of_degenerate {α : Type*} {η xper : Config α} {vl p gen : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} (c : ChainDataGeomParts η xper vl p S gen)
    (hdeg : det p c.vJ1 = 0) :
    ¬ ∃ a t : ℕ, c.vJ = (a : ℤ) • p + (t : ℤ) • c.vJ1 := by
  rintro ⟨a, t, hc⟩
  exact not_hcomb_of_degenerate c hdeg ⟨(a : ℤ), (t : ℤ), hc⟩

/-! ## §2  链上 `p ≠ 0`：退化只有一个来源 -/

/-- **`p ≠ 0`，零前提。**由 `EnvRefuteOrient.dot_nJ_p_pos_of_parts` 的 `0 < ⟪nJ,p⟫`。

⟹ `det p c.vJ1 = 0` 这一格**不可能**来自「`p` 退化成零向量」，只能来自 `vJ1 ∥ p`
（在 `hp_neg` 之下即 `vJ1 ∥ vl`，见 `TowerHbase.hb_det_p_vJ1_eq_zero_iff_collinear`）。 -/
theorem p_ne_zero_of_parts {α : Type*} {η xper : Config α} {vl p gen : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} (c : ChainDataGeomParts η xper vl p S gen) : p ≠ 0 := by
  intro h
  subst h
  have hpos : 0 < dot c.nJ ((0 : ℤ), (0 : ℤ)) := Nivat.EnvRefuteOrient.dot_nJ_p_pos_of_parts c
  simp only [dot, mul_zero, add_zero] at hpos
  omega

/-! ## §3  接到 `J = ι+1` 上（⚠ 字典是 binder，不是字段） -/

/-- ⭐ **退化格 ⟹ `J = ι+1`，且 `vJ1 = vl`**（在 `ChainDataGeomParts` 上陈述）。

`b3_colle2.txt:432` 的窗口「with `ι+1 ≤ J ≤ ι+m-1`」写成 `J = i + t + 1`、`t + 1 < m`
（同 `CyclicOrderWindow.lean` §2 的下标约定）；结论 `t = 0` 即 `J = ι + 1`。

**前提表**（硬规矩 6：逐条标明是不是 `ChainDataGeomParts` 的字段）：

| 前提 | 是字段吗 |
|---|---|
| `c : ChainDataGeomParts …` | — |
| `hc : 0 < cc`、`hp : p = -(cc:ℤ) • vl` | ❌ 不是字段，是 `exists_chainData` 的 binder `hp_neg` |
| `C : NormalCycle N m σ` | ❌ 不是字段；候选产者 `NormalCycleExists.exists_ncy_of_set` |
| `ht : t + 1 < m` | ❌ 不是字段（`b3_colle2.txt:432` 的窗口） |
| `hvl : vl = dir (C.nu i)`、`hvJ1 : c.vJ1 = dir (C.nu (i + t))` | ❌ **不是字段 —— 这就是缺口** |
| `hdeg : det p c.vJ1 = 0` | ❌ 假设（本格的定义） |

⟹ **本条不是「`J = ι+1` 在链上成立」的证明**，是「一旦索引字典到手，退化格就等同
`J = ι+1`」。缺的那条恰是 `ChainPartsFeed.lean` 的 `vJ1` 字段 docstring 自记的
「链上**不钉**这一格」。

⚠ 逆否方向（`t ≠ 0` ⟹ 横截）已在主仓：`TowerHbase.det_prev_ne_zero_of_window_pos`
（纯环序侧，不带 `ChainDataGeomParts`）。本条是**链侧**那一半，两条不重复。

⚠ 无号：本条对 `det` 只用 `= 0`，与 `σ` 无关，属第 179 轮红线的「可搬」那一栏。 -/
theorem window_bot_of_degenerate_of_dict {α : Type*} {η xper : Config α} {vl p gen : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} (c : ChainDataGeomParts η xper vl p S gen)
    {cc : ℕ} (hc : 0 < cc) (hp : p = -(cc : ℤ) • vl)
    {N : Set (ℤ × ℤ)} {m : ℕ} {σ : ℤ} (C : NormalCycle N m σ) (i t : ℕ) (ht : t + 1 < m)
    (hvl : vl = dir (C.nu i)) (hvJ1 : c.vJ1 = dir (C.nu (i + t)))
    (hdeg : det p c.vJ1 = 0) :
    t = 0 ∧ c.vJ1 = vl := by
  subst hp
  -- `Primitive`-free 半边，内联（§0.1：不导出第二份）
  have hexp : det (-(cc : ℤ) • vl) c.vJ1 = -(cc : ℤ) * det vl c.vJ1 := by
    simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  have hccz : (cc : ℤ) ≠ 0 := by
    have : 0 < (cc : ℤ) := by exact_mod_cast hc
    omega
  have hcol : det vl c.vJ1 = 0 := by
    rw [hexp] at hdeg
    rcases mul_eq_zero.mp hdeg with h' | h'
    · exact absurd (by omega : (cc : ℤ) = 0) hccz
    · exact h'
  have hdir : det (C.nu i) (C.nu (i + t)) = 0 := by
    have hdd : det (dir (C.nu i)) (dir (C.nu (i + t))) = 0 := by
      rw [← hvl, ← hvJ1]; exact hcol
    rwa [ncy_det_dir_dir] at hdd
  have ht0 : t = 0 := Nivat.CyclicOrderWindow.window_bot_of_det_prev_eq_zero C i t ht hdir
  refine ⟨ht0, ?_⟩
  refine hvJ1.trans ?_
  rw [ht0, Nat.add_zero]
  exact hvl.symm

/-! ## §4  台架（`m = 4`，常设纪律 1）

⚠ **射程自限（`PROTOCOL §84` / `§71`）**：本台架只覆盖 §3 的**环序侧**前提
（`C` / `ht` / `hdir`），**不含** `ChainDataGeomParts` —— 没有任何 `ChainDataGeomParts`
的居民被造出来。故它是「前件可满足」的**必要条件**，不是完整可满足性见证。 -/

/-- `§71` 一（前件可满足）：`m = 4` 的正八边形上，`t = 0` 那一格的两条环序侧前提同时成立。 -/
theorem window_bot_premises_sat_m_four :
    (0 : ℕ) + 1 < 4 ∧ det (ncyOctCycleCcw.nu 0) (ncyOctCycleCcw.nu (0 + 0)) = 0 := by
  refine ⟨by omega, ?_⟩
  simp only [ncyOctCycleCcw, ncyOctCcw, ncyOctBase, det]
  norm_num

/-- `§71` 二（结论鉴别）：同一台架上，窗口里另外两个 `t`（`t = 1, 2`）的 `det` **不为零**
⟹ §3 的结论 `t = 0` 不是平凡的（窗口里确实有 `t ≠ 0` 的位置，且它们被前提排除）。 -/
theorem window_bot_discriminating_m_four :
    det (ncyOctCycleCcw.nu 0) (ncyOctCycleCcw.nu (0 + 1)) ≠ 0 ∧
      det (ncyOctCycleCcw.nu 0) (ncyOctCycleCcw.nu (0 + 2)) ≠ 0 := by
  constructor <;>
    · simp only [ncyOctCycleCcw, ncyOctCcw, ncyOctBase, det]
      norm_num

end Nivat.TowerHlevDegenCell

/-! ## §5  取证 -/

#print axioms Nivat.TowerHlevDegenCell.not_hcomb_of_degenerate
#print axioms Nivat.TowerHlevDegenCell.not_hcomb_nat_of_degenerate
#print axioms Nivat.TowerHlevDegenCell.p_ne_zero_of_parts
#print axioms Nivat.TowerHlevDegenCell.window_bot_of_degenerate_of_dict
#print axioms Nivat.TowerHlevDegenCell.window_bot_premises_sat_m_four
#print axioms Nivat.TowerHlevDegenCell.window_bot_discriminating_m_four
