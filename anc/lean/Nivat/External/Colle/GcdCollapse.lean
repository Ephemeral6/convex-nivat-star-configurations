/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.ChainGeom

set_option autoImplicit false

/-!
# `gcd(d, e) = 1` 在链上塌回 `dot nJ vl = ±1` —— 本轮「新算术义务」不是新债

第 231–232 轮的线索是：`ChainDataGeom.bottom` 的合取 1 由 `gcd(d, e) = 1` 判定，
`d := dot nJ p`、`e := -dot nJ vJ1`（`NlmaxGcd` 的 `bottom_conj1_of_gcd_one`、
`TowerHbase` 的 `bottom_conj123_of_rec_p` 的 `IsCoprime` 前提）。两条 lane 都报
「`gcd = 1` 不能从 `ChainDataGeom` 字段推出，是对生产者 `exists_chainData` 的**新**算术义务」。
两条报告都对，**但「新」是错的**：在 `exists_chainData` 的 binder 下，这条义务与已被
宣告「不是 `ChainDataGeom` 的定理」的 `dot nJ vJ1 = -1` 是**同一条**。

链上两条共线事实（都不是本文件的假设，是签名里现成的）：

* `p = -(c : ℕ) • vl`、`0 < c` —— `RegionSteps` 的 `exists_chainData` binder `hp_neg`
  （2026-09-23 加，生产者在 `ColleRegion` 的 `exists_neg_multiple_of_perp`）；
  其几何来源是 `hdet_vl : det p vl = 0` ＋ `hvl_prim : Primitive vl` ＋ `hp_ne : p ≠ 0`。
  `v_ℓ` 的定义见 `b3_colle2.txt:351`（`v⃗_ℓ ∈ ℓ ∩ ℤ²`，`ℓ` 方向的非零本原向量）。
* `vJ1 = m • vl`、`0 < m` —— `LeafAShellAttain` 的 `hm` / `hmpos`（第 226 轮共线裁决，
  `CyclicOrderWindow` 里 `det vl vJ1 = 0 ⟹ vJ1 = vl` 那一支是 `m = 1` 的特例）。
  ⛔ **第 233 轮订正**：上一版这里写「`0 < m` 本身**无产者**」，**那句已经不准**。
  `LeafAShellLsideFork.m_pos_of_chain_stock`（第 233 轮落地）由 `hhp` ＋ `rec_p` ＋
  `ahat_nonempty` ＋ `dot_nJ_p` ＋ `hp_neg` 推出 `dot nJ vl < 0`，再配 `hsweep` ＋ `hm`
  给出 `0 < m`。⟹ `0 < m` **有产者**，而且定住那个比特的是链上几何（半平面 ＋ `rec_p`），
  不是 `:424` 的枚举约定。本文件下面 `m_pos_of_sign` 是同一算术的抽象形式。
  ⚠ 仍然开着的是共线裁决 `hm` 自己：结论型 `∃ m, vJ1 = m • vl` 在 `Nivat/**.lean` 里
  **0 命中**（lane-tower-hbase 第 233 轮实测，正控 `dot nJ vJ1` = 368 行）⟹ 只能报
  「没找到产者」，不能报「没有产者」。

于是 `dot nJ vl` **同时整除** `d = -c · dot nJ vl` 与 `e = m · dot nJ vl`，
互素立刻逼出 `dot nJ vl = ±1`；再由 `hsweep : dot nJ vJ1 < 0` 与 `0 < m` 定符号：

```
gcd(d, e) = 1  ⟹  dot nJ vl = -1  ∧  d = c  ∧  e = m
```

特别地 `m = 1`（即 `vJ1 = vl`，链上共线构型）时 `e = 1`，**逐字等于 `dot nJ vJ1 = -1`**。

⟹ 本轮从 `e = 1` 走到 `gcd(d, e) = 1` 再走回 `e = 1`。⛔ 不许把 `gcd = 1` 记成新入口：
它是同一笔债的重新参数化。真正的、唯一的欠项是

> **`|dot nJ vl| = 1`**（等价地 `det vJ vl = ±1`，即 `{vJ, vl}` 是 `ℤ²` 的基）。

⚠ 射程：`cgc`（`ShellConvex`）否掉的是「`ChainDataGeom` ⊨ `dot nJ vJ1 = -1`」，而
`cgc` 连 `hdet_vl : det p vl = 0` 都不满足（`det (2,1) (1,-2) = -5`，lane-leafa-shell 第 232 轮实测）
⟹ 它 **不** 否掉「`exists_chainData` 的 binder ⊨ `|dot nJ vl| = 1`」。后者仍未定，是该打的靶。
-/

namespace Nivat.GcdCollapse

open Nivat Nivat.LE2

private theorem dotZ (n : ℤ × ℤ) (k : ℤ) (z : ℤ × ℤ) : dot n (k • z) = k * dot n z := by
  simp only [dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

/-- `dot nJ vl ∣ dot nJ p`，由链上 `hp_neg` 的 `p = -c • vl`。 -/
theorem dvd_d {nJ vl p : ℤ × ℤ} {c : ℕ} (hp : p = -(c : ℤ) • vl) :
    dot nJ vl ∣ dot nJ p := by
  rw [hp, dotZ]; exact dvd_mul_left _ _

/-- `dot nJ vl ∣ -dot nJ vJ1`，由共线裁决 `vJ1 = m • vl`。 -/
theorem dvd_e {nJ vl vJ1 : ℤ × ℤ} {m : ℤ} (hm : vJ1 = m • vl) :
    dot nJ vl ∣ -dot nJ vJ1 := by
  rw [hm, dotZ]; exact dvd_neg.mpr (dvd_mul_left _ _)

/-- **核心**：`gcd(d, e) = 1` 逼出 `dot nJ vl` 是单位。不需要 `0 < c` / `0 < m` / `hsweep`。 -/
theorem dot_nJ_vl_isUnit {nJ vl p vJ1 : ℤ × ℤ} {c : ℕ} {m : ℤ}
    (hp : p = -(c : ℤ) • vl) (hm : vJ1 = m • vl)
    (hgcd : Int.gcd (dot nJ p) (-dot nJ vJ1) = 1) :
    dot nJ vl = 1 ∨ dot nJ vl = -1 := by
  have hcop : IsCoprime (dot nJ p) (-dot nJ vJ1) := Int.isCoprime_iff_gcd_eq_one.mpr hgcd
  exact Int.isUnit_iff.mp
    (hcop.isUnit_of_dvd' (dvd_d (nJ := nJ) hp) (dvd_e (nJ := nJ) hm))

/-- **塌陷定理**：链上 `gcd(d, e) = 1` ⟹ `dot nJ vl = -1`，且 `d = c`、`e = m`。 -/
theorem collapse {nJ vl p vJ1 : ℤ × ℤ} {c : ℕ} {m : ℤ}
    (hp : p = -(c : ℤ) • vl) (hm : vJ1 = m • vl) (hmpos : 0 < m)
    (hsweep : dot nJ vJ1 < 0)
    (hgcd : Int.gcd (dot nJ p) (-dot nJ vJ1) = 1) :
    dot nJ vl = -1 ∧ dot nJ p = (c : ℤ) ∧ -dot nJ vJ1 = m := by
  have hdvJ1 : dot nJ vJ1 = m * dot nJ vl := by rw [hm, dotZ]
  have hunit := dot_nJ_vl_isUnit hp hm hgcd
  have hneg : dot nJ vl = -1 := by
    rcases hunit with h | h
    · rw [h, mul_one] at hdvJ1; omega
    · exact h
  refine ⟨hneg, ?_, ?_⟩
  · rw [hp, dotZ, hneg]; ring
  · rw [hdvJ1, hneg]; ring

/-- **圆的另一半**：共线构型 `vJ1 = vl` 下，`dot nJ vl = -1` 就是 `e = 1`。
⟹ `gcd(d, e) = 1` 与被宣告「不是 `ChainDataGeom` 定理」的 `dot nJ vJ1 = -1` 在链上等价。 -/
theorem e_eq_one_of_unit {nJ vl vJ1 : ℤ × ℤ} (hvJ1 : vJ1 = vl) (h : dot nJ vl = -1) :
    dot nJ vJ1 = -1 := by rw [hvJ1, h]

/-- 合起来：链上共线构型 `vJ1 = vl` 下 `gcd(d, e) = 1 ⟹ dot nJ vJ1 = -1`。 -/
theorem unit_sweep_of_gcd_one {nJ vl p vJ1 : ℤ × ℤ} {c : ℕ}
    (hp : p = -(c : ℤ) • vl) (hvJ1 : vJ1 = vl) (hsweep : dot nJ vJ1 < 0)
    (hgcd : Int.gcd (dot nJ p) (-dot nJ vJ1) = 1) :
    dot nJ vJ1 = -1 := by
  obtain ⟨h, -, -⟩ := collapse hp (m := 1) (by simpa using hvJ1) one_pos hsweep hgcd
  exact e_eq_one_of_unit hvJ1 h

/-- 反向，说明塌陷不是空的：`dot nJ vl = -1` ＋ 共线 ⟹ `gcd(d, e) = 1` 自动成立。
⛔ **第 233 轮订正**：本条 binder 里的 `hvJ1 : vJ1 = vl` 就是 `m = 1` 写死，所以上一版据此写的
「两条义务**互相**蕴含，`gcd = 1` 一个新自由度都没给」在**一般 `m`** 下为假 ——
正确的一般形式是 `gcd(d, e) = gcd(c, m)`。等价性要靠下面 `gcd_one_iff_of_prim` 用
`Primitive vJ1`（原文 `:351`）把 `m` 钉成 `1` 才在链上恢复。 -/
theorem gcd_one_of_unit {nJ vl p vJ1 : ℤ × ℤ}
    (hvJ1 : vJ1 = vl) (h : dot nJ vl = -1) :
    Int.gcd (dot nJ p) (-dot nJ vJ1) = 1 := by
  have he : -dot nJ vJ1 = 1 := by rw [hvJ1, h]; ring
  rw [he]
  exact Int.gcd_one_right (dot nJ p)

/-! ## 同一组共线事实的第二个后果：`det p vJ1` 在链上恒为 `0`

第 232 轮有两条 lane 各自把合取 1–3 的残余压到 `det p vJ1` 上：
`TowerHlevTile` 的 `exists_tile_of_swept` 要 `hindep : det p vJ1 ≠ 0`，
`TowerHbase` 的 `bottom_conj123_of_det_unit` 要 `det p vJ1 = ±1`（经
`isCoprime_dot_of_det_unit` 产出 `hcop`）。⛔ **两条前件在链上都不可满足**：
`p` 与 `vJ1` 都是同一个 `vl` 的倍数，行列式恒为 `0`。

⟹ `TowerHbase.gcd_dot_dvd_det` / `isCoprime_dot_of_det_unit` 的代数是对的
（对任意本原 `n`、任意 `p, q` 成立），但把它们实例化到链上的 `(p, vJ1)` 时前件为假 ⟹
`bottom_conj123_of_det_unit` 与 `bottom_conj123_of_tile` 一样是**空载出口**，不减债。
⚠ 射程：只说 `(p, vJ1)` 这一对。`det vJ vl`（`NlmaxDetVl.unit_vl_iff_unimodular` 的那一对）
含 `vJ` 而非 `p`，**不**被本节触及，仍是那条唯一欠项。
-/

/-- 链上 `p = -c • vl`、`vJ1 = m • vl` ⟹ `det p vJ1 = 0`。 -/
theorem det_p_vJ1_zero {vl p vJ1 : ℤ × ℤ} {c : ℕ} {m : ℤ}
    (hp : p = -(c : ℤ) • vl) (hm : vJ1 = m • vl) : det p vJ1 = 0 := by
  subst hp; subst hm
  simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

/-- ⛔ 于是 `det p vJ1 ≠ 0` 与 `det p vJ1 = ±1` 在链上都不可满足。 -/
theorem not_det_unit {vl p vJ1 : ℤ × ℤ} {c : ℕ} {m : ℤ}
    (hp : p = -(c : ℤ) • vl) (hm : vJ1 = m • vl) :
    det p vJ1 ≠ 1 ∧ det p vJ1 ≠ -1 ∧ ¬ (det p vJ1 ≠ 0) := by
  rw [det_p_vJ1_zero hp hm]
  exact ⟨by norm_num, by norm_num, by norm_num⟩

/-! ## `hmpos : 0 < m` 也塌进同一格：它是 `hsweep` ＋ **符号** `dot nJ vl < 0` 的推论

第 232 轮 lane-leafa-shell 把 `hmpos` 定性成「ccw / cw 两支恰好一支成立，而哪一支由
`hsweep : dot nJ vJ1 < 0` 选定」，并把「`hsweep` 选哪支」报成纯欠账。下面这条说那一格是
**算术**，不是几何：`dot nJ vJ1 = m · dot nJ vl`，所以 `hsweep` 直接说「`m` 与 `dot nJ vl` 异号」。
⟹ 只要有 `dot nJ vl < 0`（**符号**，`tmp/wip/lane-substrip-sign.lean` 报已有），`0 < m` 白送。

⟹ 本轮四个债券（`hcop` / `gcd(d,e) = 1` / `dot nJ vJ1 = -1` / `hmpos`）全部塌进**一个**量
`dot nJ vl`，并且拆成两半：

| 半 | 内容 | 状态（第 233 轮更新） |
|---|---|---|
| 符号 | `dot nJ vl < 0` | ✅ **已产**：`LeafAShellLsideFork.dot_nJ_vl_neg_of_rec_p`（主仓，第 233 轮） |
| **大小** | `|dot nJ vl| = 1` ⟺ `det vJ vl = ±1`（`NlmaxDetVl.unit_vl_iff_unimodular`） | ⛔ **零产者，且第 233 轮取得两条不利证据，见文件尾** |

⛔ **第 233 轮订正这张表少一行**：hbase 的 `c = m = 2` 见证表明一般 `m` 下还要
`IsCoprime (c : ℤ) m`。但那一行**不是独立债**——它由原文 `:351` 的 `Primitive vJ1` 推出
（`isCoprime_c_m_of_prim`），见下面「`Primitive vJ1` 把 `m` 钉成 `1`」一节。
⟹ 表仍是两行，但「符号」那半已产，剩下的**只有大小那半**。
-/

/-- `hmpos` 不是独立债：`hsweep` ＋ `dot nJ vl < 0` 一步给出 `0 < m`。 -/
theorem m_pos_of_sign {nJ vl vJ1 : ℤ × ℤ} {m : ℤ}
    (hm : vJ1 = m • vl) (hsweep : dot nJ vJ1 < 0) (hsign : dot nJ vl < 0) : 0 < m := by
  have h : dot nJ vJ1 = m * dot nJ vl := by rw [hm, dotZ]
  rw [h] at hsweep
  by_contra hc
  push_neg at hc
  nlinarith

/-- 用**符号**代替 `hmpos` 定住塌陷的方向：`gcd = 1` ＋ `dot nJ vl < 0` ⟹ `dot nJ vl = -1`。 -/
theorem sweep_eq_neg_one_of_sign {nJ vl p vJ1 : ℤ × ℤ} {c : ℕ} {m : ℤ}
    (hp : p = -(c : ℤ) • vl) (hm : vJ1 = m • vl) (hsign : dot nJ vl < 0)
    (hgcd : Int.gcd (dot nJ p) (-dot nJ vJ1) = 1) : dot nJ vl = -1 := by
  rcases dot_nJ_vl_isUnit hp hm hgcd with h | h
  · omega
  · exact h

/-! ## 第 233 轮：`Primitive vJ1` 把 `m` 钉成 `1`，hbase 的第三行随之恒真

lane-tower-hbase 第 233 轮以内核见证订正了上一版的一处**实质错误**，订正成立、我接受：

* 上一版说「`gcd = 1` 与 `dot nJ vl = ±1` **互相**蕴含，`gcd = 1` 一个新自由度都没给」。
  ⛔ 这句在**一般 `m`** 下为假。反向那条 `gcd_one_of_unit` 的 binder 里有 `hvJ1 : vJ1 = vl`
  （即 `m = 1` 写死），我却把结论当成对一般 `m` 成立的。由 `collapse` 自己的 `d = c`、`e = m`
  立刻看出正确的一般形式是 `gcd(d, e) = gcd(c, m)`，所以
  `gcd = 1 ⟺ |dot nJ vl| = 1 ∧ IsCoprime (c : ℤ) m`。hbase 的 `c = m = 2` 见证
  （`not_conj1_of_dot_nJ_vl`）逐字打中这一点。

**但那第三行不是一笔独立的债，是形式化漏掉的一条原文事实。** `vJ1` 就是论文的
`v⃗_{ℓ_{J−1}}`，而 `b3_colle2.txt:351` 逐字把 `v⃗_ℓ ∈ ℓ ∩ ℤ²` 定义为
「the non-zero vector parallel to `ℓ` of **minimum norm**」⟹ `Primitive vJ1` 是原文自带的，
要它**不是**「比原文强」（硬规矩 5）。而 `Primitive vl` 已经是 `exists_chainData` 的 binder
（`RegionSteps.lean:653`）。两条本原 ＋ 共线 ⟹ `IsUnit m` ⟹ 配符号得 `m = 1`，于是

* `IsCoprime (c : ℤ) m` ＝ `IsCoprime (c : ℤ) 1` **恒真**（`isCoprime_c_m_of_prim`）；
* `vJ1 = vl`（`vJ1_eq_vl_of_prim`）⟹ `unit_sweep_of_gcd_one` / `gcd_one_of_unit` 那条
  `hvJ1` binder 在链上**被生产**，不是被假设 ⟹ 上一版的等价性结论在链上**恢复**，
  但它现在明账地依赖 `Primitive vJ1`；
* hbase 的 `c = m = 2` 见证在链上不忠实：那里 `vJ1 = (0, -2)`，`Primitive (0, -2)` **为假**
  （`witnessA_vJ1_not_prim`）。⟹ 它否掉的是「只嚼算术 binder」的版本，不是加了 `:351` 的版本。

⟹ **净欠项回到一条**：`|dot nJ vl| = 1`（＝ `det vJ vl = ±1`）。⛔ 而这一条现在有两条独立的
不利证据，见下一节。
-/

/-- `Primitive vJ1` ＋ 共线 ⟹ `IsUnit m`。原文依据 `b3_colle2.txt:351`（`v⃗_ℓ` 取模最小）。 -/
theorem isUnit_m_of_prim {vl vJ1 : ℤ × ℤ} {m : ℤ}
    (hm : vJ1 = m • vl) (hprim : Primitive vJ1) : IsUnit m := by
  have hc : IsCoprime (m * vl.1) (m * vl.2) := by
    simpa [Primitive, hm, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] using hprim
  exact hc.isUnit_of_dvd' (dvd_mul_right m vl.1) (dvd_mul_right m vl.2)

/-- 两条本原 ＋ 共线 ＋ 符号 ⟹ `m = 1`，即 `vJ1 = vl`。 -/
theorem vJ1_eq_vl_of_prim {nJ vl vJ1 : ℤ × ℤ} {m : ℤ}
    (hm : vJ1 = m • vl) (hprim : Primitive vJ1)
    (hsweep : dot nJ vJ1 < 0) (hsign : dot nJ vl < 0) : vJ1 = vl := by
  have hmpos : 0 < m := m_pos_of_sign hm hsweep hsign
  have h1 : m = 1 := by
    rcases Int.isUnit_iff.mp (isUnit_m_of_prim hm hprim) with h | h
    · exact h
    · omega
  rw [hm, h1, one_smul]

/-- hbase 第三行恒真：`Primitive vJ1` 下 `m = 1`，故 `IsCoprime (c : ℤ) m` 白送。 -/
theorem isCoprime_c_m_of_prim {nJ vl vJ1 : ℤ × ℤ} {c : ℕ} {m : ℤ}
    (hm : vJ1 = m • vl) (hprim : Primitive vJ1)
    (hsweep : dot nJ vJ1 < 0) (hsign : dot nJ vl < 0) : IsCoprime ((c : ℤ)) m := by
  have hmpos : 0 < m := m_pos_of_sign hm hsweep hsign
  have h1 : m = 1 := by
    rcases Int.isUnit_iff.mp (isUnit_m_of_prim hm hprim) with h | h
    · exact h
    · omega
  rw [h1]; exact isCoprime_one_right

/-- ⛔ hbase 的 `c = m = 2` 见证在链上不忠实：它的 `vJ1 = (0, -2)` 不本原。 -/
theorem witnessA_vJ1_not_prim : ¬ Primitive ((0, -2) : ℤ × ℤ) := by
  intro h
  have h' : IsCoprime (0 : ℤ) (-2 : ℤ) := by simpa [Primitive] using h
  rw [isCoprime_zero_left, Int.isUnit_iff] at h'
  omega

/-- **第 233 轮的净结论**：加上 `:351` 的 `Primitive vJ1`，`gcd(d, e) = 1` 与
`dot nJ vl = -1` 在链上**等价**，第三行消失，欠项只剩大小那一半。 -/
theorem gcd_one_iff_of_prim {nJ vl p vJ1 : ℤ × ℤ} {c : ℕ} {m : ℤ}
    (hp : p = -(c : ℤ) • vl) (hm : vJ1 = m • vl) (hprim : Primitive vJ1)
    (hsweep : dot nJ vJ1 < 0) (hsign : dot nJ vl < 0) :
    Int.gcd (dot nJ p) (-dot nJ vJ1) = 1 ↔ dot nJ vl = -1 := by
  have hvJ1 : vJ1 = vl := vJ1_eq_vl_of_prim hm hprim hsweep hsign
  refine ⟨fun hgcd => sweep_eq_neg_one_of_sign hp hm hsign hgcd, fun h => ?_⟩
  exact gcd_one_of_unit (p := p) hvJ1 h

/-! ## ⛔ 第 233 轮：`|dot nJ vl| = 1` 有两条独立的不利证据

1. **算术 binder 组不钉大小**（lane-tower-hbase 的 `arith_fields_do_not_pin_magnitude`）：
   同一对 `nJ = (0,1)`、`vJ = (1,0)`，`vl = (0,-1)` 给 `dot nJ vl = -1`、`vl = (1,-3)` 给 `-3`，
   两行都兑现 `Primitive nJ` / `Primitive vJ` / `Primitive vl` / `hperp`，第二行还兑现
   `hp_neg`（`c = 1`）/ `hdet_vl` / `dot nJ p ≠ 0` / `dot nJ vl < 0`。
   ⟹ 产者**必须用几何**，只嚼本原性＋垂直＋共线＋`hsweep` 的路线到不了。
2. ⛔ **几何也不钉**（lane-env-refute 的 `EnvRefuteFaceNormal`，第 233 轮落地）：
   `S = {(0,0),(0,1),(1,2)}` 格凸、**正面积**（不是退化单点窗口），`nR = (-2,1)` 是它真正的
   面法向，`lex`/`lex'`/`edge`/`edge'` 逐字兑现 `ChainDataGeom` 的同名面字段，而
   `dot nR vlR = -2`，且 `vJ1R = vlR`（`m = 1`，本原）⟹ **本轮上面那条 `m = 1` 的补强也救不了它。**
   ⚠ 射程（env-refute 自己列全）：`hξ` / `hw*` / `hℓ_*` / `hxper` / `hp_mem` / `hdet_ℓ` /
   `hpartner` / `hcase2` 以及除面字段外的全部 `ChainDataGeom` 字段都**没喂**；`r` 钉成 `1`
   是 a fortiori 方向，安全。
3. **原文层面同向**（lane-hole3-nlmax）：`b3_colle2.txt:420-432`（Lemma 3.5）只把 `J` 夹到
   `ι+1 ≤ J ≤ ι+m-1`，**不是** `J = ι+1` 相邻；`S_φ` 是 `h_1,…,h_m` 上的 zonotope，
   其**非相邻**边方向的行列式没有理由是 `±1`。⚠ nlmax 未读完 `:432` 之后到 Lemma 4.1/4.4
   是否把 `J` 收紧，故这条是「指征」不是「已判」。

⟹ ⛔ **裁决（第 233 轮）**：不再往「证明 `|dot nJ vl| = 1`」投人力。合取 1 的出路改走
env-refute 的**尖锐判据** `heights_iff_cover`（`gcd = 1` 只是充分条件，严格更强），
或在 `:432`–Lemma 4.4 里找到原文真正用来保证合取 1 的那句。
-/

end Nivat.GcdCollapse

/-! ## 公理审计（分母＝本文件声明数 17，含 private） -/

#print axioms Nivat.GcdCollapse.dotZ
#print axioms Nivat.GcdCollapse.dvd_d
#print axioms Nivat.GcdCollapse.dvd_e
#print axioms Nivat.GcdCollapse.dot_nJ_vl_isUnit
#print axioms Nivat.GcdCollapse.collapse
#print axioms Nivat.GcdCollapse.e_eq_one_of_unit
#print axioms Nivat.GcdCollapse.unit_sweep_of_gcd_one
#print axioms Nivat.GcdCollapse.gcd_one_of_unit
#print axioms Nivat.GcdCollapse.det_p_vJ1_zero
#print axioms Nivat.GcdCollapse.not_det_unit
#print axioms Nivat.GcdCollapse.m_pos_of_sign
#print axioms Nivat.GcdCollapse.sweep_eq_neg_one_of_sign
#print axioms Nivat.GcdCollapse.isUnit_m_of_prim
#print axioms Nivat.GcdCollapse.vJ1_eq_vl_of_prim
#print axioms Nivat.GcdCollapse.isCoprime_c_m_of_prim
#print axioms Nivat.GcdCollapse.witnessA_vJ1_not_prim
#print axioms Nivat.GcdCollapse.gcd_one_iff_of_prim
