/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.RegionSweep
import Nivat.External.Colle.L1RegionBuild

/-!
# `ConeRegion` — The paper's `𝓡_{ι-1}`, a two-ray cone

原文：b3_colle2.txt:784
⚠ **订正（第 199 轮，集成者 `sed` 实测每一行）：本文件初稿通篇引 `:780`，那是「Claim 4.6.」
这个**标签行**，不是公式；公式在 `:784`，型号断言在 `:786`。下面的 `:780` 已逐处改为 `:784`。**

The paper defines:
```
𝓡_{ι-1} := {g + t·v⃗_{ℓ_{ι-1}} ∈ ℤ² : g ∈ H_B(ℓ), t ∈ ℤ₊}
```

where `H_B(ℓ) = {g + t·v⃗_ℓ : g ∈ B, t ∈ ℤ₊}` is the half-strip (**line `:414`**).
⚠ **订正：初稿写 `:777`，那是空行。** `H_B(ℓ)` 的定义在 `:414`（§3，远早于 Claim 4.6）；
`:777` 附近只是**使用**它。§57 乙类（引用指向的行不含被引内容）。

Expanding: `𝓡_{ι-1} = {b + s·v⃗_ℓ + t·v⃗_{ℓ_{ι-1}} : b ∈ B, s,t ∈ ℤ₊}`.

This is **a two-ray cone**, not a half-strip. The two ray directions are `vl` (along `ℓ`)
and `u'` (along `ℓ_{ι-1}`), and they are distinct non-expansion lines, so **not parallel**.

Key difference from `wedgeFull` (L1RegionBuild.lean:230):
- `wedgeFull B vl u' = sweep (fullSweep B vl) u'`, where `fullSweep` sweeps along `±vl`
  (both directions).
- `coneRegion B vl u' = sweep (sweep B vl) u'`, where `sweep` only uses `t ∈ ℤ₊`
  (single direction).

`wedgeFull` is strictly larger, which likely explains why
`not_isLatticeConvexRegion_fullSweep_S2` refutes it — the counterexample hits the
enlarged object, not the paper's actual construction.

## Quantifier correspondence with b3_colle2.txt:784

- `b ∈ B` ↔ `g ∈ B` (base point in the seed)
- `s : ℕ` ↔ `s ∈ ℤ₊` (steps along `v⃗_ℓ`, the `ℓ` direction)
- `t : ℕ` ↔ `t ∈ ℤ₊` (steps along `v⃗_{ℓ_{ι-1}}`, the `ℓ_{ι-1}` direction)
- `z = b + (s:ℤ)•vl + (t:ℤ)•u'` ↔ `g + s·v⃗_ℓ + t·v⃗_{ℓ_{ι-1}}`

⚠ `ℕ ≡ ℤ₊` 是**字面**相等，不是转写缝：`:38` 逐字「We use `ℕ={1,2,…}` and `ℤ₊=ℕ∪{0}`」。

## 🔴 (u3) 报假：上表第 3、4 行的 `u' ↔ v⃗_{ℓ_{ι-1}}` 为**假**

**第 199 轮（lane-towerpkg 提出并给内核见证，集成者独立数值复核后采纳）。**
上面这张表除「`u'` 认成 `v⃗_{ℓ_{ι-1}}`」外逐条成立；**坏的恰是那一条**，而且两侧都是硬事实：

* **链侧（内核）**：`det u' vl = -1`。只用 `exists_cutResidualR_of_claim46` 的原生 binder
  `hprim` / `hvl_prim` / `hperp` / `hdetpos` / `hnu`——机制是恒等式 `dot nℓ x = det x vl`，
  于是 `hnu : dot nℓ u' = -1` 逐字就是 `det u' vl = -1`。
  ⟹ `det vl u' = +1 > 0` ⟹ **`u'` 在 `vl` 的逆时针侧（successor 侧）**。
  集成者数值复核：`nℓ=(1,0)`、`vl=(0,1)`、`u'=(-1,0)` ⟹ `det u' vl = -1` ✓。
* **原文侧**：`:786` 断言 `𝓡_{ι-1}` 是 `(-ℓ, ℓ_{ι-1})`-region，`:388`（Definition 3.1 的释义）
  逐字「following the orientation of `𝓡`, the edge parallel to `ℓ` comes **first**」。
  一般事实：锥 `B + ℤ₊a + ℤ₊b`（`det a b > 0`）的正定向边界是「沿 `-b` 进 → 角点 → 沿 `+a` 出」，
  故型号为 `(-b, a)`。代入 `b = v⃗_ℓ`、`a = v⃗_{ℓ_{ι-1}}` ⟹ **`det (v⃗_{ℓ_{ι-1}}) (v⃗_ℓ) > 0`**。
  集成者数值复核（硬规矩 6）：`a=(1,0)`、`b=(0,1)`、`det a b = 1 > 0`，第一象限锥的逆时针边界
  确是「沿 `(0,-1)` 下行 → 原点 → 沿 `(1,0)` 出」＝ `(-b, a)` ✓。

⟹ 原文要 `det u' vl > 0`，链上是 `-1`。**符号相反，`coneRegion B vl u' ≠ 𝓡_{ι-1}`。**
lane-towerpkg 的 `coneRegion_ne_of_det_pos` 把这条做成了消费者现场的内核反例
（`hBfin`/`hBne` 也是原生 binder，不是抽象反例）。

⚠ **承重假设，按 §50 如实标出**：两步原文推理都过「positively oriented ＝ 逆时针」。
若读成顺时针，型号公式翻成 `(-a, b)`，(u3) 反而为真。全文 grep
"counterclockwise/clockwise/ccw/cw" **零命中**（lane-hole3-cone 实测），所以这一比特的出处
在 Green 公式式的通用惯例，不在本文里。**本文件与 `NormalCycle.lean` 的 `step` 字段采同一约定**
（逆时针），两处必须同进同退——改一处就得改另一处。

⚠ **本条**不**说链上的锥造错了。** 它只说「链上的锥 ＝ 原文 `𝓡_{ι-1}`」这个认同为假。
链上的锥是 `𝓡_{ι-1}` 沿 `ℓ` 方向的**镜像**（两者共用 `vl` 那条边）。

## ⚖ 裁决（第 200 轮，规矩 17）：`hnu` 的符号**不改**，且 (u3) **不承重**

第 199 轮这里留了两支（「翻 `hnu`」／「其实是 Case 2」），都已裁掉：

**支一「翻 `hnu` 得到镜像」——否。** `det u' vl = -1` 不是可选的约定，是四条现成 binder
（`hvl_prim` / `hperp` / `hdetpos` / `hnu`）的算术后果，见主仓
`RegionNlDict.nl_eq_neg_dir_vl_and_det_u'`（`RegionNlDict.lean:86`）。
lane-env-refute 把三条路都做成了内核见证（`tmp/wip/lane-env-refute-mirror.lean`，EXIT=0，
集成者独立重跑，45 行公理全白）：
`no_legal_mirror`（`:128`）—— 四条 binder 与 `det u' vl = 1` **不相容**；
`route_flip_nl_breaks_hdetpos`（`:134`）—— 只翻 `nℓ`，`hdetpos` 当场破；
`route_flip_both_is_not_mirror`（`:150`）—— 翻 `nℓ`+`vl` 保住 binder 但**不是镜像**；
`route_flip_u'_breaks_hwneg`（`:158`）—— 翻 `u'` 才是真镜像，代价是 `hnu` 变 `+1`
**且 `hwneg` 在每一档同时翻号**（三档实测），不是改一个签名能吸收的。

**支二「其实是 Case 2」——型号猜错，且改判不走这个定理。** lane-hole3-cone 逐行读了
`:886-934`：Case 2 的区域是 **`(ℓ, ℓ_J)`**-region（`:892`/`:900`/`:928` 三处逐字一致），
**不是**这里先前猜的 `(-ℓ, ℓ_{ι+m-1})`。它要 `det (v⃗_{ℓ_J}) (v⃗_ℓ) < 0`，**与链上的 `-1` 同号**；
但消费者 `exists_cutResidualR_of_claim46` 的 binder 在结构上是 Case 1 的
（`hbase₁` 是**肯定式**周期性断言，Case 2 的假设是全称式失败），所以「重新贴标签」不成立——
真要走 Case 2，得另立一条 Case-2 形状的定理。

**⟹ 净结论：(u3) 报假成立且不撤，但它对洞 3 的矛盾**不承重**。** 理由是语句形状：
`hstrict : ∀ b ∈ Sφ, dot m a < dot m b → dot nℓ b ≤ dot nℓ a` 里**只出现 `m`、`a`、`nℓ`、`Sφ`**，
`u'` / `vl` / `det u' vl` 一个都不出现，所以翻 `u'` 的符号只能换「链把哪个方向排到第 0 档」，
改不了任何一档的真假。lane-env-refute 在具体台架上把这件事量化了
（`hstrict_true_iff_dir_eq`，`:352`：八档里 `hstrict` **恰在方向 `(-1,-1)` 一档为真**，
与下标、与 `u'`、与 `det u' vl` 的符号都无关；`true_dir_is_neither_seed`，`:379`：
那一档**既不是**原台架的种子端**也不是**镜像台架的种子端）。
⚠ 按 §50 标清等级：`hstrict_true_iff_dir_eq` 是**具体台架上的 `decide`**，管的是那个台架；
「`hstrict` 的类型不提 `u'`」才是一般性的，那一条靠读语句本身，不靠台架。
⟹ 矛盾的真正位置在「链上那一档的 `w` 是不是 `(-1,-1)`」，即 `hwadj` / 扇邻接那一侧，
**不在符号约定上**。这条把洞 3 的搜索面从「签名可能写反了」缩回「几何断言本身」。

-/

set_option autoImplicit false

namespace Nivat.ConeRegion

open Nivat Nivat.RegionSweep Nivat.LE2

/-- `ℤ`-scaling on `ℤ × ℤ`, componentwise. -/
theorem zsmul_prod (t : ℤ) (v : ℤ × ℤ) : t • v = (t * v.1, t * v.2) := rfl

/-- `dot` is `ℤ`-linear in its second argument. (`Nivat.LE2.dot_smul` scales the *first*.) -/
theorem dot_zsmul (n : ℤ × ℤ) (t : ℤ) (v : ℤ × ℤ) :
    Nivat.LE2.dot n (t • v) = t * Nivat.LE2.dot n v := by
  simp only [Nivat.LE2.dot, zsmul_prod]; ring

/-- **The paper's `𝓡_{ι-1}`, a two-ray cone.**

原文：b3_colle2.txt:784 — `𝓡_{ι-1} := {g + t·v⃗_{ℓ_{ι-1}} ∈ ℤ² : g ∈ H_B(ℓ), t ∈ ℤ₊}`.

Quantifiers:
- `b ∈ B` (base point)
- `s : ℕ` (steps along `vl`)
- `t : ℕ` (steps along `u'`)
- Result: `b + s•vl + t•u'`

This is `sweep (sweep B vl) u'` — apply `sweep` twice, once in each ray direction. -/
def coneRegion (B : Set (ℤ × ℤ)) (vl u' : ℤ × ℤ) : Set (ℤ × ℤ) :=
  Nivat.RegionSweep.sweep (Nivat.RegionSweep.sweep B vl) u'

/-- Membership in `coneRegion` means `z = b + s•vl + t•u'` for some `b ∈ B` and `s, t : ℕ`.

原文：b3_colle2.txt:784 — this is the expansion of `𝓡_{ι-1}` from `H_B(ℓ)`. -/
theorem mem_coneRegion_iff {B : Set (ℤ × ℤ)} {vl u' z : ℤ × ℤ} :
    z ∈ coneRegion B vl u' ↔ ∃ b ∈ B, ∃ s t : ℕ, z = b + (s : ℤ) • vl + (t : ℤ) • u' := by
  unfold coneRegion
  constructor
  · rintro ⟨g, ⟨b, hb, s, rfl⟩, t, rfl⟩
    exact ⟨b, hb, s, t, rfl⟩
  · rintro ⟨b, hb, s, t, rfl⟩
    exact ⟨b + (s : ℤ) • vl, ⟨b, hb, s, rfl⟩, t, rfl⟩

/-- The half-strip `halfStrip B vl` is contained in `coneRegion B vl u'` (taking `t = 0`).

原文：b3_colle2.txt:414+:784 — `H_B(ℓ) ⊆ 𝓡_{ι-1}` by definition（取 `t = 0`）. -/
theorem halfStrip_subset_coneRegion {B : Set (ℤ × ℤ)} {vl u' : ℤ × ℤ} :
    Nivat.LE2.halfStrip B vl ⊆ coneRegion B vl u' := by
  rintro z ⟨g, hg, t, rfl⟩
  rw [mem_coneRegion_iff]
  exact ⟨g, hg, t, 0, by simp⟩

/-- `coneRegion` is closed under adding `vl` (the first ray direction).

原文：b3_colle2.txt:784 — if `z = b + s•vl + t•u'`, then `z + vl = b + (s+1)•vl + t•u'`. -/
theorem add_vl_mem {B : Set (ℤ × ℤ)} {vl u' z : ℤ × ℤ}
    (hz : z ∈ coneRegion B vl u') :
    z + vl ∈ coneRegion B vl u' := by
  rw [mem_coneRegion_iff] at hz ⊢
  obtain ⟨b, hb, s, t, rfl⟩ := hz
  refine ⟨b, hb, s + 1, t, ?_⟩
  simp only [Nat.cast_add, Nat.cast_one, add_smul]
  module

/-- `coneRegion` is closed under adding `u'` (the second ray direction).

原文：b3_colle2.txt:784 — if `z = b + s•vl + t•u'`, then `z + u' = b + s•vl + (t+1)•u'`. -/
theorem add_u'_mem {B : Set (ℤ × ℤ)} {vl u' z : ℤ × ℤ}
    (hz : z ∈ coneRegion B vl u') :
    z + u' ∈ coneRegion B vl u' := by
  rw [mem_coneRegion_iff] at hz ⊢
  obtain ⟨b, hb, s, t, rfl⟩ := hz
  refine ⟨b, hb, s, t + 1, ?_⟩
  simp only [Nat.cast_add, Nat.cast_one, add_smul]
  module

/-- **Horizontal layer decomposition of the cone.**

原文：b3_colle2.txt:792-804 — the sweep conquers lines `A_i := 𝓡_{ι-1} ∩ l_i`, where
`l_i` is the `i`-th line parallel to `vl`.

Quantifiers:
- `n : ℤ × ℤ` — transverse normal (perpendicular to `vl`)
- `hperp : dot n vl = 0` — `n ⊥ vl` (line :792, lines parallel to `ℓ`)
- `hstep : dot n u' = -1` — each step along `u'` crosses exactly one line (line :803-804,
  "proceeding this way" implies uniform steps)
- `z ∈ coneRegion B vl u'` — a point in `𝓡_{ι-1}`
- Conclusion: `∃ t : ℕ, dot n z = c₀ - t` for some reference level `c₀`

The level is measured **relative to the base point `b` the point came from**, not
relative to any single reference level of `B`.  See the retraction note below for why the
`suppVal` form is false. -/
theorem dot_eq_of_mem_coneRegion {B : Set (ℤ × ℤ)} {vl u' : ℤ × ℤ} {n : ℤ × ℤ}
    (hperp : Nivat.LE2.dot n vl = 0)
    (hstep : Nivat.LE2.dot n u' = -1)
    {z : ℤ × ℤ} (hz : z ∈ coneRegion B vl u') :
    ∃ b ∈ B, ∃ t : ℕ, Nivat.LE2.dot n z = Nivat.LE2.dot n b - (t : ℤ) := by
  rw [mem_coneRegion_iff] at hz
  obtain ⟨b, hb, s, t, rfl⟩ := hz
  refine ⟨b, hb, t, ?_⟩
  calc Nivat.LE2.dot n (b + (s : ℤ) • vl + (t : ℤ) • u')
      = Nivat.LE2.dot n b + Nivat.LE2.dot n ((s : ℤ) • vl) + Nivat.LE2.dot n ((t : ℤ) • u') := by
        simp only [Nivat.LE2.dot_add]
    _ = Nivat.LE2.dot n b + (s : ℤ) * Nivat.LE2.dot n vl + (t : ℤ) * Nivat.LE2.dot n u' := by
        simp only [dot_zsmul]
    _ = Nivat.LE2.dot n b + (s : ℤ) * 0 + (t : ℤ) * (-1) := by
        rw [hperp, hstep]
    _ = Nivat.LE2.dot n b - (t : ℤ) := by ring

/-- Every point of the cone sits at or below the top `n`-level of the base `B`.

原文：b3_colle2.txt:784 — the cone opens in the `-n` direction (`dot n u' = -1`), so
sweeping never raises the level above `B`'s own maximum. -/
theorem dot_le_suppVal_of_mem_coneRegion {B : Set (ℤ × ℤ)} {vl u' : ℤ × ℤ} {n : ℤ × ℤ}
    (hfin : B.Finite) (hne : B.Nonempty)
    (hperp : Nivat.LE2.dot n vl = 0)
    (hstep : Nivat.LE2.dot n u' = -1)
    {z : ℤ × ℤ} (hz : z ∈ coneRegion B vl u') :
    Nivat.LE2.dot n z ≤ Nivat.LE2.suppVal B n := by
  obtain ⟨b, hb, t, hlev⟩ := dot_eq_of_mem_coneRegion hperp hstep hz
  have hble : Nivat.LE2.dot n b ≤ Nivat.LE2.suppVal B n := Nivat.LE2.le_suppVal hfin hne hb
  have ht : (0 : ℤ) ≤ (t : ℤ) := Int.natCast_nonneg t
  omega

/-! ### 撤回 (2026-09-20, 集成者): `mem_coneRegion_of_level` 的 `suppVal` 形式

原稿结论是 `∃ t : ℕ, dot n z = suppVal B (-n) - t`，带 `sorry` 落进主仓（红线违例）。
**它不是「没证出来」，是假的**：`mem_coneRegion_iff` 解出来的 `b` 是 `B` 的**任意**元素，
最后一步要的 `dot n b = suppVal B (-n)`（`b` 恰好取到 `B` 的 `n`-最小值）对
`B = {(0,0), (0,1)}`、`n = (0,1)` 立刻为假：从 `b = (0,1)` 出发的点与从 `b = (0,0)` 出发的
点差一层，两者不可能同时写成同一个 `suppVal` 减自然数。

原稿 docstring 说「`c₀` 是 `halfStrip B vl` 上 `dot n ·` 的最大值」——那是 `suppVal B n`，
**不是** `suppVal B (-n)`，签名与说明本身就不一致。

替代物两条，都已证：`dot_eq_of_mem_coneRegion`（层级相对于**点自己的**基点 `b`）与
`dot_le_suppVal_of_mem_coneRegion`（对 `B` 的最大层的单边界，这一条才是横向扫掠要用的）。 -/

end Nivat.ConeRegion

#print axioms Nivat.ConeRegion.mem_coneRegion_iff
#print axioms Nivat.ConeRegion.halfStrip_subset_coneRegion
#print axioms Nivat.ConeRegion.add_vl_mem
#print axioms Nivat.ConeRegion.add_u'_mem
#print axioms Nivat.ConeRegion.dot_eq_of_mem_coneRegion
#print axioms Nivat.ConeRegion.dot_le_suppVal_of_mem_coneRegion
