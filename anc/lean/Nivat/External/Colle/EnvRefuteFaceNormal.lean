/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.ShellLine
import Nivat.External.Colle.EnvRefuteCover
import Nivat.External.Colle.ChainMax
import Nivat.Defs.Complexity

/-!
# `|⟪n_J, v_ℓ⟫| = 1` 不是面法向 binder 组的定理

集成者的 `GcdCollapse.lean` 把 `gcd (dot nJ p) (-dot nJ vJ1) = 1` 与 `dot nJ vl = -1`
在链上互相蕴含 ⟹ 「`bottom` 合取 1 欠 `gcd = 1` 的产者」与「欠 `dot nJ vl = -1` 的产者」
是同一笔债。本文件给出该债**不能由几何 binder 组偿还**的内核见证。

## 居民

| 对象 | 值 | 备注 |
|---|---|---|
| `nR` | `(-2, 1)` | `Primitive`；`dot nR vlR = -2` |
| `vJR` | `(1, 2)` | `Primitive`；`dot nR vJR = 0` |
| `vlR` | `(1, 0)` | `Primitive` |
| `pR` | `(-1, 0)` | `= -(1:ℤ) • vlR`，`det pR vlR = 0` |
| `vJ1R` | `(1, 0)` | `= (1:ℤ) • vlR`，`dot nR vJ1R = -2 < 0` |
| `SR` | `{(0,0), (0,1), (1,2)}` | 格凸，**正面积**（面积 `1/2`） |
| 面 | `aR = (0,0)`，`a'R = (1,2)`，`r = 1` | `nR`-极小层，恰两点 |

⭐ **`nR` 真的是 `SR` 的面法向**，不是硬塞的参数：`latticeConvex_SR` / `lex_SR` /
`lex'_SR` / `edge_SR` / `edge'_SR` 逐条兑现 `ChainGeom.lean` 的 `ChainDataGeom` 同名字段
（`latticeConvex_S` / `lex` / `lex'` / `edge` / `edge'` / `dot_nJ_vJ`），语句逐量词照抄。

⚠ **故意不取退化窗口。** `SR` 面积 `1/2 > 0`、三个点不共线。单点窗口（如
`Step_PeriodsRays2.lean` 的 `Sw = {0}`）能满足面字段是因为它退化，那种见证对「正面积窗口
上如何」一个字没测 —— 本文件避开该反驳。

## 结论与⛔射程

`unit_dot_nJ_vl_not_of_face_binders`：把 `Primitive nJ/vJ/vl`、`dot nJ vJ = 0`、
`LatticeConvex S`、`a, a' ∈ S`、`lex`、`lex'`、`edge`、`edge'`、`p ≠ 0`、`det p vl = 0`、
`hp_neg`、共线 `vJ1 = m • vl (0 < m)`、`hsweep`、`dot nJ p ≠ 0` **全部**喂饱，
`dot nJ vl = -1` **仍不成立**。

⛔ **这不是说 `exists_chainData` 的结论为假。** 没喂的 binder 逐条列出，一条不藏：
`hξ : IsMinimalCounterexample ξ`、`hw/hw₁/hw₂`、`hℓ_nel/hℓ_pos/hℓ_neg`、`hxper`、
`hp_mem : p ∈ Per xper`、`hdet_ℓ : dot ℓ vl = 0`、`hpartner`、`hcase2`，以及
`ChainDataGeom` 除面字段外的其余字段（`bottom`、`shellSubStrip`、`rec_p`、… ）。
⟹ 本文件只证**一件事**：`|dot nJ vl| = 1` **不是上面那组几何 binder 的推论**。
若它在链上仍真，理由必须来自上面那张「没喂」的清单，而不是来自面几何。

⭐ **与 `cgc` 的关键差别**：集成者 `GcdCollapse.lean` 记「`cgc` 连 `hdet_vl : det p vl = 0`
都不满足 ⟹ 它不否掉『`exists_chainData` 的 binder ⊨ `|dot nJ vl| = 1`』，后者仍未定」。
本居民 **满足** `hdet_vl`（`det_pR_vlR`），所以它打的正是那个「仍未定」的靶。

⚠ 本文件不构造 `ChainDataGeom` 居民，也不主张能构造（`ξ` / `xper` 全未给）。
按 `AResidual.lean` 的记法，这是 binder 层的读数，不是链上义务的读数。

⭐ §7 另给**加强版** `unit_dot_nJ_vl_not_of_face_binders_prim`：再加一条 `Primitive vJ1`
（原文 `b3_colle2.txt:351` 供得出、Lean 字段表里现在没有的那条）结论依旧假
⟹ 「补 `vJ1_prim` 字段」这条路救不了 `|dot nJ vl| = 1`。

⛔ **`SR` 不是忠实的 `S_φ`（集成者第 235 轮补的射程，我照记）**：原文的 `S_φ` 是
`φ(X) = ∏(X^{h_i} - 1)` 的 Newton 多边形，即 `h_1,…,h_m` 上的 zonotope，因而**中心对称**；
`SR = {(0,0), (0,1), (1,2)}` 是三角形，不中心对称。⚠ 这**不削弱**本文件的结论 ——
结论是「`|dot nJ vl| = 1` 不是**面法向 binder 组**的定理」，而面字段里没有 zonotope 结构，
`hxper` 也明列为未喂。记这条是为了封死「换个中心对称的 `S` 就好了」那条回头路：
**那条路也不通**，因为 zonotope 的边方向就是那些 `h_i`，而 `det (h_i, h_j)` 可以任意大
（取 `h_1 = (3,1)`、`h_2 = (1,3)` 得 `8`）。⚠ 该 zonotope 读数为集成者所报，我未复核。

⭐ §8 是本文件的**正向**一半：合取 1 高度部分的尖锐判据，以及 `|dot nJ vl| = 2` 时它
**仍然成立**的共线见证 ⟹ 幺模性对合取 1 的高度部分不是必要条件。
-/

namespace Nivat.EnvRefuteFaceNormal

open Nivat Nivat.LE2 Nivat.MaxEnv Nivat.EnvRefuteCover

/-! ## §1 居民 -/

def nR : ℤ × ℤ := (-2, 1)
def vJR : ℤ × ℤ := (1, 2)
def vlR : ℤ × ℤ := (1, 0)
def pR : ℤ × ℤ := (-1, 0)
def vJ1R : ℤ × ℤ := (1, 0)
def aR : ℤ × ℤ := (0, 0)
def a'R : ℤ × ℤ := (1, 2)

/-- 三点窗口，**正面积**（面积 `1/2`）。 -/
def SR : Finset (ℤ × ℤ) := {(0, 0), (0, 1), (1, 2)}

theorem mem_SR {z : ℤ × ℤ} : z ∈ SR ↔ z = (0, 0) ∨ z = (0, 1) ∨ z = (1, 2) := by
  simp [SR]

/-! ## §2 本原性与正交性 -/

theorem prim_nR : Primitive nR := isCoprime_one_right

theorem prim_vJR : Primitive vJR := isCoprime_one_left

theorem prim_vlR : Primitive vlR := isCoprime_one_left

/-- ⭐ **`Primitive vJ1` 也满足** —— 见 §7，这条是本居民与 lane-tower-hbase 的 `c = m = 2`
见证的分水岭。 -/
theorem prim_vJ1R : Primitive vJ1R := isCoprime_one_left

/-- `ChainDataGeom.dot_nJ_vJ`。 -/
theorem dot_nR_vJR : dot nR vJR = 0 := by norm_num [dot, nR, vJR]

/-! ## §3 格凸性

`Conv SR` 关在三个半平面的交里，其格点恰为那三个顶点。 -/

/-- 三角形 `(0,0) (0,1) (1,2)` 的支撑半平面之交。 -/
def KR : Set (ℝ × ℝ) := {q | 0 ≤ q.1 ∧ 2 * q.1 - q.2 ≤ 0 ∧ q.2 - q.1 ≤ 1}

theorem convex_KR : Convex ℝ KR := by
  rintro u ⟨h1, h2, h3⟩ v ⟨k1, k2, k3⟩ s t hs ht hst
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  · nlinarith
  · nlinarith
  · nlinarith

theorem latticeConvex_SR : LatticeConvex SR := by
  intro z hz
  have hsub : Conv SR ⊆ KR := by
    apply convexHull_min _ convex_KR
    rintro _ ⟨w, hw, rfl⟩
    rw [Finset.mem_coe, mem_SR] at hw
    rcases hw with rfl | rfl | rfl <;>
      refine ⟨by norm_num [toReal], by norm_num [toReal], by norm_num [toReal]⟩
  obtain ⟨h1, h2, h3⟩ := hsub hz
  simp only [toReal] at h1 h2 h3
  have e1 : (0 : ℤ) ≤ z.1 := by exact_mod_cast h1
  have e2 : 2 * z.1 - z.2 ≤ 0 := by exact_mod_cast h2
  have e3 : z.2 - z.1 ≤ 1 := by exact_mod_cast h3
  rw [mem_SR, Prod.ext_iff, Prod.ext_iff, Prod.ext_iff]
  simp only []
  omega

/-! ## §4 面字段：`nR` 是 `SR` 在 `nR`-极小层上的面法向

四条语句逐量词照抄 `ChainGeom.lean` 的 `ChainDataGeom.lex` / `lex'` / `edge` / `edge'`，
只把 `S`、`nJ`、`vJ`、`a`、`a'`、`r` 换成本文件的具体值。 -/

theorem aR_mem : aR ∈ SR := by rw [mem_SR]; left; rfl

theorem a'R_mem : a'R ∈ SR := by rw [mem_SR]; right; right; rfl

/-- `ChainDataGeom.lex`：`a` 对 `(-n_J, -v_J)` 严格极值。 -/
theorem lex_SR : ∀ b ∈ SR.erase aR,
    dot (-nR) b < dot (-nR) aR ∨ (dot (-nR) b = dot (-nR) aR ∧ dot (-vJR) b < dot (-vJR) aR) := by
  intro b hb
  rw [Finset.mem_erase, mem_SR] at hb
  obtain ⟨hne, hb⟩ := hb
  rcases hb with rfl | rfl | rfl
  · exact absurd rfl hne
  · left; norm_num [dot, nR, aR]
  · right; constructor <;> norm_num [dot, nR, vJR, aR]

/-- `ChainDataGeom.lex'`：`a'` 对 `(-n_J, v_J)` 严格极值。 -/
theorem lex'_SR : ∀ b ∈ SR.erase a'R,
    dot (-nR) b < dot (-nR) a'R ∨ (dot (-nR) b = dot (-nR) a'R ∧ dot vJR b < dot vJR a'R) := by
  intro b hb
  rw [Finset.mem_erase, mem_SR] at hb
  obtain ⟨hne, hb⟩ := hb
  rcases hb with rfl | rfl | rfl
  · right; constructor <;> norm_num [dot, nR, vJR, a'R]
  · left; norm_num [dot, nR, a'R]
  · exact absurd rfl hne

/-- `ChainDataGeom.edge`：其余点或在面上（`a + j • v_J`，`1 ≤ j ≤ r`），或严格更高。
这里 `r = 1`。 -/
theorem edge_SR : ∀ b ∈ SR.erase aR,
    (∃ j : ℕ, 1 ≤ j ∧ j ≤ 1 ∧ b = aR + (j : ℤ) • vJR) ∨ 1 ≤ dot nR (b - aR) := by
  intro b hb
  rw [Finset.mem_erase, mem_SR] at hb
  obtain ⟨hne, hb⟩ := hb
  rcases hb with rfl | rfl | rfl
  · exact absurd rfl hne
  · right; norm_num [dot, nR, aR]
  · left; exact ⟨1, le_refl 1, le_refl 1, by norm_num [aR, vJR, Prod.ext_iff]⟩

/-- `ChainDataGeom.edge'`：`a'` 一侧的镜像。 -/
theorem edge'_SR : ∀ b ∈ SR.erase a'R,
    (∃ j : ℕ, 1 ≤ j ∧ j ≤ 1 ∧ b = a'R - (j : ℤ) • vJR) ∨ 1 ≤ dot nR (b - a'R) := by
  intro b hb
  rw [Finset.mem_erase, mem_SR] at hb
  obtain ⟨hne, hb⟩ := hb
  rcases hb with rfl | rfl | rfl
  · left; exact ⟨1, le_refl 1, le_refl 1, by norm_num [a'R, vJR, Prod.ext_iff]⟩
  · right; norm_num [dot, nR, a'R]
  · exact absurd rfl hne

/-! ## §5 `exists_chainData` 一侧的向量 binder -/

theorem pR_ne : pR ≠ 0 := by norm_num [pR, Prod.ext_iff]

/-- `exists_chainData` 的 `hdet_vl`。 -/
theorem det_pR_vlR : det pR vlR = 0 := by norm_num [det, pR, vlR]

/-- `exists_chainData` 的 `hp_neg`（2026-09-23 集成者加的那条）。 -/
theorem hp_neg_R : ∃ c : ℕ, 0 < c ∧ pR = -(c : ℤ) • vlR :=
  ⟨1, one_pos, by norm_num [pR, vlR, Prod.ext_iff]⟩

/-- 共线裁决 `vJ1 = m • vl`，`0 < m`。 -/
theorem collinear_R : ∃ m : ℕ, 0 < m ∧ vJ1R = (m : ℤ) • vlR :=
  ⟨1, one_pos, by norm_num [vJ1R, vlR, Prod.ext_iff]⟩

/-- `ChainDataGeom.dot_nJ_vJ1_neg`（`hsweep`）。 -/
theorem sweep_R : dot nR vJ1R < 0 := by norm_num [dot, nR, vJ1R]

/-- `ChainDataGeom.dot_nJ_p`。 -/
theorem dot_nR_pR : dot nR pR ≠ 0 := by norm_num [dot, nR, pR]

/-- ⭐ 关键读数：步长的法向分量是 **2**，不是 1。 -/
theorem dot_nR_vlR : dot nR vlR = -2 := by norm_num [dot, nR, vlR]

/-! ## §6 ⭐ 结论 -/

/-- ⭐⭐ **`dot nJ vl = -1` 不是面法向 binder 组的推论。**

十六条前提全部喂饱（本原性三条、正交、格凸、两个端点属于 `S`、四条面字段、
`p ≠ 0`、`det p vl = 0`、`hp_neg`、共线、`hsweep`、`dot nJ p ≠ 0`），结论仍假。

⛔ 射程见模块头：没喂的 binder（`hξ`、`hpartner`、`hcase2`、`hp_mem`、`hdet_ℓ`、
`ChainDataGeom` 的非面字段）逐条列在那里。 -/
theorem unit_dot_nJ_vl_not_of_face_binders :
    ¬ ∀ (nJ vJ vl p vJ1 a a' : ℤ × ℤ) (S : Finset (ℤ × ℤ)),
        Primitive nJ → Primitive vJ → Primitive vl →
        dot nJ vJ = 0 →
        LatticeConvex S → a ∈ S → a' ∈ S →
        (∀ b ∈ S.erase a,
          dot (-nJ) b < dot (-nJ) a ∨ (dot (-nJ) b = dot (-nJ) a ∧ dot (-vJ) b < dot (-vJ) a)) →
        (∀ b ∈ S.erase a',
          dot (-nJ) b < dot (-nJ) a' ∨ (dot (-nJ) b = dot (-nJ) a' ∧ dot vJ b < dot vJ a')) →
        (∀ b ∈ S.erase a,
          (∃ j : ℕ, 1 ≤ j ∧ j ≤ 1 ∧ b = a + (j : ℤ) • vJ) ∨ 1 ≤ dot nJ (b - a)) →
        (∀ b ∈ S.erase a',
          (∃ j : ℕ, 1 ≤ j ∧ j ≤ 1 ∧ b = a' - (j : ℤ) • vJ) ∨ 1 ≤ dot nJ (b - a')) →
        p ≠ 0 → det p vl = 0 → (∃ c : ℕ, 0 < c ∧ p = -(c : ℤ) • vl) →
        (∃ m : ℕ, 0 < m ∧ vJ1 = (m : ℤ) • vl) →
        dot nJ vJ1 < 0 → dot nJ p ≠ 0 →
        dot nJ vl = -1 := by
  intro h
  have := h nR vJR vlR pR vJ1R aR a'R SR prim_nR prim_vJR prim_vlR dot_nR_vJR
    latticeConvex_SR aR_mem a'R_mem lex_SR lex'_SR edge_SR edge'_SR
    pR_ne det_pR_vlR hp_neg_R collinear_R sweep_R dot_nR_pR
  rw [dot_nR_vlR] at this
  norm_num at this

/-- 同一居民的 `gcd` 读数：`d = 2`、`e = 2` ⟹ `gcd = 2`。

与集成者 `GcdCollapse.lean` 的 `gcd_one_of_unit` 方向一致（`dot nJ vl = -2 ≠ -1`
⟹ `gcd ≠ 1`），这里是同一事实的算术侧。 -/
theorem gcd_two_R : Int.gcd (dot nR pR) (-dot nR vJ1R) = 2 := by
  norm_num [dot, nR, pR, vJ1R]

/-- ⚠ **`det p vJ1` 在链上恒为 0** —— 已由集成者 `GcdCollapse.lean` 的 `det_p_vJ1_zero`
证出（更一般：`m : ℤ`，不要正性），本文件**不重复**，只记该事实与本居民一致：
`pR` 与 `vJ1R` 都是 `vlR` 的倍数，`det pR vJ1R = 0`。 -/
theorem det_pR_vJ1R : det pR vJ1R = 0 := by norm_num [det, pR, vJ1R]

/-! ## §7 ⭐ 加上 `Primitive vJ1` 之后本反例**不动**

lane-tower-hbase 第 234 轮报了一组「`dot nJ vl = -1` 但合取 1 为假」的见证
（`nJ = (0,1)`、`vl = (0,-1)`、`c = m = 2` ⟹ `p = (0,2)`、`vJ1 = (0,-2)`），并据此把
`dot nJ vl = -1` 列为「太弱，结论变假」。⚠ 那组见证的 `vJ1 = (0,-2)` **不是本原的**
（`m = 2`），所以它成立与否完全取决于链上有没有 `Primitive vJ1`：

* **Lean 字段表里没有这条。** `ChainDataGeomParts` 只有 `vJ_prim` 与 `nJ_prim` 两条本原性字段，
  `vJ1` 是裸数据，唯一约束是 `hsweep`。⟹ 按**现签名**，hbase 那组见证合法。
* **但原文供得出这条。** `TowerHbaseUnitSweep.lean` 的模块注释记 `b3_colle2.txt:351`
  把 `v⃗_ℓ` 定成「平行于 `ℓ` 且模最小的非零向量」⟹ `Primitive vJ1` 是原文自带的。
  ⚠ 该原文读数为 lane-tower-hbase 所报，我未复核。
* ⟹ 一旦有人把 `vJ1_prim` 补成字段，`Primitive vJ1` ＋ 共线 `vJ1 = m • vl` ＋ `Primitive vl`
  就把 `m` 钉成 `1`，hbase 那组见证**当场出局**（它要 `m = 2`）。

⭐ 本居民取 `vJ1R = (1, 0)`，`Primitive vJ1R` 成立且 `m = 1`。⟹ **补不补 `vJ1_prim`
都不影响本文件的结论**。下面这条把 `Primitive vJ1` 直接写进前提，把这点钉在内核里。 -/

/-- ⭐⭐ **加强版**：在 `unit_dot_nJ_vl_not_of_face_binders` 的十六条前提之外
再加 `Primitive vJ1`，`dot nJ vl = -1` **仍不成立**。

⟹ 「补 `vJ1_prim` 字段」这条路**救不了** `|dot nJ vl| = 1`：它能否掉 `m ≥ 2` 的见证，
但本居民 `m = 1`，不在被否掉的那一类里。 -/
theorem unit_dot_nJ_vl_not_of_face_binders_prim :
    ¬ ∀ (nJ vJ vl p vJ1 a a' : ℤ × ℤ) (S : Finset (ℤ × ℤ)),
        Primitive nJ → Primitive vJ → Primitive vl → Primitive vJ1 →
        dot nJ vJ = 0 →
        LatticeConvex S → a ∈ S → a' ∈ S →
        (∀ b ∈ S.erase a,
          dot (-nJ) b < dot (-nJ) a ∨ (dot (-nJ) b = dot (-nJ) a ∧ dot (-vJ) b < dot (-vJ) a)) →
        (∀ b ∈ S.erase a',
          dot (-nJ) b < dot (-nJ) a' ∨ (dot (-nJ) b = dot (-nJ) a' ∧ dot vJ b < dot vJ a')) →
        (∀ b ∈ S.erase a,
          (∃ j : ℕ, 1 ≤ j ∧ j ≤ 1 ∧ b = a + (j : ℤ) • vJ) ∨ 1 ≤ dot nJ (b - a)) →
        (∀ b ∈ S.erase a',
          (∃ j : ℕ, 1 ≤ j ∧ j ≤ 1 ∧ b = a' - (j : ℤ) • vJ) ∨ 1 ≤ dot nJ (b - a')) →
        p ≠ 0 → det p vl = 0 → (∃ c : ℕ, 0 < c ∧ p = -(c : ℤ) • vl) →
        (∃ m : ℕ, 0 < m ∧ vJ1 = (m : ℤ) • vl) →
        dot nJ vJ1 < 0 → dot nJ p ≠ 0 →
        dot nJ vl = -1 := by
  intro h
  have := h nR vJR vlR pR vJ1R aR a'R SR prim_nR prim_vJR prim_vlR prim_vJ1R dot_nR_vJR
    latticeConvex_SR aR_mem a'R_mem lex_SR lex'_SR edge_SR edge'_SR
    pR_ne det_pR_vlR hp_neg_R collinear_R sweep_R dot_nR_pR
  rw [dot_nR_vlR] at this
  norm_num at this

/-- 本居民的 `m` 就是 `1`：`vJ1R = vlR`。⟹ 它落在 hbase 那组见证**之外**的一格：
`m = 1` 而 `|dot nJ vl| = 2`，而非 `m = 2` 而 `|dot nJ vl| = 1`。 -/
theorem vJ1R_eq_vlR : vJ1R = vlR := rfl

/-! ## §8 合取 1 高度部分的**尖锐判据**，以及 `g ≥ 2` 可满足

集成者第 235 轮派工：在共线构型（`vJ1 = m • vl`、`p = -(c:ℤ) • vl`、`0 < c`）下，
把 `EnvRefuteCover.heights_iff_cover` 的覆盖条件写成 `(g, cJ, 基点高度)` 的形状，
并判定两支：(a) `g ≥ 2` 时可满足 ⟹ 合取 1 绕开幺模性；(b) 逼出 `g = 1` ⟹ 必须改签名。

**答案是 (a)。** 关键在模数：`-dot nJ vJ1 = -(m · dot nJ vl)`，所以覆盖条件是

> `A` 的高度集 `dot nJ '' A` 打到模 `m · |dot nJ vl|` 的**每一个**剩余类。

这**不是**关于 `|dot nJ vl|` 的条件，而是关于 `A` 的**高度谱**的条件。两者独立：
`|dot nJ vl| = 1` 只是让模数塌成 `1`、条件平凡真（`heights_of_collinear_unit`，即集成者
第 3 项问的「共线 ＋ 大小 1 ⟹ 覆盖白送？」—— **是，白送，且连共线都不必要，只要模数为 1**）；
而模数 `≥ 2` 时条件依然可以由 `A` 自己满足。

⭐ **机制**：`p` 与 `vJ1` 都是 `vl` 的倍数 ⟹ 两者都把高度平移 `dot nJ vl` 的整数倍 ⟹
**递推方向一个剩余类都换不了**。剩余类只能由 `A` 自身的高度谱提供。而面字段 `edge` 允许
窗口里存在比面高 **恰好 1** 的点（`1 ≤ dot nJ (b - a)` 没有上界），一个这样的点就打破了
任意模数下的剩余壁垒。本文件的 `SR` 正是如此：三点高度 `{0, 1, 0}`，模 `2` 两类全中。

⛔ **射程**：`AR` 是满足字段层性质（`Nonempty` / `rec_p` / `rec_vJ` / 半平面）的**抽象集合**，
**不是** `⋃ i, hatOf A kk vl i`。本节证明的是「合取 1 的高度部分与 `|dot nJ vl| = 1` 无关」，
**不是**「链上合取 1 成立」。要后者还得把 `AR` 换成真正的 `Âinf`。 -/

/-- 模数为 `1` 时覆盖条件平凡成立。⚠ 不需要共线，也不需要 `hsweep`。 -/
theorem cover_of_modulus_one {A : Set (ℤ × ℤ)} {nJ vJ1 : ℤ × ℤ}
    (hne : A.Nonempty) (he : -dot nJ vJ1 = 1) :
    ∀ r : ℤ, ∃ g ∈ A, (-dot nJ vJ1) ∣ (dot nJ g - r) := by
  obtain ⟨g₀, hg₀⟩ := hne
  exact fun r => ⟨g₀, hg₀, by rw [he]; exact one_dvd _⟩

/-- 共线 `m = 1` ＋ `dot nJ vl = -1` ⟹ 模数为 `1`。 -/
theorem modulus_one_of_collinear_unit {nJ vl vJ1 : ℤ × ℤ}
    (hm : vJ1 = (1 : ℤ) • vl) (hs : dot nJ vl = -1) : -dot nJ vJ1 = 1 := by
  rw [hm, dot_zsmul_loc, hs]; ring

/-- ⭐ 集成者第 235 轮第 3 问的答案：**共线 ＋ 大小 1 ⟹ 合取 1 的高度部分白送**。 -/
theorem heights_of_collinear_unit {A : Set (ℤ × ℤ)} {nJ vl vJ1 : ℤ × ℤ} {cJ : ℤ}
    (hne : A.Nonempty) (hhp : ∀ g ∈ A, cJ ≤ dot nJ g) (hsweep : dot nJ vJ1 < 0)
    (hm : vJ1 = (1 : ℤ) • vl) (hs : dot nJ vl = -1) :
    ∀ ε : ℕ, ∃ z ∈ reachSet A vJ1, dot nJ z = cJ - (ε : ℤ) - 1 :=
  (heights_iff_cover hsweep hhp).mpr
    (cover_of_modulus_one hne (modulus_one_of_collinear_unit hm hs))

/-- ⭐⭐ **尖锐判据，模数显式写成 `m · dot nJ vl`。**

这是 `heights_iff_cover` 在共线构型上的重述：合取 1 的高度部分 ⟺ `A` 的高度集打到
模 `m · dot nJ vl` 的每个剩余类。⟹ 欠项从「`|dot nJ vl| = 1`」变成「`A` 的高度谱满剩余类」。 -/
theorem heights_iff_cover_collinear {A : Set (ℤ × ℤ)} {nJ vl vJ1 : ℤ × ℤ} {cJ m : ℤ}
    (hm : vJ1 = m • vl) (hsweep : dot nJ vJ1 < 0) (hhp : ∀ g ∈ A, cJ ≤ dot nJ g) :
    (∀ ε : ℕ, ∃ z ∈ reachSet A vJ1, dot nJ z = cJ - (ε : ℤ) - 1) ↔
      (∀ r : ℤ, ∃ g ∈ A, (-(m * dot nJ vl)) ∣ (dot nJ g - r)) := by
  have he : -(m * dot nJ vl) = -dot nJ vJ1 := by rw [hm, dot_zsmul_loc]
  rw [he]
  exact heights_iff_cover hsweep hhp

/-! ### §8.1 `g = 2` 的见证：与 §1 同一组向量，只补一个 `A` -/

/-- 半平面居民。⚠ 抽象集合，不是 `⋃ hatOf`。 -/
def AR : Set (ℤ × ℤ) := {z : ℤ × ℤ | 0 ≤ dot nR z}

theorem mem_AR {z : ℤ × ℤ} : z ∈ AR ↔ 0 ≤ dot nR z := Iff.rfl

theorem AR_nonempty : AR.Nonempty :=
  ⟨(0, 0), by rw [mem_AR]; norm_num [dot, nR]⟩

/-- `hhp`，取 `cJ = 0`。 -/
theorem AR_hhp : ∀ g ∈ AR, (0 : ℤ) ≤ dot nR g := fun _ hg => hg

/-- `rec_p`：`p` 把高度抬高 `2`。 -/
theorem AR_rec_p : ∀ g ∈ AR, g + pR ∈ AR := by
  intro g hg
  rw [mem_AR] at hg ⊢
  rw [dot_add_loc]
  have : dot nR pR = 2 := by norm_num [dot, nR, pR]
  omega

/-- `rec_vJ`：`vJ` 保高度（`dot nJ vJ = 0`）。 -/
theorem AR_rec_vJ : ∀ g ∈ AR, g + vJR ∈ AR := by
  intro g hg
  rw [mem_AR] at hg ⊢
  rw [dot_add_loc, dot_nR_vJR]
  omega

/-- 窗口整个落在 `AR` 里 —— 剩余类正是它供的。 -/
theorem SR_sub_AR : ∀ z ∈ SR, z ∈ AR := by
  intro z hz
  rw [mem_SR] at hz
  rcases hz with rfl | rfl | rfl <;> · rw [mem_AR]; norm_num [dot, nR]

/-- ⭐ **模数 `2` 下覆盖条件成立**：高度 `(0, n)` 取遍一切 `n ≥ 0`，两个剩余类全中。 -/
theorem AR_cover : ∀ r : ℤ, ∃ g ∈ AR, (-dot nR vJ1R) ∣ (dot nR g - r) := by
  intro r
  have he : -dot nR vJ1R = 2 := by norm_num [dot, nR, vJ1R]
  refine ⟨(0, r + 2 * |r|), ?_, ?_⟩
  · rw [mem_AR]
    simp only [dot, nR]
    rcases abs_cases r with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1] <;> omega
  · refine ⟨|r|, ?_⟩
    rw [he]
    simp only [dot, nR]
    ring

/-- ⭐ 合取 1 的高度部分在 `AR` 上成立，模数是 **2**。 -/
theorem AR_heights : ∀ ε : ℕ, ∃ z ∈ reachSet AR vJ1R, dot nR z = 0 - (ε : ℤ) - 1 :=
  (heights_iff_cover sweep_R AR_hhp).mpr AR_cover

/-- ⭐⭐⭐ **本轮结论：合取 1 的高度部分不需要 `|dot nJ vl| = 1`。**

一组**共线**（`det p vl = 0`、`det p vJ1 = 0`，即集成者指出 `Aup`/`Aeven` 所缺的那条）
且 `Primitive vJ1` 的数据，`|dot nJ vl| = 2`、`gcd(d, e) = 2`，而高度部分**成立**。

⟹ 判定为集成者两支中的 **(a)**：出路绕开幺模性，`|dot nJ vl| = 1` 对合取 1 的高度部分
**不是必要条件**。⛔ 射程见 §8 抬头：`A` 是抽象集合，不是 `Âinf`。 -/
theorem conj1_heights_without_unit_magnitude :
    ∃ (A : Set (ℤ × ℤ)) (nJ vJ vl p vJ1 : ℤ × ℤ) (cJ : ℤ) (c m : ℕ),
      Primitive nJ ∧ Primitive vJ ∧ Primitive vl ∧ Primitive vJ1 ∧
      dot nJ vJ = 0 ∧
      0 < c ∧ p = -(c : ℤ) • vl ∧ 0 < m ∧ vJ1 = (m : ℤ) • vl ∧
      det p vl = 0 ∧ det p vJ1 = 0 ∧
      dot nJ vJ1 < 0 ∧ dot nJ p ≠ 0 ∧
      A.Nonempty ∧ (∀ g ∈ A, g + p ∈ A) ∧ (∀ g ∈ A, g + vJ ∈ A) ∧
      (∀ g ∈ A, cJ ≤ dot nJ g) ∧
      dot nJ vl = -2 ∧ Int.gcd (dot nJ p) (-dot nJ vJ1) = 2 ∧
      (∀ ε : ℕ, ∃ z ∈ reachSet A vJ1, dot nJ z = cJ - (ε : ℤ) - 1) :=
  ⟨AR, nR, vJR, vlR, pR, vJ1R, 0, 1, 1,
    prim_nR, prim_vJR, prim_vlR, prim_vJ1R, dot_nR_vJR,
    one_pos, by norm_num [pR, vlR, Prod.ext_iff], one_pos,
    by norm_num [vJ1R, vlR, Prod.ext_iff],
    det_pR_vlR, det_pR_vJ1R, sweep_R, dot_nR_pR,
    AR_nonempty, AR_rec_p, AR_rec_vJ, AR_hhp,
    dot_nR_vlR, gcd_two_R, AR_heights⟩

/-! ## §9 覆盖条件搬到**真** `⋃ i, hatOf A kk vl i` 上：归约到带 `B i`

集成者第 236 轮派工 (ii)：上一轮 §8 用的是抽象 `AR`，这一节按要求在真对象上说话。

⭐ **两次平移都是「模 `e` 中性」的**，这是本节全部内容：

* `Colle35.hatOf A kk vl i = {z | z + (kk i : ℤ) • vl ∈ A i}` —— 平移量 `(kk i) • vl`，
  高度变化 `(kk i) · dot nJ vl`；
* `Colle35.halfStrip (B i) vl = {z | ∃ b ∈ B i, ∃ t : ℕ, z = b + (t : ℤ) • vl}` —— 平移量
  `t • vl`，高度变化 `t · dot nJ vl`；而 `A i ⊆ halfStrip (B i) vl`
  （`Colle35.subStrip_of_max` / `Colle35.canonA_subset_halfStrip`）。

两者都是 `dot nJ vl` 的整数倍。只要 **`e ∣ dot nJ vl`**，它们就一个剩余类都换不了 ⟹

> 合取 1 的高度部分（经 `heights_iff_cover`）⟹ **`⋃ i, B i` 的高度集打满模 `e` 的剩余类**。

⟹ 这是一条**必要**条件，签名里**没有 `p`、没有 `vJ1` 的幅值、没有递推**（`vJ1` 只作为
模数出现，且被 `modulus_dvd_dot_vl` 消成 `dot nJ vl`），只吃 `A i ⊆ halfStrip (B i) vl`。

⚠ **`e ∣ dot nJ vl` 在链上如何兑现**：`e = -dot nJ vJ1 = -(m · dot nJ vl)`，`e ∣ dot nJ vl`
当且仅当 `m` 是单位。而 `Primitive vJ1`（原文 `:351`）＋ `Primitive vl` ＋ 共线把 `m` 钉成 `1`
（集成者 `GcdCollapse.vJ1_eq_vl_of_prim`）⟹ 前提在链上成立，`modulus_dvd_dot_vl` 就是这一步。
⛔ 所以本节**依赖** `vJ1_prim` 被补成字段；在补之前它是条件结论。

**反向（充分性）差一条，已命名**：`BaseSurvives` —— 「`B i` 的每个基点，其剩余类在 `A i` 里
还有代表」。`A i` 是 `canonA` 被图案吻合 `η (w + u i) = xper w` 切过的极大包络，切掉的点
恰好可能是需要的那些，所以这一条**不能**从 `B i` 的覆盖推出。有了它，必要条件升级成充要
（`cover_hatOf_of_base_cover`）。⟹ 这就是「抽象版 ⟹ 真 `hatOf` 版」缺的那一条，
按派工要求点名：它是 `canonA` / `ChainCanon` 那一格的持有者该供的，不在我的 lane 里。 -/

theorem dot_sub_loc (n a b : ℤ × ℤ) : dot n (a - b) = dot n a - dot n b := by
  simp only [dot, Prod.fst_sub, Prod.snd_sub]; ring

/-- 链上 `m = 1`（`Primitive vJ1` 之下）时模数整除 `dot nJ vl`，即 §9 的前提。 -/
theorem modulus_dvd_dot_vl {nJ vl vJ1 : ℤ × ℤ} (hm : vJ1 = (1 : ℤ) • vl) :
    (-dot nJ vJ1) ∣ dot nJ vl := by
  rw [hm, dot_zsmul_loc, one_mul]
  exact ⟨-1, by ring⟩

/-- ⭐ `hatOf` 的平移是模 `e` 中性的：覆盖条件在 `⋃ hatOf` 与 `⋃ A i` 上**等价**。 -/
theorem cover_hatOf_iff_cover_A {A : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ} {nJ vl : ℤ × ℤ} {e : ℤ}
    (hdvd : e ∣ dot nJ vl) :
    (∀ r : ℤ, ∃ z ∈ ⋃ i, Nivat.Colle35.hatOf A kk vl i, e ∣ (dot nJ z - r)) ↔
      (∀ r : ℤ, ∃ w ∈ ⋃ i, A i, e ∣ (dot nJ w - r)) := by
  constructor
  · intro h r
    obtain ⟨z, hz, hd⟩ := h r
    obtain ⟨i, hzi⟩ := Set.mem_iUnion.mp hz
    have hzi' : z + (kk i : ℤ) • vl ∈ A i := hzi
    refine ⟨z + (kk i : ℤ) • vl, Set.mem_iUnion.mpr ⟨i, hzi'⟩, ?_⟩
    have he : dot nJ (z + (kk i : ℤ) • vl) - r = (dot nJ z - r) + (kk i : ℤ) * dot nJ vl := by
      rw [dot_add_loc, dot_zsmul_loc]; ring
    rw [he]
    exact dvd_add hd (hdvd.mul_left _)
  · intro h r
    obtain ⟨w, hw, hd⟩ := h r
    obtain ⟨i, hwi⟩ := Set.mem_iUnion.mp hw
    refine ⟨w - (kk i : ℤ) • vl, Set.mem_iUnion.mpr ⟨i, ?_⟩, ?_⟩
    · show w - (kk i : ℤ) • vl + (kk i : ℤ) • vl ∈ A i
      simpa using hwi
    · have he : dot nJ (w - (kk i : ℤ) • vl) - r
          = (dot nJ w - r) - (kk i : ℤ) * dot nJ vl := by
        rw [dot_sub_loc, dot_zsmul_loc]; ring
      rw [he]
      exact dvd_sub hd (hdvd.mul_left _)

/-- ⭐ `halfStrip` 的平移同样中性：`⋃ A i` 覆盖 ⟹ `⋃ B i` 覆盖。 -/
theorem cover_base_of_cover_A {A B : ℕ → Set (ℤ × ℤ)} {nJ vl : ℤ × ℤ} {e : ℤ}
    (hdvd : e ∣ dot nJ vl)
    (hsub : ∀ i, ∀ z ∈ A i, ∃ b ∈ B i, ∃ t : ℕ, z = b + (t : ℤ) • vl)
    (hcov : ∀ r : ℤ, ∃ w ∈ ⋃ i, A i, e ∣ (dot nJ w - r)) :
    ∀ r : ℤ, ∃ b ∈ ⋃ i, B i, e ∣ (dot nJ b - r) := by
  intro r
  obtain ⟨w, hw, hd⟩ := hcov r
  obtain ⟨i, hwi⟩ := Set.mem_iUnion.mp hw
  obtain ⟨b, hb, t, rfl⟩ := hsub i w hwi
  refine ⟨b, Set.mem_iUnion.mpr ⟨i, hb⟩, ?_⟩
  have he : dot nJ b - r
      = (dot nJ (b + (t : ℤ) • vl) - r) - (t : ℤ) * dot nJ vl := by
    rw [dot_add_loc, dot_zsmul_loc]; ring
  rw [he]
  exact dvd_sub hd (hdvd.mul_left _)

/-- ⭐⭐ **必要条件，真 `hatOf` 上**：合取 1 的覆盖条件 ⟹ 带 `⋃ i, B i` 打满模 `e`。 -/
theorem cover_base_of_cover_hatOf {A B : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ} {nJ vl : ℤ × ℤ} {e : ℤ}
    (hdvd : e ∣ dot nJ vl)
    (hsub : ∀ i, ∀ z ∈ A i, ∃ b ∈ B i, ∃ t : ℕ, z = b + (t : ℤ) • vl)
    (hcov : ∀ r : ℤ, ∃ z ∈ ⋃ i, Nivat.Colle35.hatOf A kk vl i, e ∣ (dot nJ z - r)) :
    ∀ r : ℤ, ∃ b ∈ ⋃ i, B i, e ∣ (dot nJ b - r) :=
  cover_base_of_cover_A hdvd hsub ((cover_hatOf_iff_cover_A hdvd).mp hcov)

/-- ⭐⭐⭐ **可用的判伪器**：带漏掉一个剩余类 ⟹ 合取 1 的高度部分在**真** `⋃ hatOf` 上为假。

⟹ 集成者第 236 轮出口 (iii) 的「不满」那一支：要否掉合取 1，只需在某个 `r₀` 上
证明所有 `B i` 的高度都不落在 `r₀` 的剩余类里。签名不含 `p`、不含递推。 -/
theorem not_heights_of_base_misses {A B : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ}
    {nJ vl vJ1 : ℤ × ℤ} {cJ r₀ : ℤ}
    (hm : vJ1 = (1 : ℤ) • vl)
    (hsweep : dot nJ vJ1 < 0)
    (hhp : ∀ g ∈ ⋃ i, Nivat.Colle35.hatOf A kk vl i, cJ ≤ dot nJ g)
    (hsub : ∀ i, ∀ z ∈ A i, ∃ b ∈ B i, ∃ t : ℕ, z = b + (t : ℤ) • vl)
    (hmiss : ∀ b ∈ ⋃ i, B i, ¬ ((-dot nJ vJ1) ∣ (dot nJ b - r₀))) :
    ¬ (∀ ε : ℕ, ∃ z ∈ reachSet (⋃ i, Nivat.Colle35.hatOf A kk vl i) vJ1,
        dot nJ z = cJ - (ε : ℤ) - 1) := by
  intro h
  obtain ⟨b, hb, hd⟩ :=
    cover_base_of_cover_hatOf (modulus_dvd_dot_vl hm) hsub
      ((heights_iff_cover hsweep hhp).mp h) r₀
  exact hmiss b hb hd

/-- **充分性差的那一条，命名版**：`B i` 的每个基点，其剩余类在 `A i` 里还有代表。

⛔ 不能从 `B i` 的覆盖推出：`A i` 是 `Colle35.canonA` 被图案吻合条件
`η (w + u i) = xper w` 切过的极大包络，切掉的点恰好可能是需要的那些。 -/
def BaseSurvives (A B : ℕ → Set (ℤ × ℤ)) (nJ : ℤ × ℤ) (e : ℤ) : Prop :=
  ∀ i, ∀ b ∈ B i, ∃ z ∈ A i, e ∣ (dot nJ z - dot nJ b)

/-- ⭐ 有了 `BaseSurvives`，必要条件升级成**充分**条件 ⟹ 合起来是充要。 -/
theorem cover_hatOf_of_base_cover {A B : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ} {nJ vl : ℤ × ℤ} {e : ℤ}
    (hdvd : e ∣ dot nJ vl)
    (hsurv : BaseSurvives A B nJ e)
    (hcovB : ∀ r : ℤ, ∃ b ∈ ⋃ i, B i, e ∣ (dot nJ b - r)) :
    ∀ r : ℤ, ∃ z ∈ ⋃ i, Nivat.Colle35.hatOf A kk vl i, e ∣ (dot nJ z - r) := by
  refine (cover_hatOf_iff_cover_A hdvd).mpr ?_
  intro r
  obtain ⟨b, hb, hd⟩ := hcovB r
  obtain ⟨i, hbi⟩ := Set.mem_iUnion.mp hb
  obtain ⟨z, hz, hdz⟩ := hsurv i b hbi
  refine ⟨z, Set.mem_iUnion.mpr ⟨i, hz⟩, ?_⟩
  have he : dot nJ z - r = (dot nJ z - dot nJ b) + (dot nJ b - r) := by ring
  rw [he]
  exact dvd_add hdz hd

/-! ## §10 ⚠ §9 的射程订正：共线不是链上定理，而 §9 并不需要它

**订正的是本文件 §9 的射程说明，不是 §9 的任何证明。** 上一轮我把 §9 的条件性只记成
「等 `vJ1_prim` 补成字段」，漏了更靠前的一条：`vJ1 = m • vl` 本身在链上**不是**已证事实。

* `GcdCollapse.det_p_vJ1_zero` 的方向是「`hp` ＋ `hm` ⟹ `det p vJ1 = 0`」，
  即**共线 ⟹ 行列式为零**，不能反过来当共线的产者；
* `FillCoverWitness.lean` 的模块 Scope 段把 `det vl vJ1 = 0` 明写成
  「the `J = ι + 1` configuration」，`LeafAShellLsideFork.lean` 的模块说明记同一条
  （这两处是本 lane 自己打开文件核到的，不是转述）；
* lane-tower-hbase 的 `TowerHbaseRecP.collinear_iff_window_bot` 在**环序模型**里把它做成等价形。
  ⚠ 那条说的是 `dir (C.nu ·)` 两个法向之间的共线，要搬到链上的 `vl` / `vJ1` 还缺一条词典，
  本 lane 未核该词典；上面两处文件内的 Scope 记载与之独立。

⟹ §9 里唯一吃共线的只有 `not_heights_of_base_misses` 的 `hm`：两条平移引理
（`cover_hatOf_iff_cover_A` / `cover_base_of_cover_A`）与充分方向
（`cover_hatOf_of_base_cover`）从一开始就只吃 `hdvd : e ∣ dot nJ vl`。本节把那条 `hm`
换成 `hdvd`，判伪器随即脱离「窗口底端一格」。

⚠ 代价写清楚：`hdvd` 变成**待供的侧条件**。用这个判伪器的人要在自己那一格上供
`(-dot nJ vJ1) ∣ dot nJ vl`；共线 ＋ `m = 1` 只是它的一个充分条件（`modulus_dvd_dot_vl`），
而 `dvd_of_dot_vl_eq_mul` 给出它的纯高度形——产者只需说明「sweep 步长的高度整除
strip 步长的高度」，一个字都不必碰向量的平行性。 -/

/-- 侧条件的**纯高度**形：`dot nJ vl` 是 `dot nJ vJ1` 的整数倍即可，不要求 `vl ∥ vJ1`。 -/
theorem dvd_of_dot_vl_eq_mul {nJ vl vJ1 : ℤ × ℤ} {k : ℤ}
    (h : dot nJ vl = k * dot nJ vJ1) : (-dot nJ vJ1) ∣ dot nJ vl :=
  ⟨-k, by rw [h]; ring⟩

/-- ⭐⭐ **判伪器的无共线版**：只要模 `e := -dot nJ vJ1` 整除 `dot nJ vl`，带漏掉一个
剩余类就足以让合取 1 的高度部分在**真** `⋃ hatOf` 上为假。

`not_heights_of_base_misses` 是本条在 `hdvd := modulus_dvd_dot_vl hm` 处的特例；
⟹ 那一条的射程（`J = ι + 1` 构型）是它自己 `hm` 带来的，不是判伪机制带来的。 -/
theorem not_heights_of_base_misses_dvd {A B : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ}
    {nJ vl vJ1 : ℤ × ℤ} {cJ r₀ : ℤ}
    (hdvd : (-dot nJ vJ1) ∣ dot nJ vl)
    (hsweep : dot nJ vJ1 < 0)
    (hhp : ∀ g ∈ ⋃ i, Nivat.Colle35.hatOf A kk vl i, cJ ≤ dot nJ g)
    (hsub : ∀ i, ∀ z ∈ A i, ∃ b ∈ B i, ∃ t : ℕ, z = b + (t : ℤ) • vl)
    (hmiss : ∀ b ∈ ⋃ i, B i, ¬ ((-dot nJ vJ1) ∣ (dot nJ b - r₀))) :
    ¬ (∀ ε : ℕ, ∃ z ∈ reachSet (⋃ i, Nivat.Colle35.hatOf A kk vl i) vJ1,
        dot nJ z = cJ - (ε : ℤ) - 1) := by
  intro h
  obtain ⟨b, hb, hd⟩ :=
    cover_base_of_cover_hatOf hdvd hsub ((heights_iff_cover hsweep hhp).mp h) r₀
  exact hmiss b hb hd

/-! ## §11 侧条件 `hdvd` 的**充要**形，以及它在链上由谁供

§10 把判伪器的前提收到 `hdvd : (-dot nJ vJ1) ∣ dot nJ vl` 一条。本节把这条前提自身钉死：
在共线形 `vJ1 = m • vl` 之下、`dot nJ vl ≠ 0` 一侧，

> `hdvd` ⟺ `IsUnit m`

⟹ `modulus_dvd_dot_vl`（§9，走 `m = 1`）是本条的一个特例，且 `m = -1` 同样够用。

### 链上谁供（三条**全部**以 binder 形式出现，本节不 import 任何一方）

* `IsUnit m` ← `Primitive vJ1`，产者 `GcdCollapse.isUnit_m_of_prim`（已在主仓）。
* `Primitive vJ1` ← **边数据**：`nprevJ ∈ E R` ＋ `vJ1 = ±dir nprevJ`，而
  `LatticeEdges.IsEdge` 的定义里本来就带本原性。产者按 lane-tower-hbase 2026-09-25 报的
  `TowerHbaseRecP.prim_vJ1_of_edge_ccw` / `prim_vJ1_of_edge_cw`。
  ⟹ 这一条**不经过** `b3_colle2.txt`：不是「原文供得出但没补成字段」，是主仓自己的
  边数据供得出但没取出来。
* 共线形本身 ← `dot nprevJ vl = 0`（「上一条边的法向垂直于 `vl`」＝窗口底端 `J = ι+1`），
  按他报的 `TowerHbaseRecP.collinear_vJ1_vl_iff_perp_ccw` 是等价形。

⚠ §55：上面三条里后两条是 **lane 报，本 lane 未复跑**。本节两条定理一条都不 import 它们，
所有依赖都留在 binder 里，所以即使那两条日后改名或收窄，本节的内核对象不受影响。

⚠ 射程：本节只说 `hdvd` 这一条侧条件。判伪器要真咬人还欠 `⋃ i, B i` 漏掉某个剩余类
（`not_heights_of_base_misses_dvd` 的 `hmiss`），那一条不在本 lane 手里（见 §9）。 -/

/-- `m` 是单位 ⟹ 侧条件成立。⚠ `m = -1` 与 `m = 1` 同样够用，不需要挑符号。 -/
theorem dvd_of_collinear_isUnit {nJ vl vJ1 : ℤ × ℤ} {m : ℤ}
    (hm : vJ1 = m • vl) (hu : IsUnit m) : (-dot nJ vJ1) ∣ dot nJ vl := by
  have hv : dot nJ vJ1 = m * dot nJ vl := by rw [hm, dot_zsmul_loc]
  have hmm : m * m = 1 := by rcases Int.isUnit_iff.mp hu with h | h <;> rw [h] <;> ring
  refine ⟨-m, ?_⟩
  rw [hv]
  linear_combination (-(dot nJ vl)) * hmm

/-- 反向：侧条件 ＋ `dot nJ vl ≠ 0` ⟹ `m` 是单位。⟹ 共线之下 `hdvd` 一点都不比
`Primitive vJ1` 弱，`m ≥ 2` 的共线构型上它必假。 -/
theorem isUnit_of_collinear_dvd {nJ vl vJ1 : ℤ × ℤ} {m : ℤ}
    (hm : vJ1 = m • vl) (hs : dot nJ vl ≠ 0)
    (hdvd : (-dot nJ vJ1) ∣ dot nJ vl) : IsUnit m := by
  have hv : dot nJ vJ1 = m * dot nJ vl := by rw [hm, dot_zsmul_loc]
  obtain ⟨k, hk⟩ := hdvd
  rw [hv] at hk
  refine isUnit_of_dvd_one ⟨-k, ?_⟩
  have hz : dot nJ vl * (m * (-k) - 1) = 0 := by linear_combination -hk
  rcases mul_eq_zero.mp hz with h | h
  · exact absurd h hs
  · linear_combination -h

/-- ⭐ 充要形。⟹ §10 的判伪器在共线构型上恰好覆盖 `m = ±1`，一格不多一格不少。 -/
theorem dvd_iff_isUnit_of_collinear {nJ vl vJ1 : ℤ × ℤ} {m : ℤ}
    (hm : vJ1 = m • vl) (hs : dot nJ vl ≠ 0) :
    (-dot nJ vJ1) ∣ dot nJ vl ↔ IsUnit m :=
  ⟨isUnit_of_collinear_dvd hm hs, dvd_of_collinear_isUnit hm⟩

/-! ## §12 §10 判伪器的**可满足性见证**（lane-leafa-gen 2026-09-25 的限定，接受并兑现）

lane-leafa-gen 订正了我给他的「binder 对表」判据，订正是对的，而且**咬到我自己**：

> 守卫写进 binder，只有在「被否」或「被构造」的位置才算内核查过；在「被**假设**」的位置
> Lean 一个字都不查 —— 前提束若不可满足，定理照样编译、照样空真。

`not_heights_of_base_misses_dvd`（§10）正是「被假设」那一类：`hdvd` / `hsweep` / `hhp` /
`hsub` / `hmiss` 五条全是假设。⟹ 它非空真需要另配见证，本节就是那条见证。

居民：`nS = (0,1)`、`vl = vJ1 = vS = (1,-2)`、`kk ≡ 0`、`A i = B i = {(0,0)}`、`cJ = 0`、
`r₀ = 1`。`e = -dot nS vS = 2`，而基点高度 `dot nS (0,0) = 0` 落在偶剩余类里 ⟹ `hmiss` 兑现。

⚠ 这个居民同时是**链上合理**的，不是随手凑的空壳：`Primitive vS`（`prim_vS`），
`vJ1 = vl` 即 `m = 1`，于是 §11 的 `IsUnit m` 也真 —— `hdvd` 走的是那条供给路线，
不是靠取一个退化的 `vl`。

⛔ 射程：本节只证「§10 那条判伪器的前提束可满足」。它**不**说链上的 `⋃ i, B i` 长这样；
真 `B` 是 `DecompDataZ` 造的，本 lane 没读过它的构造。 -/

/-- 见证用的常值族：`A i = B i = {(0,0)}`。 -/
def ASing : ℕ → Set (ℤ × ℤ) := fun _ => {(0, 0)}

/-- 见证用的零平移。 -/
def kkS : ℕ → ℕ := fun _ => 0

def nS : ℤ × ℤ := (0, 1)

/-- `vl` 与 `vJ1` 取同一个本原向量 ⟹ `m = 1`，§11 的 `IsUnit m` 成立。 -/
def vS : ℤ × ℤ := (1, -2)

theorem prim_vS : Primitive vS := by
  refine ⟨1, 0, ?_⟩
  norm_num [vS]

theorem mem_hatOf_ASing {i : ℕ} {z : ℤ × ℤ} :
    z ∈ Nivat.Colle35.hatOf ASing kkS vS i ↔ z = (0, 0) := by
  simp [Nivat.Colle35.hatOf, ASing, kkS]

theorem iUnion_hatOf_ASing :
    (⋃ i, Nivat.Colle35.hatOf ASing kkS vS i) = {((0, 0) : ℤ × ℤ)} := by
  ext z
  simp [mem_hatOf_ASing]

theorem hhp_ASing : ∀ g ∈ ⋃ i, Nivat.Colle35.hatOf ASing kkS vS i, (0 : ℤ) ≤ dot nS g := by
  intro g hg
  rw [iUnion_hatOf_ASing] at hg
  rw [show g = ((0, 0) : ℤ × ℤ) from hg]
  norm_num [dot, nS]

theorem hsub_ASing :
    ∀ i, ∀ z ∈ ASing i, ∃ b ∈ ASing i, ∃ t : ℕ, z = b + (t : ℤ) • vS :=
  fun _ z hz => ⟨z, hz, 0, by simp⟩

theorem hmiss_ASing :
    ∀ b ∈ ⋃ i, ASing i, ¬ ((-dot nS vS) ∣ (dot nS b - 1)) := by
  intro b hb
  obtain ⟨i, hbi⟩ := Set.mem_iUnion.mp hb
  rw [show b = ((0, 0) : ℤ × ℤ) from hbi]
  rintro ⟨k, hk⟩
  simp only [dot, nS, vS] at hk
  omega

/-- ⭐⭐ **§10 的判伪器在这个居民上真的咬下去了**：前提束五条全兑现，结论非平凡地为真。

⟹ `not_heights_of_base_misses_dvd` 不是空真的。⚠ 这条**不是**说链上合取 1 为假 ——
链上的 `B` 由 `DecompDataZ` 造，本节的 `ASing` 只兑现「前提束可满足」。 -/
theorem not_heights_ASing :
    ¬ (∀ ε : ℕ, ∃ z ∈ reachSet (⋃ i, Nivat.Colle35.hatOf ASing kkS vS i) vS,
        dot nS z = 0 - (ε : ℤ) - 1) :=
  not_heights_of_base_misses_dvd (B := ASing) (r₀ := 1)
    ⟨-1, by norm_num [dot, nS, vS]⟩ (by norm_num [dot, nS, vS])
    hhp_ASing hsub_ASing hmiss_ASing

/-! ## §13 「新侧条件严格弱于共线」的**非退化**见证

lane-tower-hbase 2026-09-25 的 `TowerHbaseRecP` §10 把 gcd/覆盖那一组也脱掉了共线，
并给了一条分离见证（他报：`nJ = (0,1)`、`vl = (1,-1)`、`vJ1 = (1,1)`，整除成立而
`det vl vJ1 = 2 ≠ 0`）。⚠ §55：他那条我未复跑，但那组数值我自己算了两处：

* `dot (0,1) (1,1) = 1 > 0` ⟹ **`hsweep` 在那组上为假**；
* `e = -dot nJ vJ1 = -1` ⟹ 模数退化，此时覆盖条件由 `cover_of_modulus_one` 平凡为真。

⟹ 若他那条声明里没带 `hsweep`，它作为陈述没问题，但分离是在**链上符号 binder 之外、
且模数退化**的地方展示的 —— 这种分离买不到东西：`|e| = 1` 处整个剩余类机器是空转的。

本节补一条**非退化**的：`nJ = (0,1)`、`vl = (1,-4)`、`vJ1 = (1,-2)`。
两条都本原、两个 sweep 符号都负（`dot nJ vl = -4`、`dot nJ vJ1 = -2`）、`e = 2 ≥ 2`、
`e ∣ dot nJ vl`，而 `det vl vJ1 = 2 ≠ 0` ⟹ 根本不存在 `m` 使 `vJ1 = m • vl`。

⟹ 这才说明 §10/§11 的 `hdvd` 真的买到了东西：在剩余类机器**非空转**的区域里，
它严格弱于共线。 -/

/-- ⭐ 非退化分离：全部符号 binder ＋ 两条本原 ＋ 模数 `≥ 2` 之下，
`hdvd` 成立而共线为假。 -/
theorem hdvd_strictly_weaker_nondegenerate :
    ∃ nJ vl vJ1 : ℤ × ℤ,
      Primitive vl ∧ Primitive vJ1 ∧
      dot nJ vl < 0 ∧ dot nJ vJ1 < 0 ∧
      2 ≤ -dot nJ vJ1 ∧
      (-dot nJ vJ1) ∣ dot nJ vl ∧
      det vl vJ1 ≠ 0 ∧
      ¬ (∃ m : ℤ, vJ1 = m • vl) := by
  refine ⟨(0, 1), (1, -4), (1, -2), ⟨1, 0, by norm_num⟩, ⟨1, 0, by norm_num⟩,
    by norm_num [dot], by norm_num [dot], by norm_num [dot], ⟨-2, by norm_num [dot]⟩,
    by norm_num [det], ?_⟩
  rintro ⟨m, hm⟩
  rw [Prod.ext_iff] at hm
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, mul_one] at hm
  omega

/-! ## §14 `Primitive vJ1` 之下两条侧条件合流（lane-tower-hbase 2026-09-25 §1 的回应）

lane-tower-hbase 不采纳「把他 §10 的侧条件换成 `IsUnit m`」，理由是两条侧条件管的不是
同一个整除式：我的 `dvd_iff_isUnit_of_collinear`（§11）管 `e ∣ dot nJ **vl**`，他 §10 用的是
`e ∣ dot nJ **p**`；他报共线之下后者 `⟺ m ∣ (c : ℤ)`，而 `IsUnit m ⟹ m ∣ c` 恒真、反之不然。

**他这条区分我收：两条确实不是同一个整除式，我原来的建议在那一点上是错的。**

但他给的分离见证 `height_dvd_does_not_give_isUnit_m`（他报：`nJ = (0,1)`、`vl = (0,-1)`、
`m = 2`、`c = 4`）落在**他自己上一轮刚宣布链上有产者**的那条守卫之外。⚠ §55：他那条声明
我未复跑，只自己算了那组数值——`vJ1 = 2 • (0,-1) = (0,-2)`，而 `IsCoprime (0 : ℤ) (-2)` 为假
⟹ **`Primitive vJ1` 在他的分离点上不成立**（`not_prim_hbase_sep_vJ1`）。

而他 2026-09-25 §2 自己报的是：`Primitive vJ1` 由主仓**边数据**（`IsEdge` 定义里自带本原性）
供出，`prim_vJ1_of_edge_ccw` / `prim_vJ1_of_edge_cw` 已落地、不经过原文。

⟹ §113 两向打印，对称地照抄他 §2 对我 `m = -1` 的判词：

* `m ∣ c` 比 `IsUnit m` **多出来**的那些格子，全部落在 `¬ Primitive vJ1` 上
  （`side_condition_free_of_prim_vJ1`：共线 ＋ `Primitive vJ1` ⟹ `IsUnit m` ⟹ `∀ c, m ∣ c`）；
* 所以他 §10 的侧条件在**链上是恒真的**，不是一条要去兑现的前提
  （`dvd_dot_p_of_prim_vJ1` 直接把 `e ∣ dot nJ p` 证出来，不带 `m ∣ c` 假设）；
* 反过来 `IsUnit m` 比 `m ∣ c` 多要求的那一格（`m ≥ 2` 的共线构型），在 `Primitive vJ1`
  之下同样不可达。

⟹ 结论不是「谁比谁强」，而是**在 `Primitive vJ1` 之下两条合流**：他 §10 不必改，我 §11 也不
退让；两边各自的「严格更强／更弱」都只活在链上取不到的区域。他 §2 对我 `m = -1` 的判词与
本节对他 `m = 2` 的判词是同一条判据的两次应用。

⚠ 本节不 import `TowerHbaseRecP`：`Primitive vJ1` 留在 binder 里（他 §3 承诺那三个名字不再改名，
但按 §110.2 去重与接线是集成者的事，不是我在这里 import 的理由）。

⚠ 未主张：本节不说链上的 `m` 等于几，也不说共线本身在链上成不成立 —— 共线裁决的产者
两边都没有（§10 已记）。本节只说：**若**共线，**则** `Primitive vJ1` 让两条侧条件同时为真。 -/

/-- 共线 ＋ `Primitive vJ1` ⟹ `IsUnit m`。
⚠ 只用 `Primitive` 的定义（`IsCoprime vJ1.1 vJ1.2`），不 import `GcdCollapse.isUnit_m_of_prim`。 -/
theorem isUnit_m_of_prim_vJ1 {vl vJ1 : ℤ × ℤ} {m : ℤ}
    (hm : vJ1 = m • vl) (hprim : Primitive vJ1) : IsUnit m := by
  obtain ⟨a, b, hab⟩ := hprim
  subst hm
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at hab
  exact isUnit_of_dvd_one ⟨a * vl.1 + b * vl.2, by linear_combination -hab⟩

/-- ⭐ lane-tower-hbase §10 的侧条件 `e ∣ dot nJ p` 在 `Primitive vJ1` 之下**恒真**，
不需要 `m ∣ c` 当假设。 -/
theorem dvd_dot_p_of_prim_vJ1 {nJ vl vJ1 p : ℤ × ℤ} {m c : ℤ}
    (hm : vJ1 = m • vl) (hprim : Primitive vJ1) (hp : p = -c • vl) :
    (-dot nJ vJ1) ∣ dot nJ p := by
  have hu := isUnit_m_of_prim_vJ1 hm hprim
  have hmm : m * m = 1 := by rcases Int.isUnit_iff.mp hu with h | h <;> rw [h] <;> ring
  have hv : dot nJ vJ1 = m * dot nJ vl := by rw [hm, dot_zsmul_loc]
  have hpp : dot nJ p = -c * dot nJ vl := by rw [hp, dot_zsmul_loc]
  refine ⟨m * c, ?_⟩
  rw [hv, hpp]
  linear_combination (c * dot nJ vl) * hmm

/-- ⭐⭐ 合流：共线 ＋ `Primitive vJ1` ⟹ 三条同时成立 —— `IsUnit m`（我 §11 那一条）、
`∀ c, m ∣ c`（他 §10 那一条，退化成恒真）、`e ∣ dot nJ vl`（§10 判伪器的 `hdvd`）。 -/
theorem side_condition_free_of_prim_vJ1 {nJ vl vJ1 : ℤ × ℤ} {m : ℤ}
    (hm : vJ1 = m • vl) (hprim : Primitive vJ1) :
    IsUnit m ∧ (∀ c : ℤ, m ∣ c) ∧ (-dot nJ vJ1) ∣ dot nJ vl := by
  have hu := isUnit_m_of_prim_vJ1 hm hprim
  exact ⟨hu, fun _ => hu.dvd, dvd_of_collinear_isUnit hm hu⟩

/-- lane-tower-hbase 分离见证里的 `vJ1 = 2 • (0,-1) = (0,-2)` **不本原**。 -/
theorem not_prim_hbase_sep_vJ1 : ¬ Primitive ((0, -2) : ℤ × ℤ) := by
  rintro ⟨a, b, hab⟩
  have h : a * (0 : ℤ) + b * (-2 : ℤ) = 1 := hab
  omega

/-- ⭐ §113 反方向打印：他那组数值上整除式确实成立而 `IsUnit m` 假，
**但同一组数值上 `Primitive vJ1` 也假** ⟹ 分离点在链上取不到。 -/
theorem hbase_sep_data_fails_prim_vJ1 :
    ((0, -2) : ℤ × ℤ) = (2 : ℤ) • ((0, -1) : ℤ × ℤ) ∧
      ((0, 4) : ℤ × ℤ) = -(4 : ℤ) • ((0, -1) : ℤ × ℤ) ∧
      dot (0, 1) ((0, -1) : ℤ × ℤ) < 0 ∧
      dot (0, 1) ((0, -2) : ℤ × ℤ) < 0 ∧
      (-dot (0, 1) ((0, -2) : ℤ × ℤ)) ∣ dot (0, 1) ((0, 4) : ℤ × ℤ) ∧
      ¬ IsUnit (2 : ℤ) ∧
      ¬ Primitive ((0, -2) : ℤ × ℤ) := by
  refine ⟨by norm_num [Prod.ext_iff], by norm_num [Prod.ext_iff], by norm_num [dot],
    by norm_num [dot], ⟨2, by norm_num [dot]⟩, ?_, not_prim_hbase_sep_vJ1⟩
  intro h
  rcases Int.isUnit_iff.mp h with h | h <;> omega

/-! ## §15 两条路线的**供给面**，本 lane 亲自数的（2026-09-25，无新声明）

lane-tower-hbase §4 说 `hsign : dot nJ vl < 0` 与 `hsweep : dot nJ vJ1 < 0` 是「两条链上字段」。
结论（`m = -1` 链上取不到）我在 §14 已收，但**「字段」这个词只对其中一条成立**，
本节记三条我自己跑出来的读数（不是转述，§55）：

1. `hsweep : dot nJ vJ1 < 0` **确是** `ChainDataGeomParts`（`ChainPartsFeed.lean`）的字段，
   而该结构**没有**任何一条字段约束 `dot nJ vl`。

   ⚠ **本条的第一版仪器是错的，已换掉（§102 自曝）**：我起初用文本正则数「结构体内
   `^  name :` 行」得 **36**，lane-tower-hbase 数得 37、文件自己的 docstring 写 34，三本账打架。
   我改用内核仪器复核：`getStructureFields` ＋ 逐字段 `ppExpr` 打印（收据
   `tmp/_fieldtypes.txt`，脚本 `tmp/wip/lane-env-refute-fieldtypes.lean`），得
   **`TOTAL=37`**，逐字段全类型里 `dot` 只出现五种形状 ——
   `dot nJ p` / `dot nJ vJ1` / `dot nJ w` / `dot nJ z₀` / `dot (det p vJ • (-p.2, p.1)) g`，
   **`dot _ vl` 命中 0**（带哨兵）。
   ⟹ 数字上 **hbase 的 37 对、我的 36 错**：我的正则 `[A-Za-z0-9_']` 漏掉了字段 `I₀`
   的下标字符。结论（没有字段约束 `dot nJ vl`）不变，但它现在靠的是内核读数，不是那条正则。
   ⚠ 出处：该读数取自 `ChainPartsFeed.olean`（2026-09-25 23:56:49 构建）；同文件源码
   在 2026-09-26 00:29:26 又被改过，故本条记的是 00:29 之前那一版。
2. `dot nJ vl < 0` 是**定理**不是字段：`LeafAShellLsideFork.dot_nJ_vl_neg_of_rec_p`。
   它的前提里 `hne` / `hlb` / `rec_p` / `hdot_nJ_p` 对应字段 `ahat_nonempty` / `hhp` /
   `rec_p` / `dot_nJ_p`，但另有两条**不是字段**：`hc : 0 < c` 与 `hp_neg : p = -(c : ℤ) • vl`。
   全树扫 `^\s{2,4}\w+ : p = -`（带哨兵）命中 **0** ⟹ `Nivat/**` 里没有任何结构字段说
   `p` 是 `vl` 的负倍数。
3. `Primitive vJ1` 同样不是字段：`ChainPartsFeed.lean` 的 `vJ1` 字段 docstring（集成者
   第 234 轮亲写）把它列为**缺失字段**，要由造结构的一侧带进来；并引 lane-leafa-shell 的
   `LaneLeafAShellLsideFork.prim_vJ1_not_from_sweep_obligations` 说它推不出来。

⟹ §113 两向：他那条路线额外要 `hp_neg`（＋`0 < c`），我这条路线额外要 `Primitive vJ1`，
**两边多出来的都来自造结构的一侧，不是结构自带的**。谁也不比谁更「现货」。

⚠ 进一步的限定，同样是我自己读的：`RegionSteps.lean` 里那条「`exists_chainData` 归约成
一个 `ChainDataGeomParts`」**已被撤回**（文件自记：没有任何 `ChainDataGeomParts` 被填充，
`toChainDataGeom` 已删）。⟹ 「是不是字段」这场比较目前对两边都只是记账，不是接链。

⚠ 重复件，交集成者裁（§110.2）：本文件 §14 的 `isUnit_m_of_prim_vJ1` 与
`GcdCollapse.isUnit_m_of_prim` 是同一条。我这边不 import 只是为了不增依赖面，
不是主张它更好；要删删我这条。 -/

/-! ## §16 `hdvd` 在**横截格**上是一条真欠账（本 lane 自限，2026-09-25）

§14 之后两边都同意：共线格里一切已定（`Primitive vJ1` ＋ 两条符号 binder 把 `m` 钉成 1，
`hdvd` 随之恒真）。⟹ §10 把判伪器从共线解绑，买到的东西只可能在**横截格**
（`det vl vJ1 ≠ 0`）里；§13 与 lane-tower-hbase §12 的非退化见证也都住在那里。

那就必须问下一个问题，而且要往对自己不利的方向问：**横截格上 `hdvd` 有产者吗？**

本节回答：**没有——它不是那组几何 binder 的推论。** 见证兑现了我能用字面数据兑现的
全部链上几何货：两条本原 ＋ `Primitive nJ` ＋ `Primitive p` ＋ 两条符号 binder ＋ `2 ≤ e`
＋ `p = -(c : ℤ) • vl` 且 `0 < c` ＋ `dot nJ p ≠ 0` ＋ `det vl vJ1 ≠ 0`，而 `hdvd` 为假。

⟹ §10 的账要这样记：它把「共线」这条前提换成了「`hdvd`」，**不是把它消掉了**。
共线格里换成了恒真项（§14），横截格里换成了一条同样没有产者的侧条件（本节）。
判伪器要在横截格上真咬人，`hdvd` 必须另有产者，或者由消费者当假设供。

⚠ 本节**不**主张「横截格上 `hdvd` 必假」——§13 的见证就住在横截格且 `hdvd` 真。
主张的只是「binder 组不蕴含它」，即 §55 意义上的**未定**，不是假。 -/

/-- ⭐ `hdvd` 不是横截格几何 binder 组的推论：全部链上几何货兑现而 `e ∤ dot nJ vl`。 -/
theorem hdvd_not_implied_by_transverse_binders :
    ∃ (nJ vl vJ1 p : ℤ × ℤ) (c : ℕ),
      Primitive nJ ∧ Primitive vl ∧ Primitive vJ1 ∧ Primitive p ∧
      dot nJ vl < 0 ∧ dot nJ vJ1 < 0 ∧
      2 ≤ -dot nJ vJ1 ∧
      0 < c ∧ p = -(c : ℤ) • vl ∧ dot nJ p ≠ 0 ∧
      det vl vJ1 ≠ 0 ∧
      ¬ ((-dot nJ vJ1) ∣ dot nJ vl) := by
  refine ⟨(0, 1), (1, -3), (1, -2), (-1, 3), 1,
    ⟨0, 1, by norm_num⟩, ⟨1, 0, by norm_num⟩, ⟨1, 0, by norm_num⟩, ⟨-1, 0, by norm_num⟩,
    by norm_num [dot], by norm_num [dot], by norm_num [dot], by norm_num,
    by norm_num [Prod.ext_iff], by norm_num [dot], by norm_num [det], ?_⟩
  rintro ⟨k, hk⟩
  simp only [dot] at hk
  omega

/-! ## §17 横截格：把侧条件从「高度」搬到「平移量」（集成者第 237 轮派工的可做部分）

集成者要横截格上按硬规矩 6 做三件事：定位原文那一句、核它的前提都在 37 条字段里、
**先算一个数值实例**。本节交后两件，第一件我不能做，理由写在报告里（原文阅读对本 lane
是常设禁令，要我读得由集成者显式解禁）。

### 侧条件的真实用量：只用在「实际发生的平移量」上

重读 §9 两条翻译引理的证明体（不是 docstring）后，`hdvd` 的用处分成两段，且**不对称**：

* `cover_hatOf_iff_cover_A` 只在 `hdvd.mul_left (kk i)` 一处用它 ⟹ 它真正需要的是
  **`e ∣ (kk i) · ⟪n_J, v_ℓ⟫` 逐指标成立**，不是 `e ∣ ⟪n_J, v_ℓ⟫`。
* `cover_base_of_cover_A` 里的倍数 `t` 是 `hsub` 存在性给出的，**任意自然数**都可能出现
  ⟹ 那一步躲不开整条 `hdvd`。

⟹ 于是有两条**互不比较**的判伪器，消费者按手上有什么选：

| | 侧条件 | `hmiss` 的落点 | 另需 |
|---|---|---|---|
| §10 `not_heights_of_base_misses_dvd` | `e ∣ ⟪n_J,v_ℓ⟫`（强） | `⋃ i, B i`（弱，因 `B i ⊆ A i`） | `hsub` |
| §17 `not_heights_of_A_misses_kk` | `∀ i, e ∣ kk i · ⟪n_J,v_ℓ⟫`（弱） | `⋃ i, A i`（强） | 无 |

⚠ §113 两向：新的这条**不是纯赚**。它砍掉 `hsub`、把侧条件换弱，代价是 `hmiss` 要在更大的
集合 `⋃ A i` 上成立（`subBA` 是字段，`B i ⊆ A i`，所以在 `A` 上漏掉比在 `B` 上漏掉更强）。

### 供给面（我自己读的，链侧不是原文）

`kk` 在 37 条字段里只是数据（`kk : ℕ → ℕ`），没有任何字段约束它的算术。
`ChainKK.lean` 自记两件与本节直接相关的事：`kk` **单调**（`∀ i j, i ≤ j → kk i ≤ kk j`），
且 **`kk ≡ 0` 已死**（`not_kkZero_of_anchor`，锚点的 `IsGreatest` 上界半边配 `hreach` 迫使
`kk` 无界）。⟹ 「取 `kk ≡ 0` 让侧条件平凡」这条逃生口是关着的；`hdvdK` 在链上等价于
「`kk` 的每一项都被 `e / gcd(e, ⟪n_J,v_ℓ⟫)` 整除」，那是关于 **`kk` 的算术**的债，
产者面在 `ChainKK` / `AhatMono` 一侧，**不在几何一侧** —— 这就是我这条线下一步该派的地方。
⚠ §55：`ChainKK.lean` 那两条是我读它的 docstring 与 `exists_normalised_chain` 的结论列，
未复跑其证明体。 -/

/-- 逐指标形的侧条件由整条 `hdvd` 蕴含（⟹ §17 的判伪器在侧条件上**弱于** §10 那条）。 -/
theorem hdvdK_of_hdvd {kk : ℕ → ℕ} {nJ vl : ℤ × ℤ} {e : ℤ} (hdvd : e ∣ dot nJ vl) :
    ∀ i, e ∣ (kk i : ℤ) * dot nJ vl := fun _ => hdvd.mul_left _

/-- ⭐ §9 那条等价的**逐指标版**：只要 `e` 整除实际发生的平移量 `kk i · ⟪n_J,v_ℓ⟫`。 -/
theorem cover_hatOf_iff_cover_A_kk {A : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ} {nJ vl : ℤ × ℤ} {e : ℤ}
    (hdvdK : ∀ i, e ∣ (kk i : ℤ) * dot nJ vl) :
    (∀ r : ℤ, ∃ z ∈ ⋃ i, Nivat.Colle35.hatOf A kk vl i, e ∣ (dot nJ z - r)) ↔
      (∀ r : ℤ, ∃ w ∈ ⋃ i, A i, e ∣ (dot nJ w - r)) := by
  constructor
  · intro h r
    obtain ⟨z, hz, hd⟩ := h r
    obtain ⟨i, hzi⟩ := Set.mem_iUnion.mp hz
    have hzi' : z + (kk i : ℤ) • vl ∈ A i := hzi
    refine ⟨z + (kk i : ℤ) • vl, Set.mem_iUnion.mpr ⟨i, hzi'⟩, ?_⟩
    have he : dot nJ (z + (kk i : ℤ) • vl) - r = (dot nJ z - r) + (kk i : ℤ) * dot nJ vl := by
      rw [dot_add_loc, dot_zsmul_loc]; ring
    rw [he]
    exact dvd_add hd (hdvdK i)
  · intro h r
    obtain ⟨w, hw, hd⟩ := h r
    obtain ⟨i, hwi⟩ := Set.mem_iUnion.mp hw
    refine ⟨w - (kk i : ℤ) • vl, Set.mem_iUnion.mpr ⟨i, ?_⟩, ?_⟩
    · show w - (kk i : ℤ) • vl + (kk i : ℤ) • vl ∈ A i
      simpa using hwi
    · have he : dot nJ (w - (kk i : ℤ) • vl) - r
          = (dot nJ w - r) - (kk i : ℤ) * dot nJ vl := by
        rw [dot_sub_loc, dot_zsmul_loc]; ring
      rw [he]
      exact dvd_sub hd (hdvdK i)

/-- ⭐⭐ **横截格可用的判伪器**：侧条件只压在 `kk` 上，`hsub` 不要，代价是 `hmiss` 落在
`⋃ i, A i` 上。共线性、`p`、递推全不进签名。 -/
theorem not_heights_of_A_misses_kk {A : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ}
    {nJ vl vJ1 : ℤ × ℤ} {cJ r₀ : ℤ}
    (hdvdK : ∀ i, (-dot nJ vJ1) ∣ (kk i : ℤ) * dot nJ vl)
    (hsweep : dot nJ vJ1 < 0)
    (hhp : ∀ g ∈ ⋃ i, Nivat.Colle35.hatOf A kk vl i, cJ ≤ dot nJ g)
    (hmiss : ∀ w ∈ ⋃ i, A i, ¬ ((-dot nJ vJ1) ∣ (dot nJ w - r₀))) :
    ¬ (∀ ε : ℕ, ∃ z ∈ reachSet (⋃ i, Nivat.Colle35.hatOf A kk vl i) vJ1,
        dot nJ z = cJ - (ε : ℤ) - 1) := by
  intro h
  obtain ⟨w, hw, hd⟩ :=
    (cover_hatOf_iff_cover_A_kk hdvdK).mp ((heights_iff_cover hsweep hhp).mp h) r₀
  exact hmiss w hw hd

/-! ### 数值实例（硬规矩 6：派几何义务前先算一个）

`nJ = (0,1)`、`vl = (1,-3)`、`vJ1 = (1,-2)`、`kk ≡ 2`、`A i = {(0,0)}`、`cJ = 0`、`r₀ = 1`。
`e = 2`，`⟪n_J,v_ℓ⟫ = -3`。⟹ **`hdvd` 在这组上为假**（`2 ∤ -3`，正是 §16 那组数据），
而 `hdvdK` 为真（`2 ∣ 2·(-3)`）；`det vl vJ1 = 1 ≠ 0` ⟹ 居民住在**横截格**里。
`⋃ hatOf = {(-2,6)}`（`kk ≡ 2` 把 `(0,0)` 往回推了 `2 • vl`），高度 `6 ≥ 0 = cJ` ⟹ `hhp` 真。 -/

def ATr : ℕ → Set (ℤ × ℤ) := fun _ => {(0, 0)}
def kkTr : ℕ → ℕ := fun _ => 2
def nTr : ℤ × ℤ := (0, 1)
def vlTr : ℤ × ℤ := (1, -3)
def vJ1Tr : ℤ × ℤ := (1, -2)

theorem iUnion_hatOf_ATr :
    (⋃ i, Nivat.Colle35.hatOf ATr kkTr vlTr i) = {((-2 : ℤ), (6 : ℤ))} := by
  ext z
  simp only [Set.mem_iUnion, Nivat.Colle35.hatOf, ATr, kkTr, vlTr, Set.mem_ofPred_eq,
    Set.mem_singleton_iff, Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul, exists_const]
  constructor
  · intro h; omega
  · intro h; omega

theorem hhp_ATr :
    ∀ g ∈ ⋃ i, Nivat.Colle35.hatOf ATr kkTr vlTr i, (0 : ℤ) ≤ dot nTr g := by
  intro g hg
  rw [iUnion_hatOf_ATr] at hg
  rw [show g = ((-2 : ℤ), (6 : ℤ)) from hg]
  norm_num [dot, nTr]

theorem hmiss_ATr :
    ∀ w ∈ ⋃ i, ATr i, ¬ ((-dot nTr vJ1Tr) ∣ (dot nTr w - 1)) := by
  intro w hw
  obtain ⟨i, hwi⟩ := Set.mem_iUnion.mp hw
  rw [show w = ((0 : ℤ), (0 : ℤ)) from hwi]
  rintro ⟨k, hk⟩
  simp only [dot, nTr, vJ1Tr] at hk
  omega

/-- ⭐ 数值实例：判伪器在**横截格**上真咬下去了，且是在 `hdvd` 为假的那组数据上。 -/
theorem not_heights_ATr :
    ¬ (∀ ε : ℕ, ∃ z ∈ reachSet (⋃ i, Nivat.Colle35.hatOf ATr kkTr vlTr i) vJ1Tr,
        dot nTr z = 0 - (ε : ℤ) - 1) :=
  not_heights_of_A_misses_kk (r₀ := 1)
    (fun _ => ⟨-3, by norm_num [dot, nTr, vJ1Tr, vlTr, kkTr]⟩)
    (by norm_num [dot, nTr, vJ1Tr]) hhp_ATr hmiss_ATr

/-- ⭐ 分离打印：同一组数据上 `hdvdK` 真而 `hdvd` 假，且 `det vl vJ1 ≠ 0`（横截）。 -/
theorem transverse_witness_beyond_hdvd :
    Primitive vlTr ∧ Primitive vJ1Tr ∧
      dot nTr vlTr < 0 ∧ dot nTr vJ1Tr < 0 ∧
      det vlTr vJ1Tr ≠ 0 ∧
      (∀ i, (-dot nTr vJ1Tr) ∣ (kkTr i : ℤ) * dot nTr vlTr) ∧
      ¬ ((-dot nTr vJ1Tr) ∣ dot nTr vlTr) := by
  refine ⟨⟨1, 0, by norm_num [vlTr]⟩, ⟨1, 0, by norm_num [vJ1Tr]⟩,
    by norm_num [dot, nTr, vlTr], by norm_num [dot, nTr, vJ1Tr],
    by norm_num [det, vlTr, vJ1Tr], fun _ => ⟨-3, by norm_num [dot, nTr, vJ1Tr, vlTr, kkTr]⟩, ?_⟩
  rintro ⟨k, hk⟩
  simp only [dot, nTr, vJ1Tr, vlTr] at hk
  omega

/-! ## §18 与 `hcomb` 那侧的桥：两条无产者侧条件同属一个算术族

集成者第 237 轮指出横截格上并列着两条无产者侧条件：`hcomb`（`RecVJComb.parts_rec_vJ` 要的）
与我的 `hdvd` / `hdvdK`。我自己读了那条签名复核（不是转述）：
`RecVJComb.parts_rec_vJ` 吃 `c` ＋ `hcomb : c.vJ = (a : ℤ) • p + (t : ℤ) • c.vJ1`（`a t : ℕ`），
证明体只用 `union_hhp c` / `c.hswept` / `c.rec_p` / `c.F.dot_nJ_vJ` ⟹ **确实不经 `bottom`**。

本节的观察：把 `hcomb` 对 `n_J` 取内积，配字段 `F.dot_nJ_vJ`（`⟪n_J, v_J⟫ = 0`）与
`hp : p = -c • v_ℓ`，直接得到**一条同族的整除式**

    e ∣ (a · c) · ⟪n_J, v_ℓ⟫          （`e := -⟪n_J, v_{ℓ_{J-1}}⟫`）

⟹ `hcomb` 不是随便一条侧条件：它本身就断言「`e` 整除 `⟪n_J,v_ℓ⟫` 的某个整数倍」，
和 `hdvdK`（`e ∣ kk i · ⟪n_J,v_ℓ⟫`）是**同一形状、不同乘数**。

⛔ **不主张它能兑现 `hdvdK`**：乘数不同（`a·c` 对 `kk i`），要接上必须再有一条把 `kk i`
与 `a·c` 联系起来的东西，那个我没有，也没在字段里看到。本节只把两侧钉在同一个算术族里，
并给一个**同时满足两侧**的数值实例（下一条），以便派工时不再各说各话。 -/

/-- ⭐ 桥：`hcomb` ＋ `⟪n_J,v_J⟫ = 0` ＋ `hp` ⟹ `e ∣ (a·c)·⟪n_J,v_ℓ⟫`。
⚠ 结论里没有任何带符号的 `det`，与禁令 26／32 无关。 -/
theorem dvd_mul_dot_vl_of_comb {nJ vl p vJ vJ1 : ℤ × ℤ} {a t : ℕ} {c : ℤ}
    (hcomb : vJ = (a : ℤ) • p + (t : ℤ) • vJ1)
    (hperp : dot nJ vJ = 0) (hp : p = -c • vl) :
    (-dot nJ vJ1) ∣ ((a : ℤ) * c) * dot nJ vl := by
  have h1 : dot nJ vJ = (a : ℤ) * dot nJ p + (t : ℤ) * dot nJ vJ1 := by
    rw [hcomb, dot_add_loc, dot_zsmul_loc, dot_zsmul_loc]
  have h2 : dot nJ p = -c * dot nJ vl := by rw [hp, dot_zsmul_loc]
  rw [h2, hperp] at h1
  exact ⟨-(t : ℤ), by linear_combination h1⟩

/-! ### 同时满足两侧的数值实例

沿用 §17 的横截居民，补上 `p` 与 `v_J`：`p = (-1,3) = -(1 : ℤ) • vl`、`vJ = (1,0)`。
`hcomb` 取 `a = 2`、`t = 3`：`2 • (-1,3) + 3 • (1,-2) = (-2+3, 6-6) = (1,0) = vJ` ✓。
`⟪n_J, v_J⟫ = 0` ✓、`Primitive vJ` ✓、`⟪n_J,p⟫ = 3 ≠ 0` ✓。
桥给出 `2 ∣ (2·1)·(-3) = -6` ✓，与 §17 的 `hdvdK`（`2 ∣ 2·(-3)`）一致，
而 `hdvd`（`2 ∣ -3`）依旧为假。 -/

def pTr : ℤ × ℤ := (-1, 3)
def vJTr : ℤ × ℤ := (1, 0)

/-- ⭐ 联合实例：`hcomb` 与 `hdvdK` 在同一组横截数据上同时成立，而 `hdvd` 假。 -/
theorem comb_and_dvdK_witness_Tr :
    pTr = -(1 : ℤ) • vlTr ∧
      vJTr = ((2 : ℕ) : ℤ) • pTr + ((3 : ℕ) : ℤ) • vJ1Tr ∧
      dot nTr vJTr = 0 ∧ Primitive vJTr ∧ dot nTr pTr ≠ 0 ∧
      det vlTr vJ1Tr ≠ 0 ∧
      (∀ i, (-dot nTr vJ1Tr) ∣ (kkTr i : ℤ) * dot nTr vlTr) ∧
      ¬ ((-dot nTr vJ1Tr) ∣ dot nTr vlTr) := by
  refine ⟨by norm_num [pTr, vlTr, Prod.ext_iff], by norm_num [vJTr, pTr, vJ1Tr, Prod.ext_iff],
    by norm_num [dot, nTr, vJTr], ⟨1, 0, by norm_num [vJTr]⟩, by norm_num [dot, nTr, pTr],
    by norm_num [det, vlTr, vJ1Tr],
    fun _ => ⟨-3, by norm_num [dot, nTr, vJ1Tr, vlTr, kkTr]⟩, ?_⟩
  rintro ⟨k, hk⟩
  simp only [dot, nTr, vJ1Tr, vlTr] at hk
  omega

end Nivat.EnvRefuteFaceNormal

#print axioms Nivat.EnvRefuteFaceNormal.nR
#print axioms Nivat.EnvRefuteFaceNormal.vJR
#print axioms Nivat.EnvRefuteFaceNormal.vlR
#print axioms Nivat.EnvRefuteFaceNormal.pR
#print axioms Nivat.EnvRefuteFaceNormal.vJ1R
#print axioms Nivat.EnvRefuteFaceNormal.aR
#print axioms Nivat.EnvRefuteFaceNormal.a'R
#print axioms Nivat.EnvRefuteFaceNormal.SR
#print axioms Nivat.EnvRefuteFaceNormal.mem_SR
#print axioms Nivat.EnvRefuteFaceNormal.prim_nR
#print axioms Nivat.EnvRefuteFaceNormal.prim_vJR
#print axioms Nivat.EnvRefuteFaceNormal.prim_vlR
#print axioms Nivat.EnvRefuteFaceNormal.prim_vJ1R
#print axioms Nivat.EnvRefuteFaceNormal.dot_nR_vJR
#print axioms Nivat.EnvRefuteFaceNormal.KR
#print axioms Nivat.EnvRefuteFaceNormal.convex_KR
#print axioms Nivat.EnvRefuteFaceNormal.latticeConvex_SR
#print axioms Nivat.EnvRefuteFaceNormal.aR_mem
#print axioms Nivat.EnvRefuteFaceNormal.a'R_mem
#print axioms Nivat.EnvRefuteFaceNormal.lex_SR
#print axioms Nivat.EnvRefuteFaceNormal.lex'_SR
#print axioms Nivat.EnvRefuteFaceNormal.edge_SR
#print axioms Nivat.EnvRefuteFaceNormal.edge'_SR
#print axioms Nivat.EnvRefuteFaceNormal.pR_ne
#print axioms Nivat.EnvRefuteFaceNormal.det_pR_vlR
#print axioms Nivat.EnvRefuteFaceNormal.hp_neg_R
#print axioms Nivat.EnvRefuteFaceNormal.collinear_R
#print axioms Nivat.EnvRefuteFaceNormal.sweep_R
#print axioms Nivat.EnvRefuteFaceNormal.dot_nR_pR
#print axioms Nivat.EnvRefuteFaceNormal.dot_nR_vlR
#print axioms Nivat.EnvRefuteFaceNormal.unit_dot_nJ_vl_not_of_face_binders
#print axioms Nivat.EnvRefuteFaceNormal.gcd_two_R
#print axioms Nivat.EnvRefuteFaceNormal.det_pR_vJ1R
#print axioms Nivat.EnvRefuteFaceNormal.unit_dot_nJ_vl_not_of_face_binders_prim
#print axioms Nivat.EnvRefuteFaceNormal.vJ1R_eq_vlR
#print axioms Nivat.EnvRefuteFaceNormal.cover_of_modulus_one
#print axioms Nivat.EnvRefuteFaceNormal.modulus_one_of_collinear_unit
#print axioms Nivat.EnvRefuteFaceNormal.heights_of_collinear_unit
#print axioms Nivat.EnvRefuteFaceNormal.heights_iff_cover_collinear
#print axioms Nivat.EnvRefuteFaceNormal.AR
#print axioms Nivat.EnvRefuteFaceNormal.mem_AR
#print axioms Nivat.EnvRefuteFaceNormal.AR_nonempty
#print axioms Nivat.EnvRefuteFaceNormal.AR_hhp
#print axioms Nivat.EnvRefuteFaceNormal.AR_rec_p
#print axioms Nivat.EnvRefuteFaceNormal.AR_rec_vJ
#print axioms Nivat.EnvRefuteFaceNormal.SR_sub_AR
#print axioms Nivat.EnvRefuteFaceNormal.AR_cover
#print axioms Nivat.EnvRefuteFaceNormal.AR_heights
#print axioms Nivat.EnvRefuteFaceNormal.conj1_heights_without_unit_magnitude
#print axioms Nivat.EnvRefuteFaceNormal.dot_sub_loc
#print axioms Nivat.EnvRefuteFaceNormal.modulus_dvd_dot_vl
#print axioms Nivat.EnvRefuteFaceNormal.cover_hatOf_iff_cover_A
#print axioms Nivat.EnvRefuteFaceNormal.cover_base_of_cover_A
#print axioms Nivat.EnvRefuteFaceNormal.cover_base_of_cover_hatOf
#print axioms Nivat.EnvRefuteFaceNormal.not_heights_of_base_misses
#print axioms Nivat.EnvRefuteFaceNormal.BaseSurvives
#print axioms Nivat.EnvRefuteFaceNormal.cover_hatOf_of_base_cover
#print axioms Nivat.EnvRefuteFaceNormal.dvd_of_dot_vl_eq_mul
#print axioms Nivat.EnvRefuteFaceNormal.not_heights_of_base_misses_dvd
#print axioms Nivat.EnvRefuteFaceNormal.dvd_of_collinear_isUnit
#print axioms Nivat.EnvRefuteFaceNormal.isUnit_of_collinear_dvd
#print axioms Nivat.EnvRefuteFaceNormal.dvd_iff_isUnit_of_collinear
#print axioms Nivat.EnvRefuteFaceNormal.ASing
#print axioms Nivat.EnvRefuteFaceNormal.kkS
#print axioms Nivat.EnvRefuteFaceNormal.nS
#print axioms Nivat.EnvRefuteFaceNormal.vS
#print axioms Nivat.EnvRefuteFaceNormal.prim_vS
#print axioms Nivat.EnvRefuteFaceNormal.mem_hatOf_ASing
#print axioms Nivat.EnvRefuteFaceNormal.iUnion_hatOf_ASing
#print axioms Nivat.EnvRefuteFaceNormal.hhp_ASing
#print axioms Nivat.EnvRefuteFaceNormal.hsub_ASing
#print axioms Nivat.EnvRefuteFaceNormal.hmiss_ASing
#print axioms Nivat.EnvRefuteFaceNormal.not_heights_ASing
#print axioms Nivat.EnvRefuteFaceNormal.hdvd_strictly_weaker_nondegenerate
#print axioms Nivat.EnvRefuteFaceNormal.isUnit_m_of_prim_vJ1
#print axioms Nivat.EnvRefuteFaceNormal.dvd_dot_p_of_prim_vJ1
#print axioms Nivat.EnvRefuteFaceNormal.side_condition_free_of_prim_vJ1
#print axioms Nivat.EnvRefuteFaceNormal.not_prim_hbase_sep_vJ1
#print axioms Nivat.EnvRefuteFaceNormal.hbase_sep_data_fails_prim_vJ1
#print axioms Nivat.EnvRefuteFaceNormal.hdvd_not_implied_by_transverse_binders
#print axioms Nivat.EnvRefuteFaceNormal.hdvdK_of_hdvd
#print axioms Nivat.EnvRefuteFaceNormal.cover_hatOf_iff_cover_A_kk
#print axioms Nivat.EnvRefuteFaceNormal.not_heights_of_A_misses_kk
#print axioms Nivat.EnvRefuteFaceNormal.ATr
#print axioms Nivat.EnvRefuteFaceNormal.kkTr
#print axioms Nivat.EnvRefuteFaceNormal.nTr
#print axioms Nivat.EnvRefuteFaceNormal.vlTr
#print axioms Nivat.EnvRefuteFaceNormal.vJ1Tr
#print axioms Nivat.EnvRefuteFaceNormal.iUnion_hatOf_ATr
#print axioms Nivat.EnvRefuteFaceNormal.hhp_ATr
#print axioms Nivat.EnvRefuteFaceNormal.hmiss_ATr
#print axioms Nivat.EnvRefuteFaceNormal.not_heights_ATr
#print axioms Nivat.EnvRefuteFaceNormal.transverse_witness_beyond_hdvd
#print axioms Nivat.EnvRefuteFaceNormal.dvd_mul_dot_vl_of_comb
#print axioms Nivat.EnvRefuteFaceNormal.pTr
#print axioms Nivat.EnvRefuteFaceNormal.vJTr
#print axioms Nivat.EnvRefuteFaceNormal.comb_and_dvdK_witness_Tr
