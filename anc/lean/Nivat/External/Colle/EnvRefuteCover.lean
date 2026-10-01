/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.ShellLine

/-!
# `bottom` 合取 1 的**充要**刻画：剩余类覆盖

`ChainPartsFeed.lean` 的 `ChainDataGeomParts.bottom` 字段的第一个合取支，剥掉沿 `vJ` 的
那一半之后，是一条纯高度陈述：

> `∀ ε : ℕ, ∃ z ∈ reachSet A vJ1, dot nJ z = cJ - (ε : ℤ) - 1`

（`reachSet` 见 `ShellLine.lean` 的 `reachSet`：`t : ℕ`，**单向**扫掠。）

本文件证明：在 `hsweep`（`dot nJ vJ1 < 0`）与 `hhp`（`∀ g ∈ A, cJ ≤ dot nJ g`）两条字段下，
上式**等价于**

> `∀ r : ℤ, ∃ g ∈ A, (-dot nJ vJ1) ∣ (dot nJ g - r)`

即「`dot nJ '' A` 打满 mod `e` 的每个剩余类」，`e := -dot nJ vJ1 > 0`。

## 这条为什么值钱

`gcd (dot nJ p) e = 1` 只是**进入**这个覆盖条件的**一条**路（`cover_of_gcd_one`：沿 `p`
迭代的单条等差轨道就已打满）。它不是合取 1 的内容。三个方向在本文件里各有内核见证：

| 方向 | 真值 | 本文件的见证 |
|---|---|---|
| `gcd = 1` ⟹ 高度条件 | ✅ | `heights_of_gcd_one` |
| 覆盖条件 ⟹ `gcd = 1` | ❌ | `cover_without_gcd_one`（整个上半平面，`gcd = 2`） |
| 五条字段 ⟹ 高度条件 | ❌ | `not_heights_of_rec_fields`（偶高度半平面） |

⟹ 找产者时要盯的是 `∀ r, ∃ g ∈ A, e ∣ dot nJ g - r`，**不是** `gcd = 1`。后者严格更强：
在 `Aup` 那个居民上 `gcd = 2` 而覆盖条件真。

⚠ 分界线是 `gcd (d, e) = 1`，**不是** `e ∤ d`：`not_heights_of_rec_fields` 里
`d = 2`、`e = 4` ⟹ `e ∤ d` 成立而高度条件为假。

⛔ **射程**：本文件只谈上面那条高度陈述，即 `bottom` 的**合取 1 的高度部分**。
`bottom` 的 `∀ k : ℤ, L ≤ k → z₀ + k • vJ ∈ …` 那一支（沿 `vJ` 的整条线）与后两个合取支
**一个字没测**。⛔ 也不涉及 `Â_∞` 的实际形状：`A` 在这里是任意集合，`p` 是任意向量。

## Main results

* `heights_iff_cover` — ⭐ 充要刻画。
* `cover_of_gcd_one` / `heights_of_gcd_one` — `gcd = 1` 是充分条件（走等差轨道）。
* `cover_without_gcd_one` — 覆盖条件不蕴含 `gcd = 1`。
* `not_heights_of_rec_fields` — 那五条字段不蕴含高度条件。
-/

namespace Nivat.EnvRefuteCover

open Nivat Nivat.LE2 Nivat.MaxEnv

/-! ## §0 自足的 `dot` 代数

只 import `ShellLine`，所以这两条本地重证（内容同 `ColleReg.dot_add` /
`ColleReg.dot_zsmul_right`，不引入依赖）。 -/

theorem dot_add_loc (n a b : ℤ × ℤ) : dot n (a + b) = dot n a + dot n b := by
  simp only [dot, Prod.fst_add, Prod.snd_add]
  ring

theorem dot_zsmul_loc (n : ℤ × ℤ) (k : ℤ) (v : ℤ × ℤ) : dot n (k • v) = k * dot n v := by
  simp only [dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

theorem dot_e2 (z : ℤ × ℤ) : dot ((0, 1) : ℤ × ℤ) z = z.2 := by simp [dot]

/-- 沿 `p` 向前迭代任意自然数次仍留在 `A`（只用 `rec_p` 这一条字段）。 -/
theorem iter_mem {A : Set (ℤ × ℤ)} {p : ℤ × ℤ} (hrec : ∀ g ∈ A, g + p ∈ A) :
    ∀ (k : ℕ) {g : ℤ × ℤ}, g ∈ A → g + (k : ℤ) • p ∈ A := by
  intro k
  induction k with
  | zero => intro g hg; simpa using hg
  | succ n ih =>
      intro g hg
      have h1 : g + ((n : ℤ) • p) + p ∈ A := hrec _ (ih hg)
      have h2 : g + (((n : ℕ) + 1 : ℕ) : ℤ) • p = g + ((n : ℤ) • p) + p := by
        push_cast
        rw [add_smul, one_smul, add_assoc]
      rwa [h2]

/-! ## §1 ⭐ 充要刻画 -/

/-- **`reachSet` 里每个点的高度都是某个 `A` 的点的高度减去步长的整数倍。**

`heights_iff_cover` 两个方向共用的换算：`z = g + t • vJ1` ⟹
`dot nJ z = dot nJ g + t * dot nJ vJ1`。 -/
theorem dot_reach {A : Set (ℤ × ℤ)} {nJ vJ1 z : ℤ × ℤ} (hz : z ∈ reachSet A vJ1) :
    ∃ g ∈ A, ∃ t : ℕ, dot nJ z = dot nJ g + (t : ℤ) * dot nJ vJ1 := by
  obtain ⟨g, hg, t, rfl⟩ := hz
  exact ⟨g, hg, t, by rw [dot_add_loc, dot_zsmul_loc]⟩

/-- ⭐⭐ **`bottom` 合取 1 的高度部分 ⟺ `dot nJ '' A` 覆盖 mod `e` 的每个剩余类。**

`e := -dot nJ vJ1`，由 `hsweep` 知 `0 < e`。两条前提都是 `ChainDataGeomParts` 的现成字段
（`hsweep` 即 `ChainGeom.lean` 的 `ChainDataGeom.dot_nJ_vJ1_neg` 那一侧，
`hhp` 即 `ahat_halfPlane` 那一侧）。

⚠ `hhp` 只被 ⟸ 方向用到：正是它保证补全所需的步数非负。`reachSet` 是单向扫掠
（`t : ℕ`），所以没有 `hhp` 时 ⟸ 方向会要求一个负步数。 -/
theorem heights_iff_cover {A : Set (ℤ × ℤ)} {nJ vJ1 : ℤ × ℤ} {cJ : ℤ}
    (hsweep : dot nJ vJ1 < 0) (hhp : ∀ g ∈ A, cJ ≤ dot nJ g) :
    (∀ ε : ℕ, ∃ z ∈ reachSet A vJ1, dot nJ z = cJ - (ε : ℤ) - 1) ↔
      (∀ r : ℤ, ∃ g ∈ A, (-dot nJ vJ1) ∣ (dot nJ g - r)) := by
  set e : ℤ := -dot nJ vJ1 with hedef
  have he : 0 < e := by rw [hedef]; omega
  have hv : dot nJ vJ1 = -e := by rw [hedef]; ring
  constructor
  · intro h r
    -- 取 `ε := (cJ - 1 - r) % e`，使层 `cJ - ε - 1` 恰落在 `r` 的剩余类里。
    set m : ℤ := (cJ - 1 - r) % e with hmdef
    have hm0 : 0 ≤ m := Int.emod_nonneg _ (ne_of_gt he)
    set ε : ℕ := m.toNat with hepsdef
    have heps : (ε : ℤ) = m := Int.toNat_of_nonneg hm0
    obtain ⟨z, hz, hlev⟩ := h ε
    obtain ⟨g, hg, t, hzt⟩ := dot_reach (nJ := nJ) hz
    refine ⟨g, hg, (cJ - 1 - r) / e + (t : ℤ), ?_⟩
    have hdm : e * ((cJ - 1 - r) / e) + m = cJ - 1 - r := Int.mul_ediv_add_emod _ _
    have hlev' : dot nJ g + (t : ℤ) * (-e) = cJ - (ε : ℤ) - 1 := by
      rw [← hv, ← hzt]; exact hlev
    linear_combination hlev' - hdm - heps
  · intro hcov ε
    obtain ⟨g, hg, k, hk⟩ := hcov (cJ - (ε : ℤ) - 1)
    -- `hhp` ⟹ 目标层严格低于 `A`，于是所需步数 `k` 为正。
    have hgh : cJ ≤ dot nJ g := hhp g hg
    have hk0 : 0 ≤ k := by
      by_contra hneg
      have h1 : e * k < 0 := mul_neg_of_pos_of_neg he (by omega)
      omega
    have hkt : ((k.toNat : ℕ) : ℤ) = k := Int.toNat_of_nonneg hk0
    refine ⟨g + ((k.toNat : ℕ) : ℤ) • vJ1, ⟨g, hg, k.toNat, rfl⟩, ?_⟩
    rw [dot_add_loc, dot_zsmul_loc, hkt, hv]
    linear_combination hk

/-! ## §2 `gcd = 1` 是**一条**充分路线

`rec_p` 给的是单条等差轨道 `dot nJ g₀ + k * d`（`d := dot nJ p`，`k : ℕ` 单向）。
`gcd d e = 1` 恰好让这条轨道自己就打满 mod `e`。 -/

/-- **`gcd (dot nJ p) e = 1` ⟹ 剩余类全覆盖。**

只用 `ahat_nonempty` / `rec_p` / `hsweep` 三条字段 ＋ `hcop`。⚠ 步数取在 `ℕ` 里
（`rec_p` 只给正向），靠 `% e` 落进 `[0, e)` 保证。 -/
theorem cover_of_gcd_one {A : Set (ℤ × ℤ)} {nJ vJ1 p : ℤ × ℤ}
    (hne : A.Nonempty) (hrec : ∀ g ∈ A, g + p ∈ A) (hsweep : dot nJ vJ1 < 0)
    (hcop : Int.gcd (dot nJ p) (-dot nJ vJ1) = 1) :
    ∀ r : ℤ, ∃ g ∈ A, (-dot nJ vJ1) ∣ (dot nJ g - r) := by
  set e : ℤ := -dot nJ vJ1 with hedef
  have he : 0 < e := by rw [hedef]; omega
  obtain ⟨u, v, huv⟩ : IsCoprime (dot nJ p) e := Int.isCoprime_iff_gcd_eq_one.mpr hcop
  obtain ⟨g₀, hg₀⟩ := hne
  intro r
  set a : ℤ := dot nJ g₀ with hadef
  set M : ℤ := u * (r - a) with hMdef
  have hm0 : 0 ≤ M % e := Int.emod_nonneg _ (ne_of_gt he)
  set k : ℕ := (M % e).toNat with hkdef
  have hkv : (k : ℤ) = M % e := Int.toNat_of_nonneg hm0
  refine ⟨g₀ + (k : ℤ) • p, iter_mem hrec k hg₀, -(r - a) * v - (M / e) * dot nJ p, ?_⟩
  have hdm : e * (M / e) + M % e = M := Int.mul_ediv_add_emod _ _
  rw [dot_add_loc, dot_zsmul_loc, ← hadef]
  linear_combination (r - a) * huv + dot nJ p * hkv + dot nJ p * hdm

/-- **`gcd = 1` ⟹ `bottom` 合取 1 的高度部分。**

⚠ 这条与 `NlmaxGcd.lean` 的 `bottom_heights_of_gcd_one` 同结论；区别在于它**经过**
`heights_iff_cover`，因此把「哪一步是充分而非必要的」定位在 `cover_of_gcd_one` 这一步上。

⚠ **两条都留（集成者第 236 轮 §110.2 裁决）**：辖域不同 —— 本条吃抽象的
`A : Set (ℤ × ℤ)` ＋ `rec_p`，`NlmaxGcd` 那条吃字段形；删任一条都丢一个辖域，
而删除要触发重放、买不到东西。⟹ 这不是待清理的重复，是有意保留的两个辖域。 -/
theorem heights_of_gcd_one {A : Set (ℤ × ℤ)} {nJ vJ1 p : ℤ × ℤ} {cJ : ℤ}
    (hne : A.Nonempty) (hrec : ∀ g ∈ A, g + p ∈ A) (hhp : ∀ g ∈ A, cJ ≤ dot nJ g)
    (hsweep : dot nJ vJ1 < 0) (hcop : Int.gcd (dot nJ p) (-dot nJ vJ1) = 1) :
    ∀ ε : ℕ, ∃ z ∈ reachSet A vJ1, dot nJ z = cJ - (ε : ℤ) - 1 :=
  (heights_iff_cover hsweep hhp).mpr (cover_of_gcd_one hne hrec hsweep hcop)

/-! ## §3 覆盖条件严格弱于 `gcd = 1`

整个上半平面：`nJ = (0,1)`、`p = (1,2)`、`vJ1 = (0,-2)` ⟹ `d = 2`、`e = 2`、`gcd = 2`，
而覆盖条件成立（`A` 自己就含每个高度）。 -/

/-- 整个上半平面。高度集是全部非负整数 ⟹ 每个剩余类都被打到。 -/
def Aup : Set (ℤ × ℤ) := {w : ℤ × ℤ | 0 ≤ w.2}

theorem aup_cover : ∀ r : ℤ, ∃ g ∈ Aup, (2 : ℤ) ∣ (dot ((0, 1) : ℤ × ℤ) g - r) := by
  intro r
  refine ⟨(0, |r|), ?_, ?_⟩
  · show (0 : ℤ) ≤ ((0, |r|) : ℤ × ℤ).2
    exact abs_nonneg r
  · rw [dot_e2]
    rcases abs_choice r with h | h
    · exact ⟨0, by simp [h]⟩
    · exact ⟨-r, by rw [h]; ring⟩

/-- ⭐ **覆盖条件成立而 `gcd = 2`。**

⟹ `heights_iff_cover` 的右边**不能**换成 `gcd = 1`：那会把这个居民排除掉。 -/
theorem cover_without_gcd_one :
    (∀ r : ℤ, ∃ g ∈ Aup, (-dot ((0, 1) : ℤ × ℤ) ((0, -2) : ℤ × ℤ)) ∣
        (dot ((0, 1) : ℤ × ℤ) g - r)) ∧
      Int.gcd (dot ((0, 1) : ℤ × ℤ) ((1, 2) : ℤ × ℤ))
        (-dot ((0, 1) : ℤ × ℤ) ((0, -2) : ℤ × ℤ)) ≠ 1 := by
  refine ⟨?_, by norm_num [dot]⟩
  have h : (-dot ((0, 1) : ℤ × ℤ) ((0, -2) : ℤ × ℤ)) = 2 := by norm_num [dot]
  rw [h]
  exact aup_cover

/-! ## §4 那五条字段不蕴含高度条件

`ahat_nonempty` / `rec_p` / `ahat_halfPlane` / `hsweep` / `dot_nJ_p` 全真，而高度条件假。
居民：偶高度半平面，`nJ = (0,1)`、`p = (1,2)`、`vJ1 = (0,-4)` ⟹ `d = 2`、`e = 4`。

⚠ 这一组数值是**故意**取 `e ∤ d` 成立的：它同时说明分界线不是 `e ∤ d` 而是 `gcd = 1`。 -/

/-- 偶高度半平面。`p` 与 `vJ1` 的高度都是偶数 ⟹ 整个 `reachSet` 的高度恒为偶。 -/
def Aeven : Set (ℤ × ℤ) := {w : ℤ × ℤ | 0 ≤ w.2 ∧ (2 : ℤ) ∣ w.2}

theorem aeven_nonempty : Aeven.Nonempty := ⟨(0, 0), by simp [Aeven]⟩

theorem aeven_rec_p : ∀ g ∈ Aeven, g + ((1, 2) : ℤ × ℤ) ∈ Aeven := by
  rintro g ⟨h0, k, hk⟩
  refine ⟨?_, k + 1, ?_⟩ <;> simp only [Prod.snd_add] <;> omega

theorem aeven_halfPlane : ∀ g ∈ Aeven, (0 : ℤ) ≤ dot ((0, 1) : ℤ × ℤ) g := by
  rintro g ⟨h0, -⟩
  rw [dot_e2]
  exact h0

/-- **偶步长扫掠偶半平面，高度恒偶。** -/
theorem even_dot_of_mem_reach {v : ℤ × ℤ} (hv : (2 : ℤ) ∣ v.2) :
    ∀ z ∈ reachSet Aeven v, (2 : ℤ) ∣ dot ((0, 1) : ℤ × ℤ) z := by
  rintro z ⟨g, ⟨-, k, hk⟩, t, rfl⟩
  obtain ⟨m, hm⟩ := hv
  refine ⟨k + (t : ℤ) * m, ?_⟩
  rw [dot_e2]
  simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, hk, hm]
  ring

/-- ⭐ **五条字段不蕴含 `bottom` 合取 1 的高度部分。**

⚠ 见证里 `¬ ((-dot nJ vJ1) ∣ dot nJ p)` 也成立（`d = 2`、`e = 4`）⟹ 把 `gcd = 1`
换成 `e ∤ d` 不足以救回结论。 -/
theorem not_heights_of_rec_fields :
    ¬ ∀ (A : Set (ℤ × ℤ)) (nJ vJ1 p : ℤ × ℤ) (cJ : ℤ),
        A.Nonempty →
        (∀ g ∈ A, g + p ∈ A) →
        (∀ g ∈ A, cJ ≤ dot nJ g) →
        dot nJ vJ1 < 0 →
        dot nJ p ≠ 0 →
        ¬ ((-dot nJ vJ1) ∣ dot nJ p) →
        ∀ ε : ℕ, ∃ z ∈ reachSet A vJ1, dot nJ z = cJ - (ε : ℤ) - 1 := by
  intro h
  obtain ⟨z, hz, hlev⟩ :=
    h Aeven (0, 1) (0, -4) (1, 2) 0 aeven_nonempty aeven_rec_p aeven_halfPlane
      (by norm_num [dot]) (by norm_num [dot]) (by norm_num [dot]) 0
  obtain ⟨c, hc⟩ := even_dot_of_mem_reach (by norm_num) z hz
  rw [hlev] at hc
  omega

end Nivat.EnvRefuteCover

#print axioms Nivat.EnvRefuteCover.dot_add_loc
#print axioms Nivat.EnvRefuteCover.dot_zsmul_loc
#print axioms Nivat.EnvRefuteCover.dot_e2
#print axioms Nivat.EnvRefuteCover.iter_mem
#print axioms Nivat.EnvRefuteCover.dot_reach
#print axioms Nivat.EnvRefuteCover.heights_iff_cover
#print axioms Nivat.EnvRefuteCover.cover_of_gcd_one
#print axioms Nivat.EnvRefuteCover.heights_of_gcd_one
#print axioms Nivat.EnvRefuteCover.Aup
#print axioms Nivat.EnvRefuteCover.aup_cover
#print axioms Nivat.EnvRefuteCover.cover_without_gcd_one
#print axioms Nivat.EnvRefuteCover.Aeven
#print axioms Nivat.EnvRefuteCover.aeven_nonempty
#print axioms Nivat.EnvRefuteCover.aeven_rec_p
#print axioms Nivat.EnvRefuteCover.aeven_halfPlane
#print axioms Nivat.EnvRefuteCover.even_dot_of_mem_reach
#print axioms Nivat.EnvRefuteCover.not_heights_of_rec_fields
