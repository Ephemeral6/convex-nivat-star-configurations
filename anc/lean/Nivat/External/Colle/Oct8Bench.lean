/-
Copyright (c) 2026. Released under Apache 2.0 license.
Authors: lane-tower-hbase
-/
import Nivat.External.Colle.ShellSweep
import Nivat.External.Colle.ChainExhaustInter
import Nivat.External.Colle.AhatMono
import Nivat.External.Colle.ShellSubStrip
import Nivat.External.Colle.RegionOrientBridge

set_option autoImplicit false

/-!
# `lane-tower-hbase` (α): a legal octagonal instance for `shellSubStrip`

> **主仓准入记录（§96，team-lead 2026-09-24 批准）**：本文件原为 lane 私有台架
> `tmp/wip/lane-tower-hbase-oct8.lean`，按 §96 (B) 类「共享模型层」提进主仓，唯一理由是
> §16 禁 tmp↔tmp import ⟹ 下游 lane（指名消费者 **lane-leafa-shell**，要 `Sphi` / `shellInter_eq`
> / `mem_oct8'` / `two_le_KK` / `nd8_*` / `face_le2_Sphi` / `two_le_face_oct8` 这些**定理**）
> 除了主仓没有第二条路拿到它们。
> ⚠ 三条纪律随文件一起生效：
> 1. **整文件搬，不许拆**——拆出单条定理去抄就是 §16 的 drift。
> 2. **独占 namespace `Nivat.LaneTowerOct8`**；主仓任何文件都**不要** `open` 它。
>    §75 declscan 实测本文件 104 个声明名里有 6 个与主仓既有短名重名
>    （`Ahat` / `Sphi` / `dot_mk` / `eq_of_dot_eq_dot` / `face_eq_singleton_of_corner` / `hatOf_eq`），
>    全部靠 namespace 隔离，**不 `open` 就不咬**（CLAUDE.md 盲区 2）。
> 3. 本文件是 **leaf**：主仓无人 import 它（`gen_all.py` 生成的 `All.lean` 除外）。
>    它本身是一份**反证台架**，`not_shellSubStrip_body` 之类的结论只在这套具体参数上成立，
>    ⛔ **不许**被当作关于链上 `shellSubStrip` 的一般事实引用（§54）。

Target: `ofPartsExhaustsInter`'s `shellSubStrip` binder (in `ChainExhaustInter.lean`; find it by
binder name — §85.3: line numbers into that file drift whenever a binder docstring is
rewritten, so this file cites names only), at the
**fan successor** selection of `ν_{J+1}` that `b3_colle2.txt:518` fixes (team-lead's 第 217 轮
裁决：**`J+1` 照抄原文，「扇形后继」这个读法登记成我们的补充、不是转写**；他 2026-09-24
的那条旧裁决按 §50 已作废——全仓唯一的载体就是本行的转述，找不到出处的裁决不作数）。
§22/§24/§25 of `lane-tower-hbase-substrip.lean` reduced the binder to one question
about the tower; this file supplies the instance.

⚠ **锚订正 + 两条债（第 217 轮实测，已报 team-lead 待裁）**。原写 `:517`，那一行**逐字就是空字符串**；
真址是 `:518` 的显示式
`Â_i^{(ε)} := {g − t·v⃗_{ℓ_{J+1}} ∈ Â_∞^{(ε)} : g ∈ Â_i, t ∈ ℤ₊}`。但订正完号码之后，
`:518` 上量出两条不是格式问题的东西：

1. **`ℓ_{J+1}` 全文只出现这一次，从未被选定**（`grep -c '_{J+1}' scratch/b3_colle2.txt` = **1**；
   对照 `_{J}` 有 12 处；`:432` 给的范围 `ι+1 ≤ J ≤ ι+m-1` 使 `J+1` 是合法下标）。
   论文没有一句说 `ℓ_{J+1}` 是哪条、怎么选。⟹ 上面那句「fan successor」是**我们的裁决**，
   不是论文的转写；按硬规矩 5 这是债，不是对应物。
2. **结构平行的那条用的是 `J−1` 和 `+`**：`:440` / `:458` 都写
   `Â_∞^{(ε)} := {g + t·v⃗_{ℓ_{J-1}} : …}`。下标差 2、符号相反。
   `:738` 的枚举 `w_{i+1} is a successor edge of w_i` 是 mod `2m` 的，`ℓ_{J+1}` 与 `ℓ_{J-1}`
   相差两步，一般**不**互为相反向。⟹「`:518` 是否 `:440` 的笔误」论文自己没给判据，
   而两种读法给出**不同的 `w`**。

⟹ 逐字对齐的部分（这一条不欠）：`:518` 的集合构造式
`= reachSet Â_i (−v⃗_{ℓ_{J+1}}) ∩ Â_∞^{(ε)} = ShellMink.shellInter Â_i Â_∞^{(ε)} w`，
其中 `w := −v⃗_{ℓ_{J+1}}`——**负号被 `w` 吸收**。台架上 `w` 取 `wfan`。
⛔ 本文件**不主张** `wfan` 对应原文哪个定向（§54）：那与链上 `vJ` 的定向是同一条红线
（第 179 轮：`vl` ＝ 原文 `v⃗_{ℓ_ι}` 证出来之前，定向敏感判据双向都不许搬）。

## The assignment

Fan `E ↑𝒮_φ` = the eight primitive normals

`u₁=(1,0), u₂=(1,1), u₃=(0,1), u₄=(-1,1), u₅=(-1,0), u₆=(-1,-1), u₇=(0,-1), u₈=(1,-1)`

(ccw, consecutive `det = 1`, so the fan is smooth).  Then

* `ℓ = u₈ = (1,-1)`, `n_ℓ = -ℓ = u₄ = (-1,1)`, `v⃗_ℓ = dir(-n_ℓ) = (1,1)`, `cz = 0`;
* `J = u₁ = (1,0)`, `n_J = -J = (-1,0)`, `c_J = 0` — `0 < det ℓ J = 1`;
* `Arc _ J n_ℓ = {u₂, u₃}` has **two** elements, so successor ≠ predecessor;
* `ν_{J+1} = u₂ = (1,1)` is the ccw **successor of `J`** (`Arc _ J ν_{J+1} = ∅`), which is the
  paper's choice, and `w = -(dir ν_{J+1}) = (1,-1)`;
* `μ = u₃ = (0,1) ∈ Arc _ ν_{J+1} n_ℓ`, so `ν := -μ = u₇ = (0,-1)` is an **escaping wall**:
  `dot ν v⃗_ℓ = -1 ≤ 0 < 1 = dot ν w`;
* `v_{J+1} = v⃗_ℓ = (1,1)` (here `J = ι + 1`, allowed by `b3_colle2.txt:502`).

## Why the guard is not vacuous

`shellSubStrip` carries the envelopedness guard, and `PROTOCOL.md §41` forbids refuting a guarded
binder without first proving the guard satisfiable.  The guard is **not** free here: sweeping
`Â_i` along `w` deletes the three normals `u₁, u₇, u₈` (`0 < dot u w`), and the shell restores
only `u₁` (its `n_J`-floor) and `u₈` (the surviving edge of `Â_∞`).  The eighth, `u₇`, comes back
**only by lattice rounding**: the corner of `shellInter` between `u₆` and `u₈` has
`det u₆ u₈ = 2`, so when `-x-y ≤ d₆` has `d₆` **odd** the apex is half-integral and the lattice
hull grows a genuine `u₇`-edge with two points.  Every `Â_i` below is built with `d₆` odd for
exactly that reason.  This is the same mechanism `lane-env-refute` found for `hwedgeE`, used here
in the opposite direction — to *make* the guard true.
-/

open Nivat Nivat.LE2 Nivat.MaxEnv Nivat.ShellMink Nivat.Colle35

namespace Nivat.LaneTowerOct8

/-! ## §1  The corner lemma -/

/-- Cramer: `det u v • n = det n v • u + det u n • v`, paired with `z`. -/
theorem dot_cramer (u v n z : ℤ × ℤ) :
    det u v * dot n z = det n v * dot u z + det u n * dot v z := by
  simp only [det, dot]; ring

/-- Two lattice points agreeing on two independent normals are equal. -/
theorem eq_of_dot_eq_dot {u v z z' : ℤ × ℤ} (hd : det u v ≠ 0)
    (h1 : dot u z = dot u z') (h2 : dot v z = dot v z') : z = z' := by
  have k1 : dot u z - dot u z' = 0 := by omega
  have k2 : dot v z - dot v z' = 0 := by omega
  simp only [dot] at k1 k2
  have e1 : det u v * (z.1 - z'.1) = 0 := by
    simp only [det]; linear_combination v.2 * k1 - u.2 * k2
  have e2 : det u v * (z.2 - z'.2) = 0 := by
    simp only [det]; linear_combination (-v.1) * k1 + u.1 * k2
  have f1 : z.1 - z'.1 = 0 := by
    rcases mul_eq_zero.mp e1 with h | h
    · exact absurd h hd
    · exact h
  have f2 : z.2 - z'.2 = 0 := by
    rcases mul_eq_zero.mp e2 with h | h
    · exact absurd h hd
    · exact h
  exact Prod.ext_iff.mpr ⟨by omega, by omega⟩

/-- **Corner lemma.**  A normal strictly inside `cone{u,v}` has a singleton face when `V`
maximises both `u` and `v`. -/
theorem face_eq_singleton_of_corner {R : Set (ℤ × ℤ)} {u v n V : ℤ × ℤ}
    (hVR : V ∈ R)
    (hu : ∀ z ∈ R, dot u z ≤ dot u V) (hv : ∀ z ∈ R, dot v z ≤ dot v V)
    (hcu : 0 < det u n) (hcv : 0 < det n v) (hd : 0 < det u v) :
    face R n = {V} := by
  have hle : ∀ z ∈ R, dot n z ≤ dot n V := by
    intro z hz
    have hc := dot_cramer u v n z
    have hcV := dot_cramer u v n V
    have h1 : det n v * dot u z ≤ det n v * dot u V :=
      mul_le_mul_of_nonneg_left (hu z hz) hcv.le
    have h2 : det u n * dot v z ≤ det u n * dot v V :=
      mul_le_mul_of_nonneg_left (hv z hz) hcu.le
    nlinarith
  ext z
  simp only [Set.mem_singleton_iff]
  constructor
  · rintro ⟨hzR, hzmax⟩
    have h1 : dot u z = dot u V := le_antisymm (hu z hzR) (by
      have := hzmax V hVR
      nlinarith [dot_cramer u v n z, dot_cramer u v n V, hv z hzR, hcv, hcu])
    have h2 : dot v z = dot v V := le_antisymm (hv z hzR) (by
      have := hzmax V hVR
      nlinarith [dot_cramer u v n z, dot_cramer u v n V, hu z hzR, hcv, hcu])
    exact eq_of_dot_eq_dot (ne_of_gt hd) h1 h2
  · rintro rfl
    exact ⟨hVR, hle⟩

/-! ## §2  The octagonal family `oct8`

`oct8 c₁ … c₈ := {z | dot uₖ z ≤ cₖ}`.  Consecutive normals have `det = 1`, so all eight
vertices are lattice points:

`V₁=(c₁,c₂-c₁)`, `V₂=(c₂-c₃,c₃)`, `V₃=(c₃-c₄,c₃)`, `V₄=(-c₅,c₄-c₅)`,
`V₅=(-c₅,c₅-c₆)`, `V₆=(c₇-c₆,-c₇)`, `V₇=(c₈-c₇,-c₇)`, `V₈=(c₁,c₁-c₈)`. -/

/-- `x ≤ c₁`, `x+y ≤ c₂`, `y ≤ c₃`, `-x+y ≤ c₄`, `-x ≤ c₅`, `-x-y ≤ c₆`, `-y ≤ c₇`,
`x-y ≤ c₈`. -/
def oct8 (c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ : ℤ) : Set (ℤ × ℤ) :=
  {z | z.1 ≤ c₁ ∧ z.1 + z.2 ≤ c₂ ∧ z.2 ≤ c₃ ∧ -z.1 + z.2 ≤ c₄ ∧ -z.1 ≤ c₅ ∧
    -z.1 - z.2 ≤ c₆ ∧ -z.2 ≤ c₇ ∧ z.1 - z.2 ≤ c₈}

theorem mem_oct8 {c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ : ℤ} {z : ℤ × ℤ} :
    z ∈ oct8 c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ ↔ z.1 ≤ c₁ ∧ z.1 + z.2 ≤ c₂ ∧ z.2 ≤ c₃ ∧
      -z.1 + z.2 ≤ c₄ ∧ -z.1 ≤ c₅ ∧ -z.1 - z.2 ≤ c₆ ∧ -z.2 ≤ c₇ ∧ z.1 - z.2 ≤ c₈ := Iff.rfl

theorem mem_oct8' {c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ x y : ℤ} :
    ((x, y) : ℤ × ℤ) ∈ oct8 c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ ↔ x ≤ c₁ ∧ x + y ≤ c₂ ∧ y ≤ c₃ ∧
      -x + y ≤ c₄ ∧ -x ≤ c₅ ∧ -x - y ≤ c₆ ∧ -y ≤ c₇ ∧ x - y ≤ c₈ := Iff.rfl

theorem dot_mk (n : ℤ × ℤ) (x y : ℤ) : dot n ((x, y) : ℤ × ℤ) = n.1 * x + n.2 * y := rfl

/-- Each of the eight edges carries at least two lattice points. -/
def Nd8 (c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ : ℤ) : Prop :=
  1 ≤ c₂ + c₈ - 2 * c₁ ∧ 1 ≤ c₁ + c₃ - c₂ ∧ 1 ≤ c₂ + c₄ - 2 * c₃ ∧ 1 ≤ c₃ + c₅ - c₄ ∧
    1 ≤ c₄ + c₆ - 2 * c₅ ∧ 1 ≤ c₅ + c₇ - c₆ ∧ 1 ≤ c₆ + c₈ - 2 * c₇ ∧ 1 ≤ c₁ + c₇ - c₈

/-- The eight edge normals. -/
def oct8E : Set (ℤ × ℤ) :=
  {((1 : ℤ), (0 : ℤ)), ((1 : ℤ), (1 : ℤ)), ((0 : ℤ), (1 : ℤ)), ((-1 : ℤ), (1 : ℤ)),
    ((-1 : ℤ), (0 : ℤ)), ((-1 : ℤ), (-1 : ℤ)), ((0 : ℤ), (-1 : ℤ)), ((1 : ℤ), (-1 : ℤ))}

theorem mem_oct8E {n : ℤ × ℤ} :
    n ∈ oct8E ↔ n = ((1 : ℤ), (0 : ℤ)) ∨ n = ((1 : ℤ), (1 : ℤ)) ∨ n = ((0 : ℤ), (1 : ℤ)) ∨
      n = ((-1 : ℤ), (1 : ℤ)) ∨ n = ((-1 : ℤ), (0 : ℤ)) ∨ n = ((-1 : ℤ), (-1 : ℤ)) ∨
      n = ((0 : ℤ), (-1 : ℤ)) ∨ n = ((1 : ℤ), (-1 : ℤ)) := by
  simp only [oct8E, Set.mem_insert_iff, Set.mem_singleton_iff]

/-- **`E (oct8 …) ⊆ oct8E`.**  A normal off the eight rays sits strictly inside one of the eight
corner cones, where the corner lemma makes its face a singleton. -/
theorem E_oct8_subset {c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ : ℤ} (h : Nd8 c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈) :
    E (oct8 c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈) ⊆ oct8E := by
  obtain ⟨hA, hB, hC, hD, hE, hF, hG, hH⟩ := h
  rintro n ⟨hprim, hnt⟩
  by_contra hne
  rw [mem_oct8E] at hne
  push_neg at hne
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8⟩ := hne
  have corner : ∀ u v V : ℤ × ℤ, V ∈ oct8 c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ →
      (∀ z ∈ oct8 c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈, dot u z ≤ dot u V) →
      (∀ z ∈ oct8 c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈, dot v z ≤ dot v V) →
      0 < det u n → 0 < det n v → 0 < det u v → False := by
    intro u v V hV hu hv h1 h2 h3
    rw [face_eq_singleton_of_corner hV hu hv h1 h2 h3] at hnt
    exact absurd hnt (by simp)
  have ray : ∀ μ : ℤ × ℤ, Prim μ → det μ n = 0 → n = μ ∨ n = -μ := by
    intro μ hμ hdet
    exact eq_or_neg_of_prim_of_det_eq_zero hμ hprim hdet
  rcases lt_trichotomy n.2 0 with hy | hy | hy
  · -- lower half: split on n.1 - n.2 and n.1 and n.1 + n.2
    rcases lt_trichotomy (n.1 + n.2) 0 with hs | hs | hs
    · rcases lt_trichotomy n.1 0 with hx | hx | hx
      · rcases lt_trichotomy (n.1 - n.2) 0 with hq | hq | hq
        · -- C5 : between u₅=(-1,0) and u₆=(-1,-1), V = V₅ = (-c₅, c₅-c₆)
          refine corner ((-1 : ℤ), (0 : ℤ)) ((-1 : ℤ), (-1 : ℤ))
            ((-c₅ : ℤ), (c₅ - c₆ : ℤ)) ?_ ?_ ?_ ?_ ?_ ?_
          · rw [mem_oct8']; omega
          · intro z hz; rw [mem_oct8] at hz; simp only [dot, dot_mk]; omega
          · intro z hz; rw [mem_oct8] at hz; simp only [dot, dot_mk]; omega
          · simp only [det]; omega
          · simp only [det]; omega
          · simp only [det]; omega
        · rcases ray ((-1 : ℤ), (-1 : ℤ)) (by decide) (by simp only [det]; omega) with hn | hn
          · exact r6 hn
          · exact absurd hn (by intro hh; rw [hh] at hy; simp at hy)
        · -- C6 : between u₆=(-1,-1) and u₇=(0,-1), V = V₆ = (c₇-c₆, -c₇)
          refine corner ((-1 : ℤ), (-1 : ℤ)) ((0 : ℤ), (-1 : ℤ))
            ((c₇ - c₆ : ℤ), (-c₇ : ℤ)) ?_ ?_ ?_ ?_ ?_ ?_
          · rw [mem_oct8']; omega
          · intro z hz; rw [mem_oct8] at hz; simp only [dot, dot_mk]; omega
          · intro z hz; rw [mem_oct8] at hz; simp only [dot, dot_mk]; omega
          · simp only [det]; omega
          · simp only [det]; omega
          · simp only [det]; omega
      · -- n.1 = 0, n.2 < 0 : ray u₇
        rcases ray ((0 : ℤ), (-1 : ℤ)) (by decide) (by simp only [det]; omega) with hn | hn
        · exact r7 hn
        · exact absurd hn (by intro hh; rw [hh] at hy; simp at hy)
      · -- C7 : between u₇=(0,-1) and u₈=(1,-1), V = V₇ = (c₈-c₇, -c₇)
        refine corner ((0 : ℤ), (-1 : ℤ)) ((1 : ℤ), (-1 : ℤ))
          ((c₈ - c₇ : ℤ), (-c₇ : ℤ)) ?_ ?_ ?_ ?_ ?_ ?_
        · rw [mem_oct8']; omega
        · intro z hz; rw [mem_oct8] at hz; simp only [dot, dot_mk]; omega
        · intro z hz; rw [mem_oct8] at hz; simp only [dot, dot_mk]; omega
        · simp only [det]; omega
        · simp only [det]; omega
        · simp only [det]; omega
    · -- n.1 + n.2 = 0, n.2 < 0 : ray u₈ = (1,-1)
      rcases ray ((1 : ℤ), (-1 : ℤ)) (by decide) (by simp only [det]; omega) with hn | hn
      · exact r8 hn
      · exact absurd hn (by
          intro hh; rw [hh] at hy; simp only [Prod.snd_neg] at hy; omega)
    · -- C8 : between u₈=(1,-1) and u₁=(1,0), V = V₈ = (c₁, c₁-c₈)
      refine corner ((1 : ℤ), (-1 : ℤ)) ((1 : ℤ), (0 : ℤ))
        ((c₁ : ℤ), (c₁ - c₈ : ℤ)) ?_ ?_ ?_ ?_ ?_ ?_
      · rw [mem_oct8']; omega
      · intro z hz; rw [mem_oct8] at hz; simp only [dot, dot_mk]; omega
      · intro z hz; rw [mem_oct8] at hz; simp only [dot, dot_mk]; omega
      · simp only [det]; omega
      · simp only [det]; omega
      · simp only [det]; omega
  · -- n.2 = 0
    rcases lt_trichotomy n.1 0 with hx | hx | hx
    · rcases ray ((-1 : ℤ), (0 : ℤ)) (by decide) (by simp only [det]; omega) with hn | hn
      · exact r5 hn
      · exact absurd hn (by intro hh; rw [hh] at hx; simp at hx)
    · exact absurd hprim (by
        have : n = ((0 : ℤ), (0 : ℤ)) := Prod.ext_iff.mpr ⟨hx, hy⟩
        rw [this]; decide)
    · rcases ray ((1 : ℤ), (0 : ℤ)) (by decide) (by simp only [det]; omega) with hn | hn
      · exact r1 hn
      · exact absurd hn (by intro hh; rw [hh] at hx; simp at hx)
  · -- upper half
    rcases lt_trichotomy (n.1 - n.2) 0 with hq | hq | hq
    · rcases lt_trichotomy n.1 0 with hx | hx | hx
      · rcases lt_trichotomy (n.1 + n.2) 0 with hs | hs | hs
        · -- C4 : between u₄=(-1,1) and u₅=(-1,0), V = V₄ = (-c₅, c₄-c₅)
          refine corner ((-1 : ℤ), (1 : ℤ)) ((-1 : ℤ), (0 : ℤ))
            ((-c₅ : ℤ), (c₄ - c₅ : ℤ)) ?_ ?_ ?_ ?_ ?_ ?_
          · rw [mem_oct8']; omega
          · intro z hz; rw [mem_oct8] at hz; simp only [dot, dot_mk]; omega
          · intro z hz; rw [mem_oct8] at hz; simp only [dot, dot_mk]; omega
          · simp only [det]; omega
          · simp only [det]; omega
          · simp only [det]; omega
        · rcases ray ((-1 : ℤ), (1 : ℤ)) (by decide) (by simp only [det]; omega) with hn | hn
          · exact r4 hn
          · exact absurd hn (by
              intro hh; rw [hh] at hy; simp only [Prod.snd_neg] at hy; omega)
        · -- C3 : between u₃=(0,1) and u₄=(-1,1), V = V₃ = (c₃-c₄, c₃)
          refine corner ((0 : ℤ), (1 : ℤ)) ((-1 : ℤ), (1 : ℤ))
            ((c₃ - c₄ : ℤ), (c₃ : ℤ)) ?_ ?_ ?_ ?_ ?_ ?_
          · rw [mem_oct8']; omega
          · intro z hz; rw [mem_oct8] at hz; simp only [dot, dot_mk]; omega
          · intro z hz; rw [mem_oct8] at hz; simp only [dot, dot_mk]; omega
          · simp only [det]; omega
          · simp only [det]; omega
          · simp only [det]; omega
      · -- n.1 = 0, n.2 > 0 : ray u₃
        rcases ray ((0 : ℤ), (1 : ℤ)) (by decide) (by simp only [det]; omega) with hn | hn
        · exact r3 hn
        · exact absurd hn (by
            intro hh; rw [hh] at hy; simp only [Prod.snd_neg] at hy; omega)
      · -- C2 : between u₂=(1,1) and u₃=(0,1), V = V₂ = (c₂-c₃, c₃)
        refine corner ((1 : ℤ), (1 : ℤ)) ((0 : ℤ), (1 : ℤ))
          ((c₂ - c₃ : ℤ), (c₃ : ℤ)) ?_ ?_ ?_ ?_ ?_ ?_
        · rw [mem_oct8']; omega
        · intro z hz; rw [mem_oct8] at hz; simp only [dot, dot_mk]; omega
        · intro z hz; rw [mem_oct8] at hz; simp only [dot, dot_mk]; omega
        · simp only [det]; omega
        · simp only [det]; omega
        · simp only [det]; omega
    · -- n.1 = n.2 > 0 : ray u₂
      rcases ray ((1 : ℤ), (1 : ℤ)) (by decide) (by simp only [det]; omega) with hn | hn
      · exact r2 hn
      · exact absurd hn (by
          intro hh; rw [hh] at hy; simp only [Prod.snd_neg] at hy; omega)
    · -- C1 : between u₁=(1,0) and u₂=(1,1), V = V₁ = (c₁, c₂-c₁)
      refine corner ((1 : ℤ), (0 : ℤ)) ((1 : ℤ), (1 : ℤ))
        ((c₁ : ℤ), (c₂ - c₁ : ℤ)) ?_ ?_ ?_ ?_ ?_ ?_
      · rw [mem_oct8']; omega
      · intro z hz; rw [mem_oct8] at hz; simp only [dot, dot_mk]; omega
      · intro z hz; rw [mem_oct8] at hz; simp only [dot, dot_mk]; omega
      · simp only [det]; omega
      · simp only [det]; omega
      · simp only [det]; omega


/-! ## §3  `E`, lattice convexity, envelopedness -/

/-- **`oct8E ⊆ E (oct8 …)`**: each edge carries the vertex and one more lattice point. -/
theorem oct8E_subset_E {c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ : ℤ} (h : Nd8 c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈) :
    oct8E ⊆ E (oct8 c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈) := by
  obtain ⟨hA, hB, hC, hD, hE, hF, hG, hH⟩ := h
  intro n hn
  rw [mem_oct8E] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by decide, ⟨(c₁, c₁ - c₈), ⟨by rw [mem_oct8']; omega,
      fun y hy => by rw [mem_oct8] at hy; simp only [dot, dot_mk]; omega⟩,
      (c₁, c₁ - c₈ + 1), ⟨by rw [mem_oct8']; omega,
      fun y hy => by rw [mem_oct8] at hy; simp only [dot, dot_mk]; omega⟩,
      fun hh => by have h2 : c₁ - c₈ = c₁ - c₈ + 1 := congrArg Prod.snd hh; omega⟩⟩
  · exact ⟨by decide, ⟨(c₁, c₂ - c₁), ⟨by rw [mem_oct8']; omega,
      fun y hy => by rw [mem_oct8] at hy; simp only [dot, dot_mk]; omega⟩,
      (c₁ - 1, c₂ - c₁ + 1), ⟨by rw [mem_oct8']; omega,
      fun y hy => by rw [mem_oct8] at hy; simp only [dot, dot_mk]; omega⟩,
      fun hh => by have h1 : c₁ = c₁ - 1 := congrArg Prod.fst hh; omega⟩⟩
  · exact ⟨by decide, ⟨(c₂ - c₃, c₃), ⟨by rw [mem_oct8']; omega,
      fun y hy => by rw [mem_oct8] at hy; simp only [dot, dot_mk]; omega⟩,
      (c₂ - c₃ - 1, c₃), ⟨by rw [mem_oct8']; omega,
      fun y hy => by rw [mem_oct8] at hy; simp only [dot, dot_mk]; omega⟩,
      fun hh => by have h1 : c₂ - c₃ = c₂ - c₃ - 1 := congrArg Prod.fst hh; omega⟩⟩
  · exact ⟨by decide, ⟨(c₃ - c₄, c₃), ⟨by rw [mem_oct8']; omega,
      fun y hy => by rw [mem_oct8] at hy; simp only [dot, dot_mk]; omega⟩,
      (c₃ - c₄ - 1, c₃ - 1), ⟨by rw [mem_oct8']; omega,
      fun y hy => by rw [mem_oct8] at hy; simp only [dot, dot_mk]; omega⟩,
      fun hh => by have h1 : c₃ - c₄ = c₃ - c₄ - 1 := congrArg Prod.fst hh; omega⟩⟩
  · exact ⟨by decide, ⟨(-c₅, c₄ - c₅), ⟨by rw [mem_oct8']; omega,
      fun y hy => by rw [mem_oct8] at hy; simp only [dot, dot_mk]; omega⟩,
      (-c₅, c₄ - c₅ - 1), ⟨by rw [mem_oct8']; omega,
      fun y hy => by rw [mem_oct8] at hy; simp only [dot, dot_mk]; omega⟩,
      fun hh => by have h2 : c₄ - c₅ = c₄ - c₅ - 1 := congrArg Prod.snd hh; omega⟩⟩
  · exact ⟨by decide, ⟨(-c₅, c₅ - c₆), ⟨by rw [mem_oct8']; omega,
      fun y hy => by rw [mem_oct8] at hy; simp only [dot, dot_mk]; omega⟩,
      (-c₅ + 1, c₅ - c₆ - 1), ⟨by rw [mem_oct8']; omega,
      fun y hy => by rw [mem_oct8] at hy; simp only [dot, dot_mk]; omega⟩,
      fun hh => by have h1 : -c₅ = -c₅ + 1 := congrArg Prod.fst hh; omega⟩⟩
  · exact ⟨by decide, ⟨(c₇ - c₆, -c₇), ⟨by rw [mem_oct8']; omega,
      fun y hy => by rw [mem_oct8] at hy; simp only [dot, dot_mk]; omega⟩,
      (c₇ - c₆ + 1, -c₇), ⟨by rw [mem_oct8']; omega,
      fun y hy => by rw [mem_oct8] at hy; simp only [dot, dot_mk]; omega⟩,
      fun hh => by have h1 : c₇ - c₆ = c₇ - c₆ + 1 := congrArg Prod.fst hh; omega⟩⟩
  · exact ⟨by decide, ⟨(c₈ - c₇, -c₇), ⟨by rw [mem_oct8']; omega,
      fun y hy => by rw [mem_oct8] at hy; simp only [dot, dot_mk]; omega⟩,
      (c₈ - c₇ + 1, -c₇ + 1), ⟨by rw [mem_oct8']; omega,
      fun y hy => by rw [mem_oct8] at hy; simp only [dot, dot_mk]; omega⟩,
      fun hh => by have h1 : c₈ - c₇ = c₈ - c₇ + 1 := congrArg Prod.fst hh; omega⟩⟩

theorem E_oct8 {c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ : ℤ} (h : Nd8 c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈) :
    E (oct8 c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈) = oct8E :=
  Set.Subset.antisymm (E_oct8_subset h) (oct8E_subset_E h)

theorem two_le_face_oct8 {c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ : ℤ} (h : Nd8 c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈)
    {n : ℤ × ℤ} (hn : n ∈ oct8E) : 2 ≤ (face (oct8 c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈) n).encard := by
  obtain ⟨x, hx, y, hy, hxy⟩ := (oct8E_subset_E h hn).2
  exact two_le_encard_of_pair hx hy hxy

theorem isLatticeConvexRegion_oct8 (c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ : ℤ) :
    IsLatticeConvexRegion (oct8 c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈) := by
  have heq : oct8 c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ =
      (((((((Set.univ ∩ halfPlaneLE ((1 : ℤ), (0 : ℤ)) c₁) ∩
        halfPlaneLE ((1 : ℤ), (1 : ℤ)) c₂) ∩ halfPlaneLE ((0 : ℤ), (1 : ℤ)) c₃) ∩
        halfPlaneLE ((-1 : ℤ), (1 : ℤ)) c₄) ∩ halfPlaneLE ((-1 : ℤ), (0 : ℤ)) c₅) ∩
        halfPlaneLE ((-1 : ℤ), (-1 : ℤ)) c₆) ∩ halfPlaneLE ((0 : ℤ), (-1 : ℤ)) c₇) ∩
        halfPlaneLE ((1 : ℤ), (-1 : ℤ)) c₈ := by
    ext z
    simp only [mem_oct8, Set.mem_inter_iff, Set.mem_univ, halfPlaneLE, Set.mem_ofPred_eq,
      dot, true_and]
    omega
  rw [heq]
  iterate 8 refine isLatticeConvexRegion_inter_halfPlaneLE _ _ ?_
  exact Nivat.Colle41.isLatticeConvexRegion_univ

/-- **Envelopedness inside the family.**  If every face of the ambient one has at most two
lattice points, it envelops every other member. -/
theorem enveloped_oct8 {c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ : ℤ}
    (h : Nd8 c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈) (h' : Nd8 e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈)
    (hle2 : ∀ n ∈ oct8E, (face (oct8 c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈) n).encard ≤ 2) :
    Enveloped (oct8 c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈) (oct8 e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈) := by
  refine ⟨⟨isLatticeConvexRegion_oct8 _ _ _ _ _ _ _ _, fun n hn => ?_⟩, ?_⟩
  · rw [E_oct8 h'] at hn
    exact ⟨by rw [E_oct8 h]; exact hn, le_trans (hle2 n hn) (two_le_face_oct8 h' hn)⟩
  · rw [E_oct8 h, E_oct8 h']

/-- `oct8` is finite: it sits in a box. -/
theorem finite_oct8 (c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ : ℤ) :
    (oct8 c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈).Finite := by
  have hsub : oct8 c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ ⊆
      (Set.Icc (-c₅) c₁) ×ˢ (Set.Icc (-c₇) c₃) := by
    rintro z hz
    rw [mem_oct8] at hz
    exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩
  exact Set.Finite.subset ((Set.finite_Icc _ _).prod (Set.finite_Icc _ _)) hsub


/-! ## §4  The assignment

| slot | value |
|---|---|
| `𝒮_φ` | `oct8 0 1 2 4 3 3 1 0` — the minimal octagon, every face exactly two lattice points |
| `n_ℓ` | `(-1,1)`, `ℓ = (1,-1)`, `v⃗_ℓ = dir(-n_ℓ) = (1,1)`, `cz = 0` |
| `J` | `(1,0)`, `n_J = (-1,0)`, `c_J = 0` |
| `ν_{J+1}` | `(1,1)` — the ccw **successor** of `J`; `w = -(dir ν_{J+1}) = (1,-1)` |
| `μ` | `(0,1) ∈ Arc _ ν_{J+1} n_ℓ`, escaping wall `ν = -μ = (0,-1)` |
| `v_{J-1}` | `(1,1) = v⃗_ℓ` (here `J = ι+1`) |
| `ε` | `1` |
| `k_i` | `i + 2` |
| `Â_i` | `oct8 0 (2K-1) (2K) (8K-1) (6K) (8K-1) (2K) 0`, `K = i+2` |
| `A_i = B_i` | `oct8 K (4K-1) (3K) (8K-1) (5K) (6K-1) K 0` |

`d₆ = 8K-1` is **odd**: that is what makes the `u₇`-edge of `shellInter` appear, and hence the
guard true. -/

/-- `𝒮_φ`: twelve lattice points, eight edges, each edge exactly two points.

⚠ **一名多物（报告层风险，编译层为零）**：主仓另有一个**值完全不同**的具体常量
`Nivat.Colle37.Counterexample.Sphi`（`Claim37.lean:186`），它就是 `{(0,0), (0,1)}`；
另有两个同名结构字段 `Nivat.Colle35.DecompData.Sphi`（`DecompData.lean:106`）和
`Nivat.Colle37` 侧的一个字段（`Claim37.lean:509`）。

编译层撞不上（结构字段只能经 `d.Sphi` 访问；两个 `def` 在不同 namespace；本文件既不
`import Nivat.External.Colle.Claim37` 也无 blanket `open Nivat.Colle37.Counterexample`），
所以**本文件内一切裸写的 `Sphi` / `𝒮_φ` 一律指本声明**，不再逐处加全限定名。

危险全在**散文**里，而且比一般的重名更难露馅：本族关于 `GenClosure` 抬不动墙的承重话是
「`𝒮_φ` 的 `x`-max 由 `(0,0)`、`(0,1)` **两点**取到」——那两点**恰好就是** `Claim37` 那个
`Sphi` 的全部元素。于是「`𝒮_φ` 是 `{(0,0),(0,1)}`」与「`𝒮_φ` 的极面是 `{(0,0),(0,1)}`」
只差一个词、指的是两座台架上的两个对象，**算出来的数字还一样**。

⚠ **三方重合，不是两方**（team-lead 第 217 轮要求补记，本轮逐条实测）：

| 对象 | 值 | 实测出处 |
|---|---|---|
| `Nivat.Colle37.Counterexample.Sphi` | `{(0,0), (0,1)}`（全部） | `Claim37.lean:186` |
| `Nivat.LaneTowerOct8.Sphi`（本声明） | 12 元，**头两元**是 `(0,0), (0,1)` | 本文件下一行起 |
| `Nivat.LaneTowerOct8.faceBlockX` | `a = (0,0)`，`a' = (0,1)` | 本文件 `def faceBlockX` 的 `a` / `a'` 字段 |

⟹ 任何人去查「`Sphi` 是什么」，拿回 `{(0,0),(0,1)}` 这个答案对**三边都不矛盾**：
它是 `Claim37.Sphi` 的**全部**、是本声明的**前两元**、又是 `faceBlockX` 的**两个锚点**。
单读每一边都自洽，三边合起来才看得出是三个不同的对象。这就是这条重名比 `nJx`「差 90°」
更难抓的原因——`nJx` 错了一算就露，这个错了怎么算都对。

⟹ 跨文件转述本文件任何结论时必须写全限定名 `Nivat.LaneTowerOct8.Sphi`。 -/
def Sphi : Finset (ℤ × ℤ) :=
  {((0 : ℤ), (0 : ℤ)), ((0 : ℤ), (1 : ℤ)), ((-1 : ℤ), (-1 : ℤ)), ((-1 : ℤ), (0 : ℤ)),
    ((-1 : ℤ), (1 : ℤ)), ((-1 : ℤ), (2 : ℤ)), ((-2 : ℤ), (-1 : ℤ)), ((-2 : ℤ), (0 : ℤ)),
    ((-2 : ℤ), (1 : ℤ)), ((-2 : ℤ), (2 : ℤ)), ((-3 : ℤ), (0 : ℤ)), ((-3 : ℤ), (1 : ℤ))}

theorem coe_Sphi : (↑Sphi : Set (ℤ × ℤ)) = oct8 0 1 2 4 3 3 1 0 := by
  ext z
  simp only [Sphi, Finset.coe_insert, Set.mem_insert_iff, Finset.coe_singleton,
    Set.mem_singleton_iff, mem_oct8, Prod.ext_iff]
  omega

theorem nd8_Sphi : Nd8 0 1 2 4 3 3 1 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

def KK (i : ℕ) : ℤ := (i : ℤ) + 2

theorem two_le_KK (i : ℕ) : 2 ≤ KK i := by
  simp only [KK]; have := Int.natCast_nonneg i; omega

/-- `Â_i`. -/
def Ahat (i : ℕ) : Set (ℤ × ℤ) :=
  oct8 0 (2 * KK i - 1) (2 * KK i) (8 * KK i - 1) (6 * KK i) (8 * KK i - 1) (2 * KK i) 0

/-- `A_i = B_i = Â_i + k_i v⃗_ℓ`. -/
def Ax (i : ℕ) : Set (ℤ × ℤ) :=
  oct8 (KK i) (4 * KK i - 1) (3 * KK i) (8 * KK i - 1) (5 * KK i) (6 * KK i - 1) (KK i) 0

def Bx : ℕ → Set (ℤ × ℤ) := Ax
def kkx (i : ℕ) : ℕ := i + 2
def vlx : ℤ × ℤ := (1, 1)
def nlx : ℤ × ℤ := (-1, 1)
def ellx : ℤ × ℤ := (1, -1)
def Jx : ℤ × ℤ := (1, 0)
def nJx : ℤ × ℤ := (-1, 0)
def nuJ1x : ℤ × ℤ := (1, 1)
def wfan : ℤ × ℤ := (1, -1)
def vJ1x : ℤ × ℤ := (1, 1)
def mux : ℤ × ℤ := (0, 1)
def nux : ℤ × ℤ := (0, -1)

theorem nd8_Ahat (i : ℕ) :
    Nd8 0 (2 * KK i - 1) (2 * KK i) (8 * KK i - 1) (6 * KK i) (8 * KK i - 1) (2 * KK i) 0 := by
  have h := two_le_KK i
  exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

theorem nd8_Ax (i : ℕ) :
    Nd8 (KK i) (4 * KK i - 1) (3 * KK i) (8 * KK i - 1) (5 * KK i) (6 * KK i - 1)
      (KK i) 0 := by
  have h := two_le_KK i
  exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

theorem kkx_cast (i : ℕ) : ((kkx i : ℕ) : ℤ) = KK i := by
  simp only [kkx, KK]; push_cast; ring

theorem hatOf_eq (i : ℕ) : hatOf Ax kkx vlx i = Ahat i := by
  have hc := kkx_cast i
  ext z
  simp only [hatOf, Set.mem_ofPred_eq, Ax, Ahat, mem_oct8, vlx, Prod.fst_add, Prod.snd_add,
    Prod.smul_fst, Prod.smul_snd, smul_eq_mul, mul_one, hc]
  omega

/-! ## §5  Fan data, and the two explicit sets -/

/-- Every fan fact the producer `exists_w_hsweepW` supplies, on this assignment. -/
theorem fan_data :
    nJx = -Jx ∧ nlx = -ellx ∧ wfan = -(dir nuJ1x) ∧ vlx = dir (-nlx) ∧ vJ1x = vlx ∧
      0 < det ellx Jx ∧ 0 < det Jx nuJ1x ∧ dot nJx wfan < 0 ∧ dot nJx vJ1x < 0 ∧
      dot nlx vlx = 0 ∧ Prim nlx ∧ Prim nuJ1x ∧ vlx ≠ 0 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem E_Sphi : E (↑Sphi : Set (ℤ × ℤ)) = oct8E := by
  rw [coe_Sphi]; exact E_oct8 nd8_Sphi

/-- `ν_{J+1}` is the ccw **successor** of `J`: nothing of the fan lies strictly between. -/
theorem fan_successor : ∀ μ : ℤ × ℤ, 0 < det Jx μ → 0 < det μ nuJ1x →
    μ ∉ E (↑Sphi : Set (ℤ × ℤ)) := by
  intro μ h1 h2 hμ
  rw [E_Sphi, mem_oct8E] at hμ
  simp only [Jx, nuJ1x, det] at h1 h2
  rcases hμ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

/-- `Arc _ J n_ℓ` has **two** elements `ν_{J+1} = (1,1)` and `μ = (0,1)`, so the successor
selection is not the predecessor selection — the case `b3_colle2.txt:502` allows and the one
`shellSubStrip_of_pred` cannot reach. -/
theorem arc_J_nl_two :
    nuJ1x ∈ E (↑Sphi : Set (ℤ × ℤ)) ∧ mux ∈ E (↑Sphi : Set (ℤ × ℤ)) ∧ nuJ1x ≠ mux ∧
      0 < det Jx nuJ1x ∧ 0 < det nuJ1x nlx ∧ 0 < det Jx mux ∧ 0 < det mux nlx ∧
      nux = -mux ∧ dot nux vlx ≤ 0 ∧ 0 < dot nux wfan := by
  refine ⟨?_, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide⟩
  · rw [E_Sphi, mem_oct8E]; decide
  · rw [E_Sphi, mem_oct8E]; decide

theorem mem_iUnion_Ahat {z : ℤ × ℤ} :
    z ∈ (⋃ j, hatOf Ax kkx vlx j) ↔ z.1 ≤ 0 ∧ z.1 - z.2 ≤ 0 := by
  simp only [hatOf_eq, Set.mem_iUnion, Ahat, mem_oct8]
  constructor
  · rintro ⟨j, h1, -, -, -, -, -, -, h8⟩
    exact ⟨h1, h8⟩
  · rintro ⟨h1, h8⟩
    refine ⟨(|z.1| + |z.2|).toNat, ?_⟩
    have hc : (((|z.1| + |z.2|).toNat : ℕ) : ℤ) = |z.1| + |z.2| :=
      Int.toNat_of_nonneg (by positivity)
    have hK : KK ((|z.1| + |z.2|).toNat) = |z.1| + |z.2| + 2 := by
      simp only [KK, hc]
    rw [hK]
    have a1 := abs_nonneg z.1
    have a2 := abs_nonneg z.2
    have b1 := le_abs_self z.1
    have b2 := le_abs_self z.2
    have c1 := neg_abs_le z.1
    have c2 := neg_abs_le z.2
    exact ⟨h1, by omega, by omega, by omega, by omega, by omega, by omega, h8⟩

theorem shell_eq :
    MaxEnv.shell (⋃ j, hatOf Ax kkx vlx j) vJ1x nJx 0 1
      = {z : ℤ × ℤ | z.1 - z.2 ≤ 0 ∧ z.1 ≤ 1} := by
  ext z
  constructor
  · rintro ⟨g, hg, t, rfl, ht⟩
    rw [mem_iUnion_Ahat] at hg
    simp only [nJx, vJ1x, dot, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul, mul_one, Set.mem_ofPred_eq] at ht ⊢
    have ht0 : (0 : ℤ) ≤ (t : ℤ) := Int.natCast_nonneg t
    exact ⟨by omega, by omega⟩
  · rintro ⟨h1, h2⟩
    have hc : (((max z.1 0).toNat : ℕ) : ℤ) = max z.1 0 :=
      Int.toNat_of_nonneg (le_max_right _ _)
    have hm1 : z.1 ≤ max z.1 0 := le_max_left _ _
    have hm2 : (0 : ℤ) ≤ max z.1 0 := le_max_right _ _
    refine ⟨(z.1 - max z.1 0, z.2 - max z.1 0), ?_, (max z.1 0).toNat, ?_, ?_⟩
    · rw [mem_iUnion_Ahat]
      constructor <;> simp only <;> omega
    · simp only [vJ1x, Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
        smul_eq_mul, mul_one, hc]
      exact ⟨by omega, by omega⟩
    · simp only [nJx, dot, Set.mem_ofPred_eq]
      omega

/-- **`shellInter` is again a member of the family**, with the eighth constraint `-y ≤ 4K-1`
produced by lattice rounding: `-x-y ≤ 8K-1` (odd) together with `x ≤ y` forces `y ≥ -4K+1`, and
two lattice points realise it.  This is the step that makes the envelopedness guard true. -/
theorem shellInter_eq (i : ℕ) :
    ShellMink.shellInter (hatOf Ax kkx vlx i)
        (MaxEnv.shell (⋃ j, hatOf Ax kkx vlx j) vJ1x nJx 0 1) wfan
      = oct8 1 (2 * KK i - 1) (2 * KK i) (8 * KK i - 1) (6 * KK i) (8 * KK i - 1)
          (4 * KK i - 1) 0 := by
  have hK := two_le_KK i
  ext z
  rw [ShellMink.shellInter, Set.mem_inter_iff, shell_eq]
  constructor
  · rintro ⟨⟨g, hg, t, rfl⟩, hs⟩
    rw [hatOf_eq, Ahat, mem_oct8] at hg
    simp only [Set.mem_ofPred_eq, wfan, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul, mul_one, mul_neg] at hg hs ⊢
    have ht0 : (0 : ℤ) ≤ (t : ℤ) := Int.natCast_nonneg t
    rw [mem_oct8]
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, wfan,
      mul_one, mul_neg]
    refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
  · intro hz
    rw [mem_oct8] at hz
    have hT0 : (0 : ℤ) ≤ max (max z.1 (-2 * KK i - z.2)) 0 := le_max_right _ _
    have hc : ((((max (max z.1 (-2 * KK i - z.2)) 0).toNat : ℕ) : ℤ))
        = max (max z.1 (-2 * KK i - z.2)) 0 := Int.toNat_of_nonneg hT0
    have hTa : z.1 ≤ max (max z.1 (-2 * KK i - z.2)) 0 :=
      le_trans (le_max_left _ _) (le_max_left _ _)
    have hTb : -2 * KK i - z.2 ≤ max (max z.1 (-2 * KK i - z.2)) 0 :=
      le_trans (le_max_right _ _) (le_max_left _ _)
    have hTcases : max (max z.1 (-2 * KK i - z.2)) 0 = z.1 ∨
        max (max z.1 (-2 * KK i - z.2)) 0 = -2 * KK i - z.2 ∨
        max (max z.1 (-2 * KK i - z.2)) 0 = 0 := by
      rcases max_cases (max z.1 (-2 * KK i - z.2)) (0 : ℤ) with ⟨h, -⟩ | ⟨h, -⟩
      · rcases max_cases z.1 (-2 * KK i - z.2) with ⟨hh, -⟩ | ⟨hh, -⟩
        · exact Or.inl (by rw [h, hh])
        · exact Or.inr (Or.inl (by rw [h, hh]))
      · exact Or.inr (Or.inr h)
    refine ⟨⟨(z.1 - max (max z.1 (-2 * KK i - z.2)) 0,
        z.2 + max (max z.1 (-2 * KK i - z.2)) 0), ?_,
        (max (max z.1 (-2 * KK i - z.2)) 0).toNat, ?_⟩, ?_⟩
    · rw [hatOf_eq, Ahat, mem_oct8]
      refine ⟨by simp only; omega, by simp only; omega, by simp only; omega,
        by simp only; omega, by simp only; omega, by simp only; omega,
        by simp only; omega, by simp only; omega⟩
    · simp only [wfan, Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
        smul_eq_mul, mul_one, mul_neg, hc]
      exact ⟨by omega, by omega⟩
    · exact ⟨by omega, by omega⟩

theorem nd8_shellInter (i : ℕ) :
    Nd8 1 (2 * KK i - 1) (2 * KK i) (8 * KK i - 1) (6 * KK i) (8 * KK i - 1)
      (4 * KK i - 1) 0 := by
  have h := two_le_KK i
  exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩


/-! ## §6  Every binder holds, and the binder's body is false

The guard is discharged first (`PROTOCOL.md §41`): `enveloped_shellInter` is a **positive**
statement, proved for every `i` at `ε = 1`, so nothing below is vacuous. -/

/-- The eight faces of `𝒮_φ` have exactly two lattice points each. -/
theorem face_le2_Sphi : ∀ n ∈ oct8E, (face (oct8 0 1 2 4 3 3 1 0) n).encard ≤ 2 := by
  intro n hn
  rw [mem_oct8E] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine le_trans (Set.encard_mono (show face (oct8 0 1 2 4 3 3 1 0) ((1 : ℤ), (0 : ℤ)) ⊆
      {((0 : ℤ), (0 : ℤ)), ((0 : ℤ), (1 : ℤ))} from ?_)) (le_of_eq (Set.encard_pair (by decide)))
    rintro z ⟨hz, hmax⟩
    have h1 := hmax ((0 : ℤ), (0 : ℤ)) (by rw [mem_oct8']; omega)
    rw [mem_oct8] at hz
    simp only [dot, dot_mk] at h1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.ext_iff]
    omega
  · refine le_trans (Set.encard_mono (show face (oct8 0 1 2 4 3 3 1 0) ((1 : ℤ), (1 : ℤ)) ⊆
      {((0 : ℤ), (1 : ℤ)), ((-1 : ℤ), (2 : ℤ))} from ?_)) (le_of_eq (Set.encard_pair (by decide)))
    rintro z ⟨hz, hmax⟩
    have h1 := hmax ((0 : ℤ), (1 : ℤ)) (by rw [mem_oct8']; omega)
    rw [mem_oct8] at hz
    simp only [dot, dot_mk] at h1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.ext_iff]
    omega
  · refine le_trans (Set.encard_mono (show face (oct8 0 1 2 4 3 3 1 0) ((0 : ℤ), (1 : ℤ)) ⊆
      {((-1 : ℤ), (2 : ℤ)), ((-2 : ℤ), (2 : ℤ))} from ?_))
      (le_of_eq (Set.encard_pair (by decide)))
    rintro z ⟨hz, hmax⟩
    have h1 := hmax ((-1 : ℤ), (2 : ℤ)) (by rw [mem_oct8']; omega)
    rw [mem_oct8] at hz
    simp only [dot, dot_mk] at h1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.ext_iff]
    omega
  · refine le_trans (Set.encard_mono (show face (oct8 0 1 2 4 3 3 1 0) ((-1 : ℤ), (1 : ℤ)) ⊆
      {((-2 : ℤ), (2 : ℤ)), ((-3 : ℤ), (1 : ℤ))} from ?_))
      (le_of_eq (Set.encard_pair (by decide)))
    rintro z ⟨hz, hmax⟩
    have h1 := hmax ((-2 : ℤ), (2 : ℤ)) (by rw [mem_oct8']; omega)
    rw [mem_oct8] at hz
    simp only [dot, dot_mk] at h1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.ext_iff]
    omega
  · refine le_trans (Set.encard_mono (show face (oct8 0 1 2 4 3 3 1 0) ((-1 : ℤ), (0 : ℤ)) ⊆
      {((-3 : ℤ), (1 : ℤ)), ((-3 : ℤ), (0 : ℤ))} from ?_))
      (le_of_eq (Set.encard_pair (by decide)))
    rintro z ⟨hz, hmax⟩
    have h1 := hmax ((-3 : ℤ), (1 : ℤ)) (by rw [mem_oct8']; omega)
    rw [mem_oct8] at hz
    simp only [dot, dot_mk] at h1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.ext_iff]
    omega
  · refine le_trans (Set.encard_mono (show face (oct8 0 1 2 4 3 3 1 0) ((-1 : ℤ), (-1 : ℤ)) ⊆
      {((-3 : ℤ), (0 : ℤ)), ((-2 : ℤ), (-1 : ℤ))} from ?_))
      (le_of_eq (Set.encard_pair (by decide)))
    rintro z ⟨hz, hmax⟩
    have h1 := hmax ((-3 : ℤ), (0 : ℤ)) (by rw [mem_oct8']; omega)
    rw [mem_oct8] at hz
    simp only [dot, dot_mk] at h1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.ext_iff]
    omega
  · refine le_trans (Set.encard_mono (show face (oct8 0 1 2 4 3 3 1 0) ((0 : ℤ), (-1 : ℤ)) ⊆
      {((-2 : ℤ), (-1 : ℤ)), ((-1 : ℤ), (-1 : ℤ))} from ?_))
      (le_of_eq (Set.encard_pair (by decide)))
    rintro z ⟨hz, hmax⟩
    have h1 := hmax ((-2 : ℤ), (-1 : ℤ)) (by rw [mem_oct8']; omega)
    rw [mem_oct8] at hz
    simp only [dot, dot_mk] at h1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.ext_iff]
    omega
  · refine le_trans (Set.encard_mono (show face (oct8 0 1 2 4 3 3 1 0) ((1 : ℤ), (-1 : ℤ)) ⊆
      {((-1 : ℤ), (-1 : ℤ)), ((0 : ℤ), (0 : ℤ))} from ?_))
      (le_of_eq (Set.encard_pair (by decide)))
    rintro z ⟨hz, hmax⟩
    have h1 := hmax ((-1 : ℤ), (-1 : ℤ)) (by rw [mem_oct8']; omega)
    rw [mem_oct8] at hz
    simp only [dot, dot_mk] at h1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.ext_iff]
    omega

/-- `envB`: every `B_i` is `E(𝒮_φ)`-enveloped. -/
theorem enveloped_Bx (i : ℕ) : Enveloped (↑Sphi : Set (ℤ × ℤ)) (Bx i) := by
  rw [coe_Sphi, Bx, Ax]
  exact enveloped_oct8 nd8_Sphi (nd8_Ax i) face_le2_Sphi

/-- **The guard.**  `shellInter` at `ε = 1` is `E(𝒮_φ)`-enveloped at **every** index. -/
theorem enveloped_shellInter (i : ℕ) :
    EnvOf (↑Sphi : Set (ℤ × ℤ)) (ShellMink.shellInter (hatOf Ax kkx vlx i)
      (MaxEnv.shell (⋃ j, hatOf Ax kkx vlx j) vJ1x nJx 0 1) wfan) := by
  rw [EnvOf, shellInter_eq, coe_Sphi]
  exact enveloped_oct8 nd8_Sphi (nd8_shellInter i) face_le2_Sphi

theorem subBA (i : ℕ) : Bx i ⊆ Ax i := le_refl _

theorem subAB (i : ℕ) : Ax i ⊆ Bx (i + 1) := by
  intro z hz
  have h : KK i + 1 = KK (i + 1) := by simp only [KK]; push_cast; ring
  rw [Bx, Ax, mem_oct8] at *
  have := two_le_KK i
  omega

theorem subStrip (i : ℕ) : Ax i ⊆ Nivat.Colle35.halfStrip (Bx i) vlx :=
  Nivat.Colle35.subset_halfStrip _ _

theorem mono_hat (i j : ℕ) (hij : i ≤ j) : hatOf Ax kkx vlx i ⊆ hatOf Ax kkx vlx j := by
  intro z hz
  have h : KK i ≤ KK j := by
    have := (Nat.cast_le (α := ℤ)).mpr hij
    simp only [KK]; omega
  have hi := two_le_KK i
  rw [hatOf_eq, Ahat, mem_oct8] at hz ⊢
  omega

theorem finite_hat (i : ℕ) : (hatOf Ax kkx vlx i).Finite := by
  rw [hatOf_eq, Ahat]; exact finite_oct8 _ _ _ _ _ _ _ _

theorem hhp_x (i : ℕ) : hatOf Ax kkx vlx i ⊆ halfPlaneGE nJx 0 := by
  intro z hz
  rw [hatOf_eq, Ahat, mem_oct8] at hz
  simp only [halfPlaneGE, Set.mem_ofPred_eq, nJx, dot]
  omega

theorem swept_x : SweptClosed (⋃ j, hatOf Ax kkx vlx j) vJ1x nJx 0 := by
  intro g hg t ht
  rw [mem_iUnion_Ahat] at hg ⊢
  simp only [vJ1x, nJx, dot, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul, mul_one, Set.mem_ofPred_eq] at ht ⊢
  exact ⟨by omega, by omega⟩

theorem nonempty_x : (⋃ j, hatOf Ax kkx vlx j).Nonempty := by
  refine ⟨((0 : ℤ), (0 : ℤ)), ?_⟩
  rw [mem_iUnion_Ahat]
  exact ⟨by norm_num, by norm_num⟩

theorem exhausts_x : Nivat.Colle35.Exhausts Ax nlx 0 := by
  ext z
  simp only [Set.mem_iUnion, Ax, mem_oct8, Set.mem_ofPred_eq, nlx, dot]
  constructor
  · rintro ⟨j, -, -, -, -, -, -, -, h8⟩
    omega
  · intro hz
    refine ⟨(|z.1| + |z.2|).toNat, ?_⟩
    have hc : (((|z.1| + |z.2|).toNat : ℕ) : ℤ) = |z.1| + |z.2| :=
      Int.toNat_of_nonneg (by positivity)
    have hK : KK ((|z.1| + |z.2|).toNat) = |z.1| + |z.2| + 2 := by simp only [KK, hc]
    rw [hK]
    have b1 := le_abs_self z.1
    have b2 := le_abs_self z.2
    have c1 := neg_abs_le z.1
    have c2 := neg_abs_le z.2
    exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

/-! ### The escape

`g := (-6K+1, -2K)` is the vertex `V₆` of `Â_i`, i.e. an endpoint of `face (Â_i) ν` for the
escaping wall `ν = (0,-1)`.  One `w`-step lands in the shell and out of the strip. -/

/-- The escaping point is in `shellInter`. -/
theorem escape_mem_shellInter (i : ℕ) :
    ((-6 * KK i + 2 : ℤ), (-2 * KK i - 1 : ℤ)) ∈
      ShellMink.shellInter (hatOf Ax kkx vlx i)
        (MaxEnv.shell (⋃ j, hatOf Ax kkx vlx j) vJ1x nJx 0 1) wfan := by
  have h := two_le_KK i
  rw [shellInter_eq, mem_oct8']
  exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

/-- …and it is out of the half-strip after the `k_i v⃗_ℓ` shift: its `ν`-value is
`K + 1 > K = suppVal (B i) ν`, while sweeping along `v⃗_ℓ` can only lower `ν`. -/
theorem escape_not_mem_halfStrip (i : ℕ) :
    ((-6 * KK i + 2 : ℤ), (-2 * KK i - 1 : ℤ)) + (kkx i : ℤ) • vlx ∉
      Nivat.Colle35.halfStrip (Bx i) vlx := by
  have h := two_le_KK i
  have hc := kkx_cast i
  rintro ⟨b, hb, t, hbt⟩
  rw [Bx, Ax, mem_oct8] at hb
  have ht0 : (0 : ℤ) ≤ (t : ℤ) := Int.natCast_nonneg t
  have h2 : (-2 * KK i - 1 : ℤ) + KK i = b.2 + (t : ℤ) := by
    have := congrArg Prod.snd hbt
    simpa only [vlx, Prod.snd_add, Prod.smul_snd, smul_eq_mul, mul_one, hc] using this
  omega

/-- **The binder's body is false at every index.** -/
theorem not_shellSubStrip_body :
    ¬ (∀ i : ℕ, max 0 0 ≤ i →
        ShellMink.shellInter (hatOf Ax kkx vlx i)
            (MaxEnv.shell (⋃ j, hatOf Ax kkx vlx j) vJ1x nJx 0 1) wfan ⊆
          {z | z + (kkx i : ℤ) • vlx ∈ Nivat.Colle35.halfStrip (Bx i) vlx}) := by
  intro h
  exact escape_not_mem_halfStrip 0 (h 0 (by norm_num) (escape_mem_shellInter 0))

/-! ### The delivery -/

/-- **Every on-site binder holds, and `shellSubStrip` is false.**

The first component is the binder table of `ChainDataGeom.ofPartsExhaustsInter`
(`ChainExhaustInter.lean`, by declaration name) restricted to what `shellSubStrip` sees, together with the fan
facts `LeafAShellNNext.exists_w_hsweepW` supplies and the two `Arc` facts showing this is the
**successor** selection with `|Arc _ J n_ℓ| = 2`.  The last conjunct of the first component is
the envelopedness guard at `ε = 1`, `i₀ = 0`, proved **positively** — so the refutation in the
second component is not vacuous (`PROTOCOL.md §41`).

`I₀` is a parameter of the definition, so a counterexample may choose it; here `I₀ = 0`, and the
body fails at **every** `i`, so no value of `I₀` rescues it (`escape_mem_shellInter` and
`escape_not_mem_halfStrip` are stated for all `i`). -/
theorem binders_hold_but_not_shellSubStrip :
    ((nJx = -Jx ∧ nlx = -ellx ∧ wfan = -(dir nuJ1x) ∧ vlx = dir (-nlx) ∧
      0 < det ellx Jx ∧ 0 < det Jx nuJ1x ∧ dot nJx wfan < 0 ∧ dot nJx vJ1x < 0 ∧
      dot nlx vlx = 0 ∧ Prim nlx ∧ vlx ≠ 0) ∧
     (∀ μ : ℤ × ℤ, 0 < det Jx μ → 0 < det μ nuJ1x → μ ∉ E (↑Sphi : Set (ℤ × ℤ))) ∧
     (nuJ1x ∈ E (↑Sphi : Set (ℤ × ℤ)) ∧ mux ∈ E (↑Sphi : Set (ℤ × ℤ)) ∧ nuJ1x ≠ mux ∧
       0 < det Jx nuJ1x ∧ 0 < det nuJ1x nlx ∧ 0 < det Jx mux ∧ 0 < det mux nlx ∧
       nux = -mux ∧ dot nux vlx ≤ 0 ∧ 0 < dot nux wfan) ∧
     (∀ i, Enveloped (↑Sphi : Set (ℤ × ℤ)) (Bx i)) ∧
     (∀ i, Bx i ⊆ Ax i) ∧ (∀ i, Ax i ⊆ Bx (i + 1)) ∧
     (∀ i, Ax i ⊆ Nivat.Colle35.halfStrip (Bx i) vlx) ∧
     (∀ i j, i ≤ j → hatOf Ax kkx vlx i ⊆ hatOf Ax kkx vlx j) ∧
     (∀ i, (hatOf Ax kkx vlx i).Finite) ∧
     (∀ i, hatOf Ax kkx vlx i ⊆ halfPlaneGE nJx 0) ∧
     SweptClosed (⋃ j, hatOf Ax kkx vlx j) vJ1x nJx 0 ∧
     (⋃ j, hatOf Ax kkx vlx j).Nonempty ∧
     Nivat.Colle35.Exhausts Ax nlx 0 ∧
     (0 : ℕ) < 1 ∧
     (∀ i, 0 ≤ i → EnvOf (↑Sphi : Set (ℤ × ℤ)) (ShellMink.shellInter (hatOf Ax kkx vlx i)
        (MaxEnv.shell (⋃ j, hatOf Ax kkx vlx j) vJ1x nJx 0 1) wfan))) ∧
    ¬ (∀ i : ℕ, max 0 0 ≤ i →
        ShellMink.shellInter (hatOf Ax kkx vlx i)
            (MaxEnv.shell (⋃ j, hatOf Ax kkx vlx j) vJ1x nJx 0 1) wfan ⊆
          {z | z + (kkx i : ℤ) • vlx ∈ Nivat.Colle35.halfStrip (Bx i) vlx}) := by
  obtain ⟨f1, f2, f3, f4, -, f6, f7, f8, f9, f10, f11, -, f13⟩ := fan_data
  refine ⟨⟨⟨f1, f2, f3, f4, f6, f7, f8, f9, f10, f11, f13⟩, fan_successor, arc_J_nl_two,
    enveloped_Bx, subBA, subAB, subStrip, mono_hat, finite_hat, hhp_x, swept_x, nonempty_x,
    exhausts_x, by norm_num, fun i _ => enveloped_shellInter i⟩, not_shellSubStrip_body⟩


/-! ## §7  The recession binders, for completeness

`rec_p` / `dot_nJ_p` / `hdet` are not consumed by `shellSubStrip`, but they are cheap here and
they pin down that the assignment is a genuine chain datum rather than a degenerate one. -/

def px : ℤ × ℤ := (-1, -1)

theorem rec_p_x :
    (∀ g ∈ (⋃ j, hatOf Ax kkx vlx j), g + px ∈ (⋃ j, hatOf Ax kkx vlx j)) ∧
      dot nJx px ≠ 0 ∧ det px vlx = 0 := by
  refine ⟨?_, by decide, by decide⟩
  intro g hg
  rw [mem_iUnion_Ahat] at hg ⊢
  simp only [px, Prod.fst_add, Prod.snd_add]
  exact ⟨by omega, by omega⟩


/-! ## §8  The `(ℓ, ℓ_J)`-region orientation audit (round 167)

`team-lead`'s round-167 assignment: `b3_colle2.txt:506` ("Actually, `Â_∞` is an `(ℓ, ℓ_J)`-region")
is a binder the paper supplies, and the chain uses the *weakened* `Colle41.IsRegion`
(`Colle41.IsRegion`, `Lemma41.lean:688`) which drops the orientation datum `w ≺ ⋯ ≺ w'` of the
paper's own definition (`b3_colle2.txt:386`).  The full `LE2.IsRegion`
(`LatticeEdges.lean:2295`) keeps it as the fields `detPos` (`LatticeEdges.lean:2312`) and
`precedes` (`LatticeEdges.lean:2314`).  A counterexample must satisfy the full version, so it is
audited here.

On this assignment `Â_∞ = ⋃ j, Â_j` is the wedge `{z | z.1 ≤ 0 ∧ z.1 - z.2 ≤ 0}`
(`mem_iUnion_Ahat`), a lattice cone with apex `(0,0)` and exactly two edges:

| | ℓ-edge | ℓ_J-edge |
|---|---|---|
| outer normal | `ν_ι = -n_ℓ = (1,-1)` | `ν_J = -n_J = (1,0)` |
| face | `{z.1 = z.2 ≤ 0}` | `{z.1 = 0 ≤ z.2}` |
| ray direction | `(-1,-1) = -v⃗_ℓ` | `(0,1) = dir ν_J` |

`n_ℓ` is the **inner** normal here, because the binder `hexh : Exhausts A nℓ cz` reads
`⋃ i, A i = {z | cz ≤ ⟪n_ℓ, z⟫}`; likewise `n_J` is inner by
`hhp : Â_i ⊆ halfPlaneGE n_J c_J`.  With that, `team-lead`'s two ray rules are met:
the ℓ-ray is `-dir(ν_ι) = -dir(-n_ℓ) = -v⃗_ℓ` and the ℓ_J-ray is `+dir(ν_J) = dir(-n_J)`.
`v⃗_ℓ` itself is the **negative** of the ℓ-ray, which is forced: `Â_i = A_i - k_i v⃗_ℓ` with
`k_i` increasing, so the layers march along `-v⃗_ℓ`, i.e. along the ℓ-ray. -/

/-- `Â_∞` as an explicit wedge. -/
def Ainf : Set (ℤ × ℤ) := {z | z.1 ≤ 0 ∧ z.1 - z.2 ≤ 0}

theorem iUnion_Ahat_eq : (⋃ j, hatOf Ax kkx vlx j) = Ainf := by
  ext z; exact mem_iUnion_Ahat

/-- The two generators of the recession cone of `Â_∞` are `(-1,-1)` (the ℓ-ray) and `(0,1)`
(the ℓ_J-ray); a normal positive on either of them exposes no face at all. -/
theorem face_Ainf_empty {n : ℤ × ℤ} (h : 0 < n.2 ∨ 0 < -n.1 - n.2) : face Ainf n = ∅ := by
  ext z
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨⟨h1, h2⟩, hm⟩
  rcases h with h | h
  · have hc := hm (z.1, z.2 + 1) ⟨h1, by simp only; omega⟩
    simp only [dot] at hc
    nlinarith
  · have hc := hm (z.1 - 1, z.2 - 1) ⟨by simp only; omega, by simp only; omega⟩
    simp only [dot] at hc
    nlinarith

/-- The ℓ_J-edge: outer normal `ν_J = (1,0)`, the vertical ray out of the apex. -/
theorem face_Ainf_J : face Ainf ((1 : ℤ), (0 : ℤ)) = {z | z.1 = 0 ∧ 0 ≤ z.2} := by
  ext z
  constructor
  · rintro ⟨⟨h1, h2⟩, hm⟩
    have h := hm ((0 : ℤ), (0 : ℤ)) ⟨by norm_num, by norm_num⟩
    simp only [dot] at h
    exact ⟨by omega, by omega⟩
  · rintro ⟨h1, h2⟩
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    rintro y ⟨b1, b2⟩
    simp only [dot]
    omega

/-- The ℓ-edge: outer normal `ν_ι = -n_ℓ = (1,-1)`, the diagonal ray out of the apex, whose
direction `(-1,-1)` is `-v⃗_ℓ`. -/
theorem face_Ainf_ell : face Ainf ((1 : ℤ), (-1 : ℤ)) = {z | z.1 = z.2 ∧ z.1 ≤ 0} := by
  ext z
  constructor
  · rintro ⟨⟨h1, h2⟩, hm⟩
    have h := hm ((0 : ℤ), (0 : ℤ)) ⟨by norm_num, by norm_num⟩
    simp only [dot] at h
    exact ⟨by omega, by omega⟩
  · rintro ⟨h1, h2⟩
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    rintro y ⟨b1, b2⟩
    simp only [dot]
    omega

/-- Strictly inside the dual cone the face is the apex alone. -/
theorem face_Ainf_singleton {n : ℤ × ℤ} (h1 : n.2 < 0) (h2 : 0 < n.1 + n.2) :
    face Ainf n = {((0 : ℤ), (0 : ℤ))} := by
  ext z
  constructor
  · rintro ⟨⟨a1, a2⟩, hm⟩
    have h := hm ((0 : ℤ), (0 : ℤ)) ⟨by norm_num, by norm_num⟩
    simp only [dot] at h
    have ha : (0 : ℤ) ≤ -z.1 := by omega
    have hb : (0 : ℤ) ≤ z.2 - z.1 := by omega
    have hA : (0 : ℤ) ≤ (-z.1) * (n.1 + n.2) := mul_nonneg ha (by omega)
    have hB : (z.2 - z.1) * n.2 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hb (by omega)
    have hsum : n.1 * z.1 + n.2 * z.2
        = -((-z.1) * (n.1 + n.2)) + (z.2 - z.1) * n.2 := by ring
    have hA0 : (-z.1) * (n.1 + n.2) = 0 := by linarith
    have hB0 : (z.2 - z.1) * n.2 = 0 := by linarith
    have e1 : -z.1 = 0 := by
      rcases mul_eq_zero.mp hA0 with h' | h'
      · exact h'
      · omega
    have e2 : z.2 - z.1 = 0 := by
      rcases mul_eq_zero.mp hB0 with h' | h'
      · exact h'
      · omega
    exact Prod.ext (by omega) (by omega)
  · rintro rfl
    refine ⟨⟨by norm_num, by norm_num⟩, ?_⟩
    rintro y ⟨b1, b2⟩
    simp only [dot]
    nlinarith [mul_nonneg (by omega : (0:ℤ) ≤ -y.1) (by omega : (0:ℤ) ≤ n.1 + n.2),
      mul_nonpos_of_nonneg_of_nonpos (by omega : (0:ℤ) ≤ y.2 - y.1) (by omega : n.2 ≤ 0)]

/-- **(a).**  `Â_∞` has exactly two edges, and they are the two outer normals named above. -/
theorem E_Ainf : E Ainf = {((1 : ℤ), (-1 : ℤ)), ((1 : ℤ), (0 : ℤ))} := by
  ext n
  constructor
  · rintro ⟨hprim, hnt⟩
    by_cases hpos : 0 < n.2 ∨ 0 < -n.1 - n.2
    · rw [face_Ainf_empty hpos] at hnt; exact absurd hnt (by simp)
    · push_neg at hpos
      obtain ⟨hp1, hp2⟩ := hpos
      by_cases h2 : n.2 = 0
      · rcases prim_eq_of_snd_eq_zero hprim h2 with rfl | rfl
        · simp
        · exact absurd hp2 (by norm_num)
      · by_cases h12 : n.1 + n.2 = 0
        · rcases Nivat.ShellSweep.prim_eq_of_coord_eq_neg hprim (by omega) with rfl | rfl
          · simp
          · exact absurd hp1 (by norm_num)
        · exfalso
          rw [face_Ainf_singleton (by omega) (by omega)] at hnt
          exact Set.not_nontrivial_singleton hnt
  · rintro (rfl | rfl)
    · refine ⟨by decide, ?_⟩
      rw [face_Ainf_ell]
      exact ⟨(0, 0), ⟨rfl, le_refl _⟩, (-1, -1), ⟨rfl, by norm_num⟩, by decide⟩
    · refine ⟨by decide, ?_⟩
      rw [face_Ainf_J]
      exact ⟨(0, 0), ⟨rfl, le_refl _⟩, (0, 1), ⟨rfl, by norm_num⟩, by decide⟩

theorem infinite_face_Ainf_ell : (face Ainf ((1 : ℤ), (-1 : ℤ))).Infinite := by
  rw [face_Ainf_ell]
  refine Set.infinite_of_injective_forall_mem (f := fun k : ℕ => ((-(k : ℤ)), (-(k : ℤ))))
    (fun a b h => ?_) (fun k => ⟨rfl, by omega⟩)
  simp only [Prod.mk.injEq, neg_inj, Nat.cast_inj] at h
  exact h.1

theorem infinite_face_Ainf_J : (face Ainf ((1 : ℤ), (0 : ℤ))).Infinite := by
  rw [face_Ainf_J]
  refine Set.infinite_of_injective_forall_mem (f := fun k : ℕ => (((0 : ℤ)), ((k : ℤ))))
    (fun a b h => ?_) (fun k => ⟨rfl, by omega⟩)
  simp only [Prod.mk.injEq, Nat.cast_inj] at h
  exact h.2

theorem infinite_Ainf : Ainf.Infinite := infinite_face_Ainf_ell.mono (face_subset _ _)

theorem isLatticeConvexRegion_Ainf : IsLatticeConvexRegion Ainf := by
  refine ⟨{x : ℝ × ℝ | x.1 ≤ 0 ∧ x.1 - x.2 ≤ 0}, ?_, ?_, ?_⟩
  · rintro x ⟨hx1, hx2⟩ y ⟨hy1, hy2⟩ a b ha hb hab
    constructor
    · show a * x.1 + b * y.1 ≤ (0 : ℝ)
      nlinarith
    · show a * x.1 + b * y.1 - (a * x.2 + b * y.2) ≤ (0 : ℝ)
      nlinarith
  · exact (isClosed_le continuous_fst continuous_const).inter
      (isClosed_le (continuous_fst.sub continuous_snd) continuous_const)
  · ext z
    simp only [Set.mem_preimage, toReal]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · show ((z.1 : ℝ)) ≤ 0
        exact_mod_cast h1
      · show ((z.1 : ℝ)) - ((z.2 : ℝ)) ≤ 0
        have : ((z.1 : ℝ)) - ((z.2 : ℝ)) = (((z.1 - z.2 : ℤ)) : ℝ) := by push_cast; ring
        rw [this]; exact_mod_cast h2
    · rintro ⟨h1, h2⟩
      have g1 : ((z.1 : ℝ)) ≤ 0 := h1
      have g2 : ((z.1 : ℝ)) - ((z.2 : ℝ)) ≤ 0 := h2
      refine ⟨by exact_mod_cast g1, ?_⟩
      have : ((z.1 : ℝ)) - ((z.2 : ℝ)) = (((z.1 - z.2 : ℤ)) : ℝ) := by push_cast; ring
      rw [this] at g2
      exact_mod_cast g2

/-- **(a) + (b) + (c) together.**  `Â_∞` is a genuine `(ν_ι, ν_J)`-region in the **full**
`LE2.IsRegion` sense, orientation datum included: `detPos = det (1,-1) (1,0) = 1 > 0`, and
`precedes` is immediate because there is no third edge to be out of order. -/
theorem isRegion_Ainf : IsRegion Ainf ((1 : ℤ), (-1 : ℤ)) ((1 : ℤ), (0 : ℤ)) where
  latticeConvex := isLatticeConvexRegion_Ainf
  infinite := infinite_Ainf
  posArea := posArea_of_edges (n := ((1 : ℤ), (-1 : ℤ))) (m := ((1 : ℤ), (0 : ℤ)))
    (by rw [E_Ainf]; simp) (by rw [E_Ainf]; simp) (by decide) (by decide)
  edgesFinite := by rw [E_Ainf]; exact Set.toFinite _
  semiInf := ⟨by rw [E_Ainf]; simp, infinite_face_Ainf_ell⟩
  semiInf' := ⟨by rw [E_Ainf]; simp, infinite_face_Ainf_J⟩
  semiInfUnique := fun m hm => by
    have h := hm.1
    rw [E_Ainf] at h
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr h
  detPos := by decide
  precedes := by
    refine ⟨by rw [E_Ainf]; simp, by rw [E_Ainf]; simp, by decide, ?_⟩
    intro m hm hne hne'
    rw [E_Ainf] at hm
    rcases hm with h | h
    · exact absurd h hne
    · exact absurd h hne'

/-- **(b), the ray rules, in the kernel.**  ℓ-ray `= -dir ν_ι` and it is `-v⃗_ℓ`;
ℓ_J-ray `= +dir ν_J` and it is `dir (-n_J)`.  Both rays are checked to lie in `Â_∞` and to
span the corresponding face. -/
theorem ray_rules :
    (-(dir ellx) = -vlx ∧ -vlx = ((-1 : ℤ), (-1 : ℤ)) ∧
      ∀ k : ℕ, ((0 : ℤ), (0 : ℤ)) + (k : ℤ) • (-vlx) ∈ face Ainf ellx) ∧
    (dir Jx = ((0 : ℤ), (1 : ℤ)) ∧ Jx = -nJx ∧
      ∀ k : ℕ, ((0 : ℤ), (0 : ℤ)) + (k : ℤ) • (dir Jx) ∈ face Ainf Jx) := by
  refine ⟨⟨by decide, by decide, ?_⟩, ⟨by decide, by decide, ?_⟩⟩
  · intro k
    have : ((0 : ℤ), (0 : ℤ)) + (k : ℤ) • (-vlx) = ((-(k : ℤ)), (-(k : ℤ))) := by
      simp only [vlx, Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
        Prod.fst_neg, Prod.snd_neg, smul_eq_mul]
      constructor <;> ring
    rw [show ellx = ((1 : ℤ), (-1 : ℤ)) from rfl, this, face_Ainf_ell]
    exact ⟨rfl, by omega⟩
  · intro k
    have : ((0 : ℤ), (0 : ℤ)) + (k : ℤ) • (dir Jx) = ((0 : ℤ), ((k : ℤ))) := by
      simp only [Jx, dir, Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
        Prod.smul_snd, smul_eq_mul]
      constructor <;> ring
    rw [this, show Jx = ((1 : ℤ), (0 : ℤ)) from rfl, face_Ainf_J]
    exact ⟨rfl, by omega⟩

/-- **The successor check on `hsweepW`.**  `team-lead`'s `hsweepW_iff_successor`
(`tmp/region_orientation_probe.lean`) says `dot n_J w < 0 ↔ 0 < det ν_J ν_{J+1}` once
`n_J = -ν_J` and `w = -(dir ν_{J+1})`.  Here `ν_J = J = (1,0)` and `ν_{J+1} = (1,1)`, and
`det ν_J ν_{J+1} = 1 > 0`: `ν_{J+1}` is the ccw **successor**, not the predecessor. -/
theorem hsweepW_is_successor :
    nJx = -Jx ∧ wfan = -(dir nuJ1x) ∧ 0 < det Jx nuJ1x ∧ dot nJx wfan < 0 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- **The audit, as one statement.**  (a) the two outer normals and `detPos`;
(b) the ray rules; (c) `precedes`; plus the `hsweepW` successor check. -/
theorem region_orientation_audit :
    (⋃ j, hatOf Ax kkx vlx j) = Ainf ∧
    E Ainf = {((1 : ℤ), (-1 : ℤ)), ((1 : ℤ), (0 : ℤ))} ∧
    ((1 : ℤ), (-1 : ℤ)) = -nlx ∧ ((1 : ℤ), (0 : ℤ)) = -nJx ∧
    0 < det (-nlx) (-nJx) ∧
    IsRegion Ainf (-nlx) (-nJx) ∧
    PrecedesAll Ainf (-nlx) (-nJx) ∧
    0 < det Jx nuJ1x ∧ dot nJx wfan < 0 := by
  have h1 : (-nlx : ℤ × ℤ) = ((1 : ℤ), (-1 : ℤ)) := by decide
  have h2 : (-nJx : ℤ × ℤ) = ((1 : ℤ), (0 : ℤ)) := by decide
  refine ⟨iUnion_Ahat_eq, E_Ainf, by decide, by decide, by decide, ?_, ?_, by decide, by decide⟩
  · rw [h1, h2]; exact isRegion_Ainf
  · rw [h1, h2]; exact isRegion_Ainf.precedes


/-! ## §9  The chain-side region binder, via `RegionOrientBridge` (round 167)

`team-lead` landed `Nivat.RegionOrientBridge.colle41_of_le2` (`RegionOrientBridge.lean:73`):

    LE2.IsRegion R n n' → Colle41.IsRegion R (-(dir n)) (dir n')

which turns §8's full-strength `isRegion_Ainf` into the **weakened shape the chain actually
consumes** (`Colle41.IsRegion`, `Lemma41.lean:688`).  The two directions it produces are
`-(dir ν_ι) = (-1,-1)` and `dir ν_J = (0,1)` — literally the two ray directions §8's
`ray_rules` computed by hand, which is an independent cross-check of both.

Also recorded here: the two sweep binders restated through `team-lead`'s new
`dot_neg_dir_neg_lt_iff` (`LatticeEdges.lean:320`) instead of `decide`, so that the *fan-order*
reading is the one in the kernel rather than a coincidence of three small integers. -/

/-- **The region binder in the chain's own shape.**  `Â_∞` is a `Colle41`-region with the two
ray directions `(-1,-1)` and `(0,1)`; the first is `-v⃗_ℓ`. -/
theorem colle41_region_Ainf :
    Nivat.Colle41.IsRegion Ainf ((-1 : ℤ), (-1 : ℤ)) ((0 : ℤ), (1 : ℤ)) := by
  have h := Nivat.RegionOrientBridge.colle41_of_le2 isRegion_Ainf
  have e1 : -(dir ((1 : ℤ), (-1 : ℤ))) = ((-1 : ℤ), (-1 : ℤ)) := by decide
  have e2 : dir ((1 : ℤ), (0 : ℤ)) = ((0 : ℤ), (1 : ℤ)) := by decide
  rwa [e1, e2] at h

/-- The first ray direction the bridge produces is exactly `-v⃗_ℓ`, i.e. the direction the
tower marches in (`Â_i = A_i - k_i v⃗_ℓ`, `k_i` increasing). -/
theorem colle41_ray_eq_neg_vl : ((-1 : ℤ), (-1 : ℤ)) = -vlx := by decide

/-- **`hsweepW` is the successor relation, through the general lemma.**  No numerals are
compared here: the equivalence is `dot_neg_dir_neg_lt_iff` applied to `n_J = -ν_J` and
`w = -(dir ν_{J+1})`, and only then is `det ν_J ν_{J+1} = 1 > 0` evaluated. -/
theorem hsweepW_iff_det_via_bridge : dot nJx wfan < 0 ↔ 0 < det Jx nuJ1x := by
  have h1 : nJx = -Jx := by decide
  have h2 : wfan = -(dir nuJ1x) := by decide
  rw [h1, h2, dot_neg_dir_neg_lt_iff]

theorem hsweepW_successor : 0 < det Jx nuJ1x := by decide

/-- **`hsweep` holds under *both* readings of `v⃗_{ℓ_{J-1}}`, so it does not depend on which
convention is meant.**  `team-lead`'s round-167 note states
`hsweep ⟺ 0 < det ν_{J−1} ν_J`, while `dot_neg_dir_neg_lt_iff` applied with
`v_{J1} = -(dir μ)` gives `0 < det ν_J μ` — the two differ in the argument order, i.e. in
whether `v⃗_{ℓ_{J-1}} = -(dir ν_{J-1})` or `= +dir ν_{J-1}`.  On this instance
`v⃗_{ℓ_{J-1}} = (1,1)`, so:

* reading `-(dir ·)` forces `μ = (-1,1)` and gives `det ν_J μ = det (1,0) (-1,1) = 1 > 0`;
* reading `+dir ·` forces `μ' = (1,-1) = ν_ι` and gives `det μ' ν_J = det (1,-1) (1,0) = 1 > 0`.

Both are positive, and `dot n_J v_{J1} = -1 < 0` either way, so `hsweep` passes regardless.
The convention question is real but it is not load-bearing for this counterexample. -/
theorem hsweep_both_readings :
    (vJ1x = -(dir ((-1 : ℤ), (1 : ℤ))) ∧ 0 < det Jx ((-1 : ℤ), (1 : ℤ))) ∧
    (vJ1x = dir ((1 : ℤ), (-1 : ℤ)) ∧ 0 < det ((1 : ℤ), (-1 : ℤ)) Jx) ∧
    ((1 : ℤ), (-1 : ℤ)) = -nlx ∧
    dot nJx vJ1x < 0 := by
  refine ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩, by decide, by decide⟩

/-- **The round-167 audit, restated with the chain-side region binder included.** -/
theorem region_audit_colle41 :
    (⋃ j, hatOf Ax kkx vlx j) = Ainf ∧
    Nivat.LE2.IsRegion Ainf (-nlx) (-nJx) ∧
    Nivat.Colle41.IsRegion Ainf (-vlx) (dir (-nJx)) ∧
    (dot nJx wfan < 0 ↔ 0 < det Jx nuJ1x) ∧ 0 < det Jx nuJ1x ∧
    dot nJx vJ1x < 0 := by
  have h1 : (-nlx : ℤ × ℤ) = ((1 : ℤ), (-1 : ℤ)) := by decide
  have h2 : (-nJx : ℤ × ℤ) = ((1 : ℤ), (0 : ℤ)) := by decide
  refine ⟨iUnion_Ahat_eq, ?_, ?_, hsweepW_iff_det_via_bridge, hsweepW_successor, by decide⟩
  · rw [h1, h2]; exact isRegion_Ainf
  · have e3 : (-vlx : ℤ × ℤ) = ((-1 : ℤ), (-1 : ℤ)) := by decide
    have e4 : dir (-nJx) = ((0 : ℤ), (1 : ℤ)) := by decide
    rw [e3, e4]; exact colle41_region_Ainf

/-! ## §9  The `maxA` binder on this family — and `hnotDP` / `envShift` with it

lane-tower-hbase, 2026-09-24.  lane-leafa-shell 指出本台架的 binder 表里缺 `maxA`
（`ChainExhaustInter.lean` 的 binder `maxA`，`maxA : ∀ i, IsMaxEnvIn Env (canonA η xper vl B u i) (A i)`），
而 team-lead 本轮裁定 `IsMaxEnvIn` 的**第三支**（极大性）才是 `shellSubStrip` 可能的来源
⟹ 表里空着这一格，§6 的反证就会被「也许极大性恰好排除你这个族」挡回来。本节把它补上。

原文对应（`b3_colle2.txt:484`）：

> `A_i` is a maximal set with respect to partial ordering by inclusion among all
> `E(𝒮_φ)`-enveloped sets `𝒯 ⊂ ℤ²` such that `B_i ⊂ 𝒯 ⊂ H_{B_i}(ℓ)` and
> `(T^{u_i}η)|𝒯 = x_per|𝒯`.

* 原文「`E(𝒮_φ)`-enveloped」 ⟷ `Env = EnvOf ↑Sphi`（`ChainExhaustInter.lean` 的 binder `hEnv`）
* 原文「`𝒯 ⊂ H_{B_i}(ℓ)`」和「`(T^{u_i}η)|𝒯 = x_per|𝒯`」 ⟷ `canonA η xper vl B u i` 的两个合取分量
* 原文「maximal」 ⟷ `IsMaxEnvIn` 第三支 `∀ T, Env T → A ⊆ T → T ⊆ C → T ⊆ A`

⭐ **手法**：把 `η` 的一致性子句造成**恰好切出 `A_i`**，即 `canonA … i = A_i` 逐字成立
（`canonA_eq_Ax`）。于是第三支退化成 `T ⊆ A_i → T ⊆ A_i`，**不需要任何极大性论证**，
也不碰 `MaxEnv.no_maximal_enveloped_halfStrip`（`MaximalEnveloped.lean:352`，
半带里的 enveloped 族没有极大元）——那条否掉的是「只靠半带就想要极大元」，
这里承重的正是原文让它承重的那个一致性子句。

⚠ **为什么要分槽**：同一个 `η` 要同时服务所有 `i`，而 `H_{B_i}(ℓ)` 们互相重叠，
所以先用 `u_i` 把第 `i` 片沿 `n_ℓ` 平移到自己的槽里（`ux`／`sx`），槽互不相交
（`slot_disjoint`）之后 `η` 才能逐片定义。分槽用的是 `dot nlx vlx = 0`：半带沿 `v⃗_ℓ` 走
不改变 `n_ℓ`-坐标，所以第 `i` 片的 `n_ℓ`-跨度就是 `A_i` 的跨度 `[0, 8K_i-1]`
（`c₈ = 0` 给下界，`c₄ = 8K-1` 给上界）。

⚠ **`x_per` 不取常值**：常值对每个 `h` 都周期，`hnotDP`（`ChainExhaustInter.lean` 的同名 binder）当场假。
取 `xperx w := (w.1 = 0)`，其周期全部满足 `h.1 = 0`（`period_fst_zero`）⟹ 两两 `det = 0`
⟹ `hnotDP` 一起兑现。这个取法是 lane-leafa-shell 的（他的泛型版在
`tmp/wip/lane-leafa-shell-maxafree.lean`，§16 禁 tmp↔tmp import，所以下面是**重证**，
不是引用；构造按本族的具体数据重写）。

⚠ 射程：本节补的是 `maxA` / `hnotDP` / `envShift` 三条，**不**主张本族满足
`ofPartsExhaustsInter` 的全部 binder；仍未碰的有 `bottom`、`fillCover`、`escapeW`、`shellEnv`
的 `∃` 形等（按 `PROTOCOL.md §54`，「没碰」不等于「假」）。 -/

/-- 槽偏移的步长。第 `i` 片在 `n_ℓ` 方向的跨度是 `8K_i - 1`，所以槽心间距取 `4K_i + 4`
（乘 2 之后是 `8K_i + 8`）就够隔开，且留出 `9` 的余量。 -/
def sx : ℕ → ℤ
  | 0 => 0
  | (i + 1) => sx i + 4 * KK i + 4

theorem sx_step (i : ℕ) : sx (i + 1) = sx i + 4 * KK i + 4 := rfl

theorem sx_le_of_le {i j : ℕ} (h : i ≤ j) : sx i ≤ sx j := by
  induction j, h using Nat.le_induction with
  | base => exact le_rfl
  | succ n _ ih =>
      have := two_le_KK n
      rw [sx_step]
      omega

theorem sx_gap {i j : ℕ} (h : i < j) : sx i + 4 * KK i + 4 ≤ sx j := by
  have h2 := sx_le_of_le h
  rw [sx_step] at h2
  omega

/-- `u_i`：把第 `i` 片沿 `n_ℓ = (-1,1)` 推到第 `i` 个槽。`dot nlx (ux i) = 2 * sx i`。 -/
def ux (i : ℕ) : ℤ × ℤ := (-(sx i), sx i)

/-- 半带的 `n_ℓ`-跨度就是 `A_i` 的跨度：`dot nlx vlx = 0`，沿 `v⃗_ℓ` 走不改变它。 -/
theorem strip_nl_bound (i : ℕ) {z : ℤ × ℤ}
    (hz : z ∈ Nivat.Colle35.halfStrip (Bx i) vlx) :
    0 ≤ -z.1 + z.2 ∧ -z.1 + z.2 ≤ 8 * KK i - 1 := by
  obtain ⟨b, hb, t, rfl⟩ := hz
  rw [Bx, Ax, mem_oct8] at hb
  simp only [vlx, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, mul_one]
  omega

/-- **槽互不相交**：`i ≠ j` 时，第 `i` 片平移进槽 `i` 之后，再减去 `u_j` 就掉出第 `j` 条半带。
这是 `η` 能逐片定义的全部理由。 -/
theorem slot_disjoint {i j : ℕ} (hij : i ≠ j) {w : ℤ × ℤ}
    (hw : w ∈ Nivat.Colle35.halfStrip (Bx i) vlx) :
    w + ux i - ux j ∉ Nivat.Colle35.halfStrip (Bx j) vlx := by
  intro hmem
  obtain ⟨hlo, hhi⟩ := strip_nl_bound i hw
  obtain ⟨hlo', hhi'⟩ := strip_nl_bound j hmem
  have hki := two_le_KK i
  have hkj := two_le_KK j
  have hexp : -(w + ux i - ux j).1 + (w + ux i - ux j).2
      = (-w.1 + w.2) + 2 * sx i - 2 * sx j := by
    simp only [ux, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]
    ring
  rw [hexp] at hlo' hhi'
  rcases lt_or_gt_of_ne hij with h | h
  · have := sx_gap h
    omega
  · have := sx_gap h
    omega

/-- `x_per`：**不是**常值（常值会当场否掉 `hnotDP`）。 -/
def xperx : Config Prop := fun w => w.1 = 0

/-- `η`：在第 `i` 个槽里，`w ∈ A_i` 时复刻 `x_per`，否则取反。写成
`(w ∈ A_i) ↔ x_per w` 是因为 `P ↔ Q` 在 `P` 真时等价于 `Q`、在 `P` 假时等价于 `¬Q`，
一条式子同时给出两支。 -/
def etax : Config Prop := fun y =>
  ∃ i : ℕ, y - ux i ∈ Nivat.Colle35.halfStrip (Bx i) vlx ∧
    ((y - ux i ∈ Ax i) ↔ ((y - ux i).1 = 0))

/-- 槽 `i` 上 `η` 的取值，`∃` 被 `slot_disjoint` 钉死在 `i` 上。 -/
theorem etax_at {i : ℕ} {w : ℤ × ℤ} (hw : w ∈ Nivat.Colle35.halfStrip (Bx i) vlx) :
    etax (w + ux i) ↔ ((w ∈ Ax i) ↔ (w.1 = 0)) := by
  constructor
  · rintro ⟨j, hj, hiff⟩
    by_cases hij : i = j
    · subst hij
      simpa using hiff
    · exact absurd hj (slot_disjoint hij hw)
  · intro h
    exact ⟨i, by simpa using hw, by simpa using h⟩

/-- ⭐ **一致性子句恰好切出 `A_i`**：`canonA η x_per v⃗_ℓ B u i = A_i`。 -/
theorem canonA_eq_Ax (i : ℕ) :
    Nivat.Colle35.canonA etax xperx vlx Bx ux i = Ax i := by
  ext w
  simp only [Nivat.Colle35.canonA, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hstrip, hval⟩
    have h1 : etax (w + ux i) ↔ (w.1 = 0) := by
      rw [hval]
      exact Iff.rfl
    have h2 : ((w ∈ Ax i) ↔ (w.1 = 0)) ↔ (w.1 = 0) := (etax_at hstrip).symm.trans h1
    tauto
  · intro hA
    have hstrip : w ∈ Nivat.Colle35.halfStrip (Bx i) vlx := subStrip i hA
    refine ⟨hstrip, ?_⟩
    have hiff : etax (w + ux i) ↔ xperx w := by
      rw [etax_at hstrip]
      simp only [xperx]
      constructor
      · intro h; exact h.mp hA
      · intro h; exact iff_of_true hA h
    exact propext hiff

/-- ⭐ **`maxA` 成立**（`ChainExhaustInter.lean` 的同名 binder，`b3_colle2.txt:484`）。

三支逐条：`Env (A_i)` 是 §6 的 `enveloped_Bx`（`B_i = A_i`）；`A_i ⊆ canonA` 与
`T ⊆ canonA → T ⊆ A_i` 都由 `canonA_eq_Ax` 直接给出。**第三支没有用到任何极大性论证**，
因为约束集本身就等于 `A_i`。 -/
theorem maxA_x (i : ℕ) :
    Nivat.Colle35.IsMaxEnvIn (EnvOf (↑Sphi : Set (ℤ × ℤ)))
      (Nivat.Colle35.canonA etax xperx vlx Bx ux i) (Ax i) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [EnvOf]
    exact enveloped_Bx i
  · intro z hz
    rw [canonA_eq_Ax i]
    exact hz
  · intro T _ _ hTC
    rw [canonA_eq_Ax i] at hTC
    exact hTC

/-- `x_per` 的每个周期都满足 `h.1 = 0`：取 `g = (0, |h₁|+|h₂|)`，`g` 与 `g + h` 都在
`{z | 0 ≤ ⟪n_ℓ, z⟫}` 里，而 `x_per g` 真 ⟹ `x_per (g+h)` 真 ⟹ `h.1 = 0`。 -/
theorem period_fst_zero {h : ℤ × ℤ}
    (hp : Nivat.Colle35.PeriodicOnWith xperx {z : ℤ × ℤ | (0 : ℤ) ≤ dot nlx z} h) :
    h.1 = 0 := by
  obtain ⟨-, hper⟩ := hp
  have habs1 := abs_nonneg h.1
  have habs2 := abs_nonneg h.2
  have hle1 := le_abs_self h.1
  have hle2 := le_abs_self h.2
  have hge1 := neg_abs_le h.1
  have hge2 := neg_abs_le h.2
  have hg : ((0 : ℤ), |h.1| + |h.2|) ∈ {z : ℤ × ℤ | (0 : ℤ) ≤ dot nlx z} := by
    simp only [Set.mem_ofPred_eq, nlx, dot]
    omega
  have hgh : ((0 : ℤ), |h.1| + |h.2|) + h ∈ {z : ℤ × ℤ | (0 : ℤ) ≤ dot nlx z} := by
    simp only [Set.mem_ofPred_eq, nlx, dot, Prod.fst_add, Prod.snd_add]
    omega
  have hEq := hper _ hg hgh
  have h0 : xperx ((0 : ℤ), |h.1| + |h.2|) := by simp only [xperx]
  rw [← hEq] at h0
  simpa only [xperx, Prod.fst_add, zero_add] using h0

/-- ⭐ **`hnotDP` 成立**（`ChainExhaustInter.lean` 的同名 binder）：两个周期的第一坐标都是 `0`，
所以它们的 `det` 必为 `0`。 -/
theorem hnotDP_x :
    ¬ ∃ h h' : ℤ × ℤ, det h h' ≠ 0 ∧
      Nivat.Colle35.PeriodicOnWith xperx {z : ℤ × ℤ | (0 : ℤ) ≤ dot nlx z} h ∧
      Nivat.Colle35.PeriodicOnWith xperx {z : ℤ × ℤ | (0 : ℤ) ≤ dot nlx z} h' := by
  rintro ⟨h, h', hdet, hp, hp'⟩
  have e1 := period_fst_zero hp
  have e2 := period_fst_zero hp'
  apply hdet
  simp only [det, e1, e2]
  ring

/-- `envShift`（`ChainExhaustInter.lean` 的同名 binder）：`EnvOf` 对平移封闭，主仓现成
`LE2.enveloped_shift_right`（`LatticeEdges.lean:1753`）。 -/
theorem envShift_x (v : ℤ × ℤ) (T : Set (ℤ × ℤ))
    (hT : EnvOf (↑Sphi : Set (ℤ × ℤ)) T) :
    EnvOf (↑Sphi : Set (ℤ × ℤ)) {z : ℤ × ℤ | z + v ∈ T} := by
  have he : {z : ℤ × ℤ | z + v ∈ T} = Nivat.LE2.shift (-v) T := by
    ext z
    simp only [Nivat.LE2.shift, Set.mem_ofPred_eq, sub_neg_eq_add]
  rw [EnvOf] at hT ⊢
  rw [he]
  exact (Nivat.LE2.enveloped_shift_right (-v)).mpr hT

/-- **§71 第二类：一致性子句真的在切**。约束集 `canonA` **严格小于**半带——
`(8K, 8K)` 在 `H_{B_i}(ℓ)` 里（从 `(0,0)` 沿 `v⃗_ℓ` 走 `8K` 步）却不在 `canonA = A_i` 里
（它违反 `z.1 ≤ c₁ = K`）。

⟹ `maxA_x` 不是「约束集等于半带」的退化情形，第三支的 `T ⊆ C` 前提有实际内容；
也就是说本族并没有靠把 `C` 放大到平凡来绕过 `MaxEnv.no_maximal_enveloped_halfStrip`
（`MaximalEnveloped.lean:352`）。 -/
theorem canonA_lt_halfStrip (i : ℕ) :
    ((8 * KK i, 8 * KK i) : ℤ × ℤ) ∈ Nivat.Colle35.halfStrip (Bx i) vlx ∧
      ((8 * KK i, 8 * KK i) : ℤ × ℤ) ∉ Nivat.Colle35.canonA etax xperx vlx Bx ux i := by
  have hk := two_le_KK i
  have ht : (((8 * KK i).toNat : ℕ) : ℤ) = 8 * KK i := Int.toNat_of_nonneg (by omega)
  refine ⟨⟨((0 : ℤ), (0 : ℤ)), ?_, (8 * KK i).toNat, ?_⟩, ?_⟩
  · rw [Bx, Ax, mem_oct8']
    exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
  · simp only [vlx, ht, Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul, mul_one]
    constructor <;> omega
  · intro hmem
    rw [canonA_eq_Ax i, Ax, mem_oct8'] at hmem
    obtain ⟨h1, -⟩ := hmem
    omega

/-- **§6 的交付加上 `maxA`。**  `η` / `x_per` 这一侧的三条 binder 全部兑现，而
`shellSubStrip` 的体在每个 `i` 上都假。

⚠ 按 `PROTOCOL.md` 纪律 9 写清楚否掉的是哪一版签名：否的是
`ofPartsExhaustsInter`（`ChainExhaustInter.lean`）的 `shellSubStrip` binder 体，
在 `ε = 1`、`i₀ = 0`、`I₀ = 0` 上，**且带着**上面这些 binder（不是剥掉前提的弱化版）。
`shellEnv` 的守卫前提由 `enveloped_shellInter` **正面**证出（`§41`：非空真）。 -/
theorem maxA_holds_but_not_shellSubStrip :
    (∀ (v : ℤ × ℤ) (T : Set (ℤ × ℤ)), EnvOf (↑Sphi : Set (ℤ × ℤ)) T →
        EnvOf (↑Sphi : Set (ℤ × ℤ)) {z : ℤ × ℤ | z + v ∈ T}) ∧
    (∀ i, EnvOf (↑Sphi : Set (ℤ × ℤ)) (Bx i)) ∧
    (∀ i, Nivat.Colle35.IsMaxEnvIn (EnvOf (↑Sphi : Set (ℤ × ℤ)))
      (Nivat.Colle35.canonA etax xperx vlx Bx ux i) (Ax i)) ∧
    (¬ ∃ h h' : ℤ × ℤ, det h h' ≠ 0 ∧
      Nivat.Colle35.PeriodicOnWith xperx {z : ℤ × ℤ | (0 : ℤ) ≤ dot nlx z} h ∧
      Nivat.Colle35.PeriodicOnWith xperx {z : ℤ × ℤ | (0 : ℤ) ≤ dot nlx z} h') ∧
    (∀ i, 0 ≤ i → EnvOf (↑Sphi : Set (ℤ × ℤ)) (ShellMink.shellInter (hatOf Ax kkx vlx i)
      (MaxEnv.shell (⋃ j, hatOf Ax kkx vlx j) vJ1x nJx 0 1) wfan)) ∧
    ¬ (∀ i : ℕ, max 0 0 ≤ i →
        ShellMink.shellInter (hatOf Ax kkx vlx i)
            (MaxEnv.shell (⋃ j, hatOf Ax kkx vlx j) vJ1x nJx 0 1) wfan ⊆
          {z | z + (kkx i : ℤ) • vlx ∈ Nivat.Colle35.halfStrip (Bx i) vlx}) :=
  ⟨envShift_x, fun i => enveloped_Bx i, maxA_x, hnotDP_x,
    fun i _ => enveloped_shellInter i, not_shellSubStrip_body⟩

/-! ## §10 回归哨兵：本台架已在 `hp_per` 之外

⚠ **本节没有原文锚，也不该有。**  它陈述的不是 `b3_colle2.txt` 的哪条命题，而是**链侧
binder 表**（`ofPartsExhaustsInter`，`ChainExhaustInter.lean`）与**本文件这组具体参数**
之间的一条不相容性——属于「台架的射程」而非「Collé 的数学」。按 §54 它只说本台架，
对链上任何命题的真假**一个字都不说**。

事情的经过：第 212 轮 lane-leafa-shell 往 `ofPartsExhaustsInter` 加了
`(hp_per : p ∈ Per xper)`（原文锚 `b3_colle2.txt:496`，集成者批准），与既有的
`(hdet : det p vl = 0)` 同处一张表。`no_p_satisfies_hp_per_and_hdet` 说明：**在本台架的
`xperx` / `vlx` 下，这两条同时为真的 `p` 只有 `p = 0`，而 `p = 0` 撞表里其余 binder**
——不是 `px`（本文件 `def px`）这一个取值挂掉，是全体 `p` 都挂掉。

⟹ `binders_hold_but_not_shellSubStrip` / `maxA_holds_but_not_shellSubStrip` 依然是正确的内核
事实，但结论必须重述成「**第 211 轮那张表**推不出 `shellSubStrip`」；对含 `hp_per` 的**新表**，
本台架是空真的，补齐 `fillCover` 之类剩余 binder 也**不构成反证**。

本节的消费者就是它自己的 docstring：防止任何人（包括未来的我们）再花一轮在这个台架上
重推一遍这三行。 -/

/-- `xperx`（本文件 `def xperx`，`fun w => w.1 = 0`）的**全平面**周期群落在竖轴上：`h ∈ Per xperx → h.1 = 0`。

取 `z := (-h.1, 0)`，则 `z + h` 的第一坐标是 `0`，`xperx (z + h)` 真；`Per` 给
`xperx (z + h) = xperx z`（`Per.apply`，`Nivat/Defs/Config.lean:81`），故 `-h.1 = 0`。

⚠ 与 `period_fst_zero`（本文件，上面）**不是**同一条：那条的前提是半平面上的
`Colle35.PeriodicOnWith`（`Lemma35.lean:396`），这条的前提是全平面的 `Nivat.Per`
（`Defs/Config.lean:62`）。`hp_per` 要的是后者，**不要**拿 `period_fst_zero` 顶替。 -/
theorem mem_Per_xperx_fst_zero {h : ℤ × ℤ} (hh : h ∈ Nivat.Per xperx) : h.1 = 0 := by
  have hEq : xperx (((-h.1 : ℤ), (0 : ℤ)) + h) = xperx ((-h.1 : ℤ), (0 : ℤ)) :=
    Nivat.Per.apply hh _
  have htrue : xperx (((-h.1 : ℤ), (0 : ℤ)) + h) := by
    show ((-h.1 : ℤ) + h.1) = 0
    omega
  have hz : (-h.1 : ℤ) = 0 := (iff_of_eq hEq).mp htrue
  omega

/-- ⭐ **回归哨兵：本台架的参数下，`hp_per` + `hdet` 蕴含 `¬ hpvJ`。**

三行，逐条对着 `ofPartsExhaustsInter`（`ChainExhaustInter.lean`）的 binder：

1. `hp_per : p ∈ Per xperx`（同表 binder `hp_per`）⟹ `p.1 = 0`（`mem_Per_xperx_fst_zero`）；
2. `hdet : det p vlx = 0`（同表 binder `hdet`），`vlx = (1,1)`（本文件 `def vlx`）⟹ `p.1 = p.2` ⟹ `p = 0`；
3. `p = 0` ⟹ 对**任意** `vJ` 有 `det p vJ = 0`，正好否掉 `hpvJ : det p vJ ≠ 0`。

结论写成 `det p vJ = 0` 而不是 `False`，是为了同时做到两件事：它直接否掉 `hpvJ`，而且
**对 `vJ` 不要任何前提**（`FaceBlock` 那一侧的参数怎么选都不影响这条）。

⚠ **`hpvJ` 已经不是 binder 了（第 215 轮，lane-env-refute 执行删除）**，所以本条现在撞的是一条
**推论**而不是表里的一行：`det p vJ ≠ 0` 由 `vJ_prim` + `FaceBlock.dot_nJ_vJ` + `dot_nJ_p` 经
`det_ne_zero_of_dot`（`ChainGeom.lean:300`，模板见同文件 `ChainGeom.lean:364-365` 的 `hdetpv`——这两处行号我
第 214 轮**亲读**过）在 `ofPartsExhaustsInter` 体内 `let hpvJ` 推出。本条仍然有效（否掉一条推论
同样否掉它的结论），但**不要只靠它**：真正落在表上的是下面的
`no_p_satisfies_hp_per_hdet_dot_nJ_p`，它撞 `dot_nJ_p`，那是**输入** binder，正是上面那条推导
自己要吃的前提，划不掉。 -/
theorem no_p_satisfies_hp_per_and_hdet (p : ℤ × ℤ) (vJ : ℤ × ℤ)
    (hp_per : p ∈ Nivat.Per xperx) (hdet : det p vlx = 0) : det p vJ = 0 := by
  have h1 : p.1 = 0 := mem_Per_xperx_fst_zero hp_per
  have h2 : p.2 = 0 := by
    simp only [det, vlx] at hdet
    omega
  simp only [det, h1, h2]
  ring

/-- ⭐ **哨兵的硬化版：不经过 `hpvJ`。**

同样两步逼出 `p.1 = p.2 = 0`，但结论落在 `dot nJx p = 0`，直接否掉同表 binder
`dot_nJ_p : dot nJ p ≠ 0`。

为什么要这一条：`hpvJ` 是**可推导的**，而第 215 轮 lane-env-refute 已经按这个读数把它从表里
删掉了（现在是 `ofPartsExhaustsInter` 体内的 `let hpvJ`），上面那条
`no_p_satisfies_hp_per_and_hdet` 因此不再抵到表里的任何一行；而 `dot_nJ_p` 是表的
**输入**（`hdetpv` 的推导恰恰要用它），删不得。⟹ **无论 `hpvJ` 去留，本台架都在新表辖域之外。** -/
theorem no_p_satisfies_hp_per_hdet_dot_nJ_p (p : ℤ × ℤ)
    (hp_per : p ∈ Nivat.Per xperx) (hdet : det p vlx = 0) : dot nJx p = 0 := by
  have h1 : p.1 = 0 := mem_Per_xperx_fst_zero hp_per
  have h2 : p.2 = 0 := by
    simp only [det, vlx] at hdet
    omega
  simp only [dot, nJx, h1, h2]
  ring

/-- 上一条在本台架实际取值上的读数：`px = (-1,-1)`（本文件 `def px`）根本不是 `xperx` 的周期。
这是集成者在 `ChainExhaustInter.lean` 的 `hp_per` binder 注释里手算的那一步，落成内核事实。 -/
theorem px_not_mem_Per_xperx : px ∉ Nivat.Per xperx := by
  intro hh
  have h1 : px.1 = 0 := mem_Per_xperx_fst_zero hh
  rw [px] at h1
  exact absurd h1 (by decide)

/-! ## §11 `FaceBlock 𝒮_φ n_Jx v_Jx` 的内核构造（第 215 轮，team-lead 派工）

**为什么在这里**：`FillCoverGuarded.fillCover_of_window` 的 binder 表里有
`F : FaceBlock S nJ vJ`，lane-leafa-gen 要把「结论为假」推到「`hwin` 为假」必须过这条
定理，于是需要 `F` 的**内核**收据；在此之前它只是「lane-tower-hbase 报」（§55），
两条包装因此是条件式的。本节把它落成实物。

⚠ **`vJ` 只能取 `(0,1)`，不能取 `vJ1x`。** `FaceBlock` 的第十一个字段是
`dot_nJ_vJ : dot n v = 0`（`ANormal.lean:616`），而 `dot nJx vJ1x = -1 ≠ 0`
（`nJx = (-1,0)`、`vJ1x = (1,1)`）⟹ `FaceBlock Sphi nJx vJ1x` **是空的**，见
`no_faceBlock_at_vJ1x`。`vJ1x` 是**扫掠**方向（`hsweep : dot nJ vJ1 < 0`），
`vJ` 是**面**方向（`dot nJ vJ = 0`），两者在本表里必须不同，别混。

取值 `a = (0,0)`、`a' = (0,1)`、`r = 1`、`v = (0,1)`：`𝒮_φ` 的 `u₁`-面（`x = 0`）恰有
`(0,0)` 与 `(0,1)` 两点，其余十点满足 `x ≤ -1`，这一句同时兑现
`lex` / `lex'` / `edge` / `edge'` 四条；`edge`/`edge'` 的 `∃ j ≤ r` 在 `r = 1` 上只有
`j = 1` 一种取法。

⚠ 本节**没有原文锚**，与 §10 同理：它陈述的是本台架的一个具体对象存在，不是
`b3_colle2.txt` 的命题。 -/

/-- **`Set` 版格凸 ⟹ `Finset` 版格凸。**  主仓有反方向
（`Nivat.Colle35.isLatticeConvexRegion_coe`，`ChainAssemble.lean`，按名字找），没有这一方向。

证法：`C` 是包住 `↑S` 的凸集 ⟹ 它包住 `Conv S`（`convexHull_min`）⟹ `Conv S` 里的格点
落在 `C` 的原像里 ⟹ 落在 `↑S` 里。⚠ 只用 `Convex ℝ C`，**不用** `IsClosed C`。

本轮真有主仓消费者：下面的 `latticeConvex_Sphi_oct8`。 -/
theorem latticeConvex_of_isLatticeConvexRegion_coe {S : Finset (ℤ × ℤ)}
    (h : IsLatticeConvexRegion (↑S : Set (ℤ × ℤ))) : LatticeConvex S := by
  obtain ⟨C, hconv, -, hEq⟩ := h
  intro z hz
  have himg : toReal '' (↑S : Set (ℤ × ℤ)) ⊆ C := by
    rintro _ ⟨y, hy, rfl⟩
    rw [hEq] at hy
    exact hy
  have hzC : toReal z ∈ C := convexHull_min himg hconv hz
  have hzS : z ∈ (↑S : Set (ℤ × ℤ)) := by rw [hEq]; exact hzC
  exact Finset.mem_coe.mp hzS

/-- `Sphi` 的成员判据，摊成 `oct8` 的八条不等式（供 `omega` 用）。 -/
theorem mem_Sphi_iff {z : ℤ × ℤ} :
    z ∈ Sphi ↔ z.1 ≤ 0 ∧ z.1 + z.2 ≤ 1 ∧ z.2 ≤ 2 ∧
      -z.1 + z.2 ≤ 4 ∧ -z.1 ≤ 3 ∧ -z.1 - z.2 ≤ 3 ∧ -z.2 ≤ 1 ∧ z.1 - z.2 ≤ 0 := by
  rw [← Finset.mem_coe, coe_Sphi]
  exact mem_oct8

/-- `LatticeConvex Sphi` —— `FaceBlock` 的第四个字段。 -/
theorem latticeConvex_Sphi_oct8 : LatticeConvex Sphi :=
  latticeConvex_of_isLatticeConvexRegion_coe
    (by
      rw [coe_Sphi]
      exact isLatticeConvexRegion_oct8 _ _ _ _ _ _ _ _)

/-- `v_J := (0,1)`：由 `dot nJx v = 0`（`FaceBlock.dot_nJ_vJ`）＋ `Primitive v` ＋
`lex`/`lex'` 的方向唯一定出。**不是** `vJ1x`，见 `no_faceBlock_at_vJ1x`。 -/
def vJx : ℤ × ℤ := (0, 1)

/-- `gen := F.a'`，即 `gen_eq` 那条 binder 的取值。 -/
def genx : ℤ × ℤ := (0, 1)

theorem dot_negNJ (z : ℤ × ℤ) : dot (-nJx) z = z.1 := by
  simp only [nJx, dot, Prod.fst_neg, Prod.snd_neg]
  ring

theorem dot_NJ (z : ℤ × ℤ) : dot nJx z = -z.1 := by
  simp only [nJx, dot]
  ring

theorem dot_VJ (z : ℤ × ℤ) : dot vJx z = z.2 := by
  simp only [vJx, dot]
  ring

theorem dot_negVJ (z : ℤ × ℤ) : dot (-vJx) z = -z.2 := by
  simp only [vJx, dot, Prod.fst_neg, Prod.snd_neg]
  ring

/-- ⭐ **`FaceBlock` 包在 oct8 上为真**，逐字符对 `Nivat.Colle35.FaceBlock`
（`ANormal.lean`，按名字找；十一个字段）。 -/
def faceBlockX : Nivat.Colle35.FaceBlock Sphi nJx vJx where
  a := ((0 : ℤ), (0 : ℤ))
  a' := ((0 : ℤ), (1 : ℤ))
  r := 1
  latticeConvex_S := latticeConvex_Sphi_oct8
  a_mem := by decide
  a'_mem := by decide
  lex := by
    intro b hb
    rw [Finset.mem_erase] at hb
    obtain ⟨hne, hmem⟩ := hb
    rw [mem_Sphi_iff] at hmem
    have hne' : ¬ (b.1 = 0 ∧ b.2 = 0) := fun h => hne (Prod.ext_iff.mpr ⟨h.1, h.2⟩)
    rw [dot_negNJ, dot_negNJ, dot_negVJ, dot_negVJ]
    simp only []
    omega
  lex' := by
    intro b hb
    rw [Finset.mem_erase] at hb
    obtain ⟨hne, hmem⟩ := hb
    rw [mem_Sphi_iff] at hmem
    have hne' : ¬ (b.1 = 0 ∧ b.2 = 1) := fun h => hne (Prod.ext_iff.mpr ⟨h.1, h.2⟩)
    rw [dot_negNJ, dot_negNJ, dot_VJ, dot_VJ]
    simp only []
    omega
  edge := by
    intro b hb
    rw [Finset.mem_erase] at hb
    obtain ⟨hne, hmem⟩ := hb
    rw [mem_Sphi_iff] at hmem
    have hne' : ¬ (b.1 = 0 ∧ b.2 = 0) := fun h => hne (Prod.ext_iff.mpr ⟨h.1, h.2⟩)
    by_cases hx : b.1 = 0
    · refine Or.inl ⟨1, le_refl 1, le_refl 1, ?_⟩
      refine Prod.ext_iff.mpr ⟨?_, ?_⟩
      · simp only [vJx, Prod.fst_add, Prod.smul_fst, smul_eq_mul, Nat.cast_one]
        omega
      · simp only [vJx, Prod.snd_add, Prod.smul_snd, smul_eq_mul, Nat.cast_one]
        omega
    · refine Or.inr ?_
      rw [dot_NJ]
      simp only [Prod.fst_sub]
      omega
  edge' := by
    intro b hb
    rw [Finset.mem_erase] at hb
    obtain ⟨hne, hmem⟩ := hb
    rw [mem_Sphi_iff] at hmem
    have hne' : ¬ (b.1 = 0 ∧ b.2 = 1) := fun h => hne (Prod.ext_iff.mpr ⟨h.1, h.2⟩)
    by_cases hx : b.1 = 0
    · refine Or.inl ⟨1, le_refl 1, le_refl 1, ?_⟩
      refine Prod.ext_iff.mpr ⟨?_, ?_⟩
      · simp only [vJx, Prod.fst_sub, Prod.smul_fst, smul_eq_mul, Nat.cast_one]
        omega
      · simp only [vJx, Prod.snd_sub, Prod.smul_snd, smul_eq_mul, Nat.cast_one]
        omega
    · refine Or.inr ?_
      rw [dot_NJ]
      simp only [Prod.fst_sub]
      omega
  dot_nJ_vJ := by
    rw [dot_NJ]
    simp only [vJx, neg_zero]

/-- ⭐ **team-lead 第 215 轮点名的那条**：存在性形状，可直接喂给需要
`Nonempty (FaceBlock …)` 的消费者。要具体字段就用 `faceBlockX`。 -/
theorem faceBlock_oct8 : Nonempty (Nivat.Colle35.FaceBlock Sphi nJx vJx) :=
  ⟨faceBlockX⟩

/-- ⚠ **反向哨兵**：把 `vJ` 写成 `vJ1x` 的那版签名是**空**的。
`FaceBlock.dot_nJ_vJ` 要 `dot n v = 0`，而 `dot nJx vJ1x = -1`。
留着是为了防止有人按扫掠方向 `vJ1x` 去要 `FaceBlock`（§85.2：签名里写得出来不等于站得住）。 -/
theorem no_faceBlock_at_vJ1x : ¬ Nonempty (Nivat.Colle35.FaceBlock Sphi nJx vJ1x) := by
  rintro ⟨F⟩
  exact absurd F.dot_nJ_vJ (by decide)

/-- `nJ_prim`：`Primitive (-1,0)`。 -/
theorem nJ_prim_x : Primitive nJx :=
  prim_iff_primitive.mp (by decide : Prim nJx)

/-- `vJ_prim`：`Primitive (0,1)`。 -/
theorem vJ_prim_x : Primitive vJx :=
  prim_iff_primitive.mp (by decide : Prim vJx)

/-- `vJ_ne`。 -/
theorem vJ_ne_x : vJx ≠ 0 := by decide

/-- `gen_eq`：定义式绑定，零内容。 -/
theorem gen_eq_x : genx = faceBlockX.a' := rfl

/-! ## `i₀` / `I₀` 全称化（lane-tower-hbase，集成者 2026-09-26 批准 splice）

本节三条把 `not_shellSubStrip_body` / `binders_hold_but_not_shellSubStrip` 的
`i₀ = I₀ = 0` 实例抬成对**每一对** `(i₀, I₀)` 都成立。旧形作为新形的实例保留
（`not_shellSubStrip_body_of_all`），**接口不变**。

⭐ 为何不空真：正控那一条（`EnvOf … shellInter`）同样改成 `∀ i, i₀ ≤ i → …`，
由 `enveloped_shellInter i`（一条正向的 `∀ i` 定理）逐点兑现；`ε = 1` 保留（`0 < 1`）。
⇒ `i₀ = 0` 这个实例在证明里一个字都没用到，故 lane-leafa-gen 报的
`b3_colle2.txt:38`（`ℕ = {1,2,…}`）约定无论如何裁，本节都不需要重新实例化。

⚠ lane-tower-hlev 本轮测到：`enveloped_shellInter` 的外层 `∀ (i : ℕ)` 含 `i = 0`，
而 `ε = 1`，所以它**不**满足「包络守卫白送 `ε < i₀`」那条代理——本台架的 `Ahat` 走
`KK i = i + 2`，`i = 0` 处已经厚过 `ε = 1`。正确判准是「守卫在 `i = i₀` 处是否为真」。
（按 hlev 报，本处未复跑，§55。）
-/

/-- **`i₀` / `I₀` 全称化的反证**：不在 `i₀ = I₀ = 0` 一格上取，对**每一对** `(i₀, I₀)` 都为假。
⟹ 无论 `ChainDataGeomParts` 那边落不落 `0 < i₀` / `0 < I₀`（lane-leafa-gen 2026-09-25 报的
`b3_colle2.txt:38`「`ℕ = {1,2,…}`」约定），本条都不需要重新实例化。 -/
theorem not_shellSubStrip_body_all (i₀ I₀ : ℕ) :
    ¬ (∀ i : ℕ, max i₀ I₀ ≤ i →
        ShellMink.shellInter (hatOf Ax kkx vlx i)
            (MaxEnv.shell (⋃ j, hatOf Ax kkx vlx j) vJ1x nJx 0 1) wfan ⊆
          {z | z + (kkx i : ℤ) • vlx ∈ Nivat.Colle35.halfStrip (Bx i) vlx}) := by
  intro h
  exact escape_not_mem_halfStrip (max i₀ I₀)
    (h (max i₀ I₀) le_rfl (escape_mem_shellInter (max i₀ I₀)))

/-- **交付形，`i₀` / `I₀` 全称化**：正控（`EnvOf` 那条）也改成 `∀ i, i₀ ≤ i → …`，
故 `i₀ = 0` 这个实例一个字都没用到。`ε = 1` 保留（`0 < 1`，正性无争议）。 -/
theorem binders_hold_but_not_shellSubStrip_all (i₀ I₀ : ℕ) :
    ((nJx = -Jx ∧ nlx = -ellx ∧ wfan = -(dir nuJ1x) ∧ vlx = dir (-nlx) ∧
      0 < det ellx Jx ∧ 0 < det Jx nuJ1x ∧ dot nJx wfan < 0 ∧ dot nJx vJ1x < 0 ∧
      dot nlx vlx = 0 ∧ Prim nlx ∧ vlx ≠ 0) ∧
     (∀ μ : ℤ × ℤ, 0 < det Jx μ → 0 < det μ nuJ1x → μ ∉ E (↑Sphi : Set (ℤ × ℤ))) ∧
     (nuJ1x ∈ E (↑Sphi : Set (ℤ × ℤ)) ∧ mux ∈ E (↑Sphi : Set (ℤ × ℤ)) ∧ nuJ1x ≠ mux ∧
       0 < det Jx nuJ1x ∧ 0 < det nuJ1x nlx ∧ 0 < det Jx mux ∧ 0 < det mux nlx ∧
       nux = -mux ∧ dot nux vlx ≤ 0 ∧ 0 < dot nux wfan) ∧
     (∀ i, Enveloped (↑Sphi : Set (ℤ × ℤ)) (Bx i)) ∧
     (∀ i, Bx i ⊆ Ax i) ∧ (∀ i, Ax i ⊆ Bx (i + 1)) ∧
     (∀ i, Ax i ⊆ Nivat.Colle35.halfStrip (Bx i) vlx) ∧
     (∀ i j, i ≤ j → hatOf Ax kkx vlx i ⊆ hatOf Ax kkx vlx j) ∧
     (∀ i, (hatOf Ax kkx vlx i).Finite) ∧
     (∀ i, hatOf Ax kkx vlx i ⊆ halfPlaneGE nJx 0) ∧
     SweptClosed (⋃ j, hatOf Ax kkx vlx j) vJ1x nJx 0 ∧
     (⋃ j, hatOf Ax kkx vlx j).Nonempty ∧
     Nivat.Colle35.Exhausts Ax nlx 0 ∧
     (0 : ℕ) < 1 ∧
     (∀ i, i₀ ≤ i → EnvOf (↑Sphi : Set (ℤ × ℤ)) (ShellMink.shellInter (hatOf Ax kkx vlx i)
        (MaxEnv.shell (⋃ j, hatOf Ax kkx vlx j) vJ1x nJx 0 1) wfan))) ∧
    ¬ (∀ i : ℕ, max i₀ I₀ ≤ i →
        ShellMink.shellInter (hatOf Ax kkx vlx i)
            (MaxEnv.shell (⋃ j, hatOf Ax kkx vlx j) vJ1x nJx 0 1) wfan ⊆
          {z | z + (kkx i : ℤ) • vlx ∈ Nivat.Colle35.halfStrip (Bx i) vlx}) := by
  obtain ⟨f1, f2, f3, f4, -, f6, f7, f8, f9, f10, f11, -, f13⟩ := fan_data
  refine ⟨⟨⟨f1, f2, f3, f4, f6, f7, f8, f9, f10, f11, f13⟩, fan_successor, arc_J_nl_two,
    enveloped_Bx, subBA, subAB, subStrip, mono_hat, finite_hat, hhp_x, swept_x, nonempty_x,
    exhausts_x, by norm_num, fun i _ => enveloped_shellInter i⟩,
    not_shellSubStrip_body_all i₀ I₀⟩

/-- 旧的 `i₀ = I₀ = 0` 形是新形的一个实例，接口不变（`max 0 0 = 0` 由 `Nat.max_self`）。 -/
theorem not_shellSubStrip_body_of_all :
    ¬ (∀ i : ℕ, max 0 0 ≤ i →
        ShellMink.shellInter (hatOf Ax kkx vlx i)
            (MaxEnv.shell (⋃ j, hatOf Ax kkx vlx j) vJ1x nJx 0 1) wfan ⊆
          {z | z + (kkx i : ℤ) • vlx ∈ Nivat.Colle35.halfStrip (Bx i) vlx}) :=
  not_shellSubStrip_body_all 0 0

end Nivat.LaneTowerOct8

#print axioms Nivat.LaneTowerOct8.E_oct8
#print axioms Nivat.LaneTowerOct8.enveloped_oct8
#print axioms Nivat.LaneTowerOct8.shellInter_eq
#print axioms Nivat.LaneTowerOct8.enveloped_shellInter
#print axioms Nivat.LaneTowerOct8.escape_mem_shellInter
#print axioms Nivat.LaneTowerOct8.escape_not_mem_halfStrip
#print axioms Nivat.LaneTowerOct8.not_shellSubStrip_body
#print axioms Nivat.LaneTowerOct8.binders_hold_but_not_shellSubStrip
#print axioms Nivat.LaneTowerOct8.rec_p_x
#print axioms Nivat.LaneTowerOct8.isRegion_Ainf
#print axioms Nivat.LaneTowerOct8.region_orientation_audit
#print axioms Nivat.LaneTowerOct8.ray_rules
#print axioms Nivat.LaneTowerOct8.hsweepW_is_successor
#print axioms Nivat.LaneTowerOct8.colle41_region_Ainf
#print axioms Nivat.LaneTowerOct8.hsweepW_iff_det_via_bridge
#print axioms Nivat.LaneTowerOct8.hsweep_both_readings
#print axioms Nivat.LaneTowerOct8.region_audit_colle41
#print axioms Nivat.LaneTowerOct8.slot_disjoint
#print axioms Nivat.LaneTowerOct8.canonA_eq_Ax
#print axioms Nivat.LaneTowerOct8.maxA_x
#print axioms Nivat.LaneTowerOct8.period_fst_zero
#print axioms Nivat.LaneTowerOct8.hnotDP_x
#print axioms Nivat.LaneTowerOct8.envShift_x
#print axioms Nivat.LaneTowerOct8.canonA_lt_halfStrip
#print axioms Nivat.LaneTowerOct8.maxA_holds_but_not_shellSubStrip
#print axioms Nivat.LaneTowerOct8.mem_Per_xperx_fst_zero
#print axioms Nivat.LaneTowerOct8.no_p_satisfies_hp_per_and_hdet
#print axioms Nivat.LaneTowerOct8.no_p_satisfies_hp_per_hdet_dot_nJ_p
#print axioms Nivat.LaneTowerOct8.px_not_mem_Per_xperx
#print axioms Nivat.LaneTowerOct8.latticeConvex_of_isLatticeConvexRegion_coe
#print axioms Nivat.LaneTowerOct8.latticeConvex_Sphi_oct8
#print axioms Nivat.LaneTowerOct8.faceBlockX
#print axioms Nivat.LaneTowerOct8.faceBlock_oct8
#print axioms Nivat.LaneTowerOct8.no_faceBlock_at_vJ1x
#print axioms Nivat.LaneTowerOct8.nJ_prim_x
#print axioms Nivat.LaneTowerOct8.vJ_prim_x
#print axioms Nivat.LaneTowerOct8.gen_eq_x
#print axioms Nivat.LaneTowerOct8.not_shellSubStrip_body_all
#print axioms Nivat.LaneTowerOct8.binders_hold_but_not_shellSubStrip_all
#print axioms Nivat.LaneTowerOct8.not_shellSubStrip_body_of_all
