/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.ChainAssemble
import Nivat.External.Colle.PolyChain

/-!
# `Â_i` 与 `A_i` 的平移律：`E` / `faceLen` / `faceStart`

lane-leafa-gen，2026-09-24（第 201 轮，team-lead 口令 (iii) ＋ §6）。

**两批八条**：§1–§2 是**不变量**（`E` / `faceLen` 平移前后相等，口令 (iii)）；
§3–§5 是**带位移的**（`faceStart` / 末端随平移动，口令 §6），技术上需要一条唯一性引理，
详见 §3 的说明。§3–§5 的原文锚点与方向口径写在 §4 的节注里。

## 原文位置

`b3_colle2.txt:488`（本轮亲读，§50）定义平移本身：

> Setting $\hat{A}_{i}:=A_{i}-k_{i}\vec{v}_{\boldsymbol{\ell}}$ for all $i\in\mathbb{N}$,
> where $k_{1}=0$

即 `Â_i` 是 `A_i` 沿 `-k_i v⃗_ℓ` 的整体平移。Lean 侧 `hatOf`（`ChainMax.lean:87`）与
`hatOf_eq_shift`（`ChainAssemble.lean:327`）已把这句转录完毕，本文件不重做转录。

⚠ **本文件三条引理原文都没有逐字陈述。** 原文是在两处**默认**了它们：

* `:498`「Let $w_{i}(j)\in E(\hat{A}_{i})$ denote the edge of $\hat{A}_{i}$ that is parallel
  to the oriented line $\boldsymbol{\ell}_{j}$」—— 「`Â_i` 有一条平行于 `ℓ_j` 的边」这句话
  之所以不需要另证，正因为 `E (Â_i) = E (A_i)`（`E_hatOf`）；
* `:500`「$\left|\hat{A}_{i}\cap w_{i}(J)\right|<\left|\hat{A}_{i+1}\cap w_{i+1}(J)\right|$」
  —— 链侧的生产者（`LeafAJSelect.exists_J_of_edge_unbounded`，`LeafAJSelect.lean:321`）
  给出的是对 `A i` 说的面长，原文直接写成对 `Â_i` 说的，中间省掉的就是
  `faceLen (Â_i) ν = faceLen (A_i) ν`（`faceLen_hatOf`）。

逐量词对应：`:488` 的量词只有「for all $i\in\mathbb{N}$」，本文件三条都对所有 `i` 陈述，
对 `A` / `kk` / `vl` / `ν` 全称（原文里它们是固定的具体对象，全称化是**弱化**不是加强）。
没有原文对应物的量词一个也没加。

## 为什么值得单独落主仓（硬规矩 1/4）

这三条是**纯搬运，没有新数学**，但 `Nivat/` 里一条都没有具名版本，而 `tmp/wip/` 里已经有
三份各自重造的副本。落一份具名的，三份副本可删。

现成消费者（都在 `tmp/wip/`，等本文件进主仓后改成一行 `rw`）：

* `faceLen_shift` / `faceLen_hatOf` → `lane-leafa-shell-jdata.lean:91`（她的 `hJunb_hatOf`
  `:113`、`arcBdd_hatOf` `:124` 都只是它在 binder 下的搬运）、`LeafAAssemble.lean:605`
  （内联 `have hfaceLen_shift`，在 `:706`/`:761`/`:840` 用了三次）、
  `shell_inst.lean:77`（`private theorem faceLen_shift`）；
* `E_hatOf` → `lane-leafa-shell-jdata.lean:86`（她的 `hJEall_of_enveloped` `:103` 用它）。

## §58 查重读数（本轮亲跑，**按形状不按名字**，范围含 `tmp/wip/`）

⚠ 头一遍我只 grep 了 `faceLen (hatOf` 这一种形状，漏掉了一般的 `faceLen (shift …`；
lane-leafa-shell 提醒后补跑了下面这几条（她自己刚被同一个盲区咬过：`escapeW` 的生产者
其实在主仓 `EscapeW.lean:320`，按名字 grep 会先撞 tmp 里的过期副本）。

| 形状 | `Nivat/` | `tmp/wip/` |
|---|---|---|
| `faceLen (shift` / `faceLen (Nivat.LE2.shift` | **0** | 2（`LeafAAssemble.lean:605`、`shell_inst.lean:77`） |
| `faceLen (hatOf … ) … = faceLen` 等式形状 | **0** | 1（`lane-leafa-shell-jdata.lean:92`） |
| `E (hatOf …) = E (A` | **0** | 1（`lane-leafa-shell-jdata.lean:87`） |
| `faceLen … = faceLen …`（任意） | 3，全是**同一集合不同下标**（`LeafAJSelect.lean:406`、`ShellRegionJ.lean:406`、`HsuppCaseCW.lean:582`），不是平移律 | — |

## 与主仓已有物的边界（§58，先说清楚差在哪）

* `ShellSubStrip.E_hatOf_eq`（`ShellSubStrip.lean:2790`）给 `E (Â_i) = E ↑𝒮_φ`，要 `maxA`
  ＋ `Env` 钉死两个 binder；`AhatEnv.E_eq_of_enveloped`（`AhatEnv.lean:61`）给
  `E T = E ↑𝒮_φ`，要 `(E U).Finite` ＋ `PosArea U` ＋ `Enveloped`。
  本文件的 `E_hatOf` 是这两条的**上游**：零 binder，结论落在 `A i` 上。消费者手上只有
  `henv : ∀ i, Enveloped ↑𝒮_φ (A i)`（没有 `maxA`、不想拖 `PosArea`）时走本条。
* ⛔ **`Arc` 那一条不在本文件里，故意的。** 口令 (iii) 点名了「`faceLen` / `E` / `Arc`
  三件套」，我按字面写出来之后按形状复查，发现主仓**已有**
  `LeafAJSelect.Arc_eq_of_enveloped`（`LeafAJSelect.lean:470`），证法逐字同构
  （`Finset.ext` ＋ 两次 `mem_Arc` ＋ 一条 `E` 相等），只是喂进去的 `E` 相等换成了
  `E_eq_of_enveloped`。而 `Enveloped ↑𝒮_φ (Â_i)` 主仓也现成
  （`ShellSubStrip.enveloped_hatOf`，`:2765`）⟹ 任何「`Arc` 架在 `Â_i` 上」的需求
  已经被这两条合起来服务完了。再写一条是 `KkAlignUnique` 那次的形状，**不写**。

## ⛔ 适用范围：**只管 `A_i` / `Â_i`，不管 `shellT` / `MaxEnv.shell`**

lane-leafa-shell 2026-09-24 提醒（她的 lane-env-refute 台架读数，**我未复核，§55**）：
`shellT` 的 `n`-面在 `⟪n,w⟫ > 0` 的那一类上**不是**平移不变的——它是 `Â_i` 的面先平移
出去、再被截掉，她台架上 `n = (-1,0)` 时 `|face shellT n| = max(1, |face Â_i n| - ε)`，
且 `face shellT n` 与 `face Â_i n` **完全不相交**。她的结论：`faceLen_shift` 这一族在
`⟪n,w⟫ ≤ 0` 的一整类上是白给的（走 `face_subset_face_reachSet_inter`），
**正类上救不了 `hposFace`**。

本文件的三条与此不冲突：它们的主目标是 `shift v T` 与 `hatOf A kk vl i`，**结论里根本
没出现 `MaxEnv.shell` / `shellT`**，也没有任何一条把 `faceLen` 的不变性推广到截断之后。
写在这里是防止后来人把 `faceLen_shift` 往 `shellT` 上套——**套不上，别试**。

## 不 import 的东西（⛔ 硬规矩）

`RegionSteps` / `ColleRegion` / `Case2WindowProbe` / `NfpLPreamble` 一个都不在本文件的
传递 import 闭包里 —— 本轮用脚本重算了两条直接 import（`ChainAssemble` 闭包 158 个模块、
`PolyChain` 闭包 84 个模块）对这四个模块的命中数，均为 **0**（盲区 2：不采信别人的转述）。

## 用法警告

`Nivat.HatShift` 与 `Nivat.LaneLeafAShellJData` 里同名的两条（`E_hatOf` / `faceLen_hatOf`）
逐字重名。**请用全名引用，不要 `open Nivat.HatShift`**；或者把 tmp 里的本地副本删掉。
-/

set_option autoImplicit false

namespace Nivat.HatShift

open Nivat Nivat.LE2 Nivat.Colle35 Nivat.PolyChain

/-! ## §1. 一般的平移律：`faceLen` 不随平移改变

`E_shift`（`LatticeEdges.lean:689`）、`face_shift`（`:663`）、`encard_shift`（`:693`）
主仓已有；缺的只有 `faceLen` 这一层，因为 `faceLen` 定义在下游的 `PolyChain.lean:90`
（`faceLen T ν := (face T ν).encard.toNat - 1`）。 -/

/-- **`faceLen` 的平移不变性。**  `face` 随平移整体平移（`face_shift`），`encard` 不变
（`encard_shift`），而 `faceLen` 只是 `encard.toNat - 1`。

原文无逐字对应物：这是 `:500` 把 `|A_i ∩ w(ν)|` 与 `|Â_i ∩ w(ν)|` 当同一个数用时
所默认的事实。 -/
theorem faceLen_shift (v : ℤ × ℤ) (T : Set (ℤ × ℤ)) (ν : ℤ × ℤ) :
    faceLen (shift v T) ν = faceLen T ν := by
  unfold faceLen
  rw [face_shift, encard_shift]

/-! ## §2. 专用到 `Â_i = A_i - k_i v⃗_ℓ`（`b3_colle2.txt:488`） -/

/-- **`E (Â_i) = E (A_i)`**（`b3_colle2.txt:488` 的平移 + `E_shift`）。

这是 `:498`「the edge of $\hat{A}_{i}$ that is parallel to the oriented line
$\boldsymbol{\ell}_{j}$」这句话得以成立的理由：`Â_i` 的边法向集合与 `A_i` 逐字相同，
所以链侧对 `A_i` 拿到的边法向可以直接当作 `Â_i` 的边法向用。

与 `ShellSubStrip.E_hatOf_eq`（`:2790`）、`AhatEnv.E_eq_of_enveloped`（`AhatEnv.lean:61`）
的分界见文件头。 -/
theorem E_hatOf (A : ℕ → Set (ℤ × ℤ)) (kk : ℕ → ℕ) (vl : ℤ × ℤ) (i : ℕ) :
    E (hatOf A kk vl i) = E (A i) := by
  rw [hatOf_eq_shift, E_shift]

/-- **`faceLen (Â_i) ν = faceLen (A_i) ν`**（`b3_colle2.txt:488` 的平移 + `faceLen_shift`）。

消费者：`:500` 的面长无界条件由 `LeafAJSelect.exists_J_of_edge_unbounded`
（`LeafAJSelect.lean:321`）对 `A i` 给出，而 `hgrow_of_pinned_ccw`
（`LeafAJSelect.lean:631`）的第 6 个 binder 要的是对 `Â_i` 说的；差的正是本条。 -/
theorem faceLen_hatOf (A : ℕ → Set (ℤ × ℤ)) (kk : ℕ → ℕ) (vl ν : ℤ × ℤ) (i : ℕ) :
    faceLen (hatOf A kk vl i) ν = faceLen (A i) ν := by
  rw [hatOf_eq_shift, faceLen_shift]

/-! ## §3. `faceStart` 的唯一刻画（第二批的技术核心）

⚠ 第二批（§3–§5）与第一批（§1–§2）**形状不同**：`faceLen` / `E` 是**不变量**，
`faceStart` **不是不变量，是带位移的**，而且**不是定义性的**。

`faceStart`（`PolyChain.lean:71`）是
`if h : ∃ a ∈ face T ν, ∀ b ∈ face T ν, dot (dir ν) a ≤ dot (dir ν) b then h.choose else (0,0)`,
即 `dite` ＋ `Exists.choose`。`Exists.choose` 不是规范选择，平移前后两个 `choose` 之间
**没有任何定义性联系** ⟹ 必须先把 `faceStart` 从「某个极小点」钉成「那个极小点」。

唯一性成立的理由：`face T ν` 的任意两点相差 `dir ν` 的整数倍
（`exists_zsmul_dir_of_mem_face`，`RegionCut.lean:173`，要 `Prim ν`，由 `ν ∈ E T` 给出），
而 `dot (dir ν)` 沿该方向严格单调（`dot_dir_pos`，`PolyChain.lean:94`）⟹ 极小点唯一。

⚠ **`hfin` / `hν` 两条 binder 是必需的，不是保险**：脱掉任何一条，`faceStart` 落到
junk value `(0,0)`，等变性对 `v ≠ 0` 直接为假。 -/

/-- **`faceStart` 的唯一刻画。**  任何 `face T ν` 上的 `dot (dir ν)`-极小点就是 `faceStart T ν`。

证法：`exists_nat_shift_of_mem_face`（`PolyChain.lean:112`）把 `a` 写成
`faceStart T ν + t • dir ν` 且 `t : ℕ`；再用 `a` 的极小性压 `faceStart` 本身，得
`t * ⟪dir ν, dir ν⟫ ≤ 0`，而 `dot_dir_pos`（`PolyChain.lean:94`）给 `⟪dir ν, dir ν⟫ > 0`
⟹ `t = 0`。 -/
theorem faceStart_unique {T : Set (ℤ × ℤ)} {ν : ℤ × ℤ} (hfin : T.Finite) (hν : ν ∈ E T)
    {a : ℤ × ℤ} (ha : a ∈ face T ν)
    (hmin : ∀ b ∈ face T ν, dot (dir ν) a ≤ dot (dir ν) b) :
    faceStart T ν = a := by
  obtain ⟨t, ht⟩ := exists_nat_shift_of_mem_face hfin hν ha
  have hprimν : Prim ν := (mem_E_iff.mp hν).1
  have hD : 0 < dot (dir ν) (dir ν) := dot_dir_pos hprimν
  have hle := hmin _ (faceStart_mem hfin hν)
  have hexp : dot (dir ν) a
      = dot (dir ν) (faceStart T ν) + (t : ℤ) * dot (dir ν) (dir ν) := by
    rw [ht]
    simp only [dot, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  have hmul : (t : ℤ) * dot (dir ν) (dir ν) ≤ 0 := by linarith
  have ht0 : (t : ℤ) = 0 := by
    rcases eq_or_lt_of_le (Int.natCast_nonneg t) with h | h
    · exact h.symm
    · exact absurd hmul (not_le.mpr (mul_pos h hD))
  rw [ht, ht0, zero_smul, add_zero]

/-! ## §4. 一般的平移律：`faceStart` 随平移**整体位移**

⭐ 原文位置（硬规矩 5，本轮亲读，§50）：`b3_colle2.txt:488` 的**前半句**就是这条位移本身，
不只是 `Â_i` 的定义。逐字：

> let $k_{i}\in\mathbb{N}$ be such that the final point of
> $(A_{i}-k_{i}\vec{v}_{\boldsymbol{\ell}})\cap\boldsymbol{\ell}^{(-)}$ with respect to the
> orientation of $\boldsymbol{\ell}^{(-)}$ coincides with $g_{1}$

原文把「平移后集合的 final point」当作一个**关于 $k_i$ 的方程**来解。它之所以是 $k_i$ 的
方程，正因为「平移后的端点 ＝ 端点平移后」——右边随 $k_i$ 仿射地动。端点若不与平移等变，
那句话连方程都不是。⟹ §4–§5 是 `:488` 定义 $k_i$ 时**承重**的一步。

⚠ 诚实边界：原文**没有把这一步单独陈述成一句命题**，它隐含在 "let $k_i$ be such that"
的可解性里。不声称有逐字对应物。

⚠ **方向**（`NOTATION.md` 口径，别搞反）：原文取 **final point**（沿 $\ell^{(-)}$ 定向的
末端），Lean 的 `faceStart` 取 `dot (dir ν)`-**极小**点（**首端**）。所以原文的 $g_1$
对应的是和式 `faceStart T ν + (faceLen T ν : ℤ) • dir ν`（主仓散文叫 `faceEnd`，见
`ShellSubStrip.lean:710`、`PolyChain.lean:248`），**不是** `faceStart` 本身
⟹ 消费者要的是 `faceEnd_shift` / `faceEnd_hatOf`，`faceStart_shift` 是它们的上游。

⛔ `faceEnd` 主仓**没有 `def`**（声明头 grep 0 命中，只在散文里出现）。本文件
**不新立定义**（硬规矩 5：不立第三个名字），只借散文名当引理名，语句里把和式写全。 -/

/-- **`faceStart` 的平移等变性。**  `faceStart (shift v T) ν = faceStart T ν + v`。

与 `faceLen_shift`（§1）不同，这里**必须**带 `hfin` / `hν`（见 §3 的说明）。 -/
theorem faceStart_shift {T : Set (ℤ × ℤ)} {ν : ℤ × ℤ} (hfin : T.Finite) (hν : ν ∈ E T)
    (v : ℤ × ℤ) : faceStart (shift v T) ν = faceStart T ν + v := by
  have hfin' : (shift v T).Finite := by
    rw [shift_eq_image]; exact hfin.image _
  have hν' : ν ∈ E (shift v T) := by rw [E_shift]; exact hν
  refine faceStart_unique hfin' hν' ?_ ?_
  · rw [face_shift]
    show (faceStart T ν + v) - v ∈ face T ν
    simpa using faceStart_mem hfin hν
  · intro b hb
    rw [face_shift] at hb
    have hb' : b - v ∈ face T ν := hb
    have hmin := faceStart_min hfin hν _ hb'
    have e1 : dot (dir ν) (faceStart T ν + v)
        = dot (dir ν) (faceStart T ν) + dot (dir ν) v := dot_add _ _ _
    have e2 : dot (dir ν) (b - v) = dot (dir ν) b - dot (dir ν) v := dot_sub _ _ _
    omega

/-- **原文 `g_1` 侧的平移律**：末端（`faceStart + faceLen • dir`，主仓散文名 `faceEnd`，
本文件不为它立 `def`）同样随平移位移 `+v`。

`faceStart` 位移 `+v`（`faceStart_shift`）、`faceLen` 不动（`faceLen_shift`）。
这是 `b3_colle2.txt:488`「the final point of $(A_i - k_i\vec v_\ell)\cap\ell^{(-)}$ …
coincides with $g_1$」逐字对应的那一条。 -/
theorem faceEnd_shift {T : Set (ℤ × ℤ)} {ν : ℤ × ℤ} (hfin : T.Finite) (hν : ν ∈ E T)
    (v : ℤ × ℤ) :
    faceStart (shift v T) ν + (faceLen (shift v T) ν : ℤ) • dir ν
      = (faceStart T ν + (faceLen T ν : ℤ) • dir ν) + v := by
  rw [faceStart_shift hfin hν, faceLen_shift]
  abel

/-! ## §5. 专用到 `Â_i = A_i - k_i v⃗_ℓ`（`b3_colle2.txt:488`） -/

/-- **`faceStart (Â_i) ν = faceStart (A_i) ν - k_i • v⃗_ℓ`**（`b3_colle2.txt:488`）。

`hatOf_eq_shift`（`ChainAssemble.lean:327`）把 `Â_i` 写成 `shift (-(k_i) • v⃗_ℓ) (A_i)`，
再套 `faceStart_shift`。

⚠ binder 是对 `A i` 说的。手上若只有 `ν ∈ E (Â_i)`，用 §2 的 `E_hatOf` 换过来。 -/
theorem faceStart_hatOf {A : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ} {vl ν : ℤ × ℤ} {i : ℕ}
    (hfin : (A i).Finite) (hν : ν ∈ E (A i)) :
    faceStart (hatOf A kk vl i) ν = faceStart (A i) ν - (kk i : ℤ) • vl := by
  rw [hatOf_eq_shift, faceStart_shift hfin hν, neg_smul, ← sub_eq_add_neg]

/-- **`Â_i` 末端的平移律**——把「对 `Â_i` 说的末端」换成「对 `A_i` 说的末端 − k_i•v⃗_ℓ」。

消费者：lane-leafa-shell 的 `hg₁`（`tmp/wip/lane-leafa-shell-jdata.lean:49-63`），其左边
逐字是本条左边（`ν := ℓ`）。原文 `b3_colle2.txt:488` 的 `g_1` 条件即「`i` 变时本式左边
不动」。

⚠ 本条**不碰** `AItemFour.exists_endpoint_shift`（`AItemFour.lean:329`）的 `IsGreatest`
写法；「和式 ↔ `IsGreatest`」那一跳是消费者侧的开口，不在本文件里。 -/
theorem faceEnd_hatOf {A : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ} {vl ν : ℤ × ℤ} {i : ℕ}
    (hfin : (A i).Finite) (hν : ν ∈ E (A i)) :
    faceStart (hatOf A kk vl i) ν + (faceLen (hatOf A kk vl i) ν : ℤ) • dir ν
      = (faceStart (A i) ν + (faceLen (A i) ν : ℤ) • dir ν) - (kk i : ℤ) • vl := by
  rw [hatOf_eq_shift, faceEnd_shift hfin hν, neg_smul, ← sub_eq_add_neg]

end Nivat.HatShift

#print axioms Nivat.HatShift.faceLen_shift
#print axioms Nivat.HatShift.E_hatOf
#print axioms Nivat.HatShift.faceLen_hatOf
#print axioms Nivat.HatShift.faceStart_unique
#print axioms Nivat.HatShift.faceStart_shift
#print axioms Nivat.HatShift.faceEnd_shift
#print axioms Nivat.HatShift.faceStart_hatOf
#print axioms Nivat.HatShift.faceEnd_hatOf
