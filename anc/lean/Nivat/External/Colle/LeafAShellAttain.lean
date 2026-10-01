/-
Copyright (c) 2026. Released under Apache 2.0 license.
Authors: lane-leafa-shell
-/
-- ⚠ import 刻意取到最浅：本文件只用到 `det` / `dot` / `dir` / `dot_add`（`LatticeEdges`）与
-- `Nivat.ColleReg.dot_zsmul_right`（`Claim47Core`）。原先 import 消费者所在的
-- `ShellSubStrip` 那条线时闭包 132 个模块里含着当轮正在改的模块，`contenthash.py` 报 DRIFT，
-- 按工具盲区 1 那样的 EXIT=0 只证明「对着旧 olean 能过」。现在的闭包与 shell 组以外的
-- lane 改动解耦，收据可独立复核。
import Nivat.External.Colle.Claim47Core

/-!
# `hattain` and `0 ≤ D` are **one** unknown, not two

Lane `lane-leafa-shell`, 2026-09-25（第 227 轮）。

## §0  本文件回答什么

`shellEnv` 的装配式 `shellEnv_of_faceSeg_hD`（`tmp/wip/lane-leafa-shell-shellenv.lean` §50）
把交付面压到一张 binder 表，其中 §50 (1) 记了三条「继承自 `shellEnv_of_wedge`」的欠账
`hlcT` / `hattain` / `hwedgeF`，而 §50 的正文把 `hD : 0 ≤ det ν_{J−1} ν_{J+1}` 列为
「唯一残项」。**这两处记账把 `hattain` 和 `hD` 当成互相独立的两条债。本文件证明它们是一条。**

逐条（下面每条都是本文件的 0-sorry 声明，等级 [内核]）：

* `wedge_false_of_D_eq_zero`：`D = 0` ⟹ `hattain` 的**前提锥为空** ⟹ 该字段空真；
* `dot_vJ_neg_of_D_pos`：`0 < D` ⟹ 锥内每个 `n` 都有 `⟪n, v_J⟫ < 0`
  （即「塔沿 `v_J` 的复发方向压不破上界」这条**必要**条件成立）；
* `not_attain_of_dot_vJ_pos`：`0 < ⟪n, v_J⟫` ＋ `rec_vJ` ⟹ 该 `n` 上**没有**上确界点
  （塔对 `+v_J` 封闭，任何候选点加一步就更高）；
* `D_nonneg_of_hattain`：⟹ **`hattain` 蕴含 `0 ≤ D`**，且**不带**「锥非空」前提——`D < 0`
  那一支的锥内见证点由 `wedge_witness_of_D_neg` **造出**（`n₀ := dir v_{J−1}`，§104）；
* `dot_x_nonpos_of_dets`（§3）：上确界**存在**那一半要的是「锥内 `⟪n,x⟫ ≤ 0` 对塔的每条
  recession 方向 `x`」，本条把它化成两个行列式条件，`x := p` 那一支的残余就此命名到位。
* `k_nonneg_of_hattain` / `k_pos_of_hattain` / `not_hattain_of_k_neg`（§6）：`0 < D` 之下
  `hattain` **推出** `vJ` 的朝向 `0 < k` —— 朝向不是待裁前提，见证点 `n₀ := ν_{J−1}` 是造的；
* `k_neg_of_det_p_vJ_pos` / `not_hattain_of_vjsign_choice`（§7）：洞 1 ℓ 侧选的符号
  `0 < det p vJ` 迫使 `k < 0` ⟹ **让 `hattain` 为假**。两个洞要求相反的朝向，这是分叉
  不是矛盾（符号是我们自己从 `IsRegion` 删掉的量词）；
* `bddAbove_of_two_walls`（§4b）：`hattain` **充分性**那一半的工具 —— 两道 `i`-无关的墙
  给出显式上界，对集合零假设。

⟹ 结论（本文件的全部内容）：在 `he` / `hd` / `rec_vJ` 这三条链上现货之下，
**`0 ≤ D` 是 `hattain` 的必要条件，`D = 0` 让 `hattain` 空真，`0 < D` 兑现 `hattain` 的
那一半必要条件**。所以「先把 `hattain` 做掉、`hD` 另派人」这种排法拿不到任何东西：
`hattain` 一旦为真，`0 ≤ D` 就已经被证出来了。

## §1  Cramer 恒等式那一步（为什么符号是这样）

`cramer_dot_attain`（纯 `ring`）：对任意 `n a b x`，

    det a b * ⟪n,x⟫ = det x b * ⟪n,a⟫ + det a x * ⟪n,b⟫.

在调用点代入 `a := w = -(dir ν_{J+1})`、`b := v_{J−1} = dir ν_{J−1}`、`x := dir J`，
三个行列式逐个化掉（`det_right_dir` / `det_dir_dir_eq`）：

| 位置 | 值 | 依据 |
|---|---|---|
| `det a b` | `det ν_{J−1} ν_{J+1} = D` | `det (dir p) (dir q) = det p q`，两次取负 |
| `det x b` | `det J ν_{J−1} = −e` | 同上，`e := det ν_{J−1} J` |
| `det a x` | `det J ν_{J+1} = d` | 同上，`d := det J ν_{J+1}` |

于是 **`D * ⟪n, dir J⟫ = −e * ⟪n,w⟫ + d * ⟪n,v_{J−1}⟫`**（`D_mul_dot_dir_J`）。
`hattain` 的锥条件是 `0 < ⟪n,w⟫` 与 `⟪n,v_{J−1}⟫ ≤ 0`，配 `0 < e`（`hsweep` 侧）与
`0 < d`（`hsweepW` 侧）⟹ 右端 **严格负**。三分立刻出来，`D` 的符号就是全部内容。

## §2  `v_J` 与 `dir J` 的朝向是**前提**，不是本文件的结论

`hvJ : vJ = k • dir J` 带 `0 < k` 是一条 binder，**不是**这里证出来的。链上现货只有
`dot nJ vJ = 0`（`F.dot_nJ_vJ`）＋ `vJ ≠ 0`，它们只给 `vJ ∥ dir J`，**不定符号**
（`dir (-J) = -dir J`）。按常设闸门「带符号的 `det vl w` / `det vJ1 w` 结论两个方向都不许搬」，
本文件把朝向明写成 binder：取 `k < 0` 时下面每条结论里 `dot n vJ` 的符号整体翻转，
`D_nonneg_of_hattain` 就变成 `D ≤ 0`。**谁在调用点兑现 `hvJ`，谁负责那个符号。**

⚠ **§6 把这一段大部分撤回了。** 上面「朝向是一条要从原文裁的自由前提」在 `0 < D` 之下**不**成立：
§6 的 `k_nonneg_of_hattain` 从 `hattain` ＋ `rec_vJ` ＋ `0 < D` **推出** `0 ≤ k`。
朝向与「`hattain` 可证」是同一个比特，不是两件要分别裁的事。仍然为真的部分是：
本文件 §2 / §4 的那几条声明自己确实把 `hvJ` 当 binder 收，签名不变。

## §3  本文件没有主张什么

* **不**主张 `0 ≤ D` 为真（那是 `scratch/b3_colle2.txt:432` 的边序窗口，已派
  lane-hole3-nlmax，主仓 `DNonnegWindow.lean` 是那条线）。本文件只说 `hattain` 不比它便宜。
* **不**主张 `hattain` 在 `0 < D` 下为真：`0 < D` 只给「锥内 `⟪n,v_J⟫ < 0`」这条**必要**
  条件，上确界**存在**还要塔的**另一条** recession 方向 `p`（`rec_p`）也被压住，以及塔在
  `ℓ_ι` 那一侧的墙（`ahat_halfPlane_L`，`ChainGeom.lean:180`）。`p` 那一条 §3 的
  `dot_x_nonpos_of_dets` 化成了 `det p v_{J−1} ≤ 0 ∧ 0 ≤ det w p`，即带符号的
  `det vl v_{J−1}` 与 `det w vl` —— **那两个符号本文件一个都不主张**（常设闸门）。
* **不**碰 `hD` 的正面路线（§52 的 `D_nonneg_of_adjacent` 已冻结）。
* 空真的风险只在 `D = 0` 那一支，并且本文件把它**指名**（`wedge_empty_of_D_eq_zero`）：
  在 `D = 0` 的台架上量到「`hattain` 成立」买不到任何东西（§41）。`D ≠ 0` 支锥必非空。

## §4  原文对应

没有新 `Prop`。`hattain` 逐字取自 `shellEnv_of_wedge` 的 binder（同文件 §10），
`d` / `e` / `D` 三个行列式的原文出处是 `scratch/b3_colle2.txt:432`（边序窗口）与
`:518`（`w = −v_{ℓ_{J+1}}`、`v_{ℓ_{J−1}}` 的取法），与 §50 的登记逐字相同，不新增量词。
`rec_vJ` 是 `ChainDataGeom` 第 25 条字段（`ChainGeom.lean`，主仓已有生产者
`LaneLeafAGenRecVJ.rec_vJ_of_parts`）。
-/

set_option autoImplicit false

namespace Nivat.LaneLeafAShellAttain

open Nivat Nivat.LE2 Nivat.MaxEnv Nivat.Colle35

/-! ## §1.  Three `ring` identities -/

/-- **2 维 Cramer 恒等式，点积形。**  `det a b • x = det x b • a + det a x • b` 与 `n` 作点积。
纯 `ring`，不需要 `a`、`b` 独立。 -/
theorem cramer_dot_attain (n a b x : ℤ × ℤ) :
    det a b * dot n x = det x b * dot n a + det a x * dot n b := by
  simp only [det, dot]
  ring

/-- `det a (dir b) = ⟪a, b⟫`.  （主仓 `HsuppRoomCone.dot_dir_eq_det` 是参数翻过来的版本；
这里就地证，避免新增 import。） -/
theorem det_right_dir (a b : ℤ × ℤ) : det a (dir b) = dot a b := by
  simp only [det, dot, dir]
  ring

/-- `det (dir a) (dir b) = det a b`：旋转保行列式。 -/
theorem det_dir_dir_eq (a b : ℤ × ℤ) : det (dir a) (dir b) = det a b := by
  simp only [det, dir]
  ring

/-- `⟪dir a, b⟫ = det a b`.  （主仓 `LaneHole3Nlmax.dot_dir_eq_det_left`（`DNonnegWindow.lean:39`）
是同一条；就地证，避免新增 import。）这一条是 §4 里**造出**锥内见证点的全部内容。 -/
theorem dot_dir_left_eq_det (a b : ℤ × ℤ) : dot (dir a) b = det a b := by
  simp only [det, dot, dir]
  ring

/-- `dir (dir x) = -x`：两次旋转是中心对称。§4 的见证点因此**是一个法向的反号**，
不是随便一个向量——见 `wedge_witness_is_neg_nprevJ`。 -/
theorem dir_dir_attain (x : ℤ × ℤ) : dir (dir x) = -x := by
  ext <;> simp only [dir, Prod.fst_neg, Prod.snd_neg, neg_neg]

/-! ## §2.  The sign law on the `hattain` cone -/

/-- **`D * ⟪n, dir J⟫ = −e * ⟪n, w⟫ + d * ⟪n, v_{J−1}⟫`**，`D = det ν_{J−1} ν_{J+1}`、
`e = det ν_{J−1} J`、`d = det J ν_{J+1}`。§1 的三条恒等式加一次 `cramer_dot_attain`。 -/
theorem D_mul_dot_dir_J {nprevJ J νJ1 vJ1 w n : ℤ × ℤ}
    (hv : vJ1 = dir nprevJ) (hw : w = -(dir νJ1)) :
    det nprevJ νJ1 * dot n (dir J) =
      -(det nprevJ J) * dot n w + det J νJ1 * dot n vJ1 := by
  subst hv
  subst hw
  have hkey := cramer_dot_attain n (-(dir νJ1)) (dir nprevJ) (dir J)
  have hab : det (-(dir νJ1)) (dir nprevJ) = det nprevJ νJ1 := by
    simp only [det, dir, Prod.fst_neg, Prod.snd_neg, Prod.neg_mk]; ring
  have hxb : det (dir J) (dir nprevJ) = -(det nprevJ J) := by
    simp only [det, dir]; ring
  have hax : det (-(dir νJ1)) (dir J) = det J νJ1 := by
    simp only [det, dir, Prod.fst_neg, Prod.snd_neg, Prod.neg_mk]; ring
  rw [hab, hxb, hax] at hkey
  exact hkey

/-- **`D = 0` ⟹ `hattain` 的前提锥为空。**  `0 < ⟪n,w⟫` 与 `⟪n,v_{J−1}⟫ ≤ 0` 在
`D = 0`、`0 < e`、`0 < d` 之下不可同时成立 —— 于是那一版 `hattain` 空真。 -/
theorem wedge_false_of_D_eq_zero {nprevJ J νJ1 vJ1 w n : ℤ × ℤ}
    (hv : vJ1 = dir nprevJ) (hw : w = -(dir νJ1))
    (he : 0 < det nprevJ J) (hd : 0 < det J νJ1)
    (hD : det nprevJ νJ1 = 0)
    (hwedge : 0 < dot n w) (hnv : dot n vJ1 ≤ 0) : False := by
  have hkey := D_mul_dot_dir_J (J := J) hv hw (n := n)
  rw [hD, zero_mul] at hkey
  nlinarith [mul_pos he hwedge, mul_nonpos_of_nonneg_of_nonpos hd.le hnv]

/-- **`0 < D` ⟹ 锥内每个 `n` 都有 `⟪n, v_J⟫ < 0`**，其中 `vJ = k • dir J`、`0 < k`
（朝向是 binder，见 §2）。这是 `hattain` 的**必要**条件的那一半，不是 `hattain` 本身。 -/
theorem dot_vJ_neg_of_D_pos {nprevJ J νJ1 vJ1 w vJ n : ℤ × ℤ} {k : ℤ}
    (hv : vJ1 = dir nprevJ) (hw : w = -(dir νJ1))
    (hk : 0 < k) (hvJ : vJ = k • dir J)
    (he : 0 < det nprevJ J) (hd : 0 < det J νJ1)
    (hD : 0 < det nprevJ νJ1)
    (hwedge : 0 < dot n w) (hnv : dot n vJ1 ≤ 0) : dot n vJ < 0 := by
  have hkey := D_mul_dot_dir_J (J := J) hv hw (n := n)
  have hneg : det nprevJ νJ1 * dot n (dir J) < 0 := by
    rw [hkey]
    nlinarith [mul_pos he hwedge, mul_nonpos_of_nonneg_of_nonpos hd.le hnv]
  have hdirneg : dot n (dir J) < 0 := by
    by_contra hcon
    push_neg at hcon
    nlinarith [mul_nonneg hD.le hcon]
  have hexp : dot n vJ = k * dot n (dir J) := by
    rw [hvJ, Nivat.ColleReg.dot_zsmul_right]
  rw [hexp]
  exact mul_neg_of_pos_of_neg hk hdirneg

/-- **`D < 0` ⟹ 锥内每个 `n` 都有 `0 < ⟪n, v_J⟫`**（同一条恒等式的另一支）。 -/
theorem dot_vJ_pos_of_D_neg {nprevJ J νJ1 vJ1 w vJ n : ℤ × ℤ} {k : ℤ}
    (hv : vJ1 = dir nprevJ) (hw : w = -(dir νJ1))
    (hk : 0 < k) (hvJ : vJ = k • dir J)
    (he : 0 < det nprevJ J) (hd : 0 < det J νJ1)
    (hD : det nprevJ νJ1 < 0)
    (hwedge : 0 < dot n w) (hnv : dot n vJ1 ≤ 0) : 0 < dot n vJ := by
  have hkey := D_mul_dot_dir_J (J := J) hv hw (n := n)
  have hneg : det nprevJ νJ1 * dot n (dir J) < 0 := by
    rw [hkey]
    nlinarith [mul_pos he hwedge, mul_nonpos_of_nonneg_of_nonpos hd.le hnv]
  have hdirpos : 0 < dot n (dir J) := by
    by_contra hcon
    push_neg at hcon
    nlinarith [mul_nonneg (neg_nonneg.mpr hD.le) (neg_nonneg.mpr hcon)]
  have hexp : dot n vJ = k * dot n (dir J) := by
    rw [hvJ, Nivat.ColleReg.dot_zsmul_right]
  rw [hexp]
  exact mul_pos hk hdirpos

/-! ## §3.  A `+vJ`-recurrent tower has no `n`-maximiser when `0 < ⟪n, vJ⟫` -/

/-- **§2 的一般形：把 `dir J` 换成任意 `x`。**  `hattain` 的上确界**存在**那一半要的是
「锥内 `⟪n, x⟫ ≤ 0` 对塔的**每条** recession 方向 `x` 成立」，而塔已知的 recession 方向有两条：
`v_J`（`rec_vJ`，第 25 条字段）与 `p`（`rec_p`，`p = -(c:ℤ)•vl`，`c > 0`）。本条一次给出判据。 -/
theorem D_mul_dot_general {nprevJ νJ1 vJ1 w n x : ℤ × ℤ}
    (hv : vJ1 = dir nprevJ) (hw : w = -(dir νJ1)) :
    det nprevJ νJ1 * dot n x = det x vJ1 * dot n w + det w x * dot n vJ1 := by
  have hkey := cramer_dot_attain n w vJ1 x
  have hab : det w vJ1 = det nprevJ νJ1 := by
    subst hv; subst hw
    simp only [det, dir, Prod.fst_neg, Prod.snd_neg, Prod.neg_mk]; ring
  rw [hab] at hkey
  exact hkey

/-- **锥内 `⟪n, x⟫ ≤ 0` 的判据（`0 < D` 支）**：两条行列式条件，逐条按 `x` 报。
对 `x := v_J` 它们是 `det v_J v_{J−1} ≤ 0` 与 `0 ≤ det w v_J`（由 `he` / `hd` 兑现，见 §2）；
对 `x := p = -(c:ℤ)•vl` 它们是 `det p v_{J−1} ≤ 0` 与 `0 ≤ det w p`，即**带符号的
`det vl v_{J−1}` 与 `det w vl`** —— 那两个符号按常设闸门本文件**不主张**，只把残余命名到这里。 -/
theorem dot_x_nonpos_of_dets {nprevJ νJ1 vJ1 w n x : ℤ × ℤ}
    (hv : vJ1 = dir nprevJ) (hw : w = -(dir νJ1))
    (hD : 0 < det nprevJ νJ1)
    (hxv : det x vJ1 ≤ 0) (hwx : 0 ≤ det w x)
    (hwedge : 0 < dot n w) (hnv : dot n vJ1 ≤ 0) : dot n x ≤ 0 := by
  have hkey := D_mul_dot_general (x := x) (n := n) hv hw
  have hle : det nprevJ νJ1 * dot n x ≤ 0 := by
    rw [hkey]
    have h1 : det x vJ1 * dot n w ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hxv hwedge.le
    have h2 : det w x * dot n vJ1 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hwx hnv
    linarith
  by_contra hcon
  push_neg at hcon
  nlinarith [mul_pos hD hcon]

/-- **`rec_vJ` 杀掉上确界点。**  塔对 `+v_J` 封闭，若 `0 < ⟪n,v_J⟫` 则任何候选上确界点
`z` 加一步就更高 ⟹ 该 `n` 上没有上确界点。零几何内容。 -/
theorem not_attain_of_dot_vJ_pos {R : ℕ → Set (ℤ × ℤ)} {n vJ : ℤ × ℤ} {i : ℕ}
    (hrec : ∀ g ∈ (⋃ j, R j), g + vJ ∈ ⋃ j, R j)
    (hpos : 0 < dot n vJ) :
    ¬ (∃ z ∈ R i, ∀ g ∈ (⋃ j, R j), dot n g ≤ dot n z) := by
  rintro ⟨z, hz, hmax⟩
  have hzU : z ∈ ⋃ j, R j := Set.mem_iUnion.mpr ⟨i, hz⟩
  have hstep := hmax _ (hrec z hzU)
  rw [dot_add] at hstep
  linarith

/-! ## §4.  ⟹ `hattain` 蕴含 `0 ≤ D` -/

/-- **锥内见证点是造出来的，不是假设的**（§104）：`D ≠ 0` 时 `n₀ := dir v_{J−1}` 满足
`⟪n₀, v_{J−1}⟫ = 0`（自动 `≤ 0`）与 `⟪n₀, w⟫ = −D`。⟹ `D < 0` 那一支锥必非空。 -/
theorem wedge_witness_of_D_neg {nprevJ νJ1 vJ1 w : ℤ × ℤ}
    (hv : vJ1 = dir nprevJ) (hw : w = -(dir νJ1))
    (hD : det nprevJ νJ1 < 0) :
    0 < dot (dir vJ1) w ∧ dot (dir vJ1) vJ1 ≤ 0 := by
  constructor
  · have hval : dot (dir vJ1) w = -(det nprevJ νJ1) := by
      subst hv
      subst hw
      simp only [dot, det, dir, Prod.fst_neg, Prod.snd_neg, Prod.neg_mk]
      ring
    rw [hval]
    linarith
  · have h0 : dot (dir vJ1) vJ1 = 0 := by
      rw [dot_dir_left_eq_det]
      simp only [det]
      ring
    rw [h0]

/-- **见证点是一个法向的反号，不是随便一个向量**：`dir v_{J−1} = dir (dir ν_{J−1}) = −ν_{J−1}`。

⟹ 若有人把 `hattain` 的 `∀ n : ℤ × ℤ` **收窄**成 `∀ n ∈ E ↑𝒮_φ`（lane-leafa-gen 的
`LeafAGenAttain.lean` 按 `Finset` 收窄那一版），本文件的蕴含**照样成立**：见证点
`−ν_{J−1}` 由 `E` 的反号对称性落在收窄后的范围里。这一条就是那个兼容性。 -/
theorem wedge_witness_is_neg_nprevJ {nprevJ vJ1 : ℤ × ℤ} (hv : vJ1 = dir nprevJ) :
    dir vJ1 = -nprevJ := by
  rw [hv, dir_dir_attain]

/-- **交付面的一般形：`hattain` 的量词可以被任何谓词 `P` 收窄，只要 `P (−ν_{J−1})`。**
`P := fun _ => True` 给 `D_nonneg_of_hattain`；`P := (· ∈ E ↑𝒮_φ)` 给 gen 那一版，
其 `hP` 由 `E` 的反号对称性兑现。 -/
theorem D_nonneg_of_hattain_restricted {R : ℕ → Set (ℤ × ℤ)} {P : ℤ × ℤ → Prop}
    {nprevJ J νJ1 vJ1 w vJ : ℤ × ℤ} {k : ℤ} {i₀ : ℕ}
    (hv : vJ1 = dir nprevJ) (hw : w = -(dir νJ1))
    (hk : 0 < k) (hvJ : vJ = k • dir J)
    (he : 0 < det nprevJ J) (hd : 0 < det J νJ1)
    (hrec : ∀ g ∈ (⋃ j, R j), g + vJ ∈ ⋃ j, R j)
    (hP : P (-nprevJ))
    (hattain : ∀ i, i₀ ≤ i → ∀ m : ℤ × ℤ, P m → 0 < dot m w → dot m vJ1 ≤ 0 →
      ∃ z ∈ R i, ∀ g ∈ (⋃ j, R j), dot m g ≤ dot m z) :
    0 ≤ det nprevJ νJ1 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨hwedge, hnv⟩ := wedge_witness_of_D_neg hv hw hcon
  rw [wedge_witness_is_neg_nprevJ hv] at hwedge hnv
  exact not_attain_of_dot_vJ_pos (i := i₀) hrec
    (dot_vJ_pos_of_D_neg hv hw hk hvJ he hd hcon hwedge hnv)
    (hattain i₀ le_rfl (-nprevJ) hP hwedge hnv)

/-- **本文件的交付面：`hattain` ⟹ `0 ≤ D`，锥非空那条 binder 也去掉了。**

`hattain` 逐字取自 `shellEnv_of_wedge`（`tmp/wip/lane-leafa-shell-shellenv.lean` §10）的
binder；`hrec` 是 `ChainDataGeom` 第 25 条字段 `rec_vJ`；`he` / `hd` 是链上现货
（`hsweep` / `hsweepW`）；`hvJ` 是 §2 的朝向 binder。**没有「锥非空」前提**：`D < 0` 那一支
的见证点由 `wedge_witness_of_D_neg` 造出（§104：正控必须是造出来的）。

⟹ 排工结论：`hattain` **不**是一条可以绕开 `0 ≤ D` 单独兑现的债。 -/
theorem D_nonneg_of_hattain {R : ℕ → Set (ℤ × ℤ)}
    {nprevJ J νJ1 vJ1 w vJ : ℤ × ℤ} {k : ℤ} {i₀ : ℕ}
    (hv : vJ1 = dir nprevJ) (hw : w = -(dir νJ1))
    (hk : 0 < k) (hvJ : vJ = k • dir J)
    (he : 0 < det nprevJ J) (hd : 0 < det J νJ1)
    (hrec : ∀ g ∈ (⋃ j, R j), g + vJ ∈ ⋃ j, R j)
    (hattain : ∀ i, i₀ ≤ i → ∀ m : ℤ × ℤ, 0 < dot m w → dot m vJ1 ≤ 0 →
      ∃ z ∈ R i, ∀ g ∈ (⋃ j, R j), dot m g ≤ dot m z) :
    0 ≤ det nprevJ νJ1 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨hwedge, hnv⟩ := wedge_witness_of_D_neg hv hw hcon
  exact not_attain_of_dot_vJ_pos (i := i₀) hrec
    (dot_vJ_pos_of_D_neg hv hw hk hvJ he hd hcon hwedge hnv)
    (hattain i₀ le_rfl (dir vJ1) hwedge hnv)

/-- **同一条，`D = 0` 那一支说得更狠**：`hattain` 的锥在 `D = 0` 上是空的，所以
「`hattain` 已证」在 `D = 0` 的台架上**什么都没买到**（§41 的空真）。 -/
theorem wedge_empty_of_D_eq_zero {nprevJ J νJ1 vJ1 w : ℤ × ℤ}
    (hv : vJ1 = dir nprevJ) (hw : w = -(dir νJ1))
    (he : 0 < det nprevJ J) (hd : 0 < det J νJ1)
    (hD : det nprevJ νJ1 = 0) :
    ∀ n : ℤ × ℤ, ¬ (0 < dot n w ∧ dot n vJ1 ≤ 0) := by
  intro n ⟨h1, h2⟩
  exact wedge_false_of_D_eq_zero (J := J) hv hw he hd hD h1 h2

/-! ## §4b.  上确界**存在**那一半：两堵墙给出有界性

`hattain` 的另一半是「`⟪n,·⟫` 在塔上有上界」。塔被**两堵**对 `i` 一致的墙夹住
（`CORE-HOLES.md` 常设纪律 #7：`ℓ_J` 那堵不是唯一的一堵）：

* `hhp` / `ahat_halfPlane`：`c_J ≤ ⟪n_J, ·⟫`；
* `ahat_halfPlane_L`（`ChainGeom.lean:180`，team-lead 第 226 轮报「主仓早有生产者
  `nfp_L_of_preamble_and_exhausts`」）：`c_ℓ ≤ ⟪n_ℓ, ·⟫`。

两堵墙围出一个**尖锥**，`⟪n,·⟫` 在尖锥上有上界 ⟺ `n` 对锥的两条 recession 射线都非正。
下面这条把它做成内核判据，**没有几何前提**：只用两堵墙 ＋ 一个 Cramer 恒等式。
配 lane-leafa-gen 的 `LeafAGenAttain.exists_uniform_attain_of_bddAbove`（主仓新模块，
按 `Finset` 收窄那一版）就是 `hattain` 本身。

⚠ **朝向**：`hδ : 0 < det m1 m2` 是**给这对墙定序**的前提，不是几何断言。调用点若
`vJ ∥ -(dir n_J)` 真是塔的 recession 方向，那么 `det n_J n_ℓ < 0`，正确的代入是
`(m1, m2) := (n_ℓ, n_J)`。本文件**不主张**那个符号（常设闸门），只把两种代入都留给调用方。 -/

/-- **两堵墙的 Cramer 恒等式**：`det m1 m2 * ⟪n,z⟫ = −⟪m1,z⟫·⟪n, dir m2⟫ + ⟪m2,z⟫·⟪n, dir m1⟫`。
纯 `ring`。 -/
theorem two_wall_identity (m1 m2 n z : ℤ × ℤ) :
    det m1 m2 * dot n z =
      -(dot m1 z) * dot n (dir m2) + (dot m2 z) * dot n (dir m1) := by
  simp only [det, dot, dir]
  ring

/-- **有界性判据**：被两堵墙 `c1 ≤ ⟪m1,·⟫`、`c2 ≤ ⟪m2,·⟫` 夹住的任意集合上，若 `n` 对锥的
两条 recession 射线都非正（`⟪n, dir m1⟫ ≤ 0` 与 `0 ≤ ⟪n, dir m2⟫`），则 `⟪n,·⟫` 有上界，
上界显式给出。**对 `T` 零假设**——不要求凸、不要求有限、不要求非空。 -/
theorem bddAbove_of_two_walls {T : Set (ℤ × ℤ)} {m1 m2 n : ℤ × ℤ} {c1 c2 : ℤ}
    (hδ : 0 < det m1 m2)
    (hw1 : ∀ z ∈ T, c1 ≤ dot m1 z) (hw2 : ∀ z ∈ T, c2 ≤ dot m2 z)
    (hr1 : dot n (dir m1) ≤ 0) (hr2 : 0 ≤ dot n (dir m2)) :
    ∃ M : ℤ, ∀ z ∈ T, dot n z ≤ M := by
  refine ⟨max (-c1 * dot n (dir m2) + c2 * dot n (dir m1)) 0, ?_⟩
  intro z hz
  have hkey := two_wall_identity m1 m2 n z
  have h1 : -(dot m1 z) * dot n (dir m2) ≤ -c1 * dot n (dir m2) := by
    have := hw1 z hz
    nlinarith
  have h2 : dot m2 z * dot n (dir m1) ≤ c2 * dot n (dir m1) := by
    have := hw2 z hz
    nlinarith
  have hbound : det m1 m2 * dot n z ≤ -c1 * dot n (dir m2) + c2 * dot n (dir m1) := by
    rw [hkey]; linarith
  rcases le_or_gt (dot n z) 0 with hle | hpos
  · exact le_trans hle (le_max_right _ _)
  · have hδ1 : (1 : ℤ) ≤ det m1 m2 := hδ
    have : dot n z ≤ det m1 m2 * dot n z := le_mul_of_one_le_left hpos.le hδ1
    exact le_trans (le_trans this hbound) (le_max_left _ _)

/-! ## §5.  硬规矩 6：一个数值实例（rig A 的三条行列式）

`ν_{J−1} = (1,0)`、`ν_J = J = (0,1)`、`ν_{J+1} = (−2,1)`（§50 `rigA_hD_supply` 的同一组）：
`e = det (1,0) (0,1) = 1 > 0`、`d = det (0,1) (−2,1) = 2 > 0`、`D = det (1,0) (−2,1) = 1 > 0`。
于是 `dir J = (−1,0)`，锥 `{n : 0 < ⟪n,w⟫, ⟪n,v_{J−1}⟫ ≤ 0}` 里取 `n = (−1,−1)`：
`w = -(dir (−2,1)) = -((-1,-2)) = (1,2)`，`⟪n,w⟫ = −1−2 = −3`，**不在锥里**；
取 `n = (1,0)`：`⟪n,w⟫ = 1 > 0`，`v_{J−1} = dir (1,0) = (0,1)`，`⟪n,v_{J−1}⟫ = 0 ≤ 0` ✓ 在锥里，
而 `⟪n, dir J⟫ = ⟪(1,0),(−1,0)⟫ = −1 < 0` —— 与 `dot_vJ_neg_of_D_pos` 在 `0 < D` 下的结论一致。
下面这条把这三个数字兑成内核等式（锥非空 ⟹ §41 的守卫在 rig A 上**正面**兑现）。 -/

theorem rigA_wedge_nonempty :
    0 < det ((1 : ℤ), (0 : ℤ)) ((0 : ℤ), (1 : ℤ)) ∧
      0 < det ((0 : ℤ), (1 : ℤ)) ((-2 : ℤ), (1 : ℤ)) ∧
      0 < det ((1 : ℤ), (0 : ℤ)) ((-2 : ℤ), (1 : ℤ)) ∧
      0 < dot ((1 : ℤ), (0 : ℤ)) (-(dir ((-2 : ℤ), (1 : ℤ)))) ∧
      dot ((1 : ℤ), (0 : ℤ)) (dir ((1 : ℤ), (0 : ℤ))) ≤ 0 ∧
      dot ((1 : ℤ), (0 : ℤ)) (dir ((0 : ℤ), (1 : ℤ))) < 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [det, dot, dir]

/-! ## §6.  `0 < D` 支的锥内见证点是**造出来的**，朝向因此不再是待裁前提

lane-env-refute 本轮把 `0 < D` 做成了无前提的主仓结论
（`Nivat.CyclicOrderDPos.D_pos_of_window_of_transversal`，该 lane 报 EXIT=0 ＋ 公理白名单，
集成者报 `BUILD_RC=0`；**我未复核其证明体**）。在 `0 < D` 之下：

* 锥 `{n : 0 < ⟪n,w⟫ ∧ ⟪n,v_{J−1}⟫ ≤ 0}` **非空**，而且见证点不是「找出来的」而是
  **写下来的**：`n₀ := ν_{J−1}` 自己。`dir w = ν_{J+1}` ⟹ `⟪ν_{J−1}, w⟫ = D > 0`；
  `⟪ν_{J−1}, dir ν_{J−1}⟫ = 0` 是恒等式。
  （§104：正控必须构造，并写清什么时候不再命中。**失效点**：`⟪n₀,w⟫ = D` 这个等式本身就是
  哨兵——`D ≤ 0` 时这条见证点立刻不命中，`D < 0` 支要换成 `wedge_witness_of_D_neg` 的
  `dir v_{J−1} = -ν_{J−1}`，`D = 0` 时锥真的是空的（`wedge_empty_of_D_eq_zero`）。）
* 在这个 `n₀` 上 §2 的恒等式塌成 `D * ⟪n₀, dir J⟫ = -e * D`，约掉 `0 < D` 得
  **`⟪n₀, dir J⟫ = -e < 0`**（`dot_dir_J_at_nprevJ`）。

⟹ `k_nonneg_of_hattain`：`hattain` ＋ `rec_vJ` ＋ `0 < D` ＋ `0 < e` **推出** `0 ≤ k`；
配链上的 `vJ ≠ 0`（`Primitive vJ` 的第一合取）得 `k_pos_of_hattain : 0 < k`。
逆否形是 `not_hattain_of_k_neg`：朝向若是另一支，`hattain` 这个字段**为假**，
`shellEnv` 那条路线整条死。**两个答案都不需要读 `b3_colle2.txt`。**

⚠ 这**不**是「朝向为真」的证明（§54：没碰 ≠ 假）。它是把「朝向」与「`hattain` 可证」绑成
同一个比特：谁兑现 `hattain`，谁顺带兑现了 `0 < k`；谁证明 `k < 0`，谁顺带否掉了 `hattain`。
本节不引入新 `Prop`，`hattain` / `rec_vJ` 逐字仍是 §0 登记的那两条。 -/

/-- **`0 < D` 支的锥内见证点，造出来的**：`n₀ := ν_{J−1}` 本身。第二合取是恒等式（`= 0`，
比锥要的 `≤ 0` 强），所以这条见证点对 `⟪n,v_{J−1}⟫ ≤ 0` 是**边界上**的点。 -/
theorem wedge_witness_of_D_pos {nprevJ νJ1 vJ1 w : ℤ × ℤ}
    (hv : vJ1 = dir nprevJ) (hw : w = -(dir νJ1)) (hD : 0 < det nprevJ νJ1) :
    0 < dot nprevJ w ∧ dot nprevJ vJ1 = 0 := by
  refine ⟨?_, ?_⟩
  · have hval : dot nprevJ w = det nprevJ νJ1 := by
      subst hw
      simp only [dot, det, dir, Prod.fst_neg, Prod.snd_neg, Prod.neg_mk]
      ring
    rw [hval]
    exact hD
  · subst hv
    simp only [dot, dir]
    ring

/-- **在那个见证点上 `⟪n₀, dir J⟫ = −e`。**  §2 的恒等式在 `n := ν_{J−1}` 处两项都塌：
`⟪n₀,w⟫` 变成 `D`、`⟪n₀,v_{J−1}⟫` 变成 `0`，剩下的 `D` 可以约掉。 -/
theorem dot_dir_J_at_nprevJ {nprevJ J νJ1 vJ1 w : ℤ × ℤ}
    (hv : vJ1 = dir nprevJ) (hw : w = -(dir νJ1)) (hD : det nprevJ νJ1 ≠ 0) :
    dot nprevJ (dir J) = -(det nprevJ J) := by
  have hkey := D_mul_dot_dir_J (n := nprevJ) (J := J) hv hw
  have h1 : dot nprevJ w = det nprevJ νJ1 := by
    subst hw
    simp only [dot, det, dir, Prod.fst_neg, Prod.snd_neg, Prod.neg_mk]
    ring
  have h2 : dot nprevJ vJ1 = 0 := by
    subst hv
    simp only [dot, dir]
    ring
  rw [h1, h2, mul_zero, add_zero] at hkey
  have hk2 : det nprevJ νJ1 * dot nprevJ (dir J)
      = det nprevJ νJ1 * -(det nprevJ J) := by
    rw [hkey]; ring
  exact mul_left_cancel₀ hD hk2

/-- **`hattain` ＋ `rec_vJ` ＋ `0 < D` ＋ `0 < e` ⟹ `0 ≤ k`。**  没有「锥非空」前提：
见证点是 `wedge_witness_of_D_pos` 造出来的 `ν_{J−1}`。 -/
theorem k_nonneg_of_hattain {R : ℕ → Set (ℤ × ℤ)}
    {nprevJ J νJ1 vJ1 w vJ : ℤ × ℤ} {k : ℤ} {i₀ : ℕ}
    (hv : vJ1 = dir nprevJ) (hw : w = -(dir νJ1))
    (hvJ : vJ = k • dir J)
    (hD : 0 < det nprevJ νJ1) (he : 0 < det nprevJ J)
    (hrec : ∀ g ∈ (⋃ j, R j), g + vJ ∈ ⋃ j, R j)
    (hattain : ∀ i, i₀ ≤ i → ∀ m : ℤ × ℤ, 0 < dot m w → dot m vJ1 ≤ 0 →
      ∃ z ∈ R i, ∀ g ∈ (⋃ j, R j), dot m g ≤ dot m z) :
    0 ≤ k := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨hwedge, hzero⟩ := wedge_witness_of_D_pos hv hw hD
  have hdirJ : dot nprevJ (dir J) = -(det nprevJ J) :=
    dot_dir_J_at_nprevJ hv hw (ne_of_gt hD)
  have hpos : 0 < dot nprevJ vJ := by
    rw [hvJ, Nivat.ColleReg.dot_zsmul_right, hdirJ]
    nlinarith [mul_pos (neg_pos.mpr hcon) he]
  exact not_attain_of_dot_vJ_pos (i := i₀) hrec hpos
    (hattain i₀ le_rfl nprevJ hwedge (le_of_eq hzero))

/-- **`0 < k` 的完整形。**  `vJ ≠ 0` 是 `Primitive vJ` 的第一合取，链上现货。 -/
theorem k_pos_of_hattain {R : ℕ → Set (ℤ × ℤ)}
    {nprevJ J νJ1 vJ1 w vJ : ℤ × ℤ} {k : ℤ} {i₀ : ℕ}
    (hv : vJ1 = dir nprevJ) (hw : w = -(dir νJ1))
    (hvJ : vJ = k • dir J) (hvJne : vJ ≠ 0)
    (hD : 0 < det nprevJ νJ1) (he : 0 < det nprevJ J)
    (hrec : ∀ g ∈ (⋃ j, R j), g + vJ ∈ ⋃ j, R j)
    (hattain : ∀ i, i₀ ≤ i → ∀ m : ℤ × ℤ, 0 < dot m w → dot m vJ1 ≤ 0 →
      ∃ z ∈ R i, ∀ g ∈ (⋃ j, R j), dot m g ≤ dot m z) :
    0 < k := by
  have hnn : 0 ≤ k := k_nonneg_of_hattain hv hw hvJ hD he hrec hattain
  have hk0 : k ≠ 0 := by
    intro h
    exact hvJne (by rw [hvJ, h, zero_smul])
  omega

/-- **逆否形：朝向若是另一支，`hattain` 为假。**  这是给派工用的那一面 ——
它说「先裁朝向、再决定要不要做 `hattain`」的排法拿不到东西，两者是同一个比特。 -/
theorem not_hattain_of_k_neg {R : ℕ → Set (ℤ × ℤ)}
    {nprevJ J νJ1 vJ1 w vJ : ℤ × ℤ} {k : ℤ} {i₀ : ℕ}
    (hv : vJ1 = dir nprevJ) (hw : w = -(dir νJ1))
    (hvJ : vJ = k • dir J) (hk : k < 0)
    (hD : 0 < det nprevJ νJ1) (he : 0 < det nprevJ J)
    (hrec : ∀ g ∈ (⋃ j, R j), g + vJ ∈ ⋃ j, R j) :
    ¬ (∀ i, i₀ ≤ i → ∀ m : ℤ × ℤ, 0 < dot m w → dot m vJ1 ≤ 0 →
        ∃ z ∈ R i, ∀ g ∈ (⋃ j, R j), dot m g ≤ dot m z) := by
  intro hattain
  have hnn : 0 ≤ k := k_nonneg_of_hattain hv hw hvJ hD he hrec hattain
  omega

/-- **数值实例（硬规矩 6），§6 的见证点。**  `ν_{J−1} = (1,0)`、`J = (1,1)`、`ν_{J+1} = (0,1)`：
`e = 1 > 0`、`d = 1 > 0`、`D = 1 > 0`，见证点 `n₀ = ν_{J−1} = (1,0)` 满足
`⟪n₀,w⟫ = 1 > 0`、`⟪n₀,v_{J−1}⟫ = 0`、`⟪n₀, dir J⟫ = -1 < 0`。 -/
theorem rigA_wedge_witness_D_pos :
    det ((1 : ℤ), (0 : ℤ)) ((0 : ℤ), (1 : ℤ)) = 1 ∧
      det ((1 : ℤ), (0 : ℤ)) ((1 : ℤ), (1 : ℤ)) = 1 ∧
      det ((1 : ℤ), (1 : ℤ)) ((0 : ℤ), (1 : ℤ)) = 1 ∧
      0 < dot ((1 : ℤ), (0 : ℤ)) (-(dir ((0 : ℤ), (1 : ℤ)))) ∧
      dot ((1 : ℤ), (0 : ℤ)) (dir ((1 : ℤ), (0 : ℤ))) = 0 ∧
      dot ((1 : ℤ), (0 : ℤ)) (dir ((1 : ℤ), (1 : ℤ))) = -1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [det, dot, dir]

/-! ## §7.  两个洞要求**相反**的朝向：`0 < det p vJ` 与 `hattain` 不能同时成立

`blueprint/NOTE.md` (L) 记的路线是：`vJ` 的符号在出生点（`ANormal.exists_nJ_vJ` 经
`exists_primitive_nsmul_eq`）是**自由**的 —— 原文那条接续序 `w ≺ ⋯ ≺ w'` 被
`Lemma41.lean` 的 `IsRegion` docstring **明文丢掉**了（(L.1) 引的那句 "that orientation datum
is not used below and is dropped"）。于是洞 1 的 ℓ 侧就地**选**了一个符号：
`lead-vjsign.lean` 的 `exists_nJ_vJ_signed` 把它钉成 **`0 < det p vJ`**，由此经
`TLKSign2.kpos_iff_detpos` / `TLEndgame.Lside_all_of_kpos` 一次买到
`rec_vJ` ∧ `ahat_halfPlane_L` ∧ `ahat_attained_L` 三条 ℓ 侧义务。
（以上是 `NOTE.md` 的记账；那几份 `tmp/wip/` 收据**我未复核**。本节只用到 `0 < det p vJ`
这个**形状**，不用它们的证明。）

本节量的是那个选择对本组的代价。在链上现成的四条数据之下 ——

* `vJ1 = dir ν_{J−1}`（cone 的 `LeafAJSelect.exists_nprevJ_vJ1`，主仓）；
* `vJ1 = m • vl`，`0 < m`（共线裁决；**只用到 `m > 0`，不用 `m = 1`**，所以
  lane-tower-hbase 报的「单位模 `det vJ vJ1 = ±1` 全树零产者、`m = 1` 目前只是条件的」
  这条**不影响本节**）；
* `p = -(c : ℤ) • vl`（`hp_neg`，`RegionSteps.lean:1359`；**`0 < c` 本节不需要** ——
  `c = 0` 时 `det p vJ = 0`，`hsign` 自己空真）；
* `0 < e = det ν_{J−1} J`（同一条 cone 产出）

—— 有 `m * ⟪vl, J⟫ = e` 故 `0 < ⟪vl, J⟫`（`dot_vl_J_pos_of_collinear`），于是

    det p vJ = -( c * ( k * ⟪vl, J⟫ ) ),

`(c : ℤ) ≥ 0`、`⟪vl,J⟫ > 0` ⟹ **`0 < det p vJ` 迫使 `k < 0`**（`k_neg_of_det_p_vJ_pos`）。
配 §6 的 `not_hattain_of_k_neg` 得 `not_hattain_of_vjsign_choice`：
**洞 1 ℓ 侧选的那个符号让 `hattain` 为假。**

⟹ 这是一个**分叉，不是矛盾**。符号是我们自己选的，所以两个符号各买一边：

| 选 | 买到 | 赔掉 |
|---|---|---|
| `0 < det p vJ`（⟺ `k < 0`） | 洞 1 ℓ 侧三条义务 | `hattain` 为假 ⟹ `shellEnv` 这条路线 |
| `det p vJ < 0`（⟺ `0 < k`） | `hattain` 的必要条件（§6） | ℓ 侧三条义务要另找产者 |

⛔ **本节不裁这个分叉**，也不主张哪一支是原文的。要裁只有两条合法动作：
(a) 把原文 `scratch/b3_colle2.txt` 的接续序找回来并加回 `IsRegion` —— (L.1) 说是我们自己
    删的，所以这一步可逆；或
(b) 证明有一边其实不吃这个符号 —— ℓ 侧要去读 `TLEndgame.Lside_all_of_kpos` 的**证明体**，
    看 `0 < k` 在哪一步承重（(K.2) 的表说三条都经 `(det p vJ)² = k · ⟪nℓ, vJ⟫`，
    若如此则那三条吃的是 `0 ≤ ⟪nℓ,vJ⟫`，不一定非要 `0 < k`）。

⚠ 三条记账边界：
1. 本节**不**依赖 `0 < D`；`0 < D` 只在接到 `not_hattain_of_k_neg` 那一步用到（§6 已吃）。
2. 本节**不**证 `hattain` 为假 —— 它证的是「在 `0 < det p vJ` 之下 `hattain` 为假」。
   `0 < det p vJ` 不是主仓现货（`exists_nJ_vJ_signed` 在 `tmp/wip/`，(L.4) 第 1 条明说
   **穿线未做**，`exists_edge_block` 仍调无符号版本）。所以这**不是**对 `shellEnv` 的反驳，
   是对「两条路线同时走」的反驳。
3. §41：本节的前提在链上都能正面兑现（四条里三条是主仓现货，第四条是团队长的共线裁决），
   不是空真。数值台架见 `rigA_vjsign_fork`。 -/

/-- `det (a • u) v = a * det u v`。 -/
theorem det_zsmul_left_attain (a : ℤ) (u v : ℤ × ℤ) : det (a • u) v = a * det u v := by
  simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- `det u (a • v) = a * det u v`。 -/
theorem det_zsmul_right_attain (a : ℤ) (u v : ℤ × ℤ) : det u (a • v) = a * det u v := by
  simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- `⟪a • u, v⟫ = a * ⟪u, v⟫`。 -/
theorem dot_zsmul_left_attain (a : ℤ) (u v : ℤ × ℤ) : dot (a • u) v = a * dot u v := by
  simp only [dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- **`m * ⟪vl, J⟫ = e`，故 `0 < ⟪vl, J⟫`。**  共线支只用到 `0 < m`。 -/
theorem dot_vl_J_pos_of_collinear {nprevJ J vJ1 vl : ℤ × ℤ} {m : ℤ}
    (hv : vJ1 = dir nprevJ) (hm : vJ1 = m • vl) (hmpos : 0 < m)
    (he : 0 < det nprevJ J) : 0 < dot vl J := by
  have h1 : dot vJ1 J = m * dot vl J := by rw [hm, dot_zsmul_left_attain]
  have h2 : dot vJ1 J = det nprevJ J := by rw [hv, dot_dir_left_eq_det]
  have hkey : m * dot vl J = det nprevJ J := by rw [← h1, h2]
  by_contra hcon
  push_neg at hcon
  linarith [mul_nonpos_of_nonneg_of_nonpos hmpos.le hcon]

/-- **洞 1 ℓ 侧选的符号 `0 < det p vJ` 迫使 `k < 0`。**  `hp_neg` 的 `0 < c` 不需要。 -/
theorem k_neg_of_det_p_vJ_pos {nprevJ J vJ1 vl p vJ : ℤ × ℤ} {k m : ℤ} {c : ℕ}
    (hv : vJ1 = dir nprevJ) (hm : vJ1 = m • vl) (hmpos : 0 < m)
    (he : 0 < det nprevJ J)
    (hp : p = -(c : ℤ) • vl) (hvJ : vJ = k • dir J)
    (hsign : 0 < det p vJ) : k < 0 := by
  have hvlJ : 0 < dot vl J := dot_vl_J_pos_of_collinear hv hm hmpos he
  have hdet : det p vJ = -((c : ℤ) * (k * dot vl J)) := by
    subst hp
    subst hvJ
    simp only [det, dot, dir, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
      Prod.fst_neg, Prod.snd_neg, Prod.neg_mk]
    ring
  rw [hdet] at hsign
  by_contra hcon
  push_neg at hcon
  have hc0 : (0 : ℤ) ≤ (c : ℤ) := Int.natCast_nonneg c
  linarith [mul_nonneg hc0 (mul_nonneg hcon hvlJ.le)]

/-- **合成：洞 1 ℓ 侧的符号选择让 `hattain` 为假。**  见上表 —— 这是分叉的一支，
不是对 `shellEnv` 的反驳。 -/
theorem not_hattain_of_vjsign_choice {R : ℕ → Set (ℤ × ℤ)}
    {nprevJ J νJ1 vJ1 vl p w vJ : ℤ × ℤ} {k m : ℤ} {c : ℕ} {i₀ : ℕ}
    (hv : vJ1 = dir nprevJ) (hw : w = -(dir νJ1))
    (hm : vJ1 = m • vl) (hmpos : 0 < m)
    (hp : p = -(c : ℤ) • vl) (hvJ : vJ = k • dir J)
    (hD : 0 < det nprevJ νJ1) (he : 0 < det nprevJ J)
    (hsign : 0 < det p vJ)
    (hrec : ∀ g ∈ (⋃ j, R j), g + vJ ∈ ⋃ j, R j) :
    ¬ (∀ i, i₀ ≤ i → ∀ n : ℤ × ℤ, 0 < dot n w → dot n vJ1 ≤ 0 →
        ∃ z ∈ R i, ∀ g ∈ (⋃ j, R j), dot n g ≤ dot n z) :=
  not_hattain_of_k_neg hv hw hvJ
    (k_neg_of_det_p_vJ_pos hv hm hmpos he hp hvJ hsign) hD he hrec

/-- **数值台架（硬规矩 6 / §41），§7 的分叉。**  `ν_{J−1} = (1,0)`、`J = (1,1)`、
`ν_{J+1} = (0,1)`、`vJ1 = vl = (0,1)`（`m = 1`）、`c = 1` 故 `p = (0,−1)`、`k = −1` 故
`vJ = (1,−1)`：`e = d = D = 1 > 0`、`⟪vl, J⟫ = 1 > 0`、`det p vJ = 1 > 0`，而 `k = −1 < 0`。
⟹ §7 的前提组**可以同时兑现**（不空真），兑现之后 `hattain` 为假。 -/
theorem rigA_vjsign_fork :
    det ((1 : ℤ), (0 : ℤ)) ((1 : ℤ), (1 : ℤ)) = 1 ∧
      det ((1 : ℤ), (1 : ℤ)) ((0 : ℤ), (1 : ℤ)) = 1 ∧
      det ((1 : ℤ), (0 : ℤ)) ((0 : ℤ), (1 : ℤ)) = 1 ∧
      dir ((1 : ℤ), (0 : ℤ)) = ((0 : ℤ), (1 : ℤ)) ∧
      dot ((0 : ℤ), (1 : ℤ)) ((1 : ℤ), (1 : ℤ)) = 1 ∧
      0 < det ((0 : ℤ), (-1 : ℤ)) ((1 : ℤ), (-1 : ℤ)) ∧
      ((-1 : ℤ)) • dir ((1 : ℤ), (1 : ℤ)) = ((1 : ℤ), (-1 : ℤ)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [det, dot, dir, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Prod.mk.injEq] <;>
    norm_num

end Nivat.LaneLeafAShellAttain

#print axioms Nivat.LaneLeafAShellAttain.cramer_dot_attain
#print axioms Nivat.LaneLeafAShellAttain.det_right_dir
#print axioms Nivat.LaneLeafAShellAttain.det_dir_dir_eq
#print axioms Nivat.LaneLeafAShellAttain.D_mul_dot_dir_J
#print axioms Nivat.LaneLeafAShellAttain.wedge_false_of_D_eq_zero
#print axioms Nivat.LaneLeafAShellAttain.dot_vJ_neg_of_D_pos
#print axioms Nivat.LaneLeafAShellAttain.dot_vJ_pos_of_D_neg
#print axioms Nivat.LaneLeafAShellAttain.not_attain_of_dot_vJ_pos
#print axioms Nivat.LaneLeafAShellAttain.D_nonneg_of_hattain
#print axioms Nivat.LaneLeafAShellAttain.wedge_empty_of_D_eq_zero
#print axioms Nivat.LaneLeafAShellAttain.rigA_wedge_nonempty
#print axioms Nivat.LaneLeafAShellAttain.dot_dir_left_eq_det
#print axioms Nivat.LaneLeafAShellAttain.wedge_witness_of_D_neg
#print axioms Nivat.LaneLeafAShellAttain.D_mul_dot_general
#print axioms Nivat.LaneLeafAShellAttain.dot_x_nonpos_of_dets
#print axioms Nivat.LaneLeafAShellAttain.dir_dir_attain
#print axioms Nivat.LaneLeafAShellAttain.wedge_witness_is_neg_nprevJ
#print axioms Nivat.LaneLeafAShellAttain.D_nonneg_of_hattain_restricted
#print axioms Nivat.LaneLeafAShellAttain.two_wall_identity
#print axioms Nivat.LaneLeafAShellAttain.bddAbove_of_two_walls
#print axioms Nivat.LaneLeafAShellAttain.wedge_witness_of_D_pos
#print axioms Nivat.LaneLeafAShellAttain.dot_dir_J_at_nprevJ
#print axioms Nivat.LaneLeafAShellAttain.k_nonneg_of_hattain
#print axioms Nivat.LaneLeafAShellAttain.k_pos_of_hattain
#print axioms Nivat.LaneLeafAShellAttain.not_hattain_of_k_neg
#print axioms Nivat.LaneLeafAShellAttain.rigA_wedge_witness_D_pos
#print axioms Nivat.LaneLeafAShellAttain.det_zsmul_left_attain
#print axioms Nivat.LaneLeafAShellAttain.det_zsmul_right_attain
#print axioms Nivat.LaneLeafAShellAttain.dot_zsmul_left_attain
#print axioms Nivat.LaneLeafAShellAttain.dot_vl_J_pos_of_collinear
#print axioms Nivat.LaneLeafAShellAttain.k_neg_of_det_p_vJ_pos
#print axioms Nivat.LaneLeafAShellAttain.not_hattain_of_vjsign_choice
#print axioms Nivat.LaneLeafAShellAttain.rigA_vjsign_fork
