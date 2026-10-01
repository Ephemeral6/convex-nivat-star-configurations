/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.TowerEHelp
import Nivat.External.Colle.ANormal

/-!
# `hwadj` 的生成元判据：把「`𝒮_φ` 是 zonotope」变成有限检查（lane-towerpkg，第 183 轮）

**派工**：team-lead 第 183 轮，取代上一封第 7 条的先做项：
「把『`𝒮_φ` 是 zonotope』变成 `hwadj` 的判据。」

## 结论（一句话）

`hwadj` 不是 `2m` 条法向上的一族独立不等式，它**逐条塌成 `m` 条生成元上的一条符号乘积**：

    (∀ n ∈ E ↑d.Sphi, ¬ (dot n vl < 0 ∧ dot n w < 0))
      ↔ ∀ j : Fin d.m, det (d.h j) vl * det (d.h j) w ≤ 0

而且是 **`iff`**，不是单向蕴含。右边逐字读作：**每一条生成元直线 `ℝ h_j` 都（弱）分隔 `vl`
与 `w`**。`hwadj_iff_det_sep_Sphi`（`:199`）。

塌陷的机制是 `E` 的 `±` 对称：`E ↑d.Sphi = {±genPerp' (h j)}`
（`E_zonoF_eq_genPerp_set`，`TowerEHelp.lean:31`，前提只有 `d.h_ne` / `d.h_dir` 两个字段）。
在 `ν` 处 `hwadj` 禁掉「两个内积都 `< 0`」，在 `-ν` 处禁掉「两个内积都 `> 0`」；两条合起来
就是「两个内积不同号」，即乘积 `≤ 0`。所以 `2m` 条约束成对合并成 `m` 条。

## ⚠ 一名两物：原文的 `E(𝒮_φ)` 是**方向侧**，Lean 的 `E ↑Sphi` 是**法向侧**

`scratch/b3_colle2.txt:319`（**本轮亲读**）逐字：

> Then `|E(𝒮_φ)| = 2m` and, for each `w ∈ E(𝒮_φ)`, `w` is either parallel or antiparallel
> to some vector `h_i`, with `1 ≤ i ≤ m`.

原文的 `E(𝒮_φ)` 成员**平行于 `h_i`**（方向侧）。Lean 的 `E R`（`IsEdge`，
`LatticeEdges.lean:214`）成员是**法向**，`genPerp' (h j) ⊥ h j`。两者差一个 `dir`。
本文件全程在**法向侧**陈述 `hwadj`（因为链上 `hwadj` 的 `n` 跑遍 `E ↑Sφ` 的法向），
判据的右边则写在**方向侧**（`det (h j) · `），`dot_genPerp_eq_det`（`:82`）是唯一的换边处。

## ⛔ 射程闸（team-lead 第 181 轮的带符号 `det vl w` 硬闸）

本文件里**没有任何**「原文侧 ↔ 链上」的搬运：`hwadj_iff_det_sep_Sphi` 两边都是链上对象
（`d.Sphi`、`d.h`、`vl`、`w` 都是 Lean 侧的），它是一条**等价**，不是一条转写。
右边的 `det (d.h j) vl * det (d.h j) w ≤ 0` 是**乘积**，对 `h j ↦ -h j` 不变（这正是
「直线」而不是「向量」的表现）；它对 `vl ↦ -vl` 会变号，所以**这条判据本身不能用来定
`vl` 的符号**，只能在 `vl` 已定的前提下判 `hwadj`。

## 对 team-lead 那个问题的回答

> 在 `-w` 与 `vl` 在这 `2m` 条的循环序里**相邻**的前提下，这个有限检查是不是恒真？

**是，而且是充要的**——但「相邻」要写成无需排序的形式才接得上：

`hwadj` 在指标 `j` 处失败 ⟺ `0 < det (h j) vl * det (h j) w` ⟺
`det (h j) vl * det (h j) (-w) < 0` ⟺ 直线 `ℝ h_j` **严格分隔** `vl` 与 `-w`
（`hwadj_iff_no_gen_separates`，`:166`）。

而「`vl` 与 `-w` 在扇里相邻」的无排序写法**就是**「没有生成元直线严格分隔 `vl` 与 `-w`」。
于是判据与相邻性是同一句话，`⟸` 与 `⟹` 都成立，无需对 `m` 归纳、无需把
`f₀,…,f_{2m-1}` 的循环序形式化。`m = 4` 上的独立核对见
`tmp/wip/lane-towerpkg-conearc.lean` 的 `fan_adjacent_implies_empty`（`:1291`）。

**还欠的是**：把「排序意义下的相邻」（`sortedCand` 那一族）与本文件的 `¬ SepsLine` 对上。
本文件**不声称**已对上；`m = 4` 上 `conearc` §9.5 给了内核核对，一般 `m` 没做。
**归属（team-lead 第 191 轮）：lane-tower-hbase**——`w := extChain d nℓ vl u' i Ilean`，
`candSet`（`TowerConstruct.lean:246`）装的是**生成元方向**、不是法向——它的元素是
`wgen d nℓ j = primPart (orientGen d nℓ j)`（`:250`），而
`orientGen d nℓ j = if dot nℓ (d.h j) < 0 then d.h j else -(d.h j)`（`:124`）＝ `± d.h j`，
故 `wgen` 平行于生成元本身（`det_wgen_h_eq_zero`，`:622`）。⚠ `± d.h j` 那条等式是
`orientGen` 的，不是 `wgen` 的：`d.h j` 非本原时 `wgen` 只是**平行**、不等于 `± d.h j`。
法向侧是 `E ↑d.Sphi`，两者差一个 `genPerp'`。`sortedCand`（`:263`）按 `keyOf (-nℓ)`
排成绕 `nℓ` 的角序、`Ilean` ＝使 `𝓡_I` 周期的**最小**下标（`TowerPackage.lean:308`），
他在算 `Ilean` 是否落在角度邻位。细节见 `CORE-HOLES.md` 第 187 轮条目。

## 本文件不碰

- 不 import `RegionSteps` / `ColleRegion` / `Case2WindowProbe` / `NfpLPreamble`
  （本轮用脚本算过 `TowerEHelp` / `ANormal` 的传递闭包，四个禁项命中数 0）。
- 不改主仓任何签名。
-/

namespace Nivat.LaneTowerPkgZonoCrit

open Nivat Nivat.LE2 Nivat.Colle35

variable {m : ℕ}

/-! ## §1. 换边：法向侧的 `dot` 与方向侧的 `det` 只差一个正倍数 -/

/-- `genPerp v = dir v`（`ZonoEdgeGen.lean:43`），而 `dot (dir v) x = det v x` 逐项相等。 -/
theorem dot_genPerp_eq_det (v x : ℤ × ℤ) : dot (genPerp v) x = det v x := by
  simp only [genPerp, dir, dot, det]; ring

private theorem dot_zsmul_left (k : ℤ) (n x : ℤ × ℤ) : dot (k • n) x = k * dot n x := by
  simp only [dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

/-- `det v ·` 与 `dot (genPerp' v) ·` 差一个**正**整数倍（`primPart` 的 gcd）。 -/
theorem exists_pos_factor_det_genPerp' {v : ℤ × ℤ} (hv : v ≠ 0) :
    ∃ g : ℤ, 0 < g ∧ ∀ x : ℤ × ℤ, det v x = g * dot (genPerp' v) x := by
  obtain ⟨-, g, hgpos, heq⟩ := primPart_spec (genPerp_ne_zero hv)
  refine ⟨g, hgpos, fun x => ?_⟩
  have hgp : genPerp v = g • genPerp' v := by rw [genPerp']; exact heq
  calc det v x = dot (genPerp v) x := (dot_genPerp_eq_det v x).symm
    _ = dot (g • genPerp' v) x := by rw [hgp]
    _ = g * dot (genPerp' v) x := dot_zsmul_left _ _ _

/-- 因为差的是正倍数，**乘积的符号**在两侧一致。 -/
theorem det_mul_nonpos_iff_dot_genPerp'_mul_nonpos {v vl w : ℤ × ℤ} (hv : v ≠ 0) :
    det v vl * det v w ≤ 0 ↔ dot (genPerp' v) vl * dot (genPerp' v) w ≤ 0 := by
  obtain ⟨g, hgpos, hall⟩ := exists_pos_factor_det_genPerp' hv
  have hg2 : 0 < g * g := mul_pos hgpos hgpos
  rw [hall vl, hall w]
  constructor
  · intro hle
    by_contra hc
    push_neg at hc
    nlinarith
  · intro hle
    nlinarith

/-! ## §2. 主判据（一般 `m`，zonotope 形） -/

/-- **`hwadj` 的生成元判据**：在 `zonoF univ h` 的边法向集上，
「没有法向同时对 `vl` 与 `w` 取负内积」等价于「每条生成元直线 `ℝ h_j` 都弱分隔 `vl` 与 `w`」。

左边逐字是链上 `hwadj`（`Nivat.Hole3Room.nlmax_of_wadj` 的 binder 形状，声明行
`Hole3Room.lean:319`，`hwadj` binder 在 `:324-325`；lane-env-refute 亲读、集成者第 185 轮
复核，**不再是转引**）。右边是 `Fin m` 上的有限检查。

机制：`E_zonoF_eq_genPerp_set`（`TowerEHelp.lean:31`）把 `E` 穷举成 `{±genPerp' (h j)}`；
`+` 号那支给「不同时 `< 0`」，`-` 号那支给「不同时 `> 0`」，合起来是「乘积 `≤ 0`」。 -/
theorem hwadj_iff_det_sep (h : Fin m → ℤ × ℤ) (h_ne : ∀ j, h j ≠ 0)
    (h_dir : ∀ j k, j ≠ k → det (h j) (h k) ≠ 0) (vl w : ℤ × ℤ) :
    (∀ n ∈ E (↑(zonoF Finset.univ h) : Set (ℤ × ℤ)), ¬ (dot n vl < 0 ∧ dot n w < 0)) ↔
      ∀ j : Fin m, det (h j) vl * det (h j) w ≤ 0 := by
  constructor
  · intro hw j
    rw [det_mul_nonpos_iff_dot_genPerp'_mul_nonpos (h_ne j)]
    have h1 := hw (genPerp' (h j))
      ((E_zonoF_eq_genPerp_set h h_ne h_dir _).mpr ⟨j, Or.inl rfl⟩)
    have h2 := hw (-genPerp' (h j))
      ((E_zonoF_eq_genPerp_set h h_ne h_dir _).mpr ⟨j, Or.inr rfl⟩)
    rw [dot_neg_left, dot_neg_left] at h2
    push_neg at h1 h2
    rcases lt_trichotomy (dot (genPerp' (h j)) vl) 0 with ha | ha | ha
    · have hb := h1 ha
      nlinarith
    · rw [ha]; simp
    · have hb := h2 (by omega)
      nlinarith
  · intro hgen n hn
    rcases (E_zonoF_eq_genPerp_set h h_ne h_dir n).mp hn with ⟨j, rfl | rfl⟩
    · have hkey := (det_mul_nonpos_iff_dot_genPerp'_mul_nonpos (v := h j) (vl := vl) (w := w)
        (h_ne j)).mp (hgen j)
      rintro ⟨hA, hB⟩
      nlinarith
    · have hkey := (det_mul_nonpos_iff_dot_genPerp'_mul_nonpos (v := h j) (vl := vl) (w := w)
        (h_ne j)).mp (hgen j)
      rw [dot_neg_left, dot_neg_left]
      rintro ⟨hA, hB⟩
      nlinarith

/-! ## §3. 「相邻」的无排序写法 -/

/-- 直线 `ℝ v` **严格分隔** `a` 与 `b`。对 `v ↦ -v` 不变（所以它谈的是直线，不是向量）。 -/
def SepsLine (v a b : ℤ × ℤ) : Prop := det v a * det v b < 0

theorem sepsLine_neg_left (v a b : ℤ × ℤ) : SepsLine (-v) a b ↔ SepsLine v a b := by
  simp only [SepsLine, det, Prod.fst_neg, Prod.snd_neg]
  constructor <;> intro h <;> nlinarith

/-- **判据的「相邻」读法**：`hwadj` 成立 ⟺ **没有**生成元直线严格分隔 `vl` 与 `-w`。

右边就是「`vl` 与 `-w` 在 `𝒮_φ` 的扇里相邻」的无排序写法：一条直线严格分隔 `vl` 与 `-w`
当且仅当它穿过 `vl` 与 `-w` 之间的开扇区，所以「没有直线穿过」＝「中间没有别的边方向」。 -/
theorem hwadj_iff_no_gen_separates (h : Fin m → ℤ × ℤ) (h_ne : ∀ j, h j ≠ 0)
    (h_dir : ∀ j k, j ≠ k → det (h j) (h k) ≠ 0) (vl w : ℤ × ℤ) :
    (∀ n ∈ E (↑(zonoF Finset.univ h) : Set (ℤ × ℤ)), ¬ (dot n vl < 0 ∧ dot n w < 0)) ↔
      ∀ j : Fin m, ¬ SepsLine (h j) vl (-w) := by
  rw [hwadj_iff_det_sep h h_ne h_dir vl w]
  constructor
  · intro hgen j hsep
    have := hgen j
    simp only [SepsLine, det, Prod.fst_neg, Prod.snd_neg] at hsep
    simp only [det] at this
    nlinarith
  · intro hgen j
    have := hgen j
    simp only [SepsLine, det, Prod.fst_neg, Prod.snd_neg] at this
    simp only [det]
    nlinarith

/-- **两端是白送的**：若 `vl` 平行于某条生成元 `h j`，该 `j` 上的检查自动通过。
（`vl` 与 `w` 各自平行于某个 `h_i` 正是 `b3_colle2.txt:319` 的内容，本轮亲读。） -/
theorem det_sep_of_par_left {v vl w : ℤ × ℤ} (hpar : det v vl = 0) :
    det v vl * det v w ≤ 0 := by rw [hpar]; simp

theorem det_sep_of_par_right {v vl w : ℤ × ℤ} (hpar : det v w = 0) :
    det v vl * det v w ≤ 0 := by rw [hpar]; simp

/-! ## §4. 链上形状：`E ↑d.Sphi` -/

/-- **判据，链上形状**。`Sφ = d.toDecompData.Sphi` 由
`L1GenPackage.exists_gen_package'` 逐字给出：`obtain` 块在 `RegionSteps.lean:1979-1984`，
结论第二合取 `Sφ = d.toDecompData.Sphi` 在 `:1981`（lane-env-refute 亲读、集成者第 185 轮
复核，**不再是转引**；第 183 轮所引 `:1971-1976` 已失效）。所以 `hwadj` 的 `E ↑Sφ`
就是这里的 `E ↑d.Sphi`。

seam 是 `DecompData.E_Sphi_eq_zonoF`（`ANormal.lean:292`，本轮亲读），
它只用 `d.Sphi_eq` + `Conv_supp_prod_eq_Conv_zonoF`，不加任何前提。 -/
theorem hwadj_iff_det_sep_Sphi {α : Type*} [AddCommMonoid α] {η : Config α}
    (d : DecompData η) (vl w : ℤ × ℤ) :
    (∀ n ∈ E (↑d.Sphi : Set (ℤ × ℤ)), ¬ (dot n vl < 0 ∧ dot n w < 0)) ↔
      ∀ j : Fin d.m, det (d.h j) vl * det (d.h j) w ≤ 0 := by
  rw [d.E_Sphi_eq_zonoF]
  exact hwadj_iff_det_sep d.h d.h_ne d.h_dir vl w

/-- **相邻读法，链上形状**。 -/
theorem hwadj_iff_no_gen_separates_Sphi {α : Type*} [AddCommMonoid α] {η : Config α}
    (d : DecompData η) (vl w : ℤ × ℤ) :
    (∀ n ∈ E (↑d.Sphi : Set (ℤ × ℤ)), ¬ (dot n vl < 0 ∧ dot n w < 0)) ↔
      ∀ j : Fin d.m, ¬ SepsLine (d.h j) vl (-w) := by
  rw [d.E_Sphi_eq_zonoF]
  exact hwadj_iff_no_gen_separates d.h d.h_ne d.h_dir vl w

/-- **反过来用**：只要能指出一条生成元直线严格分隔 `vl` 与 `-w`，`hwadj` 就为假。
这是把「`hwadj` 为假」的见证从「造一条边法向 `n ∈ E ↑Sφ`」降成「指一个 `j`」。 -/
theorem not_hwadj_of_sepsLine {α : Type*} [AddCommMonoid α] {η : Config α}
    (d : DecompData η) (vl w : ℤ × ℤ) (j : Fin d.m) (hsep : SepsLine (d.h j) vl (-w)) :
    ¬ (∀ n ∈ E (↑d.Sphi : Set (ℤ × ℤ)), ¬ (dot n vl < 0 ∧ dot n w < 0)) := by
  intro hw
  exact ((hwadj_iff_no_gen_separates_Sphi d vl w).mp hw j) hsep

/-! ## §5. 公理收据 -/

#print axioms dot_genPerp_eq_det
#print axioms exists_pos_factor_det_genPerp'
#print axioms det_mul_nonpos_iff_dot_genPerp'_mul_nonpos
#print axioms hwadj_iff_det_sep
#print axioms sepsLine_neg_left
#print axioms hwadj_iff_no_gen_separates
#print axioms det_sep_of_par_left
#print axioms det_sep_of_par_right
#print axioms hwadj_iff_det_sep_Sphi
#print axioms hwadj_iff_no_gen_separates_Sphi
#print axioms not_hwadj_of_sepsLine

end Nivat.LaneTowerPkgZonoCrit
