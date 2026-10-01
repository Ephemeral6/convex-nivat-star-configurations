/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.TowerHlevCover

/-!
# `maxA` 对 hlev 的退化见证定价：**下标要挪一格，挪完 `maxA` 免费**

派工来源：`lane-tower-hlev` 第 244 轮来信「`maxA` 那条靶你拿走」。判据是他写的：
`Rdeg`（或竖射线）能不能配某个 `S` 兑现 `IsMaxEnvIn (EnvOf ↑S) (canonA …) (A i)`。
按 §84 打印分母：本文件两条都是**内核结论**，不是「没找到」。

## 答案（两条，方向相反，合起来才是全貌）

**§1（否）**：`TowerHlevCover.Adeg` **按原下标**配不出任何 `S`。机制与几何无关，
是边集基数：`Adeg 0 = {(0,0)}` 是单点 ⟹ `E (Adeg 0) = ∅`；`Adeg 1` 有两点且共线
⟹ `E (Adeg 1) = {(2,1), (-2,-1)}`，基数 2。而 `Enveloped ↑S ·` 的第二支要求
`(E ·).encard = (E ↑S).encard`，同一个 `S` 不能既等于 0 又等于 2。

**§2（是）**：把族整体挪一格（`Aray i := Adeg (i+1)`，每片都已有两点）之后，
`S = {(0,0), (-1,2)}` 就兑现 `maxA`，而且 **`⋃ i, hatOf Aray kkdeg vl i` 仍然是同一个
`Rdeg`** ⟹ hlev 两条 bundle 结论的**居民没变**。

⟹ **`maxA` 不杀这个见证**，只逼一个下标位移。`not_cover_of_geom_bundle` /
`not_unbounded_along_vJ_of_geom_bundle` 的前提表里再加一条 `maxA` 仍然可反。

⚠ 本文件**不**改 hlev 的文件（规矩 14），也**不**重述他那二十条 binder；
§2 的 `exists_maxA_for_ray` 把「换掉 `A` 之后仍然成立的那几条」（union / 有限 / 单调）
和 `maxA` 一起打包，hlev 可以直接插进自己那条的 `A := Aray` 位置。

## 与 §84 的分母

* §1 是「证明了无 `S`」（`not_maxA_Adeg`，对任意 `α / η / xper / vl / S / B / u` 全称否定）。
* §2 是「给出了 `S`」（`exists_maxA_for_ray`，显式见证）。
两条都不是「找不到」。

## 相容性收据（集成者第 243 轮新判据）

本文件**没有**新 `Prop` / `structure`；新 `def` 全是具体见证（`Sray` / `Aray` / `Bray` /
`uray` / `etaRay` / `xperRay`），它们的「前提可满足性」就是 §2 那四条结论本身：
`iUnion_hatOf_ray` / `finite_Aray` / `mono_Aray` / `maxA_ray` 逐条给出。
⚠ 按我上一轮自己摔的那一跤（相容性收据必须把**已知的字段推论**一起核），这里明写
本文件**没核**的：`envB` / `envShift` / `subBA` / `subAB` / `escapeW` / `shellSubStrip` /
`shellEnv` / `fillCover` / `nfp_L` / `F` 的各字段，一条没测。本文件只对 `maxA` 说话。
-/

set_option autoImplicit false

namespace Nivat.EnvRefuteMaxA

open Nivat Nivat.LE2 Nivat.Colle35 Nivat.TowerHlevCover

/-! ## §1  线段 `Adeg M` 的边集，以及原下标下 `maxA` 的不可满足性 -/

/-- 与方向 `(-1,2)` 垂直的法向（`n.1 = 2 n.2`）在整条线段上配对为 `0`。 -/
theorem dot_perp_Adeg {n : ℤ × ℤ} (hn : n.1 = 2 * n.2) {M : ℕ} {z : ℤ × ℤ}
    (hz : z ∈ Adeg M) : dot n z = 0 := by
  obtain ⟨t, -, rfl⟩ := hz
  simp only [dot, hn]
  ring

/-- 这样的法向把整条线段暴露成一个面。 -/
theorem face_eq_self {n : ℤ × ℤ} (hn : n.1 = 2 * n.2) (M : ℕ) :
    face (Adeg M) n = Adeg M := by
  ext z
  constructor
  · exact fun h => h.1
  · intro hz
    refine mem_face_iff.mpr ⟨hz, fun y hy => ?_⟩
    exact le_of_eq (by rw [dot_perp_Adeg hn hy, dot_perp_Adeg hn hz])

theorem zero_mem_Adeg (M : ℕ) : ((0 : ℤ), (0 : ℤ)) ∈ Adeg M :=
  ⟨0, Nat.zero_le _, by norm_num [Prod.ext_iff]⟩

theorem one_mem_Adeg {M : ℕ} (hM : 1 ≤ M) : ((-1 : ℤ), (2 : ℤ)) ∈ Adeg M :=
  ⟨1, hM, by norm_num [Prod.ext_iff]⟩

/-- ⭐ **线段的边集恰是两个方向**。`⊆` 那一半是：面里有两个不同点 ⟹ 它们的差
`(t-s)·(-1,2)` 与 `n` 正交 ⟹ `n.1 = 2 n.2` ⟹ `n.2 ∣ gcd = 1` ⟹ `n.2 = ±1`。 -/
theorem E_Adeg {M : ℕ} (hM : 1 ≤ M) :
    E (Adeg M) = {((2 : ℤ), (1 : ℤ)), ((-2 : ℤ), (-1 : ℤ))} := by
  ext n
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hprim, a, ha, b, hb, hab⟩
    have hdot := dot_eq_of_mem_face ha hb
    obtain ⟨s, -, rfl⟩ := ha.1
    obtain ⟨t, -, rfl⟩ := hb.1
    have hst : (s : ℤ) ≠ (t : ℤ) := by
      intro h
      apply hab
      have hst' : s = t := by exact_mod_cast h
      rw [hst']
    simp only [dot] at hdot
    have hn12 : n.1 = 2 * n.2 := by
      have hfac : ((t : ℤ) - (s : ℤ)) * (n.1 - 2 * n.2) = 0 := by linarith
      rcases mul_eq_zero.mp hfac with h | h
      · exact absurd (by linarith : (s : ℤ) = (t : ℤ)) hst
      · linarith
    obtain ⟨u, v, huv⟩ := prim_iff_primitive.mp hprim
    have hdvd : n.2 ∣ (1 : ℤ) :=
      ⟨u * 2 + v, by linear_combination (-1 : ℤ) * huv + u * hn12⟩
    rcases Int.isUnit_iff.mp (isUnit_of_dvd_one hdvd) with h | h
    · left
      rw [Prod.ext_iff]
      exact ⟨by rw [hn12, h]; ring, h⟩
    · right
      rw [Prod.ext_iff]
      exact ⟨by rw [hn12, h]; ring, h⟩
  · rintro (rfl | rfl)
    · refine ⟨by decide, ?_⟩
      rw [face_eq_self (by norm_num) M]
      exact ⟨_, zero_mem_Adeg M, _, one_mem_Adeg hM, by decide⟩
    · refine ⟨by decide, ?_⟩
      rw [face_eq_self (by norm_num) M]
      exact ⟨_, zero_mem_Adeg M, _, one_mem_Adeg hM, by decide⟩

theorem encard_E_Adeg {M : ℕ} (hM : 1 ≤ M) : (E (Adeg M)).encard = 2 := by
  rw [E_Adeg hM]
  exact Set.encard_pair (by decide)

/-- 单点集没有边。 -/
theorem E_Adeg_zero : E (Adeg 0) = (∅ : Set (ℤ × ℤ)) := by
  ext n
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨-, a, ha, b, hb, hab⟩
  obtain ⟨s, hs, rfl⟩ := ha.1
  obtain ⟨t, ht, rfl⟩ := hb.1
  rw [Nat.le_zero] at hs ht
  subst hs
  subst ht
  exact hab rfl

/-- ⭐ **第 0 片与第 1 片要不同的 `E(S)` 基数** ⟹ 没有 `S` 能同时包住两片。 -/
theorem not_enveloped_Adeg_zero_one {S : Finset (ℤ × ℤ)} :
    ¬ (Enveloped (↑S : Set (ℤ × ℤ)) (Adeg 0) ∧ Enveloped (↑S : Set (ℤ × ℤ)) (Adeg 1)) := by
  rintro ⟨h0, h1⟩
  have e0 : (E (↑S : Set (ℤ × ℤ))).encard = 0 := by
    rw [← h0.2, E_Adeg_zero, Set.encard_empty]
  have e1 : (E (↑S : Set (ℤ × ℤ))).encard = 2 := by
    rw [← h1.2, encard_E_Adeg le_rfl]
  rw [e0] at e1
  simp at e1

/-- ⭐ **`TowerHlevCover.Adeg` 按原下标不满足 `maxA`**，对任何 `α / η / xper / vl / S / B / u`。
⚠ 射程：本条否的是**那个具体的族 `Adeg`**，不是 `Rdeg` 这个居民；§2 说明居民本身没事。 -/
theorem not_maxA_Adeg {α : Type*} {η xper : Config α} {vl : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} {B : ℕ → Set (ℤ × ℤ)} {u : ℕ → ℤ × ℤ} :
    ¬ ∀ i : ℕ, IsMaxEnvIn (EnvOf (↑S : Set (ℤ × ℤ))) (canonA η xper vl B u i) (Adeg i) := by
  intro h
  exact not_enveloped_Adeg_zero_one ⟨(h 0).1, (h 1).1⟩

/-! ## §2  挪一格之后 `maxA` 免费，居民不变 -/

/-- 位移后的族：每片都已有两点，边集恒为 `{(2,1), (-2,-1)}`。 -/
def Aray : ℕ → Set (ℤ × ℤ) := fun i => Adeg (i + 1)

/-- `B` 取与 `A` 同一族：`canonA` 的半带从它长出来，再被 `η = x_per` 切回去。 -/
def Bray : ℕ → Set (ℤ × ℤ) := fun i => Adeg (i + 1)

def uray : ℕ → ℤ × ℤ := fun _ => ((0 : ℤ), (0 : ℤ))

/-- 切割器：半带 `H_{B_i}((1,-2))` 往 `(1,-2)` 方向溢出到 `y < 0`，`η = x_per` 把它切回。 -/
def etaRay : Config Prop := fun z => 0 ≤ z.2

def xperRay : Config Prop := fun _ => True

def vray : ℤ × ℤ := ((1 : ℤ), (-2 : ℤ))

/-- 见证 `S`：线段的头两点。`E(↑S)` 与每片的边集逐字相同。 -/
def Sray : Finset (ℤ × ℤ) := {((0 : ℤ), (0 : ℤ)), ((-1 : ℤ), (2 : ℤ))}

theorem coe_Sray : (↑Sray : Set (ℤ × ℤ)) = Adeg 1 := by
  ext z
  simp only [Sray, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  constructor
  · rintro (rfl | rfl)
    · exact zero_mem_Adeg 1
    · exact one_mem_Adeg le_rfl
  · rintro ⟨t, ht, rfl⟩
    interval_cases t
    · left; norm_num [Prod.ext_iff]
    · right; norm_num [Prod.ext_iff]

/-- 线段是格凸区域：`C = {q | -M ≤ q.1 ≤ 0 ∧ q.2 = -2 q.1}`（两条闭半平面 ∩ 一条直线）。 -/
theorem latticeConvex_Adeg (M : ℕ) : IsLatticeConvexRegion (Adeg M) := by
  refine ⟨{q : ℝ × ℝ | -(M : ℝ) ≤ q.1 ∧ q.1 ≤ 0 ∧ q.2 = -2 * q.1}, ?_, ?_, ?_⟩
  · intro x hx y hy a b ha hb hab
    refine ⟨?_, ?_, ?_⟩
    · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      have h1 : a * (-(M : ℝ)) ≤ a * x.1 := mul_le_mul_of_nonneg_left hx.1 ha
      have h2 : b * (-(M : ℝ)) ≤ b * y.1 := mul_le_mul_of_nonneg_left hy.1 hb
      nlinarith [h1, h2]
    · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      have h1 : a * x.1 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha hx.2.1
      have h2 : b * y.1 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hb hy.2.1
      linarith
    · simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      rw [hx.2.2, hy.2.2]
      ring
  · have h0 : IsClosed {q : ℝ × ℝ | -(M : ℝ) ≤ q.1} :=
      isClosed_le continuous_const continuous_fst
    have h1 : IsClosed {q : ℝ × ℝ | q.1 ≤ 0} := isClosed_le continuous_fst continuous_const
    have h2 : IsClosed {q : ℝ × ℝ | q.2 = -2 * q.1} :=
      isClosed_eq continuous_snd (continuous_const.mul continuous_fst)
    exact h0.inter (h1.inter h2)
  · ext z
    constructor
    · rintro ⟨t, ht, rfl⟩
      have htM : (t : ℤ) ≤ (M : ℤ) := by exact_mod_cast ht
      have htMr : ((t : ℤ) : ℝ) ≤ ((M : ℤ) : ℝ) := by exact_mod_cast htM
      have ht0 : (0 : ℝ) ≤ ((t : ℤ) : ℝ) := by exact_mod_cast Int.natCast_nonneg t
      refine ⟨?_, ?_, ?_⟩
      · show -(M : ℝ) ≤ ((-(t : ℤ) : ℤ) : ℝ)
        push_cast at htMr ⊢
        linarith
      · show ((-(t : ℤ) : ℤ) : ℝ) ≤ 0
        push_cast at ht0 ⊢
        linarith
      · show (((2 * (t : ℤ)) : ℤ) : ℝ) = -2 * ((-(t : ℤ) : ℤ) : ℝ)
        push_cast
        ring
    · rintro ⟨h1, h2, h3⟩
      have h1r : -((M : ℕ) : ℝ) ≤ ((z.1 : ℤ) : ℝ) := h1
      have h2r : ((z.1 : ℤ) : ℝ) ≤ 0 := h2
      have h3r : ((z.2 : ℤ) : ℝ) = -2 * ((z.1 : ℤ) : ℝ) := h3
      have h1' : -(M : ℤ) ≤ z.1 := by
        have hc : ((-(M : ℤ) : ℤ) : ℝ) ≤ ((z.1 : ℤ) : ℝ) := by
          push_cast at h1r ⊢
          linarith
        exact_mod_cast hc
      have h2' : z.1 ≤ 0 := by exact_mod_cast h2r
      have h3' : z.2 = -2 * z.1 := by exact_mod_cast h3r
      refine ⟨(-z.1).toNat, by omega, ?_⟩
      have ht : ((-z.1).toNat : ℤ) = -z.1 := Int.toNat_of_nonneg (by omega)
      rw [Prod.ext_iff]
      refine ⟨?_, ?_⟩ <;> simp only [ht] <;> omega

/-- ⭐ **每一片都被 `↑Sray` 包住**：边集逐字相同，面的基数比较退化成集合包含。 -/
theorem enveloped_Adeg {M : ℕ} (hM : 1 ≤ M) :
    Enveloped (↑Sray : Set (ℤ × ℤ)) (Adeg M) := by
  have hSE : E (↑Sray : Set (ℤ × ℤ)) = {((2 : ℤ), (1 : ℤ)), ((-2 : ℤ), (-1 : ℤ))} := by
    rw [coe_Sray]
    exact E_Adeg le_rfl
  refine ⟨⟨latticeConvex_Adeg M, ?_⟩, ?_⟩
  · intro n hn
    rw [E_Adeg hM] at hn
    have hperp : n.1 = 2 * n.2 := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
      rcases hn with rfl | rfl <;> norm_num
    refine ⟨by rw [hSE]; exact hn, ?_⟩
    rw [coe_Sray, face_eq_self hperp, face_eq_self hperp]
    exact Set.encard_mono (mono_Adeg 1 M hM)
  · rw [hSE, E_Adeg hM]

/-- ⭐ **约束集恰好就是 `A i`**：半带往 `(1,-2)` 溢出的部分全在 `y < 0`，被 `η = x_per` 切掉。 -/
theorem canonA_ray (i : ℕ) :
    canonA etaRay xperRay vray Bray uray i = Adeg (i + 1) := by
  ext w
  constructor
  · rintro ⟨hstrip, hagree⟩
    have h2 : (0 : ℤ) ≤ (w + uray i).2 := of_eq_true hagree
    have h2' : (0 : ℤ) ≤ w.2 := by simpa [uray] using h2
    obtain ⟨b, hb, t, hbt⟩ := hstrip
    obtain ⟨s, hs, rfl⟩ := hb
    have hpt : ((-(s : ℤ), 2 * (s : ℤ)) + (t : ℤ) • vray : ℤ × ℤ)
        = (-((s : ℤ) - (t : ℤ)), 2 * ((s : ℤ) - (t : ℤ))) := by
      simp only [vray, Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
        smul_eq_mul]
      constructor <;> ring
    rw [hpt] at hbt
    subst hbt
    have hts : t ≤ s := by
      simp only at h2'
      omega
    refine ⟨s - t, by omega, ?_⟩
    have hcast : ((s - t : ℕ) : ℤ) = (s : ℤ) - (t : ℤ) := by omega
    rw [Prod.ext_iff]
    refine ⟨?_, ?_⟩ <;> simp only [hcast]
  · intro hw
    obtain ⟨m, hm, rfl⟩ := hw
    refine ⟨⟨(-(m : ℤ), 2 * (m : ℤ)), ⟨m, hm, rfl⟩, 0, by simp⟩, ?_⟩
    refine eq_true ?_
    show (0 : ℤ) ≤ ((-(m : ℤ), 2 * (m : ℤ)) + uray i).2
    simp only [uray, Prod.snd_add]
    omega

theorem hatOf_ray (i : ℕ) : hatOf Aray kkdeg vray i = Aray i := by
  ext z
  simp [Nivat.Colle35.hatOf_eq, kkdeg]

theorem iUnion_hatOf_ray : (⋃ i, hatOf Aray kkdeg vray i) = Rdeg := by
  ext z
  simp only [Set.mem_iUnion, hatOf_ray, Aray]
  constructor
  · rintro ⟨i, t, -, rfl⟩
    exact ⟨t, rfl⟩
  · rintro ⟨t, rfl⟩
    exact ⟨t, t, by omega, rfl⟩

theorem finite_Aray (i : ℕ) : (hatOf Aray kkdeg vray i).Finite := by
  rw [hatOf_ray]
  exact finite_Adeg (i + 1)

theorem mono_Aray (i j : ℕ) (hij : i ≤ j) :
    hatOf Aray kkdeg vray i ⊆ hatOf Aray kkdeg vray j := by
  rw [hatOf_ray, hatOf_ray]
  exact mono_Adeg _ _ (by omega)

/-- ⭐ **`maxA` 在位移族上成立**。第二、三支塌掉是因为约束集恰好等于 `A i`。 -/
theorem maxA_ray (i : ℕ) :
    IsMaxEnvIn (EnvOf (↑Sray : Set (ℤ × ℤ)))
      (canonA etaRay xperRay vray Bray uray i) (Aray i) := by
  refine ⟨enveloped_Adeg (M := i + 1) (by omega), ?_, ?_⟩
  · intro z hz
    rw [canonA_ray i]
    exact hz
  · intro T _ _ hTC z hz
    rw [canonA_ray i] at hTC
    exact hTC hz

/-- ⭐⭐ **总结论：同一个居民 `Rdeg`，`maxA` 可满足。**
`A` 换成 `Aray` 之后 union / 有限 / 单调三条一起给出 ⟹ hlev 两条 bundle 的前提表
再加一条 `maxA` 仍然可反，`maxA` 不是那两条的挡板。

⛔ **射程自限（§50，集成者第 244 轮入库条件 ①）**：本条兑现的是 `maxA` ＋ union ＋ 有限
＋ 单调**四条**，而 `ChainDataGeomParts` 共 **37 字段**（口径是 `ChainPartsFeed.lean` 那条
内核 `run_cmd`，不用正则数）。⟹ 准确措辞只有一句：**「`maxA` 不是 hlev 那二十条几何前提的
挡板」**。以下三句都**不是**本条的结论，不许下游放大：
1. **不是**「`Rdeg` 是链上构型」——未兑现的字段见本文件抬头那张清单
   （`envB` / `envShift` / `subBA` / `subAB` / `escapeW` / `shellSubStrip` / `shellEnv` /
   `fillCover` / `nfp_L` / `F` 的其余部分）。
2. **不是**「那二十条 ＋ 全部字段仍推不出覆盖」。
3. **不是**「`Rdeg` 满足 `rec_vJ`」——恰恰相反，hlev `TowerHlevCover.not_rec_vJ_Rdeg` 证明
   它对 `vJ = (1,0)` **不**封闭；这与本条不冲突，因为 `rec_vJ_of_parts` 另吃
   `hsweep` / `hhp` / `hswept` / `F.dot_nJ_vJ` / `bottom` 五条。
4. ⚠ **合成不是内核对象**（hlev 第 245 轮要求写明，我同意）：本条与他那两条 bundle 分居两个
   文件，「含 `maxA` 的前提表同样可反」目前是**两份 docstring 的交叉记账**，不是一条内核件。
   要内核件得在本文件**下游**另写实例化。别把本条读成「`maxA` 已经打进那二十条前提表了」。

⭐ **相容性（§38.3 加强形，入库条件 ②）**：集成者点名的两条已证推论
`EnvRefuteOrient.dot_nJ_p_pos_of_parts` 与 `det_p_vJ_mul_det_p_vJ1_nonneg` 的证明体只吃
并集层字段（`hhp` / `ahat_nonempty` / `rec_p` / `hswept` / `ahat_halfPlane_L`）＋ 向量
`nJ` / `vJ` / `vJ1` / `p`，而本见证**不提供这些向量** ⟹ 那两条对本见证不可陈述，按 §84
我不报「满足」。真正能咬的是 `RecVJFromParts.latticeConvex_of_parts`：它经
`Colle35.latticeConvex_iUnion_hatOf` **只吃 `maxA` ＋ `hfin` ＋ `AhatMono`**，恰是本见证
兑现的那一包 ⟹ 非空真可检验，内核收下了合成（收据
`tmp/wip/lane-env-refute-maxa-compat.lean` 的 `latticeConvex_of_ray_fields`，`EXIT=0`、
公理全白；按 §91 射程 ≡ hlev `latticeConvex_Rdeg`，故不落主仓）。
数值侧（`tmp/_maxa_compat.py`，哨兵已响，四个向量从 `TowerHlevCover.lean` 的
`rec_p_Rdeg` / `hhp_Rdeg` / `not_rec_vJ_Rdeg` / `prim_1m2` 亲读）：
`dot nJ p = 2 > 0`、`det p vJ * det p vJ1 = -2 * 0 = 0 ≥ 0`、`|det p vJ| = 2 = dot nJ p`、
`dot nJ vJ1 = -2 < 0`、`det vl vJ1 = 0`（共线格）；独立复算
`det p vJ • (-p.2, p.1) = (4,2)` 与他 `nL_eq` 逐字相同。
⚠ **零余量**：两个乘积都恰好取 **0**（因 `p = -vJ1`）⟹ 本见证只检验非严格推论，
**对任何严格不等式推论不构成检验**。具体后果（hlev 第 245 轮指出，我复算同意）：
hbase 那个 `hslice` 反例的分格量是 `1 > 0`（严格同号格），⟹ **本见证测不到那一格**，
两组数据是两个台架，不能互换。

⭐ **第 246 轮补记（三条，都缩小本条射程，不扩大）**

**(5) `escapeW` 是比 `maxA` 更靠后的那道闸，且它已被杀。** hlev 在本台架上内核化了
`escapeW` 字段那条语句为假（`tmp/wip/hlev-escapew-guard.lean`，横截 `w`；守卫那一格
由本文件 `enveloped_Adeg` 兑现，故**不是空胜**）。⟹ 本条「`maxA` 不是挡板」仍然成立且
不受影响——两条管的是不同的闸。⚠ 但**别把那条读成本条 (4) 解了**：他走的是
`enveloped_Adeg`，**没有**走 `maxA_ray`，兑现的是包络守卫那一格，而 (4) 说的是
`maxA` ＋ union ＋ 有限 ＋ 单调四条打进前提表。(4) 的自限原样保留。
⚠ 他自己的射程自限也一并记下（我复算同意）：shell 退化成直线，**既可**归因共线格、
**也可**归因 `Rdeg` 本身一维，**分不开** ⟹ 能站住的只有「`Rdeg` 这一族一维见证扩不成
完整的 `ChainDataGeomParts`，卡在 `escapeW`」，**不是**「共线格的债落在 `escapeW` 上」。

**(5.1) ⭐ 第 247 轮：上一段那个「分不开」已经分开了，级别 ③（我亲自复跑，不是转述）。**
hlev 的 `tmp/wip/hlev-escapew-2d.lean` 我用 `check1.sh` 重跑：`EXIT=0`，30 条公理行全白
（`A + B = 30 == 30` 条 `^#print axioms`，哨兵 `ZZZnope` 读 0；树侧读数取自 180 s 内
`.olean` 变更数 = 0 / 共 447 个，故按盲区 1 用 `check1.sh` 合法）。我亲读的两件是：
* **一般形（不含任何台架常数）** `escapeW_concl_false_of_thin`：`Â_i ⊆ Â_∞`
  ＋ `hthin : ∀ z ∈ Â_∞, det u z = k`
  ＋ `hpar : det u vJ1 = 0` ＋ `hw : det u w ≠ 0` ⟹ `escapeW` 的**结论**为假。
  机制 `det u (g + t•w) = k + t·det u w`，shell 那一侧逼出它 `= k` ⟹ `t = 0` ⟹ 逃出点就是
  `g` 自己。⟹ 死因的**正面**归因有内核件，不靠两点对照。
* **两点对照** `escapeW_dim_separation`（六合取）：我逐个形参核对过参数位
  （`EscapeWStmt S Ahat vJ1 nJ w cJ I₀`），两台架**逐字同**的是 `nJ = (0,1)`、
  `w = (-1,-1)`、`cJ = 0`，两边守卫（`ShellEnvStmt`）都被兑现 ⟹ 都不是空真，而
  `escapeW` 真值一边真一边假。

⟹ 本条 (5) 的死因栏改口径：**死因是「`Â_∞` 沿 `vJ1` 方向细 ＋ `w` 横截那条直线」**
（两条都在一般形的前提里），**不是**「共线」。以后写「`Rdeg` 这一族兑现不了完整
`ChainDataGeomParts`」时死因栏照此写。⛔ 三句不许写（hlev 自己也这么自限，我同意）：
**不是**「二维 ⟹ `escapeW` 成立」（那是一般命题，两点对照分母 2，测不到）；
**不是**「`escapeW` 在链上成立」；**不是**「共线格没问题」（共线的其它债不受影响）。
⚠ 我自己再补一条他没写的精确化：一般形里的 `hpar` 是 `det u vJ1 = 0`（`u` ＝ 那条细直线的
配对向量），**不是**共线判据 `det vl vJ1 = 0`——两者同名不同物，别互相代入（规矩 97）。
本条 (5) 原文（上一段）不撤、不删，保留为第 246 轮当时的事实（§103 / §105）。

**(6) ⛔ `subBA` / `subAB` 在本台架上是退化兑现，鉴别力为零**（hlev 第 246 轮指出，我复核
属实）：`Aray` 与 `Bray` 两个 `def` 取的是同一个集合（都是 `Adeg (i+1)`）⟹ 这两条字段
塌成 `subset_rfl`。对本条无害（本见证不需要它们不同），但**任何人拿这族台架去测
`subBA` / `subAB` 都会拿到假的绿灯**。⟹ 记分时这两条必须与真兑现分开列。

**(7) `nfp_L` 在本台架上测不出来，但根因是 `xperRay` 而不是台架（②，数值未内核化）。**
`xperRay := fun _ => True` 常值 ⟹ `PeriodicOnWith xperRay U h` 对**任意** `U`、任意
`h ≠ 0` 恒成立（`η (g+h) = η g` 是 `rfl`）⟹ `nfp_L` 恒假，且没测到 `cL` / `p` / `vJ`
中的任何一个（hlev `nfp_L_false_on_ray`）。
但这**不是**「本族天然测不了 `nfp_L`」：`nfp_L` 的载体是二维半平面
`{z | cL ≤ ⟪det p vJ • (-p.2, p.1), z⟫}`（字段原文见 `ChainPartsFeed.lean` 的 `nfp_L`），
而 `canonA_ray` 只在**一维射线** `{(-m, 2m)}` 上对 `xper` 有要求——逐分支推：该留的点要
`(0 ≤ w.2) = xper w` 成立、该切的点要它不成立，**两支都只逼出「`xper w` 真」**，不逼出常值。
⟹ 射线之外 `xper` 完全自由。取 `cL = 0`（由 `ahat_attained_L` 逼出）、
`xper z := (⟪(4,2), z⟫ = 0)` 时数值上 `nfp_L` **成立**（周期格塌成一维，哨兵已响，
`tmp/` 收据）。⚠ 这一段是**数值 ②**，未内核化，且换 `xper` 后 `canonA_ray` 的证明体要改
一处（`maxA_ray` / `enveloped_Adeg` / `hatOf_ray` / `iUnion_hatOf_ray` 不提 `xper`，不动）。

**(7.1) ⭐ 第 247 轮：上一段那个「数值 ②」已内核化，升 ③。** 收据
`tmp/wip/lane-env-refute-nfpl.lean`（七条声明，`EXIT=0`，公理行全白；本轮在树
`.olean` 180 s 静默、447 个齐全的状态下**重跑过一次**）。落地的是
`exists_maxA_and_nfpL_for_ray`：同一个居民 `Rdeg`，`maxA` ＋ union ＋ 有限 ＋ 单调
**照旧兑现**，而 `xper` 换成 `xperNfp z := (dot (4,2) z = 0)` 之后 `nfp_L` 字段那条语句
**成立**（`nfp_L_ray_nfp`），并且 `¬ ∀ z, xper z` 也在结论里 ⟹ 非退化性本身进了内核，
不只是口头。载体逐字保留 `det p vJ` 槽（`{z | 0 ≤ dot (det pray vJray • (-pray.2, pray.1)) z}`，
规矩 62(i)），`cL = 0` 是**代入的常数**，不是「`ahat_attained_L` 逼出 `cL = 0`」这个主张。
上一段预言的「证明体要改一处」命中：`canonA_ray_nfp` 里由 `of_eq_true`/`eq_true` 换成
`cast`/`propext`，其余四条不动。⚠ 本条与 (5.1) 合起来的净效果是**分母措辞**变化而不是数变：
`escapeW` 仍**杀**这族台架（死因见 (5.1)）。原文（上一段）保留为当时事实。 -/
theorem exists_maxA_for_ray :
    ∃ (S : Finset (ℤ × ℤ)) (η xper : Config Prop) (A B : ℕ → Set (ℤ × ℤ)) (u : ℕ → ℤ × ℤ),
      (⋃ i, hatOf A kkdeg ((1 : ℤ), (-2 : ℤ)) i) = Rdeg
      ∧ (∀ i, (hatOf A kkdeg ((1 : ℤ), (-2 : ℤ)) i).Finite)
      ∧ (∀ i j, i ≤ j → hatOf A kkdeg ((1 : ℤ), (-2 : ℤ)) i
          ⊆ hatOf A kkdeg ((1 : ℤ), (-2 : ℤ)) j)
      ∧ (∀ i, IsMaxEnvIn (EnvOf (↑S : Set (ℤ × ℤ)))
          (canonA η xper ((1 : ℤ), (-2 : ℤ)) B u i) (A i)) :=
  ⟨Sray, etaRay, xperRay, Aray, Bray, uray,
    iUnion_hatOf_ray, finite_Aray, mono_Aray, maxA_ray⟩

/-! ## 公理表（规矩 125：覆盖本文件全部 26 条声明，含 `def`） -/

#print axioms Nivat.EnvRefuteMaxA.dot_perp_Adeg
#print axioms Nivat.EnvRefuteMaxA.face_eq_self
#print axioms Nivat.EnvRefuteMaxA.zero_mem_Adeg
#print axioms Nivat.EnvRefuteMaxA.one_mem_Adeg
#print axioms Nivat.EnvRefuteMaxA.E_Adeg
#print axioms Nivat.EnvRefuteMaxA.encard_E_Adeg
#print axioms Nivat.EnvRefuteMaxA.E_Adeg_zero
#print axioms Nivat.EnvRefuteMaxA.not_enveloped_Adeg_zero_one
#print axioms Nivat.EnvRefuteMaxA.not_maxA_Adeg
#print axioms Nivat.EnvRefuteMaxA.Aray
#print axioms Nivat.EnvRefuteMaxA.Bray
#print axioms Nivat.EnvRefuteMaxA.uray
#print axioms Nivat.EnvRefuteMaxA.etaRay
#print axioms Nivat.EnvRefuteMaxA.xperRay
#print axioms Nivat.EnvRefuteMaxA.vray
#print axioms Nivat.EnvRefuteMaxA.Sray
#print axioms Nivat.EnvRefuteMaxA.coe_Sray
#print axioms Nivat.EnvRefuteMaxA.latticeConvex_Adeg
#print axioms Nivat.EnvRefuteMaxA.enveloped_Adeg
#print axioms Nivat.EnvRefuteMaxA.canonA_ray
#print axioms Nivat.EnvRefuteMaxA.hatOf_ray
#print axioms Nivat.EnvRefuteMaxA.iUnion_hatOf_ray
#print axioms Nivat.EnvRefuteMaxA.finite_Aray
#print axioms Nivat.EnvRefuteMaxA.mono_Aray
#print axioms Nivat.EnvRefuteMaxA.maxA_ray
#print axioms Nivat.EnvRefuteMaxA.exists_maxA_for_ray

end Nivat.EnvRefuteMaxA
