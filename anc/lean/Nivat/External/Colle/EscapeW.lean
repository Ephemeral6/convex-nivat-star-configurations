/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.ChainExhaustInter

/-!
# `escapeW`，已证（`I₀` 形状，第 162 轮签名）

Lane `lane-tower-hlev`，第 164 轮（2026-09-24）落地。0 `sorry`，只 import
`ChainExhaustInter`（不 import `RegionSteps` / `ColleRegion` / `Case2WindowProbe` /
`NfpLPreamble`，不成环）。

**目标**：`escapeW`，逐字符就是 `ChainDataGeom.ofPartsExhaustsInter`
（`ChainDataGeom.ofPartsExhaustsInter` 的 `escapeW` 字段，`ChainExhaustInter.lean`）那条 binder：

```
∀ ε i₀ : ℕ, 0 < ε →
  (∀ i, i₀ ≤ i → Env (ShellMink.shellInter …)) →
  ∀ i, max i₀ I₀ ≤ i → ∃ g ∈ hatOf A kk vl i, ∃ t : ℕ,
    g + (t : ℤ) • w ∈ MaxEnv.shell (⋃ i, hatOf A kk vl i) vJ1 nJ cJ ε ∧
    g + (t : ℤ) • w ∉ hatOf A kk vl i
```

原文 `scratch/b3_colle2.txt:530`「which contradicts the maximality of `Â_i`」的甲端
（`Â_i^{(ε)} ⊋ Â_i`，纯几何、与 `:516` 的反证假设无关，裁决见 `ChainExhaustInter.lean` 抬头）。
`I₀` 是 `:520` 的第二个常数，`:524`「if we consider `i ≥ max{i₀, I₀}`」。

## 证法（一句话）

把 `Â_i` 里一个**高度恰为 `cJ + T·D - 1`** 的点沿 `w` 走 `T` 步，落到高度 `cJ - 1`：

* 落点在 `shell` 里，因为 `T • w = a • vJ + bb • vJ1`（二维 Cramer，`cramer_2d`），而
  `dot nJ vJ = 0` 逼出 `bb · (-dot nJ vJ1) = T · (-dot nJ w) > 0`，所以 `bb > 0`；
  先用 `rec_vJ` 把起点沿 `vJ` 平移 `max (-a) 0` 步（不改高度），`a` 的符号就不重要了，
  落点写成 `(Â_∞ 的点) + bb • vJ1`，正是 `reachSet … vJ1`；高度 `cJ - 1 ≥ cJ - ε`（`0 < ε`）。
* 落点**不在** `Â_i` 里，因为高度 `cJ - 1 < cJ`，而 `hhp : Â_i ⊆ halfPlaneGE nJ cJ`。
  这一步是白送的：不需要任何关于 `Â_i` 形状的信息。

唯一要干活的是**那个高度存在**。它不需要格凸性，只用三条 binder：

* `bottom` 字段（同结构，`ChainExhaustInter.lean`）在 `ε := (-dot nJ vJ1).toNat` 处给出一个
  `reachSet` 点，回代出 `q ∈ Â_∞` 且 `dot nJ q ≡ cJ - 1 (mod -dot nJ vJ1)`；
* `rec_p` + `dot_nJ_p` 把高度**抬**（`dot_p_pos`：`hhp` + 非空逼出 `0 < dot nJ p`）；
* `hswept` 把高度**降**（只要不掉到 `cJ` 以下）。

抬 `d1 · j` 步 `p`、降 `j · dp - c` 步 `vJ1`，落在高度 `cJ + T·D - 1` 上——同余对得上，
因为 `d1 ∣ T·D`（即 `bb · d1 = T · D`）。

## 用到 / 没用到

用到的 binder：`AhatMono` `hsweep` `hhp` `hswept` `ahat_nonempty` `hsweepW` `rec_p`
`dot_nJ_p` `bottom`，外加 `dot nJ vJ = 0`（`FaceBlock.dot_nJ_vJ`）、`vJ ≠ 0`（`vJ_prim`）、
`rec_vJ`（`ofPartsExhaustsInter` 体内的 `rec_vJ'`，`rec_vJ_of_bottom` 产）。

**没用到**守卫 `∀ i, i₀ ≤ i → Env (shellInter …)`，没用到 `hEnv` / `envB` / `maxA`，
没用到格凸性，没用到 `:516` 的反证假设。所以本证明不落在 `PROTOCOL.md §40` 说的那种
「条件形式照样编译」的坑里。

⚠ 口径（第 163 轮 lane-tower-hlev 收据，`tmp/wip/lane-tower-hlev-escapew.lean` §10）：
**「不需要守卫」≠「守卫惰性」**。本文件证明的是前者；后者是假的——`envOf_guard_false_on_box`
见证守卫在 `Env := EnvOf ↑S` 下把 `E (shellInter … i)` 钉成对 `i` 常值，是承重的。

`I₀` 与 `ε`、`i₀` 都**无关**（构造里唯一的 `ε` 是 `bottom` 自己的 `(-dot nJ vJ1).toNat`，
不是结论里的那个 `ε`），和 lane-leafa-gen 的 `exists_threshold_genClosure` 同形。

## §5：`I₀` 合流

⚠ **2026-09-25 订正**：`I₀` 在 Parts 层是**字段**（`ChainAsm.Aparts.ChainDataGeomParts` 的
`I₀` 字段，`ChainPartsFeed.lean`），不是输入 binder——字段即「生产者自己选」，
正是本节结论 `∃ I₀` 要的形。本节下文说的「一条 `I₀` 被三条字段共用」，
指的是同一个结构里 `escapeW` / `shellSubStrip` / `fillCover` 共用**那一个字段**，
所以合流仍然要做，但它是生产侧的事，**不再是签名欠账**。
接线见 `Nivat.LaneTowerHlevEscWire.chainDataGeomParts_of_chain_escapeW_free`
（`TowerHlevEscapeWire.lean`）。

`escapeW` / `shellSubStrip` / `fillCover` 三条字段共用一个 `I₀`，而生产者不止一个。
三条尾部都是 `∀ i, max i₀ I₀ ≤ i → P i`，对 `I₀` **反单调**
（`I₀` 越大前件越难满足），所以取各生产者给的 `I₀` 的 `max` 即可。
`tail_mono_I₀` / `escapeW_mono_I₀` 是这一步的削弱引理，`tail_of_strong` 供
不使用 `I₀`（尾部为 `∀ i, i₀ ≤ i`，更强）的生产者接入。
-/

set_option autoImplicit false

namespace Nivat.LaneTowerHlevEscPos

open Nivat Nivat.LE2 Nivat.MaxEnv

/-! ## §0  记号引理 -/

/-- `⟪n, ·⟫` 是加性的。 -/
theorem dot_add_esc (n z y : ℤ × ℤ) : dot n (z + y) = dot n z + dot n y := by
  simp only [dot, Prod.fst_add, Prod.snd_add]; ring

/-- `⟪n, ·⟫` 对 `ℤ`-数乘是齐次的。 -/
theorem dot_zsmul_esc (n : ℤ × ℤ) (c : ℤ) (z : ℤ × ℤ) : dot n (c • z) = c * dot n z := by
  simp only [dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

/-- **二维 Cramer 恒等式**：`det u v • z = det z v • u + det u z • v`，对任意三个向量成立
（不需要 `det u v ≠ 0`）。 -/
theorem cramer_2d (u v z : ℤ × ℤ) : det u v • z = det z v • u + det u z • v := by
  obtain ⟨u1, u2⟩ := u
  obtain ⟨v1, v2⟩ := v
  obtain ⟨z1, z2⟩ := z
  simp only [det, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, Prod.mk.injEq]
  constructor <;> ring

/-- `vJ ⊥ nJ`、`vJ ≠ 0`、`vJ1` 不在 `ℓ_J` 上 ⟹ `vJ` 与 `vJ1` 无关。 -/
theorem det_ne_zero_of_perp {vJ vJ1 nJ : ℤ × ℤ} (hvJ : dot nJ vJ = 0) (hvJne : vJ ≠ 0)
    (hne : dot nJ vJ1 ≠ 0) : det vJ vJ1 ≠ 0 := by
  intro hdet
  apply hvJne
  obtain ⟨x, y⟩ := vJ
  have e1 : x * dot nJ vJ1 = nJ.2 * det ((x, y) : ℤ × ℤ) vJ1 + vJ1.1 * dot nJ ((x, y) : ℤ × ℤ) := by
    simp only [dot, det]; ring
  have e2 : y * dot nJ vJ1
      = -(nJ.1 * det ((x, y) : ℤ × ℤ) vJ1) + vJ1.2 * dot nJ ((x, y) : ℤ × ℤ) := by
    simp only [dot, det]; ring
  rw [hdet, hvJ] at e1 e2
  simp only [mul_zero, neg_zero, add_zero] at e1 e2
  have hx : x = 0 := by
    rcases mul_eq_zero.mp e1 with h | h
    · exact h
    · exact absurd h hne
  have hy : y = 0 := by
    rcases mul_eq_zero.mp e2 with h | h
    · exact h
    · exact absurd h hne
  simp [hx, hy]

/-- 沿一条正向递归方向走 `n` 步不出集合。 -/
theorem rec_iter {U : Set (ℤ × ℤ)} {v : ℤ × ℤ} (h : ∀ g ∈ U, g + v ∈ U) :
    ∀ (n : ℕ) (g : ℤ × ℤ), g ∈ U → g + (n : ℤ) • v ∈ U := by
  intro n
  induction n with
  | zero => intro g hg; simpa using hg
  | succ k ih =>
    intro g hg
    have hmem := ih (g + v) (h g hg)
    have heq : g + v + (k : ℤ) • v = g + ((k + 1 : ℕ) : ℤ) • v := by
      push_cast [add_smul, one_smul]; abel
    rwa [heq] at hmem

/-- **`0 < dot nJ p`**：`rec_p` 把 `Â_∞` 往 `p` 方向无限推，而 `hhp` 把它关在
`{⟪n_J, ·⟫ ≥ c_J}` 里，所以 `p` 不能压低高度；`dot_nJ_p` 排掉零。 -/
theorem dot_p_pos {U : Set (ℤ × ℤ)} {p nJ : ℤ × ℤ} {cJ : ℤ}
    (hne : U.Nonempty) (hhp : ∀ g ∈ U, cJ ≤ dot nJ g)
    (rec_p : ∀ g ∈ U, g + p ∈ U) (hp : dot nJ p ≠ 0) : 0 < dot nJ p := by
  rcases lt_trichotomy (dot nJ p) 0 with h | h | h
  · exfalso
    obtain ⟨g, hg⟩ := hne
    have hmem := rec_iter rec_p (dot nJ g - cJ + 1).toNat g hg
    have hlev : dot nJ (g + (((dot nJ g - cJ + 1).toNat : ℕ) : ℤ) • p)
        = dot nJ g + (((dot nJ g - cJ + 1).toNat : ℕ) : ℤ) * dot nJ p := by
      rw [dot_add_esc, dot_zsmul_esc]
    have hge := hhp _ hmem
    rw [hlev] at hge
    have hN : dot nJ g - cJ + 1 ≤ (((dot nJ g - cJ + 1).toNat : ℕ) : ℤ) := Int.self_le_toNat _
    have hNnn : (0 : ℤ) ≤ (((dot nJ g - cJ + 1).toNat : ℕ) : ℤ) := Int.natCast_nonneg _
    have hdp1 : dot nJ p ≤ -1 := by omega
    have hmul : (((dot nJ g - cJ + 1).toNat : ℕ) : ℤ) * dot nJ p
        ≤ (((dot nJ g - cJ + 1).toNat : ℕ) : ℤ) * (-1) :=
      mul_le_mul_of_nonneg_left hdp1 hNnn
    linarith
  · exact absurd h hp
  · exact h

/-! ## §1  `w` 的 `(vJ, vJ1)`-分解

`T • w = a • vJ + bb • vJ1`，`T > 0`，`bb > 0`。`a` 的符号不受控，但下面用 `rec_vJ`
平移起点把它吸收掉。 -/

/-- **分解引理**。`T`、`bb` 都严格为正；`bb * (-⟪n_J, v_{J+1}⟫) = T * (-⟪n_J, w⟫)`
（写成 `T * dot nJ w = bb * dot nJ vJ1`）是后面对同余的唯一依据。 -/
theorem exists_decomp_w {vJ vJ1 nJ w : ℤ × ℤ} (hvJ : dot nJ vJ = 0) (hvJne : vJ ≠ 0)
    (hsweep : dot nJ vJ1 < 0) (hsweepW : dot nJ w < 0) :
    ∃ T a bb : ℤ, 0 < T ∧ 0 < bb ∧ (T • w = a • vJ + bb • vJ1) ∧
      T * dot nJ w = bb * dot nJ vJ1 := by
  have hdet : det vJ vJ1 ≠ 0 := det_ne_zero_of_perp hvJ hvJne (by omega)
  have hid : det vJ vJ1 • w = det w vJ1 • vJ + det vJ w • vJ1 := cramer_2d vJ vJ1 w
  have hlev : ∀ (T a bb : ℤ), (T • w = a • vJ + bb • vJ1) →
      T * dot nJ w = bb * dot nJ vJ1 := by
    intro T a bb h
    have := congrArg (dot nJ) h
    rw [dot_zsmul_esc, dot_add_esc, dot_zsmul_esc, dot_zsmul_esc, hvJ, mul_zero, zero_add] at this
    exact this
  rcases lt_trichotomy (det vJ vJ1) 0 with hlt | h0 | hgt
  · refine ⟨-det vJ vJ1, -det w vJ1, -det vJ w, by omega, ?_, ?_, ?_⟩
    · have heq : (-det vJ w) * dot nJ vJ1 = (-det vJ vJ1) * dot nJ w := by
        have := hlev (-det vJ vJ1) (-det w vJ1) (-det vJ w) (by
          rw [neg_smul, neg_smul, neg_smul, ← neg_add, hid])
        omega
      nlinarith
    · rw [neg_smul, neg_smul, neg_smul, ← neg_add, hid]
    · exact hlev _ (-det w vJ1) _ (by rw [neg_smul, neg_smul, neg_smul, ← neg_add, hid])
  · exact absurd h0 hdet
  · refine ⟨det vJ vJ1, det w vJ1, det vJ w, hgt, ?_, hid, hlev _ _ _ hid⟩
    have heq : det vJ w * dot nJ vJ1 = det vJ vJ1 * dot nJ w := (hlev _ _ _ hid).symm
    nlinarith

/-! ## §2  高度存在性：`Â_∞` 在 `cJ + T·D - 1` 上有点

`bottom` 给同余，`rec_p` 抬，`hswept` 降。 -/

/-- **目标高度上取得点**。`hbot` 是 `bottom` 字段（`ChainDataGeom.ofPartsExhaustsInter`，`ChainExhaustInter.lean`）的前两个合取
（`∀ ε` 形，本引理只在 `ε := (-dot nJ vJ1).toNat` 处用一次）。

结论的高度 `cJ - T * dot nJ w - 1` 就是 `cJ + T·D - 1`。 -/
theorem exists_mem_at_level {U : Set (ℤ × ℤ)} {p vJ vJ1 nJ w : ℤ × ℤ} {cJ : ℤ} {T : ℤ}
    (hUhp : ∀ g ∈ U, cJ ≤ dot nJ g)
    (hswept : SweptClosed U vJ1 nJ cJ)
    (hne : U.Nonempty)
    (rec_p : ∀ g ∈ U, g + p ∈ U) (hp : dot nJ p ≠ 0)
    (hvJ : dot nJ vJ = 0) (hsweep : dot nJ vJ1 < 0) (hsweepW : dot nJ w < 0)
    (hT : 0 < T) {bb : ℤ} (hTD : T * dot nJ w = bb * dot nJ vJ1)
    (hbot : ∀ ε : ℕ, ∃ (z₀ : ℤ × ℤ) (L : ℤ), dot nJ z₀ = cJ - (ε : ℤ) - 1 ∧
      ∀ k : ℤ, L ≤ k → z₀ + k • vJ ∈ reachSet U vJ1) :
    ∃ z ∈ U, dot nJ z = cJ - T * dot nJ w - 1 := by
  have hdp : 0 < dot nJ p := dot_p_pos hne hUhp rec_p hp
  -- §2.1  `bottom` 在 `ε := d₁` 处给出一个高度 `≡ cJ - 1 (mod d₁)` 的点 `q ∈ U`.
  obtain ⟨z₀, L, hz₀, hreach⟩ := hbot (-dot nJ vJ1).toNat
  have hcast : (((-dot nJ vJ1).toNat : ℕ) : ℤ) = -dot nJ vJ1 :=
    Int.toNat_of_nonneg (by omega)
  rw [hcast] at hz₀
  obtain ⟨q, hqU, s, hqs⟩ := hreach L le_rfl
  have hqlev : dot nJ q = cJ - 1 + (1 - (s : ℤ)) * dot nJ vJ1 := by
    have h := congrArg (dot nJ) hqs
    rw [dot_add_esc, dot_zsmul_esc, hvJ, mul_zero, add_zero, dot_add_esc, dot_zsmul_esc] at h
    rw [hz₀] at h
    linarith
  -- §2.2  目标高度与 `q` 的高度差是 `d₁` 的整数倍.
  obtain ⟨c, hcdef⟩ : ∃ c : ℤ, c = bb + 1 - (s : ℤ) := ⟨_, rfl⟩
  have hgap : (cJ - T * dot nJ w - 1) - dot nJ q = -(c * dot nJ vJ1) := by
    rw [hqlev, hcdef, hTD]; ring
  -- §2.3  抬 `d₁ * j` 步 `p`，再降 `j * dp - c` 步 `v_{J+1}`.
  obtain ⟨j, hjdef⟩ : ∃ j : ℕ, j = c.toNat := ⟨_, rfl⟩
  have hjge : c ≤ ((j : ℕ) : ℤ) := by rw [hjdef]; exact Int.self_le_toNat _
  have hjnn : (0 : ℤ) ≤ ((j : ℕ) : ℤ) := Int.natCast_nonneg _
  obtain ⟨d1, hd1def⟩ : ∃ d1 : ℕ, d1 = (-dot nJ vJ1).toNat := ⟨_, rfl⟩
  have hd1cast : ((d1 : ℕ) : ℤ) = -dot nJ vJ1 := by
    rw [hd1def]; exact Int.toNat_of_nonneg (by omega)
  obtain ⟨s', hs'def⟩ : ∃ s' : ℕ, s' = (((j : ℕ) : ℤ) * dot nJ p - c).toNat := ⟨_, rfl⟩
  have hs'cast : ((s' : ℕ) : ℤ) = ((j : ℕ) : ℤ) * dot nJ p - c := by
    rw [hs'def]
    refine Int.toNat_of_nonneg ?_
    nlinarith [hjnn, hjge, hdp]
  have hq' : q + ((d1 * j : ℕ) : ℤ) • p ∈ U := rec_iter rec_p (d1 * j) q hqU
  have hlev2 : dot nJ (q + ((d1 * j : ℕ) : ℤ) • p + ((s' : ℕ) : ℤ) • vJ1)
      = cJ - T * dot nJ w - 1 := by
    rw [dot_add_esc, dot_zsmul_esc, dot_add_esc, dot_zsmul_esc]
    push_cast
    rw [hd1cast, hs'cast]
    linear_combination -hgap
  refine ⟨q + ((d1 * j : ℕ) : ℤ) • p + ((s' : ℕ) : ℤ) • vJ1, hswept _ hq' s' ?_, hlev2⟩
  rw [hlev2]
  have h1 : T * dot nJ w ≤ T * (-1) := mul_le_mul_of_nonneg_left (by omega) (le_of_lt hT)
  linarith

/-! ## §3  `escapeW`，抽象族形 -/

/-- **`escapeW` 的抽象族形，0 sorry。**  `Ah` 就是 `hatOf A kk vl`；结论里的
`∃ I₀, ∀ ε i₀, … ∀ i, max i₀ I₀ ≤ i → …` 逐字符是 `escapeW` 字段
去掉那条守卫之后的样子——守卫是前提，不用它就可以丢。 -/
theorem exists_escape_abstract {Ah : ℕ → Set (ℤ × ℤ)} {p vJ vJ1 nJ w : ℤ × ℤ} {cJ : ℤ}
    (mono : ∀ i j, i ≤ j → Ah i ⊆ Ah j)
    (hhp : ∀ i, ∀ g ∈ Ah i, cJ ≤ dot nJ g)
    (hswept : SweptClosed (⋃ i, Ah i) vJ1 nJ cJ)
    (hne : (⋃ i, Ah i).Nonempty)
    (hsweep : dot nJ vJ1 < 0) (hsweepW : dot nJ w < 0)
    (hvJ : dot nJ vJ = 0) (hvJne : vJ ≠ 0)
    (rec_vJ : ∀ g ∈ ⋃ i, Ah i, g + vJ ∈ ⋃ i, Ah i)
    (rec_p : ∀ g ∈ ⋃ i, Ah i, g + p ∈ ⋃ i, Ah i)
    (dot_nJ_p : dot nJ p ≠ 0)
    (hbot : ∀ ε : ℕ, ∃ (z₀ : ℤ × ℤ) (L : ℤ), dot nJ z₀ = cJ - (ε : ℤ) - 1 ∧
      ∀ k : ℤ, L ≤ k → z₀ + k • vJ ∈ reachSet (⋃ i, Ah i) vJ1) :
    ∃ I₀ : ℕ, ∀ ε i₀ : ℕ, 0 < ε → ∀ i, max i₀ I₀ ≤ i →
      ∃ g ∈ Ah i, ∃ t : ℕ,
        g + (t : ℤ) • w ∈ MaxEnv.shell (⋃ i, Ah i) vJ1 nJ cJ ε ∧
        g + (t : ℤ) • w ∉ Ah i := by
  have hUhp : ∀ g ∈ ⋃ i, Ah i, cJ ≤ dot nJ g := by
    intro g hg
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hg
    exact hhp i g hi
  obtain ⟨T, a, bb, hT, hbb, hdecomp, hTD⟩ := exists_decomp_w hvJ hvJne hsweep hsweepW
  obtain ⟨z, hzU, hzlev⟩ :=
    exists_mem_at_level hUhp hswept hne rec_p dot_nJ_p hvJ hsweep hsweepW hT hTD hbot
  -- 把起点沿 `vJ` 平移 `max (-a) 0` 步，吸收 `a` 的符号；高度不变.
  set n0 : ℕ := (-a).toNat with hn0
  have hn0ge : -a ≤ ((n0 : ℕ) : ℤ) := Int.self_le_toNat _
  have hsum : 0 ≤ ((n0 : ℕ) : ℤ) + a := by omega
  set g : ℤ × ℤ := z + ((n0 : ℕ) : ℤ) • vJ with hg
  have hgU : g ∈ ⋃ i, Ah i := rec_iter rec_vJ n0 z hzU
  have hglev : dot nJ g = cJ - T * dot nJ w - 1 := by
    rw [hg, dot_add_esc, dot_zsmul_esc, hvJ, mul_zero, add_zero, hzlev]
  obtain ⟨i₁, hi₁⟩ := Set.mem_iUnion.mp hgU
  refine ⟨i₁, ?_⟩
  intro ε i₀ hε i hi
  have hgi : g ∈ Ah i := mono i₁ i (le_trans (le_max_right i₀ i₁) hi) hi₁
  have hTn : ((T.toNat : ℕ) : ℤ) = T := Int.toNat_of_nonneg (le_of_lt hT)
  have hbn : ((bb.toNat : ℕ) : ℤ) = bb := Int.toNat_of_nonneg (le_of_lt hbb)
  -- 落点：`g + T • w = (z + (n0 + a) • vJ) + bb • vJ1`.
  have hbase : z + (((((n0 : ℕ) : ℤ) + a).toNat : ℕ) : ℤ) • vJ ∈ ⋃ i, Ah i :=
    rec_iter rec_vJ _ z hzU
  rw [Int.toNat_of_nonneg hsum] at hbase
  have hland : g + ((T.toNat : ℕ) : ℤ) • w
      = (z + (((n0 : ℕ) : ℤ) + a) • vJ) + ((bb.toNat : ℕ) : ℤ) • vJ1 := by
    rw [hTn, hbn, hg, hdecomp, add_smul]
    abel
  have hlandlev : dot nJ (g + ((T.toNat : ℕ) : ℤ) • w) = cJ - 1 := by
    rw [dot_add_esc, dot_zsmul_esc, hTn, hglev]; ring
  refine ⟨g, hgi, T.toNat, ?_, ?_⟩
  · refine ⟨z + (((n0 : ℕ) : ℤ) + a) • vJ, hbase, bb.toNat, hland, ?_⟩
    rw [hlandlev]
    have : (1 : ℤ) ≤ (ε : ℤ) := by exact_mod_cast hε
    omega
  · intro hcon
    have := hhp i _ hcon
    rw [hlandlev] at this
    omega

/-! ## §4  `escapeW`，binder 形

`Ah := Nivat.Colle35.hatOf A kk vl`，逐字符就是 `escapeW` 字段
的结论（守卫作为前提被丢掉，见 §3 的 docstring）。 -/

/-- **`escapeW` 的 binder 形，0 sorry。**  结论里那条守卫
`(∀ i, i₀ ≤ i → Env (ShellMink.shellInter …))` 原样保留、原样不用。 -/
theorem exists_I₀_escapeW {A : ℕ → Set (ℤ × ℤ)}
    {kk : ℕ → ℕ} {vl p vJ vJ1 nJ w : ℤ × ℤ} {cJ : ℤ}
    {Env : Set (ℤ × ℤ) → Prop}
    (AhatMono : ∀ i j, i ≤ j → Nivat.Colle35.hatOf A kk vl i ⊆ Nivat.Colle35.hatOf A kk vl j)
    (hhp : ∀ i, Nivat.Colle35.hatOf A kk vl i ⊆ halfPlaneGE nJ cJ)
    (hswept : SweptClosed (⋃ i, Nivat.Colle35.hatOf A kk vl i) vJ1 nJ cJ)
    (ahat_nonempty : (⋃ i, Nivat.Colle35.hatOf A kk vl i).Nonempty)
    (hsweep : dot nJ vJ1 < 0) (hsweepW : dot nJ w < 0)
    (hvJ : dot nJ vJ = 0) (hvJne : vJ ≠ 0)
    (rec_vJ : ∀ g ∈ ⋃ i, Nivat.Colle35.hatOf A kk vl i,
      g + vJ ∈ ⋃ i, Nivat.Colle35.hatOf A kk vl i)
    (rec_p : ∀ g ∈ ⋃ i, Nivat.Colle35.hatOf A kk vl i,
      g + p ∈ ⋃ i, Nivat.Colle35.hatOf A kk vl i)
    (dot_nJ_p : dot nJ p ≠ 0)
    (hbot : ∀ ε : ℕ, ∃ (z₀ : ℤ × ℤ) (L : ℤ), dot nJ z₀ = cJ - (ε : ℤ) - 1 ∧
      ∀ k : ℤ, L ≤ k → z₀ + k • vJ ∈ reachSet (⋃ i, Nivat.Colle35.hatOf A kk vl i) vJ1) :
    ∃ I₀ : ℕ, ∀ ε i₀ : ℕ, 0 < ε →
      (∀ i, i₀ ≤ i → Env (ShellMink.shellInter (Nivat.Colle35.hatOf A kk vl i)
        (MaxEnv.shell (⋃ i, Nivat.Colle35.hatOf A kk vl i) vJ1 nJ cJ ε) w)) →
      ∀ i, max i₀ I₀ ≤ i → ∃ g ∈ Nivat.Colle35.hatOf A kk vl i, ∃ t : ℕ,
        g + (t : ℤ) • w ∈ MaxEnv.shell (⋃ i, Nivat.Colle35.hatOf A kk vl i) vJ1 nJ cJ ε ∧
        g + (t : ℤ) • w ∉ Nivat.Colle35.hatOf A kk vl i := by
  obtain ⟨I₀, hI₀⟩ :=
    exists_escape_abstract (Ah := Nivat.Colle35.hatOf A kk vl) AhatMono
      (fun i g hg => hhp i hg) hswept ahat_nonempty hsweep hsweepW hvJ hvJne rec_vJ rec_p
      dot_nJ_p hbot
  exact ⟨I₀, fun ε i₀ hε _ i hi => hI₀ ε i₀ hε i hi⟩

/-! ## §5  `I₀` 合流：三条尾部对 `I₀` 反单调

⚠ **2026-09-25 订正**：`I₀` 现在是 `ChainAsm.Aparts.ChainDataGeomParts`
（`ChainPartsFeed.lean`）的**字段**，不是输入 binder。字段即「生产者自己选」，
与本文件 `exists_I₀_escapeW` 交的 `∃ I₀` 同形 ⟹ **量词位置那条残差已关闭**。

同一个结构里 `escapeW`、`shellSubStrip`、`fillCover` 三条字段共用那**一个** `I₀` 字段，
而三条各有各的生产者、各自给出的阈值不同。三条尾部的形状都是
`∀ i, max i₀ I₀ ≤ i → P i`，`I₀` 只出现在前件里且是 `max` 的一支，所以命题对 `I₀`
**反单调**：在小 `I₀` 处成立就在大 `I₀` 处成立。接线取 `I₀ := max I₀e I₀f` 即可，
**不需要改签名**。已接好的那条是
`Nivat.LaneTowerHlevEscWire.chainDataGeomParts_of_chain_escapeW_free`
（`TowerHlevEscapeWire.lean`），它的 binder 表里既没有 `I₀` 也没有 `escapeW`。

⚠ **反单调性**买到的是「合流」，**不是** `ε`-一致性——两件事是独立的轴（lane-leafa-gen
2026-09-25 指出，本条照收）。反单调只说「`I₀` 变大更容易」；它**不说**「存在一个够用的
`I₀`」。若某条字段的逐 `(ε, i₀)` 阈值 `I₀(ε, i₀)` 随 `ε` 无界，再大的**单个** `I₀` 也不够，
而上面 `tail_mono_I₀` / `escapeW_mono_I₀` 不会对此报警。

本文件的 `∃ I₀` 形之所以成立，靠的是**另一件事**：`exists_escape_abstract` 里 `I₀ := i₁` 是在
`intro ε i₀ hε i hi` 之**前**由 `refine ⟨i₁, ?_⟩` 交出去的（`i₁` 来自 Cramer 分解
`exists_decomp_w` 那一步的落点 `g ∈ ⋃ i, Ah i`）。⟹ **`ε` 在 `i₁` 被选定时还不在作用域里**，
`ε`-一致性是项的构造顺序给的内核事实，不是签名形状、也不是反单调性给的。
⛔ 后果：若有人把 `escapeW` 换一条阈值依赖 `ε` 的证法，`∃ I₀` 形会当场断，而本节的两条
`mono` 引理照样编译（`PROTOCOL.md §40`）。改证法前先核这一句。

⚠ `fillCover` 一侧的 `ε`-一致性**本文件不表态**（lane-leafa-gen 在办，见
`FillCoverGuarded.lean` §8 的 `exists_I₀_of_per_normal`）。 -/

/-- **尾部对 `I₀` 反单调（一般形）**。三条 shell binder 的尾部同形，都可用这一条削弱。 -/
theorem tail_mono_I₀ {P : ℕ → Prop} {i₀ I₀ I₀' : ℕ} (hle : I₀ ≤ I₀')
    (h : ∀ i, max i₀ I₀ ≤ i → P i) : ∀ i, max i₀ I₀' ≤ i → P i :=
  fun i hi => h i (le_trans (max_le_max (le_refl i₀) hle) hi)

/-- **不使用 `I₀` 的生产者接入**。尾部为 `∀ i, i₀ ≤ i → P i`（比 binder 强）的生产者
（如 `shellSubStrip_of_pred`）用这一条填任意 `I₀`。 -/
theorem tail_of_strong {P : ℕ → Prop} {i₀ I₀ : ℕ} (h : ∀ i, i₀ ≤ i → P i) :
    ∀ i, max i₀ I₀ ≤ i → P i :=
  fun i hi => h i (le_trans (le_max_left i₀ I₀) hi)

/-- **`escapeW` 对 `I₀` 反单调**，binder 形。接线时把 `exists_I₀_escapeW` 给的 `I₀e`
削到 `max I₀e I₀f`：`escapeW_mono_I₀ (le_max_left I₀e I₀f) hI₀e`。 -/
theorem escapeW_mono_I₀ {A : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ} {vl vJ1 nJ w : ℤ × ℤ} {cJ : ℤ}
    {Env : Set (ℤ × ℤ) → Prop} {I₀ I₀' : ℕ} (hle : I₀ ≤ I₀')
    (h : ∀ ε i₀ : ℕ, 0 < ε →
      (∀ i, i₀ ≤ i → Env (ShellMink.shellInter (Nivat.Colle35.hatOf A kk vl i)
        (MaxEnv.shell (⋃ i, Nivat.Colle35.hatOf A kk vl i) vJ1 nJ cJ ε) w)) →
      ∀ i, max i₀ I₀ ≤ i → ∃ g ∈ Nivat.Colle35.hatOf A kk vl i, ∃ t : ℕ,
        g + (t : ℤ) • w ∈ MaxEnv.shell (⋃ i, Nivat.Colle35.hatOf A kk vl i) vJ1 nJ cJ ε ∧
        g + (t : ℤ) • w ∉ Nivat.Colle35.hatOf A kk vl i) :
    ∀ ε i₀ : ℕ, 0 < ε →
      (∀ i, i₀ ≤ i → Env (ShellMink.shellInter (Nivat.Colle35.hatOf A kk vl i)
        (MaxEnv.shell (⋃ i, Nivat.Colle35.hatOf A kk vl i) vJ1 nJ cJ ε) w)) →
      ∀ i, max i₀ I₀' ≤ i → ∃ g ∈ Nivat.Colle35.hatOf A kk vl i, ∃ t : ℕ,
        g + (t : ℤ) • w ∈ MaxEnv.shell (⋃ i, Nivat.Colle35.hatOf A kk vl i) vJ1 nJ cJ ε ∧
        g + (t : ℤ) • w ∉ Nivat.Colle35.hatOf A kk vl i :=
  fun ε i₀ hε hguard => tail_mono_I₀ hle (h ε i₀ hε hguard)

end Nivat.LaneTowerHlevEscPos

#print axioms Nivat.LaneTowerHlevEscPos.cramer_2d
#print axioms Nivat.LaneTowerHlevEscPos.det_ne_zero_of_perp
#print axioms Nivat.LaneTowerHlevEscPos.dot_p_pos
#print axioms Nivat.LaneTowerHlevEscPos.exists_decomp_w
#print axioms Nivat.LaneTowerHlevEscPos.exists_mem_at_level
#print axioms Nivat.LaneTowerHlevEscPos.exists_escape_abstract
#print axioms Nivat.LaneTowerHlevEscPos.exists_I₀_escapeW
#print axioms Nivat.LaneTowerHlevEscPos.tail_mono_I₀
#print axioms Nivat.LaneTowerHlevEscPos.tail_of_strong
#print axioms Nivat.LaneTowerHlevEscPos.escapeW_mono_I₀
-- ⚠ 补齐到逐声明 13/13。原先漏了下面三条（`tmp/_declaudit229.py` 报 missing=3）：
-- 「`EXIT=0` ＋ 上面这串干净」并不蕴含「每条声明都被审过」。
#print axioms Nivat.LaneTowerHlevEscPos.dot_add_esc
#print axioms Nivat.LaneTowerHlevEscPos.dot_zsmul_esc
#print axioms Nivat.LaneTowerHlevEscPos.rec_iter
