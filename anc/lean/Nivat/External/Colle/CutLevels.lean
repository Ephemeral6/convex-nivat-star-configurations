/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.L1Region

/-!
# `CutLevels`: the attained-distance sequence `0 = d₀ < d₁ < ⋯` (`b3_colle2.txt:816`)

原文：`b3_colle2.txt:816`

> Let `0 = d₀ < d₁ < ⋯ < d_n < ⋯` denote the sequence where, for each `g ∈ 𝓗(ℓ_I)`, there
> exists `i ∈ ℤ₊` such that `dist(g, ℓ_I) = d_i`.

两件事被这句话钉死：`d_n` 严格递增，且**每个 `d_n` 都被真正取到**（这正是
`L1Region.cut_ssubset`（`L1Region.lean:230`）的 `hgap` 所要的——取不到的距离会让
`𝓡^n_I ⊂ 𝓡^{n+1}_I` 退化成等号）。

编码对应（逐量词，硬规矩 7）：

| 原文 | 本文件 |
|---|---|
| `dist(·, ℓ'_{𝓡_I})`，`ℓ' = ℓ_I` | `Nivat.LE2.dot m ·`，`m` 是 `ℓ'` 的法向 |
| `d_n`（距离，递增） | `lev n = -d_n`（内积，递减）——`𝓡^n_I` 是 `dist ≤ d_n`，即 `dot m · ≥ lev n` |
| `d₀ = 0` | `lev 0 = b₀`，由消费者指定（`𝓡^0_I` 所在的那一层） |
| "for each `g ∈ 𝓗(ℓ_I)` there exists `i`" | `hexh`：`∀ b, ∃ n, lev n ≤ b`（层穷尽向下） |
| "there **exists** `g` with `dist(g,ℓ_I) = d_i`" | `hattained`：`∀ n, ∃ z ∈ Rinf, dot m z = lev n` |

⚠ 本文件**不**去构造「最大的更小值」。原文的 `d_n` 枚举**全部**被取到的距离，而
`ofCut`（`L1Region.lean:240`）只要一个见证点：任何**严格下降的已取到子列**都足以给出
`hlev` / `hexh` / `hgap` 三条。少枚举几个 `d_n` 只会让族 `𝓡^n_I` 上升得快一些，
`⋃_n 𝓡^n_I = 𝓡_{I−1}`（`:820`）由 `hexh` 照样成立——所以这是**比原文弱**的构造前提、
**等价**的构造输出，不是硬规矩 10 意义下的「白烧算力」。

消费者：`RegionSteps.lean:1554` `exists_cutResidualR_of_claim46` 要造的
`L1Claim.CutResidualR` 的 `hlev` / `hexh` / `hgap` 三个字段。
-/

namespace Nivat.CutLevels

open Nivat Nivat.LE2

/-- 由「下一个更低的已取到层」这一步函数迭代出的层序列。`levSeq f b₀ 0 = b₀`，
`levSeq f b₀ (n+1) = f (levSeq f b₀ n)`。对应原文 `:816` 的 `d_n`（符号相反）。 -/
private def levSeq (f : ℤ → ℤ) (b₀ : ℤ) : ℕ → ℤ
  | 0 => b₀
  | n + 1 => f (levSeq f b₀ n)

/-- **`0 = d₀ < d₁ < ⋯` 的存在性**（原文 `b3_colle2.txt:816`）。

`h0` = 「`b₀` 这一层被取到」（原文的 `d₀ = 0`，取在 `ℓ'_{𝓡_I}` 上）；
`hunb` = 「`dot m` 在 `Rinf` 上向下无界」（原文里 `𝓡_{I−1}` 含一条 `v⃗_{ℓ_{I−1}}` 射线，
所以离 `ℓ'` 任意远的点都有）。结论四条按上表逐一对应原文。 -/
theorem exists_lev_attained {Rinf : Set (ℤ × ℤ)} {m : ℤ × ℤ} {b₀ : ℤ}
    (h0 : ∃ z ∈ Rinf, Nivat.LE2.dot m z = b₀)
    (hunb : ∀ b : ℤ, ∃ z ∈ Rinf, Nivat.LE2.dot m z < b) :
    ∃ lev : ℕ → ℤ, lev 0 = b₀ ∧ StrictAnti lev ∧
      (∀ n, ∃ z ∈ Rinf, Nivat.LE2.dot m z = lev n) ∧
      (∀ b : ℤ, ∃ n, lev n ≤ b) := by
  classical
  -- 一步：任何整数层之下都还有一个**被取到**的层。
  have step : ∀ b : ℤ, ∃ b' : ℤ, b' < b ∧ ∃ z ∈ Rinf, Nivat.LE2.dot m z = b' := by
    intro b
    obtain ⟨z, hz, hlt⟩ := hunb b
    exact ⟨Nivat.LE2.dot m z, hlt, z, hz, rfl⟩
  choose f hflt hfat using step
  refine ⟨levSeq f b₀, rfl, ?_, ?_, ?_⟩
  · -- 严格下降
    refine strictAnti_nat_of_succ_lt ?_
    intro n
    exact hflt (levSeq f b₀ n)
  · -- 每一层都被取到
    intro n
    cases n with
    | zero => exact h0
    | succ k => exact hfat (levSeq f b₀ k)
  · -- 向下穷尽：整数严格下降每步至少减 1，故 `lev n ≤ b₀ - n`。
    have hbound : ∀ n : ℕ, levSeq f b₀ n ≤ b₀ - (n : ℤ) := by
      intro n
      induction n with
      | zero => simp [levSeq]
      | succ k ih =>
        have hlt : levSeq f b₀ (k + 1) < levSeq f b₀ k := hflt (levSeq f b₀ k)
        push_cast
        omega
    intro b
    refine ⟨(b₀ - b).toNat, ?_⟩
    have hb := hbound (b₀ - b).toNat
    omega

/-- **`exists_lev_attained` 打包成 `L1Region.ofCut` 的参数形状**（`L1Region.lean:240`）。

结论的后三条**逐字**是 `ofCut` 的 `hlev` / `hexh` / `hgap`；`lev 0 = b₀` 留在结论里，
是因为消费者要靠它把 `L1Region.cut Rinf m lev 0` 认成原文的 `𝓡^0_I`（`:818`，`d₀ = 0`）。

`hgap` 的见证点就是实现 `lev (n+1)` 的那个 `z`：`lev (n+1) ≤ dot m z` 取等号，
`dot m z = lev (n+1) < lev n` 由严格下降给出。 -/
theorem exists_lev_for_ofCut {Rinf : Set (ℤ × ℤ)} {m : ℤ × ℤ} {b₀ : ℤ}
    (h0 : ∃ z ∈ Rinf, Nivat.LE2.dot m z = b₀)
    (hunb : ∀ b : ℤ, ∃ z ∈ Rinf, Nivat.LE2.dot m z < b) :
    ∃ lev : ℕ → ℤ, lev 0 = b₀ ∧ Antitone lev ∧
      (∀ b : ℤ, ∃ n, lev n ≤ b) ∧
      (∀ n, ∃ z ∈ Rinf, lev (n + 1) ≤ Nivat.LE2.dot m z ∧ Nivat.LE2.dot m z < lev n) := by
  obtain ⟨lev, h00, hanti, hat, hexh⟩ := exists_lev_attained h0 hunb
  refine ⟨lev, h00, hanti.antitone, hexh, ?_⟩
  intro n
  obtain ⟨z, hz, hzeq⟩ := hat (n + 1)
  exact ⟨z, hz, le_of_eq hzeq.symm, hzeq ▸ hanti (Nat.lt_succ_self n)⟩

/-- **`𝓡_{I−1}` 在法向 `m` 上向下无界**（原文 `b3_colle2.txt:806`、`:818`）。

`exists_lev_for_ofCut` 的第二个前提 `hunb` 不是凭空要的：原文的 `𝓡_{I−1}` 按 `:806` 是
`𝓡_I + ℕ v⃗_{ℓ_{I−1}}`，即含一条 `v⃗_{ℓ_{I−1}}` 射线，而 `:818` 的 `dist(·, ℓ'_{𝓡_I}) ≤ d_n`
说明这正是**离 `ℓ'` 越来越远**的方向，在本文件的符号下就是 `dot m w < 0`（降层）。

⚠ 这条**不能**从 `Colle41.IsRegion Rinf vl u'` 推出来：`IsRegion` 给的两条射线方向是
`vl`（`hmu : 0 < dot m vl`，升层）与 `u'`（`hmu' : dot m u' = 0`，平层），两条都不降层。
降层射线是塔的构造给的，不是 region 谓词给的——所以它必须留在签名里（硬规矩 10：
少一个前提 = 证的是另一个命题）。 -/
theorem unbounded_below_of_ray {Rinf : Set (ℤ × ℤ)} {m z₀ w : ℤ × ℤ}
    (hray : ∀ k : ℕ, z₀ + (k : ℤ) • w ∈ Rinf)
    (hneg : Nivat.LE2.dot m w < 0) :
    ∀ b : ℤ, ∃ z ∈ Rinf, Nivat.LE2.dot m z < b := by
  intro b
  set K : ℕ := (Nivat.LE2.dot m z₀ - b).toNat + 1 with hK
  refine ⟨z₀ + (K : ℤ) • w, hray K, ?_⟩
  have hexp : Nivat.LE2.dot m (z₀ + (K : ℤ) • w)
      = Nivat.LE2.dot m z₀ + (K : ℤ) * Nivat.LE2.dot m w := by
    simp only [Nivat.LE2.dot, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul]
    ring
  rw [hexp]
  have hKpos : (0 : ℤ) ≤ (K : ℤ) := Int.natCast_nonneg _
  have hw1 : Nivat.LE2.dot m w ≤ -1 := by omega
  have hmul : (K : ℤ) * Nivat.LE2.dot m w ≤ (K : ℤ) * (-1) :=
    mul_le_mul_of_nonneg_left hw1 hKpos
  have hKge : Nivat.LE2.dot m z₀ - b < (K : ℤ) := by
    have : (Nivat.LE2.dot m z₀ - b) ≤ ((Nivat.LE2.dot m z₀ - b).toNat : ℤ) :=
      Int.self_le_toNat _
    push_cast [hK]
    omega
  omega

/-- **`exists_lev_for_ofCut` 的射线版**：把 `hunb` 换成原文 `:806` 直接给的那条射线。
这是 `L1Region.ofCut` 的 `hlev` / `hexh` / `hgap` 在阶段二里真正该用的入口。 -/
theorem exists_lev_for_ofCut_of_ray {Rinf : Set (ℤ × ℤ)} {m z₀ w : ℤ × ℤ} {b₀ : ℤ}
    (h0 : ∃ z ∈ Rinf, Nivat.LE2.dot m z = b₀)
    (hray : ∀ k : ℕ, z₀ + (k : ℤ) • w ∈ Rinf)
    (hneg : Nivat.LE2.dot m w < 0) :
    ∃ lev : ℕ → ℤ, lev 0 = b₀ ∧ Antitone lev ∧
      (∀ b : ℤ, ∃ n, lev n ≤ b) ∧
      (∀ n, ∃ z ∈ Rinf, lev (n + 1) ≤ Nivat.LE2.dot m z ∧ Nivat.LE2.dot m z < lev n) :=
  exists_lev_for_ofCut h0 (unbounded_below_of_ray hray hneg)

/-- **`d_n` 是相邻的**（原文 `b3_colle2.txt:816`：`0 = d₀ < d₁ < ⋯` 枚举**所有**被取到的距离）。
在 `exists_lev_for_ofCut` 的四条之外多给一条 `hconsec`：`lev n` 与 `lev (n+1)` 之间没有别的被取到的层，
于是 `cut Rinf m lev (n+1) \ cut Rinf m lev n` 恰是一条 `m`-层线（`:818` 的「gap 是一行」）。 -/
theorem exists_lev_consecutive {Rinf : Set (ℤ × ℤ)} {m : ℤ × ℤ} {b₀ : ℤ}
    (h0 : ∃ z ∈ Rinf, dot m z = b₀)
    (hunb : ∀ b : ℤ, ∃ z ∈ Rinf, dot m z < b) :
    ∃ lev : ℕ → ℤ, lev 0 = b₀ ∧ Antitone lev ∧
      (∀ b : ℤ, ∃ n, lev n ≤ b) ∧
      (∀ n, ∃ z ∈ Rinf, lev (n + 1) ≤ dot m z ∧ dot m z < lev n) ∧
      (∀ n, ∀ z ∈ Rinf, dot m z < lev n → dot m z ≤ lev (n + 1)) := by
  classical
  -- the greatest attained level strictly below `b`
  have step : ∀ b : ℤ, ∃ b' : ℤ, b' < b ∧ (∃ z ∈ Rinf, dot m z = b') ∧
      ∀ z ∈ Rinf, dot m z < b → dot m z ≤ b' := by
    intro b
    obtain ⟨z₀, hz₀, hlt₀⟩ := hunb b
    let P : ℕ → Prop := fun k => ∃ z ∈ Rinf, dot m z = b - 1 - (k : ℤ)
    have hP : ∃ k, P k := ⟨(b - 1 - dot m z₀).toNat, z₀, hz₀, by omega⟩
    have hk : P (Nat.find hP) := Nat.find_spec hP
    have hkmin : ∀ k', P k' → Nat.find hP ≤ k' := fun k' hk' => Nat.find_min' hP hk'
    obtain ⟨z, hz, hzeq⟩ := hk
    refine ⟨b - 1 - (Nat.find hP : ℤ), by omega, ⟨z, hz, hzeq⟩, ?_⟩
    intro y hy hylt
    have := hkmin (b - 1 - dot m y).toNat ⟨y, hy, by omega⟩
    omega
  choose f hflt hfat hfmax using step
  let lev : ℕ → ℤ := fun n => Nat.rec b₀ (fun _ l => f l) n
  have hlev_succ : ∀ n, lev (n + 1) = f (lev n) := fun _ => rfl
  have hanti : StrictAnti lev := strictAnti_nat_of_succ_lt fun n => by
    rw [hlev_succ]; exact hflt _
  refine ⟨lev, rfl, hanti.antitone, ?_, ?_, ?_⟩
  · have hbound : ∀ n : ℕ, lev n ≤ b₀ - (n : ℤ) := by
      intro n
      induction n with
      | zero => simp [lev]
      | succ k ih =>
        have := hflt (lev k)
        rw [hlev_succ]; push_cast; omega
    intro b
    refine ⟨(b₀ - b).toNat, ?_⟩
    have hb := hbound (b₀ - b).toNat
    omega
  · intro n
    obtain ⟨z, hz, hzeq⟩ := hfat (lev n)
    refine ⟨z, hz, ?_, ?_⟩
    · rw [hlev_succ]; omega
    · have := hflt (lev n); omega
  · intro n z hz hlt
    rw [hlev_succ]
    exact hfmax (lev n) z hz hlt

end Nivat.CutLevels

#print axioms Nivat.CutLevels.exists_lev_attained
#print axioms Nivat.CutLevels.exists_lev_for_ofCut
#print axioms Nivat.CutLevels.unbounded_below_of_ray
#print axioms Nivat.CutLevels.exists_lev_for_ofCut_of_ray
