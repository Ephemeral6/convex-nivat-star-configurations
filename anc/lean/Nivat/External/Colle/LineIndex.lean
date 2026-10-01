/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.ConeRegion

set_option autoImplicit false

/-!
# Cone-membership for translated windows (Figure 10)

This file proves that translating a seed set `S` with an apex vertex `a` preserves
cone membership when the seed lies in the cone spanned from `a` by `vl` and `u'`.

**原文：b3_colle2.txt:794-798** — Figure 10 shows `𝒮_{φ_ι}` (the seed) translated so
its extreme vertex sits at `w`, with all other points falling inside the cone region.

## Main results

* `Nivat.LE2.translate_window_mem_coneRegion` — cone membership for translated windows
* `Nivat.LE2.hapex_implies_strict` — `hapex` subsumes `hstrict` (team-lead check request)
* `Nivat.LE2.dot_translate_le_sub_one_of_hapex` — level drop from `hapex` alone
* `Nivat.LE2.hwinL_coneRegion_ascending` — the non-vacuous `hwinL` for `SweepLines.hbase_at_of_sweep_lines`
-/

namespace Nivat.LE2

open Nivat.Colle Nivat.ColleReg Nivat.ConeRegion

/-! ## §1. Translated windows stay in the cone -/

/-- **Translated windows preserve cone membership.**

If `S` is a seed set with apex `a` such that every point `z ∈ S \ {a}` satisfies
`z - a = s•vl + t•u'` for some `s, t : ℕ`, and `w ∈ coneRegion B vl u'`, then for
every `z ∈ S \ {a}`, the translated point `z + (w - a)` also lies in `coneRegion B vl u'`.

**原文：b3_colle2.txt:794-798, Figure 10** — this is the geometric content of
"translate `𝒮_{φ_ι}` so its extreme vertex sits at `w`". Each quantifier corresponds:
- `a` ↔ the extreme vertex (paper: the apex of `𝒮_{φ_ι}`)
- `z ∈ S.erase a` ↔ the other points of `𝒮_{φ_ι}`
- `w ∈ coneRegion B vl u'` ↔ `w` is in the region `𝓡_{ι-1}` (`:780`)
- `z - a = s•vl + t•u'` ↔ the seed lies in the cone spanned from `a`
- `z + (w - a)` ↔ the translation that places `a` at `w`

**Proof:** `z + (w - a) = w + (z - a) = b + (s+s')•vl + (t+t')•u'` by `add_smul`. -/
theorem translate_window_mem_coneRegion
    {B : Set (ℤ × ℤ)} {vl u' : ℤ × ℤ} {S : Finset (ℤ × ℤ)} {a : ℤ × ℤ}
    (hapex : ∀ z ∈ S.erase a, ∃ s t : ℕ, z - a = (s : ℤ) • vl + (t : ℤ) • u')
    {w : ℤ × ℤ} (hw : w ∈ coneRegion B vl u') :
    ∀ z ∈ S.erase a, z + (w - a) ∈ coneRegion B vl u' := by
  intro z hz
  obtain ⟨s', t', hza⟩ := hapex z hz
  rw [mem_coneRegion_iff] at hw ⊢
  obtain ⟨b, hb, s, t, rfl⟩ := hw
  use b, hb, s + s', t + t'
  calc z + (b + (s : ℤ) • vl + (t : ℤ) • u' - a)
      = z - a + b + (s : ℤ) • vl + (t : ℤ) • u' := by abel
    _ = (s' : ℤ) • vl + (t' : ℤ) • u' + b + (s : ℤ) • vl + (t : ℤ) • u' := by rw [hza]
    _ = b + ((s' : ℤ) • vl + (s : ℤ) • vl) + ((t' : ℤ) • u' + (t : ℤ) • u') := by abel
    _ = b + ((s + s' : ℕ) : ℤ) • vl + ((t + t' : ℕ) : ℤ) • u' := by
        push_cast [add_smul]; abel

#print axioms translate_window_mem_coneRegion

/-! ## §2. `hapex` implies strict argmax (team-lead verification request) -/

/-- **`hapex` plus `t ≥ 1` gives `hstrict`.**

⚠ **订正（集成者，2026-09-20）**：我原先的检查请求写的是「`hapex` 蕴涵 `hstrict`，白送一条 binder」，
**这是错的**。`hapex` 只给 `s t : ℕ`，即 `t ≥ 0`，于是 `⟪m, z−a⟫ = s·0 + t·(−1) = −t ≤ 0`
——只有 `≤`，**没有严格性**。`t = 0` 的点（即落在 `a + ℤ₊·vl` 上的生成元）与 `a` 同层。
所以 binder 并没有消失，它**换了形状**：从「严格极大点」变成「在去心种子上 `t ≥ 1`」，
这正是下面第四条前提 `ht_pos`。数值部分（`⟪m, z−a⟫ = −t`）我算对了，结论部分算错了。

原文：b3_colle2.txt:792 — "Lemma 2.6 implies that `𝒮_{φ_ι}` does not have any edge parallel to
`−ℓ` or `ℓ`"。原文得到严格性靠的是**无平行边**，不是靠锥的参数化；`ht_pos` 是同一件事在
锥坐标下的写法（没有平行于 `vl` 的边 ⟺ 除顶点外没有 `t = 0` 的点）。真正把「无平行边」
变成内核事实的是 `Nivat.ApexUnique.face_parallel_iff`（`ApexUnique.lean:80`），
产出严格极大点的是 `Nivat.ApexUnique.exists_strict_argmax_of_no_edge_parallel`（`:126`）。 -/
theorem hapex_implies_strict
    {S : Finset (ℤ × ℤ)} {vl u' m a : ℤ × ℤ}
    (hapex : ∀ z ∈ S.erase a, ∃ s t : ℕ, z - a = (s : ℤ) • vl + (t : ℤ) • u')
    (hm : dot m vl = 0) (hu' : dot m u' = -1)
    (ht_pos : ∀ z ∈ S.erase a, ∃ s t : ℕ, z - a = (s : ℤ) • vl + (t : ℤ) • u' ∧ t ≥ 1) :
    ∀ z ∈ S.erase a, dot m z < dot m a := by
  intro z hz
  obtain ⟨s, t, hza, ht⟩ := ht_pos z hz
  have hsub : dot m (z - a) = dot m z - dot m a := by
    simp only [dot, Prod.fst_sub, Prod.snd_sub]; ring
  have hadd : ∀ x y : ℤ × ℤ, dot m (x + y) = dot m x + dot m y := by
    intro x y; simp only [dot, Prod.fst_add, Prod.snd_add]; ring
  have hsm : ∀ (k : ℤ) (x : ℤ × ℤ), dot m (k • x) = k * dot m x := by
    intro k x; simp only [dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
  have hval : dot m (z - a) = -(t : ℤ) := by
    rw [hza, hadd, hsm, hsm, hm, hu']; ring
  have ht1 : (1 : ℤ) ≤ (t : ℤ) := by exact_mod_cast ht
  omega

#print axioms hapex_implies_strict

/-! ## §3. Level drop from `hapex` alone -/

/-- **The strict drop, derived from `hapex`.**

A cone-apex condition `hapex` with `t ≥ 1` puts every translated generator at least one level
below `w`. This is `Nivat.StrictWindow.dot_translate_le_sub_one` (`:78`) derived from `hapex`.

**原文：b3_colle2.txt:792** — the unique extreme vertex of `𝒮_{φ_ι}`. -/
theorem dot_translate_le_sub_one_of_hapex
    {S : Finset (ℤ × ℤ)} {vl u' m a : ℤ × ℤ}
    (hapex : ∀ z ∈ S.erase a, ∃ s t : ℕ, z - a = (s : ℤ) • vl + (t : ℤ) • u')
    (hm : dot m vl = 0) (hu' : dot m u' = -1)
    (ht_pos : ∀ z ∈ S.erase a, ∃ s t : ℕ, z - a = (s : ℤ) • vl + (t : ℤ) • u' ∧ t ≥ 1)
    {w : ℤ × ℤ} :
    ∀ z ∈ S.erase a, dot m (z + (w - a)) ≤ dot m w - 1 := by
  intro z hz
  have hstrict := hapex_implies_strict hapex hm hu' ht_pos z hz
  have : dot m (z + (w - a)) = dot m z + dot m w - dot m a := by
    simp [dot, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]; ring
  rw [this]
  omega

#print axioms dot_translate_le_sub_one_of_hapex

/-! ## §4. The non-vacuous hwinL over the cone -/

/-- **The non-vacuous `hwinL` for cone regions.  Lines ASCEND.**

For a seed `S` with apex `a` such that the punctured seed lies in the cone spanned from `a`
by `vl` and `u'`, if `w` lies in line `i` of the cone (lines being level sets of `dot m ·`
at height `c + 1 + i`, with `dot m vl = 0` and `dot m u' = -1`), then every translated point
`z + (w - a)` lies either in the base `coneRegion ∩ {dot m · ≤ c}` or in a strictly earlier
line `i' < i`.

**原文：b3_colle2.txt:794-798, Figure 10** — this is `hwinL` for
`SweepLines.hbase_at_of_sweep_lines` (`:183-184`), intersected with `coneRegion` so it is not
vacuous.  Both obligations are already in this file: cone membership is §1
(`translate_window_mem_coneRegion`) and the level drop is §3
(`dot_translate_le_sub_one_of_hapex`).

**Quantifier correspondence:**
- `i` ↔ line index (paper: the `i`-th line being conquered)
- `w ∈ line i` ↔ `w` on ascending line `i` with `dot m w = c + 1 + i`
- `z ∈ S.erase a` ↔ "every other point" of `𝒮_{φ_ι}` (`:794`)
- `hapex` ↔ "every other point falls inside the cone" (`:794-798`)

## 🔴 订正（集成者，2026-09-20）：上一版 `hwinL_coneRegion_descending` 为假，已删

我在派工时要求把方向翻成**下降**（`cz - 1 - i`、顶点取层**极小**），理由是对齐
`ConeHbase` 与 `:796-804` 的 `l₁ := ℓ_B^{(-)}`。**这条指令是错的**，`lake build` 当场判红
（`omega could not prove the goal`，旧 `:171` / `:174`）。错因是算术，不是策略：

`hapex` 给 `z − a = s•vl + t•u'` 且 `s t : ℕ`，于是
`⟪m, z−a⟫ = s·0 + t·(−1) = −t ≤ −1`（用 `ht_pos` 的 `t ≥ 1`）。
即 **`hapex` 强制顶点 `a` 是层极大、平移后的点往下走**，与「顶点取层极小、平移后往上走」
恰好相反。旧 `:171` 的目标 `dot m (z − a) ≥ 1` 正是 `hapex` 所给结论的**否定**，
所以它不可能证出来——不是 `omega` 不够强。

**由此得到的真实两难（两条都是内核事实，不是读法）：**
- **上升**（本定理）：`hwinL` 成立，代价是基底 `D = coneRegion ∩ {level ≤ c}` 是锥的
  **无穷下侧**，`D ⊆ halfStrip` 为假，于是 `hD` 拿不到。
- **下降**：`D = coneRegion ∩ {level ≥ cz}` 确实 `⊆ halfStrip`（§6 `D_subset_halfStrip`，
  已证），`hD` 白送，但 `hwinL` 为假——见 `StrictWindow.not_hwinL_cone_ascending`
  （`StrictWindow.lean:400`，内核反例）。

⚠ 那条反例的**见证不满足 `hapex`**（`z − a = (0,2)`，在 `vl = (1,0)`、`u' = (0,−1)` 下需 `t = −2`），
所以它否的是**只带 `hstrict` 的下降版**，并没有否掉本定理。两条同时为真，因为不是同一个命题
（`CLAUDE.md` leaf C 行的第三条教训）。**带 `hapex` 的下降版则由上面那段算术直接判死。** -/
theorem hwinL_coneRegion_ascending
    {B : Set (ℤ × ℤ)} {vl u' : ℤ × ℤ} {S : Finset (ℤ × ℤ)} {a : ℤ × ℤ}
    (hapex : ∀ z ∈ S.erase a, ∃ s t : ℕ, z - a = (s : ℤ) • vl + (t : ℤ) • u')
    (ht_pos : ∀ z ∈ S.erase a, ∃ s t : ℕ, z - a = (s : ℤ) • vl + (t : ℤ) • u' ∧ t ≥ 1)
    {m : ℤ × ℤ} (hm : dot m vl = 0) (hu' : dot m u' = -1) (c : ℤ) :
    ∀ i : ℕ, ∀ w ∈ (coneRegion B vl u' ∩ {z | dot m z = c + 1 + i}),
      ∀ z ∈ S.erase a, z + (w - a) ∈
        (coneRegion B vl u' ∩ {z | dot m z ≤ c}) ∪
        (⋃ i' ∈ {i' : ℕ | i' < i}, coneRegion B vl u' ∩ {z | dot m z = c + 1 + i'}) := by
  intro i w hw z hz
  have hmem : z + (w - a) ∈ coneRegion B vl u' :=
    translate_window_mem_coneRegion hapex hw.1 z hz
  have hdrop : dot m (z + (w - a)) ≤ dot m w - 1 :=
    dot_translate_le_sub_one_of_hapex hapex hm hu' ht_pos (w := w) z hz
  have hwlev : dot m w = c + 1 + (i : ℤ) := by
    have := hw.2
    simp only [Set.mem_setOf_eq] at this
    exact this
  by_cases h : dot m (z + (w - a)) ≤ c
  · exact Or.inl ⟨hmem, h⟩
  · apply Or.inr
    push_neg at h
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq, exists_prop]
    exact ⟨(dot m (z + (w - a)) - c - 1).toNat, by omega, hmem, by omega⟩

#print axioms hwinL_coneRegion_ascending

/-! ## §5. Coverage without finiteness (kills `hBstep`) -/

/-- **Cone coverage without `hBstep` or finiteness.**

Every point in `coneRegion B vl u'` either has level `≥ cz` (in `D`) or level `≤ cz - 1`,
and then its level is `cz - 1 - i` for some `i : ℕ`. Pure `omega` after unfolding.

**原文：b3_colle2.txt:780** — the expansion `𝓡_{ι-1} = H_B(ℓ) ∪ ⋃_i line_i`.

**This removes `hBstep`**, which `ConeLines.lean:857` refuted for every `EnvOf` witness.
Contrast `ConeLines.wedgeFull_subset_fullSweep_union_lines`, which needs `hBstep` precisely
because `wedgeFull` has no upper level bound relative to `B`. -/
theorem coneRegion_subset_union_lines
    {B : Set (ℤ × ℤ)} {vl u' nℓ : ℤ × ℤ}
    (hnℓ_vl : dot nℓ vl = 0) (hnℓ_u' : dot nℓ u' = -1)
    (cz : ℤ) :
    coneRegion B vl u' ⊆
      (coneRegion B vl u' ∩ {z | cz ≤ dot nℓ z}) ∪
      (⋃ i : ℕ, coneRegion B vl u' ∩ {z | dot nℓ z = cz - 1 - i}) := by
  intro z hz
  rw [mem_coneRegion_iff] at hz
  obtain ⟨b, hb, s, t, rfl⟩ := hz
  have hlev : dot nℓ (b + (s : ℤ) • vl + (t : ℤ) • u') = dot nℓ b - t := by
    have hadd : ∀ x y : ℤ × ℤ, dot nℓ (x + y) = dot nℓ x + dot nℓ y := by
      intro x y; simp only [dot, Prod.fst_add, Prod.snd_add]; ring
    have hsm : ∀ (k : ℤ) (x : ℤ × ℤ), dot nℓ (k • x) = k * dot nℓ x := by
      intro k x; simp only [dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
    rw [hadd, hadd, hsm, hsm, hnℓ_vl, hnℓ_u']; ring
  by_cases h : cz ≤ dot nℓ b - t
  · left
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
    rw [mem_coneRegion_iff]
    refine ⟨⟨b, hb, s, t, rfl⟩, ?_⟩
    rw [hlev]; exact h
  · right
    push_neg at h
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
    rw [mem_coneRegion_iff]
    use (cz - 1 - (dot nℓ b - (t : ℤ))).toNat
    refine ⟨⟨b, hb, s, t, rfl⟩, ?_⟩
    rw [hlev]; omega

#print axioms coneRegion_subset_union_lines

/-! ## §6. D is in the half-strip (un-strengthened `hD`) -/

/-- **`D` is contained in the forward half-strip**, so `hD` comes free from
`exists_hD_of_case1` (`L1Line0.lean:527`), un-strengthened.

A cone point is `b + s•vl + t•u'` with `s t : ℕ`, so its level is `dot nℓ b - t`.
Requiring `dot nℓ b - t ≥ cz = suppVal B nℓ` forces `t = 0` **and** `dot nℓ b = cz`,
leaving `b + s•vl` with `s ≥ 0` — a forward half-strip point.

**原文：b3_colle2.txt:777-780** — `H_B(ℓ) ⊆ 𝓡_{ι-1}` by definition, and the level-maximal
part of the cone is exactly the half-strip. This is why `cz` must be the **support value**,
not an arbitrary constant. -/
theorem D_subset_halfStrip
    {B : Set (ℤ × ℤ)} {vl u' nℓ : ℤ × ℤ}
    (hB_fin : B.Finite) (hB_ne : B.Nonempty)
    (hnℓ_vl : dot nℓ vl = 0) (hnℓ_u' : dot nℓ u' = -1) :
    (coneRegion B vl u' ∩ {z | suppVal B nℓ ≤ dot nℓ z}) ⊆ Nivat.LE2.halfStrip B vl := by
  intro z ⟨hz_cone, hz_lev⟩
  rw [mem_coneRegion_iff] at hz_cone
  obtain ⟨b, hb, s, t, rfl⟩ := hz_cone
  have hlev : dot nℓ (b + (s : ℤ) • vl + (t : ℤ) • u') = dot nℓ b - t := by
    have hadd : ∀ x y : ℤ × ℤ, dot nℓ (x + y) = dot nℓ x + dot nℓ y := by
      intro x y; simp only [dot, Prod.fst_add, Prod.snd_add]; ring
    have hsm : ∀ (k : ℤ) (x : ℤ × ℤ), dot nℓ (k • x) = k * dot nℓ x := by
      intro k x; simp only [dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
    rw [hadd, hadd, hsm, hsm, hnℓ_vl, hnℓ_u']; ring
  simp only [Set.mem_setOf_eq] at hz_lev
  rw [hlev] at hz_lev
  have hb_le : dot nℓ b ≤ suppVal B nℓ := Nivat.LE2.le_suppVal hB_fin hB_ne hb
  have ht_zero : t = 0 := by omega
  subst ht_zero
  simp only [Nivat.LE2.halfStrip, Set.mem_setOf_eq, Nat.cast_zero, zero_smul, add_zero]
  exact ⟨b, hb, s, rfl⟩

#print axioms D_subset_halfStrip

/-! ## §7. Argmax lemma via suppVal -/

/-- **Argmax of `⟪expNormal u' vl, ·⟫` on finite nonempty `B`.**

This is `exists_suppVal_eq` (`LatticeEdges.lean:755`) instantiated at `n := expNormal u' vl`.
The argmax `b₀` satisfies `∀ b ∈ B, dot (expNormal u' vl) b ≤ dot (expNormal u' vl) b₀`. -/
theorem exists_argmax_expNormal {B : Set (ℤ × ℤ)} (hfin : B.Finite) (hne : B.Nonempty)
    (u' vl : ℤ × ℤ) :
    ∃ b₀ ∈ B, ∀ b ∈ B, dot (expNormal u' vl) b ≤ dot (expNormal u' vl) b₀ := by
  obtain ⟨v, hv, heq⟩ := Nivat.LE2.exists_suppVal_eq hfin hne (expNormal u' vl)
  use v, hv
  intro b hb
  rw [heq]
  exact Nivat.LE2.le_suppVal hfin hne hb

#print axioms exists_argmax_expNormal

/-! ## §8. The argmax lemma: `chainFull ⊆ coneRegion` at `k = 0` -/

/-- **`chainFull` at level 0 is contained in `coneRegion` when `b₀` is the argmax.**

With `e := expNormal u' vl`, `chainFull B vl u' b₀ 0 = wedgeFull B vl u' ∩ halfPlaneGE e (⟪e,b₀⟫)`.
A point `b + s•vl + t•u'` has `⟪e,·⟫ = ⟪e,b⟫ + s`, so the cut says `s ≥ ⟪e,b₀⟫ − ⟪e,b⟫`.
Choose `b₀` to be the **argmax** of `⟪e,·⟫` on `B`. Then `⟪e,b₀⟫ − ⟪e,b⟫ ≥ 0` for every `b`,
hence `s ≥ 0`, hence the point is in `coneRegion B vl u'` with no shift.

**原文：b3_colle2.txt:780** — the construction of `𝓡_{ι-1}` from `H_B(ℓ)`.

**This is the round's keystone** — it converts the 30-file refactor into one lemma.
Composed with the coverage lemma above, this is `hKL` for `SweepLines.hbase_at_of_sweep_lines`. -/
theorem chainFull_subset_coneRegion_of_argmax
    {B : Set (ℤ × ℤ)} {vl u' b₀ : ℤ × ℤ}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hb₀max : ∀ b ∈ B, dot (expNormal u' vl) b ≤ dot (expNormal u' vl) b₀) :
    Nivat.ColleReg.chainFull B vl u' b₀ 0 ⊆ coneRegion B vl u' := by
  intro z hz
  unfold Nivat.ColleReg.chainFull Nivat.L1Region.cut at hz
  obtain ⟨hz_wedge, hz_lev⟩ := hz
  simp only [Nivat.ColleReg.expLevel, Nat.cast_zero, sub_zero] at hz_lev
  unfold Nivat.ColleReg.wedgeFull at hz_wedge
  rw [Nivat.RegionSweep.mem_sweep] at hz_wedge
  obtain ⟨y, hy_base, t, hz_eq⟩ := hz_wedge
  rw [Nivat.ColleReg.mem_fullSweep_iff] at hy_base
  obtain ⟨b, hb, k, hy_eq⟩ := hy_base
  subst hy_eq hz_eq
  have hlev : dot (expNormal u' vl) (b + k • vl + (t : ℤ) • u') =
              dot (expNormal u' vl) b + k := by
    have hadd : ∀ x y : ℤ × ℤ, dot (expNormal u' vl) (x + y) =
                dot (expNormal u' vl) x + dot (expNormal u' vl) y := by
      intro x y; simp only [dot, Prod.fst_add, Prod.snd_add]; ring
    have hsm : ∀ (k : ℤ) (x : ℤ × ℤ), dot (expNormal u' vl) (k • x) =
               k * dot (expNormal u' vl) x := by
      intro k x; simp only [dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
    rw [hadd, hadd, hsm, hsm, Nivat.ColleReg.dot_expNormal_vl hunimod, Nivat.ColleReg.dot_expNormal_u']
    ring
  have hk_nonneg : 0 ≤ k := by
    have : dot (expNormal u' vl) b₀ ≤ dot (expNormal u' vl) (b + k • vl + (t : ℤ) • u') :=
      hz_lev
    rw [hlev] at this
    have hmax := hb₀max b hb
    omega
  rw [mem_coneRegion_iff]
  use b, hb, k.toNat, t
  rw [Int.toNat_of_nonneg hk_nonneg]

#print axioms chainFull_subset_coneRegion_of_argmax

/-! ## §9. The argmax lemma at general k -/

/-- **`chainFull` at general level `k` is contained in `coneRegion` when `b₀` is the argmax.**

With `e := expNormal u' vl`, `chainFull B vl u' b₀ k` has cut `⟪e,·⟫ ≥ ⟪e,b₀⟫ - k`.
A point `b + s•vl + t•u'` has `⟪e,·⟫ = ⟪e,b⟫ + s`, so the cut says `s ≥ ⟪e,b₀⟫ - ⟪e,b⟫ - k`.
With `b₀` the argmax of `⟪e,·⟫` on `B`, we have `⟪e,b₀⟫ - ⟪e,b⟫ ≥ 0`, hence `s ≥ -k`.

🔴 **订正（集成者，2026-09-20）：结论里的基底不能是 `B`。** 上一版写
`chainFull B vl u' b₀ k ⊆ coneRegion B vl u'`，**对 `k ≥ 1` 为假**，`lake build` 当场留下
未解目标 `b + j•vl + t•u' = b + (j+k)•vl + t•u'`（且该版本带 `sorry` 落进主仓，违红线，已删）。
原因就是上面那行算术：`k = 0` 才给 `s ≥ 0`，一般 `k` 只给 `s ≥ -k`，而 `coneRegion B vl u'`
按定义要求 `s ≥ 0`。差的那 `k` 步不是证明技巧问题，是**基底差了 `k•vl`**。

真陈述是把基底左移 `k•vl`：`b + j•vl = (b - k•vl) + (j+k)•vl`，右边的系数 `j + k ≥ 0` 合法，
而 `b - k•vl ∈ shift (-(k•vl)) B`。所以下面的结论用 `shift (-((k:ℤ)•vl)) B` 作基底，
`k = 0` 时 `shift 0 B = B`，退化回 §8。**消费者必须接受这个位移基底**——`hKL` 要的是
`chainFull ⊆ D ∪ ⋃ lines`，而 `D`、`lines` 也都建在同一个基底上，所以位移要一路带下去。

**Consumer:** `StrictWindow.hbase_of_cone_halfStrip` (`:489`), via
`WedgeAssemble.nonempty_wedgeResidualR_of_hbase_at_shear`, reaching `RegionSteps.lean:1195`
`exists_wedgeResidualR`. The `hKL` binder requires this at a specific `k` chosen against
the sheared `expNormal`, where `k = 0` does not apply. -/
theorem chainFull_subset_coneRegion_of_argmax_general
    {B : Set (ℤ × ℤ)} {vl u' b₀ : ℤ × ℤ} (k : ℕ)
    (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hb₀max : ∀ b ∈ B, dot (expNormal u' vl) b ≤ dot (expNormal u' vl) b₀) :
    Nivat.ColleReg.chainFull B vl u' b₀ k ⊆
      Nivat.ConeRegion.coneRegion (Nivat.LE2.shift (-((k : ℤ) • vl)) B) vl u' := by
  intro z hz
  unfold Nivat.ColleReg.chainFull Nivat.L1Region.cut at hz
  obtain ⟨hz_wedge, hz_lev⟩ := hz
  simp only [Nivat.ColleReg.expLevel] at hz_lev
  unfold Nivat.ColleReg.wedgeFull at hz_wedge
  rw [Nivat.RegionSweep.mem_sweep] at hz_wedge
  obtain ⟨y, hy_base, t, hz_eq⟩ := hz_wedge
  rw [Nivat.ColleReg.mem_fullSweep_iff] at hy_base
  obtain ⟨b, hb, j, hy_eq⟩ := hy_base
  subst hy_eq hz_eq
  have hlev : dot (expNormal u' vl) (b + j • vl + (t : ℤ) • u') =
              dot (expNormal u' vl) b + j := by
    have hadd : ∀ x y : ℤ × ℤ, dot (expNormal u' vl) (x + y) =
                dot (expNormal u' vl) x + dot (expNormal u' vl) y := by
      intro x y; simp only [dot, Prod.fst_add, Prod.snd_add]; ring
    have hsm : ∀ (m : ℤ) (x : ℤ × ℤ), dot (expNormal u' vl) (m • x) =
               m * dot (expNormal u' vl) x := by
      intro m x; simp only [dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
    rw [hadd, hadd, hsm, hsm, Nivat.ColleReg.dot_expNormal_vl hunimod, Nivat.ColleReg.dot_expNormal_u']
    ring
  -- Unpack halfPlaneGE membership into direct inequality
  simp only [Nivat.LE2.halfPlaneGE, Set.mem_setOf_eq] at hz_lev
  -- hz_lev: dot (expNormal u' vl) b₀ - ↑k ≤ dot (expNormal u' vl) (b + j • vl + ↑t • u')
  rw [hlev] at hz_lev
  -- hz_lev: dot (expNormal u' vl) b₀ - ↑k ≤ dot (expNormal u' vl) b + j
  -- Need: j + k ≥ 0, then (j + k).toNat gives the cone's s-coordinate
  have hj_bound : -(k : ℤ) ≤ j := by
    have hmax := hb₀max b hb
    omega
  have hj_k_nonneg : 0 ≤ j + (k : ℤ) := by omega
  rw [mem_coneRegion_iff]
  refine ⟨b - (k : ℤ) • vl, ?_, (j + (k : ℤ)).toNat, t, ?_⟩
  · show b - (k : ℤ) • vl - (-((k : ℤ) • vl)) ∈ B
    simpa using hb
  · rw [Int.toNat_of_nonneg hj_k_nonneg, add_smul]
    abel

#print axioms chainFull_subset_coneRegion_of_argmax_general

/-! ## §10. Full cover with shifted base -/

/-- **`chainFull` is covered by shifted half-strip and descending lines.**

Composes the corrected §9 `chainFull_subset_coneRegion_of_argmax_general` (which lands in
the shifted cone) with §5 `coneRegion_subset_union_lines` (which covers any cone), then
applies §6 `D_subset_halfStrip` to convert the D-set to `halfStrip` when `cz = suppVal`.

🔴 **状态：真，但不是需要的那条（2026-09-20 集成者定义审计，`PROTOCOL.md` §14 保留不删）。**

`hcz : cz = suppVal (shift …) nℓ` 把 `cz` 钉在 **`B` 的顶层**。这一版的覆盖因此**平凡为真**：
`coneRegion ∩ {level ≥ 顶层}` 就是顶行，当然落在 `halfStrip` 里，其余全部由 `⋃ lines` 接住。
代价是它对应的**不是 Collé 的归纳**。原文 `b3_colle2.txt:796` 取 `l₁ := ℓ_B^{(-)}`，
而 `:405` 把 `ℓ^{(-)}` 定义成「平行于 `ℓ`、最靠近 `H(ℓ)` 且与 `H(ℓ)` 不交」的格线——
即**紧贴 `B` 带外侧的第一条线**，不是带内的 `顶层 − 1`。

两种读法的结局（集成者算过，不是设想）：
* `cz = suppVal`（本定理）：覆盖平凡真，但**传播当场死**。`w` 在 `顶层 − 1` 上，
  `Ŝ_{φι}` 的其余点比 `w` 高 `d = dot nℓ (z − a) ≥ 1` 层，落在 `顶层 − 1 + d`；
  `d ≥ 2` 时这一层既不在 `coneRegion`（上界是顶层）也不在 `halfStrip`（上界同为顶层），
  于是它**不在已知区域里**，归纳一步都走不动。
* `cz = infVal`（原文读法）：`l_i` 全在带外下方，`Ŝ_{φι}` 的其余点落回 `B` 的带内，
  传播才有意义——这正是 `:798` 图 10 那句「`H_B(ℓ)` 上的信息唯一决定 `A₁` 上的信息」。
  代价是覆盖**不再平凡**，它就是 `StrictWindow.not_coneRegion_subset_halfStrip_union_lines`
  （`:864`）证伪的那条，缺的前提见 `ConeRegion` 侧的 `hmono`（详见该处）。

所以本定理**不能**兑现 `StrictWindow.hbase_of_cone_halfStrip_of_geom`（`:921`）的 `hKL`：
`hKL` 要的是 `cz = infVal` 那一版。保留本条是为了钉住这个死胡同，
避免下一轮有人再把 `cz` 钉在 `suppVal` 上重走一遍。 -/
theorem chainFull_subset_shift_halfStrip_union_lines
    {B : Set (ℤ × ℤ)} {vl u' nℓ b₀ : ℤ × ℤ} (k : ℕ)
    (hB_fin : B.Finite) (hB_ne : B.Nonempty)
    (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hperp : dot nℓ vl = 0) (hstep : dot nℓ u' = -1)
    (hb₀max : ∀ b ∈ B, dot (expNormal u' vl) b ≤ dot (expNormal u' vl) b₀)
    (cz : ℤ)
    (hcz : cz = Nivat.LE2.suppVal (Nivat.LE2.shift (-((k : ℤ) • vl)) B) nℓ) :
    Nivat.ColleReg.chainFull B vl u' b₀ k ⊆
      (Nivat.LE2.halfStrip (Nivat.LE2.shift (-((k : ℤ) • vl)) B) vl) ∪
      (⋃ i : ℕ, Nivat.ConeRegion.coneRegion (Nivat.LE2.shift (-((k : ℤ) • vl)) B) vl u'
        ∩ {y | dot nℓ y = cz - 1 - (i : ℤ)}) := by
  intro z hz
  -- Step 1: chainFull ⊆ coneRegion (shifted base) via corrected §9
  have hz_cone : z ∈ Nivat.ConeRegion.coneRegion (Nivat.LE2.shift (-((k : ℤ) • vl)) B) vl u' :=
    chainFull_subset_coneRegion_of_argmax_general k hunimod hb₀max hz
  -- Step 2: coneRegion (shifted base) ⊆ D ∪ ⋃ lines via §5
  have hz_cover := coneRegion_subset_union_lines hperp hstep cz hz_cone
  cases hz_cover with
  | inl hD =>
    -- z ∈ coneRegion ∩ {level ≥ cz}
    -- Apply §6 D_subset_halfStrip with cz = suppVal
    left
    rw [hcz] at hD
    have hsfin : (Nivat.LE2.shift (-((k : ℤ) • vl)) B).Finite := by
      rw [Nivat.LE2.shift_eq_image]; exact hB_fin.image _
    have hsne : (Nivat.LE2.shift (-((k : ℤ) • vl)) B).Nonempty := by
      rw [Nivat.LE2.shift_eq_image]; exact hB_ne.image _
    exact D_subset_halfStrip hsfin hsne hperp hstep hD
  | inr hlines =>
    -- z ∈ ⋃ i, coneRegion ∩ {level = cz - 1 - i}
    right
    exact hlines

#print axioms chainFull_subset_shift_halfStrip_union_lines

/-! ## §11. Full cover with hmono hypothesis -/

/-- **`chainFull` is covered by shifted half-strip and descending lines, via `hmono`.**

Composes the corrected §9 `chainFull_subset_coneRegion_of_argmax_general` (which lands in
the shifted cone) with §5 `coneRegion_subset_union_lines` (which covers any cone). The `inl`
branch (D-set at level `≥ cz`) is discharged via `hmono` instead of pinning `cz = suppVal`.

**原文：b3_colle2.txt:780, 796-804** — the expansion `𝓡_{ι-1} = H_B(ℓ) ∪ ⋃_i l_i` with
`l₁ := ℓ_B^{(-)}` (`:796`). The paper takes `cz = infVal B nℓ` (the bottom, per `:405`
defining `ℓ^{(-)}` as the lattice line parallel to `ℓ` closest to `H(ℓ)` with `H(ℓ) ∩ ℓ' = ∅`),
not `cz = suppVal` (the top). With `cz = infVal`, the lines lie outside `B`'s band below,
so translated points `Ŝ_{φι}` land back inside the band, enabling propagation (`:798` Figure 10:
"information on `H_B(ℓ)` uniquely determines information on `A₁`"). The `hmono` hypothesis
captures exactly what the cover needs: a cone point at level `≥ cz` decomposes as
`b + s•vl + t•u' = (b + t•u') + s•vl`, `hmono` puts `b + t•u'` in the half-strip, and
the half-strip absorbs `+ s•vl`.

**`hmono` is not proved here and is not an extra assumption in disguise.** Wlines is landing
`coneRegion ∩ {level ≥ cz} ⊆ halfStrip ↔ hmono` (an `↔`, so `hmono` is exactly the cover's
content), and Wbox is landing `exists_shear_hmono` — `hmono` holds unconditionally once `u'`
is sheared, for finite lattice-convex `B`.

**Consumer:** `hKL` of `StrictWindow.hbase_of_cone_halfStrip_of_geom` (`:921`) →
`WedgeAssemble.nonempty_wedgeResidualR_of_hbase_at_shear` → `RegionSteps.lean:1195`
`exists_wedgeResidualR`. -/
theorem chainFull_subset_halfStrip_union_lines_of_hmono
    {B : Set (ℤ × ℤ)} {vl u' nℓ b₀ : ℤ × ℤ} (k : ℕ) {cz : ℤ}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hperp : dot nℓ vl = 0) (hstep : dot nℓ u' = -1)
    (hb₀max : ∀ b ∈ B, dot (expNormal u' vl) b ≤ dot (expNormal u' vl) b₀)
    (hmono : ∀ b ∈ Nivat.LE2.shift (-((k : ℤ) • vl)) B, ∀ t : ℕ,
      cz ≤ dot nℓ b - t → b + (t:ℤ) • u' ∈ Nivat.LE2.halfStrip (Nivat.LE2.shift (-((k : ℤ) • vl)) B) vl) :
    Nivat.ColleReg.chainFull B vl u' b₀ k ⊆
      (Nivat.LE2.halfStrip (Nivat.LE2.shift (-((k : ℤ) • vl)) B) vl) ∪
      (⋃ i : ℕ, Nivat.ConeRegion.coneRegion (Nivat.LE2.shift (-((k : ℤ) • vl)) B) vl u'
        ∩ {y | dot nℓ y = cz - 1 - (i : ℤ)}) := by
  intro z hz
  -- Step 1: chainFull ⊆ coneRegion (shifted base) via corrected §9
  have hz_cone : z ∈ Nivat.ConeRegion.coneRegion (Nivat.LE2.shift (-((k : ℤ) • vl)) B) vl u' :=
    chainFull_subset_coneRegion_of_argmax_general k hunimod hb₀max hz
  -- Step 2: coneRegion (shifted base) ⊆ D ∪ ⋃ lines via §5
  have hz_cover := coneRegion_subset_union_lines hperp hstep cz hz_cone
  cases hz_cover with
  | inl hD =>
    -- z ∈ coneRegion ∩ {level ≥ cz}
    -- Decompose z = b + s•vl + t•u' = (b + t•u') + s•vl
    left
    obtain ⟨hz_cone_D, hlev⟩ := hD
    rw [mem_coneRegion_iff] at hz_cone_D
    obtain ⟨b, hb, s, t, hz_eq⟩ := hz_cone_D
    subst hz_eq
    -- hlev: cz ≤ dot nℓ (b + s•vl + t•u'), stated as membership in `{z | cz ≤ dot nℓ z}`;
    -- unfold it to the inequality before rewriting (integrator fix, 2026-09-20 — the `rw`
    -- here failed on the `∈ {z | _}` form).
    have hlev' : cz ≤ dot nℓ (b + (s : ℤ) • vl + (t : ℤ) • u') := hlev
    have hlev_eq : dot nℓ (b + (s : ℤ) • vl + (t : ℤ) • u') = dot nℓ b - t := by
      have hadd : ∀ x y : ℤ × ℤ, dot nℓ (x + y) = dot nℓ x + dot nℓ y := by
        intro x y; simp only [dot, Prod.fst_add, Prod.snd_add]; ring
      have hsm : ∀ (m : ℤ) (x : ℤ × ℤ), dot nℓ (m • x) = m * dot nℓ x := by
        intro m x; simp only [dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
      rw [hadd, hadd, hsm, hsm, hperp, hstep]; ring
    rw [hlev_eq] at hlev'
    -- Apply hmono to get b + t•u' ∈ halfStrip
    have hbt : b + (t : ℤ) • u' ∈ Nivat.LE2.halfStrip (Nivat.LE2.shift (-((k : ℤ) • vl)) B) vl :=
      hmono b hb t hlev'
    -- halfStrip absorbs + s•vl: b + t•u' + s•vl ∈ halfStrip
    rw [Nivat.LE2.halfStrip] at hbt ⊢
    obtain ⟨b', hb', s', hbs'⟩ := hbt
    use b', hb', s' + s
    calc b + (s : ℤ) • vl + (t : ℤ) • u'
        = (b + (t : ℤ) • u') + (s : ℤ) • vl := by ring
      _ = (b' + (s' : ℤ) • vl) + (s : ℤ) • vl := by rw [hbs']
      _ = b' + ((s' + s : ℕ) : ℤ) • vl := by rw [Nat.cast_add, add_smul]; ring
  | inr hlines =>
    -- z ∈ ⋃ i, coneRegion ∩ {level = cz - 1 - i}
    right
    exact hlines

#print axioms chainFull_subset_halfStrip_union_lines_of_hmono

/-! ## §12. Shift-invariance — **已在 `LatticeEdges` 里，不要在这里重写**

2026-09-20 撤销：本节曾写过六条 shift 引理，其中四条无法编译或与已有声明重名，
整块删除。已在本模块闭包里的同名事实（`PROTOCOL.md` §20 的实例）：

* `Nivat.LE2.E_shift`（`LatticeEdges.lean`，带 `@[simp]`）
* `Nivat.LE2.isLatticeConvexRegion_shift`（`LatticeEdges.lean`）与
  `isLatticeConvexRegion_shift_iff`（同文件）
  ⚠ 第 201 轮删号留名：原记 `E_shift` 在 `:615`，实测声明头在 `:689`；同块另两条行号同批漂移，
  一并去号。Lean 侧引用按名字 `grep`，别按行号。
* `Nivat.LE2.shift_eq_image`（`:583`）—— 有限性 / 非空性用它一行转出，不需单独命名

真正缺的两条（`halfStrip_shift` / `coneRegion_shift`）已落在消费侧
`RegionSteps.lean`，因为它们只有那一个消费者。 -/

end Nivat.LE2
