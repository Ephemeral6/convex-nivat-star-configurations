/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.L1Line0

/-!
# `hstraddle` on `chainFull`: Figure 11(B)'s cover from a corner of `𝒮_φ`

Lane Cconv's file (exclusive, 2026-09-19).  Target: the `hstraddle` binder of
`Nivat.ColleReg.L1Claim.exists_L1MaxBResidual_of_wedgeAt_split` (`L1Claim.lean:299`), at the
`ε := εOf u' vl` that Cprobe's `hline` fixes (`L1Line0.exists_L1MaxBResidual_of_placement`,
`L1Line0.lean:349`):

    hstraddle : ∀ N, PeriodOn (T e ξ) (chainFull B vl u' b₀ (k + N)) (c • vl) →
      ¬ PeriodOn (T e ξ) (chainFull B vl u' b₀ (k + (N + 1))) (c • vl) →
      ∀ τ, (line fact at τ) →
        Straddle (T e ξ) (chainFull … (k + N)) (chainFull … (k + (N + 1)))
          S₁ (derivedQ (εOf u' vl) u' S₁) vl u' c τ

Why a new file rather than `L1StraddleMax.lean`: the slot mentions `chainFull` / `uCoord` /
`εOf` (`L1RegionBuild`, `L1Line0`), and `L1Claim → L1StraddleMax` is already an import edge
(`L1Claim.lean:5`) with `L1Line0 → L1Claim`; importing either from `L1StraddleMax` is a cycle.

## The proof, in one paragraph

`straddle_of_cover` (`L1StraddleMax.lean:129`) reduces the slot to the cover

    overlap (chainFull (n+1)) (c•vl) ⊆ genClosure 𝒮_φ a (overlap (chainFull n) (c•vl) ∪ ray g u' t₀)

for every bottom-face point `g` of `S₁` and every `t₀ ≥ τ`.  With `0 ≤ c` the left-hand side
minus `overlap (chainFull n)` is **one** `u'`-line, `{dot en z = expLevel (n+1)} ∩ wedgeFull`
(`mem_overlap_chainFull`; Afill's two-line `overlap_diff_subset_lines` is the general-`h`
statement, this is its `c ≥ 0` collapse), and the bottom face of `S₁` sits on that line
(`dot_eq_of_not_mem_derivedQ`, from Cprobe's placement `hmin` plus its attained minimum).  So the
ray `{t•u' + g : t ≥ t₀}` is a forward half of the line.  The rest of the line is filled by
`MaxEnv.subset_genClosure_of_rank` (`MaximalEnveloped.lean:721`), rank = `u'`-distance to the
ray: place the window `𝒮_φ` with its **corner** `a` on the point to fill; the other points of the
window are either one level up (inside `overlap (chainFull n)`) or on the line strictly closer
to the ray.  `cover_line` is that argument, with no `Config` in it.

The corner is a hypothesis, `hcorner : ∀ b ∈ 𝒮_φ, 0 ≤ dot en (b − a) ∧ 0 ≤ uCoord a b`, i.e.
`𝒮_φ ⊆ a + cone(vl, u')`.  It pays for two things at once: the fill above, and `GeneratesAt ξ 𝒮_φ a`
(`generatesAt_of_corner`) — `a` is the unique maximiser of the primitive functional
`cornerNormal`, hence `IsVtx`, hence a Collé vertex (`isColleVertex_of_isVtx`), hence generating
by `d.isGeneratingSet`.  It is a genuine constraint on the shared datum `u'`, stated as a binder
and not hidden (team-lead 2026-09-19: every extra demand on `B b₀ k c e u'` is a binder).
`exists_corner_shear` (§9, kernel) shows it is always satisfiable after shearing `u' ↦ u' − K•vl`
(which preserves `det u' vl`, `εOf`, `uCoord`); whether the `u'` that `hbase` / `hlev` / `hmin`
want survives that shear is the open joint-data question, not settled here.

## What is *not* in this file

No `IsMinimalCounterexample ξ` hypothesis anywhere except the §27 feeding term, which only
passes `hξ`/`d` through to `L1Claim.exists_L1MaxBResidual_of_unimod_split`.  No `sorry`.  Nothing
about `hbase`; `hlev : LevelInterval B vl` and `hEnv` are not demanded on this route at all
(rewired 2026-09-19 19:3x).

Collé baseline: `b3_colle2.txt:848-856` (Figure 11(B): "`Ŝ_φ` a translation of `𝒮_φ` … determines
uniquely such a configuration on `𝓡^{N+1}_I`").
-/

set_option autoImplicit false

namespace Nivat.L1StraddleWedge

open Nivat Nivat.LE2 Nivat.Colle Nivat.Colle41 Nivat.MaxEnv Nivat.ColleReg
  Nivat.ColleReg.L1Data Nivat.L1StraddleMax Nivat.L1Line0

variable {u' vl : ℤ × ℤ}

/-! ## §1  Coordinates in the basis `(vl, u')`, continued from `L1Line0` §1 -/

/-- Every vector is `(dot en w) • vl + (uCoord 0 w) • u'`: the `vl`-coefficient is the
`expNormal`-level, the `u'`-coefficient is `uCoord` at base point `0`. -/
theorem eq_coords (hunimod : det u' vl = 1 ∨ det u' vl = -1) (w : ℤ × ℤ) :
    w = dot (expNormal u' vl) w • vl + uCoord u' vl 0 w • u' := by
  obtain ⟨A, C, hw, hC⟩ := exists_decomp hunimod 0 w
  have hA : dot (expNormal u' vl) w = A := by
    rw [hw, zero_add, dot_add, dot_smul_right, dot_smul_right, dot_expNormal_vl hunimod,
      dot_expNormal_u']
    ring
  rw [hA, ← hC]
  conv_lhs => rw [hw]
  rw [zero_add]

theorem uCoord_add (b₀ z w : ℤ × ℤ) :
    uCoord u' vl b₀ (z + w) = uCoord u' vl b₀ z + uCoord u' vl 0 w := by
  simp only [uCoord, det, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
    Prod.fst_zero, Prod.snd_zero]
  ring

theorem uCoord_sub_eq (a b : ℤ × ℤ) : uCoord u' vl 0 (b - a) = uCoord u' vl a b := by
  simp only [uCoord, sub_zero]

theorem uCoord_sub' (b₀ z g : ℤ × ℤ) :
    uCoord u' vl 0 (z - g) = uCoord u' vl b₀ z - uCoord u' vl b₀ g := by
  simp only [uCoord, det, Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero]
  ring

theorem expLevel_succ (b₀ : ℤ × ℤ) (n : ℕ) :
    expLevel u' vl b₀ (n + 1) = expLevel u' vl b₀ n - 1 := by
  simp only [expLevel]; push_cast; ring

/-! ## §2  `wedgeFull` is closed under `+vl`, `−vl`, `+u'` -/

theorem add_mem_wedgeFull {B : Set (ℤ × ℤ)} {z : ℤ × ℤ} (hz : z ∈ wedgeFull B vl u')
    (α : ℤ) (β : ℕ) : z + (α • vl + (β : ℤ) • u') ∈ wedgeFull B vl u' := by
  obtain ⟨f, hf, t, rfl⟩ := hz
  obtain ⟨b, hb, k, rfl⟩ := mem_fullSweep_iff.mp hf
  refine ⟨b + (k + α) • vl, mem_fullSweep_iff.mpr ⟨b, hb, k + α, rfl⟩, t + β, ?_⟩
  push_cast
  simp only [add_smul]
  abel

/-- Any translation with nonnegative `u'`-coefficient keeps `wedgeFull`. -/
theorem add_mem_wedgeFull_of_nonneg (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    {B : Set (ℤ × ℤ)} {z w : ℤ × ℤ} (hz : z ∈ wedgeFull B vl u')
    (hw : 0 ≤ uCoord u' vl 0 w) : z + w ∈ wedgeFull B vl u' := by
  have h := add_mem_wedgeFull hz (dot (expNormal u' vl) w) (uCoord u' vl 0 w).toNat
  rwa [Int.toNat_of_nonneg hw, ← eq_coords hunimod w] at h

/-! ## §3  `overlap (chainFull n) (c•vl)` for `0 ≤ c` is `chainFull n` itself -/

/-- With `0 ≤ c`, the `+c•vl` conjunct of `overlap` is implied: the wedge is `vl`-closed and the
level only goes up.  So the residual `overlap (chainFull (n+1)) ∖ overlap (chainFull n)` is
exactly the single line `dot en z = expLevel (n+1)` inside the wedge — the `c ≥ 0` collapse of
Afill's two-line `overlap_diff_subset_lines` (`L1CoverWedge.lean:125`). -/
theorem mem_overlap_chainFull (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    {B : Set (ℤ × ℤ)} {b₀ : ℤ × ℤ} {n : ℕ} {c : ℤ} (hc : 0 ≤ c) {z : ℤ × ℤ} :
    z ∈ overlap (chainFull B vl u' b₀ n) (c • vl) ↔
      z ∈ wedgeFull B vl u' ∧ expLevel u' vl b₀ n ≤ dot (expNormal u' vl) z := by
  constructor
  · intro h
    obtain ⟨h1, -⟩ := mem_overlap.mp h
    exact mem_chainFull_iff.mp h1
  · rintro ⟨hw, hl⟩
    refine mem_overlap.mpr ⟨mem_chainFull_iff.mpr ⟨hw, hl⟩, mem_chainFull_iff.mpr ⟨?_, ?_⟩⟩
    · have := add_mem_wedgeFull hw c 0
      simpa using this
    · rw [dot_expNormal_add_zsmul_vl hunimod]; omega

/-! ## §4  The cover, `Config`-free -/

/-- **Figure 11(B) on `chainFull`, as a `genClosure` inclusion.**  `g` is any point on the new
line (`dot en g = expLevel n − 1`); the window `Sφ` has corner `a` (`hcorner`).  Rank of a line
point = its `u'`-distance to the ray `{t•u' + g : t ≥ t₀}`; each generation step at a line point
`z` places `a` on `z` and every other window point either one level up (in `chainFull n`) or on
the line strictly closer to the ray.

§20 note (team-lead ruling 2026-09-19 19:3x, keep both): `Nivat.L3Band.chainFull_succ_subset_genClosure`
(`L3Band.lean:3678`) is the same cover stated on `chainFull` instead of `overlap (chainFull) (c•vl)`
(equal for `0 ≤ c` by `mem_overlap_chainFull`), with extra binders `hb₁ : b₁ ∈ B` and `hBα`
(`B`'s `expDual`-minimum) that this lemma does not need.  Its `hlev ∧ hα` is this lemma's
`hcorner` verbatim, via `uCoord u' vl a b = dot (expDual u' vl) (b − a)` (kernel, `tmp/cconv_corner_eq_expDual.lean`
`uCoord_eq_dot_expDual` / `hcorner_iff_corner`, **in `tmp/`, not landed** — `expDual` lives in
`L3Band`, which this file deliberately does not import). -/
theorem cover_line (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    {B : Set (ℤ × ℤ)} {b₀ : ℤ × ℤ} {n : ℕ} {c : ℤ} (hc : 0 ≤ c)
    {Sφ : Finset (ℤ × ℤ)} {a : ℤ × ℤ}
    (hcorner : ∀ b ∈ Sφ, 0 ≤ dot (expNormal u' vl) (b - a) ∧ 0 ≤ uCoord u' vl a b)
    {g : ℤ × ℤ} (hg : dot (expNormal u' vl) g = expLevel u' vl b₀ n - 1) (t₀ : ℤ) :
    overlap (chainFull B vl u' b₀ (n + 1)) (c • vl) ⊆
      genClosure Sφ a (overlap (chainFull B vl u' b₀ n) (c • vl) ∪ ray g u' t₀) := by
  have hLn : expLevel u' vl b₀ (n + 1) = expLevel u' vl b₀ n - 1 := expLevel_succ b₀ n
  refine subset_genClosure_of_rank
    (fun z => (t₀ + uCoord u' vl b₀ g - uCoord u' vl b₀ z).toNat) ?_
  intro z hz
  obtain ⟨hzw, hzl⟩ := (mem_overlap_chainFull hunimod hc).mp hz
  by_cases hup : expLevel u' vl b₀ n ≤ dot (expNormal u' vl) z
  · exact Or.inl (Set.mem_union_left _ ((mem_overlap_chainFull hunimod hc).mpr ⟨hzw, hup⟩))
  have hzL : dot (expNormal u' vl) z = expLevel u' vl b₀ n - 1 := by omega
  by_cases hray : t₀ + uCoord u' vl b₀ g ≤ uCoord u' vl b₀ z
  · -- on the ray
    refine Or.inl (Set.mem_union_right _ (mem_ray.mpr
      ⟨uCoord u' vl b₀ z - uCoord u' vl b₀ g, by omega, ?_⟩))
    have h1 := eq_coords hunimod (z - g)
    rw [dot_sub, hzL, hg, sub_self, zero_smul, zero_add, uCoord_sub' b₀] at h1
    rw [← h1]
    abel
  · -- strictly before the ray: one generation step, corner on `z`
    refine Or.inr ⟨z - a, by abel, fun b hb => ?_⟩
    have hbS : b ∈ Sφ := Finset.mem_of_mem_erase hb
    have hba : b ≠ a := Finset.ne_of_mem_erase hb
    obtain ⟨hα, hβ⟩ := hcorner b hbS
    have hpt : b + (z - a) = z + (b - a) := by abel
    rw [hpt]
    have hw : z + (b - a) ∈ wedgeFull B vl u' :=
      add_mem_wedgeFull_of_nonneg hunimod hzw (by rw [uCoord_sub_eq]; exact hβ)
    have hlev : dot (expNormal u' vl) (z + (b - a)) =
        dot (expNormal u' vl) z + dot (expNormal u' vl) (b - a) := dot_add _ _ _
    rcases lt_or_eq_of_le hα with hpos | hzero
    · -- one level up: inside `overlap (chainFull n)`
      exact Or.inl (Set.mem_union_left _
        ((mem_overlap_chainFull hunimod hc).mpr ⟨hw, by omega⟩))
    · -- same level: on the line, strictly closer to the ray
      refine Or.inr ⟨(mem_overlap_chainFull hunimod hc).mpr ⟨hw, by omega⟩, ?_⟩
      have hβpos : 0 < uCoord u' vl a b := by
        rcases lt_or_eq_of_le hβ with h | h
        · exact h
        · exfalso
          apply hba
          have h1 := eq_coords hunimod (b - a)
          rw [← hzero, uCoord_sub_eq, ← h, zero_smul, zero_smul, add_zero] at h1
          exact sub_eq_zero.mp h1
      have hu : uCoord u' vl b₀ (z + (b - a)) = uCoord u' vl b₀ z + uCoord u' vl a b := by
        rw [uCoord_add, uCoord_sub_eq]
      show (t₀ + uCoord u' vl b₀ g - uCoord u' vl b₀ (z + (b - a))).toNat <
        (t₀ + uCoord u' vl b₀ g - uCoord u' vl b₀ z).toNat
      rw [hu]
      omega

/-! ## §5  A corner of a generating set generates -/

/-- The functional maximised uniquely at the corner: `-(en + m')` with `dot m' w = uCoord 0 w`.
`hcorner` (原符号) says `a` minimises `en + m'` on `S`, i.e. `a` maximises this. -/
noncomputable def cornerNormal (u' vl : ℤ × ℤ) : ℤ × ℤ :=
  -(expNormal u' vl + (det u' vl) • (vl.2, -vl.1))

/-- **翻号后的对偶功能函数**（2026-09-20）：`m' - en`.  `hcornerLe`
（`0 ≤ dot en (b − a) ∧ uCoord u' vl a b ≤ 0`）恰说 `a` 是它在 `S` 上的唯一最大点。

两个符号对应锥的两个不同顶角，**都是真顶点**；哪一个可用由 `hadj`
（`b3_colle2.txt:764` 的相邻性）决定，见 `EnvFit.lean` §11o 的两条内核事实
`exists_adjacent_and_corner_le` / `not_exists_adjacent_and_corner_nonneg_on_Sw`。 -/
noncomputable def cornerNormalLe (u' vl : ℤ × ℤ) : ℤ × ℤ :=
  (det u' vl) • (vl.2, -vl.1) - expNormal u' vl

theorem dot_cornerNormal (w : ℤ × ℤ) :
    dot (cornerNormal u' vl) w = -(dot (expNormal u' vl) w + uCoord u' vl 0 w) := by
  simp only [cornerNormal, uCoord, expNormal, dot, det, Prod.fst_add, Prod.snd_add,
    Prod.fst_neg, Prod.snd_neg,
    Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Prod.fst_sub, Prod.snd_sub,
    Prod.fst_zero, Prod.snd_zero]
  ring

theorem dot_cornerNormalLe (w : ℤ × ℤ) :
    dot (cornerNormalLe u' vl) w = uCoord u' vl 0 w - dot (expNormal u' vl) w := by
  simp only [cornerNormalLe, uCoord, expNormal, dot, det,
    Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Prod.fst_sub, Prod.snd_sub,
    Prod.fst_zero, Prod.snd_zero]
  ring

theorem dot_cornerNormal_sub (z a : ℤ × ℤ) :
    dot (cornerNormal u' vl) z - dot (cornerNormal u' vl) a =
      -(dot (expNormal u' vl) (z - a) + uCoord u' vl a z) := by
  rw [← dot_sub, dot_cornerNormal, uCoord_sub_eq]

theorem dot_cornerNormalLe_sub (z a : ℤ × ℤ) :
    dot (cornerNormalLe u' vl) z - dot (cornerNormalLe u' vl) a =
      uCoord u' vl a z - dot (expNormal u' vl) (z - a) := by
  rw [← dot_sub, dot_cornerNormalLe, uCoord_sub_eq]

theorem uCoord_zero_vl : uCoord u' vl 0 vl = 0 := by
  simp only [uCoord, det, Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero]
  ring

theorem prim_cornerNormal (hunimod : det u' vl = 1 ∨ det u' vl = -1) :
    Prim (cornerNormal u' vl) := by
  have h : dot (cornerNormal u' vl) vl = -1 := by
    rw [dot_cornerNormal, dot_expNormal_vl hunimod, uCoord_zero_vl]; ring
  rw [prim_iff_primitive]
  show IsCoprime (cornerNormal u' vl).1 (cornerNormal u' vl).2
  simp only [dot] at h
  exact ⟨-vl.1, -vl.2, by linear_combination -h⟩

theorem prim_cornerNormalLe (hunimod : det u' vl = 1 ∨ det u' vl = -1) :
    Prim (cornerNormalLe u' vl) := by
  have h : dot (cornerNormalLe u' vl) vl = -1 := by
    rw [dot_cornerNormalLe, dot_expNormal_vl hunimod, uCoord_zero_vl]; ring
  rw [prim_iff_primitive]
  show IsCoprime (cornerNormalLe u' vl).1 (cornerNormalLe u' vl).2
  simp only [dot] at h
  exact ⟨-vl.1, -vl.2, by linear_combination -h⟩

/-- `hcorner` says `a` is the unique maximiser of `cornerNormal` on `S`. -/
theorem face_eq_singleton_of_corner (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    {S : Finset (ℤ × ℤ)} {a : ℤ × ℤ} (ha : a ∈ S)
    (hcorner : ∀ b ∈ S, 0 ≤ dot (expNormal u' vl) (b - a) ∧ 0 ≤ uCoord u' vl a b) :
    face (↑S : Set (ℤ × ℤ)) (cornerNormal u' vl) = {a} := by
  ext z
  simp only [mem_face_iff, Set.mem_singleton_iff, Finset.mem_coe]
  constructor
  · rintro ⟨hzS, hzmax⟩
    obtain ⟨hα, hβ⟩ := hcorner z hzS
    have h1 := hzmax a ha
    have hsub := dot_cornerNormal_sub (u' := u') (vl := vl) z a
    have hα0 : dot (expNormal u' vl) (z - a) = 0 := by omega
    have hβ0 : uCoord u' vl a z = 0 := by omega
    have h := eq_coords hunimod (z - a)
    rw [hα0, uCoord_sub_eq, hβ0, zero_smul, zero_smul, add_zero] at h
    exact sub_eq_zero.mp h
  · intro hz
    rw [hz]
    refine ⟨ha, fun y hy => ?_⟩
    obtain ⟨hα, hβ⟩ := hcorner y hy
    have hsub := dot_cornerNormal_sub (u' := u') (vl := vl) y a
    omega

/-- **翻号版**：`hcornerLe` says `a` is the unique maximiser of `cornerNormalLe` on `S`. -/
theorem face_eq_singleton_of_corner_le (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    {S : Finset (ℤ × ℤ)} {a : ℤ × ℤ} (ha : a ∈ S)
    (hcorner : ∀ b ∈ S, 0 ≤ dot (expNormal u' vl) (b - a) ∧ uCoord u' vl a b ≤ 0) :
    face (↑S : Set (ℤ × ℤ)) (cornerNormalLe u' vl) = {a} := by
  ext z
  simp only [mem_face_iff, Set.mem_singleton_iff, Finset.mem_coe]
  constructor
  · rintro ⟨hzS, hzmax⟩
    obtain ⟨hα, hβ⟩ := hcorner z hzS
    have h1 := hzmax a ha
    have hsub := dot_cornerNormalLe_sub (u' := u') (vl := vl) z a
    have hα0 : dot (expNormal u' vl) (z - a) = 0 := by omega
    have hβ0 : uCoord u' vl a z = 0 := by omega
    have h := eq_coords hunimod (z - a)
    rw [hα0, uCoord_sub_eq, hβ0, zero_smul, zero_smul, add_zero] at h
    exact sub_eq_zero.mp h
  · intro hz
    rw [hz]
    refine ⟨ha, fun y hy => ?_⟩
    obtain ⟨hα, hβ⟩ := hcorner y hy
    have hsub := dot_cornerNormalLe_sub (u' := u') (vl := vl) y a
    omega

/-- **The corner generates.**  `IsVtx` via `cornerNormal`, then `isColleVertex_of_isVtx`
(`LatticeEdges.lean:380`), then `IsGeneratingSet`'s third conjunct. -/
theorem generatesAt_of_corner {A : Type*} {ξ : Config A}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    {S : Finset (ℤ × ℤ)} (hSgen : IsGeneratingSet ξ S) {a : ℤ × ℤ} (ha : a ∈ S)
    (hcorner : ∀ b ∈ S, 0 ≤ dot (expNormal u' vl) (b - a) ∧ 0 ≤ uCoord u' vl a b) :
    GeneratesAt ξ S a := by
  have hvtx : IsVtx (↑S : Set (ℤ × ℤ)) a :=
    ⟨cornerNormal u' vl, prim_cornerNormal hunimod, face_eq_singleton_of_corner hunimod ha hcorner⟩
  have hcv := isColleVertex_of_isVtx hSgen.2.1 hvtx
  exact hSgen.2.2 a hcv.1 hcv.2

/-- **翻号版的 corner generates.**  `𝒮_{φ_ι}` 上的顶角（`b3_colle2.txt:790-796`）。 -/
theorem generatesAt_of_corner_le {A : Type*} {ξ : Config A}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    {S : Finset (ℤ × ℤ)} (hSgen : IsGeneratingSet ξ S) {a : ℤ × ℤ} (ha : a ∈ S)
    (hcorner : ∀ b ∈ S, 0 ≤ dot (expNormal u' vl) (b - a) ∧ uCoord u' vl a b ≤ 0) :
    GeneratesAt ξ S a := by
  have hvtx : IsVtx (↑S : Set (ℤ × ℤ)) a :=
    ⟨cornerNormalLe u' vl, prim_cornerNormalLe hunimod,
      face_eq_singleton_of_corner_le hunimod ha hcorner⟩
  have hcv := isColleVertex_of_isVtx hSgen.2.1 hvtx
  exact hSgen.2.2 a hcv.1 hcv.2

/-! ## §6  The bottom face of `S₁` sits on the new line -/

/-- Under Cprobe's placement (all of `S₁` at level `≥ L`, and `L` attained), a point of `S₁`
outside `derivedQ (εOf u' vl)` is exactly at level `L`. -/
theorem dot_eq_of_not_mem_derivedQ (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    {S₁ : Finset (ℤ × ℤ)} {L : ℤ}
    (hmin : ∀ s ∈ S₁, L ≤ dot (expNormal u' vl) s)
    (hattain : ∃ s ∈ S₁, dot (expNormal u' vl) s = L)
    {g : ℤ × ℤ} (hg : g ∈ S₁) (hgQ : g ∉ derivedQ (εOf u' vl) u' S₁) :
    dot (expNormal u' vl) g = L := by
  obtain ⟨s, hs, hsL⟩ := hattain
  have hne : S₁.Nonempty := ⟨s, hs⟩
  unfold derivedQ at hgQ
  rw [Finset.mem_filter, not_and] at hgQ
  have hle : levelMax S₁ (cutNormal (εOf u' vl) u') ≤ inner2 (cutNormal (εOf u' vl) u') g :=
    not_lt.mp (hgQ hg)
  have hs' := le_levelMax (n := cutNormal (εOf u' vl) u') hne s hs
  rw [cutNormal_εOf hunimod, inner2_toReal, dot_neg_left] at hle hs'
  have h2 : -(dot (expNormal u' vl) s) ≤ -(dot (expNormal u' vl) g) := by
    exact_mod_cast le_trans hs' hle
  have := hmin g hg
  omega

/-! ## §7  The slot -/

/-- **`hstraddle` of `exists_L1MaxBResidual_of_wedgeAt_split`, at `ε := εOf u' vl`.**
Hypotheses beyond the slot's own: `0 ≤ c` (team WLOG `0 < c`), the maximal index `N₀` with its
two witnesses, Cprobe's placement `hmin` **plus its attained minimum** `hattain` (without it the
bottom face could sit inside `chainFull (k+N₀)` and `Straddle` would be false at a maximal
index), a generating window `Sφ` with a corner `a` (`hcorner`).  The `∀ N` collapses to `N₀` by
`maximal_index_unique`; the line fact at `τ` is not needed (the `Straddle` proved holds for every
`τ`). -/
theorem hstraddle_of_corner {ξ : Config ℤ} {e : ℤ × ℤ} {B : Set (ℤ × ℤ)} {b₀ : ℤ × ℤ}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) {c : ℤ} (hc : 0 ≤ c) {k N₀ : ℕ}
    (hN₀ : PeriodOn (T e ξ) (chainFull B vl u' b₀ (k + N₀)) (c • vl))
    (hN₀1 : ¬ PeriodOn (T e ξ) (chainFull B vl u' b₀ (k + (N₀ + 1))) (c • vl))
    {S₁ : Finset (ℤ × ℤ)}
    (hmin : ∀ s ∈ S₁, expLevel u' vl b₀ (k + N₀) - 1 ≤ dot (expNormal u' vl) s)
    (hattain : ∃ s ∈ S₁, dot (expNormal u' vl) s = expLevel u' vl b₀ (k + N₀) - 1)
    {Sφ : Finset (ℤ × ℤ)} (hSφ : IsGeneratingSet ξ Sφ) {a : ℤ × ℤ} (ha : a ∈ Sφ)
    (hcorner : ∀ b ∈ Sφ, 0 ≤ dot (expNormal u' vl) (b - a) ∧ 0 ≤ uCoord u' vl a b) :
    ∀ N : ℕ, PeriodOn (T e ξ) (chainFull B vl u' b₀ (k + N)) (c • vl) →
      ¬ PeriodOn (T e ξ) (chainFull B vl u' b₀ (k + (N + 1))) (c • vl) →
      ∀ τ : ℤ,
        (∀ z ∈ derivedQ (εOf u' vl) u' S₁,
          τ • u' + z ∈ chainFull B vl u' b₀ (k + N) ∧
          τ • u' + z + c • vl ∈ chainFull B vl u' b₀ (k + N)) →
        Nivat.L1Region.Straddle (T e ξ) (chainFull B vl u' b₀ (k + N))
          (chainFull B vl u' b₀ (k + (N + 1))) S₁ (derivedQ (εOf u' vl) u' S₁) vl u' c τ := by
  intro N hN hN1 τ _hline
  have hNN : N = N₀ :=
    Nivat.L1Prim.maximal_index_unique (monotone_chainFull_shift B vl u' b₀ k) hN hN1 hN₀ hN₀1
  subst hNN
  refine straddle_of_cover (T_mem_orbitClosure ξ e)
    (generatesAt_of_corner hunimod hSφ ha hcorner) ?_
  intro g hg hgQ t₀ _
  exact cover_line hunimod hc hcorner (dot_eq_of_not_mem_derivedQ hunimod hmin hattain hg hgQ) t₀

/-! ## §8  §27 feeding term: the slot fed into `exists_L1MaxBResidual_of_unimod_split` -/

/-- `Nivat.ColleReg.L1Claim.exists_L1MaxBResidual_of_unimod_split` (`L1Claim.lean:1033`) with
`ε := εOf u' vl`, `hline := L1Line0.hline_of_placement` (Cprobe) and
`hstraddle := hstraddle_of_corner` at `Sφ := d.Sphi`, `hSφ := d.isGeneratingSet`.
(2026-09-19 19:3x, team-lead/Cclaim: rewired from `L1Line0.exists_L1MaxBResidual_of_placement`
to `_of_unimod_split`, so `hEnv : EnvOf U B` and `hlev : LevelInterval B vl` are no longer
demanded on this route.)  What remains as binders: the C-group data `hb₀ hunimod hbase`, the
maximal index, the placement (`hmin`, `hattain`, both produced by `exists_shift_min_level`), and
the corner `a` of `d.Sphi` for this `u'`. -/
theorem exists_L1MaxBResidual_of_corner
    {ξ : Config ℤ} {ℓ : ℤ × ℤ} {S : Finset (ℤ × ℤ)}
    (hξ : IsMinimalCounterexample ξ) (d : Nivat.Colle35.DecompDataZ ξ)
    (hℓ_nel : ℓ ∈ Colle45.NonExpansiveLine ξ)
    (hℓ_neg : Colle45.IsOneSidedNonexpansive ξ (-ℓ))
    (hSgen : IsGeneratingSet ξ S)
    (hvl_prim : Primitive vl) (hdet_ℓ : dot ℓ vl = 0)
    {e v b₀ : ℤ × ℤ} {c : ℤ} {B : Set (ℤ × ℤ)}
    (hb₀ : b₀ ∈ B)
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) (hc : 0 < c) (k : ℕ)
    (hbase : PeriodOn (T e ξ) (chainFull B vl u' b₀ k) (c • vl))
    {N₀ : ℕ}
    (hN₀ : PeriodOn (T e ξ) (chainFull B vl u' b₀ (k + N₀)) (c • vl))
    (hN₀1 : ¬ PeriodOn (T e ξ) (chainFull B vl u' b₀ (k + (N₀ + 1))) (c • vl))
    (hmin : ∀ s ∈ S.image (· + v),
      expLevel u' vl b₀ (k + N₀) - 1 ≤ dot (expNormal u' vl) s)
    (hattain : ∃ s ∈ S.image (· + v),
      dot (expNormal u' vl) s = expLevel u' vl b₀ (k + N₀) - 1)
    {a : ℤ × ℤ} (ha : a ∈ d.Sphi)
    (hcorner : ∀ b ∈ d.Sphi, 0 ≤ dot (expNormal u' vl) (b - a) ∧ 0 ≤ uCoord u' vl a b) :
    ∃ (e u u' v : ℤ × ℤ) (c τ : ℤ) (ε : Bool) (S₁ : Finset (ℤ × ℤ))
      (F : Nivat.L1Region.RegionFamily (T e ξ) u u' c),
      S₁ = S.image (· + v) ∧
      Nivat.ColleReg.L1Data.MaxBResidual (ξ := ξ) ε u u' c τ S₁ F :=
  Nivat.ColleReg.L1Claim.exists_L1MaxBResidual_of_unimod_split hξ d hℓ_nel hℓ_neg hSgen
    hvl_prim hdet_ℓ (εOf u' vl) hb₀ hunimod hc.ne' k hbase
    (Nivat.L1Line0.hline_of_placement hb₀ hunimod hc hN₀ hN₀1 hmin)
    (hstraddle_of_corner hunimod hc.le hN₀ hN₀1 hmin hattain d.isGeneratingSet ha hcorner)

/-! ## §9  `hcorner` is satisfiable after shearing `u'` along `vl` — kernel fact, not a reading

`u' ↦ u' − K•vl` keeps `det u' vl` (so `hunimod`, `εOf`, `uCoord` are unchanged) and moves the
`expNormal`-level of `w` by `K · uCoord 0 w`.  Taking `a` with minimal `u'`-coordinate in `S`
(ties broken by minimal level) and `K` at least the level spread of `S` gives `hcorner`.
⚠ What this does **not** do: transport `hbase` / `hlev` / `hmin` from `u'` to `u' − K•vl`.
Those are stated at the shared `u'`; whether they survive the shear is the joint-data question
left open in the module docstring. -/

theorem det_shear (K : ℤ) : det (u' - K • vl) vl = det u' vl := by
  simp only [det, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

theorem uCoord_shear (K : ℤ) (a b : ℤ × ℤ) :
    uCoord (u' - K • vl) vl a b = uCoord u' vl a b := by
  simp only [uCoord, det, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

theorem dot_expNormal_shear (K : ℤ) (w : ℤ × ℤ) :
    dot (expNormal (u' - K • vl) vl) w = dot (expNormal u' vl) w + K * uCoord u' vl 0 w := by
  simp only [expNormal, uCoord, dot, det, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul, sub_zero]
  ring

theorem uCoord_eq_sub (a b : ℤ × ℤ) :
    uCoord u' vl a b = uCoord u' vl 0 b - uCoord u' vl 0 a := by
  rw [← uCoord_sub_eq, uCoord_sub' 0]

/-- **The wedge is shear-invariant.**  `wedgeFull B vl u'` only depends on `u'` modulo `vl`
(`fullSweep` already contains every `ℤ•vl` translate), so `u' ↦ u' − K•vl` leaves it unchanged.
Under the shear, `chainFull B vl u'' b₀ n = cut (wedgeFull B vl u') (expNormal u'' vl) …` — the
wedge is the same set, only the level cut tilts (`dot_expNormal_shear`). -/
theorem wedgeFull_shear {B : Set (ℤ × ℤ)} (K : ℤ) :
    wedgeFull B vl (u' - K • vl) = wedgeFull B vl u' := by
  ext z
  constructor
  · rintro ⟨g, hg, r, rfl⟩
    obtain ⟨b, hb, k, rfl⟩ := mem_fullSweep_iff.mp hg
    refine ⟨b + (k - (r : ℤ) * K) • vl, mem_fullSweep_iff.mpr ⟨b, hb, _, rfl⟩, r, ?_⟩
    ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Prod.fst_sub,
      Prod.snd_sub, smul_eq_mul] <;> ring
  · rintro ⟨g, hg, r, rfl⟩
    obtain ⟨b, hb, k, rfl⟩ := mem_fullSweep_iff.mp hg
    refine ⟨b + (k + (r : ℤ) * K) • vl, mem_fullSweep_iff.mpr ⟨b, hb, _, rfl⟩, r, ?_⟩
    ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Prod.fst_sub,
      Prod.snd_sub, smul_eq_mul] <;> ring

/-- **`hcorner` after a shear.**  For every nonempty finite `S` some `K` and some `a ∈ S`
satisfy `hcorner` at `u' − K•vl`. -/
theorem exists_corner_shear {S : Finset (ℤ × ℤ)} (hS : S.Nonempty) :
    ∃ K : ℤ, ∃ a ∈ S, ∀ b ∈ S,
      0 ≤ dot (expNormal (u' - K • vl) vl) (b - a) ∧ 0 ≤ uCoord (u' - K • vl) vl a b := by
  classical
  obtain ⟨β₀, hβ₀mem, hβ₀min⟩ := S.exists_min_image (fun z => uCoord u' vl 0 z) hS
  set S₀ := S.filter (fun z => uCoord u' vl 0 z = uCoord u' vl 0 β₀) with hS₀def
  have hS₀ne : S₀.Nonempty := ⟨β₀, Finset.mem_filter.mpr ⟨hβ₀mem, rfl⟩⟩
  obtain ⟨a, haS₀, hamin⟩ := S₀.exists_min_image (fun z => dot (expNormal u' vl) z) hS₀ne
  have haS : a ∈ S := (Finset.mem_filter.mp haS₀).1
  have hau : uCoord u' vl 0 a = uCoord u' vl 0 β₀ := (Finset.mem_filter.mp haS₀).2
  obtain ⟨M, hM⟩ := Finset.exists_le
    (S.image fun z => dot (expNormal u' vl) a - dot (expNormal u' vl) z)
  refine ⟨max M 0, a, haS, fun b hb => ?_⟩
  have hβ : 0 ≤ uCoord u' vl a b := by
    have h1 := hβ₀min b hb
    rw [uCoord_eq_sub]
    omega
  refine ⟨?_, by rw [uCoord_shear]; exact hβ⟩
  rw [dot_expNormal_shear, uCoord_sub_eq, dot_sub]
  have hMb : dot (expNormal u' vl) a - dot (expNormal u' vl) b ≤ M :=
    hM _ (Finset.mem_image_of_mem _ hb)
  have hK1 : M ≤ max M 0 := le_max_left M 0
  have hK0 : 0 ≤ max M 0 := le_max_right M 0
  rcases lt_or_eq_of_le hβ with hpos | hzero
  · have hKβ : max M 0 ≤ max M 0 * uCoord u' vl a b :=
      le_mul_of_one_le_right hK0 (by omega)
    omega
  · have hbS₀ : b ∈ S₀ := by
      refine Finset.mem_filter.mpr ⟨hb, ?_⟩
      have := uCoord_eq_sub (u' := u') (vl := vl) a b
      omega
    have h2 := hamin b hbS₀
    rw [← hzero, mul_zero, add_zero]
    omega

/-- **Corner shear for all large `K`** (team-lead 2026-09-20): pull the threshold out so the
conclusion holds for every `K` above it, with `a` chosen once, independent of `K`.

The existing proof chooses `a` and `M` before constructing `K := max M 0`, and no step needs the
exact value — only `M ≤ K` and `0 ≤ K`. The `uCoord` inequality (`:437-440`) is independent of `K`;
the `dot` inequality splits on `uCoord u' vl a b > 0` (`:447-450`, larger `K` only helps) vs `= 0`
(`:451-457`, `K` drops out). Pure binder reordering. -/
theorem exists_corner_shear_of_le {S : Finset (ℤ × ℤ)} (hS : S.Nonempty) :
    ∃ (M : ℤ) (a : ℤ × ℤ), a ∈ S ∧ ∀ K : ℤ, M ≤ K → ∀ b ∈ S,
      0 ≤ dot (expNormal (u' - K • vl) vl) (b - a) ∧ 0 ≤ uCoord (u' - K • vl) vl a b := by
  classical
  obtain ⟨β₀, hβ₀mem, hβ₀min⟩ := S.exists_min_image (fun z => uCoord u' vl 0 z) hS
  set S₀ := S.filter (fun z => uCoord u' vl 0 z = uCoord u' vl 0 β₀) with hS₀def
  have hS₀ne : S₀.Nonempty := ⟨β₀, Finset.mem_filter.mpr ⟨hβ₀mem, rfl⟩⟩
  obtain ⟨a, haS₀, hamin⟩ := S₀.exists_min_image (fun z => dot (expNormal u' vl) z) hS₀ne
  have haS : a ∈ S := (Finset.mem_filter.mp haS₀).1
  have hau : uCoord u' vl 0 a = uCoord u' vl 0 β₀ := (Finset.mem_filter.mp haS₀).2
  obtain ⟨M, hM⟩ := Finset.exists_le
    (S.image fun z => dot (expNormal u' vl) a - dot (expNormal u' vl) z)
  refine ⟨max M 0, a, haS, fun K hK b hb => ?_⟩
  have hβ : 0 ≤ uCoord u' vl a b := by
    have h1 := hβ₀min b hb
    rw [uCoord_eq_sub]
    omega
  refine ⟨?_, by rw [uCoord_shear]; exact hβ⟩
  rw [dot_expNormal_shear, uCoord_sub_eq, dot_sub]
  have hMb : dot (expNormal u' vl) a - dot (expNormal u' vl) b ≤ M :=
    hM _ (Finset.mem_image_of_mem _ hb)
  have hK1 : M ≤ K := le_trans (le_max_left M 0) hK
  have hK0 : 0 ≤ K := le_trans (le_max_right M 0) hK
  rcases lt_or_eq_of_le hβ with hpos | hzero
  · have hKβ : K ≤ K * uCoord u' vl a b :=
      le_mul_of_one_le_right hK0 (by omega)
    omega
  · have hbS₀ : b ∈ S₀ := by
      refine Finset.mem_filter.mpr ⟨hb, ?_⟩
      have := uCoord_eq_sub (u' := u') (vl := vl) a b
      omega
    have h2 := hamin b hbS₀
    rw [← hzero, mul_zero, add_zero]
    omega

/-! **目标（未证，2026-09-20 集成者把 `sorry` 骨架降级为注释）：`exists_corner_of_no_normal_between`**

原文：`b3_colle2.txt:764` — "Suppose `ℓ₁,…,ℓ_{2m} ⊂ ℝ²` is an enumeration of the oriented lines
through the origin **parallels to the edges of `𝒮_φ`** where the edge parallel to `ℓ_{i+1}` is a
**successor** of the edge parallel to `ℓ_i`" (repeated verbatim at `:424`, `:541`). At `:780-781`,
Claim 4.6 defines `𝓡_{ι-1} := {g + t·v_{ℓ_{ι-1}} : g ∈ H_B(ℓ), t ∈ ℤ_+}` where `v_{ℓ_{ι-1}}` is the
edge direction **adjacent** to `ℓ_ι = ℓ` in this cyclic order, making `𝓡_{ι-1}` a `(-ℓ, ℓ_{ι-1})`-region.
Two consecutive edge directions span a wedge; a convex `𝒮_φ` has a **vertex** at the corner between
them satisfying `hcorner` with no shear (`K = 0`).

待办三问（集成者已代查，见派工单）：`E R` 是**外法向**集（`LatticeEdges.lean:217`），
`face`/`suppVal`/`mem_of_dot_le_suppVal` (`:1393`/`face_eq_of_supportLevel` `:195`) 皆在库中。

**Template proof**: `Nivat.EnvFit.exists_lean_point_of_noEdgeBetween` (`EnvFit.lean:2258-2368`) —
structurally the same problem (extreme point in cone order given no edge normal in forbidden cone),
method is finite argmin done twice then contradiction via an edge normal `f` maximised at two points.
-/

/-! **Corner from adjacent edges** (team-lead 2026-09-20): `hcorner` at `K = 0` when no edge normal
lies between `u'` and `vl` in the cone order.

原文：`b3_colle2.txt:764` — cyclic successor ordering of edge directions; see the block above.

**Consumer**: `Nivat.ColleReg.wedgeResidualR_of_case1_of_cone` (`RegionSteps.lean`), binders `ha` +
`hcorner`, with `S := d.toDecompData.Sphi`.

**Adjacency hypothesis**: `hbetween` says every outer normal `ν ∈ E ↑S` makes a non-obtuse angle
with at least one of `{u', vl}`, i.e. `0 ≤ dot ν u' ∨ 0 ≤ dot ν vl`. Equivalently: no normal points
into the quadrant where both `dot ν u' < 0` and `dot ν vl < 0` — this is the successor relation of
`:764` spelled as a sign condition, without cyclic-order apparatus.

**Proof template**: follows `Nivat.EnvFit.exists_lean_point_of_noEdgeBetween` (`EnvFit.lean:2258`).

🔴 **2026-09-20 集成者降级：以下证明编译不过，整条从主仓下架。** Lstrad 落地时 Bash 被拒，
没能自测；实测 `check1.sh` 报三处错并让 `exists_corner` 依赖 `sorryAx`：

```
:536:34 Application type mismatch: The argument
:552:9  Invalid `⟨...⟩` notation: The expected type
:553:2  No goals to be solved
'Nivat.L1StraddleWedge.exists_corner' depends on axioms:
  [propext, sorryAx, Classical.choice, Quot.sound]
```

`:536` 是 `S.exists_min_image (fun z => uCoord u' vl 0 z) hSne` 的实参不匹配——
`Finset.exists_min_image` 在本版 Mathlib 里的参数顺序/隐参与这里给的不同，先 `#check` 再用。
**签名本身没有问题**（`hbetween` 是 `:764` 相邻性的符号写法，逐量词可追溯），所以原样保留成
拟证目标；修好并 `check1.sh` EXIT=0 之后再落地。

```lean
theorem exists_corner {S : Finset (ℤ × ℤ)} {vl u' : ℤ × ℤ}
    (hSne : S.Nonempty) (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hSconv : Nivat.LatticeConvex (↑S : Set (ℤ × ℤ)))
    (hbetween : ∀ ν ∈ Nivat.LE2.E (↑S : Set (ℤ × ℤ)),
        0 ≤ Nivat.LE2.dot ν u' ∨ 0 ≤ Nivat.LE2.dot ν vl) :
    ∃ a ∈ S, ∀ b ∈ S,
      0 ≤ dot (expNormal u' vl) (b - a) ∧ 0 ≤ uCoord u' vl a b
```

证明骨架（Lstrad 写的，三处错见上）：Step 1 在 `S` 上对 `uCoord u' vl 0 ·` 取极小得 `a0`；
Step 2 在同一 `uCoord` 层里对 `dot (expNormal u' vl) ·` 取极小得 `a`；Step 3 反证——
若某 `b` 违反第一合取，构造法向 `f := d2 • expNormal u' vl + d1 • (u'-坐标法向)`，
证明它在 `a` 与 `zs` 两点同时取到最大值，于是 `f ∈ E ↑S`，与 `hbetween f` 矛盾。
这一步的模板是 `EnvFit.exists_lean_point_of_noEdgeBetween`（`EnvFit.lean:2258-2368`）。
-/

/-! **撤回 (2026-09-20, 集成者第四次)：`exists_corner` 的 `sorry` 骨架删除。**

Lstrad 第四次把同一条带 `sorry` 的骨架落进主仓。签名逐记号追溯见上面的文档块，
**保留成拟证目标**；证出来之前不要再落地。拟证签名：

```lean
theorem exists_corner {S : Finset (ℤ × ℤ)} {vl u' : ℤ × ℤ}
    (hSne : S.Nonempty) (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hSconv : Nivat.LatticeConvex (↑S : Set (ℤ × ℤ)))
    (hbetween : ∀ ν ∈ Nivat.LE2.E (↑S : Set (ℤ × ℤ)),
        0 ≤ Nivat.LE2.dot ν u' ∨ 0 ≤ Nivat.LE2.dot ν vl) :
    ∃ a ∈ S, ∀ b ∈ S,
      0 ≤ dot (expNormal u' vl) (b - a) ∧ 0 ≤ uCoord u' vl a b
```

⚠ **工具盲区，本轮实测新增**：`scripts/sorries.sh` **没有报出这一条**（它按声明解析
build 产物，而 `L1StraddleWedge.lean` 自上次 `lake build` 后被改过），TOTAL 仍显示 2。
抓到它的是 `grep -n sorry` 对单文件的直接扫描。**硬规矩 3 的「只信脚本」在文件比 build 新时
失效**，与工具盲区 1 同源。 -/

section Receipts2026Sep20
#print axioms exists_corner_shear_of_le
end Receipts2026Sep20

/-! **撤回：`no_nonpos_K_corner` 的见证块（2026-09-20，集成者删）。**

Lstrad 曾在此放一个 `example` 断言「没有任何 `K ≤ 0` 满足 `hcorner`」，带两个 `sorry`。
删除有两条理由，第一条是硬规矩：

* **agent 不许把 `sorry` 落进主仓**（CLAUDE.md 并发与写权限）。`scripts/sorries.sh` 当场
  报 TOTAL=4（主线 2 条 + 此处 2 条）。
* **该断言为假。** 取它自己的见证 `u' = (1,0)`、`vl = (0,1)`、`S = {(0,0),(1,1)}`：
  `det u' vl = 1`，`expNormal u' vl = 1 • (-0,1) = (0,1)`，于是 `K = 0`、`a = (0,0)` 下
  `dot (0,1) ((1,1)-(0,0)) = 1 ≥ 0`，第一合取成立。`K = 0` **是**一个可用的 `K`，
  所以「没有 `K ≤ 0` 可用」不成立。块内注释「Actually this doesn't immediately
  contradict... let me reconsider the witness」已经说出了这一点。

这条问题本身也已经作废：`:764` 的后继枚举确定了原文走的就是 `K = 0`，
「`K ≤ 0` 行不行」不再是决策点。保留本说明而不是静默删除，依 `PROTOCOL.md` §14。 -/

section Receipts2026Sep20
#print axioms exists_corner_shear_of_le
end Receipts2026Sep20

end Nivat.L1StraddleWedge

section Receipts
/-! Standing `#print axioms` receipts.  Deletable as a block. -/

#print axioms Nivat.L1StraddleWedge.eq_coords
#print axioms Nivat.L1StraddleWedge.add_mem_wedgeFull_of_nonneg
#print axioms Nivat.L1StraddleWedge.mem_overlap_chainFull
#print axioms Nivat.L1StraddleWedge.cover_line
#print axioms Nivat.L1StraddleWedge.prim_cornerNormal
#print axioms Nivat.L1StraddleWedge.face_eq_singleton_of_corner
#print axioms Nivat.L1StraddleWedge.generatesAt_of_corner
#print axioms Nivat.L1StraddleWedge.dot_eq_of_not_mem_derivedQ
#print axioms Nivat.L1StraddleWedge.hstraddle_of_corner
#print axioms Nivat.L1StraddleWedge.exists_L1MaxBResidual_of_corner
#print axioms Nivat.L1StraddleWedge.exists_corner_shear
#print axioms Nivat.L1StraddleWedge.wedgeFull_shear

end Receipts
