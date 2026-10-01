/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.TowerLevelStep
import Nivat.External.Colle.LatticeEdges

/-!
# `LevelInterval B vl` from the two `vl`-parallel edges of `B` (lane-tower-hlev)

**What this is.**  `lane-towerpkg`'s sole residual is

```
hconv : ∀ n ≤ (sortedCand d nℓ u' i).length + 1 →
  IsLatticeConvexRegion (tower (coneRegion B vl u') (wtower d nℓ vl u' i) n)
```

and `tower _ _ 0 = R₀` makes the `n = 0` instance `IsLatticeConvexRegion (coneRegion B vl u')`.
This file discharges that instance.

**Why it is true, and why it is not free.**  The `LevelInterval` route of
`TowerLevelStep.lean` cannot reach it: `lane-tower-hbase`'s `det_wtower_vl_mul_u'_pos`
(`TowerHBaseMin.lean` §6) shows every candidate direction has `p < 0 < q` in the basis
`(vl, u')`, so the two available unit steps never combine to `±1`.  The content has to come
from the **seed** `B`, and it does:

原文：b3_colle2.txt:806-808（塔以 `𝒮_φ` 的边方向循环序扫掠）。 `d.h i` is the generator with
`dot nℓ (d.h i) = 0` (`hdoth`), i.e. `d.h i = c • vl` (`TowerConstruct.h_i_eq_zsmul_vl`).
`DecompData.Sphi_eq` (`DecompData.lean:108`) makes `Conv d.Sphi` a zonotope, so
`genPerp'_mem_E_B` (`TowerConstruct.lean:64`) puts **both** `genPerp' (d.h i)` and its negation
in `E B` — that is `±nℓ ∈ E B`, with both faces `Nontrivial`.  Hence:

1. `B`'s top and bottom `nℓ`-faces each carry two distinct lattice points, which differ by a
   nonzero `ℤ`-multiple of `vl` (§1), so each face carries a full unit `vl`-step (§2).
2. `B` is lattice-convex, so its real witness `C` contains two parallel unit segments
   `[p, p+vl]` and `[q, q+vl]`.  Their convex hull has slice length `1` at *every*
   intermediate level.
3. A real interval of length `≥ 1` contains an integer: every intermediate level carries a
   lattice point of `B`.  That is exactly `LevelInterval B vl` (`RegionSweep.lean:174`),
   stated with `det vl` (§3).
4. `isLatticeConvexRegion_sweep` (`RegionSweep.lean:213`) then gives `sweep B vl`; the second
   sweep is free because `sweep B vl` is `+vl`-closed and `det u' vl = ±1` (`hunimod`), so
   `TowerLevelStep.levelInterval_of_step_det_one` applies with **no** hypothesis on the set
   (§5).

**Sanity check done by hand before formalising** (`CLAUDE.md` 硬规矩 6): generators
`h₁ = (1,0)` (the `vl`-parallel one) and `h₂ = (-3,5)` (a maximally long primitive edge, the
direction that breaks the single-point seed in `TowerLevelStep.lean:357`).  `Z ∩ ℤ²` has 8
points; the `≤`-minimal ones are `(0,0), (-1,2), (-2,4), (-3,5)`; the hull
`{y ≥ 0, 5x+3y ≥ 0, x ≥ -3}` has no uncovered lattice point.  The points that fill the
would-be numerical-semigroup gaps — `(-1,2)`, `(-2,4)` — are *interior* points of the
zonotope, supplied by `h₁`, i.e. by `hdoth`.

**§6 is for the induction step, not for `n = 0`.**  A tower layer is unbounded in the `det w`
direction (`det w vl` and `det w u'` have the same sign — that is
`TowerHBaseMin.det_wtower_vl_mul_u'_pos`), so it has no maximal level and `levelInterval_of_unit_steps`
does not apply.  What replaces the top step is free: with `w = p•vl + q•u'`, `p < 0 < q`, every
`y` in a `+vl`/`+u'`-closed set gives the unit step `y + (-p)•vl ↦ y + q•u'`, at levels cofinal
in `ℤ`.  So the whole content of the induction step is the **single unit `w`-step at the minimal
level**, and `exists_det_extreme_unit_steps` + `exists_min_unit_step_of_seed` pay for it out of
the seed (`w` is parallel to the generator `d.h j`, so `±genPerp' (d.h j) ∈ E B` gives `B` an
edge parallel to `w` on each side).

⚠ **撤回记录**：`tmp/wip/lane-tower-hlev-hconv-refuted.lean` 是本 lane 上一轮的 `hconv` 反例，
**已撤回**——它的 `B` 是三角形，`face B (0,1)` 是单点，违反上面的 `-nℓ ∈ E B`。同理
`TowerLevelStep.lean` §7 的 sharpness 用 `B = {(0,0)}`（`E {(0,0)} = ∅`），那几条引理证明的是
「`isRegion_tower_of_steps` 这条**路线**对一般 `w` 不通」，**不能**用来论证 `hconv` 为假。
-/

set_option autoImplicit false

namespace Nivat.LaneTowerHlevConv

open Nivat Nivat.LE2 Nivat.RegionSweep Nivat.ColleReg

/-! ## §0  `toReal` is additive and commutes with `ℤ`-scaling -/

private theorem toReal_add' (z w : ℤ × ℤ) : toReal (z + w) = toReal z + toReal w := by
  simp only [toReal, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk, Int.cast_add]

private theorem toReal_zsmul' (n : ℤ) (z : ℤ × ℤ) : toReal (n • z) = (n : ℝ) • toReal z := by
  simp only [toReal, Prod.smul_fst, Prod.smul_snd, Prod.smul_mk, smul_eq_mul, Int.cast_mul]

/-! ## §1  Two points at the same `det vl`-level differ by a `vl`-multiple -/

/-- `det w` is additive in its right argument, in subtracted form. -/
theorem det_sub_right (w a b : ℤ × ℤ) : det w (b - a) = det w b - det w a := by
  simp only [det, Prod.fst_sub, Prod.snd_sub]; ring

/-- Two lattice points on the same `det vl`-level differ by an integer multiple of `vl`.
`Primitive vl` is what makes the multiple integral. -/
theorem exists_zsmul_of_det_eq {vl a b : ℤ × ℤ} (hvl : Primitive vl)
    (h : det vl a = det vl b) : ∃ k : ℤ, b = a + k • vl := by
  have hd : det vl (b - a) = 0 := by rw [det_sub_right]; omega
  obtain ⟨k, hk⟩ := Nivat.eq_zsmul_of_det_eq_zero hvl hd
  exact ⟨k, by rw [← hk]; abel⟩

/-- `det vl` is surjective onto `ℤ` when `vl` is primitive: every level of `det vl` is a
genuine lattice line.  (Bézout on the coordinates of `vl`.) -/
theorem exists_det_eq {vl : ℤ × ℤ} (hvl : Primitive vl) (m : ℤ) :
    ∃ z : ℤ × ℤ, det vl z = m := by
  obtain ⟨u, v, huv⟩ := hvl
  refine ⟨(-(v * m), u * m), ?_⟩
  simp only [det]
  linear_combination m * huv

/-! ## §2  A unit `vl`-step from a nontrivial face perpendicular to `vl` -/

/-- Lattice convexity fills in a `vl`-run: if `p` and `p + k•vl` are both in `B` with `k ≥ 1`,
then so is `p + vl`. -/
theorem add_vl_mem_of_zsmul_mem {B : Set (ℤ × ℤ)} (hB : IsLatticeConvexRegion B)
    {p vl : ℤ × ℤ} {k : ℤ} (hk : 1 ≤ k) (hp : p ∈ B) (hpk : p + k • vl ∈ B) :
    p + vl ∈ B := by
  obtain ⟨C, hCconv, _, hBeq⟩ := hB
  have hmem : ∀ z : ℤ × ℤ, z ∈ B ↔ toReal z ∈ C := by
    intro z; rw [hBeq]; exact Iff.rfl
  rw [hmem] at hp hpk ⊢
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hkne : ((k : ℝ)) ≠ 0 := ne_of_gt hkR
  have hkey : toReal (p + vl)
      = (1 - 1 / (k : ℝ)) • toReal p + (1 / (k : ℝ)) • toReal (p + k • vl) := by
    rw [toReal_add', toReal_add', toReal_zsmul']
    match_scalars <;> (field_simp; try ring)
  rw [hkey]
  refine hCconv hp hpk ?_ ?_ (by ring)
  · have h1 : (1 : ℝ) / (k : ℝ) ≤ 1 := by
      rw [div_le_one hkR]
      exact_mod_cast hk
    linarith
  · positivity

/-- **The unit step at a face.**  If `n ⟂ vl` and the exposed face of `B` in direction `n`
carries two distinct lattice points, then some `dot n`-maximiser admits a full unit `vl`-step
inside `B`.  (`dot n (c + vl) = dot n c` by `hperp`, so the step stays on the face.) -/
theorem exists_unit_step_of_face {B : Set (ℤ × ℤ)} {n vl : ℤ × ℤ}
    (hB : IsLatticeConvexRegion B) (hvl : Primitive vl) (hprim : Prim n)
    (hperp : dot n vl = 0) (hface : (face B n).Nontrivial) :
    ∃ c ∈ B, (∀ z ∈ B, dot n z ≤ dot n c) ∧ c + vl ∈ B := by
  obtain ⟨p, hp, q, hq, hpq⟩ := hface
  obtain ⟨hpB, hpmax⟩ := hp
  obtain ⟨hqB, hqmax⟩ := hq
  have hdot : dot n q = dot n p := le_antisymm (hpmax q hqB) (hqmax p hpB)
  have hdot0 : dot n (q - p) = 0 := by rw [dot_sub]; omega
  have hdet : det vl (q - p) = 0 :=
    Nivat.LE2.det_eq_zero_of_dot_eq_zero hprim.ne_zero hperp hdot0
  obtain ⟨k, hk⟩ := Nivat.eq_zsmul_of_det_eq_zero hvl hdet
  have hk0 : k ≠ 0 := by
    rintro rfl
    have hz : q - p = 0 := by rw [hk]; simp
    exact hpq (sub_eq_zero.mp hz).symm
  rcases lt_or_gt_of_ne hk0 with hneg | hpos
  · -- `k ≤ -1`: the run goes from `q` to `p`.
    refine ⟨q, hqB, fun z hz => by rw [hdot]; exact hpmax z hz, ?_⟩
    refine add_vl_mem_of_zsmul_mem hB (k := -k) (by omega) hqB ?_
    have hqp : q + (-k) • vl = p := by rw [neg_smul, ← hk]; abel
    rw [hqp]; exact hpB
  · -- `k ≥ 1`: the run goes from `p` to `q`.
    refine ⟨p, hpB, hpmax, ?_⟩
    refine add_vl_mem_of_zsmul_mem hB (k := k) (by omega) hpB ?_
    have hpq' : p + k • vl = q := by rw [← hk]; abel
    rw [hpq']; exact hqB

/-! ## §3  The core: `LevelInterval B vl` from a top step and a bottom step -/

/-- A real vector killed by `rlevel vl` is a real multiple of `vl`. -/
theorem exists_real_smul_of_rlevel_zero {vl : ℤ × ℤ} (hvl : vl ≠ 0) {p : ℝ × ℝ}
    (h : rlevel vl p = 0) : ∃ σ : ℝ, p = σ • toReal vl := by
  simp only [rlevel] at h
  rcases eq_or_ne vl.1 0 with h1 | h1
  · have h2 : vl.2 ≠ 0 := fun h2 => hvl (Prod.ext h1 h2)
    have h2R : ((vl.2 : ℤ) : ℝ) ≠ 0 := Int.cast_ne_zero.mpr h2
    have hp1 : p.1 = 0 := by
      rw [h1] at h
      simp only [Int.cast_zero, zero_mul, zero_sub, neg_eq_zero] at h
      exact (mul_eq_zero.mp h).resolve_left h2R
    refine ⟨p.2 / ((vl.2 : ℤ) : ℝ), ?_⟩
    rw [Prod.ext_iff]
    refine ⟨?_, ?_⟩
    · simp only [toReal, Prod.smul_fst, smul_eq_mul, h1, Int.cast_zero, mul_zero, hp1]
    · simp only [toReal, Prod.smul_snd, smul_eq_mul]
      field_simp
  · have h1R : ((vl.1 : ℤ) : ℝ) ≠ 0 := Int.cast_ne_zero.mpr h1
    refine ⟨p.1 / ((vl.1 : ℤ) : ℝ), ?_⟩
    rw [Prod.ext_iff]
    refine ⟨?_, ?_⟩
    · simp only [toReal, Prod.smul_fst, smul_eq_mul]
      field_simp
    · simp only [toReal, Prod.smul_snd, smul_eq_mul]
      rw [div_mul_eq_mul_div, eq_div_iff h1R]
      linear_combination h

/-- **The core interpolation.**  If a lattice-convex set carries a full unit `w`-step at some
level `≤ m` and another at some level `≥ m`, then level `m` is occupied.

原文：b3_colle2.txt:806-808.  Geometrically: the real witness `C` contains two parallel unit
segments, one at level `det w e` and one at level `det w c`; their convex hull has slice
length `1` at every intermediate level, and a real interval of length `1` contains an integer.

This is the reusable form — it asks for *two unit steps straddling `m`*, not for extremal
levels, so it also applies to the unbounded tower layers (see
`levelInterval_of_unit_steps_cofinal`). -/
theorem exists_mem_det_eq_of_unit_steps {K : Set (ℤ × ℤ)} {w e c : ℤ × ℤ} {m : ℤ}
    (hK : IsLatticeConvexRegion K) (hw : Primitive w)
    (heK : e ∈ K) (hes : e + w ∈ K) (hcK : c ∈ K) (hcs : c + w ∈ K)
    (hlow : det w e ≤ m) (hhigh : m ≤ det w c) :
    ∃ z ∈ K, det w z = m := by
  obtain ⟨C, hCconv, _, hBeq⟩ := hK
  have hmem : ∀ z : ℤ × ℤ, z ∈ K ↔ toReal z ∈ C := by
    intro z; rw [hBeq]; exact Iff.rfl
  rcases eq_or_lt_of_le (le_trans hlow hhigh) with hEq | hLt
  · exact ⟨e, heK, by omega⟩
  -- The nondegenerate case.  Interpolate between the lower and the upper unit step.
  have hMμ : (0 : ℝ) < ((det w c : ℤ) : ℝ) - ((det w e : ℤ) : ℝ) := by
    have hcast : ((det w e : ℤ) : ℝ) < ((det w c : ℤ) : ℝ) := by exact_mod_cast hLt
    linarith
  have hMμne : (((det w c : ℤ) : ℝ) - ((det w e : ℤ) : ℝ)) ≠ 0 := ne_of_gt hMμ
  set t : ℝ := ((m : ℝ) - ((det w e : ℤ) : ℝ)) /
      (((det w c : ℤ) : ℝ) - ((det w e : ℤ) : ℝ)) with ht
  have ht0 : (0 : ℝ) ≤ t := by
    have hnum : (0 : ℝ) ≤ (m : ℝ) - ((det w e : ℤ) : ℝ) := by
      have : ((det w e : ℤ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hlow
      linarith
    rw [ht]
    exact div_nonneg hnum (le_of_lt hMμ)
  have ht1 : t ≤ 1 := by
    rw [ht, div_le_one hMμ]
    have : (m : ℝ) ≤ ((det w c : ℤ) : ℝ) := by exact_mod_cast hhigh
    linarith
  set x : ℝ × ℝ := (1 - t) • toReal e + t • toReal c with hx
  have hxC : x ∈ C :=
    hCconv ((hmem e).mp heK) ((hmem c).mp hcK) (by linarith) ht0 (by ring)
  have hyC : x + toReal w ∈ C := by
    have hy : (1 - t) • toReal (e + w) + t • toReal (c + w) = x + toReal w := by
      rw [toReal_add', toReal_add', hx]; module
    rw [← hy]
    exact hCconv ((hmem _).mp hes) ((hmem _).mp hcs) (by linarith) ht0 (by ring)
  have hlevx : rlevel w x = (m : ℝ) := by
    have hlin := isLinearMap_rlevel w
    rw [hx, hlin.map_add, hlin.map_smul, hlin.map_smul, rlevel_toReal, rlevel_toReal]
    simp only [smul_eq_mul]
    have hkey : t * (((det w c : ℤ) : ℝ) - ((det w e : ℤ) : ℝ))
        = (m : ℝ) - ((det w e : ℤ) : ℝ) := by
      rw [ht]; field_simp
    rw [show (1 - t) * ((det w e : ℤ) : ℝ) + t * ((det w c : ℤ) : ℝ)
        = ((det w e : ℤ) : ℝ) + t * (((det w c : ℤ) : ℝ) - ((det w e : ℤ) : ℝ)) from by
      ring, hkey]
    ring
  -- Put a lattice point of level `m` onto the unit segment `[x, x + toReal w]`.
  obtain ⟨z₀, hz₀⟩ := exists_det_eq hw m
  have hz₀lev : rlevel w (toReal z₀) = (m : ℝ) := by rw [rlevel_toReal, hz₀]
  have hdiff : rlevel w (x - toReal z₀) = 0 := by
    have hlin := isLinearMap_rlevel w
    have hsub : x - toReal z₀ = x + (-1 : ℝ) • toReal z₀ := by rw [neg_one_smul]; abel
    rw [hsub, hlin.map_add, hlin.map_smul, hlevx, hz₀lev]
    simp only [smul_eq_mul]
    ring
  obtain ⟨σ, hσ⟩ := exists_real_smul_of_rlevel_zero hw.ne_zero hdiff
  refine ⟨z₀ + ⌈σ⌉ • w, ?_, by rw [det_add_zsmul_self]; exact hz₀⟩
  rw [hmem]
  have hθ0 : (0 : ℝ) ≤ ((⌈σ⌉ : ℤ) : ℝ) - σ := by linarith [Int.le_ceil σ]
  have hθ1 : ((⌈σ⌉ : ℤ) : ℝ) - σ ≤ 1 := by linarith [Int.ceil_lt_add_one σ]
  have hz : toReal z₀ = x - σ • toReal w := by rw [← hσ]; abel
  have hpt : toReal (z₀ + ⌈σ⌉ • w)
      = (1 - (((⌈σ⌉ : ℤ) : ℝ) - σ)) • x + (((⌈σ⌉ : ℤ) : ℝ) - σ) • (x + toReal w) := by
    rw [toReal_add', toReal_zsmul', hz]; module
  rw [hpt]
  exact hCconv hxC hyC (by linarith) hθ0 (by ring)

/-- **The engine, bounded form.**  A lattice-convex `B` whose `det vl`-maximal and
`det vl`-minimal levels each carry a full unit `vl`-step has *every* intermediate level
occupied.  原文：b3_colle2.txt:806-808. -/
theorem levelInterval_of_unit_steps {B : Set (ℤ × ℤ)} {vl : ℤ × ℤ}
    (hB : IsLatticeConvexRegion B) (hvl : Primitive vl)
    (hmax : ∃ c ∈ B, (∀ z ∈ B, det vl z ≤ det vl c) ∧ c + vl ∈ B)
    (hmin : ∃ e ∈ B, (∀ z ∈ B, det vl e ≤ det vl z) ∧ e + vl ∈ B) :
    LevelInterval B vl := by
  obtain ⟨c, hcB, hcmax, hcs⟩ := hmax
  obtain ⟨e, heB, hemin, hes⟩ := hmin
  intro a ha b hb m hma hmb
  exact exists_mem_det_eq_of_unit_steps hB hvl heB hes hcB hcs
    (le_trans (hemin a ha) hma) (le_trans hmb (hcmax b hb))

/-- **The engine, unbounded form** — for `lane-tower-hbase`'s induction step.  A tower layer is
unbounded in the `det w`-direction (both `vl` and `u'` raise `det w`, by
`TowerHBaseMin.det_wtower_vl_mul_u'_pos`), so it has no maximal level; what replaces `hmax` is
a *cofinal supply of unit steps*.  The minimal level still needs a genuine unit step, and that
is the part only the seed `B` can pay for. -/
theorem levelInterval_of_unit_steps_cofinal {K : Set (ℤ × ℤ)} {w : ℤ × ℤ}
    (hK : IsLatticeConvexRegion K) (hw : Primitive w)
    (hmin : ∃ e ∈ K, (∀ z ∈ K, det w e ≤ det w z) ∧ e + w ∈ K)
    (hcof : ∀ M : ℤ, ∃ c ∈ K, M ≤ det w c ∧ c + w ∈ K) :
    LevelInterval K w := by
  obtain ⟨e, heK, hemin, hes⟩ := hmin
  intro a ha _b _hb m hma _hmb
  obtain ⟨c, hcK, hcm, hcs⟩ := hcof m
  exact exists_mem_det_eq_of_unit_steps hK hw heK hes hcK hcs (le_trans (hemin a ha) hma) hcm

/-! ## §4  The bridge: `±n ∈ E B` with `n ⟂ vl` gives both unit steps -/

/-- With `n ⟂ vl`, both primitive, `dot n` and `det vl` agree up to a global sign.  This is
what lets a single pair of antipodal edge normals control both ends of the `det vl` range. -/
theorem exists_sign_dot_eq_det {n vl : ℤ × ℤ} (hprim : Prim n) (hvl : Primitive vl)
    (hperp : dot n vl = 0) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ z : ℤ × ℤ, dot n z = ε * det vl z := by
  have hpvl : Primitive ((vl.2, -vl.1) : ℤ × ℤ) := (isCoprime_comm.mp hvl).neg_right
  have hdet : det ((vl.2, -vl.1) : ℤ × ℤ) n = 0 := by
    simp only [det, dot] at hperp ⊢
    linear_combination hperp
  obtain ⟨d, hd⟩ := Nivat.eq_zsmul_of_det_eq_zero hpvl hdet
  have hn1 : n.1 = d * vl.2 := by rw [hd]; simp
  have hn2 : n.2 = d * -vl.1 := by rw [hd]; simp
  have hd1 : d = 1 ∨ d = -1 := by
    have hcop : IsCoprime n.1 n.2 := Int.isCoprime_iff_gcd_eq_one.mpr hprim
    exact Int.isUnit_iff.mp (hcop.isUnit_of_dvd' ⟨vl.2, hn1⟩ ⟨-vl.1, hn2⟩)
  refine ⟨-d, ?_, ?_⟩
  · rcases hd1 with h | h
    · right; omega
    · left; omega
  · intro z
    simp only [dot, det, hn1, hn2]
    ring

/-- **The `B`-side input.**  Two antipodal edge normals perpendicular to `vl`, each with a
nontrivial face, make *both* extremal `det vl`-levels of `B` carry a full unit `vl`-step.

原文：b3_colle2.txt:806-808, via `TowerConstruct.genPerp'_mem_E_B` at `j := i` (`hdoth`).

This is the primary form: it asks only for the two faces to be `Nontrivial`, which is exactly
what `LaneTowerPkgEnvSymm.face_nontrivial_neg_of_envOf` (`EnvNegSymm.lean:85`) produces from
`henv` and a single `n ∈ E B` — no need to re-derive `-n ∈ E B`.

The `vl` slot is any primitive vector parallel to the two edges — in the induction step it is
instantiated at the *sweep direction* `w = wgen d nℓ j`, which is parallel to the generator
`d.h j`, not at `vl`. -/
theorem exists_det_extreme_unit_steps_of_faces {B : Set (ℤ × ℤ)} {n vl : ℤ × ℤ}
    (hB : IsLatticeConvexRegion B) (hvl : Primitive vl) (hprim : Prim n)
    (hperp : dot n vl = 0) (hface : (face B n).Nontrivial)
    (hfaceneg : (face B (-n)).Nontrivial) :
    (∃ c ∈ B, (∀ z ∈ B, det vl z ≤ det vl c) ∧ c + vl ∈ B) ∧
    (∃ e ∈ B, (∀ z ∈ B, det vl e ≤ det vl z) ∧ e + vl ∈ B) := by
  have hprimneg : Prim (-n) := hprim.neg
  have hperpneg : dot (-n) vl = 0 := by simp [dot_neg_left, hperp]
  obtain ⟨cp, hcpB, hcpmax, hcps⟩ := exists_unit_step_of_face hB hvl hprim hperp hface
  obtain ⟨cn, hcnB, hcnmax, hcns⟩ := exists_unit_step_of_face hB hvl hprimneg hperpneg hfaceneg
  obtain ⟨ε, hε, hεz⟩ := exists_sign_dot_eq_det hprim hvl hperp
  have hcnmax' : ∀ z ∈ B, dot n cn ≤ dot n z := by
    intro z hz
    have hzz := hcnmax z hz
    rw [dot_neg_left, dot_neg_left] at hzz
    omega
  have hcpdet : ∀ z ∈ B, ε * det vl z ≤ ε * det vl cp := by
    intro z hz
    have hzz := hcpmax z hz
    rwa [hεz z, hεz cp] at hzz
  have hcndet : ∀ z ∈ B, ε * det vl cn ≤ ε * det vl z := by
    intro z hz
    have hzz := hcnmax' z hz
    rwa [hεz z, hεz cn] at hzz
  rcases hε with rfl | rfl
  · exact ⟨⟨cp, hcpB, fun z hz => by have := hcpdet z hz; omega, hcps⟩,
      ⟨cn, hcnB, fun z hz => by have := hcndet z hz; omega, hcns⟩⟩
  · exact ⟨⟨cn, hcnB, fun z hz => by have := hcndet z hz; omega, hcns⟩,
      ⟨cp, hcpB, fun z hz => by have := hcpdet z hz; omega, hcps⟩⟩

/-- The `E B` phrasing of `exists_det_extreme_unit_steps_of_faces`: `IsEdge` bundles exactly the
`Nontrivial` face this needs (`LatticeEdges.lean:213`). -/
theorem exists_det_extreme_unit_steps {B : Set (ℤ × ℤ)} {n vl : ℤ × ℤ}
    (hB : IsLatticeConvexRegion B) (hvl : Primitive vl) (hprim : Prim n)
    (hperp : dot n vl = 0) (hpos : n ∈ E B) (hneg : -n ∈ E B) :
    (∃ c ∈ B, (∀ z ∈ B, det vl z ≤ det vl c) ∧ c + vl ∈ B) ∧
    (∃ e ∈ B, (∀ z ∈ B, det vl e ≤ det vl z) ∧ e + vl ∈ B) :=
  exists_det_extreme_unit_steps_of_faces hB hvl hprim hperp hpos.2 hneg.2

/-- **The `B`-side input, packaged as `LevelInterval`** (face form). -/
theorem levelInterval_of_faces {B : Set (ℤ × ℤ)} {n vl : ℤ × ℤ}
    (hB : IsLatticeConvexRegion B) (hvl : Primitive vl) (hprim : Prim n)
    (hperp : dot n vl = 0) (hface : (face B n).Nontrivial)
    (hfaceneg : (face B (-n)).Nontrivial) :
    LevelInterval B vl :=
  levelInterval_of_unit_steps hB hvl
    (exists_det_extreme_unit_steps_of_faces hB hvl hprim hperp hface hfaceneg).1
    (exists_det_extreme_unit_steps_of_faces hB hvl hprim hperp hface hfaceneg).2

/-- **The `B`-side input, packaged as `LevelInterval`.** -/
theorem levelInterval_of_edges {B : Set (ℤ × ℤ)} {n vl : ℤ × ℤ}
    (hB : IsLatticeConvexRegion B) (hvl : Primitive vl) (hprim : Prim n)
    (hperp : dot n vl = 0) (hpos : n ∈ E B) (hneg : -n ∈ E B) :
    LevelInterval B vl :=
  levelInterval_of_faces hB hvl hprim hperp hpos.2 hneg.2

/-! ## §5  `n = 0` of `hconv`: the cone seed is lattice-convex -/

/-- `det u' vl = ±1` already forces `u'` primitive, so `hunimod` carries its own `Primitive u'`. -/
theorem primitive_of_det_eq_pm_one {u' vl : ℤ × ℤ}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) : Primitive u' := by
  rcases hunimod with h | h
  · exact ⟨vl.2, -vl.1, by simp only [det] at h; linear_combination h⟩
  · exact ⟨-vl.2, vl.1, by simp only [det] at h; linear_combination -h⟩

/-- `sweep C w` is closed under `+ w`. -/
theorem add_mem_sweep_self {C : Set (ℤ × ℤ)} {w : ℤ × ℤ} :
    ∀ g ∈ sweep C w, g + w ∈ sweep C w := by
  rintro g ⟨b, hb, s, rfl⟩
  refine ⟨b, hb, s + 1, ?_⟩
  push_cast
  rw [add_smul, one_smul]
  abel

/-- **`hconv` at `n = 0`.**  原文：b3_colle2.txt:780（种子 `𝓡_I = coneRegion B vl u'`）.

The hypotheses are exactly what `lane-towerpkg`'s binder list supplies once `hdoth` is used:
`hpos`/`hneg` are `TowerConstruct.genPerp'_mem_E_B d henv i` at `n := genPerp' (d.h i)`, and
`hperp` is `hdoth` after `h_i_eq_zsmul_vl` rewrites `d.h i = c • vl`.  `hpos`/`hneg` can equally
be fed by the shorter route `Enveloped.E_eq` (`LatticeEdges.lean:1657`) +
`Colle35.Sphi_negSymm` (`DecompData.lean:417`), which needs no `hdoth`; `hperp` still does.

⚠ **Note which binders are *absent*.**  `hBfin`, `hBne`, `hadj` and `hnu` are not used — lattice
convexity of the cone seed feeds on nothing but the two `vl`-parallel edges of `B`.  This is a
statement about the proof, not an accident: it leaves `hadj` entirely free for the `n ≥ 1`
induction step (`lane-tower-hbase`), which is where the angular ordering of `sortedCand` has to
be paid for. -/
theorem isLatticeConvexRegion_coneRegion_of_faces {B : Set (ℤ × ℤ)} {n vl u' : ℤ × ℤ}
    (hB : IsLatticeConvexRegion B) (hvl : Primitive vl) (hprim : Prim n)
    (hperp : dot n vl = 0) (hface : (face B n).Nontrivial)
    (hfaceneg : (face B (-n)).Nontrivial)
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) :
    IsLatticeConvexRegion (Nivat.ConeRegion.coneRegion B vl u') := by
  have hlev : LevelInterval B vl := levelInterval_of_faces hB hvl hprim hperp hface hfaceneg
  have h1 : IsLatticeConvexRegion (sweep B vl) := isLatticeConvexRegion_sweep hB hvl hlev
  have hstep : ∀ g ∈ sweep B vl, g + vl ∈ sweep B vl := add_mem_sweep_self
  have hlev2 : LevelInterval (sweep B vl) u' := by
    rcases hunimod with h | h
    · exact Nivat.LaneTowerHlev.levelInterval_of_step_det_one hstep h
    · exact Nivat.LaneTowerHlev.levelInterval_of_step_det_neg_one hstep h
  show IsLatticeConvexRegion (sweep (sweep B vl) u')
  exact isLatticeConvexRegion_sweep h1 (primitive_of_det_eq_pm_one hunimod) hlev2

/-- The `E B` phrasing of `isLatticeConvexRegion_coneRegion_of_faces`. -/
theorem isLatticeConvexRegion_coneRegion {B : Set (ℤ × ℤ)} {n vl u' : ℤ × ℤ}
    (hB : IsLatticeConvexRegion B) (hvl : Primitive vl) (hprim : Prim n)
    (hperp : dot n vl = 0) (hpos : n ∈ E B) (hneg : -n ∈ E B)
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) :
    IsLatticeConvexRegion (Nivat.ConeRegion.coneRegion B vl u') :=
  isLatticeConvexRegion_coneRegion_of_faces hB hvl hprim hperp hpos.2 hneg.2 hunimod

/-- The same statement in `tower` vocabulary (face form): literally the `n = 0` instance of
`lane-towerpkg`'s `hconv` binder.  Feed `hface`/`hfaceneg` with
`LaneTowerPkgEnvSymm.face_nontrivial_neg_of_envOf` (`EnvNegSymm.lean:85`). -/
theorem tower_zero_latticeConvex_of_faces {B : Set (ℤ × ℤ)} {n vl u' : ℤ × ℤ} {w : ℕ → ℤ × ℤ}
    (hB : IsLatticeConvexRegion B) (hvl : Primitive vl) (hprim : Prim n)
    (hperp : dot n vl = 0) (hface : (face B n).Nontrivial)
    (hfaceneg : (face B (-n)).Nontrivial)
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) :
    IsLatticeConvexRegion (tower (Nivat.ConeRegion.coneRegion B vl u') w 0) := by
  have h := isLatticeConvexRegion_coneRegion_of_faces hB hvl hprim hperp hface hfaceneg hunimod
  simpa [tower] using h

/-- The same statement in `tower` vocabulary: literally the `n = 0` instance of
`lane-towerpkg`'s `hconv` binder. -/
theorem tower_zero_latticeConvex {B : Set (ℤ × ℤ)} {n vl u' : ℤ × ℤ} {w : ℕ → ℤ × ℤ}
    (hB : IsLatticeConvexRegion B) (hvl : Primitive vl) (hprim : Prim n)
    (hperp : dot n vl = 0) (hpos : n ∈ E B) (hneg : -n ∈ E B)
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) :
    IsLatticeConvexRegion (tower (Nivat.ConeRegion.coneRegion B vl u') w 0) :=
  tower_zero_latticeConvex_of_faces hB hvl hprim hperp hpos.2 hneg.2 hunimod

/-! ## §6  The unbounded layers: cofinal unit steps come for free inside a cone

This section is for `lane-tower-hbase`'s induction step.  A tower layer `K = tower … n` is
closed under `+vl` and `+u'` (`ColleReg.tower_add_vl_mem` / `tower_add_u'_mem`), and the next
sweep direction is `w = p•vl + q•u'` with `p < 0 < q`
(`TowerHBaseMin.det_wtower_vl_mul_u'_pos`).  Then `-p ≥ 1`, so for **any** `y ∈ K`

```
z := y + (-p)•vl ∈ K    and    z + w = y + q•u' ∈ K
```

is a full unit `w`-step, at a level that runs off to `+∞` as `y` runs along `vl`.  So the
*upper* half of `levelInterval_of_unit_steps_cofinal` is free; the whole content of the
induction step is the **single unit `w`-step at the minimal level**, and that is what the seed
`B` pays for (via §2 and `genPerp' (d.h j) ∈ E B`: `w` is parallel to the generator `d.h j`,
so `B` has an edge parallel to `w` on each side). -/

/-- `det w` against a `ℤ`-multiple in the right argument. -/
theorem det_add_zsmul (w a b : ℤ × ℤ) (c : ℤ) : det w (a + c • b) = det w a + c * det w b := by
  simp only [det, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- Iterating a `+v` closure. -/
theorem add_nsmul_mem {K : Set (ℤ × ℤ)} {v : ℤ × ℤ} (hc : ∀ z ∈ K, z + v ∈ K) :
    ∀ (j : ℕ) {z : ℤ × ℤ}, z ∈ K → z + (j : ℤ) • v ∈ K := by
  intro j
  induction j with
  | zero => intro z hz; simpa using hz
  | succ j ih =>
      intro z hz
      have hmem := hc _ (ih hz)
      have heq : z + (j : ℤ) • v + v = z + ((j + 1 : ℕ) : ℤ) • v := by
        push_cast
        rw [add_smul, one_smul]
        abel
      rwa [heq] at hmem

/-- **The induction-step engine.**  For a lattice-convex set closed under `+vl` and `+u'`, with
`w = p•vl + q•u'`, `p < 0 < q` and `det w vl > 0`, a unit `w`-step at the minimal `det w`-level
is *all* that is needed for `LevelInterval K w` — hence, via
`isLatticeConvexRegion_sweep` (`RegionSweep.lean:213`), for lattice convexity of the next layer.

原文：b3_colle2.txt:806-808. -/
theorem levelInterval_of_cone_closure {K : Set (ℤ × ℤ)} {vl u' w : ℤ × ℤ} {p q : ℤ}
    (hK : IsLatticeConvexRegion K) (hw : Primitive w)
    (hvlc : ∀ z ∈ K, z + vl ∈ K) (hu'c : ∀ z ∈ K, z + u' ∈ K)
    (hwpq : w = p • vl + q • u') (hp : p < 0) (hq : 0 < q) (hD : 0 < det w vl)
    (hmin : ∃ e ∈ K, (∀ z ∈ K, det w e ≤ det w z) ∧ e + w ∈ K) :
    LevelInterval K w := by
  obtain ⟨e, heK, hemin, hes⟩ := hmin
  refine levelInterval_of_unit_steps_cofinal hK hw ⟨e, heK, hemin, hes⟩ ?_
  intro M
  set k : ℕ := (M - det w e).toNat with hkdef
  have hkge : M - det w e ≤ (k : ℤ) := Int.self_le_toNat _
  have hk0 : (0 : ℤ) ≤ (k : ℤ) := Int.natCast_nonneg k
  set j : ℕ := k + (-p).toNat with hjdef
  have hj : (j : ℤ) = (k : ℤ) - p := by
    rw [hjdef]
    push_cast
    rw [Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ -p)]
    ring
  have hzK : e + ((k : ℤ) - p) • vl ∈ K := by
    have := add_nsmul_mem hvlc j heK
    rwa [hj] at this
  refine ⟨e + ((k : ℤ) - p) • vl, hzK, ?_, ?_⟩
  · rw [det_add_zsmul]
    have hkp0 : (0 : ℤ) ≤ (k : ℤ) - p := by omega
    have hchain : (k : ℤ) - p ≤ ((k : ℤ) - p) * det w vl :=
      le_mul_of_one_le_right hkp0 (by omega)
    linarith
  · have hstep : e + ((k : ℤ) - p) • vl + w = e + (k : ℤ) • vl + (q : ℤ) • u' := by
      rw [hwpq]; module
    rw [hstep]
    have h1 : e + (k : ℤ) • vl ∈ K := add_nsmul_mem hvlc k heK
    have h2 := add_nsmul_mem hu'c q.toNat h1
    rwa [Int.toNat_of_nonneg (le_of_lt hq)] at h2

/-- **The seed pays for the minimal level.**  If every point of `K` is dominated in `det w` by
some seed point, then a `det w`-minimal unit `w`-step of the seed is already a `det w`-minimal
unit `w`-step of `K`.  Combined with `exists_det_extreme_unit_steps` (at `n := genPerp' (d.h j)`,
`vl := w`) this discharges the `hmin` of `levelInterval_of_cone_closure`. -/
theorem exists_min_unit_step_of_seed {K B : Set (ℤ × ℤ)} {w : ℤ × ℤ}
    (hsub : B ⊆ K) (hdom : ∀ z ∈ K, ∃ b ∈ B, det w b ≤ det w z)
    (hstep : ∃ c ∈ B, (∀ z ∈ B, det w c ≤ det w z) ∧ c + w ∈ B) :
    ∃ e ∈ K, (∀ z ∈ K, det w e ≤ det w z) ∧ e + w ∈ K := by
  obtain ⟨c, hcB, hcmin, hcs⟩ := hstep
  refine ⟨c, hsub hcB, ?_, hsub hcs⟩
  intro z hz
  obtain ⟨b, hbB, hbz⟩ := hdom z hz
  exact le_trans (hcmin b hbB) hbz

end Nivat.LaneTowerHlevConv

#print axioms Nivat.LaneTowerHlevConv.exists_unit_step_of_face
#print axioms Nivat.LaneTowerHlevConv.exists_mem_det_eq_of_unit_steps
#print axioms Nivat.LaneTowerHlevConv.levelInterval_of_unit_steps
#print axioms Nivat.LaneTowerHlevConv.levelInterval_of_unit_steps_cofinal
#print axioms Nivat.LaneTowerHlevConv.exists_sign_dot_eq_det
#print axioms Nivat.LaneTowerHlevConv.exists_det_extreme_unit_steps_of_faces
#print axioms Nivat.LaneTowerHlevConv.exists_det_extreme_unit_steps
#print axioms Nivat.LaneTowerHlevConv.levelInterval_of_faces
#print axioms Nivat.LaneTowerHlevConv.levelInterval_of_edges
#print axioms Nivat.LaneTowerHlevConv.isLatticeConvexRegion_coneRegion_of_faces
#print axioms Nivat.LaneTowerHlevConv.isLatticeConvexRegion_coneRegion
#print axioms Nivat.LaneTowerHlevConv.tower_zero_latticeConvex_of_faces
#print axioms Nivat.LaneTowerHlevConv.tower_zero_latticeConvex
#print axioms Nivat.LaneTowerHlevConv.levelInterval_of_cone_closure
#print axioms Nivat.LaneTowerHlevConv.exists_min_unit_step_of_seed
