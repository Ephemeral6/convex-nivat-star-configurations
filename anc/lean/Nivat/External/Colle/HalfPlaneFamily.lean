/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.L1Region

/-!
# `HalfPlaneFamily`: the `RegionFamily` producer on `Rinf := Set.univ`

Lane Rsweep's file (exclusive).  Consumer: lane L1B's slot in `exists_L1MaxBResidual`
(`RegionSteps.lean`), which needs an `F : L1Region.RegionFamily (T e ξ) u u' c`.

The family is Collé's `𝓡^n_I` (`b3_colle2.txt:806-816`) with the ambient region taken to be the
whole plane: `R n = halfPlaneGE m (lev₀ - n · ⟨m, u⟩)`, a stack of half-planes whose near
boundary recedes and whose far side is open in both ray directions.  It is
`L1Region.ofCut` (`L1Region.lean:240`) at `Rinf := Set.univ`; this file discharges every input
of `ofCut` except `base`, which is the only field with content and is **taken, not proved**.

## Two things the dispatch got wrong, measured here

1. **`grow` needs the level step to be `⟨m, u⟩`, not `1`.**  `cut_ssubset`'s `hgap` asks for a
   lattice point in every level window `[lev (n+1), lev n)`.  With unit steps that means every
   integer level is attained by `dot m`, which fails for `m = (2, 0)` — the odd levels are empty
   and `grow` fails at every other index.  What is free is a window of width `d := dot m u > 0`:
   it contains `dot m (q • u) = q · d` for `q = ⌊(lev₀ - n·d - 1)/d⌋` (`gap_univ_of_dot_pos`).
   So the step is `dot m u`, and **no hypothesis beyond `0 < dot m u` is needed**.  Unit steps
   are available under `Primitive m` (`ofHalfPlanesPrim`), where Bézout attains every level.
2. **`union_not` is free on `univ`, and `L1Region.lean:139`'s "genuine content" moved into
   `base`.**  `PeriodOn x univ h` unfolds to `∀ z, x (z + h) = x z`, i.e. `h ∈ Per x`
   (`periodOn_univ_iff`), so `union_not` is `c • u ∉ Per x`, which is `¬ IsPeriodic x` plus
   `c • u ≠ 0`.  Proposition 2.12 (`Interfaces.lean:45`) is not invoked: its job is
   half-plane → plane, and on `univ` there is no half-plane to lift from.  The content now sits
   entirely in `base : PeriodOn x (halfPlaneGE m lev₀) (c • u)` — a half-plane period in a
   direction **transverse** to the boundary (`0 < dot m u`), which is *not* the parallel-period
   shape Proposition 2.12 kills (`hwu : inner2 w (c • u) = 0`), so `base` and `union_not` are
   jointly satisfiable.  `witness` below exhibits that on `L1Region.wx`.
-/

set_option autoImplicit false

namespace Nivat.HalfPlaneFamily

open Nivat Nivat.Colle41 Nivat.LE2 Nivat.L1Region

/-! ## §1  `PeriodOn` on the whole plane is a global period -/

/-- `PeriodOn x univ h ↔ h ∈ Per x`: the overlap-only condition of Definition 2.11 has nothing
to exclude when `U = univ`. -/
theorem periodOn_univ_iff {A : Type*} {x : Config A} {h : ℤ × ℤ} :
    PeriodOn x Set.univ h ↔ h ∈ Per x := by
  rw [mem_Per_iff]
  constructor
  · intro hp
    funext z
    exact hp z (Set.mem_univ _) (Set.mem_univ _)
  · intro hT z _ _
    exact congrFun hT z

/-- **`union_not` for `Rinf := univ`**: a non-periodic configuration has no nonzero global
period. -/
theorem not_periodOn_univ_of_not_isPeriodic {A : Type*} {x : Config A} {h : ℤ × ℤ}
    (hnp : ¬ IsPeriodic x) (hh : h ≠ 0) : ¬ PeriodOn x Set.univ h :=
  fun hp => hnp ⟨h, periodOn_univ_iff.mp hp, hh⟩

/-- Slicing the whole plane is just the half-plane. -/
theorem cut_univ (m : ℤ × ℤ) (lev : ℕ → ℤ) (n : ℕ) :
    cut Set.univ m lev n = halfPlaneGE m (lev n) :=
  Set.univ_inter _

/-! ## §2  The level sequence `lev₀, lev₀ - step, lev₀ - 2·step, …` -/

/-- Arithmetic levels with step `step`, descending from `lev₀`. -/
def lev (lev₀ step : ℤ) (n : ℕ) : ℤ := lev₀ - (n : ℤ) * step

@[simp] theorem lev_zero (lev₀ step : ℤ) : lev lev₀ step 0 = lev₀ := by
  simp [lev]

theorem lev_antitone {lev₀ step : ℤ} (hstep : 0 ≤ step) : Antitone (lev lev₀ step) := by
  intro a b hab
  simp only [lev]
  have hab' : (a : ℤ) ≤ b := by exact_mod_cast hab
  nlinarith

theorem lev_exhaustive {lev₀ step : ℤ} (hstep : 0 < step) (b : ℤ) :
    ∃ n, lev lev₀ step n ≤ b := by
  refine ⟨(lev₀ - b).toNat, ?_⟩
  simp only [lev]
  have h1 : lev₀ - b ≤ ((lev₀ - b).toNat : ℤ) := Int.self_le_toNat _
  have h2 : (0 : ℤ) ≤ ((lev₀ - b).toNat : ℤ) := by positivity
  have h3 : ((lev₀ - b).toNat : ℤ) * 1 ≤ ((lev₀ - b).toNat : ℤ) * step :=
    mul_le_mul_of_nonneg_left hstep h2
  linarith

/-! ## §3  The gap condition on `univ` -/

theorem dot_zsmul_right (m z : ℤ × ℤ) (k : ℤ) : dot m (k • z) = k * dot m z := by
  simp only [dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

/-- Every half-open window of width `d > 0` contains a multiple of `d`. -/
theorem exists_mul_mem_window {d : ℤ} (hd : 0 < d) (a : ℤ) :
    ∃ q : ℤ, a - d < q * d ∧ q * d ≤ a := by
  have h1 := Int.mul_ediv_add_emod a d
  have h2 := Int.emod_lt_of_pos a hd
  have h3 := Int.emod_nonneg a (ne_of_gt hd)
  exact ⟨a / d, by rw [mul_comm]; linarith, by rw [mul_comm]; linarith⟩

/-- **`cut_ssubset`'s `hgap` on `univ`, with step `dot m u`.**  The witness is a multiple of
`u` itself; nothing about `m` beyond `0 < dot m u` is used. -/
theorem gap_univ_of_dot_pos {m u : ℤ × ℤ} (hmu : 0 < dot m u) (lev₀ : ℤ) (n : ℕ) :
    ∃ z ∈ (Set.univ : Set (ℤ × ℤ)),
      lev lev₀ (dot m u) (n + 1) ≤ dot m z ∧ dot m z < lev lev₀ (dot m u) n := by
  obtain ⟨q, hq1, hq2⟩ := exists_mul_mem_window hmu (lev₀ - (n : ℤ) * dot m u - 1)
  refine ⟨q • u, Set.mem_univ _, ?_, ?_⟩
  · simp only [lev, dot_zsmul_right]
    push_cast
    linarith
  · simp only [lev, dot_zsmul_right]
    linarith

/-- Under `Primitive m` every integer is a value of `dot m` (Bézout). -/
theorem exists_dot_eq_of_primitive {m : ℤ × ℤ} (hm : Primitive m) (k : ℤ) :
    ∃ z : ℤ × ℤ, dot m z = k := by
  obtain ⟨a, b, hab⟩ := hm
  refine ⟨(k * a, k * b), ?_⟩
  simp only [dot]
  linear_combination k * hab

/-- `hgap` for unit steps, under `Primitive m`. -/
theorem gap_univ_of_primitive {m : ℤ × ℤ} (hm : Primitive m) (lev₀ : ℤ) (n : ℕ) :
    ∃ z ∈ (Set.univ : Set (ℤ × ℤ)),
      lev lev₀ 1 (n + 1) ≤ dot m z ∧ dot m z < lev lev₀ 1 n := by
  obtain ⟨z, hz⟩ := exists_dot_eq_of_primitive hm (lev₀ - (n : ℤ) - 1)
  refine ⟨z, Set.mem_univ _, ?_, ?_⟩
  · simp only [lev, hz]; push_cast; linarith
  · simp only [lev, hz]; linarith

/-! ## §4  The producer -/

/-- `u ≠ 0` whenever some functional is positive on it. -/
theorem ne_zero_of_dot_pos {m u : ℤ × ℤ} (hmu : 0 < dot m u) : u ≠ 0 := by
  rintro rfl
  simp [dot] at hmu

/-- **The `base` period is transverse to the cutting line.**  `dot m (c • u) = c · dot m u ≠ 0`,
so `c • u` is not parallel to the boundary of any slice.  This is the hypothesis Proposition
2.12 needs and does not get — see `base_not_parallel` for the real-normal form that
`union_not_of_halfPlane_cover` actually asks for. -/
theorem base_transverse {m u : ℤ × ℤ} {c : ℤ} (hmu : 0 < dot m u) (hc : c ≠ 0) :
    dot m (c • u) ≠ 0 := by
  rw [dot_zsmul_right]
  exact mul_ne_zero hc hmu.ne'

/-- **Proposition 2.12's `hwu` fails on this family.**  `union_not_of_halfPlane_cover`
(`L1Region.lean:529`) needs `inner2 w (c • u) = 0` for the real normal `w` of the covering
half-plane; with `w := (m.1, m.2)` that is `dot m (c • u) = 0`, which `base_transverse` denies.
So `base` cannot be lifted to a global period by that route, and the pair
`base` / `union_not` is not self-contradictory. -/
theorem base_not_parallel {m u : ℤ × ℤ} {c : ℤ} (hmu : 0 < dot m u) (hc : c ≠ 0) :
    inner2 ((m.1 : ℝ), (m.2 : ℝ)) (c • u) ≠ 0 := by
  have h : inner2 ((m.1 : ℝ), (m.2 : ℝ)) (c • u) = ((dot m (c • u) : ℤ) : ℝ) := by
    simp only [inner2, dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; push_cast; ring
  rw [h]
  exact_mod_cast base_transverse hmu hc

/-- **`RegionFamily` from a single half-plane period, generic configuration.**

`R n = halfPlaneGE m (lev₀ - n · dot m u)`.  Inputs: the cutting normal `m` runs along `u'`
and sees `u` positively (`ofCut`'s two geometric inputs, supplied by `L1Region.exists_cut_normal`
from `det u u' ≠ 0`), `c ≠ 0` (conjunct 9), non-periodicity, and **`base` on the level-`0`
half-plane** — the one input with content.

**Why `union_not` costs nothing here.**  The union of the slices is the whole plane
(`iUnion_cut`), and on the whole plane Definition 2.11's overlap condition has nothing left to
exclude: `PeriodOn x univ h` says `x (z + h) = x z` for *every* `z`, which is `h ∈ Per x`
(`periodOn_univ_iff`).  So `union_not` is exactly "`c • u` is not a global period of `x`", and
`¬ IsPeriodic x` together with `c • u ≠ 0` gives it outright.  A family whose union is the whole
plane can therefore satisfy `union_not` — precisely when the configuration is not periodic —
and Proposition 2.12 is never invoked.

**Where the content went, and why the construction does not eat itself.**  All of it is in
`base`: a period `c • u` of `x` on the half-plane `halfPlaneGE m lev₀`.  Proposition 2.12
(`Interfaces.lean:45`, `union_not_of_halfPlane_cover`) would turn a half-plane period into a
global one — contradicting `union_not` — but only for a period **parallel** to the boundary
(`hwu : inner2 w (c • u) = 0`).  Here `dot m (c • u) = c · dot m u ≠ 0` (`base_transverse`):
the period crosses the boundary, Proposition 2.12's hypothesis fails, and `base` and `union_not`
are jointly satisfiable — `witness` below exhibits both at once. -/
def ofHalfPlanesGen {x : Config ℤ} {u u' m : ℤ × ℤ} {c lev₀ : ℤ}
    (hmu' : dot m u' = 0) (hmu : 0 < dot m u) (hc : c ≠ 0) (hnp : ¬ IsPeriodic x)
    (hbase : PeriodOn x (halfPlaneGE m lev₀) (c • u)) :
    RegionFamily x u u' c :=
  ofCut (Rinf := Set.univ) (m := m) (lev := lev lev₀ (dot m u))
    (isRegion_univ u u') hmu' hmu (lev_antitone hmu.le) (lev_exhaustive hmu)
    (gap_univ_of_dot_pos hmu lev₀)
    (by rw [cut_univ, lev_zero]; exact hbase)
    (not_periodOn_univ_of_not_isPeriodic hnp
      (zsmul_ne_zero_of_ne_zero hc (ne_zero_of_dot_pos hmu)))

theorem ofHalfPlanesGen_R {x : Config ℤ} {u u' m : ℤ × ℤ} {c lev₀ : ℤ}
    (hmu' : dot m u' = 0) (hmu : 0 < dot m u) (hc : c ≠ 0) (hnp : ¬ IsPeriodic x)
    (hbase : PeriodOn x (halfPlaneGE m lev₀) (c • u)) (n : ℕ) :
    (ofHalfPlanesGen hmu' hmu hc hnp hbase).R n = halfPlaneGE m (lev₀ - (n : ℤ) * dot m u) :=
  cut_univ m _ n

/-- **L1B's slot**: the same at `x := T e ξ`, with non-periodicity taken on `ξ` itself
(`hξ.1.2.2.1` at the call site) and transported along `T e`. -/
def ofHalfPlanes {ξ : Config ℤ} {e u u' m : ℤ × ℤ} {c lev₀ : ℤ}
    (hmu' : dot m u' = 0) (hmu : 0 < dot m u) (hc : c ≠ 0) (hnp : ¬ IsPeriodic ξ)
    (hbase : PeriodOn (T e ξ) (halfPlaneGE m lev₀) (c • u)) :
    RegionFamily (T e ξ) u u' c :=
  ofHalfPlanesGen hmu' hmu hc (Nivat.CosetPigeonhole.not_isPeriodic_T_of_not_isPeriodic e hnp)
    hbase

/-- The members, explicitly: what `line0` / `base0` / `straddle` are to be stated against. -/
theorem ofHalfPlanes_R {ξ : Config ℤ} {e u u' m : ℤ × ℤ} {c lev₀ : ℤ}
    (hmu' : dot m u' = 0) (hmu : 0 < dot m u) (hc : c ≠ 0) (hnp : ¬ IsPeriodic ξ)
    (hbase : PeriodOn (T e ξ) (halfPlaneGE m lev₀) (c • u)) (n : ℕ) :
    (ofHalfPlanes hmu' hmu hc hnp hbase).R n = halfPlaneGE m (lev₀ - (n : ℤ) * dot m u) :=
  cut_univ m _ n

theorem ofHalfPlanes_R_zero {ξ : Config ℤ} {e u u' m : ℤ × ℤ} {c lev₀ : ℤ}
    (hmu' : dot m u' = 0) (hmu : 0 < dot m u) (hc : c ≠ 0) (hnp : ¬ IsPeriodic ξ)
    (hbase : PeriodOn (T e ξ) (halfPlaneGE m lev₀) (c • u)) :
    (ofHalfPlanes hmu' hmu hc hnp hbase).R 0 = halfPlaneGE m lev₀ := by
  rw [ofHalfPlanes_R]; simp

/-- Unit-step variant: `R n = halfPlaneGE m (lev₀ - n)`, which needs `Primitive m` so that
every level is attained (`grow` fails otherwise — see the module docstring). -/
def ofHalfPlanesPrim {ξ : Config ℤ} {e u u' m : ℤ × ℤ} {c lev₀ : ℤ}
    (hm : Primitive m) (hmu' : dot m u' = 0) (hmu : 0 < dot m u) (hc : c ≠ 0)
    (hnp : ¬ IsPeriodic ξ)
    (hbase : PeriodOn (T e ξ) (halfPlaneGE m lev₀) (c • u)) :
    RegionFamily (T e ξ) u u' c :=
  ofCut (Rinf := Set.univ) (m := m) (lev := lev lev₀ 1)
    (isRegion_univ u u') hmu' hmu (lev_antitone zero_le_one) (lev_exhaustive zero_lt_one)
    (gap_univ_of_primitive hm lev₀)
    (by rw [cut_univ, lev_zero]; exact hbase)
    (not_periodOn_univ_of_not_isPeriodic
      (Nivat.CosetPigeonhole.not_isPeriodic_T_of_not_isPeriodic e hnp)
      (zsmul_ne_zero_of_ne_zero hc (ne_zero_of_dot_pos hmu)))

theorem ofHalfPlanesPrim_R {ξ : Config ℤ} {e u u' m : ℤ × ℤ} {c lev₀ : ℤ}
    (hm : Primitive m) (hmu' : dot m u' = 0) (hmu : 0 < dot m u) (hc : c ≠ 0)
    (hnp : ¬ IsPeriodic ξ)
    (hbase : PeriodOn (T e ξ) (halfPlaneGE m lev₀) (c • u)) (n : ℕ) :
    (ofHalfPlanesPrim hm hmu' hmu hc hnp hbase).R n = halfPlaneGE m (lev₀ - n) := by
  rw [show (ofHalfPlanesPrim hm hmu' hmu hc hnp hbase).R n = cut Set.univ m (lev lev₀ 1) n
    from rfl, cut_univ]
  simp [lev]

/-! ## §5  Non-vacuity

`L1Region.lean` §4's configuration `wx` (indicator of `(-5, 0)`) is not periodic, and its
`(1, 0)`-periodicity on the half-plane `{0 ≤ z.1}` is `L1Region.wbase` read through
`cut_univ`.  So every hypothesis of `ofHalfPlanesGen` / `ofHalfPlanes` is satisfiable at once,
in particular `base` together with `union_not` — the pair the module docstring says is
jointly satisfiable. -/

theorem wx_not_isPeriodic : ¬ IsPeriodic wx := by
  rintro ⟨w, hw, hw0⟩
  have h := Per.apply hw ((-5 : ℤ), (0 : ℤ))
  have h1 : wx ((-5 : ℤ), (0 : ℤ)) = 1 := by simp [wx]
  rw [h1] at h
  by_cases hz : ((-5 : ℤ), (0 : ℤ)) + w = ((-5 : ℤ), (0 : ℤ))
  · exact hw0 (add_left_cancel (hz.trans (add_zero _).symm))
  · simp only [wx, if_neg hz] at h
    omega

theorem wbase' : PeriodOn wx (halfPlaneGE ((1 : ℤ), (0 : ℤ)) 0) ((1 : ℤ) • ((1 : ℤ), (0 : ℤ))) := by
  have h := wbase
  rw [cut_univ] at h
  simpa [wlev] using h

/-- **`ofHalfPlanesGen` is inhabited.** -/
def witness : RegionFamily wx ((1 : ℤ), (0 : ℤ)) ((0 : ℤ), (1 : ℤ)) 1 :=
  ofHalfPlanesGen (m := ((1 : ℤ), (0 : ℤ))) (lev₀ := 0)
    (by simp [dot]) (by simp [dot]) one_ne_zero wx_not_isPeriodic wbase'

/-- **`ofHalfPlanes` (the `T e ξ` signature) is inhabited**, at `e = 0`. -/
def witnessT : RegionFamily (T 0 wx) ((1 : ℤ), (0 : ℤ)) ((0 : ℤ), (1 : ℤ)) 1 :=
  ofHalfPlanes (m := ((1 : ℤ), (0 : ℤ))) (lev₀ := 0)
    (by simp [dot]) (by simp [dot]) one_ne_zero wx_not_isPeriodic (by rw [T_zero]; exact wbase')

/-- The witness selects an index: `exists_index` is not vacuous on this producer. -/
theorem witness_exists_index :
    ∃ R R' : Set (ℤ × ℤ),
      PeriodOn wx R ((1 : ℤ) • ((1 : ℤ), (0 : ℤ))) ∧
      Colle41.IsRegion R ((1 : ℤ), (0 : ℤ)) ((0 : ℤ), (1 : ℤ)) ∧
      R ⊂ R' ∧
      ¬ PeriodOn wx R' ((1 : ℤ) • ((1 : ℤ), (0 : ℤ))) :=
  witness.exists_index

/-! ## §6  Unit steps really do need `Primitive m`

The module docstring's item 1 is a claim about a construction that is *not* landed; here it is
in the kernel: with `m = (2, 0)` and unit steps the slices at levels `0` and `-1` coincide, so
`grow` is false at `n = 0`. -/

theorem cut_two_zero_lev_zero_eq_one :
    cut Set.univ ((2 : ℤ), (0 : ℤ)) (lev 0 1) 0 = cut Set.univ ((2 : ℤ), (0 : ℤ)) (lev 0 1) 1 := by
  ext z
  simp only [cut, halfPlaneGE, lev, dot, Set.mem_inter_iff, Set.mem_univ, true_and,
    Set.mem_ofPred_eq]
  omega

theorem not_grow_two_zero_unit :
    ¬ cut Set.univ ((2 : ℤ), (0 : ℤ)) (lev 0 1) 0 ⊂ cut Set.univ ((2 : ℤ), (0 : ℤ)) (lev 0 1) 1 := by
  rw [cut_two_zero_lev_zero_eq_one]
  exact lt_irrefl _

/-! ## §7  `base` at *some* index, not at index `0`

`RegionFamily.base` pins the periodic member at index `0`.  That is how the structure was
written, not what the source asks: `b3_colle2.txt:806` takes the **smallest** `I` with
`(T^u η)|𝓡_I` periodic, i.e. periodicity *somewhere* along the chain.  Since
`exists_greatest_periodOn` only ever uses `base` to seed a search, a family periodic at index
`k` can be re-indexed from `k` and every other field survives: `grow` and `isRegion` are
pointwise, and the union is unchanged because the family is monotone
(`iUnion_shift_eq`).  Stated for an arbitrary `R : ℕ → Set (ℤ × ℤ)` so that both producers in
the tree — this file's half-plane stacks and `L1RegionBuild.ofWedge` — can use it. -/

theorem monotone_of_grow {R : ℕ → Set (ℤ × ℤ)} (hgrow : ∀ n, R n ⊂ R (n + 1)) : Monotone R :=
  monotone_nat_of_le_succ fun n => (hgrow n).subset

/-- Dropping a monotone family's first `k` members does not change its union. -/
theorem iUnion_shift_eq {R : ℕ → Set (ℤ × ℤ)} (hmono : Monotone R) (k : ℕ) :
    (⋃ n, R (k + n)) = ⋃ n, R n := by
  apply Set.Subset.antisymm
  · exact Set.iUnion_subset fun n => Set.subset_iUnion R (k + n)
  · exact Set.iUnion_subset fun n =>
      (hmono (Nat.le_add_left n k)).trans (Set.subset_iUnion (fun n => R (k + n)) n)

/-- **A `RegionFamily` from periodicity at some index `k`.**  `R' n := R (k + n)`. -/
def ofSomeIndex {x : Config ℤ} {u u' : ℤ × ℤ} {c : ℤ} {R : ℕ → Set (ℤ × ℤ)} (k : ℕ)
    (hgrow : ∀ n, R n ⊂ R (n + 1)) (hreg : ∀ n, Colle41.IsRegion (R n) u u')
    (hk : PeriodOn x (R k) (c • u)) (hnot : ¬ PeriodOn x (⋃ n, R n) (c • u)) :
    RegionFamily x u u' c where
  R n := R (k + n)
  grow n := by rw [← Nat.add_assoc]; exact hgrow (k + n)
  isRegion n := hreg (k + n)
  base := by simpa using hk
  union_not := by rw [iUnion_shift_eq (monotone_of_grow hgrow) k]; exact hnot

theorem ofSomeIndex_R {x : Config ℤ} {u u' : ℤ × ℤ} {c : ℤ} {R : ℕ → Set (ℤ × ℤ)} (k : ℕ)
    (hgrow : ∀ n, R n ⊂ R (n + 1)) (hreg : ∀ n, Colle41.IsRegion (R n) u u')
    (hk : PeriodOn x (R k) (c • u)) (hnot : ¬ PeriodOn x (⋃ n, R n) (c • u)) (n : ℕ) :
    (ofSomeIndex k hgrow hreg hk hnot).R n = R (k + n) :=
  rfl

/-- The half-plane stack with `base` at an arbitrary index: `R n = halfPlaneGE m (lev₀ - (k+n)·dot m u)`. -/
def ofHalfPlanesGenAt {x : Config ℤ} {u u' m : ℤ × ℤ} {c lev₀ : ℤ}
    (hmu' : dot m u' = 0) (hmu : 0 < dot m u) (hc : c ≠ 0) (hnp : ¬ IsPeriodic x) (k : ℕ)
    (hk : PeriodOn x (halfPlaneGE m (lev₀ - (k : ℤ) * dot m u)) (c • u)) :
    RegionFamily x u u' c :=
  ofSomeIndex (R := cut Set.univ m (lev lev₀ (dot m u))) k
    (cut_ssubset (lev_antitone hmu.le) (gap_univ_of_dot_pos hmu lev₀))
    (isRegion_cut (isRegion_univ u u') hmu' hmu _)
    (by rw [cut_univ]; exact hk)
    (by
      rw [iUnion_cut (lev_exhaustive hmu)]
      exact not_periodOn_univ_of_not_isPeriodic hnp
        (zsmul_ne_zero_of_ne_zero hc (ne_zero_of_dot_pos hmu)))

theorem ofHalfPlanesGenAt_R {x : Config ℤ} {u u' m : ℤ × ℤ} {c lev₀ : ℤ}
    (hmu' : dot m u' = 0) (hmu : 0 < dot m u) (hc : c ≠ 0) (hnp : ¬ IsPeriodic x) (k : ℕ)
    (hk : PeriodOn x (halfPlaneGE m (lev₀ - (k : ℤ) * dot m u)) (c • u)) (n : ℕ) :
    (ofHalfPlanesGenAt hmu' hmu hc hnp k hk).R n
      = halfPlaneGE m (lev₀ - ((k + n : ℕ) : ℤ) * dot m u) :=
  cut_univ m _ (k + n)

/-- Non-vacuity of `ofSomeIndex` with `k ≠ 0`: the level-`0` half-plane `{0 ≤ z.1}` is
`(1,0)`-periodic for `wx` and so is the level-`-4` one (`L1Region.w_periodOn_of_le`); seed at
`k = 4`, where `base` in the original indexing would already be "four levels down". -/
def witnessAt : RegionFamily wx ((1 : ℤ), (0 : ℤ)) ((0 : ℤ), (1 : ℤ)) 1 :=
  ofSomeIndex (R := cut Set.univ ((1 : ℤ), (0 : ℤ)) wlev) 4
    (cut_ssubset wlev_antitone wgap)
    (isRegion_cut (isRegion_univ _ _) (by simp [dot]) (by simp [dot]) wlev)
    (w_periodOn_of_le (by norm_num))
    (by rw [iUnion_cut wlev_exhaustive]; exact wnot)

theorem witnessAt_R_zero :
    witnessAt.R 0 = cut Set.univ ((1 : ℤ), (0 : ℤ)) wlev 4 :=
  rfl

end Nivat.HalfPlaneFamily

section Receipts
/-! Standing `#print axioms` receipts.  Deletable as a block. -/

#print axioms Nivat.HalfPlaneFamily.periodOn_univ_iff
#print axioms Nivat.HalfPlaneFamily.not_periodOn_univ_of_not_isPeriodic
#print axioms Nivat.HalfPlaneFamily.cut_univ
#print axioms Nivat.HalfPlaneFamily.lev_antitone
#print axioms Nivat.HalfPlaneFamily.lev_exhaustive
#print axioms Nivat.HalfPlaneFamily.exists_mul_mem_window
#print axioms Nivat.HalfPlaneFamily.gap_univ_of_dot_pos
#print axioms Nivat.HalfPlaneFamily.exists_dot_eq_of_primitive
#print axioms Nivat.HalfPlaneFamily.gap_univ_of_primitive
#print axioms Nivat.HalfPlaneFamily.ofHalfPlanesGen
#print axioms Nivat.HalfPlaneFamily.ofHalfPlanesGen_R
#print axioms Nivat.HalfPlaneFamily.ofHalfPlanes
#print axioms Nivat.HalfPlaneFamily.ofHalfPlanes_R
#print axioms Nivat.HalfPlaneFamily.ofHalfPlanes_R_zero
#print axioms Nivat.HalfPlaneFamily.ofHalfPlanesPrim
#print axioms Nivat.HalfPlaneFamily.ofHalfPlanesPrim_R
#print axioms Nivat.HalfPlaneFamily.wx_not_isPeriodic
#print axioms Nivat.HalfPlaneFamily.witness
#print axioms Nivat.HalfPlaneFamily.witnessT
#print axioms Nivat.HalfPlaneFamily.witness_exists_index
#print axioms Nivat.HalfPlaneFamily.not_grow_two_zero_unit
#print axioms Nivat.HalfPlaneFamily.base_transverse
#print axioms Nivat.HalfPlaneFamily.base_not_parallel
#print axioms Nivat.HalfPlaneFamily.iUnion_shift_eq
#print axioms Nivat.HalfPlaneFamily.ofSomeIndex
#print axioms Nivat.HalfPlaneFamily.ofSomeIndex_R
#print axioms Nivat.HalfPlaneFamily.ofHalfPlanesGenAt
#print axioms Nivat.HalfPlaneFamily.ofHalfPlanesGenAt_R
#print axioms Nivat.HalfPlaneFamily.witnessAt
#print axioms Nivat.HalfPlaneFamily.witnessAt_R_zero

end Receipts
