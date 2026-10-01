/-
Copyright (c) 2026 Nivat Formalization Contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lane-tower-hbase
-/
import Nivat.External.Colle.CutRecConvex
import Nivat.External.Colle.L1Region
import Nivat.External.Colle.RegionSweep
import Nivat.External.Colle.TowerBuild
import Nivat.External.Colle.ConeRegion
import Nivat.External.Colle.TowerConstruct
import Nivat.External.Colle.TowerGenBridge

/-!
# `lane-tower-hbase`: the `b₀`-group of the tower package (`h0` + `hbase`)

Consumer: `RegionSteps.lean:1749-1759`, the tower `obtain` of
`exists_cutResidualR_of_claim46`, conjuncts

```
(∃ z ∈ Rinf, dot m z = b₀) ∧ …                                              -- h0
(∀ lev : ℕ → ℤ, lev 0 = b₀ →
   Colle41.PeriodOn (T e ξ) (L1Region.cut Rinf m lev 0) (c • vl))           -- hbase
```

## The mechanism (原文 `b3_colle2.txt:806-820`)

`:814` picks `I` as the **smallest** index with `(T^u η)|𝓡_I` periodic of period `h`; `:808`
builds `𝓡_{I-1} = {g + t v⃗_{ℓ_{I-1}} : g ∈ 𝓡_I, t ∈ ℤ₊}` — i.e. `Rinf = sweep C w'` with
`C := 𝓡_I` and `w' := v⃗_{ℓ_{I-1}}`.  `:816-818` sets `ℓ' := ℓ_I`, `d₀ = 0`, so `𝓡⁰_I = 𝓡_I`:
in the Lean model the level-0 cut is `Rinf ∩ halfPlaneGE m b₀` with `b₀` the `m`-height of
`𝓡_I`'s own support line `ℓ'_{𝓡_I}`, and the content of `𝓡⁰_I = 𝓡_I` is exactly
`cut Rinf m lev 0 = C`.  Then `hbase` is `PeriodOn … C (c • vl)`, which is `:814`'s defining
property of `I` — **not** a geometric fact, and `h0` is free once `b₀ := dot m b₀pt`.

So the whole `b₀`-group reduces to one set identity, `cut (sweep C w') m lev 0 = C`, and that
identity is precisely what `ColleReg.hrec_of_convex` (`CutRecConvex.lean:55`) was built for.

## Why the `hmax` route is dead, and what replaces it

`TowerHBase.hbase_of_prev_level_periodOn` (`TowerHBase.lean:69`) asked for
`hmax : ∀ z ∈ C, dot m z ≤ b₀`, refuted on tower levels by
`LaneTowerPkg.not_bddAbove_dot_of_vl_closed`
(`tmp/wip/lane-towerpkg-interior-hbase-obstruction.lean:43`): a tower level contains
`z₀ + ℕ • vl` and the target's own `hmvl` says `0 < dot m vl`.

**The sign was upside down.**  `b₀` is the `m`-**minimum** of `C`, not its maximum: `m` is the
inward normal of `ℓ'_{𝓡_I}` (`:816`), `𝓡_I` lies on its positive side, and `𝓡_{I-1}` extends
`𝓡_I` **downwards** (`dot m w' < 0`) — which is also what the target's own
`hunb : ∀ b, ∃ z ∈ Rinf, dot m z < b` (`RegionSteps.lean:1755`) says.  With `hmax` replaced by
`hlow : ∀ z ∈ C, b₀ ≤ dot m z` the `t = 0` forcing argument of
`sweep_inter_halfPlaneGE_eq_of_max` no longer applies (a high point of `C` can be pushed
several `w'`-steps and still stay above `b₀`) — and it should not: those points *are* in `C`.
Recovering them is genuine convexity, which is `hrec_of_convex`'s convex-combination argument.
No new hypothesis beyond `hrec_of_convex`'s own is introduced here.

## Contents

* §1 `exists_base` — the `b₀`-group for an arbitrary `K = sweep C w'`, from
  `hrec_of_convex`'s premise set about `C`.
* §2 `exists_base_tower` — the same at `C = tower (coneRegion B vl u') wt n`, with `hlow`,
  `hb₀` and `hprev` traded for **seed-level** extremality of one point `b₀pt` over `B` plus
  sign conditions on `vl`, `u'` and the swept directions.
* §3 `dot_nprevOf_wtower_self`, `dot_nprevOf_wtower_succ_pos` — two of those sign conditions
  discharged for `TowerConstruct.lean`'s own `nprevOf`/`wtower`.
* §4 `cut_step_subset`, `ray_mem_tower_extChain`, `cut_tower_step`, `hcut_tower` — the `⊆`
  half of `𝓡⁰_I = 𝓡_I` at a cut level that dominates the whole seed `B`, which is the shape
  `lane-towerpkg`'s `lane_towerpkg_reduce` actually consumes (it closes `hbase` by
  `PeriodOn.mono`, so it needs only `⊆`, but it needs it at a level it can *produce*).
* §5 `dot_expNormal_eq_det_mul`, `dot_expNormal_vl_pos`, `dot_m_vl_pos`,
  `exists_dot_lt_of_sweep` — the consumer's `hmvl` (`0 < dot m vl`) and `hunb`, in the same
  `m`, showing `OPEN.md #10 / #10b`'s suspected sign tension is not one.
* §6 `det_dot_cramer`, `det_wtower_vl_mul_u'_pos` — the fifth disjunct of `lane-tower-hlev`'s
  `hcase` is unreachable on this chain, so `hconv` does not follow from
  `isRegion_tower_of_steps`.
* §7 `cramer_smul_pair`, `expNormal_basis_expand`,
  `coneRegion_inter_halfPlaneGE_eq_quadrant` — the `I = 0` slice of the seed cone is
  *unconditionally* the unimodular quadrant at the seed's corner.
* §8 `exists_cone_decomp`, `mem_of_nsmul_step`, `mem_of_cone_of_residues` — the gap set
  between the `ℕ`-span of two directions and the lattice points of the cone they span is the
  half-open fundamental parallelogram, `det a b` points; a set closed under `+a`, `+b` that
  contains them contains the whole cone.  (Currently unused by §9/§10; kept as the fallback
  if the descent route breaks.)
* §9 `exists_mem_det_eq_of_descent`, `levelInterval_of_descent` — `LevelInterval` lifts from
  the seed `B` to the whole tower level, by pure arithmetic.
* §10 `isLatticeConvexRegion_tower_of_seed` — **`hconv` reduced to hypotheses about the seed
  only**, the last of which (`LevelInterval B (wt n)`) is `lane-tower-hlev`'s concavity
  argument instantiated at the chain direction instead of at `vl`.
* §11 `det_vl_cramer_nl`, `det_wtower_vl_neg`/`_pos`, `det_wtower_prev_neg`/`_pos` — the sign
  of `det (wt n) vl` is pinned by the unit `det u' vl`, so both orientations are covered.
* §12 `isLatticeConvexRegion_tower_wtower` (and `_pos`) — §10 instantiated at the actual
  chain `wtower d nℓ vl u' i`.  **Every arithmetic binder is discharged**; what is left is
  `hR₀` and `hlevB`, both `lane-tower-hlev`'s.  The tail `n ≥ length` (where
  `wtower_last = -vl`) needs neither, by `levelInterval_of_unit_step`.

⚠ **Status of `hconv` (lattice convexity of the tower levels), corrected.**  The `n = 0`
refutation circulated by `lane-tower-hlev` has been **withdrawn by its author**, and
independently re-checked by `lane-towerpkg`: its witness seed has a non-symmetric `E`, while
`henv` forces `E B = E ↑d.Sphi` (`Enveloped.E_eq`, `LatticeEdges.lean:1657`) and the latter is
closed under negation (`Colle35.Sphi_negSymm`, `DecompData.lean:417`).  Likewise
`TowerLevelStep.sweep_cone_not_isLatticeConvexRegion` (`:375`) uses `B = {(0,0)}`, for which
`E B = ∅` — it refutes the *route* `isRegion_tower_of_steps` for a general step direction (and
§6 closes that route independently), **not** `hconv`.  So `hconv` is open, not false, and
`lane-tower-hlev` is proving it via `henv`.

Independently of that, §4 carries a primed layer `cut_step_subset_of_cut` /
`cut_tower_step_of_cut` / `hcut_tower_of_cut` whose convexity binder is only about the
**slice** `tower … n ∩ halfPlaneGE m β`, which is all the proof ever uses.  The unprimed
`cut_step_subset` / `cut_tower_step` / `hcut_tower` are the strong-binder corollaries, kept
because `lane-towerpkg` consumes `hcut_tower` verbatim.  The slice binder is *not* a way round
`hconv` for `I ≥ 1`: `TowerLevelStep`'s `w = (-2,3)` instance has its missing midpoint
`(-1,2)` at `dot m = 3` against a cut level `0`, i.e. inside the slice.  At `I = 0` the slice
binder does discharge itself — that is §7.

## Status

0 sorry.  `#print axioms`: `[propext, Classical.choice, Quot.sound]`.

§2 leaves to the tower producer: the seed extremality `hmB`/`hpB` (one point of `B`
simultaneously `dot m`-minimal and `dot nprev`-maximal — the shared vertex of two consecutive
edge normals, `HsuppTowerBase.faceStart_nprevOf_extremal`'s content) and the lattice convexity
`hC` of the tower level.

§3's `dot_nprevOf_wtower_succ_pos` needs `I + 2 ≤ (sortedCand d nℓ u' i).length`, which the
consumer cannot supply (`TowerIndex.exists_last_periodOn_finite` may return the last index).
§4 supersedes it: it needs only `I ≤ length`, the same bound `lane-towerpkg`'s
`dot_m_step_neg` carries.

§4 avoids the seed extremality entirely (the corner is just the `dot nℓ`-argmax of `B`, and
`nℓ` beats every building direction of the tower).  What it still needs from outside:
`hconv` (lattice convexity of the tower level, `lane-tower-hlev`) and `hstep`
(`dot m (wtower … I) < 0`, `lane-towerpkg`'s own `dot_m_step_neg`).
-/

set_option autoImplicit false

namespace Nivat.TowerHBaseMin

open Nivat Nivat.LE2 Nivat.RegionSweep Nivat.ConeRegion Nivat.ColleReg

variable {C : Set (ℤ × ℤ)} {m w w' nprev b₀pt : ℤ × ℤ} {b₀ : ℤ}

/-! ## §1  The `b₀`-group for an arbitrary one-step sweep -/

/-- **`𝓡⁰_I = 𝓡_I`** (`b3_colle2.txt:818`, `d₀ = 0`) for a single sweep step.

Cutting `sweep C w'` back at `C`'s own bottom `m`-level returns `C` exactly.  `⊇` is
`subset_sweep` plus `hlow`; `⊆` is `hrec_of_convex` (`CutRecConvex.lean:55`), whose hypotheses
are passed through verbatim:

* `hC` — `C` lattice convex;
* `hlow`/`hb₀` — `b₀` is `C`'s bottom `m`-level and `b₀pt` sits on it;
* `hwray`/`hmw` — the lattice `w`-ray out of `b₀pt` stays in `C` and stays on that level
  (`w = v⃗_{ℓ'}`, `:816`);
* `hneg` — the sweep direction strictly descends (`:808`, `w' = v⃗_{ℓ_{I-1}}`);
* `hprev`/`hpw`/`hpw'` — the other supporting normal at `b₀pt` puts `w` and `w'` on one side
  (`:766`, the cyclic order of edge normals). -/
theorem sweep_inter_halfPlaneGE_eq_of_min
    (hC : IsLatticeConvexRegion C)
    (hlow : ∀ z ∈ C, b₀ ≤ dot m z)
    (hb₀ : dot m b₀pt = b₀)
    (hwray : ∀ t : ℕ, b₀pt + t • w ∈ C)
    (hmw : dot m w = 0)
    (hneg : dot m w' < 0)
    (hprev : ∀ z ∈ C, dot nprev (z - b₀pt) ≤ 0)
    (hpw : dot nprev w < 0)
    (hpw' : dot nprev w' ≤ 0) :
    sweep C w' ∩ halfPlaneGE m b₀ = C := by
  apply Set.eq_of_subset_of_subset
  · rintro z ⟨⟨g, hg, t, rfl⟩, hz⟩
    have hcast : (t : ℤ) • w' = t • w' := natCast_zsmul w' t
    rw [hcast] at hz ⊢
    exact Nivat.ColleReg.hrec_of_convex hC hlow hb₀ hwray hmw hneg hprev hpw hpw' g hg t hz
  · exact fun z hz => ⟨subset_sweep C w' hz, hlow z hz⟩

/-- Restatement of `sweep_inter_halfPlaneGE_eq_of_min` in the consumer's `L1Region.cut`
vocabulary: for any level function starting at `b₀`, the level-0 slice of `Rinf = sweep C w'`
*is* `C`. -/
theorem cut_zero_eq
    (hC : IsLatticeConvexRegion C)
    (hlow : ∀ z ∈ C, b₀ ≤ dot m z)
    (hb₀ : dot m b₀pt = b₀)
    (hwray : ∀ t : ℕ, b₀pt + t • w ∈ C)
    (hmw : dot m w = 0)
    (hneg : dot m w' < 0)
    (hprev : ∀ z ∈ C, dot nprev (z - b₀pt) ≤ 0)
    (hpw : dot nprev w < 0)
    (hpw' : dot nprev w' ≤ 0)
    (lev : ℕ → ℤ) (hlev0 : lev 0 = b₀) :
    Nivat.L1Region.cut (sweep C w') m lev 0 = C := by
  show sweep C w' ∩ halfPlaneGE m (lev 0) = C
  rw [hlev0]
  exact sweep_inter_halfPlaneGE_eq_of_min hC hlow hb₀ hwray hmw hneg hprev hpw hpw'

/-- **The `b₀`-group of the tower package**, `RegionSteps.lean:1754` (`h0`) and
`:1756-1757` (`hbase`), in one shot and for an arbitrary region `K = sweep C w'`.

`b₀` is `C`'s bottom `m`-level; `h0` is witnessed by `b₀pt` itself (`C ⊆ sweep C w'`), and
`hbase` is `hper` transported along `cut_zero_eq`.  `hper` is `:814`'s choice of `I`; every
other hypothesis is about `C`'s shape only. -/
theorem exists_base {A : Type*} {ξ : Config A} {e vl : ℤ × ℤ} {c : ℤ} {K : Set (ℤ × ℤ)}
    (hK : K = sweep C w')
    (hC : IsLatticeConvexRegion C)
    (hlow : ∀ z ∈ C, b₀ ≤ dot m z)
    (hb₀ : dot m b₀pt = b₀)
    (hwray : ∀ t : ℕ, b₀pt + t • w ∈ C)
    (hmw : dot m w = 0)
    (hneg : dot m w' < 0)
    (hprev : ∀ z ∈ C, dot nprev (z - b₀pt) ≤ 0)
    (hpw : dot nprev w < 0)
    (hpw' : dot nprev w' ≤ 0)
    (hper : Nivat.Colle41.PeriodOn (T e ξ) C (c • vl)) :
    ∃ b : ℤ, (∃ z ∈ K, dot m z = b) ∧
      ∀ lev : ℕ → ℤ, lev 0 = b →
        Nivat.Colle41.PeriodOn (T e ξ) (Nivat.L1Region.cut K m lev 0) (c • vl) := by
  subst hK
  refine ⟨b₀, ⟨b₀pt, subset_sweep C w' (by simpa using hwray 0), hb₀⟩, ?_⟩
  intro lev hlev0
  rw [cut_zero_eq hC hlow hb₀ hwray hmw hneg hprev hpw hpw' lev hlev0]
  exact hper

/-! ## §2  The same, at a concrete tower level

Above, `hlow`/`hb₀`/`hprev` are global statements about `C`.  When
`C = tower (coneRegion B vl u') wt n` (原文 `:808` for the sweep iteration, `:780` for the
seed cone) they reduce to **seed-level** statements about `B` plus sign conditions on the
tower's own directions — the form `TowerConstruct.lean` already speaks.  The mechanism is the
one `HsuppTowerGeneral.dot_le_of_mem_tower_bounded` uses for `≤ top`, sharpened to an
*attained* bound: a normal that is non-positive on `vl`, on `u'` and on every swept direction
`wt k` (`k < n`) gains nothing by sweeping, so its maximum over the whole tower is already its
maximum over `B`. -/

/-- **A normal non-positive on every building direction is maximised on the seed.**

Sharpening of `HsuppTowerGeneral.dot_le_of_mem_tower_bounded` (which produces *some* `top`
from finiteness of `B`) to a bound supplied by the caller — what an *attained* support value
needs.  No finiteness of `B` is used. -/
theorem dot_le_of_mem_tower {B : Set (ℤ × ℤ)} {vl u' ν : ℤ × ℤ} {top : ℤ}
    (hνvl : dot ν vl ≤ 0) (hνu' : dot ν u' ≤ 0)
    (wt : ℕ → ℤ × ℤ) (n : ℕ) (hw : ∀ k, k < n → dot ν (wt k) ≤ 0)
    (hB : ∀ b ∈ B, dot ν b ≤ top) :
    ∀ z ∈ tower (coneRegion B vl u') wt n, dot ν z ≤ top := by
  induction n with
  | zero =>
    intro z hz
    simp only [tower] at hz
    rw [mem_coneRegion_iff] at hz
    obtain ⟨b, hb, s, t, rfl⟩ := hz
    rw [dot_add, dot_add, dot_smul_right, dot_smul_right]
    have hs : (0 : ℤ) ≤ (s : ℤ) := Int.natCast_nonneg s
    have ht : (0 : ℤ) ≤ (t : ℤ) := Int.natCast_nonneg t
    have h1 : (s : ℤ) * dot ν vl ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hs hνvl
    have h2 : (t : ℤ) * dot ν u' ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht hνu'
    have := hB b hb
    linarith
  | succ k ih =>
    intro z hz
    simp only [tower] at hz
    rw [mem_sweep] at hz
    obtain ⟨g, hg, t, rfl⟩ := hz
    have hgle := ih (fun j hj => hw j (by omega)) g hg
    rw [dot_add, dot_smul_right]
    have ht : (0 : ℤ) ≤ (t : ℤ) := Int.natCast_nonneg t
    have h1 : (t : ℤ) * dot ν (wt k) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos ht (hw k (by omega))
    linarith

/-- The mirror image: a normal **non-negative** on every building direction is minimised on
the seed.  This is `hrec_of_convex`'s `hlow` for a tower level. -/
theorem le_dot_of_mem_tower {B : Set (ℤ × ℤ)} {vl u' mm : ℤ × ℤ} {b : ℤ}
    (hmvl : 0 ≤ dot mm vl) (hmu' : 0 ≤ dot mm u')
    (wt : ℕ → ℤ × ℤ) (n : ℕ) (hw : ∀ k, k < n → 0 ≤ dot mm (wt k))
    (hB : ∀ p ∈ B, b ≤ dot mm p) :
    ∀ z ∈ tower (coneRegion B vl u') wt n, b ≤ dot mm z := by
  intro z hz
  have h := dot_le_of_mem_tower (ν := -mm) (top := -b)
    (by rw [dot_neg_left]; linarith) (by rw [dot_neg_left]; linarith)
    wt n (fun k hk => by rw [dot_neg_left]; linarith [hw k hk])
    (fun p hp => by rw [dot_neg_left]; linarith [hB p hp]) z hz
  rw [dot_neg_left] at h
  linarith

/-- `tower R₀ wt (n+1)` is `+ wt n`-closed by construction, so the whole lattice ray
`b₀pt + ℕ • wt n` sits in it as soon as `b₀pt` does.  This is `hrec_of_convex`'s `hwray` at
every tower index `≥ 1` (at the seed itself, `hwray` is the cone's own `u'`-ray instead). -/
theorem ray_mem_tower_succ {R₀ : Set (ℤ × ℤ)} (wt : ℕ → ℤ × ℤ) (n : ℕ)
    {b₀pt : ℤ × ℤ} (hb₀pt : b₀pt ∈ tower R₀ wt (n + 1)) :
    ∀ t : ℕ, b₀pt + t • wt n ∈ tower R₀ wt (n + 1) := by
  intro t
  induction t with
  | zero => simpa using hb₀pt
  | succ k ih =>
    have hstep : b₀pt + (k + 1) • wt n = (b₀pt + k • wt n) + wt n := by
      rw [succ_nsmul]; abel
    rw [hstep]
    simp only [tower] at ih ⊢
    exact add_mem_sweep ih

/-- **`h0` + `hbase` for `Rinf = tower (coneRegion B vl u') wt (n+1)`.**

Consumer: `RegionSteps.lean:1754` and `:1756-1757`.  The previous level
`C := tower (coneRegion B vl u') wt n` carries the periodicity (`hper` — `:814`'s defining
property of `I`), and `Rinf` is its one-step sweep along `wt n` (`:808`).  Premises:

* **seed extremality** (`hb₀pt`, `hmB`, `hpB`): `b₀pt ∈ B` minimises `dot m` and maximises
  `dot nprev` over `B` — the shared-vertex facts of two consecutive edge normals of `B`,
  i.e. `HsuppTowerBase.faceStart_nprevOf_extremal`'s content (`HsuppTowerGeneral.lean`);
* **sign conditions** on `m`/`nprev` against `vl`, `u'` and the tower directions;
* **lattice convexity** `hC`, and the base ray `hwray` (`ray_mem_tower_succ` when `n ≥ 1`).

`b₀` comes out as `dot m b₀pt`, so `hrec_of_convex`'s `hb₀` never appears as a premise. -/
theorem exists_base_tower {A : Type*} {ξ : Config A} {e : ℤ × ℤ} {c : ℤ}
    {B : Set (ℤ × ℤ)} {vl u' b₀pt : ℤ × ℤ}
    (wt : ℕ → ℤ × ℤ) (n : ℕ)
    (hC : IsLatticeConvexRegion (tower (coneRegion B vl u') wt n))
    (hmvl : 0 ≤ dot m vl) (hmu' : 0 ≤ dot m u') (hmwt : ∀ k, k < n → 0 ≤ dot m (wt k))
    (hmB : ∀ p ∈ B, dot m b₀pt ≤ dot m p)
    (hpvl : dot nprev vl ≤ 0) (hpu' : dot nprev u' ≤ 0)
    (hpwt : ∀ k, k < n → dot nprev (wt k) ≤ 0)
    (hpB : ∀ p ∈ B, dot nprev p ≤ dot nprev b₀pt)
    (hwray : ∀ t : ℕ, b₀pt + t • w ∈ tower (coneRegion B vl u') wt n)
    (hmw : dot m w = 0) (hneg : dot m (wt n) < 0)
    (hpw : dot nprev w < 0) (hpw' : dot nprev (wt n) ≤ 0)
    (hper : Nivat.Colle41.PeriodOn (T e ξ) (tower (coneRegion B vl u') wt n) (c • vl)) :
    ∃ b : ℤ, (∃ z ∈ tower (coneRegion B vl u') wt (n + 1), dot m z = b) ∧
      ∀ lev : ℕ → ℤ, lev 0 = b →
        Nivat.Colle41.PeriodOn (T e ξ)
          (Nivat.L1Region.cut (tower (coneRegion B vl u') wt (n + 1)) m lev 0) (c • vl) := by
  have hlow : ∀ z ∈ tower (coneRegion B vl u') wt n, dot m b₀pt ≤ dot m z :=
    le_dot_of_mem_tower hmvl hmu' wt n hmwt hmB
  have hprev : ∀ z ∈ tower (coneRegion B vl u') wt n, dot nprev (z - b₀pt) ≤ 0 := by
    intro z hz
    have h := dot_le_of_mem_tower hpvl hpu' wt n hpwt hpB z hz
    have hsub : dot nprev (z - b₀pt) = dot nprev z - dot nprev b₀pt := by
      simp only [dot, Prod.fst_sub, Prod.snd_sub]; ring
    rw [hsub]
    linarith
  exact exists_base (C := tower (coneRegion B vl u') wt n) (w' := wt n) rfl hC hlow rfl
    hwray hmw hneg hprev hpw hpw' hper

/-! ## §3  Two of the sign premises, discharged for `nprevOf` / `wtower`

`nprevOf d nℓ vl u' i I = ± genPerp' (wtower d nℓ vl u' i I)` (`TowerConstruct.lean:1074`), so
it is perpendicular to its own tower direction and — by the *next* step of the same chain
order that `dot_nprevOf_neg` reads backwards — strictly positive on the following one.  With
`m := -(nprevOf … I)` these are exactly `exists_base_tower`'s `hmw` (`dot m (wtower I) = 0`)
and `hneg` (`dot m (wtower (I+1)) < 0`), and `hpw'` for `nprev := nprevOf … I`. -/

section NprevOf

variable {ξ : Nivat.Config ℤ}

open Nivat.Colle35 Nivat.ColleReg

/-- **`nprevOf I` is perpendicular to `wtower I`.**  Immediate from
`nprevOf = ± genPerp' (wtower I)` and `det w w = 0` through `det_eq_dot_genPerp'`; no
adjacency input.  This is `hrec_of_convex`'s `hmw` (for `m := ± nprevOf I`, `w := wtower I`)
and simultaneously the *equality* case of its `hpw'`. -/
theorem dot_nprevOf_wtower_self (d : DecompData ξ) {vl nℓ u' : ℤ × ℤ}
    (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0)
    {I : ℕ} (hIlen : I < (sortedCand d nℓ u' i).length) :
    dot (nprevOf d nℓ vl u' i I) (wtower d nℓ vl u' i I) = 0 := by
  have hwprim : Primitive (wtower d nℓ vl u' i I) :=
    prim_of_mem_candSet d hvl_prim hprim hperp i hdoth (mem_candSet_wtower hIlen)
  have hwprim' : Prim (wtower d nℓ vl u' i I) := Nivat.LE2.prim_iff_primitive.mpr hwprim
  have hzero : dot (wtower d nℓ vl u' i I) (Nivat.LE2.genPerp' (wtower d nℓ vl u' i I)) = 0 := by
    rw [← det_eq_dot_genPerp' hwprim' (wtower d nℓ vl u' i I)]
    simp only [det]; ring
  unfold nprevOf
  split_ifs
  · rw [dot_comm]; exact hzero
  · rw [dot_neg_left, dot_comm]; rw [hzero]; ring

/-- **The escape step.**  `dot_nprevOf_neg` (`TowerConstruct.lean:1082`) reads the chain order
`det_pos_extChain` *backwards* from `wtower I` and gets `< 0` for every earlier direction.
Reading the very same statement *forwards* — `j := I+1`, `k := I+2`, i.e. the pair
`(wtower I, wtower (I+1))` — flips the `det_skew` sign once and gives `> 0` for the next one.

This is `exists_base_tower`'s `hneg` with `m := -(nprevOf … I)`: the tower's next sweep
direction strictly leaves the half-plane supporting the current top level, which is what makes
`cut Rinf m lev 0` a proper truncation (`b3_colle2.txt:808`, `:818`). -/
theorem dot_nprevOf_wtower_succ_pos {B : Set (ℤ × ℤ)} (d : DecompData ξ) {vl nℓ u' : ℤ × ℤ}
    (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (henv : Nivat.LE2.EnvOf (↑d.Sphi : Set (ℤ × ℤ)) B)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0)
    (hadjB : ∀ nn ∈ E B, ¬ (dot nn vl < 0 ∧ 0 < dot nn u'))
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) (hnu : dot nℓ u' < 0) (hnℓ_ne : nℓ ≠ 0)
    {I : ℕ} (hIlen : I < (sortedCand d nℓ u' i).length)
    (hI2len : I + 2 ≤ (sortedCand d nℓ u' i).length) :
    0 < dot (nprevOf d nℓ vl u' i I) (wtower d nℓ vl u' i (I + 1)) := by
  have hwprim : Primitive (wtower d nℓ vl u' i I) :=
    prim_of_mem_candSet d hvl_prim hprim hperp i hdoth (mem_candSet_wtower hIlen)
  have hwprim' : Prim (wtower d nℓ vl u' i I) := Nivat.LE2.prim_iff_primitive.mpr hwprim
  have hkey := det_pos_extChain d hvl_prim hprim hperp henv i hdoth hadjB hunimod hnu hnℓ_ne
    (j := I + 1) (k := I + 2) (by omega) hI2len
  have he1 : extChain d nℓ vl u' i (I + 1) = wtower d nℓ vl u' i I := rfl
  have he2 : extChain d nℓ vl u' i (I + 2) = wtower d nℓ vl u' i (I + 1) := rfl
  rw [he1, he2, det_eq_dot_genPerp' hwprim' (wtower d nℓ vl u' i (I + 1))] at hkey
  have hcne : det u' (-vl) ≠ 0 := by
    have h1 : det u' vl ≠ 0 := det_ne_zero_of_dot_nl_neg hvl_prim hperp hnu
    intro h0; apply h1
    have heqn : det u' (-vl) = - det u' vl := by
      simp only [det, Prod.fst_neg, Prod.snd_neg]; ring
    omega
  unfold nprevOf
  split_ifs with hc
  · have : 0 < dot (wtower d nℓ vl u' i (I + 1)) (Nivat.LE2.genPerp' (wtower d nℓ vl u' i I)) := by
      nlinarith [hkey, hc]
    rw [dot_comm]; exact this
  · push Not at hc
    have hclt : det u' (-vl) < 0 := hc.lt_of_ne hcne
    have : dot (wtower d nℓ vl u' i (I + 1)) (Nivat.LE2.genPerp' (wtower d nℓ vl u' i I)) < 0 := by
      nlinarith [hkey, hclt]
    rw [dot_neg_left, dot_comm]
    omega

end NprevOf

/-! ## §4  `hcut`: the level-`b₀` cut of `𝓡_{I−1}` lands back inside `𝓡_I`

Consumer: `lane-towerpkg`'s residual binder `hcut` of `lane_towerpkg_reduce`
(`tmp/wip/lane-towerpkg-main.lean`), which `PeriodOn.mono` turns into the package's `hbase`
conjunct (`RegionSteps.lean:1757`).

原文 `b3_colle2.txt:818`：`𝓡^n_I := {g + t·v⃗_{ℓ_{I−1}} : g ∈ 𝓡_I, t ∈ ℤ₊,
dist(·, ℓ'_{𝓡_I}) ≤ d_n}`，其中 `0 = d_0 < d_1 < ⋯`。取 `n = 0`（`d_0 = 0`）这句话就是
「`𝓡_{I−1} = sweep 𝓡_I v⃗_{ℓ_{I−1}}` 与 `ℓ'` 支撑半平面的交等于 `𝓡_I`」。逐量词对应：
`𝓡_I = tower (coneRegion B vl u') (wtower …) I`，`v⃗_{ℓ_{I−1}} = wtower … I`（扫掠方向），
`ℓ'` 的法向 `m = expNormal (extChain … I) vl`（`:816` 的 `ℓ_I = ℓ'`），`t ∈ ℤ₊ = t : ℕ`。
这里只证 `⊆` 那一半（`⊇` 是 `subset_sweep`，消费者用不到）。

⚠ **截断层必须压过整个种子 `B`，不能只压过 `𝓡_I` 自己的 `m`-支撑线。** 后者为假，内核见证在
`tmp/wip/lane-towerpkg-main.lean` 的 `hcut_support_level_false`（`:355`）：`B` 可以在 `-w`
方向探出 `𝓡_I` 的 `ℓ'`-边线之外，从那个探出点走一步 `wtower I` 又回到该边线上、却在 `𝓡_I`
之外。下面的 `hb₀ : dot m b₀pt ≤ b₀`（`b₀pt ∈ B`）正是排除它的条件。 -/

/-- **One sweep step, cut at a level at or above the corner `b₀pt`, lands back inside `C`.**

`hrec_of_convex` (`CutRecConvex.lean:55`) needs its cut level to be `C`'s *bottom* `m`-level,
attained at `b₀pt`.  The consumer's level `b₀` is not that — it sits at or above the seed's
top.  The gap is closed by applying `hrec_of_convex` to `C ∩ halfPlaneGE m (dot m b₀pt)`
instead of to `C`: that region's bottom level **is** `dot m b₀pt` by construction, its `w`-ray
out of `b₀pt` is the old one (`hmw` keeps it on the level), and its `nprev`-support is
inherited from `C`.  The step then only has to be checked at `dot m b₀pt ≤ b₀`, which is
`hb₀`.

Per-premise correspondence with `b3_colle2.txt`:
* `hC` — `𝓡_I` "is a `(−ℓ, ℓ_I)`-region" (`:808`), lattice-convexity half;
* `hbray`/`hmw` — the lattice `w`-ray out of `b₀pt` stays in `C` and stays on its `m`-level
  (`w = v⃗_{ℓ'}`, `:816`);
* `hneg` — the sweep direction strictly descends in `m` (`:808`/`:818`);
* `hprev`/`hpw`/`hpw'` — `nprev` supports `C` at `b₀pt` and puts `w`, `w'` on one side
  (`:766`, the cyclic order of edge normals);
* `hb₀` — the cut level is at or above `b₀pt` (`:818`'s `d_0 = 0` measured from `ℓ'_{𝓡_I}`).

⚠ The convexity binder is **not** `IsLatticeConvexRegion C`.  `hrec_of_convex` is applied to
`C ∩ halfPlaneGE m (dot m b₀pt)` and nothing else about `C` is convex-sensitive, so the
hypothesis is only that *that slice* is lattice convex.  This matters: `IsLatticeConvexRegion`
of a whole tower level is kernel-refuted (`lane-tower-hlev`, both at `n = 0` — the seed
`coneRegion B vl u'` is a staircase upset, non-convex as soon as `B` is — and at `n = 1`,
`TowerLevelStep.sweep_cone_not_isLatticeConvexRegion`).  The slice above the seed's own corner
avoids the apex region where the semigroup `ℕvl + ℕu' + ℕ·wtower` has its Frobenius gaps. -/
theorem cut_step_subset_of_cut
    (hCcut : IsLatticeConvexRegion (C ∩ halfPlaneGE m (dot m b₀pt)))
    (hbray : ∀ t : ℕ, b₀pt + t • w ∈ C)
    (hmw : dot m w = 0)
    (hneg : dot m w' < 0)
    (hprev : ∀ q ∈ C, dot nprev q ≤ dot nprev b₀pt)
    (hpw : dot nprev w < 0)
    (hpw' : dot nprev w' ≤ 0)
    (hb₀ : dot m b₀pt ≤ b₀)
    {z : ℤ × ℤ} (hz : z ∈ sweep C w') (hlev : b₀ ≤ dot m z) :
    z ∈ C := by
  obtain ⟨g, hg, t, rfl⟩ := hz
  have hcast : (t : ℤ) • w' = t • w' := natCast_zsmul w' t
  rw [hcast] at hlev ⊢
  have htnn : (0 : ℤ) ≤ (t : ℤ) := Int.natCast_nonneg t
  have hdrop : dot m (g + t • w') = dot m g + (t : ℤ) * dot m w' := by
    rw [← hcast, dot_add, dot_smul_right]
  have hmono : dot m (g + t • w') ≤ dot m g := by
    rw [hdrop]; nlinarith
  have hlow' : ∀ q ∈ C ∩ halfPlaneGE m (dot m b₀pt), dot m b₀pt ≤ dot m q :=
    fun q hq => hq.2
  have hwray' : ∀ s : ℕ, b₀pt + s • w ∈ C ∩ halfPlaneGE m (dot m b₀pt) := by
    intro s
    refine ⟨hbray s, ?_⟩
    show dot m b₀pt ≤ dot m (b₀pt + s • w)
    rw [← natCast_zsmul w s, dot_add, dot_smul_right, hmw, mul_zero, add_zero]
  have hprev' : ∀ q ∈ C ∩ halfPlaneGE m (dot m b₀pt), dot nprev (q - b₀pt) ≤ 0 := by
    intro q hq
    have h := hprev q hq.1
    have hexp : dot nprev (q - b₀pt) = dot nprev q - dot nprev b₀pt := by
      simp only [dot, Prod.fst_sub, Prod.snd_sub]; ring
    omega
  have hgmem : g ∈ C ∩ halfPlaneGE m (dot m b₀pt) := by
    refine ⟨hg, ?_⟩
    show dot m b₀pt ≤ dot m g
    exact le_trans (le_trans hb₀ hlev) hmono
  exact (Nivat.ColleReg.hrec_of_convex hCcut
    hlow' rfl hwray' hmw hneg hprev' hpw hpw' g hgmem t (le_trans hb₀ hlev)).1

/-- `cut_step_subset_of_cut` with the stronger, more familiar binder
`IsLatticeConvexRegion C`.  Kept because it is the shape the `hrec_of_convex` literature
states; `isLatticeConvexRegion_inter_halfPlaneGE` (`RegionCutGE.lean:25`) is the only step. -/
theorem cut_step_subset
    (hC : IsLatticeConvexRegion C)
    (hbray : ∀ t : ℕ, b₀pt + t • w ∈ C)
    (hmw : dot m w = 0)
    (hneg : dot m w' < 0)
    (hprev : ∀ q ∈ C, dot nprev q ≤ dot nprev b₀pt)
    (hpw : dot nprev w < 0)
    (hpw' : dot nprev w' ≤ 0)
    (hb₀ : dot m b₀pt ≤ b₀)
    {z : ℤ × ℤ} (hz : z ∈ sweep C w') (hlev : b₀ ≤ dot m z) :
    z ∈ C :=
  cut_step_subset_of_cut
    (Nivat.LE2.isLatticeConvexRegion_inter_halfPlaneGE hC m (dot m b₀pt))
    hbray hmw hneg hprev hpw hpw' hb₀ hz hlev

section Hcut

variable {ξ : Nivat.Config ℤ}

open Nivat.Colle35 Nivat.ColleReg

/-- **The `extChain I`-ray inside `𝓡_I` itself.**

Sharpening of `rayIn_tower_extChain`-style statements, which only place the `extChain J`-ray
inside `tower … (J+1)`: since `extChain (J+1) = wtower J` is *the* direction
`tower … (J+1) = sweep (tower … J) (wtower J)` is swept by, the ray is already in
`tower … (J+1)`, one level lower.  At `J = 0` the direction is `u'` and the ray is the cone's
own (`:808`'s `𝓡_{ι−1}` is built from `B` by `vl`- and `u'`-rays).

This is `cut_step_subset`'s `hbray` for the tower. -/
theorem ray_mem_tower_extChain {B : Set (ℤ × ℤ)} (d : DecompData ξ) {vl nℓ u' : ℤ × ℤ}
    (i : Fin d.m) (I : ℕ) {p : ℤ × ℤ} (hp : p ∈ coneRegion B vl u') (t : ℕ) :
    p + t • extChain d nℓ vl u' i I ∈
      tower (coneRegion B vl u') (wtower d nℓ vl u' i) I := by
  cases I with
  | zero =>
    show p + t • u' ∈ coneRegion B vl u'
    rw [mem_coneRegion_iff] at hp ⊢
    obtain ⟨b, hb, s, r, rfl⟩ := hp
    refine ⟨b, hb, s, r + t, ?_⟩
    rw [← natCast_zsmul u' t]
    push_cast
    module
  | succ J =>
    have hpJ : p ∈ tower (coneRegion B vl u') (wtower d nℓ vl u' i) (J + 1) :=
      tower_monotone _ _ (Nat.zero_le (J + 1)) hp
    exact ray_mem_tower_succ (wtower d nℓ vl u' i) J hpJ t

/-- **`hcut`, character for character** (`lane-towerpkg`'s residual binder).

`𝓡_{I−1} = tower … (I+1)` cut at any `dot m`-level `b` that dominates the whole seed `B`
lands back in `𝓡_I = tower … I`.  原文 `:818`，`d_0 = 0`.

Everything except lattice convexity (`hconv`, lane-tower-hlev) and the descent of the sweep
direction (`hstep`, `lane-towerpkg`'s own `dot_m_step_neg`) is discharged here against
`TowerConstruct.lean`.  The corner `b₀pt` is the `dot nℓ`-maximal point of `B`, and `nℓ`
itself is `cut_step_subset`'s `nprev`: every building direction of the tower has
`dot nℓ (·) < 0` (`dot_of_mem_candSet`, `dot_extChain_neg`) with the single exception of `vl`,
where it is `0` (`hperp`) — so `dot nℓ` is maximised on the seed (`hprev`), `dot nℓ w < 0`
(`hpw`) and `dot nℓ w' ≤ 0` (`hpw'`, an equality at the last index where
`wtower … I = -vl`).  No edge-adjacency input is needed.

The corner `p` and the convexity binder are explicit here, the latter only on the **slice**
`tower … I ∩ halfPlaneGE m (dot m p)` — see `cut_step_subset_of_cut` for why that matters now
that `IsLatticeConvexRegion (tower … n)` is refuted. -/
theorem cut_tower_step_of_cut {B : Set (ℤ × ℤ)} (d : DecompData ξ) {vl nℓ u' : ℤ × ℤ}
    (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0) (hnu : dot nℓ u' < 0)
    {I : ℕ} (hIlen : I ≤ (sortedCand d nℓ u' i).length)
    {p : ℤ × ℤ} (hpB : p ∈ B) (hpmax : ∀ q ∈ B, dot nℓ q ≤ dot nℓ p)
    (hconv : IsLatticeConvexRegion
      (tower (coneRegion B vl u') (wtower d nℓ vl u' i) I ∩
        halfPlaneGE (expNormal (extChain d nℓ vl u' i I) vl)
          (dot (expNormal (extChain d nℓ vl u' i I) vl) p)))
    (hstep : dot (expNormal (extChain d nℓ vl u' i I) vl) (wtower d nℓ vl u' i I) < 0)
    {b : ℤ} (hseed : ∀ q ∈ B, dot (expNormal (extChain d nℓ vl u' i I) vl) q ≤ b)
    {z : ℤ × ℤ}
    (hz : z ∈ tower (coneRegion B vl u') (wtower d nℓ vl u' i) (I + 1))
    (hlev : b ≤ dot (expNormal (extChain d nℓ vl u' i I) vl) z) :
    z ∈ tower (coneRegion B vl u') (wtower d nℓ vl u' i) I := by
  have hpcone : p ∈ coneRegion B vl u' := by
    rw [mem_coneRegion_iff]; exact ⟨p, hpB, 0, 0, by simp⟩
  have hwtnl : ∀ k, k < I → dot nℓ (wtower d nℓ vl u' i k) ≤ 0 := fun k hk =>
    le_of_lt (dot_of_mem_candSet d hvl_prim hprim hperp i hdoth
      (mem_candSet_wtower (by omega)))
  have hprev : ∀ q ∈ tower (coneRegion B vl u') (wtower d nℓ vl u' i) I,
      dot nℓ q ≤ dot nℓ p :=
    dot_le_of_mem_tower (le_of_eq hperp) (le_of_lt hnu) (wtower d nℓ vl u' i) I hwtnl hpmax
  have hpw : dot nℓ (extChain d nℓ vl u' i I) < 0 :=
    dot_extChain_neg d hvl_prim hprim hperp i hdoth hnu hIlen
  have hpw' : dot nℓ (wtower d nℓ vl u' i I) ≤ 0 := by
    by_cases hI : I < (sortedCand d nℓ u' i).length
    · exact le_of_lt (dot_of_mem_candSet d hvl_prim hprim hperp i hdoth
        (mem_candSet_wtower hI))
    · have hIeq : I = (sortedCand d nℓ u' i).length := by omega
      rw [hIeq, wtower_last]
      have hnegvl : dot nℓ (-vl) = - dot nℓ vl := by
        simp only [dot, Prod.fst_neg, Prod.snd_neg]; ring
      omega
  exact cut_step_subset_of_cut hconv (fun s => ray_mem_tower_extChain d i I hpcone s)
    dot_expNormal_u' hstep hprev hpw hpw' (hseed p hpB) hz hlev

/-- `cut_tower_step_of_cut` with the corner supplied by finiteness of `B` and the convexity
binder in its strong (now refuted) form.  Kept for the record; `cut_tower_step_of_cut` is the
live statement. -/
theorem cut_tower_step {B : Set (ℤ × ℤ)} (d : DecompData ξ) {vl nℓ u' : ℤ × ℤ}
    (hBfin : B.Finite) (hBne : B.Nonempty)
    (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0) (hnu : dot nℓ u' < 0)
    {I : ℕ} (hIlen : I ≤ (sortedCand d nℓ u' i).length)
    (hconv : IsLatticeConvexRegion (tower (coneRegion B vl u') (wtower d nℓ vl u' i) I))
    (hstep : dot (expNormal (extChain d nℓ vl u' i I) vl) (wtower d nℓ vl u' i I) < 0)
    {b : ℤ} (hseed : ∀ q ∈ B, dot (expNormal (extChain d nℓ vl u' i I) vl) q ≤ b)
    {z : ℤ × ℤ}
    (hz : z ∈ tower (coneRegion B vl u') (wtower d nℓ vl u' i) (I + 1))
    (hlev : b ≤ dot (expNormal (extChain d nℓ vl u' i I) vl) z) :
    z ∈ tower (coneRegion B vl u') (wtower d nℓ vl u' i) I := by
  obtain ⟨p, hpB, hpmax⟩ := B.exists_max_image (dot nℓ) hBfin hBne
  exact cut_tower_step_of_cut d hvl_prim hprim hperp i hdoth hnu hIlen hpB hpmax
    (Nivat.LE2.isLatticeConvexRegion_inter_halfPlaneGE hconv _ _) hstep hseed hz hlev

/-- **The consumer's binder, character for character.**

This is `lane_towerpkg_reduce`'s residual `hcut`
(`tmp/wip/lane-towerpkg-main.lean:437-441`) copied verbatim, under that theorem's own binders
plus the two inputs it already owns:

* `hconv` — its residual 1 (`:429-430`, owner `lane-tower-hlev`); only index `I` is used;
* `hstepAll` — its own `dot_m_step_neg` (`:148`), whose conclusion and `I ≤ length` bound
  match `hstepAll` verbatim.

`hunimod`, `henv`, `hadj`, `hc`, `hbase₁`, `hξ` are **not** needed. -/
theorem hcut_tower {B : Set (ℤ × ℤ)} (d : DecompData ξ) {vl nℓ u' : ℤ × ℤ}
    (hBfin : B.Finite) (hBne : B.Nonempty)
    (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0) (hnu : dot nℓ u' = -1)
    (hconv : ∀ n : ℕ, n ≤ (sortedCand d nℓ u' i).length + 1 →
      IsLatticeConvexRegion (tower (coneRegion B vl u') (wtower d nℓ vl u' i) n))
    (hstepAll : ∀ I : ℕ, I ≤ (sortedCand d nℓ u' i).length →
      dot (expNormal (extChain d nℓ vl u' i I) vl) (wtower d nℓ vl u' i I) < 0) :
    ∀ I : ℕ, I ≤ (sortedCand d nℓ u' i).length → ∀ b₀ : ℤ,
      (∀ b ∈ B, dot (expNormal (extChain d nℓ vl u' i I) vl) b ≤ b₀) →
      ∀ z ∈ tower (coneRegion B vl u') (wtower d nℓ vl u' i) (I + 1),
        b₀ ≤ dot (expNormal (extChain d nℓ vl u' i I) vl) z →
        z ∈ tower (coneRegion B vl u') (wtower d nℓ vl u' i) I := by
  intro I hI b₀ hseed z hz hlev
  exact cut_tower_step d hBfin hBne hvl_prim hprim hperp i hdoth (by omega) hI
    (hconv I (by omega)) (hstepAll I hI) hseed hz hlev

/-- **`hcut` with the convexity binder cut down to the half-plane above the seed.**

Same conclusion as `hcut_tower`, but instead of
`hconv : ∀ n ≤ length + 1, IsLatticeConvexRegion (tower … n)` it asks only that each tower
level be lattice convex **after intersecting with a `dot m`-half-plane**.  Strictly weaker
(`isLatticeConvexRegion_inter_halfPlaneGE`), and the level actually used is `dot m p` with `p`
the `dot nℓ`-argmax of `B`.

⚠ This is kept for the record, not as a way round `hconv`: at `I ≥ 1` the weaker binder does
not help, because the lattice points the semigroup `ℕvl + ℕu' + ℕ·wtower` misses lie *inside*
the slice (`TowerLevelStep`'s `w = (-2,3)` instance: the missing midpoint `(-1,2)` has
`dot m = 3` against a cut level `0`).  At `I = 0` the slice discharges itself — §7.  The strong
`hconv` is not refuted either: §12's `isLatticeConvexRegion_tower_wtower` proves it outright
once `lane-tower-hlev` supplies `hR₀` and `hlevB`, and the two circulated counterexamples were
both on illegal seeds (see the module docstring).

Also note the index range is `n ≤ length`, not `length + 1`: `cut_tower_step_of_cut` only ever
touches the level it lands in. -/
theorem hcut_tower_of_cut {B : Set (ℤ × ℤ)} (d : DecompData ξ) {vl nℓ u' : ℤ × ℤ}
    (hBfin : B.Finite) (hBne : B.Nonempty)
    (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0) (hnu : dot nℓ u' = -1)
    (hconv : ∀ n : ℕ, n ≤ (sortedCand d nℓ u' i).length → ∀ β : ℤ,
      IsLatticeConvexRegion (tower (coneRegion B vl u') (wtower d nℓ vl u' i) n ∩
        halfPlaneGE (expNormal (extChain d nℓ vl u' i n) vl) β))
    (hstepAll : ∀ I : ℕ, I ≤ (sortedCand d nℓ u' i).length →
      dot (expNormal (extChain d nℓ vl u' i I) vl) (wtower d nℓ vl u' i I) < 0) :
    ∀ I : ℕ, I ≤ (sortedCand d nℓ u' i).length → ∀ b₀ : ℤ,
      (∀ b ∈ B, dot (expNormal (extChain d nℓ vl u' i I) vl) b ≤ b₀) →
      ∀ z ∈ tower (coneRegion B vl u') (wtower d nℓ vl u' i) (I + 1),
        b₀ ≤ dot (expNormal (extChain d nℓ vl u' i I) vl) z →
        z ∈ tower (coneRegion B vl u') (wtower d nℓ vl u' i) I := by
  intro I hI b₀ hseed z hz hlev
  obtain ⟨p, hpB, hpmax⟩ := B.exists_max_image (dot nℓ) hBfin hBne
  exact cut_tower_step_of_cut d hvl_prim hprim hperp i hdoth (by omega) hI hpB hpmax
    (hconv I hI _) (hstepAll I hI) hseed hz hlev

end Hcut

/-! ## §5  The two sign conjuncts the consumer also asks for, in the same `m`

`OPEN.md #10 / #10b` records a suspected tension: the cover side wants `hmvl : 0 < dot m vl`
(`RegionSteps.lean:1750`) while the `hbase` side wants a bound on `dot m` in the *opposite*
direction.  There is no tension, and the reason is a sign, not a wall:

* `hmvl` and `hunb` are about **`Rinf = 𝓡_{I−1}`**, the swept region;
* `hlow` (§1) / `hb₀` (§4) are about **`C = 𝓡_I`**, the previous level, in the `dot m`-**lower**
  direction only.

`𝓡_I` is `+ vl`-closed, so `0 < dot m vl` makes `dot m` unbounded **above** on it — which is
compatible with, and in fact says nothing about, a lower bound.  And `dot m w' < 0` makes
`dot m` unbounded **below** on `sweep 𝓡_I w'` — that *is* `hunb`, and it is exactly what makes
the level-`b₀` cut a proper truncation.  Both are proved here. -/

section Signs

open Nivat.Colle35 Nivat.ColleReg

variable {ξ : Nivat.Config ℤ}

/-- `expNormal a b = (det a b) • perp a`, so pairing it against `z` is
`det a b * det a z`.  Unfolding lemma for the two sign facts below; no unimodularity, unlike
`dot_expNormal_vl` (`L1RegionBuild.lean:288`). -/
theorem dot_expNormal_eq_det_mul (a b z : ℤ × ℤ) :
    dot (expNormal a b) z = det a b * det a z := by
  simp only [expNormal, dot, det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- **`hmvl` is a square.**  `dot (expNormal a vl) vl = (det a vl)^2`, so the consumer's
`0 < dot m vl` (`RegionSteps.lean:1750`) holds as soon as `a` is not parallel to `vl`.
No unimodularity and no seed data. -/
theorem dot_expNormal_vl_pos {a vl : ℤ × ℤ} (h : det a vl ≠ 0) :
    0 < dot (expNormal a vl) vl := by
  rw [dot_expNormal_eq_det_mul]
  exact mul_self_pos.mpr h

/-- **`hmvl` for the tower's own `m`.**  `m = expNormal (extChain … I) vl` and
`dot nℓ (extChain … I) < 0` (`dot_extChain_neg`, `TowerConstruct.lean:910`) with
`dot nℓ vl = 0` force `det (extChain … I) vl ≠ 0`
(`det_ne_zero_of_dot_nl_neg`, `TowerConstruct.lean:448`).  Same hypothesis set and same index
range `I ≤ length` as `cut_tower_step`, so the two compose. -/
theorem dot_m_vl_pos (d : DecompData ξ) {vl nℓ u' : ℤ × ℤ}
    (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0) (hnu : dot nℓ u' < 0)
    {I : ℕ} (hIlen : I ≤ (sortedCand d nℓ u' i).length) :
    0 < dot (expNormal (extChain d nℓ vl u' i I) vl) vl :=
  dot_expNormal_vl_pos (det_ne_zero_of_dot_nl_neg hvl_prim hperp
    (dot_extChain_neg d hvl_prim hprim hperp i hdoth hnu hIlen))

/-- **`hunb` is free from `hneg`.**  `RegionSteps.lean:1755`:
`∀ b, ∃ z ∈ Rinf, dot m z < b`.  With `Rinf = sweep C w'` and `dot m w' < 0` the sweep
parameter alone drives `dot m` to `-∞`, so no property of `C` beyond nonemptiness is used.
This is the conjunct about the **swept** region; §1's `hlow` is about `C`, and the two never
meet. -/
theorem exists_dot_lt_of_sweep {C : Set (ℤ × ℤ)} {m w' : ℤ × ℤ}
    (hne : C.Nonempty) (hneg : dot m w' < 0) (b : ℤ) :
    ∃ z ∈ sweep C w', dot m z < b := by
  obtain ⟨g, hg⟩ := hne
  refine ⟨g + ((((dot m g - b).toNat + 1 : ℕ) : ℤ)) • w', ⟨g, hg, (dot m g - b).toNat + 1, rfl⟩, ?_⟩
  rw [dot_add, dot_smul_right]
  have h1 : (dot m g - b) ≤ ((dot m g - b).toNat : ℤ) := Int.self_le_toNat _
  have h2 : (0 : ℤ) ≤ ((dot m g - b).toNat : ℤ) := Int.natCast_nonneg _
  push_cast
  nlinarith

end Signs

/-! ## §6  `hconv` via `isRegion_tower_of_steps`: the fifth disjunct is unreachable

`lane-tower-hlev`'s `latticeConvexRegion_tower_coneRegion_of_det_cases`
(`TowerLevelStep.lean:308`) reduces `hconv` to

```
hcase : ∀ i, det (w i) vl = 1 ∨ det (w i) vl = -1 ∨ det (w i) u' = 1 ∨ det (w i) u' = -1 ∨
             det (w i) vl * det (w i) u' < 0
```

with the fifth disjunct reading, in the `(vl, u')` basis `w = p•vl + q•u'`, as `p*q > 0`.

**For the tower's own directions that disjunct is never available.**  `dot nℓ (wtower … t) < 0`
with `dot nℓ vl = 0` forces `q` and `dot nℓ u'` to have the same sign, and `det_pos_extChain`
(`TowerConstruct.lean:1009`) read at `j = 0`, `k = t+1` — i.e. the pair `(u', wtower … t)` —
forces `p` to the opposite one.  So `p*q < 0` at every index, and `hcase` collapses to

```
det (wtower … t) vl = ±1  ∨  det (wtower … t) u' = ±1,
```

i.e. **every candidate direction must be unimodular with `vl` or with `u'`**.  That is exactly
the hypothesis `lane-tower-hlev`'s own sharpness witness
(`TowerLevelStep.tower_level_one_not_isRegion`, `w = -2•vl + 3•u'`) violates, and `candSet`
(`TowerConstruct.lean:246`) is `primPart ∘ orientGen` over the decomposition's generators, which
carries no such bound.  Conclusion: `hconv` does **not** follow from `isRegion_tower_of_steps`
on this chain; it needs the seed `B` (`henv`), not the sweep directions. -/

section HcaseObstruction

open Nivat.Colle35 Nivat.ColleReg

variable {ξ : Nivat.Config ℤ}

/-- Cramer, paired against a covector: `det vl u' * dot ν w = det w u' * dot ν vl +
det vl w * dot ν u'`.  A polynomial identity in the eight coordinates. -/
theorem det_dot_cramer (vl u' w ν : ℤ × ℤ) :
    det vl u' * dot ν w = det w u' * dot ν vl + det vl w * dot ν u' := by
  simp only [det, dot]
  ring

/-- **The fifth disjunct of `hcase` is false at every tower direction.**

Hypotheses are exactly `det_pos_extChain`'s plus `t < (sortedCand …).length`.  Consequence:
`lane-tower-hlev`'s `hcase` is equivalent, on this chain, to its first four disjuncts. -/
theorem det_wtower_vl_mul_u'_pos {B : Set (ℤ × ℤ)} (d : DecompData ξ) {vl nℓ u' : ℤ × ℤ}
    (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (henv : Nivat.LE2.EnvOf (↑d.Sphi : Set (ℤ × ℤ)) B)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0)
    (hadjB : ∀ nn ∈ E B, ¬ (dot nn vl < 0 ∧ 0 < dot nn u'))
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) (hnu : dot nℓ u' < 0) (hnℓ_ne : nℓ ≠ 0)
    {t : ℕ} (ht : t < (sortedCand d nℓ u' i).length) :
    0 < det (wtower d nℓ vl u' i t) vl * det (wtower d nℓ vl u' i t) u' := by
  set w := wtower d nℓ vl u' i t with hw
  -- `q`-side: `dot nℓ w < 0` (membership in `candSet`).
  have hnw : dot nℓ w < 0 :=
    dot_of_mem_candSet d hvl_prim hprim hperp i hdoth (mem_candSet_wtower ht)
  -- `p`-side: the chain order applied to the pair `(extChain 0, extChain (t+1)) = (u', w)`.
  have hkey := det_pos_extChain d hvl_prim hprim hperp henv i hdoth hadjB hunimod hnu hnℓ_ne
    (j := 0) (k := t + 1) (by omega) (by omega)
  have he0 : extChain d nℓ vl u' i 0 = u' := rfl
  have he1 : extChain d nℓ vl u' i (t + 1) = w := rfl
  rw [he0, he1] at hkey
  -- Rewrite both determinants against `E := det u' vl`.
  have hskew1 : det u' w = - det w u' := by simp only [det]; ring
  have hskew2 : det u' (-vl) = - det u' vl := by simp only [det, Prod.fst_neg, Prod.snd_neg]; ring
  have hskew3 : det vl w = - det w vl := by simp only [det]; ring
  have hskew4 : det vl u' = - det u' vl := by simp only [det]; ring
  have hcr := det_dot_cramer vl u' w nℓ
  rw [hperp, hskew3, hskew4] at hcr
  -- `hcr : -det u' vl * dot nℓ w = det w u' * 0 + -det w vl * dot nℓ u'`
  rw [hskew1, hskew2] at hkey
  -- `hkey : 0 < -det w u' * -det u' vl`
  rcases hunimod with hE | hE <;> rw [hE] at hcr hkey <;> nlinarith [hcr, hkey, hnw, hnu]

end HcaseObstruction

/-! ## §7  The `I = 0` slice is a unimodular quadrant — unconditionally

`lane-tower-hlev`'s positive `n = 0` result (`tmp/wip/lane-tower-hlev-conv.lean:377`) needs
`IsLatticeConvexRegion B` plus `±n ∈ E B`; its `n = 0` *refutation* has been withdrawn (see the
module docstring).

**The slice needs neither hypothesis.**  Cutting at the seed's own `dot nℓ`-corner collapses
`coneRegion B vl u'` to the quadrant `p + ℕvl + ℕu'`, for *every* `B` at all: the cut level is
exactly the `vl`-coordinate of the corner, and the corner already minimises the
`u'`-coordinate, so every surviving point has both coordinates of `z - p` non-negative.  In the
(withdrawn) refuting instance the corner is `(3,0)` or `(4,0)`, the level is `3` or `4`, and
the midpoint `(1,4)` at issue sits at level `1` — cut away; so the slice statement survives
even the seeds that the unsliced statement was doubted on.

The corner is stated here through `expNormal vl u'` (the second half of the dual basis) rather
than `nℓ`; `dot nℓ · ` and `dot (expNormal vl u') ·` are negatives of each other up to the unit
`det u' vl`, so a `dot nℓ`-argmax is a `dot (expNormal vl u')`-argmin. -/

section SeedSlice

open Nivat.ColleReg

/-- Cramer for the ordered pair `(u', vl)`: `det u' vl • x = det x vl • u' + det u' x • vl`.
A polynomial identity in the six coordinates. -/
theorem cramer_smul_pair (u' vl x : ℤ × ℤ) :
    det u' vl • x = (det x vl) • u' + (det u' x) • vl := by
  simp only [det, Prod.ext_iff, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Prod.fst_add,
    Prod.snd_add]
  constructor <;> ring

/-- **The dual-basis expansion.**  `(expNormal u' vl, expNormal vl u')` is the basis dual to
`(vl, u')` when `(u', vl)` is unimodular, so every `x` reads off its own coordinates. -/
theorem expNormal_basis_expand {u' vl : ℤ × ℤ}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) (x : ℤ × ℤ) :
    x = (dot (expNormal u' vl) x) • vl + (dot (expNormal vl u') x) • u' := by
  have hE' : det vl u' = - det u' vl := by simp only [det]; ring
  have hsq : det u' vl * det u' vl = 1 := by
    rcases hunimod with hE | hE <;> rw [hE] <;> ring
  rw [dot_expNormal_eq_det_mul, dot_expNormal_eq_det_mul, hE']
  simp only [det] at hsq ⊢
  rw [Prod.ext_iff]
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Prod.fst_add, Prod.snd_add]
  exact ⟨by linear_combination (-x.1) * hsq, by linear_combination (-x.2) * hsq⟩

/-- **The `I = 0` slice of the seed is the quadrant at its corner.**

`coneRegion B vl u'` cut at the `dot (expNormal u' vl)`-level of the point `p ∈ B` that
minimises `dot (expNormal vl u')` is exactly `p + ℕvl + ℕu'`.  No hypothesis on `B` beyond
`p`'s two extremality properties — in particular neither `IsLatticeConvexRegion B` nor any
edge condition, which is what `lane-tower-hlev`'s positive `n = 0` result needs.

原文 `b3_colle2.txt:780` (the seed cone) cut at `:818`'s `d_0 = 0`.  In the dual basis
`(m₁, m₂) := (expNormal u' vl, expNormal vl u')` a point `z = b + s•vl + t•u'` has
`dot m₁ z = dot m₁ b + s` and `dot m₂ z = dot m₂ b + t`; the cut makes the first coordinate of
`z - p` non-negative and `p`'s minimality makes the second one. -/
theorem coneRegion_inter_halfPlaneGE_eq_quadrant {B : Set (ℤ × ℤ)} {vl u' p : ℤ × ℤ}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hpB : p ∈ B)
    (hpmin : ∀ q ∈ B, dot (expNormal vl u') p ≤ dot (expNormal vl u') q) :
    coneRegion B vl u' ∩ halfPlaneGE (expNormal u' vl) (dot (expNormal u' vl) p)
      = coneRegion ({p} : Set (ℤ × ℤ)) vl u' := by
  have hswap : det vl u' = 1 ∨ det vl u' = -1 := by
    have h : det vl u' = - det u' vl := by simp only [det]; ring
    rcases hunimod with hE | hE
    · exact Or.inr (by omega)
    · exact Or.inl (by omega)
  have hm1vl : dot (expNormal u' vl) vl = 1 := dot_expNormal_vl hunimod
  have hm1u' : dot (expNormal u' vl) u' = 0 := dot_expNormal_u'
  have hm2u' : dot (expNormal vl u') u' = 1 := dot_expNormal_vl hswap
  have hm2vl : dot (expNormal vl u') vl = 0 := dot_expNormal_u'
  apply Set.eq_of_subset_of_subset
  · rintro z ⟨hzc, hzl⟩
    rw [mem_coneRegion_iff] at hzc
    obtain ⟨b, hb, s, t, rfl⟩ := hzc
    have hm1 : dot (expNormal u' vl) (b + (s : ℤ) • vl + (t : ℤ) • u')
        = dot (expNormal u' vl) b + (s : ℤ) := by
      rw [dot_add, dot_add, dot_smul_right, dot_smul_right, hm1vl, hm1u']; ring
    have hm2 : dot (expNormal vl u') (b + (s : ℤ) • vl + (t : ℤ) • u')
        = dot (expNormal vl u') b + (t : ℤ) := by
      rw [dot_add, dot_add, dot_smul_right, dot_smul_right, hm2vl, hm2u']; ring
    set z := b + (s : ℤ) • vl + (t : ℤ) • u' with hz
    have hA : 0 ≤ dot (expNormal u' vl) z - dot (expNormal u' vl) p := by
      have : dot (expNormal u' vl) p ≤ dot (expNormal u' vl) z := hzl
      omega
    have hBc : 0 ≤ dot (expNormal vl u') z - dot (expNormal vl u') p := by
      have h1 := hpmin b hb
      have h2 : (0 : ℤ) ≤ (t : ℤ) := Int.natCast_nonneg t
      omega
    have hexp := expNormal_basis_expand (u' := u') (vl := vl) hunimod (z - p)
    have hd1 : dot (expNormal u' vl) (z - p)
        = dot (expNormal u' vl) z - dot (expNormal u' vl) p := by
      simp only [dot, Prod.fst_sub, Prod.snd_sub]; ring
    have hd2 : dot (expNormal vl u') (z - p)
        = dot (expNormal vl u') z - dot (expNormal vl u') p := by
      simp only [dot, Prod.fst_sub, Prod.snd_sub]; ring
    rw [hd1, hd2] at hexp
    rw [mem_coneRegion_iff]
    refine ⟨p, rfl, (dot (expNormal u' vl) z - dot (expNormal u' vl) p).toNat,
      (dot (expNormal vl u') z - dot (expNormal vl u') p).toNat, ?_⟩
    rw [Int.toNat_of_nonneg hA, Int.toNat_of_nonneg hBc]
    have hshift : z = p + ((dot (expNormal u' vl) z - dot (expNormal u' vl) p) • vl
        + (dot (expNormal vl u') z - dot (expNormal vl u') p) • u') := by
      rw [← hexp]; abel
    exact hshift.trans (add_assoc p _ _).symm
  · rintro z hz
    rw [mem_coneRegion_iff] at hz
    obtain ⟨b, hb, s, t, rfl⟩ := hz
    rw [Set.mem_singleton_iff] at hb
    subst hb
    refine ⟨?_, ?_⟩
    · rw [mem_coneRegion_iff]; exact ⟨b, hpB, s, t, rfl⟩
    · show dot (expNormal u' vl) b ≤ dot (expNormal u' vl) (b + (s : ℤ) • vl + (t : ℤ) • u')
      rw [dot_add, dot_add, dot_smul_right, dot_smul_right, hm1vl, hm1u']
      have : (0 : ℤ) ≤ (s : ℤ) := Int.natCast_nonneg s
      omega

end SeedSlice

/-! ## §8  The fundamental parallelogram: how a fat seed fills the semigroup gaps

For `n ≥ 1` the tower level is `B + ℕ`-span of the directions used so far, while lattice
convexity wants `B + (Γ ∩ ℤ²)` for the *real* cone `Γ`.  The difference is exactly the
numerical-semigroup gap set that killed the `LevelInterval` route (and that
`det_wtower_vl_mul_u'_pos` above shows cannot be dodged by unimodularity: no candidate pair is
forced to be unimodular).

This section says the gap set is *finite and explicit*: every lattice point of the cone spanned
by `a, b` is an `ℕ`-combination of `a, b` **plus one of the `|det a b|` lattice points of the
half-open fundamental parallelogram**.  Hence a set closed under `+a` and `+b` that already
contains those residues contains the whole `Γ ∩ ℤ²`.

That is the precise form of "a fat seed fills the gaps": the residues are the points the
`ℕ`-span misses, and they all lie inside the parallelogram `[0,a] + [0,b]`, which the zonotope
`𝒮_φ = Σ_j [0, d.h j]` (原文 `b3_colle2.txt:665`, `DecompData.Sphi_eq`) contains whenever `a`
and `b` are `primPart`s of two of its own generators — `[0, d.h j] ⊇ [0, primPart (d.h j)]`.
Nothing here needs `IsLatticeConvexRegion` of any tower level, so §8 is untouched by the
refutation that killed `hconv`'s convexity route.

No new `Prop` is introduced: both statements are about `Nivat.det` only. -/

section ConeDecomp

/-- **Division with remainder in a plane cone.**  If `0 < det a b` and `z` lies in the cone
spanned by `a` and `b` (read off by the two Cramer coordinates `det z b ≥ 0`, `det a z ≥ 0`),
then `z = s•a + t•b + r` with `s t : ℕ` and `r` in the half-open fundamental parallelogram,
i.e. both Cramer coordinates of `r` lie in `[0, det a b)`.

The proof is `Int.mul_ediv_add_emod` in each coordinate; `cramer_smul_pair` is the identity that
makes `(det · b, det a ·)` the coordinate pair. -/
theorem exists_cone_decomp {a b z : ℤ × ℤ} (hD : 0 < det a b)
    (hX : 0 ≤ det z b) (hY : 0 ≤ det a z) :
    ∃ (s t : ℕ) (r : ℤ × ℤ), z = (s : ℤ) • a + (t : ℤ) • b + r ∧
      0 ≤ det r b ∧ det r b < det a b ∧ 0 ≤ det a r ∧ det a r < det a b := by
  have hDne : det a b ≠ 0 := ne_of_gt hD
  have hs0 : 0 ≤ det z b / det a b := Int.ediv_nonneg hX hD.le
  have ht0 : 0 ≤ det a z / det a b := Int.ediv_nonneg hY hD.le
  have hbil1 : ∀ c d : ℤ, det (z - c • a - d • b) b = det z b - c * det a b := by
    intro c d
    simp only [det, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  have hbil2 : ∀ c d : ℤ, det a (z - c • a - d • b) = det a z - d * det a b := by
    intro c d
    simp only [det, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  have hrb : det (z - (det z b / det a b) • a - (det a z / det a b) • b) b
      = det z b % det a b := by
    rw [hbil1]
    have h := Int.mul_ediv_add_emod (det z b) (det a b)
    linear_combination -h
  have har : det a (z - (det z b / det a b) • a - (det a z / det a b) • b)
      = det a z % det a b := by
    rw [hbil2]
    have h := Int.mul_ediv_add_emod (det a z) (det a b)
    linear_combination -h
  refine ⟨(det z b / det a b).toNat, (det a z / det a b).toNat,
    z - (det z b / det a b) • a - (det a z / det a b) • b, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Int.toNat_of_nonneg hs0, Int.toNat_of_nonneg ht0]; abel
  · rw [hrb]; exact Int.emod_nonneg _ hDne
  · rw [hrb]; exact Int.emod_lt_of_pos _ hD
  · rw [har]; exact Int.emod_nonneg _ hDne
  · rw [har]; exact Int.emod_lt_of_pos _ hD

/-- Translating a set by `n • v` stays inside it, when one step does. -/
theorem mem_of_nsmul_step {S : Set (ℤ × ℤ)} {v : ℤ × ℤ} (hv : ∀ x ∈ S, x + v ∈ S)
    (n : ℕ) (x : ℤ × ℤ) (hx : x ∈ S) : x + (n : ℤ) • v ∈ S := by
  induction n with
  | zero => simpa using hx
  | succ k ih =>
      have h1 := hv _ ih
      have h2 : x + ((k : ℤ) + 1) • v = x + (k : ℤ) • v + v := by module
      push_cast
      rw [h2]
      exact h1

/-- **A set closed under `+a`, `+b` and containing the fundamental parallelogram contains the
whole cone.**  This is the gap-filling statement in the form a consumer wants: the `ℕ`-span is
`hclosed_a`/`hclosed_b`, the seed's job is `hres`, and the conclusion is membership for an
arbitrary lattice point of the real cone (again read off by its two Cramer coordinates).

`hres` quantifies over the `det a b` lattice points of the half-open parallelogram only — a
finite, explicit obligation, not a convexity hypothesis. -/
theorem mem_of_cone_of_residues {S : Set (ℤ × ℤ)} {a b : ℤ × ℤ} (hD : 0 < det a b)
    (hres : ∀ r : ℤ × ℤ, 0 ≤ det r b → det r b < det a b → 0 ≤ det a r → det a r < det a b →
      r ∈ S)
    (hclosed_a : ∀ x ∈ S, x + a ∈ S) (hclosed_b : ∀ x ∈ S, x + b ∈ S)
    {z : ℤ × ℤ} (hX : 0 ≤ det z b) (hY : 0 ≤ det a z) : z ∈ S := by
  obtain ⟨s, t, r, hz, h1, h2, h3, h4⟩ := exists_cone_decomp hD hX hY
  have hrS : r ∈ S := hres r h1 h2 h3 h4
  have hfin := mem_of_nsmul_step hclosed_b t _ (mem_of_nsmul_step hclosed_a s r hrS)
  have heq : (s : ℤ) • a + (t : ℤ) • b + r = r + (s : ℤ) • a + (t : ℤ) • b := by abel
  rw [hz, heq]
  exact hfin

end ConeDecomp

/-! ## §9  From `LevelInterval B w` to `LevelInterval T w`: the descent

This is the arithmetic half of `hconv` for `n ≥ 1`, and it is what makes `lane-tower-hlev`'s
`n = 0` convexity argument reusable at every level instead of only at the seed.

The geometric half belongs to `lane-tower-hlev`: for a lattice convex `B` whose two extreme
faces in the `det w`-functional are both edges *parallel to* `w`, concavity of the slice width
gives width `≥ 1` at every intermediate level, hence `LevelInterval B w`.  Under
`henv : EnvOf ↑d.Sphi B` both those faces exist for **every** chain direction `w = w_k`:
`Enveloped` (`LatticeEdges.lean:628`) hands over `IsLatticeConvexRegion B`, `E B = E ↑d.Sphi`
and per-edge length domination, while `E ↑d.Sphi` is closed under negation
(`Colle35.Sphi_negSymm`, `DecompData.lean:417`) because `d.Sphi` is a zonotope
(`DecompData.Sphi_eq`, `DecompData.lean:108`), so `±genPerp' (d.h k) ∈ E B` with both faces
`Nontrivial`.

What is proved here is the step from the seed to the whole tower level, with **no convexity
hypothesis at all**.  A tower level `T` is `B` plus `ℕ`-steps in directions that all have
`det w · ≤ 0`, so its level set is bounded above by `B`'s maximum `Lmax`; and `B` itself
contains one `vl`-step, so `B`'s level range is at least `|det w vl|` wide.  Translating `B` by
`vl` repeatedly therefore covers every integer level `≤ Lmax` without leaving a hole — the
consecutive ranges overlap because each is at least as long as the shift.

This is the place where the naive picture fails and it is worth recording why: for a cone with
a single apex `b` the slice one level below the apex has lattice width `1 / (q * |p|)` (writing
`w = p • vl + q • u'` in the unimodular basis, `p < 0 < q`), which is `< 1` as soon as
`q * |p| > 1` — e.g. `1/6` for `TowerLevelStep`'s `w = (-2,3)`.  A pointed cone has no lattice
point at that level.  The seed is not pointed: the edge-length clause of `Enveloped` is exactly
what supplies the missing width.

原文 `b3_colle2.txt:806-820` (the tower) with `:665` (the zonotope 𝒮_φ). -/

section Descent

/-- Levels are additive along a step: `det w (z + k • v) = det w z + k * det w v`. -/
theorem det_add_zsmul_right (w z v : ℤ × ℤ) (k : ℤ) :
    det w (z + k • v) = det w z + k * det w v := by
  simp only [det, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- Negating the level normal negates the level. -/
theorem det_neg_left' (w z : ℤ × ℤ) : det (-w) z = -det w z := by
  simp only [det, Prod.fst_neg, Prod.snd_neg]
  ring

/-- `LevelInterval` does not see the orientation of its normal: the two endpoints of the
interval simply swap.  This is what lets a consumer pick whichever of `± w` descends along
`vl`, independently of which of `det u' vl = ±1` holds. -/
theorem levelInterval_of_neg {C : Set (ℤ × ℤ)} {w : ℤ × ℤ} (h : LevelInterval C (-w)) :
    LevelInterval C w := by
  intro a ha b hb m hma hmb
  obtain ⟨c, hc, hcm⟩ := h b hb a ha (-m)
    (by rw [det_neg_left']; omega) (by rw [det_neg_left']; omega)
  rw [det_neg_left'] at hcm
  exact ⟨c, hc, by omega⟩

/-- The converse of `levelInterval_of_neg`. -/
theorem levelInterval_neg {C : Set (ℤ × ℤ)} {w : ℤ × ℤ} (h : LevelInterval C w) :
    LevelInterval C (-w) :=
  levelInterval_of_neg (by rwa [neg_neg])

/-- **`LevelInterval` for free, when the set has a unit step.**  If `C` is closed under `+ v`
and `det w v = ±1`, then stepping by `v` moves the level by exactly one, so no level between
two attained ones can be skipped.  No convexity, no seed, no bound.

This is what covers the tail of the candidate chain, where `wtower … n = -vl`
(`TowerConstruct.wtower_last`): there `det (wt n) vl = 0` and the descent of §9 is unavailable,
but `det (-vl) u' = det u' vl = ±1` and the tower level is closed under `+u'`.

⚠ **Duplicate** (`lane-tower-hlev`, 2026-09-23): this is the `∨`-merged form of the main-repo
pair `Nivat.TowerLevelStep.levelInterval_of_step_det_one` (`TowerLevelStep.lean:89`) /
`levelInterval_of_step_det_neg_one` (`:102`).  Kept as a local proof only because
`TowerLevelStep` is not among this file's imports; if an import is ever added, delete the
proof body and `rcases hdet` into those two. -/
theorem levelInterval_of_unit_step {C : Set (ℤ × ℤ)} {w v : ℤ × ℤ}
    (hstep : ∀ x ∈ C, x + v ∈ C) (hdet : det w v = 1 ∨ det w v = -1) :
    LevelInterval C w := by
  intro a ha b hb m hma hmb
  rcases hdet with hd | hd
  · refine ⟨a + ((m - det w a).toNat : ℤ) • v,
      mem_of_nsmul_step hstep _ a ha, ?_⟩
    rw [det_add_zsmul_right, hd, Int.toNat_of_nonneg (by omega)]
    omega
  · refine ⟨b + ((det w b - m).toNat : ℤ) • v,
      mem_of_nsmul_step hstep _ b hb, ?_⟩
    rw [det_add_zsmul_right, hd, Int.toNat_of_nonneg (by omega)]
    omega

/-- **The descent.**  Every integer level `≤ Lmax` is attained on `T`.

`B ⊆ T` supplies the levels it attains itself; `hstep` lets a witness be pushed down by `v`,
one `|det w v|` at a time; and the `v`-step `a, a + v ∈ B` inside `B` guarantees `B`'s own level
range is at least `|det w v|` long, so the pushed copies overlap and leave no hole.

No convexity, no finiteness: `hlevB` is the only structural input, and it is exactly
`RegionSweep.LevelInterval` (`RegionSweep.lean:174`). -/
theorem exists_mem_det_eq_of_descent {T B : Set (ℤ × ℤ)} {w v a p : ℤ × ℤ} {Lmax : ℤ}
    (hBT : B ⊆ T)
    (hlevB : LevelInterval B w)
    (hstep : ∀ x ∈ T, x + v ∈ T)
    (haB : a ∈ B) (havB : a + v ∈ B)
    (hvneg : det w v < 0)
    (hpB : p ∈ B) (hpmax : det w p = Lmax)
    (hub : ∀ z ∈ B, det w z ≤ Lmax)
    {m : ℤ} (hm : m ≤ Lmax) : ∃ z ∈ T, det w z = m := by
  have hav : det w (a + v) = det w a + det w v := by
    simpa using det_add_zsmul_right w a v 1
  by_cases hcase : det w a ≤ m
  · obtain ⟨c, hc, hcm⟩ := hlevB a haB p hpB m hcase (by omega)
    exact ⟨c, hBT hc, hcm⟩
  · push_neg at hcase
    set q : ℤ := -det w v with hq
    have hq0 : 0 < q := by omega
    set D : ℤ := det w a - m with hD
    have hD0 : 0 ≤ D := by omega
    set j : ℤ := D / q with hj
    have hj0 : 0 ≤ j := Int.ediv_nonneg hD0 hq0.le
    have hmod : det w a - (m + j * q) = D % q := by
      have h := Int.mul_ediv_add_emod D q
      rw [hD] at h ⊢
      linear_combination -h
    have hmod0 : 0 ≤ D % q := Int.emod_nonneg _ (ne_of_gt hq0)
    have hmodlt : D % q < q := Int.emod_lt_of_pos _ hq0
    obtain ⟨c, hc, hcm⟩ := hlevB (a + v) havB a haB (m + j * q) (by omega) (by omega)
    refine ⟨c + (j.toNat : ℤ) • v, mem_of_nsmul_step hstep j.toNat c (hBT hc), ?_⟩
    rw [det_add_zsmul_right, hcm, Int.toNat_of_nonneg hj0]
    have hjv : j * det w v = -(j * q) := by rw [hq]; ring
    omega

/-- **The tower level inherits `LevelInterval` from the seed.**  Packaged for
`RegionSweep.isLatticeConvexRegion_sweep` (`RegionSweep.lean:213`), whose third hypothesis this
is.  `hub` is the statement that every direction used to build `T` descends in the
`det w`-functional; on the candidate chain that is `det_wtower_vl_mul_u'_pos` for `vl` and `u'`
and `det_pos_extChain` for the earlier steps. -/
theorem levelInterval_of_descent {T B : Set (ℤ × ℤ)} {w v a p : ℤ × ℤ} {Lmax : ℤ}
    (hBT : B ⊆ T)
    (hlevB : LevelInterval B w)
    (hstep : ∀ x ∈ T, x + v ∈ T)
    (haB : a ∈ B) (havB : a + v ∈ B)
    (hvneg : det w v < 0)
    (hpB : p ∈ B) (hpmax : det w p = Lmax)
    (hub : ∀ z ∈ T, det w z ≤ Lmax) :
    LevelInterval T w := by
  intro _ _ y hy m _ hmy
  exact exists_mem_det_eq_of_descent hBT hlevB hstep haB havB hvneg hpB hpmax
    (fun z hz => hub z (hBT hz)) (le_trans hmy (hub y hy))

end Descent

/-! ## §10  The tower induction, and what is left of `hconv`

Putting §9 together with `RegionSweep.isLatticeConvexRegion_sweep` (`RegionSweep.lean:213`)
reduces `hconv` — lattice convexity of every tower level — to hypotheses that all live on the
**seed** `B` and on the arithmetic of the chain directions.  Nothing below mentions convexity
of a tower level, so the induction never has to re-establish it.

After `isLatticeConvexRegion_tower_of_seed` the only outstanding input is
`hlevB : ∀ k, LevelInterval B (wt k)` — `lane-tower-hlev`'s concavity argument, instantiated at
the chain direction `wt k` instead of at `vl`.  Its two face hypotheses are available for every
`k` because `henv` gives `E B = E ↑d.Sphi` and `E ↑d.Sphi` is closed under negation, so both
faces normal to `±genPerp' (d.h k)` are `Nontrivial` edges parallel to `wt k`.

原文 `b3_colle2.txt:806-820`. -/

section TowerInduction

/-- `+v`-closure propagates up the tower: each sweep only adds translates. -/
theorem add_mem_tower_of_seed {R₀ : Set (ℤ × ℤ)} {wt : ℕ → ℤ × ℤ} {v : ℤ × ℤ}
    (h : ∀ z ∈ R₀, z + v ∈ R₀) (n : ℕ) :
    ∀ z ∈ tower R₀ wt n, z + v ∈ tower R₀ wt n := by
  induction n with
  | zero => exact h
  | succ k ih =>
      rintro z ⟨g, hg, t, rfl⟩
      exact ⟨g + v, ih g hg, t, by abel⟩

/-- A `det w`-upper bound propagates up the tower, provided every building direction **that is
actually used** does not increase the level.

The bound `k < n` is load-bearing, not cosmetic: on the candidate chain `det_pos_extChain`
gives `det (wtower n) (wtower k) < 0` exactly for `k < n` and the *opposite* sign for `k > n`,
so an unbounded `∀ k` here would be unsatisfiable. -/
theorem det_le_of_mem_tower {R₀ : Set (ℤ × ℤ)} {wt : ℕ → ℤ × ℤ} {w : ℤ × ℤ} {L : ℤ}
    (hR₀ : ∀ z ∈ R₀, det w z ≤ L) :
    ∀ (n : ℕ), (∀ k, k < n → det w (wt k) ≤ 0) → ∀ z ∈ tower R₀ wt n, det w z ≤ L := by
  intro n
  induction n with
  | zero => intro _; exact hR₀
  | succ k ih =>
      intro hneg
      rintro z ⟨g, hg, t, rfl⟩
      rw [det_add_zsmul_right]
      have h1 : (t : ℤ) * det w (wt k) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg t) (hneg k (by omega))
      linarith [ih (fun j hj => hneg j (by omega)) g hg]

/-- The `det w`-maximum of the seed cone is attained on `B`, when both ray directions descend. -/
theorem det_le_of_mem_coneRegion {B : Set (ℤ × ℤ)} {vl u' w p : ℤ × ℤ}
    (hpmax : ∀ b ∈ B, det w b ≤ det w p)
    (hvl : det w vl ≤ 0) (hu' : det w u' ≤ 0) :
    ∀ z ∈ coneRegion B vl u', det w z ≤ det w p := by
  intro z hz
  rw [mem_coneRegion_iff] at hz
  obtain ⟨b, hb, s, t, rfl⟩ := hz
  have h1 : det w (b + (s : ℤ) • vl + (t : ℤ) • u')
      = det w b + (s : ℤ) * det w vl + (t : ℤ) * det w u' := by
    simp only [det, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  rw [h1]
  have h2 : (s : ℤ) * det w vl ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg s) hvl
  have h3 : (t : ℤ) * det w u' ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg t) hu'
  linarith [hpmax b hb]

/-- **The tower induction.**  One `isLatticeConvexRegion_sweep` per level; the only per-level
input is `LevelInterval` of that level in its own sweep direction. -/
theorem isLatticeConvexRegion_tower_of_levelInterval {R₀ : Set (ℤ × ℤ)} {wt : ℕ → ℤ × ℤ}
    (hR₀ : IsLatticeConvexRegion R₀)
    (hwprim : ∀ k, Primitive (wt k))
    (hlev : ∀ k, LevelInterval (tower R₀ wt k) (wt k)) :
    ∀ n, IsLatticeConvexRegion (tower R₀ wt n) := by
  intro n
  induction n with
  | zero => exact hR₀
  | succ k ih => exact isLatticeConvexRegion_sweep ih (hwprim k) (hlev k)

/-- The bounded form of `isLatticeConvexRegion_tower_of_levelInterval`: only the levels
strictly below `N` need a `LevelInterval`, and only the levels up to `N` are concluded convex.

This is the form the chain actually admits.  At `wt := wtower d nℓ vl u' i` the sign
hypotheses of `isLatticeConvexRegion_tower_of_seed` are **unsatisfiable** without a bound,
because past the candidate list `wtower = -vl` and `det (-vl) vl = 0`
(`lane-tower-hlev`, 2026-09-23).  The unbounded chain statement is reached instead by
`levelInterval_tower_wtower`, which handles the `-vl` tail on its own. -/
theorem isLatticeConvexRegion_tower_of_levelInterval_le {R₀ : Set (ℤ × ℤ)} {wt : ℕ → ℤ × ℤ}
    {N : ℕ}
    (hR₀ : IsLatticeConvexRegion R₀)
    (hwprim : ∀ k, k < N → Primitive (wt k))
    (hlev : ∀ k, k < N → LevelInterval (tower R₀ wt k) (wt k)) :
    ∀ n, n ≤ N → IsLatticeConvexRegion (tower R₀ wt n) := by
  intro n
  induction n with
  | zero => intro _; exact hR₀
  | succ k ih =>
      intro hk
      exact isLatticeConvexRegion_sweep (ih (by omega)) (hwprim k (by omega))
        (hlev k (by omega))

/-- **The seed-only `LevelInterval` for one tower level, in an arbitrary level normal `w`.**

`w` is *not* tied to the sweep direction here, which is what makes the two orientations of
`det u' vl = ±1` interchangeable downstream: the chain direction `wt n` and its negative give
the same `LevelInterval` (`levelInterval_of_neg`), but only one of them descends along `vl`. -/
theorem levelInterval_tower_of_seed {B : Set (ℤ × ℤ)} {wt : ℕ → ℤ × ℤ} {vl u' w : ℤ × ℤ}
    (n : ℕ)
    (hvlneg : det w vl < 0)
    (hu'neg : det w u' ≤ 0)
    (hwneg : ∀ k, k < n → det w (wt k) ≤ 0)
    (hstepB : ∃ a ∈ B, a + vl ∈ B)
    (hargmax : ∃ p ∈ B, ∀ b ∈ B, det w b ≤ det w p)
    (hlevB : LevelInterval B w) :
    LevelInterval (tower (coneRegion B vl u') wt n) w := by
  obtain ⟨a, haB, havB⟩ := hstepB
  obtain ⟨p, hpB, hpmax⟩ := hargmax
  have hBcone : B ⊆ coneRegion B vl u' := by
    intro b hb
    rw [mem_coneRegion_iff]
    exact ⟨b, hb, 0, 0, by simp⟩
  have hBT : B ⊆ tower (coneRegion B vl u') wt n :=
    hBcone.trans (tower_monotone _ _ (Nat.zero_le n))
  refine levelInterval_of_descent hBT hlevB
    (add_mem_tower_of_seed (fun z hz => ConeRegion.add_vl_mem hz) n)
    haB havB hvlneg hpB rfl ?_
  exact det_le_of_mem_tower
    (det_le_of_mem_coneRegion hpmax hvlneg.le hu'neg) n hwneg

/-- The tail-of-chain companion to `levelInterval_tower_of_seed`: when the sweep direction is
unimodular against `u'`, the tower level's `LevelInterval` is free.  Used where
`wtower … n = -vl`, since `det (-vl) u' = det u' vl = ±1`. -/
theorem levelInterval_tower_unit {B : Set (ℤ × ℤ)} {wt : ℕ → ℤ × ℤ} {vl u' : ℤ × ℤ}
    (n : ℕ) (hdet : det (wt n) u' = 1 ∨ det (wt n) u' = -1) :
    LevelInterval (tower (coneRegion B vl u') wt n) (wt n) :=
  levelInterval_of_unit_step
    (add_mem_tower_of_seed (fun _ hz => ConeRegion.add_u'_mem hz) n) hdet

/-- **`hconv` reduced to the seed**, in the orientation where the chain directions descend
along `vl` (`det (wt n) vl < 0`, i.e. `det u' vl = -1`).  Given only:

* `hR₀` — the seed cone is lattice convex (`lane-tower-hlev`'s `n = 0` result);
* `hwprim` — the chain directions are primitive (`prim_of_mem_candSet`, plus `-vl`);
* `hvlneg`/`hu'neg`/`hwneg` — every chain direction, `vl` and `u'` has `det (wt n) · ≤ 0`,
  strictly for `vl` (`det_wtower_vl_mul_u'_pos` for `vl`/`u'`, `det_pos_extChain` for the
  earlier steps);
* `hstepB` — one `vl`-step inside `B` (the seed's `vl`-parallel edge, `hdoth`);
* `hargmax` — the `det (wt n)`-argmax of `B`;
* `hlevB` — `LevelInterval B (wt n)`, the only genuinely geometric input, and the one
  `lane-tower-hlev` is producing.

⚠ **Every hypothesis is bounded by `N`, and so is the conclusion.**  An unbounded `∀ n` here
would be unsatisfiable at `wt := wtower d nℓ vl u' i`: past the candidate list
`wtower = -vl`, so `det (wt n) vl = 0` and `det (wt n) u' = det u' vl = ±1`
(`lane-tower-hlev`, 2026-09-23).  `N := (sortedCand d nℓ u' i).length` is the intended
instance; the `-vl` tail is covered separately by `levelInterval_tower_unit`, and the two are
glued in `levelInterval_tower_wtower`.

No hypothesis is about a tower level.  For the opposite orientation use
`isLatticeConvexRegion_tower_of_seed_pos`. -/
theorem isLatticeConvexRegion_tower_of_seed {B : Set (ℤ × ℤ)} {wt : ℕ → ℤ × ℤ} {vl u' : ℤ × ℤ}
    {N : ℕ}
    (hR₀ : IsLatticeConvexRegion (coneRegion B vl u'))
    (hwprim : ∀ k, k < N → Primitive (wt k))
    (hvlneg : ∀ n, n < N → det (wt n) vl < 0)
    (hu'neg : ∀ n, n < N → det (wt n) u' ≤ 0)
    (hwneg : ∀ n, n < N → ∀ k, k < n → det (wt n) (wt k) ≤ 0)
    (hstepB : ∃ a ∈ B, a + vl ∈ B)
    (hargmax : ∀ n, n < N → ∃ p ∈ B, ∀ b ∈ B, det (wt n) b ≤ det (wt n) p)
    (hlevB : ∀ n, n < N → LevelInterval B (wt n)) :
    ∀ n, n ≤ N → IsLatticeConvexRegion (tower (coneRegion B vl u') wt n) :=
  isLatticeConvexRegion_tower_of_levelInterval_le hR₀ hwprim (fun n hn =>
    levelInterval_tower_of_seed n (hvlneg n hn) (hu'neg n hn) (hwneg n hn) hstepB
      (hargmax n hn) (hlevB n hn))

/-- **`hconv` reduced to the seed**, in the orientation `det u' vl = 1`, where every
`det (wt n) ·` inequality is reversed.  The level normal used internally is `-(wt n)`, and
`levelInterval_of_neg` turns the result back into the sweep direction that
`isLatticeConvexRegion_sweep` wants.  Bounded by `N` for the same reason as
`isLatticeConvexRegion_tower_of_seed`. -/
theorem isLatticeConvexRegion_tower_of_seed_pos {B : Set (ℤ × ℤ)} {wt : ℕ → ℤ × ℤ}
    {vl u' : ℤ × ℤ} {N : ℕ}
    (hR₀ : IsLatticeConvexRegion (coneRegion B vl u'))
    (hwprim : ∀ k, k < N → Primitive (wt k))
    (hvlpos : ∀ n, n < N → 0 < det (wt n) vl)
    (hu'pos : ∀ n, n < N → 0 ≤ det (wt n) u')
    (hwpos : ∀ n, n < N → ∀ k, k < n → 0 ≤ det (wt n) (wt k))
    (hstepB : ∃ a ∈ B, a + vl ∈ B)
    (hargmin : ∀ n, n < N → ∃ p ∈ B, ∀ b ∈ B, det (wt n) p ≤ det (wt n) b)
    (hlevB : ∀ n, n < N → LevelInterval B (wt n)) :
    ∀ n, n ≤ N → IsLatticeConvexRegion (tower (coneRegion B vl u') wt n) := by
  refine isLatticeConvexRegion_tower_of_levelInterval_le hR₀ hwprim (fun n hn => ?_)
  refine levelInterval_of_neg (levelInterval_tower_of_seed (w := -(wt n)) n ?_ ?_ ?_ hstepB
    ?_ (levelInterval_neg (hlevB n hn)))
  · rw [det_neg_left']; linarith [hvlpos n hn]
  · rw [det_neg_left']; linarith [hu'pos n hn]
  · intro k hk; rw [det_neg_left']; linarith [hwpos n hn k hk]
  · obtain ⟨p, hpB, hpmin⟩ := hargmin n hn
    exact ⟨p, hpB, fun b hb => by rw [det_neg_left', det_neg_left']; linarith [hpmin b hb]⟩

end TowerInduction

/-! ## §11  The chain signs, discharged

§10's arithmetic hypotheses, instantiated at the actual candidate chain.  Everything here is
in the orientation `det u' vl = -1`; the other orientation is
`isLatticeConvexRegion_tower_of_seed_pos` and flips every inequality.

The one identity that does the work is `det_vl_cramer_nl`: with `dot nℓ vl = 0`, the two
quantities `det u' vl * dot nℓ w` and `det w vl * dot nℓ u'` coincide for every `w`.  Since
every chain direction has `dot nℓ · < 0` (`dot_of_mem_candSet`, `TowerConstruct.lean:287`) and
so does `u'`, the sign of `det w vl` is pinned by the unit `det u' vl`. -/

section ChainSigns

open Nivat.Colle35 Nivat.ColleReg

variable {ξ : Nivat.Config ℤ}

/-- **Cramer against `nℓ`.**  A polynomial identity modulo `dot nℓ vl = 0`; the coefficient of
`hperp` is `det u' w`. -/
theorem det_vl_cramer_nl (vl nℓ u' w : ℤ × ℤ) (hperp : dot nℓ vl = 0) :
    det u' vl * dot nℓ w = det w vl * dot nℓ u' := by
  simp only [det, dot] at hperp ⊢
  linear_combination (u'.1 * w.2 - u'.2 * w.1) * hperp

/-- In the orientation `det u' vl = -1`, every direction strictly below `nℓ` descends against
`vl`.  This is §10's `hvlneg`. -/
theorem det_vl_neg_of_unimod_neg {vl nℓ u' w : ℤ × ℤ} (hperp : dot nℓ vl = 0)
    (hE : det u' vl = -1) (hnw : dot nℓ w < 0) (hnu : dot nℓ u' < 0) :
    det w vl < 0 := by
  have h := det_vl_cramer_nl vl nℓ u' w hperp
  rw [hE] at h
  by_contra hc
  push_neg at hc
  nlinarith [mul_nonneg hc (le_of_lt (neg_pos.mpr hnu))]

/-- The mirror of `det_vl_neg_of_unimod_neg` in the orientation `det u' vl = 1`. -/
theorem det_vl_pos_of_unimod_pos {vl nℓ u' w : ℤ × ℤ} (hperp : dot nℓ vl = 0)
    (hE : det u' vl = 1) (hnw : dot nℓ w < 0) (hnu : dot nℓ u' < 0) :
    0 < det w vl := by
  have h := det_vl_cramer_nl vl nℓ u' w hperp
  rw [hE] at h
  by_contra hc
  push_neg at hc
  nlinarith [mul_nonneg (neg_nonneg.mpr hc) (le_of_lt (neg_pos.mpr hnu))]

/-- §10's `hvlneg`, at the chain: every candidate direction descends against `vl`. -/
theorem det_wtower_vl_neg (d : DecompData ξ) {vl nℓ u' : ℤ × ℤ}
    (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0)
    (hE : det u' vl = -1) (hnu : dot nℓ u' < 0)
    {t : ℕ} (ht : t < (sortedCand d nℓ u' i).length) :
    det (wtower d nℓ vl u' i t) vl < 0 :=
  det_vl_neg_of_unimod_neg hperp hE
    (dot_of_mem_candSet d hvl_prim hprim hperp i hdoth (mem_candSet_wtower ht)) hnu

/-- The mirror of `det_wtower_vl_neg` in the orientation `det u' vl = 1`. -/
theorem det_wtower_vl_pos (d : DecompData ξ) {vl nℓ u' : ℤ × ℤ}
    (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0)
    (hE : det u' vl = 1) (hnu : dot nℓ u' < 0)
    {t : ℕ} (ht : t < (sortedCand d nℓ u' i).length) :
    0 < det (wtower d nℓ vl u' i t) vl :=
  det_vl_pos_of_unimod_pos hperp hE
    (dot_of_mem_candSet d hvl_prim hprim hperp i hdoth (mem_candSet_wtower ht)) hnu

/-- §10's `hwneg`, at the chain: an earlier chain direction sits on the negative side of a
later one.  This is `det_pos_extChain` read at `(j, k) = (k + 1, n + 1)`, with the unit
`det u' (-vl) = 1` supplied by `hE`. -/
theorem det_wtower_prev_neg {B : Set (ℤ × ℤ)} (d : DecompData ξ) {vl nℓ u' : ℤ × ℤ}
    (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (henv : Nivat.LE2.EnvOf (↑d.Sphi : Set (ℤ × ℤ)) B)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0)
    (hadjB : ∀ nn ∈ E B, ¬ (dot nn vl < 0 ∧ 0 < dot nn u'))
    (hE : det u' vl = -1) (hnu : dot nℓ u' < 0) (hnℓ_ne : nℓ ≠ 0)
    {n k : ℕ} (hkn : k < n) (hn : n < (sortedCand d nℓ u' i).length) :
    det (wtower d nℓ vl u' i n) (wtower d nℓ vl u' i k) < 0 := by
  have hkey := det_pos_extChain d hvl_prim hprim hperp henv i hdoth hadjB (Or.inr hE) hnu
    hnℓ_ne (j := k + 1) (k := n + 1) (by omega) (by omega)
  have he1 : extChain d nℓ vl u' i (k + 1) = wtower d nℓ vl u' i k := rfl
  have he2 : extChain d nℓ vl u' i (n + 1) = wtower d nℓ vl u' i n := rfl
  rw [he1, he2] at hkey
  have hunit : det u' (-vl) = 1 := by
    simp only [det, Prod.fst_neg, Prod.snd_neg] at hE ⊢
    linarith
  rw [hunit, mul_one] at hkey
  have hskew : det (wtower d nℓ vl u' i n) (wtower d nℓ vl u' i k)
      = - det (wtower d nℓ vl u' i k) (wtower d nℓ vl u' i n) := by
    simp only [det]; ring
  omega

end ChainSigns

/-! ## §12  `hconv` on the actual chain: everything except the two geometric inputs

§10 instantiated at `wt := wtower d nℓ vl u' i`, in the orientation `det u' vl = -1`.  Every
arithmetic binder of §10 is discharged here from `TowerConstruct.lean`'s own lemmas, and the
two branches of the chain are handled separately:

* `n < (sortedCand …).length` — a genuine candidate direction, `det (wt n) vl < 0`, so §9's
  descent applies and the geometric input `LevelInterval B (wt n)` is needed;
* `n ≥ length` — `wtower_last` makes it `-vl`, `det (-vl) u' = det u' vl = -1`, and
  `levelInterval_of_unit_step` gives the level interval for free.

What remains after this section is exactly two hypotheses, both `lane-tower-hlev`'s:
`hR₀ : IsLatticeConvexRegion (coneRegion B vl u')` and `hlevB` below. -/

section ChainConv

open Nivat.Colle35 Nivat.ColleReg

variable {ξ : Nivat.Config ℤ}

/-- Past the candidate list the chain is constantly `-vl`. -/
theorem wtower_of_le (d : DecompData ξ) (nℓ vl u' : ℤ × ℤ) (i : Fin d.m) {k : ℕ}
    (hk : (sortedCand d nℓ u' i).length ≤ k) :
    wtower d nℓ vl u' i k = -vl := by
  unfold wtower
  rw [dif_neg (by omega)]

/-- §10's `hwprim` at the chain: candidates are primitive, and so is the trailing `-vl`. -/
theorem prim_wtower (d : DecompData ξ) {vl nℓ u' : ℤ × ℤ}
    (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0) (k : ℕ) :
    Primitive (wtower d nℓ vl u' i k) := by
  by_cases hk : k < (sortedCand d nℓ u' i).length
  · exact prim_of_mem_candSet d hvl_prim hprim hperp i hdoth (mem_candSet_wtower hk)
  · rw [wtower_of_le d nℓ vl u' i (by omega)]
    obtain ⟨a, b, hab⟩ := hvl_prim
    exact ⟨-a, -b, by simp only [Prod.fst_neg, Prod.snd_neg]; linear_combination hab⟩

/-- §10's `hu'neg` at the chain, for a genuine candidate: `det (wt t) u' < 0`.  Combines
`det_wtower_vl_mul_u'_pos` (§6, the product is positive) with `det_wtower_vl_neg` (§11, the
`vl` factor is negative). -/
theorem det_wtower_u'_neg {B : Set (ℤ × ℤ)} (d : DecompData ξ) {vl nℓ u' : ℤ × ℤ}
    (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (henv : Nivat.LE2.EnvOf (↑d.Sphi : Set (ℤ × ℤ)) B)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0)
    (hadjB : ∀ nn ∈ E B, ¬ (dot nn vl < 0 ∧ 0 < dot nn u'))
    (hE : det u' vl = -1) (hnu : dot nℓ u' < 0) (hnℓ_ne : nℓ ≠ 0)
    {t : ℕ} (ht : t < (sortedCand d nℓ u' i).length) :
    det (wtower d nℓ vl u' i t) u' < 0 := by
  have hpos := det_wtower_vl_mul_u'_pos d hvl_prim hprim hperp henv i hdoth hadjB
    (Or.inr hE) hnu hnℓ_ne ht
  have hneg := det_wtower_vl_neg d hvl_prim hprim hperp i hdoth hE hnu ht
  nlinarith [hpos, hneg]

/-- **The per-level `LevelInterval` for the actual chain.**  The only input that is not
arithmetic is `hlevB`, and it is only needed for `n < length`. -/
theorem levelInterval_tower_wtower {B : Set (ℤ × ℤ)} (d : DecompData ξ) {vl nℓ u' : ℤ × ℤ}
    (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (henv : Nivat.LE2.EnvOf (↑d.Sphi : Set (ℤ × ℤ)) B)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0)
    (hadjB : ∀ nn ∈ E B, ¬ (dot nn vl < 0 ∧ 0 < dot nn u'))
    (hE : det u' vl = -1) (hnu : dot nℓ u' < 0) (hnℓ_ne : nℓ ≠ 0)
    (hBfin : B.Finite) (hBne : B.Nonempty)
    (hstepB : ∃ a ∈ B, a + vl ∈ B)
    (hlevB : ∀ n, n < (sortedCand d nℓ u' i).length →
      LevelInterval B (wtower d nℓ vl u' i n))
    (n : ℕ) :
    LevelInterval (tower (coneRegion B vl u') (wtower d nℓ vl u' i) n)
      (wtower d nℓ vl u' i n) := by
  by_cases hn : n < (sortedCand d nℓ u' i).length
  · refine levelInterval_tower_of_seed n
      (det_wtower_vl_neg d hvl_prim hprim hperp i hdoth hE hnu hn)
      (det_wtower_u'_neg d hvl_prim hprim hperp henv i hdoth hadjB hE hnu hnℓ_ne hn).le
      (fun k hk => (det_wtower_prev_neg d hvl_prim hprim hperp henv i hdoth hadjB hE hnu
        hnℓ_ne hk hn).le)
      hstepB ?_ (hlevB n hn)
    exact B.exists_max_image (det (wtower d nℓ vl u' i n)) hBfin hBne
  · refine levelInterval_tower_unit n (Or.inr ?_)
    rw [wtower_of_le d nℓ vl u' i (by omega)]
    simp only [det, Prod.fst_neg, Prod.snd_neg] at hE ⊢
    linarith

/-- **`hconv` on the actual chain.**  Only `hR₀` is not discharged here; it is
`lane-tower-hlev`'s `n = 0` result, and `hlevB` is its concavity argument at the chain
direction.  Everything else comes from `TowerConstruct.lean` plus §9–§11. -/
theorem isLatticeConvexRegion_tower_wtower {B : Set (ℤ × ℤ)} (d : DecompData ξ)
    {vl nℓ u' : ℤ × ℤ}
    (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (henv : Nivat.LE2.EnvOf (↑d.Sphi : Set (ℤ × ℤ)) B)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0)
    (hadjB : ∀ nn ∈ E B, ¬ (dot nn vl < 0 ∧ 0 < dot nn u'))
    (hE : det u' vl = -1) (hnu : dot nℓ u' < 0) (hnℓ_ne : nℓ ≠ 0)
    (hBfin : B.Finite) (hBne : B.Nonempty)
    (hstepB : ∃ a ∈ B, a + vl ∈ B)
    (hR₀ : IsLatticeConvexRegion (coneRegion B vl u'))
    (hlevB : ∀ n, n < (sortedCand d nℓ u' i).length →
      LevelInterval B (wtower d nℓ vl u' i n)) :
    ∀ n, IsLatticeConvexRegion (tower (coneRegion B vl u') (wtower d nℓ vl u' i) n) :=
  isLatticeConvexRegion_tower_of_levelInterval hR₀
    (prim_wtower d hvl_prim hprim hperp i hdoth)
    (levelInterval_tower_wtower d hvl_prim hprim hperp henv i hdoth hadjB hE hnu hnℓ_ne
      hBfin hBne hstepB hlevB)

/-- The mirror of `det_wtower_vl_neg` / `det_wtower_u'_neg` / `det_wtower_prev_neg` in the
orientation `det u' vl = 1`, where `towerIdx` reads `sortedCand` backwards and every
`det (wt n) ·` inequality flips. -/
theorem det_wtower_u'_pos {B : Set (ℤ × ℤ)} (d : DecompData ξ) {vl nℓ u' : ℤ × ℤ}
    (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (henv : Nivat.LE2.EnvOf (↑d.Sphi : Set (ℤ × ℤ)) B)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0)
    (hadjB : ∀ nn ∈ E B, ¬ (dot nn vl < 0 ∧ 0 < dot nn u'))
    (hE : det u' vl = 1) (hnu : dot nℓ u' < 0) (hnℓ_ne : nℓ ≠ 0)
    {t : ℕ} (ht : t < (sortedCand d nℓ u' i).length) :
    0 < det (wtower d nℓ vl u' i t) u' := by
  have hpos := det_wtower_vl_mul_u'_pos d hvl_prim hprim hperp henv i hdoth hadjB
    (Or.inl hE) hnu hnℓ_ne ht
  have hvlpos := det_wtower_vl_pos d hvl_prim hprim hperp i hdoth hE hnu ht
  nlinarith [hpos, hvlpos]

/-- The mirror of `det_wtower_prev_neg` in the orientation `det u' vl = 1`. -/
theorem det_wtower_prev_pos {B : Set (ℤ × ℤ)} (d : DecompData ξ) {vl nℓ u' : ℤ × ℤ}
    (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (henv : Nivat.LE2.EnvOf (↑d.Sphi : Set (ℤ × ℤ)) B)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0)
    (hadjB : ∀ nn ∈ E B, ¬ (dot nn vl < 0 ∧ 0 < dot nn u'))
    (hE : det u' vl = 1) (hnu : dot nℓ u' < 0) (hnℓ_ne : nℓ ≠ 0)
    {n k : ℕ} (hkn : k < n) (hn : n < (sortedCand d nℓ u' i).length) :
    0 < det (wtower d nℓ vl u' i n) (wtower d nℓ vl u' i k) := by
  have hkey := det_pos_extChain d hvl_prim hprim hperp henv i hdoth hadjB (Or.inl hE) hnu
    hnℓ_ne (j := k + 1) (k := n + 1) (by omega) (by omega)
  have he1 : extChain d nℓ vl u' i (k + 1) = wtower d nℓ vl u' i k := rfl
  have he2 : extChain d nℓ vl u' i (n + 1) = wtower d nℓ vl u' i n := rfl
  rw [he1, he2] at hkey
  have hunit : det u' (-vl) = -1 := by
    simp only [det, Prod.fst_neg, Prod.snd_neg] at hE ⊢
    linarith
  rw [hunit] at hkey
  have hskew : det (wtower d nℓ vl u' i n) (wtower d nℓ vl u' i k)
      = - det (wtower d nℓ vl u' i k) (wtower d nℓ vl u' i n) := by
    simp only [det]; ring
  nlinarith [hkey, hskew]

/-- **`hconv` on the actual chain, orientation `det u' vl = 1`.**  Same content as
`isLatticeConvexRegion_tower_wtower`, routed through
`isLatticeConvexRegion_tower_of_seed_pos`.  Together the two cover `hunimod`. -/
theorem isLatticeConvexRegion_tower_wtower_pos {B : Set (ℤ × ℤ)} (d : DecompData ξ)
    {vl nℓ u' : ℤ × ℤ}
    (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (henv : Nivat.LE2.EnvOf (↑d.Sphi : Set (ℤ × ℤ)) B)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0)
    (hadjB : ∀ nn ∈ E B, ¬ (dot nn vl < 0 ∧ 0 < dot nn u'))
    (hE : det u' vl = 1) (hnu : dot nℓ u' < 0) (hnℓ_ne : nℓ ≠ 0)
    (hBfin : B.Finite) (hBne : B.Nonempty)
    (hstepB : ∃ a ∈ B, a + vl ∈ B)
    (hR₀ : IsLatticeConvexRegion (coneRegion B vl u'))
    (hlevB : ∀ n, n < (sortedCand d nℓ u' i).length →
      LevelInterval B (wtower d nℓ vl u' i n)) :
    ∀ n, IsLatticeConvexRegion (tower (coneRegion B vl u') (wtower d nℓ vl u' i) n) := by
  refine isLatticeConvexRegion_tower_of_levelInterval hR₀
    (prim_wtower d hvl_prim hprim hperp i hdoth) (fun n => ?_)
  by_cases hn : n < (sortedCand d nℓ u' i).length
  · refine levelInterval_of_neg (levelInterval_tower_of_seed
      (w := -(wtower d nℓ vl u' i n)) n ?_ ?_ ?_ hstepB ?_
      (levelInterval_neg (hlevB n hn)))
    · rw [det_neg_left']
      have := det_wtower_vl_pos d hvl_prim hprim hperp i hdoth hE hnu hn
      linarith
    · rw [det_neg_left']
      have := det_wtower_u'_pos d hvl_prim hprim hperp henv i hdoth hadjB hE hnu hnℓ_ne hn
      linarith
    · intro k hk
      rw [det_neg_left']
      have := det_wtower_prev_pos d hvl_prim hprim hperp henv i hdoth hadjB hE hnu hnℓ_ne hk hn
      linarith
    · obtain ⟨p, hpB, hpmin⟩ :=
        B.exists_min_image (det (wtower d nℓ vl u' i n)) hBfin hBne
      exact ⟨p, hpB, fun b hb => by
        rw [det_neg_left', det_neg_left']; linarith [hpmin b hb]⟩
  · refine levelInterval_tower_unit n (Or.inl ?_)
    rw [wtower_of_le d nℓ vl u' i (by omega)]
    simp only [det, Prod.fst_neg, Prod.snd_neg] at hE ⊢
    linarith

end ChainConv

/-! ## §13  The wiring: `hcut` from the two geometric inputs

`hcut_tower` (§4) consumes `hconv` in exactly the shape §12 produces it, so the two compose
into a single statement whose only non-arithmetic hypotheses are `lane-tower-hlev`'s
`hR₀` and `hlevB`.  Both orientations of `hunimod` are handled internally.

When `lane-tower-hlev` lands its two lemmas, `lane-towerpkg` can call this instead of
`hcut_tower` and drop the `hconv` binder entirely. -/

section Wiring

open Nivat.Colle35 Nivat.ColleReg

variable {ξ : Nivat.Config ℤ}

/-- **`hcut` with `hconv` discharged.**  Conclusion identical to `hcut_tower`; the `hconv`
binder is replaced by `hR₀` + `hlevB` (both about the seed `B` only) plus the chain data that
`lane-towerpkg` already carries. -/
theorem hcut_tower_of_seed {B : Set (ℤ × ℤ)} (d : DecompData ξ) {vl nℓ u' : ℤ × ℤ}
    (hBfin : B.Finite) (hBne : B.Nonempty)
    (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (henv : Nivat.LE2.EnvOf (↑d.Sphi : Set (ℤ × ℤ)) B)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0)
    (hadjB : ∀ nn ∈ E B, ¬ (dot nn vl < 0 ∧ 0 < dot nn u'))
    (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hnu : dot nℓ u' = -1) (hnℓ_ne : nℓ ≠ 0)
    (hstepB : ∃ a ∈ B, a + vl ∈ B)
    (hR₀ : IsLatticeConvexRegion (coneRegion B vl u'))
    (hlevB : ∀ n, n < (sortedCand d nℓ u' i).length →
      LevelInterval B (wtower d nℓ vl u' i n))
    (hstepAll : ∀ I : ℕ, I ≤ (sortedCand d nℓ u' i).length →
      dot (expNormal (extChain d nℓ vl u' i I) vl) (wtower d nℓ vl u' i I) < 0) :
    ∀ I : ℕ, I ≤ (sortedCand d nℓ u' i).length → ∀ b₀ : ℤ,
      (∀ b ∈ B, dot (expNormal (extChain d nℓ vl u' i I) vl) b ≤ b₀) →
      ∀ z ∈ tower (coneRegion B vl u') (wtower d nℓ vl u' i) (I + 1),
        b₀ ≤ dot (expNormal (extChain d nℓ vl u' i I) vl) z →
        z ∈ tower (coneRegion B vl u') (wtower d nℓ vl u' i) I := by
  have hnu' : dot nℓ u' < 0 := by omega
  have hconv : ∀ n : ℕ, n ≤ (sortedCand d nℓ u' i).length + 1 →
      IsLatticeConvexRegion (tower (coneRegion B vl u') (wtower d nℓ vl u' i) n) := by
    intro n _
    rcases hunimod with hE | hE
    · exact isLatticeConvexRegion_tower_wtower_pos d hvl_prim hprim hperp henv i hdoth hadjB
        hE hnu' hnℓ_ne hBfin hBne hstepB hR₀ hlevB n
    · exact isLatticeConvexRegion_tower_wtower d hvl_prim hprim hperp henv i hdoth hadjB
        hE hnu' hnℓ_ne hBfin hBne hstepB hR₀ hlevB n
  exact hcut_tower d hBfin hBne hvl_prim hprim hperp i hdoth hnu hconv hstepAll

end Wiring

/-! ## §14  The chain signs, ε-normalised and unbounded

`lane-towerpkg`'s `dom_tower` / `dom_tower_max` (`tmp/wip/lane-towerpkg-tower-dom.lean`) want
the three `det`-signs of a tower direction against `vl`, `u'` and the earlier directions, with
**no bound on the index** — their induction runs over the whole tower.  §11–§12 prove those
signs only for genuine candidates (`n < (sortedCand d nℓ u' i).length`), because past that
point `wtower = -vl` and the strict inequalities fail: `det (-vl) vl = 0` and
`det (-vl) u' = det u' vl = ε`.

Multiplying through by `ε := det u' vl` repairs exactly this.  The tail contributes `0` in the
`vl` slot, `ε² = 1` in the `u'` slot, and `ε · det (wt j) vl` in the earlier-direction slot —
all non-negative.  So the ε-normalised statements hold for **every** `n`, and the two
orientations of `hunimod` are a single statement.

`dets_wtower_nonneg` / `dets_wtower_nonpos` are the two per-orientation packages,
matching `dom_tower` and `dom_tower_max` binder for binder. -/

section EpsSigns

open Nivat.Colle35 Nivat.ColleReg

variable {ξ : Nivat.Config ℤ}

/-- **`lane-towerpkg`'s obligation (1)**, ε-normalised: `0 ≤ ε * det (wt n) vl` for every `n`.
For `n < length` this is `det_wtower_vl_pos` / `det_wtower_vl_neg`; past the list
`wtower = -vl` and the product is exactly `0`. -/
theorem eps_det_wtower_vl_nonneg (d : DecompData ξ) {vl nℓ u' : ℤ × ℤ}
    (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0)
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) (hnu : dot nℓ u' < 0) (n : ℕ) :
    0 ≤ det u' vl * det (wtower d nℓ vl u' i n) vl := by
  by_cases hn : n < (sortedCand d nℓ u' i).length
  · rcases hunimod with hE | hE
    · have := det_wtower_vl_pos d hvl_prim hprim hperp i hdoth hE hnu hn
      rw [hE]; linarith
    · have := det_wtower_vl_neg d hvl_prim hprim hperp i hdoth hE hnu hn
      rw [hE]; linarith
  · rw [wtower_of_le d nℓ vl u' i (by omega)]
    have hz : det (-vl) vl = 0 := by simp only [det, Prod.fst_neg, Prod.snd_neg]; ring
    rw [hz, mul_zero]

/-- **`lane-towerpkg`'s obligation (2)**, ε-normalised: `0 ≤ ε * det (wt n) u'` for every `n`.
The tail gives `ε * ε`, a square. -/
theorem eps_det_wtower_u'_nonneg {B : Set (ℤ × ℤ)} (d : DecompData ξ) {vl nℓ u' : ℤ × ℤ}
    (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (henv : Nivat.LE2.EnvOf (↑d.Sphi : Set (ℤ × ℤ)) B)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0)
    (hadjB : ∀ nn ∈ E B, ¬ (dot nn vl < 0 ∧ 0 < dot nn u'))
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) (hnu : dot nℓ u' < 0) (hnℓ_ne : nℓ ≠ 0)
    (n : ℕ) :
    0 ≤ det u' vl * det (wtower d nℓ vl u' i n) u' := by
  by_cases hn : n < (sortedCand d nℓ u' i).length
  · rcases hunimod with hE | hE
    · have := det_wtower_u'_pos d hvl_prim hprim hperp henv i hdoth hadjB hE hnu hnℓ_ne hn
      rw [hE]; linarith
    · have := det_wtower_u'_neg d hvl_prim hprim hperp henv i hdoth hadjB hE hnu hnℓ_ne hn
      rw [hE]; linarith
  · rw [wtower_of_le d nℓ vl u' i (by omega)]
    have hswap : det (-vl) u' = det u' vl := by
      simp only [det, Prod.fst_neg, Prod.snd_neg]; ring
    rw [hswap]
    exact mul_self_nonneg _

/-- **`lane-towerpkg`'s obligation (3)**, ε-normalised:
`0 ≤ ε * det (wt n) (wt j)` for every `j < n`.  For `n < length` this is
`det_wtower_prev_pos` / `det_wtower_prev_neg`; for the tail `det (-vl) (wt j) = det (wt j) vl`,
so it reduces to obligation (1) at the index `j`. -/
theorem eps_det_wtower_prev_nonneg {B : Set (ℤ × ℤ)} (d : DecompData ξ) {vl nℓ u' : ℤ × ℤ}
    (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (henv : Nivat.LE2.EnvOf (↑d.Sphi : Set (ℤ × ℤ)) B)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0)
    (hadjB : ∀ nn ∈ E B, ¬ (dot nn vl < 0 ∧ 0 < dot nn u'))
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) (hnu : dot nℓ u' < 0) (hnℓ_ne : nℓ ≠ 0)
    {n j : ℕ} (hjn : j < n) :
    0 ≤ det u' vl * det (wtower d nℓ vl u' i n) (wtower d nℓ vl u' i j) := by
  by_cases hn : n < (sortedCand d nℓ u' i).length
  · rcases hunimod with hE | hE
    · have := det_wtower_prev_pos d hvl_prim hprim hperp henv i hdoth hadjB hE hnu hnℓ_ne
        hjn hn
      rw [hE]; linarith
    · have := det_wtower_prev_neg d hvl_prim hprim hperp henv i hdoth hadjB hE hnu hnℓ_ne
        hjn hn
      rw [hE]; linarith
  · rw [wtower_of_le d nℓ vl u' i (k := n) (by omega)]
    have hswap : det (-vl) (wtower d nℓ vl u' i j) = det (wtower d nℓ vl u' i j) vl := by
      simp only [det, Prod.fst_neg, Prod.snd_neg]; ring
    rw [hswap]
    exact eps_det_wtower_vl_nonneg d hvl_prim hprim hperp i hdoth hunimod hnu j

/-- **The three obligations at once, orientation `det u' vl = 1`.**  This is exactly the
premise triple of `lane-towerpkg`'s `dom_tower`, with no bound on `n`. -/
theorem dets_wtower_nonneg {B : Set (ℤ × ℤ)} (d : DecompData ξ) {vl nℓ u' : ℤ × ℤ}
    (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (henv : Nivat.LE2.EnvOf (↑d.Sphi : Set (ℤ × ℤ)) B)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0)
    (hadjB : ∀ nn ∈ E B, ¬ (dot nn vl < 0 ∧ 0 < dot nn u'))
    (hE : det u' vl = 1) (hnu : dot nℓ u' < 0) (hnℓ_ne : nℓ ≠ 0) (n : ℕ) :
    0 ≤ det (wtower d nℓ vl u' i n) vl ∧ 0 ≤ det (wtower d nℓ vl u' i n) u' ∧
      ∀ j, j < n → 0 ≤ det (wtower d nℓ vl u' i n) (wtower d nℓ vl u' i j) := by
  refine ⟨?_, ?_, fun j hj => ?_⟩
  · have := eps_det_wtower_vl_nonneg d hvl_prim hprim hperp i hdoth (Or.inl hE) hnu n
    rw [hE] at this; linarith
  · have := eps_det_wtower_u'_nonneg d hvl_prim hprim hperp henv i hdoth hadjB (Or.inl hE)
      hnu hnℓ_ne n
    rw [hE] at this; linarith
  · have := eps_det_wtower_prev_nonneg d hvl_prim hprim hperp henv i hdoth hadjB (Or.inl hE)
      hnu hnℓ_ne hj
    rw [hE] at this; linarith

/-- **The three obligations at once, orientation `det u' vl = -1`.**  This is exactly the
premise triple of `lane-towerpkg`'s `dom_tower_max`, with no bound on `n`. -/
theorem dets_wtower_nonpos {B : Set (ℤ × ℤ)} (d : DecompData ξ) {vl nℓ u' : ℤ × ℤ}
    (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (henv : Nivat.LE2.EnvOf (↑d.Sphi : Set (ℤ × ℤ)) B)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0)
    (hadjB : ∀ nn ∈ E B, ¬ (dot nn vl < 0 ∧ 0 < dot nn u'))
    (hE : det u' vl = -1) (hnu : dot nℓ u' < 0) (hnℓ_ne : nℓ ≠ 0) (n : ℕ) :
    det (wtower d nℓ vl u' i n) vl ≤ 0 ∧ det (wtower d nℓ vl u' i n) u' ≤ 0 ∧
      ∀ j, j < n → det (wtower d nℓ vl u' i n) (wtower d nℓ vl u' i j) ≤ 0 := by
  refine ⟨?_, ?_, fun j hj => ?_⟩
  · have := eps_det_wtower_vl_nonneg d hvl_prim hprim hperp i hdoth (Or.inr hE) hnu n
    rw [hE] at this; linarith
  · have := eps_det_wtower_u'_nonneg d hvl_prim hprim hperp henv i hdoth hadjB (Or.inr hE)
      hnu hnℓ_ne n
    rw [hE] at this; linarith
  · have := eps_det_wtower_prev_nonneg d hvl_prim hprim hperp henv i hdoth hadjB (Or.inr hE)
      hnu hnℓ_ne hj
    rw [hE] at this; linarith

end EpsSigns

/-! ## §15  `hcut` with **no** geometric binder left

`lane-tower-hlev` landed `Nivat/External/Colle/TowerGenBridge.lean` (2026-09-23), which pays
the three seed-side hypotheses of §12–§13 straight from `henv`:

| §13 binder | producer in `TowerGenBridge` |
|---|---|
| `hR₀ : IsLatticeConvexRegion (coneRegion B vl u')` | `LaneTowerHlevGen.latticeConvex_coneRegion_of_envOf` (`:264`) |
| `hstepB : ∃ a ∈ B, a + vl ∈ B` | `LaneTowerHlevGen.exists_vl_step` (`:213`) |
| `hlevB : LevelInterval B (wtower …)` | `LaneTowerHlevGen.levelInterval_wtower` (`:231`) |

All three consume only `henv`, `hvl_prim`, `hprim`, `hperp`, `i`, `hdoth` (and `hunimod` for
the first), every one of which is already on the consumer's binder list
(`RegionSteps.lean:1711-1730`).  So the statements below add **no** hypothesis to what the
tower package already carries.

⚠ `levelInterval_wtower` is uniform in `k` with no upper bound; §12 only needs
`k < (sortedCand d nℓ u' i).length`, so the bound is discarded.  Its `u'` is an **explicit**
argument sitting before `k`. -/

section EnvWiring

open Nivat.Colle35 Nivat.ColleReg

variable {ξ : Nivat.Config ℤ}

/-- **`hconv` from `henv` alone.**  `isLatticeConvexRegion_tower_wtower` (`det u' vl = -1`) and
`…_pos` (`det u' vl = 1`) with `hR₀` / `hstepB` / `hlevB` discharged, and the two orientations
merged back into `hunimod`.

原文 `b3_colle2.txt:806-820`: the 6th conjunct of the tower package, `IsRegion 𝓡^N_I`. -/
theorem isLatticeConvexRegion_tower_wtower_of_envOf {B : Set (ℤ × ℤ)} (d : DecompData ξ)
    {vl nℓ u' : ℤ × ℤ}
    (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (henv : Nivat.LE2.EnvOf (↑d.Sphi : Set (ℤ × ℤ)) B)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0)
    (hadjB : ∀ nn ∈ E B, ¬ (dot nn vl < 0 ∧ 0 < dot nn u'))
    (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hnu : dot nℓ u' < 0) (hnℓ_ne : nℓ ≠ 0)
    (hBfin : B.Finite) (hBne : B.Nonempty) :
    ∀ n, IsLatticeConvexRegion (tower (coneRegion B vl u') (wtower d nℓ vl u' i) n) := by
  have hR₀ : IsLatticeConvexRegion (coneRegion B vl u') :=
    Nivat.LaneTowerHlevGen.latticeConvex_coneRegion_of_envOf d henv hvl_prim hprim hperp i
      hdoth hunimod
  have hstepB : ∃ a ∈ B, a + vl ∈ B :=
    Nivat.LaneTowerHlevGen.exists_vl_step d henv hvl_prim hprim hperp i hdoth
  have hlevB : ∀ n, n < (sortedCand d nℓ u' i).length →
      LevelInterval B (wtower d nℓ vl u' i n) := fun n _ =>
    Nivat.LaneTowerHlevGen.levelInterval_wtower d henv hvl_prim hprim hperp i hdoth u' n
  rcases hunimod with hE | hE
  · exact isLatticeConvexRegion_tower_wtower_pos d hvl_prim hprim hperp henv i hdoth hadjB
      hE hnu hnℓ_ne hBfin hBne hstepB hR₀ hlevB
  · exact isLatticeConvexRegion_tower_wtower d hvl_prim hprim hperp henv i hdoth hadjB
      hE hnu hnℓ_ne hBfin hBne hstepB hR₀ hlevB

/-- **`hcut`, with `hconv` discharged from `henv`.**  Conclusion character for character that
of `hcut_tower` (`:637`); the `hconv` binder is gone and nothing replaces it.

`hstepAll` is the only remaining hypothesis that is not a consumer binder, and
`lane-towerpkg` discharges it in one line from its own `dot_m_step_neg`. -/
theorem hcut_tower_of_envOf {B : Set (ℤ × ℤ)} (d : DecompData ξ) {vl nℓ u' : ℤ × ℤ}
    (hBfin : B.Finite) (hBne : B.Nonempty)
    (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (henv : Nivat.LE2.EnvOf (↑d.Sphi : Set (ℤ × ℤ)) B)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0)
    (hadjB : ∀ nn ∈ E B, ¬ (dot nn vl < 0 ∧ 0 < dot nn u'))
    (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hnu : dot nℓ u' = -1) (hnℓ_ne : nℓ ≠ 0)
    (hstepAll : ∀ I : ℕ, I ≤ (sortedCand d nℓ u' i).length →
      dot (expNormal (extChain d nℓ vl u' i I) vl) (wtower d nℓ vl u' i I) < 0) :
    ∀ I : ℕ, I ≤ (sortedCand d nℓ u' i).length → ∀ b₀ : ℤ,
      (∀ b ∈ B, dot (expNormal (extChain d nℓ vl u' i I) vl) b ≤ b₀) →
      ∀ z ∈ tower (coneRegion B vl u') (wtower d nℓ vl u' i) (I + 1),
        b₀ ≤ dot (expNormal (extChain d nℓ vl u' i I) vl) z →
        z ∈ tower (coneRegion B vl u') (wtower d nℓ vl u' i) I := by
  have hnu' : dot nℓ u' < 0 := by omega
  exact hcut_tower d hBfin hBne hvl_prim hprim hperp i hdoth hnu
    (fun n _ => isLatticeConvexRegion_tower_wtower_of_envOf d hvl_prim hprim hperp henv i
      hdoth hadjB hunimod hnu' hnℓ_ne hBfin hBne n)
    hstepAll

end EnvWiring





end Nivat.TowerHBaseMin

#print axioms Nivat.TowerHBaseMin.sweep_inter_halfPlaneGE_eq_of_min
#print axioms Nivat.TowerHBaseMin.cut_zero_eq
#print axioms Nivat.TowerHBaseMin.exists_base
#print axioms Nivat.TowerHBaseMin.dot_le_of_mem_tower
#print axioms Nivat.TowerHBaseMin.le_dot_of_mem_tower
#print axioms Nivat.TowerHBaseMin.ray_mem_tower_succ
#print axioms Nivat.TowerHBaseMin.exists_base_tower
#print axioms Nivat.TowerHBaseMin.dot_nprevOf_wtower_self
#print axioms Nivat.TowerHBaseMin.dot_nprevOf_wtower_succ_pos
#print axioms Nivat.TowerHBaseMin.cut_step_subset
#print axioms Nivat.TowerHBaseMin.cut_step_subset_of_cut
#print axioms Nivat.TowerHBaseMin.ray_mem_tower_extChain
#print axioms Nivat.TowerHBaseMin.cut_tower_step
#print axioms Nivat.TowerHBaseMin.cut_tower_step_of_cut
#print axioms Nivat.TowerHBaseMin.hcut_tower
#print axioms Nivat.TowerHBaseMin.hcut_tower_of_cut
#print axioms Nivat.TowerHBaseMin.dot_expNormal_eq_det_mul
#print axioms Nivat.TowerHBaseMin.dot_expNormal_vl_pos
#print axioms Nivat.TowerHBaseMin.dot_m_vl_pos
#print axioms Nivat.TowerHBaseMin.exists_dot_lt_of_sweep

#print axioms Nivat.TowerHBaseMin.det_dot_cramer
#print axioms Nivat.TowerHBaseMin.det_wtower_vl_mul_u'_pos
#print axioms Nivat.TowerHBaseMin.cramer_smul_pair
#print axioms Nivat.TowerHBaseMin.expNormal_basis_expand
#print axioms Nivat.TowerHBaseMin.coneRegion_inter_halfPlaneGE_eq_quadrant

#print axioms Nivat.TowerHBaseMin.exists_cone_decomp
#print axioms Nivat.TowerHBaseMin.mem_of_nsmul_step
#print axioms Nivat.TowerHBaseMin.mem_of_cone_of_residues

#print axioms Nivat.TowerHBaseMin.det_add_zsmul_right
#print axioms Nivat.TowerHBaseMin.exists_mem_det_eq_of_descent
#print axioms Nivat.TowerHBaseMin.levelInterval_of_descent

#print axioms Nivat.TowerHBaseMin.add_mem_tower_of_seed
#print axioms Nivat.TowerHBaseMin.det_le_of_mem_tower
#print axioms Nivat.TowerHBaseMin.det_le_of_mem_coneRegion
#print axioms Nivat.TowerHBaseMin.isLatticeConvexRegion_tower_of_levelInterval
#print axioms Nivat.TowerHBaseMin.det_neg_left'
#print axioms Nivat.TowerHBaseMin.levelInterval_of_neg
#print axioms Nivat.TowerHBaseMin.levelInterval_neg
#print axioms Nivat.TowerHBaseMin.levelInterval_of_unit_step
#print axioms Nivat.TowerHBaseMin.levelInterval_tower_unit
#print axioms Nivat.TowerHBaseMin.levelInterval_tower_of_seed
#print axioms Nivat.TowerHBaseMin.isLatticeConvexRegion_tower_of_seed
#print axioms Nivat.TowerHBaseMin.isLatticeConvexRegion_tower_of_seed_pos
#print axioms Nivat.TowerHBaseMin.det_vl_cramer_nl
#print axioms Nivat.TowerHBaseMin.det_vl_neg_of_unimod_neg
#print axioms Nivat.TowerHBaseMin.det_vl_pos_of_unimod_pos
#print axioms Nivat.TowerHBaseMin.det_wtower_vl_neg
#print axioms Nivat.TowerHBaseMin.det_wtower_vl_pos
#print axioms Nivat.TowerHBaseMin.det_wtower_prev_neg
#print axioms Nivat.TowerHBaseMin.wtower_of_le
#print axioms Nivat.TowerHBaseMin.prim_wtower
#print axioms Nivat.TowerHBaseMin.det_wtower_u'_neg
#print axioms Nivat.TowerHBaseMin.levelInterval_tower_wtower
#print axioms Nivat.TowerHBaseMin.isLatticeConvexRegion_tower_wtower
#print axioms Nivat.TowerHBaseMin.det_wtower_u'_pos
#print axioms Nivat.TowerHBaseMin.det_wtower_prev_pos
#print axioms Nivat.TowerHBaseMin.isLatticeConvexRegion_tower_wtower_pos
#print axioms Nivat.TowerHBaseMin.hcut_tower_of_seed
#print axioms Nivat.TowerHBaseMin.isLatticeConvexRegion_tower_of_levelInterval_le
#print axioms Nivat.TowerHBaseMin.eps_det_wtower_vl_nonneg
#print axioms Nivat.TowerHBaseMin.eps_det_wtower_u'_nonneg
#print axioms Nivat.TowerHBaseMin.eps_det_wtower_prev_nonneg
#print axioms Nivat.TowerHBaseMin.dets_wtower_nonneg
#print axioms Nivat.TowerHBaseMin.dets_wtower_nonpos
#print axioms Nivat.TowerHBaseMin.isLatticeConvexRegion_tower_wtower_of_envOf
#print axioms Nivat.TowerHBaseMin.hcut_tower_of_envOf
