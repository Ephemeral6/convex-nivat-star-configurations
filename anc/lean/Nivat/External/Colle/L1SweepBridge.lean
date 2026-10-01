/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.L1Claim
import Nivat.External.Colle.L1LevelSpan
import Nivat.External.Colle.L1Line0
import Nivat.External.Colle.HalfPlaneShells
import Nivat.External.Colle.L1StraddleMax
import Nivat.External.Colle.L1CoverWedge
import Nivat.External.Colle.MaxIndexProbe
import Nivat.External.Colle.HbaseFlatSeed
import Nivat.External.Colle.L1Base

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# `exists_wedgeResidualR`'s residual, counted

`Nivat.ColleReg.exists_wedgeResidualR` (`RegionSteps.lean:1114`) is one of the project's two
remaining `sorry`s.  Its goal is `Nonempty (L1Claim.WedgeResidualR ξ S vl)`.  This file discharges
**every binder of that goal that is discharge-able from `RegionSteps`' own hypotheses**, leaving
exactly two.

## Why this file exists (2026-09-19 22:xx, `OPEN.md #13` third revision)

The `hbase` / shear-compatibility programme (`OPEN.md #13`) was aimed at
`L1StraddleWedge.exists_L1MaxBResidual_of_corner`, whose `hcorner` binder is refuted at a fixed
`u'` (`HbaseVertexSeed.not_hcorner_of_zonoF_two_generators`) and therefore needs a shear.  That is
a real route and its counterexamples stand.  **It is not the only route.**

`Nivat.ColleReg.L1Claim.WedgeResidualR.ofSweep` (`L1Claim.lean:1064`) reaches the same goal with
**no `hbase` binder at all** — it discharges `hbase` internally through
`HbaseBridge.hbase_at_of_sweep_of_isGeneratingSet` together with
`L1CoverWedge.hK_of_coverEnum`.  Along that route `u'`, `B`, `D`, `a`, `e`, `v`, `c`, `ε` are all
*caller choices*, so no compatibility-across-a-shear question arises.

⚠ **This does not prove `hbase`.**  `hbase_at_of_sweep_of_isGeneratingSet` *reduces* it to
`hD + hwin + hK`; `hK` is discharged by `hK_of_coverEnum`, `hD` is discharged below, and the
content lands in `hwin`.  Nothing here removes an obligation — it relocates and names them.

## What is free, and where it comes from

| binder of `ofSweep` | discharged by |
|---|---|
| `hSgen : IsGeneratingSet ξ S` | already a hypothesis at `RegionSteps.lean:1102` |
| `hconv : IsLatticeConvexRegion (wedgeFull B vl u')` | `L1Data.isLatticeConvexRegion_wedgeFull_of_unimod'` — unconditional in `B` |
| `B`, `e := u`, `c`, `hD`, `c0` | `L1Line0.exists_hD_of_case1` applied to `hcase1`, with `D := halfStrip B vl` |
| `a`, `ha`, `hconvS` | `Colle.exists_vertex_of_generating` applied to `hSgen` |
| `hline` | `MaxIndexProbe.wiring_hline` applied to the `hbase` that HOLE 1 produces |
| `hξ`, `d` | already hypotheses at `RegionSteps.lean:1097` |
| `u'`, `b₀` | free choices; `ε := L1Line0.εOf u' vl` and `v` are *forced* by `wiring_hline` |

## What is left: two holes

`hwin` and `hcover` — carried as the single binder `holes` below so that the count is a kernel
fact rather than prose.

**`hline` is not a hole.**  HOLE 1 (`hwin`) already produces `hbase` at level `0` (that is the
step `ofSweep` performs internally; it is hoisted out of the proof below), and
`MaxIndexProbe.wiring_hline` (`Nivat.ColleReg.wiring_hline`) turns `hbase` at level `k` into
`hline` at every `N ≥ k`.  Its extra binders `hξ : IsMinimalCounterexample ξ` and
`d : DecompDataZ ξ` are free — `exists_wedgeResidualR` (`RegionSteps.lean:1097`) carries both.
So `hline` is a *consequence of* `hwin`, not an independent obligation.

`hcover` is **not** `hstraddle`: it is stated as Collé's Figure 11(B) cover
(`b3_colle2.txt:848-856`), because `L1StraddleMax.straddle_of_cover` (`:129`) converts it and its
only other binder — `hgen : GeneratesAt ξ S a` — is *also* free, being the third component of
`exists_vertex_of_generating`.  By `L1CoverWedge.overlap_diff_subset_lines` (`:125`) the part of
that containment not already present at level `N` lies on a single line.

## Two honest strengthenings (`PROTOCOL.md` §15)

1. **`hcover` is quantified over `v`.**  In the previous version `v` was a free choice of the
   caller.  It no longer is: `wiring_hline` *produces* the translate `v` (it is the placement its
   `exists_N₀_hmin_hattain` picks), so `hcover` must hold for whatever `v` comes back.  This is a
   strictly stronger ask than the pinned-`v` version, and it is the price of collapsing `hline`.
   Mitigating fact, already on the tree: `ColleReg.derivedQ_image_add` /
   `derivedQ_image_nonempty_iff` (`MaxIndexProbe.lean`) show `derivedQ ε u' (S.image (· + v))` is
   just `(derivedQ ε u' S).image (· + v)`, so the `v`-dependence is a translation, not a reshaping.
2. **`straddle_of_cover` is one-way.**  `hcover` is a priori at least as strong as the
   `hstraddle` it discharges.  Stating hole 2 this way is a bet that Figure 11(B) is the intended
   argument, not a proof that the two are equivalent.

⚠ **Neither hole has been removed.**  `sorries TOTAL` is unchanged, `sorryAx` is still in
`nivat_conjecture`'s closure, and this file is not yet imported by `RegionSteps.lean`.  What is
established is a kernel-checked count: *these two* obligations, at *this* data, suffice.

**No `sorry`, no project axiom.**  Every statement here is an implication whose unproven parts are
explicit binders (`PROTOCOL.md` §15).
-/

namespace Nivat.L1SweepBridge

open Nivat Nivat.LE2 Nivat.Colle Nivat.Colle41 Nivat.ColleReg

/-- **`exists_wedgeResidualR`'s goal, from `RegionSteps`' own hypotheses, modulo three holes.**

The hypothesis list is a subset of `exists_wedgeResidualR`'s binders (`RegionSteps.lean:1095-1113`)
together with a choice of `u'`, `ε`, `v` and the `holes` binder.  Nothing is assumed that is not
already in scope at the `sorry`.

The three holes are stated *for the data `hcase1` and `hSgen` actually hand out*, not for arbitrary
data: `holes` receives `B`, `u`, `c` and the vertex `a` as parameters and must produce a `b₀ ∈ B`
along with `hwin` and `hcover` at that data.  This is deliberate — it keeps the statement
honest about the fact that `B` is not ours to invent, it is `Case1`'s envelope.

⚠ `b₀ ∈ B` is part of `holes` rather than a separate hypothesis because `EnvOf` does **not** give
`↑Sphi ⊆ B` (`LatticeEdges.lean:624-629`: `Enveloped` constrains edge directions and face
cardinalities, not membership), so `B.Nonempty` does not follow from `Sphi.Nonempty`. -/
theorem wedgeResidualR_of_case1_holes
    {ξ xper : Config ℤ} {vl p : ℤ × ℤ} {S : Finset (ℤ × ℤ)}
    (hξ : IsMinimalCounterexample ξ) (d : Nivat.Colle35.DecompDataZ ξ)
    (hSgen : IsGeneratingSet ξ S)
    (hcase1 : Case1 ξ xper d.Sphi vl)
    (hvl_prim : Primitive vl) (hp_mem : p ∈ Per xper) (hp_ne : p ≠ 0)
    (hdet_vl : det p vl = 0)
    {u' : ℤ × ℤ} (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (holes : ∀ (B : Set (ℤ × ℤ)) (u : ℤ × ℤ) (c : ℤ) (a : ℤ × ℤ),
      a ∈ S → Nivat.LatticeConvex (S.erase a) → 0 < c →
      (∀ z ∈ halfStrip B vl, (T u ξ) z = T (c • vl) (T u ξ) z) →
      ∃ b₀ ∈ B,
        -- HOLE 1 (`hwin`): every punctured window translate along `coverEnum` lands in the
        -- half-strip seed, in an earlier row, or earlier in the current row.
        (∀ i j : ℕ, ∀ z ∈ S.erase a,
          z + (coverEnum vl u' b₀ i j - a) ∈
            halfStrip B vl ∪ (⋃ i' ∈ {i' | i' < i}, Set.range (coverEnum vl u' b₀ i')) ∪
              (coverEnum vl u' b₀ i '' {j' | j' < j})) ∧
        -- HOLE 2 (`hcover`): Collé's Figure 11(B) cover (`b3_colle2.txt:848-856`).
        -- ⚠ Quantified over `v` because the translate is no longer ours to pick: it is produced
        -- by `wiring_hline`'s placement argument.  See the module docstring.
        (∀ v : ℤ × ℤ, ∀ N : ℕ,
          PeriodOn (T u ξ) (chainFull B vl u' b₀ N) (c • vl) →
          ¬ PeriodOn (T u ξ) (chainFull B vl u' b₀ (N + 1)) (c • vl) →
          ∀ τ : ℤ,
            (∀ z ∈ L1Data.derivedQ (Nivat.L1Line0.εOf u' vl) u' (S.image (· + v)),
              τ • u' + z ∈ chainFull B vl u' b₀ N ∧
              τ • u' + z + c • vl ∈ chainFull B vl u' b₀ N) →
            ∀ g ∈ S.image (· + v), g ∉ L1Data.derivedQ (Nivat.L1Line0.εOf u' vl) u' (S.image (· + v)) →
              ∀ t₀ : ℤ, τ ≤ t₀ →
                Nivat.L1StraddleMax.overlap (chainFull B vl u' b₀ (N + 1)) (c • vl) ⊆
                  Nivat.MaxEnv.genClosure S a
                    (Nivat.L1StraddleMax.overlap (chainFull B vl u' b₀ N) (c • vl) ∪
                      Nivat.L1StraddleMax.ray g u' t₀))) :
    Nonempty (L1Claim.WedgeResidualR ξ S vl) := by
  -- `B`, `u`, `c` and `hD` all come out of `hcase1`; nothing new is assumed.
  obtain ⟨B, _hEnv, u, c, hc, _hper, _hu, hD⟩ :=
    Nivat.L1Line0.exists_hD_of_case1 hcase1 hvl_prim hp_mem hp_ne hdet_vl
  -- the vertex `a`, `LatticeConvex (S.erase a)` and `hgen` all come out of `hSgen`; also free.
  obtain ⟨a, ha, hconvS, hgen⟩ := Nivat.Colle.exists_vertex_of_generating hSgen
  obtain ⟨b₀, hb₀, hwin, hcover⟩ := holes B u c a ha hconvS hc hD
  -- **HOLE 1 already gives `hbase` at level 0** — this is exactly the step `ofSweep` performs
  -- internally, hoisted out so that `wiring_hline` can consume it.
  have hbase0 : PeriodOn (T u ξ) (chainFull B vl u' b₀ 0) (c • vl) :=
    Nivat.HbaseBridge.hbase_at_of_sweep_of_isGeneratingSet hSgen ha hconvS 0 hD
      (coverEnum vl u' b₀) hwin (hK_of_coverEnum hunimod)
  -- … and `hbase` at level 0 gives `hline` outright.  This is why there is no HOLE for `hline`.
  obtain ⟨_N₀, v, hline⟩ :=
    Nivat.ColleReg.wiring_hline hξ d hb₀ hunimod hc hvl_prim 0 hbase0 ⟨a, ha⟩
  refine ⟨L1Claim.WedgeResidualR.ofSweep (v := v) hSgen (Nivat.L1Line0.εOf u' vl) hb₀
    (Nivat.ColleReg.L1Data.isLatticeConvexRegion_wedgeFull_of_unimod' hunimod)
    hunimod hc.ne' ha hconvS hD hwin ?_ ?_⟩
  · intro N hN hN1
    have h := hline N (by simpa using hN) (by simpa using hN1)
    simpa only [Nat.zero_add] using h
  · -- HOLE 2 is delivered as Figure 11(B)'s cover; `straddle_of_cover` does the rest, and its
    -- `hgen` binder is the free third component of `exists_vertex_of_generating`.
    intro N hN hN1 τ hτ
    exact Nivat.L1StraddleMax.straddle_of_cover (Nivat.T_mem_orbitClosure ξ u) hgen
      (hcover v N hN hN1 τ hτ)

/-! ## Hole 2, opened up: `hcorner` + a placement fact

`wedgeResidualR_of_case1_holes` states hole 2 as Collé's Figure 11(B) cover — one containment,
opaque.  `MaxIndexProbe.wiring_hcover_of_corner` (`Nivat.ColleReg.wiring_hcover_of_corner`)
reduces that containment, unconditionally, to two much smaller named conditions:

* **`hcorner`** — `∀ b ∈ S, 0 ≤ dot (expNormal u' vl) (b - a) ∧ 0 ≤ uCoord u' vl a b`.
  Pure finite arithmetic on `S`; no configuration, no orbit, no chain.  This is exactly
  `OPEN.md #13`'s corner condition.
* **`place`** — at the level where periodicity first fails, the translate `S.image (· + v)` sits
  on or above `expLevel u' vl b₀ N - 1` and attains it.  This one *has* a producer:
  `MaxIndexProbe.exists_N₀_hmin_hattain`.

The theorem below is that substitution and nothing else.  `hwin` is untouched.

### What this does and does not buy

It does **not** discharge hole 2 — it renames it into two pieces, one of which is arithmetic and
one of which has a producer.  `sorries TOTAL` is unchanged (still 2), `sorryAx` is still in
`nivat_conjecture`'s closure, and `RegionSteps.lean` still does not import this file.

The reason it is worth landing is a structural fact about `u'` that is **not** recorded elsewhere
on the tree, and which the statement below makes checkable:

⚠ **`u'` is a free variable here.**  Both `wedgeResidualR_of_case1_holes` and the theorem below
bind `u'` with `hunimod` as its *only* constraint — nothing upstream (`hcase1`, `hSgen`, the
`B`/`u`/`c` handed out by `exists_hD_of_case1`) mentions it.  Consequently the shear
`u' ↦ u' - K • vl` is free along *this* route: `det_shear` keeps `hunimod`, `wedgeFull_shear`
keeps the wedge, and `MaxIndexProbe.exists_N₀_hmin_hattain_shear` already shows `place` needs zero
new code at the sheared direction.  The shear-compatibility question of `OPEN.md #13` is about
data stated at a *pre-existing* `u'`; it does not arise here.

⚠ **But the shear cannot rescue `hcorner` by itself, and the reason is the second conjunct.**
`uCoord u' vl a b = -(det u' vl) * det vl (b - a)` does not depend on `u'` beyond the sign
`det u' vl`, and `det (u' - K • vl) vl = det u' vl`; so `0 ≤ uCoord u' vl a b` is
**shear-invariant** — `exists_corner_shear`'s own proof (`L1StraddleWedge.lean:424` ff.) discharges
that conjunct at the *un-sheared* `u'` and transports it unchanged, which is the same observation.
Only the first conjunct moves with `K` (`dot_expNormal_shear`).  Hence `hcorner` is satisfiable at
some shear **iff `a` minimises `uCoord u' vl 0 ·` over `S`** — i.e. `a` is forced, up to the two
sign choices of `εOf`, to be an extreme point of `S` transverse to `vl`.

That is where hole 2 actually stands: not "is the shear compatible", but **"is there a vertex of
`S` that both generates and is `det vl`-extreme?"**

⚠ **And that vertex is *not* forced to be `ofSweep`'s `a`.**  `L1StraddleMax.straddle_of_cover`
(`:129`) binds its corner as `{a : ℤ × ℤ} (hgen : GeneratesAt ξ Sφ a)` and its **conclusion
`Straddle x Rlo Rhi S₁ Q u u' c τ` does not mention `a`** — the vertex is local to the cover.  So
the statement below takes the cover's vertex `a'` as a *separate* binder from the `a` that
`Colle.exists_vertex_of_generating` hands `ofSweep`.  Consequence: at `a'` only
`GeneratesAt ξ S a'` is needed — **`LatticeConvex (S.erase a')` is not**, that obligation stays
with `ofSweep`'s `a`.  Taking `a' := a` recovers the coupled form, so nothing is lost.

The open question is therefore narrower than `OPEN.md #13` recorded before this file: **does
`GeneratesAt ξ S a'` have a producer at a `det vl`-extreme `a'`, with no lattice-convexity
attached?** -/

/-- **`exists_wedgeResidualR`'s goal from `hwin` + `hcorner` + `place`.**  Same hypotheses as
`wedgeResidualR_of_case1_holes` with hole 2's cover replaced by the conditions
`wiring_hcover_of_corner` reduces it to.

`a'` is the **cover's** vertex and is independent of the `a` inside `holes` (which is whatever
`Colle.exists_vertex_of_generating` returns and carries the lattice-convexity that `ofSweep`
consumes).  At `a'` only `GeneratesAt` is required — see the section docstring. -/
theorem wedgeResidualR_of_hwin_corner_place
    {ξ xper : Config ℤ} {vl p : ℤ × ℤ} {S : Finset (ℤ × ℤ)}
    (hξ : IsMinimalCounterexample ξ) (d : Nivat.Colle35.DecompDataZ ξ)
    (hSgen : IsGeneratingSet ξ S)
    (hcase1 : Case1 ξ xper d.Sphi vl)
    (hvl_prim : Primitive vl) (hp_mem : p ∈ Per xper) (hp_ne : p ≠ 0)
    (hdet_vl : det p vl = 0)
    {u' : ℤ × ℤ} (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    -- the cover's vertex, decoupled from `ofSweep`'s: `GeneratesAt` only, no lattice convexity
    {a' : ℤ × ℤ} (hgen' : GeneratesAt ξ S a')
    (hcorner : ∀ b ∈ S, 0 ≤ dot (expNormal u' vl) (b - a') ∧
      0 ≤ Nivat.L1Line0.uCoord u' vl a' b)
    (holes : ∀ (B : Set (ℤ × ℤ)) (u : ℤ × ℤ) (c : ℤ) (a : ℤ × ℤ),
      a ∈ S → Nivat.LatticeConvex (S.erase a) → 0 < c →
      -- `B` is **finite**, and this is free: `Case1`'s own `B` field carries
      -- `EnvOf ↑d.Sphi B`, and `HbaseFlatSeed.finite_of_envOf_Sphi` turns that into finiteness.
      B.Finite →
      (∀ z ∈ halfStrip B vl, (T u ξ) z = T (c • vl) (T u ξ) z) →
      ∃ b₀ ∈ B,
        (∀ i j : ℕ, ∀ z ∈ S.erase a,
          z + (coverEnum vl u' b₀ i j - a) ∈
            halfStrip B vl ∪ (⋃ i' ∈ {i' | i' < i}, Set.range (coverEnum vl u' b₀ i')) ∪
              (coverEnum vl u' b₀ i '' {j' | j' < j})) ∧
        -- HOLE 2b (`place`): the placement fact, at whatever translate `wiring_hline` produces.
        -- (HOLE 2a, `hcorner`, is now a top-level binder at `a'`.)
        (∀ v : ℤ × ℤ, ∀ N : ℕ,
          PeriodOn (T u ξ) (chainFull B vl u' b₀ N) (c • vl) →
          ¬ PeriodOn (T u ξ) (chainFull B vl u' b₀ (N + 1)) (c • vl) →
          (∀ s ∈ S.image (· + v),
              expLevel u' vl b₀ N - 1 ≤ dot (expNormal u' vl) s) ∧
            (∃ s ∈ S.image (· + v),
              dot (expNormal u' vl) s = expLevel u' vl b₀ N - 1))) :
    Nonempty (L1Claim.WedgeResidualR ξ S vl) := by
  obtain ⟨B, hEnv, u, c, hc, _hper, _hu, hD⟩ :=
    Nivat.L1Line0.exists_hD_of_case1 hcase1 hvl_prim hp_mem hp_ne hdet_vl
  -- **`B` is finite, unconditionally.**  `Case1`'s `B` field carries `EnvOf ↑d.Sphi B`;
  -- `E ↑d.Sphi` has two non-parallel normals (`d.hm : 2 ≤ d.m`) and is closed under negation
  -- (`Sphi_negSymm`), each of which bounds `dot n` on `B` through its exposed face.
  have hBfin : B.Finite :=
    Nivat.HbaseFlatSeed.finite_of_envOf_Sphi d.toDecompData hEnv
  obtain ⟨a, ha, hconvS, _hgen⟩ := Nivat.Colle.exists_vertex_of_generating hSgen
  obtain ⟨b₀, hb₀, hwin, hplace⟩ := holes B u c a ha hconvS hc hBfin hD
  have hbase0 : PeriodOn (T u ξ) (chainFull B vl u' b₀ 0) (c • vl) :=
    Nivat.HbaseBridge.hbase_at_of_sweep_of_isGeneratingSet hSgen ha hconvS 0 hD
      (coverEnum vl u' b₀) hwin (hK_of_coverEnum hunimod)
  obtain ⟨_N₀, v, hline⟩ :=
    Nivat.ColleReg.wiring_hline hξ d hb₀ hunimod hc hvl_prim 0 hbase0 ⟨a, ha⟩
  refine ⟨L1Claim.WedgeResidualR.ofSweep (v := v) hSgen (Nivat.L1Line0.εOf u' vl) hb₀
    (Nivat.ColleReg.L1Data.isLatticeConvexRegion_wedgeFull_of_unimod' hunimod)
    hunimod hc.ne' ha hconvS hD hwin ?_ ?_⟩
  · intro N hN hN1
    have h := hline N (by simpa using hN) (by simpa using hN1)
    simpa only [Nat.zero_add] using h
  · intro N hN hN1 τ hτ
    obtain ⟨hmin, hattain⟩ := hplace v N hN hN1
    exact Nivat.L1StraddleMax.straddle_of_cover (Nivat.T_mem_orbitClosure ξ u) hgen'
      (Nivat.ColleReg.wiring_hcover_of_corner hunimod hc.le hcorner hmin hattain hN hN1 τ hτ)

/-! ## Hole 2 discharged: **`hwin` is the only hole left**

2026-09-19 23:1x.  Both halves of hole 2 turn out to have producers already on the tree; neither
needed new mathematics, only the observation that they are fed by *one* call to
`exists_N₀_hmin_hattain` rather than two independent asks.

* **`hcorner` (hole 2a)** — `L1StraddleWedge.exists_corner_shear` (`:424`) produces it for any
  nonempty finite set after a shear `u' ↦ u' - K•vl`, by an explicit lexicographic construction
  (`exists_min_image` on `uCoord`, filter to the tie set, `exists_min_image` on `expNormal`,
  `K := max M 0`).  Applied at `d.Sphi`, which is a generating set by
  `ColleReg.exists_Sφ` (`MaxIndexProbe.lean:214`).  The shear is harmless because `u'` is a
  *universally quantified* variable here whose only constraint is `hunimod`, preserved by
  `det_shear`; nothing is transported across the shear, so
  `HbaseVertexSeed.ChainFullShearUnbounded` (`:302`) does not apply.
* **`place` (hole 2b)** — was mis-stated in `wedgeResidualR_of_hwin_corner_place` as `∀ v, ∀ N`.
  That form is **too strong**: `hmin`/`hattain` pin `S.image (· + v)` to the single level
  `expLevel u' vl b₀ N - 1`, so one translate `v` cannot serve two different `N`, and no `v`
  serves an arbitrary one.  The correct shape is the one `ColleReg.wiring_hstraddle`
  (`MaxIndexProbe.lean:321`) already consumes: `hmin`/`hattain` at the *single* `N₀` that
  `exists_N₀_hmin_hattain` returns, from which `wiring_hstraddle` derives `hstraddle` at **every**
  `N` on its own.  The same call supplies `hline` through `hline_of_placement`, so the two are
  automatically at the same `(N₀, v)` — which is exactly the coupling the `∀ v` form was
  over-approximating.

⚠ `wedgeResidualR_of_hwin_corner_place` above is **kept** (`PROTOCOL.md` §14): it is correct as
stated — a stronger hypothesis is still a hypothesis — and it records the `∀ v` misreading. -/

/-- **`exists_wedgeResidualR`'s goal from `hwin` alone.**

Every binder of `WedgeResidualR.ofSweep` except `hwin` is discharged from `RegionSteps`' own
hypotheses.  `hwin` is stated at the sheared direction `u' - K • vl` and quantified over `K`,
because the shear `K` is chosen by `exists_corner_shear` from `d.Sphi` and is not ours to pin.

⚠ **This does not prove `hwin`.**  `sorries TOTAL` is unchanged and `RegionSteps.lean` does not
yet import this file.  What it establishes is a kernel-checked count: *one* obligation, at *this*
data, suffices for `exists_wedgeResidualR`.

⚠ **One strengthening, flagged rather than hidden** (`PROTOCOL.md` §15, and the same class of
error as the `∀ v` one corrected just above).  `hwin_hole` is quantified `∀ K`, because `K` is
produced by `exists_corner_shear` *inside* the proof and so cannot be named in a binder stated
before it.  That is strictly more than the proof consumes: it uses `hwin` at **one** `K`.

The difference from the `∀ v` mistake is that `∀ K` is **not** provably over-constrained: `v` was
pinned by an *equality* (`hattain` fixes the level exactly, so two `N` cannot share a `v`),
whereas `K` only selects a unimodular direction `u' - K • vl`, and Collé's window argument is
uniform in that direction.  **This is a reading, not a kernel fact** — no `#print axioms` output
backs it.  If a lane closes `hwin` only at a specific `K`, this statement must be restructured to
take `K` (and `hcorner` at that `K`) as binders; nothing else in the proof changes. -/
theorem wedgeResidualR_of_hwin
    {ξ xper : Config ℤ} {vl p : ℤ × ℤ} {S : Finset (ℤ × ℤ)}
    (hξ : IsMinimalCounterexample ξ) (d : Nivat.Colle35.DecompDataZ ξ)
    (hSgen : IsGeneratingSet ξ S)
    (hcase1 : Case1 ξ xper d.Sphi vl)
    (hvl_prim : Primitive vl) (hp_mem : p ∈ Per xper) (hp_ne : p ≠ 0)
    (hdet_vl : det p vl = 0)
    {u' : ℤ × ℤ} (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hwin_hole : ∀ (B : Set (ℤ × ℤ)) (u : ℤ × ℤ) (c : ℤ) (a : ℤ × ℤ) (K : ℤ),
      a ∈ S → Nivat.LatticeConvex (S.erase a) → 0 < c →
      B.Finite →
      -- `a` minimises `dot (expNormal (u' - K • vl) vl)` over `S`.  **Not decoration**: by
      -- `HbaseFlatSeed.dot_expNormal_coverEnum` every row of `coverEnum` lies at a single level
      -- `≥ dot (expNormal · vl) b₀`, so a `z ∈ S.erase a` strictly below `a` would push a whole
      -- translated row below every row's level, where only `halfStrip B vl` could catch it.
      (∀ b ∈ S, dot (expNormal (u' - K • vl) vl) a ≤ dot (expNormal (u' - K • vl) vl) b) →
      (∀ z ∈ halfStrip B vl, (T u ξ) z = T (c • vl) (T u ξ) z) →
      ∃ b₀ ∈ B,
        ∀ i j : ℕ, ∀ z ∈ S.erase a,
          z + (coverEnum vl (u' - K • vl) b₀ i j - a) ∈
            halfStrip B vl ∪
              (⋃ i' ∈ {i' | i' < i}, Set.range (coverEnum vl (u' - K • vl) b₀ i')) ∪
              (coverEnum vl (u' - K • vl) b₀ i '' {j' | j' < j})) :
    Nonempty (L1Claim.WedgeResidualR ξ S vl) := by
  obtain ⟨B, hEnv, u, c, hc, _hper, _hu, hD⟩ :=
    Nivat.L1Line0.exists_hD_of_case1 hcase1 hvl_prim hp_mem hp_ne hdet_vl
  have hBfin : B.Finite :=
    Nivat.HbaseFlatSeed.finite_of_envOf_Sphi d.toDecompData hEnv
  -- **hole 2a**: the corner, at `d.Sphi`, after a shear `K` produced by `exists_corner_shear`.
  obtain ⟨K, a₁, ha₁, hcorner⟩ :=
    Nivat.L1StraddleWedge.exists_corner_shear (u' := u') (vl := vl)
      (S := d.toDecompData.Sphi) (Nivat.ColleReg.exists_Sφ d).1
  have hunimod' : det (u' - K • vl) vl = 1 ∨ det (u' - K • vl) vl = -1 := by
    rw [Nivat.L1StraddleWedge.det_shear]; exact hunimod
  -- `ofSweep`'s vertex is chosen **in the sheared `expNormal` direction**, not arbitrarily:
  -- `exists_vertex_of_generating_dir` keeps `LatticeConvex (S.erase a)` while adding minimality.
  have hw0 : expNormal (u' - K • vl) vl ≠ 0 := by
    intro h
    have := Nivat.ColleReg.dot_expNormal_vl hunimod'
    rw [h] at this
    simp [Nivat.LE2.dot] at this
  obtain ⟨a, ha, hamin, hconvS, _hgen⟩ :=
    Nivat.ColleReg.exists_vertex_of_generating_dir hw0 hSgen
  obtain ⟨b₀, hb₀, hwin⟩ := hwin_hole B u c a K ha hconvS hc hBfin hamin hD
  have hbase0 : PeriodOn (T u ξ) (chainFull B vl (u' - K • vl) b₀ 0) (c • vl) :=
    Nivat.HbaseBridge.hbase_at_of_sweep_of_isGeneratingSet hSgen ha hconvS 0 hD
      (coverEnum vl (u' - K • vl) b₀) hwin (hK_of_coverEnum hunimod')
  -- **one** call, so `hline` and `hstraddle` are automatically at the same `(N₀, v)`.
  obtain ⟨N₀, v, hN₀, hN₀1, hmin, hattain⟩ :=
    Nivat.ColleReg.exists_N₀_hmin_hattain hξ d hb₀ hunimod' hc.ne' hvl_prim 0 hbase0 ⟨a, ha⟩
  refine ⟨L1Claim.WedgeResidualR.ofSweep (v := v) hSgen
    (Nivat.L1Line0.εOf (u' - K • vl) vl) hb₀
    (Nivat.ColleReg.L1Data.isLatticeConvexRegion_wedgeFull_of_unimod' hunimod')
    hunimod' hc.ne' ha hconvS hD hwin ?_ ?_⟩
  · intro N hN hN1
    have h := Nivat.L1Line0.hline_of_placement hb₀ hunimod' hc hN₀ hN₀1 hmin N
      (by simpa using hN) (by simpa using hN1)
    simpa only [Nat.zero_add] using h
  · intro N hN hN1 τ hτ
    have h := Nivat.ColleReg.wiring_hstraddle hunimod' hc.le hN₀ hN₀1 hmin hattain d ha₁ hcorner N
      (by simpa using hN) (by simpa using hN1) τ (by simpa using hτ)
    simpa only [Nat.zero_add] using h

/-! ## §4  Route 2 for `hbase`-at-0 (`L1Base.hbase_of_step`): the refutation, stated on the
object the binder actually mentions

Lstrad reported (2026-09-19 23:xx) that `L1Base.hbase_of_step`'s only instantiation,
`L1Base.hbase_of_copy_step` (`L1Base.lean:216`), is already refuted by
`Nivat.L1Prim.not_invariant_of_not_periodOn_smul` (`L1Prim.lean:613`).  **The citation does not
literally cover the binder**: that lemma refutes `c • v`-invariance of `halfPlaneGE n k`, whereas
`hbase_of_copy_step`'s `hinv` is `c • vl`-invariance of `cumSweep (band0 B vl u' b₀) u' t`.
Those are different sets — `cumSweep` of a band is not a half-plane — so accepting the verdict on
the citation alone would repeat the leaf-C mistake (`CLAUDE.md`: three refutations and one proof
can all be true because they are not the same proposition).

This section proves the refutation **on `cumSweep (band0 …) u' t` itself**.  The verdict stands,
and the mechanism is the one Lstrad described, but it is now a kernel fact rather than an
analogy.  The content is one line of unimodularity: `band0` is cut by `expNormal` at level
`expLevel u' vl b₀ 0`, the `u'`-sweep preserves that level (`dot_expNormal_u' = 0`), and `vl`
moves it by exactly one (`dot_expNormal_vl = 1`) — so a nonzero `c • vl` always pushes `b₀`
across the cut, in whichever direction the sign of `c` chooses. -/

open Nivat.L1Base in
/-- The `u'`-sweep of `band0` never drops below `band0`'s own cut level: `dot_expNormal_u' = 0`
means translating by `u'` is level-preserving. -/
theorem le_dot_expNormal_of_mem_cumSweep {B : Set (ℤ × ℤ)} {vl u' b₀ : ℤ × ℤ} {t : ℕ}
    {z : ℤ × ℤ} (hz : z ∈ cumSweep (band0 B vl u' b₀) u' t) :
    expLevel u' vl b₀ 0 ≤ dot (expNormal u' vl) z := by
  obtain ⟨g, hg, s, _hs, rfl⟩ := hz
  have hlev : expLevel u' vl b₀ 0 ≤ dot (expNormal u' vl) g := hg.2
  have hu : dot (expNormal u' vl) (g + (s : ℤ) • u') = dot (expNormal u' vl) g := by
    have h0 : dot (expNormal u' vl) u' = 0 := dot_expNormal_u'
    simp only [dot, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul] at h0 ⊢
    linear_combination (s : ℤ) * h0
  rw [hu]; exact hlev

open Nivat.L1Base in
/-- **Route 2's `hinv` is unsatisfiable for every `c ≠ 0`.**  Stated on `cumSweep (band0 …) u' t`
— the object `L1Base.hbase_of_copy_step`'s binder actually names — not on a half-plane.
Needs only `b₀ ∈ B` and unimodularity; no `hξ`, so this is not vacuous. -/
theorem not_hinv_cumSweep {B : Set (ℤ × ℤ)} {vl u' b₀ : ℤ × ℤ} {c : ℤ} (t : ℕ)
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) (hb₀ : b₀ ∈ B) (hc : c ≠ 0) :
    ¬ ∀ z : ℤ × ℤ, z + c • vl ∈ cumSweep (band0 B vl u' b₀) u' t ↔
        z ∈ cumSweep (band0 B vl u' b₀) u' t := by
  intro hinv
  have hshift : ∀ z : ℤ × ℤ,
      dot (expNormal u' vl) (z + c • vl) = dot (expNormal u' vl) z + c := by
    have hvl : dot (expNormal u' vl) vl = 1 := dot_expNormal_vl hunimod
    intro z
    simp only [dot, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul] at hvl ⊢
    linear_combination c * hvl
  have hb0band : b₀ ∈ band0 B vl u' b₀ := by
    refine ⟨mem_fullSweep_iff.mpr ⟨b₀, hb₀, 0, by simp⟩, ?_⟩
    show expLevel u' vl b₀ 0 ≤ dot (expNormal u' vl) b₀
    simp [expLevel]
  have hb0mem : b₀ ∈ cumSweep (band0 B vl u' b₀) u' t :=
    ⟨b₀, hb0band, 0, Nat.zero_le t, by simp⟩
  have hlev0 : expLevel u' vl b₀ 0 = dot (expNormal u' vl) b₀ := by simp [expLevel]
  rcases lt_or_gt_of_ne hc with hneg | hpos
  · -- `c < 0`: `b₀ + c • vl` sits one full `|c|` below the cut, yet `hinv` puts it in the sweep.
    have hle := le_dot_expNormal_of_mem_cumSweep ((hinv b₀).mpr hb0mem)
    rw [hshift, hlev0] at hle
    omega
  · -- `c > 0`: pull back instead — `hinv` forces the preimage `b₀ - c • vl` into the sweep.
    have hcancel : (b₀ - c • vl) + c • vl = b₀ := by abel
    have hmem : b₀ - c • vl ∈ cumSweep (band0 B vl u' b₀) u' t :=
      (hinv (b₀ - c • vl)).mp (by rw [hcancel]; exact hb0mem)
    have hle := le_dot_expNormal_of_mem_cumSweep hmem
    have h2 := hshift (b₀ - c • vl)
    rw [hcancel] at h2
    omega

/-! ## §5  The residual as a single named proposition, for wiring into `RegionSteps`

`wedgeResidualR_of_hwin` above takes `u'` as an implicit binder, but `exists_wedgeResidualR`
(`RegionSteps.lean:1096`) has no `u'` in scope — it only has `Primitive vl`.  Packaging the
residual as an **existential** over `u'` is what keeps the wiring honest: quantifying `∀ u'`
would be a strengthening (`PROTOCOL.md` §15), whereas `∃ u'` is exactly what the proof consumes,
because `u'` is chosen inside (`L1Assemble.exists_unimod_primitive_of_primitive`, and then
sheared by `exists_corner_shear`).  Nothing here is new mathematics; it is the `sorry`'s goal,
named. -/

/-- **`exists_wedgeResidualR`'s entire remaining content** (`OPEN.md #13`).  Everything else in
`WedgeResidualR` is discharged by `wedgeResidualR_of_hwin`. -/
def HwinHole (ξ : Config ℤ) (S : Finset (ℤ × ℤ)) (vl : ℤ × ℤ) : Prop :=
  ∃ u' : ℤ × ℤ, (det u' vl = 1 ∨ det u' vl = -1) ∧
    ∀ (B : Set (ℤ × ℤ)) (u : ℤ × ℤ) (c : ℤ) (a : ℤ × ℤ) (K : ℤ),
      a ∈ S → Nivat.LatticeConvex (S.erase a) → 0 < c →
      B.Finite →
      (∀ b ∈ S, dot (expNormal (u' - K • vl) vl) a ≤ dot (expNormal (u' - K • vl) vl) b) →
      (∀ z ∈ halfStrip B vl, (T u ξ) z = T (c • vl) (T u ξ) z) →
      ∃ b₀ ∈ B,
        ∀ i j : ℕ, ∀ z ∈ S.erase a,
          z + (coverEnum vl (u' - K • vl) b₀ i j - a) ∈
            halfStrip B vl ∪
              (⋃ i' ∈ {i' | i' < i}, Set.range (coverEnum vl (u' - K • vl) b₀ i')) ∪
              (coverEnum vl (u' - K • vl) b₀ i '' {j' | j' < j})

/-- **The wiring form.**  Same content as `wedgeResidualR_of_hwin`, with `u'` moved inside the
hypothesis so the binder list matches `exists_wedgeResidualR`'s exactly. **2026-09-20 — vacuous on the chain.**  `not_hwinHole_of_case1` (§23) refutes the hypothesis at
every Case 1 instance, inheriting it from §21 through `hwinHoleE_of_hwinHole`.  Do not attack
this rung: weakening along the `HwinHole -> HwinHoleE -> HwinHoleZ` axis is already exhausted.
The live successor is `HwinHoleK` (`HwinHoleK.lean`), which weakens a *different* quantifier. -/
theorem wedgeResidualR_of_hwinHole
    {ξ xper : Config ℤ} {vl p : ℤ × ℤ} {S : Finset (ℤ × ℤ)}
    (hξ : IsMinimalCounterexample ξ) (d : Nivat.Colle35.DecompDataZ ξ)
    (hSgen : IsGeneratingSet ξ S)
    (hcase1 : Case1 ξ xper d.Sphi vl)
    (hvl_prim : Primitive vl) (hp_mem : p ∈ Per xper) (hp_ne : p ≠ 0)
    (hdet_vl : det p vl = 0)
    (hhole : HwinHole ξ S vl) :
    Nonempty (L1Claim.WedgeResidualR ξ S vl) := by
  obtain ⟨u', hunimod, hwin⟩ := hhole
  exact wedgeResidualR_of_hwin hξ d hSgen hcase1 hvl_prim hp_mem hp_ne hdet_vl hunimod hwin

/-! ## §6  The enumeration is a free parameter — weakening the hole accordingly

`L1Claim.WedgeResidualR.ofSweep` (`L1Claim.lean:1064`) hard-wires the enumeration to `coverEnum`,
so `HwinHole` above inherits that choice.  **But the lemma `ofSweep` is built on does not**:
`HbaseBridge.hbase_at_of_sweep_of_isGeneratingSet` (`HbaseBridge.lean:185`) takes
`enum : ℕ → ℕ → ℤ × ℤ` as an ordinary parameter, with `hwin` and `hK` stated against it.
`coverEnum` is merely the one enumeration for which a ready-made `hK` existed
(`L1CoverWedge.hK_of_coverEnum`).

This matters for whether `hwin` is even **true**.  `coverEnum` is built on
`pairEnum := Denumerable.eqv ((ℤ×ℤ)×ℕ) |>.symm`, and `HbaseFlatSeed.dot_expNormal_coverEnum`
shows row `i` sits entirely at level `dot (expNormal u' vl) b₀ + (pairEnum i).2`.  Since
`pairEnum` is an arbitrary bijection, **row index order has no relation to level order** — so
"lands in an earlier row" (`⋃ i' < i`) is not "lands lower", and `hwin` is being asked to hold
against an essentially arbitrary ordering.  Leaving `enum` free removes that accident from the
statement of the hole.

`HwinHoleE` below is therefore **weaker** than `HwinHole` (`hwinHoleE_of_hwinHole` proves the
implication, with `coverEnum` as the witness), and it is the one wired into `RegionSteps`. -/

/-- `L1Claim.WedgeResidualR.ofSweep` with the enumeration left free **and the sweep window set
`Sw` separated from the residual's own `S`**.  Same field assignments; `hbase` differs by passing
`enum`/`hK` instead of `coverEnum`/`hK_of_coverEnum`.

⚠ **2026-09-20: `Sw` was identified with `S` and that identification was an accident.**
`HbaseBridge.hbase_at_of_sweep_of_isGeneratingSet` (`:185`) takes its generating set as a free
parameter, unrelated to `B`, `D`, `vl`, `u'`; nothing forced it to be the `S` of
`WedgeResidualR ξ S vl`, which enters this definition only through `hline`/`hstraddle`'s
`S.image (· + v)`.  Tying them made the sweep window Lemma 2.4's `𝒮` while the half-strip base
`B` envelops the zonotope `𝒮_φ` — two sets Collé never relates (`RegionSteps.lean:2318-2332`,
`DecompData.lean:113-124`).  See §15. -/
noncomputable def ofSweepEnum
    {ξ : Config ℤ} {S Sw : Finset (ℤ × ℤ)} {vl : ℤ × ℤ}
    (hSwgen : IsGeneratingSet ξ Sw)
    {e u' v b₀ : ℤ × ℤ} {c : ℤ} (ε : Bool) {B : Set (ℤ × ℤ)}
    (hb₀ : b₀ ∈ B) (hconv : IsLatticeConvexRegion (wedgeFull B vl u'))
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) (c0 : c ≠ 0)
    {a : ℤ × ℤ} (ha : a ∈ Sw) (hconvS : Nivat.LatticeConvex (Sw.erase a))
    {D : Set (ℤ × ℤ)} (hD : ∀ z ∈ D, (T e ξ) z = T (c • vl) (T e ξ) z)
    (enum : ℕ → ℕ → ℤ × ℤ)
    (hwin : ∀ i j : ℕ, ∀ z ∈ Sw.erase a,
      z + (enum i j - a) ∈
        D ∪ (⋃ i' ∈ {i' | i' < i}, Set.range (enum i')) ∪ (enum i '' {j' | j' < j}))
    (hK : chainFull B vl u' b₀ 0 ⊆ D ∪ (⋃ i, Set.range (enum i)))
    (hline : ∀ N : ℕ, PeriodOn (T e ξ) (chainFull B vl u' b₀ N) (c • vl) →
      ¬ PeriodOn (T e ξ) (chainFull B vl u' b₀ (N + 1)) (c • vl) →
      ∃ τ : ℤ, ∀ z ∈ L1Data.derivedQ ε u' (S.image (· + v)),
        τ • u' + z ∈ chainFull B vl u' b₀ N ∧
        τ • u' + z + c • vl ∈ chainFull B vl u' b₀ N)
    (hstraddle : ∀ N : ℕ, PeriodOn (T e ξ) (chainFull B vl u' b₀ N) (c • vl) →
      ¬ PeriodOn (T e ξ) (chainFull B vl u' b₀ (N + 1)) (c • vl) →
      ∀ τ : ℤ,
        (∀ z ∈ L1Data.derivedQ ε u' (S.image (· + v)),
          τ • u' + z ∈ chainFull B vl u' b₀ N ∧
          τ • u' + z + c • vl ∈ chainFull B vl u' b₀ N) →
        Nivat.L1Region.Straddle (T e ξ) (chainFull B vl u' b₀ N)
          (chainFull B vl u' b₀ (N + 1)) (S.image (· + v))
          (L1Data.derivedQ ε u' (S.image (· + v))) vl u' c τ) :
    L1Claim.WedgeResidualR ξ S vl where
  e := e
  u' := u'
  v := v
  b₀ := b₀
  c := c
  ε := ε
  B := B
  k := 0
  hb₀ := hb₀
  hunimod := hunimod
  c0 := c0
  hconv := hconv
  hbase :=
    Nivat.HbaseBridge.hbase_at_of_sweep_of_isGeneratingSet hSwgen ha hconvS 0 hD enum hwin hK
  hline := fun N hN hN1 => by
    simp only [Nat.zero_add] at hN hN1 ⊢
    exact hline N hN hN1
  hstraddle := fun N hN hN1 τ hl => by
    simp only [Nat.zero_add] at hN hN1 hl ⊢
    exact hstraddle N hN hN1 τ hl

/-- **`exists_wedgeResidualR`'s entire remaining content, with the enumeration free.**
Weaker than `HwinHole`; this is the proposition `RegionSteps.lean:1122` reduces to.

⚠ **2026-09-19, corrected: the `hEnv` binder is load-bearing and its first version omitted it.**
The first version of this definition constrained `B` by `B.Finite` alone.  That is *false*:
in `ℕ`, `{i' | i' < 0} = ∅` and `{j' | j' < 0} = ∅`, so at `i = j = 0` the `hwin` conjunct
collapses to "one single vector `enum 0 0 - a` translates all of `S.erase a` into
`halfStrip B vl`" — with the `∃ enum` contributing nothing, since no other value of `enum`
occurs.  As `halfStrip B vl = B + ℕ • vl` (`LatticeEdges.lean:1810`), a **singleton** `B`
makes that a single line parallel to `vl`, which no two `vl`-non-collinear points of
`S.erase a` can be translated into.  `B.Finite` permits singletons; `EnvOf ↑Sphi B` does not
(`Enveloped` forces `B` lattice-convex and at least as long as `Sphi` on every edge,
`LatticeEdges.lean:2433`).

The chain always supplies `hEnv`: `L1Line0.exists_hD_of_case1` (`L1Line0.lean:527`) returns
`EnvOf (↑d.Sphi) B` alongside `hD`, and `wedgeResidualR_of_hwinHoleE` below now passes it.
`B.Finite` is kept as a *separate* binder rather than derived, because the derivation
(`HbaseFlatSeed.finite_of_envOf_Sphi`) needs the `DecompData`, which this `Prop` does not carry.

⚠ Adding a hypothesis **weakens** this `Prop`; it does not make it true.  Whether the
`i = j = 0` obstruction survives under `EnvOf` is open and is the live question for leaf L1.

🔴 **2026-09-20: superseded — this `Prop` is refutable as stated, and §15 replaces it.**
`HbaseFlatSeed.envOf_holds_and_hwin_seed_refuted` (Hflat) exhibits `Sphi := B := {(0,0)}`
against `S := {(0,0),(1,0),(2,0)}`: a singleton is lattice-convex and reflexively enveloped, so
`EnvOf ↑Sphi B` holds outright while `B` stays exactly as small *relative to `S`* as it was
before the `EnvOf` fix.  The defect is that **nothing here ties `Sphi` to `S`**, and nothing in
the tree does either — Collé never identifies Lemma 2.4's `𝒮` with the zonotope `𝒮_φ`
(`RegionSteps.lean:2318-2332`; the `decomp.Sphi = S` field asserting it by fiat was deleted,
`DecompData.lean:113-124`).  Kept per the retraction discipline, not to be wired.
§15's `HwinHoleZ` closes the seam without needing such a lemma. -/
def HwinHoleE (ξ : Config ℤ) (S Sphi : Finset (ℤ × ℤ)) (vl : ℤ × ℤ) : Prop :=
  ∃ u' : ℤ × ℤ, (det u' vl = 1 ∨ det u' vl = -1) ∧
    ∀ (B : Set (ℤ × ℤ)) (u : ℤ × ℤ) (c : ℤ) (a : ℤ × ℤ) (K : ℤ),
      a ∈ S → Nivat.LatticeConvex (S.erase a) → 0 < c →
      B.Finite → EnvOf (Sphi : Set (ℤ × ℤ)) B →
      (∀ b ∈ S, dot (expNormal (u' - K • vl) vl) a ≤ dot (expNormal (u' - K • vl) vl) b) →
      (∀ z ∈ halfStrip B vl, (T u ξ) z = T (c • vl) (T u ξ) z) →
      ∃ b₀ ∈ B, ∃ enum : ℕ → ℕ → ℤ × ℤ,
        (∀ i j : ℕ, ∀ z ∈ S.erase a,
          z + (enum i j - a) ∈
            halfStrip B vl ∪ (⋃ i' ∈ {i' | i' < i}, Set.range (enum i')) ∪
              (enum i '' {j' | j' < j})) ∧
        chainFull B vl (u' - K • vl) b₀ 0 ⊆ halfStrip B vl ∪ (⋃ i, Set.range (enum i))

/-- `HwinHoleE` really is the weaker of the two: `coverEnum` is a witness, and its `hK`
is `L1CoverWedge.hK_of_coverEnum`.  (`hEnv` is simply discarded here — `HwinHole` proves the
conclusion without it, so the implication holds for every `Sphi`.) -/
theorem hwinHoleE_of_hwinHole {ξ : Config ℤ} {S Sphi : Finset (ℤ × ℤ)} {vl : ℤ × ℤ}
    (h : HwinHole ξ S vl) : HwinHoleE ξ S Sphi vl := by
  obtain ⟨u', hunimod, h⟩ := h
  refine ⟨u', hunimod, fun B u c a K ha hconvS hc hBfin _hEnv hamin hD => ?_⟩
  obtain ⟨b₀, hb₀, hwin⟩ := h B u c a K ha hconvS hc hBfin hamin hD
  have hunimod' : det (u' - K • vl) vl = 1 ∨ det (u' - K • vl) vl = -1 := by
    rw [Nivat.L1StraddleWedge.det_shear]; exact hunimod
  exact ⟨b₀, hb₀, coverEnum vl (u' - K • vl) b₀, hwin, hK_of_coverEnum hunimod'⟩

/-- **The wiring form, with the enumeration free.**  This is what `RegionSteps.lean:1122`
calls. **2026-09-20 — vacuous on the chain.**  `not_hwinHoleE_of_case1` (§23) refutes the hypothesis at
every Case 1 instance, inheriting it from §21 through `hwinHoleE_of_hwinHole`.  Do not attack
this rung: weakening along the `HwinHole -> HwinHoleE -> HwinHoleZ` axis is already exhausted.
The live successor is `HwinHoleK` (`HwinHoleK.lean`), which weakens a *different* quantifier. -/
theorem wedgeResidualR_of_hwinHoleE
    {ξ xper : Config ℤ} {vl p : ℤ × ℤ} {S : Finset (ℤ × ℤ)}
    (hξ : IsMinimalCounterexample ξ) (d : Nivat.Colle35.DecompDataZ ξ)
    (hSgen : IsGeneratingSet ξ S)
    (hcase1 : Case1 ξ xper d.Sphi vl)
    (hvl_prim : Primitive vl) (hp_mem : p ∈ Per xper) (hp_ne : p ≠ 0)
    (hdet_vl : det p vl = 0)
    (hhole : HwinHoleE ξ S d.Sphi vl) :
    Nonempty (L1Claim.WedgeResidualR ξ S vl) := by
  obtain ⟨u', hunimod, hhole⟩ := hhole
  obtain ⟨B, hEnv, u, c, hc, _hper, _hu, hD⟩ :=
    Nivat.L1Line0.exists_hD_of_case1 hcase1 hvl_prim hp_mem hp_ne hdet_vl
  have hBfin : B.Finite :=
    Nivat.HbaseFlatSeed.finite_of_envOf_Sphi d.toDecompData hEnv
  obtain ⟨K, a₁, ha₁, hcorner⟩ :=
    Nivat.L1StraddleWedge.exists_corner_shear (u' := u') (vl := vl)
      (S := d.toDecompData.Sphi) (Nivat.ColleReg.exists_Sφ d).1
  have hunimod' : det (u' - K • vl) vl = 1 ∨ det (u' - K • vl) vl = -1 := by
    rw [Nivat.L1StraddleWedge.det_shear]; exact hunimod
  have hw0 : expNormal (u' - K • vl) vl ≠ 0 := by
    intro h
    have := Nivat.ColleReg.dot_expNormal_vl hunimod'
    rw [h] at this
    simp [Nivat.LE2.dot] at this
  obtain ⟨a, ha, hamin, hconvS, _hgen⟩ :=
    Nivat.ColleReg.exists_vertex_of_generating_dir hw0 hSgen
  obtain ⟨b₀, hb₀, enum, hwin, hK⟩ := hhole B u c a K ha hconvS hc hBfin hEnv hamin hD
  have hbase0 : PeriodOn (T u ξ) (chainFull B vl (u' - K • vl) b₀ 0) (c • vl) :=
    Nivat.HbaseBridge.hbase_at_of_sweep_of_isGeneratingSet hSgen ha hconvS 0 hD enum hwin hK
  obtain ⟨N₀, v, hN₀, hN₀1, hmin, hattain⟩ :=
    Nivat.ColleReg.exists_N₀_hmin_hattain hξ d hb₀ hunimod' hc.ne' hvl_prim 0 hbase0 ⟨a, ha⟩
  refine ⟨ofSweepEnum (v := v) hSgen (Nivat.L1Line0.εOf (u' - K • vl) vl) hb₀
    (Nivat.ColleReg.L1Data.isLatticeConvexRegion_wedgeFull_of_unimod' hunimod')
    hunimod' hc.ne' ha hconvS hD enum hwin hK ?_ ?_⟩
  · intro N hN hN1
    have h := Nivat.L1Line0.hline_of_placement hb₀ hunimod' hc hN₀ hN₀1 hmin N
      (by simpa using hN) (by simpa using hN1)
    simpa only [Nat.zero_add] using h
  · intro N hN hN1 τ hτ
    have h := Nivat.ColleReg.wiring_hstraddle hunimod' hc.le hN₀ hN₀1 hmin hattain d ha₁ hcorner N
      (by simpa using hN) (by simpa using hN1) τ (by simpa using hτ)
    simpa only [Nat.zero_add] using h

/-! ## §14  The level-constant row obstruction — the first one `EnvOf` does **not** remove

§13's retraction (`HwinHoleE` gained the `EnvOf ↑Sphi B` binder) killed the singleton-`B`
pigeonhole: `Enveloped` forbids a one-point base, so "`halfStrip B vl` is a single line" is no
longer available.  The obstruction below is **immune to that fix**, and for a reason worth stating
precisely: all it asks of `B` is `B.Finite`, which `EnvOf ↑Sphi B` *supplies*
(`HbaseFlatSeed.finite_of_envOf_Sphi`, `:757`) rather than forbids.  Strengthening the binder
cannot escape a consequence of the binder.  `not_hwin_of_row_zero_levelConst_envOf` below is that
sentence as a theorem rather than as prose.

The mechanism is `HbaseBridge.not_hwin_of_row_ray_halfStrip` (`HbaseBridge.lean:423`) with its two
accidents removed.  That lemma is stated for `halfStripFrom Bf vl t₁` (a `Finset` base and an
integer threshold) and for one specific row shape, `enum 0 j = enum 0 0 + j • u'`.  Neither is
load-bearing: what its proof consumes is (a) every `dot (expNormal u' vl)`-level slice of the sweep
set is finite, and (b) row `0` is infinite and confined to **one** such level.  Restated that way
it applies to `HwinHoleE`'s own `halfStrip B vl`, and to *every* enumeration rather than to
`coverEnum`.

**What it gives (`not_hwin_of_row_zero_levelConst`)**: once some `z₀ ∈ S.erase a` sits off `a`'s
level, an admissible `enum` must have row `0` either finite-ranged or **level-mixing**.
⚠ **Reading limit**: this is a necessary condition on the `∃ enum` witness, so it does **not**
refute `HwinHoleE` — it says where a witness cannot be looked for.

Both known refutations are instances of it, which is the point of stating it once:
`HbaseBridge.not_hwin_coverEnum_halfStrip` (`:469` — `coverEnum`'s row `0` is a `u'`-ray, hence
level-constant by `dot_expNormal_u'`) and `HbaseFlatSeed.not_hwin_seed_levelEnum` (`levelEnum`'s
row `i` sits at one exact level by construction).  They agree because they are the same
obstruction, not because two independently chosen enumerations happened to fail. -/

/-- Level slices of `halfStrip B vl` are finite whenever the base is.  The `halfStrip` analogue of
`HbaseBridge.halfStripFrom_level_finite` (`HbaseBridge.lean:401`), which is stated for
`halfStripFrom` and a `Finset` base. -/
theorem halfStrip_level_finite {B : Set (ℤ × ℤ)} {vl m : ℤ × ℤ} {L : ℤ}
    (hBfin : B.Finite) (hm : dot m vl = 1) :
    {z | z ∈ halfStrip B vl ∧ dot m z = L}.Finite := by
  apply Set.Finite.subset (hBfin.image (fun g => g + (L - dot m g) • vl))
  rintro z ⟨⟨g, hg, t, rfl⟩, hlev⟩
  simp only [dot_add, dot_smul_right, hm, mul_one] at hlev
  exact ⟨g, hg, by
    show g + (L - dot m g) • vl = g + (t : ℤ) • vl
    rw [show L - dot m g = (t : ℤ) by omega]⟩

/-- **`HbaseBridge.not_hwin_of_row_ray_halfStrip` with both accidents removed.**
Base: any `B.Finite`, through `halfStrip` rather than `halfStripFrom`.  Row shape: row `0` need
only be infinite and confined to a single `dot (expNormal u' vl)`-level — it need not be a
`u'`-ray, and no property of `coverEnum` is used. -/
theorem not_hwin_of_row_zero_levelConst
    {S : Finset (ℤ × ℤ)} {a : ℤ × ℤ} {B : Set (ℤ × ℤ)} {vl u' : ℤ × ℤ}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) (hBfin : B.Finite)
    (enum : ℕ → ℕ → ℤ × ℤ)
    (hrow_inf : (Set.range (enum 0)).Infinite)
    (hrow_lev : ∀ j : ℕ, dot (expNormal u' vl) (enum 0 j) = dot (expNormal u' vl) (enum 0 0))
    {z₀ : ℤ × ℤ} (hz₀ : z₀ ∈ S.erase a)
    (hδ : dot (expNormal u' vl) z₀ ≠ dot (expNormal u' vl) a) :
    ¬ (∀ i j : ℕ, ∀ z ∈ S.erase a,
        z + (enum i j - a) ∈
          halfStrip B vl
            ∪ (⋃ i' ∈ {i' | i' < i}, Set.range (enum i'))
            ∪ (enum i '' {j' | j' < j})) := by
  intro hwin
  set m := expNormal u' vl with hm
  have hmvl : dot m vl = 1 := dot_expNormal_vl hunimod
  have hlin : ∀ j : ℕ, dot m (z₀ + (enum 0 j - a))
      = dot m z₀ + dot m (enum 0 j) - dot m a := by
    intro j
    simp only [dot, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]
    ring
  -- Each translated point of row `0` lands in the half-strip: the `⋃ i' < 0` term is empty, and
  -- the `enum 0 '' {j' < j}` term is at row `0`'s own level, which the translate misses by `hδ`.
  have hmem : ∀ j : ℕ, z₀ + (enum 0 j - a) ∈ halfStrip B vl := by
    intro j
    rcases hwin 0 j z₀ hz₀ with h | h
    · rcases h with h | h
      · exact h
      · simp at h
    · obtain ⟨j', -, hj'⟩ := h
      exfalso
      have h1 : dot m (enum 0 j') = dot m (enum 0 0) := hrow_lev j'
      have h2 : dot m (z₀ + (enum 0 j - a)) = dot m z₀ + dot m (enum 0 0) - dot m a := by
        rw [hlin j, hrow_lev j]
      rw [hj'] at h1
      omega
  -- … all at one and the same level, of which the half-strip has only finitely many points.
  refine hrow_inf (Set.Finite.subset
    ((halfStrip_level_finite (L := dot m z₀ + dot m (enum 0 0) - dot m a) hBfin hmvl).image
      (fun z => z + (a - z₀))) ?_)
  rintro _ ⟨j, rfl⟩
  exact ⟨z₀ + (enum 0 j - a), ⟨hmem j, by rw [hlin j, hrow_lev j]⟩, by module⟩

/-- **`EnvOf` cannot escape §14's obstruction, stated as a theorem rather than as a remark.**
Identical to `not_hwin_of_row_zero_levelConst` with `B.Finite` replaced by the binder
`HwinHoleE` actually carries.  The proof is one application of
`HbaseFlatSeed.finite_of_envOf_Sphi`; that is exactly the content of the claim. -/
theorem not_hwin_of_row_zero_levelConst_envOf
    {α : Type*} [AddCommMonoid α] {η : Config α}
    {S : Finset (ℤ × ℤ)} {a : ℤ × ℤ} {B : Set (ℤ × ℤ)} {vl u' : ℤ × ℤ}
    (d : Nivat.Colle35.DecompData η)
    (hEnv : Nivat.LE2.EnvOf ((d.Sphi : Set (ℤ × ℤ))) B)
    (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (enum : ℕ → ℕ → ℤ × ℤ)
    (hrow_inf : (Set.range (enum 0)).Infinite)
    (hrow_lev : ∀ j : ℕ, dot (expNormal u' vl) (enum 0 j) = dot (expNormal u' vl) (enum 0 0))
    {z₀ : ℤ × ℤ} (hz₀ : z₀ ∈ S.erase a)
    (hδ : dot (expNormal u' vl) z₀ ≠ dot (expNormal u' vl) a) :
    ¬ (∀ i j : ℕ, ∀ z ∈ S.erase a,
        z + (enum i j - a) ∈
          halfStrip B vl
            ∪ (⋃ i' ∈ {i' | i' < i}, Set.range (enum i'))
            ∪ (enum i '' {j' | j' < j})) :=
  not_hwin_of_row_zero_levelConst hunimod
    (Nivat.HbaseFlatSeed.finite_of_envOf_Sphi d hEnv) enum hrow_inf hrow_lev hz₀ hδ

/-! ## §15  The `𝒮`-vs-`𝒮_φ` seam, and why it costs nothing to close

Hflat refuted §13's `HwinHoleE` by taking `Sphi := B := {(0,0)}` against a three-point `S`:
`EnvOf ↑Sphi B` holds reflexively while `B` is still far too small to receive translates of
`S.erase a`.  The gap is real and it is **in the source, not only in the formalisation** —
`RegionSteps.lean:2318-2332` records that Collé fixes `𝒮` at Lemma 4.5 (`b3_colle2.txt:774`) as
Lemma 2.4's generating set while the chain is indexed by the zonotope `𝒮_φ` (Lemma 3.5,
`:424-428`), and never identifies the two; `DecompData.lean:113-124` records that a
`decomp.Sphi = S` field asserting the identification was deleted as unprovable.

So `hwin` was being asked to place translates of **Lemma 2.4's** `𝒮` inside a half-strip whose
base envelops the **zonotope**.  That mismatch was mine: I introduced it when wiring
`exists_hD_of_case1`'s `B` (which envelops `d.Sphi`) to `exists_vertex_of_generating_dir hSgen`
(which produces a vertex of `S`).

**It is not a mathematical obligation; it is an over-identification, and it is free to undo.**
`HbaseBridge.hbase_at_of_sweep_of_isGeneratingSet` (`:185`) takes its generating set as a
parameter unrelated to `B`, `D`, `vl`, `u'`, and the `S` of `WedgeResidualR ξ S vl` enters
`ofSweepEnum` only through `hline`/`hstraddle`'s `S.image (· + v)` — never through `hbase`.
The sweep window is therefore free to be a *different* generating set, and one is available at
exactly the right set: `Nivat.Colle35.DecompDataZ.isGeneratingSet` (`DecompData.lean:195`)
proves `IsGeneratingSet ξ d.Sphi` outright, from the annihilator.

Running the sweep on `d.Sphi` makes window and half-strip base the same set, so **no `𝒮`-vs-`𝒮_φ`
relating lemma is needed** — the one Hflat searched for and did not find, and which per the two
citations above does not exist because Collé never proves it.  `HwinHoleZ` below is `HwinHoleE`
with `S` deleted rather than related: every occurrence is the zonotope.

⚠ **Reading limit.** This removes a *spurious* obligation; it removes nothing real.  §14's
level-constant-row obstruction applies to `HwinHoleZ` verbatim (it never mentions which set the
window is), and the `i = j = 0` base case is still open.  What changes is that both are now
questions about one set instead of questions straddling two unrelated ones. -/

/-- **§13's `HwinHoleE` with the `𝒮`/`𝒮_φ` seam removed**: the sweep window, the minimality
direction and the enveloped base are all the *same* finite set `Sw`.  This is the proposition
`RegionSteps.exists_wedgeResidualR` now reduces to, at `Sw := d.Sphi`.

Note `ξ` occurs only in the `hD` hypothesis, and there is no `IsMinimalCounterexample` binder, so
this is **not** vacuous — refuting it is meaningful work.

**2026-09-20 — refuted.**  `not_hwinHoleZ_of_case1` (§21) shows this is *false* at every Case 1
instance, so `wedgeResidualR_of_hwinHoleZ` below is vacuous on the chain and
`RegionSteps.lean:1134` can never discharge it.  The culprit is the `∀ K` here: see §21 for why
an `∃ K` form is a different, unrefuted proposition. -/
def HwinHoleZ (ξ : Config ℤ) (Sw : Finset (ℤ × ℤ)) (vl : ℤ × ℤ) : Prop :=
  ∃ u' : ℤ × ℤ, (det u' vl = 1 ∨ det u' vl = -1) ∧
    ∀ (B : Set (ℤ × ℤ)) (u : ℤ × ℤ) (c : ℤ) (a : ℤ × ℤ) (K : ℤ),
      a ∈ Sw → Nivat.LatticeConvex (Sw.erase a) → 0 < c →
      B.Finite → EnvOf (Sw : Set (ℤ × ℤ)) B →
      (∀ b ∈ Sw, dot (expNormal (u' - K • vl) vl) a ≤ dot (expNormal (u' - K • vl) vl) b) →
      (∀ z ∈ halfStrip B vl, (T u ξ) z = T (c • vl) (T u ξ) z) →
      ∃ b₀ ∈ B, ∃ enum : ℕ → ℕ → ℤ × ℤ,
        (∀ i j : ℕ, ∀ z ∈ Sw.erase a,
          z + (enum i j - a) ∈
            halfStrip B vl ∪ (⋃ i' ∈ {i' | i' < i}, Set.range (enum i')) ∪
              (enum i '' {j' | j' < j})) ∧
        chainFull B vl (u' - K • vl) b₀ 0 ⊆ halfStrip B vl ∪ (⋃ i, Set.range (enum i))

/-- **The wiring form.**  This is what `RegionSteps.exists_wedgeResidualR` calls.

`hSgen` is still bound — the residual's `hline`/`hstraddle` are about `S.image (· + v)` and that
has not changed.  What changed is that the *sweep* now runs on `d.Sphi` via
`d.isGeneratingSet`, so `hSgen` is used only for `S.Nonempty`, and the half-strip base envelops
the same set the window is drawn from. -/
theorem wedgeResidualR_of_hwinHoleZ
    {ξ xper : Config ℤ} {vl p : ℤ × ℤ} {S : Finset (ℤ × ℤ)}
    (hξ : IsMinimalCounterexample ξ) (d : Nivat.Colle35.DecompDataZ ξ)
    (hSgen : IsGeneratingSet ξ S)
    (hcase1 : Case1 ξ xper d.Sphi vl)
    (hvl_prim : Primitive vl) (hp_mem : p ∈ Per xper) (hp_ne : p ≠ 0)
    (hdet_vl : det p vl = 0)
    (hhole : HwinHoleZ ξ d.Sphi vl) :
    Nonempty (L1Claim.WedgeResidualR ξ S vl) := by
  obtain ⟨u', hunimod, hhole⟩ := hhole
  obtain ⟨B, hEnv, u, c, hc, _hper, _hu, hD⟩ :=
    Nivat.L1Line0.exists_hD_of_case1 hcase1 hvl_prim hp_mem hp_ne hdet_vl
  have hBfin : B.Finite :=
    Nivat.HbaseFlatSeed.finite_of_envOf_Sphi d.toDecompData hEnv
  obtain ⟨K, a₁, ha₁, hcorner⟩ :=
    Nivat.L1StraddleWedge.exists_corner_shear (u' := u') (vl := vl)
      (S := d.toDecompData.Sphi) (Nivat.ColleReg.exists_Sφ d).1
  have hunimod' : det (u' - K • vl) vl = 1 ∨ det (u' - K • vl) vl = -1 := by
    rw [Nivat.L1StraddleWedge.det_shear]; exact hunimod
  have hw0 : expNormal (u' - K • vl) vl ≠ 0 := by
    intro h
    have := Nivat.ColleReg.dot_expNormal_vl hunimod'
    rw [h] at this
    simp [Nivat.LE2.dot] at this
  -- The sweep window is the zonotope, which is itself a generating set.
  obtain ⟨a, ha, hamin, hconvS, _hgen⟩ :=
    Nivat.ColleReg.exists_vertex_of_generating_dir hw0 d.isGeneratingSet
  obtain ⟨b₀, hb₀, enum, hwin, hK⟩ := hhole B u c a K ha hconvS hc hBfin hEnv hamin hD
  have hbase0 : PeriodOn (T u ξ) (chainFull B vl (u' - K • vl) b₀ 0) (c • vl) :=
    Nivat.HbaseBridge.hbase_at_of_sweep_of_isGeneratingSet d.isGeneratingSet ha hconvS 0 hD
      enum hwin hK
  obtain ⟨N₀, v, hN₀, hN₀1, hmin, hattain⟩ :=
    Nivat.ColleReg.exists_N₀_hmin_hattain hξ d hb₀ hunimod' hc.ne' hvl_prim 0 hbase0 hSgen.1
  refine ⟨ofSweepEnum (v := v) d.isGeneratingSet (Nivat.L1Line0.εOf (u' - K • vl) vl) hb₀
    (Nivat.ColleReg.L1Data.isLatticeConvexRegion_wedgeFull_of_unimod' hunimod')
    hunimod' hc.ne' ha hconvS hD enum hwin hK ?_ ?_⟩
  · intro N hN hN1
    have h := Nivat.L1Line0.hline_of_placement hb₀ hunimod' hc hN₀ hN₀1 hmin N
      (by simpa using hN) (by simpa using hN1)
    simpa only [Nat.zero_add] using h
  · intro N hN hN1 τ hτ
    have h := Nivat.ColleReg.wiring_hstraddle hunimod' hc.le hN₀ hN₀1 hmin hattain d ha₁ hcorner N
      (by simpa using hN) (by simpa using hN1) τ (by simpa using hτ)
    simpa only [Nat.zero_add] using h

/-! ## §16  The lex descent — `hwin` is a *global* constraint, not a row-`0` one

§14 constrains row `0` only, and Wbundle's `exists_hK_of_finiteRows` (`HwinHoleWeaken.lean`, §5)
shows the escape hatch §14 leaves is genuinely open: `hK` alone never forces a row to be
infinite, because `j ↦ e i` for a bijection `e : ℕ ≃ ℤ × ℤ` gives every row a *singleton* range
while `⋃ i, Set.range (enum i) = Set.univ`.  So `hK` cannot be the lever.

`hwin` can.  The three sets on its right-hand side are not symmetric: `⋃ i' < i` and
`enum i '' {j' < j}` are both **strictly earlier in lexicographic order**, and lex order on
`ℕ × ℕ` is well-founded.  Reading `hwin i j z` as a rewriting step

  `enum i j + w ∈ halfStrip B vl`   or   `enum i j + w = enum i' j'` with `(i', j') <ₗ (i, j)`

where `w := z - a`, the second branch cannot be taken forever.  Hence for **every** point of the
enumeration and **every** window direction `w`, some positive multiple `enum i j + k • w` lands
in the half-strip.  That is `exists_mem_halfStrip_of_hwin`, and it is enumeration-agnostic: no
row shape, no cardinality, no level hypothesis.

Applying `det · vl` turns it into an inequality.  `det` kills `vl`, so `det g vl = det b vl` for
every `g ∈ halfStrip B vl` — the half-strip occupies only the finitely many `det`-values of its
base (`B` finite, from `EnvOf`).  The descent therefore reads

  `det (enum i j) vl + k • det w vl ∈ det · vl '' B`,  `k ≥ 1`,

which **bounds `det · vl` on the whole enumeration** as soon as `det w vl ≠ 0`, with the sign of
the bound opposite to the sign of `det w vl`.  And `det w vl ≠ 0` for some `w = z - a` is exactly
`hnc` — `Sw` not contained in a single `vl`-parallel line — which
`HbaseFlatSeed.exists_hnc_of_decompData` proves unconditionally on `d.Sphi`.

⚠ **Reading limit, and it is the whole remaining gap.**  This bounds `det · vl` on
`halfStrip B vl ∪ ⋃ i, Set.range (enum i)`, which by `hK` contains `chainFull B vl u' b₀ 0`.
It refutes `HwinHoleZ` **only if `det · vl` is unbounded on `chainFull B vl u' b₀ 0`** in the
matching direction.  Nothing below asserts that; `chainFull` is not mentioned in this section. -/

/-- Every point of a half-strip carries the `det · vl` value of its own base point: `det` kills
the `vl`-direction, so the half-strip is confined to the base's finitely many `det`-levels. -/
theorem det_eq_of_mem_halfStrip {B : Set (ℤ × ℤ)} {vl g : ℤ × ℤ}
    (hg : g ∈ halfStrip B vl) : ∃ b ∈ B, det g vl = det b vl := by
  obtain ⟨b, hb, t, rfl⟩ := hg
  refine ⟨b, hb, ?_⟩
  simp only [det, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- **`hwin` forces every enumerated point to reach the half-strip along every window
direction.**  Induction on `(i, j)` in lexicographic order: `hwin i j z` either lands
`enum i j + (z - a)` in `halfStrip B vl` outright, or identifies it with some `enum i' j'` at a
strictly earlier lex index, and the latter cannot recur forever.

Enumeration-agnostic — unlike §14 this assumes nothing about row shapes, row cardinalities or
levels, and unlike `HbaseBridge.not_hwin_coverEnum_halfStrip` nothing about `coverEnum`. -/
theorem exists_mem_halfStrip_of_hwin
    {Sw : Finset (ℤ × ℤ)} {a : ℤ × ℤ} {B : Set (ℤ × ℤ)} {vl : ℤ × ℤ}
    (enum : ℕ → ℕ → ℤ × ℤ) {z : ℤ × ℤ} (hz : z ∈ Sw.erase a)
    (hwin : ∀ i j : ℕ, ∀ z ∈ Sw.erase a,
      z + (enum i j - a) ∈
        halfStrip B vl
          ∪ (⋃ i' ∈ {i' | i' < i}, Set.range (enum i'))
          ∪ (enum i '' {j' | j' < j})) :
    ∀ i j : ℕ, ∃ k : ℕ, 0 < k ∧ enum i j + (k : ℤ) • (z - a) ∈ halfStrip B vl := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i IHi =>
    intro j
    induction j using Nat.strong_induction_on with
    | _ j IHj =>
      -- One descent step: if the translate *is* `enum i' j'`, prepend a multiple of `w`.
      have step : ∀ p : ℤ × ℤ, p = z + (enum i j - a) →
          (∃ k : ℕ, 0 < k ∧ p + (k : ℤ) • (z - a) ∈ halfStrip B vl) →
          ∃ k : ℕ, 0 < k ∧ enum i j + (k : ℤ) • (z - a) ∈ halfStrip B vl := by
        rintro p rfl ⟨k, _, hmem⟩
        refine ⟨k + 1, Nat.succ_pos _, ?_⟩
        have hrw : enum i j + ((k + 1 : ℕ) : ℤ) • (z - a)
            = z + (enum i j - a) + (k : ℤ) • (z - a) := by push_cast; module
        rw [hrw]; exact hmem
      rcases hwin i j z hz with h | h
      · rcases h with h | h
        · refine ⟨1, one_pos, ?_⟩
          have hrw : enum i j + ((1 : ℕ) : ℤ) • (z - a) = z + (enum i j - a) := by
            push_cast; module
          rw [hrw]; exact h
        · simp only [Set.mem_iUnion, Set.mem_range, Set.mem_setOf_eq, exists_prop] at h
          obtain ⟨i', hi', j', hj'⟩ := h
          exact step _ hj' (IHi i' hi' j')
      · obtain ⟨j', hj'lt, hj'⟩ := h
        exact step _ hj' (IHj j' hj'lt)

/-- The lex descent in `det · vl` coordinates: the arithmetic content of §16, sign-free so that
both sign cases below are corollaries rather than duplicated proofs. -/
theorem exists_det_eq_of_hwin
    {Sw : Finset (ℤ × ℤ)} {a : ℤ × ℤ} {B : Set (ℤ × ℤ)} {vl : ℤ × ℤ}
    (enum : ℕ → ℕ → ℤ × ℤ) {z : ℤ × ℤ} (hz : z ∈ Sw.erase a)
    (hwin : ∀ i j : ℕ, ∀ z ∈ Sw.erase a,
      z + (enum i j - a) ∈
        halfStrip B vl
          ∪ (⋃ i' ∈ {i' | i' < i}, Set.range (enum i'))
          ∪ (enum i '' {j' | j' < j})) :
    ∀ i j : ℕ, ∃ k : ℕ, ∃ b ∈ B, 0 < k ∧
      det (enum i j) vl + (k : ℤ) * det (z - a) vl = det b vl := by
  intro i j
  obtain ⟨k, hk, hmem⟩ := exists_mem_halfStrip_of_hwin enum hz hwin i j
  obtain ⟨b, hb, hdet⟩ := det_eq_of_mem_halfStrip hmem
  refine ⟨k, b, hb, hk, ?_⟩
  rw [← hdet]
  simp only [det, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- **`hwin` bounds `det · vl` above on the entire enumeration**, whenever some window direction
has positive `det · vl`.  The bound is the base's, shifted by one step of the descent. -/
theorem det_le_of_hwin
    {Sw : Finset (ℤ × ℤ)} {a : ℤ × ℤ} {B : Set (ℤ × ℤ)} {vl : ℤ × ℤ}
    (hBfin : B.Finite) (enum : ℕ → ℕ → ℤ × ℤ) {z : ℤ × ℤ} (hz : z ∈ Sw.erase a)
    (hδ : 0 < det (z - a) vl)
    (hwin : ∀ i j : ℕ, ∀ z ∈ Sw.erase a,
      z + (enum i j - a) ∈
        halfStrip B vl
          ∪ (⋃ i' ∈ {i' | i' < i}, Set.range (enum i'))
          ∪ (enum i '' {j' | j' < j})) :
    ∃ M : ℤ, ∀ i j : ℕ, det (enum i j) vl ≤ M := by
  obtain ⟨M, hM⟩ := (hBfin.image (fun b => det b vl)).bddAbove
  refine ⟨M, fun i j => ?_⟩
  obtain ⟨k, b, hb, hk, heq⟩ := exists_det_eq_of_hwin enum hz hwin i j
  have hbM : det b vl ≤ M := hM ⟨b, hb, rfl⟩
  have hk1 : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  nlinarith

/-- The opposite sign: a window direction with negative `det · vl` bounds the enumeration
**below**.  Same descent, read the other way. -/
theorem le_det_of_hwin
    {Sw : Finset (ℤ × ℤ)} {a : ℤ × ℤ} {B : Set (ℤ × ℤ)} {vl : ℤ × ℤ}
    (hBfin : B.Finite) (enum : ℕ → ℕ → ℤ × ℤ) {z : ℤ × ℤ} (hz : z ∈ Sw.erase a)
    (hδ : det (z - a) vl < 0)
    (hwin : ∀ i j : ℕ, ∀ z ∈ Sw.erase a,
      z + (enum i j - a) ∈
        halfStrip B vl
          ∪ (⋃ i' ∈ {i' | i' < i}, Set.range (enum i'))
          ∪ (enum i '' {j' | j' < j})) :
    ∃ M : ℤ, ∀ i j : ℕ, M ≤ det (enum i j) vl := by
  obtain ⟨M, hM⟩ := (hBfin.image (fun b => -det b vl)).bddAbove
  refine ⟨-M, fun i j => ?_⟩
  obtain ⟨k, b, hb, hk, heq⟩ := exists_det_eq_of_hwin enum hz hwin i j
  have hbM : -det b vl ≤ M := hM ⟨b, hb, rfl⟩
  have hk1 : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  nlinarith

/-- **§16's payload for the consumer**: `hwin` together with `hK` confines
`chainFull B vl u' b₀ 0` to a `det · vl`-halfspace.  Refuting `HwinHoleZ` by this route is
exactly the task of showing `chainFull` escapes that halfspace — which this file does not
claim and does not use. -/
theorem det_le_on_chainFull_of_hwin_hK
    {Sw : Finset (ℤ × ℤ)} {a : ℤ × ℤ} {B : Set (ℤ × ℤ)} {vl u' b₀ : ℤ × ℤ}
    (hBfin : B.Finite) (enum : ℕ → ℕ → ℤ × ℤ) {z : ℤ × ℤ} (hz : z ∈ Sw.erase a)
    (hδ : 0 < det (z - a) vl)
    (hwin : ∀ i j : ℕ, ∀ z ∈ Sw.erase a,
      z + (enum i j - a) ∈
        halfStrip B vl
          ∪ (⋃ i' ∈ {i' | i' < i}, Set.range (enum i'))
          ∪ (enum i '' {j' | j' < j}))
    (hK : chainFull B vl u' b₀ 0 ⊆ halfStrip B vl ∪ (⋃ i, Set.range (enum i))) :
    ∃ M : ℤ, ∀ g ∈ chainFull B vl u' b₀ 0, det g vl ≤ M := by
  obtain ⟨M₁, hM₁⟩ := (hBfin.image (fun b => det b vl)).bddAbove
  obtain ⟨M₂, hM₂⟩ := det_le_of_hwin hBfin enum hz hδ hwin
  refine ⟨max M₁ M₂, fun g hg => ?_⟩
  rcases hK hg with h | h
  · obtain ⟨b, hb, hdet⟩ := det_eq_of_mem_halfStrip h
    exact hdet ▸ (hM₁ ⟨b, hb, rfl⟩).trans (le_max_left _ _)
  · simp only [Set.mem_iUnion, Set.mem_range] at h
    obtain ⟨i, j, hij⟩ := h
    exact hij ▸ (hM₂ i j).trans (le_max_right _ _)

/-! ## §17  The descent closes: `hwin ∧ hK` is contradictory once a window direction has the
sign matching `det u' vl`

§16 bounds `det · vl` on `chainFull B vl u' b₀ 0`.  `chainFull` does not tolerate that bound.
By `L1Base.chainFull_zero_eq_sweep_band0` the level-`0` chain is the forward `u'`-sweep of
`band0`, and `b₀` itself lies in `band0` (it is in `fullSweep B vl` at `k = 0`, and it sits
exactly *on* the cut level `expLevel u' vl b₀ 0`).  So the whole ray `b₀ + t • u'`, `t : ℕ`, is
in the chain, and `det (b₀ + t • u') vl = det b₀ vl + t · det u' vl` marches off to `±∞` at unit
speed because `u'` is unimodular against `vl`.

**Neither lemma below mentions `ξ`, `T`, `hD`, `PeriodOn` or `IsMinimalCounterexample`.**  They
are pure statements about the sets, so they are not vacuous and they do not need a configuration
to be constructed.  Together with §16 they say: an `enum` satisfying `hwin ∧ hK` exists only if
`a` is the extreme point of `Sw` in the `det · vl` direction selected by the sign of `det u' vl`.

⚠ **What is still needed to refute `HwinHoleZ` from this.**  The hole's `a` is not ours: it
arrives with `hamin` (minimality for `dot (expNormal (u' - K • vl) vl)`) and `hcorner`-style
convexity, and `K` is universally quantified while `det (u' - K • vl) vl = det u' vl` is *not*
affected by `K` (`L1StraddleWedge.det_shear`).  The remaining step is therefore a question about
which vertex `hamin` selects as `K` varies, against the fixed `det · vl` extreme — **not** a
question about enumerations any more.  `HbaseFlatSeed.exists_hnc_of_decompData` supplies the one
structural input (`d.Sphi` is not contained in a single `vl`-parallel line), i.e. that the two
`det · vl` extremes of the window are distinct. -/

/-- `b₀`'s own forward `u'`-ray lies in the level-`0` chain: `b₀ ∈ band0` because it is in
`fullSweep B vl` at `k = 0` and sits exactly on the cut level. -/
theorem mem_chainFull_zero_ray {B : Set (ℤ × ℤ)} {vl u' b₀ : ℤ × ℤ} (hb₀ : b₀ ∈ B) (t : ℕ) :
    b₀ + (t : ℤ) • u' ∈ chainFull B vl u' b₀ 0 := by
  rw [Nivat.L1Base.chainFull_zero_eq_sweep_band0]
  refine Nivat.RegionSweep.add_nsmul_mem_sweep ?_ t
  simp only [Nivat.L1Base.band0, Set.mem_inter_iff]
  refine ⟨mem_fullSweep_iff.mpr ⟨b₀, hb₀, 0, by simp⟩, ?_⟩
  show expLevel u' vl b₀ 0 ≤ dot (expNormal u' vl) b₀
  simp [expLevel]

/-- `det · vl` along `b₀`'s `u'`-ray, in closed form. -/
theorem det_ray {vl u' b₀ : ℤ × ℤ} (t : ℕ) :
    det (b₀ + (t : ℤ) • u') vl = det b₀ vl + (t : ℤ) * det u' vl := by
  simp only [det, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- **The descent closes, positive orientation.**  `det u' vl = 1` sends the chain's `det · vl`
to `+∞`, while a window direction with `0 < det (z - a) vl` caps it via §16.  Pure set theory —
no configuration, no periodicity, no minimal-counterexample hypothesis. -/
theorem false_of_hwin_hK_of_det_pos
    {Sw : Finset (ℤ × ℤ)} {a : ℤ × ℤ} {B : Set (ℤ × ℤ)} {vl u' b₀ : ℤ × ℤ}
    (hBfin : B.Finite) (hb₀ : b₀ ∈ B) (hdet : det u' vl = 1)
    (enum : ℕ → ℕ → ℤ × ℤ) {z : ℤ × ℤ} (hz : z ∈ Sw.erase a)
    (hδ : 0 < det (z - a) vl)
    (hwin : ∀ i j : ℕ, ∀ z ∈ Sw.erase a,
      z + (enum i j - a) ∈
        halfStrip B vl
          ∪ (⋃ i' ∈ {i' | i' < i}, Set.range (enum i'))
          ∪ (enum i '' {j' | j' < j}))
    (hK : chainFull B vl u' b₀ 0 ⊆ halfStrip B vl ∪ (⋃ i, Set.range (enum i))) :
    False := by
  obtain ⟨M, hM⟩ := det_le_on_chainFull_of_hwin_hK hBfin enum hz hδ hwin hK
  have hray := hM _ (mem_chainFull_zero_ray (vl := vl) (u' := u') hb₀ (M - det b₀ vl + 1).toNat)
  rw [det_ray, hdet] at hray
  have h1 : M - det b₀ vl + 1 ≤ ((M - det b₀ vl + 1).toNat : ℤ) := Int.self_le_toNat _
  omega

/-- **The descent closes, negative orientation.**  Mirror of `false_of_hwin_hK_of_det_pos`:
`det u' vl = -1` sends the chain's `det · vl` to `-∞`, capped below by a window direction with
`det (z - a) vl < 0`. -/
theorem false_of_hwin_hK_of_det_neg
    {Sw : Finset (ℤ × ℤ)} {a : ℤ × ℤ} {B : Set (ℤ × ℤ)} {vl u' b₀ : ℤ × ℤ}
    (hBfin : B.Finite) (hb₀ : b₀ ∈ B) (hdet : det u' vl = -1)
    (enum : ℕ → ℕ → ℤ × ℤ) {z : ℤ × ℤ} (hz : z ∈ Sw.erase a)
    (hδ : det (z - a) vl < 0)
    (hwin : ∀ i j : ℕ, ∀ z ∈ Sw.erase a,
      z + (enum i j - a) ∈
        halfStrip B vl
          ∪ (⋃ i' ∈ {i' | i' < i}, Set.range (enum i'))
          ∪ (enum i '' {j' | j' < j}))
    (hK : chainFull B vl u' b₀ 0 ⊆ halfStrip B vl ∪ (⋃ i, Set.range (enum i))) :
    False := by
  obtain ⟨M₁, hM₁⟩ := (hBfin.image (fun b => -det b vl)).bddAbove
  obtain ⟨M₂, hM₂⟩ := le_det_of_hwin hBfin enum hz hδ hwin
  have hM : ∀ g ∈ chainFull B vl u' b₀ 0, min (-M₁) M₂ ≤ det g vl := by
    intro g hg
    rcases hK hg with h | h
    · obtain ⟨b, hb, hdetb⟩ := det_eq_of_mem_halfStrip h
      have : -det b vl ≤ M₁ := hM₁ ⟨b, hb, rfl⟩
      rw [hdetb]
      exact le_trans (min_le_left _ _) (by omega)
    · simp only [Set.mem_iUnion, Set.mem_range] at h
      obtain ⟨i, j, hij⟩ := h
      exact hij ▸ (min_le_right _ _).trans (hM₂ i j)
  set M := min (-M₁) M₂ with hMdef
  have hray := hM _ (mem_chainFull_zero_ray (vl := vl) (u' := u') hb₀ (det b₀ vl - M + 1).toNat)
  rw [det_ray, hdet] at hray
  have h1 : det b₀ vl - M + 1 ≤ ((det b₀ vl - M + 1).toNat : ℤ) := Int.self_le_toNat _
  omega

/-! ## §18  The same descent against an arbitrary seed `D`

§16/§17 are stated against `halfStrip B vl` because that is the only seed
`L1Line0.exists_hD_of_case1` produces.  But the consumer
`HbaseBridge.hbase_at_of_sweep_of_isGeneratingSet` (`HbaseBridge.lean:185`) takes `D` as a
**free parameter**: `hwin` and `hK` are stated against `D`, and the only constraint on `D` is
`hD` (`T e ξ` is `c • vl`-periodic on it).  So the descent was never about `halfStrip`.  Run
verbatim against an arbitrary `D` it says:

> a seed `D` can carry the sweep only if `det · vl` is **unbounded** on `D`, in the direction the
> chain's own `u'`-ray escapes.

This is a necessary condition on `D` proved against the *consumer's* binders, not against
`HwinHoleZ`'s packaging, so no restatement of the hole can dodge it.  It also explains §17
rather than being explained by it: `halfStrip B vl` fails precisely because `B` is finite — and
`EnvOf ↑Sw B` **supplies** that finiteness (`HbaseFlatSeed.finite_of_envOf_Sphi`), it does not
forbid it — so the half-strip meets only finitely many `det · vl` levels.

⚠ **Reading limit.**  "`D` must be `det · vl`-unbounded" is a statement about seeds, not a
refutation of Collé's Lemma 4.5.  Nothing here claims the paper's periodicity locus is the
half-strip; what is established is that `exists_hD_of_case1`'s output is too small to be the `D`
this sweep needs, and by exactly how much.  `sorry` count and `axiom_closure` are unchanged. -/

/-- `det · vl` is affine along an integer multiple of a fixed direction. -/
theorem det_add_zsmul (p w vl : ℤ × ℤ) (k : ℤ) :
    det (p + k • w) vl = det p vl + k * det w vl := by
  simp only [det, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- **§16 against a free seed.**  `hwin`'s right-hand side names strictly lex-earlier indices in
its second and third disjuncts, so it is a rewriting step on a well-founded order: iterating it
from any `enum i j` in the fixed window direction `z - a` reaches `D` in finitely many steps.
Nothing about `D` is used. -/
theorem exists_mem_seed_of_hwin
    {Sw : Finset (ℤ × ℤ)} {a : ℤ × ℤ} {D : Set (ℤ × ℤ)}
    (enum : ℕ → ℕ → ℤ × ℤ) {z : ℤ × ℤ} (hz : z ∈ Sw.erase a)
    (hwin : ∀ i j : ℕ, ∀ z ∈ Sw.erase a,
      z + (enum i j - a) ∈
        D ∪ (⋃ i' ∈ {i' | i' < i}, Set.range (enum i'))
          ∪ (enum i '' {j' | j' < j})) :
    ∀ i j : ℕ, ∃ k : ℕ, 0 < k ∧ enum i j + (k : ℤ) • (z - a) ∈ D := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i IHi =>
    intro j
    induction j using Nat.strong_induction_on with
    | _ j IHj =>
      have step : ∀ p : ℤ × ℤ, p = z + (enum i j - a) →
          (∃ k : ℕ, 0 < k ∧ p + (k : ℤ) • (z - a) ∈ D) →
          ∃ k : ℕ, 0 < k ∧ enum i j + (k : ℤ) • (z - a) ∈ D := by
        rintro p rfl ⟨k, _, hmem⟩
        refine ⟨k + 1, Nat.succ_pos _, ?_⟩
        have hrw : enum i j + ((k + 1 : ℕ) : ℤ) • (z - a)
            = z + (enum i j - a) + (k : ℤ) • (z - a) := by push_cast; module
        rw [hrw]; exact hmem
      rcases hwin i j z hz with h | h
      · rcases h with h | h
        · refine ⟨1, one_pos, ?_⟩
          have hrw : enum i j + ((1 : ℕ) : ℤ) • (z - a) = z + (enum i j - a) := by
            push_cast; module
          rw [hrw]; exact h
        · simp only [Set.mem_iUnion, Set.mem_range, Set.mem_setOf_eq, exists_prop] at h
          obtain ⟨i', hi', j', hj'⟩ := h
          exact step _ hj' (IHi i' hi' j')
      · obtain ⟨j', hj'lt, hj'⟩ := h
        exact step _ hj' (IHj j' hj'lt)

/-- A `det · vl` ceiling on the seed becomes a strictly better ceiling on the whole
enumeration, once one window direction has positive `det · vl`. -/
theorem det_le_of_hwin_of_seed_le
    {Sw : Finset (ℤ × ℤ)} {a : ℤ × ℤ} {D : Set (ℤ × ℤ)} {vl : ℤ × ℤ} {M : ℤ}
    (hDb : ∀ g ∈ D, det g vl ≤ M)
    (enum : ℕ → ℕ → ℤ × ℤ) {z : ℤ × ℤ} (hz : z ∈ Sw.erase a)
    (hδ : 0 < det (z - a) vl)
    (hwin : ∀ i j : ℕ, ∀ z ∈ Sw.erase a,
      z + (enum i j - a) ∈
        D ∪ (⋃ i' ∈ {i' | i' < i}, Set.range (enum i'))
          ∪ (enum i '' {j' | j' < j})) :
    ∀ i j : ℕ, det (enum i j) vl ≤ M - 1 := by
  intro i j
  obtain ⟨k, hk, hmem⟩ := exists_mem_seed_of_hwin (D := D) enum hz hwin i j
  have h := hDb _ hmem
  rw [det_add_zsmul] at h
  have hk1 : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  nlinarith

/-- Mirror of `det_le_of_hwin_of_seed_le`: a floor on the seed becomes a floor on the
enumeration when one window direction has negative `det · vl`. -/
theorem le_det_of_hwin_of_le_seed
    {Sw : Finset (ℤ × ℤ)} {a : ℤ × ℤ} {D : Set (ℤ × ℤ)} {vl : ℤ × ℤ} {M : ℤ}
    (hDb : ∀ g ∈ D, M ≤ det g vl)
    (enum : ℕ → ℕ → ℤ × ℤ) {z : ℤ × ℤ} (hz : z ∈ Sw.erase a)
    (hδ : det (z - a) vl < 0)
    (hwin : ∀ i j : ℕ, ∀ z ∈ Sw.erase a,
      z + (enum i j - a) ∈
        D ∪ (⋃ i' ∈ {i' | i' < i}, Set.range (enum i'))
          ∪ (enum i '' {j' | j' < j})) :
    ∀ i j : ℕ, M + 1 ≤ det (enum i j) vl := by
  intro i j
  obtain ⟨k, hk, hmem⟩ := exists_mem_seed_of_hwin (D := D) enum hz hwin i j
  have h := hDb _ hmem
  rw [det_add_zsmul] at h
  have hk1 : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  nlinarith

/-- **The seed condition, positive orientation.**  If `det · vl` is bounded above on the seed
`D` and the window has a direction of positive `det · vl`, then `hwin ∧ hK` is contradictory —
the chain's `u'`-ray climbs past every ceiling at unit speed. -/
theorem false_of_hwin_hK_of_seed_le
    {Sw : Finset (ℤ × ℤ)} {a : ℤ × ℤ} {B D : Set (ℤ × ℤ)} {vl u' b₀ : ℤ × ℤ} {M : ℤ}
    (hDb : ∀ g ∈ D, det g vl ≤ M) (hb₀ : b₀ ∈ B) (hdet : det u' vl = 1)
    (enum : ℕ → ℕ → ℤ × ℤ) {z : ℤ × ℤ} (hz : z ∈ Sw.erase a)
    (hδ : 0 < det (z - a) vl)
    (hwin : ∀ i j : ℕ, ∀ z ∈ Sw.erase a,
      z + (enum i j - a) ∈
        D ∪ (⋃ i' ∈ {i' | i' < i}, Set.range (enum i'))
          ∪ (enum i '' {j' | j' < j}))
    (hK : chainFull B vl u' b₀ 0 ⊆ D ∪ (⋃ i, Set.range (enum i))) :
    False := by
  have hbound : ∀ g ∈ chainFull B vl u' b₀ 0, det g vl ≤ M := by
    intro g hg
    rcases hK hg with h | h
    · exact hDb _ h
    · simp only [Set.mem_iUnion, Set.mem_range] at h
      obtain ⟨i, j, hij⟩ := h
      rw [← hij]
      have := det_le_of_hwin_of_seed_le hDb enum hz hδ hwin i j
      omega
  have hray := hbound _ (mem_chainFull_zero_ray (vl := vl) (u' := u') hb₀
    (M - det b₀ vl + 1).toNat)
  rw [det_ray, hdet] at hray
  have h1 : M - det b₀ vl + 1 ≤ ((M - det b₀ vl + 1).toNat : ℤ) := Int.self_le_toNat _
  omega

/-- **The seed condition, negative orientation.**  Mirror of `false_of_hwin_hK_of_seed_le`. -/
theorem false_of_hwin_hK_of_le_seed
    {Sw : Finset (ℤ × ℤ)} {a : ℤ × ℤ} {B D : Set (ℤ × ℤ)} {vl u' b₀ : ℤ × ℤ} {M : ℤ}
    (hDb : ∀ g ∈ D, M ≤ det g vl) (hb₀ : b₀ ∈ B) (hdet : det u' vl = -1)
    (enum : ℕ → ℕ → ℤ × ℤ) {z : ℤ × ℤ} (hz : z ∈ Sw.erase a)
    (hδ : det (z - a) vl < 0)
    (hwin : ∀ i j : ℕ, ∀ z ∈ Sw.erase a,
      z + (enum i j - a) ∈
        D ∪ (⋃ i' ∈ {i' | i' < i}, Set.range (enum i'))
          ∪ (enum i '' {j' | j' < j}))
    (hK : chainFull B vl u' b₀ 0 ⊆ D ∪ (⋃ i, Set.range (enum i))) :
    False := by
  have hbound : ∀ g ∈ chainFull B vl u' b₀ 0, M ≤ det g vl := by
    intro g hg
    rcases hK hg with h | h
    · exact hDb _ h
    · simp only [Set.mem_iUnion, Set.mem_range] at h
      obtain ⟨i, j, hij⟩ := h
      rw [← hij]
      have := le_det_of_hwin_of_le_seed hDb enum hz hδ hwin i j
      omega
  have hray := hbound _ (mem_chainFull_zero_ray (vl := vl) (u' := u') hb₀
    (det b₀ vl - M + 1).toNat)
  rw [det_ray, hdet] at hray
  have h1 : det b₀ vl - M + 1 ≤ ((det b₀ vl - M + 1).toNat : ℤ) := Int.self_le_toNat _
  omega

/-- **The headline.**  Any seed that carries the sweep is `det · vl`-unbounded above, when the
chain escapes upward.  Contrapositive of `false_of_hwin_hK_of_seed_le`; stated separately
because this is the form a seed *builder* has to satisfy. -/
theorem not_bddAbove_det_seed_of_hwin_hK
    {Sw : Finset (ℤ × ℤ)} {a : ℤ × ℤ} {B D : Set (ℤ × ℤ)} {vl u' b₀ : ℤ × ℤ}
    (hb₀ : b₀ ∈ B) (hdet : det u' vl = 1)
    (enum : ℕ → ℕ → ℤ × ℤ) {z : ℤ × ℤ} (hz : z ∈ Sw.erase a)
    (hδ : 0 < det (z - a) vl)
    (hwin : ∀ i j : ℕ, ∀ z ∈ Sw.erase a,
      z + (enum i j - a) ∈
        D ∪ (⋃ i' ∈ {i' | i' < i}, Set.range (enum i'))
          ∪ (enum i '' {j' | j' < j}))
    (hK : chainFull B vl u' b₀ 0 ⊆ D ∪ (⋃ i, Set.range (enum i))) :
    ¬ ∃ M : ℤ, ∀ g ∈ D, det g vl ≤ M := by
  rintro ⟨M, hM⟩
  exact false_of_hwin_hK_of_seed_le hM hb₀ hdet enum hz hδ hwin hK

/-- Mirror of `not_bddAbove_det_seed_of_hwin_hK`. -/
theorem not_bddBelow_det_seed_of_hwin_hK
    {Sw : Finset (ℤ × ℤ)} {a : ℤ × ℤ} {B D : Set (ℤ × ℤ)} {vl u' b₀ : ℤ × ℤ}
    (hb₀ : b₀ ∈ B) (hdet : det u' vl = -1)
    (enum : ℕ → ℕ → ℤ × ℤ) {z : ℤ × ℤ} (hz : z ∈ Sw.erase a)
    (hδ : det (z - a) vl < 0)
    (hwin : ∀ i j : ℕ, ∀ z ∈ Sw.erase a,
      z + (enum i j - a) ∈
        D ∪ (⋃ i' ∈ {i' | i' < i}, Set.range (enum i'))
          ∪ (enum i '' {j' | j' < j}))
    (hK : chainFull B vl u' b₀ 0 ⊆ D ∪ (⋃ i, Set.range (enum i))) :
    ¬ ∃ M : ℤ, ∀ g ∈ D, M ≤ det g vl := by
  rintro ⟨M, hM⟩
  exact false_of_hwin_hK_of_le_seed hM hb₀ hdet enum hz hδ hwin hK

/-- The half-strip is `det · vl`-bounded above whenever `B` is finite.  With
`not_bddAbove_det_seed_of_hwin_hK` this is exactly why §17 fires, and it localises the failure
in `B.Finite` — which `EnvOf ↑Sw B` hands out. -/
theorem bddAbove_det_halfStrip {B : Set (ℤ × ℤ)} (hBfin : B.Finite) (vl : ℤ × ℤ) :
    ∃ M : ℤ, ∀ g ∈ halfStrip B vl, det g vl ≤ M := by
  obtain ⟨M, hM⟩ := (hBfin.image (fun b => det b vl)).bddAbove
  refine ⟨M, fun g hg => ?_⟩
  obtain ⟨b, hb, hdetb⟩ := det_eq_of_mem_halfStrip hg
  exact hdetb ▸ hM ⟨b, hb, rfl⟩

/-- Mirror of `bddAbove_det_halfStrip`. -/
theorem bddBelow_det_halfStrip {B : Set (ℤ × ℤ)} (hBfin : B.Finite) (vl : ℤ × ℤ) :
    ∃ M : ℤ, ∀ g ∈ halfStrip B vl, M ≤ det g vl := by
  obtain ⟨M, hM⟩ := (hBfin.image (fun b => -det b vl)).bddAbove
  refine ⟨-M, fun g hg => ?_⟩
  obtain ⟨b, hb, hdetb⟩ := det_eq_of_mem_halfStrip hg
  have hb' : -det b vl ≤ M := hM ⟨b, hb, rfl⟩
  omega

/-! ## §19  What the descent actually forces: `a` must be the `det · vl`-extreme

§17/§18 fire only when the window has a point *ahead* of `a` in the direction the chain travels.
Turned around, that is a sharp necessary condition on the vertex `a`, and it is the useful form:

> if `det u' vl = 1`, an `enum` satisfying `hwin ∧ hK` exists only when `a` is the
> `det · vl`-**maximum** of `Sw` (mirror: the minimum, when `det u' vl = -1`).

This matches the geometry of Collé's sweep: the window `S \ {a}` has to lie *behind* the point
being conquered, or the argument would be using unconquered points.  So the descent is not an
obstruction to the sweep — it is the statement that the sweep runs in one direction only.

**Where the defect therefore is.**  `HwinHoleZ` quantifies `K` universally.  But `a` is a
function of `K`: `hamin` minimises `dot (expNormal (u' - K • vl) vl)`, which by
`HbaseFlatSeed.dot_expNormal_swap_eq_lambda` equals `dot (expNormal u' vl) z + K * det u' vl *
det z vl`.  Large `K` of one sign selects the `det · vl`-minimum, the other sign selects the
maximum.  So `∀ K` makes the hole false for a reason that has nothing to do with the
mathematics: the call site `wedgeResidualR_of_hwinHoleZ` applies the hole at exactly **one** `K`,
the one `L1StraddleWedge.exists_corner_shear` produces.  Writing `∀ K` was a §15-style
strengthening on my part.

`not_exists_enum_hwin_hK_of_shear` below makes that precise: there is always a `K` at which the
conclusion is unreachable.  It refutes the `∀ K` form and says nothing about the one `K` the
caller uses — deciding that is a question about `exists_corner_shear`'s sign, not about
enumerations. -/

/-- The shear `u' ↦ u' - K • vl` leaves `det · vl` alone.  Proved locally rather than reused
from `L1StraddleWedge.det_shear` to keep §19 free of a new import (blindspot 1b). -/
theorem det_shear_vl (u' vl : ℤ × ℤ) (K : ℤ) : det (u' - K • vl) vl = det u' vl := by
  simp only [det, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- `det · vl` is additive in the left argument.  Local copy of `ColleReg.det_sub_left`, kept
here so §19 does not depend on a file another lane is still writing. -/
theorem det_sub_vl (p q vl : ℤ × ℤ) : det (p - q) vl = det p vl - det q vl := by
  simp only [det, Prod.fst_sub, Prod.snd_sub]
  ring

/-- **The necessary condition on the vertex, positive orientation.**  `a` must dominate the whole
window in `det · vl`.  Contrapositive of `false_of_hwin_hK_of_det_pos`. -/
theorem detMax_of_hwin_hK
    {Sw : Finset (ℤ × ℤ)} {a : ℤ × ℤ} {B : Set (ℤ × ℤ)} {vl u' b₀ : ℤ × ℤ}
    (hBfin : B.Finite) (hb₀ : b₀ ∈ B) (hdet : det u' vl = 1)
    (enum : ℕ → ℕ → ℤ × ℤ)
    (hwin : ∀ i j : ℕ, ∀ z ∈ Sw.erase a,
      z + (enum i j - a) ∈
        halfStrip B vl ∪ (⋃ i' ∈ {i' | i' < i}, Set.range (enum i'))
          ∪ (enum i '' {j' | j' < j}))
    (hK : chainFull B vl u' b₀ 0 ⊆ halfStrip B vl ∪ (⋃ i, Set.range (enum i))) :
    ∀ z ∈ Sw.erase a, det z vl ≤ det a vl := by
  intro z hz
  by_contra hlt
  push_neg at hlt
  refine false_of_hwin_hK_of_det_pos hBfin hb₀ hdet enum hz ?_ hwin hK
  rw [det_sub_vl]; omega

/-- **The necessary condition on the vertex, negative orientation.**  Mirror of
`detMax_of_hwin_hK`: `a` must be dominated by the whole window. -/
theorem detMin_of_hwin_hK
    {Sw : Finset (ℤ × ℤ)} {a : ℤ × ℤ} {B : Set (ℤ × ℤ)} {vl u' b₀ : ℤ × ℤ}
    (hBfin : B.Finite) (hb₀ : b₀ ∈ B) (hdet : det u' vl = -1)
    (enum : ℕ → ℕ → ℤ × ℤ)
    (hwin : ∀ i j : ℕ, ∀ z ∈ Sw.erase a,
      z + (enum i j - a) ∈
        halfStrip B vl ∪ (⋃ i' ∈ {i' | i' < i}, Set.range (enum i'))
          ∪ (enum i '' {j' | j' < j}))
    (hK : chainFull B vl u' b₀ 0 ⊆ halfStrip B vl ∪ (⋃ i, Set.range (enum i))) :
    ∀ z ∈ Sw.erase a, det a vl ≤ det z vl := by
  intro z hz
  by_contra hlt
  push_neg at hlt
  refine false_of_hwin_hK_of_det_neg hBfin hb₀ hdet enum hz ?_ hwin hK
  rw [det_sub_vl]; omega

/-- **The `∀ K` form of the hole is unreachable.**  Given only that the window is not contained
in a single `vl`-parallel line (`hnc`, produced on the chain by
`HbaseFlatSeed.exists_hnc_of_decompData_det`), there is a shear `K` at which no `hamin`-vertex
admits any `enum` satisfying `hwin ∧ hK`.

Assembled from `ColleReg.exists_shear_argmin_not_detMax` / `_not_detMin` (which choose `K` so the
sheared argmin is the *wrong* `det · vl` extreme) and §17.

⚠ **Reading limit.**  This refutes `HwinHoleZ`'s universal quantification over `K`.  It does
**not** refute the sweep, and it does **not** say `hbase` is false: the caller
`wedgeResidualR_of_hwinHoleZ` uses a single `K`, supplied by
`L1StraddleWedge.exists_corner_shear`.  Whether *that* `K` has the sound sign is a separate
question about `exists_corner_shear`.

**2026-09-20 — that separate question is now answered, and the answer is "wrong sign, always".**
See §20 below (`not_exists_enum_hwin_hK_at_corner_shear`). -/
theorem not_exists_enum_hwin_hK_of_shear
    {Sw : Finset (ℤ × ℤ)} {B : Set (ℤ × ℤ)} {vl u' : ℤ × ℤ}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hnc : ∃ z₁ ∈ Sw, ∃ z₂ ∈ Sw, det z₁ vl ≠ det z₂ vl)
    (hBfin : B.Finite) :
    ∃ K : ℤ, ∀ a ∈ Sw,
      (∀ b ∈ Sw, dot (expNormal (u' - K • vl) vl) a ≤ dot (expNormal (u' - K • vl) vl) b) →
      ∀ b₀ ∈ B, ∀ enum : ℕ → ℕ → ℤ × ℤ,
        (∀ i j : ℕ, ∀ z ∈ Sw.erase a,
          z + (enum i j - a) ∈
            halfStrip B vl ∪ (⋃ i' ∈ {i' | i' < i}, Set.range (enum i'))
              ∪ (enum i '' {j' | j' < j})) →
        ¬ chainFull B vl (u' - K • vl) b₀ 0 ⊆ halfStrip B vl ∪ (⋃ i, Set.range (enum i)) := by
  rcases hunimod with hpos | hneg
  · obtain ⟨K, hK⟩ :=
      Nivat.ColleReg.exists_shear_argmin_not_detMax (Sw := Sw) (u' := u') (vl := vl)
        (Or.inl hpos) hnc
    refine ⟨K, fun a ha hamin b₀ hb₀ enum hwin hKsub => ?_⟩
    obtain ⟨z, hz, hδ⟩ := hK a ha hamin
    exact false_of_hwin_hK_of_det_pos hBfin hb₀
      (by rw [det_shear_vl]; exact hpos) enum hz hδ hwin hKsub
  · obtain ⟨K, hK⟩ :=
      Nivat.ColleReg.exists_shear_argmin_not_detMin (Sw := Sw) (u' := u') (vl := vl)
        (Or.inr hneg) hnc
    refine ⟨K, fun a ha hamin b₀ hb₀ enum hwin hKsub => ?_⟩
    obtain ⟨z, hz, hδ⟩ := hK a ha hamin
    exact false_of_hwin_hK_of_det_neg hBfin hb₀
      (by rw [det_shear_vl]; exact hneg) enum hz hδ hwin hKsub


/-! ## §20 — the corner-shear route to `hbase` is dead **at the shear** (2026-09-20)

§19 left one question open: `wedgeResidualR_of_hwinHoleZ` does not get to choose `K`, it
receives the single `K` produced by `L1StraddleWedge.exists_corner_shear` (`:424`).  §19's
refutation ranges over *all* `K`, so it does not settle whether *that* `K` happens to land on
the sound side.

It does not.  Two facts, both kernel-checked in `MaxIndexProbe.lean` (Lstrad, 2026-09-20):

* `ColleReg.uCoord_zero_eq_det_mul_det` : `uCoord u' vl 0 z = det u' vl * det z vl`,
  unconditionally (it is `det_skew` plus `ring`).
* `ColleReg.exists_corner_shear_a_isMin_uCoordZero` : the vertex `a` that
  `exists_corner_shear` returns is the **global `uCoord u' vl 0`-minimiser** over `S`.  This
  is readable off the published conclusion (`0 ≤ uCoord (u' - K • vl) vl a b` for every
  `b ∈ S`, plus shear-invariance of `uCoord`), and the body confirms it: it is literally
  `S.exists_min_image (fun z => uCoord u' vl 0 z)` at `L1StraddleWedge.lean:428`.

Multiplying through: at `det u' vl = 1` the returned `a` is the `det · vl`-**minimum**, and at
`det u' vl = -1` it is the **maximum**.  §19's `detMax_of_hwin_hK` / `detMin_of_hwin_hK` need
exactly the opposite extreme in each case.  So the clash is not "for some `K`" — it is at the
one `K` the caller actually has, in both orientations.

⚠ **Reading limit (unchanged, and it matters).**  This refutes the *corner-shear route* to
`hbase`.  It does **not** refute `hbase`, it does **not** refute Collé's Lemma 4.5, and it
leaves §18's arbitrary-seed / flat route untouched — that route never calls
`exists_corner_shear`.  `sorry` count and `axiom_closure` are unchanged by this section. -/

/-- **The `K` from `exists_corner_shear` is always the wrong sign.**

At the `K` and vertex `a` that `L1StraddleWedge.exists_corner_shear` actually returns, no
`enum` satisfies `hwin ∧ hK` — in either orientation.  The `hnc` hypothesis is exactly the
non-degeneracy `Sw` is not `det · vl`-collinear; without it every extremality statement is
simultaneously true and there is nothing to clash. -/
theorem not_exists_enum_hwin_hK_at_corner_shear
    {Sw : Finset (ℤ × ℤ)} (hSw : Sw.Nonempty) {B : Set (ℤ × ℤ)} {vl u' b₀ : ℤ × ℤ}
    (hBfin : B.Finite) (hb₀ : b₀ ∈ B)
    (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hnc : ∃ z₁ ∈ Sw, ∃ z₂ ∈ Sw, det z₁ vl ≠ det z₂ vl) :
    ∃ K : ℤ, ∃ a ∈ Sw,
      (∀ b ∈ Sw, Nivat.L1Line0.uCoord u' vl 0 a ≤ Nivat.L1Line0.uCoord u' vl 0 b) ∧
      ∀ enum : ℕ → ℕ → ℤ × ℤ,
        (∀ i j : ℕ, ∀ z ∈ Sw.erase a,
          z + (enum i j - a) ∈
            halfStrip B vl ∪ (⋃ i' ∈ {i' | i' < i}, Set.range (enum i'))
              ∪ (enum i '' {j' | j' < j})) →
        ¬ chainFull B vl (u' - K • vl) b₀ 0 ⊆ halfStrip B vl ∪ (⋃ i, Set.range (enum i)) := by
  obtain ⟨K, a, ha, hmin⟩ :=
    Nivat.ColleReg.exists_corner_shear_a_isMin_uCoordZero hSw (u' := u') (vl := vl)
  refine ⟨K, a, ha, hmin, fun enum hwin hKsub => ?_⟩
  rcases hunimod with hpos | hneg
  · exact Nivat.ColleReg.corner_shear_a_not_detMax hmin hpos hnc ha
      (detMax_of_hwin_hK hBfin hb₀ (by rw [det_shear_vl]; exact hpos) enum hwin hKsub)
  · exact Nivat.ColleReg.corner_shear_a_not_detMin hmin hneg hnc ha
      (detMin_of_hwin_hK hBfin hb₀ (by rw [det_shear_vl]; exact hneg) enum hwin hKsub)


/-! ## Axiom receipt

Deletable block (hard rule 3): the headline claims of this file, checked by the kernel at build
time rather than asserted in prose. -/

/-! ## §21  `HwinHoleZ` is **false** at every Case 1 instance, not merely unproduced

§20 refutes the inner existential at the *one* shear `exists_corner_shear` returns, which is a
statement about that producer.  This section upgrades it to a statement about the hole itself.

The lever is the quantifier order in `HwinHoleZ` (`:849`): after `∃ u'`, the shear `K` is
**universally** quantified (`∀ (B) (u) (c) (a) (K : ℤ)`).  So the hole promises an enumeration at
*every* shear, and `not_exists_enum_hwin_hK_of_shear` (`:1479`) exhibits one shear at which no
enumeration exists — and does so for **every** `hamin`-vertex `a` (`∀ a ∈ Sw`, not some `a`), in
`HwinHoleZ`'s own `dot (expNormal (u' - K • vl) vl)` form rather than the `uCoord` form of §20.
That is precisely the shape needed: one bad `K` refutes a `∀ K` promise.

The remaining side conditions are the Case 1 data itself, taken in exactly the form
`wedgeResidualR_of_hwinHoleZ` takes them: `B`/`u`/`c`/`hD` from `exists_hD_of_case1`, finiteness
from `finite_of_envOf_Sphi`, the vertex and `LatticeConvex (Sw.erase a)` from
`exists_vertex_of_generating_dir` at the sheared direction, and `hnc` from
`HbaseFlatSeed.exists_hnc_of_decompData_det`, which holds **unconditionally** on `d.Sphi`.

**Reading limit.**  This kills `HwinHoleZ` *as written*.  It does **not** say that no
corner/window route exists: a hole that bundles `K` existentially (with the matching corner data,
since the extremal direction depends on `K`) is a different proposition, and nothing here
refutes it.  The proof below consumes `∀ K` at one specific `K`; against an `∃ K` form there is
no such step. -/
theorem not_hwinHoleZ_of_case1
    {ξ xper : Config ℤ} {vl p : ℤ × ℤ} (d : Nivat.Colle35.DecompDataZ ξ)
    (hcase1 : Case1 ξ xper d.Sphi vl)
    (hvl_prim : Primitive vl) (hp_mem : p ∈ Per xper) (hp_ne : p ≠ 0)
    (hdet_vl : det p vl = 0) :
    ¬ HwinHoleZ ξ d.Sphi vl := by
  rintro ⟨u', hunimod, hhole⟩
  obtain ⟨B, hEnv, u, c, hc, _hper, _hu, hD⟩ :=
    Nivat.L1Line0.exists_hD_of_case1 hcase1 hvl_prim hp_mem hp_ne hdet_vl
  have hBfin : B.Finite :=
    Nivat.HbaseFlatSeed.finite_of_envOf_Sphi d.toDecompData hEnv
  have hnc : ∃ z₁ ∈ d.Sphi, ∃ z₂ ∈ d.Sphi, det z₁ vl ≠ det z₂ vl :=
    Nivat.HbaseFlatSeed.exists_hnc_of_decompData_det d.toDecompData (u' := u')
      hvl_prim.ne_zero hunimod
  obtain ⟨K, hK⟩ :=
    not_exists_enum_hwin_hK_of_shear (Sw := d.Sphi) (u' := u') hunimod hnc hBfin
  have hunimod' : det (u' - K • vl) vl = 1 ∨ det (u' - K • vl) vl = -1 := by
    rw [det_shear_vl]; exact hunimod
  have hw0 : expNormal (u' - K • vl) vl ≠ 0 := by
    intro h
    have := Nivat.ColleReg.dot_expNormal_vl hunimod'
    rw [h] at this
    simp [Nivat.LE2.dot] at this
  obtain ⟨a, ha, hamin, hconvS, _hgen⟩ :=
    Nivat.ColleReg.exists_vertex_of_generating_dir hw0 d.isGeneratingSet
  obtain ⟨b₀, hb₀, enum, hwin, hKsub⟩ := hhole B u c a K ha hconvS hc hBfin hEnv hamin hD
  exact hK a ha hamin b₀ hb₀ enum hwin hKsub

/-! ## §22  A shear at which the `hamin` vertex **is** the `det · vl`-maximum

§19–§21 all run one way: `detMax_of_hwin_hK` says `hwin + hK` force the `hamin` vertex to be the
`det · vl`-maximum, and `exists_shear_argmin_not_detMax` (`MaxIndexProbe.lean:1233`) exhibits a
shear at which it provably is *not* — contradiction, route dead.

This section supplies the missing mirror.  Write `g K z := det u' z + K * det z vl`; at
`det u' vl = 1` the `hamin` functional is exactly `g K` (`dot_expNormal_eq_det_mul_det` plus
`det_shear_vl`).  As `K → +∞` the argmin of `g K` is dragged to the `det · vl`-**minimum** — that
is the lever `exists_shear_argmin_not_detMax` pulls.  As `K → -∞` it is dragged to the
`det · vl`-**maximum**, which is the end `detMax_of_hwin_hK` wants.  Taking `K := -(2M+2)` with
`M` a bound on `|det u' ·|` over `Sw` makes the second cheap: a competitor with strictly larger
`det · vl` gains at least `2M + 2` on the `K`-term and can lose at most `2M` on the other.

**What this does and does not say.**  It says the extremality obstruction behind §19–§21 is an
artefact of *which* shear one picks, not a fact about all shears — so a hole that gets to choose
`K` (`HwinHoleK.lean`) is not refutable by that argument.  It does **not** produce `hwin`, `hK`,
or any enumeration: the hole's actual content is untouched.  All this removes is the reason the
hole was impossible. -/
theorem dot_expNormal_eq_det_mul_det (p q z : ℤ × ℤ) :
    dot (expNormal p q) z = det p q * det p z := by
  simp only [Nivat.LE2.dot, expNormal, det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

theorem det_shear_apply (u' vl z : ℤ × ℤ) (K : ℤ) :
    det (u' - K • vl) z = det u' z + K * det z vl := by
  simp only [det, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

theorem exists_shear_argmin_detMax
    {Sw : Finset (ℤ × ℤ)} (hSw : Sw.Nonempty) {u' vl : ℤ × ℤ} (hdet : det u' vl = 1) :
    ∃ K : ℤ, ∃ a ∈ Sw,
      (∀ b ∈ Sw, dot (expNormal (u' - K • vl) vl) a ≤ dot (expNormal (u' - K • vl) vl) b) ∧
      (∀ z ∈ Sw, det z vl ≤ det a vl) := by
  classical
  set Mn : ℕ := Sw.sup (fun z => (det u' z).natAbs) with hMn
  set K : ℤ := -(2 * (Mn : ℤ) + 2) with hKdef
  -- The `hamin` functional at the sheared direction is `g K`.
  have hfun : ∀ z : ℤ × ℤ,
      dot (expNormal (u' - K • vl) vl) z = det u' z + K * det z vl := by
    intro z
    rw [dot_expNormal_eq_det_mul_det, det_shear_vl, hdet, one_mul, det_shear_apply]
  obtain ⟨a, ha, hmin⟩ :=
    Sw.exists_min_image (fun z => dot (expNormal (u' - K • vl) vl) z) hSw
  refine ⟨K, a, ha, hmin, fun z hz => ?_⟩
  by_contra hlt
  push_neg at hlt
  -- `|det u' ·|` is bounded by `Mn` on `Sw`, for both competitors.
  have hbz : (det u' z).natAbs ≤ Mn := by
    have h := Finset.le_sup (f := fun w => (det u' w).natAbs) hz
    simpa [hMn] using h
  have hba : (det u' a).natAbs ≤ Mn := by
    have h := Finset.le_sup (f := fun w => (det u' w).natAbs) ha
    simpa [hMn] using h
  have hstep : dot (expNormal (u' - K • vl) vl) z
      < dot (expNormal (u' - K • vl) vl) a := by
    rw [hfun, hfun, hKdef]
    have hbz' : -(Mn : ℤ) ≤ det u' z ∧ det u' z ≤ (Mn : ℤ) := by omega
    have hba' : -(Mn : ℤ) ≤ det u' a ∧ det u' a ≤ (Mn : ℤ) := by omega
    have hD : 1 ≤ det z vl - det a vl := by omega
    nlinarith [hbz'.1, hbz'.2, hba'.1, hba'.2, hD, Int.ofNat_nonneg Mn]
  exact absurd (hmin z hz) (not_le.mpr hstep)

/-- **The composable form of §22.**  `exists_shear_argmin_detMax` picks its own vertex, but on the
chain the vertex is not ours to pick — it comes from `exists_vertex_of_generating_dir`, which
also supplies `LatticeConvex (Sw.erase a)`.  This version therefore takes the `hamin` vertex as a
hypothesis and shows that *any* such vertex is the `det · vl`-maximum, provided the shear is at
least as negative as the threshold.

That is what lets it meet `HwinHoleK` (`HwinHoleK.lean`), whose `∃ K a` bundle carries `hconvS`
alongside `hamin`: choose `K` below the threshold, take the vertex from
`exists_vertex_of_generating_dir` at the sheared direction, and this lemma supplies the
extremality that `detMax_of_hwin_hK` (§19) would otherwise contradict. -/
theorem detMax_of_hamin_of_shear_le
    {Sw : Finset (ℤ × ℤ)} {u' vl a : ℤ × ℤ} (hdet : det u' vl = 1) {K : ℤ}
    (hK : K ≤ -(2 * ((Sw.sup (fun z => (det u' z).natAbs) : ℕ) : ℤ) + 2))
    (ha : a ∈ Sw)
    (hamin : ∀ b ∈ Sw, dot (expNormal (u' - K • vl) vl) a
      ≤ dot (expNormal (u' - K • vl) vl) b) :
    ∀ z ∈ Sw, det z vl ≤ det a vl := by
  classical
  intro z hz
  by_contra hlt
  push_neg at hlt
  have hfun : ∀ w : ℤ × ℤ,
      dot (expNormal (u' - K • vl) vl) w = det u' w + K * det w vl := by
    intro w
    rw [dot_expNormal_eq_det_mul_det, det_shear_vl, hdet, one_mul, det_shear_apply]
  set Mn : ℕ := Sw.sup (fun w => (det u' w).natAbs) with hMn
  have hbz : (det u' z).natAbs ≤ Mn := by
    have h := Finset.le_sup (f := fun w => (det u' w).natAbs) hz
    simpa [hMn] using h
  have hba : (det u' a).natAbs ≤ Mn := by
    have h := Finset.le_sup (f := fun w => (det u' w).natAbs) ha
    simpa [hMn] using h
  have hcmp := hamin z hz
  rw [hfun, hfun] at hcmp
  have hbz' : -(Mn : ℤ) ≤ det u' z ∧ det u' z ≤ (Mn : ℤ) := by omega
  have hba' : -(Mn : ℤ) ≤ det u' a ∧ det u' a ≤ (Mn : ℤ) := by omega
  have hD : 1 ≤ det z vl - det a vl := by omega
  have hKneg : K ≤ 0 := by omega
  -- `K * (det z vl - det a vl) ≤ K` because the gap is at least `1` and `K ≤ 0`.
  have hprod : K * (det z vl - det a vl) ≤ K := by nlinarith [hD, hKneg]
  nlinarith [hbz'.1, hbz'.2, hba'.1, hba'.2, hprod, hcmp]

/-- **The unimodular form of §22 — the one the chain can actually apply.**
`detMax_of_hamin_of_shear_le` covers only `det u' vl = 1`, but on the chain `hunimod` is always
the disjunction `det u' vl = 1 ∨ det u' vl = -1`, so half the compositions would block on it.

The two branches need shears of *opposite sign*: at `det u' vl = 1` the `hamin` functional is
`+(det u' z + K * det z vl)` and `K` must go to `-∞`; at `det u' vl = -1` it is negated, so `K`
must go to `+∞`.  Writing the threshold as `det u' vl * K ≤ -(2M + 2)` covers both at once —
the product is what has to be very negative, not `K` itself. -/
theorem detMax_of_hamin_of_shear_unimod
    {Sw : Finset (ℤ × ℤ)} {u' vl a : ℤ × ℤ}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) {K : ℤ}
    (hK : det u' vl * K ≤ -(2 * ((Sw.sup (fun z => (det u' z).natAbs) : ℕ) : ℤ) + 2))
    (ha : a ∈ Sw)
    (hamin : ∀ b ∈ Sw, dot (expNormal (u' - K • vl) vl) a
      ≤ dot (expNormal (u' - K • vl) vl) b) :
    ∀ z ∈ Sw, det z vl ≤ det a vl := by
  classical
  rcases hunimod with h1 | h1
  · exact detMax_of_hamin_of_shear_le h1 (by rw [h1] at hK; linarith) ha hamin
  · intro z hz
    by_contra hlt
    push_neg at hlt
    have hfun : ∀ w : ℤ × ℤ,
        dot (expNormal (u' - K • vl) vl) w = -(det u' w + K * det w vl) := by
      intro w
      rw [dot_expNormal_eq_det_mul_det, det_shear_vl, h1, det_shear_apply]
      ring
    set Mn : ℕ := Sw.sup (fun w => (det u' w).natAbs) with hMn
    have hbz : (det u' z).natAbs ≤ Mn := by
      have h := Finset.le_sup (f := fun w => (det u' w).natAbs) hz
      simpa [hMn] using h
    have hba : (det u' a).natAbs ≤ Mn := by
      have h := Finset.le_sup (f := fun w => (det u' w).natAbs) ha
      simpa [hMn] using h
    have hcmp := hamin z hz
    rw [hfun, hfun] at hcmp
    have hbz' : -(Mn : ℤ) ≤ det u' z ∧ det u' z ≤ (Mn : ℤ) := by omega
    have hba' : -(Mn : ℤ) ≤ det u' a ∧ det u' a ≤ (Mn : ℤ) := by omega
    have hD : 1 ≤ det z vl - det a vl := by omega
    -- At `det u' vl = -1` the threshold reads `-K ≤ -(2M+2)`, i.e. `K` is large *positive*.
    have hKpos : 2 * (Mn : ℤ) + 2 ≤ K := by rw [h1] at hK; linarith
    have hprod : K ≤ K * (det z vl - det a vl) := by nlinarith [hD, hKpos]
    nlinarith [hbz'.1, hbz'.2, hba'.1, hba'.2, hprod, hcmp]

/-! ## §23 — the refutation collapses the whole ladder below it

`HwinHoleZ ξ Sw vl` is not a new proposition: comparing `:853-865` with `:626-638` binder by
binder, it is *syntactically* `HwinHoleE ξ Sw Sw vl` — the `E` form's two set parameters
specialised to the same set (`a ∈ S` / `LatticeConvex (S.erase a)` / `z ∈ S.erase a` on one side,
`EnvOf Sphi B` on the other, all at `Sw`).  So `Iff.rfl` proves them equivalent.

That matters because `hwinHoleE_of_hwinHole` (`:643`) holds *for every* `Sphi`.  Instantiating it
at `Sphi := S := d.Sphi` turns §21's refutation of `HwinHoleZ` into a refutation of `HwinHole`
itself.  Concretely, on the chain all three of

  `wedgeResidualR_of_hwinHole` (`:503`), `wedgeResidualR_of_hwinHoleE` (`:654`),
  `wedgeResidualR_of_hwinHoleZ` (`:873`)

are vacuous, not just the last.  The ladder was built by successively weakening the hypothesis
until someone could prove it; §21 says the weakest rung is already false, so weakening further
along this axis cannot help.

⚠ **Reading limit.**  This says nothing about `HwinHoleK` (`HwinHoleK.lean`), which moves `K`
from `∀` to `∃` — a different axis, and §22 shows the §21 argument provably cannot be replayed
against it.  Nor does it touch `wedgeResidualR_of_hwin` (`:341`) or
`wedgeResidualR_of_hwin_corner_place` (`:235`), whose hypotheses are not holes of this family. -/

theorem hwinHoleZ_iff_hwinHoleE (ξ : Config ℤ) (Sw : Finset (ℤ × ℤ)) (vl : ℤ × ℤ) :
    HwinHoleZ ξ Sw vl ↔ HwinHoleE ξ Sw Sw vl := Iff.rfl

theorem not_hwinHoleE_of_case1
    {ξ xper : Config ℤ} {vl p : ℤ × ℤ} (d : Nivat.Colle35.DecompDataZ ξ)
    (hcase1 : Case1 ξ xper d.Sphi vl)
    (hvl_prim : Primitive vl) (hp_mem : p ∈ Per xper) (hp_ne : p ≠ 0)
    (hdet_vl : det p vl = 0) :
    ¬ HwinHoleE ξ d.Sphi d.Sphi vl := fun h =>
  not_hwinHoleZ_of_case1 d hcase1 hvl_prim hp_mem hp_ne hdet_vl
    ((hwinHoleZ_iff_hwinHoleE ξ d.Sphi vl).mpr h)

theorem not_hwinHole_of_case1
    {ξ xper : Config ℤ} {vl p : ℤ × ℤ} (d : Nivat.Colle35.DecompDataZ ξ)
    (hcase1 : Case1 ξ xper d.Sphi vl)
    (hvl_prim : Primitive vl) (hp_mem : p ∈ Per xper) (hp_ne : p ≠ 0)
    (hdet_vl : det p vl = 0) :
    ¬ HwinHole ξ d.Sphi vl := fun h =>
  not_hwinHoleE_of_case1 d hcase1 hvl_prim hp_mem hp_ne hdet_vl
    (hwinHoleE_of_hwinHole h)

/-- **§23, continued: `wedgeResidualR_of_hwin` falls too, at `S = d.Sphi`.**

Comparing `:487-499` with the `hwin_hole` binder of `wedgeResidualR_of_hwin` (`:349-362`), the pair
`⟨hunimod, hwin_hole⟩` at set `S` *is* `HwinHole ξ S vl` — same binders, same `coverEnum`
hard-wiring, same conclusion.  So at `S := d.Sphi` the hypothesis is refuted outright.

That makes **four** of the six `wedgeResidualR` producers vacuous on the chain:
`_of_hwin` (`:341`), `_of_hwinHole` (`:503`), `_of_hwinHoleE` (`:654`), `_of_hwinHoleZ` (`:873`).

⚠ **Two limits.**  (1) This is stated at `S = d.Sphi`; `wedgeResidualR_of_hwin` takes a general
`S` with `hSgen : IsGeneratingSet ξ S`, so a consumer calling it at some *other* generating set is
not covered — but `exists_wedgeResidualR` is the only consumer and `hcase1` pins the sweep set to
`d.Sphi`.  (2) `wedgeResidualR_of_case1_holes` (`:111`) and `wedgeResidualR_of_hwin_corner_place`
(`:235`) are still untouched by any of this. -/
theorem not_hwin_hole_arg_of_case1
    {ξ xper : Config ℤ} {vl p u' : ℤ × ℤ} (d : Nivat.Colle35.DecompDataZ ξ)
    (hcase1 : Case1 ξ xper d.Sphi vl)
    (hvl_prim : Primitive vl) (hp_mem : p ∈ Per xper) (hp_ne : p ≠ 0)
    (hdet_vl : det p vl = 0)
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) :
    ¬ (∀ (B : Set (ℤ × ℤ)) (u : ℤ × ℤ) (c : ℤ) (a : ℤ × ℤ) (K : ℤ),
        a ∈ d.Sphi → Nivat.LatticeConvex (d.Sphi.erase a) → 0 < c →
        B.Finite →
        (∀ b ∈ d.Sphi, dot (expNormal (u' - K • vl) vl) a
          ≤ dot (expNormal (u' - K • vl) vl) b) →
        (∀ z ∈ halfStrip B vl, (T u ξ) z = T (c • vl) (T u ξ) z) →
        ∃ b₀ ∈ B,
          ∀ i j : ℕ, ∀ z ∈ d.Sphi.erase a,
            z + (coverEnum vl (u' - K • vl) b₀ i j - a) ∈
              halfStrip B vl ∪
                (⋃ i' ∈ {i' | i' < i}, Set.range (coverEnum vl (u' - K • vl) b₀ i')) ∪
                (coverEnum vl (u' - K • vl) b₀ i '' {j' | j' < j})) := fun h =>
  not_hwinHole_of_case1 d hcase1 hvl_prim hp_mem hp_ne hdet_vl ⟨u', hunimod, h⟩

section AxiomReceipts

#print axioms wedgeResidualR_of_case1_holes
#print axioms wedgeResidualR_of_hwin_corner_place
#print axioms wedgeResidualR_of_hwin
#print axioms le_dot_expNormal_of_mem_cumSweep
#print axioms not_hinv_cumSweep
#print axioms wedgeResidualR_of_hwinHole
#print axioms ofSweepEnum
#print axioms hwinHoleE_of_hwinHole
#print axioms wedgeResidualR_of_hwinHoleE
#print axioms halfStrip_level_finite
#print axioms not_hwin_of_row_zero_levelConst
#print axioms not_hwin_of_row_zero_levelConst_envOf
#print axioms wedgeResidualR_of_hwinHoleZ
#print axioms det_eq_of_mem_halfStrip
#print axioms exists_mem_halfStrip_of_hwin
#print axioms exists_det_eq_of_hwin
#print axioms det_le_of_hwin
#print axioms det_add_zsmul
#print axioms exists_mem_seed_of_hwin
#print axioms det_le_of_hwin_of_seed_le
#print axioms le_det_of_hwin_of_le_seed
#print axioms false_of_hwin_hK_of_seed_le
#print axioms false_of_hwin_hK_of_le_seed
#print axioms not_bddAbove_det_seed_of_hwin_hK
#print axioms not_bddBelow_det_seed_of_hwin_hK
#print axioms bddAbove_det_halfStrip
#print axioms bddBelow_det_halfStrip
#print axioms le_det_of_hwin
#print axioms det_le_on_chainFull_of_hwin_hK
#print axioms mem_chainFull_zero_ray
#print axioms det_ray
#print axioms false_of_hwin_hK_of_det_pos
#print axioms false_of_hwin_hK_of_det_neg
#print axioms det_shear_vl
#print axioms detMax_of_hwin_hK
#print axioms detMin_of_hwin_hK
#print axioms not_exists_enum_hwin_hK_of_shear
#print axioms not_exists_enum_hwin_hK_at_corner_shear
#print axioms not_hwinHoleZ_of_case1
#print axioms dot_expNormal_eq_det_mul_det
#print axioms det_shear_apply
#print axioms exists_shear_argmin_detMax
#print axioms detMax_of_hamin_of_shear_le
#print axioms detMax_of_hamin_of_shear_unimod
#print axioms hwinHoleZ_iff_hwinHoleE
#print axioms not_hwinHoleE_of_case1
#print axioms not_hwinHole_of_case1
#print axioms not_hwin_hole_arg_of_case1

end AxiomReceipts

end Nivat.L1SweepBridge
