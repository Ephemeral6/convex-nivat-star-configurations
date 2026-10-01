/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.EscapeW
import Nivat.External.Colle.TowerHbaseUnitSweep

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# `htile` — a translate of `𝒮_φ` inside `Â_∞` (lane-tower-hlev)

`htile` is the last zero-producer premise of `Nivat.TowerHbase.bottom_conj123`
(module `TowerHbaseUnitSweep`), which discharges `ChainDataGeomParts.bottom`'s conjuncts
1–3.  Measured verbatim from that theorem's binder list:

```
{Ah : Set (ℤ × ℤ)} {S : Finset (ℤ × ℤ)} {wS : ℤ × ℤ}
htile : ∀ b ∈ S, b + wS ∈ Ah
```

`wS` is an **implicit binder of the theorem, not an `∃`**, so what a producer owes is the
existential closure `∃ wS, ∀ b ∈ S, b + wS ∈ Ah`, at `Ah := ⋃ i, hatOf A kk vl i`.  In words:
some translate of the window fits inside `Â_∞`.

## What this file does

* §1 the engine: a lattice-convex region closed under **two ℝ-independent** integer
  translations contains a translate of every finite set.  Built on
  `Nivat.exists_global_extension` (module `Section8.HalfPlane`), whose Part 1 is exactly
  "every `z` is carried into `R` by all large multiples of `h + h'`"; the two
  configuration-agreement conjuncts of `Nivat.FullyPeriodicOnWith` are met by the constant
  configuration `fun _ => (0 : ℕ)`, so no periodicity is used — only the recession geometry.
* §2 a cone-closure lemma from `hswept` + `rec_p` alone (no `bottom`), giving a second
  translation direction, and §3 the resulting `htile` producer.
* §4 the chain parametrisation, and §5 conjuncts 1–3 with `htile` discharged.
* §6 rigs: satisfiability of both premise tables, plus a kernel witness that lattice
  convexity is load-bearing.

## ⚠ Two accounting facts a reader must not skip

1. **The obvious route is circular.**  `Â_∞` is closed under `+vJ` (`rec_vJ`) and under `+p`
   (`rec_p`), and those two are independent (`dot nJ vJ = 0`, `dot nJ p ≠ 0`), so §1 applies
   at once.  But the chain-side producer of `rec_vJ` — `rec_vJ_of_parts`
   (module `RecVJFromParts`) — goes through `c.bottom`, and `htile` is a premise of
   `bottom`'s conjuncts 1–3.  So §1 + `rec_vJ` is **not** usable to build `bottom`.
   `exists_tile_of_rec_vJ` (§1) is therefore stated with `rec_vJ` as a binder and is for
   consumers that already have `bottom`.
2. ⛔ **The `det p vJ1 ≠ 0` route is dead — read §7 before using §2/§3.**  §2/§3 replace
   `rec_vJ` by `hswept` + `rec_p`, which are fields and do not pass through `bottom`.  The two
   directions produced are `p` and `Q•p + P•vJ1` (`P := ⟪nJ,p⟫ > 0`, `Q := −⟪nJ,vJ1⟫ > 0`),
   whose determinant is `P · det p vJ1`, so the cone collapses to a line exactly when
   `p ∥ vJ1`.  **On the chain it always does**: `p = -(c : ℤ) • vl` (`exists_chainData`'s
   `hp_neg`) and `vJ1 = m • vl` (the 226-round collinearity ruling) give
   `det p vJ1 = 0` outright (`GcdCollapse.det_p_vJ1_zero`).  ⟹ `hindep : det p vJ1 ≠ 0` is
   **unsatisfiable on the chain**, not merely unproved, and `exists_tile_of_swept` /
   `exists_tile_of_parts_binders` are vacuous there.  `not_indep_of_antiparallel` (§6) is the
   minimal instance of that collapse.
   ⟹ **the live route is §7**: take `vJ` rather than `vJ1` as the second direction.  Then
   independence is free (`det_vJ_vl_ne_zero_of_chain`, from `dot nJ vJ = 0` + `vJ ≠ 0` +
   `dot nJ p ≠ 0` + `hp_neg`), and §5's `bottom_conj123_of_tile` carries `hvJne : vJ ≠ 0`
   (field `vJ_prim`) in place of `hindep`.  §8 records the same collapse killing `hcomb`,
   the side condition of the `bottom`-free producer `RecVJComb.parts_rec_vJ`.

## Two other routes to `htile`, found by scanning and **not** taken

* **Minkowski reconstruction.**  `Nivat.LE2.shift_subset_iff_suppVal_le` (module
  `EnvTranslate`) already reduces "a translate of `U` fits inside `T`" to the finite integer
  system `forall n in E T, suppVal U n + dot n v <= suppVal T n`, and that file's §4 records
  that `Enveloped U T -> exists v, shift v U subseteq T` needs the Minkowski summand
  reconstruction, declaring it true but unproved.  `Enveloped (up S) (Ahat i)` does hold
  layerwise (`envA_of_max` + `envShift`), so this route would reach `htile` with no `hindep`
  and no `hswept` — at the price of the reconstruction.
  ⛔ **Not available.**  The reconstruction falls under the `CORE-HOLES.md` ruling
  "Minkowski 重建不立项", so this is a **closed** route, not an unassigned one.
  (`EnvTranslate`'s §4 used to give "this file has no consumer" as the reason it was
  unassigned; that accounting is stale and has been corrected in place to cite the ruling.)
* **Half-plane exhaustion.**  `Nivat.RecVJ.iUnion_hatOf_eq_halfPlane` (module `RecVJ`) makes
  `⋃ i, hatOf A kk vl i` *equal* to a half-plane, which would make `htile` immediate.
  ⚠ **Corrected in §9**: of its five premises, **four are produced by one call** to
  `Nivat.ItemIIChain.exists_itemII_chain` (`hlev` / `subBA` / `subAB` and `hbox` verbatim), so
  `hbox` is **not** a residual.  The whole residual is `hkk`, a sublinear-growth condition on
  `kk` that the chain's own producer `Nivat.ChainKK.exists_normalised_chain` does not give —
  it gives only monotonicity, and monotone ⇏ `hkk` (`hkk_not_from_monotone`, §9).
  ⚠ This route is also strictly stronger than `:506`, which calls `Â_∞` an `(ℓ,ℓ_J)`-region
  with two semi-infinite edges rather than a half-plane; given the other four premises `hkk`
  is *equivalent* to the half-plane equality, so a consumer owes that discrepancy an
  explanation.  Not used here.

## Paper

* `scratch/b3_colle2.txt:498` — "Since `⋃_{i=1}^{∞} A_i = H(ℓ^{(-)})`".  This is the nearest
  source content: for the **un-hatted** union `htile` is immediate, a half-plane containing a
  translate of any finite set.  Our `Ah` is the **hatted** union `Â_∞ = ⋃ (A_i − k_i v⃗_ℓ)`,
  which `:506` calls an `(ℓ,ℓ_J)`-region with two semi-infinite edges — two-dimensional and
  unbounded, but not a half-plane.  The `k_i`-shift is the entire gap between `:498` and
  `htile`.
* ⚠ `htile` itself has **no verbatim source sentence**, and neither do `bottom`'s conjuncts
  1–2 (hbase's own ⚠ at the head of `TowerHbaseUnitSweep`, measured against
  `b3_colle2.txt:518-520`).  Per hbase's `exists_eps_bottom_conj123`, the `∀ ε` in the field
  `bottom` is ours; `htile` is a premise of the `∀ ε` form and of the `∃ ε` form alike, so it
  is **not** charged to that added quantifier.  Nothing below claims a source for it.
* ⛔ `hadj : det vJ vJ1 = ±1` is untouched here — deriving it is banned (`CORE-HOLES.md`, the
  "不许去证 `det J ν_{J+1} = 1`" entry).  §5 carries it as a binder, exactly as
  `bottom_conj123_of_adjacent` does.

## ⚠ This file was withdrawn once and reinstated — read before re-withdrawing it

The integrator retracted the `htile` dispatch on the ground that `htile` has no verbatim
source sentence (that is still true — see the ⚠ above), and the file was parked out of the
build.  **The retraction was then withdrawn**, because "no source sentence" does not imply
"nobody should prove it": `htile` is a **consequence of the field table**, not a
transcription of the paper, and the same shape already exists on the tree as
`HsuppContain.hcont` (module `HsuppContain`).

The proposed replacement route was also unsound, which is the second reason this file stands:
it would have had `Colle37.GenClosure` (module `GenClosureDef`) supply `htile`, but that
inductive's only entry constructor is `base : z ∈ D → GenClosure S D z`, so it produces
*closure* facts and can never produce a membership in the union; its `step` additionally
carries `S.erase a`, and its ambient set is `Â_i ∪ Â_{i₀}^{(ε)}`, not `Â_∞`.
⟹ `bottom_conj123` keeps its `htile` binder and §5 below stays type-correct.
-/

namespace Nivat.LaneTowerHlevTile

open Nivat Nivat.LE2 Nivat.MaxEnv Nivat.Colle35

/-! ## §1  The engine: two independent recurrence directions tile any finite set

The only geometry used is the recession cone of `conv(R)`.  `Nivat.exists_global_extension`
takes a `Nivat.FullyPeriodicOnWith G R h h'`, whose five conjuncts are `det h h' ≠ 0`,
the two translation-invariances, and two agreement conditions on `G`; the last two are
discharged by a constant configuration, and `mem_interior_recCone` (the part that does the
work) ignores them anyway. -/

/-- **Two independent integer translations force a tile.**  If a lattice-convex region `R`
is nonempty and closed under `+v` and `+w` with `det v w ≠ 0`, then every finite `S` has a
translate inside `R`.

The witness is a single large multiple of `v + w`: `Nivat.exists_global_extension`'s Part 1
gives a threshold `N₀ b` for each `b`, and `Finset.sup` makes it uniform over `S`. -/
theorem exists_tile_of_two_recurrences {R : Set (ℤ × ℤ)} {v w : ℤ × ℤ}
    (hlc : IsLatticeConvexRegion R) (hne : R.Nonempty)
    (hrecv : ∀ g ∈ R, g + v ∈ R) (hrecw : ∀ g ∈ R, g + w ∈ R)
    (hdet : det v w ≠ 0) (S : Finset (ℤ × ℤ)) :
    ∃ wS : ℤ × ℤ, ∀ b ∈ S, b + wS ∈ R := by
  classical
  have hfp : Nivat.FullyPeriodicOnWith (fun _ => (0 : ℕ) : Config ℕ) R v w :=
    ⟨hdet, hrecv, hrecw, fun _ _ => rfl, fun _ _ => rfl⟩
  have hpart1 := (Nivat.exists_global_extension (Or.inl hlc) hne hfp).1
  refine ⟨((S.sup fun b => (hpart1 b).choose : ℕ) : ℤ) • (v + w), fun b hb => ?_⟩
  exact (hpart1 b).choose_spec _ (Finset.le_sup (f := fun b => (hpart1 b).choose) hb)

/-- **The circular form, kept because it has non-`bottom` consumers.**  `rec_vJ` + `rec_p`
are independent as soon as `⟪nJ,vJ⟫ = 0`, `vJ ≠ 0`, `⟪nJ,p⟫ ≠ 0`
(`LaneTowerHlevEscPos.det_ne_zero_of_perp`).

⛔ **Do not use this to build `ChainDataGeomParts.bottom`**: the chain-side producer of
`rec_vJ` is `rec_vJ_of_parts` (module `RecVJFromParts`), which consumes `c.bottom`, while
`htile` is a premise of `bottom`'s conjuncts 1–3.  §3 is the non-circular route. -/
theorem exists_tile_of_rec_vJ {R : Set (ℤ × ℤ)} {vJ p nJ : ℤ × ℤ}
    (hlc : IsLatticeConvexRegion R) (hne : R.Nonempty)
    (rec_vJ : ∀ g ∈ R, g + vJ ∈ R) (rec_p : ∀ g ∈ R, g + p ∈ R)
    (hperp : dot nJ vJ = 0) (hvJne : vJ ≠ 0) (hp : dot nJ p ≠ 0)
    (S : Finset (ℤ × ℤ)) :
    ∃ wS : ℤ × ℤ, ∀ b ∈ S, b + wS ∈ R :=
  exists_tile_of_two_recurrences hlc hne rec_vJ rec_p
    (Nivat.LaneTowerHlevEscPos.det_ne_zero_of_perp hperp hvJne hp) S

/-! ## §2  A second direction from `hswept` + `rec_p`, without `bottom`

`MaxEnv.SweptClosed A v n c` (module `MaximalEnveloped`) is
`∀ g ∈ A, ∀ t : ℕ, c ≤ dot n (g + t • v) → g + t • v ∈ A` — the guard is on the **endpoint
only**.  So walking `a` steps of `p` (all inside `R` by `rec_p`) and then `t` steps of `vJ1`
stays inside `R` whenever the net level change is nonnegative.  This is
`Nivat.LaneTowerHbaseRecVJ.rec_of_comb` (module `RecVJComb`) with its `hcomb` deleted: that
theorem needed `vJ` to *be* such a combination, which is a Bézout condition; here the
combination is the conclusion, so there is no integrality side condition at all. -/

/-- **`R` is closed under `a•p + t•vJ1` whenever the level budget is nonnegative.**  No
primitivity, no `hperp`, no `bottom`. -/
theorem rec_comb_of_swept {U : Set (ℤ × ℤ)} {p vJ1 nJ : ℤ × ℤ} {cJ : ℤ}
    (hhp : ∀ g ∈ U, cJ ≤ dot nJ g)
    (hswept : MaxEnv.SweptClosed U vJ1 nJ cJ)
    (rec_p : ∀ g ∈ U, g + p ∈ U)
    (a t : ℕ) (hbudget : 0 ≤ (a : ℤ) * dot nJ p + (t : ℤ) * dot nJ vJ1) :
    ∀ g ∈ U, g + ((a : ℤ) • p + (t : ℤ) • vJ1) ∈ U := by
  intro g hg
  have h1 : g + (a : ℤ) • p ∈ U := Nivat.LaneTowerHlevEscPos.rec_iter rec_p a g hg
  have hlev : cJ ≤ dot nJ (g + (a : ℤ) • p + (t : ℤ) • vJ1) := by
    rw [Nivat.LaneTowerHlevEscPos.dot_add_esc, Nivat.LaneTowerHlevEscPos.dot_add_esc,
      Nivat.LaneTowerHlevEscPos.dot_zsmul_esc, Nivat.LaneTowerHlevEscPos.dot_zsmul_esc]
    have := hhp g hg
    linarith
  have h2 := hswept _ h1 t hlev
  rwa [add_assoc] at h2

/-- `det` of `p` against a combination `a•p + t•vJ1` is `t · det p vJ1`. -/
theorem hlev_det_comb (p vJ1 : ℤ × ℤ) (a t : ℤ) :
    det p (a • p + t • vJ1) = t * det p vJ1 := by
  simp only [det, Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add, smul_eq_mul]
  ring

/-! ## §3  The non-circular `htile` producer

Directions: `p` itself, and `Q•p + P•vJ1` with `P := ⟪nJ,p⟫`, `Q := −⟪nJ,vJ1⟫`, both `> 0`.
The budget of the second is `Q·P + P·(−Q) = 0`, so it is admissible, and its determinant
against `p` is `P · det p vJ1`.

`0 < ⟪nJ,p⟫` is **not** assumed: it is `LaneTowerHlevEscPos.dot_p_pos` (module `EscapeW`),
from `hhp` + `rec_p` + nonemptiness. -/

/-- ⭐ **`htile` from fields only, plus `det p vJ1 ≠ 0`.**  Every hypothesis except `hindep`
is a `ChainDataGeomParts` field (in union form): `hhp`, `hswept`, `rec_p`, `dot_nJ_p`,
`hsweep`, `ahat_nonempty`, and lattice convexity via `latticeConvex_of_parts`.

⛔ **`hindep` is unsatisfiable on the chain — do not build on this theorem.**
`GcdCollapse.det_p_vJ1_zero` gives `det p vJ1 = 0` from `p = -c • vl` (`RegionSteps`'
`exists_chainData` binder `hp_neg`) together with the collinearity ruling `vJ1 = m • vl`:
`p` and `vJ1` are multiples of the **same** `vl`.  So this is a true theorem with a false
antecedent on the chain, i.e. a 空载出口 (`PROTOCOL.md §40`/§41).  It is kept because
(i) it is the honest record of where the `hswept`-only route ends, and (ii) it is still a
theorem about arbitrary `U`.  **The live producer is §7's `exists_tile_of_parts_recvJ`**,
which uses `vJ` as the second direction and needs no determinant binder at all. -/
theorem exists_tile_of_swept {U : Set (ℤ × ℤ)} {p vJ1 nJ : ℤ × ℤ} {cJ : ℤ}
    (hlc : IsLatticeConvexRegion U) (hne : U.Nonempty)
    (hhp : ∀ g ∈ U, cJ ≤ dot nJ g)
    (hswept : MaxEnv.SweptClosed U vJ1 nJ cJ)
    (rec_p : ∀ g ∈ U, g + p ∈ U) (hp : dot nJ p ≠ 0)
    (hsweep : dot nJ vJ1 < 0) (hindep : det p vJ1 ≠ 0)
    (S : Finset (ℤ × ℤ)) :
    ∃ wS : ℤ × ℤ, ∀ b ∈ S, b + wS ∈ U := by
  have hP : 0 < dot nJ p := Nivat.LaneTowerHlevEscPos.dot_p_pos hne hhp rec_p hp
  obtain ⟨P, hPeq⟩ : ∃ P : ℕ, ((P : ℕ) : ℤ) = dot nJ p :=
    ⟨(dot nJ p).toNat, Int.toNat_of_nonneg hP.le⟩
  obtain ⟨Q, hQeq⟩ : ∃ Q : ℕ, ((Q : ℕ) : ℤ) = -dot nJ vJ1 :=
    ⟨(-dot nJ vJ1).toNat, Int.toNat_of_nonneg (by omega)⟩
  have hrec2 : ∀ g ∈ U, g + ((Q : ℤ) • p + (P : ℤ) • vJ1) ∈ U := by
    refine rec_comb_of_swept hhp hswept rec_p Q P ?_
    rw [hPeq, hQeq]
    have h0 : -dot nJ vJ1 * dot nJ p + dot nJ p * dot nJ vJ1 = 0 := by ring
    rw [h0]
  have hdet2 : det p ((Q : ℤ) • p + (P : ℤ) • vJ1) ≠ 0 := by
    rw [hlev_det_comb, hPeq]
    exact mul_ne_zero (by omega) hindep
  exact exists_tile_of_two_recurrences hlc hne rec_p hrec2 hdet2 S

/-! ## §4  The chain parametrisation

`Ah := ⋃ i, hatOf A kk vl i`; lattice convexity is
`ChainAsm.latticeConvex_iUnion_hatOf` at `Env := EnvOf ↑S`, exactly as in
`LaneLeafAGenRecVJ.latticeConvex_of_parts`. -/

/-- **`htile` on the chain, from the field table.**  Binder for binder these are
`ChainDataGeomParts`' `maxA` / `hfin` / `AhatMono` / `ahat_nonempty` / `hhp` / `hswept` /
`rec_p` / `dot_nJ_p` / `hsweep`, plus `hindep`.

⛔ Same caveat as `exists_tile_of_swept`: `hindep` is **unsatisfiable on the chain**
(`GcdCollapse.det_p_vJ1_zero`).  Use §7's `exists_tile_of_parts_recvJ` instead. -/
theorem exists_tile_of_parts_binders {α : Type*}
    (η xper : Config α) (vl p : ℤ × ℤ) (S : Finset (ℤ × ℤ))
    (B A : ℕ → Set (ℤ × ℤ)) (u : ℕ → ℤ × ℤ) (kk : ℕ → ℕ)
    (maxA : ∀ i, IsMaxEnvIn (EnvOf (↑S : Set (ℤ × ℤ))) (canonA η xper vl B u i) (A i))
    (hfin : ∀ i, (hatOf A kk vl i).Finite)
    (AhatMono : ∀ i j, i ≤ j → hatOf A kk vl i ⊆ hatOf A kk vl j)
    (vJ1 nJ : ℤ × ℤ) (cJ : ℤ)
    (ahat_nonempty : (⋃ i, hatOf A kk vl i).Nonempty)
    (hhp : ∀ i, hatOf A kk vl i ⊆ halfPlaneGE nJ cJ)
    (hswept : MaxEnv.SweptClosed (⋃ i, hatOf A kk vl i) vJ1 nJ cJ)
    (rec_p : ∀ g ∈ ⋃ i, hatOf A kk vl i, g + p ∈ ⋃ i, hatOf A kk vl i)
    (dot_nJ_p : dot nJ p ≠ 0) (hsweep : dot nJ vJ1 < 0)
    (hindep : det p vJ1 ≠ 0) :
    ∃ wS : ℤ × ℤ, ∀ b ∈ S, b + wS ∈ ⋃ i, hatOf A kk vl i :=
  exists_tile_of_swept
    (latticeConvex_iUnion_hatOf η xper vl S
      (EnvOf (↑S : Set (ℤ × ℤ))) B A u kk rfl maxA hfin AhatMono)
    ahat_nonempty (fun _ hg => Set.iUnion_subset hhp hg) hswept rec_p dot_nJ_p hsweep
    hindep S

/-! ## §5  `bottom`'s conjuncts 1–3 with `htile` discharged

`Nivat.TowerHbase.bottom_conj123_of_adjacent` (module `TowerHbaseUnitSweep`) minus its
`htile`.  `hadj` stays a binder: ⛔ deriving it is banned for every lane.

## ⛔ §5 is **not** the endpoint of conjuncts 1–3 — read this before citing it

`bottom_conj123_of_tile` below inherits `hadj : det vJ vJ1 = 1 ∨ det vJ vJ1 = -1` from
`bottom_conj123_of_adjacent`, and `hadj` is **refuted on the chain** (module
`CyclicOrderAdjRefute`); the integrator's standing ruling is that `hadj` "is a proposition
with a counterexample on the chain, which `bottom` never needed", and deriving it is banned.
⟹ the exit for conjuncts 1–3 is **not** through this theorem.

The `hadj`-free route is `Nivat.TowerHbaseRecP.bottom_conj123_of_rec_p_of_tile` (module
`TowerHbaseRecP`, lane-tower-hbase), whose second binder is **verbatim** the conclusion of
`exists_tile_of_swept` below.  It trades `hadj` for
`hcop : IsCoprime (dot nJ p) (dot nJ vJ1)`.  ⚠ `hcop` has **no source sentence** either — it
is lane-tower-hbase's own added debt, not a requirement read off `b3_colle2.txt`; anyone
citing it must carry that sentence.

⟹ **What this file contributes to conjuncts 1–3 is `exists_tile_of_swept` (§3), not §5.**
§5 is kept only because it is the shortest statement of "`htile` is gone", and because it
records the `hadj` obstruction at the exact place a reader would otherwise walk into it
(`PROTOCOL.md §40`: a dead route compiles and has clean axioms just like a live one). -/

/-- ⭐ **Conjuncts 1–3 of `bottom`, `htile` gone, and `hindep` gone too.**

⚠ **2026-09-25 signature change (integrator's dispatch).**  The old binder
`hindep : det p vJ1 ≠ 0` is **unsatisfiable on the chain** — `GcdCollapse.det_p_vJ1_zero`
proves `det p vJ1 = 0` from `p = -c • vl` (`RegionSteps`' `exists_chainData` binder `hp_neg`)
plus the collinearity ruling `vJ1 = m • vl`.  It is replaced by `hvJne : vJ ≠ 0`, which is a
`ChainDataGeomParts` field (`vJ_prim`), and the second direction is now `vJ` itself: `hrec`
was **already** a binder here, so this is a strict removal, not a trade.  See §7.

⛔ **`hadj` is refuted on the chain** (see the ⛔ block above) — this theorem is a
conditional whose hypothesis has a counterexample, so it is **not** a usable exit.  The
`hadj`-free one is `TowerHbaseRecP.bottom_conj123_of_rec_p_of_tile`.

⚠ The fourth component of the conclusion is **not** conjunct 4 — it is the ray-level fact,
exactly as in `bottom_conj123`; conjunct 4 is lane-hole3-nlmax's. -/
theorem bottom_conj123_of_tile {Ah : Set (ℤ × ℤ)} {S : Finset (ℤ × ℤ)}
    {nJ vJ vJ1 a p : ℤ × ℤ} {cJ : ℤ}
    (hlc : IsLatticeConvexRegion Ah) (hne : Ah.Nonempty)
    (ha : a ∈ S)
    (hhp : ∀ z ∈ Ah, cJ ≤ dot nJ z)
    (rec_p : ∀ g ∈ Ah, g + p ∈ Ah) (hp : dot nJ p ≠ 0)
    (hrec : ∀ g ∈ Ah, g + vJ ∈ Ah)
    (hnJ_prim : Primitive nJ) (hperp : dot nJ vJ = 0) (hvJne : vJ ≠ 0)
    (hadj : det vJ vJ1 = 1 ∨ det vJ vJ1 = -1) (hsweep : dot nJ vJ1 < 0) :
    ∀ ε : ℕ, ∃ (z₀ : ℤ × ℤ) (L : ℤ), dot nJ z₀ = cJ - (ε : ℤ) - 1 ∧
      (∀ k : ℤ, L ≤ k → z₀ + k • vJ ∈ MaxEnv.reachSet Ah vJ1) ∧
      (∀ b ∈ S, ∀ k : ℤ, L ≤ k → z₀ + k • vJ + (b - a) ∈ MaxEnv.reachSet Ah vJ1) ∧
      (∀ k : ℤ, L ≤ k → dot nJ (z₀ + k • vJ) = cJ - (ε : ℤ) - 1) := by
  obtain ⟨wS, htile⟩ := exists_tile_of_rec_vJ hlc hne hrec rec_p hperp hvJne hp S
  exact Nivat.TowerHbase.bottom_conj123_of_adjacent ha htile hhp hrec hnJ_prim hperp hadj
    hsweep

/-! ## §6  Rigs

⚠ 常设纪律 1 ("台架至少 `m = 4`") does not apply: no proposition in this file mentions a
normal-cycle size `m`, so there is no `m` to set.  What the rigs do measure is
`PROTOCOL §71`'s three classes.

* `rig_two_rec` — 前件可满足 for §1.
* `rig_swept` — 前件可满足 for §3, all eight hypotheses at once.
* `not_tile_without_latticeConvex` — 结论鉴别: drop lattice convexity and the conclusion
  becomes **false**, so `hlc` is not decoration.
* `not_indep_of_antiparallel` — 限定非空, **not** 结论鉴别.  It shows the two sign conditions
  `⟪nJ,p⟫ ≠ 0` and `⟪nJ,vJ1⟫ < 0` are compatible with `det p vJ1 = 0`, i.e. `hindep` does not
  follow from them.  It does **not** falsify the conclusion; ⚠ see its own docstring. -/

/-- The upper half-plane, as a lattice-convex region. -/
def rigR : Set (ℤ × ℤ) := {z | 0 ≤ z.2}

theorem mem_rigR {z : ℤ × ℤ} : z ∈ rigR ↔ 0 ≤ z.2 := Iff.rfl

theorem rigR_latticeConvex : IsLatticeConvexRegion rigR := by
  refine ⟨{x : ℝ × ℝ | 0 ≤ x.2}, ?_, ?_, ?_⟩
  · intro x hx y hy s t hs ht _
    have hx2 : (0 : ℝ) ≤ x.2 := hx
    have hy2 : (0 : ℝ) ≤ y.2 := hy
    show (0 : ℝ) ≤ (s • x + t • y).2
    simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
    have h1 : 0 ≤ s * x.2 := mul_nonneg hs hx2
    have h2 : 0 ≤ t * y.2 := mul_nonneg ht hy2
    linarith
  · exact isClosed_le continuous_const continuous_snd
  · ext z
    show (0 : ℤ) ≤ z.2 ↔ (0 : ℝ) ≤ (toReal z).2
    simp only [toReal]
    exact ⟨fun h => by exact_mod_cast h, fun h => by exact_mod_cast h⟩

/-- **§1's premise table is satisfiable**, with two non-unimodular directions. -/
theorem rig_two_rec :
    ∃ wS : ℤ × ℤ, ∀ b ∈ ({(0, 0), (1, 0), (0, 1), (1, 1), (5, -7)} : Finset (ℤ × ℤ)),
      b + wS ∈ rigR :=
  exists_tile_of_two_recurrences (v := ((2 : ℤ), (0 : ℤ))) (w := ((0 : ℤ), (3 : ℤ)))
    rigR_latticeConvex ⟨(0, 0), mem_rigR.mpr le_rfl⟩
    (fun g hg => by
      have h : (0 : ℤ) ≤ g.2 := mem_rigR.mp hg
      refine mem_rigR.mpr ?_
      simp only [Prod.snd_add]
      linarith)
    (fun g hg => by
      have h : (0 : ℤ) ≤ g.2 := mem_rigR.mp hg
      refine mem_rigR.mpr ?_
      simp only [Prod.snd_add]
      linarith)
    (by decide) _

/-- **§3's premise table is satisfiable.**  `nJ = (0,1)`, `cJ = 0`, `p = (0,1)`,
`vJ1 = (1,-1)`: `⟪nJ,p⟫ = 1 ≠ 0`, `⟪nJ,vJ1⟫ = -1 < 0`, `det p vJ1 = -1 ≠ 0`, and
`SweptClosed` holds because on this rig the guard *is* the membership. -/
theorem rig_swept :
    ∃ wS : ℤ × ℤ, ∀ b ∈ ({(0, 0), (1, 0), (0, 1), (1, 1)} : Finset (ℤ × ℤ)),
      b + wS ∈ rigR :=
  exists_tile_of_swept (nJ := ((0 : ℤ), (1 : ℤ))) (cJ := 0) (p := ((0 : ℤ), (1 : ℤ)))
    (vJ1 := ((1 : ℤ), (-1 : ℤ)))
    rigR_latticeConvex ⟨(0, 0), mem_rigR.mpr le_rfl⟩
    (fun g hg => by
      have h : (0 : ℤ) ≤ g.2 := mem_rigR.mp hg
      simp only [dot]
      linarith)
    (fun g _ t hlev => by
      simp only [dot, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
        smul_eq_mul] at hlev
      refine mem_rigR.mpr ?_
      simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      linarith)
    (fun g hg => by
      have h : (0 : ℤ) ≤ g.2 := mem_rigR.mp hg
      refine mem_rigR.mpr ?_
      simp only [Prod.snd_add]
      linarith)
    (by decide) (by decide) (by decide) _

/-- **Lattice convexity is load-bearing.**  The sub-semigroup `ℕ(2,0) + ℕ(3,0)`-style
witness: `Reven` is closed under `+(2,0)` and `+(0,3)`, is nonempty, the two directions are
independent — and no translate of `{(0,0),(1,0)}` fits, because both points would need an
even first coordinate.  `Reven` is of course not lattice-convex. -/
def Reven : Set (ℤ × ℤ) := {z | ∃ k : ℤ, z.1 = 2 * k}

theorem not_tile_without_latticeConvex :
    (Reven.Nonempty ∧ (∀ g ∈ Reven, g + ((2 : ℤ), (0 : ℤ)) ∈ Reven) ∧
      (∀ g ∈ Reven, g + ((0 : ℤ), (3 : ℤ)) ∈ Reven) ∧
      det ((2 : ℤ), (0 : ℤ)) ((0 : ℤ), (3 : ℤ)) ≠ 0) ∧
    ¬ ∃ wS : ℤ × ℤ, ∀ b ∈ ({(0, 0), (1, 0)} : Finset (ℤ × ℤ)), b + wS ∈ Reven := by
  refine ⟨⟨⟨(0, 0), ⟨0, by norm_num⟩⟩, ?_, ?_, by decide⟩, ?_⟩
  · rintro g ⟨k, hk⟩
    exact ⟨k + 1, by simp only [Prod.fst_add]; omega⟩
  · rintro g ⟨k, hk⟩
    exact ⟨k, by simpa using hk⟩
  · rintro ⟨wS, h⟩
    obtain ⟨k, hk⟩ := h (0, 0) (by decide)
    obtain ⟨k', hk'⟩ := h (1, 0) (by decide)
    simp only [Prod.fst_add] at hk hk'
    omega

/-- **`hindep` is load-bearing — and worse, on the chain it is false.**  With `p = (0,1)`
and `vJ1 = (0,-1)` antiparallel, every other hypothesis of §3 holds on `rigR` — including
`⟪nJ,p⟫ = 1 ≠ 0` and `⟪nJ,vJ1⟫ = -1 < 0` — yet `det p vJ1 = 0`, and the two directions
produced by §3 span only the `(0,1)` line.

⚠ **2026-09-25 re-reading (integrator's dispatch).**  This rig is not merely "some
antiparallel case": taking `vl := (0,-1)` it **is** the chain's own shape, with
`p = -(1 : ℤ) • vl` (`hp_neg` at `c = 1`) and `vJ1 = (1 : ℤ) • vl` (the collinearity ruling
at `m = 1`).  So the correct reading is no longer "`hindep` is not decoration" but
**"`hindep` is not satisfiable on the chain"** — the general statement is
`GcdCollapse.det_p_vJ1_zero`, and this rig is its smallest instance.  Consequently
`exists_tile_of_swept` and `exists_tile_of_parts_binders` are 空载出口 and the live route is
§7.

⚠ **Scope.**  This exhibits the *mechanism* failing, not the conclusion: `rigR` is a
half-plane and does contain translates of every finite set, so it is no counterexample to
`htile` itself.  What it shows is that `exists_tile_of_swept`'s proof cannot be run without
`hindep` — the second direction degenerates.  Any attempt to drop `hindep` must therefore
produce a different second direction; §7 produces one (`vJ`). -/
theorem not_indep_of_antiparallel :
    dot ((0 : ℤ), (1 : ℤ)) ((0 : ℤ), (1 : ℤ)) ≠ 0 ∧
    dot ((0 : ℤ), (1 : ℤ)) ((0 : ℤ), (-1 : ℤ)) < 0 ∧
    det ((0 : ℤ), (1 : ℤ)) ((0 : ℤ), (-1 : ℤ)) = 0 := by
  refine ⟨by decide, by decide, by decide⟩

/-! ## §7  The `hindep`-free route: take `vJ`, not `vJ1`, as the second direction

⚠ **2026-09-25, integrator's dispatch.**  §3's second direction is a combination of `p` and
`vJ1`, and on the chain **both are multiples of the same `vl`**:

* `p = -(c : ℤ) • vl`, `0 < c` — `RegionSteps`' `exists_chainData` binder `hp_neg`;
* `vJ1 = m • vl`, `0 < m` — the collinearity ruling carried as `hm`/`hmpos` in
  `LeafAShellAttain`.

`GcdCollapse.det_p_vJ1_zero` turns that into `det p vJ1 = 0`, so §3's `hindep` has no
chain-side model at all.  The replacement uses `vJ`, and the required independence is
**free from the `ChainDataGeomParts` field table**:

| needed | field |
|---|---|
| `dot nJ vJ = 0` | `F.dot_nJ_vJ` (`FaceBlock`) |
| `vJ ≠ 0` | `vJ_prim` |
| `dot nJ p ≠ 0` | `dot_nJ_p` |

`LaneTowerHlevEscPos.det_ne_zero_of_perp` then gives `det vJ p ≠ 0` with no new binder, and
`det vJ vl ≠ 0` follows too (`det_vJ_vl_ne_zero_of_chain`).  Note `hhp`, `hswept`, `hsweep`,
`cJ` and `vJ1` all disappear from the tiling step.

⚠ **What this does not fix.**  The second direction is now `vJ`, so the producer needs
`rec_vJ`.  A same-round skeleton scan of `Nivat/**` for
`∀ g ∈ ⋃ i, hatOf _ _ _ i, g + vJ ∈ ⋃ i, hatOf _ _ _ i` finds producers only in
`RecVJFromParts` (`rec_vJ_of_parts`, consumes `c.bottom`), `ItemII` (`rec_vJ_of_bottom`,
consumes the whole `bottom`) and `TowerHlevRecVJ` (`rec_vJ_of_parts_bottom₁₂`, consumes
`bottom`'s conjunct 1 at `ε = 0`); every other hit is a binder.  ⟹ if `htile` is used to
produce `bottom`'s conjuncts 1–3, `rec_vJ` must come from the populator's construction, not
from any of those three.  This is **not new debt**: `bottom_conj123_of_tile` and
`TowerHbaseRecP.bottom_conj123_of_rec_p_of_tile` both already carried `hrec` as a binder
before this change.  What changed is only that `hindep` is gone. -/

/-- `dot n (k • z) = k * dot n z`. -/
private theorem dot_zsmul_tile (n : ℤ × ℤ) (k : ℤ) (z : ℤ × ℤ) :
    dot n (k • z) = k * dot n z := by
  simp only [dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

/-- `dot nJ p ≠ 0` and `p = -c • vl` force `dot nJ vl ≠ 0`.  `0 < c` is not used. -/
theorem dot_nJ_vl_ne_zero {nJ vl p : ℤ × ℤ} {c : ℕ}
    (hp : p = -(c : ℤ) • vl) (hdp : dot nJ p ≠ 0) : dot nJ vl ≠ 0 := by
  intro h
  exact hdp (by rw [hp, dot_zsmul_tile, h, mul_zero])

/-- **`det vJ vl ≠ 0`**, the independence the integrator's dispatch names. -/
theorem det_vJ_vl_ne_zero {nJ vJ vl : ℤ × ℤ}
    (hperp : dot nJ vJ = 0) (hvJne : vJ ≠ 0) (hvl : dot nJ vl ≠ 0) : det vJ vl ≠ 0 :=
  Nivat.LaneTowerHlevEscPos.det_ne_zero_of_perp hperp hvJne hvl

/-- The chain composite: three fields plus `hp_neg` give `det vJ vl ≠ 0`. -/
theorem det_vJ_vl_ne_zero_of_chain {nJ vJ vl p : ℤ × ℤ} {c : ℕ}
    (hperp : dot nJ vJ = 0) (hvJne : vJ ≠ 0) (hp : p = -(c : ℤ) • vl)
    (hdp : dot nJ p ≠ 0) : det vJ vl ≠ 0 :=
  det_vJ_vl_ne_zero hperp hvJne (dot_nJ_vl_ne_zero hp hdp)

/-- ⭐ **`htile` on the chain with no determinant binder.**  Replaces
`exists_tile_of_parts_binders`, whose `hindep` is unsatisfiable on the chain.  Every binder
is a `ChainDataGeomParts` field: `maxA` / `hfin` / `AhatMono` / `ahat_nonempty` / `rec_p` /
`dot_nJ_p` / `F.dot_nJ_vJ` / `vJ_prim`, plus `rec_vJ` (see §7's ⚠ on where that must come
from).  `hhp` / `hswept` / `hsweep` / `cJ` / `vJ1` are **not** needed. -/
theorem exists_tile_of_parts_recvJ {α : Type*}
    (η xper : Config α) (vl p : ℤ × ℤ) (S : Finset (ℤ × ℤ))
    (B A : ℕ → Set (ℤ × ℤ)) (u : ℕ → ℤ × ℤ) (kk : ℕ → ℕ)
    (maxA : ∀ i, IsMaxEnvIn (EnvOf (↑S : Set (ℤ × ℤ))) (canonA η xper vl B u i) (A i))
    (hfin : ∀ i, (hatOf A kk vl i).Finite)
    (AhatMono : ∀ i j, i ≤ j → hatOf A kk vl i ⊆ hatOf A kk vl j)
    (vJ nJ : ℤ × ℤ)
    (ahat_nonempty : (⋃ i, hatOf A kk vl i).Nonempty)
    (rec_vJ : ∀ g ∈ ⋃ i, hatOf A kk vl i, g + vJ ∈ ⋃ i, hatOf A kk vl i)
    (rec_p : ∀ g ∈ ⋃ i, hatOf A kk vl i, g + p ∈ ⋃ i, hatOf A kk vl i)
    (dot_nJ_vJ : dot nJ vJ = 0) (vJ_ne : vJ ≠ 0) (dot_nJ_p : dot nJ p ≠ 0) :
    ∃ wS : ℤ × ℤ, ∀ b ∈ S, b + wS ∈ ⋃ i, hatOf A kk vl i :=
  exists_tile_of_rec_vJ
    (latticeConvex_iUnion_hatOf η xper vl S
      (EnvOf (↑S : Set (ℤ × ℤ))) B A u kk rfl maxA hfin AhatMono)
    ahat_nonempty rec_vJ rec_p dot_nJ_vJ vJ_ne dot_nJ_p S

/-- **结论鉴别 (`PROTOCOL §71` class 二) for the swap.**  One configuration, five vectors
fixed: `nJ = (0,1)`, `vl = (0,-1)`, `p = (0,1) = -(1 : ℤ) • vl`, `vJ1 = (0,-1) = (1 : ℤ) • vl`,
`vJ = (1,0)`.  All of §3's sign binders hold, `vJ` is a legal face direction
(`⟪nJ,vJ⟫ = 0`, `vJ ≠ 0`) — and the **old** independence premise is false while the **new**
one is true on the very same data.  ⟹ the swap is a real change of route, not a rewording.

⚠ Scope: this is a witness that the two premises are not interchangeable here; it says
nothing about whether `rec_vJ` is available.  常设纪律 1 (`m ≥ 4`) does not apply — no
proposition here mentions a normal-cycle size. -/
theorem collinear_rig_old_dead_new_alive :
    ((0 : ℤ), (1 : ℤ)) = -((1 : ℕ) : ℤ) • ((0 : ℤ), (-1 : ℤ)) ∧
    ((0 : ℤ), (-1 : ℤ)) = (1 : ℤ) • ((0 : ℤ), (-1 : ℤ)) ∧
    dot ((0 : ℤ), (1 : ℤ)) ((1 : ℤ), (0 : ℤ)) = 0 ∧
    ((1 : ℤ), (0 : ℤ)) ≠ ((0 : ℤ), (0 : ℤ)) ∧
    dot ((0 : ℤ), (1 : ℤ)) ((0 : ℤ), (1 : ℤ)) ≠ 0 ∧
    det ((0 : ℤ), (1 : ℤ)) ((0 : ℤ), (-1 : ℤ)) = 0 ∧
    det ((1 : ℤ), (0 : ℤ)) ((0 : ℤ), (1 : ℤ)) ≠ 0 ∧
    det ((1 : ℤ), (0 : ℤ)) ((0 : ℤ), (-1 : ℤ)) ≠ 0 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide⟩

/-! ## §8  ⛔ `hcomb` is false on the chain — the `RecVJComb` detour round the `rec_vJ` cycle dies

`RecVJComb.parts_rec_vJ` (lane-tower-hbase) produces `rec_vJ` *without* consuming `bottom`,
so it is a candidate exit from the cycle `bottom` conj 1 ⟸ `htile` ⟸ `rec_vJ` ⟸ conj 1.
Its one extra side condition is, verbatim,

```
{a t : ℕ} (hcomb : c.vJ = (a : ℤ) • p + (t : ℤ) • c.vJ1)
```

⛔ **That premise is unsatisfiable on the chain.**  Reason, in one line: `p` and `vJ1` are both
multiples of `vl` (`p = -(c : ℤ) • vl` from `exists_chainData`'s binder `hp_neg`; `vJ1 = m • vl`
from the 226-round collinearity ruling), so the lattice they span is the *line* `ℤ • vl`, not a
two-dimensional lattice.  `hcomb` therefore forces `vJ ∈ ℤ • vl`; but `dot nJ vJ = 0`
(`FaceBlock.dot_nJ_vJ`) together with `dot nJ vl ≠ 0` (`dot_nJ_vl_ne_zero`, §7) forces the
coefficient to vanish, i.e. `vJ = 0`, contradicting `vJ ≠ 0` (`vJ_prim`).

⭐ **The proof needs strictly less than the integrator's route.**  He proposed going through
`GcdCollapse.vJ1_eq_vl_of_prim` (which pins `m = 1` using `Primitive vJ1`, `hsweep` and the
sign `dot nJ vl < 0`).  None of that is needed: collinearity `vJ1 = m • vl` alone suffices,
for *arbitrary* `m`, and the coefficients `a`, `t` may be arbitrary integers rather than
naturals.  So the verdict does not rest on the `m = 1` pinning, nor on any sign fact.

⚠ Scope, three lines:
1. This kills `hcomb`, i.e. route (a) round the cycle.  It says nothing about `hbox` / `hkk`,
   the side conditions of the *other* `bottom`-free producer `RecVJ.rec_vJ_of_halfPlane`.
2. It does **not** touch `RecVJComb.rec_of_comb` itself, whose arithmetic is correct for
   arbitrary `p`, `vJ1` — `hcomb_satisfiable_off_chain` below is a configuration where the
   premise genuinely holds.  What dies is the chain instantiation, exactly as with `hindep`
   (`GcdCollapse.det_p_vJ1_zero`) and `det p vJ1 = ±1`.
3. The collinearity ruling `vJ1 = m • vl` is itself still a premise with no located producer
   (`∃ m, vJ1 = m • vl` has 0 conclusion-position hits in `Nivat/**.lean`).  Hence the honest
   reading is conditional: *if* the collinearity ruling holds on the chain, `hcomb` is false
   there.  常设纪律 1 (`m ≥ 4`) does not apply — no proposition here mentions a normal-cycle
   size; the `m` in this section is the collinearity coefficient, a different object
   (`NOTATION.md`, 一名多物). -/

/-- **General form.**  If `p` and `vJ1` are both multiples of `vl`, and `nℓ`-height separates
`vl` from `vJ`, then `vJ` is not an integer combination of `p` and `vJ1`.

Coefficients are arbitrary integers; `m` is arbitrary; no sign hypothesis. -/
theorem not_hcomb_of_collinear {nJ vJ vJ1 vl p : ℤ × ℤ} {c : ℕ} {m a t : ℤ}
    (hp : p = -(c : ℤ) • vl) (hm : vJ1 = m • vl)
    (hdp : dot nJ p ≠ 0) (hperp : dot nJ vJ = 0) (hvJne : vJ ≠ 0) :
    vJ ≠ a • p + t • vJ1 := by
  intro hcomb
  have hvl : dot nJ vl ≠ 0 := dot_nJ_vl_ne_zero hp hdp
  have hform : a • p + t • vJ1 = (a * -(c : ℤ) + t * m) • vl := by
    rw [hp, hm, smul_smul, smul_smul, add_smul]
  rw [hform] at hcomb
  have h0 : (a * -(c : ℤ) + t * m) * dot nJ vl = 0 := by
    rw [← dot_zsmul_tile, ← hcomb]; exact hperp
  rcases mul_eq_zero.mp h0 with hk | hk
  · rw [hk, zero_smul] at hcomb; exact hvJne hcomb
  · exact hvl hk

/-- ⛔ **Chain form, matching `RecVJComb.parts_rec_vJ`'s side condition character for
character** (`a t : ℕ`, cast to `ℤ` in the combination). -/
theorem not_hcomb_of_chain {nJ vJ vJ1 vl p : ℤ × ℤ} {c : ℕ} {m : ℤ} {a t : ℕ}
    (hp : p = -(c : ℤ) • vl) (hm : vJ1 = m • vl)
    (hdp : dot nJ p ≠ 0) (hperp : dot nJ vJ = 0) (hvJne : vJ ≠ 0) :
    vJ ≠ (a : ℤ) • p + (t : ℤ) • vJ1 :=
  not_hcomb_of_collinear hp hm hdp hperp hvJne

/-- §71 class 二 discrimination: the premise that carries the refutation is **collinearity**,
not the other four.

Same shape as `RecVJComb.rec_of_comb_nonvacuous`: `nJ = (0,1)`, `vJ = (1,0)`, `p = (1,1)`,
`vJ1 = (0,-1)`, `a = t = 1`.  Here `dot nJ vJ = 0` and `vJ ≠ 0` and `dot nJ p ≠ 0` all hold
exactly as in `not_hcomb_of_collinear`, `hcomb` **is true**, and the only premise that fails is
collinearity — witnessed by `det p vJ1 ≠ 0`.  ⟹ the refutation above is a statement about the
chain's degenerate geometry, not about `hcomb`'s shape.

⭐ **Scope correction (lane-leafa-shell, adopted; name deliberately unchanged).**  The label
`off_chain` understates this witness.  It names no `vl` of its own, but the chain pins one:
`p = -(c : ℤ) • vl` with `p = (1,1)` forces `c = 1`, `vl = (-1,-1)` — uniquely, and (tighter than
shell stated) **without** using `0 < c`, since `(c : ℤ) ∣ 1` already excludes `c = 0`.  Substituting
back gives `det vl vJ1 = det (-1,-1) (0,-1) = 1 ≠ 0`, so these constants live in the **transverse**
lattice, i.e. exactly the `m − 2` slots that `not_hcomb_of_collinear` cannot reach; and
`vJ1 = (0,-1)` is no integer multiple of `vl`, so that theorem's `hm` antecedent is false here.
The two results are complementary, not in tension.  ⟹ `RecVJComb.parts_rec_vJ`'s side condition
is **satisfiable** in the transverse lattice.  Kernel-checked here as `vl_unique` /
`transverse_and_hm_false` (`tmp/_hlev_vlrecover.lean`, EXIT=0, whitelist).

⚠ Two things this does **not** say.  (i) Satisfiable ≠ true on the chain: `parts_rec_vJ` takes an
assertion about the chain's actual `c.vJ`, so wiring the transverse lattice up still needs a
producer for `vJ ∈ ⟨p, vJ1⟩`.  (ii) The set-side conjuncts of `RecVJComb.comb_nonvacuous`
(`hhp` / `SweptClosed` / `rec_p`) are hbase's file and are not re-run here. -/
theorem hcomb_satisfiable_off_chain :
    dot ((0 : ℤ), (1 : ℤ)) ((1 : ℤ), (0 : ℤ)) = 0 ∧
    ((1 : ℤ), (0 : ℤ)) ≠ ((0 : ℤ), (0 : ℤ)) ∧
    dot ((0 : ℤ), (1 : ℤ)) ((1 : ℤ), (1 : ℤ)) ≠ 0 ∧
    ((1 : ℤ), (0 : ℤ)) = ((1 : ℕ) : ℤ) • ((1 : ℤ), (1 : ℤ))
      + ((1 : ℕ) : ℤ) • ((0 : ℤ), (-1 : ℤ)) ∧
    det ((1 : ℤ), (1 : ℤ)) ((0 : ℤ), (-1 : ℤ)) ≠ 0 := by
  refine ⟨by decide, by decide, by decide, ?_, by decide⟩
  simp only [Nat.cast_one, one_smul, Prod.mk_add_mk]
  norm_num

/-! ## §9  Route (b) round the `rec_vJ` cycle: `hbox` is produced, `hkk` is the whole residual

The other `bottom`-free producer of `rec_vJ` is `RecVJ.rec_vJ_of_halfPlane`, whose side
conditions the integrator listed as `hbox` + `hkk`.  Their status, measured this round
(`#check`s run here, not quoted — `CORE-HOLES.md` (G-c′)):

* ⭐ **`hbox` has a producer, verbatim.**  `Nivat.ItemIIChain.exists_itemII_chain`'s eighth
  conjunct is character for character
  `∀ i : ℕ, ∀ z : ℤ × ℤ, |z.1| ≤ (i : ℤ) → |z.2| ≤ (i : ℤ) → cz ≤ dot nℓ z → z ∈ B (i + 1)`,
  i.e. `iUnion_hatOf_eq_halfPlane`'s `hbox` slot.  The same existential also supplies `hlev`
  (conjunct 4), `subBA` (6) and `subAB` (7), and `hperp` is one of its own binders.
  ⟹ **four of the five** premises of `iUnion_hatOf_eq_halfPlane` come from one call.
  (This corrects the "Half-plane exhaustion" bullet in the module header, which used to list
  `hbox` as a residual.)
* ⛔ **`hkk` is the only residual, and the chain's stock does not give it.**  The chain-side
  producer of `kk` is `Nivat.ChainKK.exists_normalised_chain`; everything it says about `kk`
  is **monotonicity** `∀ i j, i ≤ j → kk i ≤ kk j` (plus the `IsGreatest … 0` normalisation and
  `AhatMono`, neither of which bounds growth).  `hkk` is a *sublinear-growth* condition:
  `∀ z, ∃ i, |(z + kk (i+1) • vl).1| ≤ i ∧ |(z + kk (i+1) • vl).2| ≤ i`.
  `hkk_not_from_monotone` below is the kernel witness that monotone ⇏ `hkk`.

⚠ And a warning about what route (b) would buy, which the module header already carries:
`iUnion_hatOf_eq_halfPlane` concludes `⋃ i, hatOf A kk vl i = {z | cz ≤ dot nℓ z}`, a **half
plane**, whereas `scratch/b3_colle2.txt:506` calls `Â_∞` an `(ℓ,ℓ_J)`-region with two
semi-infinite edges.  Given the other four premises, `hkk` is therefore *equivalent* to that
half-plane equality — it is not a technical side condition but the strong geometric claim
itself.  ⟹ whoever produces `hkk` owes the `:506` discrepancy an explanation, and conversely,
if `:506` is right, `hkk` is **false** on the chain.

⚠ Grade (`PROTOCOL.md §50`): the two producer readings are ③ (own `#check`, `EXIT=0`);
`hkk_not_from_monotone` is ③; the `:506`-vs-half-plane tension is ② (reading of the paper
sentence), and I have **not** checked whether `:506` is stated for `Â_∞` under the chain's own
`kk` normalisation — that is the one link that would turn "`hkk` is false" from ② into ③.
Scope: nothing here asserts `hkk` is false; it asserts `hkk` is not derivable from what the
chain currently hands out. -/

/-- ⛔ **`kk` monotone ⇏ `hkk`.**  Left conjunct: `kk := fun k => k` is monotone, which is
everything `ChainKK.exists_normalised_chain` says about `kk`.  Right conjunct: with
`vl := (1,0)` that `kk` fails `hkk` already at `z = 0`, since `|0 + (i+1)| ≤ i` is false for
every `i`.

⟹ route (b)'s residual is real: it needs a growth bound on `kk` that no chain field supplies.
常设纪律 1 (`m ≥ 4`) does not apply — no proposition here mentions a normal-cycle size. -/
theorem hkk_not_from_monotone :
    (∀ i j : ℕ, i ≤ j → (fun k : ℕ => k) i ≤ (fun k : ℕ => k) j) ∧
    ¬ (∀ z : ℤ × ℤ, ∃ i : ℕ,
        |(z + (((fun k : ℕ => k) (i + 1) : ℕ) : ℤ) • ((1 : ℤ), (0 : ℤ))).1| ≤ (i : ℤ) ∧
        |(z + (((fun k : ℕ => k) (i + 1) : ℕ) : ℤ) • ((1 : ℤ), (0 : ℤ))).2| ≤ (i : ℤ)) := by
  refine ⟨fun _ _ h => h, ?_⟩
  intro h
  obtain ⟨i, h1, -⟩ := h ((0 : ℤ), (0 : ℤ))
  simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, mul_one] at h1
  rcases abs_le.mp h1 with ⟨-, h2⟩
  push_cast at h2
  omega

end Nivat.LaneTowerHlevTile

-- ⚠ One `#print axioms` per declaration, all 25.  A shorter block still prints a clean
-- list while leaving declarations unaudited (lane-env-refute, `tmp/_declaudit229.py`).
#print axioms Nivat.LaneTowerHlevTile.exists_tile_of_two_recurrences
#print axioms Nivat.LaneTowerHlevTile.exists_tile_of_rec_vJ
#print axioms Nivat.LaneTowerHlevTile.rec_comb_of_swept
#print axioms Nivat.LaneTowerHlevTile.hlev_det_comb
#print axioms Nivat.LaneTowerHlevTile.exists_tile_of_swept
#print axioms Nivat.LaneTowerHlevTile.exists_tile_of_parts_binders
#print axioms Nivat.LaneTowerHlevTile.bottom_conj123_of_tile
#print axioms Nivat.LaneTowerHlevTile.rigR_latticeConvex
#print axioms Nivat.LaneTowerHlevTile.rig_two_rec
#print axioms Nivat.LaneTowerHlevTile.rig_swept
#print axioms Nivat.LaneTowerHlevTile.not_tile_without_latticeConvex
#print axioms Nivat.LaneTowerHlevTile.not_indep_of_antiparallel
#print axioms Nivat.LaneTowerHlevTile.rigR
#print axioms Nivat.LaneTowerHlevTile.mem_rigR
#print axioms Nivat.LaneTowerHlevTile.Reven
#print axioms Nivat.LaneTowerHlevTile.dot_zsmul_tile
#print axioms Nivat.LaneTowerHlevTile.dot_nJ_vl_ne_zero
#print axioms Nivat.LaneTowerHlevTile.det_vJ_vl_ne_zero
#print axioms Nivat.LaneTowerHlevTile.det_vJ_vl_ne_zero_of_chain
#print axioms Nivat.LaneTowerHlevTile.exists_tile_of_parts_recvJ
#print axioms Nivat.LaneTowerHlevTile.collinear_rig_old_dead_new_alive
#print axioms Nivat.LaneTowerHlevTile.not_hcomb_of_collinear
#print axioms Nivat.LaneTowerHlevTile.not_hcomb_of_chain
#print axioms Nivat.LaneTowerHlevTile.hcomb_satisfiable_off_chain
#print axioms Nivat.LaneTowerHlevTile.hkk_not_from_monotone
