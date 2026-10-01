/-
Copyright (c) 2026. Released under Apache 2.0 license.
Authors: lane-chaindata-lead
-/
import Nivat.External.Colle.BottomReachMin
import Nivat.External.Colle.RegionCutGE
import Nivat.External.Colle.HsuppContain

/-!
# `bottom` from one "room" premise, in the shape `TowerRoom` already knows how to produce

`BottomReachMin.bottom_of_reachMin` (`BottomReachMin.lean:151`) left two premises open,
`hlow` and `hhigh`.  `hhigh` is **false** as stated — kernel witnesses in
`tmp/wip/lane-cd-hhigh-refute.lean` and `tmp/wip/lane-cd-hhigh-refute2.lean` — and Round 92
revoked the approval to dispatch it.  This file replaces both by a single premise that the
witnesses do **not** satisfy and that the repo already has a proof pattern for.

## The two premises were one premise

`dot nJ vJ = 0` (`F.dot_nJ_vJ`), so `dot nJ (z₀ + (b - a)) = (cJ - ε - 1) + dot nJ (b - a)`.
`hlow` covered `1 ≤ dot nJ (b - a) ≤ ε` and `hhigh` covered `ε < dot nJ (b - a)`; their union
is `1 ≤ dot nJ (b - a)`, which is exactly `hedge`'s second disjunct, and nothing in either
conclusion mentions `ε`.  The split was an artifact.  At `ε = 0` it degenerated completely —
`hlow` vacuous, `hhigh` carrying every raised `b` — which is what made the "large `ε` is
vacuous" reading of `hhigh_vacuous` (`BottomReachMin.lean:139`) misleading about the workload.

## Why `hroom` and not `hwin`

Merging alone does not help.  Stating the merged premise against the shell
`MaxEnv.shell T vJ1 nJ cJ ε` does not help either: for `1 ≤ dot nJ (b - a)` the level bound
`cJ - ε ≤ dot nJ ·` is automatic, so a shell-valued premise is *logically equivalent* to the
`reachSet`-valued pair, and the refutation witnesses refute it verbatim.  A restatement cannot
repair a false premise; only a premise the witnesses fail can.

`hroom` below is that premise:

    ∀ x ∈ reachSet T vJ1, dot nJ x < cJ →
      ∀ b ∈ S, 0 < dot nJ (b - a) → x + (b - a) ∈ reachSet T vJ1

It quantifies over **every** sub-`cJ` point of the swept set, not just the one point `z₀`, so
it is strictly stronger than the pair it replaces — and that is the point: it is the statement
the geometry actually proves, in one shot, rather than the pointwise shadow of it.

This is not a shape invented here.  It is, up to renaming, the conclusion of
`Nivat.TowerRoom.hroomT_of_wedge_and_cont` (`TowerRoom.lean:68`, 0 sorry):

    ∀ x ∈ Rinf, dot m x < b₀ → ∀ b ∈ Sphi, 0 < dot m (b - a) → x + (b - a) ∈ Rinf

with `Rinf ↦ reachSet T vJ1`, `m ↦ nJ`, `b₀ ↦ cJ`, `Sphi ↦ S`.  That theorem's mechanism is
pure integer closure from three inputs, all of which have counterparts here:

| `TowerRoom` input | counterpart for `bottom` |
|---|---|
| `hWedge`: every sub-`b₀` point of `Rinf` is `V + s•w + t•wtowerI`, `s t : ℕ` | ⚠ **does not transfer** — see `wedge_false_on_region` below |
| `hTowerW_gen`/`hRinf_sweep_gen`: closure under `+ℕ•w`, sweep by `+ℕ•wtowerI` | `hrecT` (closure under `+vJ`) and `reachSet`'s own `+ℕ•vJ1` |
| `hcont : ∀ b ∈ Sphi, V + (b - a) ∈ B` | `Nivat.HsuppContain.hcont` (`HsuppContain.lean:413`, 0 sorry) on the finite shell `Â_i^{(ε)}` — see §5 |

`HsuppContain.hcont` is the substantive one, and it is **already proved**: it derives
`∀ b ∈ ↑Sphi, V + (b - a) ∈ B` from `hEeq : E B = E ↑Sphi` and
`henv : ∀ n ∈ E B, (face ↑Sphi n).encard ≤ (face B n).encard` — i.e. from envelopedness of `B`
by `Sphi` — with `a` and `V` the `faceStart` anchors.  So the envelopedness input Round 92
asked me to trace does reach a window-placement conclusion, through an existing 0-sorry route.

## Which envelopedness, and why not the union

`b3_colle2.txt:506` grants `Â_∞ := ⋃ Â_i` only **weak** `E(𝒮_φ)`-envelopedness（⚠ 第 201 轮
订正：原记 `:505`，那是空行），and that is
forced, not sloppy: `Â_∞` has two semi-infinite edges while `𝒮_φ` has `2m`, so `Enveloped`'s
cardinality clause `(E T).encard = (E U).encard` (`LatticeEdges.lean:628`) is false for the
union whenever `m ≥ 2`.  `lane-cd-hhigh-refute2.lean` shows weak envelopedness does not place
the window.  So the union is the wrong object to hang the premise on — which is precisely why
`bottom_of_reachMin`'s abstract `T` could not carry it.

`b3_colle2.txt:520` grants **full** envelopedness to the stages:

> `Â_i^{(ε)} := {g - t v_{ℓ_{J+1}} ∈ Â_∞^{(ε)} : g ∈ Â_i, t ∈ ℤ_+}` is an
> `E(𝒮_φ)`-enveloped set.

`Â_i^{(ε)}` is `ShellMink.shellInter (hatOf A kk vl i) (MaxEnv.shell (⋃ i, hatOf A kk vl i) vJ1
nJ cJ ε) w` (`ShellMink.lean:507`), it is finite (`MaximalEnveloped.Enveloped.finite`), and it
sits inside `Â_∞^{(ε)}` by `shellInter_subset_right`.  Its envelopedness is **already a binder**
of the consumer — `shellEnv` (`ChainExhaustInter.lean`) — so at the call site the same fact
serves both `shellEnv` and, through `HsuppContain.hcont`, `hroom`.

## What is still owed

The window placement at `z₀` (§4's `hwin`), and nothing else.  §5 reduces it to the
envelopedness of the finite shell, which is already the consumer's `shellEnv` binder.

§3 corrects the `hWedge` row of the table above.  The corner-wedge premise —
"every sub-`cJ` point of `reachSet Â_∞ v_{J+1}` is `V + s·v_J + t·v_{J+1}`" — is *not* the
two-parameter form of `hline0`, and it does **not** follow from `Â_∞` being an
`(ℓ, ℓ_J)`-region: `wedge_false_on_region` exhibits a region satisfying every structural
hypothesis the call site has about `Â_∞` alone (`Colle41.IsRegion` with both rays, the
half-plane, the `+v_J` recession, both sign conditions, and a bottom row equal to `V + ℕ·v_J`)
whose sub-`cJ` sweep escapes the wedge, because points on the *finite* edge sweep down to the
`-v_J` side of `V`.  The same witness refutes `hroom` outright (`hroom_false_on_region`), so
`Colle41.IsRegion` is not the missing premise either — the missing premise is envelopedness.

The chain that survives, all 0 sorry:

* `hroom_of_lift` (§3.1) — `hroom` holds as soon as each sub-`cJ` point has *some* lift into
  `Â_∞` absorbing the raised window.  Minimal form: nothing about `v_J`, levels, or shape.
* `hlift_of_band` (§3.2) — `hswept` slides any lift down to the last one above `cJ`, so only
  the bottom band matters.
* `hband_of_two_corners` (§3.4) — the band lies in `conv{V, V - v_{J+1}} + ℝ₊·v_J`, so only
  `V` and `V - v_{J+1}` need to absorb.

Composed: `hroom_of_two_corners`.  Its open inputs are `hcoreV` and `hcoreV'`, and every other
input is a binder of `ofPartsExhaustsInter` or immediate from one.  At the call site `V` is
`g_J`: `hray` puts it on `Â_∞`'s bottom row and `hsupp_prev_U` makes it the `n_prevJ`-support
point, which are exactly `hVlev` and `hsupp`.

## §4/§5 (2026-09-23) — the band chain proves more than `bottom` needs

Two corrections to the plan above, in the order they were found.

**(a) `bottom_of_room` reads its premise once.**  Its proof instantiates `hroom` only at
`x := z₀`.  So the whole band chain is over-strength for this consumer, and §4's
`bottom_of_window` takes the single instance instead.  That instance is
`bottom_of_reachMin`'s `hlow`-and-`hhigh` merged: `dot nJ vJ = 0`, so neither conclusion
mentions `ε` and the split at `ε` was an artifact.  Ordering of the four forms in this file:

    hwin ⟸ hroom ⟸ hband ⟸ (hcoreV ∧ hcoreV')

**(b) `hcoreV'` is the wrong object.**  `V - v_{J+1} = g_J - v_{J+1}` is not the `n_J`-minimal
point of any `Â_i`, so `HsuppContain.hcont` at `m := n_J` does not anchor there; and anchoring
on the `n_prevJ` face instead lands the window at the far end of that face, displaced by
`|face Â_i n_prevJ| - |face 𝒮_φ n_prevJ|` steps of `-v_{J+1}` — which envelopedness allows to
be `0`.  On that equality the window anchored at `g_J` already covers the whole `n_prevJ` face
of `Â_i`, so the one-step shift leaves `Â_i`.  Nothing in this file refutes `hcoreV'`; it is
simply not reachable from `hcont` plus the binders the call site has.

`hband_of_far_corner`/`hroom_of_far_corner` narrow (b) as far as it goes: the second
corner may sit any `N ≥ 1` steps up the `n_prevJ` face, and `hcont` at `m := -n_prevJ`
delivers it at `N = faceLen Â_i n_prevJ - faceLen 𝒮_φ n_prevJ`.  So the band route closes
as soon as that face length grows *strictly*, and the single bad case is exact equality —
which envelopedness permits.  §5 is the route that does not depend on the question.

**What §5 does instead** is `b3_colle2.txt:518-520` as written: `hcont` at `m := n_J` on the
finite **shell** `Â_i^{(ε+1)}`, not on the stage `Â_i`.  `window_of_shell` is that wiring, and
it is the main tree's first consumer of `HsuppContain.hcont`.  `z₀` is the shell's
`n_J`-minimal `dir (-n_J)`-start corner because `⋃ i, Â_i^{(ε+1)} = Â_∞^{(ε+1)}` and `hline0`
makes `z₀` reach-minimal in the union, hence in every member containing it.  The `hcont`
inputs `hEeq`/`henv` are then literally the `shellEnv` binder of `ofPartsExhaustsInter`
(`ChainExhaustInter.lean`), so `bottom`'s remaining hole and `shellEnv` are one hole.

The earlier claim in this docstring that `hcont` "cannot be run on the half-strip
`Â_i^{(ε)}`" was wrong in the only way that mattered: `Â_i^{(ε)}` is the `shellInter`, which is
**finite**, so `hBfin` is satisfied.  What cannot take `hcont` is `Â_∞^{(ε)}`, the union.

⚠ §5 carries no concrete non-vacuity receipt, and cannot cheaply: `hcont` takes a
`d : DecompDataZ η`, which the repo only manufactures from `IsMinimalCounterexample`
(`DecompDataZ.of_minimalCounterexample`, `DecompData.lean:275`).  The hypotheses §5 adds on
top of `hcont`'s own list are `hPsub` (satisfiable at `T := P`, `t = 0`), `hnJvJ` and `hedge`
(both `FaceBlock` fields at the call site), so §5 inherits `hcont`'s status exactly.

Receipts, all kernel-checked, pinning each premise from both sides: `hroom` is satisfiable
(`hroom_holds_on_quadrant`) and refuted by the `hhigh` witness (`hroom_false_on_cone`);
`hband` likewise (`hband_holds_on_quadrant`, `hroom_false_on_region`); the thin and
two-corner hypothesis sets are jointly satisfiable (`thin_hypotheses_satisfiable`,
`two_corner_hypotheses_satisfiable` — the latter on a band that is genuinely two rows deep,
which is the case the thin lemma cannot reach).
-/

set_option autoImplicit false

namespace Nivat.BottomRoom

open Nivat Nivat.LE2 Nivat.MaxEnv

/-- **`bottom` from one room premise.**

Same conclusion as `BottomReachMin.bottom_of_reachMin`, with its two open premises `hlow` and
`hhigh` replaced by the single `hroom`.  Both follow by instantiating `hroom` at `x := z₀`,
whose level `cJ - ε - 1` is below `cJ`, and whose displacement condition `0 < dot nJ (b - a)`
is `hedge`'s second disjunct in both the `hlow` band and the `hhigh` tail. -/
theorem bottom_of_room {T : Set (ℤ × ℤ)} {S : Finset (ℤ × ℤ)}
    {nJ vJ vJ1 z₀ a : ℤ × ℤ} {cJ : ℤ} {ε : ℕ}
    (hrecT : ∀ g ∈ T, g + vJ ∈ T)
    (hdz : dot nJ z₀ = cJ - (ε : ℤ) - 1)
    (hz₀ : z₀ ∈ reachSet T vJ1)
    (hline0 : ∀ z ∈ reachSet T vJ1, dot nJ z = cJ - (ε : ℤ) - 1 →
      ∃ k : ℤ, 0 ≤ k ∧ z = z₀ + k • vJ)
    (hedge : ∀ b ∈ S.erase a,
      (∃ j : ℕ, 1 ≤ j ∧ b = a + (j : ℤ) • vJ) ∨ 1 ≤ dot nJ (b - a))
    (hroom : ∀ x ∈ reachSet T vJ1, dot nJ x < cJ →
      ∀ b ∈ S, 0 < dot nJ (b - a) → x + (b - a) ∈ reachSet T vJ1) :
    ∃ (z₀' : ℤ × ℤ) (L : ℤ),
      dot nJ z₀' = cJ - (ε : ℤ) - 1 ∧
      (∀ k : ℤ, L ≤ k → z₀' + k • vJ ∈ reachSet T vJ1) ∧
      (∀ b ∈ S, ∀ k : ℤ, L ≤ k → z₀' + k • vJ + (b - a) ∈ reachSet T vJ1) ∧
      (∀ z ∈ shell T vJ1 nJ cJ (ε + 1),
        z ∈ shell T vJ1 nJ cJ ε ∨ ∃ k : ℤ, L ≤ k ∧ z = z₀' + k • vJ) := by
  have hzlt : dot nJ z₀ < cJ := by
    have : (0 : ℤ) ≤ (ε : ℤ) := Int.natCast_nonneg ε
    omega
  exact BottomReachMin.bottom_of_reachMin hrecT hdz hz₀ hline0 hedge
    (fun b hb h1 _ => hroom z₀ hz₀ hzlt b hb (by omega))
    (fun b hb h => hroom z₀ hz₀ hzlt b hb (by
      have : (0 : ℤ) ≤ (ε : ℤ) := Int.natCast_nonneg ε
      omega))

/-! ## §2 Receipt 1 — `hroom` is genuinely refuted by the `hhigh` witness

`tmp/wip/lane-cd-hhigh-refute.lean` exhibits data on which every other premise of
`bottom_of_reachMin` holds and `hhigh` fails.  Since `hroom` implies `hhigh`, `hroom` must fail
there too; if it did not, `bottom_of_room` would prove a false conclusion.  The cone is
restated here (that file is unpromoted, so `check1.sh` cannot import it). -/

private def coneT : Set (ℤ × ℤ) := {z | 0 ≤ z.2 ∧ 2 * z.2 ≤ z.1}

private theorem mem_reach_cone (z : ℤ × ℤ) :
    z ∈ reachSet coneT (0, -1) ↔ (0 ≤ z.1 ∧ 2 * z.2 ≤ z.1) := by
  constructor
  · rintro ⟨g, ⟨hg1, hg2⟩, t, rfl⟩
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul] at hg1 hg2 ⊢
    constructor <;> omega
  · rintro ⟨h1, h2⟩
    by_cases hz : 0 ≤ z.2
    · exact ⟨z, ⟨hz, h2⟩, 0, by simp⟩
    · refine ⟨(z.1, 0), ⟨le_rfl, by simpa using h1⟩, (-z.2).toNat, ?_⟩
      have hc : ((-z.2).toNat : ℤ) = -z.2 := Int.toNat_of_nonneg (by omega)
      simp only [Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
        smul_eq_mul, hc]
      constructor <;> ring

/-- **`hroom` fails on the cone**, at `x = (0,-1)` and `b - a = (1,2)`: `x` is below `cJ = 0`,
`dot nJ (b - a) = 2 > 0`, and `x + (b - a) = (1,1)` is not swept, since `2 * 1 > 1`. -/
theorem hroom_false_on_cone :
    ¬ (∀ x ∈ reachSet coneT (0, -1), dot (0, 1) x < (0 : ℤ) →
        ∀ b ∈ ({(1, 2)} : Finset (ℤ × ℤ)), 0 < dot (0, 1) (b - (0, 0)) →
          x + (b - (0, 0)) ∈ reachSet coneT (0, -1)) := by
  intro h
  have hx : ((0, -1) : ℤ × ℤ) ∈ reachSet coneT (0, -1) := by
    rw [mem_reach_cone]; decide
  have hb : ((1, 2) : ℤ × ℤ) ∈ ({(1, 2)} : Finset (ℤ × ℤ)) := by decide
  have hmem := h (0, -1) hx (by simp [dot]) (1, 2) hb (by simp [dot])
  rw [mem_reach_cone] at hmem
  revert hmem
  decide

/-! ## §2 Receipt 2 — `hroom` is satisfiable

The first-quadrant instance of `tmp/_bottomreach_nonvacuity.lean`, on which every premise of
`bottom_of_reachMin` holds, also satisfies `hroom`.  So `bottom_of_room` is not vacuous. -/

private def quadT : Set (ℤ × ℤ) := {z | 0 ≤ z.1 ∧ 0 ≤ z.2}

private theorem mem_reach_quad (z : ℤ × ℤ) :
    z ∈ reachSet quadT (0, -1) ↔ 0 ≤ z.1 := by
  constructor
  · rintro ⟨g, ⟨hg1, -⟩, t, rfl⟩
    simpa using hg1
  · intro hz
    rcases le_or_gt 0 z.2 with hy | hy
    · exact ⟨z, ⟨hz, hy⟩, 0, by simp⟩
    · refine ⟨(z.1, 0), ⟨hz, le_rfl⟩, (-z.2).toNat, ?_⟩
      have hc : ((-z.2).toNat : ℤ) = -z.2 := Int.toNat_of_nonneg (by omega)
      simp [hc]

/-- **`hroom` holds on the first-quadrant instance**, for the window
`S = {(0,0), (1,0), (0,1)}` anchored at `a = (0,0)`: the only `b` with `0 < dot nJ (b - a)` is
`(0,1)`, whose displacement leaves the first coordinate — the only one `reachSet` constrains —
untouched. -/
theorem hroom_holds_on_quadrant :
    ∀ x ∈ reachSet quadT (0, -1), dot (0, 1) x < (0 : ℤ) →
      ∀ b ∈ ({(0, 0), (1, 0), (0, 1)} : Finset (ℤ × ℤ)), 0 < dot (0, 1) (b - (0, 0)) →
        x + (b - (0, 0)) ∈ reachSet quadT (0, -1) := by
  intro x hx _ b hb hbpos
  rw [mem_reach_quad] at hx ⊢
  have hb' : b = (0, 0) ∨ b = (1, 0) ∨ b = (0, 1) := by simpa using hb
  rcases hb' with rfl | rfl | rfl
  · exact absurd hbpos (by decide)
  · exact absurd hbpos (by decide)
  · simpa using hx

/-! ## §3 The sharp reduction, and why the corner-wedge route does not transfer -/

private theorem ray {T : Set (ℤ × ℤ)} {vJ : ℤ × ℤ} (hrecT : ∀ g ∈ T, g + vJ ∈ T)
    {z : ℤ × ℤ} (hz : z ∈ T) (s : ℕ) : z + (s : ℤ) • vJ ∈ T := by
  induction s with
  | zero => simpa using hz
  | succ n ih =>
    have h := hrecT _ ih
    have he : z + (n : ℤ) • vJ + vJ = z + ((n + 1 : ℕ) : ℤ) • vJ := by
      push_cast [add_smul, one_smul]; abel
    rwa [he] at h

/-- **`hroom` needs exactly one thing: a window-absorbing lift.**

Every sub-`cJ` point `x` of the swept set is `g + t • vJ1` for *some* `g ∈ T`; `hroom` holds as
soon as, for each such `x`, *some one* of its lifts `g` absorbs the raised part of the window.
The sweep bookkeeping is then a single `abel`.  This is the minimal form of the obligation:
nothing about `vJ`, about levels, or about the shape of `T` is used. -/
theorem hroom_of_lift {T : Set (ℤ × ℤ)} {S : Finset (ℤ × ℤ)} {vJ1 nJ a : ℤ × ℤ} {cJ : ℤ}
    (hlift : ∀ x ∈ reachSet T vJ1, dot nJ x < cJ →
      ∃ (g : ℤ × ℤ) (t : ℕ), x = g + (t : ℤ) • vJ1 ∧
        ∀ b ∈ S, 0 < dot nJ (b - a) → g + (b - a) ∈ T) :
    ∀ x ∈ reachSet T vJ1, dot nJ x < cJ →
      ∀ b ∈ S, 0 < dot nJ (b - a) → x + (b - a) ∈ reachSet T vJ1 := by
  intro x hx hxlt b hb hbpos
  obtain ⟨g, t, hxeq, hg⟩ := hlift x hx hxlt
  refine ⟨g + (b - a), hg b hb hbpos, t, ?_⟩
  rw [hxeq]; abel

/-- **The corner-wedge route**, i.e. `TowerRoom.hroomT_of_wedge_and_cont` transported to
`reachSet`, where its `hTowerW_gen` / `hRinf_sweep_gen` inputs are free.  Recorded because it is
the shape the tower side produces — but `wedge_false_on_region` shows `hwedge` is *not* a shape
available here, so this constructor is not the route for `bottom`. -/
theorem hroom_of_corner {T : Set (ℤ × ℤ)} {S : Finset (ℤ × ℤ)} {vJ vJ1 nJ a V : ℤ × ℤ} {cJ : ℤ}
    (hrecT : ∀ g ∈ T, g + vJ ∈ T)
    (hwedge : ∀ x ∈ reachSet T vJ1, dot nJ x < cJ →
      ∃ s t : ℕ, x = V + (s : ℤ) • vJ + (t : ℤ) • vJ1)
    (hcont : ∀ b ∈ S, 0 < dot nJ (b - a) → V + (b - a) ∈ T) :
    ∀ x ∈ reachSet T vJ1, dot nJ x < cJ →
      ∀ b ∈ S, 0 < dot nJ (b - a) → x + (b - a) ∈ reachSet T vJ1 := by
  refine hroom_of_lift (fun x hx hxlt => ?_)
  obtain ⟨s, t, hxeq⟩ := hwedge x hx hxlt
  refine ⟨V + (s : ℤ) • vJ, t, hxeq, fun b hb hbpos => ?_⟩
  have he : V + (s : ℤ) • vJ + (b - a) = V + (b - a) + (s : ℤ) • vJ := by abel
  rw [he]
  exact ray hrecT (hcont b hb hbpos) s

/-! ### §3.1 The witness: a genuine `(ℓ, ℓ_J)`-region whose sub-`cJ` sweep is not a wedge -/

private def rV : ℤ × ℤ := (0, 0)
private def rnJ : ℤ × ℤ := (0, 1)
private def rvJ : ℤ × ℤ := (1, 0)
private def rvJ1 : ℤ × ℤ := (0, -1)

/-- `conv{(0,0), (-3,5)} + cone((1,0), (1,1))`, cut out by three half-planes so that lattice
convexity is free.  Its two semi-infinite edges have directions `(1,0)` and `(1,1)`; the third
(finite) edge runs from `(0,0)` to `(-3,5)`, and it is that edge that breaks the wedge. -/
private def regT : Set (ℤ × ℤ) :=
  ((Set.univ ∩ halfPlaneGE (0, 1) 0) ∩ halfPlaneGE (5, 3) 0) ∩ halfPlaneGE (1, -1) (-8)

private theorem mem_regT {z : ℤ × ℤ} :
    z ∈ regT ↔ 0 ≤ z.2 ∧ 0 ≤ 5 * z.1 + 3 * z.2 ∧ -8 ≤ z.1 - z.2 := by
  simp only [regT, halfPlaneGE, Set.mem_inter_iff, Set.mem_univ, true_and, dot,
    Set.mem_ofPred_eq]
  omega

private theorem latticeConvex_regT : IsLatticeConvexRegion regT :=
  isLatticeConvexRegion_inter_halfPlaneGE
    (isLatticeConvexRegion_inter_halfPlaneGE
      (isLatticeConvexRegion_inter_halfPlaneGE Nivat.Colle41.isLatticeConvexRegion_univ _ _) _ _)
    _ _

/-- The swept set is the proper region `{-3 ≤ x} ∩ {y - 8 ≤ x}` — in particular **not** all of
`ℤ²`, so nothing below is true by degeneration. -/
private theorem mem_reach_regT {z : ℤ × ℤ} :
    z ∈ reachSet regT rvJ1 ↔ (-3 ≤ z.1 ∧ z.2 - 8 ≤ z.1) := by
  constructor
  · rintro ⟨g, hg, t, rfl⟩
    rw [mem_regT] at hg
    simp only [rvJ1, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    have ht : (0 : ℤ) ≤ (t : ℤ) := Int.natCast_nonneg t
    omega
  · rintro ⟨h1, h2⟩
    refine ⟨(z.1, z.2 + (z.1 - z.2 + 8)), ?_, (z.1 - z.2 + 8).toNat, ?_⟩
    · rw [mem_regT]; omega
    · have ht : (((z.1 - z.2 + 8).toNat : ℤ)) = z.1 - z.2 + 8 :=
        Int.toNat_of_nonneg (by omega)
      simp only [rvJ1, Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
        smul_eq_mul, ht]
      constructor <;> ring

private theorem not_mem_reach_regT : ((-4, 0) : ℤ × ℤ) ∉ reachSet regT rvJ1 := by
  rw [mem_reach_regT]; decide

/-- **The corner-wedge premise is false on a genuine region.**

Every structural hypothesis of the `bottom` call site that concerns `Â_∞` alone is certified
here — `Colle41.IsRegion` with both rays, the half-plane `Â_∞ ⊆ {cJ ≤ ⟪n_J, ·⟫}`, the `+v_J`
recession, `⟪n_J, v_J⟫ = 0`, `⟪n_J, v_{J+1}⟫ < 0`, and the bottom row of `Â_∞` being exactly
`V + ℕ·v_J` — and the sub-`cJ` part of `reachSet` is still not the wedge
`V + ℕ·v_J + ℕ·v_{J+1}`: the point `(-3,-1)` is swept down from `(-3,5)`, which sits on the
*finite* edge, three steps to the `-v_J` side of `V`.

Consequence: `hroom_of_corner` cannot be fed from the region structure, and
`TowerRoom.hroomT_of_wedge_and_cont`'s route does **not** transport verbatim.  The lift in
`hroom_of_lift` has to be chosen per point, not once and for all at a corner. -/
theorem wedge_false_on_region :
    Nivat.Colle41.IsRegion regT rvJ (1, 1) ∧
    (regT ⊆ {z | (0 : ℤ) ≤ dot rnJ z}) ∧
    (∀ g ∈ regT, g + rvJ ∈ regT) ∧
    dot rnJ rvJ = 0 ∧ dot rnJ rvJ1 < 0 ∧
    (∀ z : ℤ × ℤ, dot rnJ z = 0 → (z ∈ regT ↔ ∃ s : ℕ, z = rV + (s : ℤ) • rvJ)) ∧
    ((-4, 0) : ℤ × ℤ) ∉ reachSet regT rvJ1 ∧
    ((-3, -1) : ℤ × ℤ) ∈ reachSet regT rvJ1 ∧ dot rnJ ((-3, -1) : ℤ × ℤ) < 0 ∧
    ¬ (∃ s t : ℕ, ((-3, -1) : ℤ × ℤ) = rV + (s : ℤ) • rvJ + (t : ℤ) • rvJ1) := by
  refine ⟨⟨latticeConvex_regT, ⟨rV, fun k => ?_⟩, ⟨(-3, 5), fun k => ?_⟩⟩, ?_, ?_, ?_, ?_, ?_,
    not_mem_reach_regT, ?_, ?_, ?_⟩
  · rw [mem_regT]
    simp only [rV, rvJ, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    have : (0 : ℤ) ≤ (k : ℤ) := Int.natCast_nonneg k
    omega
  · rw [mem_regT]
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    have : (0 : ℤ) ≤ (k : ℤ) := Int.natCast_nonneg k
    omega
  · intro z hz
    rw [mem_regT] at hz
    simp only [Set.mem_ofPred_eq, dot, rnJ]
    omega
  · intro g hg
    rw [mem_regT] at hg ⊢
    simp only [rvJ, Prod.fst_add, Prod.snd_add]
    omega
  · decide
  · decide
  · intro z hz
    simp only [dot, rnJ] at hz
    rw [mem_regT]
    constructor
    · rintro ⟨-, h2, -⟩
      refine ⟨z.1.toNat, ?_⟩
      have ht : ((z.1.toNat : ℤ)) = z.1 := Int.toNat_of_nonneg (by omega)
      simp only [rV, rvJ, Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
        Prod.smul_snd, smul_eq_mul, ht]
      omega
    · rintro ⟨s, rfl⟩
      simp only [rV, rvJ, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
        smul_eq_mul] at hz ⊢
      have : (0 : ℤ) ≤ (s : ℤ) := Int.natCast_nonneg s
      omega
  · rw [mem_reach_regT]; decide
  · decide
  · rintro ⟨s, t, hst⟩
    simp only [rV, rvJ, rvJ1, Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul] at hst
    have hs : (0 : ℤ) ≤ (s : ℤ) := Int.natCast_nonneg s
    omega

/-- **The same witness refutes `hroom` itself**, so `Colle41.IsRegion` is not the missing
premise either — which is what forces the remaining obligation back onto envelopedness.  The
window here is the two-point stand-in `{(0,0), (-1,1)}` with anchor `a := (0,0)`; `(-1,1)` is
the direction in which `𝒮_φ` leaves the corner of its `ℓ_J`-face, so any real `𝒮_φ` with that
edge direction refutes it the same way. -/
theorem hroom_false_on_region :
    ¬ (∀ x ∈ reachSet regT rvJ1, dot rnJ x < 0 →
        ∀ b ∈ ({(0, 0), (-1, 1)} : Finset (ℤ × ℤ)), 0 < dot rnJ (b - ((0, 0) : ℤ × ℤ)) →
          x + (b - ((0, 0) : ℤ × ℤ)) ∈ reachSet regT rvJ1) := by
  intro h
  refine not_mem_reach_regT ?_
  have hx : ((-3, -1) : ℤ × ℤ) ∈ reachSet regT rvJ1 := by rw [mem_reach_regT]; decide
  have := h (-3, -1) hx (by decide) (-1, 1) (by decide) (by decide)
  simpa using this

/-! ### §3.2 `hlift` from the bottom band alone

`hroom_of_lift` asks for a lift per point, which looks like an unbounded amount of choosing.
It is not: `hswept` (`SweptClosed`, a binder of `ofPartsExhaustsInter`) says a point of `Â_∞`
may be swept along `v_{J+1}` freely as long as it stays in `ℋ(ℓ_J)`.  So from any lift one can
slide **down** to the last lift still above `cJ`, and that one lies in the bottom band

    {g ∈ Â_∞ | ⟪n_J, g⟫ + ⟪n_J, v_{J+1}⟫ < cJ}

— the at most `-⟪n_J, v_{J+1}⟫` lowest rows.  The whole obligation is therefore a statement
about those rows, where the envelopedness of `Â_∞`'s `ℓ_J`-face lives. -/

private theorem dot_sweep (n g v : ℤ × ℤ) (t : ℤ) :
    dot n (g + t • v) = dot n g + t * dot n v := by
  simp only [dot, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- Slide down to the last point of `T` on the `v_{J+1}`-ray that is still above `cJ`. -/
private theorem exists_band_lift {T : Set (ℤ × ℤ)} {vJ1 nJ : ℤ × ℤ} {cJ : ℤ}
    (hhp : ∀ g ∈ T, cJ ≤ dot nJ g) (hswept : SweptClosed T vJ1 nJ cJ) :
    ∀ (t₀ : ℕ) (g₀ : ℤ × ℤ), g₀ ∈ T → dot nJ (g₀ + (t₀ : ℤ) • vJ1) < cJ →
      ∃ g ∈ T, ∃ t : ℕ, g₀ + (t₀ : ℤ) • vJ1 = g + (t : ℤ) • vJ1 ∧
        dot nJ g + dot nJ vJ1 < cJ := by
  intro t₀
  induction t₀ with
  | zero =>
    intro g₀ hg₀ hlt
    rw [dot_sweep] at hlt
    have := hhp g₀ hg₀
    push_cast at hlt
    omega
  | succ n ih =>
    intro g₀ hg₀ hlt
    by_cases hb : dot nJ g₀ + dot nJ vJ1 < cJ
    · exact ⟨g₀, hg₀, n + 1, rfl, hb⟩
    · have hstep : g₀ + ((n + 1 : ℕ) : ℤ) • vJ1 = (g₀ + ((1 : ℕ) : ℤ) • vJ1) + (n : ℤ) • vJ1 := by
        push_cast [add_smul, one_smul]; abel
      have h1 : cJ ≤ dot nJ (g₀ + ((1 : ℕ) : ℤ) • vJ1) := by
        rw [dot_sweep]; push_cast; omega
      obtain ⟨g, hg, t, heq, hbnd⟩ := ih _ (hswept g₀ hg₀ 1 h1) (by rwa [hstep] at hlt)
      exact ⟨g, hg, t, by rw [hstep, heq], hbnd⟩

/-- **`hlift` reduces to the bottom band.**  Every hypothesis other than `hband` is already a
binder of `ofPartsExhaustsInter` (`hhp`, `hswept`). -/
theorem hlift_of_band {T : Set (ℤ × ℤ)} {S : Finset (ℤ × ℤ)} {vJ1 nJ a : ℤ × ℤ} {cJ : ℤ}
    (hhp : ∀ g ∈ T, cJ ≤ dot nJ g)
    (hswept : SweptClosed T vJ1 nJ cJ)
    (hband : ∀ g ∈ T, dot nJ g + dot nJ vJ1 < cJ →
      ∀ b ∈ S, 0 < dot nJ (b - a) → g + (b - a) ∈ T) :
    ∀ x ∈ reachSet T vJ1, dot nJ x < cJ →
      ∃ (g : ℤ × ℤ) (t : ℕ), x = g + (t : ℤ) • vJ1 ∧
        ∀ b ∈ S, 0 < dot nJ (b - a) → g + (b - a) ∈ T := by
  rintro x ⟨g₀, hg₀, t₀, rfl⟩ hxlt
  obtain ⟨g, hg, t, heq, hbnd⟩ := exists_band_lift hhp hswept t₀ g₀ hg₀ hxlt
  exact ⟨g, t, heq, hband g hg hbnd⟩

/-- **`hroom` from the bottom band.**  This is the form to discharge at the call site. -/
theorem hroom_of_band {T : Set (ℤ × ℤ)} {S : Finset (ℤ × ℤ)} {vJ1 nJ a : ℤ × ℤ} {cJ : ℤ}
    (hhp : ∀ g ∈ T, cJ ≤ dot nJ g)
    (hswept : SweptClosed T vJ1 nJ cJ)
    (hband : ∀ g ∈ T, dot nJ g + dot nJ vJ1 < cJ →
      ∀ b ∈ S, 0 < dot nJ (b - a) → g + (b - a) ∈ T) :
    ∀ x ∈ reachSet T vJ1, dot nJ x < cJ →
      ∀ b ∈ S, 0 < dot nJ (b - a) → x + (b - a) ∈ reachSet T vJ1 :=
  hroom_of_lift (hlift_of_band hhp hswept hband)

/-- **`hband` is satisfiable** — the first-quadrant instance again, where the band is the
single row `{(s, 0) | s : ℕ}`.  With `hroom_holds_on_quadrant` and `hroom_false_on_region` this
pins `hband` from both sides: not vacuous, and not free. -/
theorem hband_holds_on_quadrant :
    ∀ g ∈ quadT, dot (0, 1) g + dot ((0, 1) : ℤ × ℤ) ((0, -1) : ℤ × ℤ) < (0 : ℤ) →
      ∀ b ∈ ({(0, 0), (1, 0), (0, 1)} : Finset (ℤ × ℤ)), 0 < dot (0, 1) (b - ((0, 0) : ℤ × ℤ)) →
        g + (b - ((0, 0) : ℤ × ℤ)) ∈ quadT := by
  rintro g ⟨hg1, hg2⟩ _ b hb hbpos
  have hb' : b = (0, 0) ∨ b = (1, 0) ∨ b = (0, 1) := by simpa using hb
  rcases hb' with rfl | rfl | rfl
  · exact absurd hbpos (by decide)
  · exact absurd hbpos (by decide)
  · refine ⟨by simpa using hg1, ?_⟩
    have h2 : (g + (((0, 1) : ℤ × ℤ) - ((0, 0) : ℤ × ℤ))).2 = g.2 + 1 := by simp
    rw [h2]
    omega

/-! ### §3.3 The thin band closes completely

The band has `-⟪n_J, v_{J+1}⟫` rows.  When that is `1` the band **is** the bottom row
`V + ℕ·v_J`, and `hband` follows from the corner `V` alone: translate the corner by `b - a`
(that is `HsuppContain.hcont` at `m := n_J` on any large enough finite stage `Â_i`, where
`V` is `Â_i`'s `n_J`-minimal `dir (-n_J)`-start point and `a = F.a` is `𝒮_φ`'s) and then run
`+ℕ·v_J` back out along the row with `hrecT`.

For `-⟪n_J, v_{J+1}⟫ > 1` the band carries `-⟪n_J, v_{J+1}⟫ - 1` further rows whose left
endpoints are interior points of `Â_∞`'s left edge, not vertices, so `hcont` does not reach
them; that part is still open.

⚠ **What `hthin` is worth, quantified (2026-09-25).**  `hthin` is *not* a case split that the
chain may later discharge: `e := -⟪n_J, v_{J+1}⟫` is **data, not a theorem** — the field-complete
`ChainDataGeom` resident `Nivat.ShellConvex.cgc` (`ShellConvex.lean:586`) has `e = 2`
(`cgc_dot_nJ_vJ1`, `ShellConvex.lean:873`) with `bottom` proved.  The exact content of `hthin`
here is `Nivat.CyclicOrderStepT.level_free_of_thin` (`CyclicOrderStepT.lean:98`): at `e = 1`
every level below an occupied one is swept, with no placement information at all.  At `2 ≤ e`
the missing input is a residue condition on `Â_∞`'s heights mod `e`
(`not_bottom_conj1_of_common_residue`, `CyclicOrderStepT.lean:113`), **not** "more rows of
`hcont`".  ⚠ Those two are lane-env-refute's declarations; EXIT/axioms not re-run here (§55). -/

/-- **`hband` on a one-row band.**  Fully discharged — no open premise: `hrow` is the bottom-row
shape (`Â_∞`'s `ℓ_J`-edge is the semi-infinite ray out of `V`), `hcont` is the anchored window
placement at that corner, `hrecT` is `rec_vJ`. -/
theorem hband_of_corner_thin {T : Set (ℤ × ℤ)} {S : Finset (ℤ × ℤ)}
    {vJ vJ1 nJ a V : ℤ × ℤ} {cJ : ℤ}
    (hrecT : ∀ g ∈ T, g + vJ ∈ T)
    (hthin : dot nJ vJ1 = -1)
    (hhp : ∀ g ∈ T, cJ ≤ dot nJ g)
    (hrow : ∀ g ∈ T, dot nJ g = cJ → ∃ s : ℕ, g = V + (s : ℤ) • vJ)
    (hcont : ∀ b ∈ S, 0 < dot nJ (b - a) → V + (b - a) ∈ T) :
    ∀ g ∈ T, dot nJ g + dot nJ vJ1 < cJ →
      ∀ b ∈ S, 0 < dot nJ (b - a) → g + (b - a) ∈ T := by
  intro g hg hbd b hb hbpos
  have hlev : dot nJ g = cJ := by
    have := hhp g hg
    rw [hthin] at hbd
    omega
  obtain ⟨s, rfl⟩ := hrow g hg hlev
  have he : V + (s : ℤ) • vJ + (b - a) = V + (b - a) + (s : ℤ) • vJ := by abel
  rw [he]
  exact ray hrecT (hcont b hb hbpos) s

/-- **`hroom` on a one-row band**, assembled: `hband_of_corner_thin` into `hroom_of_band`.  This
is the complete route for `⟪n_J, v_{J+1}⟫ = -1`. -/
theorem hroom_of_corner_thin {T : Set (ℤ × ℤ)} {S : Finset (ℤ × ℤ)}
    {vJ vJ1 nJ a V : ℤ × ℤ} {cJ : ℤ}
    (hrecT : ∀ g ∈ T, g + vJ ∈ T)
    (hthin : dot nJ vJ1 = -1)
    (hhp : ∀ g ∈ T, cJ ≤ dot nJ g)
    (hswept : SweptClosed T vJ1 nJ cJ)
    (hrow : ∀ g ∈ T, dot nJ g = cJ → ∃ s : ℕ, g = V + (s : ℤ) • vJ)
    (hcont : ∀ b ∈ S, 0 < dot nJ (b - a) → V + (b - a) ∈ T) :
    ∀ x ∈ reachSet T vJ1, dot nJ x < cJ →
      ∀ b ∈ S, 0 < dot nJ (b - a) → x + (b - a) ∈ reachSet T vJ1 :=
  hroom_of_band hhp hswept (hband_of_corner_thin hrecT hthin hhp hrow hcont)

/-- **The thin-band hypotheses are jointly satisfiable**, on the first-quadrant instance:
`V = (0,0)`, `v_J = (1,0)`, `v_{J+1} = (0,-1)`, `n_J = (0,1)`, `cJ = 0`, window
`{(0,0), (1,0), (0,1)}` anchored at `(0,0)`.  Without this the theorem above could be vacuous
(`hrow` is restrictive: it pins the whole level-`cJ` slice onto one forward ray). -/
theorem thin_hypotheses_satisfiable :
    (∀ g ∈ quadT, g + ((1, 0) : ℤ × ℤ) ∈ quadT) ∧
    dot ((0, 1) : ℤ × ℤ) ((0, -1) : ℤ × ℤ) = -1 ∧
    (∀ g ∈ quadT, (0 : ℤ) ≤ dot (0, 1) g) ∧
    SweptClosed quadT (0, -1) (0, 1) 0 ∧
    (∀ g ∈ quadT, dot (0, 1) g = (0 : ℤ) →
      ∃ s : ℕ, g = ((0, 0) : ℤ × ℤ) + (s : ℤ) • ((1, 0) : ℤ × ℤ)) ∧
    (∀ b ∈ ({(0, 0), (1, 0), (0, 1)} : Finset (ℤ × ℤ)), 0 < dot (0, 1) (b - ((0, 0) : ℤ × ℤ)) →
      ((0, 0) : ℤ × ℤ) + (b - ((0, 0) : ℤ × ℤ)) ∈ quadT) := by
  refine ⟨?_, by decide, ?_, ?_, ?_, ?_⟩
  · rintro g ⟨hg1, hg2⟩
    exact ⟨by simpa using by omega, by simpa using hg2⟩
  · rintro g ⟨-, hg2⟩
    simpa [dot] using hg2
  · rintro g ⟨hg1, hg2⟩ t hle
    refine ⟨by simpa using hg1, ?_⟩
    simp only [dot, Prod.snd_add, Prod.smul_snd, smul_eq_mul] at hle ⊢
    omega
  · rintro g ⟨hg1, -⟩ hlev
    simp only [dot] at hlev
    refine ⟨g.1.toNat, ?_⟩
    have hg1' : (0 : ℤ) ≤ g.1 := hg1
    have ht : ((g.1.toNat : ℤ)) = g.1 := Int.toNat_of_nonneg hg1'
    simp only [Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul, ht]
    constructor <;> omega
  · intro b hb hbpos
    have hb' : b = (0, 0) ∨ b = (1, 0) ∨ b = (0, 1) := by simpa using hb
    rcases hb' with rfl | rfl | rfl
    · exact absurd hbpos (by decide)
    · exact absurd hbpos (by decide)
    · exact ⟨by decide, by decide⟩

/-! ### §3.4 The whole band, from two corners

`hband_of_corner_thin` needs the band to be one row.  It need not be: the band has
`-⟪n_J, v_{J+1}⟫ = |det n_J n_prevJ|` rows.  But it still only needs **two** absorbing points.

Write `g - V = α·v_J + β·(-v_{J+1})` — a real basis, since `n_J` kills `v_J` and not `v_{J+1}`
(`det_ne_zero_of_dot`).  Pairing the decomposition with `n_J` gives
`β = ⟪n_J, g - V⟫ / (-⟪n_J, v_{J+1}⟫)`, which the band condition puts in `[0, 1)`; pairing it
with `n_prevJ` — which kills `v_{J+1}` — gives `α = ⟪n_prevJ, g - V⟫ / ⟪n_prevJ, v_J⟫ ≥ 0`, from
the `n_prevJ`-support of `Â_∞` at `V`.  Both `det` factors cancel, so neither pairing needs
primitivity or a sign convention.  Hence

    band ⊆ conv{V, V - v_{J+1}} + ℝ₊·v_J

and the conclusion follows from convexity of `convHullOf Â_∞` plus the `v_J` recession.

So `hroom` is now exactly two instances of anchored window placement, at `V` and at
`V - v_{J+1}` — the bottom-left corner of `Â_∞` and the next lattice point up its `n_prevJ`
face.  At the call site `V` is `g_J` (`hray` puts it on the bottom row, `hsupp_prev_U` makes it
the `n_prevJ`-support point), and both placements are `HsuppContain.hcont` on a large enough
finite stage `Â_i`. -/

private theorem det_decomp (u v z : ℤ × ℤ) :
    det u v • z = det z v • u + det u z • v := by
  ext <;>
    simp only [det, Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add, smul_eq_mul] <;>
    ring

private theorem dotZ (n z : ℤ × ℤ) (c : ℤ) : dot n (c • z) = c * dot n z := by
  simp only [dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

private theorem dotA (n z w : ℤ × ℤ) : dot n (z + w) = dot n z + dot n w := by
  simp only [dot, Prod.fst_add, Prod.snd_add]; ring

private theorem dotN (n z : ℤ × ℤ) : dot n (-z) = -dot n z := by
  simp only [dot, Prod.fst_neg, Prod.snd_neg]; ring

private theorem dotS (n z w : ℤ × ℤ) : dot n (z - w) = dot n z - dot n w := by
  simp only [dot, Prod.fst_sub, Prod.snd_sub]; ring

private theorem tRA (z w : ℤ × ℤ) : toReal (z + w) = toReal z + toReal w := by
  simp only [toReal, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk]; push_cast; rfl

private theorem tRS (z w : ℤ × ℤ) : toReal (z - w) = toReal z - toReal w := by
  simp only [toReal, Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]; push_cast; rfl

private theorem tRN (z : ℤ × ℤ) : toReal (-z) = -toReal z := by
  simp only [toReal, Prod.fst_neg, Prod.snd_neg, Prod.neg_mk]; push_cast; rfl

private theorem tRZ (c : ℤ) (z : ℤ × ℤ) : toReal (c • z) = (c : ℝ) • toReal z := by
  simp only [toReal, Prod.smul_fst, Prod.smul_snd, Prod.smul_mk, smul_eq_mul]; push_cast; rfl

/-- `v_J` and `v_{J+1}` are independent: `n_J` kills the first and not the second. -/
private theorem det_ne_zero_of_dot {vJ vJ1 nJ : ℤ × ℤ} (hvJ : vJ ≠ 0)
    (h0 : dot nJ vJ = 0) (h1 : dot nJ vJ1 ≠ 0) : det vJ (-vJ1) ≠ 0 := by
  intro hdet
  simp only [det, Prod.fst_neg, Prod.snd_neg] at hdet
  simp only [dot] at h0 h1
  refine hvJ (Prod.ext ?_ ?_)
  · have hx : (nJ.1 * vJ1.1 + nJ.2 * vJ1.2) * vJ.1 = 0 := by
      linear_combination vJ1.1 * h0 - nJ.2 * hdet
    rcases mul_eq_zero.mp hx with h | h
    · exact absurd h h1
    · simpa using h
  · have hx : (nJ.1 * vJ1.1 + nJ.2 * vJ1.2) * vJ.2 = 0 := by
      linear_combination vJ1.2 * h0 + nJ.1 * hdet
    rcases mul_eq_zero.mp hx with h | h
    · exact absurd h h1
    · simpa using h

/-- **The whole bottom band absorbs the window, given two absorbing corners `N` apart.**

`V` is `Â_∞`'s bottom-left corner; the second corner is `V - N·v_{J+1}`, any `N ≥ 1` lattice
steps up the `n_prevJ` face.  Writing `g - V = α·v_J + β·(-v_{J+1})` (a real basis,
`det_ne_zero_of_dot`), pairing with `n_J` gives `β = ⟪n_J, g - V⟫ / (-⟪n_J, v_{J+1}⟫) ∈ [0, 1)`
— that is exactly the band condition — and pairing with `n_prevJ` gives
`α = ⟪n_prevJ, g - V⟫ / ⟪n_prevJ, v_J⟫ ≥ 0` from the `n_prevJ`-support of `Â_∞` at `V`.  Since
`β < 1 ≤ N`, every band point lies in `conv{V, V - N·v_{J+1}} + ℝ₊·v_J`, and the conclusion
follows by convexity of the hull plus the `v_J` recession.  Neither pairing needs primitivity
or a sign convention: the `det` factors cancel.

**Why `N` and not `1`** (2026-09-23): the `N = 1` corner is unreachable from
`HsuppContain.hcont`, which anchors the window at `faceStart`s only, so the second placement
it produces sits `faceLen Â_i n_prevJ - faceLen 𝒮_φ n_prevJ` steps up — a number envelopedness
bounds only from below by `0`.  Taking `N` free means any *strict* growth of that face length
suffices; the single bad case is exact equality. -/
theorem hband_of_far_corner {T : Set (ℤ × ℤ)} {S : Finset (ℤ × ℤ)}
    {vJ vJ1 nJ nprevJ a V : ℤ × ℤ} {cJ N : ℤ}
    (hlc : IsLatticeConvexRegion T)
    (hrecT : ∀ g ∈ T, g + vJ ∈ T)
    (hvJ_ne : vJ ≠ 0)
    (hnJvJ : dot nJ vJ = 0)
    (hsweep : dot nJ vJ1 < 0)
    (hnpvJ1 : dot nprevJ vJ1 = 0)
    (hnpvJ : dot nprevJ vJ < 0)
    (hVmem : V ∈ T)
    (hVlev : dot nJ V = cJ)
    (hsupp : ∀ z ∈ T, dot nprevJ z ≤ dot nprevJ V)
    (hhp : ∀ g ∈ T, cJ ≤ dot nJ g)
    (hN : 1 ≤ N)
    (hcoreV : ∀ b ∈ S, 0 < dot nJ (b - a) → V + (b - a) ∈ T)
    (hcoreV' : ∀ b ∈ S, 0 < dot nJ (b - a) → V - N • vJ1 + (b - a) ∈ T) :
    ∀ g ∈ T, dot nJ g + dot nJ vJ1 < cJ →
      ∀ b ∈ S, 0 < dot nJ (b - a) → g + (b - a) ∈ T := by
  intro g hg hbd b hb hbpos
  have hD0 : det vJ (-vJ1) ≠ 0 := det_ne_zero_of_dot hvJ_ne hnJvJ (by omega)
  set c : ℤ × ℤ := b - a with hcdef
  set z : ℤ × ℤ := g - V with hzdef
  have hkey := congrArg (dot nJ) (det_decomp vJ (-vJ1) z)
  rw [dotZ, dotA, dotZ, dotZ, hnJvJ, dotN] at hkey
  have hkey' := congrArg (dot nprevJ) (det_decomp vJ (-vJ1) z)
  rw [dotZ, dotA, dotZ, dotZ, dotN, hnpvJ1] at hkey'
  have hzJ : dot nJ z = dot nJ g - cJ := by rw [hzdef, dotS, hVlev]
  have hjlo : 0 ≤ dot nJ z := by have := hhp g hg; omega
  have hjhi : dot nJ z < -dot nJ vJ1 := by omega
  have hznp : dot nprevJ z ≤ 0 := by
    have := hsupp g hg
    rw [hzdef, dotS]; omega
  have hDR : ((det vJ (-vJ1) : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hD0
  have hδR : ((-dot nJ vJ1 : ℤ) : ℝ) ≠ 0 := by
    have : (-dot nJ vJ1 : ℤ) ≠ 0 := by omega
    exact_mod_cast this
  have hnpR : ((dot nprevJ vJ : ℤ) : ℝ) ≠ 0 := by
    have : (dot nprevJ vJ : ℤ) ≠ 0 := by omega
    exact_mod_cast this
  set α : ℝ := ((dot nprevJ z : ℤ) : ℝ) / ((dot nprevJ vJ : ℤ) : ℝ) with hαdef
  set β : ℝ := ((dot nJ z : ℤ) : ℝ) / ((-dot nJ vJ1 : ℤ) : ℝ) with hβdef
  have hAR : ((det vJ (-vJ1) : ℤ) : ℝ) * β = ((det vJ z : ℤ) : ℝ) := by
    rw [hβdef]
    have hint : det vJ (-vJ1) * dot nJ z = -dot nJ vJ1 * det vJ z := by linarith [hkey]
    field_simp
    exact_mod_cast hint
  have hBR : ((det vJ (-vJ1) : ℤ) : ℝ) * α = ((det z (-vJ1) : ℤ) : ℝ) := by
    rw [hαdef]
    have hint : det vJ (-vJ1) * dot nprevJ z = dot nprevJ vJ * det z (-vJ1) := by
      linarith [hkey']
    field_simp
    exact_mod_cast hint
  have hβ0 : 0 ≤ β := by
    rw [hβdef]
    refine div_nonneg (by exact_mod_cast hjlo) ?_
    have : (0 : ℤ) ≤ -dot nJ vJ1 := by omega
    exact_mod_cast this
  have hβ1 : β < 1 := by
    rw [hβdef, div_lt_one]
    · exact_mod_cast hjhi
    · have : (0 : ℤ) < -dot nJ vJ1 := by omega
      exact_mod_cast this
  have hα0 : 0 ≤ α := by
    rw [hαdef]
    have h1 : ((dot nprevJ z : ℤ) : ℝ) ≤ 0 := by exact_mod_cast hznp
    have h2 : ((dot nprevJ vJ : ℤ) : ℝ) ≤ 0 := by
      have : (dot nprevJ vJ : ℤ) ≤ 0 := by omega
      exact_mod_cast this
    have := div_nonneg (neg_nonneg.mpr h1) (neg_nonneg.mpr h2)
    rwa [neg_div_neg_eq] at this
  -- split the `-v_{J+1}` coefficient across `N` steps
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  set t : ℝ := β / (N : ℝ) with htdef
  have hNt : (N : ℝ) * t = β := by
    rw [htdef]; field_simp
  have ht0 : 0 ≤ t := div_nonneg hβ0 (by linarith)
  have ht1 : t ≤ 1 := by
    rw [htdef, div_le_one (by linarith)]
    linarith
  have hzreal : toReal z = α • toReal vJ + ((N : ℝ) * t) • (-toReal vJ1) := by
    rw [hNt]
    have h := congrArg toReal (det_decomp vJ (-vJ1) z)
    rw [tRZ, tRA, tRZ, tRZ, tRN] at h
    rw [← hAR, ← hBR] at h
    have h2 : toReal z = (((det vJ (-vJ1) : ℤ) : ℝ))⁻¹ •
        ((((det vJ (-vJ1) : ℤ) : ℝ)) • toReal z) := by
      rw [smul_smul, inv_mul_cancel₀ hDR, one_smul]
    rw [h2, h, smul_add, smul_smul, smul_smul, ← mul_assoc, ← mul_assoc,
      inv_mul_cancel₀ hDR, one_mul, one_mul]
  have hXC : toReal (V + c) ∈ convHullOf T := mem_convHullOf_of_mem (hcoreV b hb hbpos)
  have hYC : toReal (V - N • vJ1 + c) ∈ convHullOf T :=
    mem_convHullOf_of_mem (hcoreV' b hb hbpos)
  have hmid : (1 - t) • toReal (V + c) + t • toReal (V - N • vJ1 + c) ∈ convHullOf T :=
    convex_convHullOf T hXC hYC (by linarith) ht0 (by ring)
  have hurec : toReal vJ ∈ recCone T :=
    toReal_mem_recCone_of_nat_ray (fun k => ray hrecT hVmem k)
  have hfinal := smul_mem_recCone hα0 hurec _ hmid
  rw [eq_preimage_convHullOf hlc]
  show toReal (g + c) ∈ convHullOf T
  convert hfinal using 1
  have hgV : toReal g = toReal V + toReal z := by
    rw [hzdef, tRS]; abel
  rw [tRA, tRA, tRA, hgV, hzreal,
    show toReal (V - N • vJ1) = toReal V - (N : ℝ) • toReal vJ1 from by
      rw [tRS, tRZ]]
  module

/-- **The `N = 1` case**: the second corner is the next lattice point up the `n_prevJ` face. -/
theorem hband_of_two_corners {T : Set (ℤ × ℤ)} {S : Finset (ℤ × ℤ)}
    {vJ vJ1 nJ nprevJ a V : ℤ × ℤ} {cJ : ℤ}
    (hlc : IsLatticeConvexRegion T)
    (hrecT : ∀ g ∈ T, g + vJ ∈ T)
    (hvJ_ne : vJ ≠ 0)
    (hnJvJ : dot nJ vJ = 0)
    (hsweep : dot nJ vJ1 < 0)
    (hnpvJ1 : dot nprevJ vJ1 = 0)
    (hnpvJ : dot nprevJ vJ < 0)
    (hVmem : V ∈ T)
    (hVlev : dot nJ V = cJ)
    (hsupp : ∀ z ∈ T, dot nprevJ z ≤ dot nprevJ V)
    (hhp : ∀ g ∈ T, cJ ≤ dot nJ g)
    (hcoreV : ∀ b ∈ S, 0 < dot nJ (b - a) → V + (b - a) ∈ T)
    (hcoreV' : ∀ b ∈ S, 0 < dot nJ (b - a) → V - vJ1 + (b - a) ∈ T) :
    ∀ g ∈ T, dot nJ g + dot nJ vJ1 < cJ →
      ∀ b ∈ S, 0 < dot nJ (b - a) → g + (b - a) ∈ T :=
  hband_of_far_corner hlc hrecT hvJ_ne hnJvJ hsweep hnpvJ1 hnpvJ hVmem hVlev hsupp hhp
    (N := 1) le_rfl hcoreV (by simpa using hcoreV')

/-- **`hroom` from two corners**, assembled.  The general-`δ` replacement for
`hroom_of_corner_thin`. -/
theorem hroom_of_two_corners {T : Set (ℤ × ℤ)} {S : Finset (ℤ × ℤ)}
    {vJ vJ1 nJ nprevJ a V : ℤ × ℤ} {cJ : ℤ}
    (hlc : IsLatticeConvexRegion T)
    (hrecT : ∀ g ∈ T, g + vJ ∈ T)
    (hvJ_ne : vJ ≠ 0)
    (hnJvJ : dot nJ vJ = 0)
    (hsweep : dot nJ vJ1 < 0)
    (hnpvJ1 : dot nprevJ vJ1 = 0)
    (hnpvJ : dot nprevJ vJ < 0)
    (hVmem : V ∈ T)
    (hVlev : dot nJ V = cJ)
    (hsupp : ∀ z ∈ T, dot nprevJ z ≤ dot nprevJ V)
    (hhp : ∀ g ∈ T, cJ ≤ dot nJ g)
    (hswept : SweptClosed T vJ1 nJ cJ)
    (hcoreV : ∀ b ∈ S, 0 < dot nJ (b - a) → V + (b - a) ∈ T)
    (hcoreV' : ∀ b ∈ S, 0 < dot nJ (b - a) → V - vJ1 + (b - a) ∈ T) :
    ∀ x ∈ reachSet T vJ1, dot nJ x < cJ →
      ∀ b ∈ S, 0 < dot nJ (b - a) → x + (b - a) ∈ reachSet T vJ1 :=
  hroom_of_band hhp hswept
    (hband_of_two_corners hlc hrecT hvJ_ne hnJvJ hsweep hnpvJ1 hnpvJ hVmem hVlev hsupp hhp
      hcoreV hcoreV')

/-- **`hroom` from two corners `N` apart**, assembled.  The form the call site should use once
the `n_prevJ` face length gap is known: any `N ≥ 1` works. -/
theorem hroom_of_far_corner {T : Set (ℤ × ℤ)} {S : Finset (ℤ × ℤ)}
    {vJ vJ1 nJ nprevJ a V : ℤ × ℤ} {cJ N : ℤ}
    (hlc : IsLatticeConvexRegion T)
    (hrecT : ∀ g ∈ T, g + vJ ∈ T)
    (hvJ_ne : vJ ≠ 0)
    (hnJvJ : dot nJ vJ = 0)
    (hsweep : dot nJ vJ1 < 0)
    (hnpvJ1 : dot nprevJ vJ1 = 0)
    (hnpvJ : dot nprevJ vJ < 0)
    (hVmem : V ∈ T)
    (hVlev : dot nJ V = cJ)
    (hsupp : ∀ z ∈ T, dot nprevJ z ≤ dot nprevJ V)
    (hhp : ∀ g ∈ T, cJ ≤ dot nJ g)
    (hswept : SweptClosed T vJ1 nJ cJ)
    (hN : 1 ≤ N)
    (hcoreV : ∀ b ∈ S, 0 < dot nJ (b - a) → V + (b - a) ∈ T)
    (hcoreV' : ∀ b ∈ S, 0 < dot nJ (b - a) → V - N • vJ1 + (b - a) ∈ T) :
    ∀ x ∈ reachSet T vJ1, dot nJ x < cJ →
      ∀ b ∈ S, 0 < dot nJ (b - a) → x + (b - a) ∈ reachSet T vJ1 :=
  hroom_of_band hhp hswept
    (hband_of_far_corner hlc hrecT hvJ_ne hnJvJ hsweep hnpvJ1 hnpvJ hVmem hVlev hsupp hhp hN
      hcoreV hcoreV')

private def bandT : Set (ℤ × ℤ) :=
  (Set.univ ∩ halfPlaneGE (0, 1) 0) ∩ halfPlaneGE (2, 1) 0

private theorem mem_bandT {z : ℤ × ℤ} : z ∈ bandT ↔ 0 ≤ z.2 ∧ 0 ≤ 2 * z.1 + z.2 := by
  simp only [bandT, halfPlaneGE, Set.mem_inter_iff, Set.mem_univ, true_and, dot,
    Set.mem_ofPred_eq]
  omega

private theorem latticeConvex_bandT : IsLatticeConvexRegion bandT :=
  isLatticeConvexRegion_inter_halfPlaneGE
    (isLatticeConvexRegion_inter_halfPlaneGE Nivat.Colle41.isLatticeConvexRegion_univ _ _) _ _

/-- **The two-corner hypotheses are satisfiable on a band that is genuinely two rows deep** —
the case `hband_of_corner_thin` cannot reach.  `n_J = (0,1)`, `v_J = (1,0)`,
`v_{J+1} = (1,-2)` (so `⟪n_J, v_{J+1}⟫ = -2`), `n_prevJ = (-2,-1)`, `cJ = 0`, `V = (0,0)`,
`T = {0 ≤ y} ∩ {0 ≤ 2x + y}`, window `{(0,0), (0,1)}` anchored at `(0,0)`.  The last two
conjuncts exhibit both band rows as nonempty, so the extra rows are really exercised. -/
theorem two_corner_hypotheses_satisfiable :
    IsLatticeConvexRegion bandT ∧
    (∀ g ∈ bandT, g + ((1, 0) : ℤ × ℤ) ∈ bandT) ∧
    ((1, 0) : ℤ × ℤ) ≠ 0 ∧
    dot ((0, 1) : ℤ × ℤ) ((1, 0) : ℤ × ℤ) = 0 ∧
    dot ((0, 1) : ℤ × ℤ) ((1, -2) : ℤ × ℤ) < 0 ∧
    dot ((-2, -1) : ℤ × ℤ) ((1, -2) : ℤ × ℤ) = 0 ∧
    dot ((-2, -1) : ℤ × ℤ) ((1, 0) : ℤ × ℤ) < 0 ∧
    ((0, 0) : ℤ × ℤ) ∈ bandT ∧
    dot ((0, 1) : ℤ × ℤ) ((0, 0) : ℤ × ℤ) = 0 ∧
    (∀ z ∈ bandT, dot (-2, -1) z ≤ dot ((-2, -1) : ℤ × ℤ) ((0, 0) : ℤ × ℤ)) ∧
    (∀ g ∈ bandT, (0 : ℤ) ≤ dot (0, 1) g) ∧
    (∀ b ∈ ({(0, 0), (0, 1)} : Finset (ℤ × ℤ)), 0 < dot (0, 1) (b - ((0, 0) : ℤ × ℤ)) →
      ((0, 0) : ℤ × ℤ) + (b - ((0, 0) : ℤ × ℤ)) ∈ bandT) ∧
    (∀ b ∈ ({(0, 0), (0, 1)} : Finset (ℤ × ℤ)), 0 < dot (0, 1) (b - ((0, 0) : ℤ × ℤ)) →
      ((0, 0) : ℤ × ℤ) - (1, -2) + (b - ((0, 0) : ℤ × ℤ)) ∈ bandT) ∧
    (((0, 0) : ℤ × ℤ) ∈ bandT ∧
      dot ((0, 1) : ℤ × ℤ) ((0, 0) : ℤ × ℤ) + dot ((0, 1) : ℤ × ℤ) ((1, -2) : ℤ × ℤ) < 0) ∧
    (((0, 1) : ℤ × ℤ) ∈ bandT ∧
      dot ((0, 1) : ℤ × ℤ) ((0, 1) : ℤ × ℤ) + dot ((0, 1) : ℤ × ℤ) ((1, -2) : ℤ × ℤ) < 0) := by
  refine ⟨latticeConvex_bandT, ?_, by decide, by decide, by decide, by decide, by decide,
    by rw [mem_bandT]; decide, by decide, ?_, ?_, ?_, ?_,
    ⟨by rw [mem_bandT]; decide, by decide⟩, ⟨by rw [mem_bandT]; decide, by decide⟩⟩
  · intro g hg
    rw [mem_bandT] at hg ⊢
    simp only [Prod.fst_add, Prod.snd_add]
    omega
  · intro z hz
    rw [mem_bandT] at hz
    simp only [dot]
    omega
  · intro g hg
    rw [mem_bandT] at hg
    simp only [dot]
    omega
  · intro b hb hbpos
    have hb' : b = (0, 0) ∨ b = (0, 1) := by simpa using hb
    rcases hb' with rfl | rfl
    · exact absurd hbpos (by decide)
    · rw [mem_bandT]; decide
  · intro b hb hbpos
    have hb' : b = (0, 0) ∨ b = (0, 1) := by simpa using hb
    rcases hb' with rfl | rfl
    · exact absurd hbpos (by decide)
    · rw [mem_bandT]; decide

/-! ## §4 The premise is only ever read at `z₀`

`bottom_of_room` above quantifies `hroom` over every `x ∈ reachSet T vJ1` below `cJ`, but its
proof instantiates it **once**, at `x := z₀`.  §3's whole chain (`hroom_of_lift` →
`hlift_of_band` → `hband_of_two_corners`) therefore proves strictly more than `bottom` needs:
it covers the entire bottom band, while the conclusion only ever asks about the reach-minimal
point of the single level `cJ - ε - 1`.

`bottom_of_window` is that minimal interface.  Its premise `hwin` is exactly
`BottomReachMin.bottom_of_reachMin`'s `hlow`-and-`hhigh` merged along `dot nJ vJ = 0` (neither
conclusion mentions `ε`, so the split at `ε` was an artifact), and it is the weakest of the
four forms in this file:

    hwin ⟸ hroom ⟸ hband ⟸ (hcoreV ∧ hcoreV')

Non-vacuity is already on record: `tmp/_bottomreach_nonvacuity.lean`
(`bottom_reachMin_hypotheses_satisfiable`) certifies `hrecT, hdz, hz₀, hline0, hedge, hlow,
hhigh` simultaneously on the closed first quadrant, and `hwin` is `hlow ∧ hhigh`. -/

/-- **`bottom` from the window fitting at `z₀` alone.**  Same conclusion as `bottom_of_room`,
with `hroom` weakened to its single used instance. -/
theorem bottom_of_window {T : Set (ℤ × ℤ)} {S : Finset (ℤ × ℤ)}
    {nJ vJ vJ1 z₀ a : ℤ × ℤ} {cJ : ℤ} {ε : ℕ}
    (hrecT : ∀ g ∈ T, g + vJ ∈ T)
    (hdz : dot nJ z₀ = cJ - (ε : ℤ) - 1)
    (hz₀ : z₀ ∈ reachSet T vJ1)
    (hline0 : ∀ z ∈ reachSet T vJ1, dot nJ z = cJ - (ε : ℤ) - 1 →
      ∃ k : ℤ, 0 ≤ k ∧ z = z₀ + k • vJ)
    (hedge : ∀ b ∈ S.erase a,
      (∃ j : ℕ, 1 ≤ j ∧ b = a + (j : ℤ) • vJ) ∨ 1 ≤ dot nJ (b - a))
    (hwin : ∀ b ∈ S, 0 < dot nJ (b - a) → z₀ + (b - a) ∈ reachSet T vJ1) :
    ∃ (z₀' : ℤ × ℤ) (L : ℤ),
      dot nJ z₀' = cJ - (ε : ℤ) - 1 ∧
      (∀ k : ℤ, L ≤ k → z₀' + k • vJ ∈ reachSet T vJ1) ∧
      (∀ b ∈ S, ∀ k : ℤ, L ≤ k → z₀' + k • vJ + (b - a) ∈ reachSet T vJ1) ∧
      (∀ z ∈ shell T vJ1 nJ cJ (ε + 1),
        z ∈ shell T vJ1 nJ cJ ε ∨ ∃ k : ℤ, L ≤ k ∧ z = z₀' + k • vJ) :=
  BottomReachMin.bottom_of_reachMin hrecT hdz hz₀ hline0 hedge
    (fun b hb h1 _ => hwin b hb (by omega))
    (fun b hb h => hwin b hb (by
      have : (0 : ℤ) ≤ (ε : ℤ) := Int.natCast_nonneg ε
      omega))

/-! ## §5 `hwin` is `HsuppContain.hcont` on the finite enveloped shell

This is the route `b3_colle2.txt:518-520` takes, and the first consumer of
`HsuppContain.hcont` (`HsuppContain.lean:413`, 0 sorry) in the main tree.

    Â_i^{(ε)} := {g - t v_{ℓ_{J+1}} ∈ Â_∞^{(ε)} : g ∈ Â_i, t ∈ ℤ_+}   is E(𝒮_φ)-enveloped

`hcont` at `m := n_J` on `P := Â_i^{(ε+1)}` returns `∀ b ∈ 𝒮_φ, V + (b - a) ∈ P` for `V` the
`n_J`-minimal `dir (-n_J)`-start corner of `P`.  Three facts make `V = z₀`:

* `⋃_i Â_i^{(ε)} = Â_∞^{(ε)}`, so `z₀ ∈ Â_i^{(ε+1)}` once `i` is large;
* `z₀` is reach-minimal in the whole of `Â_∞^{(ε+1)}` at its level (`hline0`), so a fortiori
  in the subset `Â_i^{(ε+1)}` — that is `hz₀min`/`hz₀end`;
* `P ⊆ reachSet Â_∞ v_{J-1}`, so the conclusion lands where `bottom` reads it.

What §5 does **not** do is produce `P`.  `hEeq`/`henv` here are precisely the `shellEnv`
binder of `ChainDataGeom.ofPartsExhaustsInter` (`ChainExhaustInter.lean`), so the two GAPs
are one GAP; the paper proves neither ("Note that […] is an `E(𝒮_φ)`-enveloped set", `:516`).

⚠ Non-vacuity is **not** certified by a concrete instance, and cannot be cheaply: `hcont`
takes a `d : DecompDataZ η`, which the repo only manufactures from
`IsMinimalCounterexample` (`DecompDataZ.of_minimalCounterexample`, `DecompData.lean:275`).
The hypotheses §5 adds on top of `hcont`'s own list are `hPsub` (satisfiable at `T := P`,
`t = 0`), `hnJvJ` and `hedge` (both discharged at the call site by the `FaceBlock`), so §5
inherits exactly `hcont`'s status and adds no new joint constraint. -/

/-- **The two `hcont` anchor conditions at `a`, read off `FaceBlock.edge`.**  `ha_min` says
`a` minimises `dot nJ` over `S`; `ha_end` says the minimising row is the forward `vJ`-run out
of `a`.  Both are `hedge` plus `dot nJ vJ = 0` — the `vJ`-run disjunct is level-preserving, and
the other disjunct raises by at least `1`. -/
theorem faceStart_of_edge {S : Finset (ℤ × ℤ)} {nJ vJ a : ℤ × ℤ}
    (hnJvJ : dot nJ vJ = 0)
    (hedge : ∀ b ∈ S.erase a,
      (∃ j : ℕ, 1 ≤ j ∧ b = a + (j : ℤ) • vJ) ∨ 1 ≤ dot nJ (b - a)) :
    (∀ b ∈ (↑S : Set (ℤ × ℤ)), dot nJ a ≤ dot nJ b) ∧
    (∀ b ∈ (↑S : Set (ℤ × ℤ)), dot nJ b = dot nJ a → ∃ t : ℕ, b = a + (t : ℤ) • vJ) := by
  have key : ∀ b ∈ (↑S : Set (ℤ × ℤ)), b = a ∨
      (∃ j : ℕ, 1 ≤ j ∧ b = a + (j : ℤ) • vJ) ∨ 1 ≤ dot nJ (b - a) := by
    intro b hb
    by_cases hba : b = a
    · exact Or.inl hba
    · exact Or.inr (hedge b (Finset.mem_erase.mpr ⟨hba, hb⟩))
  constructor
  · intro b hb
    rcases key b hb with rfl | ⟨j, -, rfl⟩ | h
    · exact le_rfl
    · rw [dot_add, Nivat.ColleReg.dot_zsmul_right, hnJvJ]; simp
    · rw [dot_sub] at h; omega
  · intro b hb hlev
    rcases key b hb with rfl | ⟨j, -, rfl⟩ | h
    · exact ⟨0, by simp⟩
    · exact ⟨j, rfl⟩
    · rw [dot_sub] at h; omega

/-- **`hwin` from an enveloped finite shell `P` sitting inside `reachSet T vJ1`.**

`P` is `Â_i^{(ε+1)}`; `hEeq`/`henv` are its `E(𝒮_φ)`-envelopedness, `hz₀P`/`hz₀min`/`hz₀end`
say `z₀` is its `dir (-n_J)`-start corner on the `n_J`-lowest row.  The conclusion is stronger
than `bottom_of_window`'s `hwin`: it holds for every `b ∈ 𝒮_φ`, guard or not. -/
theorem window_of_shell {η : Config ℤ} (d : Nivat.Colle35.DecompDataZ η)
    {T P : Set (ℤ × ℤ)} {nJ vJ vJ1 z₀ a : ℤ × ℤ}
    (hPfin : P.Finite) (hPne : P.Nonempty) (hParea : PosArea P)
    (hlcP : IsLatticeConvexRegion P)
    (hPsub : P ⊆ reachSet T vJ1)
    (hvJ_eq : vJ = dir (-nJ)) (hnJ_ne : nJ ≠ 0)
    (hEeq : E P = E (↑d.toDecompData.Sphi : Set (ℤ × ℤ)))
    (hnegm_mem : -nJ ∈ E (↑d.toDecompData.Sphi : Set (ℤ × ℤ)))
    (henv : ∀ n ∈ E P,
      (face (↑d.toDecompData.Sphi : Set (ℤ × ℤ)) n).encard ≤ (face P n).encard)
    (ha_mem : a ∈ (↑d.toDecompData.Sphi : Set (ℤ × ℤ)))
    (hnJvJ : dot nJ vJ = 0)
    (hedge : ∀ b ∈ d.toDecompData.Sphi.erase a,
      (∃ j : ℕ, 1 ≤ j ∧ b = a + (j : ℤ) • vJ) ∨ 1 ≤ dot nJ (b - a))
    (hz₀P : z₀ ∈ P)
    (hz₀min : ∀ b ∈ P, dot nJ z₀ ≤ dot nJ b)
    (hz₀end : ∀ b ∈ P, dot nJ b = dot nJ z₀ → ∃ t : ℕ, b = z₀ + (t : ℤ) • vJ) :
    ∀ b ∈ d.toDecompData.Sphi, z₀ + (b - a) ∈ reachSet T vJ1 := by
  obtain ⟨ha_min, ha_end⟩ := faceStart_of_edge hnJvJ hedge
  intro b hb
  exact hPsub (Nivat.HsuppContain.hcont d hPfin hPne hParea hlcP hvJ_eq hnJ_ne hEeq
    hnegm_mem henv ha_mem ha_min ha_end hz₀P hz₀min hz₀end b hb)

/-! ### §6 (2026-09-25) — `window_of_shell`'s three `z₀`-side premises are already paid for

`window_of_shell` takes seventeen binders.  Three of them — `hPsub`, `hz₀min`, `hz₀end` — are
**not** new obligations.  They follow from one containment, `P ⊆ Â_∞^{(ε+1)}` (which for
`P := Â_i^{(ε+1)}` is `ShellMink.shellInter_subset_right`, `ShellMink.lean:572`), together
with the two binders `BottomReachMin.bottom_of_reachMin` (`BottomReachMin.lean:151`) already
carries, `hdz` and `hline0`.

* `hPsub` — `MaxEnv.shell_eq_reach_inter` (`ShellLine.lean:43`) *is*
  `shell = reachSet ∩ half-plane`, so the containment hands over the `reachSet` component.
* `hz₀min` — the same intersection gives `cJ - (ε + 1) ≤ dot nJ b` for every `b ∈ P`, and
  `hdz` says `dot nJ z₀ = cJ - ε - 1`, which is that bound verbatim.  So `z₀` sits on the
  lowest line the shell admits and nothing in `P` can be below it.  This is
  `b3_colle2.txt:442` read the right way round: `0 = d_0 < d_1 < ⋯` enumerates the distances
  *attained*, so the `(ε+1)`-shell's new layer is the last line it has.
* `hz₀end` — `hline0` already says every reachable point at `z₀`'s level is `z₀ + k • vJ`
  with `k ≥ 0`; `hPsub` restricts that to `P` and `k.toNat` supplies the `ℕ`.

⟹ **nobody has to prove that `z₀` is the shell's `dir (-n_J)`-start corner — `hline0` makes
it one.**  In particular the `bottom`-side and `NlmaxReachMin`-side `z₀` cannot disagree, so
no "do the two witnesses coincide" lemma is needed between the two lanes.

What survives of `window_of_shell` after this:

* `hEeq` / `henv` — the consumer's `shellEnv` binder, already recorded in §5 as the same hole;
  Collé asserts it (`b3_colle2.txt:516`, `:520`) and proves it nowhere.
* `hz₀P` — `z₀ ∈ Â_i^{(ε+1)}` for large `i`, i.e. `⋃_i Â_i^{(ε)} = Â_∞^{(ε)}`.
* `hPfin` / `hPne` / `hParea` / `hlcP` — properties of `shellInter`, not facts about `z₀`.

⚠ This section says nothing about `hvJ_eq : vJ = dir (-nJ)`.  That binder is
orientation-sensitive and the round-179 redline forbids moving it in either direction until
"chain `vl` ＝ source `v⃗_{ℓ_ι}`" is settled; it is carried through unexamined.

⚠ Nothing here weakens the `hhigh` refutations (`tmp/wip/lane-cd-hhigh-refute.lean`,
`-refute2.lean`; both re-verified 2026-09-25, `check1.sh EXIT=0`, axioms clean).  Those refute
`hhigh` against an **abstract** `T` and against `WeaklyEnveloped ↑S T`; they supply no finite
`P` with `E P = E ↑S`, and by their own §"Consequence" the repair has to come from the finite
stages — which is the route `window_of_shell` takes.
-/

/-- **The three `z₀`-side premises of `window_of_shell`, from `hdz` and `hline0`.**

`P` is `Â_i^{(ε+1)}` and `shell T vJ1 nJ cJ (ε+1)` is `Â_∞^{(ε+1)}`.  Nothing about
envelopedness, finiteness or `S` is used — this is the level bookkeeping only. -/
theorem shellCorner_of_line {T P : Set (ℤ × ℤ)} {nJ vJ vJ1 z₀ : ℤ × ℤ} {cJ : ℤ} {ε : ℕ}
    (hPshell : P ⊆ shell T vJ1 nJ cJ (ε + 1))
    (hdz : dot nJ z₀ = cJ - (ε : ℤ) - 1)
    (hline0 : ∀ z ∈ reachSet T vJ1, dot nJ z = cJ - (ε : ℤ) - 1 →
      ∃ k : ℤ, 0 ≤ k ∧ z = z₀ + k • vJ) :
    P ⊆ reachSet T vJ1 ∧
    (∀ b ∈ P, dot nJ z₀ ≤ dot nJ b) ∧
    (∀ b ∈ P, dot nJ b = dot nJ z₀ → ∃ t : ℕ, b = z₀ + (t : ℤ) • vJ) := by
  have key : ∀ b ∈ P, b ∈ reachSet T vJ1 ∧ cJ - ((ε : ℤ) + 1) ≤ dot nJ b := by
    intro b hb
    have hmem := hPshell hb
    rw [shell_eq_reach_inter] at hmem
    obtain ⟨hr, hd⟩ := hmem
    simp only [Set.mem_ofPred_eq] at hd
    push_cast at hd
    exact ⟨hr, by omega⟩
  refine ⟨fun b hb => (key b hb).1, fun b hb => ?_, fun b hb hlev => ?_⟩
  · have hge := (key b hb).2
    rw [hdz]
    omega
  · obtain ⟨k, hk0, hk⟩ := hline0 b (key b hb).1 (by rw [hlev]; exact hdz)
    refine ⟨k.toNat, ?_⟩
    rwa [Int.toNat_of_nonneg hk0]

/-- **`hwin` from the enveloped finite shell, with the `z₀`-side premises discharged.**

Same conclusion as `window_of_shell`, with its `hPsub` / `hz₀min` / `hz₀end` replaced by the
containment `P ⊆ Â_∞^{(ε+1)}` and `bottom_of_reachMin`'s own `hdz` / `hline0`.  This is the
form the `bottom` call site can actually feed: every premise other than `hEeq` / `henv`
(= `shellEnv`) and `hz₀P` is either a binder it already holds or a property of `shellInter`. -/
theorem window_of_shell_of_line {η : Config ℤ} (d : Nivat.Colle35.DecompDataZ η)
    {T P : Set (ℤ × ℤ)} {nJ vJ vJ1 z₀ a : ℤ × ℤ} {cJ : ℤ} {ε : ℕ}
    (hPfin : P.Finite) (hPne : P.Nonempty) (hParea : PosArea P)
    (hlcP : IsLatticeConvexRegion P)
    (hPshell : P ⊆ shell T vJ1 nJ cJ (ε + 1))
    (hvJ_eq : vJ = dir (-nJ)) (hnJ_ne : nJ ≠ 0)
    (hEeq : E P = E (↑d.toDecompData.Sphi : Set (ℤ × ℤ)))
    (hnegm_mem : -nJ ∈ E (↑d.toDecompData.Sphi : Set (ℤ × ℤ)))
    (henv : ∀ n ∈ E P,
      (face (↑d.toDecompData.Sphi : Set (ℤ × ℤ)) n).encard ≤ (face P n).encard)
    (ha_mem : a ∈ (↑d.toDecompData.Sphi : Set (ℤ × ℤ)))
    (hnJvJ : dot nJ vJ = 0)
    (hedge : ∀ b ∈ d.toDecompData.Sphi.erase a,
      (∃ j : ℕ, 1 ≤ j ∧ b = a + (j : ℤ) • vJ) ∨ 1 ≤ dot nJ (b - a))
    (hz₀P : z₀ ∈ P)
    (hdz : dot nJ z₀ = cJ - (ε : ℤ) - 1)
    (hline0 : ∀ z ∈ reachSet T vJ1, dot nJ z = cJ - (ε : ℤ) - 1 →
      ∃ k : ℤ, 0 ≤ k ∧ z = z₀ + k • vJ) :
    ∀ b ∈ d.toDecompData.Sphi, z₀ + (b - a) ∈ reachSet T vJ1 := by
  obtain ⟨hPsub, hz₀min, hz₀end⟩ := shellCorner_of_line hPshell hdz hline0
  exact window_of_shell d hPfin hPne hParea hlcP hPsub hvJ_eq hnJ_ne hEeq hnegm_mem henv
    ha_mem hnJvJ hedge hz₀P hz₀min hz₀end

end Nivat.BottomRoom

#print axioms Nivat.BottomRoom.bottom_of_room
#print axioms Nivat.BottomRoom.hroom_false_on_cone
#print axioms Nivat.BottomRoom.hroom_holds_on_quadrant
#print axioms Nivat.BottomRoom.hroom_of_lift
#print axioms Nivat.BottomRoom.hroom_of_corner
#print axioms Nivat.BottomRoom.wedge_false_on_region
#print axioms Nivat.BottomRoom.hroom_false_on_region
#print axioms Nivat.BottomRoom.hlift_of_band
#print axioms Nivat.BottomRoom.hroom_of_band
#print axioms Nivat.BottomRoom.hband_holds_on_quadrant
#print axioms Nivat.BottomRoom.hband_of_corner_thin
#print axioms Nivat.BottomRoom.hroom_of_corner_thin
#print axioms Nivat.BottomRoom.thin_hypotheses_satisfiable
#print axioms Nivat.BottomRoom.hband_of_far_corner
#print axioms Nivat.BottomRoom.hband_of_two_corners
#print axioms Nivat.BottomRoom.hroom_of_two_corners
#print axioms Nivat.BottomRoom.hroom_of_far_corner
#print axioms Nivat.BottomRoom.two_corner_hypotheses_satisfiable
#print axioms Nivat.BottomRoom.bottom_of_window
#print axioms Nivat.BottomRoom.faceStart_of_edge
#print axioms Nivat.BottomRoom.window_of_shell
#print axioms Nivat.BottomRoom.shellCorner_of_line
#print axioms Nivat.BottomRoom.window_of_shell_of_line

#print axioms Nivat.BottomRoom.coneT
#print axioms Nivat.BottomRoom.mem_reach_cone
#print axioms Nivat.BottomRoom.quadT
#print axioms Nivat.BottomRoom.mem_reach_quad
#print axioms Nivat.BottomRoom.ray
#print axioms Nivat.BottomRoom.rV
#print axioms Nivat.BottomRoom.rnJ
#print axioms Nivat.BottomRoom.rvJ
#print axioms Nivat.BottomRoom.rvJ1
#print axioms Nivat.BottomRoom.regT
#print axioms Nivat.BottomRoom.mem_regT
#print axioms Nivat.BottomRoom.latticeConvex_regT
#print axioms Nivat.BottomRoom.mem_reach_regT
#print axioms Nivat.BottomRoom.not_mem_reach_regT
#print axioms Nivat.BottomRoom.dot_sweep
#print axioms Nivat.BottomRoom.exists_band_lift
#print axioms Nivat.BottomRoom.det_decomp
#print axioms Nivat.BottomRoom.dotZ
#print axioms Nivat.BottomRoom.dotA
#print axioms Nivat.BottomRoom.dotN
#print axioms Nivat.BottomRoom.dotS
#print axioms Nivat.BottomRoom.tRA
#print axioms Nivat.BottomRoom.tRS
#print axioms Nivat.BottomRoom.tRN
#print axioms Nivat.BottomRoom.tRZ
#print axioms Nivat.BottomRoom.det_ne_zero_of_dot
#print axioms Nivat.BottomRoom.bandT
#print axioms Nivat.BottomRoom.mem_bandT
#print axioms Nivat.BottomRoom.latticeConvex_bandT
