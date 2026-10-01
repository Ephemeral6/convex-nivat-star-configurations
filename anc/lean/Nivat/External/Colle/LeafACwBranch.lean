/-
Lane `lane-cd-cw` (sub-lane of `lane-chaindata-lead`), 2026-09-22.  `tmp/wip/`, 0 `sorry`.

# The `dir (-nℓ) = -vl` (clockwise) branch of `tmp/wip/LeafAAssemble.lean:235`

**Purpose.**  `tmp/wip/LeafAAssemble.lean` splits on the orientation
`dir (-nℓ) = vl ∨ dir (-nℓ) = -vl` (`LeafAAssemble.lean:219`).  The `= vl` (ccw) branch is
wired; the `= -vl` (cw) branch was a named `sorry`.  This file packages the cw branch's
`J`-selection output into ONE tuple `(J, vJ1, wJ, g_J, σ, i₀)` with exactly the seven
conjuncts that the ccw branch also produces, so that the shell/fill obligations downstream
of the split can be written once.  `ℓ` below is instantiated by the caller as `-nℓ`.

Paper: `delivery/scratch/b3_colle2.txt:498` (the choice of `J` as the smallest index whose
edge `w_i(J)` grows without bound, with every strictly-earlier edge stabilising),
`delivery/scratch/b3_colle2.txt:506` (`Â_∞` is an `(ℓ, ℓ_J)`-region: two semi-infinite edges,
one parallel to `ℓ` and one parallel to `ℓ_J`), and
`delivery/scratch/b3_colle2.txt:440` (`v_{ℓ_{J-1}}`, the fan-neighbour direction that becomes
`vJ1`).

## §0. The worked numeric wedge (硬规矩 6 — computed on paper first, Lean-checked in §1)

Region (lattice-convex, finite): the hexagon

    Hex := {z : ℤ × ℤ | -2 ≤ z.1 ≤ 2, -2 ≤ z.2 ≤ 2, -2 ≤ z.1 - z.2 ≤ 2}

whose six edge normals are `E = {(1,0), (0,1), (-1,1), (-1,0), (0,-1), (1,-1)}`
(one per binding inequality).  Recall `dir (a,b) = (-b, a)` (`LatticeEdges.lean:248`,
`dir`), `det u v = u.1*v.2 - u.2*v.1` (`Config.lean:43`, `det`),
`dot n z = n.1*z.1 + n.2*z.2` (`LatticeEdges.lean:72`, `dot`).

Anchor and `J` (cw orientation, so the tag is `0 < det J ℓ`, NOT `0 < det ℓ J`):

    ℓ := (0,1)      J := (1,-1)      det J ℓ = 1*1 - (-1)*0 = 1 > 0   ✓

Fan neighbour of `J` **on the `ℓ` side** — i.e. inside `Arc J ℓ = {ν : 0 < det J ν ∧ 0 < det ν ℓ}`.
With `det J ν = ν.1 + ν.2` and `det ν ℓ = ν.1`, the only member of `E` is `ν = (1,0)`:

    nprevJ := (1,0)   det J nprevJ = 1*0 - (-1)*1 = 1 > 0             ✓
    Arc J nprevJ = ∅  (needs ν.2 < 0 and ν.1 + ν.2 > 0; no such ν ∈ E)  ✓
    vJ1 := -dir nprevJ = -(0,1) = (0,-1)
    dot (-J) vJ1 = dot (-1,1) (0,-1) = 0 + (-1) = -1 < 0              ✓ ← the sign that matters

  Sanity on the sign recipe: `dot (-J) (-dir n) = dot J (dir n) = det n J = -det J n`, so
  `0 < det J n` is EXACTLY what makes `-dir n` a legal `vJ1`.  (This is the cw branch: taking
  `vJ1 := +dir nprevJ` here would give `+1 > 0` and be WRONG.  The ccw branch has the opposite
  convention — `exists_nprevJ_vJ1` uses `vJ1 := dir nprevJ` off `0 < det nprevJ J`.)

Fan neighbour of `J` **on the far side from `ℓ`** — inside `Arc (-ℓ) J`.  With `-ℓ = (0,-1)`,
`det (-ℓ) ν = ν.1` and `det ν J = -ν.1 - ν.2`, no `ν ∈ E` qualifies, so the neighbour is `-ℓ`
itself:

    nnextJ := -ℓ = (0,-1)   det nnextJ J = 0*(-1) - (-1)*1 = 1 > 0    ✓
    Arc nnextJ J = ∅                                                  ✓
    wJ := dir nnextJ = (1,0)
    dot (-J) wJ = dot (-1,1) (1,0) = -1 + 0 = -1 < 0                  ✓ ← the sign that matters

  Here the recipe is the *other* one: `dot (-J) (dir n) = -dot (dir n) J = -det n J`, so
  `0 < det n J` is what makes `+dir n` legal.  The two neighbours of `J` therefore take
  OPPOSITE sign conventions; getting this backwards is the failure mode the task warned about.

Consistency of the whole cw chain on `Hex` (all three faces computed by hand):

    face Hex J      = {(0,-2), (1,-1), (2,0)},  dir J = (1,1),
                      faceStart = (0,-2), faceLen = 2, faceEnd = (0,-2) + 2•(1,1) = (2,0)
    face Hex nprevJ = {(2,0), (2,1), (2,2)},    dir nprevJ = (0,1),
                      faceStart = (2,0), faceLen = 2
    face Hex ℓ      = {(0,2), (1,2), (2,2)},    dir ℓ = (-1,0),
                      faceStart = (2,2)

  * `g_J := faceEnd Hex J = (2,0)` — this is `exists_gJ_pinned_cw`'s output shape (the face
    *end*, not the start; that is why this file's conclusion is stated as `g_J ∈ face _ J`,
    which both endpoints satisfy, making the cw and ccw branches interchangeable downstream).
  * `faceStart Hex nprevJ = (2,0) = g_J` — `hsupp_prev_cw`'s shared-vertex pinning.
  * `faceEnd Hex nnextJ = (-2,-2) + 2•(1,0) = (0,-2) = faceStart Hex J` — the other endpoint.
  * `g₁ := faceStart Hex ℓ = (2,2)`, and the `chain_cw_final` identity
    `g₁ - g_J = ∑_{ν ∈ Arc J ℓ} faceLen ν • dir ν` reads `(2,2) - (2,0) = 2 • (0,1) = (0,2)`. ✓

## §2. What the theorem is assembled from (every ingredient already 0-sorry in `Nivat/`)

* `Nivat.LeafAJSelect.exists_J_stable_cw` (`LeafAJSelect.lean:281`) — consumes `hunb` verbatim.
* `Nivat.LeafAJSelect.ne_and_ne_neg_of_det_pos_cw` (`LeafAJSelect.lean:349`) — the cw instance
  of the `J ≠ ℓ ∧ J ≠ -ℓ` pair already exists; no mirror had to be written.
* `Nivat.LeafAJSelect.exists_nprevJ_vJ1_cw` (`LeafAJSelect.lean:971`) — gives `vJ1` with
  `dot (-J) vJ1 < 0` directly off `0 < det J ℓ`.  (`LeafAShellNNext.exists_w_hsweepW` is NOT
  reusable here: it needs `0 < det ℓ J`, the ccw tag.)
* `Nivat.LeafAJSelect.exists_nprevJ_vJ1` (`LeafAJSelect.lean:833`) instantiated at `ℓ := -ℓ` —
  gives `wJ`, using `0 < det (-ℓ) J = det J ℓ`.
* `Nivat.LeafAJSelect.exists_gJ_pinned_cw` (`LeafAJSelect.lean:546`) — consumes `hg₁` in the
  `faceStart _ ℓ = g₁` shape and returns the pinned face *end*.
* `Nivat.PolyChain.faceEnd_mem` (`PolyChain.lean:234`) — converts the pinned face end into
  `g_J ∈ face (Ahat (σ i)) J`.
* `Nivat.AhatEnv.E_eq_of_enveloped` — transports `J ∈ E ↑Sphi` to `J ∈ E (Ahat (σ i))`.

**Note on the requested signature.** The task sheet wrote `Nivat.LE2.det`; no such name exists
(`det` is `Nivat.det`, `Config.lean:43`; only `dot`/`dir`/`E`/`face` live in `Nivat.LE2`).
The statement below uses the real names, which is what `LeafAAssemble.lean` itself uses.

## §3. `hswept` in the cw branch (round 2, answering lane-chaindata-lead)

`Nivat.LaneCdSwept.sweptClosed_of_pinned_ccw` (`LeafASwept.lean:99`) **cannot** be used
verbatim in the cw branch.  Eight of its nine binders survive; two do not, and both failures
have the same root cause:

* `hnprevdet : 0 < det nprevJ J` — the cw fan neighbour at the pinned vertex carries the
  OPPOSITE tag `0 < det J nprevJ` (`exists_fan_pred_cw`).  It is used only to derive
  `dot nprevJ (dir J) < 0`; in cw one gets `dot nprevJ (dir J) = det J nprevJ > 0` instead.
* `hgrow : ∀ N, ∃ i, ∀ t ≤ N, g_J + t • dir J ∈ Ahat i` — cw pins the face *end*, so the only
  available growth statement is `LeafAJSelect.hgrow_of_pinned_cw` (`LeafAJSelect.lean:693`,
  already landed 0-sorry — lane-chaindata-lead's message asked me to prove this mirror, but it
  exists), whose conclusion walks *backwards*: `g_J - t • dir J ∈ Ahat (σ i)`.

Both are the same statement: in cw the ray out of `g_J` along `J`'s face points along
`-dir J`, not `+dir J`.  Crucially this is **not** repairable by instantiation:
`sweptClosed_of_pinned_ccw`'s `J` is pinned to `-nJ` by `hnJ`, so `dir J` cannot be replaced,
and there is no other admissible `g_J` — in the cw tower `faceStart (Ahat (σ i)) J` is the
*moving* endpoint, receding along `-dir J`, so no fixed base point emits a `+dir J` ray that
stays in the tower for all `N`.

So the cw branch genuinely owes a mirror.  Rather than duplicate the ccw proof, §3 below
proves `sweptClosed_of_pinned_ray`, which is `sweptClosed_of_pinned_ccw`'s argument with the
ray direction abstracted to a bare `e` (the original uses `J` only through the four facts
`dir J ≠ 0`, `dot nJ (dir J) = 0`, `dot nprevJ (dir J) < 0`, and `hgrow`'s `dir J`), and then
derives `sweptClosed_of_pinned_cw` from it at `e := -dir J`.  The generalisation also subsumes
`sweptClosed_of_pinned_ccw` itself (`e := dir J`), so the integrator may collapse
`LeafASwept.lean`'s theorem to a corollary if desired.

The other seven binders do survive the cw data unchanged, and are all supplied by the widened
package in §2: `hJne0` (`J ≠ 0`), `hnJ`/`hcJ` (caller's definitions), `hsweep`
(`dot (-J) vJ1 < 0`), `hdotnprevvJ1 : dot nprevJ vJ1 = 0` — which is indeed sign-blind, as
lane-chaindata-lead predicted: `dot n (-dir n) = -dot n (dir n) = 0` (`dot_dir`,
`LatticeEdges.lean:250`) — and `hsupp_prev` from `LeafAJSelect.hsupp_prev_cw`
(`LeafAJSelect.lean:1002`), whose own binders `0 < det J nprevJ`, `Arc J nprevJ = ∅` and the
*equation* form of the pinning are exactly the three items the widening adds.

Does NOT import `RegionSteps`/`ColleRegion`/`Case2WindowProbe`/`NfpLPreamble` (red line).
-/
import Nivat.External.Colle.LeafAJSelect
import Nivat.External.Colle.LeafASwept

set_option autoImplicit false

namespace Nivat.LaneCdCw

open Nivat Nivat.LE2 Nivat.PolyChain Nivat.PolyChainSum

/-! ### §1. The worked numeric wedge of §0, Lean-checked

Every `det`/`dot` value quoted in the module docstring, plus the two fan-adjacency
(`Arc … = ∅`) checks, `decide`d on the hexagon's six edge normals.  `Hex` itself is recorded
so the reader can re-derive the faces; the face computations are prose (they need `suppVal`,
which is not decidable), but the *signs* — the failure mode — are all machine-checked here. -/

namespace CwWedge

/-- The hexagon `-2 ≤ x, y, x-y ≤ 2`, lattice-convex, with six edge normals. -/
def Hex : Set (ℤ × ℤ) :=
  {z : ℤ × ℤ | -2 ≤ z.1 ∧ z.1 ≤ 2 ∧ -2 ≤ z.2 ∧ z.2 ≤ 2 ∧ -2 ≤ z.1 - z.2 ∧ z.1 - z.2 ≤ 2}

/-- `Hex`'s edge normals, one per binding inequality. -/
def Efan : Finset (ℤ × ℤ) := {(1, 0), (0, 1), (-1, 1), (-1, 0), (0, -1), (1, -1)}

/-- The anchor; instantiated as `-nℓ` at the call site. -/
def lw : ℤ × ℤ := (0, 1)

/-- The unbounded-face normal, on the **cw** side of `lw` (`0 < det Jw lw`). -/
def Jw : ℤ × ℤ := (1, -1)

/-- Fan neighbour of `Jw` on the `lw` side (`Arc Jw lw`). -/
def nprevw : ℤ × ℤ := (1, 0)

/-- `vJ1 := -dir nprevw`.  The sign is forced by `0 < det Jw nprevw`. -/
def vJ1w : ℤ × ℤ := (0, -1)

/-- Fan neighbour of `Jw` on the far side from `lw` (`Arc (-lw) Jw`); here it is `-lw`. -/
def nnextw : ℤ × ℤ := (0, -1)

/-- `wJ := dir nnextw`.  The **opposite** sign convention from `vJ1w`, forced by
`0 < det nnextw Jw`. -/
def wJw : ℤ × ℤ := (1, 0)

/-- Membership check: the six normals are exactly `Efan`, and `-lw = nnextw`. -/
theorem neg_lw : -lw = nnextw := by decide

/-- The cw orientation tag, and both fan-adjacency determinants. -/
theorem det_signs :
    0 < det Jw lw ∧ 0 < det Jw nprevw ∧ 0 < det nnextw Jw ∧ 0 < det (-lw) Jw := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- The two direction assignments, with their opposite signs. -/
theorem dir_assignments : vJ1w = -dir nprevw ∧ wJw = dir nnextw := by
  refine ⟨by decide, by decide⟩

/-- **The two sign conditions that `ofPartsExhaustsInter`'s `hsweep`/`hsweepW` binders
literally are** (`dot nJ vJ1 < 0` with `nJ = -J`), on the worked instance. -/
theorem sweep_signs : dot (-Jw) vJ1w = -1 ∧ dot (-Jw) wJw = -1 := by
  refine ⟨by decide, by decide⟩

/-- `Arc Jw nprevw = ∅`: no edge normal of `Hex` lies strictly between `Jw` and `nprevw`,
so `nprevw` really is fan-adjacent to `Jw`. -/
theorem arc_J_nprev_empty : ∀ ν ∈ Efan, ¬ (0 < det Jw ν ∧ 0 < det ν nprevw) := by decide

/-- `Arc nnextw Jw = ∅`: the mirror adjacency on the far side. -/
theorem arc_nnext_J_empty : ∀ ν ∈ Efan, ¬ (0 < det nnextw ν ∧ 0 < det ν Jw) := by decide

/-- `nprevw` really does sit in `Arc Jw lw` (so it is the neighbour *towards* `lw`, not away
from it), and `nnextw` sits on the far side. -/
theorem neighbours_on_correct_sides :
    (0 < det Jw nprevw ∧ 0 < det nprevw lw) ∧ 0 < det nnextw Jw := by
  refine ⟨⟨by decide, by decide⟩, by decide⟩

/-- Had we copied the ccw convention `vJ1 := +dir nprevw`, the sweep sign would come out
**positive**, i.e. wrong.  Recorded as a kernel-checked guard against the sign slip. -/
theorem wrong_sign_guard : 0 < dot (-Jw) (dir nprevw) := by decide

#print axioms neg_lw
#print axioms det_signs
#print axioms dir_assignments
#print axioms sweep_signs
#print axioms arc_J_nprev_empty
#print axioms arc_nnext_J_empty
#print axioms neighbours_on_correct_sides
#print axioms wrong_sign_guard

end CwWedge

/-! ### §2. The cw package -/

/-- **The `dir (-nℓ) = -vl` (clockwise) branch's `J`-package.**

`ℓ` is instantiated by the caller as `-nℓ`.  In this orientation `anchorPoint` is the ccw
*start* of the `ℓ`-row, so the pinning hypothesis is `hg₁ : ∀ i, faceStart (Ahat i) ℓ = g₁`
(`LeafAWire.anchor_is_faceStart`'s output shape), and the unbounded face sits on the cw side
of `ℓ`, i.e. the tag is `0 < det J ℓ` (mirror of the ccw branch's `0 < det ℓ J`).

The `g_J` pinning is reported in **both** shapes: the equation
`faceStart (Ahat (σ i)) J + faceLen (Ahat (σ i)) J • dir J = g_J` (the face *end*, what
`exists_gJ_pinned_cw` actually produces, and what `hsupp_prev_cw` / `hgrow_of_pinned_cw`
consume) and the membership `g_J ∈ face (Ahat (σ i)) J` (what the half-plane step wants, and
the shape in which the cw and ccw branches become interchangeable, since `exists_gJ_pinned_ccw`
pins the face *start* and both endpoints lie in `face _ J`).

Both fan neighbours of `J` are exported with their adjacency tags.  **They use opposite sign
conventions** — `vJ1 = -(dir nprevJ)` off `0 < det J nprevJ`, but `wJ = dir nnextJ` off
`0 < det nnextJ J` — see §0 for the worked instance and §1 for the machine-checked signs.

Paper: `delivery/scratch/b3_colle2.txt:498` (choice of `J`: smallest index with unboundedly
growing edge, all strictly-earlier edges stabilising — here "earlier" is measured cw, i.e.
along `Arc J ℓ`), `:506` (`Â_∞` is an `(ℓ, ℓ_J)`-region), `:440` (`v_{ℓ_{J-1}}`, realised as
`vJ1`, the fan neighbour direction towards `ℓ`). -/
theorem exists_J_package_cw
    {Sphi : Finset (ℤ × ℤ)} {Ahat : ℕ → Set (ℤ × ℤ)} {ℓ g₁ : ℤ × ℤ}
    (hfin : ∀ i, (Ahat i).Finite)
    (hne : ∀ i, (Ahat i).Nonempty)
    (hlc : ∀ i, IsLatticeConvexRegion (Ahat i))
    (henv : ∀ i, Enveloped (↑Sphi : Set (ℤ × ℤ)) (Ahat i))
    (hSfin : (Nivat.LE2.E (↑Sphi : Set (ℤ × ℤ))).Finite)
    (hSarea : PosArea (↑Sphi : Set (ℤ × ℤ)))
    (AhatMono : ∀ i j, i ≤ j → Ahat i ⊆ Ahat j)
    (hSymm : ∀ μ ∈ Nivat.LE2.E (↑Sphi : Set (ℤ × ℤ)),
      -μ ∈ Nivat.LE2.E (↑Sphi : Set (ℤ × ℤ)))
    (hℓE : ℓ ∈ Nivat.LE2.E (↑Sphi : Set (ℤ × ℤ)))
    (hnegℓE : (-ℓ) ∈ Nivat.LE2.E (↑Sphi : Set (ℤ × ℤ)))
    -- the cw pinning of the ℓ-face (`anchor_is_faceStart`'s output shape)
    (hg₁ : ∀ i, Nivat.PolyChain.faceStart (Ahat i) ℓ = g₁)
    -- the cw-side unbounded face (first conjunct of `exists_edge_unbounded_both`)
    (hunb : ∃ ν ∈ Nivat.LE2.E (↑Sphi : Set (ℤ × ℤ)), 0 < det ν ℓ ∧
      ¬ ∃ L : ℕ, ∀ i, Nivat.PolyChain.faceLen (Ahat i) ν ≤ L) :
    ∃ J ∈ Nivat.LE2.E (↑Sphi : Set (ℤ × ℤ)),
      ∃ (nprevJ nnextJ vJ1 wJ g_J : ℤ × ℤ) (σ : ℕ → ℕ) (i₀ : ℕ),
      StrictMono σ ∧
      0 < det J ℓ ∧
      J ≠ 0 ∧ J ≠ ℓ ∧ J ≠ -ℓ ∧
      (¬ ∃ L : ℕ, ∀ i, Nivat.PolyChain.faceLen (Ahat i) J ≤ L) ∧
      -- fan neighbour of `J` towards `ℓ`, inside `Arc J ℓ`; carries `vJ1`
      (nprevJ ∈ Nivat.LE2.E (↑Sphi : Set (ℤ × ℤ)) ∧
        0 < det J nprevJ ∧
        Nivat.PolyChainSum.Arc (Sphi.finite_toSet) J nprevJ = ∅ ∧
        vJ1 = -(Nivat.LE2.dir nprevJ) ∧
        Nivat.LE2.dot nprevJ vJ1 = 0 ∧
        Nivat.LE2.dot (-J) vJ1 < 0) ∧
      -- fan neighbour of `J` away from `ℓ`, inside `Arc (-ℓ) J`; carries `wJ`
      (nnextJ ∈ Nivat.LE2.E (↑Sphi : Set (ℤ × ℤ)) ∧
        0 < det nnextJ J ∧
        Nivat.PolyChainSum.Arc (Sphi.finite_toSet) nnextJ J = ∅ ∧
        wJ = Nivat.LE2.dir nnextJ ∧
        Nivat.LE2.dot nnextJ wJ = 0 ∧
        Nivat.LE2.dot (-J) wJ < 0) ∧
      -- the pinned face END of `J`, in equation form …
      (∀ i, i₀ ≤ i → Nivat.PolyChain.faceStart (Ahat (σ i)) J
        + (Nivat.PolyChain.faceLen (Ahat (σ i)) J : ℤ) • Nivat.LE2.dir J = g_J) ∧
      -- … and in membership form
      (∀ i, i₀ ≤ i → g_J ∈ Nivat.LE2.face (Ahat (σ i)) J) := by
  classical
  -- `J`, the cw-minimal unbounded edge (`:498`).
  obtain ⟨J, hJE, hJℓ, hJunb, hArcbdd⟩ :=
    Nivat.LeafAJSelect.exists_J_stable_cw (A := Ahat) (ℓ := ℓ) hunb
  -- `J ≠ ±ℓ`, already available in the cw orientation.
  obtain ⟨hJne1, hJne2⟩ := Nivat.LeafAJSelect.ne_and_ne_neg_of_det_pos_cw hJℓ
  have hJne0 : J ≠ 0 := hJE.1.ne_zero
  -- `vJ1`: fan neighbour of `J` towards `ℓ` (inside `Arc J ℓ`), with `vJ1 := -dir nprevJ`.
  -- `dot (-J) (-dir n) = dot J (dir n) = det n J = -det J n < 0` since `0 < det J nprevJ`.
  obtain ⟨nprevJ, vJ1, hnprevE, hnprevdet, hnprevempty, -, hvJ1eq, hdotnprevvJ1, hsweep⟩ :=
    Nivat.LeafAJSelect.exists_nprevJ_vJ1_cw (Sphi := Sphi) hℓE hJE hJℓ
  -- `wJ`: fan neighbour of `J` on the far side from `ℓ` (inside `Arc (-ℓ) J`), with
  -- `wJ := dir nnextJ`.  Legal second endpoint: `det (-ℓ) J = -det ℓ J = det J ℓ > 0`.
  have hnegℓJ : 0 < det (-ℓ) J := by
    have h1 : det (-ℓ) J = -det ℓ J := det_neg_left ℓ J
    have h2 : det ℓ J = -det J ℓ := det_skew ℓ J
    omega
  obtain ⟨nnextJ, wJ, hnnextE, hnnextdet, hnnextempty, -, hwJeq, hdotnnextwJ, hsweepW⟩ :=
    Nivat.LeafAJSelect.exists_nprevJ_vJ1 (Sphi := Sphi) hnegℓE hJE hnegℓJ
  -- `g_J`, the pinned *end* of `J`'s face along a stabilising subsequence (`:506`).
  obtain ⟨g_J, σ, hσmono, i₀, hgJ⟩ :=
    Nivat.LeafAJSelect.exists_gJ_pinned_cw (Ahat := Ahat) hfin hlc henv hSfin hSarea
      hℓE hJE hJℓ hg₁ hArcbdd
  refine ⟨J, hJE, nprevJ, nnextJ, vJ1, wJ, g_J, σ, i₀, hσmono, hJℓ, hJne0, hJne1, hJne2,
    hJunb,
    ⟨hnprevE, hnprevdet, hnprevempty, hvJ1eq, hdotnprevvJ1, hsweep⟩,
    ⟨hnnextE, hnnextdet, hnnextempty, hwJeq, hdotnnextwJ, hsweepW⟩,
    hgJ, fun i hi => ?_⟩
  -- Face end ⟹ membership: `faceEnd_mem` (`PolyChain.lean:234`), after transporting
  -- `J ∈ E ↑Sphi` to `J ∈ E (Ahat (σ i))`.
  have hJEi : J ∈ Nivat.LE2.E (Ahat (σ i)) := by
    rw [Nivat.AhatEnv.E_eq_of_enveloped hSfin hSarea (henv (σ i))]; exact hJE
  exact hgJ i hi ▸ Nivat.PolyChain.faceEnd_mem (hlc (σ i)) (hfin (σ i)) hJEi

/-! ### §3. `hswept` for the cw branch

`sweptClosed_of_pinned_ray` is `LaneCdSwept.sweptClosed_of_pinned_ccw`'s proof
(`LeafASwept.lean:99`) with the ray direction abstracted from `dir J` to a bare `e`; that
theorem uses `J` only through `dir J ≠ 0`, `dot nJ (dir J) = 0`, `dot nprevJ (dir J) < 0`
(which it derives from `hnprevdet`) and `hgrow`, all of which become binders here.
`sweptClosed_of_pinned_cw` then instantiates `e := -dir J`, which is the direction in which
`J`'s face actually grows out of the pinned vertex in the cw orientation.

Paper anchor unchanged from `LeafASwept.lean`: `delivery/scratch/b3_colle2.txt:800-806`
(`𝓡_i := {g + t·v⃗_{ℓ_i} : g ∈ 𝓡_{i+1}, t ∈ ℤ₊}`, the sweep defining the region chain). -/

section Swept

open Nivat.MaxEnv

/-- **`SweptClosed` with the face ray direction abstracted.**  Generalises
`Nivat.LaneCdSwept.sweptClosed_of_pinned_ccw` (`LeafASwept.lean:99`): take `e := dir J` and the
three `e`-binders are exactly the facts that proof derives from `hJne0` / `hnJ` / `hnprevdet`.
The cw branch needs `e := -dir J`, which is why the abstraction is made. -/
theorem sweptClosed_of_pinned_ray
    {Ahat : ℕ → Set (ℤ × ℤ)} {nprevJ g_J vJ1 nJ e : ℤ × ℤ} {cJ : ℤ}
    (hnJne : nJ ≠ 0)
    (hene : e ≠ 0)
    (hcJ : cJ = dot nJ g_J)
    (hsweep : dot nJ vJ1 < 0)
    (hdotnJe : dot nJ e = 0)
    (hdotnpreve : dot nprevJ e < 0)
    (hdotnprevvJ1 : dot nprevJ vJ1 = 0)
    (hgrow : ∀ N : ℕ, ∃ i, ∀ t : ℕ, t ≤ N → g_J + (t : ℤ) • e ∈ Ahat i)
    (hsupp_prev : ∀ i, ∀ z ∈ Ahat i, dot nprevJ z ≤ dot nprevJ g_J)
    (hTconv : IsLatticeConvexRegion (⋃ i, Ahat i)) :
    SweptClosed (⋃ i, Ahat i) vJ1 nJ cJ := by
  classical
  have ip_toReal : ∀ n z : ℤ × ℤ, Nivat.Colle35.ip n (toReal z) = (dot n z : ℝ) := by
    intro n z; unfold Nivat.Colle35.ip; exact dot_cast_toReal n z
  have ip_sub : ∀ (n : ℤ × ℤ) (a b : ℝ × ℝ),
      Nivat.Colle35.ip n (a - b) = Nivat.Colle35.ip n a - Nivat.Colle35.ip n b := by
    intro n a b; simp only [Nivat.Colle35.ip, Prod.fst_sub, Prod.snd_sub]; ring
  set T : Set (ℤ × ℤ) := ⋃ i, Ahat i with hT
  set Cset : Set (ℝ × ℝ) := convHullOf T with hCset
  have hTeq : T = toReal ⁻¹' Cset := by rw [hCset]; exact eq_preimage_convHullOf hTconv
  unfold SweptClosed
  intro g hgT t ht
  obtain ⟨i1, hgi1⟩ := Set.mem_iUnion.mp hgT
  rcases Nat.eq_zero_or_pos t with rfl | htpos
  · simpa using hgT
  set m : ℝ := (dot nJ vJ1 : ℝ) with hm
  have hmneg : m < 0 := by rw [hm]; exact_mod_cast hsweep
  have hmne : m ≠ 0 := ne_of_lt hmneg
  set s : ℝ := ((cJ : ℝ) - (dot nJ g : ℝ)) / m with hs_def
  have hsm : s * m = (cJ : ℝ) - (dot nJ g : ℝ) := (eq_div_iff hmne).mp hs_def
  have hcast : (cJ : ℝ) - (dot nJ g : ℝ) ≤ (t : ℝ) * m := by
    have hint : (cJ : ℤ) ≤ dot nJ (g + (t : ℤ) • vJ1) := ht
    have hexp : dot nJ (g + (t : ℤ) • vJ1) = dot nJ g + t * dot nJ vJ1 := by
      rw [dot_add, dot_comm nJ ((t : ℤ) • vJ1), dot_smul, dot_comm vJ1 nJ]
    rw [hexp] at hint
    have : (cJ : ℝ) ≤ (dot nJ g : ℝ) + (t : ℝ) * (dot nJ vJ1 : ℝ) := by exact_mod_cast hint
    linarith
  have hts : (t : ℝ) ≤ s := by
    by_contra hcon
    push_neg at hcon
    have hflip : t * m < s * m := by
      nlinarith [mul_pos (sub_pos.mpr hcon) (neg_pos.mpr hmneg)]
    rw [hsm] at hflip
    linarith
  have htpos' : (0 : ℝ) < (t : ℝ) := by exact_mod_cast htpos
  have hspos : (0 : ℝ) < s := lt_of_lt_of_le htpos' hts
  set G : ℝ × ℝ := toReal g with hG
  set W : ℝ × ℝ := toReal vJ1 with hW
  set Q0 : ℝ × ℝ := toReal g_J with hQ0
  set q : ℝ × ℝ := G + s • W with hq_def
  have hip_nJ_q_sub_Q0 : Nivat.Colle35.ip nJ (q - Q0) = 0 := by
    have hipG : Nivat.Colle35.ip nJ G = (dot nJ g : ℝ) := by rw [hG]; exact ip_toReal nJ g
    have hipW : Nivat.Colle35.ip nJ W = m := by rw [hW]; exact ip_toReal nJ vJ1
    have hipQ0 : Nivat.Colle35.ip nJ Q0 = (dot nJ g_J : ℝ) := by rw [hQ0]; exact ip_toReal nJ g_J
    have hipq : Nivat.Colle35.ip nJ q = (cJ : ℝ) := by
      rw [hq_def, Nivat.Colle35.ip_add, Nivat.Colle35.ip_smul, hipG, hipW]
      linarith [hsm]
    rw [ip_sub, hipq, hipQ0, hcJ]; ring
  obtain ⟨c, hc⟩ :=
    Nivat.SweepCrit.exists_smul_of_ip_zero hnJne hene hdotnJe hip_nJ_q_sub_Q0
  have hqQ0 : q = Q0 + c • toReal e := by rw [← hc]; module
  have hc_nonneg : 0 ≤ c := by
    have hipnp_G : Nivat.Colle35.ip nprevJ G = (dot nprevJ g : ℝ) := by
      rw [hG]; exact ip_toReal nprevJ g
    have hipnp_W : Nivat.Colle35.ip nprevJ W = 0 := by
      rw [hW, ip_toReal nprevJ vJ1, hdotnprevvJ1]; norm_num
    have hipnp_Q0 : Nivat.Colle35.ip nprevJ Q0 = (dot nprevJ g_J : ℝ) := by
      rw [hQ0]; exact ip_toReal nprevJ g_J
    have hipnp_q : Nivat.Colle35.ip nprevJ q = (dot nprevJ g : ℝ) := by
      rw [hq_def, Nivat.Colle35.ip_add, Nivat.Colle35.ip_smul, hipnp_G, hipnp_W]; ring
    have hle : (dot nprevJ g : ℝ) ≤ (dot nprevJ g_J : ℝ) := by
      exact_mod_cast hsupp_prev i1 g hgi1
    have hipnp_e : Nivat.Colle35.ip nprevJ (toReal e) = (dot nprevJ e : ℝ) :=
      ip_toReal nprevJ e
    have hqsub_le : Nivat.Colle35.ip nprevJ (q - Q0) ≤ 0 := by
      rw [ip_sub, hipnp_q, hipnp_Q0]; linarith
    have hqsub_eq : Nivat.Colle35.ip nprevJ (q - Q0) = c * (dot nprevJ e : ℝ) := by
      rw [hqQ0]
      have : Nivat.Colle35.ip nprevJ (Q0 + c • toReal e - Q0)
          = Nivat.Colle35.ip nprevJ (c • toReal e) := by
        congr 1; abel
      rw [this, Nivat.Colle35.ip_smul, hipnp_e]
    have hxneg : (dot nprevJ e : ℝ) < 0 := by exact_mod_cast hdotnpreve
    by_contra hcneg
    push_neg at hcneg
    have hpos : 0 < c * (dot nprevJ e : ℝ) := mul_pos_of_neg_of_neg hcneg hxneg
    rw [← hqsub_eq] at hpos
    linarith [hqsub_le]
  set k0 : ℕ := ⌈c⌉₊ with hk0
  have hck0 : c ≤ (k0 : ℝ) := Nat.le_ceil c
  obtain ⟨i2, hi2⟩ := hgrow k0
  have hQ0mem : g_J ∈ Ahat i2 := by simpa using hi2 0 (Nat.zero_le k0)
  have hQk0mem : g_J + (k0 : ℤ) • e ∈ Ahat i2 := hi2 k0 (le_refl k0)
  have hQ0T : g_J ∈ T := Set.mem_iUnion.mpr ⟨i2, hQ0mem⟩
  have hQk0T : g_J + (k0 : ℤ) • e ∈ T := Set.mem_iUnion.mpr ⟨i2, hQk0mem⟩
  have hQ0Cset : Q0 ∈ Cset := by rw [hQ0, hCset]; exact toReal_mem_convHullOf hQ0T
  have hQk0Cset' : toReal (g_J + (k0 : ℤ) • e) ∈ Cset := by
    rw [hCset]; exact toReal_mem_convHullOf hQk0T
  have hQk0eq : toReal (g_J + (k0 : ℤ) • e) = Q0 + (k0 : ℝ) • toReal e := by
    rw [hQ0]; exact Nivat.SweepCrit.toReal_add_nsmul g_J e k0
  have hQk0Cset : Q0 + (k0 : ℝ) • toReal e ∈ Cset := hQk0eq ▸ hQk0Cset'
  have hCconv : Convex ℝ Cset := by rw [hCset]; exact Nivat.LE2.convex_convHullOf T
  have hqCset : q ∈ Cset := by
    rcases Nat.eq_zero_or_pos k0 with hk00 | hk0pos
    · have hc0 : c = 0 := by
        have : c ≤ (0 : ℝ) := by rw [hk00] at hck0; exact_mod_cast hck0
        linarith
      have hqeq : q = Q0 := by rw [hqQ0, hc0]; module
      rw [hqeq]; exact hQ0Cset
    · have hk0pos' : (0 : ℝ) < (k0 : ℝ) := by exact_mod_cast hk0pos
      set lam : ℝ := c / (k0 : ℝ) with hlam
      have hlam0 : 0 ≤ lam := div_nonneg hc_nonneg hk0pos'.le
      have hlam1 : lam ≤ 1 := by rw [hlam, div_le_one hk0pos']; exact hck0
      have hsum : (1 - lam) + lam = 1 := by ring
      have hmem := hCconv hQ0Cset hQk0Cset (by linarith : (0:ℝ) ≤ 1 - lam) hlam0 hsum
      have hlamk0 : lam * (k0 : ℝ) = c := by rw [hlam]; field_simp
      have heq : (1 - lam) • Q0 + lam • (Q0 + (k0 : ℝ) • toReal e) = q := by
        rw [hqQ0, ← hlamk0]; module
      rwa [heq] at hmem
  rw [hTeq]
  show toReal (g + (t : ℤ) • vJ1) ∈ Cset
  have hGCset : G ∈ Cset := by rw [hG, hCset]; exact toReal_mem_convHullOf hgT
  set lam2 : ℝ := (t : ℝ) / s with hlam2
  have hlam2_0 : 0 ≤ lam2 := div_nonneg htpos'.le hspos.le
  have hlam2_1 : lam2 ≤ 1 := by rw [hlam2, div_le_one hspos]; exact hts
  have hsum2 : (1 - lam2) + lam2 = 1 := by ring
  have hmem2 := hCconv hGCset hqCset (by linarith : (0:ℝ) ≤ 1 - lam2) hlam2_0 hsum2
  have hlam2s : lam2 * s = (t : ℝ) := by rw [hlam2]; field_simp
  have heq2 : (1 - lam2) • G + lam2 • q = toReal (g + (t : ℤ) • vJ1) := by
    rw [hq_def, Nivat.SweepCrit.toReal_add_nsmul, ← hG, ← hW, ← hlam2s]
    module
  rwa [heq2] at hmem2

/-- **`hswept` for the clockwise branch.**  Mirror of
`Nivat.LaneCdSwept.sweptClosed_of_pinned_ccw` (`LeafASwept.lean:99`): the two binders that do
not survive the cw orientation are flipped — `hnprevdet` becomes `0 < det J nprevJ`
(`exists_fan_pred_cw`'s tag) and `hgrow` walks backwards along `-dir J`
(`LeafAJSelect.hgrow_of_pinned_cw`'s conclusion, `LeafAJSelect.lean:693`).  Everything else is
unchanged.  Supply `hsupp_prev` from `LeafAJSelect.hsupp_prev_cw` (`LeafAJSelect.lean:1002`). -/
theorem sweptClosed_of_pinned_cw
    {Ahat : ℕ → Set (ℤ × ℤ)} {J nprevJ g_J vJ1 nJ : ℤ × ℤ} {cJ : ℤ}
    (hJne0 : J ≠ 0)
    (hnJ : nJ = -J)
    (hcJ : cJ = dot nJ g_J)
    (hsweep : dot nJ vJ1 < 0)
    (hnprevdet : 0 < det J nprevJ)
    (hdotnprevvJ1 : dot nprevJ vJ1 = 0)
    (hgrow : ∀ N : ℕ, ∃ i, ∀ t : ℕ, t ≤ N → g_J - (t : ℤ) • dir J ∈ Ahat i)
    (hsupp_prev : ∀ i, ∀ z ∈ Ahat i, dot nprevJ z ≤ dot nprevJ g_J)
    (hTconv : IsLatticeConvexRegion (⋃ i, Ahat i)) :
    SweptClosed (⋃ i, Ahat i) vJ1 nJ cJ := by
  have hnJne : nJ ≠ 0 := by rw [hnJ]; simpa using hJne0
  have hdirJne : dir J ≠ ((0 : ℤ), (0 : ℤ)) := by
    intro h
    apply hJne0
    have h1 : J.1 = 0 := by have := congrArg Prod.snd h; simpa [dir] using this
    have h2 : J.2 = 0 := by have := congrArg Prod.fst h; simpa [dir] using this
    exact Prod.ext h1 h2
  have hene : (-(dir J)) ≠ 0 := by
    simpa using (neg_ne_zero (a := dir J)).mpr hdirJne
  -- `dot nJ (-dir J) = -dot nJ (dir J) = 0`.
  have hdotnJdirJ : dot nJ (dir J) = 0 := by rw [hnJ, dot_neg_left]; simp [dot_dir]
  have hdotnJe : dot nJ (-(dir J)) = 0 := by
    rw [dot_comm nJ (-(dir J)), dot_neg_left, dot_comm, hdotnJdirJ, neg_zero]
  -- `dot nprevJ (-dir J) = -dot nprevJ (dir J) = -det J nprevJ < 0`  ← the cw sign flip.
  have hdot_nprev_dirJ : dot nprevJ (dir J) = det J nprevJ := by
    rw [dot_comm nprevJ (dir J)]; exact Nivat.PolyChainSum.dot_dir_left J nprevJ
  have hdotnpreve : dot nprevJ (-(dir J)) < 0 := by
    rw [dot_comm nprevJ (-(dir J)), dot_neg_left, dot_comm, hdot_nprev_dirJ]
    omega
  have hgrow' : ∀ N : ℕ, ∃ i, ∀ t : ℕ, t ≤ N → g_J + (t : ℤ) • (-(dir J)) ∈ Ahat i := by
    intro N
    obtain ⟨i, hi⟩ := hgrow N
    refine ⟨i, fun t ht => ?_⟩
    have heq : g_J + (t : ℤ) • (-(dir J)) = g_J - (t : ℤ) • dir J := by
      rw [smul_neg]; abel
    rw [heq]; exact hi t ht
  exact sweptClosed_of_pinned_ray hnJne hene hcJ hsweep hdotnJe hdotnpreve hdotnprevvJ1
    hgrow' hsupp_prev hTconv

/-- Substantiates the claim in §3 that `sweptClosed_of_pinned_ray` subsumes the landed ccw
theorem: this re-derives `Nivat.LaneCdSwept.sweptClosed_of_pinned_ccw`'s exact statement
(`LeafASwept.lean:99`) from the abstracted one at `e := dir J`, in a dozen lines.  Kept so the
integrator can, if desired, collapse `LeafASwept.lean`'s 160-line proof into a corollary
instead of maintaining two copies of the same sweep argument. -/
theorem sweptClosed_of_pinned_ccw'
    {Ahat : ℕ → Set (ℤ × ℤ)} {J nprevJ g_J vJ1 nJ : ℤ × ℤ} {cJ : ℤ}
    (hJne0 : J ≠ 0)
    (hnJ : nJ = -J)
    (hcJ : cJ = dot nJ g_J)
    (hsweep : dot nJ vJ1 < 0)
    (hnprevdet : 0 < det nprevJ J)
    (hdotnprevvJ1 : dot nprevJ vJ1 = 0)
    (hgrow : ∀ N : ℕ, ∃ i, ∀ t : ℕ, t ≤ N → g_J + (t : ℤ) • dir J ∈ Ahat i)
    (hsupp_prev : ∀ i, ∀ z ∈ Ahat i, dot nprevJ z ≤ dot nprevJ g_J)
    (hTconv : IsLatticeConvexRegion (⋃ i, Ahat i)) :
    SweptClosed (⋃ i, Ahat i) vJ1 nJ cJ := by
  have hnJne : nJ ≠ 0 := by rw [hnJ]; simpa using hJne0
  have hene : dir J ≠ 0 := by
    intro h
    apply hJne0
    have h1 : J.1 = 0 := by have := congrArg Prod.snd h; simpa [dir] using this
    have h2 : J.2 = 0 := by have := congrArg Prod.fst h; simpa [dir] using this
    exact Prod.ext h1 h2
  have hdotnJe : dot nJ (dir J) = 0 := by rw [hnJ, dot_neg_left]; simp [dot_dir]
  have hdotnpreve : dot nprevJ (dir J) < 0 := by
    have h : dot nprevJ (dir J) = det J nprevJ := by
      rw [dot_comm nprevJ (dir J)]; exact Nivat.PolyChainSum.dot_dir_left J nprevJ
    have hskew : det J nprevJ = -det nprevJ J := Nivat.LE2.det_skew J nprevJ
    omega
  exact sweptClosed_of_pinned_ray hnJne hene hcJ hsweep hdotnJe hdotnpreve hdotnprevvJ1
    hgrow hsupp_prev hTconv

end Swept

end Nivat.LaneCdCw

#print axioms Nivat.LaneCdCw.exists_J_package_cw
#print axioms Nivat.LaneCdCw.sweptClosed_of_pinned_ray
#print axioms Nivat.LaneCdCw.sweptClosed_of_pinned_cw
#print axioms Nivat.LaneCdCw.sweptClosed_of_pinned_ccw'
