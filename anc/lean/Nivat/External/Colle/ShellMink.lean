/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.MinkowskiEdges
import Nivat.External.Colle.EnvelopedConvex
import Nivat.External.Colle.MaximalEnveloped
import Nivat.External.Colle.ANormal
import Nivat.External.Colle.Lemma35Wiring
import Nivat.External.Colle.Step_PeriodsRays2
import Nivat.External.Colle.GenClosureWeaken

/-!
# Fourth encoding of `ChainData.shellEnv`: **add a parallel Minkowski generator**

## §1. The mechanism (general, landed from `tmp/shellenv4_relax.lean`)

`shell := latHull (A + B)` for a finite nonempty generator set `B` with `E B ⊆ E A`.

This is **not** "relax one support constant `c_k` by `ε`" — that encoding dies: for the
`m = 3` hexagon below, relaxing only the support constant of the edge with normal `(1,0)`
(from `c = 2` to `c = 2 + ε`) makes the two adjacent edges (normals `(1,-1)` and `(0,1)`)
meet the relaxed line at exactly `ε = 1`, all three lines through `(3,2)`, and the relaxed
edge collapses to that single point — its face is no longer `Nontrivial`, so
`(1,0) ∉ E(shell)`.  Since `ChainData.shellProper` forces `0 < ε` with `ε : ℕ`, `ε = 1` is
the *least legal choice* and exactly the failure point.

**Adding a Minkowski generator is a different operation.**  `face_add`
(`MinkowskiEdges.lean:105`) gives `face (A + B) n = face A n + face B n`, and a sumset with a
nonempty second summand can only translate-or-grow, never shrink — the argument is uniform
over all edge directions at once.  Convexity is supplied by `latHull`
(`isLatticeConvexRegion_latHull` / `E_latHull` / `face_subset_face_latHull`,
`EnvelopedConvex.lean:171,260,185`, all unconditional), sidestepping whether `A + B` is
itself lattice-convex.

`enveloped_add_of_finite` — the general lemma; `enveloped_hexagon_shell`,
`subShell_hexagon`, `shellProper_hexagon` — a concrete `m = 3` instance.

## §2. `shellSubInf` with `B := segOf vJ1` — **refuted, and the reason is general**

The integrator's candidate was `B := segOf vJ1` (the sweep direction of `shellInf`).  It is
pinned by `ChainDataWithShell.shellInf_eq` (`ChainShell.lean:58-59`) against
`MaxEnv.shell (⋃ Ahat) vJ1 nJ cJ ε`, whose membership predicate
(`MaxEnv.mem_shell`, `MaximalEnveloped.lean:567`) filters **every swept point** by the layer
cut `cJ - ε ≤ dot nJ z`, not just the seed.  So the one-step sweep `g + vJ1` at a `g ∈ Ahat i`
attaining `cJ` needs `cJ - ε ≤ cJ + dot nJ vJ1`, i.e. `-ε ≤ dot nJ vJ1`.

`not_shellSubInf_of_dot_neg` proves, **for arbitrary `A vJ1 nJ cJ ε`**: if some `g ∈ A`
attains the level `cJ` and `dot nJ vJ1 < -ε`, then `latHull (A + segOf vJ1) ⊄
MaxEnv.shell A vJ1 nJ cJ ε` — the witness is `g + vJ1`.  In particular at `ε = 0` any
strictly negative `dot nJ vJ1` kills the candidate (`not_shellSubInf_zero_of_dot_neg`).
`dot nJ vJ1 < 0` is the generic convex-polygon situation (`nJ` is the inward normal of the
edge *after* the one with direction `vJ1`, so `vJ1` points *out* of `ℓ_J`'s half-plane), and
attainment of `cJ` on `Ahat i` is the generic reading of "`c_J` is the support value"; but
the theorem takes both as explicit hypotheses and does not derive them from `ChainData`.

The concrete unit-square instance from `tmp/Ashell_segOfvJ1_shellSubInf_dies.lean` is
re-landed here as `not_shellSubInf_sq_zero`, now as a two-line corollary of the general
statement.

## §2'. On the real bundle: the ε-independent candidate dies on **every** `ChainDataGeom`

`ChainDataGeom.exists_not_shellSubInf_segOf_vJ1_zero`: for every `cg : ChainDataGeom` there
is an `i` with `latHull (Ahat i + segOf vJ1) ⊄ shellInf 0`.  No attainment hypothesis: take
`g` minimising `dot nJ` over `⋃ Ahat` (`ahat_nonempty` + `ahat_halfPlane`), then
`g + vJ1 ∈ shellInf 0 ⊆ ⋃ Ahat` (`shellInfZero`) would sit strictly below `g`
(`ChainDataGeom.dot_nJ_vJ1_neg`, `ANormal.lean:747`).  So `shell i ε := latHull (Ahat i +
segOf vJ1)` **as an ε-independent definition is dead** — `shellSubInf` fails at `ε = 0`.

What this does **not** kill: the ε-dependent variant `shell i 0 := Ahat i`,
`shell i (ε+1) := latHull (Ahat i + segOf vJ1)`.

**ε is not free** (signature reading, `#check`ed 2026-09-19): `shellSubInf`, `subShell`,
`shellProper`, `shellSubStrip`, `shellFinite`, `fillZero`, `fillCover` all quantify
`∀ i ε` and tie `shell i ε` to `shellInf ε` at the **same** `ε`; only `shellEnv` has
`∃ ε i₀, 0 < ε ∧ …`.  So Collé's "appropriate ε fixed" lives in `shellEnv` alone; the
constructor must still supply `shell i ε ⊆ shellInf ε` for **every** `ε`, in particular
`ε = 1`, where `shellProper` forces a new point and the layer cut is `cJ - 1`.  Choosing a
large ε does not rescue anything.

For the ε-dependent variant the raw sum is inside `shellInf ε` exactly when
`-ε ≤ dot nJ vJ1` (`ChainDataWithShell.add_segOf_vJ1_subset_shellInf`), so at `ε = 1` it needs
`dot nJ vJ1 = -1` on the nose (`ChainDataGeom.not_shellSubInf_segOf_vJ1` kills `≤ -2` given
attainment).  `ChainDataWithShell.latHull_add_segOf_vJ1_subset_shellInf` then reduces the
whole of `shellSubInf` to **one** residual: `latHull (Ahat i + segOf vJ1) ⊆ reachSet (⋃ Ahat)
vJ1` — the layer cut survives `latHull` for free (it is a half-plane bound).  §4 shows that
residual is **false on raw parameters**: a lattice-convex `A` with `v` among its edge
directions whose hull escapes `reachSet A v`.  Whether it holds on the real bundle is
**open** (conjecture, not kernel fact: for an `(ℓ, ℓ_J)`-region with `ℓ_{J-1}` a genuine
edge of direction `vJ1`, chords parallel to `vJ1` should be at least as long as that edge by
concavity of the chord-length function on an unbounded convex region, which would make the
sweep of `⋃ Ahat` lattice-convex; but `ChainDataGeom` records **no** field saying `vJ1` is an
edge direction of `⋃ Ahat` or of `S`, so nothing in the bundle currently forces it).

Disagreement obligation (§3 of `LEAF-A.md`): the variant adds the points `g + vJ1`
(plus hull fill) outside `Ahat i`; the forced disagreement point lands on one of them.  This
is **compatible**, not a wall: the escape encoding died because `Env` failed on the enlarged
set, whereas here `Env` is delivered by `enveloped_add_of_finite` (once `E (segOf vJ1) ⊆ E S`
and `Env := EnvOf ↑S`), and the disagreement is then what `maximalHat` *produces* on any
strictly larger `Env` set in the strip, not an extra thing to construct.  ⚠ `shellSubStrip`
is a separate, unexamined constraint on the same points: `g + vJ1` must stay in
`{z | z + kk i • vl ∈ halfStrip (B i) vl}`, which depends on `B i` and is not settled here.

## §3. What is *not* claimed

* `enveloped_add_of_finite` does **not** by itself discharge `ChainData.shellEnv`: `Env` is an
  abstract field, and the lift `Enveloped ↑S (Ahat i) → Enveloped ↑S (latHull (Ahat i + B))`
  via `Enveloped.trans` (`LatticeEdges.lean:1668`) only applies once the constructor takes
  `Env := EnvOf ↑S`.
* No choice of `B` is shown to satisfy `shellSubInf`; §2 only kills `B := segOf vJ1`.
* `IsLatticeConvexRegion (A + B)` (without `latHull`) is neither proved nor used.
-/

set_option autoImplicit false

namespace Nivat.ShellMink

open Nivat Nivat.LE2 Nivat.LE2.Colle36Fit Pointwise

/-! ## §1. The general lemma: adding a parallel generator, via `latHull` -/

/-- **Adding a Minkowski generator whose edge directions are already present keeps the
envelope, unconditionally on convexity of the sum.**  `A`, `B` finite and nonempty,
`E B ⊆ E A`.  Then `Enveloped A (latHull (A + B))`.

The face-monotonicity clause is proved by exhibiting, for each `n`, an injection
`face A n ↪ face A n + face B n = face (A + B) n ⊆ face (latHull (A+B)) n`
via `a ↦ a + b` for a fixed maximiser `b ∈ face B n` (`face_nonempty`). -/
theorem enveloped_add_of_finite {A B : Set (ℤ × ℤ)} (hAfin : A.Finite) (hAne : A.Nonempty)
    (hBfin : B.Finite) (hBne : B.Nonempty) (hEsub : E B ⊆ E A) :
    Enveloped A (latHull (A + B)) := by
  have hTfin : (A + B).Finite := hAfin.add hBfin
  have hEeq : E (A + B) = E A := by
    rw [E_add_of_finite hAfin hBfin hAne hBne, Set.union_eq_self_of_subset_right hEsub]
  have hface : ∀ n, (face A n).encard ≤ (face (A + B) n).encard := by
    intro n
    obtain ⟨b, hb⟩ := face_nonempty hBfin hBne n
    have hinj : Set.InjOn (fun a => a + b) (face A n) :=
      fun x _ y _ h => by simpa using h
    have himg : (fun a => a + b) '' face A n ⊆ face A n + face B n := by
      rintro _ ⟨a, ha, rfl⟩
      exact Set.add_mem_add ha hb
    calc (face A n).encard = ((fun a => a + b) '' face A n).encard :=
          (Set.InjOn.encard_image hinj).symm
      _ ≤ (face A n + face B n).encard := Set.encard_mono himg
      _ = (face (A + B) n).encard := by rw [face_add]
  refine ⟨⟨isLatticeConvexRegion_latHull hTfin, fun n hn => ?_⟩, ?_⟩
  · rw [E_latHull hTfin, hEeq] at hn
    exact ⟨hn, le_trans (hface n) (Set.encard_mono (face_subset_face_latHull (A + B) n))⟩
  · rw [E_latHull hTfin, hEeq]

/-! ## §1'. The concrete `m = 3` hexagon instance -/

/-- The hexagon `(0,0),(1,0),(2,1),(2,2),(1,2),(0,1)`, as a Minkowski sum. -/
def hexA : Set (ℤ × ℤ) := segOf ((1 : ℤ), (0 : ℤ)) + segOf ((1 : ℤ), (1 : ℤ)) +
  segOf ((0 : ℤ), (1 : ℤ))

theorem hexA_finite : hexA.Finite :=
  ((finite_segOf _).add (finite_segOf _)).add (finite_segOf _)

theorem hexA_nonempty : hexA.Nonempty :=
  ((nonempty_segOf _).add (nonempty_segOf _)).add (nonempty_segOf _)

/-- `E hexA` is the union of the three generators' edge sets: filling in `E_add_of_finite`
twice. -/
theorem E_hexA :
    E hexA = E (segOf ((1 : ℤ), (0 : ℤ))) ∪ E (segOf ((1 : ℤ), (1 : ℤ))) ∪
      E (segOf ((0 : ℤ), (1 : ℤ))) := by
  unfold hexA
  rw [E_add_of_finite ((finite_segOf _).add (finite_segOf _)) (finite_segOf _)
      ((nonempty_segOf _).add (nonempty_segOf _)) (nonempty_segOf _),
    E_add_of_finite (finite_segOf _) (finite_segOf _) (nonempty_segOf _) (nonempty_segOf _)]

/-- `E (segOf (1,0)) ⊆ E hexA`: the extra generator is literally `hexA`'s first summand. -/
theorem E_segOf10_subset_E_hexA :
    E (segOf ((1 : ℤ), (0 : ℤ))) ⊆ E hexA := by
  rw [E_hexA]; exact Set.subset_union_of_subset_left Set.subset_union_left _

/-- **The instance.**  `Enveloped hexA (latHull (hexA + segOf (1,0)))`. -/
theorem enveloped_hexagon_shell :
    Enveloped hexA (latHull (hexA + segOf ((1 : ℤ), (0 : ℤ)))) :=
  enveloped_add_of_finite hexA_finite hexA_nonempty
    (finite_segOf _) (nonempty_segOf _) E_segOf10_subset_E_hexA

theorem mem_segOf_iff {v z : ℤ × ℤ} : z ∈ segOf v ↔ z = 0 ∨ z = v := Iff.rfl

/-- `subShell` for any generator set containing `0`: `A ⊆ latHull (A + B)`. -/
theorem subset_latHull_add_of_zero_mem {A B : Set (ℤ × ℤ)} (h0 : (0 : ℤ × ℤ) ∈ B) :
    A ⊆ latHull (A + B) := fun z hz =>
  subset_latHull _ (Set.mem_add.mpr ⟨z, hz, 0, h0, by simp⟩)

/-- `subShell`: `hexA ⊆ latHull (hexA + segOf (1,0))`. -/
theorem subShell_hexagon :
    hexA ⊆ latHull (hexA + segOf ((1 : ℤ), (0 : ℤ))) :=
  subset_latHull_add_of_zero_mem (mem_segOf_zero _)

/-- `dot n z ≤ max 0 (dot n v)` for `z ∈ segOf v`. -/
theorem dot_le_of_mem_segOf {n v z : ℤ × ℤ} (hz : z ∈ segOf v) :
    dot n z ≤ max 0 (dot n v) := by
  rcases mem_segOf_iff.mp hz with rfl | rfl
  · simp [dot]
  · exact le_max_right _ _

/-- **Support bound**: every point of `hexA` satisfies `x - y ≤ 1` (direction `(1,-1)`). -/
theorem dot_hexA_le (z : ℤ × ℤ) (hz : z ∈ hexA) : dot ((1 : ℤ), (-1 : ℤ)) z ≤ 1 := by
  obtain ⟨w, hw, c, hc, rfl⟩ := Set.mem_add.mp hz
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_add.mp hw
  have h1 := dot_le_of_mem_segOf (n := ((1:ℤ),(-1:ℤ))) ha
  have h2 := dot_le_of_mem_segOf (n := ((1:ℤ),(-1:ℤ))) hb
  have h3 := dot_le_of_mem_segOf (n := ((1:ℤ),(-1:ℤ))) hc
  simp only [dot, Prod.fst_add, Prod.snd_add] at h1 h2 h3 ⊢
  omega

/-- `(2,0) ∉ hexA`: it violates the support bound `x - y ≤ 1`. -/
theorem notMem_20_hexA : ((2 : ℤ), (0 : ℤ)) ∉ hexA := by
  intro h
  have := dot_hexA_le _ h
  simp [dot] at this

/-- `(1,0) ∈ hexA` (as `(1,0) + 0 + 0`). -/
theorem mem_10_hexA : ((1 : ℤ), (0 : ℤ)) ∈ hexA :=
  Set.mem_add.mpr ⟨((1:ℤ),(0:ℤ)),
    Set.mem_add.mpr ⟨((1:ℤ),(0:ℤ)), mem_segOf_self _, 0, mem_segOf_zero _, by simp⟩,
    0, mem_segOf_zero _, by simp⟩

/-- `(2,0) ∈ hexA + segOf (1,0)`, witnessing that the shell strictly exceeds `hexA`. -/
theorem mem_20_add : ((2 : ℤ), (0 : ℤ)) ∈ hexA + segOf ((1 : ℤ), (0 : ℤ)) :=
  Set.mem_add.mpr ⟨((1:ℤ),(0:ℤ)), mem_10_hexA, ((1:ℤ),(0:ℤ)), mem_segOf_self _, by simp⟩

/-- **`shellProper` for the instance**: the shell is not contained in `hexA`. -/
theorem shellProper_hexagon :
    ¬ (latHull (hexA + segOf ((1 : ℤ), (0 : ℤ))) ⊆ hexA) := by
  intro hsub
  exact notMem_20_hexA (hsub (subset_latHull _ mem_20_add))

/-! ## §2. `shellSubInf` with `B := segOf vJ1` is refuted, in general -/

/-- `g + v ∈ A + segOf v` whenever `g ∈ A`. -/
theorem add_mem_add_segOf {A : Set (ℤ × ℤ)} {g : ℤ × ℤ} (hg : g ∈ A) (v : ℤ × ℤ) :
    g + v ∈ A + segOf v :=
  Set.mem_add.mpr ⟨g, hg, v, mem_segOf_self _, rfl⟩

/-- **General refutation of `shellSubInf` for `B := segOf vJ1`.**  If `A` attains the level
`c` at `g` and the sweep direction `v` drops more than `ε` below `ℓ_J`
(`dot n v < -ε`), then `g + v` lies in `latHull (A + segOf v)` but not in
`MaxEnv.shell A v n c ε`, because the layer cut of `MaxEnv.shell` is imposed on the swept
point itself (`MaxEnv.mem_shell`). -/
theorem not_shellSubInf_of_dot_neg {A : Set (ℤ × ℤ)} {v n : ℤ × ℤ} {c : ℤ} {ε : ℕ}
    {g : ℤ × ℤ} (hg : g ∈ A) (hatt : dot n g = c) (hneg : dot n v < -(ε : ℤ)) :
    ¬ (latHull (A + segOf v) ⊆ MaxEnv.shell A v n c ε) := by
  intro hsub
  obtain ⟨_, _, _, _, hlayer⟩ := hsub (subset_latHull _ (add_mem_add_segOf hg v))
  rw [dot_add, hatt] at hlayer
  omega

/-- The `ε = 0` case: any strictly negative `dot n v` suffices. -/
theorem not_shellSubInf_zero_of_dot_neg {A : Set (ℤ × ℤ)} {v n : ℤ × ℤ} {c : ℤ}
    {g : ℤ × ℤ} (hg : g ∈ A) (hatt : dot n g = c) (hneg : dot n v < 0) :
    ¬ (latHull (A + segOf v) ⊆ MaxEnv.shell A v n c 0) :=
  not_shellSubInf_of_dot_neg hg hatt (by simpa using hneg)

/-- The unit square, as a Minkowski sum of its two "lower" edge generators. -/
def sq : Set (ℤ × ℤ) := segOf ((1 : ℤ), (0 : ℤ)) + segOf ((0 : ℤ), (1 : ℤ))

/-- `(1,1) ∈ sq`. -/
theorem mem_11_sq : ((1 : ℤ), (1 : ℤ)) ∈ sq :=
  Set.mem_add.mpr ⟨((1 : ℤ), (0 : ℤ)), mem_segOf_self _, ((0 : ℤ), (1 : ℤ)),
    mem_segOf_self _, by simp⟩

/-- `ahat_halfPlane` holds for `sq` with `nJ = (0,-1)`, `cJ = -1`. -/
theorem ahat_halfPlane_sq : ∀ z ∈ sq, (-1 : ℤ) ≤ dot ((0 : ℤ), (-1 : ℤ)) z := by
  rintro z hz
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_add.mp hz
  rcases mem_segOf_iff.mp ha with rfl | rfl <;> rcases mem_segOf_iff.mp hb with rfl | rfl <;>
    simp [dot]

/-- **The concrete instance** (`Ahat := sq`, `vJ1 := (0,1)`, `nJ := (0,-1)`, `cJ := -1`,
`ε := 0`), now a corollary of `not_shellSubInf_zero_of_dot_neg` at `g := (1,1)`. -/
theorem not_shellSubInf_sq_zero :
    ¬ (latHull (sq + segOf ((0 : ℤ), (1 : ℤ))) ⊆
        MaxEnv.shell sq ((0 : ℤ), (1 : ℤ)) ((0 : ℤ), (-1 : ℤ)) (-1 : ℤ) 0) :=
  not_shellSubInf_zero_of_dot_neg mem_11_sq (by simp [dot]) (by simp [dot])

/-! ## §2'. The same two facts on the real bundle `ChainDataGeom` -/

section Bundle

open Nivat.Colle35 Nivat.MaxEnv

variable {α : Type*}

/-- **Positive half of the layer cut.**  The raw sum `Ahat i + segOf vJ1` lies in
`shellInf ε` as soon as `ε ≥ -dot nJ vJ1`: both `g` and `g + vJ1` are in `reachSet`, and
`ahat_halfPlane` plus the bound on `dot nJ vJ1` keep them above the cut.  This is the only
part of `shellSubInf` that the raw sum can owe; what `latHull` adds is not covered here. -/
theorem ChainDataWithShell.add_segOf_vJ1_subset_shellInf {η xper : Config α} {vl gen : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} (cd : ChainDataWithShell η xper vl S gen) (i ε : ℕ)
    (hε : -(ε : ℤ) ≤ dot cd.nJ cd.vJ1) :
    cd.toChainData.Ahat i + segOf cd.vJ1 ⊆ cd.toChainData.shellInf ε := by
  rw [cd.shellInf_eq]
  rintro z hz
  obtain ⟨g, hg, b, hb, rfl⟩ := Set.mem_add.mp hz
  have hgU : g ∈ ⋃ j, cd.toChainData.Ahat j := Set.mem_iUnion.mpr ⟨i, hg⟩
  have hgh := cd.ahat_halfPlane g hgU
  rcases mem_segOf_iff.mp hb with rfl | rfl
  · exact ⟨g, hgU, 0, by simp, by rw [add_zero]; omega⟩
  · exact ⟨g, hgU, 1, by simp, by rw [dot_add]; omega⟩

/-- **Exact residual obligation of the ε-dependent variant.**  If the layer cut is affordable
(`-ε ≤ dot nJ vJ1`) and the hull does not escape the sweep set
(`latHull (Ahat i + segOf vJ1) ⊆ reachSet (⋃ Ahat) vJ1`), then
`latHull (Ahat i + segOf vJ1) ⊆ shellInf ε`.  The layer cut survives `latHull` because it is a
half-plane bound (`dot_le_of_mem_latHull` on `-nJ`); only the sweep-set containment is left,
and §4 shows that containment is not free. -/
theorem ChainDataWithShell.latHull_add_segOf_vJ1_subset_shellInf {η xper : Config α}
    {vl gen : ℤ × ℤ} {S : Finset (ℤ × ℤ)} (cd : ChainDataWithShell η xper vl S gen) (i ε : ℕ)
    (hε : -(ε : ℤ) ≤ dot cd.nJ cd.vJ1)
    (hreach : latHull (cd.toChainData.Ahat i + segOf cd.vJ1) ⊆
      reachSet (⋃ j, cd.toChainData.Ahat j) cd.vJ1) :
    latHull (cd.toChainData.Ahat i + segOf cd.vJ1) ⊆ cd.toChainData.shellInf ε := by
  intro z hz
  rw [cd.shellInf_eq, shell_eq_reach_inter]
  refine ⟨hreach hz, ?_⟩
  have hbound : ∀ y ∈ cd.toChainData.Ahat i + segOf cd.vJ1, dot (-cd.nJ) y ≤ (ε : ℤ) - cd.cJ := by
    rintro y hy
    obtain ⟨g, hg, b, hb, rfl⟩ := Set.mem_add.mp hy
    have hgh := cd.ahat_halfPlane g (Set.mem_iUnion.mpr ⟨i, hg⟩)
    rw [dot_neg_left, dot_add]
    rcases mem_segOf_iff.mp hb with rfl | rfl
    · rw [dot_zero_right]; omega
    · omega
  have := dot_le_of_mem_latHull hbound hz
  rw [dot_neg_left] at this
  show cd.cJ - (ε : ℤ) ≤ dot cd.nJ z
  omega

/-- **Refutation on the real bundle.**  For any `ChainDataGeom cg`, any `i`, and any
`g ∈ Ahat i` attaining `cJ`, the candidate `latHull (Ahat i + segOf vJ1)` is **not** contained
in `shellInf ε` whenever `dot nJ vJ1 < -ε`.  The sign `dot nJ vJ1 < 0` is
`ChainDataGeom.dot_nJ_vJ1_neg` (`ANormal.lean:747`), forced by `bottom 0`; so at `ε = 0` the
only remaining hypothesis is attainment (`ChainDataGeom.not_shellSubInf_segOf_vJ1_zero`).

Consequence: the ε-independent encoding `shell i ε := latHull (Ahat i + segOf vJ1)` violates
`shellSubInf` at `ε = 0` on every bundle where `cJ` is attained on some `Ahat i`; and the
ε-dependent variant that switches it on for `0 < ε` still fails at `ε = 1` whenever
`dot nJ vJ1 ≤ -2`. -/
theorem ChainDataGeom.not_shellSubInf_segOf_vJ1 {η xper : Config α} {vl p gen : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} (cg : ChainDataGeom η xper vl p S gen) {i : ℕ} {g : ℤ × ℤ}
    (hg : g ∈ cg.toChainData.Ahat i) (hatt : dot cg.nJ g = cg.cJ) (ε : ℕ)
    (hε : dot cg.nJ cg.vJ1 < -(ε : ℤ)) :
    ¬ (latHull (cg.toChainData.Ahat i + segOf cg.vJ1) ⊆ cg.toChainData.shellInf ε) := by
  rw [cg.shellInf_eq]
  intro hsub
  obtain ⟨_, _, _, _, hlayer⟩ := hsub (subset_latHull _ (add_mem_add_segOf hg cg.vJ1))
  rw [dot_add, hatt] at hlayer
  omega

/-- The `ε = 0` case on the real bundle: attainment alone refutes it, the sign being
`ChainDataGeom.dot_nJ_vJ1_neg`. -/
theorem ChainDataGeom.not_shellSubInf_segOf_vJ1_zero {η xper : Config α} {vl p gen : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} (cg : ChainDataGeom η xper vl p S gen) {i : ℕ} {g : ℤ × ℤ}
    (hg : g ∈ cg.toChainData.Ahat i) (hatt : dot cg.nJ g = cg.cJ) :
    ¬ (latHull (cg.toChainData.Ahat i + segOf cg.vJ1) ⊆ cg.toChainData.shellInf 0) :=
  ChainDataGeom.not_shellSubInf_segOf_vJ1 cg hg hatt 0 (by simpa using cg.dot_nJ_vJ1_neg)

/-- **Unconditional refutation on the real bundle: no attainment hypothesis.**  For every
`ChainDataGeom cg` there is an `i` at which `latHull (Ahat i + segOf vJ1) ⊄ shellInf 0`.

Take `g ∈ ⋃ Ahat` minimising `dot nJ` (exists: `ahat_nonempty`, bounded below by `cJ` via
`ahat_halfPlane`), say `g ∈ Ahat i`.  Then `g + vJ1 ∈ Ahat i + segOf vJ1`; were it in
`shellInf 0`, `shellInfZero` would put it in `⋃ Ahat` with
`dot nJ (g + vJ1) = dot nJ g + dot nJ vJ1 < dot nJ g` (`ChainDataGeom.dot_nJ_vJ1_neg`),
contradicting minimality.  So the ε-independent encoding `shell i ε := latHull (Ahat i +
segOf vJ1)` violates `shellSubInf` at `ε = 0` on **every** `ChainDataGeom`. -/
theorem ChainDataGeom.exists_not_shellSubInf_segOf_vJ1_zero {η xper : Config α}
    {vl p gen : ℤ × ℤ} {S : Finset (ℤ × ℤ)} (cg : ChainDataGeom η xper vl p S gen) :
    ∃ i : ℕ, ¬ (latHull (cg.toChainData.Ahat i + segOf cg.vJ1) ⊆ cg.toChainData.shellInf 0) := by
  -- the minimiser of `dot nJ` over `⋃ Ahat`
  obtain ⟨m, ⟨g, hgU, hgm⟩, hmin⟩ := Int.exists_least_of_bdd
    (P := fun z => ∃ g ∈ ⋃ j, cg.toChainData.Ahat j, dot cg.nJ g = z)
    ⟨cg.cJ, fun z ⟨g, hg, hz⟩ => hz ▸ cg.ahat_halfPlane g hg⟩
    (let ⟨g, hg⟩ := cg.ahat_nonempty; ⟨dot cg.nJ g, g, hg, rfl⟩)
  obtain ⟨i, hgi⟩ := Set.mem_iUnion.mp hgU
  refine ⟨i, fun hsub => ?_⟩
  have hmem : g + cg.vJ1 ∈ cg.toChainData.shellInf 0 :=
    hsub (subset_latHull _ (add_mem_add_segOf hgi cg.vJ1))
  have hU : g + cg.vJ1 ∈ ⋃ j, cg.toChainData.Ahat j := cg.shellInfZero hmem
  have hle : m ≤ dot cg.nJ (g + cg.vJ1) := hmin _ ⟨_, hU, rfl⟩
  have hneg := cg.dot_nJ_vJ1_neg
  rw [dot_add, hgm] at hle
  omega

end Bundle

/-! ## §4. `latHull` escapes the sweep set — kernel counterexample on raw parameters

`tri := {(x,y) | 0 ≤ y, 0 ≤ 7x - 3y, 7x - 2y ≤ 7}` is the lattice-point set of the lattice
triangle `(0,0),(1,0),(3,7)`; `(1,0)` is one of its edge directions (bottom edge).  At height
`y = 3` its chord is `x ∈ [9/7, 13/7]`, shorter than `1` and lattice-point-free, so
`tri ∩ {y = 3} = ∅`.  Hence `(2,3) ∉ reachSet tri (1,0)` (a swept point keeps its height), but
`(2,3)` is the midpoint of `(2,2) ∈ tri + (1,0)` and `(2,4) ∈ tri`, so
`(2,3) ∈ latHull (tri + segOf (1,0))`.  The raw sum is not lattice-convex, and its hull leaves
the sweep set: `latHull (A + segOf v) ⊆ reachSet A v` is **false in general**, even for `A`
lattice-convex and `v` one of `A`'s edge directions. -/

section Escape

open Nivat.MaxEnv

/-- Lattice points of the triangle `(0,0),(1,0),(3,7)`. -/
def tri : Set (ℤ × ℤ) :=
  {z | 0 ≤ z.2 ∧ 0 ≤ 7 * z.1 - 3 * z.2 ∧ 7 * z.1 - 2 * z.2 ≤ 7}

theorem mem_12_tri : ((1 : ℤ), (2 : ℤ)) ∈ tri := by simp [tri]

theorem mem_24_tri : ((2 : ℤ), (4 : ℤ)) ∈ tri := by simp [tri]

/-- No point of `tri` at height `3`. -/
theorem not_mem_tri_of_snd_eq_three (z : ℤ × ℤ) (hz : z.2 = 3) : z ∉ tri := by
  rintro ⟨_, h1, h2⟩; omega

/-- `(2,3)` is not reached by sweeping `tri` along `(1,0)`. -/
theorem not_mem_reachSet_tri : ((2 : ℤ), (3 : ℤ)) ∉ reachSet tri ((1 : ℤ), (0 : ℤ)) := by
  rintro ⟨g, hg, t, heq⟩
  refine not_mem_tri_of_snd_eq_three g ?_ hg
  have := congrArg Prod.snd heq
  simp at this
  omega

/-- `(2,3) ∈ latHull (tri + segOf (1,0))`, as the midpoint of `(2,2)` and `(2,4)`. -/
theorem mem_latHull_tri_add : ((2 : ℤ), (3 : ℤ)) ∈ latHull (tri + segOf ((1 : ℤ), (0 : ℤ))) := by
  have h22 : ((2 : ℤ), (2 : ℤ)) ∈ tri + segOf ((1 : ℤ), (0 : ℤ)) :=
    Set.mem_add.mpr ⟨_, mem_12_tri, _, mem_segOf_self _, by simp⟩
  have h24 : ((2 : ℤ), (4 : ℤ)) ∈ tri + segOf ((1 : ℤ), (0 : ℤ)) :=
    Set.mem_add.mpr ⟨_, mem_24_tri, 0, mem_segOf_zero _, by simp⟩
  rw [mem_latHull_iff]
  have hx := subset_convexHull ℝ _ (Set.mem_image_of_mem toReal h22)
  have hy := subset_convexHull ℝ _ (Set.mem_image_of_mem toReal h24)
  have hmid := (convex_convexHull ℝ _) hx hy (a := (1 / 2 : ℝ)) (b := (1 / 2 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
  have heq : toReal ((2 : ℤ), (3 : ℤ)) =
      (1 / 2 : ℝ) • toReal ((2 : ℤ), (2 : ℤ)) + (1 / 2 : ℝ) • toReal ((2 : ℤ), (4 : ℤ)) := by
    refine Prod.ext ?_ ?_ <;> simp [toReal] <;> norm_num
  rw [heq]; exact hmid

/-- **`latHull (A + segOf v) ⊆ reachSet A v` fails**, for `A := tri`, `v := (1,0)`. -/
theorem not_latHull_add_subset_reachSet :
    ¬ (latHull (tri + segOf ((1 : ℤ), (0 : ℤ))) ⊆ reachSet tri ((1 : ℤ), (0 : ℤ))) :=
  fun h => not_mem_reachSet_tri (h mem_latHull_tri_add)

/-- The same point escapes every `MaxEnv.shell tri (1,0) n c ε`, since the shell is a subset
of the reach set (`shell_eq_reach_inter`). -/
theorem not_latHull_add_subset_shell (n : ℤ × ℤ) (c : ℤ) (ε : ℕ) :
    ¬ (latHull (tri + segOf ((1 : ℤ), (0 : ℤ))) ⊆ shell tri ((1 : ℤ), (0 : ℤ)) n c ε) := by
  intro h
  have := h mem_latHull_tri_add
  rw [shell_eq_reach_inter] at this
  exact not_mem_reachSet_tri this.1

end Escape

/-! ## §5. The faithful `:518` **intersection** encoding

`b3_colle2.txt:518` verbatim: `Â_i^{(ε)} := {g − t·v_{ℓ_{J+1}} ∈ Â_∞^{(ε)} : g ∈ Â_i, t ∈ ℤ₊}`.
The `∈ Â_∞^{(ε)}` inside the set-builder is a filter, so the definition is
`(sweep of Â_i along w) ∩ Â_∞^{(ε)}` with `w := −v_{ℓ_{J+1}}` — `shellInter` below.
`shellSubInf` is then `Set.inter_subset_right` (`shellInter_subset_right`).

⛔ **2026-09-25 裁决（集成者）：`w := vJ1`（`J−1` 读法）已被反驳，本节收敛成单栏 ——
活的是下面的横截读法 `w := −v_{ℓ_{J+1}}`。** 本段与随后的价目表按 §14 一字不删地留在原处，
因为它们现在是**反驳的前一半证据**，不再是一个可选读法。

反驳是两条内核事实的合成，不是偏好：

1. `shellInter_shell_eq`（`:529`）＋ `ChainDataWithShell.shellInter_vJ1_eq`（`:588`）证明
   取 `w := vJ1` 时 `:518` 的对象**逐点等于**单次 sweep `MaxEnv.shell (Ahat i) vJ1 nJ cJ ε`。
   这两条仍然成立，见 `:588` 的反向警示。
2. `FillCoverWitness.not_fillCover_singleSweep`（`FillCoverWitness.lean:126`）在**正是本构型的
   数据上**（`vl = vJ1 = (0,-1)`、`nJ = (0,1)`、`cJ = 0`、`(i,i₀,ε) = (2,1,1)`）内核否掉
   单次 sweep 的 `fillCover`，对一切 `gen.1 ≤ 1` 成立 —— 含 `gen = (1,0) = F.a'`
   （`not_fillCover_singleSweep_gen10`，`:143`；`gen_eq` 钉的就是这个）。

⛔ **2026-09-25 就地订正（lane-leafa-gen，PROTOCOL §26 / §103）：上面第 2 条撑不起对
迁移后字段的反驳，`(1)+(2)` 这条合成作废。** 裁决结论（`w` 必须横截）不变，但引证要换。

* 第 2 条否掉的是 `ChainDataGeom.ofParts` 的**无守卫** `fillCover` binder
  —— `FillCoverWitness.lean` 自己的开头（`:19-20`）就是这么写辖域的。
* 迁移后链上的字段带守卫 `(∀ i, i₀ ≤ i → EnvOf ↑S (shellInter …))`
  （`ChainPartsFeed.lean:271-279`）。在第 2 条所用的**同一台架**上取 `w := vJ1`，
  那条守卫**对一切 `ε`、一切 `i` 都为假**（`FillCoverWit.not_envOf_shell_Ai`，
  `FillCoverWitness.lean` §5）：塌成的单次 sweep 丢了 `(1,-1)` 边（`Nondeg` 的
  `1 ≤ a - d + e` 在 `d = 2i+ε` 处恰好破），`E` 只剩 5 个法向。
  ⟹ 带守卫的 `fillCover` 字段在那里是**空真**的
  （`FillCoverWit.fillCover_field_vacuous_at_vJ1`），反例咬不到它。
* ✅ **正确引证：同一条 `not_envOf_shell_Ai` 直接否掉 `shellEnv` 字段**
  （`ChainPartsFeed.lean:265-267`，`∃ ε i₀, 0 < ε ∧ ∀ i ≥ i₀, EnvOf …`）——
  `FillCoverWit.not_shellEnv_field_at_vJ1`。**`w := vJ1` 死在 `shellEnv` 上，
  不是死在 `fillCover` 上。** 对照：横截 `w = (-1,-1)` 在同一台架同一 `ε` 上守卫成立
  （`FillCoverWit.envOf_shell518_transverse`），外层壳两边都写成 `⋃ k, Ai k`
  （`iUnion_Ai_eq_quad` 钉成 `quad`，PROTOCOL §102）。
* ⟹ 本节下面那句「`shellEnv` — unchanged by the intersection: the set is the same set」
  也随之改判：在 `w := vJ1` 读法下 `shellEnv` 不是「不变」，而是**在台架上为假**；
  交集恰恰是它活下来的唯一原因。

合成（订正后）：`w := vJ1` ⟹ `:518` 对象 ≡ 单次 sweep ⟹ 该对象兑现不了 `EnvOf ↑S`
⟹ `shellEnv` 字段为假。⟹ **`w` 必须横截。**

⚠ **2026-09-25 续测：上面这条合成的第三步是**窗口相关**的，不是一般事实**
（lane-leafa-gen，`FillCoverWitness.lean` §6）。换成方窗口 `sq1`、塔取
`box (0,0) (i+1,i+1)` 后，同一个 `w := vJ1` 的 `shellEnv` 字段**成立**
（`FillCoverWit.shellEnv_field_at_vJ1_square`，`ε = 1`、`i₀ = 0`、对一切 `i`），
而链上 16 条对 `w`/`vl`/`vJ1`/`nJ`/`S`/`Â` 有约束力的前提全兑现
（`FillCoverWit.not_shellEnv_imp_det_ne_zero`）。⟹ 本节的裁决对 `hexF` 台架成立，
**但「`w` 必须横截」不能作为 `ChainDataGeomParts` 层面的定理引用** ——
`det vl w ≠ 0` 是字段（集成者第 228 轮加），不是从 `shellEnv` 导出的。
机制的一般形是 `FillCoverWit.E_shell_eq_of_shellEnv_at_vJ1`：`w := vl` 那一格逼出的是
`E(单次 sweep) = E ↑S`，成败只看 `E ↑S` 里有没有被 `vJ1` 抬高、又不是 `-nJ` 的法向。

⛔ 原合成（留档，勿再引用）：`w := vJ1` ⟹ `:518` 对象 ≡ 单次 sweep ⟹ 继承 (2) 的反例 ⟹
`fillCover` 在 `ChainDataGeomParts` 真正需要的那个 `gen` 上为假。

正方向同一实例：`FillCoverWitness.fillCover_518_gen10`（`:160`）在 `:518` 的交集对象上、
取横截 `w = (-1,-1)`（`det vJ1 w = -1 ≠ 0`）时 `fillCover` **成立**。
⚠ 分母：该正向收据是**对 `gen = (1,0)` 这一个生成元**的；同节 `not_fillCover_518_gen00`（`:203`）
说明横截并不救所有 `gen`。救的恰好是 `gen_eq` 钉死的那个，这是它够用的理由，不是它普遍成立。

⚠ 与 `vJ1 ∥ vl` 不冲突：`vJ1` 共线（`J = ι+1` 构型）说的是 `vJ1`，`w` 是**另一份**数据，
`hsweepW : dot nJ w < 0` 与 `det vl w ≠ 0` 照旧是独立输入（`ChainPartsFeed.lean:236-239`）。

---

**以下为已被反驳的 `J−1` 读法原文（§14 留档）。**
Under the `J−1` reading (`w = vJ1`, the sweep direction of `shellInf` itself) the
intersection form is not a new encoding: `shellInter_shell_eq` shows
`reachSet A vJ1 ∩ MaxEnv.shell A' vJ1 n c ε = MaxEnv.shell A vJ1 n c ε` whenever `A ⊆ A'`, and
`ChainDataWithShell.shellInter_vJ1_eq` specialises it to the bundle: the `:518` shell **is** the
single sweep `MaxEnv.shell (Ahat i) vJ1 nJ cJ ε`, as a set equality.  Everything measured
against the single sweep transfers verbatim.

The price, under that (refuted) reading (all kernel facts on raw parameters, then on the
bundle):

* `shellFinite`, `subShell` — free: `MaxEnv.shell_finite` with `ChainDataGeom.dot_nJ_vJ1_neg`,
  `MaxEnv.subset_shell` with `ahat_halfPlane`.
* `shellProper` — **conditional, and the condition is the old wall `−ε ≤ dot nJ vJ1`
  again.**  `not_shell_subset_of_dot_eq_neg_one`: when `dot nJ vJ1 = −1` the `dot nJ`-minimiser
  of a finite nonempty `Ahat i` steps out of `Ahat i` and stays above the cut, for every
  `0 < ε`.  `shell_subset_of_thin`: when every `g ∈ A` has `dot nJ g + dot nJ vJ1 < cJ − ε`,
  the cut removes every swept point with `t ≥ 1` and the shell collapses to `A` — in particular
  (`shell_one_subset_of_support_line`) `dot nJ vJ1 ≤ −2` with `A` on the support line kills
  `ε = 1`.  So the intersection with `Â_∞^{(ε)}` *does* shrink the shell back into `Â_i`
  exactly when the sweep step is deeper than the cut allows.
* `shellSubStrip` — binds exactly as before.  Positive: `ChainData.shell_subset_strip_of_nsmul`
  (`vJ1 = m • vl`, `m : ℕ`, the sweep stays in the half-strip).  Negative:
  `not_shellSubStrip_of_transverse_sweep` (re-landed from `tmp/shell_block_free.lean:285`):
  `det vl vJ1 ≠ 0` fails the field at some `ε`, for any `n c k`, as soon as `B i` is finite and
  `Ahat i` nonempty.
* `shellEnv` — unchanged by the intersection: the set is the same set.  Not attempted here.

**Under the literal `J+1` reading (`w` transverse to `vJ1`) —— 2026-09-25 裁决后这是唯一活的
读法** only `shellSubInf` and `subShell` are settled (both free, `shellInter_subset_right` /
`subset_shellInter`).  `shellProper` is
the criterion `not_shellInter_subset` (some `g + t • w`, `t ≥ 1`, inside `Â_∞^{(ε)}` and outside
`Â_i`), and `shellInter_transverse_collapses` is a kernel example where a transverse `w` makes
the intersection collapse to `A` although the same `A`, `Â_∞^{(ε)}` are proper under `w = vJ1`.

⛔ **本段末句「Whether that happens on a real bundle is not settled: `ChainDataGeom` says
nothing about `v_{ℓ_{J+1}}`」已过期，2026-09-25 就地订正。** 它写于 `w` 还不是数据的时候。
现在 `w` 是 `ChainDataGeomParts` 的**字段**（`ChainPartsFeed.lean:236`），连同
`hsweepW : dot nJ w < 0`（`:239`）一并由生产者提供 —— 结构体不再对 `v_{ℓ_{J+1}}` 沉默。
`shellInter_transverse_collapses` 因此不再是「可能发生的坏事」，而是**对生产者的一条约束**：
选 `w` 时必须避开它刻画的那个退化构型。⚠ 生产者侧是否真能避开，本文件**未主张**。 -/

section Inter

open Nivat.MaxEnv Nivat.Colle35

/-- **`b3_colle2.txt:518`**: `{g + t • w : g ∈ A, t ∈ ℤ₊} ∩ Ainf`.  With `w := −v_{ℓ_{J+1}}`
this is the paper's `Â_i^{(ε)}`; with `w := v_{ℓ_{J−1}}` the typo-corrected reading. -/
def shellInter (A Ainf : Set (ℤ × ℤ)) (w : ℤ × ℤ) : Set (ℤ × ℤ) :=
  reachSet A w ∩ Ainf

/-- **`shellSubInf` for the intersection form is `Set.inter_subset_right`**, for any `w`. -/
theorem shellInter_subset_right (A Ainf : Set (ℤ × ℤ)) (w : ℤ × ℤ) :
    shellInter A Ainf w ⊆ Ainf :=
  Set.inter_subset_right

/-- **`subShell` for the intersection form**: `A ⊆ Ainf` suffices (`t = 0`), for any `w`. -/
theorem subset_shellInter {A Ainf : Set (ℤ × ℤ)} (hA : A ⊆ Ainf) (w : ℤ × ℤ) :
    A ⊆ shellInter A Ainf w :=
  fun g hg => ⟨⟨g, hg, 0, by simp⟩, hA hg⟩

theorem reachSet_mono {A A' : Set (ℤ × ℤ)} (h : A ⊆ A') (v : ℤ × ℤ) :
    reachSet A v ⊆ reachSet A' v := by
  rintro z ⟨g, hg, t, rfl⟩
  exact ⟨g, h hg, t, rfl⟩

/-- **`J−1` reading: the intersection form collapses to the single sweep.**  If `A ⊆ A'` then
`reachSet A v ∩ MaxEnv.shell A' v n c ε = MaxEnv.shell A v n c ε`: the `Â_∞`-sweep condition is
implied by the `Â_i`-sweep condition, and only the layer cut is left. -/
theorem shellInter_shell_eq {A A' : Set (ℤ × ℤ)} (h : A ⊆ A') (v n : ℤ × ℤ) (c : ℤ) (ε : ℕ) :
    shellInter A (shell A' v n c ε) v = shell A v n c ε := by
  unfold shellInter
  rw [shell_eq_reach_inter, shell_eq_reach_inter]
  ext z
  constructor
  · rintro ⟨hr, -, hd⟩; exact ⟨hr, hd⟩
  · rintro ⟨hr, hd⟩; exact ⟨hr, reachSet_mono h v hr, hd⟩

/-- **`shellProper` criterion for the intersection form** (any `w`): a swept point inside
`Ainf` and outside `A`. -/
theorem not_shellInter_subset {A Ainf : Set (ℤ × ℤ)} {w g : ℤ × ℤ} {t : ℕ} (hg : g ∈ A)
    (hin : g + (t : ℤ) • w ∈ Ainf) (hout : g + (t : ℤ) • w ∉ A) :
    ¬ shellInter A Ainf w ⊆ A :=
  fun h => hout (h ⟨⟨g, hg, t, rfl⟩, hin⟩)

/-- **The cut can collapse a sweep back into `A`.**  If every `g ∈ A` sits so low that one
step along `v` already falls below `c − ε`, the only surviving swept points are the `t = 0`
ones, i.e. `A` itself — and `shellProper` fails at this `ε`. -/
theorem shell_subset_of_thin {A : Set (ℤ × ℤ)} {v n : ℤ × ℤ} {c : ℤ} {ε : ℕ}
    (hv : dot n v < 0) (hthin : ∀ g ∈ A, dot n g + dot n v < c - (ε : ℤ)) :
    shell A v n c ε ⊆ A := by
  rintro z ⟨g, hg, t, rfl, hz⟩
  rcases t with _ | t
  · simpa using hg
  · exfalso
    have hdot : dot n (g + ((t + 1 : ℕ) : ℤ) • v) = dot n g + ((t : ℤ) + 1) * dot n v := by
      rw [dot_add, Nivat.ColleReg.dot_zsmul_right]; push_cast; ring
    have ht : (t : ℤ) * dot n v ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg t) hv.le
    have := hthin g hg
    rw [hdot] at hz
    nlinarith

/-- **`dot n v ≤ −2` with `A` on the support line kills `ε = 1`.**  Concretely: the single-sweep
(= `J−1`-intersection) shell of thickness `1` is contained in `A`. -/
theorem shell_one_subset_of_support_line {A : Set (ℤ × ℤ)} {v n : ℤ × ℤ} {c : ℤ}
    (hv : dot n v ≤ -2) (hline : ∀ g ∈ A, dot n g = c) :
    shell A v n c 1 ⊆ A :=
  shell_subset_of_thin (by omega) (fun g hg => by rw [hline g hg]; push_cast; omega)

/-- **`shellProper` for the single sweep when `dot n v = −1`.**  The `dot n`-minimiser `g` of a
finite nonempty `A ⊆ {c ≤ dot n ·}` has `g + v ∉ A` (strictly lower level) and
`dot n (g + v) = dot n g − 1 ≥ c − 1 ≥ c − ε` for every `0 < ε`. -/
theorem not_shell_subset_of_dot_eq_neg_one {A : Set (ℤ × ℤ)} {v n : ℤ × ℤ} {c : ℤ}
    (hA : A.Finite) (hne : A.Nonempty) (hhalf : ∀ g ∈ A, c ≤ dot n g) (hv : dot n v = -1)
    {ε : ℕ} (hε : 0 < ε) : ¬ shell A v n c ε ⊆ A := by
  obtain ⟨g, hg, hmin⟩ := Set.exists_min_image A (dot n) hA hne
  have hgv : dot n (g + ((1 : ℕ) : ℤ) • v) = dot n g - 1 := by
    rw [dot_add, Nivat.ColleReg.dot_zsmul_right, hv]; push_cast; ring
  refine not_shell_subset (t := 1) hg ?_ ?_
  · intro h
    have := hmin _ h
    rw [hgv] at this
    omega
  · rw [hgv]
    have := hhalf g hg
    omega

/-- **Bundle: the `:518` shell under the `J−1` reading is the single sweep, as sets.**

⛔ **不得用于填 `ChainDataGeomParts` 的 shell 字段**（`shellSubStrip` / `shellEnv` /
`fillCover`，`ChainPartsFeed.lean:257-279`）。2026-09-25 裁决：本定理成立，但它证明的正是
`w := vJ1` 使 `:518` 的对象塌回单次 sweep，而单次 sweep 的 `fillCover` 已被
`FillCoverWitness.not_fillCover_singleSweep`（`FillCoverWitness.lean:126`）在同一组数据上
（`vJ1 = (0,-1)`、`nJ = (0,1)`、`cJ = 0`、`(i,i₀,ε) = (2,1,1)`、一切 `gen.1 ≤ 1`，含
`gen = (1,0) = F.a'`）内核否掉。⟹ 拿本定理去把字段改写成单次 sweep，等于把那个反例接进链上。
完整论证见 §5 开头的裁决段。

本定理的**正当用途**是：当需要说明「为什么 `w` 不能取 `vJ1`」时引它作前一半证据；
以及在 `w` 确实等于 `vJ1` 的**台架**上做化简（§54：台架结论不外推）。 -/
theorem ChainDataWithShell.shellInter_vJ1_eq {α : Type*} {η xper : Config α} {vl gen : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} (cd : ChainDataWithShell η xper vl S gen) (i ε : ℕ) :
    shellInter (cd.toChainData.Ahat i) (cd.toChainData.shellInf ε) cd.vJ1 =
      shell (cd.toChainData.Ahat i) cd.vJ1 cd.nJ cd.cJ ε := by
  rw [cd.shellInf_eq]
  exact shellInter_shell_eq (Set.subset_iUnion (fun j => cd.toChainData.Ahat j) i) _ _ _ _

/-- `Â_i` is finite on any `ChainData`, from the existing shell fields at `ε = 0`
(`RegionSteps.lean` uses the same two fields for `hAhatfin`). -/
theorem ChainData.ahat_finite {α : Type*} {η xper : Config α} {vl gen : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} (c : ChainData η xper vl S gen) (i : ℕ) : (c.Ahat i).Finite :=
  (c.shellFinite i 0).subset (c.subShell i 0)

/-- **Bundle, `shellFinite`**: free from `dot_nJ_vJ1_neg`. -/
theorem ChainDataGeom.shellInter_vJ1_finite {α : Type*} {η xper : Config α}
    {vl p gen : ℤ × ℤ} {S : Finset (ℤ × ℤ)} (cg : ChainDataGeom η xper vl p S gen) (i ε : ℕ) :
    (shellInter (cg.toChainData.Ahat i) (cg.toChainData.shellInf ε) cg.vJ1).Finite := by
  rw [ChainDataWithShell.shellInter_vJ1_eq]
  exact shell_finite (ChainData.ahat_finite cg.toChainData i) cg.dot_nJ_vJ1_neg

/-- **Bundle, `subShell`**: free from `ahat_halfPlane`. -/
theorem ChainDataWithShell.subset_shellInter_vJ1 {α : Type*} {η xper : Config α}
    {vl gen : ℤ × ℤ} {S : Finset (ℤ × ℤ)} (cd : ChainDataWithShell η xper vl S gen) (i ε : ℕ) :
    cd.toChainData.Ahat i ⊆ shellInter (cd.toChainData.Ahat i) (cd.toChainData.shellInf ε) cd.vJ1 := by
  rw [ChainDataWithShell.shellInter_vJ1_eq]
  exact subset_shell ε (fun g hg => cd.ahat_halfPlane g (Set.mem_iUnion.mpr ⟨i, hg⟩))

/-- **Bundle, `shellProper` under `dot nJ vJ1 = −1`**, for every `i` with `Â_i ≠ ∅`.  Nothing in
`ChainDataGeom` records `dot nJ vJ1 = −1` (only `< 0`, `ChainDataGeom.dot_nJ_vJ1_neg`) nor
`(Ahat i).Nonempty` for every `i` (only `ahat_nonempty` for the union), so both are hypotheses. -/
theorem ChainDataGeom.shellInter_vJ1_proper {α : Type*} {η xper : Config α}
    {vl p gen : ℤ × ℤ} {S : Finset (ℤ × ℤ)} (cg : ChainDataGeom η xper vl p S gen)
    (hv : dot cg.nJ cg.vJ1 = -1) (i : ℕ) (hne : (cg.toChainData.Ahat i).Nonempty) {ε : ℕ}
    (hε : 0 < ε) :
    ¬ shellInter (cg.toChainData.Ahat i) (cg.toChainData.shellInf ε) cg.vJ1 ⊆
      cg.toChainData.Ahat i := by
  rw [ChainDataWithShell.shellInter_vJ1_eq]
  exact not_shell_subset_of_dot_eq_neg_one (ChainData.ahat_finite cg.toChainData i) hne
    (fun g hg => cg.ahat_halfPlane g (Set.mem_iUnion.mpr ⟨i, hg⟩)) hv hε

/-- **`shellSubStrip` for a sweep along a non-negative multiple of `vl`.**  `Â_i` lies in the
shifted half-strip by `AhatEq` + `subStrip`, and `+ t • (m • vl)` stays in it. -/
theorem ChainData.shell_subset_strip_of_nsmul {α : Type*} {η xper : Config α} {vl gen : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} (c : ChainData η xper vl S gen) (i ε : ℕ) {v : ℤ × ℤ} {m : ℕ}
    (hm : v = (m : ℤ) • vl) (n : ℤ × ℤ) (cc : ℤ) :
    shell (c.Ahat i) v n cc ε ⊆ {z | z + (c.kk i : ℤ) • vl ∈ Colle35.halfStrip (c.B i) vl} := by
  rintro z ⟨g, hg, t, rfl, -⟩
  have hg' : g + (c.kk i : ℤ) • vl ∈ c.A i := by
    rw [c.AhatEq] at hg; exact hg
  obtain ⟨b, hb, s, hs⟩ := c.subStrip i hg'
  refine ⟨b, hb, s + t * m, ?_⟩
  show g + (t : ℤ) • v + (c.kk i : ℤ) • vl = b + ((s + t * m : ℕ) : ℤ) • vl
  rw [hm, smul_smul]
  push_cast
  rw [add_smul, ← add_assoc, ← hs]
  abel

/-- `det u (x + y) = det u x + det u y`. -/
theorem det_add_right (u x y : ℤ × ℤ) : det u (x + y) = det u x + det u y := by
  simp only [det, Prod.fst_add, Prod.snd_add]; ring

/-- `det vl ·` is constant along `vl`, hence bounded on a half-strip with finite base
(re-landed from `tmp/shell_block_free.lean:265`). -/
theorem det_bounded_on_halfStrip {Bi : Set (ℤ × ℤ)} (hB : Bi.Finite) (vl : ℤ × ℤ) :
    ∃ M : ℤ, ∀ z ∈ Colle35.halfStrip Bi vl, |det vl z| ≤ M := by
  obtain ⟨M, hM⟩ := (hB.image (fun b => |det vl b|)).bddAbove
  refine ⟨max M 0, ?_⟩
  rintro z ⟨b, hb, t, rfl⟩
  have hb' : |det vl b| ≤ M := hM ⟨b, hb, rfl⟩
  have : det vl (b + (t : ℤ) • vl) = det vl b := by
    rw [det_add_right, Nivat.ColleReg.det_smul_right, det_self]; ring
  rw [this]
  exact le_trans hb' (le_max_left _ _)

/-- **`shellSubStrip` refutes every transverse sweep** (re-landed from
`tmp/shell_block_free.lean:285`).  If `shell i ε := MaxEnv.shell (Â_i) v n c ε` with
`det vl v ≠ 0`, then `ChainData.shellSubStrip` fails at some `ε`, for any `n c k`, as soon as
`B_i` is finite and `Â_i` is nonempty: go far enough along `v` to leave the strip, then choose
`ε` large enough that the cut does not remove that point.  Via `shellInter_shell_eq` this is
verbatim the `:518` intersection form under the `J−1` reading. -/
theorem not_shellSubStrip_of_transverse_sweep {Bi Ai : Set (ℤ × ℤ)} (hB : Bi.Finite)
    {vl v n : ℤ × ℤ} {c : ℤ} {k : ℕ} (hAne : Ai.Nonempty) (hdet : det vl v ≠ 0) :
    ∃ ε : ℕ, ¬ (shell Ai v n c ε ⊆ {z : ℤ × ℤ | z + (k : ℤ) • vl ∈ Colle35.halfStrip Bi vl}) := by
  obtain ⟨M, hM⟩ := det_bounded_on_halfStrip hB vl
  obtain ⟨g, hg⟩ := hAne
  have hD : 1 ≤ |det vl v| := by
    rcases lt_trichotomy (det vl v) 0 with h | h | h
    · rw [abs_of_neg h]; omega
    · exact absurd h hdet
    · rw [abs_of_pos h]; omega
  set t : ℕ := (M + |det vl g| + 1).toNat with ht
  have htcast : (M + |det vl g| + 1 : ℤ) ≤ (t : ℤ) := by
    rw [ht]
    have : (0 : ℤ) ≤ |det vl g| := abs_nonneg _
    omega
  set w : ℤ × ℤ := g + (t : ℤ) • v with hw
  have hdetw : det vl w = det vl g + (t : ℤ) * det vl v := by
    rw [hw, det_add_right, Nivat.ColleReg.det_smul_right]
  have hbig : M < |det vl w| := by
    have h1 : |(t : ℤ) * det vl v| - |det vl g| ≤ |det vl g + (t : ℤ) * det vl v| := by
      have h := abs_sub_abs_le_abs_sub ((t : ℤ) * det vl v) (-(det vl g))
      rw [abs_neg, sub_neg_eq_add, add_comm] at h
      exact h
    have h2 : |(t : ℤ) * det vl v| = (t : ℤ) * |det vl v| := by
      rw [abs_mul, abs_of_nonneg (Int.natCast_nonneg t)]
    have h3 : (t : ℤ) ≤ (t : ℤ) * |det vl v| := by
      nlinarith [Int.natCast_nonneg t]
    rw [hdetw]
    linarith
  refine ⟨(c - dot n w).toNat, ?_⟩
  intro hsub
  have hlev : c - ((c - dot n w).toNat : ℤ) ≤ dot n w := by
    have : (0 : ℤ) ≤ ((c - dot n w).toNat : ℤ) := Int.natCast_nonneg _
    omega
  have hmem : w ∈ shell Ai v n c ((c - dot n w).toNat) := ⟨g, hg, t, rfl, hlev⟩
  have hstrip := hsub hmem
  have hshift : det vl (w + (k : ℤ) • vl) = det vl w := by
    rw [det_add_right, Nivat.ColleReg.det_smul_right, det_self]; ring
  have := hM _ hstrip
  rw [hshift] at this
  exact absurd this (not_le.mpr hbig)

/-! ### The literal `J+1` reading: a transverse `w` can collapse the intersection

`A := {0}`, `Â_∞^{(1)} := MaxEnv.shell {0} (0,-1) (0,1) 0 1 = {(0,0), (0,-1)}`.  Sweeping `A`
along `w = (1,-1)` gives `{(t,-t)}`, which meets `Â_∞^{(1)}` only at `t = 0`: the intersection
form is `{0} = A`, so `shellProper` fails — while the same data under `w = vJ1 = (0,-1)` is
proper (`(0,-1)` is in and outside `A`).  Raw parameters only; it shows the mechanism the
integrator named ("intersecting with `shellInf ε` can shrink the shell back inside `Ahat i`")
is real, not that it happens on a bundle. -/

theorem shellInter_transverse_collapses :
    shellInter {(0 : ℤ × ℤ)} (shell {(0 : ℤ × ℤ)} ((0 : ℤ), (-1 : ℤ)) ((0 : ℤ), (1 : ℤ)) 0 1)
      ((1 : ℤ), (-1 : ℤ)) ⊆ {(0 : ℤ × ℤ)} := by
  rintro z ⟨⟨g, hg, t, rfl⟩, g', hg', t', heq, hlev⟩
  rw [Set.mem_singleton_iff] at hg hg'
  subst hg hg'
  have h1 := congrArg Prod.fst heq
  have h2 := congrArg Prod.snd heq
  simp at h1 h2
  simp only [dot, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
    Prod.fst_zero, Prod.snd_zero] at hlev
  have ht : t = 0 := by omega
  subst ht
  simp

theorem shellInter_vJ1_proper_example :
    ¬ shellInter {(0 : ℤ × ℤ)} (shell {(0 : ℤ × ℤ)} ((0 : ℤ), (-1 : ℤ)) ((0 : ℤ), (1 : ℤ)) 0 1)
      ((0 : ℤ), (-1 : ℤ)) ⊆ {(0 : ℤ × ℤ)} :=
  not_shellInter_subset (t := 1) rfl ⟨0, rfl, 1, rfl, by simp [dot]⟩ (by simp)

end Inter

/-! ## §6. The box probe: `chainB` climbed with `vJ1 := (-1,0)`, and where it breaks

`chainB` (`Lemma35Wiring.lean:239`) is a complete `ChainData` whose shell is a **box**,
`shell i ε = box (0,0) (1+i+ε, 1)`, with `⋃ Ahat = shellInf ε = strip := {0 ≤ x, 0 ≤ y ≤ 1}`
for every `ε`.  The integrator's hand-read proposal was: extend it to `ChainDataWithShell`
with `vJ1 := (-1,0)`, `nJ := (1,0)`, `cJ := 0`, so that `dot nJ vJ1 = -1 < 0`, and read
`shellInf ε` off `shellInf_eq` as `{-ε ≤ x, 0 ≤ y ≤ 1}`.

**Step 1 (arithmetic): half right.**  `shell_strip_neg_eq` confirms
`MaxEnv.shell strip (-1,0) (1,0) 0 ε = {-ε ≤ x, 0 ≤ y ≤ 1}`.  But `chainB.shellInf` is
**data already fixed** by `chainB` (it is `strip` for every `ε`, `chainB_shellInf_eq_strip`),
so `shellInf_eq` is **false** for `toChainData := chainB` with `vJ1 = (-1,0)`
(`chainB_shellInf_ne_shell_neg`, witness `(-1,0)` at `ε = 1`).  The fix is mechanical:
`chainBNeg` is `chainB` with `shellInf` replaced by the `ε`-dependent band and the two
fields that mention `shellInf` (`shellSubInf`, `shellInfZero`) re-proved; everything else is
inherited verbatim.

**Step 2 (`ChainDataWithShell`): lands.**  `chainBShellNeg`, `dot nJ vJ1 = -1`
(`chainBShellNeg_dot_nJ_vJ1_neg`).  The `-1` is **not** a constraint here: the box's
`shellProper` never looks at `vJ1`, and `shellSubInf` holds for `vJ1 = (-k,0)` with any
`k ≥ 1` (the band only widens).  `not_shell_subset_of_dot_eq_neg_one` (§5) is a fact about
*sweep-shaped* shells and does not bind a box.

**Step 3 (`ChainDataGeom`): dies, and not on the shell.**  A signature fact first: none of
`ChainDataGeom`'s 23 fields (`ChainGeom.lean:66-193`) mentions `shell`; only `bottom`
mentions `shellInf`.  So the box-vs-sweep question is confined to `ChainData`'s seven shell
fields plus `shellInf_eq`, and the climb cannot break on the shape of `shell i ε`.  It breaks
on the shape of **`Â_∞`**: `ChainDataGeom.false_of_ahat_subset_band` proves that **no**
`ChainDataGeom` has `⋃ Ahat` inside a band `{a ≤ dot m · ≤ b}` (`m ≠ 0`) — `rec_p` and
`rec_vJ` force `dot m p = dot m vJ = 0`, hence `det p vJ = 0`, contradicting the
transversality `det_ne_zero_of_dot vJ_ne dot_nJ_vJ dot_nJ_p`.  The strip is such a band
(`m = (0,1)`, `a = 0`, `b = 1`), so `not_chainDataGeom_of_strip`: no `ChainDataGeom`, for any
`p`, `vl`, `η`, `xper`, `S`, `gen`, has `⋃ Ahat = strip` — in particular none extends
`chainBShellNeg` or `chainBShell`, under any choice of `vJ1`, `nJ`, `cJ`.

The named break is therefore the **conjunction** `rec_p ∧ rec_vJ ∧ dot_nJ_p ∧ dot_nJ_vJ ∧
vJ_ne` — the "two semi-infinite edges" of an `(ℓ_ι, ℓ_J)`-region (`b3_colle2.txt:506`) — and
it is independent of the reading of `:518`, of `vJ1`, and of the shell.  `chainB`'s `Â_∞` has
a one-dimensional recession cone; a probe that reaches `ChainDataGeom` needs an `Â_∞` with
two independent recession directions, i.e. a genuine wedge, before any shell question is
even asked. -/

section BoxProbe

open Nivat.MaxEnv Nivat.Colle35

/-- The horizontal strip `{0 ≤ x, 0 ≤ y ≤ 1}`: `⋃ i, chainB.Ahat i`, and `chainB.shellInf ε`
for every `ε`. -/
def strip : Set (ℤ × ℤ) := {z : ℤ × ℤ | 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.2 ≤ 1}

theorem chainB_Ahat_iUnion : (⋃ i : ℕ, chainB.Ahat i) = strip := by
  ext z
  simp only [Set.mem_iUnion, strip, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨i, h1, _, h3, h4⟩
    exact ⟨h1, h3, h4⟩
  · rintro ⟨h1, h3, h4⟩
    have hcast : ((z.1.toNat : ℕ) : ℤ) = z.1 := Int.toNat_of_nonneg h1
    exact ⟨z.1.toNat, h1, by rw [hcast]; omega, h3, h4⟩

theorem chainB_shellInf_eq_strip (ε : ℕ) : chainB.shellInf ε = strip := by
  show (⋃ i : ℕ, box ((0 : ℤ), (0 : ℤ)) (1 + (i : ℤ) + (ε : ℤ), (1 : ℤ))) = strip
  ext z
  simp only [Set.mem_iUnion, strip, Set.mem_ofPred_eq, box]
  constructor
  · rintro ⟨i, h1, _, h3, h4⟩
    exact ⟨h1, h3, h4⟩
  · rintro ⟨h1, h3, h4⟩
    have hcast : ((z.1.toNat : ℕ) : ℤ) = z.1 := Int.toNat_of_nonneg h1
    exact ⟨z.1.toNat, h1, by rw [hcast]; omega, h3, h4⟩

/-- **The integrator's arithmetic, confirmed**: sweeping the strip along `(-1,0)` with the cut
`-ε ≤ x` gives the band `{-ε ≤ x, 0 ≤ y ≤ 1}`. -/
theorem shell_strip_neg_eq (ε : ℕ) :
    shell strip ((-1 : ℤ), (0 : ℤ)) ((1 : ℤ), (0 : ℤ)) 0 ε =
      {z : ℤ × ℤ | -(ε : ℤ) ≤ z.1 ∧ 0 ≤ z.2 ∧ z.2 ≤ 1} := by
  ext z
  constructor
  · rintro ⟨g, ⟨hg1, hg3, hg4⟩, t, rfl, hlev⟩
    simp only [dot, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
      Set.mem_ofPred_eq] at hlev ⊢
    omega
  · rintro ⟨h1, h3, h4⟩
    have hnn : (0 : ℤ) ≤ max z.1 0 - z.1 := by omega
    have hcast : (((max z.1 0 - z.1).toNat : ℕ) : ℤ) = max z.1 0 - z.1 :=
      Int.toNat_of_nonneg hnn
    refine ⟨(max z.1 0, z.2), ⟨le_max_right _ _, h3, h4⟩, (max z.1 0 - z.1).toNat, ?_, ?_⟩
    · refine Prod.ext ?_ ?_ <;> simp [hcast]
    · simp [dot]
      omega

/-- **`shellInf_eq` is false for `chainB` itself with `vJ1 = (-1,0)`**: `chainB.shellInf 1` is
the strip, which does not contain `(-1,0)`. -/
theorem chainB_shellInf_ne_shell_neg :
    chainB.shellInf 1 ≠
      shell (⋃ i, chainB.Ahat i) ((-1 : ℤ), (0 : ℤ)) ((1 : ℤ), (0 : ℤ)) 0 1 := by
  rw [chainB_Ahat_iUnion, shell_strip_neg_eq, chainB_shellInf_eq_strip]
  intro h
  have hm : ((-1 : ℤ), (0 : ℤ)) ∈ strip := by
    rw [h]; exact ⟨by norm_num, le_rfl, by norm_num⟩
  exact absurd hm.1 (by norm_num)

/-- `chainB` with the `ε`-dependent `shellInf` the `(-1,0)` sweep demands.  Only the two
fields mentioning `shellInf` are re-proved. -/
def chainBNeg : ChainData (fun z : ℤ × ℤ => decide ((2 : ℤ) ≤ z.1))
    (fun _ : ℤ × ℤ => false) ((1 : ℤ), (0 : ℤ))
    {((0 : ℤ), (0 : ℤ)), ((1 : ℤ), (0 : ℤ))} ((1 : ℤ), (0 : ℤ)) :=
  { chainB with
    shellInf := fun ε => {z : ℤ × ℤ | -(ε : ℤ) ≤ z.1 ∧ 0 ≤ z.2 ∧ z.2 ≤ 1}
    shellSubInf := by
      intro i ε z hz
      obtain ⟨h1, _, h3, h4⟩ := hz
      simp only at h1 h3 h4
      exact ⟨by omega, h3, h4⟩
    shellInfZero := by
      rintro z ⟨h1, h3, h4⟩
      show z ∈ ⋃ i, chainB.Ahat i
      rw [chainB_Ahat_iUnion]
      exact ⟨by simpa using h1, h3, h4⟩ }

theorem chainBNeg_Ahat_iUnion : (⋃ i : ℕ, chainBNeg.Ahat i) = strip := chainB_Ahat_iUnion

/-- **`chainB` climbs to `ChainDataWithShell` with the sign the geometry wants.** -/
def chainBShellNeg : ChainDataWithShell (fun z : ℤ × ℤ => decide ((2 : ℤ) ≤ z.1))
    (fun _ : ℤ × ℤ => false) ((1 : ℤ), (0 : ℤ))
    {((0 : ℤ), (0 : ℤ)), ((1 : ℤ), (0 : ℤ))} ((1 : ℤ), (0 : ℤ)) where
  toChainData := chainBNeg
  vJ1 := ((-1 : ℤ), (0 : ℤ))
  nJ := ((1 : ℤ), (0 : ℤ))
  cJ := 0
  shellInf_eq := by
    intro ε
    show {z : ℤ × ℤ | -(ε : ℤ) ≤ z.1 ∧ 0 ≤ z.2 ∧ z.2 ≤ 1} =
      shell (⋃ i, chainB.Ahat i) ((-1 : ℤ), (0 : ℤ)) ((1 : ℤ), (0 : ℤ)) 0 ε
    rw [chainB_Ahat_iUnion, shell_strip_neg_eq]
  ahat_nonempty := by
    show (⋃ i, chainB.Ahat i).Nonempty
    rw [chainB_Ahat_iUnion]
    exact ⟨((0 : ℤ), (0 : ℤ)), le_rfl, le_rfl, by norm_num⟩
  ahat_halfPlane := by
    show ∀ g ∈ ⋃ i, chainB.Ahat i, (0 : ℤ) ≤ dot ((1 : ℤ), (0 : ℤ)) g
    rw [chainB_Ahat_iUnion]
    rintro g ⟨h1, -, -⟩
    simp only [dot]
    omega

theorem chainBShellNeg_dot_nJ_vJ1_neg : dot chainBShellNeg.nJ chainBShellNeg.vJ1 = -1 := by
  decide

/-- **No `ChainDataGeom` has `Â_∞` inside a band.**  `rec_p` and `rec_vJ` push a point of
`Â_∞` arbitrarily far along `p` and along `vJ`, so both are `dot m`-null; then
`det p vJ = 0` (`det_eq_zero_of_dot_eq_zero`), against `det_ne_zero_of_dot vJ_ne dot_nJ_vJ
dot_nJ_p`.  Uses nothing about `shell`, `shellInf`, `vJ1` or the reading of `:518`. -/
theorem ChainDataGeom.false_of_ahat_subset_band {α : Type*} {η xper : Config α}
    {vl p gen : ℤ × ℤ} {S : Finset (ℤ × ℤ)} (cg : ChainDataGeom η xper vl p S gen)
    {m : ℤ × ℤ} (hm : m ≠ 0) {a b : ℤ}
    (hband : ∀ g ∈ ⋃ i, cg.toChainData.Ahat i, a ≤ dot m g ∧ dot m g ≤ b) : False := by
  obtain ⟨g, hg⟩ := cg.ahat_nonempty
  have hdir : ∀ d : ℤ × ℤ,
      (∀ g ∈ ⋃ i, cg.toChainData.Ahat i, g + d ∈ ⋃ i, cg.toChainData.Ahat i) →
      dot m d = 0 := by
    intro d hd
    by_contra hne
    have hk : ∀ k : ℕ, a ≤ dot m g + (k : ℤ) * dot m d ∧ dot m g + (k : ℤ) * dot m d ≤ b := by
      intro k
      have := hband _ (Nivat.ColleReg.ray_of_recession hd hg k)
      rwa [dot_add, Nivat.ColleReg.dot_zsmul_right] at this
    set k : ℕ := (b - a + 1).toNat with hk_def
    have hkge : b - a + 1 ≤ (k : ℤ) := Int.self_le_toNat _
    have hk0 : (0 : ℤ) ≤ (k : ℤ) := Int.natCast_nonneg k
    obtain ⟨hlo, hhi⟩ := hk k
    obtain ⟨hlo0, hhi0⟩ := hband g hg
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · have : (k : ℤ) * dot m d ≤ -(k : ℤ) := by nlinarith
      omega
    · have : (k : ℤ) ≤ (k : ℤ) * dot m d := by nlinarith
      omega
  have hp : dot m p = 0 := hdir p cg.rec_p
  have hv : dot m cg.vJ = 0 := hdir cg.vJ cg.rec_vJ
  exact Nivat.ColleReg.det_ne_zero_of_dot cg.vJ_ne cg.dot_nJ_vJ cg.dot_nJ_p
    (det_eq_zero_of_dot_eq_zero hm hp hv)

/-- **The box probe cannot reach `ChainDataGeom`**: the strip is a band. -/
theorem not_chainDataGeom_of_strip {α : Type*} {η xper : Config α}
    {vl p gen : ℤ × ℤ} {S : Finset (ℤ × ℤ)} (cg : ChainDataGeom η xper vl p S gen)
    (h : (⋃ i, cg.toChainData.Ahat i) = strip) : False :=
  ChainDataGeom.false_of_ahat_subset_band cg (m := ((0 : ℤ), (1 : ℤ))) (by decide) (a := 0) (b := 1) (by
    rw [h]
    rintro g ⟨-, h3, h4⟩
    simp only [dot]
    omega)

/-- In particular no `ChainDataGeom` extends `chainBShellNeg` (nor any other
`ChainDataWithShell` over `chainB`/`chainBNeg`), for any `p`. -/
theorem not_chainDataGeom_over_chainBNeg {p : ℤ × ℤ}
    (cg : ChainDataGeom (fun z : ℤ × ℤ => decide ((2 : ℤ) ≤ z.1))
      (fun _ : ℤ × ℤ => false) ((1 : ℤ), (0 : ℤ)) p
      {((0 : ℤ), (0 : ℤ)), ((1 : ℤ), (0 : ℤ))} ((1 : ℤ), (0 : ℤ)))
    (h : cg.toChainData.Ahat = chainBNeg.Ahat) : False :=
  not_chainDataGeom_of_strip cg (by rw [h]; exact chainBNeg_Ahat_iUnion)

end BoxProbe

/-! ## §7. Is the box's `shellEnv` genuine, and what does `bottom` really demand?

**Two questions, both kernel-settled, both about which layer of the 46 obligations is
shape-sensitive.**

### 7.1 `chainB` discharges `shellEnv` genuinely — for `Env := EnvOf sq1`, and only for that.

`chainB.shellEnv` (`Lemma35Wiring.lean:323`) is `envOf_sq1_box` at every `i` and every `ε`
(`chainB_shellEnv_all` below, stronger than the `∃ ε i₀` the field asks for).  It is not
vacuous: `chainB.Env = EnvOf sq1 = Enveloped sq1` (`chainB_Env_eq`, by `rfl`), which refuses the
singleton `{0}` (`chainB_env_restrictive`, already in the build), and `Enveloped` is Collé's
Definition 3.2 verbatim (`LatticeEdges.lean:628`: lattice-convex, `E T ⊆ E U`, faces at least as
long, `|E T| = |E U|`).  So the integrator's reading is right at the level it was made:
**a box shell passes `shellEnv`.**

But the reason it passes is `E (box p q) = E sq1` (`E_box`, `E_sq1`), and that cuts both ways:

* `enveloped_box_E_eq`: `Enveloped U (box p q)` **forces** `E U = {(1,0),(-1,0),(0,1),(0,-1)}`
  (`Enveloped.E_eq`, one line).  A box is `E(U)`-enveloped for exactly one edge-normal set.
* `not_envOf_S_chainB_shell`: under the pin `exists_chainData` actually imposes
  (`RegionSteps.lean:825`, `Env = EnvOf ↑d.Sphi`), with `chainB`'s **own** `S = {(0,0),(1,0)}`,
  every `chainB.shell i ε` is **not** enveloped — `E ↑S = {(0,1),(0,-1)}` has two normals, the box
  has four.  (`envB`/`envA` fail the same way; `chainB` only stands because its `Env` was chosen
  to match its boxes, not its `S`.)
* `DecompData.not_enveloped_box_of_off_axis_normal`: on the real `S_φ` of a `DecompData`, one
  generator `h i` off both axes already kills every box (the primitive normal to `h i` is in
  `E ↑d.Sphi` by `mem_E_Sphi_of_dot_eq_zero` and is not an axis normal).

**So the honest form of "the box did not fail" is: a box passes `shellEnv` iff `E(S_φ)` is the
four axis normals, i.e. (hand-read, not kernel) `m = 2` with axis-parallel generators — and up to
a unimodular change of basis, `m = 2` in general, with "box" read as "parallelogram".**
For `m ≥ 3` the shell must carry all `2m` edge normals, which is `LEAF-A.md`'s "`E T = E U`
exactly" criterion, and no box does.  `shellEnv` is therefore not gone; what is gone is the
assumption that its witness is a sweep.  The four sweep deaths and the box's survival have one
cause: **`shellEnv` is a statement about the edge-normal set of the shell**, nothing else.

### 7.2 `bottom` forces `a = a'` on every `ChainDataGeom`.

⚠ **Status 2026-09-19: retired shape — twice over.**  Everything in 7.2 was proved against the
*unguarded* conjunct (iv) of `bottom`.  That conjunct was first *guarded* by
`1 ≤ dot nJ (b - a')` (the ruling recorded here earlier that day) and then, the same day,
**deleted outright** from `ChainGeom.lean`: (iv) is derivable from (iii) wherever the sweep
reads it (`Colle37Geom.run_of_face` + `gen_of_line_late`, `ShellGeom.lean`), and the guarded
form was still false on Collé's own `m = 2` shape (`tmp/Abottom_noIV.lean`,
`not_guardedIV_quad_sq1`; receipt, not landed).  The field now has **four** conjuncts.  The
theorems below take the retired five-conjunct shape as the explicit hypothesis
`hold : ChainDataGeom.RetiredBottom cg` (§14: the record stays, its status changes), so they
still elaborate and still say what they said; they no longer read `cg.bottom` at all, so their
continued compilation says nothing about the live field.  Read every "every `ChainDataGeom`"
in 7.2 as "every `ChainDataGeom` satisfying `RetiredBottom`"; `cgwA` (§9) is a `ChainDataGeom`
with `a ≠ a'` and `¬ RetiredBottom`.

Walking the wedge probe (`Â_∞` = quadrant, box `Ahat i`, box shell, `S` with a genuine `ℓ_J`-edge
so that `a ≠ a'`) into `ChainDataGeom` field by field, the first break is `bottom` conjunct (iv)
(`ChainGeom.lean:104-105`), and it is not a property of the wedge.  In the kernel:

`ChainDataGeom.a_eq_a'`: **every** bundle has `a = a'`.  Proof: if `a ≠ a'`, then `a'` sits on
`a`'s `(-n_J)`-level (`a_mem_face_negNJ` / `a'_mem_face_negNJ`, `FaceDistinct.lean:61,73`), so
`edge` puts `a' = a + j • v_J` with `1 ≤ j`.  Take `bottom 0 = ⟨z₀, L, …⟩`.  Conjunct (iv) at
`b := a`, `k := L` says `z₀ + (L - j) • v_J ∈ reachSet Â_∞ v_{J−1}`; that point has
`⟪n_J, ·⟫ = c_J - 1` (`dot_nJ_vJ`), so by `shellInf_eq` it lies in `shellInf 1` and not in
`shellInf 0`; conjunct (v) then writes it as `z₀ + k • v_J` with `L ≤ k`, and `v_J ≠ 0` gives
`k = L - j < L`.  Fields used: `lex`, `lex'`, `edge`, `dot_nJ_vJ`, `bottom`, `vJ_ne`,
`shellInf_eq`.  Not used: anything about `shell`, `Env`, `p`, or the shape of `Â_∞`.

Consequences (kernel where marked; all under `hold : RetiredBottom cg`):

* (derivable, **not written**) the `(-n_J)`-face of `S` has at most one lattice point — one line
  from `a_eq_a'` through `a_ne_a'_iff_face_nontrivial`.  No declaration by that name exists;
  an earlier version of this list called it `face_negNJ_subsingleton` as if it were kernel.
  Nothing is concluded about the number `r`: the
  bundle never states `a' = a + r • vJ`, so `r` is unconstrained by `a = a'`.
* `ChainDataGeom.negNJ_not_mem_E` (kernel): `-n_J ∉ E ↑S` (via `a_ne_a'_iff_negNJ_mem_E`).
* `ChainDataGeom.not_dot_h_eq_zero` (kernel): at the real call site `S = d.Sphi`, **no**
  decomposition period is orthogonal to `n_J` (via `a_ne_a'_of_dot_h_eq_zero`).  But `ℓ_J` is by
  definition one of the `ℓ_1, …, ℓ_m`, i.e. `n_J ⊥ h_J` (`b3_colle2.txt:506`: "the other one is
  parallel to `ℓ_J`").  So any bundle satisfying the retired shape has a one-point `ℓ_J`-face
  and is **not Collé's region** — `exists_chainData` was not thereby refutable (`n_J` is a
  field of its existential, unpinned), it would just have produced the wrong object.
  `bottom` (iv) and `edge` together contradicted `OPEN.md` #7's `a ≠ a'` — which
  was proved *conditionally* on `dot n_J (h i) = 0`, exactly the hypothesis this shows no
  retired-shape bundle can have.  With (iv) deleted, `a_ne_a'_of_dot_h_eq_zero`
  (`FaceDistinct.lean:174`) is usable again.

What this says about the transcription (reading, not kernel): conjunct (iv) translates the new
layer's half-line by `S - a'`, and `a - a' = -r • v_J` is a translate *against* the half-line.
The paper's absorption (`b3_colle2.txt:440`, region + `E(S_φ)`-enveloped) needs the translates
that point *into* the region, which is one endpoint's worth, not both.  Which endpoint is a
sign/orientation question for the definition audit, not for this lane; what this lane can say
is that with both, `r = 0` is forced, and with `r = 0` the `-n_J`-edge of `S_φ` is a vertex,
which is not Collé's `ℓ_J`.  `cgw` (`Step_PeriodsRays2.lean:233`), the only full
`ChainDataGeom` in the tree, has `Sw = {0}`, `a = a' = 0`, `r = 0` — consistent with this, and
now explained by it rather than by its degeneracy.

**Scope:** this is a refutation of the *bundle's* joint satisfiability with `a ≠ a'`, not of any
sentence of Collé.  `exists_chainData` (`RegionSteps.lean:811`) still quantifies over the given
`d.Sphi` and `ξ`; the theorem below says its output can never have `n_J` among the decomposition
normals, which is a fact about the signature, not progress on the `sorry`.  The wedge-and-box
climb itself was not landed: with `a = a'` forced there is nothing to climb that `cgw` has not
already climbed, and the `Env := EnvOf sq1` upgrade of `cgw` is the degenerate-`S` case §7.1
shows to be off the real call site anyway. -/

section BottomForcesDegenerateFace

open Nivat.MaxEnv Nivat.Colle35

/-- `chainB.Env` is Definition 3.2 at `U = sq1`, by definition. -/
theorem chainB_Env_eq : chainB.Env = EnvOf sq1 := rfl

/-- **`chainB` discharges `shellEnv` at every `i` and every `ε`**, not just the `∃ ε i₀` the
field asks for, and the discharge is `envOf_sq1_box`, i.e. genuine Definition 3.2 content
(lattice convexity, `E (box) = E sq1`, every face at least two points). -/
theorem chainB_shellEnv_all (i ε : ℕ) : chainB.Env (chainB.shell i ε) := by
  show EnvOf sq1 (box ((0 : ℤ), (0 : ℤ)) (1 + (i : ℤ) + (ε : ℤ), (1 : ℤ)))
  exact Colle35.envOf_sq1_box (by show (0 : ℤ) < 1 + (i : ℤ) + (ε : ℤ); omega) (by norm_num)

/-- **A box is `E(U)`-enveloped only if `E U` is the four axis normals.** One line from
`Enveloped.E_eq` and `E_box`; this is the whole reason `chainB`'s boxes pass `shellEnv` for
`U = sq1`, and the whole reason they cannot pass it for any `U` with another edge normal. -/
theorem enveloped_box_E_eq {U : Set (ℤ × ℤ)} (hU : (E U).Finite) {p q : ℤ × ℤ}
    (hp : p.1 < q.1) (hq : p.2 < q.2) (h : Enveloped U (box p q)) :
    E U = {((1 : ℤ), (0 : ℤ)), ((-1 : ℤ), (0 : ℤ)), ((0 : ℤ), (1 : ℤ)), ((0 : ℤ), (-1 : ℤ))} := by
  rw [← h.E_eq hU, E_box hp hq]

/-- Any edge normal of `U` off both axes kills every non-degenerate box. -/
theorem not_enveloped_box_of_off_axis {U : Set (ℤ × ℤ)} (hU : (E U).Finite) {n : ℤ × ℤ}
    (hn : n ∈ E U) (hoff : n.1 ≠ 0 ∧ n.2 ≠ 0) {p q : ℤ × ℤ} (hp : p.1 < q.1) (hq : p.2 < q.2) :
    ¬ Enveloped U (box p q) := by
  intro h
  rw [enveloped_box_E_eq hU hp hq h] at hn
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
  rcases hn with rfl | rfl | rfl | rfl <;> simp at hoff

/-- `chainB`'s own window, as a set, is the horizontal unit segment. -/
theorem coe_chainB_S :
    ((({((0 : ℤ), (0 : ℤ)), ((1 : ℤ), (0 : ℤ))} : Finset (ℤ × ℤ))) : Set (ℤ × ℤ)) =
      segOf ((1 : ℤ), (0 : ℤ)) := by
  ext z; simp [segOf, Prod.ext_iff]

/-- **Under the pin `Env = EnvOf ↑S` that `exists_chainData` imposes, `chainB`'s shell is NOT
enveloped** — for `chainB`'s own `S`.  `E ↑S = {(0,1),(0,-1)}` (`E_segOf_horizontal`) has two
normals; the box has four.  So `chainB` passes `shellEnv` only because its `Env` was chosen to
match its boxes rather than its `S`. -/
theorem not_envOf_S_chainB_shell (i ε : ℕ) :
    ¬ EnvOf ((({((0 : ℤ), (0 : ℤ)), ((1 : ℤ), (0 : ℤ))} : Finset (ℤ × ℤ))) : Set (ℤ × ℤ))
      (chainB.shell i ε) := by
  rw [coe_chainB_S]
  show ¬ Enveloped (segOf ((1 : ℤ), (0 : ℤ))) (box ((0 : ℤ), (0 : ℤ)) (1 + (i : ℤ) + (ε : ℤ), (1 : ℤ)))
  intro h
  have hE := enveloped_box_E_eq (finite_E_of_finite (finite_segOf _))
    (by show (0 : ℤ) < 1 + (i : ℤ) + (ε : ℤ); omega) (by norm_num) h
  rw [E_segOf_horizontal] at hE
  have hmem : ((1 : ℤ), (0 : ℤ)) ∈ ({((0 : ℤ), (1 : ℤ)), ((0 : ℤ), (-1 : ℤ))} : Set (ℤ × ℤ)) := by
    rw [hE]; simp
  simp at hmem

/-- **On the real `S_φ`, one generator off both axes kills every box.**  The primitive normal
`n` to `h i` is an edge normal of `S_φ` (`DecompData.mem_E_Sphi_of_dot_eq_zero`,
`FaceDistinct.lean:146`), and it is off-axis exactly when `h i` is. -/
theorem DecompData.not_enveloped_box_of_off_axis_normal {α : Type*} [AddCommMonoid α]
    {η : Config α} (d : DecompData η) {n : ℤ × ℤ} (hprim : Prim n) (i : Fin d.m)
    (hdot : dot n (d.h i) = 0) (hoff : n.1 ≠ 0 ∧ n.2 ≠ 0) {p q : ℤ × ℤ}
    (hp : p.1 < q.1) (hq : p.2 < q.2) :
    ¬ Enveloped (↑d.Sphi : Set (ℤ × ℤ)) (box p q) :=
  not_enveloped_box_of_off_axis (finite_E_of_finite (Finset.finite_toSet _))
    (d.mem_E_Sphi_of_dot_eq_zero hprim i hdot) hoff hp hq

/-- **The retired shape of `bottom` (status: retired 2026-09-19, kept per §14).**  This is
`ChainDataGeom.bottom` as it stood before any repair: five conjuncts, with (iv) *unguarded*,
i.e. the translate `b - a'` demanded for every `b ∈ S`, on-face points included.  The live
field (`ChainGeom.lean`) has since dropped (iv) altogether (after a one-day interlude in which
it was guarded by `1 ≤ dot nJ (b - a')`); the three theorems below are the kernel's record of
*why* — they are stated against this predicate so that they still elaborate and still say
exactly what they said when they forced the repair. -/
def ChainDataGeom.RetiredBottom {α : Type*} {η xper : Config α} {vl p : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} {gen : ℤ × ℤ} (cg : ChainDataGeom η xper vl p S gen) : Prop :=
  ∀ ε : ℕ, ∃ (z₀ : ℤ × ℤ) (L : ℤ),
    dot cg.nJ z₀ = cg.cJ - (ε : ℤ) - 1 ∧
    (∀ k : ℤ, L ≤ k → z₀ + k • cg.vJ ∈ reachSet (⋃ i, cg.toChainData.Ahat i) cg.vJ1) ∧
    (∀ b ∈ S, ∀ k : ℤ, L ≤ k →
      z₀ + k • cg.vJ + (b - cg.a) ∈ reachSet (⋃ i, cg.toChainData.Ahat i) cg.vJ1) ∧
    (∀ b ∈ S, ∀ k : ℤ, L ≤ k →
      z₀ + k • cg.vJ + (b - cg.a') ∈ reachSet (⋃ i, cg.toChainData.Ahat i) cg.vJ1) ∧
    (∀ z ∈ cg.toChainData.shellInf (ε + 1),
      z ∈ cg.toChainData.shellInf ε ∨ ∃ k : ℤ, L ≤ k ∧ z = z₀ + k • cg.vJ)

/-- The live field is implied by the retired one (deleting a conjunct only drops instances).
Until 2026-09-19 this produced the *guarded* five-conjunct shape; it now produces the
four-conjunct field verbatim. -/
theorem ChainDataGeom.bottom_of_retiredBottom {α : Type*} {η xper : Config α} {vl p : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} {gen : ℤ × ℤ} (cg : ChainDataGeom η xper vl p S gen)
    (hold : ChainDataGeom.RetiredBottom cg) (ε : ℕ) :
    ∃ (z₀ : ℤ × ℤ) (L : ℤ),
      dot cg.nJ z₀ = cg.cJ - (ε : ℤ) - 1 ∧
      (∀ k : ℤ, L ≤ k → z₀ + k • cg.vJ ∈ reachSet (⋃ i, cg.toChainData.Ahat i) cg.vJ1) ∧
      (∀ b ∈ S, ∀ k : ℤ, L ≤ k →
        z₀ + k • cg.vJ + (b - cg.a) ∈ reachSet (⋃ i, cg.toChainData.Ahat i) cg.vJ1) ∧
      (∀ z ∈ cg.toChainData.shellInf (ε + 1),
        z ∈ cg.toChainData.shellInf ε ∨ ∃ k : ℤ, L ≤ k ∧ z = z₀ + k • cg.vJ) := by
  obtain ⟨z₀, L, hdz, hline, hstab, -, hsplit⟩ := hold ε
  exact ⟨z₀, L, hdz, hline, hstab, hsplit⟩

/-- **The retired `bottom` forces `a = a'` on every `ChainDataGeom`.**
(Status: archival since 2026-09-19 — the hypothesis `hold` is the *retired* shape; the live
field no longer supplies it (conjunct (iv) deleted), and `cgwA` below is a `ChainDataGeom`
with `a ≠ a'`.  ⚠ This theorem does not read `cg.bottom`, so its compiling after the deletion
is not evidence about the live field; `cgwA_a_ne_a'` is.)
See §7.2 above for the argument; fields used are `lex`, `lex'` (through `FaceDistinct`),
`edge`, `dot_nJ_vJ`, `vJ_ne`, `shellInf_eq`, plus `hold`.  Nothing about `shell`, `Env`, `p`,
or the shape of `Â_∞` enters. -/
theorem ChainDataGeom.a_eq_a' {α : Type*} {η xper : Config α} {vl p : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} {gen : ℤ × ℤ} (cg : ChainDataGeom η xper vl p S gen)
    (hold : ChainDataGeom.RetiredBottom cg) :
    cg.a = cg.a' := by
  by_contra hne
  -- `a'` is on `a`'s `(-n_J)`-level, so `edge` puts it at `a + j • v_J`, `1 ≤ j`.
  have hlevel : dot (-cg.nJ) cg.a = dot (-cg.nJ) cg.a' :=
    dot_eq_of_mem_face cg.a_mem_face_negNJ cg.a'_mem_face_negNJ
  rw [dot_neg_left, dot_neg_left] at hlevel
  have hdot0 : ¬ (1 ≤ dot cg.nJ (cg.a' - cg.a)) := by
    rw [dot_sub]; omega
  obtain ⟨j, hj1, -, hj⟩ :=
    (cg.edge cg.a' (Finset.mem_erase.mpr ⟨Ne.symm hne, cg.a'_mem⟩)).resolve_right hdot0
  -- retired `bottom 0`.
  obtain ⟨z₀, L, hdz, -, -, hstab', hsplit⟩ := hold 0
  -- Conjunct (iv) at `b := a`, `k := L`: the point `z₀ + (L - j) • v_J` is reached.
  have hw : z₀ + (L - (j : ℤ)) • cg.vJ ∈ reachSet (⋃ i, cg.toChainData.Ahat i) cg.vJ1 := by
    have h := hstab' cg.a cg.a_mem L le_rfl
    have he : z₀ + L • cg.vJ + (cg.a - cg.a') = z₀ + (L - (j : ℤ)) • cg.vJ := by
      rw [hj, sub_add_cancel_left, sub_smul]; abel
    rwa [he] at h
  -- Its `n_J`-level is `c_J - 1`.
  have hdw : dot cg.nJ (z₀ + (L - (j : ℤ)) • cg.vJ) = cg.cJ - 1 := by
    rw [dot_add, Nivat.ColleReg.dot_zsmul_right, cg.dot_nJ_vJ, hdz]; push_cast; ring
  -- So it is in `shellInf 1` …
  have hw1 : z₀ + (L - (j : ℤ)) • cg.vJ ∈ cg.toChainData.shellInf (0 + 1) := by
    rw [cg.shellInf_eq]
    obtain ⟨g, hg, t, hgt⟩ := hw
    exact ⟨g, hg, t, hgt, by rw [hdw]; push_cast; omega⟩
  -- … and conjunct (v) must place it on the half-line, at some `k ≥ L`.
  rcases hsplit _ hw1 with h0 | ⟨k, hk, hwk⟩
  · -- but not in `shellInf 0`, whose level is `≥ c_J`.
    rw [cg.shellInf_eq] at h0
    have := shell_subset_halfPlaneGE h0
    change cg.cJ - ((0 : ℕ) : ℤ) ≤ dot cg.nJ _ at this
    rw [hdw] at this
    push_cast at this
    omega
  · -- `(L - j) • v_J = k • v_J` with `v_J ≠ 0` gives `k = L - j < L`.
    have hsm : (L - (j : ℤ) - k) • cg.vJ = 0 := by
      rw [sub_smul, sub_eq_zero]
      exact add_left_cancel hwk
    rcases smul_eq_zero.mp hsm with h | h
    · omega
    · exact cg.vJ_ne h

/-- (Status: archival, retired shape.)  Under the retired `bottom`, the `(-n_J)`-face of the
window is a single point: `-n_J` is **not** an edge normal of `S`
(`a_ne_a'_iff_negNJ_mem_E`, `FaceDistinct.lean:125`). -/
theorem ChainDataGeom.negNJ_not_mem_E {α : Type*} {η xper : Config α} {vl p : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} {gen : ℤ × ℤ} (cg : ChainDataGeom η xper vl p S gen)
    (hold : ChainDataGeom.RetiredBottom cg) :
    -cg.nJ ∉ E (↑S : Set (ℤ × ℤ)) :=
  fun h => cg.a_ne_a'_iff_negNJ_mem_E.mpr h (ChainDataGeom.a_eq_a' cg hold)

/-- (Status: archival, retired shape.)  **Under the retired `bottom`, at the real call site no
decomposition period is orthogonal to `n_J`.**  This is the contrapositive of
`a_ne_a'_of_dot_h_eq_zero` (`FaceDistinct.lean:174`, `OPEN.md` #7) through `a_eq_a'`.  Collé's
`ℓ_J` is one of the `ℓ_1, …, ℓ_m` (`b3_colle2.txt:506`), so under the retired shape any bundle
that could exist had a one-point `ℓ_J`-face and was not the `(ℓ, ℓ_J)`-region Collé constructs.
That is what forced the repair; with (iv) deleted from the field, `a_ne_a'_of_dot_h_eq_zero`
is usable again. -/
theorem ChainDataGeom.not_dot_h_eq_zero {α : Type*} [AddCommMonoid α] {η xper : Config α}
    {vl p gen : ℤ × ℤ} (d : DecompData η) (cg : ChainDataGeom η xper vl p d.Sphi gen)
    (hold : ChainDataGeom.RetiredBottom cg) (i : Fin d.m) : dot cg.nJ (d.h i) ≠ 0 :=
  fun h => ChainDataGeom.a_ne_a'_of_dot_h_eq_zero d cg i h (ChainDataGeom.a_eq_a' cg hold)

end BottomForcesDegenerateFace

/-! ## §8. The wedge-and-box probe under the `Env` pin: it dies at the pin, not at the wedge

⚠ **Status 2026-09-19: the break named here was `bottom` (iv) in its retired, unguarded form.**
The two theorems of §8.2 now take `hold : ChainDataGeom.RetiredBottom cg` and are archival; with
(iv) deleted from the field the probe's `bottom` no longer fails at `b = (0,0)` (that is
`cgwA`, §9), and the question whether a box shell survives the `Env` pin is **reopened**, not
settled.

**Probe, not a solution.**  The data were `cgw`'s (`Step_PeriodsRays2.lean:233`): `Â_∞ = Qs`
(the closed first quadrant), `p = (0,1)`, `v_J = (1,0)`, `n_J = (0,1)`, `c_J = 0`,
`v_{J-1} = v_ℓ = (0,-1)`, with the two upgrades the integrator asked for — a genuine
`Env := EnvOf sq1` in place of `fun _ => True`, and box-shaped `Â_i`, `Â_i^{(ε)}` throughout.

### 8.1 Hand-read climb (reading, not kernel; nothing below this line is a `def`)

* `Â_i := box (0,0) (i+1, i+1)`, not `cgw`'s `Ah i` — `Ah 0 = {0}` is a degenerate box and
  `EnvOf sq1 {0}` is false (`chainB_env_restrictive`, `Lemma35Wiring.lean:377`), so `envA 0`
  would fail on the first field.  With the `+1`, `envB`/`envA`/`shellEnv` are `envOf_sq1_box` at
  every `i`, `ε`, exactly as for `chainB`.  `maximalHat` is `cgw`'s wall argument unchanged (the
  `Env Tset` hypothesis is never used).  `fill` needs a genuine row-by-row filtration once
  `S.erase gen ≠ ∅`; the diagonal potential `x - y` works for `gen = (1,0)`.  All 19 pass.
* `ChainDataWithShell`: `shellInf ε = {0 ≤ x, -ε ≤ y}` is `cgw`'s `shellInf_eq` verbatim.  Passes.
* `ChainDataGeom`, first the pin.  `exists_chainData` (`RegionSteps.lean:825`) requires
  `Env = EnvOf ↑S`, so `Env := EnvOf sq1` forces `S := {(0,0),(1,0),(0,1),(1,1)}` (or any `S`
  with the same `E`, §7.1).  Then the `(-n_J) = (0,-1)`-face of `S` is `{(0,0),(1,0)}`, so
  `lex`/`lex'`/`edge`/`edge'` are all satisfiable with `a = (0,0)`, `a' = (1,0)`, `r = 1` —
  and `bottom` conjunct (iv) fails at `b = (0,0)`, `k = L`, precisely as
  `ChainDataGeom.a_eq_a'` says it must.  **First break: `bottom` (iv), through the pin.**
  Without the pin (`cgw`'s `Sw = {0}`) every field passes; the probe is `cgw` again.

### 8.2 What the kernel says (below): the break is not this wedge's, and not this box's

`ChainDataGeom.false_of_envOf_S_boxA`: **no** `ChainDataGeom` has `Env = EnvOf ↑S` together with
non-degenerate boxes for its `A i`.  The proof has two halves, and the second is the new one:

* `nJ_off_axis_of_E_eq`: if `E ↑S` is the four axis normals (which one enveloped box forces,
  `enveloped_box_E_eq`), then `n_J` is **off both axes** — because `-n_J ∉ E ↑S`
  (`negNJ_not_mem_E`, i.e. `a = a'`) and a primitive axis vector is `±(1,0)`, `±(0,1)`.  So
  under the pin, a box shell does not merely tolerate `ℓ_J`: it forces `ℓ_J` to be *diagonal*
  to the box.  That is the integrator's "shape pinned by `S_φ`", one level sharper: the shell's
  edge normals are `E(S_φ)`, and `ℓ_J`'s normal is **not** among them.
* `vJ_off_axis` then makes `v_J` off-axis too (`dot_nJ_vJ`, `vJ_ne`).  Now `Â_∞ = ⋃ Â_i` is a
  nested union of boxes (`AhatMono`, `AhatEq` + `preimage_add_box`), so with `g ∈ Â_∞` and
  `g + t • v_J ∈ Â_∞` (`rec_vJ`, iterated) the two *corners* `(g.1 + t v_J.1, g.2)` and
  `(g.1, g.2 + t v_J.2)` are in the same box, hence in `Â_∞`.  `dot n_J` of the corners is
  `dot n_J g + t • (n_J.1 v_J.1)` and `dot n_J g + t • (n_J.2 v_J.2)`; the two products sum to
  zero and are nonzero, so one is `≤ -1`, and `ahat_halfPlane` fails at
  `t = dot n_J g - c_J + 1`.

Fields used: `envA`, `AhatEq`, `AhatMono`, `ahat_nonempty`, `ahat_halfPlane`, `rec_vJ`,
`dot_nJ_vJ`, `vJ_ne`, `nJ_prim`, and `a = a'` (hence `bottom`, `lex`, `lex'`, `edge`,
`shellInf_eq`).  Not used: `shell`, `shellEnv`, `p`, `rec_p`, the shape of `Â_∞` beyond
"nested union of boxes".

**Which `Env` was `shellEnv` discharged against, and is the argument `sq1`-specific?**
`envOf_sq1_box` is `sq1`-specific in exactly one place — `E (box p q) = E sq1` — and §7.1
shows that place is the whole content: a box is `E(U)`-enveloped iff `E U` is the axis set.  So
for the wedge probe, `shellEnv` is discharged against `EnvOf sq1` and only against `EnvOf U` with
`E U = E sq1`; under the pin that is `E(S_φ) = E sq1`, and 8.2 then kills the bundle anyway.
The `shellEnv` field and the `Env` pin were **never both satisfied by a box** except in `chainB`,
whose `Env` is not `EnvOf` of its own `S` (`not_envOf_S_chainB_shell`).

**Reading of the result (not kernel):** the constraint is the *nested-boxes* shape of `Â_∞`,
which is what `Env := EnvOf (axis-normal S)` forces on the `A i`.  A region with two
semi-infinite edges in the *non-axis* directions `p` and `v_J` (Collé's `(ℓ, ℓ_J)`-region) has
`A i` whose `E` contains the normals of `p` and `v_J`, so under the pin `E(S_φ)` must contain them
too — i.e. `S_φ` must have edges parallel to `ℓ` and `ℓ_J`, which is Collé's setup (`ℓ_J` is one
of the `ℓ_1, …, ℓ_m`).  But then `-n_J ∈ E(S_φ)` and `negNJ_not_mem_E` kills it.  So under the
current transcription of `bottom`, the pin `Env = EnvOf ↑d.Sphi` is unsatisfiable by **any**
region whose `A i` carry an `ℓ_J`-parallel edge — not just by boxes.  The kernel form of that
general statement needs `E (A i) ∋ ±n_J` from a geometric description of `A i`, which this lane
did not build; the box case is the one where `E (A i)` is known in closed form. -/

section WedgePin

open Nivat.MaxEnv Nivat.Colle35

/-- Translating a box: `{z | z + w ∈ box p q} = box (p - w) (q - w)`. -/
theorem preimage_add_box (w p q : ℤ × ℤ) :
    {z : ℤ × ℤ | z + w ∈ box p q} = box (p - w) (q - w) := by
  ext z
  simp only [Set.mem_ofPred_eq, mem_box, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]
  omega

/-- (Status: archival, retired shape.)  **Under `E ↑S = {axis normals}` and the retired
`bottom`, `n_J` is off both axes.**  `-n_J ∉ E ↑S` (`negNJ_not_mem_E`, from `a = a'`), and a
primitive vector with a zero coordinate is `±(1,0)` or `±(0,1)`, whose negatives are all axis
normals. -/
theorem ChainDataGeom.nJ_off_axis_of_E_eq {α : Type*} {η xper : Config α} {vl p : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} {gen : ℤ × ℤ} (cg : ChainDataGeom η xper vl p S gen)
    (hold : ChainDataGeom.RetiredBottom cg)
    (hE : E (↑S : Set (ℤ × ℤ)) =
      {((1:ℤ),(0:ℤ)), ((-1:ℤ),(0:ℤ)), ((0:ℤ),(1:ℤ)), ((0:ℤ),(-1:ℤ))}) :
    cg.nJ.1 ≠ 0 ∧ cg.nJ.2 ≠ 0 := by
  have hnot := ChainDataGeom.negNJ_not_mem_E cg hold
  rw [hE] at hnot
  have hprim : IsCoprime cg.nJ.1 cg.nJ.2 := cg.nJ_prim
  constructor
  · intro h1
    rw [h1, isCoprime_zero_left, Int.isUnit_iff] at hprim
    apply hnot
    rcases hprim with h2 | h2
    · have : -cg.nJ = ((0:ℤ),(-1:ℤ)) := Prod.ext (by simp [h1]) (by simp [h2])
      rw [this]; simp
    · have : -cg.nJ = ((0:ℤ),(1:ℤ)) := Prod.ext (by simp [h1]) (by simp [h2])
      rw [this]; simp
  · intro h2
    rw [h2, isCoprime_zero_right, Int.isUnit_iff] at hprim
    apply hnot
    rcases hprim with h1 | h1
    · have : -cg.nJ = ((-1:ℤ),(0:ℤ)) := Prod.ext (by simp [h1]) (by simp [h2])
      rw [this]; simp
    · have : -cg.nJ = ((1:ℤ),(0:ℤ)) := Prod.ext (by simp [h1]) (by simp [h2])
      rw [this]; simp

/-- `n_J` off-axis and `n_J ⊥ v_J ≠ 0` make `v_J` off-axis. -/
theorem ChainDataGeom.vJ_off_axis {α : Type*} {η xper : Config α} {vl p : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} {gen : ℤ × ℤ} (cg : ChainDataGeom η xper vl p S gen)
    (hn : cg.nJ.1 ≠ 0 ∧ cg.nJ.2 ≠ 0) : cg.vJ.1 ≠ 0 ∧ cg.vJ.2 ≠ 0 := by
  have hd : cg.nJ.1 * cg.vJ.1 + cg.nJ.2 * cg.vJ.2 = 0 := cg.dot_nJ_vJ
  have hne := cg.vJ_ne
  constructor
  · intro h1
    rw [h1, mul_zero, zero_add] at hd
    rcases mul_eq_zero.mp hd with h | h
    · exact hn.2 h
    · exact hne (Prod.ext h1 h)
  · intro h2
    rw [h2, mul_zero, add_zero] at hd
    rcases mul_eq_zero.mp hd with h | h
    · exact hn.1 h
    · exact hne (Prod.ext h h2)

/-- (Status: archival, retired shape.)  **Under the retired `bottom`, no `ChainDataGeom` has
`Env = EnvOf ↑S` and box-shaped `A i`.**  See §8.2. -/
theorem ChainDataGeom.false_of_envOf_S_boxA {α : Type*} {η xper : Config α} {vl p : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} {gen : ℤ × ℤ} (cg : ChainDataGeom η xper vl p S gen)
    (hold : ChainDataGeom.RetiredBottom cg)
    (hpin : cg.toChainData.Env = EnvOf (↑S : Set (ℤ × ℤ)))
    (hA : ∀ i, ∃ p q : ℤ × ℤ, p.1 < q.1 ∧ p.2 < q.2 ∧ cg.toChainData.A i = box p q) :
    False := by
  -- 1. `E ↑S` is the axis set, so `n_J`, `v_J` are off-axis.
  obtain ⟨p₀, q₀, hp₀, hq₀, hA₀⟩ := hA 0
  have henv : Enveloped (↑S : Set (ℤ × ℤ)) (box p₀ q₀) := by
    have h := cg.toChainData.envA 0
    rw [hpin, hA₀] at h
    exact h
  have hE := enveloped_box_E_eq (finite_E_of_finite (Finset.finite_toSet S)) hp₀ hq₀ henv
  obtain ⟨hn1, hn2⟩ := ChainDataGeom.nJ_off_axis_of_E_eq cg hold hE
  obtain ⟨hv1, hv2⟩ := ChainDataGeom.vJ_off_axis cg ⟨hn1, hn2⟩
  -- 2. Each `Â_i` is a box.
  have hAhat : ∀ i, ∃ p q : ℤ × ℤ, cg.toChainData.Ahat i = box p q := by
    intro i
    obtain ⟨p, q, -, -, hAi⟩ := hA i
    refine ⟨p - (cg.toChainData.kk i : ℤ) • vl, q - (cg.toChainData.kk i : ℤ) • vl, ?_⟩
    rw [cg.toChainData.AhatEq i, hAi, preimage_add_box]
  -- 3. The `v_J`-ray from a point of `Â_∞` stays in `Â_∞`.
  obtain ⟨g, hg⟩ := cg.ahat_nonempty
  have hray : ∀ t : ℕ, g + (t : ℤ) • cg.vJ ∈ ⋃ i, cg.toChainData.Ahat i := by
    intro t
    induction t with
    | zero => simpa using hg
    | succ t ih =>
      have e : g + ((t + 1 : ℕ) : ℤ) • cg.vJ = g + (t : ℤ) • cg.vJ + cg.vJ := by
        push_cast; rw [add_smul, one_smul, add_assoc]
      rw [e]
      exact cg.rec_vJ _ ih
  -- 4. Both corners of the rectangle spanned by `g` and `g + t • v_J` are in `Â_∞`.
  have hcorner : ∀ t : ℕ,
      ((g.1 + (t : ℤ) * cg.vJ.1, g.2) : ℤ × ℤ) ∈ ⋃ i, cg.toChainData.Ahat i ∧
      ((g.1, g.2 + (t : ℤ) * cg.vJ.2) : ℤ × ℤ) ∈ ⋃ i, cg.toChainData.Ahat i := by
    intro t
    obtain ⟨i₀, hi₀⟩ := Set.mem_iUnion.mp hg
    obtain ⟨i₁, hi₁⟩ := Set.mem_iUnion.mp (hray t)
    have h0 : g ∈ cg.toChainData.Ahat (max i₀ i₁) :=
      cg.toChainData.AhatMono _ _ (le_max_left _ _) hi₀
    have h1 : g + (t : ℤ) • cg.vJ ∈ cg.toChainData.Ahat (max i₀ i₁) :=
      cg.toChainData.AhatMono _ _ (le_max_right _ _) hi₁
    obtain ⟨p, q, hpq⟩ := hAhat (max i₀ i₁)
    rw [hpq] at h0 h1
    obtain ⟨a1, a2, a3, a4⟩ := h0
    obtain ⟨b1, b2, b3, b4⟩ := h1
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      at b1 b2 b3 b4
    constructor
    · exact Set.mem_iUnion.mpr ⟨max i₀ i₁, by rw [hpq]; exact ⟨b1, b2, a3, a4⟩⟩
    · exact Set.mem_iUnion.mpr ⟨max i₀ i₁, by rw [hpq]; exact ⟨a1, a2, b3, b4⟩⟩
  -- 5. One of the two products `n_J.1 v_J.1`, `n_J.2 v_J.2` is negative; push `t` up.
  have hsum : cg.nJ.1 * cg.vJ.1 + cg.nJ.2 * cg.vJ.2 = 0 := cg.dot_nJ_vJ
  have hne : cg.nJ.1 * cg.vJ.1 ≠ 0 := mul_ne_zero hn1 hv1
  have hD : ∀ t : ℕ, cg.cJ ≤ dot cg.nJ g + (t : ℤ) * (cg.nJ.1 * cg.vJ.1) ∧
      cg.cJ ≤ dot cg.nJ g + (t : ℤ) * (cg.nJ.2 * cg.vJ.2) := by
    intro t
    obtain ⟨h1, h2⟩ := hcorner t
    have e1 := cg.ahat_halfPlane _ h1
    have e2 := cg.ahat_halfPlane _ h2
    constructor
    · convert e1 using 1; simp only [dot]; ring
    · convert e2 using 1; simp only [dot]; ring
  generalize hc1 : cg.nJ.1 * cg.vJ.1 = c1 at hsum hne hD
  generalize hc2 : cg.nJ.2 * cg.vJ.2 = c2 at hsum hD
  have hneg : c1 ≤ -1 ∨ c2 ≤ -1 := by omega
  set D := dot cg.nJ g with hDdef
  have ht0 : D - cg.cJ + 1 ≤ ((D - cg.cJ + 1).toNat : ℤ) := Int.self_le_toNat _
  have htn : (0 : ℤ) ≤ ((D - cg.cJ + 1).toNat : ℤ) := Int.natCast_nonneg _
  obtain ⟨e1, e2⟩ := hD (D - cg.cJ + 1).toNat
  generalize hT : ((D - cg.cJ + 1).toNat : ℤ) = T at ht0 htn e1 e2
  rcases hneg with h | h
  · have := mul_le_mul_of_nonneg_left h htn
    generalize T * c1 = w at e1 this
    omega
  · have := mul_le_mul_of_nonneg_left h htn
    generalize T * c2 = w at e2 this
    omega

end WedgePin

/-! ## §9. Pricing the repair of `bottom`: the `a'`-conjunct restricted to off-face windows

**Status 2026-09-19, twice revised.**  The *restriction* priced here landed first (06:17–06:43:
`ChainGeom.lean` (iv) guarded, `ShellGeom.lean` / `ChainShell.lean` / `ANormal.lean` consumers
guarded to match), and was then **superseded the same day by deletion**: conjunct (iv) is gone
from `ChainDataGeom.bottom`, `gen_of_shell` no longer takes `hstab'` and derives the `a'`-side
itself (`Colle37Geom.run_of_face`, `gen_of_line_late`, `ShellGeom.lean`), and `FaceBlock.gen`,
`bottom_of_seed`, `bottom_shape` followed.  What made the guard insufficient: guarded (iv)
together with (v) is still false on the closed quadrant with the unit-square window,
`a = (0,0)`, `a' = (1,0)`, `r = 1` — Collé's `m = 2` shape — at the off-face `b = (0,1)`,
`k = L` (`tmp/Abottom_noIV.lean`, `not_guardedIV_quad_sq1`; receipt in `tmp/`, not landed).
The prose below is the pricing as written before either decision, kept per §14; where it
argues for restriction *over* deletion (§9.2, second paragraph) it is **withdrawn**, see the
note there.  The local copies it refers to (`ChainDataGeomA`, `gen_of_shell_offFace`,
`ChainDataGeomA.genLayers`) were deleted once they became verbatim duplicates of the real
declarations.  `cgwA` is a `ChainDataGeom` and survives the deletion unchanged.

### 9.1 The culprit, isolated

`ChainDataGeom.a_eq_a'` (§7.2) uses conjunct (iv) of `bottom` (`ChainGeom.lean:104-105`) at
`b := a`, a point **on** the `ℓ_J`-face (`dot n_J (a - a') = 0`).  `ChainDataGeomA` below is
`ChainDataGeom` verbatim except that (iv) is restricted to `b` **strictly above** the face,
`1 ≤ dot n_J (b - a')`.  Then:

* `cgwA` inhabits it over `cgw`'s data (`Step_PeriodsRays2.lean:233`) with the window
  `Sgenw = {(0,0),(1,0)}`, `a = (0,0) ≠ a' = (1,0)`, `r = 1` — `cgwA_a_ne_a'`.  Every field of
  `ChainDataGeom` other than (iv) is discharged verbatim; the restricted (iv) is vacuous on this
  window (no point of `Sgenw` is above the face), which is exactly the point: with the on-face
  instance gone, `a ≠ a'` is consistent.  (`Env := fun _ => True` as in `cgw`; `a_eq_a'` does not
  touch `Env`, so this does not weaken the test.)
* `cgwA_full_stab'_false`: the **un**restricted (iv) is false on `cgwA`'s data at every `ε`, and
  the failing instance is `b = a`, `k` at the start of the half-line — the same instance
  `a_eq_a'` uses.  So (iv)-on-the-face is the sole culprit, not a symptom of something else.

### 9.2 The consumer survives the restriction — kernel, no hand-read

The only consumer of (iii)/(iv) is `ChainDataWithShell.gen` (`ChainShell.lean:110`) through
`Colle37Geom.gen_of_shell` (`ShellGeom.lean:146`) and `Colle37.gen_of_line` (`ShellGen.lean:203`).
Reading `gen_of_shell`: `hstab`/`hstab'` are consumed **only** under the second disjunct of
`hedge`/`hedge'`, i.e. only at `b` with `1 ≤ dot n (b - a)` resp. `1 ≤ dot n (b - a')`.
`gen_of_shell_offFace` below is `gen_of_shell` with the restricted `hstab`, `hstab'`, same
proof; `ChainDataGeomA.genLayers` is `ChainDataGeom.genLayers` (`ChainGeom.lean:199`) on the
weakened bundle.  So the restriction costs the downstream chain nothing:
`region_not_periodic_of_geom` (`ChainGeom.lean:220`) only needs `genLayers`.

⚠ **Withdrawn 2026-09-19 (kept per §14).**  The paragraph that followed here argued that
*dropping* (iv) entirely could not keep the consumer fed, on the hand-read that `ray_up` needs
the off-face translates `b - a'` and "placing `a` there instead would need the face points
`a + j•d` *above* the target, not yet generated".  The hand-read missed that `a' = a + j•d`
with `j ≤ r` is forced by the face hypotheses (`Colle37Geom.run_of_face`), so the translate
`z₀ + k•d + (b - a')` **is** `z₀ + (k - j)•d + (b - a)`, and `ray_up` only fires at
`k > M + r ≥ L + r`, where `k - j ≥ L`: the `a`-side absorption alone feeds `hup`.  The kernel
has this as `Colle37Geom.gen_of_shell` with `hstab'` removed (`ShellGeom.lean`), so
`gen_of_line` was *not* refuted without `hup` — `hup` was *supplied* from `hstab`.  Original
text, verbatim:

> What is **not** shown here: that *dropping* (iv) entirely (the integrator's first proposal)
> keeps the consumer fed.  Hand-read of `genClosure_ray` (`ShellGen.lean:132-146`): the upward
> half of the ray induction (`ray_up`) places the window with `a'` at the target so that the other
> face points `a' - j•d` lie *below* (already generated), and needs the off-face translates
> `b - a'` to land in `Â_∞^{(ε)}` — that is `hup`'s second disjunct, fed by `hstab'`.  Placing `a`
> there instead would need the face points `a + j•d` *above* the target, not yet generated.  So
> the `a'`-side is load-bearing for the upward ray, and the repair that keeps `gen_of_line` intact
> is the **restriction**, not the deletion.  (c) until someone refutes `gen_of_line` without
> `hup`; the restriction is the safe one and is what is measured here.

### 9.3 Which endpoint does the source want?  (hand-read of `b3_colle2.txt` only)

The source never writes a translate of the new line by `S_φ - a` or `S_φ - a'`.  What it says
(`:597`): *"Since `S_φ` is an `η`-generating set, we may enlarge the set where `ϑ` and `x̂_per`
coincide so that `ϑ|Â^{(ε+1)}_∞ = x̂_per|Â^{(ε+1)}_∞`"* — generation from a seed block, both
directions along the line.  Generation upward needs the window placed with its `v_J`-**max**
face point at the target (the other face points then trail behind, already generated) and its
off-face points inside `Â^{(ε)}_∞`; downward, with the `v_J`-**min** face point at the target.
So the source needs *both* endpoints, each only for its **off-face** points — which is the
restricted form, and matches `gen_of_line`'s `hdown`/`hup` exactly.  The bundle's mistake is
not "wrong endpoint" but "on-face points included": at `b = a`, (iv) asks `Â_∞` to absorb the
translate `-r•v_J`, i.e. to contain the half-line's `r` predecessors — which contradicts
`z₀ + L•v_J` being its *start* (conjunct (v)).  §7.2's orientation reading ("`a − a'` points
against the half-line") was the right diagnosis with the wrong prescription: the fix is to
exclude the face, not the endpoint.

### 9.4 Blast radius (grep, 2026-09-19, `\.bottom\b` and `hstab'`; updated after the deletion)

Consumers of `bottom` in the tree outside this file, and what the deletion of (iv) did to each:
`ChainDataGeom.genLayers` (`ChainGeom.lean`, destructures the four conjuncts, passes to
`ChainDataWithShell.gen` — one pattern and one argument fewer); `ChainDataGeom.dot_nJ_vJ1_neg`
(`ANormal.lean`, uses (i),(ii) only — one pattern fewer); `ChainDataGeom.bottom_shape`
(`ANormal.lean`, shape receipt — restates the four-conjunct field);
`ChainDataWithShell.bottom_of_seed` (`ANormal.lean`, producer-side — `hseedS'` and the `a'`
binder gone); `Claim411.*` (`RegionClaim411.lean`, uses (i),(ii),(v) only — one pattern fewer);
the bundle witnesses `cgw` (`Step_PeriodsRays2.lean`), `cgn`, `cgc` (`ShellConvex.lean`),
`cgwA` (below), `Case2WindowProbe.Gen.cgg` — each lost one `?_` and one bullet.  Statements
that *restated* the (iv) shape as a hypothesis, now without it: `ChainDataWithShell.gen`
(`ChainShell.lean`), `FaceBlock.gen` (`ANormal.lean`), `gen_of_shell` (`ShellGeom.lean`, which
now *derives* the `a'`-side).  `MaxEnv.BottomShape` (`BottomNotEventual.lean`) is a refutation
of the *old* shape and stays as archive.  Kernel results that changed status: `a_eq_a'`,
`negNJ_not_mem_E`, `not_dot_h_eq_zero`, `false_of_envOf_S_boxA` (§7–§8) are facts about
`RetiredBottom`; OPEN #7's `a_ne_a'_of_dot_h_eq_zero` (`FaceDistinct.lean:174`) is usable
again. -/

section BottomRepair

open Nivat.MaxEnv Nivat.Colle35 Nivat.Colle37 Nivat.Colle37Geom Nivat.ColleStep.PeriodsRays2

variable {α : Type*}

/-! **2026-09-19, after the repair landed in `ChainGeom.lean`:** the local structure
`ChainDataGeomA` and its `gen_of_shell_offFace` / `ChainDataGeomA.genLayers` that lived here
while the repair was being priced have been **deleted** — `ChainDataGeomA` was `ChainDataGeom`
verbatim once the guard went into the real field, and `gen_of_shell_offFace` became
`Colle37Geom.gen_of_shell` itself (`ShellGeom.lean`; since the deletion of (iv) that theorem
no longer takes `hstab'` at all).  `cgwA` below is therefore a `ChainDataGeom`, not a copy of
one. -/

/-- Column-by-column filtration for the window `Sgenw = {(0,0),(1,0)}`, `gen = (1,0)`:
each new site needs its left neighbour. -/
def FilA (i i₀ ε n : ℕ) : Set (ℤ × ℤ) :=
  Ah i ∪ Sh i₀ ε ∪ (Sh i ε ∩ {z | z.1 < (n : ℤ)})

/-- Column `0` of `Sh i ε` lies in `Ah i ∪ Sh i₀ ε`, for every `i₀`. -/
theorem col0_mem {i i₀ ε : ℕ} {z : ℤ × ℤ} (hz : z ∈ Sh i ε) (h0 : z.1 = 0) :
    z ∈ Ah i ∪ Sh i₀ ε := by
  obtain ⟨h1, h2, h3, h4⟩ := hz
  rcases le_or_gt 0 z.2 with h5 | h5
  · exact Or.inl ⟨h1, h2, h5, h4⟩
  · have hi₀ : (0 : ℤ) ≤ (i₀ : ℤ) := Int.natCast_nonneg i₀
    exact Or.inr ⟨h1, by omega, h3, by omega⟩

/-- `Sgenw.erase (1,0) = {(0,0)}`, hence lattice convex. -/
theorem latticeConvex_Sgenw_erase :
    LatticeConvex (Sgenw.erase ((1 : ℤ), (0 : ℤ))) := by
  have hE : Sgenw.erase ((1 : ℤ), (0 : ℤ)) = {((0 : ℤ), (0 : ℤ))} := by decide
  rw [hE]
  exact Nivat.Colle37.latticeConvex_singleton _

/-- `ChainData.fillZero` for `FilA`, factored out so `fillCover` can reuse it. -/
theorem FilA_zero (i i₀ ε : ℕ) : FilA i i₀ ε 0 ⊆ Ah i ∪ Sh i₀ ε := by
  rintro z (hz | ⟨hz, hlt⟩)
  · exact hz
  · exfalso
    have := hz.1
    simp only [Set.mem_ofPred_eq, Nat.cast_zero] at hlt
    omega

/-- `ChainData.fillStep` for `FilA`, factored out so `fillCover` can reuse it. -/
theorem FilA_step (i i₀ ε : ℕ) : ∀ n : ℕ, ∀ z ∈ FilA i i₀ ε (n + 1),
    z ∈ FilA i i₀ ε n ∨ ∃ t : ℤ × ℤ, z = ((1 : ℤ), (0 : ℤ)) + t ∧
      ∀ b ∈ Sgenw.erase ((1 : ℤ), (0 : ℤ)), b + t ∈ FilA i i₀ ε n := by
  rintro n z (hz | ⟨hzS, hlt⟩)
  · exact Or.inl (Or.inl hz)
  · simp only [Set.mem_ofPred_eq, Nat.cast_add, Nat.cast_one] at hlt
    rcases lt_or_ge z.1 (n : ℤ) with h | h
    · exact Or.inl (Or.inr ⟨hzS, h⟩)
    · have hz1 : z.1 = (n : ℤ) := by omega
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        exact Or.inl (Or.inl (col0_mem hzS (by simpa using hz1)))
      · refine Or.inr ⟨z - ((1 : ℤ), (0 : ℤ)), by abel, ?_⟩
        intro b hb
        have hb0 : b = ((0 : ℤ), (0 : ℤ)) := by
          simp only [Sgenw, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hb
          rcases hb.2 with h | h
          · exact h
          · exact absurd h hb.1
        subst hb0
        obtain ⟨h1, h2, h3, h4⟩ := hzS
        have hn' : (1 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
        refine Or.inr ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
        all_goals (simp; omega)

/-- **`ChainDataGeom` is inhabited with `a ≠ a'`.**  `cgw`'s data, window `Sgenw`.  Built
2026-09-19 against the *guarded* (iv) (vacuous on this window: no point of `Sgenw` is above the
face); survives the deletion of (iv) unchanged, and is now the tree's witness that a bundle with
a genuine `ℓ_J`-edge (`r = 1`) exists. -/
def cgwA : ChainDataGeom etaC xperC vlv pv Sgenw ((1 : ℤ), (0 : ℤ)) where
  Env := fun _ => True
  B := Ah
  A := Ah
  u := fun _ => 0
  kk := fun _ => 0
  Ahat := Ah
  shell := Sh
  shellInf := ShInf
  envB := fun _ => trivial
  envA := fun _ => trivial
  subBA := fun _ => subset_rfl
  subAB := cgw.toChainData.subAB
  subStrip := fun i => Colle35.subset_halfStrip _ _
  agreeA := cgw.toChainData.agreeA
  AhatEq := cgw.toChainData.AhatEq
  AhatMono := cgw.toChainData.AhatMono
  maximalHat := cgw.toChainData.maximalHat
  shellFinite := cgw.toChainData.shellFinite
  subShell := cgw.toChainData.subShell
  shellSubInf := cgw.toChainData.shellSubInf
  shellInfZero := cgw.toChainData.shellInfZero
  -- `I₀`（第 162 轮，`b3_colle2.txt:520`）：整条转发 `cgw`，两条 shell 字段直接复用。
  I₀ := cgw.toChainData.I₀
  shellSubStrip := cgw.toChainData.shellSubStrip
  shellProper := cgw.toChainData.shellProper
  shellEnv := ⟨1, 0, one_pos, fun _ _ => trivial⟩
  fill := FilA
  fillZero := FilA_zero
  fillStep := fun i i₀ ε n => FilA_step i i₀ ε n
  -- Round 80 (`Lemma35.lean:765`) rephrased `fillCover` against `Colle37.GenClosure`;
  -- `genFill_of_abstract_fill` (`GenClosureWeaken.lean:116`) turns `FilA_zero` / `FilA_step`
  -- into it, at the same filtration index `z.1.toNat + 1` the old `⋃ n` witness used.  Its
  -- `hconv` side condition is `latticeConvex_Sgenw_erase` (`Sgenw.erase (1,0) = {(0,0)}`).
  fillCover := by
    intro ε i₀ _hε _hEnv i _hi z hz
    refine Nivat.GenClosureWeaken.genFill_of_abstract_fill (S := Sgenw)
      (gen := ((1 : ℤ), (0 : ℤ))) (fill := FilA i i₀ ε) (by decide)
      latticeConvex_Sgenw_erase (FilA_zero i i₀ ε) (FilA_step i i₀ ε)
      (z.1.toNat + 1) z (Or.inr ⟨hz, ?_⟩)
    show z.1 < ((z.1.toNat + 1 : ℕ) : ℤ)
    have := Int.self_le_toNat z.1
    push_cast
    omega
  vJ1 := vlv
  nJ := nJv
  cJ := 0
  shellInf_eq := cgw.shellInf_eq
  ahat_nonempty := cgw.ahat_nonempty
  ahat_halfPlane := cgw.ahat_halfPlane
  vJ := vJv
  a := ((0 : ℤ), (0 : ℤ))
  a' := ((1 : ℤ), (0 : ℤ))
  r := 1
  latticeConvex_S := latticeConvex_Sgenw
  a_mem := by simp [Sgenw]
  a'_mem := by simp [Sgenw]
  lex := by
    intro b hb
    simp only [Sgenw, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb.2 with rfl | rfl
    · exact absurd rfl hb.1
    · right; norm_num [dot, nJv, vJv]
  lex' := by
    intro b hb
    simp only [Sgenw, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb.2 with rfl | rfl
    · right; norm_num [dot, nJv, vJv]
    · exact absurd rfl hb.1
  edge := by
    intro b hb
    simp only [Sgenw, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb.2 with rfl | rfl
    · exact absurd rfl hb.1
    · exact Or.inl ⟨1, le_rfl, le_rfl, by simp [vJv]⟩
  edge' := by
    intro b hb
    simp only [Sgenw, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb.2 with rfl | rfl
    · exact Or.inl ⟨1, le_rfl, le_rfl, by simp [vJv]⟩
    · exact absurd rfl hb.1
  dot_nJ_vJ := by simp [dot, nJv, vJv]
  bottom := by
    intro ε
    refine ⟨((0:ℤ), -(ε:ℤ) - 1), 0, ?_, ?_, ?_, ?_⟩
    · show dot nJv ((0:ℤ), -(ε:ℤ) - 1) = (0:ℤ) - (ε:ℤ) - 1
      simp [dot, nJv]
    · intro k hk
      rw [iUnion_Ah, reach_Qs]
      show (0 : ℤ) ≤ _
      simp only [Prod.fst_add, Prod.smul_fst, vJv, smul_eq_mul, mul_one]
      omega
    · intro b hb k hk
      have hb' : b = ((0:ℤ), (0:ℤ)) ∨ b = ((1:ℤ), (0:ℤ)) := by simpa [Sgenw] using hb
      rw [iUnion_Ah, reach_Qs]
      show (0 : ℤ) ≤ _
      rcases hb' with rfl | rfl <;>
        simp only [Prod.fst_add, Prod.fst_sub, Prod.smul_fst, vJv, smul_eq_mul, mul_one] <;>
        omega
    · rintro z ⟨h1, h2⟩
      rcases le_or_gt (-(ε:ℤ)) z.2 with h | h
      · exact Or.inl ⟨h1, h⟩
      · refine Or.inr ⟨z.1, h1, ?_⟩
        have hz2 : z.2 = -(ε:ℤ) - 1 := by push_cast at h2; omega
        refine Prod.ext ?_ ?_
        · simp [vJv]
        · simp [vJv, hz2]
  rec_p := cgw.rec_p
  dot_nJ_p := cgw.dot_nJ_p
  vJ_ne := cgw.vJ_ne
  vJ_prim := cgw.vJ_prim
  rec_vJ := cgw.rec_vJ
  cL := 0
  ahat_halfPlane_L := cgw.ahat_halfPlane_L
  ahat_attained_L := cgw.ahat_attained_L
  nJ_prim := cgw.nJ_prim
  nfp_L := cgw.nfp_L

/-- `ChainDataGeom` admits `a ≠ a'`: the derivation `a_eq_a'` needs the on-face instance of the
retired conjunct (iv), which the field no longer has.  Kernel witness that the deletion freed
`a ≠ a'` (`a_eq_a'` itself compiles regardless — it reads `RetiredBottom`, not `cg.bottom`). -/
theorem cgwA_a_ne_a' : cgwA.a ≠ cgwA.a' := by
  show ((0:ℤ), (0:ℤ)) ≠ ((1:ℤ), (0:ℤ))
  simp

theorem cgwA_r : cgwA.r = 1 := rfl

/-- **The unrestricted (iv) is false on `cgwA`'s data, at every `ε`, at `b = a`.**  Given only
conjunct (v) (the half-line is exactly the new layer), the translate by `a - a' = (-1,0)` of
the line's first point `(0, -ε-1)` leaves `reachSet Â_∞ v_{J-1} = {0 ≤ x}`. -/
theorem cgwA_full_stab'_false (ε : ℕ) :
    ¬ ∃ (z₀ : ℤ × ℤ) (L : ℤ),
      (∀ b ∈ Sgenw, ∀ k : ℤ, L ≤ k →
        z₀ + k • cgwA.vJ + (b - cgwA.a') ∈ reachSet (⋃ i, cgwA.toChainData.Ahat i) cgwA.vJ1) ∧
      (∀ z ∈ cgwA.toChainData.shellInf (ε + 1),
        z ∈ cgwA.toChainData.shellInf ε ∨ ∃ k : ℤ, L ≤ k ∧ z = z₀ + k • cgwA.vJ) := by
  rintro ⟨z₀, L, hstab', hsplit⟩
  have hz : ((0:ℤ), -(ε:ℤ) - 1) ∈ cgwA.toChainData.shellInf (ε + 1) := by
    refine ⟨le_rfl, ?_⟩
    show -((ε + 1 : ℕ) : ℤ) ≤ -(ε:ℤ) - 1
    push_cast
    omega
  rcases hsplit _ hz with h | ⟨k, hk, hzk⟩
  · have h2 : -(ε:ℤ) ≤ -(ε:ℤ) - 1 := h.2
    omega
  · have hmem := hstab' ((0:ℤ), (0:ℤ)) (by simp [Sgenw]) k hk
    have hU : (⋃ i, cgwA.toChainData.Ahat i) = Qs := iUnion_Ah
    have hR : reachSet Qs cgwA.vJ1 = {z : ℤ × ℤ | 0 ≤ z.1} := reach_Qs
    rw [hU, hR, ← hzk] at hmem
    have h3 : (0:ℤ) ≤ ((((0:ℤ), -(ε:ℤ) - 1) : ℤ × ℤ) + (((0:ℤ), (0:ℤ)) - ((1:ℤ), (0:ℤ)))).1 :=
      hmem
    simp at h3

/-- **`cgwA` is a `ChainDataGeom` that does not satisfy the retired `bottom`** — the kernel
witness that the deletion is a strict weakening and that `a_eq_a'` was about the retired shape,
not about `ChainDataGeom`. -/
theorem cgwA_not_retiredBottom : ¬ ChainDataGeom.RetiredBottom cgwA := by
  intro hold
  obtain ⟨z₀, L, -, -, -, hstab', hsplit⟩ := hold 0
  exact cgwA_full_stab'_false 0 ⟨z₀, L, hstab', hsplit⟩

/-- **The link `:424` → `not_dot_h_eq_zero`, at the kernel:** the edge normals of `S_φ` are
exactly the primitive vectors orthogonal to some generator `h_i`.  Packaging of
`E_zono` (`MinkowskiEdges.lean:292`) and `E_segOf` (`:204`) through `DecompData.Sphi_eq`, the
same three transport lemmas as `mem_E_Sphi_of_dot_eq_zero` (`FaceDistinct.lean:146`). -/
theorem DecompData.E_Sphi_eq [AddCommMonoid α] {η : Config α} (d : DecompData η) :
    E (↑d.Sphi : Set (ℤ × ℤ)) = ⋃ i : Fin d.m, {n | Prim n ∧ dot n (d.h i) = 0} := by
  have hconv : Conv d.Sphi = Conv (zonoF Finset.univ d.h) := by
    rw [d.Sphi_eq, Conv_supp_prod_eq_Conv_zonoF Finset.univ d.h (fun j _ => d.h_ne j)]
  rw [E_congr_of_Conv_eq hconv, coe_zonoF, E_zono]
  ext n
  simp only [Set.mem_iUnion, Finset.mem_univ, exists_true_left]
  refine exists_congr fun i => ?_
  rw [E_segOf (d.h_ne i)]

end BottomRepair

end Nivat.ShellMink

#print axioms Nivat.ShellMink.enveloped_add_of_finite
#print axioms Nivat.ShellMink.enveloped_hexagon_shell
#print axioms Nivat.ShellMink.subShell_hexagon
#print axioms Nivat.ShellMink.shellProper_hexagon
#print axioms Nivat.ShellMink.not_shellSubInf_of_dot_neg
#print axioms Nivat.ShellMink.not_shellSubInf_zero_of_dot_neg
#print axioms Nivat.ShellMink.not_shellSubInf_sq_zero
#print axioms Nivat.ShellMink.ChainDataWithShell.add_segOf_vJ1_subset_shellInf
#print axioms Nivat.ShellMink.ChainDataGeom.not_shellSubInf_segOf_vJ1
#print axioms Nivat.ShellMink.ChainDataGeom.not_shellSubInf_segOf_vJ1_zero
#print axioms Nivat.ShellMink.ChainDataGeom.exists_not_shellSubInf_segOf_vJ1_zero
#print axioms Nivat.ShellMink.not_latHull_add_subset_reachSet
#print axioms Nivat.ShellMink.not_latHull_add_subset_shell
#print axioms Nivat.ShellMink.ChainDataWithShell.latHull_add_segOf_vJ1_subset_shellInf
#print axioms Nivat.ShellMink.shellInter_subset_right
#print axioms Nivat.ShellMink.subset_shellInter
#print axioms Nivat.ShellMink.shellInter_shell_eq
#print axioms Nivat.ShellMink.ChainDataWithShell.shellInter_vJ1_eq
#print axioms Nivat.ShellMink.shell_subset_of_thin
#print axioms Nivat.ShellMink.shell_one_subset_of_support_line
#print axioms Nivat.ShellMink.not_shell_subset_of_dot_eq_neg_one
#print axioms Nivat.ShellMink.ChainDataGeom.shellInter_vJ1_finite
#print axioms Nivat.ShellMink.ChainDataWithShell.subset_shellInter_vJ1
#print axioms Nivat.ShellMink.ChainDataGeom.shellInter_vJ1_proper
#print axioms Nivat.ShellMink.ChainData.shell_subset_strip_of_nsmul
#print axioms Nivat.ShellMink.not_shellSubStrip_of_transverse_sweep
#print axioms Nivat.ShellMink.shellInter_transverse_collapses
#print axioms Nivat.ShellMink.shellInter_vJ1_proper_example
#print axioms Nivat.ShellMink.chainB_Ahat_iUnion
#print axioms Nivat.ShellMink.chainB_shellInf_eq_strip
#print axioms Nivat.ShellMink.shell_strip_neg_eq
#print axioms Nivat.ShellMink.chainB_shellInf_ne_shell_neg
#print axioms Nivat.ShellMink.chainBNeg
#print axioms Nivat.ShellMink.chainBShellNeg
#print axioms Nivat.ShellMink.chainBShellNeg_dot_nJ_vJ1_neg
#print axioms Nivat.ShellMink.ChainDataGeom.false_of_ahat_subset_band
#print axioms Nivat.ShellMink.not_chainDataGeom_of_strip
#print axioms Nivat.ShellMink.not_chainDataGeom_over_chainBNeg
#print axioms Nivat.ShellMink.chainB_Env_eq
#print axioms Nivat.ShellMink.chainB_shellEnv_all
#print axioms Nivat.ShellMink.enveloped_box_E_eq
#print axioms Nivat.ShellMink.not_enveloped_box_of_off_axis
#print axioms Nivat.ShellMink.coe_chainB_S
#print axioms Nivat.ShellMink.not_envOf_S_chainB_shell
#print axioms Nivat.ShellMink.DecompData.not_enveloped_box_of_off_axis_normal
#print axioms Nivat.ShellMink.ChainDataGeom.a_eq_a'
#print axioms Nivat.ShellMink.ChainDataGeom.negNJ_not_mem_E
#print axioms Nivat.ShellMink.ChainDataGeom.not_dot_h_eq_zero
#print axioms Nivat.ShellMink.preimage_add_box
#print axioms Nivat.ShellMink.ChainDataGeom.nJ_off_axis_of_E_eq
#print axioms Nivat.ShellMink.ChainDataGeom.vJ_off_axis
#print axioms Nivat.ShellMink.ChainDataGeom.false_of_envOf_S_boxA
#print axioms Nivat.ShellMink.ChainDataGeom.RetiredBottom
#print axioms Nivat.ShellMink.ChainDataGeom.bottom_of_retiredBottom
#print axioms Nivat.ShellMink.cgwA_not_retiredBottom
#print axioms Nivat.ShellMink.cgwA
#print axioms Nivat.ShellMink.cgwA_a_ne_a'
#print axioms Nivat.ShellMink.cgwA_full_stab'_false
#print axioms Nivat.ShellMink.DecompData.E_Sphi_eq
