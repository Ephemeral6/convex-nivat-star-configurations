/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.ChainGeom
import Nivat.External.Colle.Generating
import Nivat.External.Colle.L1Fields
import Nivat.External.Colle.R2Orientation
import Nivat.External.Colle.Step_PeriodsRays2

/-!
# Collé's (4.1) on a generating set: the `ℝ`/`ℤ` bridge, and a refutation

Target: `RegionSteps.lean:1739` (`exists_case2_run`, leaf C's whole remaining `sorry` as of
2026-09-19), owned by the integrator; this file produces standalone lemmas that bear on it and
does **not** edit `RegionSteps.lean`.

## Task (1) — the `ℝ`/`ℤ` bridge (below), landed regardless of task (2)

`L1Data.exists_side_with_run_of_latticeConvex` (`L1Fields.lean:633`) is stated over the real
normal `n : ℝ × ℝ` and `Nivat.R2.face` (`R2Orientation.lean:80`, a filter on `inner2 w z = c`
with `inner2 : ℝ × ℝ → ℤ × ℤ → ℝ`).  `exists_case2_run` is stated over the integer normal
`cg.nJ : ℤ × ℤ` and `Nivat.LE2.dot` (`LatticeEdges.lean:72`).  `inner2_toReal_eq_dot` and
`face_eq_filter_dot` are the two bridging facts; `exists_max_face` is the max-side mirror of
`L1Data.exists_min_face` (`L1Fields.lean:651`), needed because `exists_case2_run`'s conclusion
is phrased at the **top** of the `nJ`-order, i.e. the second disjunct of
`exists_side_with_run_of_latticeConvex`.

## Task (2) — the side selection: **`exists_case2_run` is FALSE as stated**

Team-lead's dispatch asked to spend twenty minutes on whether the "bad branch" is outright
impossible (candidate (c)) before attempting the general WLOG.  It is not merely possible —
**the whole statement fails**, independent of which branch is picked, because the statement
never requires the `nJ`-bottom face to be a proper face (`< Sgen.card` points): if *every*
point of `Sgen` sits at the same `nJ`-level, `hmin` holds vacuously and the conclusion demands
a `q` strictly above that level, which cannot exist.

This is not a contrived degeneracy manufactured for this file: the tree already contains a
complete, non-degenerate `ChainDataGeom` (`cgw`, `Step_PeriodsRays2.lean:233`) together with a
generating set for its own `ξ` (`Sgenw = {(0,0),(1,0)}`, `Step_PeriodsRays2.lean:65`, certified
by `isGeneratingSet_etaC`) whose two points sit at the **same** `cgw.nJ`-level (`nJv = (0,1)`,
`dot nJv (0,0) = dot nJv (1,0) = 0`).  Taking `a₀ := (0,0)` satisfies `hmin` vacuously
(`hmin` only needs to dominate the other point, which is tied) and refutes the conclusion:
there is no `q ∈ Sgenw` with `dot nJv (0,0) < dot nJv q`, since both elements score `0`.

`not_exists_case2_run` below states the theorem's own closure (universally quantified exactly
as written at `RegionSteps.lean:1739-1746`) and refutes it with this witness, compiled.

**Status update, 2026-09-19 (integrator):** `Nivat.ColleReg.exists_case2_run` — the real
theorem, now carrying six additional binders threaded onto the signature this file refutes, and
discharged via L3band's `C11Bridge.exists_run` — is proved and on-chain
(`#print axioms Nivat.ColleReg.exists_case2_run` = `[propext, Classical.choice, Quot.sound]`,
no `sorryAx`), in the same `rc=0` build as `not_exists_case2_run` below. This is not a
contradiction: `not_exists_case2_run` refutes the closure of the *unthreaded* signature read
off disk before that threading landed, which is a strictly different (weaker-hypothesis)
proposition from the real theorem. This file stays as the off-chain kernel record that those
six binders are load-bearing, not decoration; it no longer describes an open gap in leaf C.

### What this does and does not mean for leaf C

* It does **not** mean Collé's (4.1) is false — Collé's actual statement (`b3_colle2.txt:627`,
  `:774`) is about the face **exposed at the minimum**, which by definition has `≤ |Sgen|`
  points but need not be all of `Sgen`; the gap here is that `exists_case2_run`'s `hmin`
  hypothesis allows the degenerate case where the "face" is the whole set, and the conclusion
  was never weakened to allow for it (a flat `Sgen`, or an `Sgen` with a flat `nJ`-image, simply
  has no admissible `q`).
* The fix is a missing non-degeneracy hypothesis, e.g. `∃ w ∈ Sgen, dot cg.nJ a₀ <
  dot cg.nJ w` (the bottom face is a proper subset of `Sgen`) — exactly the `hne`/`hmaxne`
  premise `exists_max_face` below supplies.  **But adding it does not, on its own, close the
  side-selection question the dispatch asked about.**  `exists_side_with_run`'s proof
  (`L1Fields.lean:496-502`) branches on `card_pigeonhole (face S₁ n cmax).card
  (face S₁ n cmin).card` — which disjunct fires is decided by a **cardinality comparison
  between the top and bottom faces**, not a free choice.  `exists_case2_run`'s conclusion is
  the *bottom*-face branch (`n := cg.nJ`, level `cmin := dot cg.nJ a₀`); the dichotomy hands it
  out only when the bottom face is the *smaller* one.  So even after the non-degeneracy fix,
  landing `exists_case2_run` still needs either (i) an independent argument that the bottom
  face is never the larger one for this `Sgen`/`nJ` (this is where Collé's Lemma 2.3
  parallelogram, `b3_colle2.txt:627`/`:774`, earns its keep — it is not a WLOG-relabelling
  device, it is the missing card comparison), or (ii) a version of `exists_side_with_run`
  strengthened to hand back a designated branch.  **Candidate (c) from the dispatch (`the bad
  branch is outright impossible`) is therefore the right question, but it reduces to a genuine
  face-cardinality inequality, not to a `Sgen`-membership degeneracy** — the twenty-minute
  check asked for is not yet answered; it is now stated precisely enough to attempt.  No
  lemma in the tree currently supplies that inequality (`L1Fields.lean`'s own scope note at
  `:631` says the same for conjuncts 14–16).
-/

set_option autoImplicit false

namespace Nivat.RunSide

open Nivat Nivat.LE2 Nivat.Colle35 Nivat.ColleReg Nivat.ColleReg.L1Data

/-! ## Task (1): the `ℝ`/`ℤ` bridge -/

/-- **The real level function agrees with the integer one, cast.**  `toReal`
(`Defs/Complexity.lean:87`), `inner2` (`Section8/HalfPlane.lean:42`), `dot`
(`LatticeEdges.lean:72`). -/
theorem inner2_toReal_eq_dot (m z : ℤ × ℤ) :
    inner2 (Nivat.toReal m) z = ((Nivat.LE2.dot m z : ℤ) : ℝ) := by
  simp only [inner2, Nivat.toReal, Nivat.LE2.dot]
  push_cast
  ring

/-- **`Nivat.R2.face` at an integer normal and integer level is exactly the integer `filter`.**
Bridges `L1Data.exists_side_with_run_of_latticeConvex`'s real-valued `Nivat.R2.face S₁ n cmax`
to `exists_case2_run`'s integer-valued `Sgen.filter fun w => dot m w = c`. -/
theorem face_eq_filter_dot (Sgen : Finset (ℤ × ℤ)) (m : ℤ × ℤ) (c : ℤ) :
    Nivat.R2.face Sgen (Nivat.toReal m) ((c : ℤ) : ℝ) =
      Sgen.filter fun w => Nivat.LE2.dot m w = c := by
  ext z
  rw [Nivat.R2.mem_face, Finset.mem_filter, inner2_toReal_eq_dot]
  constructor
  · rintro ⟨hz, heq⟩; exact ⟨hz, by exact_mod_cast heq⟩
  · rintro ⟨hz, heq⟩; exact ⟨hz, by exact_mod_cast heq⟩

/-- **The max-side mirror of `L1Data.exists_min_face` (`L1Fields.lean:651`).**  A non-empty
finite set has a maximising level for any normal, needed because `exists_case2_run`'s
conclusion sits at the *top* of the `nJ`-order (the second disjunct of
`exists_side_with_run_of_latticeConvex`, at `n := toReal (-cg.nJ)`, `cmin := -(dot cg.nJ a₀)`). -/
theorem exists_max_face {S₁ : Finset (ℤ × ℤ)} {n : ℝ × ℝ} {cmin : ℝ}
    (hSne : (S₁.filter fun z => cmin < inner2 n z).Nonempty) :
    ∃ cmax : ℝ, (∀ z ∈ S₁, inner2 n z ≤ cmax) ∧
      (Nivat.R2.face S₁ n cmax).Nonempty ∧ cmin < cmax := by
  classical
  obtain ⟨z₁, hz₁⟩ := hSne
  rw [Finset.mem_filter] at hz₁
  obtain ⟨zmax, hzmaxS, hzmax⟩ := S₁.exists_max_image (fun z => inner2 n z) ⟨z₁, hz₁.1⟩
  refine ⟨inner2 n zmax, hzmax, ⟨zmax, Nivat.R2.mem_face.mpr ⟨hzmaxS, rfl⟩⟩, ?_⟩
  exact lt_of_lt_of_le hz₁.2 (hzmax z₁ hz₁.1)

/-! ## Task (2): the side selection is impossible to save by WLOG — the statement needs a
non-degeneracy hypothesis instead.  First, the refutation of the statement as dispatched. -/

/-- **`exists_case2_run`'s statement, verbatim** (`RegionSteps.lean:1739-1746`), as a
free-standing `Prop` so it can be refuted without editing that file. -/
def ExistsCase2RunStatement : Prop :=
  ∀ {ξ xper : Config ℤ} {vl p : ℤ × ℤ} {S : Finset (ℤ × ℤ)} {gen : ℤ × ℤ}
    (cg : ChainDataGeom ξ xper vl p S gen)
    {Sgen : Finset (ℤ × ℤ)}, Nivat.Colle.IsGeneratingSet ξ Sgen →
    ∀ {a₀ : ℤ × ℤ}, a₀ ∈ Sgen →
      (∀ w ∈ Sgen, Nivat.LE2.dot cg.nJ a₀ ≤ Nivat.LE2.dot cg.nJ w) →
      ∃ q ∈ Sgen, Nivat.LE2.dot cg.nJ a₀ < Nivat.LE2.dot cg.nJ q ∧
        ∀ i : ℕ, i < (Sgen.filter fun w =>
            Nivat.LE2.dot cg.nJ w = Nivat.LE2.dot cg.nJ a₀).card - 1 →
          q + (i : ℤ) • cg.vJ ∈ Sgen

open Nivat.ColleStep.PeriodsRays2 in
/-- **Refutation.**  Witness: `cgw` (a genuine, non-degenerate `ChainDataGeom`) with
`Sgen := Sgenw = {(0,0),(1,0)}` (a certified `IsGeneratingSet` for `cgw`'s own `ξ`) and
`a₀ := (0,0)`.  `cgw.nJ = nJv = (0,1)` scores both points of `Sgenw` at level `0`, so `hmin`
holds vacuously and no `q` with a strictly higher score exists. -/
theorem not_exists_case2_run : ¬ ExistsCase2RunStatement := by
  intro H
  obtain ⟨q, hq, hgt, -⟩ :=
    H cgw isGeneratingSet_etaC (Finset.mem_insert_self ((0 : ℤ), (0 : ℤ)) _)
      (by
        intro w hw
        fin_cases hw <;> simp [Nivat.LE2.dot, cgw, nJv])
  have hqv : cgw.nJ = nJv := rfl
  rw [hqv] at hgt
  simp only [Sgenw, Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl <;> simp [Nivat.LE2.dot, nJv] at hgt

/-! ## What remains open, precisely (not stubbed — see module docstring)

`exists_max_face` above is exactly the non-degeneracy premise `exists_case2_run` is missing
(`hSne`/`hmaxne` in `exists_side_with_run_of_latticeConvex`'s vocabulary).  Composing it with
`inner2_toReal_eq_dot`/`face_eq_filter_dot` and `exists_side_with_run_of_latticeConvex` would
close `exists_case2_run` **only on the branch `card_pigeonhole` hands out**; the remaining
gap — showing the bottom face is never the larger one for the `Sgen`/`nJ` this leaf actually
supplies, i.e. Collé's Lemma 2.3 parallelogram argument — is not attempted here. No stub is
left for it: a `theorem ... := by sorry` for a statement whose precise hypotheses are not yet
known would be worse than an explicit gap in prose (`CLAUDE.md`, 🔴 "agent 不许把 `sorry` 落进
主仓"). -/

end Nivat.RunSide

#print axioms Nivat.RunSide.inner2_toReal_eq_dot
#print axioms Nivat.RunSide.face_eq_filter_dot
#print axioms Nivat.RunSide.exists_max_face
#print axioms Nivat.RunSide.not_exists_case2_run
