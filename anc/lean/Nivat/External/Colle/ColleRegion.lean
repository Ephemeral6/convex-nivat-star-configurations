/-
Copyright (c) 2025 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import Nivat.Section8.ExternalDefs
import Nivat.External.Colle.Lemma35
import Nivat.External.Colle.Lemma45
import Nivat.External.Colle.LatticeEdges
import Nivat.External.Colle.RegionSteps
import Nivat.External.Colle.Claim414Wire

/-!
# Collé region construction (Theorem from Section 8)

This file proves `colle_region`, which constructs a lattice-convex region with periodic structure
from a minimal counterexample. It combines:
- Lemma 3.5 (already proved, `Nivat.Colle35.lemma35`)
- The geometric chain construction of Colle's Definition 3.2, now *concrete* via
  `Nivat.LE2.EnvOf` (`Nivat/External/Colle/LatticeEdges.lean`)

**2026-09-16 note:** `Nivat.Colle45.claim46` was removed; see `Lemma45.lean` §5.

## What changed on 2026-09-13 (de-degeneration pass)

The file used to carry a `Placeholder` namespace with

```
def NonExpansiveLine (ξ : Config ℤ) : Set (ℤ × ℤ) := ∅
def IsOneSidedNonexpansive (ξ : Config ℤ) (ℓ : ℤ × ℤ) : Prop := False
```

and a witness-extraction step guarded by `∀ t, ∀ z, dot ℓ z ≤ t → x z = y z`.  All three are
degenerate: the first two make every downstream statement vacuous, and the third forces
`x = y` (take `t := dot ℓ z`), so it can never be satisfied together with `x ≠ y`.  The
degeneracy of the third is now *recorded as a compiled theorem*,
`old_guard_forces_eq`, so the bug cannot come back silently.

They are replaced by the real definitions `Nivat.Colle45.NonExpansiveLine` and
`Nivat.Colle45.IsOneSidedNonexpansive` (both fixed to the `t = 0` half-plane, matching the
`sideOf`/`ONED` convention of `Nivat.Section8.ExternalDefs`).

The `Env` field of `Nivat.Colle35.ChainData` — Colle's "is an `E(S_φ)`-enveloped set",
left abstract in `Lemma35.lean` — is now *pinned* in the statement of the chain-data step to

```
Env = Nivat.LE2.EnvOf (↑d.Sphi : Set (ℤ × ℤ))
```

for `d : Nivat.Colle35.DecompDataZ ξ` (since 2026-09-17; before that the set was the
Lemma 2.4 `S` of `exists_preamble`, which is a different set from Collé's `𝒮_φ` — see
"Which set" in `RegionSteps.lean`), as instructed by §10 of `LatticeEdges.lean`, and the
same statement additionally demands
`∀ i, c.B i ⊂ c.B (i + 1)`, i.e. the chain really grows.  Section `Nondegeneracy` below
proves that this pair of demands is satisfiable, by an explicit chain of lattice boxes.

## Honest status

**Closed 2026-09-30.**  All leaves of `RegionSteps.lean` are proved (the last,
`exists_chainData`, by `Nivat.ColleReg.exists_chainData_closed` in `Hole1PushShell.lean`);
measured that day, `Nivat.nivat_conjecture` — and hence `colle_region` on its chain — reports
`[propext, Classical.choice, Quot.sound]`, and `bash scripts/sorries.sh` reports `TOTAL: 0`.
The rest of this section, including the `sorryAx` readings, is dated history.

Until then `colle_region` was **not** proved — `#print axioms Nivat.ColleReg.colle_region`
reported `sorryAx`.  But it contains no `sorry` of its own: it is pure assembly over named theorems in
`Nivat/External/Colle/RegionSteps.lean`, so every hole has a name, a type, and an address the
blueprint can point at, and several people can work on them at once.  `bash scripts/sorries.sh`
is the authoritative list; do not read the count off this docstring.

**Since 2026-09-18 this theorem is on the main chain.**  Its conclusion is character-for-character
the one `Nivat/Section8/External.lean` used to carry as the `axiom colle_region`
(`tmp/subst_check.lean`, FROZEN E1's `rfl` check, is green), it is substituted at
`Section8/ExternalDischarged.lean`'s `exists_fullyPeriodic_region'`, and the axiom declaration is
deleted.  Consequently, until 2026-09-30, `Nivat.nivat_conjecture` measured
`[propext, sorryAx, Classical.choice, Quot.sound]`, the `sorryAx` being exactly the open leaves
below.  The `¬ IsPeriodic ξ'` clause, which for two days was the reason the check was red, is
produced differently in the two cases and neither route goes through `region_not_periodic`'s
weakened Claim 3.7 form (which stays as an *input*):

* Case 1 (`region_case1`): `ξ'` is a translate `T e ξ` (`b3_colle2.txt:778`), so
  `¬ IsPeriodic ξ'` is `CosetPigeonhole.not_isPeriodic_T_of_not_isPeriodic` on `hξ.1.2.2.1`
  — `b3_colle2.txt:846` verbatim.
* Case 2 (this file's second branch): `ϑ` comes from Lemma 3.5 and is not a translate, so it
  needs Claim 4.14 (`b3_colle2.txt:918-922`), supplied by `claim414_of_chainDataGeom`
  (`Claim414Wire.lean`, closure `[propext, Classical.choice, Quot.sound]`).

The leaves, and where they stood on the day the assembly was first written (2026-09-14; the
table is kept for the correction below it, not as a status board):

| theorem | content | |
|---|---|---|
| `exists_biONED_direction` | Colle **Lemma 2.6**, the rationality step | **PROVED**, kernel-clean |
| `exists_chainData` | Colle's §3 chain construction | convex geometry + Zorn |
| `region_latticeConvex` | `Â_∞` is lattice-convex | **PROVED** 2026-09-17 |
| `region_nonempty` | `Â_∞` is nonempty | **PROVED**, kernel-clean |
| `region_periods_and_rays` | two periods with rays inside `Â_∞` | |
| `region_not_periodic` | Claim 3.7 for `ϑ` | **PROVED** 2026-09-17 (`ChainGeom.lean`) |

**Correction, 2026-09-14.**  This table used to read
`| exists_biONED_direction | Claim 4.6 at A := ℤ | all of Colle §4 |`, and the blueprint node
`lem:biONED` called it the hardest of the six.  Checked against the source that is wrong twice
over: Colle's Claim 4.6 is a statement about a region `R_{ι-1}`, not about the existence of a
bi-nonexpansive lattice direction, and where §4 needs such a direction it *assumes* one,
citing Theorem 1.14 and Lemma 2.6.  The node is Lemma 2.6 and nothing more; it has since been
proved in `Step_BiONED.lean` and was among the *easier* of the six.  See the docstring of
`ColleReg.exists_biONED_direction` for the full reading with line references.

Splitting them up also exposed two joints the old single proof had left unconnected — see
"Joints that do not close" in `RegionSteps.lean`.

Before the 2026-09-13 pass there were ten holes, three of which (`h_line_sweep`,
`h_line_closure`, `h_2d_sweep`) were unused `have`s citing `Nivat.Colle43.line_sweep_equality`
and `Nivat.Colle43.line_closure_of_period` — names that no longer exist in `Claim43.lean`.
They were deleted rather than left as decoration.

Everything in the `Nondegeneracy` section, and `old_guard_forces_eq`, is `sorry`-free.

NOTE: this module is not reachable from the `Nivat` root, so plain `lake build` does not
compile it.  Check it with `lake build Nivat.External.Colle.ColleRegion`.
-/

namespace Nivat.ColleReg

open Nivat

/-! ## Regression guard for the `∀ t` degeneracy

The two placeholder predicates that used to live here were `∅` and `False`.  The third
degeneracy was subtler and is the one worth keeping a proof of: an agreement clause with
`t` universally quantified is not a half-plane condition at all, it is agreement
everywhere. -/

/-- **The old guard was vacuous.**  `∀ t : ℤ, ∀ z, dot ℓ z ≤ t → x z = y z` implies `x = y`
outright, so it can never coexist with the `x ≠ y` conjunct it was written next to.  This
is why `IsOneSidedNonexpansive` is stated with the fixed half-plane `dot ℓ z ≤ 0`. -/
theorem old_guard_forces_eq {x y : Config ℤ} {ℓ : ℤ × ℤ}
    (h : ∀ t : ℤ, ∀ z, Nivat.LE2.dot ℓ z ≤ t → x z = y z) : x = y := by
  funext z
  exact h (Nivat.LE2.dot ℓ z) z le_rfl

/-- The same trap in its `NonExpansiveLine` spelling: `∃ t, z ∈ halfPlaneLE ℓ t` holds for
every `z`, so the old membership condition also collapsed to `x = y`. -/
theorem old_halfPlane_guard_trivial (ℓ z : ℤ × ℤ) :
    ∃ t : ℤ, z ∈ Nivat.LE2.halfPlaneLE ℓ t :=
  ⟨Nivat.LE2.dot ℓ z, le_refl (Nivat.LE2.dot ℓ z)⟩

/-! ## Nondegeneracy of the `Env := EnvOf ↑S` wiring

`LatticeEdges.lean` §10 says the `Env` field of `ChainData` should be instantiated with
`Nivat.LE2.EnvOf (↑S : Set (ℤ × ℤ))`, and leaves the wiring to whoever joins the two files.
The danger of doing that is that the demand could turn out to be satisfiable only by a
degenerate chain (the existing `Nivat.Colle35.nonempty_chainData` takes `B i = {0}` for all
`i`, so its chain never grows).

This section rules that out: with `S` the four lattice points of `[0,1]²`, the boxes
`B i = [0, i+1]²` are all `E(S)`-enveloped and `B i ⊊ B (i+1)` for every `i`, with the
explicit separating point `(i+2, i+2)`. -/

section Nondegeneracy

open Nivat.LE2

/-- The generating window of the witness: the four lattice points of the unit square. -/
def winS : Finset (ℤ × ℤ) := {(0, 0), (1, 0), (0, 1), (1, 1)}

@[simp] theorem coe_winS : (winS : Set (ℤ × ℤ)) = sq1 := by
  ext z
  obtain ⟨a, b⟩ := z
  simp only [winS, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff, sq1, mem_box, Prod.mk.injEq]
  constructor
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> norm_num
  · rintro ⟨h1, h2, h3, h4⟩
    omega

/-- The candidate chain: `Bchain i = [0, i+1]²`. -/
def Bchain (i : ℕ) : Set (ℤ × ℤ) := box (0, 0) ((i : ℤ) + 1, (i : ℤ) + 1)

theorem mem_Bchain {i : ℕ} {a b : ℤ} :
    ((a, b) : ℤ × ℤ) ∈ Bchain i ↔
      0 ≤ a ∧ a ≤ (i : ℤ) + 1 ∧ 0 ≤ b ∧ b ≤ (i : ℤ) + 1 := Iff.rfl

theorem Bchain_pos (i : ℕ) : (0 : ℤ) < (i : ℤ) + 1 := by omega

theorem Bchain_zero : Bchain 0 = sq1 := by norm_num [Bchain, sq1]

theorem Bchain_one : Bchain 1 = sq2 := by norm_num [Bchain, sq2]

/-- Every member of the chain is a genuine lattice polygon: four edges, positive area. -/
theorem E_Bchain (i : ℕ) : E (Bchain i) = {(1, 0), (-1, 0), (0, 1), (0, -1)} :=
  E_box (p := (0, 0)) (q := ((i : ℤ) + 1, (i : ℤ) + 1)) (Bchain_pos i) (Bchain_pos i)

theorem posArea_Bchain (i : ℕ) : PosArea (Bchain i) :=
  posArea_of_three_edges (n := (1, 0)) (m := (-1, 0)) (k := (0, 1))
    (by rw [E_Bchain]; simp) (by rw [E_Bchain]; simp) (by rw [E_Bchain]; simp)
    (by decide) (by decide) (by decide)

theorem two_le_face_Bchain_right (i : ℕ) : 2 ≤ (face (Bchain i) (1, 0)).encard := by
  rw [Bchain, face_box_right (le_of_lt (Bchain_pos i))]
  exact two_le_encard_of_pair (a := ((i : ℤ) + 1, (0 : ℤ))) (b := ((i : ℤ) + 1, (1 : ℤ)))
    ⟨rfl, by norm_num, by omega⟩ ⟨rfl, by norm_num, by omega⟩
    (by intro h; rw [Prod.ext_iff] at h; omega)

theorem two_le_face_Bchain_left (i : ℕ) : 2 ≤ (face (Bchain i) (-1, 0)).encard := by
  rw [Bchain, face_box_left (le_of_lt (Bchain_pos i))]
  exact two_le_encard_of_pair (a := ((0 : ℤ), (0 : ℤ))) (b := ((0 : ℤ), (1 : ℤ)))
    ⟨rfl, by norm_num, by omega⟩ ⟨rfl, by norm_num, by omega⟩
    (by intro h; rw [Prod.ext_iff] at h; omega)

theorem two_le_face_Bchain_top (i : ℕ) : 2 ≤ (face (Bchain i) (0, 1)).encard := by
  rw [Bchain, face_box_top (le_of_lt (Bchain_pos i))]
  exact two_le_encard_of_pair (a := ((0 : ℤ), (i : ℤ) + 1)) (b := ((1 : ℤ), (i : ℤ) + 1))
    ⟨by norm_num, by omega, rfl⟩ ⟨by norm_num, by omega, rfl⟩
    (by intro h; rw [Prod.ext_iff] at h; omega)

theorem two_le_face_Bchain_bot (i : ℕ) : 2 ≤ (face (Bchain i) (0, -1)).encard := by
  rw [Bchain, face_box_bot (le_of_lt (Bchain_pos i))]
  exact two_le_encard_of_pair (a := ((0 : ℤ), (0 : ℤ))) (b := ((1 : ℤ), (0 : ℤ)))
    ⟨by norm_num, by omega, rfl⟩ ⟨by norm_num, by omega, rfl⟩
    (by intro h; rw [Prod.ext_iff] at h; omega)

/-- **The chain satisfies the wired `Env`.**  Each `Bchain i` is `E(↑winS)`-enveloped, i.e.
`Nivat.LE2.EnvOf (↑winS) (Bchain i)` — exactly the shape the `envB`/`envA` fields of
`ChainData` need once `Env := EnvOf ↑S`. -/
theorem envOf_Bchain (i : ℕ) : EnvOf (winS : Set (ℤ × ℤ)) (Bchain i) := by
  rw [coe_winS]
  refine envOf_of_E_eq (isLatticeConvexRegion_box _ _) ?_ ?_
  · rw [E_Bchain, E_sq1]
  · intro n hn
    rw [E_sq1] at hn
    rcases hn with rfl | rfl | rfl | rfl
    · rw [encard_face_sq1_right]; exact two_le_face_Bchain_right i
    · rw [encard_face_sq1_left]; exact two_le_face_Bchain_left i
    · rw [encard_face_sq1_top]; exact two_le_face_Bchain_top i
    · rw [encard_face_sq1_bot]; exact two_le_face_Bchain_bot i

theorem Bchain_subset_succ (i : ℕ) : Bchain i ⊆ Bchain (i + 1) := by
  rintro ⟨a, b⟩ hz
  rw [mem_Bchain] at hz ⊢
  omega

/-- **The chain grows strictly**, with the explicit separating point `(i+2, i+2)`. -/
theorem Bchain_ssubset (i : ℕ) : Bchain i ⊂ Bchain (i + 1) := by
  rw [Set.ssubset_iff_of_subset (Bchain_subset_succ i)]
  refine ⟨((i : ℤ) + 2, (i : ℤ) + 2), ?_, ?_⟩
  · rw [mem_Bchain]; push_cast; omega
  · rw [mem_Bchain]; omega

/-- The base case spelled out with explicit elements: `B 0 = [0,1]²`, `B 1 = [0,2]²`, and
`(2,2)` lies in the second but not the first. -/
theorem Bchain_zero_ssubset_one :
    Bchain 0 ⊂ Bchain 1 ∧ ((2 : ℤ), (2 : ℤ)) ∈ Bchain 1 ∧ ((2 : ℤ), (2 : ℤ)) ∉ Bchain 0 := by
  refine ⟨Bchain_ssubset 0, ?_, ?_⟩
  · rw [mem_Bchain]; norm_num
  · rw [mem_Bchain]; norm_num

/-- **Non-degeneracy of the wiring `Env := Nivat.LE2.EnvOf ↑S`.**

There is a window `S` and a chain `B : ℕ → Set (ℤ × ℤ)` such that every `B i` is a genuine
lattice polygon of positive area, satisfies the wired `Env`, and `B i ⊊ B (i+1)` for every
`i`.

Scope of this check, stated precisely: it shows that the two clauses added to
`h_chain_data` below — `Env = EnvOf ↑S` and `∀ i, B i ⊂ B (i+1)` — are **jointly
satisfiable in isolation**, so neither is vacuous and the pair is not self-contradictory.
It does *not* show that a full 28-field `ChainData` exists with both, which is the content
of the remaining `sorry`.  It does, however, rule out the escape route taken by
`Nivat.Colle35.nonempty_chainData`, whose chain is `B i = {0}` for all `i` and therefore
fails `∀ i, B i ⊂ B (i+1)` at every step. -/
theorem envOf_chain_nondegenerate :
    ∃ (S : Finset (ℤ × ℤ)) (B : ℕ → Set (ℤ × ℤ)),
      (∀ i, Nivat.LE2.EnvOf (S : Set (ℤ × ℤ)) (B i)) ∧
      (∀ i, PosArea (B i)) ∧
      (∀ i, B i ⊂ B (i + 1)) :=
  ⟨winS, Bchain, envOf_Bchain, posArea_Bchain, Bchain_ssubset⟩

end Nondegeneracy

/-! ## The region theorem -/

theorem colle_region {ξ : Config ℤ} (hξ : IsMinimalCounterexample ξ) {w : ℝ × ℝ} (hw : w ≠ 0)
    (hw₁ : w ∈ ONED ξ) (hw₂ : -w ∈ ONED ξ) :
    ∃ ξ' ∈ orbitClosure ξ, ¬ IsPeriodic ξ' ∧ ∃ R : Set (ℤ × ℤ),
      IsLatticeConvexRegion R ∧ R.Nonempty ∧
        ∃ h h' z₀ z₀' : ℤ × ℤ, det h h' ≠ 0 ∧
          (∀ k : ℕ, z₀ + (k : ℤ) • h ∈ R) ∧ (∀ k : ℕ, z₀' + (k : ℤ) • h' ∈ R) ∧
          (∀ z ∈ R, z + h ∈ R → ξ' (z + h) = ξ' z) ∧
          (∀ z ∈ R, z + h' ∈ R → ξ' (z + h') = ξ' z) := by
  -- ═══════════════════════════════════════════════════════════════════════════════════
  -- PROOF ARCHITECTURE: pure assembly, no `sorry` in this block
  -- ═══════════════════════════════════════════════════════════════════════════════════
  --
  -- Every hole of this proof has a name, in `RegionSteps.lean`.  The table below is
  -- GENERATED, not hand-written: `tmp/assembly_axioms.lean` runs `#print axioms` on each
  -- step, via `bash scripts/check1.sh` (which pins the `lakefile.toml` `[leanOptions]`;
  -- see `blueprint/NOTE.md` "验证口径漏洞").  Verbatim output, 2026-09-17:
  --
  --   'Nivat.ColleReg.exists_biONED_direction' [propext, Classical.choice, Quot.sound]
  --   'Nivat.ColleReg.exists_preamble'         [propext, Classical.choice, Quot.sound]
  --   'Nivat.ColleReg.not_case2_of_case1'      [propext, Classical.choice, Quot.sound]
  --   'Nivat.ColleReg.case1_of_not_case2'      [propext, Classical.choice, Quot.sound]
  --   'Nivat.ColleReg.exists_chainData'        [propext, sorryAx, Classical.choice, Quot.sound]
  --   'Nivat.ColleReg.region_case1'            [propext, sorryAx, Classical.choice, Quot.sound]
  --   'Nivat.Colle35.lemma35'                  [propext, Classical.choice, Quot.sound]
  --   'Nivat.ColleReg.region_latticeConvex'    [propext, Classical.choice, Quot.sound]
  --   'Nivat.ColleReg.region_nonempty'         [propext, Classical.choice, Quot.sound]
  --   'Nivat.ColleReg.region_periods_and_rays' [propext, sorryAx, Classical.choice, Quot.sound]
  --   'Nivat.ColleReg.region_not_periodic'     [propext, Classical.choice, Quot.sound]
  --   'Nivat.ColleReg.colle_region'            [propext, sorryAx, Classical.choice, Quot.sound]
  --
  -- Three steps carry `sorryAx`.  `exists_preamble` (`b3_colle2.txt:774-776`) and the
  -- `by_cases` on `Case2` (`:758`) were added on 2026-09-17: before that, `exists_chainData`
  -- asserted Collé's **Case 2** output unconditionally, while `:760` says Case 1 runs a
  -- different route entirely (Claim 4.6 + Lemma 4.1, region `𝓡_{ι−1}`, configuration
  -- `T^u η`).  `region_case1` is that route.  The case split itself is closed:
  -- `case1_of_not_case2` and `not_case2_of_case1` are kernel-clean, the latter because
  -- `B ⊆ H_B(ℓ)` (Definition 3.4 admits `t = 0`).
  --
  -- `exists_preamble` was **closed the same day it was opened** (2026-09-17), after its last
  -- conjunct was corrected from `det ℓ vl = 0` to `Nivat.LE2.dot ℓ vl = 0`: the Lean `ℓ` is
  -- the *normal* of the nonexpansive line (`Lemma45.lean:95-97`), so `det ℓ vl = 0` asked for
  -- `vl ∥ ℓ`, a 90° rotation away from Collé's `v_ℓ`, and the route through Propositions 2.10
  -- and 2.12 could never have produced it.  `RegionSteps.det_ne_zero_of_dot_eq_zero` is the
  -- compiled record.  See `blueprint/NOTE.md` 「已裁决：`exists_preamble` 的 `det ℓ vl = 0`
  -- 应为 `dot ℓ vl = 0` — 2026-09-17」.
  --
  -- `region_periods_and_rays` was *reopened* the same day: it had been closed through
  -- `DoublyPeriodic xper`, a conjunct that `b3_colle2.txt:890` (§4 Case 2) assumes to be
  -- false.  Its live route is Claim 4.11 + Lemma 4.1 on a subregion `𝒦 ⊂ Â_∞^{(ε)}`
  -- (`b3_colle2.txt:904`); `blueprint/NOTE.md` 「`DoublyPeriodic xper` 第三次入侵」 has the
  -- full adjudication.
  -- `region_not_periodic` remains closed via `ChainGeom.lean`; the geometry it uses is
  -- fields of `Nivat.Colle35.ChainDataGeom`, i.e. obligations of `exists_chainData`.
  -- Case 1's counterpart of that clause is **Claim 4.8** (`b3_colle2.txt:850`), which goes
  -- through **Lemma 4.4** (`:711`) instead of Claim 3.7 — a separate, more elementary
  -- argument, and an obligation of `region_case1`.
  --
  -- `d : DecompDataZ ξ` (2026-09-17) is Collé's `:764` data — the ℤ-minimal decomposition,
  -- `φ`, and `𝒮_φ := conv(−supp φ) ∩ ℤ²` (`:298`).  `Case1`/`Case2`, `exists_chainData` and
  -- `region_case1` are stated over `d.Sphi`, as `:756-758` are; the Lemma 2.4 set `S` of
  -- `exists_preamble` is a *different* set and is passed only where Collé uses `𝒮`
  -- (Claims 4.7 and 4.11): `exists_chainData` no longer takes `S` at all, and Lemma 3.5 /
  -- Claim 3.7 take `hgenφ` (output of `exists_chainData`) and `d.isGeneratingSet`.
  --
  -- The signatures there are frozen against exactly these call sites: adding a hypothesis
  -- to any of them breaks this block.
  --
  -- History (2026-09-16 → 18).  For two days this theorem's first clause was weakened to
  -- Colle's Claim 3.7 under FROZEN E1 (`blueprint/FROZEN.md:93-96`), while the axiom in
  -- `Section8/External.lean` exported `¬ IsPeriodic ξ'`, so the E1 alias check
  -- (`tmp/subst_check.lean`) was red and clearing the leaves would not have retired the axiom.
  -- On 2026-09-18 the clause was restored to `¬ IsPeriodic ξ'` — Case 1 via the translate,
  -- Case 2 via Claim 4.14 (`claim414_of_chainDataGeom`), see "Honest status" above — the check
  -- went green, the theorem was substituted at the call site and the axiom deleted.  Claim 3.7
  -- (`region_not_periodic`) is still consumed, as an *input* to Claim 4.14.
  -- ═══════════════════════════════════════════════════════════════════════════════════

  -- The only projection of `hξ` needed here; `hξ` itself is passed on whole.
  have hfin : (Set.range ξ).Finite := hξ.1.1

  obtain ⟨ℓ, hℓ_nel, hℓ_pos, hℓ_neg⟩ := exists_biONED_direction hξ hw hw₁ hw₂

  -- `b3_colle2.txt:774`: the Lemma 2.4 generating set `𝒮` and `x_per` are fixed *before* the case
  -- split.  `hSgen` goes to both branches — Claim 4.7 (`region_case1`) and Claim 4.11
  -- (`region_periods_and_rays`, its `Sgen` binder, 2026-09-17); `hdef` goes to Case 1 and, once
  -- `region_periods_and_rays` takes it, to Claim 4.11 too.  Neither is about `𝒮_φ`.
  obtain ⟨xper, vl, p, S, gen, hxper_mem, hgen, hSgen, hp_mem, hp_ne, hvl_ne, hvl_prim,
    hdet_vl, hdet_ℓ, hpartner, hdef⟩ := exists_preamble_pair hξ hw hw₁ hw₂ hℓ_nel hℓ_pos hℓ_neg

  -- **2026-09-23 (集成者): sign-normalise `p` against `vl`, shadowing the four `p`-facts.**
  -- `exists_neg_multiple_of_perp` (`RegionSteps.lean:1002`) replaces `p` by whichever of `±p`
  -- is a *negative* multiple of `vl`; `Per xper` is an `AddSubgroup` so the swap is free, and
  -- `hp_mem`/`hp_ne`/`hdet_vl` are the only downstream facts about `p` (all sign-symmetric).
  -- The new conjunct `hp_neg` is what `exists_chainData` now takes: leaf A's `rec_p` iterates
  -- the hat union's `-vl`-closure, which is false for the `+vl` sign.  Both branches of the
  -- `by_cases` below see the normalised `p`, so Case 1 is unaffected except by strictly more
  -- information.
  obtain ⟨p, hp_mem, hp_ne, hdet_vl, hp_neg⟩ :=
    exists_neg_multiple_of_perp hvl_prim hp_mem hp_ne hdet_vl

  -- `b3_colle2.txt:764`: the ℤ-minimal decomposition and `𝒮_φ`, fixed before the split.
  obtain ⟨d⟩ := Colle35.DecompDataZ.of_minimalCounterexample hξ

  -- `b3_colle2.txt:758`: Collé's two complementary cases, over `E(𝒮_φ)`-enveloped sets.
  by_cases hcase2 : Case2 ξ xper d.Sphi vl
  · -- ── Case 2 (`b3_colle2.txt:886`): Lemma 3.5 gives the chain, then Claims 4.11/4.15. ──
    obtain ⟨genφ, cg, hgenφ, hc_env⟩ :=
      exists_chainData hξ d hw hw₁ hw₂ hℓ_nel hℓ_pos hℓ_neg hxper_mem hp_mem hp_ne hvl_ne
        hvl_prim hdet_vl hdet_ℓ hp_neg hpartner hcase2

    -- **2026-09-20.**  `exists_chainData` used to export a third conjunct
    -- `∀ i, cg.toChainData.B i ⊂ cg.toChainData.B (i + 1)`.  Its sole consumer was
    -- `region_nonempty`, whose proof (`Step_Nonempty.lean`) uses it at index `0` only and
    -- discards the `∉ c.B 0` half immediately -- i.e. all it ever needed was that
    -- `cg.toChainData.B 1` is inhabited.  That is free here: `ChainData.envB`
    -- (`Lemma35.lean:714`) says `Env (B 1)`, `hc_env` rewrites `Env` to `EnvOf ↑d.Sphi`, and
    -- `L1Line0.nonempty_of_enveloped_Sphi` (`:640`) turns an `E(𝒮_φ)`-envelope into a point
    -- (the envelope has the same nonempty edge set as `𝒮_φ`, and an edge's face is a
    -- nonempty subset).  So the conjunct was deleted from the obligation rather than
    -- weakened: leaf A no longer owes it at all.
    have hB1ne : (cg.toChainData.B 1).Nonempty := by
      have h := cg.toChainData.envB 1
      rw [hc_env] at h
      exact Nivat.L1Line0.nonempty_of_enveloped_Sphi d h

    -- Round 80 swapped `lemma35`'s generation hypothesis from `GeneratesAt η S gen` to
    -- `IsGeneratingSet η S` (`Lemma35.lean:883`), because the `fillCover` field is now phrased
    -- against `Colle37.GenClosure` and the agreement step is `agree_on_genClosure`, which reads
    -- the whole generating set rather than the one distinguished point.  `d.isGeneratingSet`
    -- is already on hand (it is what `:416`/`:424` pass), so nothing new is owed upstream;
    -- `hgenφ : GeneratesAt ξ d.Sphi genφ` keeps its other three consumers.
    have h_lemma35 :=
      Colle35.lemma35 hfin hxper_mem d.isGeneratingSet hvl_ne hp_mem hp_ne hdet_vl
        cg.toChainData

    obtain ⟨ϑ, hϑ_mem, K, hϑ_agree, hϑ_periodic, ε, hshell_ε, hshell_not_εp1⟩ := h_lemma35

    have hR_lattice_convex : IsLatticeConvexRegion (⋃ i, cg.toChainData.Ahat i) :=
      region_latticeConvex cg.toChainData hξ hxper_mem hc_env hgenφ

    have hR_nonempty : (⋃ i, cg.toChainData.Ahat i).Nonempty :=
      region_nonempty_of_nonempty_B1 cg.toChainData hB1ne

    -- the trailing `⟨n, 0 < n, h' = n • cg.vJ⟩` is live since 2026-09-18: `Claim414`'s
    -- `ℓ′`-half needs the ray along `cg.vJ` itself (`Claim414EllPrime.lean:160`, via
    -- `ColleReg.rayIn_of_rayIn_nsmul`), which `claim414_of_chainDataGeom` refines out of the
    -- `h'`-ray using exactly these three components.
    -- `hξ`/`hϑ_mem` restored 2026-09-18 (`Step_PeriodsRays2.lean`): they are the first two
    -- arguments of `Colle41.lemma41_of_sweep`, the producer of the second period.
    -- `hc_env`/`hgenφ` added the same day to close the `Env := fun _ => True` and
    -- `cg.S := {0}` loopholes the same witness used; same binders `region_not_periodic`
    -- already takes at `:401`.
    -- 2026-09-18: `hshell_ε`/`hshell_not_εp1` (Collé's (4.6), `b3_colle2.txt:894`, the
    -- input Claim 4.11's proof names at `:902`) and `hdef` (Claim 4.2's deficit, for the
    -- Lemma 4.1 endgame at `:904`) added — the signature could not state "not periodic on
    -- `Â_∞^(ε+1)`" without them.  All three were already bound here (`:363`, `:378`).
    obtain ⟨R, -, hRconv', hRne', h, h', z₀, z₀', hdet, hray_h, hray_h', hper_h, hper_h',
      n, hn, hh'_eq⟩ :=
      region_periods_and_rays cg hSgen d.isGeneratingSet hξ hϑ_mem hc_env hgenφ hB1ne hp_mem
        hR_lattice_convex hR_nonempty hϑ_agree hshell_ε hshell_not_εp1 hdef
        hvl_prim hdet_vl hℓ_nel hℓ_pos hℓ_neg hdet_ℓ

    have hϑ_no_fully_periodic_acc :
        ¬ ∃ y : Config ℤ, Colle45.IsFullyPeriodic y ∧
          ∀ (W : Finset (ℤ × ℤ)) (M : ℕ), ∃ t : ℕ, M ≤ t ∧
            ∀ z ∈ W, y z = T ((t : ℤ) • cg.vJ) ϑ z :=
      region_not_periodic cg hξ hc_env hgenφ d.isGeneratingSet hvl_ne hp_ne hp_mem hdet_vl
        hxper_mem hϑ_mem hϑ_agree hϑ_periodic hshell_ε hshell_not_εp1

    -- **Claim 4.14** (`b3_colle2.txt:918-922`): *"The configuration `ϑ` is non-periodic."*
    -- This is the Case 2 route to `¬ IsPeriodic`, and it is the only one: unlike Case 1's
    -- `ξ' = T^u η`, `ϑ` is produced by Lemma 3.5 and is not a translate of `ξ`, so
    -- `CosetPigeonhole.not_isPeriodic_T_of_not_isPeriodic` does not apply here.  Claim 3.7
    -- (`hϑ_no_fully_periodic_acc`) is an input to Claim 4.14, not a substitute for it.
    have hϑ_np : ¬ IsPeriodic ϑ :=
      claim414_of_chainDataGeom cg hξ hϑ_mem hℓ_nel hdet_ℓ hp_ne hvl_ne hdet_vl hp_mem
        hR_lattice_convex hϑ_agree hRconv' hdet hray_h hray_h' hper_h' hn hh'_eq
        hϑ_no_fully_periodic_acc

    exact ⟨ϑ, hϑ_mem, hϑ_np, R, hRconv', hRne',
      h, h', z₀, z₀', hdet, hray_h, hray_h', hper_h, hper_h'⟩
  · -- ── Case 1 (`b3_colle2.txt:780`): Claims 4.6-4.8, then Lemma 4.1. ──
    exact region_case1 hξ d hℓ_nel hℓ_pos hℓ_neg hxper_mem hgen hSgen hp_mem hp_ne hvl_ne
      hvl_prim hdet_vl hdet_ℓ hdef (case1_of_not_case2 hcase2)

end Nivat.ColleReg
