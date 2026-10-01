/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.ConeRegion

/-!
# `ConeLines` — the line-by-line decomposition of `𝓡_{ι-1}`, and the `wedgeFull` comparison

原文：b3_colle2.txt:784-804 (Claim 4.6) 与 b3_colle2.txt:402 (Definition 3.2), :406
(Notation 3.3), :412 (Definition 3.4).

## What Claim 4.6's induction actually needs

The paper (`:784`) sets
`𝓡_{ι-1} := {g + t·v⃗_{ℓ_{ι-1}} ∈ ℤ² : g ∈ H_B(ℓ), t ∈ ℤ₊}`
and then conquers it one line at a time: `A₁ := 𝓡_{ι-1} ∩ l₁` with `l₁ := ℓ_B^{(-)}` (`:796`),
`A₂ := 𝓡_{ι-1} ∩ l₂` with `l₂ := l₁^{(-)}` (`:804`), "proceeding this way" — and concludes
periodicity on **all of** `𝓡_{ι-1}`.  For that conclusion to follow, the pieces must cover:

    𝓡_{ι-1} ⊆ H_B(ℓ) ∪ ⋃_{i ≥ 1} (𝓡_{ι-1} ∩ l_i).                                    (★)

Unwinding the notation fixes the levels.  `Notation 3.3` (`:406`): `ℓ^{(-)}` is the nearest
lattice line parallel to `ℓ` lying strictly outside `ℋ(ℓ)`.  `ℓ_B` is "the support line of `B`
determined by `ℓ`" (`:420`), and item (i) of Lemma 3.x (`:472`, `B_i ∩ ℓ_{B_i} ⊂ ℓ^{(-)}`)
together with item (ii) (`:476`, `B_i ⊇ [-i+1,i-1]² ∩ ℋ(ℓ^{(-)})`) pins the convention down:
`X ⊆ ℋ(ℓ_X)`, so `ℓ_X` is the boundary of the half plane that contains `X`, and `ℓ_X^{(-)}`
is the next lattice line *away from* `X`.  Writing `nℓ` for the transverse normal normalised by
`dot nℓ vl = 0`, `dot nℓ u' = -1` (so that a `u'`-step drops exactly one line, `:804`
"proceeding this way"), and `cz` for the `nℓ`-level of `ℓ_B`, this reads

* `∀ b ∈ B, cz ≤ dot nℓ b`   (`B ⊆ ℋ(ℓ_B)`),
* `l_i` is the level set `{y | dot nℓ y = cz - i}`, for `i = 1, 2, …`.

## (★) is FALSE from those two facts alone

`not_coneRegion_subset_halfStrip_union_lines` below is a kernel refutation.  The mechanism the
level bookkeeping leaves open: a cone point `b + s•vl + t•u'` with `b` high in `B` and `t ≥ 1`
sits at a level in `[cz, cz + height B]`, i.e. **above every line** `l_i`, while
`H_B(ℓ) = B + ℕ·vl` need not contain it.  In the witness below the concrete escape is that
**`B` skips a level**: `B = {(0,0), (0,2)}` has nothing at level `1`, so the `u'`-step out of
`(0,2)` lands on a level the strip never occupies.  (读法，非内核事实: a second, independent
escape route is the `u'`-step leaving `B` on the `-vl` side, where the *forward* strip does not
reach; that one is not witnessed here.)

The refutation witness additionally satisfies `det u' vl = 1`, so **a unimodularity/orientation
condition on `(u', vl)` cannot repair (★)**.  That is not an accident: with `vl = (1,0)` and
`nℓ = (0,1)`, `dot nℓ u' = -1` forces `u'.2 = -1` and hence `det u' vl = 1` for *every* value of
`u'.1` — the determinant says nothing at all about the `vl`-component of `u'`, which is precisely
the component that decides whether the `u'`-step escapes the half-strip.

**Nor does replacing the one-directional `H_B(ℓ)` by the two-sided `fullSweep B vl` repair it.**
`not_wedgeFull_subset_fullSweep_union_lines` (§6) refutes that version with the *same* witness:
the escape in the witness is a skipped level, not a `-vl` overhang, and sweeping `±vl` does not
create a point at a level `B` never meets.  This is worth stating explicitly because the
`fullSweep` rescue is the natural first guess.

## The true statement, and where the source licenses its hypothesis

What (★) really needs is that the half-strip absorbs a `u'`-step *as long as the step lands at or
above `ℓ_B`*:

    hstepIn : ∀ z ∈ H_B(ℓ), cz ≤ dot nℓ (z + u') → z + u' ∈ H_B(ℓ).

This is the hypothesis of `coneRegion_subset_halfStrip_union_lines`, and it is what Figure 10
(`:798`) draws: the boundary of `𝓡_{ι-1}` consists of an edge `w` parallel to `-ℓ` **and an edge
`w'` parallel to `ℓ_{ι-1}`** — i.e. the cone acquires no new boundary above `ℓ_B`, the `ℓ_{ι-1}`
edge of the cone is the continuation of `B`'s own `ℓ_{ι-1}` edge.  `B` has such an edge because
it is `E(𝒮_φ)`-enveloped (`Definition 3.2`, `:402`: convex, `|E(B)| = |E(𝒮_φ)|`, every edge of
`B` parallel to an edge of `𝒮_φ` and at least as long), and `ℓ_{ι-1}` is by construction the
direction of an edge of `𝒮_φ` (`:770`).

⚠ **Not done here, and not claimed**: *deriving* `hstepIn` from a Lean `Enveloped B (𝒮_φ)`
predicate.  That is a separate convex-geometry obligation; this file takes `hstepIn` as a
hypothesis and proves that it is exactly enough, and that the level bounds alone are not.

Quantifier correspondence for `hstepIn`:
- `∀ z ∈ H_B(ℓ)` ↔ ranges over `H_B(ℓ)` of `:414`; no counterpart is invented.
- `cz ≤ dot nℓ (z + u')` ↔ "`z + u'` is at or above `ℓ_B`", i.e. `z + u' ∈ ℋ(ℓ_B)`, the half
  plane of `:406` / `:420`.
- conclusion `z + u' ∈ H_B(ℓ)` ↔ Figure 10's assertion (`:798`) that `E(𝓡_{ι-1})` gains only the
  `-ℓ` edge and the `ℓ_{ι-1}` edge.

## The `wedgeFull` comparison

`Nivat.ColleReg.wedgeFull B vl u' = sweep (fullSweep B vl) u'` (`L1RegionBuild.lean:230`)
sweeps `±vl`, so it is a strict enlargement of the paper's forward-only `𝓡_{ι-1}`.
`coneRegion_subset_wedgeFull` and `not_wedgeFull_subset_coneRegion` below make the gap exact.
This matters because `WedgeResidualR` (`L1Claim.lean:928`) is stated over `wedgeFull` while the
paper's object is `coneRegion`.

§6 sharpens this to an **identity**: `wedgeFull B vl u' = coneRegion (fullSweep B vl) vl u'`
(`wedgeFull_eq_coneRegion_fullSweep`).  The two objects are the *same construction on different
seeds* — `B` versus `B + ℤ·vl` — which is what lets §4's covering be pointed at `wedgeFull`,
and hence at `chainFull` (`L1RegionBuild.lean:305`).

⚠ 记号订正：`wedgeFull` 的全名是 `Nivat.ColleReg.wedgeFull`，**不是**
`Nivat.L1RegionBuild.wedgeFull`（`L1RegionBuild.lean:40` 开的 namespace 是 `Nivat.ColleReg`）。
-/

set_option autoImplicit false

namespace Nivat.ConeLines

open Nivat Nivat.RegionSweep Nivat.LE2 Nivat.ConeRegion

/-! ### §1  The half-strip is the inner sweep -/

/-- `Nivat.LE2.halfStrip B vl` and `Nivat.RegionSweep.sweep B vl` are the same set: both are
`{g | ∃ b ∈ B, ∃ t : ℕ, g = b + (t:ℤ)•vl}`.

原文：b3_colle2.txt:414 — `H_B(ℓ) := {g + t·v⃗_ℓ : g ∈ B, t ∈ ℤ₊}`. -/
theorem halfStrip_eq_sweep (B : Set (ℤ × ℤ)) (vl : ℤ × ℤ) :
    Nivat.LE2.halfStrip B vl = Nivat.RegionSweep.sweep B vl := rfl

/-- `coneRegion B vl u'` is the `u'`-sweep of the half-strip — the paper's `𝓡_{ι-1}` read
literally off `:784` (`g` ranges over `H_B(ℓ)`, `t ∈ ℤ₊` along `v⃗_{ℓ_{ι-1}}`). -/
theorem coneRegion_eq_sweep_halfStrip (B : Set (ℤ × ℤ)) (vl u' : ℤ × ℤ) :
    coneRegion B vl u' = Nivat.RegionSweep.sweep (Nivat.LE2.halfStrip B vl) u' := rfl

/-! ### §2  The unconditional level decomposition

This one needs no hypotheses at all: every integer is either `≥ cz` or of the form `cz - 1 - i`
with `i : ℕ`.  It is recorded because it is the honest *hypothesis-free* substitute for (★) —
and it is the reason the substitute is not useful on its own: the top piece is
`coneRegion ∩ {level ≥ cz}`, not `H_B(ℓ)`, so it carries no information about the seed. -/

/-- **Level partition of the cone** (unconditional, and trivial): splitting at level `cz`.

原文：b3_colle2.txt:796-804 — the induction's index set `l_1, l_2, …` is the descending family
of lattice lines below `ℓ_B`; this lemma only says that those lines together with the closed
upper part exhaust `ℤ²`. -/
theorem coneRegion_eq_upper_union_lines (B : Set (ℤ × ℤ)) (vl u' nℓ : ℤ × ℤ) (cz : ℤ) :
    coneRegion B vl u' =
      (coneRegion B vl u' ∩ {y | cz ≤ Nivat.LE2.dot nℓ y}) ∪
        ⋃ i : ℕ, (coneRegion B vl u' ∩ {y | Nivat.LE2.dot nℓ y = cz - 1 - (i : ℤ)}) := by
  apply Set.Subset.antisymm
  · intro z hz
    by_cases hlev : cz ≤ Nivat.LE2.dot nℓ z
    · exact Or.inl ⟨hz, hlev⟩
    · refine Or.inr (Set.mem_iUnion.mpr ⟨(cz - 1 - Nivat.LE2.dot nℓ z).toNat, hz, ?_⟩)
      have h : (0 : ℤ) ≤ cz - 1 - Nivat.LE2.dot nℓ z := by omega
      simp only [Set.mem_ofPred_eq]
      rw [Int.toNat_of_nonneg h]
      omega
  · refine Set.union_subset Set.inter_subset_left (Set.iUnion_subset ?_)
    exact fun _ => Set.inter_subset_left

/-! ### §3  The refutation of (★) from the level bounds alone -/

/-- **(★) is false from `dot nℓ vl = 0`, `dot nℓ u' = -1`, `∀ b ∈ B, cz ≤ dot nℓ b` alone** —
and stays false after adding `det u' vl = 1`.

原文：b3_colle2.txt:796-804 — this refutes the *covering* that Claim 4.6's line induction
tacitly uses, **not** Claim 4.6.  The witness violates `hstepIn` of
`coneRegion_subset_halfStrip_union_lines`, which is where the missing content lives.

Witness: `nℓ = (0,1)`, `vl = (1,0)`, `u' = (0,-1)`, `cz = 0`, `B = {(0,0), (0,2)}`.
The escaping point is `(0,1) = (0,2) + 0•vl + 1•u' ∈ 𝓡_{ι-1}`; it is at level `1`, hence on no
line `{level = -1 - i}`, and it is not in `H_B(ℓ) = {(t,0)} ∪ {(t,2)}` because `B` skips level
`1` in the `vl`-column it needs.

Note `det u' vl = 0*0 - (-1)*1 = 1`: the unimodular/orientation repair (ii) does not help. With
`vl = (1,0)` and `nℓ = (0,1)`, `dot nℓ u' = -1` already forces `u'.2 = -1`, hence
`det u' vl = 1` for **every** `u'.1` — the determinant does not constrain the `vl`-component of
`u'`, which is the component that decides the escape. -/
theorem not_coneRegion_subset_halfStrip_union_lines :
    ∃ (B : Set (ℤ × ℤ)) (vl u' nℓ : ℤ × ℤ) (cz : ℤ),
      Nivat.LE2.dot nℓ vl = 0 ∧
      Nivat.LE2.dot nℓ u' = -1 ∧
      Nivat.det u' vl = 1 ∧
      (∀ b ∈ B, cz ≤ Nivat.LE2.dot nℓ b) ∧
      ¬ (coneRegion B vl u' ⊆ Nivat.LE2.halfStrip B vl ∪
            ⋃ i : ℕ, (coneRegion B vl u' ∩
              {y | Nivat.LE2.dot nℓ y = cz - 1 - (i : ℤ)})) := by
  refine ⟨({((0 : ℤ), (0 : ℤ)), ((0 : ℤ), (2 : ℤ))} : Set (ℤ × ℤ)),
    ((1 : ℤ), (0 : ℤ)), ((0 : ℤ), (-1 : ℤ)), ((0 : ℤ), (1 : ℤ)), 0,
    by simp [Nivat.LE2.dot], by simp [Nivat.LE2.dot], by simp [Nivat.det], ?_, ?_⟩
  · rintro b (rfl | rfl) <;> simp [Nivat.LE2.dot]
  · intro hsub
    -- The escaping point.
    have hz : ((0 : ℤ), (1 : ℤ)) ∈
        coneRegion ({((0 : ℤ), (0 : ℤ)), ((0 : ℤ), (2 : ℤ))} : Set (ℤ × ℤ))
          ((1 : ℤ), (0 : ℤ)) ((0 : ℤ), (-1 : ℤ)) := by
      rw [mem_coneRegion_iff]
      refine ⟨((0 : ℤ), (2 : ℤ)), by simp, 0, 1, ?_⟩
      simp
    rcases hsub hz with hstrip | hlines
    · obtain ⟨b, hb, t, ht⟩ := hstrip
      rcases hb with rfl | rfl <;> simp [Prod.ext_iff] at ht
    · obtain ⟨i, _, hi⟩ := Set.mem_iUnion.mp hlines
      simp only [Set.mem_ofPred_eq, Nivat.LE2.dot] at hi
      omega

/-! ### §4  The repaired covering

The content is entirely about a `+vl`-closed *seed*, so it is proved once for an arbitrary seed
`S` and then specialised twice: to `S = halfStrip B vl` (the paper's `H_B(ℓ)`, §4) and to
`S = fullSweep B vl` (the codebase's two-sided strip, §6). -/

/-- A `+vl`-closed seed absorbs its own `vl`-sweep, so its cone is just its `u'`-sweep. -/
theorem coneRegion_eq_sweep_of_add_vl_mem {S : Set (ℤ × ℤ)} {vl : ℤ × ℤ}
    (hvl : ∀ z ∈ S, z + vl ∈ S) (u' : ℤ × ℤ) :
    coneRegion S vl u' = Nivat.RegionSweep.sweep S u' := by
  unfold coneRegion
  rw [(Nivat.RegionSweep.sweep_eq_self_iff S vl).mpr hvl]

/-- Re-seeding the cone by the half-strip changes nothing: `coneRegion` already sweeps `vl`. -/
theorem coneRegion_halfStrip (B : Set (ℤ × ℤ)) (vl u' : ℤ × ℤ) :
    coneRegion (Nivat.LE2.halfStrip B vl) vl u' = coneRegion B vl u' := by
  unfold coneRegion
  rw [halfStrip_eq_sweep, Nivat.RegionSweep.sweep_sweep_self]

/-- **The covering, for an arbitrary `+vl`-closed seed `S`.**

原文：b3_colle2.txt:796-804.  `hstep` is `l₂ := l₁^{(-)}` … "proceeding this way" (`:804`): one
`u'`-step drops exactly one lattice line.  `hstepIn` is Figure 10's assertion (`:798`) that
`E(𝓡_{ι-1})` gains only the `-ℓ` edge and *one* `ℓ_{ι-1}` edge — i.e. the seed already absorbs
every `u'`-step that lands at or above `ℓ_B`.

Quantifiers:
- `∀ z ∈ S` ↔ ranges over the seed; the paper's seed is `H_B(ℓ)` of `:414`.
- `cz ≤ dot nℓ (z + u')` ↔ "`z + u'` is at or above `ℓ_B`", i.e. `z + u' ∈ ℋ(ℓ_B)` (`:406`, `:420`).
- conclusion `z + u' ∈ S` ↔ the `ℓ_{ι-1}` edge of `𝓡_{ι-1}` continues the seed's own (`:798`).
- `i : ℕ` ↔ the index of `l_i` in `l₁, l₂, …` (`:796`, `:804`). -/
theorem coneRegion_subset_seed_union_lines
    {S : Set (ℤ × ℤ)} {vl u' nℓ : ℤ × ℤ} {cz : ℤ}
    (hstep : Nivat.LE2.dot nℓ u' = -1)
    (hvl : ∀ z ∈ S, z + vl ∈ S)
    (hstepIn : ∀ z ∈ S, cz ≤ Nivat.LE2.dot nℓ (z + u') → z + u' ∈ S) :
    coneRegion S vl u' ⊆ S ∪
      ⋃ i : ℕ, (coneRegion S vl u' ∩ {y | Nivat.LE2.dot nℓ y = cz - 1 - (i : ℤ)}) := by
  have hcone : coneRegion S vl u' = Nivat.RegionSweep.sweep S u' :=
    coneRegion_eq_sweep_of_add_vl_mem hvl u'
  -- Above level `cz`, the `u'`-sweep has not left the seed yet.
  have key : ∀ (g : ℤ × ℤ), g ∈ S → ∀ (t : ℕ),
      cz ≤ Nivat.LE2.dot nℓ (g + (t : ℤ) • u') → g + (t : ℤ) • u' ∈ S := by
    intro g hg t
    induction t with
    | zero => intro _; simpa using hg
    | succ t ih =>
        intro hlev
        have hsucc : g + ((t + 1 : ℕ) : ℤ) • u' = (g + (t : ℤ) • u') + u' := by
          push_cast
          rw [add_smul, one_smul]
          abel
        have hdrop : Nivat.LE2.dot nℓ ((g + (t : ℤ) • u') + u')
            = Nivat.LE2.dot nℓ (g + (t : ℤ) • u') - 1 := by
          rw [Nivat.LE2.dot_add, hstep]; ring
        rw [hsucc] at hlev ⊢
        rw [hdrop] at hlev
        exact hstepIn _ (ih (by omega)) (by omega)
  intro z hz
  have hz' : z ∈ Nivat.RegionSweep.sweep S u' := hcone ▸ hz
  obtain ⟨g, hg, t, rfl⟩ := hz'
  by_cases hlev : cz ≤ Nivat.LE2.dot nℓ (g + (t : ℤ) • u')
  · exact Or.inl (key g hg t hlev)
  · refine Or.inr (Set.mem_iUnion.mpr
      ⟨(cz - 1 - Nivat.LE2.dot nℓ (g + (t : ℤ) • u')).toNat, hz, ?_⟩)
    have h : (0 : ℤ) ≤ cz - 1 - Nivat.LE2.dot nℓ (g + (t : ℤ) • u') := by omega
    simp only [Set.mem_ofPred_eq]
    rw [Int.toNat_of_nonneg h]
    omega

/-- **The covering Claim 4.6's line induction needs** (`:796-804`), for the paper's own seed
`H_B(ℓ)`.  A specialisation of `coneRegion_subset_seed_union_lines`; the half-strip's
`+vl`-closure is free (`Nivat.RegionSweep.add_mem_sweep`).

Hypotheses, each pointing at the source:
- `hperp : dot nℓ vl = 0` — `nℓ` is the transverse normal, the lines `l_i` are parallel to `ℓ`
  (`:796`, `l₁ := ℓ_B^{(-)}` is parallel to `ℓ` by `Notation 3.3`, `:406`).
- `hstep : dot nℓ u' = -1` — one `u'`-step drops exactly one lattice line, which is what
  `l₂ := l₁^{(-)}` … "proceeding this way" (`:804`) means.
- `hstepIn` — the half-strip absorbs a `u'`-step that lands at or above `ℓ_B`.  This is
  Figure 10's assertion (`:798`) that `E(𝓡_{ι-1})` consists of the `-ℓ` edge and *one*
  `ℓ_{ι-1}` edge, which continues `B`'s own `ℓ_{ι-1}` edge; `B` has one because it is
  `E(𝒮_φ)`-enveloped (`Definition 3.2`, `:402`) and `ℓ_{ι-1}` is an edge direction of `𝒮_φ`
  (`:770`).

Note `∀ b ∈ B, cz ≤ dot nℓ b` (`B ⊆ ℋ(ℓ_B)`) is **not** needed and is therefore not assumed:
`hstepIn` already carries the whole geometric content.  By
`not_coneRegion_subset_halfStrip_union_lines`, that level bound alone would *not* suffice.

⚠ Also not needed: `hperp : dot nℓ vl = 0`.  The proof only uses `hstep`, because the
`vl`-component of a cone point never changes the `nℓ`-level bookkeeping once `hstepIn` supplies
the half-strip step.  `hperp` is the *intended reading* of `nℓ` (it is what makes the level sets
`{dot nℓ · = c}` be the lines `l_i` parallel to `ℓ`), so it is recorded in
`coneRegion_subset_halfStrip_union_lines_of_lower_bound` with the source's full hypothesis list;
it is dropped here to keep the theorem at its true strength. -/
theorem coneRegion_subset_halfStrip_union_lines
    {B : Set (ℤ × ℤ)} {vl u' nℓ : ℤ × ℤ} {cz : ℤ}
    (hstep : Nivat.LE2.dot nℓ u' = -1)
    (hstepIn : ∀ z ∈ Nivat.LE2.halfStrip B vl,
      cz ≤ Nivat.LE2.dot nℓ (z + u') → z + u' ∈ Nivat.LE2.halfStrip B vl) :
    coneRegion B vl u' ⊆ Nivat.LE2.halfStrip B vl ∪
      ⋃ i : ℕ, (coneRegion B vl u' ∩ {y | Nivat.LE2.dot nℓ y = cz - 1 - (i : ℤ)}) := by
  have h := coneRegion_subset_seed_union_lines (S := Nivat.LE2.halfStrip B vl) (u' := u')
    (nℓ := nℓ) (cz := cz) hstep
    (fun z hz => Nivat.RegionSweep.add_mem_sweep (w := vl) hz) hstepIn
  rwa [coneRegion_halfStrip B vl u'] at h

/-- Restated with the source's literal hypothesis list (`hperp`, `hstep`, `hBlow`, `hstepIn`),
for the reader who wants to see all four: adding `nℓ ⊥ vl` and `B ⊆ ℋ(ℓ_B)` changes nothing,
it is `hstepIn` that does the work.

原文：b3_colle2.txt:472 — `B_i ∩ ℓ_{B_i} ⊂ ℓ^{(-)}`, i.e. `B ⊆ ℋ(ℓ_B)`;
b3_colle2.txt:406 — `l_i` parallel to `ℓ`, i.e. `dot nℓ vl = 0`. -/
theorem coneRegion_subset_halfStrip_union_lines_of_lower_bound
    {B : Set (ℤ × ℤ)} {vl u' nℓ : ℤ × ℤ} {cz : ℤ}
    (_hperp : Nivat.LE2.dot nℓ vl = 0) (hstep : Nivat.LE2.dot nℓ u' = -1)
    (_hBlow : ∀ b ∈ B, cz ≤ Nivat.LE2.dot nℓ b)
    (hstepIn : ∀ z ∈ Nivat.LE2.halfStrip B vl,
      cz ≤ Nivat.LE2.dot nℓ (z + u') → z + u' ∈ Nivat.LE2.halfStrip B vl) :
    coneRegion B vl u' ⊆ Nivat.LE2.halfStrip B vl ∪
      ⋃ i : ℕ, (coneRegion B vl u' ∩ {y | Nivat.LE2.dot nℓ y = cz - 1 - (i : ℤ)}) :=
  coneRegion_subset_halfStrip_union_lines hstep hstepIn

/-! ### §5  `coneRegion` versus `wedgeFull` -/

/-- The forward half-strip sits inside the two-sided strip: `sweep B vl ⊆ fullSweep B vl`. -/
theorem halfStrip_subset_fullSweep (B : Set (ℤ × ℤ)) (vl : ℤ × ℤ) :
    Nivat.LE2.halfStrip B vl ⊆ Nivat.ColleReg.fullSweep B vl := by
  rintro z ⟨b, hb, t, rfl⟩
  exact Nivat.ColleReg.mem_fullSweep_iff.mpr ⟨b, hb, (t : ℤ), rfl⟩

/-- **The paper's cone is contained in the codebase's wedge.**

原文：b3_colle2.txt:784 — `𝓡_{ι-1}` sweeps `v⃗_ℓ` forward only (`t ∈ ℤ₊`), whereas
`Nivat.ColleReg.wedgeFull` (`L1RegionBuild.lean:230`) sweeps `±vl`. -/
theorem coneRegion_subset_wedgeFull {B : Set (ℤ × ℤ)} (vl u' : ℤ × ℤ) :
    coneRegion B vl u' ⊆ Nivat.ColleReg.wedgeFull B vl u' :=
  Nivat.RegionSweep.sweep_mono (halfStrip_subset_fullSweep B vl) u'

/-- **The containment is strict**: `wedgeFull` is genuinely bigger than the paper's `𝓡_{ι-1}`.

Witness: `B = {(0,0)}`, `vl = (1,0)`, `u' = (0,1)`.  Then `(-1,0) = (0,0) + (-1)•vl` lies in
`fullSweep B vl ⊆ wedgeFull B vl u'`, while `coneRegion B vl u' = {(s,t) : s,t ∈ ℕ}` has only
non-negative first coordinate.

原文：b3_colle2.txt:784 — `t ∈ ℤ₊`, not `t ∈ ℤ`.  Any statement proved about `wedgeFull` is a
statement about an enlargement of Collé's object, and a refutation aimed at `wedgeFull` need not
touch `𝓡_{ι-1}`. -/
theorem not_wedgeFull_subset_coneRegion :
    ∃ (B : Set (ℤ × ℤ)) (vl u' : ℤ × ℤ),
      ¬ (Nivat.ColleReg.wedgeFull B vl u' ⊆ coneRegion B vl u') := by
  refine ⟨({((0 : ℤ), (0 : ℤ))} : Set (ℤ × ℤ)), ((1 : ℤ), (0 : ℤ)), ((0 : ℤ), (1 : ℤ)), ?_⟩
  intro hsub
  have hmem : ((-1 : ℤ), (0 : ℤ)) ∈
      Nivat.ColleReg.wedgeFull ({((0 : ℤ), (0 : ℤ))} : Set (ℤ × ℤ))
        ((1 : ℤ), (0 : ℤ)) ((0 : ℤ), (1 : ℤ)) := by
    refine ⟨((-1 : ℤ), (0 : ℤ)), ?_, 0, by simp⟩
    exact Nivat.ColleReg.mem_fullSweep_iff.mpr ⟨((0 : ℤ), (0 : ℤ)), rfl, -1, by simp⟩
  obtain ⟨b, hb, s, t, hst⟩ := (mem_coneRegion_iff).mp (hsub hmem)
  rw [hb] at hst
  simp [Prod.ext_iff] at hst

/-! ### §6  `wedgeFull` **is** a `coneRegion`, and what that buys

`Nivat.ColleReg.fullSweep B vl` is already `±vl`-closed, so sweeping it once more by `+vl`
changes nothing and `wedgeFull B vl u'` is literally `coneRegion (fullSweep B vl) vl u'`.
Consequently §4's covering applies to `wedgeFull` **with seed `fullSweep B vl`** — which is what
lets a `coneRegion`-shaped engine be pointed at `WedgeResidualR`'s objects
(`L1Claim.lean:928`), and at `chainFull B vl u' b₀ k` (`L1RegionBuild.lean:305`).

🔴 **The `fullSweep` seed does NOT make the covering unconditional.**
`not_wedgeFull_subset_fullSweep_union_lines` refutes that with the same witness as §3.  The
escape in that witness is a *skipped level* in `B`, and sweeping `±vl` cannot manufacture a point
at a level `B` never meets.  So §6 still needs a seed-step hypothesis; `stepIn_fullSweep` reduces
it from a condition on the whole strip to a condition on `B` alone.

⚠ 原文：b3_colle2.txt:777-780 — Collé's `H_B(ℓ)` is genuinely one-directional (`t ∈ ℤ₊`).
Everything in this section is therefore a statement about **our enlarged object**, not about the
paper's step.  It is usable as a bridge to the existing `wedgeFull` machinery, not as a
formalisation of Claim 4.6. -/

/-- `fullSweep B vl` is `+vl`-closed. -/
theorem add_vl_mem_fullSweep {B : Set (ℤ × ℤ)} {vl z : ℤ × ℤ}
    (hz : z ∈ Nivat.ColleReg.fullSweep B vl) : z + vl ∈ Nivat.ColleReg.fullSweep B vl := by
  obtain ⟨b, hb, k, rfl⟩ := Nivat.ColleReg.mem_fullSweep_iff.mp hz
  refine Nivat.ColleReg.mem_fullSweep_iff.mpr ⟨b, hb, k + 1, ?_⟩
  rw [add_smul, one_smul, add_assoc]

/-- **`wedgeFull` is a `coneRegion` with the two-sided strip as seed.**

`wedgeFull B vl u' = sweep (fullSweep B vl) u'` (`L1RegionBuild.lean:230`) and
`coneRegion S vl u' = sweep (sweep S vl) u'`; since `fullSweep B vl` is `+vl`-closed
(`add_vl_mem_fullSweep`), the inner sweep is the identity.  Set-theoretically: both sides are
`B + ℤ·vl + ℕ·u'`, the only content being `ℕ + ℤ = ℤ` in the `vl` coordinate.

⚠ The namespace is `Nivat.ColleReg`, not `Nivat.L1RegionBuild` (`L1RegionBuild.lean:40`). -/
theorem wedgeFull_eq_coneRegion_fullSweep (B : Set (ℤ × ℤ)) (vl u' : ℤ × ℤ) :
    Nivat.ColleReg.wedgeFull B vl u' = coneRegion (Nivat.ColleReg.fullSweep B vl) vl u' :=
  (coneRegion_eq_sweep_of_add_vl_mem (fun _ hz => add_vl_mem_fullSweep hz) u').symm

/-- `coneRegion_subset_wedgeFull` again, now as a corollary of the identity plus
`B ⊆ fullSweep B vl`: the paper's cone is the same construction on a smaller seed. -/
theorem coneRegion_subset_coneRegion_fullSweep {B : Set (ℤ × ℤ)} (vl u' : ℤ × ℤ) :
    coneRegion B vl u' ⊆ coneRegion (Nivat.ColleReg.fullSweep B vl) vl u' :=
  (wedgeFull_eq_coneRegion_fullSweep B vl u') ▸ coneRegion_subset_wedgeFull vl u'

/-- **Seed-step hypothesis for `fullSweep`, reduced to a condition on `B` alone.**

`hBstep` only quantifies over `b ∈ B` (a finite set in the intended application), not over the
whole strip.  This is where `hperp : dot nℓ vl = 0` finally earns its place: the `ℤ·vl` tail of a
strip point does not move its `nℓ`-level, so the level test can be pushed back onto `b`.

原文：b3_colle2.txt:402 (Definition 3.2) — `B` is `E(𝒮_φ)`-enveloped, hence has an edge parallel
to each edge direction of `𝒮_φ`, in particular to `ℓ_{ι-1}` (`:770`); that edge is exactly what
supplies `b'`.  ⚠ Deriving `hBstep` from a Lean `Enveloped` predicate is **not** done here. -/
theorem stepIn_fullSweep {B : Set (ℤ × ℤ)} {vl u' nℓ : ℤ × ℤ} {cz : ℤ}
    (hperp : Nivat.LE2.dot nℓ vl = 0)
    (hBstep : ∀ b ∈ B, cz ≤ Nivat.LE2.dot nℓ (b + u') →
      ∃ b' ∈ B, ∃ k : ℤ, b + u' = b' + k • vl) :
    ∀ z ∈ Nivat.ColleReg.fullSweep B vl,
      cz ≤ Nivat.LE2.dot nℓ (z + u') → z + u' ∈ Nivat.ColleReg.fullSweep B vl := by
  intro z hz hlev
  obtain ⟨b, hb, m, rfl⟩ := Nivat.ColleReg.mem_fullSweep_iff.mp hz
  have hlv : Nivat.LE2.dot nℓ (b + m • vl + u') = Nivat.LE2.dot nℓ (b + u') := by
    simp only [Nivat.LE2.dot_add, dot_zsmul, hperp]
    ring
  obtain ⟨b', hb', k, hk⟩ := hBstep b hb (by rw [← hlv]; exact hlev)
  refine Nivat.ColleReg.mem_fullSweep_iff.mpr ⟨b', hb', k + m, ?_⟩
  have hre : b + m • vl + u' = (b + u') + m • vl := by abel
  rw [hre, hk, add_smul]
  abel

/-- **The payoff: §4's covering, applied to `wedgeFull`.**

The seed is the two-sided strip `fullSweep B vl`, not the paper's `H_B(ℓ)` — see the §6 header
for why that makes this a statement about our enlargement.  The hypothesis `hBstep` is not free:
`not_wedgeFull_subset_fullSweep_union_lines` refutes the version without it. -/
theorem wedgeFull_subset_fullSweep_union_lines
    {B : Set (ℤ × ℤ)} {vl u' nℓ : ℤ × ℤ} {cz : ℤ}
    (hperp : Nivat.LE2.dot nℓ vl = 0) (hstep : Nivat.LE2.dot nℓ u' = -1)
    (hBstep : ∀ b ∈ B, cz ≤ Nivat.LE2.dot nℓ (b + u') →
      ∃ b' ∈ B, ∃ k : ℤ, b + u' = b' + k • vl) :
    Nivat.ColleReg.wedgeFull B vl u' ⊆ Nivat.ColleReg.fullSweep B vl ∪
      ⋃ i : ℕ, (Nivat.ColleReg.wedgeFull B vl u' ∩
        {y | Nivat.LE2.dot nℓ y = cz - 1 - (i : ℤ)}) := by
  rw [wedgeFull_eq_coneRegion_fullSweep]
  exact coneRegion_subset_seed_union_lines hstep (fun _ hz => add_vl_mem_fullSweep hz)
    (stepIn_fullSweep hperp hBstep)

/-- **🔴 The `fullSweep` seed does not rescue (★).**

Same witness as `not_coneRegion_subset_halfStrip_union_lines`: `nℓ = (0,1)`, `vl = (1,0)`,
`u' = (0,-1)`, `cz = 0`, `B = {(0,0), (0,2)}`, escaping point `(0,1) = (0,2) + 1•u'`.

`fullSweep B vl = {(x,0) : x ∈ ℤ} ∪ {(x,2) : x ∈ ℤ}` misses `(0,1)` for the same reason the
forward half-strip does: `B` has **no point at level 1**, and sweeping `±vl` does not create one.
The escape is a skipped level, not a `-vl` overhang, so two-sidedness is irrelevant to it.

The witness also satisfies `dot nℓ vl = 0`, `dot nℓ u' = -1`, `det u' vl = 1` and
`∀ b ∈ B, cz ≤ dot nℓ b`, so none of those repairs the statement either. -/
theorem not_wedgeFull_subset_fullSweep_union_lines :
    ∃ (B : Set (ℤ × ℤ)) (vl u' nℓ : ℤ × ℤ) (cz : ℤ),
      Nivat.LE2.dot nℓ vl = 0 ∧
      Nivat.LE2.dot nℓ u' = -1 ∧
      Nivat.det u' vl = 1 ∧
      (∀ b ∈ B, cz ≤ Nivat.LE2.dot nℓ b) ∧
      ¬ (Nivat.ColleReg.wedgeFull B vl u' ⊆ Nivat.ColleReg.fullSweep B vl ∪
            ⋃ i : ℕ, (Nivat.ColleReg.wedgeFull B vl u' ∩
              {y | Nivat.LE2.dot nℓ y = cz - 1 - (i : ℤ)})) := by
  refine ⟨({((0 : ℤ), (0 : ℤ)), ((0 : ℤ), (2 : ℤ))} : Set (ℤ × ℤ)),
    ((1 : ℤ), (0 : ℤ)), ((0 : ℤ), (-1 : ℤ)), ((0 : ℤ), (1 : ℤ)), 0,
    by simp [Nivat.LE2.dot], by simp [Nivat.LE2.dot], by simp [Nivat.det], ?_, ?_⟩
  · rintro b (rfl | rfl) <;> simp [Nivat.LE2.dot]
  · intro hsub
    have hz : ((0 : ℤ), (1 : ℤ)) ∈
        Nivat.ColleReg.wedgeFull ({((0 : ℤ), (0 : ℤ)), ((0 : ℤ), (2 : ℤ))} : Set (ℤ × ℤ))
          ((1 : ℤ), (0 : ℤ)) ((0 : ℤ), (-1 : ℤ)) := by
      refine ⟨((0 : ℤ), (2 : ℤ)), ?_, 1, by simp⟩
      exact Nivat.ColleReg.mem_fullSweep_iff.mpr ⟨((0 : ℤ), (2 : ℤ)), by simp, 0, by simp⟩
    rcases hsub hz with hstrip | hlines
    · obtain ⟨b, hb, k, hk⟩ := Nivat.ColleReg.mem_fullSweep_iff.mp hstrip
      rcases hb with rfl | rfl <;> simp [Prod.ext_iff] at hk
    · obtain ⟨i, _, hi⟩ := Set.mem_iUnion.mp hlines
      simp only [Set.mem_ofPred_eq, Nivat.LE2.dot] at hi
      omega


/-! ## §7. 🔴 The finite reduction of `hBstep` is **false** for enveloped `B`

原文：b3_colle2.txt:402 (Definition 3.2, `E(𝒮_φ)`-enveloped), :472 (`B_i ∩ ℓ_{B_i} ⊂ ℓ^{(-)}`,
the support line), :474 (item (ii)), :770 (fan adjacency).

`hBstep` (`stepIn_fullSweep`, `:409`) is equivalent — given `hperp`, `nℓ` primitive, `vl ⊥ nℓ`
primitive, so that each `nℓ`-level of `ℤ²` is a single `vl`-orbit — to

    `B` is non-empty at **every** level between `cz` and `suppVal B nℓ`.

That statement is refuted below on an `E(𝒮_φ)`-enveloped `B`, so `hBstep` does **not** follow
from envelopedness and must keep its place as a hypothesis (or the covering must change).

**The witness is a sliver**: `sliver = {(0,0), (1,0), (1,1), (2,3)}`, the lattice points of the
triangle `conv{(0,0), (1,0), (2,3)}`.  With `nℓ = (0,1)` the occupied levels are `0, 1, 3`;
**level 2 is empty** while `0 = min` and `3 = max` are both occupied.  The cross-section of the
triangle at height `2` is the segment `x ∈ [4/3, 5/3]`, of length `1/3 < 1`, and it contains no
integer.  This is exactly the "rational crossing" step failing: the segment from a low point to
a high point crosses level `2` at a non-lattice point, and lattice convexity adds nothing,
because there is no lattice point of the hull there to add.

Three hypotheses that might have been expected to rescue it are discharged **on this same
witness**, so none of them does:

* `Nivat.LE2.PosArea` — `posArea_sliver` (the points `(0,0), (1,0), (1,1)` are not collinear);
* `Nivat.IsLatticeConvexRegion` — `isLatticeConvexRegion_sliver` (`sliver` is *by construction*
  `toReal ⁻¹'` of an intersection of three closed half planes, so it contains every lattice
  point of its own hull);
* `-nℓ ∈ E B`, i.e. the support line `ℓ^{(-)}` carries a genuine **edge** and not just a vertex
  — `edge_bot_sliver` (`face sliver (0,-1) ⊇ {(0,0), (1,0)}`).  This is the hypothesis
  `Nivat.AenvfixProbe.absorbHyp_of_mem_E` needs, and the one that kills the simpler witness
  `{(0,0), (1,0), (2,0), (0,1)}` with `nℓ = (-1,3)`; it does not kill this one.

`EnvOf ↑sliver sliver` is `Nivat.LE2.enveloped_refl` — envelopedness of `B` over the generating
set `𝒮_φ` constrains `B` only through `E B = E 𝒮_φ` and edge-length dominance, and taking
`𝒮_φ := B` satisfies both by reflexivity.  ⚠ Reading, not a kernel fact: a caller who also knows
`𝒮_φ` is small (e.g. the unit square) is **not** covered by this refutation; what is refuted is
the derivation of `hBstep` from `EnvOf` alone.

⚠ **Orientation note.** `suppVal B (-nℓ) = -min` and `suppVal B nℓ = max`, so "`c` lies between
the two extreme levels" is `-c ≤ suppVal B (-nℓ) ∧ c ≤ suppVal B nℓ`.  Written with the first
inequality reversed, `suppVal B (-nℓ) ≤ -c`, the pair collapses to `c ≤ min` and the conclusion
fails for every `c < min` — `not_levels_nonempty_of_envOf_as_stated` records that separately, on
the same witness, so the substantive refutation cannot be mistaken for the sign slip. -/

/-- The sliver `{(0,0), (1,0), (1,1), (2,3)}`: the lattice points of `conv{(0,0),(1,0),(2,3)}`. -/
def sliver : Finset (ℤ × ℤ) :=
  {((0 : ℤ), (0 : ℤ)), ((1 : ℤ), (0 : ℤ)), ((1 : ℤ), (1 : ℤ)), ((2 : ℤ), (3 : ℤ))}

theorem mem_sliver {z : ℤ × ℤ} :
    z ∈ (↑sliver : Set (ℤ × ℤ)) ↔
      z = (0, 0) ∨ z = (1, 0) ∨ z = (1, 1) ∨ z = (2, 3) := by
  simp [sliver]

/-- The H-description: `sliver` is cut out by `y ≥ 0`, `3x ≥ 2y`, `3x - y ≤ 3`. -/
theorem mem_sliver_iff_ineq {z : ℤ × ℤ} :
    z ∈ (↑sliver : Set (ℤ × ℤ)) ↔
      0 ≤ z.2 ∧ 0 ≤ 3 * z.1 - 2 * z.2 ∧ 3 * z.1 - z.2 ≤ 3 := by
  simp only [mem_sliver, Prod.ext_iff]
  omega

private theorem toReal_mem_realHalfPlaneLE_iff (n : ℤ × ℤ) (c : ℤ) (z : ℤ × ℤ) :
    Nivat.toReal z ∈ Nivat.LE2.realHalfPlaneLE n c ↔ Nivat.LE2.dot n z ≤ c := by
  rw [Nivat.LE2.mem_realHalfPlaneLE]
  simp only [Nivat.toReal, Nivat.LE2.dot]
  constructor <;> intro h <;> exact_mod_cast h

/-- `sliver` is a lattice-convex region: it is `toReal ⁻¹'` of an intersection of three closed
half planes, so it contains every lattice point of its own convex hull. -/
theorem isLatticeConvexRegion_sliver :
    Nivat.IsLatticeConvexRegion (↑sliver : Set (ℤ × ℤ)) := by
  refine ⟨Nivat.LE2.realHalfPlaneLE (0, -1) 0 ∩
      (Nivat.LE2.realHalfPlaneLE (-3, 2) 0 ∩ Nivat.LE2.realHalfPlaneLE (3, -1) 3),
    (Nivat.LE2.realHalfPlaneLE_convex _ _).inter
      ((Nivat.LE2.realHalfPlaneLE_convex _ _).inter (Nivat.LE2.realHalfPlaneLE_convex _ _)),
    (Nivat.LE2.realHalfPlaneLE_isClosed _ _).inter
      ((Nivat.LE2.realHalfPlaneLE_isClosed _ _).inter
        (Nivat.LE2.realHalfPlaneLE_isClosed _ _)),
    ?_⟩
  ext z
  simp only [Set.mem_preimage, Set.mem_inter_iff, toReal_mem_realHalfPlaneLE_iff,
    mem_sliver_iff_ineq, Nivat.LE2.dot]
  norm_num

/-- `(0,0), (1,0), (1,1)` are not collinear. -/
theorem posArea_sliver : Nivat.LE2.PosArea (↑sliver : Set (ℤ × ℤ)) := by
  refine ⟨(0, 0), mem_sliver.mpr (Or.inl rfl), (1, 0), mem_sliver.mpr (Or.inr (Or.inl rfl)),
    (1, 1), mem_sliver.mpr (Or.inr (Or.inr (Or.inl rfl))), ?_⟩
  decide

/-- 原文：b3_colle2.txt:402 — Definition 3.2 constrains `B` only through `E B = E 𝒮_φ` and
edge-length dominance, both of which `𝒮_φ := B` satisfies. -/
theorem envOf_sliver :
    Nivat.LE2.EnvOf (↑sliver : Set (ℤ × ℤ)) (↑sliver : Set (ℤ × ℤ)) :=
  Nivat.LE2.enveloped_refl _ isLatticeConvexRegion_sliver

theorem mem_face_sliver_bot {z : ℤ × ℤ} (hz : z ∈ (↑sliver : Set (ℤ × ℤ)))
    (h0 : z.2 = 0) : z ∈ Nivat.LE2.face (↑sliver : Set (ℤ × ℤ)) ((0 : ℤ), (-1 : ℤ)) := by
  refine ⟨hz, fun y hy => ?_⟩
  rw [mem_sliver_iff_ineq] at hy
  simp only [Nivat.LE2.dot, h0]
  omega

/-- 原文：b3_colle2.txt:472 — the support line `ℓ^{(-)}` carries an **edge** of `B`, not just a
vertex.  `face sliver (0,-1) ⊇ {(0,0), (1,0)}`. -/
theorem edge_bot_sliver :
    ((0 : ℤ), (-1 : ℤ)) ∈ Nivat.LE2.E (↑sliver : Set (ℤ × ℤ)) := by
  refine ⟨by decide, ⟨(0, 0), mem_face_sliver_bot (mem_sliver.mpr (Or.inl rfl)) rfl,
    (1, 0), mem_face_sliver_bot (mem_sliver.mpr (Or.inr (Or.inl rfl))) rfl, by decide⟩⟩

theorem suppVal_sliver_bot :
    Nivat.LE2.suppVal (↑sliver : Set (ℤ × ℤ)) ((0 : ℤ), (-1 : ℤ)) = 0 := by
  rw [Nivat.LE2.suppVal_eq (mem_face_sliver_bot (mem_sliver.mpr (Or.inl rfl)) rfl)]
  decide

theorem suppVal_sliver_top :
    Nivat.LE2.suppVal (↑sliver : Set (ℤ × ℤ)) ((0 : ℤ), (1 : ℤ)) = 3 := by
  have hface : ((2 : ℤ), (3 : ℤ)) ∈
      Nivat.LE2.face (↑sliver : Set (ℤ × ℤ)) ((0 : ℤ), (1 : ℤ)) := by
    refine ⟨mem_sliver.mpr (Or.inr (Or.inr (Or.inr rfl))), fun y hy => ?_⟩
    rw [mem_sliver_iff_ineq] at hy
    simp only [Nivat.LE2.dot]
    omega
  rw [Nivat.LE2.suppVal_eq hface]
  decide

/-- **Level 2 is empty**, while levels `0` and `3` are occupied. -/
theorem no_level_two :
    ¬ ∃ z ∈ (↑sliver : Set (ℤ × ℤ)), Nivat.LE2.dot ((0 : ℤ), (1 : ℤ)) z = 2 := by
  rintro ⟨z, hz, hlev⟩
  rw [mem_sliver_iff_ineq] at hz
  simp only [Nivat.LE2.dot] at hlev
  omega

private theorem neg_nl : -((0 : ℤ), (1 : ℤ)) = ((0 : ℤ), (-1 : ℤ)) := by decide

/-- **🔴 A finite lattice-convex enveloped set of positive area can skip a level.**

The conclusion `∃ z ∈ B, dot nℓ z = c` is refuted at `c = 2` with every hypothesis discharged
in the kernel on the witness: envelopedness, primitivity of `nℓ`, finiteness, non-emptiness,
positive area, the edge condition `-nℓ ∈ E B`, and the two support bounds — stated both through
`suppVal` and as the unambiguous strict bracketing `∃ p ∈ B, dot nℓ p < c` /
`∃ q ∈ B, c < dot nℓ q`, so no orientation convention can be blamed. -/
theorem not_levels_nonempty_of_envOf :
    ∃ (S : Finset (ℤ × ℤ)) (B : Set (ℤ × ℤ)) (nl : ℤ × ℤ) (c : ℤ),
      Nivat.LE2.EnvOf (↑S : Set (ℤ × ℤ)) B ∧
      Nivat.Primitive nl ∧ B.Finite ∧ B.Nonempty ∧ Nivat.LE2.PosArea B ∧
      (-nl) ∈ Nivat.LE2.E (↑S : Set (ℤ × ℤ)) ∧
      -c ≤ Nivat.LE2.suppVal B (-nl) ∧ c ≤ Nivat.LE2.suppVal B nl ∧
      (∃ p ∈ B, Nivat.LE2.dot nl p < c) ∧ (∃ q ∈ B, c < Nivat.LE2.dot nl q) ∧
      ¬ (∃ z ∈ B, Nivat.LE2.dot nl z = c) := by
  refine ⟨sliver, (↑sliver : Set (ℤ × ℤ)), ((0 : ℤ), (1 : ℤ)), 2, envOf_sliver,
    isCoprime_one_right, sliver.finite_toSet, ⟨(0, 0), mem_sliver.mpr (Or.inl rfl)⟩,
    posArea_sliver, ?_, ?_, ?_, ?_, ?_, no_level_two⟩
  · rw [neg_nl]; exact edge_bot_sliver
  · rw [neg_nl, suppVal_sliver_bot]; norm_num
  · rw [suppVal_sliver_top]; norm_num
  · exact ⟨(0, 0), mem_sliver.mpr (Or.inl rfl), by decide⟩
  · exact ⟨(2, 3), mem_sliver.mpr (Or.inr (Or.inr (Or.inr rfl))), by decide⟩

/-- The same witness against the **literal** hypothesis pair `suppVal B (-nℓ) ≤ -c` and
`c ≤ suppVal B nℓ`, which says `c ≤ min` and is refuted by any `c < min` (here `c = -1`).
Kept separate so that `not_levels_nonempty_of_envOf` cannot be read as this sign slip. -/
theorem not_levels_nonempty_of_envOf_as_stated :
    ∃ (S : Finset (ℤ × ℤ)) (B : Set (ℤ × ℤ)) (nl : ℤ × ℤ) (c : ℤ),
      Nivat.LE2.EnvOf (↑S : Set (ℤ × ℤ)) B ∧
      Nivat.Primitive nl ∧ B.Finite ∧ B.Nonempty ∧ Nivat.LE2.PosArea B ∧
      (-nl) ∈ Nivat.LE2.E (↑S : Set (ℤ × ℤ)) ∧
      Nivat.LE2.suppVal B (-nl) ≤ -c ∧ c ≤ Nivat.LE2.suppVal B nl ∧
      ¬ (∃ z ∈ B, Nivat.LE2.dot nl z = c) := by
  refine ⟨sliver, (↑sliver : Set (ℤ × ℤ)), ((0 : ℤ), (1 : ℤ)), -1, envOf_sliver,
    isCoprime_one_right, sliver.finite_toSet, ⟨(0, 0), mem_sliver.mpr (Or.inl rfl)⟩,
    posArea_sliver, ?_, ?_, ?_, ?_⟩
  · rw [neg_nl]; exact edge_bot_sliver
  · rw [neg_nl, suppVal_sliver_bot]; norm_num
  · rw [suppVal_sliver_top]; norm_num
  · rintro ⟨z, hz, hlev⟩
    rw [mem_sliver_iff_ineq] at hz
    simp only [Nivat.LE2.dot] at hlev
    omega

/-- **🔴 `hBstep` itself is refuted, in the exact shape `stepIn_fullSweep` (`:409`) consumes.**

`b := (2,3)`, `u' := (0,-1)`, so `b + u' = (2,2)` sits at level `2 ≥ cz = 0`; but no point of
`B` is at level `2`, and the `ℤ·vl` tail cannot change a point's level (`hperp`), so no
`b' ∈ B`, `k : ℤ` satisfy `b + u' = b' + k • vl`.

Discharged on the witness besides envelopedness: `Primitive nℓ`, `Primitive vl`,
`dot nℓ vl = 0`, `dot nℓ u' = -1`, `det u' vl = 1` (unimodular, so no sign condition on the
determinant repairs it), `-nℓ ∈ E B`, `suppVal B (-nℓ) = -cz` (so `cz` really is the support
level of `ℓ^{(-)}`, `:472`), and `∀ b ∈ B, cz ≤ dot nℓ b`.

**Consequence for `wedgeFull_subset_fullSweep_union_lines` (`:431`)**: its `hBstep` binder is
not discharged by `EnvOf`, so the covering still has no producer from envelopedness alone. -/
theorem not_hBstep_of_envOf :
    ∃ (S : Finset (ℤ × ℤ)) (B : Set (ℤ × ℤ)) (vl u' nl : ℤ × ℤ) (cz : ℤ),
      Nivat.LE2.EnvOf (↑S : Set (ℤ × ℤ)) B ∧
      B.Finite ∧ B.Nonempty ∧ Nivat.LE2.PosArea B ∧
      Nivat.Primitive nl ∧ Nivat.Primitive vl ∧
      Nivat.LE2.dot nl vl = 0 ∧ Nivat.LE2.dot nl u' = -1 ∧ Nivat.det u' vl = 1 ∧
      (-nl) ∈ Nivat.LE2.E (↑S : Set (ℤ × ℤ)) ∧
      Nivat.LE2.suppVal B (-nl) = -cz ∧
      (∀ b ∈ B, cz ≤ Nivat.LE2.dot nl b) ∧
      ¬ (∀ b ∈ B, cz ≤ Nivat.LE2.dot nl (b + u') →
          ∃ b' ∈ B, ∃ k : ℤ, b + u' = b' + k • vl) := by
  refine ⟨sliver, (↑sliver : Set (ℤ × ℤ)), ((1 : ℤ), (0 : ℤ)), ((0 : ℤ), (-1 : ℤ)),
    ((0 : ℤ), (1 : ℤ)), 0, envOf_sliver, sliver.finite_toSet,
    ⟨(0, 0), mem_sliver.mpr (Or.inl rfl)⟩, posArea_sliver,
    isCoprime_one_right, isCoprime_one_left,
    by decide, by decide, by decide, ?_, ?_, ?_, ?_⟩
  · rw [neg_nl]; exact edge_bot_sliver
  · rw [neg_nl, suppVal_sliver_bot]; norm_num
  · intro b hb
    rw [mem_sliver_iff_ineq] at hb
    simp only [Nivat.LE2.dot]
    omega
  · intro h
    obtain ⟨b', hb', k, hk⟩ :=
      h ((2 : ℤ), (3 : ℤ)) (mem_sliver.mpr (Or.inr (Or.inr (Or.inr rfl)))) (by decide)
    rw [mem_sliver_iff_ineq] at hb'
    have h2 := congrArg Prod.snd hk
    simp at h2
    omega

/-! ## §8. The refutation does not depend on the choice of `𝒮_φ`

原文：b3_colle2.txt:402 (Definition 3.2, `E(𝒰)`-enveloped).

§7 built its witness with `Nivat.LE2.enveloped_refl`, so there `𝒮_φ = B`.  That left one
escape open: a caller who additionally knows `𝒮_φ` is *small* — forcing short edges on `B`
— would not have been refuted.  **That escape does not exist**, for two independent reasons
proved below.

The geometric fact behind both is that the fourth point `(1,1)` of `sliver` is the
**centroid** of the hull's three vertices:

    3 · ⟪n,(1,1)⟫ = ⟪n,(0,0)⟫ + ⟪n,(1,0)⟫ + ⟪n,(2,3)⟫ .

An average equals a maximum only when all three terms are equal, which for the three
vertices forces `n = 0`.  So for every `n ≠ 0` the point `(1,1)` is strictly below the
maximum, and `face sliver n = face tri n` on the nose
(`face_sliver_eq_face_tri`).  Hence `E sliver = E tri` and every edge length agrees.

1. `envOf_tri_sliver` — the **3-point** set `tri = {(0,0),(1,0),(2,3)}` envelopes `sliver`,
   and `tri ⊂ sliver` strictly (`tri_ssubset_sliver`).  So a legal `𝒮_φ` here need not be as
   big as `B`; §7's use of `enveloped_refl` was a convenience, not a crutch.

2. `not_hBstep_of_any_envOf` — `hBstep` fails for **every** `𝒮_φ` that legally envelopes
   this `B`, not merely for some.  This is what actually closes the question, and it makes
   the size of `𝒮_φ` irrelevant: the only hypothesis of §7's refutation that mentions `𝒮_φ`
   at all is the edge condition `-nℓ ∈ E 𝒮_φ`, and `Nivat.LE2.Enveloped.E_eq`
   (`LatticeEdges.lean:1656`) transports it from `B` to any enveloping `𝒮_φ` for free.
   Every other conjunct is a fact about `B = sliver` alone.

**Reading limit (读法, not a kernel fact).** These say nothing about whether some *other*
`B`, with extra properties not in Definition 3.2, satisfies `hBstep`.  They say that
`EnvOf 𝒮_φ B` together with `PosArea B`, finiteness, and `-nℓ ∈ E 𝒮_φ` does not imply it,
for any `𝒮_φ` whatsoever. -/

/-- The three vertices of the sliver's hull: a **3-point** candidate for `𝒮_φ`, strictly
smaller than `sliver` itself.

原文：b3_colle2.txt:402 — Definition 3.2 constrains `𝒰 = 𝒮_φ` only through its edge set and
edge lengths, so `𝒰` need not be lattice convex and need not contain `𝒯`. -/
def tri : Finset (ℤ × ℤ) :=
  {((0 : ℤ), (0 : ℤ)), ((1 : ℤ), (0 : ℤ)), ((2 : ℤ), (3 : ℤ))}

theorem mem_tri {z : ℤ × ℤ} :
    z ∈ (↑tri : Set (ℤ × ℤ)) ↔ z = (0, 0) ∨ z = (1, 0) ∨ z = (2, 3) := by
  simp [tri]

theorem tri_subset_sliver : (↑tri : Set (ℤ × ℤ)) ⊆ (↑sliver : Set (ℤ × ℤ)) := by
  intro z hz
  rcases mem_tri.mp hz with rfl | rfl | rfl
  · exact mem_sliver.mpr (Or.inl rfl)
  · exact mem_sliver.mpr (Or.inr (Or.inl rfl))
  · exact mem_sliver.mpr (Or.inr (Or.inr (Or.inr rfl)))

/-- `tri` is a **proper** subset: `(1,1) ∈ sliver \ tri`. -/
theorem tri_ssubset_sliver : (↑tri : Set (ℤ × ℤ)) ⊂ (↑sliver : Set (ℤ × ℤ)) := by
  refine ⟨tri_subset_sliver, fun h => ?_⟩
  have h11 := h (mem_sliver.mpr (Or.inr (Or.inr (Or.inl rfl))))
  rcases mem_tri.mp h11 with h' | h' | h' <;> exact absurd h' (by decide)

private theorem prim_ne_zero {n : ℤ × ℤ} (hp : Nivat.LE2.Prim n) :
    n ≠ ((0 : ℤ), (0 : ℤ)) := by
  rintro rfl
  simp [Nivat.LE2.Prim] at hp

/-- **The extra point `(1,1)` is the centroid of the hull, so it never lies on a face.**

`3 · ⟪n,(1,1)⟫ = ⟪n,(0,0)⟫ + ⟪n,(1,0)⟫ + ⟪n,(2,3)⟫`, and an average attains the maximum only
when the three terms agree — which forces `n = 0`.  Hence for `n ≠ 0` the faces of `sliver`
and of its three hull vertices coincide exactly, not merely up to cardinality. -/
theorem face_sliver_eq_face_tri {n : ℤ × ℤ} (hn : n ≠ ((0 : ℤ), (0 : ℤ))) :
    Nivat.LE2.face (↑sliver : Set (ℤ × ℤ)) n =
      Nivat.LE2.face (↑tri : Set (ℤ × ℤ)) n := by
  ext z
  constructor
  · rintro ⟨hz, hmax⟩
    refine ⟨?_, fun y hy => hmax y (tri_subset_sliver hy)⟩
    rcases mem_sliver.mp hz with rfl | rfl | rfl | rfl
    · exact mem_tri.mpr (Or.inl rfl)
    · exact mem_tri.mpr (Or.inr (Or.inl rfl))
    · exfalso
      have h1 := hmax (0, 0) (mem_sliver.mpr (Or.inl rfl))
      have h2 := hmax (1, 0) (mem_sliver.mpr (Or.inr (Or.inl rfl)))
      have h3 := hmax (2, 3) (mem_sliver.mpr (Or.inr (Or.inr (Or.inr rfl))))
      simp only [Nivat.LE2.dot] at h1 h2 h3
      exact hn (Prod.ext (by omega) (by omega))
    · exact mem_tri.mpr (Or.inr (Or.inr rfl))
  · rintro ⟨hz, hmax⟩
    refine ⟨tri_subset_sliver hz, fun y hy => ?_⟩
    have h1 := hmax (0, 0) (mem_tri.mpr (Or.inl rfl))
    have h2 := hmax (1, 0) (mem_tri.mpr (Or.inr (Or.inl rfl)))
    have h3 := hmax (2, 3) (mem_tri.mpr (Or.inr (Or.inr rfl)))
    rcases mem_sliver.mp hy with rfl | rfl | rfl | rfl
    · exact h1
    · exact h2
    · simp only [Nivat.LE2.dot] at h1 h2 h3 ⊢
      linarith
    · exact h3

/-- `sliver` and its hull vertices have the same edge set. -/
theorem E_sliver_eq_E_tri :
    Nivat.LE2.E (↑sliver : Set (ℤ × ℤ)) = Nivat.LE2.E (↑tri : Set (ℤ × ℤ)) := by
  ext n
  constructor
  · rintro ⟨hp, hnt⟩
    exact ⟨hp, by rwa [face_sliver_eq_face_tri (prim_ne_zero hp)] at hnt⟩
  · rintro ⟨hp, hnt⟩
    exact ⟨hp, by rwa [face_sliver_eq_face_tri (prim_ne_zero hp)]⟩

/-- **A 3-point `𝒮_φ` envelopes the sliver.**

原文：b3_colle2.txt:402 — all three clauses of Definition 3.2 hold: `sliver` is lattice
convex, every edge normal of `sliver` is one of `tri` (they are equal), each edge of `tri`
carries no more lattice points than the corresponding edge of `sliver` (the faces are
equal), and `|E(sliver)| = |E(tri)|`.

Together with `tri_ssubset_sliver` this shows §7's refutation is not an artifact of
`enveloped_refl`: a strictly smaller `𝒮_φ` is legal and changes nothing. -/
theorem envOf_tri_sliver :
    Nivat.LE2.EnvOf (↑tri : Set (ℤ × ℤ)) (↑sliver : Set (ℤ × ℤ)) := by
  refine ⟨⟨isLatticeConvexRegion_sliver, fun n hn => ?_⟩, ?_⟩
  · have hp : Nivat.LE2.Prim n := hn.1
    exact ⟨E_sliver_eq_E_tri ▸ hn, le_of_eq (by rw [face_sliver_eq_face_tri (prim_ne_zero hp)])⟩
  · rw [E_sliver_eq_E_tri]

/-- **Every** legal `𝒮_φ` for the sliver has `(0,-1) = -nℓ` as an edge normal.

原文：b3_colle2.txt:472 — the support line `ℓ^{(-)}` carries an edge.  By
`Nivat.LE2.Enveloped.E_eq` (`LatticeEdges.lean:1656`) the edge set of an enveloped set
equals that of its envelope, so this hypothesis is free for any `𝒮_φ` at all, not just for
the two exhibited above. -/
theorem edge_bot_of_envOf_sliver {S : Finset (ℤ × ℤ)}
    (hS : Nivat.LE2.EnvOf (↑S : Set (ℤ × ℤ)) (↑sliver : Set (ℤ × ℤ))) :
    ((0 : ℤ), (-1 : ℤ)) ∈ Nivat.LE2.E (↑S : Set (ℤ × ℤ)) := by
  rw [← Nivat.LE2.Enveloped.E_eq (Nivat.LE2.finite_E_of_finite S.finite_toSet) hS]
  exact edge_bot_sliver

private theorem neg_nl' : -((0 : ℤ), (1 : ℤ)) = ((0 : ℤ), (-1 : ℤ)) := by decide

/-- **🔴 `hBstep` fails for EVERY legal `𝒮_φ`, not merely for one.**

This is the universally quantified form of `not_hBstep_of_envOf` (`:675`): `S` ranges over
**all** finite sets that envelope the witness, and the refutation holds for each.  Producers
exist, so the statement is not vacuous — `envOf_sliver` (`𝒮_φ = B`, 4 points) and
`envOf_tri_sliver` (`𝒮_φ = tri`, 3 points) are both legal.

Every conjunct is discharged in the kernel on the witness, exactly as in `:675`; the only
one that mentions `S` is `-nℓ ∈ E ↑S`, supplied by `edge_bot_of_envOf_sliver`.

**Consequence.** No side knowledge about `𝒮_φ` — its size, its edge lengths, its shape —
can repair `hBstep`, because `𝒮_φ` is quantified away.  Whatever a producer of `hBstep`
uses, it is not Definition 3.2 (`:402`). -/
theorem not_hBstep_of_any_envOf {S : Finset (ℤ × ℤ)}
    (hS : Nivat.LE2.EnvOf (↑S : Set (ℤ × ℤ)) (↑sliver : Set (ℤ × ℤ))) :
    ∃ (vl u' nl : ℤ × ℤ) (cz : ℤ),
      (↑sliver : Set (ℤ × ℤ)).Finite ∧ (↑sliver : Set (ℤ × ℤ)).Nonempty ∧
      Nivat.LE2.PosArea (↑sliver : Set (ℤ × ℤ)) ∧
      Nivat.Primitive nl ∧ Nivat.Primitive vl ∧
      Nivat.LE2.dot nl vl = 0 ∧ Nivat.LE2.dot nl u' = -1 ∧ Nivat.det u' vl = 1 ∧
      (-nl) ∈ Nivat.LE2.E (↑S : Set (ℤ × ℤ)) ∧
      Nivat.LE2.suppVal (↑sliver : Set (ℤ × ℤ)) (-nl) = -cz ∧
      (∀ b ∈ (↑sliver : Set (ℤ × ℤ)), cz ≤ Nivat.LE2.dot nl b) ∧
      ¬ (∀ b ∈ (↑sliver : Set (ℤ × ℤ)), cz ≤ Nivat.LE2.dot nl (b + u') →
          ∃ b' ∈ (↑sliver : Set (ℤ × ℤ)), ∃ k : ℤ, b + u' = b' + k • vl) := by
  refine ⟨((1 : ℤ), (0 : ℤ)), ((0 : ℤ), (-1 : ℤ)), ((0 : ℤ), (1 : ℤ)), 0,
    sliver.finite_toSet, ⟨(0, 0), mem_sliver.mpr (Or.inl rfl)⟩, posArea_sliver,
    isCoprime_one_right, isCoprime_one_left,
    by decide, by decide, by decide, ?_, ?_, ?_, ?_⟩
  · rw [neg_nl']; exact edge_bot_of_envOf_sliver hS
  · rw [neg_nl', suppVal_sliver_bot]; norm_num
  · intro b hb
    rw [mem_sliver_iff_ineq] at hb
    simp only [Nivat.LE2.dot]
    omega
  · intro h
    obtain ⟨b', hb', k, hk⟩ :=
      h ((2 : ℤ), (3 : ℤ)) (mem_sliver.mpr (Or.inr (Or.inr (Or.inr rfl)))) (by decide)
    rw [mem_sliver_iff_ineq] at hb'
    have h2 := congrArg Prod.snd hk
    simp at h2
    omega

/-! ## §9. The line-level covering on `fullSweep` is the **same** condition, not a weaker one

原文：b3_colle2.txt:792-804 (Claim 4.6's induction over the lines `l_i`).

The natural repair after §7–§8 is to stop asking a point-level question about `B` and ask a
line-level question about the two-sided strip instead: is every level between `cz` and
`suppVal B nℓ` met by `fullSweep B vl`?  `fullSweep` is closed under `±vl`, so it is a union
of full lattice lines, and one might hope it fills levels that `B` skips.

**It does not, and the reason is `hperp` itself.**  `dot nℓ vl = 0` says the sweep direction
lies *inside* a level, so adding `m • vl` never changes `⟪nℓ,·⟫`.  The occupied levels of
`fullSweep B vl` are therefore exactly the occupied levels of `B` — `nonempty_level_fullSweep_iff`
below is an **iff**, so this is not a one-sided bound that some cleverer argument could improve.

Consequence (`hcover_fullSweep_iff`): the line-level hypothesis on `fullSweep B vl` is
*logically equivalent* to the point-level level-nonemptiness of `B` that §7 refuted.  It is a
restatement, not a weakening, and `not_hcover_fullSweep_of_any_envOf` kills it on the same
witness, for every `𝒮_φ`.

**What this does and does not settle.**  It settles that `fullSweep` is not the fix: any
covering hypothesis phrased through `⟪nℓ,·⟫`-levels of `B` or of its `vl`-sweep is dead, whatever
the seed.  It does **not** say Claim 4.6 is false.  A genuine line-level reading would index the
induction by the lines `l_i` of `:792` themselves and let the region `𝓡_{ι-1}` — which is swept
by `u'` as well as `vl`, and so is *not* confined to `B`'s levels — supply the points; the escape
hatch is that `u'` moves the level (`dot nℓ u' = -1`), and nothing here touches that. -/

/-- **Sweeping along `vl` cannot create a new `nℓ`-level.**

原文：b3_colle2.txt:777 — `H_B(ℓ)` sweeps along `v⃗_ℓ`, and `nℓ ⊥ v⃗_ℓ`, so the sweep moves
points *within* a level.  Stated as an `iff` so that no strengthening of the left side is
possible: a level of the two-sided strip is occupied exactly when the corresponding level of
the seed `B` is. -/
theorem nonempty_level_fullSweep_iff {B : Set (ℤ × ℤ)} {vl nℓ : ℤ × ℤ}
    (hperp : Nivat.LE2.dot nℓ vl = 0) (c : ℤ) :
    (Nivat.ColleReg.fullSweep B vl ∩ {z | Nivat.LE2.dot nℓ z = c}).Nonempty ↔
      ∃ b ∈ B, Nivat.LE2.dot nℓ b = c := by
  constructor
  · rintro ⟨z, hz, hlev⟩
    obtain ⟨b, hb, m, rfl⟩ := Nivat.ColleReg.mem_fullSweep_iff.mp hz
    refine ⟨b, hb, ?_⟩
    have : Nivat.LE2.dot nℓ (b + m • vl) = Nivat.LE2.dot nℓ b := by
      simp only [Nivat.LE2.dot_add, dot_zsmul, hperp]
      ring
    rw [← this]
    exact hlev
  · rintro ⟨b, hb, hc⟩
    exact ⟨b, Nivat.ColleReg.mem_fullSweep_iff.mpr ⟨b, hb, 0, by simp⟩, hc⟩

/-- **The line-level covering hypothesis is a restatement of the point-level one.**

Left side: every level in `[cz, suppVal B nℓ]` is met by the two-sided strip `fullSweep B vl`.
Right side: every such level is met by `B` itself — the condition refuted in §7. -/
theorem hcover_fullSweep_iff {B : Set (ℤ × ℤ)} {vl nℓ : ℤ × ℤ} {cz : ℤ}
    (hperp : Nivat.LE2.dot nℓ vl = 0) :
    (∀ c : ℤ, cz ≤ c → c ≤ Nivat.LE2.suppVal B nℓ →
        (Nivat.ColleReg.fullSweep B vl ∩ {z | Nivat.LE2.dot nℓ z = c}).Nonempty) ↔
      (∀ c : ℤ, cz ≤ c → c ≤ Nivat.LE2.suppVal B nℓ → ∃ b ∈ B, Nivat.LE2.dot nℓ b = c) := by
  constructor
  · intro h c h1 h2
    exact (nonempty_level_fullSweep_iff hperp c).mp (h c h1 h2)
  · intro h c h1 h2
    exact (nonempty_level_fullSweep_iff hperp c).mpr (h c h1 h2)

/-- **🔴 The line-level covering on `fullSweep` fails, for every legal `𝒮_φ`.**

Same witness as §7–§8, same missing level `c = 2`, now against the `fullSweep` form of the
hypothesis: `cz = 0 ≤ 2 ≤ 3 = suppVal sliver nℓ`, yet `fullSweep sliver vl` has no point at
level `2`, because `dot nℓ vl = 0` means the sweep stays inside each level.

Every side condition is discharged on the witness as in `not_hBstep_of_any_envOf` (`:857`),
and `S` is again universally quantified, so no property of `𝒮_φ` repairs it.

**Consequence.** Replacing the point-level `hBstep` of `stepIn_fullSweep` (`:409`) with a
line-level covering on `fullSweep B vl` does not produce a provable hypothesis: by
`hcover_fullSweep_iff` the two are equivalent, so the replacement dies with the original. -/
theorem not_hcover_fullSweep_of_any_envOf {S : Finset (ℤ × ℤ)}
    (hS : Nivat.LE2.EnvOf (↑S : Set (ℤ × ℤ)) (↑sliver : Set (ℤ × ℤ))) :
    ∃ (vl u' nl : ℤ × ℤ) (cz : ℤ),
      (↑sliver : Set (ℤ × ℤ)).Finite ∧ (↑sliver : Set (ℤ × ℤ)).Nonempty ∧
      Nivat.LE2.PosArea (↑sliver : Set (ℤ × ℤ)) ∧
      Nivat.Primitive nl ∧ Nivat.Primitive vl ∧
      Nivat.LE2.dot nl vl = 0 ∧ Nivat.LE2.dot nl u' = -1 ∧ Nivat.det u' vl = 1 ∧
      (-nl) ∈ Nivat.LE2.E (↑S : Set (ℤ × ℤ)) ∧
      Nivat.LE2.suppVal (↑sliver : Set (ℤ × ℤ)) (-nl) = -cz ∧
      (∀ b ∈ (↑sliver : Set (ℤ × ℤ)), cz ≤ Nivat.LE2.dot nl b) ∧
      ¬ (∀ c : ℤ, cz ≤ c → c ≤ Nivat.LE2.suppVal (↑sliver : Set (ℤ × ℤ)) nl →
          (Nivat.ColleReg.fullSweep (↑sliver : Set (ℤ × ℤ)) vl ∩
            {z | Nivat.LE2.dot nl z = c}).Nonempty) := by
  refine ⟨((1 : ℤ), (0 : ℤ)), ((0 : ℤ), (-1 : ℤ)), ((0 : ℤ), (1 : ℤ)), 0,
    sliver.finite_toSet, ⟨(0, 0), mem_sliver.mpr (Or.inl rfl)⟩, posArea_sliver,
    isCoprime_one_right, isCoprime_one_left,
    by decide, by decide, by decide, ?_, ?_, ?_, ?_⟩
  · rw [neg_nl']; exact edge_bot_of_envOf_sliver hS
  · rw [neg_nl', suppVal_sliver_bot]; norm_num
  · intro b hb
    rw [mem_sliver_iff_ineq] at hb
    simp only [Nivat.LE2.dot]
    omega
  · intro h
    have h2 := h 2 (by norm_num) (by rw [suppVal_sliver_top]; norm_num)
    rw [nonempty_level_fullSweep_iff (by decide)] at h2
    exact no_level_two h2

/-! ## §10. The floor: a legal `𝒮_φ` here has **three** points, and three is attained

原文：b3_colle2.txt:402 (Definition 3.2, `E(𝒰)`-enveloped).

§8 makes the *size* of `𝒮_φ` irrelevant to the refutation.  This section records what that size
can be, so a later round can cite it as a kernel fact instead of a reading.

**The argument runs through the cardinality conjunct, not through the face bound.**
Definition 3.2 bounds the faces of `𝒰` from **above** by those of `𝒯` (`|w ∩ 𝒰| ≤ |ϖ ∩ 𝒯|`),
so the bound by itself permits a face of `𝒮_φ` to be a single point — in which case that normal
is not an edge of `𝒮_φ` at all and `|E 𝒮_φ|` drops below `|E B|`.  What forbids that is the
other conjunct, `|E 𝒯| = |E 𝒰|`: with `E 𝒯 ⊆ E 𝒰` and finiteness it yields
`E 𝒮_φ = E B` (`Nivat.LE2.Enveloped.E_eq`, `LatticeEdges.lean:1656`), so **every** edge normal
of `B` is an edge normal of `𝒮_φ` and therefore has a nontrivial face there.

Two of the three edge normals of `B = sliver` suffice.  `(0,-1)` and `(3,-1)` are not parallel,
while a set of at most two points has every nontrivial face equal to the whole set; so both
normals would have to annihilate the same difference vector, forcing it to be zero and the two
points to coincide.

- `three_le_card_of_envOf_sliver` — every legal `𝒮_φ` has at least three points.
- `exists_envOf_sliver_card_three` — three is attained, by `tri`.

**Reading limit (读法, not a kernel fact).** The floor is `3` for *this* `B`; nothing here says
what it is in general, and nothing here is used by §7–§9. -/

/-- Every point of `sliver` satisfies `3x - y ≤ 3`, so a point with equality is on the face. -/
theorem mem_face_sliver_right {z : ℤ × ℤ} (hz : z ∈ (↑sliver : Set (ℤ × ℤ)))
    (h3 : 3 * z.1 - z.2 = 3) :
    z ∈ Nivat.LE2.face (↑sliver : Set (ℤ × ℤ)) ((3 : ℤ), (-1 : ℤ)) := by
  refine ⟨hz, fun y hy => ?_⟩
  rw [mem_sliver_iff_ineq] at hy
  simp only [Nivat.LE2.dot]
  omega

/-- 原文：b3_colle2.txt:402 — the second edge of `sliver`:
`face sliver (3,-1) ⊇ {(1,0), (2,3)}`, and `(3,-1)` is not parallel to `(0,-1)`. -/
theorem edge_right_sliver :
    ((3 : ℤ), (-1 : ℤ)) ∈ Nivat.LE2.E (↑sliver : Set (ℤ × ℤ)) := by
  refine ⟨by decide, ⟨(1, 0),
    mem_face_sliver_right (mem_sliver.mpr (Or.inr (Or.inl rfl))) (by norm_num),
    (2, 3),
    mem_face_sliver_right (mem_sliver.mpr (Or.inr (Or.inr (Or.inr rfl)))) (by norm_num),
    by decide⟩⟩

/-- An edge normal has two distinct points of the set at the same level: both lie on the face,
and each dominates the other. -/
private theorem exists_edge_pair {X : Set (ℤ × ℤ)} {n : ℤ × ℤ} (hn : n ∈ Nivat.LE2.E X) :
    ∃ a ∈ X, ∃ b ∈ X, a ≠ b ∧ Nivat.LE2.dot n a = Nivat.LE2.dot n b := by
  obtain ⟨-, a, ha, b, hb, hab⟩ := hn
  exact ⟨a, ha.1, b, hb.1, hab, le_antisymm (hb.2 a ha.1) (ha.2 b hb.1)⟩

/-- **A legal `𝒮_φ` for this `B` cannot have fewer than three points.**

原文：b3_colle2.txt:402 — via the cardinality conjunct of Definition 3.2, which is what puts
both edge normals of `B` into `E 𝒮_φ`; the edge-length clause alone would not. -/
theorem three_le_card_of_envOf_sliver {S : Finset (ℤ × ℤ)}
    (hS : Nivat.LE2.EnvOf (↑S : Set (ℤ × ℤ)) (↑sliver : Set (ℤ × ℤ))) :
    3 ≤ S.card := by
  have hE : Nivat.LE2.E (↑sliver : Set (ℤ × ℤ)) = Nivat.LE2.E (↑S : Set (ℤ × ℤ)) :=
    Nivat.LE2.Enveloped.E_eq (Nivat.LE2.finite_E_of_finite S.finite_toSet) hS
  have hbot : ((0 : ℤ), (-1 : ℤ)) ∈ Nivat.LE2.E (↑S : Set (ℤ × ℤ)) := by
    rw [← hE]; exact edge_bot_sliver
  have hright : ((3 : ℤ), (-1 : ℤ)) ∈ Nivat.LE2.E (↑S : Set (ℤ × ℤ)) := by
    rw [← hE]; exact edge_right_sliver
  obtain ⟨a, ha, b, hb, hab, h1⟩ := exists_edge_pair hbot
  obtain ⟨c, hc, d, hd, hcd, h2⟩ := exists_edge_pair hright
  by_contra hcard
  have hsub : ({a, b} : Finset (ℤ × ℤ)) ⊆ S := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact Finset.mem_coe.mp ha
    · exact Finset.mem_coe.mp hb
  have hpair : ({a, b} : Finset (ℤ × ℤ)) = S :=
    Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_pair hab]; omega)
  have hcm : c = a ∨ c = b := by
    have hcS : c ∈ ({a, b} : Finset (ℤ × ℤ)) := by rw [hpair]; exact Finset.mem_coe.mp hc
    simpa using hcS
  have hdm : d = a ∨ d = b := by
    have hdS : d ∈ ({a, b} : Finset (ℤ × ℤ)) := by rw [hpair]; exact Finset.mem_coe.mp hd
    simpa using hdS
  have h2' : Nivat.LE2.dot ((3 : ℤ), (-1 : ℤ)) a = Nivat.LE2.dot ((3 : ℤ), (-1 : ℤ)) b := by
    rcases hcm with hcm | hcm <;> rcases hdm with hdm | hdm
    · exact absurd (hcm.trans hdm.symm) hcd
    · rw [← hcm, ← hdm]; exact h2
    · rw [← hcm, ← hdm]; exact h2.symm
    · exact absurd (hcm.trans hdm.symm) hcd
  refine hab ?_
  simp only [Nivat.LE2.dot] at h1 h2'
  exact Prod.ext (by omega) (by omega)

theorem card_tri : tri.card = 3 := by decide

/-- **Three is attained**, so `three_le_card_of_envOf_sliver` is sharp. -/
theorem exists_envOf_sliver_card_three :
    ∃ S : Finset (ℤ × ℤ),
      Nivat.LE2.EnvOf (↑S : Set (ℤ × ℤ)) (↑sliver : Set (ℤ × ℤ)) ∧ S.card = 3 :=
  ⟨tri, envOf_tri_sliver, card_tri⟩

/-! ## §11. 🟢 The two-ray cone occupies **every** level, so the hole that killed `hBstep` is gone

原文：b3_colle2.txt:780 (`𝓡_{ι-1} := {g + t·v⃗_{ℓ_{ι-1}} : g ∈ H_B(ℓ), t ∈ ℤ₊}`), `:792-804`
(the line induction `A₁ := 𝓡_{ι-1} ∩ l₁`, `l₂ := l₁^{(-)}`, "proceeding this way").

§7–§9 close the negative side: a lattice-convex, positive-area, enveloped `B` can skip an
`nℓ`-level (`no_level_two`), no `𝒮_φ` repairs it (`not_hBstep_of_any_envOf`, `:857`), and
sweeping along `vl` cannot fill the hole because `hperp` puts `vl` **inside** a level
(`nonempty_level_fullSweep_iff`, `:919`).

The cone is the first object in this file that is not confined to `B`'s rows.  Because
`dot nℓ u' = -1`, the `u'`-ray steps **down one level per step** (`dot_eq_of_mem_coneRegion`,
`ConeRegion.lean:132`), so starting from a point of `B` at the top level every level below it is
reached.  The occupied levels of `coneRegion B vl u'` are therefore *all* of
`{c | c ≤ suppVal B nℓ}` — contiguous, with no holes, whatever `B` looks like.

That is why `:792-804` never needed anything like `hBstep`: it draws `A₁` from `𝓡_{ι-1}`, while
every encoding we tried demanded the witness come back from `B` or from `fullSweep B vl`, both of
which are confined to `B`'s own rows.

⚠ **Reading limit (`PROTOCOL.md` §15).**  This removes exactly one obstruction — the skipped
level that refutes `hBstep` and its `fullSweep` restatement.  It does **not** give `hconv`,
`hbase` or `hline` of `WedgeResidualR` (`L1Claim.lean:928`), and nothing here says the covering
`coneRegion_subset_halfStrip_union_lines` (`:289`) acquires a producer: that one needs the
**half-strip** to absorb the step, which is a different claim and is refuted for the half-strip by
`not_coneRegion_subset_halfStrip_union_lines` (`:166`). -/

/-- **Every level at or below the top of `B` is occupied in the cone.**

原文：b3_colle2.txt:780, `:804`.  Take the `B`-point `b` attaining `suppVal B nℓ` and step
`t = suppVal B nℓ - c` times along `u'`; each step drops the level by exactly one (`hu'`), so the
result sits at level `c`, and it is in the cone with `s = 0`.

⚠ `hperp` is **not used** and is therefore taken as `_hperp`, following the house convention of
`coneRegion_subset_halfStrip_union_lines_of_lower_bound` (`:307`): the cone fills every level
whether or not `nℓ ⊥ vl`.  `hperp` is the intended reading of `nℓ` — it is what makes the level
sets `{z | dot nℓ z = c}` be the lines `l_i` parallel to `ℓ` (`:796`) — so it is kept in the
signature rather than dropped. -/
theorem nonempty_level_coneRegion {B : Set (ℤ × ℤ)} {vl u' nℓ : ℤ × ℤ}
    (hne : B.Nonempty) (_hperp : Nivat.LE2.dot nℓ vl = 0)
    (hu' : Nivat.LE2.dot nℓ u' = -1) (hfin : B.Finite)
    {c : ℤ} (hc : c ≤ Nivat.LE2.suppVal B nℓ) :
    (coneRegion B vl u' ∩ {z | Nivat.LE2.dot nℓ z = c}).Nonempty := by
  obtain ⟨b, hb, hbeq⟩ := Nivat.LE2.exists_suppVal_eq hfin hne nℓ
  refine ⟨b + ((Nivat.LE2.suppVal B nℓ - c).toNat : ℤ) • u', ?_, ?_⟩
  · exact Nivat.ConeRegion.mem_coneRegion_iff.mpr
      ⟨b, hb, 0, (Nivat.LE2.suppVal B nℓ - c).toNat, by simp⟩
  · show Nivat.LE2.dot nℓ (b + ((Nivat.LE2.suppVal B nℓ - c).toNat : ℤ) • u') = c
    rw [Nivat.LE2.dot_add, dot_zsmul, hu', hbeq]
    omega

/-- **The covering hypothesis of §9, on the cone: free.**

`hcover_fullSweep_iff` (`:939`) shows the same hypothesis on `fullSweep B vl` is *equivalent* to
point-level level-nonemptiness of `B`, which `not_hcover_fullSweep_of_any_envOf` (`:962`) refutes.
On the cone it needs no hypothesis beyond finiteness, non-emptiness and `hu'` — the contrast
between the two is the whole content of this section. -/
theorem hcover_coneRegion {B : Set (ℤ × ℤ)} {vl u' nℓ : ℤ × ℤ}
    (hne : B.Nonempty) (hperp : Nivat.LE2.dot nℓ vl = 0)
    (hu' : Nivat.LE2.dot nℓ u' = -1) (hfin : B.Finite) (cz : ℤ) :
    ∀ c : ℤ, cz ≤ c → c ≤ Nivat.LE2.suppVal B nℓ →
      (coneRegion B vl u' ∩ {z | Nivat.LE2.dot nℓ z = c}).Nonempty :=
  fun _ _ hc => nonempty_level_coneRegion hne hperp hu' hfin hc

/-- **`hBstep`'s own shape, with the cone as the witness set: true, and trivially so.**

Compare `not_hBstep_of_any_envOf` (`:857`), which refutes exactly this statement with `B` in place
of `coneRegion B vl u'`.  The witness is `b' := b + u'` with `k = 0`: the cone is closed under
`u'` by construction (`Nivat.ConeRegion.add_u'_mem`, `ConeRegion.lean:107`), so no level argument
is needed at all.  `cz` and the level hypothesis are carried only so the shape matches. -/
theorem stepIn_coneRegion {B : Set (ℤ × ℤ)} {vl u' nℓ : ℤ × ℤ} {cz : ℤ} :
    ∀ b ∈ coneRegion B vl u', cz ≤ Nivat.LE2.dot nℓ (b + u') →
      ∃ b' ∈ coneRegion B vl u', ∃ k : ℤ, b + u' = b' + k • vl :=
  fun b hb _ => ⟨b + u', Nivat.ConeRegion.add_u'_mem hb, 0, by simp⟩

/-- **The cone is the union of its own level lines, with no seed and no hypothesis on `B`
beyond finiteness and non-emptiness.**

原文：b3_colle2.txt:792-804 — this is the family `l₁, l₂, …` the induction walks over, indexed
downward from the top level of `B`.  Every cone point is at level `≤ suppVal B nℓ`
(`dot_le_suppVal_of_mem_coneRegion`, `ConeRegion.lean:153`), so it lies on line `i` for exactly
one `i`; and by `nonempty_level_coneRegion` every one of those lines is non-empty.

Contrast `coneRegion_subset_seed_union_lines` (`:225`), whose seed `S` costs an `hstepIn`
hypothesis: here there is no seed, so nothing is owed.  ⚠ That also means this decomposition
carries no periodicity information — it is the index set of the induction, not a step of it. -/
theorem coneRegion_subset_union_levels {B : Set (ℤ × ℤ)} {vl u' nℓ : ℤ × ℤ}
    (hfin : B.Finite) (hne : B.Nonempty)
    (hperp : Nivat.LE2.dot nℓ vl = 0) (hu' : Nivat.LE2.dot nℓ u' = -1) :
    coneRegion B vl u' ⊆
      ⋃ i : ℕ, (coneRegion B vl u' ∩
        {y | Nivat.LE2.dot nℓ y = Nivat.LE2.suppVal B nℓ - (i : ℤ)}) := by
  intro z hz
  have hle : Nivat.LE2.dot nℓ z ≤ Nivat.LE2.suppVal B nℓ :=
    Nivat.ConeRegion.dot_le_suppVal_of_mem_coneRegion hfin hne hperp hu' hz
  refine Set.mem_iUnion.mpr ⟨(Nivat.LE2.suppVal B nℓ - Nivat.LE2.dot nℓ z).toNat, hz, ?_⟩
  show Nivat.LE2.dot nℓ z
    = Nivat.LE2.suppVal B nℓ - ((Nivat.LE2.suppVal B nℓ - Nivat.LE2.dot nℓ z).toNat : ℤ)
  omega

end Nivat.ConeLines

#print axioms Nivat.ConeLines.halfStrip_eq_sweep
#print axioms Nivat.ConeLines.coneRegion_eq_sweep_halfStrip
#print axioms Nivat.ConeLines.coneRegion_eq_upper_union_lines
#print axioms Nivat.ConeLines.not_coneRegion_subset_halfStrip_union_lines
#print axioms Nivat.ConeLines.coneRegion_subset_halfStrip_union_lines
#print axioms Nivat.ConeLines.coneRegion_subset_halfStrip_union_lines_of_lower_bound
#print axioms Nivat.ConeLines.halfStrip_subset_fullSweep
#print axioms Nivat.ConeLines.coneRegion_subset_wedgeFull
#print axioms Nivat.ConeLines.not_wedgeFull_subset_coneRegion
#print axioms Nivat.ConeLines.coneRegion_eq_sweep_of_add_vl_mem
#print axioms Nivat.ConeLines.coneRegion_halfStrip
#print axioms Nivat.ConeLines.coneRegion_subset_seed_union_lines
#print axioms Nivat.ConeLines.add_vl_mem_fullSweep
#print axioms Nivat.ConeLines.wedgeFull_eq_coneRegion_fullSweep
#print axioms Nivat.ConeLines.coneRegion_subset_coneRegion_fullSweep
#print axioms Nivat.ConeLines.stepIn_fullSweep
#print axioms Nivat.ConeLines.wedgeFull_subset_fullSweep_union_lines
#print axioms Nivat.ConeLines.not_wedgeFull_subset_fullSweep_union_lines
#print axioms Nivat.ConeLines.mem_sliver
#print axioms Nivat.ConeLines.mem_sliver_iff_ineq
#print axioms Nivat.ConeLines.isLatticeConvexRegion_sliver
#print axioms Nivat.ConeLines.posArea_sliver
#print axioms Nivat.ConeLines.envOf_sliver
#print axioms Nivat.ConeLines.mem_face_sliver_bot
#print axioms Nivat.ConeLines.edge_bot_sliver
#print axioms Nivat.ConeLines.suppVal_sliver_bot
#print axioms Nivat.ConeLines.suppVal_sliver_top
#print axioms Nivat.ConeLines.no_level_two
#print axioms Nivat.ConeLines.not_levels_nonempty_of_envOf
#print axioms Nivat.ConeLines.not_levels_nonempty_of_envOf_as_stated
#print axioms Nivat.ConeLines.not_hBstep_of_envOf
#print axioms Nivat.ConeLines.mem_tri
#print axioms Nivat.ConeLines.tri_subset_sliver
#print axioms Nivat.ConeLines.tri_ssubset_sliver
#print axioms Nivat.ConeLines.face_sliver_eq_face_tri
#print axioms Nivat.ConeLines.E_sliver_eq_E_tri
#print axioms Nivat.ConeLines.envOf_tri_sliver
#print axioms Nivat.ConeLines.edge_bot_of_envOf_sliver
#print axioms Nivat.ConeLines.not_hBstep_of_any_envOf
#print axioms Nivat.ConeLines.nonempty_level_fullSweep_iff
#print axioms Nivat.ConeLines.hcover_fullSweep_iff
#print axioms Nivat.ConeLines.not_hcover_fullSweep_of_any_envOf
#print axioms Nivat.ConeLines.mem_face_sliver_right
#print axioms Nivat.ConeLines.edge_right_sliver
#print axioms Nivat.ConeLines.three_le_card_of_envOf_sliver
#print axioms Nivat.ConeLines.card_tri
#print axioms Nivat.ConeLines.exists_envOf_sliver_card_three
#print axioms Nivat.ConeLines.nonempty_level_coneRegion
#print axioms Nivat.ConeLines.hcover_coneRegion
#print axioms Nivat.ConeLines.stepIn_coneRegion
#print axioms Nivat.ConeLines.coneRegion_subset_union_levels
