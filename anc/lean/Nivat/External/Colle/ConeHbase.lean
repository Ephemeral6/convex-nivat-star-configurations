/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.SweepLines
import Nivat.External.Colle.ConeLines

/-!
# `ConeHbase` — wiring the line-by-line sweep into `chainFull`

原文：b3_colle2.txt:792-804 (Claim 4.6's line induction).

The engine is `Nivat.SweepLines.hbase_at_of_sweep_lines` (`SweepLines.lean:177`); the covering
is `Nivat.ConeLines` (`ConeLines.lean`).  This file joins them and reports, in the kernel, the
one place where the shapes do **not** join.

## The shape mismatch, stated precisely

`hbase_at_of_sweep_lines` needs

    hD  : ∀ z ∈ D, (T e ξ) z = T (c • vl) (T e ξ) z
    hKL : chainFull B vl u' b₀ k ⊆ D ∪ (⋃ i, lines i)

with **one and the same `D`**.  The two ends supply different `D`:

* `Nivat.L1Line0.exists_hD_of_case1` (`L1Line0.lean:527`) produces `hD` only on
  `halfStrip B vl` — the paper's forward half-strip `H_B(ℓ)` (`b3_colle2.txt:414`, `t ∈ ℤ₊`).
* `chainFull B vl u' b₀ k = L1Region.cut (wedgeFull B vl u') (expNormal u' vl) (expLevel …)`
  (`L1RegionBuild.lean:305`), and `wedgeFull` sweeps `±vl` (`L1RegionBuild.lean:230`).  The cut
  is by `expNormal u' vl`, which satisfies `dot (expNormal u' vl) vl = 1` and
  `dot (expNormal u' vl) u' = 0` (`L1RegionBuild.lean:287`, `:295`) — so it bounds the `vl`
  coordinate **from below at `dot (expNormal u' vl) b₀ - k`**, not at `0`.  It therefore does
  *not* restore forward-only `vl`: `chainFull` still contains `-vl` translates of `B`.

`not_chainFull_subset_halfStrip_union_lines` below is the kernel witness: with
`B = {(0,0)}`, `vl = (1,0)`, `u' = (0,-1)`, `b₀ = (0,0)`, `k = 1`, the point `(-1,0)` lies in
`chainFull B vl u' b₀ 1`, is not in `halfStrip B vl`, and sits at `nℓ`-level `0`, hence on **no**
line `{dot nℓ · = cz - 1 - i}`.  All of `ConeLines`' hypotheses hold at that witness —
`det u' vl = 1`, `dot nℓ vl = 0`, `dot nℓ u' = -1`, `∀ b ∈ B, cz ≤ dot nℓ b`, `b₀ ∈ B`,
`B.Finite`, and `hstepIn` (vacuously) — so **the obstruction is not `hstepIn` and not the
covering**; it is that `chainFull ⊄ coneRegion`.

⚠ 这否掉的是 `hKL` 的 `D := halfStrip B vl` 那一版，**不是** `hbase_at_of_sweep_lines`，
也不是 `ConeLines` 的任何一条。派工提示（`LEAF-C` 的教训）：报「陈述是假的」时要说清否的是哪一版
签名的闭包。

## What does join

Taking `D := fullSweep B vl` (the two-sided strip) makes both ends match:
`hbase_of_cone_lines` below is `hbase_at_of_sweep_lines` fed by
`Nivat.ConeLines.wedgeFull_subset_fullSweep_union_lines`, and it type-checks.  The price is
exactly one hypothesis upgrade, and it is named: **`hD` must hold on `fullSweep B vl`, not just
on `halfStrip B vl`.**  That is a strictly stronger statement about `T e ξ` than Case 1 gives,
and nothing in this file discharges it.

原文：b3_colle2.txt:777-780 — Collé's `H_B(ℓ)` really is one-directional, so the upgraded `hD`
is a statement about **our** enlarged seed.  Two honest exits, neither taken here (both are
integrator decisions, outside this file):
1. strengthen `exists_hD_of_case1` to the two-sided strip, or
2. restate `chainFull` over `coneRegion` instead of `wedgeFull`, i.e. change
   `L1RegionBuild.lean:305` and `WedgeResidualR` (`L1Claim.lean:928`).
-/

set_option autoImplicit false

namespace Nivat.ConeHbase

open Nivat Nivat.LE2 Nivat.ColleReg

/-! ### §1  `chainFull` is a cut of `wedgeFull` -/

/-- `chainFull B vl u' b₀ k ⊆ wedgeFull B vl u'`: the cut only removes points.

`chainFull … = L1Region.cut (wedgeFull B vl u') (expNormal u' vl) (expLevel u' vl b₀)` and
`L1Region.cut Rinf m lev n = Rinf ∩ halfPlaneGE m (lev n)` (`L1Region.lean:197`). -/
theorem chainFull_subset_wedgeFull (B : Set (ℤ × ℤ)) (vl u' b₀ : ℤ × ℤ) (k : ℕ) :
    Nivat.ColleReg.chainFull B vl u' b₀ k ⊆ Nivat.ColleReg.wedgeFull B vl u' :=
  Set.inter_subset_left

/-! ### §2  The assembly that type-checks, with `D := fullSweep B vl` -/

/-- **`hbase` at index `k` from the paper's line-by-line sweep.**

`Nivat.SweepLines.hbase_at_of_sweep_lines` (`SweepLines.lean:177`) with

* `D := fullSweep B vl`,
* `lines i := wedgeFull B vl u' ∩ {y | dot nℓ y = cz - 1 - i}`,

and `hKL` discharged by `chainFull_subset_wedgeFull` composed with
`Nivat.ConeLines.wedgeFull_subset_fullSweep_union_lines`.

原文：b3_colle2.txt:796-804 — `lines i` is `A_{i+1} = 𝓡_{ι-1} ∩ l_{i+1}`, `l_1 := ℓ_B^{(-)}`;
`hstep : dot nℓ u' = -1` is "proceeding this way" (one `u'`-step per line, `:804`);
`hperp : dot nℓ vl = 0` is that the `l_i` are parallel to `ℓ` (`:406`, `:796`);
`hBstep` is the seed-step condition of `Nivat.ConeLines.stepIn_fullSweep`, licensed by
`B` being `E(𝒮_φ)`-enveloped (`Definition 3.2`, `:402`) with `ℓ_{ι-1}` an edge direction of
`𝒮_φ` (`:770`).

⚠ `hD` is on `fullSweep B vl`, **not** on the paper's `halfStrip B vl`.  See the module
docstring: `not_chainFull_subset_halfStrip_union_lines` shows the `halfStrip` version of `hKL`
is false, so this upgrade is forced, not chosen.  `hBstep` and the upgraded `hD` have no
producer in the tree. -/
theorem hbase_of_cone_lines {ξ : Nivat.Config ℤ} {e : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} {a : ℤ × ℤ} (hS : Nivat.Colle.GeneratesAt ξ S a)
    (ha : a ∈ S) (hconv : Nivat.LatticeConvex (S.erase a))
    {B : Set (ℤ × ℤ)} {vl u' b₀ nℓ : ℤ × ℤ} {c cz : ℤ} (k : ℕ)
    (hD : ∀ z ∈ Nivat.ColleReg.fullSweep B vl,
      Nivat.T e ξ z = Nivat.T (c • vl) (Nivat.T e ξ) z)
    (hperp : Nivat.LE2.dot nℓ vl = 0) (hstep : Nivat.LE2.dot nℓ u' = -1)
    (hBstep : ∀ b ∈ B, cz ≤ Nivat.LE2.dot nℓ (b + u') →
      ∃ b' ∈ B, ∃ m : ℤ, b + u' = b' + m • vl)
    (hwinL : ∀ i : ℕ,
      ∀ w ∈ Nivat.ColleReg.wedgeFull B vl u' ∩
        {y | Nivat.LE2.dot nℓ y = cz - 1 - (i : ℤ)},
      ∀ z ∈ S.erase a,
        z + (w - a) ∈ Nivat.ColleReg.fullSweep B vl ∪
          (⋃ i' ∈ {i' | i' < i}, Nivat.ColleReg.wedgeFull B vl u' ∩
            {y | Nivat.LE2.dot nℓ y = cz - 1 - (i' : ℤ)})) :
    Nivat.Colle41.PeriodOn (Nivat.T e ξ) (Nivat.ColleReg.chainFull B vl u' b₀ k) (c • vl) :=
  Nivat.SweepLines.hbase_at_of_sweep_lines hS ha hconv k hD
    (fun i => Nivat.ColleReg.wedgeFull B vl u' ∩
      {y | Nivat.LE2.dot nℓ y = cz - 1 - (i : ℤ)})
    hwinL
    ((chainFull_subset_wedgeFull B vl u' b₀ k).trans
      (Nivat.ConeLines.wedgeFull_subset_fullSweep_union_lines hperp hstep hBstep))

/-! ### §3  The mismatch: `hKL` with the paper's seed `halfStrip B vl` is false -/

/-- **🔴 `hKL` cannot be discharged with `D := halfStrip B vl`.**

Witness: `B = {(0,0)}`, `vl = (1,0)`, `u' = (0,-1)`, `b₀ = (0,0)`, `k = 1`, `nℓ = (0,1)`,
`cz = 0`.  Here `expNormal u' vl = (1,0)` and `expLevel u' vl b₀ 1 = -1`, so the cut admits
`(-1,0)`:

* `(-1,0) ∈ chainFull B vl u' b₀ 1` — it is `(0,0) + (-1)•vl ∈ fullSweep B vl ⊆ wedgeFull`,
  and `dot (expNormal u' vl) (-1,0) = -1 ≥ -1`;
* `(-1,0) ∉ halfStrip B vl = {(s,0) : s ∈ ℕ}` — the forward strip never goes to `-vl`;
* `dot nℓ (-1,0) = 0`, and every line sits at `cz - 1 - i ≤ -1`, so it is on no line.

The `lines` family used is the **largest** one this construction can offer,
`wedgeFull B vl u' ∩ {level}`; a fortiori the `coneRegion`-based family fails too.

Every hypothesis `ConeLines` asks for holds at this witness — `det u' vl = 1`,
`dot nℓ vl = 0`, `dot nℓ u' = -1`, `∀ b ∈ B, cz ≤ dot nℓ b`, `b₀ ∈ B`, `B.Finite`, and
`hstepIn` (vacuously, since every `u'`-step out of the strip lands below `cz`).  So the
obstruction is **not** the covering and **not** `hstepIn`: it is that `chainFull` inherits
`wedgeFull`'s two-sided `vl`-sweep and the `expNormal` cut does not undo it.

原文：b3_colle2.txt:414 — `H_B(ℓ)` has `t ∈ ℤ₊`.  Collé's object never contains `b - vl`;
`chainFull` does. -/
theorem not_chainFull_subset_halfStrip_union_lines :
    ∃ (B : Set (ℤ × ℤ)) (vl u' b₀ nℓ : ℤ × ℤ) (cz : ℤ) (k : ℕ),
      Nivat.det u' vl = 1 ∧
      Nivat.LE2.dot nℓ vl = 0 ∧
      Nivat.LE2.dot nℓ u' = -1 ∧
      b₀ ∈ B ∧ B.Finite ∧
      (∀ b ∈ B, cz ≤ Nivat.LE2.dot nℓ b) ∧
      (∀ z ∈ Nivat.LE2.halfStrip B vl,
        cz ≤ Nivat.LE2.dot nℓ (z + u') → z + u' ∈ Nivat.LE2.halfStrip B vl) ∧
      ¬ (Nivat.ColleReg.chainFull B vl u' b₀ k ⊆ Nivat.LE2.halfStrip B vl ∪
            (⋃ i : ℕ, Nivat.ColleReg.wedgeFull B vl u' ∩
              {y | Nivat.LE2.dot nℓ y = cz - 1 - (i : ℤ)})) := by
  refine ⟨({((0 : ℤ), (0 : ℤ))} : Set (ℤ × ℤ)), ((1 : ℤ), (0 : ℤ)), ((0 : ℤ), (-1 : ℤ)),
    ((0 : ℤ), (0 : ℤ)), ((0 : ℤ), (1 : ℤ)), 0, 1,
    by simp [Nivat.det], by simp [Nivat.LE2.dot], by simp [Nivat.LE2.dot], rfl,
    Set.finite_singleton _, ?_, ?_, ?_⟩
  · rintro b rfl; simp [Nivat.LE2.dot]
  · -- `hstepIn` holds vacuously: every `u'`-step out of the strip lands at level `-1 < cz`.
    rintro z ⟨b, rfl, t, rfl⟩ hlev
    exfalso
    simp [Nivat.LE2.dot] at hlev
  · intro hsub
    -- `(-1,0)` survives the `expNormal` cut at `k = 1`.
    have hw : ((-1 : ℤ), (0 : ℤ)) ∈
        Nivat.ColleReg.wedgeFull ({((0 : ℤ), (0 : ℤ))} : Set (ℤ × ℤ))
          ((1 : ℤ), (0 : ℤ)) ((0 : ℤ), (-1 : ℤ)) := by
      refine ⟨((-1 : ℤ), (0 : ℤ)), ?_, 0, by simp⟩
      exact Nivat.ColleReg.mem_fullSweep_iff.mpr ⟨((0 : ℤ), (0 : ℤ)), rfl, -1, by simp⟩
    have hcut : ((-1 : ℤ), (0 : ℤ)) ∈
        Nivat.LE2.halfPlaneGE
          (Nivat.ColleReg.expNormal ((0 : ℤ), (-1 : ℤ)) ((1 : ℤ), (0 : ℤ)))
          (Nivat.ColleReg.expLevel ((0 : ℤ), (-1 : ℤ)) ((1 : ℤ), (0 : ℤ))
            ((0 : ℤ), (0 : ℤ)) 1) := by
      simp [Nivat.LE2.halfPlaneGE, Nivat.ColleReg.expNormal, Nivat.ColleReg.expLevel,
        Nivat.LE2.dot, Nivat.det]
    rcases hsub ⟨hw, hcut⟩ with hstrip | hlines
    · obtain ⟨b, hb, t, ht⟩ := hstrip
      rw [hb] at ht
      simp [Prod.ext_iff] at ht
    · obtain ⟨i, _, hi⟩ := Set.mem_iUnion.mp hlines
      simp only [Set.mem_ofPred_eq, Nivat.LE2.dot] at hi
      omega

/-! ### §4  `chainFull ⊄ coneRegion`, as a kernel fact rather than a docstring reading -/

/-- **🔴 The module docstring's `chainFull ⊄ coneRegion` (`:40`), promoted to a theorem.**

Same witness as §3: `B = {(0,0)}`, `vl = (1,0)`, `u' = (0,-1)`, `b₀ = (0,0)`, `k = 1`.  The point
`(-1,0)` survives the `expNormal` cut, but `coneRegion B vl u'` sweeps `+vl` only, so every one
of its points has first coordinate `≥ 0`.

原文：b3_colle2.txt:414, :784 — both `H_B(ℓ)` and `𝓡_{ι-1}` are `ℤ₊`-sweeps.  `chainFull` is a
cut of `wedgeFull`, which sweeps `±vl` (`L1RegionBuild.lean:230`), and the cut is by
`expNormal u' vl` at level `expLevel … - k`, which bounds the `vl`-coordinate from below but not
at `0`.

This is what `Nivat.StrictWindow.hbase_of_cone_halfStrip_of_hmono`'s `hchain` binder asks for,
so that binder is a genuine hypothesis and not free. -/
theorem not_chainFull_subset_coneRegion :
    ∃ (B : Set (ℤ × ℤ)) (vl u' b₀ : ℤ × ℤ) (k : ℕ),
      Nivat.det u' vl = 1 ∧ b₀ ∈ B ∧ B.Finite ∧
      ¬ (Nivat.ColleReg.chainFull B vl u' b₀ k ⊆
          Nivat.ConeRegion.coneRegion B vl u') := by
  refine ⟨({((0 : ℤ), (0 : ℤ))} : Set (ℤ × ℤ)), ((1 : ℤ), (0 : ℤ)), ((0 : ℤ), (-1 : ℤ)),
    ((0 : ℤ), (0 : ℤ)), 1, by simp [Nivat.det], rfl, Set.finite_singleton _, ?_⟩
  intro hsub
  have hw : ((-1 : ℤ), (0 : ℤ)) ∈
      Nivat.ColleReg.wedgeFull ({((0 : ℤ), (0 : ℤ))} : Set (ℤ × ℤ))
        ((1 : ℤ), (0 : ℤ)) ((0 : ℤ), (-1 : ℤ)) := by
    refine ⟨((-1 : ℤ), (0 : ℤ)), ?_, 0, by simp⟩
    exact Nivat.ColleReg.mem_fullSweep_iff.mpr ⟨((0 : ℤ), (0 : ℤ)), rfl, -1, by simp⟩
  have hcut : ((-1 : ℤ), (0 : ℤ)) ∈
      Nivat.LE2.halfPlaneGE
        (Nivat.ColleReg.expNormal ((0 : ℤ), (-1 : ℤ)) ((1 : ℤ), (0 : ℤ)))
        (Nivat.ColleReg.expLevel ((0 : ℤ), (-1 : ℤ)) ((1 : ℤ), (0 : ℤ))
          ((0 : ℤ), (0 : ℤ)) 1) := by
    simp [Nivat.LE2.halfPlaneGE, Nivat.ColleReg.expNormal, Nivat.ColleReg.expLevel,
      Nivat.LE2.dot, Nivat.det]
  obtain ⟨b, hb, s, t, hst⟩ :=
    Nivat.ConeRegion.mem_coneRegion_iff.mp (hsub ⟨hw, hcut⟩)
  rw [Set.mem_singleton_iff] at hb
  subst hb
  have h1 := congrArg Prod.fst hst
  simp at h1

/-! ### §5  🔴 `hmono` is false for every shear, on an enveloped witness -/

/-- **🔴 `hmono` fails for every legal `𝒮_φ` and every admissible `u'` — the shear does not help.**

`hmono` is `Nivat.StrictWindow.coneRegion_inter_level_subset_halfStrip_iff_hmono`'s right-hand
side, i.e. *exactly* the content of the covering `𝓡_{ι-1} ⊆ H_B(ℓ) ∪ ⋃ A_i`:

    ∀ b ∈ B, ∀ t : ℕ, cz ≤ ⟪nℓ,b⟫ - t → b + t•u' ∈ H_B(ℓ) .

**Why no `u'` works.**  `⟪nℓ,vl⟫ = 0`, so `H_B(ℓ) = B + ℕ·vl` meets exactly the levels that `B`
itself meets.  `Nivat.ConeLines.no_level_two` says the witness `sliver` has **no point at level
2**, while it has points at levels `0, 1, 3`.  Any `u'` with `⟪nℓ,u'⟫ = -1` sends `(2,3)`, at
level `3`, to level `2`, which is `≥ cz = 0` — and there is nothing there to land on.  The
missing level is a property of `B` and `nℓ` alone, so **the shear `u' ↦ u' - K•vl` is powerless**:
it never changes any level.  That is why `u'` is quantified universally here rather than fixed.

This is strictly stronger than `Nivat.ConeLines.not_hBstep_of_any_envOf` (`ConeLines.lean:857`):
that one fixes `u' = (0,-1)` and allows a two-sided tail `k : ℤ`; this one ranges over all `u'`.

Everything Definition 3.2 (`:402`) offers is discharged on the witness — `EnvOf ↑S B` for an
arbitrary enveloping `S`, lattice convexity, positive area, `PosArea`, primitivity of `nℓ` and
`vl`, `⟪nℓ,vl⟫ = 0`, the edge condition `-nℓ ∈ E ↑S` of `:472`, `suppVal B (-nℓ) = -cz`, and
`B ⊆ ℋ(ℓ_B)`.  Producers for `hS` exist, so this is not vacuous: `Nivat.ConeLines.envOf_sliver`
(4 points) and `Nivat.ConeLines.envOf_tri_sliver` (3 points).

⚠ **读法, 非内核事实 (scope).**  What is refuted is the derivation of `hmono` from Definition 3.2
plus the `:472` edge condition, for a finite lattice-convex `B` of positive area.  A producer
that also knows `B` has **no empty level inside its own band** is not refuted — and by the
argument above that gap-freeness is precisely what `hmono` needs beyond what is assumed here. -/
theorem not_hmono_of_any_envOf {S : Finset (ℤ × ℤ)}
    (hS : Nivat.LE2.EnvOf (↑S : Set (ℤ × ℤ)) (↑Nivat.ConeLines.sliver : Set (ℤ × ℤ))) :
    ∃ (B : Set (ℤ × ℤ)) (vl nℓ : ℤ × ℤ) (cz : ℤ),
      B.Finite ∧ B.Nonempty ∧ Nivat.IsLatticeConvexRegion B ∧ Nivat.LE2.PosArea B ∧
      Nivat.Primitive nℓ ∧ Nivat.Primitive vl ∧
      Nivat.LE2.dot nℓ vl = 0 ∧
      (-nℓ) ∈ Nivat.LE2.E (↑S : Set (ℤ × ℤ)) ∧
      Nivat.LE2.suppVal B (-nℓ) = -cz ∧
      (∀ b ∈ B, cz ≤ Nivat.LE2.dot nℓ b) ∧
      (∀ u' : ℤ × ℤ, Nivat.LE2.dot nℓ u' = -1 →
        ¬ (∀ b ∈ B, ∀ t : ℕ, cz ≤ Nivat.LE2.dot nℓ b - (t : ℤ) →
            b + (t : ℤ) • u' ∈ Nivat.LE2.halfStrip B vl)) := by
  refine ⟨(↑Nivat.ConeLines.sliver : Set (ℤ × ℤ)), ((1 : ℤ), (0 : ℤ)), ((0 : ℤ), (1 : ℤ)), 0,
    Nivat.ConeLines.sliver.finite_toSet,
    ⟨(0, 0), Nivat.ConeLines.mem_sliver.mpr (Or.inl rfl)⟩,
    Nivat.ConeLines.isLatticeConvexRegion_sliver, Nivat.ConeLines.posArea_sliver,
    isCoprime_one_right, isCoprime_one_left, by decide, ?_, ?_, ?_, ?_⟩
  · have hneg : (-((0 : ℤ), (1 : ℤ)) : ℤ × ℤ) = ((0 : ℤ), (-1 : ℤ)) := by decide
    rw [hneg]
    exact Nivat.ConeLines.edge_bot_of_envOf_sliver hS
  · have hneg : (-((0 : ℤ), (1 : ℤ)) : ℤ × ℤ) = ((0 : ℤ), (-1 : ℤ)) := by decide
    rw [hneg, Nivat.ConeLines.suppVal_sliver_bot]
    norm_num
  · intro b hb
    rw [Nivat.ConeLines.mem_sliver_iff_ineq] at hb
    simp only [Nivat.LE2.dot]
    omega
  · intro u' hu' hmono
    obtain ⟨b', hb', s, hbs⟩ :=
      hmono ((2 : ℤ), (3 : ℤ))
        (Nivat.ConeLines.mem_sliver.mpr (Or.inr (Or.inr (Or.inr rfl)))) 1
        (by norm_num [Nivat.LE2.dot])
    rw [Nivat.ConeLines.mem_sliver_iff_ineq] at hb'
    simp only [Nivat.LE2.dot] at hu'
    have h2 := congrArg Prod.snd hbs
    simp at h2
    omega

end Nivat.ConeHbase

#print axioms Nivat.ConeHbase.chainFull_subset_wedgeFull
#print axioms Nivat.ConeHbase.hbase_of_cone_lines
#print axioms Nivat.ConeHbase.not_chainFull_subset_halfStrip_union_lines
#print axioms Nivat.ConeHbase.not_chainFull_subset_coneRegion
#print axioms Nivat.ConeHbase.not_hmono_of_any_envOf
