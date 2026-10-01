/-
Copyright (c) 2026 Nivat formalisation project. All rights reserved.
-/
import Nivat.External.Colle.L1RegionBuild
import Nivat.External.Colle.L1Region
-- 盲区 1b 实测：本文件的唯一 importer 是 `RegionSteps.lean`，而 `ConeRegion` 已在它的
-- import 闭包内（`RegionSteps.lean:1408` 用 `Nivat.ConeRegion.coneRegion`），故新进闭包 0 个。
import Nivat.External.Colle.ConeRegion
import Nivat.External.Colle.TowerBuild

/-!
# Stage 2: The maximal index lemma

This file proves the existence of the **greatest** index `N` such that `(T^u η)|𝓡^N_I` is
periodic of period `h` (`b3_colle2.txt:818-820`).

## Main result

* `exists_greatest_periodOn_chainFull` — the maximal index `N` exists whenever the base slice is
  periodic but the union is not.

This is exactly Collé's setup at `:818-820`: "From the fact that `⋃_{n=0}^∞ 𝓡^n_I = 𝓡_{I−1}`,
we may consider the **greatest** integer `N ∈ ℤ₊` such that `(T^u η)|𝓡^N_I` is periodic of
period `h`."

## Consumer

`Nivat.ColleReg.exists_stage2_frame_of_claim46` (`RegionSteps.lean:1461`) — the stage-2
frame builder that wraps the L1 maximal-index selection.
-/

set_option autoImplicit false

namespace Nivat.ColleReg

open Nivat Nivat.Colle41 Nivat.LE2

/-- **Exhaustion of levels by `expLevel`** (`b3_colle2.txt:816`, the union `⋃_n 𝓡^n_I = 𝓡_{I−1}`).

原文：b3_colle2.txt:816
The levels `expLevel u' vl b₀ n = dot (expNormal u' vl) b₀ - n` descend through all integers,
so every level `b : ℤ` is eventually reached. This is the hypothesis `∀ b, ∃ n, lev n ≤ b` that
`Nivat.L1Region.iUnion_cut` needs to prove the union equals `wedgeFull R vl u₂`.

Quantifiers:
- `u' vl b₀ : ℤ × ℤ` — the cutting normal's inputs (see `expNormal`, `expLevel` in
  `L1RegionBuild.lean:284-301`).
- `b : ℤ` — an arbitrary level to be reached.
- `∃ n : ℕ` — the index at which `expLevel u' vl b₀ n` drops to or below `b`. -/
theorem expLevel_exhausts (u' vl b₀ : ℤ × ℤ) (b : ℤ) :
    ∃ n : ℕ, expLevel u' vl b₀ n ≤ b := by
  refine ⟨(dot (expNormal u' vl) b₀ - b).toNat, ?_⟩
  simp only [expLevel]
  have := Int.self_le_toNat (dot (expNormal u' vl) b₀ - b)
  omega

/-- **The maximal index `N` exists, at an arbitrary ambient region** (`b3_colle2.txt:818-820`).

原文：b3_colle2.txt:816-820
Collé writes: "From the fact that `⋃_{n=0}^∞ 𝓡^n_I = 𝓡_{I−1}`, we may consider the **greatest**
integer `N ∈ ℤ₊` such that `(T^u η)|𝓡^N_I` is periodic of period `h`."

This is the faithful form: the non-periodicity hypothesis sits on **`Rinf` itself**, which is
the paper's `𝓡_{I−1}`, with no assumption about how `Rinf` was built.  In particular it does
**not** require `Rinf` to be a `fullSweep`, so it carries none of the `ℤ·vl` over-sweep debt
recorded in §2.

Quantifiers, against the paper:
- `Rinf : Set (ℤ × ℤ)` — `𝓡_{I−1}` (`:808`, `:820`).
- `m : ℤ × ℤ`, `lev : ℕ → ℤ` — the cutting normal and the distances `d_n` of `:818`
  (`dist(·, ℓ'_{𝓡_I}) ≤ d_n`).  `m` is unconstrained here; the region hypotheses on it are
  needed only to know each slice is a region (`L1Region.isRegion_cut`), not for maximality.
- `hlev` — the `d_n` increase, i.e. the levels descend (`Antitone lev`).
- `hexh` — the `d_n` are unbounded, which is what makes `⋃_n 𝓡^n_I = 𝓡_{I−1}` at `:820`
  (`L1Region.iUnion_cut`).
- `hbase` — `(T^u η)|𝓡^0_I` is periodic.
- `hnot` — `(T^u η)|𝓡_{I−1}` is **not** periodic.  This is not a new debt: it is the second
  output of the *outer* chain's maximality argument, `RegionFamily.exists_index_I`
  (`L1Region.lean:591`), as that file's §8 (`:563-571`) records.
- `∃ N : ℕ` — the greatest index: periodic at `N`, not at `N + 1`. -/
theorem exists_greatest_periodOn_cut
    {A : Type*} {x : Config A} {Rinf : Set (ℤ × ℤ)} {m : ℤ × ℤ} {lev : ℕ → ℤ} {h : ℤ × ℤ}
    (hlev : Antitone lev) (hexh : ∀ b : ℤ, ∃ n, lev n ≤ b)
    (hbase : PeriodOn x (Nivat.L1Region.cut Rinf m lev 0) h)
    (hnot : ¬ PeriodOn x Rinf h) :
    ∃ N : ℕ,
      PeriodOn x (Nivat.L1Region.cut Rinf m lev N) h ∧
      ¬ PeriodOn x (Nivat.L1Region.cut Rinf m lev (N + 1)) h := by
  have hmono : Monotone (Nivat.L1Region.cut Rinf m lev) := Nivat.L1Region.cut_mono hlev
  rw [← Nivat.L1Region.iUnion_cut (Rinf := Rinf) (m := m) hexh] at hnot
  exact Nivat.L1Region.exists_greatest_periodOn hmono hbase hnot

/-- **The maximal index `N` exists** (`b3_colle2.txt:818-820`, "the greatest integer `N ∈ ℤ₊`
such that `(T^u η)|𝓡^N_I` is periodic of period `h`").

原文：b3_colle2.txt:818-820
Collé writes: "From the fact that `⋃_{n=0}^∞ 𝓡^n_I = 𝓡_{I−1}`, we may consider the **greatest**
integer `N ∈ ℤ₊` such that `(T^u η)|𝓡^N_I` is periodic of period `h`."

In our encoding:
- `𝓡^n_I` is `chainFull R vl u₂ b₀ n` (see `L1RegionBuild.lean:305`).
- `𝓡_{I−1}` is `wedgeFull R vl u₂` (see `L1RegionBuild.lean:230`).
- The union `⋃_n 𝓡^n_I = 𝓡_{I−1}` is proved by `Nivat.L1Region.iUnion_cut` (`:215`) from
  `expLevel_exhausts` above.
- `(T^u η)|𝓡^N_I` periodic means `PeriodOn x (chainFull R vl u₂ b₀ N) h`.

Quantifiers:
- `A : Type*` — the alphabet (usually `ℤ` in the paper).
- `x : Config A` — the configuration `(T^u η)` (see `Nivat.Config`, `Defs/Config.lean:38`).
- `R : Set (ℤ × ℤ)` — the base region (Collé's `𝓡_I`).
- `vl u₂ b₀ h : ℤ × ℤ` — the two ray directions, a base point, and the period.
- `hbase` — periodicity at index `0` (the bottom of the chain).
- `hnot` — **non-periodicity on the union** `wedgeFull R vl u₂`.  This is exactly the
  second output of the *outer* chain's maximality argument (`L1Region.lean:591`,
  `exists_index_I`), handed down to the inner chain per `L1Region.lean` §8.
- `∃ N : ℕ` — the **greatest** index with periodicity.  At `N` it holds; at `N+1` it fails.

⚠ **This is the over-swept special case.**  Prefer `exists_greatest_periodOn_cut` below, which
is the same statement at an *arbitrary* ambient region and therefore matches `:818-820`
literally.  See `chainFull_eq_cut_wedgeFull` for the exact specialization. -/
theorem exists_greatest_periodOn_chainFull
    {A : Type*} {x : Config A} {R : Set (ℤ × ℤ)} {vl u₂ b₀ h : ℤ × ℤ}
    (hbase : PeriodOn x (chainFull R vl u₂ b₀ 0) h)
    (hnot : ¬ PeriodOn x (wedgeFull R vl u₂) h) :
    ∃ N : ℕ,
      PeriodOn x (chainFull R vl u₂ b₀ N) h ∧
      ¬ PeriodOn x (chainFull R vl u₂ b₀ (N + 1)) h :=
  exists_greatest_periodOn_cut (expLevel_antitone u₂ vl b₀) (expLevel_exhausts u₂ vl b₀)
    hbase hnot

/-- **`𝓡^n_I` is a cut of the ambient region** — definitional, but stating it makes the
relationship between the two framings a kernel fact instead of a docstring claim.

`chainFull` is *by definition* `cut` applied to the ambient set `wedgeFull R vl u₂`
(`L1RegionBuild.lean:305`).  Everything the `chainFull` framing costs us over the paper is
therefore concentrated in **one** place: the choice of ambient set.  Collé's ambient is
`𝓡_{I−1}` (`:808`, a pure `ℕ`-sweep); ours is `wedgeFull` (an `ℤ·vl` over-sweep).  The
`cut` layer itself is faithful. -/
theorem chainFull_eq_cut_wedgeFull (R : Set (ℤ × ℤ)) (vl u₂ b₀ : ℤ × ℤ) :
    chainFull R vl u₂ b₀ =
      Nivat.L1Region.cut (wedgeFull R vl u₂) (expNormal u₂ vl) (expLevel u₂ vl b₀) :=
  rfl

/-! ## §2  The stage-1 → stage-2 seam

`exists_greatest_periodOn_chainFull` above consumes `hbase`, periodicity on
`chainFull R vl u₂ b₀ 0`.  Whoever discharges `RegionSteps.exists_stage2_frame_of_claim46`
must produce that from stage one's output.  This section measures exactly what the step costs.

**The shape of `wedgeFull`.**  Unfolding `L1RegionBuild.lean:230/164`,
`wedgeFull R vl u₂ = R + ℤ·vl + ℕ·u₂` — the `vl`-sweep runs in **both** directions
(`fullSweep` is `sweep (sweep · (-vl)) vl`), the `u₂`-sweep only forward.

**Consequence (positive half, `wedgeFull_subset_of_invariant`).**  A region closed under
**both** `+ℤ·vl` and `+ℕ·u₂` absorbs its own `wedgeFull`, so every slice sits inside it and
`PeriodOn.mono` (`Lemma41.lean:662`, antitone in the set) transfers periodicity for free.

⚠ **But both hypotheses together are too strong to be the producer**, and this is the point of
`wedgeFull_eq_self_of_invariant` below: they force `wedgeFull R vl u₂ = R`, which makes `hnot`
contradict periodicity on `R`.  Collé's `𝓡_I` has `hvl` and **not** `hu₂` — `:808`'s
`𝓡_{I−1} := 𝓡_I + ℕ v⃗_{ℓ_{I−1}}` is a *strict* growth, which is what lets `:812` write
`𝓡_{ι−1} ⊂ ⋯ ⊂ 𝓡_{ι−m+1}` with proper inclusions.  So the three positive lemmas below are a
**fence**, not a road: they say precisely which `R` the residual must *not* ask for.

**Consequence (negative half, `not_forall_coneRegion_zsmul_vl_mem`).**  Stage one's output
region `coneRegion B vl u'` (`ConeRegion.lean:68`) sweeps `vl` **forward only**, so it fails
even `hvl`.

🔴 **Read this the right way round.**  It is *not* a gap in the paper to be closed — it is a
**mismatch between `wedgeFull` and Collé**, i.e. a hard-rule-7 debt on our side.  `:808` defines
`𝓡_{I−1} := {g + t·v⃗_{ℓ_{I−1}} : g ∈ 𝓡_I, t ∈ ℤ₊}`: a **pure `ℕ`-sweep, with no `ℤ·vl`
component at all**.  Collé's `𝓡_{ι−1}` is likewise a `(−ℓ, ℓ_{ι−1})`-*region* (`:796`,
Figure 10), i.e. a wedge with two edge directions — not a `ℤ·vl`-invariant set.  Our
`fullSweep` therefore **over-sweeps**: `wedgeFull R vl u₂ ⊇ 𝓡_{I−1}`, strictly in general.

Directions of the resulting debt, measured against `exists_greatest_periodOn_chainFull`:
- `hnot` (on `wedgeFull`) is **weaker** than the paper's `¬PeriodOn 𝓡_{I−1} h` — harmless, in
  fact easier to produce.
- `hbase` (on `chainFull … 0`, a cut of the *over*-swept wedge) is **stronger** than the paper's
  `PeriodOn 𝓡^0_I h` — this is the debt: 比原文强 = 债.

So if `hbase` turns out unreachable, the `ℤ·vl` over-sweep in `fullSweep` is the **first**
suspect, ahead of any corner or frame question.

原文：b3_colle2.txt:796（`𝓡_{ι−1}` 是 `(−ℓ, ℓ_{ι−1})`-region，两个边方向的楔形）、
:808（`𝓡_i := 𝓡_{i+1} + ℕ v⃗_{ℓ_i}`，纯 `ℕ` 扫，严格增长）、:812（真包含链）、:818（`𝓡^n_I`）。 -/

/-- **A `ℤ·vl`- and `ℕ·u₂`-invariant region absorbs its own `wedgeFull`.**

原文：b3_colle2.txt:795-802, :818.

Quantifiers:
- `R : Set (ℤ × ℤ)` — Collé's `𝓡_I`.
- `hvl` — invariance under `+ k·vl` for **every** `k : ℤ`; this is what the line-by-line
  induction of `:795-802` buys, and it is the hypothesis `coneRegion` fails (see
  `not_forall_coneRegion_zsmul_vl_mem`).
- `hu₂` — invariance under `+ t·u₂` for `t : ℕ`; this is `:808`'s `𝓡_i := 𝓡_{i+1} + ℕ v⃗_{ℓ_i}`
  read as a closure property of the limit region. -/
theorem wedgeFull_subset_of_invariant {R : Set (ℤ × ℤ)} {vl u₂ : ℤ × ℤ}
    (hvl : ∀ z ∈ R, ∀ k : ℤ, z + k • vl ∈ R)
    (hu₂ : ∀ z ∈ R, ∀ t : ℕ, z + (t : ℤ) • u₂ ∈ R) :
    wedgeFull R vl u₂ ⊆ R := by
  intro z hz
  have hz' : ∃ g ∈ fullSweep R vl, ∃ t : ℕ, z = g + (t : ℤ) • u₂ := hz
  obtain ⟨g, hg, t, rfl⟩ := hz'
  obtain ⟨b, hb, k, rfl⟩ := mem_fullSweep_iff.mp hg
  exact hu₂ _ (hvl b hb k) t

/-- **Every slice of an invariant region sits inside it** (`𝓡^n_I ⊆ 𝓡_I`, `b3_colle2.txt:818`). -/
theorem chainFull_subset_of_invariant {R : Set (ℤ × ℤ)} {vl u₂ b₀ : ℤ × ℤ}
    (hvl : ∀ z ∈ R, ∀ k : ℤ, z + k • vl ∈ R)
    (hu₂ : ∀ z ∈ R, ∀ t : ℕ, z + (t : ℤ) • u₂ ∈ R) (n : ℕ) :
    chainFull R vl u₂ b₀ n ⊆ R :=
  fun _ hz => wedgeFull_subset_of_invariant hvl hu₂ hz.1

/-- **Periodicity descends from an invariant region to all of its slices.**

⚠ **Not the producer the stage-2 frame needs** — see `wedgeFull_eq_self_of_invariant`: an `R`
meeting both invariance hypotheses cannot simultaneously satisfy `hnot`.  This lemma is the
fence that makes that collapse checkable, not a road to `hbase`.

原文：b3_colle2.txt:814-818. -/
theorem periodOn_chainFull_of_invariant {A : Type*} {x : Config A}
    {R : Set (ℤ × ℤ)} {vl u₂ b₀ h : ℤ × ℤ}
    (hvl : ∀ z ∈ R, ∀ k : ℤ, z + k • vl ∈ R)
    (hu₂ : ∀ z ∈ R, ∀ t : ℕ, z + (t : ℤ) • u₂ ∈ R)
    (hR : PeriodOn x R h) (n : ℕ) :
    PeriodOn x (chainFull R vl u₂ b₀ n) h :=
  PeriodOn.mono (chainFull_subset_of_invariant hvl hu₂ n) hR

/-- **Both invariances collapse the wedge**: `wedgeFull R vl u₂ = R`.

🔴 **This is a warning, not a tool.**  `exists_greatest_periodOn_chainFull` consumes `hbase`
(periodicity at index `0`) *together with* `hnot` (non-periodicity on `wedgeFull R vl u₂`).
By this equality, an `R` satisfying **both** invariances has `wedgeFull R vl u₂ = R`, so on such
an `R` the pair `PeriodOn x R h` ＋ `hnot` is **contradictory**.  Anyone reshaping
`RegionSteps.exists_stage2_frame_of_claim46` must therefore *not* ask the residual for an `R`
that is both fully invariant and periodic — that residual is vacuous, and a vacuous residual is
the failure mode `CLAUDE.md` 硬规矩 7 exists to catch.

The escape is that Collé's `𝓡_I` satisfies `hvl` (from `:795-802`) but **not** `hu₂`: `:808`'s
`𝓡_{I−1} := 𝓡_I + ℕ v⃗_{ℓ_{I−1}}` is a *strict* growth, which is exactly why `:812` can write the
chain `𝓡_{ι−1} ⊂ ⋯ ⊂ 𝓡_{ι−m+1}` with proper inclusions. -/
theorem wedgeFull_eq_self_of_invariant {R : Set (ℤ × ℤ)} {vl u₂ : ℤ × ℤ}
    (hvl : ∀ z ∈ R, ∀ k : ℤ, z + k • vl ∈ R)
    (hu₂ : ∀ z ∈ R, ∀ t : ℕ, z + (t : ℤ) • u₂ ∈ R) :
    wedgeFull R vl u₂ = R := by
  refine Set.Subset.antisymm (wedgeFull_subset_of_invariant hvl hu₂) ?_
  intro z hz
  exact Nivat.RegionSweep.subset_sweep _ _ (Nivat.RegionSweep.subset_sweep _ _
    (Nivat.RegionSweep.subset_sweep _ _ hz))

/-- The contradiction of `wedgeFull_eq_self_of_invariant`, stated positively: on a fully
invariant region, periodicity propagates to the wedge, so `hnot` cannot also hold. -/
theorem periodOn_wedgeFull_of_invariant {A : Type*} {x : Config A}
    {R : Set (ℤ × ℤ)} {vl u₂ h : ℤ × ℤ}
    (hvl : ∀ z ∈ R, ∀ k : ℤ, z + k • vl ∈ R)
    (hu₂ : ∀ z ∈ R, ∀ t : ℕ, z + (t : ℤ) • u₂ ∈ R)
    (hR : PeriodOn x R h) :
    PeriodOn x (wedgeFull R vl u₂) h := by
  rw [wedgeFull_eq_self_of_invariant hvl hu₂]
  exact hR

/-! ### §2.1  The ambient form — the producer that survives the collapse

`wedgeFull_eq_self_of_invariant` rules out asking for an `R` that is itself fully invariant
*and* carries `hnot`.  The escape is to **separate the two roles**: let `R` be Collé's small
base and let the invariance live on an **ambient** `P ⊇ R`.  Then `R` is free to be tiny while
`P` supplies the closure, and no collapse occurs because nothing is asserted about
`wedgeFull P vl u₂`.

This became usable on 2026-09-20, when the stage-2 residual in
`RegionSteps.exists_stage2_frame_of_claim46` dropped its `hnot` conjunct (it was never
consumed — see the comment there).  While `hnot` was present these lemmas would have been
self-defeating; with it gone they are exactly the producer the residual needs.

原文：b3_colle2.txt:795-802（逐行归纳把周期性推到整条线，给 `hvl`）、
:808（`𝓡_i := 𝓡_{i+1} + ℕ v⃗_{ℓ_i}`，给 `hu₂`）、:818（`𝓡^n_I` 是切片，给 `chainFull`）。 -/

/-- **A region inside an invariant ambient set has its whole wedge inside that ambient set.**

Quantifiers:
- `R` — Collé's base `𝓡_I`; no closure property is required of it.
- `P` — the ambient periodic region; `hvl` is what `:795-802`'s line-by-line induction buys
  (periodicity along whole lines `∥ ℓ`), `hu₂` is `:808`'s forward sweep.
- `hRP : R ⊆ P` — the base sits inside the ambient set. -/
theorem wedgeFull_subset_of_ambient {R P : Set (ℤ × ℤ)} {vl u₂ : ℤ × ℤ}
    (hRP : R ⊆ P)
    (hvl : ∀ z ∈ P, ∀ k : ℤ, z + k • vl ∈ P)
    (hu₂ : ∀ z ∈ P, ∀ t : ℕ, z + (t : ℤ) • u₂ ∈ P) :
    wedgeFull R vl u₂ ⊆ P := by
  intro z hz
  have hz' : ∃ g ∈ fullSweep R vl, ∃ t : ℕ, z = g + (t : ℤ) • u₂ := hz
  obtain ⟨g, hg, t, rfl⟩ := hz'
  obtain ⟨b, hb, k, rfl⟩ := mem_fullSweep_iff.mp hg
  exact hu₂ _ (hvl b (hRP hb) k) t

/-- **Every slice sits inside the ambient set.** -/
theorem chainFull_subset_of_ambient {R P : Set (ℤ × ℤ)} {vl u₂ b₀ : ℤ × ℤ}
    (hRP : R ⊆ P)
    (hvl : ∀ z ∈ P, ∀ k : ℤ, z + k • vl ∈ P)
    (hu₂ : ∀ z ∈ P, ∀ t : ℕ, z + (t : ℤ) • u₂ ∈ P) (n : ℕ) :
    chainFull R vl u₂ b₀ n ⊆ P :=
  fun _ hz => wedgeFull_subset_of_ambient hRP hvl hu₂ hz.1

/-- **🟢 The stage-2 base, produced.**  Periodicity on the ambient set descends to every slice.

This discharges the `PeriodOn (T e ξ) (chainFull R vl u₂ b₀ 0) (c • vl)` conjunct of the
residual in `RegionSteps.exists_stage2_frame_of_claim46` from an ambient periodic region —
**with no constraint on `R` beyond `R ⊆ P`**, so the caller may take `R` as small as it likes
(a single point `{b₀}` suffices).

⚠ Contrast `periodOn_chainFull_of_invariant`, which takes `P = R` and is therefore a fence,
not a road: there the same hypotheses additionally force `wedgeFull R vl u₂ = R`.  Here `P` and
`R` are separate, `wedgeFull R vl u₂ ⊆ P` is generally **strict**, and nothing collapses.

原文：b3_colle2.txt:795-802, :808, :818. -/
theorem periodOn_chainFull_of_ambient {A : Type*} {x : Config A}
    {R P : Set (ℤ × ℤ)} {vl u₂ b₀ h : ℤ × ℤ}
    (hRP : R ⊆ P)
    (hvl : ∀ z ∈ P, ∀ k : ℤ, z + k • vl ∈ P)
    (hu₂ : ∀ z ∈ P, ∀ t : ℕ, z + (t : ℤ) • u₂ ∈ P)
    (hP : PeriodOn x P h) (n : ℕ) :
    PeriodOn x (chainFull R vl u₂ b₀ n) h :=
  PeriodOn.mono (chainFull_subset_of_ambient hRP hvl hu₂ n) hP

/-- **🟢 The stage-2 residual's periodicity conjunct, from an ambient region alone.**

This is the residual of `RegionSteps.exists_stage2_frame_of_claim46` with the corner clause
stripped (that clause is free — `WedgeAssemble.exists_shear_corner_data` produces it
unconditionally from `Sphi.Nonempty`).  Taking `R := {b₀}` is legitimate because the residual
quantifies `R` existentially and imposes **no** closure property on it.

**What this buys.**  The remaining debt is now exactly one object: an ambient set `P` that is
`ℤ·vl`-closed, `ℕ·u₂`-closed, `h`-periodic, and nonempty.  Against the paper that is
`𝓡_{I−1}`: `hvl` is `:795-802` (the line-by-line induction makes whole lines `∥ ℓ` periodic),
`hu₂` is `:808` (`𝓡_i := 𝓡_{i+1} + ℕ v⃗_{ℓ_i}`), `hP` is Claim 4.6 at `:804`.

⚠ **Deliberately not used to restate the `sorry`.**  Demanding `∃ P, …` would be *stronger*
than the current residual (it implies it, not conversely), and strengthening a residual is
硬规矩 7's 「比原文强 = 债」.  So this stays a sufficient route, offered to whoever discharges
the residual, and the residual itself keeps its weakest honest form.

原文：b3_colle2.txt:795-802, :804, :808, :818. -/
theorem exists_stage2_data_of_ambient {A : Type*} {x : Config A}
    {P : Set (ℤ × ℤ)} {vl u₂ b₀ h : ℤ × ℤ}
    (hb₀ : b₀ ∈ P)
    (hvl : ∀ z ∈ P, ∀ k : ℤ, z + k • vl ∈ P)
    (hu₂ : ∀ z ∈ P, ∀ t : ℕ, z + (t : ℤ) • u₂ ∈ P)
    (hP : PeriodOn x P h) :
    ∃ (R : Set (ℤ × ℤ)) (b : ℤ × ℤ), b ∈ R ∧ PeriodOn x (chainFull R vl u₂ b 0) h :=
  ⟨{b₀}, b₀, rfl,
    periodOn_chainFull_of_ambient (Set.singleton_subset_iff.mpr hb₀) hvl hu₂ hP 0⟩

/-- **`wedgeFull` is `ℤ·vl`-closed** — for free, from `fullSweep`'s two-sided sweep. -/
theorem zsmul_vl_mem_wedgeFull {B : Set (ℤ × ℤ)} {vl u₂ : ℤ × ℤ} :
    ∀ z ∈ wedgeFull B vl u₂, ∀ k : ℤ, z + k • vl ∈ wedgeFull B vl u₂ := by
  rintro z hz k
  have hz' : ∃ g ∈ fullSweep B vl, ∃ t : ℕ, z = g + (t : ℤ) • u₂ := hz
  obtain ⟨g, hg, t, rfl⟩ := hz'
  obtain ⟨b, hb, j, rfl⟩ := mem_fullSweep_iff.mp hg
  refine ⟨b + (j + k) • vl, mem_fullSweep_iff.mpr ⟨b, hb, j + k, rfl⟩, t, ?_⟩
  rw [add_smul]
  abel

/-- **`wedgeFull` is `ℕ·u₂`-closed** — for free, from the outer `sweep`. -/
theorem nsmul_u₂_mem_wedgeFull {B : Set (ℤ × ℤ)} {vl u₂ : ℤ × ℤ} :
    ∀ z ∈ wedgeFull B vl u₂, ∀ t : ℕ, z + (t : ℤ) • u₂ ∈ wedgeFull B vl u₂ := by
  rintro z hz t
  have hz' : ∃ g ∈ fullSweep B vl, ∃ s : ℕ, z = g + (s : ℤ) • u₂ := hz
  obtain ⟨g, hg, s, rfl⟩ := hz'
  refine ⟨g, hg, s + t, ?_⟩
  push_cast
  rw [add_smul]
  abel

/-- **🔴 The stage-2 seam, reduced to a single hypothesis.**

Combining `zsmul_vl_mem_wedgeFull` and `nsmul_u₂_mem_wedgeFull` with
`exists_stage2_data_of_ambient` at `P := wedgeFull B vl u₂`: both closure hypotheses are
**automatic**, so the entire periodicity half of the stage-2 residual reduces to the single
statement `PeriodOn x (wedgeFull B vl u₂) h`.

**This is the honest name of the remaining debt.**  Note what it is *not*: it is not a corner
question, not a frame question, and not a choice of `R` — `R` may be taken to be `{b₀}`.  And
note the symmetry with §2: `wedgeFull B vl u₂` is precisely the set the *old* residual asked
to be **non**-periodic (the deleted `hnot`).  Having removed that demand, the same set is now
where the periodicity must come from.

原文：b3_colle2.txt:795-802（`hvl` 那一半）、:808（`hu₂` 那一半）、:804（Claim 4.6 的周期性）。 -/
theorem exists_stage2_data_of_periodOn_wedgeFull {A : Type*} {x : Config A}
    {B : Set (ℤ × ℤ)} {vl u₂ b₀ h : ℤ × ℤ}
    (hb₀ : b₀ ∈ wedgeFull B vl u₂)
    (hP : PeriodOn x (wedgeFull B vl u₂) h) :
    ∃ (R : Set (ℤ × ℤ)) (b : ℤ × ℤ), b ∈ R ∧ PeriodOn x (chainFull R vl u₂ b 0) h :=
  exists_stage2_data_of_ambient hb₀ zsmul_vl_mem_wedgeFull nsmul_u₂_mem_wedgeFull hP

/-- **The stage-2 seam, all the way down to the paper's row induction.**

Composes `periodOn_wedgeFull_of_layers` (`TowerBuild.lean`) with
`exists_stage2_data_of_periodOn_wedgeFull`.  The input is now exactly what `:795-802` provides:
periodicity **one row at a time**, with no relation asserted between rows and no ordering
inside a row.

原文：b3_colle2.txt:795-802（逐行归纳）、:808（ℕ-sweep）、:804（Claim 4.6 给出周期 `c`）。 -/
theorem exists_stage2_data_of_layers {A : Type*} {x : Config A}
    {B : Set (ℤ × ℤ)} {vl u₂ b₀ : ℤ × ℤ} {k : ℤ}
    (hb₀ : b₀ ∈ wedgeFull B vl u₂)
    (hlayer : ∀ t : ℕ, PeriodOn x
        {z | ∃ g ∈ fullSweep B vl, z = g + (t : ℤ) • u₂} (k • vl)) :
    ∃ (R : Set (ℤ × ℤ)) (b : ℤ × ℤ),
      b ∈ R ∧ PeriodOn x (chainFull R vl u₂ b 0) (k • vl) :=
  exists_stage2_data_of_periodOn_wedgeFull hb₀ (periodOn_wedgeFull_of_layers hlayer)

/-- **Stage one's region is not `ℤ·vl`-invariant** — the negative half of the seam.
`coneRegion B vl u'` sweeps `vl` forward only (`ConeRegion.lean:68`), so the hypothesis `hvl`
of `wedgeFull_subset_of_invariant` genuinely fails for it.  Witness: `B = {(0,0)}`,
`vl = (1,0)`, `u' = (0,1)`, `z = (0,0)`, `k = -1`; the cone is the first quadrant and
`(-1,0)` is outside it.

**Reading.**  This does *not* say the stage-2 frame is unreachable.  It says the upgrade from
`ℕ·vl` to `ℤ·vl` must be *done*, and that Collé does it at `:795-802` by the line-by-line
induction — it is not free from stage one. -/
theorem not_forall_coneRegion_zsmul_vl_mem :
    ∃ (B : Set (ℤ × ℤ)) (vl u' z : ℤ × ℤ) (k : ℤ),
      z ∈ Nivat.ConeRegion.coneRegion B vl u' ∧
        z + k • vl ∉ Nivat.ConeRegion.coneRegion B vl u' := by
  refine ⟨{((0 : ℤ), (0 : ℤ))}, (1, 0), (0, 1), (0, 0), -1, ?_, ?_⟩
  · rw [Nivat.ConeRegion.mem_coneRegion_iff]
    exact ⟨(0, 0), rfl, 0, 0, by simp⟩
  · rw [Nivat.ConeRegion.mem_coneRegion_iff]
    rintro ⟨b, hb, s, t, hz⟩
    simp only [Set.mem_singleton_iff] at hb
    subst hb
    have h1 := congrArg Prod.fst hz
    simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul] at h1
    omega

/-- **`chainFull` 在 `vl` 方向有下界** —— 直接就是 `cut` 的第二分量。

原文：b3_colle2.txt:386（`(ℓ,ℓ′)`-region 的定义：**凸集，恰有两条半无限边**，
一条平行 `ℓ`、一条平行 `ℓ′`）、:818（`𝓡^n_I` 是 `𝓡_I` 沿 `v⃗_{ℓ_{I−1}}` 的 `ℤ₊`-扫掠再按
`dist ≤ d_n` 截断）。

**量词对应**：`dot (expNormal u₂ vl) z` 是 `:818` 里的 `dist(·, ℓ′_{𝓡_I})`（差一个符号与幺模标定），
`expLevel u₂ vl b₀ k = dot (expNormal u₂ vl) b₀ - k` 是 `d_n`，`k` 是 `n`。 -/
theorem chainFull_dot_expNormal_ge {R : Set (ℤ × ℤ)} {vl u₂ b₀ : ℤ × ℤ} {k : ℕ}
    {z : ℤ × ℤ} (hz : z ∈ chainFull R vl u₂ b₀ k) :
    dot (expNormal u₂ vl) b₀ - (k : ℤ) ≤ dot (expNormal u₂ vl) z :=
  hz.2

/-- **`chainFull` 是楔形，不是双向带** —— 沿 `-vl` 走有限步必然掉出去。

原文：b3_colle2.txt:386。`(ℓ,ℓ′)`-region 有**两条**半无限边，所以两个方向都是单侧的。

🔴 **这条订正 `RegionSteps.lean:1179` / `:1313-1314` 反复出现的读法**
「`chainFull` 沿 `±vl` 双向扫」。双向的是**截断之前**的 `wedgeFull`
（`L1RegionBuild.lean:230`，`fullSweep` 是 `ℤ·vl`）；`chainFull` 的截法向 `expNormal u₂ vl`
满足 `dot · vl = 1`（`L1RegionBuild.dot_expNormal_vl`），所以截断把 `-vl` 的尾巴切掉了，
`vl`-坐标下界为 `dot (expNormal u₂ vl) b₀ - k - dot (expNormal u₂ vl) r`。

**推论（对 `RegionSteps.lean:1581` 的消费者）**：`chainFull ⊆ coneRegion` 之所以会失败
（`ConeHbase.not_chainFull_subset_coneRegion`）**不是**因为左边双向、右边单向——两边都是单向的——
而是因为**两个下界的位置不同**。`b₀` 与 `k` 都还是存在量词，所以这是一个**可调**的量，
不是结构性障碍。 -/
theorem chainFull_vl_bddBelow {R : Set (ℤ × ℤ)} {vl u₂ b₀ r : ℤ × ℤ} {k : ℕ}
    (hunimod : det u₂ vl = 1 ∨ det u₂ vl = -1) (s : ℤ)
    (hs : r + s • vl ∈ chainFull R vl u₂ b₀ k) :
    dot (expNormal u₂ vl) b₀ - (k : ℤ) - dot (expNormal u₂ vl) r ≤ s := by
  have h1 : dot (expNormal u₂ vl) vl = 1 := dot_expNormal_vl hunimod
  have h2 := chainFull_dot_expNormal_ge hs
  rw [dot_add, dot_smul_right, h1, mul_one] at h2
  omega

/-- **`R := {b₀}` 时 `chainFull` 恰是锥** —— 截断把 `fullSweep` 的 `-vl` 尾巴整根切掉。

原文：b3_colle2.txt:386（`(ℓ,ℓ′)`-region：凸集，恰两条半无限边）、:818（`𝓡^n_I`）。

**这条是 `RegionSteps.lean:1581` 的化简器，而且是无损的**：
`chainFull` 对底集单调，`b₀ ∈ R` 时 `chainFull {b₀} … ⊆ chainFull R …`，
所以由 `PeriodOn.mono`，「∃ R b₀, b₀ ∈ R ∧ PeriodOn (chainFull R vl u₂ b₀ 0)」
与「∃ b₀, PeriodOn (coneRegion {b₀} vl u₂)」**等价**，不是加强也不是减弱。

化简后残债落在 `coneRegion` 上——原文自己的对象——于是
`periodOn_coneRegion_of_lines` 可以直接对着它说话。 -/
theorem chainFull_singleton_eq_coneRegion {vl u₂ b₀ : ℤ × ℤ}
    (hunimod : det u₂ vl = 1 ∨ det u₂ vl = -1) :
    chainFull ({b₀} : Set (ℤ × ℤ)) vl u₂ b₀ 0
      = Nivat.ConeRegion.coneRegion ({b₀} : Set (ℤ × ℤ)) vl u₂ := by
  have hadd : ∀ (b : ℤ × ℤ) (s t : ℤ),
      dot (expNormal u₂ vl) (b + s • vl + t • u₂) = dot (expNormal u₂ vl) b + s := by
    intro b s t
    rw [dot_add, dot_add, dot_smul_right, dot_smul_right, dot_expNormal_vl hunimod,
      dot_expNormal_u']
    ring
  ext z
  simp only [chainFull, Nivat.L1Region.cut, Set.mem_inter_iff,
    Nivat.ConeRegion.mem_coneRegion_iff, Set.mem_singleton_iff,
    halfPlaneGE, Set.mem_setOf_eq, expLevel, Nat.cast_zero, sub_zero, wedgeFull]
  constructor
  · rintro ⟨hw, hge⟩
    obtain ⟨g, hg, t, rfl⟩ := hw
    rw [mem_fullSweep_iff] at hg
    obtain ⟨b, hb, k, rfl⟩ := hg
    simp only [Set.mem_singleton_iff] at hb
    subst hb
    rw [hadd] at hge
    exact ⟨_, rfl, k.toNat, t, by rw [Int.toNat_of_nonneg (by omega)]⟩
  · rintro ⟨b, rfl, s, t, rfl⟩
    refine ⟨⟨b + (s : ℤ) • vl, ?_, t, rfl⟩, ?_⟩
    · rw [mem_fullSweep_iff]; exact ⟨b, rfl, (s : ℤ), rfl⟩
    · rw [hadd]; omega

/-- **剪切量 `K ≤ 0` 时，单点锥含于原底锥。**

原文：b3_colle2.txt:808（`𝓡_i := {g + t·v⃗_{ℓ_i} : g ∈ 𝓡_{i+1}, t ∈ ℤ₊}`，单侧 `ℤ₊`）。

`b₀ + s•vl + t•(u' − K•vl) = b₀ + (s − tK)•vl + t•u'`；`K ≤ 0` 时 `s − tK ≥ 0`，
所以落在 `coneRegion B vl u'` 里。`K > 0` 时 `t → ∞` 使 `s − tK → −∞`，包含**不成立**
（这正是 `ShearSign.nonpos_shear_of_chainFull_subset` 的方向）。 -/
theorem coneRegion_singleton_shear_subset
    {B : Set (ℤ × ℤ)} {vl u' b₀ : ℤ × ℤ} {K : ℤ} (hK : K ≤ 0) (hb₀ : b₀ ∈ B) :
    Nivat.ConeRegion.coneRegion ({b₀} : Set (ℤ × ℤ)) vl (u' - K • vl)
      ⊆ Nivat.ConeRegion.coneRegion B vl u' := by
  intro z hz
  rw [Nivat.ConeRegion.mem_coneRegion_iff] at hz ⊢
  obtain ⟨b, hb, s, t, rfl⟩ := hz
  simp only [Set.mem_singleton_iff] at hb
  subst hb
  have ht : (0 : ℤ) ≤ (t : ℤ) := Int.natCast_nonneg t
  have hs : (0 : ℤ) ≤ (s : ℤ) := Int.natCast_nonneg s
  have hmul : (0 : ℤ) ≤ (t : ℤ) * (-K) := mul_nonneg ht (neg_nonneg.mpr hK)
  have hnn : (0 : ℤ) ≤ (s : ℤ) - (t : ℤ) * K := by nlinarith
  refine ⟨b, hb₀, ((s : ℤ) - (t : ℤ) * K).toNat, t, ?_⟩
  rw [Int.toNat_of_nonneg hnn]
  module

/-- **`K ≤ 0` 时 `RegionSteps.exists_stage2_frame_of_claim46` 的残债直接由 `hbase₁` 关闭。**

原文：b3_colle2.txt:808 + `:414`（底座在正向半带 `H_B(ℓ)` 上）。

`PeriodOn.mono` 是反变的（`Lemma41.lean:662`），所以底锥上的周期性传到任何子集。
**消费者**：`RegionSteps.exists_stage2_frame_of_claim46`（`:1612` 的 `sorry`）——
只要 `WedgeAssemble.exists_shear_corner_data` 给出的 `K` 能取到 `≤ 0`。 -/
theorem periodOn_coneRegion_singleton_of_nonpos_shear
    {A : Type*} {x : Config A} {B : Set (ℤ × ℤ)} {vl u' b₀ h : ℤ × ℤ} {K : ℤ}
    (hK : K ≤ 0) (hb₀ : b₀ ∈ B)
    (hbase : PeriodOn x (Nivat.ConeRegion.coneRegion B vl u') h) :
    PeriodOn x (Nivat.ConeRegion.coneRegion ({b₀} : Set (ℤ × ℤ)) vl (u' - K • vl)) h :=
  PeriodOn.mono (coneRegion_singleton_shear_subset hK hb₀) hbase

end Nivat.ColleReg

section Receipts

#print axioms Nivat.ColleReg.expLevel_exhausts
#print axioms Nivat.ColleReg.exists_greatest_periodOn_cut
#print axioms Nivat.ColleReg.exists_greatest_periodOn_chainFull
#print axioms Nivat.ColleReg.chainFull_eq_cut_wedgeFull
#print axioms Nivat.ColleReg.wedgeFull_subset_of_invariant
#print axioms Nivat.ColleReg.chainFull_subset_of_invariant
#print axioms Nivat.ColleReg.periodOn_chainFull_of_invariant
#print axioms Nivat.ColleReg.wedgeFull_eq_self_of_invariant
#print axioms Nivat.ColleReg.periodOn_wedgeFull_of_invariant
#print axioms Nivat.ColleReg.wedgeFull_subset_of_ambient
#print axioms Nivat.ColleReg.chainFull_subset_of_ambient
#print axioms Nivat.ColleReg.periodOn_chainFull_of_ambient
#print axioms Nivat.ColleReg.exists_stage2_data_of_ambient
#print axioms Nivat.ColleReg.zsmul_vl_mem_wedgeFull
#print axioms Nivat.ColleReg.nsmul_u₂_mem_wedgeFull
#print axioms Nivat.ColleReg.exists_stage2_data_of_periodOn_wedgeFull
#print axioms Nivat.ColleReg.exists_stage2_data_of_layers
#print axioms Nivat.ColleReg.not_forall_coneRegion_zsmul_vl_mem

end Receipts
#print axioms Nivat.ColleReg.chainFull_dot_expNormal_ge
#print axioms Nivat.ColleReg.chainFull_vl_bddBelow
#print axioms Nivat.ColleReg.chainFull_singleton_eq_coneRegion
#print axioms Nivat.ColleReg.coneRegion_singleton_shear_subset
#print axioms Nivat.ColleReg.periodOn_coneRegion_singleton_of_nonpos_shear
