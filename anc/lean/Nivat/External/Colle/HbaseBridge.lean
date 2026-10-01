/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.Claim43
import Nivat.External.Colle.L1RegionBuild
import Nivat.External.Colle.L1CoverWedge

/-!
# `HbaseBridge` — `ofWedge`'s `hbase` slot, reduced to four named sweep hypotheses

`Nivat.ColleReg.ofWedge` (`L1RegionBuild.lean:344`) takes one opaque obligation about `ξ`,

```
hbase : Colle41.PeriodOn (T e ξ) (chainFull B vl u' b₀ 0) (c • vl)
```

and its own docstring says of it and `hinf` that they "name `ξ` and are genuinely open — no
set-shape argument can supply them".  That is right about *set shapes*, but it leaves the
obligation as a single blob nobody can split work on.  This file splits it.

## The measurement behind the file

The step that was expected to be a gap — Claim 4.3's sweep concludes *configuration agreement*
`x = y`, whereas `hbase` wants a `PeriodOn` on a region — **is not a gap, and the bridge is not
the `L3Cover` one.**  `Nivat.Colle43.periodOn_of_agree_T` (`Claim43.lean:429`) turns agreement
with the translate into `PeriodOn` with *no* closure, invariance or covering hypothesis, because
`PeriodOn` is Definition 2.11's overlap-only — hence weaker — statement:

```
theorem periodOn_of_agree_T (hag : ∀ z ∈ U, x z = T h x z) : PeriodOn x U h
```

and `Nivat.Colle43.claim43_periodOn_of_sweep` (`Claim43.lean:435`) already packages sweep plus
bridge, concluding `PeriodOn x K h'` directly.  So `hbase` needs no new periodicity-propagation
argument at all; it needs the four inputs of that packaging, instantiated at
`K := chainFull B vl u' b₀ k`.

## ⚠ How to read this file

**"The propagation gap is zero" does not read as "`hbase` is nearly done".**  The content did
not vanish — it moved into the geometry of `hwin`/`hK` and into `hgen`.  What the file buys is
that those are now four *separately dispatchable* named holes instead of one blob:

* `hgen : Nivat.Colle.GeneratesAt η S a` — Collé Lemma 2.5 / Lemma 2.6.  ⚠ `IsGeneratingSet`
  (`Generating.lean:58`) hands out `GeneratesAt` only where `LatticeConvex (S.erase a)` holds,
  i.e. at *vertices*; `a` is constrained, it is not an arbitrary point of `S`.
* `hD` — the seed of (4.4): `T e ξ` already agrees with its `c • vl`-translate on `D`.
* `hwin` — every punctured window translate lands in the seed or in a strictly earlier stage.
* `hK` — the covering `chainFull B vl u' b₀ k ⊆ D ∪ ⋃ i, Set.range (enum i)`.

`hK` is the only one with half-plane content, and it is a *containment*, i.e. exactly the
direction `Nivat.L1Prim.halfPlaneGE_forward_of_dot_nonneg` serves.  Nothing here touches the
`vl`-invariance question of `L1Prim.lean` §8: `periodOn_of_agree_T` asks for no invariance in
any direction.

Scope: this file is about `hbase` / `chainFull`.  It says nothing about leaf L3's `genClosure`
target, which was not measured.
-/

set_option autoImplicit false

namespace Nivat.HbaseBridge

open Nivat Nivat.Colle Nivat.Colle41 Nivat.Colle43 Nivat.ColleReg

/-! ## §1  The orbit-closure side is free

`claim43_periodOn_of_sweep` needs `T e ξ ∈ orbitClosure η`.  Taking `η := ξ` this is free for
every `e`, so it is not one of the residuals.  Every consumer of the bridge below wants it. -/

/-- Every translate of `ξ` lies in `ξ`'s own orbit closure. -/
theorem T_mem_orbitClosure_self {A : Type*} (ξ : Config A) (e : ℤ × ℤ) :
    T e ξ ∈ orbitClosure ξ :=
  T_mem_of_mem_orbitClosure (self_mem_orbitClosure ξ) e

/-! ## §2  `hbase` from the sweep

The binders are `claim43_periodOn_of_sweep`'s own, specialised at `x := T e ξ`, `h' := c • vl`,
`K := chainFull B vl u' b₀ k`.  Nothing else is needed: no half-plane closure lemma, no
invariance, no `L3Cover` detour. -/

/-- **`hbase` at an arbitrary index `k`, from Claim 4.3's sweep.**  Conclusion is verbatim the
`hbase` binder of `Nivat.ColleReg.ofWedgeAt` (`L1RegionBuild.lean:389`). -/
theorem hbase_at_of_sweep {ξ η : Config ℤ} {e : ℤ × ℤ}
    (hx : T e ξ ∈ orbitClosure η)
    {S : Finset (ℤ × ℤ)} {a : ℤ × ℤ} (hgen : GeneratesAt η S a)
    {B : Set (ℤ × ℤ)} {vl u' b₀ : ℤ × ℤ} {c : ℤ} (k : ℕ)
    {D : Set (ℤ × ℤ)} (hD : ∀ z ∈ D, (T e ξ) z = T (c • vl) (T e ξ) z)
    (enum : ℕ → ℕ → ℤ × ℤ)
    (hwin : ∀ i j : ℕ, ∀ z ∈ S.erase a,
      z + (enum i j - a) ∈
        D ∪ (⋃ i' ∈ {i' | i' < i}, Set.range (enum i')) ∪ (enum i '' {j' | j' < j}))
    (hK : chainFull B vl u' b₀ k ⊆ D ∪ (⋃ i, Set.range (enum i))) :
    Colle41.PeriodOn (T e ξ) (chainFull B vl u' b₀ k) (c • vl) :=
  claim43_periodOn_of_sweep hx hgen (c • vl) hD enum hwin hK

/-- **`hbase` at index `0`** — verbatim the `hbase` binder of `Nivat.ColleReg.ofWedge`
(`L1RegionBuild.lean:347`).  See `ofWedgeOfSweep` below for the kernel check that it is
verbatim: it is fed into that slot. -/
theorem hbase_of_sweep {ξ η : Config ℤ} {e : ℤ × ℤ}
    (hx : T e ξ ∈ orbitClosure η)
    {S : Finset (ℤ × ℤ)} {a : ℤ × ℤ} (hgen : GeneratesAt η S a)
    {B : Set (ℤ × ℤ)} {vl u' b₀ : ℤ × ℤ} {c : ℤ}
    {D : Set (ℤ × ℤ)} (hD : ∀ z ∈ D, (T e ξ) z = T (c • vl) (T e ξ) z)
    (enum : ℕ → ℕ → ℤ × ℤ)
    (hwin : ∀ i j : ℕ, ∀ z ∈ S.erase a,
      z + (enum i j - a) ∈
        D ∪ (⋃ i' ∈ {i' | i' < i}, Set.range (enum i')) ∪ (enum i '' {j' | j' < j}))
    (hK : chainFull B vl u' b₀ 0 ⊆ D ∪ (⋃ i, Set.range (enum i))) :
    Colle41.PeriodOn (T e ξ) (chainFull B vl u' b₀ 0) (c • vl) :=
  hbase_at_of_sweep hx hgen 0 hD enum hwin hK

/-- The same with `η := ξ`, so that `hx` is discharged by §1 and the caller supplies only the
four residuals. -/
theorem hbase_of_sweep_self {ξ : Config ℤ} {e : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} {a : ℤ × ℤ} (hgen : GeneratesAt ξ S a)
    {B : Set (ℤ × ℤ)} {vl u' b₀ : ℤ × ℤ} {c : ℤ}
    {D : Set (ℤ × ℤ)} (hD : ∀ z ∈ D, (T e ξ) z = T (c • vl) (T e ξ) z)
    (enum : ℕ → ℕ → ℤ × ℤ)
    (hwin : ∀ i j : ℕ, ∀ z ∈ S.erase a,
      z + (enum i j - a) ∈
        D ∪ (⋃ i' ∈ {i' | i' < i}, Set.range (enum i')) ∪ (enum i '' {j' | j' < j}))
    (hK : chainFull B vl u' b₀ 0 ⊆ D ∪ (⋃ i, Set.range (enum i))) :
    Colle41.PeriodOn (T e ξ) (chainFull B vl u' b₀ 0) (c • vl) :=
  hbase_of_sweep (T_mem_orbitClosure_self ξ e) hgen hD enum hwin hK

/-! ## §3  Kernel check that the statement is the one `ofWedge` wants

The two definitions below are not convenience wrappers first and foremost — they are the
evidence that §2's conclusion is *verbatim* `ofWedge`'s / `ofWedgeAt`'s `hbase` slot: if it
drifted by so much as an index, these would not elaborate.  They also happen to be the shape a
consumer wants, since they leave exactly the four residuals plus the five shape hypotheses on
`B`/`vl`/`u'` plus `hinf`. -/

/-- `ofWedge`, with its `hbase` slot filled by the sweep. -/
noncomputable def ofWedgeOfSweep {ξ : Config ℤ} {e vl u' : ℤ × ℤ} {c : ℤ} {B : Set (ℤ × ℤ)}
    {b₀ : ℤ × ℤ}
    (hb₀ : b₀ ∈ B) (hB : IsLatticeConvexRegion B) (hvl : Primitive vl) (hu' : Primitive u')
    (hlev : Nivat.RegionSweep.LevelInterval B vl) (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    {S : Finset (ℤ × ℤ)} {a : ℤ × ℤ} (hgen : GeneratesAt ξ S a)
    {D : Set (ℤ × ℤ)} (hD : ∀ z ∈ D, (T e ξ) z = T (c • vl) (T e ξ) z)
    (enum : ℕ → ℕ → ℤ × ℤ)
    (hwin : ∀ i j : ℕ, ∀ z ∈ S.erase a,
      z + (enum i j - a) ∈
        D ∪ (⋃ i' ∈ {i' | i' < i}, Set.range (enum i')) ∪ (enum i '' {j' | j' < j}))
    (hK : chainFull B vl u' b₀ 0 ⊆ D ∪ (⋃ i, Set.range (enum i)))
    (hinf : ¬ Colle41.PeriodOn (T e ξ) (wedgeFull B vl u') (c • vl)) :
    Nivat.L1Region.RegionFamily (T e ξ) vl u' c :=
  ofWedge hb₀ hB hvl hu' hlev hunimod (hbase_of_sweep_self hgen hD enum hwin hK) hinf

/-- `ofWedgeAt`, with its `hbase` slot filled by the sweep at the same index `k`. -/
noncomputable def ofWedgeAtOfSweep {ξ : Config ℤ} {e vl u' : ℤ × ℤ} {c : ℤ} {B : Set (ℤ × ℤ)}
    {b₀ : ℤ × ℤ}
    (hb₀ : b₀ ∈ B) (hB : IsLatticeConvexRegion B) (hvl : Primitive vl) (hu' : Primitive u')
    (hlev : Nivat.RegionSweep.LevelInterval B vl) (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (k : ℕ)
    {S : Finset (ℤ × ℤ)} {a : ℤ × ℤ} (hgen : GeneratesAt ξ S a)
    {D : Set (ℤ × ℤ)} (hD : ∀ z ∈ D, (T e ξ) z = T (c • vl) (T e ξ) z)
    (enum : ℕ → ℕ → ℤ × ℤ)
    (hwin : ∀ i j : ℕ, ∀ z ∈ S.erase a,
      z + (enum i j - a) ∈
        D ∪ (⋃ i' ∈ {i' | i' < i}, Set.range (enum i')) ∪ (enum i '' {j' | j' < j}))
    (hK : chainFull B vl u' b₀ k ⊆ D ∪ (⋃ i, Set.range (enum i)))
    (hinf : ¬ Colle41.PeriodOn (T e ξ) (wedgeFull B vl u') (c • vl)) :
    Nivat.L1Region.RegionFamily (T e ξ) vl u' c :=
  ofWedgeAt hb₀ hB hvl hu' hlev hunimod k
    (hbase_at_of_sweep (T_mem_orbitClosure_self ξ e) hgen k hD enum hwin hK) hinf

/-! ## §4  The form for a consumer that already binds `IsGeneratingSet`

Measured against the one live consumer of `ofWedgeAt`,
`Nivat.ColleReg.L1Claim.exists_L1MaxBResidual_of_wedgeAt` (`L1Claim.lean:230`, whose body calls
`ofWedgeAt … k hbase hinf` at `:263`): that theorem **already binds**
`hSgen : Nivat.Colle.IsGeneratingSet ξ S`.  By `Generating.lean:58` an `IsGeneratingSet` hands
out `GeneratesAt ξ S a` at every `a ∈ S` with `Nivat.LatticeConvex (S.erase a)`.

So in that slot `hgen` is **not** an open hole — what is open is *a vertex of `S`*, which is
exactly the existential AnfpL's `VertexFromEdge` produces.  The version below takes the
generating set plus the vertex, so such a consumer needs no `GeneratesAt` of its own.

⚠ This does not shrink the obligation, it relocates it: `ha`/`hconv` are the vertex, and
`LatticeConvex (S.erase a)` is where Lemma 2.6's "no edge has normal `rot90 ℓ`" is spent. -/

/-- `hbase` at index `k` for a consumer holding an `IsGeneratingSet` and a vertex of it. -/
theorem hbase_at_of_sweep_of_isGeneratingSet {ξ : Config ℤ} {e : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} (hS : Nivat.Colle.IsGeneratingSet ξ S)
    {a : ℤ × ℤ} (ha : a ∈ S) (hconv : Nivat.LatticeConvex (S.erase a))
    {B : Set (ℤ × ℤ)} {vl u' b₀ : ℤ × ℤ} {c : ℤ} (k : ℕ)
    {D : Set (ℤ × ℤ)} (hD : ∀ z ∈ D, (T e ξ) z = T (c • vl) (T e ξ) z)
    (enum : ℕ → ℕ → ℤ × ℤ)
    (hwin : ∀ i j : ℕ, ∀ z ∈ S.erase a,
      z + (enum i j - a) ∈
        D ∪ (⋃ i' ∈ {i' | i' < i}, Set.range (enum i')) ∪ (enum i '' {j' | j' < j}))
    (hK : chainFull B vl u' b₀ k ⊆ D ∪ (⋃ i, Set.range (enum i))) :
    Colle41.PeriodOn (T e ξ) (chainFull B vl u' b₀ k) (c • vl) :=
  hbase_at_of_sweep (T_mem_orbitClosure_self ξ e) (hS.2.2 a ha hconv) k hD enum hwin hK

/-! ## §5  The four holes are **not** independent: `D` is squeezed from both sides

Measured 2026-09-19 (team-lead's second interface-consistency assignment).  `hD` pushes `D`
down, `hwin`/`hK` push it up, and the upper bound comes from a binder `ofWedge` already
carries — `hinf`.  So `D` cannot be chosen by whoever builds `hD` in isolation. -/

/-- `hK` is monotone in `D`: a bigger seed only helps. -/
theorem hK_mono {K D D' : Set (ℤ × ℤ)} (hDD : D ⊆ D') {enum : ℕ → ℕ → ℤ × ℤ}
    (hK : K ⊆ D ∪ (⋃ i, Set.range (enum i))) :
    K ⊆ D' ∪ (⋃ i, Set.range (enum i)) :=
  hK.trans (Set.union_subset_union_left _ hDD)

/-- `hwin` is monotone in `D` as well — same direction as `hK`. -/
theorem hwin_mono {S : Finset (ℤ × ℤ)} {a : ℤ × ℤ} {D D' : Set (ℤ × ℤ)} (hDD : D ⊆ D')
    {enum : ℕ → ℕ → ℤ × ℤ}
    (hwin : ∀ i j : ℕ, ∀ z ∈ S.erase a,
      z + (enum i j - a) ∈
        D ∪ (⋃ i' ∈ {i' | i' < i}, Set.range (enum i')) ∪ (enum i '' {j' | j' < j})) :
    ∀ i j : ℕ, ∀ z ∈ S.erase a,
      z + (enum i j - a) ∈
        D' ∪ (⋃ i' ∈ {i' | i' < i}, Set.range (enum i')) ∪ (enum i '' {j' | j' < j}) := by
  intro i j z hz
  exact Set.union_subset_union_left _
    (Set.union_subset_union_left _ hDD) (hwin i j z hz)

/-- **The upper bound on `D`, from `hinf`.**  `hD` cannot be had on a seed swallowing
`wedgeFull`: `periodOn_of_agree_T` would then contradict `ofWedge`'s own `hinf`. -/
theorem not_hD_of_wedgeFull_subset {ξ : Config ℤ} {e : ℤ × ℤ} {B : Set (ℤ × ℤ)}
    {vl u' : ℤ × ℤ} {c : ℤ} {D : Set (ℤ × ℤ)}
    (hinf : ¬ Colle41.PeriodOn (T e ξ) (wedgeFull B vl u') (c • vl))
    (hsub : wedgeFull B vl u' ⊆ D) :
    ¬ (∀ z ∈ D, (T e ξ) z = T (c • vl) (T e ξ) z) := fun hD =>
  hinf (periodOn_of_agree_T (fun z hz => hD z (hsub hz)))

/-- **The lower bound on `D`.**  `hwin` at `i = j = 0` has both union tails empty, so a whole
translate of `S.erase a` must already lie in the seed. -/
theorem window_zero_subset_D {S : Finset (ℤ × ℤ)} {a : ℤ × ℤ} {D : Set (ℤ × ℤ)}
    {enum : ℕ → ℕ → ℤ × ℤ}
    (hwin : ∀ i j : ℕ, ∀ z ∈ S.erase a,
      z + (enum i j - a) ∈
        D ∪ (⋃ i' ∈ {i' | i' < i}, Set.range (enum i')) ∪ (enum i '' {j' | j' < j}))
    (z : ℤ × ℤ) (hz : z ∈ S.erase a) : z + (enum 0 0 - a) ∈ D := by
  have h := hwin 0 0 z hz
  rcases h with h | h
  · rcases h with h | h
    · exact h
    · simp at h
  · simp at h

/-- Once `D` is fixed, `hK` is exactly "the rows cover what `D` misses". -/
theorem hK_iff_diff {K D U : Set (ℤ × ℤ)} : K ⊆ D ∪ U ↔ K \ D ⊆ U := by
  constructor
  · rintro h z ⟨hz, hzD⟩
    exact (h hz).resolve_left hzD
  · intro h z hz
    by_cases hzD : z ∈ D
    · exact Or.inl hzD
    · exact Or.inr (h ⟨hz, hzD⟩)

/-! ## §6  The period direction is `vl`, and `hD`'s seed must run along it

`Nivat.Colle43.agree_T_on_halfStripFrom` (`Claim43.lean:401`) is the intended producer of `hD`.
Its direction binder is *named* `u'`, but a binder name is not an actual argument
(PROTOCOL §23): its conclusion translates by `(n*q) • (that direction)`, while `hD` wants
`c • vl`.  With a unimodular pair those are reconcilable only at direction `:= vl`. -/

/-- With a unimodular pair, `c • vl` is a multiple of `u'` only when `c = 0`. -/
theorem smul_vl_ne_smul_u' {u' vl : ℤ × ℤ} (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    {c m : ℤ} (hc : c ≠ 0) : c • vl ≠ m • u' := by
  intro h
  apply hc
  have := congrArg (Nivat.LE2.dot (expNormal u' vl)) h
  rwa [dot_smul_right, dot_smul_right, dot_expNormal_vl hunimod,
    dot_expNormal_u' (u' := u') (vl := vl), mul_zero, mul_one] at this

/-- **`hD` from the half-strip seed, at the only direction that types.**  ⚠ The strip runs
along `vl`, not `u'`, and `c` is forced to be the natural number `n * q` — in particular
`0 < c` and `q ∣ c`.  ⚠ The strip's base is a `Finset`, while `chainFull`'s `B` is a `Set`;
they are not the same object. -/
theorem hD_of_halfStrip {ξ : Config ℤ} {e : ℤ × ℤ} {Bf : Finset (ℤ × ℤ)} {vl : ℤ × ℤ}
    {t₁ : ℤ} {q n : ℕ} {c : ℤ} (hc : c = ((n * q : ℕ) : ℤ))
    (hqper : ∀ g ∈ Bf, ∀ t : ℤ, t₁ ≤ t →
      (T e ξ) (g + (t + (q : ℤ)) • vl) = (T e ξ) (g + t • vl)) :
    ∀ z ∈ halfStripFrom Bf vl t₁, (T e ξ) z = T (c • vl) (T e ξ) z := by
  subst hc
  exact agree_T_on_halfStripFrom (x := T e ξ) (B := Bf) (u' := vl) (t₁ := t₁) hqper n

/-! ## §7  Index discipline: the covering is index-`0`-sharp, and that is free

`expLevel` descends by one per step, so `chainFull` **grows** with the index and index `0` is
the *smallest* slice — hence the *weakest* `hbase`.  A consumer may always pin `k := 0`, which
is the index Afill's covering (`L1CoverWedge.coverEnum`) serves. -/

theorem chainFull_zero_subset (B : Set (ℤ × ℤ)) (vl u' b₀ : ℤ × ℤ) (k : ℕ) :
    chainFull B vl u' b₀ 0 ⊆ chainFull B vl u' b₀ k := by
  rintro z ⟨hz1, hz2⟩
  exact ⟨hz1, le_trans (expLevel_antitone u' vl b₀ (Nat.zero_le k)) hz2⟩

/-- `hbase` at any index implies `hbase` at index `0`. -/
theorem hbase_zero_of_hbase {ξ : Config ℤ} {e : ℤ × ℤ} {B : Set (ℤ × ℤ)} {vl u' b₀ : ℤ × ℤ}
    {c : ℤ} (k : ℕ)
    (hbase : Colle41.PeriodOn (T e ξ) (chainFull B vl u' b₀ k) (c • vl)) :
    Colle41.PeriodOn (T e ξ) (chainFull B vl u' b₀ 0) (c • vl) :=
  Colle41.PeriodOn.mono (chainFull_zero_subset B vl u' b₀ k) hbase

/-! ## §8  Why the covering is index-`0`-sharp: an impossibility, not a proof gap

`Nivat.ColleReg.coverEnum` (`L1CoverWedge.lean:387`) bases row `i` at level
`dot (expNormal u' vl) b₀ + n` with `n : ℕ`, and sweeping by `u'` leaves the level fixed
(`dot_expNormal_u' = 0`).  So the union of its rows never reaches below `expLevel u' vl b₀ 0`,
while `chainFull … 1` does.  The index-`0` restriction in `hK_of_coverEnum` is therefore not a
weakness of its proof — no proof exists.  By §7 this costs nothing. -/

theorem dot_coverEnum (vl u' b₀ : ℤ × ℤ) (hunimod : det u' vl = 1 ∨ det u' vl = -1) (i j : ℕ) :
    Nivat.LE2.dot (expNormal u' vl) (coverEnum vl u' b₀ i j)
      = Nivat.LE2.dot (expNormal u' vl) b₀ + ((pairEnum i).2 : ℤ) := by
  simp only [coverEnum, Nivat.LE2.dot_add, dot_smul_right, dot_expNormal_vl hunimod,
    dot_expNormal_u' (u' := u') (vl := vl), mul_zero, mul_one]
  ring

theorem expLevel_le_dot_coverEnum (vl u' b₀ : ℤ × ℤ)
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) (i j : ℕ) :
    expLevel u' vl b₀ 0 ≤ Nivat.LE2.dot (expNormal u' vl) (coverEnum vl u' b₀ i j) := by
  rw [dot_coverEnum vl u' b₀ hunimod]
  simp only [expLevel, Nat.cast_zero, sub_zero]
  omega

/-- **`hK_of_coverEnum` at index `1` is false** (with `D := ∅`). -/
theorem not_hK_coverEnum_one {B : Set (ℤ × ℤ)} {vl u' b₀ : ℤ × ℤ} (hb₀ : b₀ ∈ B)
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) :
    ¬ (chainFull B vl u' b₀ 1 ⊆
        (∅ : Set (ℤ × ℤ)) ∪ (⋃ i, Set.range (coverEnum vl u' b₀ i))) := by
  intro hsub
  obtain ⟨z, hzw, hz1, hz0⟩ := expLevel_gap hb₀ hunimod 0
  rcases hsub ⟨hzw, hz1⟩ with h | h
  · exact absurd h (Set.notMem_empty z)
  · simp only [Set.mem_iUnion, Set.mem_range] at h
    obtain ⟨i, j, rfl⟩ := h
    exact absurd hz0 (not_lt.mpr (expLevel_le_dot_coverEnum vl u' b₀ hunimod i j))

/-! ## §9  Afill's covering is *exactly* the level-`0` half-plane

§8 gave the inclusion; the reverse holds too, because `pairEnum` ranges over **all** of
`(ℤ × ℤ) × ℕ`, so every point at level `≥ expLevel … 0` is the `j = 0` entry of some row.
Consequence for dispatch: `coverEnum` is not "some" covering — it is the maximal one its shape
allows, and it is *rows of forward `u'`-rays*.  §10 shows that shape is exactly what `hwin`
cannot accept. -/

theorem iUnion_coverEnum_eq (vl u' b₀ : ℤ × ℤ) (hunimod : det u' vl = 1 ∨ det u' vl = -1) :
    (⋃ i, Set.range (coverEnum vl u' b₀ i))
      = Nivat.LE2.halfPlaneGE (expNormal u' vl) (expLevel u' vl b₀ 0) := by
  apply Set.Subset.antisymm
  · rintro z hz
    simp only [Set.mem_iUnion, Set.mem_range] at hz
    obtain ⟨i, j, rfl⟩ := hz
    exact expLevel_le_dot_coverEnum vl u' b₀ hunimod i j
  · intro w hw
    simp only [Nivat.LE2.halfPlaneGE, Set.mem_ofPred_eq, expLevel, Nat.cast_zero,
      sub_zero] at hw
    set m₀ : ℤ := Nivat.LE2.dot (expNormal u' vl) w - Nivat.LE2.dot (expNormal u' vl) b₀
      with hm₀
    set b : ℤ × ℤ := w + (-m₀) • vl with hb
    obtain ⟨i, hi⟩ := (Denumerable.eqv ((ℤ × ℤ) × ℕ)).symm.surjective (b, m₀.toNat)
    refine Set.mem_iUnion.mpr ⟨i, 0, ?_⟩
    have hdb : Nivat.LE2.dot (expNormal u' vl) b = Nivat.LE2.dot (expNormal u' vl) b₀ := by
      simp only [hb, Nivat.LE2.dot_add, dot_smul_right, dot_expNormal_vl hunimod, mul_one]
      omega
    have hn : (m₀.toNat : ℤ) = m₀ := Int.toNat_of_nonneg (by omega)
    show coverEnum vl u' b₀ i 0 = w
    unfold coverEnum pairEnum
    rw [hi]
    simp only [hdb, hn]
    simp only [hb]
    module

/-! ## §10  Why a ray-shaped `enum` cannot serve `hwin` against a `vl`-half-strip seed

This is the measurement team-lead asked for, and the answer is negative for a structural
reason that has nothing to do with `coverEnum` in particular.

`dot (expNormal u' vl)` is constant along `u'` and increases by one per `vl`-step.  So:

* a forward `u'`-ray lies in a **single level**, and is infinite there;
* a `vl`-half-strip over a **finite** base meets each level in **finitely many** points
  (`halfStripFrom_level_finite`);
* translating a row by `z - a` shifts its level by `dot m z - dot m a`.

At `i = 0` both union tails of `hwin` are empty except row `0` itself, which sits at its own
single level.  So as soon as some `z ∈ S.erase a` sits at a different level from `a`, the whole
translated ray is forced into the seed — infinitely many points at one level, into a set with
finitely many.  Contradiction.

⚠ **Read this as a constraint on `enum`, not as "`hwin` is impossible".**  What dies is the
*row-shape* `enum 0 j = enum 0 0 + j • u'`, which is precisely the shape that made `hK` free.
The escape is not to make `coverEnum` depend on `a` — a translation moves every row by the
same vector and changes no level difference — it is to give up rays for rows ordered so that
each row's window translates are already covered, i.e. Collé's line-by-line extension. -/

theorem u'_ne_zero {u' vl : ℤ × ℤ} (hunimod : det u' vl = 1 ∨ det u' vl = -1) : u' ≠ 0 := by
  rintro rfl
  rcases hunimod with h | h <;> simp [det] at h

/-- A `vl`-half-strip over a finite base meets each level line in finitely many points. -/
theorem halfStripFrom_level_finite {Bf : Finset (ℤ × ℤ)} {vl m : ℤ × ℤ} {t₁ L : ℤ}
    (hm : Nivat.LE2.dot m vl = 1) :
    {z | z ∈ halfStripFrom Bf vl t₁ ∧ Nivat.LE2.dot m z = L}.Finite := by
  apply Set.Finite.subset
    (Bf.image (fun g => g + (L - Nivat.LE2.dot m g) • vl)).finite_toSet
  rintro z ⟨⟨g, hg, t, ht, rfl⟩, hlev⟩
  simp only [Nivat.LE2.dot_add, dot_smul_right, hm, mul_one] at hlev
  refine Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨g, hg, ?_⟩)
  rw [show L - Nivat.LE2.dot m g = t by omega]

/-- A forward `u'`-ray is infinite. -/
theorem infinite_ray {w u' : ℤ × ℤ} (hu' : u' ≠ 0) :
    (Set.range (fun j : ℕ => w + (j : ℤ) • u')).Infinite := by
  apply Set.infinite_range_of_injective
  intro j k hjk
  simp only [add_right_inj] at hjk
  have : ((j : ℤ) - k) • u' = 0 := by rw [sub_smul, hjk, sub_self]
  rcases smul_eq_zero.mp this with h | h
  · exact_mod_cast sub_eq_zero.mp h
  · exact absurd h hu'

/-- **The refutation, stated for any ray-shaped row `0`.** -/
theorem not_hwin_of_row_ray_halfStrip
    {S : Finset (ℤ × ℤ)} {a : ℤ × ℤ} {Bf : Finset (ℤ × ℤ)} {vl u' : ℤ × ℤ} {t₁ : ℤ}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (enum : ℕ → ℕ → ℤ × ℤ)
    (hrow : ∀ j : ℕ, enum 0 j = enum 0 0 + (j : ℤ) • u')
    {z₀ : ℤ × ℤ} (hz₀ : z₀ ∈ S.erase a)
    (hδ : Nivat.LE2.dot (expNormal u' vl) z₀ ≠ Nivat.LE2.dot (expNormal u' vl) a) :
    ¬ (∀ i j : ℕ, ∀ z ∈ S.erase a,
        z + (enum i j - a) ∈
          halfStripFrom Bf vl t₁
            ∪ (⋃ i' ∈ {i' | i' < i}, Set.range (enum i'))
            ∪ (enum i '' {j' | j' < j})) := by
  intro hwin
  set m := expNormal u' vl with hm
  have hmvl : Nivat.LE2.dot m vl = 1 := dot_expNormal_vl hunimod
  have hmu' : Nivat.LE2.dot m u' = 0 := dot_expNormal_u' (u' := u') (vl := vl)
  set w : ℤ × ℤ := z₀ + (enum 0 0 - a) with hw
  have hray : ∀ j : ℕ, z₀ + (enum 0 j - a) = w + (j : ℤ) • u' := by
    intro j; rw [hrow j, hw]; module
  have hlevel : ∀ j : ℕ, Nivat.LE2.dot m (w + (j : ℤ) • u') = Nivat.LE2.dot m w := by
    intro j
    simp only [Nivat.LE2.dot_add, dot_smul_right, hmu', mul_zero, add_zero]
  have hrow0 : ∀ j : ℕ, Nivat.LE2.dot m (enum 0 j) = Nivat.LE2.dot m (enum 0 0) := by
    intro j; rw [hrow j]
    simp only [Nivat.LE2.dot_add, dot_smul_right, hmu', mul_zero, add_zero]
  have hwne : Nivat.LE2.dot m w ≠ Nivat.LE2.dot m (enum 0 0) := by
    have hlin : Nivat.LE2.dot m w
        = Nivat.LE2.dot m z₀ + Nivat.LE2.dot m (enum 0 0) - Nivat.LE2.dot m a := by
      simp only [hw, Nivat.LE2.dot, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]
      ring
    omega
  have hsub : (Set.range (fun j : ℕ => w + (j : ℤ) • u')) ⊆
      {z | z ∈ halfStripFrom Bf vl t₁ ∧ Nivat.LE2.dot m z = Nivat.LE2.dot m w} := by
    rintro _ ⟨j, rfl⟩
    refine ⟨?_, hlevel j⟩
    have h := hwin 0 j z₀ hz₀
    rw [hray j] at h
    rcases h with h | h
    · rcases h with h | h
      · exact h
      · simp at h
    · obtain ⟨j', _, hj'⟩ := h
      exact absurd (by rw [← hlevel j, ← hj', hrow0 j']) hwne
  exact (infinite_ray (u'_ne_zero hunimod))
    (Set.Finite.subset (halfStripFrom_level_finite hmvl) hsub)

/-- **The instance that answers the dispatch question**: Afill's `coverEnum` and the
half-strip seed cannot both be kept. -/
theorem not_hwin_coverEnum_halfStrip
    {S : Finset (ℤ × ℤ)} {a : ℤ × ℤ} {Bf : Finset (ℤ × ℤ)} {vl u' b₀ : ℤ × ℤ} {t₁ : ℤ}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    {z₀ : ℤ × ℤ} (hz₀ : z₀ ∈ S.erase a)
    (hδ : Nivat.LE2.dot (expNormal u' vl) z₀ ≠ Nivat.LE2.dot (expNormal u' vl) a) :
    ¬ (∀ i j : ℕ, ∀ z ∈ S.erase a,
        z + (coverEnum vl u' b₀ i j - a) ∈
          halfStripFrom Bf vl t₁
            ∪ (⋃ i' ∈ {i' | i' < i}, Set.range (coverEnum vl u' b₀ i'))
            ∪ (coverEnum vl u' b₀ i '' {j' | j' < j})) :=
  not_hwin_of_row_ray_halfStrip hunimod _
    (fun j => by simp only [coverEnum, Nat.cast_zero, zero_smul]; module) hz₀ hδ

/-! ## §11  The **step** case of `hwin`: what each step buys, and what it costs

§5's `window_zero_subset_D` pinned the base case `(i,j) = (0,0)`.  This section does the same
for the two steps.  The two right-hand-side increments are wildly asymmetric, and that
asymmetry *is* the shape `enum` has to have:

* `(i, j) → (i, j+1)` adds **exactly one point**, `enum i j`  (`rhs_succ_col`);
* `(i, ·) → (i+1, ·)` adds an **entire row**, `Set.range (enum i)`, all columns at once,
  including columns the sweep has not reached  (`rhs_succ_row`).

Meanwhile the demand at every single `(i,j)` is the *whole* translated window — `S.erase a`,
i.e. `S.card - 1` points.  Hence the budget statement `windowDeficit_card_le`: at column `j`
of row `i` at most `j` points of that window may still be missing from `D` and the strictly
earlier rows; at column `0` of *every* row the deficit is exactly zero
(`windowDeficit_zero`, `window_row_start_subset`).

⚠ Reading limit: these are *necessary* conditions extracted from `hwin`, not a construction.
They say what shape a would-be `enum` must have; they do not produce one.  Consistent with
`Nivat.Colle43.sweep_covers_not_derivable` (`Claim43.lean:997`). -/

/-- Column step: moving `j → j+1` enlarges the right-hand side of `hwin` by **exactly one
point**, `enum i j`. -/
theorem rhs_succ_col (D : Set (ℤ × ℤ)) (enum : ℕ → ℕ → ℤ × ℤ) (i j : ℕ) :
    D ∪ (⋃ i' ∈ {i' | i' < i}, Set.range (enum i')) ∪ (enum i '' {j' | j' < j + 1})
      = (D ∪ (⋃ i' ∈ {i' | i' < i}, Set.range (enum i')) ∪ (enum i '' {j' | j' < j}))
          ∪ {enum i j} := by
  ext w
  simp only [Set.mem_union, Set.mem_image, Set.mem_ofPred_eq, Set.mem_singleton_iff,
    Nat.lt_succ_iff_lt_or_eq]
  constructor
  · rintro (h | ⟨j', hj' | rfl, rfl⟩)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr ⟨j', hj', rfl⟩)
    · exact Or.inr rfl
  · rintro ((h | ⟨j', hj', rfl⟩) | rfl)
    · exact Or.inl h
    · exact Or.inr ⟨j', Or.inl hj', rfl⟩
    · exact Or.inr ⟨j, Or.inr rfl, rfl⟩

/-- Row step: moving `i → i+1` enlarges the "earlier rows" block by an **entire row**,
`Set.range (enum i)` — every column of it at once, including columns not yet reached. -/
theorem rhs_succ_row (enum : ℕ → ℕ → ℤ × ℤ) (i : ℕ) :
    (⋃ i' ∈ {i' | i' < i + 1}, Set.range (enum i'))
      = (⋃ i' ∈ {i' | i' < i}, Set.range (enum i')) ∪ Set.range (enum i) := by
  ext w
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Set.mem_union, exists_prop,
    Nat.lt_succ_iff_lt_or_eq]
  constructor
  · rintro ⟨i', hi' | rfl, hw⟩
    · exact Or.inl ⟨i', hi', hw⟩
    · exact Or.inr hw
  · rintro (⟨i', hi', hw⟩ | hw)
    · exact ⟨i', Or.inl hi', hw⟩
    · exact ⟨i, Or.inr rfl, hw⟩

/-- **Each row starts with zero credit.**  At column `0` of *any* row `i` — not just row `0` —
the whole translated window must already sit in `D` together with the strictly earlier rows;
its own row contributes nothing.  `window_zero_subset_D` (§5) is the case `i = 0`, where the
earlier-rows block is empty as well. -/
theorem window_row_start_subset {S : Finset (ℤ × ℤ)} {a : ℤ × ℤ} {D : Set (ℤ × ℤ)}
    {enum : ℕ → ℕ → ℤ × ℤ}
    (hwin : ∀ i j : ℕ, ∀ z ∈ S.erase a,
      z + (enum i j - a) ∈
        D ∪ (⋃ i' ∈ {i' | i' < i}, Set.range (enum i')) ∪ (enum i '' {j' | j' < j}))
    (i : ℕ) (z : ℤ × ℤ) (hz : z ∈ S.erase a) :
    z + (enum i 0 - a) ∈ D ∪ (⋃ i' ∈ {i' | i' < i}, Set.range (enum i')) := by
  have h := hwin i 0 z hz
  rcases h with h | h
  · exact h
  · simp only [Set.mem_image, Set.mem_ofPred_eq, Nat.not_lt_zero, false_and, exists_false] at h

open scoped Classical in
/-- The part of the window translate at `(i,j)` that `D` and the strictly earlier rows do
**not** already contain — the credit row `i` has to pay out of its own earlier columns. -/
noncomputable def windowDeficit (S : Finset (ℤ × ℤ)) (a : ℤ × ℤ) (D : Set (ℤ × ℤ))
    (enum : ℕ → ℕ → ℤ × ℤ) (i j : ℕ) : Finset (ℤ × ℤ) :=
  ((S.erase a).image (fun z => z + (enum i j - a))).filter
    (fun w => w ∉ D ∪ (⋃ i' ∈ {i' | i' < i}, Set.range (enum i')))

/-- The deficit at `(i,j)` has to be paid entirely out of row `i`'s first `j` columns. -/
theorem windowDeficit_subset {S : Finset (ℤ × ℤ)} {a : ℤ × ℤ} {D : Set (ℤ × ℤ)}
    {enum : ℕ → ℕ → ℤ × ℤ}
    (hwin : ∀ i j : ℕ, ∀ z ∈ S.erase a,
      z + (enum i j - a) ∈
        D ∪ (⋃ i' ∈ {i' | i' < i}, Set.range (enum i')) ∪ (enum i '' {j' | j' < j}))
    (i j : ℕ) :
    windowDeficit S a D enum i j ⊆ (Finset.range j).image (enum i) := by
  classical
  intro w hw
  simp only [windowDeficit, Finset.mem_filter, Finset.mem_image, Finset.mem_range] at hw ⊢
  obtain ⟨⟨z, hz, rfl⟩, hnot⟩ := hw
  rcases hwin i j z hz with h | h
  · exact absurd h hnot
  · simp only [Set.mem_image, Set.mem_ofPred_eq] at h
    obtain ⟨j', hj', hj'eq⟩ := h
    exact ⟨j', hj', hj'eq⟩

/-- **The step budget, as a number.**  By column `j` of row `i`, at most `j` points of the
translated window may still be missing from `D` and the earlier rows. -/
theorem windowDeficit_card_le {S : Finset (ℤ × ℤ)} {a : ℤ × ℤ} {D : Set (ℤ × ℤ)}
    {enum : ℕ → ℕ → ℤ × ℤ}
    (hwin : ∀ i j : ℕ, ∀ z ∈ S.erase a,
      z + (enum i j - a) ∈
        D ∪ (⋃ i' ∈ {i' | i' < i}, Set.range (enum i')) ∪ (enum i '' {j' | j' < j}))
    (i j : ℕ) : (windowDeficit S a D enum i j).card ≤ j :=
  le_trans (Finset.card_le_card (windowDeficit_subset hwin i j))
    (le_trans Finset.card_image_le (le_of_eq (Finset.card_range j)))

/-- Column `0` of every row: deficit exactly zero. -/
theorem windowDeficit_zero {S : Finset (ℤ × ℤ)} {a : ℤ × ℤ} {D : Set (ℤ × ℤ)}
    {enum : ℕ → ℕ → ℤ × ℤ}
    (hwin : ∀ i j : ℕ, ∀ z ∈ S.erase a,
      z + (enum i j - a) ∈
        D ∪ (⋃ i' ∈ {i' | i' < i}, Set.range (enum i')) ∪ (enum i '' {j' | j' < j}))
    (i : ℕ) : windowDeficit S a D enum i 0 = ∅ :=
  Finset.card_eq_zero.1 (Nat.le_zero.1 (windowDeficit_card_le hwin i 0))

open scoped Classical in
/-- Same statement read positively: at `(i,j)` at least `(S.card - 1) - j` of the window's
translated points are already in `D` or in a strictly earlier row. -/
theorem window_absorbed_card_ge {S : Finset (ℤ × ℤ)} {a : ℤ × ℤ} {D : Set (ℤ × ℤ)}
    {enum : ℕ → ℕ → ℤ × ℤ}
    (hwin : ∀ i j : ℕ, ∀ z ∈ S.erase a,
      z + (enum i j - a) ∈
        D ∪ (⋃ i' ∈ {i' | i' < i}, Set.range (enum i')) ∪ (enum i '' {j' | j' < j}))
    (i j : ℕ) :
    (S.erase a).card - j
      ≤ (((S.erase a).image (fun z => z + (enum i j - a))).filter
          (fun w => w ∈ D ∪ (⋃ i' ∈ {i' | i' < i}, Set.range (enum i')))).card := by
  classical
  have hinj : Function.Injective (fun z : ℤ × ℤ => z + (enum i j - a)) :=
    fun x y h => by simpa using h
  have hcard : ((S.erase a).image (fun z => z + (enum i j - a))).card = (S.erase a).card :=
    Finset.card_image_of_injective _ hinj
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (S.erase a).image (fun z => z + (enum i j - a)))
    (p := fun w => w ∈ D ∪ (⋃ i' ∈ {i' | i' < i}, Set.range (enum i')))
  have hdef : (windowDeficit S a D enum i j).card ≤ j := windowDeficit_card_le hwin i j
  simp only [windowDeficit] at hdef
  omega

/-! ## §12  `hK` is still free, if the new `enum` keeps one property of the old one

Afill's `hK_of_rows_cover_diff` (`L1CoverWedge.lean:452`) is the forward direction of §5's
`hK_iff_diff`: it turns `hK` into the premise `chainFull … k \ D ⊆ ⋃ i, range (enum i)`.  That
**relocates** the obligation onto whoever builds `enum`; it does not discharge it.  The old
`hK_of_coverEnum` really did discharge it, and §9's `iUnion_coverEnum_eq` says exactly why:
`⋃ i, range (coverEnum vl u' b₀ i)` *equals* `halfPlaneGE (expNormal u' vl) (expLevel u' vl b₀ 0)`,
and `chainFull … 0` is contained in that half-plane by construction (`cut` intersects with it).

So the property to preserve is not `coverEnum` itself — it is **half-plane surjectivity of the
row union**.  Any `enum` with it discharges `hK` at `k := 0` for *every* `D`, `hwin`-compatible
or not.  This is a `D`-independent, checkable design target to hand the `enum` builder alongside
the §11 well-ordering, and the two do not obviously conflict: §11 constrains the *order* in which
rows are laid down, §12 only the *union* of their images. -/

/-- `chainFull … 0` sits in the level-`0` half-plane because `cut` intersects with it. -/
theorem chainFull_zero_subset_halfPlane (B : Set (ℤ × ℤ)) (vl u' b₀ : ℤ × ℤ) :
    chainFull B vl u' b₀ 0
      ⊆ Nivat.LE2.halfPlaneGE (expNormal u' vl) (expLevel u' vl b₀ 0) :=
  fun _ hz => hz.2

/-- **The `D`-independent sufficient condition for `hK` at `k := 0`.**  No hypothesis on `D`,
on `B`, or on the order of the rows. -/
theorem hK_zero_of_halfPlane_subset {B : Set (ℤ × ℤ)} {vl u' b₀ : ℤ × ℤ} (D : Set (ℤ × ℤ))
    {enum : ℕ → ℕ → ℤ × ℤ}
    (hcov : Nivat.LE2.halfPlaneGE (expNormal u' vl) (expLevel u' vl b₀ 0)
              ⊆ ⋃ i, Set.range (enum i)) :
    chainFull B vl u' b₀ 0 ⊆ D ∪ (⋃ i, Set.range (enum i)) :=
  fun _ hz => Or.inr (hcov hz.2)

/-- `coverEnum` meets that condition — with equality (§9).  Kept as the statement of *what*
a replacement `enum` has to reproduce. -/
theorem coverEnum_halfPlane_subset (vl u' b₀ : ℤ × ℤ)
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) :
    Nivat.LE2.halfPlaneGE (expNormal u' vl) (expLevel u' vl b₀ 0)
      ⊆ ⋃ i, Set.range (coverEnum vl u' b₀ i) :=
  (iUnion_coverEnum_eq vl u' b₀ hunimod).ge

/-! ## §13  A row order that makes `hwin` a single strict inequality

§10 refuted `u'`-ray rows; §11 said the content of `hwin` is a well-ordering of rows.  This
section supplies one, and reduces `hwin` to *one* strict inequality.

**The order.**  Index rows by the level sets of a linear functional `dot n` for a normal `n`
chosen *generically with respect to `S`*: `dot n` injective on `S`, so `S` has a unique
`n`-argmax `a`, and every other `z ∈ S` satisfies `dot n z < dot n a` strictly.  Then for
`k` in row `i`, the window translate `z + (k - a)` has `dot n`-value strictly below `k`'s,
so it lands in a **strictly earlier row** — no case analysis, no geometry
(`hwin_of_level_rows`).  The same rows discharge `hK` with no hypothesis on `D`
(`hK_of_level_rows`), so §11's order requirement and §12's covering requirement are met by
one and the same `enum`.

**⚠ Correction to the dispatch (硬规矩 3, measured).**  The dispatched condition (ii) was
`0 < dot n vl ∧ 0 < dot n (expNormal u' vl)`.  That is *satisfiable* — `exists_generic_normal`
proves it — but it is **not** the load-bearing half.  `dot (expNormal u' vl) u' = 0`
(`dot_expNormal_u'`, unconditional), so a condition stated against `expNormal u' vl` says
**nothing** about the `u'` direction, and `wedgeFull B vl u'` is swept *along `u'`*
(`RegionSweep.sweep`, `L1RegionBuild.lean:230`).  The condition that controls that direction is
`0 < dot n u'`.  `exists_generic_normal` therefore delivers **all three** positivities; the one
to quote downstream is `0 < dot n u'`.

**What is *not* free.**  Two binders remain, and they are where the geometry went:

* `hbot` — `dot n` bounded below on the region.  `dot_generic_ge_on_chainFull_zero` reduces it
  to a condition **on `B` alone**: `∃ β, ∀ b ∈ B, β ≤ dot (expNormal vl u') b`, i.e. `B` does not
  run away in the `-u'` direction.  (`dot (expNormal vl u') u' = 1`, `… vl = 0`.)
* `hfringe` — `∀ k ∈ R, ∀ z ∈ S.erase a, z + (k - a) ∈ R ∪ D`.  **Named, not discharged**, per the
  dispatch.  It absorbs both failure modes at once: leaving `R`, and dropping below the base
  level.

⚠ Reading limit: `hwin_of_level_rows` is an implication with `hfringe` as an explicit binder.
It does not produce a `D`, and it does not claim any concrete `(S, a, D)` satisfies it. -/



theorem hwin_of_level_rows
    {S : Finset (ℤ × ℤ)} {a n : ℤ × ℤ} {L₀ : ℤ} {R D : Set (ℤ × ℤ)}
    (enum : ℕ → ℕ → ℤ × ℤ)
    (hlt : ∀ z ∈ S.erase a, Nivat.LE2.dot n z < Nivat.LE2.dot n a)
    (hmemR : ∀ i j, enum i j ∈ R)
    (hlevel : ∀ i j, Nivat.LE2.dot n (enum i j) = L₀ + (i : ℤ))
    (hsurj : ∀ (i : ℕ) (w : ℤ × ℤ), w ∈ R → Nivat.LE2.dot n w = L₀ + (i : ℤ) → ∃ j, enum i j = w)
    (hbot : ∀ w ∈ R, L₀ ≤ Nivat.LE2.dot n w)
    (hfringe : ∀ k ∈ R, ∀ z ∈ S.erase a, z + (k - a) ∈ R ∪ D) :
    ∀ i j : ℕ, ∀ z ∈ S.erase a,
      z + (enum i j - a) ∈
        D ∪ (⋃ i' ∈ {i' | i' < i}, Set.range (enum i')) ∪ (enum i '' {j' | j' < j}) := by
  intro i j z hz
  rcases hfringe (enum i j) (hmemR i j) z hz with hR | hD
  · have hdot : Nivat.LE2.dot n (z + (enum i j - a))
        = L₀ + (i : ℤ) - (Nivat.LE2.dot n a - Nivat.LE2.dot n z) := by
      rw [Nivat.LE2.dot_add, Nivat.LE2.dot_sub, hlevel i j]; ring
    have hpos : 1 ≤ Nivat.LE2.dot n a - Nivat.LE2.dot n z := by have := hlt z hz; omega
    have hle := hbot _ hR
    rw [hdot] at hle
    obtain ⟨d, hd⟩ : ∃ d : ℕ, (d : ℤ) = Nivat.LE2.dot n a - Nivat.LE2.dot n z :=
      ⟨(Nivat.LE2.dot n a - Nivat.LE2.dot n z).toNat, Int.toNat_of_nonneg (by omega)⟩
    have hdi : d ≤ i := by omega
    have hcast : ((i - d : ℕ) : ℤ) = (i : ℤ) - (d : ℤ) := Nat.cast_sub hdi
    have hlv : Nivat.LE2.dot n (z + (enum i j - a)) = L₀ + ((i - d : ℕ) : ℤ) := by
      rw [hdot, hcast, ← hd]; ring
    obtain ⟨j', hj'⟩ := hsurj (i - d) _ hR hlv
    refine Or.inl (Or.inr ?_)
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop, Set.mem_range]
    exact ⟨i - d, by omega, j', hj'⟩
  · exact Or.inl (Or.inl hD)

/-- The same rows discharge `hK` for free: no hypothesis on `D`. -/
theorem hK_of_level_rows
    {n : ℤ × ℤ} {L₀ : ℤ} {R D K : Set (ℤ × ℤ)} (enum : ℕ → ℕ → ℤ × ℤ)
    (hsurj : ∀ (i : ℕ) (w : ℤ × ℤ), w ∈ R → Nivat.LE2.dot n w = L₀ + (i : ℤ) → ∃ j, enum i j = w)
    (hbot : ∀ w ∈ R, L₀ ≤ Nivat.LE2.dot n w)
    (hKR : K ⊆ R) :
    K ⊆ D ∪ (⋃ i, Set.range (enum i)) := by
  intro w hw
  have hwR := hKR hw
  have hb := hbot w hwR
  obtain ⟨i, hi⟩ : ∃ i : ℕ, (i : ℤ) = Nivat.LE2.dot n w - L₀ :=
    ⟨(Nivat.LE2.dot n w - L₀).toNat, Int.toNat_of_nonneg (by omega)⟩
  obtain ⟨j, hj⟩ := hsurj i w hwR (by omega)
  exact Or.inr (Set.mem_iUnion.2 ⟨i, ⟨j, hj⟩⟩)



theorem sq_ge_one {a : ℤ} (ha : a ≠ 0) : 1 ≤ a * a := by
  rcases lt_trichotomy a 0 with h | h | h
  · have h' : a ≤ -1 := by omega
    nlinarith
  · exact absurd h ha
  · have h' : 1 ≤ a := by omega
    nlinarith

theorem det_swap {u' vl : ℤ × ℤ} (hunimod : det u' vl = 1 ∨ det u' vl = -1) :
    det vl u' = 1 ∨ det vl u' = -1 := by
  rcases hunimod with h | h
  · right; simp only [det] at h ⊢; linear_combination -h
  · left; simp only [det] at h ⊢; linear_combination -h

theorem basis_expansion {u' vl : ℤ × ℤ} (hunimod : det u' vl = 1 ∨ det u' vl = -1) (w : ℤ × ℤ) :
    (Nivat.LE2.dot (expNormal vl u') w) • u' + (Nivat.LE2.dot (expNormal u' vl) w) • vl = w := by
  have hsq : det u' vl * det u' vl = 1 := by rcases hunimod with h | h <;> rw [h] <;> ring
  simp only [det] at hsq
  refine Prod.ext_iff.mpr ⟨?_, ?_⟩ <;>
    simp only [expNormal, Nivat.LE2.dot, det, Prod.fst_add, Prod.snd_add,
      Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  · linear_combination w.1 * hsq
  · linear_combination w.2 * hsq

theorem eq_zero_of_dot_eq_zero {u' vl : ℤ × ℤ} (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    {w : ℤ × ℤ} (h1 : Nivat.LE2.dot (expNormal u' vl) w = 0)
    (h2 : Nivat.LE2.dot (expNormal vl u') w = 0) : w = 0 := by
  have hb := basis_expansion hunimod w
  rw [h1, h2] at hb
  simp only [zero_smul, add_zero] at hb
  exact hb.symm

open scoped Classical in
/-- `exists_generic_normal_unit` with `c` and its spread bound **exported**.  Same construction,
same witness; the only change is that `c` and `hspread` leave the proof, which is what makes the
lex conjunct provable downstream instead of being a claim about a hidden number. -/
theorem exists_generic_normal_data (S : Finset (ℤ × ℤ)) {u' vl : ℤ × ℤ}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) :
    ∃ c : ℤ, 0 < c ∧
      (∀ x ∈ S, ∀ y ∈ S,
        Nivat.LE2.dot (expNormal vl u') x - Nivat.LE2.dot (expNormal vl u') y < c) ∧
      Nivat.LE2.Prim (c • expNormal u' vl + expNormal vl u') ∧
      Set.InjOn (Nivat.LE2.dot (c • expNormal u' vl + expNormal vl u')) (↑S : Set (ℤ × ℤ)) ∧
      0 < Nivat.LE2.dot (c • expNormal u' vl + expNormal vl u') vl ∧
      Nivat.LE2.dot (c • expNormal u' vl + expNormal vl u') u' = 1 ∧
      0 < Nivat.LE2.dot (c • expNormal u' vl + expNormal vl u') (expNormal u' vl) := by
  classical
  set m : ℤ × ℤ := expNormal u' vl with hm
  set m' : ℤ × ℤ := expNormal vl u' with hm'
  have hmvl : Nivat.LE2.dot m vl = 1 := dot_expNormal_vl hunimod
  have hmu' : Nivat.LE2.dot m u' = 0 := dot_expNormal_u'
  have hm'u' : Nivat.LE2.dot m' u' = 1 := dot_expNormal_vl (det_swap hunimod)
  have hm'vl : Nivat.LE2.dot m' vl = 0 := dot_expNormal_u'
  have hsq : det u' vl * det u' vl = 1 := by rcases hunimod with h | h <;> rw [h] <;> ring
  have hu'ne : u'.1 ≠ 0 ∨ u'.2 ≠ 0 := by
    rcases eq_or_ne u'.1 0 with h1 | h1
    · rcases eq_or_ne u'.2 0 with h2 | h2
      · exfalso; rcases hunimod with h | h <;> · simp only [det, h1, h2] at h; omega
      · exact Or.inr h2
    · exact Or.inl h1
  have hmm : 1 ≤ Nivat.LE2.dot m m := by
    have hexp : Nivat.LE2.dot m m = (det u' vl * det u' vl) * (u'.2 * u'.2 + u'.1 * u'.1) := by
      simp only [hm, expNormal, Nivat.LE2.dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      ring
    rw [hexp, hsq, one_mul]
    rcases hu'ne with h | h
    · have := sq_ge_one h
      nlinarith [mul_self_nonneg u'.2]
    · have := sq_ge_one h
      nlinarith [mul_self_nonneg u'.1]
  set SB : ℕ := (S ×ˢ S).sup (fun p => (Nivat.LE2.dot m' (p.1 - p.2)).natAbs) with hSB
  set c : ℤ := 1 + ((Nivat.LE2.dot m' m).natAbs : ℤ) + (SB : ℤ) with hc
  have hSBnn : (0 : ℤ) ≤ (SB : ℤ) := Int.natCast_nonneg _
  have hmmnn : (0 : ℤ) ≤ ((Nivat.LE2.dot m' m).natAbs : ℤ) := Int.natCast_nonneg _
  have hc0 : 0 < c := by omega
  have hcnn : 0 ≤ c := le_of_lt hc0
  have hspread : ∀ x ∈ S, ∀ y ∈ S,
      Nivat.LE2.dot m' x - Nivat.LE2.dot m' y < c := by
    intro x hx y hy
    have hmem : ((x, y) : (ℤ × ℤ) × (ℤ × ℤ)) ∈ S ×ˢ S := Finset.mem_product.mpr ⟨hx, hy⟩
    have hle : (Nivat.LE2.dot m' (x - y)).natAbs ≤ SB := by
      rw [hSB]
      exact Finset.le_sup (f := fun p : (ℤ × ℤ) × (ℤ × ℤ) =>
        (Nivat.LE2.dot m' (p.1 - p.2)).natAbs) hmem
    have hxy : Nivat.LE2.dot m' (x - y) = Nivat.LE2.dot m' x - Nivat.LE2.dot m' y :=
      Nivat.LE2.dot_sub _ _ _
    have hle' : Nivat.LE2.dot m' (x - y) ≤ (SB : ℤ) := by omega
    omega
  have hdotn : ∀ w : ℤ × ℤ,
      Nivat.LE2.dot (c • m + m') w = c * Nivat.LE2.dot m w + Nivat.LE2.dot m' w := by
    intro w
    simp only [Nivat.LE2.dot, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul]
    ring
  have hdu : Nivat.LE2.dot (c • m + m') u' = 1 := by rw [hdotn, hmu', hm'u']; ring
  refine ⟨c, hc0, hspread, ?_, ?_, ?_, ?_, ?_⟩
  · have hdvd : ((Int.gcd (c • m + m').1 (c • m + m').2 : ℤ)) ∣ 1 := by
      rw [← hdu]
      simp only [Nivat.LE2.dot]
      exact dvd_add ((Int.gcd_dvd_left _ _).mul_right _) ((Int.gcd_dvd_right _ _).mul_right _)
    have h1 := Int.eq_one_of_dvd_one (Int.natCast_nonneg _) hdvd
    exact_mod_cast h1
  · intro z hz z' hz' heq
    have hzS : z ∈ S := Finset.mem_coe.mp hz
    have hz'S : z' ∈ S := Finset.mem_coe.mp hz'
    rw [hdotn, hdotn] at heq
    have h1 := hspread z hzS z' hz'S
    have h2 := hspread z' hz'S z hzS
    have hk0 : Nivat.LE2.dot m z - Nivat.LE2.dot m z' = 0 := by
      by_contra hcon
      rcases lt_or_gt_of_ne hcon with hlt | hgt
      · have hle : Nivat.LE2.dot m z - Nivat.LE2.dot m z' ≤ -1 := by omega
        nlinarith [mul_le_mul_of_nonneg_left hle hcnn]
      · have hge : (1 : ℤ) ≤ Nivat.LE2.dot m z - Nivat.LE2.dot m z' := by omega
        nlinarith [mul_le_mul_of_nonneg_left hge hcnn]
    have hmeq : Nivat.LE2.dot m (z - z') = 0 := by
      rw [Nivat.LE2.dot_sub]; omega
    have hm'eq : Nivat.LE2.dot m' (z - z') = 0 := by
      rw [Nivat.LE2.dot_sub]
      have : c * Nivat.LE2.dot m z = c * Nivat.LE2.dot m z' := by
        have : Nivat.LE2.dot m z = Nivat.LE2.dot m z' := by omega
        rw [this]
      omega
    exact sub_eq_zero.mp (eq_zero_of_dot_eq_zero hunimod hmeq hm'eq)
  · rw [hdotn, hmvl, hm'vl]; omega
  · rw [hdotn, hmu', hm'u']; ring
  · rw [hdotn]
    have h4 : -((Nivat.LE2.dot m' m).natAbs : ℤ) ≤ Nivat.LE2.dot m' m := by omega
    have h3 : c ≤ c * Nivat.LE2.dot m m := by nlinarith
    linarith

/-- The `= 1` form of the row-order normal.  Signature unchanged since it landed
(`PROTOCOL.md` §14 — `HbaseSeed.lean` obtains from it); the 70-line construction moved up into
`exists_generic_normal_data`, which exports `c` and the spread as well, and this is now its
projection. -/
theorem exists_generic_normal_unit (S : Finset (ℤ × ℤ)) {u' vl : ℤ × ℤ}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) :
    ∃ n : ℤ × ℤ, Nivat.LE2.Prim n ∧ Set.InjOn (Nivat.LE2.dot n) (↑S : Set (ℤ × ℤ)) ∧
      0 < Nivat.LE2.dot n vl ∧ Nivat.LE2.dot n u' = 1 ∧
      0 < Nivat.LE2.dot n (expNormal u' vl) := by
  obtain ⟨c, _hc0, _hspread, hprim, hinj, hvl, hu', hexp⟩ := exists_generic_normal_data S hunimod
  exact ⟨c • expNormal u' vl + expNormal vl u', hprim, hinj, hvl, hu', hexp⟩

/-- The original, weaker form: `0 < dot n u'` rather than `= 1`.  Kept verbatim so existing
consumers' `obtain` patterns do not move (`PROTOCOL.md` §14); it is now a one-line corollary of
`exists_generic_normal_unit`.

⚠ **Use the `_unit` form downstream.**  `0 < dot n u'` is *not* enough for the level induction:
with `dot n u' = 2` the shift `w ↦ w + u'` would jump two levels at a time and
`∀ i, level i ≠ ∅` would be false on the odd levels.  The `= 1` is what makes the levels
gap-free, and it was always true of the witness — it is proved en route to `Prim n` — it just was
not exposed. -/
theorem exists_generic_normal (S : Finset (ℤ × ℤ)) {u' vl : ℤ × ℤ}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) :
    ∃ n : ℤ × ℤ, Nivat.LE2.Prim n ∧ Set.InjOn (Nivat.LE2.dot n) (↑S : Set (ℤ × ℤ)) ∧
      0 < Nivat.LE2.dot n vl ∧ 0 < Nivat.LE2.dot n u' ∧
      0 < Nivat.LE2.dot n (expNormal u' vl) := by
  obtain ⟨n, hprim, hinj, hvl, hu', hexp⟩ := exists_generic_normal_unit S hunimod
  exact ⟨n, hprim, hinj, hvl, by omega, hexp⟩




theorem dot_generic_ge_on_chainFull_zero
    {B : Set (ℤ × ℤ)} {u' vl b₀ : ℤ × ℤ} (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    {c β : ℤ} (hc0 : 0 ≤ c)
    (hB : ∀ b ∈ B, β ≤ Nivat.LE2.dot (expNormal vl u') b)
    {w : ℤ × ℤ} (hw : w ∈ chainFull B vl u' b₀ 0) :
    c * Nivat.LE2.dot (expNormal u' vl) b₀ + β
      ≤ Nivat.LE2.dot (c • expNormal u' vl + expNormal vl u') w := by
  have hm'u' : Nivat.LE2.dot (expNormal vl u') u' = 1 := dot_expNormal_vl (det_swap hunimod)
  have hm'vl : Nivat.LE2.dot (expNormal vl u') vl = 0 := dot_expNormal_u'
  have hdotn : ∀ y : ℤ × ℤ, Nivat.LE2.dot (c • expNormal u' vl + expNormal vl u') y
      = c * Nivat.LE2.dot (expNormal u' vl) y + Nivat.LE2.dot (expNormal vl u') y := by
    intro y
    simp only [Nivat.LE2.dot, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul]
    ring
  obtain ⟨hw1, hw2⟩ := hw
  have hlev : Nivat.LE2.dot (expNormal u' vl) b₀ ≤ Nivat.LE2.dot (expNormal u' vl) w := by
    simpa [expLevel, Nivat.LE2.halfPlaneGE] using hw2
  obtain ⟨g, hg, t, rfl⟩ := hw1
  rw [mem_fullSweep_iff] at hg
  obtain ⟨b, hb, s, rfl⟩ := hg
  have hm' : Nivat.LE2.dot (expNormal vl u') (b + s • vl + (t : ℤ) • u')
      = Nivat.LE2.dot (expNormal vl u') b + (t : ℤ) := by
    rw [Nivat.LE2.dot_add, Nivat.LE2.dot_add, dot_smul_right, dot_smul_right, hm'vl, hm'u']
    ring
  have hbb := hB b hb
  rw [hdotn, hm']
  have hmul : c * Nivat.LE2.dot (expNormal u' vl) b₀
      ≤ c * Nivat.LE2.dot (expNormal u' vl) (b + s • vl + (t : ℤ) • u') :=
    mul_le_mul_of_nonneg_left hlev hc0
  have ht : (0 : ℤ) ≤ (t : ℤ) := Int.natCast_nonneg t
  linarith

/-! ## §14  `enum` **produced**, not assumed — and with it `hwin` and `hK` together

§13 left `enum` as a binder carrying three hypotheses (`hmemR`, `hlevel`, `hsurj`) that **no
declaration anywhere in the tree produced**.  That is the same failure mode as
`hK_of_rows_cover_diff` (`L1CoverWedge.lean:452`): an obligation *relocated* onto the enumeration's
builder rather than discharged.  This section discharges it.

The construction needs nothing geometric.  Each level
`A i := {w ∈ R | dot n w = L₀ + i}` is a subset of `ℤ × ℤ`, hence countable for free
(`Set.to_countable`, no hypothesis), so as soon as it is **nonempty** there is a surjection
`ℕ → A i` (`Set.Countable.exists_eq_range`, `Mathlib/Data/Set/Countable.lean:151`, delivering
`A i = Set.range (f i)` — one object giving both `hmemR` and `hsurj`).  `choose` assembles the
family.  So level-nonemptiness is the *whole* content of `enum`'s existence; no enumeration order,
no explicit formula, no decidability.

`exists_enum_hwin_hK` is then the capstone: its hypotheses never mention `enum`, and it returns
one `enum` satisfying `hwin` **and** `hK` simultaneously — team-lead's 2026-09-19 ruling #2
("`enum` 只有一个") discharged constructively rather than argued.

⚠ Division of labour (2026-09-19, to avoid duplicating L3win): `hlevne` and `hbot` are **not**
proved here.  Both follow from the single `B`-side condition
`∃ β, ∀ b ∈ B, β ≤ dot (expNormal vl u') b` via `dot_generic_ge_on_chainFull_zero` plus
`Int.exists_least_of_bdd` (minimise over the *level predicate* `P L := ∃ w ∈ R, dot n w = L`, not
over points — `R = chainFull B vl u' b₀ 0` is infinite, so no `Finset` argmin applies); L3win is
landing that chain in `HbaseSeed.lean`.  This file consumes their output, it does not re-derive it.
-/

open scoped Classical in
/-- **`enum` exists.**  Level-nonemptiness is the only input: countability of each level is free
in `ℤ × ℤ`.  Returns the three properties §13's `hwin_of_level_rows`/`hK_of_level_rows` take as
binders. -/
theorem exists_enum_of_levels {n : ℤ × ℤ} {L₀ : ℤ} {R : Set (ℤ × ℤ)}
    (hlevne : ∀ i : ℕ, ∃ w ∈ R, Nivat.LE2.dot n w = L₀ + (i : ℤ)) :
    ∃ enum : ℕ → ℕ → ℤ × ℤ,
      (∀ i j, enum i j ∈ R) ∧
      (∀ i j, Nivat.LE2.dot n (enum i j) = L₀ + (i : ℤ)) ∧
      (∀ (i : ℕ) (w : ℤ × ℤ), w ∈ R → Nivat.LE2.dot n w = L₀ + (i : ℤ) →
        ∃ j, enum i j = w) := by
  classical
  have hchoice : ∀ i : ℕ, ∃ f : ℕ → ℤ × ℤ,
      {w : ℤ × ℤ | w ∈ R ∧ Nivat.LE2.dot n w = L₀ + (i : ℤ)} = Set.range f := by
    intro i
    refine Set.Countable.exists_eq_range (Set.to_countable _) ?_
    obtain ⟨w, hwR, hwl⟩ := hlevne i
    exact ⟨w, hwR, hwl⟩
  choose f hf using hchoice
  refine ⟨f, ?_, ?_, ?_⟩
  · intro i j
    exact ((hf i).ge (Set.mem_range_self j)).1
  · intro i j
    exact ((hf i).ge (Set.mem_range_self j)).2
  · intro i w hwR hwl
    exact (hf i).le ⟨hwR, hwl⟩

/-- **The capstone.**  No hypothesis mentions `enum`; one `enum` comes out satisfying both `hwin`
and `hK`.  The remaining inputs are exactly four: the window's strictness at `a` (`hlt`), the
level structure of `R` (`hlevne`, `hbot` — both from L3win's `B`-side β condition), the fringe
condition (`hfringe`, Afill's), and `K ⊆ R`. -/
theorem exists_enum_hwin_hK {S : Finset (ℤ × ℤ)} {a n : ℤ × ℤ} {L₀ : ℤ}
    {R D K : Set (ℤ × ℤ)}
    (hlt : ∀ z ∈ S.erase a, Nivat.LE2.dot n z < Nivat.LE2.dot n a)
    (hlevne : ∀ i : ℕ, ∃ w ∈ R, Nivat.LE2.dot n w = L₀ + (i : ℤ))
    (hbot : ∀ w ∈ R, L₀ ≤ Nivat.LE2.dot n w)
    (hfringe : ∀ k ∈ R, ∀ z ∈ S.erase a, z + (k - a) ∈ R ∪ D)
    (hKR : K ⊆ R) :
    ∃ enum : ℕ → ℕ → ℤ × ℤ,
      (∀ i j : ℕ, ∀ z ∈ S.erase a,
        z + (enum i j - a) ∈
          D ∪ (⋃ i' ∈ {i' | i' < i}, Set.range (enum i')) ∪ (enum i '' {j' | j' < j}))
      ∧ K ⊆ D ∪ (⋃ i, Set.range (enum i)) := by
  obtain ⟨enum, hmemR, hlevel, hsurj⟩ := exists_enum_of_levels hlevne
  refine ⟨enum, ?_, ?_⟩
  · exact hwin_of_level_rows enum hlt hmemR hlevel hsurj hbot hfringe
  · exact hK_of_level_rows enum hsurj hbot hKR

/-! ## §15  `hlt` is free too: the same `n` that orders the rows also *chooses* `a`

§14 still took `hlt : ∀ z ∈ S.erase a, dot n z < dot n a` as a binder, with `a` arriving from
somewhere else (`VertexFromEdge.exists_isVtx_of_finite`, say) and `n` from
`exists_generic_normal` — two independent choices that then have to be compatible.  They need not
be: **take `a` to be the `dot n`-argmax of `S`.**  Since `exists_generic_normal` already delivers
`Set.InjOn (dot n) ↑S`, the argmax is strict on `S.erase a`, which is `hlt`; and strictness of the
maximum is precisely `face (↑S) n = {a}`, i.e. `IsVtx (↑S) a` — the same object
`VertexFromEdge.exists_isVtx_of_finite` (`VertexFromEdge.lean:242`) produces with its own generic
normal `(1, N)`.

So one `n` does both jobs at once, and the vertex it exposes is the one the row order wants.  Note
the direction of the dependency is the legal one per `VertexFromEdge.lean:37-43`: `a` is produced
*before* and independently of `D`/`enum`, and is delivered existentially.

⚠ This does **not** subsume `VertexFromEdge.exists_isVtx_of_finite` — that one needs no
`hunimod` and no `u'`/`vl` at all, so it stays the right tool when there is no wedge in sight
(`PROTOCOL.md` §14: not retracted, different hypotheses).  What is new here is only the
*compatibility*: the vertex and the row order come from a single normal.

**2026-09-19 18:0x addition — the lex conjunct.**  `exists_vertex_and_row_order_lex` is the
primary form; `exists_vertex_and_row_order` is its projection, signature unchanged.  The extra
conjunct says the same `a` is lex-extreme at the **max** end for
`(expNormal u' vl, expNormal vl u')` — see §17 for what that buys (`hgen` at this very `a`), for
the orientation measurement against `L3Band`, and for `not_lex_max_and_min`, which shows the max
and min ends are different points whenever `2 ≤ S.card`.
-/

theorem dot_weighted (m m' : ℤ × ℤ) (c : ℤ) (w : ℤ × ℤ) :
    Nivat.LE2.dot (c • m + m') w = c * Nivat.LE2.dot m w + Nivat.LE2.dot m' w := by
  simp only [Nivat.LE2.dot, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul]
  ring

/-- **The lex step at the max end.**  A strict drop in the weighted functional, with `c` past the
`m'`-spread of `S`, is exactly lex-smallness for `(m, m')`. -/
theorem lex_max_of_dot_lt {S : Finset (ℤ × ℤ)} {m m' a z : ℤ × ℤ} {c : ℤ}
    (hspread : ∀ x ∈ S, ∀ y ∈ S, Nivat.LE2.dot m' x - Nivat.LE2.dot m' y < c)
    (haS : a ∈ S) (hzS : z ∈ S)
    (hlt : Nivat.LE2.dot (c • m + m') z < Nivat.LE2.dot (c • m + m') a) :
    Nivat.LE2.dot m z < Nivat.LE2.dot m a ∨
      (Nivat.LE2.dot m z = Nivat.LE2.dot m a ∧ Nivat.LE2.dot m' z < Nivat.LE2.dot m' a) := by
  rw [dot_weighted, dot_weighted] at hlt
  have hc0 : 0 < c := by have := hspread a haS a haS; omega
  have hza := hspread z hzS a haS
  have haz := hspread a haS z hzS
  rcases lt_trichotomy (Nivat.LE2.dot m z) (Nivat.LE2.dot m a) with h | h | h
  · exact Or.inl h
  · exact Or.inr ⟨h, by rw [h] at hlt; omega⟩
  · exfalso
    have hge : (1 : ℤ) ≤ Nivat.LE2.dot m z - Nivat.LE2.dot m a := by omega
    nlinarith [mul_le_mul_of_nonneg_left hge hc0.le]

/-- The same at the min end, by swapping the two points. -/
theorem lex_min_of_dot_lt {S : Finset (ℤ × ℤ)} {m m' a z : ℤ × ℤ} {c : ℤ}
    (hspread : ∀ x ∈ S, ∀ y ∈ S, Nivat.LE2.dot m' x - Nivat.LE2.dot m' y < c)
    (haS : a ∈ S) (hzS : z ∈ S)
    (hlt : Nivat.LE2.dot (c • m + m') a < Nivat.LE2.dot (c • m + m') z) :
    Nivat.LE2.dot m a < Nivat.LE2.dot m z ∨
      (Nivat.LE2.dot m a = Nivat.LE2.dot m z ∧ Nivat.LE2.dot m' a < Nivat.LE2.dot m' z) :=
  lex_max_of_dot_lt hspread hzS haS hlt

open scoped Classical in
/-- **`§15` with the lex conjunct exposed.**  Same `n`, same `a`, same four old conjuncts; the new
fifth conjunct is lex-extremality of `a` at the **max** end for
`(expNormal u' vl, expNormal vl u' = expDual u' vl)`, which is
`Colle37Geom.latticeConvex_erase_of_lexExtreme`'s `hlex` verbatim. -/
theorem exists_vertex_and_row_order_lex {S : Finset (ℤ × ℤ)} (hne : S.Nonempty)
    {u' vl : ℤ × ℤ} (hunimod : Nivat.det u' vl = 1 ∨ Nivat.det u' vl = -1) :
    ∃ (n a : ℤ × ℤ), Nivat.LE2.Prim n ∧ Nivat.LE2.IsVtx (↑S : Set (ℤ × ℤ)) a ∧ a ∈ S ∧
      (∀ z ∈ S.erase a, Nivat.LE2.dot n z < Nivat.LE2.dot n a) ∧
      (∀ z ∈ S.erase a,
        Nivat.LE2.dot (expNormal u' vl) z < Nivat.LE2.dot (expNormal u' vl) a ∨
          (Nivat.LE2.dot (expNormal u' vl) z = Nivat.LE2.dot (expNormal u' vl) a ∧
            Nivat.LE2.dot (expNormal vl u') z < Nivat.LE2.dot (expNormal vl u') a)) ∧
      0 < Nivat.LE2.dot n vl ∧ Nivat.LE2.dot n u' = 1 ∧
      0 < Nivat.LE2.dot n (expNormal u' vl) := by
  classical
  obtain ⟨c, hc0, hspread, hprim, hinj, hvl, hu', hexp⟩ := exists_generic_normal_data S hunimod
  set n : ℤ × ℤ := c • expNormal u' vl + expNormal vl u' with hn
  obtain ⟨a, haS, hamax⟩ := S.exists_mem_eq_sup' hne (fun z => Nivat.LE2.dot n z)
  have hamax' : ∀ z ∈ S, Nivat.LE2.dot n z ≤ Nivat.LE2.dot n a := by
    intro z hz
    have hle := Finset.le_sup' (fun z => Nivat.LE2.dot n z) hz
    rw [hamax] at hle
    exact hle
  have hlt : ∀ z ∈ S.erase a, Nivat.LE2.dot n z < Nivat.LE2.dot n a := by
    intro z hz
    have hzS : z ∈ S := Finset.mem_of_mem_erase hz
    have hzne : z ≠ a := Finset.ne_of_mem_erase hz
    refine lt_of_le_of_ne (hamax' z hzS) ?_
    intro heq
    exact hzne (hinj (Finset.mem_coe.mpr hzS) (Finset.mem_coe.mpr haS) heq)
  have hface : Nivat.LE2.face (↑S : Set (ℤ × ℤ)) n = {a} := by
    ext z
    simp only [Nivat.LE2.mem_face_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hzS, hzmax⟩
      have heq : Nivat.LE2.dot n z = Nivat.LE2.dot n a :=
        le_antisymm (hamax' z (Finset.mem_coe.mp hzS)) (hzmax a (Finset.mem_coe.mpr haS))
      exact hinj hzS (Finset.mem_coe.mpr haS) heq
    · rintro rfl
      exact ⟨Finset.mem_coe.mpr haS, fun y hy => hamax' y (Finset.mem_coe.mp hy)⟩
  refine ⟨n, a, hprim, ⟨n, hprim, hface⟩, haS, hlt, ?_, hvl, hu', hexp⟩
  intro z hz
  exact lex_max_of_dot_lt hspread haS (Finset.mem_of_mem_erase hz) (hlt z hz)

/-- **One normal, both jobs.**  `n` orders the rows (three positivities, as in
`exists_generic_normal`) *and* exposes the vertex `a` at which `hlt` holds — no separate vertex
choice, no compatibility obligation between the two.  Signature unchanged since it landed
(`PROTOCOL.md` §14); it is now the lex-free projection of `exists_vertex_and_row_order_lex`. -/
theorem exists_vertex_and_row_order {S : Finset (ℤ × ℤ)} (hne : S.Nonempty)
    {u' vl : ℤ × ℤ} (hunimod : Nivat.det u' vl = 1 ∨ Nivat.det u' vl = -1) :
    ∃ (n a : ℤ × ℤ), Nivat.LE2.Prim n ∧ Nivat.LE2.IsVtx (↑S : Set (ℤ × ℤ)) a ∧ a ∈ S ∧
      (∀ z ∈ S.erase a, Nivat.LE2.dot n z < Nivat.LE2.dot n a) ∧
      0 < Nivat.LE2.dot n vl ∧ Nivat.LE2.dot n u' = 1 ∧
      0 < Nivat.LE2.dot n (expNormal u' vl) := by
  obtain ⟨n, a, hprim, hvtx, haS, hlt, _hlex, hvl, hu', hexp⟩ :=
    exists_vertex_and_row_order_lex hne hunimod
  exact ⟨n, a, hprim, hvtx, haS, hlt, hvl, hu', hexp⟩

/-! ## §16  `hfringe`, reduced to `B`/`S` data with `D` and `R` eliminated

Dispatch of 2026-09-19: do to `hfringe` what §13 did to `hbot`.  The binder
`hfringe : ∀ k ∈ R, ∀ z ∈ S.erase a, z + (k - a) ∈ R ∪ D` mentions `R`, `S`, `a`, `D` at once,
so nobody could check it against their own side.  It splits cleanly, because leaving
`R = chainFull B vl u' b₀ 0` can happen in exactly two independent ways, and the two are
**transverse** to each other.

Write `m := expNormal u' vl`, `m' := expNormal vl u'` — the dual basis of `(u', vl)`
(`basis_expansion`), with `dot m vl = 1`, `dot m u' = 0`, `dot m' u' = 1`, `dot m' vl = 0`.
Every `k ∈ R` is `b + s • vl + t • u'` with `b ∈ B`, `s : ℤ`, `t : ℕ` (`rep_of_mem_chainFull_zero`),
and for `v := z - a` the basis expansion gives `k + v = b + (s + dot m v) • vl + (t + dot m' v) • u'`.
So the window shift moves `s` by `dot m v` and `t` by `dot m' v`, and:

* **the cut failure** — `dot m (k + v)` dropping below `dot m b₀`.  Controlled by
  `cutWidth S a u' vl := (S.erase a).sup (fun z => (dot m (z - a)).natAbs)`.
* **the sweep-edge failure** — `t + dot m' v` going negative, i.e. falling off the `ℕ`-indexed
  `u'`-sweep.  Controlled by `edgeWidth S a u' vl` (same `sup`, against `m'`).

`deep_stays` is the content: past both widths, **no escape is possible at all**, with no
hypothesis on `D`.  `hfringe_of_cover_bands` is the reduction the dispatch asked for — its `hD`
quantifies over `b ∈ B`, `s : ℤ`, `t : ℕ` and the two width conditions, so `R` never appears and
each side can check it locally.

### The dispatch's payoff question, answered: **no**

The hope was that the cut failure is confined to finitely many levels, so `D` need only cover a
bounded band, reachable from `hcase1`'s `halfStrip` conjunct.  It is not, and
`not_ray_subset_halfStrip` proves it rather than asserting it:

* the cut band is bounded transversally (width `cutWidth` in `dot m`) but **`u'`-ray-closed** —
  `dot m u' = 0`, so `k + i • u'` stays in it for every `i` (`cutBand_ray_u'`);
* `Case1` (`CaseSplit.lean:82`) supplies agreement on `halfStrip B vl` (`LatticeEdges.lean:1810`),
  and `dot m' vl = 0` means `dot m'` is **constant along that strip**, taking only the finitely
  many values it takes on the base.

So `dot m'` is unbounded on the cut band and bounded on any `vl`-half-strip over a finite base:
the two are transverse and no `Case1`-shaped `D` covers the cut band.  The bands are transverse to
*each other* too — the cut band runs along `u'`, the edge band along `vl`.

### The escape half: the weakest `B`-side condition, and nothing supplies it

`UPushable B vl u' N` — every `b ∈ B` is already `N` steps along `u'` inside `B`'s own `vl`-sweep —
is exactly what makes every point of the wedge admit a representation with `t ≥ N`, killing the
edge band (`rep_deep_of_uPushable`, `hfringe_of_uPushable`: with it, only the cut band is left).

⚠ **Nothing on the chain supplies it, and this is structural, not a gap in the search.**
`Case1 ξ xper S vl` (`CaseSplit.lean:82-84`) is `∃ B, EnvOf ↑S B ∧ ∃ u, ∀ z ∈ halfStrip B vl, …` —
**`u'` does not occur in it**, verified by reading the definition, not relayed.  `hunimod` is a
relation between `u'` and `vl`, not between `B` and `u'`.  So no on-chain hypothesis constrains `B`
in the `u'` direction, and `UPushable` cannot be derived from what `Case1` hands out; it would have
to be arranged when `B` is *chosen*.  Per the dispatch, a clean statement of the hole is the
deliverable here.

⚠ Reading limit (`PROTOCOL.md` §15): every theorem below is an implication with its band
conditions as explicit binders.  None of them produces a `D`, and `not_ray_subset_halfStrip`
refutes *containment of the `u'`-ray in a finite-base `vl`-half-strip* — it does not claim
`hfringe` is unsatisfiable. -/

/-- Width of the window against the cut normal `expNormal u' vl`. -/
noncomputable def cutWidth (S : Finset (ℤ × ℤ)) (a u' vl : ℤ × ℤ) : ℕ :=
  (S.erase a).sup (fun z => (Nivat.LE2.dot (expNormal u' vl) (z - a)).natAbs)

/-- Width of the window against the sweep normal `expNormal vl u'`. -/
noncomputable def edgeWidth (S : Finset (ℤ × ℤ)) (a u' vl : ℤ × ℤ) : ℕ :=
  (S.erase a).sup (fun z => (Nivat.LE2.dot (expNormal vl u') (z - a)).natAbs)

theorem neg_cutWidth_le {S : Finset (ℤ × ℤ)} {a u' vl z : ℤ × ℤ} (hz : z ∈ S.erase a) :
    -((cutWidth S a u' vl : ℤ)) ≤ Nivat.LE2.dot (expNormal u' vl) (z - a) := by
  have h1 : (Nivat.LE2.dot (expNormal u' vl) (z - a)).natAbs ≤ cutWidth S a u' vl :=
    Finset.le_sup (f := fun z => (Nivat.LE2.dot (expNormal u' vl) (z - a)).natAbs) hz
  omega

theorem neg_edgeWidth_le {S : Finset (ℤ × ℤ)} {a u' vl z : ℤ × ℤ} (hz : z ∈ S.erase a) :
    -((edgeWidth S a u' vl : ℤ)) ≤ Nivat.LE2.dot (expNormal vl u') (z - a) := by
  have h1 : (Nivat.LE2.dot (expNormal vl u') (z - a)).natAbs ≤ edgeWidth S a u' vl :=
    Finset.le_sup (f := fun z => (Nivat.LE2.dot (expNormal vl u') (z - a)).natAbs) hz
  omega

theorem mem_chainFull_zero_of_rep {B : Set (ℤ × ℤ)} {vl u' b₀ b : ℤ × ℤ} (hb : b ∈ B)
    (s : ℤ) (t : ℕ)
    (hcut : Nivat.LE2.dot (expNormal u' vl) b₀
      ≤ Nivat.LE2.dot (expNormal u' vl) (b + s • vl + (t : ℤ) • u')) :
    b + s • vl + (t : ℤ) • u' ∈ chainFull B vl u' b₀ 0 := by
  refine ⟨⟨b + s • vl, ?_, t, rfl⟩, ?_⟩
  · exact mem_fullSweep_iff.mpr ⟨b, hb, s, rfl⟩
  · simpa [expLevel, Nivat.LE2.halfPlaneGE] using hcut

theorem rep_of_mem_chainFull_zero {B : Set (ℤ × ℤ)} {vl u' b₀ w : ℤ × ℤ}
    (hw : w ∈ chainFull B vl u' b₀ 0) :
    ∃ b ∈ B, ∃ s : ℤ, ∃ t : ℕ, w = b + s • vl + (t : ℤ) • u' := by
  obtain ⟨⟨g, hg, t, rfl⟩, -⟩ := hw
  obtain ⟨b, hb, s, rfl⟩ := mem_fullSweep_iff.mp hg
  exact ⟨b, hb, s, t, rfl⟩

/-- **The core: deep points do not escape.** -/
theorem deep_stays {S : Finset (ℤ × ℤ)} {a : ℤ × ℤ} {B : Set (ℤ × ℤ)} {vl u' b₀ b : ℤ × ℤ}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hb : b ∈ B) {s : ℤ} {t : ℕ}
    (hcut : Nivat.LE2.dot (expNormal u' vl) b₀ + (cutWidth S a u' vl : ℤ)
      ≤ Nivat.LE2.dot (expNormal u' vl) (b + s • vl + (t : ℤ) • u'))
    (hedge : (edgeWidth S a u' vl : ℤ) ≤ (t : ℤ)) :
    ∀ z ∈ S.erase a,
      z + ((b + s • vl + (t : ℤ) • u') - a) ∈ chainFull B vl u' b₀ 0 := by
  intro z hz
  have hbasis : (Nivat.LE2.dot (expNormal vl u') (z - a)) • u'
      + (Nivat.LE2.dot (expNormal u' vl) (z - a)) • vl = z - a := basis_expansion hunimod (z - a)
  obtain ⟨α, hαd⟩ : ∃ α : ℤ, Nivat.LE2.dot (expNormal vl u') (z - a) = α := ⟨_, rfl⟩
  obtain ⟨β, hβd⟩ : ∃ β : ℤ, Nivat.LE2.dot (expNormal u' vl) (z - a) = β := ⟨_, rfl⟩
  rw [hαd, hβd] at hbasis
  have hα : -((edgeWidth S a u' vl : ℤ)) ≤ α := by rw [← hαd]; exact neg_edgeWidth_le hz
  have hβ : -((cutWidth S a u' vl : ℤ)) ≤ β := by rw [← hβd]; exact neg_cutWidth_le hz
  have ht' : 0 ≤ (t : ℤ) + α := by omega
  obtain ⟨t', ht'eq⟩ : ∃ t' : ℕ, (t' : ℤ) = (t : ℤ) + α :=
    ⟨((t : ℤ) + α).toNat, Int.toNat_of_nonneg ht'⟩
  have hrep : z + ((b + s • vl + (t : ℤ) • u') - a) = b + (s + β) • vl + (t' : ℤ) • u' := by
    have h1 : z + ((b + s • vl + (t : ℤ) • u') - a) = (b + s • vl + (t : ℤ) • u') + (z - a) := by
      abel
    rw [h1, ← hbasis, ht'eq]
    module
  rw [hrep]
  refine mem_chainFull_zero_of_rep hb _ _ ?_
  have hmvl : Nivat.LE2.dot (expNormal u' vl) vl = 1 := dot_expNormal_vl hunimod
  have hmu' : Nivat.LE2.dot (expNormal u' vl) u' = 0 := dot_expNormal_u'
  have hL : Nivat.LE2.dot (expNormal u' vl) (b + (s + β) • vl + (t' : ℤ) • u')
      = Nivat.LE2.dot (expNormal u' vl) (b + s • vl + (t : ℤ) • u') + β := by
    simp only [Nivat.LE2.dot_add, dot_smul_right, hmvl, hmu']
    ring
  rw [hL]
  omega

/-- The reduction: `D` only ever has to meet the two explicit bands. -/
theorem hfringe_of_cover_bands {S : Finset (ℤ × ℤ)} {a : ℤ × ℤ} {B D : Set (ℤ × ℤ)}
    {vl u' b₀ : ℤ × ℤ} (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hD : ∀ b ∈ B, ∀ (s : ℤ) (t : ℕ),
      (Nivat.LE2.dot (expNormal u' vl) (b + s • vl + (t : ℤ) • u')
          < Nivat.LE2.dot (expNormal u' vl) b₀ + (cutWidth S a u' vl : ℤ)
        ∨ (t : ℤ) < (edgeWidth S a u' vl : ℤ)) →
      ∀ z ∈ S.erase a, z + ((b + s • vl + (t : ℤ) • u') - a) ∈ D) :
    ∀ k ∈ chainFull B vl u' b₀ 0, ∀ z ∈ S.erase a,
      z + (k - a) ∈ chainFull B vl u' b₀ 0 ∪ D := by
  intro k hk z hz
  obtain ⟨b, hb, s, t, rfl⟩ := rep_of_mem_chainFull_zero hk
  by_cases hdeep : Nivat.LE2.dot (expNormal u' vl) b₀ + (cutWidth S a u' vl : ℤ)
      ≤ Nivat.LE2.dot (expNormal u' vl) (b + s • vl + (t : ℤ) • u')
        ∧ (edgeWidth S a u' vl : ℤ) ≤ (t : ℤ)
  · exact Or.inl (deep_stays hunimod hb hdeep.1 hdeep.2 z hz)
  · refine Or.inr (hD b hb s t ?_ z hz)
    rcases not_and_or.mp hdeep with h | h
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)

/-- The `B`-side condition that kills the sweep-edge band: `B` is already `N` steps along `u'`
inside its own `vl`-sweep. -/
def UPushable (B : Set (ℤ × ℤ)) (vl u' : ℤ × ℤ) (N : ℕ) : Prop :=
  ∀ b ∈ B, ∃ b' ∈ B, ∃ s : ℤ, b = b' + s • vl + (N : ℤ) • u'

theorem rep_deep_of_uPushable {B : Set (ℤ × ℤ)} {vl u' : ℤ × ℤ} {N : ℕ}
    (h : UPushable B vl u' N) {b : ℤ × ℤ} (hb : b ∈ B) (s : ℤ) (t : ℕ) :
    ∃ b'' ∈ B, ∃ s'' : ℤ, ∃ t'' : ℕ, (N : ℤ) ≤ (t'' : ℤ) ∧
      b + s • vl + (t : ℤ) • u' = b'' + s'' • vl + (t'' : ℤ) • u' := by
  obtain ⟨b', hb', s', hrep⟩ := h b hb
  refine ⟨b', hb', s + s', t + N, by push_cast; omega, ?_⟩
  rw [hrep]
  push_cast
  module

/-- **With the escape half assumed away, only the cut band is left for `D`.** -/
theorem hfringe_of_uPushable {S : Finset (ℤ × ℤ)} {a : ℤ × ℤ} {B D : Set (ℤ × ℤ)}
    {vl u' b₀ : ℤ × ℤ} (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hpush : UPushable B vl u' (edgeWidth S a u' vl))
    (hD : ∀ k ∈ chainFull B vl u' b₀ 0,
      Nivat.LE2.dot (expNormal u' vl) k
          < Nivat.LE2.dot (expNormal u' vl) b₀ + (cutWidth S a u' vl : ℤ) →
      ∀ z ∈ S.erase a, z + (k - a) ∈ D) :
    ∀ k ∈ chainFull B vl u' b₀ 0, ∀ z ∈ S.erase a,
      z + (k - a) ∈ chainFull B vl u' b₀ 0 ∪ D := by
  intro k hk z hz
  by_cases hcut : Nivat.LE2.dot (expNormal u' vl) b₀ + (cutWidth S a u' vl : ℤ)
      ≤ Nivat.LE2.dot (expNormal u' vl) k
  · obtain ⟨b, hb, s, t, hkrep⟩ := rep_of_mem_chainFull_zero hk
    obtain ⟨b'', hb'', s'', t'', ht'', heq⟩ := rep_deep_of_uPushable hpush hb s t
    have hk2 : k = b'' + s'' • vl + (t'' : ℤ) • u' := by rw [hkrep]; exact heq
    subst hk2
    exact Or.inl (deep_stays hunimod hb'' hcut ht'' z hz)
  · exact Or.inr (hD k hk (by omega) z hz)

/-! ## Is the cut band coverable by `Case1`'s `halfStrip B vl`? -/

/-- The cut band is closed under `+ u'`, and `u'` moves `dot (expNormal vl u')` by exactly one. -/
theorem cutBand_ray_u' {B : Set (ℤ × ℤ)} {vl u' b₀ k : ℤ × ℤ}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hk : k ∈ chainFull B vl u' b₀ 0) (i : ℕ) :
    k + (i : ℤ) • u' ∈ chainFull B vl u' b₀ 0 ∧
      Nivat.LE2.dot (expNormal u' vl) (k + (i : ℤ) • u')
        = Nivat.LE2.dot (expNormal u' vl) k ∧
      Nivat.LE2.dot (expNormal vl u') (k + (i : ℤ) • u')
        = Nivat.LE2.dot (expNormal vl u') k + (i : ℤ) := by
  have hmu' : Nivat.LE2.dot (expNormal u' vl) u' = 0 := dot_expNormal_u'
  have hm'u' : Nivat.LE2.dot (expNormal vl u') u' = 1 := dot_expNormal_vl (det_swap hunimod)
  have hcut : Nivat.LE2.dot (expNormal u' vl) (k + (i : ℤ) • u')
      = Nivat.LE2.dot (expNormal u' vl) k := by
    simp only [Nivat.LE2.dot_add, dot_smul_right, hmu']
    ring
  refine ⟨?_, hcut, by simp only [Nivat.LE2.dot_add, dot_smul_right, hm'u']; ring⟩
  obtain ⟨b, hb, s, t, rfl⟩ := rep_of_mem_chainFull_zero hk
  have hrep : b + s • vl + (t : ℤ) • u' + (i : ℤ) • u'
      = b + s • vl + ((t + i : ℕ) : ℤ) • u' := by push_cast; module
  rw [hrep]
  refine mem_chainFull_zero_of_rep hb _ _ ?_
  have := hk.2
  simp only [expLevel, Nivat.LE2.halfPlaneGE] at this
  rw [← hrep, hcut]
  simpa using this

/-- **The negative answer.**  On `halfStrip (↑B') vl` the functional `dot (expNormal vl u')` takes
only the finitely many values it takes on `B'`; on the cut band it is unbounded.  So no
`Case1`-style `vl`-half-strip over a finite base contains the `u'`-ray through any point of the
chain — the cut band is transverse to it. -/
theorem not_ray_subset_halfStrip {B : Set (ℤ × ℤ)} {vl u' b₀ k : ℤ × ℤ}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hk : k ∈ chainFull B vl u' b₀ 0) (B' : Finset (ℤ × ℤ)) :
    ¬ (∀ i : ℕ, k + (i : ℤ) • u' ∈ Nivat.LE2.halfStrip (↑B' : Set (ℤ × ℤ)) vl) := by
  intro hsub
  have hm'vl : Nivat.LE2.dot (expNormal vl u') vl = 0 := dot_expNormal_u'
  set M : ℕ := B'.sup (fun b => (Nivat.LE2.dot (expNormal vl u') b).natAbs) with hM
  have hbound : ∀ i : ℕ, Nivat.LE2.dot (expNormal vl u') k + (i : ℤ) ≤ (M : ℤ) := by
    intro i
    obtain ⟨b, hb, t, hbt⟩ := hsub i
    have hval : Nivat.LE2.dot (expNormal vl u') (k + (i : ℤ) • u')
        = Nivat.LE2.dot (expNormal vl u') b := by
      rw [hbt]
      simp only [Nivat.LE2.dot_add, dot_smul_right, hm'vl]
      ring
    have hle : (Nivat.LE2.dot (expNormal vl u') b).natAbs ≤ M :=
      Finset.le_sup (f := fun b => (Nivat.LE2.dot (expNormal vl u') b).natAbs)
        (Finset.mem_coe.mp hb)
    have := (cutBand_ray_u' hunimod hk i).2.2
    omega
  have hbig := hbound ((M : ℤ) - Nivat.LE2.dot (expNormal vl u') k + 1).toNat
  have hnn : (0 : ℤ) ≤ (M : ℤ) - Nivat.LE2.dot (expNormal vl u') k + 1 := by
    have := hbound 0
    omega
  rw [Int.toNat_of_nonneg hnn] at hbig
  omega

/-! ## §17  The row-order normal **is** the lex functional; `hgen` falls out of it

Dispatch of 2026-09-19 18:0x (team-lead, off their own `tmp/lexbridge_probe.lean` receipt).
`§13`'s normal is `n := c • expNormal u' vl + expNormal vl u'`, and
`VertexFromEdge.expNormal_swap_eq_expDual` (`VertexFromEdge.lean:351`, unconditional) says
`expNormal vl u' = L3Band.expDual u' vl`.  So `dot n` is literally the **lex functional** for the
coordinate pair `(expNormal u' vl, expDual u' vl)` with weight `c` — the same pair
`L3Band.expFrame` carries (`expFrame_n`/`expFrame_d'`, both `rfl`).  This section exposes what
that buys, all through the elaborator.

**`c` really is past the `expDual`-spread.**  `exists_generic_normal_unit` hid `c` inside its
proof; `exists_generic_normal_data` below is the same construction with `c` and the spread bound
`hspread` exported, so the lex step is a theorem rather than a claim about a hidden witness.
`exists_generic_normal_unit`/`exists_generic_normal` are **not** retracted or changed
(`PROTOCOL.md` §14) — `_data` is a strictly-more-informative sibling, and `_unit` is now its
projection.  The lex machinery itself (`dot_weighted`, `lex_max_of_dot_lt`, `lex_min_of_dot_lt`,
`exists_vertex_and_row_order_lex`) sits in §15, where the vertex is chosen; this section is what
the lex conjunct buys.

**Orientation — the question team-lead asked to have named, not papered over.**  `§15`'s `a` is
the `dot n`-**argmax**, so the lex conjunct it satisfies is at the **max** end:
`dot m z < dot m a ∨ (= ∧ dot m' z < dot m' a)` for `z ∈ S.erase a`, with
`m := expNormal u' vl`, `m' := expNormal vl u' = expDual u' vl`.  That is the end
`Colle37Geom.latticeConvex_erase_of_lexExtreme` (`ShellGeom.lean:74`) wants — its `hlex` binder is
character-for-character this — so consumer (1) is served, and `exists_generatesAt_and_row_order`
below feeds it through the elaborator to produce `GeneratesAt ξ S a` **at the row-order `a`
itself**, closing `hgen` without `IsVtx`/`face` and without `VertexFromEdge`'s separate generic
normal.  L3band's corner is at the **min** end, so `exists_lexMin_vertex` supplies that end
separately.  ⚠ The two ends are **different points** whenever `2 ≤ S.card`
(`not_lex_max_and_min`): there is no single `a` serving both, and the row order fixes which one
`hwin`/`hgen` get.  ⚠ Second mismatch, measured not assumed: `L3Band.hwin_corner`
(`L3Band.lean:3564`) binds a *double* minimum (`hlev : ∀ b ∈ S, dot fr.n a ≤ dot fr.n b` **and**
`hα : ∀ b ∈ S, dot fr.d' a ≤ dot fr.d' b`), which is strictly stronger than lex-min; `§E` does
**not** discharge it as it stands.  It discharges the lex-min restatement team-lead has asked
L3band for.

⚠ Reading limit (`PROTOCOL.md` §15): `hbase_of_row_order` is an implication — it still takes the
level/fringe data (`hseed`) and `hD` as binders.  It produces no `D`, and the `hfringe` hole of
§16 is untouched by this section.
-/

/-- **The two ends are different points.**  No `a` is both the strict `dot n`-max and the strict
`dot n`-min of an `S` with at least two elements — so "use the same `a` for the row order and for
L3band's corner" is not available, for a kernel reason. -/
theorem not_lex_max_and_min {S : Finset (ℤ × ℤ)} {n a : ℤ × ℤ}
    (h2 : 2 ≤ S.card) (haS : a ∈ S)
    (hmax : ∀ z ∈ S.erase a, Nivat.LE2.dot n z < Nivat.LE2.dot n a)
    (hmin : ∀ z ∈ S.erase a, Nivat.LE2.dot n a < Nivat.LE2.dot n z) : False := by
  have hcard : (S.erase a).card = S.card - 1 := Finset.card_erase_of_mem haS
  have hne : (S.erase a).Nonempty := by
    rw [← Finset.card_pos, hcard]; omega
  obtain ⟨z, hz⟩ := hne
  exact absurd (hmax z hz) (not_lt.mpr (le_of_lt (hmin z hz)))

open scoped Classical in
/-- **The min end, for L3band's corner.**  Same `n`, argmin instead of argmax.  ⚠ This is
lex-minimality, *not* `L3Band.hwin_corner`'s double minimum (`hlev ∧ hα`, both over all of `S`),
which is strictly stronger and which their own `no_corner_vertex_parallelogram` refutes on
Lemma 2.3's shape.  It discharges the lex restatement, not the current binder.
⚠ **Sharpened 2026-09-19 by L3band's §36, and not in this lemma's favour.**
`L3Band.chainFull_succ_subset_genClosure_iff_of_ahead` makes the double minimum an **`iff`**
under `hahead`: the containment holds *exactly when* `a` is the `(expNormal, expDual)` double
minimum.  So the gap is not an artifact of how the binder was written — lex-minimality
provably cannot be enough, and `exists_lexMin_vertex` is **not** a producer for that consumer.
Their `_of_reachback` sibling deletes `hlev`/`hα` outright and leaves `a` free, but its
`hreach` **cannot be supplied on-chain**: `Straddle` (`L1Region.lean:412`) quantifies
`∀ t₀, τ ≤ t₀ → …`, so `hcover` must hold for *every* larger `t₀`, and for large `t₀` `hahead`
holds — at which point the `iff` makes the double minimum **necessary**.  `_of_reachback`
covers only the small-`t₀` segment and was ruled zero-consumers-by-construction (team-lead,
2026-09-19 18:30; L3band annotated it in place per §14).  So the corner side does **not**
become moot, and this section's max/min distinction stands.  (Recorded as the statement and
ruling L3band relays; not re-run here.) -/
theorem exists_lexMin_vertex {S : Finset (ℤ × ℤ)} (hne : S.Nonempty)
    {u' vl : ℤ × ℤ} (hunimod : Nivat.det u' vl = 1 ∨ Nivat.det u' vl = -1) :
    ∃ a ∈ S, ∀ z ∈ S.erase a,
      Nivat.LE2.dot (expNormal u' vl) a < Nivat.LE2.dot (expNormal u' vl) z ∨
        (Nivat.LE2.dot (expNormal u' vl) a = Nivat.LE2.dot (expNormal u' vl) z ∧
          Nivat.LE2.dot (expNormal vl u') a < Nivat.LE2.dot (expNormal vl u') z) := by
  classical
  obtain ⟨c, hc0, hspread, hprim, hinj, hvl, hu', hexp⟩ := exists_generic_normal_data S hunimod
  set n : ℤ × ℤ := c • expNormal u' vl + expNormal vl u' with hn
  obtain ⟨a, haS, hamin⟩ := S.exists_mem_eq_inf' hne (fun z => Nivat.LE2.dot n z)
  have hamin' : ∀ z ∈ S, Nivat.LE2.dot n a ≤ Nivat.LE2.dot n z := by
    intro z hz
    have hle := Finset.inf'_le (fun z => Nivat.LE2.dot n z) hz
    rw [hamin] at hle
    exact hle
  refine ⟨a, haS, ?_⟩
  intro z hz
  have hzS : z ∈ S := Finset.mem_of_mem_erase hz
  have hzne : z ≠ a := Finset.ne_of_mem_erase hz
  have hlt : Nivat.LE2.dot n a < Nivat.LE2.dot n z := by
    refine lt_of_le_of_ne (hamin' z hzS) ?_
    intro heq
    exact hzne (hinj (Finset.mem_coe.mpr hzS) (Finset.mem_coe.mpr haS) heq.symm)
  exact lex_min_of_dot_lt hspread haS hzS hlt

/-- **`hgen` at the row-order `a`, through the elaborator (`PROTOCOL.md` §27).**  The lex conjunct
is fed straight into `Colle37Geom.latticeConvex_erase_of_lexExtreme`, whose output is
`IsGeneratingSet`'s third field's premise.  So the vertex that generates and the vertex that
orders the rows are the *same point*, with no compatibility obligation and no `IsVtx`/`face`
detour. -/
theorem exists_generatesAt_and_row_order {A : Type*} {ξ : Config A} {S : Finset (ℤ × ℤ)}
    (hSgen : IsGeneratingSet ξ S) {u' vl : ℤ × ℤ}
    (hunimod : Nivat.det u' vl = 1 ∨ Nivat.det u' vl = -1) :
    ∃ (n a : ℤ × ℤ), GeneratesAt ξ S a ∧ Nivat.LE2.Prim n ∧ a ∈ S ∧
      (∀ z ∈ S.erase a, Nivat.LE2.dot n z < Nivat.LE2.dot n a) ∧
      0 < Nivat.LE2.dot n vl ∧ Nivat.LE2.dot n u' = 1 ∧
      0 < Nivat.LE2.dot n (expNormal u' vl) := by
  obtain ⟨hne, hconv, hgen⟩ := hSgen
  obtain ⟨n, a, hprim, _hvtx, haS, hlt, hlex, hvl, hu', hexp⟩ :=
    exists_vertex_and_row_order_lex hne hunimod
  exact ⟨n, a, hgen a haS (Nivat.Colle37Geom.latticeConvex_erase_of_lexExtreme hconv hlex),
    hprim, haS, hlt, hvl, hu', hexp⟩

/-- **The assembled `hbase`, with `a`, `n`, `hgen`, `hlt` and `enum` all internal.**  What is left
for the caller is exactly `hD` and the level/fringe data `hseed` — and `hseed` receives `n` and
`a` as *parameters*, so it never has to name them.  ⚠ `hseed` is a binder: this theorem produces
no `D` and does not touch §16's `hfringe` hole. -/
theorem hbase_of_row_order {ξ : Config ℤ} {e : ℤ × ℤ} {S : Finset (ℤ × ℤ)}
    (hSgen : IsGeneratingSet ξ S) {u' vl : ℤ × ℤ}
    (hunimod : Nivat.det u' vl = 1 ∨ Nivat.det u' vl = -1)
    {B : Set (ℤ × ℤ)} {b₀ : ℤ × ℤ} {c : ℤ} {D : Set (ℤ × ℤ)}
    (hD : ∀ z ∈ D, (T e ξ) z = T (c • vl) (T e ξ) z)
    (hseed : ∀ n a : ℤ × ℤ, a ∈ S →
      Nivat.LE2.dot n u' = 1 → 0 < Nivat.LE2.dot n vl →
      ∃ L₀ : ℤ,
        (∀ i : ℕ, ∃ w ∈ chainFull B vl u' b₀ 0, Nivat.LE2.dot n w = L₀ + (i : ℤ)) ∧
        (∀ w ∈ chainFull B vl u' b₀ 0, L₀ ≤ Nivat.LE2.dot n w) ∧
        (∀ k ∈ chainFull B vl u' b₀ 0, ∀ z ∈ S.erase a,
          z + (k - a) ∈ chainFull B vl u' b₀ 0 ∪ D)) :
    Colle41.PeriodOn (T e ξ) (chainFull B vl u' b₀ 0) (c • vl) := by
  obtain ⟨n, a, hgen, _hprim, haS, hlt, hvl, hu', _hexp⟩ :=
    exists_generatesAt_and_row_order hSgen hunimod
  obtain ⟨L₀, hlevne, hbot, hfringe⟩ := hseed n a haS hu' hvl
  obtain ⟨enum, hwin, hK⟩ :=
    exists_enum_hwin_hK (K := chainFull B vl u' b₀ 0) (D := D) hlt hlevne hbot hfringe
      (subset_refl _)
  exact hbase_of_sweep_self hgen hD enum hwin hK


/-! ## §18  The cut band vs `wedgeFull`: escape is governed by `expNormal vl u'`, not by the cut

Team-lead's dispatch (2026-09-19 18:5x) asked for this: for every `n` with `0 < dot n vl` and
`dot n u' = 1`, every `a` that is the strict `n`-max of `S`, and every `z ∈ S.erase a` with
`dot (expNormal u' vl) z < dot (expNormal u' vl) a`, the cut band escapes `R ∪ D` for **every**
`D ⊆ wedgeFull B vl u'`.

**That statement is false.  This section is its refutation together with the exact replacement.**

*Reduction.*  Every band point has `dot (expNormal u' vl) w < dot (expNormal u' vl) b₀` while
`chainFull … 0` demands `≥`, so the band is disjoint from `chainFull … 0` and the ask is exactly
`cutBand ⊄ wedgeFull B vl u'`.

*Why the expected mechanism does not transfer.*  Cclaim's `not_cutFringe_subset_halfStrip`
(`L1Claim.lean` §4) works because the band is closed under `+ u'`, so `dot (expNormal vl u')` is
unbounded above on it, which no **finite-base** half-strip can contain.  `wedgeFull` is not such a
target: `dot (expNormal vl u') u' = 1` (`dot_expNormal_swap_u'`) and `wedgeFull` contains whole
`u'`-rays, so it is unbounded above in the very same functional.

*What does govern it.*  `exists_dot_le_of_mem_wedgeFull` below is the missing converse of
`mem_wedgeFull_of_dot_le` (`L1CoverWedge.lean:209`): **`wedgeFull B vl u'` is the
`expNormal vl u'`-upper set of `B`.**  A fringe translate `k + (z - a)` shifts that functional by
`dot (expNormal vl u') (z - a)`, so *leaving the wedge* needs
`dot (expNormal vl u') z < dot (expNormal vl u') a`, while *dropping below the cut* needs
`dot (expNormal u' vl) z < dot (expNormal u' vl) a`.  `not_cutBand_subset_wedgeFull_iff` states
that the escape happens **exactly** when some `z ∈ S.erase a` is strictly below `a` in *both*.

*The suggested binder does not rescue it.*  Non-collinearity of `S` along `u'` — in this file's
terms `cutWidth S a u' vl ≠ 0` — is **not** the missing hypothesis.  §18.4's witness has
`cutWidth = 1`, satisfies every premise of the ask, and still admits no escape
(`premises_Ex`, `cutBand_subset_Ex`).

*No producer, and provably not from lex-maximality.*  Nothing on the chain supplies the
doubly-lower binder.  §15's `a` is the argmax of `n = c • expNormal u' vl + expNormal vl u'`, and
its lex conjunct is a **disjunction** — `dot m z < dot m a` *or* (`=` together with
`dot m' z < dot m' a`).  §18.4's witness is an instance where the first disjunct holds for the only
`z` while `dot m' z > dot m' a`, so the doubly-lower condition is genuinely extra content, not
slack in the present vertex choice.

⚠ Reading limit (`PROTOCOL.md` §15/§25).  What is refuted is the **universally quantified** ask.
The `iff` is a characterisation of when the band escapes; it is **not** a claim that the chain's
`S` fails it.  Whether `d.Sphi` has a doubly-lower point at its row-order vertex is open and is
not measured here.

⚠ `cutBand` is `L1Claim.cutFringe` with `fringe` unfolded, and is stated here rather than reused
because `L1Claim.lean` imports this file, not the other way round.  The two are `rfl`-equal;
that equality is checked by the kernel in `tmp/Aface_cutband_rfl.lean` (**in `tmp/`, not landed**),
not asserted by this docstring.
-/

/-! ### §18.1  The swapped frame, and `wedgeFull` as an upper set -/

theorem det_swap_unimod {u' vl : ℤ × ℤ} (hunimod : det u' vl = 1 ∨ det u' vl = -1) :
    det vl u' = 1 ∨ det vl u' = -1 := by
  simp only [det] at hunimod ⊢
  rcases hunimod with h | h
  · right; linear_combination -h
  · left; linear_combination -h

theorem dot_expNormal_swap_vl (u' vl : ℤ × ℤ) : Nivat.LE2.dot (expNormal vl u') vl = 0 :=
  dot_expNormal_u' (u' := vl) (vl := u')

theorem dot_expNormal_swap_u' {u' vl : ℤ × ℤ} (hunimod : det u' vl = 1 ∨ det u' vl = -1) :
    Nivat.LE2.dot (expNormal vl u') u' = 1 :=
  dot_expNormal_vl (u' := vl) (vl := u') (det_swap_unimod hunimod)

/-- **`wedgeFull` is the `expNormal vl u'`-upper set of `B`.**  The converse of
`mem_wedgeFull_of_dot_le` (`L1CoverWedge.lean:209`), which had only the `←` direction. -/
theorem exists_dot_le_of_mem_wedgeFull {B : Set (ℤ × ℤ)} {vl u' z : ℤ × ℤ}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) (hz : z ∈ wedgeFull B vl u') :
    ∃ b ∈ B, Nivat.LE2.dot (expNormal vl u') b ≤ Nivat.LE2.dot (expNormal vl u') z := by
  obtain ⟨g, hg, t, rfl⟩ := hz
  obtain ⟨b, hb, k, rfl⟩ := mem_fullSweep_iff.mp hg
  refine ⟨b, hb, ?_⟩
  rw [Nivat.LE2.dot_add, Nivat.LE2.dot_add, dot_smul_right,
    dot_smul_right, dot_expNormal_swap_vl, dot_expNormal_swap_u' hunimod]
  simp only [mul_zero, mul_one, add_zero]
  omega

/-! ### §18.2  The cut band, spelled out -/

/-- `L1Claim.cutFringe B vl u' b₀ S a` with `fringe` unfolded.  `rfl`-equal to it; stated here
because `L1Claim.lean` imports this file, not the other way round. -/
noncomputable def cutBand (B : Set (ℤ × ℤ)) (vl u' b₀ : ℤ × ℤ) (S : Finset (ℤ × ℤ))
    (a : ℤ × ℤ) : Set (ℤ × ℤ) :=
  {w | w ∈ ({w | ∃ k ∈ chainFull B vl u' b₀ 0, ∃ z ∈ S.erase a, w = k + (z - a)} \
      chainFull B vl u' b₀ 0) ∧
    Nivat.LE2.dot (expNormal u' vl) w < Nivat.LE2.dot (expNormal u' vl) b₀}

/-! ### §18.3  Escape happens iff `S` has a point strictly below `a` in BOTH functionals -/

theorem not_cutBand_subset_of_doubly_lower {B : Finset (ℤ × ℤ)} (hBne : B.Nonempty)
    {vl u' b₀ a : ℤ × ℤ} {S : Finset (ℤ × ℤ)}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hz : ∃ z ∈ S.erase a,
      Nivat.LE2.dot (expNormal u' vl) z < Nivat.LE2.dot (expNormal u' vl) a ∧
      Nivat.LE2.dot (expNormal vl u') z < Nivat.LE2.dot (expNormal vl u') a)
    {D : Set (ℤ × ℤ)} (hD : D ⊆ wedgeFull (↑B : Set (ℤ × ℤ)) vl u') :
    ¬ cutBand (↑B : Set (ℤ × ℤ)) vl u' b₀ S a ⊆
      chainFull (↑B : Set (ℤ × ℤ)) vl u' b₀ 0 ∪ D := by
  classical
  obtain ⟨z₀, hz₀, hzm, hzm'⟩ := hz
  obtain ⟨bmin, hbminB, hbmin⟩ :=
    B.exists_min_image (fun b => Nivat.LE2.dot (expNormal vl u') b) hBne
  set m : ℤ × ℤ := expNormal u' vl with hm
  set m' : ℤ × ℤ := expNormal vl u' with hm'
  obtain ⟨κ, hκ⟩ : ∃ κ : ℤ, κ = Nivat.LE2.dot m b₀ - Nivat.LE2.dot m bmin := ⟨_, rfl⟩
  obtain ⟨k, hk⟩ : ∃ k : ℤ × ℤ, k = bmin + κ • vl := ⟨_, rfl⟩
  have hmvl : Nivat.LE2.dot m vl = 1 := by rw [hm]; exact dot_expNormal_vl hunimod
  have hm'vl : Nivat.LE2.dot m' vl = 0 := by rw [hm']; exact dot_expNormal_swap_vl u' vl
  have hkwedge : k ∈ wedgeFull (↑B : Set (ℤ × ℤ)) vl u' :=
    ⟨k, mem_fullSweep_iff.mpr ⟨bmin, hbminB, κ, hk⟩, 0, by simp⟩
  have hklev : Nivat.LE2.dot m k = Nivat.LE2.dot m b₀ := by
    rw [hk, Nivat.LE2.dot_add, dot_smul_right, hmvl]; omega
  have hkm' : Nivat.LE2.dot m' k = Nivat.LE2.dot m' bmin := by
    rw [hk, Nivat.LE2.dot_add, dot_smul_right, hm'vl]; ring
  have hkK : k ∈ chainFull (↑B : Set (ℤ × ℤ)) vl u' b₀ 0 := by
    refine ⟨hkwedge, ?_⟩
    show expLevel u' vl b₀ 0 ≤ Nivat.LE2.dot (expNormal u' vl) k
    simp only [expLevel, Nat.cast_zero, sub_zero]
    rw [← hm, hklev]
  obtain ⟨w, hw⟩ : ∃ w : ℤ × ℤ, w = k + (z₀ - a) := ⟨_, rfl⟩
  have hwmlt : Nivat.LE2.dot m w < Nivat.LE2.dot m b₀ := by
    rw [hw, Nivat.LE2.dot_add, hklev, Nivat.LE2.dot_sub]; omega
  have hwnotK : w ∉ chainFull (↑B : Set (ℤ × ℤ)) vl u' b₀ 0 := by
    refine not_mem_chainFull_iff.mpr (Or.inr ?_)
    simpa only [expLevel, Nat.cast_zero, sub_zero, ← hm] using hwmlt
  have hwband : w ∈ cutBand (↑B : Set (ℤ × ℤ)) vl u' b₀ S a :=
    ⟨⟨⟨k, hkK, z₀, hz₀, hw⟩, hwnotK⟩, by simpa only [← hm] using hwmlt⟩
  have hwnotwedge : w ∉ wedgeFull (↑B : Set (ℤ × ℤ)) vl u' := by
    intro hmem
    obtain ⟨b, hb, hble⟩ := exists_dot_le_of_mem_wedgeFull hunimod hmem
    rw [← hm'] at hble
    have hbb : Nivat.LE2.dot m' bmin ≤ Nivat.LE2.dot m' b := hbmin b hb
    have hwm' : Nivat.LE2.dot m' w = Nivat.LE2.dot m' bmin + Nivat.LE2.dot m' (z₀ - a) := by
      rw [hw, Nivat.LE2.dot_add, hkm']
    rw [Nivat.LE2.dot_sub] at hwm'
    omega
  intro hsub
  rcases hsub hwband with h | h
  · exact hwnotK h
  · exact hwnotwedge (hD h)

/-- **The converse: with no doubly-lower point, the band stays inside `wedgeFull`.**
No finiteness, no nonemptiness on `B`.  This is what refutes the ask as stated. -/
theorem cutBand_subset_wedgeFull_of_not_doubly_lower {B : Set (ℤ × ℤ)}
    {vl u' b₀ a : ℤ × ℤ} {S : Finset (ℤ × ℤ)}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hno : ∀ z ∈ S.erase a,
      Nivat.LE2.dot (expNormal u' vl) z < Nivat.LE2.dot (expNormal u' vl) a →
      Nivat.LE2.dot (expNormal vl u') a ≤ Nivat.LE2.dot (expNormal vl u') z) :
    cutBand B vl u' b₀ S a ⊆ wedgeFull B vl u' := by
  rintro w ⟨⟨⟨k, hkK, z, hz, rfl⟩, -⟩, hcut⟩
  have hklev : expLevel u' vl b₀ 0 ≤ Nivat.LE2.dot (expNormal u' vl) k := hkK.2
  simp only [expLevel, Nat.cast_zero, sub_zero] at hklev
  have hzm : Nivat.LE2.dot (expNormal u' vl) z < Nivat.LE2.dot (expNormal u' vl) a := by
    rw [Nivat.LE2.dot_add, Nivat.LE2.dot_sub] at hcut; omega
  have hzm' := hno z hz hzm
  obtain ⟨b, hb, hble⟩ := exists_dot_le_of_mem_wedgeFull hunimod hkK.1
  refine mem_wedgeFull_of_dot_le hunimod hb ?_
  rw [Nivat.LE2.dot_add, Nivat.LE2.dot_sub]
  omega

/-- **The exact characterisation**, for the finite nonempty `B` the chain hands us. -/
theorem not_cutBand_subset_wedgeFull_iff {B : Finset (ℤ × ℤ)} (hBne : B.Nonempty)
    {vl u' b₀ a : ℤ × ℤ} {S : Finset (ℤ × ℤ)}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) :
    (¬ cutBand (↑B : Set (ℤ × ℤ)) vl u' b₀ S a ⊆
        chainFull (↑B : Set (ℤ × ℤ)) vl u' b₀ 0 ∪ wedgeFull (↑B : Set (ℤ × ℤ)) vl u') ↔
      ∃ z ∈ S.erase a,
        Nivat.LE2.dot (expNormal u' vl) z < Nivat.LE2.dot (expNormal u' vl) a ∧
        Nivat.LE2.dot (expNormal vl u') z < Nivat.LE2.dot (expNormal vl u') a := by
  constructor
  · intro hnot
    by_contra hno
    exact hnot (Set.Subset.trans (cutBand_subset_wedgeFull_of_not_doubly_lower hunimod
      (fun z hz hzm => not_lt.mp (fun hlt => hno ⟨z, hz, hzm, hlt⟩))) Set.subset_union_right)
  · intro hz
    exact not_cutBand_subset_of_doubly_lower hBne hunimod hz (subset_refl _)

/-! ### §18.4  The witness: every premise of the ask holds, and the conclusion fails -/

def uEx : ℤ × ℤ := (1, 0)
def vEx : ℤ × ℤ := (0, 1)
def bEx : ℤ × ℤ := (0, 0)
def aEx : ℤ × ℤ := (0, 0)
def nEx : ℤ × ℤ := (1, 2)
def SEx : Finset (ℤ × ℤ) := {((0 : ℤ), (0 : ℤ)), ((1 : ℤ), (-1 : ℤ))}
def BEx : Finset (ℤ × ℤ) := {((0 : ℤ), (0 : ℤ))}

theorem erase_SEx : SEx.erase aEx = {((1 : ℤ), (-1 : ℤ))} := by decide

theorem expNormal_uv : expNormal uEx vEx = ((0 : ℤ), (1 : ℤ)) := by
  simp only [expNormal, uEx, vEx, det]; decide

theorem expNormal_vu : expNormal vEx uEx = ((1 : ℤ), (0 : ℤ)) := by
  simp only [expNormal, uEx, vEx, det]; decide

/-- All the premises team-lead's ask carries, at the witness data. -/
theorem premises_Ex :
    det uEx vEx = 1 ∧
    Nivat.LE2.dot nEx uEx = 1 ∧
    0 < Nivat.LE2.dot nEx vEx ∧
    aEx ∈ SEx ∧ bEx ∈ BEx ∧ BEx.Nonempty ∧
    (∀ z ∈ SEx.erase aEx, Nivat.LE2.dot nEx z < Nivat.LE2.dot nEx aEx) ∧
    (∃ z ∈ SEx.erase aEx,
      Nivat.LE2.dot (expNormal uEx vEx) z < Nivat.LE2.dot (expNormal uEx vEx) aEx) ∧
    cutWidth SEx aEx uEx vEx ≠ 0 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, ⟨bEx, by decide⟩, ?_, ?_, ?_⟩
  · rw [erase_SEx]; intro z hz
    rw [Finset.mem_singleton] at hz; subst hz; decide
  · refine ⟨((1 : ℤ), (-1 : ℤ)), by rw [erase_SEx]; exact Finset.mem_singleton_self _, ?_⟩
    rw [expNormal_uv]; decide
  · intro hzero
    have h1 : (Nivat.LE2.dot (expNormal uEx vEx) (((1 : ℤ), (-1 : ℤ)) - aEx)).natAbs
        ≤ cutWidth SEx aEx uEx vEx :=
      Finset.le_sup (f := fun z => (Nivat.LE2.dot (expNormal uEx vEx) (z - aEx)).natAbs)
        (by rw [erase_SEx]; exact Finset.mem_singleton_self _)
    rw [hzero, expNormal_uv] at h1
    revert h1
    decide

/-- **The conclusion fails at that data**: the band is inside `wedgeFull`, so `D := wedgeFull`
witnesses `cutBand ⊆ chainFull ∪ D` with `D ⊆ wedgeFull`. -/
theorem cutBand_subset_Ex :
    cutBand (↑BEx : Set (ℤ × ℤ)) vEx uEx bEx SEx aEx ⊆
      chainFull (↑BEx : Set (ℤ × ℤ)) vEx uEx bEx 0 ∪ wedgeFull (↑BEx : Set (ℤ × ℤ)) vEx uEx := by
  refine Set.Subset.trans (cutBand_subset_wedgeFull_of_not_doubly_lower (by decide) ?_)
    Set.subset_union_right
  rw [erase_SEx, expNormal_uv, expNormal_vu]
  intro z hz
  rw [Finset.mem_singleton] at hz; subst hz
  intro _; decide

/-- **The diagnosis, isolated**: the witness has no doubly-lower point.  This is the conjunct
`§18.3`'s `iff` identifies as the real content, and the one §15's lex-maximality cannot supply —
here `z` is strictly *below* `a` in `expNormal uEx vEx` and strictly *above* it in
`expNormal vEx uEx`. -/
theorem no_doubly_lower_Ex :
    ¬ ∃ z ∈ SEx.erase aEx,
      Nivat.LE2.dot (expNormal uEx vEx) z < Nivat.LE2.dot (expNormal uEx vEx) aEx ∧
      Nivat.LE2.dot (expNormal vEx uEx) z < Nivat.LE2.dot (expNormal vEx uEx) aEx := by
  rintro ⟨z, hz, -, h2⟩
  rw [erase_SEx, Finset.mem_singleton] at hz
  subst hz
  rw [expNormal_vu] at h2
  revert h2
  decide

/-! ## §19.  Two queued kernel facts

Both were promised in the §18 report and are landed here unchanged in content.

**(a) When is the cut band empty?**  `cutWidth S a u' vl = 0` ⟺ `S` is a *single level* of the
cut normal `expNormal u' vl` ⟺ `S ⊆ a + ℤ·u'`.  The second equivalence needs `hunimod` and
is Cramer (`Nivat.ColleReg.reconstruct`, `L1CoverWedge.lean:195`): a lattice point killed by
`expNormal u' vl` has no `vl`-component left, so it *is* a multiple of `u'`.  Together with
Cclaim's `cutFringe_nonempty_iff` (`L1Claim.lean:661`) this closes the shape question for the
flat `hwin` route's `a`: the cut band of that route is empty exactly on a collinear window.

⚠ **Reading limit (`PROTOCOL.md` §15/§25), stated because the interesting half is *not* kernel.**
`cutWidth_ne_zero_of_not_collinear` is an implication with `∃ z ∈ S, ∀ t, z ≠ a + t • u'` as an
explicit binder.  That binder is **not** discharged anywhere in this file.  Cclaim's argument
that it holds on the chain — `S := d.Sphi` is the support of a product of `m ≥ 2` pairwise
non-parallel binomials (`DecompData.lean:106`, `RegionSteps.lean:1122`), hence contains the four
vertices of a non-degenerate parallelogram and cannot be collinear — is **their reading, not
compiled**, and is recorded here as attribution only.  The degenerate shapes (`m = 1`, all `h i`
parallel) are not covered by it.

⚠ **Scope limit (L3band's correction, accepted).**  Everything here characterises the **flat
`hwin` route's** `a` — the one that `exists_hwin_hK_chainFull_zero`'s `hlt` makes
`expNormal`-maximal.  The corner route's `a` is a *different consumer's* binder
(`straddle_of_cover`, `L1StraddleMax.lean:129`, carries its own `hgen`), and §19 says nothing
about it.  Do not read "the flat route's band is empty" as "the corner route dies too".

**(b) Nothing that pairs positively with `vl` is bounded below on `wedgeFull`.**
`fullSweep` sweeps **both** ways along `vl` (`fullSweep B vl = sweep (sweep B (-vl)) vl`), so for
any `n` with `0 < dot n vl` and any bound `c`, a single backward `vl`-step far enough puts a
`wedgeFull` point below `c`.  No finiteness, no unimodularity, no hypothesis on `u'`; `B`
nonempty is the only cost.  This is the arithmetic behind §18's remark that Cclaim's
`not_cutFringe_subset_halfStrip` mechanism does not transfer to `wedgeFull`: the half-strip is
bounded in a functional that `wedgeFull` is unbounded in, and `wedgeFull` is unbounded *below*
in every functional positive on `vl` as well.
-/

/-- **`cutWidth = 0` ⟺ the window is a single level of the cut normal.** -/
theorem cutWidth_eq_zero_iff_level {S : Finset (ℤ × ℤ)} {a u' vl : ℤ × ℤ} :
    cutWidth S a u' vl = 0 ↔
      ∀ z ∈ S.erase a, Nivat.LE2.dot (expNormal u' vl) z = Nivat.LE2.dot (expNormal u' vl) a := by
  constructor
  · intro h z hz
    have h1 : (Nivat.LE2.dot (expNormal u' vl) (z - a)).natAbs ≤ cutWidth S a u' vl :=
      Finset.le_sup (f := fun z => (Nivat.LE2.dot (expNormal u' vl) (z - a)).natAbs) hz
    have h2 : Nivat.LE2.dot (expNormal u' vl) (z - a)
        = Nivat.LE2.dot (expNormal u' vl) z - Nivat.LE2.dot (expNormal u' vl) a :=
      Nivat.LE2.dot_sub _ _ _
    omega
  · intro h
    refine Nat.le_zero.mp (Finset.sup_le ?_)
    intro z hz
    have h2 : Nivat.LE2.dot (expNormal u' vl) (z - a)
        = Nivat.LE2.dot (expNormal u' vl) z - Nivat.LE2.dot (expNormal u' vl) a :=
      Nivat.LE2.dot_sub _ _ _
    have := h z hz
    omega

/-- **`cutWidth = 0` ⟺ `S ⊆ a + ℤ·u'`.**  Cramer's identity, `hunimod` the only cost. -/
theorem cutWidth_eq_zero_iff_collinear {S : Finset (ℤ × ℤ)} {a u' vl : ℤ × ℤ}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) :
    cutWidth S a u' vl = 0 ↔ ∀ z ∈ S, ∃ t : ℤ, z = a + t • u' := by
  rw [cutWidth_eq_zero_iff_level]
  constructor
  · intro h z hz
    by_cases hza : z = a
    · exact ⟨0, by rw [hza]; simp⟩
    · have hze : z ∈ S.erase a := Finset.mem_erase.2 ⟨hza, hz⟩
      refine ⟨Nivat.LE2.dot (expNormal vl u') (z - a), ?_⟩
      have hrec := Nivat.ColleReg.reconstruct hunimod (z - a)
      have h0 : Nivat.LE2.dot (expNormal u' vl) (z - a) = 0 := by
        have h2 : Nivat.LE2.dot (expNormal u' vl) (z - a)
            = Nivat.LE2.dot (expNormal u' vl) z - Nivat.LE2.dot (expNormal u' vl) a :=
          Nivat.LE2.dot_sub _ _ _
        have := h z hze
        omega
      rw [h0, zero_smul, zero_add] at hrec
      rw [← hrec]
      abel
  · intro h z hz
    obtain ⟨t, ht⟩ := h z (Finset.mem_of_mem_erase hz)
    have h2 : Nivat.LE2.dot (expNormal u' vl) (z - a)
        = Nivat.LE2.dot (expNormal u' vl) z - Nivat.LE2.dot (expNormal u' vl) a :=
      Nivat.LE2.dot_sub _ _ _
    have h3 : z - a = t • u' := by rw [ht]; abel
    rw [h3, dot_smul_right, dot_expNormal_u', mul_zero] at h2
    omega

/-- **A non-collinear window has `cutWidth ≠ 0`.**  ⚠ The binder is *not* discharged here; see
the §19 reading limit above for why `d.Sphi` satisfying it is Cclaim's reading, not kernel. -/
theorem cutWidth_ne_zero_of_not_collinear {S : Finset (ℤ × ℤ)} {a u' vl : ℤ × ℤ}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (h : ∃ z ∈ S, ∀ t : ℤ, z ≠ a + t • u') : cutWidth S a u' vl ≠ 0 := by
  intro h0
  obtain ⟨z, hz, hzne⟩ := h
  obtain ⟨t, ht⟩ := (cutWidth_eq_zero_iff_collinear hunimod).mp h0 z hz
  exact hzne t ht

/-- **`wedgeFull` is unbounded below in every functional positive on `vl`.**  The backward half of
`fullSweep` does all the work; `B.Nonempty` is the only hypothesis on `B`, and `u'` is free. -/
theorem exists_mem_wedgeFull_dot_lt {B : Set (ℤ × ℤ)} {vl u' n : ℤ × ℤ}
    (hB : B.Nonempty) (hn : 0 < Nivat.LE2.dot n vl) (c : ℤ) :
    ∃ z ∈ wedgeFull B vl u', Nivat.LE2.dot n z < c := by
  obtain ⟨b, hb⟩ := hB
  set k : ℤ := min 0 (c - Nivat.LE2.dot n b - 1) with hk
  refine ⟨b + k • vl, ⟨b + k • vl, mem_fullSweep_iff.mpr ⟨b, hb, k, rfl⟩, 0, by simp⟩, ?_⟩
  have hdot : Nivat.LE2.dot n (b + k • vl)
      = Nivat.LE2.dot n b + k * Nivat.LE2.dot n vl := by
    rw [Nivat.LE2.dot_add, dot_smul_right]
  have hk0 : k ≤ 0 := min_le_left _ _
  have hk1 : k ≤ c - Nivat.LE2.dot n b - 1 := min_le_right _ _
  have hstep : k * Nivat.LE2.dot n vl ≤ k := by nlinarith
  omega

/-! ## §20.  The measurement team-lead asked for: does the chain's window admit a
doubly-lower point?

§18.3's `not_cutBand_subset_wedgeFull_iff` reduced "the cut band escapes `R`" to one exact
condition on the window `S` and its row-order vertex `a`:

```
∃ z ∈ S.erase a, dot (expNormal u' vl) z < dot (expNormal u' vl) a ∧
                  dot (expNormal vl u') z < dot (expNormal vl u') a
```

§18 reported this had **no producer**, and that §15's lex-maximality provably cannot supply it
(that conjunct is a *disjunction*).  §18.4 exhibited a window satisfying every premise of the
original ask — including `cutWidth ≠ 0` — with no such `z`.  **This section answers the
question that was left open, and the answer is yes: the condition is satisfiable, and the
lever is the shear of `u'`.**

**The mechanism, in one line.**  `u'` is only pinned up to `u' ↦ u' - T • vl`
(`det_shear`: unimodularity survives).  Under that shear the two normals behave completely
differently — `expNormal_shear` / `expNormal_swap_shear`:

```
expNormal (u' - T • vl) vl = expNormal u' vl + T • expNormal vl u'      -- the cut normal shears
expNormal vl (u' - T • vl) = expNormal vl u'                            -- the sweep normal does not
```

So the *sweep* coordinate of every point, and hence which vertex is the sweep-maximum, is
**invariant** under the shear, while the *cut* coordinate of a point strictly below `a` in the
sweep normal is driven to `-∞`.  Take `a` to be the sweep-maximum and `T` large: every point
below `a` in the sweep normal is eventually below it in the cut normal too.  Explicitly
`n := expNormal u' vl + K • expNormal vl u'` with `K := 2*M + 2`,
`M := S.sup (fun z => (dot (expNormal u' vl) z).natAbs)`, and `T := K - 1`.

**What the conclusion hands the consumer.**  All four binders of
`HbaseSeed.exists_hwin_hK_chainFull_zero` are produced at the sheared `u'`, in the shape the
elaborator reports for them (`PROTOCOL.md` §27 — `#check`ed, not recalled):
`det u'' vl = 1`, `∀ z ∈ S.erase a, dot n z < dot n a`, `0 ≤ dot n vl`, `dot n u'' = 1`.
Note `0 ≤`, non-strict; the witness gives `dot n vl = 1`.

⚠ **What this does NOT say — three limits, all load-bearing.**

1. **It is an existential over `T`, not a statement about a given `u'`.**  §18.4's witness is a
   fixed-`u'` instance where the condition **fails**, and that is not retracted
   (`PROTOCOL.md` §14).  The shear is the content of this section, not decoration: without it
   the condition is simply false for some `u'`.
2. **`hnc` is a binder and is not discharged here.**  It asks for two points of `S` with
   different `expNormal vl u'` value — i.e. `S` is not contained in a single line parallel to
   `vl`.  The on-chain argument (`d.h` pairwise non-parallel by `DecompData.h_dir`, `2 ≤ d.m`,
   so at most one generator is parallel to `vl`, so the zonotope hull is not a `vl`-line) is
   **reading, not compiled** — and it has to travel through `Sphi_eq`, which constrains only
   `Conv d.Sphi`, never `d.Sphi` itself.  No producer is named.
3. **Whether the L1 route can *use* the sheared `u'` is not measured.**  `u'` is existential in
   the goal at `RegionSteps.lean:1122` (`∃ e u u' v …`), which is why the shear is available at
   all; but the same `u'` carries the rest of `MaxBResidual`, and nothing here checks that a
   large `T` is compatible with those.  This is the next question, not a settled one.
-/

theorem dot_add_left (x y z : ℤ × ℤ) :
    Nivat.LE2.dot (x + y) z = Nivat.LE2.dot x z + Nivat.LE2.dot y z := by
  simp only [Nivat.LE2.dot, Prod.fst_add, Prod.snd_add]; ring

theorem dot_smul_left (c : ℤ) (x z : ℤ × ℤ) :
    Nivat.LE2.dot (c • x) z = c * Nivat.LE2.dot x z := by
  simp only [Nivat.LE2.dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

theorem dot_sub_rightN (x z w : ℤ × ℤ) :
    Nivat.LE2.dot x (z - w) = Nivat.LE2.dot x z - Nivat.LE2.dot x w := by
  simp only [Nivat.LE2.dot, Prod.fst_sub, Prod.snd_sub]; ring

theorem dot_smul_rightN (x : ℤ × ℤ) (c : ℤ) (z : ℤ × ℤ) :
    Nivat.LE2.dot x (c • z) = c * Nivat.LE2.dot x z := by
  simp only [Nivat.LE2.dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

theorem shear_mul_le_neg {K d : ℤ} (hK : 0 < K) (hd : d ≤ -1) : K * d ≤ -K := by
  nlinarith

theorem shear_le_mul {K d : ℤ} (hK : 0 < K) (hd : 1 ≤ d) : K ≤ K * d := by nlinarith

/-- The shear keeps the pair unimodular. -/
theorem det_shear {u' vl : ℤ × ℤ} (hdet : det u' vl = 1) (T : ℤ) :
    det (u' - T • vl) vl = 1 := by
  simp only [det, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at *
  linear_combination hdet

/-- **The cut normal shears; the sweep normal does not.** -/
theorem expNormal_shear {u' vl : ℤ × ℤ} (hdet : det u' vl = 1) (T : ℤ) :
    expNormal (u' - T • vl) vl = expNormal u' vl + T • expNormal vl u' := by
  have h1 : det (u' - T • vl) vl = 1 := det_shear hdet T
  have h2 : det vl u' = -1 := by
    simp only [det] at hdet ⊢; linear_combination -hdet
  simp only [expNormal, h1, hdet, h2, one_smul]
  apply Prod.ext <;>
    simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul] <;> ring

theorem expNormal_swap_shear {u' vl : ℤ × ℤ} (T : ℤ) :
    expNormal vl (u' - T • vl) = expNormal vl u' := by
  have h2 : det vl (u' - T • vl) = det vl u' := by
    simp only [det, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
  simp only [expNormal, h2]

/-- **The measurement.**

⚠ If this theorem's signature or proof changes, `exists_shear_hlt_and_doubly_lower_detMax` below
(the companion exporting `a`'s `det · vl`-maximality at `det u' vl = 1`, per team-lead
2026-09-20) reproduces this proof's internals (`M`, `K`, `n`, `hstrict`, `hBmax`) line-for-line and
must be updated to match, or it will silently drift from what this theorem actually proves. -/
theorem exists_shear_hlt_and_doubly_lower
    {vl u' : ℤ × ℤ} (hdet : det u' vl = 1)
    {S : Finset (ℤ × ℤ)} {z₀ w₀ : ℤ × ℤ} (hz₀ : z₀ ∈ S) (hw₀ : w₀ ∈ S)
    (hnc : Nivat.LE2.dot (expNormal vl u') z₀ ≠ Nivat.LE2.dot (expNormal vl u') w₀) :
    ∃ (T : ℤ) (a n : ℤ × ℤ),
      a ∈ S ∧
      det (u' - T • vl) vl = 1 ∧
      Nivat.LE2.dot n (u' - T • vl) = 1 ∧
      0 ≤ Nivat.LE2.dot n vl ∧
      (∀ z ∈ S.erase a, Nivat.LE2.dot n z < Nivat.LE2.dot n a) ∧
      (∃ z ∈ S.erase a,
        Nivat.LE2.dot (expNormal (u' - T • vl) vl) z
            < Nivat.LE2.dot (expNormal (u' - T • vl) vl) a ∧
        Nivat.LE2.dot (expNormal vl (u' - T • vl)) z
            < Nivat.LE2.dot (expNormal vl (u' - T • vl)) a) := by
  classical
  have hunimod : det u' vl = 1 ∨ det u' vl = -1 := Or.inl hdet
  have hinj : ∀ z w : ℤ × ℤ,
      Nivat.LE2.dot (expNormal u' vl) z = Nivat.LE2.dot (expNormal u' vl) w →
      Nivat.LE2.dot (expNormal vl u') z = Nivat.LE2.dot (expNormal vl u') w → z = w := by
    intro z w h1 h2
    have hz := Nivat.ColleReg.reconstruct hunimod z
    have hw := Nivat.ColleReg.reconstruct hunimod w
    rw [hz, hw, h1, h2]
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = S.sup (fun z => (Nivat.LE2.dot (expNormal u' vl) z).natAbs) :=
    ⟨_, rfl⟩
  have hbound : ∀ z ∈ S, -(M : ℤ) ≤ Nivat.LE2.dot (expNormal u' vl) z ∧
      Nivat.LE2.dot (expNormal u' vl) z ≤ (M : ℤ) := by
    intro z hz
    have : (Nivat.LE2.dot (expNormal u' vl) z).natAbs ≤ M := by
      rw [hM]
      exact Finset.le_sup (f := fun z => (Nivat.LE2.dot (expNormal u' vl) z).natAbs) hz
    omega
  obtain ⟨K, hK⟩ : ∃ K : ℤ, K = 2 * (M : ℤ) + 2 := ⟨_, rfl⟩
  have hKpos : (0 : ℤ) < K := by omega
  obtain ⟨n, hn⟩ : ∃ n, n = expNormal u' vl + K • expNormal vl u' := ⟨_, rfl⟩
  have hdotn : ∀ z, Nivat.LE2.dot n z
      = Nivat.LE2.dot (expNormal u' vl) z + K * Nivat.LE2.dot (expNormal vl u') z := by
    intro z; rw [hn, dot_add_left, dot_smul_left]
  have hSne : S.Nonempty := ⟨z₀, hz₀⟩
  obtain ⟨a, haS, hamax⟩ := S.exists_max_image (fun z => Nivat.LE2.dot n z) hSne
  obtain ⟨ha1, ha2⟩ := hbound a haS
  -- strict maximality
  have hstrict : ∀ z ∈ S.erase a, Nivat.LE2.dot n z < Nivat.LE2.dot n a := by
    intro z hz
    obtain ⟨hne, hzS⟩ := Finset.mem_erase.1 hz
    rcases lt_or_eq_of_le (hamax z hzS) with h | h
    · exact h
    · exfalso
      rw [hdotn, hdotn] at h
      obtain ⟨hz1, hz2⟩ := hbound z hzS
      have hms : K * (Nivat.LE2.dot (expNormal vl u') z - Nivat.LE2.dot (expNormal vl u') a)
          = K * Nivat.LE2.dot (expNormal vl u') z - K * Nivat.LE2.dot (expNormal vl u') a :=
        mul_sub _ _ _
      rcases lt_trichotomy (Nivat.LE2.dot (expNormal vl u') z)
        (Nivat.LE2.dot (expNormal vl u') a) with hlt | heq | hgt
      · have h1 : Nivat.LE2.dot (expNormal vl u') z - Nivat.LE2.dot (expNormal vl u') a ≤ -1 := by
          omega
        have h2 := shear_mul_le_neg hKpos h1
        omega
      · rw [heq] at h
        exact hne (hinj z a (by omega) heq)
      · have h1 : (1 : ℤ) ≤ Nivat.LE2.dot (expNormal vl u') z
            - Nivat.LE2.dot (expNormal vl u') a := by omega
        have h2 := shear_le_mul hKpos h1
        omega
  -- `a` is the sweep-normal max
  have hBmax : ∀ z ∈ S, Nivat.LE2.dot (expNormal vl u') z
      ≤ Nivat.LE2.dot (expNormal vl u') a := by
    intro z hz
    by_contra hcon
    rw [not_le] at hcon
    have h := hamax z hz
    rw [hdotn, hdotn] at h
    obtain ⟨hz1, hz2⟩ := hbound z hz
    have hms : K * (Nivat.LE2.dot (expNormal vl u') z - Nivat.LE2.dot (expNormal vl u') a)
        = K * Nivat.LE2.dot (expNormal vl u') z - K * Nivat.LE2.dot (expNormal vl u') a :=
      mul_sub _ _ _
    have h1 : (1 : ℤ) ≤ Nivat.LE2.dot (expNormal vl u') z
        - Nivat.LE2.dot (expNormal vl u') a := by omega
    have h2 := shear_le_mul hKpos h1
    omega
  -- a point strictly below in the sweep normal
  have hBne : ∃ z ∈ S, Nivat.LE2.dot (expNormal vl u') z
      ≠ Nivat.LE2.dot (expNormal vl u') a := by
    by_contra hall
    push_neg at hall
    exact hnc ((hall z₀ hz₀).trans (hall w₀ hw₀).symm)
  obtain ⟨z₁, hz₁S, hz₁ne⟩ := hBne
  have hz₁lt : Nivat.LE2.dot (expNormal vl u') z₁ < Nivat.LE2.dot (expNormal vl u') a :=
    lt_of_le_of_ne (hBmax z₁ hz₁S) hz₁ne
  obtain ⟨hzz1, hzz2⟩ := hbound z₁ hz₁S
  refine ⟨K - 1, a, n, haS, det_shear hdet _, ?_, ?_, hstrict, ?_⟩
  · rw [hn, dot_add_left, dot_smul_left, dot_sub_rightN, dot_sub_rightN, dot_smul_rightN,
      dot_smul_rightN, dot_expNormal_u', dot_expNormal_vl hunimod,
      dot_expNormal_swap_u' hunimod, dot_expNormal_swap_vl]
    ring
  · rw [hn, dot_add_left, dot_smul_left, dot_expNormal_vl hunimod, dot_expNormal_swap_vl]
    omega
  · refine ⟨z₁, Finset.mem_erase.2 ⟨fun h => hz₁ne (by rw [h]), hz₁S⟩, ?_, ?_⟩
    · rw [expNormal_shear hdet, dot_add_left, dot_add_left, dot_smul_left, dot_smul_left]
      have h1 : Nivat.LE2.dot (expNormal vl u') z₁ - Nivat.LE2.dot (expNormal vl u') a ≤ -1 := by
        omega
      have h2 := shear_mul_le_neg (by omega : (0:ℤ) < K - 1) h1
      have hms : (K - 1) * (Nivat.LE2.dot (expNormal vl u') z₁
            - Nivat.LE2.dot (expNormal vl u') a)
          = (K - 1) * Nivat.LE2.dot (expNormal vl u') z₁
            - (K - 1) * Nivat.LE2.dot (expNormal vl u') a := mul_sub _ _ _
      omega
    · rw [expNormal_swap_shear]
      exact hz₁lt

/-! ## Companion (team-lead, 2026-09-20): `exists_shear_hlt_and_doubly_lower`'s `a` is also the
`det · vl`-maximum

**Verified before use, per team-lead's checklist:**

- `dot (expNormal p q) z = det p q * det p z` for any `p q z` — unfold `expNormal`, `dot`, `det`
  to components and `ring`; unconditional.  Specialised to `(p,q) := (vl,u')`:
  `dot (expNormal vl u') z = det vl u' * det vl z`.  `det_comm` gives `det vl u' = -det u' vl` and
  `det vl z = -det z vl`, and the two negations cancel: `dot (expNormal vl u') z = det u' vl * det z vl`
  (`dot_expNormal_swap_eq_det` below) — confirmed, matches team-lead's derivation exactly.
- `M := S.sup (fun z => (dot (expNormal u' vl) z).natAbs)` really bounds
  `|dot (expNormal u' vl) z|` over `S`: that is literally `hbound` in the proof above
  (`Finset.le_sup` against the same `sup`), already present, re-used as-is.
- `a ∈ S` and the target is over `S.erase a`: at `z = a` the goal `det a vl ≤ det a vl` is `le_refl`,
  so restricting the derived `∀ z ∈ S, det z vl ≤ det a vl` to `S.erase a` is immediate
  (`Finset.mem_erase.1 hz |>.2`).
- **No mirror at `det u' vl = -1`.** `exists_shear_hlt_and_doubly_lower` takes `hdet : det u' vl = 1`
  as a hypothesis, not a disjunction — there is nothing to mirror; the theorem only ever runs in
  the `+1` branch.

**Not a restatement or weakening of `exists_shear_hlt_and_doubly_lower`.**  That theorem's
signature and proof above are untouched; this is a separate companion built by reconstructing its
`hBmax` step (`dot (expNormal vl u') z ≤ dot (expNormal vl u') a`, proved above but not exported)
and translating it through the identity into `det z vl ≤ det a vl`, matching
`detMax_of_hwin_hK`'s exact non-strict shape at `det u' vl = 1`.  `hnc` here is definitionally the
same non-degeneracy hypothesis the sibling theorem takes (by the same identity, since
`dot (expNormal vl u') z₀ ≠ dot (expNormal vl u') w₀` unfolds to `det z₀ vl ≠ det w₀ vl` at
`hdet`) — no new obligation. -/

theorem dot_expNormal_swap_eq_det (u' vl z : ℤ × ℤ) :
    Nivat.LE2.dot (expNormal vl u') z = det u' vl * det z vl := by
  simp only [expNormal, Nivat.LE2.dot, det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

theorem exists_shear_hlt_and_doubly_lower_detMax
    {vl u' : ℤ × ℤ} (hdet : det u' vl = 1)
    {S : Finset (ℤ × ℤ)} {z₀ w₀ : ℤ × ℤ} (hz₀ : z₀ ∈ S) (hw₀ : w₀ ∈ S)
    (hnc : Nivat.LE2.dot (expNormal vl u') z₀ ≠ Nivat.LE2.dot (expNormal vl u') w₀) :
    ∃ (T : ℤ) (a n : ℤ × ℤ),
      a ∈ S ∧
      (∀ z ∈ S.erase a, det z vl ≤ det a vl) ∧
      det (u' - T • vl) vl = 1 ∧
      Nivat.LE2.dot n (u' - T • vl) = 1 ∧
      0 ≤ Nivat.LE2.dot n vl ∧
      (∀ z ∈ S.erase a, Nivat.LE2.dot n z < Nivat.LE2.dot n a) ∧
      (∃ z ∈ S.erase a,
        Nivat.LE2.dot (expNormal (u' - T • vl) vl) z
            < Nivat.LE2.dot (expNormal (u' - T • vl) vl) a ∧
        Nivat.LE2.dot (expNormal vl (u' - T • vl)) z
            < Nivat.LE2.dot (expNormal vl (u' - T • vl)) a) := by
  classical
  have hunimod : det u' vl = 1 ∨ det u' vl = -1 := Or.inl hdet
  have hinj : ∀ z w : ℤ × ℤ,
      Nivat.LE2.dot (expNormal u' vl) z = Nivat.LE2.dot (expNormal u' vl) w →
      Nivat.LE2.dot (expNormal vl u') z = Nivat.LE2.dot (expNormal vl u') w → z = w := by
    intro z w h1 h2
    have hz := Nivat.ColleReg.reconstruct hunimod z
    have hw := Nivat.ColleReg.reconstruct hunimod w
    rw [hz, hw, h1, h2]
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = S.sup (fun z => (Nivat.LE2.dot (expNormal u' vl) z).natAbs) :=
    ⟨_, rfl⟩
  have hbound : ∀ z ∈ S, -(M : ℤ) ≤ Nivat.LE2.dot (expNormal u' vl) z ∧
      Nivat.LE2.dot (expNormal u' vl) z ≤ (M : ℤ) := by
    intro z hz
    have : (Nivat.LE2.dot (expNormal u' vl) z).natAbs ≤ M := by
      rw [hM]
      exact Finset.le_sup (f := fun z => (Nivat.LE2.dot (expNormal u' vl) z).natAbs) hz
    omega
  obtain ⟨K, hK⟩ : ∃ K : ℤ, K = 2 * (M : ℤ) + 2 := ⟨_, rfl⟩
  have hKpos : (0 : ℤ) < K := by omega
  obtain ⟨n, hn⟩ : ∃ n, n = expNormal u' vl + K • expNormal vl u' := ⟨_, rfl⟩
  have hdotn : ∀ z, Nivat.LE2.dot n z
      = Nivat.LE2.dot (expNormal u' vl) z + K * Nivat.LE2.dot (expNormal vl u') z := by
    intro z; rw [hn, dot_add_left, dot_smul_left]
  have hSne : S.Nonempty := ⟨z₀, hz₀⟩
  obtain ⟨a, haS, hamax⟩ := S.exists_max_image (fun z => Nivat.LE2.dot n z) hSne
  obtain ⟨ha1, ha2⟩ := hbound a haS
  have hstrict : ∀ z ∈ S.erase a, Nivat.LE2.dot n z < Nivat.LE2.dot n a := by
    intro z hz
    obtain ⟨hne, hzS⟩ := Finset.mem_erase.1 hz
    rcases lt_or_eq_of_le (hamax z hzS) with h | h
    · exact h
    · exfalso
      rw [hdotn, hdotn] at h
      obtain ⟨hz1, hz2⟩ := hbound z hzS
      have hms : K * (Nivat.LE2.dot (expNormal vl u') z - Nivat.LE2.dot (expNormal vl u') a)
          = K * Nivat.LE2.dot (expNormal vl u') z - K * Nivat.LE2.dot (expNormal vl u') a :=
        mul_sub _ _ _
      rcases lt_trichotomy (Nivat.LE2.dot (expNormal vl u') z)
        (Nivat.LE2.dot (expNormal vl u') a) with hlt | heq | hgt
      · have h1 : Nivat.LE2.dot (expNormal vl u') z - Nivat.LE2.dot (expNormal vl u') a ≤ -1 := by
          omega
        have h2 := shear_mul_le_neg hKpos h1
        omega
      · rw [heq] at h
        exact hne (hinj z a (by omega) heq)
      · have h1 : (1 : ℤ) ≤ Nivat.LE2.dot (expNormal vl u') z
            - Nivat.LE2.dot (expNormal vl u') a := by omega
        have h2 := shear_le_mul hKpos h1
        omega
  have hBmax : ∀ z ∈ S, Nivat.LE2.dot (expNormal vl u') z
      ≤ Nivat.LE2.dot (expNormal vl u') a := by
    intro z hz
    by_contra hcon
    rw [not_le] at hcon
    have h := hamax z hz
    rw [hdotn, hdotn] at h
    obtain ⟨hz1, hz2⟩ := hbound z hz
    have hms : K * (Nivat.LE2.dot (expNormal vl u') z - Nivat.LE2.dot (expNormal vl u') a)
        = K * Nivat.LE2.dot (expNormal vl u') z - K * Nivat.LE2.dot (expNormal vl u') a :=
      mul_sub _ _ _
    have h1 : (1 : ℤ) ≤ Nivat.LE2.dot (expNormal vl u') z
        - Nivat.LE2.dot (expNormal vl u') a := by omega
    have h2 := shear_le_mul hKpos h1
    omega
  have hdetMax : ∀ z ∈ S.erase a, det z vl ≤ det a vl := by
    intro z hz
    have hzS := (Finset.mem_erase.1 hz).2
    have h := hBmax z hzS
    rw [dot_expNormal_swap_eq_det, dot_expNormal_swap_eq_det, hdet, one_mul, one_mul] at h
    exact h
  have hBne : ∃ z ∈ S, Nivat.LE2.dot (expNormal vl u') z
      ≠ Nivat.LE2.dot (expNormal vl u') a := by
    by_contra hall
    push_neg at hall
    exact hnc ((hall z₀ hz₀).trans (hall w₀ hw₀).symm)
  obtain ⟨z₁, hz₁S, hz₁ne⟩ := hBne
  have hz₁lt : Nivat.LE2.dot (expNormal vl u') z₁ < Nivat.LE2.dot (expNormal vl u') a :=
    lt_of_le_of_ne (hBmax z₁ hz₁S) hz₁ne
  obtain ⟨hzz1, hzz2⟩ := hbound z₁ hz₁S
  refine ⟨K - 1, a, n, haS, hdetMax, det_shear hdet _, ?_, ?_, hstrict, ?_⟩
  · rw [hn, dot_add_left, dot_smul_left, dot_sub_rightN, dot_sub_rightN, dot_smul_rightN,
      dot_smul_rightN, dot_expNormal_u', dot_expNormal_vl hunimod,
      dot_expNormal_swap_u' hunimod, dot_expNormal_swap_vl]
    ring
  · rw [hn, dot_add_left, dot_smul_left, dot_expNormal_vl hunimod, dot_expNormal_swap_vl]
    omega
  · refine ⟨z₁, Finset.mem_erase.2 ⟨fun h => hz₁ne (by rw [h]), hz₁S⟩, ?_, ?_⟩
    · rw [expNormal_shear hdet, dot_add_left, dot_add_left, dot_smul_left, dot_smul_left]
      have h1 : Nivat.LE2.dot (expNormal vl u') z₁ - Nivat.LE2.dot (expNormal vl u') a ≤ -1 := by
        omega
      have h2 := shear_mul_le_neg (by omega : (0:ℤ) < K - 1) h1
      have hms : (K - 1) * (Nivat.LE2.dot (expNormal vl u') z₁
            - Nivat.LE2.dot (expNormal vl u') a)
          = (K - 1) * Nivat.LE2.dot (expNormal vl u') z₁
            - (K - 1) * Nivat.LE2.dot (expNormal vl u') a := mul_sub _ _ _
      omega
    · rw [expNormal_swap_shear]
      exact hz₁lt

section AfaceSec20DetMaxReceipts
#print axioms dot_expNormal_swap_eq_det
#print axioms exists_shear_hlt_and_doubly_lower_detMax
end AfaceSec20DetMaxReceipts

/-! ## K-parametrized variant (team-lead, 2026-09-20): export the shear as a hypothesis

The fixed-`K` theorem above produces `T` internally as `K - 1` where `K := 2*M+2`; a consumer
holding only the sealed `∃ T a n, ...` cannot choose its own shear. This variant moves `K` into
the hypothesis list with the weakest condition the proof actually uses (`2M+2 ≤ K`, an inequality),
so a caller needing to match an externally-determined shear threshold can do so.

**Three verification checks per team-lead's instruction (reading the proof, not guessing):**

1. **Direction**: `u' - T•vl` where `T := K - 1` and `K > 0`, so shears in the **negative `vl`
   direction** (subtracts a positive scalar multiple of `vl`).

2. **M-relationship**: This theorem's `M := S.sup (fun z => (dot (expNormal u' vl) z).natAbs)`;
   team-lead's is `Sw.sup (fun z => (det u' z).natAbs)`. Kernel-verified identity
   `dot (expNormal u' vl) z = det u' vl * det u' z` (`tmp/check_expNormal_identity.lean`) collapses
   to `det u' z` at `hdet : det u' vl = 1`, so **the two `M` definitions are identical** under
   `hdet`, differing only in Finset name (`S` vs `Sw`). Thresholds `2M+2` directly comparable.

3. **`hdet : det u' vl = 1` only**: Not cheap to generalize. `det_shear` / `expNormal_shear`
   (`:1969`, `:1975`) both require `= 1` in their signatures; the `hdetMax` step (`:2224-2229`)
   rewrites `dot (expNormal vl u') z = det u' vl * det z vl` using `hdet` to get `det z vl`,
   yielding `det z vl ≤ det a vl`. **At `det u' vl = -1` the sign flips** → conclusion becomes
   det**Min**, not det**Max** — would need a mirrored proof and separate statement, not bookkeeping. -/

theorem exists_shear_hlt_and_doubly_lower_detMax_at
    {vl u' : ℤ × ℤ} (hdet : det u' vl = 1)
    {S : Finset (ℤ × ℤ)} {z₀ w₀ : ℤ × ℤ} (hz₀ : z₀ ∈ S) (hw₀ : w₀ ∈ S)
    (hnc : Nivat.LE2.dot (expNormal vl u') z₀ ≠ Nivat.LE2.dot (expNormal vl u') w₀)
    (K : ℤ)
    (hK : 2 * ((S.sup (fun z => (Nivat.LE2.dot (expNormal u' vl) z).natAbs) : ℕ) : ℤ) + 2 ≤ K) :
    ∃ (a n : ℤ × ℤ),
      a ∈ S ∧
      (∀ z ∈ S.erase a, det z vl ≤ det a vl) ∧
      det (u' - (K - 1) • vl) vl = 1 ∧
      Nivat.LE2.dot n (u' - (K - 1) • vl) = 1 ∧
      0 ≤ Nivat.LE2.dot n vl ∧
      (∀ z ∈ S.erase a, Nivat.LE2.dot n z < Nivat.LE2.dot n a) ∧
      (∃ z ∈ S.erase a,
        Nivat.LE2.dot (expNormal (u' - (K - 1) • vl) vl) z
            < Nivat.LE2.dot (expNormal (u' - (K - 1) • vl) vl) a ∧
        Nivat.LE2.dot (expNormal vl (u' - (K - 1) • vl)) z
            < Nivat.LE2.dot (expNormal vl (u' - (K - 1) • vl)) a) := by
  classical
  have hunimod : det u' vl = 1 ∨ det u' vl = -1 := Or.inl hdet
  have hinj : ∀ z w : ℤ × ℤ,
      Nivat.LE2.dot (expNormal u' vl) z = Nivat.LE2.dot (expNormal u' vl) w →
      Nivat.LE2.dot (expNormal vl u') z = Nivat.LE2.dot (expNormal vl u') w → z = w := by
    intro z w h1 h2
    have hz := Nivat.ColleReg.reconstruct hunimod z
    have hw := Nivat.ColleReg.reconstruct hunimod w
    rw [hz, hw, h1, h2]
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = S.sup (fun z => (Nivat.LE2.dot (expNormal u' vl) z).natAbs) :=
    ⟨_, rfl⟩
  have hbound : ∀ z ∈ S, -(M : ℤ) ≤ Nivat.LE2.dot (expNormal u' vl) z ∧
      Nivat.LE2.dot (expNormal u' vl) z ≤ (M : ℤ) := by
    intro z hz
    have : (Nivat.LE2.dot (expNormal u' vl) z).natAbs ≤ M := by
      rw [hM]
      exact Finset.le_sup (f := fun z => (Nivat.LE2.dot (expNormal u' vl) z).natAbs) hz
    omega
  have hKpos : (0 : ℤ) < K := by omega
  obtain ⟨n, hn⟩ : ∃ n, n = expNormal u' vl + K • expNormal vl u' := ⟨_, rfl⟩
  have hdotn : ∀ z, Nivat.LE2.dot n z
      = Nivat.LE2.dot (expNormal u' vl) z + K * Nivat.LE2.dot (expNormal vl u') z := by
    intro z; rw [hn, dot_add_left, dot_smul_left]
  have hSne : S.Nonempty := ⟨z₀, hz₀⟩
  obtain ⟨a, haS, hamax⟩ := S.exists_max_image (fun z => Nivat.LE2.dot n z) hSne
  obtain ⟨ha1, ha2⟩ := hbound a haS
  have hstrict : ∀ z ∈ S.erase a, Nivat.LE2.dot n z < Nivat.LE2.dot n a := by
    intro z hz
    obtain ⟨hne, hzS⟩ := Finset.mem_erase.1 hz
    rcases lt_or_eq_of_le (hamax z hzS) with h | h
    · exact h
    · exfalso
      rw [hdotn, hdotn] at h
      obtain ⟨hz1, hz2⟩ := hbound z hzS
      have hms : K * (Nivat.LE2.dot (expNormal vl u') z - Nivat.LE2.dot (expNormal vl u') a)
          = K * Nivat.LE2.dot (expNormal vl u') z - K * Nivat.LE2.dot (expNormal vl u') a :=
        mul_sub _ _ _
      rcases lt_trichotomy (Nivat.LE2.dot (expNormal vl u') z)
        (Nivat.LE2.dot (expNormal vl u') a) with hlt | heq | hgt
      · have h1 : Nivat.LE2.dot (expNormal vl u') z - Nivat.LE2.dot (expNormal vl u') a ≤ -1 := by
          omega
        have h2 := shear_mul_le_neg hKpos h1
        omega
      · rw [heq] at h
        exact hne (hinj z a (by omega) heq)
      · have h1 : (1 : ℤ) ≤ Nivat.LE2.dot (expNormal vl u') z
            - Nivat.LE2.dot (expNormal vl u') a := by omega
        have h2 := shear_le_mul hKpos h1
        omega
  have hBmax : ∀ z ∈ S, Nivat.LE2.dot (expNormal vl u') z
      ≤ Nivat.LE2.dot (expNormal vl u') a := by
    intro z hz
    by_contra hcon
    rw [not_le] at hcon
    have h := hamax z hz
    rw [hdotn, hdotn] at h
    obtain ⟨hz1, hz2⟩ := hbound z hz
    have hms : K * (Nivat.LE2.dot (expNormal vl u') z - Nivat.LE2.dot (expNormal vl u') a)
        = K * Nivat.LE2.dot (expNormal vl u') z - K * Nivat.LE2.dot (expNormal vl u') a :=
      mul_sub _ _ _
    have h1 : (1 : ℤ) ≤ Nivat.LE2.dot (expNormal vl u') z
        - Nivat.LE2.dot (expNormal vl u') a := by omega
    have h2 := shear_le_mul hKpos h1
    omega
  have hdetMax : ∀ z ∈ S.erase a, det z vl ≤ det a vl := by
    intro z hz
    have hzS := (Finset.mem_erase.1 hz).2
    have h := hBmax z hzS
    rw [dot_expNormal_swap_eq_det, dot_expNormal_swap_eq_det, hdet, one_mul, one_mul] at h
    exact h
  have hBne : ∃ z ∈ S, Nivat.LE2.dot (expNormal vl u') z
      ≠ Nivat.LE2.dot (expNormal vl u') a := by
    by_contra hall
    push_neg at hall
    exact hnc ((hall z₀ hz₀).trans (hall w₀ hw₀).symm)
  obtain ⟨z₁, hz₁S, hz₁ne⟩ := hBne
  have hz₁lt : Nivat.LE2.dot (expNormal vl u') z₁ < Nivat.LE2.dot (expNormal vl u') a :=
    lt_of_le_of_ne (hBmax z₁ hz₁S) hz₁ne
  obtain ⟨hzz1, hzz2⟩ := hbound z₁ hz₁S
  refine ⟨a, n, haS, hdetMax, det_shear hdet _, ?_, ?_, hstrict, ?_⟩
  · rw [hn, dot_add_left, dot_smul_left, dot_sub_rightN, dot_sub_rightN, dot_smul_rightN,
      dot_smul_rightN, dot_expNormal_u', dot_expNormal_vl hunimod,
      dot_expNormal_swap_u' hunimod, dot_expNormal_swap_vl]
    ring
  · rw [hn, dot_add_left, dot_smul_left, dot_expNormal_vl hunimod, dot_expNormal_swap_vl]
    omega
  · refine ⟨z₁, Finset.mem_erase.2 ⟨fun h => hz₁ne (by rw [h]), hz₁S⟩, ?_, ?_⟩
    · rw [expNormal_shear hdet, dot_add_left, dot_add_left, dot_smul_left, dot_smul_left]
      have h1 : Nivat.LE2.dot (expNormal vl u') z₁ - Nivat.LE2.dot (expNormal vl u') a ≤ -1 := by
        omega
      have h2 := shear_mul_le_neg (by omega : (0:ℤ) < K - 1) h1
      have hms : (K - 1) * (Nivat.LE2.dot (expNormal vl u') z₁
            - Nivat.LE2.dot (expNormal vl u') a)
          = (K - 1) * Nivat.LE2.dot (expNormal vl u') z₁
            - (K - 1) * Nivat.LE2.dot (expNormal vl u') a := mul_sub _ _ _
      omega
    · rw [expNormal_swap_shear]
      exact hz₁lt

section AfaceSec20DetMaxAtReceipts
#print axioms exists_shear_hlt_and_doubly_lower_detMax_at
end AfaceSec20DetMaxAtReceipts

end Nivat.HbaseBridge

section AfaceSec18Receipts

#print axioms Nivat.HbaseBridge.exists_dot_le_of_mem_wedgeFull
#print axioms Nivat.HbaseBridge.not_cutBand_subset_of_doubly_lower
#print axioms Nivat.HbaseBridge.cutBand_subset_wedgeFull_of_not_doubly_lower
#print axioms Nivat.HbaseBridge.not_cutBand_subset_wedgeFull_iff
#print axioms Nivat.HbaseBridge.premises_Ex
#print axioms Nivat.HbaseBridge.no_doubly_lower_Ex
#print axioms Nivat.HbaseBridge.cutBand_subset_Ex
#print axioms Nivat.HbaseBridge.cutWidth_eq_zero_iff_level
#print axioms Nivat.HbaseBridge.cutWidth_eq_zero_iff_collinear
#print axioms Nivat.HbaseBridge.cutWidth_ne_zero_of_not_collinear
#print axioms Nivat.HbaseBridge.exists_mem_wedgeFull_dot_lt
#print axioms Nivat.HbaseBridge.expNormal_shear
#print axioms Nivat.HbaseBridge.expNormal_swap_shear
#print axioms Nivat.HbaseBridge.exists_shear_hlt_and_doubly_lower

end AfaceSec18Receipts

