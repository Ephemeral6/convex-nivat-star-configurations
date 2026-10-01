/-
Copyright (c) 2026 Nivat formalisation project. All rights reserved.
-/
import Nivat.External.Colle.L1StraddleWedge
import Nivat.External.Colle.L1CoverWedge

/-!
# The maximal index `N₀` for `WedgeResidualR.ofCorner` is free, not a binder

Lane Lstrad's file (exclusive).  Team-lead's retargeted ask: of the nine live binders of
`Nivat.L1StraddleWedge.exists_L1MaxBResidual_of_corner` (`L1StraddleWedge.lean:346`) /
`Nivat.ColleReg.L1Claim.WedgeResidualR.ofCorner` (`WedgeBundleBuild.lean:50`) beyond `hbase`
(dead, `OPEN.md #13`) and `hcorner` (Hvert's), determine producer status of each, with the
`hN₀`/`hN₀1` pair prioritised.

## Answer: `hN₀` / `hN₀1` are not a genuine binder — `exists_hN₀` below derives them

`hN₀ : PeriodOn (T e ξ) (chainFull B vl u' b₀ (k + N₀)) (c • vl)` and
`hN₀1 : ¬ PeriodOn (T e ξ) (chainFull B vl u' b₀ (k + (N₀ + 1))) (c • vl)` together say: the
chain, started periodic at `k` (`hbase`), stays periodic up to some maximal index `N₀` and then
stops.  This is exactly `Nivat.L1Region.exists_greatest_periodOn` (`L1Region.lean:102`) applied
to `Rf n := chainFull B vl u' b₀ (k + n)`, fed by

* `hbase` at `Rf 0` (`k + 0 = k` is definitional, no rewrite needed),
* `Rf` monotone: `Nivat.L1Line0.monotone_chainFull_shift` (`L1Line0.lean:318`, already landed),
* `¬ PeriodOn (⋃ n, Rf n) (c • vl)`: `⋃ n, Rf n = wedgeFull B vl u'`
  (`iUnion_chainFull_shift` below — the same exhaustiveness argument as `L1RegionBuild.ofWedgeAt`'s
  `iUnion_cut (expLevel_exhaustive u' vl b₀)`, reindexed by `k`) composed with `hinf_of_ge`
  (`L1CoverWedge.lean:237`, Afill, already landed, needs only `hξ d hb₀ hunimod` and
  `c • vl ≠ 0`).

**So `hN₀`/`hN₀1` cost nothing beyond what `WedgeResidualR.ofCorner` already asks for**
(`hξ d hb₀ hunimod hc k hbase hvl_prim`) — no new mathematical content, no new binder.  This
answers the team-lead's priority question: it is **not** a second `hbase`-level debt; it is a
free corollary of `hbase` plus the already-closed `hinf`.

## The other seven live binders (`hb₀ hunimod hc k hmin hattain ha`), read off the tree

| binder | status | producer |
|---|---|---|
| `hb₀ : b₀ ∈ B` | **data choice, not an obligation** — `B`/`b₀` are existentials in the final goal `∃ … B …`, so any `B` with a chosen member works; the content lives in whether *that* `B` also carries `hbase`/`hcorner`, not in `hb₀` itself. |
| `hunimod : det u' vl = ±1` | **free** — `Primitive.exists_dual hvl_prim` (`Config.lean:164`) plus `Primitive_of_det_eq_one` (`PeriodCount.lean:340`) manufacture a `u'` satisfying it; recorded closed in `LEAF-L1.md` 14:2x ("`hunimod` 归档"). |
| `hc : 0 < c` (`c0` in the split) | **paired with `hbase`, not independently free** — `c` is shared between `hbase` and `hc`; `c := 1` trivially satisfies `hc` alone but then `hbase` must hold at that `c`, so this is `hbase`'s problem, not a separate gap (`L1Claim.lean:191-200`, "One owner, two binders"). |
| `k : ℕ` | **free** — pure data, `k := 0` always admissible; no proof obligation attaches to the choice of `k` itself (the obligation is `hbase` *at* that `k`). |
| `hmin`, `hattain` (jointly, Cprobe's placement) | **has a producer**: `Nivat.L1Line0.exists_shift_min_level` (`L1Line0.lean:294`) produces exactly this pair (`∀ s ∈ S₁, L ≤ dot (expNormal u' vl) s` and `∃ s ∈ S₁, dot (expNormal u' vl) s = L`) from `hu' : Primitive u'` and `hunimod`, for `S₁ := S.image (· + v)` and `L := expLevel u' vl b₀ (k + N₀) - 1` chosen via `v`. **Caveat, not independently checked here**: `exists_shift_min_level`'s output level must be threaded to equal `expLevel u' vl b₀ (k+N₀) - 1` for the *same* `N₀` `exists_hN₀` below produces — that threading is one `omega`/`rw` away but is not performed in this file (out of scope: doing so would duplicate `WedgeBundleBuild.lean`'s assembly, not add new content). |
| `ha : a ∈ Sφ` | **free once `Sφ`/`a` are chosen** — same shape as `hb₀`; the content is in `hcorner`, which names `a` and is Hvert's. |

## The 22 unused `L1Straddle.lean` declarations, rechecked against these seven

None of the 22 (`hline_not_free_of_base`, the `hline`/`hstraddle`/`semiAmbiguousAlong`
antitone lemmas, `not_eventually_period_of_straddle`, the `conj14_*`/`conj15_*`/`conj16_*` +
`SideData` block) mentions `chainFull`, `expLevel`, `expNormal`, `uCoord`, or `wedgeFull` at
all — they are stated on abstract `R R' : Set (ℤ × ℤ)` and `IsRegion`/`upperQuad`, one
`Config`-abstraction layer above the wedge-concrete route these seven binders live on.  So as
with the earlier report: **zero of the 22 feed any of these seven**; they remain a separate,
already-closed investigation (`LEAF-L1.md`'s same-side/cross-side result).  Module-level
orphan scan (`PROTOCOL.md` §20) confirms no new consumer for any of them appears on this route.
-/

set_option autoImplicit false

namespace Nivat.ColleReg

open Nivat Nivat.LE2 Nivat.Colle Nivat.Colle41 Nivat.L1Line0

variable {u' vl : ℤ × ℤ}

/-- `⋃ n, chainFull B vl u' b₀ (k + n) = wedgeFull B vl u'`: the same downward-exhaustiveness
as `L1RegionBuild.ofWedgeAt`'s union computation, reindexed by an arbitrary offset `k`. -/
theorem iUnion_chainFull_shift (B : Set (ℤ × ℤ)) (vl u' b₀ : ℤ × ℤ) (k : ℕ) :
    (⋃ n, chainFull B vl u' b₀ (k + n)) = wedgeFull B vl u' := by
  ext z
  simp only [Set.mem_iUnion, mem_chainFull_iff]
  constructor
  · rintro ⟨n, hz, -⟩
    exact hz
  · intro hz
    obtain ⟨n, hn⟩ := expLevel_exhaustive u' vl b₀ (dot (expNormal u' vl) z + (k : ℤ))
    refine ⟨n, hz, ?_⟩
    simp only [expLevel] at hn ⊢
    push_cast
    omega

/-- **`hN₀`/`hN₀1` cost nothing beyond `hbase` and the already-closed `hinf`.**  Free corollary
of `Nivat.L1Region.exists_greatest_periodOn`, `Nivat.L1Line0.monotone_chainFull_shift`,
`iUnion_chainFull_shift`, and `hinf_of_ge`.  Feeds directly into
`Nivat.L1StraddleWedge.exists_L1MaxBResidual_of_corner`'s `N₀ hN₀ hN₀1` binders (and hence into
`WedgeResidualR.ofCorner`), so a caller only needs `hb₀ hunimod hc k hbase` (already required
elsewhere) plus `hξ d hvl_prim` (already leaf-level binders) to get the maximal index for free. -/
theorem exists_hN₀ {ξ : Config ℤ} {e : ℤ × ℤ} (hξ : IsMinimalCounterexample ξ)
    (d : Nivat.Colle35.DecompDataZ ξ)
    {B : Set (ℤ × ℤ)} {b₀ : ℤ × ℤ} {c : ℤ} (hb₀ : b₀ ∈ B)
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) (hc0 : c ≠ 0) (hvl_prim : Primitive vl)
    (k : ℕ) (hbase : PeriodOn (T e ξ) (chainFull B vl u' b₀ k) (c • vl)) :
    ∃ N₀ : ℕ, PeriodOn (T e ξ) (chainFull B vl u' b₀ (k + N₀)) (c • vl) ∧
      ¬ PeriodOn (T e ξ) (chainFull B vl u' b₀ (k + (N₀ + 1))) (c • vl) := by
  have hinf : ¬ PeriodOn (T e ξ) (wedgeFull B vl u') (c • vl) :=
    hinf_of_ge e hξ d hb₀ hunimod (smul_ne_zero hc0 hvl_prim.ne_zero)
  have hunion : ¬ PeriodOn (T e ξ) (⋃ n, chainFull B vl u' b₀ (k + n)) (c • vl) := by
    rwa [iUnion_chainFull_shift]
  exact Nivat.L1Region.exists_greatest_periodOn
    (Nivat.L1Line0.monotone_chainFull_shift B vl u' b₀ k) hbase hunion

end Nivat.ColleReg

section Receipts
/-! Standing `#print axioms` receipts.  Deletable as a block. -/

#print axioms Nivat.ColleReg.iUnion_chainFull_shift
#print axioms Nivat.ColleReg.exists_hN₀

end Receipts
