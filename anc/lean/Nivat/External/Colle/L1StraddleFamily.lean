/-
Copyright (c) 2026 Nivat formalisation project. All rights reserved.
-/
import Nivat.External.Colle.L1StraddleMax
import Nivat.External.Colle.HalfPlaneFamily

/-!
# `MaxBResidual.straddle` on Rsweep's half-plane family

Lane Afill's file (exclusive).  Target: the `straddle` field of `MaxBResidual`
(`L1Assemble.lean:962`), specialized to `Nivat.HalfPlaneFamily.ofHalfPlanes`
(`HalfPlaneFamily.lean:205`), where `F.R n = halfPlaneGE m (lev₀ - n * dot m u)`
(`ofHalfPlanes_R`, `HalfPlaneFamily.lean:213`).  Read-only on `HalfPlaneFamily.lean` and
`L1Assemble.lean`; does not touch `L1StraddleMax.lean` (Cconv's file), only imports it.

## §1  Vacuity check — result: **not vacuous**, confirmed in general, not just on this family

Team-lead's speculative collapse: `F.R N` and `F.R (N+1)` are literal translates of one another
on this family (`F.R (N+1) = {z | z + u ∈ F.R N}`, since `dot m` of a translate by `-u` shifts
the level by exactly `-dot m u`); could "periodic on `F.R N`, not periodic on `F.R (N+1)`" be
automatically contradictory, making `straddle` vacuous and free?

**No — checked directly, and the check does not even need the half-plane shape.** The only free
implication between the two levels is `PeriodOn.mono` (`Lemma41.lean`) applied to
`(F.grow N).subset : F.R N ⊆ F.R (N + 1)` (`RegionFamily.grow`, `L1Region.lean:135`), and it runs
the *other* way: periodicity on the **bigger** set `F.R (N+1)` gives periodicity on the smaller
`F.R N`, not the reverse. `periodOn_of_periodOn_succ` below is exactly that one-line fact, for
*any* `RegionFamily`, and it is silent on the converse. So `hN : PeriodOn (F.R N) (c•u)` and
`hN1 : ¬ PeriodOn (F.R (N+1)) (c•u)` are not merely non-contradictory in the abstract — they are
**exactly the pair `Nivat.L1Region.exists_greatest_periodOn` (`L1Region.lean:102-117`) produces**
for *every* `RegionFamily` whose family is not globally periodic (`F.union_not`), a theorem whose
own proof (`Nat.find` on the upward-closed failure set) witnesses that this configuration of
hypotheses genuinely occurs. `ofHalfPlanes` supplies exactly `F.monotone`, `F.base`, `F.union_not`
(via `hbase`, `hnp`), so the maximal-index construction applies to it unchanged, and `straddle`'s
premises are live on this family precisely as often as on any other. The half-plane shape changes
*what the conclusion needs* (see §2), not *whether the premises can both hold*.

## §2  What is left: the geometric content, restated concretely

Cconv's `straddle_of_cover` (`L1StraddleMax.lean:129`) reduces `Straddle` to a `genClosure` cover
hypothesis against an abstract `Rlo`/`Rhi`. It needs a generating set `Sφ` and vertex `a`
(`GeneratesAt ξ Sφ a`) — data `ofHalfPlanes`'s five inputs (`hmu'`, `hmu`, `hc`, `hnp`, `hbase`)
do not supply and cannot be manufactured from them: `ofHalfPlanes` only ever sees `m`, `lev₀`,
and a single half-plane period, nothing about how `ξ` is generated. So **there is no shortcut
from the slab shape alone** — the cover is still the whole geometric content, exactly as flagged
in `L1StraddleMax.lean`'s own docstring (§3: "not proved here", "depends on the shape of `F`").

What this file adds is `straddle_of_cover_ofHalfPlanes`: `straddle_of_cover` specialized via
`ofHalfPlanes_R`, so `hcover` is stated directly against `halfPlaneGE m (lev₀ - N * dot m u)` and
`halfPlaneGE m (lev₀ - (N+1) * dot m u)` — no `F.R` left to unfold — which is the form whoever
supplies the generating-set data (presumably from `chainFull`, per `L1StraddleMax.lean`'s closing
paragraph) will need to discharge against.
-/

set_option autoImplicit false

namespace Nivat.L1StraddleFamily

open Nivat Nivat.Colle Nivat.Colle41 Nivat.MaxEnv Nivat.L1Region Nivat.HalfPlaneFamily
  Nivat.L1StraddleMax Nivat.LE2

variable {ξ : Config ℤ} {e u u' m : ℤ × ℤ} {c lev₀ : ℤ} {S₁ Q : Finset (ℤ × ℤ)} {τ : ℤ}

/-! ## §1  The vacuity check, as a kernel fact -/

/-- **The only free direction between consecutive family members.**  Periodicity on the bigger
set `F.R (N+1)` gives periodicity on the smaller `F.R N`, via `PeriodOn.mono` and
`RegionFamily.grow`. This is general (no half-plane hypothesis used), and it runs opposite to
what would be needed to make `straddle`'s premises (`hN` true, `hN1` false) contradictory — so
they are not. -/
theorem periodOn_of_periodOn_succ {x : Config ℤ} {u u' : ℤ × ℤ} {c : ℤ}
    (F : RegionFamily x u u' c) {h : ℤ × ℤ} {N : ℕ} (hp : PeriodOn x (F.R (N + 1)) h) :
    PeriodOn x (F.R N) h :=
  hp.mono (F.grow N).subset

/-! ## §2  `Straddle` from a cover, restated against concrete half-planes -/

/-- **`straddle_of_cover`, specialized to `ofHalfPlanes`'s concrete `R`.**  Same content as
`Nivat.L1StraddleMax.straddle_of_cover`, with `F.R` unfolded via `ofHalfPlanes_R` so `hcover` is
stated directly against `halfPlaneGE m (lev₀ - N * dot m u)` / `halfPlaneGE m
(lev₀ - (N+1) * dot m u)` — nothing abstract left for a downstream geometric argument to unfold
through. -/
theorem straddle_of_cover_ofHalfPlanes
    (hmu' : dot m u' = 0) (hmu : 0 < dot m u) (hc : c ≠ 0) (hnp : ¬ IsPeriodic ξ)
    (hbase : PeriodOn (T e ξ) (halfPlaneGE m lev₀) (c • u)) (N : ℕ)
    (hN : PeriodOn (T e ξ) (halfPlaneGE m (lev₀ - (N : ℤ) * dot m u)) (c • u))
    (hN1 : ¬ PeriodOn (T e ξ) (halfPlaneGE m (lev₀ - ((N : ℤ) + 1) * dot m u)) (c • u))
    {Sφ : Finset (ℤ × ℤ)} {a : ℤ × ℤ} (hgen : GeneratesAt ξ Sφ a)
    (hcover : ∀ g ∈ S₁, g ∉ Q → ∀ t₀ : ℤ, τ ≤ t₀ →
      overlap (halfPlaneGE m (lev₀ - ((N : ℤ) + 1) * dot m u)) (c • u) ⊆
        genClosure Sφ a
          (overlap (halfPlaneGE m (lev₀ - (N : ℤ) * dot m u)) (c • u) ∪ ray g u' t₀)) :
    Straddle (T e ξ) (halfPlaneGE m (lev₀ - (N : ℤ) * dot m u))
      (halfPlaneGE m (lev₀ - ((N : ℤ) + 1) * dot m u)) S₁ Q u u' c τ :=
  straddle_of_cover (T_mem_orbitClosure ξ e) hgen hcover

/-- **All indices at once**, `MaxBResidual.straddle`'s quantifier shape, fully unfolded against
`ofHalfPlanes`. -/
theorem straddle_all_of_cover_ofHalfPlanes
    (hmu' : dot m u' = 0) (hmu : 0 < dot m u) (hc : c ≠ 0) (hnp : ¬ IsPeriodic ξ)
    (hbase : PeriodOn (T e ξ) (halfPlaneGE m lev₀) (c • u))
    {Sφ : Finset (ℤ × ℤ)} {a : ℤ × ℤ} (hgen : GeneratesAt ξ Sφ a)
    (hcover : ∀ N : ℕ,
      PeriodOn (T e ξ) (halfPlaneGE m (lev₀ - (N : ℤ) * dot m u)) (c • u) →
      ¬ PeriodOn (T e ξ) (halfPlaneGE m (lev₀ - ((N : ℤ) + 1) * dot m u)) (c • u) →
      ∀ g ∈ S₁, g ∉ Q → ∀ t₀ : ℤ, τ ≤ t₀ →
        overlap (halfPlaneGE m (lev₀ - ((N : ℤ) + 1) * dot m u)) (c • u) ⊆
          genClosure Sφ a
            (overlap (halfPlaneGE m (lev₀ - (N : ℤ) * dot m u)) (c • u) ∪ ray g u' t₀)) :
    ∀ N : ℕ,
      PeriodOn (T e ξ) ((ofHalfPlanes hmu' hmu hc hnp hbase).R N) (c • u) →
      ¬ PeriodOn (T e ξ) ((ofHalfPlanes hmu' hmu hc hnp hbase).R (N + 1)) (c • u) →
      Straddle (T e ξ) ((ofHalfPlanes hmu' hmu hc hnp hbase).R N)
        ((ofHalfPlanes hmu' hmu hc hnp hbase).R (N + 1)) S₁ Q u u' c τ := by
  intro N hN hN1
  rw [ofHalfPlanes_R] at hN hN1 ⊢
  rw [ofHalfPlanes_R]
  exact straddle_of_cover_ofHalfPlanes hmu' hmu hc hnp hbase N hN hN1 hgen (hcover N hN hN1)

end Nivat.L1StraddleFamily

section Receipts
/-! Standing `#print axioms` receipts.  Deletable as a block. -/

#print axioms Nivat.L1StraddleFamily.periodOn_of_periodOn_succ
#print axioms Nivat.L1StraddleFamily.straddle_of_cover_ofHalfPlanes
#print axioms Nivat.L1StraddleFamily.straddle_all_of_cover_ofHalfPlanes

end Receipts
