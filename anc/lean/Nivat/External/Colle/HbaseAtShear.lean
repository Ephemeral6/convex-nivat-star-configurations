/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.MaxIndexProbe
import Nivat.External.Colle.HbaseBridge
import Nivat.External.Colle.L1SweepBridge
import Nivat.External.Colle.WedgeBundleBuild

/-!
# Lane Aparts: does any `hbase` producer transport (or produce afresh) at a sheared direction?

Dispatch: `WedgeResidualR.ofCorner` (`WedgeBundleBuild.lean:50/88`) bypasses `hwin`/`coverEnum`
entirely except for its `hbase` binder, `PeriodOn (T e ξ) (chainFull B vl u' b₀ k) (c • vl)`.
`hcorner` now has a producer (Lstrad's shear+corner constructor). The remaining question: is
there any producer of `hbase` that is *direction-free*, i.e. that either (a) transports an
already-proven `hbase` at `u'` to `hbase` at the sheared `u' - K • vl` without redoing the hard
work at the new point, or (b) proves `hbase` afresh at `u' - K • vl` from hypotheses no harder
to discharge there than at `u'`?

**Search method (shape, not name).** `grep -n "PeriodOn.*chainFull\|chainFull.*PeriodOn"` across
every file in `Nivat/External/Colle/` (not `grep hbase`, per the dispatch's explicit warning that
name search has twice missed a real producer). This surfaced every declaration whose statement
mentions `PeriodOn (T _ _) (chainFull …) (_ • vl)` in any position — binder, hypothesis inside a
`∀`, or conclusion — across `HbaseBridge.lean`, `HbaseSeed.lean`, `HwinHoleWeaken.lean`,
`L1Base.lean`, `L1Claim.lean`, `L1Contract.lean`, `L1CoverWedge.lean`, `L1Line0.lean`,
`L1StraddleFeed.lean`, `L1StraddleWedge.lean`, `L1SweepBridge.lean`, `MaxIndexProbe.lean`,
`VertexFromEdge.lean`, `WedgeBundleBuild.lean`. Filtering to declarations whose **conclusion**
(not just a `∀`-hypothesis threading the shape through) is `PeriodOn (T e ξ) (chainFull …) (c•vl)`
leaves exactly three candidate producers, examined below.

## Finding: no direction-free producer exists. The gap is already named, unproven, in the tree.

**1. `Nivat.HbaseBridge.hbase_of_row_order` (`HbaseBridge.lean:1506`).** Its `u'` is a genuine
theorem-level implicit `{u' vl : ℤ × ℤ}` (not a file-scope `variable` pinning it), so it is
formally direction-polymorphic — nothing stops instantiating it at `u' - K • vl`. But its
`hseed` hypothesis (`:1511-1517`) is stated *at that same `u'`*: it asks for the level/fringe
data of `chainFull B vl u' b₀ 0` itself. Instantiating at the sheared direction does not reuse
any work done at the unsheared direction — it relocates the identical difficulty (`hseed` at the
new point) rather than discharging it. `hseed` at a sheared direction is exactly what lane Hflat
is characterizing (`HbaseFlatSeed.lean`, per the dispatch — not duplicated here).

**2. `Nivat.HbaseBridge.hbase_at_of_sweep_of_isGeneratingSet`** (consumed at
`L1SweepBridge.lean:386`). Also direction-polymorphic in the same formal sense — it is called
there *at* the sheared direction `u' - K • vl` directly, producing `hbase0` at that point
(`L1SweepBridge.lean:385-387`). This looked, at first read, like exactly the affirmative answer
the dispatch was checking for. It is not: its `hwin` hypothesis at line 387 is supplied by
`hwin_hole B u c a K ha hconvS hc hBfin hamin hD`, and `hwin_hole` is not a proved lemma — it is
an **explicit hypothesis parameter** of the enclosing theorem `wedgeResidualR_of_hwin`
(`L1SweepBridge.lean:341-363`, binder at `:349`), whose own docstring states plainly
(`:326-328`): "⚠ **This does not prove `hwin`.** `sorries TOTAL` is unchanged and
`RegionSteps.lean` does not yet import this file. What it establishes is a kernel-checked count:
*one* obligation, at *this* data, suffices." So this producer is direction-generic in form, but
every instance of it — sheared or not — is gated behind the same unproven `hwin` (team-lead's
"dead route"); using it at a sheared direction does not avoid that gate.

**3. `Nivat.ColleReg.ChainFullShearTransport` (`MaxIndexProbe.lean:264-267`).** This is the actual
transport statement — "`hbase` at `u'` implies `hbase` at `u' - K • vl`" — but it is declared as
a bare `def _ : Prop`, not a theorem, and its own docstring (`:260-263`) states: "No producer for
this anywhere in the tree (grepped for `chainFull_shear`, no hits beyond this file)." It is
consumed nowhere as a proof — only `exists_N₀_hmin_hattain_shear` (`:274-290`) takes an *instance*
of it (`hbase'`, already assumed true at the sheared point) as an explicit hypothesis and derives
the rest of the placement data downstream of that assumption. This is precisely team-lead's and
Wbundle's prior finding (`HbaseVertexSeed.ChainFullShearUnbounded` is the negative side), and this
window's independent shape search confirms it rather than finding a fourth item.

**Why a cheap transport doesn't exist.** `PeriodOn x U h := ∀ z ∈ U, z + h ∈ U → x (z+h) = x z`
(`Lemma41.lean:659-660`) is a condition quantified over the *specific* set `U`. Shearing changes
`chainFull`'s defining set: `mem_chainFull_shear_iff` (`MaxIndexProbe.lean:241-258`, proved) gives
the membership characterization of `chainFull B vl (u' - K•vl) b₀ n`, but it is a membership
*iff*, not an equality of sets with the unsheared `chainFull B vl u' b₀ n` — so `PeriodOn` at one
does not unfold into `PeriodOn` at the other via `mem_chainFull_shear_iff` alone; some genuinely
new argument about how `T e ξ`'s periodicity behaves across the two different sets is needed.
That argument is exactly `ChainFullShearTransport`, and it has no proof anywhere in the tree.

## Conclusion for `ofCorner`

`WedgeResidualR.ofCorner` is blocked on the same wall as the `hwin` route it was built to bypass:
`hcorner` now has a producer, but `hbase` does not, at any direction, sheared or not, by any path
this search found. The **minimal missing lemma**, stated precisely (not proved — this is exactly
`Nivat.ColleReg.ChainFullShearTransport` already sitting in the tree unproven, restated here as
the deliverable the dispatch asked to pin down):

```
theorem chainFull_shear_transport {ξ : Config ℤ} {e : ℤ × ℤ} {B : Set (ℤ × ℤ)}
    {vl u' b₀ : ℤ × ℤ} {c : ℤ} (K : ℤ) (k : ℕ) :
    PeriodOn (T e ξ) (chainFull B vl u' b₀ k) (c • vl) →
    PeriodOn (T e ξ) (chainFull B vl (u' - K • vl) b₀ k) (c • vl)
```

closing exactly the `ChainFullShearTransport ξ e B vl u' b₀ c K k` `Prop`. Nothing weaker
suffices for `ofCorner`'s `hbase` binder as stated; nothing stronger is asked for by any
consumer found in this search.
-/

set_option autoImplicit false

open Nivat Nivat.LE2 Nivat.Colle41 Nivat.ColleReg Nivat.HbaseBridge Nivat.L1SweepBridge

-- Confirm the three candidate producers' exact shapes, fresh this window (not inherited from
-- the docstrings above), per hard rule 3.

#check @Nivat.HbaseBridge.hbase_of_row_order
#check @Nivat.HbaseBridge.hbase_at_of_sweep_of_isGeneratingSet
#check @Nivat.ColleReg.ChainFullShearTransport
#check @Nivat.ColleReg.mem_chainFull_shear_iff
#check @Nivat.L1SweepBridge.wedgeResidualR_of_hwin
#check @Nivat.ColleReg.L1Claim.WedgeResidualR.ofCorner

-- `ChainFullShearTransport` is `Prop`-valued and never instantiated by a closed proof term
-- anywhere in the tree (confirmed by the `hbase'` binder at `exists_N₀_hmin_hattain_shear`,
-- `MaxIndexProbe.lean:279`, which *assumes* an instance rather than deriving one).
#check @Nivat.ColleReg.exists_N₀_hmin_hattain_shear
