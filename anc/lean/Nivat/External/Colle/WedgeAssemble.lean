/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.MaxIndexProbe
import Nivat.External.Colle.WedgeBundleBuild

set_option autoImplicit false

/-!
# `WedgeAssemble` — the wiring that reduces `exists_wedgeResidualR` to `hbase`

原文：b3_colle2.txt:792-804 (Claim 4.6).

This file contains **no new mathematics**.  Every ingredient below was already proved,
kernel-clean, and sitting off-chain; what was missing is the assembly action itself
(`CLAUDE.md` hard rule 4, "拆而后落" / the off-chain ledger note).

## Why this exists

`RegionSteps.lean:1035`'s docstring once reduced `exists_wedgeResidualR` to "`hbase` alone",
then **retracted** that reduction on 2026-09-20 (kept per `PROTOCOL.md` §14).  The retraction
was correct *for its own reason*: the reduction there ran through `HwinHoleZ`, which
`L1SweepBridge.not_hwinHoleZ_of_case1` (`:1604`) refutes from binders `exists_wedgeResidualR`
already has.

The reduction below goes through a **different** chain and is stated as a compiled theorem
rather than a docstring claim, so it is checkable instead of quotable:

| `ofCorner` obligation | discharged by |
|---|---|
| `ε`, `hconv`, `hline`, `hstraddle`, `c0` | `WedgeResidualR.ofCorner` itself (`WedgeBundleBuild.lean:50`) |
| `Sφ`, `hSφ` | `Nivat.ColleReg.exists_Sφ` (`MaxIndexProbe.lean:224`) |
| `a`, `ha`, `hcorner` | `Nivat.L1StraddleWedge.exists_corner_shear` (`L1StraddleWedge.lean:423`) |
| `N₀`, `hN₀`, `hN₀1`, `v`, `hmin`, `hattain` | `Nivat.ColleReg.exists_N₀_hmin_hattain_shear` (`MaxIndexProbe.lean:284`) |
| **`hbase`** | **nothing — the sole remaining hypothesis** |

## The shear, and why it is not the refuted `∀ K`

`hcorner` is **false at a fixed `u'`**: `HbaseVertexSeed.not_hcorner_of_zonoF_two_generators`
(`:188`) exhibits a genuine two-generator zonotope — the shape `Sphi_eq` is allowed to force on
`d.Sphi` — with no corner point at `u' = (1,0)`, `vl = (0,1)`.  It is nevertheless
**unconditionally satisfiable** once `u'` is allowed to shear, because `u'` is a *data field* of
`WedgeResidualR` (`L1Claim.lean:930`) whose only constraint is `hunimod`, and
`L1StraddleWedge.det_shear` (`:384`) shows `det (u' - K • vl) vl = det u' vl`.  So the two
refutations kill "**every** `u'` works", not "**some** `u'` works", and we were always entitled
to choose.  `L1StraddleWedge.wedgeFull_shear` (`:407`) confirms the shear does not move
`wedgeFull`, so `hconv` is untouched.

⚠ **`K` is an explicit parameter here, deliberately.**  It is *not* quantified `∀ K` inside a
hypothesis.  That move — `HwinHoleZ`'s "for every shear" — is exactly what
`not_hwinHoleZ_of_case1` defeats by driving `K` unbounded, and `CLAUDE.md` hard rule 7's
corollary names re-narrowing it to `∃ K` as the same invention with a different quantifier.
Here `K` is instead **chosen once by `exists_corner_shear` from `d.Sphi` alone** and then held
fixed; `hbase` is required at that one shear and nowhere else.  `chainFull` is genuinely *not*
shear-invariant (`MaxIndexProbe.mem_chainFull_shear_iff`, `:251`), which is why `hbase` must be
proved **at the sheared `u'` directly** rather than transported — and why any `hbase` lemma must
stay generic in `u'`.

**Dependency order, no circularity:** `K` depends on `d.Sphi` only; `b₀` and `k` may then be
chosen against the sheared `expNormal`; `N₀` depends on `hbase`; `v` depends on `N₀`.
-/

namespace Nivat.WedgeAssemble

open Nivat Nivat.LE2 Nivat.Colle Nivat.Colle41 Nivat.ColleReg Nivat.L1Line0
open Nivat.L1StraddleWedge Nivat.ColleReg.L1Claim

variable {u' vl : ℤ × ℤ}

/-- **`exists_wedgeResidualR` reduces to `hbase` at a single, named shear.**

Given `hbase` at the shear `u' - K • vl` together with a corner of `d.Sphi` at that same shear,
every other field of `WedgeResidualR` is produced by lemmas already on the tree.

原文：b3_colle2.txt:792-804.  Quantifier correspondence:
- `K` ↔ the choice of the second basis vector completing `ℓ` (Collé fixes one and never varies
  it; the shear freedom is ours, coming from `u'` being data rather than given)
- `a`, `hcorner` ↔ the extreme vertex of `𝒮_{φ_ι}` placed at `w` in Figure 10 (`:794-798`)
- `N₀`, `hN₀`, `hN₀1` ↔ the maximal index `ι` (`:800-804`)
- `hbase` ↔ "the knowledge of `T^u η` on `H_B(ℓ)` determines `T^u η` on `A₁`" (`:796`) -/
theorem nonempty_wedgeResidualR_of_hbase_at_shear
    {ξ : Config ℤ} {e : ℤ × ℤ} (hξ : Nivat.IsMinimalCounterexample ξ)
    (d : Nivat.Colle35.DecompDataZ ξ)
    {B : Set (ℤ × ℤ)} {b₀ : ℤ × ℤ} {c : ℤ} (hb₀ : b₀ ∈ B)
    (hunimod : Nivat.det u' vl = 1 ∨ Nivat.det u' vl = -1)
    (hc : 0 < c) (hvl_prim : Nivat.Primitive vl)
    (K : ℤ) (k : ℕ)
    (hbase : Nivat.Colle41.PeriodOn (Nivat.T e ξ)
      (Nivat.ColleReg.chainFull B vl (u' - K • vl) b₀ k) (c • vl))
    {a : ℤ × ℤ} (ha : a ∈ d.toDecompData.Sphi)
    (hcorner : ∀ b ∈ d.toDecompData.Sphi,
      0 ≤ Nivat.LE2.dot (Nivat.ColleReg.expNormal (u' - K • vl) vl) (b - a) ∧
        0 ≤ Nivat.L1Line0.uCoord (u' - K • vl) vl a b)
    {S : Finset (ℤ × ℤ)} (hS : S.Nonempty) :
    Nonempty (Nivat.ColleReg.L1Claim.WedgeResidualR ξ S vl) := by
  obtain ⟨N₀, v, hN₀, hN₀1, hmin, hattain⟩ :=
    Nivat.ColleReg.exists_N₀_hmin_hattain_shear hξ d hb₀ hunimod hc.ne' hvl_prim K k hbase hS
  have hunimod' : Nivat.det (u' - K • vl) vl = 1 ∨ Nivat.det (u' - K • vl) vl = -1 := by
    rwa [Nivat.L1StraddleWedge.det_shear]
  exact ⟨Nivat.ColleReg.L1Claim.WedgeResidualR.ofCorner (v := v) hb₀ hunimod' hc k hbase
    hN₀ hN₀1 hmin hattain (Nivat.ColleReg.exists_Sφ d) ha hcorner⟩

/-- **The shear is not an extra hypothesis: `exists_corner_shear` supplies it.**

The corner data `K`, `a`, `hcorner` of the previous theorem is produced unconditionally from
`d.Sphi.Nonempty`, so the only thing a caller must still bring is `hbase` **at the shear this
existential names**.  Stated in this order — `K` first, `hbase` after — precisely so that
`hbase` is never required `∀ K` (see the module docstring). -/
theorem exists_shear_corner_data
    {ξ : Config ℤ} (d : Nivat.Colle35.DecompDataZ ξ) (hSφ : d.toDecompData.Sphi.Nonempty) :
    ∃ (K : ℤ) (a : ℤ × ℤ), a ∈ d.toDecompData.Sphi ∧
      ∀ b ∈ d.toDecompData.Sphi,
        0 ≤ Nivat.LE2.dot (Nivat.ColleReg.expNormal (u' - K • vl) vl) (b - a) ∧
          0 ≤ Nivat.L1Line0.uCoord (u' - K • vl) vl a b := by
  obtain ⟨K, a, ha, hcorner⟩ :=
    Nivat.L1StraddleWedge.exists_corner_shear (u' := u') (vl := vl) hSφ
  exact ⟨K, a, ha, hcorner⟩

end Nivat.WedgeAssemble

section Receipts
/-! Standing `#print axioms` receipts.  Deletable as a block. -/

#print axioms Nivat.WedgeAssemble.nonempty_wedgeResidualR_of_hbase_at_shear
#print axioms Nivat.WedgeAssemble.exists_shear_corner_data

end Receipts
