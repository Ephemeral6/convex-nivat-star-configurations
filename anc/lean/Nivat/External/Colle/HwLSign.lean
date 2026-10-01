/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.LatticeEdges

/-!
# `hwL`: the `ℓ_ι`-side sign of the second sweep direction `w`

Integrator, round 246.  Taken rather than dispatched: `hwL` sits on the round-179 orientation
freeze and its holder `w` is assembled at `RegionSteps.exists_chainData`, which is my account.

## What `hwL` is

The `ℓ_ι`-side normal of `ChainDataGeomParts` is

    n_L := det p vJ • (-p.2, p.1)

(`ChainPartsFeed.lean`, fields `ahat_halfPlane_L` / `ahat_attained_L` / `nfp_L`; the same
expression verbatim in `ChainGeom.lean`, `ChainAssemble.lean`, `ChainAssembleInter.lean`,
`HalfPlaneDoublyPeriodic.lean`, and `ItemII.dot_nL_self`).  `hwL` is the statement that the
second sweep direction `w` (`ChainPartsFeed.lean`, field `w` = Collé's `−v_{ℓ_{J+1}}`,
`b3_colle2.txt:518`) does not point out of the `ℓ_ι`-side half plane:

    hwL : dot n_L w ≤ 0

## §1 is an identity, §2 is the ruling

§1 shows `hwL` is not a new geometric quantity: `dot n_L w = det p vJ * det p w`, so it is a
sign condition on `det p w` relative to `det p vJ` and nothing more.

§2 is the part that decides how `hwL` gets discharged, and it is **negative**: the on-chain
sign fields do not force it.  The only field constraining `w` by a sign is

    hsweepW : dot nJ w < 0                 (`ChainPartsFeed.lean`, `b3_colle2.txt:518`)

and `nJ ⊥ vJ` (`FaceBlock.dot_nJ_vJ`, `ANormal.lean`).  §2 exhibits two configurations
agreeing on every on-chain sign field — `hsweep`, `hsweepW`, `dot_nJ_p`, `dot_nJ_vJ`,
`Primitive vJ`, `Primitive nJ` — in which `dot n_L w` takes **opposite** signs.  Hence `hwL`
is an independent bit that the producer of `ChainDataGeomParts` must supply, exactly like
`Primitive vJ1` (`ChainPartsFeed.lean`, field `vJ1`, item 1 of its ⛔ list).

⚠ Scope, stated so it is not inflated later (PROTOCOL §50/§54).  §2 refutes *derivability
from the listed sign fields*.  It does **not** claim `hwL` is false, and it does not range
over the fields that mention no sign (`bottom`, `escapeW`, the shell three, `rec_p`), which
could in principle pin `w` further.  What it does establish is that no purely sign-level
argument closes `hwL`, so the discharge must come from the construction of `w` itself.
-/

namespace Nivat
namespace LeadHwL

open Nivat.LE2

/-! ## §1.  `hwL` is a sign condition on `det p w` -/

/-- **The identity.**  `⟪n_L, w⟫ = det p v_J · det p w`, where `n_L = det p v_J • (-p.2, p.1)`
is the `ℓ_ι`-normal of `ahat_halfPlane_L` (`ChainPartsFeed.lean`).

Both sides expand to polynomials in the four coordinates; `ring` closes it.  Nothing about
`p`, `vJ`, `w` is assumed — in particular this holds in the collinear cell (`det p vl = 0`)
and the transverse one alike. -/
theorem dot_nL_eq (p vJ w : ℤ × ℤ) :
    dot (det p vJ • ((-p.2, p.1) : ℤ × ℤ)) w = det p vJ * det p w := by
  simp only [dot, det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

/-- **`hwL` restated.**  `⟪n_L, w⟫ ≤ 0` is exactly `det p v_J · det p w ≤ 0`, i.e. `det p w`
is opposite in sign to `det p v_J` (or zero).  So `hwL` carries no information beyond the
relative orientation of `w` and `v_J` about `p`. -/
theorem hwL_iff (p vJ w : ℤ × ℤ) :
    dot (det p vJ • ((-p.2, p.1) : ℤ × ℤ)) w ≤ 0 ↔ det p vJ * det p w ≤ 0 := by
  rw [dot_nL_eq]

/-- The `det p vJ ≠ 0` form, which is the one the chain is in (`ANormal.lean:46` records
`det p vJ ≠ 0` as the non-degeneracy `n_L` needs).  Under `det p vJ < 0` — the sign that
`EnvRefuteOrient.lean` (`wedge_gen_pos_multiple`) shows holds on the same-sign cell — `hwL`
becomes `0 ≤ det p w`. -/
theorem hwL_iff_of_neg {p vJ w : ℤ × ℤ} (h : det p vJ < 0) :
    dot (det p vJ • ((-p.2, p.1) : ℤ × ℤ)) w ≤ 0 ↔ 0 ≤ det p w := by
  rw [dot_nL_eq]
  constructor
  · intro hle; nlinarith
  · intro hge; nlinarith

/-! ## §2.  The sign fields do not force `hwL`

Two explicit configurations.  Both satisfy every sign-bearing on-chain field; they differ in
the sign of `⟪n_L, w⟫`.  All data is concrete, so the kernel checks the whole thing by
`decide`/`norm_num` with no geometry.

Shared: `p = (0,1)`, `vJ = (1,0)`, `nJ = (0,1)`, `vJ1 = (0,-1)`.
Then `det p vJ = 0·0 − 1·1 = −1 ≠ 0`, `dot nJ vJ = 0`, `dot nJ p = 1 ≠ 0`,
`dot nJ vJ1 = −1 < 0` (`hsweep`), and `hwL ↔ 0 ≤ det p w` by `hwL_iff_of_neg`.

`hsweepW : dot nJ w < 0` reads `w.2 < 0`, which leaves `w.1` completely free — and
`det p w = 0·w.2 − 1·w.1 = −w.1`.  So `w.1` flips `hwL` while every field above is untouched.
-/

/-- Configuration **A**: `w = (-1,-1)`.  This is the transverse `w` that
`ChainPartsFeed.lean`'s `w` docstring records as the one making `fillCover` hold on
`FillCoverWitness.lean` §2's instance. -/
theorem configA_hsweepW : dot ((0 : ℤ), (1 : ℤ)) ((-1 : ℤ), (-1 : ℤ)) < 0 := by decide

/-- Under configuration A, `⟪n_L, w⟫ = -1 ≤ 0`: `hwL` **holds**. -/
theorem configA_hwL :
    dot (det ((0 : ℤ), (1 : ℤ)) ((1 : ℤ), (0 : ℤ)) • ((-(1 : ℤ), (0 : ℤ)) : ℤ × ℤ))
      ((-1 : ℤ), (-1 : ℤ)) ≤ 0 := by decide

/-- Configuration **B**: `w = (1,-1)`.  Same `hsweepW`. -/
theorem configB_hsweepW : dot ((0 : ℤ), (1 : ℤ)) ((1 : ℤ), (-1 : ℤ)) < 0 := by decide

/-- Under configuration B, `⟪n_L, w⟫ = 1 > 0`: `hwL` **fails**. -/
theorem configB_not_hwL :
    ¬ dot (det ((0 : ℤ), (1 : ℤ)) ((1 : ℤ), (0 : ℤ)) • ((-(1 : ℤ), (0 : ℤ)) : ℤ × ℤ))
      ((1 : ℤ), (-1 : ℤ)) ≤ 0 := by decide

/-- The shared sign fields, checked once so the two configurations are known to differ in `w`
alone.  `dot nJ vJ = 0` is `FaceBlock.dot_nJ_vJ`; `dot nJ p ≠ 0` is `dot_nJ_p`;
`dot nJ vJ1 < 0` is `hsweep`; `det p vJ ≠ 0` is `ANormal.lean:46`'s non-degeneracy. -/
theorem shared_sign_fields :
    dot ((0 : ℤ), (1 : ℤ)) ((1 : ℤ), (0 : ℤ)) = 0 ∧
    dot ((0 : ℤ), (1 : ℤ)) ((0 : ℤ), (1 : ℤ)) ≠ 0 ∧
    dot ((0 : ℤ), (1 : ℤ)) ((0 : ℤ), (-1 : ℤ)) < 0 ∧
    det ((0 : ℤ), (1 : ℤ)) ((1 : ℤ), (0 : ℤ)) ≠ 0 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Both `vJ` and `nJ` are primitive here, so `vJ_prim` / `nJ_prim` are met too and cannot be
the missing constraint.  `Primitive v = IsCoprime v.1 v.2` (`Defs/Config.lean:156`); for
`(1,0)` and `(0,1)` this is `isCoprime_one_left` / `isCoprime_one_right`. -/
theorem shared_primitive :
    Primitive ((1 : ℤ), (0 : ℤ)) ∧ Primitive ((0 : ℤ), (1 : ℤ)) :=
  ⟨isCoprime_one_left, isCoprime_one_right⟩

/-- **The ruling, as one statement.**  There are two vectors `w₁ w₂` satisfying the same
`hsweepW` against the same `nJ`, with `⟪n_L, w₁⟫ ≤ 0` and `¬ ⟪n_L, w₂⟫ ≤ 0`.  Since every
other sign-bearing field of `ChainDataGeomParts` is a statement about `p`, `vJ`, `vJ1`, `nJ`
only — none mentions `w` except `hsweepW` — no conjunction of them implies `hwL`.

⟹ `hwL` is an obligation on whoever *constructs* `w` in `exists_chainData`, not a consequence
of the bundle's sign data. -/
theorem hwL_not_forced_by_hsweepW :
    ∃ w₁ w₂ : ℤ × ℤ,
      dot ((0 : ℤ), (1 : ℤ)) w₁ < 0 ∧ dot ((0 : ℤ), (1 : ℤ)) w₂ < 0 ∧
      dot (det ((0 : ℤ), (1 : ℤ)) ((1 : ℤ), (0 : ℤ)) • ((-(1 : ℤ), (0 : ℤ)) : ℤ × ℤ)) w₁ ≤ 0 ∧
      ¬ dot (det ((0 : ℤ), (1 : ℤ)) ((1 : ℤ), (0 : ℤ)) • ((-(1 : ℤ), (0 : ℤ)) : ℤ × ℤ)) w₂ ≤ 0 :=
  ⟨(-1, -1), (1, -1), configA_hsweepW, configB_hsweepW, configA_hwL, configB_not_hwL⟩

/-! ## §3.  What this leaves owed

`hwL` must be produced alongside `w`.  §1 says what to produce: with `det p vJ < 0` (the
same-sign cell's sign, `EnvRefuteOrient.lean`), it is exactly `0 ≤ det p w`, i.e. `w` lies on
the `v_J` side of the line `ℝp`.  Since `p ∥ v_ℓ` in the collinear cell (`RegionSteps.lean`'s
`hp_neg : ∃ c, 0 < c ∧ p = -(c:ℤ) • vl`), there `det p w = -(c:ℤ) * det vl w`, so the
condition becomes `det vl w ≤ 0` — a statement purely about the two sweep directions relative
to `v_ℓ`, with no `p` left in it. -/

/-- The collinear-cell reduction of §3, checked.  With `p = -(c:ℤ) • vl` and `0 < c`,
`hwL ↔ det vl w ≤ 0`, provided `det p vJ < 0`.  (`p` has been eliminated: the right-hand side
mentions only `vl` and `w`.) -/
theorem hwL_iff_collinear {vl vJ w : ℤ × ℤ} {c : ℕ} (hc : 0 < c)
    (hneg : det (-(c : ℤ) • vl) vJ < 0) :
    dot (det (-(c : ℤ) • vl) vJ • ((-(-(c : ℤ) • vl).2, (-(c : ℤ) • vl).1) : ℤ × ℤ)) w ≤ 0 ↔
      det vl w ≤ 0 := by
  rw [hwL_iff_of_neg hneg]
  have hcpos : (0 : ℤ) < (c : ℤ) := by exact_mod_cast hc
  have hexp : det (-(c : ℤ) • vl) w = -(c : ℤ) * det vl w := by
    simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
  rw [hexp]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

#print axioms dot_nL_eq
#print axioms hwL_iff
#print axioms hwL_iff_of_neg
#print axioms configA_hwL
#print axioms configB_not_hwL
#print axioms shared_sign_fields
#print axioms shared_primitive
#print axioms hwL_not_forced_by_hsweepW
#print axioms hwL_iff_collinear

end LeadHwL
end Nivat
