/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.LatticeEdges
import Nivat.External.Colle.DecompData
import Nivat.External.Colle.WindowFit
import Nivat.External.Colle.ZonoEdgeGen
import Nivat.External.Colle.Claim47Core
import Nivat.External.Colle.L1RegionBuild
import Nivat.External.Colle.PolyChain
import Nivat.External.Colle.PolyChainSum
import Nivat.External.Colle.HsuppLengthBound
import Nivat.External.Colle.ConvTransport
import Nivat.External.Colle.HsuppCaseCW

/-!
# `HsuppAssemble` — Part (E) of `blueprint/LEAF-HSUPP.md`, assembling `hsuppZ`

原文：Definition 3.2（`b3_colle2.txt:402`）＋ Claim 4.6 的窗口（`:792-804`）。

**Target.** The exact statement of the `sorry` at
`Nivat/External/Colle/RegionSteps.lean:2899-2906`, reproduced verbatim below as
`hsuppZ_target`, with all hypotheses in the consumer's scope
(`RegionSteps.lean:2606-2686`) named explicitly as binders. `RegionSteps.lean`,
`ColleRegion.lean`, `Case2WindowProbe.lean`, `NfpLPreamble.lean` are **not** imported
here (hard rule); this file is checked standalone via `check1.sh`, never `lake build`.

## Status (2026-09-22, lane-chain)

`hsuppZ_target`'s statement is locked to the consumer's exact types (checked against
`RegionSteps.lean` line-by-line, see the table in the docstring below). The `n = -nℓ`
sub-case is fully proved (both sides are `0`). The two open half-plane sub-cases
(`0 < det (-nℓ) n` and `0 < det n (-nℓ)`) are **blocked** on lane-hsupp's parts (A)
`adjacent_shared_vertex` and (B) `face_eq_segment`, which are not yet in
`tmp/wip/PolyChain.lean` (only part (C) `det_pos_trans` is done there so far). They are
recorded below as explicit `sorry`s under §3, each with the exact statement still owed.
-/

namespace Nivat.HsuppAssemble

open Nivat Nivat.LE2 Nivat.ColleReg Nivat.Colle35 Finset Classical Pointwise

/-! ## §1. The scope, reproduced from `RegionSteps.lean:2606-2686`

Every binder here is either bound identically in `exists_cutResidualR`'s body (checked
against the file at the given line), or a consequence proved there with 0 `sorry`
(`hEeq`, `hlcB`, `hareaB`, `hnℓ_neg_mem`) — we take those as hypotheses too, since this
file cannot import `RegionSteps.lean`. -/

variable {ξ : Config ℤ} (d : DecompDataZ ξ)
variable {B : Set (ℤ × ℤ)} (hBfin : B.Finite) (hBne : B.Nonempty)
variable (hareaB : Nivat.LE2.PosArea B) (hlcB : Nivat.IsLatticeConvexRegion B)
variable {vl nℓ u' : ℤ × ℤ}
variable (hprim : Nivat.LE2.Prim nℓ) (hperp : Nivat.LE2.dot nℓ vl = 0)
variable {i : Fin d.toDecompData.m} (hdoth : Nivat.LE2.dot nℓ (d.toDecompData.h i) = 0)
variable (hunimod : det u' vl = 1 ∨ det u' vl = -1) (hnu : Nivat.LE2.dot nℓ u' = -1)
variable {cz : ℤ}
variable (hEeq : Nivat.LE2.E B = Nivat.LE2.E (↑d.toDecompData.Sphi : Set (ℤ × ℤ)))
variable (hnℓ_neg_mem : -nℓ ∈ Nivat.LE2.E (↑d.toDecompData.Sphi : Set (ℤ × ℤ)))

/-- **`hsuppZ`, verbatim**: the exact statement of the `sorry` at
`RegionSteps.lean:2899-2906`. Reproduced here quantifier-for-quantifier — every `∀`/`∃`
in this statement is copied from that file, no strengthening. -/
def hsuppZ_target : Prop :=
  ∀ g : ℤ × ℤ, g ∈ B → Nivat.LE2.dot nℓ g = cz →
    (∀ b ∈ B, Nivat.LE2.dot nℓ b = cz →
      Nivat.LE2.dot (expNormal u' vl) g ≤ Nivat.LE2.dot (expNormal u' vl) b) →
    ∀ n ∈ Nivat.LE2.E B,
      (∑ j ∈ Finset.univ.erase i,
          max 0 (Nivat.LE2.dot n
            (Nivat.ColleReg.orientUp (d.toDecompData.h j) nℓ))) ≤
        Nivat.LE2.suppVal B n - Nivat.LE2.dot n g

/-! ## §2. `n = -nℓ`: both sides are `0`, no chain needed.

`blueprint/LEAF-HSUPP.md` §2(E), first bullet. `dot (-nℓ) (orientUp (h j) nℓ) ≤ 0` for
every `j` (by definition of `orientUp`), so every summand on the left is `max 0 (≤0) = 0`.
On the right, `g` is `dot nℓ`-minimal in `B` at level `cz`, i.e. `dot (-nℓ) g` is
`dot (-nℓ)`-*maximal*, so `suppVal B (-nℓ) = dot (-nℓ) g`, making the right side `0` too. -/

omit hprim hperp hdoth hunimod hnu hEeq hnℓ_neg_mem in
include hBfin hBne in
theorem case_neg_nℓ (_hcz : ∀ g ∈ B, Nivat.LE2.dot nℓ g = cz →
      (∀ b ∈ B, Nivat.LE2.dot nℓ b = cz →
        Nivat.LE2.dot (expNormal u' vl) g ≤ Nivat.LE2.dot (expNormal u' vl) b) →
      True)
    (g : ℤ × ℤ) (hgcz : Nivat.LE2.dot nℓ g = cz) (_hgmin : ∀ b ∈ B, Nivat.LE2.dot nℓ b = cz →
      Nivat.LE2.dot (expNormal u' vl) g ≤ Nivat.LE2.dot (expNormal u' vl) b)
    (hgB : g ∈ B) (hgle : ∀ b ∈ B, cz ≤ Nivat.LE2.dot nℓ b) :
    (∑ j ∈ Finset.univ.erase i,
        max 0 (Nivat.LE2.dot (-nℓ)
          (Nivat.ColleReg.orientUp (d.toDecompData.h j) nℓ))) ≤
      Nivat.LE2.suppVal B (-nℓ) - Nivat.LE2.dot (-nℓ) g := by
  classical
  have hsum0 : (∑ j ∈ Finset.univ.erase i,
      max 0 (Nivat.LE2.dot (-nℓ)
        (Nivat.ColleReg.orientUp (d.toDecompData.h j) nℓ))) = 0 := by
    refine Finset.sum_eq_zero fun j _ => ?_
    unfold Nivat.ColleReg.orientUp
    by_cases hc : Nivat.LE2.dot nℓ (d.toDecompData.h j) < 0
    · rw [if_pos hc]
      have : Nivat.LE2.dot (-nℓ) (-(d.toDecompData.h j)) = Nivat.LE2.dot nℓ (d.toDecompData.h j) := by
        simp only [Nivat.LE2.dot, Prod.fst_neg, Prod.snd_neg]; ring
      rw [this]; omega
    · rw [if_neg hc]
      push_neg at hc
      have : Nivat.LE2.dot (-nℓ) (d.toDecompData.h j) = - Nivat.LE2.dot nℓ (d.toDecompData.h j) :=
        Nivat.LE2.dot_neg_left nℓ (d.toDecompData.h j)
      rw [this]; omega
  rw [hsum0]
  have hrhs : Nivat.LE2.suppVal B (-nℓ) - Nivat.LE2.dot (-nℓ) g = 0 := by
    have hle : Nivat.LE2.dot (-nℓ) g ≤ Nivat.LE2.suppVal B (-nℓ) :=
      Nivat.LE2.le_suppVal hBfin hBne hgB
    have hge : Nivat.LE2.suppVal B (-nℓ) ≤ Nivat.LE2.dot (-nℓ) g := by
      obtain ⟨z, hzB, hzeq⟩ := Nivat.LE2.exists_suppVal_eq hBfin hBne (-nℓ)
      rw [← hzeq]
      have hzlev : cz ≤ Nivat.LE2.dot nℓ z := hgle z hzB
      have hz : Nivat.LE2.dot (-nℓ) z = - Nivat.LE2.dot nℓ z := Nivat.LE2.dot_neg_left nℓ z
      have hg : Nivat.LE2.dot (-nℓ) g = - Nivat.LE2.dot nℓ g :=
        Nivat.LE2.dot_neg_left nℓ g
      rw [hz, hg]
      omega
    omega
  rw [hrhs]

/-! ## §3. The two open-half-plane sub-cases — **blocked, owed statements**

`blueprint/LEAF-HSUPP.md` §2(E), second/third bullets. Both need `chain_ccw_scalar`
(resp. `chain_cw_scalar`) from `tmp/wip/PolyChainSum.lean` applied with `T := B`,
`ν₀ := -nℓ`, plus:

* the per-generator normal `ν_j := primPart (-(dir (orientUp (d.toDecompData.h j) nℓ)))`
  (so `dir ν_j = orientUp (d.toDecompData.h j) nℓ / gcd`), shown to lie in
  `Arc hfin (-nℓ) n` for `n` with `dot n (orientUp (h j) nℓ) > 0`;
* injectivity of `j ↦ ν_j` on `{j | dot n (orientUp (h j) nℓ) > 0}`, from
  `d.toDecompData.h_dir` (`det (h j) (h k) ≠ 0` for `j ≠ k`);
* the length bound `faceLen B ν_j ≥ gcd(orientUp (h j) nℓ)`, from
  `Nivat.LE2.mem_E_zonoF` / `Nivat.LE2.face_encard_zonoF` (`ZonoEdgeGen.lean:116,209`,
  the zonotope's own 2-point face) plus `Nivat.Claim47.latticeConvex_between`
  (`Claim47Core.lean:248`, the `gcd - 1` intermediate lattice points) transported from
  `Sphi` to `B` via `hEeq` and the encard monotonicity in `henv` (**not yet threaded into
  this file's scope** — still need `henv`'s encard inequality
  `(face Sphi n).encard ≤ (face B n).encard` as an explicit binder here).

**Still owed** (exact target statements, both currently `sorry` pending lane-hsupp's
(A)/(B)):

```
theorem case_pos_ccw : 0 < det (-nℓ) n →
  (∑ j ∈ univ.erase i, max 0 (dot n (orientUp (h j) nℓ))) ≤ suppVal B n - dot n g

theorem case_pos_cw : 0 < det n (-nℓ) →
  (∑ j ∈ univ.erase i, max 0 (dot n (orientUp (h j) nℓ))) ≤ suppVal B n - dot n g
```

with the same binders as `hsuppZ_target` above, `n ∈ E B`, and `g` as in `hsuppZ_target`.
Once lane-hsupp lands `adjacent_shared_vertex` and `face_eq_segment`, `chain_ccw_scalar`/
`chain_cw_scalar` (`tmp/wip/PolyChainSum.lean`) instantiated at `T := B`, `ν₀ := -nℓ`
give the vector identity; the remaining work in *this* file is exactly the `ν_j`
injectivity + `gcd` bound sketched above (blueprint §2(E) paragraph 2), which does not
depend on (A)/(B) and could be started now as a separate lemma if useful.
-/

/-! ## §4. The per-generator normal `ν_j`: direction identity + membership

Independent of lane-hsupp's (A)/(B) — pure `ZonoEdgeGen.lean` algebra. `νGen h nℓ j :=
-genPerp' (orientUp (h j) nℓ)`, chosen so `dir (νGen h nℓ j) = primPart (orientUp (h j) nℓ)`
(same direction as the oriented generator, not its negation — `genPerp' v` itself points
the *other* way, `dir (genPerp' v) = -primPart v`, which is why the outer `-` is needed). -/

variable {m : ℕ}

/-- `dir (genPerp' v) = -primPart v`, for `v ≠ 0`. Proved by direct component computation:
`genPerp' v = primPart (dir v)` has components `((-v.2)/G, v.1/G)` for `G := gcd v.1 v.2`
(the gcd of `dir v`'s components equals `G` by negation/commutativity invariance of `gcd`,
and `(-v.2)/G = -(v.2/G)` since `G` divides `v.2` exactly), so
`dir (genPerp' v) = (-(v.1/G), -(v.2/G)) = -primPart v`. -/
theorem dir_genPerp' {v : ℤ × ℤ} (hv : v ≠ 0) :
    Nivat.LE2.dir (Nivat.LE2.genPerp' v) = - Nivat.LE2.primPart v := by
  set G : ℤ := (Int.gcd v.1 v.2 : ℤ) with hGdef
  have hGdvd2 : G ∣ v.2 := hGdef ▸ Int.gcd_dvd_right (a := v.1) (b := v.2)
  have hGne0 : G ≠ 0 := by
    intro hz
    rw [hGdef] at hz
    apply hv
    have hz' : Int.gcd v.1 v.2 = 0 := by exact_mod_cast hz
    rcases Int.gcd_eq_zero_iff.mp hz' with ⟨h1, h2⟩
    exact Prod.ext h1 h2
  have hGeq : (Int.gcd (-v.2) v.1 : ℤ) = G := by
    have h1 : Int.gcd (-v.2) v.1 = Int.gcd v.2 v.1 := by
      unfold Int.gcd; simp
    rw [h1, Int.gcd_comm]
  have hdivneg : (-v.2) / G = -(v.2 / G) := by
    obtain ⟨k, hk⟩ := hGdvd2
    have hk1 : v.2 / G = k := by rw [hk]; exact Int.mul_ediv_cancel_left k hGne0
    have hk2 : (-v.2) / G = -k := by
      rw [hk, show -(G * k) = G * (-k) by ring]
      exact Int.mul_ediv_cancel_left (-k) hGne0
    rw [hk1, hk2]
  show Nivat.LE2.dir (Nivat.LE2.primPart (Nivat.LE2.dir v)) = - Nivat.LE2.primPart v
  ext
  · show -(Nivat.LE2.primPart (Nivat.LE2.dir v)).2 = -(Nivat.LE2.primPart v).1
    show -(v.1 / (Int.gcd (-v.2) v.1 : ℤ)) = -(v.1 / G)
    rw [hGeq]
  · show (Nivat.LE2.primPart (Nivat.LE2.dir v)).1 = -(Nivat.LE2.primPart v).2
    show (-v.2) / (Int.gcd (-v.2) v.1 : ℤ) = -(v.2 / G)
    rw [hGeq]; exact hdivneg


/-! ## §5. The sum bound (blueprint §2(E), paragraph 2): the per-generator normal
`νGen`, its membership/orthogonality/numeric facts, and the assembled inequality
`∑_{j≠i, dot n uⱼ>0} dot n uⱼ ≤ ∑_{ν∈Arc(-nℓ)n} faceLen B ν · det ν n`. -/

/-- `dir` is odd. -/
theorem dir_neg (x : ℤ × ℤ) : Nivat.LE2.dir (-x) = - Nivat.LE2.dir x := by
  simp only [Nivat.LE2.dir]; ext <;> simp

/-- `primPart` is odd (trivially at `0`, by the gcd/ediv computation otherwise). -/
theorem primPart_neg (w : ℤ × ℤ) : Nivat.LE2.primPart (-w) = - Nivat.LE2.primPart w := by
  by_cases hw : w = 0
  · simp [hw, Nivat.LE2.primPart]
  set G : ℤ := (Int.gcd w.1 w.2 : ℤ) with hGdef
  have hGdvd1 : G ∣ w.1 := hGdef ▸ Int.gcd_dvd_left w.1 w.2
  have hGdvd2 : G ∣ w.2 := hGdef ▸ Int.gcd_dvd_right w.1 w.2
  have hGne0 : G ≠ 0 := by
    intro hz
    apply hw
    have hz' : Int.gcd w.1 w.2 = 0 := by rw [hGdef] at hz; exact_mod_cast hz
    rcases Int.gcd_eq_zero_iff.mp hz' with ⟨h1, h2⟩
    exact Prod.ext h1 h2
  have hGeq : (Int.gcd (-w).1 (-w).2 : ℤ) = G := by
    rw [hGdef]
    show (Int.gcd (-w.1) (-w.2) : ℤ) = (Int.gcd w.1 w.2 : ℤ)
    congr 1
    unfold Int.gcd; simp
  have hdiv1 : (-w).1 / G = -(w.1 / G) := by
    obtain ⟨k, hk⟩ := hGdvd1
    have hk1 : w.1 / G = k := by rw [hk]; exact Int.mul_ediv_cancel_left k hGne0
    have hk2 : (-w).1 / G = -k := by
      rw [Prod.fst_neg, hk, show -(G * k) = G * (-k) by ring]
      exact Int.mul_ediv_cancel_left (-k) hGne0
    rw [hk1, hk2]
  have hdiv2 : (-w).2 / G = -(w.2 / G) := by
    obtain ⟨k, hk⟩ := hGdvd2
    have hk1 : w.2 / G = k := by rw [hk]; exact Int.mul_ediv_cancel_left k hGne0
    have hk2 : (-w).2 / G = -k := by
      rw [Prod.snd_neg, hk, show -(G * k) = G * (-k) by ring]
      exact Int.mul_ediv_cancel_left (-k) hGne0
    rw [hk1, hk2]
  ext
  · show (-w).1 / (Int.gcd (-w).1 (-w).2 : ℤ) = -(w.1 / (Int.gcd w.1 w.2 : ℤ))
    rw [hGeq, ← hGdef]; exact hdiv1
  · show (-w).2 / (Int.gcd (-w).1 (-w).2 : ℤ) = -(w.2 / (Int.gcd w.1 w.2 : ℤ))
    rw [hGeq, ← hGdef]; exact hdiv2

/-- `genPerp'` is odd. -/
theorem genPerp'_neg (v : ℤ × ℤ) :
    Nivat.LE2.genPerp' (-v) = - Nivat.LE2.genPerp' v := by
  show Nivat.LE2.primPart (Nivat.LE2.dir (-v)) = - Nivat.LE2.primPart (Nivat.LE2.dir v)
  rw [dir_neg, primPart_neg]

/-- `Int.gcd` is invariant under negating both components. -/
theorem gcd_neg_both (w : ℤ × ℤ) : Int.gcd (-w).1 (-w).2 = Int.gcd w.1 w.2 := by
  show Int.gcd (-w.1) (-w.2) = Int.gcd w.1 w.2
  unfold Int.gcd; simp

theorem orientUp_eq_or_eq_neg (w nℓ : ℤ × ℤ) :
    Nivat.ColleReg.orientUp w nℓ = w ∨ Nivat.ColleReg.orientUp w nℓ = -w := by
  unfold Nivat.ColleReg.orientUp
  split_ifs
  · right; rfl
  · left; rfl

/-- The identity `⟪x, dir ν⟫ = det ν x` (blueprint §0, "约定"). -/
theorem dot_dir_eq_det (x ν : ℤ × ℤ) : Nivat.LE2.dot x (Nivat.LE2.dir ν) = det ν x := by
  simp only [Nivat.LE2.dot, Nivat.LE2.dir, det]; ring

/-- The per-generator edge normal for generator `j`, oriented so that
`dir (νGen j) = primPart (orientUp (h j) nℓ)`. -/
noncomputable def νGen (j : Fin d.toDecompData.m) : ℤ × ℤ :=
  - Nivat.LE2.genPerp' (Nivat.ColleReg.orientUp (d.toDecompData.h j) nℓ)

variable {d}

include hprim in
omit hprim in
theorem νGen_ne_zero {j : Fin d.toDecompData.m} (h_ne_j : d.toDecompData.h j ≠ 0) :
    νGen d (nℓ := nℓ) j ≠ 0 := by
  have hw_ne : Nivat.ColleReg.orientUp (d.toDecompData.h j) nℓ ≠ 0 := by
    rcases orientUp_eq_or_eq_neg (d.toDecompData.h j) nℓ with h | h <;> rw [h]
    · exact h_ne_j
    · exact neg_ne_zero.mpr h_ne_j
  have := (Nivat.LE2.genPerp'_prim hw_ne).ne_zero
  exact neg_ne_zero.mpr this

theorem dir_νGen {j : Fin d.toDecompData.m} (h_ne_j : d.toDecompData.h j ≠ 0) :
    Nivat.LE2.dir (νGen d (nℓ := nℓ) j) =
      Nivat.LE2.primPart (Nivat.ColleReg.orientUp (d.toDecompData.h j) nℓ) := by
  have hw_ne : Nivat.ColleReg.orientUp (d.toDecompData.h j) nℓ ≠ 0 := by
    rcases orientUp_eq_or_eq_neg (d.toDecompData.h j) nℓ with h | h <;> rw [h]
    · exact h_ne_j
    · exact neg_ne_zero.mpr h_ne_j
  unfold νGen
  rw [dir_neg, dir_genPerp' hw_ne, neg_neg]

theorem dot_neg_right (x y : ℤ × ℤ) : Nivat.LE2.dot x (-y) = - Nivat.LE2.dot x y := by
  rw [Nivat.LE2.dot_comm, Nivat.LE2.dot_neg_left, Nivat.LE2.dot_comm]

theorem dot_νGen_h {j : Fin d.toDecompData.m} :
    Nivat.LE2.dot (νGen d (nℓ := nℓ) j) (d.toDecompData.h j) = 0 := by
  set w := Nivat.ColleReg.orientUp (d.toDecompData.h j) nℓ with hwdef
  have hgp : Nivat.LE2.dot w (Nivat.LE2.genPerp' w) = 0 := by
    by_cases hw0 : w = 0
    · rw [hw0]; unfold Nivat.LE2.genPerp'; simp [Nivat.LE2.dot]
    · exact Nivat.LE2.dot_genPerp' hw0
  have hw : w = d.toDecompData.h j ∨ w = - d.toDecompData.h j := orientUp_eq_or_eq_neg _ _
  have hbase : Nivat.LE2.dot (d.toDecompData.h j)
      (Nivat.LE2.genPerp' (d.toDecompData.h j)) = 0 := by
    rcases hw with hw | hw
    · rw [← hw]; rw [Nivat.LE2.dot_comm]; rw [Nivat.LE2.dot_comm] at hgp; exact hgp
    · have hgp' : Nivat.LE2.dot (- d.toDecompData.h j)
          (Nivat.LE2.genPerp' (- d.toDecompData.h j)) = 0 := hw ▸ hgp
      rw [genPerp'_neg, Nivat.LE2.dot_neg_left, dot_neg_right] at hgp'
      have := hgp'
      simp only [neg_neg] at this
      exact this
  have hfinal : Nivat.LE2.dot (Nivat.LE2.genPerp' w) (d.toDecompData.h j) = 0 := by
    rcases hw with hw | hw
    · rw [hw, Nivat.LE2.dot_comm]; exact hbase
    · rw [hw, genPerp'_neg, Nivat.LE2.dot_neg_left, Nivat.LE2.dot_comm, hbase]; ring
  unfold νGen
  rw [← hwdef, Nivat.LE2.dot_neg_left, hfinal]
  ring


/-! ## §6. `νGen j ∈ E B`, via `zonoF univ h ⊆ Sφ`-style `Conv` transport. -/

include hEeq hprim hBfin hBne hlcB in
theorem νGen_mem_EB {j : Fin d.toDecompData.m} :
    νGen d (nℓ := nℓ) j ∈ Nivat.LE2.E B := by
  have hconv : Nivat.Conv (Nivat.LE2.zonoF Finset.univ d.toDecompData.h) =
      Nivat.Conv d.toDecompData.Sphi := by
    rw [d.toDecompData.Sphi_eq,
      Nivat.LE2.Conv_supp_prod_eq_Conv_zonoF Finset.univ d.toDecompData.h
        (fun k _ => d.toDecompData.h_ne k)]
  have hEzono : Nivat.LE2.E (↑(Nivat.LE2.zonoF Finset.univ d.toDecompData.h) : Set (ℤ × ℤ)) =
      Nivat.LE2.E (↑d.toDecompData.Sphi : Set (ℤ × ℤ)) := E_congr_of_Conv_eq hconv
  have hmem2 := Nivat.LE2.mem_E_zonoF d.toDecompData.h d.toDecompData.h_ne d.toDecompData.h_dir j
  have hw : Nivat.ColleReg.orientUp (d.toDecompData.h j) nℓ = d.toDecompData.h j ∨
      Nivat.ColleReg.orientUp (d.toDecompData.h j) nℓ = - d.toDecompData.h j :=
    orientUp_eq_or_eq_neg _ _
  have hzono : νGen d (nℓ := nℓ) j ∈
      Nivat.LE2.E (↑(Nivat.LE2.zonoF Finset.univ d.toDecompData.h) : Set (ℤ × ℤ)) := by
    unfold νGen
    rcases hw with hw | hw
    · rw [hw]; exact hmem2.2
    · rw [hw, genPerp'_neg, neg_neg]; exact hmem2.1
  rw [hEeq, ← hEzono]; exact hzono

/-! ## §7. The numeric identities: `dot n uⱼ = gcd(uⱼ) • det (νGen j) n`, etc. -/

/-- `w = G • primPart w` for `G := gcd w.1 w.2`, `w ≠ 0` (exact integer factorisation, not
just the existential form of `primPart_spec`). -/
theorem eq_gcd_smul_primPart {w : ℤ × ℤ} (hw : w ≠ 0) :
    w = ((Int.gcd w.1 w.2 : ℤ)) • Nivat.LE2.primPart w := by
  ext
  · show w.1 = (Int.gcd w.1 w.2 : ℤ) * (w.1 / (Int.gcd w.1 w.2 : ℤ))
    exact (Int.mul_ediv_cancel' (Int.gcd_dvd_left w.1 w.2)).symm
  · show w.2 = (Int.gcd w.1 w.2 : ℤ) * (w.2 / (Int.gcd w.1 w.2 : ℤ))
    exact (Int.mul_ediv_cancel' (Int.gcd_dvd_right w.1 w.2)).symm

theorem gcd_pos_of_ne_zero {w : ℤ × ℤ} (hw : w ≠ 0) : 0 < (Int.gcd w.1 w.2 : ℤ) := by
  have : Int.gcd w.1 w.2 ≠ 0 := by
    intro hz
    apply hw
    rcases Int.gcd_eq_zero_iff.mp hz with ⟨h1, h2⟩
    exact Prod.ext h1 h2
  exact_mod_cast Nat.pos_of_ne_zero this

/-- `dot x uⱼ = gcd(uⱼ) * det (νGen j) x`, for any `x`. -/
theorem dot_eq_gcd_mul_det {j : Fin d.toDecompData.m} (x : ℤ × ℤ)
    (hw_ne : Nivat.ColleReg.orientUp (d.toDecompData.h j) nℓ ≠ 0) :
    Nivat.LE2.dot x (Nivat.ColleReg.orientUp (d.toDecompData.h j) nℓ) =
      (Int.gcd (Nivat.ColleReg.orientUp (d.toDecompData.h j) nℓ).1
        (Nivat.ColleReg.orientUp (d.toDecompData.h j) nℓ).2 : ℤ) *
      det (νGen d (nℓ := nℓ) j) x := by
  have hdetx : det (νGen d (nℓ := nℓ) j) x =
      Nivat.LE2.dot x (Nivat.LE2.dir (νGen d (nℓ := nℓ) j)) :=
    (dot_dir_eq_det x (νGen d (nℓ := nℓ) j)).symm
  rw [hdetx, dir_νGen (h_ne_j := by
    rcases orientUp_eq_or_eq_neg (d.toDecompData.h j) nℓ with h | h
    · intro hc; apply hw_ne; rw [h]; exact hc
    · intro hc; apply hw_ne; rw [h, hc]; simp)]
  conv_lhs => rw [eq_gcd_smul_primPart hw_ne]
  rw [Nivat.LE2.dot_zsmul_right']


/-! ## §8. `gcd(uⱼ) = gcd(h j)`, `det(-a) b = det b a`, and the per-`j` `Arc`
membership + inequality. -/

theorem gcd_orientUp_eq {j : Fin d.toDecompData.m} :
    Int.gcd (Nivat.ColleReg.orientUp (d.toDecompData.h j) nℓ).1
      (Nivat.ColleReg.orientUp (d.toDecompData.h j) nℓ).2 =
      Int.gcd (d.toDecompData.h j).1 (d.toDecompData.h j).2 := by
  rcases orientUp_eq_or_eq_neg (d.toDecompData.h j) nℓ with hw | hw
  · rw [hw]
  · rw [hw]; exact gcd_neg_both (d.toDecompData.h j)

theorem det_neg_left_swap (a b : ℤ × ℤ) : det (-a) b = det b a := by
  simp only [det, Prod.fst_neg, Prod.snd_neg]; ring

include hprim hdoth in
theorem dotnl_hj_ne_zero {j : Fin d.toDecompData.m} (hij : j ≠ i) :
    Nivat.LE2.dot nℓ (d.toDecompData.h j) ≠ 0 := by
  intro hc
  exact hij (Nivat.LE2.at_most_one_orthogonal d.toDecompData.h d.toDecompData.h_dir nℓ
    hprim.ne_zero j i hc hdoth)

theorem dotnl_orientUp_pos {j : Fin d.toDecompData.m}
    (hne : Nivat.LE2.dot nℓ (d.toDecompData.h j) ≠ 0) :
    0 < Nivat.LE2.dot nℓ (Nivat.ColleReg.orientUp (d.toDecompData.h j) nℓ) := by
  unfold Nivat.ColleReg.orientUp
  by_cases hc : Nivat.LE2.dot nℓ (d.toDecompData.h j) < 0
  · rw [if_pos hc]
    have : Nivat.LE2.dot nℓ (-(d.toDecompData.h j)) = - Nivat.LE2.dot nℓ (d.toDecompData.h j) :=
      dot_neg_right nℓ (d.toDecompData.h j)
    rw [this]; omega
  · rw [if_neg hc]; omega

include hEeq hprim hdoth hBfin hBne hlcB in
/-- **`νGen j ∈ Arc (-nℓ) n`**, for `j ≠ i` and `dot n uⱼ > 0`. -/
theorem νGen_mem_Arc {n : ℤ × ℤ} {j : Fin d.toDecompData.m} (hij : j ≠ i)
    (hdotn : 0 < Nivat.LE2.dot n (Nivat.ColleReg.orientUp (d.toDecompData.h j) nℓ)) :
    νGen d (nℓ := nℓ) j ∈ Nivat.LE2.E B ∧
      0 < det (-nℓ) (νGen d (nℓ := nℓ) j) ∧ 0 < det (νGen d (nℓ := nℓ) j) n := by
  have hne0 : Nivat.LE2.dot nℓ (d.toDecompData.h j) ≠ 0 := dotnl_hj_ne_zero hprim hdoth hij
  have hnlpos : 0 < Nivat.LE2.dot nℓ (Nivat.ColleReg.orientUp (d.toDecompData.h j) nℓ) :=
    dotnl_orientUp_pos hne0
  have hw_ne : Nivat.ColleReg.orientUp (d.toDecompData.h j) nℓ ≠ 0 := by
    intro hc; rw [hc] at hnlpos; simp [Nivat.LE2.dot] at hnlpos
  have hgcdpos := gcd_pos_of_ne_zero hw_ne
  have heq_nl := dot_eq_gcd_mul_det (d := d) (nℓ := nℓ) (j := j) nℓ hw_ne
  have heq_n := dot_eq_gcd_mul_det (d := d) (nℓ := nℓ) (j := j) n hw_ne
  refine ⟨νGen_mem_EB hBfin hBne hlcB hprim hEeq, ?_, ?_⟩
  · rw [det_neg_left_swap]
    by_contra hcon
    push_neg at hcon
    have : Nivat.LE2.dot nℓ (Nivat.ColleReg.orientUp (d.toDecompData.h j) nℓ) ≤ 0 := by
      rw [heq_nl]; exact mul_nonpos_of_nonneg_of_nonpos hgcdpos.le hcon
    omega
  · by_contra hcon
    push_neg at hcon
    have : Nivat.LE2.dot n (Nivat.ColleReg.orientUp (d.toDecompData.h j) nℓ) ≤ 0 := by
      rw [heq_n]; exact mul_nonpos_of_nonneg_of_nonpos hgcdpos.le hcon
    omega

include hEeq hBfin hBne hlcB in
/-- **The per-`j` inequality**: `dot n uⱼ ≤ faceLen B (νGen j) * det (νGen j) n`. -/
theorem dot_le_faceLen_mul_det
    (hencard : ∀ n ∈ Nivat.LE2.E B,
      (Nivat.LE2.face (↑d.toDecompData.Sphi : Set (ℤ × ℤ)) n).encard ≤
        (Nivat.LE2.face B n).encard)
    {n : ℤ × ℤ} {j : Fin d.toDecompData.m}
    (hdotn : 0 < Nivat.LE2.dot n (Nivat.ColleReg.orientUp (d.toDecompData.h j) nℓ))
    (hw_ne : Nivat.ColleReg.orientUp (d.toDecompData.h j) nℓ ≠ 0)
    (hνEB : νGen d (nℓ := nℓ) j ∈ Nivat.LE2.E B) :
    Nivat.LE2.dot n (Nivat.ColleReg.orientUp (d.toDecompData.h j) nℓ) ≤
      (Nivat.PolyChain.faceLen B (νGen d (nℓ := nℓ) j) : ℤ) *
        det (νGen d (nℓ := nℓ) j) n := by
  have heq_n := dot_eq_gcd_mul_det (d := d) (nℓ := nℓ) (j := j) n hw_ne
  rw [gcd_orientUp_eq] at heq_n
  have hνne : νGen d (nℓ := nℓ) j ≠ 0 := νGen_ne_zero (d.toDecompData.h_ne j)
  have hgcdbound := Nivat.HsuppLengthBound.faceLen_ge_gcd d hBfin hBne hlcB hEeq hencard
    hνne dot_νGen_h hνEB
  have hdetpos : 0 < det (νGen d (nℓ := nℓ) j) n := by
    by_contra hcon
    push_neg at hcon
    have hgcdpos : 0 < (Int.gcd (d.toDecompData.h j).1 (d.toDecompData.h j).2 : ℤ) := by
      rw [← gcd_orientUp_eq]; exact gcd_pos_of_ne_zero hw_ne
    have : Nivat.LE2.dot n (Nivat.ColleReg.orientUp (d.toDecompData.h j) nℓ) ≤ 0 := by
      rw [heq_n]
      exact mul_nonpos_of_nonneg_of_nonpos hgcdpos.le hcon
    omega
  calc Nivat.LE2.dot n (Nivat.ColleReg.orientUp (d.toDecompData.h j) nℓ)
      = (Int.gcd (d.toDecompData.h j).1 (d.toDecompData.h j).2 : ℤ) *
          det (νGen d (nℓ := nℓ) j) n := heq_n
    _ ≤ (Nivat.PolyChain.faceLen B (νGen d (nℓ := nℓ) j) : ℤ) *
          det (νGen d (nℓ := nℓ) j) n :=
        mul_le_mul_of_nonneg_right hgcdbound hdetpos.le


/-! ## §9. Injectivity of `j ↦ νGen j`. -/

include hprim in
theorem νGen_inj {j k : Fin d.toDecompData.m}
    (h_ne_j : d.toDecompData.h j ≠ 0) (hjk : νGen d (nℓ := nℓ) j = νGen d (nℓ := nℓ) k) :
    j = k := by
  have hνne : νGen d (nℓ := nℓ) j ≠ 0 := νGen_ne_zero h_ne_j
  have hdk : Nivat.LE2.dot (νGen d (nℓ := nℓ) j) (d.toDecompData.h k) = 0 := by
    rw [hjk]; exact dot_νGen_h
  exact Nivat.LE2.at_most_one_orthogonal d.toDecompData.h d.toDecompData.h_dir
    (νGen d (nℓ := nℓ) j) hνne j k dot_νGen_h hdk

/-! ## §10. The core sum-bound lemma: `∑_{j∈S} dot n u_j ≤ ∑_{ν∈Arc} faceLen B ν * det ν n`. -/

include hEeq hprim hdoth hBfin hBne hlcB in
/-- The core Finset-level inequality driving both `case_pos_ccw` and `case_pos_cw`
(via the sign of `νGen j` resp. `-νGen j`). Stated here for the counter-clockwise
`Arc (-nℓ) n` (`ν₀ := -nℓ`). -/
theorem core_sum_bound
    (hencard : ∀ n ∈ Nivat.LE2.E B,
      (Nivat.LE2.face (↑d.toDecompData.Sphi : Set (ℤ × ℤ)) n).encard ≤
        (Nivat.LE2.face B n).encard)
    {n : ℤ × ℤ} :
    (∑ j ∈ Finset.univ.erase i,
        max 0 (Nivat.LE2.dot n (Nivat.ColleReg.orientUp (d.toDecompData.h j) nℓ))) ≤
      ∑ ν ∈ (Nivat.LE2.finite_E_of_finite hBfin).toFinset.filter
          (fun ν => 0 < det (-nℓ) ν ∧ 0 < det ν n),
        (Nivat.PolyChain.faceLen B ν : ℤ) * det ν n := by
  classical
  set S : Finset (Fin d.toDecompData.m) :=
    (Finset.univ.erase i).filter
      (fun j => 0 < Nivat.LE2.dot n (Nivat.ColleReg.orientUp (d.toDecompData.h j) nℓ)) with hSdef
  set Arc : Finset (ℤ × ℤ) :=
    (Nivat.LE2.finite_E_of_finite hBfin).toFinset.filter
      (fun ν => 0 < det (-nℓ) ν ∧ 0 < det ν n) with hArcdef
  have hstep1 : (∑ j ∈ Finset.univ.erase i,
      max 0 (Nivat.LE2.dot n (Nivat.ColleReg.orientUp (d.toDecompData.h j) nℓ))) =
      ∑ j ∈ S, Nivat.LE2.dot n (Nivat.ColleReg.orientUp (d.toDecompData.h j) nℓ) := by
    rw [hSdef, Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hc : 0 < Nivat.LE2.dot n (Nivat.ColleReg.orientUp (d.toDecompData.h j) nℓ)
    · rw [if_pos hc]; omega
    · rw [if_neg hc]; omega
  rw [hstep1]
  have hSij : ∀ j ∈ S, j ≠ i := fun j hj =>
    (Finset.mem_erase.mp (Finset.mem_filter.mp hj).1).1
  have hSdotpos : ∀ j ∈ S, 0 < Nivat.LE2.dot n (Nivat.ColleReg.orientUp (d.toDecompData.h j) nℓ) :=
    fun j hj => (Finset.mem_filter.mp hj).2
  have hw_ne_of : ∀ j ∈ S, Nivat.ColleReg.orientUp (d.toDecompData.h j) nℓ ≠ 0 := by
    intro j hj hc
    have := hSdotpos j hj
    rw [hc] at this
    simp [Nivat.LE2.dot] at this
  have hmapArc : ∀ j ∈ S, νGen d (nℓ := nℓ) j ∈ Arc := by
    intro j hj
    have h1 := νGen_mem_Arc (d := d) (nℓ := nℓ) (i := i) (hEeq := hEeq) (hprim := hprim)
      (hdoth := hdoth) (hBfin := hBfin) (hBne := hBne) (hlcB := hlcB)
      (hij := hSij j hj) (hdotn := hSdotpos j hj)
    rw [hArcdef, Finset.mem_filter, (Nivat.LE2.finite_E_of_finite hBfin).mem_toFinset]
    exact ⟨h1.1, h1.2.1, h1.2.2⟩
  have hinj : ∀ j1 ∈ S, ∀ j2 ∈ S, νGen d (nℓ := nℓ) j1 = νGen d (nℓ := nℓ) j2 → j1 = j2 := by
    intro j1 hj1 j2 _ heq
    exact νGen_inj hprim (d.toDecompData.h_ne j1) heq
  have hstep2 : ∑ j ∈ S, Nivat.LE2.dot n (Nivat.ColleReg.orientUp (d.toDecompData.h j) nℓ) ≤
      ∑ j ∈ S, (Nivat.PolyChain.faceLen B (νGen d (nℓ := nℓ) j) : ℤ) *
        det (νGen d (nℓ := nℓ) j) n := by
    apply Finset.sum_le_sum
    intro j hj
    have hνEB : νGen d (nℓ := nℓ) j ∈ Nivat.LE2.E B := by
      have h1 := νGen_mem_Arc (d := d) (nℓ := nℓ) (i := i) (hEeq := hEeq) (hprim := hprim)
        (hdoth := hdoth) (hBfin := hBfin) (hBne := hBne) (hlcB := hlcB)
        (hij := hSij j hj) (hdotn := hSdotpos j hj)
      exact h1.1
    exact dot_le_faceLen_mul_det (d := d) (nℓ := nℓ) (hBfin := hBfin) (hBne := hBne)
      (hlcB := hlcB) (hEeq := hEeq) hencard (hSdotpos j hj) (hw_ne_of j hj) hνEB
  have hstep3 : ∑ j ∈ S, (Nivat.PolyChain.faceLen B (νGen d (nℓ := nℓ) j) : ℤ) *
      det (νGen d (nℓ := nℓ) j) n =
      ∑ ν ∈ S.image (νGen d (nℓ := nℓ)), (Nivat.PolyChain.faceLen B ν : ℤ) * det ν n := by
    rw [Finset.sum_image hinj]
  have hsub : S.image (νGen d (nℓ := nℓ)) ⊆ Arc := by
    intro ν hν
    obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp hν
    rw [← heq]; exact hmapArc j hj
  have hnonneg : ∀ ν ∈ Arc, ν ∉ S.image (νGen d (nℓ := nℓ)) →
      0 ≤ (Nivat.PolyChain.faceLen B ν : ℤ) * det ν n := by
    intro ν hν _
    have hdetpos := (Finset.mem_filter.mp hν).2.2
    exact mul_nonneg (Int.natCast_nonneg _) hdetpos.le
  have hstep4 : ∑ ν ∈ S.image (νGen d (nℓ := nℓ)), (Nivat.PolyChain.faceLen B ν : ℤ) * det ν n ≤
      ∑ ν ∈ Arc, (Nivat.PolyChain.faceLen B ν : ℤ) * det ν n :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub hnonneg
  calc ∑ j ∈ S, Nivat.LE2.dot n (Nivat.ColleReg.orientUp (d.toDecompData.h j) nℓ)
      ≤ ∑ j ∈ S, (Nivat.PolyChain.faceLen B (νGen d (nℓ := nℓ) j) : ℤ) *
          det (νGen d (nℓ := nℓ) j) n := hstep2
    _ = ∑ ν ∈ S.image (νGen d (nℓ := nℓ)), (Nivat.PolyChain.faceLen B ν : ℤ) * det ν n := hstep3
    _ ≤ ∑ ν ∈ Arc, (Nivat.PolyChain.faceLen B ν : ℤ) * det ν n := hstep4


/-! ## §11. The `g ↔ faceStart/faceEnd B (-nℓ)` bridge.

Self-contained duplicate of `tmp/wip/hsupp_case_cw.lean`'s `g_eq_faceStart_or_faceEnd`
(that file cannot be imported here — `lake env lean` does not resolve `tmp/wip` module
paths). Identical statement, independent of ccw/cw. -/

include hEeq hnℓ_neg_mem in
theorem negnl_mem_EB : -nℓ ∈ Nivat.LE2.E B := by rw [hEeq]; exact hnℓ_neg_mem

theorem g_mem_face_negnl {g : ℤ × ℤ} (hgB : g ∈ B) (hgcz : Nivat.LE2.dot nℓ g = cz)
    (hgle : ∀ b ∈ B, cz ≤ Nivat.LE2.dot nℓ b) : g ∈ Nivat.LE2.face B (-nℓ) := by
  refine ⟨hgB, fun y hy => ?_⟩
  have h1 : cz ≤ Nivat.LE2.dot nℓ y := hgle y hy
  have h2 : Nivat.LE2.dot (-nℓ) y = - Nivat.LE2.dot nℓ y := Nivat.LE2.dot_neg_left nℓ y
  have h3 : Nivat.LE2.dot (-nℓ) g = - Nivat.LE2.dot nℓ g := Nivat.LE2.dot_neg_left nℓ g
  rw [h2, h3, hgcz]; omega

include hnu in
theorem dot_expNormal_dir_negnl :
    Nivat.LE2.dot (expNormal u' vl) (Nivat.LE2.dir (-nℓ)) = det u' vl := by
  have hnu' : nℓ.1 * u'.1 + nℓ.2 * u'.2 = -1 := hnu
  simp only [Nivat.LE2.dot, Nivat.LE2.dir, expNormal, Prod.fst_neg, Prod.snd_neg,
    Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  linear_combination (-(det u' vl)) * hnu'

include hBfin hlcB hEeq hnℓ_neg_mem hnu in
theorem g_eq_faceStart_or_faceEnd {g : ℤ × ℤ} (hgB : g ∈ B) (hgcz : Nivat.LE2.dot nℓ g = cz)
    (hgle : ∀ b ∈ B, cz ≤ Nivat.LE2.dot nℓ b)
    (hgmin : ∀ b ∈ B, Nivat.LE2.dot nℓ b = cz →
      Nivat.LE2.dot (expNormal u' vl) g ≤ Nivat.LE2.dot (expNormal u' vl) b) :
    (det u' vl = 1 → g = Nivat.PolyChain.faceStart B (-nℓ)) ∧
    (det u' vl = -1 → g = Nivat.PolyChain.faceStart B (-nℓ) +
      (Nivat.PolyChain.faceLen B (-nℓ) : ℤ) • Nivat.LE2.dir (-nℓ)) := by
  have hnmem : -nℓ ∈ Nivat.LE2.E B := negnl_mem_EB hEeq hnℓ_neg_mem
  have hgface : g ∈ Nivat.LE2.face B (-nℓ) := g_mem_face_negnl hgB hgcz hgle
  have hgmax : ∀ y ∈ B, Nivat.LE2.dot (-nℓ) y ≤ Nivat.LE2.dot (-nℓ) g := hgface.2
  have hseg := Nivat.PolyChain.face_eq_segment hlcB hBfin hnmem
  have hgface' := hgface
  rw [hseg] at hgface'
  obtain ⟨t0, ht0le, ht0eq⟩ := hgface'
  have hmemOfT : ∀ t : ℕ, t ≤ Nivat.PolyChain.faceLen B (-nℓ) →
      Nivat.PolyChain.faceStart B (-nℓ) + (t : ℤ) • Nivat.LE2.dir (-nℓ) ∈
        Nivat.LE2.face B (-nℓ) := by
    intro t htle; rw [hseg]; exact ⟨t, htle, rfl⟩
  have hlevel : ∀ t : ℕ, t ≤ Nivat.PolyChain.faceLen B (-nℓ) →
      Nivat.LE2.dot nℓ (Nivat.PolyChain.faceStart B (-nℓ) +
        (t : ℤ) • Nivat.LE2.dir (-nℓ)) = cz := by
    intro t htle
    have hmemt := hmemOfT t htle
    have hmemB : Nivat.PolyChain.faceStart B (-nℓ) + (t : ℤ) • Nivat.LE2.dir (-nℓ) ∈ B :=
      hmemt.1
    have h1 : Nivat.LE2.dot (-nℓ) g ≤ Nivat.LE2.dot (-nℓ)
        (Nivat.PolyChain.faceStart B (-nℓ) + (t : ℤ) • Nivat.LE2.dir (-nℓ)) :=
      hmemt.2 g hgB
    have h2 : Nivat.LE2.dot (-nℓ)
        (Nivat.PolyChain.faceStart B (-nℓ) + (t : ℤ) • Nivat.LE2.dir (-nℓ)) ≤
        Nivat.LE2.dot (-nℓ) g := hgmax _ hmemB
    have heq : Nivat.LE2.dot (-nℓ)
        (Nivat.PolyChain.faceStart B (-nℓ) + (t : ℤ) • Nivat.LE2.dir (-nℓ)) =
        Nivat.LE2.dot (-nℓ) g := le_antisymm h2 h1
    have e1 : Nivat.LE2.dot (-nℓ)
        (Nivat.PolyChain.faceStart B (-nℓ) + (t : ℤ) • Nivat.LE2.dir (-nℓ)) =
        - Nivat.LE2.dot nℓ
          (Nivat.PolyChain.faceStart B (-nℓ) + (t : ℤ) • Nivat.LE2.dir (-nℓ)) :=
      Nivat.LE2.dot_neg_left nℓ _
    have e2 : Nivat.LE2.dot (-nℓ) g = - Nivat.LE2.dot nℓ g := Nivat.LE2.dot_neg_left nℓ g
    rw [e1, e2] at heq
    omega
  have hexp : ∀ t : ℕ, t ≤ Nivat.PolyChain.faceLen B (-nℓ) →
      Nivat.LE2.dot (expNormal u' vl)
        (Nivat.PolyChain.faceStart B (-nℓ) + (t : ℤ) • Nivat.LE2.dir (-nℓ)) =
      Nivat.LE2.dot (expNormal u' vl) (Nivat.PolyChain.faceStart B (-nℓ)) +
        (t : ℤ) * det u' vl := by
    intro t _
    rw [Nivat.LE2.dot_add, Nivat.PolyChainSum.dot_zsmul_right, dot_expNormal_dir_negnl hnu]
  constructor
  · intro hbranch
    have hforall : ∀ t : ℕ, t ≤ Nivat.PolyChain.faceLen B (-nℓ) → (t0 : ℤ) ≤ (t : ℤ) := by
      intro t htle
      have hmemB : Nivat.PolyChain.faceStart B (-nℓ) + (t : ℤ) • Nivat.LE2.dir (-nℓ) ∈ B :=
        (hmemOfT t htle).1
      have hlevt := hlevel t htle
      have hmin := hgmin _ hmemB hlevt
      rw [ht0eq, hexp t0 ht0le, hexp t htle, hbranch] at hmin
      linarith
    have ht00 : t0 = 0 := by have := hforall 0 (Nat.zero_le _); omega
    rw [ht0eq, ht00]; simp
  · intro hbranch
    have hforall : ∀ t : ℕ, t ≤ Nivat.PolyChain.faceLen B (-nℓ) → (t : ℤ) ≤ (t0 : ℤ) := by
      intro t htle
      have hmemB : Nivat.PolyChain.faceStart B (-nℓ) + (t : ℤ) • Nivat.LE2.dir (-nℓ) ∈ B :=
        (hmemOfT t htle).1
      have hlevt := hlevel t htle
      have hmin := hgmin _ hmemB hlevt
      rw [ht0eq, hexp t0 ht0le, hexp t htle, hbranch] at hmin
      linarith
    have ht0max : t0 = Nivat.PolyChain.faceLen B (-nℓ) := by
      have := hforall (Nivat.PolyChain.faceLen B (-nℓ)) (le_refl _)
      omega
    rw [ht0eq, ht0max]

/-! ## §12. `case_pos_ccw`: assembly for the `0 < det (-nℓ) n` branch. -/

include hEeq hprim hdoth hBfin hBne hlcB hnℓ_neg_mem hnu hunimod in
/-- **`case_pos_ccw`**: `blueprint/LEAF-HSUPP.md` §2(E), second bullet. Wires
`chain_ccw_scalar_final` (`T := B`, `ν₀ := -nℓ`), the bridge `g_eq_faceStart_or_faceEnd`,
and `core_sum_bound` together. Both branches of `hunimod` reduce to the same core
inequality: the `det u' vl = 1` branch drops a nonnegative extra term, the
`det u' vl = -1` branch cancels it exactly (via `dot_dir_eq_det`). -/
theorem case_pos_ccw
    (hencard : ∀ n ∈ Nivat.LE2.E B,
      (Nivat.LE2.face (↑d.toDecompData.Sphi : Set (ℤ × ℤ)) n).encard ≤
        (Nivat.LE2.face B n).encard)
    {n : ℤ × ℤ} (hnB : n ∈ Nivat.LE2.E B) (hdotpos : 0 < det (-nℓ) n)
    {g : ℤ × ℤ} (hgB : g ∈ B) (hgcz : Nivat.LE2.dot nℓ g = cz)
    (hgle : ∀ b ∈ B, cz ≤ Nivat.LE2.dot nℓ b)
    (hgmin : ∀ b ∈ B, Nivat.LE2.dot nℓ b = cz →
      Nivat.LE2.dot (expNormal u' vl) g ≤ Nivat.LE2.dot (expNormal u' vl) b) :
    (∑ j ∈ Finset.univ.erase i,
        max 0 (Nivat.LE2.dot n (Nivat.ColleReg.orientUp (d.toDecompData.h j) nℓ))) ≤
      Nivat.LE2.suppVal B n - Nivat.LE2.dot n g := by
  have hnmem : -nℓ ∈ Nivat.LE2.E B := negnl_mem_EB hEeq hnℓ_neg_mem
  have hchain := Nivat.PolyChainSum.chain_ccw_scalar_final hBfin hlcB hnmem hnB hdotpos
  have hcore := core_sum_bound hBfin hBne hlcB hprim hdoth hEeq hencard (n := n)
  have hbridge := g_eq_faceStart_or_faceEnd hBfin hlcB hnu hEeq hnℓ_neg_mem hgB hgcz hgle hgmin
  rcases hunimod with h1 | h1
  · have hgeq := hbridge.1 h1
    rw [hgeq]
    have hterm_nonneg : 0 ≤ (Nivat.PolyChain.faceLen B (-nℓ) : ℤ) * det (-nℓ) n :=
      mul_nonneg (Int.natCast_nonneg _) hdotpos.le
    linarith [hchain, hcore, hterm_nonneg]
  · have hgeq := hbridge.2 h1
    rw [hgeq]
    have hdotg : Nivat.LE2.dot n
        (Nivat.PolyChain.faceStart B (-nℓ) + (Nivat.PolyChain.faceLen B (-nℓ) : ℤ) •
          Nivat.LE2.dir (-nℓ)) =
        Nivat.LE2.dot n (Nivat.PolyChain.faceStart B (-nℓ)) +
          (Nivat.PolyChain.faceLen B (-nℓ) : ℤ) * det (-nℓ) n := by
      rw [Nivat.LE2.dot_add, Nivat.PolyChainSum.dot_zsmul_right, dot_dir_eq_det]
    rw [hdotg]
    linarith [hchain, hcore]
#print axioms Nivat.HsuppAssemble.case_pos_ccw

/-! ## §13. `case_eq_nℓ`: assembly for the `n = nℓ` boundary branch (`det (-nℓ) nℓ = 0`).

`blueprint/LEAF-HSUPP.md` §2(E), fourth bullet. `chain_ccw_scalar_final` cannot be invoked
at `n := nℓ` directly (its `hpos` is strict, and `det (-nℓ) nℓ = 0` exactly). The identity
`det ν nℓ = det (-nℓ) ν` (`det_neg_left_swap nℓ ν`, since `nℓ` and `-nℓ` are antipodal)
collapses `core_sum_bound`'s two-condition filter `Arc := {ν ∈ E B | 0 < det (-nℓ) ν ∧
0 < det ν nℓ}` into the single condition `0 < det (-nℓ) ν`. When `Arc` is empty the bound
is the trivial `dot nℓ g ≤ suppVal B nℓ` (`le_suppVal`, from `g ∈ B`). When `Arc` is
nonempty, its `det`-maximal element `ν'` (`exists_max_det`, `e := -nℓ`) is fan-adjacent to
`nℓ` (`adjacent_shared_vertex`, using `0 < det ν' nℓ` from `ν' ∈ Arc` and the same
collapse to show `Arc \ {ν'} = {ν ∈ E B | 0 < det (-nℓ) ν ∧ 0 < det ν ν'}`), one step short
of `chain_ccw_scalar_final` applied at `n := ν'`; adding that step gives the exact
identity `suppVal B nℓ - dot nℓ g = ∑_{ν ∈ Arc} faceLen B ν * det ν nℓ`, matching
`core_sum_bound`. -/

include hEeq hprim hdoth hBfin hBne hlcB hnℓ_neg_mem hnu hunimod in
theorem case_eq_nℓ
    (hencard : ∀ n ∈ Nivat.LE2.E B,
      (Nivat.LE2.face (↑d.toDecompData.Sphi : Set (ℤ × ℤ)) n).encard ≤
        (Nivat.LE2.face B n).encard)
    (hnB : nℓ ∈ Nivat.LE2.E B)
    {g : ℤ × ℤ} (hgB : g ∈ B) (hgcz : Nivat.LE2.dot nℓ g = cz)
    (hgle : ∀ b ∈ B, cz ≤ Nivat.LE2.dot nℓ b)
    (hgmin : ∀ b ∈ B, Nivat.LE2.dot nℓ b = cz →
      Nivat.LE2.dot (expNormal u' vl) g ≤ Nivat.LE2.dot (expNormal u' vl) b) :
    (∑ j ∈ Finset.univ.erase i,
        max 0 (Nivat.LE2.dot nℓ (Nivat.ColleReg.orientUp (d.toDecompData.h j) nℓ))) ≤
      Nivat.LE2.suppVal B nℓ - Nivat.LE2.dot nℓ g := by
  classical
  have hnmem : -nℓ ∈ Nivat.LE2.E B := negnl_mem_EB hEeq hnℓ_neg_mem
  have hcore := core_sum_bound hBfin hBne hlcB hprim hdoth hEeq hencard (n := nℓ)
  have hidnty : ∀ ν : ℤ × ℤ, det ν nℓ = det (-nℓ) ν := fun ν => (det_neg_left_swap nℓ ν).symm
  have hzero : det (-nℓ) nℓ = 0 := by rw [det_neg_left_swap]; exact det_self nℓ
  have hArcEq : (Nivat.LE2.finite_E_of_finite hBfin).toFinset.filter
      (fun ν => 0 < det (-nℓ) ν ∧ 0 < det ν nℓ) =
      (Nivat.LE2.finite_E_of_finite hBfin).toFinset.filter (fun ν => 0 < det (-nℓ) ν) := by
    apply Finset.filter_congr
    intro ν _
    rw [hidnty ν]; tauto
  set Arc := (Nivat.LE2.finite_E_of_finite hBfin).toFinset.filter
      (fun ν => 0 < det (-nℓ) ν) with hArcdef
  rw [hArcEq] at hcore
  have hbridge := g_eq_faceStart_or_faceEnd hBfin hlcB hnu hEeq hnℓ_neg_mem hgB hgcz hgle hgmin
  have hgeq0 : Nivat.LE2.dot nℓ g = Nivat.LE2.dot nℓ (Nivat.PolyChain.faceStart B (-nℓ)) := by
    rcases hunimod with h1 | h1
    · rw [hbridge.1 h1]
    · rw [hbridge.2 h1, Nivat.LE2.dot_add, Nivat.PolyChainSum.dot_zsmul_right,
        dot_dir_eq_det, hzero, mul_zero, add_zero]
  by_cases hArcNe : Arc.Nonempty
  · obtain ⟨ν', hν'Arc, hν'max⟩ := Nivat.PolyChainSum.exists_max_det (S := Arc) (e := -nℓ)
      (neg_ne_zero.mpr hprim.ne_zero) (fun ν hν => (Finset.mem_filter.mp hν).2) hArcNe
    have hν'EB' : ν' ∈ (Nivat.LE2.finite_E_of_finite hBfin).toFinset :=
      (Finset.mem_filter.mp hν'Arc).1
    have hν'EB : ν' ∈ Nivat.LE2.E B := (Nivat.LE2.finite_E_of_finite hBfin).mem_toFinset.mp hν'EB'
    have hν'pos : 0 < det (-nℓ) ν' := (Finset.mem_filter.mp hν'Arc).2
    have hposnℓ : 0 < det ν' nℓ := by rw [hidnty]; exact hν'pos
    have hadj : ∀ μ ∈ Nivat.LE2.E B, ¬ (0 < det ν' μ ∧ 0 < det μ nℓ) := by
      rintro μ hμ ⟨hμ1, hμ2⟩
      have hμArc : μ ∈ Arc := by
        rw [hArcdef, Finset.mem_filter, (Nivat.LE2.finite_E_of_finite hBfin).mem_toFinset]
        exact ⟨hμ, by rw [← hidnty]; exact hμ2⟩
      exact hν'max μ hμArc hμ1
    have hchain := Nivat.PolyChainSum.chain_ccw_final hBfin hlcB hnmem hν'EB hν'pos
    have hshare := Nivat.PolyChain.adjacent_shared_vertex hBfin hlcB hν'EB hnB hposnℓ hadj
    have hArc'eq : (Nivat.LE2.finite_E_of_finite hBfin).toFinset.filter
        (fun ν => 0 < det (-nℓ) ν ∧ 0 < det ν ν') = Arc.erase ν' := by
      apply Finset.ext
      intro ν
      rw [Finset.mem_filter, Finset.mem_erase, hArcdef, Finset.mem_filter]
      constructor
      · rintro ⟨hνE, hν1, hν2⟩
        refine ⟨fun hcon => ?_, hνE, hν1⟩
        rw [hcon] at hν2
        rw [det_self] at hν2
        exact absurd hν2 (lt_irrefl 0)
      · rintro ⟨hne, hνE, hν1⟩
        refine ⟨hνE, hν1, ?_⟩
        have hνEB : ν ∈ Nivat.LE2.E B := (Nivat.LE2.finite_E_of_finite hBfin).mem_toFinset.mp hνE
        have hνArc : ν ∈ Arc := by rw [hArcdef, Finset.mem_filter]; exact ⟨hνE, hν1⟩
        have hle : det ν' ν ≤ 0 := by
          by_contra hcon; push_neg at hcon; exact hν'max ν hνArc hcon
        have hne0 : det ν' ν ≠ 0 := by
          intro hz
          have hprimν' : Nivat.LE2.Prim ν' := (Nivat.LE2.mem_E_iff.mp hν'EB).1
          have hprimν : Nivat.LE2.Prim ν := (Nivat.LE2.mem_E_iff.mp hνEB).1
          rcases Nivat.LE2.eq_or_neg_of_prim_of_det_eq_zero hprimν' hprimν hz with h | h
          · exact hne h
          · rw [h] at hν1
            have : det (-nℓ) (-ν') = - det (-nℓ) ν' := by
              simp only [det, Prod.fst_neg, Prod.snd_neg]; ring
            rw [this] at hν1
            linarith
        have hltz : det ν' ν < 0 := lt_of_le_of_ne hle hne0
        have hanti : det ν' ν = - det ν ν' := by simp only [det]; ring
        rw [hanti] at hltz
        linarith
    rw [hArc'eq] at hchain
    have hArcsum : ∀ f : ℤ × ℤ → ℤ × ℤ,
        (∑ ν ∈ Arc.erase ν', f ν) + f ν' = ∑ ν ∈ Arc, f ν :=
      fun f => Finset.sum_erase_add Arc f hν'Arc
    have hvec : Nivat.PolyChain.faceStart B nℓ - Nivat.PolyChain.faceStart B (-nℓ) =
        (Nivat.PolyChain.faceLen B (-nℓ) : ℤ) • Nivat.LE2.dir (-nℓ) +
          ∑ ν ∈ Arc, (Nivat.PolyChain.faceLen B ν : ℤ) • Nivat.LE2.dir ν := by
      have e1 : Nivat.PolyChain.faceStart B nℓ - Nivat.PolyChain.faceStart B (-nℓ) =
          (Nivat.PolyChain.faceStart B ν' - Nivat.PolyChain.faceStart B (-nℓ)) +
            (Nivat.PolyChain.faceLen B ν' : ℤ) • Nivat.LE2.dir ν' := by
        rw [← hshare]; abel
      rw [e1, hchain, ← hArcsum (fun ν => (Nivat.PolyChain.faceLen B ν : ℤ) • Nivat.LE2.dir ν)]
      abel
    have hsv : Nivat.LE2.suppVal B nℓ = Nivat.LE2.dot nℓ (Nivat.PolyChain.faceStart B nℓ) :=
      Nivat.PolyChainSum.suppVal_faceStart (Nivat.PolyChainSum.hseg_real hBfin hlcB) hnB
    have hdotvec : Nivat.LE2.dot nℓ (Nivat.PolyChain.faceStart B nℓ) -
        Nivat.LE2.dot nℓ (Nivat.PolyChain.faceStart B (-nℓ)) =
        (Nivat.PolyChain.faceLen B (-nℓ) : ℤ) * det (-nℓ) nℓ +
          ∑ ν ∈ Arc, (Nivat.PolyChain.faceLen B ν : ℤ) * det ν nℓ := by
      have h1 : Nivat.LE2.dot nℓ (Nivat.PolyChain.faceStart B nℓ -
          Nivat.PolyChain.faceStart B (-nℓ)) =
          Nivat.LE2.dot nℓ ((Nivat.PolyChain.faceLen B (-nℓ) : ℤ) • Nivat.LE2.dir (-nℓ) +
            ∑ ν ∈ Arc, (Nivat.PolyChain.faceLen B ν : ℤ) • Nivat.LE2.dir ν) := by rw [hvec]
      rw [Nivat.LE2.dot_sub] at h1
      rw [Nivat.LE2.dot_add, Nivat.PolyChainSum.dot_zsmul_right, Nivat.PolyChainSum.dot_sum] at h1
      rw [h1]
      congr 1
      · rw [dot_dir_eq_det]
      · exact Finset.sum_congr rfl fun ν _ => by
          rw [Nivat.PolyChainSum.dot_zsmul_right, dot_dir_eq_det]
    rw [hzero, mul_zero, zero_add] at hdotvec
    rw [hsv, hgeq0, hdotvec]
    linarith [hcore]
  · have hArcEmpty : Arc = ∅ := Finset.not_nonempty_iff_eq_empty.mp hArcNe
    rw [hArcEmpty, Finset.sum_empty] at hcore
    have htrivial : Nivat.LE2.dot nℓ g ≤ Nivat.LE2.suppVal B nℓ :=
      Nivat.LE2.le_suppVal hBfin hBne hgB
    linarith [hcore]
#print axioms Nivat.HsuppAssemble.case_eq_nℓ

/-! ## §14. Final assembly: `hsuppZ_target_proof`. -/

include hEeq hprim hperp hdoth hBfin hBne hlcB hnℓ_neg_mem hnu hunimod in
/-- **`hsuppZ_target_proof`**: assembles `case_neg_nℓ`, `case_pos_ccw`,
`Nivat.HsuppCaseCW.case_pos_cw`, and `case_eq_nℓ` into a full proof of `hsuppZ_target`
(§2(E)'s four bullets, case-split on the sign of `det (-nℓ) n` and, in the zero case, on
`n = nℓ` vs. `n = -nℓ` via `Nivat.LE2.eq_or_neg_of_prim_of_det_eq_zero`). -/
theorem hsuppZ_target_proof
    (hencard : ∀ n ∈ Nivat.LE2.E B,
      (Nivat.LE2.face (↑d.toDecompData.Sphi : Set (ℤ × ℤ)) n).encard ≤
        (Nivat.LE2.face B n).encard)
    (hcz : ∀ b ∈ B, cz ≤ Nivat.LE2.dot nℓ b) :
    hsuppZ_target d (B := B) (i := i) (vl := vl) (nℓ := nℓ) (u' := u') (cz := cz) := by
  classical
  unfold hsuppZ_target
  intro g hgB hgcz hgmin n hn
  rcases lt_trichotomy (det (-nℓ) n) 0 with hneg | hzero | hpos
  · exact Nivat.HsuppCaseCW.case_pos_cw (d := d) (hprim := hprim) (hdoth := hdoth)
      (hBfin := hBfin) (hlcB := hlcB) (hEeqD := hEeq) (henv := hencard) (hEeq := hEeq)
      (hnℓ_neg_mem := hnℓ_neg_mem) (hnu := hnu) (hunimod := hunimod) (hn := hn)
      (hpos := by
        have : det n (-nℓ) = - det (-nℓ) n := by simp only [det]; ring
        omega)
      (hgB := hgB) (hgcz := hgcz) (hgle := hcz)
      (hgmin := hgmin)
  · have hprimn : Nivat.LE2.Prim n := (Nivat.LE2.mem_E_iff.mp hn).1
    rcases Nivat.LE2.eq_or_neg_of_prim_of_det_eq_zero hprim.neg hprimn hzero with h | h
    · rw [h]
      exact case_neg_nℓ d hBfin hBne
        (fun g' hg'B hg'cz hg'min => trivial) g hgcz hgmin hgB hcz
    · rw [h, neg_neg]
      exact case_eq_nℓ hBfin hBne hlcB hprim hdoth hunimod hnu hEeq hnℓ_neg_mem hencard
        (by rw [h, neg_neg] at hn; exact hn) hgB hgcz hcz hgmin
  · exact case_pos_ccw hBfin hBne hlcB hprim hdoth hunimod hnu hEeq hnℓ_neg_mem hencard
      hn hpos hgB hgcz hcz hgmin
#print axioms Nivat.HsuppAssemble.hsuppZ_target_proof

end Nivat.HsuppAssemble
#print axioms Nivat.HsuppAssemble.case_neg_nℓ
#print axioms Nivat.HsuppAssemble.dir_genPerp'
#print axioms Nivat.HsuppAssemble.νGen_inj
#print axioms Nivat.HsuppAssemble.core_sum_bound
#print axioms Nivat.HsuppAssemble.negnl_mem_EB
#print axioms Nivat.HsuppAssemble.g_mem_face_negnl
#print axioms Nivat.HsuppAssemble.dot_expNormal_dir_negnl
#print axioms Nivat.HsuppAssemble.g_eq_faceStart_or_faceEnd
#print axioms Nivat.HsuppAssemble.case_pos_ccw
