/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.ItemII

/-!
# `ChainDataGeom.ofParts` with its `ℓ_ι` side discharged by exhaustion

Lane Aenvfix, 2026-09-19.  Wiring only, no new mathematics.  Amink's
`Colle35.ell_side_of_exhausts` (`ItemII.lean` §5) produces, from `Exhausts A nℓ cz` +
`rec_vJ` + the pair's `¬DP`, exactly the four `ℓ_ι`-side obligations of
`ChainDataGeom.ofParts` (`cL` / `ahat_halfPlane_L` / `ahat_attained_L` / `nfp_L`).  It had zero
consumers; this file is the consumer.

Why a separate file: `ItemII.lean` imports `ChainAssemble.lean` (for `hatOf` and the binder
shapes), so `ChainAssemble` cannot import `ItemII` back.  The wiring therefore lives one module
downstream of both.  `ofParts` itself is untouched.

PROTOCOL §27: the claim "the four conjuncts are the four slots" is not asserted in prose —
`ofPartsExhausts` feeds each conjunct of `ell_side_of_exhausts` into the corresponding slot of
`ofParts` and the elaborator certifies the match.  Every other binder of `ofParts` is passed
through verbatim; the four `ℓ_ι` binders are replaced by
`nℓ cz hprim hperp hvl hdet hpvJ hexh hnotDP` (nine binders, all already exported by
`exists_preamble_pair` / `exists_faceBlock` except `hexh`, which is the producer's item (ii)
through `exhausts_of_itemII`).

**2026-09-19 swap (team-lead ruling, option (c)).**  `rec_vJ` is no longer a binder here;
`hEnv : Env = EnvOf ↑S` is.  Measured (`ChainAssemble.latticeConvex_iUnion_hatOf`,
`tmp/aenvfix_conv_of_env.lean`): `ofParts`'s 25 binders leave `Env` unconstrained, so the
lattice-convexity of `Â_∞` that `rec_vJ_of_bottom` (`ItemII.lean` §8) needs is **not** derivable
from them — the honest bookkeeping is a **swap** (25 → 25), not a deletion.  `hEnv` is the
conjunct `exists_chainData` already exports, so it is free at the call site.  `ofParts` itself
keeps `rec_vJ` as a binder and is untouched.
-/

set_option autoImplicit false

namespace Nivat.Colle35

open Nivat Nivat.LE2 Nivat.MaxEnv Nivat.ChainAsm

variable {α : Type*}

/-- **`ofParts` with the `ℓ_ι` side supplied by `ell_side_of_exhausts`.**  Same binders as
`ChainDataGeom.ofParts` up to `dot_nJ_p`; then `hEnv : Env = EnvOf ↑S` **in place of** `rec_vJ`
(2026-09-19 swap, 25 → 25: `rec_vJ` is derived from `bottom`/`hswept`/`hEnv`); then the
exhaustion data instead of `cL / ahat_halfPlane_L / ahat_attained_L / nfp_L`. -/
noncomputable def ChainDataGeom.ofPartsExhausts
    (η xper : Config α) (vl p : ℤ × ℤ) (S : Finset (ℤ × ℤ)) (gen : ℤ × ℤ)
    (Env : Set (ℤ × ℤ) → Prop) (B A : ℕ → Set (ℤ × ℤ)) (u : ℕ → ℤ × ℤ) (kk : ℕ → ℕ)
    (envShift : ∀ (v : ℤ × ℤ) (T : Set (ℤ × ℤ)), Env T → Env {z | z + v ∈ T})
    (envB : ∀ i, Env (B i))
    (maxA : ∀ i, IsMaxEnvIn Env (canonA η xper vl B u i) (A i))
    (subBA : ∀ i, B i ⊆ A i) (subAB : ∀ i, A i ⊆ B (i + 1))
    (AhatMono : ∀ i j, i ≤ j → hatOf A kk vl i ⊆ hatOf A kk vl j)
    (vJ1 nJ : ℤ × ℤ) (cJ : ℤ)
    (hsweep : dot nJ vJ1 < 0)
    (hfin : ∀ i, (hatOf A kk vl i).Finite)
    (hhp : ∀ i, hatOf A kk vl i ⊆ halfPlaneGE nJ cJ)
    (hswept : SweptClosed (⋃ i, hatOf A kk vl i) vJ1 nJ cJ)
    (ahat_nonempty : (⋃ i, hatOf A kk vl i).Nonempty)
    (shellSubStrip : ∀ ε i₀ : ℕ, 0 < ε →
      (∀ i, i₀ ≤ i → Env (shell (hatOf A kk vl i) vJ1 nJ cJ ε)) →
      ∀ i, i₀ ≤ i → shell (hatOf A kk vl i) vJ1 nJ cJ ε ⊆
        {z | z + (kk i : ℤ) • vl ∈ halfStrip (B i) vl})
    (escape : ∀ (i ε : ℕ), 0 < ε → ∃ g ∈ hatOf A kk vl i, ∃ t : ℕ,
      g + (t : ℤ) • vJ1 ∉ hatOf A kk vl i ∧ cJ - (ε : ℤ) ≤ dot nJ (g + (t : ℤ) • vJ1))
    (shellEnv : ∃ ε i₀, 0 < ε ∧ ∀ i, i₀ ≤ i → Env (shell (hatOf A kk vl i) vJ1 nJ cJ ε))
    (fillCover : ∀ i i₀ ε, i₀ ≤ i → shell (hatOf A kk vl i) vJ1 nJ cJ ε ⊆
      ⋃ n, genFill S gen (hatOf A kk vl i ∪ shell (hatOf A kk vl i₀) vJ1 nJ cJ ε) n)
    (vJ : ℤ × ℤ) (F : FaceBlock S nJ vJ)
    -- **The generating point is the `v_J`-forward end of the face** (2026-09-19, team-lead
    -- ruling on Amink's finding).  Kernel receipt (`tmp/aenvfix_fillCover_wit.lean`, and
    -- `FillCoverWitness.lean` once landed): on `ShellSweep`'s data at `(i, i₀, ε) = (2, 1, 1)`
    -- the `:518` `fillCover` instance holds for `gen = (1,0) = a'` (`lex'`, `v_J`-maximal) and
    -- fails for `gen = (0,0) = a`.  Reading, not kernel fact: `bottom` puts the new sites of
    -- `Â_∞^{(ε+1)}` on a `+v_J` half-line, so only the `+v_J` endpoint can generate them.
    -- Free at the producer given `IsGeneratingSet` (`FaceBlock.generatesAt_a'` below).
    (gen_eq : gen = F.a')
    (vJ_prim : Primitive vJ) (nJ_prim : Primitive nJ)
    (bottom : ∀ ε : ℕ, ∃ (z₀ : ℤ × ℤ) (L : ℤ),
      dot nJ z₀ = cJ - (ε : ℤ) - 1 ∧
      (∀ k : ℤ, L ≤ k → z₀ + k • vJ ∈ reachSet (⋃ i, hatOf A kk vl i) vJ1) ∧
      (∀ b ∈ S, ∀ k : ℤ, L ≤ k →
        z₀ + k • vJ + (b - F.a) ∈ reachSet (⋃ i, hatOf A kk vl i) vJ1) ∧
      (∀ z ∈ shell (⋃ i, hatOf A kk vl i) vJ1 nJ cJ (ε + 1),
        z ∈ shell (⋃ i, hatOf A kk vl i) vJ1 nJ cJ ε ∨ ∃ k : ℤ, L ≤ k ∧ z = z₀ + k • vJ))
    (rec_p : ∀ g ∈ ⋃ i, hatOf A kk vl i, g + p ∈ ⋃ i, hatOf A kk vl i)
    (dot_nJ_p : dot nJ p ≠ 0)
    -- **Swapped 2026-09-19 (team-lead ruling, option (c)): `rec_vJ` out, the `Env` pin in.**
    -- `rec_vJ` is derived below from `bottom` + `hswept` + lattice-convexity of `Â_∞`
    -- (`rec_vJ_of_bottom`, `ItemII.lean` §8), and the convexity from `hEnv` + `maxA` + `hfin` +
    -- `AhatMono` (`latticeConvex_iUnion_hatOf`, `ChainAssemble.lean`).  `ofParts` itself is
    -- unchanged (25 binders); this constructor still takes 25 — a swap, not a deletion.
    (hEnv : Env = EnvOf (↑S : Set (ℤ × ℤ)))
    (nℓ : ℤ × ℤ) (cz : ℤ) (hprim : Primitive nℓ) (hperp : dot nℓ vl = 0)
    (hvl : vl ≠ 0) (hdet : det p vl = 0) (hpvJ : det p vJ ≠ 0)
    (hexh : Exhausts A nℓ cz)
    (hnotDP : ¬ ∃ h h' : ℤ × ℤ, det h h' ≠ 0 ∧
      PeriodicOnWith xper {z | cz ≤ dot nℓ z} h ∧ PeriodicOnWith xper {z | cz ≤ dot nℓ z} h') :
    ChainDataGeom η xper vl p S gen :=
  let rec_vJ' : ∀ g ∈ ⋃ i, hatOf A kk vl i, g + vJ ∈ ⋃ i, hatOf A kk vl i :=
    rec_vJ_of_bottom (latticeConvex_iUnion_hatOf η xper vl S Env B A u kk hEnv maxA hfin AhatMono)
      hsweep (fun _ hg => Set.iUnion_subset hhp hg) hswept F.dot_nJ_vJ bottom
  let side := ell_side_of_exhausts (xper := xper) (Ahat := hatOf A kk vl) hvl hdet hpvJ hprim
    hperp (fun i => hatOf_eq i) hexh rec_vJ' hnotDP
  ChainDataGeom.ofParts η xper vl p S gen Env B A u kk envShift envB maxA subBA subAB AhatMono vJ1 nJ cJ hsweep hfin hhp hswept ahat_nonempty shellSubStrip escape shellEnv fillCover vJ F gen_eq vJ_prim nJ_prim bottom rec_p dot_nJ_p rec_vJ'
    side.choose_spec.choose
    side.choose_spec.choose_spec.2.2.2.1
    side.choose_spec.choose_spec.2.2.2.2.1
    side.choose_spec.choose_spec.2.2.2.2.2

/-- The `ℓ_ι` level of the assembled bundle is the one `ell_side_of_exhausts` produced:
`cL = k * cz` for the `k > 0` with `n_ℓ = k • nℓ`.  Recorded so the choice is visible. -/
theorem ChainDataGeom.ofPartsExhausts_cL_spec
    (η xper : Config α) (vl p : ℤ × ℤ) (S : Finset (ℤ × ℤ)) (gen : ℤ × ℤ)
    (Env : Set (ℤ × ℤ) → Prop) (B A : ℕ → Set (ℤ × ℤ)) (u : ℕ → ℤ × ℤ) (kk : ℕ → ℕ)
    (envShift : ∀ (v : ℤ × ℤ) (T : Set (ℤ × ℤ)), Env T → Env {z | z + v ∈ T})
    (envB : ∀ i, Env (B i))
    (maxA : ∀ i, IsMaxEnvIn Env (canonA η xper vl B u i) (A i))
    (subBA : ∀ i, B i ⊆ A i) (subAB : ∀ i, A i ⊆ B (i + 1))
    (AhatMono : ∀ i j, i ≤ j → hatOf A kk vl i ⊆ hatOf A kk vl j)
    (vJ1 nJ : ℤ × ℤ) (cJ : ℤ)
    (hsweep : dot nJ vJ1 < 0)
    (hfin : ∀ i, (hatOf A kk vl i).Finite)
    (hhp : ∀ i, hatOf A kk vl i ⊆ halfPlaneGE nJ cJ)
    (hswept : SweptClosed (⋃ i, hatOf A kk vl i) vJ1 nJ cJ)
    (ahat_nonempty : (⋃ i, hatOf A kk vl i).Nonempty)
    (shellSubStrip : ∀ ε i₀ : ℕ, 0 < ε →
      (∀ i, i₀ ≤ i → Env (shell (hatOf A kk vl i) vJ1 nJ cJ ε)) →
      ∀ i, i₀ ≤ i → shell (hatOf A kk vl i) vJ1 nJ cJ ε ⊆
        {z | z + (kk i : ℤ) • vl ∈ halfStrip (B i) vl})
    (escape : ∀ (i ε : ℕ), 0 < ε → ∃ g ∈ hatOf A kk vl i, ∃ t : ℕ,
      g + (t : ℤ) • vJ1 ∉ hatOf A kk vl i ∧ cJ - (ε : ℤ) ≤ dot nJ (g + (t : ℤ) • vJ1))
    (shellEnv : ∃ ε i₀, 0 < ε ∧ ∀ i, i₀ ≤ i → Env (shell (hatOf A kk vl i) vJ1 nJ cJ ε))
    (fillCover : ∀ i i₀ ε, i₀ ≤ i → shell (hatOf A kk vl i) vJ1 nJ cJ ε ⊆
      ⋃ n, genFill S gen (hatOf A kk vl i ∪ shell (hatOf A kk vl i₀) vJ1 nJ cJ ε) n)
    (vJ : ℤ × ℤ) (F : FaceBlock S nJ vJ)
    -- **The generating point is the `v_J`-forward end of the face** (2026-09-19, team-lead
    -- ruling on Amink's finding).  Kernel receipt (`tmp/aenvfix_fillCover_wit.lean`, and
    -- `FillCoverWitness.lean` once landed): on `ShellSweep`'s data at `(i, i₀, ε) = (2, 1, 1)`
    -- the `:518` `fillCover` instance holds for `gen = (1,0) = a'` (`lex'`, `v_J`-maximal) and
    -- fails for `gen = (0,0) = a`.  Reading, not kernel fact: `bottom` puts the new sites of
    -- `Â_∞^{(ε+1)}` on a `+v_J` half-line, so only the `+v_J` endpoint can generate them.
    -- Free at the producer given `IsGeneratingSet` (`FaceBlock.generatesAt_a'` below).
    (gen_eq : gen = F.a')
    (vJ_prim : Primitive vJ) (nJ_prim : Primitive nJ)
    (bottom : ∀ ε : ℕ, ∃ (z₀ : ℤ × ℤ) (L : ℤ),
      dot nJ z₀ = cJ - (ε : ℤ) - 1 ∧
      (∀ k : ℤ, L ≤ k → z₀ + k • vJ ∈ reachSet (⋃ i, hatOf A kk vl i) vJ1) ∧
      (∀ b ∈ S, ∀ k : ℤ, L ≤ k →
        z₀ + k • vJ + (b - F.a) ∈ reachSet (⋃ i, hatOf A kk vl i) vJ1) ∧
      (∀ z ∈ shell (⋃ i, hatOf A kk vl i) vJ1 nJ cJ (ε + 1),
        z ∈ shell (⋃ i, hatOf A kk vl i) vJ1 nJ cJ ε ∨ ∃ k : ℤ, L ≤ k ∧ z = z₀ + k • vJ))
    (rec_p : ∀ g ∈ ⋃ i, hatOf A kk vl i, g + p ∈ ⋃ i, hatOf A kk vl i)
    (dot_nJ_p : dot nJ p ≠ 0)
    -- **Swapped 2026-09-19 (team-lead ruling, option (c)): `rec_vJ` out, the `Env` pin in.**
    -- `rec_vJ` is derived below from `bottom` + `hswept` + lattice-convexity of `Â_∞`
    -- (`rec_vJ_of_bottom`, `ItemII.lean` §8), and the convexity from `hEnv` + `maxA` + `hfin` +
    -- `AhatMono` (`latticeConvex_iUnion_hatOf`, `ChainAssemble.lean`).  `ofParts` itself is
    -- unchanged (25 binders); this constructor still takes 25 — a swap, not a deletion.
    (hEnv : Env = EnvOf (↑S : Set (ℤ × ℤ)))
    (nℓ : ℤ × ℤ) (cz : ℤ) (hprim : Primitive nℓ) (hperp : dot nℓ vl = 0)
    (hvl : vl ≠ 0) (hdet : det p vl = 0) (hpvJ : det p vJ ≠ 0)
    (hexh : Exhausts A nℓ cz)
    (hnotDP : ¬ ∃ h h' : ℤ × ℤ, det h h' ≠ 0 ∧
      PeriodicOnWith xper {z | cz ≤ dot nℓ z} h ∧ PeriodicOnWith xper {z | cz ≤ dot nℓ z} h') :
    ∃ k : ℤ, 0 < k ∧ det p vJ • (-p.2, p.1) = k • nℓ ∧
      (ChainDataGeom.ofPartsExhausts η xper vl p S gen Env B A u kk envShift envB maxA subBA subAB AhatMono vJ1 nJ cJ hsweep hfin hhp hswept ahat_nonempty shellSubStrip escape shellEnv fillCover vJ F gen_eq vJ_prim nJ_prim bottom rec_p dot_nJ_p hEnv
        nℓ cz hprim hperp hvl hdet hpvJ hexh hnotDP).cL = k * cz := by
  let rec_vJ' : ∀ g ∈ ⋃ i, hatOf A kk vl i, g + vJ ∈ ⋃ i, hatOf A kk vl i :=
    rec_vJ_of_bottom (latticeConvex_iUnion_hatOf η xper vl S Env B A u kk hEnv maxA hfin AhatMono)
      hsweep (fun _ hg => Set.iUnion_subset hhp hg) hswept F.dot_nJ_vJ bottom
  let side := ell_side_of_exhausts (xper := xper) (Ahat := hatOf A kk vl) hvl hdet hpvJ hprim
    hperp (fun i => hatOf_eq i) hexh rec_vJ' hnotDP
  exact ⟨side.choose, side.choose_spec.choose_spec.1, side.choose_spec.choose_spec.2.1,
    side.choose_spec.choose_spec.2.2.1⟩

end Nivat.Colle35

#print axioms Nivat.Colle35.ChainDataGeom.ofPartsExhausts
#print axioms Nivat.Colle35.ChainDataGeom.ofPartsExhausts_cL_spec
