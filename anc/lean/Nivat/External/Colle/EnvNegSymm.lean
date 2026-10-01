/-
Copyright (c) 2026 Nivat Formalization Contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lane-towerpkg
-/
import Nivat.External.Colle.LatticeEdges
import Nivat.External.Colle.DecompData
import Nivat.External.Colle.TowerConstruct

/-! # `E B` is closed under negation — and why the `hconv` refutation does not instantiate

**What this file is for.**  `tmp/wip/lane-tower-hlev-hconv-refuted.lean` claims to refute

```
hconv : ∀ n ≤ (sortedCand d nℓ u' i).length + 1,
  IsLatticeConvexRegion (tower (coneRegion B vl u') (wtower d nℓ vl u' i) n)
```

at `n = 0`, with `B = 𝒮_φ = BX := {(0,5), (2,2), (3,1), (3,0), (4,0)}`.  Its statement
`hconv_refuted` quantifies `SphiX` **freely**: it never exhibits a `d : DecompData ξ` with
`d.Sphi = SphiX`.  That gap is fatal, and this file closes it from the kernel.

**The mechanism.**  `henv : EnvOf (↑d.Sphi) B` is `Enveloped`, whose second clause is the
cardinality equation `(E B).encard = (E ↑d.Sphi).encard` (`LatticeEdges.lean:628-629`).
Together with `E B ⊆ E ↑d.Sphi` and finiteness that forces `E B = E ↑d.Sphi`
(`Nivat.LE2.Enveloped.E_eq`, `LatticeEdges.lean:1657`).  And `E ↑d.Sphi` is closed under
negation **unconditionally**, for every `DecompData`, because `Conv d.Sphi` is the zonotope of
`h₁, …, h_m` (`DecompData.Sphi_eq`, `DecompData.lean:108`) and a zonotope's edge normals come
in antipodal pairs (`Nivat.Colle35.Sphi_negSymm`, `DecompData.lean:417`).

So **every `B` on `lane-towerpkg`'s binder list has an antipodally symmetric edge set.**
`BX` does not: `(0,-1) ∈ E BX` (the bottom edge `(3,0)-(4,0)`, which the refutation itself
proves as `edge_vl_BX`), but `(0,1) ∉ E BX`, because the top of the triangle
`(0,5), (3,0), (4,0)` is a **vertex**, not an edge — `face BX (0,1) = {(0,5)}`.

That asymmetry is not incidental to the refutation, it *is* its mechanism: the triangle
narrows to width `0.2` near the apex, the row `y = 4` of `conv BX` carries no lattice point of
`BX`, and that is the only reason `(1,4)` escapes `coneRegion BX vl u'`.

原文：`scratch/b3_colle2.txt:402` (Definition 3.2, the `|E(𝒯)| = |E(𝒰)|` clause) and
`:402`'s antecedent "a finite convex set `𝒰` such that `conv(𝒰)` has positive area", with
`𝒰 := 𝒮_φ` fixed by `:770` to be the support of `φ(X) = (X^{h₁}−1)⋯(X^{h_m}−1)`.

**Scope of the claim.**  This file refutes the *instantiability* of
`lane-tower-hlev-hconv-refuted.lean:209 hconv_refuted` at `SphiX := BX`.  It does **not** prove
`hconv`; it restores `hconv` to the status of an open obligation, and hands the tower lanes the
extra structure (`E B = E ↑d.Sphi`, antipodally symmetric) that the binder list carries but
never spelled out.
-/

set_option autoImplicit false

namespace Nivat.LaneTowerPkgEnvSymm

open Nivat Nivat.LE2 Nivat.Colle35

variable {α : Type*} [AddCommMonoid α] {η : Config α}

/-! ## §1  What `henv` really gives -/

/-- **An enveloped `B` has exactly `𝒮_φ`'s edge normals.**  `Enveloped.E_eq`
(`LatticeEdges.lean:1657`) with finiteness from `d.Sphi` being a `Finset`.

原文：`b3_colle2.txt:402` — Definition 3.2's cardinality clause `|E(𝒯)| = |E(𝒰)|`. -/
theorem E_eq_of_envOf (d : DecompData η) {B : Set (ℤ × ℤ)}
    (henv : EnvOf (↑d.Sphi : Set (ℤ × ℤ)) B) :
    E B = E (↑d.Sphi : Set (ℤ × ℤ)) :=
  Nivat.LE2.Enveloped.E_eq (finite_E_of_finite d.Sphi.finite_toSet) henv

/-- **`E B` is closed under negation**, for every `E(𝒮_φ)`-enveloped `B`.  No hypothesis beyond
`henv`: the symmetry comes from `Conv d.Sphi` being a zonotope (`DecompData.Sphi_eq`), via
`Colle35.Sphi_negSymm` (`DecompData.lean:417`).

原文：`b3_colle2.txt:770` — `φ(X) := (X^{h₁}−1)⋯(X^{h_m}−1)`, whose Newton polygon is a
zonotope, hence centrally symmetric. -/
theorem E_negSymm_of_envOf (d : DecompData η) {B : Set (ℤ × ℤ)}
    (henv : EnvOf (↑d.Sphi : Set (ℤ × ℤ)) B) (n : ℤ × ℤ) :
    n ∈ E B ↔ -n ∈ E B := by
  rw [E_eq_of_envOf d henv]
  exact Sphi_negSymm d n

/-- The form the tower lanes want: **both** faces of an edge normal are nontrivial.  This is the
"top and bottom of `B` each carry at least two lattice points" input of
`lane-tower-hlev`'s step (A). -/
theorem face_nontrivial_neg_of_envOf (d : DecompData η) {B : Set (ℤ × ℤ)}
    (henv : EnvOf (↑d.Sphi : Set (ℤ × ℤ)) B) {n : ℤ × ℤ} (hn : n ∈ E B) :
    (face B n).Nontrivial ∧ (face B (-n)).Nontrivial :=
  ⟨hn.2, ((E_negSymm_of_envOf d henv n).mp hn).2⟩

/-! ## §2  The refutation's witness violates it -/

/-- The refutation's `B = 𝒮_φ`: the lattice points of the triangle `(0,5), (3,0), (4,0)`.
Copied verbatim from `tmp/wip/lane-tower-hlev-hconv-refuted.lean:73`. -/
def BX : Set (ℤ × ℤ) := {((0 : ℤ), (5 : ℤ)), (2, 2), (3, 1), (3, 0), (4, 0)}

/-- `(0,-1) ∈ E BX`: the bottom edge `(3,0)-(4,0)`.  (This is the refutation's own
`edge_vl_BX`, reproved here so that this file stands alone.) -/
theorem neg_e2_mem_E_BX : ((0 : ℤ), (-1 : ℤ)) ∈ E BX := by
  refine ⟨by decide, ⟨((3 : ℤ), (0 : ℤ)), ⟨by simp [BX], ?_⟩,
    ((4 : ℤ), (0 : ℤ)), ⟨by simp [BX], ?_⟩, by decide⟩⟩
  · intro y hy
    simp only [BX, Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl <;> simp only [dot] <;> omega
  · intro y hy
    simp only [BX, Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl <;> simp only [dot] <;> omega

/-- `face BX (0,1) = {(0,5)}`: the apex of the triangle is a **vertex**, not an edge. -/
theorem face_BX_e2_subsingleton : (face BX ((0 : ℤ), (1 : ℤ))).Subsingleton := by
  have key : ∀ z ∈ face BX ((0 : ℤ), (1 : ℤ)), z = ((0 : ℤ), (5 : ℤ)) := by
    rintro z ⟨hzB, hz⟩
    have h05 : dot ((0 : ℤ), (1 : ℤ)) ((0 : ℤ), (5 : ℤ)) ≤ dot ((0 : ℤ), (1 : ℤ)) z :=
      hz _ (by simp [BX])
    simp only [dot] at h05
    simp only [BX, Set.mem_insert_iff, Set.mem_singleton_iff] at hzB
    rcases hzB with rfl | rfl | rfl | rfl | rfl <;> simp only at h05 ⊢ <;> omega
  intro x hx y hy
  rw [key x hx, key y hy]

/-- `(0,1) ∉ E BX`. -/
theorem e2_not_mem_E_BX : ((0 : ℤ), (1 : ℤ)) ∉ E BX := fun h =>
  face_BX_e2_subsingleton.not_nontrivial h.2

/-- **`E BX` is not antipodally symmetric.** -/
theorem E_BX_not_negSymm :
    ¬ (∀ n : ℤ × ℤ, n ∈ E BX ↔ -n ∈ E BX) := by
  intro h
  refine e2_not_mem_E_BX ?_
  have : -((0 : ℤ), (1 : ℤ)) = ((0 : ℤ), (-1 : ℤ)) := by decide
  exact (h ((0 : ℤ), (1 : ℤ))).mpr (by rw [this]; exact neg_e2_mem_E_BX)

/-! ## §3  Conclusion: the refutation instance does not exist -/

/-- **No `DecompData` envelops `BX`.**  Hence `lane-tower-hlev-hconv-refuted.lean:209`'s
`henv` conjunct cannot be met with `SphiX := ↑d.Sphi` for any actual `d`, and the file does not
refute `hconv` as it occurs in `lane_towerpkg_reduce` (whose binder list contains
`d : DecompData ξ` and `henv : EnvOf (↑d.Sphi) B`, not a free `SphiX`). -/
theorem not_envOf_Sphi_BX (d : DecompData η) :
    ¬ EnvOf (↑d.Sphi : Set (ℤ × ℤ)) BX := fun henv =>
  E_BX_not_negSymm (E_negSymm_of_envOf d henv)

/-! ## §4  One-point seeds are illegal too

Several proposed refutations of `hconv` / of its half-plane weakenings take `B := {(0,0)}`
(`TowerLevelStep.sweep_cone_not_isLatticeConvexRegion`, and `lane-tower-hbase`'s `I ≥ 1`
computation of 2026-09-23).  No such instance exists either, for a cruder reason than `BX`'s:
a one-point set has **no** edges at all, while `E ↑d.Sphi` always has at least the antipodal
pair `± genPerp' (d.h j)` (`ColleReg.genPerp'_mem_E_Sphi`, `TowerConstruct.lean:55`, which needs
only `d.h_ne` and `d.Sphi_eq`), and `Enveloped` equates the two cardinalities.

原文：`b3_colle2.txt:402` — Definition 3.2 again, same clause as §1. -/
theorem not_envOf_Sphi_of_subsingleton {ξ : Config ℤ} (d : DecompData ξ) {B : Set (ℤ × ℤ)}
    (hB : B.Subsingleton) : ¬ EnvOf (↑d.Sphi : Set (ℤ × ℤ)) B := by
  intro henv
  have hj : (0 : ℕ) < d.m := lt_of_lt_of_le (by norm_num) d.hm
  have hmem : Nivat.LE2.genPerp' (d.h ⟨0, hj⟩) ∈ E B := by
    rw [E_eq_of_envOf d henv]
    exact (Nivat.ColleReg.genPerp'_mem_E_Sphi d ⟨0, hj⟩).1
  exact (hB.anti (fun z hz => hz.1)).not_nontrivial hmem.2

/-! ## §5  From `lane-towerpkg`'s binder list to `lane-tower-hlev`'s `n = 0` inputs

`Nivat.LaneTowerHlevConv.isLatticeConvexRegion_coneRegion` (`TowerSeedConvex.lean:421`) asks for
`hB : IsLatticeConvexRegion B`, `hprim : Prim n`, `hperp : dot n vl = 0`, `hpos : n ∈ E B`,
`hneg : -n ∈ E B`, `hunimod`.  `lane_towerpkg_reduce`'s binder list supplies all six **with
`n := nℓ`** and with no new binder:

| hlev asks | `lane-towerpkg` supplies |
|---|---|
| `hB` | `latticeConvex_of_envOf henv` — `Enveloped` ⊃ `WeaklyEnveloped` ⊃ `IsLatticeConvexRegion B` (`LatticeEdges.lean:624`) |
| `hprim` | `hprim : Prim nℓ` (`RegionSteps.lean:1725`) |
| `hperp` | `hperp : dot nℓ vl = 0` (`RegionSteps.lean:1720`) |
| `hpos`/`hneg` | `nl_mem_E_B_of_hdoth` below, from `henv` + `hprim` + `i` + `hdoth` |
| `hunimod` | `hunimod : det u' vl = 1 ∨ det u' vl = -1` (`RegionSteps.lean:1718`) |

So the `n = 0` rung of `hconv` costs **no** extra hypothesis.  Note in particular that `hbase₁`,
`hnu`, `hadj`, `hBfin`, `hBne` and `hc` are all untouched.

The only non-formal step is `nl_mem_E_B_of_hdoth`: `hdoth` says `nℓ ⟂ d.h i`, and `genPerp' (d.h i)`
is by construction also `⟂ d.h i`, so the two are parallel; both are primitive, hence equal up to
sign; and *both* signs of `genPerp' (d.h i)` lie in `E B` (`ColleReg.genPerp'_mem_E_B`,
`TowerConstruct.lean:64`).  This is the same "`d.h i` is the `vl`-parallel generator" content that
`h_i_eq_zsmul_vl` extracts, but it does not need `hperp` or `Primitive vl`.

原文：`b3_colle2.txt:806-808`（塔以 `𝒮_φ` 的边方向扫掠）+ `:402`（Definition 3.2）. -/

/-- `EnvOf` carries lattice convexity of the envelope: it is the first clause of
`WeaklyEnveloped` (`LatticeEdges.lean:624`).  Stated separately because `lane-towerpkg`'s binder
list has no `IsLatticeConvexRegion B` of its own — it comes out of `henv`. -/
theorem latticeConvex_of_envOf {U B : Set (ℤ × ℤ)} (henv : Nivat.LE2.EnvOf U B) :
    IsLatticeConvexRegion B := henv.1.1

/-- **Both signs of `nℓ` are edge normals of `B`.**  `hdoth : dot nℓ (d.h i) = 0` makes `nℓ`
parallel to `genPerp' (d.h i)`; both are primitive, so they agree up to sign, and
`ColleReg.genPerp'_mem_E_B` puts both signs of `genPerp' (d.h i)` in `E B`.

原文：`b3_colle2.txt:806-808`；这是 `RegionSteps.lean:1725-1727` 的 `hprim`/`i`/`hdoth` 三条
binder 的几何内容。 -/
theorem nl_mem_E_B_of_hdoth {ξ : Config ℤ} (d : DecompData ξ) {B : Set (ℤ × ℤ)} {nℓ : ℤ × ℤ}
    (henv : Nivat.LE2.EnvOf (↑d.Sphi : Set (ℤ × ℤ)) B) (hprim : Prim nℓ)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0) :
    nℓ ∈ E B ∧ -nℓ ∈ E B := by
  have hhne : d.h i ≠ 0 := d.h_ne i
  have hmem := Nivat.ColleReg.genPerp'_mem_E_B d henv i
  have hp2 : Prim (Nivat.LE2.genPerp' (d.h i)) := Nivat.LE2.genPerp'_prim hhne
  have hd0 : det nℓ (Nivat.LE2.genPerp' (d.h i)) = 0 :=
    Nivat.LE2.det_eq_zero_of_dot_eq_zero hhne (by rw [dot_comm]; exact hdoth)
      (Nivat.LE2.dot_genPerp' hhne)
  rcases Nivat.LE2.eq_or_neg_of_prim_of_det_eq_zero hprim hp2 hd0 with heq | heq
  · rw [heq] at hmem; exact hmem
  · rw [heq] at hmem
    exact ⟨by simpa using hmem.2, hmem.1⟩

end Nivat.LaneTowerPkgEnvSymm

#print axioms Nivat.LaneTowerPkgEnvSymm.E_eq_of_envOf
#print axioms Nivat.LaneTowerPkgEnvSymm.E_negSymm_of_envOf
#print axioms Nivat.LaneTowerPkgEnvSymm.face_nontrivial_neg_of_envOf
#print axioms Nivat.LaneTowerPkgEnvSymm.neg_e2_mem_E_BX
#print axioms Nivat.LaneTowerPkgEnvSymm.e2_not_mem_E_BX
#print axioms Nivat.LaneTowerPkgEnvSymm.E_BX_not_negSymm
#print axioms Nivat.LaneTowerPkgEnvSymm.not_envOf_Sphi_BX
#print axioms Nivat.LaneTowerPkgEnvSymm.not_envOf_Sphi_of_subsingleton
#print axioms Nivat.LaneTowerPkgEnvSymm.latticeConvex_of_envOf
#print axioms Nivat.LaneTowerPkgEnvSymm.nl_mem_E_B_of_hdoth
