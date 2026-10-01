/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.ChainGeom
import Nivat.External.Colle.Lemma41

/-!
# The shells `Â_∞^{(ε)}` of a `ChainDataGeom`: what is free

Upstream companion of `ShellConvex.lean`.  That file refutes lattice-convexity of the shells
with two explicit `ChainDataGeom` witnesses and therefore sits downstream of
`Step_PeriodsRays2` — and hence of `RegionSteps`, the file holding the `sorry` these facts
inform.  The five general lemmas below need only `ChainGeom` and `Lemma41` (for
`Colle41.RayIn` / `IsRegion`), so they live here where
`RegionSteps.lean` can `import` them (`PROTOCOL.md` §20: a lemma downstream of its consumer is
stranded).

* `ChainDataWithShell.shellInf_zero_eq`: `Â_∞^{(0)} = Â_∞`.  One inclusion is the field
  `shellInfZero` (`Lemma35.lean:741`); the other is `t = 0` in the shell formula `shellInf_eq`
  (`ChainShell.lean:58`) with `ahat_halfPlane` (`ChainShell.lean:63`).  Consequently
  `IsLatticeConvexRegion (shellInf 0) ↔ IsLatticeConvexRegion (⋃ i, Ahat i)`
  (`isLatticeConvexRegion_shellInf_zero_iff`) — at `ε = 0` shell convexity *is* `hRconv`.
* `ChainDataWithShell.ahat_subset_shellInf`: `Â_∞ ⊆ Â_∞^{(ε)}` for every `ε`.
* `ChainDataGeom.rayIn_shellInf_p` / `rayIn_shellInf_vJ`: the two ray conjuncts of
  `Colle41.IsRegion (shellInf ε) p vJ` (`Lemma41.lean:688`) hold unconditionally, by iterating
  `rec_p` / `rec_vJ` inside `Â_∞` and pushing along `ahat_subset_shellInf`.
* `ChainDataGeom.isRegion_shellInf_iff`: hence `IsRegion (shellInf ε) p vJ` is exactly its
  convexity conjunct.  `ShellConvex.lean` shows that conjunct is **not** a consequence of the
  bundle, even under `hRconv`.
-/

set_option autoImplicit false

namespace Nivat.Colle35

open Nivat Nivat.LE2 Nivat.MaxEnv

variable {α : Type*}

/-- **`Â_∞^{(0)} = Â_∞`.**  `⊆` is the field `shellInfZero`; `⊇` is `t = 0` in the shell
formula plus `ahat_halfPlane`. -/
theorem ChainDataWithShell.shellInf_zero_eq {η xper : Config α} {vl : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} {gen : ℤ × ℤ} (c : ChainDataWithShell η xper vl S gen) :
    c.toChainData.shellInf 0 = ⋃ i, c.toChainData.Ahat i := by
  refine Set.Subset.antisymm c.shellInfZero ?_
  intro g hg
  rw [c.shellInf_eq]
  refine ⟨g, hg, 0, by simp, ?_⟩
  simpa using c.ahat_halfPlane g hg

/-- At thickness `0`, lattice-convexity of the shell **is** `hRconv`. -/
theorem ChainDataWithShell.isLatticeConvexRegion_shellInf_zero_iff {η xper : Config α}
    {vl : ℤ × ℤ} {S : Finset (ℤ × ℤ)} {gen : ℤ × ℤ} (c : ChainDataWithShell η xper vl S gen) :
    IsLatticeConvexRegion (c.toChainData.shellInf 0) ↔
      IsLatticeConvexRegion (⋃ i, c.toChainData.Ahat i) := by
  rw [c.shellInf_zero_eq]

/-- `Â_∞ ⊆ Â_∞^{(ε)}` for every `ε`: `t = 0` in the shell formula, and `cJ - ε ≤ cJ ≤ dot nJ g`. -/
theorem ChainDataWithShell.ahat_subset_shellInf {η xper : Config α} {vl : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} {gen : ℤ × ℤ} (c : ChainDataWithShell η xper vl S gen) (ε : ℕ) :
    (⋃ i, c.toChainData.Ahat i) ⊆ c.toChainData.shellInf ε := by
  intro g hg
  rw [c.shellInf_eq]
  refine ⟨g, hg, 0, by simp, ?_⟩
  have := c.ahat_halfPlane g hg
  omega

/-! ### The two ray conjuncts of `IsRegion (shellInf ε) p vJ` — unconditional

`Colle41.IsRegion K u u'` (`Lemma41.lean:688`) is `IsLatticeConvexRegion K ∧ (∃ z₀, RayIn K z₀ u)
∧ (∃ z₀', RayIn K z₀' u')`.  The two rays are free: `rec_p` / `rec_vJ` iterate inside `⋃ Ahat`,
and `ahat_subset_shellInf` puts that inside every shell.  Only the convexity conjunct is in
question, and `ShellConvex.lean` refutes it. -/

/-- Iterating a recession direction of `Â_∞` from any point of `Â_∞`. -/
theorem ChainDataWithShell.rayIn_iUnion_ahat_of_rec {η xper : Config α} {vl : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} {gen : ℤ × ℤ} (c : ChainDataWithShell η xper vl S gen) {v : ℤ × ℤ}
    (hrec : ∀ g ∈ ⋃ i, c.toChainData.Ahat i, g + v ∈ ⋃ i, c.toChainData.Ahat i)
    {g : ℤ × ℤ} (hg : g ∈ ⋃ i, c.toChainData.Ahat i) :
    Colle41.RayIn (⋃ i, c.toChainData.Ahat i) g v := by
  intro k
  induction k with
  | zero => simpa using hg
  | succ k ih =>
    have := hrec _ ih
    convert this using 1
    push_cast
    rw [add_smul, one_smul, add_assoc]

/-- `∃ z₀, RayIn (Â_∞^{(ε)}) z₀ p`, from `ahat_nonempty` and `rec_p`. -/
theorem ChainDataGeom.rayIn_shellInf_p {η xper : Config α} {vl p : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} {gen : ℤ × ℤ} (cg : ChainDataGeom η xper vl p S gen) (ε : ℕ) :
    ∃ z₀ : ℤ × ℤ, Colle41.RayIn (cg.toChainData.shellInf ε) z₀ p := by
  obtain ⟨g, hg⟩ := cg.ahat_nonempty
  exact ⟨g, fun k => cg.ahat_subset_shellInf ε
    (cg.toChainDataWithShell.rayIn_iUnion_ahat_of_rec cg.rec_p hg k)⟩

/-- `∃ z₀', RayIn (Â_∞^{(ε)}) z₀' v_J`, from `ahat_nonempty` and `rec_vJ`. -/
theorem ChainDataGeom.rayIn_shellInf_vJ {η xper : Config α} {vl p : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} {gen : ℤ × ℤ} (cg : ChainDataGeom η xper vl p S gen) (ε : ℕ) :
    ∃ z₀' : ℤ × ℤ, Colle41.RayIn (cg.toChainData.shellInf ε) z₀' cg.vJ := by
  obtain ⟨g, hg⟩ := cg.ahat_nonempty
  exact ⟨g, fun k => cg.ahat_subset_shellInf ε
    (cg.toChainDataWithShell.rayIn_iUnion_ahat_of_rec cg.rec_vJ hg k)⟩

/-- **`IsRegion (Â_∞^{(ε)}) p v_J` reduces to its convexity conjunct alone.**  This is the
`hR_region` slot of `case1_sweep` at `R := shellInf ε`, `u := p`, `u' := cg.vJ`, priced. -/
theorem ChainDataGeom.isRegion_shellInf_iff {η xper : Config α} {vl p : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} {gen : ℤ × ℤ} (cg : ChainDataGeom η xper vl p S gen) (ε : ℕ) :
    Colle41.IsRegion (cg.toChainData.shellInf ε) p cg.vJ ↔
      IsLatticeConvexRegion (cg.toChainData.shellInf ε) :=
  ⟨fun h => h.1, fun h => ⟨h, cg.rayIn_shellInf_p ε, cg.rayIn_shellInf_vJ ε⟩⟩

end Nivat.Colle35

#print axioms Nivat.Colle35.ChainDataWithShell.shellInf_zero_eq
#print axioms Nivat.Colle35.ChainDataWithShell.isLatticeConvexRegion_shellInf_zero_iff
#print axioms Nivat.Colle35.ChainDataWithShell.ahat_subset_shellInf
#print axioms Nivat.Colle35.ChainDataWithShell.rayIn_iUnion_ahat_of_rec
#print axioms Nivat.Colle35.ChainDataGeom.rayIn_shellInf_p
#print axioms Nivat.Colle35.ChainDataGeom.rayIn_shellInf_vJ
#print axioms Nivat.Colle35.ChainDataGeom.isRegion_shellInf_iff
