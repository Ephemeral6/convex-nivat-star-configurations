/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.EnvBound
import Nivat.External.Colle.ChainRecursion
import Nivat.External.Colle.CaseSplit

/-!
# The leaf-A seam: `Case2` + item (iv) ⟹ `StepHyp`

Landed 2026-09-18 from `tmp/tl_stephyp_of_case2.lean`, after discovering that item (iv) has
been compiled and in the main build since 2026-09-17
(`Nivat/External/Colle/EnvBound.lean`).

`ChainRecursion.lean` already turns `StepHyp` (`:49-59`) into an ℕ-indexed chain
(`chainState`, `:66`) and discharges six of `ChainData`'s nineteen fields from it
(`envB_chain`/`envA_chain`/`subBA_chain`/`subAB_chain`/`subStrip_chain`/`agreeA_chain`,
`:117-146`).  `EnvBound.lean` already produces the maximal element
(`exists_maximal_agreeFamily`, `:111`).  Nobody had checked whether the two meet.

They do, and exactly:

* `StepHyp`'s five conjuncts (`ChainRecursion.lean:51-59`) are, in order, the four conjuncts of
  `chainFamily U B (halfStrip B vl) P` (`MaximalEnveloped.lean:254`) plus the maximality
  clause — the same shape `exists_maximal_agreeFamily` concludes with.
* `exists_maximal_agreeFamily` needs a **fixed** disagreement point `z₀ = b₀ + t₀ • vl` with
  `b₀ ∈ B`, per `B`.  `Case2` (`RegionSteps.lean:327-331`) is universally quantified over `B`
  and `u`, so it supplies one for every `B` the recursion reaches — and `halfStrip`'s
  definition (`LatticeEdges.lean:1810-1811`) is literally `{g | ∃ b ∈ B, ∃ t : ℕ, g = b + t•v}`,
  so unpacking membership yields `hb₀`/`hz₀` in exactly the form item (iv) demands.  No
  translation step, no side condition.
* The seed `T₀` is `B` itself: `subset_halfStrip` (`LatticeEdges.lean:1813`) gives
  `B ⊆ halfStrip B vl`, and the other three conjuncts are `StepHyp`'s own hypotheses.

The edge-normal hypotheses (`hU`/`hdet`/`hn`/`hn'`/`hm`/`hm'`) are passed through rather than
discharged: at `S := d.Sphi` they come from `exists_two_nonparallel_edge_normals`
(`EdgeNormals.lean:38`) and `hSfin_of_decompDataZ` (`tmp/L1_hSfin.lean`, not yet landed).
Keeping them as parameters is deliberate — this lemma is about the *seam*, and the supplier is
a separate obligation that should not be silently fused into it.

⚠ **Downstream warning, proved not suspected.**  This lemma itself never mentions `kk`, `Ahat`
or `ChainDataGeom`; it only produces `StepHyp`.  But whoever assembles the full
`ChainDataGeom` on top of this wiring must give `kk` a genuine dependence on `i`:
`ChainRecursion.lean` has no indexed `u` field (every use is the literal parameter `u₀`) and
`chainB_succ_eq_chainA` (`ChainRecursion.lean:91-92`) is `rfl`, i.e. `B (i+1) = A i` exactly;
those two facts alone make `kk ≡ 0` contradictory (`tmp/stephyp_landing_audit.lean`,
`tmp/chaindata_kkzero_false.lean`).  See `delivery/blueprint/LEAF-A.md`.
-/

namespace Nivat.TLSeam

open Nivat Nivat.LE2 Nivat.ColleReg4

/-- **`Case2` plus the item (iv) bound gives the single-step hypothesis of the chain
recursion.**

This is the composition that closes leaf A's pieces 1 and 2 into the form
`ChainRecursion.chainState` consumes. -/
theorem stepHyp_of_case2 {ξ xper : Config ℤ} {S : Finset (ℤ × ℤ)} {vl u₀ : ℤ × ℤ}
    (hU : (E (↑S : Set (ℤ × ℤ))).Finite)
    {n m : ℤ × ℤ} (hdet : det n m ≠ 0)
    (hn : n ∈ E (↑S : Set (ℤ × ℤ))) (hn' : -n ∈ E (↑S : Set (ℤ × ℤ)))
    (hm : m ∈ E (↑S : Set (ℤ × ℤ))) (hm' : -m ∈ E (↑S : Set (ℤ × ℤ)))
    (hcase2 : Nivat.ColleReg.Case2 ξ xper S vl) :
    StepHyp ξ xper S vl u₀ := by
  intro B hB hagree
  -- 1. Case 2 supplies a disagreement point inside `H_B(ℓ_ι)`.
  have hdis := hcase2 B hB u₀ hagree
  push Not at hdis
  obtain ⟨z₀, hz₀mem, hz₀ne⟩ := hdis
  -- 2. `halfStrip` membership *is* item (iv)'s `hb₀`/`hz₀` shape.
  obtain ⟨b₀, hb₀, t₀, hz₀eq⟩ := hz₀mem
  -- 3. `B` is finite, being enveloped over a set with two independent antipodal normals.
  have hBfin : B.Finite := Nivat.MaxEnv.finite_of_envOf hU hdet hn hn' hm hm' hB
  -- 4. The seed of the family is `B` itself.
  have hseed : B ∈ Nivat.MaxEnv.chainFamily (↑S : Set (ℤ × ℤ)) B
      (Nivat.LE2.halfStrip B vl) (fun z => T u₀ ξ z = xper z) :=
    ⟨hB, subset_rfl, subset_halfStrip B vl, hagree⟩
  -- 5. Item (iv).
  obtain ⟨M, hM, -, hmax⟩ :=
    Nivat.ProbeUB.exists_maximal_agreeFamily hU hdet hn hn' hm hm' hBfin hb₀ hz₀eq
      (P := fun z => T u₀ ξ z = xper z) hz₀ne hseed
  obtain ⟨hMenv, hBM, hMstrip, hMagree⟩ := hM
  exact ⟨M, hMenv, hBM, hMstrip, hMagree,
    fun Tset hT hBT hTstrip hTagree hMT => hmax Tset ⟨hT, hBT, hTstrip, hTagree⟩ hMT⟩

end Nivat.TLSeam

#print axioms Nivat.TLSeam.stepHyp_of_case2
