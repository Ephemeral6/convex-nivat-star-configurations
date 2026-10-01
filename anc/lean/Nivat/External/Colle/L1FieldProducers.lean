/-
Lane: L1-field (2026-09-21)
Producers for the 14 field-level sorries in RegionSteps.lean:1733-1746.

Task: wire existing producers to `exists_cutResidualR_of_claim46_ofPieces`'s 14 parameters.
-/
import Nivat.External.Colle.WindowPlace
import Nivat.External.Colle.MaxIndexProbe
import Nivat.External.Colle.DecompData
import Nivat.External.Colle.L1Line0

namespace Nivat.L1FieldProducers

/-! ## Field 1-2: Window translation `v` and placement `τ`

Original text: b3_colle2.txt:822-826
- `:822-824`: the translate `𝒯` sits inside `𝓡^N_I`
- `:826`: `τ` chosen after maximal index N

**Status**: `exists_tau_mem_cut_pair` (WindowPlace.lean:91) produces both simultaneously.
The producer requires `htail` (each level ≥ lev N contains a u'-tail in Rinf).

TODO: `htail` producer is the remaining debt. It comes from the definition of 𝓡_{I-1}
as a tower built by `:806-812`. Not producing here; this is geometric content about
the tower structure itself.
-/

/-! ## Field 3: Side parameter `ε : Bool`

Original text: b3_colle2.txt — implicit in the window construction.

**Status**: `εOf` (L1Line0.lean) determines which side is "top" from geometric data.
This is a definition, not an existence statement.
-/

/-- **Field 3 producer**: `ε` from geometric data. -/
def εOf_field (u' vl : ℤ × ℤ) : Bool :=
  Nivat.L1Line0.εOf u' vl

/-! ## Field 4: Tower region `Rinf : Set (ℤ × ℤ)`

Original text: b3_colle2.txt:806-820 — `𝓡_{I-1}` is the union of regions in the tower.

**Status**: This is the fundamental debt of the tower construction. The tower is built
by successive half-plane extensions (`:806-812`), and `Rinf` is their union.
L1RegionBuild.lean has infrastructure, but no complete producer yet.

TODO: This is major geometric content, not a field wiring issue.
-/

/-! ## Field 5-6: Generating set `Sφ` and anchor `a`

Original text: b3_colle2.txt:848-856 (Figure 11(B))

**Status for Sφ**: `d.Sphi` is the generating set from DecompData.
`DecompDataZ.isGeneratingSet` (DecompData.lean:195) proves it generates.

**Status for a**: Paired with corner point from `hcorner`. MaxIndexProbe.lean
has `exists_corner_shear_of_generating` but this couples with geometric constraints.

TODO: `a` production needs coordination with corner geometry.
-/

/-- **Field 5 producer**: `Sφ` from decomposition data.

Given `d : DecompDataZ ξ`, we have `d.Sphi : Finset (ℤ × ℤ)` and
`d.isGeneratingSet : IsGeneratingSet ξ d.Sphi` (DecompData.lean:195).

This is already available, no new theorem needed — just use `d.Sphi` and `d.isGeneratingSet`.
-/
example {ξ : Config ℤ} (d : Nivat.Colle35.DecompDataZ ξ) :
    Nivat.Colle.IsGeneratingSet ξ (d.toDecompData.Sphi) :=
  d.isGeneratingSet

/-! ## Field 7: Generator proof `hgen : GeneratesAt ξ Sφ a`

Original text: b3_colle2.txt:848-856 (Figure 11(B))

**Status**: Once `Sφ` and `a` are fixed, this follows from `IsGeneratingSet`.
The conversion from `IsGeneratingSet` to `GeneratesAt` at a specific anchor
is definitional given the anchor is in the set.

TODO: Needs `a ∈ Sφ` or appropriate anchor selection.
-/

/-! ## Field 8: Region property `hR : IsRegion Rinf vl u'`

Original text: b3_colle2.txt:806-820

**Status**: This is part of the tower construction debt. Each level in the tower
is a region, and their union must also be a region. This is non-trivial geometric
content about lattice convexity preservation under directed unions.

TODO: Major geometric content.
-/

/-! ## Field 9-10: Level existence `h0` and unboundedness `hunb`

These are inputs to `CutLevels.exists_lev_for_ofCut`.

Original text: b3_colle2.txt:806-820 (tower properties)

**Status**:
- `h0`: level 0 contains a point (immediate from nonemptiness)
- `hunb`: unboundedness downward (follows from tower being a union of half-strips)

TODO: Wire from tower nonemptiness and structure.
-/

/-! ## Field 11: Base periodicity `hbase`

Original text: b3_colle2.txt:806

**Status**: This is the core periodicity hypothesis for the tower construction.
It states that `(T^e ξ)` is periodic on `cut Rinf m lev 0` with period `c • vl`.

This is a **parameter**, not something to be produced — it's part of the standing
hypothesis for the tower route.

TODO: Clarify the relationship between this `hbase` and the input `hbase₁` on
`coneRegion B vl u'`.
-/

/-! ## Field 12: Non-periodicity `hinf`

Original text: b3_colle2.txt:814

**Status**: Dual to `hbase`. States that the *full* union `Rinf` is NOT periodic.
This is what forces the tower to be finite-height (contradicting `:814`).

MaxIndexProbe.lean has `hinf_of_ge` which derives this from covering arguments.

TODO: Wire from the contradiction argument.
-/

/-! ## Field 13: Placement `hline`

Original text: b3_colle2.txt:822-824 (Claim 4.7)

**Status**: `exists_tau_mem_cut_pair` (WindowPlace.lean:91) produces the required
`τ` satisfying placement constraints at any given level N.

The field signature quantifies over `lev` and `N`, so we need to show that
the same `τ` works at the *maximal* N (where periodicity transitions).

TODO: Instantiate `exists_tau_mem_cut_pair` at the maximal index.
-/

/-! ## Field 14: Cover `hcover`

Original text: b3_colle2.txt:848-856 (Figure 11(B))

**Status**: The geometric cover argument showing that `overlap Rhi` is contained
in `genClosure Sφ a (overlap Rlo ∪ ray g u' t₀)`.

This is substantial geometric content about how the generating set determines
the boundary structure.

TODO: Major geometric content.
-/

/-! ## Summary

**Fields with existing producers (can wire immediately)**:
- Field 3 (`ε`): definitional from `εOf`
- Field 5 (`Sφ`): `d.Sphi` with `isGeneratingSet`

**Fields requiring minor wiring**:
- Fields 1-2 (`v`, `τ`): `exists_tau_mem_cut_pair` exists, needs `htail`
- Fields 9-10 (`h0`, `hunb`): should follow from tower structure

**Fields requiring geometric work**:
- Field 4 (`Rinf`): tower union construction
- Field 6 (`a`): corner/anchor coordination
- Field 7 (`hgen`): follows once `a` is fixed
- Field 8 (`hR`): region property of tower union
- Field 11 (`hbase`): standing hypothesis, needs clarification
- Field 12 (`hinf`): contradiction setup
- Field 13 (`hline`): instantiation at maximal index
- Field 14 (`hcover`): Figure 11(B) geometric cover

**Recommendation**: The 14 sorries should NOT be cleared individually here.
Instead, they represent 5-6 major geometric components:
1. Tower construction (fields 4, 8, 9, 10, 11, 12)
2. Window placement (fields 1, 2, 13)
3. Corner/anchor geometry (fields 6, 7)
4. Cover argument (field 14)
5. Trivial fields (fields 3, 5)

Clearing them requires addressing these components, not just writing field producers.
-/

end Nivat.L1FieldProducers
