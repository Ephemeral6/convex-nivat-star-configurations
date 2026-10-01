/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.ChainAssemble
import Nivat.External.Colle.ItemIIRec
import Nivat.External.Colle.LeafAItemII
import Nivat.External.Colle.RegionCut

/-!
# Leaf A assembly attempt — `exists_chainData` from `ChainDataGeom.ofParts`

Lane task 2026-09-22. Goal: assemble `exists_chainData` (RegionSteps.lean:1129-1156) using
`ChainDataGeom.ofParts` (ChainAssemble.lean) and available item (ii) producers.

## Strategy
1. List all 25 binders of `ofParts` with their producers (from `#check` output)
2. Attempt assembly for binders with producers
3. Document missing producers with their paper citations
-/

set_option autoImplicit false

namespace Nivat.LeafAWire

open Nivat Nivat.LE2 Nivat.MaxEnv Nivat.Colle35 Nivat.ChainAsm

/-! ## Step 1: Inventory of `ChainDataGeom.ofParts` binders — producer analysis

From `#check @Nivat.Colle35.ChainDataGeom.ofParts`, the 25 hypotheses with producer status:

**Chain block (6):**
1. `envShift` — FREE (Env shift property, `ItemIIRec` doesn't use this, `ofParts` discharges it from `Env` alone)
2. `envB` — **ItemIIRec.envB_ch** (`:174`)
3. `maxA` — **ItemIIRec.maxA_ch** (needs checking)
4. `subBA` — **ItemIIRec.subBA_ch**
5. `subAB` — **ItemIIRec.subAB_ch**
6. `AhatMono` — **NO PRODUCER** (LEAF-A.md: proven false under item (ii) chain, needs subsequence extraction per `:498-504`)

**Shell block (9):**
7. `hsweep` — depends on `nJ vJ1` choice
8. `hfin` — depends on `kk` and finiteness of `A i`
9. `hhp` — depends on `nJ cJ` and `hatOf` placement
10. `hswept` — depends on limit set construction
11. `ahat_nonempty` — depends on chain non-emptiness
12. `shellSubStrip` — **NO PRODUCER** (ChainAssemble.lean:34-39 explicitly states it stays a hypothesis)
13. `escape` — depends on `hatOf` not filling half-plane
14. `shellEnv` — depends on shell being Env eventually
15. `fillCover` — **NO PRODUCER** (b3_colle2.txt:518, needs `S` generating)

**Face block (4):**
16. `F : FaceBlock S nJ vJ` — depends on `S nJ vJ` data
17. `gen_eq : gen = F.a'` — FREE from `F`
18. `vJ_prim : Primitive vJ` — depends on `vJ` choice
19. `nJ_prim : Primitive nJ` — depends on `nJ` choice

**Region block (4):**
20. `bottom` — **NO PRODUCER** (b3_colle2.txt:518, constructive but not yet coded)
21. `rec_p` — depends on `p` choice and limit set
22. `dot_nJ_p : dot nJ p ≠ 0` — depends on `nJ p` transversality
23. `rec_vJ` — **RecVJ.lean has conditional producer** (needs checking: may replace with `bottom`)

**ℓ_ι side (3):**
24. `ahat_halfPlane_L` — depends on `cL` definition
25. `ahat_attained_L` — depends on limit set non-empty
26. `nfp_L` — **ItemII.nfp_of_itemII** (via `Exhausts`)

**Data fields:** `η xper vl p S gen Env B A u kk vJ1 nJ cJ vJ cL` — some from `exists_chainData` signature, others from recursion construction.

-/

/-! ## Step 2: Producer verification from actual `#check` results

Checking ItemIIRec exports to understand what's available for assembly.
-/

section ProducerCheck

-- The following compiles if the producers exist
variable {ξ xper : Config ℤ} {S : Finset (ℤ × ℤ)} {vl nℓ : ℤ × ℤ} {cz : ℤ}
variable (c : AenvfixProbe.Ctx ξ xper S vl nℓ) (s₀ : AenvfixProbe.St ξ xper S nℓ cz)

-- Chain block producers (4 of 6)
example (i : ℕ) : EnvOf (↑S : Set (ℤ × ℤ)) (AenvfixProbe.chB c s₀ i) :=
  AenvfixProbe.envB_ch c s₀ i

example (i : ℕ) : IsMaxEnvIn (EnvOf (↑S : Set (ℤ × ℤ)))
    (canonA ξ xper vl (AenvfixProbe.chB c s₀) (AenvfixProbe.chU c s₀) i)
    (AenvfixProbe.chA c s₀ i) :=
  AenvfixProbe.maxA_ch c s₀ i

example (i : ℕ) : AenvfixProbe.chB c s₀ i ⊆ AenvfixProbe.chA c s₀ i :=
  AenvfixProbe.subBA_ch c s₀ i

example (i : ℕ) : AenvfixProbe.chA c s₀ i ⊆ AenvfixProbe.chB c s₀ (i + 1) :=
  AenvfixProbe.subAB_ch c s₀ i

-- ItemII and Exhausts
example : ItemII (AenvfixProbe.chB c s₀) nℓ cz :=
  AenvfixProbe.itemII_ch c s₀

example : Exhausts (AenvfixProbe.chA c s₀) nℓ cz :=
  AenvfixProbe.exhausts_ch c s₀

end ProducerCheck

/-! ## Step 3: Defining `kk` and feeding `exists_subseq_chain`

**Paper citation:** b3_colle2.txt:488-490

"Let `g₁ ∈ A₁` denote the final point of `A₁ ∩ ℓ⁻` with respect to the orientation of `ℓ⁻`
and, for each `i > 1`, let `k_i ∈ ℕ` be such that the final point of `(A_i - k_i v⃗_ℓ) ∩ ℓ⁻`
coincides with `g₁`. Setting `Â_i := A_i - k_i v⃗_ℓ` for all `i ∈ ℕ`, where `k₁ = 0`."

The shift `k_i` aligns the `ℓ⁻`-support line of `A_i` with that of `A₁`. Since `x_per` is periodic
along `vl` (from `hpartner` via `exists_preamble_pair`), the alignment can be taken modulo the
period, and `:496` extracts a subsequence to make `k_i` stabilize modulo period.

For the ItemIIRec chain, `suppVal (chA c s₀ i) (-nℓ) = -cz` for all `i` (ItemIIRec.suppVal_stepA),
so the support line is already constant. The shift `kk i` is then determined by aligning a chosen
anchor point `g₁ ∈ A 0 ∩ ℓ⁻` across all stages.
-/

section KKDefinition

variable {ξ xper : Config ℤ} {S : Finset (ℤ × ℤ)} {vl nℓ : ℤ × ℤ} {cz : ℤ}
variable (c : AenvfixProbe.Ctx ξ xper S vl nℓ) (s₀ : AenvfixProbe.St ξ xper S nℓ cz)

/-- The anchor point `g₁` from b3_colle2.txt:488: a point in `A₀ ∩ ℓ⁻` (i.e., on the support line
`dot nℓ z = cz`). We take it to be any such point; the paper's "final point with respect to
orientation" is a choice among the support points, any of which serves for alignment. -/
noncomputable def anchorPoint (hne : (AenvfixProbe.chA c s₀ 0).Nonempty) : ℤ × ℤ :=
  let henvA := (AenvfixProbe.stepA_spec c (AenvfixProbe.chain c s₀ 0)).1
  Classical.choose (exists_suppVal_eq (c.hfin _ henvA) hne (-nℓ))

theorem anchorPoint_mem (hne : (AenvfixProbe.chA c s₀ 0).Nonempty) :
    anchorPoint c s₀ hne ∈ AenvfixProbe.chA c s₀ 0 := by
  let henvA := (AenvfixProbe.stepA_spec c (AenvfixProbe.chain c s₀ 0)).1
  exact (Classical.choose_spec (exists_suppVal_eq (c.hfin _ henvA) hne (-nℓ))).1

theorem anchorPoint_suppVal (hne : (AenvfixProbe.chA c s₀ 0).Nonempty) :
    dot (-nℓ) (anchorPoint c s₀ hne) = suppVal (AenvfixProbe.chA c s₀ 0) (-nℓ) := by
  let henvA := (AenvfixProbe.stepA_spec c (AenvfixProbe.chain c s₀ 0)).1
  exact (Classical.choose_spec (exists_suppVal_eq (c.hfin _ henvA) hne (-nℓ))).2

theorem anchorPoint_level (hne : (AenvfixProbe.chA c s₀ 0).Nonempty) :
    dot nℓ (anchorPoint c s₀ hne) = cz := by
  have h := anchorPoint_suppVal c s₀ hne
  have hsup : suppVal (AenvfixProbe.chA c s₀ 0) (-nℓ) = -cz :=
    AenvfixProbe.suppVal_stepA c (AenvfixProbe.chain c s₀ 0)
  rw [hsup, dot_neg_left] at h
  linarith

end KKDefinition

/-! ## Step 3b: Proper `kk` construction via Finset.max'

Per team-lead: `hatOf A kk vl i := {z | z + kk i • vl ∈ A i}`, so `g₁ ∈ hatOf … i` means
`g₁ + kk i • vl ∈ A i`. By b3_colle2.txt:488, `kk i` is the endpoint of the vl-ray from `g₁`
within `A i`. Construction: take `Finset.max'` of `{k : ℕ | g₁ + k • vl ∈ A i}`.
-/

section KKConstruction

variable {ξ xper : Config ℤ} {S : Finset (ℤ × ℤ)} {vl nℓ : ℤ × ℤ} {cz : ℤ}
variable (c : AenvfixProbe.Ctx ξ xper S vl nℓ) (s₀ : AenvfixProbe.St ξ xper S nℓ cz)

/-- `A` is monotone: `A i ⊆ A j` for `i ≤ j`, from `subBA` and `subAB` chaining. -/
theorem A_mono (i j : ℕ) (hij : i ≤ j) :
    AenvfixProbe.chA c s₀ i ⊆ AenvfixProbe.chA c s₀ j := by
  induction hij with
  | refl => rfl
  | step hij ih =>
    calc AenvfixProbe.chA c s₀ i
      _ ⊆ AenvfixProbe.chA c s₀ _ := ih
      _ ⊆ AenvfixProbe.chB c s₀ (_ + 1) := AenvfixProbe.subAB_ch c s₀ _
      _ ⊆ AenvfixProbe.chA c s₀ (_ + 1) := AenvfixProbe.subBA_ch c s₀ _

/-- The set of positions `k` where `g₁ + k • vl ∈ A i`, as a Finset. -/
noncomputable def rayInA (hvl : vl ≠ 0) (hne : (AenvfixProbe.chA c s₀ 0).Nonempty) (i : ℕ) :
    Finset ℕ := by
  classical
  let g₁ := anchorPoint c s₀ hne
  let hAifin := c.hfin _ (AenvfixProbe.stepA_spec c (AenvfixProbe.chain c s₀ i)).1
  exact Finset.filter (fun k => g₁ + (k : ℤ) • vl ∈ AenvfixProbe.chA c s₀ i)
    (Finset.range (hAifin.toFinset.card + 1))

theorem rayInA_nonempty (hvl : vl ≠ 0) (hne : (AenvfixProbe.chA c s₀ 0).Nonempty) (i : ℕ) :
    (rayInA c s₀ hvl hne i).Nonempty := by
  use 0
  simp only [rayInA, Finset.mem_filter, Finset.mem_range]
  constructor
  · omega
  · have h0 : anchorPoint c s₀ hne ∈ AenvfixProbe.chA c s₀ 0 := anchorPoint_mem c s₀ hne
    have hmono : AenvfixProbe.chA c s₀ 0 ⊆ AenvfixProbe.chA c s₀ i := A_mono c s₀ 0 i (Nat.zero_le i)
    simp only [Nat.cast_zero, zero_smul, add_zero]
    exact hmono h0

/-- `kk i` is the maximal `k` where `g₁ + k • vl ∈ A i`. -/
noncomputable def kkOf (hvl : vl ≠ 0) (hperp : dot nℓ vl = 0)
    (hne : (AenvfixProbe.chA c s₀ 0).Nonempty) : ℕ → ℕ :=
  fun i => (rayInA c s₀ hvl hne i).max' (rayInA_nonempty c s₀ hvl hne i)

theorem kkOf_mem (hvl : vl ≠ 0) (hperp : dot nℓ vl = 0)
    (hne : (AenvfixProbe.chA c s₀ 0).Nonempty) (i : ℕ) :
    anchorPoint c s₀ hne + (kkOf c s₀ hvl hperp hne i : ℤ) • vl ∈ AenvfixProbe.chA c s₀ i := by
  have h := Finset.max'_mem (rayInA c s₀ hvl hne i) (rayInA_nonempty c s₀ hvl hne i)
  simp only [rayInA, Finset.mem_filter] at h
  exact h.2

/-- `A i` is lattice-convex (free from `maxA_ch` via `Enveloped.1.1.latticeConvex`,
`WeaklyEnveloped.latticeConvex`). -/
theorem chA_latticeConvex (i : ℕ) :
    IsLatticeConvexRegion (AenvfixProbe.chA c s₀ i) :=
  (AenvfixProbe.maxA_ch c s₀ i).1.1.latticeConvex

/-- **`kkOf` is maximal, not just a member**: any `t : ℕ` with `g₁ + t • vl ∈ A i` satisfies
`t ≤ kkOf … i`.  This is the `kkOf_max` lemma `lane-leafa` flagged as missing
(`tmp/wip/LeafARecP2.lean`'s docstring).

**Why `t` lands inside `rayInA`'s `Finset.range (card + 1)` domain** (the non-obvious half):
`g₁ ∈ A i` (monotonicity + `anchorPoint_mem`) and `g₁ + t • vl ∈ A i` together with
`A i`'s lattice-convexity (`mem_of_between`) put every `g₁ + k • vl`, `0 ≤ k ≤ t`, inside `A i`;
these `t + 1` points are pairwise distinct (`vl ≠ 0`), so `t + 1 ≤ (A i).toFinset.card`, i.e.
`t < card + 1`. -/
theorem kkOf_max (hvl : vl ≠ 0) (hperp : dot nℓ vl = 0)
    (hne : (AenvfixProbe.chA c s₀ 0).Nonempty) (i : ℕ) (t : ℕ)
    (ht : anchorPoint c s₀ hne + (t : ℤ) • vl ∈ AenvfixProbe.chA c s₀ i) :
    t ≤ kkOf c s₀ hvl hperp hne i := by
  classical
  set g₁ := anchorPoint c s₀ hne with hg₁def
  have hAifin : (AenvfixProbe.chA c s₀ i).Finite :=
    c.hfin _ (AenvfixProbe.stepA_spec c (AenvfixProbe.chain c s₀ i)).1
  have hg₁_in_i : g₁ ∈ AenvfixProbe.chA c s₀ i :=
    A_mono c s₀ 0 i (Nat.zero_le i) (anchorPoint_mem c s₀ hne)
  -- every intermediate point is in `A i`, by lattice convexity.
  have hstep : ∀ k : ℕ, k ≤ t → g₁ + (k : ℤ) • vl ∈ AenvfixProbe.chA c s₀ i := by
    intro k hk
    have hs : g₁ + (0 : ℤ) • vl ∈ AenvfixProbe.chA c s₀ i := by simpa using hg₁_in_i
    have hu : g₁ + (t : ℤ) • vl ∈ AenvfixProbe.chA c s₀ i := ht
    have h1 : (0 : ℤ) ≤ (k : ℤ) := by positivity
    have h2 : (k : ℤ) ≤ (t : ℤ) := by exact_mod_cast hk
    exact Nivat.LE2.mem_of_between (chA_latticeConvex c s₀ i) hs hu h1 h2
  -- the map `k ↦ g₁ + k • vl` is injective on `ℕ` (`vl ≠ 0`).
  have hinj : Function.Injective (fun k : ℕ => g₁ + (k : ℤ) • vl) := by
    intro k1 k2 heq
    simp only at heq
    have heq' : ((k1 : ℤ) - (k2 : ℤ)) • vl = 0 := by
      have := heq
      rw [← sub_eq_zero] at this
      rw [sub_smul]
      rw [show g₁ + (k1 : ℤ) • vl - (g₁ + (k2 : ℤ) • vl) = (k1 : ℤ) • vl - (k2 : ℤ) • vl by abel]
        at this
      linear_combination this
    rcases eq_or_ne vl.1 0 with hv1 | hv1
    · rcases eq_or_ne vl.2 0 with hv2 | hv2
      · exact absurd (Prod.ext hv1 hv2) hvl
      · have : ((k1 : ℤ) - (k2 : ℤ)) * vl.2 = 0 := by
          have := congrArg Prod.snd heq'
          simpa using this
        have hk12 : (k1 : ℤ) - (k2 : ℤ) = 0 := by
          rcases mul_eq_zero.mp this with h | h
          · exact h
          · exact absurd h hv2
        have : (k1 : ℤ) = (k2 : ℤ) := by linarith
        exact_mod_cast this
    · have : ((k1 : ℤ) - (k2 : ℤ)) * vl.1 = 0 := by
        have := congrArg Prod.fst heq'
        simpa using this
      have hk12 : (k1 : ℤ) - (k2 : ℤ) = 0 := by
        rcases mul_eq_zero.mp this with h | h
        · exact h
        · exact absurd h hv1
      have : (k1 : ℤ) = (k2 : ℤ) := by linarith
      exact_mod_cast this
  -- so `t + 1 ≤ card`, i.e. `t` is in `rayInA`'s index range.
  have hmapsub : (Finset.range (t + 1)).image (fun k : ℕ => g₁ + (k : ℤ) • vl) ⊆ hAifin.toFinset := by
    intro z hz
    simp only [Finset.mem_image, Finset.mem_range] at hz
    obtain ⟨k, hk, rfl⟩ := hz
    simp only [Set.Finite.mem_toFinset]
    exact hstep k (by omega)
  have hcard : t + 1 ≤ hAifin.toFinset.card := by
    have himg_card : ((Finset.range (t + 1)).image
        (fun k : ℕ => g₁ + (k : ℤ) • vl)).card = t + 1 := by
      rw [Finset.card_image_of_injective _ hinj, Finset.card_range]
    calc t + 1 = ((Finset.range (t + 1)).image (fun k : ℕ => g₁ + (k : ℤ) • vl)).card := himg_card.symm
      _ ≤ hAifin.toFinset.card := Finset.card_le_card hmapsub
  have ht_mem : t ∈ rayInA c s₀ hvl hne i := by
    simp only [rayInA, Finset.mem_filter, Finset.mem_range]
    have hcard' : hAifin.toFinset.card =
        (c.hfin _ (AenvfixProbe.stepA_spec c (AenvfixProbe.chain c s₀ i)).1).toFinset.card := by
      congr 1
    refine ⟨by rw [← hcard']; omega, ?_⟩
    show g₁ + (t : ℤ) • vl ∈ AenvfixProbe.chA c s₀ i
    exact ht
  exact Finset.le_max' _ _ ht_mem

/-- `g₁ ∈ hatOf A kk vl i` for all `i` (b3_colle2.txt:488 alignment property). -/
theorem g₁_mem_hatOf (hvl : vl ≠ 0) (hperp : dot nℓ vl = 0)
    (hne : (AenvfixProbe.chA c s₀ 0).Nonempty) (i : ℕ) :
    anchorPoint c s₀ hne ∈ hatOf (AenvfixProbe.chA c s₀) (kkOf c s₀ hvl hperp hne) vl i := by
  simp [hatOf]
  exact kkOf_mem c s₀ hvl hperp hne i

/-- `kk i` is monotone for `i ≤ j`, from `A` monotonicity. -/
theorem kkOf_mono (hvl : vl ≠ 0) (_hperp : dot nℓ vl = 0)
    (hne : (AenvfixProbe.chA c s₀ 0).Nonempty) :
    ∀ i j : ℕ, i ≤ j → kkOf c s₀ hvl _hperp hne i ≤ kkOf c s₀ hvl _hperp hne j := by
  intro i j hij
  have hmono := A_mono c s₀ i j hij
  have hkki := kkOf_mem c s₀ hvl _hperp hne i
  have hkki_in_j : anchorPoint c s₀ hne + (kkOf c s₀ hvl _hperp hne i : ℤ) • vl ∈
      AenvfixProbe.chA c s₀ j := hmono hkki
  -- kkOf j is max, so kkOf i ≤ kkOf j
  have h_in_ray : kkOf c s₀ hvl _hperp hne i ∈ rayInA c s₀ hvl hne j := by
    simp only [rayInA, Finset.mem_filter, Finset.mem_range]
    constructor
    · -- kkOf i is in rayInA i, which filters range (card_i + 1), but we need it in range (card_j + 1)
      -- Since A i ⊆ A j and both are finite, we have kkOf i < card_i + 1 ≤ card_j + 1
      have h_in_ray_i : kkOf c s₀ hvl _hperp hne i ∈ rayInA c s₀ hvl hne i := by
        apply Finset.max'_mem
      simp only [rayInA, Finset.mem_filter, Finset.mem_range] at h_in_ray_i
      have hcard : (c.hfin _ (AenvfixProbe.stepA_spec c (AenvfixProbe.chain c s₀ i)).1).toFinset.card ≤
          (c.hfin _ (AenvfixProbe.stepA_spec c (AenvfixProbe.chain c s₀ j)).1).toFinset.card := by
        have hAi : (AenvfixProbe.chA c s₀ i).Finite :=
          c.hfin _ (AenvfixProbe.stepA_spec c (AenvfixProbe.chain c s₀ i)).1
        have hAj : (AenvfixProbe.chA c s₀ j).Finite :=
          c.hfin _ (AenvfixProbe.stepA_spec c (AenvfixProbe.chain c s₀ j)).1
        have : hAi.toFinset ⊆ hAj.toFinset := by
          intro x hx
          simp only [Set.Finite.mem_toFinset] at hx ⊢
          exact hmono hx
        exact Finset.card_le_card this
      omega
    · exact hkki_in_j
  exact Finset.le_max' _ _ h_in_ray

end KKConstruction

/-! ## Step 4: Feeding `exists_subseq_chain` to get AhatMono

Now we assemble the 12 hypotheses of `exists_subseq_chain` from ItemIIRec producers and the
`kkOf` definition above.
-/

section SubseqAssembly

variable {ξ xper : Config ℤ} {S : Finset (ℤ × ℤ)} {vl nℓ : ℤ × ℤ} {cz : ℤ}
variable (c : AenvfixProbe.Ctx ξ xper S vl nℓ) (s₀ : AenvfixProbe.St ξ xper S nℓ cz)
variable (hvl : vl ≠ 0) (hperp : dot nℓ vl = 0)
variable (hne : (AenvfixProbe.chA c s₀ 0).Nonempty)

/-- The reindexed chain with `AhatMono` from b3_colle2.txt:498-504 subsequence extraction.
All three gaps closed inline. -/
theorem exists_subseq_chain_of_itemII (hlatconv : IsLatticeConvexRegion (↑S : Set (ℤ × ℤ))) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      (∀ i, EnvOf (↑S : Set (ℤ × ℤ)) (AenvfixProbe.chB c s₀ (σ i))) ∧
      (∀ i, IsMaxEnvIn (EnvOf (↑S : Set (ℤ × ℤ)))
        (canonA ξ xper vl (fun n => AenvfixProbe.chB c s₀ (σ n))
          (fun n => AenvfixProbe.chU c s₀ (σ n)) i)
        (AenvfixProbe.chA c s₀ (σ i))) ∧
      (∀ i, AenvfixProbe.chB c s₀ (σ i) ⊆ AenvfixProbe.chA c s₀ (σ i)) ∧
      (∀ i, AenvfixProbe.chA c s₀ (σ i) ⊆ AenvfixProbe.chB c s₀ (σ (i + 1))) ∧
      (∀ i, (AenvfixProbe.chA c s₀ (σ i)).Finite) ∧
      ItemII (fun n => AenvfixProbe.chB c s₀ (σ n)) nℓ cz ∧
      Exhausts (fun n => AenvfixProbe.chA c s₀ (σ n)) nℓ cz ∧
      (∀ i j, i ≤ j →
        hatOf (fun n => AenvfixProbe.chA c s₀ (σ n))
          (fun n => kkOf c s₀ hvl hperp hne (σ n)) vl i ⊆
        hatOf (fun n => AenvfixProbe.chA c s₀ (σ n))
          (fun n => kkOf c s₀ hvl hperp hne (σ n)) vl j) := by
  apply LeafAItemII.exists_subseq_chain
  · exact S.finite_toSet
  · -- Gap 1: PosArea S from enveloped_refl and c.harea
    have henv : Enveloped (↑S : Set (ℤ × ℤ)) (↑S : Set (ℤ × ℤ)) :=
      LE2.enveloped_refl (↑S : Set (ℤ × ℤ)) hlatconv
    exact c.harea (↑S : Set (ℤ × ℤ)) henv
  · exact fun i => AenvfixProbe.envB_ch c s₀ i
  · exact fun i => AenvfixProbe.maxA_ch c s₀ i
  · -- Gap 2: Enveloped from IsMaxEnvIn's first projection
    intro i
    exact (AenvfixProbe.maxA_ch c s₀ i).1
  · intro i
    have henvA := (AenvfixProbe.stepA_spec c (AenvfixProbe.chain c s₀ i)).1
    exact c.hfin _ henvA
  · exact fun i => AenvfixProbe.subBA_ch c s₀ i
  · exact fun i => AenvfixProbe.subAB_ch c s₀ i
  · exact kkOf_mono c s₀ hvl hperp hne
  · exact fun i => g₁_mem_hatOf c s₀ hvl hperp hne i  -- Gap 3: stubbed for i > 0
  · exact AenvfixProbe.itemII_ch c s₀
  · exact AenvfixProbe.exhausts_ch c s₀

end SubseqAssembly

/-! ## Step 5: Direct binders from limit set properties

Two of the 21 remaining `ofParts` binders are direct consequences of the limit set definition:
- Binder 7: Finiteness of each `hatOf A kk vl i`
- Binder 10: Nonemptiness of `⋃ i, hatOf A kk vl i`
-/

section LimitSetDirect

variable {ξ xper : Config ℤ} {S : Finset (ℤ × ℤ)} {vl nℓ : ℤ × ℤ} {cz : ℤ}
variable (c : AenvfixProbe.Ctx ξ xper S vl nℓ) (s₀ : AenvfixProbe.St ξ xper S nℓ cz)
variable (hvl : vl ≠ 0) (hperp : dot nℓ vl = 0)
variable (hne : (AenvfixProbe.chA c s₀ 0).Nonempty)

/-- Binder 7: Each `hatOf A kk vl i` is finite.

**Proof:** `hatOf A kk vl i = {z | z + kk i • vl ∈ A i}`. Since `A i` is finite (from `c.hfin`)
and the map `z ↦ z + kk i • vl` is bijective onto its image, `hatOf A kk vl i` is finite. -/
theorem hatOf_finite (i : ℕ) : (hatOf (AenvfixProbe.chA c s₀) (kkOf c s₀ hvl hperp hne) vl i).Finite := by
  have hAi_fin : (AenvfixProbe.chA c s₀ i).Finite :=
    c.hfin _ (AenvfixProbe.stepA_spec c (AenvfixProbe.chain c s₀ i)).1
  -- hatOf A kk vl i = {z | z + kk i • vl ∈ A i} is the image of A i under z ↦ z - kk i • vl
  have : hatOf (AenvfixProbe.chA c s₀) (kkOf c s₀ hvl hperp hne) vl i =
      (fun z => z - (kkOf c s₀ hvl hperp hne i : ℤ) • vl) '' (AenvfixProbe.chA c s₀ i) := by
    ext z
    simp only [hatOf, Set.mem_image, Set.mem_setOf]
    constructor
    · intro hz
      use z + (kkOf c s₀ hvl hperp hne i : ℤ) • vl
      constructor
      · exact hz
      · ring
    · intro ⟨w, hw, heq⟩
      rw [← heq]
      simp only [sub_add_cancel]
      exact hw
  rw [this]
  exact hAi_fin.image _

/-- Binder 10: The limit set `⋃ i, hatOf A kk vl i` is nonempty.

**Proof:** `g₁ ∈ hatOf A kk vl 0` by `g₁_mem_hatOf`, so `g₁ ∈ ⋃ i, hatOf A kk vl i`. -/
theorem limitSet_nonempty :
    (⋃ i, hatOf (AenvfixProbe.chA c s₀) (kkOf c s₀ hvl hperp hne) vl i).Nonempty := by
  use anchorPoint c s₀ hne
  simp only [Set.mem_iUnion]
  use 0
  exact g₁_mem_hatOf c s₀ hvl hperp hne 0

end LimitSetDirect

/-! ## Step 6: Summary

Based on examination of ChainAssemble.lean and ItemIIRec.lean:

### Available producers (chain block, 4 of 6):
- `envB` — **ItemIIRec.envB_ch**
- `maxA` — **ItemIIRec.maxA_ch**
- `subBA` — **ItemIIRec.subBA_ch**
- `subAB` — **ItemIIRec.subAB_ch**

### Available from ItemII:
- `ItemII (chB c s₀) nℓ cz` — **ItemIIRec.itemII_ch** (b3_colle2.txt:474)
- `Exhausts (chA c s₀) nℓ cz` — **ItemIIRec.exhausts_ch** (b3_colle2.txt:495)

### Gap closures:
1. `PosArea S` — closed via `enveloped_refl` + `c.harea`
2. `Enveloped U (A i)` — closed via `maxA_ch.1`
3. `kk` construction — closed via `Finset.max'` of vl-ray from g₁

### Assembly theorem:
- `exists_subseq_chain_of_itemII` produces reindexed chain σ with AhatMono (0 sorry)

### Direct limit set binders:
- `hatOf_finite`: Each `hatOf A kk vl i` is finite
- `limitSet_nonempty`: `⋃ i, hatOf A kk vl i` is nonempty

-/

end LeafAWire

-- Axiom check for the main assembly theorem
#print axioms Nivat.LeafAWire.exists_subseq_chain_of_itemII

#print axioms Nivat.LeafAWire.kkOf_max
