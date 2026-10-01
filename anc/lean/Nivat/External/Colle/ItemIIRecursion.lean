/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.ChainKK
import Nivat.External.Colle.ItemII

/-!
# Item (ii) recursive construction: the entry point for `exists_chainData`

Lane ItemIIRecursion, 2026-09-21. **Consumer**: `exists_chainData` (`RegionSteps.lean`).
Upstream of `RegionSteps`: all imports already in its closure.

## Why this file exists

`ChainRecursion`'s construction `B(i+1) := A i` is dead
(`ChainAsm.not_chainDataGeom_of_chainRecursion`, `ChainAssemble.lean:520`): it traps the chain
in a finite-width band, which cannot house a `ChainDataGeom` that recedes transverse to `vl`.
The only surviving escape valve (LEAF-A.md) is Collé's item (ii), `b3_colle2.txt:474`:

    B_i ⊇ A_{i-1} ∪ ([-i+1, i-1]² ∩ ℋ(ℓ⁻))

This file is the **design document and entry point** for the recursion that implements item (ii).
It does not re-prove what is already on the tree; it **connects** the existing pieces and states
clearly what a producer of `exists_chainData` must compute.

## What the recursion computes (the four-tuple at each step `i`)

原文：b3_colle2.txt:466-504

1. **`B(i+1)`** from item (ii) itself (`:474-476`):
   ```
   B(i+1) ⊇ A i ∪ {z ∈ [-i, i]² | cz ≤ ⟪nℓ, z⟫}
   ```
   The box `[-i, i]² ∩ ℋ(ℓ⁻)` ensures all-direction growth and `⋃ B_i = ℋ(ℓ⁻)`.

2. **`u i`** from orbit closure density (`:480`, Claim 3.6):
   At each step, find `u_i` such that `T^{u_i} η` agrees with `x_per` on `B i`.
   Producer: `Colle36.exists_shift_agreeing_on_finite` (already in the tree).

3. **`k i`** from endpoint alignment (`:488`):
   Choose `k_i` such that the `+v_ℓ` endpoint of `Â_i ∩ ℓ⁻` coincides with a fixed `g₁`.
   Producer: `AItemFour.exists_endpoint_shift` (already in the tree).

4. **`A i`** from maximality (`:484`):
   Among all `E(𝒮_φ)`-enveloped sets `𝒯` with `B i ⊆ 𝒯 ⊆ H_{B_i}(ℓ)` and agreeing on `𝒯`,
   take a maximal one.
   Producer: `exists_maximal_of_subset_finite` (`MaximalEnveloped.lean:227`).

## The existing infrastructure (what's already on the tree)

* **Compatibility** (`ItemIICompat.lean`, §5):
  `itemII_compatible_with_ofParts_hypotheses` proves that under the paper's hypotheses,
  a recursion satisfying item (ii) and all `ofParts` hypotheses exists.

* **The chain construction** (`ItemIIChain.exists_itemII_chain`, imported here):
  Produces `B A u` satisfying item (ii), the chain fields (`envB finB maxA subBA subAB`),
  and `Exhausts A nℓ cz` (`:498`, `⋃ A_i = ℋ(ℓ⁻)`).

* **Endpoint normalization** (`ChainKK.exists_normalised_chain`, imported here):
  Takes the raw item (ii) chain, applies `:488` alignment to get `kk` and `g₁`, tail-shifts
  to make alignment hold at every index, then extracts the subsequence (`:496-504`) along
  which `Â_i ⊆ Â_{i+1}` holds.

* **Exhaustion and placement** (`ItemII.lean`, §1-3):
  From `ItemII B nℓ cz` + chain fields, derives `Exhausts A nℓ cz` and the placement
  `cL = k * cz` (`:922`), discharging the `ℓ_ι` block of `ofParts` (§6).

## What this file provides

1. **Entry point theorem** (`exists_itemII_recursion`): bundles the above into one statement
   with the recursion's output type matching `ChainDataGeom.ofParts`'s input.

2. **Design notes** documenting:
   - Why `B(i+1) := A i` is dead and item (ii) is necessary
   - The four pieces that must be computed at each step
   - How varying `u_i` and `k_i` keep the construction alive

3. **No new proofs**: everything is in `ItemIICompat`, `ChainKK`, `ItemIIChain`. This file
   is glue + documentation.

原文：b3_colle2.txt:474 (item (ii)), :480 (agreement), :484 (maximality), :488 (alignment),
:496-504 (subsequence), :498 (exhaustion)
-/

set_option autoImplicit false

namespace Nivat.ItemIIRecursion

open Nivat Nivat.LE2 Nivat.Colle35

/-! ## §1. The recursion type signature

What `exists_chainData` must produce: the four sequences and their properties. -/

/-- **The recursion output type**: four sequences `B A u kk` with the properties that
`ChainDataGeom.ofParts` (`ChainAssemble.lean:179-226`) requires on the chain side.

Compared to `ChainRecursion`'s output:
- `B(i+1)` is **not** equal to `A i`; it contains `A i` plus a growing box (item (ii)).
- `u : ℕ → ℤ × ℤ` is **not** constant; it varies to maintain agreement on growing `B i`.
- `kk : ℕ → ℕ` is **not** constant zero; it varies per `:488` to keep `Â_i` bounded.

原文：b3_colle2.txt:466-504 -/
structure ItemIIRecursionData (η xper : Config ℤ) (S : Finset (ℤ × ℤ)) (vl nℓ : ℤ × ℤ)
    (cz : ℤ) where
  /-- The sequence of `E(𝒮_φ)`-enveloped sets, growing by item (ii). -/
  B : ℕ → Set (ℤ × ℤ)
  /-- The sequence of maximal enveloped sets. -/
  A : ℕ → Set (ℤ × ℤ)
  /-- The shift sequence making `T^{u_i} η` agree with `x_per` on `B i`. -/
  u : ℕ → ℤ × ℤ
  /-- The normalization sequence pinning `Â_i ∩ ℓ⁻` at `g₁`. -/
  kk : ℕ → ℕ
  /-- The fixed point of `:488`. -/
  g₁ : ℤ × ℤ
  /-- `B i` is `E(𝒮_φ)`-enveloped. -/
  envB : ∀ i, EnvOf (↑S : Set (ℤ × ℤ)) (B i)
  /-- `B i` is finite (from the box bound). -/
  finB : ∀ i, (B i).Finite
  /-- `B i` lies in the half-plane `ℋ(ℓ⁻)`. -/
  hB : ∀ i, ∀ z ∈ B i, cz ≤ dot nℓ z
  /-- `A i` is maximal in the constraint set at step `i`. -/
  maxA : ∀ i, IsMaxEnvIn (EnvOf (↑S : Set (ℤ × ℤ))) (canonA η xper vl B u i) (A i)
  /-- `B i ⊆ A i`. -/
  subBA : ∀ i, B i ⊆ A i
  /-- `A i ⊆ B(i+1)`. -/
  subAB : ∀ i, A i ⊆ B (i + 1)
  /-- `A i` is finite. -/
  hfin : ∀ i, (A i).Finite
  /-- **Item (ii)** (`:474-476`): every box point in the half-plane lies in the corresponding `B`. -/
  itemII : ItemII B nℓ cz
  /-- **Exhaustion** (`:498`): the union of the `A_i` is the half-plane. -/
  exhausts : Exhausts A nℓ cz
  /-- `kk` is monotone. -/
  kk_mono : ∀ i j, i ≤ j → kk i ≤ kk j
  /-- `g₁` lies on `ℓ⁻`. -/
  hg₁ : dot nℓ g₁ = cz
  /-- **Endpoint alignment** (`:488`): `g₁` is the `+v_ℓ` endpoint of `Â_i ∩ ℓ⁻` for every `i`. -/
  halign : ∀ i, IsGreatest {t : ℤ | g₁ + t • vl ∈ hatOf A kk vl i ∧ dot nℓ (g₁ + t • vl) = cz} 0
  /-- **Monotonicity** (`:496-504`, after subsequence): `Â_i ⊆ Â_{i+1}`. -/
  AhatMono : ∀ i j, i ≤ j → hatOf A kk vl i ⊆ hatOf A kk vl j

/-! ## §2. The entry point theorem

This bundles `ChainKK.exists_normalised_chain` with the placement lemmas, providing everything
a producer of `exists_chainData` needs in one statement. -/

/-- **The item (ii) recursion exists** under the paper's hypotheses.

原文：b3_colle2.txt:466-504.  Quantifier ledger (hard rule 7):
* All hypotheses ↔ the standing assumptions of §4 (`:38` case 2, `:402` lattice-convex `U`,
  `:40` primitivity, determinant condition from case 2).
* The conclusion's `B A u kk g₁` ↔ exactly the sequences the paper constructs in `:466-504`.

**Output**: an `ItemIIRecursionData` instance packaging the four sequences with all properties
`ChainDataGeom.ofParts` asks for on the chain side, plus `ItemII`, `Exhausts`, and the alignment.

**What's not here**: the shell block, `bottom`, `fill`, `rec_p`. Those remain genuine obligations
of `exists_chainData`'s producer and are not discharged by item (ii) alone.

**Proof strategy**: call `ChainKK.exists_normalised_chain`, which calls `ItemIIChain` for the
raw chain, `AItemFour` for `:488`, and `LeafAItemII` for the `:496-504` subsequence. -/
theorem exists_itemII_recursion {ξ xper : Config ℤ} {S : Finset (ℤ × ℤ)} {vl nℓ : ℤ × ℤ}
    (cz : ℤ) (hS : LatticeConvex S) (hSne : S.Nonempty)
    (hxper : xper ∈ orbitClosure ξ)
    (hvl : vl ≠ 0) (hvl_prim : Primitive vl)
    (hprim : Primitive nℓ) (hperp : dot nℓ vl = 0)
    (hnℓ' : -nℓ ∈ E (↑S : Set (ℤ × ℤ)))
    {n m : ℤ × ℤ} (hdet : det n m ≠ 0)
    (hn : n ∈ E (↑S : Set (ℤ × ℤ))) (hn' : -n ∈ E (↑S : Set (ℤ × ℤ)))
    (hm : m ∈ E (↑S : Set (ℤ × ℤ))) (hm' : -m ∈ E (↑S : Set (ℤ × ℤ)))
    (hcase2 : Nivat.ColleReg.Case2 ξ xper S vl) :
    ∃ _rd : ItemIIRecursionData ξ xper S vl nℓ cz, True := by
  obtain ⟨B, A, u, kk, g₁, envB, finB, hB, maxA, subBA, subAB, hfin, itemII, exhausts,
    kk_mono, hg₁, halign, AhatMono⟩ :=
    Nivat.ChainKK.exists_normalised_chain cz hS hSne hxper hvl hvl_prim hprim hperp hnℓ'
      hdet hn hn' hm hm' hcase2
  exact ⟨⟨B, A, u, kk, g₁, envB, finB, hB, maxA, subBA, subAB, hfin, itemII, exhausts,
    kk_mono, hg₁, halign, AhatMono⟩, trivial⟩

/-! ## §3. Design notes: why item (ii) is necessary

`ChainRecursion`'s `B(i+1) := A i` is dead (`ChainAsm.not_chainDataGeom_of_chainRecursion`):
it traps the chain in `halfStrip (B 0) vl`, a band of bounded width, but a `ChainDataGeom`
recedes along `v_J` (transverse to `vl`), which requires unbounded width.

Three escape valves were considered (LEAF-A.md):
1. **`kk ≢ 0`**: `tmp/chaindata_kkzero_false.lean` ruled this out under `hchain`.
2. **Backward-growing `B`**: would contradict `subAB : A i ⊆ B(i+1)`.
3. **Non-constant `u`**: necessary but not sufficient alone — the recursion `B(i+1) := A i`
   forces `hchain`, and `not_chainDataGeom_of_chainRecursion` needs no assumption on `u`.

**Only item (ii) survives**: `B(i+1) ⊇ A i ∪ (box ∩ ℋ(ℓ⁻))` grows in all directions inside
the half-plane, breaking the band trap. This is not a workaround; it is Collé's construction
(`:474`), and it makes `⋃ A_i = ℋ(ℓ⁻)` (`:498`), which the placement `cL = k * cz` (`:922`)
depends on.

The recursion **must** compute varying `u_i` (item (iii): "for some `u_i`") and varying `k_i`
(`:488`) to keep `Â_i` bounded and agreeing as `B_i` grows. -/

/-! ## §4. The four pieces at each step (detailed computation recipe)

原文：b3_colle2.txt:474, :480, :484, :488

At step `i`, given `B i` and `A i`:

### 4.1. Compute `B(i+1)` — item (ii)

```
B(i+1) := A i ∪ {z ∈ [-i, i]² | cz ≤ ⟪nℓ, z⟫}
```

The box `[-i, i]² ∩ ℋ(ℓ⁻)` is a **concrete, computable set**: for each `i`, enumerate all
`z` with `|z.1| ≤ i`, `|z.2| ≤ i`, `cz ≤ dot nℓ z`, and take their union with `A i`.

**Key property** (`ItemII.halfPlane_subset_iUnion`, `ItemII.lean:101`): this makes
`⋃ B_i ⊇ ℋ(ℓ⁻)`, and with `B i ⊆ A i` and `A i ⊆ halfStrip (B i) vl`, gives
`Exhausts A nℓ cz` (`exhausts_of_itemII`, `ItemII.lean:129`).

### 4.2. Compute `u i` — agreement

```
u i := (the shift making T^{u_i} η agree with x_per on B i)
```

**Producer**: `Colle36.exists_shift_agreeing_on_finite` (Claim 3.6, `Claim36.lean`).
Input: `xper ∈ orbitClosure ξ`, `(B i).Finite`.
Output: `u_i` such that `∀ z ∈ B i, T u_i ξ z = xper z`.

Since `xper` is in the orbit closure of `ξ`, and `B i` is finite, such a shift exists at
every step. The shifts vary with `i` because `B i` grows.

### 4.3. Compute `A i` — maximality

```
A i := (a maximal E(𝒮_φ)-enveloped set in canonA ξ xper vl B u i)
```

**Producer**: `exists_maximal_of_subset_finite` (`MaximalEnveloped.lean:227`).
Input: the constraint set `canonA ξ xper vl B u i` (which is `{𝒯 : B i ⊆ 𝒯 ⊆ halfStrip (B i) vl,
T^{u_i} η agrees with x_per on 𝒯}`) and a finite bound (from item (i)'s `:472`, which gives
a finite enveloping set).
Output: an `A i` that is `IsMaxEnvIn` over that constraint set.

Maximality is relative to **this step's** constraint set, not a fixed one. As `B i` grows,
the constraint set grows, so maximality at step `i` and step `i+1` are independent statements.

### 4.4. Compute `k i` — endpoint alignment

```
k i := (the shift making the +v_ℓ endpoint of (A i - k_i • v_ℓ) ∩ ℓ⁻ equal g₁)
```

**Producer**: `AItemFour.exists_endpoint_shift` (`AItemFour.lean`, imported by `ChainKK`).
Input: the sequence `A`, the monotonicity `A i ⊆ A j` for `i ≤ j`, the existence of a point
on `ℓ⁻` in each `A i` (from item (i)'s support-line clause `:472`), and the geometry
`nℓ ⊥ vl`, `vl ≠ 0`, `Primitive vl`.
Output: a fixed `g₁ ∈ ℓ⁻` and a sequence `k i` such that for every `i ≥ 1`, `g₁` is the
`+v_ℓ` endpoint of `(A i - k_i • v_ℓ) ∩ ℓ⁻`.

This pins each `Â_i` at the same level along `ℓ⁻`, preventing unbounded drift. The paper
states this at `:488`; the kernel proof is `AItemFour.exists_endpoint_shift`.

**Why varying `k_i` is necessary**: as `A i` grows along `+v_ℓ` (from the growing `B i`),
the un-normalized `A i ∩ ℓ⁻` drifts; subtracting `k_i • v_ℓ` with increasing `k_i` cancels
that drift and keeps `Â_i ∩ ℓ⁻` pinned.

-/

/-! ## §5. Summary: what the producer of `exists_chainData` must do

1. **Call `exists_itemII_recursion`** (this file, above) with the hypotheses from
   `exists_preamble_pair` and the case 2 data.

2. **Extract the four sequences** `B A u kk` from the `ItemIIRecursionData`.

3. **Compute the shell and fill** (not provided by item (ii); separate obligations):
   - `shell i ε := MaxEnv.shell (hatOf A kk vl i) vJ1 nJ cJ ε`
   - `fill i i₀ ε := MaxEnv.genFill S gen (hatOf A kk vl i ∪ shell i₀ ε)`

4. **Prove `bottom`** (the `v_J`-ray, `:500-506` selection of `J`): this is the genuinely new
   input, not derivable from item (ii) alone. `ItemII.lean` §8 documents that `rec_vJ` is
   derivable from `bottom` + `hswept` + convexity, so `bottom` (ii) is the obligation.

5. **Feed everything to `ChainDataGeom.ofParts`** (`ChainAssemble.lean:179`), which will
   discharge all mechanical obligations and produce the `ChainDataGeom`.

**What item (ii) gives you for free** (§6 of `ItemII.lean`):
- `ahat_nonempty`
- The entire `ℓ_ι` block: `cL`, `ahat_halfPlane_L`, `ahat_attained_L`, `nfp_L`
  (from `Exhausts` + `rec_vJ`, via `ell_side_of_exhausts`)

**What item (ii) does not give you**:
- The shell block (`shellInf_sup`, `shellInf_union`, `shellInf_eq`, `shellSubStrip`)
- `bottom` (the `v_J`-ray from `:500-506` face-growth selection)
- `rec_p` (but see `ChainKK.rec_p_forces_backward`: the sign is forced)

The producer's work is therefore: implement §4 (the four computations), prove `bottom`,
and assemble via `ofParts`.

-/

end Nivat.ItemIIRecursion

#print axioms Nivat.ItemIIRecursion.exists_itemII_recursion
