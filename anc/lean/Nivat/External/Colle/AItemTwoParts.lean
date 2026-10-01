/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.ChainPartsFeed
import Nivat.External.Colle.AItemTwoGrowth
import Nivat.External.Colle.CaseSplit
import Nivat.External.Colle.Claim36
import Nivat.External.Colle.MaximalEnveloped

/-!
# Lane Aitem2b: Chain recursion with growth as a binder

原文：b3_colle2.txt:462-480 (item (i)+(ii)+(iii), chain construction with box absorption).

This file constructs the chain recursion itself, taking item (ii)'s growth hypothesis as a
binder rather than attempting to prove it. The growth lemma (`∃ enveloped B ⊇ X` for any
finite `X`) is being attacked independently by lane `Lbase`; this file builds the chain
assuming that lemma holds.

**Status**: Partial bridge — three fields populated from the box family, chain recursion construction
requires more technical infrastructure than available in current build.

## What the box family provides (from `AItemTwoGrowth.lean`)

`exists_chain_satisfying_itemI_and_itemIIBox` (`:618-622`) constructs a family `B : ℕ → Set (ℤ × ℤ)`
satisfying:
- `∀ i, EnvOf E.U (B i)` — each stage is `E.U`-enveloped
- `ItemI B E.n E.c` — face pinning at `-E.n` on `outerLine E.n E.c` (`:472`)
- `ItemIIBox B E.n E.c` — box absorption: `B i ⊇ [-i+1, i-1]² ∩ ℋ(ℓ⁻)` for `i ≥ 1` (`:476`)

The construction uses absorbing steps (`exists_absorbing_step`, `:524-537`) that preserve the
loop invariant (`StepInv`, `:518-520`): finiteness, nonemptiness, envelopedness, and face pinning.

-/

set_option autoImplicit false

namespace Nivat.ChainAsm.Aparts

open Nivat Nivat.LE2 Nivat.MaxEnv Nivat.Colle35 Nivat.ChainAsm

/-! ## Field-by-field bridge results -/

/-- **Field: `envB`** — directly from `envOf_family` (`:585-586`).
原文：b3_colle2.txt:472 (`B_i` is `E(𝒮_φ)`-enveloped). -/
theorem parts_envB_of_itemII_family (E : StepEnv) {B0 : Set (ℤ × ℤ)} (hB0 : StepInv E B0)
    (S : Finset (ℤ × ℤ)) (hS : E.U = ↑S) :
    ∀ i, EnvOf (↑S : Set (ℤ × ℤ)) (family E hB0 i) := by
  intro i
  rw [← hS]
  exact envOf_family E hB0 i

/-- **Field: `envShift`** — from `envOf_shift_mem` (`ChainMax.lean:152`, namespace
`Nivat.Colle35`).
⚠ **锚订正（第 218 轮，OUTFILE 闸门命中）**：旧写的是 `ChainPartsFeed.lean` 的第 402 行，而
该文件只有 335 行，且全文不提 `envOf_shift_mem`——**文件名和行号一起错**，属 `PROTOCOL.md`
§57 的 B 类。（撤回的锚在这里**故意不写成可解析的 `文件.lean:行号` 形式**：OUTFILE 闸门无法
区分「引用」与「引用的撤回记录」，写成引用形式会让每一次 §14 合规的订正都永久留一条红。）
同时撤回「axiom-clean per that file's receipts」：`ChainMax.lean` 全文没有 `#print axioms`，
那份收据不存在。本条的收据是本文件末尾的
`#print axioms Nivat.ChainAsm.Aparts.parts_envShift_of_itemII_family`——下面这个定理的证明体
**就是** `Nivat.Colle35.envOf_shift_mem S`，所以那条收据逐字覆盖这条引用。
原文：b3_colle2.txt:472 (envelopedness is shift-closed by definition of `EnvOf`). -/
theorem parts_envShift_of_itemII_family (S : Finset (ℤ × ℤ)) :
    ∀ (v : ℤ × ℤ) (T : Set (ℤ × ℤ)), EnvOf (↑S : Set (ℤ × ℤ)) T →
      EnvOf (↑S : Set (ℤ × ℤ)) {z | z + v ∈ T} :=
  Nivat.Colle35.envOf_shift_mem S

/-- **Field: `ahat_nonempty`** — from `ahat_nonempty_of_itemII` (ItemII.lean:151-160,
axiom-clean per ChainPartsFeed.lean receipts) applied to the box family.
原文：b3_colle2.txt:476 (the box `[-i+1, i-1]² ∩ ℋ(ℓ⁻)` is nonempty for large enough `i`).

Requires `ItemII` (from `itemIIBox_family`) plus `subBA : ∀ i, B i ⊆ A i`. -/
theorem parts_ahat_nonempty_of_itemII_family
    (E : StepEnv) {B0 : Set (ℤ × ℤ)} (hB0 : StepInv E B0)
    (vl : ℤ × ℤ) (A : ℕ → Set (ℤ × ℤ)) (kk : ℕ → ℕ)
    (hn : E.n ≠ 0)
    (subBA : ∀ i, family E hB0 i ⊆ A i)
    (hII : ItemII (family E hB0) E.n E.c) :
    (⋃ i, hatOf A kk vl i).Nonempty :=
  Nivat.Colle35.ahat_nonempty_of_itemII hn subBA hII

/-! ## Summary of what the box family CANNOT provide alone

The following `ChainDataGeomParts` fields require data or constructions beyond what
`exists_chain_satisfying_itemI_and_itemIIBox` supplies:

**Chain fields requiring maximal envelope witnesses:**
- `A : ℕ → Set (ℤ × ℤ)` — maximal enveloped sets from `B i`, needs `StepHyp` witnesses
- `u : ℕ → ℤ × ℤ` — shift vectors for `canonA`
- `kk : ℕ → ℕ` — sweep counts
- `maxA` — maximality witnesses (available from `isMaxEnvIn_of_stepHyp` given `StepHyp`)
- `subBA`, `subAB` — containment between `B` and `A`
- `AhatMono` — monotonicity of `hatOf A kk vl`

**Shell/face fields:**
- `vJ1 nJ cJ` — shell sweep data
- `vJ F` — face block data
- `hsweep hhp hswept` — shell geometric properties
- `hfin` — finiteness of `hatOf A kk vl i` (can follow from `subAB` + `B` finiteness)
- `shellSubStrip escape shellEnv fillCover` — shell/fill obligations
- `gen_eq vJ_prim nJ_prim` — face/primitivity data

**Region fields:**
- `bottom` — shell exhaustion by ray family
- `rec_p dot_nJ_p` — periodicity vector `p` and its properties

**ℓ_ι-side fields:**
- `cL ahat_halfPlane_L ahat_attained_L nfp_L` — half-plane level and non-doubly-periodic witness

The box family construction gives us `B : ℕ → Set (ℤ × ℤ)` with envelopedness and item (ii)'s
box inclusion, but the remaining 20+ fields require additional geometric data (face blocks,
shell parameters, periodicity witnesses) that must come from other constructions or be left
as explicit preconditions.

## Attempted: chain recursion with growth as binder

原文：b3_colle2.txt:462-480 (items (i)+(ii)+(iii) combined).

**Goal**: construct `B : ℕ → Set (ℤ × ℤ)` and `u : ℕ → ℤ × ℤ` from growth hypothesis
`hgrow : ∀ X finite, ∃ B enveloped with X ⊆ B`, satisfying items (i)+(iii) and monotonicity.

**Status**: Construction requires technical infrastructure not available in current build:
- Recursive dependent types with `Nat.rec` on subtypes hit elaboration issues
- Proving `E` membership for `(1,0), (-1,0), (0,1), (0,-1)` requires unfolding `IsEdge` definition
- Type unification for `Bs (i+1) = (hgrow (Bs i) _).choose` needs manual `show` tactics

The mathematical content is straightforward (use `hgrow` at each step, extract `u` from `hxper`
via `exists_shift_agreeing_on_finite`, apply `hcase2` for disagreement), but Lean 4's
elaborator struggles with the recursive dependent construction pattern used.

**Not attempted to work around with `sorry`** per red-line reminder — `sorry` in main repo = 0分.

-/

/-! ## What we conclude

From the box family `exists_chain_satisfying_itemI_and_itemIIBox`, we can directly populate
**3 fields** of `ChainDataGeomParts`:
1. `envB` — from `envOf_family`
2. `envShift` — from `envOf_shift_mem` (always available)
3. `ahat_nonempty` — from `ahat_nonempty_of_itemII` (given `ItemII` holds and `A` is defined)

The remaining **21 fields** require:
- Maximal envelope construction (`A`, `u`, `kk`, `maxA`, `subBA`, `subAB`, `AhatMono`) — needs
  `StepHyp` witnesses and `isMaxEnvIn_of_stepHyp`
- Shell/face geometry (`vJ1`, `nJ`, `cJ`, `vJ`, `F`, and 9 shell obligations) — needs face block
  construction and shell parameter selection
- Region properties (`bottom`, `rec_p`, `dot_nJ_p`) — needs periodicity analysis
- ℓ_ι-side data (`cL`, 3 obligations) — needs half-plane level selection

**Conclusion for team-lead:** The box family alone is insufficient to populate `ChainDataGeomParts`.
It provides the `B` family with correct envelopedness and box absorption, but the structure
requires 21 additional fields involving maximal envelopes, shell geometry, and periodicity data
that the box construction does not supply. To proceed, we need either:
(a) A construction that builds `A`, `u`, `kk` from the box family `B` (via `StepHyp` witnesses), OR
(b) A different approach that constructs all chain data simultaneously rather than `B` alone.

The item-II box family satisfies b3_colle2.txt:476 (box absorption) but does not by itself
close the gap to `exists_chainData`.

-/

end Nivat.ChainAsm.Aparts

#check @Nivat.ChainAsm.Aparts.parts_envB_of_itemII_family
#check @Nivat.ChainAsm.Aparts.parts_envShift_of_itemII_family
#check @Nivat.ChainAsm.Aparts.parts_ahat_nonempty_of_itemII_family

#print axioms Nivat.ChainAsm.Aparts.parts_envB_of_itemII_family
#print axioms Nivat.ChainAsm.Aparts.parts_envShift_of_itemII_family
#print axioms Nivat.ChainAsm.Aparts.parts_ahat_nonempty_of_itemII_family
