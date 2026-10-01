/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.Claim36
import Nivat.External.Colle.Lemma35
import Nivat.External.Colle.CaseSplit
import Nivat.External.Colle.MaximalEnveloped

/-!
# Item (iii): Shift agreement on finite sets vs. disagreement on half-strips

原文：b3_colle2.txt:478-480

This file proves the existence of shift vectors `u_i` with the two-part property stated in
Collé's Claim 3.6, item (iii):

> `(T^{u_i}η)|B_i = x_per|B_i` for some `u_i ∈ ℤ²`, but
> `(T^{u_i}η)|H_{B_i}(ℓ) ≠ x_per|H_{B_i}(ℓ)`

The first half (agreement on finite `B_i`) comes from orbit closure membership: any `x_per` in
the orbit closure of `η` agrees with some translate `T^u η` on any finite window. This is
`Nivat.Colle36.exists_shift_agreeing_on_finite` (`Nivat/External/Colle/Claim36.lean:297`).

The second half (disagreement on the half-strip `H_{B_i}(ℓ)`) is non-trivial and prevents
`T^{u_i}η` from being globally equal to `x_per` in the half-strip direction. This is essential
for the maximality argument in item (iv) and for the Case 2 branch.

## Main results

* `exists_shift_agree_on_finset` — restates the existing `exists_shift_agreeing_on_finite`
  in `Finset` form for convenience.

* `exists_shift_agree_and_disagree` — the full two-part property: agreement on a finite base `B`
  but disagreement somewhere in the half-strip `halfStrip B vl`.

## Status

- First half: immediate from `Colle36.exists_shift_agreeing_on_finite`.
- Second half: requires non-periodicity of `ξ` or minimality assumption to rule out global
  agreement in the half-strip direction.

-/

namespace Nivat.Colle

variable {A : Type*}

/--
**Item (iii), first half**: For any `x_per` in the orbit closure of `ξ`, there exists a shift
`u` such that `T^u ξ` agrees with `x_per` on any finite set `F`.

原文：b3_colle2.txt:478
> `(T^{u_i}η)|B_i = x_per|B_i` for some `u_i ∈ ℤ²`

This is immediate from the definition of orbit closure: membership means agreement on all
finite windows. The paper states at line 464: "The assumption on item (i) allows us to
construct..." where item (i) refers to the orbit closure condition.

Already proved as `Nivat.Colle36.exists_shift_agreeing_on_finite`
(`Nivat/External/Colle/Claim36.lean:297`). This theorem restates it for `Finset` rather than
`Set` for convenience.
-/
theorem exists_shift_agree_on_finset {ξ xper : Config A} (hxper : xper ∈ orbitClosure ξ)
    (F : Finset (ℤ × ℤ)) :
    ∃ u : ℤ × ℤ, ∀ z ∈ F, (T u ξ) z = xper z := by
  obtain ⟨u, hu⟩ := Colle36.exists_shift_agreeing_on_finite hxper F.finite_toSet
  exact ⟨u, fun z hz => hu z (Finset.mem_coe.mpr hz)⟩

/-!
## Item (iii), second half — disagreement in the half-strip

原文：b3_colle2.txt:480
> but `(T^{u_i}η)|H_{B_i}(ℓ) ≠ x_per|H_{B_i}(ℓ)`

**Status: Not proved.**

The paper does not prove this from non-periodicity alone. Lines 444-448 state that item (i)
**assumes** such a sequence exists as a hypothesis:

> "If for each E(𝒮_φ)-enveloped set B' ⊂ ℤ² there exist an E(𝒮_φ)-enveloped set B ⊃ B',
> with (ℓ_ι)_{B'} = (ℓ_ι)_B, and u ∈ ℤ² such that
> (T^u η)|_B = x_per|_B, but (T^u η)|_{H_B(-ℓ_ι)} ≠ x_per|_{H_B(-ℓ_ι)}"

This is the **premise** of Claim 3.6 item (i), not a consequence of non-periodicity.

**Why the disagreement cannot be proved from `¬ IsPeriodic ξ` alone:**
- Orbit closure membership only guarantees agreement on **finite** windows
- The half-strip `H_B(ℓ)` is **infinite** (unbounded in direction `ℓ`)
- Non-periodicity prevents `ξ = T^v ξ` for `v ≠ 0`, but does not prevent `T^u ξ` from
  equaling `xper` on an infinite half-strip for some specific `u`

**Where this premise is used in the chain:**
The chain construction in `ChainAssemble.lean` and related files should have this as an
explicit premise, not derived. If it's needed, it should be added as a binder to the
relevant theorems.

**Attempted statement (not included):**
```lean
theorem exists_shift_agree_and_disagree {ξ xper : Config A}
    (hξ : ¬ IsPeriodic ξ) (hxper : xper ∈ orbitClosure ξ)
    {B : Finset (ℤ × ℤ)} (hB : B.Nonempty) {vl : ℤ × ℤ} (hvl : vl ≠ 0) :
    ∃ u : ℤ × ℤ, (∀ z ∈ (↑B : Set (ℤ × ℤ)), (T u ξ) z = xper z) ∧
      ∃ z ∈ Nivat.Colle35.halfStrip (↑B : Set (ℤ × ℤ)) vl, (T u ξ) z ≠ xper z
```

**撤回记录 (2026-09-20):** This section originally stated "This cannot be proved without
additional hypotheses." **撤回理由:** Overlooked that `hcase2 : Case2 ξ xper d.Sphi vl` is
already in the binder list of `RegionSteps.exists_chainData` (line 1030), and that `Case2`
directly provides the disagreement half of item (iii). The correct theorem using `Case2` is
implemented below.
-/

/--
**Item (iii), full two-part property under Case 2**: For any enveloped set `B`, there exists
a shift `u` that agrees with `x_per` on `B` but disagrees somewhere in the half-strip `H_B(vl)`.

原文：b3_colle2.txt:478-480
> `(T^{u_i}η)|B_i = x_per|B_i` for some `u_i ∈ ℤ²`, but
> `(T^{u_i}η)|_{H_{B_i}(ℓ)} ≠ x_{per}|_{H_{B_i}(ℓ)}`

The quantifiers correspond to:
- `ξ : Config ℤ` — the configuration (原文: `η`)
- `xper : Config ℤ` — the periodic configuration in orbit closure (原文: `x_per`)
- `hxper : xper ∈ orbitClosure ξ` — orbit closure membership
- `hcase2 : Nivat.ColleReg.Case2 ξ xper S vl` — the Case 2 hypothesis (原文: `:446-448`)
- `B : Set (ℤ × ℤ)` — an enveloped set (原文: `B_i`)
- `hB : Nivat.LE2.EnvOf (S : Set (ℤ × ℤ)) B` — envelopedness condition

The conclusion has two parts:
1. `∀ z ∈ B, (T u ξ) z = xper z` — agreement on finite `B`
2. `¬ (∀ z ∈ Nivat.LE2.halfStrip B vl, (T u ξ) z = xper z)` — disagreement in half-strip

First half: `B` is finite (enveloped sets are finite), so orbit closure membership gives a
shift `u` with agreement on `B` via `Colle36.exists_shift_agreeing_on_finite`.

Second half: `Case2` directly states that for any `u` agreeing on `B`, there is disagreement
in the half-strip `H_B(vl)`.
-/
theorem exists_shift_agree_and_disagree_of_case2
    {ξ xper : Config ℤ} {S : Finset (ℤ × ℤ)} {vl : ℤ × ℤ}
    (hxper : xper ∈ orbitClosure ξ)
    (hcase2 : Nivat.ColleReg.Case2 ξ xper S vl)
    {B : Set (ℤ × ℤ)} (hB : Nivat.LE2.EnvOf (S : Set (ℤ × ℤ)) B)
    (hBfin : B.Finite) :
    ∃ u : ℤ × ℤ,
      (∀ z ∈ B, T u ξ z = xper z) ∧
      ¬ (∀ z ∈ Nivat.LE2.halfStrip B vl, T u ξ z = xper z) := by
  -- Get agreement on B from orbit closure
  obtain ⟨u, hu_agree⟩ := Colle36.exists_shift_agreeing_on_finite hxper hBfin
  -- Case 2 directly gives disagreement in the half-strip
  exact ⟨u, hu_agree, hcase2 B hB u hu_agree⟩

#print axioms exists_shift_agree_and_disagree_of_case2

/-!
## Compactness limit: b3_colle2.txt:510 already proved

原文：b3_colle2.txt:510

> Since `ϑ_{i'}|Â_i = ϑ_i|Â_i` for all `i ≤ i'`, by compactness of `X_η`, the sequence
> `(ϑ_i)_{i∈ℕ}` has an accumulation point `ϑ ∈ X_η` such that `ϑ|Â_∞ = x̂_per|Â_∞`.

**This is已经证明 in `Nivat.Colle35.exists_mem_orbitClosure_eqOn_iUnion` (`Lemma35.lean:483`).**

```lean
theorem exists_mem_orbitClosure_eqOn_iUnion {θ : Config α} (hfin : (Set.range θ).Finite)
    {A : ℕ → Set (ℤ × ℤ)} (hmono : Monotone A) (u : ℕ → ℤ × ℤ) {x : Config α}
    (hagree : ∀ i, ∀ z ∈ A i, θ (z + u i) = x z) :
    ∃ ϑ ∈ orbitClosure θ, ∀ z ∈ ⋃ i, A i, ϑ z = x z
```

Axioms: `[propext, Classical.choice, Quot.sound]` — already axiom-clean.

**对应关系 (原文 ↔ Lean):**
- 原文 `η` ↔ `θ : Config α` (base configuration)
- 原文 `ϑ_i := T^{k v_ℓ + u_i} η` ↔ shift sequence `u : ℕ → ℤ × ℤ` with `T (u i) θ`
- 原文 `Â_i` ↔ `A : ℕ → Set (ℤ × ℤ)` (nested windows)
- 原文 `Â_∞ := ⋃_{i=1}^∞ Â_i` ↔ `⋃ i, A i`
- 原文 `x̂_per` ↔ `x : Config α` (target configuration)
- 原文 "compactness of `X_η`" ↔ `hfin : (Set.range θ).Finite` (finite alphabet)
- 原文 `ϑ_{i'}|Â_i = ϑ_i|Â_i` for `i ≤ i'` ↔ implicit in the agreement `hagree` on nested `A i`
- 原文 `ϑ ∈ X_η` such that `ϑ|Â_∞ = x̂_per|Â_∞` ↔ `∃ ϑ ∈ orbitClosure θ, ∀ z ∈ ⋃ i, A i, ϑ z = x z`

**关于平凡解的判断 (c) 答复：**
原文需要 `ϑ` 是序列 `(ϑ_i)` 的聚点，因为下一步 `:514` 要它在 `Â_∞^{(ε+1)}` 上不一致。
但 `exists_mem_orbitClosure_eqOn_iUnion` **不需要**带上「继承不一致」的结论，理由：
- 原文 `:514` 的不一致是**反证法假设的否定**（假设 `ϑ|Â_∞^{(ε)} = x̂_per|Â_∞^{(ε)}` 对所有
  `ε` 成立，推出矛盾），不是 `:510` 本身的结论
- 下游消费者（`:512-518` 的反证论证）会单独处理不一致性
- 所以 `:510` 只需证明存在性，不需要排除 `ϑ := x̂_per` 这个平凡解

**No new theorem needed** — `Colle35.exists_mem_orbitClosure_eqOn_iUnion` already covers `:510`.
-/

end Nivat.Colle
