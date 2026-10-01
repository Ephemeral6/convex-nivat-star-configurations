/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.Claim43
import Nivat.External.Colle.HbaseBridge
import Nivat.External.Colle.L1RegionBuild
import Nivat.External.Colle.ConeRegion
-- **2026-09-21 集成者补 import（盲区 1b：先算受影响集合，再加 import）。**
-- §7 的 `hbase_at_of_sweep_lines_reduceMod` 用 `ColleReg.periodOn_of_periodOn_reduceMod_sub`
-- （`PhiIotaWindow.lean:421`）把 `ZMod p` 上的周期性抬回 `ℤ`。
-- 无环实测：`PhiIotaWindow` 的 import 闭包**不含** `SweepLines`。
-- 受影响集合实测（`SweepLines` 的下游是 `ConeHbase` / `StrictWindow` / `TowerBuild`
-- → `Stage2Index` → `RegionSteps`）：`RegionSteps` 闭包 151 → 151（**新进 0 个**，
-- 三者本已在内）；`StrictWindow` 99 → 100（新进 `PhiIotaWindow`）；
-- `ConeHbase` / `TowerBuild` 96 → 99（新进 `PhiIotaWindow` / `NoEdgePlacement` / `Claim36`）。
import Nivat.External.Colle.PhiIotaWindow

/-!
# `SweepLines` — Paper-faithful line-by-line sweep engine

**原文：b3_colle2.txt:792-804**

This file implements Collé's actual sweep argument from Claim 4.6, which proceeds
**line by line** with no ordering within each line, instead of the lexicographic
enumeration `enum : ℕ → ℕ → ℤ × ℤ` that appears in `HbaseBridge.lean:185`.

## The difference that matters

The current `hbase_at_of_sweep_of_isGeneratingSet` requires at each `enum i j`:

```
z + (enum i j - a) ∈ D ∪ (⋃ i' < i, range (enum i')) ∪ (enum i '' {j' | j' < j})
```

The third term `enum i '' {j' | j' < j}` is the **strict prefix within row `i`**.

**The paper (lines 792-804) has no such thing.** It defines:
- `A₁ := 𝓡_{ι-1} ∩ l₁` where `l₁ := ℓ_B^{(-)}` (the first line)
- extends periodicity from `H_B(ℓ)` to `H_B(ℓ) ∪ A₁` (using the whole line at once)
- then `A₂ := 𝓡_{ι-1} ∩ l₂` where `l₂ := l₁^{(-)}` (the second line)
- extends to `H_B(ℓ) ∪ A₁ ∪ A₂`
- "Proceeding this way, we get by induction" (line :804)

**Line-by-line induction, with no ordering within each line.**

## Why the lexicographic version was refuted

`L1SweepBridge.lean:1604` `not_hwinHoleZ_of_case1` constructs a counterexample where
row 0 is infinite, all at the same level, with no variation in the `vl`-coordinate.
The strict prefix `{j' | j' < j}` of row 0 contains no point at a different level,
so the generating-set window cannot be closed, and the sweep fails.

**In the paper's version**, when conquering line `i`, the window may reach into
`D ∪ (⋃ i' < i, lines i')` — i.e., **the entirety of all previous lines**. If those
lines have varying levels (which they do in any model satisfying the paper's
hypotheses), the window closes.

## This file's deliverable

`hbase_at_of_sweep_lines` — same conclusion as `hbase_at_of_sweep_of_isGeneratingSet`,
but with `lines : ℕ → Set (ℤ × ℤ)` and

```
hwinL : ∀ i, ∀ w ∈ lines i, ∀ z ∈ S.erase a,
  z + (w - a) ∈ D ∪ (⋃ i' < i, lines i')
```

No `j` index, no strict prefix within the line. Each line is conquered as a whole,
in one inductive step.

-/

set_option autoImplicit false

namespace Nivat.SweepLines

open Nivat Nivat.Colle Nivat.Colle41 Nivat.Colle43 Nivat.ColleReg Nivat.HbaseBridge

/-! ## §1  Line-by-line sweep: the engine

原文：b3_colle2.txt:792-804

The outer induction is over lines `ℓ₀, ℓ₁, …`. At step `i`, we have periodicity on
`D ∪ (⋃ i' < i, lines i')`. To conquer line `i`, for each `w ∈ lines i`, the
generating-set window `S.erase a` translated so that `a` sits at `w` must land in
the seed plus all previous lines.

**Correspondence with the paper:**
- `D` ↔ `H_B(ℓ)` (the initial half-strip seed)
- `lines i` ↔ `A_i = 𝓡_{ι-1} ∩ l_i` (the `i`-th line)
- `⋃ i' < i, lines i'` ↔ `A₁ ∪ … ∪ A_{i-1}` (all previous lines)
- The induction conclusion is `PeriodOn (T e ξ) (D ∪ ⋃ i' ≤ i, lines i') (c • vl)`

**Quantifiers:**
- `∀ i : ℕ` — for each line index (paper: "proceeding this way", line :804)
- `∀ w ∈ lines i` — for each point on line `i` (no ordering within the line)
- `∀ z ∈ S.erase a` — for each generator in the punctured generating set
  (paper: "Since `𝒮_{φ_ι}` is a generating set, the knowledge of `T^u η` on
  `H_B(ℓ)` determines uniquely `T^u η` on `A₁`", line :798)
- `z + (w - a) ∈ D ∪ (⋃ i' < i, lines i')` — the translated window lands in
  the seed or in previous lines (no `j' < j` prefix within the current line)

-/

/-- **Line-by-line sweep engine.**  If the generating-set window at each point `w`
of line `i` lands entirely in the seed `D` plus all previous lines, then `x` and `y`
agree on `D ∪ (⋃ i, lines i)`.

原文：b3_colle2.txt:792-804, particularly line :804 "Proceeding this way, we get by
induction". The induction is over line indices `i`, with no ordering within each line. -/
theorem lines_sweep {A : Type*} {η x y : Config A}
    (hx : x ∈ orbitClosure η) (hy : y ∈ orbitClosure η)
    {S : Finset (ℤ × ℤ)} {a : ℤ × ℤ} (hgen : GeneratesAt η S a)
    {D : Set (ℤ × ℤ)} (hD : ∀ z ∈ D, x z = y z)
    (lines : ℕ → Set (ℤ × ℤ))
    (hwinL : ∀ i : ℕ, ∀ w ∈ lines i, ∀ z ∈ S.erase a,
      z + (w - a) ∈ D ∪ (⋃ i' ∈ {i' | i' < i}, lines i')) :
    ∀ i : ℕ, ∀ w ∈ lines i, x w = y w := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ihI =>
    -- At this stage, we have `x = y` on `D ∪ (⋃ i' < i, lines i')` by IH
    have hDprev : ∀ z ∈ D ∪ (⋃ i' ∈ {i' | i' < i}, lines i'), x z = y z := by
      rintro z (hzD | hzU)
      · exact hD z hzD
      · simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hzU
        obtain ⟨i', hi', hzline⟩ := hzU
        exact ihI i' hi' _ hzline
    -- Now conquer line `i`: for each `w ∈ lines i`, the window lands in the seed
    intro w hw
    have key : x (a + (w - a)) = y (a + (w - a)) := by
      refine Nivat.Colle43.agree_at_of_generatesAt hx hy hgen hDprev (w - a) ?_
      exact hwinL i w hw
    have e : a + (w - a) = w := by abel
    rwa [e] at key

/-! ## §2  Packaging with `PeriodOn`

The line sweep gives agreement `x = y` on each line. To conclude `PeriodOn x K h'`,
we package it via `periodOn_of_agree_T` (same as in `HbaseBridge`). -/

/-- **Line-by-line sweep concludes `PeriodOn`.**

原文：b3_colle2.txt:792-804. The paper's conclusion (line :804) is "$(T^u η)|_{𝓡_{ι-1}}$
is periodic with period parallel to `ℓ`". In our setting, `x := T e ξ`, `h' := c • vl`,
`K := chainFull B vl u' b₀ k`, and the hypothesis is that `K ⊆ D ∪ (⋃ i, lines i)`. -/
theorem periodOn_of_lines_sweep {A : Type*} {η x : Config A}
    (hx : x ∈ orbitClosure η)
    {S : Finset (ℤ × ℤ)} {a : ℤ × ℤ} (hgen : GeneratesAt η S a)
    (h' : ℤ × ℤ)
    {D : Set (ℤ × ℤ)} (hD : ∀ z ∈ D, x z = T h' x z)
    (lines : ℕ → Set (ℤ × ℤ))
    (hwinL : ∀ i : ℕ, ∀ w ∈ lines i, ∀ z ∈ S.erase a,
      z + (w - a) ∈ D ∪ (⋃ i' ∈ {i' | i' < i}, lines i'))
    {K : Set (ℤ × ℤ)} (hKL : K ⊆ D ∪ (⋃ i, lines i)) :
    PeriodOn x K h' := by
  have hag : ∀ z ∈ K, x z = T h' x z := by
    intro z hz
    rcases hKL hz with hzD | hzU
    · exact hD z hzD
    · simp only [Set.mem_iUnion] at hzU
      obtain ⟨i, hzline⟩ := hzU
      have : x z = (T h' x) z :=
        lines_sweep hx (T_mem_of_mem_orbitClosure hx h') hgen hD lines hwinL i z hzline
      exact this
  exact periodOn_of_agree_T hag

/-! ## §3  `hbase` from the line sweep

Now we instantiate at `x := T e ξ`, `η := ξ`, `K := chainFull B vl u' b₀ k`,
`h' := c • vl`, matching `HbaseBridge.lean:185`. -/

/-- **`hbase` at index `k` from the line-by-line sweep.**

原文：b3_colle2.txt:792-804

This is the paper-faithful version of `hbase_at_of_sweep_of_isGeneratingSet`. The
only difference is the shape of `hwinL`: it has one `ℕ` index (line number) instead
of two, and no `j' < j` strict prefix within the line.

**Quantifiers:**
- `i : ℕ` — line index (paper: `A_i`, the `i`-th line conquered)
- `w ∈ lines i` — a point on line `i` (no ordering, paper conquers the whole line)
- `z ∈ S.erase a` — a generator in the punctured set (paper: `𝒮_{φ_ι}`)
- The window `z + (w - a)` must land in `D ∪ (⋃ i' < i, lines i')` — the seed plus
  **all** previous lines, not just a prefix within the current line. -/
theorem hbase_at_of_sweep_lines {ξ : Config ℤ} {e : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} {a : ℤ × ℤ} (hS : Nivat.Colle.GeneratesAt ξ S a)
    (ha : a ∈ S) (hconv : Nivat.LatticeConvex (S.erase a))
    {B : Set (ℤ × ℤ)} {vl u' b₀ : ℤ × ℤ} {c : ℤ} (k : ℕ)
    {D : Set (ℤ × ℤ)} (hD : ∀ z ∈ D, (T e ξ) z = T (c • vl) (T e ξ) z)
    (lines : ℕ → Set (ℤ × ℤ))
    (hwinL : ∀ i : ℕ, ∀ w ∈ lines i, ∀ z ∈ S.erase a,
      z + (w - a) ∈ D ∪ (⋃ i' ∈ {i' | i' < i}, lines i'))
    (hKL : chainFull B vl u' b₀ k ⊆ D ∪ (⋃ i, lines i)) :
    Colle41.PeriodOn (T e ξ) (chainFull B vl u' b₀ k) (c • vl) := by
  refine periodOn_of_lines_sweep (T_mem_orbitClosure_self ξ e)
    hS (c • vl) hD lines hwinL hKL

/-! ## §4  Goal 2: Relationship with the lexicographic sweep and sign of `a`

Goal 2a: Monotonicity — the line-based `hwinL` implies the lexicographic `hwin`.
Goal 2b: Does the refutation replay?
Goal 2c: Check the sign of `a` (min vs max). -/

/-- **Goal 2a: Line-based sweep implies lexicographic sweep (monotonicity).**

If `lines i := Set.range (enum i)`, then `hwinL` implies `hwin`. This is straightforward
monotonicity: the line-based RHS `D ∪ (⋃ i' < i, lines i')` equals
`D ∪ (⋃ i' < i, Set.range (enum i'))`, which is contained in the lexicographic RHS
`D ∪ (⋃ i' < i, Set.range (enum i')) ∪ (enum i '' {j' | j' < j})`. -/
theorem hwin_of_hwinL {S : Finset (ℤ × ℤ)} {a : ℤ × ℤ} {D : Set (ℤ × ℤ)}
    (enum : ℕ → ℕ → ℤ × ℤ)
    (hwinL : ∀ i : ℕ, ∀ w ∈ Set.range (enum i), ∀ z ∈ S.erase a,
      z + (w - a) ∈ D ∪ (⋃ i' ∈ {i' | i' < i}, Set.range (enum i'))) :
    ∀ i j : ℕ, ∀ z ∈ S.erase a,
      z + (enum i j - a) ∈
        D ∪ (⋃ i' ∈ {i' | i' < i}, Set.range (enum i')) ∪ (enum i '' {j' | j' < j}) := by
  intro i j z hz
  have : z + (enum i j - a) ∈ D ∪ (⋃ i' ∈ {i' | i' < i}, Set.range (enum i')) :=
    hwinL i (enum i j) ⟨j, rfl⟩ z hz
  exact Or.inl this

/-! ## §5  Goal 2b: Refutation replay (analysis in docstring, theorem removed)

**Analysis:** `L1SweepBridge.not_hwin_of_row_zero_levelConst` (line :749) proves that if
row 0 is infinite, confined to a single `dot (expNormal u' vl)`-level, and some
`z₀ ∈ S.erase a` sits off `a`'s level, then the lexicographic `hwin` fails.

**The refutation uses only `i = 0`, where both RHS are identical.** At `i = 0`:
- Lexicographic RHS: `D ∪ (⋃ i' < 0, range (enum i')) ∪ (enum 0 '' {j' | j' < 0})`
- Line-based RHS: `D ∪ (⋃ i' < 0, lines i')`
- Both `⋃ i' < 0` terms are empty, and `enum 0 '' {j' | j' < 0}` is also empty.
- Therefore both reduce to just `D`, and the counterexample **applies verbatim** to `hwinL`.

**Conclusion:** The line-based sweep does NOT escape the refutation. The problem is not
the indexing structure (lexicographic vs. line-by-line), but the choice of `a` — see Goal 2c.

原文对应：b3_colle2.txt:792-804. The paper assumes `𝒮_{φ_ι}` has no edge parallel to `±ℓ`
(line :792 "Lemma 2.6 implies that `𝒮_{φ_ι}` does not have any edge parallel to `-ℓ` or `ℓ`"),
which forces the translated window to have varying levels. The counterexample satisfies
all formal hypotheses but violates this geometric precondition. -/

/-! ## §5  Goal 2c: Sign of `a` — the paper says argmax

原文：b3_colle2.txt:792-798. The paper translates the generating set so that the
**outward** extreme point (the one farthest from the half-strip) sits on the new line,
and all other points fall **inside** the half-strip. This requires `a` to be the
**maximum**, not minimum, of `dot n ·` over `S`.

The two theorems below establish that taking `argmax` gives the correct orientation. -/

/-- **Goal 2c.1: With `a = argmax`, the translated punctured set falls into the seed.**

原文：b3_colle2.txt:794-798 — "Since `Ŝ_{φ_ι}` is an `η-η̄_{ι₀}`-generating set, the
knowledge of `T^u η` on `H_B(ℓ)` determines uniquely `T^u η` on `A₁`."

The mechanism: for each `w ∈ A₁`, translate `S` so that `a` sits at `w`. If `a` is the
**maximum** of `dot n ·` over `S`, and `w` lies in the seed `{z | dot n z ≤ c}`, then
`∀ z ∈ S.erase a, dot n (z + (w - a)) = dot n z - dot n a + dot n w ≤ dot n w ≤ c`,
so the entire translated punctured set lands in the seed. -/
theorem translate_minus_apex_subset_of_argmax
    {S : Finset (ℤ × ℤ)} {n : ℤ × ℤ} {a : ℤ × ℤ} (ha : a ∈ S)
    (hamax : ∀ z ∈ S, Nivat.LE2.dot n z ≤ Nivat.LE2.dot n a)
    {D : Set (ℤ × ℤ)} {c : ℤ}
    (hD : {z : ℤ × ℤ | Nivat.LE2.dot n z ≤ c} ⊆ D)
    {w : ℤ × ℤ} (hw : Nivat.LE2.dot n w ≤ c) :
    ∀ z ∈ S.erase a, z + (w - a) ∈ D := by
  intro z hz
  apply hD
  have hza : z ∈ S := Finset.mem_of_mem_erase hz
  calc Nivat.LE2.dot n (z + (w - a))
      = Nivat.LE2.dot n z + Nivat.LE2.dot n w - Nivat.LE2.dot n a := by
        simp only [Nivat.LE2.dot, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]
        ring
    _ ≤ Nivat.LE2.dot n a + Nivat.LE2.dot n w - Nivat.LE2.dot n a := by
        gcongr
        exact hamax z hza
    _ = Nivat.LE2.dot n w := by ring
    _ ≤ c := hw

/-! ### 撤回 (2026-09-20, 集成者): `translate_minus_apex_subset_halfStrip` 整条删除

签名是集成者给错的：法向用了 `expNormal u' vl`（满足 `dot n vl = 1`），那是**沿线**坐标，
不是横向坐标。原文 `:792-804` 的归纳是**横向**扫掠（`l₁ := ℓ_B^{(-)}`, `l₂ := l₁^{(-)}`, …），
要的是 `dot m vl = 0` 的 `m`。带 `hwide` 的那版另外还编译不过
（`obtain ⟨g, hg, t, _ht, rfl⟩ := hw` 触发依赖消去）。替代物是横向法向版本，
配 `NoEdgePlacement.unique_argmax_of_no_edge_parallel` 的严格唯一 argmin。 -/

/-! ## §6  Cone step: blocked on uCoord decomposition lemmas

原文：b3_colle2.txt:792-804

TARGET for `wedgeResidualR_of_case1_of_cone_at_base` binder `hcone`. **Not wireable this
round** — consumer is over wrong set until OPEN.md #15 resolves.

```lean
theorem hcone_coneStep_of_window
    {B : Set (ℤ × ℤ)} {Sw : Finset (ℤ × ℤ)} {vl u' nℓ a₀ : ℤ × ℤ} {cz : ℤ}
    (hperp : Nivat.LE2.dot nℓ vl = 0)
    (hnu : Nivat.LE2.dot nℓ u' = -1)
    (hstrict : ∀ z ∈ Sw.erase a₀, Nivat.LE2.dot nℓ a₀ < Nivat.LE2.dot nℓ z)
    (hcorner : ∀ z ∈ Sw, 0 ≤ Nivat.LE2.uCoord u' vl a₀ z)
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) :
    ∀ w ∈ Nivat.ConeRegion.coneRegion B vl u', Nivat.LE2.dot nℓ w < cz →
      ∀ z ∈ Sw.erase a₀, Nivat.LE2.dot nℓ (z + (w - a₀)) < cz →
        z + (w - a₀) ∈ Nivat.ConeRegion.coneRegion B vl u'
```

**Obstruction:** Need lemmas connecting `uCoord u' vl a₀ z` to the basis decomposition
`z - a₀ = s•vl + t•u'`. `L1Line0.lean:93` defines `uCoord u' vl b₀ z := -(det u' vl) * det vl (z - b₀)`,
which gives the `u'`-coefficient in the unimodular basis. With `hcorner : 0 ≤ uCoord u' vl a₀ z`
and `hunimod`, I need:
1. A lemma extracting `t : ℕ` from `0 ≤ uCoord u' vl a₀ z`
2. A lemma extracting the `vl`-coefficient `s : ℕ`
3. A lemma stating `z - a₀ = (s:ℤ)•vl + (t:ℤ)•u'`

Cannot find these in `L1Line0.lean` or `L1StraddleWedge.lean`. Without them, cannot
prove `z + (w - a₀) = (b + (z - a₀)) + (s:ℤ)•vl + (t:ℤ)•u' ∈ coneRegion B vl u'`. -/

/-! ## §7  The sweep in the *reduced* alphabet — `:786`, `:790`, `:792`

原文：b3_colle2.txt:786, :790, :792, :804

`periodOn_of_lines_sweep` (§2) is already stated for an arbitrary alphabet `A`.
`hbase_at_of_sweep_lines` (§3) then throws that generality away by fixing `A := ℤ` and
`η := ξ`, and **that is where the chain stops matching the paper**: Collé's window set
`𝒮_{φ_ι}` at `:792` is a generating set of `η − η̄_{ι₀}` **inside `ZMod p`** (Lemma 2.5,
`AlphabetReduction.isGeneratingSet_psi_at_prime`), never of `η` in `ℤ`.  The two steps that
buy the way back are both in the source:

- `:786` "changing the alphabet if necessary, let `p` be a prime such that `𝒜 ⊆ ℤ_p`" —
  the reduction `ℤ → ZMod p` is injective on `ξ`'s (finite) alphabet, so periods descend;
- `:790` "Note that `η̄_{ι₀}` … is periodic with period parallel to `ℓ`" — the subtracted
  term has the very period `c • vl` we are proving, so it can be added back.

Both are already kernel facts (`ColleReg.periodOn_of_periodOn_reduceMod_sub`,
`PhiIotaWindow.lean:421`).  §7 is the two-line composition: run the §2 engine at
`A := ZMod p`, lift the conclusion to `ℤ`.

**Why this matters for `RegionSteps.lean:2429`.**  The `sorry` there is a binder
`GeneratesAt ξ Sw a₀` — a statement about `ξ` in `ℤ` that the paper never asserts and that is
false for the expected witness `Sw := 𝒮_{φ_ι}`.  `hbase_at_of_sweep_lines_reduceMod` is the
consumer-side shape that makes the *true* statement (`GeneratesAt (reduceMod p ξ − ζbar) Sw a₀`)
sufficient, so the binder can be re-stated rather than discharged. -/

/-- **Descending the base periodicity into the reduced alphabet** (`:786`, `:790`).

原文：b3_colle2.txt:786 — `𝒜 ⊆ ℤ_p`, the alphabet change
原文：b3_colle2.txt:790 — `η̄_{ι₀}` is periodic with period parallel to `ℓ`

The converse direction of `ColleReg.periodOn_of_periodOn_reduceMod_sub`, and the easy one:
reduction mod `p` is a ring map applied pointwise, so it preserves any agreement; and `ζbar`
agrees with itself by `hbar`.  This is what turns the half-strip periodicity of `:788`
(available for `ξ` over `ℤ`) into the hypothesis `hD` that the reduced sweep needs.

Quantifiers:
- `hbar : h ∈ Per ζbar` — `:790`, `η̄_{ι₀}` is `h`-periodic
- `hD` — `:788`, `(T^u η)|_{H_B(ℓ)}` is `h`-periodic
- Conclusion: the same on `D` for the difference configuration `reduceMod p ξ − ζbar`. -/
theorem agree_reduceMod_sub_of_agree {ξ : Config ℤ} {p : ℕ} {ζbar : Config (ZMod p)}
    {D : Set (ℤ × ℤ)} {e h : ℤ × ℤ}
    (hbar : h ∈ Nivat.Per ζbar)
    (hD : ∀ z ∈ D, (T e ξ) z = T h (T e ξ) z) :
    ∀ z ∈ D, (T e (Nivat.Colle.AlphabetReduction.reduceMod p ξ - ζbar)) z
      = T h (T e (Nivat.Colle.AlphabetReduction.reduceMod p ξ - ζbar)) z := by
  intro z hz
  have hξ : ξ (z + e) = ξ (z + h + e) := by
    have := hD z hz
    simpa only [T_apply] using this
  have hζ : ζbar (z + h + e) = ζbar (z + e) := by
    have h0 := congrFun hbar (z + e)
    simp only [T_apply] at h0
    have h' : z + e + h = z + h + e := by abel
    rwa [h'] at h0
  simp only [T_apply, Pi.sub_apply, Nivat.Colle.AlphabetReduction.reduceMod_apply]
  rw [hξ, hζ]

/-- **The line-by-line sweep, run in `ZMod p`, concluded in `ℤ`** (`:786`–`:804`).

原文：b3_colle2.txt:792 — `𝒮_{φ_ι}` generates `η − η̄_{ι₀}` (Lemma 2.5, in `ZMod p`)
原文：b3_colle2.txt:794-804 — the line-by-line induction `A₁, A₂, …`
原文：b3_colle2.txt:790 — add back `η̄_{ι₀}`
原文：b3_colle2.txt:786 — lift from `ZMod p` back to `ℤ`

Quantifiers (per CLAUDE.md hard rule 7):
- `hinj : Set.InjOn (· : ℤ → ZMod p) (Set.range ξ)` — `:786`, `𝒜 ⊆ ℤ_p`
- `hbar : c • vl ∈ Per ζbar` — `:790`, `η̄_{ι₀}` is `c • v⃗_ℓ`-periodic
- `hgen : GeneratesAt (reduceMod p ξ − ζbar) Sw a₀` — `:792`, Lemma 2.5 **in the reduced
  alphabet**; this is the hypothesis the paper actually supplies
- `hD` — `:788`, periodicity on the seed `D` (`= H_B(ℓ)` at the call site), stated for the
  difference configuration; `agree_reduceMod_sub_of_agree` produces it from the `ℤ` version
- `lines`, `hwinL` — `:794-804`, one line at a time, no ordering inside a line
- `hKL : K ⊆ D ∪ ⋃ lines` — the covering (`ConeLines.coneRegion_subset_halfStrip_union_lines`)
- Conclusion: `PeriodOn (T e ξ) K (c • vl)` — `:804`, `(T^u η)|_{𝓡_{ι-1}}` is periodic with
  period parallel to `ℓ`, back in the **original** alphabet.

⚠ Note what is *not* assumed: nothing about `ξ` being generated by `Sw`.  That assumption
(`GeneratesAt ξ Sw a₀`, the shape of the `RegionSteps.lean:2429` binder) is our invention and
is false for `Sw := 𝒮_{φ_ι}`; the paper only ever generates the difference. -/
theorem hbase_at_of_sweep_lines_reduceMod {ξ : Config ℤ} {p : ℕ}
    {ζbar : Config (ZMod p)} {e : ℤ × ℤ}
    {Sw : Finset (ℤ × ℤ)} {a₀ vl : ℤ × ℤ} {c : ℤ}
    (hinj : Set.InjOn (fun a : ℤ => (a : ZMod p)) (Set.range ξ))
    (hbar : c • vl ∈ Nivat.Per ζbar)
    (hgen : GeneratesAt (Nivat.Colle.AlphabetReduction.reduceMod p ξ - ζbar) Sw a₀)
    {D : Set (ℤ × ℤ)}
    (hD : ∀ z ∈ D, (T e (Nivat.Colle.AlphabetReduction.reduceMod p ξ - ζbar)) z
      = T (c • vl) (T e (Nivat.Colle.AlphabetReduction.reduceMod p ξ - ζbar)) z)
    (lines : ℕ → Set (ℤ × ℤ))
    (hwinL : ∀ i : ℕ, ∀ w ∈ lines i, ∀ z ∈ Sw.erase a₀,
      z + (w - a₀) ∈ D ∪ (⋃ i' ∈ {i' | i' < i}, lines i'))
    {K : Set (ℤ × ℤ)} (hKL : K ⊆ D ∪ (⋃ i, lines i)) :
    Colle41.PeriodOn (T e ξ) K (c • vl) := by
  have hsub : Colle41.PeriodOn
      (T e (Nivat.Colle.AlphabetReduction.reduceMod p ξ - ζbar)) K (c • vl) :=
    periodOn_of_lines_sweep
      (T_mem_orbitClosure_self (Nivat.Colle.AlphabetReduction.reduceMod p ξ - ζbar) e)
      hgen (c • vl) hD lines hwinL hKL
  exact Nivat.ColleReg.periodOn_of_periodOn_reduceMod_sub hinj hbar hsub

/-- **`:786` + `:790` + `:792` bundled into one hypothesis.**

原文：b3_colle2.txt:786 — "changing the alphabet if necessary, let `p` be a prime such that
`𝒜 ⊆ ℤ_p`"
原文：b3_colle2.txt:790 — "Note that `η̄_{ι₀}` … is periodic with period parallel to `ℓ`"
原文：b3_colle2.txt:792 — `𝒮_{φ_ι}` is a generating set of `η − η̄_{ι₀}`

This is what Collé actually has available at the point where the line-by-line sweep starts.
Each conjunct is one clause of the source, in order:

- `p`, `hinj` — the prime of `:786` and the injectivity of `ℤ → ZMod p` on `ξ`'s alphabet;
- `ζbar`, `hbar` — the periodic part `η̄_{ι₀}` of `:790`, with the very period `h` the sweep
  is about to propagate;
- `hgen` — Lemma 2.5 at `:792`, a generating set of the **difference**, at the apex `a₀`.

It is strictly weaker than `GeneratesAt ξ Sw a₀` (`reducedGeneratesAt_of_generatesAt`, via
`p = 0`, `ζbar = 0`), which is the shape the chain used to demand and which the source never
asserts. -/
def ReducedGeneratesAt (ξ : Config ℤ) (Sw : Finset (ℤ × ℤ)) (a₀ h : ℤ × ℤ) : Prop :=
  ∃ (p : ℕ) (ζbar : Config (ZMod p)),
    Set.InjOn (fun a : ℤ => (a : ZMod p)) (Set.range ξ) ∧
    h ∈ Nivat.Per ζbar ∧
    GeneratesAt (Nivat.Colle.AlphabetReduction.reduceMod p ξ - ζbar) Sw a₀

/-- **The old hypothesis implies the new one**, so the refactor loses nothing.

Take `p = 0` (`ZMod 0 = ℤ`, and `Int.cast : ℤ → ℤ` is the identity, hence injective) and
`ζbar = 0` (every vector is a period of the constant-zero configuration).  Then
`reduceMod 0 ξ - 0 = ξ`. -/
theorem reducedGeneratesAt_of_generatesAt {ξ : Config ℤ} {Sw : Finset (ℤ × ℤ)} {a₀ h : ℤ × ℤ}
    (hgen : GeneratesAt ξ Sw a₀) : ReducedGeneratesAt ξ Sw a₀ h := by
  refine ⟨0, 0, ?_, ?_, ?_⟩
  · intro a _ b _ hab
    simpa using hab
  · show Nivat.T h (0 : Config (ZMod 0)) = 0
    funext z; rfl
  · have : Nivat.Colle.AlphabetReduction.reduceMod 0 ξ - 0 = ξ := by
      funext z
      simp only [Pi.sub_apply, Pi.zero_apply, sub_zero,
        Nivat.Colle.AlphabetReduction.reduceMod_apply]
      first
        | exact Int.cast_id
        | exact congrFun Int.cast_id (ξ z)
        | rfl
        | simp
    rwa [this]

/-- **The sweep, consumer-side: `hD` stays in `ℤ`, generation is in the reduced alphabet.**

原文：b3_colle2.txt:786-804

Same conclusion as `hbase_at_of_sweep_lines` (`:186`), same `hD` (the `:788` half-strip
periodicity of `T^u η` over `ℤ`), same `lines` / `hwinL` / `hKL`.  The **only** change is the
generation hypothesis: `ReducedGeneratesAt ξ Sw a₀ (c • vl)` instead of
`GeneratesAt ξ Sw a₀`.  That single token is the difference between a hypothesis the paper
supplies at `:792` and one it never states.

The proof pushes `hD` down into the reduced alphabet (`agree_reduceMod_sub_of_agree`), runs
the §2 engine there, and lifts the conclusion back (`hbase_at_of_sweep_lines_reduceMod`). -/
theorem hbase_at_of_reducedGeneratesAt {ξ : Config ℤ} {e : ℤ × ℤ}
    {Sw : Finset (ℤ × ℤ)} {a₀ vl : ℤ × ℤ} {c : ℤ}
    (hR : ReducedGeneratesAt ξ Sw a₀ (c • vl))
    {D : Set (ℤ × ℤ)} (hD : ∀ z ∈ D, (T e ξ) z = T (c • vl) (T e ξ) z)
    (lines : ℕ → Set (ℤ × ℤ))
    (hwinL : ∀ i : ℕ, ∀ w ∈ lines i, ∀ z ∈ Sw.erase a₀,
      z + (w - a₀) ∈ D ∪ (⋃ i' ∈ {i' | i' < i}, lines i'))
    {K : Set (ℤ × ℤ)} (hKL : K ⊆ D ∪ (⋃ i, lines i)) :
    Colle41.PeriodOn (T e ξ) K (c • vl) := by
  obtain ⟨p, ζbar, hinj, hbar, hgen⟩ := hR
  exact hbase_at_of_sweep_lines_reduceMod hinj hbar hgen
    (agree_reduceMod_sub_of_agree hbar hD) lines hwinL hKL

/-- **`hbase_at_of_sweep_lines` with the source's own generation hypothesis** (`:786-804`).

原文：b3_colle2.txt:792 — `𝒮_{φ_ι}` generates `η − η̄_{ι₀}` in `ZMod p`, **not** `η` in `ℤ`

Identical to `hbase_at_of_sweep_lines` (`:186`) in every binder except the first: it asks for
`ReducedGeneratesAt ξ S a (c • vl)` (the `:786`+`:790`+`:792` bundle) instead of
`GeneratesAt ξ S a`.  The unused binders `ha`, `hconv` are kept so that call sites can be
migrated by renaming the lemma and nothing else. -/
theorem hbase_at_of_sweep_lines_reduced {ξ : Config ℤ} {e : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} {a : ℤ × ℤ}
    {B : Set (ℤ × ℤ)} {vl u' b₀ : ℤ × ℤ} {c : ℤ}
    (hR : ReducedGeneratesAt ξ S a (c • vl))
    (_ha : a ∈ S) (_hconv : Nivat.LatticeConvex (S.erase a)) (k : ℕ)
    {D : Set (ℤ × ℤ)} (hD : ∀ z ∈ D, (T e ξ) z = T (c • vl) (T e ξ) z)
    (lines : ℕ → Set (ℤ × ℤ))
    (hwinL : ∀ i : ℕ, ∀ w ∈ lines i, ∀ z ∈ S.erase a,
      z + (w - a) ∈ D ∪ (⋃ i' ∈ {i' | i' < i}, lines i'))
    (hKL : Nivat.ColleReg.chainFull B vl u' b₀ k ⊆ D ∪ (⋃ i, lines i)) :
    Colle41.PeriodOn (T e ξ) (Nivat.ColleReg.chainFull B vl u' b₀ k) (c • vl) :=
  hbase_at_of_reducedGeneratesAt hR hD lines hwinL hKL

/-- **`:790` verbatim: "periodic with period *parallel to* `ℓ`"** — direction, not multiple.

原文：b3_colle2.txt:790 — "Note that `η̄_{ι₀}` … is periodic with period parallel to `ℓ`"

`ReducedGeneratesAt` fixes the period vector `h`, which is what the deep call sites want.  But
at the *top* of the chain (`claim46_of_case1`) the period `c • vl` is not a binder — it is
produced inside, from `Per xper`.  What the source gives there is only the **direction**:
`η̄_{ι₀}` has *some* nonzero period parallel to `ℓ`.  That is this predicate.

`reducedGeneratesAt_of_dir` closes the gap: any common multiple works, and `Per ζbar` is a
subgroup, so `c₀ • vl ∈ Per ζbar` gives `(c * c₀) • vl ∈ Per ζbar` for every `c`. -/
def ReducedGeneratesAtDir (ξ : Config ℤ) (Sw : Finset (ℤ × ℤ)) (a₀ vl : ℤ × ℤ) : Prop :=
  ∃ (p : ℕ) (ζbar : Config (ZMod p)) (c₀ : ℤ), 0 < c₀ ∧
    Set.InjOn (fun a : ℤ => (a : ZMod p)) (Set.range ξ) ∧
    c₀ • vl ∈ Nivat.Per ζbar ∧
    GeneratesAt (Nivat.Colle.AlphabetReduction.reduceMod p ξ - ζbar) Sw a₀

/-- **From the direction form to the fixed-vector form, by passing to a multiple** (`:790`).

Gives one `c₀ > 0` that works for *every* multiplier `c` simultaneously, which is what a call
site needs: it picks its own `c` from `Per xper` (`L1Line0.exists_pos_zsmul_mem_Per`) and then
runs the sweep at `c * c₀`. -/
theorem reducedGeneratesAt_of_dir {ξ : Config ℤ} {Sw : Finset (ℤ × ℤ)} {a₀ vl : ℤ × ℤ}
    (hR : ReducedGeneratesAtDir ξ Sw a₀ vl) :
    ∃ c₀ : ℤ, 0 < c₀ ∧ ∀ c : ℤ, ReducedGeneratesAt ξ Sw a₀ ((c * c₀) • vl) := by
  obtain ⟨p, ζbar, c₀, hc₀, hinj, hbar, hgen⟩ := hR
  refine ⟨c₀, hc₀, fun c => ⟨p, ζbar, hinj, ?_, hgen⟩⟩
  have : (c * c₀) • vl = c • (c₀ • vl) := by rw [mul_smul]
  rw [this]
  exact AddSubgroup.zsmul_mem _ hbar c

/-- **`ReducedGeneratesAt` at a fixed vector implies the direction form**, provided the vector
is a positive multiple of `vl`.  Together with `reducedGeneratesAt_of_dir` this says the two
forms carry the same content. -/
theorem reducedGeneratesAtDir_of_reducedGeneratesAt {ξ : Config ℤ} {Sw : Finset (ℤ × ℤ)}
    {a₀ vl : ℤ × ℤ} {c : ℤ} (hc : 0 < c) (hR : ReducedGeneratesAt ξ Sw a₀ (c • vl)) :
    ReducedGeneratesAtDir ξ Sw a₀ vl := by
  obtain ⟨p, ζbar, hinj, hbar, hgen⟩ := hR
  exact ⟨p, ζbar, c, hc, hinj, hbar, hgen⟩

/-- The old hypothesis implies the direction form too (`p = 0`, `ζbar = 0`, `c₀ = 1`). -/
theorem reducedGeneratesAtDir_of_generatesAt {ξ : Config ℤ} {Sw : Finset (ℤ × ℤ)}
    {a₀ vl : ℤ × ℤ} (hgen : GeneratesAt ξ Sw a₀) : ReducedGeneratesAtDir ξ Sw a₀ vl :=
  reducedGeneratesAtDir_of_reducedGeneratesAt (c := 1) one_pos
    (by simpa using (reducedGeneratesAt_of_generatesAt (h := (1 : ℤ) • vl) hgen))

/-- **Periodicity descends through `reduceMod`** (`:786`, `:790`).

原文：b3_colle2.txt:786 — the alphabet `𝒜` is embedded in `ℤ_p`, i.e. everything in sight is
read mod `p`; `:790` — `η̄_{ι₀}` is periodic with period parallel to `ℓ`.

The `:790` periodicity is a statement about `η̄_{ι₀}` **in `ℤ`** (it is one of the `m`
one-dimensional components of the decomposition), while `ReducedGeneratesAtDir` needs it about
its mod-`p` reduction.  Reduction is a pointwise map, so it transports periods forward. -/
theorem mem_Per_reduceMod_of_mem_Per {η : Config ℤ} {p : ℕ} {h : ℤ × ℤ}
    (hh : h ∈ Nivat.Per η) :
    h ∈ Nivat.Per (Nivat.Colle.AlphabetReduction.reduceMod p η) := by
  show Nivat.T h (Nivat.Colle.AlphabetReduction.reduceMod p η)
    = Nivat.Colle.AlphabetReduction.reduceMod p η
  funext z
  have h0 := congrFun hh z
  simp only [T_apply] at h0 ⊢
  simp only [Nivat.Colle.AlphabetReduction.reduceMod_apply, h0]

/-- **The `:786`+`:790`+`:792` bundle, assembled from its three source ingredients.**

原文：b3_colle2.txt:786 — pick a prime `p` with `𝒜 ⊆ ℤ_p` (this is `hinj`)
原文：b3_colle2.txt:790 — `η̄_{ι₀}` has a period parallel to `ℓ` (this is `hc₀`/`hper`)
原文：b3_colle2.txt:792 — Lemma 2.5: `𝒮_{φ_ι}` is an `η − η̄_{ι₀}`-generating set
(this is `hgen`, produced on chain by
`AlphabetReduction.isGeneratingSet_psi_at_prime` via `ColleReg.exists_window_strict_at_prime`).

Quantifier-by-quantifier: every binder below is one of those three source clauses, and
nothing else.  In particular there is **no** clause asserting that `Sw` generates `ξ` itself —
that was our invention, and it is exactly what `ReducedGeneratesAtDir` removes.

⚠ The `IsGeneratingSet → GeneratesAt` step needs `LatticeConvex (Sw.erase a₀)`, which the
window producer supplies (`ColleReg.latticeConvex_erase_of_strict_argmin`). -/
theorem reducedGeneratesAtDir_of_isGeneratingSet_sub {ξ η : Config ℤ} {p : ℕ}
    {Sw : Finset (ℤ × ℤ)} {a₀ vl : ℤ × ℤ} {c₀ : ℤ}
    (hinj : Set.InjOn (fun a : ℤ => (a : ZMod p)) (Set.range ξ))
    (hc₀ : 0 < c₀) (hper : c₀ • vl ∈ Nivat.Per η)
    (hgen : Nivat.Colle.IsGeneratingSet
      (Nivat.Colle.AlphabetReduction.reduceMod p ξ
        - Nivat.Colle.AlphabetReduction.reduceMod p η) Sw)
    (ha₀ : a₀ ∈ Sw) (hconv : Nivat.LatticeConvex (Sw.erase a₀)) :
    ReducedGeneratesAtDir ξ Sw a₀ vl :=
  ⟨p, Nivat.Colle.AlphabetReduction.reduceMod p η, c₀, hc₀, hinj,
    mem_Per_reduceMod_of_mem_Per hper, hgen.2.2 a₀ ha₀ hconv⟩

end Nivat.SweepLines

#print axioms Nivat.SweepLines.lines_sweep
#print axioms Nivat.SweepLines.periodOn_of_lines_sweep
#print axioms Nivat.SweepLines.hbase_at_of_sweep_lines
#print axioms Nivat.SweepLines.hwin_of_hwinL
#print axioms Nivat.SweepLines.translate_minus_apex_subset_of_argmax
#print axioms Nivat.SweepLines.agree_reduceMod_sub_of_agree
#print axioms Nivat.SweepLines.hbase_at_of_sweep_lines_reduceMod
#print axioms Nivat.SweepLines.reducedGeneratesAt_of_generatesAt
#print axioms Nivat.SweepLines.hbase_at_of_reducedGeneratesAt
#print axioms Nivat.SweepLines.hbase_at_of_sweep_lines_reduced
#print axioms Nivat.SweepLines.reducedGeneratesAt_of_dir
#print axioms Nivat.SweepLines.reducedGeneratesAtDir_of_reducedGeneratesAt
#print axioms Nivat.SweepLines.reducedGeneratesAtDir_of_generatesAt
#print axioms Nivat.SweepLines.mem_Per_reduceMod_of_mem_Per
#print axioms Nivat.SweepLines.reducedGeneratesAtDir_of_isGeneratingSet_sub
