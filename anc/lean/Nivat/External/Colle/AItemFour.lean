/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.MaximalEnveloped
import Nivat.External.Colle.Lemma35
import Nivat.External.Colle.ChainMax
import Nivat.Defs.Config

/-!
# Item (iv) of Colle's chain construction: investigation of maximal agreeing enveloped sets

原文：b3_colle2.txt:480-484

> fixed a sequence `(u_i)` fulfilling the previous item, `A_i` is a **maximal set** with
> respect to partial ordering by inclusion among all `E(𝒮_φ)`-enveloped sets
> `𝒯 ⊂ ℤ²` such that `B_i ⊆ 𝒯 ⊆ H_{B_i}(ℓ)` and `(T^{u_i} η)|𝒯 = x_per|𝒯`

## Status (2026-09-20 corrected)

**Item (iv) is already closed.** The chain-on-main realization is
`Nivat.ProbeUB.exists_maximal_agreeFamily` (`EnvBound.lean:119`), which proves maximal
element existence via the bounded-family route:

- `uniform_bound` (`:72`) derives a finite bound `K` from the agreement constraint and
  disagreement witness `z₀`, proving that the family is uniformly bounded
- `window_finite` (`:93`) constructs the finite window `W(B, vl, K)`
- `exists_maximal_agreeFamily` applies `exists_maximal_of_subset_finite` to obtain the
  maximal element

The mechanism is exactly "agreement constraint itself bounds the family": `uniform_bound`
shows that every agreeing enveloped set avoiding `z₀` is confined to a bounded region,
so the unbounded half-strip `H_{B_i}(ℓ)` in the paper's statement becomes a finite window
in the proof.

**This file's `exists_maximal_agreeing_enveloped` (below)** takes finiteness as a hypothesis
`hW : W.Finite` rather than deriving it as a theorem. This is the substantive difference:
- `EnvBound.uniform_bound` is a **theorem** that proves the bound exists
- `exists_maximal_agreeing_enveloped` assumes the bound via `hW : W.Finite`

Therefore `exists_maximal_agreeing_enveloped` is a **weakened duplicate** of the chain-on-main
result and does not add new content to item (iv).

**Note on `no_maximal_enveloped_halfStrip`**: The counterexample (`MaximalEnveloped.lean:352`)
exhibits a family with no maximal element, but that family has **no agreement constraint**.
It does not refute item (iv), which includes the agreement clause `(T^u η)|𝒯 = x_per|𝒯`.

## What is proved

`exists_maximal_agreeing_enveloped`: a maximal element exists when the family is bounded
by a finite window `W`. This is a partial result superseded by `EnvBound.lean`.

`infinitely_many_boxes_satisfy_agreement`: demonstrates that agreement constraints can be
satisfied by infinitely many enveloped sets, illustrating why the bound must come from the
specific constraint `(T^u η)|𝒯 = x_per|𝒯` combined with disagreement witness `z₀`, not from
general properties of agreement predicates.

## Status

No `sorry`. No `axiom` beyond Mathlib.
-/

namespace Nivat.AItemFour

open Nivat Nivat.LE2 Nivat.MaxEnv

variable {α : Type*}

/-- **Colle item (iv): existence of maximal agreeing enveloped set.**

原文：b3_colle2.txt:480-484

The family of `E(S)`-enveloped sets sandwiched between `B` and the window `W`,
all satisfying agreement predicate `P`, has a maximal element above any given member `T₀`.

The key hypothesis is the **disagreement witness** `w₀ ∈ W` with `¬ P w₀`: this ensures
the family cannot reach all of `W`, hence is bounded. Since the family is bounded by
the finite set `W ∖ {w₀}`, `exists_maximal_of_subset_finite` applies.

**Deviation from source**: Colle writes the agreement as `(T^u η)|𝒯 = x_per|𝒯` and
item (iii) as `(T^u η)|H_{B}(ℓ) ≠ x_per|H_{B}(ℓ)`. Here we abstract both to a predicate
`P : (ℤ × ℤ) → Prop`, with the disagreement witness making the boundedness explicit.

The hypothesis `W.Finite` reflects that Colle's item (iv) is applied to a finite window,
not the entire half-strip: the half-strip is infinite, but the construction works within
a bounded region where disagreement has been witnessed. -/
theorem exists_maximal_agreeing_enveloped
    {S : Set (ℤ × ℤ)} (hS : S.Finite)
    {B W : Set (ℤ × ℤ)} (hB : B.Finite) (hW : W.Finite) (hBsub : B ⊆ W)
    (P : (ℤ × ℤ) → Prop)
    {w₀ : ℤ × ℤ} (hw₀ : w₀ ∈ W) (hPw₀ : ¬ P w₀)
    {T₀ : Set (ℤ × ℤ)}
    (h0 : EnvOf S T₀ ∧ B ⊆ T₀ ∧ T₀ ⊆ W ∧ ∀ z ∈ T₀, P z) :
    ∃ M : Set (ℤ × ℤ),
      (EnvOf S M ∧ B ⊆ M ∧ M ⊆ W ∧ ∀ z ∈ M, P z) ∧
      T₀ ⊆ M ∧
      ∀ M' : Set (ℤ × ℤ),
        (EnvOf S M' ∧ B ⊆ M' ∧ M' ⊆ W ∧ ∀ z ∈ M', P z) →
        M ⊆ M' → M' = M := by
  -- The witness `w₀` where `P` fails ensures no member equals `W`.
  -- Every member is therefore contained in `W ∖ {w₀}`.
  have hbound : ∀ T : Set (ℤ × ℤ),
      (EnvOf S T ∧ B ⊆ T ∧ T ⊆ W ∧ ∀ z ∈ T, P z) →
      T ⊆ (W \ {w₀}) := by
    intro T ⟨_, _, hTW, hTP⟩
    intro z hz
    refine ⟨hTW hz, ?_⟩
    intro heq
    rw [Set.mem_singleton_iff] at heq
    rw [heq] at hz
    exact hPw₀ (hTP w₀ hz)
  -- `W ∖ {w₀}` is finite (finite set minus one point).
  have hWfin : (W \ {w₀}).Finite := Set.Finite.sdiff hW
  -- Apply the finite-family maximal element theorem.
  set Fam : Set (Set (ℤ × ℤ)) :=
    {T | EnvOf S T ∧ B ⊆ T ∧ T ⊆ W ∧ ∀ z ∈ T, P z} with hFam
  obtain ⟨M, hMfam, hT₀M, hMmax⟩ :=
    exists_maximal_of_subset_finite hWfin Fam (fun T hT => hbound T hT) h0
  exact ⟨M, hMfam, hT₀M, fun M' hM' hMM' => hMmax M' hM' hMM'⟩

/-- **Investigation: can the `no_maximal_enveloped_halfStrip` family satisfy an agreement
constraint?**

The counterexample family `famHS` consists of boxes `box (0,0) (k,1)` for all `k ≥ 1`.
These are all `E(sq1)`-enveloped, all lie in the half-strip, and the family has no maximal
element. The question is: can we impose a non-trivial agreement predicate `P : (ℤ × ℤ) → Prop`
such that infinitely many of these boxes satisfy `∀ z ∈ box (0,0) (k,1), P z`?

If **yes**: then agreement alone doesn't bound the family, and item (iv) as literally stated
(with the unbounded half-strip) would require chain closure (Zorn) instead of bounded-family
finiteness.

If **no**: then every non-trivial agreement constraint kills all but finitely many boxes,
so the family becomes finite and a maximal element exists.

This investigation constructs an explicit agreement predicate that infinitely many boxes
satisfy, proving that agreement alone is insufficient to bound the family. -/
theorem infinitely_many_boxes_satisfy_agreement :
    ∃ P : (ℤ × ℤ) → Prop, (∀ z, P z ∨ ¬ P z) ∧  -- decidable
      (∃ z, ¬ P z) ∧  -- non-trivial
      (∀ n : ℕ, ∃ k > n, ∀ z ∈ box ((0 : ℤ), (0 : ℤ)) ((k : ℤ), (1 : ℤ)), P z) := by
  -- Take P z := z.2 ≤ 1. This holds on every box (0,0) (k,1) because all points have
  -- y-coordinate 0 or 1. It's non-trivial because P (0,2) = false.
  refine ⟨fun z => z.2 ≤ 1, ?_, ⟨(0, 2), by norm_num⟩, ?_⟩
  · intro z
    by_cases h : z.2 ≤ 1
    · left; exact h
    · right; exact h
  · intro n
    refine ⟨n + 2, by omega, fun z hz => ?_⟩
    obtain ⟨_, _, h2, h3⟩ := hz
    omega

/-! **Conclusion: item (iv) with the unbounded half-strip requires chain closure, not
bounded-family finiteness.**

The above shows that agreement alone doesn't bound the family: we can construct predicates
where infinitely many enveloped sets in the half-strip satisfy the agreement constraint.
Therefore, `exists_maximal_agreeing_enveloped` with its `W.Finite` hypothesis does **not**
discharge item (iv) as stated in the paper.

The correct approach must be:
1. Prove chain closure: if `C` is a chain of agreeing enveloped sets, is `⋃₀ C` still
   enveloped and agreeing? Then use `exists_maximal_of_chain_closed` (`:241`).
2. **However**, `Enveloped.finite` (`:157`) proves every enveloped set is finite, so an
   infinite ascending chain cannot exist — the union of such a chain cannot be enveloped.
   This means chain closure fails for the same reason as bounded finiteness.

**Status**: Item (iv) as literally stated may be **false**. The paper's "It is easy to see"
elides a gap that neither route (A) nor route (B) can close without additional hypotheses
not present in the text. -/

/-! ## Item (i) continuation: the `:496` subsequence extraction

原文：b3_colle2.txt:496

> Since `x_per ∈ X_η` is a periodic configuration with **period parallel to `ℓ`**, there
> exists an integer `k ≥ 0` such that `T^{k v_ℓ} x_per = T^{k_i v_ℓ} x_per` for
> **infinitely many** `i`. By passing to a subsequence, we can assume this holds for **all** `i`.

This is the pigeonhole step that produces the constant `kk` and the monotonicity `AhatMono`
in `ChainData`. The mechanism: `x_per` is periodic with period `q = t • vl`, so
`T^{k v_ℓ} x_per` only depends on `k mod |t|` — finitely many values. An infinite sequence
`k_i` has infinitely many indices mapping to the same residue class, yielding the constant
subsequence.

**Note** ⚠ 订正 2026-09-25（集成者，第 226 轮）：本条原引 `tmp/aenvfix_kk_forced.lean` 的
`ChainDataGeom.not_exhausts_of_kk_zero`（「2/2 clean」）。**该文件在盘上不存在，该声明全树零定义**
⟹ 引用是死的。活着的替代品：`tmp/wip/hbase_anchor.lean` 的 `not_kkZero_of_anchor`
（lane-tower-hbase 2026-09-25，`check1.sh` EXIT=0，公理全白名单），否掉 `kk ≡ 0` 的依据换成
`ChainKK.lean:114` 的锚点合取项 ＋ 可达性（不是 `Exhausts`）。⟹ 结论不变——
`kk` 必须是 `:490` 的端点归一化，不是平凡取法 `kk i := 0`——但**理由换了，且收据尚在 `tmp/wip/`
未落地**。详见 `ChainKK.lean` 文件头同日订正。 -/

/-- An infinite set of naturals carries a **strictly** monotone enumeration.

`Nivat.Colle35.exists_monotone_of_infinite` (`Lemma35.lean:632`) builds exactly this
function — `strictMono_nat_of_lt_succ hlt` appears inside its proof — but its statement
only exposes `Monotone` plus `n ≤ σ n`, and those two do **not** imply `StrictMono`
(`σ n := max n 5` satisfies both). So the strict version is rebuilt here rather than
derived; `Lemma35.lean` is not touched because its consumer at `:889` destructures the
three-conjunct shape. -/
theorem exists_strictMono_of_infinite {I : Set ℕ} (hI : I.Infinite) :
    ∃ σ : ℕ → ℕ, (∀ n, σ n ∈ I) ∧ StrictMono σ := by
  classical
  have hgt : ∀ n : ℕ, ∃ m, m ∈ I ∧ n < m := by
    intro n
    obtain ⟨m, hm, hm'⟩ := hI.exists_gt n
    exact ⟨m, hm, hm'⟩
  choose f hfI hflt using hgt
  obtain ⟨m₀, hm₀⟩ := hI.nonempty
  refine ⟨fun n => Nat.rec (motive := fun _ => ℕ) m₀ (fun _ p => f p) n, ?_, ?_⟩
  · intro n
    induction n with
    | zero => exact hm₀
    | succ n _ => exact hfI _
  · exact strictMono_nat_of_lt_succ (fun n => hflt _)

/-- 原文：b3_colle2.txt:496

**The `:496` subsequence extraction.** Given a configuration `xper` with period `q` parallel
to `vl` (i.e., `q = t • vl` for some `t ≠ 0`), and any sequence `ks : ℕ → ℕ` of translation
amounts along `vl`, there exists a constant `k` and a strictly monotone subsequence `φ`
such that `T^{k v_ℓ} xper = T^{ks(φ i) v_ℓ} xper` for all `i`.

This is Colle's "by passing to a subsequence, we can assume this holds for all `i`" — the
pigeonhole principle applied to the finite quotient induced by periodicity. -/
theorem exists_const_shift_subseq {α : Type*}
    {xper : Config α} {vl : ℤ × ℤ} {q : ℤ × ℤ}
    (hper : q ∈ Nivat.Per xper)          -- x_per is periodic with period q
    (hq : ∃ t : ℤ, q = t • vl) (hq0 : q ≠ 0)     -- period parallel to ℓ
    (hvl : vl ≠ 0)
    (ks : ℕ → ℕ) :
    ∃ (k : ℕ) (φ : ℕ → ℕ), StrictMono φ ∧
      ∀ i, ∀ z : ℤ × ℤ, xper (z + (k : ℤ) • vl) = xper (z + (ks (φ i) : ℤ) • vl) := by
  obtain ⟨t, rfl⟩ := hq
  have hdet : det (t • vl) vl = 0 := by
    simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
  obtain ⟨k, hk⟩ := Nivat.Colle35.exists_infinite_translate_eq hper hq0 hvl hdet ks
  obtain ⟨σ, hσmem, hσstrict⟩ := exists_strictMono_of_infinite hk
  refine ⟨k, σ, hσstrict, fun i z => ?_⟩
  have heq : Nivat.T ((ks (σ i) : ℤ) • vl) xper = Nivat.T ((k : ℤ) • vl) xper :=
    hσmem i
  show xper (z + (k : ℤ) • vl) = xper (z + (ks (σ i) : ℤ) • vl)
  have h1 : Nivat.T ((ks (σ i) : ℤ) • vl) xper z = xper (z + (ks (σ i) : ℤ) • vl) := rfl
  have h2 : Nivat.T ((k : ℤ) • vl) xper z = xper (z + (k : ℤ) • vl) := rfl
  rw [← h1, ← h2, heq]

/-! ## Item (i) continuation: the `:488` endpoint alignment

原文：b3_colle2.txt:488

> Let `g₁ ∈ A₁` denote the final point of `A₁ ∩ ℓ^(-)` with respect to the orientation of
> `ℓ^(-)` and, for each `i > 1`, let `k_i ∈ ℕ` be such that the final point of
> `(A_i − k_i v⃗_ℓ) ∩ ℓ^(-)` … coincides with `g₁`. Setting `Â_i := A_i − k_i v⃗_ℓ` …, where `k₁ = 0`

This constructs the `kk : ℕ → ℕ` sequence that `ofPartsExhausts` needs. The "final point"
of a finite set on a line, with respect to a direction `vl`, is the point with maximum
`vl`-coordinate. Since `dot nℓ vl = 0` and `vl` primitive, points on `ℓ^(-)` that differ
by `t • vl` have distinct `vl`-coordinates (measured by `t`).

**Note** ⚠ 同上，订正 2026-09-25（集成者，第 226 轮）：原引 `tmp/aenvfix_kk_forced.lean` 的
`ChainDataGeom.not_exhausts_of_kk_zero` 是死引用（文件不存在、声明全树零定义）。
活着的替代品是 `tmp/wip/hbase_anchor.lean` 的 `not_kkZero_of_anchor`（EXIT=0，公理干净，
未落地）。结论不变：`kk` 必须是这条 `:488` 端点定义，不是平凡的 `kk i := 0`。 -/

/-- A finite non-empty set of integers has a greatest element. -/
theorem exists_max_of_finite {T : Set ℤ} (hfin : T.Finite) (hne : T.Nonempty) :
    ∃ m ∈ T, ∀ t ∈ T, t ≤ m := by
  classical
  obtain ⟨x, hx⟩ := hne
  have hxF : x ∈ hfin.toFinset := hfin.mem_toFinset.mpr hx
  refine ⟨hfin.toFinset.max' ⟨x, hxF⟩, hfin.mem_toFinset.mp (Finset.max'_mem _ _), ?_⟩
  intro t ht
  exact Finset.le_max' _ t (hfin.mem_toFinset.mpr ht)

/-- `ℤ`-scaling on `ℤ × ℤ` written componentwise, matching the pair form that
`Nivat.LE2.exists_smul_of_det_eq_zero` produces. -/
theorem zsmul_prod (t : ℤ) (v : ℤ × ℤ) : t • v = (t * v.1, t * v.2) := rfl

/-- `dot` is `ℤ`-linear in its second argument. (`Nivat.LE2.dot_smul` scales the *first*.) -/
theorem dot_zsmul (n : ℤ × ℤ) (t : ℤ) (v : ℤ × ℤ) : dot n (t • v) = t * dot n v := by
  simp only [dot, zsmul_prod]; ring

/-- Two vectors orthogonal to the same non-zero `n` are parallel.

This is the lattice fact that makes the line `ℓ⁻ = {z | ⟪nℓ, z⟫ = cz}` a single
`v_ℓ`-orbit, which is what lets `:488`'s "final point" be indexed by one integer.

⚠ **第 247 轮去重（集成者，§110.2）**：本条与 `Nivat.LE2.det_eq_zero_of_dot_eq_zero`
（`LatticeEdges.lean:110`）**同名同命题**，证明体已换成一行桥接。规范形在 `LatticeEdges`；
本条按 §105 留名（`:306`、`AbsorbEnv.lean:368`、`AGlue.lean:36`、`AhatMono.lean:504` 都在引它）。
⛔ 新代码请直接用 `Nivat.LE2.det_eq_zero_of_dot_eq_zero`。 -/
theorem det_eq_zero_of_dot_eq_zero {n v z : ℤ × ℤ} (hn : n ≠ 0)
    (hv : dot n v = 0) (hz : dot n z = 0) : det v z = 0 :=
  Nivat.LE2.det_eq_zero_of_dot_eq_zero hn hv hz

/-- Every point of the line `{z | ⟪nℓ, z⟫ = cz}` is `p₀ + t • v_ℓ` for a unique `t`. -/
theorem exists_coord_on_line {nℓ vl p₀ q : ℤ × ℤ} {cz : ℤ}
    (hnℓ : nℓ ≠ 0) (hprim : Primitive vl) (hperp : dot nℓ vl = 0)
    (hp₀ : dot nℓ p₀ = cz) (hq : dot nℓ q = cz) :
    ∃ t : ℤ, q = p₀ + t • vl := by
  have hd : det vl (q - p₀) = 0 := by
    refine det_eq_zero_of_dot_eq_zero hnℓ hperp ?_
    simp only [dot, Prod.fst_sub, Prod.snd_sub] at *
    linarith [hp₀, hq]
  obtain ⟨t, ht⟩ := exists_smul_of_det_eq_zero (prim_iff_primitive.mpr hprim) hd
  exact ⟨t, by rw [zsmul_prod, ← ht]; abel⟩

/-- 原文：b3_colle2.txt:488

**The `:488` endpoint alignment — this is the producer of `kk`.**

> Let `g₁ ∈ A₁` denote the final point of `A₁ ∩ ℓ^(-)` with respect to the orientation of
> `ℓ^(-)` and, for each `i > 1`, let `k_i ∈ ℕ` be such that the final point of
> `(A_i − k_i v⃗_ℓ) ∩ ℓ^(-)` coincides with `g₁`. Setting `Â_i := A_i − k_i v⃗_ℓ`, where `k₁ = 0`.

**量词对应原文**:
- `A : ℕ → Set (ℤ × ℤ)` ↔ the family `A_i` of `:484`
- `ℓ^(-)` ↔ `{z | dot nℓ z = cz}`, the support line; `hne` is the paper's tacit
  assumption that every `A_i` meets it (`:472`, `B_i ∩ ℓ_{B_i} ⊂ ℓ^(-)`)
- "final point … with respect to the orientation of `ℓ^(-)`" ↔ the `v_ℓ`-maximum,
  which exists because `A i` is finite (`hfin`) and the line is one `v_ℓ`-orbit
- `k_i ∈ ℕ` ↔ `kk i`; non-negativity is **not** free — it comes from `hmono`, which
  gives `A 1 ⊆ A i`, hence the `i`-th final point is at least as far along `v_ℓ`
- `k₁ = 0` ↔ `kk 1 = 0`
- "the final point of `Â_i ∩ ℓ^(-)` coincides with `g₁`" ↔ `IsGreatest … 0`: the
  `v_ℓ`-offset from `g₁` attained inside `Nivat.Colle35.hatOf A kk vl i` is exactly `0`.

Indexing starts at `1`, as in the paper: `A 0` may sit strictly inside `A 1`, in which
case `g₁` is not reachable at index `0` and the statement is false there. -/
theorem exists_endpoint_shift
    {A : ℕ → Set (ℤ × ℤ)} {vl nℓ : ℤ × ℤ} {cz : ℤ}
    (hfin : ∀ i, (A i).Finite) (hne : ∀ i, (A i ∩ {z | dot nℓ z = cz}).Nonempty)
    (hnℓ : nℓ ≠ 0) (hperp : dot nℓ vl = 0) (hvl : vl ≠ 0) (hprim : Primitive vl)
    (hmono : ∀ i j, i ≤ j → A i ⊆ A j) :
    ∃ (g₁ : ℤ × ℤ) (kk : ℕ → ℕ), kk 1 = 0 ∧ dot nℓ g₁ = cz ∧
      ∀ i, 1 ≤ i →
        IsGreatest {t : ℤ | g₁ + t • vl ∈ Nivat.Colle35.hatOf A kk vl i ∧ dot nℓ (g₁ + t • vl) = cz} 0 := by
  classical
  -- A base point on the line, taken inside `A 1`.
  obtain ⟨p₀, hp₀A, hp₀L⟩ := hne 1
  -- `t ↦ p₀ + t • vl` is injective, so each coordinate set is finite.
  have hinj : Function.Injective (fun t : ℤ => p₀ + t • vl) := by
    intro s t hst
    have h0 : (s - t) • vl = 0 := by
      have := sub_eq_zero.mpr hst
      simpa [sub_smul] using this
    rcases smul_eq_zero.mp h0 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hvl
  -- The `v_ℓ`-coordinates of `A i ∩ ℓ⁻`, read off from `p₀`.
  have hTfin : ∀ i, {t : ℤ | p₀ + t • vl ∈ A i}.Finite :=
    fun i => Set.Finite.preimage hinj.injOn (hfin i)
  have hTne : ∀ i, {t : ℤ | p₀ + t • vl ∈ A i}.Nonempty := by
    intro i
    obtain ⟨q, hqA, hqL⟩ := hne i
    obtain ⟨t, ht⟩ := exists_coord_on_line hnℓ hprim hperp hp₀L hqL
    exact ⟨t, by show p₀ + t • vl ∈ A i; rw [← ht]; exact hqA⟩
  -- `m i` is the `v_ℓ`-coordinate of the final point of `A i ∩ ℓ⁻` (`:488`'s "final point").
  choose m hmMem hmMax using fun i => exists_max_of_finite (hTfin i) (hTne i)
  have hmMem' : ∀ i, p₀ + m i • vl ∈ A i := hmMem
  have hmMax' : ∀ i, ∀ t : ℤ, p₀ + t • vl ∈ A i → t ≤ m i := hmMax
  -- Final points only move forward along `v_ℓ` as the family grows: this is what makes
  -- `k_i` a natural number rather than an integer.
  have hmMono : ∀ i, 1 ≤ i → m 1 ≤ m i :=
    fun i hi => hmMax' i (m 1) (hmono 1 i hi (hmMem' 1))
  have hg₁ : dot nℓ (p₀ + m 1 • vl) = cz := by
    rw [dot_add, dot_zsmul, hperp, mul_zero, add_zero, hp₀L]
  refine ⟨p₀ + m 1 • vl, fun i => (m i - m 1).toNat, by simp, hg₁, ?_⟩
  intro i hi
  have hcast : (((m i - m 1).toNat : ℕ) : ℤ) = m i - m 1 :=
    Int.toNat_of_nonneg (by linarith [hmMono i hi])
  -- Membership in `Â_i` at `v_ℓ`-offset `t` from `g₁` is membership of coordinate `m i + t`.
  have hmem : ∀ t : ℤ,
      ((p₀ + m 1 • vl) + t • vl ∈ Nivat.Colle35.hatOf A (fun j => (m j - m 1).toNat) vl i)
        ↔ p₀ + (m i + t) • vl ∈ A i := by
    intro t
    have harg : (p₀ + m 1 • vl) + t • vl + ((((m i - m 1).toNat : ℕ) : ℤ)) • vl
        = p₀ + (m i + t) • vl := by rw [hcast]; module
    show ((p₀ + m 1 • vl) + t • vl + ((((m i - m 1).toNat : ℕ) : ℤ)) • vl ∈ A i) ↔ _
    rw [harg]
  have hlev : ∀ t : ℤ, dot nℓ ((p₀ + m 1 • vl) + t • vl) = cz := by
    intro t
    rw [dot_add, dot_zsmul, hperp, mul_zero, add_zero, hg₁]
  constructor
  · exact ⟨(hmem 0).mpr (by simpa using hmMem' i), hlev 0⟩
  · rintro t ⟨ht, -⟩
    have := hmMax' i (m i + t) ((hmem t).mp ht)
    linarith

end Nivat.AItemFour

#print axioms Nivat.AItemFour.exists_maximal_agreeing_enveloped
#print axioms Nivat.AItemFour.infinitely_many_boxes_satisfy_agreement
#print axioms Nivat.AItemFour.exists_strictMono_of_infinite
#print axioms Nivat.AItemFour.exists_const_shift_subseq
#print axioms Nivat.AItemFour.exists_max_of_finite
#print axioms Nivat.AItemFour.det_eq_zero_of_dot_eq_zero
#print axioms Nivat.AItemFour.exists_coord_on_line
#print axioms Nivat.AItemFour.exists_endpoint_shift
