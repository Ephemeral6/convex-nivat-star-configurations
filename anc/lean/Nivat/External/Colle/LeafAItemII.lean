/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.AhatMono

/-!
# Leaf A, item (ii): `AhatMono` is free once the chain is re-indexed

Lane LeafA, 2026-09-21.

## What this file is for

`AhatMono : ∀ i j, i ≤ j → hatOf A kk vl i ⊆ hatOf A kk vl j` (`ChainAssemble.lean:186`) is
the one binder of `ChainDataGeom.ofParts` with no producer.  `AhatMono.lean` settles a great
deal about it and leaves exactly one residual, `hsupp` / `hext`
(`ahatMono_of_fwd_suppVal` `AhatMono.lean:3048`, `ahatMono_field_of_extraction`
`ChainPartsFeed.lean:258`), described there as having **no source counterpart**.

This file closes that residual by **passing to a subsequence** — the move Collé makes three
times in the same proof (`b3_colle2.txt:496`, `:500`, `:504`) — and it does so for an
**arbitrary finite fan**, so it does not depend on the hexagon normalisation `hES` that
`AhatMono.lean` §11 needs and that its §18 octagon defeats.

## The argument

`Â_i := A_i − k_i v⃗_ℓ` is `E(𝒰)`-enveloped, so it is cut out by its support numbers on the
fixed finite fan `E 𝒰` (`subset_iff_suppVal_le_of_enveloped`, `AhatMono.lean:2356`), and
`Â_i ⊆ Â_j` is exactly `suppVal Â_i n ≤ suppVal Â_j n` for every `n ∈ E 𝒰`.

* On normals with `⟪n, v⃗_ℓ⟫ ≤ 0` this is already free from `:486` (`A_i ⊆ A_j`) and `:488`
  (`k_i ≤ k_j`) — `suppVal_hatOf_mono_of_nonpos` (`AhatMono.lean:1757`).
* On normals with `⟪n, v⃗_ℓ⟫ > 0` it is the residual.  But `:488` also says `g₁ ∈ Â_i`
  (endpoint alignment pins the final point of `Â_i ∩ ℓ⁻` at `g₁`), so each of these finitely
  many integer sequences `i ↦ suppVal Â_i n` is **bounded below** by `⟪n, g₁⟫`.  Finitely
  many ℕ-valued sequences have a simultaneously non-decreasing subsequence — Dickson's lemma,
  `Pi.wellQuasiOrderedLE` in Mathlib — and along that subsequence the residual holds by
  construction.

  ⚠ `AItemFour.exists_endpoint_shift` (`AItemFour.lean:329`) delivers `g₁ ∈ Â_i` only for
  `1 ≤ i`, not at `i = 0`; `exists_subseq_ahatMono_of_endpoint_shift` is the variant that
  matches it, and it is the one a chain consumer should call.

So `AhatMono` is not an extra geometric fact about the chain: it is a property of *some*
subsequence of every chain that satisfies `:484`/`:486`/`:488`.

## Relation to the four counterexamples in `AhatMono.lean`

`not_ahatMono_of_enveloped` (§5), `not_ahatMono_of_ofParts_chain_binders` (§8),
`not_ahatMono_of_exhausting_chain` (§9), `not_ahatMono_of_ofParts_chain_binders_with_xper`
(§10) and `not_ahatMono_octagon` (§18) all refute `AhatMono` **at the given indexing**.
None of them is contradicted here and none of them is weakened: `exists_subseq_ahatMono`
asserts only that a re-indexing exists.  §11 already observed this for the §9 family by hand
(`ahatMono_shift4_xA`, `σ i = i + 4`); this file replaces the hand-picked shift by an
existence theorem that does not look at the fan, and so also covers §18's octagon, which §11
explicitly left "untested".

⚠ **What this does not do.**  It does not produce a chain.  It converts the debt
"`AhatMono` for the chain the recursion builds" into "the consumer must accept a re-indexed
chain", and §2 below discharges that conversion for every other chain-side binder
(`envB`, `maxA`, `subBA`, `subAB`, `ItemII`, `Exhausts`, `hfin`, `hhp`).  `ChainDataGeomParts`
(`ChainPartsFeed.lean:173`) is the consumer; wiring it is the integrator's.
-/

set_option autoImplicit false

namespace Nivat.LeafAItemII

open Nivat Nivat.LE2 Nivat.Colle35 Nivat.AhatMono

/-! ## §1. The subsequence -/

/-- `Â_i` is finite when `A_i` is. -/
theorem finite_hatOf {A : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ} {vl : ℤ × ℤ} {i : ℕ}
    (h : (A i).Finite) : (hatOf A kk vl i).Finite := by
  rw [hatOf_eq_shift_neg]
  exact finite_shift h

/-- **The residual `hsupp` of `AhatMono.lean` §19 holds along a subsequence.**

原文：b3_colle2.txt:496 / :500 / :504 — "By passing to a subsequence, we can assume this holds
for all `i`", the move Collé makes three times in this very proof; and `:488`, which supplies
the lower bound `g₁ ∈ Â_i`.

量词对应原文:
* `henv` ↔ `:484` ("among all `E(𝒮_φ)`-enveloped sets"), Definition 3.2 at `:402`;
* `hUfin`, `hUarea` ↔ `:402` ("a finite, convex set such that `conv(𝒰)` has positive area");
* `hfin` ↔ finiteness of each stage, `:402` again (`𝒯` enveloped by a finite `𝒰`);
* `hmono` ↔ `:486`, Figure 5, `A₁ ⊂ A₂ ⊂ ⋯`;
* `hkk` ↔ `:488` through `kk_le_of_endpointAligned` (`AhatMono.lean:106`);
* `hg₁` ↔ `:488`, "the final point of `(A_i − k_i v⃗_ℓ) ∩ ℓ⁻` … coincides with `g₁`" — in
  particular `g₁ ∈ Â_i`;
* `σ` ↔ the subsequence of `:496`/`:500`/`:504`.

No quantifier here is ours: the conclusion is `ChainAssemble.lean:186`'s `AhatMono` verbatim,
read along `σ`. -/
theorem exists_subseq_ahatMono
    {U : Set (ℤ × ℤ)} {A : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ} {vl g₁ : ℤ × ℤ}
    (hUfin : U.Finite) (hUarea : PosArea U)
    (henv : ∀ i, Enveloped U (A i))
    (hfin : ∀ i, (A i).Finite)
    (hmono : ∀ i j, i ≤ j → A i ⊆ A j)
    (hkk : ∀ i j, i ≤ j → kk i ≤ kk j)
    (hg₁ : ∀ i, g₁ ∈ hatOf A kk vl i) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∀ i j, i ≤ j →
        hatOf (fun n => A (σ n)) (fun n => kk (σ n)) vl i
          ⊆ hatOf (fun n => A (σ n)) (fun n => kk (σ n)) vl j := by
  classical
  have harea : ∀ i, PosArea (A i) := fun i => posArea_of_enveloped hUfin hUarea (henv i)
  have hne : ∀ i, (A i).Nonempty := fun i => by
    obtain ⟨p, hp, -⟩ := harea i; exact ⟨p, hp⟩
  have hEfin : (E U).Finite := finite_E_of_finite hUfin
  -- the finitely many coordinates: the support numbers of `Â_i` on the fan, shifted to ℕ by
  -- the `:488` lower bound `⟪n, g₁⟫ ≤ suppVal Â_i n`.
  have hlow : ∀ (i : ℕ) (n : ℤ × ℤ), dot n g₁ ≤ suppVal (hatOf A kk vl i) n := fun i n =>
    le_suppVal (finite_hatOf (hfin i)) ⟨g₁, hg₁ i⟩ (hg₁ i)
  set ι : Type := {x : ℤ × ℤ // x ∈ hEfin.toFinset} with hι
  set F : ℕ → (ι → ℕ) :=
    fun i n => (suppVal (hatOf A kk vl i) n.1 - dot n.1 g₁).toNat with hF
  have hpwo : (Set.univ : Set (ι → ℕ)).IsPWO := Set.isPWO_of_wellQuasiOrderedLE _
  obtain ⟨g, hg⟩ := hpwo.exists_monotone_subseq (f := F) (fun _ => Set.mem_univ _)
  refine ⟨fun i => g i, g.strictMono, ?_⟩
  -- the residual, along `σ`
  have hsupp : ∀ i j, i ≤ j → ∀ n ∈ E U, 0 < dot n vl →
      suppVal (A (g i)) n + ((kk (g j) : ℤ) - (kk (g i) : ℤ)) * dot n vl
        ≤ suppVal (A (g j)) n := by
    intro i j hij n hn _
    have hnmem : n ∈ hEfin.toFinset := by simpa using hn
    have hcoord : F (g i) ⟨n, hnmem⟩ ≤ F (g j) ⟨n, hnmem⟩ := hg hij ⟨n, hnmem⟩
    have hi0 : (0 : ℤ) ≤ suppVal (hatOf A kk vl (g i)) n - dot n g₁ := by
      linarith [hlow (g i) n]
    have hj0 : (0 : ℤ) ≤ suppVal (hatOf A kk vl (g j)) n - dot n g₁ := by
      linarith [hlow (g j) n]
    have hcast : (suppVal (hatOf A kk vl (g i)) n - dot n g₁)
        ≤ (suppVal (hatOf A kk vl (g j)) n - dot n g₁) := by
      have := Int.ofNat_le.mpr hcoord
      rwa [hF, Int.toNat_of_nonneg hi0, Int.toNat_of_nonneg hj0] at this
    rw [suppVal_hatOf (hfin (g i)) (hne (g i)), suppVal_hatOf (hfin (g j)) (hne (g j))] at hcast
    linarith
  exact ahatMono_of_fwd_suppVal hUfin hUarea (fun i => henv (g i)) (fun i => hfin (g i))
    (fun i j hij => hmono _ _ (g.strictMono.monotone hij))
    (fun i j hij => hkk _ _ (g.strictMono.monotone hij)) hsupp

/-- The same with `:488` in the shape `AhatMono.lean`'s `endpointAligned_*` lemmas produce it:
`IsGreatest {t | g₁ + t•v⃗_ℓ ∈ Â_i ∧ ⟪nℓ, g₁ + t•v⃗_ℓ⟫ = cz} 0`.

原文：b3_colle2.txt:488 verbatim; the `0 ∈ ·` half of `IsGreatest` is `g₁ ∈ Â_i`. -/
theorem exists_subseq_ahatMono_of_aligned
    {U : Set (ℤ × ℤ)} {A : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ} {vl g₁ nℓ : ℤ × ℤ} {cz : ℤ}
    (hUfin : U.Finite) (hUarea : PosArea U)
    (henv : ∀ i, Enveloped U (A i))
    (hfin : ∀ i, (A i).Finite)
    (hmono : ∀ i j, i ≤ j → A i ⊆ A j)
    (hkk : ∀ i j, i ≤ j → kk i ≤ kk j)
    (halign : ∀ i,
      IsGreatest {t : ℤ | g₁ + t • vl ∈ hatOf A kk vl i ∧ dot nℓ (g₁ + t • vl) = cz} 0) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∀ i j, i ≤ j →
        hatOf (fun n => A (σ n)) (fun n => kk (σ n)) vl i
          ⊆ hatOf (fun n => A (σ n)) (fun n => kk (σ n)) vl j := by
  refine exists_subseq_ahatMono (g₁ := g₁) hUfin hUarea henv hfin hmono hkk (fun i => ?_)
  have h := (halign i).1.1
  simpa using h

/-- **The form `AItemFour.exists_endpoint_shift` (`AItemFour.lean:329`) actually produces.**

⚠ That lemma aligns only for `1 ≤ i`: its `g₁` is the final point of `A₁ ∩ ℓ⁻`, and
`g₁ ∈ Â₀` is **not** among its conclusions (`kk 0 = 0` and `A 0 ⊆ A 1` leave `g₁ ∈ A 0` open).
So `exists_subseq_ahatMono`'s `hg₁` is *not* free at index `0` on the chain.  The repair is
to run the argument on the tail `i ↦ A (i+1)`, which costs nothing because the output is a
subsequence anyway — and the extra conclusion `1 ≤ σ i` is what a consumer needs to re-use
`halign` itself after the re-indexing. -/
theorem exists_subseq_ahatMono_of_endpoint_shift
    {U : Set (ℤ × ℤ)} {A : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ} {vl g₁ nℓ : ℤ × ℤ} {cz : ℤ}
    (hUfin : U.Finite) (hUarea : PosArea U)
    (henv : ∀ i, Enveloped U (A i))
    (hfin : ∀ i, (A i).Finite)
    (hmono : ∀ i j, i ≤ j → A i ⊆ A j)
    (hkk : ∀ i j, i ≤ j → kk i ≤ kk j)
    (halign : ∀ i, 1 ≤ i →
      IsGreatest {t : ℤ | g₁ + t • vl ∈ hatOf A kk vl i ∧ dot nℓ (g₁ + t • vl) = cz} 0) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ (∀ i, 1 ≤ σ i) ∧
      ∀ i j, i ≤ j →
        hatOf (fun n => A (σ n)) (fun n => kk (σ n)) vl i
          ⊆ hatOf (fun n => A (σ n)) (fun n => kk (σ n)) vl j := by
  obtain ⟨τ, hτ, hmono'⟩ :=
    exists_subseq_ahatMono (A := fun n => A (n + 1)) (kk := fun n => kk (n + 1)) (g₁ := g₁)
      hUfin hUarea (fun i => henv (i + 1)) (fun i => hfin (i + 1))
      (fun i j hij => hmono (i + 1) (j + 1) (by omega))
      (fun i j hij => hkk (i + 1) (j + 1) (by omega))
      (fun i => by
        have h : g₁ + (0 : ℤ) • vl + (kk (i + 1) : ℤ) • vl ∈ A (i + 1) :=
          (halign (i + 1) (by omega)).1.1
        show g₁ + (kk (i + 1) : ℤ) • vl ∈ A (i + 1)
        simpa using h)
  exact ⟨fun i => τ i + 1, fun _ _ hij => Nat.succ_lt_succ (hτ hij),
    fun i => Nat.le_add_left 1 (τ i), hmono'⟩

/-- §19's `U = ↑𝒮_φ` form: `PosArea` is free from `DecompData.hm` (`posArea_Sphi`,
`AhatMono.lean:3175`), so the only binders left are `:484`, `:486`, `:488`. -/
theorem exists_subseq_ahatMono_Sphi {α : Type*} [AddCommMonoid α] {η : Config α}
    (d : DecompData η) {A : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ} {vl g₁ : ℤ × ℤ}
    (henv : ∀ i, EnvOf (↑d.Sphi : Set (ℤ × ℤ)) (A i))
    (hfin : ∀ i, (A i).Finite)
    (hmono : ∀ i j, i ≤ j → A i ⊆ A j)
    (hkk : ∀ i j, i ≤ j → kk i ≤ kk j)
    (hg₁ : ∀ i, g₁ ∈ hatOf A kk vl i) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∀ i j, i ≤ j →
        hatOf (fun n => A (σ n)) (fun n => kk (σ n)) vl i
          ⊆ hatOf (fun n => A (σ n)) (fun n => kk (σ n)) vl j :=
  exists_subseq_ahatMono d.Sphi.finite_toSet (posArea_Sphi d) henv hfin hmono hkk hg₁

/-! ## §2. Every other chain-side binder survives the re-indexing

The point of this section is the conversion cost.  `exists_subseq_ahatMono` is only useful to
`ChainDataGeomParts` (`ChainPartsFeed.lean:173`) if the *other* fields transfer to
`(B ∘ σ, A ∘ σ, u ∘ σ, kk ∘ σ)`, and `subAB` is the one that is not pointwise. -/

/-- `canonA` reads only stage `i`'s own `B i` and `u i`, so re-indexing commutes with it.
This is what makes `maxA` transfer with no hypothesis at all. -/
theorem canonA_comp {α : Type*} (η xper : Config α) (vl : ℤ × ℤ)
    (B : ℕ → Set (ℤ × ℤ)) (u : ℕ → ℤ × ℤ) (σ : ℕ → ℕ) (i : ℕ) :
    canonA η xper vl (fun n => B (σ n)) (fun n => u (σ n)) i = canonA η xper vl B u (σ i) := rfl

/-- `B` is monotone as soon as `subBA` and `subAB` hold — the `B`-side twin of
`Nivat.ChainAsm.Aparts.A_mono_of_subBA_subAB`（`ChainPartsFeed.lean`，⚠ 第 201 轮删号留名：
原记 `:277`，实测声明头在 `:310`；该文件全主仓被引了 20 多个互不相同的行号，按名字 `grep`）。
原文：b3_colle2.txt:466, `B' ⊂ B₁ ⊂ A₁ ⊂ B₂ ⊂ ⋯`. -/
theorem B_mono_of_subBA_subAB {B A : ℕ → Set (ℤ × ℤ)}
    (subBA : ∀ i, B i ⊆ A i) (subAB : ∀ i, A i ⊆ B (i + 1)) :
    ∀ i j, i ≤ j → B i ⊆ B j := by
  have hstep : ∀ i, B i ⊆ B (i + 1) := fun i => (subBA i).trans (subAB i)
  intro i j hij
  induction j with
  | zero => obtain rfl : i = 0 := Nat.le_zero.mp hij; exact subset_rfl
  | succ n ih =>
    rcases Nat.lt_or_ge i (n + 1) with h | h
    · exact (ih (Nat.lt_succ_iff.mp h)).trans (hstep n)
    · obtain rfl : i = n + 1 := le_antisymm hij h; exact subset_rfl

/-- **`subAB` transfers.**  This is the only binder for which re-indexing is not pointwise:
`A (σ i) ⊆ B (σ i + 1)` has to be pushed forward to `B (σ (i+1))`, which needs `σ` strictly
monotone and `B` monotone. -/
theorem subAB_comp {B A : ℕ → Set (ℤ × ℤ)} {σ : ℕ → ℕ}
    (hσ : StrictMono σ)
    (subBA : ∀ i, B i ⊆ A i) (subAB : ∀ i, A i ⊆ B (i + 1)) :
    ∀ i, A (σ i) ⊆ B (σ (i + 1)) := fun i =>
  (subAB (σ i)).trans
    (B_mono_of_subBA_subAB subBA subAB _ _ (Nat.succ_le_of_lt (hσ (Nat.lt_succ_self i))))

/-- **Collé item (ii) transfers** (`b3_colle2.txt:474`): the box of stage `i` is already inside
`B i ⊆ B (σ i)`. -/
theorem itemII_comp {B : ℕ → Set (ℤ × ℤ)} {nℓ : ℤ × ℤ} {cz : ℤ} {σ : ℕ → ℕ}
    (hσ : StrictMono σ) (hBmono : ∀ i j, i ≤ j → B i ⊆ B j)
    (h : ItemII B nℓ cz) : ItemII (fun n => B (σ n)) nℓ cz :=
  fun i z h1 h2 hz => hBmono i (σ i) (le_apply_of_strictMono hσ i) (h i z h1 h2 hz)

/-- **`:498` transfers**: `⋃ A (σ i) = ⋃ A i` for a monotone family along a strictly monotone
re-indexing (`iUnion_reindex_of_strictMono`, `AhatMono.lean:1690`). -/
theorem exhausts_comp {A : ℕ → Set (ℤ × ℤ)} {nℓ : ℤ × ℤ} {cz : ℤ} {σ : ℕ → ℕ}
    (hσ : StrictMono σ) (hmono : ∀ i j, i ≤ j → A i ⊆ A j)
    (h : Exhausts A nℓ cz) : Exhausts (fun n => A (σ n)) nℓ cz := by
  unfold Exhausts at h ⊢
  rw [iUnion_reindex_of_strictMono hmono hσ]
  exact h

/-- `⋃ Â_i` is unchanged by the re-indexing, once `AhatMono` holds on both sides.  The shell
block of `ofParts` (`hswept`, `ahat_nonempty`, `bottom`, `rec_p`, `fillCover`) is stated about
this union, so it transfers verbatim. -/
theorem iUnion_hatOf_comp {A : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ} {vl : ℤ × ℤ} {σ : ℕ → ℕ}
    (hσ : StrictMono σ)
    (hmono : ∀ i j, i ≤ j → hatOf A kk vl i ⊆ hatOf A kk vl j) :
    (⋃ i, hatOf (fun n => A (σ n)) (fun n => kk (σ n)) vl i) = ⋃ i, hatOf A kk vl i := by
  have hpt : ∀ i, hatOf (fun n => A (σ n)) (fun n => kk (σ n)) vl i = hatOf A kk vl (σ i) :=
    fun _ => rfl
  simp only [hpt]
  exact iUnion_reindex_of_strictMono hmono hσ

/-! ## §3. The package

Everything `ChainDataGeomParts` asks of the `(B, A, u, kk)` block, plus `AhatMono`, on one
re-indexed chain.  The binders are, in order: Definition 3.2 on `𝒰` (`:402`); `:484`
(`envB` / `maxA` / envelopedness and finiteness of `A_i`); `:486` (`subBA` / `subAB`);
`:488` (`hkk` / `hg₁`); `:474` (`ItemII`); `:498` (`Exhausts`). -/

/-- **The re-indexed chain.**  原文：b3_colle2.txt:496/:500/:504 ("by passing to a
subsequence"), applied once to the whole block instead of coordinate by coordinate.

⚠ `hg₁` is taken at **every** index here; on the chain `AItemFour.exists_endpoint_shift`
(`AItemFour.lean:329`) only supplies it for `1 ≤ i`.  A caller who has only the `1 ≤ i` form
should pre-compose with `i ↦ i + 1` — the same tail trick as
`exists_subseq_ahatMono_of_endpoint_shift`, which is free because the output is a subsequence.

Nothing is strengthened: every hypothesis is a clause of `:402`–`:498` and every conclusion is
the same clause read along `σ`, except the last, which is `ChainAssemble.lean:186`. -/
theorem exists_subseq_chain
    {α : Type*} {η xper : Config α}
    {U : Set (ℤ × ℤ)} {B A : ℕ → Set (ℤ × ℤ)} {u : ℕ → ℤ × ℤ} {kk : ℕ → ℕ}
    {vl g₁ nℓ : ℤ × ℤ} {cz : ℤ}
    (hUfin : U.Finite) (hUarea : PosArea U)
    (envB : ∀ i, EnvOf U (B i))
    (maxA : ∀ i, IsMaxEnvIn (EnvOf U) (canonA η xper vl B u i) (A i))
    (henv : ∀ i, Enveloped U (A i))
    (hfin : ∀ i, (A i).Finite)
    (subBA : ∀ i, B i ⊆ A i) (subAB : ∀ i, A i ⊆ B (i + 1))
    (hkk : ∀ i j, i ≤ j → kk i ≤ kk j)
    (hg₁ : ∀ i, g₁ ∈ hatOf A kk vl i)
    (hII : ItemII B nℓ cz) (hexh : Exhausts A nℓ cz) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      (∀ i, EnvOf U (B (σ i))) ∧
      (∀ i, IsMaxEnvIn (EnvOf U)
        (canonA η xper vl (fun n => B (σ n)) (fun n => u (σ n)) i) (A (σ i))) ∧
      (∀ i, B (σ i) ⊆ A (σ i)) ∧ (∀ i, A (σ i) ⊆ B (σ (i + 1))) ∧
      (∀ i, (A (σ i)).Finite) ∧
      ItemII (fun n => B (σ n)) nℓ cz ∧ Exhausts (fun n => A (σ n)) nℓ cz ∧
      (∀ i j, i ≤ j →
        hatOf (fun n => A (σ n)) (fun n => kk (σ n)) vl i
          ⊆ hatOf (fun n => A (σ n)) (fun n => kk (σ n)) vl j) := by
  have hAmono : ∀ i j, i ≤ j → A i ⊆ A j := by
    have hstep : ∀ i, A i ⊆ A (i + 1) := fun i => (subAB i).trans (subBA (i + 1))
    intro i j hij
    induction j with
    | zero => obtain rfl : i = 0 := Nat.le_zero.mp hij; exact subset_rfl
    | succ n ih =>
      rcases Nat.lt_or_ge i (n + 1) with h | h
      · exact (ih (Nat.lt_succ_iff.mp h)).trans (hstep n)
      · obtain rfl : i = n + 1 := le_antisymm hij h; exact subset_rfl
  obtain ⟨σ, hσ, hahat⟩ :=
    exists_subseq_ahatMono hUfin hUarea henv hfin hAmono hkk hg₁
  refine ⟨σ, hσ, fun i => envB (σ i), fun i => ?_, fun i => subBA (σ i),
    subAB_comp hσ subBA subAB, fun i => hfin (σ i),
    itemII_comp hσ (B_mono_of_subBA_subAB subBA subAB) hII,
    exhausts_comp hσ hAmono hexh, hahat⟩
  rw [canonA_comp]
  exact maxA (σ i)

/-! ## §4. Non-vacuity receipt, on the family that refutes `AhatMono`

`AhatMono.lean` §9's `xA` / `xKK` is the growing, exhausting chain on which
`not_ahatMono_xA` (`AhatMono.lean:954`) refutes `AhatMono` at `i = 3`, `j = 4`.  Every
hypothesis of `exists_subseq_ahatMono` holds on it, so the theorem is not vacuous, and its
conclusion is not implied by the chain binders — the two live side by side on one family.

§11's `ahatMono_shift4_xA` finds the same subsequence by hand (`σ i = i + 4`, chosen after
inspecting where `xRx` stalls); the point of `exists_subseq_ahatMono_xA` is that nothing about
`xRx` is consulted. -/

/-- `xKK` is monotone: `:488` through `kk_le_of_endpointAligned` on this family. -/
theorem xKK_mono : ∀ i j : ℕ, i ≤ j → xKK i ≤ xKK j := by
  intro i j hij
  unfold xKK
  split_ifs <;> omega

/-- `g₁ = (1,0)` lies in every `Â_i` of the §9 family, index `0` included
(`endpointAligned_xA` covers `1 ≤ i` only). -/
theorem g₁_mem_hatOf_xA : ∀ i, ((1 : ℤ), (0 : ℤ)) ∈ hatOf xA xKK ((1 : ℤ), (0 : ℤ)) i := by
  intro i
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · show ((1 : ℤ), (0 : ℤ)) + (xKK 0 : ℤ) • ((1 : ℤ), (0 : ℤ)) ∈ xA 0
    rw [ce_shift, mem_xA]
    norm_num [xKK, xN, xRx]
  · have h := (endpointAligned_xA i hi).1.1
    simpa using h

/-- **The receipt.**  On one and the same chain: item (ii) (`:474`), exhaustion (`:498`),
`AhatMono` **false** at the given indexing, and `AhatMono` **true** along a subsequence
(`:496`/`:500`/`:504`).  `B := A` here, as in `not_ahatMono_of_exhausting_chain`. -/
theorem itemII_chain_ahatMono_after_reindexing :
    ItemII xA ((0 : ℤ), (1 : ℤ)) 0 ∧
    Exhausts xA ((0 : ℤ), (1 : ℤ)) 0 ∧
    ¬ (∀ i j, i ≤ j →
        hatOf xA xKK ((1 : ℤ), (0 : ℤ)) i ⊆ hatOf xA xKK ((1 : ℤ), (0 : ℤ)) j) ∧
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∀ i j, i ≤ j →
        hatOf (fun n => xA (σ n)) (fun n => xKK (σ n)) ((1 : ℤ), (0 : ℤ)) i
          ⊆ hatOf (fun n => xA (σ n)) (fun n => xKK (σ n)) ((1 : ℤ), (0 : ℤ)) j :=
  ⟨itemII_xA, exhausts_xA, not_ahatMono_xA,
    exists_subseq_ahatMono finite_hexA posArea_hexA enveloped_xA finite_xA
      (fun _ _ hij => mono_xA hij) xKK_mono g₁_mem_hatOf_xA⟩

end Nivat.LeafAItemII

#print axioms Nivat.LeafAItemII.finite_hatOf
#print axioms Nivat.LeafAItemII.exists_subseq_ahatMono
#print axioms Nivat.LeafAItemII.exists_subseq_ahatMono_of_aligned
#print axioms Nivat.LeafAItemII.exists_subseq_ahatMono_of_endpoint_shift
#print axioms Nivat.LeafAItemII.exists_subseq_ahatMono_Sphi
#print axioms Nivat.LeafAItemII.canonA_comp
#print axioms Nivat.LeafAItemII.B_mono_of_subBA_subAB
#print axioms Nivat.LeafAItemII.subAB_comp
#print axioms Nivat.LeafAItemII.itemII_comp
#print axioms Nivat.LeafAItemII.exhausts_comp
#print axioms Nivat.LeafAItemII.iUnion_hatOf_comp
#print axioms Nivat.LeafAItemII.exists_subseq_chain
#print axioms Nivat.LeafAItemII.xKK_mono
#print axioms Nivat.LeafAItemII.g₁_mem_hatOf_xA
#print axioms Nivat.LeafAItemII.itemII_chain_ahatMono_after_reindexing
