/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.ChainAssemble
import Nivat.External.Colle.RegionCut
import Nivat.External.Colle.ItemII
import Nivat.External.Colle.LeafAWire

/-!
# Lane recp: `rec_p` (with `p := -vl`) from the anchor `g₁` and `kk`-unboundedness

Lane `lane-recp`, 2026-09-22.  Target: `ChainDataGeom.ofParts`'s `rec_p` binder
(`ChainAssemble.lean:210`, `∀ g ∈ ⋃ i, hatOf A kk vl i, g + p ∈ ⋃ i, hatOf A kk vl i`),
instantiated at `p := -vl` (team-lead's dispatch).

## The paper argument (`b3_colle2.txt:487-506`), and why it is a *different* mechanism from
`rec_vJ`'s

`rec_vJ` (`ItemII.lean` §7-§8, already landed as `Colle35.rec_vJ_of_bottom`) is derived from a
`+v_J`-ray plus lattice-convexity of `Â_∞` (`Colle35.rec_of_ray`).  `rec_p` (`p = -v_ℓ`, the
*other* semi-infinite edge, parallel to `ℓ` itself) has the same *shape* of proof — a ray plus
`rec_of_ray` — but the ray comes from a different piece of the construction: not the minimal-`J`
selection (`:500-506`), but the anchor/normalisation step at `:487-490`:

> "Let `g₁ ∈ A₁` denote the final point of `A₁ ∩ ℓ^(−)` … and, for each `i > 1`, let `k_i ∈ ℕ`
> be such that the final point of `(A_i - k_i v⃗_ℓ) ∩ ℓ^(−)` … coincides with `g₁`.  Setting
> `Â_i := A_i - k_i v⃗_ℓ` … where `k₁ = 0`."

Unwound: `g₁ ∈ A_1` (`hg₁0` below, `i = 0` in Lean's zero-based convention) and, since the whole
chain `B' ⊂ B_1 ⊂ A_1 ⊂ B_2 ⊂ A_2 ⊂ ⋯` (`:465`) is `⊆`-increasing, `g₁ ∈ A_i` for **every**
`i` (`hg₁_in` below, from `subBA`/`subAB`, `ofParts`'s own chain binders — no new hypothesis).
The normalisation itself, `k_i` chosen so `g₁ + k_i • v_ℓ ∈ A_i`, is exactly
`g₁ ∈ hatOf A kk vl i`, i.e. `hg₁_reach` below (the defining property of `kk`, `:488-490`).

What is genuinely new — not free from any `ofParts` binder — is that `k_i` is **unbounded**:
`item (ii)` (`:474`, `B_i ⊇ A_{i-1} ∪ [-i+1,i-1]² ∩ ℋ(ℓ^(−))`) forces `A_i`, hence `B_{i+1}`, to
extend arbitrarily far along `ℓ^(−)` towards `+v_ℓ` as `i → ∞`; re-pinning `g₁` at the *far*
(`v_ℓ`-maximal) end after each such extension is exactly what pushes `k_i → ∞`.  This is
`CORE-HOLES.md`'s "Task A1" debt (`itemII_exhausts`) restated as a scalar fact about `kk`
instead of a set fact about `B`; it is **not** proved here (no producer for item (ii)'s growth
exists yet on the tree — `AItemTwoGrowth.lean`, `ItemIIRec.lean` module docstrings, both quoted
in this file's imports, say so explicitly).  It is `hkk_unbounded` below, cited to `:474`/`:490`.

## What this file proves

Given the anchor/reach data (`hg₁0`, `hg₁_reach`, `hkk_unbounded`) plus lattice-convexity of
each `A i` (free from `maxA` via `Enveloped.latticeConvex`, `ChainAssemble.latticeConvex_iUnion_hatOf`'s
own proof pattern) and of `⋃ i, hatOf A kk vl i` (free from `ChainAssemble.latticeConvex_iUnion_hatOf`,
itself only consuming `ofParts`'s own `hEnv`/`maxA`/`hfin`/`AhatMono`), `rec_p` at `p := -vl`
follows by the *same* two-step mechanism as `rec_vJ`: build a `-v_ℓ`-ray from `g₁` using
`RegionCut.mem_of_between` (lattice convexity along the line through `g₁` and `g₁ + kk i • vl`),
then `Colle35.rec_of_ray` (lattice convexity of the union + the ray ⟹ closure under `+(-vl)`).

**Numeric check (rule 6) before formalising**: the hexagon family `eA`/`eKK`
(`AhatMono.lean` §7, `vl = (1,0)`, `nℓ = (0,1)`, `g₁ = (1,0)`) that refutes `rec_p` in
`tmp/wip/leafa_recp_refute_eA.lean` has `eKK i = i` for `i ≤ 2` capped/non-monotone in a way
that makes `kk` **bounded** on the relevant range (`eKK 2 = 2`, but the family is only defined
for `i ≤ 2` — `mem_eA`'s `split_ifs` has no branch past `i = 2`, so `eA i` for `i > 2` is
whatever the `else`-branch default is, not a genuinely growing box); it is not a counterexample
to the hypotheses used here, since `hkk_unbounded` fails for it (this is consistent with
`refute_rec_p_anchored`'s own scope note: it refutes a *weaker* anchored signature, one without
`hAhatConv`/lattice-convexity of the union — see that file's binder list, no `IsLatticeConvexRegion`
of `⋃ i, hatOf A kk vl i` appears). The two refutations in `tmp/wip/leafa_refute_recp.lean`
and `tmp/wip/leafa_recp_refute_eA.lean` both refute signatures *without* the union-convexity
hypothesis; this file's `hAhatConv` closes exactly that gap (and is a hypothesis with a free
producer at the true `ofParts` binders, per `latticeConvex_iUnion_hatOf`).

**Correction (team-lead, 2026-09-22, after review):** `hAhatConv` is *not* free on the raw
index — `ChainAssemble.latticeConvex_iUnion_hatOf` consumes `AhatMono`, which is refuted for the
raw chain (`AhatMono.lean`) and only holds along the subsequence `σ` of
`LeafAItemII.exists_subseq_chain` (`LeafAWire.exists_subseq_chain_of_itemII`).  So `hAhatConv`
(and hence `rec_p_of_anchor` as a whole) is free **on the reindexed chain** `A ∘ σ`, `kk ∘ σ`,
which is exactly where `ofParts` is applied anyway (it is instantiated post-subsequence-
extraction). No change to the theorem statement is needed — the caller supplies `A := A ∘ σ` etc.

## `hkk_unbounded`, discharged (2026-09-22, second pass)

`kk_unbounded_of_itemII` below discharges `hkk_unbounded` from `ItemII` directly (`:474`), with
no dependence on the subsequence or on `kkOf`'s specific `Finset.max'` construction: item (ii)'s
box `[-(i-1),i-1]² ∩ {cz ≤ ⟪nℓ,·⟫} ⊆ B i ⊆ A i` contains `g₁ + N•vl` once `i` is large enough
(`i - 1 ≥ |g₁.1| + |g₁.2| + N•(|vl.1|+|vl.2|)`, and `dot nℓ (g₁+N•vl) = dot nℓ g₁ ≥ cz` since
`hperp : dot nℓ vl = 0`), so `N ≤ kk i` follows from `kk`'s own maximality property
(`hkk_max`, exported concretely as `LeafAWire.kkOf_max` for the `kkOf` construction). -/

set_option autoImplicit false

namespace Nivat.LeafARecP

open Nivat Nivat.LE2 Nivat.Colle35 Nivat.MaxEnv

/-- **`rec_p` (`p := -vl`) from the anchor/reach data.**  `subBA`/`subAB` are `ofParts`'s own
chain binders (`ChainAssemble.lean:184-185`); `hAconv` and `hAhatConv` are free at the producer
(`Enveloped.latticeConvex` via `maxA`, and `Colle35.latticeConvex_iUnion_hatOf` respectively);
`hg₁0`, `hg₁_reach`, `hkk_unbounded` are the genuinely new content, cited to `b3_colle2.txt:474`,
`:487-490` in the module docstring. Conclusion is `ofParts`'s `rec_p` binder verbatim at
`p := -vl`. -/
theorem rec_p_of_anchor
    {A B : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ} {vl g₁ : ℤ × ℤ}
    (hAconv : ∀ i, IsLatticeConvexRegion (A i))
    (subBA : ∀ i, B i ⊆ A i)
    (subAB : ∀ i, A i ⊆ B (i + 1))
    (hg₁0 : g₁ ∈ A 0)
    (hg₁_reach : ∀ i, g₁ + (kk i : ℤ) • vl ∈ A i)
    (hkk_unbounded : ∀ N : ℕ, ∃ i, N ≤ kk i)
    (hAhatConv : IsLatticeConvexRegion (⋃ i, hatOf A kk vl i)) :
    ∀ g ∈ ⋃ i, hatOf A kk vl i, g + (-vl) ∈ ⋃ i, hatOf A kk vl i := by
  -- `A` is `⊆`-increasing: `A i ⊆ B (i+1) ⊆ A (i+1)`, chained.
  have hAmono : ∀ i j, i ≤ j → A i ⊆ A j := by
    intro i j hij
    induction j, hij using Nat.le_induction with
    | base => exact subset_rfl
    | succ n _ ih => exact ih.trans ((subAB n).trans (subBA (n + 1)))
  -- `g₁` stays in every `A i` (`:487`, `g₁ ∈ A₁ ⊆ A_i`).
  have hg₁_in : ∀ i, g₁ ∈ A i := fun i => hAmono 0 i (Nat.zero_le i) hg₁0
  -- The `-v_ℓ`-ray from `g₁`, using `kk`-unboundedness and lattice convexity along the line
  -- through `g₁` and `g₁ + kk i • vl`.
  have hray : ∀ k : ℕ, g₁ + (k : ℤ) • (-vl) ∈ ⋃ i, hatOf A kk vl i := by
    intro k
    obtain ⟨i, hi⟩ := hkk_unbounded k
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    show g₁ + (k : ℤ) • (-vl) + (kk i : ℤ) • vl ∈ A i
    have hs : g₁ + (0 : ℤ) • vl ∈ A i := by simpa using hg₁_in i
    have hu : g₁ + (kk i : ℤ) • vl ∈ A i := hg₁_reach i
    have h1 : (0 : ℤ) ≤ (kk i : ℤ) - (k : ℤ) := by
      have : (k : ℤ) ≤ (kk i : ℤ) := by exact_mod_cast hi
      linarith
    have h2 : (kk i : ℤ) - (k : ℤ) ≤ (kk i : ℤ) := by
      have : (0 : ℤ) ≤ (k : ℤ) := by positivity
      linarith
    have hmem := Nivat.LE2.mem_of_between (hAconv i) hs hu h1 h2
    have heq : g₁ + (k : ℤ) • (-vl) + (kk i : ℤ) • vl = g₁ + ((kk i : ℤ) - (k : ℤ)) • vl := by
      rw [sub_smul]
      have : (k : ℤ) • (-vl) = -((k : ℤ) • vl) := smul_neg _ _
      rw [this]
      abel
    rw [heq]
    exact hmem
  exact rec_of_ray hAhatConv hray

/-- **`hkk_unbounded`, discharged.**  Item (ii)'s box (`:474`) forces `g₁ + N • vl` into `A i`
once `i` is large enough, so `kk`'s maximality (`hkk_max`, e.g. `LeafAWire.kkOf_max`) gives
`N ≤ kk i`.  `hg₁_level` is `g₁`'s level (`anchorPoint_level`, `LeafAWire.lean:145`, `= cz`, so
`≥ cz` is immediate); `hperp` is `AenvfixProbe.Ctx`'s own `vl ⊥ nℓ`. -/
theorem kk_unbounded_of_itemII
    {A B : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ} {vl g₁ nℓ : ℤ × ℤ} {cz : ℤ}
    (hperp : dot nℓ vl = 0)
    (itemII : ItemII B nℓ cz)
    (hB_sub_A : ∀ i, B i ⊆ A i)
    (hg₁_level : cz ≤ dot nℓ g₁)
    (hkk_max : ∀ i t : ℕ, g₁ + (t : ℤ) • vl ∈ A i → t ≤ kk i) :
    ∀ N : ℕ, ∃ i, N ≤ kk i := by
  intro N
  set i : ℕ := (|g₁.1| + |g₁.2| + (N : ℤ) * (|vl.1| + |vl.2|) + 2).toNat with hi_def
  have hi_cast : (i : ℤ) = |g₁.1| + |g₁.2| + (N : ℤ) * (|vl.1| + |vl.2|) + 2 := by
    rw [hi_def, Int.toNat_of_nonneg]; positivity
  refine ⟨i, ?_⟩
  have hmemA : g₁ + (N : ℤ) • vl ∈ A i := by
    apply hB_sub_A i
    apply itemII i
    · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, hi_cast]
      have h1 := abs_add_le (g₁.1) ((N : ℤ) * vl.1)
      have h2 : |(N : ℤ) * vl.1| = (N : ℤ) * |vl.1| := by rw [abs_mul, Nat.abs_cast]
      have h3 : 0 ≤ (N : ℤ) * |vl.2| := by positivity
      nlinarith [abs_nonneg g₁.2, abs_nonneg vl.1, abs_nonneg vl.2]
    · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, hi_cast]
      have h1 := abs_add_le (g₁.2) ((N : ℤ) * vl.2)
      have h2 : |(N : ℤ) * vl.2| = (N : ℤ) * |vl.2| := by rw [abs_mul, Nat.abs_cast]
      have h3 : 0 ≤ (N : ℤ) * |vl.1| := by positivity
      nlinarith [abs_nonneg g₁.1, abs_nonneg vl.1, abs_nonneg vl.2]
    · have hlevel : dot nℓ (g₁ + (N : ℤ) • vl) = dot nℓ g₁ := by
        rw [dot_add]
        simp only [dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at hperp ⊢
        nlinarith [hperp]
      rw [hlevel]; exact hg₁_level
  exact hkk_max i N hmemA

/-- **Wired to the concrete `AenvfixProbe` chain.**  Everything is discharged except
`hAhatConv` — union lattice-convexity, which (per the correction above) is only free *after*
subsequence extraction (`LeafAWire.exists_subseq_chain_of_itemII`), so it stays an explicit
hypothesis here on the raw index; a caller applying `ofParts` post-extraction supplies it via
`ChainAssemble.latticeConvex_iUnion_hatOf` on the reindexed chain, with `A := chA c s₀ ∘ σ` etc.
substituted throughout. -/
theorem rec_p_wired
    {ξ xper : Config ℤ} {S : Finset (ℤ × ℤ)} {vl nℓ : ℤ × ℤ} {cz : ℤ}
    (c : AenvfixProbe.Ctx ξ xper S vl nℓ) (s₀ : AenvfixProbe.St ξ xper S nℓ cz)
    (hvl : vl ≠ 0) (hne : (AenvfixProbe.chA c s₀ 0).Nonempty)
    (hAhatConv : IsLatticeConvexRegion
      (⋃ i, hatOf (AenvfixProbe.chA c s₀) (LeafAWire.kkOf c s₀ hvl c.hperp hne) vl i)) :
    ∀ g ∈ ⋃ i, hatOf (AenvfixProbe.chA c s₀) (LeafAWire.kkOf c s₀ hvl c.hperp hne) vl i,
      g + (-vl) ∈ ⋃ i, hatOf (AenvfixProbe.chA c s₀) (LeafAWire.kkOf c s₀ hvl c.hperp hne) vl i := by
  apply rec_p_of_anchor
  · exact fun i => LeafAWire.chA_latticeConvex c s₀ i
  · exact AenvfixProbe.subBA_ch c s₀
  · exact AenvfixProbe.subAB_ch c s₀
  · exact LeafAWire.anchorPoint_mem c s₀ hne
  · exact LeafAWire.kkOf_mem c s₀ hvl c.hperp hne
  · exact kk_unbounded_of_itemII c.hperp (AenvfixProbe.itemII_ch c s₀) (AenvfixProbe.subBA_ch c s₀)
      (le_of_eq (LeafAWire.anchorPoint_level c s₀ hne).symm)
      (LeafAWire.kkOf_max c s₀ hvl c.hperp hne)
  · exact hAhatConv

end Nivat.LeafARecP

#print axioms Nivat.LeafARecP.rec_p_of_anchor
#print axioms Nivat.LeafARecP.kk_unbounded_of_itemII
#print axioms Nivat.LeafARecP.rec_p_wired
