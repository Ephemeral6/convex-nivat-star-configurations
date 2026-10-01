/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.Defs.Orbit

/-!
# Subsequential limits along an infinite set of times

A refinement of `Nivat.subseqLimits_nonempty` needed by the proof of Proposition 8.14 and of
Lemma 8.16 in *The Convex Nivat Conjecture* (Pan): the sequence
`n ↦ T^{n • d} G` has a subsequential limit **whose times can be taken inside a prescribed
infinite set `S ⊆ ℕ`**.

This is what §8 Step 2(a) consumes.  There one assumes, for contradiction, that the set `S` of
times at which `T^{n d} G` disagrees with every element of `Ω = subseqLimits G d` on a fixed
window is infinite, and extracts a limit `y` along `S`.  The point is that `y` is
simultaneously
* a genuine element of `Ω` (an infinite subset of `ℕ` is still cofinal in `ℕ`), and
* approximated at times lying in `S`,

which is the contradiction.  Both halves come out of the single statement
`Nivat.exists_mem_subseqLimits_along`.

The proof is that of `Nivat.subseqLimits_nonempty` with one change: the ultrafilter refines
`atTop ⊓ 𝓟 S` instead of `atTop`.  That filter is `NeBot` precisely because `S` is infinite,
and an ultrafilter above it contains `S` as well as every tail `{n | M ≤ n}`.

## Main results

* `Nivat.exists_cofinal_mem_of_infinite` — an infinite set of naturals meets every tail.
* `Nivat.exists_mem_subseqLimits_along` — the compactness statement.

## Status

Complete; no `sorry`.
-/

namespace Nivat

open Filter

/-- An infinite set of naturals is cofinal: it meets every tail `{n | M ≤ n}`.

Stated separately because it is exactly the `NeBot` input for `atTop ⊓ 𝓟 S` below. -/
theorem exists_cofinal_mem_of_infinite {S : Set ℕ} (hS : S.Infinite) (M : ℕ) :
    ∃ n ∈ S, M ≤ n := by
  by_contra hcon
  refine hS (Set.Finite.subset (Set.finite_lt_nat M) fun n hn => ?_)
  show n < M
  by_contra hlt
  exact hcon ⟨n, hn, not_lt.1 hlt⟩

/-- **Compactness of `α^{ℤ²}` along an infinite set of times.**  For finite `α` and any
infinite `S ⊆ ℕ`, the sequence `n ↦ T^{n • d} G` has a subsequential limit `y` that is
approximated at times taken from `S`.  In particular `y ∈ subseqLimits G d`.

Paper §8, Step 2(a) of the proof of Lemma 8.16 (and Proposition 8.14).  This strengthens
`Nivat.subseqLimits_nonempty`, which is the case `S = Set.univ`.

The limit is read off from any ultrafilter `𝔲` refining `atTop ⊓ 𝓟 S`, which is `NeBot`
because `S` is infinite: for each `w` the pushforward of `𝔲` along `n ↦ G (w + n d)` is an
ultrafilter on the finite type `α`, hence principal at a unique value, and that value is
`y w`.  Since `S ∈ 𝔲` the witnessing times can be found in `S`. -/
theorem exists_mem_subseqLimits_along {α : Type*} [Finite α] (G : Config α) (d : ℤ × ℤ)
    {S : Set ℕ} (hS : S.Infinite) :
    ∃ y ∈ subseqLimits G d,
      ∀ (W : Finset (ℤ × ℤ)) (M : ℕ), ∃ n ∈ S, M ≤ n ∧ ∀ w ∈ W, y w = G (w + (n : ℤ) • d) := by
  classical
  have hne : (atTop ⊓ 𝓟 S).NeBot := by
    rw [← frequently_mem_iff_neBot, frequently_atTop]
    intro a
    obtain ⟨n, hnS, hna⟩ := exists_cofinal_mem_of_infinite hS a
    exact ⟨n, hna, hnS⟩
  set 𝔲 : Ultrafilter ℕ := Ultrafilter.of (atTop ⊓ 𝓟 S) with h𝔲
  -- Every tail, and `S` itself, belong to `𝔲`.
  have hle : (𝔲 : Filter ℕ) ≤ atTop ⊓ 𝓟 S := Ultrafilter.of_le _
  have hSmem : S ∈ 𝔲 := hle (mem_inf_of_right (mem_principal_self S))
  -- For each `w` the colour `G (w + n d)` is `𝔲`-almost everywhere constant.
  have key : ∀ w : ℤ × ℤ, ∃ a : α, {n : ℕ | G (w + (n : ℤ) • d) = a} ∈ 𝔲 := by
    intro w
    obtain ⟨a, ha⟩ :=
      Ultrafilter.eq_pure_of_finite (Ultrafilter.map (fun n : ℕ => G (w + (n : ℤ) • d)) 𝔲)
    refine ⟨a, ?_⟩
    have hmem : ({a} : Set α) ∈ Ultrafilter.map (fun n : ℕ => G (w + (n : ℤ) • d)) 𝔲 := by
      rw [ha]; exact Ultrafilter.mem_pure.mpr rfl
    rwa [Ultrafilter.mem_map] at hmem
  choose y hy using key
  have main : ∀ (W : Finset (ℤ × ℤ)) (M : ℕ),
      ∃ n ∈ S, M ≤ n ∧ ∀ w ∈ W, y w = G (w + (n : ℤ) • d) := by
    intro W M
    have h1 : {n : ℕ | M ≤ n} ∈ 𝔲 := hle (mem_inf_of_left (mem_atTop M))
    have h2 : (⋂ w ∈ W, {n : ℕ | G (w + (n : ℤ) • d) = y w}) ∈ 𝔲 :=
      (Filter.biInter_finset_mem W).mpr fun w _ => hy w
    obtain ⟨n, hn⟩ := Ultrafilter.nonempty_of_mem (Filter.inter_mem hSmem (Filter.inter_mem h1 h2))
    refine ⟨n, hn.1, hn.2.1, fun w hw => ?_⟩
    have hn2 := hn.2.2
    simp only [Set.mem_iInter, Set.mem_ofPred_eq] at hn2
    exact (hn2 w hw).symm
  exact ⟨y, fun W M => (main W M).imp fun _ h => ⟨h.2.1, h.2.2⟩, main⟩

end Nivat
