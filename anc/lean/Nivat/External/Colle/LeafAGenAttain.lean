/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.LatticeEdges

/-!
# `LeafAGenAttain` — turning `hattain` into per-direction boundedness (lane-leafa-gen)

`shellEnv`'s residue contains (`tmp/wip/lane-leafa-shell-shellenv.lean`,
`shellEnv_of_wedge` §10, the `hattain` binder):

```lean
hattain : ∀ i, i₀ ≤ i → ∀ n : ℤ × ℤ, 0 < dot n w → dot n vJ1 ≤ 0 →
  ∃ z ∈ hatOf A kk vl i, ∀ g ∈ (⋃ j, hatOf A kk vl j), dot n g ≤ dot n z
```

i.e. «`Â_i` already attains `Â_∞`'s supremum in direction `n`» — the formal reading of
`b3_colle2.txt:516`'s "for an appropriate `ε ∈ ℕ` fixed and all `i` sufficiently large".

⚠ **The expensive part is not attainment, it is that `i₀` is uniform in `n`.**  Per direction,
attainment is nearly free (§2 below: a nonempty set of integers bounded above has a maximum).
What costs is one index working for *every* `n` at once.  This file isolates that:

* **§1** — if the directions range over a **`Finset`**, uniformity is a `Finset.sup`: take the
  max of the per-direction witness indices and let monotonicity carry it.  So over a finite
  set of normals `hattain` is exactly «per-direction attainment», no uniformity surcharge.
* **§2** — per-direction attainment reduces to **boundedness** of `dot n` on `Â_∞`.
* **§3** — composed: over a `Finset` of directions, `hattain` ⟸ per-direction boundedness.
* **§4** — kernel witnesses that both hypotheses of §1 are load-bearing, and that the
  `Finset` cannot be dropped for free.

⛔ **What this file does not do.**  It does not prove `dot n` is bounded above on `Â_∞` for any
particular `n` — that is the geometric content (`Â_∞`'s recession directions) and belongs to
whoever owns the tower.  It also does not decide *which* finite set of normals suffices; see
the note below.

## Why a `Finset` of normals is the right shape (§59 reading of the consumer)

`enveloped_of_two_sweeps` (`tmp/wip/lane-leafa-shell-shellenv.lean:648`) uses `hattain` exactly
three times, and **every one of them already has an edge-normal hypothesis in scope**:

| use | line | hypothesis in scope |
|---|---|---|
| `hfaceUT`, positive-`w` / non-positive-`v` branch | `:673-676` | `hn : n ∈ E U` |
| `hUT`, same branch | `:684-685` | `hn : n ∈ E U` |
| `hTU`, same branch | `:694-695` | `hn : n ∈ E T` |

and `E U = E ↑𝒮_φ` is finite (`hUE`, `:649`).  That file's `:642-643` states the opposite
(«both uses need it at normals that are not known in advance to be edge normals»); ⚠ this
file does **not** silently act on that discrepancy — the weakening has to be made in the
owning lane, and only the `E U` two of the three are covered by a finite `Finset` anyway
(`E T` is not known finite a priori).  §1/§3 are stated for an arbitrary `Finset` so they
apply the moment that reduction is made, and are independently true regardless.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Nivat.LeafAGenAttain

open Nivat Nivat.LE2

/-! ## §1. Uniformity over a `Finset` of directions is a `Finset.sup`

Monotonicity is what makes this work: a witness found at index `j` stays a witness at every
`i ≥ j`, so the single index `N.sup f` serves all of `N` at once. -/

theorem exists_uniform_attain_of_finset {C : ℕ → Set (ℤ × ℤ)}
    (hmono : ∀ i j : ℕ, i ≤ j → C i ⊆ C j) (N : Finset (ℤ × ℤ))
    (hpt : ∀ n ∈ N, ∃ j : ℕ, ∃ z ∈ C j, ∀ g ∈ (⋃ k, C k), dot n g ≤ dot n z) :
    ∃ i₀ : ℕ, ∀ i, i₀ ≤ i → ∀ n ∈ N,
      ∃ z ∈ C i, ∀ g ∈ (⋃ k, C k), dot n g ≤ dot n z := by
  classical
  choose! f z hz hmax using hpt
  refine ⟨N.sup f, fun i hi n hn => ⟨z n, ?_, hmax n hn⟩⟩
  exact hmono (f n) i (le_trans (Finset.le_sup hn) hi) (hz n hn)

/-! ## §2. Per-direction attainment is boundedness

`dot n` takes integer values, so a nonempty set of them that is bounded above has a greatest
element; the point realising it lies in some layer. -/

theorem exists_attain_of_bddAbove {C : ℕ → Set (ℤ × ℤ)}
    (hne : (⋃ k, C k).Nonempty) (n : ℤ × ℤ)
    (hbdd : ∃ M : ℤ, ∀ g ∈ (⋃ k, C k), dot n g ≤ M) :
    ∃ j : ℕ, ∃ z ∈ C j, ∀ g ∈ (⋃ k, C k), dot n g ≤ dot n z := by
  classical
  obtain ⟨M, hM⟩ := hbdd
  obtain ⟨g₀, hg₀⟩ := hne
  obtain ⟨m, ⟨zm, hzm, hzmeq⟩, hlub⟩ :=
    Int.exists_greatest_of_bdd (P := fun m : ℤ => ∃ g ∈ (⋃ k, C k), dot n g = m)
      ⟨M, fun m hm => by obtain ⟨g, hg, rfl⟩ := hm; exact hM g hg⟩
      ⟨dot n g₀, g₀, hg₀, rfl⟩
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hzm
  refine ⟨j, zm, hj, fun g hg => ?_⟩
  rw [hzmeq]
  exact hlub (dot n g) ⟨g, hg, rfl⟩

/-! ## §3. Composed

Over a `Finset` of directions, the whole `hattain` binder — uniform index included — costs
exactly «`dot n` is bounded above on `Â_∞`, for each of those finitely many `n`». -/

theorem exists_uniform_attain_of_bddAbove {C : ℕ → Set (ℤ × ℤ)}
    (hmono : ∀ i j : ℕ, i ≤ j → C i ⊆ C j) (hne : (⋃ k, C k).Nonempty)
    (N : Finset (ℤ × ℤ))
    (hbdd : ∀ n ∈ N, ∃ M : ℤ, ∀ g ∈ (⋃ k, C k), dot n g ≤ M) :
    ∃ i₀ : ℕ, ∀ i, i₀ ≤ i → ∀ n ∈ N,
      ∃ z ∈ C i, ∀ g ∈ (⋃ k, C k), dot n g ≤ dot n z :=
  exists_uniform_attain_of_finset hmono N
    (fun n hn => exists_attain_of_bddAbove hne n (hbdd n hn))

/-! ## §4. Kernel witnesses

⛔ §54: these refute the **stated general forms**; they say nothing about the real tower. -/

/-- **Monotonicity is load-bearing in §1.**  Without it a per-direction witness at index `j`
need not survive to larger `i`, and no uniform index exists. -/
theorem not_uniform_attain_without_mono :
    ¬ (∀ (C : ℕ → Set (ℤ × ℤ)) (N : Finset (ℤ × ℤ)),
        (∀ n ∈ N, ∃ j : ℕ, ∃ z ∈ C j, ∀ g ∈ (⋃ k, C k), dot n g ≤ dot n z) →
        ∃ i₀ : ℕ, ∀ i, i₀ ≤ i → ∀ n ∈ N,
          ∃ z ∈ C i, ∀ g ∈ (⋃ k, C k), dot n g ≤ dot n z) := by
  intro h
  have hhyp : ∀ n ∈ ({((1 : ℤ), (0 : ℤ))} : Finset (ℤ × ℤ)),
      ∃ j : ℕ, ∃ z ∈ (fun k => if k = 0 then {((0 : ℤ), (0 : ℤ))} else ∅ : ℕ → Set (ℤ × ℤ)) j,
        ∀ g ∈ (⋃ k, (fun k => if k = 0 then {((0 : ℤ), (0 : ℤ))} else ∅ : ℕ → Set (ℤ × ℤ)) k),
          dot n g ≤ dot n z := by
    intro n _
    refine ⟨0, ((0 : ℤ), (0 : ℤ)), by simp, fun g hg => ?_⟩
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hg
    by_cases hk0 : k = 0
    · subst hk0; simp at hk; subst hk; exact le_rfl
    · simp [hk0] at hk
  obtain ⟨i₀, hi₀⟩ := h _ _ hhyp
  obtain ⟨z, hz, -⟩ := hi₀ (i₀ + 1) (by omega) ((1 : ℤ), (0 : ℤ)) (by simp)
  simp at hz

/-- **Boundedness is load-bearing in §2**: an unbounded `dot n` attains no supremum. -/
theorem not_attain_without_bddAbove :
    ¬ (∀ (C : ℕ → Set (ℤ × ℤ)) (n : ℤ × ℤ), (⋃ k, C k).Nonempty →
        ∃ j : ℕ, ∃ z ∈ C j, ∀ g ∈ (⋃ k, C k), dot n g ≤ dot n z) := by
  intro h
  obtain ⟨j, z, hz, hmax⟩ :=
    h (fun k => {((k : ℤ), (0 : ℤ))}) ((1 : ℤ), (0 : ℤ)) ⟨((0 : ℤ), (0 : ℤ)), by
      exact Set.mem_iUnion.mpr ⟨0, by simp⟩⟩
  simp only [Set.mem_singleton_iff] at hz
  subst hz
  have hstep : dot ((1 : ℤ), (0 : ℤ)) (((j : ℤ) + 1), (0 : ℤ)) ≤
      dot ((1 : ℤ), (0 : ℤ)) (((j : ℤ)), (0 : ℤ)) :=
    hmax _ (Set.mem_iUnion.mpr ⟨j + 1, by simp⟩)
  simp [Nivat.LE2.dot] at hstep

end Nivat.LeafAGenAttain

#print axioms Nivat.LeafAGenAttain.exists_uniform_attain_of_finset
#print axioms Nivat.LeafAGenAttain.exists_attain_of_bddAbove
#print axioms Nivat.LeafAGenAttain.exists_uniform_attain_of_bddAbove
#print axioms Nivat.LeafAGenAttain.not_uniform_attain_without_mono
#print axioms Nivat.LeafAGenAttain.not_attain_without_bddAbove
