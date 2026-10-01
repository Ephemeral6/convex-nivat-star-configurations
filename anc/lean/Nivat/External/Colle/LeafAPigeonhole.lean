import Mathlib.Data.Nat.Nth
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Fintype.Pi

set_option autoImplicit false

namespace Nivat

/-- **Pigeonhole collapse of a residue-`h` invariant along a strictly increasing subsequence.**
`b3_colle2.txt:496`: `x_per`'s period `vl` collapses the private endpoint shifts `k_i` into
finitely many residue classes mod the period length `h`; some class is hit infinitely often,
and reindexing along that class gives a common residue `r` for *every* index of the
subsequence. This is the one genuinely combinatorial (not topological) step the compactness
argument at `:496-510` needs before the accumulation-point machinery
(`Nivat.exists_limit_agreeing_along_growing_windows`, `LeafALimit.lean`) applies. -/
theorem exists_strictMono_const_mod {h : ℕ} (hh : 0 < h) (kk : ℕ → ℕ) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ r : ℕ, ∀ i, kk (σ i) % h = r := by
  classical
  have hcover : (Set.univ : Set ℕ) =
      ⋃ r ∈ Finset.range h, {n : ℕ | kk n % h = r} := by
    ext n
    simp only [Set.mem_univ, Set.mem_iUnion, Set.mem_ofPred_eq, Finset.mem_range, true_iff]
    exact ⟨kk n % h, Nat.mod_lt _ hh, rfl⟩
  have hex : ∃ r ∈ Finset.range h, {n : ℕ | kk n % h = r}.Infinite := by
    by_contra hc
    push Not at hc
    have hfin : (⋃ r ∈ Finset.range h, {n : ℕ | kk n % h = r}).Finite :=
      Set.Finite.biUnion (Finset.range h).finite_toSet
        (fun r hr => hc r hr)
    rw [← hcover] at hfin
    exact Set.infinite_univ hfin
  obtain ⟨r, -, hr⟩ := hex
  refine ⟨Nat.nth (fun n => kk n % h = r), Nat.nth_strictMono hr, r, fun i => ?_⟩
  exact Nat.nth_mem_of_infinite hr i

#print axioms exists_strictMono_const_mod

/-- **Finite-product pigeonhole: a bounded `Fin k → ℕ`-valued sequence is literally constant
along a strictly-monotone subsequence.**  Generalises `exists_strictMono_const_mod` (a single
residue class mod `h`, i.e. `k = 1` with `B = fun _ => h`) to a `k`-tuple of simultaneously
bounded coordinates.  Feeds `b3_colle2.txt:498-504`'s second subsequence extraction: for
`ι+1 ≤ j ≤ J-1` (finitely many `j`, indexed here by `Fin k`), the edge-length tuple
`(|Â_i ∩ w_i(j)|)_j` is a `Fin k → ℕ`-valued sequence; once it is known to be bounded
(each coordinate `< B j`, from `J`'s minimality forcing eventual non-growth on a fixed
bound), this pigeonhole extracts a subsequence on which the tuple is constant for every
index at once — matching the paper's "we may assume that ... for every `ι+1 ≤ j ≤ J-1`
and all `i`" (not just eventually: literally all `i` of the extracted subsequence). -/
theorem exists_strictMono_const_of_bounded {k : ℕ} (B : Fin k → ℕ)
    (kk : ℕ → Fin k → ℕ) (hkk : ∀ n i, kk n i < B i) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ r : Fin k → ℕ, ∀ n, kk (σ n) = r := by
  classical
  set tuples : Finset (Fin k → ℕ) := Fintype.piFinset (fun i => Finset.range (B i)) with htuples
  have hcover : (Set.univ : Set ℕ) = ⋃ v ∈ tuples, {n : ℕ | kk n = v} := by
    ext n
    simp only [Set.mem_univ, Set.mem_iUnion, Set.mem_ofPred_eq, true_iff]
    refine ⟨kk n, ?_, rfl⟩
    rw [htuples, Fintype.mem_piFinset]
    exact fun i => Finset.mem_range.mpr (hkk n i)
  have hex : ∃ v ∈ tuples, {n : ℕ | kk n = v}.Infinite := by
    by_contra hc
    push Not at hc
    have hfin : (⋃ v ∈ tuples, {n : ℕ | kk n = v}).Finite :=
      Set.Finite.biUnion tuples.finite_toSet (fun v hv => hc v hv)
    rw [← hcover] at hfin
    exact Set.infinite_univ hfin
  obtain ⟨v, -, hv⟩ := hex
  refine ⟨Nat.nth (fun n => kk n = v), Nat.nth_strictMono hv, v, fun n => ?_⟩
  exact Nat.nth_mem_of_infinite hv n

#print axioms exists_strictMono_const_of_bounded

/-- **`product_pigeonhole`** — the exact shape `tmp/wip/LeafAJSelect.lean`'s
`exists_eventually_const_before` consumes (lane-recp, 2026-09-22): a `ℕ`-indexed family of
`Fin k → ℕ` tuples, uniformly bounded by `M`, has a strictly-monotone subsequence along which
every coordinate is (not just eventually, but from the very first index `i₀ := 0`) constant.
A trivial corollary of `exists_strictMono_const_of_bounded` (`B := fun _ => M + 1`, since
`f i j ≤ M ↔ f i j < M + 1`); kept as its own named lemma so callers can `exact` it against
the literal `product_pigeonhole` signature without repackaging. -/
theorem product_pigeonhole {k M : ℕ} (f : ℕ → Fin k → ℕ) (hbdd : ∀ i j, f i j ≤ M) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ i₀ : ℕ, ∀ j : Fin k, ∀ i ≥ i₀, f (σ i) j = f (σ i₀) j := by
  obtain ⟨σ, hσmono, r, hr⟩ :=
    exists_strictMono_const_of_bounded (fun _ : Fin k => M + 1) f
      (fun n j => Nat.lt_succ_of_le (hbdd n j))
  exact ⟨σ, hσmono, 0, fun j i _ => by rw [hr i, hr 0]⟩

#print axioms product_pigeonhole

end Nivat
