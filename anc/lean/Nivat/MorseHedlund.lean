/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.Words

/-!
# The one-dimensional Morse–Hedlund theorem

This file proves the one-dimensional Morse–Hedlund theorem: a bi-infinite sequence
`x : ℤ → β` over a finite alphabet `β` whose number of length-`n` subwords is at most `n`
(for some `n > 0`) must be periodic.

This is used in `Nivat.AppendixD` (Appendix D of the paper) to conclude periodicity of a
one-dimensional sequence from a low subword-complexity bound.

## Main definitions

* `Nivat.subwords x n` : the set of length-`n` subwords occurring in `x : ℤ → β`.

## Main results

* `Nivat.periodic_of_subwords_le` : the Morse–Hedlund theorem.

## Status

Complete. `periodic_of_subwords_le` is fully proved, no `sorry`.

The proof reduces to `Nivat.periodic_of_two_sided_determinacy` (from `Nivat.Words`) with
`Q := 1`: either the length-`1` subword complexity is already `1` (so `x` is constant, and
`q := 1` works trivially), or the subword-complexity function `k ↦ (subwords x k).ncard`
has a "plateau" `p k = p (k+1)` for some `k < n`; at a plateau, the drop-last-symbol and
drop-first-symbol maps `(Fin (k+1) → β) → (Fin k → β)` are surjections between finite sets
of equal cardinality between `subwords x (k+1)` and `subwords x k`, hence bijections, hence
injective; injectivity of the drop-last map gives the forward determinacy condition and
injectivity of the drop-first map gives the backward determinacy condition needed to invoke
`periodic_of_two_sided_determinacy`.

Note: the theorem requires `[Finite β]`. Without it, `(subwords x n).ncard ≤ n` can hold
vacuously (`Set.ncard` of an infinite set is defined to be `0`) while `x` is not periodic,
e.g. `β := ℤ`, `x := id`, `n := 1`.
-/

namespace Nivat

/-- The set of length-`n` subwords occurring in the bi-infinite sequence `x`. -/
def subwords {β : Type*} (x : ℤ → β) (n : ℕ) : Set (Fin n → β) :=
  Set.range fun i : ℤ => fun l : Fin n => x (i + (l.val : ℤ))

/-- **The one-dimensional Morse–Hedlund theorem.**  If a bi-infinite sequence `x : ℤ → β`
over a finite alphabet has at most `n` subwords of length `n` (for some `n > 0`), then `x`
is periodic. -/
theorem periodic_of_subwords_le {β : Type*} [Finite β] (x : ℤ → β) {n : ℕ} (hn : 0 < n)
    (h : (subwords x n).ncard ≤ n) : ∃ q : ℕ, 0 < q ∧ ∀ i : ℤ, x (i + q) = x i := by
  classical
  -- `W k i` is the length-`k` window starting at position `i`.
  let W : ∀ k : ℕ, ℤ → (Fin k → β) := fun k i l => x (i + (l.val : ℤ))
  have hsub : ∀ k : ℕ, subwords x k = Set.range (W k) := fun k => rfl
  -- the "drop last symbol" and "drop first symbol" maps
  let dl : ∀ k : ℕ, (Fin (k + 1) → β) → (Fin k → β) := fun k w l => w ⟨l.val, by omega⟩
  let dr : ∀ k : ℕ, (Fin (k + 1) → β) → (Fin k → β) := fun k w l => w ⟨l.val + 1, by omega⟩
  have hdl_W : ∀ k i, dl k (W (k + 1) i) = W k i := by
    intro k i; funext l; rfl
  have hdr_W : ∀ k i, dr k (W (k + 1) i) = W k (i + 1) := by
    intro k i; funext l
    show x (i + ((⟨l.val + 1, by omega⟩ : Fin (k + 1)).val : ℤ)) = x (i + 1 + (l.val : ℤ))
    congr 1; push_cast; ring
  -- both maps send `subwords x (k+1)` onto `subwords x k`
  have himg_dl : ∀ k : ℕ, dl k '' subwords x (k + 1) = subwords x k := by
    intro k
    rw [hsub k, hsub (k + 1)]
    apply Set.Subset.antisymm
    · rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩; exact ⟨i, hdl_W k i⟩
    · rintro _ ⟨i, rfl⟩; exact ⟨W (k + 1) i, ⟨i, rfl⟩, hdl_W k i⟩
  have himg_dr : ∀ k : ℕ, dr k '' subwords x (k + 1) = subwords x k := by
    intro k
    rw [hsub k, hsub (k + 1)]
    apply Set.Subset.antisymm
    · rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩; exact ⟨i + 1, (hdr_W k i).symm⟩
    · rintro _ ⟨i, rfl⟩
      refine ⟨W (k + 1) (i - 1), ⟨i - 1, rfl⟩, ?_⟩
      rw [hdr_W k (i - 1)]
      congr 1
      ring
  have hfin : ∀ k : ℕ, (subwords x k).Finite := fun k => Set.toFinite _
  have hne : ∀ k : ℕ, (subwords x k).Nonempty := fun k => ⟨W k 0, 0, rfl⟩
  set p : ℕ → ℕ := fun k => (subwords x k).ncard with hp_def
  have h' : p n ≤ n := h
  have hp_mono : ∀ k : ℕ, p k ≤ p (k + 1) := by
    intro k
    have hle := Set.ncard_image_le (f := dl k) (hfin (k + 1))
    rw [himg_dl k] at hle
    exact hle
  have hp1_pos : 0 < p 1 := (Set.ncard_pos (hfin 1)).2 (hne 1)
  by_cases hstrict : ∀ k : ℕ, 1 ≤ k → k < n → p k < p (k + 1)
  · -- Case A: the complexity is strictly increasing all the way, forcing `p 1 = 1`.
    have hind : ∀ m : ℕ, 1 ≤ m → m ≤ n → p 1 + (m - 1) ≤ p m := by
      intro m hm
      induction m, hm using Nat.le_induction with
      | base => intro _; omega
      | succ m hm ih =>
        intro hmn
        have hstep := hstrict m hm (by omega)
        have := ih (by omega)
        omega
    have hi := hind n hn (le_refl n)
    have hp1_eq : p 1 = 1 := by omega
    obtain ⟨a, ha⟩ := Set.ncard_eq_one.mp hp1_eq
    have hWa : ∀ i : ℤ, W 1 i = a := by
      intro i
      have : W 1 i ∈ subwords x 1 := ⟨i, rfl⟩
      rw [ha] at this
      exact this
    have hconst : ∀ i : ℤ, x i = a ⟨0, by omega⟩ := by
      intro i
      have := congrFun (hWa i) ⟨0, by omega⟩
      simpa [W] using this
    refine ⟨1, one_pos, fun i => ?_⟩
    have e1 := hconst (i + 1)
    have e2 := hconst i
    push_cast
    rw [e1, e2]
  · -- Case B: there is a "plateau" `p k = p (k+1)` with `1 ≤ k < n`.
    push Not at hstrict
    obtain ⟨k, hk1, hkn, hknlt⟩ := hstrict
    have hpk_eq : p k = p (k + 1) := le_antisymm (hp_mono k) hknlt
    have hk_pos : 0 < k := hk1
    -- injectivity of the drop-last and drop-first maps on `subwords x (k+1)`
    have hinj_dl : Set.InjOn (dl k) (subwords x (k + 1)) := by
      apply Set.injOn_of_ncard_image_eq (hs := hfin (k + 1))
      rw [himg_dl k]
      exact hpk_eq
    have hinj_dr : Set.InjOn (dr k) (subwords x (k + 1)) := by
      apply Set.injOn_of_ncard_image_eq (hs := hfin (k + 1))
      rw [himg_dr k]
      exact hpk_eq
    have hwin_eq : ∀ i j : ℤ, (∀ l : ℕ, l < k → x (i + l) = x (j + l)) → W k i = W k j := by
      intro i j hij
      funext l
      show x (i + (l.val : ℤ)) = x (j + (l.val : ℤ))
      exact hij l.val l.isLt
    have hfwd : ∀ i j : ℤ, (i : ZMod 1) = (j : ZMod 1) →
        (∀ l : ℕ, l < k → x (i + l) = x (j + l)) → x (i + k) = x (j + k) := by
      intro i j _ hij
      have heq : dl k (W (k + 1) i) = dl k (W (k + 1) j) := by
        rw [hdl_W k i, hdl_W k j]; exact hwin_eq i j hij
      have hmem_i : W (k + 1) i ∈ subwords x (k + 1) := ⟨i, rfl⟩
      have hmem_j : W (k + 1) j ∈ subwords x (k + 1) := ⟨j, rfl⟩
      have := hinj_dl hmem_i hmem_j heq
      have := congrFun this ⟨k, by omega⟩
      simpa [W] using this
    have hbwd : ∀ i j : ℤ, (i : ZMod 1) = (j : ZMod 1) →
        (∀ l : ℕ, l < k → x (i + l) = x (j + l)) → x (i - 1) = x (j - 1) := by
      intro i j _ hij
      have heq : dr k (W (k + 1) (i - 1)) = dr k (W (k + 1) (j - 1)) := by
        rw [hdr_W k (i - 1), hdr_W k (j - 1), show i - 1 + 1 = i by ring,
          show j - 1 + 1 = j by ring]
        exact hwin_eq i j hij
      have hmem_i : W (k + 1) (i - 1) ∈ subwords x (k + 1) := ⟨i - 1, rfl⟩
      have hmem_j : W (k + 1) (j - 1) ∈ subwords x (k + 1) := ⟨j - 1, rfl⟩
      have := hinj_dr hmem_i hmem_j heq
      have := congrFun this ⟨0, by omega⟩
      simpa [W] using this
    obtain ⟨Q', hQ'pos, -, hQ'per⟩ :=
      periodic_of_two_sided_determinacy (β := β) (Q := 1) (K := k) one_pos hk_pos x hfwd hbwd
    exact ⟨Q', hQ'pos, hQ'per⟩

end Nivat
