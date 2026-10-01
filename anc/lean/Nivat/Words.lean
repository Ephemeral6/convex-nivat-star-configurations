/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Set.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Finite-state periodicity lemmas for bi-infinite sequences, used in Appendix D and §8.3

This file proves, independently of the rest of the project, classical facts about bi-infinite
sequences `ℤ → β`:

* a two-sided finite-state periodicity lemma, which is the argument of step (6) of Lemma D.7 of
  Appendix D and is quoted again as Lemma 8.8 of §8.3;
* a one-sided variant, needed for the half-plane case of Lemma 8.8, where the two-sided
  hypotheses are only available on a half-line `i ≥ t0` (resp. `i ≤ t0`);
* its mirror image, obtained from the one-sided lemma by the reflection `z n := y (-n)`, for the
  other half-plane.

These statements concern only bi-infinite sequences and are otherwise unrelated to the rest of
the development, so this file has no dependence on any other `Nivat.*` file.

-- TODO(lineW): the one-dimensional Morse–Hedlund theorem [13] (step (5) of Lemma D.7) was
-- originally planned for this file but has been assigned to lineL in `Nivat.MorseHedlund`
-- instead, together with the `subwords` definition; neither lives here.

## Main results

* `Nivat.periodic_of_two_sided_determinacy` — the two-sided finite-state lemma.
* `Nivat.periodic_of_one_sided_determinacy` — the one-sided finite-state lemma (half-line
  `i ≥ t0`).
* `Nivat.periodic_of_one_sided_determinacy_neg` — its mirror image (half-line `i ≤ t0`).
-/

namespace Nivat

/-! ### The two-sided finite-state lemma -/

/-- If `y` is periodic with period `d : ℤ` (in the sense `y (i + d) = y i` for all `i`), then it
is periodic with period `d * m` for every natural number `m`. -/
private theorem periodic_nat_mul_of_periodic {β : Type*} {y : ℤ → β} {d : ℤ}
    (hd : ∀ i : ℤ, y (i + d) = y i) : ∀ (m : ℕ) (i : ℤ), y (i + d * m) = y i := by
  intro m
  induction m with
  | zero => intro i; simp
  | succ n ih =>
      intro i
      have e : i + d * ((n : ℤ) + 1) = (i + d * n) + d := by ring
      have e' : i + d * ((n + 1 : ℕ) : ℤ) = i + d * ((n : ℤ) + 1) := by push_cast; ring
      rw [e', e, hd, ih]

/-- **The two-sided finite-state lemma**, the argument of step (6) of Lemma D.7, isolated
because Lemma 8.8 of §8.3 quotes it again.

A bi-infinite sequence `y` over a finite alphabet whose value at `i + K` is determined by the
phase `i mod Q` together with the window `y i, …, y (i + K - 1)`, and whose value at `i - 1` is
determined by the same data, is periodic with a period that is a multiple of `Q`: the map
`Σ i = (i mod Q; y i, …, y (i + K - 1)) ↦ Σ (i + 1)` is a well-defined injection of the finite
set of occurring states into itself, hence a bijection, so the orbit `(Σ i)` is periodic. -/
theorem periodic_of_two_sided_determinacy {β : Type*} [Finite β] {Q K : ℕ} (hQ : 0 < Q)
    (hK : 0 < K) (y : ℤ → β)
    (fwd : ∀ i j : ℤ, (i : ZMod Q) = (j : ZMod Q) →
      (∀ l : ℕ, l < K → y (i + l) = y (j + l)) → y (i + K) = y (j + K))
    (bwd : ∀ i j : ℤ, (i : ZMod Q) = (j : ZMod Q) →
      (∀ l : ℕ, l < K → y (i + l) = y (j + l)) → y (i - 1) = y (j - 1)) :
    ∃ Q' : ℕ, 0 < Q' ∧ Q ∣ Q' ∧ ∀ i : ℤ, y (i + Q') = y i := by
  have : NeZero Q := ⟨hQ.ne'⟩
  classical
  -- The state at position `i` : the phase `i mod Q` together with the length-`K` window.
  let σ : ℤ → ZMod Q × (Fin K → β) :=
    fun i => ((i : ZMod Q), fun l : Fin K => y (i + (l.val : ℤ)))
  have hwin : ∀ a b : ℤ, σ a = σ b ↔
      (a : ZMod Q) = (b : ZMod Q) ∧ ∀ l : ℕ, l < K → y (a + l) = y (b + l) := by
    intro a b
    constructor
    · intro h
      refine ⟨congrArg Prod.fst h, fun l hl => ?_⟩
      have := congrFun (congrArg Prod.snd h) (⟨l, hl⟩ : Fin K)
      simpa using this
    · rintro ⟨h1, h2⟩
      refine Prod.ext h1 ?_
      funext l
      exact h2 l.val l.isLt
  -- One step forward and one step backward preserve equality of states.
  have hstep_fwd : ∀ a b : ℤ, σ a = σ b → σ (a + 1) = σ (b + 1) := by
    intro a b hab
    obtain ⟨h1, h2⟩ := (hwin a b).1 hab
    have hK' : y (a + K) = y (b + K) := fwd a b h1 h2
    rw [hwin]
    refine ⟨by push_cast; rw [h1], fun l hl => ?_⟩
    rcases lt_or_eq_of_le (Nat.succ_le_of_lt hl) with hlt | heq
    · have hh := h2 (l + 1) hlt
      have e1 : a + 1 + (l : ℤ) = a + ((l + 1 : ℕ) : ℤ) := by push_cast; ring
      have e2 : b + 1 + (l : ℤ) = b + ((l + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [e1, e2]; exact hh
    · have hKeq : (l : ℤ) + 1 = (K : ℤ) := by exact_mod_cast heq
      have e1 : a + 1 + (l : ℤ) = a + (K : ℤ) := by linarith
      have e2 : b + 1 + (l : ℤ) = b + (K : ℤ) := by linarith
      rw [e1, e2]; exact hK'
  have hstep_bwd : ∀ a b : ℤ, σ a = σ b → σ (a - 1) = σ (b - 1) := by
    intro a b hab
    obtain ⟨h1, h2⟩ := (hwin a b).1 hab
    have hm1 : y (a - 1) = y (b - 1) := bwd a b h1 h2
    rw [hwin]
    refine ⟨by push_cast; rw [h1], fun l hl => ?_⟩
    rcases Nat.eq_zero_or_pos l with hz | hpos
    · subst hz; simpa using hm1
    · have hl' : l - 1 < K := by omega
      have hh := h2 (l - 1) hl'
      have hcast : ((l - 1 : ℕ) : ℤ) = (l : ℤ) - 1 := by
        have h1l : (1 : ℕ) ≤ l := hpos
        have hns := Nat.cast_sub (R := ℤ) h1l
        simpa using hns
      have e1 : a - 1 + (l : ℤ) = a + ((l - 1 : ℕ) : ℤ) := by rw [hcast]; ring
      have e2 : b - 1 + (l : ℤ) = b + ((l - 1 : ℕ) : ℤ) := by rw [hcast]; ring
      rw [e1, e2]; exact hh
  -- Equality of states propagates in both directions to every integer offset.
  have hinv : ∀ a b : ℤ, σ a = σ b → ∀ d : ℤ, σ (a + d) = σ (b + d) := by
    intro a b hab d
    induction d using Int.induction_on with
    | zero => simpa using hab
    | succ n ih =>
        have e1 : a + ((n : ℤ) + 1) = (a + n) + 1 := by ring
        have e2 : b + ((n : ℤ) + 1) = (b + n) + 1 := by ring
        rw [e1, e2]; exact hstep_fwd _ _ ih
    | pred n ih =>
        have e1 : a + (-(n : ℤ) - 1) = (a + (-(n : ℤ))) - 1 := by ring
        have e2 : b + (-(n : ℤ) - 1) = (b + (-(n : ℤ))) - 1 := by ring
        rw [e1, e2]; exact hstep_bwd _ _ ih
  have hgeneral : ∀ a b : ℤ, a < b → σ a = σ b →
      ∃ Q' : ℕ, 0 < Q' ∧ Q ∣ Q' ∧ ∀ i : ℤ, y (i + Q') = y i := by
    intro a b hab hσab
    set q : ℕ := (b - a).toNat with hqdef
    have hqcast : (q : ℤ) = b - a := Int.toNat_of_nonneg (by linarith)
    have hqpos : 0 < q := by
      have : (0 : ℤ) < q := by rw [hqcast]; linarith
      exact_mod_cast this
    have hper : ∀ n : ℤ, y (n + q) = y n := by
      intro n
      have h1 := hinv a b hσab (n - a)
      have e1 : a + (n - a) = n := by ring
      have e2 : b + (n - a) = n + (q : ℤ) := by rw [hqcast]; ring
      rw [e1, e2] at h1
      have h2 := ((hwin n (n + (q : ℤ))).1 h1).2 0 hK
      simpa using h2.symm
    refine ⟨q * Q, Nat.mul_pos hqpos hQ, ⟨q, by ring⟩, fun i => ?_⟩
    have h3 := periodic_nat_mul_of_periodic hper Q i
    have e : (i : ℤ) + (q : ℤ) * (Q : ℤ) = i + ((q * Q : ℕ) : ℤ) := by push_cast; ring
    rwa [e] at h3
  obtain ⟨i, j, hij, hσij⟩ := Finite.exists_ne_map_eq_of_infinite σ
  rcases lt_or_gt_of_ne hij with h | h
  · exact hgeneral i j h hσij
  · exact hgeneral j i h hσij.symm

/-! ### The one-sided finite-state lemma -/

/-- **The one-sided finite-state lemma**, needed for the half-plane case of Lemma 8.8 of §8.3:
there `fwd`/`bwd` are only available once the *base point* of the window lies in a half-line,
i.e. for `i ≥ t0` resp. `i ≥ t0 + 1`, not for all `i : ℤ` as in
`Nivat.periodic_of_two_sided_determinacy`.  The conclusion is correspondingly one-sided: genuine
(not merely eventual) periodicity is obtained only for `i ≥ t0`, matching the domain where the
hypotheses hold.

The proof: pigeonhole a repeated window `S a = S b` (`a < b`) among the windows based at
`t0, t0 + 1, …`, then walk the match down to the base `S 0 = S (b - a)` using `bwd` (this needs
only *injectivity*, i.e. cancellability, not full bijectivity), then propagate that single
period match forward to every window using `fwd`. -/
theorem periodic_of_one_sided_determinacy {β : Type*} [Finite β] {K : ℕ} (hK : 0 < K)
    (y : ℤ → β) (t0 : ℤ)
    (fwd : ∀ i j : ℤ, t0 ≤ i → t0 ≤ j →
      (∀ l : ℕ, l < K → y (i + l) = y (j + l)) → y (i + K) = y (j + K))
    (bwd : ∀ i j : ℤ, t0 + 1 ≤ i → t0 + 1 ≤ j →
      (∀ l : ℕ, l < K → y (i + l) = y (j + l)) → y (i - 1) = y (j - 1)) :
    ∃ q : ℕ, 0 < q ∧ ∀ i : ℤ, t0 ≤ i → y (i + q) = y i := by
  classical
  have : Fintype β := Fintype.ofFinite β
  let W : ℤ → ℤ → Prop := fun i j => ∀ l : ℕ, l < K → y (i + l) = y (j + l)
  let S : ℕ → (Fin K → β) := fun n l => y (t0 + (n : ℤ) + (l.val : ℤ))
  have hWS : ∀ n m : ℕ, S n = S m ↔ W (t0 + (n : ℤ)) (t0 + (m : ℤ)) := by
    intro n m
    constructor
    · intro h l hl
      have := congrFun h ⟨l, hl⟩
      exact this
    · intro h
      funext l
      exact h l.val l.isLt
  have main : ∀ a b : ℕ, a < b → S a = S b →
      ∃ q : ℕ, 0 < q ∧ ∀ i : ℤ, t0 ≤ i → y (i + q) = y i := by
    intro a b hlt hSab
    have hW0 : W (t0 + (a : ℤ)) (t0 + (b : ℤ)) := (hWS a b).mp hSab
    have hdesc : ∀ m : ℕ, m ≤ a → W (t0 + ((a : ℤ) - m)) (t0 + ((b : ℤ) - m)) := by
      intro m
      induction m with
      | zero => intro _; simpa using hW0
      | succ n ih =>
        intro hmn
        have hna : n ≤ a := by omega
        have hprev := ih hna
        have hi : t0 + 1 ≤ t0 + ((a : ℤ) - n) := by
          have h1 : (n : ℤ) + 1 ≤ (a : ℤ) := by exact_mod_cast hmn
          linarith
        have hj : t0 + 1 ≤ t0 + ((b : ℤ) - n) := by
          have hab' : (a : ℤ) < (b : ℤ) := by exact_mod_cast hlt
          have h1 : (n : ℤ) + 1 ≤ (a : ℤ) := by exact_mod_cast hmn
          linarith
        have hbw := bwd (t0 + ((a : ℤ) - n)) (t0 + ((b : ℤ) - n)) hi hj hprev
        intro l hl
        rcases Nat.eq_zero_or_pos l with hl0 | hlpos
        · subst hl0
          have e1 : t0 + ((a : ℤ) - ((n : ℕ) + 1 : ℕ)) + ((0 : ℕ) : ℤ)
              = t0 + ((a : ℤ) - n) - 1 := by push_cast; ring
          have e2 : t0 + ((b : ℤ) - ((n : ℕ) + 1 : ℕ)) + ((0 : ℕ) : ℤ)
              = t0 + ((b : ℤ) - n) - 1 := by push_cast; ring
          rw [e1, e2]; exact hbw
        · have hl1 : l - 1 < K := by omega
          have hcast : (l : ℤ) = (((l - 1 : ℕ) : ℤ)) + 1 := by
            have hll : l = (l - 1) + 1 := by omega
            exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) hll
          have e1 : t0 + ((a : ℤ) - ((n : ℕ) + 1 : ℕ)) + (l : ℕ)
              = t0 + ((a : ℤ) - n) + ((l - 1 : ℕ) : ℤ) := by rw [hcast]; push_cast; ring
          have e2 : t0 + ((b : ℤ) - ((n : ℕ) + 1 : ℕ)) + (l : ℕ)
              = t0 + ((b : ℤ) - n) + ((l - 1 : ℕ) : ℤ) := by rw [hcast]; push_cast; ring
          rw [e1, e2]
          exact hprev (l - 1) hl1
    set q : ℕ := b - a with hqdef
    have hqpos : 0 < q := by omega
    have hqZ : (q : ℤ) = (b : ℤ) - a := by have h1 : a < b := hlt; omega
    have hbase' : W t0 (t0 + (q : ℤ)) := by
      have h := hdesc a le_rfl
      simp only [sub_self, add_zero] at h
      rwa [hqZ]
    have hup : ∀ n : ℕ, W (t0 + (n : ℤ)) (t0 + (n : ℤ) + (q : ℤ)) := by
      intro n
      induction n with
      | zero => simpa using hbase'
      | succ m ih =>
        intro l hl
        rcases Nat.lt_or_ge (l + 1) K with hlt' | hge
        · have e1 : t0 + (((m : ℕ) + 1 : ℕ) : ℤ) + (l : ℕ)
              = t0 + (m : ℤ) + ((l + 1 : ℕ) : ℤ) := by push_cast; ring
          have e2 : t0 + (((m : ℕ) + 1 : ℕ) : ℤ) + (q : ℤ) + (l : ℕ)
              = t0 + (m : ℤ) + (q : ℤ) + ((l + 1 : ℕ) : ℤ) := by push_cast; ring
          rw [e1, e2]
          exact ih (l + 1) hlt'
        · have hlK : l + 1 = K := by omega
          have hi : t0 ≤ t0 + (m : ℤ) := by
            have : (0 : ℤ) ≤ (m : ℤ) := Int.natCast_nonneg _
            linarith
          have hj : t0 ≤ t0 + (m : ℤ) + (q : ℤ) := by
            have h1 : (0 : ℤ) ≤ (m : ℤ) := Int.natCast_nonneg _
            have h2 : (0 : ℤ) ≤ (q : ℤ) := Int.natCast_nonneg _
            linarith
          have hfw := fwd (t0 + (m : ℤ)) (t0 + (m : ℤ) + (q : ℤ)) hi hj ih
          have hlKZ : (l : ℤ) + 1 = (K : ℤ) := by exact_mod_cast hlK
          have e1 : t0 + (((m : ℕ) + 1 : ℕ) : ℤ) + (l : ℕ)
              = t0 + (m : ℤ) + (K : ℤ) := by push_cast; linarith
          have e2 : t0 + (((m : ℕ) + 1 : ℕ) : ℤ) + (q : ℤ) + (l : ℕ)
              = t0 + (m : ℤ) + (q : ℤ) + (K : ℤ) := by push_cast; linarith
          rw [e1, e2]
          exact hfw
    refine ⟨q, hqpos, ?_⟩
    intro i hi
    have hn : (0 : ℤ) ≤ i - t0 := by linarith
    set n : ℕ := (i - t0).toNat with hndef
    have hnZ : (n : ℤ) = i - t0 := Int.toNat_of_nonneg hn
    have hupn := hup n 0 hK
    simp only [Nat.cast_zero, add_zero] at hupn
    have e1 : t0 + (n : ℤ) = i := by rw [hnZ]; ring
    have e2 : t0 + (n : ℤ) + (q : ℤ) = i + q := by rw [hnZ]; ring
    rw [e2, e1] at hupn
    exact hupn.symm
  obtain ⟨a, b, hab, hSab⟩ := Finite.exists_ne_map_eq_of_infinite S
  rcases lt_or_gt_of_ne hab with hlt | hlt
  · exact main a b hlt hSab
  · exact main b a hlt hSab.symm

/-- **Mirror image of `periodic_of_one_sided_determinacy`**, for the other half-plane: the
window is now read leftward (`y i, y (i-1), …, y (i-K+1)`), the domain is `i ≤ t0` instead of
`i ≥ t0`, `fwd` extends the window one step further left, and `bwd` extends it one step to the
right.  Obtained from `periodic_of_one_sided_determinacy` by the reflection `z n := y (-n)`,
which turns a rightward window based at `-i` into a leftward window based at `i`, and turns
`i ≥ t0` into `-i ≤ -t0`. -/
theorem periodic_of_one_sided_determinacy_neg {β : Type*} [Finite β] {K : ℕ} (hK : 0 < K)
    (y : ℤ → β) (t0 : ℤ)
    (fwd : ∀ i j : ℤ, i ≤ t0 → j ≤ t0 →
      (∀ l : ℕ, l < K → y (i - l) = y (j - l)) → y (i - K) = y (j - K))
    (bwd : ∀ i j : ℤ, i ≤ t0 - 1 → j ≤ t0 - 1 →
      (∀ l : ℕ, l < K → y (i - l) = y (j - l)) → y (i + 1) = y (j + 1)) :
    ∃ q : ℕ, 0 < q ∧ ∀ i : ℤ, i ≤ t0 → y (i - q) = y i := by
  have hz := periodic_of_one_sided_determinacy hK (fun n : ℤ => y (-n)) (-t0)
    (fun i j hi hj hwin => by
      have hi' : -i ≤ t0 := by linarith
      have hj' : -j ≤ t0 := by linarith
      have hwin' : ∀ l : ℕ, l < K → y (-i - l) = y (-j - l) := by
        intro l hl
        have h := hwin l hl
        have e1 : -(i + (l : ℤ)) = -i - l := by ring
        have e2 : -(j + (l : ℤ)) = -j - l := by ring
        rwa [e1, e2] at h
      have h := fwd (-i) (-j) hi' hj' hwin'
      have e1 : -i - (K : ℤ) = -(i + (K : ℤ)) := by ring
      have e2 : -j - (K : ℤ) = -(j + (K : ℤ)) := by ring
      rwa [e1, e2] at h)
    (fun i j hi hj hwin => by
      have hi' : -i ≤ t0 - 1 := by linarith
      have hj' : -j ≤ t0 - 1 := by linarith
      have hwin' : ∀ l : ℕ, l < K → y (-i - l) = y (-j - l) := by
        intro l hl
        have h := hwin l hl
        have e1 : -(i + (l : ℤ)) = -i - l := by ring
        have e2 : -(j + (l : ℤ)) = -j - l := by ring
        rwa [e1, e2] at h
      have h := bwd (-i) (-j) hi' hj' hwin'
      have e1 : -i + 1 = -(i - 1) := by ring
      have e2 : -j + 1 = -(j - 1) := by ring
      rwa [e1, e2] at h)
  obtain ⟨q, hqpos, hq⟩ := hz
  refine ⟨q, hqpos, fun i hi => ?_⟩
  have hi' : -t0 ≤ -i := by linarith
  have h := hq (-i) hi'
  have e1 : -((-i : ℤ) + (q : ℤ)) = i - q := by ring
  have e2 : -(-i : ℤ) = i := by ring
  rw [e1, e2] at h
  exact h

end Nivat
