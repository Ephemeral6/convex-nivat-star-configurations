/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.Section8.Normalisation

/-!
# §8.6. The convex Nivat conjecture

Formalisation of §8.6 of *The Convex Nivat Conjecture* (Pan): the end of the
paper.

Theorem 8.18 assembles the whole development.  Suppose the convex Nivat conjecture has a
counterexample.  Embed the alphabet into `ℤ_{>0}`, which changes neither the number of patterns
nor periodicity, and use Remark 8.3 to choose a counterexample `ξ` of minimal order.  Then:

* (0) Theorem 8.4 supplies the annihilator `Δ = ∏ᵢ (X^{hᵢ} − 1)`;
* (1) Theorem 8.6 supplies the line `ℓ`, and Theorem 8.7 a non-periodic `ξ' ∈ X` fully periodic
  on a lattice-convex region `R`;
* (2) Lemma 8.5 decomposes `ξ' mod p` over `𝔽_p`;
* (3) Corollary 8.10 gives the first half-planes `Uᵢ`;
* (4) Theorem 8.12 gives the second half-planes `Vᵢ` — at this point Theorem 8.1 holds;
* (5) reading the values in `𝔽_p` merges no colours, so `P_ζ(S) ≤ P_ξ(S) ≤ |S|`;
* (6) Lemma 8.17 turns `ζ` into a star configuration;
* (7) Theorem 7.3 gives `P_ζ(S) ≥ |S| + 1`, contradicting (8.1).

## Main results

* `Nivat.convex_nivat` — **Theorem 8.18 (Convex Nivat conjecture)**.
* `Nivat.nivat_conjecture` — **Corollary 8.19 (Nivat's conjecture)**.

## Status

Complete; no `sorry`.  Theorem 8.18 and Corollary 8.19 are fully assembled from §8.1–§8.5 and
Theorem 7.3.  Measured 2026-09-30: the whole development is `sorry`-free
(`bash scripts/sorries.sh` → `TOTAL: 0`) and `#print axioms Nivat.nivat_conjecture` reports
`[propext, Classical.choice, Quot.sound]`.  Re-run `scripts/sorries.sh` and
`scripts/check_axioms.sh` for the current reading; do not read it off this paragraph.
-/

namespace Nivat

open Finset

/-- An injective encoding of a finite alphabet into `ℤ_{>0}` changes neither the number of
patterns nor periodicity.  Paper §8.6, first line of the proof of Theorem 8.18. -/
theorem exists_intEncoding {α : Type*} [Finite α] (ξ : Config α) :
    ∃ ζ : Config ℤ, (Set.range ζ).Finite ∧ (∀ z, 0 < ζ z) ∧
      (∀ S : Finset (ℤ × ℤ), P ζ S = P ξ S) ∧ (IsPeriodic ζ ↔ IsPeriodic ξ) := by
  classical
  have _ := Fintype.ofFinite α
  set e : α → ℤ := fun a => ((Fintype.equivFin α a : ℕ) : ℤ) + 1 with he
  have hepos : ∀ a, 0 < e a := by
    intro a
    have h0 : (0 : ℤ) ≤ ((Fintype.equivFin α a : ℕ) : ℤ) := Int.natCast_nonneg _
    show (0 : ℤ) < ((Fintype.equivFin α a : ℕ) : ℤ) + 1
    omega
  have hinj : Function.Injective e := by
    intro a b hab
    rw [he] at hab
    simp only [add_left_inj, Nat.cast_inj] at hab
    exact (Fintype.equivFin α).injective (Fin.val_injective hab)
  -- The encoding is injective, so it preserves the period subgroup on the nose.
  have hPer : Per (fun z => e (ξ z)) = Per ξ := by
    ext u
    simp only [mem_Per_iff]
    constructor
    · intro hu
      funext z
      have hz : e (ξ (z + u)) = e (ξ z) := congrFun hu z
      show ξ (z + u) = ξ z
      exact hinj hz
    · intro hu
      funext z
      have hz : ξ (z + u) = ξ z := congrFun hu z
      show e (ξ (z + u)) = e (ξ z)
      rw [hz]
  refine ⟨fun z => e (ξ z), ?_, fun z => hepos _, ?_, ?_⟩
  · exact (Set.finite_range e).subset (by rintro _ ⟨z, rfl⟩; exact ⟨ξ z, rfl⟩)
  · -- Post-composition with an injection is a bijection between the two pattern sets.
    intro S
    have himg : patterns (fun z => e (ξ z)) S
        = (fun g : S → α => fun q => e (g q)) '' patterns ξ S := by
      ext x
      constructor
      · rintro ⟨u, rfl⟩
        exact ⟨pattern ξ S u, ⟨u, rfl⟩, rfl⟩
      · rintro ⟨g, ⟨u, rfl⟩, rfl⟩
        exact ⟨u, rfl⟩
    have hinjOn : Set.InjOn (fun g : S → α => fun q => e (g q)) (patterns ξ S) := by
      intro g₁ _ g₂ _ heq
      funext q
      exact hinj (congrFun heq q)
    rw [P, P, himg, hinjOn.ncard_image]
  · constructor
    · rintro ⟨u, hu, hu0⟩
      exact ⟨u, hPer ▸ hu, hu0⟩
    · rintro ⟨u, hu, hu0⟩
      exact ⟨u, hPer ▸ hu, hu0⟩

/-- A finite alphabet `A ⊆ ℤ` admits a prime `p > max A`.  Paper §8.6, step (2). -/
theorem exists_prime_gt {ξ : Config ℤ} (hfin : (Set.range ξ).Finite) :
    ∃ p : ℕ, p.Prime ∧ ∀ z, ξ z < p := by
  obtain ⟨B, hB⟩ := hfin.bddAbove
  obtain ⟨p, hpge, hp⟩ := Nat.exists_infinite_primes (B.toNat + 1)
  refine ⟨p, hp, fun z => ?_⟩
  have h1 : ξ z ≤ B := hB (Set.mem_range_self z)
  have h2 : B ≤ (B.toNat : ℤ) := Int.self_le_toNat B
  have h3 : ((B.toNat + 1 : ℕ) : ℤ) ≤ (p : ℤ) := by exact_mod_cast hpge
  push_cast at h3
  omega

/-- **Theorem 8.18 (Convex Nivat conjecture).**  Let `ξ : ℤ² → A` with `A` finite, and suppose
there is a non-empty finite lattice-convex `S` with `P_ξ(S) ≤ |S|`.  Then `ξ` is periodic. -/
theorem convex_nivat {α : Type*} [Finite α] {ξ : Config α} {S : Finset (ℤ × ℤ)}
    (hne : S.Nonempty) (hS : LatticeConvex S) (hP : P ξ S ≤ S.card) : IsPeriodic ξ := by
  by_contra hnp
  -- Embed the alphabet into `ℤ_{>0}`.
  obtain ⟨ζ, hfin, hpos, hPeq, hperiff⟩ := exists_intEncoding ξ
  have hcex : IsCounterexample ζ :=
    ⟨hfin, hpos, fun h => hnp (hperiff.mp h), S, hne, hS, (hPeq S).symm ▸ hP⟩
  -- Remark 8.3: choose a counterexample of minimal order.
  obtain ⟨ξ₀, hξ₀⟩ := exists_minimalCounterexample ⟨ζ, hcex⟩
  -- Step (2): a prime `p > max A`.
  obtain ⟨p, hp, hlt⟩ := exists_prime_gt hξ₀.1.1
  have : Fact p.Prime := ⟨hp⟩
  -- Steps (1)–(5): Theorem 8.1 together with the complexity bound (8.1).
  obtain ⟨zeta, m, hznp, -, hadm, W, hWne, hWconv, hWP⟩ := structure_input hξ₀ hlt
  -- Step (6): Lemma 8.17.
  obtain ⟨m', Sc, hSc⟩ := exists_starConfig_of_admissible hznp hadm
  -- Step (7): Theorem 7.3 = Theorem A.
  have hA : W.card + 1 ≤ P Sc.θ W := star_complexity_lower_bound Sc hWne hWconv
  rw [hSc] at hA
  omega

/-- The rectangular window `[1, n] × [1, k]`.  Paper Corollary 8.19. -/
noncomputable def rectangle (n k : ℕ) : Finset (ℤ × ℤ) :=
  Finset.Icc 1 (n : ℤ) ×ˢ Finset.Icc 1 (k : ℤ)

@[simp] theorem card_rectangle (n k : ℕ) : (rectangle n k).card = n * k := by
  simp [rectangle, Finset.card_product, Int.card_Icc]

theorem rectangle_nonempty {n k : ℕ} (hn : 0 < n) (hk : 0 < k) : (rectangle n k).Nonempty := by
  refine ⟨(1, 1), ?_⟩
  simp only [rectangle, Finset.mem_product, Finset.mem_Icc]
  omega

/-- A real convex combination of two numbers in `[lo, hi]` stays in `[lo, hi]`. -/
private theorem mem_Icc_convex {lo hi u v a b : ℝ} (h1 : lo ≤ u) (h2 : u ≤ hi) (h3 : lo ≤ v)
    (h4 : v ≤ hi) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    lo ≤ a * u + b * v ∧ a * u + b * v ≤ hi := by
  have e1 : a * lo ≤ a * u := mul_le_mul_of_nonneg_left h1 ha
  have e2 : b * lo ≤ b * v := mul_le_mul_of_nonneg_left h3 hb
  have e3 : a * u ≤ a * hi := mul_le_mul_of_nonneg_left h2 ha
  have e4 : b * v ≤ b * hi := mul_le_mul_of_nonneg_left h4 hb
  have elo : a * lo + b * lo = lo := by rw [← add_mul, hab, one_mul]
  have ehi : a * hi + b * hi = hi := by rw [← add_mul, hab, one_mul]
  constructor <;> linarith

/-- A rectangle is lattice-convex.  Paper Corollary 8.19.

`Conv(rectangle n k)` is contained in the real box `[1, n] × [1, k]`, because that box is convex
and contains the generating lattice points; a lattice point of the box is a lattice point of the
rectangle since the bounds are integers. -/
theorem latticeConvex_rectangle (n k : ℕ) : LatticeConvex (rectangle n k) := by
  have hfst : ∀ w : ℤ × ℤ, (toReal w).1 = (w.1 : ℝ) := fun _ => rfl
  have hsnd : ∀ w : ℤ × ℤ, (toReal w).2 = (w.2 : ℝ) := fun _ => rfl
  intro z hz
  have hconv : Convex ℝ {x : ℝ × ℝ | 1 ≤ x.1 ∧ x.1 ≤ (n : ℝ) ∧ 1 ≤ x.2 ∧ x.2 ≤ (k : ℝ)} := by
    rintro x ⟨hx1, hx2, hx3, hx4⟩ y ⟨hy1, hy2, hy3, hy4⟩ a b ha hb hab
    obtain ⟨p1, p2⟩ := mem_Icc_convex hx1 hx2 hy1 hy2 ha hb hab
    obtain ⟨q1, q2⟩ := mem_Icc_convex hx3 hx4 hy3 hy4 ha hb hab
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    exacts [p1, p2, q1, q2]
  have hsub : Conv (rectangle n k) ⊆ {x : ℝ × ℝ | 1 ≤ x.1 ∧ x.1 ≤ (n : ℝ) ∧ 1 ≤ x.2 ∧
      x.2 ≤ (k : ℝ)} := by
    refine convexHull_min ?_ hconv
    rintro _ ⟨w, hw, rfl⟩
    simp only [rectangle, Finset.mem_coe, Finset.mem_product, Finset.mem_Icc] at hw
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hw
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hfst]; exact_mod_cast h1
    · rw [hfst]; exact_mod_cast h2
    · rw [hsnd]; exact_mod_cast h3
    · rw [hsnd]; exact_mod_cast h4
  obtain ⟨h1, h2, h3, h4⟩ := hsub hz
  rw [hfst] at h1 h2
  rw [hsnd] at h3 h4
  simp only [rectangle, Finset.mem_product, Finset.mem_Icc]
  exact ⟨⟨by exact_mod_cast h1, by exact_mod_cast h2⟩, by exact_mod_cast h3, by exact_mod_cast h4⟩

/-- **Corollary 8.19 (Nivat's conjecture).**  If `P_ξ([1, n] × [1, k]) ≤ nk` for some
`n, k ≥ 1`, then `ξ` is periodic. -/
theorem nivat_conjecture {α : Type*} [Finite α] {ξ : Config α} {n k : ℕ} (hn : 0 < n)
    (hk : 0 < k) (hP : P ξ (rectangle n k) ≤ n * k) : IsPeriodic ξ :=
  convex_nivat (rectangle_nonempty hn hk) (latticeConvex_rectangle n k)
    (by rwa [card_rectangle])

end Nivat
