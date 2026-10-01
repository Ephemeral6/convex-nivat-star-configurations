/-
Lane: Wfit（2026-09-21 由集成者落地为 `Nivat/External/Colle/WindowPlace.lean`；消费者 `RegionSteps.exists_cutResidualR_of_claim46` 同轮加 import）
Placement lemma for Claim 4.7 (b3_colle2.txt:822-824).

原文：b3_colle2.txt:822-824 — the translate `𝒯` minus its edge sits inside `𝓡^N_I`.
-/
import Nivat.External.Colle.L1Region

namespace Nivat.L1Claim

open Nivat.LE2 (dot)

variable {Rinf : Set (ℤ × ℤ)} {m u' : ℤ × ℤ} {lev : ℕ → ℤ}

/-- **Claim 4.7 placement (`:822-824`): translate exists at any level.**

Given:
- `Q` finite and all in level `≥ lev N`
- `m ⟂ u'` (cutting line runs along `u'`)
- `htail`: each level `≥ lev N` contains a `u'`-tail in `Rinf`

then there exists `τ` such that `∀ z ∈ Q, τ•u' + z ∈ cut Rinf m lev N`.

**Why this works (per CLAUDE.md hard rule 10)**: `cut Rinf m lev N = Rinf ∩ halfPlaneGE m (lev N)`
(`L1Region.lean:197`). Because `dot m u' = 0`, translating by `u'` does not change the level,
so the half-plane condition depends only on `z`. The real content is `τ•u' + z ∈ Rinf`, which
is guaranteed by `htail` for sufficiently large `τ`. Taking the maximum over the finite set `Q`
gives the required `τ`. -/
theorem exists_tau_mem_cut
    {N : ℕ} {Q : Set (ℤ × ℤ)}
    (hQfin : Q.Finite)
    (hmu' : dot m u' = 0)
    (hQlev : ∀ z ∈ Q, lev N ≤ dot m z)
    (htail : ∀ z : ℤ × ℤ, lev N ≤ dot m z →
      ∃ T : ℤ, ∀ t : ℤ, T ≤ t → t • u' + z ∈ Rinf) :
    ∃ τ : ℤ, ∀ z ∈ Q, τ • u' + z ∈ Nivat.L1Region.cut Rinf m lev N := by
  classical
  by_cases hQne : Q.Nonempty
  · -- Get threshold for each element
    have hT : ∀ z ∈ Q, ∃ T : ℤ, ∀ t ≥ T, t • u' + z ∈ Rinf :=
      fun z hz => htail z (hQlev z hz)
    choose T hT' using hT
    -- Get finset
    obtain ⟨Qfin, rfl⟩ := hQfin.exists_finset_coe
    have hQfin_ne : Qfin.Nonempty := hQne
    -- Build finset of thresholds
    let Tvals : Finset ℤ := Qfin.attach.image (fun z => T z.val (Finset.mem_coe.mp z.property))
    have hTne : Tvals.Nonempty := by
      obtain ⟨z, hz⟩ := hQfin_ne
      use T z (Finset.mem_coe.mp hz)
      simp only [Tvals, Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists]
      use z, hz
    let τ := Tvals.max' hTne
    use τ
    intro z hz
    constructor
    · -- τ•u' + z ∈ Rinf
      have hTz_mem : T z hz ∈ Tvals := by
        simp only [Tvals, Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists]
        use z, hz
      have hTz_le : T z hz ≤ τ := Finset.le_max' Tvals (T z hz) hTz_mem
      exact hT' z hz τ hTz_le
    · -- lev N ≤ dot m (τ•u' + z)
      simp only [Nivat.L1Region.cut, Set.mem_inter_iff, Nivat.LE2.halfPlaneGE, Set.mem_setOf]
      have hmz : lev N ≤ dot m z := hQlev z hz
      have heq : dot m z = dot m (τ • u' + z) := by
        simp only [dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Prod.fst_add, Prod.snd_add]
        have h0 : m.1 * u'.1 + m.2 * u'.2 = 0 := by
          convert hmu' using 1
          simp [dot]
        calc m.1 * z.1 + m.2 * z.2
            = m.1 * (τ * u'.1 + z.1) + m.2 * (τ * u'.2 + z.2) - τ * (m.1 * u'.1 + m.2 * u'.2) := by ring
          _ = m.1 * (τ * u'.1 + z.1) + m.2 * (τ * u'.2 + z.2) - τ * 0 := by rw [h0]
          _ = m.1 * (τ * u'.1 + z.1) + m.2 * (τ * u'.2 + z.2) := by ring
      rw [← heq]
      exact hmz
  · -- Q empty
    simp only [Set.not_nonempty_iff_eq_empty] at hQne
    use 0
    intro z hz
    simp [hQne] at hz



/-- **Claim 4.7 placement, pair version**: both `τ•u' + z` and `τ•u' + z + c•vl` fit.

This is the shape needed for `CutResidualR.hline` (`:1055-1060`). The consumer
(`L1Claim.lean:1055-1060`) always uses `c • vl` where `c` comes from the period
(`c • vl` is the period vector in `:806`), and by `L1Claim.lean:1020` +
`RegionSteps.lean:1569` we have `hc : 0 < c`, so the constraint `0 ≤ c` is satisfied. -/
theorem exists_tau_mem_cut_pair
    {N : ℕ} {Q : Set (ℤ × ℤ)} {c : ℤ} {vl : ℤ × ℤ}
    (hQfin : Q.Finite)
    (hmu' : dot m u' = 0)
    (hmvl : 0 < dot m vl)
    (hc : 0 ≤ c)
    (hQlev : ∀ z ∈ Q, lev N ≤ dot m z)
    (htail : ∀ z : ℤ × ℤ, lev N ≤ dot m z →
      ∃ T : ℤ, ∀ t : ℤ, T ≤ t → t • u' + z ∈ Rinf) :
    ∃ τ : ℤ, ∀ z ∈ Q,
      τ • u' + z ∈ Nivat.L1Region.cut Rinf m lev N ∧
      τ • u' + z + c • vl ∈ Nivat.L1Region.cut Rinf m lev N := by
  -- Apply exists_tau_mem_cut to Q ∪ (· + c•vl) '' Q
  -- Now that we have `hc : 0 ≤ c`, the level constraint is satisfied for both sets.
  let Q' := Q ∪ (· + c • vl) '' Q
  have hQ'fin : Q'.Finite := Set.Finite.union hQfin (Set.Finite.image _ hQfin)
  have hQ'lev : ∀ z ∈ Q', lev N ≤ dot m z := by
    intro z hz
    cases hz with
    | inl hz => exact hQlev z hz
    | inr hz =>
      obtain ⟨w, hw, rfl⟩ := hz
      simp only [dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Prod.fst_add, Prod.snd_add]
      have hw' : lev N ≤ m.1 * w.1 + m.2 * w.2 := hQlev w hw
      -- Since c ≥ 0 and dot m vl > 0, adding c•vl increases the level
      calc lev N
          ≤ m.1 * w.1 + m.2 * w.2 := hw'
        _ ≤ m.1 * w.1 + m.2 * w.2 + c * (m.1 * vl.1 + m.2 * vl.2) := by
            have : 0 ≤ c * (m.1 * vl.1 + m.2 * vl.2) := Int.mul_nonneg hc (Int.le_of_lt hmvl)
            omega
        _ = m.1 * (w.1 + c * vl.1) + m.2 * (w.2 + c * vl.2) := by ring
  obtain ⟨τ, hτ⟩ := exists_tau_mem_cut hQ'fin hmu' hQ'lev htail
  use τ
  intro z hz
  constructor
  · exact hτ z (Set.mem_union_left _ hz)
  · have hmem : z + c • vl ∈ Q' := Set.mem_union_right _ ⟨z, hz, rfl⟩
    have := hτ (z + c • vl) hmem
    convert this using 1
    ring



end Nivat.L1Claim

#print axioms Nivat.L1Claim.exists_tau_mem_cut
#print axioms Nivat.L1Claim.exists_tau_mem_cut_pair
