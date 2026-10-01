import Nivat.External.Colle.L1Region

/-!
# Tower index theorems — Collé b3_colle2.txt:806-820

**原文：b3_colle2.txt:806-820** — the finite outer tower `𝓡_i := {g + t·v⃗_{ℓ_i} : g ∈ 𝓡_{i+1}, t ∈ ℤ₊}`
for `ι−m+1 ≤ i ≤ ι−2`, giving the chain `𝓡_{ι−1} ⊂ 𝓡_{ι−2} ⊂ ⋯ ⊂ 𝓡_{ι−m+1}` (`:812`),
with the **smallest** index `I` such that `(T^u η)|𝓡_I` is still periodic of period `h` (`:814`).

## Index convention

Collé's indices **decrease** as sets grow: `𝓡_{ι−1} ⊂ 𝓡_{ι−2}` means `ι−1` labels the smallest set
(the tower base, periodic) and `ι−m` labels the largest (the tower top, not periodic).

We reverse the encoding: `R 0` is the base (smallest, periodic), `R n` grows with `n`, and
`R M` is the top (largest, not periodic).  Under this encoding, "the smallest `I` such that
`𝓡_I` is periodic" becomes "the **largest** `I` such that `R I` is periodic", or equivalently
"the last `I < M` such that `R I` is periodic but `R (I+1)` is not".

-/

namespace Nivat.TowerIndex

open Nivat.Colle41 (PeriodOn)

/-- **Existence of the last periodic index in a finite tower** (`b3_colle2.txt:812-814`).

原文：b3_colle2.txt:812-814 — "Hence, as `𝓡_{ι−1} ⊂ 𝓡_{ι−2} ⊂ ⋯ ⊂ 𝓡_{ι−m+1}`, we may
consider the smallest integer `ι−m+1 ≤ I ≤ ι−1` such that `(T^u η)|_{𝓡_I}` is periodic of
period `h`."

In our reversed indexing (`R 0` = base, `R M` = top), this becomes: given a tower where the
base `R 0` is periodic and the top `R M` is not, there exists a **last** index `I < M` where
`R I` is periodic but `R (I + 1)` is not.

量词对应：
- 原文 "the smallest integer" → 我们的 `I : ℕ`（存在量词，由 `Nat.find` 给出）
- 原文 `ι−m+1 ≤ I ≤ ι−1` → 我们的 `I < M`（指标落在塔内部）
- 原文 "`(T^u η)|_{𝓡_I}` is periodic of period `h`" → 我们的 `PeriodOn x (R I) h`
- 原文的「最小」= 我们编码下的「最大 = 最后一个」，体现为 `¬ PeriodOn x (R (I+1)) h`

**本定理不需要 `Monotone R`**：`Nat.find` 的最小性已经给出 `I` 是最后一个满足周期性的指标，
不依赖于 `R` 是否单调。(Compare `L1Region.lean:102` `exists_greatest_periodOn`, which
*does* use `Monotone` because it works with the union `⋃ n, Rf n`; here we only need the
pointwise data `h0` and `hM`.) -/
theorem exists_last_periodOn_finite {A : Type*} {x : Nivat.Config A} {h : ℤ × ℤ}
    {R : ℕ → Set (ℤ × ℤ)} {M : ℕ}
    (h0 : PeriodOn x (R 0) h)
    (hM : ¬ PeriodOn x (R M) h) :
    ∃ I : ℕ, I < M ∧ PeriodOn x (R I) h ∧ ¬ PeriodOn x (R (I + 1)) h := by
  classical
  -- The set of non-periodic indices is nonempty (witnessed by M)
  have hex : ∃ n, ¬ PeriodOn x (R n) h := by exact ⟨M, hM⟩
  -- Its least element is positive (since 0 is periodic)
  have hpos : 0 < Nat.find hex := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with hz | hp
    · exact absurd h0 (by rw [← hz]; exact Nat.find_spec hex)
    · exact hp
  -- Take I := Nat.find hex - 1
  refine ⟨Nat.find hex - 1, ?_, ?_, ?_⟩
  · -- I < M
    calc Nat.find hex - 1 < Nat.find hex := by omega
      _ ≤ M := Nat.find_le hM
  · -- PeriodOn x (R I) h
    exact not_not.mp (Nat.find_min hex (m := Nat.find hex - 1) (by omega))
  · -- ¬ PeriodOn x (R (I + 1)) h
    have he : Nat.find hex - 1 + 1 = Nat.find hex := by omega
    rw [he]
    exact Nat.find_spec hex

/-- **Periodicity is inherited downwards along a monotone tower.**

If `R j ⊆ R I` and `R I` is periodic, then `R j` is periodic.  This is just `PeriodOn.mono`
(`Lemma41.lean:662`) composed with the monotonicity hypothesis. -/
theorem periodOn_of_le_last {A : Type*} {x : Nivat.Config A} {h : ℤ × ℤ}
    {R : ℕ → Set (ℤ × ℤ)} {I : ℕ} (hmono : Monotone R)
    (hI : PeriodOn x (R I) h) {j : ℕ} (hj : j ≤ I) :
    PeriodOn x (R j) h :=
  Nivat.Colle41.PeriodOn.mono (hmono hj) hI

end Nivat.TowerIndex

#print axioms Nivat.TowerIndex.exists_last_periodOn_finite
#print axioms Nivat.TowerIndex.periodOn_of_le_last
