/-
Copyright (c) 2026 Nivat conjecture contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rowind
-/
import Nivat.External.Colle.TowerBuild

/-!
# Tower climb: `:806-820`

This file implements the tower construction from `b3_colle2.txt:806-820`:
`𝓡_{ι-1} ⊂ 𝓡_{ι-2} ⊂ ... ⊂ 𝓡_{ι-m+1}`, taking the smallest `I` such that
`(T^u η)|_{𝓡_I}` is still periodic.

## Main declarations

* `periodOn_tower` — induction applying `periodOn_coneRegion_of_lines` level by level

原文：b3_colle2.txt:806-820

## Implementation notes

The tower is `periodOn_coneRegion_of_lines` iterated with the base replaced at each level.
We do NOT implement Claim 4.7's maximality (`:820-852`) here — `exists_greatest_periodOn_cut`
already exists for that (`Stage2Index.lean`, per `RegionSteps.lean:1540-1544`).

-/

namespace Nivat.ColleReg

variable {ξ : Config ℤ} {S : Finset (ℤ × ℤ)} {vl : ℤ × ℤ}

/-! ## §1  ℤ·vl-invariance after tower iteration

原文：b3_colle2.txt:808 — each `𝓡_i := {g + t·v⃗_{ℓ_i} : g ∈ 𝓡_{i+1}, t ∈ ℤ₊}`.
Walking the cyclic order of edge directions means `-vl` eventually sits in the ℕ-cone
of two tower directions `w₁, w₂`, so `fullSweep R vl ⊆ coneRegion (coneRegion R vl w₁) vl w₂`.

**Why this works (per CLAUDE.md hard rule 10):** The paper walks edge directions cyclically
(`:808`) so that after enough steps, the *negative* direction `-vl` can be expressed as
`a•w₁ + b•w₂` with `a, b : ℕ`. Positive multiples of `vl` are already in `coneRegion R vl w₁`
(from the `ℕ·vl` component), and negative multiples become reachable via the ℕ-cone of `w₁, w₂`.
This is the paper's mechanism for achieving ℤ·vl-invariance without changing the ℕ-sweep
construction at each level.
-/

/-- **After enough tower steps, `fullSweep R vl ⊆ coneRegion ...`.**

原文：b3_colle2.txt:808 — the tower construction `𝓡_{i} := 𝓡_{i+1} + ℕ·v⃗_{ℓ_i}`.

If `-vl = a•w₁ + b•w₂` with `a, b : ℕ`, then negative multiples of `vl` are reachable
via the ℕ-cone of `w₁` and `w₂`, and positive multiples are free from the `ℕ·vl` in
`coneRegion R vl w₁`. This is the paper's reason for walking edge directions cyclically
(per CLAUDE.md hard rule 10: we align on *why* `:808` uses cyclic order, not just *what*
the tower construction is). -/
theorem fullSweep_subset_coneRegion_iterate
    {R : Set (ℤ × ℤ)} {vl w₁ w₂ : ℤ × ℤ} {a b : ℕ}
    (hneg : -vl = (a : ℤ) • w₁ + (b : ℤ) • w₂) :
    Nivat.ColleReg.fullSweep R vl
      ⊆ Nivat.ConeRegion.coneRegion (Nivat.ConeRegion.coneRegion R vl w₁) vl w₂ := by
  intro z hz
  rw [Nivat.ColleReg.mem_fullSweep_iff] at hz
  obtain ⟨r, hr, t, rfl⟩ := hz
  rw [Nivat.ConeRegion.mem_coneRegion_iff]
  by_cases ht : 0 ≤ t
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, t = (n : ℤ) := ⟨t.toNat, by omega⟩
    refine ⟨r, ?_, n, 0, by push_cast; module⟩
    rw [Nivat.ConeRegion.mem_coneRegion_iff]
    exact ⟨r, hr, 0, 0, by module⟩
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, t = -(n : ℤ) := ⟨(-t).toNat, by omega⟩
    refine ⟨r + ((n * a : ℕ) : ℤ) • w₁, ?_, 0, n * b, ?_⟩
    · rw [Nivat.ConeRegion.mem_coneRegion_iff]
      exact ⟨r, hr, 0, n * a, by module⟩
    · -- goal: r + (-↑n) • vl = r + ↑(n*a) • w₁ + ↑0 • vl + ↑(n*b) • w₂
      have h : (-(n : ℤ)) • vl = (n : ℤ) • (-vl) := by module
      rw [h, hneg]
      push_cast
      module

/-! ## §2  Tower induction

原文：b3_colle2.txt:806-812

Applies `periodOn_coneRegion_of_lines` level by level. The per-level window conditions
are taken as explicit indexed hypotheses (per team-lead: "discharging them is a separate round"). -/

/-- **Tower induction: periodicity climbs level by level.**

原文：b3_colle2.txt:806-812

Each `R (n+1) = coneRegion (R n) vl (w n)` with `R 0` the stage-1 region.
Conclusion: `∀ n, PeriodOn (T e ξ) (R n) (c • vl)`.

Per-level hypotheses `hstepIn`, `hD`, `hwinL` are explicit — discharging them is
a separate task. -/
theorem periodOn_tower
    {ξ : Config ℤ} {e : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} {a : ℤ × ℤ} (hS : Nivat.Colle.GeneratesAt ξ S a)
    (ha : a ∈ S) (hconv : Nivat.LatticeConvex (S.erase a))
    {vl nℓ : ℤ × ℤ} {c cz : ℤ}
    (hperp : Nivat.LE2.dot nℓ vl = 0)
    (R : ℕ → Set (ℤ × ℤ)) (w : ℕ → ℤ × ℤ)
    (hR : ∀ n, R (n + 1) = Nivat.ConeRegion.coneRegion (R n) vl (w n))
    (hstep : ∀ n, Nivat.LE2.dot nℓ (w n) = -1)
    (hBlow : ∀ n, ∀ b ∈ R n, cz ≤ Nivat.LE2.dot nℓ b)
    (hstepIn : ∀ n, ∀ z ∈ Nivat.LE2.halfStrip (R n) vl,
      cz ≤ Nivat.LE2.dot nℓ (z + w n) → z + w n ∈ Nivat.LE2.halfStrip (R n) vl)
    (hD : ∀ n, ∀ z ∈ Nivat.LE2.halfStrip (R n) vl,
      Nivat.T e ξ z = Nivat.T (c • vl) (Nivat.T e ξ) z)
    (hwinL : ∀ n, ∀ i : ℕ,
      ∀ p ∈ Nivat.ConeRegion.coneRegion (R n) vl (w n) ∩
        {y | Nivat.LE2.dot nℓ y = cz - 1 - (i : ℤ)},
      ∀ z ∈ S.erase a,
        z + (p - a) ∈ Nivat.LE2.halfStrip (R n) vl ∪
          (⋃ i' ∈ {i' | i' < i}, Nivat.ConeRegion.coneRegion (R n) vl (w n) ∩
            {y | Nivat.LE2.dot nℓ y = cz - 1 - (i' : ℤ)}))
    (hbase : Nivat.Colle41.PeriodOn (Nivat.T e ξ) (R 0) (c • vl)) :
    ∀ n : ℕ, Nivat.Colle41.PeriodOn (Nivat.T e ξ) (R n) (c • vl) := by
  intro n
  induction n with
  | zero => exact hbase
  | succ n ih =>
    rw [hR]
    refine Nivat.ColleReg.periodOn_coneRegion_of_lines
      hS ha hconv hperp (hstep n) ?_ (hstepIn n) (hD n) (hwinL n)
    intro b hb
    exact hBlow n b hb

/-- **🔴 `fullSweep_subset_coneRegion_iterate` 的 `hneg` 在塔的语境里不可满足。**

原文：b3_colle2.txt:806-812。

上面那条引理本身**是真的**，且不带 `nℓ`——它只说「若 `-vl` 落在 `w₁, w₂` 的 ℕ-锥里，
则双向扫掠含于两步锥」。**假的是把它接到塔上的那一步**：塔的每一步方向都满足
`dot nℓ (w i) = -1`（`periodOn_coneRegion_of_lines` 的 `hstep`，本文件
`periodOn_tower` 的 `hstep` 原样转发），而 `dot nℓ vl = 0`。对 `hneg` 两边取 `dot nℓ`：

```
0 = dot nℓ (-vl) = (a : ℤ) * (-1) + (b : ℤ) * (-1) = -(a + b)
```

`a b : ℕ` 于是 `a = b = 0`，`hneg` 退化成 `-vl = 0`。所以任何以
`Primitive vl` 为前提的消费者处，`hneg` 与 `hperp`/`hstep` 三条**联合不可满足**，
由它们导出的结论**空真**。

**为什么这不是「换个 `w` 就好」**：`nℓ`-层是严格下降的（每步 `-1`），ℕ-组合只能继续下降，
永远回不到层 0。这与选哪两条边无关，是层函数的单调性。

**原文没有这个动作。** `:808` 的塔是 `𝓡_i := {g + t·v⃗_{ℓ_i} : g ∈ 𝓡_{i+1}, t ∈ ℤ₊}`，
**每一步都是单侧 `ℤ₊`**，底座 `𝓡_{ι−1}` 坐在 `H_B(ℓ)`（`:414`，**正向**半带）上。
Collé 从头到尾没有构造双向扫掠；`fullSweep`（`L1RegionBuild.lean:164`，`ℤ·vl`）是**我们**的
编码，`hneg` 是为了迁就它而发明的前提（硬规矩 7：没有对应物的量词 = 我们发明的）。

**活着的接缝是 `Stage2Index.exists_stage2_data_of_layers`**（`Stage2Index.lean:403`），
它按 `:795-802` 的**逐行**形状取输入，不经过塔。

**Consumer**: 无（反例档案，天生无消费者）。存在的理由是挡住重建这条路线。 -/
theorem hneg_forces_vl_zero
    {nℓ vl w₁ w₂ : ℤ × ℤ} {a b : ℕ}
    (hperp : Nivat.LE2.dot nℓ vl = 0)
    (hstep₁ : Nivat.LE2.dot nℓ w₁ = -1)
    (hstep₂ : Nivat.LE2.dot nℓ w₂ = -1)
    (hneg : -vl = (a : ℤ) • w₁ + (b : ℤ) • w₂) :
    vl = 0 ∧ a = 0 ∧ b = 0 := by
  have key : ∀ (n w : ℤ × ℤ) (k : ℤ),
      Nivat.LE2.dot n (k • w) = k * Nivat.LE2.dot n w := by
    rintro ⟨n1, n2⟩ ⟨w1, w2⟩ k
    simp only [Nivat.LE2.dot, Prod.smul_mk, smul_eq_mul]
    ring
  have hdot : Nivat.LE2.dot nℓ (-vl)
      = Nivat.LE2.dot nℓ ((a : ℤ) • w₁ + (b : ℤ) • w₂) := by rw [hneg]
  rw [Nivat.LE2.dot_add, key, key, hstep₁, hstep₂] at hdot
  have hneg0 : Nivat.LE2.dot nℓ (-vl) = 0 := by
    have hn : Nivat.LE2.dot nℓ (-vl) = -Nivat.LE2.dot nℓ vl := by
      obtain ⟨n1, n2⟩ := nℓ; obtain ⟨v1, v2⟩ := vl
      simp only [Nivat.LE2.dot, Prod.neg_mk]; ring
    rw [hn, hperp]; ring
  rw [hneg0] at hdot
  have ha0 : a = 0 := by omega
  have hb0 : b = 0 := by omega
  subst ha0; subst hb0
  refine ⟨?_, rfl, rfl⟩
  simp only [Nat.cast_zero, zero_smul, add_zero] at hneg
  exact neg_eq_zero.mp hneg

#print axioms fullSweep_subset_coneRegion_iterate
#print axioms periodOn_tower
#print axioms hneg_forces_vl_zero


end Nivat.ColleReg
