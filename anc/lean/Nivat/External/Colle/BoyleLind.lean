/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.Section8.External
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Algebra.Order.Field

/-!
# The Boyle–Lind corollary used by Colle §3.1

Colle (*Nivat's conjecture for some classes of configurations*, arXiv:1909.08195) uses three
times the following statement, attributed there and in Kari–Moutot (Prop. 19) to a "well-known
corollary of a theorem of Boyle and Lind":

> if the orbit closure of `x` is deterministic in every direction — equivalently, `x` has no
> one-sided nonexpansive direction — then `x` is doubly periodic.

This file proves that statement **for configurations of finite range**
(`Nivat.BL.doublyPeriodic_of_forall_notMem_ONED`), and shows that the finiteness hypothesis
cannot be dropped (`Nivat.BL.boyleLindStatement_false`): the unqualified proposition

```
∀ x : Config ℤ, (∀ w : ℝ × ℝ, w ≠ 0 → w ∉ ONED x) → DoublyPeriodic x
```

is refuted by `x (m, n) = m`.

## Extra hypothesis

`(Set.range x).Finite` is genuinely needed (see `slope` below) and is available downstream:
Colle §3.1 works over a finite alphabet, and `Nivat.Section8.External.colle_doublyPeriodic`
already carries `(hA : (Set.range ξ).Finite)`.  Moreover finiteness is inherited by the orbit
closure (`Nivat.BL.finite_range_of_mem_orbitClosure`), which is what §3.1 needs when it applies
the corollary to a configuration produced inside `orbitClosure ξ`.

## Route

The published Boyle–Lind text was not available, and Kari–Moutot state their Proposition 19
without proof, so the argument below is self-contained and elementary; it is *not* a
transcription of Boyle–Lind's proof.  Outline, with `X = orbitClosure x`:

* `eq_of_agree_openSide` — the hypothesis is stated with *closed* half-planes `sideOf w`
  (`⟪w, z⟫ ≤ 0`) and *real* directions; translating by a lattice vector strictly inside the
  half-plane upgrades it to determinism across *open* half-planes.
* `exists_win_injOn` — the key compactness step.  If no finite box `win M` separated the points
  of `X`, pick for each `M` a pair `y M ≠ y' M` agreeing on `win M`, and a point `p M` of
  *minimal Euclidean norm* where they differ; `p M ∉ win M`, so `‖p M‖₁ > M → ∞`.  Recentre at
  `p M` and take an ultrafilter limit: the values live in the finite set `Set.range x`, so the
  limits `z ≠ z'` exist and lie in `X`; the directions `p M / ‖p M‖₁` converge to some `ν ≠ 0`;
  and minimality of `p M` forces `z = z'` on the open half-plane `⟪ν, ·⟫ < 0`.  This
  contradicts `eq_of_agree_openSide`.
* `doublyPeriodic_of_forall_notMem_ONED` — with such an `M`, the pattern of `x` on `win M`
  determines the translate, and the pigeonhole principle along each coordinate axis produces
  two independent periods.

## Non-vacuity

The conclusion is *not* automatic in the degenerate cases, and the hypothesis is *not* vacuous.
For a constant configuration `X = {x}`, `ONED x = ∅` holds and `DoublyPeriodic x` indeed holds
— the statement is consistent, and the proof genuinely produces the two periods rather than
deriving `False`.  Conversely `ONED` is nonempty for, say, a configuration that is constant on
a half-plane and not globally constant, so the hypothesis really constrains `x`.  The alphabet
`α` is never assumed nonempty or inhabited; `Config α` for empty `α` is itself empty, so the
theorems are then vacuous for lack of an `x`, not for lack of content.

## Status

Complete; no `sorry`, no new `axiom`.
-/

namespace Nivat.BL

open Nivat Filter Topology

/-! ### The statement, restated -/

/-- The proposition Colle §3.1 appeals to, *without* any finiteness hypothesis.
`boyleLindStatement_false` below shows it is false as stated. -/
def BoyleLindStatement : Prop :=
  ∀ x : Config ℤ, (∀ w : ℝ × ℝ, w ≠ 0 → w ∉ ONED x) → DoublyPeriodic x

/-! ### Values of orbit-closure members -/

/-- Every value taken by a member of the orbit closure is already a value of `ξ`. -/
theorem range_subset_of_mem_orbitClosure {α : Type*} {ξ y : Config α}
    (hy : y ∈ orbitClosure ξ) : Set.range y ⊆ Set.range ξ := by
  rintro _ ⟨w, rfl⟩
  obtain ⟨u, hu⟩ := hy {w}
  exact ⟨u + w, (hu w (Finset.mem_singleton_self w)).symm⟩

/-- Finiteness of the alphabet actually used is inherited by the orbit closure. -/
theorem finite_range_of_mem_orbitClosure {α : Type*} {ξ y : Config α}
    (hA : (Set.range ξ).Finite) (hy : y ∈ orbitClosure ξ) : (Set.range y).Finite :=
  hA.subset (range_subset_of_mem_orbitClosure hy)

/-! ### From closed half-planes to open half-planes -/

/-- Every nonzero real direction has a lattice vector strictly on its negative side. -/
theorem exists_lattice_inner2_neg {ν : ℝ × ℝ} (hν : ν ≠ 0) : ∃ t : ℤ × ℤ, inner2 ν t < 0 := by
  have hor : ν.1 ≠ 0 ∨ ν.2 ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hν (Prod.ext hc.1 hc.2)
  rcases hor with h | h
  · rcases lt_or_gt_of_ne h with h' | h'
    · exact ⟨(1, 0), by simp [inner2]; linarith⟩
    · exact ⟨(-1, 0), by simp [inner2]; linarith⟩
  · rcases lt_or_gt_of_ne h with h' | h'
    · exact ⟨(0, 1), by simp [inner2]; linarith⟩
    · exact ⟨(0, -1), by simp [inner2]; linarith⟩

/-- **Open determinism.**  If no nonzero direction is one-sided nonexpansive, then two members
of the orbit closure agreeing on an *open* half-plane are equal.  (`ONED` is phrased with the
closed half-plane `sideOf`; the upgrade is by translating inside the half-plane.) -/
theorem eq_of_agree_openSide {α : Type*} {ξ : Config α}
    (hONED : ∀ w : ℝ × ℝ, w ≠ 0 → w ∉ ONED ξ) {ν : ℝ × ℝ} (hν : ν ≠ 0) {y y' : Config α}
    (hy : y ∈ orbitClosure ξ) (hy' : y' ∈ orbitClosure ξ)
    (hagree : ∀ v : ℤ × ℤ, inner2 ν v < 0 → y v = y' v) : y = y' := by
  obtain ⟨t, ht⟩ := exists_lattice_inner2_neg hν
  by_contra hne
  refine hONED ν hν ⟨hν, T t y, T_mem_of_mem_orbitClosure hy t, T t y',
    T_mem_of_mem_orbitClosure hy' t, ?_, ?_⟩
  · intro hTeq
    refine hne ?_
    have h2 : T (-t) (T t y) = T (-t) (T t y') := by rw [hTeq]
    rwa [← T_add, ← T_add, neg_add_cancel, T_zero, T_zero] at h2
  · intro z hz
    have hz0 : inner2 ν z ≤ 0 := hz
    show y (z + t) = y' (z + t)
    refine hagree _ ?_
    rw [inner2_add]
    linarith

/-! ### The separating window -/

/-- The `ℓ^∞`-box of radius `M`. -/
noncomputable def win (M : ℕ) : Finset (ℤ × ℤ) :=
  Finset.Icc (-(M : ℤ)) (M : ℤ) ×ˢ Finset.Icc (-(M : ℤ)) (M : ℤ)

theorem mem_win {M : ℕ} {z : ℤ × ℤ} :
    z ∈ win M ↔ (-(M : ℤ) ≤ z.1 ∧ z.1 ≤ (M : ℤ)) ∧ (-(M : ℤ) ≤ z.2 ∧ z.2 ≤ (M : ℤ)) := by
  simp [win, Finset.mem_product, Finset.mem_Icc]

/-- A point outside the box of radius `M` has `ℓ^1`-norm greater than `M`. -/
theorem lt_l1_of_notMem_win {M : ℕ} {z : ℤ × ℤ} (h : z ∉ win M) :
    (M : ℤ) < |z.1| + |z.2| := by
  by_contra hc
  push Not at hc
  refine h (mem_win.mpr ?_)
  have e1 := le_abs_self z.1
  have e2 := neg_abs_le z.1
  have e3 := le_abs_self z.2
  have e4 := neg_abs_le z.2
  have e5 := abs_nonneg z.1
  have e6 := abs_nonneg z.2
  omega

/-- Squared Euclidean norm on the lattice, as a natural number (so that `Nat.find` applies). -/
def sq (z : ℤ × ℤ) : ℕ := z.1.natAbs ^ 2 + z.2.natAbs ^ 2

theorem sq_cast (z : ℤ × ℤ) : (sq z : ℤ) = z.1 ^ 2 + z.2 ^ 2 := by
  simp only [sq, Nat.cast_add, Nat.cast_pow, Int.natCast_natAbs, sq_abs]

/-! ### Ultrafilter toolbox -/

/-- An ultrafilter limit of a bounded real sequence. -/
theorem exists_tendsto_of_bounded (𝔲 : Ultrafilter ℕ) (g : ℕ → ℝ) (C : ℝ) (hg : ∀ n, |g n| ≤ C) :
    ∃ a : ℝ, Tendsto g (𝔲 : Filter ℕ) (𝓝 a) := by
  have hmem : Set.Icc (-C) C ∈ Ultrafilter.map g 𝔲 := by
    rw [Ultrafilter.mem_map]
    have : g ⁻¹' Set.Icc (-C) C = Set.univ := by
      ext n
      simpa [Set.mem_Icc] using abs_le.mp (hg n)
    rw [this]
    exact Filter.univ_mem
  obtain ⟨a, -, ha⟩ := isCompact_Icc.ultrafilter_le_nhds' (Ultrafilter.map g 𝔲) hmem
  refine ⟨a, ?_⟩
  rwa [Tendsto, ← Ultrafilter.coe_map]

/-- An ultrafilter limit of a sequence with values in a finite set. -/
theorem exists_eventually_eq_of_finite {β : Type*} (𝔲 : Ultrafilter ℕ) (g : ℕ → β) (S : Set β)
    (hS : S.Finite) (hg : ∀ n, g n ∈ S) : ∃ a : β, {n : ℕ | g n = a} ∈ 𝔲 := by
  have hmem : S ∈ Ultrafilter.map g 𝔲 := by
    rw [Ultrafilter.mem_map]
    have : g ⁻¹' S = Set.univ := by ext n; simpa using hg n
    rw [this]
    exact Filter.univ_mem
  obtain ⟨a, -, ha⟩ := Ultrafilter.eq_pure_of_finite_mem hS hmem
  refine ⟨a, ?_⟩
  have h1 : ({a} : Set β) ∈ Ultrafilter.map g 𝔲 := by
    rw [ha]; exact Ultrafilter.mem_pure.mpr rfl
  rw [Ultrafilter.mem_map] at h1
  exact h1

/-! ### The key compactness lemma -/

/-- **Window injectivity.**  Under the hypothesis of the Boyle–Lind corollary and finiteness of
the alphabet, some finite box `win M` already separates the points of the orbit closure. -/
theorem exists_win_injOn {α : Type*} {ξ : Config α} (hA : (Set.range ξ).Finite)
    (hONED : ∀ w : ℝ × ℝ, w ≠ 0 → w ∉ ONED ξ) :
    ∃ M : ℕ, ∀ y ∈ orbitClosure ξ, ∀ y' ∈ orbitClosure ξ,
      (∀ w ∈ win M, y w = y' w) → y = y' := by
  classical
  by_contra hcon
  push Not at hcon
  choose y hy y' hy' hagr hne using hcon
  -- For each `M`, a point of minimal Euclidean norm at which `y M` and `y' M` differ.
  have hex : ∀ M : ℕ, ∃ k : ℕ, ∃ z : ℤ × ℤ, y M z ≠ y' M z ∧ sq z = k := by
    intro M
    obtain ⟨z, hz⟩ := Function.ne_iff.mp (hne M)
    exact ⟨sq z, z, hz, rfl⟩
  have hspec : ∀ M : ℕ, ∃ z : ℤ × ℤ, y M z ≠ y' M z ∧ sq z = Nat.find (hex M) :=
    fun M => Nat.find_spec (hex M)
  choose p hpne hpsq using hspec
  have hmin : ∀ (M : ℕ) (z : ℤ × ℤ), sq z < sq (p M) → y M z = y' M z := by
    intro M z hz
    by_contra hc
    rw [hpsq M] at hz
    exact Nat.find_min (hex M) hz ⟨z, hc, rfl⟩
  have hpwin : ∀ M : ℕ, p M ∉ win M := fun M hmem => hpne M (hagr M _ hmem)
  have hpl1 : ∀ M : ℕ, (M : ℤ) < |(p M).1| + |(p M).2| := fun M => lt_l1_of_notMem_win (hpwin M)
  -- Normalising factor.
  set s : ℕ → ℝ := fun M => ((|(p M).1| + |(p M).2| : ℤ) : ℝ) with hs_def
  have hsM : ∀ M : ℕ, (M : ℝ) < s M := by
    intro M
    have h := hpl1 M
    simp only [hs_def]
    exact_mod_cast h
  have hspos : ∀ M : ℕ, 0 < s M := by
    intro M
    have h1 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
    have := hsM M
    linarith
  -- The ultrafilter.
  set 𝔲 : Ultrafilter ℕ := Ultrafilter.of Filter.atTop with h𝔲_def
  have h𝔲le : (𝔲 : Filter ℕ) ≤ Filter.atTop := Ultrafilter.of_le _
  -- `s → ∞` along `𝔲`.
  have hstop : Tendsto s (𝔲 : Filter ℕ) Filter.atTop := by
    refine tendsto_atTop_mono (fun M => (hsM M).le) ?_
    exact tendsto_natCast_atTop_atTop.mono_left h𝔲le
  -- The normalised direction.
  set q1 : ℕ → ℝ := fun M => ((p M).1 : ℝ) / s M with hq1_def
  set q2 : ℕ → ℝ := fun M => ((p M).2 : ℝ) / s M with hq2_def
  have habs : ∀ M : ℕ, |q1 M| + |q2 M| = 1 := by
    intro M
    have hsp := hspos M
    have hs1 : |((p M).1 : ℝ)| + |((p M).2 : ℝ)| = s M := by
      simp only [hs_def]
      push_cast
      ring
    simp only [hq1_def, hq2_def, abs_div, abs_of_pos hsp]
    rw [← add_div, hs1, div_self (ne_of_gt hsp)]
  have hbd : ∀ (g : ℕ → ℝ), (∀ M, |g M| ≤ |q1 M| + |q2 M|) → ∀ M, |g M| ≤ 1 := by
    intro g hg M; rw [← habs M]; exact hg M
  obtain ⟨ν1, hν1⟩ := exists_tendsto_of_bounded 𝔲 q1 1
    (hbd q1 fun M => le_add_of_nonneg_right (abs_nonneg _))
  obtain ⟨ν2, hν2⟩ := exists_tendsto_of_bounded 𝔲 q2 1
    (hbd q2 fun M => le_add_of_nonneg_left (abs_nonneg _))
  set ν : ℝ × ℝ := (ν1, ν2) with hν_def
  -- `ν ≠ 0` because `|ν1| + |ν2| = 1`.
  have hνnorm : |ν1| + |ν2| = 1 := by
    have hlim : Tendsto (fun M => |q1 M| + |q2 M|) (𝔲 : Filter ℕ) (𝓝 (|ν1| + |ν2|)) :=
      (hν1.abs).add (hν2.abs)
    have hconst : Tendsto (fun M => |q1 M| + |q2 M|) (𝔲 : Filter ℕ) (𝓝 1) := by
      simp only [habs]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique hlim hconst
  have hνne : ν ≠ 0 := by
    intro h
    rw [hν_def, Prod.ext_iff] at h
    simp only [Prod.fst_zero, Prod.snd_zero] at h
    rw [h.1, h.2] at hνnorm
    norm_num at hνnorm
  -- Limits of the recentred configurations.
  have hyval : ∀ v : ℤ × ℤ, ∃ a : α, {M : ℕ | y M (v + p M) = a} ∈ 𝔲 := by
    intro v
    exact exists_eventually_eq_of_finite 𝔲 _ (Set.range ξ) hA
      fun M => range_subset_of_mem_orbitClosure (hy M) ⟨v + p M, rfl⟩
  have hy'val : ∀ v : ℤ × ℤ, ∃ a : α, {M : ℕ | y' M (v + p M) = a} ∈ 𝔲 := by
    intro v
    exact exists_eventually_eq_of_finite 𝔲 _ (Set.range ξ) hA
      fun M => range_subset_of_mem_orbitClosure (hy' M) ⟨v + p M, rfl⟩
  choose z hz using hyval
  choose z' hz' using hy'val
  -- Both limits lie in the orbit closure.
  have hzmem : ∀ (Y : ℕ → Config α), (∀ M, Y M ∈ orbitClosure ξ) →
      ∀ (Z : Config α), (∀ v : ℤ × ℤ, {M : ℕ | Y M (v + p M) = Z v} ∈ 𝔲) →
      Z ∈ orbitClosure ξ := by
    intro Y hY Z hZ
    refine orbitClosure_closed ?_
    intro W
    have hbig : (⋂ w ∈ W, {M : ℕ | Y M (w + p M) = Z w}) ∈ (𝔲 : Filter ℕ) :=
      (Filter.biInter_finset_mem W).mpr fun w _ => hZ w
    obtain ⟨M, hM⟩ := Filter.nonempty_of_mem hbig
    refine ⟨T (p M) (Y M), T_mem_of_mem_orbitClosure (hY M) _, fun w hw => ?_⟩
    simp only [Set.mem_iInter] at hM
    have := hM w hw
    show Z w = Y M (w + p M)
    exact this.symm
  have hzoc : z ∈ orbitClosure ξ := hzmem y hy z hz
  have hz'oc : z' ∈ orbitClosure ξ := hzmem y' hy' z' hz'
  -- They differ at the origin.
  have hdiff : z 0 ≠ z' 0 := by
    obtain ⟨M, hM1, hM2⟩ := Filter.nonempty_of_mem (Filter.inter_mem (hz 0) (hz' 0))
    simp only [Set.mem_ofPred_eq, zero_add] at hM1 hM2
    rw [← hM1, ← hM2]
    exact hpne M
  -- But they agree on an open half-plane, contradiction.
  have hagree : ∀ v : ℤ × ℤ, inner2 ν v < 0 → z v = z' v := by
    intro v hv
    -- The set of `M` where the minimality of `p M` applies.
    have hE : {M : ℕ | sq (v + p M) < sq (p M)} ∈ (𝔲 : Filter ℕ) := by
      set c : ℝ := ((v.1 ^ 2 + v.2 ^ 2 : ℤ) : ℝ) with hc_def
      have hfun : Tendsto (fun M => c / s M + 2 * ((v.1 : ℝ) * q1 M + (v.2 : ℝ) * q2 M))
          (𝔲 : Filter ℕ) (𝓝 (0 + 2 * ((v.1 : ℝ) * ν1 + (v.2 : ℝ) * ν2))) := by
        refine Tendsto.add ?_ (Tendsto.const_mul _ ((hν1.const_mul _).add (hν2.const_mul _)))
        have h0 : Tendsto (fun M => (s M)⁻¹) (𝔲 : Filter ℕ) (𝓝 0) := hstop.inv_tendsto_atTop
        have := h0.const_mul c
        simpa [div_eq_mul_inv] using this
      have hlim : (0 : ℝ) + 2 * ((v.1 : ℝ) * ν1 + (v.2 : ℝ) * ν2) < 0 := by
        have : inner2 ν v = (v.1 : ℝ) * ν1 + (v.2 : ℝ) * ν2 := by
          simp [inner2, hν_def]
        rw [this] at hv
        linarith
      have hev := hfun.eventually (gt_mem_nhds hlim)
      refine Filter.mem_of_superset hev ?_
      intro M hM
      simp only [Set.mem_ofPred_eq] at hM ⊢
      -- convert to the integer inequality
      have hkey : ((sq (v + p M) : ℤ) : ℝ) < ((sq (p M) : ℤ) : ℝ) := by
        have hsp : (0 : ℝ) < s M := hspos M
        have hsne : s M ≠ 0 := ne_of_gt hsp
        have hq1e : q1 M * s M = ((p M).1 : ℝ) := by
          simp only [hq1_def]; field_simp
        have hq2e : q2 M * s M = ((p M).2 : ℝ) := by
          simp only [hq2_def]; field_simp
        have hmul : (c / s M + 2 * ((v.1 : ℝ) * q1 M + (v.2 : ℝ) * q2 M)) * s M < 0 * s M :=
          mul_lt_mul_of_pos_right hM hsp
        rw [zero_mul] at hmul
        have hexp : (c / s M + 2 * ((v.1 : ℝ) * q1 M + (v.2 : ℝ) * q2 M)) * s M
            = c + 2 * ((v.1 : ℝ) * ((p M).1 : ℝ) + (v.2 : ℝ) * ((p M).2 : ℝ)) := by
          field_simp
          rw [← hq1e, ← hq2e]
          ring
        rw [hexp, hc_def] at hmul
        rw [sq_cast, sq_cast]
        simp only [Prod.fst_add, Prod.snd_add]
        push_cast at hmul ⊢
        nlinarith [hmul]
      have hint : (sq (v + p M) : ℤ) < (sq (p M) : ℤ) := by exact_mod_cast hkey
      exact_mod_cast hint
    obtain ⟨M, hM1, hM2, hM3⟩ :=
      Filter.nonempty_of_mem (Filter.inter_mem (hz v) (Filter.inter_mem (hz' v) hE))
    simp only [Set.mem_ofPred_eq] at hM1 hM2 hM3
    rw [← hM1, ← hM2]
    exact hmin M (v + p M) hM3
  exact hdiff (congrFun (eq_of_agree_openSide hONED hνne hzoc hz'oc hagree) 0)

/-! ### The corollary -/

/-- **The Boyle–Lind corollary** (finite-alphabet form).  If no nonzero direction is one-sided
nonexpansive on the orbit closure of `ξ`, then `ξ` is doubly periodic. -/
theorem doublyPeriodic_of_forall_notMem_ONED {α : Type*} {ξ : Config α}
    (hA : (Set.range ξ).Finite) (hONED : ∀ w : ℝ × ℝ, w ≠ 0 → w ∉ ONED ξ) :
    DoublyPeriodic ξ := by
  classical
  obtain ⟨M, hM⟩ := exists_win_injOn hA hONED
  -- A repeated window pattern gives a period.
  have key : ∀ u u' : ℤ × ℤ, (∀ w ∈ win M, ξ (u + w) = ξ (u' + w)) → (-u' + u) ∈ Per ξ := by
    intro u u' h
    have heq : T u ξ = T u' ξ := by
      refine hM (T u ξ) (T_mem_orbitClosure ξ u) (T u' ξ) (T_mem_orbitClosure ξ u') ?_
      intro w hw
      simp only [T_apply]
      rw [add_comm w u, add_comm w u']
      exact h w hw
    rw [mem_Per_iff]
    have h2 : T (-u') (T u ξ) = T (-u') (T u' ξ) := by rw [heq]
    rwa [← T_add, ← T_add, neg_add_cancel, T_zero] at h2
  -- Pigeonhole along any line.
  have hfin : ∀ g : ℤ → ℤ × ℤ, ∃ a b : ℤ, a ≠ b ∧ ∀ w ∈ win M, ξ (g a + w) = ξ (g b + w) := by
    intro g
    have hfin : Finite ↥(Set.range ξ) := hA.to_subtype
    obtain ⟨a, b, hab, heq⟩ := Finite.exists_ne_map_eq_of_infinite
      (fun k : ℤ => (fun w : {w // w ∈ win M} =>
        (⟨ξ (g k + w.1), Set.mem_range_self _⟩ : ↥(Set.range ξ))))
    refine ⟨a, b, hab, fun w hw => ?_⟩
    have := congrFun heq ⟨w, hw⟩
    exact congrArg Subtype.val this
  obtain ⟨a1, b1, hab1, h1⟩ := hfin (fun k : ℤ => (k, 0))
  obtain ⟨a2, b2, hab2, h2⟩ := hfin (fun k : ℤ => (0, k))
  refine ⟨-(b1, 0) + (a1, 0), key _ _ h1, -((0 : ℤ), b2) + ((0 : ℤ), a2), key _ _ h2, ?_⟩
  simp only [det, Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg, neg_zero, add_zero]
  have e1 : -b1 + a1 ≠ 0 := by omega
  have e2 : -b2 + a2 ≠ 0 := by omega
  simpa using mul_ne_zero e1 e2

/-- The `Config ℤ` form used by Colle §3.1. -/
theorem boyleLind {x : Config ℤ} (hA : (Set.range x).Finite)
    (hONED : ∀ w : ℝ × ℝ, w ≠ 0 → w ∉ ONED x) : DoublyPeriodic x :=
  doublyPeriodic_of_forall_notMem_ONED hA hONED

/-! ### Non-vacuity: the hypotheses are satisfiable -/

/-- The constant configuration. -/
def const0 : Config ℤ := fun _ => 0

theorem const0_orbitClosure_eq {y : Config ℤ} (hy : y ∈ orbitClosure const0) : y = const0 := by
  funext z
  obtain ⟨u, hu⟩ := hy {z}
  exact hu z (Finset.mem_singleton_self z)

/-- `const0` satisfies both hypotheses of `boyleLind`, so the theorem is not vacuous. -/
theorem const0_hyps :
    (Set.range const0).Finite ∧ ∀ w : ℝ × ℝ, w ≠ 0 → w ∉ ONED const0 := by
  constructor
  · exact Set.Finite.subset (Set.finite_singleton (0 : ℤ)) (by rintro _ ⟨z, rfl⟩; rfl)
  · rintro w hw ⟨-, y, hy, y', hy', hne, -⟩
    exact hne ((const0_orbitClosure_eq hy).trans (const0_orbitClosure_eq hy').symm)

example : DoublyPeriodic const0 := boyleLind const0_hyps.1 const0_hyps.2

/-! ### The finiteness hypothesis cannot be dropped -/

/-- The "linear ramp" configuration `(m, n) ↦ m`. -/
def slope : Config ℤ := fun z => z.1

theorem slope_apply_of_mem_orbitClosure {y : Config ℤ} (hy : y ∈ orbitClosure slope)
    (z : ℤ × ℤ) : y z = y 0 + z.1 := by
  obtain ⟨u, hu⟩ := hy {0, z}
  have h0 := hu 0 (by simp)
  have hz := hu z (by simp)
  simp only [slope, Prod.fst_add, add_zero] at h0 hz
  omega

theorem slope_ONED_empty : ∀ w : ℝ × ℝ, w ≠ 0 → w ∉ ONED slope := by
  rintro w hw ⟨-, y, hy, y', hy', hne, hagr⟩
  refine hne ?_
  funext z
  have h0 : y 0 = y' 0 := hagr 0 (by simp [sideOf, inner2])
  rw [slope_apply_of_mem_orbitClosure hy z, slope_apply_of_mem_orbitClosure hy' z, h0]

theorem slope_not_doublyPeriodic : ¬ DoublyPeriodic slope := by
  rintro ⟨u, hu, v, hv, hdet⟩
  have h1 : u.1 = 0 := by
    have := Per.apply hu 0
    simpa [slope] using this
  have h2 : v.1 = 0 := by
    have := Per.apply hv 0
    simpa [slope] using this
  exact hdet (by simp [det, h1, h2])

/-- **The unqualified Boyle–Lind statement is false.**  Some finiteness hypothesis on the
alphabet is genuinely needed. -/
theorem boyleLindStatement_false : ¬ BoyleLindStatement :=
  fun h => slope_not_doublyPeriodic (h slope slope_ONED_empty)

/-- The finite-alphabet repair of `BoyleLindStatement`, in the exact shape Colle §3.1 needs. -/
theorem boyleLindStatement_of_finite :
    ∀ x : Config ℤ, (Set.range x).Finite →
      (∀ w : ℝ × ℝ, w ≠ 0 → w ∉ ONED x) → DoublyPeriodic x :=
  fun _ hA hONED => boyleLind hA hONED

end Nivat.BL
