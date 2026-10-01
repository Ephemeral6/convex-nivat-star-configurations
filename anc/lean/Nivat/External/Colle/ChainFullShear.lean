/-
Copyright (c) 2026 Nivat formalisation project.
-/
import Nivat.External.Colle.MaxIndexProbe

/-!
# `ChainFullShearTransport` is false: a kernel-checked counterexample

Target (team-lead's dispatch, verbatim, = `Nivat.ColleReg.ChainFullShearTransport` unfolded,
`MaxIndexProbe.lean:264-267`):

```lean
theorem chainFull_shear_transport {ξ : Config ℤ} {e : ℤ × ℤ} {B : Set (ℤ × ℤ)}
    {vl u' b₀ : ℤ × ℤ} {c : ℤ} (K : ℤ) (k : ℕ) :
    PeriodOn (T e ξ) (chainFull B vl u' b₀ k) (c • vl) →
    PeriodOn (T e ξ) (chainFull B vl (u' - K • vl) b₀ k) (c • vl)
```

**Verdict: false.**  A concrete instance is built below where the antecedent holds and the
conclusion fails.  `check1.sh` EXIT=0, `#print axioms` clean.

## Why it breaks: the shear does not enlarge the level but can enlarge the domain

`mem_chainFull_shear_iff` (`MaxIndexProbe.lean:241`, already on the tree) says

    z ∈ chainFull B vl (u' - K•vl) b₀ n ↔
      z ∈ wedgeFull B vl u' ∧ expLevel u' vl b₀ n - K * uCoord u' vl b₀ z ≤ dot (expNormal u' vl) z

i.e. the sheared chain is `wedgeFull B vl u'` (shear-invariant, `wedgeFull_shear`) cut by a
*tilted* half-plane — the cut normal rotates by `K` units of `uCoord`, it is not a reindexing of
`z`.  `PeriodOn x U h := ∀ z ∈ U, z + h ∈ U → x (z+h) = x z` (`Lemma41.lean:659`) is **antitone**
in `U` (`PeriodOn.mono : U ⊆ V → PeriodOn x V h → PeriodOn x U h`, same file) — periodicity on a
*bigger* set implies it on a smaller subset, never the other way.  So if shearing enlarges the
domain (`chainFull B vl u' b₀ k ⊆ chainFull B vl (u'-K•vl) b₀ k`, which happens for suitable
signs of `K`), `PeriodOn` on the small piece says nothing about the enlarged piece: exactly the
gap the witness below exploits.

## The witness, concretely

`B := {(0,0)}`, `vl := (0,1)`, `u' := (1,0)`, `b₀ := (0,0)`, `K := 1`, `c := 1`, `k := 0`,
`e := (0,0)`.  With these numbers (`mem_wedgeFull_cex`, `expNormal`/`expLevel`/`uCoord` computed
directly below):

* unsheared: `chainFull B vl u' b₀ 0 = {z | 0 ≤ z.1 ∧ 0 ≤ z.2}` (`mem_chainFull0_cex`);
* sheared (`K=1`): `chainFull B vl (u'-vl) b₀ 0 = {z | 0 ≤ z.1 ∧ 0 ≤ z.2 + z.1}`
  (`mem_chainFull1_cex`) — a **strictly bigger** set (e.g. `(1,-1)` is in it but not in the
  unsheared set).

`ξCex (x,y) := if 0 ≤ y then 0 else if (x,y) = (1,-1) then 1 else 0` is constant `0` on the
unsheared set (period `1 • vl = (0,1)` trivially holds there, `not_periodOn` isn't even needed),
but `(1,-1)` and `(1,-1)+(0,1) = (1,0)` are **both** in the sheared set, and `ξCex` disagrees on
them (`1 ≠ 0`) — so `PeriodOn` fails on the sheared set.  `e := (0,0)` throughout, so `T e ξCex =
ξCex` (`T_zero`), no obfuscation from the shift.

## Witness legality (`ChainFullShearTransport` has no side premises beyond its own antecedent)

`ChainFullShearTransport ξ e B vl u' b₀ c K k` is our own named `Prop`, not a transcription of a
Collé definition, and it carries no hypotheses beyond `PeriodOn (T e ξ) (chainFull B vl u' b₀ k)
(c•vl)` itself — no `hunimod`, no primitivity, no minimal-counterexample binder.  So the only
thing to verify is that this one antecedent holds for the witness, which `periodOn_chainFull0`
proves outright (kernel-checked, no `sorry`), and that the conclusion fails, which
`not_periodOn_chainFull1` proves outright.  There is nothing left to smuggle in.
-/

set_option autoImplicit false

namespace Nivat.ChainFullShear

open Nivat
open Nivat.LE2 (dot)
open Nivat.ColleReg
open Nivat.L1Line0 (uCoord)
open Nivat.Colle41 (PeriodOn)

/-! ## The witness data -/

/-- `Bcex := {(0,0)}`. -/
def Bcex : Set (ℤ × ℤ) := {(0, 0)}

/-- `vlCex := (0,1)`. -/
def vlCex : ℤ × ℤ := (0, 1)

/-- `u'Cex := (1,0)`. -/
def u'Cex : ℤ × ℤ := (1, 0)

/-- `b₀Cex := (0,0)`. -/
def b₀Cex : ℤ × ℤ := (0, 0)

/-- The configuration: `0` on the upper half-plane `y ≥ 0`, `1` at the single point `(1,-1)`,
`0` everywhere else. -/
noncomputable def ξCex : Config ℤ :=
  fun z => if 0 ≤ z.2 then (0 : ℤ) else if z = (1, -1) then 1 else 0

/-! ## Membership computations -/

theorem mem_wedgeFull_cex {z : ℤ × ℤ} :
    z ∈ wedgeFull Bcex vlCex u'Cex ↔ 0 ≤ z.1 := by
  constructor
  · rintro ⟨g, hg, t, rfl⟩
    rw [mem_fullSweep_iff] at hg
    obtain ⟨b, hb, k, rfl⟩ := hg
    simp only [Bcex, Set.mem_singleton_iff] at hb
    subst hb
    simp only [vlCex, u'Cex, Prod.fst_add, Prod.smul_fst, smul_eq_mul]
    omega
  · intro hz
    refine ⟨(0, z.2), ?_, z.1.toNat, ?_⟩
    · rw [mem_fullSweep_iff]
      exact ⟨(0, 0), rfl, z.2, by simp [vlCex]⟩
    · have ht : ((z.1.toNat : ℤ)) = z.1 := Int.toNat_of_nonneg hz
      apply Prod.ext
      · simp only [Prod.fst_add, Prod.smul_fst, u'Cex, smul_eq_mul, mul_one, Prod.fst_zero]
        omega
      · simp only [Prod.snd_add, Prod.smul_snd, u'Cex, smul_eq_mul, mul_zero, Prod.snd_zero]
        ring

theorem expNormal_cex : expNormal u'Cex vlCex = (0, 1) := by
  simp [expNormal, det, u'Cex, vlCex]

theorem expLevel0_cex : expLevel u'Cex vlCex b₀Cex 0 = 0 := by
  simp [expLevel, expNormal_cex, dot, b₀Cex]

theorem uCoord_cex (z : ℤ × ℤ) : uCoord u'Cex vlCex b₀Cex z = z.1 := by
  simp only [uCoord, det, u'Cex, vlCex, b₀Cex, Prod.fst_sub, Prod.snd_sub, Prod.fst_zero,
    Prod.snd_zero]
  ring

theorem mem_chainFull0_cex {z : ℤ × ℤ} :
    z ∈ chainFull Bcex vlCex u'Cex b₀Cex 0 ↔ 0 ≤ z.1 ∧ 0 ≤ z.2 := by
  rw [Nivat.L1Line0.mem_chainFull_iff, mem_wedgeFull_cex, expLevel0_cex, expNormal_cex]
  simp only [dot, Prod.fst_zero, zero_mul, Prod.snd_one, one_mul, zero_add]

theorem mem_chainFull1_cex {z : ℤ × ℤ} :
    z ∈ chainFull Bcex vlCex (u'Cex - (1 : ℤ) • vlCex) b₀Cex 0 ↔ 0 ≤ z.1 ∧ 0 ≤ z.2 + z.1 := by
  rw [mem_chainFull_shear_iff, mem_wedgeFull_cex, expLevel0_cex, expNormal_cex, uCoord_cex]
  simp only [dot, Prod.fst_zero, zero_mul, Prod.snd_one, one_mul, zero_sub, one_mul]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith⟩

/-! ## The two `PeriodOn` facts -/

theorem periodOn_chainFull0 :
    PeriodOn (T (0, 0) ξCex) (chainFull Bcex vlCex u'Cex b₀Cex 0) ((1 : ℤ) • vlCex) := by
  intro z hz _
  rw [mem_chainFull0_cex] at hz
  obtain ⟨_, hz2⟩ := hz
  simp only [T_apply, ξCex, vlCex]
  norm_num
  have h1 : (0 : ℤ) ≤ z.2 + 1 := by linarith
  have h2 : (0 : ℤ) ≤ z.2 := hz2
  simp [if_pos h1, if_pos h2]

theorem not_periodOn_chainFull1 :
    ¬ PeriodOn (T (0, 0) ξCex) (chainFull Bcex vlCex (u'Cex - (1 : ℤ) • vlCex) b₀Cex 0)
      ((1 : ℤ) • vlCex) := by
  intro h
  have hz : ((1, -1) : ℤ × ℤ) ∈ chainFull Bcex vlCex (u'Cex - (1 : ℤ) • vlCex) b₀Cex 0 := by
    rw [mem_chainFull1_cex]; constructor <;> norm_num
  have hstep : ((1, -1) : ℤ × ℤ) + (1 : ℤ) • vlCex = (1, 0) := by
    simp [vlCex]
  have hz' : ((1, -1) : ℤ × ℤ) + (1 : ℤ) • vlCex ∈
      chainFull Bcex vlCex (u'Cex - (1 : ℤ) • vlCex) b₀Cex 0 := by
    rw [hstep, mem_chainFull1_cex]; constructor <;> norm_num
  have heq := h (1, -1) hz hz'
  rw [hstep] at heq
  simp only [T_apply, zero_add, ξCex] at heq
  norm_num at heq

/-! ## The refutation -/

/-- **`ChainFullShearTransport` is false.**  Kernel-checked counterexample: `hbase` holds on the
unsheared level-`0` chain and fails on the `K = 1` sheared one, for the concrete data above. -/
theorem not_chainFullShearTransport :
    ¬ ChainFullShearTransport ξCex (0, 0) Bcex vlCex u'Cex b₀Cex 1 1 0 := by
  intro h
  exact not_periodOn_chainFull1 (h periodOn_chainFull0)

section AxiomReceipts

#print axioms Nivat.ChainFullShear.mem_wedgeFull_cex
#print axioms Nivat.ChainFullShear.expNormal_cex
#print axioms Nivat.ChainFullShear.expLevel0_cex
#print axioms Nivat.ChainFullShear.uCoord_cex
#print axioms Nivat.ChainFullShear.mem_chainFull0_cex
#print axioms Nivat.ChainFullShear.mem_chainFull1_cex
#print axioms Nivat.ChainFullShear.periodOn_chainFull0
#print axioms Nivat.ChainFullShear.not_periodOn_chainFull1
#print axioms Nivat.ChainFullShear.not_chainFullShearTransport

end AxiomReceipts

end Nivat.ChainFullShear
