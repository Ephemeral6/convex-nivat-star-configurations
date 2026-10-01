/-
# `region_periods_and_rays` was false a second time (2026-09-18)

`Nivat.ColleReg.region_periods_and_rays` (`RegionSteps.lean`) was rewritten on 2026-09-17 over
a `ChainDataGeom`, and `hξ` was dropped from it as "unused".  `Step_PeriodsRays.lean` refutes
the *earlier* bare-`ChainData` form; its witness has a half-strip region with one recession
direction and cannot carry a `ChainDataGeom` (`RegionSteps.lean`, section "Why the r67
refutation no longer applies").  This file refutes the **2026-09-17 form**: the witness below
does carry a `ChainDataGeom`, every field proved.

## The witness

* `ξ := etaC = fun z => z.1 + [z.2 < 0]`, `xper := xperC = fun z => z.1`, `ϑ := thC = fun z => z.1`.
* `Â_∞ = Qs`, the closed first quadrant — receding in both `p = (0,1)` and `v_J = (1,0)`,
  so `rec_p`/`rec_vJ`/`vJ_ne`/`dot_nJ_vJ`/`dot_nJ_p` all hold (the conjunction that defeats the
  old witness).
* `nfp_L` holds because the period group of `xperC` on the half-plane `{0 ≤ z.1}` is exactly
  the vertical vectors: rank **one**.

## Why the statement fails on it

The conclusion asks for `h' = n • v_J = (n, 0)`, `n > 0`, with `ϑ (z + h') = ϑ z` along a ray
inside `R`; but `ϑ z = z.1`, so `z.1 + n = z.1`.  Nothing in the hypotheses forbids this: the
second period in Collé comes from **Lemma 4.1** (`b3_colle2.txt:904`, "Due to Claim 4.11 and
Lemma 4.1"), whose Lean form `Colle41.lemma41_of_sweep` (`Lemma41.lean:702-703`) consumes
`(Set.range η).Finite` and `x ∈ orbitClosure η` as its first two arguments — the two facts the
2026-09-17 signature had dropped.  `etaC` has infinite range and `thC` is unconstrained.

## Substitution check (measured before the signature was repaired)

With the 2026-09-17 signature the following elaborated, so `RPRStatement` is *implied by* the
theorem and refuting it refutes the theorem (FROZEN E1 discipline):

    example : RPRStatement := fun _ _ _ _ _ _ _ cg _ hSgen _ hc hp hconv hne hag =>
      Nivat.ColleReg.region_periods_and_rays cg hSgen hc hp hconv hne hag

`bash scripts/check1.sh tmp/rpr_refute.lean`, 2026-09-18:

    'Nivat.RPRCx.not_RPRStatement' depends on axioms: [propext, Classical.choice, Quot.sound]
    EXIT=0

The `example` is not kept live: the repaired signature takes `hξ` and `hϑ_mem`, which
`RPRStatement` deliberately does not offer.  `RPRStatement` below is the 2026-09-17 statement
verbatim, binders made explicit.
-/
-- **2026-09-20, `CLAUDE.md` hard rule 9 — import narrowed, no declaration touched.**
-- This file used to `import Nivat.External.Colle.RegionSteps`, and that was its *only* import.
-- Nothing after this line references `Nivat.ColleReg` (grep: zero hits); the dependency was
-- inherited from the days when §4 below quoted `region_periods_and_rays` by name rather than
-- restating it.  The edge was expensive: `ShellMink` imports this module for `cgw`'s data, so
-- the whole shell/chain tower above it (`ShellSweep`, `AhatMono`, `ChainAssemble`, `ItemIIRec`)
-- was transitively **downstream of the `sorry` it is built to fill**
-- (`RegionSteps.lean:1035`, `exists_chainData`), and `ChainPartsFeed.lean` could not `import`
-- any of it.  Same shape as the 2026-09-20 `ChainPartsFeed` fix, one level up.
import Nivat.External.Colle.ChainGeom

namespace Nivat.ColleStep.PeriodsRays2

open Nivat Nivat.LE2 Nivat.MaxEnv Nivat.Colle Nivat.Colle35

/-! ## 1. The data -/

def xperC : Config ℤ := fun z => z.1
def etaC  : Config ℤ := fun z => z.1 + (if z.2 < 0 then 1 else 0)
def thC   : Config ℤ := fun z => z.1

def vlv : ℤ × ℤ := (0, -1)   -- `v_ℓ`, also the shell sweep direction `v_{ℓ_{J-1}}`
def pv  : ℤ × ℤ := (0, 1)    -- the period `p`
def vJv : ℤ × ℤ := (1, 0)    -- `v_{ℓ_J}`
def nJv : ℤ × ℤ := (0, 1)    -- `n_J`

def Sw    : Finset (ℤ × ℤ) := {0}
def genw  : ℤ × ℤ := 0
def Sgenw : Finset (ℤ × ℤ) := {(0, 0), (1, 0)}

def Qs : Set (ℤ × ℤ) := {z | 0 ≤ z.1 ∧ 0 ≤ z.2}
def Ah (i : ℕ) : Set (ℤ × ℤ) :=
  {z | 0 ≤ z.1 ∧ z.1 ≤ (i : ℤ) ∧ 0 ≤ z.2 ∧ z.2 ≤ (i : ℤ)}
def Sh (i ε : ℕ) : Set (ℤ × ℤ) :=
  {z | 0 ≤ z.1 ∧ z.1 ≤ (i : ℤ) ∧ -(ε : ℤ) ≤ z.2 ∧ z.2 ≤ (i : ℤ)}
def ShInf (ε : ℕ) : Set (ℤ × ℤ) := {z | 0 ≤ z.1 ∧ -(ε : ℤ) ≤ z.2}
def Fil (i i₀ ε n : ℕ) : Set (ℤ × ℤ) :=
  match n with
  | 0 => Ah i ∪ Sh i₀ ε
  | _ + 1 => Ah i ∪ Sh i₀ ε ∪ Sh i ε

theorem mem_Qs {z : ℤ × ℤ} : z ∈ Qs ↔ 0 ≤ z.1 ∧ 0 ≤ z.2 := Iff.rfl
theorem mem_Ah {i : ℕ} {z : ℤ × ℤ} :
    z ∈ Ah i ↔ 0 ≤ z.1 ∧ z.1 ≤ (i : ℤ) ∧ 0 ≤ z.2 ∧ z.2 ≤ (i : ℤ) := Iff.rfl
theorem mem_Sh {i ε : ℕ} {z : ℤ × ℤ} :
    z ∈ Sh i ε ↔ 0 ≤ z.1 ∧ z.1 ≤ (i : ℤ) ∧ -(ε : ℤ) ≤ z.2 ∧ z.2 ≤ (i : ℤ) := Iff.rfl
theorem mem_ShInf {ε : ℕ} {z : ℤ × ℤ} :
    z ∈ ShInf ε ↔ 0 ≤ z.1 ∧ -(ε : ℤ) ≤ z.2 := Iff.rfl

theorem iUnion_Ah : (⋃ i, Ah i) = Qs := by
  ext z
  constructor
  · intro hz
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
    exact ⟨hi.1, hi.2.2.1⟩
  · intro hz
    refine Set.mem_iUnion.mpr ⟨(max z.1 z.2).toNat, ?_⟩
    have h : ((max z.1 z.2).toNat : ℤ) = max z.1 z.2 :=
      Int.toNat_of_nonneg (le_trans hz.1 (le_max_left _ _))
    exact ⟨hz.1, by rw [h]; exact le_max_left _ _, hz.2,
      by rw [h]; exact le_max_right _ _⟩

theorem reach_Qs : reachSet Qs vlv = {z : ℤ × ℤ | 0 ≤ z.1} := by
  ext z
  constructor
  · rintro ⟨g, hg, t, rfl⟩
    show (0 : ℤ) ≤ _
    simp only [Prod.fst_add, Prod.smul_fst, vlv, smul_eq_mul, mul_zero, add_zero]
    exact hg.1
  · intro hz
    have hz1 : (0 : ℤ) ≤ z.1 := hz
    rcases le_or_gt 0 z.2 with h | h
    · exact ⟨z, ⟨hz1, h⟩, 0, by simp⟩
    · refine ⟨(z.1, 0), ⟨hz1, le_refl 0⟩, (-z.2).toNat, ?_⟩
      have ht : (((-z.2).toNat : ℤ)) = -z.2 := Int.toNat_of_nonneg (by omega)
      refine Prod.ext ?_ ?_
      · simp [vlv]
      · simp [vlv, ht]

/-! ## 2. Lattice convexity and the generating set -/

theorem convex_pt : Convex ℝ {q : ℝ × ℝ | q.1 = 0 ∧ q.2 = 0} := by
  intro u hu v hv a b _ _ hab
  refine ⟨?_, ?_⟩
  · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, hu.1, hv.1]; ring
  · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, hu.2, hv.2]; ring

theorem latticeConvex_Sw : LatticeConvex Sw := by
  intro z hz
  have hsub : Conv Sw ⊆ {q : ℝ × ℝ | q.1 = 0 ∧ q.2 = 0} := by
    apply convexHull_min _ convex_pt
    rintro _ ⟨w, hw, rfl⟩
    rw [Finset.mem_coe] at hw
    have hw0 : w = (0 : ℤ × ℤ) := by simpa [Sw] using hw
    subst hw0
    exact ⟨by norm_num [toReal], by norm_num [toReal]⟩
  obtain ⟨h1, h2⟩ := hsub hz
  simp only [toReal] at h1 h2
  have e1 : z.1 = 0 := by exact_mod_cast h1
  have e2 : z.2 = 0 := by exact_mod_cast h2
  simp [Sw, Prod.ext_iff, e1, e2]

/-- `Sw.erase 0 = ∅`, hence lattice convex vacuously. -/
theorem latticeConvex_Sw_erase : LatticeConvex (Sw.erase 0) := by
  have hE : Sw.erase 0 = (∅ : Finset (ℤ × ℤ)) := by decide
  rw [hE]
  intro y hy
  simp [Conv, convexHull_empty] at hy

/-- **The degenerate window generates everywhere.**  Round 80 widened `ChainData.fillCover`
(`Lemma35.lean:765`) from the single-generator filtration `⋃ n, fill i i₀ ε n` to the
unrestricted `Colle37.GenClosure S (Ahat i ∪ shell i₀ ε)`.  For the one-point window
`Sw = {0}` the erased set is empty, so a single `GenClosure.step` at `a := 0`, `w := z` has no
premise to discharge and reaches every `z` from any `D` whatsoever — the same degeneracy that
makes `fillStep` one line at every `Sw`-based witness instance.  Used by the `cgw` instance
below and by `ShellConvex.cgn` / `ShellConvex.cgc`. -/
theorem genClosure_Sw_all (D : Set (ℤ × ℤ)) (z : ℤ × ℤ) : Colle37.GenClosure Sw D z := by
  have hE : Sw.erase 0 = (∅ : Finset (ℤ × ℤ)) := by decide
  have h := Colle37.GenClosure.step (S := Sw) (D := D) (a := (0 : ℤ × ℤ)) (w := z)
    (by simp [Sw]) latticeConvex_Sw_erase (by rw [hE]; simp)
  simpa using h

theorem convex_seg : Convex ℝ {q : ℝ × ℝ | q.2 = 0 ∧ 0 ≤ q.1 ∧ q.1 ≤ 1} := by
  intro u hu v hv a b ha hb hab
  obtain ⟨hu1, hu2, hu3⟩ := hu
  obtain ⟨hv1, hv2, hv3⟩ := hv
  refine ⟨?_, ?_, ?_⟩
  · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, hu1, hv1]; ring
  · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
    have := mul_nonneg ha hu2
    have := mul_nonneg hb hv2
    linarith
  · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
    nlinarith

theorem latticeConvex_Sgenw : LatticeConvex Sgenw := by
  intro z hz
  have hsub : Conv Sgenw ⊆ {q : ℝ × ℝ | q.2 = 0 ∧ 0 ≤ q.1 ∧ q.1 ≤ 1} := by
    apply convexHull_min _ convex_seg
    rintro _ ⟨w, hw, rfl⟩
    rw [Finset.mem_coe] at hw
    have hw' : w = ((0:ℤ), (0:ℤ)) ∨ w = ((1:ℤ), (0:ℤ)) := by simpa [Sgenw] using hw
    rcases hw' with rfl | rfl <;>
      exact ⟨by norm_num [toReal], by norm_num [toReal], by norm_num [toReal]⟩
  obtain ⟨h1, h2, h3⟩ := hsub hz
  simp only [toReal] at h1 h2 h3
  have e1 : z.2 = 0 := by exact_mod_cast h1
  have e2 : (0 : ℤ) ≤ z.1 := by exact_mod_cast h2
  have e3 : z.1 ≤ 1 := by exact_mod_cast h3
  have e4 : z.1 = 0 ∨ z.1 = 1 := by omega
  rcases e4 with h | h <;> simp [Sgenw, Prod.ext_iff, e1, h]

/-- Every member of `X_η` satisfies the same first difference along `(1,0)`: this is
`η z = z.1 + f z.2`, read through `orbitClosure` (`Orbit.lean:43`). -/
theorem shift_inv {x : Config ℤ} (hx : x ∈ orbitClosure etaC) (w : ℤ × ℤ) :
    x (w + (1, 0)) = x w + 1 := by
  obtain ⟨u, hu⟩ := hx {w, w + (1, 0)}
  have h1 : x w = etaC (u + w) := hu w (by simp)
  have h2 : x (w + (1, 0)) = etaC (u + (w + (1, 0))) := hu _ (by simp)
  have hs : (u + (w + ((1:ℤ), (0:ℤ)))).2 = (u + w).2 := by simp
  have hf : (u + (w + ((1:ℤ), (0:ℤ)))).1 = (u + w).1 + 1 := by simp; ring
  rw [h1, h2]
  simp only [etaC, hs, hf]
  ring

theorem isGeneratingSet_etaC : IsGeneratingSet etaC Sgenw := by
  refine ⟨⟨(0, 0), by simp [Sgenw]⟩, latticeConvex_Sgenw, ?_⟩
  intro a ha _
  have hstep : ∀ {x : Config ℤ}, x ∈ orbitClosure etaC →
      x ((1 : ℤ), (0 : ℤ)) = x ((0 : ℤ), (0 : ℤ)) + 1 := by
    intro x hx
    have := shift_inv hx ((0 : ℤ), (0 : ℤ))
    simpa using this
  have ha' : a = ((0:ℤ), (0:ℤ)) ∨ a = ((1:ℤ), (0:ℤ)) := by simpa [Sgenw] using ha
  rcases ha' with rfl | rfl
  · refine ⟨ha, ?_⟩
    intro x hx y hy hagr
    have h10 : x ((1:ℤ), (0:ℤ)) = y ((1:ℤ), (0:ℤ)) :=
      hagr _ (by simp [Sgenw, Prod.ext_iff])
    have hx' := hstep hx
    have hy' := hstep hy
    omega
  · refine ⟨ha, ?_⟩
    intro x hx y hy hagr
    have h00 : x ((0:ℤ), (0:ℤ)) = y ((0:ℤ), (0:ℤ)) :=
      hagr _ (by simp [Sgenw, Prod.ext_iff])
    have hx' := hstep hx
    have hy' := hstep hy
    omega

/-! ## 3. The bundle -/

/-- `Â_i^{(ε)}` sits in the half-strip `H_{B_i}(ℓ) - k_i v_ℓ`: the strip runs *downwards*
because `vl = (0,-1)`, which is exactly the side the shell grows on. -/
theorem strip_mem {i ε : ℕ} {z : ℤ × ℤ} (hz : z ∈ Sh i ε) :
    z + ((0 : ℕ) : ℤ) • vlv ∈ Colle35.halfStrip (Ah i) vlv := by
  obtain ⟨h1, h2, _, h4⟩ := hz
  have hi : (0 : ℤ) ≤ (i : ℤ) := Int.natCast_nonneg i
  rcases le_or_gt 0 z.2 with h | h
  · exact ⟨z, ⟨h1, h2, h, h4⟩, 0, by simp⟩
  · refine ⟨(z.1, 0), ⟨h1, h2, le_refl 0, hi⟩, (-z.2).toNat, ?_⟩
    have ht : (((-z.2).toNat : ℤ)) = -z.2 := Int.toNat_of_nonneg (by omega)
    refine Prod.ext ?_ ?_
    · simp [vlv]
    · simp [vlv, ht]

/-- The `ℓ_ι`-normal that `ChainDataGeom.ahat_halfPlane_L` / `nfp_L` write out inline
(`ChainGeom.lean:134-135`, `:172-174`): `det p v_J • (-p.2, p.1)`. -/
def nLv : ℤ × ℤ := det pv vJv • ((-pv.2, pv.1) : ℤ × ℤ)

theorem nLv_eq : nLv = ((1 : ℤ), (0 : ℤ)) := by
  simp [nLv, det, pv, vJv]

theorem dot_nLv (z : ℤ × ℤ) : dot nLv z = z.1 := by
  rw [nLv_eq]; simp [dot]

def cgw : ChainDataGeom etaC xperC vlv pv Sw genw where
  Env := fun _ => True
  B := Ah
  A := Ah
  u := fun _ => 0
  kk := fun _ => 0
  Ahat := Ah
  shell := Sh
  shellInf := ShInf
  envB := fun _ => trivial
  envA := fun _ => trivial
  subBA := fun _ => subset_rfl
  subAB := by
    intro i z hz
    obtain ⟨h1, h2, h3, h4⟩ := hz
    refine ⟨h1, ?_, h3, ?_⟩ <;> push_cast <;> omega
  subStrip := fun i => Colle35.subset_halfStrip _ _
  agreeA := by
    intro i z hz
    have hnn : ¬ (z.2 < 0) := by have := hz.2.2.1; omega
    simp only [etaC, xperC, add_zero, if_neg hnn, add_zero]
  AhatEq := by
    intro i
    ext z
    simp
  AhatMono := by
    intro i j hij z hz
    obtain ⟨h1, h2, h3, h4⟩ := hz
    have hc : (i : ℤ) ≤ (j : ℤ) := by exact_mod_cast hij
    exact ⟨h1, by omega, h3, by omega⟩
  maximalHat := by
    intro i Tset _ _ hstrip hagr z hz
    obtain ⟨b, hb, t, hbt⟩ := hstrip hz
    obtain ⟨hb1, hb2, hb3, hb4⟩ := hb
    have ht : (0 : ℤ) ≤ (t : ℤ) := Int.natCast_nonneg t
    have hf : z.1 = b.1 := by
      have h := congrArg Prod.fst hbt
      simp [vlv] at h
      omega
    have hs : z.2 = b.2 - (t : ℤ) := by
      have h := congrArg Prod.snd hbt
      simp [vlv] at h
      omega
    have hzz : etaC z = xperC z := by simpa using hagr z hz
    have hnn : (0 : ℤ) ≤ z.2 := by
      by_contra hc
      have hc' : z.2 < 0 := not_le.mp hc
      simp only [etaC, xperC] at hzz
      rw [if_pos hc'] at hzz
      omega
    exact ⟨by omega, by omega, hnn, by omega⟩
  shellFinite := by
    intro i ε
    have hfin : ((Set.Icc (0:ℤ) (i:ℤ)) ×ˢ (Set.Icc (-(ε:ℤ)) (i:ℤ))).Finite :=
      (Set.finite_Icc _ _).prod (Set.finite_Icc _ _)
    refine hfin.subset ?_
    rintro z ⟨h1, h2, h3, h4⟩
    exact ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
  subShell := by
    rintro i ε z ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h2, by omega, h4⟩
  shellSubInf := by
    rintro i ε z ⟨h1, _, h3, _⟩
    exact ⟨h1, h3⟩
  shellInfZero := by
    rintro z ⟨h1, h2⟩
    have h2' : (0 : ℤ) ≤ z.2 := by simpa using h2
    rw [iUnion_Ah]
    exact ⟨h1, h2'⟩
  -- `I₀`（第 162 轮，`b3_colle2.txt:520`）：本实例的 shell 字段都不看 `i` 的下界，取 0。
  I₀ := 0
  shellSubStrip := fun _ _ _ _ _ _ _ hz => strip_mem hz
  shellProper := by
    intro ε _i₀ hε _hEnv i _hi hsub
    have hε' : (1 : ℤ) ≤ (ε : ℤ) := by exact_mod_cast hε
    have hi : (0 : ℤ) ≤ (i : ℤ) := Int.natCast_nonneg i
    have hmem : ((0:ℤ), (-1:ℤ)) ∈ Sh i ε :=
      ⟨le_refl 0, hi, by omega, by omega⟩
    have hcon := hsub hmem
    have := hcon.2.2.1
    omega
  shellEnv := ⟨1, 0, one_pos, fun _ _ => trivial⟩
  fill := Fil
  fillZero := fun i i₀ ε z hz => hz
  fillStep := by
    intro i i₀ ε n z _
    refine Or.inr ⟨z, (zero_add z).symm, ?_⟩
    intro b hb
    simp [Sw, genw] at hb
  -- Round 80 widened `ChainData.fillCover` from `⋃ n, fill i i₀ ε n` to the unrestricted
  -- `Colle37.GenClosure S (Ahat i ∪ shell i₀ ε)` (`Lemma35.lean:765`); `genClosure_Sw_all`
  -- (`:150`) discharges it for the one-point window.
  fillCover := fun ε i₀ _hε _hEnv i _hi z _ => genClosure_Sw_all (Ah i ∪ Sh i₀ ε) z
  -- ChainDataWithShell (ChainShell.lean:49-63)
  vJ1 := vlv
  nJ := nJv
  cJ := 0
  shellInf_eq := by
    intro ε
    rw [iUnion_Ah, shell_eq_reach_inter, reach_Qs]
    ext z
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      show (0 : ℤ) - (ε : ℤ) ≤ dot nJv z
      simp only [dot, nJv]
      omega
    · rintro ⟨h1, h2⟩
      have h2' : (0 : ℤ) - (ε : ℤ) ≤ dot nJv z := h2
      simp only [dot, nJv] at h2'
      exact ⟨h1, by omega⟩
  ahat_nonempty := by
    refine ⟨((0:ℤ), (0:ℤ)), ?_⟩
    rw [iUnion_Ah]
    exact ⟨le_refl 0, le_refl 0⟩
  ahat_halfPlane := by
    intro g hg
    rw [iUnion_Ah] at hg
    show (0 : ℤ) ≤ dot nJv g
    simp only [dot, nJv]
    have := hg.2
    omega
  -- ChainDataGeom (ChainGeom.lean:69-174)
  vJ := vJv
  a := 0
  a' := 0
  r := 0
  latticeConvex_S := latticeConvex_Sw
  a_mem := by simp [Sw]
  a'_mem := by simp [Sw]
  lex := by intro b hb; simp [Sw] at hb
  lex' := by intro b hb; simp [Sw] at hb
  edge := by intro b hb; simp [Sw] at hb
  edge' := by intro b hb; simp [Sw] at hb
  dot_nJ_vJ := by simp [dot, nJv, vJv]
  bottom := by
    intro ε
    refine ⟨((0:ℤ), -(ε:ℤ) - 1), 0, ?_, ?_, ?_, ?_⟩
    · show dot nJv ((0:ℤ), -(ε:ℤ) - 1) = (0:ℤ) - (ε:ℤ) - 1
      simp [dot, nJv]
    · intro k hk
      rw [iUnion_Ah, reach_Qs]
      show (0 : ℤ) ≤ _
      simp only [Prod.fst_add, Prod.smul_fst, vJv, smul_eq_mul, mul_one]
      omega
    · intro b hb k hk
      have hb0 : b = (0 : ℤ × ℤ) := by simpa [Sw] using hb
      subst hb0
      rw [iUnion_Ah, reach_Qs]
      show (0 : ℤ) ≤ _
      simp only [sub_self, add_zero, Prod.fst_add, Prod.smul_fst, vJv,
        smul_eq_mul, mul_one]
      omega
    · rintro z ⟨h1, h2⟩
      rcases le_or_gt (-(ε:ℤ)) z.2 with h | h
      · exact Or.inl ⟨h1, h⟩
      · refine Or.inr ⟨z.1, h1, ?_⟩
        have hz2 : z.2 = -(ε:ℤ) - 1 := by push_cast at h2; omega
        refine Prod.ext ?_ ?_
        · simp [vJv]
        · simp [vJv, hz2]
  rec_p := by
    intro g hg
    rw [iUnion_Ah] at hg ⊢
    obtain ⟨h1, h2⟩ := hg
    refine ⟨?_, ?_⟩
    · show (0:ℤ) ≤ (g + pv).1; simp [pv]; omega
    · show (0:ℤ) ≤ (g + pv).2; simp [pv]; omega
  dot_nJ_p := by simp [dot, nJv, pv]
  vJ_ne := by simp [vJv, Prod.ext_iff]
  vJ_prim := by
    -- `vJv = (1, 0)`, so `Primitive vJv` is `IsCoprime 1 0`.
    show IsCoprime ((1 : ℤ)) ((0 : ℤ))
    exact isCoprime_one_left
  rec_vJ := by
    intro g hg
    rw [iUnion_Ah] at hg ⊢
    obtain ⟨h1, h2⟩ := hg
    refine ⟨?_, ?_⟩
    · show (0:ℤ) ≤ (g + vJv).1; simp [vJv]; omega
    · show (0:ℤ) ≤ (g + vJv).2; simp [vJv]; omega
  cL := 0
  ahat_halfPlane_L := by
    intro g hg
    rw [iUnion_Ah] at hg
    show (0:ℤ) ≤ dot nLv g
    rw [dot_nLv]
    exact hg.1
  ahat_attained_L := by
    refine ⟨((0:ℤ), (0:ℤ)), ?_, ?_⟩
    · rw [iUnion_Ah]; exact ⟨le_refl 0, le_refl 0⟩
    · show dot nLv ((0:ℤ), (0:ℤ)) = 0
      rw [dot_nLv]
  nJ_prim := by
    show IsCoprime (0 : ℤ) (1 : ℤ)
    exact isCoprime_one_right
  nfp_L := by
    rintro ⟨h, h', hdet, ⟨-, hh⟩, ⟨-, hh'⟩⟩
    have key : ∀ q : ℤ × ℤ,
        (∀ g ∈ {z : ℤ × ℤ | (0:ℤ) ≤ dot nLv z},
          g + q ∈ {z : ℤ × ℤ | (0:ℤ) ≤ dot nLv z} → xperC (g + q) = xperC g) →
        q.1 = 0 := by
      intro q hq
      have hm : ∀ w : ℤ × ℤ, (0:ℤ) ≤ w.1 →
          w ∈ {z : ℤ × ℤ | (0:ℤ) ≤ dot nLv z} := by
        intro w hw
        show (0:ℤ) ≤ dot nLv w
        rw [dot_nLv]; exact hw
      have h1 := hm (max 0 (-q.1), 0) (le_max_left _ _)
      have h2 := hm ((max 0 (-q.1), 0) + q) (by
        simp only [Prod.fst_add]
        have := le_max_right (0:ℤ) (-q.1)
        omega)
      have he := hq _ h1 h2
      simp only [xperC, Prod.fst_add] at he
      omega
    exact hdet (by simp [det, key h hh, key h' hh'])

/-! ## 4. The hypotheses of `region_periods_and_rays` -/

theorem hc_grow : ∀ i, cgw.toChainData.B i ⊂ cgw.toChainData.B (i + 1) := by
  intro i
  have hsub : Ah i ⊆ Ah (i + 1) := by
    rintro z ⟨h1, h2, h3, h4⟩
    refine ⟨h1, ?_, h3, ?_⟩ <;> push_cast <;> omega
  have hmem : (((i : ℤ) + 1), (0 : ℤ)) ∈ Ah (i + 1) := by
    refine ⟨?_, ?_, le_refl 0, ?_⟩ <;> push_cast <;> omega
  have hnot : (((i : ℤ) + 1), (0 : ℤ)) ∉ Ah i := by
    rintro ⟨-, h2, -, -⟩
    simp only at h2
    omega
  show Ah i ⊂ Ah (i + 1)
  rw [Set.ssubset_def]
  exact ⟨hsub, fun hc => hnot (hc hmem)⟩

theorem hp_per : pv ∈ Per xperC := by
  show T pv xperC = xperC
  funext z
  simp [T, xperC, pv]

theorem hRconv : IsLatticeConvexRegion (⋃ i, cgw.toChainData.Ahat i) := by
  have hU : (⋃ i, cgw.toChainData.Ahat i) = Qs := iUnion_Ah
  rw [hU]
  refine ⟨{x : ℝ × ℝ | 0 ≤ x.1 ∧ 0 ≤ x.2}, ?_, ?_, ?_⟩
  · intro u hu v hv a b ha hb _
    refine ⟨?_, ?_⟩
    · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      exact add_nonneg (mul_nonneg ha hu.1) (mul_nonneg hb hv.1)
    · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      exact add_nonneg (mul_nonneg ha hu.2) (mul_nonneg hb hv.2)
  · have he : {x : ℝ × ℝ | 0 ≤ x.1 ∧ 0 ≤ x.2}
        = {x : ℝ × ℝ | 0 ≤ x.1} ∩ {x : ℝ × ℝ | 0 ≤ x.2} := rfl
    rw [he]
    exact (isClosed_le continuous_const continuous_fst).inter
      (isClosed_le continuous_const continuous_snd)
  · ext z
    simp only [Qs, Set.mem_preimage, Set.mem_ofPred_eq, toReal]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩

theorem hRne : (⋃ i, cgw.toChainData.Ahat i).Nonempty := by
  refine ⟨((0:ℤ), (0:ℤ)), ?_⟩
  show ((0:ℤ), (0:ℤ)) ∈ ⋃ i, Ah i
  rw [iUnion_Ah]
  exact ⟨le_refl 0, le_refl 0⟩

theorem hagree : ∀ z ∈ ⋃ i, cgw.toChainData.Ahat i,
    thC z = T (((0 : ℕ) : ℤ) • vlv) xperC z := by
  intro z _
  simp [thC, xperC, T]

/-! ## 5. The statement, verbatim, and its refutation -/

def RPRStatement : Prop :=
  ∀ (ξ xper ϑ : Config ℤ) (vl p : ℤ × ℤ) (S : Finset (ℤ × ℤ)) (gen : ℤ × ℤ)
    (cg : ChainDataGeom ξ xper vl p S gen)
    (Sgen : Finset (ℤ × ℤ)), Nivat.Colle.IsGeneratingSet ξ Sgen →
    ∀ (K : ℕ),
      (∀ i, cg.toChainData.B i ⊂ cg.toChainData.B (i + 1)) →
      p ∈ Per xper →
      IsLatticeConvexRegion (⋃ i, cg.toChainData.Ahat i) →
      (⋃ i, cg.toChainData.Ahat i).Nonempty →
      (∀ z ∈ ⋃ i, cg.toChainData.Ahat i, ϑ z = T ((K : ℤ) • vl) xper z) →
      ∃ R : Set (ℤ × ℤ), R ⊆ ⋃ i, cg.toChainData.Ahat i ∧
        IsLatticeConvexRegion R ∧ R.Nonempty ∧
        ∃ h h' z₀ z₀' : ℤ × ℤ, det h h' ≠ 0 ∧
          (∀ k : ℕ, z₀ + (k : ℤ) • h ∈ R) ∧
          (∀ k : ℕ, z₀' + (k : ℤ) • h' ∈ R) ∧
          (∀ z ∈ R, z + h ∈ R → ϑ (z + h) = ϑ z) ∧
          (∀ z ∈ R, z + h' ∈ R → ϑ (z + h') = ϑ z) ∧
          ∃ n : ℕ, 0 < n ∧ h' = (n : ℤ) • cg.vJ

/-- **The 2026-09-17 statement of `region_periods_and_rays` is false.**

The conclusion's `h'`-ray gives `z₀', z₀' + h' ∈ R`, so its `h'`-period clause forces
`ϑ (z₀' + h') = ϑ z₀'`; but `h' = n • v_J = (n, 0)` with `n > 0`, and `ϑ z = z.1`. -/
theorem not_RPRStatement : ¬ RPRStatement := by
  intro H
  obtain ⟨R, -, -, -, h, h', z0, z0', hdet, hray, hray', hper, hper', n, hn, hh'⟩ :=
    H etaC xperC thC vlv pv Sw genw cgw Sgenw isGeneratingSet_etaC 0
      hc_grow hp_per hRconv hRne hagree
  have h0 : z0' ∈ R := by simpa using hray' 0
  have h1 : z0' + h' ∈ R := by simpa using hray' 1
  have hEq := hper' z0' h0 h1
  rw [hh'] at hEq
  have hvJ : cgw.vJ = vJv := rfl
  simp only [thC, hvJ, vJv, Prod.fst_add, Prod.smul_fst, smul_eq_mul, mul_one] at hEq
  omega

end Nivat.ColleStep.PeriodsRays2

