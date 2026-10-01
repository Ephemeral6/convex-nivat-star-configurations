/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.Step_PeriodsRays2
import Nivat.External.Colle.ShellRegion

/-!
# Lattice-convexity of the shells `Â_∞^{(ε)}` is **not** a consequence of `ChainDataGeom`

The sweep hypothesis `hR_region : Colle41.IsRegion R u u'` of `case1_sweep`
(`RegionSteps.lean`) is instantiated in `Claim411.region_of_claim411_of_sweep`
(`RegionClaim411.lean:357`) at `R := cg.toChainData.shellInf ε`, and `IsRegion` opens with
`IsLatticeConvexRegion` (`Lemma41.lean:688`).  Collé asserts (`b3_colle2.txt:440`) that
`Â_∞^{(ε)}` is an `(ℓ, ℓ_J)`-region without proof.  This file settles whether the assertion
follows from the fields of `ChainDataGeom` (`ChainGeom.lean:66-174`).  It does not.

## §1 The level `ε = 0` is exactly `Â_∞`

`ChainDataWithShell.shellInf_zero_eq`: `Â_∞^{(0)} = Â_∞`.  One inclusion is the field
`shellInfZero` (`Lemma35.lean:741`); the other is `t = 0` in the shell formula `shellInf_eq`
(`ChainShell.lean:58`) together with `ahat_halfPlane` (`ChainShell.lean:63`).  Consequently
`IsLatticeConvexRegion (shellInf 0) ↔ IsLatticeConvexRegion (⋃ i, Ahat i)`
(`isLatticeConvexRegion_shellInf_zero_iff`) — at `ε = 0` the question is *literally*
`hRconv`, the hypothesis `region_periods_and_rays` (`RegionSteps.lean`) already takes
separately, and which `region_latticeConvex` (`RegionSteps.lean:1250`) derives only under
`hc_env : c.Env = EnvOf ↑S`.  `ChainDataGeom` itself leaves `Env` abstract.

## §2 A `ChainDataGeom` whose every shell is non-convex

`cgn` below is `Step_PeriodsRays2.cgw` (`Step_PeriodsRays2.lean:233`) with the region bent:

* `Â_∞ = W := {0 ≤ x, 0 ≤ y, (2 ≤ x ∨ 4 ≤ x + y)}` — the closed first quadrant with the
  seven points `x ∈ {0,1}, x + y ≤ 3` removed.  Its rows have left endpoints
  `0, 1, 2, 2, 2` at heights `4, 3, 2, 1, 0` — a *concave* profile, so `(1,2)`, the midpoint
  of `(0,4)` and `(2,0)`, is missing.
* sweep direction `vJ1 = vl = (1,-1)`, `nJ = (0,1)`, `cJ = 0`, `vJ = (1,0)`, `p = (0,1)`.
  `W` is closed under `+(1,0)`, `+(0,1)`, and under `+(1,-1)` as long as `y ≥ 0` — exactly
  what `rec_vJ`, `rec_p` and `shellInfZero` demand.
* `reachSet W (1,-1) = Wr := {(2 ≤ x ∧ 2 ≤ x+y) ∨ (0 ≤ x ∧ 4 ≤ x+y)}` (`reach_W`), so
  `Â_∞^{(ε)} = Wr ∩ {-ε ≤ y}` and `(0,4), (2,0) ∈ Â_∞^{(ε)}`, `(1,2) ∉ Â_∞^{(ε)}` for
  **every** `ε` (`not_isLatticeConvexRegion_shellInf`).
* `A_i = B_i = Â_i := W ∩ {x + y ≤ i + 4}`, finite, and closed under `+(1,-1)` inside
  `{y ≥ 0}`, which is what makes `maximalHat` go through with `Env := fun _ => True`:
  the agreement clause fails exactly at `y < 0` (`etaC` vs `xperC`), so any admissible
  `Tset` lies in `halfStrip (A_i) (1,-1) ∩ {y ≥ 0} = A_i`.
* `η = etaC`, `x_per = xperC`, `S = {0}`, `gen = 0`, and the `ℓ_ι`-normal data
  (`cL = 0`, `nfp_L`) are inherited verbatim from `cgw`, since `p`, `vJ` are unchanged.

`not_forall_isLatticeConvexRegion_shellInf` is the refutation of the universal statement.

## §3 What this does and does not say

* It refutes *"`IsLatticeConvexRegion (cg.toChainData.shellInf ε)` for every
  `ChainDataGeom`"*, at every `ε`, including `ε = 0`; by §1 the `ε = 0` failure is the
  failure of `hRconv`, so any producer of the bundle that also delivers `hRconv` is not
  contradicted by *this* witness.  §3 below then shows that `hRconv` is **not** enough
  either: `cgc` has a lattice-convex `Â_∞` and a non-convex `Â_∞^{(2)}`, because its sweep
  direction has `dot nJ vJ1 = -2`, which `ChainDataGeom.dot_nJ_vJ1_neg` (`ANormal.lean:747`,
  `< 0`) permits, **and** its `Â_∞` has no edge parallel to `vJ1`.  Source check
  (2026-09-19, `b3_colle2.txt`): the step size `|dot nJ vJ1| = |det v_{J-1} v_J|` is *not*
  forced to be `1` — `S_φ` is a zonotope (`:298`) and consecutive generators may have any
  determinant — so `cgc` is faithful on the step.  What the source *does* have and the bundle
  does not record is the **`ℓ_{J-1}`-edge**: the `Â_i` are `E(S_φ)`-enveloped (`:492`,
  Definition 3.2 `:402` demands every edge direction, at least as long as in `S_φ`) and its
  cardinality stabilises (`:504`), so `Â_∞` has an edge parallel to `v_{ℓ_{J-1}}` with `≥ 2`
  lattice points.  Hand-read, not kernel fact: with that edge, every chord of `conv Â_∞`
  parallel to `vJ1` contains a translate of it, hence an integer sweep index, so
  `reachSet = ℤ² ∩ (conv Â_∞ + ℝ₊ vJ1)` and every shell is lattice-convex, for *any* step
  size.  The earlier candidate `hRconv ∧ dot nJ vJ1 = -1` is therefore the wrong repair;
  see §3.
* The witness has `ξ = etaC` of infinite range, so it is not a minimal counterexample;
  `hξ`-carrying statements are untouched, as `Step_PeriodsRays2.lean` already notes.
-/

set_option autoImplicit false

/-! The five general lemmas (`shellInf_zero_eq`, `ahat_subset_shellInf`, `rayIn_shellInf_p`,
`rayIn_shellInf_vJ`, `isRegion_shellInf_iff`) moved 2026-09-19 to `ShellRegion.lean`, which imports
only `ChainGeom` + `Lemma41` and is therefore importable from `RegionSteps.lean`; this file sits
downstream of `RegionSteps` via `Step_PeriodsRays2` and only holds the refutations. -/

namespace Nivat.ShellConvex

open Nivat Nivat.LE2 Nivat.MaxEnv Nivat.Colle Nivat.Colle35 Nivat.ColleStep.PeriodsRays2

/-! ## §2.1 The sets -/

/-- `v_ℓ = v_{ℓ_{J-1}} = (1,-1)`: the sweep direction, pointing out of `{y ≥ 0}`. -/
def vln : ℤ × ℤ := (1, -1)

/-- `Â_∞`: the first quadrant minus the seven points `x ∈ {0,1}`, `x + y ≤ 3`. -/
def W : Set (ℤ × ℤ) := {z | 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ (2 ≤ z.1 ∨ 4 ≤ z.1 + z.2)}

/-- `reachSet W (1,-1)`, computed. -/
def Wr : Set (ℤ × ℤ) :=
  {z | (2 ≤ z.1 ∧ 2 ≤ z.1 + z.2) ∨ (0 ≤ z.1 ∧ 4 ≤ z.1 + z.2)}

/-- `Â_i = A_i = B_i`. -/
def An (i : ℕ) : Set (ℤ × ℤ) :=
  {z | 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ (2 ≤ z.1 ∨ 4 ≤ z.1 + z.2) ∧ z.1 + z.2 ≤ (i : ℤ) + 4}

/-- `Â_i^{(ε)}`. -/
def Shn (i ε : ℕ) : Set (ℤ × ℤ) :=
  {z | ((2 ≤ z.1 ∧ 2 ≤ z.1 + z.2) ∨ (0 ≤ z.1 ∧ 4 ≤ z.1 + z.2)) ∧
    -(ε : ℤ) ≤ z.2 ∧ z.1 + z.2 ≤ (i : ℤ) + 4}

/-- `Â_∞^{(ε)}`. -/
def ShInfn (ε : ℕ) : Set (ℤ × ℤ) :=
  {z | ((2 ≤ z.1 ∧ 2 ≤ z.1 + z.2) ∨ (0 ≤ z.1 ∧ 4 ≤ z.1 + z.2)) ∧ -(ε : ℤ) ≤ z.2}

def Filn (i i₀ ε n : ℕ) : Set (ℤ × ℤ) :=
  match n with
  | 0 => An i ∪ Shn i₀ ε
  | _ + 1 => An i ∪ Shn i₀ ε ∪ Shn i ε

theorem mem_W {z : ℤ × ℤ} : z ∈ W ↔ 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ (2 ≤ z.1 ∨ 4 ≤ z.1 + z.2) := Iff.rfl
theorem mem_Wr {z : ℤ × ℤ} :
    z ∈ Wr ↔ (2 ≤ z.1 ∧ 2 ≤ z.1 + z.2) ∨ (0 ≤ z.1 ∧ 4 ≤ z.1 + z.2) := Iff.rfl
theorem mem_An {i : ℕ} {z : ℤ × ℤ} :
    z ∈ An i ↔ 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ (2 ≤ z.1 ∨ 4 ≤ z.1 + z.2) ∧ z.1 + z.2 ≤ (i : ℤ) + 4 :=
  Iff.rfl
theorem mem_Shn {i ε : ℕ} {z : ℤ × ℤ} :
    z ∈ Shn i ε ↔ ((2 ≤ z.1 ∧ 2 ≤ z.1 + z.2) ∨ (0 ≤ z.1 ∧ 4 ≤ z.1 + z.2)) ∧
      -(ε : ℤ) ≤ z.2 ∧ z.1 + z.2 ≤ (i : ℤ) + 4 := Iff.rfl
theorem mem_ShInfn {ε : ℕ} {z : ℤ × ℤ} :
    z ∈ ShInfn ε ↔ ((2 ≤ z.1 ∧ 2 ≤ z.1 + z.2) ∨ (0 ≤ z.1 ∧ 4 ≤ z.1 + z.2)) ∧
      -(ε : ℤ) ≤ z.2 := Iff.rfl

theorem dot_nJv_mk (a b : ℤ) : dot nJv (a, b) = b := by simp [dot, nJv]
theorem dot_nJv (z : ℤ × ℤ) : dot nJv z = z.2 := by simp [dot, nJv]

theorem iUnion_An : (⋃ i, An i) = W := by
  ext z
  constructor
  · intro hz
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
    exact ⟨hi.1, hi.2.1, hi.2.2.1⟩
  · intro hz
    obtain ⟨h1, h2, h3⟩ := hz
    refine Set.mem_iUnion.mpr ⟨(z.1 + z.2).toNat, h1, h2, h3, ?_⟩
    have h : ((z.1 + z.2).toNat : ℤ) = z.1 + z.2 := Int.toNat_of_nonneg (by omega)
    omega

/-- **The sweep of `W` along `(1,-1)`.** -/
theorem reach_W : reachSet W vln = Wr := by
  ext z
  constructor
  · rintro ⟨g, hg, t, rfl⟩
    obtain ⟨h1, h2, h3⟩ := hg
    rw [mem_Wr]
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, vln, smul_eq_mul,
      mul_one, mul_neg]
    omega
  · intro hz
    rw [mem_Wr] at hz
    rcases le_or_gt 0 z.2 with h | h
    · refine ⟨z, ?_, 0, by simp⟩
      rw [mem_W]
      omega
    · refine ⟨(z.1 + z.2, 0), ?_, (-z.2).toNat, ?_⟩
      · rw [mem_W]
        simp only
        omega
      · have ht : (((-z.2).toNat : ℤ)) = -z.2 := Int.toNat_of_nonneg (by omega)
        refine Prod.ext ?_ ?_
        · simp [vln, ht]
        · simp [vln, ht]

/-- `Â_∞^{(ε)}` is the shell formula of `b3_colle2.txt:440` on `W`. -/
theorem ShInfn_eq_shell (ε : ℕ) : ShInfn ε = MaxEnv.shell W vln nJv 0 ε := by
  rw [shell_eq_reach_inter, reach_W]
  ext z
  simp only [mem_ShInfn, Set.mem_inter_iff, mem_Wr, Set.mem_ofPred_eq, dot_nJv]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩

/-- `Â_i^{(ε)} ⊆ H_{B_i}(ℓ)`: sweep back to height `0` along `-(1,-1)`. -/
theorem strip_mem {i ε : ℕ} {z : ℤ × ℤ} (hz : z ∈ Shn i ε) :
    z + ((0 : ℕ) : ℤ) • vln ∈ Colle35.halfStrip (An i) vln := by
  obtain ⟨h1, h2, h3⟩ := hz
  rcases le_or_gt 0 z.2 with h | h
  · refine ⟨z, ?_, 0, by simp⟩
    rw [mem_An]
    omega
  · refine ⟨(z.1 + z.2, 0), ?_, (-z.2).toNat, ?_⟩
    · rw [mem_An]
      simp only
      omega
    · have ht : (((-z.2).toNat : ℤ)) = -z.2 := Int.toNat_of_nonneg (by omega)
      refine Prod.ext ?_ ?_
      · simp [vln, ht]
      · simp [vln, ht]

/-! ## §2.2 The bundle -/

def cgn : ChainDataGeom etaC xperC vln pv Sw genw where
  Env := fun _ => True
  B := An
  A := An
  u := fun _ => 0
  kk := fun _ => 0
  Ahat := An
  shell := Shn
  shellInf := ShInfn
  envB := fun _ => trivial
  envA := fun _ => trivial
  subBA := fun _ => subset_rfl
  subAB := by
    intro i z hz
    rw [mem_An] at hz ⊢
    push_cast
    omega
  subStrip := fun i => Colle35.subset_halfStrip _ _
  agreeA := by
    intro i z hz
    have hnn : ¬ (z.2 < 0) := by have := hz.2.1; omega
    simp only [etaC, xperC, add_zero, if_neg hnn, add_zero]
  AhatEq := by
    intro i
    ext z
    simp
  AhatMono := by
    intro i j hij z hz
    rw [mem_An] at hz ⊢
    have hc : (i : ℤ) ≤ (j : ℤ) := by exact_mod_cast hij
    omega
  maximalHat := by
    intro i Tset _ _ hstrip hagr z hz
    obtain ⟨b, hb, t, hbt⟩ := hstrip hz
    rw [mem_An] at hb
    have hf : z.1 = b.1 + (t : ℤ) := by
      have h := congrArg Prod.fst hbt
      simp [vln] at h
      omega
    have hs : z.2 = b.2 - (t : ℤ) := by
      have h := congrArg Prod.snd hbt
      simp [vln] at h
      omega
    have hzz : etaC z = xperC z := by simpa using hagr z hz
    have hnn : (0 : ℤ) ≤ z.2 := by
      by_contra hc
      have hc' : z.2 < 0 := not_le.mp hc
      simp only [etaC, xperC] at hzz
      rw [if_pos hc'] at hzz
      omega
    rw [mem_An]
    omega
  shellFinite := by
    intro i ε
    have hfin : ((Set.Icc (0:ℤ) ((i:ℤ) + 4 + (ε:ℤ))) ×ˢ
        (Set.Icc (-(ε:ℤ)) ((i:ℤ) + 4))).Finite :=
      (Set.finite_Icc _ _).prod (Set.finite_Icc _ _)
    refine hfin.subset ?_
    intro z hz
    rw [mem_Shn] at hz
    exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩
  subShell := by
    intro i ε z hz
    rw [mem_An] at hz
    rw [mem_Shn]
    omega
  shellSubInf := by
    intro i ε z hz
    exact ⟨hz.1, hz.2.1⟩
  shellInfZero := by
    intro z hz
    rw [iUnion_An, mem_W]
    obtain ⟨h1, h2⟩ := hz
    have h2' : (0 : ℤ) ≤ z.2 := by simpa using h2
    omega
  -- `I₀`（第 162 轮，`b3_colle2.txt:520`）：本实例的三条 shell 字段都不看 `i` 的下界，取 0。
  I₀ := 0
  shellSubStrip := fun _ _ _ _ _ _ _ hz => strip_mem hz
  shellProper := by
    intro ε _i₀ hε _hEnv i _hi hsub
    have hε' : (1 : ℤ) ≤ (ε : ℤ) := by exact_mod_cast hε
    have hmem : ((3:ℤ), (-1:ℤ)) ∈ Shn i ε := by
      rw [mem_Shn]
      simp only
      omega
    have hcon := hsub hmem
    rw [mem_An] at hcon
    simp only at hcon
    omega
  shellEnv := ⟨1, 0, one_pos, fun _ _ => trivial⟩
  fill := Filn
  fillZero := fun i i₀ ε z hz => hz
  fillStep := by
    intro i i₀ ε n z _
    refine Or.inr ⟨z, (zero_add z).symm, ?_⟩
    intro b hb
    simp [Sw, genw] at hb
  -- Round 80 widened `ChainData.fillCover` (`Lemma35.lean:765`) to `Colle37.GenClosure`;
  -- `genClosure_Sw_all` (`Step_PeriodsRays2.lean:150`) discharges it for `Sw = {0}`.
  fillCover := fun ε i₀ _hε _hEnv i _hi z _ =>
    Nivat.ColleStep.PeriodsRays2.genClosure_Sw_all (An i ∪ Shn i₀ ε) z
  -- ChainDataWithShell (ChainShell.lean:49-63)
  vJ1 := vln
  nJ := nJv
  cJ := 0
  shellInf_eq := by
    intro ε
    rw [iUnion_An]
    exact ShInfn_eq_shell ε
  ahat_nonempty := by
    refine ⟨((0:ℤ), (4:ℤ)), ?_⟩
    rw [iUnion_An, mem_W]
    norm_num
  ahat_halfPlane := by
    intro g hg
    rw [iUnion_An, mem_W] at hg
    rw [dot_nJv]
    exact hg.2.1
  -- ChainDataGeom (ChainGeom.lean:69-193)
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
    refine ⟨((ε:ℤ) + 3, -(ε:ℤ) - 1), 0, ?_, ?_, ?_, ?_⟩
    · rw [dot_nJv_mk]; ring
    · intro k hk
      rw [iUnion_An, reach_W, mem_Wr]
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, vJv, smul_eq_mul,
        mul_one, mul_zero, add_zero]
      omega
    · intro b hb k hk
      have hb0 : b = (0 : ℤ × ℤ) := by simpa [Sw] using hb
      subst hb0
      rw [iUnion_An, reach_W, mem_Wr]
      simp only [sub_self, add_zero, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
        vJv, smul_eq_mul, mul_one, mul_zero]
      omega
    · intro z hz
      rw [mem_ShInfn] at hz
      obtain ⟨h1, h2⟩ := hz
      push_cast at h2
      rcases le_or_gt (-(ε:ℤ)) z.2 with h | h
      · exact Or.inl ⟨h1, h⟩
      · refine Or.inr ⟨z.1 - (ε:ℤ) - 3, by omega, ?_⟩
        have hz2 : z.2 = -(ε:ℤ) - 1 := by omega
        refine Prod.ext ?_ ?_
        · simp [vJv]
        · simp [vJv, hz2]
  rec_p := by
    intro g hg
    rw [iUnion_An, mem_W] at hg ⊢
    simp only [Prod.fst_add, Prod.snd_add, pv]
    omega
  dot_nJ_p := by simp [dot, nJv, pv]
  vJ_ne := by simp [vJv, Prod.ext_iff]
  vJ_prim := by
    show IsCoprime ((1 : ℤ)) ((0 : ℤ))
    exact isCoprime_one_left
  rec_vJ := by
    intro g hg
    rw [iUnion_An, mem_W] at hg ⊢
    simp only [Prod.fst_add, Prod.snd_add, vJv]
    omega
  cL := 0
  ahat_halfPlane_L := by
    intro g hg
    rw [iUnion_An, mem_W] at hg
    show (0:ℤ) ≤ dot nLv g
    rw [dot_nLv]
    exact hg.1
  ahat_attained_L := by
    refine ⟨((0:ℤ), (4:ℤ)), ?_, ?_⟩
    · rw [iUnion_An, mem_W]; norm_num
    · show dot nLv ((0:ℤ), (4:ℤ)) = 0
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

/-! ## §2.3 The refutation -/

theorem mem_04_shellInf (ε : ℕ) : ((0:ℤ), (4:ℤ)) ∈ cgn.toChainData.shellInf ε := by
  show ((0:ℤ), (4:ℤ)) ∈ ShInfn ε
  rw [mem_ShInfn]
  simp only
  omega

theorem mem_20_shellInf (ε : ℕ) : ((2:ℤ), (0:ℤ)) ∈ cgn.toChainData.shellInf ε := by
  show ((2:ℤ), (0:ℤ)) ∈ ShInfn ε
  rw [mem_ShInfn]
  simp only
  omega

theorem not_mem_12_shellInf (ε : ℕ) : ((1:ℤ), (2:ℤ)) ∉ cgn.toChainData.shellInf ε := by
  show ((1:ℤ), (2:ℤ)) ∉ ShInfn ε
  rw [mem_ShInfn]
  simp only
  omega

/-- **No shell of `cgn` is lattice-convex**: `(1,2)` is the midpoint of `(0,4)` and `(2,0)`,
both in `Â_∞^{(ε)}`, and is not. -/
theorem not_isLatticeConvexRegion_shellInf (ε : ℕ) :
    ¬ IsLatticeConvexRegion (cgn.toChainData.shellInf ε) := by
  rintro ⟨C, hconv, -, heq⟩
  have h04 : toReal ((0 : ℤ), (4 : ℤ)) ∈ C := by
    have hm := mem_04_shellInf ε; rw [heq] at hm; exact hm
  have h20 : toReal ((2 : ℤ), (0 : ℤ)) ∈ C := by
    have hm := mem_20_shellInf ε; rw [heq] at hm; exact hm
  have hmid : toReal ((1 : ℤ), (2 : ℤ)) ∈ C := by
    have hA : ((1 : ℝ) / 2) • toReal ((0 : ℤ), (4 : ℤ))
        + ((1 : ℝ) / 2) • toReal ((2 : ℤ), (0 : ℤ)) ∈ C :=
      hconv h04 h20 (by norm_num) (by norm_num) (by norm_num)
    have hAeq : ((1 : ℝ) / 2) • toReal ((0 : ℤ), (4 : ℤ))
        + ((1 : ℝ) / 2) • toReal ((2 : ℤ), (0 : ℤ)) = toReal ((1 : ℤ), (2 : ℤ)) := by
      simp only [toReal, Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk, Prod.mk.injEq]
      norm_num
    rwa [hAeq] at hA
  have hmem : ((1 : ℤ), (2 : ℤ)) ∈ cgn.toChainData.shellInf ε := by rw [heq]; exact hmid
  exact not_mem_12_shellInf ε hmem

/-- The same failure read at `ε = 0`: `Â_∞` itself is not lattice-convex, i.e. `hRconv`
(`RegionSteps.lean`, binder of `region_periods_and_rays`) fails on `cgn`. -/
theorem not_hRconv : ¬ IsLatticeConvexRegion (⋃ i, cgn.toChainData.Ahat i) := by
  rw [← cgn.isLatticeConvexRegion_shellInf_zero_iff]
  exact not_isLatticeConvexRegion_shellInf 0

/-- **The universal statement is false.** -/
theorem not_forall_isLatticeConvexRegion_shellInf :
    ¬ ∀ (ξ xper : Config ℤ) (vl p : ℤ × ℤ) (S : Finset (ℤ × ℤ)) (gen : ℤ × ℤ)
        (cg : ChainDataGeom ξ xper vl p S gen) (ε : ℕ),
        IsLatticeConvexRegion (cg.toChainData.shellInf ε) :=
  fun h => not_isLatticeConvexRegion_shellInf 0 (h _ _ _ _ _ _ cgn 0)

/-- Also false with `0 < ε`, the thickness `shellEnv` actually lives at. -/
theorem not_forall_isLatticeConvexRegion_shellInf_pos :
    ¬ ∀ (ξ xper : Config ℤ) (vl p : ℤ × ℤ) (S : Finset (ℤ × ℤ)) (gen : ℤ × ℤ)
        (cg : ChainDataGeom ξ xper vl p S gen) (ε : ℕ), 0 < ε →
        IsLatticeConvexRegion (cg.toChainData.shellInf ε) :=
  fun h => not_isLatticeConvexRegion_shellInf 1 (h _ _ _ _ _ _ cgn 1 one_pos)

/-! ## §3 `hRconv` does not rescue `ε > 0` when `dot nJ vJ1 = -2`

`cgc` below has `Â_∞ = Kc := {0 ≤ y ∧ 2y ≤ x}`, a lattice-convex cone (`hRconv_cone`), so
by §1 `shellInf 0` is lattice-convex.  The sweep direction is `vl = vJ1 = (1,-2)`, so
`dot nJ vJ1 = -2` — allowed by `ChainDataGeom.dot_nJ_vJ1_neg` (`ANormal.lean:747`), which
only says `< 0`.  Then `reachSet Kc (1,-2)` reaches row `y = -1` only from row `y = 1`
(`x ≥ 2`) shifted by one, i.e. at `x ≥ 3`, but row `y = -2` from row `0` at `x ≥ 1`; so
`(1,-2)` and `(3,0)` lie in `Â_∞^{(2)}` while their midpoint `(2,-1)` does not
(`not_isLatticeConvexRegion_shellInf_cgc_two`).

Hand-read, not kernel fact: `Â_∞^{(1)}` of this witness *is* lattice-convex (its rows
`y = -1, 0, 1, 2, …` start at `x = 3, 0, 2, 4, …`, a convex profile), so the failure is not
"any cut of a non-convex sweep"; it is the parity gap that `|dot nJ vJ1| ≥ 2` opens between
consecutive layers **when `Â_∞` has no edge parallel to `vJ1`** — `Kc`'s `(1,-2)`-support
line meets it only at the vertex `0`.

What the source forces (`b3_colle2.txt`, checked 2026-09-19).  The step size is *not*
forced: `v_{ℓ_{J-1}}` is the predecessor edge direction of `ℓ_J` on `S_φ` (`:424`, `:440`),
`v_ℓ` is merely primitive (`:351`), and `S_φ = conv(-supp φ) ∩ ℤ²` (`:298`) is a zonotope
whose consecutive generators may have any determinant — generators `(1,-2), (1,0)` give
exactly this witness's `vl2`, `vJv`.  So `cgc` is faithful on `dot nJ vJ1 = -2`.  What *is*
forced and unrecorded is the `ℓ_{J-1}`-**edge** of `Â_∞`: each `Â_i` is `E(S_φ)`-enveloped
(`:492`; Definition 3.2, `:402`, demands an edge in every direction of `E(S_φ)`, at least as
long as in `S_φ`), and `|Â_i ∩ w_i(J-1)|` is stabilised across `i` (`:504`), so `Â_∞` has
an edge parallel to `v_{ℓ_{J-1}}` with `≥ 2` lattice points.  Hand-read: with such an edge
every chord of `conv Â_∞` in direction `vJ1` contains a translate of it, so the set of
sweep parameters `{τ ∈ ℝ : z - τ vJ1 ∈ conv Â_∞}` has length `≥ 1` and contains an integer;
hence `reachSet Â_∞ vJ1 = ℤ² ∩ (conv Â_∞ + ℝ₊ vJ1)` and every shell is lattice-convex, at
any step size.  Checked by hand on `Kc' = {y ≥ 0, 2x + y ≥ 0, x - 2y ≥ -5}` (`Kc` with the
edge `(-1,2) → (0,0)` adjoined, step still `2`): `Â_∞^{(0)}, Â_∞^{(1)}, Â_∞^{(2)}` are all
lattice-convex.  So the missing hypothesis is the edge, not `dot nJ vJ1 = -1`; the earlier
conjecture `hRconv ∧ dot nJ vJ1 = -1 ⟹ ∀ ε, IsLatticeConvexRegion (shellInf ε)` is
retracted as the wrong repair (it may still be true, but it is not what Collé has).
Nothing in `ChainDataGeom` records the `ℓ_{J-1}`-edge, and `bottom` is satisfied by `cgc`,
so `bottom` does not force it either. -/

/-- `v_ℓ = v_{ℓ_{J-1}} = (1,-2)`. -/
def vl2 : ℤ × ℤ := (1, -2)
/-- `p = (2,1)`, the other recession direction of the cone. -/
def p2 : ℤ × ℤ := (2, 1)

/-- `Â_∞`: the lattice cone `0 ≤ y`, `2y ≤ x`. -/
def Kc : Set (ℤ × ℤ) := {z | 0 ≤ z.2 ∧ 2 * z.2 ≤ z.1}
/-- `Â_i = A_i = B_i`. -/
def Ac (i : ℕ) : Set (ℤ × ℤ) := {z | 0 ≤ z.2 ∧ 2 * z.2 ≤ z.1 ∧ z.1 + z.2 ≤ (i : ℤ) + 3}
/-- `Â_i^{(ε)}`, by the shell formula. -/
def Shc (i ε : ℕ) : Set (ℤ × ℤ) := MaxEnv.shell (Ac i) vl2 nJv 0 ε
/-- `Â_∞^{(ε)}`, by the shell formula. -/
def ShInfc (ε : ℕ) : Set (ℤ × ℤ) := MaxEnv.shell Kc vl2 nJv 0 ε
def Filc (i i₀ ε n : ℕ) : Set (ℤ × ℤ) :=
  match n with
  | 0 => Ac i ∪ Shc i₀ ε
  | _ + 1 => Ac i ∪ Shc i₀ ε ∪ Shc i ε

theorem mem_Kc {z : ℤ × ℤ} : z ∈ Kc ↔ 0 ≤ z.2 ∧ 2 * z.2 ≤ z.1 := Iff.rfl
theorem mem_Ac {i : ℕ} {z : ℤ × ℤ} :
    z ∈ Ac i ↔ 0 ≤ z.2 ∧ 2 * z.2 ≤ z.1 ∧ z.1 + z.2 ≤ (i : ℤ) + 3 := Iff.rfl

theorem iUnion_Ac : (⋃ i, Ac i) = Kc := by
  ext z
  constructor
  · intro hz
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
    exact ⟨hi.1, hi.2.1⟩
  · intro hz
    obtain ⟨h1, h2⟩ := hz
    refine Set.mem_iUnion.mpr ⟨(z.1 + z.2).toNat, h1, h2, ?_⟩
    have h : ((z.1 + z.2).toNat : ℤ) = z.1 + z.2 := Int.toNat_of_nonneg (by omega)
    omega

/-- Membership in `Â_∞^{(ε)}`, with the sweep parameter `t` exposed to `omega`. -/
theorem mem_ShInfc {ε : ℕ} {z : ℤ × ℤ} :
    z ∈ ShInfc ε ↔ ∃ t : ℕ, 0 ≤ z.2 + 2 * (t : ℤ) ∧ 2 * (z.2 + 2 * (t : ℤ)) ≤ z.1 - (t : ℤ) ∧
      -(ε : ℤ) ≤ z.2 := by
  constructor
  · rintro ⟨g, hg, t, rfl, hd⟩
    rw [mem_Kc] at hg
    rw [dot_nJv] at hd
    refine ⟨t, ?_, ?_, ?_⟩ <;>
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, vl2, smul_eq_mul,
        mul_one, mul_neg] at hd ⊢ <;> omega
  · rintro ⟨t, h1, h2, h3⟩
    refine ⟨(z.1 - (t : ℤ), z.2 + 2 * (t : ℤ)), ⟨h1, h2⟩, t, ?_, ?_⟩
    · refine Prod.ext ?_ ?_
      · simp [vl2]
      · simp [vl2]; ring
    · rw [dot_nJv]; simpa using h3

theorem mem_Shc {i ε : ℕ} {z : ℤ × ℤ} :
    z ∈ Shc i ε ↔ ∃ t : ℕ, 0 ≤ z.2 + 2 * (t : ℤ) ∧ 2 * (z.2 + 2 * (t : ℤ)) ≤ z.1 - (t : ℤ) ∧
      z.1 + z.2 + (t : ℤ) ≤ (i : ℤ) + 3 ∧ -(ε : ℤ) ≤ z.2 := by
  constructor
  · rintro ⟨g, hg, t, rfl, hd⟩
    rw [mem_Ac] at hg
    rw [dot_nJv] at hd
    refine ⟨t, ?_, ?_, ?_, ?_⟩ <;>
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, vl2, smul_eq_mul,
        mul_one, mul_neg] at hd ⊢ <;> omega
  · rintro ⟨t, h1, h2, h3, h4⟩
    refine ⟨(z.1 - (t : ℤ), z.2 + 2 * (t : ℤ)), ⟨h1, h2, by dsimp only; omega⟩, t, ?_, ?_⟩
    · refine Prod.ext ?_ ?_
      · simp [vl2]
      · simp [vl2]; ring
    · rw [dot_nJv]; simpa using h4

/-- The `ℓ_ι`-normal of `ChainGeom.lean:153`, at `p = (2,1)`, `v_J = (1,0)`. -/
def nLc : ℤ × ℤ := det p2 vJv • ((-p2.2, p2.1) : ℤ × ℤ)

theorem nLc_eq : nLc = ((1 : ℤ), (-2 : ℤ)) := by
  simp [nLc, det, p2, vJv]

theorem dot_nLc (z : ℤ × ℤ) : dot nLc z = z.1 - 2 * z.2 := by
  rw [nLc_eq]; simp [dot]; ring

/-- The left endpoint of the new row `y = -(ε+1)` of the sweep: `m/2` for `m = ε + 1` even,
`m/2 + 3` for `m` odd. -/
def Mc (ε : ℕ) : ℤ := ((ε : ℤ) + 1) / 2 + 3 * (((ε : ℤ) + 1) % 2)

def cgc : ChainDataGeom etaC xperC vl2 p2 Sw genw where
  Env := fun _ => True
  B := Ac
  A := Ac
  u := fun _ => 0
  kk := fun _ => 0
  Ahat := Ac
  shell := Shc
  shellInf := ShInfc
  envB := fun _ => trivial
  envA := fun _ => trivial
  subBA := fun _ => subset_rfl
  subAB := by
    intro i z hz
    rw [mem_Ac] at hz ⊢
    push_cast
    omega
  subStrip := fun i => Colle35.subset_halfStrip _ _
  agreeA := by
    intro i z hz
    have hnn : ¬ (z.2 < 0) := by have := hz.1; omega
    simp only [etaC, xperC, add_zero, if_neg hnn, add_zero]
  AhatEq := by
    intro i
    ext z
    simp
  AhatMono := by
    intro i j hij z hz
    rw [mem_Ac] at hz ⊢
    have hc : (i : ℤ) ≤ (j : ℤ) := by exact_mod_cast hij
    omega
  maximalHat := by
    intro i Tset _ _ hstrip hagr z hz
    obtain ⟨b, hb, t, hbt⟩ := hstrip hz
    rw [mem_Ac] at hb
    have hf : z.1 = b.1 + (t : ℤ) := by
      have h := congrArg Prod.fst hbt
      simp [vl2] at h
      omega
    have hs : z.2 = b.2 - 2 * (t : ℤ) := by
      have h := congrArg Prod.snd hbt
      simp [vl2] at h
      omega
    have hzz : etaC z = xperC z := by simpa using hagr z hz
    have hnn : (0 : ℤ) ≤ z.2 := by
      by_contra hc
      have hc' : z.2 < 0 := not_le.mp hc
      simp only [etaC, xperC] at hzz
      rw [if_pos hc'] at hzz
      omega
    rw [mem_Ac]
    omega
  shellFinite := by
    intro i ε
    have hfin : ((Set.Icc (0:ℤ) ((i:ℤ) + 3 + (ε:ℤ))) ×ˢ
        (Set.Icc (-(ε:ℤ)) ((i:ℤ) + 3))).Finite :=
      (Set.finite_Icc _ _).prod (Set.finite_Icc _ _)
    refine hfin.subset ?_
    intro z hz
    obtain ⟨t, h1, h2, h3, h4⟩ := mem_Shc.mp hz
    exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩
  subShell := by
    intro i ε z hz
    rw [mem_Ac] at hz
    exact mem_Shc.mpr ⟨0, by omega, by omega, by omega, by omega⟩
  shellSubInf := by
    intro i ε z hz
    obtain ⟨t, h1, h2, -, h4⟩ := mem_Shc.mp hz
    exact mem_ShInfc.mpr ⟨t, h1, h2, h4⟩
  shellInfZero := by
    intro z hz
    obtain ⟨t, h1, h2, h3⟩ := mem_ShInfc.mp hz
    rw [iUnion_Ac, mem_Kc]
    push_cast at h3
    omega
  -- `I₀`（第 162 轮，`b3_colle2.txt:520`）：本实例的三条 shell 字段都不看 `i` 的下界，取 0。
  I₀ := 0
  shellSubStrip := by
    intro ε _ _ _ i _ z hz
    obtain ⟨g, hg, t, rfl, -⟩ := hz
    exact ⟨g, hg, t, by simp⟩
  shellProper := by
    intro ε _i₀ hε _hEnv i _hi hsub
    have hε' : (1 : ℤ) ≤ (ε : ℤ) := by exact_mod_cast hε
    have hmem : ((3:ℤ), (-1:ℤ)) ∈ Shc i ε :=
      mem_Shc.mpr ⟨1, by norm_num, by norm_num, by push_cast; omega, by omega⟩
    have hcon := hsub hmem
    rw [mem_Ac] at hcon
    simp only at hcon
    omega
  shellEnv := ⟨1, 0, one_pos, fun _ _ => trivial⟩
  fill := Filc
  fillZero := fun i i₀ ε z hz => hz
  fillStep := by
    intro i i₀ ε n z _
    refine Or.inr ⟨z, (zero_add z).symm, ?_⟩
    intro b hb
    simp [Sw, genw] at hb
  -- Round 80 widened `ChainData.fillCover` (`Lemma35.lean:765`) to `Colle37.GenClosure`;
  -- `genClosure_Sw_all` (`Step_PeriodsRays2.lean:150`) discharges it for `Sw = {0}`.
  fillCover := fun ε i₀ _hε _hEnv i _hi z _ =>
    Nivat.ColleStep.PeriodsRays2.genClosure_Sw_all (Ac i ∪ Shc i₀ ε) z
  -- ChainDataWithShell (ChainShell.lean:49-63)
  vJ1 := vl2
  nJ := nJv
  cJ := 0
  shellInf_eq := by
    intro ε
    rw [iUnion_Ac]
    rfl
  ahat_nonempty := by
    refine ⟨((0:ℤ), (0:ℤ)), ?_⟩
    rw [iUnion_Ac, mem_Kc]
    norm_num
  ahat_halfPlane := by
    intro g hg
    rw [iUnion_Ac, mem_Kc] at hg
    rw [dot_nJv]
    exact hg.1
  -- ChainDataGeom (ChainGeom.lean:69-193)
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
    have hreach : ∀ k : ℤ, 0 ≤ k →
        (Mc ε, -(ε:ℤ) - 1) + k • vJv ∈ reachSet Kc vl2 := by
      intro k hk
      refine ⟨(Mc ε + k - (((ε + 2) / 2 : ℕ) : ℤ), -(ε:ℤ) - 1 + 2 * (((ε + 2) / 2 : ℕ) : ℤ)),
        ?_, (ε + 2) / 2, ?_⟩
      · rw [mem_Kc]
        simp only [Mc]
        omega
      · refine Prod.ext ?_ ?_
        · simp [vJv, vl2]
        · simp [vJv, vl2]; ring
    refine ⟨(Mc ε, -(ε:ℤ) - 1), 0, ?_, ?_, ?_, ?_⟩
    · rw [dot_nJv_mk]; ring
    · intro k hk
      rw [iUnion_Ac]
      exact hreach k hk
    · intro b hb k hk
      have hb0 : b = (0 : ℤ × ℤ) := by simpa [Sw] using hb
      subst hb0
      rw [iUnion_Ac, sub_self, add_zero]
      exact hreach k hk
    · intro z hz
      obtain ⟨t, h1, h2, h3⟩ := mem_ShInfc.mp hz
      push_cast at h3
      rcases le_or_gt (-(ε:ℤ)) z.2 with h | h
      · exact Or.inl (mem_ShInfc.mpr ⟨t, h1, h2, h⟩)
      · have hz2 : z.2 = -(ε:ℤ) - 1 := by omega
        have hM : Mc ε ≤ z.1 := by
          simp only [Mc]
          omega
        refine Or.inr ⟨z.1 - Mc ε, by omega, ?_⟩
        refine Prod.ext ?_ ?_
        · simp [vJv]
        · simp [vJv, hz2]
  rec_p := by
    intro g hg
    rw [iUnion_Ac, mem_Kc] at hg ⊢
    simp only [Prod.fst_add, Prod.snd_add, p2]
    omega
  dot_nJ_p := by simp [dot, nJv, p2]
  vJ_ne := by simp [vJv, Prod.ext_iff]
  vJ_prim := by
    show IsCoprime ((1 : ℤ)) ((0 : ℤ))
    exact isCoprime_one_left
  rec_vJ := by
    intro g hg
    rw [iUnion_Ac, mem_Kc] at hg ⊢
    simp only [Prod.fst_add, Prod.snd_add, vJv]
    omega
  cL := 0
  ahat_halfPlane_L := by
    intro g hg
    rw [iUnion_Ac, mem_Kc] at hg
    show (0:ℤ) ≤ dot nLc g
    rw [dot_nLc]
    omega
  ahat_attained_L := by
    refine ⟨((0:ℤ), (0:ℤ)), ?_, ?_⟩
    · rw [iUnion_Ac, mem_Kc]; norm_num
    · show dot nLc ((0:ℤ), (0:ℤ)) = 0
      rw [dot_nLc]; norm_num
  nJ_prim := by
    show IsCoprime (0 : ℤ) (1 : ℤ)
    exact isCoprime_one_right
  nfp_L := by
    rintro ⟨h, h', hdet, ⟨-, hh⟩, ⟨-, hh'⟩⟩
    have key : ∀ q : ℤ × ℤ,
        (∀ g ∈ {z : ℤ × ℤ | (0:ℤ) ≤ dot nLc z},
          g + q ∈ {z : ℤ × ℤ | (0:ℤ) ≤ dot nLc z} → xperC (g + q) = xperC g) →
        q.1 = 0 := by
      intro q hq
      have hm : ∀ w : ℤ × ℤ, (0:ℤ) ≤ w.1 - 2 * w.2 →
          w ∈ {z : ℤ × ℤ | (0:ℤ) ≤ dot nLc z} := by
        intro w hw
        show (0:ℤ) ≤ dot nLc w
        rw [dot_nLc]; exact hw
      have h1 := hm (max 0 (2 * q.2 - q.1), 0) (by simp only [mul_zero, sub_zero]; exact le_max_left _ _)
      have h2 := hm ((max 0 (2 * q.2 - q.1), 0) + q) (by
        simp only [Prod.fst_add, Prod.snd_add, zero_add]
        have := le_max_right (0:ℤ) (2 * q.2 - q.1)
        omega)
      have he := hq _ h1 h2
      simp only [xperC, Prod.fst_add] at he
      omega
    exact hdet (by simp [det, key h hh, key h' hh'])

/-- `hRconv` holds for `cgc`: the cone `Kc` is lattice-convex. -/
theorem hRconv_cone : IsLatticeConvexRegion (⋃ i, cgc.toChainData.Ahat i) := by
  have hU : (⋃ i, cgc.toChainData.Ahat i) = Kc := iUnion_Ac
  rw [hU]
  refine ⟨{x : ℝ × ℝ | 0 ≤ x.2 ∧ 2 * x.2 ≤ x.1}, ?_, ?_, ?_⟩
  · intro u hu v hv a b ha hb _
    refine ⟨?_, ?_⟩
    · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      exact add_nonneg (mul_nonneg ha hu.1) (mul_nonneg hb hv.1)
    · simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      have h1 := mul_le_mul_of_nonneg_left hu.2 ha
      have h2 := mul_le_mul_of_nonneg_left hv.2 hb
      linarith
  · have he : {x : ℝ × ℝ | 0 ≤ x.2 ∧ 2 * x.2 ≤ x.1}
        = {x : ℝ × ℝ | 0 ≤ x.2} ∩ {x : ℝ × ℝ | 2 * x.2 ≤ x.1} := rfl
    rw [he]
    exact (isClosed_le continuous_const continuous_snd).inter
      (isClosed_le (continuous_const.mul continuous_snd) continuous_fst)
  · ext z
    simp only [Kc, Set.mem_preimage, Set.mem_ofPred_eq, toReal]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩

theorem mem_1m2_shellInf_cgc_two : ((1:ℤ), (-2:ℤ)) ∈ cgc.toChainData.shellInf 2 :=
  mem_ShInfc.mpr ⟨1, by norm_num, by norm_num, by norm_num⟩

theorem mem_30_shellInf_cgc_two : ((3:ℤ), (0:ℤ)) ∈ cgc.toChainData.shellInf 2 :=
  mem_ShInfc.mpr ⟨0, by norm_num, by norm_num, by norm_num⟩

theorem not_mem_2m1_shellInf_cgc_two : ((2:ℤ), (-1:ℤ)) ∉ cgc.toChainData.shellInf 2 := by
  intro h
  obtain ⟨t, h1, h2, -⟩ := mem_ShInfc.mp h
  simp only at h1 h2
  omega

/-- **With `hRconv` true, `Â_∞^{(2)}` is still not lattice-convex**: `(2,-1)` is the midpoint
of `(1,-2)` and `(3,0)`. -/
theorem not_isLatticeConvexRegion_shellInf_cgc_two :
    ¬ IsLatticeConvexRegion (cgc.toChainData.shellInf 2) := by
  rintro ⟨C, hconv, -, heq⟩
  have hA : toReal ((1 : ℤ), (-2 : ℤ)) ∈ C := by
    have hm := mem_1m2_shellInf_cgc_two; rw [heq] at hm; exact hm
  have hB : toReal ((3 : ℤ), (0 : ℤ)) ∈ C := by
    have hm := mem_30_shellInf_cgc_two; rw [heq] at hm; exact hm
  have hmid : toReal ((2 : ℤ), (-1 : ℤ)) ∈ C := by
    have hM : ((1 : ℝ) / 2) • toReal ((1 : ℤ), (-2 : ℤ))
        + ((1 : ℝ) / 2) • toReal ((3 : ℤ), (0 : ℤ)) ∈ C :=
      hconv hA hB (by norm_num) (by norm_num) (by norm_num)
    have hMeq : ((1 : ℝ) / 2) • toReal ((1 : ℤ), (-2 : ℤ))
        + ((1 : ℝ) / 2) • toReal ((3 : ℤ), (0 : ℤ)) = toReal ((2 : ℤ), (-1 : ℤ)) := by
      simp only [toReal, Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk, Prod.mk.injEq]
      norm_num
    rwa [hMeq] at hM
  have hmem : ((2 : ℤ), (-1 : ℤ)) ∈ cgc.toChainData.shellInf 2 := by rw [heq]; exact hmid
  exact not_mem_2m1_shellInf_cgc_two hmem

/-- **`hRconv` is not the missing hypothesis.**  Even granting lattice-convexity of `Â_∞`,
the shells of a `ChainDataGeom` need not be lattice-convex. -/
theorem not_forall_isLatticeConvexRegion_shellInf_of_hRconv :
    ¬ ∀ (ξ xper : Config ℤ) (vl p : ℤ × ℤ) (S : Finset (ℤ × ℤ)) (gen : ℤ × ℤ)
        (cg : ChainDataGeom ξ xper vl p S gen),
        IsLatticeConvexRegion (⋃ i, cg.toChainData.Ahat i) →
        ∀ ε : ℕ, IsLatticeConvexRegion (cg.toChainData.shellInf ε) :=
  fun h => not_isLatticeConvexRegion_shellInf_cgc_two (h _ _ _ _ _ _ cgc hRconv_cone 2)

/-- The sign datum of the second witness, for the record: `dot nJ vJ1 = -2`. -/
theorem cgc_dot_nJ_vJ1 : dot cgc.nJ cgc.vJ1 = -2 := by
  show dot nJv vl2 = -2
  simp [dot, nJv, vl2]

/-- **`hR_region` of `case1_sweep` at `R := shellInf ε` is not a theorem of the bundle**, even
with `hRconv`: both rays are free (`isRegion_shellInf_iff`), the convexity conjunct is not. -/
theorem not_isRegion_shellInf_cgc_two :
    ¬ Colle41.IsRegion (cgc.toChainData.shellInf 2) p2 cgc.vJ := by
  rw [cgc.isRegion_shellInf_iff]
  exact not_isLatticeConvexRegion_shellInf_cgc_two

end Nivat.ShellConvex

#print axioms Nivat.ShellConvex.reach_W
#print axioms Nivat.ShellConvex.cgn
#print axioms Nivat.ShellConvex.not_isLatticeConvexRegion_shellInf
#print axioms Nivat.ShellConvex.not_hRconv
#print axioms Nivat.ShellConvex.not_forall_isLatticeConvexRegion_shellInf
#print axioms Nivat.ShellConvex.not_forall_isLatticeConvexRegion_shellInf_pos
#print axioms Nivat.ShellConvex.cgc
#print axioms Nivat.ShellConvex.hRconv_cone
#print axioms Nivat.ShellConvex.not_isLatticeConvexRegion_shellInf_cgc_two
#print axioms Nivat.ShellConvex.not_forall_isLatticeConvexRegion_shellInf_of_hRconv
#print axioms Nivat.ShellConvex.cgc_dot_nJ_vJ1
#print axioms Nivat.ShellConvex.not_isRegion_shellInf_cgc_two
