/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.LatticeEdges

/-!
# `convex_forces_mem` is FALSE, and so is the finite window it was meant to build

This file refutes, at kernel level, the step

> `T` lattice-convex, `B ⊆ T ⊆ H_B(ℓ)`, `g ∈ H_B(ℓ)`, and `T` contains a point that
> overshoots `g` along `ℓ`  ⟹  `g ∈ T`

which was proposed as the route to the finite window `W` needed by
`ChainData.maximalHat` (via `Nivat.MaxEnv.exists_maximal_chainFamily`).

The informal argument was: *the half-strip is bounded transversally, so a lattice-convex
`T` that runs far along `ℓ` must fill the strip and swallow `g`.*  That is wrong.  A
lattice-convex set may run arbitrarily far along `ℓ` inside a width-1 strip as a **thin
wedge** that hugs one side of the strip, and a wedge can miss `g` forever.

`wedge N = {(0,0)} ∪ {(t,1) : 0 ≤ t ≤ N}` is lattice-convex (witness: the triangle with
vertices `(0,0)`, `(0,1)`, `(N,1)`), sits between `B = {(0,0),(0,1)}` and `H_B((1,0))`,
reaches `(N,1)`, and never contains `(5,0)`.

Two consequences, both proved below:

* `convex_forces_mem_false` — the implication itself is false.
* `no_finite_window` — the *goal* is false too, not just the proof: the family of
  lattice-convex sets sandwiched between `B` and `H_B(ℓ)` and avoiding `g` has unbounded
  diameter, so no finite `W` contains it.

## Diagnosis

The wedge's slanted edge has outer normal `(1, -N)`, which **depends on `N`**.  The
statement is repaired by pinning the edge normals, i.e. by adding the envelopedness
hypothesis `E T = E U` for a fixed finite `E U`: with the slant directions fixed, the
front edge can only shift the reach along `ℓ` by a bounded amount.

This is the failure mode CLAUDE.md already documents for
`isLatticeConvexRegion_iUnion_of_mono`: dropping the fixed-edge-direction data makes the
statement false, and the repair is to put that data back
(`isLatticeConvexRegion_iUnion_of_mono_fixedEdges_finite`, `LatticeEdges.lean:1592`).

Nothing here is assumed; no `sorry`, no local `axiom`.
-/

namespace Nivat.ConvexForcesRefuted

open Nivat.LE2

/-! ## §1. The wedge -/

/-- `wedge N` = the lattice points of the triangle with vertices `(0,0)`, `(0,1)`,
`(N,1)`.  For `1 ≤ N` this is `{(0,0)} ∪ {(t,1) : 0 ≤ t ≤ N}`. -/
def wedge (N : ℤ) : Set (ℤ × ℤ) :=
  {z | 0 ≤ z.1 ∧ z.2 ≤ 1 ∧ z.1 ≤ N * z.2}

/-- The real triangle cutting out `wedge N`. -/
def wedgeC (N : ℤ) : Set (ℝ × ℝ) :=
  {p | 0 ≤ p.1 ∧ p.2 ≤ 1 ∧ p.1 ≤ (N : ℝ) * p.2}

/-- `B = {(0,0), (0,1)}`, the transversal cross-section of the strip. -/
def Bbase : Set (ℤ × ℤ) := {z | z.1 = 0 ∧ 0 ≤ z.2 ∧ z.2 ≤ 1}

theorem mem_wedge {N : ℤ} {z : ℤ × ℤ} :
    z ∈ wedge N ↔ 0 ≤ z.1 ∧ z.2 ≤ 1 ∧ z.1 ≤ N * z.2 := Iff.rfl

theorem mem_Bbase {z : ℤ × ℤ} : z ∈ Bbase ↔ z.1 = 0 ∧ 0 ≤ z.2 ∧ z.2 ≤ 1 := Iff.rfl

theorem wedgeC_convex (N : ℤ) : Convex ℝ (wedgeC N) := by
  rintro x ⟨hx1, hx2, hx3⟩ y ⟨hy1, hy2, hy3⟩ a b ha hb hab
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  · nlinarith
  · nlinarith
  · nlinarith

theorem wedgeC_closed (N : ℤ) : IsClosed (wedgeC N) := by
  have h1 : IsClosed {p : ℝ × ℝ | 0 ≤ p.1} := isClosed_le continuous_const continuous_fst
  have h2 : IsClosed {p : ℝ × ℝ | p.2 ≤ 1} := isClosed_le continuous_snd continuous_const
  have h3 : IsClosed {p : ℝ × ℝ | p.1 ≤ (N : ℝ) * p.2} :=
    isClosed_le continuous_fst (continuous_const.mul continuous_snd)
  exact h1.inter (h2.inter h3)

theorem wedge_eq_preimage (N : ℤ) : wedge N = Nivat.toReal ⁻¹' wedgeC N := by
  ext z
  simp only [mem_wedge, wedgeC, Nivat.toReal, Set.mem_preimage, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨by exact_mod_cast h1, by exact_mod_cast h2, ?_⟩
    have : ((z.1 : ℝ)) ≤ ((N * z.2 : ℤ) : ℝ) := by exact_mod_cast h3
    push_cast at this
    exact this
  · rintro ⟨h1, h2, h3⟩
    refine ⟨by exact_mod_cast h1, by exact_mod_cast h2, ?_⟩
    have : ((z.1 : ℝ)) ≤ ((N * z.2 : ℤ) : ℝ) := by push_cast; exact h3
    exact_mod_cast this

theorem wedge_latticeConvex (N : ℤ) : Nivat.IsLatticeConvexRegion (wedge N) :=
  ⟨wedgeC N, wedgeC_convex N, wedgeC_closed N, wedge_eq_preimage N⟩

/-! ## §2. The wedge satisfies every hypothesis -/

/-- For `1 ≤ N` the wedge stays in the upper half: the slanted edge pins `0 ≤ z.2`. -/
theorem wedge_snd_nonneg {N : ℤ} (hN : 1 ≤ N) {z : ℤ × ℤ} (hz : z ∈ wedge N) : 0 ≤ z.2 := by
  obtain ⟨h1, -, h3⟩ := hz
  by_contra hc
  have h4 : N * z.2 ≤ N * (-1) := mul_le_mul_of_nonneg_left (by omega) (by omega)
  rw [mul_neg_one] at h4
  linarith

theorem Bbase_subset_wedge {N : ℤ} (hN : 1 ≤ N) : Bbase ⊆ wedge N := by
  rintro z ⟨h1, h2, h3⟩
  exact ⟨by omega, h3, by rw [h1]; exact mul_nonneg (by omega) h2⟩

theorem wedge_subset_halfStrip {N : ℤ} (hN : 1 ≤ N) :
    wedge N ⊆ halfStrip Bbase ((1 : ℤ), (0 : ℤ)) := by
  intro z hz
  have hz2 : 0 ≤ z.2 := wedge_snd_nonneg hN hz
  obtain ⟨h1, h2, -⟩ := hz
  -- `z = (0, z.2) + z.1 • (1,0)`, and `(0, z.2) ∈ Bbase` because `0 ≤ z.2 ≤ 1`.
  refine ⟨(0, z.2), ⟨rfl, hz2, h2⟩, z.1.toNat, ?_⟩
  rw [Int.toNat_of_nonneg h1]
  simp

/-- The point `(5,0)` lies in the strip: it is `(0,0) + 5•(1,0)`. -/
theorem g_mem_halfStrip :
    ((5 : ℤ), (0 : ℤ)) ∈ halfStrip Bbase ((1 : ℤ), (0 : ℤ)) :=
  ⟨(0, 0), ⟨rfl, le_refl _, by norm_num⟩, 5, by norm_num [Prod.ext_iff]⟩

/-- …but it is in no wedge. -/
theorem g_notMem_wedge (N : ℤ) : ((5 : ℤ), (0 : ℤ)) ∉ wedge N := by
  rintro ⟨-, -, h3⟩
  simp only [mul_zero] at h3
  omega

/-- The wedge reaches arbitrarily far along `(1,0)`. -/
theorem far_mem_wedge {N : ℤ} (hN : 1 ≤ N) : (N, (1 : ℤ)) ∈ wedge N :=
  ⟨by omega, le_refl _, by simp⟩

theorem Bbase_finite : Bbase.Finite := by
  have : Bbase = (fun t : ℤ => ((0 : ℤ), t)) '' {t : ℤ | 0 ≤ t ∧ t ≤ 1} := by
    ext z
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨z.2, ⟨h2, h3⟩, by simp [Prod.ext_iff, h1]⟩
    · rintro ⟨t, ⟨ht1, ht2⟩, rfl⟩
      exact ⟨rfl, ht1, ht2⟩
  rw [this]
  exact Set.Finite.image _ (Set.finite_Icc (0 : ℤ) 1)

theorem Bbase_latticeConvex : Nivat.IsLatticeConvexRegion Bbase := by
  refine ⟨{p : ℝ × ℝ | p.1 = 0 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1}, ?_, ?_, ?_⟩
  · rintro x ⟨hx1, hx2, hx3⟩ y ⟨hy1, hy2, hy3⟩ a b ha hb hab
    refine ⟨?_, ?_, ?_⟩ <;>
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    · rw [hx1, hy1]; ring
    · nlinarith
    · nlinarith
  · exact (isClosed_eq continuous_fst continuous_const).inter
      ((isClosed_le continuous_const continuous_snd).inter
        (isClosed_le continuous_snd continuous_const))
  · ext z
    simp only [mem_Bbase, Nivat.toReal, Set.mem_preimage, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨by exact_mod_cast h1, by exact_mod_cast h2, by exact_mod_cast h3⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨by exact_mod_cast h1, by exact_mod_cast h2, by exact_mod_cast h3⟩

/-! ## §3. The refutations -/

/-- **The proposed step is false.**  Every hypothesis that was offered is included here —
`B` finite and itself lattice-convex, `v` and `n` primitive, `n` positively paired with
the sweep direction `v` — and the conclusion still fails. -/
theorem convex_forces_mem_false :
    ¬ ∀ (B T : Set (ℤ × ℤ)) (v n g z : ℤ × ℤ),
        B.Finite → Nivat.IsLatticeConvexRegion B →
        Prim v → Prim n → 0 < dot n v →
        Nivat.IsLatticeConvexRegion T →
        B ⊆ T → T ⊆ halfStrip B v →
        g ∈ halfStrip B v →
        z ∈ T → dot n g < dot n z →
        g ∈ T := by
  intro h
  refine g_notMem_wedge 10 (h Bbase (wedge 10) (1, 0) (1, 0) (5, 0) (10, 1)
    Bbase_finite Bbase_latticeConvex
    (by decide : Int.gcd (1 : ℤ) (0 : ℤ) = 1) (by decide : Int.gcd (1 : ℤ) (0 : ℤ) = 1)
    (by simp [dot])
    (wedge_latticeConvex 10) (Bbase_subset_wedge (by norm_num))
    (wedge_subset_halfStrip (by norm_num)) g_mem_halfStrip
    (far_mem_wedge (by norm_num)) (by simp [dot]))

/-- **The goal is false too, not merely the proof.**  For every bound `k` the family of
lattice-convex sets sandwiched between `Bbase` and `H_Bbase((1,0))` that avoid `(5,0)`
contains a member reaching past `k` along `(1,0)`. -/
theorem unbounded_family (k : ℤ) :
    ∃ T : Set (ℤ × ℤ),
      Nivat.IsLatticeConvexRegion T ∧
      Bbase ⊆ T ∧ T ⊆ halfStrip Bbase ((1 : ℤ), (0 : ℤ)) ∧
      ((5 : ℤ), (0 : ℤ)) ∉ T ∧
      ∃ z ∈ T, k < dot ((1 : ℤ), (0 : ℤ)) z := by
  refine ⟨wedge (max k 0 + 1), wedge_latticeConvex _, Bbase_subset_wedge (by omega),
    wedge_subset_halfStrip (by omega), g_notMem_wedge _,
    (max k 0 + 1, 1), far_mem_wedge (by omega), ?_⟩
  simp only [dot]
  omega

/-- **No finite window.**  There is no finite `W` containing every lattice-convex `T`
sandwiched between `Bbase` and the strip and avoiding `(5,0)`.  So
`Nivat.MaxEnv.exists_maximal_chainFamily` cannot be applied to this family, and the
half-strip truncation argument cannot supply its `hW`. -/
theorem no_finite_window (W : Set (ℤ × ℤ)) (hW : W.Finite) :
    ¬ ∀ T : Set (ℤ × ℤ),
        Nivat.IsLatticeConvexRegion T → Bbase ⊆ T →
        T ⊆ halfStrip Bbase ((1 : ℤ), (0 : ℤ)) →
        ((5 : ℤ), (0 : ℤ)) ∉ T → T ⊆ W := by
  intro h
  obtain ⟨k, hk⟩ := (hW.image (fun z => dot ((1 : ℤ), (0 : ℤ)) z)).bddAbove
  obtain ⟨T, hconv, hB, hstrip, hg, z, hzT, hzk⟩ := unbounded_family k
  have hle : dot ((1 : ℤ), (0 : ℤ)) z ≤ k := hk ⟨z, h T hconv hB hstrip hg hzT, rfl⟩
  omega

/-! ## §4. The diagnosis, kernel-backed

The wedge escapes because its slanted front edge has outer normal `(1, -N)`, which
**depends on `N`**.  Envelopedness pins the edge normals to the fixed finite set `E U`,
so no single `U` can admit the whole family. -/

/-- The slanted edge of `wedge N` has outer normal `(1,-N)`: the face is `{(0,0),(N,1)}`. -/
theorem slant_mem_E {N : ℤ} (hN : 1 ≤ N) : ((1 : ℤ), -N) ∈ E (wedge N) := by
  have hzero : ∀ y ∈ wedge N, dot ((1 : ℤ), -N) y ≤ 0 := by
    rintro y ⟨-, -, h3⟩
    show (1 : ℤ) * y.1 + (-N) * y.2 ≤ 0
    linarith
  have horigin : ((0 : ℤ), (0 : ℤ)) ∈ face (wedge N) ((1 : ℤ), -N) := by
    refine ⟨⟨le_refl _, by norm_num, by simp⟩, fun y hy => ?_⟩
    have h0 : dot ((1 : ℤ), -N) ((0 : ℤ), (0 : ℤ)) = 0 := by
      show (1 : ℤ) * 0 + (-N) * 0 = 0
      ring
    rw [h0]
    exact hzero y hy
  have hfar : (N, (1 : ℤ)) ∈ face (wedge N) ((1 : ℤ), -N) := by
    refine ⟨far_mem_wedge hN, fun y hy => ?_⟩
    have h0 : dot ((1 : ℤ), -N) (N, (1 : ℤ)) = 0 := by
      show (1 : ℤ) * N + (-N) * 1 = 0
      ring
    rw [h0]
    exact hzero y hy
  refine ⟨?_, ⟨(0, 0), horigin, (N, 1), hfar, ?_⟩⟩
  · show Int.gcd (1 : ℤ) (-N) = 1
    simp
  · simp only [ne_eq, Prod.mk.injEq, not_and]
    omega

/-- **No fixed `U` envelopes the whole family.**  `Enveloped U T` forces `E T ⊆ E U`, but
`E (wedge N)` contains the `N`-dependent normal `(1,-N)`, so `E U` would have to be
infinite.  This is exactly the hypothesis the refuted step was missing. -/
theorem no_single_envelope {U : Set (ℤ × ℤ)} (hU : (E U).Finite) :
    ¬ ∀ N : ℤ, 1 ≤ N → Enveloped U (wedge N) := by
  intro h
  have hsub : (fun N : ℤ => ((1 : ℤ), -N)) '' {N : ℤ | 1 ≤ N} ⊆ E U := by
    rintro _ ⟨N, hN, rfl⟩
    exact (h N hN).1.E_subset (slant_mem_E hN)
  have hinj : Set.InjOn (fun N : ℤ => ((1 : ℤ), -N)) {N : ℤ | 1 ≤ N} := by
    intro a _ b _ hab
    simp only [Prod.mk.injEq, neg_inj] at hab
    exact hab.2
  have hfinN : {N : ℤ | 1 ≤ N}.Finite := Set.Finite.of_finite_image (hU.subset hsub) hinj
  obtain ⟨k, hk⟩ := hfinN.bddAbove
  have hmem : max k 0 + 1 ∈ {N : ℤ | 1 ≤ N} := by
    have := le_max_right k 0
    simp only [Set.mem_ofPred_eq]
    omega
  have hle : max k 0 + 1 ≤ k := hk hmem
  have := le_max_left k 0
  omega

#print axioms convex_forces_mem_false
#print axioms unbounded_family
#print axioms no_finite_window
#print axioms slant_mem_E
#print axioms no_single_envelope

end Nivat.ConvexForcesRefuted
