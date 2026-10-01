/-
Copyright (c) 2026. Released under Apache 2.0 license.
Authors: lane-cd-substrip (§1), lane-chaindata-lead (§2)
-/
import Nivat.External.Colle.LatticeEdges
import Nivat.Section8.HalfPlane

/-!
# Points between two parallel rays of a lattice-convex region

Consumer: the `hstrip` hypothesis of `hseedS_of_parts` (`tmp/wip/lane-cd-bottom.lean`), which
discharges the `hseedS` half of the `bottom` binder of
`Nivat.Colle35.ChainDataGeom.ofPartsExhaustsInter` (`ChainExhaustInter.lean`).

A lattice-convex region `T` containing two `vJ`-parallel rays, one at `dot nJ`-level
`dot nJ g` and one at level `dot nJ q`, eventually contains the `vJ`-ray out of any `y` whose
level lies between the two.  "Eventually" is essential and not a weakness of the proof: the
convex hull argument places `y` past both rays' base points only for large enough parameter,
and the sharp integer threshold is strictly worse than the real one (see the numeric instance
below).  `hseedS_of_parts` only ever needs eventual membership, so `∃ L, ∀ k ≥ L` is the right
conclusion.

Extracted from `tmp/wip/lane-cd-substrip.lean` §10 (lane `lane-cd-substrip`, 2026-09-23,
EXIT=0 and axiom-clean there and again here).  `IsLatticeConvexRegion` here is
`Nivat.IsLatticeConvexRegion` (`Section8/HalfPlane.lean:174`) — the only definition of that
name in the tree; `AEnv.lean:83` merely quotes it inside a docstring.

## 硬规矩 6 numeric check (worked by hand before the Lean proof)

Take `T := {z : ℤ × ℤ | 0 ≤ z.1 ∧ 0 ≤ z.2}` (first quadrant, a lattice-convex region: real
hull `C := {p : ℝ×ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2}`), `vJ := (1,0)`, `nJ := (0,1)` (`dot nJ vJ = 0`),
`g := (0,0)` (level `0`), `q := (-5,3)` (level `3`), `y := (-9,2)` (level `2`, between `0` and
`3`).  `g`'s ray `{(k,0)}` is in `T` for all `k`; `q`'s ray `{(-5+k,3)}` needs `k ≥ 5`.  The
target claim checks directly: `y + k • vJ = (-9+k, 2) ∈ T ⟺ k ≥ 9`, so `L = 9` works and is
optimal (`k = 8` gives `(-1,2) ∉ T`).

Cross-check against the barycentric argument the proof actually runs:
`μ := (dot nJ q - dot nJ y)/(dot nJ q - dot nJ g) = (3-2)/(3-0) = 1/3`, and
`(1/3)•(0,0) + (2/3)•(-5,3) = (-10/3, 2)`, so `y - (-10/3,2) = (-17/3, 0) = (-17/3) • vJ`,
i.e. `s = -17/3` and the proof returns `L = ⌈17/3⌉ = 6`.  That is below the sharp lattice
answer `9`, which is exactly why the conclusion is stated as eventual membership rather than
with an explicit optimal `L`.
-/

set_option autoImplicit false

namespace Nivat.StripRay

open Nivat

/-! ## §1.  The strip lemma (from `lane-cd-substrip.lean` §10, verbatim) -/

/-- Two `ℝ`-vectors both orthogonal (w.r.t. the standard `ℝ × ℝ` pairing) to a common nonzero
`nJ`, with the first (`vJ`) itself nonzero, forces the second to be a real multiple of the
first.  Pure 2D linear algebra: `nJ`'s orthogonal complement in `ℝ²` is 1-dimensional. -/
theorem real_smul_of_dot_eq_zero {nJ vJ w : ℝ × ℝ}
    (hnvJ : nJ.1 * vJ.1 + nJ.2 * vJ.2 = 0) (hvJ : vJ ≠ 0) (hnJ : nJ ≠ 0)
    (hw : nJ.1 * w.1 + nJ.2 * w.2 = 0) : ∃ s : ℝ, w = s • vJ := by
  have hD1 : nJ.1 * (vJ.1 * w.2 - vJ.2 * w.1) = 0 := by linear_combination w.2 * hnvJ - vJ.2 * hw
  have hD2 : nJ.2 * (vJ.1 * w.2 - vJ.2 * w.1) = 0 := by
    linear_combination (-w.1) * hnvJ + vJ.1 * hw
  have hnJ' : nJ.1 ≠ 0 ∨ nJ.2 ≠ 0 := by
    rcases eq_or_ne nJ.1 0 with h1 | h1
    · rcases eq_or_ne nJ.2 0 with h2 | h2
      · exact absurd (Prod.ext h1 h2) hnJ
      · exact Or.inr h2
    · exact Or.inl h1
  have hD : vJ.1 * w.2 - vJ.2 * w.1 = 0 := by
    rcases hnJ' with h | h
    · exact (mul_eq_zero.mp hD1).resolve_left h
    · exact (mul_eq_zero.mp hD2).resolve_left h
  have hvJ' : vJ.1 ≠ 0 ∨ vJ.2 ≠ 0 := by
    rcases eq_or_ne vJ.1 0 with h1 | h1
    · rcases eq_or_ne vJ.2 0 with h2 | h2
      · exact absurd (Prod.ext h1 h2) hvJ
      · exact Or.inr h2
    · exact Or.inl h1
  rcases hvJ' with hv1 | hv2
  · refine ⟨w.1 / vJ.1, Prod.ext ?_ ?_⟩
    · show w.1 = w.1 / vJ.1 * vJ.1
      field_simp
    · show w.2 = w.1 / vJ.1 * vJ.2
      have heq : vJ.1 * w.2 = w.1 * vJ.2 := by linarith
      field_simp
      linarith
  · refine ⟨w.2 / vJ.2, Prod.ext ?_ ?_⟩
    · show w.1 = w.2 / vJ.2 * vJ.1
      have heq : vJ.2 * w.1 = w.2 * vJ.1 := by linarith
      field_simp
      linarith
    · show w.2 = w.2 / vJ.2 * vJ.2
      field_simp

/-- If `toReal (p + k • vJ) ∈ C` for every `k : ℕ` and `C` is convex, the same holds for every
real parameter `t ≥ 0` in place of the natural number `k` (interpolate between `⌊t⌋` and
`⌊t⌋ + 1`). -/
theorem toReal_ray_mem {C : Set (ℝ × ℝ)} (hC : Convex ℝ C) {p vJ : ℤ × ℤ}
    (hray : ∀ k : ℕ, toReal (p + (k : ℤ) • vJ) ∈ C) {t : ℝ} (ht : 0 ≤ t) :
    toReal p + t • toReal vJ ∈ C := by
  set n : ℕ := ⌊t⌋₊ with hndef
  have hn1 : (n : ℝ) ≤ t := Nat.floor_le ht
  have hn2 : t ≤ (n : ℝ) + 1 := (Nat.lt_floor_add_one t).le
  set θ : ℝ := t - n with hθdef
  have hθ0 : 0 ≤ θ := by rw [hθdef]; linarith
  have hθ1 : θ ≤ 1 := by rw [hθdef]; linarith
  have hm1 : toReal p + (n : ℝ) • toReal vJ ∈ C := by
    have h := hray n
    rw [Nivat.toReal_add, Nivat.toReal_zsmul] at h
    push_cast at h
    exact h
  have hm2 : toReal p + ((n : ℝ) + 1) • toReal vJ ∈ C := by
    have h := hray (n + 1)
    rw [Nivat.toReal_add, Nivat.toReal_zsmul] at h
    push_cast at h
    exact h
  have hcomb := hC hm1 hm2 (show (0:ℝ) ≤ 1 - θ by linarith) hθ0 (by ring)
  have heq : (1 - θ) • (toReal p + (n : ℝ) • toReal vJ) + θ • (toReal p + ((n : ℝ) + 1) • toReal vJ)
      = toReal p + t • toReal vJ := by
    have ht' : t = (n : ℝ) + θ := by rw [hθdef]; ring
    rw [ht']
    module
  rwa [heq] at hcomb

/-- `y` at a `dot nJ`-level between `g` and `q`, both on rays parallel to `vJ` and contained in
the lattice-convex region `T`, is itself eventually on its own `vJ`-parallel ray inside `T`. -/
theorem eventually_mem_of_between_parallel_rays {T : Set (ℤ × ℤ)}
    (hlc : IsLatticeConvexRegion T) {nJ vJ g q y : ℤ × ℤ}
    (hgray : ∀ k : ℕ, g + (k : ℤ) • vJ ∈ T) (hqray : ∀ k : ℕ, q + (k : ℤ) • vJ ∈ T)
    (hnvJ : Nivat.LE2.dot nJ vJ = 0) (hvJ : vJ ≠ 0) (hnJ : nJ ≠ 0)
    (hlow : Nivat.LE2.dot nJ g ≤ Nivat.LE2.dot nJ y)
    (hhigh : Nivat.LE2.dot nJ y ≤ Nivat.LE2.dot nJ q) :
    ∃ L : ℤ, ∀ k : ℤ, L ≤ k → y + k • vJ ∈ T := by
  obtain ⟨C, hCconv, -, hTeq⟩ := hlc
  set a : ℝ := (Nivat.LE2.dot nJ g : ℝ) with hadef
  set b : ℝ := (Nivat.LE2.dot nJ q : ℝ) with hbdef
  set c : ℝ := (Nivat.LE2.dot nJ y : ℝ) with hcdef
  have hab : a ≤ c := by rw [hadef, hcdef]; exact_mod_cast hlow
  have hcb : c ≤ b := by rw [hcdef, hbdef]; exact_mod_cast hhigh
  set μ : ℝ := (b - c) / (b - a) with hμdef
  have hμ0 : 0 ≤ μ := by
    rcases eq_or_lt_of_le (hab.trans hcb) with heq | hlt
    · rw [hμdef, ← heq]; simp
    · exact div_nonneg (by linarith) (by linarith)
  have hμ1 : μ ≤ 1 := by
    rcases eq_or_lt_of_le (hab.trans hcb) with heq | hlt
    · rw [hμdef, ← heq]; simp
    · rw [div_le_one (by linarith)]; linarith
  have hcombo : c = μ * a + (1 - μ) * b := by
    rcases eq_or_lt_of_le (hab.trans hcb) with heq | hlt
    · have hca : c = a := le_antisymm (heq ▸ hcb) hab
      rw [hμdef, ← heq, hca]; ring
    · rw [hμdef]
      have hba : b - a ≠ 0 := by linarith
      field_simp
      ring
  have hgC : ∀ k : ℕ, toReal (g + (k : ℤ) • vJ) ∈ C := by
    intro k; have h := hgray k; rw [hTeq] at h; exact h
  have hqC : ∀ k : ℕ, toReal (q + (k : ℤ) • vJ) ∈ C := by
    intro k; have h := hqray k; rw [hTeq] at h; exact h
  have hnvJR : (toReal nJ).1 * (toReal vJ).1 + (toReal nJ).2 * (toReal vJ).2 = 0 := by
    have h0 : (Nivat.LE2.dot nJ vJ : ℝ) = 0 := by exact_mod_cast hnvJ
    simpa [toReal, Nivat.LE2.dot] using h0
  have hnJR : toReal nJ ≠ 0 := by
    intro h
    apply hnJ
    have h1 : (nJ.1 : ℝ) = 0 := congrArg Prod.fst h
    have h2 : (nJ.2 : ℝ) = 0 := congrArg Prod.snd h
    exact Prod.ext (by exact_mod_cast h1) (by exact_mod_cast h2)
  have hvJR : toReal vJ ≠ 0 := by
    intro h
    apply hvJ
    have h1 : (vJ.1 : ℝ) = 0 := congrArg Prod.fst h
    have h2 : (vJ.2 : ℝ) = 0 := congrArg Prod.snd h
    exact Prod.ext (by exact_mod_cast h1) (by exact_mod_cast h2)
  have hwR : (toReal nJ).1 * (toReal y - (μ • toReal g + (1 - μ) • toReal q)).1
      + (toReal nJ).2 * (toReal y - (μ • toReal g + (1 - μ) • toReal q)).2 = 0 := by
    have hy : (toReal nJ).1 * (toReal y).1 + (toReal nJ).2 * (toReal y).2 = c := by
      simp only [hcdef, toReal, Nivat.LE2.dot]; push_cast; ring
    have hg : (toReal nJ).1 * (toReal g).1 + (toReal nJ).2 * (toReal g).2 = a := by
      simp only [hadef, toReal, Nivat.LE2.dot]; push_cast; ring
    have hq : (toReal nJ).1 * (toReal q).1 + (toReal nJ).2 * (toReal q).2 = b := by
      simp only [hbdef, toReal, Nivat.LE2.dot]; push_cast; ring
    simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul]
    nlinarith [hy, hg, hq, hcombo]
  obtain ⟨s, hs⟩ := real_smul_of_dot_eq_zero hnvJR hvJR hnJR hwR
  refine ⟨⌈-s⌉, fun k hk => ?_⟩
  have hkR : -s ≤ (k : ℝ) := by
    have h1 : (-s : ℝ) ≤ (⌈-s⌉ : ℝ) := Int.le_ceil _
    have h2 : (⌈-s⌉ : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  have htnn : (0:ℝ) ≤ s + (k : ℝ) := by linarith
  have hg' := toReal_ray_mem hCconv hgC htnn
  have hq' := toReal_ray_mem hCconv hqC htnn
  have hcomb := hCconv hg' hq' hμ0 (by linarith : (0:ℝ) ≤ 1 - μ) (by ring)
  have hyeq : toReal y = μ • toReal g + (1 - μ) • toReal q + s • toReal vJ := by
    have := hs
    simp only [Prod.ext_iff, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add,
      Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at this ⊢
    constructor <;> linarith [this.1, this.2]
  have hfinal : μ • (toReal g + (s + (k:ℝ)) • toReal vJ) + (1 - μ) • (toReal q + (s + (k:ℝ)) • toReal vJ)
      = toReal (y + k • vJ) := by
    rw [Nivat.toReal_add, Nivat.toReal_zsmul]
    apply Prod.ext <;>
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
        Prod.ext_iff] at hyeq ⊢ <;>
      nlinarith [hyeq.1, hyeq.2]
  rw [hfinal] at hcomb
  rw [hTeq]
  exact hcomb

/-! ## §2.  Repackaged as `hseedS_of_parts`'s `hstrip`

`hstrip` quantifies over `g`, `q`, `y` *inside* the hypothesis, with the four ambient facts
(`hlc`, `dot nJ vJ = 0`, `vJ ≠ 0`, `nJ ≠ 0`) held fixed outside.  §1's lemma has them in the
other order, so a caller supplying it directly has to write an explicit `fun g q y hg hq …`
and get the binder order right.  This corollary does that once. -/

/-- **`hstrip`.**  Exactly the shape `hseedS_of_parts` takes, with the four ambient facts
discharged up front. -/
theorem hstrip_of_latticeConvex {T : Set (ℤ × ℤ)} {nJ vJ : ℤ × ℤ}
    (hlc : IsLatticeConvexRegion T)
    (hnvJ : Nivat.LE2.dot nJ vJ = 0) (hvJ : vJ ≠ 0) (hnJ : nJ ≠ 0) :
    ∀ g q y : ℤ × ℤ, (∀ k : ℕ, g + (k : ℤ) • vJ ∈ T) → (∀ k : ℕ, q + (k : ℤ) • vJ ∈ T) →
      Nivat.LE2.dot nJ g ≤ Nivat.LE2.dot nJ y → Nivat.LE2.dot nJ y ≤ Nivat.LE2.dot nJ q →
      ∃ L : ℤ, ∀ k : ℤ, L ≤ k → y + k • vJ ∈ T :=
  fun _ _ _ hg hq hlow hhigh =>
    eventually_mem_of_between_parallel_rays hlc hg hq hnvJ hvJ hnJ hlow hhigh

/-! ## §3.  `hindep`

`hseedS_of_parts` needs `{vJ, vJ1}` to be a frame (`det vJ vJ1 ≠ 0`).  The chain never supplies
that directly, but it is forced: `vJ` spans `nJ`'s orthogonal line, and `vJ1` is strictly off
that line because the sweep direction strictly decreases `dot nJ`. -/

/-- **`hindep`.**  A primitive `vJ` orthogonal to `nJ` is independent of any `vJ1` on which
`dot nJ` is strictly negative. -/
theorem det_ne_zero_of_perp_of_dot_neg {nJ vJ vJ1 : ℤ × ℤ}
    (hvJprim : Nivat.LE2.Prim vJ) (hnJvJ : Nivat.LE2.dot nJ vJ = 0)
    (hsweep : Nivat.LE2.dot nJ vJ1 < 0) : det vJ vJ1 ≠ 0 := by
  intro hdet
  obtain ⟨t, ht⟩ := Nivat.LE2.exists_smul_of_det_eq_zero hvJprim hdet
  have h0 : Nivat.LE2.dot nJ vJ1 = t * Nivat.LE2.dot nJ vJ := by
    subst ht
    show nJ.1 * (t * vJ.1) + nJ.2 * (t * vJ.2) = t * (nJ.1 * vJ.1 + nJ.2 * vJ.2)
    ring
  rw [hnJvJ, mul_zero] at h0
  omega

end Nivat.StripRay

#print axioms Nivat.StripRay.real_smul_of_dot_eq_zero
#print axioms Nivat.StripRay.toReal_ray_mem
#print axioms Nivat.StripRay.eventually_mem_of_between_parallel_rays
#print axioms Nivat.StripRay.hstrip_of_latticeConvex
#print axioms Nivat.StripRay.det_ne_zero_of_perp_of_dot_neg
