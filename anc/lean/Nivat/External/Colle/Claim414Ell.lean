/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.Section8.RegionUpgrade
import Nivat.External.Colle.ChainGeom
import Nivat.External.Colle.Theorem114Step3
import Nivat.External.Colle.Interfaces
import Nivat.External.Colle.Lemma45
import Nivat.External.Colle.BoyleLind

set_option autoImplicit false

/-!
# Collé Claim 4.14, the `ℓ`-half (`delivery/scratch/b3_colle2.txt:918-922`)

Blocks 1–6 of the approved plan.  Every block ends in a named theorem followed by
`#print axioms`.  Nothing here touches `Nivat/`.
-/

open Nivat

namespace Nivat.Claim414

/-! ## Block 1: the recession cone swallows the support half-plane

Paper input (`b3_colle2.txt:922`): "the support line of `Â^(ε)_∞` determined by `ℓ`
coincides with `ℓ^(−)`", so every lattice point on the `Â_∞`-side of that support line is
reached from `Â_∞` by moving far enough along `p` (the recession direction parallel to `ℓ`).
Here `n` is the normal of that support line (`dot n p = 0`), `v` is the second recession
direction, pointing strictly into the half-plane (`0 < dot n v`), and `z₀ ∈ R` lies on the
support line (only `dot n z₀ ≤ dot n z` is used). -/

/-- 2D Cramer identity in the integers, scaled by `det v p ^ 2`. -/
private theorem cramer_sq (v p w : ℤ × ℤ) (t : ℤ) :
    (det v p * det v p) • (w + t • p) =
      (det v p * det w p) • v + (det v p * (det v w + t * det v p)) • p := by
  ext <;> simp only [det, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul] <;> ring

theorem exists_nat_smul_add_mem_of_dot_le
    {R : Set (ℤ × ℤ)} (hR : IsLatticeConvexRegion R) {z₀ : ℤ × ℤ} (hz₀ : z₀ ∈ R)
    {p v n : ℤ × ℤ} (hp0 : p ≠ 0)
    (hrec_p : ∀ g ∈ R, g + p ∈ R) (hrec_v : ∀ g ∈ R, g + v ∈ R)
    (hnp : LE2.dot n p = 0) (hnv : 0 < LE2.dot n v) :
    ∀ z : ℤ × ℤ, LE2.dot n z₀ ≤ LE2.dot n z → ∃ t : ℕ, z + (t : ℤ) • p ∈ R := by
  intro z hz
  have hD0 : det v p ≠ 0 := ColleReg.det_ne_zero_of_dot hp0 hnp hnv.ne'
  -- `w := z - z₀`
  have hnw : 0 ≤ LE2.dot n (z - z₀) := by
    have : LE2.dot n (z - z₀) = LE2.dot n z - LE2.dot n z₀ := by
      simp only [LE2.dot, Prod.fst_sub, Prod.snd_sub]; ring
    linarith
  -- `det w p * dot n v = det v p * dot n w` (uses `dot n p = 0`)
  have hkey : det (z - z₀) p * LE2.dot n v = det v p * LE2.dot n (z - z₀) := by
    simp only [det, LE2.dot, Prod.fst_sub, Prod.snd_sub] at hnp ⊢
    linear_combination ((z.1 - z₀.1) * v.2 - (z.2 - z₀.2) * v.1) * hnp
  -- coefficient of `v` is nonnegative
  have hα : 0 ≤ det v p * det (z - z₀) p := by
    have h1 : (det v p * det (z - z₀) p) * LE2.dot n v
        = (det v p * det v p) * LE2.dot n (z - z₀) := by
      rw [mul_assoc, hkey]; ring
    have h2 : 0 ≤ (det v p * det v p) * LE2.dot n (z - z₀) :=
      mul_nonneg (mul_self_nonneg _) hnw
    by_contra hcon
    push Not at hcon
    nlinarith [h1, h2, hnv, hcon]
  -- choose `t := |det v w|`; coefficient of `p` is then nonnegative
  refine ⟨(det v (z - z₀)).natAbs, ?_⟩
  have ht : (((det v (z - z₀)).natAbs : ℕ) : ℤ) = |det v (z - z₀)| := Int.natCast_natAbs _
  have hβ : 0 ≤ det v p * (det v (z - z₀) + (((det v (z - z₀)).natAbs : ℕ) : ℤ) * det v p) := by
    rw [ht]
    have h3 : -(|det v p| * |det v (z - z₀)|) ≤ det v p * det v (z - z₀) := by
      rw [← abs_mul]; exact neg_abs_le _
    have h4 : |det v p| * |det v p| = det v p * det v p := abs_mul_abs_self _
    have h5 : 1 ≤ |det v p| := Int.one_le_abs hD0
    have h6 : 0 ≤ |det v (z - z₀)| * |det v p| * (|det v p| - 1) :=
      mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (sub_nonneg.mpr h5)
    nlinarith [h3, h4, h5, h6]
  -- recession-cone membership
  have hv_rc : toReal v ∈ recCone R := toReal_mem_recCone hrec_v
  have hp_rc : toReal p ∈ recCone R := toReal_mem_recCone hrec_p
  have hbig : toReal ((det v p * det v p) •
      ((z - z₀) + (((det v (z - z₀)).natAbs : ℕ) : ℤ) • p)) ∈ recCone R := by
    rw [cramer_sq, toReal_add, toReal_zsmul, toReal_zsmul]
    exact add_mem_recCone (smul_mem_recCone (by exact_mod_cast hα) hv_rc)
      (smul_mem_recCone (by exact_mod_cast hβ) hp_rc)
  have hsmall : toReal ((z - z₀) + (((det v (z - z₀)).natAbs : ℕ) : ℤ) • p) ∈ recCone R := by
    have hne : ((det v p * det v p : ℤ) : ℝ) ≠ 0 := by
      exact_mod_cast mul_ne_zero hD0 hD0
    have hDD : (0 : ℝ) ≤ ((det v p * det v p : ℤ) : ℝ) := by
      exact_mod_cast mul_self_nonneg (det v p)
    have h := smul_mem_recCone (inv_nonneg.mpr hDD) hbig
    rw [toReal_zsmul, inv_smul_smul₀ hne] at h
    exact h
  have hmem := add_mem_of_mem_recCone hR hsmall hz₀
  have heq : z₀ + ((z - z₀) + (((det v (z - z₀)).natAbs : ℕ) : ℤ) • p)
      = z + (((det v (z - z₀)).natAbs : ℕ) : ℤ) • p := by abel
  rw [heq] at hmem
  exact hmem


/-! ## Block 2: an accumulation point along `p` agrees with `x̂_per` on the half-plane and
is not fully periodic

Paper input (`b3_colle2.txt:922`, first two sentences): "as `ϑ|Â^(ε)_∞ = x̂_per|Â^(ε)_∞` is
periodic with period parallel to `ℓ` and the support line of `Â^(ε)_∞` determined by `ℓ`
coincides with `ℓ^(−)`, the fact that `x_per|ℋ(ℓ^(−))` and so `x̂_per|ℋ(ℓ^(−))` is not fully
periodic prevents the set `{T^{−t v_ℓ} ϑ : t ∈ ℤ₊}` from having a fully periodic
accumulation point", together with "`z_per|ℋ(ℓ^(−))` is periodic with period parallel to
`ℓ`".  The hypothesis `hnfp` is the Case 2 standing assumption `b3_colle2.txt:890`
("we may assume that `x_per|ℋ(ℓ^(−))` is not fully periodic"), stated in the literal
Definition 2.11 form (`b3_colle2.txt:367-369`) via `Colle35.PeriodicOnWith`; `x̂_per :=
T^{k v_ℓ} x_per` (`b3_colle2.txt:896`) is `T (K • vl) xper`, and the half-plane
`ℋ(ℓ^(−))` is `{z | c ≤ dot n z}` where `hexh` (block 1) says it is swallowed by `R` along `p`. -/

/-- A period can be added to the argument of a configuration. -/
private theorem eval_add_of_mem_Per {α : Type*} {f : Config α} {u : ℤ × ℤ} (hu : u ∈ Per f)
    (w : ℤ × ℤ) : f (w + u) = f w :=
  congrFun (mem_Per_iff.mp hu) w

theorem accPointAlong_eq_on_halfPlane_and_not_doublyPeriodic
    {ϑ xper y : Config ℤ} {R : Set (ℤ × ℤ)} {p n vl : ℤ × ℤ} {K : ℕ} {c : ℤ}
    (hrec : ∀ g ∈ R, g + p ∈ R)
    (hexh : ∀ z, c ≤ LE2.dot n z → ∃ t : ℕ, z + (t : ℤ) • p ∈ R)
    (hagree : ∀ z ∈ R, ϑ z = T ((K : ℤ) • vl) xper z)
    (hp_per : p ∈ Per xper) (hvl_tan : LE2.dot n vl = 0)
    (hnfp : ¬ ∃ h h' : ℤ × ℤ, det h h' ≠ 0 ∧
      Colle35.PeriodicOnWith xper {z | c ≤ LE2.dot n z} h ∧
      Colle35.PeriodicOnWith xper {z | c ≤ LE2.dot n z} h')
    (hy : Colle3.IsAccPointAlong p ϑ y) :
    (∀ z, c ≤ LE2.dot n z → y z = T ((K : ℤ) • vl) xper z) ∧ ¬ DoublyPeriodic y := by
  have hpart1 : ∀ z, c ≤ LE2.dot n z → y z = T ((K : ℤ) • vl) xper z := by
    intro z hz
    obtain ⟨t₀, ht₀⟩ := hexh z hz
    obtain ⟨t, ht₀t, hW⟩ := hy {z} t₀
    have hyz : y z = ϑ (z + (t : ℤ) • p) := hW z (Finset.mem_singleton_self z)
    -- `z + t • p = (z + t₀ • p) + (t - t₀) • p ∈ R`
    have hmem : z + (t : ℤ) • p ∈ R := by
      have h := ColleReg.ray_of_recession hrec ht₀ (t - t₀)
      have hcast : (((t - t₀ : ℕ) : ℤ)) = (t : ℤ) - (t₀ : ℤ) := Nat.cast_sub ht₀t
      rw [hcast, sub_smul, add_assoc, add_sub_cancel] at h
      exact h
    rw [hyz, hagree _ hmem]
    -- kill the period `t • p` of `xper`
    show xper (z + (t : ℤ) • p + (K : ℤ) • vl) = xper (z + (K : ℤ) • vl)
    have hper : (t : ℤ) • p ∈ Per xper := (Per xper).zsmul_mem hp_per _
    rw [add_right_comm, eval_add_of_mem_Per hper]
  refine ⟨hpart1, ?_⟩
  rintro ⟨u, hu, v, hv, hdet⟩
  apply hnfp
  -- each period of `y` becomes a Definition 2.11 period of `xper` on the half-plane
  have hshift : ∀ g, c ≤ LE2.dot n g → xper g = y (g - (K : ℤ) • vl) := by
    intro g hg
    have hg' : c ≤ LE2.dot n (g - (K : ℤ) • vl) := by
      have : LE2.dot n (g - (K : ℤ) • vl) = LE2.dot n g - (K : ℤ) * LE2.dot n vl := by
        simp only [LE2.dot, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd,
          smul_eq_mul]; ring
      rw [this, hvl_tan]; simpa using hg
    rw [hpart1 _ hg']
    show xper g = xper (g - (K : ℤ) • vl + (K : ℤ) • vl)
    rw [sub_add_cancel]
  have hmk : ∀ w ∈ Per y, w ≠ 0 → Colle35.PeriodicOnWith xper {z | c ≤ LE2.dot n z} w := by
    intro w hw hw0
    refine ⟨hw0, fun g hg hgw => ?_⟩
    simp only [Set.mem_ofPred_eq] at hg hgw
    rw [hshift _ hg, hshift _ hgw, add_sub_right_comm, eval_add_of_mem_Per hw]
  have hu0 : u ≠ 0 := by
    rintro rfl; apply hdet; simp [det]
  have hv0 : v ≠ 0 := by
    rintro rfl; apply hdet; simp [det]
  exact ⟨u, v, hdet, hmk u hu hu0, hmk v hv hv0⟩


/-! ## Block 3: Proposition 2.12, instantiated

Paper (`b3_colle2.txt:373-375`, Kari–Szabados): "If `η|ℋ(ℓ)` is periodic with period parallel
to some oriented line `ℓ ⊂ ℝ²`, then `η` is periodic with period parallel to `ℓ`."  Used at
`b3_colle2.txt:922`: "Thus, Proposition 2.12 implies that `z_per` is periodic with period
parallel to `ℓ`".  The repo form is `Colle.period_multiple_of_periodicDecompZ`; the
`PeriodicDecompZ` input comes from minimality of `ξ` through
`IsMinimalCounterexample.of_mem_orbitClosure` (pattern of `RegionSteps.lean:586-590`). -/

theorem exists_zsmul_mem_Per_of_halfPlane_period
    {ξ y : Config ℤ} (hξ : IsMinimalCounterexample ξ) (hy : y ∈ orbitClosure ξ)
    {n p : ℤ × ℤ} (hn : n ≠ 0) (hp : p ≠ 0) (hnp : LE2.dot n p = 0) {c : ℤ}
    (hlocal : ∀ z, c ≤ LE2.dot n z → y (z + p) = y z) :
    ∃ k : ℤ, k ≠ 0 ∧ k • p ∈ Per y := by
  obtain ⟨m, hdec⟩ : ∃ m, PeriodicDecompZ y m := by
    by_cases hper : IsPeriodic y
    · exact ⟨1, fun _ => y, fun _ => hper, fun z => by simp⟩
    · obtain ⟨m, hord, -⟩ := hξ.2
      exact ⟨m, ((hξ.of_mem_orbitClosure hy hper).2 m hord).1⟩
  refine Colle.period_multiple_of_periodicDecompZ hdec (KM.toReal_ne_zero hn) (c := (c : ℝ))
    hp ?_ ?_
  · rw [LE2.inner2_toReal, hnp]; simp
  · intro z hz
    rw [LE2.inner2_toReal] at hz
    exact hlocal z (by exact_mod_cast hz)


/-! ## Block 4: a period plus "not fully periodic" puts `ℓ` into the non-expansive lines

Paper (`b3_colle2.txt:922`): "`z_per` is periodic with period parallel to `ℓ`, but not fully
periodic, which means that `ℓ ∈ nexpl(z_per) ⊂ nexpl(ϑ)`."  The line `ℓ` is recorded by a
normal vector `ℓ` (`dot ℓ h = 0`).

Here "nexpl" is `Colle45.NonExpansiveLine` (`Lemma45.lean:85`), a placeholder semantics:
`v` is a primitive normal and two distinct points of the orbit closure agree on
`halfPlaneLE v 0`.  It is not the Boyle–Lind NEL, but it is what `exists_chainData` and the
other existing signatures consume, and it suffices for the `b3_colle2.txt:90` closing
(block 6).  The proof is the contrapositive of `Colle3.doublyPeriodic_of_notMem_ONED_perp`
at `w := ±toReal ℓ`. -/

theorem mem_nonExpansiveLine_of_period_of_not_doublyPeriodic
    {y : Config ℤ} (hfin : (Set.range y).Finite) {ℓ : ℤ × ℤ} (hℓ : Primitive ℓ)
    {h : ℤ × ℤ} (hh : h ∈ Per y) (hh0 : h ≠ 0) (hperp : LE2.dot ℓ h = 0)
    (hnd : ¬ DoublyPeriodic y) :
    ℓ ∈ Colle45.NonExpansiveLine y ∧
      Colle45.IsOneSidedNonexpansive y ℓ ∧ Colle45.IsOneSidedNonexpansive y (-ℓ) := by
  have key : ∀ m : ℤ × ℤ, m ≠ 0 → LE2.dot m h = 0 → Colle45.IsOneSidedNonexpansive y m := by
    intro m hm hmh
    have hw : toReal m ∈ ONED y := by
      by_contra hcon
      exact hnd (Colle3.doublyPeriodic_of_notMem_ONED_perp hfin hh hh0 (KM.toReal_ne_zero hm)
        (by rw [LE2.inner2_toReal, hmh]; simp) hcon)
    obtain ⟨-, x, hx, y', hy', hxy, hagree⟩ := hw
    refine ⟨x, y', hx, hy', hxy, fun z hz => hagree z ?_⟩
    show inner2 (toReal m) z ≤ 0
    rw [LE2.inner2_toReal]; exact_mod_cast hz
  have hℓ0 : ℓ ≠ 0 := hℓ.ne_zero
  have h1 := key ℓ hℓ0 hperp
  have h2 := key (-ℓ) (neg_ne_zero.mpr hℓ0) (by rw [LE2.dot_neg_left, hperp, neg_zero])
  refine ⟨⟨hℓ, ?_⟩, h1, h2⟩
  obtain ⟨x, y', hx, hy', hxy, hagree⟩ := h1
  exact ⟨x, y', hx, hy', hxy, fun z hz => hagree z hz⟩


/-- `nexpl(z_per) ⊂ nexpl(ϑ)` for `z_per ∈ X_ϑ` (`b3_colle2.txt:922`). -/
theorem nonExpansiveLine_mono_of_mem_orbitClosure {ϑ y : Config ℤ}
    (hy : y ∈ orbitClosure ϑ) : Colle45.NonExpansiveLine y ⊆ Colle45.NonExpansiveLine ϑ := by
  rintro v ⟨hv, x, y', hx, hy', hxy, hagree⟩
  exact ⟨hv, x, y', Colle.mem_orbitClosure_trans hy hx, Colle.mem_orbitClosure_trans hy hy',
    hxy, hagree⟩


/-! ## Block 6: two non-expansive lines forbid periodicity

Paper (`b3_colle2.txt:90`): "any configuration `η ∈ 𝒜^{ℤ²}` where `nexpl(η)` has at least two
elements can not be periodic."  With the placeholder `NonExpansiveLine` this is elementary:
a period `u` must be orthogonal to every normal in `NonExpansiveLine ϑ`
(`Colle3.notMem_ONED_of_inner2_ne_zero`), and two independent normals force `u = 0`. -/

theorem not_isPeriodic_of_two_nonExpansiveLines {ϑ : Config ℤ} {ℓ ℓ' : ℤ × ℤ}
    (h₁ : ℓ ∈ Colle45.NonExpansiveLine ϑ) (h₂ : ℓ' ∈ Colle45.NonExpansiveLine ϑ)
    (hdet : det ℓ ℓ' ≠ 0) : ¬ IsPeriodic ϑ := by
  rintro ⟨u, hu, hu0⟩
  have hmem : ∀ m : ℤ × ℤ, m ∈ Colle45.NonExpansiveLine ϑ → LE2.dot m u = 0 := by
    rintro m ⟨hm, x, y, hx, hy, hxy, hagree⟩
    by_contra hne
    have hnot : toReal m ∉ ONED ϑ :=
      Colle3.notMem_ONED_of_inner2_ne_zero hu (by rw [LE2.inner2_toReal]; exact_mod_cast hne)
    refine hnot ⟨KM.toReal_ne_zero hm.ne_zero, x, hx, y, hy, hxy, fun z hz => hagree z ?_⟩
    have hz' : inner2 (toReal m) z ≤ 0 := hz
    rw [LE2.inner2_toReal] at hz'
    exact_mod_cast hz'
  have e1 := hmem ℓ h₁
  have e2 := hmem ℓ' h₂
  apply hu0
  simp only [LE2.dot] at e1 e2
  have h1 : det ℓ ℓ' * u.1 = 0 := by
    simp only [det]; linear_combination ℓ'.2 * e1 - ℓ.2 * e2
  have h2 : det ℓ ℓ' * u.2 = 0 := by
    simp only [det]; linear_combination ℓ.1 * e2 - ℓ'.1 * e1
  refine Prod.ext ?_ ?_
  · exact (mul_eq_zero.mp h1).resolve_left hdet
  · exact (mul_eq_zero.mp h2).resolve_left hdet


/-! ## Block 5: Claim 4.14, the `ℓ`-half (`b3_colle2.txt:918-922`)

Verbatim (`b3_colle2.txt:922`, first four sentences): "Indeed, as `ϑ|Â^(ε)_∞ = x̂_per|Â^(ε)_∞`
is periodic with period parallel to `ℓ` and the support line of `Â^(ε)_∞` determined by `ℓ`
coincides with `ℓ^(−)`, the fact that `x_per|ℋ(ℓ^(−))` and so `x̂_per|ℋ(ℓ^(−))` is not fully
periodic prevents the set `{T^{−t v_ℓ} ϑ : t ∈ ℤ₊}` from having a fully periodic
accumulation point.  Let `z_per` be an accumulation point of `{T^{−t v_ℓ} ϑ : t ∈ ℤ₊}`.  As
`ϑ|Â^(ε)_∞` is periodic with period parallel to `ℓ`, then `z_per|ℋ(ℓ^(−))` is periodic with
period parallel to `ℓ`.  Thus, Proposition 2.12 implies that `z_per` is periodic with period
parallel to `ℓ`, but not fully periodic, which means that `ℓ ∈ nexpl(z_per) ⊂ nexpl(ϑ)`."

Dictionary.  `Â^(ε)_∞` is `⋃ i, cg.toChainData.Ahat i`; `ℓ` is recorded by its normal
vector `ℓ` (`dot ℓ vl = 0`); `v_ℓ` is `vl`, and the recession direction `p ∥ vl`
(`det p vl = 0`) of `Â_∞` replaces `−v_ℓ` as the orbit direction (the sign of `p` against
`vl` is not recorded in `ChainDataGeom`).  The support line `ℓ^(−)` is the line
`dot nℓ · = c` with `nℓ := det p cg.vJ • (-p.2, p.1)` (so `dot nℓ p = 0` and
`0 < dot nℓ cg.vJ`); `hsupp`/`hatt` say `Â_∞` lies in `{c ≤ dot nℓ ·}` and touches its
boundary, i.e. that this is the support line of `Â_∞` determined by `ℓ`.  `hagree` is (4.6)
with `x̂_per := T^{k v_ℓ} x_per` (`b3_colle2.txt:894-896`), `hp_per` is "periodic with period
parallel to `ℓ`", and `hnfp` is the Case 2 standing assumption `b3_colle2.txt:890` in the
Definition 2.11 form.  The conclusion `ℓ ∈ nexpl(ϑ)` is `Colle45.NonExpansiveLine`
(placeholder semantics, see block 4). -/

theorem claim414_ell {ξ xper ϑ : Config ℤ} {vl p ℓ : ℤ × ℤ} {S : Finset (ℤ × ℤ)} {gen : ℤ × ℤ}
    (cg : Colle35.ChainDataGeom ξ xper vl p S gen) {K : ℕ}
    (hξ : IsMinimalCounterexample ξ)
    (hℓ_nel : ℓ ∈ Colle45.NonExpansiveLine ξ) (hdet_ℓ : LE2.dot ℓ vl = 0)
    (hp_ne : p ≠ 0) (hvl_ne : vl ≠ 0) (hdet_vl : det p vl = 0) (hp_per : p ∈ Per xper)
    (hϑ_mem : ϑ ∈ orbitClosure ξ)
    (hRconv : IsLatticeConvexRegion (⋃ i, cg.toChainData.Ahat i))
    (hagree : ∀ z ∈ ⋃ i, cg.toChainData.Ahat i, ϑ z = T ((K : ℤ) • vl) xper z)
    {c : ℤ}
    -- `_hsupp` is the other half of "support line"; the proof only needs the touching point
    -- `hatt` (block 1 uses `dot nℓ z₀ ≤ dot nℓ z` only).  Kept to match the approved signature.
    (_hsupp : ∀ g ∈ ⋃ i, cg.toChainData.Ahat i, c ≤ LE2.dot (det p cg.vJ • (-p.2, p.1)) g)
    (hatt : ∃ g ∈ ⋃ i, cg.toChainData.Ahat i, LE2.dot (det p cg.vJ • (-p.2, p.1)) g = c)
    (hnfp : ¬ ∃ h h' : ℤ × ℤ, det h h' ≠ 0 ∧
      Colle35.PeriodicOnWith xper {z | c ≤ LE2.dot (det p cg.vJ • (-p.2, p.1)) z} h ∧
      Colle35.PeriodicOnWith xper {z | c ≤ LE2.dot (det p cg.vJ • (-p.2, p.1)) z} h') :
    ℓ ∈ Colle45.NonExpansiveLine ϑ := by
  set nℓ : ℤ × ℤ := det p cg.vJ • (-p.2, p.1) with hnℓ
  set R : Set (ℤ × ℤ) := ⋃ i, cg.toChainData.Ahat i with hRdef
  -- geometry of the normal `nℓ`
  have hDvJ : det p cg.vJ ≠ 0 := ColleReg.det_ne_zero_of_dot cg.vJ_ne cg.dot_nJ_vJ cg.dot_nJ_p
  have hnp : LE2.dot nℓ p = 0 := by
    simp only [hnℓ, LE2.dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
  have hnv : 0 < LE2.dot nℓ cg.vJ := by
    have : LE2.dot nℓ cg.vJ = det p cg.vJ * det p cg.vJ := by
      simp only [hnℓ, LE2.dot, det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
    rw [this]; exact mul_self_pos.mpr hDvJ
  have hvl_tan : LE2.dot nℓ vl = 0 := by
    have : LE2.dot nℓ vl = det p cg.vJ * det p vl := by
      simp only [hnℓ, LE2.dot, det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
    rw [this, hdet_vl, mul_zero]
  have hnℓ0 : nℓ ≠ 0 := by
    intro h0
    have h1 : LE2.dot nℓ cg.vJ = 0 := by rw [h0]; simp [LE2.dot]
    exact hnv.ne' h1
  -- block 1: the half-plane `{c ≤ dot nℓ ·}` is swallowed by `R` along `p`
  obtain ⟨z₀, hz₀, hz₀c⟩ := hatt
  have hexh : ∀ z, c ≤ LE2.dot nℓ z → ∃ t : ℕ, z + (t : ℤ) • p ∈ R := by
    intro z hz
    exact exists_nat_smul_add_mem_of_dot_le hRconv hz₀ hp_ne cg.rec_p cg.rec_vJ hnp hnv z
      (hz₀c ▸ hz)
  -- accumulation point `z_per` of `{T^{t p} ϑ}`
  have hϑfin : (Set.range ϑ).Finite := BL.finite_range_of_mem_orbitClosure hξ.1.1 hϑ_mem
  obtain ⟨y, hy⟩ := Colle3.exists_accPointAlong hϑfin p
  -- block 2
  obtain ⟨hy_eq, hy_nd⟩ := accPointAlong_eq_on_halfPlane_and_not_doublyPeriodic
    cg.rec_p hexh hagree hp_per hvl_tan hnfp hy
  have hy_memξ : y ∈ orbitClosure ξ := Colle3.mem_orbitClosure_of_accPointAlong hϑ_mem hy
  have hy_memϑ : y ∈ orbitClosure ϑ :=
    Colle3.mem_orbitClosure_of_accPointAlong (self_mem_orbitClosure ϑ) hy
  -- block 3: `z_per|ℋ(ℓ^(−))` periodic along `p` ⟹ `z_per` periodic along `p`
  have hlocal : ∀ z, c ≤ LE2.dot nℓ z → y (z + p) = y z := by
    intro z hz
    have hz' : c ≤ LE2.dot nℓ (z + p) := by rw [LE2.dot_add, hnp, add_zero]; exact hz
    rw [hy_eq _ hz', hy_eq _ hz]
    show xper (z + p + (K : ℤ) • vl) = xper (z + (K : ℤ) • vl)
    rw [add_right_comm, eval_add_of_mem_Per hp_per]
  obtain ⟨k, hk0, hkp⟩ := exists_zsmul_mem_Per_of_halfPlane_period hξ hy_memξ hnℓ0 hp_ne hnp
    hlocal
  -- `ℓ ⊥ p` from `ℓ ⊥ vl` and `p ∥ vl`
  have hℓp : LE2.dot ℓ p = 0 := by
    obtain ⟨k', l, hk', hkl⟩ := Colle.exists_common_multiple_of_det_eq_zero hp_ne hvl_ne hdet_vl
    have h1 : LE2.dot ℓ (k' • p) = LE2.dot ℓ (l • vl) := by rw [hkl]
    have h2 : LE2.dot ℓ (k' • p) = k' * LE2.dot ℓ p := by
      simp only [LE2.dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
    have h3 : LE2.dot ℓ (l • vl) = l * LE2.dot ℓ vl := by
      simp only [LE2.dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
    rw [h2, h3, hdet_ℓ, mul_zero] at h1
    exact (mul_eq_zero.mp h1).resolve_left hk'
  have hperp : LE2.dot ℓ (k • p) = 0 := by
    have : LE2.dot ℓ (k • p) = k * LE2.dot ℓ p := by
      simp only [LE2.dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
    rw [this, hℓp, mul_zero]
  have hkp0 : k • p ≠ 0 := smul_ne_zero hk0 hp_ne
  -- block 4
  have hyfin : (Set.range y).Finite := BL.finite_range_of_mem_orbitClosure hξ.1.1 hy_memξ
  obtain ⟨hℓy, -, -⟩ := mem_nonExpansiveLine_of_period_of_not_doublyPeriodic hyfin hℓ_nel.1
    hkp hkp0 hperp hy_nd
  exact nonExpansiveLine_mono_of_mem_orbitClosure hy_memϑ hℓy


end Nivat.Claim414
