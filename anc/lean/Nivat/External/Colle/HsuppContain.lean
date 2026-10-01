/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.HsuppRoomCone
import Nivat.External.Colle.PolyChainSum
import Nivat.External.Colle.EnvTranslate
import Nivat.External.Colle.DecompData
import Nivat.External.Colle.ChainAssemble
import Nivat.External.Colle.HsuppAssemble
import Nivat.External.Colle.AhatMono

/-!
# `HsuppContain` — the full-zonotope anchored containment `hcont`

Lane `lane-hsupp`, dispatched by team-lead 2026-09-22:

`hcont : ∀ b ∈ Sphi, V + (b − a) ∈ B` — the full-zonotope version of `hsuppZ` (no `erase i`,
ALL generators), for `a`/`V` the `−w` ends of `Sphi`'s / `B`'s `m`-lowest face
(`w := dir (-m)`).

## Route (revised 2026-09-22, simpler than first planned)

`shift_subset_of_suppVal_le` (`EnvTranslate.lean:78`) reduces `hcont` to
`∀ n ∈ E B, suppVal Sphi n - dot n a ≤ suppVal B n - dot n V`.

`a`/`V` are pinned to `faceStart Sphi (-m)` / `faceStart B (-m)` via
`HsuppRoomCone.a_eq_faceStart` — pure algebra from `ha_min`/`ha_end`, no zonotope
machinery needed.

For the main inequality, **the ccw/cw branches need no generator-level machinery at
all**: applying `PolyChainSum.chain_ccw_scalar_final`/`chain_cw_scalar_final` to `Sphi`
and to `B` separately (same `ν₀ := -m`, same `n`) and subtracting gives exactly the
target, termwise, from `hEeq : E B = E Sphi` (so the `Arc` filter set is identical) and
`henv`'s face-length domination (`faceLen Sphi ν ≤ faceLen B ν` for `ν ∈ E B`) — every
summand on both sides shares the same nonnegative `det` factor. The `n = -m` case is
trivial (`suppVal_eq` at `faceStart`, both sides collapse to `0 ≤ 0`).

`n = m` (where `det (-m) m = 0` blocks both chain identities) is handled by a generic
`width_identity` (mirrors `HsuppAssemble.case_eq_nℓ`'s nonempty-`Arc` branch, generalized
to any lattice-convex `T`, stripped of the `g`/generator-specific machinery), applied to
`Sphi` and to `B` and subtracted termwise exactly as in `dominance_ccw`. The remaining gap
was `arc_nonempty_of_posArea`: a positive-area convex region can never have `-m, m ∈ E T`
chain-adjacent. Proved (lane `lane-hroom-close`, 2026-09-22) directly from `isFrame_E`:
taking `c := dir (-m)` (nonzero, and `det (-m) c > 0` since `c` is `-m`'s own edge
direction), `isFrame_E` writes `c` as a nonnegative combination `a • n₁ + b • n₂` of two
edges `n₁, n₂ ∈ E T`; pairing with `det (-m) ·` (ℝ-linear) forces `det (-m) n₁ > 0` or
`det (-m) n₂ > 0`, since both cannot be `≤ 0` while `a, b ≥ 0` and the combination is
positive. No closing-polygon sum identity or `E T = {-m, m}` degeneracy argument needed.

## Status (2026-09-22)

`hcont`: 0 sorry, axioms `[propext, Classical.choice, Quot.sound]`. `a`/`V` pinning,
`faceLen` domination, the `n = -m` case, the ccw/cw branches, `width_identity` and
`arc_nonempty_of_posArea` for the `n = m` case, and the final
`shift_subset_of_suppVal_le` assembly are all proved.
-/

set_option autoImplicit false

namespace Nivat.HsuppContain

open Nivat Nivat.LE2 Nivat.Colle35 Finset

variable {η : Config ℤ} (d : DecompDataZ η)
variable {B : Set (ℤ × ℤ)} (hBfin : B.Finite) (hBne : B.Nonempty)
  (hBarea : PosArea B) (hlcB : IsLatticeConvexRegion B)
variable {m w a V : ℤ × ℤ}
  (hw_eq : w = dir (-m)) (hm_ne : m ≠ 0)
  (hEeq : E B = E (↑d.toDecompData.Sphi : Set (ℤ × ℤ)))
  (hnegm_mem : -m ∈ E (↑d.toDecompData.Sphi : Set (ℤ × ℤ)))
  (henv : ∀ n ∈ E B,
    (face (↑d.toDecompData.Sphi : Set (ℤ × ℤ)) n).encard ≤ (face B n).encard)
  (ha_mem : a ∈ (↑d.toDecompData.Sphi : Set (ℤ × ℤ)))
  (ha_min : ∀ b ∈ (↑d.toDecompData.Sphi : Set (ℤ × ℤ)), dot m a ≤ dot m b)
  (ha_end : ∀ b ∈ (↑d.toDecompData.Sphi : Set (ℤ × ℤ)), dot m b = dot m a →
    ∃ t : ℕ, b = a + (t : ℤ) • w)
  (hV_mem : V ∈ B)
  (hV_min : ∀ b ∈ B, dot m V ≤ dot m b)
  (hV_end : ∀ b ∈ B, dot m b = dot m V → ∃ t : ℕ, b = V + (t : ℤ) • w)

/-! ## §1. Pinning `a`, `V` to `faceStart` -/

include hEeq hnegm_mem in
theorem hnegm_mem_B : -m ∈ E B := by rw [hEeq]; exact hnegm_mem

include d hw_eq hm_ne hnegm_mem ha_mem ha_min ha_end in
theorem a_eq : a = Nivat.PolyChain.faceStart (↑d.toDecompData.Sphi : Set (ℤ × ℤ)) (-m) :=
  Nivat.HsuppRoomCone.a_eq_faceStart d.toDecompData.Sphi.finite_toSet (Nivat.ChainAsm.isLatticeConvexRegion_coe d.Sphi_conv) hw_eq
    (Nivat.HsuppRoomCone.w_ne_zero_of_dir_neg_m hw_eq hm_ne) hnegm_mem ha_mem ha_min ha_end

include d hBfin hlcB hw_eq hm_ne hEeq hnegm_mem hV_mem hV_min hV_end in
theorem V_eq : V = Nivat.PolyChain.faceStart B (-m) :=
  Nivat.HsuppRoomCone.a_eq_faceStart hBfin hlcB hw_eq
    (Nivat.HsuppRoomCone.w_ne_zero_of_dir_neg_m hw_eq hm_ne) (hnegm_mem_B d hEeq hnegm_mem)
    hV_mem hV_min hV_end

/-! ## §2. Face-length domination, direct from `henv` -/

include d hBfin henv in
theorem faceLen_dom {ν : ℤ × ℤ} (hνB : ν ∈ E B) :
    (Nivat.PolyChain.faceLen (↑d.toDecompData.Sphi : Set (ℤ × ℤ)) ν : ℤ) ≤
      (Nivat.PolyChain.faceLen B ν : ℤ) := by
  have hSfin : (face (↑d.toDecompData.Sphi : Set (ℤ × ℤ)) ν).Finite :=
    d.toDecompData.Sphi.finite_toSet.subset (face_subset _ _)
  have hBffin : (face B ν).Finite := hBfin.subset (face_subset _ _)
  obtain ⟨n1, hn1⟩ := hSfin.exists_encard_eq_coe
  obtain ⟨n2, hn2⟩ := hBffin.exists_encard_eq_coe
  have hle := henv ν hνB
  rw [hn1, hn2] at hle
  have hn12 : n1 ≤ n2 := by exact_mod_cast hle
  unfold Nivat.PolyChain.faceLen
  rw [hn1, hn2]
  have hsub : n1 - 1 ≤ n2 - 1 := Nat.sub_le_sub_right hn12 1
  simp only [ENat.toNat_natCast]
  exact_mod_cast hsub

/-! ## §3. The `n = -m` case (trivial) -/

include d hBfin hlcB hw_eq hm_ne hEeq hnegm_mem ha_mem ha_min ha_end hV_mem hV_min
  hV_end in
theorem dominance_at_negm :
    suppVal (↑d.toDecompData.Sphi : Set (ℤ × ℤ)) (-m) - dot (-m) a ≤
      suppVal B (-m) - dot (-m) V := by
  rw [a_eq d hw_eq hm_ne hnegm_mem ha_mem ha_min ha_end,
    V_eq d hBfin hlcB hw_eq hm_ne hEeq hnegm_mem hV_mem hV_min hV_end]
  rw [suppVal_eq (Nivat.PolyChain.faceStart_mem d.toDecompData.Sphi.finite_toSet hnegm_mem),
    suppVal_eq (Nivat.PolyChain.faceStart_mem hBfin (hnegm_mem_B d hEeq hnegm_mem))]
  simp

/-! ## §4. The ccw/cw branches: termwise face-length domination, no generator machinery -/

include d hBfin hBarea hlcB hw_eq hm_ne hEeq hnegm_mem henv ha_mem ha_min ha_end hV_mem
  hV_min hV_end in
/-- `0 < det (-m) n` (ccw): apply `chain_ccw_scalar_final` to `Sphi` and to `B`, subtract
termwise using `faceLen_dom`. -/
theorem dominance_ccw {n : ℤ × ℤ} (hnB : n ∈ E B) (hpos : 0 < det (-m) n) :
    suppVal (↑d.toDecompData.Sphi : Set (ℤ × ℤ)) n - dot n a ≤ suppVal B n - dot n V := by
  have hnS : n ∈ E (↑d.toDecompData.Sphi : Set (ℤ × ℤ)) := hEeq ▸ hnB
  have hSphifin : (↑d.toDecompData.Sphi : Set (ℤ × ℤ)).Finite := d.toDecompData.Sphi.finite_toSet
  rw [a_eq d hw_eq hm_ne hnegm_mem ha_mem ha_min ha_end,
    V_eq d hBfin hlcB hw_eq hm_ne hEeq hnegm_mem hV_mem hV_min hV_end]
  have hS := Nivat.PolyChainSum.chain_ccw_scalar_final hSphifin (Nivat.ChainAsm.isLatticeConvexRegion_coe d.Sphi_conv) hnegm_mem hnS hpos
  have hB := Nivat.PolyChainSum.chain_ccw_scalar_final hBfin hlcB (hnegm_mem_B d hEeq hnegm_mem)
    hnB hpos
  rw [hS, hB]
  have hArceq : (finite_E_of_finite hSphifin).toFinset.filter
      (fun ν => 0 < det (-m) ν ∧ 0 < det ν n) =
      (finite_E_of_finite hBfin).toFinset.filter (fun ν => 0 < det (-m) ν ∧ 0 < det ν n) := by
    ext ν
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset, hEeq]
  rw [hArceq]
  apply add_le_add
  · exact mul_le_mul_of_nonneg_right (faceLen_dom d hBfin henv (hnegm_mem_B d hEeq hnegm_mem))
      hpos.le
  · apply Finset.sum_le_sum
    intro ν hν
    have hνB : ν ∈ E B := (finite_E_of_finite hBfin).mem_toFinset.mp (Finset.mem_filter.mp hν).1
    have hνpos : 0 < det ν n := (Finset.mem_filter.mp hν).2.2
    exact mul_le_mul_of_nonneg_right (faceLen_dom d hBfin henv hνB) hνpos.le

include d hBfin hBarea hlcB hw_eq hm_ne hEeq hnegm_mem henv ha_mem ha_min ha_end hV_mem
  hV_min hV_end in
/-- `0 < det n (-m)` (cw): the symmetric argument via `chain_cw_scalar_final`. -/
theorem dominance_cw {n : ℤ × ℤ} (hnB : n ∈ E B) (hpos : 0 < det n (-m)) :
    suppVal (↑d.toDecompData.Sphi : Set (ℤ × ℤ)) n - dot n a ≤ suppVal B n - dot n V := by
  have hnS : n ∈ E (↑d.toDecompData.Sphi : Set (ℤ × ℤ)) := hEeq ▸ hnB
  have hSphifin : (↑d.toDecompData.Sphi : Set (ℤ × ℤ)).Finite := d.toDecompData.Sphi.finite_toSet
  rw [a_eq d hw_eq hm_ne hnegm_mem ha_mem ha_min ha_end,
    V_eq d hBfin hlcB hw_eq hm_ne hEeq hnegm_mem hV_mem hV_min hV_end]
  have hS := Nivat.PolyChainSum.chain_cw_scalar_final hSphifin (Nivat.ChainAsm.isLatticeConvexRegion_coe d.Sphi_conv) hnegm_mem hnS hpos
  have hB := Nivat.PolyChainSum.chain_cw_scalar_final hBfin hlcB (hnegm_mem_B d hEeq hnegm_mem)
    hnB hpos
  rw [hS, hB]
  have hArceq : (finite_E_of_finite hSphifin).toFinset.filter
      (fun ν => 0 < det ν (-m) ∧ 0 < det n ν) =
      (finite_E_of_finite hBfin).toFinset.filter (fun ν => 0 < det ν (-m) ∧ 0 < det n ν) := by
    ext ν
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset, hEeq]
  rw [hArceq]
  apply Finset.sum_le_sum
  intro ν hν
  have hνB : ν ∈ E B := (finite_E_of_finite hBfin).mem_toFinset.mp (Finset.mem_filter.mp hν).1
  have hνpos : 0 < det n ν := (Finset.mem_filter.mp hν).2.2
  exact mul_le_mul_of_nonneg_right (faceLen_dom d hBfin henv hνB) hνpos.le

/-! ## §5. The `n = m` boundary case, via a generic width identity

`chain_ccw_scalar_final`/`chain_cw_scalar_final` both need `det (-m) m ≠ 0`, which fails
exactly at `n = m`. `width_identity` below proves the boundary identity directly
(`HsuppAssemble.case_eq_nℓ`'s nonempty-`Arc` branch, generalized to any lattice-convex
`T` and stripped of the `g`/generator-specific machinery not needed here), and then
`dominance_at_m` applies it to `Sphi` and to `B` and subtracts termwise exactly as in
`dominance_ccw`. `hArcNe` (below, via `arc_nonempty_of_posArea`) is the fact that a
positive-area convex region can never have `μ, -μ` chain-adjacent — i.e. `Arc` is always
nonempty. -/

include d hBfin hBarea hlcB hw_eq hm_ne hEeq hnegm_mem henv ha_mem ha_min ha_end hV_mem
  hV_min hV_end in
/-- A positive-area lattice-convex region cannot have
two antipodal edges `-m, m ∈ E T` chain-adjacent: strict convexity forces every
consecutive turn to be `< 180°`, so `Arc := {ν ∈ E T | 0 < det (-m) ν}` is always
nonempty when `-m, m ∈ E T` and `T` has `PosArea`. -/
theorem arc_nonempty_of_posArea {T : Set (ℤ × ℤ)} (hTfin : T.Finite)
    (hTarea : PosArea T) (hTlc : IsLatticeConvexRegion T) (hnegmT : -m ∈ E T)
    (hmT : m ∈ E T) :
    ((finite_E_of_finite hTfin).toFinset.filter (fun ν => 0 < det (-m) ν)).Nonempty := by
  classical
  have hTne : T.Nonempty := by
    obtain ⟨z, hz⟩ := (mem_E_iff.mp hnegmT).2.nonempty
    exact ⟨z, face_subset T (-m) hz⟩
  have hmne : m ≠ 0 := (mem_E_iff.mp hmT).1.ne_zero
  have hpne : dir (-m) ≠ 0 := Nivat.PolyChainSum.dir_ne_zero (neg_ne_zero.mpr hmne)
  have hpos : 0 < dot (dir (-m)) (dir (-m)) := by
    simp only [ne_eq, Prod.ext_iff, not_and_or] at hpne
    rcases hpne with h | h
    · simp only [dot]; nlinarith [mul_self_nonneg (dir (-m)).2, mul_self_pos.mpr h]
    · simp only [dot]; nlinarith [mul_self_nonneg (dir (-m)).1, mul_self_pos.mpr h]
  set c : ℝ × ℝ := toReal (dir (-m)) with hcdef
  have hcne : c ≠ 0 := by
    intro hz
    apply hpne
    have h1 : ((dir (-m)).1 : ℝ) = 0 := by
      have := congrArg Prod.fst hz; simpa [hcdef, toReal] using this
    have h2 : ((dir (-m)).2 : ℝ) = 0 := by
      have := congrArg Prod.snd hz; simpa [hcdef, toReal] using this
    have e1 : (dir (-m)).1 = 0 := by exact_mod_cast h1
    have e2 : (dir (-m)).2 = 0 := by exact_mod_cast h2
    exact Prod.ext e1 e2
  obtain ⟨n1, n2, a, b, hn1, hn2, ha, hb, hc1, hc2, v, hvle, hvn1, hvn2⟩ :=
    isFrame_E hTfin hTne hTarea c hcne
  have hDc : ((-m).1 : ℝ) * c.2 - ((-m).2 : ℝ) * c.1 =
      a * ((det (-m) n1 : ℤ) : ℝ) + b * ((det (-m) n2 : ℤ) : ℝ) := by
    have e1 : ((det (-m) n1 : ℤ) : ℝ) = ((-m).1 : ℝ) * (n1.2 : ℝ) - ((-m).2 : ℝ) * (n1.1 : ℝ) := by
      simp only [det]; push_cast; ring
    have e2 : ((det (-m) n2 : ℤ) : ℝ) = ((-m).1 : ℝ) * (n2.2 : ℝ) - ((-m).2 : ℝ) * (n2.1 : ℝ) := by
      simp only [det]; push_cast; ring
    rw [e1, e2, hc1, hc2]; ring
  have hval : ((-m).1 : ℝ) * c.2 - ((-m).2 : ℝ) * c.1 = ((det (-m) (dir (-m)) : ℤ) : ℝ) := by
    simp only [hcdef, toReal, det]; push_cast; ring
  have hdd : det (-m) (dir (-m)) = dot (dir (-m)) (dir (-m)) :=
    (Nivat.PolyChainSum.dot_dir_left (-m) (dir (-m))).symm
  have hDcpos : (0 : ℝ) < ((-m).1 : ℝ) * c.2 - ((-m).2 : ℝ) * c.1 := by
    rw [hval, hdd]; exact_mod_cast hpos
  rw [hDc] at hDcpos
  have hexists : 0 < det (-m) n1 ∨ 0 < det (-m) n2 := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨h1, h2⟩ := hcon
    have h1' : ((det (-m) n1 : ℤ) : ℝ) ≤ 0 := by exact_mod_cast h1
    have h2' : ((det (-m) n2 : ℤ) : ℝ) ≤ 0 := by exact_mod_cast h2
    nlinarith [mul_nonneg ha (neg_nonneg.mpr h1'), mul_nonneg hb (neg_nonneg.mpr h2')]
  rcases hexists with h | h
  · exact ⟨n1, Finset.mem_filter.mpr ⟨(finite_E_of_finite hTfin).mem_toFinset.mpr hn1, h⟩⟩
  · exact ⟨n2, Finset.mem_filter.mpr ⟨(finite_E_of_finite hTfin).mem_toFinset.mpr hn2, h⟩⟩

theorem width_identity {T : Set (ℤ × ℤ)} (hTfin : T.Finite) (hTarea : PosArea T)
    (hTlc : IsLatticeConvexRegion T) {μ : ℤ × ℤ} (hμne : μ ≠ 0)
    (hnegμ : -μ ∈ E T) (hμ : μ ∈ E T)
    (hArcNe : ((finite_E_of_finite hTfin).toFinset.filter
      (fun ν => 0 < det (-μ) ν)).Nonempty) :
    suppVal T μ - dot μ (Nivat.PolyChain.faceStart T (-μ)) =
      ∑ ν ∈ (finite_E_of_finite hTfin).toFinset.filter (fun ν => 0 < det (-μ) ν),
        (Nivat.PolyChain.faceLen T ν : ℤ) * det ν μ := by
  classical
  have hidnty : ∀ ν : ℤ × ℤ, det ν μ = det (-μ) ν := fun ν => (Nivat.HsuppAssemble.det_neg_left_swap μ ν).symm
  have hzero : det (-μ) μ = 0 := by rw [Nivat.HsuppAssemble.det_neg_left_swap]; exact det_self μ
  have hdotdir : ∀ x ν : ℤ × ℤ, dot x (dir ν) = det ν x := fun x ν => by
    rw [dot_comm]; exact Nivat.HsuppRoomCone.dot_dir_eq_det ν x
  set Arc := (finite_E_of_finite hTfin).toFinset.filter
      (fun ν => 0 < det (-μ) ν) with hArcdef
  obtain ⟨ν', hν'Arc, hν'max⟩ := Nivat.PolyChainSum.exists_max_det (S := Arc) (e := -μ)
    (neg_ne_zero.mpr hμne) (fun ν hν => (Finset.mem_filter.mp hν).2) hArcNe
  have hν'E' : ν' ∈ (finite_E_of_finite hTfin).toFinset :=
    (Finset.mem_filter.mp hν'Arc).1
  have hν'E : ν' ∈ E T := (finite_E_of_finite hTfin).mem_toFinset.mp hν'E'
  have hν'pos : 0 < det (-μ) ν' := (Finset.mem_filter.mp hν'Arc).2
  have hposμ : 0 < det ν' μ := by rw [hidnty]; exact hν'pos
  have hadj : ∀ x ∈ E T, ¬ (0 < det ν' x ∧ 0 < det x μ) := by
    rintro x hx ⟨hx1, hx2⟩
    have hxArc : x ∈ Arc := by
      rw [hArcdef, Finset.mem_filter, (finite_E_of_finite hTfin).mem_toFinset]
      exact ⟨hx, by rw [← hidnty]; exact hx2⟩
    exact hν'max x hxArc hx1
  have hchain := Nivat.PolyChainSum.chain_ccw_final hTfin hTlc hnegμ hν'E hν'pos
  have hshare := Nivat.PolyChain.adjacent_shared_vertex hTfin hTlc hν'E hμ hposμ hadj
  have hArc'eq : (finite_E_of_finite hTfin).toFinset.filter
      (fun ν => 0 < det (-μ) ν ∧ 0 < det ν ν') = Arc.erase ν' := by
    apply Finset.ext
    intro ν
    rw [Finset.mem_filter, Finset.mem_erase, hArcdef, Finset.mem_filter]
    constructor
    · rintro ⟨hνE, hν1, hν2⟩
      refine ⟨fun hcon => ?_, hνE, hν1⟩
      rw [hcon, det_self] at hν2
      exact absurd hν2 (lt_irrefl 0)
    · rintro ⟨hne, hνE, hν1⟩
      refine ⟨hνE, hν1, ?_⟩
      have hνT : ν ∈ E T := (finite_E_of_finite hTfin).mem_toFinset.mp hνE
      have hνArc : ν ∈ Arc := by rw [hArcdef, Finset.mem_filter]; exact ⟨hνE, hν1⟩
      have hle : det ν' ν ≤ 0 := by
        by_contra hcon; push_neg at hcon; exact hν'max ν hνArc hcon
      have hne0 : det ν' ν ≠ 0 := by
        intro hz
        have hprimν' : Prim ν' := (mem_E_iff.mp hν'E).1
        have hprimν : Prim ν := (mem_E_iff.mp hνT).1
        rcases eq_or_neg_of_prim_of_det_eq_zero hprimν' hprimν hz with h | h
        · exact hne h
        · rw [h] at hν1
          have heq2 : det (-μ) (-ν') = - det (-μ) ν' := by
            simp only [det, Prod.fst_neg, Prod.snd_neg]; ring
          rw [heq2] at hν1
          linarith
      have hltz : det ν' ν < 0 := lt_of_le_of_ne hle hne0
      have hanti : det ν' ν = - det ν ν' := by simp only [det]; ring
      rw [hanti] at hltz
      linarith
  rw [hArc'eq] at hchain
  have hArcsum : ∀ f : ℤ × ℤ → ℤ × ℤ,
      (∑ ν ∈ Arc.erase ν', f ν) + f ν' = ∑ ν ∈ Arc, f ν :=
    fun f => Finset.sum_erase_add Arc f hν'Arc
  have hvec : Nivat.PolyChain.faceStart T μ - Nivat.PolyChain.faceStart T (-μ) =
      (Nivat.PolyChain.faceLen T (-μ) : ℤ) • dir (-μ) +
        ∑ ν ∈ Arc, (Nivat.PolyChain.faceLen T ν : ℤ) • dir ν := by
    have e1 : Nivat.PolyChain.faceStart T μ - Nivat.PolyChain.faceStart T (-μ) =
        (Nivat.PolyChain.faceStart T ν' - Nivat.PolyChain.faceStart T (-μ)) +
          (Nivat.PolyChain.faceLen T ν' : ℤ) • dir ν' := by
      rw [← hshare]; abel
    rw [e1, hchain, ← hArcsum (fun ν => (Nivat.PolyChain.faceLen T ν : ℤ) • dir ν)]
    abel
  have hsv : suppVal T μ = dot μ (Nivat.PolyChain.faceStart T μ) :=
    Nivat.PolyChainSum.suppVal_faceStart (Nivat.PolyChainSum.hseg_real hTfin hTlc) hμ
  have hdotvec : dot μ (Nivat.PolyChain.faceStart T μ) -
      dot μ (Nivat.PolyChain.faceStart T (-μ)) =
      (Nivat.PolyChain.faceLen T (-μ) : ℤ) * det (-μ) μ +
        ∑ ν ∈ Arc, (Nivat.PolyChain.faceLen T ν : ℤ) * det ν μ := by
    have h1 : dot μ (Nivat.PolyChain.faceStart T μ - Nivat.PolyChain.faceStart T (-μ)) =
        dot μ ((Nivat.PolyChain.faceLen T (-μ) : ℤ) • dir (-μ) +
          ∑ ν ∈ Arc, (Nivat.PolyChain.faceLen T ν : ℤ) • dir ν) := by rw [hvec]
    rw [dot_sub] at h1
    rw [dot_add, Nivat.PolyChainSum.dot_zsmul_right, Nivat.PolyChainSum.dot_sum] at h1
    rw [h1]
    congr 1
    · rw [hdotdir]
    · exact Finset.sum_congr rfl fun ν _ => by
        rw [Nivat.PolyChainSum.dot_zsmul_right, hdotdir]
  rw [hzero, mul_zero, zero_add] at hdotvec
  rw [hsv, hdotvec]

include d hBfin hBarea hlcB hw_eq hm_ne hEeq hnegm_mem henv ha_mem ha_min ha_end hV_mem
  hV_min hV_end in
theorem dominance_at_m (hmB : m ∈ E B) :
    suppVal (↑d.toDecompData.Sphi : Set (ℤ × ℤ)) m - dot m a ≤ suppVal B m - dot m V := by
  have hSphifin : (↑d.toDecompData.Sphi : Set (ℤ × ℤ)).Finite := d.toDecompData.Sphi.finite_toSet
  have hSphilc : IsLatticeConvexRegion (↑d.toDecompData.Sphi : Set (ℤ × ℤ)) :=
    Nivat.ChainAsm.isLatticeConvexRegion_coe d.Sphi_conv
  have hSphiarea : PosArea (↑d.toDecompData.Sphi : Set (ℤ × ℤ)) :=
    Nivat.AhatMono.posArea_Sphi d.toDecompData
  have hmS : m ∈ E (↑d.toDecompData.Sphi : Set (ℤ × ℤ)) := hEeq ▸ hmB
  have hArcNe := arc_nonempty_of_posArea d hBfin hBarea hlcB hw_eq hm_ne hEeq hnegm_mem henv
    ha_mem ha_min ha_end hV_mem hV_min hV_end hSphifin hSphiarea hSphilc hnegm_mem hmS
  have hArcEeq : (finite_E_of_finite hSphifin).toFinset.filter (fun ν => 0 < det (-m) ν) =
      (finite_E_of_finite hBfin).toFinset.filter (fun ν => 0 < det (-m) ν) := by
    ext ν
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset, hEeq]
  have hArcNeB : ((finite_E_of_finite hBfin).toFinset.filter
      (fun ν => 0 < det (-m) ν)).Nonempty := hArcEeq ▸ hArcNe
  have hS := width_identity hSphifin hSphiarea hSphilc hm_ne hnegm_mem hmS hArcNe
  have hB := width_identity hBfin hBarea hlcB hm_ne (hnegm_mem_B d hEeq hnegm_mem) hmB hArcNeB
  rw [a_eq d hw_eq hm_ne hnegm_mem ha_mem ha_min ha_end,
    V_eq d hBfin hlcB hw_eq hm_ne hEeq hnegm_mem hV_mem hV_min hV_end, hS, hB, hArcEeq]
  apply Finset.sum_le_sum
  intro ν hν
  have hνB : ν ∈ E B := (finite_E_of_finite hBfin).mem_toFinset.mp (Finset.mem_filter.mp hν).1
  have hνpos : 0 < det (-m) ν := (Finset.mem_filter.mp hν).2
  have hνmpos : 0 < det ν m := by
    have hidnty : det ν m = det (-m) ν := (Nivat.HsuppAssemble.det_neg_left_swap m ν).symm
    rw [hidnty]; exact hνpos
  exact mul_le_mul_of_nonneg_right (faceLen_dom d hBfin henv hνB) hνmpos.le

/-! ## §6. Assembly -/

include d hBfin hBarea hlcB hw_eq hm_ne hEeq hnegm_mem henv ha_mem ha_min ha_end hV_mem
  hV_min hV_end in
theorem dominance_all : ∀ n ∈ E B,
    suppVal (↑d.toDecompData.Sphi : Set (ℤ × ℤ)) n - dot n a ≤ suppVal B n - dot n V := by
  intro n hnB
  by_cases hnm : n = m
  · subst hnm; exact dominance_at_m d hBfin hBarea hlcB hw_eq hm_ne hEeq hnegm_mem henv
      ha_mem ha_min ha_end hV_mem hV_min hV_end hnB
  by_cases hnnegm : n = -m
  · subst hnnegm
    exact dominance_at_negm d hBfin hlcB hw_eq hm_ne hEeq hnegm_mem ha_mem ha_min ha_end
      hV_mem hV_min hV_end
  · have hnS : n ∈ E (↑d.toDecompData.Sphi : Set (ℤ × ℤ)) := hEeq ▸ hnB
    have hprimnegm : Prim (-m) := (mem_E_iff.mp hnegm_mem).1
    have hprimn : Prim n := (mem_E_iff.mp hnS).1
    have hdetne : det (-m) n ≠ 0 := by
      intro hz
      rcases eq_or_neg_of_prim_of_det_eq_zero hprimnegm hprimn hz with h | h
      · exact hnnegm h
      · exact hnm (by rw [h, neg_neg])
    rcases lt_or_gt_of_ne hdetne with hlt | hgt
    · have hcw : 0 < det n (-m) := by have := det_skew (-m) n; linarith
      exact dominance_cw d hBfin hBarea hlcB hw_eq hm_ne hEeq hnegm_mem henv ha_mem ha_min
        ha_end hV_mem hV_min hV_end hnB hcw
    · exact dominance_ccw d hBfin hBarea hlcB hw_eq hm_ne hEeq hnegm_mem henv ha_mem ha_min
        ha_end hV_mem hV_min hV_end hnB hgt

include d hBfin hBne hBarea hlcB hw_eq hm_ne hEeq hnegm_mem henv ha_mem ha_min ha_end hV_mem
  hV_min hV_end in
/-- **Main theorem.** The full-zonotope anchored containment: shifting `Sphi` by `V - a`
lands it inside `B`. -/
theorem hcont : ∀ b ∈ (↑d.toDecompData.Sphi : Set (ℤ × ℤ)), V + (b - a) ∈ B := by
  have hshift : shift (V - a) (↑d.toDecompData.Sphi : Set (ℤ × ℤ)) ⊆ B :=
    Nivat.LE2.shift_subset_of_suppVal_le hBfin hBne hBarea hlcB
      d.toDecompData.Sphi.finite_toSet d.Sphi_nonempty (fun n hn => by
        have hd := dominance_all d hBfin hBarea hlcB hw_eq hm_ne hEeq hnegm_mem henv ha_mem
          ha_min ha_end hV_mem hV_min hV_end n hn
        rw [dot_sub]
        linarith)
  intro b hb
  have : b + (V - a) ∈ shift (V - a) (↑d.toDecompData.Sphi : Set (ℤ × ℤ)) := by
    show b + (V - a) - (V - a) ∈ (↑d.toDecompData.Sphi : Set (ℤ × ℤ))
    simpa using hb
  have hmem := hshift this
  have heq : b + (V - a) = V + (b - a) := by abel
  rwa [heq] at hmem

end Nivat.HsuppContain
