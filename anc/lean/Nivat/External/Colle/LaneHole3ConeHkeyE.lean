/-
Copyright (c) 2026 Nivat Formalization Contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lane-hole3-cone
-/
import Nivat.External.Colle.ChainAssemble
import Nivat.External.Colle.ShellSubStrip
import Nivat.External.Colle.LatticeEdges
import Nivat.External.Colle.LeafAJSelect
import Nivat.External.Colle.ShellRegionJ

/-!
# The interior polar-cone leg of `hkey`/`hkeyE` (`b3_colle2.txt:500-506`)

team-lead's assignment (round after `lane-hole3-cone-arc-member.lean` landed): supply the
`0 < ⟪n, w⟫`, `n ≠ J`, `n` on the interior arc `Arc ℓ J` branch of
`Nivat.LaneCdFaceFree.enveloped_of_corners_of_key`'s `hkey`
(`ShellSubStrip.lean:2903`, chosen as the consumer — its `{p, q}` two-corner shape is the one
`face_encard_le_union_of_dom` (`ShellSubStrip.lean:2865`) is stated against; the multi-corner
`C`-based successor at `hkeyE`, `ShellSubStrip.lean:3747`, is lane-hroom-close's, and this
file's conclusion specializes to it for `{p, q} = ↑C` at the caller's choice, not re-derived
here).

**What this assembles.**  `face_encard_le_union_of_dom`'s residual hypothesis is `hdom`
(`⟪n, ·⟫`'s supremum over `Y := ⋃ j, hatOf A kk vl j =: Â_∞` already attained on the finite
level `Â_i`).  §1 below (`hdom_of_mem_E_iUnion`) reduces that to `n ∈ E Â_∞`; §2
(`exists_faceStart_pinned_ccw` / `mem_E_iUnion_of_arc_ccw`, both ported unchanged from
`tmp/wip/lane-hole3-cone-arc-member.lean` — `check1.sh` cannot resolve cross-`tmp/wip` imports
since those files carry no built `.olean`, so the two landed theorems are inlined here rather
than imported) supplies exactly that, for `n := μ ∈ Arc ℓ J`.  §3 is the bridge from that
abstract `Ahat` formulation to the concrete `hatOf A kk vl` formulation the real call site has,
using only binders `ChainDataGeom.ofParts` already carries (`AhatMono`, `hfin`, `maxA` +
`hEnv`).  Nothing new is proved geometrically here beyond what those two files already forced.

**Not encoded here** (per team-lead's scope): the classification that a given `n` actually
falls on this branch (`0 < ⟪n, w⟫`, interior arc) — that is §21's
`recovered_of_sweep_deleted_dot`, supplied by the caller via `hμ : μ ∈ Arc ℓ J`; and
`⟪μ, v⟫ ≤ 0` (the "wedge polar cone" half of the classification, `v := vJ1` at the real call
site) — kept as a hypothesis `hμv`, not re-derived, since judging *which* sign `⟪n_ℓ, ·⟫`-style
quantities take is explicitly lane-tower-hbase's + env-refute's ground (纪律51/56), not mine.
`μ ≠ J` is *not* an independent hypothesis here — `mem_Arc.mp hμ` gives `0 < det μ J`, which
excludes `μ = J` (`det J J = 0`) for free; confirmed with lane-hole3-nlmax 2026-09-24, who
initially offered `det_le_zero_of_swept`/`missing_iff_arc` for it before we found the arc
membership itself already carries it.

**⚠ No call-site wiring yet.**  `hg₁`, `hArcbdd`, `0 < ⟪μ, w⟫`, `⟪μ, v⟫ ≤ 0` are all
left as hypotheses; team-lead's next assignment is to locate `mem_E_of_arc_stabilizes`'s real
main-tree call site and report which of these five arrive free versus still need proof there.
This file has zero importers until that wiring lands. -/

set_option autoImplicit false

namespace Nivat.LaneHole3ConeHkeyE

open Nivat Nivat.LE2 Nivat.MaxEnv Nivat.Colle35 Nivat.PolyChain Nivat.PolyChainSum

/-! ## §1. `hdom` from `n ∈ E Â_∞` (ported from `lane-hole3-cone-hdom.lean`) -/

theorem hdom_of_mem_E_iUnion {A : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ} {vl n : ℤ × ℤ}
    (hmono : ∀ i j, i ≤ j → hatOf A kk vl i ⊆ hatOf A kk vl j)
    (hn : n ∈ E (⋃ j, hatOf A kk vl j)) :
    ∃ i₀ : ℕ, ∀ i, i₀ ≤ i → ∀ g ∈ (⋃ j, hatOf A kk vl j), ∀ y ∈ face (hatOf A kk vl i) n,
      dot n g ≤ dot n y := by
  obtain ⟨z, hzmem, hzmax⟩ := hn.2.nonempty
  obtain ⟨i₀, hzi₀⟩ := Set.mem_iUnion.mp hzmem
  refine ⟨i₀, fun i hi g hg y hy => ?_⟩
  have hzi : z ∈ hatOf A kk vl i := hmono i₀ i hi hzi₀
  exact le_trans (hzmax g hg) (hy.2 z hzi)

/-! ## §2. `μ ∈ E Â_∞` for interior arc normals (ported from
`lane-hole3-cone-arc-member.lean`) -/

theorem exists_faceStart_pinned_ccw
    {Ahat : ℕ → Set (ℤ × ℤ)} {Sphi : Finset (ℤ × ℤ)} {ℓ J μ g₁ : ℤ × ℤ}
    (hfin : ∀ i, (Ahat i).Finite) (hlc : ∀ i, IsLatticeConvexRegion (Ahat i))
    (henv : ∀ i, Enveloped (↑Sphi : Set (ℤ × ℤ)) (Ahat i))
    (hSfin : (E (↑Sphi : Set (ℤ × ℤ))).Finite) (hSarea : PosArea (↑Sphi : Set (ℤ × ℤ)))
    (hℓE : ℓ ∈ E (↑Sphi : Set (ℤ × ℤ))) (hJE : J ∈ E (↑Sphi : Set (ℤ × ℤ)))
    (hℓJ : 0 < det ℓ J)
    (hμ : μ ∈ Nivat.PolyChainSum.Arc (Sphi.finite_toSet) ℓ J)
    (hg₁ : ∀ i, faceStart (Ahat i) ℓ + (faceLen (Ahat i) ℓ : ℤ) • dir ℓ = g₁)
    (hArcbdd : ∀ ν ∈ Nivat.PolyChainSum.Arc (Sphi.finite_toSet) ℓ J,
      ∃ L : ℕ, ∀ i, faceLen (Ahat i) ν ≤ L) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ i₀ : ℕ,
      (∀ i ≥ i₀, faceLen (Ahat (σ i)) μ = faceLen (Ahat (σ i₀)) μ) ∧
      (∀ i ≥ i₀, faceStart (Ahat (σ i)) μ = faceStart (Ahat (σ i₀)) μ) := by
  classical
  obtain ⟨hμE, hℓμ, hμJ⟩ := Nivat.PolyChainSum.mem_Arc.mp hμ
  set T : Finset (ℤ × ℤ) := Nivat.PolyChainSum.Arc (Sphi.finite_toSet) ℓ J with hT_def
  obtain ⟨σ, hσmono, i₀, hr⟩ := Nivat.LeafAJSelect.exists_eventually_const_before
    (Ahat := Ahat) T hfin hArcbdd
  refine ⟨σ, hσmono, i₀, fun i hi => hr μ hμ i hi, fun i hi => ?_⟩
  have hpin : ∀ k, faceStart (Ahat k) μ - g₁
      = ∑ ν ∈ Nivat.PolyChainSum.Arc (Sphi.finite_toSet) ℓ μ,
        (faceLen (Ahat k) ν : ℤ) • dir ν := by
    intro k
    have hEℓ : ℓ ∈ E (Ahat k) := by
      rw [Nivat.AhatEnv.E_eq_of_enveloped hSfin hSarea (henv k)]; exact hℓE
    have hEμ : μ ∈ E (Ahat k) := by
      rw [Nivat.AhatEnv.E_eq_of_enveloped hSfin hSarea (henv k)]; exact hμE
    have hchain := Nivat.PolyChainSum.chain_ccw_final (hfin k) (hlc k) hEℓ hEμ hℓμ
    have hArc : (finite_E_of_finite (hfin k)).toFinset.filter
          (fun ν => 0 < det ℓ ν ∧ 0 < det ν μ)
        = Nivat.PolyChainSum.Arc (Sphi.finite_toSet) ℓ μ :=
      Nivat.LeafAJSelect.Arc_eq_of_enveloped (hfin k) hSfin hSarea (henv k) ℓ μ
    rw [hArc] at hchain
    have hsub : g₁ = faceStart (Ahat k) ℓ + (faceLen (Ahat k) ℓ : ℤ) • dir ℓ := (hg₁ k).symm
    rw [hsub]
    have hre : faceStart (Ahat k) μ - (faceStart (Ahat k) ℓ + (faceLen (Ahat k) ℓ : ℤ) • dir ℓ)
        = (faceStart (Ahat k) μ - faceStart (Ahat k) ℓ) - (faceLen (Ahat k) ℓ : ℤ) • dir ℓ := by
      abel
    rw [hre, hchain]
    abel
  have hArcμ_sub : Nivat.PolyChainSum.Arc (Sphi.finite_toSet) ℓ μ
      ⊆ Nivat.PolyChainSum.Arc (Sphi.finite_toSet) ℓ J :=
    Nivat.LeafAJSelect.Arc_subset_of_mem_Arc (Sphi.finite_toSet) hℓJ hμ
  have hsum_eq : ∑ ν ∈ Nivat.PolyChainSum.Arc (Sphi.finite_toSet) ℓ μ,
        (faceLen (Ahat (σ i)) ν : ℤ) • dir ν
      = ∑ ν ∈ Nivat.PolyChainSum.Arc (Sphi.finite_toSet) ℓ μ,
        (faceLen (Ahat (σ i₀)) ν : ℤ) • dir ν := by
    apply Finset.sum_congr rfl
    intro ν hν
    rw [hr ν (hArcμ_sub hν) i hi]
  have heq : faceStart (Ahat (σ i)) μ - g₁ = faceStart (Ahat (σ i₀)) μ - g₁ :=
    (hpin (σ i)).trans (hsum_eq.trans (hpin (σ i₀)).symm)
  exact sub_left_inj.mp heq

theorem mem_E_iUnion_of_arc_ccw
    {Ahat : ℕ → Set (ℤ × ℤ)} {Sphi : Finset (ℤ × ℤ)} {ℓ J μ g₁ : ℤ × ℤ}
    (hmono : Monotone Ahat)
    (hfin : ∀ i, (Ahat i).Finite) (hlc : ∀ i, IsLatticeConvexRegion (Ahat i))
    (henv : ∀ i, Enveloped (↑Sphi : Set (ℤ × ℤ)) (Ahat i))
    (hSfin : (E (↑Sphi : Set (ℤ × ℤ))).Finite) (hSarea : PosArea (↑Sphi : Set (ℤ × ℤ)))
    (hℓE : ℓ ∈ E (↑Sphi : Set (ℤ × ℤ))) (hJE : J ∈ E (↑Sphi : Set (ℤ × ℤ)))
    (hℓJ : 0 < det ℓ J)
    (hμ : μ ∈ Nivat.PolyChainSum.Arc (Sphi.finite_toSet) ℓ J)
    (hg₁ : ∀ i, faceStart (Ahat i) ℓ + (faceLen (Ahat i) ℓ : ℤ) • dir ℓ = g₁)
    (hArcbdd : ∀ ν ∈ Nivat.PolyChainSum.Arc (Sphi.finite_toSet) ℓ J,
      ∃ L : ℕ, ∀ i, faceLen (Ahat i) ν ≤ L) :
    μ ∈ E (⋃ i, Ahat i) := by
  classical
  obtain ⟨hμE, -, -⟩ := Nivat.PolyChainSum.mem_Arc.mp hμ
  obtain ⟨σ, hσmono, i₀, hlen_stab, hstart_stab⟩ :=
    exists_faceStart_pinned_ccw hfin hlc henv hSfin hSarea hℓE hJE hℓJ hμ hg₁ hArcbdd
  have hμEσ : ∀ j, μ ∈ E (Ahat (σ j)) := fun j => by
    rw [Nivat.AhatEnv.E_eq_of_enveloped hSfin hSarea (henv (σ j))]; exact hμE
  refine Nivat.ShellRegionJ.mem_E_of_arc_stabilizes hmono hσmono hlc hfin
    (fun j _ => hμEσ j) hlen_stab hstart_stab ?_
  exact Nivat.PolyChain.one_le_faceLen (hfin (σ i₀)) (hμEσ i₀)

/-! ## §3. The bridge: `hatOf A kk vl` satisfies `mem_E_iUnion_of_arc_ccw`'s abstract binders -/

variable {α : Type*}

/-- **`hlc` for `hatOf A kk vl`, exported.**  Not a binder of `ChainDataGeom.ofPartsExhaustsInter`
(only `hmono`/`hfin` are), but provable from `maxA` + `hEnv` alone — same three-line argument
already inlined, unexported, in `ChainAssemble.lean:348-350`'s `latticeConvex_iUnion_hatOf`
(re-derived here, not imported from there, per team-lead's instruction not to touch/export out
of that file). -/
theorem isLatticeConvexRegion_hatOf_of_maxA
    (η xper : Config α) (vl : ℤ × ℤ) (S : Finset (ℤ × ℤ))
    (Env : Set (ℤ × ℤ) → Prop) (B A : ℕ → Set (ℤ × ℤ)) (u : ℕ → ℤ × ℤ) (kk : ℕ → ℕ)
    (hEnv : Env = EnvOf (↑S : Set (ℤ × ℤ)))
    (maxA : ∀ i, IsMaxEnvIn Env (canonA η xper vl B u i) (A i)) (i : ℕ) :
    IsLatticeConvexRegion (hatOf A kk vl i) := by
  have henvA : Enveloped (↑S : Set (ℤ × ℤ)) (A i) := by
    have h := envA_of_max maxA i; rwa [hEnv] at h
  rw [Nivat.Colle35.hatOf_eq_shift]
  exact isLatticeConvexRegion_shift _ henvA.1.1

/-- **The bridge**: `hatOf A kk vl` satisfies every structural hypothesis
`mem_E_iUnion_of_arc_ccw` asks of its abstract `Ahat`, from exactly the binders
`ChainDataGeom.ofParts` already carries. -/
theorem mem_E_iUnion_hatOf_of_arc
    (η xper : Config α) (vl : ℤ × ℤ) (S : Finset (ℤ × ℤ))
    (Env : Set (ℤ × ℤ) → Prop) (B A : ℕ → Set (ℤ × ℤ)) (u : ℕ → ℤ × ℤ) (kk : ℕ → ℕ)
    (hEnv : Env = EnvOf (↑S : Set (ℤ × ℤ)))
    (maxA : ∀ i, IsMaxEnvIn Env (canonA η xper vl B u i) (A i))
    (hfin : ∀ i, (hatOf A kk vl i).Finite)
    (AhatMono : ∀ i j, i ≤ j → hatOf A kk vl i ⊆ hatOf A kk vl j)
    {ℓ J μ g₁ : ℤ × ℤ}
    (hSfin : (E (↑S : Set (ℤ × ℤ))).Finite) (hSarea : PosArea (↑S : Set (ℤ × ℤ)))
    (hℓE : ℓ ∈ E (↑S : Set (ℤ × ℤ))) (hJE : J ∈ E (↑S : Set (ℤ × ℤ)))
    (hℓJ : 0 < det ℓ J)
    (hμ : μ ∈ Nivat.PolyChainSum.Arc (S.finite_toSet) ℓ J)
    (hg₁ : ∀ i, faceStart (hatOf A kk vl i) ℓ + (faceLen (hatOf A kk vl i) ℓ : ℤ) • dir ℓ = g₁)
    (hArcbdd : ∀ ν ∈ Nivat.PolyChainSum.Arc (S.finite_toSet) ℓ J,
      ∃ L : ℕ, ∀ i, faceLen (hatOf A kk vl i) ν ≤ L) :
    μ ∈ E (⋃ i, hatOf A kk vl i) := by
  have hlc : ∀ i, IsLatticeConvexRegion (hatOf A kk vl i) :=
    fun i => isLatticeConvexRegion_hatOf_of_maxA η xper vl S Env B A u kk hEnv maxA i
  have henv : ∀ i, Enveloped (↑S : Set (ℤ × ℤ)) (hatOf A kk vl i) :=
    fun i => Nivat.LaneCdFaceFree.enveloped_hatOf η xper vl S Env B A u kk hEnv maxA i
  exact mem_E_iUnion_of_arc_ccw
    (Ahat := fun i => hatOf A kk vl i) (Sphi := S)
    (fun _ _ h => AhatMono _ _ h) hfin hlc henv hSfin hSarea hℓE hJE hℓJ hμ hg₁ hArcbdd

/-- **Assembly: the interior polar-cone leg of `hkey`, stabilised.**  For `μ ∈ Arc ℓ J`
(`0 < ⟪μ, w⟫` and `μ ≠ J` are the caller's classification, not re-derived here — see the file
docstring), once `⟪μ, v⟫ ≤ 0` (the polar-cone half, also the caller's) there is a level `i₀`
past which *every* two `v`-reachable corners `p, q` from `Â_∞` leave `μ`'s face-and-edge status
against `hatOf A kk vl i ∪ {p, q}` at least as strong as against `↑S` — exactly `hkey`'s
conclusion at `n := μ`. -/
theorem exists_hkey_leg_of_arc
    (η xper : Config α) (vl : ℤ × ℤ) (S : Finset (ℤ × ℤ))
    (Env : Set (ℤ × ℤ) → Prop) (B A : ℕ → Set (ℤ × ℤ)) (u : ℕ → ℤ × ℤ) (kk : ℕ → ℕ)
    (hEnv : Env = EnvOf (↑S : Set (ℤ × ℤ)))
    (maxA : ∀ i, IsMaxEnvIn Env (canonA η xper vl B u i) (A i))
    (hfin : ∀ i, (hatOf A kk vl i).Finite)
    (AhatMono : ∀ i j, i ≤ j → hatOf A kk vl i ⊆ hatOf A kk vl j)
    {ℓ J μ g₁ v : ℤ × ℤ}
    (hSfin : (E (↑S : Set (ℤ × ℤ))).Finite) (hSarea : PosArea (↑S : Set (ℤ × ℤ)))
    (hℓE : ℓ ∈ E (↑S : Set (ℤ × ℤ))) (hJE : J ∈ E (↑S : Set (ℤ × ℤ)))
    (hℓJ : 0 < det ℓ J)
    (hμ : μ ∈ Nivat.PolyChainSum.Arc (S.finite_toSet) ℓ J)
    (hg₁ : ∀ i, faceStart (hatOf A kk vl i) ℓ + (faceLen (hatOf A kk vl i) ℓ : ℤ) • dir ℓ = g₁)
    (hArcbdd : ∀ ν ∈ Nivat.PolyChainSum.Arc (S.finite_toSet) ℓ J,
      ∃ L : ℕ, ∀ i, faceLen (hatOf A kk vl i) ν ≤ L)
    (hμv : dot μ v ≤ 0) :
    ∃ i₀ : ℕ, ∀ i, i₀ ≤ i → ∀ p q : ℤ × ℤ,
      p ∈ reachSet (⋃ j, hatOf A kk vl j) v → q ∈ reachSet (⋃ j, hatOf A kk vl j) v →
      μ ∈ E (hatOf A kk vl i ∪ {p, q}) ∧
        (face (↑S : Set (ℤ × ℤ)) μ).encard ≤
          (face (hatOf A kk vl i ∪ {p, q}) μ).encard := by
  have hμS : μ ∈ E (↑S : Set (ℤ × ℤ)) := (Nivat.PolyChainSum.mem_Arc.mp hμ).1
  have hμU : μ ∈ E (⋃ i, hatOf A kk vl i) :=
    mem_E_iUnion_hatOf_of_arc η xper vl S Env B A u kk hEnv maxA hfin AhatMono
      hSfin hSarea hℓE hJE hℓJ hμ hg₁ hArcbdd
  obtain ⟨i₀, hi₀⟩ := hdom_of_mem_E_iUnion AhatMono hμU
  refine ⟨i₀, fun i hi p q hp hq => ?_⟩
  exact Nivat.LaneCdFaceFree.face_encard_le_union_of_dom η xper vl S Env B A u kk hEnv maxA i
    hp hq hμS hμv (hi₀ i hi)

end Nivat.LaneHole3ConeHkeyE

#print axioms Nivat.LaneHole3ConeHkeyE.isLatticeConvexRegion_hatOf_of_maxA
#print axioms Nivat.LaneHole3ConeHkeyE.mem_E_iUnion_hatOf_of_arc
#print axioms Nivat.LaneHole3ConeHkeyE.exists_hkey_leg_of_arc
