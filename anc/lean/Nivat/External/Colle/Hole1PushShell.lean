/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.ItemIIRecursion
import Nivat.External.Colle.ChainAssemble
import Nivat.External.Colle.LeafAWire
import Nivat.External.Colle.LeafAItemII
import Nivat.External.Colle.LeafAJSelect
import Nivat.External.Colle.LeafAFaceAt
import Nivat.External.Colle.LeafAFaceRev
import Nivat.External.Colle.ShellRegionJ
import Nivat.External.Colle.LeafASwept
import Nivat.External.Colle.LeafACwBranch
import Nivat.External.Colle.EdgeUnboundedBoth
import Nivat.External.Colle.AhatMono
import Nivat.External.Colle.AhatEnv
import Nivat.External.Colle.RegionConvex
import Nivat.External.Colle.NlmaxReachMin
import Nivat.External.Colle.FanEndpoint
import Nivat.External.Colle.ShellLine
import Nivat.External.Colle.CyrKra224
import Nivat.External.Colle.SweepOppEdge
import Nivat.External.Colle.EnvelopedConvex
import Nivat.External.Colle.FillCoverReduce
import Nivat.External.Colle.GenClosureWeaken
import Nivat.External.Colle.ChainAssembleInter
import Nivat.External.Colle.TowerHlevEscapeWire
import Nivat.External.Colle.LeafAGenRecP
import Nivat.External.Colle.RecVJFromParts
import Nivat.External.Colle.ItemIIFeed
import Nivat.External.Colle.HsuppContain
import Nivat.External.Colle.CaseSplit
import Nivat.External.Colle.LineGenIndex

/-!
# Hole 1 closed: `exists_chainData` via the push-`J`-face shell

`ColleReg.exists_chainData_closed` proves `RegionSteps.lean` `exists_chainData` with its exact
signature; `RegionSteps.lean` now discharges its former `sorry` by it.

Route (2026-09-30): `ChainData.shell` is free data (only `shellInf` is pinned); instead of Collé's
`:518` sweep `Â_i^{(ε)}` — whose "easy to see" envelope/strip claims fail on general chains — the
per-level shell is `Â_i` with only its `J`-face pushed out by `L = det prev J · det J next`
lattice layers (`Hole1QShell.pushShell`), plus a non-convex filler below the threshold.  This
repairs the paper's proof of Lemma 3.5(i); the statement of `exists_chainData` is unchanged.

Sections (in order): the J package for a general item-(ii) chain (`Hole1JPack.exists_jpack`,
lane A), the `bottom` field (`Hole1Bottom.bottom_of_pinned`, lane B), the push shell and its seven
`ChainData` obligations (`Hole1QShell.*`, ending in `PinTower.shell_pack`), and the assembly.
Formerly `tmp/wip/hole1-{jpack,bottom,qshell,close}.lean`.
-/

/-! ## Copy of `RegionSteps.lean` `Hole2Room.sphi_shift_subset` (so this module need not import
`RegionSteps`, which consumes it).  Proof verbatim. -/

namespace Nivat.Hole1QShell

open Nivat Nivat.Colle35 Nivat.LE2 Nivat.ConeRegion

variable {ξ : Config ℤ}

/-- **Minkowski translate** (`HsuppContain.hcont` at the normal `ν`): `𝒮_φ` shifted so that its
`ν`-face start sits on `B`'s `ν`-face start lies inside `B`. -/
theorem sphi_shift_subset' {B : Set (ℤ × ℤ)} (d : DecompDataZ ξ)
    (henv : EnvOf (↑d.toDecompData.Sphi : Set (ℤ × ℤ)) B) (hBfin : B.Finite)
    {ν : ℤ × ℤ} (hνS : ν ∈ E (↑d.toDecompData.Sphi : Set (ℤ × ℤ))) :
    ∀ b ∈ (↑d.toDecompData.Sphi : Set (ℤ × ℤ)),
      Nivat.PolyChain.faceStart B ν +
        (b - Nivat.PolyChain.faceStart (↑d.toDecompData.Sphi : Set (ℤ × ℤ)) ν) ∈ B := by
  set S : Set (ℤ × ℤ) := ↑d.toDecompData.Sphi with hS
  have hSfin : S.Finite := d.toDecompData.Sphi.finite_toSet
  have hSlc : IsLatticeConvexRegion S := Nivat.ChainAsm.isLatticeConvexRegion_coe d.Sphi_conv
  have hSarea : PosArea S := Nivat.AhatMono.posArea_Sphi d.toDecompData
  have hE : E B = E S := Enveloped.E_eq (finite_E_of_finite hSfin) henv
  have hνB : ν ∈ E B := hE ▸ hνS
  have hBarea : PosArea B := Nivat.AhatMono.posArea_of_enveloped hSfin hSarea henv
  have hlcB : IsLatticeConvexRegion B := henv.1.1
  have hBne : B.Nonempty := by obtain ⟨p, hp, -⟩ := hBarea; exact ⟨p, hp⟩
  have hνne : ν ≠ 0 := (mem_E_iff.mp hνS).1.ne_zero
  have hdom : ∀ n ∈ E B, (face S n).encard ≤ (face B n).encard :=
    fun n hn => (henv.1.2 n hn).2
  -- the two face-starts, in `hcont`'s `(m, w) := (-ν, dir ν)` convention
  have hend : ∀ {T : Set (ℤ × ℤ)}, T.Finite → IsLatticeConvexRegion T → ν ∈ E T →
      (∀ b ∈ T, dot (-ν) (Nivat.PolyChain.faceStart T ν) ≤ dot (-ν) b) ∧
      (∀ b ∈ T, dot (-ν) b = dot (-ν) (Nivat.PolyChain.faceStart T ν) →
        ∃ t : ℕ, b = Nivat.PolyChain.faceStart T ν + (t : ℤ) • dir ν) := by
    intro T hTfin hTlc hνT
    have hface := Nivat.PolyChain.faceStart_mem hTfin hνT
    refine ⟨fun b hb => ?_, fun b hb hbeq => ?_⟩
    · rw [dot_neg_left, dot_neg_left]; linarith [hface.2 b hb]
    · rw [dot_neg_left, dot_neg_left] at hbeq
      have hbface : b ∈ face T ν := ⟨hb, fun y hy => by linarith [hface.2 y hy]⟩
      rw [Nivat.PolyChain.face_eq_segment hTlc hTfin hνT] at hbface
      obtain ⟨t, -, ht⟩ := hbface
      exact ⟨t, ht⟩
  obtain ⟨hSmin, hSend⟩ := hend hSfin hSlc hνS
  obtain ⟨hBmin, hBend⟩ := hend hBfin hlcB hνB
  exact Nivat.HsuppContain.hcont d hBfin hBne hBarea hlcB (m := -ν) (w := dir ν)
    (by rw [neg_neg]) (neg_ne_zero.mpr hνne) hE (by rw [neg_neg]; exact hνS) hdom
    (Nivat.PolyChain.faceStart_mem hSfin hνS).1 hSmin hSend
    (Nivat.PolyChain.faceStart_mem hBfin hνB).1 hBmin hBend

end Nivat.Hole1QShell



-- ===== begin tmp/wip/hole1-jpack.lean =====
/-
Lane hole1-jpack, 2026-09-30.  `tmp/wip/`, self-contained (copies §0-§3 and the cw half of §4-§5 of
`tmp/wip/lane-leafa-shell-hg1.lean` verbatim under a new namespace, because tmp files cannot be
imported), no `sorry`.

**Purpose**: port the cw `J`-package of `tmp/wip/LeafAAssemble.lean` (`case inr`, the
`exists_J_package_cw` branch and the `FaceBlock` step) from the chain-specific
`AenvfixProbe.chA`/`anchorPoint` to a GENERAL item-(ii) chain
`rd : ItemIIRecursion.ItemIIRecursionData`, and re-index by `n ↦ σ' (n + i₀)` so that every
statement holds for ALL indices.
-/

set_option autoImplicit false

namespace Nivat.Hole1JPack

open Nivat Nivat.LE2 Nivat.Colle35 Nivat.PolyChain

variable {A : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ} {vl nℓ g₁ : ℤ × ℤ} {cz : ℤ}

/-! ## §0. Algebra -/

/-- `dot nℓ` is blind to `v⃗_ℓ`-translation when `nℓ ⟂ v⃗_ℓ`. -/
theorem dot_add_zsmul_perp (hperp : dot nℓ vl = 0) (z : ℤ × ℤ) (t : ℤ) :
    dot nℓ (z + t • vl) = dot nℓ z := by
  simp only [dot, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at *
  linear_combination t * hperp

/-- `dot (-n) z = - dot n z` — reused from `LatticeEdges.lean:82` (§61 撞名 grep 命中 1 条，
就是那条；本文件不重证，直接用). -/
theorem dot_neg_left' (n z : ℤ × ℤ) : dot (-n) z = - dot n z := Nivat.LE2.dot_neg_left n z

/-! ## §1. The `cw` mirror of `faceEnd_eq_of_add_dir_not_mem`

`LeafAWire.faceEnd_eq_of_add_dir_not_mem` (`AnchorIsFaceEnd.lean:124`) says: a point of
`face T ν` whose successor along `dir ν` leaves `T` is the *far* endpoint.  The statement below
is the same argument run the other way — a point whose *predecessor* leaves `T` is the *near*
endpoint, i.e. `faceStart`.  Both are pure `face_eq_segment` bookkeeping, no paper line. -/

/-- **A point of an edge face that cannot retreat along `dir ν` is `faceStart`.** -/
theorem faceStart_eq_of_sub_dir_not_mem {T : Set (ℤ × ℤ)} {ν a : ℤ × ℤ}
    (hlc : IsLatticeConvexRegion T) (hfin : T.Finite) (hν : ν ∈ Nivat.LE2.E T)
    (ha : a ∈ Nivat.LE2.face T ν) (hstop : a - dir ν ∉ T) :
    Nivat.PolyChain.faceStart T ν = a := by
  obtain ⟨t, htle, ht⟩ := by
    rw [Nivat.PolyChain.face_eq_segment hlc hfin hν] at ha; exact ha
  have ht0 : t = 0 := by
    by_contra h0
    have h1 : 1 ≤ t := Nat.one_le_iff_ne_zero.mpr h0
    have hpred : a - dir ν ∈ Nivat.LE2.face T ν := by
      rw [Nivat.PolyChain.face_eq_segment hlc hfin hν]
      refine ⟨t - 1, by omega, ?_⟩
      rw [ht]
      have hcast : ((t - 1 : ℕ) : ℤ) = (t : ℤ) - 1 := by omega
      rw [hcast, sub_smul, one_smul]
      abel
    exact hstop (Nivat.LE2.face_subset T ν hpred)
  rw [ht, ht0]; simp

/-! ## §2. `hmemFace` is free: `g₁` is on the `-nℓ`-face of every `Â_i`

原文 `b3_colle2.txt:488` puts `g₁` on `ℓ^(−)`, the floor line `dot nℓ · = cz`, and the chain's
`hlev` puts every `Â_i` weakly above that floor.  Being *in* `T` and *at the minimum of*
`dot nℓ` over `T` is literally being in `face T (-nℓ)`. -/

/-- `Â_i` inherits `A_i`'s floor, because `nℓ ⟂ v⃗_ℓ` and `Â_i` is a `v⃗_ℓ`-translate. -/
theorem level_hatOf (hperp : dot nℓ vl = 0) {i : ℕ}
    (hlev : ∀ z ∈ A i, cz ≤ dot nℓ z) :
    ∀ z ∈ hatOf A kk vl i, cz ≤ dot nℓ z := by
  intro z hz
  have h := hlev _ hz
  rwa [dot_add_zsmul_perp hperp] at h

/-- **`hmemFace`, discharged.**  A point of `T` at the floor level `cz`, when no point of `T`
is below `cz`, lies on `face T (-nℓ)`. -/
theorem mem_bottomFace {T : Set (ℤ × ℤ)} (hg₁cz : dot nℓ g₁ = cz)
    (hlev : ∀ z ∈ T, cz ≤ dot nℓ z) (hmem : g₁ ∈ T) :
    g₁ ∈ Nivat.LE2.face T (-nℓ) := by
  refine ⟨hmem, fun y hy => ?_⟩
  rw [dot_neg_left', dot_neg_left', hg₁cz]
  linarith [hlev y hy]

/-- `Â_i` is lattice-convex when `A_i` is (it is a translate). -/
theorem latticeConvex_hatOf {i : ℕ} (h : IsLatticeConvexRegion (A i)) :
    IsLatticeConvexRegion (hatOf A kk vl i) := by
  rw [Nivat.Colle35.hatOf_eq_shift]
  exact isLatticeConvexRegion_shift _ h

/-! ## §3. `hstop` from `:488`'s `IsGreatest` -/

/-- **"Final point" ⟹ one more `v⃗_ℓ`-step leaves `Â_i`.**  原文 `b3_colle2.txt:488`: `g₁` is the
*final* point of `Â_i ∩ ℓ^(−)`.  `g₁ + v⃗_ℓ` is still on `ℓ^(−)` (`hperp`), so if it were in
`Â_i` the parameter `1` would beat the claimed greatest `0`. -/
theorem add_vl_not_mem_of_halign (hperp : dot nℓ vl = 0) (hg₁cz : dot nℓ g₁ = cz)
    (halign : ∀ i, IsGreatest
      {t : ℤ | g₁ + t • vl ∈ hatOf A kk vl i ∧ dot nℓ (g₁ + t • vl) = cz} 0)
    (i : ℕ) : g₁ + vl ∉ hatOf A kk vl i := by
  intro hmem
  have h1 : g₁ + (1 : ℤ) • vl ∈ hatOf A kk vl i := by simpa using hmem
  have h2 : dot nℓ (g₁ + (1 : ℤ) • vl) = cz := by rw [dot_add_zsmul_perp hperp, hg₁cz]
  have hle := (halign i).2 ⟨h1, h2⟩
  omega


/-- **`hg₁` for `LeafAJSelect.exists_gJ_pinned_cw` at `ℓ := -nℓ`.**  Same inputs, opposite sign
branch: here `g₁ + v⃗_ℓ = g₁ - dir (-nℓ)`, so `:488`'s "final point" says `g₁` cannot retreat,
and §1 makes it `faceStart`. -/
theorem hg1_faceStart_of_halign
    (hperp : dot nℓ vl = 0) (hg₁cz : dot nℓ g₁ = cz)
    (hlev : ∀ i, ∀ z ∈ A i, cz ≤ dot nℓ z)
    (hfin : ∀ i, (A i).Finite) (hlc : ∀ i, IsLatticeConvexRegion (A i))
    (hEdge : ∀ i, (-nℓ) ∈ Nivat.LE2.E (hatOf A kk vl i))
    (halign : ∀ i, IsGreatest
      {t : ℤ | g₁ + t • vl ∈ hatOf A kk vl i ∧ dot nℓ (g₁ + t • vl) = cz} 0)
    (hdir : Nivat.LE2.dir (-nℓ) = -vl) :
    ∀ i, Nivat.PolyChain.faceStart (hatOf A kk vl i) (-nℓ) = g₁ := by
  intro i
  refine faceStart_eq_of_sub_dir_not_mem (latticeConvex_hatOf (hlc i))
    (Nivat.LeafAItemII.finite_hatOf (hfin i)) (hEdge i)
    (mem_bottomFace hg₁cz (level_hatOf hperp (hlev i)) (by simpa using (halign i).1.1)) ?_
  rw [hdir]
  have : g₁ - -vl = g₁ + vl := by abel
  rw [this]
  exact add_vl_not_mem_of_halign hperp hg₁cz halign i


/-! ## Enveloped transport (verbatim from `lane-leafa-shell-hg1.lean` §5) -/

/-- **Definition 3.2 is translation-invariant** (weak half). -/
theorem weaklyEnveloped_shift {U T : Set (ℤ × ℤ)} (v : ℤ × ℤ)
    (h : WeaklyEnveloped U T) : WeaklyEnveloped U (shift v T) := by
  refine ⟨isLatticeConvexRegion_shift v h.1, fun n hn => ?_⟩
  rw [E_shift] at hn
  obtain ⟨hnU, hle⟩ := h.2 n hn
  refine ⟨hnU, ?_⟩
  rw [face_shift, encard_shift]
  exact hle

/-- **Definition 3.2 is translation-invariant.** -/
theorem enveloped_shift {U T : Set (ℤ × ℤ)} (v : ℤ × ℤ)
    (h : Enveloped U T) : Enveloped U (shift v T) :=
  ⟨weaklyEnveloped_shift v h.1, by rw [E_shift]; exact h.2⟩

/-- `Â_i` is enveloped by `↑S` whenever `A_i` is. -/
theorem enveloped_hatOf_of_enveloped {S : Finset (ℤ × ℤ)} {i : ℕ}
    (h : Enveloped (↑S : Set (ℤ × ℤ)) (A i)) :
    Enveloped (↑S : Set (ℤ × ℤ)) (hatOf A kk vl i) := by
  rw [Nivat.Colle35.hatOf_eq_shift]
  exact enveloped_shift _ h

/-- **`hEdge`, discharged.**  `Â_i` has exactly `↑S`'s edge directions. -/
theorem E_hatOf_eq_of_enveloped {S : Finset (ℤ × ℤ)} {i : ℕ}
    (h : Enveloped (↑S : Set (ℤ × ℤ)) (A i)) :
    Nivat.LE2.E (hatOf A kk vl i) = Nivat.LE2.E (↑S : Set (ℤ × ℤ)) :=
  (enveloped_hatOf_of_enveloped h).E_eq (finite_E_of_finite S.finite_toSet)

end Nivat.Hole1JPack

namespace Nivat.Hole1JPack

open Nivat Nivat.LE2 Nivat.Colle35

/-- `dir (-n) = -dir n`. -/
theorem dir_neg' (n : ℤ × ℤ) : Nivat.LE2.dir (-n) = -Nivat.LE2.dir n := by
  simp only [Nivat.LE2.dir, Prod.fst_neg, Prod.snd_neg, Prod.neg_mk, neg_neg]

/-- **The cw orientation is forced by `0 < det nℓ vl`.**  `dir nℓ = ±vl`
(`ShellRegionJ.dir_nℓ_eq_or_neg_vl`); `dir nℓ = -vl` gives `det nℓ vl = -(n₁² + n₂²) ≤ 0`. -/
theorem dir_neg_nℓ_eq_neg_vl {nℓ vl : ℤ × ℤ} (hnℓ_ne : nℓ ≠ 0) (hnℓ_prim : Primitive nℓ)
    (hvl_prim : Primitive vl) (hperp : dot nℓ vl = 0) (hdetpos : 0 < det nℓ vl) :
    Nivat.LE2.dir (-nℓ) = -vl := by
  rcases Nivat.ShellRegionJ.dir_nℓ_eq_or_neg_vl hnℓ_ne
      (Nivat.LE2.prim_iff_primitive.mpr hnℓ_prim) hvl_prim hperp with h | h
  · rw [dir_neg', h]
  · exfalso
    have hvl : vl = -Nivat.LE2.dir nℓ := by rw [h]; simp
    rw [hvl] at hdetpos
    obtain ⟨n1, n2⟩ := nℓ
    simp only [det, Nivat.LE2.dir, Prod.fst_neg, Prod.snd_neg] at hdetpos
    nlinarith [sq_nonneg n1, sq_nonneg n2]

/-- **The J package, cw branch, for a general item-(ii) chain.**

Port of `tmp/wip/LeafAAssemble.lean` `case inr` (`exists_J_package_cw` branch) and the
`FaceBlock` step, from `AenvfixProbe.chA`/`anchorPoint` to an arbitrary
`ItemIIRecursionData`; the `hg₁` pinning comes from `hg1_faceStart_of_halign`
(`rd.halign`, `rd.hg₁`).  Final index shift `σ n := σ' (n + i₀)` makes the face-end pinning hold
for ALL `n`.

Only added hypothesis: `hnE : -nℓ ∈ E ↑d.Sphi`
(available at the caller as `ItemIIFeed.mem_E_Sphi_and_neg_of_prim_perp`'s second conjunct, or as
`hnℓ'` of `ItemIIRecursion.exists_itemII_recursion`). -/
theorem exists_jpack {ξ xper : Config ℤ} (d : DecompDataZ ξ) {vl nℓ : ℤ × ℤ} {cz : ℤ}
    (rd : Nivat.ItemIIRecursion.ItemIIRecursionData ξ xper d.Sphi vl nℓ cz)
    (hvl : vl ≠ 0) (hvl_prim : Primitive vl) (hnℓ_ne : nℓ ≠ 0) (hnℓ_prim : Primitive nℓ)
    (hperp : dot nℓ vl = 0) (hdetpos : 0 < det nℓ vl)
    (hnE : -nℓ ∈ E (↑d.Sphi : Set (ℤ × ℤ))) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ J prv nxt g : ℤ × ℤ,
      J ∈ E (↑d.Sphi : Set (ℤ × ℤ)) ∧ prv ∈ E (↑d.Sphi : Set (ℤ × ℤ)) ∧
      nxt ∈ E (↑d.Sphi : Set (ℤ × ℤ)) ∧
      0 < det prv J ∧ 0 < det J nxt ∧
      (∀ μ ∈ E (↑d.Sphi : Set (ℤ × ℤ)), ¬(0 < det prv μ ∧ 0 < det μ J)) ∧
      (∀ μ ∈ E (↑d.Sphi : Set (ℤ × ℤ)), ¬(0 < det J μ ∧ 0 < det μ nxt)) ∧
      J ≠ nℓ ∧ J ≠ -nℓ ∧
      0 < det J (-nℓ) ∧
      (∀ i, Nivat.PolyChain.faceStart (hatOf rd.A rd.kk vl (σ i)) J
          + (Nivat.PolyChain.faceLen (hatOf rd.A rd.kk vl (σ i)) J : ℤ) • dir J = g) ∧
      (∀ L : ℕ, ∃ i, L ≤ Nivat.PolyChain.faceLen (hatOf rd.A rd.kk vl (σ i)) J) ∧
      (∀ i, hatOf rd.A rd.kk vl (σ i) ⊆ Nivat.CK224.halfPlaneGE (-J) (dot (-J) g)) ∧
      Nivat.MaxEnv.SweptClosed (⋃ i, hatOf rd.A rd.kk vl (σ i)) (-(dir nxt)) (-J) (dot (-J) g) ∧
      (∀ k : ℕ, g - (k : ℤ) • dir J ∈ ⋃ i, hatOf rd.A rd.kk vl (σ i)) ∧
      (∀ z ∈ ⋃ i, hatOf rd.A rd.kk vl (σ i), dot nxt z ≤ dot nxt g) ∧
      Nonempty (Nivat.Colle35.FaceBlock d.Sphi (-J) (-(dir J))) := by
  classical
  have hnℓ_prim' : Prim nℓ := Nivat.LE2.prim_iff_primitive.mpr hnℓ_prim
  have hnℓE : nℓ ∈ E (↑d.Sphi : Set (ℤ × ℤ)) :=
    (Nivat.Colle35.Sphi_negSymm d.toDecompData nℓ).mpr hnE
  have hSymmE : ∀ μ ∈ E (↑d.Sphi : Set (ℤ × ℤ)), -μ ∈ E (↑d.Sphi : Set (ℤ × ℤ)) :=
    fun μ hμ => (Nivat.Colle35.Sphi_negSymm d.toDecompData μ).mp hμ
  have henvA : ∀ i, Enveloped (↑d.Sphi : Set (ℤ × ℤ)) (rd.A i) := fun i => (rd.maxA i).1
  obtain ⟨hunb_cw, -⟩ := Nivat.LaneCdEdgeUnb.exists_edge_unbounded_both
    hnℓ_ne rd.itemII rd.subBA rd.hfin henvA hnℓE hnE hSymmE
  -- orientation
  have hdir_negvl : Nivat.LE2.dir (-nℓ) = -vl :=
    dir_neg_nℓ_eq_neg_vl hnℓ_ne hnℓ_prim hvl_prim hperp hdetpos
  -- J-independent tower facts
  have hhatFin : ∀ i, (hatOf rd.A rd.kk vl i).Finite := fun i =>
    Nivat.LeafAItemII.finite_hatOf (rd.hfin i)
  have henvAhat : ∀ i, Enveloped (↑d.Sphi : Set (ℤ × ℤ)) (hatOf rd.A rd.kk vl i) := fun i =>
    enveloped_hatOf_of_enveloped (henvA i)
  have hlcAhat : ∀ i, IsLatticeConvexRegion (hatOf rd.A rd.kk vl i) := fun i => (henvAhat i).1.1
  have hSfin : (E (↑d.Sphi : Set (ℤ × ℤ))).Finite :=
    Nivat.LE2.finite_E_of_finite d.Sphi.finite_toSet
  have hSarea : PosArea (↑d.Sphi : Set (ℤ × ℤ)) := Nivat.AhatMono.posArea_Sphi d.toDecompData
  have hAlevel : ∀ i, ∀ z ∈ rd.A i, cz ≤ dot nℓ z := by
    intro i z hz
    have hsub : rd.A i ⊆ {z : ℤ × ℤ | cz ≤ dot nℓ z} := by
      rw [← rd.exhausts]; exact Set.subset_iUnion _ i
    exact hsub hz
  have hAhatNe : ∀ j, (hatOf rd.A rd.kk vl j).Nonempty := fun j =>
    ⟨rd.g₁ + (0 : ℤ) • vl, (rd.halign j).1.1⟩
  have hfaceLen_shift : ∀ (v : ℤ × ℤ) (R : Set (ℤ × ℤ)) (n : ℤ × ℤ),
      Nivat.PolyChain.faceLen (Nivat.LE2.shift v R) n = Nivat.PolyChain.faceLen R n := by
    intro v R n
    unfold Nivat.PolyChain.faceLen
    rw [Nivat.LE2.face_shift, Nivat.LE2.encard_shift]
  have hAhatConvU : IsLatticeConvexRegion (⋃ i, hatOf rd.A rd.kk vl i) :=
    Nivat.Colle35.latticeConvex_iUnion_hatOf ξ xper vl d.Sphi
      (EnvOf (↑d.Sphi : Set (ℤ × ℤ))) rd.B rd.A rd.u rd.kk rfl rd.maxA hhatFin rd.AhatMono
  have hEAhat : ∀ i, E (hatOf rd.A rd.kk vl i) = E (↑d.Sphi : Set (ℤ × ℤ)) :=
    fun i => Nivat.AhatEnv.E_eq_of_enveloped hSfin hSarea (henvAhat i)
  -- `hg₁` pinning (cw: the `-nℓ`-face START is the fixed point `rd.g₁`)
  have hg₁cw : ∀ i, Nivat.PolyChain.faceStart (hatOf rd.A rd.kk vl i) (-nℓ) = rd.g₁ :=
    hg1_faceStart_of_halign hperp rd.hg₁ hAlevel rd.hfin (fun i => (henvA i).1.1)
      (fun i => by rw [E_hatOf_eq_of_enveloped (henvA i)]; exact hnE) rd.halign hdir_negvl
  have hunb_cw' : ∃ ν ∈ E (↑d.Sphi : Set (ℤ × ℤ)), 0 < det ν (-nℓ) ∧
      ¬ ∃ L : ℕ, ∀ i, Nivat.PolyChain.faceLen (hatOf rd.A rd.kk vl i) ν ≤ L := by
    obtain ⟨ν, hνE, hd, hu⟩ := hunb_cw
    refine ⟨ν, hνE, ?_, ?_⟩
    · have hmir : det ν (-nℓ) = det nℓ ν := by
        simp only [det, Prod.fst_neg, Prod.snd_neg]; ring
      rw [hmir]; exact hd
    · rintro ⟨L, hL⟩
      refine hu ⟨L, fun i => ?_⟩
      have hi := hL i
      rwa [Nivat.Colle35.hatOf_eq_shift, hfaceLen_shift] at hi
  obtain ⟨J, hJE, nprevJ, nnextJ, vJ1, wJ, g_J, σ', i₀, hσ'mono, hℓJ, hJne0,
      hJneℓ, hJnegℓ, hJunbHat,
      ⟨hnprevE, hnprevdet, hnprevempty, hvJ1_eq, hdotnprevvJ1, hsweep⟩,
      ⟨hnnextE, hnnextdet, hnnextempty, hwJ_eq, hdotnnextwJ, hsweepW⟩,
      hgJspec, hgJmem⟩ :=
    Nivat.LaneCdCw.exists_J_package_cw (Ahat := hatOf rd.A rd.kk vl) (ℓ := -nℓ)
      hhatFin hAhatNe hlcAhat henvAhat hSfin hSarea rd.AhatMono hSymmE
      hnE (by rw [neg_neg]; exact hnℓE) hg₁cw hunb_cw'
  have hJprim : Primitive J := Nivat.LE2.prim_iff_primitive.mp hJE.1
  have hJmemAllIdx : ∀ i, J ∈ E (hatOf rd.A rd.kk vl i) := by
    intro i; rw [hEAhat i]; exact hJE
  -- monotonicity bookkeeping
  have hle : ∀ i, hatOf rd.A rd.kk vl i ⊆ hatOf rd.A rd.kk vl (σ' (i + i₀)) := fun i =>
    rd.AhatMono i (σ' (i + i₀)) (le_trans (Nat.le_add_right i i₀) hσ'mono.le_apply)
  have hunion : (⋃ n, hatOf rd.A rd.kk vl (σ' (n + i₀))) = ⋃ i, hatOf rd.A rd.kk vl i := by
    apply Set.Subset.antisymm
    · exact Set.iUnion_subset fun n => Set.subset_iUnion _ _
    · exact Set.iUnion_subset fun i => (hle i).trans (Set.subset_iUnion (fun n =>
        hatOf rd.A rd.kk vl (σ' (n + i₀))) i)
  have hhp_all : ∀ i, hatOf rd.A rd.kk vl i ⊆ Nivat.CK224.halfPlaneGE (-J) (dot (-J) g_J) := by
    intro i z hz
    have hz' : z ∈ hatOf rd.A rd.kk vl (σ' (i + i₀)) := hle i hz
    have hmax := (hgJmem (i + i₀) (by omega)).2 z hz'
    show dot (-J) g_J ≤ dot (-J) z
    rw [Nivat.LE2.dot_neg_left, Nivat.LE2.dot_neg_left]
    omega
  have hsupp_prev_all : ∀ i, ∀ z ∈ hatOf rd.A rd.kk vl i,
      Nivat.LE2.dot nprevJ z ≤ Nivat.LE2.dot nprevJ g_J := by
    have hbase := Nivat.LeafAJSelect.hsupp_prev_cw (Ahat := hatOf rd.A rd.kk vl) hhatFin hAhatNe
      hlcAhat henvAhat hSfin hSarea rd.AhatMono hnprevE hJE hnprevdet hnprevempty hσ'mono hgJspec
    intro i z hz
    exact hbase (i + i₀) z (hle i hz)
  have hgrow := Nivat.LeafAJSelect.hgrow_of_pinned_cw rd.AhatMono hhatFin hAhatNe
    hlcAhat hJmemAllIdx hJunbHat hσ'mono hgJspec
  have hswept_all :
      Nivat.MaxEnv.SweptClosed (⋃ i, hatOf rd.A rd.kk vl i) vJ1 (-J) (dot (-J) g_J) :=
    Nivat.LaneCdCw.sweptClosed_of_pinned_cw (nprevJ := nprevJ) (g_J := g_J)
      hJne0 rfl rfl hsweep hnprevdet hdotnprevvJ1
      (by
        intro N
        obtain ⟨i, hi⟩ := hgrow N
        exact ⟨σ' i, hi⟩)
      hsupp_prev_all hAhatConvU
  -- `FaceBlock` at `-J`, direction `-(dir J)`
  have hJnegE : -J ∈ E (↑d.Sphi : Set (ℤ × ℤ)) := hSymmE J hJE
  have hJne : J ≠ nℓ ∧ J ≠ -nℓ := ⟨by rw [← neg_neg nℓ]; exact hJnegℓ, hJneℓ⟩
  have hdotnvl : dot (-J) vl ≠ 0 := by
    rw [Nivat.LE2.dot_neg_left]
    exact neg_ne_zero.mpr
      (Nivat.LeafAJSelect.dot_J_vl_ne_zero hJprim hnℓ_prim hvl hperp hJne)
  have hedirJ_prim : Primitive (-(Nivat.LE2.dir J)) :=
    Nivat.LE2.prim_iff_primitive.mp
      (Nivat.LE2.prim_iff_primitive.mpr (Nivat.CK224.prim_dir hJE.1)).neg
  have hFB : Nonempty (Nivat.Colle35.FaceBlock d.Sphi (-J) (-(Nivat.LE2.dir J))) := by
    obtain ⟨v, F, hv_prim, -, hdotnv, -, -, -, -⟩ := d.exists_faceBlock_at hJnegE hdotnvl
    have hJne0' : (-J) ≠ 0 := fun h => hJne0 (neg_eq_zero.mp h)
    have h1 : dot v (-J) = 0 := by rw [Nivat.LE2.dot_comm]; exact hdotnv
    have h2 : dot (-(Nivat.LE2.dir J)) (-J) = 0 := by
      rw [Nivat.LE2.dot_comm, Nivat.LE2.dot_neg_right]
      simp [Nivat.LE2.dot_neg_left, Nivat.LE2.dot_dir]
    rcases Nivat.AGlue.eq_or_neg_of_primitive_of_perp hJne0' hv_prim hedirJ_prim h1 h2 with
      heq | heq
    · rw [← heq]; exact ⟨F⟩
    · have hF := F.reverse
      rw [heq, neg_neg] at hF
      exact ⟨hF⟩
  refine ⟨fun n => σ' (n + i₀), fun a b hab => hσ'mono (by omega), J, nnextJ, nprevJ, g_J,
    hJE, hnnextE, hnprevE, hnnextdet, hnprevdet, ?_, ?_, hJne.1, hJne.2, hℓJ, ?_, ?_, ?_, ?_, ?_, ?_,
    hFB⟩
  · intro μ hμ hcon
    have hμArc : μ ∈ Nivat.PolyChainSum.Arc (d.Sphi.finite_toSet) nnextJ J :=
      Nivat.PolyChainSum.mem_Arc.mpr ⟨hμ, hcon.1, hcon.2⟩
    rw [hnnextempty] at hμArc
    exact absurd hμArc (by simp)
  · intro μ hμ hcon
    have hμArc : μ ∈ Nivat.PolyChainSum.Arc (d.Sphi.finite_toSet) J nprevJ :=
      Nivat.PolyChainSum.mem_Arc.mpr ⟨hμ, hcon.1, hcon.2⟩
    rw [hnprevempty] at hμArc
    exact absurd hμArc (by simp)
  · intro i
    exact hgJspec (i + i₀) (by omega)
  · intro L
    obtain ⟨i, hi⟩ := hgrow L
    have hmemL : g_J - (L : ℤ) • dir J ∈ hatOf rd.A rd.kk vl (σ' (i + i₀)) :=
      rd.AhatMono (σ' i) (σ' (i + i₀)) (hσ'mono.monotone (Nat.le_add_right i i₀))
        (hi L le_rfl)
    have hface : g_J - (L : ℤ) • dir J ∈ Nivat.LE2.face (hatOf rd.A rd.kk vl (σ' (i + i₀))) J := by
      refine ⟨hmemL, fun y hy => ?_⟩
      have hmax := (hgJmem (i + i₀) (by omega)).2 y hy
      have hd : dot J (g_J - (L : ℤ) • dir J) = dot J g_J := by
        rw [Nivat.LE2.dot_sub, Nivat.LE2.dot_comm J ((L : ℤ) • dir J), Nivat.LE2.dot_smul,
          Nivat.LE2.dot_comm (dir J) J, Nivat.LE2.dot_dir]; ring
      rw [hd]; exact hmax
    rw [Nivat.PolyChain.face_eq_segment (hlcAhat _) (hhatFin _) (hJmemAllIdx _)] at hface
    obtain ⟨t, ht, hteq⟩ := hface
    have hg := hgJspec (i + i₀) (by omega)
    have hdne : Nivat.LE2.dir J ≠ 0 := (Nivat.CK224.prim_dir hJE.1).ne_zero
    refine ⟨i, ?_⟩
    set Lf := Nivat.PolyChain.faceLen (hatOf rd.A rd.kk vl (σ' (i + i₀))) J with hLf
    set a := Nivat.PolyChain.faceStart (hatOf rd.A rd.kk vl (σ' (i + i₀))) J with ha
    have h1 := congrArg Prod.fst hteq
    have h2 := congrArg Prod.snd hteq
    have h3 := congrArg Prod.fst hg
    have h4 := congrArg Prod.snd hg
    simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul] at h1 h2 h3 h4
    have hsm : (((Lf : ℤ) - t - L) • Nivat.LE2.dir J) = 0 := by
      refine Prod.ext ?_ ?_
      · simp only [Prod.smul_fst, smul_eq_mul, Prod.fst_zero]
        linear_combination h3 + h1
      · simp only [Prod.smul_snd, smul_eq_mul, Prod.snd_zero]
        linear_combination h4 + h2
    rcases smul_eq_zero.mp hsm with h0 | h0
    · omega
    · exact absurd h0 hdne
  · intro i
    exact hhp_all _
  · beta_reduce
    rw [hunion, ← hvJ1_eq]
    exact hswept_all
  · intro k
    obtain ⟨i, hi⟩ := hgrow k
    beta_reduce
    rw [hunion]
    exact Set.mem_iUnion.mpr ⟨σ' i, hi k le_rfl⟩
  · intro z hz
    beta_reduce at hz
    rw [hunion] at hz
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
    exact hsupp_prev_all i z hi

end Nivat.Hole1JPack
#print axioms Nivat.Hole1JPack.dot_add_zsmul_perp
#print axioms Nivat.Hole1JPack.dot_neg_left'
#print axioms Nivat.Hole1JPack.faceStart_eq_of_sub_dir_not_mem
#print axioms Nivat.Hole1JPack.level_hatOf
#print axioms Nivat.Hole1JPack.mem_bottomFace
#print axioms Nivat.Hole1JPack.latticeConvex_hatOf
#print axioms Nivat.Hole1JPack.add_vl_not_mem_of_halign
#print axioms Nivat.Hole1JPack.hg1_faceStart_of_halign
#print axioms Nivat.Hole1JPack.weaklyEnveloped_shift
#print axioms Nivat.Hole1JPack.enveloped_shift
#print axioms Nivat.Hole1JPack.enveloped_hatOf_of_enveloped
#print axioms Nivat.Hole1JPack.E_hatOf_eq_of_enveloped
#print axioms Nivat.Hole1JPack.dir_neg'
#print axioms Nivat.Hole1JPack.dir_neg_nℓ_eq_neg_vl
#print axioms Nivat.Hole1JPack.exists_jpack

-- ===== end tmp/wip/hole1-jpack.lean =====

-- ===== begin tmp/wip/hole1-bottom.lean =====
/-
Scratch checkpoint (hole 1): the `bottom` obligation of `GeomCoreShell` from a **pinned J tower**.

Statement: `bottom_of_pinned` (end of file).  Proof idea (all of it, no reach-minimality needed):

* `R := reachSet Ainf vJ1` is lattice-convex (`EdgeJ1Data.isLatticeConvexRegion_reachSet`, edge
  data at the pinned corner `g`), closed under `+vJ1` (by definition) and `+vJ` (from the
  `vJ`-ray `hray` and `rec_of_ray`).
* **Quadrant lemma** (`quadrant_mem`): `x ∈ R`, `dot (-J) y ≤ dot (-J) x`, `dot nxt y ≤ dot nxt x`
  ⟹ `y ∈ R`.  In the skew coordinates `y - x = α • vJ1 + β • vJ` with
  `α = (dot(-J) x - dot(-J) y)/δ ≥ 0`, `β = (dot nxt x - dot nxt y)/δ ≥ 0`,
  `δ = det J nxt > 0`; the lattice point `y` lies in the real parallelogram spanned by four
  lattice points of `R`.
* The window `g + (S - F.a) ⊆ Ainf` at the pinned corner is the Minkowski corner fit at `nxt`
  (`sphi_shift_subset`, `faceStart (Ah i) nxt = g`, `F.a = faceStart S nxt`).
* `L` is the exact threshold `⌈(dot nxt z₀ - dot nxt g)/δ⌉` of the `nxt`-support; every clause of
  `bottom` is then the quadrant lemma applied at `x = g + (b - F.a)`.

Per CLAUDE.md hard rule 19/22 this is not in `Nivat/`: it is a `tmp/wip` deliverable whose
consumer is `GeomCoreShell.bottom` in `tmp/wip/hole1-qshell.lean` §9.
Numeric receipts: `tmp/wip/hole1-bottom-check.py` (zonotope model, strict `L = 0`),
`tmp/wip/hole1-bottom-gen.py` (random non-symmetric `S`, exact reach-minimal `z₀`): 0 failures.
-/

set_option autoImplicit false

namespace Nivat.Hole1Bottom

open Nivat Nivat.LE2 Nivat.MaxEnv

/-! ## §1. Real rays and the cone lemma -/

/-- A real ray: if `q + k • v ∈ C` for every natural `k` and `C` is convex, then `q + t • v ∈ C`
for every real `t ≥ 0`. -/
theorem real_ray_mem {C : Set (ℝ × ℝ)} (hC : Convex ℝ C) {q v : ℝ × ℝ}
    (hray : ∀ k : ℕ, q + (k : ℝ) • v ∈ C) {t : ℝ} (ht : 0 ≤ t) : q + t • v ∈ C := by
  set n : ℕ := ⌊t⌋₊ with hndef
  have hn1 : (n : ℝ) ≤ t := Nat.floor_le ht
  have hn2 : t ≤ (n : ℝ) + 1 := (Nat.lt_floor_add_one t).le
  set θ : ℝ := t - n with hθdef
  have hθ0 : 0 ≤ θ := by rw [hθdef]; linarith
  have hθ1 : θ ≤ 1 := by rw [hθdef]; linarith
  have hm1 := hray n
  have hm2 := hray (n + 1)
  push_cast at hm2
  have hcomb := hC hm1 hm2 (show (0:ℝ) ≤ 1 - θ by linarith) hθ0 (by ring)
  have heq : (1 - θ) • (q + (n : ℝ) • v) + θ • (q + ((n : ℝ) + 1) • v) = q + t • v := by
    have ht' : t = (n : ℝ) + θ := by rw [hθdef]; ring
    rw [ht']
    module
  rwa [heq] at hcomb

private theorem toReal_add' (z w : ℤ × ℤ) : toReal (z + w) = toReal z + toReal w := by
  simp [toReal]

private theorem toReal_zsmul' (n : ℤ) (z : ℤ × ℤ) : toReal (n • z) = (n : ℝ) • toReal z := by
  simp [toReal]

theorem mem_of_nat_iter {R : Set (ℤ × ℤ)} {r : ℤ × ℤ} (h : ∀ z ∈ R, z + r ∈ R) {z : ℤ × ℤ}
    (hz : z ∈ R) (k : ℕ) : z + (k : ℤ) • r ∈ R := by
  induction k with
  | zero => simpa using hz
  | succ k ih =>
    have e : z + ((k + 1 : ℕ) : ℤ) • r = (z + (k : ℤ) • r) + r := by
      rw [Nat.cast_succ, add_smul, one_smul, add_assoc]
    rw [e]; exact h _ ih

/-- **Cone lemma.**  A lattice-convex `R`, closed under `+r₁` and `+r₂`, contains every lattice
point `y = x + α r₁ + β r₂` (real `α, β ≥ 0`) over a point `x ∈ R`. -/
theorem cone_mem {R : Set (ℤ × ℤ)} (hlc : IsLatticeConvexRegion R) {r₁ r₂ : ℤ × ℤ}
    (h1 : ∀ z ∈ R, z + r₁ ∈ R) (h2 : ∀ z ∈ R, z + r₂ ∈ R) {x y : ℤ × ℤ} (hx : x ∈ R)
    {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hy : toReal y = toReal x + α • toReal r₁ + β • toReal r₂) : y ∈ R := by
  obtain ⟨C, hC, -, hReq⟩ := hlc
  have hmem : ∀ z, z ∈ R → toReal z ∈ C := fun z hz => by rw [hReq] at hz; exact hz
  -- step A: for every natural `k`, the real point `x + k r₁ + β r₂` is in `C`
  have hA : ∀ k : ℕ, toReal x + (k : ℝ) • toReal r₁ + β • toReal r₂ ∈ C := by
    intro k
    have hk : x + (k : ℤ) • r₁ ∈ R := mem_of_nat_iter h1 hx k
    have hray : ∀ j : ℕ, toReal (x + (k : ℤ) • r₁) + (j : ℝ) • toReal r₂ ∈ C := by
      intro j
      have := hmem _ (mem_of_nat_iter h2 hk j)
      rw [toReal_add' (x + (k : ℤ) • r₁) ((j : ℤ) • r₂), toReal_zsmul'] at this
      simpa using this
    have := real_ray_mem hC hray hβ
    rw [toReal_add', toReal_zsmul'] at this
    simpa using this
  have hB := real_ray_mem hC (q := toReal x + β • toReal r₂) (v := toReal r₁)
    (fun k => by
      have := hA k
      rwa [add_right_comm] at this) hα
  have hfin : toReal y ∈ C := by
    rw [hy]
    have : toReal x + β • toReal r₂ + α • toReal r₁ = toReal x + α • toReal r₁ + β • toReal r₂ := by
      abel
    rw [← this]; exact hB
  rw [hReq]; exact hfin

/-! ## §2. The quadrant lemma -/

/-- **Quadrant lemma.**  `R` is lattice-convex, closed under `+(-(dir nxt))` and `+(-(dir J))`, and
`δ = det J nxt > 0`.  Then any lattice point weakly below-left (in the `(dot (-J), dot nxt)`
coordinates) of a point of `R` is in `R`. -/
theorem quadrant_mem {R : Set (ℤ × ℤ)} (hlc : IsLatticeConvexRegion R) {J nxt : ℤ × ℤ}
    (hδ : 0 < det J nxt)
    (h1 : ∀ z ∈ R, z + (-(dir nxt)) ∈ R) (h2 : ∀ z ∈ R, z + (-(dir J)) ∈ R)
    {x y : ℤ × ℤ} (hx : x ∈ R)
    (hl : dot (-J) y ≤ dot (-J) x) (hv : dot nxt y ≤ dot nxt x) : y ∈ R := by
  have hδR : (0 : ℝ) < (det J nxt : ℝ) := by exact_mod_cast hδ
  have hA0 : (0 : ℝ) ≤ ((dot (-J) x - dot (-J) y : ℤ) : ℝ) / (det J nxt : ℝ) :=
    div_nonneg (by exact_mod_cast sub_nonneg.mpr hl) hδR.le
  have hB0 : (0 : ℝ) ≤ ((dot nxt x - dot nxt y : ℤ) : ℝ) / (det J nxt : ℝ) :=
    div_nonneg (by exact_mod_cast sub_nonneg.mpr hv) hδR.le
  refine cone_mem hlc h1 h2 hx hA0 hB0 ?_
  have hne : (det J nxt : ℝ) ≠ 0 := hδR.ne'
  apply Prod.ext
  · simp only [toReal, dot, det, dir, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul, Prod.fst_neg, Prod.snd_neg, Int.cast_sub, Int.cast_add, Int.cast_mul,
      Int.cast_neg] at hne ⊢
    field_simp
    ring
  · simp only [toReal, dot, det, dir, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul, Prod.fst_neg, Prod.snd_neg, Int.cast_sub, Int.cast_add, Int.cast_mul,
      Int.cast_neg] at hne ⊢
    field_simp
    ring

/-! ## §3. Small algebra -/

private theorem dot_zsmul'' (m : ℤ × ℤ) (k : ℤ) (z : ℤ × ℤ) : dot m (k • z) = k * dot m z := by
  simp only [dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

private theorem prim_neg' {n : ℤ × ℤ} (h : Prim n) : Prim (-n) := by
  unfold Prim at h ⊢
  simpa [Int.gcd_neg, Int.neg_gcd] using h

/-! ## §4. The theorem -/

theorem bottom_of_pinned {ξ : Config ℤ} (d : Nivat.Colle35.DecompDataZ ξ)
    {Ah : ℕ → Set (ℤ × ℤ)} {J prv nxt g : ℤ × ℤ}
    (hfin : ∀ i, (Ah i).Finite)
    (henv : ∀ i, Nivat.LE2.EnvOf (↑d.Sphi : Set (ℤ × ℤ)) (Ah i))
    (hmono : ∀ i j, i ≤ j → Ah i ⊆ Ah j)
    (hJ : J ∈ Nivat.LE2.E (↑d.Sphi : Set (ℤ × ℤ)))
    (hprv : prv ∈ Nivat.LE2.E (↑d.Sphi : Set (ℤ × ℤ)))
    (hnxt : nxt ∈ Nivat.LE2.E (↑d.Sphi : Set (ℤ × ℤ)))
    (hdp : 0 < det prv J) (hdn : 0 < det J nxt)
    (hadjP : ∀ μ ∈ Nivat.LE2.E (↑d.Sphi : Set (ℤ × ℤ)), ¬(0 < det prv μ ∧ 0 < det μ J))
    (hadjN : ∀ μ ∈ Nivat.LE2.E (↑d.Sphi : Set (ℤ × ℤ)), ¬(0 < det J μ ∧ 0 < det μ nxt))
    (hpin : ∀ i, Nivat.PolyChain.faceStart (Ah i) J
        + (Nivat.PolyChain.faceLen (Ah i) J : ℤ) • Nivat.LE2.dir J = g)
    (hunb : ∀ L : ℕ, ∃ i, L ≤ Nivat.PolyChain.faceLen (Ah i) J)
    (hhp : ∀ i, Ah i ⊆ Nivat.CK224.halfPlaneGE (-J) (Nivat.LE2.dot (-J) g))
    (hswept : Nivat.MaxEnv.SweptClosed (⋃ i, Ah i) (-(Nivat.LE2.dir nxt)) (-J)
      (Nivat.LE2.dot (-J) g))
    (hray : ∀ k : ℕ, g - (k : ℤ) • Nivat.LE2.dir J ∈ ⋃ i, Ah i)
    (hsupp : ∀ z ∈ ⋃ i, Ah i, Nivat.LE2.dot nxt z ≤ Nivat.LE2.dot nxt g)
    (hconv : IsLatticeConvexRegion (⋃ i, Ah i))
    (F : Nivat.Colle35.FaceBlock d.Sphi (-J) (-(Nivat.LE2.dir J))) :
    ∀ ε : ℕ, ∃ (z₀ : ℤ × ℤ) (L : ℤ),
      Nivat.LE2.dot (-J) z₀ = Nivat.LE2.dot (-J) g - (ε : ℤ) - 1 ∧
      (∀ k : ℤ, L ≤ k → z₀ + k • (-(Nivat.LE2.dir J)) ∈
        Nivat.MaxEnv.reachSet (⋃ i, Ah i) (-(Nivat.LE2.dir nxt))) ∧
      (∀ b ∈ d.Sphi, ∀ k : ℤ, L ≤ k →
        z₀ + k • (-(Nivat.LE2.dir J)) + (b - F.a) ∈
          Nivat.MaxEnv.reachSet (⋃ i, Ah i) (-(Nivat.LE2.dir nxt))) ∧
      (∀ z ∈ Nivat.MaxEnv.shell (⋃ i, Ah i) (-(Nivat.LE2.dir nxt)) (-J)
          (Nivat.LE2.dot (-J) g) (ε + 1),
        z ∈ Nivat.MaxEnv.shell (⋃ i, Ah i) (-(Nivat.LE2.dir nxt)) (-J)
          (Nivat.LE2.dot (-J) g) ε ∨
          ∃ k : ℤ, L ≤ k ∧ z = z₀ + k • (-(Nivat.LE2.dir J))) := by
  classical
  set S : Set (ℤ × ℤ) := (↑d.Sphi : Set (ℤ × ℤ)) with hS
  set Ainf : Set (ℤ × ℤ) := ⋃ i, Ah i with hAinf
  set δ : ℤ := det J nxt with hδdef
  have hSfin : S.Finite := d.toDecompData.Sphi.finite_toSet
  have hSlc : IsLatticeConvexRegion S :=
    Nivat.ChainAsm.isLatticeConvexRegion_coe F.latticeConvex_S
  have hUE : (E S).Finite := finite_E_of_finite hSfin
  have hEi : ∀ i, E (Ah i) = E S := fun i => Enveloped.E_eq hUE (henv i)
  have hlci : ∀ i, IsLatticeConvexRegion (Ah i) := fun i => (henv i).1.1
  have hJi : ∀ i, J ∈ E (Ah i) := fun i => (hEi i) ▸ hJ
  have hnxti : ∀ i, nxt ∈ E (Ah i) := fun i => (hEi i) ▸ hnxt
  have hadji : ∀ i, ∀ μ ∈ E (Ah i), ¬(0 < det J μ ∧ 0 < det μ nxt) :=
    fun i μ hμ => hadjN μ ((hEi i) ▸ hμ)
  -- the pinned corner is the start of the `nxt`-face of every `Ah i`
  have hgstart : ∀ i, Nivat.PolyChain.faceStart (Ah i) nxt = g := by
    intro i
    have := Nivat.PolyChain.adjacent_shared_vertex (hfin i) (hlci i) (hJi i) (hnxti i) hdn
      (hadji i)
    rw [hpin i] at this
    exact this.symm
  -- `F.a` is the start of the `nxt`-face of `S`
  have hnpvJ : dot nxt (-(dir J)) < 0 := by
    have : dot nxt (-(dir J)) = -δ := by
      simp only [dot, dir, det, hδdef, Prod.fst_neg, Prod.snd_neg]; ring
    rw [this]; omega
  have hFa : F.a = Nivat.PolyChain.faceStart S nxt := by
    have hcore := Nivat.FanEndpoint.mem_face_of_adjacent_endpoint_cw_core hSfin hSlc hJ hnxt hdn
      (Nivat.FanEndpoint.faceBlock_a_mem_face F) (Nivat.FanEndpoint.faceBlock_faceparam F)
      hnpvJ hadjN
    rw [hcore.2]
    exact Nivat.PolyChain.adjacent_shared_vertex hSfin hSlc hJ hnxt hdn hadjN
  -- the window at the pinned corner
  have hwin_g : ∀ b ∈ S, g + (b - F.a) ∈ Ainf := by
    intro b hb
    have h := Nivat.Hole1QShell.sphi_shift_subset' d (henv 0) (hfin 0) hnxt b hb
    rw [hgstart 0, ← hFa] at h
    exact Set.mem_iUnion.mpr ⟨0, h⟩
  -- recession
  have hgA : g ∈ Ainf := by simpa using hray 0
  have hrayV : ∀ k : ℕ, g + (k : ℤ) • (-(dir J)) ∈ Ainf := by
    intro k
    have := hray k
    rwa [smul_neg, ← sub_eq_add_neg]
  have hrecJ : ∀ z ∈ Ainf, z + (-(dir J)) ∈ Ainf := Nivat.Colle35.rec_of_ray hconv hrayV
  -- `g + dir nxt ∈ Ainf`: the `nxt`-face of `Ah 0` has at least two points
  have hprev : g - (-(dir nxt)) ∈ Ainf := by
    have hseg := Nivat.PolyChain.face_eq_segment (hlci 0) (hfin 0) (hnxti 0)
    have hlen := Nivat.PolyChain.one_le_faceLen (hfin 0) (hnxti 0)
    have hmem : Nivat.PolyChain.faceStart (Ah 0) nxt + ((1 : ℕ) : ℤ) • dir nxt
        ∈ face (Ah 0) nxt := by
      rw [hseg]; exact ⟨1, hlen, rfl⟩
    rw [hgstart 0] at hmem
    have : g - (-(dir nxt)) = g + ((1 : ℕ) : ℤ) • dir nxt := by simp [sub_eq_add_neg]
    rw [this]
    exact Set.mem_iUnion.mpr ⟨0, (face_subset _ _) hmem⟩
  -- edge data at the pinned corner and lattice-convexity of the swept set
  have hJne : J ≠ 0 := (mem_E_iff.mp hJ).1.ne_zero
  have hdirJne : dir J ≠ 0 := by
    intro h
    apply hJne
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only [dir, Prod.fst_zero, Prod.snd_zero] at h1 h2
    exact Prod.ext (by simpa using h2) (by simpa using h1)
  have hnxtne : nxt ≠ 0 := (mem_E_iff.mp hnxt).1.ne_zero
  have hnJvJ : dot (-J) (-(dir J)) = 0 := by
    simp only [dot, dir, Prod.fst_neg, Prod.snd_neg]; ring
  have hnJv : dot (-J) (-(dir nxt)) < 0 := by
    have : dot (-J) (-(dir nxt)) = -δ := by
      simp only [dot, dir, det, hδdef, Prod.fst_neg, Prod.snd_neg]; ring
    rw [this]; omega
  have hAhalf : ∀ z ∈ Ainf, dot (-J) g ≤ dot (-J) z := fun z hz => Set.iUnion_subset hhp hz
  have hzero : reachSet Ainf (-(dir nxt)) ∩ Nivat.CK224.halfPlaneGE (-J) (dot (-J) g) ⊆ Ainf := by
    rintro z ⟨⟨a, ha, t, rfl⟩, hlev⟩
    exact hswept a ha t hlev
  have e : Nivat.Colle35.EdgeJ1Data Ainf (-(dir nxt)) (-J) (dot (-J) g) :=
    { a₀ := g
      a₀_mem := hgA
      a₀_on := rfl
      prev_mem := hprev
      nJ1 := -nxt
      dot_nJ1_v := by simp only [dot, dir, Prod.fst_neg, Prod.snd_neg]; ring
      nJ1_ne := neg_ne_zero.mpr hnxtne
      support := fun z hz => by
        rw [dot_neg_left, dot_neg_left]; exact neg_le_neg (hsupp z hz) }
  have hRlc : IsLatticeConvexRegion (reachSet Ainf (-(dir nxt))) :=
    e.isLatticeConvexRegion_reachSet hconv hAhalf hzero hrecJ hnJvJ hnJv (neg_ne_zero.mpr hdirJne)
  -- closure properties of `R`
  have hR1 : ∀ z ∈ reachSet Ainf (-(dir nxt)), z + (-(dir nxt)) ∈ reachSet Ainf (-(dir nxt)) := by
    rintro z ⟨a, ha, t, rfl⟩
    refine ⟨a, ha, t + 1, ?_⟩
    rw [Nat.cast_succ, add_smul, one_smul, add_assoc]
  have hR2 : ∀ z ∈ reachSet Ainf (-(dir nxt)), z + (-(dir J)) ∈ reachSet Ainf (-(dir nxt)) := by
    rintro z ⟨a, ha, t, rfl⟩
    refine ⟨a + (-(dir J)), hrecJ a ha, t, ?_⟩
    rw [add_right_comm]
  have hRsupp : ∀ z ∈ reachSet Ainf (-(dir nxt)), dot nxt z ≤ dot nxt g := by
    rintro z ⟨a, ha, t, rfl⟩
    have : dot nxt (a + (t : ℤ) • (-(dir nxt))) = dot nxt a := by
      simp only [dot, dir, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
        Prod.fst_neg, Prod.snd_neg]; ring
    rw [this]; exact hsupp a ha
  have hAR : ∀ z ∈ Ainf, z ∈ reachSet Ainf (-(dir nxt)) := fun z hz => ⟨z, hz, 0, by simp⟩
  have hquad : ∀ x ∈ reachSet Ainf (-(dir nxt)), ∀ y : ℤ × ℤ,
      dot (-J) y ≤ dot (-J) x → dot nxt y ≤ dot nxt x → y ∈ reachSet Ainf (-(dir nxt)) :=
    fun x hx y hl hv => quadrant_mem hRlc hdn hR1 hR2 hx hl hv
  -- primitivity
  have hJprim : Prim J := (mem_E_iff.mp hJ).1
  have hnJprim : Prim (-J) := prim_neg' hJprim
  have hvJprim : Prim (-(dir J)) := prim_neg' (Nivat.LaneCdOppEdge.prim_dir hJprim)
  intro ε
  obtain ⟨z₁, hz₁⟩ := Nivat.HalfPlaneFamily.exists_dot_eq_of_primitive
    (prim_iff_primitive.mp hnJprim) (dot (-J) g - (ε : ℤ) - 1)
  set z₀ : ℤ × ℤ := z₁ with hz₀def
  set M : ℤ := dot nxt g with hMdef
  set X : ℤ := dot nxt z₀ - M with hXdef
  set L : ℤ := -((-X) / δ) with hLdef
  have hδpos : 0 < δ := hdn
  have hdotv : ∀ k : ℤ, dot nxt (z₀ + k • (-(dir J))) = dot nxt z₀ - k * δ := by
    intro k
    simp only [dot, dir, det, hδdef, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul, Prod.fst_neg, Prod.snd_neg]; ring
  have hLiff : ∀ k : ℤ, L ≤ k ↔ dot nxt (z₀ + k • (-(dir J))) ≤ M := by
    intro k
    rw [hdotv]
    have h1 : L ≤ k ↔ -k ≤ (-X) / δ := by rw [hLdef]; omega
    rw [h1, Int.le_ediv_iff_mul_le hδpos, hXdef]
    constructor <;> intro h <;> nlinarith
  have hlevk : ∀ k : ℤ, dot (-J) (z₀ + k • (-(dir J))) = dot (-J) g - (ε : ℤ) - 1 := by
    intro k
    rw [dot_add, dot_zsmul'', hnJvJ, mul_zero, add_zero, hz₁]
  refine ⟨z₀, L, hz₁, ?_, ?_, ?_⟩
  · intro k hk
    refine hquad g (hAR g hgA) _ ?_ ((hLiff k).mp hk)
    rw [hlevk]; omega
  · intro b hb k hk
    have hbS : b ∈ S := Finset.mem_coe.mpr hb
    have hx := hAR _ (hwin_g b hbS)
    refine hquad _ hx _ ?_ ?_
    · have := hlevk k
      simp only [dot_add] at this ⊢
      omega
    · have := (hLiff k).mp hk
      simp only [dot_add] at this ⊢
      omega
  · intro z hz
    rcases (mem_shell_succ_iff (A := Ainf) (v := -(dir nxt)) (n := -J)
        (c := dot (-J) g) (ε := ε) (z := z)).mp hz with h | ⟨hzR, hzl⟩
    · exact Or.inl h
    · right
      obtain ⟨s, hs⟩ := Nivat.NlmaxReachMin.exists_zsmul_of_dot_eq hnJprim hvJprim hnJvJ
        (x := z₀) (y := z) (by rw [hz₁, hzl])
      refine ⟨s, ?_, hs⟩
      rw [hLiff]
      have := hRsupp z hzR
      rw [hs] at this
      exact this

end Nivat.Hole1Bottom

#print axioms Nivat.Hole1Bottom.real_ray_mem
#print axioms Nivat.Hole1Bottom.cone_mem
#print axioms Nivat.Hole1Bottom.quadrant_mem
#print axioms Nivat.Hole1Bottom.bottom_of_pinned

-- ===== end tmp/wip/hole1-bottom.lean =====

-- ===== begin tmp/wip/hole1-qshell.lean =====
/-
Scratch checkpoint (hole 1, `exists_chainData`, `RegionSteps.lean` `exists_chainData`):
**the "push only the J-face" shell** — a replacement for the `:518` sweep shell.

Why (2026-09-30, integrator): `ChainData.shell` (`Lemma35.lean`, field `shell`) is free data;
only `shellInf` is pinned (`ChainShell.lean` `shellInf_eq`).  The Parts/GeomCore route
re-pinned `shell i ε` to `ShellMink.shellInter (hatOf i) (MaxEnv.shell …) w` (Collé `:518`,
sweep along `-v_{J+1}`), and every refutation of 2026-09-26..28 (`shellEnv_false_at_m_four`,
`not_backSeal_*`, `not_fillCover_oct8`, the `P`-nonempty collapse tables) is about that sweep.
Numeric pre-check (`tmp/wip/hole1-qshell-*.py`, faithful `(ℓ,ℓ_J)`-region zonotope model):
the sweep shell fails `Enveloped` on 1083/2448 rows even there, while the push shell below
passes `shellEnv`/`shellSubStrip`/`shellSubInf`/`shellProper`/`fillCover` on every row.

This file: the **general, chain-free** core lemma.  `T` is `E(S)`-enveloped, `nO ∈ E T` is the
outer normal of the face being pushed, `W = {p + j•vJ | j ≤ k}` is one new lattice row at
level `suppVal T nO + L`, with endpoints `p` (tight for `m1`) and `p + k•vJ` (tight for `m2`)
and strictly inside every other supporting half plane.  Then `latHull (T ∪ W)` is again
`E(S)`-enveloped.  Proof pattern = `ShellMink.enveloped_add_of_finite`: compute `E` and faces
of the finite set `T ∪ W`, then close convexity with `latHull` (`EnvelopedConvex.lean`).
The only geometric step, `E (T ∪ W) ⊆ E T`, uses the cone decomposition `isFrame_E`.

Per CLAUDE.md hard rule 19/22 this is **not** in `Nivat/`: no consumer yet.
-/

set_option autoImplicit false

namespace Nivat.Hole1QShell

open Nivat Nivat.LE2

/-! ## §0. The new row -/

/-- The new lattice row `p, p + vJ, …, p + k•vJ`. -/
def rowW (p vJ : ℤ × ℤ) (k : ℕ) : Set (ℤ × ℤ) :=
  {z | ∃ j : ℕ, j ≤ k ∧ z = p + (j : ℤ) • vJ}

/-- **The push shell**: the lattice hull of `T` together with the new row. -/
def pushShell (T : Set (ℤ × ℤ)) (p vJ : ℤ × ℤ) (k : ℕ) : Set (ℤ × ℤ) :=
  latHull (T ∪ rowW p vJ k)

theorem dot_row (n p vJ : ℤ × ℤ) (j : ℤ) : dot n (p + j • vJ) = dot n p + j * dot n vJ := by
  simp only [dot, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

theorem rowW_eq_image (p vJ : ℤ × ℤ) (k : ℕ) :
    rowW p vJ k = (fun j : ℕ => p + (j : ℤ) • vJ) '' ↑(Finset.range (k + 1)) := by
  ext z
  simp only [rowW, Set.mem_setOf_eq, Set.mem_image, Finset.coe_range, Set.mem_Iio]
  constructor
  · rintro ⟨j, hj, rfl⟩; exact ⟨j, by omega, rfl⟩
  · rintro ⟨j, hj, rfl⟩; exact ⟨j, by omega, rfl⟩

theorem rowW_finite (p vJ : ℤ × ℤ) (k : ℕ) : (rowW p vJ k).Finite := by
  rw [rowW_eq_image]; exact (Finset.finite_toSet _).image _

theorem rowW_encard (p vJ : ℤ × ℤ) (k : ℕ) (hvJ : vJ ≠ 0) :
    (rowW p vJ k).encard = (k : ℕ∞) + 1 := by
  rw [rowW_eq_image]
  have hinj : Set.InjOn (fun j : ℕ => p + (j : ℤ) • vJ) ↑(Finset.range (k + 1)) := by
    intro i _ j _ h
    have h' : (i : ℤ) • vJ = (j : ℤ) • vJ := add_left_cancel h
    exact_mod_cast smul_left_injective ℤ hvJ h'
  rw [hinj.encard_image, Set.encard_coe_eq_coe_finsetCard, Finset.card_range]
  push_cast; rfl

theorem left_mem_rowW (p vJ : ℤ × ℤ) (k : ℕ) : p ∈ rowW p vJ k := ⟨0, Nat.zero_le _, by simp⟩

theorem right_mem_rowW (p vJ : ℤ × ℤ) (k : ℕ) : p + (k : ℤ) • vJ ∈ rowW p vJ k :=
  ⟨k, le_rfl, rfl⟩

/-- A linear bound at both endpoints of the row holds along the whole row. -/
theorem dot_rowW_le {m p vJ : ℤ × ℤ} {k : ℕ} {s : ℤ} (h0 : dot m p ≤ s)
    (hk : dot m (p + (k : ℤ) • vJ) ≤ s) : ∀ z ∈ rowW p vJ k, dot m z ≤ s := by
  rintro _ ⟨j, hj, rfl⟩
  rw [dot_row] at hk ⊢
  have hj' : (j : ℤ) ≤ k := by exact_mod_cast hj
  rcases le_or_gt (dot m vJ) 0 with hd | hd
  · nlinarith [(Nat.cast_nonneg j : (0 : ℤ) ≤ j)]
  · nlinarith

/-! ## §1. Two small algebraic facts -/

/-- A primitive vector that is a positive real multiple of a primitive vector equals it. -/
theorem eq_of_prim_of_real_smul {n m : ℤ × ℤ} (hn : Prim n) (hm : Prim m) {lam : ℝ}
    (hlam : 0 < lam) (h1 : (n.1 : ℝ) = lam * m.1) (h2 : (n.2 : ℝ) = lam * m.2) : n = m := by
  have hdet : det m n = 0 := by
    have : ((det m n : ℤ) : ℝ) = 0 := by
      simp only [det]; push_cast; rw [h1, h2]; ring
    exact_mod_cast this
  rcases eq_or_neg_of_prim_of_det_eq_zero hm hn hdet with h | h
  · exact h
  · exfalso
    apply hm.ne_zero
    have e1 : (lam + 1) * (m.1 : ℝ) = 0 := by
      have := h1; rw [h] at this; simp only [Prod.fst_neg, Int.cast_neg] at this; linarith
    have e2 : (lam + 1) * (m.2 : ℝ) = 0 := by
      have := h2; rw [h] at this; simp only [Prod.snd_neg, Int.cast_neg] at this; linarith
    have hne : lam + 1 ≠ 0 := by linarith
    have m1 : (m.1 : ℝ) = 0 := (mul_eq_zero.mp e1).resolve_left hne
    have m2 : (m.2 : ℝ) = 0 := (mul_eq_zero.mp e2).resolve_left hne
    exact Prod.ext (by exact_mod_cast m1) (by exact_mod_cast m2)

theorem rdotZ_cast (n z : ℤ × ℤ) : rdotZ ((n.1 : ℝ), (n.2 : ℝ)) z = (dot n z : ℝ) := by
  simp only [rdotZ, dot]; push_cast; ring

/-! ## §2. The endpoint lemma (the only geometric step) -/

/-- **Endpoint lemma.**  Suppose the new endpoint `e` (tight for `mt`, level `suppVal T nO + L`,
strictly inside every other supporting half plane except `nO`) ties in direction `n` with a
point `t` of `T` maximising `n` on `T`, and `e` beats the other endpoint `e'` (tight for `mo`).
Then `n` is already an edge normal of `T`. -/
theorem mem_E_of_endpoint {T : Set (ℤ × ℤ)} (hfin : T.Finite) (hne : T.Nonempty)
    (harea : PosArea T) {n nO mt mo e e' : ℤ × ℤ} {L : ℤ} (hn : Prim n) (hL : 0 < L)
    (hmo_mt : mo ≠ mt) (hmo_nO : mo ≠ nO)
    (he_lev : dot nO e = suppVal T nO + L) (he'_lev : dot nO e' = suppVal T nO + L)
    (he_mt : dot mt e = suppVal T mt) (he'_mo : dot mo e' = suppVal T mo)
    (hse : ∀ m ∈ E T, m ≠ mt → m ≠ nO → dot m e < suppVal T m)
    (hadj : ∀ m ∈ E T, m ≠ nO → m ≠ mt → m ≠ mo → ∀ v ∈ face T nO, v ∉ face T m)
    {t : ℤ × ℤ} (ht : t ∈ face T n) (hte : dot n t = dot n e) (hmax : dot n e' ≤ dot n e) :
    n ∈ E T := by
  set c : ℝ × ℝ := ((n.1 : ℝ), (n.2 : ℝ)) with hcdef
  have hc0 : c ≠ 0 := by
    intro h
    apply hn.ne_zero
    have h1 : (n.1 : ℝ) = 0 := congrArg Prod.fst h
    have h2 : (n.2 : ℝ) = 0 := congrArg Prod.snd h
    exact Prod.ext (by exact_mod_cast h1) (by exact_mod_cast h2)
  obtain ⟨n1, n2, a, b, hn1, hn2, ha, hb, hc1, hc2, v, hvmax, hv1, hv2⟩ :=
    isFrame_E hfin hne harea c hc0
  have hc1' : (n.1 : ℝ) = a * n1.1 + b * n2.1 := hc1
  have hc2' : (n.2 : ℝ) = a * n1.2 + b * n2.2 := hc2
  have decomp : ∀ z : ℤ × ℤ, (dot n z : ℝ) = a * dot n1 z + b * dot n2 z := by
    intro z; simp only [dot]; push_cast; rw [hc1', hc2']; ring
  -- `v` and `t` both maximise `n` on `T`
  have hvt : dot n v = dot n t := by
    have h1 : dot n v ≤ dot n t := ht.2 v hv1.1
    have h2 : (dot n t : ℝ) ≤ dot n v := by
      have := hvmax t ht.1; rwa [rdotZ_cast, rdotZ_cast] at this
    have h2' : dot n t ≤ dot n v := by exact_mod_cast h2
    omega
  have hs1 : dot n1 v = suppVal T n1 := (suppVal_eq hv1).symm
  have hs2 : dot n2 v = suppVal T n2 := (suppVal_eq hv2).symm
  -- the balance equation `a·δ(n1) + b·δ(n2) = 0`
  have hbal : a * ((dot n1 e : ℝ) - suppVal T n1) + b * ((dot n2 e : ℝ) - suppVal T n2) = 0 := by
    have hA := decomp e
    have hB := decomp v
    rw [hs1, hs2] at hB
    have : (dot n e : ℝ) = dot n v := by exact_mod_cast (hvt.trans hte).symm
    linarith
  -- sign of `δ(m) := dot m e - suppVal T m` off `nO`
  have hδle : ∀ m ∈ E T, m ≠ nO → dot m e ≤ suppVal T m := by
    intro m hm hmO
    by_cases hmt : m = mt
    · subst hmt; exact he_mt.le
    · exact (hse m hm hmt hmO).le
  have hδ0 : ∀ m ∈ E T, m ≠ nO → dot m e = suppVal T m → m = mt := by
    intro m hm hmO heq
    by_contra hmt
    have := hse m hm hmt hmO; omega
  -- three ways to conclude
  have hprim1 : Prim n1 := hn1.1
  have hprim2 : Prim n2 := hn2.1
  have fin_b0 : b = 0 → n ∈ E T := by
    intro hb0
    have ha0 : 0 < a := by
      rcases ha.lt_or_eq with h | h
      · exact h
      · exfalso; apply hc0
        rw [hcdef]; ext
        · show (n.1 : ℝ) = 0; rw [hc1', ← h, hb0]; ring
        · show (n.2 : ℝ) = 0; rw [hc2', ← h, hb0]; ring
    have := eq_of_prim_of_real_smul hn hprim1 ha0 (by rw [hc1', hb0]; ring)
      (by rw [hc2', hb0]; ring)
    rw [this]; exact hn1
  have fin_a0 : a = 0 → n ∈ E T := by
    intro ha0
    have hb0 : 0 < b := by
      rcases hb.lt_or_eq with h | h
      · exact h
      · exfalso; apply hc0
        rw [hcdef]; ext
        · show (n.1 : ℝ) = 0; rw [hc1', ← h, ha0]; ring
        · show (n.2 : ℝ) = 0; rw [hc2', ← h, ha0]; ring
    have := eq_of_prim_of_real_smul hn hprim2 hb0 (by rw [hc1', ha0]; ring)
      (by rw [hc2', ha0]; ring)
    rw [this]; exact hn2
  have fin_eq : n1 = n2 → 0 < a → n ∈ E T := by
    intro h12 ha0
    subst h12
    have := eq_of_prim_of_real_smul hn hprim1 (add_pos_of_pos_of_nonneg ha0 hb)
      (by rw [hc1']; ring) (by rw [hc2']; ring)
    rw [this]; exact hn1
  -- the contradiction used in the mixed case: `e'` would beat `e`
  have mixed : ∀ (x y : ℤ × ℤ) (α β : ℝ), 0 < α → 0 < β → x = nO → y ∈ E T → y ≠ nO →
      v ∈ face T x → v ∈ face T y →
      (∀ z : ℤ × ℤ, (dot n z : ℝ) = α * dot x z + β * dot y z) →
      α * ((dot x e : ℝ) - suppVal T x) + β * ((dot y e : ℝ) - suppVal T y) = 0 → False := by
    intro x y α β hα hβ hx hy hyO hvx hvy hdec hb'
    rw [hx] at hvx hdec hb'
    rw [he_lev] at hb'
    have hαL : 0 < α * (L : ℝ) := mul_pos hα (by exact_mod_cast hL)
    have hδy : (dot y e : ℝ) - suppVal T y < 0 := by
      push_cast at hb'
      nlinarith
    have hymt : y ≠ mt := by
      intro h; rw [h, he_mt] at hδy; simp at hδy
    have hymo : y = mo := by
      by_contra hymo
      exact hadj y hy hyO hymt hymo v hvx hvy
    rw [hymo] at hdec hy
    have hlt : dot mo e < suppVal T mo := hse mo hy hmo_mt hmo_nO
    have hlt' : ((dot mo e : ℤ) : ℝ) < suppVal T mo := by exact_mod_cast hlt
    have h3 : (dot nO e' : ℝ) = (dot nO e : ℝ) := by rw [he'_lev, he_lev]
    have h4 : (dot mo e' : ℝ) = suppVal T mo := by exact_mod_cast he'_mo
    have hgap : (dot n e' : ℝ) - dot n e = β * ((suppVal T mo : ℝ) - dot mo e) := by
      linear_combination hdec e' - hdec e + α * h3 + β * h4
    have hmax' : (dot n e' : ℝ) ≤ dot n e := by exact_mod_cast hmax
    nlinarith
  -- case split on whether `n1`, `n2` are the pushed normal
  rcases ha.lt_or_eq with ha0 | ha0
  · rcases hb.lt_or_eq with hb0 | hb0
    · by_cases h1 : n1 = nO
      · by_cases h2 : n2 = nO
        · exact fin_eq (h1.trans h2.symm) ha0
        · exact (mixed n1 n2 a b ha0 hb0 h1 hn2 h2 hv1 hv2 decomp hbal).elim
      · by_cases h2 : n2 = nO
        · refine (mixed n2 n1 b a hb0 ha0 h2 hn1 h1 hv2 hv1 (fun z => ?_) (by linarith)).elim
          rw [decomp z]; ring
        · -- both off `nO`: both `δ ≤ 0`, sum `0`, so both `0`, so both `= mt`
          have d1 : dot n1 e ≤ suppVal T n1 := hδle n1 hn1 h1
          have d2 : dot n2 e ≤ suppVal T n2 := hδle n2 hn2 h2
          have d1' : ((dot n1 e : ℤ) : ℝ) ≤ suppVal T n1 := by exact_mod_cast d1
          have d2' : ((dot n2 e : ℤ) : ℝ) ≤ suppVal T n2 := by exact_mod_cast d2
          have e1 : ((dot n1 e : ℤ) : ℝ) = suppVal T n1 := by nlinarith
          have e2 : ((dot n2 e : ℤ) : ℝ) = suppVal T n2 := by nlinarith
          have k1 := hδ0 n1 hn1 h1 (by exact_mod_cast e1)
          have k2 := hδ0 n2 hn2 h2 (by exact_mod_cast e2)
          exact fin_eq (k1.trans k2.symm) ha0
    · exact fin_b0 hb0.symm
  · exact fin_a0 ha0.symm

/-! ## §3. The core lemma -/

variable {S T : Set (ℤ × ℤ)} {nO m1 m2 p vJ : ℤ × ℤ} {k : ℕ} {L : ℤ}

/-- Standing hypotheses of the push, bundled. -/
structure PushData (S T : Set (ℤ × ℤ)) (nO m1 m2 p vJ : ℤ × ℤ) (k : ℕ) (L : ℤ) : Prop where
  hTfin : T.Finite
  hTne : T.Nonempty
  harea : PosArea T
  hT : Enveloped S T
  hnO : nO ∈ E T
  hm1 : m1 ∈ E T
  hm2 : m2 ∈ E T
  h12 : m1 ≠ m2
  h1O : m1 ≠ nO
  h2O : m2 ≠ nO
  hvJ : vJ ≠ 0
  hvJO : dot nO vJ = 0
  hL : 0 < L
  hlev : dot nO p = suppVal T nO + L
  hp1 : dot m1 p = suppVal T m1
  hp2 : dot m2 (p + (k : ℤ) • vJ) = suppVal T m2
  hs1 : ∀ m ∈ E T, m ≠ m1 → m ≠ nO → dot m p < suppVal T m
  hs2 : ∀ m ∈ E T, m ≠ m2 → m ≠ nO → dot m (p + (k : ℤ) • vJ) < suppVal T m
  hadj : ∀ m ∈ E T, m ≠ nO → m ≠ m1 → m ≠ m2 → ∀ v ∈ face T nO, v ∉ face T m
  hk : 1 ≤ k
  hlen : (face S nO).encard ≤ (k : ℕ∞) + 1

namespace PushData

variable (D : PushData S T nO m1 m2 p vJ k L)
include D

theorem rowW_lev : ∀ z ∈ rowW p vJ k, dot nO z = suppVal T nO + L := by
  rintro _ ⟨j, -, rfl⟩
  rw [dot_row, D.hvJO, D.hlev]; ring

theorem rowW_le (m : ℤ × ℤ) (hm : m ∈ E T) (hmO : m ≠ nO) :
    ∀ z ∈ rowW p vJ k, dot m z ≤ suppVal T m := by
  refine dot_rowW_le ?_ ?_
  · by_cases h : m = m1
    · subst h; exact D.hp1.le
    · exact (D.hs1 m hm h hmO).le
  · by_cases h : m = m2
    · subst h; exact D.hp2.le
    · exact (D.hs2 m hm h hmO).le

theorem Y_finite : (T ∪ rowW p vJ k).Finite := D.hTfin.union (rowW_finite p vJ k)

theorem face_T_subset (m : ℤ × ℤ) (hm : m ∈ E T) (hmO : m ≠ nO) :
    face T m ⊆ face (T ∪ rowW p vJ k) m := by
  intro z hz
  refine ⟨Or.inl hz.1, fun y hy => ?_⟩
  rcases hy with hy | hy
  · exact hz.2 y hy
  · rw [← suppVal_eq hz]; exact D.rowW_le m hm hmO y hy

theorem rowW_subset_face : rowW p vJ k ⊆ face (T ∪ rowW p vJ k) nO := by
  intro z hz
  refine ⟨Or.inr hz, fun y hy => ?_⟩
  rw [D.rowW_lev z hz]
  rcases hy with hy | hy
  · have := le_suppVal D.hTfin D.hTne (n := nO) hy; linarith [D.hL]
  · rw [D.rowW_lev y hy]

theorem E_T_subset : E T ⊆ E (T ∪ rowW p vJ k) := by
  intro m hm
  refine ⟨hm.1, ?_⟩
  by_cases hmO : m = nO
  · subst hmO
    refine nontrivial_of_subset D.rowW_subset_face ⟨p, left_mem_rowW p vJ k,
      p + (k : ℤ) • vJ, right_mem_rowW p vJ k, ?_⟩
    intro h
    have h' : p + (k : ℤ) • vJ = p + (0 : ℤ) • vJ := by rw [zero_smul, add_zero]; exact h.symm
    have h'' := smul_left_injective ℤ D.hvJ (add_left_cancel h')
    have : (k : ℤ) = 0 := h''
    have := D.hk; omega
  · exact nontrivial_of_subset (D.face_T_subset m hm hmO) hm.2

/-- **`E (T ∪ W) ⊆ E T`**: the new row creates no new edge direction. -/
theorem E_subset_T : E (T ∪ rowW p vJ k) ⊆ E T := by
  intro n hn
  obtain ⟨hprim, x, hx, y, hy, hxy⟩ := hn
  set Y := T ∪ rowW p vJ k with hY
  by_cases hW : ∃ w ∈ rowW p vJ k, w ∈ face Y n
  · obtain ⟨w, ⟨j, hj, rfl⟩, hwf⟩ := hW
    by_cases hd : dot n vJ = 0
    · -- `n ⊥ vJ`, so `n = ± nO`
      have hdet : det nO n = 0 :=
        det_eq_zero_of_dot_eq_zero D.hvJ (by rw [dot_comm]; exact D.hvJO)
          (by rw [dot_comm]; exact hd)
      rcases eq_or_neg_of_prim_of_det_eq_zero D.hnO.1 hprim hdet with h | h
      · rw [h]; exact D.hnO
      · exfalso
        obtain ⟨t0, ht0⟩ := D.hTne
        have h1 := hwf.2 t0 (Or.inl ht0)
        rw [h, dot_neg_left, dot_neg_left, dot_row, D.hvJO, D.hlev] at h1
        have h2 := le_suppVal D.hTfin D.hTne (n := nO) ht0
        linarith [D.hL]
    · -- `n` is not constant along the row: the row meets the face in at most one point,
      -- so the face also contains a point `t` of `T`
      have hrow_single : ∀ a ∈ face Y n, ∀ b ∈ face Y n, a ∈ rowW p vJ k →
          b ∈ rowW p vJ k → a = b := by
        rintro a ha b hb ⟨i, -, rfl⟩ ⟨i', -, rfl⟩
        have e1 := ha.2 _ hb.1
        have e2 := hb.2 _ ha.1
        rw [dot_row, dot_row] at e1 e2
        have : ((i : ℤ) - i') * dot n vJ = 0 := by nlinarith
        rcases mul_eq_zero.mp this with h | h
        · have : (i : ℤ) = i' := by linarith
          rw [this]
        · exact absurd h hd
      have hT_in : ∃ t ∈ T, t ∈ face Y n := by
        rcases hx.1 with hxT | hxW
        · exact ⟨x, hxT, hx⟩
        · rcases hy.1 with hyT | hyW
          · exact ⟨y, hyT, hy⟩
          · exact absurd (hrow_single x hx y hy hxW hyW) hxy
      obtain ⟨t, htT, htf⟩ := hT_in
      have ht : t ∈ face T n := ⟨htT, fun z hz => htf.2 z (Or.inl hz)⟩
      have hte : dot n t = dot n (p + (j : ℤ) • vJ) :=
        le_antisymm (hwf.2 t (Or.inl htT)) (htf.2 _ (Or.inr ⟨j, hj, rfl⟩))
      have hpY : p ∈ Y := Or.inr (left_mem_rowW p vJ k)
      have hqY : p + (k : ℤ) • vJ ∈ Y := Or.inr (right_mem_rowW p vJ k)
      rcases lt_or_gt_of_ne hd with hneg | hpos
      · -- `w = p`
        have hj0 : j = 0 := by
          by_contra hj0
          have hmem : p + ((j - 1 : ℕ) : ℤ) • vJ ∈ Y := Or.inr ⟨j - 1, by omega, rfl⟩
          have := hwf.2 _ hmem
          rw [dot_row, dot_row] at this
          have hc : ((j - 1 : ℕ) : ℤ) = (j : ℤ) - 1 := by push_cast [Nat.one_le_iff_ne_zero.mpr hj0]; ring
          rw [hc] at this; nlinarith
        subst hj0
        simp only [Nat.cast_zero, zero_smul, add_zero] at hwf hte
        exact mem_E_of_endpoint D.hTfin D.hTne D.harea hprim D.hL D.h12.symm D.h2O
          D.hlev (by rw [dot_row, D.hvJO, D.hlev]; ring) D.hp1 D.hp2 D.hs1
          (fun m hm h1 h2 h3 => D.hadj m hm h1 h2 h3) ht hte (hwf.2 _ hqY)
      · -- `w = p + k•vJ`
        have hjk : j = k := by
          by_contra hjk
          have hmem : p + ((j + 1 : ℕ) : ℤ) • vJ ∈ Y := Or.inr ⟨j + 1, by omega, rfl⟩
          have := hwf.2 _ hmem
          rw [dot_row, dot_row] at this
          push_cast at this; nlinarith
        subst hjk
        exact mem_E_of_endpoint D.hTfin D.hTne D.harea hprim D.hL D.h12 D.h1O
          (by rw [dot_row, D.hvJO, D.hlev]; ring) D.hlev D.hp2 D.hp1 D.hs2
          (fun m hm h1 h2 h3 => D.hadj m hm h1 h3 h2) ht hte (hwf.2 _ hpY)
  · -- the face avoids the row, so it is a face of `T`
    push_neg at hW
    have hsub : face Y n ⊆ face T n := by
      intro z hz
      rcases hz.1 with hzT | hzW
      · exact ⟨hzT, fun w hw => hz.2 w (Or.inl hw)⟩
      · exact absurd hz (hW z hzW)
    exact ⟨hprim, nontrivial_of_subset hsub ⟨x, hx, y, hy, hxy⟩⟩

theorem E_eq : E (T ∪ rowW p vJ k) = E T := Set.Subset.antisymm D.E_subset_T D.E_T_subset

/-- **Core lemma: the push shell is `E(S)`-enveloped.** -/
theorem enveloped : Enveloped S (pushShell T p vJ k) := by
  have hYfin := D.Y_finite
  refine ⟨⟨isLatticeConvexRegion_latHull hYfin, fun n hn => ?_⟩, ?_⟩
  · rw [pushShell, E_latHull hYfin, D.E_eq] at hn
    refine ⟨(D.hT.1.2 n hn).1, le_trans ?_ (Set.encard_mono (face_subset_face_latHull _ n))⟩
    by_cases hnO : n = nO
    · subst hnO
      calc (face S n).encard ≤ (k : ℕ∞) + 1 := D.hlen
        _ = (rowW p vJ k).encard := (rowW_encard p vJ k D.hvJ).symm
        _ ≤ _ := Set.encard_mono D.rowW_subset_face
    · exact le_trans (D.hT.1.2 n hn).2 (Set.encard_mono (D.face_T_subset n hn hnO))
  · rw [pushShell, E_latHull hYfin, D.E_eq]; exact D.hT.2

/-! ## §4. The cheap shell fields -/

theorem subset_pushShell : T ⊆ pushShell T p vJ k :=
  fun _ hz => subset_latHull _ (Or.inl hz)

theorem pushShell_finite : (pushShell T p vJ k).Finite := by
  -- bounded by the `2`-direction box cut out by `nO`, `-nO` and a transverse normal is not
  -- needed: `latHull` of a finite set is finite through its real hull being compact.
  have hYfin := D.Y_finite
  have hc : IsCompact (rHull (T ∪ rowW p vJ k)) :=
    Set.Finite.isCompact_convexHull (𝕜 := ℝ) (hYfin.image toReal)
  -- lattice points in a compact set are finite
  have hbdd := hc.isBounded
  obtain ⟨R, hR⟩ := hbdd.subset_closedBall (0 : ℝ × ℝ)
  refine (Set.finite_Icc ((-(⌈R⌉ : ℤ)), (-(⌈R⌉ : ℤ))) ((⌈R⌉ : ℤ), (⌈R⌉ : ℤ))).subset ?_
  intro z hz
  have hz' := hR (mem_latHull_iff.mp hz)
  rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def] at hz'
  simp only [toReal, Real.norm_eq_abs] at hz'
  have h1 : |(z.1 : ℝ)| ≤ R := by
    have := le_max_left ‖(toReal z).1‖ ‖(toReal z).2‖
    simp only [toReal, Real.norm_eq_abs] at this; linarith
  have h2 : |(z.2 : ℝ)| ≤ R := by
    have := le_max_right ‖(toReal z).1‖ ‖(toReal z).2‖
    simp only [toReal, Real.norm_eq_abs] at this; linarith
  have c1 : |z.1| ≤ ⌈R⌉ := by
    have := Int.le_ceil R
    have : (|z.1| : ℝ) ≤ ⌈R⌉ := by push_cast; linarith
    exact_mod_cast this
  have c2 : |z.2| ≤ ⌈R⌉ := by
    have := Int.le_ceil R
    have : (|z.2| : ℝ) ≤ ⌈R⌉ := by push_cast; linarith
    exact_mod_cast this
  rw [abs_le] at c1 c2
  exact ⟨⟨c1.1, c2.1⟩, ⟨c1.2, c2.2⟩⟩

/-- `shellProper`: the push shell strictly exceeds `T` (the point `p` is new). -/
theorem not_pushShell_subset : ¬ pushShell T p vJ k ⊆ T := by
  intro h
  have hp := h (subset_latHull _ (Or.inr (left_mem_rowW p vJ k)))
  have := le_suppVal D.hTfin D.hTne (n := nO) hp
  rw [D.hlev] at this; linarith [D.hL]

/-- The push shell stays inside every supporting half plane of `T` other than `nO`, and
inside the `nO` half plane moved out by `L`.  (Feeds `shellSubStrip` / `shellSubInf`.) -/
theorem pushShell_le : ∀ z ∈ pushShell T p vJ k,
    (∀ m ∈ E T, m ≠ nO → dot m z ≤ suppVal T m) ∧ dot nO z ≤ suppVal T nO + L := by
  intro z hz
  refine ⟨fun m hm hmO => dot_le_of_mem_latHull (fun y hy => ?_) hz,
    dot_le_of_mem_latHull (fun y hy => ?_) hz⟩
  · rcases hy with hy | hy
    · exact le_suppVal D.hTfin D.hTne hy
    · exact D.rowW_le m hm hmO y hy
  · rcases hy with hy | hy
    · have := le_suppVal D.hTfin D.hTne (n := nO) hy; linarith [D.hL]
    · exact (D.rowW_lev y hy).le

end PushData


/-! ## §6. `fillCover` for a push shell reduces to a window-fit margin -/

/-- **Window fit by H-representation.**  In a lattice-convex `Y` of positive area, the
translate `S - a' + z` lies in `Y` as soon as `z` keeps, against every edge `m` of `Y`, the
margin `suppVal S m - dot m a'` that `S` needs on the `m`-side of `a'`. -/
theorem window_fit {S : Finset (ℤ × ℤ)} {Y : Set (ℤ × ℤ)} (hSne : S.Nonempty)
    (hYfin : Y.Finite) (hYne : Y.Nonempty) (harea : PosArea Y) (hlc : IsLatticeConvexRegion Y)
    {a' z : ℤ × ℤ}
    (hz : ∀ m ∈ E Y, dot m z + (suppVal (↑S : Set (ℤ × ℤ)) m - dot m a') ≤ suppVal Y m) :
    ∀ b ∈ S, z + (b - a') ∈ Y := by
  intro b hb
  refine mem_of_dot_le_suppVal hYfin hYne harea hlc (fun m hm => ?_)
  have h1 := le_suppVal (S.finite_toSet) (by exact_mod_cast hSne) (n := m)
    (show b ∈ (↑S : Set (ℤ × ℤ)) from hb)
  have h2 := hz m hm
  rw [dot_add, dot_sub]; linarith

/-- **`fillCover` from window fit.**  If every point of `Y` outside the seed `X ⊆ Y` has its
whole `S`-window (anchored at `gen`) inside `Y`, and `gen` is a strict minimiser of some
covector on `S`, then `Y` is generated from `X` — in the unrestricted `Colle37.GenClosure`
form that `ChainData.fillCover` states. -/
theorem fillCover_of_window {S : Finset (ℤ × ℤ)} {gen n' : ℤ × ℤ} {X Y : Set (ℤ × ℤ)}
    (hYfin : Y.Finite) (hgenS : gen ∈ S) (hconv : LatticeConvex (S.erase gen))
    (hn' : ∀ b ∈ S.erase gen, dot n' gen < dot n' b)
    (hwin : ∀ z ∈ Y, z ∉ X → ∀ b ∈ S, z + (b - gen) ∈ Y) :
    ∀ z ∈ Y, Colle37.GenClosure S X z := by
  classical
  obtain ⟨C, hC⟩ : ∃ C : ℤ, ∀ z ∈ Y, dot n' z ≤ C := by
    obtain ⟨C, hC⟩ := (hYfin.image (fun z => dot n' z)).bddAbove
    exact ⟨C, fun z hz => hC ⟨z, hz, rfl⟩⟩
  have hsub : Y ⊆ MaxEnv.genClosure S gen X :=
    Nivat.LaneFillCover.subset_genClosure_of_covector (S := S) (gen := gen) (n' := n') (C := C)
      hC hn' (fun z hz => by
        by_cases hzX : z ∈ X
        · exact Or.inl hzX
        · exact Or.inr (fun b hb => Or.inr (hwin z hz hzX b (Finset.mem_of_mem_erase hb))))
  intro z hz
  exact Nivat.GenClosureWeaken.genClosure_subset_genClosure hgenS hconv z (hsub hz)

/-! ## §7. `shellSubStrip`: the strip only depends on `A i`, and the push shell stays in it -/

/-- **`H_{B}(ℓ) = H_{A}(ℓ)`** whenever `B ⊆ A ⊆ H_B(ℓ)` — so the strip of `ChainData.subStrip`
is determined by `A i` alone and `B i` drops out of `shellSubStrip`. -/
theorem halfStrip_eq_of_sandwich {A B : Set (ℤ × ℤ)} {v : ℤ × ℤ} (hBA : B ⊆ A)
    (hAB : A ⊆ Colle35.halfStrip B v) : Colle35.halfStrip B v = Colle35.halfStrip A v := by
  ext z
  constructor
  · rintro ⟨b, hb, t, rfl⟩; exact ⟨b, hBA hb, t, rfl⟩
  · rintro ⟨a, ha, t, rfl⟩
    obtain ⟨b, hb, t', rfl⟩ := hAB ha
    refine ⟨b, hb, t' + t, ?_⟩
    push_cast; rw [add_smul, add_assoc]

/-- The `shellSubStrip` target set, rewritten on the normalised side: with
`Ahat = A - kk•v` it is just `H_{Ahat}(ℓ)`. -/
theorem strip_target_eq {A B : Set (ℤ × ℤ)} {v : ℤ × ℤ} {K : ℕ} (hBA : B ⊆ A)
    (hAB : A ⊆ Colle35.halfStrip B v) :
    {z | z + (K : ℤ) • v ∈ Colle35.halfStrip B v} =
      Colle35.halfStrip {z | z + (K : ℤ) • v ∈ A} v := by
  rw [halfStrip_eq_of_sandwich hBA hAB]
  ext z
  constructor
  · rintro ⟨a, ha, t, ht⟩
    refine ⟨a - (K : ℤ) • v, by simpa using ha, t, ?_⟩
    rw [sub_add_eq_add_sub, ← ht]; abel
  · rintro ⟨a, ha, t, rfl⟩
    exact ⟨a + (K : ℤ) • v, ha, t, by abel⟩

/-- **Every intermediate lattice row of a lattice-convex set is occupied.**  If `T` has two
points `a, a + μ•vl` on one line and `c, c + ν•vl` on another (`μ, ν ≥ 1`), then every lattice
point `z` whose `nℓ`-level lies between theirs has a lattice point of `T` on its own row
`z + ℤ•vl`.  (Real convexity: the cross-section at `z`'s level has length `≥ |vl|`.) -/
theorem row_nonempty {T : Set (ℤ × ℤ)} (hlc : IsLatticeConvexRegion T) {nℓ vl a c z : ℤ × ℤ}
    {μ ν : ℕ} (hμ : 1 ≤ μ) (hν : 1 ≤ ν) (hn : nℓ ≠ 0) (hvl : vl ≠ 0) (hperp : dot nℓ vl = 0)
    (ha : a ∈ T) (ha' : a + (μ : ℤ) • vl ∈ T) (hc : c ∈ T) (hc' : c + (ν : ℤ) • vl ∈ T)
    (hlo : dot nℓ a ≤ dot nℓ z) (hhi : dot nℓ z ≤ dot nℓ c) :
    ∃ j : ℤ, z + j • vl ∈ T := by
  obtain ⟨C, hconv, -, rfl⟩ := hlc
  have hlo' : (dot nℓ a : ℝ) ≤ dot nℓ z := by exact_mod_cast hlo
  have hhi' : (dot nℓ z : ℝ) ≤ dot nℓ c := by exact_mod_cast hhi
  obtain ⟨lam, hl0, hl1, hlev⟩ : ∃ lam : ℝ, 0 ≤ lam ∧ lam ≤ 1 ∧
      (dot nℓ z : ℝ) = (1 - lam) * dot nℓ a + lam * dot nℓ c := by
    rcases eq_or_lt_of_le (le_trans hlo' hhi') with he | hlt
    · exact ⟨0, le_rfl, zero_le_one, by linarith⟩
    · refine ⟨((dot nℓ z : ℝ) - dot nℓ a) / ((dot nℓ c : ℝ) - dot nℓ a),
        div_nonneg (by linarith) (by linarith), (div_le_one (by linarith)).mpr (by linarith), ?_⟩
      field_simp; ring
  -- real coordinates
  set n1 : ℝ := (nℓ.1 : ℝ) with hn1
  set n2 : ℝ := (nℓ.2 : ℝ) with hn2
  set v1 : ℝ := (vl.1 : ℝ) with hv1
  set v2 : ℝ := (vl.2 : ℝ) with hv2
  have hperpR : n1 * v1 + n2 * v2 = 0 := by
    have := hperp; simp only [dot] at this; simp only [n1, n2, v1, v2]; exact_mod_cast this
  have hdotR : ∀ w : ℤ × ℤ, (dot nℓ w : ℝ) = n1 * w.1 + n2 * w.2 := by
    intro w; simp only [dot, n1, n2]; push_cast; ring
  rw [hdotR, hdotR, hdotR] at hlev
  -- `x := P - z`, `P := (1-λ)a + λc`
  set x1 : ℝ := (1 - lam) * a.1 + lam * c.1 - z.1 with hx1d
  set x2 : ℝ := (1 - lam) * a.2 + lam * c.2 - z.2 with hx2d
  have hx : n1 * x1 + n2 * x2 = 0 := by simp only [x1, x2]; linear_combination -hlev
  have hD : v1 * x2 - v2 * x1 = 0 := by
    have h1 : (v1 * x2 - v2 * x1) * n1 = 0 := by linear_combination x2 * hperpR - v2 * hx
    have h2 : (v1 * x2 - v2 * x1) * n2 = 0 := by linear_combination v1 * hx - x1 * hperpR
    rcases mul_eq_zero.mp h1 with h | h
    · exact h
    · rcases mul_eq_zero.mp h2 with h' | h'
      · exact h'
      · refine absurd (Prod.ext ?_ ?_ : nℓ = 0) hn
        · simp only [Prod.fst_zero]; rw [hn1] at h; exact_mod_cast h
        · simp only [Prod.snd_zero]; rw [hn2] at h'; exact_mod_cast h'
  have hv2pos : 0 < v1 ^ 2 + v2 ^ 2 := by
    by_contra hle
    push_neg at hle
    have e1 : v1 = 0 := by nlinarith [sq_nonneg v1, sq_nonneg v2]
    have e2 : v2 = 0 := by nlinarith [sq_nonneg v1, sq_nonneg v2]
    refine hvl (Prod.ext ?_ ?_)
    · simp only [Prod.fst_zero]; rw [hv1] at e1; exact_mod_cast e1
    · simp only [Prod.snd_zero]; rw [hv2] at e2; exact_mod_cast e2
  set r : ℝ := (x1 * v1 + x2 * v2) / (v1 ^ 2 + v2 ^ 2)
  have hr1 : x1 = r * v1 := by
    simp only [r]; field_simp; linear_combination (-v2) * hD
  have hr2 : x2 = r * v2 := by
    simp only [r]; field_simp; linear_combination v1 * hD
  -- the row index `j := ⌈r⌉` and the in-segment parameter `s`
  set κ : ℝ := (1 - lam) * μ + lam * ν
  have hμR : (1 : ℝ) ≤ μ := by exact_mod_cast hμ
  have hνR : (1 : ℝ) ≤ ν := by exact_mod_cast hν
  have hκ : 1 ≤ κ := by simp only [κ]; nlinarith
  set j : ℤ := ⌈r⌉
  have hj0 : 0 ≤ (j : ℝ) - r := by simp only [j]; linarith [Int.le_ceil r]
  have hj1 : (j : ℝ) - r < 1 := by simp only [j]; linarith [Int.ceil_lt_add_one r]
  set s : ℝ := ((j : ℝ) - r) / κ
  have hs0 : 0 ≤ s := div_nonneg hj0 (by linarith)
  have hs1 : s ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
  have hsκ : s * κ = (j : ℝ) - r := by simp only [s]; field_simp
  simp only [κ] at hsκ
  clear_value s j r x1 x2 κ n1 n2 v1 v2
  subst hv1 hv2
  refine ⟨j, ?_⟩
  -- the two edge points and their convex combination
  have hA1 : (1 - s) • toReal a + s • toReal (a + (μ : ℤ) • vl) ∈ C :=
    hconv ha ha' (by linarith) hs0 (by ring)
  have hA2 : (1 - s) • toReal c + s • toReal (c + (ν : ℤ) • vl) ∈ C :=
    hconv hc hc' (by linarith) hs0 (by ring)
  have hX := hconv hA1 hA2 (by linarith : (0 : ℝ) ≤ 1 - lam) hl0 (by ring)
  have heq : toReal (z + j • vl) = (1 - lam) • ((1 - s) • toReal a + s • toReal (a + (μ : ℤ) • vl))
      + lam • ((1 - s) • toReal c + s • toReal (c + (ν : ℤ) • vl)) := by
    simp only [toReal, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, Prod.fst_add, Prod.snd_add,
      Prod.smul_fst, Prod.smul_snd]
    push_cast
    refine Prod.ext ?_ ?_
    · show (z.1 : ℝ) + j * vl.1 = (1 - lam) * ((1 - s) * a.1 + s * (a.1 + μ * vl.1))
        + lam * ((1 - s) * c.1 + s * (c.1 + ν * vl.1))
      linear_combination hx1d - hr1 - (vl.1 : ℝ) * hsκ
    · show (z.2 : ℝ) + j * vl.2 = (1 - lam) * ((1 - s) * a.2 + s * (a.2 + μ * vl.2))
        + lam * ((1 - s) * c.2 + s * (c.2 + ν * vl.2))
      linear_combination hx2d - hr2 - (vl.2 : ℝ) * hsκ
  show toReal (z + j • vl) ∈ C
  rw [heq]; exact hX

/-- Two distinct points on one `nℓ`-level line give a pair `a, a + μ•vl` (`μ ≥ 1`) among them. -/
theorem exists_step_pair {T : Set (ℤ × ℤ)} {nℓ vl x y : ℤ × ℤ} (hn : nℓ ≠ 0) (hvl : Prim vl)
    (hperp : dot nℓ vl = 0) (hx : x ∈ T) (hy : y ∈ T) (hxy : x ≠ y)
    (hlev : dot nℓ x = dot nℓ y) :
    ∃ (a : ℤ × ℤ) (μ : ℕ), a ∈ T ∧ a + (μ : ℤ) • vl ∈ T ∧ 1 ≤ μ ∧ dot nℓ a = dot nℓ x := by
  have hd : dot nℓ (y - x) = 0 := by rw [dot_sub, hlev, sub_self]
  have hdet : det vl (y - x) = 0 := det_eq_zero_of_dot_eq_zero hn hperp hd
  obtain ⟨t, ht⟩ := exists_smul_of_det_eq_zero hvl hdet
  have hyx : y = x + t • vl := by
    have : y - x = t • vl := by rw [ht]; rfl
    rw [← this]; abel
  rcases lt_trichotomy t 0 with htn | ht0 | htp
  · refine ⟨y, (-t).toNat, hy, ?_, by omega, hlev.symm⟩
    rw [Int.toNat_of_nonneg (by omega), hyx]
    convert hx using 1; rw [add_assoc, ← add_smul]; simp
  · exfalso; apply hxy; rw [hyx, ht0, zero_smul, add_zero]
  · refine ⟨x, t.toNat, hx, ?_, by omega, rfl⟩
    rw [Int.toNat_of_nonneg (by omega), ← hyx]; exact hy

/-- **`shellSubStrip` for the push shell.**  If `T` is a lattice-convex region whose two faces
parallel to `vl` (normals `±nℓ`) are genuine edges, and the pushed face `nO` points forward
(`0 < dot nO vl`), then the push shell lies in the half-strip `T + ℕ•vl`. -/
theorem PushData.subset_halfStrip {S T : Set (ℤ × ℤ)} {nO m1 m2 p vJ : ℤ × ℤ} {k : ℕ} {L : ℤ}
    (D : PushData S T nO m1 m2 p vJ k L) (hlc : IsLatticeConvexRegion T) {nℓ vl : ℤ × ℤ}
    (hnℓ : nℓ ∈ E T) (hnℓ' : -nℓ ∈ E T) (hvl : Prim vl) (hperp : dot nℓ vl = 0)
    (hpos : 0 < dot nO vl) :
    pushShell T p vJ k ⊆ Colle35.halfStrip T vl := by
  intro z hz
  by_cases hzT : z ∈ T
  · exact ⟨z, hzT, 0, by simp⟩
  obtain ⟨hle, -⟩ := D.pushShell_le z hz
  have hn0 : nℓ ≠ 0 := hnℓ.1.ne_zero
  have hnO1 : nℓ ≠ nO := by rintro rfl; rw [hperp] at hpos; exact lt_irrefl 0 hpos
  have hnO2 : -nℓ ≠ nO := by
    rintro h; rw [← h, dot_neg_left, hperp] at hpos; simp at hpos
  -- `z` beats `T` in direction `nO` (otherwise it would already be in `T`)
  have hzO : suppVal T nO < dot nO z := by
    by_contra hc
    push_neg at hc
    exact hzT (mem_of_dot_le_suppVal D.hTfin D.hTne D.harea hlc (fun m hm => by
      by_cases hmO : m = nO
      · rw [hmO]; exact hc
      · exact hle m hm hmO))
  -- a step pair on the top face and on the bottom face
  obtain ⟨hpc, c1, hc1, c2, hc2, hc12⟩ := hnℓ
  obtain ⟨c, ν, hc, hc', hν, hclev⟩ := exists_step_pair hn0 hvl hperp hc1.1 hc2.1 hc12
    (by rw [← suppVal_eq hc1, ← suppVal_eq hc2])
  obtain ⟨hpa, a1, ha1, a2, ha2, ha12⟩ := hnℓ'
  have hperp' : dot (-nℓ) vl = 0 := by rw [dot_neg_left, hperp, neg_zero]
  obtain ⟨a, μ, ha, ha', hμ, halev⟩ := exists_step_pair (neg_ne_zero.mpr hn0) hvl hperp'
    ha1.1 ha2.1 ha12 (by rw [← suppVal_eq ha1, ← suppVal_eq ha2])
  have hlo : dot nℓ a ≤ dot nℓ z := by
    have h1 := hle (-nℓ) ⟨hpa, a1, ha1, a2, ha2, ha12⟩ hnO2
    rw [suppVal_eq ha1, ← halev] at h1
    rw [dot_neg_left, dot_neg_left] at h1; linarith
  have hhi : dot nℓ z ≤ dot nℓ c := by
    have h1 := hle nℓ ⟨hpc, c1, hc1, c2, hc2, hc12⟩ hnO1
    rw [hclev, ← suppVal_eq hc1]; exact h1
  obtain ⟨j, hj⟩ := row_nonempty hlc hμ hν hn0
    hvl.ne_zero hperp ha ha' hc hc' hlo hhi
  -- the row point sits behind `z`
  have hjneg : j < 0 := by
    by_contra hj0
    push_neg at hj0
    have h1 := le_suppVal D.hTfin D.hTne (n := nO) hj
    have e : dot nO (z + j • vl) = dot nO z + j * dot nO vl := dot_row nO z vl j
    rw [e] at h1
    nlinarith
  refine ⟨z + j • vl, hj, (-j).toNat, ?_⟩
  rw [Int.toNat_of_nonneg (by omega), add_assoc, ← add_smul]; simp

/-! ## §5. Non-vacuity: `PushData` is satisfiable (`T = box (0,0) (3,1)`, push the right face) -/

namespace Bench

def T0 : Set (ℤ × ℤ) := box (0, 0) (3, 1)

theorem sv {n v : ℤ × ℤ} (hv : v ∈ T0) (hb : ∀ y ∈ T0, dot n y ≤ dot n v) :
    suppVal T0 n = dot n v := suppVal_eq ⟨hv, hb⟩

theorem sv_r : suppVal T0 (1, 0) = 3 :=
  sv (v := (3, 0)) (by simp [T0, box]) (by intro y hy; simp only [T0, box, Set.mem_setOf_eq] at hy; simp [dot]; omega)
theorem sv_b : suppVal T0 (0, -1) = 0 :=
  sv (v := (0, 0)) (by simp [T0, box]) (by intro y hy; simp only [T0, box, Set.mem_setOf_eq] at hy; simp [dot]; omega)
theorem sv_t : suppVal T0 (0, 1) = 1 :=
  sv (v := (0, 1)) (by simp [T0, box]) (by intro y hy; simp only [T0, box, Set.mem_setOf_eq] at hy; simp [dot]; omega)
theorem sv_l : suppVal T0 (-1, 0) = 0 :=
  sv (v := (0, 0)) (by simp [T0, box]) (by intro y hy; simp only [T0, box, Set.mem_setOf_eq] at hy; simp [dot]; omega)

theorem E_T0 : E T0 = {(1, 0), (-1, 0), (0, 1), (0, -1)} := E_box (by norm_num) (by norm_num)

theorem pushData_bench :
    PushData sq1 T0 (1, 0) (0, -1) (0, 1) (4, 0) (0, 1) 1 1 := by
  refine
    { hTfin := finite_box _ _
      hTne := ⟨(0, 0), by simp [T0, box]⟩
      harea := ⟨(0, 0), by simp [T0, box], (1, 0), by simp [T0, box], (0, 1), by simp [T0, box],
        by decide⟩
      hT := envOf_sq1_box (by norm_num) (by norm_num)
      hnO := by rw [E_T0]; simp
      hm1 := by rw [E_T0]; simp
      hm2 := by rw [E_T0]; simp
      h12 := by decide
      h1O := by decide
      h2O := by decide
      hvJ := by decide
      hvJO := by simp [dot]
      hL := by norm_num
      hlev := by rw [sv_r]; simp [dot]
      hp1 := by rw [sv_b]; simp [dot]
      hp2 := by rw [sv_t]; simp [dot]
      hs1 := ?_
      hs2 := ?_
      hadj := ?_
      hk := le_rfl
      hlen := ?_ }
  · intro m hm h1 h2
    rw [E_T0] at hm
    rcases hm with rfl | rfl | rfl | rfl
    · exact absurd rfl h2
    · rw [sv_l]; simp [dot]
    · rw [sv_t]; simp [dot]
    · exact absurd rfl h1
  · intro m hm h1 h2
    rw [E_T0] at hm
    rcases hm with rfl | rfl | rfl | rfl
    · exact absurd rfl h2
    · rw [sv_l]; simp [dot]
    · exact absurd rfl h1
    · rw [sv_b]; simp [dot]
  · intro m hm h1 h2 h3 v hv hv'
    rw [E_T0] at hm
    rcases hm with rfl | rfl | rfl | rfl
    · exact h1 rfl
    · have a1 := hv.2 (3, 0) (by simp [T0, box])
      have a2 := hv'.2 (0, 0) (by simp [T0, box])
      simp [dot] at a1 a2; omega
    · exact h3 rfl
    · exact h2 rfl
  · rw [encard_face_sq1_right]; norm_num

/-- The bench push shell really is `E(sq1)`-enveloped and strictly bigger than `T0`. -/
theorem bench_ok : Enveloped sq1 (pushShell T0 (4, 0) (0, 1) 1) ∧
    ¬ pushShell T0 (4, 0) (0, 1) 1 ⊆ T0 :=
  ⟨pushData_bench.enveloped, pushData_bench.not_pushShell_subset⟩

end Bench

end Nivat.Hole1QShell

/-! ## §8. `ChainDataGeom.ofShell`: `ofPartsInter` with the shell family left free

`ChainDataGeom.ofPartsInter` (`ChainAssembleInter.lean`) hard-wires
`shell i ε := shellInter (hatOf i) (MaxEnv.shell …) w`.  Every other field of the bundle is
shell-blind, so the constructor below copies `ofPartsInter` verbatim except that the shell
family `sh` and its seven obligations are parameters.  The `ChainData` shell fields are then
discharged **by whatever `sh` the caller chooses** — here, eventually, the push shell. -/

namespace Nivat.Colle35

open Nivat Nivat.LE2 Nivat.MaxEnv Nivat.ChainAsm

variable {α : Type*}

noncomputable def ChainDataGeom.ofShell
    (η xper : Config α) (vl p : ℤ × ℤ) (S : Finset (ℤ × ℤ)) (gen : ℤ × ℤ)
    (Env : Set (ℤ × ℤ) → Prop) (B A : ℕ → Set (ℤ × ℤ)) (u : ℕ → ℤ × ℤ) (kk : ℕ → ℕ)
    (envShift : ∀ (v : ℤ × ℤ) (T : Set (ℤ × ℤ)), Env T → Env {z | z + v ∈ T})
    (envB : ∀ i, Env (B i))
    (maxA : ∀ i, IsMaxEnvIn Env (canonA η xper vl B u i) (A i))
    (subBA : ∀ i, B i ⊆ A i) (subAB : ∀ i, A i ⊆ B (i + 1))
    (AhatMono : ∀ i j, i ≤ j → hatOf A kk vl i ⊆ hatOf A kk vl j)
    (vJ1 nJ : ℤ × ℤ) (cJ : ℤ)
    (hhp : ∀ i, hatOf A kk vl i ⊆ halfPlaneGE nJ cJ)
    (hswept : SweptClosed (⋃ i, hatOf A kk vl i) vJ1 nJ cJ)
    (ahat_nonempty : (⋃ i, hatOf A kk vl i).Nonempty)
    -- the free shell family and its obligations
    (sh : ℕ → ℕ → Set (ℤ × ℤ))
    (shellFinite : ∀ i ε, (sh i ε).Finite)
    (subShell : ∀ i ε, hatOf A kk vl i ⊆ sh i ε)
    (shellSubInf : ∀ i ε, sh i ε ⊆ MaxEnv.shell (⋃ i, hatOf A kk vl i) vJ1 nJ cJ ε)
    (I₀ : ℕ)
    (shellSubStrip : ∀ ε i₀ : ℕ, 0 < ε → (∀ i, i₀ ≤ i → Env (sh i ε)) →
      ∀ i, max i₀ I₀ ≤ i → sh i ε ⊆ {z | z + (kk i : ℤ) • vl ∈ Colle35.halfStrip (B i) vl})
    (shellProper : ∀ ε i₀ : ℕ, 0 < ε → (∀ i, i₀ ≤ i → Env (sh i ε)) →
      ∀ i, max i₀ I₀ ≤ i → ¬ (sh i ε ⊆ hatOf A kk vl i))
    (shellEnv : ∃ ε i₀, 0 < ε ∧ ∀ i, i₀ ≤ i → Env (sh i ε))
    (fillCover : ∀ ε i₀ : ℕ, 0 < ε → (∀ i, i₀ ≤ i → Env (sh i ε)) →
      ∀ i, max i₀ I₀ ≤ i →
      sh i ε ⊆ {z | Colle37.GenClosure S (hatOf A kk vl i ∪ sh i₀ ε) z})
    (vJ : ℤ × ℤ) (F : FaceBlock S nJ vJ)
    (gen_eq : gen = F.a')
    (vJ_prim : Primitive vJ) (nJ_prim : Primitive nJ)
    (bottom : ∀ ε : ℕ, ∃ (z₀ : ℤ × ℤ) (L : ℤ),
      dot nJ z₀ = cJ - (ε : ℤ) - 1 ∧
      (∀ k : ℤ, L ≤ k → z₀ + k • vJ ∈ reachSet (⋃ i, hatOf A kk vl i) vJ1) ∧
      (∀ b ∈ S, ∀ k : ℤ, L ≤ k →
        z₀ + k • vJ + (b - F.a) ∈ reachSet (⋃ i, hatOf A kk vl i) vJ1) ∧
      (∀ z ∈ MaxEnv.shell (⋃ i, hatOf A kk vl i) vJ1 nJ cJ (ε + 1),
        z ∈ MaxEnv.shell (⋃ i, hatOf A kk vl i) vJ1 nJ cJ ε ∨
          ∃ k : ℤ, L ≤ k ∧ z = z₀ + k • vJ))
    (rec_p : ∀ g ∈ ⋃ i, hatOf A kk vl i, g + p ∈ ⋃ i, hatOf A kk vl i)
    (dot_nJ_p : dot nJ p ≠ 0)
    (rec_vJ : ∀ g ∈ ⋃ i, hatOf A kk vl i, g + vJ ∈ ⋃ i, hatOf A kk vl i)
    (cL : ℤ)
    (ahat_halfPlane_L : ∀ g ∈ ⋃ i, hatOf A kk vl i, cL ≤ dot (det p vJ • (-p.2, p.1)) g)
    (ahat_attained_L : ∃ g ∈ ⋃ i, hatOf A kk vl i, dot (det p vJ • (-p.2, p.1)) g = cL)
    (nfp_L : ¬ ∃ h h' : ℤ × ℤ, det h h' ≠ 0 ∧
      PeriodicOnWith xper {z | cL ≤ dot (det p vJ • (-p.2, p.1)) z} h ∧
      PeriodicOnWith xper {z | cL ≤ dot (det p vJ • (-p.2, p.1)) z} h') :
    ChainDataGeom η xper vl p S gen where
  Env := Env
  B := B
  A := A
  u := u
  kk := kk
  Ahat := hatOf A kk vl
  shell := sh
  shellInf := fun ε => MaxEnv.shell (⋃ i, hatOf A kk vl i) vJ1 nJ cJ ε
  fill := fun i i₀ ε => genFill S gen (hatOf A kk vl i ∪ sh i₀ ε)
  envB := envB
  envA := envA_of_max maxA
  subBA := subBA
  subAB := subAB
  subStrip := subStrip_of_max maxA
  agreeA := agreeA_of_max maxA
  AhatEq := fun i => hatOf_eq i
  AhatMono := AhatMono
  maximalHat := maximalHat_of_max envShift maxA
  shellFinite := shellFinite
  subShell := subShell
  shellSubInf := shellSubInf
  shellInfZero := shellInfZero_of (Set.iUnion_subset hhp) hswept
  I₀ := I₀
  shellSubStrip := shellSubStrip
  shellProper := shellProper
  shellEnv := shellEnv
  fillZero := fun i i₀ ε => subset_rfl
  fillStep := by
    subst gen_eq
    exact fun i i₀ ε m z hz => genFill_step S F.a' _ m z hz
  fillCover := fillCover
  vJ1 := vJ1
  nJ := nJ
  cJ := cJ
  shellInf_eq := fun _ => rfl
  ahat_nonempty := ahat_nonempty
  ahat_halfPlane := fun g hg => Set.iUnion_subset hhp hg
  vJ := vJ
  a := F.a
  a' := F.a'
  r := F.r
  latticeConvex_S := F.latticeConvex_S
  a_mem := F.a_mem
  a'_mem := F.a'_mem
  lex := F.lex
  lex' := F.lex'
  edge := F.edge
  edge' := F.edge'
  dot_nJ_vJ := F.dot_nJ_vJ
  bottom := bottom
  rec_p := rec_p
  dot_nJ_p := dot_nJ_p
  vJ_ne := vJ_prim.ne_zero
  vJ_prim := vJ_prim
  rec_vJ := rec_vJ
  cL := cL
  ahat_halfPlane_L := ahat_halfPlane_L
  ahat_attained_L := ahat_attained_L
  nJ_prim := nJ_prim
  nfp_L := nfp_L

end Nivat.Colle35

/-! ## §9. The reduction of `exists_chainData` through `ofShell`

Same shape as `tmp/wip/hole1-geomcore.lean` `exists_chainData_of_geomCore`, but the residual
`GeomCoreShell` carries **no** `w` / `hsweepW` / `escapeW`: the shell family is the caller's. -/

namespace Nivat.Hole1QShell

open Nivat Nivat.LE2 Nivat.MaxEnv Nivat.Colle35 Nivat.ChainAsm

/-- The geometric residual with a free shell family. -/
structure GeomCoreShell (xper : Config ℤ) (vl p : ℤ × ℤ) (S : Finset (ℤ × ℤ))
    (B A : ℕ → Set (ℤ × ℤ)) (kk : ℕ → ℕ) where
  vJ1 : ℤ × ℤ
  nJ : ℤ × ℤ
  cJ : ℤ
  hsweep : dot nJ vJ1 < 0
  hhp : ∀ i, hatOf A kk vl i ⊆ halfPlaneGE nJ cJ
  hswept : MaxEnv.SweptClosed (⋃ i, hatOf A kk vl i) vJ1 nJ cJ
  vJ : ℤ × ℤ
  F : Colle35.FaceBlock S nJ vJ
  vJ_prim : Primitive vJ
  nJ_prim : Primitive nJ
  bottom : ∀ ε : ℕ, ∃ (z₀ : ℤ × ℤ) (L : ℤ),
    dot nJ z₀ = cJ - (ε : ℤ) - 1 ∧
    (∀ k : ℤ, L ≤ k → z₀ + k • vJ ∈ MaxEnv.reachSet (⋃ i, hatOf A kk vl i) vJ1) ∧
    (∀ b ∈ S, ∀ k : ℤ, L ≤ k →
      z₀ + k • vJ + (b - F.a) ∈ MaxEnv.reachSet (⋃ i, hatOf A kk vl i) vJ1) ∧
    (∀ z ∈ MaxEnv.shell (⋃ i, hatOf A kk vl i) vJ1 nJ cJ (ε + 1),
      z ∈ MaxEnv.shell (⋃ i, hatOf A kk vl i) vJ1 nJ cJ ε ∨ ∃ k : ℤ, L ≤ k ∧ z = z₀ + k • vJ)
  dot_nJ_p : dot nJ p ≠ 0
  sh : ℕ → ℕ → Set (ℤ × ℤ)
  shellFinite : ∀ i ε, (sh i ε).Finite
  subShell : ∀ i ε, hatOf A kk vl i ⊆ sh i ε
  shellSubInf : ∀ i ε, sh i ε ⊆ MaxEnv.shell (⋃ i, hatOf A kk vl i) vJ1 nJ cJ ε
  I₀ : ℕ
  shellSubStrip : ∀ ε i₀ : ℕ, 0 < ε → (∀ i, i₀ ≤ i → EnvOf (↑S : Set (ℤ × ℤ)) (sh i ε)) →
    ∀ i, max i₀ I₀ ≤ i → sh i ε ⊆ {z | z + (kk i : ℤ) • vl ∈ Colle35.halfStrip (B i) vl}
  shellProper : ∀ ε i₀ : ℕ, 0 < ε → (∀ i, i₀ ≤ i → EnvOf (↑S : Set (ℤ × ℤ)) (sh i ε)) →
    ∀ i, max i₀ I₀ ≤ i → ¬ (sh i ε ⊆ hatOf A kk vl i)
  shellEnv : ∃ ε i₀, 0 < ε ∧ ∀ i, i₀ ≤ i → EnvOf (↑S : Set (ℤ × ℤ)) (sh i ε)
  fillCover : ∀ ε i₀ : ℕ, 0 < ε → (∀ i, i₀ ≤ i → EnvOf (↑S : Set (ℤ × ℤ)) (sh i ε)) →
    ∀ i, max i₀ I₀ ≤ i →
    sh i ε ⊆ {z | Colle37.GenClosure S (hatOf A kk vl i ∪ sh i₀ ε) z}

/-- **`GeomCoreShell` ＋ item-(ii) chain ⟹ `ChainDataGeom`** (through `ofShell`). -/
noncomputable def geom_of_geomCoreShell {ξ xper : Config ℤ} {S : Finset (ℤ × ℤ)}
    {vl nℓ p : ℤ × ℤ} {cz : ℤ}
    (rd : Nivat.ItemIIRecursion.ItemIIRecursionData ξ xper S vl nℓ cz)
    (hvl : vl ≠ 0) (hprim : Primitive nℓ) (hperp : dot nℓ vl = 0)
    (hdet : det p vl = 0) (hp_neg : ∃ c : ℕ, 0 < c ∧ p = -(c : ℤ) • vl)
    (hnotDP : ¬ ∃ h h' : ℤ × ℤ, det h h' ≠ 0 ∧
      PeriodicOnWith xper {z | cz ≤ dot nℓ z} h ∧ PeriodicOnWith xper {z | cz ≤ dot nℓ z} h')
    {σ : ℕ → ℕ} (hσ : StrictMono σ)
    (G : GeomCoreShell xper vl p S (fun n => rd.B (σ n)) (fun n => rd.A (σ n))
      (fun n => rd.kk (σ n))) :
    ChainDataGeom ξ xper vl p S G.F.a' :=
  let B : ℕ → Set (ℤ × ℤ) := fun n => rd.B (σ n)
  let A : ℕ → Set (ℤ × ℤ) := fun n => rd.A (σ n)
  let u : ℕ → ℤ × ℤ := fun n => rd.u (σ n)
  let kk : ℕ → ℕ := fun n => rd.kk (σ n)
  let maxA : ∀ i, IsMaxEnvIn (EnvOf (↑S : Set (ℤ × ℤ))) (canonA ξ xper vl B u i) (A i) :=
    fun i => rd.maxA (σ i)
  let subAB : ∀ i, A i ⊆ B (i + 1) :=
    fun i => Nivat.LeafAItemII.subAB_comp (B := rd.B) (A := rd.A) (σ := σ) hσ rd.subBA
      rd.subAB i
  let AhatMono : ∀ i j, i ≤ j → hatOf A kk vl i ⊆ hatOf A kk vl j :=
    fun i j hij => rd.AhatMono (σ i) (σ j) (hσ.monotone hij)
  let hfin : ∀ i, (hatOf A kk vl i).Finite :=
    hatOf_finite kk vl (fun i => (rd.finB (σ (i + 1))).subset (subAB i))
  let hII : ItemII B nℓ cz :=
    Nivat.LeafAItemII.itemII_comp hσ
      (Nivat.LeafAItemII.B_mono_of_subBA_subAB rd.subBA rd.subAB) rd.itemII
  let hexh : Exhausts A nℓ cz :=
    Nivat.LeafAItemII.exhausts_comp hσ (Nivat.ChainKK.A_mono rd.subBA rd.subAB) rd.exhausts
  let halign : ∀ i, IsGreatest
      {t : ℤ | rd.g₁ + t • vl ∈ hatOf A kk vl i ∧ dot nℓ (rd.g₁ + t • vl) = cz} 0 :=
    fun i => rd.halign (σ i)
  let hne : (⋃ i, hatOf A kk vl i).Nonempty :=
    ⟨rd.g₁, Set.mem_iUnion.mpr ⟨0, by simpa using (halign 0).1.1⟩⟩
  let hrecp : ∀ g ∈ ⋃ i, hatOf A kk vl i, g + p ∈ ⋃ i, hatOf A kk vl i :=
    Nivat.LaneLeafAGenRecP.rec_p_free_smul ξ xper vl S hp_neg.choose hp_neg.choose_spec.2
      hperp maxA (fun i => rd.subBA (σ i)) subAB (fun i => rd.hfin (σ i)) hII rd.hg₁ halign
      AhatMono
  let rec_vJ : ∀ g ∈ ⋃ i, hatOf A kk vl i, g + G.vJ ∈ ⋃ i, hatOf A kk vl i :=
    rec_vJ_of_bottom
      (latticeConvex_iUnion_hatOf ξ xper vl S (EnvOf (↑S : Set (ℤ × ℤ))) B A u kk rfl
        maxA hfin AhatMono)
      G.hsweep (fun _ hg => Set.iUnion_subset G.hhp hg) G.hswept G.F.dot_nJ_vJ G.bottom
  let hpvJ : det p G.vJ ≠ 0 :=
    Nivat.ColleReg.det_ne_zero_of_dot G.vJ_prim.ne_zero G.F.dot_nJ_vJ G.dot_nJ_p
  let side := ell_side_of_exhausts (xper := xper) (Ahat := hatOf A kk vl) hvl hdet hpvJ hprim
    hperp (fun i => hatOf_eq i) hexh rec_vJ hnotDP
  ChainDataGeom.ofShell ξ xper vl p S G.F.a' (EnvOf (↑S : Set (ℤ × ℤ))) B A u kk
    (fun v Tset hT => Colle35.envOf_shift_mem _ v Tset hT)
    (fun i => rd.envB (σ i)) maxA (fun i => rd.subBA (σ i)) subAB AhatMono
    G.vJ1 G.nJ G.cJ G.hhp G.hswept hne
    G.sh G.shellFinite G.subShell G.shellSubInf G.I₀ G.shellSubStrip G.shellProper G.shellEnv
    G.fillCover G.vJ G.F rfl G.vJ_prim G.nJ_prim G.bottom hrecp G.dot_nJ_p rec_vJ
    side.choose_spec.choose
    side.choose_spec.choose_spec.2.2.2.1
    side.choose_spec.choose_spec.2.2.2.2.1
    side.choose_spec.choose_spec.2.2.2.2.2

end Nivat.Hole1QShell

namespace Nivat.ColleReg

open Nivat Nivat.Colle35

variable {ξ xper ϑ : Config ℤ} {vl p ℓ : ℤ × ℤ} {S : Finset (ℤ × ℤ)} {gen : ℤ × ℤ}

/-- **`exists_chainData` ⟸ its own binders ＋ `hgeomShell`** (binder list copied from
`RegionSteps.lean` `exists_chainData`, one extra hypothesis at the end). -/
theorem exists_chainData_of_geomCoreShell (hξ : IsMinimalCounterexample ξ) (d : DecompDataZ ξ)
    {w : ℝ × ℝ} (hw : w ≠ 0) (hw₁ : w ∈ ONED ξ) (hw₂ : -w ∈ ONED ξ)
    (hℓ_nel : ℓ ∈ Colle45.NonExpansiveLine ξ)
    (hℓ_pos : Colle45.IsOneSidedNonexpansive ξ ℓ)
    (hℓ_neg : Colle45.IsOneSidedNonexpansive ξ (-ℓ))
    (hxper : xper ∈ orbitClosure ξ)
    (hp_mem : p ∈ Per xper) (hp_ne : p ≠ 0) (hvl_ne : vl ≠ 0) (hvl_prim : Primitive vl)
    (hdet_vl : det p vl = 0) (hdet_ℓ : Nivat.LE2.dot ℓ vl = 0)
    (hp_neg : ∃ c : ℕ, 0 < c ∧ p = -(c : ℤ) • vl)
    (hpartner : ∃ (yper : Config ℤ) (nℓ : ℤ × ℤ) (cz : ℤ) (g : ℤ × ℤ),
      yper ∈ orbitClosure ξ ∧ xper ≠ yper ∧
      nℓ ≠ 0 ∧ Primitive nℓ ∧ Nivat.LE2.dot nℓ vl = 0 ∧ 0 < det nℓ vl ∧
      (∀ z : ℤ × ℤ, cz < Nivat.LE2.dot nℓ z → xper z = yper z) ∧
      Nivat.LE2.dot nℓ g = cz ∧ xper g ≠ yper g ∧
      ¬ ∃ h h' : ℤ × ℤ, det h h' ≠ 0 ∧
        PeriodicOnWith xper {z | cz ≤ Nivat.LE2.dot nℓ z} h ∧
        PeriodicOnWith xper {z | cz ≤ Nivat.LE2.dot nℓ z} h')
    (hcase2 : Case2 ξ xper d.Sphi vl)
    (hgeomShell : ∀ (nℓ : ℤ × ℤ) (cz : ℤ),
      nℓ ≠ 0 → Primitive nℓ → Nivat.LE2.dot nℓ vl = 0 →
      ∀ rd : Nivat.ItemIIRecursion.ItemIIRecursionData ξ xper d.Sphi vl nℓ cz,
      ∃ σ : ℕ → ℕ, StrictMono σ ∧
        Nonempty (Nivat.Hole1QShell.GeomCoreShell xper vl p d.Sphi
          (fun n => rd.B (σ n)) (fun n => rd.A (σ n)) (fun n => rd.kk (σ n)))) :
    ∃ (genφ : ℤ × ℤ) (cg : ChainDataGeom ξ xper vl p d.Sphi genφ),
      Nivat.Colle.GeneratesAt ξ d.Sphi genφ ∧
      cg.toChainData.Env = Nivat.LE2.EnvOf (d.Sphi : Set (ℤ × ℤ)) := by
  obtain ⟨yper, nℓ, cz, g, hyper, hxy, hnℓ_ne, hnℓ_prim, hperp, hdetpos, hagree, hgz, hgxy,
    hnotDP⟩ := hpartner
  obtain ⟨rd⟩ :=
    Nivat.ItemIIFeed.nonempty_itemIIRecursionData_of_chainData_binders d cz hxper hvl_ne
      hvl_prim hℓ_nel hℓ_pos hℓ_neg hdet_ℓ hnℓ_prim hperp hcase2
  obtain ⟨σ, hσ, ⟨G⟩⟩ := hgeomShell nℓ cz hnℓ_ne hnℓ_prim hperp rd
  exact ⟨G.F.a', Nivat.Hole1QShell.geom_of_geomCoreShell rd hvl_ne hnℓ_prim hperp hdet_vl
    hp_neg hnotDP hσ G, Nivat.Colle35.FaceBlock.generatesAt_a' G.F d.isGeneratingSet, rfl⟩

end Nivat.ColleReg

/-! ## §10. `PushData` from fan-adjacent face geometry

For a lattice polygon `T` whose pushed face `J` has fan-adjacent neighbours `prev` (before)
and `next` (after), the push data are explicit:
`p := faceStart T J + D₂ • dir prev`, `q := faceEnd T J - D₁ • dir next`,
`D₁ := det prev J`, `D₂ := det J next`, `L := D₁ * D₂`, `vJ := dir J`.
Everything needed is local; "the `J`-face is long" enters only through `hbig1`/`hbig2`/`hk`/
`hlenS`, which hold for all large `i` on a chain whose `J`-face grows without bound. -/

namespace Nivat.Hole1QShell

open Nivat Nivat.LE2 Nivat.PolyChain

theorem dot_dir_eq_det (m ν : ℤ × ℤ) : dot m (dir ν) = det ν m := by
  simp only [dot, dir, det]; ring

/-- Two primitive vectors with vanishing determinant are equal or opposite (`det a b = 0`
form, argument order as used below). -/
theorem eq_or_neg_of_det_zero {a b : ℤ × ℤ} (ha : Prim a) (hb : Prim b) (h : det a b = 0) :
    b = a ∨ b = -a := eq_or_neg_of_prim_of_det_eq_zero ha hb h

theorem det_neg_right' (a b : ℤ × ℤ) : det a (-b) = -det a b := by
  simp only [det, Prod.fst_neg, Prod.snd_neg]; ring

theorem det_neg_left' (a b : ℤ × ℤ) : det (-a) b = -det a b := by
  simp only [det, Prod.fst_neg, Prod.snd_neg]; ring

theorem det_swap (a b : ℤ × ℤ) : det a b = -det b a := by simp only [det]; ring

/-- A point of the `J`-face that is also tight for an edge `m` forces `m ∈ {prev, J, next}`. -/
theorem hadj_of_fan {T : Set (ℤ × ℤ)} (hfin : T.Finite) (hlc : IsLatticeConvexRegion T)
    (harea : PosArea T) {J prev next : ℤ × ℤ} (hJ : J ∈ E T) (hprev : prev ∈ E T)
    (hnext : next ∈ E T) (hdp : 0 < det prev J) (hdn : 0 < det J next)
    (hadjP : ∀ μ ∈ E T, ¬(0 < det prev μ ∧ 0 < det μ J))
    (hadjN : ∀ μ ∈ E T, ¬(0 < det J μ ∧ 0 < det μ next)) :
    ∀ m ∈ E T, m ≠ J → m ≠ prev → m ≠ next → ∀ v ∈ face T J, v ∉ face T m := by
  intro m hm hmJ hmP hmN v hvJ hvm
  have hs0 : faceStart T J ∈ face T prev := by
    rw [← adjacent_shared_vertex hfin hlc hprev hJ hdp hadjP]; exact faceEnd_mem hlc hfin hprev
  have he0 : faceStart T J + (faceLen T J : ℤ) • dir J ∈ face T next := by
    rw [adjacent_shared_vertex hfin hlc hJ hnext hdn hadjN]
    have h0 : faceStart T next = faceStart T next + ((0 : ℕ) : ℤ) • dir next := by simp
    rw [h0, face_eq_segment hlc hfin hnext]; exact ⟨0, Nat.zero_le _, rfl⟩
  have hseg := face_eq_segment hlc hfin hJ
  have hlen1 := one_le_faceLen hfin hJ
  have hsegmem : ∀ t : ℕ, t ≤ faceLen T J → faceStart T J + (t : ℤ) • dir J ∈ T :=
    fun t ht => face_subset T J (by rw [hseg]; exact ⟨t, ht, rfl⟩)
  rw [hseg] at hvJ
  obtain ⟨t, ht, rfl⟩ := hvJ
  have hexp : ∀ s : ℤ, dot m (faceStart T J + s • dir J) =
      dot m (faceStart T J) + s * det J m := by
    intro s; rw [dot_row, dot_dir_eq_det]
  have hmax := hvm.2
  -- `m` must be orthogonal-or-cone-trapped
  rcases Nat.eq_zero_or_pos t with ht0 | htpos
  · -- `v = faceStart T J`, shared with `prev`
    subst ht0
    simp only [Nat.cast_zero, zero_smul, add_zero] at hmax
    have h1 := hmax _ (hsegmem 1 hlen1)
    rw [hexp] at h1
    push_cast at h1
    -- the previous point on the `prev` face
    have hprevpt : faceStart T J - dir prev ∈ T := by
      have hlp := one_le_faceLen hfin hprev
      have := face_subset T prev (by
        rw [face_eq_segment hlc hfin hprev]
        exact ⟨faceLen T prev - 1, Nat.sub_le _ _, rfl⟩ :
          faceStart T prev + ((faceLen T prev - 1 : ℕ) : ℤ) • dir prev ∈ face T prev)
      convert this using 1
      rw [← adjacent_shared_vertex hfin hlc hprev hJ hdp hadjP]
      push_cast [hlp]; rw [sub_smul, one_smul]; abel
    have h2 := hmax _ hprevpt
    rw [dot_sub, dot_dir_eq_det] at h2
    have c1 : det J m ≤ 0 := by linarith
    have c2 : 0 ≤ det prev m := by linarith
    rcases eq_or_lt_of_le c2 with e | e
    · rcases eq_or_neg_of_det_zero hprev.1 hm.1 e.symm with h | h
      · exact hmP h
      · rw [h, det_swap, det_neg_left'] at c1; linarith
    · rcases eq_or_lt_of_le c1 with e' | e'
      · rcases eq_or_neg_of_det_zero hJ.1 hm.1 e' with h | h
        · exact hmJ h
        · rw [h, det_neg_right'] at e; linarith
      · exact hadjP m hm ⟨e, by rw [det_swap]; linarith⟩
  · rcases eq_or_lt_of_le ht with htl | htl
    · -- `v = faceEnd T J`, shared with `next`
      subst htl
      have hlm1 : faceLen T J - 1 ≤ faceLen T J := Nat.sub_le _ _
      have h1 := hmax _ (hsegmem _ hlm1)
      rw [hexp, hexp] at h1
      have hc : ((faceLen T J - 1 : ℕ) : ℤ) = (faceLen T J : ℤ) - 1 := by push_cast [hlen1]; ring
      rw [hc] at h1
      have c1 : 0 ≤ det J m := by nlinarith
      -- the next point on the `next` face
      have hnextpt : faceStart T J + (faceLen T J : ℤ) • dir J + dir next ∈ T := by
        have hln := one_le_faceLen hfin hnext
        rw [adjacent_shared_vertex hfin hlc hJ hnext hdn hadjN]
        exact face_subset T next (by
          rw [face_eq_segment hlc hfin hnext]; exact ⟨1, hln, by simp⟩)
      have h2 := hmax _ hnextpt
      rw [dot_add, dot_dir_eq_det] at h2
      have c2 : det next m ≤ 0 := by linarith
      rcases eq_or_lt_of_le c1 with e | e
      · rcases eq_or_neg_of_det_zero hJ.1 hm.1 e.symm with h | h
        · exact hmJ h
        · rw [h, det_neg_right', det_swap] at c2; linarith
      · rcases eq_or_lt_of_le c2 with e' | e'
        · rcases eq_or_neg_of_det_zero hnext.1 hm.1 e' with h | h
          · exact hmN h
          · rw [h, det_neg_right'] at e; linarith
        · exact hadjN m hm ⟨e, by rw [det_swap]; linarith⟩
    · -- interior point: `m ⊥ dir J`, so `m = ±J`
      have h1 := hmax _ (hsegmem 0 (Nat.zero_le _))
      have h2 := hmax _ (hsegmem (t + 1) htl)
      rw [hexp, hexp] at h2
      simp only [Nat.cast_zero, zero_smul, add_zero] at h1
      rw [hexp] at h1
      push_cast at h2
      have htz : (0 : ℤ) < t := by exact_mod_cast htpos
      have hd0 : det J m = 0 := by nlinarith
      rcases eq_or_neg_of_det_zero hJ.1 hm.1 hd0 with h | h
      · exact hmJ h
      · -- `m = -J`: then `J` is constant on `T`, contradicting positive area
        apply not_posArea_of_dot_const hJ.1.ne_zero _ harea
        intro y hy z hz
        have hy1 := (face_subset T J (by rw [hseg]; exact ⟨t, ht, rfl⟩) :
          faceStart T J + (t : ℤ) • dir J ∈ T)
        have hJmax : ∀ x ∈ T, dot J x ≤ dot J (faceStart T J + (t : ℤ) • dir J) := by
          have : faceStart T J + (t : ℤ) • dir J ∈ face T J := by rw [hseg]; exact ⟨t, ht, rfl⟩
          exact this.2
        have hJmin : ∀ x ∈ T, dot J (faceStart T J + (t : ℤ) • dir J) ≤ dot J x := by
          intro x hx
          have := hmax x hx
          rw [h, dot_neg_left, dot_neg_left] at this; linarith
        have a1 := hJmax y hy; have a2 := hJmin y hy
        have b1 := hJmax z hz; have b2 := hJmin z hz
        linarith

end Nivat.Hole1QShell

namespace Nivat.Hole1QShell

open Nivat Nivat.LE2 Nivat.PolyChain

theorem dot_smul_r (m v : ℤ × ℤ) (c : ℤ) : dot m (c • v) = c * dot m v := by
  simp only [dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

/-- **`PushData` from fan-adjacent face geometry.**
`p := faceStart T J + D₂ • dir prev`, `vJ := dir J`, `L := D₁ * D₂`, `k := len - c` where
`D₁ • dir next + D₂ • dir prev = c • dir J` (a fixed integer relation of the fan).
The four "long face" hypotheses `hk`, `hlenS`, `hbig1`, `hbig2` are the only size inputs. -/
theorem pushData_of_fan {S T : Set (ℤ × ℤ)} (hTfin : T.Finite) (hTne : T.Nonempty)
    (harea : PosArea T) (hlc : IsLatticeConvexRegion T) (hT : Enveloped S T)
    {J prev next : ℤ × ℤ} (hJ : J ∈ E T) (hprev : prev ∈ E T) (hnext : next ∈ E T)
    (hdp : 0 < det prev J) (hdn : 0 < det J next)
    (hadjP : ∀ μ ∈ E T, ¬(0 < det prev μ ∧ 0 < det μ J))
    (hadjN : ∀ μ ∈ E T, ¬(0 < det J μ ∧ 0 < det μ next))
    {c : ℤ} (hc : det prev J • dir next + det J next • dir prev = c • dir J)
    (hk : c + 1 ≤ (faceLen T J : ℤ))
    (hlenS : (face S J).encard ≤ (((faceLen T J : ℤ) - c).toNat : ℕ∞) + 1)
    (hbig1 : ∀ m ∈ E T, 0 < det J m → det J next * det prev m < (faceLen T J : ℤ) * det J m)
    (hbig2 : ∀ m ∈ E T, det J m < 0 →
      det prev J * (-det next m) < (faceLen T J : ℤ) * (-det J m)) :
    PushData S T J prev next (faceStart T J + det J next • dir prev) (dir J)
      (((faceLen T J : ℤ) - c).toNat) (det prev J * det J next) := by
  set s0 := faceStart T J with hs0def
  set len : ℕ := faceLen T J with hlendef
  set k : ℕ := (((len : ℤ) - c).toNat) with hkdef
  have hkZ : (k : ℤ) = (len : ℤ) - c := Int.toNat_of_nonneg (by omega)
  have hlen1 : 1 ≤ len := one_le_faceLen hTfin hJ
  have hseg := face_eq_segment hlc hTfin hJ
  have hsegmem : ∀ t : ℕ, t ≤ len → s0 + (t : ℤ) • dir J ∈ T :=
    fun t ht => face_subset T J (by rw [hseg]; exact ⟨t, ht, rfl⟩)
  have hs0J : s0 ∈ face T J := by
    have : s0 = s0 + ((0 : ℕ) : ℤ) • dir J := by simp
    rw [this, hseg]; exact ⟨0, Nat.zero_le _, rfl⟩
  have hs0P : s0 ∈ face T prev := by
    rw [hs0def, ← adjacent_shared_vertex hTfin hlc hprev hJ hdp hadjP]
    exact faceEnd_mem hlc hTfin hprev
  set e0 := s0 + (len : ℤ) • dir J with he0def
  have he0N : e0 ∈ face T next := by
    rw [he0def, hs0def, hlendef, adjacent_shared_vertex hTfin hlc hJ hnext hdn hadjN]
    have h0 : faceStart T next = faceStart T next + ((0 : ℕ) : ℤ) • dir next := by simp
    rw [h0, face_eq_segment hlc hTfin hnext]; exact ⟨0, Nat.zero_le _, rfl⟩
  have he0J : e0 ∈ face T J := by rw [hseg]; exact ⟨len, le_rfl, rfl⟩
  have svJ : suppVal T J = dot J s0 := suppVal_eq hs0J
  have svP : suppVal T prev = dot prev s0 := suppVal_eq hs0P
  have svN : suppVal T next = dot next e0 := suppVal_eq he0N
  have hdirJ : dot J (dir J) = 0 := by rw [dot_dir_eq_det]; simp [det]; ring
  -- `q = p + k • dir J = e0 - (det prev J) • dir next`
  have hq : s0 + (det J next) • dir prev + (k : ℤ) • dir J = e0 - (det prev J) • dir next := by
    rw [hkZ, he0def, sub_smul]
    have : (det prev J) • dir next = c • dir J - (det J next) • dir prev := by rw [← hc]; abel
    rw [this]; abel
  have hle : ∀ m ∈ E T, ∀ x ∈ T, dot m x ≤ suppVal T m :=
    fun m _ x hx => le_suppVal hTfin hTne hx
  refine
    { hTfin := hTfin, hTne := hTne, harea := harea, hT := hT
      hnO := hJ, hm1 := hprev, hm2 := hnext
      h12 := ?_, h1O := ?_, h2O := ?_
      hvJ := ?_, hvJO := hdirJ
      hL := mul_pos hdp hdn
      hlev := ?_, hp1 := ?_, hp2 := ?_
      hs1 := ?_, hs2 := ?_
      hadj := fun m hm h1 h2 h3 => hadj_of_fan hTfin hlc harea hJ hprev hnext hdp hdn hadjP
        hadjN m hm h1 h2 h3
      hk := by omega
      hlen := hlenS }
  · intro h; rw [h] at hdp; rw [det_swap] at hdp; linarith
  · intro h; rw [h, det_self] at hdp; exact lt_irrefl 0 hdp
  · intro h; rw [h, det_self] at hdn; exact lt_irrefl 0 hdn
  · intro h
    have h1 : -J.2 = 0 := congrArg Prod.fst h
    have h2 : J.1 = 0 := congrArg Prod.snd h
    exact hJ.1.ne_zero (Prod.ext h2 (by simpa using h1))
  · rw [svJ, dot_add, dot_smul_r, dot_dir_eq_det]; ring
  · rw [svP, dot_add, dot_smul_r, dot_dir_eq_det, det_self]; ring
  · rw [hq, svN, dot_sub, dot_smul_r, dot_dir_eq_det, det_self]; ring
  · -- `hs1`
    intro m hm hmP hmJ
    rw [dot_add, dot_smul_r, dot_dir_eq_det]
    rcases lt_trichotomy (det prev m) 0 with hneg | hzero | hpos
    · have := hle m hm s0 hs0J.1; nlinarith
    · rcases eq_or_neg_of_det_zero hprev.1 hm.1 hzero with h | h
      · exact absurd h hmP
      · rw [hzero, mul_zero, add_zero]
        have h1 := hle m hm _ (hsegmem 1 hlen1)
        rw [dot_row, dot_dir_eq_det, h, det_neg_right'] at h1
        rw [h]
        push_cast at h1
        have := det_swap J prev
        linarith
    · have hJm : 0 < det J m := by
        rcases lt_trichotomy (det J m) 0 with h | h | h
        · exact absurd ⟨hpos, by rw [det_swap]; linarith⟩ (hadjP m hm)
        · rcases eq_or_neg_of_det_zero hJ.1 hm.1 h with h' | h'
          · exact absurd h' hmJ
          · rw [h', det_neg_right'] at hpos; linarith
        · exact h
      have h1 := hle m hm _ (hsegmem len le_rfl)
      rw [dot_row, dot_dir_eq_det] at h1
      have := hbig1 m hm hJm
      linarith
  · -- `hs2`
    intro m hm hmN hmJ
    rw [hq, dot_sub, dot_smul_r, dot_dir_eq_det]
    rcases lt_trichotomy (det next m) 0 with hneg | hzero | hpos
    · have hJm : det J m < 0 := by
        rcases lt_trichotomy (det J m) 0 with h | h | h
        · exact h
        · rcases eq_or_neg_of_det_zero hJ.1 hm.1 h with h' | h'
          · exact absurd h' hmJ
          · rw [h', det_neg_right', det_swap] at hneg; linarith
        · exact absurd ⟨h, by rw [det_swap]; linarith⟩ (hadjN m hm)
      have h1 := hle m hm s0 hs0J.1
      have := hbig2 m hm hJm
      rw [he0def, dot_row, dot_dir_eq_det]
      nlinarith
    · rcases eq_or_neg_of_det_zero hnext.1 hm.1 hzero with h | h
      · exact absurd h hmN
      · rw [hzero, mul_zero, sub_zero]
        have hlm1 : len - 1 ≤ len := Nat.sub_le _ _
        have h1 := hle m hm _ (hsegmem (len - 1) hlm1)
        have hc1 : ((len - 1 : ℕ) : ℤ) = (len : ℤ) - 1 := by push_cast [hlen1]; ring
        rw [dot_row, dot_dir_eq_det, hc1] at h1
        rw [he0def, dot_row, dot_dir_eq_det]
        rw [h, det_neg_right'] at h1 ⊢
        linarith
    · have := hle m hm e0 he0J.1
      nlinarith

end Nivat.Hole1QShell

/-! ## §12. The quadrilateral bound

A point `z` lying between the `J`-levels `s` and `s + L`, on the inner side of the line
`a₀a₁` (functional `u`, decreasing along `dir J`) and of the line `b₀b₁` (functional `v`,
increasing along `dir J`), is a real convex combination of `a₀, a₁, b₀, b₁`; so every linear
bound valid at the four corners is valid at `z`.  This single lemma serves both the
`fillCover` window margin and the seed coverage. -/

namespace Nivat.Hole1QShell

open Nivat Nivat.LE2

theorem quad_bound {J u v a0 a1 b0 b1 z m : ℤ × ℤ} {s L c : ℤ} (hL : 0 < L) (hJ : J ≠ 0)
    (ha0 : dot J a0 = s) (hb0 : dot J b0 = s) (ha1 : dot J a1 = s + L) (hb1 : dot J b1 = s + L)
    (hu : dot u a0 = dot u a1) (hv : dot v b0 = dot v b1)
    (hud : dot u (dir J) < 0) (hvd : 0 < dot v (dir J))
    (hz1 : s ≤ dot J z) (hz2 : dot J z ≤ s + L) (hzu : dot u z ≤ dot u a0)
    (hzv : dot v z ≤ dot v b0)
    (h0 : dot m a0 ≤ c) (h1 : dot m a1 ≤ c) (h2 : dot m b0 ≤ c) (h3 : dot m b1 ≤ c) :
    dot m z ≤ c := by
  -- real coordinates
  have cast : ∀ n w : ℤ × ℤ, (dot n w : ℝ) = (n.1 : ℝ) * w.1 + (n.2 : ℝ) * w.2 := by
    intro n w; simp only [dot]; push_cast; ring
  set J1 : ℝ := ((J.1 : ℤ) : ℝ) with hJ1
  set J2 : ℝ := ((J.2 : ℤ) : ℝ) with hJ2
  have hJJ : 0 < J1 ^ 2 + J2 ^ 2 := by
    by_contra hle; push_neg at hle
    have e1 : J1 = 0 := by nlinarith [sq_nonneg J1, sq_nonneg J2]
    have e2 : J2 = 0 := by nlinarith [sq_nonneg J1, sq_nonneg J2]
    refine absurd (Prod.ext ?_ ?_ : J = 0) hJ
    · simp only [Prod.fst_zero]; rw [hJ1] at e1; exact_mod_cast e1
    · simp only [Prod.snd_zero]; rw [hJ2] at e2; exact_mod_cast e2
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  set lam : ℝ := ((dot J z : ℝ) - s) / L with hlam
  have hz1R : (s : ℝ) ≤ dot J z := by exact_mod_cast hz1
  have hz2R : (dot J z : ℝ) ≤ s + L := by exact_mod_cast hz2
  have hl0 : 0 ≤ lam := div_nonneg (by linarith) hLR.le
  have hl1 : lam ≤ 1 := (div_le_one hLR).mpr (by linarith)
  -- `P = (1-λ)a₀ + λa₁`, `Q = (1-λ)b₀ + λb₁`, as coordinates
  set P1 : ℝ := (1 - lam) * a0.1 + lam * a1.1
  set P2 : ℝ := (1 - lam) * a0.2 + lam * a1.2
  set Q1 : ℝ := (1 - lam) * b0.1 + lam * b1.1
  set Q2 : ℝ := (1 - lam) * b0.2 + lam * b1.2
  -- `z - P` and `Q - P` are orthogonal to `J`
  have hlevP : J1 * P1 + J2 * P2 = (dot J z : ℝ) := by
    have e0 := cast J a0; have e1 := cast J a1
    rw [ha0] at e0; rw [ha1] at e1
    simp only [P1, P2, hlam]; field_simp; push_cast at e0 e1 ⊢; nlinarith
  have hlevQ : J1 * Q1 + J2 * Q2 = (dot J z : ℝ) := by
    have e0 := cast J b0; have e1 := cast J b1
    rw [hb0] at e0; rw [hb1] at e1
    simp only [Q1, Q2, hlam]; field_simp; push_cast at e0 e1 ⊢; nlinarith
  have hzJ := cast J z
  -- decomposition along `dir J = (-J2, J1)`
  have key : J1 * ((z.1 : ℝ) - P1) + J2 * ((z.2 : ℝ) - P2) = 0 := by linarith
  have keyQ : J1 * (Q1 - P1) + J2 * (Q2 - P2) = 0 := by linarith
  have hN : (J1 ^ 2 + J2 ^ 2) ≠ 0 := hJJ.ne'
  set α : ℝ := (-J2 * ((z.1 : ℝ) - P1) + J1 * ((z.2 : ℝ) - P2)) / (J1 ^ 2 + J2 ^ 2)
  set β : ℝ := (-J2 * (Q1 - P1) + J1 * (Q2 - P2)) / (J1 ^ 2 + J2 ^ 2)
  have hzα1 : (z.1 : ℝ) = P1 + α * (-J2) := by
    have : α * (-J2) = (z.1 : ℝ) - P1 := by
      simp only [α]; rw [div_mul_eq_mul_div, div_eq_iff hN]; linear_combination (-J1) * key
    linarith
  have hzα2 : (z.2 : ℝ) = P2 + α * J1 := by
    have : α * J1 = (z.2 : ℝ) - P2 := by
      simp only [α]; rw [div_mul_eq_mul_div, div_eq_iff hN]; linear_combination (-J2) * key
    linarith
  have hQβ1 : Q1 = P1 + β * (-J2) := by
    have : β * (-J2) = Q1 - P1 := by
      simp only [β]; rw [div_mul_eq_mul_div, div_eq_iff hN]; linear_combination (-J1) * keyQ
    linarith
  have hQβ2 : Q2 = P2 + β * J1 := by
    have : β * J1 = Q2 - P2 := by
      simp only [β]; rw [div_mul_eq_mul_div, div_eq_iff hN]; linear_combination (-J2) * keyQ
    linarith
  -- evaluate a functional `n` along the decomposition
  have evalP : ∀ n : ℤ × ℤ, (n.1 : ℝ) * P1 + n.2 * P2 =
      (1 - lam) * (dot n a0 : ℝ) + lam * dot n a1 := by
    intro n; rw [cast, cast]; simp only [P1, P2]; ring
  have evalQ : ∀ n : ℤ × ℤ, (n.1 : ℝ) * Q1 + n.2 * Q2 =
      (1 - lam) * (dot n b0 : ℝ) + lam * dot n b1 := by
    intro n; rw [cast, cast]; simp only [Q1, Q2]; ring
  have evalDir : ∀ n : ℤ × ℤ, (dot n (dir J) : ℝ) = (n.1 : ℝ) * (-J2) + n.2 * J1 := by
    intro n; rw [cast]; simp [dir, J1, J2]
  have evalZ : ∀ n : ℤ × ℤ, (dot n z : ℝ) =
      (1 - lam) * (dot n a0 : ℝ) + lam * dot n a1 + α * dot n (dir J) := by
    intro n; rw [cast n z, hzα1, hzα2, evalDir, ← evalP]; ring
  have evalQ' : ∀ n : ℤ × ℤ, (1 - lam) * (dot n b0 : ℝ) + lam * dot n b1 =
      (1 - lam) * (dot n a0 : ℝ) + lam * dot n a1 + β * dot n (dir J) := by
    intro n; rw [← evalQ, hQβ1, hQβ2, evalDir, ← evalP]; ring
  -- signs: `0 ≤ α ≤ β`
  have huR : (dot u (dir J) : ℝ) < 0 := by exact_mod_cast hud
  have hvR : (0 : ℝ) < dot v (dir J) := by exact_mod_cast hvd
  have hα0 : 0 ≤ α := by
    have e := evalZ u
    have hzu' : (dot u z : ℝ) ≤ dot u a0 := by exact_mod_cast hzu
    have hu' : (dot u a1 : ℝ) = dot u a0 := by exact_mod_cast hu.symm
    rw [hu'] at e
    have hαdu : α * (dot u (dir J) : ℝ) ≤ 0 := by linarith
    by_contra hneg; push_neg at hneg
    have := mul_pos_of_neg_of_neg hneg huR
    linarith
  have hαβ : α ≤ β := by
    have e := evalZ v
    have e' := evalQ' v
    have hzv' : (dot v z : ℝ) ≤ dot v b0 := by exact_mod_cast hzv
    have hv' : (dot v b1 : ℝ) = dot v b0 := by exact_mod_cast hv.symm
    rw [hv'] at e'
    have hmul : α * (dot v (dir J) : ℝ) ≤ β * dot v (dir J) := by linarith
    exact le_of_mul_le_mul_right hmul hvR
  -- conclude for `m`
  have ez := evalZ m
  have eq := evalQ' m
  clear_value α β P1 P2 Q1 Q2 lam
  have hmR0 : (dot m a0 : ℝ) ≤ c := by exact_mod_cast h0
  have hmR1 : (dot m a1 : ℝ) ≤ c := by exact_mod_cast h1
  have hmR2 : (dot m b0 : ℝ) ≤ c := by exact_mod_cast h2
  have hmR3 : (dot m b1 : ℝ) ≤ c := by exact_mod_cast h3
  have hP : (1 - lam) * (dot m a0 : ℝ) + lam * dot m a1 ≤ c := by
    linarith [mul_nonneg (sub_nonneg.2 hl1) (sub_nonneg.2 hmR0), mul_nonneg hl0 (sub_nonneg.2 hmR1)]
  have hQ : (1 - lam) * (dot m b0 : ℝ) + lam * dot m b1 ≤ c := by
    linarith [mul_nonneg (sub_nonneg.2 hl1) (sub_nonneg.2 hmR2), mul_nonneg hl0 (sub_nonneg.2 hmR3)]
  have goal : (dot m z : ℝ) ≤ c := by
    rcases eq_or_lt_of_le (hα0.trans hαβ) with hβ0 | hβpos
    · have : α = 0 := le_antisymm (hβ0 ▸ hαβ) hα0
      rw [ez, this]; linarith
    · -- `z = (1-μ)P + μQ` with `μ = α/β`
      set μ : ℝ := α / β
      have hμ0 : 0 ≤ μ := div_nonneg hα0 hβpos.le
      have hμ1 : μ ≤ 1 := (div_le_one hβpos).mpr hαβ
      have hαμ : α = μ * β := by simp only [μ]; field_simp
      have : (dot m z : ℝ) = (1 - μ) * ((1 - lam) * (dot m a0 : ℝ) + lam * dot m a1) +
          μ * ((1 - lam) * (dot m b0 : ℝ) + lam * dot m b1) := by
        rw [ez, eq, hαμ]; ring
      rw [this]
      linarith [mul_nonneg (sub_nonneg.2 hμ1) (sub_nonneg.2 hP), mul_nonneg hμ0 (sub_nonneg.2 hQ)]
  exact_mod_cast goal

end Nivat.Hole1QShell

/-! ## §13. The shape of the push shell's pushed face

With `vJ = dir nO` and the neighbour signs `dot m1 vJ < 0 < dot m2 vJ`, the `nO`-face of the
push shell is exactly the new row, starting at `p` and of length `k`. -/

namespace Nivat.Hole1QShell

open Nivat Nivat.LE2 Nivat.PolyChain

namespace PushData

variable {S T : Set (ℤ × ℤ)} {nO m1 m2 p vJ : ℤ × ℤ} {k : ℕ} {L : ℤ}
variable (D : PushData S T nO m1 m2 p vJ k L)
include D

theorem E_pushShell : E (pushShell T p vJ k) = E T := by
  rw [pushShell, E_latHull D.Y_finite, D.E_eq]

theorem face_eq_rowW (hvJp : Prim vJ) (hd1 : dot m1 vJ < 0) (hd2 : 0 < dot m2 vJ) :
    face (pushShell T p vJ k) nO = rowW p vJ k := by
  apply Set.Subset.antisymm
  · intro w hw
    have hpY : p ∈ pushShell T p vJ k := subset_latHull _ (Or.inr (left_mem_rowW p vJ k))
    obtain ⟨hle, hlev⟩ := D.pushShell_le w hw.1
    have hwlev : dot nO w = suppVal T nO + L := by
      have := hw.2 p hpY; rw [D.hlev] at this; linarith
    have hdw : dot nO (w - p) = 0 := by rw [dot_sub, hwlev, D.hlev]; ring
    have hdet : det vJ (w - p) = 0 :=
      det_eq_zero_of_dot_eq_zero D.hnO.1.ne_zero D.hvJO hdw
    obtain ⟨t, ht⟩ := exists_smul_of_det_eq_zero hvJp hdet
    have hwt : w = p + t • vJ := by
      have : w - p = t • vJ := by rw [ht]; rfl
      rw [← this]; abel
    have h1 := hle m1 D.hm1 D.h1O
    have h2 := hle m2 D.hm2 D.h2O
    rw [hwt, dot_row] at h1 h2
    rw [← D.hp1] at h1
    rw [← D.hp2, dot_row] at h2
    have ht0 : 0 ≤ t := by
      by_contra hneg; push_neg at hneg
      have := mul_pos_of_neg_of_neg hneg hd1; linarith
    have htk : t ≤ k := by
      by_contra hgt; push_neg at hgt
      have := mul_lt_mul_of_pos_right hgt hd2; linarith
    exact ⟨t.toNat, by omega, by rw [hwt, Int.toNat_of_nonneg ht0]⟩
  · exact fun z hz => face_subset_face_latHull _ nO (D.rowW_subset_face hz)

theorem faceStart_eq (hvJ : vJ = dir nO) (hvJp : Prim vJ) (hd1 : dot m1 vJ < 0)
    (hd2 : 0 < dot m2 vJ) : faceStart (pushShell T p vJ k) nO = p := by
  have hfin := D.pushShell_finite
  have hE : nO ∈ E (pushShell T p vJ k) := by rw [D.E_pushShell]; exact D.hnO
  have hface := D.face_eq_rowW hvJp hd1 hd2
  have hmem := faceStart_mem hfin hE
  have hmin := faceStart_min hfin hE p (by rw [hface]; exact left_mem_rowW p vJ k)
  rw [hface] at hmem
  obtain ⟨j, -, hj⟩ := hmem
  rw [hj, ← hvJ, dot_row] at hmin
  have hpos : 0 < dot vJ vJ := by
    rw [hvJ]; exact dot_dir_pos D.hnO.1
  have : (j : ℤ) = 0 := by nlinarith [(Nat.cast_nonneg j : (0 : ℤ) ≤ j)]
  rw [hj, this, zero_smul, add_zero]

theorem faceLen_eq (hvJp : Prim vJ) (hd1 : dot m1 vJ < 0) (hd2 : 0 < dot m2 vJ) :
    faceLen (pushShell T p vJ k) nO = k := by
  unfold faceLen
  rw [D.face_eq_rowW hvJp hd1 hd2, rowW_encard p vJ k D.hvJ]
  norm_cast

/-- The far corner: the `m2`-face of the push shell starts at `p + k • vJ`. -/
theorem faceStart_m2 (hvJ : vJ = dir nO) (hvJp : Prim vJ) (hd1 : dot m1 vJ < 0)
    (hd2 : 0 < dot m2 vJ) (hdet : 0 < det nO m2)
    (hadj : ∀ μ ∈ E T, ¬(0 < det nO μ ∧ 0 < det μ m2)) :
    faceStart (pushShell T p vJ k) m2 = p + (k : ℤ) • vJ := by
  have hfin := D.pushShell_finite
  have hlc : IsLatticeConvexRegion (pushShell T p vJ k) :=
    isLatticeConvexRegion_latHull D.Y_finite
  have hEY := D.E_pushShell
  have h := adjacent_shared_vertex hfin hlc (hEY ▸ D.hnO) (hEY ▸ D.hm2) hdet
    (by rw [hEY]; exact hadj)
  rw [← h, D.faceStart_eq hvJ hvJp hd1 hd2, D.faceLen_eq hvJp hd1 hd2, hvJ]

end PushData

end Nivat.Hole1QShell

/-! ## §14. Pinned-end face parametrisation, monotone face length; §15. the filler -/

namespace Nivat.Hole1QShell

open Nivat Nivat.LE2 Nivat.PolyChain

/-- With the `J`-face end pinned at `g`, the face is `{g - t • dir J | t ≤ len}`. -/
theorem mem_face_of_pinned {T : Set (ℤ × ℤ)} {J g : ℤ × ℤ} (hlc : IsLatticeConvexRegion T)
    (hfin : T.Finite) (hJ : J ∈ E T) (hpin : faceStart T J + (faceLen T J : ℤ) • dir J = g) :
    ∀ t : ℕ, t ≤ faceLen T J → g - (t : ℤ) • dir J ∈ face T J := by
  intro t ht
  rw [face_eq_segment hlc hfin hJ]
  refine ⟨faceLen T J - t, Nat.sub_le _ _, ?_⟩
  rw [← hpin]
  push_cast [ht]
  rw [sub_smul]; abel

/-- The start of a pinned face. -/
theorem faceStart_of_pinned {T : Set (ℤ × ℤ)} {J g : ℤ × ℤ}
    (hpin : faceStart T J + (faceLen T J : ℤ) • dir J = g) :
    faceStart T J = g - (faceLen T J : ℤ) • dir J := by
  rw [← hpin]; abel

/-- Face length is monotone along a nested tower sharing the pinned `J`-face end and the
`J`-support level. -/
theorem faceLen_mono_of_pinned {T T' : Set (ℤ × ℤ)} {J g : ℤ × ℤ}
    (hlc : IsLatticeConvexRegion T) (hfin : T.Finite) (hJ : J ∈ E T)
    (hlc' : IsLatticeConvexRegion T') (hfin' : T'.Finite) (hJ' : J ∈ E T')
    (hsub : T ⊆ T') (hpin : faceStart T J + (faceLen T J : ℤ) • dir J = g)
    (hpin' : faceStart T' J + (faceLen T' J : ℤ) • dir J = g)
    (hlev : ∀ z ∈ T', dot J z ≤ dot J g) :
    faceLen T J ≤ faceLen T' J := by
  have hx := mem_face_of_pinned hlc hfin hJ hpin (faceLen T J) le_rfl
  have hxT' : g - (faceLen T J : ℤ) • dir J ∈ face T' J := by
    refine ⟨hsub hx.1, fun y hy => ?_⟩
    rw [dot_sub, dot_smul_r, dot_dir_eq_det, det_self, mul_zero, sub_zero]
    exact hlev y hy
  rw [face_eq_segment hlc' hfin' hJ'] at hxT'
  obtain ⟨t, ht, heq⟩ := hxT'
  rw [faceStart_of_pinned hpin'] at heq
  have hprim := prim_dir_of_prim hJ'.1
  have h2 : ((faceLen T' J : ℤ) - faceLen T J - t) • dir J = 0 := by
    have e : g - (faceLen T J : ℤ) • dir J - (g - (faceLen T' J : ℤ) • dir J + (t : ℤ) • dir J) = 0 := by
      rw [heq]; abel
    calc ((faceLen T' J : ℤ) - faceLen T J - t) • dir J
        = g - (faceLen T J : ℤ) • dir J - (g - (faceLen T' J : ℤ) • dir J + (t : ℤ) • dir J) := by
          simp only [sub_smul]; abel
      _ = 0 := e
  have h3 := (smul_eq_zero.mp h2).resolve_right hprim.ne_zero
  omega

/-- **The filler is never enveloped**: adding the lattice point two steps beyond the start of
the `J`-face breaks lattice convexity (the skipped point `faceStart - dir J` is in the hull). -/
theorem not_envOf_filler {U T : Set (ℤ × ℤ)} {J : ℤ × ℤ}
    (hfin : T.Finite) (hJ : J ∈ E T) :
    ¬ EnvOf U (T ∪ {faceStart T J - (2 : ℤ) • dir J}) := by
  intro henv
  obtain ⟨C, hconv, -, hCeq⟩ := henv.1.1
  set s0 := faceStart T J
  have hs0 : s0 ∈ face T J := faceStart_mem hfin hJ
  have hin : s0 ∈ T ∪ {s0 - (2 : ℤ) • dir J} := Or.inl hs0.1
  have hx : s0 - (2 : ℤ) • dir J ∈ T ∪ {s0 - (2 : ℤ) • dir J} := Or.inr rfl
  rw [hCeq] at hin hx
  have hmid : toReal (s0 - dir J) ∈ C := by
    have := hconv hin hx (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)
    convert this using 1
    simp only [toReal, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, Prod.fst_sub, Prod.snd_sub,
      Prod.smul_fst, Prod.smul_snd]
    push_cast
    ext <;> simp <;> ring
  have hmem : s0 - dir J ∈ T ∪ {s0 - (2 : ℤ) • dir J} := by rw [hCeq]; exact hmid
  have hne2 : s0 - dir J ≠ s0 - (2 : ℤ) • dir J := by
    intro h
    have h' : dir J = (2 : ℤ) • dir J := by
      have := congrArg (fun v => s0 - v) h; simpa using this
    have : (1 : ℤ) • dir J = (2 : ℤ) • dir J := by rw [one_smul]; exact h'
    have := smul_left_injective ℤ (prim_dir_of_prim hJ.1).ne_zero this
    norm_num at this
  rcases hmem with hT | hx'
  · -- `s0 - dir J` would be on the `J`-face, before its start
    have hface : s0 - dir J ∈ face T J := by
      refine ⟨hT, fun y hy => ?_⟩
      rw [dot_sub, dot_dir_eq_det, det_self, sub_zero]; exact hs0.2 y hy
    have hmin := faceStart_min hfin hJ _ hface
    rw [dot_sub] at hmin
    have := dot_dir_pos hJ.1
    linarith
  · exact hne2 hx'

end Nivat.Hole1QShell

/-! ## §16. `quad_mem`: membership in a lattice polygon from four corners (with a shift) -/

namespace Nivat.Hole1QShell

open Nivat Nivat.LE2

theorem quad_mem {Y : Set (ℤ × ℤ)} (hYfin : Y.Finite) (hYne : Y.Nonempty) (harea : PosArea Y)
    (hlc : IsLatticeConvexRegion Y)
    {J u v a0 a1 b0 b1 z w : ℤ × ℤ} {s L : ℤ} (hL : 0 < L) (hJ : J ≠ 0)
    (ha0 : dot J a0 = s) (hb0 : dot J b0 = s) (ha1 : dot J a1 = s + L) (hb1 : dot J b1 = s + L)
    (hu : dot u a0 = dot u a1) (hv : dot v b0 = dot v b1)
    (hud : dot u (dir J) < 0) (hvd : 0 < dot v (dir J))
    (hz1 : s ≤ dot J z) (hz2 : dot J z ≤ s + L) (hzu : dot u z ≤ dot u a0)
    (hzv : dot v z ≤ dot v b0)
    (h0 : a0 + w ∈ Y) (h1 : a1 + w ∈ Y) (h2 : b0 + w ∈ Y) (h3 : b1 + w ∈ Y) :
    z + w ∈ Y := by
  refine mem_of_dot_le_suppVal hYfin hYne harea hlc (fun m _ => ?_)
  have e0 := le_suppVal hYfin hYne (n := m) h0
  have e1 := le_suppVal hYfin hYne (n := m) h1
  have e2 := le_suppVal hYfin hYne (n := m) h2
  have e3 := le_suppVal hYfin hYne (n := m) h3
  rw [dot_add] at e0 e1 e2 e3 ⊢
  have := quad_bound (m := m) (c := suppVal Y m - dot m w) hL hJ ha0 hb0 ha1 hb1 hu hv hud hvd
    hz1 hz2 hzu hzv (by linarith) (by linarith) (by linarith) (by linarith)
  linarith

end Nivat.Hole1QShell

/-! ## §17. The pinned `J`-tower: bundled hypotheses and per-index facts

`PinTower` bundles exactly what `Hole1JPack.exists_jpack` (J package, cw) and the chain
provide, for the reindexed chain `A B kk`.  Everything below is chain-agnostic. -/

namespace Nivat.Hole1QShell

open Nivat Nivat.LE2 Nivat.PolyChain Nivat.Colle35

/-- Copied from `tmp/wip/hole1-bottom.lean` (tmp files cannot import each other). -/
theorem qs_real_ray_mem {C : Set (ℝ × ℝ)} (hC : Convex ℝ C) {q v : ℝ × ℝ}
    (hray : ∀ k : ℕ, q + (k : ℝ) • v ∈ C) {t : ℝ} (ht : 0 ≤ t) : q + t • v ∈ C := by
  set n : ℕ := ⌊t⌋₊ with hndef
  have hn1 : (n : ℝ) ≤ t := Nat.floor_le ht
  have hn2 : t ≤ (n : ℝ) + 1 := (Nat.lt_floor_add_one t).le
  set θ : ℝ := t - n with hθdef
  have hθ0 : 0 ≤ θ := by rw [hθdef]; linarith
  have hθ1 : θ ≤ 1 := by rw [hθdef]; linarith
  have hm1 := hray n
  have hm2 := hray (n + 1)
  push_cast at hm2
  have hcomb := hC hm1 hm2 (show (0:ℝ) ≤ 1 - θ by linarith) hθ0 (by ring)
  have heq : (1 - θ) • (q + (n : ℝ) • v) + θ • (q + ((n : ℝ) + 1) • v) = q + t • v := by
    have ht' : t = (n : ℝ) + θ := by rw [hθdef]; ring
    rw [ht']
    module
  rwa [heq] at hcomb

theorem qs_mem_of_nat_iter {R : Set (ℤ × ℤ)} {r : ℤ × ℤ} (h : ∀ z ∈ R, z + r ∈ R)
    {z : ℤ × ℤ} (hz : z ∈ R) (k : ℕ) : z + (k : ℤ) • r ∈ R := by
  induction k with
  | zero => simpa using hz
  | succ k ih =>
    have e : z + ((k + 1 : ℕ) : ℤ) • r = (z + (k : ℤ) • r) + r := by
      rw [Nat.cast_succ, add_smul, one_smul, add_assoc]
    rw [e]; exact h _ ih

theorem qs_cone_mem {R : Set (ℤ × ℤ)} (hlc : IsLatticeConvexRegion R) {r₁ r₂ : ℤ × ℤ}
    (h1 : ∀ z ∈ R, z + r₁ ∈ R) (h2 : ∀ z ∈ R, z + r₂ ∈ R) {x y : ℤ × ℤ} (hx : x ∈ R)
    {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hy : toReal y = toReal x + α • toReal r₁ + β • toReal r₂) : y ∈ R := by
  have tadd : ∀ z w : ℤ × ℤ, toReal (z + w) = toReal z + toReal w := fun z w => by simp [toReal]
  have tsmul : ∀ (n : ℤ) (z : ℤ × ℤ), toReal (n • z) = (n : ℝ) • toReal z :=
    fun n z => by simp [toReal]
  obtain ⟨C, hC, -, hReq⟩ := hlc
  have hmem : ∀ z, z ∈ R → toReal z ∈ C := fun z hz => by rw [hReq] at hz; exact hz
  have hA : ∀ k : ℕ, toReal x + (k : ℝ) • toReal r₁ + β • toReal r₂ ∈ C := by
    intro k
    have hk : x + (k : ℤ) • r₁ ∈ R := qs_mem_of_nat_iter h1 hx k
    have hray : ∀ j : ℕ, toReal (x + (k : ℤ) • r₁) + (j : ℝ) • toReal r₂ ∈ C := by
      intro j
      have := hmem _ (qs_mem_of_nat_iter h2 hk j)
      rw [tadd (x + (k : ℤ) • r₁) ((j : ℤ) • r₂), tsmul] at this
      simpa using this
    have := qs_real_ray_mem hC hray hβ
    rw [tadd, tsmul] at this
    simpa using this
  have hB := qs_real_ray_mem hC (q := toReal x + β • toReal r₂) (v := toReal r₁)
    (fun k => by
      have := hA k
      rwa [add_right_comm] at this) hα
  have hfin : toReal y ∈ C := by
    rw [hy]
    have : toReal x + β • toReal r₂ + α • toReal r₁ =
        toReal x + α • toReal r₁ + β • toReal r₂ := by abel
    rw [← this]; exact hB
  rw [hReq]; exact hfin

theorem qs_quadrant_mem {R : Set (ℤ × ℤ)} (hlc : IsLatticeConvexRegion R) {J nxt : ℤ × ℤ}
    (hδ : 0 < det J nxt)
    (h1 : ∀ z ∈ R, z + (-(dir nxt)) ∈ R) (h2 : ∀ z ∈ R, z + (-(dir J)) ∈ R)
    {x y : ℤ × ℤ} (hx : x ∈ R)
    (hl : dot (-J) y ≤ dot (-J) x) (hv : dot nxt y ≤ dot nxt x) : y ∈ R := by
  have hδR : (0 : ℝ) < (det J nxt : ℝ) := by exact_mod_cast hδ
  have hA0 : (0 : ℝ) ≤ ((dot (-J) x - dot (-J) y : ℤ) : ℝ) / (det J nxt : ℝ) :=
    div_nonneg (by exact_mod_cast sub_nonneg.mpr hl) hδR.le
  have hB0 : (0 : ℝ) ≤ ((dot nxt x - dot nxt y : ℤ) : ℝ) / (det J nxt : ℝ) :=
    div_nonneg (by exact_mod_cast sub_nonneg.mpr hv) hδR.le
  refine qs_cone_mem hlc h1 h2 hx hA0 hB0 ?_
  have hne : (det J nxt : ℝ) ≠ 0 := hδR.ne'
  apply Prod.ext
  · simp only [toReal, dot, det, dir, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul, Prod.fst_neg, Prod.snd_neg, Int.cast_sub, Int.cast_add, Int.cast_mul,
      Int.cast_neg] at hne ⊢
    field_simp
    ring
  · simp only [toReal, dot, det, dir, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul, Prod.fst_neg, Prod.snd_neg, Int.cast_sub, Int.cast_add, Int.cast_mul,
      Int.cast_neg] at hne ⊢
    field_simp
    ring

/-- The pinned `J`-tower (cw orientation), as delivered by the J package. -/
structure PinTower {ξ : Config ℤ} (d : DecompDataZ ξ) (A B : ℕ → Set (ℤ × ℤ)) (kk : ℕ → ℕ)
    (vl nℓ J prv nxt g : ℤ × ℤ) : Prop where
  hfin : ∀ i, (hatOf A kk vl i).Finite
  henv : ∀ i, EnvOf (↑d.Sphi : Set (ℤ × ℤ)) (hatOf A kk vl i)
  hmono : ∀ i j, i ≤ j → hatOf A kk vl i ⊆ hatOf A kk vl j
  hBA : ∀ i, B i ⊆ A i
  hAB : ∀ i, A i ⊆ Colle35.halfStrip (B i) vl
  hJ : J ∈ E (↑d.Sphi : Set (ℤ × ℤ))
  hprv : prv ∈ E (↑d.Sphi : Set (ℤ × ℤ))
  hnxt : nxt ∈ E (↑d.Sphi : Set (ℤ × ℤ))
  hdp : 0 < det prv J
  hdn : 0 < det J nxt
  hadjP : ∀ μ ∈ E (↑d.Sphi : Set (ℤ × ℤ)), ¬(0 < det prv μ ∧ 0 < det μ J)
  hadjN : ∀ μ ∈ E (↑d.Sphi : Set (ℤ × ℤ)), ¬(0 < det J μ ∧ 0 < det μ nxt)
  hpin : ∀ i, faceStart (hatOf A kk vl i) J + (faceLen (hatOf A kk vl i) J : ℤ) • dir J = g
  hunb : ∀ L : ℕ, ∃ i, L ≤ faceLen (hatOf A kk vl i) J
  hhp : ∀ i, hatOf A kk vl i ⊆ Nivat.CK224.halfPlaneGE (-J) (dot (-J) g)
  hswept : Nivat.MaxEnv.SweptClosed (⋃ i, hatOf A kk vl i) (-(dir nxt)) (-J) (dot (-J) g)
  hray : ∀ k : ℕ, g - (k : ℤ) • dir J ∈ ⋃ i, hatOf A kk vl i
  hsupp : ∀ z ∈ ⋃ i, hatOf A kk vl i, dot nxt z ≤ dot nxt g
  hconv : IsLatticeConvexRegion (⋃ i, hatOf A kk vl i)
  hnℓ : nℓ ∈ E (↑d.Sphi : Set (ℤ × ℤ))
  hnℓ' : -nℓ ∈ E (↑d.Sphi : Set (ℤ × ℤ))
  hvlp : Prim vl
  hperp : dot nℓ vl = 0
  hfwd : 0 < dot J vl

namespace PinTower

variable {ξ : Config ℤ} {d : DecompDataZ ξ} {A B : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ}
  {vl nℓ J prv nxt g : ℤ × ℤ}
variable (P : PinTower d A B kk vl nℓ J prv nxt g)
include P

theorem Sfin : (↑d.Sphi : Set (ℤ × ℤ)).Finite := d.Sphi.finite_toSet
theorem Sarea : PosArea (↑d.Sphi : Set (ℤ × ℤ)) := Nivat.AhatMono.posArea_Sphi d.toDecompData
theorem Slc : IsLatticeConvexRegion (↑d.Sphi : Set (ℤ × ℤ)) :=
  Nivat.ChainAsm.isLatticeConvexRegion_coe d.Sphi_conv

theorem hlc (i : ℕ) : IsLatticeConvexRegion (hatOf A kk vl i) := (P.henv i).1.1
theorem harea (i : ℕ) : PosArea (hatOf A kk vl i) :=
  Nivat.AhatMono.posArea_of_enveloped P.Sfin P.Sarea (P.henv i)
theorem hne (i : ℕ) : (hatOf A kk vl i).Nonempty := by
  obtain ⟨a, ha, -⟩ := P.harea i; exact ⟨a, ha⟩
theorem hE (i : ℕ) : E (hatOf A kk vl i) = E (↑d.Sphi : Set (ℤ × ℤ)) :=
  Enveloped.E_eq (finite_E_of_finite P.Sfin) (P.henv i)

theorem hJi (i : ℕ) : J ∈ E (hatOf A kk vl i) := by rw [P.hE]; exact P.hJ
theorem hprvi (i : ℕ) : prv ∈ E (hatOf A kk vl i) := by rw [P.hE]; exact P.hprv
theorem hnxti (i : ℕ) : nxt ∈ E (hatOf A kk vl i) := by rw [P.hE]; exact P.hnxt

/-- The pinned end is the start of the `nxt`-face. -/
theorem faceStart_nxt (i : ℕ) : faceStart (hatOf A kk vl i) nxt = g := by
  have := adjacent_shared_vertex (P.hfin i) (P.hlc i) (P.hJi i) (P.hnxti i) P.hdn
    (by rw [P.hE]; exact P.hadjN)
  rw [P.hpin i] at this; exact this.symm

theorem g_mem_face (i : ℕ) : g ∈ face (hatOf A kk vl i) J := by
  have := mem_face_of_pinned (P.hlc i) (P.hfin i) (P.hJi i) (P.hpin i) 0 (Nat.zero_le _)
  simpa using this

theorem g_mem_nxt (i : ℕ) : g ∈ face (hatOf A kk vl i) nxt := by
  rw [← P.faceStart_nxt i]; exact faceStart_mem (P.hfin i) (P.hnxti i)

theorem s0_mem_prv (i : ℕ) : faceStart (hatOf A kk vl i) J ∈ face (hatOf A kk vl i) prv := by
  rw [← adjacent_shared_vertex (P.hfin i) (P.hlc i) (P.hprvi i) (P.hJi i) P.hdp
    (by rw [P.hE]; exact P.hadjP)]
  exact faceEnd_mem (P.hlc i) (P.hfin i) (P.hprvi i)

theorem svJ (i : ℕ) : suppVal (hatOf A kk vl i) J = dot J g := suppVal_eq (P.g_mem_face i)

theorem faceLen_mono {i j : ℕ} (hij : i ≤ j) :
    faceLen (hatOf A kk vl i) J ≤ faceLen (hatOf A kk vl j) J :=
  faceLen_mono_of_pinned (P.hlc i) (P.hfin i) (P.hJi i) (P.hlc j) (P.hfin j) (P.hJi j)
    (P.hmono i j hij) (P.hpin i) (P.hpin j) (fun z hz => by
      have := (P.g_mem_face j).2 z hz; exact this)

theorem eventually_long (Λ : ℕ) : ∃ N, ∀ i, N ≤ i → Λ ≤ faceLen (hatOf A kk vl i) J := by
  obtain ⟨N, hN⟩ := P.hunb Λ
  exact ⟨N, fun i hi => le_trans hN (P.faceLen_mono hi)⟩

end PinTower

end Nivat.Hole1QShell

/-! ## §18. The fan constant `c`, the length threshold `Λ`, and `PushData` at every long level -/

namespace Nivat.Hole1QShell

open Nivat Nivat.LE2 Nivat.PolyChain Nivat.Colle35

theorem encard_face_eq_faceLen {T : Set (ℤ × ℤ)} {ν : ℤ × ℤ} (hlc : IsLatticeConvexRegion T)
    (hfin : T.Finite) (hν : ν ∈ E T) :
    (face T ν).encard = (faceLen T ν : ℕ∞) + 1 := by
  rw [face_eq_segment hlc hfin hν]
  have hinj : Set.InjOn (fun t : ℕ => faceStart T ν + (t : ℤ) • dir ν)
      ↑(Finset.range (faceLen T ν + 1)) := by
    intro a _ b _ h
    exact_mod_cast smul_left_injective ℤ (prim_dir_of_prim hν.1).ne_zero (add_left_cancel h)
  have : {z | ∃ t : ℕ, t ≤ faceLen T ν ∧ z = faceStart T ν + (t : ℤ) • dir ν} =
      (fun t : ℕ => faceStart T ν + (t : ℤ) • dir ν) '' ↑(Finset.range (faceLen T ν + 1)) := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_image, Finset.coe_range, Set.mem_Iio]
    constructor
    · rintro ⟨t, ht, rfl⟩; exact ⟨t, by omega, rfl⟩
    · rintro ⟨t, ht, rfl⟩; exact ⟨t, by omega, rfl⟩
  rw [this, hinj.encard_image, Set.encard_coe_eq_coe_finsetCard, Finset.card_range]
  push_cast; rfl

namespace PinTower

variable {ξ : Config ℤ} {d : DecompDataZ ξ} {A B : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ}
  {vl nℓ J prv nxt g : ℤ × ℤ}
variable (P : PinTower d A B kk vl nℓ J prv nxt g)
include P

theorem exists_c : ∃ c : ℤ, det prv J • dir nxt + det J nxt • dir prv = c • dir J := by
  have hJ0 : J ≠ 0 := P.hJ.1.ne_zero
  have hd : dot J (det prv J • dir nxt + det J nxt • dir prv) = 0 := by
    rw [dot_add, dot_smul_r, dot_smul_r, dot_dir_eq_det, dot_dir_eq_det, det_swap nxt J,
      det_swap prv J]; ring
  have hdirJ : dot J (dir J) = 0 := by rw [dot_dir_eq_det, det_self]
  have hdet := det_eq_zero_of_dot_eq_zero hJ0 hdirJ hd
  obtain ⟨a, ha⟩ := exists_smul_of_det_eq_zero (prim_dir_of_prim P.hJ.1) hdet
  exact ⟨a, by rw [ha]; rfl⟩

/-- All size requirements hold beyond one threshold. -/
theorem exists_Λ (c : ℤ) : ∃ Λ : ℕ, ∀ len : ℕ, Λ ≤ len →
    c + 1 ≤ (len : ℤ) ∧
    faceLen (↑d.Sphi : Set (ℤ × ℤ)) J ≤ ((len : ℤ) - c).toNat ∧
    faceLen (↑d.Sphi : Set (ℤ × ℤ)) J ≤ len ∧
    (∀ m ∈ E (↑d.Sphi : Set (ℤ × ℤ)), 0 < det J m →
      det J nxt * det prv m < (len : ℤ) * det J m) ∧
    (∀ m ∈ E (↑d.Sphi : Set (ℤ × ℤ)), det J m < 0 →
      det prv J * (-det nxt m) < (len : ℤ) * (-det J m)) := by
  have hEfin : (E (↑d.Sphi : Set (ℤ × ℤ))).Finite := finite_E_of_finite P.Sfin
  obtain ⟨K, hK⟩ := (hEfin.image
    (fun m => |det J nxt * det prv m| + |det prv J * det nxt m|)).bddAbove
  set lenS := faceLen (↑d.Sphi : Set (ℤ × ℤ)) J
  refine ⟨(|c| + lenS + |K| + 1).toNat, fun len hlen => ?_⟩
  have hlen' : |c| + lenS + |K| + 1 ≤ (len : ℤ) := by
    have := Int.self_le_toNat (|c| + (lenS : ℤ) + |K| + 1)
    exact le_trans this (by exact_mod_cast hlen)
  have hcabs := le_abs_self c
  have hKabs := le_abs_self K
  have bnd : ∀ m ∈ E (↑d.Sphi : Set (ℤ × ℤ)),
      |det J nxt * det prv m| + |det prv J * det nxt m| ≤ K :=
    fun m hm => hK ⟨m, hm, rfl⟩
  have hc0 := abs_nonneg c
  have hK0 := abs_nonneg K
  refine ⟨by omega, ?_, ?_, ?_, ?_⟩
  · have : (lenS : ℤ) ≤ (len : ℤ) - c := by linarith [abs_nonneg K]
    have h2 : ((lenS : ℤ)) ≤ (((len : ℤ) - c).toNat : ℤ) :=
      le_trans this (Int.self_le_toNat _)
    exact_mod_cast h2
  · have : (lenS : ℤ) ≤ (len : ℤ) := by linarith [abs_nonneg c, abs_nonneg K]
    exact_mod_cast this
  · intro m hm hpos
    have h1 := bnd m hm
    have h2 := le_abs_self (det J nxt * det prv m)
    have h3 := abs_nonneg (det prv J * det nxt m)
    have hlenpos : (0 : ℤ) ≤ len := by positivity
    nlinarith [abs_nonneg c]
  · intro m hm hneg
    have h1 := bnd m hm
    have h2 := neg_abs_le (det prv J * det nxt m)
    have h3 := abs_nonneg (det J nxt * det prv m)
    have hlenpos : (0 : ℤ) ≤ len := by positivity
    nlinarith [abs_nonneg c]

/-- `PushData` at a long level. -/
theorem pushData {c : ℤ} (hc : det prv J • dir nxt + det J nxt • dir prv = c • dir J)
    (i : ℕ) (hk : c + 1 ≤ (faceLen (hatOf A kk vl i) J : ℤ))
    (hlenS : faceLen (↑d.Sphi : Set (ℤ × ℤ)) J ≤ (((faceLen (hatOf A kk vl i) J : ℤ) - c).toNat))
    (hbig1 : ∀ m ∈ E (↑d.Sphi : Set (ℤ × ℤ)), 0 < det J m →
      det J nxt * det prv m < (faceLen (hatOf A kk vl i) J : ℤ) * det J m)
    (hbig2 : ∀ m ∈ E (↑d.Sphi : Set (ℤ × ℤ)), det J m < 0 →
      det prv J * (-det nxt m) < (faceLen (hatOf A kk vl i) J : ℤ) * (-det J m)) :
    PushData (↑d.Sphi : Set (ℤ × ℤ)) (hatOf A kk vl i) J prv nxt
      (faceStart (hatOf A kk vl i) J + det J nxt • dir prv) (dir J)
      (((faceLen (hatOf A kk vl i) J : ℤ) - c).toNat) (det prv J * det J nxt) := by
  have hc' : det prv J • dir nxt + det J nxt • dir prv = c • dir J := hc
  refine pushData_of_fan (P.hfin i) (P.hne i) (P.harea i) (P.hlc i) (P.henv i) (P.hJi i)
    (P.hprvi i) (P.hnxti i) P.hdp P.hdn (by rw [P.hE]; exact P.hadjP)
    (by rw [P.hE]; exact P.hadjN) hc' hk ?_ (by rw [P.hE]; exact hbig1)
    (by rw [P.hE]; exact hbig2)
  rw [encard_face_eq_faceLen P.Slc P.Sfin P.hJ]
  have h : ((faceLen (↑d.Sphi : Set (ℤ × ℤ)) J : ℕ) : ℕ∞) ≤
      ((((faceLen (hatOf A kk vl i) J : ℤ) - c).toNat : ℕ) : ℕ∞) := by exact_mod_cast hlenS
  exact add_le_add h le_rfl

end PinTower

end Nivat.Hole1QShell

/-! ## §19. Corner fits, the far corner `q`, and the window lemma -/

namespace Nivat.Hole1QShell

open Nivat Nivat.LE2 Nivat.PolyChain Nivat.Colle35

theorem aprime_eq_faceStart {S : Finset (ℤ × ℤ)} {J : ℤ × ℤ}
    (F : Nivat.Colle35.FaceBlock S (-J) (-(dir J))) (hJ : J ∈ E (↑S : Set (ℤ × ℤ))) :
    F.a' = faceStart (↑S : Set (ℤ × ℤ)) J := by
  have hmem : F.a' ∈ face (↑S : Set (ℤ × ℤ)) J := by
    have := Nivat.FanEndpoint.faceBlock_a_mem_face F.reverse
    simpa using this
  have hpar : ∀ b ∈ face (↑S : Set (ℤ × ℤ)) J, ∃ j : ℕ, b = F.a' + (j : ℤ) • dir J := by
    intro b hb
    obtain ⟨j, hj⟩ := Nivat.FanEndpoint.faceBlock_faceparam F.reverse b hb
    exact ⟨j, by simpa using hj⟩
  have hfin : (↑S : Set (ℤ × ℤ)).Finite := S.finite_toSet
  obtain ⟨j, hj⟩ := hpar _ (faceStart_mem hfin hJ)
  have hmin := faceStart_min hfin hJ _ hmem
  rw [hj, dot_row] at hmin
  have hpos := dot_dir_pos hJ.1
  have : (j : ℤ) = 0 := by nlinarith [(Nat.cast_nonneg j : (0 : ℤ) ≤ j)]
  rw [hj, this, zero_smul, add_zero]

namespace PinTower

variable {ξ : Config ℤ} {d : DecompDataZ ξ} {A B : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ}
  {vl nℓ J prv nxt g : ℤ × ℤ}
variable (P : PinTower d A B kk vl nℓ J prv nxt g)
include P

theorem faceStart_eq_pin (i : ℕ) :
    faceStart (hatOf A kk vl i) J = g - (faceLen (hatOf A kk vl i) J : ℤ) • dir J :=
  faceStart_of_pinned (P.hpin i)

/-- The far end of every long level's new row is the same point `q = g - D₁ • dir nxt`. -/
theorem row_end {c : ℤ} (hc : det prv J • dir nxt + det J nxt • dir prv = c • dir J) (i : ℕ)
    (hk : c + 1 ≤ (faceLen (hatOf A kk vl i) J : ℤ)) :
    faceStart (hatOf A kk vl i) J + det J nxt • dir prv +
      ((((faceLen (hatOf A kk vl i) J : ℤ) - c).toNat : ℕ) : ℤ) • dir J =
      g - det prv J • dir nxt := by
  rw [Int.toNat_of_nonneg (by omega), P.faceStart_eq_pin i, sub_smul]
  have : det J nxt • dir prv = c • dir J - det prv J • dir nxt := by rw [← hc]; abel
  rw [this]; abel

theorem faceStart_S_nxt :
    faceStart (↑d.Sphi : Set (ℤ × ℤ)) nxt =
      faceStart (↑d.Sphi : Set (ℤ × ℤ)) J + (faceLen (↑d.Sphi : Set (ℤ × ℤ)) J : ℤ) • dir J :=
  (adjacent_shared_vertex P.Sfin P.Slc P.hJ P.hnxt P.hdn P.hadjN).symm

theorem hd1 : dot prv (dir J) < 0 := by
  rw [dot_dir_eq_det, det_swap]; linarith [P.hdp]
theorem hd2 : 0 < dot nxt (dir J) := by rw [dot_dir_eq_det]; exact P.hdn

/-- **The window lemma.**  For `i₀ ≤ i` two long levels, every point of the level-`i` push shell
outside `Â_i ∪ Y_{i₀}` carries a full `𝒮_φ`-window anchored at `F.a'`. -/
theorem window {c : ℤ} (hc : det prv J • dir nxt + det J nxt • dir prv = c • dir J)
    (F : Nivat.Colle35.FaceBlock d.Sphi (-J) (-(dir J))) {i₀ i : ℕ}
    (D : PushData (↑d.Sphi : Set (ℤ × ℤ)) (hatOf A kk vl i) J prv nxt
      (faceStart (hatOf A kk vl i) J + det J nxt • dir prv) (dir J)
      (((faceLen (hatOf A kk vl i) J : ℤ) - c).toNat) (det prv J * det J nxt))
    (D₀ : PushData (↑d.Sphi : Set (ℤ × ℤ)) (hatOf A kk vl i₀) J prv nxt
      (faceStart (hatOf A kk vl i₀) J + det J nxt • dir prv) (dir J)
      (((faceLen (hatOf A kk vl i₀) J : ℤ) - c).toNat) (det prv J * det J nxt))
    (hk : c + 1 ≤ (faceLen (hatOf A kk vl i) J : ℤ))
    (hk₀ : c + 1 ≤ (faceLen (hatOf A kk vl i₀) J : ℤ))
    (hS₀ : faceLen (↑d.Sphi : Set (ℤ × ℤ)) J ≤ faceLen (hatOf A kk vl i₀) J)
    (hSk₀ : faceLen (↑d.Sphi : Set (ℤ × ℤ)) J ≤ (((faceLen (hatOf A kk vl i₀) J : ℤ) - c).toNat)) :
    ∀ z ∈ pushShell (hatOf A kk vl i) (faceStart (hatOf A kk vl i) J + det J nxt • dir prv)
        (dir J) (((faceLen (hatOf A kk vl i) J : ℤ) - c).toNat),
      z ∉ hatOf A kk vl i ∪ pushShell (hatOf A kk vl i₀)
        (faceStart (hatOf A kk vl i₀) J + det J nxt • dir prv) (dir J)
        (((faceLen (hatOf A kk vl i₀) J : ℤ) - c).toNat) →
      ∀ b ∈ d.Sphi, z + (b - F.a') ∈ pushShell (hatOf A kk vl i)
        (faceStart (hatOf A kk vl i) J + det J nxt • dir prv) (dir J)
        (((faceLen (hatOf A kk vl i) J : ℤ) - c).toNat) := by
  intro z hz hzX b hb
  -- abbreviations
  set T := hatOf A kk vl i with hTdef
  set T₀ := hatOf A kk vl i₀ with hT₀def
  set s0 := faceStart T J with hs0def
  set p := s0 + det J nxt • dir prv with hpdef
  set k := ((faceLen T J : ℤ) - c).toNat with hkdef
  set Y := pushShell T p (dir J) k with hYdef
  set p₀ := faceStart T₀ J + det J nxt • dir prv with hp₀def
  set k₀ := ((faceLen T₀ J : ℤ) - c).toNat with hk₀def
  set Y₀ := pushShell T₀ p₀ (dir J) k₀ with hY₀def
  set lenS := faceLen (↑d.Sphi : Set (ℤ × ℤ)) J with hlenSdef
  set q := g - det prv J • dir nxt with hqdef
  set L := det prv J * det J nxt with hLdef
  set s := dot J g with hsdef
  have hL : 0 < L := mul_pos P.hdp P.hdn
  have hJ0 : J ≠ 0 := P.hJ.1.ne_zero
  have hdirJp : Prim (dir J) := prim_dir_of_prim P.hJ.1
  have hdJJ : dot J (dir J) = 0 := by rw [dot_dir_eq_det, det_self]
  -- row ends
  have hq : p + (k : ℤ) • dir J = q := P.row_end hc i hk
  have hq₀ : p₀ + (k₀ : ℤ) • dir J = q := P.row_end hc i₀ hk₀
  -- the shells
  have hYfin : Y.Finite := D.pushShell_finite
  have hYenv : EnvOf (↑d.Sphi : Set (ℤ × ℤ)) Y := D.enveloped
  have hYlc : IsLatticeConvexRegion Y := isLatticeConvexRegion_latHull D.Y_finite
  have hYarea : PosArea Y := Nivat.AhatMono.posArea_of_enveloped P.Sfin P.Sarea hYenv
  have hYne : Y.Nonempty := by obtain ⟨a, ha, -⟩ := hYarea; exact ⟨a, ha⟩
  have hY₀fin : Y₀.Finite := D₀.pushShell_finite
  have hY₀env : EnvOf (↑d.Sphi : Set (ℤ × ℤ)) Y₀ := D₀.enveloped
  have hY₀lc : IsLatticeConvexRegion Y₀ := isLatticeConvexRegion_latHull D₀.Y_finite
  have hY₀area : PosArea Y₀ := Nivat.AhatMono.posArea_of_enveloped P.Sfin P.Sarea hY₀env
  have hY₀ne : Y₀.Nonempty := by obtain ⟨a, ha, -⟩ := hY₀area; exact ⟨a, ha⟩
  have hEY : E Y = E T := D.E_pushShell
  -- levels
  have hsvJ : suppVal T J = s := P.svJ i
  have hs0J : dot J s0 = s := by
    rw [← hsvJ]; exact (suppVal_eq (faceStart_mem (P.hfin i) (P.hJi i))).symm
  have hpJ : dot J p = s + L := by rw [D.hlev, hsvJ]
  have hqJ : dot J q = s + L := by rw [← hq, dot_row, hdJJ, hpJ]; ring
  have hshiftJ : ∀ x : ℤ × ℤ, ∀ t : ℤ, dot J (x - t • dir J) = dot J x := by
    intro x t; rw [dot_sub, dot_smul_r, hdJJ]; ring
  have hshiftN : ∀ x : ℤ × ℤ, ∀ t : ℤ, dot nxt (x - t • dir J) = dot nxt x - t * dot nxt (dir J) := by
    intro x t; rw [dot_sub, dot_smul_r]
  have hnq : dot nxt q = dot nxt g := by
    rw [hqdef, dot_sub, dot_smul_r, dot_dir_eq_det, det_self]; ring
  have hpp : dot prv p = dot prv s0 := by
    rw [hpdef, dot_add, dot_smul_r, dot_dir_eq_det, det_self]; ring
  -- the anchor `F.a'`
  have ha' : F.a' = faceStart (↑d.Sphi : Set (ℤ × ℤ)) J := aprime_eq_faceStart F P.hJ
  -- corner fits (all shifted by `b - F.a'`)
  have C1 : s0 + (b - F.a') ∈ Y := by
    rw [ha']
    exact D.subset_pushShell
      (Nivat.Hole1QShell.sphi_shift_subset' d (P.henv i) (P.hfin i) P.hJ b hb)
  have hYstart : faceStart Y J = p :=
    D.faceStart_eq rfl hdirJp P.hd1 P.hd2
  have C2 : p + (b - F.a') ∈ Y := by
    rw [ha', ← hYstart]
    exact Nivat.Hole1QShell.sphi_shift_subset' d hYenv hYfin P.hJ b hb
  have C3 : (g - (lenS : ℤ) • dir J) + (b - F.a') ∈ Y := by
    have h := Nivat.Hole1QShell.sphi_shift_subset' d (P.henv i) (P.hfin i) P.hnxt b hb
    rw [P.faceStart_nxt i, P.faceStart_S_nxt, ← ha'] at h
    have e : g + (b - (F.a' + (lenS : ℤ) • dir J)) = (g - (lenS : ℤ) • dir J) + (b - F.a') := by
      abel
    rw [e] at h
    exact D.subset_pushShell h
  have hYnxt : faceStart Y nxt = q := by
    rw [D.faceStart_m2 rfl hdirJp P.hd1 P.hd2 P.hdn (by rw [P.hE]; exact P.hadjN), hq]
  have C4 : (q - (lenS : ℤ) • dir J) + (b - F.a') ∈ Y := by
    have h := Nivat.Hole1QShell.sphi_shift_subset' d hYenv hYfin P.hnxt b hb
    rw [hYnxt, P.faceStart_S_nxt, ← ha'] at h
    have e : q + (b - (F.a' + (lenS : ℤ) • dir J)) = (q - (lenS : ℤ) • dir J) + (b - F.a') := by
      abel
    rw [e] at h; exact h
  -- facts about `z`
  obtain ⟨hzle, hzlev⟩ := D.pushShell_le z hz
  rw [hsvJ] at hzlev
  have hzT : z ∉ T := fun h => hzX (Or.inl h)
  have hzY₀ : z ∉ Y₀ := fun h => hzX (Or.inr h)
  have hz1 : s ≤ dot J z := by
    by_contra hlt; push_neg at hlt
    exact hzT (mem_of_dot_le_suppVal (P.hfin i) (P.hne i) (P.harea i) (P.hlc i) (fun m hm => by
      by_cases hmJ : m = J
      · rw [hmJ, hsvJ]; exact hlt.le
      · exact hzle m hm hmJ))
  have hzprv : dot prv z ≤ dot prv s0 := by
    have hprvJ : prv ≠ J := fun h => by
      have := P.hdp; rw [h, det_self] at this; exact lt_irrefl 0 this
    have := hzle prv (P.hprvi i) hprvJ
    rwa [suppVal_eq (P.s0_mem_prv i)] at this
  have hznxt : dot nxt z ≤ dot nxt g := by
    have hnxtJ : nxt ≠ J := fun h => by
      have := P.hdn; rw [h, det_self] at this; exact lt_irrefl 0 this
    have := hzle nxt (P.hnxti i) hnxtJ
    rwa [suppVal_eq (P.g_mem_nxt i)] at this
  -- the two cases
  by_cases hnear : dot nxt (g - (lenS : ℤ) • dir J) < dot nxt z
  · -- seed: `z` lies in `Y₀`
    exfalso
    apply hzY₀
    have v0 : (g - (lenS : ℤ) • dir J) + 0 ∈ Y₀ := by
      rw [add_zero]
      exact D₀.subset_pushShell
        (mem_face_of_pinned (P.hlc i₀) (P.hfin i₀) (P.hJi i₀) (P.hpin i₀) lenS hS₀).1
    have v1 : (q - (lenS : ℤ) • dir J) + 0 ∈ Y₀ := by
      have e : q - (lenS : ℤ) • dir J = p₀ + ((k₀ - lenS : ℕ) : ℤ) • dir J := by
        rw [← hq₀]; push_cast [hSk₀]; rw [sub_smul]; abel
      rw [e, add_zero]
      exact subset_latHull _ (Or.inr ⟨k₀ - lenS, Nat.sub_le _ _, rfl⟩)
    have v2 : g + 0 ∈ Y₀ := by
      rw [add_zero]; exact D₀.subset_pushShell (P.g_mem_face i₀).1
    have v3 : q + 0 ∈ Y₀ := by
      rw [← hq₀, add_zero]; exact subset_latHull _ (Or.inr (right_mem_rowW _ _ _))
    have hu' : dot (-nxt) (g - (lenS : ℤ) • dir J) = dot (-nxt) (q - (lenS : ℤ) • dir J) := by
      rw [dot_neg_left, dot_neg_left, hshiftN, hshiftN, hnq]
    have hud' : dot (-nxt) (dir J) < 0 := by rw [dot_neg_left]; linarith [P.hd2]
    have hzu' : dot (-nxt) z ≤ dot (-nxt) (g - (lenS : ℤ) • dir J) := by
      rw [dot_neg_left, dot_neg_left]; linarith
    have hw := quad_mem hY₀fin hY₀ne hY₀area hY₀lc hL hJ0 (by rw [hshiftJ]) rfl
      (by rw [hshiftJ, hqJ]) hqJ hu' hnq.symm hud' P.hd2 hz1 hzlev hzu' hznxt v0 v1 v2 v3
    simpa using hw
  · -- window: four corner fits and the quadrilateral
    push_neg at hnear
    exact quad_mem hYfin hYne hYarea hYlc hL hJ0 (u := prv) (v := nxt)
      (a0 := s0) (a1 := p) (b0 := g - (lenS : ℤ) • dir J) (b1 := q - (lenS : ℤ) • dir J)
      hs0J (by rw [hshiftJ]) hpJ (by rw [hshiftJ, hqJ]) hpp.symm
      (by rw [hshiftN, hshiftN, hnq]) P.hd1 P.hd2 hz1 hzlev hzprv hnear C1 C2 C3 C4

end PinTower

end Nivat.Hole1QShell

/-! ## §20. The shell family and its seven `ChainData` obligations -/

namespace Nivat.Hole1QShell

open Nivat Nivat.LE2 Nivat.PolyChain Nivat.Colle35

namespace PinTower

variable {ξ : Config ℤ} {d : DecompDataZ ξ} {A B : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ}
  {vl nℓ J prv nxt g : ℤ × ℤ}
variable (P : PinTower d A B kk vl nℓ J prv nxt g)
include P

/-- `reachSet Â_∞ vJ1` is lattice-convex and closed under `+vJ1`, `+vJ` (from `hole1-bottom.lean`). -/
theorem reach_facts :
    IsLatticeConvexRegion (MaxEnv.reachSet (⋃ i, hatOf A kk vl i) (-(dir nxt))) ∧
    (∀ z ∈ MaxEnv.reachSet (⋃ i, hatOf A kk vl i) (-(dir nxt)),
      z + (-(dir nxt)) ∈ MaxEnv.reachSet (⋃ i, hatOf A kk vl i) (-(dir nxt))) ∧
    (∀ z ∈ MaxEnv.reachSet (⋃ i, hatOf A kk vl i) (-(dir nxt)),
      z + (-(dir J)) ∈ MaxEnv.reachSet (⋃ i, hatOf A kk vl i) (-(dir nxt))) := by
  set Ainf := ⋃ i, hatOf A kk vl i
  have hgA : g ∈ Ainf := by
    have := P.hray 0; rw [Nat.cast_zero, zero_smul, sub_zero] at this; exact this
  have hrayV : ∀ k : ℕ, g + (k : ℤ) • (-(dir J)) ∈ Ainf := by
    intro k; have := P.hray k; rwa [smul_neg, ← sub_eq_add_neg]
  have hrecJ : ∀ z ∈ Ainf, z + (-(dir J)) ∈ Ainf := Nivat.Colle35.rec_of_ray P.hconv hrayV
  have hprev : g - (-(dir nxt)) ∈ Ainf := by
    have hseg := face_eq_segment (P.hlc 0) (P.hfin 0) (P.hnxti 0)
    have hlen := one_le_faceLen (P.hfin 0) (P.hnxti 0)
    have hmem : faceStart (hatOf A kk vl 0) nxt + ((1 : ℕ) : ℤ) • dir nxt
        ∈ face (hatOf A kk vl 0) nxt := by rw [hseg]; exact ⟨1, hlen, rfl⟩
    rw [P.faceStart_nxt 0] at hmem
    have : g - (-(dir nxt)) = g + ((1 : ℕ) : ℤ) • dir nxt := by simp [sub_eq_add_neg]
    rw [this]; exact Set.mem_iUnion.mpr ⟨0, (face_subset _ _) hmem⟩
  have hdirJne : dir J ≠ 0 := (prim_dir_of_prim P.hJ.1).ne_zero
  have hnxtne : nxt ≠ 0 := P.hnxt.1.ne_zero
  have hnJvJ : dot (-J) (-(dir J)) = 0 := by simp only [dot, dir, Prod.fst_neg, Prod.snd_neg]; ring
  have hnJv : dot (-J) (-(dir nxt)) < 0 := by
    have : dot (-J) (-(dir nxt)) = -det J nxt := by
      simp only [dot, dir, det, Prod.fst_neg, Prod.snd_neg]; ring
    rw [this]; linarith [P.hdn]
  have hAhalf : ∀ z ∈ Ainf, dot (-J) g ≤ dot (-J) z := fun z hz => Set.iUnion_subset P.hhp hz
  have hzero : MaxEnv.reachSet Ainf (-(dir nxt)) ∩ Nivat.CK224.halfPlaneGE (-J) (dot (-J) g) ⊆ Ainf := by
    rintro z ⟨⟨a, ha, t, rfl⟩, hlev⟩
    exact P.hswept a ha t hlev
  have e : Nivat.Colle35.EdgeJ1Data Ainf (-(dir nxt)) (-J) (dot (-J) g) :=
    { a₀ := g
      a₀_mem := hgA
      a₀_on := rfl
      prev_mem := hprev
      nJ1 := -nxt
      dot_nJ1_v := by simp only [dot, dir, Prod.fst_neg, Prod.snd_neg]; ring
      nJ1_ne := neg_ne_zero.mpr hnxtne
      support := fun z hz => by
        rw [dot_neg_left, dot_neg_left]; exact neg_le_neg (P.hsupp z hz) }
  refine ⟨e.isLatticeConvexRegion_reachSet P.hconv hAhalf hzero hrecJ hnJvJ hnJv
    (neg_ne_zero.mpr hdirJne), ?_, ?_⟩
  · rintro z ⟨a, ha, t, rfl⟩
    exact ⟨a, ha, t + 1, by rw [Nat.cast_succ, add_smul, one_smul, add_assoc]⟩
  · rintro z ⟨a, ha, t, rfl⟩
    exact ⟨a + (-(dir J)), hrecJ a ha, t, by rw [add_right_comm]⟩

/-- A point of a level's push shell off the level itself lies strictly beyond the `J`-line. -/
theorem beyond_of_not_mem {c : ℤ} {i : ℕ}
    (D : PushData (↑d.Sphi : Set (ℤ × ℤ)) (hatOf A kk vl i) J prv nxt
      (faceStart (hatOf A kk vl i) J + det J nxt • dir prv) (dir J)
      (((faceLen (hatOf A kk vl i) J : ℤ) - c).toNat) (det prv J * det J nxt))
    {z : ℤ × ℤ} (hz : z ∈ pushShell (hatOf A kk vl i)
      (faceStart (hatOf A kk vl i) J + det J nxt • dir prv) (dir J)
      (((faceLen (hatOf A kk vl i) J : ℤ) - c).toNat))
    (hzT : z ∉ hatOf A kk vl i) : dot J g < dot J z := by
  obtain ⟨hzle, -⟩ := D.pushShell_le z hz
  by_contra hlt; push_neg at hlt
  exact hzT (mem_of_dot_le_suppVal (P.hfin i) (P.hne i) (P.harea i) (P.hlc i) (fun m hm => by
    by_cases hmJ : m = J
    · rw [hmJ, P.svJ i]; exact hlt
    · exact hzle m hm hmJ))

theorem shell_pack (F : Nivat.Colle35.FaceBlock d.Sphi (-J) (-(dir J))) :
    ∃ (sh : ℕ → ℕ → Set (ℤ × ℤ)) (I₀ : ℕ),
      (∀ i ε, (sh i ε).Finite) ∧
      (∀ i ε, hatOf A kk vl i ⊆ sh i ε) ∧
      (∀ i ε, sh i ε ⊆ MaxEnv.shell (⋃ i, hatOf A kk vl i) (-(dir nxt)) (-J) (dot (-J) g) ε) ∧
      (∀ ε i₀ : ℕ, 0 < ε → (∀ i, i₀ ≤ i → EnvOf (↑d.Sphi : Set (ℤ × ℤ)) (sh i ε)) →
        ∀ i, max i₀ I₀ ≤ i → sh i ε ⊆ {z | z + (kk i : ℤ) • vl ∈ Colle35.halfStrip (B i) vl}) ∧
      (∀ ε i₀ : ℕ, 0 < ε → (∀ i, i₀ ≤ i → EnvOf (↑d.Sphi : Set (ℤ × ℤ)) (sh i ε)) →
        ∀ i, max i₀ I₀ ≤ i → ¬ (sh i ε ⊆ hatOf A kk vl i)) ∧
      (∃ ε i₀, 0 < ε ∧ ∀ i, i₀ ≤ i → EnvOf (↑d.Sphi : Set (ℤ × ℤ)) (sh i ε)) ∧
      (∀ ε i₀ : ℕ, 0 < ε → (∀ i, i₀ ≤ i → EnvOf (↑d.Sphi : Set (ℤ × ℤ)) (sh i ε)) →
        ∀ i, max i₀ I₀ ≤ i →
        sh i ε ⊆ {z | Colle37.GenClosure d.Sphi (hatOf A kk vl i ∪ sh i₀ ε) z}) := by
  classical
  obtain ⟨c, hc⟩ := P.exists_c
  obtain ⟨Λ, hΛ⟩ := P.exists_Λ c
  obtain ⟨N, hN⟩ := P.eventually_long Λ
  set L := det prv J * det J nxt with hLdef
  have hL : 0 < L := mul_pos P.hdp P.hdn
  -- the long-level data
  have hlong : ∀ i, N ≤ i → _ := fun i hi => hΛ _ (hN i hi)
  let Y : ℕ → Set (ℤ × ℤ) := fun i => pushShell (hatOf A kk vl i)
    (faceStart (hatOf A kk vl i) J + det J nxt • dir prv) (dir J)
    (((faceLen (hatOf A kk vl i) J : ℤ) - c).toNat)
  let Fil : ℕ → Set (ℤ × ℤ) := fun i =>
    hatOf A kk vl i ∪ {faceStart (hatOf A kk vl i) J - (2 : ℤ) • dir J}
  have hD : ∀ i, N ≤ i → PushData (↑d.Sphi : Set (ℤ × ℤ)) (hatOf A kk vl i) J prv nxt
      (faceStart (hatOf A kk vl i) J + det J nxt • dir prv) (dir J)
      (((faceLen (hatOf A kk vl i) J : ℤ) - c).toNat) L := fun i hi =>
    P.pushData hc i (hlong i hi).1 (hlong i hi).2.1 (hlong i hi).2.2.2.1 (hlong i hi).2.2.2.2
  let sh : ℕ → ℕ → Set (ℤ × ℤ) := fun i ε => if L ≤ (ε : ℤ) ∧ N ≤ i then Y i else Fil i
  have sh_pos : ∀ (i ε : ℕ), L ≤ (ε : ℤ) → N ≤ i → sh i ε = Y i := fun i ε h1 h2 => if_pos ⟨h1, h2⟩
  have sh_neg : ∀ (i ε : ℕ), ¬ (L ≤ (ε : ℤ) ∧ N ≤ i) → sh i ε = Fil i := fun i ε h => if_neg h
  -- the guard forces the push branch from `i₀` on
  have hguard : ∀ ε i₀ : ℕ, (∀ i, i₀ ≤ i → EnvOf (↑d.Sphi : Set (ℤ × ℤ)) (sh i ε)) →
      L ≤ (ε : ℤ) ∧ N ≤ i₀ := by
    intro ε i₀ hG
    by_contra hcond
    have h := hG i₀ le_rfl
    rw [sh_neg i₀ ε hcond] at h
    exact not_envOf_filler (P.hfin i₀) (P.hJi i₀) h
  obtain ⟨hRlc, hR1, hR2⟩ := P.reach_facts
  refine ⟨sh, N, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- finite
    intro i ε
    by_cases h : L ≤ (ε : ℤ) ∧ N ≤ i
    · rw [sh_pos i ε h.1 h.2]; exact (hD i h.2).pushShell_finite
    · rw [sh_neg i ε h]; exact (P.hfin i).union (Set.finite_singleton _)
  · -- subShell
    intro i ε
    by_cases h : L ≤ (ε : ℤ) ∧ N ≤ i
    · rw [sh_pos i ε h.1 h.2]; exact (hD i h.2).subset_pushShell
    · rw [sh_neg i ε h]; exact Set.subset_union_left
  · -- shellSubInf
    intro i ε z hz
    have hAinf : ∀ x ∈ hatOf A kk vl i, x ∈ ⋃ j, hatOf A kk vl j :=
      fun x hx => Set.mem_iUnion.mpr ⟨i, hx⟩
    have hbase : ∀ x ∈ ⋃ j, hatOf A kk vl j,
        x ∈ MaxEnv.shell (⋃ j, hatOf A kk vl j) (-(dir nxt)) (-J) (dot (-J) g) ε := by
      intro x hx
      refine ⟨x, hx, 0, by simp, ?_⟩
      have := Set.iUnion_subset P.hhp hx
      show dot (-J) g - (ε : ℤ) ≤ dot (-J) x
      have h2 : dot (-J) g ≤ dot (-J) x := this
      linarith
    by_cases h : L ≤ (ε : ℤ) ∧ N ≤ i
    · rw [sh_pos i ε h.1 h.2] at hz
      have D := hD i h.2
      by_cases hzT : z ∈ hatOf A kk vl i
      · exact hbase z (hAinf z hzT)
      · rw [MaxEnv.shell_eq_reach_inter]
        have hgR : g ∈ MaxEnv.reachSet (⋃ j, hatOf A kk vl j) (-(dir nxt)) :=
          ⟨g, by have := P.hray 0; rw [Nat.cast_zero, zero_smul, sub_zero] at this; exact this, 0, by simp⟩
        have hbey := P.beyond_of_not_mem D hz hzT
        obtain ⟨hzle, hzlev⟩ := D.pushShell_le z hz
        have hnxtJ : nxt ≠ J := fun e => by
          have := P.hdn; rw [e, det_self] at this; exact lt_irrefl 0 this
        have hzn : dot nxt z ≤ dot nxt g := by
          have := hzle nxt (P.hnxti i) hnxtJ; rwa [suppVal_eq (P.g_mem_nxt i)] at this
        refine ⟨qs_quadrant_mem hRlc P.hdn hR1 hR2 hgR
          (by rw [dot_neg_left, dot_neg_left]; linarith) hzn, ?_⟩
        show dot (-J) g - (ε : ℤ) ≤ dot (-J) z
        rw [P.svJ i] at hzlev
        rw [dot_neg_left, dot_neg_left]; linarith [h.1]
    · rw [sh_neg i ε h] at hz
      rcases hz with hz | hz
      · exact hbase z (hAinf z hz)
      · rw [Set.mem_singleton_iff] at hz
        rw [hz]
        apply hbase
        have e : faceStart (hatOf A kk vl i) J - (2 : ℤ) • dir J =
            g - ((faceLen (hatOf A kk vl i) J + 2 : ℕ) : ℤ) • dir J := by
          rw [P.faceStart_eq_pin i]; push_cast; rw [add_smul]; abel
        rw [e]; exact P.hray _
  · -- shellSubStrip
    intro ε i₀ _ hG i hi
    obtain ⟨hLε, hN₀⟩ := hguard ε i₀ hG
    have hNi : N ≤ i := le_trans hN₀ (le_trans (le_max_left _ _) hi)
    rw [sh_pos i ε hLε hNi, strip_target_eq (P.hBA i) (P.hAB i)]
    have D := hD i hNi
    exact D.subset_halfStrip (P.hlc i) (by rw [P.hE]; exact P.hnℓ) (by rw [P.hE]; exact P.hnℓ')
      P.hvlp P.hperp P.hfwd
  · -- shellProper
    intro ε i₀ _ hG i hi
    obtain ⟨hLε, hN₀⟩ := hguard ε i₀ hG
    have hNi : N ≤ i := le_trans hN₀ (le_trans (le_max_left _ _) hi)
    rw [sh_pos i ε hLε hNi]
    exact (hD i hNi).not_pushShell_subset
  · -- shellEnv
    refine ⟨L.toNat, N, by omega, fun i hi => ?_⟩
    rw [sh_pos i L.toNat (by omega) hi]
    exact (hD i hi).enveloped
  · -- fillCover
    intro ε i₀ _ hG i hi
    obtain ⟨hLε, hN₀⟩ := hguard ε i₀ hG
    have hi₀i : i₀ ≤ i := le_trans (le_max_left _ _) hi
    have hNi : N ≤ i := le_trans hN₀ hi₀i
    rw [sh_pos i ε hLε hNi, sh_pos i₀ ε hLε hN₀]
    have D := hD i hNi
    have D₀ := hD i₀ hN₀
    obtain ⟨n', hn'⟩ := Nivat.LaneFillCover.exists_lex_covector F
    have hconvE := Nivat.Colle37Geom.latticeConvex_erase_of_lexExtreme F.latticeConvex_S F.lex'
    have hwin := P.window hc F D D₀ (hlong i hNi).1 (hlong i₀ hN₀).1 (hlong i₀ hN₀).2.2.1
      (hlong i₀ hN₀).2.1
    intro z hz
    exact fillCover_of_window D.pushShell_finite F.a'_mem hconvE hn' hwin z hz

end PinTower

end Nivat.Hole1QShell

#print axioms Nivat.Hole1QShell.eq_of_prim_of_real_smul
#print axioms Nivat.Hole1QShell.mem_E_of_endpoint
#print axioms Nivat.Hole1QShell.PushData.E_subset_T
#print axioms Nivat.Hole1QShell.PushData.enveloped
#print axioms Nivat.Hole1QShell.PushData.pushShell_finite
#print axioms Nivat.Hole1QShell.PushData.not_pushShell_subset
#print axioms Nivat.Hole1QShell.PushData.pushShell_le
#print axioms Nivat.Hole1QShell.Bench.pushData_bench
#print axioms Nivat.Hole1QShell.Bench.bench_ok
#print axioms Nivat.Hole1QShell.window_fit
#print axioms Nivat.Hole1QShell.fillCover_of_window
#print axioms Nivat.Hole1QShell.halfStrip_eq_of_sandwich
#print axioms Nivat.Hole1QShell.strip_target_eq
#print axioms Nivat.Hole1QShell.row_nonempty
#print axioms Nivat.Hole1QShell.PushData.subset_halfStrip
#print axioms Nivat.Colle35.ChainDataGeom.ofShell
#print axioms Nivat.Hole1QShell.geom_of_geomCoreShell
#print axioms Nivat.ColleReg.exists_chainData_of_geomCoreShell
#print axioms Nivat.Hole1QShell.hadj_of_fan
#print axioms Nivat.Hole1QShell.pushData_of_fan
#print axioms Nivat.Hole1QShell.quad_bound
#print axioms Nivat.Hole1QShell.PushData.face_eq_rowW
#print axioms Nivat.Hole1QShell.PushData.faceStart_eq
#print axioms Nivat.Hole1QShell.PushData.faceLen_eq
#print axioms Nivat.Hole1QShell.PushData.faceStart_m2
#print axioms Nivat.Hole1QShell.mem_face_of_pinned
#print axioms Nivat.Hole1QShell.faceLen_mono_of_pinned
#print axioms Nivat.Hole1QShell.not_envOf_filler
#print axioms Nivat.Hole1QShell.quad_mem
#print axioms Nivat.Hole1QShell.qs_quadrant_mem
#print axioms Nivat.Hole1QShell.PinTower.faceStart_nxt
#print axioms Nivat.Hole1QShell.PinTower.eventually_long
#print axioms Nivat.Hole1QShell.PinTower.s0_mem_prv
#print axioms Nivat.Hole1QShell.PinTower.exists_c
#print axioms Nivat.Hole1QShell.PinTower.exists_Λ
#print axioms Nivat.Hole1QShell.PinTower.pushData
#print axioms Nivat.Hole1QShell.aprime_eq_faceStart
#print axioms Nivat.Hole1QShell.PinTower.row_end
#print axioms Nivat.Hole1QShell.PinTower.window
#print axioms Nivat.Hole1QShell.PinTower.reach_facts
#print axioms Nivat.Hole1QShell.PinTower.shell_pack

-- ===== end tmp/wip/hole1-qshell.lean =====

/-! ## Final assembly: `exists_chainData` with no residual hypothesis -/

namespace Nivat.ColleReg

open Nivat Nivat.Colle35

variable {ξ xper ϑ : Config ℤ} {vl p ℓ : ℤ × ℤ} {S : Finset (ℤ × ℤ)} {gen : ℤ × ℤ}

/-- **`RegionSteps.lean` `exists_chainData`, closed.**  Binder list and conclusion copied
verbatim from `RegionSteps.lean` (same namespace, `open`s and `variable`s); no extra hypothesis. -/
theorem exists_chainData_closed (hξ : IsMinimalCounterexample ξ) (d : DecompDataZ ξ)
    {w : ℝ × ℝ} (hw : w ≠ 0) (hw₁ : w ∈ ONED ξ) (hw₂ : -w ∈ ONED ξ)
    (hℓ_nel : ℓ ∈ Colle45.NonExpansiveLine ξ)
    (hℓ_pos : Colle45.IsOneSidedNonexpansive ξ ℓ)
    (hℓ_neg : Colle45.IsOneSidedNonexpansive ξ (-ℓ))
    (hxper : xper ∈ orbitClosure ξ)
    (hp_mem : p ∈ Per xper) (hp_ne : p ≠ 0) (hvl_ne : vl ≠ 0) (hvl_prim : Primitive vl)
    (hdet_vl : det p vl = 0) (hdet_ℓ : Nivat.LE2.dot ℓ vl = 0)
    (hp_neg : ∃ c : ℕ, 0 < c ∧ p = -(c : ℤ) • vl)
    (hpartner : ∃ (yper : Config ℤ) (nℓ : ℤ × ℤ) (cz : ℤ) (g : ℤ × ℤ),
      yper ∈ orbitClosure ξ ∧ xper ≠ yper ∧
      nℓ ≠ 0 ∧ Primitive nℓ ∧ Nivat.LE2.dot nℓ vl = 0 ∧ 0 < det nℓ vl ∧
      (∀ z : ℤ × ℤ, cz < Nivat.LE2.dot nℓ z → xper z = yper z) ∧
      Nivat.LE2.dot nℓ g = cz ∧ xper g ≠ yper g ∧
      ¬ ∃ h h' : ℤ × ℤ, det h h' ≠ 0 ∧
        PeriodicOnWith xper {z | cz ≤ Nivat.LE2.dot nℓ z} h ∧
        PeriodicOnWith xper {z | cz ≤ Nivat.LE2.dot nℓ z} h')
    (hcase2 : Case2 ξ xper d.Sphi vl) :
    ∃ (genφ : ℤ × ℤ) (cg : ChainDataGeom ξ xper vl p d.Sphi genφ),
      Nivat.Colle.GeneratesAt ξ d.Sphi genφ ∧
      cg.toChainData.Env = Nivat.LE2.EnvOf (d.Sphi : Set (ℤ × ℤ)) := by
  obtain ⟨yper, nℓ, cz, g0, hyper, hxy, hnℓ_ne, hnℓ_prim, hperp, hdetpos, hagree, hgz, hgxy,
    hnotDP⟩ := hpartner
  obtain ⟨rd⟩ :=
    Nivat.ItemIIFeed.nonempty_itemIIRecursionData_of_chainData_binders d cz hxper hvl_ne
      hvl_prim hℓ_nel hℓ_pos hℓ_neg hdet_ℓ hnℓ_prim hperp hcase2
  obtain ⟨hnE, hnE'⟩ := Nivat.ItemIIFeed.mem_E_Sphi_and_neg_of_prim_perp d hvl_ne hℓ_nel hℓ_pos
    hℓ_neg hdet_ℓ hnℓ_prim hperp
  obtain ⟨σ, hσ, J, prv, nxt, g, hJ, hprv, hnxt, hdp, hdn, hadjP, hadjN, hJne1, hJne2, hdetJ,
    hpin, hunb, hhp, hswept, hray, hsupp, ⟨F⟩⟩ :=
    Nivat.Hole1JPack.exists_jpack d rd hvl_ne hvl_prim hnℓ_ne hnℓ_prim hperp hdetpos hnE'
  -- the reindexed chain
  let A' : ℕ → Set (ℤ × ℤ) := fun n => rd.A (σ n)
  let B' : ℕ → Set (ℤ × ℤ) := fun n => rd.B (σ n)
  let u' : ℕ → ℤ × ℤ := fun n => rd.u (σ n)
  let kk' : ℕ → ℕ := fun n => rd.kk (σ n)
  have maxA' : ∀ i, IsMaxEnvIn (Nivat.LE2.EnvOf (↑d.Sphi : Set (ℤ × ℤ)))
      (canonA ξ xper vl B' u' i) (A' i) := fun i => rd.maxA (σ i)
  have subAB' : ∀ i, A' i ⊆ B' (i + 1) :=
    fun i => Nivat.LeafAItemII.subAB_comp (B := rd.B) (A := rd.A) (σ := σ) hσ rd.subBA rd.subAB i
  have hfin' : ∀ i, (hatOf A' kk' vl i).Finite :=
    Nivat.ChainAsm.hatOf_finite kk' vl (fun i => (rd.finB (σ (i + 1))).subset (subAB' i))
  have AhatMono' : ∀ i j, i ≤ j → hatOf A' kk' vl i ⊆ hatOf A' kk' vl j :=
    fun i j hij => rd.AhatMono (σ i) (σ j) (hσ.monotone hij)
  have henv' : ∀ i, Nivat.LE2.EnvOf (↑d.Sphi : Set (ℤ × ℤ)) (hatOf A' kk' vl i) := by
    intro i
    show Nivat.LE2.Enveloped _ _
    rw [Nivat.Colle35.hatOf_eq_shift]
    exact (Nivat.LE2.enveloped_shift_right _).mpr (maxA' i).1
  have hconv' : IsLatticeConvexRegion (⋃ i, hatOf A' kk' vl i) :=
    latticeConvex_iUnion_hatOf ξ xper vl d.Sphi (Nivat.LE2.EnvOf (↑d.Sphi : Set (ℤ × ℤ)))
      B' A' u' kk' rfl maxA' hfin' AhatMono'
  -- orientation: `vl = dir nℓ`, so the pushed face points forward
  have hdirneg := Nivat.Hole1JPack.dir_neg_nℓ_eq_neg_vl hnℓ_ne hnℓ_prim hvl_prim hperp hdetpos
  have hvl_dir : Nivat.LE2.dir nℓ = vl := by
    have e : Nivat.LE2.dir (-nℓ) = -Nivat.LE2.dir nℓ := by
      simp only [Nivat.LE2.dir, Prod.fst_neg, Prod.snd_neg, Prod.neg_mk, neg_neg]
    rw [e] at hdirneg; exact neg_inj.mp hdirneg
  have hfwd : 0 < Nivat.LE2.dot J vl := by
    rw [← hvl_dir, Nivat.Hole1QShell.dot_dir_eq_det]
    have : det J (-nℓ) = det nℓ J := by simp only [det, Prod.fst_neg, Prod.snd_neg]; ring
    rw [this] at hdetJ; exact hdetJ
  have P : Nivat.Hole1QShell.PinTower d A' B' kk' vl nℓ J prv nxt g :=
    { hfin := hfin'
      henv := henv'
      hmono := AhatMono'
      hBA := fun i => rd.subBA (σ i)
      hAB := subStrip_of_max maxA'
      hJ := hJ, hprv := hprv, hnxt := hnxt, hdp := hdp, hdn := hdn
      hadjP := hadjP, hadjN := hadjN
      hpin := hpin, hunb := hunb, hhp := hhp, hswept := hswept, hray := hray, hsupp := hsupp
      hconv := hconv'
      hnℓ := hnE, hnℓ' := hnE'
      hvlp := Nivat.LE2.prim_iff_primitive.mpr hvl_prim
      hperp := hperp
      hfwd := hfwd }
  obtain ⟨sh, I₀, h1, h2, h3, h4, h5, h6, h7⟩ := P.shell_pack F
  have hbot := Nivat.Hole1Bottom.bottom_of_pinned d hfin' henv' AhatMono' hJ hprv hnxt hdp hdn
    hadjP hadjN hpin hunb hhp hswept hray hsupp hconv' F
  -- the period is transverse to `J`
  have hdotp : Nivat.LE2.dot (-J) p ≠ 0 := by
    obtain ⟨cN, hcN, hp_eq⟩ := hp_neg
    have := Nivat.LeafAJSelect.dot_J_p_ne_zero (k := -(cN : ℤ))
      (Nivat.LE2.prim_iff_primitive.mp hJ.1) hnℓ_prim hvl_ne hperp ⟨hJne1, hJne2⟩
      (neg_ne_zero.mpr (by exact_mod_cast hcN.ne')) hp_eq
    rw [Nivat.LE2.dot_neg_left]; exact neg_ne_zero.mpr this
  have hsweep : Nivat.LE2.dot (-J) (-(Nivat.LE2.dir nxt)) < 0 := by
    have : Nivat.LE2.dot (-J) (-(Nivat.LE2.dir nxt)) = -det J nxt := by
      simp only [Nivat.LE2.dot, Nivat.LE2.dir, det, Prod.fst_neg, Prod.snd_neg]; ring
    rw [this]; linarith
  let G : Nivat.Hole1QShell.GeomCoreShell xper vl p d.Sphi B' A' kk' :=
    { vJ1 := -(Nivat.LE2.dir nxt)
      nJ := -J
      cJ := Nivat.LE2.dot (-J) g
      hsweep := hsweep
      hhp := hhp
      hswept := hswept
      vJ := -(Nivat.LE2.dir J)
      F := F
      vJ_prim := Nivat.LE2.prim_iff_primitive.mp (Nivat.LE2.prim_dir_of_prim hJ.1).neg
      nJ_prim := Nivat.LE2.prim_iff_primitive.mp hJ.1.neg
      bottom := hbot
      dot_nJ_p := hdotp
      sh := sh
      shellFinite := h1
      subShell := h2
      shellSubInf := h3
      I₀ := I₀
      shellSubStrip := h4
      shellProper := h5
      shellEnv := h6
      fillCover := h7 }
  exact ⟨G.F.a', Nivat.Hole1QShell.geom_of_geomCoreShell rd hvl_ne hnℓ_prim hperp hdet_vl
    hp_neg hnotDP hσ G, Nivat.Colle35.FaceBlock.generatesAt_a' G.F d.isGeneratingSet, rfl⟩

end Nivat.ColleReg

-- type and axiom closure of the closed hole (`RegionSteps.lean`'s `exists_chainData` `exact`s it)
#check @Nivat.ColleReg.exists_chainData_closed
#print axioms Nivat.ColleReg.exists_chainData_closed
