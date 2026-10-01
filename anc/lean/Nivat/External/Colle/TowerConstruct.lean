/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.TowerBuild
import Nivat.External.Colle.ConeRegion
import Nivat.External.Colle.DecompData
import Nivat.External.Colle.ZonoEdgeGen
import Nivat.External.Colle.NewtonZonotope
import Nivat.External.Colle.ConvTransport
import Nivat.External.Colle.LatticeEdges
import Nivat.External.Colle.HsuppCaseCW
import Nivat.External.Colle.PolyChain
import Nivat.External.Colle.TowerEHelp

/-!
# Constructing `wtower`/`M` from `d.toDecompData.h` (lane-tower, `blueprint/LEAF-TOWER.md`)

Consumer: `Nivat.External.Colle.RegionSteps.exists_cutResidualR_of_claim46`
(`RegionSteps.lean:1708-1726`). As of 2026-09-22 its binder list has been extended (credited to
this lane's discovery) to include `hprim : Prim nℓ`, `i : Fin d.toDecompData.m`,
`hdoth : dot nℓ (d.toDecompData.h i) = 0`, and
`hadj : ∀ n ∈ Nivat.LE2.E (↑d.toDecompData.Sphi : Set (ℤ × ℤ)), ¬ (Nivat.LE2.dot n vl < 0 ∧
0 < Nivat.LE2.dot n u')` — threaded through from the upstream sites that originally produced
them (hole 1 at `:2634`, hole 2 at `:2646`), so all four are now available here directly; no
separate reconstruction of `i`/`hdoth`/`hadj` is needed in this file.

## §1. Every generator direction of `d.h` gives an edge normal of `B`

This is unconditional (`Sphi_negSymm`'s proof pattern), needs only `d` and `henv`, and does not
depend on the missing `i`/`hdoth`/`hadj`. It is the first step of the recipe team-lead gave
2026-09-22 ("construct `wtower` from `d.h`"): each generator `h j` contributes a pair of
antipodal edge normals to `B`, which is where the candidate `wtower` directions come from.
-/

namespace Nivat.ColleReg

open Nivat.LE2 Nivat.Colle35 Nivat.PolyChain

variable {ξ : Nivat.Config ℤ}

/-- `Conv d.Sphi = Conv (zonoF univ d.h)` — the convex-hull identity `Sphi_negSymm`'s proof
uses internally, extracted so it can be reused for the `E`-transport in both directions. -/
theorem conv_Sphi_eq_conv_zonoF (d : DecompData ξ) :
    Nivat.Conv d.Sphi = Nivat.Conv (Nivat.LE2.zonoF Finset.univ d.h) := by
  rw [d.Sphi_eq, Nivat.LE2.Conv_supp_prod_eq_Conv_zonoF Finset.univ d.h (fun i _ => d.h_ne i)]

/-- `E ↑d.Sphi = E ↑(zonoF univ d.h)`, the transported edge-normal set. -/
theorem E_Sphi_eq_E_zonoF (d : DecompData ξ) :
    E (↑d.Sphi : Set (ℤ × ℤ)) =
      E (↑(Nivat.LE2.zonoF Finset.univ d.h) : Set (ℤ × ℤ)) :=
  Nivat.LE2.E_congr_of_Conv_eq (conv_Sphi_eq_conv_zonoF d)

/-- Each generator `d.h j` contributes both `genPerp' (d.h j)` and its negation as edge normals
of `d.Sphi`. -/
theorem genPerp'_mem_E_Sphi (d : DecompData ξ) (j : Fin d.m) :
    Nivat.LE2.genPerp' (d.h j) ∈ E (↑d.Sphi : Set (ℤ × ℤ)) ∧
    -Nivat.LE2.genPerp' (d.h j) ∈ E (↑d.Sphi : Set (ℤ × ℤ)) := by
  rw [E_Sphi_eq_E_zonoF]
  exact Nivat.LE2.mem_E_zonoF d.h d.h_ne d.h_dir j

/-- Transported to `B` via `henv`: each generator `d.h j` contributes both `genPerp' (d.h j)`
and its negation as edge normals of `B`. This is `E B = E ↑d.Sphi` (`Enveloped.E_eq`) applied to
`genPerp'_mem_E_Sphi`; it needs `(E ↑d.Sphi).Finite`, free from `d.Sphi.finite_toSet`. -/
theorem genPerp'_mem_E_B {B : Set (ℤ × ℤ)} (d : DecompData ξ)
    (henv : Nivat.LE2.EnvOf (↑d.Sphi : Set (ℤ × ℤ)) B) (j : Fin d.m) :
    Nivat.LE2.genPerp' (d.h j) ∈ E B ∧
    -Nivat.LE2.genPerp' (d.h j) ∈ E B := by
  have hfin : (E (↑d.Sphi : Set (ℤ × ℤ))).Finite :=
    Nivat.LE2.finite_E_of_finite d.Sphi.finite_toSet
  have hE : E B = E (↑d.Sphi : Set (ℤ × ℤ)) := Nivat.LE2.Enveloped.E_eq hfin henv
  rw [hE]
  exact genPerp'_mem_E_Sphi d j

/-! ## §2. `hadjB` from `hadj`, and excluding the `vl`-parallel generator

Consumer now supplies `hprim : Prim nℓ`, `i : Fin d.m`, `hdoth : dot nℓ (d.h i) = 0`,
`hadj : ∀ n ∈ E ↑d.Sphi, ¬(dot n vl < 0 ∧ 0 < dot n u')` (`RegionSteps.lean:1706-1725`,
2026-09-22 threading). This section converts `hadj` to the `E B` version (`hadjB`, needed for
the `I = 0` base case of `hbase`'s induction) and proves every generator `d.h j`, `j ≠ i`, is
not parallel to `vl` — so it can be legitimately oriented into a `wtower` direction. -/

/-- `hadjB`, transported from `hadj` via `henv`. -/
theorem hadjB_of_hadj {B : Set (ℤ × ℤ)} (d : DecompData ξ) {vl u' : ℤ × ℤ}
    (henv : Nivat.LE2.EnvOf (↑d.Sphi : Set (ℤ × ℤ)) B)
    (hadj : ∀ n ∈ E (↑d.Sphi : Set (ℤ × ℤ)), ¬ (dot n vl < 0 ∧ 0 < dot n u')) :
    ∀ n ∈ E B, ¬ (dot n vl < 0 ∧ 0 < dot n u') := by
  have hfin : (E (↑d.Sphi : Set (ℤ × ℤ))).Finite :=
    Nivat.LE2.finite_E_of_finite d.Sphi.finite_toSet
  have hE : E B = E (↑d.Sphi : Set (ℤ × ℤ)) := Nivat.LE2.Enveloped.E_eq hfin henv
  intro n hn
  exact hadj n (hE ▸ hn)

/-- `d.h i` (the generator `hdoth` singles out) is a `ℤ`-multiple of `vl`: both are `⊥ nℓ`,
and `nℓ ≠ 0` (from `hprim`) forces `det vl (d.h i) = 0`, so `Primitive vl` gives the multiple. -/
theorem h_i_eq_zsmul_vl (d : DecompData ξ) {vl nℓ : ℤ × ℤ}
    (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0) :
    ∃ c : ℤ, d.h i = c • vl := by
  have hnℓ_ne : nℓ ≠ 0 := (Nivat.LE2.prim_iff_primitive.mp hprim).ne_zero
  have hdet : det vl (d.h i) = 0 :=
    Nivat.LE2.det_eq_zero_of_dot_eq_zero hnℓ_ne hperp hdoth
  exact Nivat.eq_zsmul_of_det_eq_zero hvl_prim hdet

/-- Every generator `d.h j` with `j ≠ i` has `dot nℓ (d.h j) ≠ 0`: if it vanished, `d.h j` would
also be a multiple of `vl` (same argument as `h_i_eq_zsmul_vl`), hence parallel to `d.h i`,
contradicting `h_dir i j`. -/
theorem dot_nl_h_ne_zero (d : DecompData ξ) {vl nℓ : ℤ × ℤ}
    (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0) {j : Fin d.m} (hij : j ≠ i) :
    dot nℓ (d.h j) ≠ 0 := by
  intro hdothj
  have hnℓ_ne : nℓ ≠ 0 := (Nivat.LE2.prim_iff_primitive.mp hprim).ne_zero
  obtain ⟨ci, hci⟩ := h_i_eq_zsmul_vl d hvl_prim hprim hperp i hdoth
  have hdetj : det vl (d.h j) = 0 :=
    Nivat.LE2.det_eq_zero_of_dot_eq_zero hnℓ_ne hperp hdothj
  obtain ⟨cj, hcj⟩ := Nivat.eq_zsmul_of_det_eq_zero hvl_prim hdetj
  apply d.h_dir j i hij
  rw [hci, hcj]
  simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- The oriented, non-primitive generator: `d.h j` flipped in sign, if necessary, so that
`dot nℓ (·) < 0`. Only meaningful for `j ≠ i` (elsewhere `dot nℓ (d.h j) = 0`, no orientation
is forced). -/
noncomputable def orientGen (d : DecompData ξ) (nℓ : ℤ × ℤ) (j : Fin d.m) : ℤ × ℤ :=
  if dot nℓ (d.h j) < 0 then d.h j else -(d.h j)

theorem dot_orientGen_neg (d : DecompData ξ) {vl nℓ : ℤ × ℤ}
    (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0) {j : Fin d.m} (hij : j ≠ i) :
    dot nℓ (orientGen d nℓ j) < 0 := by
  have hne := dot_nl_h_ne_zero d hvl_prim hprim hperp i hdoth hij
  unfold orientGen
  split_ifs with hlt
  · exact hlt
  · have hflip : dot nℓ (-(d.h j)) = - dot nℓ (d.h j) := by
      rw [dot_comm, dot_neg_left, dot_comm]
    rw [hflip]
    omega

/-- The primitive tower-direction candidate from generator `j ≠ i`: `primPart` of the oriented
generator. Primitive by construction, `dot nℓ (·) < 0` since `primPart` divides by a positive
gcd (sign-preserving). -/
noncomputable def wgen (d : DecompData ξ) (nℓ : ℤ × ℤ) (j : Fin d.m) : ℤ × ℤ :=
  Nivat.LE2.primPart (orientGen d nℓ j)

theorem wgen_prim (d : DecompData ξ) {vl nℓ : ℤ × ℤ}
    (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0) {j : Fin d.m} (hij : j ≠ i) :
    Primitive (wgen d nℓ j) := by
  have hne : orientGen d nℓ j ≠ 0 := by
    intro h0
    have := dot_orientGen_neg d hvl_prim hprim hperp i hdoth hij
    rw [h0] at this
    simp [dot] at this
  exact Nivat.LE2.prim_iff_primitive.mp (Nivat.LE2.primPart_spec hne).1

theorem dot_wgen_neg (d : DecompData ξ) {vl nℓ : ℤ × ℤ}
    (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0) {j : Fin d.m} (hij : j ≠ i) :
    dot nℓ (wgen d nℓ j) < 0 := by
  have hlt := dot_orientGen_neg d hvl_prim hprim hperp i hdoth hij
  have hne : orientGen d nℓ j ≠ 0 := by
    intro h0; rw [h0] at hlt; simp [dot] at hlt
  obtain ⟨g, hgpos, hgeq⟩ := (Nivat.LE2.primPart_spec hne).2
  have heq : dot nℓ (orientGen d nℓ j) = g * dot nℓ (wgen d nℓ j) := by
    conv_lhs => rw [hgeq]
    show dot nℓ (g • Nivat.LE2.primPart (orientGen d nℓ j)) = g * dot nℓ (wgen d nℓ j)
    rw [dot_comm, dot_smul, dot_comm (Nivat.LE2.primPart (orientGen d nℓ j)) nℓ]
    rfl
  rw [heq] at hlt
  nlinarith

/-! ## §3. Sorting the candidates: the rational key (team-lead's 2026-09-22 recipe)

Avoids a recursive `exists_max_det` peel (which would be 150-300 lines): for `v` with
`0 < dot e v` (`e := -nℓ` in the eventual application), `keyOf e v := det e v / dot e v ∈ ℚ`
is monotone in the angular position of `v` **in the `det`-increasing sense** (`det_pos_iff_key_lt`:
`0 < det a b ↔ keyOf e a < keyOf e b`), so sorting by `keyOf` and reading off
consecutive pairs gives `hside` for free (no third candidate has a key strictly between two
consecutive ones, since the list contains every candidate). -/

/-- The angular-sort key, ascending in the `det`-order.

⚠ **2026-09-24（第 197 轮）订正**（lane-tower-hlev 实测，集成者复核后落盘）：本条 docstring
原写 `The clockwise-sort key.`，**方位词写反了**。`det u v = u.1*v.2 - u.2*v.1`
（`Nivat.det`，`Config.lean:43`）在标准取向下，`0 < det a b` 是「`b` 在 `a` 的**逆时针**一侧」；
配 `det_pos_iff_key_lt`（本文件，`0 < det a b ↔ keyOf e a < keyOf e b`）⟹ **`keyOf` 升序
＝ 逆时针**，不是顺时针。

无任何证明依赖那个词（本文件所有引理给的都是 `det` 不等式），但下游若照字面读去对原文
`b3_colle2.txt:764` 的 `ℓ_1,…,ℓ_{2m}` 环序，会把 `sortedCand` 的两端认反——第 197 轮正好
有一格（`hstrict` ⟺ `𝒮_φ` 的 `ℓ'`-边与 `ℓ`-边相邻）压在这个方向上。⟹ **下游陈述端序时
一律用 `det` 说，不要用方位词。** -/
noncomputable def keyOf (e v : ℤ × ℤ) : ℚ := (det e v : ℚ) / (dot e v : ℚ)

/-- Core algebraic identity behind `keyOf`'s monotonicity: pure `ring`. -/
theorem key_identity (e a b : ℤ × ℤ) :
    det e b * dot e a - det e a * dot e b = (e.1 ^ 2 + e.2 ^ 2) * det a b := by
  simp only [det, dot]; ring

/-- `keyOf e` is order-monotone with `det` on the open half-plane `{dot e · > 0}`. -/
theorem det_pos_iff_key_lt {e a b : ℤ × ℤ} (he : e ≠ 0) (ha : 0 < dot e a) (hb : 0 < dot e b) :
    0 < det a b ↔ keyOf e a < keyOf e b := by
  have hne2 : e.1 ^ 2 + e.2 ^ 2 ≠ 0 := by
    intro h
    apply he
    have h1 : e.1 = 0 := by nlinarith [sq_nonneg e.1, sq_nonneg e.2]
    have h2 : e.2 = 0 := by nlinarith [sq_nonneg e.1, sq_nonneg e.2]
    exact Prod.ext h1 h2
  have hepos : (0 : ℤ) < e.1 ^ 2 + e.2 ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm hne2)
  have hid := key_identity e a b
  have haQ : (0 : ℚ) < (dot e a : ℚ) := by exact_mod_cast ha
  have hbQ : (0 : ℚ) < (dot e b : ℚ) := by exact_mod_cast hb
  unfold keyOf
  rw [div_lt_iff₀ haQ, div_mul_eq_mul_div, lt_div_iff₀ hbQ]
  constructor
  · intro hab
    have hz : det e a * dot e b < det e b * dot e a := by nlinarith
    exact_mod_cast hz
  · intro hlt
    have hz : (det e a : ℤ) * dot e b < (det e b : ℤ) * dot e a := by exact_mod_cast hlt
    nlinarith

/-- Injectivity of `keyOf e` on the open half-plane, for distinct non-parallel directions. -/
theorem keyOf_injOn {e : ℤ × ℤ} (he : e ≠ 0) {a b : ℤ × ℤ}
    (ha : 0 < dot e a) (hb : 0 < dot e b) (hab : det a b ≠ 0) :
    keyOf e a ≠ keyOf e b := by
  rcases lt_or_gt_of_ne hab with h | h
  · intro hcon
    have := (det_pos_iff_key_lt he hb ha).mp (by
      have hdba : det b a = - det a b := det_skew b a
      omega)
    linarith [hcon]
  · intro hcon
    have := (det_pos_iff_key_lt he ha hb).mp h
    linarith [hcon]

/-! ## §4. Assembling the sorted candidate list

The candidates are `wgen d nℓ j` for `j ≠ i`; every one has `dot nℓ (·) < 0`
(`dot_wgen_neg`), i.e. `0 < dot (-nℓ) (·)`, so `keyOf (-nℓ)` is defined and monotone on the
whole candidate set. We sort with `List.mergeSort` using the *Boolean* comparator
`leKey nℓ a b := decide (keyOf (-nℓ) a ≤ keyOf (-nℓ) b)`; since `≤` on `ℚ` is transitive and
total on the nose (no need to restrict to the half-plane, unlike `Finset.sort`'s typeclass
route, which would need a global `Std.Antisymm` instance `keyOf` does not have), the two
hypotheses `pairwise_mergeSort` asks for are immediate `le_trans`/`le_total`. Distinctness of
consecutive elements then upgrades the resulting `≤`-pairwise list to `<` termwise, which
transports back to `det` positivity via `det_pos_iff_key_lt`. -/

/-- The candidate directions: every generator except `i`, canonically oriented and primitivized
towards `nℓ`, with `u'` itself erased. **Team-lead 2026-09-22:** filtering `u'` out here (rather
than threading a `w ≠ u'` side condition through every downstream lemma) is free — the `u'`-ray
is already covered by `coneRegion`/the tower's base step, so dropping a candidate literally equal
to `u'` from the interior sweep changes nothing geometrically — and it makes `w ≠ u'` (hence
`det w u' ≠ 0`, via `det_ne_zero_wgen_u'_of_ne`/Lemma H) available for free at every candidate,
closing the one open side condition in `hside_boundary_u'`/the half-turn lemma (§7–§8). -/
noncomputable def candSet (d : DecompData ξ) (nℓ u' : ℤ × ℤ) (i : Fin d.m) : Finset (ℤ × ℤ) :=
  ((Finset.univ.erase i).image (wgen d nℓ)).erase u'

/-- Boolean comparator for the angular sort: `keyOf (-nℓ)`, ascending
(＝ `det`-increasing; see the ⚠ on `keyOf`). -/
noncomputable def leKey (nℓ a b : ℤ × ℤ) : Bool := decide (keyOf (-nℓ) a ≤ keyOf (-nℓ) b)

theorem leKey_trans (nℓ : ℤ × ℤ) : ∀ a b c, leKey nℓ a b → leKey nℓ b c → leKey nℓ a c := by
  intro a b c hab hbc
  simp only [leKey, decide_eq_true_eq] at hab hbc ⊢
  exact le_trans hab hbc

theorem leKey_total (nℓ : ℤ × ℤ) : ∀ a b, leKey nℓ a b || leKey nℓ b a := by
  intro a b
  simp only [leKey, decide_eq_true_eq, Bool.or_eq_true]
  exact le_total _ _

/-- The candidates, sorted by `keyOf (-nℓ)` ascending (＝ `det`-increasing order;
the ⚠ on `keyOf` explains why this used to say "clockwise" and why that was wrong). -/
noncomputable def sortedCand (d : DecompData ξ) (nℓ u' : ℤ × ℤ) (i : Fin d.m) : List (ℤ × ℤ) :=
  (candSet d nℓ u' i).toList.mergeSort (leKey nℓ)

theorem sortedCand_pairwise (d : DecompData ξ) (nℓ u' : ℤ × ℤ) (i : Fin d.m) :
    (sortedCand d nℓ u' i).Pairwise (fun a b => leKey nℓ a b = true) := by
  have := List.pairwise_mergeSort (le := leKey nℓ) (leKey_trans nℓ) (leKey_total nℓ)
    ((candSet d nℓ u' i).toList)
  simpa [sortedCand] using this

theorem sortedCand_nodup (d : DecompData ξ) (nℓ u' : ℤ × ℤ) (i : Fin d.m) :
    (sortedCand d nℓ u' i).Nodup :=
  (List.mergeSort_perm _ _).nodup_iff.mpr (Finset.nodup_toList _)

theorem sortedCand_perm (d : DecompData ξ) (nℓ u' : ℤ × ℤ) (i : Fin d.m) :
    List.Perm (sortedCand d nℓ u' i) (candSet d nℓ u' i).toList :=
  List.mergeSort_perm _ _

theorem mem_sortedCand (d : DecompData ξ) (nℓ u' : ℤ × ℤ) (i : Fin d.m) {v : ℤ × ℤ} :
    v ∈ sortedCand d nℓ u' i ↔ v ∈ candSet d nℓ u' i := by
  rw [← Finset.mem_toList]
  exact (sortedCand_perm d nℓ u' i).mem_iff

/-- Every candidate has `dot nℓ (·) < 0`, i.e. lies in the open half-plane `dot (-nℓ) (·) > 0`
where `keyOf (-nℓ)` is monotone with `det`. -/
theorem dot_of_mem_candSet {vl nℓ u' : ℤ × ℤ} (d : DecompData ξ)
    (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0) {v : ℤ × ℤ} (hv : v ∈ candSet d nℓ u' i) :
    dot nℓ v < 0 := by
  obtain ⟨_, hv_img⟩ := Finset.mem_erase.mp hv
  obtain ⟨j, hj_mem, hj⟩ := Finset.mem_image.mp hv_img
  have hij : j ≠ i := (Finset.mem_erase.mp hj_mem).1
  rw [← hj]
  exact dot_wgen_neg d hvl_prim hprim hperp i hdoth hij

/-- Every candidate is primitive (it is `wgen d nℓ j` for some `j ≠ i`). -/
theorem prim_of_mem_candSet {vl nℓ u' : ℤ × ℤ} (d : DecompData ξ)
    (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0) {v : ℤ × ℤ} (hv : v ∈ candSet d nℓ u' i) :
    Primitive v := by
  obtain ⟨_, hv_img⟩ := Finset.mem_erase.mp hv
  obtain ⟨j, hj_mem, hj⟩ := Finset.mem_image.mp hv_img
  have hij : j ≠ i := (Finset.mem_erase.mp hj_mem).1
  rw [← hj]
  exact wgen_prim d hvl_prim hprim hperp i hdoth hij

/-- Every candidate is literally distinct from `u'` — `candSet` is defined as the image erased
of `u'` (team-lead 2026-09-22: filtering `u'` out of the sweep loses nothing geometrically, since
the `u'`-ray is already covered by `coneRegion`/the tower's base step), so this is immediate from
`Finset.mem_erase`, no case analysis needed. -/
theorem ne_u'_of_mem_candSet {d : DecompData ξ} {nℓ u' : ℤ × ℤ} {i : Fin d.m} {v : ℤ × ℤ}
    (hv : v ∈ candSet d nℓ u' i) : v ≠ u' :=
  (Finset.mem_erase.mp hv).1

/-- Two distinct candidates never have zero determinant: both are primitive with
`dot nℓ (·) < 0`, so `w = v ∨ w = -v` (from `eq_or_eq_neg_of_det_eq_zero`) forces `w = v`
(ruled out by distinctness) since `w = -v` would flip the sign of `dot nℓ`. -/
theorem det_ne_zero_of_mem_candSet {vl nℓ u' : ℤ × ℤ} (d : DecompData ξ)
    (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0) {a b : ℤ × ℤ}
    (ha : a ∈ candSet d nℓ u' i) (hb : b ∈ candSet d nℓ u' i) (hab : a ≠ b) :
    det a b ≠ 0 := by
  intro hd
  have hap : Primitive a := prim_of_mem_candSet d hvl_prim hprim hperp i hdoth ha
  have hbp : Primitive b := prim_of_mem_candSet d hvl_prim hprim hperp i hdoth hb
  have hda : dot nℓ a < 0 := dot_of_mem_candSet d hvl_prim hprim hperp i hdoth ha
  have hdb : dot nℓ b < 0 := dot_of_mem_candSet d hvl_prim hprim hperp i hdoth hb
  rcases Nivat.eq_or_eq_neg_of_det_eq_zero hap hbp hd with heq | heq
  · exact hab heq.symm
  · rw [heq] at hdb
    rw [dot_comm, dot_neg_left, dot_comm] at hdb
    omega

/-- Two consecutive elements of `sortedCand` have strictly positive `det`: the earlier one
comes strictly first in the `det`-increasing angular order around `-nℓ` (see the ⚠ on `keyOf`;
this used to say "clockwise", which was the wrong orientation word). -/
theorem det_pos_of_sortedCand_pairwise {vl nℓ u' : ℤ × ℤ} (d : DecompData ξ)
    (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0)
    (hnℓ_ne : nℓ ≠ 0) {a b : ℤ × ℤ}
    (ha : a ∈ candSet d nℓ u' i) (hb : b ∈ candSet d nℓ u' i) (hab : a ≠ b)
    (hle : leKey nℓ a b = true) :
    0 < det a b := by
  have hea : 0 < dot (-nℓ) a := by
    have := dot_of_mem_candSet d hvl_prim hprim hperp i hdoth ha
    rw [dot_neg_left]; omega
  have heb : 0 < dot (-nℓ) b := by
    have := dot_of_mem_candSet d hvl_prim hprim hperp i hdoth hb
    rw [dot_neg_left]; omega
  have he_ne : (-nℓ : ℤ × ℤ) ≠ 0 := by
    intro h0; apply hnℓ_ne
    have hnn : nℓ = -(-nℓ) := by ring
    rw [hnn, h0]; simp
  have hkey_le : keyOf (-nℓ) a ≤ keyOf (-nℓ) b := by
    simpa [leKey] using hle
  have hab_det_ne : det a b ≠ 0 :=
    det_ne_zero_of_mem_candSet d hvl_prim hprim hperp i hdoth ha hb hab
  have hkey_ne : keyOf (-nℓ) a ≠ keyOf (-nℓ) b := keyOf_injOn he_ne hea heb hab_det_ne
  have hkey_lt : keyOf (-nℓ) a < keyOf (-nℓ) b := lt_of_le_of_ne hkey_le hkey_ne
  exact (det_pos_iff_key_lt he_ne hea heb).mpr hkey_lt

/-! ## §5. `wtower`/`Mtower`: indexing into `sortedCand`, direction fixed by `sign (det u' vl)`

Team-lead 2026-09-22 (追加六/七): the naive "always-ascending `keyOf`" order used in an earlier
draft is wrong in general — whether the tower sweeps `sortedCand` forward or backward depends
on `sign (det u' vl)` (`hunimod`). `wtower k` reads off `sortedCand` at index `k` (forward) or
`length - 1 - k` (backward, when `0 < det u' vl`), for `k < length`, and is `-vl` at `k = length`
and beyond (junk). This makes every consecutive interior pair's `det` sign match the constant
sign `det (candidate) (-vl)` has on the whole half-plane (`det_vl_sign_eq_of_dot_nl_neg`, §6),
so `hside` at every interior index is a product of two same-signed nonzero factors. -/

/-- The index into `sortedCand` that `wtower` reads at position `k`: forward if
`det u' vl ≤ 0`, backward (from the end) if `0 < det u' vl`. -/
noncomputable def towerIdx (vl u' : ℤ × ℤ) (len k : ℕ) : ℕ :=
  if 0 < det u' vl then len - 1 - k else k

theorem towerIdx_lt {vl u' : ℤ × ℤ} {len k : ℕ} (h : k < len) :
    towerIdx vl u' len k < len := by
  unfold towerIdx; split_ifs <;> omega

/-- The tower directions: `sortedCand`, read forward or backward depending on
`sign (det u' vl)`, then `-vl`. -/
noncomputable def wtower (d : DecompData ξ) (nℓ vl u' : ℤ × ℤ) (i : Fin d.m) (k : ℕ) : ℤ × ℤ :=
  if h : k < (sortedCand d nℓ u' i).length then
    (sortedCand d nℓ u' i)[towerIdx vl u' (sortedCand d nℓ u' i).length k]'(towerIdx_lt h)
  else -vl

/-- The tower length: one more than the number of sorted candidates (for the appended `-vl`). -/
noncomputable def Mtower (d : DecompData ξ) (nℓ u' : ℤ × ℤ) (i : Fin d.m) : ℕ :=
  (sortedCand d nℓ u' i).length + 1

theorem wtower_eq_getElem {d : DecompData ξ} {nℓ vl u' : ℤ × ℤ} {i : Fin d.m} {k : ℕ}
    (h : k < (sortedCand d nℓ u' i).length) :
    wtower d nℓ vl u' i k =
      (sortedCand d nℓ u' i)[towerIdx vl u' (sortedCand d nℓ u' i).length k]'(towerIdx_lt h) := by
  unfold wtower; simp [h]

theorem wtower_last (d : DecompData ξ) (nℓ vl u' : ℤ × ℤ) (i : Fin d.m) :
    wtower d nℓ vl u' i (sortedCand d nℓ u' i).length = -vl := by
  unfold wtower; simp

theorem mem_candSet_wtower {d : DecompData ξ} {nℓ vl u' : ℤ × ℤ} {i : Fin d.m} {k : ℕ}
    (h : k < (sortedCand d nℓ u' i).length) :
    wtower d nℓ vl u' i k ∈ candSet d nℓ u' i := by
  rw [wtower_eq_getElem h, ← mem_sortedCand]
  exact List.getElem_mem _

theorem mem_candSet_getElem {d : DecompData ξ} {nℓ u' : ℤ × ℤ} {i : Fin d.m} {k : ℕ}
    (h : k < (sortedCand d nℓ u' i).length) :
    (sortedCand d nℓ u' i)[k] ∈ candSet d nℓ u' i := by
  rw [← mem_sortedCand]
  exact List.getElem_mem h

/-! ## §6. The sign of `det v (-vl)` is constant across the whole half-plane

Since `vl ⊥ nℓ`, `key_identity nℓ v vl` (with `dot nℓ vl = 0`) gives
`(nℓ.1²+nℓ.2²) · det v vl = det nℓ vl · dot nℓ v` for every `v` — so `sign (det v vl)` depends
only on `sign (dot nℓ v)` (via the fixed constant `det nℓ vl`), not on `v` itself. Both every
candidate (`dot nℓ (·) < 0`, `dot_wgen_neg`) and `u'` itself (`dot nℓ u' = -1 < 0`, `hnu`) lie in
this same half-plane, so `sign (det v vl)` is the SAME for every candidate and for `u'` — no
`hadj` needed for this part. -/

theorem det_vl_sign_eq_of_dot_nl_neg {nℓ vl a b : ℤ × ℤ} (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (ha : dot nℓ a < 0) (hb : dot nℓ b < 0) :
    0 < det a vl ↔ 0 < det b vl := by
  have hnℓ_ne : nℓ ≠ 0 := (Nivat.LE2.prim_iff_primitive.mp hprim).ne_zero
  have hne2 : nℓ.1 ^ 2 + nℓ.2 ^ 2 ≠ 0 := by
    intro h
    apply hnℓ_ne
    have h1 : nℓ.1 = 0 := by nlinarith [sq_nonneg nℓ.1, sq_nonneg nℓ.2]
    have h2 : nℓ.2 = 0 := by nlinarith [sq_nonneg nℓ.1, sq_nonneg nℓ.2]
    exact Prod.ext h1 h2
  have hepos : (0 : ℤ) < nℓ.1 ^ 2 + nℓ.2 ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm hne2)
  have hida := key_identity nℓ a vl
  have hidb := key_identity nℓ b vl
  rw [hperp, mul_zero, sub_zero] at hida hidb
  constructor
  · intro hpa
    have hD_neg : det nℓ vl < 0 := by nlinarith [mul_pos hepos hpa]
    nlinarith [mul_pos_of_neg_of_neg hD_neg hb]
  · intro hpb
    have hD_neg : det nℓ vl < 0 := by nlinarith [mul_pos hepos hpb]
    nlinarith [mul_pos_of_neg_of_neg hD_neg ha]

/-- Any vector with `dot nℓ v < 0` (in particular, any tower candidate, or `u'` via `hnu`) is
never parallel to `vl` — the algebraic core of both `det_vl_sign_eq_of_dot_nl_neg`'s nonzero
side conditions and the `-vl`-end boundary case. -/
theorem det_ne_zero_of_dot_nl_neg {vl nℓ v : ℤ × ℤ} (hvl_prim : Primitive vl)
    (hperp : dot nℓ vl = 0) (hv : dot nℓ v < 0) : det v vl ≠ 0 := by
  intro hd
  have hd' : det vl v = 0 := by
    have hskew := det_skew v vl
    omega
  obtain ⟨c, hc⟩ := Nivat.eq_zsmul_of_det_eq_zero hvl_prim hd'
  have hcalc : dot nℓ v = c * dot nℓ vl := by
    rw [hc, dot_comm, dot_smul, dot_comm vl nℓ]
  rw [hperp, mul_zero] at hcalc
  omega

/-- The distinguishing sign: `0 < det u' (-vl)` iff `det u' vl < 0`. Combined with
`det_vl_sign_eq_of_dot_nl_neg`, every candidate `w` has `det w (-vl)` with this SAME sign. -/
theorem det_w_negvl_sign_eq {vl nℓ u' : ℤ × ℤ} (d : DecompData ξ)
    (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0) (hnu : dot nℓ u' < 0)
    {w : ℤ × ℤ} (hw : w ∈ candSet d nℓ u' i) :
    (0 < det w (-vl)) ↔ (0 < det u' (-vl)) := by
  have hdw : dot nℓ w < 0 := dot_of_mem_candSet d hvl_prim hprim hperp i hdoth hw
  have hiff : (0 < det w vl) ↔ (0 < det u' vl) :=
    det_vl_sign_eq_of_dot_nl_neg hprim hperp hdw hnu
  have hnew : det w vl ≠ 0 := det_ne_zero_of_dot_nl_neg hvl_prim hperp hdw
  have hneu : det u' vl ≠ 0 := det_ne_zero_of_dot_nl_neg hvl_prim hperp hnu
  have heqw : det w (-vl) = - det w vl := by
    simp only [det, Prod.fst_neg, Prod.snd_neg]; ring
  have hequ : det u' (-vl) = - det u' vl := by
    simp only [det, Prod.fst_neg, Prod.snd_neg]; ring
  rw [heqw, hequ]
  omega

/-- Strict `det`-positivity, in the direction `sign (det u' (-vl))`, for every consecutive pair
of tower directions strictly inside `sortedCand` (i.e. not touching the `-vl` boundary):
`towerIdx` reads `sortedCand` in the direction that makes this so. -/
theorem hside_interior {vl nℓ u' : ℤ × ℤ} (d : DecompData ξ)
    (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0) (hnℓ_ne : nℓ ≠ 0) (hnu : dot nℓ u' < 0)
    {k : ℕ} (hk : k + 1 < (sortedCand d nℓ u' i).length) :
    0 < det (wtower d nℓ vl u' i k) (wtower d nℓ vl u' i (k + 1)) *
        det (wtower d nℓ vl u' i k) (-vl) := by
  have hk0 : k < (sortedCand d nℓ u' i).length := by omega
  have hwk : wtower d nℓ vl u' i k ∈ candSet d nℓ u' i := mem_candSet_wtower hk0
  have hdw : dot nℓ (wtower d nℓ vl u' i k) < 0 :=
    dot_of_mem_candSet d hvl_prim hprim hperp i hdoth hwk
  have hne_w : det (wtower d nℓ vl u' i k) vl ≠ 0 := det_ne_zero_of_dot_nl_neg hvl_prim hperp hdw
  have hne_u : det u' vl ≠ 0 := det_ne_zero_of_dot_nl_neg hvl_prim hperp hnu
  have hiff : (0 < det (wtower d nℓ vl u' i k) vl) ↔ (0 < det u' vl) :=
    det_vl_sign_eq_of_dot_nl_neg hprim hperp hdw hnu
  have heq_w : det (wtower d nℓ vl u' i k) (-vl) = - det (wtower d nℓ vl u' i k) vl := by
    simp only [det, Prod.fst_neg, Prod.snd_neg]; ring
  by_cases hcase : 0 < det u' vl
  · -- backward read: towerIdx k = len-1-k > towerIdx (k+1) = len-2-k
    have heq0 : wtower d nℓ vl u' i k =
        (sortedCand d nℓ u' i)[(sortedCand d nℓ u' i).length - 1 - k] := by
      rw [wtower_eq_getElem hk0]; congr 1; unfold towerIdx; simp [hcase]
    have heq1 : wtower d nℓ vl u' i (k + 1) =
        (sortedCand d nℓ u' i)[(sortedCand d nℓ u' i).length - 1 - (k + 1)] := by
      rw [wtower_eq_getElem hk]; congr 1; unfold towerIdx; simp [hcase]
    have hlt1 : (sortedCand d nℓ u' i).length - 1 - (k + 1) < (sortedCand d nℓ u' i).length := by omega
    have hlt0 : (sortedCand d nℓ u' i).length - 1 - k < (sortedCand d nℓ u' i).length := by omega
    have hpw := sortedCand_pairwise d nℓ u' i
    have hrel := List.pairwise_iff_getElem.mp hpw
      ((sortedCand d nℓ u' i).length - 1 - (k + 1)) ((sortedCand d nℓ u' i).length - 1 - k)
      hlt1 hlt0 (by omega)
    have hne := List.pairwise_iff_getElem.mp (sortedCand_nodup d nℓ u' i)
      ((sortedCand d nℓ u' i).length - 1 - (k + 1)) ((sortedCand d nℓ u' i).length - 1 - k)
      hlt1 hlt0 (by omega)
    have hposrev : 0 < det
        (sortedCand d nℓ u' i)[(sortedCand d nℓ u' i).length - 1 - (k + 1)]
        (sortedCand d nℓ u' i)[(sortedCand d nℓ u' i).length - 1 - k] :=
      det_pos_of_sortedCand_pairwise d hvl_prim hprim hperp i hdoth hnℓ_ne
        (mem_candSet_getElem hlt1) (mem_candSet_getElem hlt0) hne hrel
    have hnegfwd : det (wtower d nℓ vl u' i k) (wtower d nℓ vl u' i (k + 1)) < 0 := by
      rw [heq0, heq1]
      have hskew := det_skew
        (sortedCand d nℓ u' i)[(sortedCand d nℓ u' i).length - 1 - (k + 1)]
        (sortedCand d nℓ u' i)[(sortedCand d nℓ u' i).length - 1 - k]
      omega
    have hwvl_pos : 0 < det (wtower d nℓ vl u' i k) vl := hiff.mpr hcase
    have hwneg : det (wtower d nℓ vl u' i k) (-vl) < 0 := by rw [heq_w]; omega
    exact mul_pos_of_neg_of_neg hnegfwd hwneg
  · -- forward read: towerIdx k = k < towerIdx (k+1) = k+1
    have hwvl_neg : det (wtower d nℓ vl u' i k) vl < 0 := by
      rcases lt_or_gt_of_ne hne_w with h | h
      · exact h
      · exact absurd (hiff.mp h) hcase
    have heq0 : wtower d nℓ vl u' i k = (sortedCand d nℓ u' i)[k] := by
      rw [wtower_eq_getElem hk0]; congr 1; unfold towerIdx; simp [hcase]
    have heq1 : wtower d nℓ vl u' i (k + 1) = (sortedCand d nℓ u' i)[k + 1] := by
      rw [wtower_eq_getElem hk]; congr 1; unfold towerIdx; simp [hcase]
    have hpw := sortedCand_pairwise d nℓ u' i
    have hrel := List.pairwise_iff_getElem.mp hpw k (k + 1) hk0 hk (by omega)
    have hne := List.pairwise_iff_getElem.mp (sortedCand_nodup d nℓ u' i) k (k + 1) hk0 hk (by omega)
    have hposfwd : 0 < det (wtower d nℓ vl u' i k) (wtower d nℓ vl u' i (k + 1)) := by
      rw [heq0, heq1]
      exact det_pos_of_sortedCand_pairwise d hvl_prim hprim hperp i hdoth hnℓ_ne
        (mem_candSet_getElem hk0) (mem_candSet_getElem hk) hne hrel
    have hwpos : 0 < det (wtower d nℓ vl u' i k) (-vl) := by rw [heq_w]; omega
    exact mul_pos hposfwd hwpos

/-- The `-vl`-end boundary case of the unified `hside`: at the last transition (last tower
candidate to `-vl`), the product is a nonzero square, hence positive — independent of the
forward/backward reading direction. -/
theorem hside_boundary_vl {vl nℓ u' : ℤ × ℤ} (d : DecompData ξ)
    (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0)
    (hpos : 0 < (sortedCand d nℓ u' i).length) :
    0 < det (wtower d nℓ vl u' i ((sortedCand d nℓ u' i).length - 1))
          (wtower d nℓ vl u' i (sortedCand d nℓ u' i).length) *
        det (wtower d nℓ vl u' i ((sortedCand d nℓ u' i).length - 1)) (-vl) := by
  rw [wtower_last]
  set k := (sortedCand d nℓ u' i).length - 1 with hk_def
  have hk : k < (sortedCand d nℓ u' i).length := by omega
  have hwk : wtower d nℓ vl u' i k ∈ candSet d nℓ u' i := mem_candSet_wtower hk
  have hdv : dot nℓ (wtower d nℓ vl u' i k) < 0 :=
    dot_of_mem_candSet d hvl_prim hprim hperp i hdoth hwk
  have hne : det (wtower d nℓ vl u' i k) vl ≠ 0 := det_ne_zero_of_dot_nl_neg hvl_prim hperp hdv
  have hne' : det (wtower d nℓ vl u' i k) (-vl) ≠ 0 := by
    intro h0
    apply hne
    have heq : det (wtower d nℓ vl u' i k) (-vl) = - det (wtower d nℓ vl u' i k) vl := by
      simp only [det, Prod.fst_neg, Prod.snd_neg]; ring
    omega
  have hsq : (0 : ℤ) ≤ (det (wtower d nℓ vl u' i k) (-vl)) *
      (det (wtower d nℓ vl u' i k) (-vl)) := mul_self_nonneg _
  rcases hsq.lt_or_eq with h | h
  · exact h
  · exact absurd (mul_self_eq_zero.mp h.symm) hne'

/-! ## §7. The `u'`-end: `hadj` forces `sign (det w u') = sign (det w vl)` for every candidate

Team-lead 2026-09-22 (Lemma H). Cleaner route than transporting scalars through `primPart`:
`det` is invariant under the 90°-rotation `dir` (`det (dir a) (dir b) = det a b`, pure `ring`),
and if `u, v ≠ 0` with `det u v = 0` then `det (primPart u) (primPart v) = 0` too (cancel the two
positive `primPart_spec` scalars). Chaining these: since `wgen d nℓ j` is a nonzero integer
multiple of `d.h j` (`det (wgen d nℓ j) (d.h j) = 0`, direct from `orientGen`), its own normal
`genPerp' (wgen d nℓ j)` is parallel to `genPerp' (d.h j)`, hence (`eq_or_neg_of_prim_of_det_eq_zero`,
both primitive) equal to `±genPerp' (d.h j)` — a member of `E B` in both signs
(`genPerp'_mem_E_B`). `hadjB` on both signs then pins the sign of `dot · vl` in terms of
`dot · u'`, exactly as for `nℓ`/`dot_nl_h_ne_zero`. -/

/-- `det` is invariant under the simultaneous 90°-rotation `dir` of both arguments. -/
theorem det_dir_dir (a b : ℤ × ℤ) : det (Nivat.LE2.dir a) (Nivat.LE2.dir b) = det a b := by
  simp only [det, Nivat.LE2.dir]; ring

/-- `primPart` preserves vanishing of `det` (cancel the two positive `primPart_spec` scalars). -/
theorem primPart_det_eq_zero_of_det_eq_zero {u v : ℤ × ℤ} (hu : u ≠ 0) (hv : v ≠ 0)
    (h : det u v = 0) : det (Nivat.LE2.primPart u) (Nivat.LE2.primPart v) = 0 := by
  obtain ⟨_, Gu, hGu, hequ⟩ := Nivat.LE2.primPart_spec hu
  obtain ⟨_, Gv, hGv, heqv⟩ := Nivat.LE2.primPart_spec hv
  have hfact : det u v = Gu * Gv * det (Nivat.LE2.primPart u) (Nivat.LE2.primPart v) := by
    conv_lhs => rw [hequ, heqv]
    simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
  rw [hfact] at h
  rcases mul_eq_zero.mp h with h' | h'
  · exact absurd h' (mul_pos hGu hGv).ne'
  · exact h'

/-- `genPerp'` preserves vanishing of `det`: parallel vectors have parallel own-normals. -/
theorem genPerp'_det_eq_zero_of_det_eq_zero {a b : ℤ × ℤ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : det a b = 0) : det (Nivat.LE2.genPerp' a) (Nivat.LE2.genPerp' b) = 0 := by
  have hda : Nivat.LE2.dir a ≠ 0 := by
    intro h0; apply ha
    have h12 : a.2 = 0 ∧ a.1 = 0 := by
      simpa [Nivat.LE2.dir, Prod.ext_iff, eq_comm] using h0
    exact Prod.ext h12.2 h12.1
  have hdb : Nivat.LE2.dir b ≠ 0 := by
    intro h0; apply hb
    have h12 : b.2 = 0 ∧ b.1 = 0 := by
      simpa [Nivat.LE2.dir, Prod.ext_iff, eq_comm] using h0
    exact Prod.ext h12.2 h12.1
  have hdir0 : det (Nivat.LE2.dir a) (Nivat.LE2.dir b) = 0 := by rw [det_dir_dir]; exact h
  exact primPart_det_eq_zero_of_det_eq_zero hda hdb hdir0

/-- The candidate `wgen d nℓ j` is a nonzero integer multiple of `d.h j` (via `orientGen`). -/
theorem det_wgen_h_eq_zero (d : DecompData ξ) {vl nℓ : ℤ × ℤ}
    (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0) {j : Fin d.m} (hij : j ≠ i) :
    det (wgen d nℓ j) (d.h j) = 0 := by
  have hne : orientGen d nℓ j ≠ 0 := by
    intro h0
    have := dot_orientGen_neg d hvl_prim hprim hperp i hdoth hij
    rw [h0] at this; simp [dot] at this
  obtain ⟨_, G, hGpos, hGeq⟩ := Nivat.LE2.primPart_spec hne
  have horient : orientGen d nℓ j = d.h j ∨ orientGen d nℓ j = -(d.h j) := by
    unfold orientGen; split_ifs <;> simp
  have hzz : det (wgen d nℓ j) (wgen d nℓ j) = 0 := by simp only [det]; ring
  have hwgen_eq : wgen d nℓ j = Nivat.LE2.primPart (orientGen d nℓ j) := rfl
  rcases horient with heq | heq
  · have : d.h j = G • wgen d nℓ j := by rw [← heq, hwgen_eq]; exact hGeq
    rw [this]
    simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at hzz ⊢
    nlinarith [hzz]
  · have hh : d.h j = -(G • wgen d nℓ j) := by
      have h1 : -(orientGen d nℓ j) = d.h j := by rw [heq, neg_neg]
      rw [← h1, hGeq, hwgen_eq]
    rw [hh]
    simp only [det, Prod.fst_neg, Prod.snd_neg, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at hzz ⊢
    nlinarith [hzz]

/-- Every candidate `w`'s own normal is `±genPerp' (d.h j)`, hence both signs of it lie in
`E B` (via `genPerp'_mem_E_B`, which already gives both signs of `genPerp' (d.h j)`). -/
theorem genPerp'_wgen_mem_E_B {B : Set (ℤ × ℤ)} (d : DecompData ξ) {vl nℓ : ℤ × ℤ}
    (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (henv : Nivat.LE2.EnvOf (↑d.Sphi : Set (ℤ × ℤ)) B)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0) {j : Fin d.m} (hij : j ≠ i) :
    Nivat.LE2.genPerp' (wgen d nℓ j) ∈ E B ∧
    -Nivat.LE2.genPerp' (wgen d nℓ j) ∈ E B := by
  have hmem := genPerp'_mem_E_B d henv j
  have hwne : wgen d nℓ j ≠ 0 := (wgen_prim d hvl_prim hprim hperp i hdoth hij).ne_zero
  have hhne : d.h j ≠ 0 := d.h_ne j
  have hd0 : det (wgen d nℓ j) (d.h j) = 0 :=
    det_wgen_h_eq_zero d hvl_prim hprim hperp i hdoth hij
  have hg0 : det (Nivat.LE2.genPerp' (wgen d nℓ j)) (Nivat.LE2.genPerp' (d.h j)) = 0 :=
    genPerp'_det_eq_zero_of_det_eq_zero hwne hhne hd0
  have hp1 : Prim (Nivat.LE2.genPerp' (wgen d nℓ j)) := Nivat.LE2.genPerp'_prim hwne
  have hp2 : Prim (Nivat.LE2.genPerp' (d.h j)) := Nivat.LE2.genPerp'_prim hhne
  rcases Nivat.LE2.eq_or_neg_of_prim_of_det_eq_zero hp1 hp2 hg0 with heq | heq
  · rw [← heq]; exact hmem
  · have hgw : Nivat.LE2.genPerp' (wgen d nℓ j) = -Nivat.LE2.genPerp' (d.h j) := by
      rw [heq, neg_neg]
    refine ⟨?_, ?_⟩
    · rw [hgw]; exact hmem.2
    · rw [hgw, neg_neg]; exact hmem.1

/-- The candidate's normal is never perpendicular to `vl` (mirrors `dot_nl_h_ne_zero`, with the
candidate's own normal playing the role `nℓ` plays there): if it were, `wgen d nℓ j` would be
parallel to `vl`, hence (via `orientGen`) `d.h j` would too, contradicting `h_dir`. -/
theorem dot_genPerp'_wgen_vl_ne_zero (d : DecompData ξ) {vl nℓ : ℤ × ℤ}
    (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0) {j : Fin d.m} (hij : j ≠ i) :
    dot (Nivat.LE2.genPerp' (wgen d nℓ j)) vl ≠ 0 := by
  intro hz
  have hwne : wgen d nℓ j ≠ 0 := (wgen_prim d hvl_prim hprim hperp i hdoth hij).ne_zero
  have hdw : dot (Nivat.LE2.genPerp' (wgen d nℓ j)) (wgen d nℓ j) = 0 := by
    rw [dot_comm]; exact Nivat.LE2.dot_genPerp' hwne
  have hnw_ne : Nivat.LE2.genPerp' (wgen d nℓ j) ≠ 0 :=
    (Nivat.LE2.genPerp'_prim hwne).ne_zero
  have hdvw : det vl (wgen d nℓ j) = 0 :=
    Nivat.LE2.det_eq_zero_of_dot_eq_zero hnw_ne hz hdw
  have hd0 : det (wgen d nℓ j) (d.h j) = 0 :=
    det_wgen_h_eq_zero d hvl_prim hprim hperp i hdoth hij
  obtain ⟨c, hc⟩ := Nivat.eq_zsmul_of_det_eq_zero hvl_prim hdvw
  have hcne : c ≠ 0 := by
    intro h0; apply hwne; rw [hc, h0, zero_smul]
  have hdethj : det vl (d.h j) = 0 := by
    have hcd : det (c • vl) (d.h j) = 0 := by rw [← hc]; exact hd0
    have hexp : det (c • vl) (d.h j) = c * det vl (d.h j) := by
      simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
    rw [hexp] at hcd
    rcases mul_eq_zero.mp hcd with h' | h'
    · exact absurd h' hcne
    · exact h'
  obtain ⟨e, he⟩ := Nivat.eq_zsmul_of_det_eq_zero hvl_prim hdethj
  obtain ⟨ci, hci⟩ := h_i_eq_zsmul_vl d hvl_prim hprim hperp i hdoth
  apply d.h_dir j i hij
  rw [he, hci]
  simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

/-! ### Lemma H: `hadj` pins `sign (det w u')` to `sign (det w vl)` for every candidate

`genPerp'` of a *primitive* vector is literally `dir` (no further normalisation needed, since
`dir` preserves `Prim`), so `dot x (genPerp' w) = dot x (dir w) = det w x` (`dot_dir_eq_det`)
identifies `det w x` with `dot x n_w` where `n_w := genPerp' w`. `hadjB` applied to `n_w` and to
`-n_w` (both in `E B`, via `genPerp'_wgen_mem_E_B`) rules out `dot n_w vl` and `dot n_w u'`
having strictly *opposite* signs (`no_opposite_sign_of_hadjB`, unconditional, landed below).
Turning "no opposite sign" into the full iff needs one more fact: `dot n_w u' ≠ 0`.

**Resolved (team-lead 2026-09-22):** unlike the `vl`-side (`dot_genPerp'_wgen_vl_ne_zero`, which
uses `h_i_eq_zsmul_vl` + `d.h_dir` to rule out `w ∥ vl`), there is no candidate-indexed generator
of `u'` in scope to run the same argument for `u'`. If `dot n_w u' = 0` then (since `n_w ≠ 0`
is `⊥` to both `w` and `u'`) `w ∥ u'`; as both are primitive (`w` via `wgen_prim`, `u'` via
`prim_u'_of_hunimod` below, from `hunimod : det u' vl = ±1`), `eq_or_neg_of_prim_of_det_eq_zero`
gives `w = u' ∨ w = -u'`. `w = -u'` is excluded (`dot nℓ w < 0` vs `dot nℓ u' < 0` would force
`dot nℓ w > 0`, contradiction — `det_ne_zero_wgen_u'_of_ne` below); `w = u'` is now excluded by
construction — `candSet` (§4) is defined with `u'` erased from the image
(`((univ.erase i).image (wgen d nℓ)).erase u'`), so every `w ∈ candSet d nℓ u' i` already comes
with `w ≠ u'` free (`ne_u'_of_mem_candSet`). Dropping `u'` from the interior sweep loses nothing
geometrically: the `u'`-ray is already covered by `coneRegion`/the tower's base step.
`det_w_u'_sign_eq_of_hadjB` below still takes `hwu' : wgen d nℓ j ≠ u'` as an explicit hypothesis
(kept as a generic helper, independent of `candSet`'s particular filtering choice); its callers
in this file (`hside_boundary_u'`) now derive it in one line from `ne_u'_of_mem_candSet` instead
of assuming it externally. -/

theorem prim_dir_of_prim {v : ℤ × ℤ} (hv : Prim v) : Prim (Nivat.LE2.dir v) := by
  unfold Prim Int.gcd at hv
  unfold Prim Nivat.LE2.dir Int.gcd
  simpa [Int.natAbs_neg, Nat.gcd_comm] using hv

theorem primPart_eq_self_of_prim {v : ℤ × ℤ} (hv : Prim v) : Nivat.LE2.primPart v = v := by
  have hgcd : (Int.gcd v.1 v.2 : ℤ) = 1 := by exact_mod_cast hv
  unfold Nivat.LE2.primPart
  rw [hgcd]; simp

theorem genPerp'_eq_dir_of_prim {v : ℤ × ℤ} (hv : Prim v) :
    Nivat.LE2.genPerp' v = Nivat.LE2.dir v :=
  primPart_eq_self_of_prim (prim_dir_of_prim hv)

theorem det_eq_dot_genPerp' {w : ℤ × ℤ} (hw : Prim w) (x : ℤ × ℤ) :
    det w x = dot x (Nivat.LE2.genPerp' w) := by
  rw [genPerp'_eq_dir_of_prim hw]
  exact (Nivat.HsuppCaseCW.dot_dir_eq_det x w).symm

/-- `{u', vl}` being a `det = ±1` basis forces `u'` itself to be primitive (any common factor of
`u'`'s coordinates would divide the determinant). -/
theorem prim_u'_of_hunimod {u' vl : ℤ × ℤ} (hunimod : det u' vl = 1 ∨ det u' vl = -1) :
    Prim u' := by
  have hg1 : (Int.gcd u'.1 u'.2 : ℤ) ∣ u'.1 := Int.gcd_dvd_left u'.1 u'.2
  have hg2 : (Int.gcd u'.1 u'.2 : ℤ) ∣ u'.2 := Int.gcd_dvd_right u'.1 u'.2
  have hgdvd : (Int.gcd u'.1 u'.2 : ℤ) ∣ det u' vl := by
    unfold det
    exact dvd_sub (dvd_mul_of_dvd_left hg1 vl.2) (dvd_mul_of_dvd_left hg2 vl.1)
  have hgdvd1 : (Int.gcd u'.1 u'.2 : ℤ) ∣ 1 := by
    rcases hunimod with h | h
    · rw [h] at hgdvd; exact hgdvd
    · rw [h] at hgdvd; exact (dvd_neg).mp hgdvd
  have hgdvd1' : Int.gcd u'.1 u'.2 ∣ 1 := by exact_mod_cast hgdvd1
  exact Nat.dvd_one.mp hgdvd1'

/-- The unconditional half of Lemma H: `hadjB` alone (no nonzero side condition) already rules
out `det w vl` and `det w u'` having strictly opposite sign, for every candidate `w`. -/
theorem no_opposite_sign_of_hadjB {B : Set (ℤ × ℤ)} (d : DecompData ξ) {vl nℓ u' : ℤ × ℤ}
    (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (henv : Nivat.LE2.EnvOf (↑d.Sphi : Set (ℤ × ℤ)) B)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0)
    (hadjB : ∀ n ∈ E B, ¬ (dot n vl < 0 ∧ 0 < dot n u')) {j : Fin d.m} (hij : j ≠ i) :
    ¬ (det (wgen d nℓ j) vl < 0 ∧ 0 < det (wgen d nℓ j) u') ∧
    ¬ (0 < det (wgen d nℓ j) vl ∧ det (wgen d nℓ j) u' < 0) := by
  set w := wgen d nℓ j with hw_def
  have hwprim : Prim w :=
    Nivat.LE2.prim_iff_primitive.mpr (wgen_prim d hvl_prim hprim hperp i hdoth hij)
  set n_w := Nivat.LE2.genPerp' w with hnw_def
  have hmem := genPerp'_wgen_mem_E_B d hvl_prim hprim hperp henv i hdoth hij
  have hdw_vl : det w vl = dot n_w vl := by
    rw [det_eq_dot_genPerp' hwprim vl, dot_comm]
  have hdw_u' : det w u' = dot n_w u' := by
    rw [det_eq_dot_genPerp' hwprim u', dot_comm]
  have h1 := hadjB n_w hmem.1
  have h2 := hadjB (-n_w) hmem.2
  refine ⟨?_, ?_⟩
  · intro hc
    rw [hdw_vl] at hc; rw [hdw_u'] at hc
    exact h1 hc
  · intro hc
    rw [hdw_vl] at hc; rw [hdw_u'] at hc
    apply h2
    constructor
    · rw [dot_neg_left]; omega
    · rw [dot_neg_left]; omega

/-- If a candidate `wgen d nℓ j` is not literally `u'`, its determinant with `u'` is nonzero:
zero would force (both primitive) `wgen d nℓ j = u' ∨ wgen d nℓ j = -u'`, and the second case
flips the sign of `dot nℓ (·)` (`< 0` for the candidate, but `-u'` would force `> 0` since
`hnu : dot nℓ u' < 0`), a contradiction. -/
theorem det_ne_zero_wgen_u'_of_ne {vl nℓ u' : ℤ × ℤ} (d : DecompData ξ)
    (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0)
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) (hnu : dot nℓ u' < 0)
    {j : Fin d.m} (hij : j ≠ i) (hwu' : wgen d nℓ j ≠ u') :
    det (wgen d nℓ j) u' ≠ 0 := by
  intro hd
  have hwprim : Prim (wgen d nℓ j) :=
    Nivat.LE2.prim_iff_primitive.mpr (wgen_prim d hvl_prim hprim hperp i hdoth hij)
  have hu'prim : Prim u' := prim_u'_of_hunimod hunimod
  rcases Nivat.LE2.eq_or_neg_of_prim_of_det_eq_zero hwprim hu'prim hd with heq | heq
  · exact hwu' heq.symm
  · have hdw : dot nℓ (wgen d nℓ j) < 0 := dot_wgen_neg d hvl_prim hprim hperp i hdoth hij
    have hwu'neg : wgen d nℓ j = -u' := by
      rw [heq]; ring
    rw [hwu'neg, dot_comm, dot_neg_left, dot_comm] at hdw
    omega

/-- **Lemma H (full form).** For every candidate `w = wgen d nℓ j` other than `u'` itself,
`hadj`/`hadjB` pins `sign (det w u')` to `sign (det w vl)`: combined with the unconditional
"no opposite sign" fact (`no_opposite_sign_of_hadjB`) and the two nonvanishing facts
(`det w vl ≠ 0` from `det_ne_zero_of_dot_nl_neg`, `det w u' ≠ 0` from
`det_ne_zero_wgen_u'_of_ne`, both needing `hwu' : w ≠ u'` for the latter), the two nonzero
integers `det w vl` and `det w u'` can never land on opposite sides of `0`, hence agree. -/
theorem det_w_u'_sign_eq_of_hadjB {B : Set (ℤ × ℤ)} (d : DecompData ξ) {vl nℓ u' : ℤ × ℤ}
    (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (henv : Nivat.LE2.EnvOf (↑d.Sphi : Set (ℤ × ℤ)) B)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0)
    (hadjB : ∀ n ∈ E B, ¬ (dot n vl < 0 ∧ 0 < dot n u'))
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) (hnu : dot nℓ u' < 0)
    {j : Fin d.m} (hij : j ≠ i) (hwu' : wgen d nℓ j ≠ u') :
    0 < det (wgen d nℓ j) vl ↔ 0 < det (wgen d nℓ j) u' := by
  obtain ⟨h1, h2⟩ := no_opposite_sign_of_hadjB d hvl_prim hprim hperp henv i hdoth hadjB hij
  have hvne : det (wgen d nℓ j) vl ≠ 0 :=
    det_ne_zero_of_dot_nl_neg hvl_prim hperp (dot_wgen_neg d hvl_prim hprim hperp i hdoth hij)
  have hune : det (wgen d nℓ j) u' ≠ 0 :=
    det_ne_zero_wgen_u'_of_ne d hvl_prim hprim hperp i hdoth hunimod hnu hij hwu'
  omega

/-- Pure order-theoretic helper: two nonzero integers whose positivity is `Iff`-linked always
have positive product (either both positive, or both negative). -/
theorem mul_pos_of_iff_pos_ne_zero {a b : ℤ} (hiff : 0 < a ↔ 0 < b) (ha : a ≠ 0) (hb : b ≠ 0) :
    0 < a * b := by
  rcases lt_or_gt_of_ne ha with h | h
  · have hb' : b < 0 := by
      rcases lt_or_gt_of_ne hb with h2 | h2
      · exact h2
      · exact absurd (hiff.mpr h2) (by omega)
    exact mul_pos_of_neg_of_neg h hb'
  · exact mul_pos h (hiff.mp h)

/-- **The `u'`-boundary case of `hside`** (the step from `u'` into the first tower candidate).
Combines Lemma G (`det_vl_sign_eq_of_dot_nl_neg`, `sign (det w vl) = sign (det u' vl)`) with
Lemma H (`det_w_u'_sign_eq_of_hadjB`, `sign (det w vl) = sign (det w u')`, needs `w ≠ u'`) to get
`sign (det w u') = sign (det u' vl)`, hence (via `det_skew`/sign-flip algebra)
`0 < det u' w * det u' (-vl)`. **Resolved (team-lead 2026-09-22):** `w ≠ u'` no longer needs to be
threaded in as a hypothesis — `candSet` is now defined with `u'` erased (see `candSet`'s
docstring), so `wtower d nℓ vl u' i 0 ∈ candSet d nℓ u' i` already gives `w ≠ u'` directly via
`ne_u'_of_mem_candSet`. -/
theorem hside_boundary_u' {B : Set (ℤ × ℤ)} {vl nℓ u' : ℤ × ℤ} (d : DecompData ξ)
    (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (henv : Nivat.LE2.EnvOf (↑d.Sphi : Set (ℤ × ℤ)) B)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0)
    (hadjB : ∀ n ∈ E B, ¬ (dot n vl < 0 ∧ 0 < dot n u'))
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) (hnu : dot nℓ u' < 0)
    (hpos : 0 < (sortedCand d nℓ u' i).length) :
    0 < det u' (wtower d nℓ vl u' i 0) * det u' (-vl) := by
  have hw0 : wtower d nℓ vl u' i 0 ∈ candSet d nℓ u' i := mem_candSet_wtower hpos
  have hwu' : wtower d nℓ vl u' i 0 ≠ u' := ne_u'_of_mem_candSet hw0
  obtain ⟨_, hw0_img⟩ := Finset.mem_erase.mp hw0
  obtain ⟨j, hj_mem, hj⟩ := Finset.mem_image.mp hw0_img
  have hij : j ≠ i := (Finset.mem_erase.mp hj_mem).1
  have hjne : wgen d nℓ j ≠ u' := by rw [hj]; exact hwu'
  have hiffH : 0 < det (wgen d nℓ j) vl ↔ 0 < det (wgen d nℓ j) u' :=
    det_w_u'_sign_eq_of_hadjB d hvl_prim hprim hperp henv i hdoth hadjB hunimod hnu hij hjne
  have hdw : dot nℓ (wgen d nℓ j) < 0 := dot_wgen_neg d hvl_prim hprim hperp i hdoth hij
  have hiffG : 0 < det (wgen d nℓ j) vl ↔ 0 < det u' vl :=
    det_vl_sign_eq_of_dot_nl_neg hprim hperp hdw hnu
  have hune : det (wgen d nℓ j) u' ≠ 0 :=
    det_ne_zero_wgen_u'_of_ne d hvl_prim hprim hperp i hdoth hunimod hnu hij hjne
  have hvne : det u' vl ≠ 0 := det_ne_zero_of_dot_nl_neg hvl_prim hperp hnu
  have hprod : 0 < det (wgen d nℓ j) u' * det u' vl :=
    mul_pos_of_iff_pos_ne_zero (hiffH.symm.trans hiffG) hune hvne
  have hskew : det u' (wgen d nℓ j) = - det (wgen d nℓ j) u' := det_skew u' (wgen d nℓ j)
  have heqneg : det u' (-vl) = - det u' vl := by
    simp only [det, Prod.fst_neg, Prod.snd_neg]; ring
  rw [← hj, heqneg, hskew]
  nlinarith [hprod]

/-! ## §8. The half-turn lemma: transitive `det`-positivity across the whole tower chain

Team-lead 2026-09-22 assignment (after `hside` is complete): the `hbase` induction that will
land `RegionSteps.lean:1735-1744` needs, at each tower step `I`, that every *earlier* direction
in the chain `u', wtower 0, …, wtower(len-1)` sits on one side of the edge normal at step `I`
(`blueprint/LEAF-TOWER.md`'s "半圈引理"). The engine is `Nivat.PolyChain.det_pos_trans`
(`Nivat/External/Colle/PolyChain.lean:42`), applied repeatedly along the whole chain, not just
to consecutive `hside` steps. `extChain` packages `u'` as index `0` and `wtower t` as index
`t + 1`; `det_pos_extChain` gives the fully transitive statement
`0 < det (extChain j) (extChain k) * det u' (-vl)` for every `j < k ≤ len`
(`len := (sortedCand d nℓ u' i).length`), generalizing the three `hside_*` lemmas (which only cover
`k = j + 1`) to arbitrary index gaps — the product form matches the file's existing `hside_*`
convention so it packages the two possible sweep directions (`hunimod`'s sign) uniformly. -/

/-- `u'` prepended to the tower: index `0` is `u'`, index `t + 1` is `wtower t`. -/
noncomputable def extChain (d : DecompData ξ) (nℓ vl u' : ℤ × ℤ) (i : Fin d.m) : ℕ → ℤ × ℤ
  | 0 => u'
  | (t + 1) => wtower d nℓ vl u' i t

theorem dot_extChain_neg {vl nℓ u' : ℤ × ℤ} (d : DecompData ξ)
    (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0) (hnu : dot nℓ u' < 0)
    {t : ℕ} (ht : t ≤ (sortedCand d nℓ u' i).length) :
    dot nℓ (extChain d nℓ vl u' i t) < 0 := by
  cases t with
  | zero => exact hnu
  | succ t' =>
    have ht' : t' < (sortedCand d nℓ u' i).length := by omega
    exact dot_of_mem_candSet d hvl_prim hprim hperp i hdoth (mem_candSet_wtower ht')

/-- Pure order-theoretic helper (converse of `mul_pos_of_iff_pos_ne_zero`): a strictly positive
product `a * b` forces `(0 < a) ↔ (0 < b)`. -/
theorem iff_pos_of_mul_pos {a b : ℤ} (hab : 0 < a * b) : (0 < a ↔ 0 < b) := by
  constructor
  · intro ha
    by_contra hb; push_neg at hb
    exact absurd (mul_nonpos_of_nonneg_of_nonpos ha.le hb) (by linarith)
  · intro hb
    by_contra ha; push_neg at ha
    exact absurd (mul_nonpos_of_nonpos_of_nonneg ha hb.le) (by linarith)

/-- Every consecutive `extChain` step has `det`-sign matching `det u' (-vl)`, and is itself
nonzero — both read directly off the `hside_boundary_u'`/`hside_interior` product facts (if the
step were `0`, the product would vanish, contradicting strict positivity). -/
theorem det_extChain_consec {B : Set (ℤ × ℤ)} (d : DecompData ξ) {vl nℓ u' : ℤ × ℤ}
    (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (henv : Nivat.LE2.EnvOf (↑d.Sphi : Set (ℤ × ℤ)) B)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0)
    (hadjB : ∀ n ∈ E B, ¬ (dot n vl < 0 ∧ 0 < dot n u'))
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) (hnu : dot nℓ u' < 0) (hnℓ_ne : nℓ ≠ 0)
    {t : ℕ} (ht : t < (sortedCand d nℓ u' i).length) :
    ((0 < det (extChain d nℓ vl u' i t) (extChain d nℓ vl u' i (t + 1))) ↔ (0 < det u' (-vl))) ∧
    det (extChain d nℓ vl u' i t) (extChain d nℓ vl u' i (t + 1)) ≠ 0 := by
  cases t with
  | zero =>
    have hpos := hside_boundary_u' d hvl_prim hprim hperp henv i hdoth hadjB hunimod hnu
      (by omega)
    refine ⟨?_, ?_⟩
    · simpa [extChain] using iff_pos_of_mul_pos hpos
    · simp only [extChain]
      intro h0; rw [h0] at hpos; simp at hpos
  | succ t' =>
    have hk : t' + 1 < (sortedCand d nℓ u' i).length := ht
    have hpos := hside_interior d hvl_prim hprim hperp i hdoth hnℓ_ne hnu hk
    have ht'lt : t' < (sortedCand d nℓ u' i).length := by omega
    have hiff2 : (0 < det (wtower d nℓ vl u' i t') (-vl)) ↔ (0 < det u' (-vl)) :=
      det_w_negvl_sign_eq d hvl_prim hprim hperp i hdoth hnu (mem_candSet_wtower ht'lt)
    refine ⟨?_, ?_⟩
    · simpa [extChain] using (iff_pos_of_mul_pos hpos).trans hiff2
    · simp only [extChain]
      intro h0; rw [h0] at hpos; simp at hpos

/-- **Half-plane chain transitivity** (forward direction). If `f` stays strictly on the
`e`-positive side and each consecutive step has `0 < det (f t) (f (t+1))`, then `det (f j) (f k)`
is positive for every `j < k`, not just consecutive pairs — repeated `PolyChain.det_pos_trans`. -/
theorem det_pos_chain {f : ℕ → ℤ × ℤ} {e : ℤ × ℤ} {n : ℕ}
    (he : ∀ t, t ≤ n → 0 < dot e (f t)) (hstep : ∀ t, t < n → 0 < det (f t) (f (t + 1))) :
    ∀ j k, j < k → k ≤ n → 0 < det (f j) (f k) := by
  intro j k
  induction k with
  | zero => intro h; omega
  | succ k ih =>
    intro hjk hkn
    rcases Nat.lt_or_ge j k with hlt | hge
    · have hk1 : k ≤ n := by omega
      have hprev : 0 < det (f j) (f k) := ih hlt hk1
      have hk0 : k < n := by omega
      exact Nivat.PolyChain.det_pos_trans (he j (by omega)) (he k hk1) (he (k + 1) hkn)
        hprev (hstep k hk0)
    · have hjk' : j = k := by omega
      subst hjk'
      exact hstep j (by omega)

/-- The reversed-direction sibling of `det_pos_chain`: if each consecutive step instead has
`0 < det (f (t+1)) (f t)`, then `det (f k) (f j)` is positive for every `j < k`. -/
theorem det_pos_chain_rev {f : ℕ → ℤ × ℤ} {e : ℤ × ℤ} {n : ℕ}
    (he : ∀ t, t ≤ n → 0 < dot e (f t)) (hstep : ∀ t, t < n → 0 < det (f (t + 1)) (f t)) :
    ∀ j k, j < k → k ≤ n → 0 < det (f k) (f j) := by
  intro j k
  induction k with
  | zero => intro h; omega
  | succ k ih =>
    intro hjk hkn
    rcases Nat.lt_or_ge j k with hlt | hge
    · have hk1 : k ≤ n := by omega
      have hprev : 0 < det (f k) (f j) := ih hlt hk1
      have hk0 : k < n := by omega
      exact Nivat.PolyChain.det_pos_trans (he (k + 1) hkn) (he k hk1) (he j (by omega))
        (hstep k hk0) hprev
    · have hjk' : j = k := by omega
      subst hjk'
      exact hstep j (by omega)

/-- **Half-turn lemma.** Every pair of tower-chain indices `j < k ≤ len` (indices into
`extChain`, i.e. `u'` at `0` and `wtower t` at `t + 1`) has `det (extChain j) (extChain k)` with
the SAME sign as `det u' (-vl)` — the transitive extension of `hside_boundary_u'`/`hside_interior`
(which only cover `k = j + 1`) via `PolyChain.det_pos_trans`. This is exactly the fact the
`hbase` induction (`nprev I` sees every earlier tower direction on one side) needs. -/
theorem det_pos_extChain {B : Set (ℤ × ℤ)} (d : DecompData ξ) {vl nℓ u' : ℤ × ℤ}
    (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (henv : Nivat.LE2.EnvOf (↑d.Sphi : Set (ℤ × ℤ)) B)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0)
    (hadjB : ∀ n ∈ E B, ¬ (dot n vl < 0 ∧ 0 < dot n u'))
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) (hnu : dot nℓ u' < 0) (hnℓ_ne : nℓ ≠ 0)
    {j k : ℕ} (hjk : j < k) (hk : k ≤ (sortedCand d nℓ u' i).length) :
    0 < det (extChain d nℓ vl u' i j) (extChain d nℓ vl u' i k) * det u' (-vl) := by
  set len := (sortedCand d nℓ u' i).length with hlen
  have he : ∀ t, t ≤ len → 0 < dot (-nℓ) (extChain d nℓ vl u' i t) := by
    intro t ht
    have h := dot_extChain_neg d hvl_prim hprim hperp i hdoth hnu ht
    rw [dot_neg_left]; omega
  by_cases hc : 0 < det u' (-vl)
  · have hstep : ∀ t, t < len →
        0 < det (extChain d nℓ vl u' i t) (extChain d nℓ vl u' i (t + 1)) :=
      fun t ht => ((det_extChain_consec d hvl_prim hprim hperp henv i hdoth hadjB hunimod hnu
        hnℓ_ne ht).1).mpr hc
    have hmain := det_pos_chain he hstep j k hjk hk
    exact mul_pos hmain hc
  · push_neg at hc
    have hcne : det u' (-vl) ≠ 0 := by
      have h1 : det u' vl ≠ 0 := det_ne_zero_of_dot_nl_neg hvl_prim hperp hnu
      intro h0; apply h1
      have heqn : det u' (-vl) = - det u' vl := by
        simp only [det, Prod.fst_neg, Prod.snd_neg]; ring
      omega
    have hclt : det u' (-vl) < 0 := hc.lt_of_ne hcne
    have hstep' : ∀ t, t < len →
        0 < det (extChain d nℓ vl u' i (t + 1)) (extChain d nℓ vl u' i t) := by
      intro t ht
      obtain ⟨hiff, hne⟩ := det_extChain_consec d hvl_prim hprim hperp henv i hdoth hadjB hunimod
        hnu hnℓ_ne ht
      have hlt : det (extChain d nℓ vl u' i t) (extChain d nℓ vl u' i (t + 1)) < 0 := by
        rcases lt_or_gt_of_ne hne with h | h
        · exact h
        · exact absurd (hiff.mp h) (not_lt.mpr hclt.le)
      have hskew := det_skew (extChain d nℓ vl u' i t) (extChain d nℓ vl u' i (t + 1))
      omega
    have hmain := det_pos_chain_rev he hstep' j k hjk hk
    have hltjk : det (extChain d nℓ vl u' i j) (extChain d nℓ vl u' i k) < 0 := by
      have hskew2 := det_skew (extChain d nℓ vl u' i j) (extChain d nℓ vl u' i k)
      omega
    exact mul_pos_of_neg_of_neg hltjk hclt

/-! ## §9. The `nprev` bridge: `det_pos_extChain`'s sign statement as `dot (nprev I) d < 0`

Team-lead's `hbase` induction (`blueprint/LEAF-TOWER.md`, "补充：集成者的裁决") needs, at each
tower step `I`, an edge normal `nprev I ∈ E B` of the `wtower I`-edge with
`dot (nprev I) (wIdx I) < 0` (defining its sign) and `dot (nprev I) d ≤ 0` for every earlier
chain direction `d`. `wtower I` is primitive when `I` is a genuine candidate index
(`I < (sortedCand d nℓ u' i).length`, `prim_of_mem_candSet` via `mem_candSet_wtower`), so
`genPerp' (wtower I)` is the (unsigned) unit normal; `det_eq_dot_genPerp'` converts
`det_pos_extChain`'s `det`-sign statement between `extChain j` and `extChain (I+1) = wtower I`
into a `dot (genPerp' (wtower I)) (extChain j)`-sign statement, uniformly for every `j ≤ I`
(same `I`, same constant sign `det u' (-vl)`) — this is exactly the missing `sign` flip: pick
`nprev` to be `genPerp' (wtower I)` or its negation according to which sign of `det u' (-vl)`
holds, and the same case split gives `< 0` (not just `≤ 0`) for every `j ≤ I` at once, `wIdx I`
included as the `j = I` case (so the "fixes the sign" reading of the boundary condition is
automatic, not a separate check). -/

/-- The signed edge normal at tower step `I`: `genPerp' (wtower I)` flipped so that
`dot (nprev) (wtower I)` itself is negative (equivalently, `dot (nprev) (wIdx I) < 0` in the
blueprint's notation, since `wIdx I = extChain I` and `wtower I = extChain (I+1)` are both
covered by the `j ≤ I` range `dot_nprev_lt` below). -/
noncomputable def nprevOf (d : DecompData ξ) (nℓ vl u' : ℤ × ℤ) (i : Fin d.m) (I : ℕ) :
    ℤ × ℤ :=
  if 0 < det u' (-vl) then Nivat.LE2.genPerp' (wtower d nℓ vl u' i I)
  else -(Nivat.LE2.genPerp' (wtower d nℓ vl u' i I))

/-- **The `nprev` bridge.** For every tower step `I` inside the candidate range and every
earlier-or-equal chain index `j ≤ I` (`extChain j` ranges over `u'` and `wtower 0, …, wtower I`,
i.e. exactly `{vl-free earlier directions} ∪ {wIdx I}`), `dot (nprevOf I) (extChain j) < 0`. -/
theorem dot_nprevOf_neg {B : Set (ℤ × ℤ)} (d : DecompData ξ) {vl nℓ u' : ℤ × ℤ}
    (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (henv : Nivat.LE2.EnvOf (↑d.Sphi : Set (ℤ × ℤ)) B)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0)
    (hadjB : ∀ n ∈ E B, ¬ (dot n vl < 0 ∧ 0 < dot n u'))
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) (hnu : dot nℓ u' < 0) (hnℓ_ne : nℓ ≠ 0)
    {I j : ℕ} (hIlen : I < (sortedCand d nℓ u' i).length) (hjI : j ≤ I) :
    dot (nprevOf d nℓ vl u' i I) (extChain d nℓ vl u' i j) < 0 := by
  have hwprim : Primitive (wtower d nℓ vl u' i I) :=
    prim_of_mem_candSet d hvl_prim hprim hperp i hdoth (mem_candSet_wtower hIlen)
  have hwprim' : Prim (wtower d nℓ vl u' i I) := Nivat.LE2.prim_iff_primitive.mpr hwprim
  have hextsucc : extChain d nℓ vl u' i (I + 1) = wtower d nℓ vl u' i I := rfl
  have hkey := det_pos_extChain d hvl_prim hprim hperp henv i hdoth hadjB hunimod hnu hnℓ_ne
    (j := j) (k := I + 1) (by omega) (by omega)
  rw [hextsucc] at hkey
  have hdetflip : det (extChain d nℓ vl u' i j) (wtower d nℓ vl u' i I) =
      - dot (extChain d nℓ vl u' i j) (Nivat.LE2.genPerp' (wtower d nℓ vl u' i I)) := by
    rw [det_skew, det_eq_dot_genPerp' hwprim' (extChain d nℓ vl u' i j)]
  rw [hdetflip] at hkey
  have hcne : det u' (-vl) ≠ 0 := by
    have h1 : det u' vl ≠ 0 := det_ne_zero_of_dot_nl_neg hvl_prim hperp hnu
    intro h0; apply h1
    have heqn : det u' (-vl) = - det u' vl := by
      simp only [det, Prod.fst_neg, Prod.snd_neg]; ring
    omega
  unfold nprevOf
  split_ifs with hc
  · -- `0 < det u' (-vl)`: `hkey : 0 < -(dot (extChain j) (genPerp' (wtower I))) * det u' (-vl)`
    have hlt : dot (extChain d nℓ vl u' i j) (Nivat.LE2.genPerp' (wtower d nℓ vl u' i I)) < 0 := by
      nlinarith [hkey, hc]
    rw [dot_comm]; exact hlt
  · push_neg at hc
    have hclt : det u' (-vl) < 0 := hc.lt_of_ne hcne
    have hgt : 0 < dot (extChain d nℓ vl u' i j) (Nivat.LE2.genPerp' (wtower d nℓ vl u' i I)) := by
      nlinarith [hkey, hclt]
    rw [dot_neg_left, dot_comm]
    omega

/-- `nprevOf` is genuinely an edge normal of `B`: it is (up to the sign flip `nprevOf` already
performs) `genPerp' (wtower I)`, and `wtower I ∈ candSet` is `wgen d nℓ j` for some `j ≠ i`, whose
`genPerp'` (both signs) is already known to lie in `E B` (`genPerp'_wgen_mem_E_B`). -/
theorem nprevOf_mem_E_B {B : Set (ℤ × ℤ)} (d : DecompData ξ) {vl nℓ u' : ℤ × ℤ}
    (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (henv : Nivat.LE2.EnvOf (↑d.Sphi : Set (ℤ × ℤ)) B)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0)
    {I : ℕ} (hIlen : I < (sortedCand d nℓ u' i).length) :
    nprevOf d nℓ vl u' i I ∈ E B := by
  have hwmem : wtower d nℓ vl u' i I ∈ candSet d nℓ u' i := mem_candSet_wtower hIlen
  obtain ⟨_, hw_img⟩ := Finset.mem_erase.mp hwmem
  obtain ⟨j, hj_mem, hj⟩ := Finset.mem_image.mp hw_img
  have hij : j ≠ i := (Finset.mem_erase.mp hj_mem).1
  have hmem := genPerp'_wgen_mem_E_B d hvl_prim hprim hperp henv i hdoth (j := j) hij
  unfold nprevOf
  rw [← hj]
  split_ifs
  · exact hmem.1
  · exact hmem.2

/-! ## §10. The `hbase` propagation step: `V I − L I • wtower I = V (I+1)`

Team-lead's role split (2026-09-22): lane-hsupp owns the `I = 0` base case
(`tmp/wip/hsupp_tower_base.lean`); this lane owns the propagation step, via
`Nivat.PolyChain.adjacent_shared_vertex` applied to the consecutive pair `nprevOf I`,
`nprevOf (I+1)` — both already known to lie in `E B` (`nprevOf_mem_E_B`). The two remaining
geometric facts (`hdet_succ : 0 < det (nprevOf I) (nprevOf (I+1))`, and `hadj_succ`, no edge of
`B` strictly between them) are the actual "半圈" content for *consecutive* tower steps — kept as
explicit hypotheses here (parallel-lane protocol: shared objects get their properties stated as
explicit assumptions traceable upstream), to be discharged once `sortedCand`'s `keyOf`-ordering
is shown to control `E B`'s cyclic order, not just `candSet`'s. -/

/-- `nprevOf`'s direction (`dir`) is `wtower I` up to a global sign fixed once by
`0 < det u' (-vl)` — independent of `I`, since that comparison only involves `u', vl`. -/
noncomputable def nprevSign (vl u' : ℤ × ℤ) : ℤ := if 0 < det u' (-vl) then -1 else 1

theorem dir_nprevOf (d : DecompData ξ) {vl nℓ u' : ℤ × ℤ}
    (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0)
    {I : ℕ} (hIlen : I < (sortedCand d nℓ u' i).length) :
    Nivat.LE2.dir (nprevOf d nℓ vl u' i I) =
      nprevSign vl u' • wtower d nℓ vl u' i I := by
  have hwprim : Primitive (wtower d nℓ vl u' i I) :=
    prim_of_mem_candSet d hvl_prim hprim hperp i hdoth (mem_candSet_wtower hIlen)
  have hwprim' : Prim (wtower d nℓ vl u' i I) := Nivat.LE2.prim_iff_primitive.mpr hwprim
  have hdd : Nivat.LE2.dir (Nivat.LE2.dir (wtower d nℓ vl u' i I))
      = - wtower d nℓ vl u' i I := by
    apply Prod.ext <;> simp [Nivat.LE2.dir]
  have hdneg : Nivat.LE2.dir (-(Nivat.LE2.dir (wtower d nℓ vl u' i I)))
      = -(Nivat.LE2.dir (Nivat.LE2.dir (wtower d nℓ vl u' i I))) := by
    apply Prod.ext <;> simp [Nivat.LE2.dir]
  unfold nprevOf nprevSign
  split_ifs with hc
  · rw [genPerp'_eq_dir_of_prim hwprim', hdd, neg_one_smul]
  · rw [genPerp'_eq_dir_of_prim hwprim', hdneg, hdd, neg_neg, one_smul]

/-- `nprevOf`'s own sign flip (`nprevSign`) cancels in a *consecutive* `det`: both `nprevOf I`
and `nprevOf (I+1)` pick up the *same* global `±1` factor (`0 < det u' (-vl)` doesn't depend on
`I`), which squares away. So the consecutive-normal `det` is literally the consecutive-direction
`det`, unconditionally — no branch dependence survives this particular identity (the branch
dependence shows up one level up, in `det_pos_nprevOf_succ` below, where the *sign* of that
common value against `det u' (-vl)` is what `det_pos_extChain` fixes). -/
theorem det_nprevOf_succ_eq (d : DecompData ξ) {vl nℓ u' : ℤ × ℤ}
    (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0)
    {I : ℕ} (hIlen1 : I < (sortedCand d nℓ u' i).length)
    (hIlen2 : I + 1 < (sortedCand d nℓ u' i).length) :
    det (nprevOf d nℓ vl u' i I) (nprevOf d nℓ vl u' i (I + 1)) =
      det (wtower d nℓ vl u' i I) (wtower d nℓ vl u' i (I + 1)) := by
  have hwprim1 : Primitive (wtower d nℓ vl u' i I) :=
    prim_of_mem_candSet d hvl_prim hprim hperp i hdoth (mem_candSet_wtower hIlen1)
  have hwprim1' : Prim (wtower d nℓ vl u' i I) := Nivat.LE2.prim_iff_primitive.mpr hwprim1
  have hwprim2 : Primitive (wtower d nℓ vl u' i (I + 1)) :=
    prim_of_mem_candSet d hvl_prim hprim hperp i hdoth (mem_candSet_wtower hIlen2)
  have hwprim2' : Prim (wtower d nℓ vl u' i (I + 1)) := Nivat.LE2.prim_iff_primitive.mpr hwprim2
  unfold nprevOf
  rw [genPerp'_eq_dir_of_prim hwprim1', genPerp'_eq_dir_of_prim hwprim2']
  split_ifs with hc
  · exact det_dir_dir _ _
  · have hdd := det_dir_dir (wtower d nℓ vl u' i I) (wtower d nℓ vl u' i (I + 1))
    simp only [det, Prod.fst_neg, Prod.snd_neg] at hdd ⊢
    linarith

/-- **The genuine "half-turn between consecutive tower steps" fact.** Unlike
`dot_nprevOf_neg` (which compares `nprevOf I` against *earlier* chain directions and is branch-
independent), the consecutive-normal `det` (previous lemma) has the *same* sign as
`det (wtower I) (wtower (I+1))`, which `det_pos_extChain` (applied at `j := I+1`, `k := I+2`,
i.e. `extChain (I+1) = wtower I`, `extChain (I+2) = wtower (I+1)`) ties to the sign of
`det u' (-vl)` — so which of `nprevOf I`, `nprevOf (I+1)` is "first" in `adjacent_shared_vertex`'s
sense depends on that global sign, not on `I`. -/
theorem det_pos_nprevOf_succ {B : Set (ℤ × ℤ)} (d : DecompData ξ) {vl nℓ u' : ℤ × ℤ}
    (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (henv : Nivat.LE2.EnvOf (↑d.Sphi : Set (ℤ × ℤ)) B)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0)
    (hadjB : ∀ n ∈ E B, ¬ (dot n vl < 0 ∧ 0 < dot n u'))
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) (hnu : dot nℓ u' < 0) (hnℓ_ne : nℓ ≠ 0)
    {I : ℕ} (hIlen1 : I < (sortedCand d nℓ u' i).length)
    (hIlen2 : I + 1 < (sortedCand d nℓ u' i).length) :
    (0 < det u' (-vl) ∧
      0 < det (nprevOf d nℓ vl u' i I) (nprevOf d nℓ vl u' i (I + 1))) ∨
    (det u' (-vl) < 0 ∧
      0 < det (nprevOf d nℓ vl u' i (I + 1)) (nprevOf d nℓ vl u' i I)) := by
  have heq := det_nprevOf_succ_eq d hvl_prim hprim hperp i hdoth hIlen1 hIlen2
  have hkey := det_pos_extChain d hvl_prim hprim hperp henv i hdoth hadjB hunimod hnu hnℓ_ne
    (j := I + 1) (k := I + 2) (by omega) (by omega)
  have hextsucc1 : extChain d nℓ vl u' i (I + 1) = wtower d nℓ vl u' i I := rfl
  have hextsucc2 : extChain d nℓ vl u' i (I + 2) = wtower d nℓ vl u' i (I + 1) := rfl
  rw [hextsucc1, hextsucc2] at hkey
  have hcne : det u' (-vl) ≠ 0 := by
    have h1 : det u' vl ≠ 0 := det_ne_zero_of_dot_nl_neg hvl_prim hperp hnu
    intro h0; apply h1
    have heqn : det u' (-vl) = - det u' vl := by
      simp only [det, Prod.fst_neg, Prod.snd_neg]; ring
    omega
  rcases lt_or_gt_of_ne hcne with hlt | hgt
  · right
    refine ⟨hlt, ?_⟩
    rw [det_skew (nprevOf d nℓ vl u' i (I + 1)) (nprevOf d nℓ vl u' i I), heq]
    nlinarith [hkey, hlt]
  · left
    refine ⟨hgt, ?_⟩
    rw [heq]
    nlinarith [hkey, hgt]

/-! ## §11. `no_between_nprevOf`: lane-tower's owned exclusion (2026-09-22)

`faceStart_nprevOf_succ`'s remaining hypothesis `hadj_succ` says no edge normal `μ ∈ E B` sits
strictly between `nprevOf I` and `nprevOf (I+1)` (in the `det`-cyclic-order sense, branch-aware).
Team-lead confirmed (2026-09-22) this should only be built for *consecutive* tower steps
(`k = j+1`), not a general `j < k` claim (which is false — `blueprint/LEAF-HSUPP.md`'s Lemma D
induction on `|Arc n|` presupposes nonempty arcs exist in general). Split three ways by what `μ`
traces back to: `± nℓ` (the `i`-generator, `h_i_eq_zsmul_vl`), `± genPerp' u'` (the `u'` ray
itself), or `± nprevOf m` for some other candidate index `m` (`E_zonoF_eq_genPerp_set` traces
`μ` to a generator `j₀`, `wgen`'s definition re-orients it, `exists_wtower_eq_of_mem_candSet`
locates its tower position). -/

/-- Generalizes `hside_boundary_u'` from `I = 0` to every candidate index: `det u' (wtower I)`
has the same sign as `det u' (-vl)`, via `det_pos_extChain` at `j := 0, k := I + 1`
(`extChain 0 = u'`, `extChain (I+1) = wtower I` definitionally). -/
theorem det_pos_u'_wtower {B : Set (ℤ × ℤ)} (d : DecompData ξ) {vl nℓ u' : ℤ × ℤ}
    (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (henv : Nivat.LE2.EnvOf (↑d.Sphi : Set (ℤ × ℤ)) B)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0)
    (hadjB : ∀ n ∈ E B, ¬ (dot n vl < 0 ∧ 0 < dot n u'))
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) (hnu : dot nℓ u' < 0) (hnℓ_ne : nℓ ≠ 0)
    {I : ℕ} (hIlen : I < (sortedCand d nℓ u' i).length) :
    0 < det u' (wtower d nℓ vl u' i I) * det u' (-vl) := by
  have hkey := det_pos_extChain d hvl_prim hprim hperp henv i hdoth hadjB hunimod hnu hnℓ_ne
    (j := 0) (k := I + 1) (by omega) (by omega)
  have h0 : extChain d nℓ vl u' i 0 = u' := rfl
  have h1 : extChain d nℓ vl u' i (I + 1) = wtower d nℓ vl u' i I := rfl
  rw [h0, h1] at hkey
  exact hkey

/-- **`u'`-boundary exclusion.** `det (nprevOf I) (genPerp' u')` is strictly negative for *every*
candidate index `I`, in *both* branches of `0 < det u' (-vl)` — a genuinely global (not just
branch-constant) sign fact, since `genPerp' u'` is a fixed reference direction while `nprevOf`'s
own branch flip exactly compensates for the two possible sweep directions. -/
theorem det_nprevOf_genPerp'u'_neg {B : Set (ℤ × ℤ)} (d : DecompData ξ) {vl nℓ u' : ℤ × ℤ}
    (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (henv : Nivat.LE2.EnvOf (↑d.Sphi : Set (ℤ × ℤ)) B)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0)
    (hadjB : ∀ n ∈ E B, ¬ (dot n vl < 0 ∧ 0 < dot n u'))
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) (hnu : dot nℓ u' < 0) (hnℓ_ne : nℓ ≠ 0)
    {I : ℕ} (hIlen : I < (sortedCand d nℓ u' i).length) :
    det (nprevOf d nℓ vl u' i I) (Nivat.LE2.genPerp' u') < 0 := by
  have hu'prim : Prim u' := prim_u'_of_hunimod hunimod
  have hgu' : Nivat.LE2.genPerp' u' = Nivat.LE2.dir u' := genPerp'_eq_dir_of_prim hu'prim
  have hwprim : Primitive (wtower d nℓ vl u' i I) :=
    prim_of_mem_candSet d hvl_prim hprim hperp i hdoth (mem_candSet_wtower hIlen)
  have hwprim' : Prim (wtower d nℓ vl u' i I) := Nivat.LE2.prim_iff_primitive.mpr hwprim
  have hsign := det_pos_u'_wtower d hvl_prim hprim hperp henv i hdoth hadjB hunimod hnu hnℓ_ne
    hIlen
  have hiff := iff_pos_of_mul_pos hsign
  have hskew := det_skew u' (wtower d nℓ vl u' i I)
  have hAne : det u' (wtower d nℓ vl u' i I) ≠ 0 := by
    intro h0; rw [h0] at hsign; simp at hsign
  unfold nprevOf
  rw [hgu', genPerp'_eq_dir_of_prim hwprim']
  have hdd := det_dir_dir (wtower d nℓ vl u' i I) u'
  split_ifs with hc
  · rw [hdd]
    have hpos2 : 0 < det u' (wtower d nℓ vl u' i I) := hiff.mpr hc
    linarith [hskew]
  · push_neg at hc
    have hcne : det u' (-vl) ≠ 0 := by
      have h1 : det u' vl ≠ 0 := det_ne_zero_of_dot_nl_neg hvl_prim hperp hnu
      intro h0; apply h1
      have heqn : det u' (-vl) = - det u' vl := by
        simp only [det, Prod.fst_neg, Prod.snd_neg]; ring
      omega
    have hclt : det u' (-vl) < 0 := hc.lt_of_ne hcne
    have hAle : det u' (wtower d nℓ vl u' i I) ≤ 0 := by
      by_contra hpos; push_neg at hpos
      exact absurd (hiff.mp hpos) (not_lt.mpr hclt.le)
    have hAlt : det u' (wtower d nℓ vl u' i I) < 0 := hAle.lt_of_ne hAne
    have hng : det (-(Nivat.LE2.dir (wtower d nℓ vl u' i I))) (Nivat.LE2.dir u')
        = - det (Nivat.LE2.dir (wtower d nℓ vl u' i I)) (Nivat.LE2.dir u') := by
      simp only [det, Prod.fst_neg, Prod.snd_neg]; ring
    rw [hng, hdd]
    linarith [hskew]

/-- **`nℓ`-boundary sign** (lane-tower's own derivation, mirroring lane-hsupp's
`no_nl_between_nprevOf` mechanism to stay self-contained within `Nivat/`): `det (nprevOf I) nℓ`
has a sign depending only on the branch of `0 < det u' (-vl)`, constant across every candidate
index `I`. -/
theorem det_nprevOf_nl_sign {vl nℓ u' : ℤ × ℤ} (d : DecompData ξ)
    (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0)
    {I : ℕ} (hIlen : I < (sortedCand d nℓ u' i).length) :
    (0 < det u' (-vl) → 0 < det (nprevOf d nℓ vl u' i I) nℓ) ∧
    (det u' (-vl) < 0 → det (nprevOf d nℓ vl u' i I) nℓ < 0) := by
  have hwprim : Primitive (wtower d nℓ vl u' i I) :=
    prim_of_mem_candSet d hvl_prim hprim hperp i hdoth (mem_candSet_wtower hIlen)
  have hwprim' : Prim (wtower d nℓ vl u' i I) := Nivat.LE2.prim_iff_primitive.mpr hwprim
  have hdotneg : dot nℓ (wtower d nℓ vl u' i I) < 0 :=
    dot_of_mem_candSet d hvl_prim hprim hperp i hdoth (mem_candSet_wtower hIlen)
  have hdd : det (Nivat.LE2.dir (wtower d nℓ vl u' i I)) nℓ
      = - dot (wtower d nℓ vl u' i I) nℓ := by
    simp only [det, dot, Nivat.LE2.dir]; ring
  have hdc : dot (wtower d nℓ vl u' i I) nℓ = dot nℓ (wtower d nℓ vl u' i I) := dot_comm _ _
  unfold nprevOf
  rw [genPerp'_eq_dir_of_prim hwprim']
  constructor
  · intro hc
    rw [if_pos hc, hdd, hdc]
    linarith
  · intro hc
    rw [if_neg (by linarith : ¬ 0 < det u' (-vl))]
    have hng : det (-(Nivat.LE2.dir (wtower d nℓ vl u' i I))) nℓ
        = - det (Nivat.LE2.dir (wtower d nℓ vl u' i I)) nℓ := by
      simp only [det, Prod.fst_neg, Prod.snd_neg]; ring
    rw [hng, hdd, hdc]
    linarith

/-- Generalizes `det_nprevOf_succ_eq` from consecutive `I, I+1` to arbitrary pairs `a, b` — the
proof never used consecutiveness, only that both `a, b` are genuine candidate indices. -/
theorem det_nprevOf_eq (d : DecompData ξ) {vl nℓ u' : ℤ × ℤ}
    (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0)
    {a b : ℕ} (halen : a < (sortedCand d nℓ u' i).length)
    (hblen : b < (sortedCand d nℓ u' i).length) :
    det (nprevOf d nℓ vl u' i a) (nprevOf d nℓ vl u' i b) =
      det (wtower d nℓ vl u' i a) (wtower d nℓ vl u' i b) := by
  have hwprim1 : Primitive (wtower d nℓ vl u' i a) :=
    prim_of_mem_candSet d hvl_prim hprim hperp i hdoth (mem_candSet_wtower halen)
  have hwprim1' : Prim (wtower d nℓ vl u' i a) := Nivat.LE2.prim_iff_primitive.mpr hwprim1
  have hwprim2 : Primitive (wtower d nℓ vl u' i b) :=
    prim_of_mem_candSet d hvl_prim hprim hperp i hdoth (mem_candSet_wtower hblen)
  have hwprim2' : Prim (wtower d nℓ vl u' i b) := Nivat.LE2.prim_iff_primitive.mpr hwprim2
  unfold nprevOf
  rw [genPerp'_eq_dir_of_prim hwprim1', genPerp'_eq_dir_of_prim hwprim2']
  split_ifs with hc
  · exact det_dir_dir _ _
  · have hdd := det_dir_dir (wtower d nℓ vl u' i a) (wtower d nℓ vl u' i b)
    simp only [det, Prod.fst_neg, Prod.snd_neg] at hdd ⊢
    linarith

/-- The transitive gap fact for `nprevOf`, for arbitrary (not just consecutive) index pairs
`a < b < len`: corollary of `det_pos_extChain` at `j := a + 1, k := b + 1` combined with
`det_nprevOf_eq`. -/
theorem det_pos_nprevOf_gap {B : Set (ℤ × ℤ)} (d : DecompData ξ) {vl nℓ u' : ℤ × ℤ}
    (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (henv : Nivat.LE2.EnvOf (↑d.Sphi : Set (ℤ × ℤ)) B)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0)
    (hadjB : ∀ n ∈ E B, ¬ (dot n vl < 0 ∧ 0 < dot n u'))
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) (hnu : dot nℓ u' < 0) (hnℓ_ne : nℓ ≠ 0)
    {a b : ℕ} (hab : a < b) (hblen : b < (sortedCand d nℓ u' i).length) :
    0 < det (nprevOf d nℓ vl u' i a) (nprevOf d nℓ vl u' i b) * det u' (-vl) := by
  have halen : a < (sortedCand d nℓ u' i).length := by omega
  have heq := det_nprevOf_eq d hvl_prim hprim hperp i hdoth halen hblen
  have hgap := det_pos_extChain d hvl_prim hprim hperp henv i hdoth hadjB hunimod hnu hnℓ_ne
    (j := a + 1) (k := b + 1) (by omega) (by omega)
  have h1 : extChain d nℓ vl u' i (a + 1) = wtower d nℓ vl u' i a := rfl
  have h2 : extChain d nℓ vl u' i (b + 1) = wtower d nℓ vl u' i b := rfl
  rw [h1, h2] at hgap
  rw [heq]; exact hgap

/-- Locates a candidate's tower position: if `v ∈ candSet`, some `m < len` has `wtower m = v`
(`towerIdx` is an involution on `[0, len)`, so `m := towerIdx len p` inverts the position `p`
where `v` sits in `sortedCand`). -/
theorem exists_wtower_eq_of_mem_candSet {d : DecompData ξ} {nℓ vl u' : ℤ × ℤ} {i : Fin d.m}
    {v : ℤ × ℤ} (hv : v ∈ candSet d nℓ u' i) :
    ∃ m, m < (sortedCand d nℓ u' i).length ∧ wtower d nℓ vl u' i m = v := by
  rw [← mem_sortedCand] at hv
  obtain ⟨p, hp, hgetp⟩ := List.mem_iff_getElem.mp hv
  have hm : towerIdx vl u' (sortedCand d nℓ u' i).length p < (sortedCand d nℓ u' i).length :=
    towerIdx_lt hp
  refine ⟨towerIdx vl u' (sortedCand d nℓ u' i).length p, hm, ?_⟩
  have hinv : towerIdx vl u' (sortedCand d nℓ u' i).length
      (towerIdx vl u' (sortedCand d nℓ u' i).length p) = p := by
    unfold towerIdx; split_ifs <;> omega
  rw [wtower_eq_getElem hm]
  simp only [hinv]
  exact hgetp

/-- `nprevOf m` is, as an unordered pair, exactly `{genPerp' (wtower m), -genPerp' (wtower m)}`
— immediate from unfolding the branch. -/
theorem nprevOf_eq_cases (d : DecompData ξ) (nℓ vl u' : ℤ × ℤ) (i : Fin d.m) (m : ℕ) :
    nprevOf d nℓ vl u' i m = Nivat.LE2.genPerp' (wtower d nℓ vl u' i m) ∨
      nprevOf d nℓ vl u' i m = -Nivat.LE2.genPerp' (wtower d nℓ vl u' i m) := by
  unfold nprevOf; split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- **Generator tracing.** Every `μ ∈ E B` is, up to sign, either `nℓ` (the `i`-generator),
`genPerp' u'` (the `u'` ray), or `nprevOf m` for some other candidate position `m < len`. -/
theorem cases_of_mem_E_B {B : Set (ℤ × ℤ)} (d : DecompData ξ) {vl nℓ u' : ℤ × ℤ}
    (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (henv : Nivat.LE2.EnvOf (↑d.Sphi : Set (ℤ × ℤ)) B)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0)
    {μ : ℤ × ℤ} (hμ : μ ∈ E B) :
    (μ = nℓ ∨ μ = -nℓ) ∨
    (μ = Nivat.LE2.genPerp' u' ∨ μ = -Nivat.LE2.genPerp' u') ∨
    (∃ m, m < (sortedCand d nℓ u' i).length ∧
      (μ = nprevOf d nℓ vl u' i m ∨ μ = -(nprevOf d nℓ vl u' i m))) := by
  have hfin : (E (↑d.Sphi : Set (ℤ × ℤ))).Finite :=
    Nivat.LE2.finite_E_of_finite d.Sphi.finite_toSet
  have hE : E B = E (↑d.Sphi : Set (ℤ × ℤ)) := Nivat.LE2.Enveloped.E_eq hfin henv
  rw [hE, E_Sphi_eq_E_zonoF] at hμ
  obtain ⟨j₀, hcase⟩ := (Nivat.LE2.E_zonoF_eq_genPerp_set d.h d.h_ne d.h_dir μ).mp hμ
  by_cases hji : j₀ = i
  · subst hji
    obtain ⟨c, hci⟩ := h_i_eq_zsmul_vl d hvl_prim hprim hperp j₀ hdoth
    have hcne : c ≠ 0 := by
      intro h0; apply d.h_ne j₀; rw [hci, h0]; simp
    have hvlne0 : vl ≠ 0 := hvl_prim.ne_zero
    have hdotgp : dot (d.h j₀) (Nivat.LE2.genPerp' (d.h j₀)) = 0 :=
      Nivat.LE2.dot_genPerp' (d.h_ne j₀)
    have hdotvlgp : dot vl (Nivat.LE2.genPerp' (d.h j₀)) = 0 := by
      have heq0 : dot (c • vl) (Nivat.LE2.genPerp' (d.h j₀)) = 0 := by rw [← hci]; exact hdotgp
      have hdc : dot (c • vl) (Nivat.LE2.genPerp' (d.h j₀))
          = c * dot vl (Nivat.LE2.genPerp' (d.h j₀)) := by
        simp only [dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
      rw [hdc] at heq0
      rcases mul_eq_zero.mp heq0 with h | h
      · exact absurd h hcne
      · exact h
    have hdvlnl : dot vl nℓ = 0 := by rw [dot_comm]; exact hperp
    have hdetnl : det nℓ (Nivat.LE2.genPerp' (d.h j₀)) = 0 :=
      Nivat.LE2.det_eq_zero_of_dot_eq_zero hvlne0 hdvlnl hdotvlgp
    have hgnl : Nivat.LE2.genPerp' (d.h j₀) = nℓ ∨ Nivat.LE2.genPerp' (d.h j₀) = -nℓ :=
      Nivat.LE2.eq_or_neg_of_prim_of_det_eq_zero hprim (Nivat.LE2.genPerp'_prim (d.h_ne j₀))
        hdetnl
    left
    rcases hcase with hc1 | hc1 <;> rcases hgnl with hg1 | hg1
    · exact Or.inl (by rw [hc1, hg1])
    · exact Or.inr (by rw [hc1, hg1])
    · exact Or.inr (by rw [hc1, hg1])
    · exact Or.inl (by rw [hc1, hg1]; ring)
  · by_cases hwu : wgen d nℓ j₀ = u'
    · have hwne : wgen d nℓ j₀ ≠ 0 := (wgen_prim d hvl_prim hprim hperp i hdoth hji).ne_zero
      have hhne : d.h j₀ ≠ 0 := d.h_ne j₀
      have hd0 : det (wgen d nℓ j₀) (d.h j₀) = 0 :=
        det_wgen_h_eq_zero d hvl_prim hprim hperp i hdoth hji
      have hg0 : det (Nivat.LE2.genPerp' (wgen d nℓ j₀)) (Nivat.LE2.genPerp' (d.h j₀)) = 0 :=
        genPerp'_det_eq_zero_of_det_eq_zero hwne hhne hd0
      have hp1 : Prim (Nivat.LE2.genPerp' (wgen d nℓ j₀)) := Nivat.LE2.genPerp'_prim hwne
      have hp2 : Prim (Nivat.LE2.genPerp' (d.h j₀)) := Nivat.LE2.genPerp'_prim hhne
      have hgeq := Nivat.LE2.eq_or_neg_of_prim_of_det_eq_zero hp1 hp2 hg0
      rw [hwu] at hgeq
      right; left
      rcases hcase with hc1 | hc1 <;> rcases hgeq with hg1 | hg1
      · exact Or.inl (by rw [hc1, hg1])
      · exact Or.inr (by rw [hc1, hg1])
      · exact Or.inr (by rw [hc1, hg1])
      · exact Or.inl (by rw [hc1, hg1]; ring)
    · have hmem : wgen d nℓ j₀ ∈ candSet d nℓ u' i := by
        apply Finset.mem_erase.mpr
        refine ⟨hwu, Finset.mem_image.mpr ⟨j₀, Finset.mem_erase.mpr ⟨hji, Finset.mem_univ _⟩,
          rfl⟩⟩
      obtain ⟨m, hmlen, hweq⟩ :=
        exists_wtower_eq_of_mem_candSet (vl := vl) hmem
      have hwne : wgen d nℓ j₀ ≠ 0 := (wgen_prim d hvl_prim hprim hperp i hdoth hji).ne_zero
      have hhne : d.h j₀ ≠ 0 := d.h_ne j₀
      have hd0 : det (wgen d nℓ j₀) (d.h j₀) = 0 :=
        det_wgen_h_eq_zero d hvl_prim hprim hperp i hdoth hji
      have hg0 : det (Nivat.LE2.genPerp' (wgen d nℓ j₀)) (Nivat.LE2.genPerp' (d.h j₀)) = 0 :=
        genPerp'_det_eq_zero_of_det_eq_zero hwne hhne hd0
      have hp1 : Prim (Nivat.LE2.genPerp' (wgen d nℓ j₀)) := Nivat.LE2.genPerp'_prim hwne
      have hp2 : Prim (Nivat.LE2.genPerp' (d.h j₀)) := Nivat.LE2.genPerp'_prim hhne
      have hgeq := Nivat.LE2.eq_or_neg_of_prim_of_det_eq_zero hp1 hp2 hg0
      rw [← hweq] at hgeq
      have hnc := nprevOf_eq_cases d nℓ vl u' i m
      right; right
      refine ⟨m, hmlen, ?_⟩
      rcases hcase with hc1 | hc1 <;> rcases hgeq with hg1 | hg1 <;> rcases hnc with hn1 | hn1
      · exact Or.inl (by simp only [hc1, hg1, hn1]; try ring)
      · exact Or.inr (by simp only [hc1, hg1, hn1]; try ring)
      · exact Or.inr (by simp only [hc1, hg1, hn1]; try ring)
      · exact Or.inl (by simp only [hc1, hg1, hn1]; try ring)
      · exact Or.inr (by simp only [hc1, hg1, hn1]; try ring)
      · exact Or.inl (by simp only [hc1, hg1, hn1]; try ring)
      · exact Or.inl (by simp only [hc1, hg1, hn1]; try ring)
      · exact Or.inr (by simp only [hc1, hg1, hn1]; try ring)

/-- **The assembled exclusion**, matching `faceStart_nprevOf_succ`'s `hadj_succ` parameter
exactly: no `μ ∈ E B` sits strictly between `nprevOf I` and `nprevOf (I+1)`, in whichever branch
of `0 < det u' (-vl)` is active. Combines the three cases from `cases_of_mem_E_B`: `± nℓ`
(`det_nprevOf_nl_sign`, branch-matched), `± genPerp' u'` (`det_nprevOf_genPerp'u'_neg`, globally
negative), and `± nprevOf m` for `m ∉ {I, I+1}` (`det_pos_nprevOf_gap` transitivity; `m ∈ {I,
I+1}` is excluded immediately since `det x x = 0`). -/
theorem no_between_nprevOf {B : Set (ℤ × ℤ)} (d : DecompData ξ) {vl nℓ u' : ℤ × ℤ}
    (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (henv : Nivat.LE2.EnvOf (↑d.Sphi : Set (ℤ × ℤ)) B)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0)
    (hadjB : ∀ n ∈ E B, ¬ (dot n vl < 0 ∧ 0 < dot n u'))
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) (hnu : dot nℓ u' < 0) (hnℓ_ne : nℓ ≠ 0)
    {I : ℕ} (hIlen1 : I < (sortedCand d nℓ u' i).length)
    (hIlen2 : I + 1 < (sortedCand d nℓ u' i).length) :
    (0 < det u' (-vl) → ∀ μ ∈ E B, ¬ (0 < det (nprevOf d nℓ vl u' i I) μ ∧
        0 < det μ (nprevOf d nℓ vl u' i (I + 1)))) ∧
    (det u' (-vl) < 0 → ∀ μ ∈ E B, ¬ (0 < det (nprevOf d nℓ vl u' i (I + 1)) μ ∧
        0 < det μ (nprevOf d nℓ vl u' i I))) := by
  have hzeroI : det (nprevOf d nℓ vl u' i I) (nprevOf d nℓ vl u' i I) = 0 := by
    simp only [det]; ring
  have hzeroI1 : det (nprevOf d nℓ vl u' i (I + 1)) (nprevOf d nℓ vl u' i (I + 1)) = 0 := by
    simp only [det]; ring
  constructor
  · intro hc μ hμ hcon
    obtain ⟨h1, h2⟩ := hcon
    rcases cases_of_mem_E_B d hvl_prim hprim hperp henv i hdoth hμ with
      hnl | hu' | ⟨m, hmlen, hm⟩
    · rcases hnl with hμeq | hμeq
      · rw [hμeq] at h2
        have hsign := (det_nprevOf_nl_sign d hvl_prim hprim hperp i hdoth hIlen2).1 hc
        rw [det_skew nℓ (nprevOf d nℓ vl u' i (I + 1))] at h2
        linarith
      · rw [hμeq] at h1
        have hsign := (det_nprevOf_nl_sign d hvl_prim hprim hperp i hdoth hIlen1).1 hc
        have hng : det (nprevOf d nℓ vl u' i I) (-nℓ)
            = - det (nprevOf d nℓ vl u' i I) nℓ := by
          simp only [det, Prod.fst_neg, Prod.snd_neg]; ring
        rw [hng] at h1
        linarith
    · rcases hu' with hμeq | hμeq
      · rw [hμeq] at h1
        have hsign := det_nprevOf_genPerp'u'_neg d hvl_prim hprim hperp henv i hdoth hadjB
          hunimod hnu hnℓ_ne hIlen1
        linarith
      · rw [hμeq] at h2
        have hsign := det_nprevOf_genPerp'u'_neg d hvl_prim hprim hperp henv i hdoth hadjB
          hunimod hnu hnℓ_ne hIlen2
        have hng : det (-Nivat.LE2.genPerp' u') (nprevOf d nℓ vl u' i (I + 1))
            = - det (Nivat.LE2.genPerp' u') (nprevOf d nℓ vl u' i (I + 1)) := by
          simp only [det, Prod.fst_neg, Prod.snd_neg]; ring
        rw [hng] at h2
        have hskew := det_skew (Nivat.LE2.genPerp' u') (nprevOf d nℓ vl u' i (I + 1))
        linarith
    · rcases lt_trichotomy m I with hmI | hmI | hmI
      · have hgap1 := det_pos_nprevOf_gap d hvl_prim hprim hperp henv i hdoth hadjB hunimod hnu
          hnℓ_ne hmI hIlen1
        have hgap2 := det_pos_nprevOf_gap d hvl_prim hprim hperp henv i hdoth hadjB hunimod hnu
          hnℓ_ne (by omega : m < I + 1) hIlen2
        have hA : 0 < det (nprevOf d nℓ vl u' i m) (nprevOf d nℓ vl u' i I) := by
          nlinarith [hgap1, hc]
        have hB : 0 < det (nprevOf d nℓ vl u' i m) (nprevOf d nℓ vl u' i (I + 1)) := by
          nlinarith [hgap2, hc]
        rcases hm with hμeq | hμeq
        · rw [hμeq] at h1
          have hAskew := det_skew (nprevOf d nℓ vl u' i m) (nprevOf d nℓ vl u' i I)
          linarith [hAskew, hA]
        · rw [hμeq] at h2
          have hng : det (-(nprevOf d nℓ vl u' i m)) (nprevOf d nℓ vl u' i (I + 1))
              = - det (nprevOf d nℓ vl u' i m) (nprevOf d nℓ vl u' i (I + 1)) := by
            simp only [det, Prod.fst_neg, Prod.snd_neg]; ring
          rw [hng] at h2; linarith [hB]
      · subst hmI; rcases hm with hμeq | hμeq
        · rw [hμeq] at h1; linarith [hzeroI]
        · rw [hμeq] at h1
          have hz : det (nprevOf d nℓ vl u' i m) (-(nprevOf d nℓ vl u' i m)) = 0 := by
            simp only [det, Prod.fst_neg, Prod.snd_neg]; ring
          linarith [hz]
      · rcases eq_or_lt_of_le (by omega : I + 1 ≤ m) with hme | hme
        · rw [← hme] at hm
          rcases hm with hμeq | hμeq
          · rw [hμeq] at h2; linarith [hzeroI1]
          · rw [hμeq] at h2
            have hz : det (-(nprevOf d nℓ vl u' i (I + 1))) (nprevOf d nℓ vl u' i (I + 1)) = 0 := by
              simp only [det, Prod.fst_neg, Prod.snd_neg]; ring
            linarith [hz]
        · have hgap1 := det_pos_nprevOf_gap d hvl_prim hprim hperp henv i hdoth hadjB hunimod hnu
            hnℓ_ne (a := I) (b := m) (by omega) hmlen
          have hgap2 := det_pos_nprevOf_gap d hvl_prim hprim hperp henv i hdoth hadjB hunimod hnu
            hnℓ_ne (a := I + 1) (b := m) (by omega) hmlen
          have hA : 0 < det (nprevOf d nℓ vl u' i I) (nprevOf d nℓ vl u' i m) := by
            nlinarith [hgap1, hc]
          have hB : 0 < det (nprevOf d nℓ vl u' i (I + 1)) (nprevOf d nℓ vl u' i m) := by
            nlinarith [hgap2, hc]
          rcases hm with hμeq | hμeq
          · rw [hμeq] at h2
            have hng : det (nprevOf d nℓ vl u' i m) (nprevOf d nℓ vl u' i (I + 1))
                = - det (nprevOf d nℓ vl u' i (I + 1)) (nprevOf d nℓ vl u' i m) := det_skew _ _
            rw [hng] at h2; linarith [hB]
          · rw [hμeq] at h1
            have hng : det (nprevOf d nℓ vl u' i I) (-(nprevOf d nℓ vl u' i m))
                = - det (nprevOf d nℓ vl u' i I) (nprevOf d nℓ vl u' i m) := by
              simp only [det, Prod.fst_neg, Prod.snd_neg]; ring
            rw [hng] at h1; linarith [hA]
  · intro hc μ hμ hcon
    obtain ⟨h1, h2⟩ := hcon
    rcases cases_of_mem_E_B d hvl_prim hprim hperp henv i hdoth hμ with
      hnl | hu' | ⟨m, hmlen, hm⟩
    · rcases hnl with hμeq | hμeq
      · rw [hμeq] at h1
        have hsign := (det_nprevOf_nl_sign d hvl_prim hprim hperp i hdoth hIlen2).2 hc
        linarith
      · rw [hμeq] at h2
        have hsign := (det_nprevOf_nl_sign d hvl_prim hprim hperp i hdoth hIlen1).2 hc
        have hng : det (-nℓ) (nprevOf d nℓ vl u' i I)
            = - det nℓ (nprevOf d nℓ vl u' i I) := by
          simp only [det, Prod.fst_neg, Prod.snd_neg]; ring
        rw [hng, det_skew nℓ (nprevOf d nℓ vl u' i I)] at h2
        linarith
    · rcases hu' with hμeq | hμeq
      · rw [hμeq] at h1
        have hsign := det_nprevOf_genPerp'u'_neg d hvl_prim hprim hperp henv i hdoth hadjB
          hunimod hnu hnℓ_ne hIlen2
        linarith
      · rw [hμeq] at h2
        have hsign := det_nprevOf_genPerp'u'_neg d hvl_prim hprim hperp henv i hdoth hadjB
          hunimod hnu hnℓ_ne hIlen1
        have hng : det (-Nivat.LE2.genPerp' u') (nprevOf d nℓ vl u' i I)
            = - det (Nivat.LE2.genPerp' u') (nprevOf d nℓ vl u' i I) := by
          simp only [det, Prod.fst_neg, Prod.snd_neg]; ring
        rw [hng, det_skew (Nivat.LE2.genPerp' u') (nprevOf d nℓ vl u' i I)] at h2
        linarith
    · rcases lt_trichotomy m I with hmI | hmI | hmI
      · have hgap1 := det_pos_nprevOf_gap d hvl_prim hprim hperp henv i hdoth hadjB hunimod hnu
          hnℓ_ne hmI hIlen1
        have hgap2 := det_pos_nprevOf_gap d hvl_prim hprim hperp henv i hdoth hadjB hunimod hnu
          hnℓ_ne (by omega : m < I + 1) hIlen2
        have hA : det (nprevOf d nℓ vl u' i m) (nprevOf d nℓ vl u' i I) < 0 := by
          nlinarith [hgap1, hc]
        have hB : det (nprevOf d nℓ vl u' i m) (nprevOf d nℓ vl u' i (I + 1)) < 0 := by
          nlinarith [hgap2, hc]
        rcases hm with hμeq | hμeq
        · rw [hμeq] at h2
          have hng : det (nprevOf d nℓ vl u' i m) (nprevOf d nℓ vl u' i I)
              = - det (nprevOf d nℓ vl u' i I) (nprevOf d nℓ vl u' i m) := det_skew _ _
          rw [hng] at hA
          linarith [h2, hA]
        · rw [hμeq] at h1
          have hng : det (nprevOf d nℓ vl u' i (I + 1)) (-(nprevOf d nℓ vl u' i m))
              = - det (nprevOf d nℓ vl u' i (I + 1)) (nprevOf d nℓ vl u' i m) := by
            simp only [det, Prod.fst_neg, Prod.snd_neg]; ring
          rw [hng] at h1
          have hBskew := det_skew (nprevOf d nℓ vl u' i m) (nprevOf d nℓ vl u' i (I + 1))
          linarith [hB, hBskew]
      · subst hmI; rcases hm with hμeq | hμeq
        · rw [hμeq] at h2
          linarith [hzeroI]
        · rw [hμeq] at h2
          have hz : det (-(nprevOf d nℓ vl u' i m)) (nprevOf d nℓ vl u' i m) = 0 := by
            simp only [det, Prod.fst_neg, Prod.snd_neg]; ring
          linarith [hz]
      · rcases eq_or_lt_of_le (by omega : I + 1 ≤ m) with hme | hme
        · rw [← hme] at hm
          rcases hm with hμeq | hμeq
          · rw [hμeq] at h1; linarith [hzeroI1]
          · rw [hμeq] at h1
            have hz : det (nprevOf d nℓ vl u' i (I + 1)) (-(nprevOf d nℓ vl u' i (I + 1))) = 0 := by
              simp only [det, Prod.fst_neg, Prod.snd_neg]; ring
            linarith [hz]
        · have hgap1 := det_pos_nprevOf_gap d hvl_prim hprim hperp henv i hdoth hadjB hunimod hnu
            hnℓ_ne (a := I) (b := m) (by omega) hmlen
          have hgap2 := det_pos_nprevOf_gap d hvl_prim hprim hperp henv i hdoth hadjB hunimod hnu
            hnℓ_ne (a := I + 1) (b := m) (by omega) hmlen
          have hA : det (nprevOf d nℓ vl u' i I) (nprevOf d nℓ vl u' i m) < 0 := by
            nlinarith [hgap1, hc]
          have hB : det (nprevOf d nℓ vl u' i (I + 1)) (nprevOf d nℓ vl u' i m) < 0 := by
            nlinarith [hgap2, hc]
          rcases hm with hμeq | hμeq
          · rw [hμeq] at h1
            linarith [hB]
          · rw [hμeq] at h2
            have hng : det (-(nprevOf d nℓ vl u' i m)) (nprevOf d nℓ vl u' i I)
                = - det (nprevOf d nℓ vl u' i m) (nprevOf d nℓ vl u' i I) := by
              simp only [det, Prod.fst_neg, Prod.snd_neg]; ring
            rw [hng] at h2
            have hAskew := det_skew (nprevOf d nℓ vl u' i m) (nprevOf d nℓ vl u' i I)
            linarith [hA, hAskew]

/-- **The `hbase` propagation step, branch-aware** (team-lead's ruling 2026-09-22: `hdet_succ`
is genuinely branch-dependent on the global sign of `det u' (-vl)`, not a free hypothesis —
`det_pos_nprevOf_succ` pins which of the two orders is the "correct" one for
`adjacent_shared_vertex`, and the theorem must produce whichever conclusion shape matches).
`hadj_succ` is stated as a pair of *conditional* facts (one per branch) so the caller only
owes the adjacency fact for the order that is actually meaningful in each branch — the
reversed order in the "wrong" branch need not even be true. -/
theorem faceStart_nprevOf_succ {B : Set (ℤ × ℤ)} (d : DecompData ξ) {vl nℓ u' : ℤ × ℤ}
    (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (henv : Nivat.LE2.EnvOf (↑d.Sphi : Set (ℤ × ℤ)) B)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0)
    (hBfin : B.Finite) (hBconv : IsLatticeConvexRegion B)
    (hadjB : ∀ n ∈ E B, ¬ (dot n vl < 0 ∧ 0 < dot n u'))
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) (hnu : dot nℓ u' < 0) (hnℓ_ne : nℓ ≠ 0)
    {I : ℕ} (hIlen1 : I < (sortedCand d nℓ u' i).length)
    (hIlen2 : I + 1 < (sortedCand d nℓ u' i).length) :
    (0 < det u' (-vl) ∧
      faceStart B (nprevOf d nℓ vl u' i I) +
        ((faceLen B (nprevOf d nℓ vl u' i I) : ℤ) * nprevSign vl u') •
          wtower d nℓ vl u' i I
        = faceStart B (nprevOf d nℓ vl u' i (I + 1))) ∨
    (det u' (-vl) < 0 ∧
      faceStart B (nprevOf d nℓ vl u' i (I + 1)) +
        (faceLen B (nprevOf d nℓ vl u' i (I + 1)) : ℤ) •
          Nivat.LE2.dir (nprevOf d nℓ vl u' i (I + 1))
        = faceStart B (nprevOf d nℓ vl u' i I)) := by
  have hadj_succ := no_between_nprevOf d hvl_prim hprim hperp henv i hdoth hadjB hunimod hnu
    hnℓ_ne hIlen1 hIlen2
  rcases det_pos_nprevOf_succ d hvl_prim hprim hperp henv i hdoth hadjB hunimod hnu hnℓ_ne
      hIlen1 hIlen2 with ⟨hpos, hdetpos⟩ | ⟨hneg, hdetpos⟩
  · left
    refine ⟨hpos, ?_⟩
    have hkey := Nivat.PolyChain.adjacent_shared_vertex hBfin hBconv
      (nprevOf_mem_E_B d hvl_prim hprim hperp henv i hdoth hIlen1)
      (nprevOf_mem_E_B d hvl_prim hprim hperp henv i hdoth hIlen2)
      hdetpos (hadj_succ.1 hpos)
    rw [dir_nprevOf d hvl_prim hprim hperp i hdoth hIlen1, smul_smul] at hkey
    exact hkey
  · right
    refine ⟨hneg, ?_⟩
    exact Nivat.PolyChain.adjacent_shared_vertex hBfin hBconv
      (nprevOf_mem_E_B d hvl_prim hprim hperp henv i hdoth hIlen2)
      (nprevOf_mem_E_B d hvl_prim hprim hperp henv i hdoth hIlen1)
      hdetpos (hadj_succ.2 hneg)

end Nivat.ColleReg

#print axioms Nivat.ColleReg.genPerp'_mem_E_B
#print axioms Nivat.ColleReg.dot_wgen_neg
#print axioms Nivat.ColleReg.wgen_prim
#print axioms Nivat.ColleReg.key_identity
#print axioms Nivat.ColleReg.det_pos_iff_key_lt
#print axioms Nivat.ColleReg.keyOf_injOn
#print axioms Nivat.ColleReg.sortedCand_pairwise
#print axioms Nivat.ColleReg.sortedCand_nodup
#print axioms Nivat.ColleReg.mem_sortedCand
#print axioms Nivat.ColleReg.ne_u'_of_mem_candSet
#print axioms Nivat.ColleReg.det_pos_of_sortedCand_pairwise
#print axioms Nivat.ColleReg.det_vl_sign_eq_of_dot_nl_neg
#print axioms Nivat.ColleReg.det_ne_zero_of_dot_nl_neg
#print axioms Nivat.ColleReg.det_w_negvl_sign_eq
#print axioms Nivat.ColleReg.hside_interior
#print axioms Nivat.ColleReg.hside_boundary_vl
#print axioms Nivat.ColleReg.det_dir_dir
#print axioms Nivat.ColleReg.primPart_det_eq_zero_of_det_eq_zero
#print axioms Nivat.ColleReg.genPerp'_det_eq_zero_of_det_eq_zero
#print axioms Nivat.ColleReg.det_wgen_h_eq_zero
#print axioms Nivat.ColleReg.genPerp'_wgen_mem_E_B
#print axioms Nivat.ColleReg.dot_genPerp'_wgen_vl_ne_zero
#print axioms Nivat.ColleReg.prim_dir_of_prim
#print axioms Nivat.ColleReg.primPart_eq_self_of_prim
#print axioms Nivat.ColleReg.genPerp'_eq_dir_of_prim
#print axioms Nivat.ColleReg.det_eq_dot_genPerp'

#print axioms Nivat.ColleReg.prim_u'_of_hunimod
#print axioms Nivat.ColleReg.no_opposite_sign_of_hadjB
#print axioms Nivat.ColleReg.det_ne_zero_wgen_u'_of_ne
#print axioms Nivat.ColleReg.det_w_u'_sign_eq_of_hadjB
#print axioms Nivat.ColleReg.mul_pos_of_iff_pos_ne_zero
#print axioms Nivat.ColleReg.hside_boundary_u'
#print axioms Nivat.ColleReg.dot_extChain_neg
#print axioms Nivat.ColleReg.iff_pos_of_mul_pos
#print axioms Nivat.ColleReg.det_extChain_consec
#print axioms Nivat.ColleReg.det_pos_chain
#print axioms Nivat.ColleReg.det_pos_chain_rev
#print axioms Nivat.ColleReg.det_pos_extChain
#print axioms Nivat.ColleReg.dot_nprevOf_neg
#print axioms Nivat.ColleReg.nprevOf_mem_E_B
#print axioms Nivat.ColleReg.dir_nprevOf
#print axioms Nivat.ColleReg.faceStart_nprevOf_succ
#print axioms Nivat.ColleReg.det_nprevOf_succ_eq
#print axioms Nivat.ColleReg.det_pos_nprevOf_succ

#print axioms Nivat.ColleReg.det_pos_u'_wtower
#print axioms Nivat.ColleReg.det_nprevOf_genPerp'u'_neg
#print axioms Nivat.ColleReg.det_nprevOf_nl_sign
#print axioms Nivat.ColleReg.det_nprevOf_eq
#print axioms Nivat.ColleReg.det_pos_nprevOf_gap
#print axioms Nivat.ColleReg.exists_wtower_eq_of_mem_candSet
#print axioms Nivat.ColleReg.nprevOf_eq_cases
#print axioms Nivat.ColleReg.cases_of_mem_E_B
#print axioms Nivat.ColleReg.no_between_nprevOf
