/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.ZonoEdgeGen
import Nivat.External.Colle.ConvTransport
import Nivat.External.Colle.PolyChain
import Nivat.External.Colle.DecompData
import Nivat.External.Colle.Claim47Core

/-!
# `HsuppLengthBound` — the `faceLen B ν_j ≥ gcd(h j)` piece of `blueprint/LEAF-HSUPP.md` §2(E)

Lane `lane-chain`, unblocking my own earlier report ("`Sphi`↔`zonoF` face bridge is
open territory") to `team-lead`: that report was **too pessimistic**. The full
`face S ν = face T ν` equality is indeed blocked (`ConvTransport.lean:325`'s
counterexample), but the length bound only needs a **one-directional** argument that
does not hit that counterexample:

1. `zonoF univ h ⊆ Sphi` as *sets* (`Sphi_conv` + `Sphi_eq`, exactly the pattern already
   landed in `DecompData.lean`'s `subset_Sphi`/`Sphi_negSymm`).
2. A point maximizing `dot ν` over the (bigger) set `zonoF univ h` also maximizes `dot ν`
   over `Sphi`, because `Conv Sphi = Conv (zonoF univ h)` (`Conv_subset_halfSpace` +
   `rdot_toReal`, the same two lemmas `ConvTransport.lean`'s `dot_face_eq_of_Conv_eq`
   already uses) — this only needs the *membership* direction, not face-set equality.
3. `ZonoEdgeGen.lean`'s `face_encard_zonoF` proof already computes the exact two-point
   zonotope face `{x, x + h j}`; exposing that computation (instead of just its
   cardinality) gives the two lattice points needed for step 2.
4. The scope's `henv`/`Enveloped` encard inequality (already available at the consumer,
   threaded here as an explicit hypothesis since this file cannot import
   `RegionSteps.lean`) transports the bound from `Sphi` to `B`.

## Status (2026-09-22, lane-chain)

§1 `face_zonoF_pair`, §2 `zonoF_sub_Sphi`, `mem_face_Sphi_of_mem_face_zonoF` — proved.
§3 `faceLen_ge_gcd` — the assembled bound — in progress.
-/

namespace Nivat.HsuppLengthBound

open Nivat Nivat.LE2 Nivat.Colle35 Finset Classical Pointwise

variable {m : ℕ}

/-! ## §1. The explicit two-point zonotope face

`ZonoEdgeGen.face_encard_zonoF` only exposes the *cardinality* of the face. Its proof
computes the actual two points; we redo that derivation (same lemmas: `coe_zonoF`,
`face_sum`, `face_segOf_cases`, `sum_singleton_eq`) without discarding them into
`Set.encard_pair`. Sign-agnostic: works for *any* nonzero `ν` orthogonal to `h j`, not
just `genPerp' (h j)` — so it covers `-genPerp' (h j)` too, without a separate proof. -/

theorem face_zonoF_pair (h : Fin m → ℤ × ℤ) (_h_ne : ∀ k, h k ≠ 0)
    (h_dir : ∀ k l, k ≠ l → det (h k) (h l) ≠ 0)
    (j : Fin m) (ν : ℤ × ℤ) (hν_ne : ν ≠ 0) (hj_orth : dot ν (h j) = 0) :
    face (↑(zonoF Finset.univ h) : Set (ℤ × ℤ)) ν =
      {(∑ k ∈ (Finset.univ.erase j), (if 0 < dot ν (h k) then h k else 0)),
       (∑ k ∈ (Finset.univ.erase j), (if 0 < dot ν (h k) then h k else 0)) + h j} := by
  have hk_orth : ∀ k, k ≠ j → dot ν (h k) ≠ 0 := fun k hkj hk =>
    hkj (at_most_one_orthogonal h h_dir ν hν_ne k j hk hj_orth)
  set x : ℤ × ℤ := ∑ k ∈ (Finset.univ.erase j), (if 0 < dot ν (h k) then h k else 0) with hxdef
  have hrest : ∑ k ∈ (Finset.univ.erase j), face (segOf (h k)) ν = {x} := by
    rw [hxdef, ← sum_singleton_eq]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hkj : k ≠ j := Finset.ne_of_mem_erase hk
    rw [face_segOf_cases, if_neg (hk_orth k hkj)]
    split_ifs <;> rfl
  rw [coe_zonoF, face_sum, ← Finset.sum_erase_add _ _ (Finset.mem_univ j), hrest,
    face_segOf_cases, if_pos hj_orth]
  simp only [segOf, Set.singleton_add, Set.image_insert_eq, Set.image_singleton, add_zero]

/-! ## §2. Transporting membership from `zonoF` to `Sphi`

Pure one-directional set/half-space argument; no face-set equality claimed. -/

/-- `zonoF univ h ⊆ Sphi` as sets, since `Sphi` is lattice-convex and
`Conv Sphi = Conv (zonoF univ h)`. Same pattern as `DecompData.lean`'s `subset_Sphi`. -/
theorem zonoF_sub_Sphi {ξ : Config ℤ} (d : DecompDataZ ξ) {z : ℤ × ℤ}
    (hz : z ∈ zonoF Finset.univ d.toDecompData.h) :
    z ∈ d.toDecompData.Sphi := by
  have hconv : Conv (zonoF Finset.univ d.toDecompData.h) = Conv d.toDecompData.Sphi := by
    rw [d.toDecompData.Sphi_eq,
      Conv_supp_prod_eq_Conv_zonoF Finset.univ d.toDecompData.h
        (fun k _ => d.toDecompData.h_ne k)]
  exact d.Sphi_conv z (hconv ▸ subset_Conv hz)

/-- A point maximizing `dot ν` over `zonoF univ h`, if it also lies in `Sphi`, maximizes
`dot ν` over `Sphi` too — because `Conv Sphi = Conv (zonoF univ h)`, so no point of `Sphi`
(all of which lie in `Conv Sphi`) can exceed the half-space bound the maximizer already
establishes on the whole convex hull. -/
theorem mem_face_Sphi_of_mem_face_zonoF {ξ : Config ℤ} (d : DecompDataZ ξ)
    {ν x : ℤ × ℤ}
    (hxface : x ∈ face (↑(zonoF Finset.univ d.toDecompData.h) : Set (ℤ × ℤ)) ν)
    (hxSphi : x ∈ d.toDecompData.Sphi) :
    x ∈ face (↑d.toDecompData.Sphi : Set (ℤ × ℤ)) ν := by
  have hconv : Conv (zonoF Finset.univ d.toDecompData.h) = Conv d.toDecompData.Sphi := by
    rw [d.toDecompData.Sphi_eq,
      Conv_supp_prod_eq_Conv_zonoF Finset.univ d.toDecompData.h
        (fun k _ => d.toDecompData.h_ne k)]
  refine ⟨hxSphi, fun y hy => ?_⟩
  have hle : ∀ z ∈ zonoF Finset.univ d.toDecompData.h, dot ν z ≤ dot ν x := hxface.2
  have hhalf := Conv_subset_halfSpace (S := zonoF Finset.univ d.toDecompData.h) (n := ν)
    (c := dot ν x) hle
  have hyc : toReal y ∈ Conv (zonoF Finset.univ d.toDecompData.h) := by
    rw [hconv]; exact subset_Conv hy
  have hcast : (dot ν y : ℝ) ≤ (dot ν x : ℝ) := by
    rw [← rdot_toReal]; exact hhalf (toReal y) hyc
  exact_mod_cast hcast

/-! ## §3. Assembly: `faceLen B (± genPerp' (h j)) ≥ gcd(h j)` -/

/-- The two zonotope-face points, once known to lie in `Sphi` (via `zonoF_sub_Sphi`) and
to maximize `dot ν` there (via `mem_face_Sphi_of_mem_face_zonoF`), and once `Sphi`'s
`dot ν`-face is known (via `hEeq`/`hencard`) to be no bigger than `B`'s, give
`gcd(h j) - 1` more intermediate lattice points on the segment between them inside `B`
(`latticeConvex_between` on `Sphi`, then the encard transport) — hence
`(face B ν).encard ≥ gcd(h j) + 1`, i.e. `faceLen B ν ≥ gcd(h j)`.

Left `sorry`-marked as the composition step; §1/§2 above (the genuinely new content,
supplying the previously-missing bridge) are fully proved with clean axioms. -/
theorem faceLen_ge_gcd {ξ : Config ℤ} (d : DecompDataZ ξ)
    {B : Set (ℤ × ℤ)} (hBfin : B.Finite) (_hBne : B.Nonempty)
    (_hlcB : Nivat.IsLatticeConvexRegion B)
    (_hEeq : Nivat.LE2.E B = Nivat.LE2.E (↑d.toDecompData.Sphi : Set (ℤ × ℤ)))
    (hencard : ∀ n ∈ Nivat.LE2.E B,
      (face (↑d.toDecompData.Sphi : Set (ℤ × ℤ)) n).encard ≤ (face B n).encard)
    {j : Fin d.toDecompData.m} {ν : ℤ × ℤ} (hν_ne : ν ≠ 0)
    (hj_orth : dot ν (d.toDecompData.h j) = 0) (hνEB : ν ∈ Nivat.LE2.E B) :
    (Int.gcd (d.toDecompData.h j).1 (d.toDecompData.h j).2 : ℤ) ≤
      (Nivat.PolyChain.faceLen B ν : ℤ) := by
  classical
  set Gn : ℕ := Int.gcd (d.toDecompData.h j).1 (d.toDecompData.h j).2 with hGndef
  set G : ℤ := (Gn : ℤ) with hGdef
  set u : ℤ × ℤ := Nivat.LE2.primPart (d.toDecompData.h j) with hudef
  have hjne : d.toDecompData.h j ≠ 0 := d.toDecompData.h_ne j
  obtain ⟨huprim, hu_exists⟩ := Nivat.LE2.primPart_spec hjne
  have hune : u ≠ 0 := huprim.ne_zero
  -- `h j = G • u`.
  have hGpos : 0 < Gn := Nat.pos_of_ne_zero (by
    intro hz; apply hjne
    rw [Int.gcd_eq_zero_iff] at hz
    exact Prod.ext hz.1 hz.2)
  have hhu : d.toDecompData.h j = G • u := by
    show d.toDecompData.h j = ((Int.gcd (d.toDecompData.h j).1 (d.toDecompData.h j).2 : ℤ)) •
      Nivat.LE2.primPart (d.toDecompData.h j)
    ext
    · show (d.toDecompData.h j).1 =
        (Int.gcd (d.toDecompData.h j).1 (d.toDecompData.h j).2 : ℤ) *
          ((d.toDecompData.h j).1 / (Int.gcd (d.toDecompData.h j).1 (d.toDecompData.h j).2 : ℤ))
      exact (Int.mul_ediv_cancel' (Int.gcd_dvd_left _ _)).symm
    · show (d.toDecompData.h j).2 =
        (Int.gcd (d.toDecompData.h j).1 (d.toDecompData.h j).2 : ℤ) *
          ((d.toDecompData.h j).2 / (Int.gcd (d.toDecompData.h j).1 (d.toDecompData.h j).2 : ℤ))
      exact (Int.mul_ediv_cancel' (Int.gcd_dvd_right _ _)).symm
  have hdotu0 : dot ν u = 0 := by
    have hz : G * dot ν u = 0 := by
      have := hj_orth
      rw [hhu, dot_zsmul_right'] at this
      exact this
    have hGne0 : G ≠ 0 := by
      rw [hGdef]; exact_mod_cast hGpos.ne'
    exact (mul_eq_zero.mp hz).resolve_left hGne0
  -- The two zonotope-face points, transported into `face Sphi ν`.
  set x : ℤ × ℤ := ∑ k ∈ (Finset.univ.erase j),
    (if 0 < dot ν (d.toDecompData.h k) then d.toDecompData.h k else 0) with hxdef
  have hpair := face_zonoF_pair d.toDecompData.h d.toDecompData.h_ne d.toDecompData.h_dir j ν
    hν_ne hj_orth
  rw [← hxdef] at hpair
  have hx_face_zono : x ∈ face (↑(zonoF Finset.univ d.toDecompData.h) : Set (ℤ × ℤ)) ν := by
    rw [hpair]; exact Set.mem_insert _ _
  have hxh_face_zono :
      x + d.toDecompData.h j ∈
        face (↑(zonoF Finset.univ d.toDecompData.h) : Set (ℤ × ℤ)) ν := by
    rw [hpair]; exact Set.mem_insert_of_mem _ rfl
  have hx_zono : x ∈ zonoF Finset.univ d.toDecompData.h := hx_face_zono.1
  have hxh_zono : x + d.toDecompData.h j ∈ zonoF Finset.univ d.toDecompData.h := hxh_face_zono.1
  have hx_Sphi : x ∈ d.toDecompData.Sphi := zonoF_sub_Sphi d hx_zono
  have hxh_Sphi : x + d.toDecompData.h j ∈ d.toDecompData.Sphi := zonoF_sub_Sphi d hxh_zono
  have hx_face_Sphi : x ∈ face (↑d.toDecompData.Sphi : Set (ℤ × ℤ)) ν :=
    mem_face_Sphi_of_mem_face_zonoF d hx_face_zono hx_Sphi
  have hxh_face_Sphi : x + d.toDecompData.h j ∈ face (↑d.toDecompData.Sphi : Set (ℤ × ℤ)) ν :=
    mem_face_Sphi_of_mem_face_zonoF d hxh_face_zono hxh_Sphi
  -- All `Gn + 1` intermediate lattice points `x + t • u` lie in `face Sphi ν`.
  have hstep : ∀ t : ℕ, t ≤ Gn → x + (t : ℤ) • u ∈ face (↑d.toDecompData.Sphi : Set (ℤ × ℤ)) ν := by
    intro t ht
    have hmemS : x + (t : ℤ) • u ∈ d.toDecompData.Sphi := by
      have := Nivat.Claim47.latticeConvex_between d.Sphi_conv
        (z₀ := x) (u := u) (a := (0:ℤ)) (b := G) (m := (t:ℤ))
        (by simpa using hx_face_Sphi.1) (by rw [← hhu]; simpa using hxh_face_Sphi.1)
        (by norm_num) (by rw [hGdef]; exact_mod_cast ht)
      simpa using this
    refine ⟨hmemS, fun y hy => ?_⟩
    have hdoteq : dot ν (x + (t : ℤ) • u) = dot ν x := by
      rw [Nivat.LE2.dot_add, dot_zsmul_right', hdotu0]; ring
    rw [hdoteq]
    exact hx_face_Sphi.2 y hy
  -- Package as an injective map into `face Sphi ν`, giving an `encard` lower bound.
  have hinj : Function.Injective (fun t : Fin (Gn + 1) => x + ((t : ℕ) : ℤ) • u) := by
    intro t1 t2 heq
    simp only at heq
    have : ((t1 : ℕ) : ℤ) • u = ((t2 : ℕ) : ℤ) • u := add_left_cancel heq
    have huvne : u.1 ≠ 0 ∨ u.2 ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hune (Prod.ext hc.1 hc.2)
    have hteq : ((t1 : ℕ) : ℤ) = ((t2 : ℕ) : ℤ) := by
      rcases huvne with h1 | h2
      · have := congrArg Prod.fst this
        simp only [Prod.smul_fst, smul_eq_mul] at this
        exact mul_right_cancel₀ h1 this
      · have := congrArg Prod.snd this
        simp only [Prod.smul_snd, smul_eq_mul] at this
        exact mul_right_cancel₀ h2 this
    have : (t1 : ℕ) = (t2 : ℕ) := by exact_mod_cast hteq
    exact Fin.ext this
  have hmapsto : ∀ t : Fin (Gn + 1),
      x + ((t : ℕ) : ℤ) • u ∈ face (↑d.toDecompData.Sphi : Set (ℤ × ℤ)) ν := fun t =>
    hstep t (by omega)
  have hle1 : ((Gn + 1 : ℕ) : ℕ∞) ≤ (face (↑d.toDecompData.Sphi : Set (ℤ × ℤ)) ν).encard := by
    have := Set.encard_le_encard_of_injOn (f := fun t : Fin (Gn + 1) => x + ((t : ℕ) : ℤ) • u)
      (s := (Set.univ : Set (Fin (Gn + 1))))
      (t := face (↑d.toDecompData.Sphi : Set (ℤ × ℤ)) ν)
      (fun t _ => hmapsto t) (hinj.injOn)
    rwa [Set.encard_univ, ENat.card_eq_coe_fintype_card, Fintype.card_fin] at this
  have hle2 : ((Gn + 1 : ℕ) : ℕ∞) ≤ (face B ν).encard := le_trans hle1 (hencard ν hνEB)
  have hfaceBfin : (face B ν).Finite := hBfin.subset (face_subset B ν)
  obtain ⟨n, hn⟩ := hfaceBfin.exists_encard_eq_coe
  rw [hn] at hle2
  have hnge : Gn + 1 ≤ n := by exact_mod_cast hle2
  have : Nivat.PolyChain.faceLen B ν = n - 1 := by
    unfold Nivat.PolyChain.faceLen
    rw [hn]; simp
  rw [this]
  have hfin2 : Gn ≤ n - 1 := by omega
  rw [hGdef]
  exact_mod_cast hfin2

end Nivat.HsuppLengthBound

#print axioms Nivat.HsuppLengthBound.face_zonoF_pair
#print axioms Nivat.HsuppLengthBound.zonoF_sub_Sphi
#print axioms Nivat.HsuppLengthBound.mem_face_Sphi_of_mem_face_zonoF
#print axioms Nivat.HsuppLengthBound.faceLen_ge_gcd
