/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.HsuppTowerBase2
import Nivat.External.Colle.TowerConstruct
import Nivat.External.Colle.TowerHBSub
import Nivat.External.Colle.TowerHBase

/-!
# `hsupp_tower_general` — the extremality derivation, generalized past `I = 0`

`lane-tower3`, dispatched by team-lead 2026-09-22 ("Focus on closing the support-point
induction past `I = 0` — that's real content, feeds both `h0` and `hmax`").

## What "past `I = 0`" actually needs

`HsuppTowerBase2.b0pt_face_facts` is already stated for *arbitrary* edge normals `negm₀ w₀`
of `B` satisfying two fan-adjacency hypotheses (`hdet_order`, `hno_between`); its "`I = 0`"
character comes only from *where those two hypotheses were discharged*, not from the theorem
itself. `TowerConstruct.lean` already proves the fan-adjacency facts at *every* tower index:
`det_pos_nprevOf_succ` (`:1210`) and `no_between_nprevOf` (`:1522`) are both stated for a
general `I` with `I + 1` in range — they are not built by recursion on `I`, but derived
directly from the global chain order (`det_pos_chain`/`det_pos_extChain`), so no induction on
`ℕ` is needed to generalize.

So the generalization is: (1) strip `b0pt_face_facts`'s proof down to a fully general,
`nuGen`-free two-normal extremality lemma (`face_extremal_of_adjacent`), then (2) instantiate
it at `nprevOf d nℓ vl u' i I` / `nprevOf d nℓ vl u' i (I+1)` for arbitrary `I`, branch-aware
on the sign of `det u' (-vl)` exactly as `faceStart_nprevOf_succ` already is. The result,
`faceStart_nprevOf_extremal`, is the level-`I` generalization of `b0pt_face_facts`: at every
tower level `I` (with `I+1` still in range), the shared vertex between the faces at
`nprevOf I` and `nprevOf (I+1)` both lies in, and maximizes `dot (dir ·)` over, the "earlier"
face of the pair (whichever of the two the branch identifies as such).

## Status

0 sorry, axiom-clean.
-/

set_option autoImplicit false

namespace Nivat.HsuppTowerBase

open Nivat Nivat.LE2 Nivat.PolyChain Nivat.ColleReg Nivat.ConeRegion Nivat.RegionSweep

/-! ## Step 1: the two-normal extremality lemma, stripped of `nuGen`/`negm₀` naming

This is literally `b0pt_face_facts`'s proof with the names generalized — `ν₁ := nuGen w₀`,
`ν₂ := negm₀` there. -/

/-- **General two-normal extremality.** If `ν₁` is fan-adjacent to `ν₂` in `T`'s edge-normal
set (`0 < det ν₁ ν₂`, nothing strictly between), the shared vertex `faceStart T ν₂` both lies
in `face T ν₁` and maximizes `dot (dir ν₁)` over that face. -/
theorem face_extremal_of_adjacent {T : Set (ℤ × ℤ)} (hTfin : T.Finite)
    (hTconv : Nivat.IsLatticeConvexRegion T)
    {ν₁ ν₂ : ℤ × ℤ} (hν₁ : ν₁ ∈ E T) (hν₂ : ν₂ ∈ E T)
    (hdet_order : 0 < det ν₁ ν₂)
    (hno_between : ∀ μ ∈ E T, ¬ (0 < det ν₁ μ ∧ 0 < det μ ν₂)) :
    (faceStart T ν₂ ∈ face T ν₁) ∧
    (∀ z ∈ face T ν₁, dot (dir ν₁) z ≤ dot (dir ν₁) (faceStart T ν₂)) := by
  have hi := adjacent_shared_vertex hTfin hTconv hν₁ hν₂ hdet_order hno_between
  refine ⟨hi ▸ faceEnd_mem hTconv hTfin hν₁, ?_⟩
  rw [← hi]
  exact faceEnd_maxdir hTconv hTfin hν₁ rfl

/-! ## Step 2: instantiate at `nprevOf I` / `nprevOf (I+1)`, branch-aware, for general `I` -/

variable {ξ : Nivat.Config ℤ}

open Nivat.ColleReg in
/-- **The level-`I` generalization of `b0pt_face_facts`.** At every tower index `I` (with
`I + 1` still in `sortedCand`'s range), the shared vertex between the faces of `B` at
`nprevOf I` and `nprevOf (I+1)` lies in, and is extremal for, whichever of the two faces the
branch (`det u' (-vl)`'s sign, the same global branch `faceStart_nprevOf_succ` splits on)
identifies as the "earlier" one. Setting `I := 0` recovers exactly `b0pt_face_facts`'s
content once `negm₀ := nprevOf 0`, `nuGen w₀ := nprevOf 1` are unwound via `dir_nprevOf`. -/
theorem faceStart_nprevOf_extremal {B : Set (ℤ × ℤ)} (d : Nivat.Colle35.DecompData ξ)
    {vl nℓ u' : ℤ × ℤ}
    (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (henv : Nivat.LE2.EnvOf (↑d.Sphi : Set (ℤ × ℤ)) B)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0)
    (hBfin : B.Finite) (hBconv : Nivat.IsLatticeConvexRegion B)
    (hadjB : ∀ n ∈ E B, ¬ (dot n vl < 0 ∧ 0 < dot n u'))
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) (hnu : dot nℓ u' < 0) (hnℓ_ne : nℓ ≠ 0)
    {I : ℕ} (hIlen1 : I < (sortedCand d nℓ u' i).length)
    (hIlen2 : I + 1 < (sortedCand d nℓ u' i).length) :
    (0 < det u' (-vl) ∧
      (faceStart B (nprevOf d nℓ vl u' i (I + 1)) ∈ face B (nprevOf d nℓ vl u' i I)) ∧
      (∀ z ∈ face B (nprevOf d nℓ vl u' i I),
        dot (dir (nprevOf d nℓ vl u' i I)) z
          ≤ dot (dir (nprevOf d nℓ vl u' i I)) (faceStart B (nprevOf d nℓ vl u' i (I + 1))))) ∨
    (det u' (-vl) < 0 ∧
      (faceStart B (nprevOf d nℓ vl u' i I) ∈ face B (nprevOf d nℓ vl u' i (I + 1))) ∧
      (∀ z ∈ face B (nprevOf d nℓ vl u' i (I + 1)),
        dot (dir (nprevOf d nℓ vl u' i (I + 1))) z
          ≤ dot (dir (nprevOf d nℓ vl u' i (I + 1))) (faceStart B (nprevOf d nℓ vl u' i I)))) := by
  have hadj_succ := Nivat.ColleReg.no_between_nprevOf d hvl_prim hprim hperp henv i hdoth hadjB
    hunimod hnu hnℓ_ne hIlen1 hIlen2
  rcases Nivat.ColleReg.det_pos_nprevOf_succ d hvl_prim hprim hperp henv i hdoth hadjB hunimod hnu
      hnℓ_ne hIlen1 hIlen2 with ⟨hpos, hdetpos⟩ | ⟨hneg, hdetpos⟩
  · left
    refine ⟨hpos, ?_⟩
    exact face_extremal_of_adjacent hBfin hBconv
      (Nivat.ColleReg.nprevOf_mem_E_B d hvl_prim hprim hperp henv i hdoth hIlen1)
      (Nivat.ColleReg.nprevOf_mem_E_B d hvl_prim hprim hperp henv i hdoth hIlen2)
      hdetpos (hadj_succ.1 hpos)
  · right
    refine ⟨hneg, ?_⟩
    exact face_extremal_of_adjacent hBfin hBconv
      (Nivat.ColleReg.nprevOf_mem_E_B d hvl_prim hprim hperp henv i hdoth hIlen2)
      (Nivat.ColleReg.nprevOf_mem_E_B d hvl_prim hprim hperp henv i hdoth hIlen1)
      hdetpos (hadj_succ.2 hneg)

/-! ## Step 3: `dot (nprevOf ... I) vl < 0` at every level `I`

The boundedness argument for `hmax`/`h0` needs `m := nprevOf ... I` to have non-positive `dot`
against `vl` too (not just against `u'`/`wtower`), since `coneRegion B vl u'` already contains
the unbounded `vl`-ray at level `0` — a recession-cone requirement, not a formalization
artifact. `TowerConstruct.lean` proves this for `u'`/`wtower` (`dot_nprevOf_neg`) but not `vl`;
this closes the gap via the same `genPerp'`/`det` bridge `HsuppTowerBase2`'s Bridge 3 used at
`I = 0`, except now `wtower ... I` is identified with `wgen d nℓ j` for *whichever* `j` the
membership `wtower ... I ∈ candSet d nℓ u' i` produces (via `candSet`'s definition as an image
of `wgen`), rather than a hardcoded `j₀`. -/

open Nivat.ColleReg in
/-- **`vl`-boundedness of `nprevOf`, at every level `I`.** Both branches of `nprevOf`'s
definition (`0 < det u' (-vl)` or not) give a strictly negative result, by the same
sign-chase as `det_nprevOf_genPerp'u'_neg`: `det_pos_u'_wtower` pins the sign of
`det u' (wtower I)` to `det u' (-vl)`'s branch, and `det_w_u'_sign_eq_of_hadjB` (applied at
the generator index for `wtower I`) transports that sign from `u'` to `vl`. -/
theorem dot_nprevOf_vl_neg {B : Set (ℤ × ℤ)} (d : Nivat.Colle35.DecompData ξ)
    {vl nℓ u' : ℤ × ℤ}
    (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (henv : Nivat.LE2.EnvOf (↑d.Sphi : Set (ℤ × ℤ)) B)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0)
    (hadjB : ∀ n ∈ E B, ¬ (dot n vl < 0 ∧ 0 < dot n u'))
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) (hnu : dot nℓ u' < 0) (hnℓ_ne : nℓ ≠ 0)
    {I : ℕ} (hIlen : I < (sortedCand d nℓ u' i).length) :
    dot (nprevOf d nℓ vl u' i I) vl < 0 := by
  have hwmem : wtower d nℓ vl u' i I ∈ candSet d nℓ u' i := mem_candSet_wtower hIlen
  obtain ⟨hne, hv_img⟩ := Finset.mem_erase.mp hwmem
  obtain ⟨j, hj_mem, hj⟩ := Finset.mem_image.mp hv_img
  have hij : j ≠ i := (Finset.mem_erase.mp hj_mem).1
  have hwu' : wgen d nℓ j ≠ u' := hj ▸ hne
  have hwprim : Primitive (wtower d nℓ vl u' i I) :=
    prim_of_mem_candSet d hvl_prim hprim hperp i hdoth hwmem
  have hwprim' : Prim (wtower d nℓ vl u' i I) := Nivat.LE2.prim_iff_primitive.mpr hwprim
  have hsignUp := det_pos_u'_wtower d hvl_prim hprim hperp henv i hdoth hadjB hunimod hnu hnℓ_ne
    hIlen
  have hiff := det_w_u'_sign_eq_of_hadjB d hvl_prim hprim hperp henv i hdoth hadjB hunimod hnu
    hij hwu'
  rw [hj] at hiff
  have hune : det u' (wtower d nℓ vl u' i I) ≠ 0 := by
    intro h0; rw [h0] at hsignUp; simp at hsignUp
  have hvne : det (wtower d nℓ vl u' i I) vl ≠ 0 :=
    det_ne_zero_of_dot_nl_neg hvl_prim hperp
      (dot_of_mem_candSet d hvl_prim hprim hperp i hdoth hwmem)
  have hval : ∀ x : ℤ × ℤ, dot (Nivat.LE2.genPerp' (wtower d nℓ vl u' i I)) x
      = det (wtower d nℓ vl u' i I) x := by
    intro x; rw [dot_comm, ← det_eq_dot_genPerp' hwprim' x]
  unfold nprevOf
  by_cases hc : 0 < det u' (-vl)
  · simp only [hc, if_true, hval]
    have hupos : 0 < det u' (wtower d nℓ vl u' i I) := by
      rcases mul_pos_iff.mp hsignUp with ⟨h1, -⟩ | ⟨-, h2⟩
      · exact h1
      · linarith
    have hu'neg : det (wtower d nℓ vl u' i I) u' < 0 := by
      have hskew := det_skew (wtower d nℓ vl u' i I) u'
      linarith [hskew, hupos]
    rcases lt_or_gt_of_ne hvne with hlt | hgt
    · exact hlt
    · exact absurd (hiff.mp hgt) (not_lt.mpr (le_of_lt hu'neg))
  · simp only [hc, if_false, dot_neg_left, hval]
    have huneg : det u' (wtower d nℓ vl u' i I) < 0 := by
      rcases mul_pos_iff.mp hsignUp with ⟨-, h2⟩ | ⟨h1, -⟩
      · exact absurd h2 hc
      · exact h1
    have hu'pos : 0 < det (wtower d nℓ vl u' i I) u' := by
      have hskew := det_skew (wtower d nℓ vl u' i I) u'
      linarith [hskew, huneg]
    have hvlpos : 0 < det (wtower d nℓ vl u' i I) vl := hiff.mpr hu'pos
    linarith

/-! ## Step 4: boundedness of `dot (nprevOf ... I)` over the swept tower, at every level `I`

`TowerPackage.lean`'s `dot_nl_le_of_mem_tower` is the right induction template — it already
fixes a *single* normal `nℓ` across the whole sweep-count induction — but its hypotheses
(`dot nℓ vl = 0`, `dot nℓ u' = -1` exactly, `∀ i, dot nℓ (wtower i) < 0` unconditionally) are
tighter than what `nprevOf` gives: `dot_nprevOf_vl_neg`/`dot_nprevOf_neg` only give strict
inequalities, and `dot_nprevOf_neg` only reaches tower directions `wtower k` for `k < I` (the
ones actually swept by `tower _ I`), not all `k`. Relaxing to `≤`/bounded-`k` hypotheses proves
the same induction with no other change — no separate auxiliary induction variable is needed:
fixing `m := nprevOf d nℓ vl u' i I` for the specific `I` under study, and running the sweep
induction out to exactly `n := I`, is precisely what `tower _ I` unfolds to. -/

/-- **Generalization of `dot_nl_le_of_mem_tower` to `≤`/bounded-index hypotheses.** -/
theorem dot_le_of_mem_tower_bounded {B : Set (ℤ × ℤ)} (hBfin : B.Finite)
    {vl u' m : ℤ × ℤ} (hperp : dot m vl ≤ 0) (hnu : dot m u' ≤ 0)
    (wtower : ℕ → ℤ × ℤ) (n : ℕ) (hwlow : ∀ k, k < n → dot m (wtower k) ≤ 0) :
    ∃ top : ℤ, ∀ z ∈ tower (coneRegion B vl u') wtower n, dot m z ≤ top := by
  obtain ⟨top, htop⟩ : ∃ top : ℤ, ∀ b ∈ B, dot m b ≤ top := by
    have hfin : (dot m '' B).Finite := hBfin.image _
    obtain ⟨top, htop⟩ := hfin.bddAbove
    exact ⟨top, fun b hb => htop ⟨b, hb, rfl⟩⟩
  refine ⟨top, ?_⟩
  induction n with
  | zero =>
    intro z hz
    simp only [tower] at hz
    rw [mem_coneRegion_iff] at hz
    obtain ⟨b, hb, s, t, rfl⟩ := hz
    have heq : dot m (b + (s : ℤ) • vl + (t : ℤ) • u')
        = dot m b + (s : ℤ) * dot m vl + (t : ℤ) * dot m u' := by
      rw [dot_add, dot_add]
      congr 2
      · cases m; cases vl; simp only [dot, Prod.smul_mk, smul_eq_mul]; ring
      · cases m; cases u'; simp only [dot, Prod.smul_mk, smul_eq_mul]; ring
    rw [heq]
    have hs : (0 : ℤ) ≤ (s : ℤ) := by positivity
    have ht : (0 : ℤ) ≤ (t : ℤ) := by positivity
    nlinarith [htop b hb, mul_nonpos_of_nonneg_of_nonpos hs hperp,
      mul_nonpos_of_nonneg_of_nonpos ht hnu]
  | succ k ih =>
    intro z hz
    simp only [tower] at hz
    rw [Nivat.RegionSweep.mem_sweep] at hz
    obtain ⟨g, hg, t, rfl⟩ := hz
    have hgle := ih (fun j hj => hwlow j (by omega)) g hg
    have heq : dot m (g + (t : ℤ) • wtower k) = dot m g + (t : ℤ) * dot m (wtower k) := by
      rw [dot_add]
      congr 1
      cases m; cases (wtower k); simp only [dot, Prod.smul_mk, smul_eq_mul]; ring
    rw [heq]
    have ht : (0 : ℤ) ≤ (t : ℤ) := by positivity
    nlinarith [hwlow k (by omega), hgle, mul_nonpos_of_nonneg_of_nonpos ht (hwlow k (by omega))]

open Nivat.ColleReg in
/-- **`nprevOf`-boundedness over the tower, at every level `I`.** The normal `nprevOf ... I` is
bounded above on `tower (coneRegion B vl u') (wtower d nℓ vl u' i) I` by its own max on the
finite seed `B` — the fact `hmax`/`h0` need past `I = 0`. -/
theorem dot_nprevOf_le_of_mem_tower {B : Set (ℤ × ℤ)} (d : Nivat.Colle35.DecompData ξ)
    (hBfin : B.Finite)
    {vl nℓ u' : ℤ × ℤ}
    (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (henv : Nivat.LE2.EnvOf (↑d.Sphi : Set (ℤ × ℤ)) B)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0)
    (hadjB : ∀ n ∈ E B, ¬ (dot n vl < 0 ∧ 0 < dot n u'))
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) (hnu : dot nℓ u' < 0) (hnℓ_ne : nℓ ≠ 0)
    {I : ℕ} (hIlen : I < (sortedCand d nℓ u' i).length) :
    ∃ top : ℤ, ∀ z ∈ tower (coneRegion B vl u') (wtower d nℓ vl u' i) I,
      dot (nprevOf d nℓ vl u' i I) z ≤ top := by
  have hIlen' : I ≤ (sortedCand d nℓ u' i).length := le_of_lt hIlen
  refine dot_le_of_mem_tower_bounded hBfin ?_ ?_ (wtower d nℓ vl u' i) I ?_
  · exact le_of_lt (dot_nprevOf_vl_neg d hvl_prim hprim hperp henv i hdoth hadjB hunimod hnu
      hnℓ_ne hIlen)
  · have h0 := dot_nprevOf_neg d hvl_prim hprim hperp henv i hdoth hadjB hunimod hnu hnℓ_ne
      hIlen (j := 0) (by omega)
      -- `extChain 0 = u'` definitionally
    exact le_of_lt h0
  · intro k hk
    have hj := dot_nprevOf_neg d hvl_prim hprim hperp henv i hdoth hadjB hunimod hnu hnℓ_ne
      hIlen (j := k + 1) (by omega)
    exact le_of_lt hj

/-! ## Step 5: attainment — the `h0` witness

`B ⊆ tower (coneRegion B vl u') w n` for every `n` (`B_subset_tower`, `TowerHBSub.lean:27`,
already 0-sorry). Combined with `B`'s own max in direction `nprevOf ... I` (attained, since `B`
is finite and nonempty) and the boundedness of Step 4, the max over `B` *is* the max over the
whole swept tower region at level `I` — this is `h0`'s existential witness. -/

/-- **General-purpose**: a finite nonempty set attains its `dot n` maximum. -/
theorem exists_max_dot {B : Set (ℤ × ℤ)} (hBfin : B.Finite) (hBne : B.Nonempty) (n : ℤ × ℤ) :
    ∃ b ∈ B, ∀ b' ∈ B, dot n b' ≤ dot n b :=
  B.exists_max_image (dot n) hBfin hBne

/-- **`dot_le_of_mem_tower_bounded`, with the bound supplied explicitly.** Same induction, but
`top` is a hypothesis instead of derived from `Set.Finite.bddAbove`, so the caller can pin it to
the actual attained max instead of an arbitrary upper bound. -/
theorem dot_le_of_mem_tower_of_bound {B : Set (ℤ × ℤ)}
    {vl u' m : ℤ × ℤ} (hperp : dot m vl ≤ 0) (hnu : dot m u' ≤ 0)
    (wtower : ℕ → ℤ × ℤ) (n : ℕ) (hwlow : ∀ k, k < n → dot m (wtower k) ≤ 0)
    {top : ℤ} (htop : ∀ b ∈ B, dot m b ≤ top) :
    ∀ z ∈ tower (coneRegion B vl u') wtower n, dot m z ≤ top := by
  induction n with
  | zero =>
    intro z hz
    simp only [tower] at hz
    rw [mem_coneRegion_iff] at hz
    obtain ⟨b, hb, s, t, rfl⟩ := hz
    have heq : dot m (b + (s : ℤ) • vl + (t : ℤ) • u')
        = dot m b + (s : ℤ) * dot m vl + (t : ℤ) * dot m u' := by
      rw [dot_add, dot_add]
      congr 2
      · cases m; cases vl; simp only [dot, Prod.smul_mk, smul_eq_mul]; ring
      · cases m; cases u'; simp only [dot, Prod.smul_mk, smul_eq_mul]; ring
    rw [heq]
    have hs : (0 : ℤ) ≤ (s : ℤ) := by positivity
    have ht : (0 : ℤ) ≤ (t : ℤ) := by positivity
    nlinarith [htop b hb, mul_nonpos_of_nonneg_of_nonpos hs hperp,
      mul_nonpos_of_nonneg_of_nonpos ht hnu]
  | succ k ih =>
    intro z hz
    simp only [tower] at hz
    rw [Nivat.RegionSweep.mem_sweep] at hz
    obtain ⟨g, hg, t, rfl⟩ := hz
    have hgle := ih (fun j hj => hwlow j (by omega)) g hg
    have heq : dot m (g + (t : ℤ) • wtower k) = dot m g + (t : ℤ) * dot m (wtower k) := by
      rw [dot_add]
      congr 1
      cases m; cases (wtower k); simp only [dot, Prod.smul_mk, smul_eq_mul]; ring
    rw [heq]
    have ht : (0 : ℤ) ≤ (t : ℤ) := by positivity
    nlinarith [hwlow k (by omega), hgle, mul_nonpos_of_nonneg_of_nonpos ht (hwlow k (by omega))]

open Nivat.ColleReg in
/-- **`h0`'s witness at every level `I`.** The point of `B` maximizing `dot (nprevOf ... I)`
also maximizes it over the entire swept tower region `tower (coneRegion B vl u') (wtower ...) I`
— since `B` embeds in that region (`B_subset_tower`) and nothing swept in afterwards can exceed
`B`'s own max (Step 4's bound, pinned to this specific attained value via
`dot_le_of_mem_tower_of_bound`). -/
theorem exists_max_nprevOf_of_mem_tower {B : Set (ℤ × ℤ)} (d : Nivat.Colle35.DecompData ξ)
    (hBfin : B.Finite) (hBne : B.Nonempty)
    {vl nℓ u' : ℤ × ℤ}
    (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (henv : Nivat.LE2.EnvOf (↑d.Sphi : Set (ℤ × ℤ)) B)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0)
    (hadjB : ∀ n ∈ E B, ¬ (dot n vl < 0 ∧ 0 < dot n u'))
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) (hnu : dot nℓ u' < 0) (hnℓ_ne : nℓ ≠ 0)
    {I : ℕ} (hIlen : I < (sortedCand d nℓ u' i).length) :
    ∃ b ∈ tower (coneRegion B vl u') (wtower d nℓ vl u' i) I,
      ∀ z ∈ tower (coneRegion B vl u') (wtower d nℓ vl u' i) I,
        dot (nprevOf d nℓ vl u' i I) z ≤ dot (nprevOf d nℓ vl u' i I) b := by
  obtain ⟨b, hb, hbmax⟩ := exists_max_dot hBfin hBne (nprevOf d nℓ vl u' i I)
  refine ⟨b, B_subset_tower (wtower d nℓ vl u' i) I hb, ?_⟩
  refine dot_le_of_mem_tower_of_bound ?_ ?_ (wtower d nℓ vl u' i) I ?_ hbmax
  · exact le_of_lt (dot_nprevOf_vl_neg d hvl_prim hprim hperp henv i hdoth hadjB hunimod hnu
      hnℓ_ne hIlen)
  · have h0 := dot_nprevOf_neg d hvl_prim hprim hperp henv i hdoth hadjB hunimod hnu hnℓ_ne
      hIlen (j := 0) (by omega)
    exact le_of_lt h0
  · intro k hk
    have hj := dot_nprevOf_neg d hvl_prim hprim hperp henv i hdoth hadjB hunimod hnu hnℓ_ne
      hIlen (j := k + 1) (by omega)
    exact le_of_lt hj

/-! ## Step 6: wiring into `hbase_of_prev_level_periodOn` — the `hbase` field, at every level `I`

`TowerHBase.hbase_of_prev_level_periodOn` reduces `hbase` to three inputs against the *sweep*
step `C := tower(...) I ↦ Rinf := sweep C (wtower ... I)`: `hmax` (a normal `m` bounded on `C`
by `b₀`), `hneg` (`dot m (wtower ... I) < 0`), and `hper` (periodicity of `C`, from outside this
file — the actual `I`-minimality machinery). The right `m` is `nprevOf ... (I+1)`, not
`nprevOf ... I`: `dot_nprevOf_neg` only reaches `dot (nprevOf ... I) (wtower k)` for `k < I`
(the steps *already* swept into `C`), not `k = I` (the *next* step out of `C`) — indeed
`dot (nprevOf ... I) (wtower ... I) = 0` by construction (`nprevOf I` is `wtower I`'s own
`genPerp'`). Stepping the normal to `nprevOf (I+1)` fixes this (`dot_nprevOf_neg` at `j = I+1`
reaches exactly `wtower I`), and `exists_max_nprevOf_of_mem_tower`/`dot_nprevOf_le_of_mem_tower`
at level `I+1` bound `nprevOf (I+1)` on the *bigger* region `tower(...) (I+1) ⊇ C`
(`tower_subset_succ`), hence on `C` itself. -/

open Nivat.ColleReg in
/-- **`hbase` at level `I`, modulo the previous level's periodicity.** Given that `C :=
tower (coneRegion B vl u') (wtower d nℓ vl u' i) I` is `(c • vl)`-periodic, produces the `b₀`
and the `hbase` obligation for `Rinf := sweep C (wtower d nℓ vl u' i I)` against the normal
`nprevOf d nℓ vl u' i (I + 1)`. -/
theorem exists_hbase_nprevOf {B : Set (ℤ × ℤ)} (d : Nivat.Colle35.DecompData ξ)
    (hBfin : B.Finite) (hBne : B.Nonempty)
    {vl nℓ u' : ℤ × ℤ}
    (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (henv : Nivat.LE2.EnvOf (↑d.Sphi : Set (ℤ × ℤ)) B)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0)
    (hadjB : ∀ n ∈ E B, ¬ (dot n vl < 0 ∧ 0 < dot n u'))
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) (hnu : dot nℓ u' < 0) (hnℓ_ne : nℓ ≠ 0)
    {I : ℕ} (hIlen2 : I + 1 < (sortedCand d nℓ u' i).length)
    {e : ℤ × ℤ} {c : ℤ}
    (hper : Nivat.Colle41.PeriodOn (T e ξ) (tower (coneRegion B vl u') (wtower d nℓ vl u' i) I)
      (c • vl)) :
    ∃ b₀ : ℤ, ∀ lev : ℕ → ℤ, lev 0 = b₀ →
      Nivat.Colle41.PeriodOn (T e ξ)
        (Nivat.L1Region.cut (sweep (tower (coneRegion B vl u') (wtower d nℓ vl u' i) I)
          (wtower d nℓ vl u' i I)) (nprevOf d nℓ vl u' i (I + 1)) lev 0) (c • vl) := by
  obtain ⟨b, hbmem, hbmax⟩ := exists_max_nprevOf_of_mem_tower d hBfin hBne hvl_prim hprim hperp
    henv i hdoth hadjB hunimod hnu hnℓ_ne hIlen2
  refine ⟨dot (nprevOf d nℓ vl u' i (I + 1)) b, ?_⟩
  refine hbase_of_prev_level_periodOn rfl ?_ ?_ hper
  · exact fun z hz => hbmax z (tower_subset_succ _ _ I hz)
  · have hneg := dot_nprevOf_neg d hvl_prim hprim hperp henv i hdoth hadjB hunimod hnu hnℓ_ne
      hIlen2 (j := I + 1) (le_refl _)
    exact hneg

end Nivat.HsuppTowerBase

#print axioms Nivat.HsuppTowerBase.face_extremal_of_adjacent
#print axioms Nivat.HsuppTowerBase.faceStart_nprevOf_extremal
#print axioms Nivat.HsuppTowerBase.dot_nprevOf_vl_neg
#print axioms Nivat.HsuppTowerBase.dot_le_of_mem_tower_bounded
#print axioms Nivat.HsuppTowerBase.dot_nprevOf_le_of_mem_tower
#print axioms Nivat.HsuppTowerBase.exists_max_dot
#print axioms Nivat.HsuppTowerBase.dot_le_of_mem_tower_of_bound
#print axioms Nivat.HsuppTowerBase.exists_max_nprevOf_of_mem_tower
#print axioms Nivat.HsuppTowerBase.exists_hbase_nprevOf
