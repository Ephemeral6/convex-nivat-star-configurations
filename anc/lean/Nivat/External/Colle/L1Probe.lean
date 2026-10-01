/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.Case2WindowProbe

/-!
# `L1Probe` — is `MaxBResidual` jointly satisfiable, and non-degenerately?

Falsification lane for leaf **L1**.  The leaf is `ColleReg.exists_L1MaxBResidual`
(`RegionSteps.lean`), a `sorry` whose conclusion is

  `∃ e u u' v c τ ε S₁ F, S₁ = S.image (· + v) ∧ L1Data.MaxBResidual ε u u' c τ S₁ F`

with `MaxBResidual` the six fields `det' prim c0 line0 base0 straddle` (`L1Assemble.lean`,
weak `base0` of 2026-09-19) over a `RegionFamily (T e ξ) u u' c` (`L1Region.lean:131`).

The method is the one that found both definition-level errors so far: **write the model, let
the kernel decide.**  Everything below is `#print axioms`-clean; nothing is argued.

## The model

* `ξL z = hstep z.1 + hstep z.2` with `hstep a = if 0 ≤ a then 1 else 0` — the sum of two
  half-plane indicators (`η₁` vertical-boundary, `η₂` horizontal-boundary).  Range `{0,1,2}`,
  **not periodic** (`per_ξL_eq_zero`), annihilated by `(X^{(1,0)}−1)(X^{(0,1)}−1)` — which is
  what makes the unit square, and every window containing unit squares at each vertex, a
  generating set (`orbitClosure_quad`, `isGeneratingSet_S₁L`).
* `u = (1,0)` (the period direction `ℓ`), `u' = (0,1)` (`v_{ℓ'}`), `c = 1`, `τ = 0`, `e = 0`.
* `F` = the half-planes `{z | -n ≤ z.1}` via `L1Region.ofCut`: `ξL` is `(1,0)`-periodic on
  `{0 ≤ z.1}` (where `η₁ ≡ 1`) and not on `ℤ²` (the jump between columns `-1` and `0`).  The
  maximal periodic index is `N = 0`.
* `S₁ = {-1,0} × {-1,0,1}`, side `ε = true`: the top face is the column `x = -1` (3 points,
  **outside** `F.R 0`), `derivedQ` is the column `x = 0` (3 points, inside), `pw = 2`, and
  `maxB = {(0,-1),(0,0)}`.

## What the kernel says

1. **`MaxBResidual` is satisfiable** (`maxBResidual_L`), and the leaf's conclusion holds at
   `ξ := ξL`, `S := S₁L`, `v := 0` (`l1Conclusion_L`, matched to the live target by the
   `type_of%` guard `l1_target_type_eq`).
2. **Non-degenerate**: both `u'`-faces have 3 points (`card_topFaceL`, `card_bottomFaceL`),
   `derivedQ` is nonempty (`derivedQ_L_nonempty`), `maxB` has two points, `ξL` is not periodic
   and `S₁L` is a genuine generating set.  Nothing is vacuous: `F.union_not` and the
   straddle's `¬PeriodOn (F.R 1)` are both witnessed by a real disagreement.
3. **Where the content sits.** `straddle` is the only field that *constrains the placement*:
   with `S₁` entirely inside `F.R 0` the field is **false** (`not_straddle_inside`) — the
   face's `u'`-line is then periodic for free and `F.R 1` is not — so the face must stick out
   of `F.R N`, exactly Collé's Claim 4.7 set-up (`𝒯 \ ℓ'_𝒯 ⊂ 𝓡^N_I`, `𝒯 ⊄ 𝓡^N_I`,
   `b3_colle2.txt:820`).  And `base0`'s weak form is what lets the face stick out: the strong
   form's `b ∈ maxB` with `b + S₁ ⊆ F.R 0` is **false** here (`not_strong_base0_L`), because
   `maxB ⊆ {x = 0}` puts `b + (-1, ·)` in column `-1`.  So the 2026-09-19 weakening is not
   cosmetic on this model — it is the difference between satisfiable and not.
4. **Binders of the leaf on `ξL`** (§4): `hSgen`, `hgen`, `hℓ_nel`, `hℓ_pos`, `hℓ_neg`,
   `hxper`, `hp_mem`, `hp_ne`, `hvl_ne`, `hvl_prim`, `hdet_vl`, `hdet_ℓ` all hold at the kernel
   with `ℓ = (1,0)`, `vl = (0,1)`, `xper = hstep z.1 + 1`, `p = (0,1)`.  `hξ` is **false**
   (`not_isCounterexample_ξL`: `ξL` takes the value `0`), so — as with every model in this
   project — this is a satisfiability result for the *conclusion and twelve binders*, not for
   the theorem.  `hdef` and `hcase1` are **not measured** (a real-normal complexity bound and a
   `DecompDataZ`, respectively).
-/

set_option autoImplicit false

namespace Nivat.L1Probe

open Nivat Nivat.LE2 Nivat.Colle Nivat.Colle35 Nivat.ColleReg Nivat.ColleReg.L1Data
  Nivat.L1Region Nivat.Case2WindowProbe

/-! ## §1 The configuration and the window -/

/-- Half-line indicator on `ℤ`. -/
def hstep (a : ℤ) : ℤ := if 0 ≤ a then 1 else 0

/-- `η₁ + η₂`: the sum of the two coordinate half-plane indicators. -/
def ξL : Config ℤ := fun z => hstep z.1 + hstep z.2

/-- `u = (1,0)`, Collé's period direction `ℓ`. -/
def uL : ℤ × ℤ := (1, 0)
/-- `u' = (0,1)`, Collé's `v_{ℓ'}`. -/
def u'L : ℤ × ℤ := (0, 1)

/-- `𝒯 = {-1,0} × {-1,0,1}`. -/
def S₁L : Finset (ℤ × ℤ) := ({-1, 0} : Finset ℤ) ×ˢ ({-1, 0, 1} : Finset ℤ)

theorem mem_S₁L {z : ℤ × ℤ} : z ∈ S₁L ↔ (-1 ≤ z.1 ∧ z.1 ≤ 0) ∧ (-1 ≤ z.2 ∧ z.2 ≤ 1) := by
  simp only [S₁L, Finset.mem_product, Finset.mem_insert, Finset.mem_singleton]
  omega

theorem S₁L_nonempty : S₁L.Nonempty := ⟨0, mem_S₁L.mpr (by norm_num)⟩

theorem latticeConvex_S₁L : LatticeConvex S₁L :=
  Gen.latticeConvex_of_box (fun _ => mem_S₁L)

/-- `ξL` is not periodic: its period group is trivial.  Two sites pin each coordinate. -/
theorem per_ξL_eq_zero {h : ℤ × ℤ} (hh : h ∈ Per ξL) : h = 0 := by
  rw [mem_Per_iff] at hh
  have e0 := congrFun hh (-h.1, -h.2)
  have e1 := congrFun hh (-1 - h.1, -1 - h.2)
  simp only [T, ξL, hstep, Prod.fst_add, Prod.snd_add] at e0 e1
  rw [Prod.ext_iff]
  simp only [Prod.fst_zero, Prod.snd_zero]
  split_ifs at e0 e1 <;> omega

theorem not_isPeriodic_ξL : ¬ IsPeriodic ξL := by
  rintro ⟨h, hh, hne⟩
  exact hne (per_ξL_eq_zero hh)

/-- `ξL` is not a counterexample in the sense of `IsMinimalCounterexample`: it takes the
value `0` at `(-1,-1)`.  So `hξ` fails on this model, as on every model in the project. -/
theorem not_isCounterexample_ξL : ¬ IsCounterexample ξL := by
  rintro ⟨-, hpos, -, -⟩
  have := hpos (-1, -1)
  norm_num [ξL, hstep] at this

/-! ## §2 `S₁L` is a generating set: the annihilator relation survives in the orbit closure -/

/-- Every member of `X_{ξL}` satisfies the unit-square relation
`x w - x (w + (1,0)) - x (w + (0,1)) + x (w + (1,1)) = 0` — the annihilator
`(X^{(1,0)}−1)(X^{(0,1)}−1)`, read off a four-point window. -/
theorem orbitClosure_quad {x : Config ℤ} (hx : x ∈ orbitClosure ξL) (w : ℤ × ℤ) :
    x w - x (w + (1, 0)) - x (w + (0, 1)) + x (w + (1, 1)) = 0 := by
  obtain ⟨u, hu⟩ := hx {w, w + (1, 0), w + (0, 1), w + (1, 1)}
  rw [hu w (by simp), hu (w + (1, 0)) (by simp), hu (w + (0, 1)) (by simp),
    hu (w + (1, 1)) (by simp)]
  simp only [ξL, Prod.fst_add, Prod.snd_add, add_zero]
  ring

/-- **Every point of `𝒯` is generated** — not only the vertices.  Each point is a corner of a
unit square inside `𝒯`, and the quad relation determines a corner from the other three. -/
theorem generatesAt_S₁L (a : ℤ × ℤ) (ha : a ∈ S₁L) : GeneratesAt ξL S₁L a := by
  refine ⟨ha, ?_⟩
  intro x hx y hy hagr
  have hin : ∀ c : ℤ × ℤ, c ∈ S₁L → c ≠ a → x c = y c := fun c hc hne =>
    hagr c (Finset.mem_erase.mpr ⟨hne, hc⟩)
  -- the square with lower-left corner `w = (-1, min a.2 0)`
  have hw : ∀ w : ℤ × ℤ, w.1 = -1 → -1 ≤ w.2 → w.2 ≤ 0 →
      (∀ c ∈ ({w, w + (1, 0), w + (0, 1), w + (1, 1)} : Finset (ℤ × ℤ)), c ≠ a → x c = y c) →
      x w - x (w + (1, 0)) - x (w + (0, 1)) + x (w + (1, 1)) = 0 →
      y w - y (w + (1, 0)) - y (w + (0, 1)) + y (w + (1, 1)) = 0 →
      (a = w ∨ a = w + (1, 0) ∨ a = w + (0, 1) ∨ a = w + (1, 1)) → x a = y a := by
    intro w _ _ _ hc hqx hqy hcase
    rcases hcase with rfl | rfl | rfl | rfl
    · have h1 := hc (a + (1, 0)) (by simp) (by simp [Prod.ext_iff])
      have h2 := hc (a + (0, 1)) (by simp) (by simp [Prod.ext_iff])
      have h3 := hc (a + (1, 1)) (by simp) (by simp [Prod.ext_iff])
      linarith
    · have h1 := hc w (by simp) (by simp [Prod.ext_iff])
      have h2 := hc (w + (0, 1)) (by simp) (by simp [Prod.ext_iff])
      have h3 := hc (w + (1, 1)) (by simp) (by simp [Prod.ext_iff])
      linarith
    · have h1 := hc w (by simp) (by simp [Prod.ext_iff])
      have h2 := hc (w + (1, 0)) (by simp) (by simp [Prod.ext_iff])
      have h3 := hc (w + (1, 1)) (by simp) (by simp [Prod.ext_iff])
      linarith
    · have h1 := hc w (by simp) (by simp [Prod.ext_iff])
      have h2 := hc (w + (1, 0)) (by simp) (by simp [Prod.ext_iff])
      have h3 := hc (w + (0, 1)) (by simp) (by simp [Prod.ext_iff])
      linarith
  obtain ⟨⟨ha1, ha2⟩, ha3, ha4⟩ := mem_S₁L.mp ha
  set w : ℤ × ℤ := (-1, min a.2 0) with hwdef
  have hcorner : ∀ c ∈ ({w, w + (1, 0), w + (0, 1), w + (1, 1)} : Finset (ℤ × ℤ)), c ∈ S₁L := by
    intro c hc
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rw [mem_S₁L]
    rcases hc with rfl | rfl | rfl | rfl <;> simp only [hwdef, Prod.fst_add, Prod.snd_add] <;>
      omega
  refine hw w rfl (by simp only [hwdef]; omega) (by simp only [hwdef]; omega)
    (fun c hc hne => hin c (hcorner c hc) hne)
    (orbitClosure_quad hx w) (orbitClosure_quad hy w) ?_
  simp only [hwdef, Prod.ext_iff, Prod.fst_add, Prod.snd_add]
  omega

/-- **`𝒯` is `ξL`-generating.** -/
theorem isGeneratingSet_S₁L : IsGeneratingSet ξL S₁L :=
  ⟨S₁L_nonempty, latticeConvex_S₁L, fun a ha _ => generatesAt_S₁L a ha⟩

/-! ## §3 The region family and the six fields -/

/-- Cut levels `0, -1, -2, …` (as in `L1Region.wlev`). -/
def levL : ℕ → ℤ := fun n => -(n : ℤ)

theorem levL_antitone : Antitone levL := by
  intro a b hab
  simp only [levL, neg_le_neg_iff, Nat.cast_le]
  exact hab

theorem levL_exhaustive (b : ℤ) : ∃ n, levL n ≤ b := by
  refine ⟨(-b).toNat, ?_⟩
  simp only [levL]
  omega

theorem gapL (n : ℕ) :
    ∃ z ∈ (Set.univ : Set (ℤ × ℤ)), levL (n + 1) ≤ dot uL z ∧ dot uL z < levL n := by
  refine ⟨(-(n : ℤ) - 1, 0), Set.mem_univ _, ?_, ?_⟩ <;>
    · simp only [dot, levL, uL]
      push_cast
      omega

/-- `F.R n = {z | -n ≤ z.1}`. -/
theorem mem_RL (n : ℕ) (z : ℤ × ℤ) : z ∈ cut Set.univ uL levL n ↔ -(n : ℤ) ≤ z.1 := by
  simp only [cut, Set.mem_inter_iff, Set.mem_univ, true_and, halfPlaneGE, dot, levL, uL,
    Set.mem_ofPred_eq]
  omega

/-- On `{0 ≤ z.1}`, `ξL` is `(1,0)`-periodic: `η₁ ≡ 1` there. -/
theorem ξL_add_uL {z : ℤ × ℤ} (hz : 0 ≤ z.1) : ξL (z + (1 : ℤ) • uL) = ξL z := by
  simp only [ξL, hstep, uL, one_smul, Prod.fst_add, Prod.snd_add, add_zero]
  split_ifs <;> omega

theorem baseL : Colle41.PeriodOn (T 0 ξL) (cut Set.univ uL levL 0) ((1 : ℤ) • uL) := by
  intro z hz _
  rw [mem_RL] at hz
  rw [T_zero]
  exact ξL_add_uL (by simpa using hz)

/-- …and not on `ℤ²`: `ξL (-1,0) = 1 ≠ 2 = ξL (0,0)`. -/
theorem notL : ¬ Colle41.PeriodOn (T 0 ξL) (Set.univ : Set (ℤ × ℤ)) ((1 : ℤ) • uL) := by
  intro h
  have := h (-1, 0) (Set.mem_univ _) (Set.mem_univ _)
  norm_num [T, ξL, hstep, uL] at this

/-- **The family**: `𝓡^n = {z | -n ≤ z.1}`, `(1,0)`-periodic at `n = 0` only. -/
def FL : RegionFamily (T 0 ξL) uL u'L 1 :=
  ofCut (Rinf := Set.univ) (m := uL) (lev := levL)
    (isRegion_univ _ _)
    (by simp [dot, uL, u'L])
    (by simp [dot, uL])
    levL_antitone
    levL_exhaustive
    gapL
    baseL
    notL

theorem FL_R (n : ℕ) : FL.R n = cut Set.univ uL levL n := rfl

/-- The only periodic index is `0`. -/
theorem periodOn_FL_iff (N : ℕ) : Colle41.PeriodOn (T 0 ξL) (FL.R N) ((1 : ℤ) • uL) ↔ N = 0 := by
  constructor
  · intro h
    by_contra hN
    have := h (-1, 0) ((mem_RL N _).mpr (by simp only; omega))
      ((mem_RL N _).mpr (by simp only [uL, one_smul, Prod.fst_add]; omega))
    norm_num [T, ξL, hstep, uL] at this
  · rintro rfl
    exact baseL

/-! ### The cut on `𝒯` -/

theorem dot_wcut_true (z : ℤ × ℤ) : dot (wcut true u'L) z = -z.1 := by
  simp [wcut, perp, dot, u'L]

theorem dot_wcut_false (z : ℤ × ℤ) : dot (wcut false u'L) z = z.1 := by
  simp [wcut, perp, dot, u'L]

/-- `derivedQ` is the column `x = 0`. -/
theorem mem_QL {z : ℤ × ℤ} : z ∈ derivedQ true u'L S₁L ↔ z ∈ S₁L ∧ z.1 = 0 := by
  rw [mem_derivedQ_iff]
  simp only [dot_wcut_true]
  constructor
  · rintro ⟨hz, y, hy, hlt⟩
    have := (mem_S₁L.mp hz).1
    have := (mem_S₁L.mp hy).1
    exact ⟨hz, by omega⟩
  · rintro ⟨hz, h0⟩
    exact ⟨hz, (-1, 0), mem_S₁L.mpr (by norm_num), by simp only; omega⟩

/-- The top face is the column `x = -1`. -/
theorem mem_topFaceL {z : ℤ × ℤ} : z ∈ topFace true u'L S₁L ↔ z ∈ S₁L ∧ z.1 = -1 := by
  rw [mem_topFace_iff]
  simp only [dot_wcut_true]
  constructor
  · rintro ⟨hz, hmin⟩
    have := hmin (-1, 0) (mem_S₁L.mpr (by norm_num))
    have := (mem_S₁L.mp hz).1
    exact ⟨hz, by simp only at *; omega⟩
  · rintro ⟨hz, h⟩
    refine ⟨hz, fun y hy => ?_⟩
    have := (mem_S₁L.mp hy).1
    omega

/-- The bottom face is the column `x = 0`. -/
theorem mem_bottomFaceL {z : ℤ × ℤ} : z ∈ bottomFace true u'L S₁L ↔ z ∈ S₁L ∧ z.1 = 0 := by
  rw [← topFace_not true u'L S₁L_nonempty, mem_topFace_iff]
  simp only [Bool.not_true, dot_wcut_false]
  constructor
  · rintro ⟨hz, hmax⟩
    have := hmax (0, 0) (mem_S₁L.mpr (by norm_num))
    have := (mem_S₁L.mp hz).1
    exact ⟨hz, by simp only at *; omega⟩
  · rintro ⟨hz, h⟩
    refine ⟨hz, fun y hy => ?_⟩
    have := (mem_S₁L.mp hy).1
    omega

theorem topFaceL_eq : topFace true u'L S₁L = ({-1} : Finset ℤ) ×ˢ ({-1, 0, 1} : Finset ℤ) := by
  ext z
  rw [mem_topFaceL, mem_S₁L]
  simp only [Finset.mem_product, Finset.mem_singleton, Finset.mem_insert]
  omega

theorem bottomFaceL_eq :
    bottomFace true u'L S₁L = ({0} : Finset ℤ) ×ˢ ({-1, 0, 1} : Finset ℤ) := by
  ext z
  rw [mem_bottomFaceL, mem_S₁L]
  simp only [Finset.mem_product, Finset.mem_singleton, Finset.mem_insert]
  omega

/-- **Non-degeneracy**: the top `u'`-face has three points. -/
theorem card_topFaceL : (topFace true u'L S₁L).card = 3 := by
  rw [topFaceL_eq, Finset.card_product]
  rfl

/-- **Non-degeneracy**: the bottom `u'`-face has three points. -/
theorem card_bottomFaceL : (bottomFace true u'L S₁L).card = 3 := by
  rw [bottomFaceL_eq, Finset.card_product]
  rfl

/-- **Non-degeneracy**: `derivedQ` is nonempty. -/
theorem derivedQ_L_nonempty : (derivedQ true u'L S₁L).Nonempty :=
  ⟨0, mem_QL.mpr ⟨mem_S₁L.mpr (by norm_num), rfl⟩⟩

/-- `pw = 2`, and `maxB` is `{(0,-1), (0,0)}`. -/
theorem mem_maxBL {g : ℤ × ℤ} :
    g ∈ maxB (derivedQ true u'L S₁L) u'L ((topFace true u'L S₁L).card - 1) ↔
      g.1 = 0 ∧ (g.2 = -1 ∨ g.2 = 0) := by
  rw [card_topFaceL, mem_maxB]
  constructor
  · rintro ⟨hg, hrun⟩
    have h1 := hrun 1 (by norm_num)
    rw [mem_QL, mem_S₁L] at hg h1
    simp only [u'L, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
      Nat.cast_one] at h1
    omega
  · rintro ⟨h1, h2⟩
    refine ⟨mem_QL.mpr ⟨mem_S₁L.mpr ⟨by omega, by omega⟩, h1⟩, fun i hi => ?_⟩
    rw [mem_QL, mem_S₁L]
    simp only [u'L, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    omega

/-- **The six fields, at the kernel.** -/
theorem maxBResidual_L : MaxBResidual true uL u'L 1 0 S₁L FL where
  det' := by simp [det, uL, u'L]
  prim := by
    show IsCoprime (0 : ℤ) 1
    exact isCoprime_zero_left.mpr isUnit_one
  c0 := one_ne_zero
  line0 := by
    intro t _ z hz
    obtain ⟨-, h0⟩ := mem_QL.mp hz
    rw [FL_R, mem_RL, mem_RL]
    simp only [u'L, uL, one_smul, Prod.fst_add, Prod.smul_fst, smul_eq_mul, mul_zero]
    omega
  base0 := by
    refine ⟨⟨(0, -1), mem_maxBL.mpr ⟨rfl, Or.inl rfl⟩⟩, (1, 0), fun z hz => ?_⟩
    rw [FL_R, mem_RL]
    have := (mem_S₁L.mp hz).1
    simp only [Prod.fst_add]
    omega
  straddle := by
    intro N _ _
    unfold Nivat.L1Region.Straddle
    intro g hg hgQ t₀ _ _ hline
    exfalso
    have hg1 : g.1 = -1 := by
      have := (mem_S₁L.mp hg).1
      by_contra hne
      exact hgQ (mem_QL.mpr ⟨hg, by omega⟩)
    have := hline t₀ le_rfl
    simp only [T_zero, ξL, hstep, uL, u'L, one_smul, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul, mul_zero, mul_one, add_zero, zero_add, hg1] at this
    split_ifs at this <;> omega

/-! ## §4 The leaf's conclusion, and the `type_of%` guard -/

/-- The conclusion of `exists_L1MaxBResidual` at `ξ`, `S`, verbatim. -/
def L1Conclusion (ξ : Config ℤ) (S : Finset (ℤ × ℤ)) : Prop :=
  ∃ (e u u' v : ℤ × ℤ) (c τ : ℤ) (ε : Bool) (S₁ : Finset (ℤ × ℤ))
    (F : RegionFamily (T e ξ) u u' c),
    S₁ = S.image (· + v) ∧ MaxBResidual (ξ := ξ) ε u u' c τ S₁ F

/-- **The live target is `L1Conclusion`, as a kernel fact with no hypotheses** — same device
as `Case2WindowProbe.target_type_eq`.  If the leaf's signature drifts, this line stops
compiling (only the full `lake build` sees it; `check1.sh` / `shadow_check.sh` do not). -/
theorem l1_target_type_eq :
    type_of% @Nivat.ColleReg.exists_L1MaxBResidual =
      (∀ {ξ xper : Config ℤ} {vl p ℓ : ℤ × ℤ} {S : Finset (ℤ × ℤ)} {gen : ℤ × ℤ},
        IsMinimalCounterexample ξ →
        ∀ (d : DecompDataZ ξ),
        ℓ ∈ Colle45.NonExpansiveLine ξ →
        Colle45.IsOneSidedNonexpansive ξ ℓ →
        Colle45.IsOneSidedNonexpansive ξ (-ℓ) →
        xper ∈ orbitClosure ξ →
        GeneratesAt ξ S gen →
        IsGeneratingSet ξ S →
        p ∈ Per xper → p ≠ 0 → vl ≠ 0 → Primitive vl →
        det p vl = 0 → Nivat.LE2.dot ℓ vl = 0 →
        (∀ (n : ℝ × ℝ) (cmax cmin : ℝ),
          (∀ z ∈ S, inner2 n z ≤ cmax) → (Nivat.R2.face S n cmax).Nonempty →
          (∀ z ∈ S, cmin ≤ inner2 n z) → (Nivat.R2.face S n cmin).Nonempty →
            P ξ S - P ξ (S.filter fun z => inner2 n z < cmax) ≤
              (Nivat.R2.face S n cmax).card - 1 ∧
            P ξ S - P ξ (S.filter fun z => cmin < inner2 n z) ≤
              (Nivat.R2.face S n cmin).card - 1) →
        Case1 ξ xper d.Sphi vl →
        L1Conclusion ξ S) :=
  rfl

/-- **The leaf's conclusion holds on the model**, with `S := S₁L`, `v := 0`. -/
theorem l1Conclusion_L : L1Conclusion ξL S₁L :=
  ⟨0, uL, u'L, 0, 1, 0, true, S₁L, FL, by simp, maxBResidual_L⟩

/-! ## §5 Where the content sits: two negatives on the same model

`straddle` is the field that forces the *placement* of `𝒯`, and the weak `base0` is what
allows that placement.  Both facts are measured on the same `ξL`, `FL`, `S₁L`. -/

/-- **The strong `base0` (retired 2026-09-19) is false on this model.**  Every `b ∈ maxB` has
`b.1 = 0`, so `b + (-1, 0) ∉ F.R 0`. -/
theorem not_strong_base0_L :
    ¬ ∃ b ∈ maxB (derivedQ true u'L S₁L) u'L ((topFace true u'L S₁L).card - 1),
      ∀ z ∈ S₁L, b + z ∈ FL.R 0 := by
  rintro ⟨b, hb, hall⟩
  have h := hall (-1, 0) (mem_S₁L.mpr (by norm_num))
  rw [FL_R, mem_RL] at h
  have := (mem_maxBL.mp hb).1
  simp only [Prod.fst_add] at h
  omega

/-- The same window translated **inside** `F.R 0` (by `(1,0)`): `line0` and `base0` still hold
(they only ask for membership in `F.R 0`), but `straddle` **fails** — the face column `x = 0`
now has a `(1,0)`-periodic `u'`-line, and `F.R 1` is not periodic.  So `straddle` is the field
that pins `𝒯` to straddle the boundary of `F.R N`. -/
def S₁L' : Finset (ℤ × ℤ) := S₁L.image (· + (1, 0))

theorem mem_S₁L' {z : ℤ × ℤ} : z ∈ S₁L' ↔ (0 ≤ z.1 ∧ z.1 ≤ 1) ∧ (-1 ≤ z.2 ∧ z.2 ≤ 1) := by
  simp only [S₁L', Finset.mem_image, mem_S₁L]
  constructor
  · rintro ⟨w, ⟨⟨h1, h2⟩, h3, h4⟩, rfl⟩
    simp only [Prod.fst_add, Prod.snd_add]
    omega
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨(z.1 - 1, z.2), ⟨⟨by omega, by omega⟩, h3, h4⟩, by ext <;> simp⟩

theorem mem_QL' {z : ℤ × ℤ} : z ∈ derivedQ true u'L S₁L' ↔ z ∈ S₁L' ∧ z.1 = 1 := by
  rw [mem_derivedQ_iff]
  simp only [dot_wcut_true]
  constructor
  · rintro ⟨hz, y, hy, hlt⟩
    have := (mem_S₁L'.mp hz).1
    have := (mem_S₁L'.mp hy).1
    exact ⟨hz, by omega⟩
  · rintro ⟨hz, h0⟩
    exact ⟨hz, (0, 0), mem_S₁L'.mpr (by norm_num), by simp only; omega⟩

theorem not_straddle_inside :
    ¬ Straddle (T 0 ξL) (FL.R 0) (FL.R 1) S₁L' (derivedQ true u'L S₁L') uL u'L 1 0 := by
  intro h
  have hg : ((0 : ℤ), (0 : ℤ)) ∈ S₁L' := mem_S₁L'.mpr (by norm_num)
  have hgQ : ((0 : ℤ), (0 : ℤ)) ∉ derivedQ true u'L S₁L' := fun hq => by
    have := (mem_QL'.mp hq).2
    norm_num at this
  refine absurd (h (0, 0) hg hgQ 0 le_rfl baseL ?_) ((periodOn_FL_iff 1).not.mpr one_ne_zero)
  intro t _
  have h0 : (0 : ℤ) ≤ (t • u'L + ((0 : ℤ), (0 : ℤ))).1 := by simp [u'L]
  simp only [T_zero]
  exact ξL_add_uL h0

/-! ## §6 The leaf's binders on `ξL`

Twelve of the fifteen binders, at `ℓ = (1,0)`, `vl = (0,1)`, `xper = hstep z.1 + 1`,
`p = (0,1)`.  Not measured: `hdef` (a complexity bound over all real normals) and `hcase1`
(needs a `DecompDataZ ξL`).  `hξ` is false (`not_isCounterexample_ξL`). -/

/-- `ℓ = (1,0)`, the normal of the vertical lines. -/
def ℓL : ℤ × ℤ := (1, 0)

/-- `x_per`: the limit of `T^{(0,n)} ξL`, `η₁ + 1`. -/
def xperL : Config ℤ := fun z => hstep z.1 + 1

theorem xperL_mem : xperL ∈ orbitClosure ξL := by
  intro W
  refine ⟨(0, ((W.sup fun w => (-w.2).toNat : ℕ) : ℤ)), fun w hw => ?_⟩
  have h1 : (-w.2).toNat ≤ W.sup fun w => (-w.2).toNat :=
    Finset.le_sup (f := fun w : ℤ × ℤ => (-w.2).toNat) hw
  have h2 : -w.2 ≤ ((-w.2).toNat : ℤ) := Int.self_le_toNat _
  have h3 : (((-w.2).toNat : ℕ) : ℤ) ≤ ((W.sup fun w => (-w.2).toNat : ℕ) : ℤ) :=
    Nat.cast_le.mpr h1
  simp only [xperL, ξL, hstep, Prod.fst_add, Prod.snd_add, zero_add]
  split_ifs <;> omega

theorem p_mem_per_xperL : ((0 : ℤ), (1 : ℤ)) ∈ Per xperL := by
  rw [mem_Per_iff]
  funext z
  simp [T, xperL]

/-- The pair `T^{(-1,0)} ξL ≠ T^{(-2,0)} ξL` agrees on `{z.1 ≤ 0}`. -/
theorem shifted_ne : T (-1, 0) ξL ≠ T (-2, 0) ξL := by
  intro h
  have := congrFun h (1, 0)
  norm_num [T, ξL, hstep] at this

theorem shifted_agree {z : ℤ × ℤ} (hz : z.1 ≤ 0) : T (-1, 0) ξL z = T (-2, 0) ξL z := by
  simp only [T, ξL, hstep, Prod.fst_add, Prod.snd_add, add_zero]
  split_ifs <;> omega

/-- The pair `T^{(1,0)} ξL ≠ T^{(2,0)} ξL` agrees on `{0 ≤ z.1}`. -/
theorem shifted_ne' : T (1, 0) ξL ≠ T (2, 0) ξL := by
  intro h
  have := congrFun h (-2, 0)
  norm_num [T, ξL, hstep] at this

theorem shifted_agree' {z : ℤ × ℤ} (hz : 0 ≤ z.1) : T (1, 0) ξL z = T (2, 0) ξL z := by
  simp only [T, ξL, hstep, Prod.fst_add, Prod.snd_add, add_zero]
  split_ifs <;> omega

theorem primitive_ℓL : Primitive ℓL := by
  show IsCoprime (1 : ℤ) 0
  exact isCoprime_one_left

theorem hℓ_pos_L : Colle45.IsOneSidedNonexpansive ξL ℓL :=
  ⟨T (-1, 0) ξL, T (-2, 0) ξL, T_mem_orbitClosure _ _, T_mem_orbitClosure _ _, shifted_ne,
    fun z hz => shifted_agree (by simpa [dot, ℓL] using hz)⟩

theorem hℓ_neg_L : Colle45.IsOneSidedNonexpansive ξL (-ℓL) :=
  ⟨T (1, 0) ξL, T (2, 0) ξL, T_mem_orbitClosure _ _, T_mem_orbitClosure _ _, shifted_ne',
    fun z hz => shifted_agree' (by simpa [dot, ℓL] using hz)⟩

theorem hℓ_nel_L : ℓL ∈ Colle45.NonExpansiveLine ξL :=
  ⟨primitive_ℓL, T (-1, 0) ξL, T (-2, 0) ξL, T_mem_orbitClosure _ _, T_mem_orbitClosure _ _,
    shifted_ne, fun z hz => shifted_agree (by simpa [halfPlaneLE, dot, ℓL] using hz)⟩

/-- **Twelve binders of `exists_L1MaxBResidual` on the model**, bundled in the leaf's order
(`hℓ_nel hℓ_pos hℓ_neg hxper hgen hSgen hp_mem hp_ne hvl_ne hvl_prim hdet_vl hdet_ℓ`), with
`vl := u'L = (0,1)` and `p := (0,1)`. -/
theorem binders_L :
    ℓL ∈ Colle45.NonExpansiveLine ξL ∧
    Colle45.IsOneSidedNonexpansive ξL ℓL ∧
    Colle45.IsOneSidedNonexpansive ξL (-ℓL) ∧
    xperL ∈ orbitClosure ξL ∧
    GeneratesAt ξL S₁L 0 ∧
    IsGeneratingSet ξL S₁L ∧
    ((0 : ℤ), (1 : ℤ)) ∈ Per xperL ∧
    ((0 : ℤ), (1 : ℤ)) ≠ 0 ∧
    u'L ≠ 0 ∧ Primitive u'L ∧
    det ((0 : ℤ), (1 : ℤ)) u'L = 0 ∧
    Nivat.LE2.dot ℓL u'L = 0 :=
  ⟨hℓ_nel_L, hℓ_pos_L, hℓ_neg_L, xperL_mem,
    generatesAt_S₁L 0 (mem_S₁L.mpr (by norm_num)), isGeneratingSet_S₁L, p_mem_per_xperL, by simp [Prod.ext_iff], by simp [u'L, Prod.ext_iff],
    maxBResidual_L.prim, by simp [det, u'L], by simp [dot, ℓL, u'L]⟩

end Nivat.L1Probe

section Receipts

#print axioms Nivat.L1Probe.per_ξL_eq_zero
#print axioms Nivat.L1Probe.not_isPeriodic_ξL
#print axioms Nivat.L1Probe.not_isCounterexample_ξL
#print axioms Nivat.L1Probe.orbitClosure_quad
#print axioms Nivat.L1Probe.generatesAt_S₁L
#print axioms Nivat.L1Probe.isGeneratingSet_S₁L
#print axioms Nivat.L1Probe.FL
#print axioms Nivat.L1Probe.periodOn_FL_iff
#print axioms Nivat.L1Probe.mem_QL
#print axioms Nivat.L1Probe.mem_topFaceL
#print axioms Nivat.L1Probe.mem_bottomFaceL
#print axioms Nivat.L1Probe.card_topFaceL
#print axioms Nivat.L1Probe.card_bottomFaceL
#print axioms Nivat.L1Probe.derivedQ_L_nonempty
#print axioms Nivat.L1Probe.mem_maxBL
#print axioms Nivat.L1Probe.maxBResidual_L
#print axioms Nivat.L1Probe.l1_target_type_eq
#print axioms Nivat.L1Probe.l1Conclusion_L
#print axioms Nivat.L1Probe.not_strong_base0_L
#print axioms Nivat.L1Probe.not_straddle_inside
#print axioms Nivat.L1Probe.xperL_mem
#print axioms Nivat.L1Probe.hℓ_pos_L
#print axioms Nivat.L1Probe.hℓ_neg_L
#print axioms Nivat.L1Probe.hℓ_nel_L
#print axioms Nivat.L1Probe.binders_L

end Receipts
