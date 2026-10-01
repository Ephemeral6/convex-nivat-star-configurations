/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.ChainAssemble
import Nivat.External.Colle.ConvTransport
import Nivat.External.Colle.Generating

/-!
# `EnvSuperset` — every finite set is contained in an `E(𝒮_φ)`-enveloped set

原文：b3_colle2.txt:470-476 (Lemma 3.5's proof, clauses (i) and (ii)).

Collé's clause (i) (`:470-472`) asserts that `B_i` is an `E(𝒮_φ)`-enveloped set
(Definition 3.2 at `:402`), and clause (ii) (`:474-476`) asserts

> `B_i` contains both `A_{i-1}` and `[-i+1, i-1]² ∩ ℋ(ℓ^{(-)})`.

Our `ChainRecursion` only ever produced the first half of (ii) (`B (i+1) := A i`).  This file
supplies the existence statement that makes the *conjunction* of (i) and (ii) satisfiable:

> for any finite `F ⊆ ℤ²` there is a **finite** `E(𝒮_φ)`-enveloped `B ⊇ F`.

**No new `Prop` and no new `structure` is introduced here** (hard rule 7 has nothing to bind
to): everything is stated with `Nivat.LE2.EnvOf`, transcribed from Definition 3.2 in
`LatticeEdges.lean:624-629`, and the only new `def` is the affine map `aff` of §1.

## The construction

`𝒮_φ` has positive area (`AhatMono.posArea_Sphi`, the on-chain producer of the single
hypothesis below), so it contains a positively oriented triple `a, b, c`.  Put `u := b - a`,
`v := c - a`, `D := det u v ≥ 1`.  For `k > 0` and `w : ℤ²` set `aff k w z := k z + w`.  Then

* `face (aff k w '' T) n = aff k w '' face T n` (§1, `face_aff`) — dilating by a **positive**
  factor and translating is an order isomorphism for every `dot n ·`;
* hence `E (aff k w '' T) = E T` and every face keeps its cardinality.

Take `S' := aff k w '' 𝒮_φ` and let `B` be its lattice-convex completion
(`Nivat.Colle.exists_latticeConvex_completion`, `Generating.lean:90`).  Completion preserves
the convex hull, so `E ↑B = E ↑S' = E ↑𝒮_φ` by `E_congr_of_Conv_eq` (`ConvTransport.lean:233`),
and `face ↑S' n ⊆ face ↑B n` (§2, `face_subset_of_hull_eq`), which is the inequality
Definition 3.2 asks for.  Choosing `k` large and `w` a suitable back-shift puts every point of
`F` inside the triangle `aff k w a, aff k w b, aff k w c` (§3–§4), hence inside `Conv S'`,
hence inside `B` by lattice convexity.

⚠ **Scope.**  This produces *an* enveloped superset, nothing more.  It does **not** say that
the `B_i` so produced can be threaded into `ChainRecursion` (the `AhatMono` / `subAB`
obligations are untouched), and it does not touch the `Aenvfix` counterexample, which is about
the old `B (i+1) := A i` encoding.  What it removes is the reason that encoding was forced:
the second half of clause (ii) is now constructible.
-/

set_option autoImplicit false

namespace Nivat.EnvSuperset

open Nivat Nivat.LE2

/-! ### §1  The affine map `z ↦ k z + w`

原文：b3_colle2.txt:402 — Definition 3.2 compares *edges* of `𝒯` with edges of `𝒰`, and the
comparison is by parallelism and lattice length.  A positive dilation followed by a
translation fixes every edge normal and can only lengthen an edge, which is why it is the
right enlargement to use here. -/

/-- The affine map `z ↦ k z + w` on `ℤ²`, written out in coordinates. -/
def aff (k : ℤ) (w : ℤ × ℤ) (z : ℤ × ℤ) : ℤ × ℤ := (k * z.1 + w.1, k * z.2 + w.2)

theorem dot_aff (n : ℤ × ℤ) (k : ℤ) (w z : ℤ × ℤ) :
    dot n (aff k w z) = k * dot n z + dot n w := by
  simp only [dot, aff]
  ring

theorem aff_injective {k : ℤ} (hk : k ≠ 0) (w : ℤ × ℤ) : Function.Injective (aff k w) := by
  intro p q h
  rw [aff, aff, Prod.ext_iff] at h
  obtain ⟨h1, h2⟩ := h
  simp only at h1 h2
  exact Prod.ext (mul_left_cancel₀ hk (by omega)) (mul_left_cancel₀ hk (by omega))

/-- **Faces transport along a positive dilation-translation.** -/
theorem face_aff {k : ℤ} (hk : 0 < k) (w : ℤ × ℤ) (T : Set (ℤ × ℤ)) (n : ℤ × ℤ) :
    face (aff k w '' T) n = aff k w '' face T n := by
  ext y
  constructor
  · rintro ⟨⟨z, hzT, rfl⟩, hmax⟩
    refine ⟨z, ⟨hzT, fun t ht => ?_⟩, rfl⟩
    have h := hmax (aff k w t) ⟨t, ht, rfl⟩
    rw [dot_aff, dot_aff] at h
    exact le_of_mul_le_mul_left (by linarith) hk
  · rintro ⟨z, ⟨hzT, hzmax⟩, rfl⟩
    refine ⟨⟨z, hzT, rfl⟩, ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    rw [dot_aff, dot_aff]
    have h : k * dot n t ≤ k * dot n z :=
      mul_le_mul_of_nonneg_left (hzmax t ht) (le_of_lt hk)
    linarith

theorem nontrivial_image_iff {f : ℤ × ℤ → ℤ × ℤ} (hf : Function.Injective f)
    (s : Set (ℤ × ℤ)) : (f '' s).Nontrivial ↔ s.Nontrivial := by
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, hne⟩
    exact ⟨x, hx, y, hy, fun h => hne (congrArg f h)⟩
  · rintro ⟨x, hx, y, hy, hne⟩
    exact ⟨f x, ⟨x, hx, rfl⟩, f y, ⟨y, hy, rfl⟩, fun h => hne (hf h)⟩

/-- **The edge set is invariant under a positive dilation-translation.** -/
theorem E_aff {k : ℤ} (hk : 0 < k) (w : ℤ × ℤ) (T : Set (ℤ × ℤ)) :
    E (aff k w '' T) = E T := by
  ext n
  simp only [mem_E_iff, face_aff hk,
    nontrivial_image_iff (aff_injective (ne_of_gt hk) w)]

/-- **Every face keeps its cardinality under a positive dilation-translation.** -/
theorem encard_face_aff {k : ℤ} (hk : 0 < k) (w : ℤ × ℤ) (T : Set (ℤ × ℤ)) (n : ℤ × ℤ) :
    (face (aff k w '' T) n).encard = (face T n).encard := by
  rw [face_aff hk]
  exact Set.InjOn.encard_image
    (fun _ _ _ _ h => aff_injective (ne_of_gt hk) w h)

/-! ### §2  The lattice-convex completion keeps every face

`Nivat.Colle.exists_latticeConvex_completion` (`Generating.lean:90`) returns `S ⊆ B` with
`Conv B = Conv S`.  Faces do **not** transport along equality of hulls in general
(`Nivat.LE2.exists_Conv_eq_face_ne`, `ConvTransport.lean:322`), but the *inclusion* we need
does, because the support value is determined by the hull. -/

/-- **Completion only enlarges faces.** -/
theorem face_subset_of_hull_eq {S B : Finset (ℤ × ℤ)} (hsub : S ⊆ B)
    (hhull : Conv B = Conv S) (n : ℤ × ℤ) :
    face (↑S : Set (ℤ × ℤ)) n ⊆ face (↑B : Set (ℤ × ℤ)) n := by
  rintro z ⟨hzS, hzmax⟩
  refine ⟨Finset.mem_coe.mpr (hsub (Finset.mem_coe.mp hzS)), fun y hy => ?_⟩
  have hyC : toReal y ∈ Conv S := by
    rw [← hhull]
    exact subset_Conv (Finset.mem_coe.mp hy)
  have h1 : rdot (toReal n) (toReal y) ≤ ((dot n z : ℤ) : ℝ) :=
    Conv_subset_halfSpace (fun t ht => hzmax t (Finset.mem_coe.mpr ht)) (toReal y) hyC
  rw [rdot_toReal] at h1
  exact_mod_cast h1

/-! ### §3  Barycentric membership in a lattice triangle

Everything here is phrased with **integer** hypotheses, so the caller never touches ℝ. -/

/-- **A lattice point with non-negative integral barycentric coordinates lies in the hull.**

`N` plays the role of the common denominator; `X`, `Y` of the two numerators. -/
theorem mem_Conv_triangle {S : Finset (ℤ × ℤ)} {P₀ P₁ P₂ z : ℤ × ℤ}
    (h0 : P₀ ∈ S) (h1 : P₁ ∈ S) (h2 : P₂ ∈ S)
    {X Y N : ℤ} (hN : 0 < N) (hX : 0 ≤ X) (hY : 0 ≤ Y) (hXY : X + Y ≤ N)
    (e1 : N * z.1 = (N - X - Y) * P₀.1 + X * P₁.1 + Y * P₂.1)
    (e2 : N * z.2 = (N - X - Y) * P₀.2 + X * P₁.2 + Y * P₂.2) :
    toReal z ∈ Conv S := by
  have hC : Convex ℝ (Conv S) := convex_convexHull ℝ _
  have hm0 : toReal P₀ ∈ Conv S := subset_Conv h0
  have hm1 : toReal P₁ ∈ Conv S := subset_Conv h1
  have hm2 : toReal P₂ ∈ Conv S := subset_Conv h2
  rcases eq_or_lt_of_le (by omega : (0 : ℤ) ≤ X + Y) with hXY0 | hXY0
  · -- degenerate: `z = P₀`
    have hX0 : X = 0 := by omega
    have hY0 : Y = 0 := by omega
    subst hX0; subst hY0
    have c1 : z.1 = P₀.1 := by
      have : N * z.1 = N * P₀.1 := by linarith [e1]
      exact mul_left_cancel₀ (by omega) this
    have c2 : z.2 = P₀.2 := by
      have : N * z.2 = N * P₀.2 := by linarith [e2]
      exact mul_left_cancel₀ (by omega) this
    have : z = P₀ := Prod.ext c1 c2
    rw [this]
    exact hm0
  · have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hXr : (0 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
    have hYr : (0 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY
    have hSr : (0 : ℝ) < (X : ℝ) + (Y : ℝ) := by exact_mod_cast hXY0
    have hXYr : (X : ℝ) + (Y : ℝ) ≤ (N : ℝ) := by exact_mod_cast hXY
    set s : ℝ := ((X : ℝ) + (Y : ℝ)) / (N : ℝ) with hs
    have hs0 : 0 < s := div_pos hSr hNr
    have hs1 : s ≤ 1 := by
      rw [hs, div_le_one hNr]; exact hXYr
    -- the inner combination of `P₁` and `P₂`
    have hq : ((X : ℝ) / ((X : ℝ) + (Y : ℝ))) • toReal P₁
        + ((Y : ℝ) / ((X : ℝ) + (Y : ℝ))) • toReal P₂ ∈ Conv S := by
      refine hC hm1 hm2 (div_nonneg hXr (le_of_lt hSr)) (div_nonneg hYr (le_of_lt hSr)) ?_
      field_simp
    have hmain := hC hm0 hq (by linarith : (0 : ℝ) ≤ 1 - s) (le_of_lt hs0)
      (by ring)
    -- identify the result with `toReal z`
    have hz : toReal z = (1 - s) • toReal P₀
        + s • (((X : ℝ) / ((X : ℝ) + (Y : ℝ))) • toReal P₁
            + ((Y : ℝ) / ((X : ℝ) + (Y : ℝ))) • toReal P₂) := by
      have e1r : (N : ℝ) * (z.1 : ℝ)
          = ((N : ℝ) - (X : ℝ) - (Y : ℝ)) * (P₀.1 : ℝ)
            + (X : ℝ) * (P₁.1 : ℝ) + (Y : ℝ) * (P₂.1 : ℝ) := by exact_mod_cast e1
      have e2r : (N : ℝ) * (z.2 : ℝ)
          = ((N : ℝ) - (X : ℝ) - (Y : ℝ)) * (P₀.2 : ℝ)
            + (X : ℝ) * (P₁.2 : ℝ) + (Y : ℝ) * (P₂.2 : ℝ) := by exact_mod_cast e2
      refine Prod.ext ?_ ?_ <;>
        simp only [toReal, hs, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
          smul_eq_mul]
      · field_simp
        linarith [e1r]
      · field_simp
        linarith [e2r]
    rw [hz]
    exact hmain

/-! ### §4  Cramer's rule in `ℤ²` -/

/-- **Cramer's rule.**  `det u v • p = (det p v) • u + (det u p) • v`, coordinatewise. -/
theorem cramer_fst (u v p : ℤ × ℤ) :
    det u v * p.1 = det p v * u.1 + det u p * v.1 := by
  simp only [det]; ring

theorem cramer_snd (u v p : ℤ × ℤ) :
    det u v * p.2 = det p v * u.2 + det u p * v.2 := by
  simp only [det]; ring

/-! ### §5  The main theorem -/

/-- **A positively oriented triple inside a set of positive area.** -/
theorem exists_pos_det {T : Set (ℤ × ℤ)} (h : PosArea T) :
    ∃ a ∈ T, ∃ b ∈ T, ∃ c ∈ T, 0 < det (b - a) (c - a) := by
  obtain ⟨a, ha, b, hb, c, hc, hdet⟩ := h
  rcases lt_or_gt_of_ne hdet with hlt | hgt
  · refine ⟨a, ha, c, hc, b, hb, ?_⟩
    have : det (c - a) (b - a) = - det (b - a) (c - a) := by simp only [det]; ring
    omega
  · exact ⟨a, ha, b, hb, c, hc, hgt⟩

/-- **Every finite set of lattice points is contained in a finite `E(𝒮_φ)`-enveloped set.**

原文：b3_colle2.txt:470-476 — clause (i) is `EnvOf ↑Sphi ↑B`, clause (ii) is `F ⊆ B` with
`F := A_{i-1} ∪ ([-i+1,i-1]² ∩ ℋ(ℓ^{(-)}))`.  Definition 3.2 is at `:402`.

Per-quantifier correspondence (hard rule 7):

| binder | source |
|---|---|
| `Sphi : Finset (ℤ × ℤ)` | `𝒮_φ`, `:470` "an `E(𝒮_φ)`-enveloped set" |
| `harea : PosArea ↑Sphi` | `:402` "`conv(𝒰)` has positive area" — Definition 3.2's standing hypothesis on the enveloping set.  On-chain producer: `Nivat.AhatMono.posArea_Sphi` |
| `F : Finset (ℤ × ℤ)` | the union in `:474`; finiteness is Collé's, both `A_{i-1}` and the box are finite |
| `∃ B` | `B_i`, `:474` |

There is **no** quantifier here without a counterpart in `:470-476`; in particular nothing is
asserted about `A_i`, about `k_i`, or about the relation between consecutive `B_i`. -/
theorem exists_enveloped_superset (Sphi : Finset (ℤ × ℤ))
    (harea : PosArea (↑Sphi : Set (ℤ × ℤ))) (F : Finset (ℤ × ℤ)) :
    ∃ B : Finset (ℤ × ℤ), (↑F : Set (ℤ × ℤ)) ⊆ (↑B : Set (ℤ × ℤ)) ∧
      EnvOf (↑Sphi : Set (ℤ × ℤ)) (↑B : Set (ℤ × ℤ)) := by
  classical
  obtain ⟨a, ha, b, hb, c, hc, hD⟩ := exists_pos_det harea
  set u : ℤ × ℤ := b - a with hu
  set v : ℤ × ℤ := c - a with hv
  set D : ℤ := det u v with hDdef
  -- the size bound
  set Mn : ℕ := F.sup (fun z => max (det z v).natAbs (det u z).natAbs) with hMn
  set M : ℤ := (Mn : ℤ) with hM
  have hM0 : 0 ≤ M := by positivity
  have hMbound : ∀ z ∈ F, |det z v| ≤ M ∧ |det u z| ≤ M := by
    intro z hz
    have hle : max (det z v).natAbs (det u z).natAbs ≤ Mn :=
      Finset.le_sup (f := fun z => max (det z v).natAbs (det u z).natAbs) hz
    constructor
    · have h : (det z v).natAbs ≤ Mn := le_trans (le_max_left _ _) hle
      rw [hM, Int.abs_eq_natAbs]
      exact_mod_cast h
    · have h : (det u z).natAbs ≤ Mn := le_trans (le_max_right _ _) hle
      rw [hM, Int.abs_eq_natAbs]
      exact_mod_cast h
  set k : ℤ := 4 * M + 1 with hk
  have hk0 : 0 < k := by omega
  set w : ℤ × ℤ :=
    (-(k * a.1) - M * u.1 - M * v.1, -(k * a.2) - M * u.2 - M * v.2) with hw
  set S' : Finset (ℤ × ℤ) := Sphi.image (aff k w) with hS'
  have hS'coe : (↑S' : Set (ℤ × ℤ)) = aff k w '' (↑Sphi : Set (ℤ × ℤ)) := by
    rw [hS', Finset.coe_image]
  obtain ⟨B, hsub, hconvB, hhull⟩ := Nivat.Colle.exists_latticeConvex_completion S'
  refine ⟨B, ?_, ?_⟩
  · -- `F ⊆ B`
    intro z hz
    have hzF : z ∈ F := Finset.mem_coe.mp hz
    obtain ⟨hz1, hz2⟩ := hMbound z hzF
    obtain ⟨hz1l, hz1r⟩ := abs_le.mp hz1
    obtain ⟨hz2l, hz2r⟩ := abs_le.mp hz2
    -- coordinates of the basis vectors
    have hu1 : u.1 = b.1 - a.1 := by rw [hu]; rfl
    have hu2 : u.2 = b.2 - a.2 := by rw [hu]; rfl
    have hv1 : v.1 = c.1 - a.1 := by rw [hv]; rfl
    have hv2 : v.2 = c.2 - a.2 := by rw [hv]; rfl
    -- the shifted point
    set p : ℤ × ℤ := (z.1 + M * (u.1 + v.1), z.2 + M * (u.2 + v.2)) with hp
    set X : ℤ := det p v with hX
    set Y : ℤ := det u p with hY
    have hXeq : X = det z v + M * D := by
      simp only [hX, hp, hDdef, det]; ring
    have hYeq : Y = det u z + M * D := by
      simp only [hY, hp, hDdef, det]; ring
    have hD1 : 1 ≤ D := hD
    have hMD : M ≤ M * D := le_mul_of_one_le_right hM0 hD1
    have hXnn : 0 ≤ X := by omega
    have hYnn : 0 ≤ Y := by omega
    have hXYle : X + Y ≤ D * k := by
      have hkk : D * k = 4 * (M * D) + D := by rw [hk]; ring
      omega
    -- the three triangle vertices
    have hP0 : aff k w a ∈ S' := Finset.mem_image_of_mem _ (Finset.mem_coe.mp ha)
    have hP1 : aff k w b ∈ S' := Finset.mem_image_of_mem _ (Finset.mem_coe.mp hb)
    have hP2 : aff k w c ∈ S' := Finset.mem_image_of_mem _ (Finset.mem_coe.mp hc)
    -- Cramer, in the two coordinates
    have hp1 : p.1 = z.1 + M * (u.1 + v.1) := by rw [hp]
    have hp2 : p.2 = z.2 + M * (u.2 + v.2) := by rw [hp]
    have hcr1 : D * (z.1 + M * (u.1 + v.1)) = X * u.1 + Y * v.1 := by
      rw [← hp1, hDdef, hX, hY]; exact cramer_fst u v p
    have hcr2 : D * (z.2 + M * (u.2 + v.2)) = X * u.2 + Y * v.2 := by
      rw [← hp2, hDdef, hX, hY]; exact cramer_snd u v p
    -- the vertex coordinates
    have hA1 : (aff k w a).1 = -(M * u.1) - M * v.1 := by
      simp only [aff, hw]; ring
    have hA2 : (aff k w a).2 = -(M * u.2) - M * v.2 := by
      simp only [aff, hw]; ring
    have hB1 : (aff k w b).1 = k * u.1 - M * u.1 - M * v.1 := by
      simp only [aff, hw, hu1]; ring
    have hB2 : (aff k w b).2 = k * u.2 - M * u.2 - M * v.2 := by
      simp only [aff, hw, hu2]; ring
    have hC1 : (aff k w c).1 = k * v.1 - M * u.1 - M * v.1 := by
      simp only [aff, hw, hv1]; ring
    have hC2 : (aff k w c).2 = k * v.2 - M * u.2 - M * v.2 := by
      simp only [aff, hw, hv2]; ring
    have e1 : D * k * z.1
        = (D * k - X - Y) * (aff k w a).1 + X * (aff k w b).1 + Y * (aff k w c).1 := by
      rw [hA1, hB1, hC1]
      linear_combination k * hcr1
    have e2 : D * k * z.2
        = (D * k - X - Y) * (aff k w a).2 + X * (aff k w b).2 + Y * (aff k w c).2 := by
      rw [hA2, hB2, hC2]
      linear_combination k * hcr2
    have hmem : toReal z ∈ Conv S' :=
      mem_Conv_triangle hP0 hP1 hP2 (mul_pos hD hk0) hXnn hYnn hXYle e1 e2
    have : toReal z ∈ Conv B := by rw [hhull]; exact hmem
    exact Finset.mem_coe.mpr (hconvB z this)
  · -- `EnvOf ↑Sphi ↑B`
    have hEB : E (↑B : Set (ℤ × ℤ)) = E (↑Sphi : Set (ℤ × ℤ)) := by
      rw [E_congr_of_Conv_eq hhull, hS'coe, E_aff hk0]
    refine envOf_of_E_eq (Nivat.ChainAsm.isLatticeConvexRegion_coe hconvB) hEB ?_
    intro n _
    have h1 : (face (↑Sphi : Set (ℤ × ℤ)) n).encard = (face (↑S' : Set (ℤ × ℤ)) n).encard := by
      rw [hS'coe, encard_face_aff hk0]
    rw [h1]
    exact Set.encard_mono (face_subset_of_hull_eq hsub hhull n)

/-- **Set-level form**, the shape `ChainRecursion` consumes. -/
theorem exists_enveloped_superset_of_finite (Sphi : Finset (ℤ × ℤ))
    (harea : PosArea (↑Sphi : Set (ℤ × ℤ))) {F : Set (ℤ × ℤ)} (hF : F.Finite) :
    ∃ B : Set (ℤ × ℤ), F ⊆ B ∧ B.Finite ∧ EnvOf (↑Sphi : Set (ℤ × ℤ)) B := by
  classical
  obtain ⟨B, hsub, hEnv⟩ := exists_enveloped_superset Sphi harea hF.toFinset
  refine ⟨(↑B : Set (ℤ × ℤ)), ?_, B.finite_toSet, hEnv⟩
  intro z hz
  exact hsub (by simpa using hz)

/-- **Clause (ii) in its two-part form**: a single enveloped `B` containing both the previous
`A` and a prescribed box.

原文：b3_colle2.txt:474-476 — "`B_i` contains both `A_{i-1}` and `[-i+1,i-1]² ∩ ℋ(ℓ^{(-)})`". -/
theorem exists_enveloped_superset_pair (Sphi : Finset (ℤ × ℤ))
    (harea : PosArea (↑Sphi : Set (ℤ × ℤ)))
    {A Box : Set (ℤ × ℤ)} (hA : A.Finite) (hBox : Box.Finite) :
    ∃ B : Set (ℤ × ℤ), A ⊆ B ∧ Box ⊆ B ∧ B.Finite ∧ EnvOf (↑Sphi : Set (ℤ × ℤ)) B := by
  obtain ⟨B, hsub, hfin, hEnv⟩ :=
    exists_enveloped_superset_of_finite Sphi harea (hA.union hBox)
  exact ⟨B, fun z hz => hsub (Or.inl hz), fun z hz => hsub (Or.inr hz), hfin, hEnv⟩

/-! ### §6  Non-vacuity

The single hypothesis of §5 is `PosArea ↑Sphi`.  Its on-chain producer is
`Nivat.AhatMono.posArea_Sphi` (`AhatMono.lean:3175`), which takes `d : DecompData η` and no
side conditions; this file deliberately does not import `AhatMono`, so that it stays upstream
of everything and can be imported anywhere.  The receipts below show the hypothesis is
satisfiable by a concrete finite set, so none of §5 is vacuously true. -/

/-- The unit triangle, a concrete set of positive area. -/
def tri : Finset (ℤ × ℤ) := {((0 : ℤ), (0 : ℤ)), ((1 : ℤ), (0 : ℤ)), ((0 : ℤ), (1 : ℤ))}

theorem posArea_tri : PosArea (↑tri : Set (ℤ × ℤ)) := by
  refine ⟨((0 : ℤ), (0 : ℤ)), ?_, ((1 : ℤ), (0 : ℤ)), ?_, ((0 : ℤ), (1 : ℤ)), ?_, ?_⟩
  · simp [tri]
  · simp [tri]
  · simp [tri]
  · simp [det]

/-- **Non-vacuity receipt.**  Every finite `F` sits inside a set enveloped by the unit
triangle's edge fan.  This is `exists_enveloped_superset` with all binders discharged. -/
theorem exists_enveloped_superset_tri (F : Finset (ℤ × ℤ)) :
    ∃ B : Finset (ℤ × ℤ), (↑F : Set (ℤ × ℤ)) ⊆ (↑B : Set (ℤ × ℤ)) ∧
      EnvOf (↑tri : Set (ℤ × ℤ)) (↑B : Set (ℤ × ℤ)) :=
  exists_enveloped_superset tri posArea_tri F

/-- The same receipt in the set-level form clause (ii) consumes. -/
theorem exists_enveloped_superset_pair_tri {A Box : Set (ℤ × ℤ)}
    (hA : A.Finite) (hBox : Box.Finite) :
    ∃ B : Set (ℤ × ℤ), A ⊆ B ∧ Box ⊆ B ∧ B.Finite ∧ EnvOf (↑tri : Set (ℤ × ℤ)) B :=
  exists_enveloped_superset_pair tri posArea_tri hA hBox

end Nivat.EnvSuperset

#print axioms Nivat.EnvSuperset.dot_aff
#print axioms Nivat.EnvSuperset.aff_injective
#print axioms Nivat.EnvSuperset.face_aff
#print axioms Nivat.EnvSuperset.nontrivial_image_iff
#print axioms Nivat.EnvSuperset.E_aff
#print axioms Nivat.EnvSuperset.encard_face_aff
#print axioms Nivat.EnvSuperset.face_subset_of_hull_eq
#print axioms Nivat.EnvSuperset.mem_Conv_triangle
#print axioms Nivat.EnvSuperset.cramer_fst
#print axioms Nivat.EnvSuperset.cramer_snd
#print axioms Nivat.EnvSuperset.exists_pos_det
#print axioms Nivat.EnvSuperset.exists_enveloped_superset
#print axioms Nivat.EnvSuperset.exists_enveloped_superset_of_finite
#print axioms Nivat.EnvSuperset.exists_enveloped_superset_pair
#print axioms Nivat.EnvSuperset.posArea_tri
#print axioms Nivat.EnvSuperset.exists_enveloped_superset_tri
#print axioms Nivat.EnvSuperset.exists_enveloped_superset_pair_tri
