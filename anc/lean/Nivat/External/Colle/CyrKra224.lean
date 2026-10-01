/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.LatticeEdges
import Nivat.External.Colle.Generating
import Nivat.External.Colle.Prop210
import Nivat.MorseHedlund

/-!
# Cyr-Kra Lemma 2.24 and Corollary 2.25 — ambiguity implies periodicity

Formalization of the key machinery from Van Cyr and Bryna Kra,
*Nonexpansive ℤ²-subdynamics and Nivat's conjecture*, arXiv:1208.4090v2,
§2.4 "Ambiguous half planes and periodicity".

This file provides the missing piece for `Nivat.External.Colle.Prop210`:
the relationship between ambiguity (non-unique extension over an edge)
and periodicity on strips/borders.

## Status (as of 2026-09-16)

**Cyr-Kra Lemma 2.24 bypass complete, and this file is now sorry-free.** The working
version `border_period_of_ambiguousAlong` is proved with no axioms beyond the standard
kernel axioms `[propext, Classical.choice, Quot.sound]`.

The placeholder transcription of Lemma 2.24 (`periodic_border_of_ambiguous`) that stood
in §5 was **withdrawn on 2026-09-16**: it is false as it was stated (refuted in §5b), it
had no consumers, and the working form already exists.  See §5 for the full record.  The
actual consumption path goes through `Prop210.cyrKra_downward_induction`, which is proved
and has axiom closure `[propext, Classical.choice, Quot.sound]`.

**NOTE (2026-09-13):** The theorems in this file require SFT (subshift of finite type)
infrastructure that is not yet formalized. The key results (`exists_row_period_of_ambiguousAlong`
and `exists_strip_period_of_ambiguousAlong`) are **already fully proved** in `Prop210.lean`
using different machinery (Colle's `AmbiguousAlong` notion + pattern counting + Morse-Hedlund).

This file is kept for reference and for the definitions (`Border`, `Interior`, `SFT_patterns`,
etc.) that may be needed later, but the main theorems now delegate to Prop210.

## Source reference

arXiv:1208.4090v2, §2.4, specifically:
- Definition 2.19: extensions `Ext_w(𝒯)` and `j`-subextensions
- Definition 2.23: `(𝒮,w)`-border and `m`-interior
- Lemma 2.24: ambiguous half-plane ⇒ periodic border
- Corollary 2.25: ambiguous extension ⇒ periodic interior of some subextension

## Main definitions

* `Nivat.CK224.Transl` — `V_{𝒮,𝒯,w}`, the translations admitted by Definition 2.23
* `Nivat.CK224.Border` — the `(𝒮,w)`-border of a half-plane `H`
* `Nivat.CK224.Interior` — the `g`-interior of that border

## Main results

* `Nivat.CK224.height_lemma` — Lemma 2.11, repaired (see §4/§4b: the previous statement
  was false, and `height_lemma_old_false` refutes it)
* `Nivat.CK224.periodic_border_of_ambiguous_false` — §5b, the machine-checked refutation
  of the transcription of Lemma 2.24 that stood in §5 until 2026-09-16.  The statement it
  refutes has been withdrawn; this refutation is kept as the record of why
* `Nivat.CK224.periodic_interior_of_ambiguous_extension` — Corollary 2.25, **repaired and
  proved** (§7, 2026-09-14).  The previous statement was false — it is refuted by
  `periodic_interior_of_ambiguous_extension_false` (§7b), which is kept — because its
  conclusion existentially quantified an unconstrained set `B`.  The repaired statement
  ties the periodic region back to Definition 2.23's `g`-interior of the
  `(𝒮 ∖ w, w)`-border of the given extension, as in the source.  §7c exhibits a
  concrete instance in which every hypothesis holds and that interior is nonempty, so
  the repair is not vacuous.
* `Nivat.CK224.border_period_of_ambiguousAlong` — the working form of Lemma 2.24 behind
  §7, proved from `Nivat.Colle.exists_row_period_of_ambiguousAlong`

This file carries no `sorry`.  The usable content of Lemma 2.24 is proved, under Colle's
`AmbiguousAlong` notion, as `Nivat.Colle.exists_row_period_of_ambiguousAlong` and
`exists_strip_period_of_ambiguousAlong`, and is packaged here as
`border_period_of_ambiguousAlong`.
-/

namespace Nivat.CK224

open Nivat Nivat.Colle Nivat.LE2

/-! ## §1. Preliminaries: half-planes and rational directions -/

/-- A half-plane in ℤ² with boundary normal `n`.
Convention: `halfPlaneGE n c = {z : ℤ × ℤ | c ≤ dot n z}`. -/
def halfPlaneGE (n : ℤ × ℤ) (c : ℤ) : Set (ℤ × ℤ) :=
  {z : ℤ × ℤ | c ≤ dot n z}

/-- A vector is parallel to a primitive vector if it's a scalar multiple. -/
def IsParallel (v w : ℤ × ℤ) : Prop :=
  ∃ k : ℤ, v = (k * w.1, k * w.2)

/-- Decidable instance for IsParallel - we make this noncomputable for simplicity. -/
noncomputable instance instDecidableIsParallel (v w : ℤ × ℤ) :
    Decidable (IsParallel v w) :=
  Classical.propDecidable _

/-- The vertical primitive direction (0,1). -/
def vertical : ℤ × ℤ := (0, 1)

theorem vertical_prim : Prim vertical := by simp [Prim, vertical]

/-! ## §2. The (𝒮,w)-border of a half-plane

**Cyr-Kra Definition 2.23 (arXiv:1208.4090v2), verbatim:**

> If `𝒯` is a convex set, `𝒮 ⊂ 𝒯` is convex, and `w ∈ E(𝒮)` is parallel to an edge
> `w* ∈ E(𝒯)`, let `V_{𝒮,𝒯,w}` be the (possibly empty) set of translations that take
> `𝒮` to a subset of `𝒯` such that the translated edge of `𝒮` is contained in the
> edge of `𝒯` parallel to `w`:
>
>   `V_{𝒮,𝒯,w} = {v ∈ ℤ² : (𝒮 + v) ⊆ 𝒯, (w + v) ⊆ w*}`.
>
> When `V_{𝒮,𝒯,w} ≠ ∅`, there exist vectors `a_{𝒮,𝒯,w}, b_{𝒮,𝒯,w} ∈ ℤ²` such that
> `V_{𝒮,𝒯,w} = {a + λb : λ ∈ I}`, where `I = {0,…,|V|-1}` if `‖w*‖ < ∞`;
> `ℕ ∪ {0}` if `w*` is a semi-infinite line; `ℤ` if `w*` is a line.
> Let `I_min, I_max` be the minimum and maximum elements of `I` … Then the
> `(𝒮,w)`-border of `𝒯` is the set `⋃_{v ∈ V_{𝒮,𝒯,w}} (𝒮 + v)`.
>
> For integers `0 ≤ g < ½(I_max - I_min)`, the `g`-interior of the `(𝒮,w)`-border
> is the set `⋃_{λ=I_min+g}^{I_max-g-1} (𝒮 + a_{𝒮,𝒯,w} + λ b_{𝒮,𝒯,w})`.

Encoding conventions in this development (see `Nivat.External.Colle.LatticeEdges`):
edges are indexed by their **primitive outer normal**, so the paper's edge `w ∈ E(𝒮)`
is here the normal `w : ℤ × ℤ` together with the point set `face ↑𝒮 w`, and the
paper's `w* ∈ E(𝒯)` — which by the footnote to Definition 2.23 is *uniquely*
determined by `w`, because the boundaries carry orientations — is `face 𝒯 w`.
Hence `(w + v) ⊆ w*` becomes `∀ s ∈ face ↑𝒮 w, s + v ∈ face 𝒯 w`.

**2026-09-13 (defect fix).**  The previous version of `Border` below never mentioned
its `w` argument, so it collected *every* translate landing inside `𝒯`, dropping the
`(w + v) ⊆ w*` guard entirely; `Interior B m _w` was worse still — its guard
`∃ v, ∀ k, |k| ≤ m → z + k • v ∈ B` is satisfied by `v = 0` for every `z ∈ B`, so it
was provably equal to `B` for all `B`, `m`, `w`.  Both are restored to Definition 2.23
here, and §6 exhibits a concrete non-degenerate member of the corrected `Border`
together with a translate that the restored guard rejects. -/

/-- `V_{S,H,w}` of Cyr-Kra Definition 2.23: the translations `v` that take `S` into `H`
with the `w`-edge of `S` landing inside the `w`-edge of `H`.

The two conjuncts are, verbatim, `(S + v) ⊆ H` and `(w + v) ⊆ w*`. -/
def Transl (S : Finset (ℤ × ℤ)) (w : ℤ × ℤ) (H : Set (ℤ × ℤ)) : Set (ℤ × ℤ) :=
  {v : ℤ × ℤ | (∀ s ∈ S, s + v ∈ H) ∧ ∀ s ∈ face (↑S : Set (ℤ × ℤ)) w, s + v ∈ face H w}

/-- The `(S,w)`-border of `H`: `⋃_{v ∈ V_{S,H,w}} (S + v)`.

Unlike the previous version, the `w`-edge condition is present: a translate contributes
only when its `w`-edge lies on the `w`-edge of `H`. -/
def Border (S : Finset (ℤ × ℤ)) (w : ℤ × ℤ) (H : Set (ℤ × ℤ)) : Set (ℤ × ℤ) :=
  {z : ℤ × ℤ | ∃ v ∈ Transl S w H, ∃ s ∈ S, z = s + v}

/-- The `g`-interior of the `(S,w)`-border of `H`.

Definition 2.23 writes `V_{S,H,w} = {a + λ b : λ ∈ I}` and takes the union over
`λ ∈ [I_min + g, I_max - g - 1]`.  The step vector `b` runs along the edge `w*`, hence
is perpendicular to the normal `w`; for primitive `w` it is `± dir w`
(`dot_dir : dot n (dir n) = 0`).  Membership `λ ∈ [I_min+g, I_max-g-1]` is then
equivalent to `v + i • dir w ∈ V_{S,H,w}` for every `-g ≤ i ≤ g + 1`, which is how the
condition is written below.  The upper bound is `g + 1`, not `g`, because the paper's
index range is half-open at the top (`I_max - g - 1`).

Taking the direction from `w` rather than as a free parameter is deliberate: an
existentially quantified direction would be satisfiable by `0` and collapse the
definition back to `Border`.

Two honest caveats about this encoding.  (a) It is a *local* reformulation: the paper's
index condition `λ ∈ [I_min+g, I_max-g-1]` is a statement about the global arithmetic
progression `V = {a + λb}`, whereas the condition below only inspects the `2g+2`
translations neighbouring `v`.  The two agree exactly when `V` really is an arithmetic
progression with step `± dir w`, which is what Definition 2.23 asserts; in that regime
`v = a + λb` has all of `v + i·b`, `-g ≤ i ≤ g+1`, in `V` precisely when
`I_min + g ≤ λ ≤ I_max - g - 1`.  This development does not prove that structural claim
about `V`, so for pathological `H` the two may differ.  (b) The paper's `b` is determined
only up to sign, and requiring the condition for `i` of both signs makes the definition
insensitive to that choice, apart from the deliberate top-end off-by-one. -/
def Interior (S : Finset (ℤ × ℤ)) (w : ℤ × ℤ) (H : Set (ℤ × ℤ)) (g : ℕ) : Set (ℤ × ℤ) :=
  {z : ℤ × ℤ | ∃ v ∈ Transl S w H,
    (∀ i : ℤ, -(g : ℤ) ≤ i → i ≤ (g : ℤ) + 1 → v + i • dir w ∈ Transl S w H) ∧
    ∃ s ∈ S, z = s + v}

/-- The diameter in direction w: number of distinct lines parallel to w
intersecting the set. -/
def diam_w (S : Finset (ℤ × ℤ)) (w : ℤ × ℤ) : ℕ :=
  if hw : w = (0, 0) then 0
  else if w.1 = 0 then (S.image Prod.fst).card
  else if w.2 = 0 then (S.image Prod.snd).card
  else
    -- For general direction, count equivalence classes under w-shifts
    (S.image (fun z => (w.2 * z.1 - w.1 * z.2))).card

/-! ## §3. Ambiguity and the SFT X_𝒮(η)

An (𝒮,η)-coloring is a configuration whose 𝒮-patterns all occur in η.
This forms a subshift of finite type X_𝒮(η). -/

/-- The subshift of finite type generated by the 𝒮-patterns of η.
A configuration f is in X_𝒮(η) if every S-pattern of f appears somewhere in η. -/
def SFT_patterns {A : Type*} (η : Config A) (S : Finset (ℤ × ℤ)) : Set (Config A) :=
  {f : Config A | ∀ v : ℤ × ℤ, ∃ u : ℤ × ℤ,
    ∀ s ∈ S, f (s + v) = (T u η) (s + v)}

/-- The orbit closure is contained in the SFT.
TODO(source): This follows from the definition of orbit closure and SFT_patterns.
Every configuration in the orbit closure has all its patterns appearing in η. -/
theorem orbitClosure_subset_SFT {A : Type*} {η : Config A} {S : Finset (ℤ × ℤ)} :
    orbitClosure η ⊆ SFT_patterns η S := by
  -- Every f in orbitClosure η satisfies: for any window W, there exists u with f|_W = η|_{u+W}
  -- In particular, for any translate v, there exists u with f|_{S+v} = η|_{u+S+v}
  -- So every S-pattern of f appears in η at some position
  intro f hf
  intro v
  -- Need: ∃ u, ∀ s ∈ S, f (s + v) = (T u η) (s + v)
  -- From orbit closure: ∃ u₀, ∀ w ∈ S.image (· + v), f w = η (u₀ + w)
  obtain ⟨u₀, hu₀⟩ := hf (S.image fun s => s + v)
  use u₀
  intro s hs
  have hmem : s + v ∈ S.image (fun s => s + v) := Finset.mem_image.mpr ⟨s, hs, rfl⟩
  rw [hu₀ (s + v) hmem]
  simp only [T]
  rw [add_comm]

/-- A coloring is (𝒮,H,η)-ambiguous if it does not extend uniquely from H
to the next layer. -/
def IsAmbiguous {A : Type*} (η : Config A) (S : Finset (ℤ × ℤ))
    (f : Config A) (H : Set (ℤ × ℤ)) : Prop :=
  f ∈ SFT_patterns η S ∧
  ∃ g₁ g₂ : Config A, g₁ ∈ SFT_patterns η S ∧ g₂ ∈ SFT_patterns η S ∧
    (∀ z ∈ H, g₁ z = f z ∧ g₂ z = f z) ∧
    ∃ z₀ : ℤ × ℤ, z₀ ∉ H ∧ g₁ z₀ ≠ g₂ z₀

/-! ## §3b. ℓ-balanced sets (Cyr-Kra Definition 4.5)

An ℓ-balanced set is one where:
(i) Every line parallel to ℓ through S has ≥ h points (h = |ℓ(S) ∩ S| - 1)
(ii) The endpoints of ℓ(S) are η-generated
(iii) D_η(S \ ℓ(S)) > D_η(S) -/

/-- A set is ℓ-balanced if lines parallel to ℓ intersect it in many points
and removing the ℓ-edge increases discrepancy. -/
def IsBalanced {A : Type*} (η : Config A) (S : Finset (ℤ × ℤ))
    (ℓ : ℤ × ℤ) : Prop :=
  ∃ (h : ℕ), h + 1 ≤ S.card ∧
  (∀ x : ℤ, (S.filter (fun z => IsParallel (z - (x, 0)) ℓ)).Nonempty →
    h ≤ (S.filter (fun z => IsParallel (z - (x, 0)) ℓ)).card) ∧
  (∃ w ∈ S, GeneratesAt η S w)

/-! ## §4. The height lemma (Cyr-Kra Lemma 2.11)

Every vertical line through 𝒮 contains at least h points, where
h = |w₁ ∩ 𝒮| - 1 and w₁ is the vertical edge. -/

-- Helper: lattice points on a vertical segment are in a lattice-convex set
lemma latticeConvex_vertical_segment {S : Finset (ℤ × ℤ)} (hS : LatticeConvex S)
    {x y1 y2 : ℤ} (h1 : (x, y1) ∈ S) (h2 : (x, y2) ∈ S) (hy : y1 ≤ y2) :
    ∀ y : ℤ, y1 ≤ y ∧ y ≤ y2 → (x, y) ∈ S := by
  intro y ⟨hy1, hy2⟩
  by_cases heq1 : y = y1
  · rwa [heq1]
  by_cases heq2 : y = y2
  · rwa [heq2]
  -- The point (x, y) is strictly between (x, y1) and (x, y2)
  have hy_strict : y1 < y ∧ y < y2 := by omega
  -- Express (x, y) as a convex combination
  have hy_pos : 0 < y2 - y1 := by omega
  have hlt : (y1 : ℝ) < (y2 : ℝ) := by exact_mod_cast (by omega : y1 < y2)
  have hden : ((y2 : ℝ) - (y1 : ℝ)) ≠ 0 := sub_ne_zero.mpr hlt.ne'
  have hc1 : toReal (x, y1) ∈ Conv S := subset_Conv h1
  have hc2 : toReal (x, y2) ∈ Conv S := subset_Conv h2
  have h_in_conv : toReal (x, y) ∈ Conv S := by
    -- toReal (x, y) is the convex combination with weight (y - y1) / (y2 - y1)
    rw [Conv] at hc1 hc2 ⊢
    apply Convex.segment_subset (convex_convexHull ℝ _) hc1 hc2
    -- Show that toReal (x, y) ∈ segment ℝ (toReal (x, y1)) (toReal (x, y2))
    rw [segment_eq_image]
    refine ⟨((y : ℝ) - (y1 : ℝ)) / ((y2 : ℝ) - (y1 : ℝ)), ⟨?_, ?_⟩, ?_⟩
    · exact div_nonneg (sub_nonneg.mpr (by exact_mod_cast hy1)) (sub_nonneg.mpr hlt.le)
    · rw [div_le_one (sub_pos.mpr hlt)]
      have : (y : ℝ) ≤ (y2 : ℝ) := by exact_mod_cast hy2
      linarith
    · simp only [toReal, Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk, Prod.mk.injEq]
      refine ⟨by ring, ?_⟩
      field_simp
      ring
  exact hS (x, y) h_in_conv

/-- `Conv S` is convex. -/
lemma conv_convex (S : Finset (ℤ × ℤ)) : Convex ℝ (Conv S) := by
  rw [Conv]
  exact convex_convexHull ℝ _

/-- A column of a lattice-convex `S` carrying at least `h+1` points contains a vertical
pair at distance exactly `h`: the column is an unbroken lattice segment (by
`latticeConvex_vertical_segment`) of length at least `h`. -/
lemma col_span {S : Finset (ℤ × ℤ)} (hS : LatticeConvex S) {h : ℕ} {c : ℤ}
    (hcard : h + 1 ≤ (S.filter (fun z => z.1 = c)).card) :
    ∃ a : ℤ, (c, a) ∈ S ∧ (c, a + (h : ℤ)) ∈ S := by
  classical
  have hne : (S.filter (fun z => z.1 = c)).Nonempty := Finset.card_pos.mp (by omega)
  have himg : ((S.filter (fun z => z.1 = c)).image Prod.snd).Nonempty := by
    rwa [Finset.image_nonempty]
  set col := S.filter (fun z => z.1 = c) with hcoldef
  set ym := (col.image Prod.snd).min' himg with hym
  set yM := (col.image Prod.snd).max' himg with hyM
  have hym_mem : ym ∈ col.image Prod.snd := Finset.min'_mem _ himg
  have hyM_mem : yM ∈ col.image Prod.snd := Finset.max'_mem _ himg
  have mem_of : ∀ y ∈ col.image Prod.snd, (c, y) ∈ S := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
    have hz1 : z.1 = c := (Finset.mem_filter.mp hz).2
    have : (z.1, z.2) ∈ S := by simpa using (Finset.mem_filter.mp hz).1
    rwa [hz1] at this
  have hSmin : (c, ym) ∈ S := mem_of _ hym_mem
  have hSmax : (c, yM) ∈ S := mem_of _ hyM_mem
  have hle : ym ≤ yM := Finset.min'_le _ _ hyM_mem
  -- `col` injects into `Finset.Icc ym yM` via the second coordinate
  have hinj : Set.InjOn Prod.snd (col : Set (ℤ × ℤ)) := by
    intro a ha b hb hab
    have ha1 : a.1 = c := (Finset.mem_filter.mp (Finset.mem_coe.mp ha)).2
    have hb1 : b.1 = c := (Finset.mem_filter.mp (Finset.mem_coe.mp hb)).2
    exact Prod.ext (by rw [ha1, hb1]) hab
  have hsub : col.image Prod.snd ⊆ Finset.Icc ym yM := by
    intro y hy
    exact Finset.mem_Icc.mpr ⟨Finset.min'_le _ _ hy, Finset.le_max' _ _ hy⟩
  have hcard2 : col.card ≤ (Finset.Icc ym yM).card := by
    rw [← Finset.card_image_of_injOn hinj]
    exact Finset.card_le_card hsub
  rw [Int.card_Icc] at hcard2
  have hspan : (h : ℤ) ≤ yM - ym := by omega
  exact ⟨ym, hSmin,
    latticeConvex_vertical_segment hS hSmin hSmax hle _ ⟨by omega, by omega⟩⟩

/-- The geometric core of Lemma 2.11.  If two columns `c₁ < c₂` of a lattice-convex `S`
each carry a vertical lattice segment of height `h`, then every column strictly between
them carries at least `h` lattice points of `S`.

Proof: the two segments' endpoints span, at abscissa `x`, a real vertical segment
`[p, p+h]` inside `Conv S`; it contains the `h` integers `⌈p⌉, …, ⌈p⌉+h-1`, which lattice
convexity returns to `S`. -/
lemma fill_column {S : Finset (ℤ × ℤ)} (hS : LatticeConvex S) {h : ℕ} (hh : 0 < h)
    {c₁ c₂ x a₁ a₂ : ℤ}
    (hx1 : c₁ < x) (hx2 : x < c₂)
    (hA : (c₁, a₁) ∈ S) (hB : (c₁, a₁ + (h : ℤ)) ∈ S)
    (hC : (c₂, a₂) ∈ S) (hD : (c₂, a₂ + (h : ℤ)) ∈ S) :
    h ≤ (S.filter (fun z => z.1 = x)).card := by
  classical
  have hc12 : (c₁ : ℝ) < (c₂ : ℝ) := by exact_mod_cast (by omega : c₁ < c₂)
  have hxc1 : (c₁ : ℝ) < (x : ℝ) := by exact_mod_cast hx1
  have hxc2 : (x : ℝ) < (c₂ : ℝ) := by exact_mod_cast hx2
  have hd : (0 : ℝ) < (c₂ : ℝ) - (c₁ : ℝ) := by linarith
  have hdne : ((c₂ : ℝ) - (c₁ : ℝ)) ≠ 0 := ne_of_gt hd
  set t : ℝ := ((x : ℝ) - (c₁ : ℝ)) / ((c₂ : ℝ) - (c₁ : ℝ)) with ht
  have ht0 : (0 : ℝ) ≤ t := div_nonneg (by linarith) hd.le
  have ht1 : t ≤ 1 := by rw [ht, div_le_one hd]; linarith
  have hxc : (1 - t) * (c₁ : ℝ) + t * (c₂ : ℝ) = (x : ℝ) := by
    rw [ht]; field_simp; ring
  have hconv := conv_convex S
  have key : ∀ (u v : ℤ), (c₁, u) ∈ S → (c₂, v) ∈ S →
      (((x : ℝ)), (1 - t) * (u : ℝ) + t * (v : ℝ)) ∈ Conv S := by
    intro u v hu hv
    have hmem := hconv (subset_Conv hu) (subset_Conv hv)
      (by linarith : (0 : ℝ) ≤ 1 - t) ht0 (by ring)
    have heq : (1 - t) • toReal (c₁, u) + t • toReal (c₂, v)
        = (((x : ℝ)), (1 - t) * (u : ℝ) + t * (v : ℝ)) := by
      simp only [toReal, Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk, Prod.mk.injEq,
        and_true]
      exact hxc
    rwa [heq] at hmem
  set p : ℝ := (1 - t) * (a₁ : ℝ) + t * (a₂ : ℝ) with hp
  have hP : (((x : ℝ)), p) ∈ Conv S := key a₁ a₂ hA hC
  have hQ : (((x : ℝ)), p + (h : ℝ)) ∈ Conv S := by
    have hkey := key (a₁ + (h : ℤ)) (a₂ + (h : ℤ)) hB hD
    have heq : (1 - t) * ((a₁ + (h : ℤ) : ℤ) : ℝ) + t * ((a₂ + (h : ℤ) : ℤ) : ℝ)
        = p + (h : ℝ) := by rw [hp]; push_cast; ring
    rwa [heq] at hkey
  have hh' : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  -- every integer of the real interval `[p, p+h]` at abscissa `x` lies in `S`
  have vfill : ∀ y : ℤ, p ≤ (y : ℝ) → (y : ℝ) ≤ p + (h : ℝ) → (x, y) ∈ S := by
    intro y hy1 hy2
    apply hS
    set s : ℝ := ((y : ℝ) - p) / (h : ℝ) with hs
    have hs0 : (0 : ℝ) ≤ s := div_nonneg (by linarith) hh'.le
    have hs1 : s ≤ 1 := by rw [hs, div_le_one hh']; linarith
    have hmem := hconv hP hQ (by linarith : (0 : ℝ) ≤ 1 - s) hs0 (by ring)
    have heq : (1 - s) • (((x : ℝ)), p) + s • (((x : ℝ)), p + (h : ℝ)) = toReal (x, y) := by
      simp only [toReal, Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk, Prod.mk.injEq]
      refine ⟨by ring, ?_⟩
      rw [hs]
      field_simp
      ring
    rwa [heq] at hmem
  -- count the integers `⌈p⌉, …, ⌈p⌉ + h - 1`, all of which lie in `[p, p+h]`
  set n : ℤ := ⌈p⌉ with hn
  have hnp : p ≤ (n : ℝ) := Int.le_ceil p
  have hnp2 : (n : ℝ) < p + 1 := Int.ceil_lt_add_one p
  have hmaps : ∀ y ∈ Finset.Icc n (n + (h : ℤ) - 1),
      (x, y) ∈ S.filter (fun z => z.1 = x) := by
    intro y hy
    rw [Finset.mem_Icc] at hy
    refine Finset.mem_filter.mpr ⟨vfill y ?_ ?_, rfl⟩
    · have : (n : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy.1
      linarith
    · have hy2 : (y : ℝ) ≤ (n : ℝ) + (h : ℝ) - 1 := by
        have h' := hy.2
        have h'' : ((y : ℤ) : ℝ) ≤ ((n + (h : ℤ) - 1 : ℤ) : ℝ) := by exact_mod_cast h'
        push_cast at h''
        linarith
      linarith
  have hcount : (Finset.Icc n (n + (h : ℤ) - 1)).card
      ≤ (S.filter (fun z => z.1 = x)).card := by
    refine Finset.card_le_card_of_injOn (fun y : ℤ => (x, y)) ?_ ?_
    · intro y hy
      exact Finset.mem_coe.mpr (hmaps y (Finset.mem_coe.mp hy))
    · intro a _ b _ hab
      simpa using congrArg Prod.snd hab
  rw [Int.card_Icc] at hcount
  omega

/-- **Cyr-Kra Lemma 2.11 (the height lemma), repaired statement.**

`S` is lattice-convex, `c₁` and `c₂` bound its columns (so the columns at `c₁` and `c₂`
are the two *antiparallel vertical edges* `w₁`, `w₂` of Definition-2.23 language), the
`c₁`-column has `h+1` points and the `c₂`-column has at least as many (`|w₁| ≤ |w₂|`).
Then every column meeting `S` has at least `h` points.

**2026-09-13 (statement repair; signature change, see `height_lemma_old_false`).**
The statement previously read

```
theorem height_lemma {S : Finset (ℤ × ℤ)} {h : ℕ}
    (hS : LatticeConvex S)
    (hvert : ∃ c : ℤ, (S.filter (fun z => z.1 = c)).Nonempty ∧
      (S.filter (fun z => z.1 = c)).card = h + 1) :
    ∀ x : ℤ, (S.filter (fun z => z.1 = x)).Nonempty →
      h ≤ (S.filter (fun z => z.1 = x)).card
```

and is **false**: `height_lemma_old_false` below refutes it with
`S = {(0,0),(0,1),(0,2),(1,0)}`, `h = 2`, `c = 0`, `x = 1` — a lattice-convex set whose
left column has three points and whose right column has one.  (This is the *second*
refutation this statement has attracted; the first, in
`audit-2026-09-13/status-1648/HeightCounterexample.lean`, killed an even earlier version
whose `hvert` was vacuously satisfiable by a `c` outside `S`, and the `Nonempty`
conjunct was added in response.  That patch was not enough.)

The two hypotheses restored here, `hspan` and `hle`, are exactly the ones Cyr-Kra carry
as standing assumptions of the section: `w₁, w₂ ∈ E(S)` are *antiparallel edges* — which
in the vertical encoding says every point of `S` lies in the closed column range
`[c₁, c₂]` whose ends are those two edges — and `|w₁| ≤ |w₂|`, which fixes `h` as coming
from the *shorter* edge.  Neither implies the conclusion: `height_lemma_witness` exhibits
a model of all the hypotheses with `h = 1`, and dropping either one re-enables the
counterexample (`S0` satisfies `hspan` with `c₁ = 0, c₂ = 1` but violates `hle`). -/
theorem height_lemma {S : Finset (ℤ × ℤ)} {h : ℕ}
    (hS : LatticeConvex S) {c₁ c₂ : ℤ}
    (hspan : ∀ z ∈ S, c₁ ≤ z.1 ∧ z.1 ≤ c₂)
    (hne₁ : (S.filter (fun z => z.1 = c₁)).Nonempty)
    (hcard₁ : (S.filter (fun z => z.1 = c₁)).card = h + 1)
    (hle : (S.filter (fun z => z.1 = c₁)).card ≤ (S.filter (fun z => z.1 = c₂)).card) :
    ∀ x : ℤ, (S.filter (fun z => z.1 = x)).Nonempty →
      h ≤ (S.filter (fun z => z.1 = x)).card := by
  classical
  intro x hx
  rcases Nat.eq_zero_or_pos h with rfl | hh
  · exact Nat.zero_le _
  have h₁ : h + 1 ≤ (S.filter (fun z => z.1 = c₁)).card := by omega
  have h₂ : h + 1 ≤ (S.filter (fun z => z.1 = c₂)).card := by omega
  by_cases hxe1 : x = c₁
  · subst hxe1; omega
  by_cases hxe2 : x = c₂
  · subst hxe2; omega
  obtain ⟨z, hz⟩ := hx
  have hzS : z ∈ S := (Finset.mem_filter.mp hz).1
  have hz1 : z.1 = x := (Finset.mem_filter.mp hz).2
  obtain ⟨hb1, hb2⟩ := hspan z hzS
  rw [hz1] at hb1 hb2
  obtain ⟨a₁, hA, hB⟩ := col_span hS h₁
  obtain ⟨a₂, hC, hD⟩ := col_span hS h₂
  exact fill_column hS hh (by omega) (by omega) hA hB hC hD

/-! ### §4b. The refutation of the previous `height_lemma`, and a satisfiability witness

Both are kernel-checked with no `sorry`. -/

/-- The counterexample window `{(0,0),(0,1),(0,2),(1,0)}`: lattice-convex, left column of
three points, right column of one. -/
def S0 : Finset (ℤ × ℤ) := {(0, 0), (0, 1), (0, 2), (1, 0)}

/-- The closed triangle `{0 ≤ x, 0 ≤ y, 2x + y ≤ 2}`, which contains `Conv S0` and whose
lattice points are exactly `S0`. -/
def Tri : Set (ℝ × ℝ) := {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ 2 * p.1 + p.2 ≤ 2}

theorem Tri_convex : Convex ℝ Tri := by
  intro p hp q hq a b ha hb hab
  obtain ⟨hp1, hp2, hp3⟩ := hp
  obtain ⟨hq1, hq2, hq3⟩ := hq
  refine ⟨?_, ?_, ?_⟩
  · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
    nlinarith
  · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
    nlinarith
  · simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    nlinarith

theorem S0_latticeConvex : LatticeConvex S0 := by
  have hsub : toReal '' (S0 : Set (ℤ × ℤ)) ⊆ Tri := by
    rintro _ ⟨z, hz, rfl⟩
    simp only [S0, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl <;> simp [Tri, toReal]
  have hConv : Conv S0 ⊆ Tri := convexHull_min hsub Tri_convex
  intro z hz
  obtain ⟨h1, h2, h3⟩ := hConv hz
  simp only [toReal] at h1 h2 h3
  have h1' : (0 : ℤ) ≤ z.1 := by exact_mod_cast h1
  have h2' : (0 : ℤ) ≤ z.2 := by exact_mod_cast h2
  have h3' : 2 * z.1 + z.2 ≤ 2 := by exact_mod_cast h3
  obtain ⟨a, b⟩ := z
  simp only at h1' h2' h3'
  simp only [S0, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
  omega

/-- **The pre-2026-09-13 `height_lemma` statement is false.**  Stated as the honest
universal closure of that statement: the implicit `{S}` and `{h}` become `∀`, and the
hypotheses and conclusion are copied verbatim. -/
theorem height_lemma_old_false :
    ¬ (∀ (S : Finset (ℤ × ℤ)) (h : ℕ), LatticeConvex S →
        (∃ c : ℤ, (S.filter (fun z => z.1 = c)).Nonempty ∧
          (S.filter (fun z => z.1 = c)).card = h + 1) →
        ∀ x : ℤ, (S.filter (fun z => z.1 = x)).Nonempty →
          h ≤ (S.filter (fun z => z.1 = x)).card) := by
  intro H
  have := H S0 2 S0_latticeConvex ⟨0, by decide, by decide⟩ 1 (by decide)
  revert this
  decide

/-- **Non-degeneracy of the repaired `height_lemma`.**  The unit square satisfies every
hypothesis with `h = 1` (and `c₁ = 0`, `c₂ = 1`), so the repaired statement is not
vacuous.  `hle` holds because both columns have two points. -/
theorem height_lemma_witness :
    LatticeConvex ({(0,0), (0,1), (1,0), (1,1)} : Finset (ℤ × ℤ)) ∧
    (∀ z ∈ ({(0,0), (0,1), (1,0), (1,1)} : Finset (ℤ × ℤ)),
      (0 : ℤ) ≤ z.1 ∧ z.1 ≤ 1) ∧
    ((({(0,0), (0,1), (1,0), (1,1)} : Finset (ℤ × ℤ))).filter
      (fun z => z.1 = (0 : ℤ))).card = 1 + 1 ∧
    ((({(0,0), (0,1), (1,0), (1,1)} : Finset (ℤ × ℤ))).filter
      (fun z => z.1 = (0 : ℤ))).card ≤
      ((({(0,0), (0,1), (1,0), (1,1)} : Finset (ℤ × ℤ))).filter
      (fun z => z.1 = (1 : ℤ))).card := by
  refine ⟨?_, by decide, by decide, by decide⟩
  have hsub : toReal '' ((({(0,0), (0,1), (1,0), (1,1)} : Finset (ℤ × ℤ))) : Set (ℤ × ℤ))
      ⊆ {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1} := by
    rintro _ ⟨z, hz, rfl⟩
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl <;> norm_num [toReal]
  have hcvx : Convex ℝ {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1} := by
    intro p hp q hq a b ha hb hab
    obtain ⟨hp1, hp2, hp3, hp4⟩ := hp
    obtain ⟨hq1, hq2, hq3, hq4⟩ := hq
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;>
      nlinarith
  intro z hz
  obtain ⟨h1, h2, h3, h4⟩ := convexHull_min hsub hcvx hz
  simp only [toReal] at h1 h2 h3 h4
  have h1' : (0 : ℤ) ≤ z.1 := by exact_mod_cast h1
  have h2' : z.1 ≤ 1 := by exact_mod_cast h2
  have h3' : (0 : ℤ) ≤ z.2 := by exact_mod_cast h3
  have h4' : z.2 ≤ 1 := by exact_mod_cast h4
  obtain ⟨a, b⟩ := z
  simp only at h1' h2' h3' h4'
  simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
  omega

/-! ## §5. Lemma 2.24 — ambiguous half-plane implies periodic border (statement withdrawn)

**Cyr-Kra Lemma 2.24 (arXiv:1208.4090v2).**
Suppose η : ℤ² → 𝒜, 𝒮 ⊂ ℤ² is an η-generating set and there exist
antiparallel w₁, w₂ ∈ E(𝒮). Suppose |w₁| ≤ |w₂|, H is a w₁-half plane,
and f ∈ X_𝒮(η) with f|_H being (𝒮,η)-ambiguous. Then the (𝒮∖w₁,w₁)-border
of H is periodic with period vector parallel to w₁, with period ≤ |w₁ ∩ 𝒮| - 1.

**Withdrawn 2026-09-16.**  A `theorem ... := by sorry` transcribing that sentence stood
here from 2026-09-13.  It was removed, not proved and not weakened, for three reasons,
each measured rather than asserted:

* It is **false as it was stated**.  `periodic_border_of_ambiguous_false` (§5b) refutes
  its honest universal closure; measured 2026-09-16, that refutation depends only on
  `[propext, Classical.choice, Quot.sound]`.
* It had **no consumers**.  The one reason recorded for keeping it — that
  `periodic_interior_of_ambiguous_extension` (§7) still cited it — expired when §7 was
  restated and closed on 2026-09-14: that theorem now discharges its border step through
  `border_period_of_ambiguousAlong` (§6), and is itself sorry-free.
* The **working form of Lemma 2.24 already exists** and is proved:
  `border_period_of_ambiguousAlong`, which periodises along the *edge* direction `dir w`
  rather than along the normal `w`, over `Border (edgeErase S w) w`, under Colle's
  `AmbiguousAlong`.  That is the form Cyr-Kra's own proof establishes and the form §7
  consumes; see §6.

The two places the withdrawn transcription departed from the source, and which together
let the §5b witness through, are recorded in §5b: it periodised along the *normal* `w`
where Cyr-Kra periodise *parallel* to `w₁`, and it used point-deletion `S.erase w` where
Cyr-Kra delete the whole `w`-face (their Lemma 2.8 counting bound needs `𝒮∖w₁ ≠ ∅`,
which fails vacuously for the domino witness). -/

/-! ## §5b. The *former* `periodic_border_of_ambiguous` is false as stated

Counterexample data.  `A = Bool`; `pbEta` is the checkerboard; `pbS = {(0,0),(1,0)}`
is a horizontal domino; `pbW = (0,1)`; `pbH` is the lower half plane `{z | z.2 ≤ 0}`.

Two remarks on why this is not a cheap shot.

*The half-plane side condition is respected.*  Cyr-Kra require `H` to be a `w₁`-half
plane, and `pbW = (0,1)` really is the outer normal of `pbH`, so the counterexample
does not exploit a missing "`H` is a `w`-half plane" hypothesis.

*What is actually missing.*  Two things.  (a) Cyr-Kra's generating sets (Definition 2.9)
carry a discrepancy condition — every nonempty proper convex subset has strictly larger
discrepancy — which `Nivat.Colle.IsGeneratingSet` does not include; without it the SFT
`X_S(η)` here contains the whole family `pbF g`, `g : ℤ → Bool` arbitrary, so no
Morse-Hedlund counting bound is available and nothing forces periodicity along `pbW`.
(b) The paper's `𝒮 ∖ w₁` removes an *edge* of `𝒮`, whereas `S.erase w` removes a
*point*; here `pbW ∉ pbS`, so `S.erase w = S` and the intended thinning never happens. -/

/-- The checkerboard configuration on `Bool`. -/
def pbEta : Config Bool := fun z => decide ((z.1 + z.2) % 2 = 0)

/-- The horizontal domino `{(0,0),(1,0)}`. -/
def pbS : Finset (ℤ × ℤ) := {(0, 0), (1, 0)}

/-- The direction: primitive, and the outer normal of `pbH`. -/
def pbW : ℤ × ℤ := (0, 1)

/-- The lower half plane. -/
def pbH : Set (ℤ × ℤ) := {z : ℤ × ℤ | z.2 ≤ 0}

/-- The family of configurations that alternate horizontally with an arbitrary
row-profile `g`.  Every one of them lies in `SFT_patterns pbEta pbS`. -/
def pbF (g : ℤ → Bool) : Config Bool := fun z => xor (g z.2) (decide (z.1 % 2 = 0))

/-- Row profile marking row `2`. -/
def pbG : ℤ → Bool := fun y => decide (y = 2)

/-- The configuration to which the false conclusion is applied. -/
def pbf : Config Bool := pbF pbG

lemma pbEta_step (z : ℤ × ℤ) : pbEta ((1, 0) + z) = !(pbEta z) := by
  simp only [pbEta, Prod.fst_add, Prod.snd_add]
  by_cases hc : (z.1 + z.2) % 2 = 0
  · have h2 : ¬ (((1 : ℤ) + z.1) + ((0 : ℤ) + z.2)) % 2 = 0 := by omega
    rw [decide_eq_false h2, decide_eq_true hc]
    rfl
  · have h2 : (((1 : ℤ) + z.1) + ((0 : ℤ) + z.2)) % 2 = 0 := by omega
    rw [decide_eq_true h2, decide_eq_false hc]
    rfl

lemma pbF_step (g : ℤ → Bool) (z : ℤ × ℤ) : pbF g ((1, 0) + z) = !(pbF g z) := by
  simp only [pbF, Prod.fst_add, Prod.snd_add]
  by_cases hc : z.1 % 2 = 0
  · have h2 : ¬ ((1 : ℤ) + z.1) % 2 = 0 := by omega
    cases hg : g ((0 : ℤ) + z.2) <;> cases hg2 : g z.2 <;> simp_all
  · have h2 : ((1 : ℤ) + z.1) % 2 = 0 := by omega
    cases hg : g ((0 : ℤ) + z.2) <;> cases hg2 : g z.2 <;> simp_all

lemma pbS_latticeConvex : LatticeConvex pbS := by
  have hsub : toReal '' (pbS : Set (ℤ × ℤ))
      ⊆ {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ p.2 = 0} := by
    rintro _ ⟨z, hz, rfl⟩
    simp only [pbS, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl <;> norm_num [toReal]
  have hcvx : Convex ℝ {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ p.2 = 0} := by
    intro p hp q hq a b ha hb hab
    obtain ⟨hp1, hp2, hp3⟩ := hp
    obtain ⟨hq1, hq2, hq3⟩ := hq
    refine ⟨?_, ?_, ?_⟩ <;>
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;>
      nlinarith
  intro z hz
  obtain ⟨h1, h2, h3⟩ := convexHull_min hsub hcvx hz
  simp only [toReal] at h1 h2 h3
  have h1' : (0 : ℤ) ≤ z.1 := by exact_mod_cast h1
  have h2' : z.1 ≤ 1 := by exact_mod_cast h2
  have h3' : z.2 = 0 := by exact_mod_cast h3
  obtain ⟨a, b⟩ := z
  simp only at h1' h2' h3'
  simp only [pbS, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
  omega

/-- Every orbit-closure point of the checkerboard alternates across the domino. -/
lemma pb_orbit_alt {x : Config Bool} (hx : x ∈ orbitClosure pbEta) :
    x (1, 0) = !(x (0, 0)) := by
  obtain ⟨u, hu⟩ := hx pbS
  have h0 : x (0, 0) = pbEta (u + (0, 0)) := hu (0, 0) (by decide)
  have h1 : x (1, 0) = pbEta (u + (1, 0)) := hu (1, 0) (by decide)
  have e0 : u + ((0 : ℤ), (0 : ℤ)) = u := add_zero u
  have e1 : u + ((1 : ℤ), (0 : ℤ)) = ((1 : ℤ), (0 : ℤ)) + u := add_comm _ _
  rw [e0] at h0
  rw [e1] at h1
  rw [h1, h0, pbEta_step]

/-- Satisfiability witness for the `IsGeneratingSet` hypothesis. -/
lemma pbS_generating : IsGeneratingSet pbEta pbS := by
  refine ⟨⟨(0, 0), by decide⟩, pbS_latticeConvex, ?_⟩
  intro a ha _
  have hcases : a = ((0 : ℤ), (0 : ℤ)) ∨ a = ((1 : ℤ), (0 : ℤ)) := by
    simpa only [pbS, Finset.mem_insert, Finset.mem_singleton] using ha
  rcases hcases with rfl | rfl
  · refine ⟨ha, ?_⟩
    intro x hx y hy hagree
    have h10 : x ((1 : ℤ), (0 : ℤ)) = y ((1 : ℤ), (0 : ℤ)) :=
      hagree (1, 0) (Finset.mem_erase.mpr ⟨by decide, by decide⟩)
    rw [pb_orbit_alt hx, pb_orbit_alt hy] at h10
    exact Bool.not_inj h10
  · refine ⟨ha, ?_⟩
    intro x hx y hy hagree
    have h00 : x ((0 : ℤ), (0 : ℤ)) = y ((0 : ℤ), (0 : ℤ)) :=
      hagree (0, 0) (Finset.mem_erase.mpr ⟨by decide, by decide⟩)
    rw [pb_orbit_alt hx, pb_orbit_alt hy, h00]

/-- The whole family `pbF g` sits inside the SFT: this is exactly the freedom that
Cyr-Kra's discrepancy condition on generating sets would remove. -/
lemma pbF_mem_SFT (g : ℤ → Bool) : pbF g ∈ SFT_patterns pbEta pbS := by
  intro v
  have hzv : ∀ t : ℤ × ℤ, ((0 : ℤ), (0 : ℤ)) + t = t := by
    intro t; refine Prod.ext ?_ ?_ <;> simp
  have hT0 : ∀ t : ℤ × ℤ, (T ((0 : ℤ), (0 : ℤ)) pbEta) t = pbEta t := by
    intro t; simp only [T]; rw [add_comm t, hzv]
  have hT1 : ∀ t : ℤ × ℤ,
      (T ((1 : ℤ), (0 : ℤ)) pbEta) t = pbEta (((1 : ℤ), (0 : ℤ)) + t) := by
    intro t; simp only [T]; rw [add_comm t]
  have hmem : ∀ s ∈ pbS, s = ((0 : ℤ), (0 : ℤ)) ∨ s = ((1 : ℤ), (0 : ℤ)) := by
    intro s hs
    simpa only [pbS, Finset.mem_insert, Finset.mem_singleton] using hs
  by_cases hc : pbF g v = pbEta v
  · refine ⟨(0, 0), ?_⟩
    intro s hs
    rcases hmem s hs with rfl | rfl
    · rw [hT0, hzv]; exact hc
    · rw [hT0, pbF_step, pbEta_step, hc]
  · have hne : pbF g v = !(pbEta v) := by
      cases h1 : pbF g v <;> cases h2 : pbEta v <;> simp_all
    refine ⟨(1, 0), ?_⟩
    intro s hs
    rcases hmem s hs with rfl | rfl
    · rw [hT1, hzv, pbEta_step]; exact hne
    · rw [hT1, pbF_step, pbEta_step, pbEta_step, hne]

/-- Satisfiability witness for the `IsAmbiguous` hypothesis, for every row-profile:
flipping row `1` changes nothing on the lower half plane but changes `(0,1)`. -/
lemma pb_ambiguous_of (g : ℤ → Bool) : IsAmbiguous pbEta pbS (pbF g) pbH := by
  refine ⟨pbF_mem_SFT g, pbF g, pbF (fun y => if y = 1 then !(g y) else g y),
    pbF_mem_SFT g, pbF_mem_SFT _, ?_, ?_⟩
  · intro z hz
    refine ⟨rfl, ?_⟩
    have hz2 : z.2 ≤ 0 := hz
    have hz1 : z.2 ≠ 1 := by omega
    simp only [pbF]
    rw [if_neg hz1]
  · refine ⟨((0 : ℤ), (1 : ℤ)), ?_, ?_⟩
    · intro hmem
      have : (1 : ℤ) ≤ 0 := hmem
      omega
    · cases hg : g 1 <;> simp [pbF, hg]

/-- Satisfiability witness for the `IsAmbiguous` hypothesis. -/
lemma pbf_ambiguous : IsAmbiguous pbEta pbS pbf pbH := pb_ambiguous_of pbG

/-- Non-degeneracy of the corrected `Border` in this instance: the origin really is
in the `(pbS, pbW)`-border of `pbH`, so the refutation below is not vacuous. -/
lemma pb_zero_mem_border : ((0 : ℤ), (0 : ℤ)) ∈ Border (pbS.erase pbW) pbW pbH := by
  have herase : pbS.erase pbW = pbS := by decide
  rw [herase]
  refine ⟨(0, 0), ⟨?_, ?_⟩, (0, 0), by decide, by simp⟩
  · intro s hs
    have hcases : s = ((0 : ℤ), (0 : ℤ)) ∨ s = ((1 : ℤ), (0 : ℤ)) := by
      simpa only [pbS, Finset.mem_insert, Finset.mem_singleton] using hs
    rcases hcases with rfl | rfl <;> simp [pbH]
  · intro s hs
    have hsS : s ∈ (pbS : Set (ℤ × ℤ)) := face_subset _ _ hs
    have hcases : s = ((0 : ℤ), (0 : ℤ)) ∨ s = ((1 : ℤ), (0 : ℤ)) := by
      simpa only [pbS, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] using hsS
    have hs2 : s.2 = 0 := by rcases hcases with rfl | rfl <;> rfl
    refine ⟨?_, ?_⟩
    · show (s + ((0 : ℤ), (0 : ℤ))).2 ≤ 0
      simp [hs2]
    · intro y hy
      have hy2 : y.2 ≤ 0 := hy
      simp only [pbW, dot, Prod.fst_add, Prod.snd_add]
      simp [hs2]
      omega

/-- **The former `periodic_border_of_ambiguous` is false as stated.**

This is the honest universal closure of the statement that stood in §5 until its
withdrawal on 2026-09-16: the implicit binders `{A}`, `{η}`, `{S}`, `{w}`, `{H}`, `{f}`
and the instance `[Finite A]` are made explicit, and the hypotheses and conclusion are
copied verbatim.  A `Type 0` counterexample refutes the universe-polymorphic statement. -/
theorem periodic_border_of_ambiguous_false :
    ¬ (∀ (A : Type) (_ : Finite A) (η : Config A) (S : Finset (ℤ × ℤ)),
        IsGeneratingSet η S → ∀ (w : ℤ × ℤ), Prim w →
        ∀ (H : Set (ℤ × ℤ)) (f : Config A), IsAmbiguous η S f H →
        ∃ (p : ℕ), 0 < p ∧ p ≤ S.card ∧
          ∀ z ∈ Border (S.erase w) w H, ∀ k : ℤ,
            f (z + (k * p * w.1, k * p * w.2)) = f z) := by
  intro Hyp
  obtain ⟨p, hp0, hpcard, hper⟩ :=
    Hyp Bool inferInstance pbEta pbS pbS_generating pbW (by decide) pbH pbf pbf_ambiguous
  have hcard : pbS.card = 2 := by decide
  rw [hcard] at hpcard
  have key : ∀ k : ℤ, pbf (((0 : ℤ), (0 : ℤ)) + (k * p * pbW.1, k * p * pbW.2))
      = pbf ((0 : ℤ), (0 : ℤ)) := fun k => hper _ pb_zero_mem_border k
  interval_cases p
  · -- `p = 1`: take `k = 2`, landing on the marked row `2`
    have h := key 2
    norm_num [pbW] at h
    revert h
    simp only [pbf, pbF, pbG]
    decide
  · -- `p = 2`: take `k = 1`
    have h := key 1
    norm_num [pbW] at h
    revert h
    simp only [pbf, pbF, pbG]
    decide

/-! ## §6. Non-degeneracy instances

We must prove that our definitions are not vacuous by providing
both positive and negative instances. -/

/-- Instance: a half-plane exists. -/
example : (halfPlaneGE (1, 0) 0).Nonempty := ⟨(0, 0), by simp [halfPlaneGE, dot]⟩

/-- Instance: the trivial configuration (constant function) is in any SFT. -/
example {A : Type*} (a : A) (S : Finset (ℤ × ℤ)) :
    (fun _ : ℤ × ℤ => a) ∈ SFT_patterns (fun _ : ℤ × ℤ => a) S := by
  intro v
  use 0
  intro s _
  rfl

/-- Instance: not every configuration is ambiguous.
The constant configuration has unique extensions. -/
example : ∃ (A : Type) (_ : Finite A) (η : Config A) (S : Finset (ℤ × ℤ))
    (f : Config A) (H : Set (ℤ × ℤ)), ¬IsAmbiguous η S f H := by
  use Bool, inferInstance
  use (fun _ => true)  -- constant configuration
  use {(0, 0)}  -- singleton set
  use (fun _ => true)
  use {z : ℤ × ℤ | z.2 ≥ 0}  -- upper half-plane
  intro ⟨_, g₁, g₂, hg₁_sft, hg₂_sft, hagree, z₀, hz₀_notin, hne⟩
  -- For the constant configuration, all extensions must also be constant
  -- So g₁ and g₂ must both be the constant true function
  -- This contradicts the requirement that they differ at z₀
  have hg₁_const : ∀ z, g₁ z = true := by
    intro z
    -- From hg₁_sft: g₁ ∈ SFT_patterns (fun _ => true) {(0,0)}
    obtain ⟨u, hu⟩ := hg₁_sft z
    have h := hu (0, 0) (by simp)
    simp only [T] at h
    convert h using 1
    congr 1
    simp
  have hg₂_const : ∀ z, g₂ z = true := by
    intro z
    obtain ⟨u, hu⟩ := hg₂_sft z
    have h := hu (0, 0) (by simp)
    simp only [T] at h
    convert h using 1
    congr 1
    simp
  -- Now g₁ z₀ = true and g₂ z₀ = true, contradicting hne
  exact hne (by rw [hg₁_const z₀, hg₂_const z₀])

/-! ### §6b. Non-degeneracy of the corrected `Border` and `Interior`

The `w`-edge guard restored in §2 could in principle have emptied `Border` out.  It does
not.  The running witness is

* `Sw = {(0,0), (0,1)}` — a vertical two-point segment;
* `w = (-1,0)` — the primitive **outer** normal of the left edge of `Sw`.  Since every
  point of `Sw` has first coordinate `0`, `face ↑Sw w = ↑Sw`, so `w ∈ E(↑Sw)`;
* `Hw = halfPlaneGE (1,0) 0 = {z | 0 ≤ z.1}` — a `w`-half plane, whose `w`-edge is
  `face Hw w = {z | z.1 = 0}`, its boundary line.

Then `Transl Sw w Hw = {v | v.1 = 0}`, which is nonempty, so the border is nonempty; and
the guard has real content, since `v = (1,0)` maps `Sw` into `Hw` (hence was admitted by
the old, `w`-free definition) yet is rejected by Definition 2.23. -/

/-- The witness set: a vertical two-point segment. -/
def Sw : Finset (ℤ × ℤ) := {(0, 0), (0, 1)}

/-- The witness half-plane `{z | 0 ≤ z.1}`. -/
def Hw : Set (ℤ × ℤ) := halfPlaneGE (1, 0) 0

theorem mem_Sw {z : ℤ × ℤ} : z ∈ Sw ↔ z = (0, 0) ∨ z = (0, 1) := by
  simp [Sw]

theorem mem_coe_Sw {z : ℤ × ℤ} :
    z ∈ (↑Sw : Set (ℤ × ℤ)) ↔ z = (0, 0) ∨ z = (0, 1) := by
  simp [Sw]

/-- Every point of `Sw` has first coordinate zero, so `⟨(-1,0), ·⟩` is constant on `Sw`;
hence the `(-1,0)`-face of `Sw` is all of `Sw`. -/
theorem face_coe_Sw : face (↑Sw : Set (ℤ × ℤ)) (-1, 0) = (↑Sw : Set (ℤ × ℤ)) := by
  ext z
  refine ⟨fun h => h.1, fun hz => ⟨hz, fun y hy => ?_⟩⟩
  rw [mem_coe_Sw] at hz hy
  rcases hz with rfl | rfl <;> rcases hy with rfl | rfl <;> simp [dot]

/-- The `(-1,0)`-face of the half-plane `Hw` is its boundary line `{z | z.1 = 0}`. -/
theorem face_Hw : face Hw (-1, 0) = {z : ℤ × ℤ | z.1 = 0} := by
  ext z
  constructor
  · rintro ⟨hzH, hmax⟩
    have h0 : (0 : ℤ) ≤ dot (1, 0) z := hzH
    have h1 := hmax (0, 0) (by simp [Hw, halfPlaneGE, dot])
    simp only [dot] at h0 h1
    simpa using le_antisymm (by omega) (by omega : (0 : ℤ) ≤ z.1)
  · intro hz1
    have hz1' : z.1 = 0 := hz1
    refine ⟨by simp [Hw, halfPlaneGE, dot, hz1'], fun y hy => ?_⟩
    have hy0 : (0 : ℤ) ≤ dot (1, 0) y := hy
    simp only [dot] at hy0 ⊢
    omega

/-- `w = (-1,0)` really is an edge normal of the witness set `Sw`. -/
example : IsEdge (↑Sw : Set (ℤ × ℤ)) (-1, 0) := by
  refine ⟨by simp [Prim], ?_⟩
  rw [face_coe_Sw]
  exact ⟨(0, 0), by rw [mem_coe_Sw]; exact Or.inl rfl,
    (0, 1), by rw [mem_coe_Sw]; exact Or.inr rfl, by simp⟩

/-- The translations admitted by Definition 2.23 for `(Sw, (-1,0), Hw)` are exactly those
on the boundary line: `Transl Sw (-1,0) Hw = {v | v.1 = 0}`. -/
theorem transl_Sw : Transl Sw (-1, 0) Hw = {v : ℤ × ℤ | v.1 = 0} := by
  ext v
  constructor
  · rintro ⟨-, hedge⟩
    have h := hedge (0, 0) (by rw [face_coe_Sw, mem_coe_Sw]; exact Or.inl rfl)
    rw [face_Hw] at h
    have h' : ((0, 0) + v).1 = 0 := h
    simpa using h'
  · intro hv
    have hv1 : v.1 = 0 := hv
    refine ⟨fun s hs => ?_, fun s hs => ?_⟩
    · rw [mem_Sw] at hs
      rcases hs with rfl | rfl <;> simp [Hw, halfPlaneGE, dot, hv1]
    · rw [face_coe_Sw, mem_coe_Sw] at hs
      rw [face_Hw]
      rcases hs with rfl | rfl <;> simp [hv1]

/-- **Non-degeneracy witness for the corrected `Border`.**  The point `(0,0)` lies in the
`(Sw, (-1,0))`-border of `Hw`, witnessed by the translation `v = 0`.  So the `w`-edge
guard of Definition 2.23 does not make `Border` empty. -/
example : ((0, 0) : ℤ × ℤ) ∈ Border Sw (-1, 0) Hw := by
  refine ⟨0, ?_, (0, 0), by rw [mem_Sw]; exact Or.inl rfl, by simp⟩
  rw [transl_Sw]
  rfl

/-- The border is in fact the whole boundary line, so it is infinite — a far cry from
empty. -/
example : {z : ℤ × ℤ | z.1 = 0} ⊆ Border Sw (-1, 0) Hw := by
  intro z hz
  have hz1 : z.1 = 0 := hz
  refine ⟨z, ?_, (0, 0), by rw [mem_Sw]; exact Or.inl rfl, by simp⟩
  rw [transl_Sw]
  exact hz1

/-- **The restored guard has content.**  The translation `v = (1,0)` takes `Sw` into `Hw`,
so the *old* `w`-free definition of `Border` admitted it; Definition 2.23 rejects it,
because the translated `w`-edge of `Sw` sits strictly inside `Hw` rather than on its
`w`-edge.  Hence the corrected `Border` is genuinely smaller than the old one. -/
example : (∀ s ∈ Sw, s + (1, 0) ∈ Hw) ∧ ((1, 0) : ℤ × ℤ) ∉ Transl Sw (-1, 0) Hw := by
  refine ⟨fun s hs => ?_, ?_⟩
  · rw [mem_Sw] at hs
    rcases hs with rfl | rfl <;> simp [Hw, halfPlaneGE, dot]
  · rw [transl_Sw]
    intro h
    have : (1 : ℤ) = 0 := h
    omega

/-! The `Interior` witness uses a *finite* `w`-edge, so that the index set `I` of
Definition 2.23 has genuine endpoints to be trimmed.  Take the same `Sw` and `w = (-1,0)`
but `Hf = {0} × [0,2]`.  Then `Transl Sw (-1,0) Hf = {(0,0), (0,1)}`, so the border is
all of `Hf`, whereas the `0`-interior — index range `[I_min, I_max - 1]`, a single
index — drops the endpoint translation and hence the border point `(0,0)`. -/

/-- The witness set with a finite `w`-edge: `{0} × [0,2]`. -/
def Hf : Set (ℤ × ℤ) := {z : ℤ × ℤ | z.1 = 0 ∧ 0 ≤ z.2 ∧ z.2 ≤ 2}

/-- Every point of `Hf` has first coordinate `0`, so `⟨(-1,0), ·⟩` is constant on it. -/
theorem face_Hf : face Hf (-1, 0) = Hf := by
  ext z
  refine ⟨fun h => h.1, fun hz => ⟨hz, fun y hy => ?_⟩⟩
  have hy1 : y.1 = 0 := hy.1
  have hz1 : z.1 = 0 := hz.1
  simp [dot, hy1, hz1]

/-- `Transl Sw (-1,0) Hf = {(0,0), (0,1)}`: the two translations that fit the
two-point segment inside the three-point column. -/
theorem transl_Hf : Transl Sw (-1, 0) Hf = {v : ℤ × ℤ | v.1 = 0 ∧ 0 ≤ v.2 ∧ v.2 ≤ 1} := by
  ext v
  constructor
  · rintro ⟨hin, -⟩
    have h0 : ((0, 0) + v) ∈ Hf := hin (0, 0) (by rw [mem_Sw]; exact Or.inl rfl)
    have h1 : ((0, 1) + v) ∈ Hf := hin (0, 1) (by rw [mem_Sw]; exact Or.inr rfl)
    obtain ⟨ha, hb, -⟩ := h0
    obtain ⟨-, -, hf⟩ := h1
    simp only [Prod.fst_add, Prod.snd_add] at ha hb hf
    exact ⟨by omega, by omega, by omega⟩
  · rintro ⟨hv1, hv2, hv3⟩
    refine ⟨fun s hs => ?_, fun s hs => ?_⟩
    · rw [mem_Sw] at hs
      rcases hs with rfl | rfl <;>
        exact ⟨by simp [hv1], by simp; omega, by simp; omega⟩
    · rw [face_coe_Sw, mem_coe_Sw] at hs
      rw [face_Hf]
      rcases hs with rfl | rfl <;>
        exact ⟨by simp [hv1], by simp; omega, by simp; omega⟩

theorem dir_neg_one_zero : dir ((-1 : ℤ), (0 : ℤ)) = (0, -1) := by simp [dir]

/-- **`Interior` is not degenerate, and is strictly smaller than `Border`.**  The point
`(0,2)` lies in the `0`-interior, so it is nonempty; the border point `(0,0)` does not,
matching Definition 2.23's half-open index range `[I_min + g, I_max - g - 1]`.  In
particular the previous definition — which was provably equal to `B` for every `B`, `m`,
`w`, because its `∃ v` was satisfied by `v = 0` — has been genuinely repaired. -/
example :
    ((0, 0) : ℤ × ℤ) ∈ Border Sw (-1, 0) Hf ∧
    ((0, 2) : ℤ × ℤ) ∈ Interior Sw (-1, 0) Hf 0 ∧
    ((0, 0) : ℤ × ℤ) ∉ Interior Sw (-1, 0) Hf 0 := by
  refine ⟨⟨(0, 0), ?_, (0, 0), by rw [mem_Sw]; exact Or.inl rfl, by simp⟩, ?_, ?_⟩
  · rw [transl_Hf]; exact ⟨rfl, le_refl 0, by norm_num⟩
  · -- `(0,2) = (0,1) + (0,1)` with `v = (0,1)`; both `v` and `v + 1•(0,-1) = (0,0)` are legal
    refine ⟨(0, 1), by rw [transl_Hf]; exact ⟨rfl, by norm_num, le_refl 1⟩, ?_,
      (0, 1), by rw [mem_Sw]; exact Or.inr rfl, by simp⟩
    intro i hi1 hi2
    rw [transl_Hf, dir_neg_one_zero]
    simp only [Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_mk, smul_eq_mul]
    refine ⟨by ring, by omega, by omega⟩
  · -- `(0,0)` forces `v = (0,0)` or `v = (0,-1)`; the step condition rules both out
    rintro ⟨v, hv, hstep, s, hsS, hsv⟩
    have hv' : v.1 = 0 ∧ 0 ≤ v.2 ∧ v.2 ≤ 1 := by rw [transl_Hf] at hv; exact hv
    have h1 := hstep 1 (by norm_num) (by norm_num)
    rw [transl_Hf, dir_neg_one_zero] at h1
    have h1' : (v + (1 : ℤ) • ((0, -1) : ℤ × ℤ)).1 = 0 ∧
        0 ≤ (v + (1 : ℤ) • ((0, -1) : ℤ × ℤ)).2 ∧
        (v + (1 : ℤ) • ((0, -1) : ℤ × ℤ)).2 ≤ 1 := h1
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_mk, smul_eq_mul] at h1'
    -- so `v.2 = 1`, forcing `s = (0,0) - (0,1) = (0,-1) ∉ Sw`
    rw [mem_Sw] at hsS
    have hsv2 : (0 : ℤ) = s.2 + v.2 := congrArg Prod.snd hsv
    rcases hsS with rfl | rfl <;> simp only at hsv2 <;> omega

/-! ## §7. Corollary 2.25 — ambiguous extension implies periodic interior

**2026-09-14 (statement repaired and proved).**

The version of `periodic_interior_of_ambiguous_extension` that stood here until
2026-09-14 carried a permanent `sorry`, and rightly so: it is **false**.  Its universal
closure is refuted, in this same file and with a machine-checked `Type 0` counterexample,
by `periodic_interior_of_ambiguous_extension_false` (§7b, kept untouched below; its
kernel closure is `[propext, Classical.choice, Quot.sound]`, no `sorryAx`).  The defect:
its conclusion read

    ∃ (p : ℕ) (B : Set (ℤ × ℤ)), 0 < p ∧ B.Nonempty ∧
      ∀ z ∈ B, ∀ k : ℤ, f (z + (k * p * w.1, k * p * w.2)) = f z

with `B` **completely unconstrained**, i.e. it claimed only "`f` has *some* `w`-period at
*some* single point".  Severing `B` from the extension does not weaken the claim into
triviality — it makes it false, because a configuration of the SFT can be `w`-periodic
nowhere (§7b's `pbG2 y = decide (0 ≤ y)` is non-constant on every arithmetic
progression).

Cyr-Kra's Corollary 2.25 never says that.  Its conclusion is (arXiv:1208.4090v2, §2.4):

> … there exists `j ≤ depth` such that `f` restricted to the `(|w ∩ 𝒮| - 1)`-interior of
> the `(𝒮 ∖ w, w)`-border of the `(w,j)`-subextension of `𝒯` is periodic with period
> vector **parallel to `w`** [the edge] and period at most `|w ∩ 𝒮| - 1`,

and its proof is "identical to the proof of Lemma 2.24 except that Morse-Hedlund is
applied on a finite (or semi-infinite) interval".  The repair below puts `B` back to
exactly that: the `g`-interior (`Interior`, Definition 2.23, §2 of this file) of the
`(𝒮 ∖ w, w)`-border of the given extension, with `g = |w ∩ 𝒮| - 1`.

**Faithfulness, and the deviations, stated plainly.**  What is kept from the source:
`𝒮` convex (`LatticeConvex`), `w ∈ E(𝒮)` (`IsEdge`), the edge-erased set `𝒮 ∖ w`
(`edgeErase`, Lemma 2.24's `S̃` — note this deletes the *whole* edge `w ∩ 𝒮`, whereas the
old statement's `S.erase w` deleted the single lattice point `w`, which is not even a
point of `𝒮` in this encoding), `|w ∩ 𝒮| = h + 1` so that `g = h = |w ∩ 𝒮| - 1`, the
"opposite edge is at least as long" hypothesis `|w ∩ 𝒮| ≤ |(-w) ∩ 𝒮|` under which
Lemma 2.24 chooses its bottom rows, the complexity budget `P η 𝒮 - P η (𝒮 ∖ w) ≤ h`
(Lemma 2.24's count of ambiguous `S̃`-colourings), Definition 2.23's progression
structure `V_{𝒮∖w,𝒯,w} ⊆ v₀ + ℤ · b` for the border translations (`hprog`, with
`b = dir w`), and the conclusion: periodicity on the `g`-interior along a vector
**parallel to the edge**.

Deviations, all of them widening no claim:
1. *Direction.*  Edges are indexed here by their primitive outer **normal** `w`, so the
   paper's "period vector parallel to `w`" is `dir w = (-w.2, w.1)`, not `w`.  (The old
   statement's `(k*p*w.1, k*p*w.2)` was periodic along the normal — a second, independent
   defect of it.)
2. *No `∃ j` over subextensions.*  Definition 2.19 (`Ext_w`, `(w,j)`-subextension) is not
   formalized in this development.  The statement is therefore proved for an **arbitrary**
   set `Tset` satisfying the Definition-2.23 data, hence in particular for whichever
   subextension a future formalization of `Ext_w` produces; nothing is lost.
3. *No `p ≤ h` bound.*  The bound in the source comes from Morse-Hedlund on a finite
   interval; the Morse-Hedlund available here (`Nivat.periodic_of_subwords_le`, and
   `Nivat.Colle.exists_row_period_of_ambiguousAlong` built on it) is bi-infinite and
   returns no bound.  The old statement had no bound either, so this is not a regression.
   (The naive finite-word form "complexity `p(h) ≤ h` ⇒ period `≤ h`" is *false* —
   `aaaaab` with `h = 2` — which is exactly why Cyr-Kra trim to the `g`-interior.)
4. *Ambiguity in `AmbiguousAlong` form.*  `IsAmbiguous` was bridged to periodicity only
   via §5's `periodic_border_of_ambiguous`, which is refuted (§5b) and was withdrawn on
   2026-09-16.  The hypothesis used here is Colle's `AmbiguousAlong`, which
   is verbatim the claim Cyr-Kra establish *inside* the proof of Lemma 2.24 ("every
   `f|_{S̃+u+(0,λ)}` has at least two extensions"), taken at an admissible anchor `v₀`.

§7c below exhibits a concrete instance — a `2 × 2` square, its left edge, the alphabet
`Bool` — in which **every** hypothesis holds simultaneously and the `g`-interior is
nonempty, so the repaired statement is not vacuous. -/

/-! ### §7.0  Finset-level faces and the edge-erased set `𝒮 ∖ w` -/

/-- `w ∩ 𝒮` of Cyr-Kra, as a `Finset`: the exposed face of `S` in the direction of the
outer normal `w`.  See `coe_faceF` for agreement with `Nivat.LE2.face`. -/
def faceF (S : Finset (ℤ × ℤ)) (w : ℤ × ℤ) : Finset (ℤ × ℤ) :=
  S.filter (fun z => ∀ y ∈ S, dot w y ≤ dot w z)

/-- `𝒮 ∖ w` of Cyr-Kra Lemma 2.24 (there called `S̃`): `S` with the **whole edge**
`w ∩ 𝒮` deleted. -/
def edgeErase (S : Finset (ℤ × ℤ)) (w : ℤ × ℤ) : Finset (ℤ × ℤ) := S \ faceF S w

theorem mem_faceF {S : Finset (ℤ × ℤ)} {w z : ℤ × ℤ} :
    z ∈ faceF S w ↔ z ∈ S ∧ ∀ y ∈ S, dot w y ≤ dot w z := by
  simp [faceF]

theorem coe_faceF (S : Finset (ℤ × ℤ)) (w : ℤ × ℤ) :
    (↑(faceF S w) : Set (ℤ × ℤ)) = face (↑S : Set (ℤ × ℤ)) w := by
  ext z
  simp [faceF, LE2.face]

theorem mem_edgeErase {S : Finset (ℤ × ℤ)} {w z : ℤ × ℤ} :
    z ∈ edgeErase S w ↔ z ∈ S ∧ ∃ y ∈ S, dot w z < dot w y := by
  simp [edgeErase, mem_faceF]
  tauto

theorem prim_dir {w : ℤ × ℤ} (hw : Prim w) : Primitive (dir w) := by
  rw [← prim_iff_primitive]
  simpa [Prim, dir, Int.gcd_comm] using hw

theorem interior_subset_border (S : Finset (ℤ × ℤ)) (w : ℤ × ℤ) (H : Set (ℤ × ℤ)) (g : ℕ) :
    Interior S w H g ⊆ Border S w H := by
  rintro z ⟨v, hv, -, s, hs, rfl⟩
  exact ⟨v, hv, s, hs, rfl⟩

theorem two_le_card_faceF {S : Finset (ℤ × ℤ)} {w : ℤ × ℤ}
    (hedge : IsEdge (↑S : Set (ℤ × ℤ)) w) : 2 ≤ (faceF S w).card := by
  obtain ⟨a, ha, b, hb, hab⟩ := hedge.2
  rw [← coe_faceF] at ha hb
  exact Finset.one_lt_card.mpr ⟨a, ha, b, hb, hab⟩

/-! ### §7.1  Lemma 2.24 in working form

This is the content of Cyr-Kra Lemma 2.24 that Corollary 2.25 consumes, assembled from
`Nivat.Colle.exists_rowBase_of_latticeConvex` (the choice of the bottom `h` rows of the
convex set, Lemma 2.24's `ℛ`) and `Nivat.Colle.exists_row_period_of_ambiguousAlong`
(the ambiguity count plus Morse-Hedlund).  The `(𝒮,w)`-border of `Tset` is periodic along
`dir w`, the direction of the edge. -/
theorem border_period_of_ambiguousAlong {A : Type*} [Finite A]
    {η f : Config A} (hf : f ∈ orbitClosure η)
    {S : Finset (ℤ × ℤ)} (hSc : LatticeConvex S) (hSne : S.Nonempty)
    {w : ℤ × ℤ} (hw : Prim w)
    {h : ℕ} (hh : 0 < h)
    (hcard : (faceF S w).card = h + 1)
    (hle : (faceF S w).card ≤ (faceF S (-w)).card)
    (hcount : P η S - P η (edgeErase S w) ≤ h)
    {Tset : Set (ℤ × ℤ)} {v₀ : ℤ × ℤ}
    (hprog : ∀ v' ∈ Transl (edgeErase S w) w Tset, ∃ l : ℤ, v' = v₀ + l • dir w)
    (hamb : AmbiguousAlong η (edgeErase S w) S (T v₀ f) (dir w)) :
    ∃ p : ℕ, 0 < p ∧ ∀ z ∈ Border (edgeErase S w) w Tset, ∀ k : ℤ,
      f (z + (k * (p : ℤ)) • dir w) = f z := by
  classical
  have hvprim : Primitive (dir w) := prim_dir hw
  set wR : ℝ × ℝ := toReal (-w) with hwR_def
  have hinner : ∀ z : ℤ × ℤ, inner2 wR z = -((dot w z : ℤ) : ℝ) := by
    intro z
    rw [hwR_def, inner2_toReal, dot_neg_left]
    push_cast; ring
  have hwR0 : wR ≠ 0 := by
    intro hcon
    have h1 : ((-w).1 : ℝ) = 0 := congrArg Prod.fst hcon
    have h2 : ((-w).2 : ℝ) = 0 := congrArg Prod.snd hcon
    have e1 : w.1 = 0 := by
      have : ((w.1 : ℝ)) = 0 := by simpa using h1
      exact_mod_cast this
    have e2 : w.2 = 0 := by
      have : ((w.2 : ℝ)) = 0 := by simpa using h2
      exact_mod_cast this
    exact hw.ne_zero (Prod.ext e1 e2)
  have hwv : inner2 wR (dir w) = 0 := by
    rw [hinner, dot_dir]; simp
  obtain ⟨z₀, hz₀S, hz₀max⟩ := S.exists_max_image (fun z => dot w z) hSne
  obtain ⟨z₁, hz₁S, hz₁min⟩ := S.exists_min_image (fun z => dot w z) hSne
  set c : ℝ := inner2 wR z₀ with hc_def
  set c' : ℝ := inner2 wR z₁ with hc'_def
  have hmin : ∀ z ∈ S, c ≤ inner2 wR z := by
    intro z hz
    rw [hc_def, hinner, hinner]
    have := hz₀max z hz
    exact_mod_cast neg_le_neg (by exact_mod_cast this)
  have hmax : ∀ z ∈ S, inner2 wR z ≤ c' := by
    intro z hz
    rw [hc'_def, hinner, hinner]
    have := hz₁min z hz
    exact_mod_cast neg_le_neg (by exact_mod_cast this)
  have hfc : (S.filter fun z => inner2 wR z = c) = faceF S w := by
    ext z
    simp only [Finset.mem_filter, mem_faceF, hc_def, hinner]
    constructor
    · rintro ⟨hzS, heq⟩
      have hz : dot w z = dot w z₀ := by
        have : ((dot w z : ℤ) : ℝ) = ((dot w z₀ : ℤ) : ℝ) := by linarith
        exact_mod_cast this
      exact ⟨hzS, fun y hy => by rw [hz]; exact hz₀max y hy⟩
    · rintro ⟨hzS, hzmax⟩
      refine ⟨hzS, ?_⟩
      have : dot w z = dot w z₀ := le_antisymm (hz₀max z hzS) (hzmax z₀ hz₀S)
      rw [this]
  have hfc' : (S.filter fun z => inner2 wR z = c') = faceF S (-w) := by
    ext z
    simp only [Finset.mem_filter, mem_faceF, hc'_def, hinner, dot_neg_left, neg_le_neg_iff]
    constructor
    · rintro ⟨hzS, heq⟩
      have hz : dot w z = dot w z₁ := by
        have : ((dot w z : ℤ) : ℝ) = ((dot w z₁ : ℤ) : ℝ) := by linarith
        exact_mod_cast this
      exact ⟨hzS, fun y hy => by rw [hz]; exact hz₁min y hy⟩
    · rintro ⟨hzS, hzmin⟩
      refine ⟨hzS, ?_⟩
      have : dot w z = dot w z₁ := le_antisymm (hzmin z₁ hz₁S) (hz₁min z hzS)
      rw [this]
  have hQ : (S.filter fun z => c < inner2 wR z) = edgeErase S w := by
    ext z
    simp only [Finset.mem_filter, mem_edgeErase, hc_def, hinner]
    constructor
    · rintro ⟨hzS, hlt⟩
      refine ⟨hzS, z₀, hz₀S, ?_⟩
      have : ((dot w z : ℤ) : ℝ) < ((dot w z₀ : ℤ) : ℝ) := by linarith
      exact_mod_cast this
    · rintro ⟨hzS, y, hyS, hlt⟩
      refine ⟨hzS, ?_⟩
      have hlt' : dot w z < dot w z₀ := lt_of_lt_of_le hlt (hz₀max y hyS)
      have : ((dot w z : ℤ) : ℝ) < ((dot w z₀ : ℤ) : ℝ) := by exact_mod_cast hlt'
      linarith
  have hleR : (S.filter fun z => inner2 wR z = c).card
      ≤ (S.filter fun z => inner2 wR z = c').card := by rw [hfc, hfc']; exact hle
  obtain ⟨B, hrow, hcover⟩ :=
    exists_rowBase_of_latticeConvex hSc hvprim hwR0 hwv hmin hmax hleR
  rw [hfc, hcard, hQ] at hrow
  rw [hQ] at hcover
  have hfT : T v₀ f ∈ orbitClosure η := T_mem_of_mem_orbitClosure hf v₀
  have hη : (Set.range η).Finite := Set.toFinite _
  obtain ⟨q, hq, hper⟩ :=
    exists_row_period_of_ambiguousAlong hη hfT
      (show edgeErase S w ⊆ S from Finset.sdiff_subset) hamb hh
      (by simpa only [Nat.add_sub_cancel] using hrow) hcount
  refine ⟨q, hq, ?_⟩
  have hstep : ∀ (t : ℤ) (b : ℤ × ℤ), b ∈ B →
      f ((t + (q : ℤ)) • dir w + b + v₀) = f (t • dir w + b + v₀) := by
    intro t b hb
    have := hper t b hb
    simpa [T] using this
  have hiter : ∀ (m : ℤ) (t : ℤ) (b : ℤ × ℤ), b ∈ B →
      f ((t + m * (q : ℤ)) • dir w + b + v₀) = f (t • dir w + b + v₀) := by
    intro m
    induction m using Int.induction_on with
    | zero => intro t b _; simp
    | succ n ih =>
        intro t b hb
        have e : t + ((n : ℤ) + 1) * (q : ℤ) = (t + (n : ℤ) * (q : ℤ)) + (q : ℤ) := by ring
        rw [e, hstep _ b hb, ih t b hb]
    | pred n ih =>
        intro t b hb
        have e : (t + (-(n : ℤ) - 1) * (q : ℤ)) + (q : ℤ) = t + (-(n : ℤ)) * (q : ℤ) := by ring
        have hs := hstep (t + (-(n : ℤ) - 1) * (q : ℤ)) b hb
        rw [e] at hs
        rw [← hs]
        exact ih t b hb
  intro z hz k
  obtain ⟨v', hv', s, hs, rfl⟩ := hz
  obtain ⟨l, rfl⟩ := hprog v' hv'
  obtain ⟨b, hb, kk, rfl⟩ := hcover s hs
  have e1 : kk • dir w + b + (v₀ + l • dir w) + (k * (q : ℤ)) • dir w
      = ((kk + l) + k * (q : ℤ)) • dir w + b + v₀ := by
    rw [add_smul, add_smul]; abel
  have e2 : kk • dir w + b + (v₀ + l • dir w) = (kk + l) • dir w + b + v₀ := by
    rw [add_smul]; abel
  rw [e1, e2]
  exact hiter k (kk + l) b hb

/-! ### §7.2  Corollary 2.25, repaired -/

/-- **Cyr-Kra Corollary 2.25, repaired.**  (Replaces, on 2026-09-14, a statement that was
false and refuted by `periodic_interior_of_ambiguous_extension_false`, §7b; see the §7
header for the full account of the defect and of this statement's source basis.)

`𝒮` is a convex lattice set with edge `w` (indexed by its primitive outer normal), of
length `|w ∩ 𝒮| = h + 1`, no longer than the opposite edge; `𝒮 ∖ w` is Lemma 2.24's `S̃`;
`Tset` is the extension, whose border translations form the progression
`v₀ + ℤ · dir w` of Definition 2.23; and `f` is ambiguous along `dir w` over `𝒮 ∖ w` in
Colle's sense.  Then `f` is periodic, along a vector **parallel to the edge**, on the
`h`-interior of the `(𝒮 ∖ w, w)`-border of `Tset` — with `h = |w ∩ 𝒮| - 1`, exactly the
`g` of the source. -/
theorem periodic_interior_of_ambiguous_extension {A : Type*} [Finite A]
    {η f : Config A} (hf : f ∈ orbitClosure η)
    {S : Finset (ℤ × ℤ)} (hSc : LatticeConvex S) (hSne : S.Nonempty)
    {w : ℤ × ℤ} (hedge : IsEdge (↑S : Set (ℤ × ℤ)) w)
    {h : ℕ} (hcard : (faceF S w).card = h + 1)
    (hle : (faceF S w).card ≤ (faceF S (-w)).card)
    (hcount : P η S - P η (edgeErase S w) ≤ h)
    {Tset : Set (ℤ × ℤ)} {v₀ : ℤ × ℤ}
    (hprog : ∀ v' ∈ Transl (edgeErase S w) w Tset, ∃ l : ℤ, v' = v₀ + l • dir w)
    (hamb : AmbiguousAlong η (edgeErase S w) S (T v₀ f) (dir w)) :
    ∃ p : ℕ, 0 < p ∧ ∀ z ∈ Interior (edgeErase S w) w Tset h, ∀ k : ℤ,
      f (z + (k * (p : ℤ)) • dir w) = f z := by
  have hh : 0 < h := by have := two_le_card_faceF hedge; omega
  obtain ⟨p, hp, hper⟩ :=
    border_period_of_ambiguousAlong hf hSc hSne hedge.1 hh hcard hle hcount hprog hamb
  exact ⟨p, hp, fun z hz => hper z (interior_subset_border _ _ _ _ hz)⟩

/-! ## §7b. The *previous* `periodic_interior_of_ambiguous_extension` is false

**Kept deliberately.**  This section refutes the statement that stood in §7 until
2026-09-14 (and whose repaired replacement now occupies §7); it is the evidence that the
repair was necessary rather than cosmetic, and it must not be deleted.

The defect is independent of the one in §5b and is much cruder: the conclusion
existentially quantifies an *unconstrained* nonempty set `B`, so it asserts only
"`f` has *some* `w`-period at *some* single point".  Cyr-Kra's Corollary 2.25 ties
the periodic region to the `g`-interior of the border of a *specific* subextension;
dropping that tie does not weaken the statement into triviality, it makes it false,
because a configuration of the SFT may fail to be `w`-periodic at every point.

The witness reuses §5b's data with the row-profile `pbG2 y = decide (0 ≤ y)`.
Along any arithmetic progression `y₀ + kp` with `p > 0` this profile takes both
values, so `pbF pbG2` is `w`-periodic at no point at all, while all four
hypotheses (`IsGeneratingSet`, `Prim`, the balancedness condition, ambiguity)
hold. -/

/-- A row-profile that is non-constant on every arithmetic progression. -/
def pbG2 : ℤ → Bool := fun y => decide (0 ≤ y)

/-- The configuration refuting Corollary 2.25 as stated. -/
def pbf2 : Config Bool := pbF pbG2

/-- Satisfiability witness for the balancedness hypothesis. -/
lemma pbS_balanced : ∀ x : ℤ, (pbS.filter (fun z => z.1 = x)).Nonempty →
    pbS.card - 1 ≤ (pbS.filter (fun z => z.1 = x)).card := by
  intro x hx
  have hc : pbS.card = 2 := by decide
  have h1 : 0 < (pbS.filter (fun z => z.1 = x)).card := Finset.card_pos.mpr hx
  omega

/-- **`periodic_interior_of_ambiguous_extension` is false as it stood before 2026-09-14.**

The honest universal closure of the statement that occupied §7 until then: implicit
binders and the `[Finite A]` instance are made explicit, hypotheses and conclusion copied
verbatim.  A `Type 0` counterexample refutes the universe-polymorphic statement. -/
theorem periodic_interior_of_ambiguous_extension_false :
    ¬ (∀ (A : Type) (_ : Finite A) (η : Config A) (S : Finset (ℤ × ℤ)),
        IsGeneratingSet η S → ∀ (w : ℤ × ℤ), Prim w →
        (∀ x : ℤ, (S.filter (fun z => z.1 = x)).Nonempty →
          S.card - 1 ≤ (S.filter (fun z => z.1 = x)).card) →
        ∀ (f : Config A), (∃ T : Set (ℤ × ℤ), IsAmbiguous η S f T) →
        ∃ (p : ℕ) (B : Set (ℤ × ℤ)),
          0 < p ∧ B.Nonempty ∧
          ∀ z ∈ B, ∀ k : ℤ, f (z + (k * p * w.1, k * p * w.2)) = f z) := by
  intro Hyp
  obtain ⟨p, B, hp0, hBne, hper⟩ :=
    Hyp Bool inferInstance pbEta pbS pbS_generating pbW (by decide) pbS_balanced
      pbf2 ⟨pbH, pb_ambiguous_of pbG2⟩
  obtain ⟨z, hzB⟩ := hBne
  have hpt : ∀ k : ℤ, z + (k * (p : ℤ) * pbW.1, k * (p : ℤ) * pbW.2)
      = (z.1, z.2 + k * (p : ℤ)) := by
    intro k
    simp only [pbW]
    refine Prod.ext ?_ ?_ <;> simp
  have hxor : ∀ a b c : Bool, (xor a c) = (xor b c) → a = b := by decide
  have hcancel : ∀ k : ℤ, pbG2 (z.2 + k * (p : ℤ)) = pbG2 z.2 := by
    intro k
    have h := hper z hzB k
    rw [hpt k] at h
    simp only [pbf2, pbF] at h
    exact hxor _ _ _ h
  have hP : (1 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp0
  have hN : (0 : ℤ) ≤ ((z.2).natAbs : ℤ) := Int.natCast_nonneg _
  -- far to the right the profile is `true`
  have hup : 0 ≤ z.2 + ((z.2).natAbs : ℤ) * (p : ℤ) := by
    have h1 : -z.2 ≤ ((z.2).natAbs : ℤ) := by omega
    nlinarith [mul_nonneg hN (by linarith : (0 : ℤ) ≤ (p : ℤ) - 1)]
  -- far to the left it is `false`
  have hdn : z.2 + (-(((z.2).natAbs : ℤ) + 1)) * (p : ℤ) < 0 := by
    have h1 : z.2 ≤ ((z.2).natAbs : ℤ) := by omega
    nlinarith [mul_nonneg (by linarith : (0 : ℤ) ≤ ((z.2).natAbs : ℤ) + 1)
      (by linarith : (0 : ℤ) ≤ (p : ℤ) - 1)]
  have e1 : pbG2 z.2 = true := by
    rw [← hcancel ((z.2).natAbs : ℤ)]
    simp only [pbG2]
    exact decide_eq_true hup
  have e2 : pbG2 z.2 = false := by
    rw [← hcancel (-(((z.2).natAbs : ℤ) + 1))]
    simp only [pbG2]
    exact decide_eq_false (not_le.mpr hdn)
  rw [e1] at e2
  exact Bool.noConfusion e2

/-! ## §7c. The repaired Corollary 2.25 is not vacuous

A statement can be "repaired" by piling on hypotheses until nothing satisfies them.  This
section rules that out for §7 by exhibiting a concrete instance in which **every**
hypothesis of `periodic_interior_of_ambiguous_extension` holds simultaneously *and* the
`h`-interior on which its conclusion speaks is nonempty.

The data: `𝒮` the unit square `{0,1}²`, `w = (-1,0)` its left edge (as an outer normal),
so `w ∩ 𝒮 = {(0,0),(0,1)}` has two points and `h = 1`; the opposite edge `(-w) ∩ 𝒮` also
has two, so `hle` holds; `𝒮 ∖ w = {(1,0),(1,1)}`; `η = f` the column indicator
`z ↦ [z.1 = 0]`, for which `P η 𝒮 = 3` and `P η (𝒮 ∖ w) ≥ 2`, so the budget
`P η 𝒮 - P η (𝒮 ∖ w) ≤ 1 = h` holds; `Tset` the vertical strip `1 ≤ z.1 ≤ 5`, whose
border translations are exactly `{v : v.1 = 0} = (0,0) + ℤ · dir w`, giving `hprog`; and
ambiguity along `dir w = (0,-1)` witnessed by the anchors `(0,0)` and `(2,0)`, which agree
with `f` on `𝒮 ∖ w` but differ on `𝒮`.  The point `(1,0)` lies in the `1`-interior. -/

/-- §7c witness: the unit square. -/
def wtS : Finset (ℤ × ℤ) := {(0, 0), (0, 1), (1, 0), (1, 1)}

/-- §7c witness: the outer normal of the left edge of `wtS`. -/
def wtW : ℤ × ℤ := (-1, 0)

/-- §7c witness: the column indicator configuration. -/
def wtEta : Config Bool := fun z => decide (z.1 = 0)

/-- §7c witness: the extension, a vertical strip. -/
def wtT : Set (ℤ × ℤ) := {z : ℤ × ℤ | 1 ≤ z.1 ∧ z.1 ≤ 5}

theorem wtS_latticeConvex : LatticeConvex wtS := by
  have hsub : toReal '' (wtS : Set (ℤ × ℤ))
      ⊆ {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1} := by
    rintro _ ⟨z, hz, rfl⟩
    simp only [wtS, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl <;> norm_num [toReal]
  have hcvx : Convex ℝ {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1} := by
    intro p hp q hq a b ha hb hab
    obtain ⟨hp1, hp2, hp3, hp4⟩ := hp
    obtain ⟨hq1, hq2, hq3, hq4⟩ := hq
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;>
      nlinarith
  intro z hz
  obtain ⟨h1, h2, h3, h4⟩ := convexHull_min hsub hcvx hz
  simp only [toReal] at h1 h2 h3 h4
  have h1' : (0 : ℤ) ≤ z.1 := by exact_mod_cast h1
  have h2' : z.1 ≤ 1 := by exact_mod_cast h2
  have h3' : (0 : ℤ) ≤ z.2 := by exact_mod_cast h3
  have h4' : z.2 ≤ 1 := by exact_mod_cast h4
  obtain ⟨a, b⟩ := z
  simp only at h1' h2' h3' h4'
  simp only [wtS, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
  omega

theorem wt_faceF : faceF wtS wtW = {(0, 0), (0, 1)} := by decide

theorem wt_faceF_neg : faceF wtS (-wtW) = {(1, 0), (1, 1)} := by decide

theorem wt_edgeErase : edgeErase wtS wtW = {(1, 0), (1, 1)} := by decide

theorem wt_isEdge : IsEdge (↑wtS : Set (ℤ × ℤ)) wtW := by
  refine ⟨by decide, ?_⟩
  rw [← coe_faceF, wt_faceF]
  refine ⟨(0, 0), by simp, (0, 1), by simp, by simp⟩

theorem wt_P_S_le : P wtEta wtS ≤ 3 := by
  have hsub : patterns wtEta wtS ⊆
      ({pattern wtEta wtS (0, 0), pattern wtEta wtS (-1, 0),
        pattern wtEta wtS (2, 0)} : Set (wtS → Bool)) := by
    rintro _ ⟨u, rfl⟩
    by_cases h0 : u.1 = 0
    · refine Or.inl ?_
      funext q
      show wtEta (u + (q : ℤ × ℤ)) = wtEta (((0, 0) : ℤ × ℤ) + (q : ℤ × ℤ))
      simp only [wtEta, Prod.fst_add, h0]
    by_cases h1 : u.1 = -1
    · refine Or.inr (Or.inl ?_)
      funext q
      show wtEta (u + (q : ℤ × ℤ)) = wtEta (((-1, 0) : ℤ × ℤ) + (q : ℤ × ℤ))
      simp only [wtEta, Prod.fst_add, h1]
    · refine Or.inr (Or.inr ?_)
      funext q
      have hq : (q : ℤ × ℤ) ∈ wtS := q.2
      have hq1 : (q : ℤ × ℤ).1 = 0 ∨ (q : ℤ × ℤ).1 = 1 := by
        simp only [wtS, Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with h | h | h | h <;> rw [h] <;> simp
      show wtEta (u + (q : ℤ × ℤ)) = wtEta (((2, 0) : ℤ × ℤ) + (q : ℤ × ℤ))
      simp only [wtEta, Prod.fst_add, decide_eq_decide]
      omega
  have h1 : P wtEta wtS ≤ ({pattern wtEta wtS (0, 0), pattern wtEta wtS (-1, 0),
      pattern wtEta wtS (2, 0)} : Set (wtS → Bool)).ncard :=
    Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 : ({pattern wtEta wtS (0, 0), pattern wtEta wtS (-1, 0),
      pattern wtEta wtS (2, 0)} : Set (wtS → Bool)).ncard ≤ 3 := by
    refine le_trans (Set.ncard_insert_le _ _) ?_
    have := Set.ncard_insert_le (pattern wtEta wtS (-1, 0))
      ({pattern wtEta wtS (2, 0)} : Set (wtS → Bool))
    simp only [Set.ncard_singleton] at this
    omega
  omega

theorem wt_P_Q_ge : 2 ≤ P wtEta (edgeErase wtS wtW) := by
  have hmem : ((1, 0) : ℤ × ℤ) ∈ edgeErase wtS wtW := by rw [wt_edgeErase]; decide
  have hne : pattern wtEta (edgeErase wtS wtW) (0, 0)
      ≠ pattern wtEta (edgeErase wtS wtW) (-1, 0) := by
    intro hcon
    have := congrFun hcon ⟨(1, 0), hmem⟩
    simp only [pattern, wtEta] at this
    revert this
    norm_num
  have hsub : ({pattern wtEta (edgeErase wtS wtW) (0, 0),
      pattern wtEta (edgeErase wtS wtW) (-1, 0)} : Set (edgeErase wtS wtW → Bool))
      ⊆ patterns wtEta (edgeErase wtS wtW) := by
    rintro p (rfl | rfl)
    · exact ⟨(0, 0), rfl⟩
    · exact ⟨(-1, 0), rfl⟩
  have := Set.ncard_le_ncard hsub
    (patterns_finite_of_range_finite (Set.toFinite _) (edgeErase wtS wtW))
  rwa [Set.ncard_pair hne] at this

theorem wt_faceF_Q : faceF (edgeErase wtS wtW) wtW = edgeErase wtS wtW := by decide

theorem wt_face_T : face wtT wtW = {z : ℤ × ℤ | z.1 = 1} := by
  ext z
  simp only [LE2.face, wtT, wtW, dot, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨h1, h2⟩, hmax⟩
    have h3 := hmax (1, 0) (by norm_num)
    norm_num at h3
    omega
  · intro hz
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    rintro y ⟨hy1, hy2⟩
    omega

theorem wt_Transl : Transl (edgeErase wtS wtW) wtW wtT = {v : ℤ × ℤ | v.1 = 0} := by
  ext v
  constructor
  · rintro ⟨-, h2⟩
    have hq : ((1, 0) : ℤ × ℤ) ∈ face (↑(edgeErase wtS wtW) : Set (ℤ × ℤ)) wtW := by
      rw [← coe_faceF, wt_faceF_Q, wt_edgeErase]
      simp
    have h3 := h2 _ hq
    rw [wt_face_T] at h3
    have : (1 : ℤ) + v.1 = 1 := h3
    show v.1 = 0
    omega
  · intro hv
    have hv' : v.1 = 0 := hv
    constructor
    · intro s hs
      rw [wt_edgeErase] at hs
      simp only [Finset.mem_insert, Finset.mem_singleton] at hs
      rcases hs with rfl | rfl <;> exact ⟨by simp; omega, by simp; omega⟩
    · intro s hs
      rw [← coe_faceF, wt_faceF_Q, wt_edgeErase] at hs
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hs
      rw [wt_face_T]
      rcases hs with rfl | rfl <;> · show (1 : ℤ) + v.1 = 1; omega

theorem wt_dir : dir wtW = ((0, -1) : ℤ × ℤ) := by decide

theorem wt_hprog : ∀ v' ∈ Transl (edgeErase wtS wtW) wtW wtT,
    ∃ l : ℤ, v' = ((0, 0) : ℤ × ℤ) + l • dir wtW := by
  intro v' hv'
  rw [wt_Transl] at hv'
  have h1 : v'.1 = 0 := hv'
  refine ⟨-v'.2, Prod.ext ?_ ?_⟩
  · simpa [wt_dir] using h1
  · simp [wt_dir]

theorem wt_amb :
    AmbiguousAlong wtEta (edgeErase wtS wtW) wtS (T ((0, 0) : ℤ × ℤ) wtEta) (dir wtW) := by
  intro t
  refine ⟨(0, 0), (2, 0), ?_, ?_, ?_⟩
  · intro hcon
    have hmem : ((0, 0) : ℤ × ℤ) ∈ wtS := by decide
    have := congrFun hcon ⟨(0, 0), hmem⟩
    simp only [pattern, wtEta] at this
    revert this
    norm_num
  · intro q hq
    rw [wt_edgeErase] at hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl <;> simp [wtEta, T, wt_dir]
  · intro q hq
    rw [wt_edgeErase] at hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl <;> simp [wtEta, T, wt_dir]

theorem wt_interior_mem : ((1, 0) : ℤ × ℤ) ∈ Interior (edgeErase wtS wtW) wtW wtT 1 := by
  refine ⟨(0, 0), ?_, ?_, (1, 0), ?_, ?_⟩
  · rw [wt_Transl]; rfl
  · intro i _ _
    rw [wt_Transl]
    show (((0, 0) : ℤ × ℤ) + i • dir wtW).1 = 0
    simp [wt_dir]
  · rw [wt_edgeErase]; decide
  · simp

/-- **Non-vacuity of the repaired Corollary 2.25.**  Every hypothesis of
`periodic_interior_of_ambiguous_extension` is simultaneously satisfiable, and on the
instance that satisfies them the `h`-interior carrying the conclusion is nonempty.  So the
repair in §7 did not buy provability by making the hypotheses unsatisfiable or the
conclusion empty. -/
theorem periodic_interior_of_ambiguous_extension_nonvacuous :
    (Interior (edgeErase wtS wtW) wtW wtT 1).Nonempty ∧
      ∃ p : ℕ, 0 < p ∧ ∀ z ∈ Interior (edgeErase wtS wtW) wtW wtT 1, ∀ k : ℤ,
        wtEta (z + (k * (p : ℤ)) • dir wtW) = wtEta z := by
  refine ⟨⟨(1, 0), wt_interior_mem⟩, ?_⟩
  refine periodic_interior_of_ambiguous_extension (h := 1)
    (self_mem_orbitClosure wtEta) wtS_latticeConvex (by decide) wt_isEdge
    (by rw [wt_faceF]; decide) (by rw [wt_faceF, wt_faceF_neg]; decide) ?_ wt_hprog wt_amb
  have h1 := wt_P_S_le
  have h2 := wt_P_Q_ge
  omega

end Nivat.CK224
