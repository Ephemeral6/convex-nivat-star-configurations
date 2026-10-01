/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.ShellRegionJ
import Nivat.External.Colle.ItemII

/-!
# `Â_∞`'s two boundary normals: the maximality and infinity producers (`b3_colle2.txt:488-506`)

Lane `lane-leafa-shell`, 2026-09-24 (team-lead's nomination ruling, round 187).

`ShellRegionJ.E_iUnion_eq_insert_arc` (`ShellRegionJ.lean:291`) assembles
`E (⋃ Ahat) = {ν₀, J} ∪ Arc` from consumer-facing binders and says so in its own docstring:
the ray/maximality pairs are "supplied by whoever pins `g₁`/`g_J`, **not re-derived here** —
this file only assembles".  This file is that supplier for the two *maximality* binders,
`hmax_ν₀` (`ShellRegionJ.lean:297`) and `hmax_J` (`ShellRegionJ.lean:300`), plus the
`ℓ`-side face infinity and the `ℓ_J`-side edge membership.

## What is here, and where each piece comes from in the paper

| declaration | paper | supplies |
|---|---|---|
| `ahat_subset_halfplane` | `:488` + `:498` | every layer sits under one support line |
| `hmax_neg_nl` | `:488` + `:498` | `E_iUnion_eq_insert_arc`'s `hmax_ν₀`, at `ν₀ = -nℓ` |
| `mem_face_neg_nl_of_dot_eq`, `face_neg_nl_infinite` | `:506` (the `ℓ`-parallel edge) | the `.Infinite` half of that semi-infinite edge |
| `hmax_of_hhp_of_mono` | `:504` → `g_J` pinned | `E_iUnion_eq_insert_arc`'s `hmax_J` |
| `gJ_mem_of_faceStart_pinned`, `mem_E_iUnion_of_faceStart_pinned` | `:506` (the `ℓ_J`-parallel edge) | `ν_J ∈ E Â_∞` |

Receipts and the surrounding analysis (including the discriminating counterexamples that show
each hypothesis is load-bearing) live in `tmp/wip/lane-leafa-shell-htop-limitedge.lean`,
§12–§17; this file carries only the declarations with a named main-repo binder to feed.

## `Monotone Ahat` is a **field**, not a derivable fact

Two declarations here (`hmax_of_hhp_of_mono`, `mem_E_iUnion_of_faceStart_pinned`) take
`hmono : Monotone Ahat`.  Read `AhatMono.lean:43` precisely: what it refutes is that
"`:486-500` **does not supply** `AhatMono`", i.e. that the containment is *derivable* from the
other chain binders of `:486-500`.  It does **not** say the containment is false downstream.

Downstream it is a structure field: `Nivat.Colle35.ChainData.AhatMono`
(`Lemma35.lean:729`, `∀ i j, i ≤ j → Ahat i ⊆ Ahat j`), stated on the **same raw index `i`**
on which the consumer forms `Â_∞ = ⋃ i, Ahat i`.  So a caller holding a `ChainData` discharges
`hmono` verbatim by `fun i j hij => cd.AhatMono i j hij`, and these statements are **not**
vacuous there; the obligation is the *producer's* (`exists_chainData` must build the field).

⚠ An earlier revision of this paragraph said the raw indexing makes these two statements
vacuous and that callers must instantiate only post-reindexing.  That was over-strong and is
withdrawn (lane-leafa-shell, 2026-09-24); the reindexing route below is still correct, it is
just not the only one.

**Reindexing route (still valid)**: `ChainKK.exists_normalised_chain` (`ChainKK.lean:93`)
outputs one chain on which `AhatMono`, `Exhausts`, `hfin`, the `:488` alignment and
`dot nℓ g₁ = cz` hold **simultaneously** — it composes `ItemIIChain.exists_itemII_chain`,
`AItemFour.exists_endpoint_shift` and `LeafAItemII.exists_subseq_chain`, and its last conjunct
is exactly `∀ i j, i ≤ j → hatOf A kk vl i ⊆ hatOf A kk vl j`.  The subsequence is consumed
inside that theorem, so its output carries no leftover `σ`.

`hmax_neg_nl` and `face_neg_nl_infinite` carry no monotonicity at all — the `ℓ`-side bound is
per-layer, because the support value `cz` is `v⃗_ℓ`-translation invariant (`hperp`).
-/

set_option autoImplicit false

namespace Nivat.AhatLimitEdge

open Nivat Nivat.LE2

/-! ## §1 The `ℓ` side: one support line for every layer

原文 `b3_colle2.txt:488` defines `Â_i := A_i − k_i v⃗_ℓ` and `:498` states
`⋃_{i=1}^∞ A_i = ℋ(ℓ^(−))`.  Since `dot nℓ v⃗_ℓ = 0` (`hperp`), subtracting `k_i v⃗_ℓ` does not
move a point's `nℓ`-height, so *every* layer lands under the *same* line — no monotonicity,
no `i₀`, no subsequence.
-/

/-- Every layer `Â_i` lies on one side of a single support line.
Quantifiers: `hAhat` is `:488`'s `Â_i := A_i − k_i v⃗_ℓ` (as a set equation, one per `i`),
`hexh` is `:498`'s `⋃ A_i = ℋ(ℓ^(−))` in `Colle35.Exhausts` form (`ItemII.lean:96`, the
**inward** normal `nℓ`, so the outward edge normal is `-nℓ`), `hperp` is `⟪nℓ, v⃗_ℓ⟫ = 0`. -/
theorem ahat_subset_halfplane {A Ahat : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ} {nl vl : ℤ × ℤ} {cz : ℤ}
    (hAhat : ∀ i, Ahat i = {z | z + (kk i : ℤ) • vl ∈ A i})
    (hexh : Nivat.Colle35.Exhausts A nl cz) (hperp : dot nl vl = 0) (i : ℕ) :
    Ahat i ⊆ {z | dot (-nl) z ≤ -cz} := by
  intro z hz
  rw [hAhat i] at hz
  have hmem : z + (kk i : ℤ) • vl ∈ (⋃ j, A j) := Set.mem_iUnion.mpr ⟨i, hz⟩
  rw [hexh] at hmem
  have hval : dot nl (z + (kk i : ℤ) • vl) = dot nl z :=
    Nivat.Colle35.dot_add_zsmul_of_perp hperp z _
  have : cz ≤ dot nl z := by rw [← hval]; exact hmem
  simp only [Set.mem_setOf_eq, dot, Prod.fst_neg, Prod.snd_neg] at this ⊢
  linarith

/-- **`E_iUnion_eq_insert_arc`'s `hmax_ν₀` binder** (`ShellRegionJ.lean:297`), at `ν₀ = -nℓ`.
Any `g₁` on the support line attains the bound; `:488` supplies such a `g₁` (the common final
point of `Â_i ∩ ℓ^(−)`) and `ChainKK.exists_normalised_chain` exports `dot nℓ g₁ = cz`
verbatim.  ⚠ No monotonicity and no `i₀`: the bound is per-layer. -/
theorem hmax_neg_nl
    {A Ahat : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ} {nl vl : ℤ × ℤ} {cz : ℤ}
    (hAhat : ∀ i, Ahat i = {z | z + (kk i : ℤ) • vl ∈ A i})
    (hexh : Nivat.Colle35.Exhausts A nl cz) (hperp : dot nl vl = 0)
    {g₁ : ℤ × ℤ} (hg₁ : dot nl g₁ = cz) :
    ∀ z ∈ (⋃ i, Ahat i), dot (-nl) z ≤ dot (-nl) g₁ := by
  intro z hz
  obtain ⟨i, hzi⟩ := Set.mem_iUnion.mp hz
  have h1 : dot (-nl) z ≤ -cz := ahat_subset_halfplane hAhat hexh hperp i hzi
  simp only [dot, Prod.fst_neg, Prod.snd_neg] at h1 hg₁ ⊢
  linarith

/-! ## §2 The `ℓ` side: that face is infinite

原文 `b3_colle2.txt:506`: "… with two semi-infinite edges, one of which is parallel to `ℓ` …".
This section proves the `.Infinite` conjunct for the `ℓ` one.  `:498`'s `Exhausts` hands over
the *whole* support line inside `⋃ A_i`, and `hperp` moves it into `⋃ Â_i` one `v⃗_ℓ`-step at a
time.  ⚠ What comes out is an **upper-unbounded** set of offsets, not all of `ℤ`: `k_i ≥ 0`
pushes the offset one way.  Upper-unboundedness already contradicts finiteness, which is all
`.Infinite` needs — so Figure 6's monotonicity (`:508`) is *not* used here.
-/

/-- Translating along `v⃗_ℓ` is injective on offsets when `v⃗_ℓ ≠ 0`. -/
theorem zsmul_left_cancel_of_ne_zero {vl : ℤ × ℤ} (hvl : vl ≠ 0) {s t : ℤ}
    (h : s • vl = t • vl) : s = t := by
  have h1 : (s - t) * vl.1 = 0 := by
    have := congrArg Prod.fst h
    simp only [Prod.smul_fst, smul_eq_mul] at this
    linarith [this]
  have h2 : (s - t) * vl.2 = 0 := by
    have := congrArg Prod.snd h
    simp only [Prod.smul_snd, smul_eq_mul] at this
    linarith [this]
  rcases mul_eq_zero.mp h1 with h | h
  · omega
  · rcases mul_eq_zero.mp h2 with h' | h'
    · omega
    · exact absurd (Prod.ext h h' : vl = (0, 0)) hvl

/-- A point of `⋃ Â_i` at height exactly `cz` is in the `(-nℓ)`-face: `§1` caps the whole
union at `-cz`, and this point attains the cap. -/
theorem mem_face_neg_nl_of_dot_eq
    {A Ahat : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ} {nl vl : ℤ × ℤ} {cz : ℤ}
    (hAhat : ∀ i, Ahat i = {z | z + (kk i : ℤ) • vl ∈ A i})
    (hexh : Nivat.Colle35.Exhausts A nl cz) (hperp : dot nl vl = 0)
    {z : ℤ × ℤ} (hz : z ∈ (⋃ i, Ahat i)) (hdot : dot nl z = cz) :
    z ∈ face (⋃ i, Ahat i) (-nl) := by
  refine ⟨hz, fun y hy => ?_⟩
  obtain ⟨i, hyi⟩ := Set.mem_iUnion.mp hy
  have h1 : dot (-nl) y ≤ -cz := ahat_subset_halfplane hAhat hexh hperp i hyi
  simp only [dot, Prod.fst_neg, Prod.snd_neg] at h1 hdot ⊢
  linarith

/-- **The `ℓ`-parallel face of `Â_∞` is infinite** (`:506`, first sentence, the `ℓ` edge).
`dot_surjective` (`LatticeEdges.lean:1845`) puts one point `p₀` at height `cz`; `:498` puts
every `p₀ - s v⃗_ℓ` into some `A i`; `hAhat` then puts `p₀ - (s + k_i) v⃗_ℓ` into `Â_i`.
That set of offsets is unbounded above, hence infinite, and injects into the face. -/
theorem face_neg_nl_infinite
    {A Ahat : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ} {nl vl : ℤ × ℤ} {cz : ℤ}
    (hprim : Prim nl)
    (hAhat : ∀ i, Ahat i = {z | z + (kk i : ℤ) • vl ∈ A i})
    (hexh : Nivat.Colle35.Exhausts A nl cz) (hperp : dot nl vl = 0) (hvl : vl ≠ 0) :
    (face (⋃ i, Ahat i) (-nl)).Infinite := by
  obtain ⟨p₀, hp₀⟩ := LE2.dot_surjective hprim cz
  have hline : ∀ t : ℤ, dot nl (p₀ - t • vl) = cz := by
    intro t
    rw [Nivat.Colle35.dot_sub_zsmul_of_perp hperp]
    exact hp₀
  have hcof : ∀ s : ℕ, ∃ t : ℤ, (p₀ - t • vl ∈ (⋃ i, Ahat i)) ∧ (s : ℤ) ≤ t := by
    intro s
    have hmem : p₀ - (s : ℤ) • vl ∈ (⋃ j, A j) := by
      rw [hexh]; exact le_of_eq (hline (s : ℤ)).symm
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hmem
    refine ⟨(s : ℤ) + (kk i : ℤ), Set.mem_iUnion.mpr ⟨i, ?_⟩, by omega⟩
    rw [hAhat i]
    have hsum : p₀ - ((s : ℤ) + (kk i : ℤ)) • vl + (kk i : ℤ) • vl = p₀ - (s : ℤ) • vl := by
      refine Prod.ext ?_ ?_ <;>
        simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
          Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ring
    simpa only [Set.mem_setOf_eq, hsum] using hi
  set T : Set ℤ := {t : ℤ | p₀ - t • vl ∈ (⋃ i, Ahat i)} with hTdef
  have hTinf : T.Infinite := by
    intro hfin
    obtain ⟨M, hM⟩ := hfin.bddAbove
    obtain ⟨t, htT, hts⟩ := hcof (M.toNat + 1)
    have hle : t ≤ M := hM (show t ∈ T from htT)
    omega
  have hinjOn : Set.InjOn (fun t : ℤ => p₀ - t • vl) T := by
    intro a _ b _ hab
    exact zsmul_left_cancel_of_ne_zero hvl (sub_right_inj.mp hab)
  have himg : ((fun t : ℤ => p₀ - t • vl) '' T).Infinite := hTinf.image hinjOn
  intro hfin
  refine himg (hfin.subset ?_)
  rintro z ⟨t, htT, rfl⟩
  exact mem_face_neg_nl_of_dot_eq hAhat hexh hperp htT (hline t)

/-! ## §3 The `ℓ_J` side: `ν_J ∈ E Â_∞`

原文 `b3_colle2.txt:506`: "… the other one is parallel to `ℓ_J`".  The mechanism is `:488`'s
fixed vertex `g₁` plus `:504`'s layerwise-constant intermediate edges, which pin the `ν_J`-edge's
start vertex `g_J` and hence the support value.  Each step of that chain is already on the tree
(`LeafAJSelect.exists_eventually_const_before`, `LeafAJSelect.exists_gJ_pinned_ccw`,
`ShellRegionJ.hhp_of_faceStart_pinned`, `ShellRegionJ.mem_E_of_ray_in_face`); the one missing
link is that `hhp_of_faceStart_pinned` only covers `i ≥ i₀` while `mem_E_of_ray_in_face` needs
maximality over the whole union.  `hmax_of_hhp_of_mono` is that link.
-/

/-- **`E_iUnion_eq_insert_arc`'s `hmax_J` binder** (`ShellRegionJ.lean:300`).  Upgrades
`ShellRegionJ.hhp_of_faceStart_pinned`'s per-layer half-plane bound (`i₀ ≤ i` only) to a bound
on the whole union: monotonicity absorbs the layers below `i₀` into `Â_{i₀}`.
`hmono` is discharged verbatim by `ChainData.AhatMono` (`Lemma35.lean:729`) — see the module
docstring for why the `AhatMono.lean` refutation does not make this vacuous. -/
theorem hmax_of_hhp_of_mono {Ahat : ℕ → Set (ℤ × ℤ)} (hmono : Monotone Ahat)
    {J gJ : ℤ × ℤ} {i₀ : ℕ}
    (hhp : ∀ i, i₀ ≤ i → Ahat i ⊆ LE2.halfPlaneGE (-J) (dot (-J) gJ)) :
    ∀ z ∈ (⋃ i, Ahat i), dot J z ≤ dot J gJ := by
  intro z hz
  obtain ⟨k, hzk⟩ := Set.mem_iUnion.mp hz
  have hzmax : z ∈ Ahat (max k i₀) := hmono (le_max_left k i₀) hzk
  have h2 : dot (-J) gJ ≤ dot (-J) z := hhp (max k i₀) (le_max_right k i₀) hzmax
  simp only [dot, Prod.fst_neg, Prod.snd_neg] at h2 ⊢
  linarith

/-- `g_J` pinned as a `faceStart` puts `g_J` itself in every layer past `i₀`
(`PolyChain.faceStart_mem`, `PolyChain.lean:75`) — so no separate membership binder is needed. -/
theorem gJ_mem_of_faceStart_pinned {Ahat : ℕ → Set (ℤ × ℤ)} {J gJ : ℤ × ℤ} {i₀ : ℕ}
    (hfin : ∀ i, (Ahat i).Finite)
    (hJmem : ∀ i, i₀ ≤ i → J ∈ E (Ahat i))
    (hgJ : ∀ i, i₀ ≤ i → Nivat.PolyChain.faceStart (Ahat i) J = gJ) :
    ∀ i, i₀ ≤ i → gJ ∈ Ahat i := by
  intro i hi
  have h := Nivat.PolyChain.faceStart_mem (hfin i) (hJmem i hi)
  rw [hgJ i hi] at h
  exact h.1

/-- **`ν_J ∈ E Â_∞`** (`:506`, the `ℓ_J`-parallel edge, membership half).  `hgJ` is
`LeafAJSelect.exists_gJ_pinned_ccw`'s conclusion shape; `hray` is the `ℓ_J`-direction ray in the
union (the same binder `Colle41.RayIn` supplies, `Lemma41.lean:675`); the two witnesses
`k = 0, 1` are what make the face nontrivial.
`hmono` is discharged verbatim by `ChainData.AhatMono` (`Lemma35.lean:729`) — see the module
docstring for why the `AhatMono.lean` refutation does not make this vacuous. -/
theorem mem_E_iUnion_of_faceStart_pinned {Ahat : ℕ → Set (ℤ × ℤ)} (hmono : Monotone Ahat)
    {J gJ : ℤ × ℤ} {i₀ : ℕ} (hprim : Prim J)
    (hfin : ∀ i, (Ahat i).Finite) (hne : ∀ i, (Ahat i).Nonempty)
    (hlc : ∀ i, IsLatticeConvexRegion (Ahat i))
    (hJmem : ∀ i, i₀ ≤ i → J ∈ E (Ahat i))
    (hgJ : ∀ i, i₀ ≤ i → Nivat.PolyChain.faceStart (Ahat i) J = gJ)
    (hray : ∀ k : ℕ, gJ + (k : ℤ) • dir J ∈ ⋃ i, Ahat i) :
    J ∈ E (⋃ i, Ahat i) := by
  have hJne : J ≠ (0 : ℤ × ℤ) := fun h => by simp [Prim, h] at hprim
  have hmax := hmax_of_hhp_of_mono hmono
    (Nivat.ShellRegionJ.hhp_of_faceStart_pinned hfin hne hlc hJmem hgJ)
  refine Nivat.ShellRegionJ.mem_E_of_ray_in_face hprim (dot_dir J)
    (Nivat.PolyChainSum.dir_ne_zero hJne) hmax ?_ ?_
  · simpa using hray 0
  · simpa using hray 1

end Nivat.AhatLimitEdge

#print axioms Nivat.AhatLimitEdge.ahat_subset_halfplane
#print axioms Nivat.AhatLimitEdge.hmax_neg_nl
#print axioms Nivat.AhatLimitEdge.zsmul_left_cancel_of_ne_zero
#print axioms Nivat.AhatLimitEdge.mem_face_neg_nl_of_dot_eq
#print axioms Nivat.AhatLimitEdge.face_neg_nl_infinite
#print axioms Nivat.AhatLimitEdge.hmax_of_hhp_of_mono
#print axioms Nivat.AhatLimitEdge.gJ_mem_of_faceStart_pinned
#print axioms Nivat.AhatLimitEdge.mem_E_iUnion_of_faceStart_pinned
