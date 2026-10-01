/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.PolyChain
import Nivat.External.Colle.PolyChainSum
import Nivat.External.Colle.TowerEHelp
import Nivat.External.Colle.AGlue
import Nivat.External.Colle.CyrKra224

/-!
# `:506` region/face structure, abstract layer (lane-shell, 2026-09-22)

Team-lead's ruling (`blueprint/LEAF-A.md`, "hsweepW 从扇邻接算出来"): the fan `E ↑Sφ` is
already pinned to `{±genPerp'(h j)}` (`Nivat.LE2.E_zonoF_eq_genPerp_set`,
`TowerEHelp.lean:31`), cyclically ordered by `det`, and `ν_{J+1}` is the `Arc`-successor of
`J` in that fan (`Nivat.PolyChainSum.Arc hfin J ν_{J+1} = ∅`, same adjacency notion as
`adjacent_shared_vertex`, `PolyChain.lean:245`). This file lands the first piece consumable
by `ofPartsInter`'s `hsweepW : dot nJ w < 0` binder (`ChainAssembleInter.lean:41`), taking
`nJ := -J` and `w := -dir ν_{J+1}` (Collé's `-v_{ℓ_{J+1}}`, `:512`).

**Status**: this is pure fan algebra (`0 < det J ν_{J+1}` ⟹ `dot (-J) (-dir ν_{J+1}) < 0`),
not yet the full `(ℓ, ℓ_J)`-region face structure (part (1) of the `:506` task). That part is
still blocked on real `g₁`/`g_J`/`hgrow` binders from lane-recp's J-package (see `LEAF-A.md`,
"ShellRegion：已有的射线机器" and the follow-up status messages) — no faithful `J > ι+1`
numeric instance exists yet to test the face-structure statements against, so they are not
attempted here. This file only contains what is provable from the fan-adjacency algebra alone.
-/

set_option autoImplicit false

namespace Nivat.ShellRegionJ

open Nivat Nivat.LE2 Nivat.PolyChain Nivat.PolyChainSum

/-- **`hsweepW` from fan adjacency.** If `J` and `ν_{J+1}` are consecutive edge normals in a
fan (in the sense that `0 < det J ν_{J+1}`, which is exactly what `Arc hfin J ν_{J+1} = ∅`
supplies via `mem_Arc`), then taking `nJ := -J` and `w := -dir ν_{J+1}` (Collé's
`-v_{ℓ_{J+1}}`) gives the sign condition `ofPartsInter`'s `hsweepW` binder needs. The
`nJ := -J` choice (rather than `nJ := J`) is forced: `J` itself is an *outward* edge normal of
the region (`dot J z ≤ suppVal` on the region), while `hhp : Ahat i ⊆ halfPlaneGE nJ cJ`
needs the *inward* convention `dot nJ z ≥ cJ`, so `nJ` must be the negation of `J` — the same
"take the negative" pattern already used for `hnE` elsewhere in the project. -/
theorem hsweepW_of_fan_adjacent (J νJ1 : ℤ × ℤ) (hpos : 0 < det J νJ1) :
    dot (-J) (-(dir νJ1)) < 0 := by
  have h1 : dot (-J) (-(dir νJ1)) = dot J (dir νJ1) := by
    rw [dot_neg_left, dot_neg_right, neg_neg]
  have h2 : dot J (dir νJ1) = det νJ1 J := dot_dir_right νJ1 J
  have h3 : det νJ1 J = -det J νJ1 := by rw [det_skew]
  rw [h1, h2, h3]
  omega

/-- Same statement, phrased with the `Arc`-adjacency hypothesis directly (the shape team-lead's
ruling names as the binder: `ν_{J+1}` is the unique fan element with no element of `E T`
strictly between it and `J`). `hJ_adj` here is not itself consumed by the algebra (only
`0 < det J ν_{J+1}`, which `mem_Arc` extracts from `hAcc`, is) — it is carried as a binder so
this theorem's signature matches what a real `J`-package will hand over: `ν_{J+1} ∈ E T` with
`Arc hfin J ν_{J+1} = ∅` and `0 < det J ν_{J+1}` together pin down "the next edge after `J`". -/
theorem hsweepW_of_arc_empty {T : Set (ℤ × ℤ)} (hfin : T.Finite) {J νJ1 : ℤ × ℤ}
    (_hJ : J ∈ E T) (_hνJ1 : νJ1 ∈ E T) (hpos : 0 < det J νJ1)
    (_hJ_adj : Arc hfin J νJ1 = ∅) :
    dot (-J) (-(dir νJ1)) < 0 :=
  hsweepW_of_fan_adjacent J νJ1 hpos

/-- **`hhp` from `g_J`-pinning (team-lead's `:506` task, part (a)).** Once `faceStart (Ahat i) J`
has stabilised at `g_J` (lane-recp's `exists_gJ_pinned_ccw` conclusion, `LEAF-A.md:3578`,
literal shape: `∀ i ≥ i₀, faceStart (Ahat i) J = g_J`), every `z ∈ Ahat i` (for those same `i`)
lies in the `nJ`-halfplane through `g_J`, with `nJ := -J` and `cJ := dot nJ g_J = dot (-J) g_J`
— exactly `ofPartsInter`'s `hhp` binder (pre-reindexing; the `∀ i` in that binder is recovered
after shifting by `i₀`, same pattern as the `escapeW`/`shellEnv` `i₀`-absorption team-lead ruled
on earlier). Proof: `dot J z ≤ suppVal (Ahat i) J` (`le_suppVal`, any `z ∈ Ahat i`) `= dot J
g_J` (`suppVal_faceStart` + the pinning hypothesis); negate. -/
theorem hhp_of_faceStart_pinned {Ahat : ℕ → Set (ℤ × ℤ)} {J gJ : ℤ × ℤ} {i₀ : ℕ}
    (hfin : ∀ i, (Ahat i).Finite) (hne : ∀ i, (Ahat i).Nonempty)
    (hlc : ∀ i, IsLatticeConvexRegion (Ahat i))
    (hJmem : ∀ i, i₀ ≤ i → J ∈ E (Ahat i))
    (hgJ : ∀ i, i₀ ≤ i → faceStart (Ahat i) J = gJ) :
    ∀ i, i₀ ≤ i → Ahat i ⊆ halfPlaneGE (-J) (dot (-J) gJ) := by
  intro i hi z hz
  have hle : dot J z ≤ suppVal (Ahat i) J := le_suppVal (hfin i) (hne i) hz
  have hseg : ∀ ν ∈ E (Ahat i), face (Ahat i) ν =
      {w | ∃ t : ℕ, t ≤ faceLen (Ahat i) ν ∧ w = faceStart (Ahat i) ν + (t : ℤ) • dir ν} :=
    fun ν hν => face_eq_segment (hlc i) (hfin i) hν
  have hsupp : suppVal (Ahat i) J = dot J gJ := by
    rw [suppVal_faceStart hseg (hJmem i hi), hgJ i hi]
  show dot (-J) gJ ≤ dot (-J) z
  rw [dot_neg_left, dot_neg_left]
  rw [hsupp] at hle
  omega

/-- **Face of the union stabilises where the finite pieces do.** Team-lead's `:506` task part
(c): `face (⋃ Ahat) ν` for `ν` in the fixed chain equals the stabilised finite face. Needs only
`Monotone Ahat` and the eventually-constant-face hypothesis `hstab` (the set-level packaging of
"`faceLen`/`faceStart` eventually constant") — no finiteness/enveloped hypotheses at all,
because `face` is defined directly as the pointwise argmax condition (`LatticeEdges.lean:160`),
not via `suppVal`. Both directions of the `Set.ext` use the same trick: a point `z` of one face
is tested against `Ahat j` for a specific `j`, splitting on `j ≤ i₀` (use `hmono`) vs `i₀ ≤ j`
(use `hstab`) to transport membership/maximality between `Ahat j`, `Ahat i₀`, and the union. -/
theorem face_iUnion_of_stabilizes {Ahat : ℕ → Set (ℤ × ℤ)} (hmono : Monotone Ahat)
    {ν : ℤ × ℤ} {i₀ : ℕ} (hstab : ∀ j, i₀ ≤ j → face (Ahat j) ν = face (Ahat i₀) ν) :
    face (⋃ i, Ahat i) ν = face (Ahat i₀) ν := by
  ext z
  constructor
  · rintro ⟨hzmem, hzmax⟩
    obtain ⟨k, hzk⟩ := Set.mem_iUnion.mp hzmem
    have hzmax' : ∀ i, ∀ y ∈ Ahat i, dot ν y ≤ dot ν z := fun i y hy =>
      hzmax y (Set.mem_iUnion.mpr ⟨i, hy⟩)
    rcases Nat.lt_or_ge i₀ k with hk | hk
    · have hzfacek : z ∈ face (Ahat k) ν := ⟨hzk, hzmax' k⟩
      rw [hstab k hk.le] at hzfacek
      exact hzfacek
    · exact ⟨hmono hk hzk, hzmax' i₀⟩
  · rintro ⟨hzmem, hzmax⟩
    refine ⟨Set.mem_iUnion.mpr ⟨i₀, hzmem⟩, ?_⟩
    intro y hy
    obtain ⟨j, hyj⟩ := Set.mem_iUnion.mp hy
    rcases Nat.lt_or_ge j i₀ with hj | hj
    · exact hzmax y (hmono hj.le hyj)
    · have hzfacej : z ∈ face (Ahat j) ν := by rw [hstab j hj]; exact ⟨hzmem, hzmax⟩
      exact hzfacej.2 y hyj

/-- **σ-reindexing doesn't change the union** (lane-recp's flag, 2026-09-22: the real
`exists_gJ_pinned_ccw`/`_cw` conclusions stabilise along a subsequence `Ahat ∘ σ`, not the raw
index). This is the fact that makes `hhp_of_faceStart_pinned`/`face_iUnion_of_stabilizes`
directly reusable with **no change to their statements**: apply them to `Ahat ∘ σ` in place of
`Ahat`, and this lemma identifies `⋃ i, Ahat (σ i)` with the real target `⋃ i, Ahat i` — same
`i₀`-absorption-by-reindexing pattern team-lead already ruled on for `escapeW`. -/
theorem iUnion_comp_strictMono_eq {Ahat : ℕ → Set (ℤ × ℤ)} (hmono : Monotone Ahat)
    {σ : ℕ → ℕ} (hσ : StrictMono σ) :
    (⋃ i, Ahat (σ i)) = ⋃ i, Ahat i := by
  refine Set.Subset.antisymm (Set.iUnion_subset fun i => Set.subset_iUnion Ahat (σ i)) ?_
  refine Set.iUnion_subset fun n z hz => ?_
  exact Set.mem_iUnion.mpr ⟨n, hmono (hσ.le_apply) hz⟩

/-- **A normal with a diverging ray in `T` has empty face** (task `:506` part (b), the `⊆`
direction of `E (⋃ Ahat)`, `LEAF-A.md` "task (3) part (b)" 追加note). `IsEdge`/`E`
(`LatticeEdges.lean:214`) only needs `(face T n).Nontrivial`, not boundedness — so the
semi-infinite `ℓ`/`ℓ_J` rays themselves stay edges for free (⊇ direction, no lemma needed
beyond exhibiting two ray points). This lemma is the ⊆ direction's one piece of content: if
`dot n` is unbounded above along *some* ray inside `T` (any `g`, `d` with `dot n d > 0` and
the whole ray `g + k•d ⊆ T`), no point of `T` can be a `dot n`-maximiser, so `face T n = ∅`
and `n ∉ E T`. -/
theorem face_eq_empty_of_ray_unbounded {T : Set (ℤ × ℤ)} {n g d : ℤ × ℤ}
    (hray : ∀ k : ℕ, g + (k : ℤ) • d ∈ T) (hpos : 0 < dot n d) :
    face T n = ∅ := by
  ext z
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨-, hmax⟩
  set k : ℕ := (dot n z - dot n g).toNat + 1 with hk_def
  have hyT : g + (k : ℤ) • d ∈ T := hray k
  have hdot : dot n (g + (k : ℤ) • d) = dot n g + (k : ℤ) * dot n d := by
    rw [dot_add, dot_zsmul_right]
  have hkpos : (1 : ℤ) ≤ (k : ℤ) := by
    have : (0 : ℤ) ≤ (dot n z - dot n g).toNat := Int.natCast_nonneg _
    omega
  have hstep : dot n g + (k : ℤ) * dot n d > dot n z := by
    have hk_gt : (k : ℤ) > dot n z - dot n g := by
      have := Int.toNat_le.mp (le_refl (dot n z - dot n g).toNat)
      omega
    nlinarith
  have := hmax _ hyT
  rw [hdot] at this
  omega

theorem not_mem_E_of_ray_unbounded {T : Set (ℤ × ℤ)} {n g d : ℤ × ℤ}
    (hray : ∀ k : ℕ, g + (k : ℤ) • d ∈ T) (hpos : 0 < dot n d) :
    n ∉ E T := by
  rw [mem_E_iff, face_eq_empty_of_ray_unbounded hray hpos]
  simp

/-- **Dispatch, `J`-side of the complementary arc.** A normal strictly past `J` (ccw) is not an
edge of `T∞`: the `vJ := dir J`-ray from `g_J` (`ray_of_pinned_growth`, `ItemII.lean:786`)
already makes `dot ν` unbounded there. -/
theorem not_mem_E_of_det_J_pos {T : Set (ℤ × ℤ)} {J ν g_J vJ : ℤ × ℤ}
    (hvJ : vJ = dir J) (hray : ∀ k : ℕ, g_J + (k : ℤ) • vJ ∈ T) (hpos : 0 < det J ν) :
    ν ∉ E T := by
  apply not_mem_E_of_ray_unbounded hray
  rw [hvJ, dot_dir_right]
  exact hpos

/-- **Dispatch, `ν₀`-side of the complementary arc.** A normal strictly before `ν₀` (ccw,
wrapping back) is not an edge of `T∞`: the `ℓ`-ray from `g₁` grows in the `-dir ν₀` direction
(`g₁` is the *far* end of the `ℓ`-face, pinned; the near end recedes as `i → ∞`), and that ray
already makes `dot ν` unbounded there. -/
theorem not_mem_E_of_det_ν₀_pos {T : Set (ℤ × ℤ)} {ν₀ ν g₁ d : ℤ × ℤ}
    (hd : d = -dir ν₀) (hray : ∀ k : ℕ, g₁ + (k : ℤ) • d ∈ T) (hpos : 0 < det ν ν₀) :
    ν ∉ E T := by
  apply not_mem_E_of_ray_unbounded hray
  have hdd : dot ν d = det ν ν₀ := by
    subst hd
    simp only [dot, dir, det, Prod.fst_neg, Prod.snd_neg]
    ring
  rw [hdd]
  exact hpos

/-- **A pinned ray with zero pairing stays in the face — the `⊇` direction's edge-membership
lemma.** Companion to `not_mem_E_of_ray_unbounded`: there, `dot n d > 0` along a ray forces
`n ∉ E T`; here, `dot n d = 0` along a ray whose base point `g` already maximises `dot n` on
`T` forces `n ∈ E T`, because every ray point ties `g`'s pairing (so the whole ray sits inside
`face T n`, which is then `Nontrivial` since `d ≠ 0`). This is exactly what `ν₀`/`J`
themselves need to land in `E (⋃ Ahat)`: take `g := g₁`/`g_J` (the pinned point) and `d :=
-dir ν₀`/`dir J` (`dot_dir`/`dot_neg_right`+`dot_dir` give the zero pairing for free), reusing
the same ray hypotheses `not_mem_E_of_det_ν₀_pos`/`not_mem_E_of_det_J_pos` already consume. -/
theorem mem_E_of_ray_in_face {T : Set (ℤ × ℤ)} {n g d : ℤ × ℤ}
    (hprim : Prim n) (hd0 : dot n d = 0) (hdne : d ≠ 0)
    (hmax : ∀ z ∈ T, dot n z ≤ dot n g) (hgT : g ∈ T)
    (hray1 : g + (1 : ℤ) • d ∈ T) :
    n ∈ E T := by
  rw [mem_E_iff]
  refine ⟨hprim, ?_⟩
  have hdotgd : dot n (g + (1 : ℤ) • d) = dot n g := by
    rw [dot_add, dot_zsmul_right, hd0]; ring
  have hgface : g ∈ face T n := ⟨hgT, hmax⟩
  have hgdface : g + (1 : ℤ) • d ∈ face T n := by
    refine ⟨hray1, ?_⟩
    intro y hy
    rw [hdotgd]
    exact hmax y hy
  refine ⟨g, hgface, g + (1 : ℤ) • d, hgdface, ?_⟩
  intro hcontra
  apply hdne
  have hfst : g.1 = g.1 + d.1 := by
    have := congrArg Prod.fst hcontra
    simpa [one_smul] using this
  have hsnd : g.2 = g.2 + d.2 := by
    have := congrArg Prod.snd hcontra
    simpa [one_smul] using this
  have hd1 : d.1 = 0 := by omega
  have hd2 : d.2 = 0 := by omega
  exact Prod.ext hd1 hd2

/-- **Complementary-arc dichotomy.** If `ν` is not parallel to `ν₀` and not parallel to `J`
(the generic case: `det ν₀ ν ≠ 0`, `det ν J ≠ 0`), and `ν` is not strictly between `ν₀` and
`J` in the ccw sense (`¬(0 < det ν₀ ν ∧ 0 < det ν J)`, i.e. `ν ∉ Arc hfin ν₀ J`), then `ν`
falls on one of the two dispatch sides: either `0 < det J ν` (feeds
`not_mem_E_of_det_J_pos`) or `0 < det ν ν₀` (feeds `not_mem_E_of_det_ν₀_pos`). Pure sign
bookkeeping via `det_skew`, no cyclic-order machinery needed: failing the ccw-betweenness
conjunction forces one conjunct false, and antisymmetry flips a `< 0` fact on one side into
a `> 0` fact on the dispatch side. **Caveat (does not cover the antipodal case):** this
needs `ν ≠ -ν₀` and `ν ≠ J` up to sign, i.e. `det ν₀ ν ≠ 0`/`det ν J ≠ 0` as hypotheses —
if `ν` is antiparallel to `ν₀` or `J` (`Sφ` being a zonotope, `E Sφ` can contain antipodal
pairs), those hypotheses fail and this lemma says nothing; that case needs a separate
argument from `T`'s actual boundedness shape, not general position. -/
theorem det_J_or_det_ν₀_pos_of_not_mem_arc {ν₀ J ν : ℤ × ℤ}
    (hν₀ν : det ν₀ ν ≠ 0) (hνJ : det ν J ≠ 0)
    (hnot : ¬ (0 < det ν₀ ν ∧ 0 < det ν J)) :
    0 < det J ν ∨ 0 < det ν ν₀ := by
  rcases lt_or_gt_of_ne hν₀ν with h1 | h1
  · right
    have hskew : det ν ν₀ = -det ν₀ ν := det_skew ν ν₀
    omega
  · rcases lt_or_gt_of_ne hνJ with h2 | h2
    · left
      have hskew : det J ν = -det ν J := det_skew J ν
      omega
    · exact absurd ⟨h1, h2⟩ hnot

/-- **Antipodal gap, `ν₀`-side.** `nℓ = -ν₀` is not an edge of `T∞`: the `J`-ray from `g_J`
already makes `dot nℓ` unbounded there, since `dot nℓ (dir J) = det ν₀ J > 0` (team-lead's
closure, `LEAF-A.md` 第二十一轮: `J ≠ ±ν₀` gives the strict sign via the standing `0 < det ν₀
J` hypothesis, not a fresh ambient argument). One-liner on top of `not_mem_E_of_ray_unbounded`,
reusing exactly the `J`-ray hypothesis `not_mem_E_of_det_J_pos` already consumes. -/
theorem not_mem_E_of_neg_ν₀ {T : Set (ℤ × ℤ)} {ν₀ J g_J : ℤ × ℤ}
    (hray : ∀ k : ℕ, g_J + (k : ℤ) • dir J ∈ T) (hν₀J : 0 < det ν₀ J) :
    (-ν₀) ∉ E T := by
  apply not_mem_E_of_ray_unbounded hray
  have h1 : dot (-ν₀) (dir J) = -dot ν₀ (dir J) := dot_neg_left ν₀ (dir J)
  have h2 : dot ν₀ (dir J) = det J ν₀ := dot_dir_right J ν₀
  have h3 : det J ν₀ = -det ν₀ J := det_skew J ν₀
  rw [h1, h2, h3]
  omega

/-- **Antipodal gap, `J`-side.** `-J` is not an edge of `T∞`: the `ℓ`-ray from `g₁` (direction
`-dir ν₀`, same ray `not_mem_E_of_det_ν₀_pos` consumes) already makes `dot (-J)` unbounded
there, since `dot (-J) (-dir ν₀) = det ν₀ J > 0` by the same standing hypothesis. -/
theorem not_mem_E_of_neg_J {T : Set (ℤ × ℤ)} {ν₀ J g₁ : ℤ × ℤ}
    (hray : ∀ k : ℕ, g₁ + (k : ℤ) • (-(dir ν₀)) ∈ T) (hν₀J : 0 < det ν₀ J) :
    (-J) ∉ E T := by
  apply not_mem_E_of_ray_unbounded hray
  have h1 : dot (-J) (-(dir ν₀)) = dot J (dir ν₀) := by
    rw [dot_neg_left, dot_neg_right, neg_neg]
  have h2 : dot J (dir ν₀) = det ν₀ J := dot_dir_right ν₀ J
  rw [h1, h2]
  exact hν₀J

/-- **Full edge-set assembly, `:506` part (b).** `E (⋃ Ahat) = {ν₀, J} ∪ Arc hfin ν₀ J`.
Consumer-facing binders: `hEeq` bridges `E (⋃ Ahat)` to the fixed finite `E T` (Enveloped
argument, lane-recp's `Arc_eq_of_enveloped`/`AhatEnv.E_eq_of_enveloped`); `hν₀J` is the
standing "`J` really is past `ν₀`, ccw" fact; the two ray/maximality pairs are exactly
`hgrow_of_pinned_ccw`/`_cw`'s shape plus an `hhp`-style bound at `ν₀`/`J` themselves
(supplied by whoever pins `g₁`/`g_J`, not re-derived here — this file only assembles).

**Producers for the two maximality binders** (lane-leafa-shell, 2026-09-24):
`hmax_ν₀` ← `AhatLimitEdge.hmax_neg_nl` (at `ν₀ = -nℓ`), `hmax_J` ←
`AhatLimitEdge.hmax_of_hhp_of_mono`.  They are *not* imported here — `AhatLimitEdge` imports
**this** file (it uses `hhp_of_faceStart_pinned` and `mem_E_of_ray_in_face`), so the dependency
runs one way only; call sites of `E_iUnion_eq_insert_arc` are where the two meet.
⚠ `hmax_of_hhp_of_mono` carries `Monotone Ahat`.  That is a *field* of `ChainData`
(`ChainData.AhatMono`, `Lemma35.lean:729`), stated on the same raw index on which `Â_∞` is
formed, so call sites holding a `ChainData` discharge it verbatim; what `AhatMono.lean:43`
refutes is only that `:486-500` *supplies* it.  (An earlier revision of this paragraph said
the raw indexing makes it vacuous — withdrawn 2026-09-24, over-strong.)

⛔⛔ **PARKED IN PLACE（第 193 轮，集成者裁）。本条无消费者，且其 `hEeq` 前提不可兑现。**

1. **无落点**：`ChainData`（`Lemma35.lean:696-830`）/ `ChainDataWithShell`（`ChainShell.lean:49`）/
   `ChainDataGeom`（`ChainGeom.lean:67`）三层字段体扫 `E (` / `IsEdge` / `IsSemiInfEdge`，
   **命中 0**；洞 1 目标（`RegionSteps.lean` `exists_chainData`）的三个合取项也都不含边集。
   全树调用点 0（`AhatLimitEdge.lean` 的提及全在 docstring 表格里，不是代码）。
2. **前提不可兑现**：`hEeq` 要的是**强** `Enveloped`（弱 ＋ `|E 𝒯| = |E 𝒰|`），而原文
   `scratch/b3_colle2.txt:402`（弱包络的**定义**处；`:506` 只是用词现场）逐字只给**弱**。
   基数条款在并集上必假——数值反例：`S_φ = {0,1}²`（`E ↑S_φ` 四条法向）对第一象限 `Â_∞`
   （`E Â_∞` 两条），弱包络成立、基数 2 ≠ 4。
   内核见证 `hEeq_false`（`tmp/wip/lane-leafa-shell-heeq-refute.lean:211`，
   `E (⋃ i, boxFam i) ≠ E ↑winSq`）与 `conclusion_holds`（同文件 `:243`）——
   ⚠ 二者在 `tmp/wip/`，**不在主仓、不在 build 里**，引用时按「链外收据」对待，不算「已有」。
   ⟹ 结论收窄为：`hEeq` 在**现签名**下接不通；换签名（只要弱包络）是另一件事，未判。
3. **`:506` 在包里的真正对应物**是六个「后退方向＋支撑值」字段：`rec_vJ`（`ChainGeom.lean:163`）/
   `rec_p`（`:136`）/ `ahat_halfPlane`（`ChainShell.lean:63`）/ `ahat_nonempty`（`:61`）/
   `ahat_halfPlane_L`（`ChainGeom.lean:180`）/ `ahat_attained_L`（`:185`）。**谁要接 `:506`，打这六个，不要打本条。**

证据来源：lane-leafa-shell（机器扫字段体 ＋ `hEeq` 数值反例）与 lane-hole3-cone（独立查调用点
＋ 目标形状），两条独立路径收敛。⚠ 不移文件：本条 0 `sorry`、公理全白、与同文件其余 17 条共享
`not_mem_E_of_*` 等辅助引理，搬走要连带切除并有破坏绿树的风险；硬规矩 22 针对的是**带 `sorry`**
的无消费者文件，本条不属于。就地封存即可。 -/
theorem E_iUnion_eq_insert_arc {Ahat : ℕ → Set (ℤ × ℤ)} {T : Set (ℤ × ℤ)} (hTfin : T.Finite)
    {ν₀ J g₁ g_J : ℤ × ℤ}
    (hEeq : E (⋃ i, Ahat i) = E T)
    (hν₀J : 0 < det ν₀ J)
    (hprim_ν₀ : Prim ν₀) (hprim_J : Prim J)
    (hray_ν₀ : ∀ k : ℕ, g₁ + (k : ℤ) • (-(dir ν₀)) ∈ ⋃ i, Ahat i)
    (hmax_ν₀ : ∀ z ∈ ⋃ i, Ahat i, dot ν₀ z ≤ dot ν₀ g₁)
    (hg₁mem : g₁ ∈ ⋃ i, Ahat i)
    (hray_J : ∀ k : ℕ, g_J + (k : ℤ) • dir J ∈ ⋃ i, Ahat i)
    (hmax_J : ∀ z ∈ ⋃ i, Ahat i, dot J z ≤ dot J g_J)
    (hgJmem : g_J ∈ ⋃ i, Ahat i) :
    E (⋃ i, Ahat i) = insert ν₀ (insert J (↑(Arc hTfin ν₀ J) : Set (ℤ × ℤ))) := by
  have hν₀_ne : ν₀ ≠ (0 : ℤ × ℤ) := fun h => by
    simp [Prim, h] at hprim_ν₀
  have hJ_ne : J ≠ (0 : ℤ × ℤ) := fun h => by
    simp [Prim, h] at hprim_J
  ext ν
  simp only [Set.mem_insert_iff, Finset.mem_coe]
  constructor
  · intro hνU
    have hνT : ν ∈ E T := hEeq ▸ hνU
    have hprim_ν : Prim ν := (mem_E_iff.mp hνT).1
    by_cases hcase1 : det ν₀ ν = 0
    · rcases eq_or_neg_of_prim_of_det_eq_zero hprim_ν₀ hprim_ν hcase1 with heq | heq
      · exact Or.inl heq
      · exact absurd (heq ▸ hνU) (not_mem_E_of_neg_ν₀ hray_J hν₀J)
    · by_cases hcase2 : det ν J = 0
      · have hcase2' : det J ν = 0 := by
          have := det_skew J ν
          omega
        rcases eq_or_neg_of_prim_of_det_eq_zero hprim_J hprim_ν hcase2' with heq | heq
        · exact Or.inr (Or.inl heq)
        · exact absurd (heq ▸ hνU) (not_mem_E_of_neg_J hray_ν₀ hν₀J)
      · refine Or.inr (Or.inr (mem_Arc.mpr ⟨hνT, ?_⟩))
        by_contra hnot
        rcases det_J_or_det_ν₀_pos_of_not_mem_arc hcase1 hcase2 hnot with hpos | hpos
        · exact absurd hνU (not_mem_E_of_det_J_pos rfl hray_J hpos)
        · exact absurd hνU (not_mem_E_of_det_ν₀_pos rfl hray_ν₀ hpos)
  · rintro (heq | heq | hArc)
    · rw [heq]
      exact mem_E_of_ray_in_face hprim_ν₀ (by rw [dot_neg_right, dot_dir]; ring)
        (neg_ne_zero.mpr (dir_ne_zero hν₀_ne)) hmax_ν₀ hg₁mem (by simpa using hray_ν₀ 1)
    · rw [heq]
      exact mem_E_of_ray_in_face hprim_J (dot_dir J) (dir_ne_zero hJ_ne) hmax_J hgJmem
        (by simpa using hray_J 1)
    · exact hEeq ▸ (mem_Arc.mp hArc).1

/-- **`hsweep` from fan adjacency, `ℓ`-side (team-lead's ruling, `vJ1 := v_{ℓ_{J−1}}`).**
Mirror of `hsweepW_of_fan_adjacent`, but for the fan edge *before* `J` rather than after:
`vJ1 := dir νJm1` where `νJm1` is `J`'s ccw predecessor (`0 < det νJm1 J`). No double
negation needed here (unlike the `+1` side) because the orientation is already right:
`dot (-J) (dir νJm1) = -det νJm1 J < 0` directly. -/
theorem hsweep_of_fan_adjacent (J νJm1 : ℤ × ℤ) (hpos : 0 < det νJm1 J) :
    dot (-J) (dir νJm1) < 0 := by
  have h1 : dot (-J) (dir νJm1) = -dot J (dir νJm1) := dot_neg_left J (dir νJm1)
  have h2 : dot J (dir νJm1) = det νJm1 J := dot_dir_right νJm1 J
  rw [h1, h2]
  omega

/-- Same statement, phrased with the `Arc`-adjacency hypothesis directly (companion to
`hsweepW_of_arc_empty`). -/
theorem hsweep_of_arc_empty {T : Set (ℤ × ℤ)} (hfin : T.Finite) {J νJm1 : ℤ × ℤ}
    (_hJ : J ∈ E T) (_hνJm1 : νJm1 ∈ E T) (hpos : 0 < det νJm1 J)
    (_hJm1_adj : Arc hfin νJm1 J = ∅) :
    dot (-J) (dir νJm1) < 0 :=
  hsweep_of_fan_adjacent J νJm1 hpos

/-- **Arc edges survive into the union — the last piece of `:506` part (b) `⊇`.**
Team-lead's ruling: for `μ` strictly between `ν₀` and `J` (in the fixed fan), the finite
face `face (Ahat (σ i)) μ` is eventually constant once BOTH `faceLen` and `faceStart`
stabilise along the reindexed chain (`faceLen` via lane-recp's `exists_eventually_const_before`
+ pigeonhole; `faceStart` via `chain_ccw_final`, since it is a sum of already-frozen
`faceLen`s of earlier arc edges plus the pinned `g₁` — assembled by the consumer, not
re-derived here). Given both stabilisation facts, `face_eq_segment` makes the two finite
faces literally equal sets, `face_iUnion_of_stabilizes` transports this to the union, and
`faceLen ≥ 1` gives the two distinct points (`t = 0, 1`) needed for `Nontrivial`. -/
theorem mem_E_of_arc_stabilizes {Ahat : ℕ → Set (ℤ × ℤ)} (hmono : Monotone Ahat)
    {σ : ℕ → ℕ} (hσ : StrictMono σ) {μ : ℤ × ℤ} {i₀ : ℕ}
    (hlc : ∀ i, IsLatticeConvexRegion (Ahat i)) (hfin : ∀ i, (Ahat i).Finite)
    (hμE : ∀ j, i₀ ≤ j → μ ∈ E (Ahat (σ j)))
    (hlen_stab : ∀ j, i₀ ≤ j →
      Nivat.PolyChain.faceLen (Ahat (σ j)) μ = Nivat.PolyChain.faceLen (Ahat (σ i₀)) μ)
    (hstart_stab : ∀ j, i₀ ≤ j →
      Nivat.PolyChain.faceStart (Ahat (σ j)) μ = Nivat.PolyChain.faceStart (Ahat (σ i₀)) μ)
    (hLpos : 1 ≤ Nivat.PolyChain.faceLen (Ahat (σ i₀)) μ) :
    μ ∈ E (⋃ i, Ahat i) := by
  have hμ0 : μ ∈ E (Ahat (σ i₀)) := hμE i₀ le_rfl
  have hprimμ : Prim μ := (mem_E_iff.mp hμ0).1
  have hmono' : Monotone (Ahat ∘ σ) := fun i j hij => hmono (hσ.monotone hij)
  have hface_stab : ∀ j, i₀ ≤ j → face ((Ahat ∘ σ) j) μ = face ((Ahat ∘ σ) i₀) μ := by
    intro j hj
    simp only [Function.comp_apply]
    rw [face_eq_segment (hlc (σ j)) (hfin (σ j)) (hμE j hj),
        face_eq_segment (hlc (σ i₀)) (hfin (σ i₀)) hμ0, hlen_stab j hj, hstart_stab j hj]
  have hstab := face_iUnion_of_stabilizes (Ahat := Ahat ∘ σ) hmono' hface_stab
  simp only [Function.comp_apply] at hstab
  have hunion_eq : (⋃ i, (Ahat ∘ σ) i) = ⋃ i, Ahat i := iUnion_comp_strictMono_eq hmono hσ
  simp only [Function.comp_apply] at hunion_eq
  rw [hunion_eq] at hstab
  rw [mem_E_iff]
  refine ⟨hprimμ, ?_⟩
  rw [hstab, face_eq_segment (hlc (σ i₀)) (hfin (σ i₀)) hμ0]
  refine ⟨Nivat.PolyChain.faceStart (Ahat (σ i₀)) μ, ⟨0, Nat.zero_le _, by simp⟩,
    Nivat.PolyChain.faceStart (Ahat (σ i₀)) μ + (1 : ℤ) • dir μ, ⟨1, hLpos, rfl⟩, ?_⟩
  have hdne : dir μ ≠ 0 := dir_ne_zero (fun h => by simp [Prim, h] at hprimμ)
  intro hcontra
  apply hdne
  have hfst : (dir μ).1 = 0 := by
    have h := congrArg Prod.fst hcontra
    simp only [Prod.fst_add, one_smul] at h
    omega
  have hsnd : (dir μ).2 = 0 := by
    have h := congrArg Prod.snd hcontra
    simp only [Prod.snd_add, one_smul] at h
    omega
  exact Prod.ext hfst hsnd

/-- **The sign fact needed to convert `LeafAShellRay`'s `vl`-ray into a `−dir ν₀`-ray**
(`ν₀ := −nℓ`, so `dir ν₀ = −dir nℓ`, and `dot nℓ vl = 0` with both `nℓ`, `vl` primitive forces
`dir nℓ = ± vl`). Two primitive vectors perpendicular to the same nonzero vector `nℓ` are `±`
each other (`Nivat.AGlue.eq_or_neg_of_primitive_of_perp`), applied to `dir nℓ` (primitive by
`Nivat.CK224.prim_dir`, perpendicular to `nℓ` by `dot_dir` + `dot_comm`) and `vl` itself
(perpendicular to `nℓ` by hypothesis + `dot_comm`). -/
theorem dir_nℓ_eq_or_neg_vl {nℓ vl : ℤ × ℤ}
    (hnℓ_ne : nℓ ≠ 0) (hnℓ_prim : Prim nℓ) (hvl_prim : Primitive vl)
    (hperp : dot nℓ vl = 0) :
    dir nℓ = vl ∨ dir nℓ = -vl := by
  have hdirprim : Primitive (dir nℓ) := Nivat.CK224.prim_dir hnℓ_prim
  have h1 : dot vl nℓ = 0 := by rw [dot_comm]; exact hperp
  have h2 : dot (dir nℓ) nℓ = 0 := by rw [dot_comm]; exact dot_dir nℓ
  exact Nivat.AGlue.eq_or_neg_of_primitive_of_perp hnℓ_ne hdirprim hvl_prim h2 h1

end Nivat.ShellRegionJ

#print axioms Nivat.ShellRegionJ.dir_nℓ_eq_or_neg_vl
#print axioms Nivat.ShellRegionJ.det_J_or_det_ν₀_pos_of_not_mem_arc
#print axioms Nivat.ShellRegionJ.hsweepW_of_fan_adjacent
#print axioms Nivat.ShellRegionJ.hsweepW_of_arc_empty
#print axioms Nivat.ShellRegionJ.hhp_of_faceStart_pinned
#print axioms Nivat.ShellRegionJ.face_iUnion_of_stabilizes
#print axioms Nivat.ShellRegionJ.iUnion_comp_strictMono_eq
#print axioms Nivat.ShellRegionJ.face_eq_empty_of_ray_unbounded
#print axioms Nivat.ShellRegionJ.not_mem_E_of_ray_unbounded
#print axioms Nivat.ShellRegionJ.not_mem_E_of_det_J_pos
#print axioms Nivat.ShellRegionJ.not_mem_E_of_det_ν₀_pos
#print axioms Nivat.ShellRegionJ.mem_E_of_ray_in_face
#print axioms Nivat.ShellRegionJ.not_mem_E_of_neg_ν₀
#print axioms Nivat.ShellRegionJ.not_mem_E_of_neg_J
#print axioms Nivat.ShellRegionJ.E_iUnion_eq_insert_arc
#print axioms Nivat.ShellRegionJ.hsweep_of_fan_adjacent
#print axioms Nivat.ShellRegionJ.hsweep_of_arc_empty
#print axioms Nivat.ShellRegionJ.mem_E_of_arc_stabilizes
