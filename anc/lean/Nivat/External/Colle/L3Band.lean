/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.L3Cover
import Nivat.External.Colle.BoyleLind
import Nivat.External.Colle.RegionCutGE
import Nivat.Lattice.Primitive
import Nivat.External.Colle.ShellGeom
import Nivat.External.Colle.L1Assemble
import Nivat.External.Colle.L1RegionBuild

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# `hband`: non-vacuity, and why a producer would be self-defeating

`Nivat.L3Cover.cone_subset_genClosure_of_box` (`L3Cover.lean:258`) reduces L3's `covers`
obligation to two hypotheses with no producer: `hSbox` (verbatim `window_of_box`'s,
`SweptSeed.lean:474`) and

```
hband : ∀ p q : ℤ, -(M : ℤ) ≤ p → -(N : ℤ) ≤ q → (p < 0 ∨ q < 0) →
  g₀ + p • w' + q • w ∈ D
```

Its non-vacuity witness `cone_hypotheses_nonvacuous` (`L3Cover.lean:388`) uses
`S = {(0,0), (-1,0)}` — two points, i.e. exactly the collinear shape that
`no_hSrun_of_nonCollinear` (`SweptSeed.lean:412`) rules out at the real call site — and
`h = (0,0)`, i.e. a degenerate sweep direction.  This file answers the two questions that
raises.

## §1–§2  Non-vacuity, answered: the hypotheses survive a genuinely 2D `S`

`one_le_of_hSbox_of_nonCollinear` (§1) shows first that three non-collinear points in `S` force
`1 ≤ N` **and** `1 ≤ M` — the degenerate box is exactly the refuted run.  §2 then exhibits
parameters at which `hSbox ∧ hband` both hold with

* `S = {(0,0), (0,-1), (-1,0)}`, three non-collinear points (`bdS_nonCollinear`);
* `h = -((1 : ℤ) • u) ≠ 0`, the genuine shape `sweptSeed_subset_R` (`SweptSeed.lean:255`)
  demands, not `L3Cover.lean:388`'s `h = 0`;
* a genuine `sweptSeed`, `N = M = 1`.

So §5 of `L3Cover.lean` is **not** vacuous the way `window_of_runs` was.

## §3–§5  But a producer in the seed's own recession cone proves nothing

`sweptSeed B u' t₁ h` is closed under `+u'` and under `-h` (§3).  Hence (§4) whenever `w` and
`w'` are `ℕ`-combinations of `u'` and `-h` — which is the *only* configuration
`blueprint/LEAF-L3.md`'s cone note contemplates, `-h = n • u` and `w ∈ cone(u', u)` — the
single corner instance `p = q = -1` of `hband` already puts the **whole** quarter-cone inside
the seed:

```
cone_subset_sweptSeed_of_band :
  1 ≤ N → 1 ≤ M → w = α • u' + β • (-h) → w' = α' • u' + β' • (-h) → hband →
    ∀ i j : ℕ, g₀ + i • w' + j • w ∈ sweptSeed B u' t₁ h
```

`genClosure` is not mentioned; `hSbox` is not used.  §5 turns that into
`covers_free_of_band`: under the same reading, `hKcone` gives `K ⊆ sweptSeed B u' t₁ h`
outright, so `cone_subset_genClosure_of_box`'s conclusion is reached without any window at all.
§6 checks the §2 witness is one of these (its cone really is inside its seed).

⚠ **Scope.**  This does **not** refute `cone_subset_genClosure_of_box`, and does not say
`hband` is unsatisfiable — §2 says the opposite.  It says a producer that keeps `w, w'` in
`cone(u', -h)` makes §5 a tautology *and* forces `K ⊆ sweptSeed`, which is the hypothesis the
seed-obstruction refutations attack (`no_region_in_det_two_seed`, in `tmp/`, **not landed**).
Nothing is claimed about `w, w'` outside that cone; `Nivat.L3win.no_hbase_of_transverse`
(`tmp/L3win_hbase_refute.lean`, **not landed**) is the only statement on record there and it
concerns the doubly-infinite form.
-/

namespace Nivat.L3Band

open Nivat Nivat.MaxEnv Nivat.Colle Nivat.Colle41 Nivat.Colle43
open Nivat.LE2 (dot halfPlaneGE)

/-! ## §1  A two-dimensional `S` forces both box dimensions to be positive -/

/-- **`hSbox` with `N = 0` or `M = 0` is `hSrun` in disguise**, hence refuted by
`no_hSrun_of_nonCollinear` (`SweptSeed.lean:412`) as soon as `S` has three non-collinear
points.  So at the intended call site both box dimensions are at least `1`, and `hband`
genuinely asks for an `L`-shaped band with **both** arms infinite — the `p = -1` arm along `w`
and the `q = -1` arm along `w'`. -/
theorem one_le_of_hSbox_of_nonCollinear {S : Finset (ℤ × ℤ)} {p₁ p₂ p₃ : ℤ × ℤ}
    (h₁ : p₁ ∈ S) (h₂ : p₂ ∈ S) (h₃ : p₃ ∈ S)
    (hncol : det (p₂ - p₁) (p₃ - p₁) ≠ 0)
    {a : ℤ × ℤ} (ha : a ∈ S) {w w' : ℤ × ℤ} {N M : ℕ}
    (hSbox : ∀ b ∈ S.erase a, ∃ k m : ℕ, k ≤ N ∧ m ≤ M ∧ 1 ≤ k + m ∧
      b = a - (k : ℤ) • w - (m : ℤ) • w') :
    1 ≤ N ∧ 1 ≤ M := by
  constructor
  · by_contra hN
    refine no_hSrun_of_nonCollinear h₁ h₂ h₃ hncol a ha w' ?_
    intro b hb
    obtain ⟨k, m, hk, -, hkm, hb'⟩ := hSbox b hb
    have hk0 : k = 0 := by omega
    subst hk0
    exact ⟨m, by omega, by simpa using hb'⟩
  · by_contra hM
    refine no_hSrun_of_nonCollinear h₁ h₂ h₃ hncol a ha w ?_
    intro b hb
    obtain ⟨k, m, -, hm, hkm, hb'⟩ := hSbox b hb
    have hm0 : m = 0 := by omega
    subst hm0
    exact ⟨k, by omega, by simpa using hb'⟩

/-! ## §2  The §5 hypotheses are satisfiable with a genuinely two-dimensional `S`

All of `L3Cover.lean:360-399`'s shortcomings are removed at once: `S` has three non-collinear
points, `h` is a genuine nonzero `-((n : ℤ) • u)` with `n = 1 > 0`, `N = M = 1` (which §1 says
is forced), and the seed is a real `sweptSeed`.
-/

private def bdS : Finset (ℤ × ℤ) := {(0, 0), (0, -1), (-1, 0)}
private def bdB : Finset (ℤ × ℤ) := {(-1, -1)}
/-- Within-row direction, Collé's `≈ v_ℓ`. -/
private def bdw : ℤ × ℤ := (0, 1)
/-- Row-stepping direction, Collé's `≈ v_{ℓ'}`. -/
private def bdw' : ℤ × ℤ := (1, 0)
private def bdu : ℤ × ℤ := (1, 0)
private def bdu' : ℤ × ℤ := (0, 1)
/-- `= -((1 : ℤ) • bdu)`, the shape `sweptSeed_subset_R` (`SweptSeed.lean:255`) demands. -/
private def bdh : ℤ × ℤ := (-1, 0)

/-- The three points of `bdS` are not collinear, in the exact sense
`no_hSrun_of_nonCollinear` (`SweptSeed.lean:412`) uses. -/
theorem bdS_nonCollinear :
    ((0, 0) : ℤ × ℤ) ∈ bdS ∧ ((0, -1) : ℤ × ℤ) ∈ bdS ∧ ((-1, 0) : ℤ × ℤ) ∈ bdS ∧
      det (((0, -1) : ℤ × ℤ) - (0, 0)) (((-1, 0) : ℤ × ℤ) - (0, 0)) ≠ 0 := by
  refine ⟨by simp [bdS], by simp [bdS], by simp [bdS], ?_⟩
  norm_num [det]

/-- The seed here is the quarter plane `{(x, y) | -1 ≤ x ∧ -1 ≤ y}`. -/
theorem mem_bd_seed {p q : ℤ} (hp : -1 ≤ p) (hq : -1 ≤ q) :
    ((p, q) : ℤ × ℤ) ∈ sweptSeed bdB bdu' 0 bdh := by
  refine ⟨(p + 1).toNat, ((-1, -1) : ℤ × ℤ), by simp [bdB], q + 1, by omega, ?_⟩
  have hcast : (((p + 1).toNat : ℕ) : ℤ) = p + 1 := Int.toNat_of_nonneg (by omega)
  simp only [bdh, bdu', Prod.mk_add_mk, Prod.smul_mk, smul_eq_mul, Prod.ext_iff, hcast]
  constructor <;> ring

/-- `hSbox` for `bdS`, verbatim `window_of_box`'s shape (`SweptSeed.lean:474`), with
`N = M = 1`. -/
theorem bd_hSbox : ∀ b ∈ bdS.erase ((0, 0) : ℤ × ℤ),
    ∃ k m : ℕ, k ≤ 1 ∧ m ≤ 1 ∧ 1 ≤ k + m ∧
      b = ((0, 0) : ℤ × ℤ) - (k : ℤ) • bdw - (m : ℤ) • bdw' := by
  intro b hb
  have hb' : b = ((0, -1) : ℤ × ℤ) ∨ b = ((-1, 0) : ℤ × ℤ) := by
    simp only [bdS, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hb
    tauto
  rcases hb' with rfl | rfl
  · exact ⟨1, 0, le_refl 1, Nat.zero_le 1, by omega, by norm_num [bdw, bdw', Prod.ext_iff]⟩
  · exact ⟨0, 1, Nat.zero_le 1, le_refl 1, by omega, by norm_num [bdw, bdw', Prod.ext_iff]⟩

/-- `hband` for the same parameters, verbatim `cone_subset_genClosure_of_box`'s shape
(`L3Cover.lean:263`). -/
theorem bd_hband : ∀ p q : ℤ, -((1 : ℕ) : ℤ) ≤ p → -((1 : ℕ) : ℤ) ≤ q → (p < 0 ∨ q < 0) →
    ((0, 0) : ℤ × ℤ) + p • bdw' + q • bdw ∈ sweptSeed bdB bdu' 0 bdh := by
  intro p q hp hq _
  have he : ((0, 0) : ℤ × ℤ) + p • bdw' + q • bdw = ((p, q) : ℤ × ℤ) := by
    simp only [bdw, bdw', Prod.mk_add_mk, Prod.smul_mk, smul_eq_mul, Prod.ext_iff]
    constructor <;> ring
  rw [he]
  exact mem_bd_seed (by exact_mod_cast hp) (by exact_mod_cast hq)

/-- **Answer to the vacuity question: `hSbox ∧ hband` is satisfiable with a genuinely
two-dimensional `S` and a genuine sweep direction.**

Compare `L3Cover.lean:388`, whose `S` has two points and whose `h` is `(0,0)`.  Here `S` has
three non-collinear points and `h = -((1 : ℤ) • u) ≠ 0`, so §5 of `L3Cover.lean` is not
vacuous in the way `window_of_runs` was (`no_hSrun_of_nonCollinear`, `SweptSeed.lean:412`).

⚠ What this does **not** say: that the witness is useful.  §6 shows its cone is already
contained in its seed. -/
theorem box_and_band_satisfiable_with_2D_S :
    (((0, 0) : ℤ × ℤ) ∈ bdS ∧ ((0, -1) : ℤ × ℤ) ∈ bdS ∧ ((-1, 0) : ℤ × ℤ) ∈ bdS ∧
        det (((0, -1) : ℤ × ℤ) - (0, 0)) (((-1, 0) : ℤ × ℤ) - (0, 0)) ≠ 0) ∧
      bdh = -((1 : ℤ) • bdu) ∧ bdh ≠ 0 ∧
      (∀ b ∈ bdS.erase ((0, 0) : ℤ × ℤ), ∃ k m : ℕ, k ≤ 1 ∧ m ≤ 1 ∧ 1 ≤ k + m ∧
        b = ((0, 0) : ℤ × ℤ) - (k : ℤ) • bdw - (m : ℤ) • bdw') ∧
      (∀ p q : ℤ, -((1 : ℕ) : ℤ) ≤ p → -((1 : ℕ) : ℤ) ≤ q → (p < 0 ∨ q < 0) →
        ((0, 0) : ℤ × ℤ) + p • bdw' + q • bdw ∈ sweptSeed bdB bdu' 0 bdh) :=
  ⟨bdS_nonCollinear, by norm_num [bdh, bdu, Prod.ext_iff],
    by norm_num [bdh, Prod.ext_iff], bd_hSbox, bd_hband⟩

/-- **The shapes really are `cone_subset_genClosure_of_box`'s.**  `bd_hSbox` and `bd_hband` are
fed to `Nivat.L3Cover.cone_subset_genClosure_of_box` (`L3Cover.lean:258`) as they stand, with
`N := 1`, `M := 1`; unification against the real lemma is the check that §2 states the intended
hypotheses and not look-alikes (`PROTOCOL.md` §2, 照抄形状). -/
theorem bd_hypotheses_fit :
    ∀ i j : ℕ, ((0, 0) : ℤ × ℤ) + (i : ℤ) • bdw' + (j : ℤ) • bdw ∈
      genClosure bdS ((0, 0) : ℤ × ℤ) (sweptSeed bdB bdu' 0 bdh) :=
  Nivat.L3Cover.cone_subset_genClosure_of_box (N := 1) (M := 1) bd_hSbox bd_hband

/-! ## §3  `sweptSeed`'s recession directions -/

/-- The swept seed is closed under `+u'`. -/
theorem sweptSeed_add_u' {B : Finset (ℤ × ℤ)} {u' : ℤ × ℤ} {t₁ : ℤ} {h z : ℤ × ℤ}
    (hz : z ∈ sweptSeed B u' t₁ h) : z + u' ∈ sweptSeed B u' t₁ h := by
  obtain ⟨ι, hι⟩ := hz
  refine ⟨ι, ?_⟩
  have e : (z + u') + (ι : ℤ) • h = (z + (ι : ℤ) • h) + ((1 : ℕ) : ℤ) • u' := by
    push_cast; module
  rw [e]
  exact halfStripFrom_add_nsmul hι 1

/-- The swept seed is closed under `-h`, i.e. under `+(-h)`: that is what the `ι : ℕ` in
`sweptSeed` (`SweptSeed.lean:65`) buys.  With `h = -((n : ℤ) • u)` this is the `u`-direction. -/
theorem sweptSeed_sub_h {B : Finset (ℤ × ℤ)} {u' : ℤ × ℤ} {t₁ : ℤ} {h z : ℤ × ℤ}
    (hz : z ∈ sweptSeed B u' t₁ h) : z + (-h) ∈ sweptSeed B u' t₁ h := by
  obtain ⟨ι, hι⟩ := hz
  refine ⟨ι + 1, ?_⟩
  have e : (z + (-h)) + ((ι + 1 : ℕ) : ℤ) • h = z + (ι : ℤ) • h := by push_cast; module
  rw [e]
  exact hι

theorem sweptSeed_add_nsmul_u' {B : Finset (ℤ × ℤ)} {u' : ℤ × ℤ} {t₁ : ℤ} {h z : ℤ × ℤ}
    (hz : z ∈ sweptSeed B u' t₁ h) (α : ℕ) : z + (α : ℤ) • u' ∈ sweptSeed B u' t₁ h := by
  induction α with
  | zero => simpa using hz
  | succ α ih =>
    have e : z + ((α + 1 : ℕ) : ℤ) • u' = (z + (α : ℤ) • u') + u' := by push_cast; module
    rw [e]
    exact sweptSeed_add_u' ih

theorem sweptSeed_add_nsmul_neg_h {B : Finset (ℤ × ℤ)} {u' : ℤ × ℤ} {t₁ : ℤ} {h z : ℤ × ℤ}
    (hz : z ∈ sweptSeed B u' t₁ h) (β : ℕ) : z + (β : ℤ) • (-h) ∈ sweptSeed B u' t₁ h := by
  induction β with
  | zero => simpa using hz
  | succ β ih =>
    have e : z + ((β + 1 : ℕ) : ℤ) • (-h) = (z + (β : ℤ) • (-h)) + (-h) := by push_cast; module
    rw [e]
    exact sweptSeed_sub_h ih

/-- **The seed absorbs every `ℕ`-combination of its two generating directions.** -/
theorem sweptSeed_add_natComb {B : Finset (ℤ × ℤ)} {u' : ℤ × ℤ} {t₁ : ℤ} {h z : ℤ × ℤ}
    (hz : z ∈ sweptSeed B u' t₁ h) (α β : ℕ) :
    z + (α : ℤ) • u' + (β : ℤ) • (-h) ∈ sweptSeed B u' t₁ h :=
  sweptSeed_add_nsmul_neg_h (sweptSeed_add_nsmul_u' hz α) β

/-! ## §4  Inside the seed's own cone, `hband` already gives the whole quarter-cone -/

/-- **`hband` is self-defeating when `w, w'` lie in `cone(u', -h)`.**

`blueprint/LEAF-L3.md`'s cone note pins exactly this configuration: `h = -((n : ℤ) • u)` so
that the seed's two generating directions are `u'` and `u`, and the condition on the row
direction is `w ∈ cone(u', u)`.  Under it, the **single** corner instance `p = q = -1` of
`hband` — legal because `1 ≤ N` and `1 ≤ M`, which §1 says a two-dimensional `S` forces —
already puts the entire quarter-cone inside the seed.

Consequences, both immediate:

* `cone_subset_genClosure_of_box` (`L3Cover.lean:258`) becomes a tautology at such parameters:
  its conclusion follows from `subset_genClosure` (`MaximalEnveloped.lean:697`) alone, with
  `hSbox` unused and the window never consulted.
* Combined with `hKcone` it gives `K ⊆ sweptSeed B u' t₁ h` (§5) — the hypothesis the seed
  obstructions attack.

⚠ **Scope.**  This assumes `w` and `w'` are `ℕ`-combinations of `u'` and `-h`.  It says
nothing when they are not; in particular it does not refute `hband`, and §2 exhibits a model
where `hband` holds. -/
theorem cone_subset_sweptSeed_of_band
    {B : Finset (ℤ × ℤ)} {u' : ℤ × ℤ} {t₁ : ℤ} {h w w' g₀ : ℤ × ℤ} {N M : ℕ}
    (hN : 1 ≤ N) (hM : 1 ≤ M) {α β α' β' : ℕ}
    (hw : w = (α : ℤ) • u' + (β : ℤ) • (-h))
    (hw' : w' = (α' : ℤ) • u' + (β' : ℤ) • (-h))
    (hband : ∀ p q : ℤ, -(M : ℤ) ≤ p → -(N : ℤ) ≤ q → (p < 0 ∨ q < 0) →
      g₀ + p • w' + q • w ∈ sweptSeed B u' t₁ h) :
    ∀ i j : ℕ, g₀ + (i : ℤ) • w' + (j : ℤ) • w ∈ sweptSeed B u' t₁ h := by
  intro i j
  have hMz : -(M : ℤ) ≤ (-1 : ℤ) := by
    have : (1 : ℤ) ≤ (M : ℤ) := by exact_mod_cast hM
    omega
  have hNz : -(N : ℤ) ≤ (-1 : ℤ) := by
    have : (1 : ℤ) ≤ (N : ℤ) := by exact_mod_cast hN
    omega
  have hcorner := hband (-1) (-1) hMz hNz (Or.inl (by norm_num))
  have key := sweptSeed_add_natComb hcorner ((i + 1) * α' + (j + 1) * α)
    ((i + 1) * β' + (j + 1) * β)
  have e : (g₀ + (-1 : ℤ) • w' + (-1 : ℤ) • w)
        + (((i + 1) * α' + (j + 1) * α : ℕ) : ℤ) • u'
        + (((i + 1) * β' + (j + 1) * β : ℕ) : ℤ) • (-h)
      = g₀ + (i : ℤ) • w' + (j : ℤ) • w := by
    subst hw; subst hw'; push_cast; module
  rw [← e]
  exact key

/-! ## §5  Hence `covers` is free, and `K` is trapped in the seed -/

/-- **`SweptCoverData.covers` needs no window at these parameters** — and says more than it
was supposed to: the cone hypothesis plus the band put `K` inside the seed outright.

The second conjunct is the one that matters.  `SweptCoverData` also carries
`seed_subset_R`, so `K ⊆ R` comes free too; but `K` is additionally required to satisfy
`IsRegion K u u'` (`Lemma41.lean:688`), and "a region inside the seed" is exactly the
configuration the seed obstructions rule out (`no_region_in_det_two_seed`, in `tmp/`,
**not landed**, so cited as a pointer and not used here). -/
theorem covers_free_of_band
    {B : Finset (ℤ × ℤ)} {u' : ℤ × ℤ} {t₁ : ℤ} {h w w' g₀ : ℤ × ℤ} {N M : ℕ}
    (hN : 1 ≤ N) (hM : 1 ≤ M) {α β α' β' : ℕ}
    (hw : w = (α : ℤ) • u' + (β : ℤ) • (-h))
    (hw' : w' = (α' : ℤ) • u' + (β' : ℤ) • (-h))
    (hband : ∀ p q : ℤ, -(M : ℤ) ≤ p → -(N : ℤ) ≤ q → (p < 0 ∨ q < 0) →
      g₀ + p • w' + q • w ∈ sweptSeed B u' t₁ h)
    {K : Set (ℤ × ℤ)}
    (hKcone : K ⊆ {z : ℤ × ℤ | ∃ i j : ℕ, z = g₀ + (i : ℤ) • w' + (j : ℤ) • w}) :
    K ⊆ sweptSeed B u' t₁ h ∧
      ∀ (S : Finset (ℤ × ℤ)) (a : ℤ × ℤ), K ⊆ genClosure S a (sweptSeed B u' t₁ h) := by
  have hsub : K ⊆ sweptSeed B u' t₁ h := by
    intro z hz
    obtain ⟨i, j, rfl⟩ := hKcone hz
    exact cone_subset_sweptSeed_of_band hN hM hw hw' hband i j
  exact ⟨hsub, fun S a => hsub.trans (subset_genClosure S a _)⟩

/-! ## §6  The §2 witness is one of these -/

/-- In §2's model `w = u'` and `w' = -h`, so §4 applies: the quarter-cone is already inside
the seed.  Concretely the seed is the quarter plane `-1 ≤ x, -1 ≤ y` and the cone is the first
quadrant.  **So §2 answers "satisfiable", not "useful".** -/
theorem bd_cone_subset_seed :
    ∀ i j : ℕ, ((0, 0) : ℤ × ℤ) + (i : ℤ) • bdw' + (j : ℤ) • bdw
      ∈ sweptSeed bdB bdu' 0 bdh :=
  cone_subset_sweptSeed_of_band (N := 1) (M := 1) le_rfl le_rfl
    (α := 1) (β := 0) (α' := 0) (β' := 1)
    (by norm_num [bdw, bdu', bdh, Prod.ext_iff])
    (by norm_num [bdw', bdh, Prod.ext_iff])
    bd_hband

/-! ## §7  For a one-point base, `hband` *forces* the cone hypothesis of §4

§4 assumed `w, w' ∈ cone(u', -h)`.  This section removes the assumption when `B` is a
singleton: the two arms of the band are infinite rays, and an infinite ray inside
`sweptSeed {g} u' t₁ h` can only run in an `ℕ`-combination of the seed's own two generating
directions.  So for `|B| = 1` there is no escape: **every** producer of `hband` makes
`cone_subset_genClosure_of_box` (`L3Cover.lean:258`) a tautology.

⚠ `|B| = 1` is a real restriction and is not removed here.  For `|B| ≥ 2` the pigeonhole
leaves the ray's coefficients merely rational, and I did not close the quantisation gap; see
the report.  (`tmp/L3_row0_and_swept_repair.lean`'s `no_region_in_det_two_seed`, **not
landed**, is also a one-point-base statement.)
-/

private theorem seed_singleton_iff {g u' h z : ℤ × ℤ} {t₁ : ℤ} :
    z ∈ sweptSeed {g} u' t₁ h ↔ ∃ ι : ℕ, ∃ t : ℤ, t₁ ≤ t ∧ z + (ι : ℤ) • h = g + t • u' := by
  constructor
  · rintro ⟨ι, g', hg', t, ht, he⟩
    simp only [Finset.mem_singleton] at hg'
    exact ⟨ι, t, ht, by rw [he, hg']⟩
  · rintro ⟨ι, t, ht, he⟩
    exact ⟨ι, g, Finset.mem_singleton_self g, t, ht, he⟩

/-- Coordinates with respect to two `ℤ`-independent vectors are unique. -/
private theorem coords_zero {v v' : ℤ × ℤ} (hdet : det v v' ≠ 0) {a b : ℤ}
    (hab : a • v + b • v' = 0) : a = 0 ∧ b = 0 := by
  have h1 : a * v.1 + b * v'.1 = 0 := by
    have := congrArg Prod.fst hab; simpa using this
  have h2 : a * v.2 + b * v'.2 = 0 := by
    have := congrArg Prod.snd hab; simpa using this
  have hA : a * det v v' = 0 := by
    simp only [det]; linear_combination v'.2 * h1 - v'.1 * h2
  have hB : b * det v v' = 0 := by
    simp only [det]; linear_combination v.1 * h2 - v.2 * h1
  exact ⟨by rcases mul_eq_zero.mp hA with h | h; exact h; exact absurd h hdet,
    by rcases mul_eq_zero.mp hB with h | h; exact h; exact absurd h hdet⟩

/-- **An infinite ray inside a one-point swept seed runs in an `ℕ`-combination of `u'` and
`-h`.**

The seed's only two recession directions are `u'` (unbounded `t`) and `-h` (unbounded `ι`),
and with `|B| = 1` and `det u' h ≠ 0` the coordinates `(ι_q, t_q)` of the ray's `q`-th point
are *uniquely determined* and affine in `q`.  `ι_q : ℕ` forces the `-h` slope to be `≥ 0`;
`t₁ ≤ t_q` forces the `u'` slope to be `≥ 0`. -/
theorem natComb_of_ray_in_singleton_seed
    {g u' h w c : ℤ × ℤ} {t₁ : ℤ} (hdet : det u' h ≠ 0)
    (hray : ∀ q : ℕ, c + (q : ℤ) • w ∈ sweptSeed {g} u' t₁ h) :
    ∃ α β : ℕ, w = (α : ℤ) • u' + (β : ℤ) • (-h) := by
  obtain ⟨ι₀, s₀, hs₀, he₀⟩ := seed_singleton_iff.mp (by simpa using hray 0)
  obtain ⟨ι₁, s₁, -, he₁⟩ := seed_singleton_iff.mp (by simpa using hray 1)
  -- The step from `q = 0` to `q = 1` already determines `w`'s coordinates.
  have e2 : w + ((ι₁ : ℤ) - (ι₀ : ℤ)) • h = (s₁ - s₀) • u' := by
    have hl : (c + w + (ι₁ : ℤ) • h) - (c + (ι₀ : ℤ) • h)
        = w + ((ι₁ : ℤ) - (ι₀ : ℤ)) • h := by module
    have hr : (g + s₁ • u') - (g + s₀ • u') = (s₁ - s₀) • u' := by module
    rw [← hl, ← hr, he₁, he₀]
  have hw : w = (s₁ - s₀) • u' + ((ι₁ : ℤ) - (ι₀ : ℤ)) • (-h) := by
    have hstep : w = (s₁ - s₀) • u' - ((ι₁ : ℤ) - (ι₀ : ℤ)) • h := by rw [← e2]; module
    rw [hstep]; module
  -- Every later point's coordinates are then forced.
  have key : ∀ q : ℕ, ∀ ιq : ℕ, ∀ sq : ℤ,
      c + (q : ℤ) • w + (ιq : ℤ) • h = g + sq • u' →
      (ιq : ℤ) = (ι₀ : ℤ) + (q : ℤ) * ((ι₁ : ℤ) - (ι₀ : ℤ)) ∧
        sq = s₀ + (q : ℤ) * (s₁ - s₀) := by
    intro q ιq sq heq
    have hzero : ((q : ℤ) * (s₁ - s₀) - (sq - s₀)) • u'
        + ((ιq : ℤ) - (ι₀ : ℤ) - (q : ℤ) * ((ι₁ : ℤ) - (ι₀ : ℤ))) • h = 0 := by
      have hid : ((q : ℤ) * (s₁ - s₀) - (sq - s₀)) • u'
            + ((ιq : ℤ) - (ι₀ : ℤ) - (q : ℤ) * ((ι₁ : ℤ) - (ι₀ : ℤ))) • h
          = ((c + (q : ℤ) • w + (ιq : ℤ) • h) - (g + sq • u'))
            - ((c + (ι₀ : ℤ) • h) - (g + s₀ • u'))
            + (q : ℤ) • (((s₁ - s₀) • u' + ((ι₁ : ℤ) - (ι₀ : ℤ)) • (-h)) - w) := by
        module
      rw [hid, heq, he₀, ← hw]
      simp
    obtain ⟨hA, hB⟩ := coords_zero hdet hzero
    exact ⟨by linarith, by linarith⟩
  -- Both slopes are non-negative.
  have hBpos : 0 ≤ (ι₁ : ℤ) - (ι₀ : ℤ) := by
    by_contra hneg
    obtain ⟨ιq, sq, -, heq⟩ := seed_singleton_iff.mp (hray (ι₀ + 1))
    obtain ⟨h1, -⟩ := key (ι₀ + 1) ιq sq heq
    push_cast at h1
    have hnn : (0 : ℤ) ≤ (ιq : ℤ) := Int.natCast_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left (show (ι₁ : ℤ) - (ι₀ : ℤ) ≤ -1 by omega)
      (show (0 : ℤ) ≤ (ι₀ : ℤ) + 1 by positivity)]
  have hApos : 0 ≤ s₁ - s₀ := by
    by_contra hneg
    set Qn : ℕ := (s₀ - t₁).toNat + 1 with hQn
    obtain ⟨ιq, sq, hsq, heq⟩ := seed_singleton_iff.mp (hray Qn)
    obtain ⟨-, h2⟩ := key Qn ιq sq heq
    have hQnz : (s₀ - t₁) + 1 ≤ (Qn : ℤ) := by
      have hself := Int.self_le_toNat (s₀ - t₁)
      rw [hQn]; push_cast; omega
    have hQnn : (0 : ℤ) ≤ (Qn : ℤ) := Int.natCast_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left (show s₁ - s₀ ≤ -1 by omega) hQnn]
  refine ⟨(s₁ - s₀).toNat, ((ι₁ : ℤ) - (ι₀ : ℤ)).toNat, ?_⟩
  rw [Int.toNat_of_nonneg hApos, Int.toNat_of_nonneg hBpos]
  exact hw

/-- **For a one-point base, `hband` alone puts the whole quarter-cone inside the seed** — no
hypothesis on `w`, `w'` beyond what `hband` itself implies.

So the `hband` obligation of `cone_subset_genClosure_of_box` (`L3Cover.lean:258`) cannot be
discharged in a way that leaves `genClosure` any work to do: at `|B| = 1` the two arms of the
band already force `w, w' ∈ cone(u', -h)` (§7's ray lemma), and §4 then gives the conclusion
without `hSbox`. -/
theorem cone_subset_sweptSeed_of_band_singleton
    {g u' : ℤ × ℤ} {t₁ : ℤ} {h w w' g₀ : ℤ × ℤ} {N M : ℕ}
    (hdet : det u' h ≠ 0) (hN : 1 ≤ N) (hM : 1 ≤ M)
    (hband : ∀ p q : ℤ, -(M : ℤ) ≤ p → -(N : ℤ) ≤ q → (p < 0 ∨ q < 0) →
      g₀ + p • w' + q • w ∈ sweptSeed {g} u' t₁ h) :
    ∀ i j : ℕ, g₀ + (i : ℤ) • w' + (j : ℤ) • w ∈ sweptSeed {g} u' t₁ h := by
  have hMz : -(M : ℤ) ≤ (-1 : ℤ) := by
    have : (1 : ℤ) ≤ (M : ℤ) := by exact_mod_cast hM
    omega
  have hNz : -(N : ℤ) ≤ (-1 : ℤ) := by
    have : (1 : ℤ) ≤ (N : ℤ) := by exact_mod_cast hN
    omega
  -- Arm `p = -1`: an infinite ray in direction `w`.
  have hrayw : ∀ q : ℕ, (g₀ + (-1 : ℤ) • w') + (q : ℤ) • w ∈ sweptSeed {g} u' t₁ h := by
    intro q
    exact hband (-1) (q : ℤ) hMz (by omega) (Or.inl (by norm_num))
  -- Arm `q = -1`: an infinite ray in direction `w'`.
  have hrayw' : ∀ p : ℕ, (g₀ + (-1 : ℤ) • w) + (p : ℤ) • w' ∈ sweptSeed {g} u' t₁ h := by
    intro p
    have hb := hband (p : ℤ) (-1) (by omega) hNz (Or.inr (by norm_num))
    have e : (g₀ + (-1 : ℤ) • w) + (p : ℤ) • w' = g₀ + (p : ℤ) • w' + (-1 : ℤ) • w := by module
    rw [e]; exact hb
  obtain ⟨α, β, hw⟩ := natComb_of_ray_in_singleton_seed hdet hrayw
  obtain ⟨α', β', hw'⟩ := natComb_of_ray_in_singleton_seed hdet hrayw'
  exact cone_subset_sweptSeed_of_band hN hM hw hw' hband
/-! ## §8  A region cannot live in the swept seed unless the base is at least `n` points

§4–§7 put `K` inside `sweptSeed B u' t₁ h`.  This section shows that is fatal, by reading the
definitions involved literally (all five printed out, not recalled):

```
RayIn (U : Set (ℤ × ℤ)) (z₀ v : ℤ × ℤ) : Prop := ∀ k : ℕ, z₀ + (k : ℤ) • v ∈ U
                                                             -- `Lemma41.lean:675`
IsRegion (K : Set (ℤ × ℤ)) (u u' : ℤ × ℤ) : Prop :=
  IsLatticeConvexRegion K ∧ (∃ z₀, RayIn K z₀ u) ∧ (∃ z₀', RayIn K z₀' u')
                                                             -- `Lemma41.lean:688`
sweptSeed (B) (u') (t₁) (h) : Set (ℤ × ℤ) :=
  {z | ∃ ι : ℕ, z + (ι : ℤ) • h ∈ halfStripFrom B u' t₁}     -- `SweptSeed.lean:65`
halfStripFrom (B) (u') (t₁) : Set (ℤ × ℤ) :=
  {z | ∃ g ∈ B, ∃ t : ℤ, t₁ ≤ t ∧ z = g + t • u'}            -- `Claim43.lean:388`
det (u v : ℤ × ℤ) : ℤ := u.1 * v.2 - u.2 * v.1               -- `Nivat/Defs/Config.lean:43`
```

With `h = -((n : ℤ) • u)` — the shape `sweptSeed_subset_R` (`SweptSeed.lean:255`) demands, so
this is the seed L3 actually uses — the seed is
`{g + t • u' + m • u : g ∈ B, t ≥ t₁, m ∈ n·ℕ}`: its `u`-displacements are **quantised to
multiples of `n`**.  A `RayIn` asks for step `1`.  The only way to reconcile the two is to
change base point, and `B` is finite, so `n ≤ B.card`.

⚠ This is a theorem, not a counterexample: no parameter is fixed.  What it does **not** say is
that §5 is unconditionally unsatisfiable — at `n ≤ B.card` the obstruction is absent, and §2's
witness (`n = 1`, `B.card = 1`) is a model on the other side of that line.
-/

/-- **The `u`-quantisation of the swept seed, as a determinant equation.**

If `z₀ + k • u` lies in `sweptSeed B u' t₁ (-((n : ℤ) • u))`, then for the witnessing
`g ∈ B` and `ι : ℕ` one has `(k - ι·n) · det u u' = det u' z₀ - det u' g`.  Applying
`det u' ·` kills both `u'` and the strip parameter `t`, leaving the `u`-coordinate alone. -/
theorem det_eq_of_mem_sweptSeed {B : Finset (ℤ × ℤ)} {u u' z₀ : ℤ × ℤ} {t₁ : ℤ} {n k : ℕ}
    (hmem : z₀ + (k : ℤ) • u ∈ sweptSeed B u' t₁ (-((n : ℤ) • u))) :
    ∃ g ∈ B, ∃ ι : ℕ,
      ((k : ℤ) - (ι : ℤ) * (n : ℤ)) * det u u' = det u' z₀ - det u' g := by
  obtain ⟨ι, g, hg, t, -, heq⟩ := hmem
  refine ⟨g, hg, ι, ?_⟩
  have h1 := congrArg Prod.fst heq
  have h2 := congrArg Prod.snd heq
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Prod.fst_neg,
    Prod.snd_neg, smul_eq_mul] at h1 h2
  simp only [det]
  linear_combination u'.2 * h1 - u'.1 * h2

/-- **A `u`-ray inside the swept seed forces `n ≤ |B|`.**

Only `RayIn` is used — not `IsLatticeConvexRegion`, not the `u'`-ray.  Two ray points at `k`
and `k'` sharing a base point `g ∈ B` satisfy `k - k' = n·(ι - ι')`, so the `n` indices
`k = 0, …, n-1` need `n` distinct base points.

This subsumes `no_region_in_det_two_seed` (`tmp/L3_row0_and_swept_repair.lean:3534`, **in
`tmp/`, not landed**), which is the single case `n = 2`, `|B| = 1`, `u = (1,0)`, `u' = (0,2)`
and additionally spends `IsLatticeConvexRegion` on a parity/midpoint argument. -/
theorem card_le_of_rayIn_sweptSeed
    {B : Finset (ℤ × ℤ)} {u u' z₀ : ℤ × ℤ} {t₁ : ℤ} {n : ℕ}
    (hdet : det u u' ≠ 0)
    (hray : RayIn (sweptSeed B u' t₁ (-((n : ℤ) • u))) z₀ u) :
    n ≤ B.card := by
  choose g hgB ι hgeq using fun k : ℕ => det_eq_of_mem_sweptSeed (hray k)
  have hcard : (Finset.range n).card ≤ B.card := by
    refine Finset.card_le_card_of_injOn g (fun k _ => hgB k) ?_
    intro k hk k' hk' hgg
    have hkn : k < n := Finset.mem_range.mp hk
    have hk'n : k' < n := Finset.mem_range.mp hk'
    have hcancel : ((k : ℤ) - (ι k : ℤ) * (n : ℤ)) = ((k' : ℤ) - (ι k' : ℤ) * (n : ℤ)) :=
      mul_right_cancel₀ hdet (((hgeq k).trans (by rw [hgg])).trans (hgeq k').symm)
    have hkk : (k : ℤ) - (k' : ℤ) = ((ι k : ℤ) - (ι k' : ℤ)) * (n : ℤ) := by
      linear_combination hcancel
    have hn0 : (0 : ℤ) ≤ (n : ℤ) := Int.natCast_nonneg n
    have hlt : (ι k : ℤ) - (ι k' : ℤ) < 1 :=
      lt_of_mul_lt_mul_right (by rw [one_mul, ← hkk]; omega) hn0
    have hgt : (-1 : ℤ) < (ι k : ℤ) - (ι k' : ℤ) :=
      lt_of_mul_lt_mul_right (by rw [← hkk]; omega) hn0
    have hz : ((ι k : ℤ) - (ι k' : ℤ)) = 0 := by omega
    rw [hz, zero_mul] at hkk
    omega
  simpa using hcard

/-- **`IsRegion K u u'` and `K ⊆ sweptSeed B u' t₁ (-(n • u))` are incompatible when
`B.card < n`.**  The `u`-ray of `IsRegion` (`Lemma41.lean:688`) is the only component
consumed. -/
theorem not_isRegion_of_subset_sweptSeed
    {B : Finset (ℤ × ℤ)} {K : Set (ℤ × ℤ)} {u u' : ℤ × ℤ} {t₁ : ℤ} {n : ℕ}
    (hdet : det u u' ≠ 0) (hcard : B.card < n)
    (hK : K ⊆ sweptSeed B u' t₁ (-((n : ℤ) • u))) :
    ¬ IsRegion K u u' := by
  rintro ⟨-, ⟨z₀, hray⟩, -⟩
  exact absurd (card_le_of_rayIn_sweptSeed hdet fun k => hK (hray k)) (by omega)

/-! ## §9  `L3Cover.lean` §5 is unsatisfiable whenever `B.card < n`

§4/§7 (cone inside seed) composed with §8 (no region inside seed).  Two forms: a general one
that still carries §4's cone assumption on `w`, `w'`, and a one-point-base one that carries
**no** hypothesis on `w`, `w'` at all, because §7 forces it out of `hband`.
-/

/-- **The four §5 conditions are jointly false** when `w`, `w'` lie in the seed's recession
cone and `B.card < n`.

`_hSbox` is listed so the statement is literally "`hSbox ∧ hband ∧ K` a cone `∧ IsRegion K u u'`
is contradictory", and is deliberately **not consumed** — that it is dead weight is part of the
finding (§4). -/
theorem no_box_band_cone_region
    {S : Finset (ℤ × ℤ)} {a : ℤ × ℤ} {B : Finset (ℤ × ℤ)} {u u' : ℤ × ℤ} {t₁ : ℤ} {n : ℕ}
    {w w' g₀ : ℤ × ℤ} {N M : ℕ} {K : Set (ℤ × ℤ)}
    (hdet : det u u' ≠ 0) (hcard : B.card < n) (hN : 1 ≤ N) (hM : 1 ≤ M)
    {α β α' β' : ℕ}
    (hw : w = (α : ℤ) • u' + (β : ℤ) • ((n : ℤ) • u))
    (hw' : w' = (α' : ℤ) • u' + (β' : ℤ) • ((n : ℤ) • u))
    (_hSbox : ∀ b ∈ S.erase a, ∃ k m : ℕ, k ≤ N ∧ m ≤ M ∧ 1 ≤ k + m ∧
      b = a - (k : ℤ) • w - (m : ℤ) • w')
    (hband : ∀ p q : ℤ, -(M : ℤ) ≤ p → -(N : ℤ) ≤ q → (p < 0 ∨ q < 0) →
      g₀ + p • w' + q • w ∈ sweptSeed B u' t₁ (-((n : ℤ) • u)))
    (hKcone : K ⊆ {z : ℤ × ℤ | ∃ i j : ℕ, z = g₀ + (i : ℤ) • w' + (j : ℤ) • w}) :
    ¬ IsRegion K u u' := by
  refine not_isRegion_of_subset_sweptSeed (t₁ := t₁) hdet hcard ?_
  intro z hz
  obtain ⟨i, j, rfl⟩ := hKcone hz
  exact cone_subset_sweptSeed_of_band hN hM (by rw [hw, neg_neg]) (by rw [hw', neg_neg])
    hband i j

/-- **For a one-point base and `2 ≤ n`, §5 is unsatisfiable outright.**

No hypothesis on `w`, `w'`: §7's `natComb_of_ray_in_singleton_seed` extracts it from the two
arms of `hband` itself.  `_hSbox` again unused.

This is the sharpest form of the finding.  The L1 lane's `L1Data.ofEdgeRun`
(`L1Fields.lean:154`) sets `B := {z₀}`, so `B.card = 1` is what L1 currently exports, and
`2 ≤ n` then closes the §5 route there. -/
theorem no_band_cone_region_singleton
    {S : Finset (ℤ × ℤ)} {a : ℤ × ℤ} {g : ℤ × ℤ} {u u' : ℤ × ℤ} {t₁ : ℤ} {n : ℕ}
    {w w' g₀ : ℤ × ℤ} {N M : ℕ} {K : Set (ℤ × ℤ)}
    (hdet : det u u' ≠ 0) (hn : 2 ≤ n) (hN : 1 ≤ N) (hM : 1 ≤ M)
    (_hSbox : ∀ b ∈ S.erase a, ∃ k m : ℕ, k ≤ N ∧ m ≤ M ∧ 1 ≤ k + m ∧
      b = a - (k : ℤ) • w - (m : ℤ) • w')
    (hband : ∀ p q : ℤ, -(M : ℤ) ≤ p → -(N : ℤ) ≤ q → (p < 0 ∨ q < 0) →
      g₀ + p • w' + q • w ∈ sweptSeed {g} u' t₁ (-((n : ℤ) • u)))
    (hKcone : K ⊆ {z : ℤ × ℤ | ∃ i j : ℕ, z = g₀ + (i : ℤ) • w' + (j : ℤ) • w}) :
    ¬ IsRegion K u u' := by
  have hdet' : det u' (-((n : ℤ) • u)) ≠ 0 := by
    have e : det u' (-((n : ℤ) • u)) = (n : ℤ) * det u u' := by
      simp only [det, Prod.fst_neg, Prod.snd_neg, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      ring
    rw [e]
    exact mul_ne_zero (by exact_mod_cast (by omega : (n : ℕ) ≠ 0)) hdet
  have hcard : ({g} : Finset (ℤ × ℤ)).card < n := by
    rw [Finset.card_singleton]; omega
  refine not_isRegion_of_subset_sweptSeed (t₁ := t₁) hdet hcard ?_
  intro z hz
  obtain ⟨i, j, rfl⟩ := hKcone hz
  exact cone_subset_sweptSeed_of_band_singleton hdet' hN hM hband i j
/-! ## §10  §9 is not vacuous: a model of everything except `IsRegion`

PROTOCOL §10 applied to my own result.  `no_box_band_cone_region` would be worthless if its
*hypotheses* were unsatisfiable, so here is a model of all of them, with a **nonempty** `K`:

```
u = (1,0)   u' = (0,1)   n = 2   h = -(2 • u) = (-2,0)   B = {(0,0)}   t₁ = 0
w = (0,1)   w' = (2,0)   g₀ = (2,1)   N = M = 1
S = {(0,0), (0,-1), (-2,0)}   a = (0,0)      (three non-collinear points, §1's requirement)
K = {(2,1) + i • (2,0) + j • (0,1) : i, j ∈ ℕ}
```

The seed is `{(x, y) : x even, x ≥ 0, y ≥ 0}`; the band `(2 + 2p, 1 + q)` for `p, q ≥ -1` sits
inside it, and so does the whole cone.  Applying §9 gives a concrete nonempty set that provably
is **not** a region — that is the statement with content, and it is stated below rather than
left implicit.
-/

private def qS : Finset (ℤ × ℤ) := {(0, 0), (0, -1), (-2, 0)}
private def qB : Finset (ℤ × ℤ) := {(0, 0)}
private def qu : ℤ × ℤ := (1, 0)
private def qu' : ℤ × ℤ := (0, 1)
private def qw : ℤ × ℤ := (0, 1)
private def qw' : ℤ × ℤ := (2, 0)
private def qg₀ : ℤ × ℤ := (2, 1)
private def qK : Set (ℤ × ℤ) :=
  {z : ℤ × ℤ | ∃ i j : ℕ, z = qg₀ + (i : ℤ) • qw' + (j : ℤ) • qw}

/-- The seed here is `{(2ι, y) : ι ∈ ℕ, y ≥ 0}` — every point has **even, non-negative** first
coordinate.  That quantisation is exactly what §8 exploits. -/
private theorem mem_q_seed (i : ℕ) {y : ℤ} (hy : 0 ≤ y) :
    ((2 * (i : ℤ), y) : ℤ × ℤ) ∈ sweptSeed qB qu' 0 (-((2 : ℕ) • qu : ℤ × ℤ)) := by
  refine ⟨i, ((0, 0) : ℤ × ℤ), by simp [qB], y, hy, ?_⟩
  simp only [qu, qu', Prod.mk_add_mk, Prod.smul_mk, Prod.neg_mk, smul_eq_mul, Prod.ext_iff]
  constructor <;> ring

private theorem q_hSbox : ∀ b ∈ qS.erase ((0, 0) : ℤ × ℤ),
    ∃ k m : ℕ, k ≤ 1 ∧ m ≤ 1 ∧ 1 ≤ k + m ∧
      b = ((0, 0) : ℤ × ℤ) - (k : ℤ) • qw - (m : ℤ) • qw' := by
  intro b hb
  have hb' : b = ((0, -1) : ℤ × ℤ) ∨ b = ((-2, 0) : ℤ × ℤ) := by
    simp only [qS, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hb
    tauto
  rcases hb' with rfl | rfl
  · exact ⟨1, 0, le_refl 1, Nat.zero_le 1, by omega, by norm_num [qw, qw', Prod.ext_iff]⟩
  · exact ⟨0, 1, Nat.zero_le 1, le_refl 1, by omega, by norm_num [qw, qw', Prod.ext_iff]⟩

/-- The three points of `qS` are non-collinear, so §1's `1 ≤ N ∧ 1 ≤ M` is met honestly and
the model is not the degenerate run that `no_hSrun_of_nonCollinear` (`SweptSeed.lean:412`)
kills. -/
private theorem q_nonCollinear :
    ((0, 0) : ℤ × ℤ) ∈ qS ∧ ((0, -1) : ℤ × ℤ) ∈ qS ∧ ((-2, 0) : ℤ × ℤ) ∈ qS ∧
      det (((0, -1) : ℤ × ℤ) - (0, 0)) (((-2, 0) : ℤ × ℤ) - (0, 0)) ≠ 0 := by
  refine ⟨by simp [qS], by simp [qS], by simp [qS], ?_⟩
  norm_num [det]

private theorem q_hband : ∀ p q : ℤ, -((1 : ℕ) : ℤ) ≤ p → -((1 : ℕ) : ℤ) ≤ q →
    (p < 0 ∨ q < 0) →
    qg₀ + p • qw' + q • qw ∈ sweptSeed qB qu' 0 (-((2 : ℕ) • qu : ℤ × ℤ)) := by
  intro p q hp hq _
  have he : qg₀ + p • qw' + q • qw = ((2 * ((p + 1).toNat : ℤ), q + 1) : ℤ × ℤ) := by
    have hc : (((p + 1).toNat : ℕ) : ℤ) = p + 1 := Int.toNat_of_nonneg (by omega)
    simp only [qg₀, qw, qw', Prod.mk_add_mk, Prod.smul_mk, smul_eq_mul, Prod.ext_iff, hc]
    constructor <;> ring
  rw [he]
  exact mem_q_seed _ (by omega)

/-- **`no_box_band_cone_region`'s hypotheses are simultaneously satisfiable with a nonempty
`K`.**  So §9 is a genuine obstruction and not an empty implication. -/
theorem no_box_band_cone_region_nonvacuous :
    det qu qu' ≠ 0 ∧ qB.card < 2 ∧
      (∀ b ∈ qS.erase ((0, 0) : ℤ × ℤ), ∃ k m : ℕ, k ≤ 1 ∧ m ≤ 1 ∧ 1 ≤ k + m ∧
        b = ((0, 0) : ℤ × ℤ) - (k : ℤ) • qw - (m : ℤ) • qw') ∧
      (∀ p q : ℤ, -((1 : ℕ) : ℤ) ≤ p → -((1 : ℕ) : ℤ) ≤ q → (p < 0 ∨ q < 0) →
        qg₀ + p • qw' + q • qw ∈ sweptSeed qB qu' 0 (-((2 : ℕ) • qu : ℤ × ℤ))) ∧
      qK.Nonempty ∧
      qK ⊆ {z : ℤ × ℤ | ∃ i j : ℕ, z = qg₀ + (i : ℤ) • qw' + (j : ℤ) • qw} :=
  ⟨by norm_num [det, qu, qu'], by simp [qB], q_hSbox, q_hband,
    ⟨qg₀ + (0 : ℤ) • qw' + (0 : ℤ) • qw, 0, 0, rfl⟩, fun _ hz => hz⟩

/-- **The payoff, on a concrete nonempty set.**  `qK` is a nonempty quarter-cone that sits
inside a genuine `sweptSeed` over a one-point base with `n = 2`, satisfies `hband` for a
genuinely two-dimensional `qS`, and is **not** a region in the sense of `IsRegion`
(`Lemma41.lean:688`).

This is `no_box_band_cone_region` instantiated, i.e. the general theorem is what does the work;
the instance exists so that §9 cannot be dismissed as vacuous. -/
theorem not_isRegion_qK : ¬ IsRegion qK qu qu' :=
  no_box_band_cone_region (S := qS) (a := ((0, 0) : ℤ × ℤ)) (n := 2) (t₁ := 0)
    (by norm_num [det, qu, qu']) (by simp [qB]) le_rfl le_rfl
    (α := 1) (β := 0) (α' := 0) (β' := 1)
    (by norm_num [qw, qu', qu, Prod.ext_iff])
    (by norm_num [qw', qu', qu, Prod.ext_iff])
    q_hSbox q_hband (fun _ hz => hz)
/-! ## §11  `hsweep_of_box_of_cone` against `case1_sweep`, checked by unification

Last round I reported the comparison as "read off the signatures, never `exact`-ed".  This
section removes that caveat.  `case1_sweep`'s conclusion (`RegionSteps.lean:1074-1077`) is
transcribed **verbatim** below, and `Nivat.L3Cover.hsweep_of_box_of_cone` (`L3Cover.lean:317`)
is applied to it.  A transcription error would be a unification failure here, not a silent
mismatch.

Two things the compilation of `case1_sweep_conclusion_of_box_of_cone` establishes in the
kernel:

1. **The conclusions do match**, with `t₁ := τ + (pw : ℤ)` — that is the only wiring the
   half-strip parameter needs, since `case1_sweep`'s `hqper` antecedent reads `τ + pw ≤ t`.
2. **Twelve of `case1_sweep`'s thirteen hypotheses do not appear in the binder list below**,
   which is complete; `hξ'` is the only one that does.  Three of the twelve — `hSgen`,
   `hRper`, `hR_region` — could plausibly supply `hgen`, `hper` and `hseedR`, though that
   wiring is not done here.  The remaining **nine** (`hξ`, `hQS`, `hdet`, `hc`, `hu'_prim`,
   `hdef41`, `hline`, `hB_covers_window`, `hamb`) have no consumer on this route at all.
   What does appear, and is *not* among `case1_sweep`'s hypotheses, is the whole of the
   existential it is supposed to produce:
   `K`, `hKR`, `hKregion`, `hKne`, `t₀`, `ht₀` — plus `hgen`, `hSbox`, `hseedR`, `hper`,
   `hband`, `hKcone`.  §5 of `L3Cover.lean` produces exactly one of the four conjuncts of
   `case1_sweep`'s conclusion, the `PeriodOn` one, and takes the other three as input.

So this is **a block of real math, not a step of wiring** — and §12 says the block cannot be
completed along this route at the parameters L1 currently exports.

The *other* half of the transcription — that the text below really is `case1_sweep`'s
conclusion and not a look-alike — is machine-checked in `tmp/L3band_case1_sweep_shape.lean`
(**in `tmp/`, not landed**, and not landable: it discharges `case1_sweep`'s full signature by
`@Nivat.ColleReg.case1_sweep` itself, so it carries `sorryAx`).  The conclusion block there is
byte-identical to the one below, modulo whitespace.
-/

/-- **`case1_sweep`'s conclusion, verbatim, from the box/cone route.**

The conclusion is copied character-for-character from `RegionSteps.lean:1074-1077` (including
the `Colle41.` qualifications and the `((t₀ * q : ℕ) : ℤ)` cast); the proof is a single
application of `Nivat.L3Cover.hsweep_of_box_of_cone`.  See the section docstring for what the
binder list does and does not contain. -/
theorem case1_sweep_conclusion_of_box_of_cone
    {ξ ξ' : Config ℤ} (hξ' : ξ' ∈ orbitClosure ξ)
    {u u' : ℤ × ℤ} {τ : ℤ} {pw : ℕ} {B : Finset (ℤ × ℤ)} {R : Set (ℤ × ℤ)}
    {S : Finset (ℤ × ℤ)} {a : ℤ × ℤ} (hgen : Nivat.Colle.GeneratesAt ξ S a)
    {w w' : ℤ × ℤ} {N M : ℕ}
    (hSbox : ∀ b ∈ S.erase a, ∃ k m : ℕ, k ≤ N ∧ m ≤ M ∧ 1 ≤ k + m ∧
      b = a - (k : ℤ) • w - (m : ℤ) • w')
    {h g₀ : ℤ × ℤ}
    (hseedR : sweptSeed B u' (τ + (pw : ℤ)) h ⊆ R)
    (hper : ∀ z ∈ R, z + h ∈ R → ξ' (z + h) = ξ' z)
    (hband : ∀ p q : ℤ, -(M : ℤ) ≤ p → -(N : ℤ) ≤ q → (p < 0 ∨ q < 0) →
      g₀ + p • w' + q • w ∈ sweptSeed B u' (τ + (pw : ℤ)) h)
    {K : Set (ℤ × ℤ)} (hKR : K ⊆ R) (hKregion : IsRegion K u u') (hKne : K.Nonempty)
    (hKcone : K ⊆ {z : ℤ × ℤ | ∃ i j : ℕ, z = g₀ + (i : ℤ) • w' + (j : ℤ) • w})
    {t₀ : ℕ} (ht₀ : 0 < t₀) :
    ∀ q : ℕ, 0 < q →
      (∀ g ∈ B, ∀ t : ℤ, τ + (pw : ℤ) ≤ t → ξ' (g + (t + (q : ℤ)) • u') = ξ' (g + t • u')) →
      ∃ K : Set (ℤ × ℤ), K ⊆ R ∧ Colle41.IsRegion K u u' ∧ K.Nonempty ∧
        ∃ t₀ : ℕ, 0 < t₀ ∧ Colle41.PeriodOn ξ' K (((t₀ * q : ℕ) : ℤ) • u') := by
  intro q hq hqper
  exact Nivat.L3Cover.hsweep_of_box_of_cone hξ' hgen hSbox hseedR hper hband hKR hKregion
    hKne hKcone ht₀ hqper

/-! ## §12  The route cannot fire at L1's current parameters -/

/-- **At the L3 call site, with `B` a singleton and `2 ≤ n`, the box/cone route is dead.**

Same wiring as §11 (`t₁ := τ + (pw : ℤ)`, `h := -((n : ℤ) • u)` as `sweptSeed_subset_R`
demands), same `hband` and `hKcone`, and the conclusion is that `hKregion` — one of the inputs
§11 needs — cannot hold.  So `case1_sweep_conclusion_of_box_of_cone` has no instance at these
parameters, however `hSbox`, `hseedR` and `hper` are discharged.

`B = {g}` is what `Nivat.ColleReg.L1Data.ofEdgeRun` (`L1Fields.lean:154`) exports, and
`n` is the natural period multiplier that `exists_neg_nsmul_period` (`SweptSeed.lean:269`)
produces from `hRper`/`hc`; `n = 1` is the only surviving case. -/
theorem box_of_cone_route_dead_singleton
    {S : Finset (ℤ × ℤ)} {a : ℤ × ℤ} {g : ℤ × ℤ} {u u' : ℤ × ℤ} {τ : ℤ} {pw : ℕ} {n : ℕ}
    {w w' g₀ : ℤ × ℤ} {N M : ℕ} {K : Set (ℤ × ℤ)}
    (hdet : det u u' ≠ 0) (hn : 2 ≤ n) (hN : 1 ≤ N) (hM : 1 ≤ M)
    (hSbox : ∀ b ∈ S.erase a, ∃ k m : ℕ, k ≤ N ∧ m ≤ M ∧ 1 ≤ k + m ∧
      b = a - (k : ℤ) • w - (m : ℤ) • w')
    (hband : ∀ p q : ℤ, -(M : ℤ) ≤ p → -(N : ℤ) ≤ q → (p < 0 ∨ q < 0) →
      g₀ + p • w' + q • w ∈ sweptSeed {g} u' (τ + (pw : ℤ)) (-((n : ℤ) • u)))
    (hKcone : K ⊆ {z : ℤ × ℤ | ∃ i j : ℕ, z = g₀ + (i : ℤ) • w' + (j : ℤ) • w}) :
    ¬ IsRegion K u u' :=
  no_band_cone_region_singleton (S := S) (a := a) (t₁ := τ + (pw : ℤ))
    hdet hn hN hM hSbox hband hKcone

/-! ## §13  The converse: when *does* the swept seed contain a `u`-ray?

§8 (`card_le_of_rayIn_sweptSeed`) shows `n ≤ |B|` is **necessary**.  This section answers the
sufficiency question, which is what decides whether enlarging leaf L1's `B` revives the
box/cone route or not.

The answer, in one line: **`n ≤ |B|` is necessary but a cardinality hypothesis is never
sufficient.**  What *is* sufficient is that `B` contain a full set of `u`-step representatives
(`rayIn_sweptSeed_of_residues` below); §14 exhibits a `B` with `|B| = n = 2` and **no** `u`-ray
from any base point at all, so no theorem of the form `n ≤ B.card → ∃ ray` can exist. -/

/-- **`n` consecutive `u`-translates inside `B` build the `u`-ray.**

If `B ⊇ {g₀, g₀ + u, …, g₀ + (n-1) • u}` then `sweptSeed B u' t₁ (-((n : ℤ) • u))` contains the
whole `u`-ray based at `g₀ + t₁ • u'`.  Writing `k = q·n + r` with `r < n`, the point
`g₀ + t₁ • u' + k • u` returns to `g₀ + r • u + t₁ • u'` after `q` applications of
`h = -((n : ℤ) • u)`, and that point is in `halfStripFrom B u' t₁` because `g₀ + r • u ∈ B`.

No hypothesis on `u`, `u'` or `det u u'` is needed: the witness `(ι, g, t) = (k / n,
g₀ + (k % n) • u, t₁)` is explicit.  This is the exact converse of §8 and the two are
consistent — `card_le_of_residues` runs the round trip through both. -/
theorem rayIn_sweptSeed_of_residues {B : Finset (ℤ × ℤ)} {u u' g₀ : ℤ × ℤ} {t₁ : ℤ} {n : ℕ}
    (hn : 0 < n) (hB : ∀ r : ℕ, r < n → g₀ + (r : ℤ) • u ∈ B) :
    RayIn (sweptSeed B u' t₁ (-((n : ℤ) • u))) (g₀ + t₁ • u') u := by
  intro k
  refine ⟨k / n, g₀ + ((k % n : ℕ) : ℤ) • u, hB _ (Nat.mod_lt _ hn), t₁, le_rfl, ?_⟩
  have hk : (k : ℤ) = ((k / n : ℕ) : ℤ) * (n : ℤ) + ((k % n : ℕ) : ℤ) := by
    exact_mod_cast (Nat.div_add_mod' k n).symm
  rw [hk]
  module

/-- **The round trip: §13's sufficient condition implies §8's necessary one.**

Not new mathematics — `n` distinct points are staring at you — but it is the cheap check that
`rayIn_sweptSeed_of_residues` and `card_le_of_rayIn_sweptSeed` are talking about the same
object, which a hand-read comparison of two signatures cannot establish. -/
theorem card_le_of_residues {B : Finset (ℤ × ℤ)} {u u' g₀ : ℤ × ℤ} {t₁ : ℤ} {n : ℕ}
    (hdet : det u u' ≠ 0) (hn : 0 < n)
    (hB : ∀ r : ℕ, r < n → g₀ + (r : ℤ) • u ∈ B) : n ≤ B.card :=
  card_le_of_rayIn_sweptSeed (u' := u') (t₁ := t₁) hdet (rayIn_sweptSeed_of_residues hn hB)

/-! ## §14  `n ≤ |B|` alone is **not** sufficient

⚠ This section is a **counterexample at fixed parameters**, not a theorem about general
parameters — `n = 2`, `B = {(0,0), (2,0)}`, `u = (1,0)`, `u' = (0,1)`, `t₁ = 0`.  What it rules
out is general: a lemma of the shape `n ≤ B.card → ∃ z₀, RayIn (sweptSeed …) z₀ u` would apply
to these parameters and contradict `no_rayIn_cB_seed`, so no such lemma exists.

The mechanism is §8's determinant equation read as a congruence: the seed only ever displaces
along `u` in multiples of `n`, so the `n` residues mod `n` have to be supplied by `B` itself.
Here both points of `B` sit in the **same** residue class, so half of the ray is missing however
large the ray's base point is chosen. -/

private def cB : Finset (ℤ × ℤ) := {(0, 0), (2, 0)}

/-- **No base point whatsoever carries a `u`-ray inside the `cB` seed**, even though
`cB.card = 2 = n`. -/
theorem no_rayIn_cB_seed (z₀ : ℤ × ℤ) :
    ¬ RayIn (sweptSeed cB qu' 0 (-(((2 : ℕ) : ℤ) • qu))) z₀ qu := by
  intro hray
  have key : ∀ k : ℕ, ∃ m : ℤ, z₀.1 + (k : ℤ) = 2 * m := by
    intro k
    obtain ⟨g, hg, ι, heq⟩ := det_eq_of_mem_sweptSeed (hray k)
    have hg1 : g.1 = 0 ∨ g.1 = 2 := by
      simp only [cB, Finset.mem_insert, Finset.mem_singleton] at hg
      rcases hg with rfl | rfl <;> simp
    simp only [det, qu, qu'] at heq
    rcases hg1 with h | h
    · exact ⟨(ι : ℤ), by linear_combination heq + h⟩
    · exact ⟨(ι : ℤ) + 1, by linear_combination heq + h⟩
  obtain ⟨m0, h0⟩ := key 0
  obtain ⟨m1, h1⟩ := key 1
  push_cast at h0 h1
  omega

/-- **Cardinality is the wrong hypothesis.**  `|B| = n` with no `u`-ray anywhere. -/
theorem card_alone_insufficient :
    cB.card = 2 ∧ ¬ ∃ z₀ : ℤ × ℤ, RayIn (sweptSeed cB qu' 0 (-(((2 : ℕ) : ℤ) • qu))) z₀ qu := by
  refine ⟨by decide, ?_⟩
  rintro ⟨z₀, hz₀⟩
  exact no_rayIn_cB_seed z₀ hz₀

/-! ## §15  With `B` arranged right, all four §5 conditions **are** satisfiable

This is the positive answer to the question §9 leaves open, and it is stated to the same
standard §10 imposes on the negative answer: a **model**, every hypothesis discharged in the
kernel, nothing assumed.

Parameters (`n = 2`, `|B| = 2`, so `B.card < n` — §9's hypothesis — **fails**, and it is the
only thing that fails):

| object | value |
|---|---|
| `u`, `u'` | `qu = (1,0)`, `qu' = (0,1)`; `det u u' = 1` |
| `n`, `h` | `2`, `h = -((2 : ℤ) • u) = (-2,0)` |
| `B`, `t₁` | `mB = {(-1,0), (0,0)}`, `0` — two points **one `u`-step apart** |
| seed | `{(x,y) : -1 ≤ x, 0 ≤ y}` |
| `S`, `a` | `bdS = {(0,0), (0,-1), (-1,0)}` — three **non-collinear** points — and `a = (0,0)` |
| `N`, `M`, `w`, `w'` | `1`, `1`, `mw = (0,1)`, `mw' = (1,0)` |
| `g₀`, cone | `mg₀ = (0,1)`; cone `= {(i, 1+j) : i, j ∈ ℕ}` |
| `K` | `upperQuad = {z : 0 ≤ z.1, 1 ≤ z.2}` (`Claim43.lean:1047`) — equals the cone |

So the route is **not** dead as such: it is dead exactly on `B.card < n`, which is where leaf
L1 currently puts it (`L1Data`'s `B` field is instantiated as a singleton downstream).  §14 says
the fix is not "make `B` bigger" but "make `B` a full residue system along `u`" — here
`mB = {g₀ + r • u : r < 2}` with `g₀ = (-1,0)`, and `m_rayIn` is obtained from §13, not by hand.

⚠ Two things this does **not** say.  (i) It does not say leaf L1 can produce such a `B`:
conjunct 8 (`hBQ`, `L1Data.lean:116`) and conjunct 16 (`hbase`, `:136`) constrain `B` and are
not checked here — that is L1's question, not L3's.  (ii) It does not discharge `case1_sweep`:
§11 already measured that twelve of its thirteen hypotheses are absent from the box/cone
route's binder list. -/

private def mB : Finset (ℤ × ℤ) := {(-1, 0), (0, 0)}
/-- Within-row direction. -/
private def mw : ℤ × ℤ := (0, 1)
/-- Row-stepping direction. -/
private def mw' : ℤ × ℤ := (1, 0)
/-- Cone apex, chosen one `w`-step above the seed's boundary row so that `hband`'s points
(which sit *outside* the cone) still land inside the seed. -/
private def mg₀ : ℤ × ℤ := (0, 1)

/-- The `mB` seed is the half plane-ish quadrant `{(x,y) : -1 ≤ x ∧ 0 ≤ y}`. -/
private theorem mem_m_seed {p q : ℤ} (hp : -1 ≤ p) (hq : 0 ≤ q) :
    ((p, q) : ℤ × ℤ) ∈ sweptSeed mB qu' 0 (-(((2 : ℕ) : ℤ) • qu)) := by
  refine ⟨((p + 1) / 2).toNat, ((p - 2 * ((p + 1) / 2), 0) : ℤ × ℤ), ?_, q, hq, ?_⟩
  · have hcase : p - 2 * ((p + 1) / 2) = -1 ∨ p - 2 * ((p + 1) / 2) = 0 := by omega
    rcases hcase with h | h <;> simp [mB, Prod.ext_iff, h]
  · have hcast : ((((p + 1) / 2).toNat : ℕ) : ℤ) = (p + 1) / 2 :=
      Int.toNat_of_nonneg (by omega)
    simp only [qu, qu', Prod.mk_add_mk, Prod.smul_mk, Prod.neg_mk, smul_eq_mul, Prod.ext_iff,
      hcast, Nat.cast_ofNat]
    constructor <;> ring

/-- `hSbox` at the §15 parameters, with `bdS`'s three non-collinear points. -/
private theorem m_hSbox : ∀ b ∈ bdS.erase ((0, 0) : ℤ × ℤ),
    ∃ k m : ℕ, k ≤ 1 ∧ m ≤ 1 ∧ 1 ≤ k + m ∧
      b = ((0, 0) : ℤ × ℤ) - (k : ℤ) • mw - (m : ℤ) • mw' := by
  intro b hb
  have hb' : b = ((0, -1) : ℤ × ℤ) ∨ b = ((-1, 0) : ℤ × ℤ) := by
    simp only [bdS, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hb
    tauto
  rcases hb' with rfl | rfl
  · exact ⟨1, 0, le_refl 1, Nat.zero_le 1, by omega, by norm_num [mw, mw', Prod.ext_iff]⟩
  · exact ⟨0, 1, Nat.zero_le 1, le_refl 1, by omega, by norm_num [mw, mw', Prod.ext_iff]⟩

/-- `hband` at the §15 parameters. -/
private theorem m_hband : ∀ p q : ℤ, -((1 : ℕ) : ℤ) ≤ p → -((1 : ℕ) : ℤ) ≤ q →
    (p < 0 ∨ q < 0) → mg₀ + p • mw' + q • mw ∈ sweptSeed mB qu' 0 (-(((2 : ℕ) : ℤ) • qu)) := by
  intro p q hp hq _
  have hp' : (-1 : ℤ) ≤ p := by exact_mod_cast hp
  have hq' : (-1 : ℤ) ≤ q := by exact_mod_cast hq
  have he : mg₀ + p • mw' + q • mw = ((p, 1 + q) : ℤ × ℤ) := by
    simp only [mg₀, mw, mw', Prod.mk_add_mk, Prod.smul_mk, smul_eq_mul, Prod.ext_iff]
    constructor <;> ring
  rw [he]
  exact mem_m_seed hp' (by omega)

/-- `K = upperQuad` is exactly the cone `{g₀ + i • w' + j • w}`. -/
private theorem upperQuad_subset_mcone :
    upperQuad ⊆ {z : ℤ × ℤ | ∃ i j : ℕ, z = mg₀ + (i : ℤ) • mw' + (j : ℤ) • mw} := by
  intro z hz
  obtain ⟨hx, hy⟩ := hz
  refine ⟨z.1.toNat, (z.2 - 1).toNat, ?_⟩
  have h1 : ((z.1.toNat : ℕ) : ℤ) = z.1 := Int.toNat_of_nonneg hx
  have h2 : (((z.2 - 1).toNat : ℕ) : ℤ) = z.2 - 1 := Int.toNat_of_nonneg (by omega)
  simp only [mg₀, mw, mw', Prod.mk_add_mk, Prod.smul_mk, smul_eq_mul, Prod.ext_iff, h1, h2]
  constructor <;> ring

/-- `K ⊆ seed`, which is what §8 would have refuted had `|B| < n`. -/
private theorem upperQuad_subset_m_seed :
    upperQuad ⊆ sweptSeed mB qu' 0 (-(((2 : ℕ) : ℤ) • qu)) := by
  intro z hz
  obtain ⟨hx, hy⟩ := hz
  have hz' : z = ((z.1, z.2) : ℤ × ℤ) := rfl
  rw [hz']
  exact mem_m_seed (by omega) (by omega)

/-- The `u`-ray inside the seed, obtained from §13 rather than by hand:
`mB = {g₀ + r • u : r < 2}` with `g₀ = (-1,0)`. -/
private theorem m_rayIn :
    RayIn (sweptSeed mB qu' 0 (-(((2 : ℕ) : ℤ) • qu))) ((-1, 0) : ℤ × ℤ) qu := by
  have hres : ∀ r : ℕ, r < 2 → ((-1, 0) : ℤ × ℤ) + (r : ℤ) • qu ∈ mB := by
    intro r hr
    interval_cases r <;> norm_num [mB, qu, Prod.ext_iff]
  have h := rayIn_sweptSeed_of_residues (B := mB) (u := qu) (u' := qu') (t₁ := 0)
    (g₀ := ((-1, 0) : ℤ × ℤ)) (n := 2) (by norm_num) hres
  simpa using h

/-- **All four §5 conditions are simultaneously satisfiable, with `S` genuinely
two-dimensional, `K` nonempty, and `IsRegion K u u'` actually proved.**

Read against `no_box_band_cone_region` (§9): every one of its hypotheses holds here **except**
`B.card < n` (here `mB.card = 2 = n`).  So §9's hypothesis is not an artefact — it is the
whole obstruction, and it is sharp. -/
theorem box_band_cone_region_satisfiable :
    det qu qu' ≠ 0 ∧
      mB.card = 2 ∧
      (((0, 0) : ℤ × ℤ) ∈ bdS ∧ ((0, -1) : ℤ × ℤ) ∈ bdS ∧ ((-1, 0) : ℤ × ℤ) ∈ bdS ∧
        det (((0, -1) : ℤ × ℤ) - (0, 0)) (((-1, 0) : ℤ × ℤ) - (0, 0)) ≠ 0) ∧
      (∀ b ∈ bdS.erase ((0, 0) : ℤ × ℤ), ∃ k m : ℕ, k ≤ 1 ∧ m ≤ 1 ∧ 1 ≤ k + m ∧
        b = ((0, 0) : ℤ × ℤ) - (k : ℤ) • mw - (m : ℤ) • mw') ∧
      (∀ p q : ℤ, -((1 : ℕ) : ℤ) ≤ p → -((1 : ℕ) : ℤ) ≤ q → (p < 0 ∨ q < 0) →
        mg₀ + p • mw' + q • mw ∈ sweptSeed mB qu' 0 (-(((2 : ℕ) : ℤ) • qu))) ∧
      upperQuad ⊆ {z : ℤ × ℤ | ∃ i j : ℕ, z = mg₀ + (i : ℤ) • mw' + (j : ℤ) • mw} ∧
      upperQuad.Nonempty ∧
      IsRegion upperQuad qu qu' ∧
      upperQuad ⊆ sweptSeed mB qu' 0 (-(((2 : ℕ) : ℤ) • qu)) ∧
      RayIn (sweptSeed mB qu' 0 (-(((2 : ℕ) : ℤ) • qu))) ((-1, 0) : ℤ × ℤ) qu :=
  ⟨by norm_num [det, qu, qu'], by decide, bdS_nonCollinear, m_hSbox, m_hband,
    upperQuad_subset_mcone, upperQuad_nonempty, isRegion_upperQuad, upperQuad_subset_m_seed,
    m_rayIn⟩

/-! ## §16  The `n = 1` hole, closed — positively

The gap left open in §8–§9 was `n ≤ B.card`, and in particular `n = 1` (Collé's `c = ±1`),
where a **singleton** `B` already satisfies §13's residue condition vacuously-but-really
(`r < 1` means `r = 0`, so `g₀ ∈ B` is the whole requirement).  So the `n = 1` case should be
satisfiable for the same reason §15 is, and it is: the §2 witness, which was only ever checked
against `hSbox ∧ hband`, extends to a full model once `K` is supplied.

Parameters: `u = bdu = (1,0)`, `u' = bdu' = (0,1)`, `n = 1`, `h = bdh = (-1,0)`,
`B = bdB = {(-1,-1)}`, `t₁ = 0`, seed `= {(x,y) : -1 ≤ x ∧ -1 ≤ y}`,
`S = bdS` (three non-collinear points), `a = (0,0)`, `N = M = 1`, `g₀ = (0,0)`,
cone `= {(i,j) : i, j ∈ ℕ}`, and `K = upperQuad ⊊` cone.

**Consequence for the leaf.**  Combining §9, §15 and §16: the four §5 conditions are
satisfiable at `n = 1` with `|B| = 1`, satisfiable at `n = 2` with `|B| = 2` arranged along
`u`, and **un**satisfiable at `n = 2` with `|B| = 1`.  `B.card < n` is therefore the exact
dividing line, and nothing else about §5 is obstructed. -/

/-- The ray at `n = 1`, again from §13 rather than by hand: `bdB = {g₀}` with `g₀ = (-1,-1)`
is already a full residue system when `n = 1`. -/
private theorem bd_rayIn :
    RayIn (sweptSeed bdB bdu' 0 bdh) ((-1, -1) : ℤ × ℤ) bdu := by
  have hh : bdh = -(((1 : ℕ) : ℤ) • bdu) := by norm_num [bdh, bdu, Prod.ext_iff]
  have hres : ∀ r : ℕ, r < 1 → ((-1, -1) : ℤ × ℤ) + (r : ℤ) • bdu ∈ bdB := by
    intro r hr
    interval_cases r
    norm_num [bdB, bdu, Prod.ext_iff]
  have h := rayIn_sweptSeed_of_residues (B := bdB) (u := bdu) (u' := bdu') (t₁ := 0)
    (g₀ := ((-1, -1) : ℤ × ℤ)) (n := 1) (by norm_num) hres
  rw [hh]
  simpa using h

/-- `upperQuad` sits inside the `n = 1` cone `{(i,j) : i, j ∈ ℕ}`. -/
private theorem upperQuad_subset_bdcone :
    upperQuad ⊆ {z : ℤ × ℤ | ∃ i j : ℕ, z = ((0, 0) : ℤ × ℤ) + (i : ℤ) • bdw' + (j : ℤ) • bdw} := by
  intro z hz
  obtain ⟨hx, hy⟩ := hz
  refine ⟨z.1.toNat, z.2.toNat, ?_⟩
  have h1 : ((z.1.toNat : ℕ) : ℤ) = z.1 := Int.toNat_of_nonneg hx
  have h2 : ((z.2.toNat : ℕ) : ℤ) = z.2 := Int.toNat_of_nonneg (by omega)
  simp only [bdw, bdw', Prod.mk_add_mk, Prod.smul_mk, smul_eq_mul, Prod.ext_iff, h1, h2]
  constructor <;> ring

/-- `upperQuad` also sits inside the `n = 1` seed. -/
private theorem upperQuad_subset_bd_seed : upperQuad ⊆ sweptSeed bdB bdu' 0 bdh := by
  intro z hz
  obtain ⟨hx, hy⟩ := hz
  have hz' : z = ((z.1, z.2) : ℤ × ℤ) := rfl
  rw [hz']
  exact mem_bd_seed (by omega) (by omega)

/-- **The `n = 1` case is satisfiable too**, to the same standard as §15: every conjunct
proved, `S` non-collinear, `K` nonempty, `IsRegion K u u'` in the kernel. -/
theorem box_band_cone_region_satisfiable_n_eq_one :
    det bdu bdu' ≠ 0 ∧
      bdB.card = 1 ∧
      bdh = -(((1 : ℕ) : ℤ) • bdu) ∧
      (((0, 0) : ℤ × ℤ) ∈ bdS ∧ ((0, -1) : ℤ × ℤ) ∈ bdS ∧ ((-1, 0) : ℤ × ℤ) ∈ bdS ∧
        det (((0, -1) : ℤ × ℤ) - (0, 0)) (((-1, 0) : ℤ × ℤ) - (0, 0)) ≠ 0) ∧
      (∀ b ∈ bdS.erase ((0, 0) : ℤ × ℤ), ∃ k m : ℕ, k ≤ 1 ∧ m ≤ 1 ∧ 1 ≤ k + m ∧
        b = ((0, 0) : ℤ × ℤ) - (k : ℤ) • bdw - (m : ℤ) • bdw') ∧
      (∀ p q : ℤ, -((1 : ℕ) : ℤ) ≤ p → -((1 : ℕ) : ℤ) ≤ q → (p < 0 ∨ q < 0) →
        ((0, 0) : ℤ × ℤ) + p • bdw' + q • bdw ∈ sweptSeed bdB bdu' 0 bdh) ∧
      upperQuad ⊆ {z : ℤ × ℤ | ∃ i j : ℕ, z = ((0, 0) : ℤ × ℤ) + (i : ℤ) • bdw' + (j : ℤ) • bdw} ∧
      upperQuad.Nonempty ∧
      IsRegion upperQuad bdu bdu' ∧
      upperQuad ⊆ sweptSeed bdB bdu' 0 bdh ∧
      RayIn (sweptSeed bdB bdu' 0 bdh) ((-1, -1) : ℤ × ℤ) bdu :=
  ⟨by norm_num [det, bdu, bdu'], by decide, by norm_num [bdh, bdu, Prod.ext_iff],
    bdS_nonCollinear, bd_hSbox, bd_hband, upperQuad_subset_bdcone, upperQuad_nonempty,
    isRegion_upperQuad, upperQuad_subset_bd_seed, bd_rayIn⟩

/-! ## §17  The `hseedR` / `hper` wiring, measured

Item 3: are `hsweep_of_box_of_cone`'s `hseedR` and `hper` (`L3Cover.lean:324-325`) wiring, or
real inputs?  Measured against `case1_sweep`'s **own** hypothesis list, transcribed from
`RegionSteps.lean:1054-1072`:

    hξ  hSgen  hξ'  hQS  hdet  hc  hu'_prim  hdef41  hline  hRper  hR_region
    hB_covers_window  hamb

**`hper` wires.**  It is `Colle41.PeriodOn ξ' R h` unfolded (`Lemma41.lean:659`), and
`exists_neg_nsmul_period` (`SweptSeed.lean:269`) turns `hc : c ≠ 0` plus
`hRper : PeriodOn ξ' R (c • u)` — **both present** — into `∃ n, 0 < n ∧ PeriodOn ξ' R
(-((n : ℤ) • u))`.  That is the whole wiring; `hper_of_hRper` below is the one-line check.

**`hseedR` does not wire.**  `sweptSeed_subset_R` (`SweptSeed.lean:255`) reduces it to
`halfStripFrom B u' (τ + pw) ⊆ R`, and `halfStripFrom_subset_R` (`SweptSeed.lean:304`) reduces
*that* to two things:

1. `B ⊆ Q`, available only through `subset_Q_of_hline` (`SweptSeed.lean:319`), which consumes
   **`0 < pw`** — not in the list above.  (This is the known L1 debt, `LEAF-L3.md`.)
2. `hQR : ∀ t, τ ≤ t → ∀ z ∈ Q, t • u' + z ∈ R ∧ t • u' + z + c • u ∈ R` — **not in the list
   above at all.**  It is L1's conjunct 14 (`L1Data.lean:128`), so L1 does produce it, but
   `case1_sweep`'s signature never receives it.

⚠ **Absence from a binder list is not underivability**, and this file does not claim it is.
What was checked is that nothing else in the list links `Q` to `R`: `hamb` is
`SemiAmbiguousAlong` (`Lemma41.lean:540-544`), whose unfolding mentions `η`, `x`, `S`, `Q`,
`u'`, `τ` and **no** `R`; `hQS` is `Q ⊆ S`; and `hB_covers_window` is
`∃ b ∈ B, ∀ z ∈ S, b + z ∈ R`, which pins **finitely many** points of `R` while
`halfStripFrom B u' t₁` is unbounded in `t`.  Upward closure along `u'` (`ray_all_of_rayIn`,
`SweptSeed.lean:231`) does extend a point of `R` along `+u'`, but it extends it from the point
it is given, and `hB_covers_window` gives no point of the form `b + t • u'`.

`case1_sweep_conclusion_wired` is the positive half made kernel-checkable: it keeps `hc`,
`hRper`, `hR_region`, `hline` **verbatim** from `case1_sweep`, adds exactly `hpw` and `hQR`,
and produces `case1_sweep`'s conclusion verbatim.  Its binder list is therefore the precise
statement of what the box/cone route still needs. -/

/-- **`hper` is wiring**: `exists_neg_nsmul_period` at `hsweep_of_box_of_cone`'s `hper` shape,
which is `PeriodOn` unfolded.  Both inputs are in `case1_sweep`'s hypothesis list. -/
theorem hper_of_hRper {ξ' : Config ℤ} {R : Set (ℤ × ℤ)} {u : ℤ × ℤ} {c : ℤ}
    (hc : c ≠ 0) (hRper : PeriodOn ξ' R (c • u)) :
    ∃ n : ℕ, 0 < n ∧
      ∀ z ∈ R, z + -((n : ℤ) • u) ∈ R → ξ' (z + -((n : ℤ) • u)) = ξ' z :=
  exists_neg_nsmul_period hc hRper

/-- **`hseedR` is wiring only once `0 < pw` and `hQR` are supplied.**  Neither is in
`case1_sweep`'s hypothesis list; `hQR` is L1's conjunct 14 (`L1Data.lean:128`).

The `t₁ := τ + pw` shift is free: `hQR` at `τ` implies `hQR` at `τ + pw` because `pw : ℕ`. -/
theorem hseedR_of_hQR {R : Set (ℤ × ℤ)} {u u' : ℤ × ℤ} {B Q : Finset (ℤ × ℤ)} {τ : ℤ} {pw : ℕ}
    {c : ℤ} (hR_region : IsRegion R u u') (n : ℕ) (hpw : 0 < pw)
    (hline : ∀ g ∈ B, ∀ i : ℕ, i < pw → g + (i : ℤ) • u' ∈ Q)
    (hQR : ∀ t : ℤ, τ ≤ t → ∀ z ∈ Q, t • u' + z ∈ R ∧ t • u' + z + c • u ∈ R) :
    sweptSeed B u' (τ + (pw : ℤ)) (-((n : ℤ) • u)) ⊆ R :=
  sweptSeed_subset_R hR_region n
    (halfStripFrom_subset_R (c := c) (u := u) (subset_Q_of_hline hpw hline)
      (fun t ht z hz => hQR t (by omega) z hz))

/-- **`case1_sweep`'s conclusion from the box/cone route with `hseedR` and `hper` wired.**

Compare `case1_sweep_conclusion_of_box_of_cone` (§11), which *assumes* `hseedR` and `hper`.
Here they are gone: `hper` is produced from `hc` + `hRper`, and `hseedR` from `hR_region` +
`hline` + the two extra inputs `hpw` and `hQR`.  The conclusion block is byte-identical to
§11's, which is byte-identical to `case1_sweep`'s (`RegionSteps.lean:1074-1077`).

`hband` is quantified over the `n` that `exists_neg_nsmul_period` returns, because the sweep
direction `h = -((n : ℤ) • u)` is not known until `hc` and `hRper` are consumed.  That is not a
weakening for bookkeeping's sake: `hband` genuinely has to hold for whatever period multiple
the region supplies.

**What is still missing, read off this binder list**: `hgen`, `hSbox`, `hband`, `hKR`,
`hKregion`, `hKne`, `hKcone`, `ht₀` (the geometric content §11 already flagged), plus `hpw` and
`hQR` (the two `hseedR` needs).  Ten inputs, not two. -/
theorem case1_sweep_conclusion_wired
    {ξ ξ' : Config ℤ} (hξ' : ξ' ∈ orbitClosure ξ)
    {u u' : ℤ × ℤ} {Q : Finset (ℤ × ℤ)} {τ : ℤ} {pw : ℕ} {B : Finset (ℤ × ℤ)}
    {R : Set (ℤ × ℤ)} {c : ℤ}
    (hc : c ≠ 0)
    (hline : ∀ g ∈ B, ∀ i : ℕ, i < pw → g + (i : ℤ) • u' ∈ Q)
    (hRper : Colle41.PeriodOn ξ' R (c • u))
    (hR_region : Colle41.IsRegion R u u')
    (hpw : 0 < pw)
    (hQR : ∀ t : ℤ, τ ≤ t → ∀ z ∈ Q, t • u' + z ∈ R ∧ t • u' + z + c • u ∈ R)
    {S : Finset (ℤ × ℤ)} {a : ℤ × ℤ} (hgen : Nivat.Colle.GeneratesAt ξ S a)
    {w w' g₀ : ℤ × ℤ} {N M : ℕ}
    (hSbox : ∀ b ∈ S.erase a, ∃ k m : ℕ, k ≤ N ∧ m ≤ M ∧ 1 ≤ k + m ∧
      b = a - (k : ℤ) • w - (m : ℤ) • w')
    (hband : ∀ n : ℕ, 0 < n → Colle41.PeriodOn ξ' R (-((n : ℤ) • u)) →
      ∀ p q : ℤ, -(M : ℤ) ≤ p → -(N : ℤ) ≤ q → (p < 0 ∨ q < 0) →
        g₀ + p • w' + q • w ∈ sweptSeed B u' (τ + (pw : ℤ)) (-((n : ℤ) • u)))
    {K : Set (ℤ × ℤ)} (hKR : K ⊆ R) (hKregion : Colle41.IsRegion K u u') (hKne : K.Nonempty)
    (hKcone : K ⊆ {z : ℤ × ℤ | ∃ i j : ℕ, z = g₀ + (i : ℤ) • w' + (j : ℤ) • w})
    {t₀ : ℕ} (ht₀ : 0 < t₀) :
    ∀ q : ℕ, 0 < q →
      (∀ g ∈ B, ∀ t : ℤ, τ + (pw : ℤ) ≤ t → ξ' (g + (t + (q : ℤ)) • u') = ξ' (g + t • u')) →
      ∃ K : Set (ℤ × ℤ), K ⊆ R ∧ Colle41.IsRegion K u u' ∧ K.Nonempty ∧
        ∃ t₀ : ℕ, 0 < t₀ ∧ Colle41.PeriodOn ξ' K (((t₀ * q : ℕ) : ℤ) • u') := by
  intro q hq hqper
  obtain ⟨n, hn, hnper⟩ := exists_neg_nsmul_period hc hRper
  exact Nivat.L3Cover.hsweep_of_box_of_cone hξ' hgen hSbox
    (hseedR_of_hQR hR_region n hpw hline hQR) hnper (hband n hn hnper) hKR hKregion hKne
    hKcone ht₀ hqper

/-! ## §19  The call site: `hQR` is already in scope, `0 < pw` is not

§17 measured that `hseedR` needs two inputs `case1_sweep` does not have.  This section checks
where those two inputs actually sit, at `case1_sweep`'s one call site
(`region_case1`, `RegionSteps.lean:1167`), and the two answers are opposite.

**`hQR` is free.**  `region_case1` destructures L1's export at `RegionSteps.lean:1155-1158`,
and the `obtain` pattern binds `hQR` **by that name** — it is L1's conjunct 14
(`L1Data.lean:128`).  It is already consumed one line down by
`case1_claim47_semiAmbiguous` (`:1163`).  It is simply **not passed** to `case1_sweep`
(`:1167`).  So routing it in is a signature edit with the term already in scope: zero
mathematics, and `hseedR`'s first obstruction disappears.

⚠ I cannot make that edit — `RegionSteps.lean` is not my file — and this paragraph is a
**reading of the call site**, not a compiled fact; what is compiled is everything downstream of
assuming `hQR`, which is `case1_sweep_of_box_of_cone_callsite` below.

**`0 < pw` is not free.**  `pw` is bound at `:1156` with no positivity anywhere in scope, and
`L1Fields.lean:754` records the same fact independently ("binds `{pw : ℕ}` with no
positivity").  This one is a real open debt and it belongs to L1, not L3.

> **2026-09-19 status change (kept per `PROTOCOL.md` §14): superseded.**  `0 < pw` *is* free
> at the call site — `Nivat.ColleStep.pos_pw_of_case1_hyps` (`RegionSteps.lean:1185`, not
> this file, not imported here) derives it from `hξ.1.1`, `hξ'`, `hQS`, `hdef41`, `hline`,
> `hB_covers_window` and `hamb`, because `wordsFrom y τ 0` is a singleton and Claim 4.2's count
> then contradicts `hdef` + `hamb` at `pw = 0`.  The `hpw` binders of §17, §19 and §22 below
> are therefore dischargeable at the call site; they are left as they are because those three
> sections belong to the box/cone route, which §12 and §21 already showed cannot fire.
> Nothing in §23–§30 takes `pw` at all.

**`hSgen` is not dead weight either.**  `IsGeneratingSet` (`Generating.lean:58-60`) is
`S.Nonempty ∧ LatticeConvex S ∧ ∀ a ∈ S, LatticeConvex (S.erase a) → GeneratesAt ξ S a`, so it
*produces* the box/cone route's `hgen`, given `a ∈ S` and `LatticeConvex (S.erase a)` — the
same two side conditions `region_case1` itself discharges at `RegionSteps.lean:1040`.
`hgen_of_hSgen` below is that one line, compiled.

### The remaining seven, classified

After §17 and `hgen_of_hSgen`, the box/cone route consumes `hξ'`, `hc`, `hline`, `hRper`,
`hR_region`, `hSgen`.  Unconsumed: `hξ`, `hQS`, `hdet`, `hu'_prim`, `hdef41`,
`hB_covers_window`, `hamb`.

**None of them is dead weight in the signature.**  They are the input set of *Collé's* proof of
the sweep (the pigeonhole of `b3_colle2.txt:700` plus the line-by-line sweep of Claim 4.3,
`:680-698`), and four of them have a consumer already proved in this repo:
`wordsFrom_ncard_le_of_semiAmbiguous` (`Lemma41.lean:550-556`) takes `hQS`, `hdef` (which is
`hdef41` verbatim), `hline` and `hamb`.  `hu'_prim` is consumed by Claim 4.3's lattice-point
walk and by `exists_face_end_data_gen`'s `Primitive d` (`Claim47Core.lean:159`), as
`case1_sweep`'s own comment at `RegionSteps.lean:1064-1069` records.  `hdet` is consumed by
`lemma41_colle_region_shape` at the outer level (`:1171`) — and, on this file's side, by §8.

So the honest reading of "nine hypotheses with no consumer" is **not** "the signature is
bloated".  It is: **the box/cone route is a different proof, not a partial wiring of Collé's.**
It replaces the counting argument rather than using it, which is why it drops the counting
inputs and picks up `hSbox`/`hband`/`hKcone` instead.  The decision in front of L3 is therefore
a choice between two proofs, not a question of how much of one is wired.

**`hξ` is the one worth calling out separately.**  `case1_sweep` assumes
`IsMinimalCounterexample ξ`; the box/cone route does not, and nothing below takes it.  Per
`PROTOCOL.md`'s two-layer note, a proposition carrying `hξ` can be true vacuously; everything
in this file is free of it, so none of it is vacuous for that reason. -/

/-- **`hSgen` produces `hgen`.**  `IsGeneratingSet.2.2` at the two side conditions
`region_case1` already discharges for itself (`RegionSteps.lean:1040`). -/
theorem hgen_of_hSgen {ξ : Config ℤ} {S : Finset (ℤ × ℤ)}
    (hSgen : Nivat.Colle.IsGeneratingSet ξ S) {a : ℤ × ℤ} (haS : a ∈ S)
    (hconv : LatticeConvex (S.erase a)) : Nivat.Colle.GeneratesAt ξ S a :=
  hSgen.2.2 a haS hconv

/-- **`case1_sweep`'s conclusion in call-site shape.**

Every hypothesis below other than the box/cone block is either verbatim from `case1_sweep`
(`hξ'`, `hSgen`, `hc`, `hline`, `hRper`, `hR_region`) or in scope at its call site (`hQR`,
`RegionSteps.lean:1156`; `haS`/`hconv`, discharged at `:1040`).  The single hypothesis that is
neither is **`hpw : 0 < pw`**.

Together with §17 this is the precise residual of the box/cone route:

* free at the call site — `hQR`, `haS`, `hconv`;
* open debt on L1 — `hpw`;
* real geometry with no producer — `hSbox`, `hband`, `hKR`, `hKregion`, `hKne`, `hKcone`,
  `ht₀`;
* not needed at all — `hξ`, `hQS`, `hdet`, `hu'_prim`, `hdef41`, `hB_covers_window`, `hamb`.

The conclusion block is byte-identical to `case1_sweep`'s (`RegionSteps.lean:1074-1077`);
three-way checked against §11 and §17. -/
theorem case1_sweep_of_box_of_cone_callsite
    {ξ ξ' : Config ℤ} (hξ' : ξ' ∈ orbitClosure ξ)
    {u u' : ℤ × ℤ} {Q : Finset (ℤ × ℤ)} {τ : ℤ} {pw : ℕ} {B : Finset (ℤ × ℤ)}
    {R : Set (ℤ × ℤ)} {c : ℤ}
    {S : Finset (ℤ × ℤ)} (hSgen : Nivat.Colle.IsGeneratingSet ξ S)
    {a : ℤ × ℤ} (haS : a ∈ S) (hconv : LatticeConvex (S.erase a))
    (hc : c ≠ 0)
    (hline : ∀ g ∈ B, ∀ i : ℕ, i < pw → g + (i : ℤ) • u' ∈ Q)
    (hRper : Colle41.PeriodOn ξ' R (c • u))
    (hR_region : Colle41.IsRegion R u u')
    (hQR : ∀ t : ℤ, τ ≤ t → ∀ z ∈ Q, t • u' + z ∈ R ∧ t • u' + z + c • u ∈ R)
    (hpw : 0 < pw)
    {w w' g₀ : ℤ × ℤ} {N M : ℕ}
    (hSbox : ∀ b ∈ S.erase a, ∃ k m : ℕ, k ≤ N ∧ m ≤ M ∧ 1 ≤ k + m ∧
      b = a - (k : ℤ) • w - (m : ℤ) • w')
    (hband : ∀ n : ℕ, 0 < n → Colle41.PeriodOn ξ' R (-((n : ℤ) • u)) →
      ∀ p q : ℤ, -(M : ℤ) ≤ p → -(N : ℤ) ≤ q → (p < 0 ∨ q < 0) →
        g₀ + p • w' + q • w ∈ sweptSeed B u' (τ + (pw : ℤ)) (-((n : ℤ) • u)))
    {K : Set (ℤ × ℤ)} (hKR : K ⊆ R) (hKregion : Colle41.IsRegion K u u') (hKne : K.Nonempty)
    (hKcone : K ⊆ {z : ℤ × ℤ | ∃ i j : ℕ, z = g₀ + (i : ℤ) • w' + (j : ℤ) • w})
    {t₀ : ℕ} (ht₀ : 0 < t₀) :
    ∀ q : ℕ, 0 < q →
      (∀ g ∈ B, ∀ t : ℤ, τ + (pw : ℤ) ≤ t → ξ' (g + (t + (q : ℤ)) • u') = ξ' (g + t • u')) →
      ∃ K : Set (ℤ × ℤ), K ⊆ R ∧ Colle41.IsRegion K u u' ∧ K.Nonempty ∧
        ∃ t₀ : ℕ, 0 < t₀ ∧ Colle41.PeriodOn ξ' K (((t₀ * q : ℕ) : ℤ) • u') :=
  case1_sweep_conclusion_wired hξ' hc hline hRper hR_region hpw hQR
    (hgen_of_hSgen hSgen haS hconv) hSbox hband hKR hKregion hKne hKcone ht₀

/-! ## §20  `hKcone ∧ hKregion` forces `(w, w')` unimodular

`case1_sweep_of_box_of_cone_callsite` (§19) takes the geometric block `hKregion : IsRegion K u u'`,
`hKne : K.Nonempty`, `hKcone : K ⊆ {g₀ + i • w' + j • w}`.  Nobody had priced these three
*jointly*.  This section does: a nonempty lattice-convex region with rays `u`, `u'` contains
every lattice point of a real quadrant `z₀ + ℝ≥0 u + ℝ≥0 u'` (§20a), and those lattice points
generate `ℤ²` as a group; so if they all lie in the coset `g₀ + ℤw + ℤw'` then
`ℤw + ℤw' = ℤ²`, i.e. **`det w w' = ±1`** (§20b).

Consequences (§21): with `w, w'` `ℕ`-combinations of `u'` and `n • u` — which §7 shows `hband`
*forces* at `|B| = 1` — `det w w' = n · (αβ' − α'β) · det u' u`, so `|det w w'| = 1` gives
**`n = 1` and `|det u u'| = 1`**.  `case1_sweep`'s only determinant hypothesis is
`hdet : det u u' ≠ 0` (`RegionSteps.lean:1103`), and `n` is `|c|` for a period `c` nothing bounds.
So at L1's current `B = {g}` the box/cone route can fire **only** when both the period along `u`
is `±u` and `(u, u')` is a lattice basis.  §12 already had the first condition; the second is
new, and it is independent of `n`. -/

/-- **Lattice points of the real cone at `z₀` are in `K`.**  `IsRegion K u u'` puts `toReal u`
and `toReal u'` in `recCone K` (`toReal_mem_recCone_of_nat_ray`), the cone is closed under
non-negative real combinations (`smul_mem_recCone`, `add_mem_recCone`), and a lattice-convex
region absorbs its recession directions (`add_mem_of_mem_recCone`). -/
theorem mem_of_nonneg_real_comb {K : Set (ℤ × ℤ)} {u u' : ℤ × ℤ}
    (hK : IsRegion K u u') {z₀ : ℤ × ℤ} (hz₀ : z₀ ∈ K)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) {p : ℤ × ℤ}
    (hp : toReal p = a • toReal u + b • toReal u') : z₀ + p ∈ K := by
  obtain ⟨hconv, ⟨z₁, hray⟩, ⟨z₁', hray'⟩⟩ := hK
  have hu : toReal u ∈ recCone K := toReal_mem_recCone_of_nat_ray hray
  have hu' : toReal u' ∈ recCone K := toReal_mem_recCone_of_nat_ray hray'
  have hp' : toReal p ∈ recCone K := by
    rw [hp]
    exact add_mem_recCone (smul_mem_recCone ha hu) (smul_mem_recCone hb hu')
  exact add_mem_of_mem_recCone hconv hp' hz₀

/-- Cramer's rule in `ℤ²`, as the identity used below: `D • e = (det e u') • u + (det u e) • u'`
with `D = det u u'`, read off coordinatewise. -/
private theorem cramer_fst (u u' e : ℤ × ℤ) :
    det e u' * u.1 + det u e * u'.1 = e.1 * det u u' := by
  simp only [det]; ring

private theorem cramer_snd (u u' e : ℤ × ℤ) :
    det e u' * u.2 + det u e * u'.2 = e.2 * det u u' := by
  simp only [det]; ring

/-- **Every lattice vector `e` is reached from `z₀` inside `K` after a large enough push along
`u + u'`.**  With `m ≥ |det e u'| + |det u e|` the point `m • (u + u') + e` is
`(m + det e u' / D) • u + (m + det u e / D) • u'` with both real coefficients `≥ 0`. -/
theorem exists_nsmul_add_mem {K : Set (ℤ × ℤ)} {u u' : ℤ × ℤ} (hdet : det u u' ≠ 0)
    (hK : IsRegion K u u') {z₀ : ℤ × ℤ} (hz₀ : z₀ ∈ K) (e : ℤ × ℤ) :
    ∃ m : ℕ, z₀ + ((m : ℤ) • (u + u') + e) ∈ K := by
  set A : ℤ := det e u' with hA
  set B : ℤ := det u e with hB
  set D : ℤ := det u u' with hD
  refine ⟨A.natAbs + B.natAbs, ?_⟩
  set m : ℕ := A.natAbs + B.natAbs with hm
  have hDr : (D : ℝ) ≠ 0 := by exact_mod_cast hdet
  have hDabs : (1 : ℝ) ≤ |(D : ℝ)| := by
    have := Int.one_le_abs hdet
    exact_mod_cast this
  have hmA : |(A : ℝ)| ≤ (m : ℝ) := by
    have h1 : (A.natAbs : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.le_add_right _ _
    rwa [Nat.cast_natAbs, Int.cast_abs] at h1
  have hmB : |(B : ℝ)| ≤ (m : ℝ) := by
    have h1 : (B.natAbs : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.le_add_left _ _
    rwa [Nat.cast_natAbs, Int.cast_abs] at h1
  have hbound : ∀ X : ℝ, |X| ≤ (m : ℝ) → 0 ≤ (m : ℝ) + X / (D : ℝ) := by
    intro X hX
    have h1 : |X / (D : ℝ)| ≤ (m : ℝ) := by
      rw [abs_div]
      exact (div_le_self (abs_nonneg _) hDabs).trans hX
    linarith [neg_abs_le (X / (D : ℝ))]
  refine mem_of_nonneg_real_comb hK hz₀ (a := (m : ℝ) + (A : ℝ) / (D : ℝ))
    (b := (m : ℝ) + (B : ℝ) / (D : ℝ)) (hbound _ hmA) (hbound _ hmB) ?_
  have hc1 := cramer_fst u u' e
  have hc2 := cramer_snd u u' e
  rw [← hA, ← hB, ← hD] at hc1 hc2
  have hc1r : (A : ℝ) * u.1 + (B : ℝ) * u'.1 = e.1 * (D : ℝ) := by exact_mod_cast hc1
  have hc2r : (A : ℝ) * u.2 + (B : ℝ) * u'.2 = e.2 * (D : ℝ) := by exact_mod_cast hc2
  refine Prod.ext ?_ ?_
  · simp only [toReal, Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd, smul_eq_mul]
    push_cast
    field_simp
    linear_combination (-1 : ℝ) * hc1r
  · simp only [toReal, Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd, smul_eq_mul]
    push_cast
    field_simp
    linear_combination (-1 : ℝ) * hc2r

private theorem det_comb (a b c d : ℤ) (x y : ℤ × ℤ) :
    det (a • x + b • y) (c • x + d • y) = (a * d - b * c) * det x y := by
  simp only [det, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- **A nonempty `(u, u')`-region inside the sublattice cone `g₀ + ℕw' + ℕw` forces
`det w w' = ±1`.**

Only `hKcone`, `hKregion`, `hKne` and `hdet` are consumed — none of `hSbox`, `hband`, or the
configuration.  So this is a price the box/cone route pays *before* any of its sweep hypotheses
are even stated. -/
theorem det_eq_pm_one_of_region_subset_cone {K : Set (ℤ × ℤ)} {u u' w w' g₀ : ℤ × ℤ}
    (hdet : det u u' ≠ 0) (hK : IsRegion K u u') (hKne : K.Nonempty)
    (hKcone : K ⊆ {z : ℤ × ℤ | ∃ i j : ℕ, z = g₀ + (i : ℤ) • w' + (j : ℤ) • w}) :
    det w w' = 1 ∨ det w w' = -1 := by
  obtain ⟨z₀, hz₀⟩ := hKne
  -- every lattice vector is an integer combination of `w'` and `w`
  have hgen : ∀ e : ℤ × ℤ, ∃ a b : ℤ, e = a • w' + b • w := by
    intro e
    obtain ⟨m, hm⟩ := exists_nsmul_add_mem hdet hK hz₀ e
    have hm0 : z₀ + (m : ℤ) • (u + u') ∈ K := by
      refine mem_of_nonneg_real_comb hK hz₀ (a := (m : ℝ)) (b := (m : ℝ))
        (Nat.cast_nonneg m) (Nat.cast_nonneg m) ?_
      rw [toReal_zsmul, toReal_add, smul_add]
      simp
    obtain ⟨i₁, j₁, h₁⟩ := hKcone hm0
    obtain ⟨i₂, j₂, h₂⟩ := hKcone hm
    refine ⟨(i₂ : ℤ) - i₁, (j₂ : ℤ) - j₁, ?_⟩
    have he : e = (z₀ + ((m : ℤ) • (u + u') + e)) - (z₀ + (m : ℤ) • (u + u')) := by abel
    rw [he, h₂, h₁]
    module
  obtain ⟨a, b, hab⟩ := hgen (1, 0)
  obtain ⟨c, d, hcd⟩ := hgen (0, 1)
  have h1 : det ((1, 0) : ℤ × ℤ) (0, 1) = 1 := by simp [det]
  rw [hab, hcd, det_comb] at h1
  have hsw : det w' w = -det w w' := by simp only [det]; ring
  rw [hsw] at h1
  have h2 : det w w' * (-(a * d - b * c)) = 1 := by linear_combination h1
  exact Int.eq_one_or_neg_one_of_mul_eq_one h2

/-! ## §21  Hence at `|B| = 1` the route needs `n = 1` **and** `|det u u'| = 1` -/

/-- **`w, w' ∈ ℕ-cone(u', n • u)` plus §20 give `n = 1` and `det u u' = ±1`.**  The shape of
`hw`/`hw'` is that of `no_box_band_cone_region` (§9), i.e. the seed's own recession cone with
`-h = n • u`. -/
theorem n_eq_one_and_unimodular_of_cone {K : Set (ℤ × ℤ)} {u u' w w' g₀ : ℤ × ℤ} {n : ℕ}
    {α β α' β' : ℕ}
    (hdet : det u u' ≠ 0) (hK : IsRegion K u u') (hKne : K.Nonempty)
    (hw : w = (α : ℤ) • u' + (β : ℤ) • ((n : ℤ) • u))
    (hw' : w' = (α' : ℤ) • u' + (β' : ℤ) • ((n : ℤ) • u))
    (hKcone : K ⊆ {z : ℤ × ℤ | ∃ i j : ℕ, z = g₀ + (i : ℤ) • w' + (j : ℤ) • w}) :
    n = 1 ∧ (det u u' = 1 ∨ det u u' = -1) := by
  have h := det_eq_pm_one_of_region_subset_cone hdet hK hKne hKcone
  have e : det w w' = (n : ℤ) * (((β : ℤ) * α' - (α : ℤ) * β') * det u u') := by
    rw [hw, hw']
    simp only [det, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  have habs : (det w w').natAbs = 1 := by
    rcases h with h | h <;> simp [h]
  rw [e, Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_natCast] at habs
  have hn : n = 1 := Nat.eq_one_of_mul_eq_one_right habs
  have hXY := Nat.eq_one_of_mul_eq_one_left habs
  have hD : (det u u').natAbs = 1 := Nat.eq_one_of_mul_eq_one_left hXY
  refine ⟨hn, ?_⟩
  rcases Int.natAbs_eq_iff.mp hD with h | h
  · exact Or.inl (by simpa using h)
  · exact Or.inr (by simpa using h)

/-- **At L1's `B = {g}`, the box/cone route's geometric block is satisfiable only if `n = 1`
and `(u, u')` is a lattice basis.**

Same `hband`/`hKcone` as `box_of_cone_route_dead_singleton` (§12), plus the two conjuncts of
that block §12 did not touch, `hKregion` and `hKne`.  §7 turns the two arms of `hband` into
`w, w' ∈ ℕ-cone(u', n • u)` and §21 finishes.  Read against §12: the `2 ≤ n` obstruction there
is the first conjunct here; the second — `|det u u'| = 1` — is new and does **not** go away at
`n = 1`.  `case1_sweep` supplies only `det u u' ≠ 0`. -/
theorem box_of_cone_route_singleton_needs_unimodular
    {g u u' : ℤ × ℤ} {t₁ : ℤ} {n : ℕ} {w w' g₀ : ℤ × ℤ} {N M : ℕ} {K : Set (ℤ × ℤ)}
    (hdet : det u u' ≠ 0) (hn : 0 < n) (hN : 1 ≤ N) (hM : 1 ≤ M)
    (hband : ∀ p q : ℤ, -(M : ℤ) ≤ p → -(N : ℤ) ≤ q → (p < 0 ∨ q < 0) →
      g₀ + p • w' + q • w ∈ sweptSeed {g} u' t₁ (-((n : ℤ) • u)))
    (hKregion : IsRegion K u u') (hKne : K.Nonempty)
    (hKcone : K ⊆ {z : ℤ × ℤ | ∃ i j : ℕ, z = g₀ + (i : ℤ) • w' + (j : ℤ) • w}) :
    n = 1 ∧ (det u u' = 1 ∨ det u u' = -1) := by
  have hdet' : det u' (-((n : ℤ) • u)) ≠ 0 := by
    have e : det u' (-((n : ℤ) • u)) = (n : ℤ) * det u u' := by
      simp only [det, Prod.fst_neg, Prod.snd_neg, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      ring
    rw [e]
    exact mul_ne_zero (by exact_mod_cast (by omega : (n : ℕ) ≠ 0)) hdet
  have hMz : -(M : ℤ) ≤ (-1 : ℤ) := by
    have : (1 : ℤ) ≤ (M : ℤ) := by exact_mod_cast hM
    omega
  have hNz : -(N : ℤ) ≤ (-1 : ℤ) := by
    have : (1 : ℤ) ≤ (N : ℤ) := by exact_mod_cast hN
    omega
  have hrayw : ∀ q : ℕ, (g₀ + (-1 : ℤ) • w') + (q : ℤ) • w ∈ sweptSeed {g} u' t₁ (-((n : ℤ) • u)) :=
    fun q => hband (-1) (q : ℤ) hMz (by omega) (Or.inl (by norm_num))
  have hrayw' : ∀ p : ℕ, (g₀ + (-1 : ℤ) • w) + (p : ℤ) • w' ∈ sweptSeed {g} u' t₁ (-((n : ℤ) • u)) := by
    intro p
    have hb := hband (p : ℤ) (-1) (by omega) hNz (Or.inr (by norm_num))
    have e : (g₀ + (-1 : ℤ) • w) + (p : ℤ) • w' = g₀ + (p : ℤ) • w' + (-1 : ℤ) • w := by module
    rw [e]; exact hb
  obtain ⟨α, β, hw⟩ := natComb_of_ray_in_singleton_seed hdet' hrayw
  obtain ⟨α', β', hw'⟩ := natComb_of_ray_in_singleton_seed hdet' hrayw'
  rw [neg_neg] at hw hw'
  exact n_eq_one_and_unimodular_of_cone hdet hKregion hKne hw hw' hKcone

/-! ## §22  Item 1 re-measured: the `B ⊆ Q` form of the call-site residual

`case1_sweep_of_box_of_cone_callsite` (§19) carries `hpw : 0 < pw`, which `LEAF-L3.md` and
`L1Fields.lean:217-246` have since shown is spent at a single instance, `hline g hg 0 hpw : g ∈ Q`.
This variant takes `hBQ : ∀ g ∈ B, g ∈ Q` instead and drops `hline` altogether; it is strictly
weaker in its hypotheses (`subset_Q_of_hline` recovers `hBQ` from `hpw` + `hline`) and has the
same conclusion.  With `hQR` now a parameter of `case1_sweep` (`RegionSteps.lean:1127`), the
binder list below is: **inherited verbatim** — `hξ'`, `hSgen`, `hc`, `hRper`, `hR_region`,
`hQR`; **free at the call site** — `haS`, `hconv` (`RegionSteps.lean:1040`); **L1 debt** — `hBQ`
(equivalently `hpw`, `pw_pos_iff_subset_Q`); **geometry** — the seven of §19, of which §20–§21
now price `hKregion ∧ hKne ∧ hKcone` at `det w w' = ±1`. -/
theorem case1_sweep_of_box_of_cone_callsite_BQ
    {ξ ξ' : Config ℤ} (hξ' : ξ' ∈ orbitClosure ξ)
    {u u' : ℤ × ℤ} {Q : Finset (ℤ × ℤ)} {τ : ℤ} {pw : ℕ} {B : Finset (ℤ × ℤ)}
    {R : Set (ℤ × ℤ)} {c : ℤ}
    {S : Finset (ℤ × ℤ)} (hSgen : Nivat.Colle.IsGeneratingSet ξ S)
    {a : ℤ × ℤ} (haS : a ∈ S) (hconv : LatticeConvex (S.erase a))
    (hc : c ≠ 0)
    (hRper : Colle41.PeriodOn ξ' R (c • u))
    (hR_region : Colle41.IsRegion R u u')
    (hQR : ∀ t : ℤ, τ ≤ t → ∀ z ∈ Q, t • u' + z ∈ R ∧ t • u' + z + c • u ∈ R)
    (hBQ : ∀ g ∈ B, g ∈ Q)
    {w w' g₀ : ℤ × ℤ} {N M : ℕ}
    (hSbox : ∀ b ∈ S.erase a, ∃ k m : ℕ, k ≤ N ∧ m ≤ M ∧ 1 ≤ k + m ∧
      b = a - (k : ℤ) • w - (m : ℤ) • w')
    (hband : ∀ n : ℕ, 0 < n → Colle41.PeriodOn ξ' R (-((n : ℤ) • u)) →
      ∀ p q : ℤ, -(M : ℤ) ≤ p → -(N : ℤ) ≤ q → (p < 0 ∨ q < 0) →
        g₀ + p • w' + q • w ∈ sweptSeed B u' (τ + (pw : ℤ)) (-((n : ℤ) • u)))
    {K : Set (ℤ × ℤ)} (hKR : K ⊆ R) (hKregion : Colle41.IsRegion K u u') (hKne : K.Nonempty)
    (hKcone : K ⊆ {z : ℤ × ℤ | ∃ i j : ℕ, z = g₀ + (i : ℤ) • w' + (j : ℤ) • w})
    {t₀ : ℕ} (ht₀ : 0 < t₀) :
    ∀ q : ℕ, 0 < q →
      (∀ g ∈ B, ∀ t : ℤ, τ + (pw : ℤ) ≤ t → ξ' (g + (t + (q : ℤ)) • u') = ξ' (g + t • u')) →
      ∃ K : Set (ℤ × ℤ), K ⊆ R ∧ Colle41.IsRegion K u u' ∧ K.Nonempty ∧
        ∃ t₀ : ℕ, 0 < t₀ ∧ Colle41.PeriodOn ξ' K (((t₀ * q : ℕ) : ℤ) • u') := by
  intro q hq hqper
  obtain ⟨n, hn, hnper⟩ := exists_neg_nsmul_period hc hRper
  have hseedR : sweptSeed B u' (τ + (pw : ℤ)) (-((n : ℤ) • u)) ⊆ R :=
    sweptSeed_subset_R hR_region n
      (halfStripFrom_subset_R (c := c) (u := u) hBQ
        (fun t ht z hz => hQR t (by omega) z hz))
  exact Nivat.L3Cover.hsweep_of_box_of_cone hξ' (hgen_of_hSgen hSgen haS hconv) hSbox
    hseedR hnper (hband n hn hnper) hKR hKregion hKne hKcone ht₀ hqper

/-! ## §23  Collé's route, item (a): the `𝒯`-band (`b3_colle2.txt:700`)

Collé: *"there exist `0 < t'₀ ≤ P_η(𝒯) + 1` and infinitely many integers `r > 0` so that (4.3)
holds for `r` and `s = r + t'₀`"*, where (4.3) says agreement of `x` on `𝒯 + r h'` and
`𝒯 + s h'` propagates to the half-strip `H_𝒯 + r h'` (`:672`).  Read as the sweep engine
needs it: for every `N` there is an `r ≥ N` such that `ξ'` agrees with its `t₀ q u'`-translate
on the whole slab `{g + r q u' + k u : g ∈ F₀, k : ℕ}`.

Two steps, both kernel-checked here:

* `band_pigeonhole` — the pigeonhole itself.  `r ↦ (ξ'(g + r v + j u))_{g ∈ F₀, j < n}` takes
  values in a finite type (`↥F₀ × Fin n → ↥(range ξ')`), so `exists_bounded_repeat`
  (`Claim43.lean:711`, previously with **no consumer**) gives a gap `t₀` realised arbitrarily
  late.  This is where `(Set.range ξ').Finite` is spent; it is the *only* place.
* `exists_band_repeat` — ray closure.  On `R`, `ξ'` is `n u`-periodic (`hRper` via
  `exists_neg_nsmul_period`), so is its `u'`-translate (`T_periodOn_of_periodOn_of_ray`, which
  needs the `u'`-ray of `IsRegion R u u'`), and the `n` consecutive agreements of the
  pigeonhole seed extend along the whole `u`-ray by `ray_closure_of_period`
  (`Claim43.lean:466`).

**Quantifier shape, stated explicitly (lead's caution).**  The conclusion is
`∀ N, ∃ r ≥ N, …` — *infinitely many* `r`, **not** all `r`.  Collé's ladder (item (b),
**not built here**) chooses one such `r` per `N`; nothing below asserts agreement at every `r`.

**What is consumed and where it comes from at the call site** (`RegionSteps.lean:1097-1134`):
`hc`, `hRper`, `hR_region` are binders; `hfin : (Set.range ξ').Finite` is **not** a binder but
is derivable — `Nivat.BL.finite_range_of_mem_orbitClosure hξ.1.1 hξ'` type-checks against the
call site's `hξ : IsMinimalCounterexample ξ` and `hξ'` (`tmp/l3band_deriv_probe.lean`, receipt
in `tmp/`, **not landed**).  `BoyleLind` is upstream of `RegionSteps` (its 35-module import
closure does not contain it), so importing it here is safe.  `F₀ ⊆ R` is the caller's choice
of the finite box `𝒯 ⊂ ℛ`; `q` is the step of `case1_sweep`'s conclusion.

**No finiteness lemma of the `finite_of_dot_bounded` kind was needed**: the band is indexed by
a `Finset` `F₀` from the outset, so the "bounded `{dot n₁, dot n₂}` is finite" step I had
priced in the report is not consumed.  (`Step_ChainData.finite_of_dot_bounded`, `:38`, does
have that shape — checked by reading, not imported.) -/

/-- **The pigeonhole (`b3_colle2.txt:700`).**  Agreement on the finite window
`F₀ + r v + {0, …, n-1} u` recurs with a fixed positive gap `t₀`, arbitrarily late in `r`.
The bound `t₀ ≤ P_η(𝒯) + 1` is dropped: nothing downstream consumes it. -/
theorem band_pigeonhole {ξ' : Config ℤ} (hfin : (Set.range ξ').Finite)
    (F₀ : Finset (ℤ × ℤ)) (n : ℕ) (u v : ℤ × ℤ) :
    ∃ t₀ : ℕ, 0 < t₀ ∧ ∀ N : ℕ, ∃ r : ℕ, N ≤ r ∧
      ∀ g ∈ F₀, ∀ j : ℕ, j < n →
        ξ' (g + (r : ℤ) • v + (j : ℤ) • u) = ξ' (g + ((r + t₀ : ℕ) : ℤ) • v + (j : ℤ) • u) := by
  have : Finite ↥(Set.range ξ') := hfin.to_subtype
  let f : ℕ → (↥F₀ × Fin n → ↥(Set.range ξ')) := fun r p =>
    ⟨ξ' (p.1.1 + (r : ℤ) • v + ((p.2 : ℕ) : ℤ) • u), ⟨_, rfl⟩⟩
  obtain ⟨t₀, ht₀, -, hrep⟩ := exists_bounded_repeat f
  refine ⟨t₀, ht₀, fun N => ?_⟩
  obtain ⟨r, hr, s, -, rfl, hfs⟩ := hrep N
  refine ⟨r, hr, fun g hg j hj => ?_⟩
  have := congrFun hfs (⟨g, hg⟩, ⟨j, hj⟩)
  exact congrArg Subtype.val this

/-- A `u`-period of `ξ'` on `R` is a `u`-period of every forward `u'`-translate of `ξ'` on `R`,
because `R` is closed under `+ u'` (`IsRegion`'s `u'`-ray plus `ray_all_of_rayIn`). -/
theorem T_periodOn_of_periodOn_of_ray {ξ' : Config ℤ} {R : Set (ℤ × ℤ)} {u u' : ℤ × ℤ}
    (hR : IsRegion R u u') {n : ℕ} (hper : PeriodOn ξ' R ((n : ℤ) • u)) (m : ℕ) :
    PeriodOn (T ((m : ℤ) • u') ξ') R ((n : ℤ) • u) := by
  obtain ⟨hconv, -, ⟨z₁', hray'⟩⟩ := hR
  intro z hz hz'
  have h1 : z + (m : ℤ) • u' ∈ R := by
    have := ray_all_of_rayIn hconv hray' m z hz 1
    simpa using this
  have h2 : z + (n : ℤ) • u + (m : ℤ) • u' ∈ R := by
    have := ray_all_of_rayIn hconv hray' m _ hz' 1
    simpa using this
  have := hper (z + (m : ℤ) • u') h1 (by rw [add_right_comm]; exact h2)
  simp only [T_apply]
  rw [add_right_comm] at this
  exact this

/-- **The band, i.e. Collé's `:700` in sweep-engine shape.**  For every `N` there is `r ≥ N`
such that `ξ'` agrees with `T^{t₀ q u'} ξ'` on the whole slab `F₀ + r q u' + ℕ u`.

`∀ N, ∃ r ≥ N` — infinitely many `r`, not all `r`.  The gap `t₀` does not depend on `N`. -/
theorem exists_band_repeat {ξ' : Config ℤ} (hfin : (Set.range ξ').Finite)
    {R : Set (ℤ × ℤ)} {u u' : ℤ × ℤ} {c : ℤ} (hc : c ≠ 0)
    (hRper : PeriodOn ξ' R (c • u)) (hR : IsRegion R u u')
    {F₀ : Finset (ℤ × ℤ)} (hF₀ : ∀ g ∈ F₀, g ∈ R) (q : ℕ) :
    ∃ t₀ : ℕ, 0 < t₀ ∧ ∀ N : ℕ, ∃ r : ℕ, N ≤ r ∧
      ∀ g ∈ F₀, ∀ k : ℕ,
        ξ' (g + (r : ℤ) • ((q : ℤ) • u') + (k : ℤ) • u)
          = T (((t₀ * q : ℕ) : ℤ) • u') ξ' (g + (r : ℤ) • ((q : ℤ) • u') + (k : ℤ) • u) := by
  obtain ⟨n, hn, hnper⟩ := exists_neg_nsmul_period hc hRper
  have hper : PeriodOn ξ' R ((n : ℤ) • u) := by simpa using hnper.neg
  obtain ⟨t₀, ht₀, hrep⟩ := band_pigeonhole hfin F₀ n u ((q : ℤ) • u')
  refine ⟨t₀, ht₀, fun N => ?_⟩
  obtain ⟨r, hr, hagree⟩ := hrep N
  refine ⟨r, hr, fun g hg k => ?_⟩
  have hconv := hR.1
  obtain ⟨-, ⟨z₁, hray⟩, ⟨z₁', hray'⟩⟩ := hR
  -- the base point `g + r q u'` is in `R`, and so is its whole `u`-ray
  have hz₀ : g + (r : ℤ) • ((q : ℤ) • u') ∈ R := by
    have := ray_all_of_rayIn hconv hray' q g (hF₀ g hg) r
    simpa [smul_smul, mul_comm] using this
  have hrayR : ∀ k : ℕ, g + (r : ℤ) • ((q : ℤ) • u') + (k : ℤ) • u ∈ R := by
    intro k
    have := ray_all_of_rayIn hconv hray 1 _ hz₀ k
    simpa using this
  refine ray_closure_of_period hn hper
    (T_periodOn_of_periodOn_of_ray ⟨hconv, ⟨z₁, hray⟩, ⟨z₁', hray'⟩⟩ hper (t₀ * q)) hrayR ?_ k
  intro j hj
  rw [T_apply, hagree g hg j hj]
  congr 1
  push_cast
  module

/-! ## §24  The band at `case1_sweep`'s call site: `F₀` nonempty, `hfin` derived

`exists_band_repeat` admits `F₀ = ∅` vacuously.  This section instantiates it against the
binders `case1_sweep` (`RegionSteps.lean:1097-1134`) actually carries, with a **nonempty**
`F₀ ⊆ R`: the translated window `b + S` that `hB_covers_window` (`:1127`) places inside `R`,
nonempty because `IsGeneratingSet` (`Generating.lean:58`) carries `S.Nonempty`.

`hfin : (Set.range ξ').Finite` is not a binder there.  It is derived from
`(Set.range ξ).Finite` — the first conjunct of `IsCounterexample` (`ExternalDefs.lean:48`),
hence of `hξ : IsMinimalCounterexample ξ` — via `Nivat.BL.finite_range_of_mem_orbitClosure`
(`BoyleLind.lean:94`).  **This is the one place in the L3 lane where `hξ` is consumed for real
content** (a finite alphabet), not for the vacuous strength `PROTOCOL.md` warns about; the
main theorem below therefore takes only `hA : (Set.range ξ).Finite`, and `hfin_of_counterexample`
is the one-line bridge from `hξ.1`.  Landing this retires `tmp/l3band_deriv_probe.lean`. -/

/-- The only content of `hξ` the band consumes: the alphabet is finite, and finiteness passes
to the orbit closure. -/
theorem hfin_of_counterexample {ξ ξ' : Config ℤ} (hξ : IsCounterexample ξ)
    (hξ' : ξ' ∈ orbitClosure ξ) : (Set.range ξ').Finite :=
  Nivat.BL.finite_range_of_mem_orbitClosure hξ.1 hξ'

/-- **The band at the call site, non-vacuously.**  Every binder here is either one of
`case1_sweep`'s (`hξ'`, `hSgen`, `hc`, `hRper`, `hR_region`, `hB_covers_window`) or is `hA`,
which is `hξ.1.1`.  The delivered `F₀` is `b + S`, nonempty, inside `R`.

Quantifier shape unchanged from `exists_band_repeat`: `∀ N, ∃ r ≥ N` — infinitely many `r`. -/
theorem exists_band_repeat_callsite {ξ ξ' : Config ℤ}
    (hA : (Set.range ξ).Finite) (hξ' : ξ' ∈ orbitClosure ξ)
    {S : Finset (ℤ × ℤ)} (hSgen : IsGeneratingSet ξ S)
    {u u' : ℤ × ℤ} {B : Finset (ℤ × ℤ)} {R : Set (ℤ × ℤ)} {c : ℤ} (hc : c ≠ 0)
    (hRper : PeriodOn ξ' R (c • u)) (hR_region : IsRegion R u u')
    (hB_covers_window : ∃ b ∈ B, ∀ z ∈ S, b + z ∈ R) (q : ℕ) :
    ∃ F₀ : Finset (ℤ × ℤ), F₀.Nonempty ∧ (∀ g ∈ F₀, g ∈ R) ∧
      ∃ t₀ : ℕ, 0 < t₀ ∧ ∀ N : ℕ, ∃ r : ℕ, N ≤ r ∧
        ∀ g ∈ F₀, ∀ k : ℕ,
          ξ' (g + (r : ℤ) • ((q : ℤ) • u') + (k : ℤ) • u)
            = T (((t₀ * q : ℕ) : ℤ) • u') ξ' (g + (r : ℤ) • ((q : ℤ) • u') + (k : ℤ) • u) := by
  obtain ⟨b, -, hbR⟩ := hB_covers_window
  have hF₀R : ∀ g ∈ S.image (fun z => b + z), g ∈ R := by
    intro g hg
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hg
    exact hbR z hz
  exact ⟨_, (hSgen.1).image _, hF₀R,
    exists_band_repeat (Nivat.BL.finite_range_of_mem_orbitClosure hA hξ') hc hRper
      hR_region hF₀R q⟩

/-! ## §25  Collé's route, item (b): the ladder **step**, seed taken as an assumption

Collé (`b3_colle2.txt:694-698`): each successive line `ℓ_{i+1} := ℓ_i^{(−)}` is conquered by
the generating window, *starting from* the `|𝒮 ∩ ℓ_𝒮| − 1` consecutive points of
`ℓ_{i+1} ∩ (H_Q − ιh)` on which (4.4) already gives agreement.  In the paper that seed comes
from the band's width; in Lean that width is the open `B`-extent question (`LEAF-L3.md`,
with L1asm).  **This section does not build the seed.**  It builds the step with the seed as
a named hypothesis, `hseed_assumed`, so that when the width question is answered the ladder
either closes by discharging that one binder or dies visibly at it.

🔴 **Status: `hseed_assumed` is an assumption, not a theorem.**  Nothing in this file or in the
tree produces it.  `ladder_line_step` and `ladder_of_seeds` are conditional on it and must not
be reported as closing the ladder.

Shape.  `sweep_induction` (`Claim43.lean:316`) needs the window to land in the conquered set at
*every* stage, which fails for the first `s` points of a line (their windows reach past the
line's start).  `ladder_line_step` is `sweep_induction` with those `s` stages supplied by the
seed instead: the window condition `hwin` is only demanded for `j ≥ s`.  `ladder_of_seeds` is
the outer induction over lines, `multi_line_sweep` (`:362`) with a seed on every line.

**Quantifier shape (lead's caution).**  Both theorems run at *one fixed* band — `D` is the
agreement set of a single `r` from `exists_band_repeat`'s `∀ N, ∃ r ≥ N`; the ladder is
`∀ i j` along and across the lines **for that `r`**.  Nothing here quantifies over `r`, so the
band's "infinitely many `r`" is not silently promoted to "all `r`".  Passing from "for
infinitely many `r`, `ξ'|K_r` is `t₀ q u'`-periodic" to `case1_sweep`'s single `K` is a
separate step (Collé's last sentence at `:700`), **not built here**. -/

/-- **One line of the ladder.**  Agreement on the first `s` points is *assumed*
(`hseed_assumed`); from the `s`-th point on, the window lands in `D` or in earlier points of the
line, and `agree_at_of_generatesAt` conquers the rest.  Compare `line_sweep_along`
(`Claim43.lean:337`), which is the case `s = 0`. -/
theorem ladder_line_step {A : Type*} {η x y : Config A}
    (hx : x ∈ orbitClosure η) (hy : y ∈ orbitClosure η)
    {S : Finset (ℤ × ℤ)} {a : ℤ × ℤ} (hgen : GeneratesAt η S a)
    {D : Set (ℤ × ℤ)} (hD : ∀ z ∈ D, x z = y z)
    (g₁ w : ℤ × ℤ) (s : ℕ)
    (hseed_assumed : ∀ j : ℕ, j < s → x (g₁ + (j : ℤ) • w) = y (g₁ + (j : ℤ) • w))
    (hwin : ∀ j : ℕ, s ≤ j → ∀ z ∈ S.erase a,
      z + (g₁ + (j : ℤ) • w - a) ∈ D ∨
        ∃ i : ℕ, i < j ∧ z + (g₁ + (j : ℤ) • w - a) = g₁ + (i : ℤ) • w) :
    ∀ j : ℕ, x (g₁ + (j : ℤ) • w) = y (g₁ + (j : ℤ) • w) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    by_cases hj : j < s
    · exact hseed_assumed j hj
    · have key : x (a + (g₁ + (j : ℤ) • w - a)) = y (a + (g₁ + (j : ℤ) • w - a)) := by
        refine agree_at_of_generatesAt hx hy hgen
          (D := D ∪ {p | ∃ i : ℕ, i < j ∧ p = g₁ + (i : ℤ) • w}) ?_ _ ?_
        · rintro z (hzD | ⟨i, hi, rfl⟩)
          · exact hD z hzD
          · exact ih i hi
        · intro z hz
          rcases hwin j (Nat.le_of_not_lt hj) z hz with h | ⟨i, hi, he⟩
          · exact Or.inl h
          · exact Or.inr ⟨i, hi, he⟩
      have e : a + (g₁ + (j : ℤ) • w - a) = g₁ + (j : ℤ) • w := by abel
      rwa [e] at key

/-- **The ladder, conditional on a seed per line.**  Line `i` is `g i + ℕ • w`; its first `s`
points are *assumed* to agree (`hseed_assumed`); from there the window may reach into `D`, into
any earlier line, or into earlier points of the same line.

`∀ i j` — every point of every line, **at the one fixed band `D`**.  See the section header for
what this does and does not say about `r`. -/
theorem ladder_of_seeds {A : Type*} {η x y : Config A}
    (hx : x ∈ orbitClosure η) (hy : y ∈ orbitClosure η)
    {S : Finset (ℤ × ℤ)} {a : ℤ × ℤ} (hgen : GeneratesAt η S a)
    {D : Set (ℤ × ℤ)} (hD : ∀ z ∈ D, x z = y z)
    (g : ℕ → ℤ × ℤ) (w : ℤ × ℤ) (s : ℕ)
    (hseed_assumed : ∀ i j : ℕ, j < s → x (g i + (j : ℤ) • w) = y (g i + (j : ℤ) • w))
    (hwin : ∀ i j : ℕ, s ≤ j → ∀ z ∈ S.erase a,
      z + (g i + (j : ℤ) • w - a) ∈
        D ∪ {p | ∃ i' : ℕ, i' < i ∧ ∃ j' : ℕ, p = g i' + (j' : ℤ) • w} ∨
        ∃ j' : ℕ, j' < j ∧ z + (g i + (j : ℤ) • w - a) = g i + (j' : ℤ) • w) :
    ∀ i j : ℕ, x (g i + (j : ℤ) • w) = y (g i + (j : ℤ) • w) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ihI =>
    refine ladder_line_step hx hy hgen
      (D := D ∪ {p | ∃ i' : ℕ, i' < i ∧ ∃ j' : ℕ, p = g i' + (j' : ℤ) • w}) ?_
      (g i) w s (hseed_assumed i) (hwin i)
    rintro z (hzD | ⟨i', hi', j', rfl⟩)
    · exact hD z hzD
    · exact ihI i' hi' j'

/-! ## §26  Collé's route, the closing step: infinitely many `r` → one `K`

Collé's last sentence (`b3_colle2.txt:700`): *"as there exist `0 < t'₀ ≤ P_η(𝒯)+1` and
infinitely many integers `r > 0` so that (4.3) holds for `r` and `s = r + t'₀`, Claim 4.3
implies that `x|ℋ(ℓ_{Q'}) ∩ ℛ` is periodic of period `t'₀ h'`."*

**Verifying the lead's hand-read of `IsRegion`** (off the definition, `Lemma41.lean:688-689`):
`IsRegion K u u' = IsLatticeConvexRegion K ∧ (∃ z₀, RayIn K z₀ u) ∧ (∃ z₀', RayIn K z₀' u')` —
yes, rays in **both** directions, plus lattice convexity.  A single slab
`F₀ + r q u' + ℕ u` has only the `u`-ray and is not lattice-convex for a general `F₀`, so it
cannot be `case1_sweep`'s `K`.  But the fix is **not** "union the slabs": a union of slabs is
not convex either.  Collé's `K` is the *fixed* region `ℋ(ℓ_{Q'}) ∩ ℛ` (`R ∩ halfPlaneGE n c`,
a region by `Nivat.LE2.isRegion_inter_halfPlaneGE`, `RegionCutGE.lean:58`, which produces both
rays itself); the `r`-indexed objects are Claim 4.3's *nested cuts*
`K ∩ ℋ(−ℓ_{𝒯 + r h'}) = K ∩ {z | dot ν z ≤ c₀ + r d}` (`:680`), each of which is
`t₀ q u'`-periodic **for the infinitely many good `r`**.  So the `∀ N, ∃ r ≥ N` is doing real
work: it is what lets any two points of `K` be caught by one periodic cut.

**Where "infinitely many" is *not* silently promoted to "all".**  `periodOn_iUnion_of_cofinal`
needs two things: the cuts are **monotone** in `r` (`levels_mono`, from `0 < d`), and
periodicity holds on a **cofinal** set of `r`.  It never asks for `r + t₀` to be a good index —
`PeriodOn` on the level `r` cut already contains the `+ t₀ q u'` step because both endpoints of
a period pair land in a common level, by monotonicity.  That is the whole trick, and it is why
the index set does not need to be closed under `+ t₀`.

🔴 **Status: `hlevels_assumed` is an assumption, not a theorem.**  It is what the ladder (§25,
itself standing on `hseed_assumed`) is supposed to deliver at each good `r`: periodicity on the
cut below the `r`-th line.  Nothing in the tree produces it.  `sweep_conclusion_of_cofinal_levels`
is conditional on it and does **not** close `case1_sweep`.  The chain now reads
`band (§23, proved) → ladder (§25, on hseed_assumed) → levels (hlevels_assumed) → this`. -/

/-- Periodicity on a monotone family of sets, holding at a cofinal set of indices, is
periodicity on the union.  No index needs to be closed under `+ t₀`: both endpoints of a period
pair sit in some common member of the family. -/
theorem periodOn_iUnion_of_cofinal {A : Type*} {x : Config A} {K : ℕ → Set (ℤ × ℤ)}
    (hmono : Monotone K) {h : ℤ × ℤ}
    (hcof : ∀ N : ℕ, ∃ r : ℕ, N ≤ r ∧ PeriodOn x (K r) h) :
    PeriodOn x (⋃ r, K r) h := by
  intro z hz hz'
  obtain ⟨r₁, hr₁⟩ := Set.mem_iUnion.mp hz
  obtain ⟨r₂, hr₂⟩ := Set.mem_iUnion.mp hz'
  obtain ⟨r, hr, hper⟩ := hcof (max r₁ r₂)
  exact hper z (hmono (le_trans (le_max_left _ _) hr) hr₁)
    (hmono (le_trans (le_max_right _ _) hr) hr₂)

/-- The nested cuts `K₀ ∩ {dot ν z ≤ c₀ + r d}` exhaust `K₀` when `0 < d`. -/
theorem iUnion_levels_eq {K₀ : Set (ℤ × ℤ)} {ν : ℤ × ℤ} {c₀ d : ℤ} (hd : 0 < d) :
    (⋃ r : ℕ, K₀ ∩ {z | dot ν z ≤ c₀ + (r : ℤ) * d}) = K₀ := by
  ext z
  simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq, exists_and_left]
  refine ⟨fun ⟨h, _⟩ => h, fun hz => ⟨hz, (dot ν z - c₀).toNat, ?_⟩⟩
  have h1 : dot ν z - c₀ ≤ ((dot ν z - c₀).toNat : ℤ) := Int.self_le_toNat _
  have h2 : ((dot ν z - c₀).toNat : ℤ) * 1 ≤ ((dot ν z - c₀).toNat : ℤ) * d :=
    mul_le_mul_of_nonneg_left hd (Int.natCast_nonneg _)
  omega

/-- The cuts are monotone in `r`. -/
theorem levels_mono {K₀ : Set (ℤ × ℤ)} {ν : ℤ × ℤ} {c₀ d : ℤ} (hd : 0 < d) :
    Monotone (fun r : ℕ => K₀ ∩ {z | dot ν z ≤ c₀ + (r : ℤ) * d}) := by
  intro r₁ r₂ hr z ⟨hz, hle⟩
  refine ⟨hz, ?_⟩
  simp only [Set.mem_ofPred_eq] at hle ⊢
  have : (r₁ : ℤ) * d ≤ (r₂ : ℤ) * d :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hr) hd.le
  omega

/-- **`case1_sweep`'s conclusion block, from cofinal periodicity on the cuts.**  The conclusion
is byte-identical to `case1_sweep`'s (`RegionSteps.lean:1130-1133`).  `K := R ∩ halfPlaneGE n c`
is Collé's `ℋ(ℓ_{Q'}) ∩ ℛ`; `n` is the inward normal of `ℓ_{Q'}` (`dot n u = 0`,
`0 < dot n u'`), `ν` the normal of the `𝒯`-lines with `d = dot ν (q u')`-type step `0 < d`.

`hlevels_assumed` is the assumption (see the section header).  Everything else is
`hR_region` plus data. -/
theorem sweep_conclusion_of_cofinal_levels {ξ' : Config ℤ}
    {R : Set (ℤ × ℤ)} {u u' : ℤ × ℤ} (hR_region : IsRegion R u u')
    (n : ℤ × ℤ) (c : ℤ) (hnu : dot n u = 0) (hnu' : 0 < dot n u')
    (ν : ℤ × ℤ) (c₀ d : ℤ) (hd : 0 < d)
    (q : ℕ) {t₀ : ℕ} (ht₀ : 0 < t₀)
    (hlevels_assumed : ∀ N : ℕ, ∃ r : ℕ, N ≤ r ∧
      PeriodOn ξ' ((R ∩ halfPlaneGE n c) ∩ {z | dot ν z ≤ c₀ + (r : ℤ) * d})
        (((t₀ * q : ℕ) : ℤ) • u')) :
    ∃ K : Set (ℤ × ℤ), K ⊆ R ∧ IsRegion K u u' ∧ K.Nonempty ∧
      ∃ t₀ : ℕ, 0 < t₀ ∧ PeriodOn ξ' K (((t₀ * q : ℕ) : ℤ) • u') := by
  have hK : IsRegion (R ∩ halfPlaneGE n c) u u' :=
    Nivat.LE2.isRegion_inter_halfPlaneGE hR_region n c hnu hnu'
  obtain ⟨z₀, hray⟩ := hK.2.1
  refine ⟨R ∩ halfPlaneGE n c, Set.inter_subset_left, hK, ⟨z₀, by simpa using hray 0⟩,
    t₀, ht₀, ?_⟩
  rw [← iUnion_levels_eq (K₀ := R ∩ halfPlaneGE n c) (ν := ν) (c₀ := c₀) hd]
  exact periodOn_iUnion_of_cofinal (levels_mono hd) hlevels_assumed

/-! ## §27  The ladder's window condition is satisfiable for a 2-D `S` (and the seed is needed)

Lead's secondary item: §25's `hwin` was "engine present, no geometric witness".  Here is the
witness, at the smallest genuinely two-dimensional window `S = {(0,0), (−1,0), (0,−1)}` with
`a = (0,0)` — the same non-collinear shape §2 uses — lines `g i = (0, i)`, direction
`w = (1, 0)`, seed `D = {p | p.2 < 0}` (the lower half-plane, playing the band), `s = 1`.

`ladder_hwin_witness`: for every line `i` and every `j ≥ 1`, the punctured window
`{(−1,0), (0,−1)} + (j, i)` lands in `D` ∪ (earlier lines) ∪ (earlier points of line `i`).
`ladder_hwin_witness_needs_seed`: at `j = 0` the point `(−1, i)` is in none of the three, so
`s = 0` (i.e. `line_sweep_along`, `Claim43.lean:337`) would **not** do — the seed hypothesis
of §25 is load-bearing, not decorative, even in this toy.

Scope: this shows `hwin` is *satisfiable*, at one shape.  It says nothing about whether L1's `S`
and Collé's `ℓ_i^{(−)}` ordering produce it — that is the same `B`-width question as
`hseed_assumed`. -/

/-- The three-point window `{(0,0), (−1,0), (0,−1)}`. -/
def ladS : Finset (ℤ × ℤ) := {(0, 0), (-1, 0), (0, -1)}

theorem ladS_erase : ladS.erase (0, 0) = {(-1, 0), (0, -1)} := by decide

/-- `hwin` of `ladder_of_seeds` holds at `ladS`, rows `(0, i)`, step `(1, 0)`, lower
half-plane seed, `s = 1`. -/
theorem ladder_hwin_witness :
    ∀ i j : ℕ, 1 ≤ j → ∀ z ∈ ladS.erase (0, 0),
      z + (((0 : ℤ), (i : ℤ)) + (j : ℤ) • ((1 : ℤ), (0 : ℤ)) - (0, 0)) ∈
        {p : ℤ × ℤ | p.2 < 0} ∪
          {p | ∃ i' : ℕ, i' < i ∧ ∃ j' : ℕ, p = ((0 : ℤ), (i' : ℤ)) + (j' : ℤ) • ((1 : ℤ), (0 : ℤ))} ∨
        ∃ j' : ℕ, j' < j ∧ z + (((0 : ℤ), (i : ℤ)) + (j : ℤ) • ((1 : ℤ), (0 : ℤ)) - (0, 0))
          = ((0 : ℤ), (i : ℤ)) + (j' : ℤ) • ((1 : ℤ), (0 : ℤ)) := by
  intro i j hj z hz
  rw [ladS_erase] at hz
  simp only [Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with rfl | rfl
  · right
    refine ⟨j - 1, by omega, ?_⟩
    ext <;> simp; omega
  · left
    cases i with
    | zero => left; simp
    | succ i =>
      right
      refine ⟨i, by omega, j, ?_⟩
      ext <;> simp

/-- The seed is genuinely needed: at `j = 0` the window point `(−1, i)` is in none of the three
places `hwin` allows, so `s = 0` would not do. -/
theorem ladder_hwin_witness_needs_seed (i : ℕ) :
    ¬ ((((-1 : ℤ), (0 : ℤ)) + (((0 : ℤ), (i : ℤ)) + ((0 : ℕ) : ℤ) • ((1 : ℤ), (0 : ℤ)) - (0, 0))) ∈
        {p : ℤ × ℤ | p.2 < 0} ∪
          {p | ∃ i' : ℕ, i' < i ∧ ∃ j' : ℕ, p = ((0 : ℤ), (i' : ℤ)) + (j' : ℤ) • ((1 : ℤ), (0 : ℤ))} ∨
        ∃ j' : ℕ, j' < 0 ∧ True) := by
  rintro ((h | ⟨i', _, j', h⟩) | ⟨j', hj', -⟩)
  · simp at h; omega
  · have := congrArg Prod.fst h; simp at this
  · omega

/-! ## §28  The gluing step: ladder output → `PeriodOn` on a cut

Lead's NOT-CHECKED (2).  §25 delivers `∀ i j, ξ' (g i + j u) = T h' ξ' (g i + j u)` — forward
rays only.  §26 consumes `PeriodOn ξ' Cut h'` on the whole cut.  Two things bridge them:

* **Per-line completion by periodicity** (Collé `:696`: *"the periodicity of `x|ℓ₁ ∩ ℛ` and
  `(T x)|ℓ₁ ∩ ℛ` implies `x|ℓ₁ ∩ ℛ = (T x)|ℓ₁ ∩ ℛ`"*).  `agree_on_line_of_ray_of_period`: on a
  `+u`-closed set where both configurations are `n u`-periodic, agreement on the forward ray
  `g + ℕ u` gives agreement at every `g + m u`, `m : ℤ`, of the set — push `z` forward by
  `|m| n` steps of `n u` onto the ray, then pull back by periodicity.
  ⚠ This forces the ladder's line direction to be `+u`: `R` is closed under `+u`
  (`ray_all_of_rayIn`) but not `−u`, and the push-forward has to stay inside the set.
* **Cover**: `hcover : ∀ z ∈ Cut, ∃ i m, z = g i + m u` — the enumeration exhausts the cut.
  This is *not* produced here; it is a property of the line enumeration `g` (which is the
  ladder's, i.e. `hseed_assumed`'s, and so the `B`-width question's).  `periodOn_of_ladder_cover`
  takes it as a binder.

**§20 check**: `L3Cover.lean` has no lemma of this shape — its `covers` (`:128`, `:198`,
`:300`) is `K ⊆ genClosure …`, the box/cone route's closure operator, not a line enumeration.
Nothing to pick up.

**Claim 4.3's cut sign, settled by reading `b3_colle2.txt:680` against the ℋ definition**
(`Lemma41.lean:22`, quoting the paper: `ℋ(ℓ) = {g : ⟨g, (−u₂, u₁)⟩ ≥ 0}`, so `ℋ(−ℓ)` is the
*opposite* closed half-plane of the same line).  The region at `:680` is
`ℋ(ℓ_{Q'}) ∩ ℛ ∩ ℋ(−ℓ_{𝒯 + r h'})`: the band between the fixed line `ℓ_{Q'}` and the moving
line `ℓ_{𝒯 + r h'}`, on the `ℓ_{Q'}` side of the latter.  With `n` the inward normal of
`ℋ(ℓ_{Q'})` (`dot n u = 0`, `0 < dot n u'`, exactly `isRegion_inter_halfPlaneGE`'s hypotheses),
`ℋ(−ℓ_{𝒯 + r h'}) = {z | dot n z ≤ dot n (𝒯-base) + r · dot n h'}`, and `dot n h' > 0`
because `h'` is the `u'`-period.  In Lean the band index is `r • (q • u')`
(`exists_band_repeat`), so `ν := n`, `d := q · dot n u' > 0`.  §26's `{dot ν z ≤ c₀ + r d}`
with `0 < d` is therefore the right form, and `levels_mono` is the right monotonicity.
**Label: hand-read against the definition; not a kernel fact** — no Lean object is Collé's
`ℋ(−ℓ)`.  The assembly theorem below sharpens §26 to `ν = n`.

🔴 **Status.**  `sweep_conclusion_of_cofinal_ladders` takes the *whole* per-`r` ladder
input — seed, window condition, cover — as one named assumption `hladder_assumed`.  It is the
same debt as `hseed_assumed` + `hlevels_assumed`, restated as exactly what a producer must
supply per good `r`.  Nothing in the tree produces it.  Chain now:
`band (§23, proved) → hladder_assumed (seed + hwin + cover, per cofinal r) → §28 → §26 → conclusion`,
i.e. **one named assumption** between the band and `case1_sweep`'s conclusion block. -/

theorem mem_add_nsmul_of_closed {U : Set (ℤ × ℤ)} {u : ℤ × ℤ}
    (hU : ∀ z ∈ U, z + u ∈ U) {z : ℤ × ℤ} (hz : z ∈ U) (k : ℕ) : z + (k : ℤ) • u ∈ U := by
  induction k with
  | zero => simpa using hz
  | succ k ih =>
    have e : z + ((k + 1 : ℕ) : ℤ) • u = (z + (k : ℤ) • u) + u := by push_cast; rw [add_smul]; abel
    rw [e]; exact hU _ ih

theorem eq_add_nsmul_period_of_closed {A : Type*} {x : Config A} {U : Set (ℤ × ℤ)} {u : ℤ × ℤ}
    (hU : ∀ z ∈ U, z + u ∈ U) {n : ℕ} (hper : PeriodOn x U ((n : ℤ) • u))
    {z : ℤ × ℤ} (hz : z ∈ U) (k : ℕ) : x (z + (k : ℤ) • ((n : ℤ) • u)) = x z := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : z + ((k + 1 : ℕ) : ℤ) • ((n : ℤ) • u) = (z + (k : ℤ) • ((n : ℤ) • u)) + (n : ℤ) • u := by
      push_cast; rw [add_smul]; abel
    have h1 : z + (k : ℤ) • ((n : ℤ) • u) ∈ U := by
      have := mem_add_nsmul_of_closed hU hz (k * n)
      have e1 : z + ((k * n : ℕ) : ℤ) • u = z + (k : ℤ) • ((n : ℤ) • u) := by push_cast; module
      rwa [e1] at this
    have h2 : z + (k : ℤ) • ((n : ℤ) • u) + (n : ℤ) • u ∈ U := by
      have := mem_add_nsmul_of_closed hU hz ((k + 1) * n)
      have e2 : z + (((k + 1) * n : ℕ) : ℤ) • u = z + (k : ℤ) • ((n : ℤ) • u) + (n : ℤ) • u := by
        push_cast; module
      rwa [e2] at this
    rw [e, hper _ h1 h2, ih]

/-- **Per-line completion by periodicity.**  Agreement on the forward ray `g + ℕ u`, together
with `n u`-periodicity of both configurations on a `+u`-closed set `U`, gives agreement on every
point `g + m u ∈ U`, `m : ℤ` — backwards included. -/
theorem agree_on_line_of_ray_of_period {A : Type*} {x y : Config A} {U : Set (ℤ × ℤ)}
    {u : ℤ × ℤ} (hU : ∀ z ∈ U, z + u ∈ U) {n : ℕ} (hn : 0 < n)
    (hxper : PeriodOn x U ((n : ℤ) • u)) (hyper : PeriodOn y U ((n : ℤ) • u))
    {g : ℤ × ℤ} (hray : ∀ j : ℕ, x (g + (j : ℤ) • u) = y (g + (j : ℤ) • u)) :
    ∀ m : ℤ, g + m • u ∈ U → x (g + m • u) = y (g + m • u) := by
  intro m hm
  set k : ℕ := m.natAbs with hk
  have hnn : 0 ≤ m + (k : ℤ) * (n : ℤ) := by
    have h2 : (k : ℤ) * 1 ≤ (k : ℤ) * (n : ℤ) :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast hn) (Int.natCast_nonneg _)
    omega
  have e : g + m • u + (k : ℤ) • ((n : ℤ) • u) = g + (((m + (k : ℤ) * (n : ℤ)).toNat : ℕ) : ℤ) • u := by
    rw [Int.toNat_of_nonneg hnn, add_smul, mul_smul]; abel
  rw [← eq_add_nsmul_period_of_closed hU hxper hm k, ← eq_add_nsmul_period_of_closed hU hyper hm k,
    e]
  exact hray _

/-- **The gluing step.**  Ladder output (agreement of `x` with `T h' x` on every forward ray
`g i + ℕ u`) plus per-line completion plus a cover of `U` by those lines gives `PeriodOn x U h'`. -/
theorem periodOn_of_ladder_cover {A : Type*} {x : Config A} {U : Set (ℤ × ℤ)} {u : ℤ × ℤ}
    (hU : ∀ z ∈ U, z + u ∈ U) {n : ℕ} (hn : 0 < n)
    (hxper : PeriodOn x U ((n : ℤ) • u)) (h' : ℤ × ℤ)
    (hyper : PeriodOn (T h' x) U ((n : ℤ) • u))
    (g : ℕ → ℤ × ℤ)
    (hlad : ∀ i j : ℕ, x (g i + (j : ℤ) • u) = T h' x (g i + (j : ℤ) • u))
    (hcover : ∀ z ∈ U, ∃ i : ℕ, ∃ m : ℤ, z = g i + m • u) :
    PeriodOn x U h' := by
  refine periodOn_of_agree_T ?_
  intro z hz
  obtain ⟨i, m, rfl⟩ := hcover z hz
  exact agree_on_line_of_ray_of_period hU hn hxper hyper (hlad i) m hz

/-- The cut is closed under `+u`. -/
theorem cut_add_u_mem {R : Set (ℤ × ℤ)} {u u' : ℤ × ℤ} (hR : IsRegion R u u')
    {n : ℤ × ℤ} (hnu : dot n u = 0) (c c₁ : ℤ) :
    ∀ z ∈ (R ∩ halfPlaneGE n c) ∩ {z | dot n z ≤ c₁}, z + u ∈ (R ∩ halfPlaneGE n c) ∩ {z | dot n z ≤ c₁} := by
  rintro z ⟨⟨hzR, hzH⟩, hzL⟩
  obtain ⟨hconv, ⟨z₀, hray⟩, -⟩ := hR
  have hdot : dot n (z + u) = dot n z := by
    simp only [dot, Prod.fst_add, Prod.snd_add] at hnu ⊢; linarith [hnu]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have := ray_all_of_rayIn hconv hray 1 z hzR 1
    simpa using this
  · show c ≤ dot n (z + u); rw [hdot]; exact hzH
  · show dot n (z + u) ≤ c₁; rw [hdot]; exact hzL


/-- **From ladder inputs at cofinally many `r` to `case1_sweep`'s conclusion block.**
Every binder is one of `case1_sweep`'s (`hξ'`, `hgen` via `hSgen`, `hR_region`, `hc`, `hRper`)
or geometric data (`n`, `cQ`, `c₀`, `d`, `q`, `t₀`), except `hladder_assumed`.

Quantifier shape: `∀ N, ∃ r ≥ N` — the ladder is demanded only at cofinally many `r`, and at
each such `r` the data `D, g, s` may depend on `r`.  Not all `r`. -/
theorem sweep_conclusion_of_cofinal_ladders {ξ ξ' : Config ℤ} (hξ' : ξ' ∈ orbitClosure ξ)
    {S : Finset (ℤ × ℤ)} {a : ℤ × ℤ} (hgen : GeneratesAt ξ S a)
    {R : Set (ℤ × ℤ)} {u u' : ℤ × ℤ} (hR_region : IsRegion R u u')
    {c : ℤ} (hc : c ≠ 0) (hRper : PeriodOn ξ' R (c • u))
    (n : ℤ × ℤ) (cQ : ℤ) (hnu : dot n u = 0) (hnu' : 0 < dot n u')
    (c₀ d : ℤ) (hd : 0 < d) (q : ℕ) {t₀ : ℕ} (ht₀ : 0 < t₀)
    (hladder_assumed : ∀ N : ℕ, ∃ r : ℕ, N ≤ r ∧
      ∃ (D : Set (ℤ × ℤ)) (g : ℕ → ℤ × ℤ) (s : ℕ),
        (∀ z ∈ D, ξ' z = T (((t₀ * q : ℕ) : ℤ) • u') ξ' z) ∧
        (∀ i j : ℕ, j < s →
          ξ' (g i + (j : ℤ) • u) = T (((t₀ * q : ℕ) : ℤ) • u') ξ' (g i + (j : ℤ) • u)) ∧
        (∀ i j : ℕ, s ≤ j → ∀ z ∈ S.erase a,
          z + (g i + (j : ℤ) • u - a) ∈
            D ∪ {p | ∃ i' : ℕ, i' < i ∧ ∃ j' : ℕ, p = g i' + (j' : ℤ) • u} ∨
            ∃ j' : ℕ, j' < j ∧ z + (g i + (j : ℤ) • u - a) = g i + (j' : ℤ) • u) ∧
        (∀ z ∈ (R ∩ halfPlaneGE n cQ) ∩ {z | dot n z ≤ c₀ + (r : ℤ) * d},
          ∃ i : ℕ, ∃ m : ℤ, z = g i + m • u)) :
    ∃ K : Set (ℤ × ℤ), K ⊆ R ∧ IsRegion K u u' ∧ K.Nonempty ∧
      ∃ t₀ : ℕ, 0 < t₀ ∧ PeriodOn ξ' K (((t₀ * q : ℕ) : ℤ) • u') := by
  obtain ⟨np, hnp, hnper⟩ := exists_neg_nsmul_period hc hRper
  have hper : PeriodOn ξ' R ((np : ℤ) • u) := by simpa using hnper.neg
  refine sweep_conclusion_of_cofinal_levels hR_region n cQ hnu hnu' n c₀ d hd q ht₀ ?_
  intro N
  obtain ⟨r, hr, D, g, s, hD, hseed, hwin, hcover⟩ := hladder_assumed N
  refine ⟨r, hr, ?_⟩
  have hlad := ladder_of_seeds hξ' (T_mem_of_mem_orbitClosure hξ' _) hgen hD g u s hseed hwin
  exact periodOn_of_ladder_cover (cut_add_u_mem hR_region hnu cQ _) hnp
    (hper.mono (fun z hz => hz.1.1)) _
    ((T_periodOn_of_periodOn_of_ray hR_region hper (t₀ * q)).mono (fun z hz => hz.1.1))
    g hlad hcover

/-! ## §29  `Primitive u` is free: WLOG reduction of `case1_sweep` to a primitive `u`

Question (lead, 2026-09-19): `case1_sweep` (`RegionSteps.lean:1097`) binds `hu'_prim : Primitive u'`
but nothing about `u`, and `u` is produced existentially by L1's export at `:1212`.  If the cover
producer for `hcover` (§28) needs `u` primitive, is that a new L1 export obligation?

**Answer: no — `Primitive u` is derivable at the call site, and this section proves it.**
Every `u`-mentioning binder of `case1_sweep` — `hdet hc hRper hR_region hQR` — and its conclusion
`IsRegion K u u'` transfer between `u` and the primitive `u₀` with `u = k • u₀`, `0 < k`
(`Nivat.exists_primitive_nsmul_eq`, `Lattice/Primitive.lean:52`).  The remaining binders
(`hξ hSgen hξ' hQS hu'_prim hdef41 hline hB_covers_window hamb` and the `q`-hypothesis at `:1131`)
mention no `u` at all, so they pass through unchanged.

The one direction the lead flagged as "not free" — a ray along `k • u₀` giving a ray along `u₀` —
*is* free for a lattice-convex region, which is what `IsRegion` demands: `toReal (k • u₀)` lies in
the recession cone `K_R` (`toReal_mem_recCone_of_nat_ray`), `K_R` is a cone
(`smul_mem_recCone` with the scalar `1/k`), so `toReal u₀ ∈ K_R`, and `subset_of_mem_recCone`
turns that into `R + u₀ ⊆ R`.  A bare set with a ray along `2 u₀` need not contain a ray along `u₀`;
a lattice-convex region does — the lead's reasoning was right for sets and wrong for regions.

What primitivity actually buys the cover (answer to the lead's question 1): `hcover` alone needs
nothing — any enumeration of `ℤ²` satisfies it with `m = 0`.  What needs each `n`-level to be a
*single* coset `g + ℤ u` is `hwin`'s same-line clause in `ladder_of_seeds`: the window's
same-level points must lie on the current line at `j' < j`, and that is only possible if the level
is one line.  `exists_zsmul_of_dot_perp_eq` below shows a level is one coset when `u` is primitive
and `n = (-u.2, u.1)`; `level_not_coset_of_nonprimitive` shows it is not when `u = (2, 0)`.
So the requirement is exactly `Primitive u` (for the normal `n = u^⊥`), and it is free. -/

/-- Lattice-convex regions divide rays: a ray along `k • u₀`, `0 < k`, gives `R + u₀ ⊆ R`. -/
theorem add_mem_of_rayIn_nsmul {R : Set (ℤ × ℤ)} (hR : IsLatticeConvexRegion R)
    {z₀ u₀ : ℤ × ℤ} {k : ℕ} (hk : 0 < k) (hray : RayIn R z₀ ((k : ℤ) • u₀)) :
    ∀ z ∈ R, z + u₀ ∈ R := by
  have hrec : toReal ((k : ℤ) • u₀) ∈ recCone R := toReal_mem_recCone_of_nat_ray hray
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hrec₀ : toReal u₀ ∈ recCone R := by
    have := smul_mem_recCone (le_of_lt (inv_pos.mpr hk')) hrec
    rwa [toReal_zsmul, smul_smul, Int.cast_natCast, inv_mul_cancel₀ hk'.ne', one_smul] at this
  exact subset_of_mem_recCone hR hrec₀

/-- The ray form of `add_mem_of_rayIn_nsmul`: `RayIn R z₀ (k • u₀)` with `0 < k` gives
`RayIn R z₀ u₀` — the direction the lead flagged as not free.  It is, for lattice-convex `R`. -/
theorem rayIn_of_rayIn_nsmul {R : Set (ℤ × ℤ)} (hR : IsLatticeConvexRegion R)
    {z₀ u₀ : ℤ × ℤ} {k : ℕ} (hk : 0 < k) (hray : RayIn R z₀ ((k : ℤ) • u₀)) :
    RayIn R z₀ u₀ := fun j =>
  mem_add_nsmul_of_closed (add_mem_of_rayIn_nsmul hR hk hray) (by simpa using hray 0) j

/-- `IsRegion R (k • u₀) u'` with `0 < k` gives `IsRegion R u₀ u'`. -/
theorem isRegion_of_isRegion_nsmul {R : Set (ℤ × ℤ)} {u₀ u' : ℤ × ℤ} {k : ℕ} (hk : 0 < k)
    (hR : IsRegion R ((k : ℤ) • u₀) u') : IsRegion R u₀ u' :=
  ⟨hR.1, (hR.2.1).imp (fun _ h => rayIn_of_rayIn_nsmul hR.1 hk h), hR.2.2⟩

/-- The easy converse, for the conclusion: `IsRegion K u₀ u'` gives `IsRegion K (k • u₀) u'`. -/
theorem isRegion_nsmul_of_isRegion {R : Set (ℤ × ℤ)} {u₀ u' : ℤ × ℤ} (k : ℕ)
    (hR : IsRegion R u₀ u') : IsRegion R ((k : ℤ) • u₀) u' :=
  ⟨hR.1, (hR.2.1).imp (fun _ h => h.nsmul k), hR.2.2⟩

/-- **WLOG `u` primitive, generic form** (serves both leaves: Case 1's `case1_sweep` and C's
`hsweep` in `RegionClaim411.lean:377-381`, which is the same conclusion block with
`u := p, u' := cg.vJ, ξ' := ϑ, R := shellInf ε`).  Only the two binders that every instantiation
has — `hdet` and `hR_region` — are consumed; the decomposition `u = k • u₀` is *exposed* to
`hprim_case`, so any further `u`-mentioning binder (`hRper`, `hQR`, …) can be transported by the
caller with `rw [hu]`.  The period binder is not even mentioned. -/
theorem sweep_conclusion_wlog_primitive {ξ' : Config ℤ}
    {u u' : ℤ × ℤ} {R : Set (ℤ × ℤ)}
    (hdet : det u u' ≠ 0) (hR_region : IsRegion R u u') (q : ℕ)
    (hprim_case : ∀ (u₀ : ℤ × ℤ) (k : ℕ), Primitive u₀ → 0 < k → u = (k : ℤ) • u₀ →
      det u₀ u' ≠ 0 → IsRegion R u₀ u' →
      ∃ K : Set (ℤ × ℤ), K ⊆ R ∧ IsRegion K u₀ u' ∧ K.Nonempty ∧
        ∃ t₀ : ℕ, 0 < t₀ ∧ PeriodOn ξ' K (((t₀ * q : ℕ) : ℤ) • u')) :
    ∃ K : Set (ℤ × ℤ), K ⊆ R ∧ IsRegion K u u' ∧ K.Nonempty ∧
      ∃ t₀ : ℕ, 0 < t₀ ∧ PeriodOn ξ' K (((t₀ * q : ℕ) : ℤ) • u') := by
  have hu : u ≠ 0 := by rintro rfl; exact hdet (by simp [det])
  obtain ⟨u₀, k, hprim, hk, hku⟩ := exists_primitive_nsmul_eq hu
  have hdet₀ : det u₀ u' ≠ 0 := by
    intro h; apply hdet
    have : det ((k : ℤ) • u₀) u' = (k : ℤ) * det u₀ u' := by
      simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
    rw [hku, this, h, mul_zero]
  obtain ⟨K, hKR, hKreg, hKne, t₀, ht₀, hKper⟩ :=
    hprim_case u₀ k hprim hk hku hdet₀ (isRegion_of_isRegion_nsmul hk (hku ▸ hR_region))
  exact ⟨K, hKR, hku ▸ isRegion_nsmul_of_isRegion k hKreg, hKne, t₀, ht₀, hKper⟩

/-- **WLOG `u` primitive, Case 1 letters.**  If the conclusion block of `case1_sweep` holds
whenever the direction is primitive (hypothesis `hprim_case`, which restates the five
`u`-mentioning binders of `case1_sweep` for a primitive `u₀` and a rescaled `c₀`), then it holds
for the given `u`.  Instance of `sweep_conclusion_wlog_primitive` with `hRper`, `hc`, `hQR`
transported through `u = k • u₀`, `c₀ := c * k`.  Nothing about `ξ ξ' S Q B τ pw` is touched. -/
theorem case1_sweep_conclusion_wlog_primitive {ξ' : Config ℤ}
    {u u' : ℤ × ℤ} {Q : Finset (ℤ × ℤ)} {τ : ℤ} {R : Set (ℤ × ℤ)} {c : ℤ}
    (hdet : det u u' ≠ 0) (hc : c ≠ 0)
    (hRper : PeriodOn ξ' R (c • u)) (hR_region : IsRegion R u u')
    (hQR : ∀ t : ℤ, τ ≤ t → ∀ z ∈ Q, t • u' + z ∈ R ∧ t • u' + z + c • u ∈ R)
    (q : ℕ)
    (hprim_case : ∀ (u₀ : ℤ × ℤ) (c₀ : ℤ), Primitive u₀ → det u₀ u' ≠ 0 → c₀ ≠ 0 →
      PeriodOn ξ' R (c₀ • u₀) → IsRegion R u₀ u' →
      (∀ t : ℤ, τ ≤ t → ∀ z ∈ Q, t • u' + z ∈ R ∧ t • u' + z + c₀ • u₀ ∈ R) →
      ∃ K : Set (ℤ × ℤ), K ⊆ R ∧ IsRegion K u₀ u' ∧ K.Nonempty ∧
        ∃ t₀ : ℕ, 0 < t₀ ∧ PeriodOn ξ' K (((t₀ * q : ℕ) : ℤ) • u')) :
    ∃ K : Set (ℤ × ℤ), K ⊆ R ∧ IsRegion K u u' ∧ K.Nonempty ∧
      ∃ t₀ : ℕ, 0 < t₀ ∧ PeriodOn ξ' K (((t₀ * q : ℕ) : ℤ) • u') := by
  refine sweep_conclusion_wlog_primitive hdet hR_region q ?_
  intro u₀ k hprim hk hku hdet₀ hreg₀
  subst hku
  have hkz : (k : ℤ) ≠ 0 := by exact_mod_cast hk.ne'
  have hcs : c • ((k : ℤ) • u₀) = (c * k) • u₀ := smul_smul _ _ _
  exact hprim_case u₀ (c * k) hprim hdet₀ (mul_ne_zero hc hkz) (by rw [← hcs]; exact hRper)
    hreg₀ (fun t ht z hz => by rw [← hcs]; exact hQR t ht z hz)

/-- What primitivity buys the cover: with `u` primitive and `n := (-u.2, u.1)` its normal,
`dot n z = det u z`, so two lattice points on one `n`-level differ by an integer multiple of `u` —
each level is a single coset `g + ℤ u`.  This is the `hcover` / `hwin` same-line input. -/
theorem exists_zsmul_of_dot_perp_eq {u : ℤ × ℤ} (hu : Primitive u) {z w : ℤ × ℤ}
    (h : dot (-u.2, u.1) z = dot (-u.2, u.1) w) : ∃ m : ℤ, z = w + m • u := by
  have hd : det u (z - w) = 0 := by
    simp only [det, dot, Prod.fst_sub, Prod.snd_sub] at h ⊢; linarith
  obtain ⟨m, hm⟩ := eq_zsmul_of_det_eq_zero hu hd
  exact ⟨m, by rw [← hm]; abel⟩

/-- And what its absence costs: for `u = (2, 0)`, `n = (0, 2)`, the points `(1, 0)` and `(0, 0)`
share the level `dot n = 0` but differ by no multiple of `u`.  Levels split into `k` cosets. -/
theorem level_not_coset_of_nonprimitive :
    dot (0, 2) ((1 : ℤ), (0 : ℤ)) = dot (0, 2) (0, 0)
      ∧ ∀ m : ℤ, ((1 : ℤ), (0 : ℤ)) ≠ (0, 0) + m • ((2 : ℤ), (0 : ℤ)) := by
  refine ⟨by simp [dot], fun m h => ?_⟩
  have := congrArg Prod.fst h
  simp at this
  omega

/-! ## §30  The level enumeration: `hcover` and `hwin`'s cross-level clause, produced

Item (1') of the 2026-09-19 report.  §28 left `hladder_assumed` as one blob (seed ∧ window ∧
cover per good `r`).  This section produces the window and cover clauses from a concrete
enumeration, leaving **only the seed** unproduced.

**The frame** (`LevelFrame u u'`): `n` is a normal to `u` with `dot n u' > 0`; `dv` is a lattice
vector with `dot n dv = 1` (one level per step); `d'` is the dual coordinate with `dot d' u = 1`,
`dot d' dv = 0`.  `decomp` says `(d', n)` are coordinates: `z = dot d' z • u + dot n z • dv`.
The extra sign condition `dot d' u' ≤ 0` is what makes `dv` a *nonnegative* real combination of
`u` and `u'`, so a region with rays along `u` and `u'` absorbs `+dv` (`add_nsmul_dv_mem`) — that is
how the band's base points `b₀ + j₀ • dv` are placed inside `R` without any extra hypothesis.
`exists_levelFrame` builds one from `Primitive u` and `det u u' ≠ 0` (Bézout dual + a shear
`dv := σ e + m u` with `m = (det u' e)⁺` to fix the sign).

**What `Primitive u` is used for** (answer to the lead's question 1, now kernel-checked rather
than hand-read): only `exists_levelFrame`.  A level `{dot n = const}` must be a single coset
`g + ℤ u` for `hwin`'s same-line clause; that needs `dot n dv = 1` with `n ⊥ u`, i.e. `u`
primitive (`level_not_coset_of_nonprimitive`, §29).  §29's WLOG supplies it for free.

**The enumeration** (`levelLine fr top M m₀ W i`): line `i` is the level `top − min i M`, based at
`d'`-coordinate `m₀ + (min i M) · W`.  Lines descend one level per index from `top` (the level just
below the band) down to `cQ` (the cut), and each line's base is pushed `W` further along `u` than
the previous one's, where `W` bounds the `d'`-extent of `S` behind its vertex — so a window placed
at `g i + j u`, `j ≥ Wrow`, reaches earlier lines only at `d'`-coordinates ≥ their bases
(`hwin_of_levelLine`, case "lands on an earlier line").  Beyond `M` the enumeration is constant,
which is harmless: `hcover` only needs surjectivity onto the cut (`cover_of_levelLine`).

**The vertex** (`exists_vertex`, `latticeConvex_erase_of_vertex`, `exists_generating_vertex`):
`a` is the lex-max of `S` for `(−dot n, dot d')`, i.e. on the *lowest* level of `S` and furthest
along `+u` there.  `S.erase a` is lattice-convex by
`Nivat.Colle37Geom.latticeConvex_erase_of_lexExtreme` (`ShellGeom.lean:60`, §20 pickup — the §20
scan also found `latticeConvex_erase_of_extremePoint` (`LowComplexityWindow.lean:41`), which wants
`extremePoints ℝ` and would need a lex-max-is-extreme bridge; the lex form is the one that
matches).  So `IsGeneratingSet ξ S` pays out `GeneratesAt ξ S a` at exactly this `a`.

**Quantifier shape.**  Every statement is `∀ i j` over the lines of **one** good `r`; the band's
"infinitely many `r`" is consumed by §28's `hladder_assumed`, never promoted to all `r`.
The seed in `sweep_conclusion_of_levelFrame_of_seed_assumed` is *conditional* on the band's
agreement at that same `r`, so it asks nothing where the band is silent. -/

theorem dot_zsmul' (n : ℤ × ℤ) (k : ℤ) (v : ℤ × ℤ) : dot n (k • v) = k * dot n v := by
  simp only [dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

structure LevelFrame (u u' : ℤ × ℤ) where
  n : ℤ × ℤ
  dv : ℤ × ℤ
  d' : ℤ × ℤ
  dot_n_u : dot n u = 0
  dot_n_u' : 0 < dot n u'
  dot_n_dv : dot n dv = 1
  dot_d'_u : dot d' u = 1
  dot_d'_dv : dot d' dv = 0
  dot_d'_u' : dot d' u' ≤ 0
  decomp : ∀ z : ℤ × ℤ, z = dot d' z • u + dot n z • dv

namespace LevelFrame

variable {u u' : ℤ × ℤ} (fr : LevelFrame u u')

theorem ext_dots {w w' : ℤ × ℤ} (h1 : dot fr.n w = dot fr.n w')
    (h2 : dot fr.d' w = dot fr.d' w') : w = w' :=
  calc w = dot fr.d' w • u + dot fr.n w • fr.dv := fr.decomp w
    _ = dot fr.d' w' • u + dot fr.n w' • fr.dv := by rw [h1, h2]
    _ = w' := (fr.decomp w').symm

theorem add_nsmul_dv_mem {K : Set (ℤ × ℤ)} (hK : IsRegion K u u') {z₀ : ℤ × ℤ}
    (hz₀ : z₀ ∈ K) (j : ℕ) : z₀ + (j : ℤ) • fr.dv ∈ K := by
  have hD : (0 : ℝ) < (dot fr.n u' : ℝ) := by exact_mod_cast fr.dot_n_u'
  have hd' : (dot fr.d' u' : ℝ) ≤ 0 := by exact_mod_cast fr.dot_d'_u'
  have h := fr.decomp u'
  have h1 : (u'.1 : ℝ) = (dot fr.d' u' : ℝ) * u.1 + (dot fr.n u' : ℝ) * fr.dv.1 := by
    have := congrArg Prod.fst h
    simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul] at this
    exact_mod_cast this
  have h2 : (u'.2 : ℝ) = (dot fr.d' u' : ℝ) * u.2 + (dot fr.n u' : ℝ) * fr.dv.2 := by
    have := congrArg Prod.snd h
    simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul] at this
    exact_mod_cast this
  refine mem_of_nonneg_real_comb hK hz₀
    (a := (j : ℝ) * (-(dot fr.d' u' : ℝ)) / (dot fr.n u' : ℝ))
    (b := (j : ℝ) / (dot fr.n u' : ℝ)) ?_ ?_ ?_
  · exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (by linarith)) hD.le
  · exact div_nonneg (Nat.cast_nonneg _) hD.le
  · apply Prod.ext
    · simp only [toReal, Prod.smul_fst, Prod.fst_add, smul_eq_mul, Int.cast_mul, Int.cast_natCast]
      rw [h1]; field_simp; ring
    · simp only [toReal, Prod.smul_snd, Prod.snd_add, smul_eq_mul, Int.cast_mul, Int.cast_natCast]
      rw [h2]; field_simp; ring

end LevelFrame

theorem exists_levelFrame {u u' : ℤ × ℤ} (hu : Primitive u) (hdet : det u u' ≠ 0) :
    Nonempty (LevelFrame u u') := by
  obtain ⟨e, he⟩ := hu.exists_dual
  obtain ⟨σ, hσ, hσdet⟩ : ∃ σ : ℤ, σ * σ = 1 ∧ 0 < σ * det u u' := by
    rcases lt_or_gt_of_ne hdet with h | h
    · exact ⟨-1, by ring, by linarith⟩
    · exact ⟨1, by ring, by linarith⟩
  set m : ℕ := (det u' e).toNat with hm
  have hm0 : (0 : ℤ) ≤ m := Int.natCast_nonneg _
  have hm1 : det u' e ≤ (m : ℤ) := Int.self_le_toNat _
  set dv : ℤ × ℤ := σ • e + (m : ℤ) • u with hdv
  have hdet_dv : det u dv = σ := by
    simp only [hdv, det, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    simp only [det] at he
    linear_combination σ * he
  have hdet_u'dv : det u' dv = det u' e * σ - (m : ℤ) * det u u' := by
    simp only [hdv, det, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  simp only [det] at he hdet_dv hdet_u'dv hσdet
  refine ⟨⟨(-(σ * u.2), σ * u.1), dv, (σ * dv.2, -(σ * dv.1)), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · simp only [dot]; ring
  · simp only [dot]; linarith
  · simp only [dot]
    linear_combination σ * hdet_dv + hσ
  · simp only [dot]
    linear_combination σ * hdet_dv + hσ
  · simp only [dot]; ring
  · simp only [dot]
    -- `σ * det u' dv = det u' e * σ² - m * σ * det u u' = det u' e - m * (σ det u u') ≤ 0`
    have hmD : (m : ℤ) ≤ (m : ℤ) * (σ * (u.1 * u'.2 - u.2 * u'.1)) :=
      le_mul_of_one_le_right hm0 (by omega)
    have hsq : σ * (u'.1 * dv.2 - u'.2 * dv.1) =
        (u'.1 * e.2 - u'.2 * e.1) * (σ * σ) - (m : ℤ) * (σ * (u.1 * u'.2 - u.2 * u'.1)) := by
      linear_combination σ * hdet_u'dv
    have hlin : σ * (u'.1 * dv.2 - u'.2 * dv.1) =
        (u'.1 * e.2 - u'.2 * e.1) - (m : ℤ) * (σ * (u.1 * u'.2 - u.2 * u'.1)) := by
      rw [hsq, hσ]; ring
    have hm1' := hm1
    simp only [det] at hm1'
    linarith
  · intro z
    apply Prod.ext
    · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, dot]
      linear_combination (-(σ * z.1)) * hdet_dv + (-z.1) * hσ
    · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, dot]
      linear_combination (-(σ * z.2)) * hdet_dv + (-z.2) * hσ

/-! ### The enumeration -/

def levelLine {u u' : ℤ × ℤ} (fr : LevelFrame u u') (top : ℤ) (M : ℕ) (m₀ : ℤ) (W : ℕ)
    (i : ℕ) : ℤ × ℤ :=
  (top - ((min i M : ℕ) : ℤ)) • fr.dv + (m₀ + ((min i M : ℕ) : ℤ) * W) • u

theorem dot_n_levelLine {u u' : ℤ × ℤ} (fr : LevelFrame u u') (top : ℤ) (M : ℕ) (m₀ : ℤ)
    (W : ℕ) (i : ℕ) : dot fr.n (levelLine fr top M m₀ W i) = top - ((min i M : ℕ) : ℤ) := by
  simp only [levelLine, Nivat.LE2.dot_add, dot_zsmul', fr.dot_n_dv, fr.dot_n_u]; ring

theorem dot_d'_levelLine {u u' : ℤ × ℤ} (fr : LevelFrame u u') (top : ℤ) (M : ℕ) (m₀ : ℤ)
    (W : ℕ) (i : ℕ) : dot fr.d' (levelLine fr top M m₀ W i) = m₀ + ((min i M : ℕ) : ℤ) * W := by
  simp only [levelLine, Nivat.LE2.dot_add, dot_zsmul', fr.dot_d'_dv, fr.dot_d'_u]; ring

def bandSet {u u' : ℤ × ℤ} (fr : LevelFrame u u') (b₀ v : ℤ × ℤ) (H : ℕ) : Set (ℤ × ℤ) :=
  {w | ∃ j₀ : ℕ, j₀ ≤ H ∧ ∃ k : ℕ, w = b₀ + (j₀ : ℤ) • fr.dv + v + (k : ℤ) • u}

theorem agree_on_bandSet {ξ' : Config ℤ} {u u' : ℤ × ℤ} (fr : LevelFrame u u')
    (b₀ v : ℤ × ℤ) (H : ℕ) (h' : ℤ × ℤ)
    (hband : ∀ g ∈ (Finset.range (H + 1)).image (fun j₀ : ℕ => b₀ + (j₀ : ℤ) • fr.dv),
      ∀ k : ℕ, ξ' (g + v + (k : ℤ) • u) = T h' ξ' (g + v + (k : ℤ) • u)) :
    ∀ w ∈ bandSet fr b₀ v H, ξ' w = T h' ξ' w := by
  rintro w ⟨j₀, hj₀, k, rfl⟩
  exact hband _ (Finset.mem_image.mpr ⟨j₀, Finset.mem_range.mpr (by omega), rfl⟩) k

theorem cover_of_levelLine {u u' : ℤ × ℤ} (fr : LevelFrame u u') {top cQ : ℤ} {M : ℕ}
    (hM : top - cQ ≤ M) (m₀ : ℤ) (W : ℕ) :
    ∀ z : ℤ × ℤ, cQ ≤ dot fr.n z → dot fr.n z ≤ top →
      ∃ i : ℕ, ∃ m : ℤ, z = levelLine fr top M m₀ W i + m • u := by
  intro z h1 h2
  set ι : ℕ := (top - dot fr.n z).toNat with hι
  have hιM : ι ≤ M := by omega
  have hmin : min ι M = ι := min_eq_left hιM
  have hιval : (ι : ℤ) = top - dot fr.n z := by omega
  refine ⟨ι, dot fr.d' z - (m₀ + (ι : ℤ) * W), fr.ext_dots ?_ ?_⟩
  · rw [Nivat.LE2.dot_add, dot_zsmul', fr.dot_n_u, dot_n_levelLine, hmin]; omega
  · rw [Nivat.LE2.dot_add, dot_zsmul', fr.dot_d'_u, dot_d'_levelLine, hmin]; ring

theorem hwin_of_levelLine {u u' : ℤ × ℤ} (fr : LevelFrame u u') {S : Finset (ℤ × ℤ)}
    {a : ℤ × ℤ}
    (hvert : ∀ b ∈ S.erase a,
      dot fr.n a < dot fr.n b ∨ (dot fr.n a = dot fr.n b ∧ dot fr.d' b < dot fr.d' a))
    {H W Wrow : ℕ}
    (hH : ∀ z ∈ S, dot fr.n z - dot fr.n a ≤ H)
    (hW : ∀ z ∈ S, dot fr.d' a - dot fr.d' z ≤ W)
    (hWrow : ∀ z ∈ S, dot fr.n z = dot fr.n a → dot fr.d' a - dot fr.d' z ≤ Wrow)
    (b₀ v : ℤ × ℤ) (M : ℕ) :
    ∀ i j : ℕ, Wrow ≤ j → ∀ z ∈ S.erase a,
      z + (levelLine fr (dot fr.n (b₀ + v) - 1) M (dot fr.d' (b₀ + v) + W) W i
            + (j : ℤ) • u - a) ∈
        bandSet fr b₀ v H ∪
          {p | ∃ i' : ℕ, i' < i ∧ ∃ j' : ℕ,
            p = levelLine fr (dot fr.n (b₀ + v) - 1) M (dot fr.d' (b₀ + v) + W) W i'
                  + (j' : ℤ) • u} ∨
        ∃ j' : ℕ, j' < j ∧
          z + (levelLine fr (dot fr.n (b₀ + v) - 1) M (dot fr.d' (b₀ + v) + W) W i
                + (j : ℤ) • u - a) =
            levelLine fr (dot fr.n (b₀ + v) - 1) M (dot fr.d' (b₀ + v) + W) W i
              + (j' : ℤ) • u := by
  intro i j hj z hz
  set top : ℤ := dot fr.n (b₀ + v) - 1 with htop
  set mb : ℤ := dot fr.d' (b₀ + v) with hmb
  set m₀ : ℤ := mb + W with hm₀
  set ι : ℕ := min i M with hι
  have hιi : ι ≤ i := min_le_left _ _
  have hιM : ι ≤ M := min_le_right _ _
  set p : ℤ × ℤ := levelLine fr top M m₀ W i with hp
  have hpn : dot fr.n p = top - ι := dot_n_levelLine fr top M m₀ W i
  have hpd : dot fr.d' p = m₀ + (ι : ℤ) * W := dot_d'_levelLine fr top M m₀ W i
  set w : ℤ × ℤ := z + (p + (j : ℤ) • u - a) with hw
  have hwn : dot fr.n w = dot fr.n z + (top - ι) - dot fr.n a := by
    simp only [hw, Nivat.LE2.dot_add, Nivat.LE2.dot_sub, dot_zsmul', fr.dot_n_u, hpn]; ring
  have hwd : dot fr.d' w = dot fr.d' z + (m₀ + (ι : ℤ) * W) + j - dot fr.d' a := by
    simp only [hw, Nivat.LE2.dot_add, Nivat.LE2.dot_sub, dot_zsmul', fr.dot_d'_u, hpd]; ring
  have hzS : z ∈ S := (Finset.mem_erase.mp hz).2
  have hWz := hW z hzS
  have hW0 : (0 : ℤ) ≤ W := Int.natCast_nonneg _
  rcases hvert z hz with hlt | ⟨heq, hdlt⟩
  · -- cross-level: `z` sits `k ≥ 1` levels above `a`
    have hk := hH z hzS
    by_cases hcase : dot fr.n z - dot fr.n a ≤ ι
    · -- lands on an earlier line
      set kk : ℕ := (dot fr.n z - dot fr.n a).toNat with hkk
      have hkkval : (kk : ℤ) = dot fr.n z - dot fr.n a := by omega
      have hkk1 : 1 ≤ kk := by omega
      have hkkι : kk ≤ ι := by omega
      set i' : ℕ := ι - kk with hi'
      have hi'ι : i' + kk = ι := by omega
      have hi'M : i' ≤ M := by omega
      have hmin' : min i' M = i' := min_eq_left hi'M
      have hi'W : (i' : ℤ) * W ≤ ((ι : ℤ) - 1) * W :=
        mul_le_mul_of_nonneg_right (by omega) hW0
      have hnn : 0 ≤ dot fr.d' w - (m₀ + (i' : ℤ) * W) := by rw [hwd]; linarith
      refine Or.inl (Or.inr ⟨i', by omega, (dot fr.d' w - (m₀ + (i' : ℤ) * W)).toNat,
        fr.ext_dots ?_ ?_⟩)
      · rw [hwn, Nivat.LE2.dot_add, dot_zsmul', fr.dot_n_u, dot_n_levelLine, hmin']; omega
      · rw [Int.toNat_of_nonneg hnn, hwd, Nivat.LE2.dot_add, dot_zsmul', fr.dot_d'_u,
          dot_d'_levelLine, hmin']; ring
    · -- above the top line: in the band
      push Not at hcase
      have hιW : (0 : ℤ) ≤ (ι : ℤ) * W := mul_nonneg (Int.natCast_nonneg _) hW0
      have hj0 : 0 ≤ dot fr.n z - dot fr.n a - 1 - ι := by omega
      have hk0 : 0 ≤ dot fr.d' w - mb := by rw [hwd]; linarith
      refine Or.inl (Or.inl ⟨(dot fr.n z - dot fr.n a - 1 - ι).toNat, by omega,
        (dot fr.d' w - mb).toNat, fr.ext_dots ?_ ?_⟩)
      · simp only [Nivat.LE2.dot_add, dot_zsmul', fr.dot_n_u, fr.dot_n_dv,
          Int.toNat_of_nonneg hj0, hwn]
        rw [htop, Nivat.LE2.dot_add]; ring
      · rw [Int.toNat_of_nonneg hk0]
        simp only [Nivat.LE2.dot_add, dot_zsmul', fr.dot_d'_u, fr.dot_d'_dv, hwd]
        rw [hmb, Nivat.LE2.dot_add]; ring
  · -- same level as `a`: `z` is strictly behind `a` along `u`
    have hrow := hWrow z hzS heq.symm
    set t : ℕ := (dot fr.d' a - dot fr.d' z).toNat with ht
    have htval : (t : ℤ) = dot fr.d' a - dot fr.d' z := by omega
    have ht1 : 1 ≤ t := by omega
    have htj : t ≤ j := by omega
    refine Or.inr ⟨j - t, by omega, fr.ext_dots ?_ ?_⟩
    · rw [hwn, Nivat.LE2.dot_add, dot_zsmul', fr.dot_n_u, hpn]; omega
    · rw [hwd, Nivat.LE2.dot_add, dot_zsmul', fr.dot_d'_u, hpd, Nat.cast_sub htj]; linarith

/-! ### The vertex -/

theorem exists_vertex {u u' : ℤ × ℤ} (fr : LevelFrame u u') {S : Finset (ℤ × ℤ)}
    (hS : S.Nonempty) :
    ∃ a ∈ S, ∀ b ∈ S.erase a,
      dot fr.n a < dot fr.n b ∨ (dot fr.n a = dot fr.n b ∧ dot fr.d' b < dot fr.d' a) := by
  obtain ⟨a, ha, hmax⟩ :=
    Finset.exists_max_image S (fun z => toLex (-dot fr.n z, dot fr.d' z)) hS
  refine ⟨a, ha, fun b hb => ?_⟩
  obtain ⟨hne, hbS⟩ := Finset.mem_erase.mp hb
  have h := hmax b hbS
  rw [Prod.Lex.toLex_le_toLex] at h
  dsimp only at h
  rcases h with h | ⟨h1, h2⟩
  · left; linarith
  · right
    refine ⟨by linarith, lt_of_le_of_ne h2 ?_⟩
    intro heq
    exact hne (fr.ext_dots (by linarith) heq)

theorem latticeConvex_erase_of_vertex {u u' : ℤ × ℤ} (fr : LevelFrame u u')
    {S : Finset (ℤ × ℤ)} (hS : LatticeConvex S) {a : ℤ × ℤ}
    (hvert : ∀ b ∈ S.erase a,
      dot fr.n a < dot fr.n b ∨ (dot fr.n a = dot fr.n b ∧ dot fr.d' b < dot fr.d' a)) :
    LatticeConvex (S.erase a) := by
  apply Nivat.Colle37Geom.latticeConvex_erase_of_lexExtreme hS (n := -fr.n) (d := fr.d')
  intro b hb
  rcases hvert b hb with h | ⟨h1, h2⟩
  · left; rw [Nivat.LE2.dot_neg_left, Nivat.LE2.dot_neg_left]; linarith
  · right; exact ⟨by rw [Nivat.LE2.dot_neg_left, Nivat.LE2.dot_neg_left, h1], h2⟩

theorem exists_generating_vertex {ξ : Config ℤ} {u u' : ℤ × ℤ} (fr : LevelFrame u u')
    {S : Finset (ℤ × ℤ)} (hS : IsGeneratingSet ξ S) :
    ∃ a ∈ S, GeneratesAt ξ S a ∧ ∀ b ∈ S.erase a,
      dot fr.n a < dot fr.n b ∨ (dot fr.n a = dot fr.n b ∧ dot fr.d' b < dot fr.d' a) := by
  obtain ⟨a, ha, hvert⟩ := exists_vertex fr hS.1
  exact ⟨a, ha, hS.2.2 a ha (latticeConvex_erase_of_vertex fr hS.2.1 hvert), hvert⟩

/-! ### Assembly -/

def Hsup {u u' : ℤ × ℤ} (fr : LevelFrame u u') (S : Finset (ℤ × ℤ)) (a : ℤ × ℤ) : ℕ :=
  S.sup (fun z => (dot fr.n z - dot fr.n a).toNat)

def Wsup {u u' : ℤ × ℤ} (fr : LevelFrame u u') (S : Finset (ℤ × ℤ)) (a : ℤ × ℤ) : ℕ :=
  S.sup (fun z => (dot fr.d' a - dot fr.d' z).toNat)

def Wrow {u u' : ℤ × ℤ} (fr : LevelFrame u u') (S : Finset (ℤ × ℤ)) (a : ℤ × ℤ) : ℕ :=
  (S.filter (fun z => dot fr.n z = dot fr.n a)).sup (fun z => (dot fr.d' a - dot fr.d' z).toNat)

abbrev rowLine {u u' : ℤ × ℤ} (fr : LevelFrame u u') (b₀ : ℤ × ℤ) (cQ : ℤ) (q W : ℕ)
    (r i : ℕ) : ℤ × ℤ :=
  levelLine fr (dot fr.n (b₀ + (r : ℤ) • ((q : ℤ) • u')) - 1)
    (dot fr.n (b₀ + (r : ℤ) • ((q : ℤ) • u')) - 1 - cQ).toNat
    (dot fr.d' (b₀ + (r : ℤ) • ((q : ℤ) • u')) + W) W i

theorem le_Hsup {u u' : ℤ × ℤ} (fr : LevelFrame u u') {S : Finset (ℤ × ℤ)} (a : ℤ × ℤ) :
    ∀ z ∈ S, dot fr.n z - dot fr.n a ≤ Hsup fr S a := fun z hz =>
  le_trans (Int.self_le_toNat _)
    (by exact_mod_cast Finset.le_sup (f := fun z => (dot fr.n z - dot fr.n a).toNat) hz)

theorem le_Wsup {u u' : ℤ × ℤ} (fr : LevelFrame u u') {S : Finset (ℤ × ℤ)} (a : ℤ × ℤ) :
    ∀ z ∈ S, dot fr.d' a - dot fr.d' z ≤ Wsup fr S a := fun z hz =>
  le_trans (Int.self_le_toNat _)
    (by exact_mod_cast Finset.le_sup (f := fun z => (dot fr.d' a - dot fr.d' z).toNat) hz)

theorem le_Wrow {u u' : ℤ × ℤ} (fr : LevelFrame u u') {S : Finset (ℤ × ℤ)} (a : ℤ × ℤ) :
    ∀ z ∈ S, dot fr.n z = dot fr.n a → dot fr.d' a - dot fr.d' z ≤ Wrow fr S a :=
  fun z hz hrow => by
  have hmem : z ∈ S.filter (fun z => dot fr.n z = dot fr.n a) :=
    Finset.mem_filter.mpr ⟨hz, hrow⟩
  have h := Finset.le_sup (f := fun z => (dot fr.d' a - dot fr.d' z).toNat) hmem
  exact le_trans (Int.self_le_toNat _) (by exact_mod_cast h)



/-- **Assembly: band + level enumeration + vertex → the sweep's conclusion, modulo the seed.**

Everything in `hladder_assumed` (§28) is now produced *except* the per-line seed, which is the
single remaining assumption.  Its shape is deliberately conditional: for the `t₀` and the good `r`
that the band (§23) hands over, and **given** the band's own agreement at that `r`, the first
`Wrow` points of every enumerated line agree.  Nothing is asked at `r` where the band is silent.

🔴 `hseed_assumed` has no producer.  It is the `B`-width question (`LEAF-L3.md`), unchanged. -/
theorem sweep_conclusion_of_levelFrame_of_seed_assumed {ξ ξ' : Config ℤ}
    (hfin : (Set.range ξ').Finite) (hξ' : ξ' ∈ orbitClosure ξ)
    {S : Finset (ℤ × ℤ)} {R : Set (ℤ × ℤ)} {u u' : ℤ × ℤ} (hR_region : IsRegion R u u')
    {c : ℤ} (hc : c ≠ 0) (hRper : PeriodOn ξ' R (c • u))
    (fr : LevelFrame u u') {a : ℤ × ℤ} (hgen : GeneratesAt ξ S a)
    (hvert : ∀ b ∈ S.erase a,
      dot fr.n a < dot fr.n b ∨ (dot fr.n a = dot fr.n b ∧ dot fr.d' b < dot fr.d' a))
    (cQ : ℤ) {q : ℕ} (hq : 0 < q) {b₀ : ℤ × ℤ} (hb₀ : b₀ ∈ R)
    (hseed_assumed : ∀ t₀ : ℕ, 0 < t₀ → ∀ r : ℕ,
      (∀ g ∈ (Finset.range (Hsup fr S a + 1)).image (fun j₀ : ℕ => b₀ + (j₀ : ℤ) • fr.dv),
        ∀ k : ℕ, ξ' (g + (r : ℤ) • ((q : ℤ) • u') + (k : ℤ) • u)
          = T (((t₀ * q : ℕ) : ℤ) • u') ξ' (g + (r : ℤ) • ((q : ℤ) • u') + (k : ℤ) • u)) →
      ∀ i j : ℕ, j < Wrow fr S a →
        ξ' (rowLine fr b₀ cQ q (Wsup fr S a) r i + (j : ℤ) • u) =
          T (((t₀ * q : ℕ) : ℤ) • u') ξ' (rowLine fr b₀ cQ q (Wsup fr S a) r i + (j : ℤ) • u)) :
    ∃ K : Set (ℤ × ℤ), K ⊆ R ∧ IsRegion K u u' ∧ K.Nonempty ∧
      ∃ t₀ : ℕ, 0 < t₀ ∧ PeriodOn ξ' K (((t₀ * q : ℕ) : ℤ) • u') := by
  have hF₀R : ∀ g ∈ (Finset.range (Hsup fr S a + 1)).image
      (fun j₀ : ℕ => b₀ + (j₀ : ℤ) • fr.dv), g ∈ R := by
    intro g hg
    obtain ⟨j₀, -, rfl⟩ := Finset.mem_image.mp hg
    exact fr.add_nsmul_dv_mem hR_region hb₀ j₀
  obtain ⟨t₀, ht₀, hrep⟩ := exists_band_repeat hfin hc hRper hR_region hF₀R q
  have hd : 0 < (q : ℤ) * dot fr.n u' := mul_pos (by exact_mod_cast hq) fr.dot_n_u'
  refine sweep_conclusion_of_cofinal_ladders hξ' hgen hR_region hc hRper fr.n cQ
    fr.dot_n_u fr.dot_n_u' (dot fr.n b₀ - 1) ((q : ℤ) * dot fr.n u') hd q ht₀ ?_
  intro N
  obtain ⟨r, hr, hband⟩ := hrep N
  refine ⟨r, hr, bandSet fr b₀ ((r : ℤ) • ((q : ℤ) • u')) (Hsup fr S a),
    rowLine fr b₀ cQ q (Wsup fr S a) r, Wrow fr S a, ?_, ?_, ?_, ?_⟩
  · exact agree_on_bandSet fr b₀ _ _ _ hband
  · exact hseed_assumed t₀ ht₀ r hband
  · exact hwin_of_levelLine fr hvert (le_Hsup fr a) (le_Wsup fr a) (le_Wrow fr a) b₀ _ _
  · intro z hz
    have h1 : cQ ≤ dot fr.n z := hz.1.2
    have h2 : dot fr.n z ≤ dot fr.n (b₀ + (r : ℤ) • ((q : ℤ) • u')) - 1 := by
      have h := hz.2
      simp only [Set.mem_ofPred_eq] at h
      rw [Nivat.LE2.dot_add, dot_zsmul', dot_zsmul']; linarith
    exact cover_of_levelLine fr (Int.self_le_toNat _) _ _ z h1 h2

/-- **The same, from `IsGeneratingSet` and `Primitive u` alone.**  The frame and the vertex are
chosen inside; what comes out is the vertex `a` and the one implication "seed at `a` → sweep
conclusion".  Generic in `(u, u', ξ', R)`; `Primitive u` is discharged by §29's WLOG at the
call site. -/
theorem sweep_conclusion_of_generatingSet_of_seed_assumed {ξ ξ' : Config ℤ}
    (hfin : (Set.range ξ').Finite) (hξ' : ξ' ∈ orbitClosure ξ)
    {S : Finset (ℤ × ℤ)} (hS : IsGeneratingSet ξ S)
    {R : Set (ℤ × ℤ)} {u u' : ℤ × ℤ} (hu : Primitive u) (hdet : det u u' ≠ 0)
    (hR_region : IsRegion R u u')
    {c : ℤ} (hc : c ≠ 0) (hRper : PeriodOn ξ' R (c • u))
    (cQ : ℤ) {q : ℕ} (hq : 0 < q) {b₀ : ℤ × ℤ} (hb₀ : b₀ ∈ R) :
    ∃ (fr : LevelFrame u u') (a : ℤ × ℤ), a ∈ S ∧ GeneratesAt ξ S a ∧
      ((∀ t₀ : ℕ, 0 < t₀ → ∀ r : ℕ,
        (∀ g ∈ (Finset.range (Hsup fr S a + 1)).image (fun j₀ : ℕ => b₀ + (j₀ : ℤ) • fr.dv),
          ∀ k : ℕ, ξ' (g + (r : ℤ) • ((q : ℤ) • u') + (k : ℤ) • u)
            = T (((t₀ * q : ℕ) : ℤ) • u') ξ' (g + (r : ℤ) • ((q : ℤ) • u') + (k : ℤ) • u)) →
        ∀ i j : ℕ, j < Wrow fr S a →
          ξ' (rowLine fr b₀ cQ q (Wsup fr S a) r i + (j : ℤ) • u) =
            T (((t₀ * q : ℕ) : ℤ) • u') ξ' (rowLine fr b₀ cQ q (Wsup fr S a) r i + (j : ℤ) • u))
        →
      ∃ K : Set (ℤ × ℤ), K ⊆ R ∧ IsRegion K u u' ∧ K.Nonempty ∧
        ∃ t₀ : ℕ, 0 < t₀ ∧ PeriodOn ξ' K (((t₀ * q : ℕ) : ℤ) • u')) := by
  obtain ⟨fr⟩ := exists_levelFrame hu hdet
  obtain ⟨a, ha, hgen, hvert⟩ := exists_generating_vertex fr hS
  exact ⟨fr, a, ha, hgen, fun hseed =>
    sweep_conclusion_of_levelFrame_of_seed_assumed hfin hξ' hR_region hc hRper fr hgen hvert
      cQ hq hb₀ hseed⟩

/-! ## §31  `case1_seed` restated: the seed from a `B`-block, both sweep directions

Answer to the lead's two questions on `case1_seed` (2026-09-19), landed as Lean rather than prose.

**The column is the band, not the seed.**  `case1_seed`'s antecedent (agreement on the column
`{b₀ + j₀ dv}` along every `u`-line) is Collé's band `H_𝒯 + r h'` of (4.3), produced by
`exists_band_repeat` (§23) and consumed by the window (`hwin_*_of_lineAt`).  The seed of each row
is *not* derived from it.  It comes from the trace of `H_Q` (`b3_colle2.txt:694`,
"`ℓ_1 ∩ (H_Q − ιh)` has at least `|S ∩ ℓ_S| − 1` elements"), and its *agreement* is already a
binder of `case1_sweep`: the `q`-antecedent `hladder`, iterated on the half-strip by
`Nivat.Colle43.agree_T_on_halfStripFrom` (`Claim43.lean:401`, §20 pickup).  Only the *width* is
open, and it is a statement about `B` — `HasBlock` below.

**Three defects of `case1_seed` as first stated**, all fixed by the shape `LineSeed`:
1. its `cQ` is universally quantified, but the trace exists only from a level on — `∃ cQ`;
2. its line bases are pinned to `m₀ + i·W` from the band's `b₀`, but `c u`-periodicity reaches
   only positions `≡ trace (mod c)` — `∃ m₀ : ℕ → ℤ` with the stagger `m₀ i + W ≤ m₀ (i+1)`;
3. it covered only the downward sweep; when the `u`-edge of `S` on the `−u'` side is the longer
   one Collé sweeps upward instead (`:702-706`) — `sweep_conclusion_up_of_lineSeed`.

**`HasBlock u u' B m`** (frame-free, the string routed to L1): a base point at each of
`|det u u'|` consecutive levels of `(−u.2, u.1)`, each carrying `m` consecutive `u`-points of
`B`.  A `u'`-ray meets only the levels of one residue class mod `|det u u'|`, so one row of `B`
seeds one level in `|det u u'|`; Collé's parallelogram `Q ∖ ℓ'_Q` (`:628-650`) has all classes.
`frameBlock_of_hasBlock` transfers it to the frame's normal (`fr.n = ±(−u.2, u.1)` for `u`
primitive), `seed_of_block` turns it into `LineSeed`, and
`sweep_conclusion_of_generatingSet_of_block` closes both directions under
`min (Wrow aLo) (Wrow aHi) ≤ m` — the **min** of the two `u`-edge rows (minus one), which is
exactly the width `L1Assemble.maxB_wide` provides (hand-read of its statement).

**What is left for L3**: one statement about `B`, `∃ m, HasBlock u u' B m ∧ min … ≤ m`,
with everything else in `case1_sweep`'s binder list (`hBQ` from `hline` at `i = 0` and
`pos_pw_of_case1_hyps`, `RegionSteps.lean`).  ⚠ This is a split, not a discharge: `sorry TOTAL`
does not change until that statement is produced. -/

/-! ## §31  The seed, produced from a `B`-block; both sweep directions -/

theorem dot_zsmul_left (k : ℤ) (n v : ℤ × ℤ) : dot (k • n) v = k * dot n v := by
  simp only [dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

/-- Line `i` of an enumeration: level `L i`, `d'`-coordinate `m₀ i`. -/
def lineAt {u u' : ℤ × ℤ} (fr : LevelFrame u u') (L m₀ : ℕ → ℤ) (i : ℕ) : ℤ × ℤ :=
  L i • fr.dv + m₀ i • u

theorem dot_n_lineAt {u u' : ℤ × ℤ} (fr : LevelFrame u u') (L m₀ : ℕ → ℤ) (i : ℕ) :
    dot fr.n (lineAt fr L m₀ i) = L i := by
  simp only [lineAt, Nivat.LE2.dot_add, dot_zsmul', fr.dot_n_dv, fr.dot_n_u]; ring

theorem dot_d'_lineAt {u u' : ℤ × ℤ} (fr : LevelFrame u u') (L m₀ : ℕ → ℤ) (i : ℕ) :
    dot fr.d' (lineAt fr L m₀ i) = m₀ i := by
  simp only [lineAt, Nivat.LE2.dot_add, dot_zsmul', fr.dot_d'_dv, fr.dot_d'_u]; ring

/-- **The per-line seed.**  For every gap `t₀`, every level enumeration `L` staying above
`cQ`, and every floor `lo`, there is a choice of line bases `m₀` — clearing `lo` on line 0 and
staggered by `W` — such that the first `s` points of every line agree with the `t₀ q u'`-shift. -/
def LineSeed {u u' : ℤ × ℤ} (fr : LevelFrame u u') (ξ' : Config ℤ) (q W s : ℕ) (cQ : ℤ) :
    Prop :=
  ∀ t₀ : ℕ, 0 < t₀ → ∀ L : ℕ → ℤ, (∀ i, cQ ≤ L i) → ∀ lo : ℤ,
    ∃ m₀ : ℕ → ℤ, lo ≤ m₀ 0 ∧ (∀ i, m₀ i + W ≤ m₀ (i + 1)) ∧
      ∀ i j : ℕ, j < s →
        ξ' (lineAt fr L m₀ i + (j : ℤ) • u) =
          T (((t₀ * q : ℕ) : ℤ) • u') ξ' (lineAt fr L m₀ i + (j : ℤ) • u)

/-- **The `B`-block**: a base point at each of `|det u u'|` consecutive levels of the normal
`(-u.2, u.1)`, each carrying `m` consecutive `u`-points of `B`. -/
def HasBlock (u u' : ℤ × ℤ) (B : Finset (ℤ × ℤ)) (m : ℕ) : Prop :=
  ∃ g₀ : ℤ × ℤ, ∀ ρ : ℕ, ρ < (det u u').natAbs → ∃ g : ℤ × ℤ,
    dot (-u.2, u.1) g = dot (-u.2, u.1) g₀ + ρ ∧ ∀ k : ℕ, k < m → g + (k : ℤ) • u ∈ B

/-- **Adapter for L1's export shape.**  L1 exports the block with a direction `w = u ∨ w = -u`;
`HasBlock` fixes `w = u`.  The `-u` branch is a re-basing along the same level
(`dot (-u.2, u.1) u = 0`): the run `g, g - u, …, g - (m-1)•u` read from its far end is the run
`g - (m-1)•u, …, g`. -/
theorem hasBlock_of_either {u u' : ℤ × ℤ} {B : Finset (ℤ × ℤ)} {m : ℕ}
    (h : ∃ (g₀ w : ℤ × ℤ), (w = u ∨ w = -u) ∧
      ∀ ρ : ℕ, ρ < (det u u').natAbs → ∃ g : ℤ × ℤ,
        dot (-u.2, u.1) g = dot (-u.2, u.1) g₀ + ρ ∧ ∀ j : ℕ, j < m → g + (j : ℤ) • w ∈ B) :
    HasBlock u u' B m := by
  obtain ⟨g₀, w, hw, hblk⟩ := h
  rcases hw with rfl | rfl
  · exact ⟨g₀, hblk⟩
  · refine ⟨g₀, fun ρ hρ => ?_⟩
    obtain ⟨g, hg, hrun⟩ := hblk ρ hρ
    refine ⟨g + (1 - (m : ℤ)) • u, ?_, fun k hk => ?_⟩
    · rw [Nivat.LE2.dot_add, dot_zsmul']
      have : dot (-u.2, u.1) u = 0 := by simp only [Nivat.LE2.dot]; ring
      rw [this, hg]; ring
    · have := hrun (m - 1 - k) (by omega)
      have hcast : ((m - 1 - k : ℕ) : ℤ) = (m : ℤ) - 1 - k := by omega
      rw [hcast] at this
      convert this using 1
      rw [add_assoc, ← add_smul, smul_neg, ← neg_smul]
      congr 2; ring

/-! ### Staggered bases -/

/-- Shift each line's natural base forward by a multiple of `np` so that line 0 clears `lo` and
each later line clears the previous one by `W`. -/
def stagBase (β : ℕ → ℤ) (np : ℕ) (lo : ℤ) (W : ℕ) : ℕ → ℤ
  | 0 => β 0 + (np : ℤ) * ((lo - β 0).toNat : ℤ)
  | i + 1 => β (i + 1) + (np : ℤ) * ((stagBase β np lo W i + W - β (i + 1)).toNat : ℤ)

theorem exists_nat_stagBase (β : ℕ → ℤ) (np : ℕ) (lo : ℤ) (W : ℕ) (i : ℕ) :
    ∃ k : ℕ, stagBase β np lo W i = β i + (np : ℤ) * k := by
  cases i with
  | zero => exact ⟨_, rfl⟩
  | succ i => exact ⟨_, rfl⟩

theorem le_stagBase_zero {β : ℕ → ℤ} {np : ℕ} (hnp : 0 < np) (lo : ℤ) (W : ℕ) :
    lo ≤ stagBase β np lo W 0 := by
  show lo ≤ β 0 + (np : ℤ) * ((lo - β 0).toNat : ℤ)
  have hk : lo - β 0 ≤ ((lo - β 0).toNat : ℤ) := Int.self_le_toNat _
  have hk0 : (0 : ℤ) ≤ ((lo - β 0).toNat : ℤ) := Int.natCast_nonneg _
  have h1 : (1 : ℤ) ≤ np := by exact_mod_cast hnp
  nlinarith

theorem stagBase_stagger {β : ℕ → ℤ} {np : ℕ} (hnp : 0 < np) (lo : ℤ) (W : ℕ) (i : ℕ) :
    stagBase β np lo W i + W ≤ stagBase β np lo W (i + 1) := by
  show _ ≤ β (i + 1) + (np : ℤ) * ((stagBase β np lo W i + W - β (i + 1)).toNat : ℤ)
  have hk := Int.self_le_toNat (stagBase β np lo W i + W - β (i + 1))
  have hk0 : (0 : ℤ) ≤ ((stagBase β np lo W i + W - β (i + 1)).toNat : ℤ) :=
    Int.natCast_nonneg _
  have h1 : (1 : ℤ) ≤ np := by exact_mod_cast hnp
  nlinarith

theorem mono_of_stagger {m₀ : ℕ → ℤ} {W : ℕ} (hstag : ∀ i, m₀ i + W ≤ m₀ (i + 1)) :
    ∀ i i' : ℕ, i' ≤ i → m₀ i' ≤ m₀ i := by
  intro i i' h
  induction i with
  | zero => obtain rfl := Nat.le_zero.mp h; exact le_rfl
  | succ i ih =>
    rcases Nat.of_le_succ h with h | rfl
    · have := hstag i
      have := Int.natCast_nonneg W
      linarith [ih h]
    · exact le_rfl

/-! ### The seed from the block -/

/-- **`seed_of_block`.**  Agreement comes from `hladder` (the `q`-antecedent of `case1_sweep`)
iterated on the half-strip (`agree_T_on_halfStripFrom`); the run at each level comes from the
block; the position is adjusted by `c u`-periodicity inside `R`.  The cut `cQ` is the lowest
level at which every residue class has a trace point with parameter `t ≥ t₁`. -/
theorem seed_of_block {ξ' : Config ℤ} {u u' : ℤ × ℤ} (fr : LevelFrame u u')
    {R : Set (ℤ × ℤ)} (hR_region : IsRegion R u u')
    {c : ℤ} (hc : c ≠ 0) (hRper : PeriodOn ξ' R (c • u))
    {B Q : Finset (ℤ × ℤ)} {τ t₁ : ℤ} (hτ : τ ≤ t₁) (hBQ : ∀ g ∈ B, g ∈ Q)
    (hQR : ∀ t : ℤ, τ ≤ t → ∀ z ∈ Q, t • u' + z ∈ R ∧ t • u' + z + c • u ∈ R)
    {q : ℕ}
    (hladder : ∀ g ∈ B, ∀ t : ℤ, t₁ ≤ t → ξ' (g + (t + (q : ℤ)) • u') = ξ' (g + t • u'))
    {g₀ : ℤ × ℤ} {m : ℕ}
    (hblock : ∀ ρ : ℕ, (ρ : ℤ) < dot fr.n u' → ∃ g : ℤ × ℤ,
      dot fr.n g = dot fr.n g₀ + ρ ∧ ∀ k : ℕ, k < m → g + (k : ℤ) • u ∈ B)
    (W : ℕ) {s : ℕ} (hs : s ≤ m) :
    ∃ cQ : ℤ, LineSeed fr ξ' q W s cQ := by
  classical
  obtain ⟨np, hnp, hnper⟩ := exists_neg_nsmul_period hc hRper
  have hper : PeriodOn ξ' R ((np : ℤ) • u) := by simpa using hnper.neg
  have hU : ∀ z ∈ R, z + u ∈ R := by
    obtain ⟨hconv, ⟨z₁, hray⟩, -⟩ := hR_region
    intro z hz
    have := ray_all_of_rayIn hconv hray 1 z hz 1
    simpa using this
  have hδpos : 0 < dot fr.n u' := fr.dot_n_u'
  choose gsel hgsel using hblock
  have hg1 : ∀ ρ h, dot fr.n (gsel ρ h) = dot fr.n g₀ + ρ := fun ρ h => (hgsel ρ h).1
  have hg2 : ∀ ρ h, ∀ k : ℕ, k < m → gsel ρ h + (k : ℤ) • u ∈ B := fun ρ h => (hgsel ρ h).2
  have hρlt : ∀ lam : ℤ,
      ((((lam - dot fr.n g₀) % dot fr.n u').toNat : ℕ) : ℤ) < dot fr.n u' := by
    intro lam
    rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hδpos.ne')]
    exact Int.emod_lt_of_pos _ hδpos
  set trace : ℤ → ℤ × ℤ := fun lam =>
    gsel _ (hρlt lam) + ((lam - dot fr.n g₀) / dot fr.n u') • u' with htrace
  refine ⟨dot fr.n g₀ + t₁ * dot fr.n u', ?_⟩
  intro t₀ ht₀ L hL lo
  have htr_n : ∀ lam, dot fr.n (trace lam) = lam := by
    intro lam
    simp only [htrace, Nivat.LE2.dot_add, dot_zsmul', hg1,
      Int.toNat_of_nonneg (Int.emod_nonneg (lam - dot fr.n g₀) hδpos.ne')]
    have h1 := Int.emod_add_ediv_mul (lam - dot fr.n g₀) (dot fr.n u')
    linear_combination h1
  have htr_t : ∀ lam, dot fr.n g₀ + t₁ * dot fr.n u' ≤ lam →
      t₁ ≤ (lam - dot fr.n g₀) / dot fr.n u' := by
    intro lam hlam
    rw [Int.le_ediv_iff_mul_le hδpos]; linarith
  have htr_R : ∀ lam, dot fr.n g₀ + t₁ * dot fr.n u' ≤ lam → ∀ j : ℕ, j < m →
      trace lam + (j : ℤ) • u ∈ R := by
    intro lam hlam j hj
    have := (hQR _ (le_trans hτ (htr_t lam hlam)) _ (hBQ _ (hg2 _ (hρlt lam) j hj))).1
    have e : ((lam - dot fr.n g₀) / dot fr.n u') • u' + (gsel _ (hρlt lam) + (j : ℤ) • u)
        = trace lam + (j : ℤ) • u := by simp only [htrace]; abel
    rwa [e] at this
  have htr_agree : ∀ lam, dot fr.n g₀ + t₁ * dot fr.n u' ≤ lam → ∀ j : ℕ, j < m →
      ξ' (trace lam + (j : ℤ) • u) =
        T (((t₀ * q : ℕ) : ℤ) • u') ξ' (trace lam + (j : ℤ) • u) := by
    intro lam hlam j hj
    refine agree_T_on_halfStripFrom hladder t₀ _
      ⟨_, hg2 _ (hρlt lam) j hj, _, htr_t lam hlam, ?_⟩
    simp only [htrace]; abel
  set β : ℕ → ℤ := fun i => dot fr.d' (trace (L i)) with hβ
  refine ⟨stagBase β np lo W, le_stagBase_zero hnp lo W, stagBase_stagger hnp lo W, ?_⟩
  intro i j hj
  obtain ⟨k, hk⟩ := exists_nat_stagBase β np lo W i
  have hlam := hL i
  have hjm : j < m := lt_of_lt_of_le hj hs
  have e : lineAt fr L (stagBase β np lo W) i + (j : ℤ) • u
      = trace (L i) + (j : ℤ) • u + (k : ℤ) • ((np : ℤ) • u) := by
    apply fr.ext_dots
    · simp only [Nivat.LE2.dot_add, dot_zsmul', fr.dot_n_u, dot_n_lineAt, htr_n]; ring
    · simp only [Nivat.LE2.dot_add, dot_zsmul', fr.dot_d'_u, dot_d'_lineAt]
      rw [hk]; simp only [hβ]; ring
  rw [e, eq_add_nsmul_period_of_closed hU hper (htr_R _ hlam j hjm) k,
    eq_add_nsmul_period_of_closed hU (T_periodOn_of_periodOn_of_ray hR_region hper (t₀ * q))
      (htr_R _ hlam j hjm) k]
  exact htr_agree _ hlam j hjm

/-- The frame-free block transfers to the frame's normal: `fr.n = ±(-u.2, u.1)` when `u` is
primitive, and a run of `|det u u'|` consecutive levels is a run in either orientation. -/
theorem frameBlock_of_hasBlock {u u' : ℤ × ℤ} (hu : Primitive u) (fr : LevelFrame u u')
    {B : Finset (ℤ × ℤ)} {m : ℕ} (hB : HasBlock u u' B m) :
    ∃ g₀ : ℤ × ℤ, ∀ ρ : ℕ, (ρ : ℤ) < dot fr.n u' → ∃ g : ℤ × ℤ,
      dot fr.n g = dot fr.n g₀ + ρ ∧ ∀ k : ℕ, k < m → g + (k : ℤ) • u ∈ B := by
  obtain ⟨g₀, hg₀⟩ := hB
  set p : ℤ × ℤ := (-u.2, u.1) with hp
  have hpprim : Primitive p := by
    show IsCoprime (-u.2) u.1
    exact hu.symm.neg_left
  have h0 : det p fr.n = 0 := by
    have := fr.dot_n_u
    simp only [det, hp, dot] at this ⊢; linarith
  obtain ⟨c, hc⟩ := eq_zsmul_of_det_eq_zero hpprim h0
  have hdv : c * dot p fr.dv = 1 := by rw [← dot_zsmul_left, ← hc]; exact fr.dot_n_dv
  have hpu' : dot p u' = det u u' := by simp only [hp, dot, det]; ring
  have hnu' : dot fr.n u' = c * det u u' := by rw [hc, dot_zsmul_left, hpu']
  have hng : ∀ g, dot fr.n g = c * dot p g := fun g => by rw [hc, dot_zsmul_left]
  have hδ : 0 < dot fr.n u' := fr.dot_n_u'
  rw [hnu'] at hδ
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' hdv with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · have habs : ((det u u').natAbs : ℤ) = dot fr.n u' := by rw [hnu']; omega
    refine ⟨g₀, fun ρ hρ => ?_⟩
    obtain ⟨g, hg, hrun⟩ := hg₀ ρ (by omega)
    exact ⟨g, by rw [hng, hng, one_mul, one_mul, hg], hrun⟩
  · have habs : ((det u u').natAbs : ℤ) = dot fr.n u' := by rw [hnu']; omega
    set δ : ℕ := (det u u').natAbs with hδn
    have hδ1 : 1 ≤ δ := by omega
    obtain ⟨gt, hgt, -⟩ := hg₀ (δ - 1) (by omega)
    refine ⟨gt, fun ρ hρ => ?_⟩
    obtain ⟨g, hg, hrun⟩ := hg₀ (δ - 1 - ρ) (by omega)
    refine ⟨g, ?_, hrun⟩
    rw [hng, hng, hgt, hg]
    have e1 : ((δ - 1 - ρ : ℕ) : ℤ) = (δ : ℤ) - 1 - ρ := by omega
    have e2 : ((δ - 1 : ℕ) : ℤ) = (δ : ℤ) - 1 := by omega
    rw [e1, e2]; ring

/-! ### Enumeration, cover and window, both directions -/

theorem cover_of_lineAt_down {u u' : ℤ × ℤ} (fr : LevelFrame u u') {top cQ : ℤ} {M : ℕ}
    (hM : top - cQ ≤ M) (m₀ : ℕ → ℤ) :
    ∀ z : ℤ × ℤ, cQ ≤ dot fr.n z → dot fr.n z ≤ top →
      ∃ i : ℕ, ∃ m : ℤ, z = lineAt fr (fun i => top - ((min i M : ℕ) : ℤ)) m₀ i + m • u := by
  intro z h1 h2
  set ι : ℕ := (top - dot fr.n z).toNat with hι
  have hιM : ι ≤ M := by omega
  have hmin : min ι M = ι := min_eq_left hιM
  refine ⟨ι, dot fr.d' z - m₀ ι, fr.ext_dots ?_ ?_⟩
  · simp only [Nivat.LE2.dot_add, dot_zsmul', fr.dot_n_u, dot_n_lineAt, hmin]; omega
  · simp only [Nivat.LE2.dot_add, dot_zsmul', fr.dot_d'_u, dot_d'_lineAt]; ring

theorem cover_of_lineAt_up {u u' : ℤ × ℤ} (fr : LevelFrame u u') (bot : ℤ) (m₀ : ℕ → ℤ) :
    ∀ z : ℤ × ℤ, bot ≤ dot fr.n z →
      ∃ i : ℕ, ∃ m : ℤ, z = lineAt fr (fun i => bot + (i : ℤ)) m₀ i + m • u := by
  intro z h
  refine ⟨(dot fr.n z - bot).toNat, dot fr.d' z - m₀ (dot fr.n z - bot).toNat, fr.ext_dots ?_ ?_⟩
  · simp only [Nivat.LE2.dot_add, dot_zsmul', fr.dot_n_u, dot_n_lineAt]; omega
  · simp only [Nivat.LE2.dot_add, dot_zsmul', fr.dot_d'_u, dot_d'_lineAt]; ring

/-- **Window condition, downward sweep** (vertex `a` on the lowest level of `S`, lines below the
band).  Generic in the level enumeration `L`: it need only stay below the band (`hLtop`) and
contain every intermediate level at an earlier index (`hLprev`). -/
theorem hwin_down_of_lineAt {u u' : ℤ × ℤ} (fr : LevelFrame u u') {S : Finset (ℤ × ℤ)}
    {a : ℤ × ℤ}
    (hvert : ∀ b ∈ S.erase a,
      dot fr.n a < dot fr.n b ∨ (dot fr.n a = dot fr.n b ∧ dot fr.d' b < dot fr.d' a))
    {H W Wrow : ℕ}
    (hH : ∀ z ∈ S, dot fr.n z - dot fr.n a ≤ H)
    (hW : ∀ z ∈ S, dot fr.d' a - dot fr.d' z ≤ W)
    (hWrow : ∀ z ∈ S, dot fr.n z = dot fr.n a → dot fr.d' a - dot fr.d' z ≤ Wrow)
    (b₀ v : ℤ × ℤ) {L m₀ : ℕ → ℤ}
    (hLtop : ∀ i, L i ≤ dot fr.n (b₀ + v) - 1)
    (hLprev : ∀ i k : ℕ, 1 ≤ k → L i + k ≤ dot fr.n (b₀ + v) - 1 →
      ∃ i' : ℕ, i' < i ∧ L i' = L i + k)
    (hm₀0 : dot fr.d' (b₀ + v) + W ≤ m₀ 0) (hstag : ∀ i, m₀ i + W ≤ m₀ (i + 1)) :
    ∀ i j : ℕ, Wrow ≤ j → ∀ z ∈ S.erase a,
      z + (lineAt fr L m₀ i + (j : ℤ) • u - a) ∈
        bandSet fr b₀ v H ∪
          {p | ∃ i' : ℕ, i' < i ∧ ∃ j' : ℕ, p = lineAt fr L m₀ i' + (j' : ℤ) • u} ∨
        ∃ j' : ℕ, j' < j ∧
          z + (lineAt fr L m₀ i + (j : ℤ) • u - a) = lineAt fr L m₀ i + (j' : ℤ) • u := by
  intro i j hj z hz
  have hmono := mono_of_stagger hstag
  set p : ℤ × ℤ := lineAt fr L m₀ i with hp
  have hpn : dot fr.n p = L i := dot_n_lineAt fr L m₀ i
  have hpd : dot fr.d' p = m₀ i := dot_d'_lineAt fr L m₀ i
  set w : ℤ × ℤ := z + (p + (j : ℤ) • u - a) with hw
  have hwn : dot fr.n w = dot fr.n z + L i - dot fr.n a := by
    simp only [hw, Nivat.LE2.dot_add, Nivat.LE2.dot_sub, dot_zsmul', fr.dot_n_u, hpn]; ring
  have hwd : dot fr.d' w = dot fr.d' z + m₀ i + j - dot fr.d' a := by
    simp only [hw, Nivat.LE2.dot_add, Nivat.LE2.dot_sub, dot_zsmul', fr.dot_d'_u, hpd]; ring
  have hzS : z ∈ S := (Finset.mem_erase.mp hz).2
  have hWz := hW z hzS
  have hW0 : (0 : ℤ) ≤ W := Int.natCast_nonneg _
  rcases hvert z hz with hlt | ⟨heq, hdlt⟩
  · have hk := hH z hzS
    set kk : ℕ := (dot fr.n z - dot fr.n a).toNat with hkk
    have hkkval : (kk : ℤ) = dot fr.n z - dot fr.n a := by omega
    have hkk1 : 1 ≤ kk := by omega
    by_cases hcase : L i + kk ≤ dot fr.n (b₀ + v) - 1
    · obtain ⟨i', hi', hLi'⟩ := hLprev i kk hkk1 hcase
      have hle : m₀ i' + W ≤ m₀ i := le_trans (hstag i') (hmono _ _ hi')
      have hnn : 0 ≤ dot fr.d' w - m₀ i' := by rw [hwd]; linarith
      refine Or.inl (Or.inr ⟨i', hi', (dot fr.d' w - m₀ i').toNat, fr.ext_dots ?_ ?_⟩)
      · rw [hwn, Nivat.LE2.dot_add, dot_zsmul', fr.dot_n_u, dot_n_lineAt, hLi']; omega
      · rw [Int.toNat_of_nonneg hnn, hwd, Nivat.LE2.dot_add, dot_zsmul', fr.dot_d'_u,
          dot_d'_lineAt]; ring
    · push Not at hcase
      have hLi := hLtop i
      have hm0i : m₀ 0 ≤ m₀ i := hmono i 0 (Nat.zero_le _)
      have hj0 : 0 ≤ dot fr.n w - dot fr.n (b₀ + v) := by rw [hwn]; omega
      have hk0 : 0 ≤ dot fr.d' w - dot fr.d' (b₀ + v) := by rw [hwd]; linarith
      refine Or.inl (Or.inl ⟨(dot fr.n w - dot fr.n (b₀ + v)).toNat, by omega,
        (dot fr.d' w - dot fr.d' (b₀ + v)).toNat, fr.ext_dots ?_ ?_⟩)
      · rw [Int.toNat_of_nonneg hj0]
        simp only [Nivat.LE2.dot_add, dot_zsmul', fr.dot_n_u, fr.dot_n_dv]; ring
      · rw [Int.toNat_of_nonneg hk0]
        simp only [Nivat.LE2.dot_add, dot_zsmul', fr.dot_d'_u, fr.dot_d'_dv]; ring
  · have hrow := hWrow z hzS heq.symm
    set t : ℕ := (dot fr.d' a - dot fr.d' z).toNat with ht
    have htval : (t : ℤ) = dot fr.d' a - dot fr.d' z := by omega
    have ht1 : 1 ≤ t := by omega
    have htj : t ≤ j := by omega
    refine Or.inr ⟨j - t, by omega, fr.ext_dots ?_ ?_⟩
    · rw [hwn, Nivat.LE2.dot_add, dot_zsmul', fr.dot_n_u, hpn]; omega
    · rw [hwd, Nivat.LE2.dot_add, dot_zsmul', fr.dot_d'_u, hpd, Nat.cast_sub htj]; linarith

/-- **Window condition, upward sweep** (vertex `a` on the highest level of `S`, lines above the
band, `b3_colle2.txt:702-706`).  Mirror of `hwin_down_of_lineAt`. -/
theorem hwin_up_of_lineAt {u u' : ℤ × ℤ} (fr : LevelFrame u u') {S : Finset (ℤ × ℤ)}
    {a : ℤ × ℤ}
    (hvert : ∀ b ∈ S.erase a,
      dot fr.n b < dot fr.n a ∨ (dot fr.n b = dot fr.n a ∧ dot fr.d' b < dot fr.d' a))
    {H W Wrow : ℕ}
    (hH : ∀ z ∈ S, dot fr.n a - dot fr.n z ≤ H)
    (hW : ∀ z ∈ S, dot fr.d' a - dot fr.d' z ≤ W)
    (hWrow : ∀ z ∈ S, dot fr.n z = dot fr.n a → dot fr.d' a - dot fr.d' z ≤ Wrow)
    (b₀ v : ℤ × ℤ) {L m₀ : ℕ → ℤ}
    (hLbot : ∀ i, dot fr.n (b₀ + v) + H + 1 ≤ L i)
    (hLprev : ∀ i k : ℕ, 1 ≤ k → dot fr.n (b₀ + v) + H + 1 ≤ L i - k →
      ∃ i' : ℕ, i' < i ∧ L i' = L i - k)
    (hm₀0 : dot fr.d' (b₀ + v) + W ≤ m₀ 0) (hstag : ∀ i, m₀ i + W ≤ m₀ (i + 1)) :
    ∀ i j : ℕ, Wrow ≤ j → ∀ z ∈ S.erase a,
      z + (lineAt fr L m₀ i + (j : ℤ) • u - a) ∈
        bandSet fr b₀ v H ∪
          {p | ∃ i' : ℕ, i' < i ∧ ∃ j' : ℕ, p = lineAt fr L m₀ i' + (j' : ℤ) • u} ∨
        ∃ j' : ℕ, j' < j ∧
          z + (lineAt fr L m₀ i + (j : ℤ) • u - a) = lineAt fr L m₀ i + (j' : ℤ) • u := by
  intro i j hj z hz
  have hmono := mono_of_stagger hstag
  set p : ℤ × ℤ := lineAt fr L m₀ i with hp
  have hpn : dot fr.n p = L i := dot_n_lineAt fr L m₀ i
  have hpd : dot fr.d' p = m₀ i := dot_d'_lineAt fr L m₀ i
  set w : ℤ × ℤ := z + (p + (j : ℤ) • u - a) with hw
  have hwn : dot fr.n w = dot fr.n z + L i - dot fr.n a := by
    simp only [hw, Nivat.LE2.dot_add, Nivat.LE2.dot_sub, dot_zsmul', fr.dot_n_u, hpn]; ring
  have hwd : dot fr.d' w = dot fr.d' z + m₀ i + j - dot fr.d' a := by
    simp only [hw, Nivat.LE2.dot_add, Nivat.LE2.dot_sub, dot_zsmul', fr.dot_d'_u, hpd]; ring
  have hzS : z ∈ S := (Finset.mem_erase.mp hz).2
  have hWz := hW z hzS
  have hW0 : (0 : ℤ) ≤ W := Int.natCast_nonneg _
  rcases hvert z hz with hlt | ⟨heq, hdlt⟩
  · have hk := hH z hzS
    set kk : ℕ := (dot fr.n a - dot fr.n z).toNat with hkk
    have hkkval : (kk : ℤ) = dot fr.n a - dot fr.n z := by omega
    have hkk1 : 1 ≤ kk := by omega
    by_cases hcase : dot fr.n (b₀ + v) + H + 1 ≤ L i - kk
    · obtain ⟨i', hi', hLi'⟩ := hLprev i kk hkk1 hcase
      have hle : m₀ i' + W ≤ m₀ i := le_trans (hstag i') (hmono _ _ hi')
      have hnn : 0 ≤ dot fr.d' w - m₀ i' := by rw [hwd]; linarith
      refine Or.inl (Or.inr ⟨i', hi', (dot fr.d' w - m₀ i').toNat, fr.ext_dots ?_ ?_⟩)
      · rw [hwn, Nivat.LE2.dot_add, dot_zsmul', fr.dot_n_u, dot_n_lineAt, hLi']; omega
      · rw [Int.toNat_of_nonneg hnn, hwd, Nivat.LE2.dot_add, dot_zsmul', fr.dot_d'_u,
          dot_d'_lineAt]; ring
    · push Not at hcase
      have hLi := hLbot i
      have hm0i : m₀ 0 ≤ m₀ i := hmono i 0 (Nat.zero_le _)
      have hj0 : 0 ≤ dot fr.n w - dot fr.n (b₀ + v) := by rw [hwn]; omega
      have hk0 : 0 ≤ dot fr.d' w - dot fr.d' (b₀ + v) := by rw [hwd]; linarith
      refine Or.inl (Or.inl ⟨(dot fr.n w - dot fr.n (b₀ + v)).toNat, by omega,
        (dot fr.d' w - dot fr.d' (b₀ + v)).toNat, fr.ext_dots ?_ ?_⟩)
      · rw [Int.toNat_of_nonneg hj0]
        simp only [Nivat.LE2.dot_add, dot_zsmul', fr.dot_n_u, fr.dot_n_dv]; ring
      · rw [Int.toNat_of_nonneg hk0]
        simp only [Nivat.LE2.dot_add, dot_zsmul', fr.dot_d'_u, fr.dot_d'_dv]; ring
  · have hrow := hWrow z hzS heq
    set t : ℕ := (dot fr.d' a - dot fr.d' z).toNat with ht
    have htval : (t : ℤ) = dot fr.d' a - dot fr.d' z := by omega
    have ht1 : 1 ≤ t := by omega
    have htj : t ≤ j := by omega
    refine Or.inr ⟨j - t, by omega, fr.ext_dots ?_ ?_⟩
    · rw [hwn, Nivat.LE2.dot_add, dot_zsmul', fr.dot_n_u, hpn]; omega
    · rw [hwd, Nivat.LE2.dot_add, dot_zsmul', fr.dot_d'_u, hpd, Nat.cast_sub htj]; linarith

/-! ### The upward vertex -/

theorem exists_vertex_up {u u' : ℤ × ℤ} (fr : LevelFrame u u') {S : Finset (ℤ × ℤ)}
    (hS : S.Nonempty) :
    ∃ a ∈ S, ∀ b ∈ S.erase a,
      dot fr.n b < dot fr.n a ∨ (dot fr.n b = dot fr.n a ∧ dot fr.d' b < dot fr.d' a) := by
  obtain ⟨a, ha, hmax⟩ :=
    Finset.exists_max_image S (fun z => toLex (dot fr.n z, dot fr.d' z)) hS
  refine ⟨a, ha, fun b hb => ?_⟩
  obtain ⟨hne, hbS⟩ := Finset.mem_erase.mp hb
  have h := hmax b hbS
  rw [Prod.Lex.toLex_le_toLex] at h
  dsimp only at h
  rcases h with h | ⟨h1, h2⟩
  · left; exact h
  · right
    exact ⟨h1, lt_of_le_of_ne h2 (fun heq => hne (fr.ext_dots h1 heq))⟩

theorem latticeConvex_erase_of_vertex_up {u u' : ℤ × ℤ} (fr : LevelFrame u u')
    {S : Finset (ℤ × ℤ)} (hS : LatticeConvex S) {a : ℤ × ℤ}
    (hvert : ∀ b ∈ S.erase a,
      dot fr.n b < dot fr.n a ∨ (dot fr.n b = dot fr.n a ∧ dot fr.d' b < dot fr.d' a)) :
    LatticeConvex (S.erase a) :=
  Nivat.Colle37Geom.latticeConvex_erase_of_lexExtreme hS (n := fr.n) (d := fr.d') hvert

theorem exists_generating_vertex_up {ξ : Config ℤ} {u u' : ℤ × ℤ} (fr : LevelFrame u u')
    {S : Finset (ℤ × ℤ)} (hS : IsGeneratingSet ξ S) :
    ∃ a ∈ S, GeneratesAt ξ S a ∧ ∀ b ∈ S.erase a,
      dot fr.n b < dot fr.n a ∨ (dot fr.n b = dot fr.n a ∧ dot fr.d' b < dot fr.d' a) := by
  obtain ⟨a, ha, hvert⟩ := exists_vertex_up fr hS.1
  exact ⟨a, ha, hS.2.2 a ha (latticeConvex_erase_of_vertex_up fr hS.2.1 hvert), hvert⟩

def HsupUp {u u' : ℤ × ℤ} (fr : LevelFrame u u') (S : Finset (ℤ × ℤ)) (a : ℤ × ℤ) : ℕ :=
  S.sup (fun z => (dot fr.n a - dot fr.n z).toNat)

theorem le_HsupUp {u u' : ℤ × ℤ} (fr : LevelFrame u u') {S : Finset (ℤ × ℤ)} (a : ℤ × ℤ) :
    ∀ z ∈ S, dot fr.n a - dot fr.n z ≤ HsupUp fr S a := fun z hz =>
  le_trans (Int.self_le_toNat _)
    (by exact_mod_cast Finset.le_sup (f := fun z => (dot fr.n a - dot fr.n z).toNat) hz)

theorem halfCut_add_u_mem {R : Set (ℤ × ℤ)} {u u' : ℤ × ℤ} (hR : IsRegion R u u')
    {n : ℤ × ℤ} (hnu : dot n u = 0) (c : ℤ) :
    ∀ z ∈ R ∩ halfPlaneGE n c, z + u ∈ R ∩ halfPlaneGE n c := by
  rintro z ⟨hzR, hzH⟩
  obtain ⟨hconv, ⟨z₀, hray⟩, -⟩ := hR
  have hdot : dot n (z + u) = dot n z := by rw [Nivat.LE2.dot_add, hnu, add_zero]
  refine ⟨?_, ?_⟩
  · have := ray_all_of_rayIn hconv hray 1 z hzR 1
    simpa using this
  · show c ≤ dot n (z + u); rw [hdot]; exact hzH

/-! ### Assembly, downward -/

theorem sweep_conclusion_down_of_lineSeed {ξ ξ' : Config ℤ}
    (hfin : (Set.range ξ').Finite) (hξ' : ξ' ∈ orbitClosure ξ)
    {S : Finset (ℤ × ℤ)} {R : Set (ℤ × ℤ)} {u u' : ℤ × ℤ} (hR_region : IsRegion R u u')
    {c : ℤ} (hc : c ≠ 0) (hRper : PeriodOn ξ' R (c • u))
    (fr : LevelFrame u u') {a : ℤ × ℤ} (hgen : GeneratesAt ξ S a)
    (hvert : ∀ b ∈ S.erase a,
      dot fr.n a < dot fr.n b ∨ (dot fr.n a = dot fr.n b ∧ dot fr.d' b < dot fr.d' a))
    {q : ℕ} (hq : 0 < q) {b₀ : ℤ × ℤ} (hb₀ : b₀ ∈ R)
    {cQ : ℤ} (hseed : LineSeed fr ξ' q (Wsup fr S a) (Wrow fr S a) cQ) :
    ∃ K : Set (ℤ × ℤ), K ⊆ R ∧ IsRegion K u u' ∧ K.Nonempty ∧
      ∃ t₀ : ℕ, 0 < t₀ ∧ PeriodOn ξ' K (((t₀ * q : ℕ) : ℤ) • u') := by
  have hF₀R : ∀ g ∈ (Finset.range (Hsup fr S a + 1)).image
      (fun j₀ : ℕ => b₀ + (j₀ : ℤ) • fr.dv), g ∈ R := by
    intro g hg
    obtain ⟨j₀, -, rfl⟩ := Finset.mem_image.mp hg
    exact fr.add_nsmul_dv_mem hR_region hb₀ j₀
  obtain ⟨t₀, ht₀, hrep⟩ := exists_band_repeat hfin hc hRper hR_region hF₀R q
  have hδ : 0 < dot fr.n u' := fr.dot_n_u'
  have hd : 0 < (q : ℤ) * dot fr.n u' := mul_pos (by exact_mod_cast hq) hδ
  refine sweep_conclusion_of_cofinal_ladders hξ' hgen hR_region hc hRper fr.n cQ
    fr.dot_n_u fr.dot_n_u' (dot fr.n b₀ - 1) ((q : ℤ) * dot fr.n u') hd q ht₀ ?_
  intro N
  obtain ⟨r, hr, hband⟩ := hrep (max N (cQ - dot fr.n b₀ + 1).toNat)
  set v : ℤ × ℤ := (r : ℤ) • ((q : ℤ) • u') with hv
  have hvn : dot fr.n v = (r : ℤ) * ((q : ℤ) * dot fr.n u') := by
    simp only [hv, dot_zsmul']
  set top : ℤ := dot fr.n (b₀ + v) - 1 with htop
  have hrge : (r : ℤ) ≤ (r : ℤ) * ((q : ℤ) * dot fr.n u') := by
    have h1 : (1 : ℤ) ≤ (q : ℤ) * dot fr.n u' := by linarith
    nlinarith [Int.natCast_nonneg r]
  have htopcQ : cQ ≤ top := by
    have h1 : cQ - dot fr.n b₀ + 1 ≤ ((cQ - dot fr.n b₀ + 1).toNat : ℤ) := Int.self_le_toNat _
    have h2 : ((max N (cQ - dot fr.n b₀ + 1).toNat : ℕ) : ℤ) ≤ r := by exact_mod_cast hr
    have h3 : ((cQ - dot fr.n b₀ + 1).toNat : ℤ) ≤ ((max N (cQ - dot fr.n b₀ + 1).toNat : ℕ) : ℤ) := by
      exact_mod_cast le_max_right _ _
    rw [htop, Nivat.LE2.dot_add, hvn]; linarith
  set M : ℕ := (top - cQ).toNat with hM
  have hML : ∀ i : ℕ, cQ ≤ top - ((min i M : ℕ) : ℤ) := by intro i; omega
  obtain ⟨m₀, hm₀0, hstag, hseedm⟩ :=
    hseed t₀ ht₀ (fun i => top - ((min i M : ℕ) : ℤ)) hML (dot fr.d' (b₀ + v) + Wsup fr S a)
  refine ⟨r, le_trans (le_max_left _ _) hr, bandSet fr b₀ v (Hsup fr S a),
    lineAt fr (fun i => top - ((min i M : ℕ) : ℤ)) m₀, Wrow fr S a, ?_, ?_, ?_, ?_⟩
  · exact agree_on_bandSet fr b₀ _ _ _ hband
  · exact hseedm
  · refine hwin_down_of_lineAt fr hvert (le_Hsup fr a) (le_Wsup fr a) (le_Wrow fr a) b₀ v
      (L := fun i => top - ((min i M : ℕ) : ℤ)) ?_ ?_ hm₀0 hstag
    · intro i; show top - ((min i M : ℕ) : ℤ) ≤ top; omega
    · intro i k hk hle
      beta_reduce at hle
      refine ⟨min i M - k, by omega, ?_⟩
      show top - ((min (min i M - k) M : ℕ) : ℤ) = top - ((min i M : ℕ) : ℤ) + k
      omega
  · intro z hz
    have h1 : cQ ≤ dot fr.n z := hz.1.2
    have h2 : dot fr.n z ≤ top := by
      have h := hz.2
      simp only [Set.mem_ofPred_eq] at h
      rw [htop, Nivat.LE2.dot_add, hvn]; linarith
    exact cover_of_lineAt_down fr (Int.self_le_toNat _) m₀ z h1 h2

/-! ### Assembly, upward -/

theorem sweep_conclusion_up_of_lineSeed {ξ ξ' : Config ℤ}
    (hfin : (Set.range ξ').Finite) (hξ' : ξ' ∈ orbitClosure ξ)
    {S : Finset (ℤ × ℤ)} {R : Set (ℤ × ℤ)} {u u' : ℤ × ℤ} (hR_region : IsRegion R u u')
    {c : ℤ} (hc : c ≠ 0) (hRper : PeriodOn ξ' R (c • u))
    (fr : LevelFrame u u') {a : ℤ × ℤ} (hgen : GeneratesAt ξ S a)
    (hvert : ∀ b ∈ S.erase a,
      dot fr.n b < dot fr.n a ∨ (dot fr.n b = dot fr.n a ∧ dot fr.d' b < dot fr.d' a))
    {q : ℕ} (hq : 0 < q) {b₀ : ℤ × ℤ} (hb₀ : b₀ ∈ R)
    {cQ : ℤ} (hseed : LineSeed fr ξ' q (Wsup fr S a) (Wrow fr S a) cQ) :
    ∃ K : Set (ℤ × ℤ), K ⊆ R ∧ IsRegion K u u' ∧ K.Nonempty ∧
      ∃ t₀ : ℕ, 0 < t₀ ∧ PeriodOn ξ' K (((t₀ * q : ℕ) : ℤ) • u') := by
  have hF₀R : ∀ g ∈ (Finset.range (HsupUp fr S a + 1)).image
      (fun j₀ : ℕ => b₀ + (j₀ : ℤ) • fr.dv), g ∈ R := by
    intro g hg
    obtain ⟨j₀, -, rfl⟩ := Finset.mem_image.mp hg
    exact fr.add_nsmul_dv_mem hR_region hb₀ j₀
  obtain ⟨t₀, ht₀, hrep⟩ := exists_band_repeat hfin hc hRper hR_region hF₀R q
  obtain ⟨np, hnp, hnper⟩ := exists_neg_nsmul_period hc hRper
  have hper : PeriodOn ξ' R ((np : ℤ) • u) := by simpa using hnper.neg
  have hδ : 0 < dot fr.n u' := fr.dot_n_u'
  have hd : 0 < (q : ℤ) * dot fr.n u' := mul_pos (by exact_mod_cast hq) hδ
  obtain ⟨r, hr, hband⟩ := hrep (cQ - dot fr.n b₀).toNat
  set v : ℤ × ℤ := (r : ℤ) • ((q : ℤ) • u') with hv
  have hvn : dot fr.n v = (r : ℤ) * ((q : ℤ) * dot fr.n u') := by
    simp only [hv, dot_zsmul']
  set bot : ℤ := dot fr.n (b₀ + v) + HsupUp fr S a + 1 with hbot
  have hrge : (r : ℤ) ≤ (r : ℤ) * ((q : ℤ) * dot fr.n u') := by
    have h1 : (1 : ℤ) ≤ (q : ℤ) * dot fr.n u' := by linarith
    nlinarith [Int.natCast_nonneg r]
  have hbotcQ : cQ ≤ bot := by
    have h1 : cQ - dot fr.n b₀ ≤ ((cQ - dot fr.n b₀).toNat : ℤ) := Int.self_le_toNat _
    have h2 : (((cQ - dot fr.n b₀).toNat : ℕ) : ℤ) ≤ r := by exact_mod_cast hr
    have h3 : (0 : ℤ) ≤ HsupUp fr S a := Int.natCast_nonneg _
    rw [hbot, Nivat.LE2.dot_add, hvn]; linarith
  have hL : ∀ i : ℕ, cQ ≤ bot + (i : ℤ) := fun i => by
    have := Int.natCast_nonneg i; linarith
  obtain ⟨m₀, hm₀0, hstag, hseedm⟩ :=
    hseed t₀ ht₀ (fun i => bot + (i : ℤ)) hL (dot fr.d' (b₀ + v) + Wsup fr S a)
  have hwin := hwin_up_of_lineAt fr hvert (le_HsupUp fr a) (le_Wsup fr a) (le_Wrow fr a) b₀ v
    (L := fun i => bot + (i : ℤ)) (fun i => by show bot ≤ bot + (i : ℤ); omega)
    (fun i k hk hle => by
      refine ⟨i - k, by omega, ?_⟩
      show bot + ((i - k : ℕ) : ℤ) = bot + (i : ℤ) - k
      omega) hm₀0 hstag
  have hlad := ladder_of_seeds hξ' (T_mem_of_mem_orbitClosure hξ' _) hgen
    (D := bandSet fr b₀ v (HsupUp fr S a)) (agree_on_bandSet fr b₀ _ _ _ hband)
    (lineAt fr (fun i => bot + (i : ℤ)) m₀) u (Wrow fr S a) hseedm hwin
  have hU : ∀ z ∈ R ∩ halfPlaneGE fr.n bot, z + u ∈ R ∩ halfPlaneGE fr.n bot :=
    halfCut_add_u_mem hR_region fr.dot_n_u bot
  have hK : IsRegion (R ∩ halfPlaneGE fr.n bot) u u' :=
    Nivat.LE2.isRegion_inter_halfPlaneGE hR_region fr.n bot fr.dot_n_u fr.dot_n_u'
  obtain ⟨z₀, hray⟩ := hK.2.1
  refine ⟨R ∩ halfPlaneGE fr.n bot, Set.inter_subset_left, hK, ⟨z₀, by simpa using hray 0⟩,
    t₀, ht₀, ?_⟩
  refine periodOn_of_ladder_cover hU hnp (hper.mono Set.inter_subset_left) _
    ((T_periodOn_of_periodOn_of_ray hR_region hper (t₀ * q)).mono Set.inter_subset_left)
    _ hlad ?_
  intro z hz
  exact cover_of_lineAt_up fr bot m₀ z hz.2

/-! ### The two directions from `IsGeneratingSet`, and the block -/

/-- **Both sweeps from `IsGeneratingSet`, `Primitive u`, and a seed in either direction.** -/
theorem sweep_conclusion_of_generatingSet_of_lineSeeds {ξ ξ' : Config ℤ}
    (hfin : (Set.range ξ').Finite) (hξ' : ξ' ∈ orbitClosure ξ)
    {S : Finset (ℤ × ℤ)} (hS : IsGeneratingSet ξ S)
    {R : Set (ℤ × ℤ)} {u u' : ℤ × ℤ} (hu : Primitive u) (hdet : det u u' ≠ 0)
    (hR_region : IsRegion R u u')
    {c : ℤ} (hc : c ≠ 0) (hRper : PeriodOn ξ' R (c • u))
    {q : ℕ} (hq : 0 < q) {b₀ : ℤ × ℤ} (hb₀ : b₀ ∈ R) :
    ∃ (fr : LevelFrame u u') (aLo aHi : ℤ × ℤ), aLo ∈ S ∧ aHi ∈ S ∧
      (∀ b ∈ S.erase aLo,
        dot fr.n aLo < dot fr.n b ∨ (dot fr.n aLo = dot fr.n b ∧ dot fr.d' b < dot fr.d' aLo)) ∧
      (∀ b ∈ S.erase aHi,
        dot fr.n b < dot fr.n aHi ∨ (dot fr.n b = dot fr.n aHi ∧ dot fr.d' b < dot fr.d' aHi)) ∧
      (((∃ cQ : ℤ, LineSeed fr ξ' q (Wsup fr S aLo) (Wrow fr S aLo) cQ) ∨
        (∃ cQ : ℤ, LineSeed fr ξ' q (Wsup fr S aHi) (Wrow fr S aHi) cQ)) →
      ∃ K : Set (ℤ × ℤ), K ⊆ R ∧ IsRegion K u u' ∧ K.Nonempty ∧
        ∃ t₀ : ℕ, 0 < t₀ ∧ PeriodOn ξ' K (((t₀ * q : ℕ) : ℤ) • u')) := by
  obtain ⟨fr⟩ := exists_levelFrame hu hdet
  obtain ⟨aLo, haLo, hgenLo, hvertLo⟩ := exists_generating_vertex fr hS
  obtain ⟨aHi, haHi, hgenHi, hvertHi⟩ := exists_generating_vertex_up fr hS
  refine ⟨fr, aLo, aHi, haLo, haHi, hvertLo, hvertHi, ?_⟩
  rintro (⟨cQ, hseed⟩ | ⟨cQ, hseed⟩)
  · exact sweep_conclusion_down_of_lineSeed hfin hξ' hR_region hc hRper fr hgenLo hvertLo hq hb₀
      hseed
  · exact sweep_conclusion_up_of_lineSeed hfin hξ' hR_region hc hRper fr hgenHi hvertHi hq hb₀
      hseed

/-- **The sweep's conclusion from a `B`-block.**  Everything except `HasBlock` and the width
comparison is a binder of `case1_sweep` (or `0 < pw` + `hline`, for `hBQ`). -/
theorem sweep_conclusion_of_generatingSet_of_block {ξ ξ' : Config ℤ}
    (hfin : (Set.range ξ').Finite) (hξ' : ξ' ∈ orbitClosure ξ)
    {S : Finset (ℤ × ℤ)} (hS : IsGeneratingSet ξ S)
    {R : Set (ℤ × ℤ)} {u u' : ℤ × ℤ} (hu : Primitive u) (hdet : det u u' ≠ 0)
    (hR_region : IsRegion R u u')
    {c : ℤ} (hc : c ≠ 0) (hRper : PeriodOn ξ' R (c • u))
    {B Q : Finset (ℤ × ℤ)} {τ t₁ : ℤ} (hτ : τ ≤ t₁) (hBQ : ∀ g ∈ B, g ∈ Q)
    (hQR : ∀ t : ℤ, τ ≤ t → ∀ z ∈ Q, t • u' + z ∈ R ∧ t • u' + z + c • u ∈ R)
    {q : ℕ} (hq : 0 < q)
    (hladder : ∀ g ∈ B, ∀ t : ℤ, t₁ ≤ t → ξ' (g + (t + (q : ℤ)) • u') = ξ' (g + t • u'))
    {b₀ : ℤ × ℤ} (hb₀ : b₀ ∈ R) :
    ∃ (fr : LevelFrame u u') (aLo aHi : ℤ × ℤ), aLo ∈ S ∧ aHi ∈ S ∧
      (∀ b ∈ S.erase aLo,
        dot fr.n aLo < dot fr.n b ∨ (dot fr.n aLo = dot fr.n b ∧ dot fr.d' b < dot fr.d' aLo)) ∧
      (∀ b ∈ S.erase aHi,
        dot fr.n b < dot fr.n aHi ∨ (dot fr.n b = dot fr.n aHi ∧ dot fr.d' b < dot fr.d' aHi)) ∧
      ∀ m : ℕ, HasBlock u u' B m → min (Wrow fr S aLo) (Wrow fr S aHi) ≤ m →
        ∃ K : Set (ℤ × ℤ), K ⊆ R ∧ IsRegion K u u' ∧ K.Nonempty ∧
          ∃ t₀ : ℕ, 0 < t₀ ∧ PeriodOn ξ' K (((t₀ * q : ℕ) : ℤ) • u') := by
  obtain ⟨fr, aLo, aHi, haLo, haHi, hvertLo, hvertHi, himp⟩ :=
    sweep_conclusion_of_generatingSet_of_lineSeeds hfin hξ' hS hu hdet hR_region hc hRper hq hb₀
  refine ⟨fr, aLo, aHi, haLo, haHi, hvertLo, hvertHi, fun m hB hm => himp ?_⟩
  obtain ⟨g₀, hblock⟩ := frameBlock_of_hasBlock hu fr hB
  rcases min_le_iff.mp hm with h | h
  · exact Or.inl (seed_of_block fr hR_region hc hRper hτ hBQ hQR hladder hblock _ h)
  · exact Or.inr (seed_of_block fr hR_region hc hRper hτ hBQ hQR hladder hblock _ h)

/-! ## §32  The width bridge to L1's `maxB_wide`

`sweep_conclusion_of_generatingSet_of_block` (§31) asks for `min (Wrow fr S aLo) (Wrow fr S aHi) ≤ m`;
L1's `maxB_wide` (`L1Assemble.lean:1279`) supplies a run of length
`min (topFace true u S).card (bottomFace true u S).card - 1`.  This section proves the two sides
are the **same number** (`min_Wrow_eq_min_card_face`), so the `hm` obligation of `case1_seed`
closes by `le_of_eq` once L1's block is exported.

Mechanism: `Wrow fr S a` is the sup of `dot fr.d' a - dot fr.d' z` over `a`'s `fr.n`-level in `S`;
that level is a `u`-run (`L1Data.faceIsRun`) on which `dot fr.d'` steps by `1`, and `a` is the
`d'`-maximal end (`hvertLo`/`hvertHi`), so the sup is `|face| - 1`
(`Wrow_eq_card_face_sub_one`).  Which of `aLo`/`aHi` sits on `bottomFace`/`topFace` depends on
whether `fr.n = ±(-u.2, u.1)` (`LevelFrame.dot_n_eq_pm_det`); the `min` absorbs the swap.

Only `topFace`/`bottomFace`/`levelMin`/`levelMax`/`cutNormal`/`faceIsRun` and their four
one-line lemmas are used from `L1Assemble` / `L1Fields`. -/

/-- The normal of a `LevelFrame` over a primitive `u` is `±(-u.2, u.1)`, i.e.
`dot fr.n z = ±det u z`. -/
theorem LevelFrame.dot_n_eq_pm_det {u u' : ℤ × ℤ} (hu : Primitive u) (fr : LevelFrame u u') :
    ∃ c : ℤ, (c = 1 ∨ c = -1) ∧ ∀ z : ℤ × ℤ, dot fr.n z = c * det u z := by
  set p : ℤ × ℤ := (-u.2, u.1) with hp
  have hpprim : Primitive p := by
    show IsCoprime (-u.2) u.1
    exact hu.symm.neg_left
  have h0 : det p fr.n = 0 := by
    have := fr.dot_n_u
    simp only [det, hp, dot] at this ⊢; linarith
  obtain ⟨c, hc⟩ := eq_zsmul_of_det_eq_zero hpprim h0
  have hdv : c * dot p fr.dv = 1 := by rw [← dot_zsmul_left, ← hc]; exact fr.dot_n_dv
  have hpz : ∀ z, dot p z = det u z := fun z => by simp only [hp, dot, det]; ring
  refine ⟨c, ?_, fun z => by rw [hc, dot_zsmul_left, hpz]⟩
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' hdv with ⟨h, -⟩ | ⟨h, -⟩
  · exact Or.inl h
  · exact Or.inr h

/-- `levelMin` is attained at any point minimising the form. -/
theorem levelMin_eq_of_min {S : Finset (ℤ × ℤ)} {w : ℝ × ℝ} (hne : S.Nonempty) {a : ℤ × ℤ}
    (ha : a ∈ S) (hmin : ∀ z ∈ S, inner2 w a ≤ inner2 w z) :
    Nivat.ColleReg.L1Data.levelMin S w = inner2 w a := by
  apply le_antisymm (Nivat.ColleReg.L1Data.levelMin_le hne a ha)
  obtain ⟨z, hz⟩ := Nivat.ColleReg.L1Data.face_levelMin_nonempty (n := w) hne
  rw [Nivat.R2.mem_face] at hz
  rw [← hz.2]; exact hmin z hz.1

theorem levelMax_eq_of_max {S : Finset (ℤ × ℤ)} {w : ℝ × ℝ} (hne : S.Nonempty) {a : ℤ × ℤ}
    (ha : a ∈ S) (hmax : ∀ z ∈ S, inner2 w z ≤ inner2 w a) :
    Nivat.ColleReg.L1Data.levelMax S w = inner2 w a := by
  apply le_antisymm _ (Nivat.ColleReg.L1Data.le_levelMax hne a ha)
  obtain ⟨z, hz⟩ := Nivat.ColleReg.L1Data.face_levelMax_nonempty (n := w) hne
  rw [Nivat.R2.mem_face] at hz
  rw [← hz.2]; exact hmax z hz.1

/-- **`Wrow` is the face length minus one.**  If `a` maximises `dot fr.d'` on its `fr.n`-level,
and that level is the `w`-face at `inner2 w a`, then `Wrow fr S a = |face| - 1`.  The face is a
`u`-run (`L1Data.faceIsRun`), and `dot fr.d'` steps by `1` along `u`. -/
theorem Wrow_eq_card_face_sub_one {u u' : ℤ × ℤ} (fr : LevelFrame u u') {S : Finset (ℤ × ℤ)}
    (hS : LatticeConvex S) (hu : Primitive u) {w : ℝ × ℝ} (hw0 : w ≠ 0) (hwu : inner2 w u = 0)
    (hlev : ∀ z y : ℤ × ℤ, inner2 w z = inner2 w y ↔ dot fr.n z = dot fr.n y)
    {a : ℤ × ℤ} (ha : a ∈ S)
    (hmax : ∀ z ∈ S, dot fr.n z = dot fr.n a → dot fr.d' z ≤ dot fr.d' a) :
    Wrow fr S a = (Nivat.R2.face S w (inner2 w a)).card - 1 := by
  classical
  set F := Nivat.R2.face S w (inner2 w a) with hF
  have hFmem : ∀ z, z ∈ F ↔ z ∈ S ∧ dot fr.n z = dot fr.n a := fun z => by
    rw [hF, Nivat.R2.mem_face, hlev]
  have haF : a ∈ F := (hFmem a).mpr ⟨ha, rfl⟩
  have hfilt : S.filter (fun z => dot fr.n z = dot fr.n a) = F := by
    ext z; rw [Finset.mem_filter, hFmem]
  obtain ⟨z₀, hz₀F, hrun⟩ := Nivat.ColleReg.L1Data.faceIsRun (S₁ := S) (n := w)
    (cmax := inner2 w a) (u' := u) hS hu hw0 hwu ⟨a, haF⟩
  have hd' : ∀ i : ℕ, dot fr.d' (z₀ + (i : ℤ) • u) = dot fr.d' z₀ + i := by
    intro i; rw [Nivat.LE2.dot_add, dot_zsmul', fr.dot_d'_u]; ring
  -- the run exhausts the face
  have himg : (Finset.range F.card).image (fun i : ℕ => z₀ + (i : ℤ) • u) = F := by
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
      exact hrun i (Finset.mem_range.mp hi)
    · rw [Finset.card_image_of_injective _ ?_, Finset.card_range]
      intro i j hij
      have := congrArg (dot fr.d') hij
      rw [hd', hd'] at this
      exact_mod_cast (by linarith : (i : ℤ) = j)
  have hmemF : ∀ z ∈ F, ∃ i : ℕ, i < F.card ∧ z = z₀ + (i : ℤ) • u := by
    intro z hz
    rw [← himg] at hz
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
    exact ⟨i, Finset.mem_range.mp hi, rfl⟩
  obtain ⟨k, hk⟩ : ∃ k : ℕ, F.card = k + 1 :=
    ⟨F.card - 1, by have := Finset.card_pos.mpr ⟨a, haF⟩; omega⟩
  have hk' : (Nivat.R2.face S w (inner2 w a)).card = k + 1 := hk
  -- `a` sits at the far end of the run
  have htop : dot fr.d' z₀ + k ≤ dot fr.d' a := by
    have hmem := hrun k (by omega)
    rw [hFmem] at hmem
    have := hmax _ hmem.1 hmem.2
    rwa [hd'] at this
  have hbot : dot fr.d' a ≤ dot fr.d' z₀ + k := by
    obtain ⟨i, hi, hai⟩ := hmemF a haF
    rw [hai, hd']; omega
  have hda : dot fr.d' a = dot fr.d' z₀ + k := le_antisymm hbot htop
  -- evaluate the sup
  unfold Wrow
  rw [hfilt, hk, Nat.add_sub_cancel]
  apply le_antisymm
  · apply Finset.sup_le
    intro z hz
    obtain ⟨i, hi, rfl⟩ := hmemF z hz
    rw [hd', hda]; omega
  · have := Finset.le_sup (f := fun z => (dot fr.d' a - dot fr.d' z).toNat) hz₀F
    refine le_trans (le_of_eq ?_) this
    rw [hda]; omega

/-- **The bridge to L1's width.**  For the two vertices of `sweep_conclusion_of_generatingSet_of_block`
the minimum of the two `Wrow`s is exactly the width `maxB_wide` (`L1Assemble.lean:1279`)
supplies, `min |top u-face| |bottom u-face| - 1`.  Which vertex sits on which face depends on
the sign of `fr.n` against `(-u.2, u.1)`; the `min` absorbs it. -/
theorem min_Wrow_eq_min_card_face {u u' : ℤ × ℤ} (fr : LevelFrame u u') {S : Finset (ℤ × ℤ)}
    (hS : LatticeConvex S) (hne : S.Nonempty) (hu : Primitive u)
    {aLo aHi : ℤ × ℤ} (haLo : aLo ∈ S) (haHi : aHi ∈ S)
    (hvertLo : ∀ b ∈ S.erase aLo,
      dot fr.n aLo < dot fr.n b ∨ (dot fr.n aLo = dot fr.n b ∧ dot fr.d' b < dot fr.d' aLo))
    (hvertHi : ∀ b ∈ S.erase aHi,
      dot fr.n b < dot fr.n aHi ∨ (dot fr.n b = dot fr.n aHi ∧ dot fr.d' b < dot fr.d' aHi)) :
    min (Wrow fr S aLo) (Wrow fr S aHi) =
      min (Nivat.ColleReg.L1Data.topFace true u S).card
        (Nivat.ColleReg.L1Data.bottomFace true u S).card - 1 := by
  classical
  set w : ℝ × ℝ := Nivat.ColleReg.L1Data.cutNormal true u with hw
  have hw0 : w ≠ 0 := Nivat.ColleReg.L1Data.cutNormal_ne_zero true hu.ne_zero
  have hwu : inner2 w u = 0 := Nivat.ColleReg.L1Data.inner2_cutNormal true u
  have hwz : ∀ z : ℤ × ℤ, inner2 w z = (det u z : ℝ) := by
    intro z
    simp only [hw, Nivat.ColleReg.L1Data.cutNormal, if_true, Nivat.LE2.inner2_toReal,
      Nivat.ColleReg.dot_perp]
  obtain ⟨c, hc, hn⟩ := fr.dot_n_eq_pm_det hu
  have hc0 : c ≠ 0 := by rcases hc with rfl | rfl <;> norm_num
  have hlev : ∀ z y : ℤ × ℤ, inner2 w z = inner2 w y ↔ dot fr.n z = dot fr.n y := by
    intro z y
    rw [hwz, hwz, hn, hn, Int.cast_inj]
    exact (mul_right_inj' hc0).symm
  -- the two vertices are extremal on their levels
  have hmaxLo : ∀ z ∈ S, dot fr.n z = dot fr.n aLo → dot fr.d' z ≤ dot fr.d' aLo := by
    intro z hz hlv
    by_cases hza : z = aLo
    · rw [hza]
    · rcases hvertLo z (Finset.mem_erase.mpr ⟨hza, hz⟩) with h | h
      · omega
      · exact h.2.le
  have hmaxHi : ∀ z ∈ S, dot fr.n z = dot fr.n aHi → dot fr.d' z ≤ dot fr.d' aHi := by
    intro z hz hlv
    by_cases hza : z = aHi
    · rw [hza]
    · rcases hvertHi z (Finset.mem_erase.mpr ⟨hza, hz⟩) with h | h
      · omega
      · exact h.2.le
  have hLo : ∀ z ∈ S, dot fr.n aLo ≤ dot fr.n z := by
    intro z hz
    by_cases hza : z = aLo
    · rw [hza]
    · rcases hvertLo z (Finset.mem_erase.mpr ⟨hza, hz⟩) with h | h
      · exact h.le
      · exact h.1.le
  have hHi : ∀ z ∈ S, dot fr.n z ≤ dot fr.n aHi := by
    intro z hz
    by_cases hza : z = aHi
    · rw [hza]
    · rcases hvertHi z (Finset.mem_erase.mpr ⟨hza, hz⟩) with h | h
      · exact h.le
      · exact h.1.le
  have eLo := Wrow_eq_card_face_sub_one fr hS hu hw0 hwu hlev haLo hmaxLo
  have eHi := Wrow_eq_card_face_sub_one fr hS hu hw0 hwu hlev haHi hmaxHi
  have hdetLo : ∀ z ∈ S, c * det u aLo ≤ c * det u z := fun z hz => by
    rw [← hn, ← hn]; exact hLo z hz
  have hdetHi : ∀ z ∈ S, c * det u z ≤ c * det u aHi := fun z hz => by
    rw [← hn, ← hn]; exact hHi z hz
  unfold Nivat.ColleReg.L1Data.topFace Nivat.ColleReg.L1Data.bottomFace
  rw [← hw]
  rcases hc with rfl | rfl
  · -- `fr.n = (-u.2, u.1)`: `aLo` on the bottom face, `aHi` on the top face
    have hmin : Nivat.ColleReg.L1Data.levelMin S w = inner2 w aLo :=
      levelMin_eq_of_min hne haLo fun z hz => by
        rw [hwz, hwz]; exact_mod_cast (by simpa using hdetLo z hz : det u aLo ≤ det u z)
    have hmax : Nivat.ColleReg.L1Data.levelMax S w = inner2 w aHi :=
      levelMax_eq_of_max hne haHi fun z hz => by
        rw [hwz, hwz]; exact_mod_cast (by simpa using hdetHi z hz : det u z ≤ det u aHi)
    rw [hmin, hmax, eLo, eHi]; omega
  · -- `fr.n = -(-u.2, u.1)`: `aLo` on the top face, `aHi` on the bottom face
    have hmax : Nivat.ColleReg.L1Data.levelMax S w = inner2 w aLo :=
      levelMax_eq_of_max hne haLo fun z hz => by
        rw [hwz, hwz]
        have := hdetLo z hz
        exact_mod_cast (by linarith : det u z ≤ det u aLo)
    have hmin : Nivat.ColleReg.L1Data.levelMin S w = inner2 w aHi :=
      levelMin_eq_of_min hne haHi fun z hz => by
        rw [hwz, hwz]
        have := hdetHi z hz
        exact_mod_cast (by linarith : det u aHi ≤ det u z)
    rw [hmin, hmax, eLo, eHi]; omega

/-! ## §33  The block itself: `maxB` carries `|det u u'|` levels

§31 asked L1 for `HasBlock u u' B m` and §32 settled the width.  The block is produced on L1's
side: `L1Data.maxB_wide_levels` (`L1Assemble.lean:1530`) shows `maxB (derivedQ ε u' S₁) u' pw`
meets `|det u u'| + 1` consecutive `det u ·`-levels with a `u`-run of width
`min |top u-face| |bottom u-face| − 1` on each, and `L1Data.maxB_block` (`L1Assemble.lean:1631`)
re-indexes that by residues into the byte-identical hypothesis of `hasBlock_of_either` (§31).
So `hasBlock_maxB` below is glue, not mathematics.

History (§20): a first version of this section (2026-09-19 08:27, ~300 lines:
`mem_of_parallelogram` / `window_ceil` / `window_floor` / `hasBlock_of_corners`) proved the same
block here from the four corners of Collé's parallelogram `Q` (`b3_colle2.txt:628`), kernel-clean.
It was written in the same hour as L1's `maxB_levels_core` / `maxB_wide_levels`, neither lane
having seen the other's; team-lead ruled the proof lives where `maxB` / `derivedQ` / `topFace`
are defined, and this copy was deleted.  The only thing retained from it is the hypothesis
`2 ≤ |top u'-face|` (i.e. `0 < pw`), which is **necessary**: on the unit square with `u = (1,0)`,
`u' = (1,3)`, `ε = true` the top `u'`-face is a single point, `maxB` has two levels, and the
block wants three (hand computation).  At the call site `0 < pw` is
`Nivat.ColleStep.pos_pw_of_case1_hyps` (`RegionSteps.lean`).

⚠ This closes the *mathematics* of `case1_seed`'s block conjunct; it is not a discharge.
`sorry TOTAL` does not move until `case1_seed` is wired through `hasBlock_maxB` and
`min_Wrow_eq_min_card_face`, which happens in `RegionSteps.lean`, not here. -/

open Nivat.ColleReg.L1Data in
/-- **`maxB` has the block** (the `|det u u'|`-level strengthening of `maxB_wide`,
`L1Assemble.lean:1279`).  Same hypotheses plus `2 ≤ |top u'-face|` (i.e. `0 < pw`), which is
what makes Collé's parallelogram `Q` (`b3_colle2.txt:628`) have a `u'`-edge at all; without it
the block is false (unit square, `u = (1,0)`, `u' = (1,3)`).  Body: L1's `maxB_block` through
the §31 adapter. -/
theorem hasBlock_maxB {S₁ : Finset (ℤ × ℤ)} (hS : LatticeConvex S₁) (hne : S₁.Nonempty)
    {u u' : ℤ × ℤ} (hu : Primitive u) (hu' : Primitive u') (hdet : det u u' ≠ 0) (ε : Bool)
    (hkt : 2 ≤ (topFace ε u' S₁).card) :
    HasBlock u u' (maxB (derivedQ ε u' S₁) u' ((topFace ε u' S₁).card - 1))
      (min (topFace true u S₁).card (bottomFace true u S₁).card - 1) :=
  hasBlock_of_either (Nivat.ColleReg.L1Data.maxB_block hS hne hu hu' hdet ε hkt)

open Nivat.ColleReg (expNormal expLevel chainFull wedgeFull fullSweep mem_fullSweep_iff
  dot_expNormal_vl dot_expNormal_u')

/-! ## §34  `LevelFrame` on L1's `expNormal` / `expLevel` frame, and the corner sweep -/

/-- The dual coordinate to `expNormal u' vl`: `dot (expDual u' vl) u' = 1`,
`dot (expDual u' vl) vl = 0` under unimodularity. -/
def expDual (u' vl : ℤ × ℤ) : ℤ × ℤ := det u' vl • (vl.2, -vl.1)

theorem dot_expDual_vl (u' vl : ℤ × ℤ) : dot (expDual u' vl) vl = 0 := by
  simp only [expDual, dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

theorem dot_expDual_u' {u' vl : ℤ × ℤ} (hunimod : det u' vl = 1 ∨ det u' vl = -1) :
    dot (expDual u' vl) u' = 1 := by
  have hsq : det u' vl * det u' vl = 1 := by rcases hunimod with h | h <;> rw [h] <;> ring
  simp only [expDual, dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, det] at hsq ⊢
  linear_combination hsq

/-- **`LevelFrame u' vl` with normal `expNormal u' vl`.**  Lines run along `u'`, levels are
`dot (expNormal u' vl)`, the level step is `vl`. -/
noncomputable def expFrame {u' vl : ℤ × ℤ} (hunimod : det u' vl = 1 ∨ det u' vl = -1) :
    LevelFrame u' vl where
  n := expNormal u' vl
  dv := vl
  d' := expDual u' vl
  dot_n_u := dot_expNormal_u'
  dot_n_u' := by rw [dot_expNormal_vl hunimod]; exact one_pos
  dot_n_dv := dot_expNormal_vl hunimod
  dot_d'_u := dot_expDual_u' hunimod
  dot_d'_dv := dot_expDual_vl u' vl
  dot_d'_u' := by rw [dot_expDual_vl]
  decomp := by
    intro z
    have hsq : det u' vl * det u' vl = 1 := by rcases hunimod with h | h <;> rw [h] <;> ring
    simp only [det] at hsq
    apply Prod.ext
    · simp only [expNormal, expDual, dot, det, Prod.fst_add, Prod.smul_fst, Prod.smul_snd,
        smul_eq_mul]
      linear_combination (-z.1) * hsq
    · simp only [expNormal, expDual, dot, det, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
        smul_eq_mul]
      linear_combination (-z.2) * hsq

@[simp] theorem expFrame_n {u' vl : ℤ × ℤ} (hunimod : det u' vl = 1 ∨ det u' vl = -1) :
    (expFrame hunimod).n = expNormal u' vl := rfl

@[simp] theorem expFrame_d' {u' vl : ℤ × ℤ} (hunimod : det u' vl = 1 ∨ det u' vl = -1) :
    (expFrame hunimod).d' = expDual u' vl := rfl

/-! ### The corner sweep, on an abstract frame -/

/-- Backward enumeration of a line from the ray start `g₁`: `g₁ - u, g₁ - 2u, …`, clamped at
`M + 1` steps. -/
def cornerEnum (u g₁ : ℤ × ℤ) (M : ℕ) (j : ℕ) : ℤ × ℤ :=
  g₁ - (((min j M : ℕ) : ℤ) + 1) • u

theorem hwin_corner {u u' : ℤ × ℤ} (fr : LevelFrame u u') {S : Finset (ℤ × ℤ)} {a : ℤ × ℤ}
    (hlev : ∀ b ∈ S, dot fr.n a ≤ dot fr.n b)
    (hα : ∀ b ∈ S, dot fr.d' a ≤ dot fr.d' b)
    {D : Set (ℤ × ℤ)} {g₁ : ℤ × ℤ} {M : ℕ}
    (hDup : ∀ z, dot fr.n g₁ < dot fr.n z → dot fr.d' g₁ - (M + 1) ≤ dot fr.d' z → z ∈ D)
    (hDray : ∀ z, dot fr.n z = dot fr.n g₁ → dot fr.d' g₁ ≤ dot fr.d' z → z ∈ D) :
    ∀ j : ℕ, ∀ z ∈ S.erase a,
      z + (cornerEnum u g₁ M j - a) ∈ D ∨
        ∃ j' : ℕ, j' < j ∧ z + (cornerEnum u g₁ M j - a) = cornerEnum u g₁ M j' := by
  intro j z hz
  obtain ⟨hne, hzS⟩ := Finset.mem_erase.mp hz
  set k : ℕ := min j M with hk
  have hkj : k ≤ j := min_le_left _ _
  have hkM : k ≤ M := min_le_right _ _
  set w : ℤ × ℤ := z + (cornerEnum u g₁ M j - a) with hw
  have hwn : dot fr.n w = dot fr.n z + dot fr.n g₁ - dot fr.n a := by
    simp only [hw, cornerEnum, Nivat.LE2.dot_add, Nivat.LE2.dot_sub, dot_zsmul', fr.dot_n_u]
    ring
  have hwd : dot fr.d' w = dot fr.d' z + dot fr.d' g₁ - ((k : ℤ) + 1) - dot fr.d' a := by
    simp only [hw, cornerEnum, Nivat.LE2.dot_add, Nivat.LE2.dot_sub, dot_zsmul', fr.dot_d'_u]
    ring
  have hlz := hlev z hzS
  have haz := hα z hzS
  have hkM' : (k : ℤ) ≤ M := by exact_mod_cast hkM
  rcases lt_or_eq_of_le hlz with hlt | heq
  · left
    refine hDup w (by rw [hwn]; linarith) ?_
    rw [hwd]; linarith
  · have hαlt : dot fr.d' a < dot fr.d' z := by
      rcases lt_or_eq_of_le haz with h | h
      · exact h
      · exact absurd (fr.ext_dots heq.symm h.symm) hne
    set t : ℕ := (dot fr.d' z - dot fr.d' a).toNat with ht
    have htval : (t : ℤ) = dot fr.d' z - dot fr.d' a := by omega
    have ht1 : 1 ≤ t := by omega
    by_cases hkt : k + 1 ≤ t
    · left
      refine hDray w (by rw [hwn]; linarith) ?_
      have : (k : ℤ) + 1 ≤ t := by exact_mod_cast hkt
      rw [hwd]; linarith
    · push Not at hkt
      right
      have htk : t ≤ k := by omega
      refine ⟨k - t, by omega, fr.ext_dots ?_ ?_⟩
      · rw [hwn]; simp only [cornerEnum, Nivat.LE2.dot_sub, dot_zsmul', fr.dot_n_u]; linarith
      · rw [hwd]; simp only [cornerEnum, Nivat.LE2.dot_sub, dot_zsmul', fr.dot_d'_u]
        have hmin : min (k - t) M = k - t := min_eq_left (by omega)
        rw [hmin, Nat.cast_sub htk]; linarith

theorem cover_corner {u u' : ℤ × ℤ} (fr : LevelFrame u u') (g₁ : ℤ × ℤ) (M : ℕ) :
    ∀ z : ℤ × ℤ, dot fr.n z = dot fr.n g₁ → dot fr.d' g₁ - (M + 1) ≤ dot fr.d' z →
      dot fr.d' z < dot fr.d' g₁ → ∃ j : ℕ, z = cornerEnum u g₁ M j := by
  intro z hn hlo hhi
  set j : ℕ := (dot fr.d' g₁ - dot fr.d' z - 1).toNat with hj
  have hjval : (j : ℤ) = dot fr.d' g₁ - dot fr.d' z - 1 := by omega
  have hjM : j ≤ M := by omega
  refine ⟨j, fr.ext_dots ?_ ?_⟩
  · simp only [cornerEnum, Nivat.LE2.dot_sub, dot_zsmul', fr.dot_n_u]; linarith
  · simp only [cornerEnum, Nivat.LE2.dot_sub, dot_zsmul', fr.dot_d'_u, min_eq_left hjM]
    linarith

/-- **The corner segment of a line is generated from the region above it and the ray ahead of
it**, provided `a` is the corner vertex of `S` (lowest level, and first along `+u` among all of
`S`).  Pure combinatorics: no `Config`, no `GeneratesAt`. -/
theorem corner_line_subset_genClosure {u u' : ℤ × ℤ} (fr : LevelFrame u u')
    {S : Finset (ℤ × ℤ)} {a : ℤ × ℤ}
    (hlev : ∀ b ∈ S, dot fr.n a ≤ dot fr.n b)
    (hα : ∀ b ∈ S, dot fr.d' a ≤ dot fr.d' b)
    {D : Set (ℤ × ℤ)} {g₁ : ℤ × ℤ} {M : ℕ}
    (hDup : ∀ z, dot fr.n g₁ < dot fr.n z → dot fr.d' g₁ - (M + 1) ≤ dot fr.d' z → z ∈ D)
    (hDray : ∀ z, dot fr.n z = dot fr.n g₁ → dot fr.d' g₁ ≤ dot fr.d' z → z ∈ D) :
    {z | dot fr.n z = dot fr.n g₁ ∧ dot fr.d' g₁ - (M + 1) ≤ dot fr.d' z} ⊆
      genClosure S a D := by
  rintro z ⟨hn, hlo⟩
  by_cases hhi : dot fr.d' z < dot fr.d' g₁
  · obtain ⟨j, rfl⟩ := cover_corner fr g₁ M z hn hlo hhi
    refine Nivat.L3Cover.enum_mem_genClosure_of_window
      (enum := fun _ j => cornerEnum u g₁ M j) ?_ 0 j
    intro i j z hz
    rcases hwin_corner fr hlev hα hDup hDray j z hz with h | ⟨j', hj', he⟩
    · exact Or.inl (Or.inl h)
    · exact Or.inr ⟨j', hj', he.symm⟩
  · push Not at hhi
    exact subset_genClosure S a D (hDray z hn hhi)

/-! ### The wedge in `expDual` coordinates -/

theorem mem_wedgeFull_of_expDual_le {B : Set (ℤ × ℤ)} {vl u' : ℤ × ℤ}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) {b₁ : ℤ × ℤ} (hb₁ : b₁ ∈ B) {z : ℤ × ℤ}
    (hz : dot (expDual u' vl) b₁ ≤ dot (expDual u' vl) z) : z ∈ wedgeFull B vl u' := by
  set fr := expFrame hunimod
  refine ⟨b₁ + (dot (expNormal u' vl) z - dot (expNormal u' vl) b₁) • vl,
    mem_fullSweep_iff.mpr ⟨b₁, hb₁, _, rfl⟩,
    (dot (expDual u' vl) z - dot (expDual u' vl) b₁).toNat, fr.ext_dots ?_ ?_⟩
  · show dot (expNormal u' vl) z = dot (expNormal u' vl) _
    simp only [Nivat.LE2.dot_add, dot_zsmul', dot_expNormal_vl hunimod, dot_expNormal_u']
    ring
  · show dot (expDual u' vl) z = dot (expDual u' vl) _
    simp only [Nivat.LE2.dot_add, dot_zsmul', dot_expDual_vl, dot_expDual_u' hunimod]
    rw [Int.toNat_of_nonneg (by linarith)]; ring

theorem expDual_le_of_mem_wedgeFull {B : Set (ℤ × ℤ)} {vl u' : ℤ × ℤ}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) {b₁ : ℤ × ℤ}
    (hBα : ∀ b ∈ B, dot (expDual u' vl) b₁ ≤ dot (expDual u' vl) b) {z : ℤ × ℤ}
    (hz : z ∈ wedgeFull B vl u') : dot (expDual u' vl) b₁ ≤ dot (expDual u' vl) z := by
  obtain ⟨g, hg, t, rfl⟩ := hz
  obtain ⟨b, hb, k, rfl⟩ := mem_fullSweep_iff.mp hg
  have := hBα b hb
  simp only [Nivat.LE2.dot_add, dot_zsmul', dot_expDual_vl, dot_expDual_u' hunimod]
  have ht : (0 : ℤ) ≤ t := Int.natCast_nonneg _
  linarith

/-! ### `chainFull`: the next slice is generated from the current one plus a ray -/

theorem chainFull_succ_subset_genClosure {B : Set (ℤ × ℤ)} {vl u' b₀ : ℤ × ℤ}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    {b₁ : ℤ × ℤ} (hb₁ : b₁ ∈ B)
    (hBα : ∀ b ∈ B, dot (expDual u' vl) b₁ ≤ dot (expDual u' vl) b)
    {S : Finset (ℤ × ℤ)} {a : ℤ × ℤ}
    (hlev : ∀ b ∈ S, dot (expNormal u' vl) a ≤ dot (expNormal u' vl) b)
    (hα : ∀ b ∈ S, dot (expDual u' vl) a ≤ dot (expDual u' vl) b)
    (N : ℕ) {g : ℤ × ℤ} (hg : dot (expNormal u' vl) g = expLevel u' vl b₀ (N + 1)) (t₀ : ℤ) :
    chainFull B vl u' b₀ (N + 1) ⊆
      genClosure S a (chainFull B vl u' b₀ N ∪ {z | ∃ t : ℤ, t₀ ≤ t ∧ z = t • u' + g}) := by
  set fr := expFrame hunimod with hfr
  intro z hz
  have hz' : z ∈ wedgeFull B vl u' ∧ expLevel u' vl b₀ (N + 1) ≤ dot (expNormal u' vl) z := hz
  obtain ⟨hzW, hzlev⟩ := hz'
  by_cases hN : expLevel u' vl b₀ N ≤ dot (expNormal u' vl) z
  · exact subset_genClosure _ _ _ (Or.inl ⟨hzW, hN⟩)
  have hline : dot (expNormal u' vl) z = expLevel u' vl b₀ (N + 1) := by
    simp only [expLevel] at hzlev hN ⊢; push_cast at hzlev hN ⊢; omega
  have hstep : expLevel u' vl b₀ N = expLevel u' vl b₀ (N + 1) + 1 := by
    simp only [expLevel]; push_cast; ring
  set g₁ : ℤ × ℤ := g + t₀ • u' with hg₁
  have hg₁n : dot (expNormal u' vl) g₁ = expLevel u' vl b₀ (N + 1) := by
    simp only [hg₁, Nivat.LE2.dot_add, dot_zsmul', dot_expNormal_u', hg]; ring
  have hg₁d : dot (expDual u' vl) g₁ = dot (expDual u' vl) g + t₀ := by
    simp only [hg₁, Nivat.LE2.dot_add, dot_zsmul', dot_expDual_u' hunimod]; ring
  have hzα := expDual_le_of_mem_wedgeFull hunimod hBα hzW
  -- the ray, as a membership lemma
  have hray : ∀ w, dot (expNormal u' vl) w = expLevel u' vl b₀ (N + 1) →
      dot (expDual u' vl) g₁ ≤ dot (expDual u' vl) w →
      w ∈ chainFull B vl u' b₀ N ∪ {z | ∃ t : ℤ, t₀ ≤ t ∧ z = t • u' + g} := by
    intro w hwn hwd
    refine Or.inr ⟨dot (expDual u' vl) w - dot (expDual u' vl) g, by linarith, fr.ext_dots ?_ ?_⟩
    · show dot (expNormal u' vl) w = dot (expNormal u' vl) _
      simp only [Nivat.LE2.dot_add, dot_zsmul', dot_expNormal_u', hwn, hg]; ring
    · show dot (expDual u' vl) w = dot (expDual u' vl) _
      simp only [Nivat.LE2.dot_add, dot_zsmul', dot_expDual_u' hunimod]; ring
  by_cases hcase : dot (expDual u' vl) g₁ ≤ dot (expDual u' vl) b₁
  · exact subset_genClosure _ _ _ (hray z hline (le_trans hcase hzα))
  push Not at hcase
  set M : ℕ := (dot (expDual u' vl) g₁ - dot (expDual u' vl) b₁ - 1).toNat with hM
  have hMval : (M : ℤ) + 1 = dot (expDual u' vl) g₁ - dot (expDual u' vl) b₁ := by omega
  refine corner_line_subset_genClosure fr (M := M) (g₁ := g₁) hlev hα ?_ ?_ ⟨?_, ?_⟩
  · intro w hwn hwd
    refine Or.inl ⟨mem_wedgeFull_of_expDual_le hunimod hb₁ ?_, ?_⟩
    · show dot (expDual u' vl) b₁ ≤ dot (expDual u' vl) w
      have : dot fr.d' g₁ - (M + 1) ≤ dot fr.d' w := hwd
      simp only [hfr, expFrame_d'] at this; linarith
    · show expLevel u' vl b₀ N ≤ dot (expNormal u' vl) w
      have : dot fr.n g₁ < dot fr.n w := hwn
      simp only [hfr, expFrame_n] at this; omega
  · intro w hwn hwd
    exact hray w (by simpa [hfr, hg₁n] using hwn) hwd
  · show dot (expNormal u' vl) z = dot (expNormal u' vl) g₁
    rw [hline, hg₁n]
  · show dot (expDual u' vl) g₁ - (M + 1) ≤ dot (expDual u' vl) z
    linarith

/-! ### Necessity: with a fixed generating vertex, the corner condition cannot be dropped -/

/-- Generation from a fixed vertex `a` never lowers a linear functional below its infimum on the
seed, once some other point of `S` sits strictly below `a` for that functional. -/
theorem genClosure_subset_of_exists_dot_lt {S : Finset (ℤ × ℤ)} {a : ℤ × ℤ} (n : ℤ × ℤ)
    (hnot : ∃ b ∈ S.erase a, dot n b < dot n a) {D : Set (ℤ × ℤ)} {c : ℤ}
    (hD : ∀ z ∈ D, c ≤ dot n z) : genClosure S a D ⊆ D ∪ {z | c < dot n z} := by
  obtain ⟨b₀, hb₀, hlt⟩ := hnot
  have key : ∀ m : ℕ, ∀ z ∈ genFill S a D m, z ∈ D ∪ {z | c < dot n z} := by
    intro m
    induction m with
    | zero => exact fun z hz => Or.inl hz
    | succ m ih =>
      intro z hz
      rcases hz with hz | ⟨t, rfl, ht⟩
      · exact ih z hz
      · right
        have h := ih _ (ht b₀ hb₀)
        have hc : c ≤ dot n (b₀ + t) := by
          rcases h with h | h
          · exact hD _ h
          · exact le_of_lt h
        show c < dot n (a + t)
        rw [Nivat.LE2.dot_add] at hc ⊢; linarith
  intro z hz
  obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hz
  exact key m z hm

/-- **The corner point of the next slice is not generated when `a` is not the corner vertex.**
If some `b ∈ S.erase a` is strictly lower (`expNormal`) or strictly behind (`expDual`) than
`a`, and the ray starts strictly ahead of the wedge's `vl`-edge, then
`chainFull (N+1) ⊄ genClosure S a (chainFull N ∪ ray)`.  Converse of
`chainFull_succ_subset_genClosure`: the two corner hypotheses there are necessary, not a
convenience. -/
theorem not_chainFull_succ_subset_genClosure {B : Set (ℤ × ℤ)} {vl u' b₀ : ℤ × ℤ}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    {b₁ : ℤ × ℤ} (hb₁ : b₁ ∈ B)
    (hBα : ∀ b ∈ B, dot (expDual u' vl) b₁ ≤ dot (expDual u' vl) b)
    {S : Finset (ℤ × ℤ)} {a : ℤ × ℤ}
    (hnot : (∃ b ∈ S.erase a, dot (expNormal u' vl) b < dot (expNormal u' vl) a) ∨
      (∃ b ∈ S.erase a, dot (expDual u' vl) b < dot (expDual u' vl) a))
    (N : ℕ) {g : ℤ × ℤ} (hg : dot (expNormal u' vl) g = expLevel u' vl b₀ (N + 1)) (t₀ : ℤ)
    (hahead : dot (expDual u' vl) b₁ < dot (expDual u' vl) g + t₀) :
    ¬ chainFull B vl u' b₀ (N + 1) ⊆
      genClosure S a (chainFull B vl u' b₀ N ∪ {z | ∃ t : ℤ, t₀ ≤ t ∧ z = t • u' + g}) := by
  intro hsub
  set fr := expFrame hunimod with hfr
  set D : Set (ℤ × ℤ) :=
    chainFull B vl u' b₀ N ∪ {z | ∃ t : ℤ, t₀ ≤ t ∧ z = t • u' + g} with hD
  -- the corner point of the new line
  set p₀ : ℤ × ℤ := b₁ + (expLevel u' vl b₀ (N + 1) - dot (expNormal u' vl) b₁) • vl with hp₀
  have hp₀n : dot (expNormal u' vl) p₀ = expLevel u' vl b₀ (N + 1) := by
    simp only [hp₀, Nivat.LE2.dot_add, dot_zsmul', dot_expNormal_vl hunimod]; ring
  have hp₀d : dot (expDual u' vl) p₀ = dot (expDual u' vl) b₁ := by
    simp only [hp₀, Nivat.LE2.dot_add, dot_zsmul', dot_expDual_vl]; ring
  have hp₀mem : p₀ ∈ chainFull B vl u' b₀ (N + 1) :=
    ⟨mem_wedgeFull_of_expDual_le hunimod hb₁ (le_of_eq hp₀d.symm), le_of_eq hp₀n.symm⟩
  have hstep : expLevel u' vl b₀ N = expLevel u' vl b₀ (N + 1) + 1 := by
    simp only [expLevel]; push_cast; ring
  -- `p₀ ∉ D`
  have hp₀D : p₀ ∉ D := by
    rintro (⟨-, hlev⟩ | ⟨t, ht, hpt⟩)
    · have : expLevel u' vl b₀ N ≤ dot (expNormal u' vl) p₀ := hlev
      omega
    · have := congrArg (dot (expDual u' vl)) hpt
      simp only [Nivat.LE2.dot_add, dot_zsmul', dot_expDual_u' hunimod, hp₀d] at this
      linarith
  -- every point of `D` is at level `≥ expLevel (N+1)` and at `expDual ≥ expDual b₁`
  have hDn : ∀ z ∈ D, expLevel u' vl b₀ (N + 1) ≤ dot (expNormal u' vl) z := by
    rintro z (⟨-, hlev⟩ | ⟨t, ht, rfl⟩)
    · have : expLevel u' vl b₀ N ≤ dot (expNormal u' vl) z := hlev
      omega
    · simp only [Nivat.LE2.dot_add, dot_zsmul', dot_expNormal_u', hg]; omega
  have hDd : ∀ z ∈ D, dot (expDual u' vl) b₁ ≤ dot (expDual u' vl) z := by
    rintro z (⟨hW, -⟩ | ⟨t, ht, rfl⟩)
    · exact expDual_le_of_mem_wedgeFull hunimod hBα hW
    · simp only [Nivat.LE2.dot_add, dot_zsmul', dot_expDual_u' hunimod]; linarith
  have hgen := hsub hp₀mem
  rcases hnot with hn | hn
  · rcases genClosure_subset_of_exists_dot_lt _ hn hDn hgen with h | h
    · exact hp₀D h
    · have : expLevel u' vl b₀ (N + 1) < dot (expNormal u' vl) p₀ := h
      omega
  · rcases genClosure_subset_of_exists_dot_lt _ hn hDd hgen with h | h
    · exact hp₀D h
    · have : dot (expDual u' vl) b₁ < dot (expDual u' vl) p₀ := h
      omega

/-- The corner condition is not implied by having two `vl`-parallel edges (Lemma 2.3's guard):
the parallelogram `{(0,1),(0,2),(1,0),(1,1)}` with `u' = (1,0)`, `vl = (0,1)` has its
`expNormal`-minimum at `(1,0)` alone and its `expDual`-minimum on `{(0,1),(0,2)}`. -/
theorem no_corner_vertex_parallelogram :
    ¬ ∃ a ∈ ({((0 : ℤ), (1 : ℤ)), (0, 2), (1, 0), (1, 1)} : Finset (ℤ × ℤ)),
      (∀ b ∈ ({((0 : ℤ), (1 : ℤ)), (0, 2), (1, 0), (1, 1)} : Finset (ℤ × ℤ)),
        dot (expNormal ((1 : ℤ), (0 : ℤ)) ((0 : ℤ), (1 : ℤ))) a ≤
          dot (expNormal ((1 : ℤ), (0 : ℤ)) ((0 : ℤ), (1 : ℤ))) b) ∧
      (∀ b ∈ ({((0 : ℤ), (1 : ℤ)), (0, 2), (1, 0), (1, 1)} : Finset (ℤ × ℤ)),
        dot (expDual ((1 : ℤ), (0 : ℤ)) ((0 : ℤ), (1 : ℤ))) a ≤
          dot (expDual ((1 : ℤ), (0 : ℤ)) ((0 : ℤ), (1 : ℤ))) b) := by
  rintro ⟨a, ha, h1, h2⟩
  have e1 := h1 (1, 0) (by simp)
  have e2 := h2 (0, 1) (by simp)
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha
  simp only [expNormal, expDual, dot, det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at e1 e2
  rcases ha with rfl | rfl | rfl | rfl
  all_goals (dsimp only at e1 e2; omega)

/-! ## §35  The lex bridge: Aface's generic normal is the `(expNormal, expDual)` lex functional -/

/-- (1) Swapping the arguments of `expNormal` is the dual: `expNormal vl u' = expDual u' vl`.
Copied verbatim from team-lead's `tmp/lexbridge_probe.lean` (2026-09-19 17:5x). -/
theorem expNormal_swap_eq_expDual (u' vl : ℤ × ℤ) :
    expNormal vl u' = expDual u' vl := by
  apply Prod.ext <;>
    simp only [expNormal, expDual, det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ring

/-- `dot` is ℤ-linear in its first slot. -/
theorem dot_smul_add (a b : ℤ × ℤ) (c : ℤ) (z : ℤ × ℤ) :
    dot (c • a + b) z = c * dot a z + dot b z := by
  show (c • a + b).1 * z.1 + (c • a + b).2 * z.2
     = c * (a.1 * z.1 + a.2 * z.2) + (b.1 * z.1 + b.2 * z.2)
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- (2) `HbaseBridge.exists_generic_normal_unit`'s normal `c • expNormal u' vl + expNormal vl u'`
is the `(expNormal, expDual)` lex functional with weight `c`.  The explicit `u' vl` in the
rewrite is load-bearing: `expNormal ?a ?b` matches `expNormal u' vl` first. -/
theorem dot_generic_eq_lex (u' vl : ℤ × ℤ) (c : ℤ) (z : ℤ × ℤ) :
    dot (c • expNormal u' vl + expNormal vl u') z
      = c * dot (expNormal u' vl) z + dot (expDual u' vl) z := by
  rw [dot_smul_add, expNormal_swap_eq_expDual u' vl]

/-! ### The lex-weakened corner sweep: true on an abstract frame, with a bigger `D` -/

/-- `hwin_corner` with the corner hypotheses `hlev ∧ hα` replaced by lex-minimality of `a` for
`(fr.n, fr.d')` (min-side: `a` lowest level; on its own level, furthest back).  The price is
`hDup'`: `D` must contain the **entire** open upper half-plane above `g₁`'s level, not just the
`M + 1`-wide strip of `hwin_corner` — a point of `S` on a higher level may now sit arbitrarily
far behind `a`.  (`hwin_corner` is kept verbatim above; this is not a replacement.) -/
theorem hwin_corner_lex {u u' : ℤ × ℤ} (fr : LevelFrame u u') {S : Finset (ℤ × ℤ)} {a : ℤ × ℤ}
    (hlex : ∀ b ∈ S.erase a,
      dot fr.n a < dot fr.n b ∨ (dot fr.n a = dot fr.n b ∧ dot fr.d' a < dot fr.d' b))
    {D : Set (ℤ × ℤ)} {g₁ : ℤ × ℤ} {M : ℕ}
    (hDup' : ∀ z, dot fr.n g₁ < dot fr.n z → z ∈ D)
    (hDray : ∀ z, dot fr.n z = dot fr.n g₁ → dot fr.d' g₁ ≤ dot fr.d' z → z ∈ D) :
    ∀ j : ℕ, ∀ z ∈ S.erase a,
      z + (cornerEnum u g₁ M j - a) ∈ D ∨
        ∃ j' : ℕ, j' < j ∧ z + (cornerEnum u g₁ M j - a) = cornerEnum u g₁ M j' := by
  intro j z hz
  set k : ℕ := min j M with hk
  have hkj : k ≤ j := min_le_left _ _
  have hkM : k ≤ M := min_le_right _ _
  set w : ℤ × ℤ := z + (cornerEnum u g₁ M j - a) with hw
  have hwn : dot fr.n w = dot fr.n z + dot fr.n g₁ - dot fr.n a := by
    simp only [hw, cornerEnum, Nivat.LE2.dot_add, Nivat.LE2.dot_sub, dot_zsmul', fr.dot_n_u]
    ring
  have hwd : dot fr.d' w = dot fr.d' z + dot fr.d' g₁ - ((k : ℤ) + 1) - dot fr.d' a := by
    simp only [hw, cornerEnum, Nivat.LE2.dot_add, Nivat.LE2.dot_sub, dot_zsmul', fr.dot_d'_u]
    ring
  rcases hlex z hz with hlt | ⟨heq, hαlt⟩
  · left
    exact hDup' w (by rw [hwn]; linarith)
  · set t : ℕ := (dot fr.d' z - dot fr.d' a).toNat with ht
    have htval : (t : ℤ) = dot fr.d' z - dot fr.d' a := by omega
    have ht1 : 1 ≤ t := by omega
    by_cases hkt : k + 1 ≤ t
    · left
      refine hDray w (by rw [hwn]; linarith) ?_
      have : (k : ℤ) + 1 ≤ t := by exact_mod_cast hkt
      rw [hwd]; linarith
    · push Not at hkt
      right
      have htk : t ≤ k := by omega
      refine ⟨k - t, by omega, fr.ext_dots ?_ ?_⟩
      · rw [hwn]; simp only [cornerEnum, Nivat.LE2.dot_sub, dot_zsmul', fr.dot_n_u]; linarith
      · rw [hwd]; simp only [cornerEnum, Nivat.LE2.dot_sub, dot_zsmul', fr.dot_d'_u]
        have hmin : min (k - t) M = k - t := min_eq_left (by omega)
        rw [hmin, Nat.cast_sub htk]; linarith

/-- `corner_line_subset_genClosure` under lex-minimality, at the same price (`hDup'`). -/
theorem corner_line_subset_genClosure_lex {u u' : ℤ × ℤ} (fr : LevelFrame u u')
    {S : Finset (ℤ × ℤ)} {a : ℤ × ℤ}
    (hlex : ∀ b ∈ S.erase a,
      dot fr.n a < dot fr.n b ∨ (dot fr.n a = dot fr.n b ∧ dot fr.d' a < dot fr.d' b))
    {D : Set (ℤ × ℤ)} {g₁ : ℤ × ℤ} {M : ℕ}
    (hDup' : ∀ z, dot fr.n g₁ < dot fr.n z → z ∈ D)
    (hDray : ∀ z, dot fr.n z = dot fr.n g₁ → dot fr.d' g₁ ≤ dot fr.d' z → z ∈ D) :
    {z | dot fr.n z = dot fr.n g₁ ∧ dot fr.d' g₁ - (M + 1) ≤ dot fr.d' z} ⊆
      genClosure S a D := by
  rintro z ⟨hn, hlo⟩
  by_cases hhi : dot fr.d' z < dot fr.d' g₁
  · obtain ⟨j, rfl⟩ := cover_corner fr g₁ M z hn hlo hhi
    refine Nivat.L3Cover.enum_mem_genClosure_of_window
      (enum := fun _ j => cornerEnum u g₁ M j) ?_ 0 j
    intro i j z hz
    rcases hwin_corner_lex fr hlex hDup' hDray j z hz with h | ⟨j', hj', he⟩
    · exact Or.inl (Or.inl h)
    · exact Or.inr ⟨j', hj', he.symm⟩
  · push Not at hhi
    exact subset_genClosure S a D (hDray z hn hhi)

/-! ### The lex-weakened `chainFull` step is false -/

/-- **`chainFull_succ_subset_genClosure` does not survive weakening `hlev ∧ hα` to lex-minimality.**
The parallelogram `{(0,1),(0,2),(1,0),(1,1)}` with `u' = (1,0)`, `vl = (0,1)` has the lex-minimum
`a = (1,0)` for `(expNormal, expDual)` (the first conjunct below, proved), yet with the wedge
`B = {(0,0)}` and the ray starting one step ahead of the wedge's `vl`-edge, the next slice is not
generated (second conjunct).  Mechanism: `not_chainFull_succ_subset_genClosure`'s second
disjunct — `(0,1)` sits strictly behind `a` in `expDual`, so the corner of the new slice is never
reached.  The global `hα` in `chainFull_succ_subset_genClosure` is therefore not slack that lex
removes; on a quadrant-shaped `D` it is the whole obligation. -/
theorem not_chainFull_succ_subset_genClosure_of_lexMin :
    (∀ b ∈ ({((0 : ℤ), (1 : ℤ)), (0, 2), (1, 0), (1, 1)} : Finset (ℤ × ℤ)).erase
        ((1 : ℤ), (0 : ℤ)),
      dot (expNormal ((1 : ℤ), (0 : ℤ)) ((0 : ℤ), (1 : ℤ))) ((1 : ℤ), (0 : ℤ)) <
          dot (expNormal ((1 : ℤ), (0 : ℤ)) ((0 : ℤ), (1 : ℤ))) b ∨
        (dot (expNormal ((1 : ℤ), (0 : ℤ)) ((0 : ℤ), (1 : ℤ))) ((1 : ℤ), (0 : ℤ)) =
            dot (expNormal ((1 : ℤ), (0 : ℤ)) ((0 : ℤ), (1 : ℤ))) b ∧
          dot (expDual ((1 : ℤ), (0 : ℤ)) ((0 : ℤ), (1 : ℤ))) ((1 : ℤ), (0 : ℤ)) <
            dot (expDual ((1 : ℤ), (0 : ℤ)) ((0 : ℤ), (1 : ℤ))) b)) ∧
    ¬ chainFull ({((0 : ℤ), (0 : ℤ))} : Set (ℤ × ℤ)) ((0 : ℤ), (1 : ℤ)) ((1 : ℤ), (0 : ℤ))
        ((0 : ℤ), (0 : ℤ)) 1 ⊆
      genClosure ({((0 : ℤ), (1 : ℤ)), (0, 2), (1, 0), (1, 1)} : Finset (ℤ × ℤ))
        ((1 : ℤ), (0 : ℤ))
        (chainFull ({((0 : ℤ), (0 : ℤ))} : Set (ℤ × ℤ)) ((0 : ℤ), (1 : ℤ)) ((1 : ℤ), (0 : ℤ))
            ((0 : ℤ), (0 : ℤ)) 0 ∪
          {z | ∃ t : ℤ, 1 ≤ t ∧ z = t • ((1 : ℤ), (0 : ℤ)) + ((0 : ℤ), (-1 : ℤ))}) := by
  refine ⟨?_, ?_⟩
  · intro b hb
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hb
    obtain ⟨hne, hb⟩ := hb
    simp only [expNormal, expDual, dot, det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    rcases hb with rfl | rfl | rfl | rfl
    · left; norm_num
    · left; norm_num
    · exact absurd rfl hne
    · left; norm_num
  · refine not_chainFull_succ_subset_genClosure (Or.inl (by simp [det]))
      (Set.mem_singleton _) ?_ (Or.inr ⟨((0 : ℤ), (1 : ℤ)), by simp, ?_⟩) 0 ?_ 1 ?_
    · intro b hb
      rw [Set.mem_singleton_iff] at hb
      subst hb
      exact le_rfl
    · simp [expDual, dot, det]
    · simp [expLevel, expNormal, dot, det]
    · simp [expDual, dot, det]

/-! ### Which end: Aface's strict `dot n`-maximum is the level-**maximum**, the corner is the
level-**minimum** -/

/-- On any `LevelFrame`, a strict maximum `a` of the weighted lex functional
`c * dot fr.n + dot fr.d'` with `c` at least the `fr.d'`-spread of `S` about `a` is a
`fr.n`-**maximum** of `S`.  This is the shape `HbaseBridge.exists_vertex_and_row_order`'s `hlt`
takes once `dot_generic_eq_lex` is applied. -/
theorem level_le_of_lex_strict_max {u u' : ℤ × ℤ} (fr : LevelFrame u u') {S : Finset (ℤ × ℤ)}
    {a : ℤ × ℤ} {c : ℤ} (hc : 0 ≤ c)
    (hspread : ∀ b ∈ S, dot fr.d' a - dot fr.d' b ≤ c)
    (hlt : ∀ z ∈ S.erase a, c * dot fr.n z + dot fr.d' z < c * dot fr.n a + dot fr.d' a) :
    ∀ b ∈ S, dot fr.n b ≤ dot fr.n a := by
  intro b hb
  by_cases hba : b = a
  · subst hba; exact le_rfl
  by_contra hgt
  push Not at hgt
  have h1 : 1 ≤ dot fr.n b - dot fr.n a := by omega
  have h2 := mul_le_mul_of_nonneg_left h1 hc
  have h3 := hlt b (Finset.mem_erase.mpr ⟨hba, hb⟩)
  have h4 := hspread b hb
  nlinarith

/-- **Opposite ends.**  `chainFull_succ_subset_genClosure`'s corner is a `fr.n`-**minimum**
(`hlev`, necessary by `not_chainFull_succ_subset_genClosure`); Aface's row-order vertex is a
`fr.n`-**maximum** (`level_le_of_lex_strict_max`).  The same `a` can be both only if `S` lies on
a single `fr.n`-level.  Negating Aface's `n` is not available (`0 < dot n vl` is one of their
positivity constraints and is what bounds `dot n` below on `chainFull … 0`); the two sweeps
simply need two different vertices of `S`, which `IsGeneratingSet` supplies. -/
theorem single_level_of_lex_strict_max_of_hlev {u u' : ℤ × ℤ} (fr : LevelFrame u u')
    {S : Finset (ℤ × ℤ)} {a : ℤ × ℤ} {c : ℤ} (hc : 0 ≤ c)
    (hspread : ∀ b ∈ S, dot fr.d' a - dot fr.d' b ≤ c)
    (hlt : ∀ z ∈ S.erase a, c * dot fr.n z + dot fr.d' z < c * dot fr.n a + dot fr.d' a)
    (hlev : ∀ b ∈ S, dot fr.n a ≤ dot fr.n b) :
    ∀ b ∈ S, dot fr.n b = dot fr.n a :=
  fun b hb => le_antisymm (level_le_of_lex_strict_max fr hc hspread hlt b hb) (hlev b hb)

/-- The `expNormal` instance, fed Aface's normal **literally** (`c • expNormal u' vl +
expNormal vl u'`, `HbaseBridge.lean` §13) through `dot_generic_eq_lex`: their strict maximum is
an `expNormal u' vl`-maximum.  §27: the bridge identity is consumed here, not just stated. -/
theorem expNormal_le_of_generic_strict_max {u' vl : ℤ × ℤ}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) {S : Finset (ℤ × ℤ)} {a : ℤ × ℤ} {c : ℤ}
    (hc : 0 ≤ c)
    (hspread : ∀ b ∈ S, dot (expDual u' vl) a - dot (expDual u' vl) b ≤ c)
    (hlt : ∀ z ∈ S.erase a, dot (c • expNormal u' vl + expNormal vl u') z <
      dot (c • expNormal u' vl + expNormal vl u') a) :
    ∀ b ∈ S, dot (expNormal u' vl) b ≤ dot (expNormal u' vl) a := by
  simp only [dot_generic_eq_lex] at hlt
  exact level_le_of_lex_strict_max (expFrame hunimod) hc hspread hlt

/-! ## §36  Reach-back: when the ray starts at or behind the wedge's `vl`-edge, no vertex
condition is needed -/

/-- **`chainFull_succ_subset_genClosure` with `hlev`, `hα` (and `hb₁`) dropped, at the price of
`hreach`** — the negation of `not_chainFull_succ_subset_genClosure`'s `hahead`.  `S` and `a` are
completely free: every point of the new slice is already in the seed `D`, so `genClosure` is
never entered.  This is exactly the `hcase` branch of `chainFull_succ_subset_genClosure`.

⚠ **Zero consumers by construction** (integrator, 2026-09-19 18:3x, kept per §14): `Straddle`'s
`∀ t₀` (`L1Region.lean:412`) means this covers only the small-`t₀` segment; `hcover` must also hold
for every larger `t₀`, where `hahead` holds and the vertex condition is necessary
(`chainFull_succ_subset_genClosure_iff_of_ahead`). -/
theorem chainFull_succ_subset_genClosure_of_reachback {B : Set (ℤ × ℤ)} {vl u' b₀ : ℤ × ℤ}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    {b₁ : ℤ × ℤ}
    (hBα : ∀ b ∈ B, dot (expDual u' vl) b₁ ≤ dot (expDual u' vl) b)
    (S : Finset (ℤ × ℤ)) (a : ℤ × ℤ)
    (N : ℕ) {g : ℤ × ℤ} (hg : dot (expNormal u' vl) g = expLevel u' vl b₀ (N + 1)) (t₀ : ℤ)
    (hreach : dot (expDual u' vl) g + t₀ ≤ dot (expDual u' vl) b₁) :
    chainFull B vl u' b₀ (N + 1) ⊆
      genClosure S a (chainFull B vl u' b₀ N ∪ {z | ∃ t : ℤ, t₀ ≤ t ∧ z = t • u' + g}) := by
  set fr := expFrame hunimod with hfr
  intro z hz
  have hz' : z ∈ wedgeFull B vl u' ∧ expLevel u' vl b₀ (N + 1) ≤ dot (expNormal u' vl) z := hz
  obtain ⟨hzW, hzlev⟩ := hz'
  by_cases hN : expLevel u' vl b₀ N ≤ dot (expNormal u' vl) z
  · exact subset_genClosure _ _ _ (Or.inl ⟨hzW, hN⟩)
  have hline : dot (expNormal u' vl) z = expLevel u' vl b₀ (N + 1) := by
    simp only [expLevel] at hzlev hN ⊢; push_cast at hzlev hN ⊢; omega
  have hzα := expDual_le_of_mem_wedgeFull hunimod hBα hzW
  refine subset_genClosure _ _ _
    (Or.inr ⟨dot (expDual u' vl) z - dot (expDual u' vl) g, by linarith, fr.ext_dots ?_ ?_⟩)
  · show dot (expNormal u' vl) z = dot (expNormal u' vl) _
    simp only [Nivat.LE2.dot_add, dot_zsmul', dot_expNormal_u', hline, hg]; ring
  · show dot (expDual u' vl) z = dot (expDual u' vl) _
    simp only [Nivat.LE2.dot_add, dot_zsmul', dot_expDual_u' hunimod]; ring

/-- **The exact dichotomy.**  Once the ray starts strictly ahead of the `vl`-edge (`hahead`),
the next slice is generated from `chainFull N ∪ ray` **iff** `a` is the double-minimum corner
vertex of `S`.  `←` is `chainFull_succ_subset_genClosure`, `→` is the contrapositive of
`not_chainFull_succ_subset_genClosure`; together with `_of_reachback` this pins the residual:
the vertex condition is needed exactly when `hahead` holds. -/
theorem chainFull_succ_subset_genClosure_iff_of_ahead {B : Set (ℤ × ℤ)} {vl u' b₀ : ℤ × ℤ}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    {b₁ : ℤ × ℤ} (hb₁ : b₁ ∈ B)
    (hBα : ∀ b ∈ B, dot (expDual u' vl) b₁ ≤ dot (expDual u' vl) b)
    {S : Finset (ℤ × ℤ)} {a : ℤ × ℤ}
    (N : ℕ) {g : ℤ × ℤ} (hg : dot (expNormal u' vl) g = expLevel u' vl b₀ (N + 1)) (t₀ : ℤ)
    (hahead : dot (expDual u' vl) b₁ < dot (expDual u' vl) g + t₀) :
    chainFull B vl u' b₀ (N + 1) ⊆
        genClosure S a (chainFull B vl u' b₀ N ∪ {z | ∃ t : ℤ, t₀ ≤ t ∧ z = t • u' + g}) ↔
      (∀ b ∈ S, dot (expNormal u' vl) a ≤ dot (expNormal u' vl) b) ∧
        (∀ b ∈ S, dot (expDual u' vl) a ≤ dot (expDual u' vl) b) := by
  constructor
  · intro hsub
    by_contra hnot
    refine not_chainFull_succ_subset_genClosure hunimod hb₁ hBα ?_ N hg t₀ hahead hsub
    rw [not_and_or] at hnot
    rcases hnot with h | h <;> push Not at h <;> obtain ⟨b, hb, hlt⟩ := h
    · exact Or.inl ⟨b, Finset.mem_erase.mpr ⟨fun e => by subst e; exact lt_irrefl _ hlt, hb⟩, hlt⟩
    · exact Or.inr ⟨b, Finset.mem_erase.mpr ⟨fun e => by subst e; exact lt_irrefl _ hlt, hb⟩, hlt⟩
  · rintro ⟨hlev, hα⟩
    exact chainFull_succ_subset_genClosure hunimod hb₁ hBα hlev hα N hg t₀

/-! ## §18  Axiom receipts

Deletable block (`section AxiomReceipts` … `end AxiomReceipts`): every headline claim of this
file, checked by the kernel at build time instead of asserted in prose (hard rule 3).  Delete
the section, not the individual lines, if the build output needs to be quieter. -/

section AxiomReceipts

#print axioms one_le_of_hSbox_of_nonCollinear
#print axioms box_and_band_satisfiable_with_2D_S
#print axioms cone_subset_sweptSeed_of_band
#print axioms covers_free_of_band
#print axioms cone_subset_sweptSeed_of_band_singleton
#print axioms det_eq_of_mem_sweptSeed
#print axioms card_le_of_rayIn_sweptSeed
#print axioms not_isRegion_of_subset_sweptSeed
#print axioms no_box_band_cone_region
#print axioms no_band_cone_region_singleton
#print axioms no_box_band_cone_region_nonvacuous
#print axioms not_isRegion_qK
#print axioms case1_sweep_conclusion_of_box_of_cone
#print axioms box_of_cone_route_dead_singleton
#print axioms rayIn_sweptSeed_of_residues
#print axioms card_le_of_residues
#print axioms no_rayIn_cB_seed
#print axioms card_alone_insufficient
#print axioms box_band_cone_region_satisfiable
#print axioms box_band_cone_region_satisfiable_n_eq_one
#print axioms hper_of_hRper
#print axioms hseedR_of_hQR
#print axioms case1_sweep_conclusion_wired
#print axioms hgen_of_hSgen
#print axioms case1_sweep_of_box_of_cone_callsite
#print axioms mem_of_nonneg_real_comb
#print axioms exists_nsmul_add_mem
#print axioms det_eq_pm_one_of_region_subset_cone
#print axioms n_eq_one_and_unimodular_of_cone
#print axioms box_of_cone_route_singleton_needs_unimodular
#print axioms case1_sweep_of_box_of_cone_callsite_BQ
#print axioms band_pigeonhole
#print axioms T_periodOn_of_periodOn_of_ray
#print axioms exists_band_repeat
#print axioms hfin_of_counterexample
#print axioms exists_band_repeat_callsite
#print axioms ladder_line_step
#print axioms ladder_of_seeds
#print axioms periodOn_iUnion_of_cofinal
#print axioms iUnion_levels_eq
#print axioms levels_mono
#print axioms sweep_conclusion_of_cofinal_levels
#print axioms ladder_hwin_witness
#print axioms ladder_hwin_witness_needs_seed
#print axioms agree_on_line_of_ray_of_period
#print axioms periodOn_of_ladder_cover
#print axioms cut_add_u_mem
#print axioms sweep_conclusion_of_cofinal_ladders
#print axioms add_mem_of_rayIn_nsmul
#print axioms rayIn_of_rayIn_nsmul
#print axioms isRegion_of_isRegion_nsmul
#print axioms isRegion_nsmul_of_isRegion
#print axioms sweep_conclusion_wlog_primitive
#print axioms case1_sweep_conclusion_wlog_primitive
#print axioms exists_zsmul_of_dot_perp_eq
#print axioms level_not_coset_of_nonprimitive
#print axioms LevelFrame.ext_dots
#print axioms LevelFrame.add_nsmul_dv_mem
#print axioms exists_levelFrame
#print axioms agree_on_bandSet
#print axioms cover_of_levelLine
#print axioms hwin_of_levelLine
#print axioms exists_vertex
#print axioms latticeConvex_erase_of_vertex
#print axioms exists_generating_vertex
#print axioms sweep_conclusion_of_levelFrame_of_seed_assumed
#print axioms sweep_conclusion_of_generatingSet_of_seed_assumed
#print axioms Nivat.Colle43.agree_T_on_halfStripFrom
#print axioms lineAt
#print axioms stagBase_stagger
#print axioms le_stagBase_zero
#print axioms mono_of_stagger
#print axioms seed_of_block
#print axioms frameBlock_of_hasBlock
#print axioms cover_of_lineAt_down
#print axioms cover_of_lineAt_up
#print axioms hwin_down_of_lineAt
#print axioms hwin_up_of_lineAt
#print axioms exists_vertex_up
#print axioms latticeConvex_erase_of_vertex_up
#print axioms exists_generating_vertex_up
#print axioms halfCut_add_u_mem
#print axioms sweep_conclusion_down_of_lineSeed
#print axioms sweep_conclusion_up_of_lineSeed
#print axioms sweep_conclusion_of_generatingSet_of_lineSeeds
#print axioms sweep_conclusion_of_generatingSet_of_block
#print axioms hasBlock_of_either
#print axioms LevelFrame.dot_n_eq_pm_det
#print axioms Wrow_eq_card_face_sub_one
#print axioms min_Wrow_eq_min_card_face
#print axioms hasBlock_maxB

#print axioms expFrame
#print axioms hwin_corner
#print axioms corner_line_subset_genClosure
#print axioms chainFull_succ_subset_genClosure
#print axioms genClosure_subset_of_exists_dot_lt
#print axioms not_chainFull_succ_subset_genClosure
#print axioms no_corner_vertex_parallelogram

#print axioms expNormal_swap_eq_expDual
#print axioms dot_generic_eq_lex
#print axioms hwin_corner_lex
#print axioms corner_line_subset_genClosure_lex
#print axioms not_chainFull_succ_subset_genClosure_of_lexMin
#print axioms level_le_of_lex_strict_max
#print axioms single_level_of_lex_strict_max_of_hlev
#print axioms expNormal_le_of_generic_strict_max
#print axioms chainFull_succ_subset_genClosure_of_reachback
#print axioms chainFull_succ_subset_genClosure_iff_of_ahead
end AxiomReceipts

end Nivat.L3Band
