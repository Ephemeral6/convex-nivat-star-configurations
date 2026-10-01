/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.LineIndex
import Nivat.External.Colle.L1StraddleWedge
import Nivat.External.Colle.ApexUnique

set_option autoImplicit false

/-!
# `EnvFit` — the cone-fit condition is **equivalent** to `hapex`, and envelopedness cannot help

Lane Wbox's file (exclusive).  Target as dispatched: produce

```
hfit : ∀ w ∈ coneRegion B vl u', ∀ z ∈ S.erase a, z + (w - a) ∈ coneRegion B vl u'
```

from Definition 3.2 envelopedness (`b3_colle2.txt:402`, `:777` "Let `B ⊂ ℤ²` be an
`E(𝒮_φ)`-**enveloped** set").

## 🔴 Result: envelopedness is not the missing ingredient, because there is no missing ingredient

`hfit_iff_hapex` (§3) proves, for **every** finite nonempty `B`, that `hfit` is *equivalent* to

```
hapex : ∀ z ∈ S.erase a, ∃ s t : ℕ, z - a = s•vl + t•u'
```

— the very condition `translate_window_mem_coneRegion` (`LineIndex.lean:46`) already assumes.
So no hypothesis on `B` beyond finiteness and nonemptiness can buy `hfit`: `Enveloped ↑S B`,
`IsLatticeConvexRegion B`, edge-length dominance are all *irrelevant*, since the forward
implication `hfit → hapex` holds without them and `hapex` mentions no `B` at all.

**Why the "switch to another `b' ∈ B`" escape fails** (the dispatch's proposed mechanism).
Write the two dual coordinates of the unimodular basis as `ψ := dot (expNormal u' vl) ·`
(`dot ψ vl = 1`, `dot ψ u' = 0`) and `χ := uCoord u' vl 0 ·` (`χ vl = 0`, `χ u' = 1`).  Then
`mem_coneRegion_iff_coords` (§2) says

```
x ∈ coneRegion B vl u'  ↔  ∃ b ∈ B, ψ b ≤ ψ x ∧ χ b ≤ χ x.
```

The cone is a **union of translated quadrants**, one per `b ∈ B`, and each quadrant opens in
the `+ψ`, `+χ` directions.  Hence `ψ` and `χ` are each bounded below on the whole cone, and
both bounds are *attained on `B` itself* (`B` finite).  Put `w` at the `ψ`-minimiser of `B`:
translating by `z - a` shifts `ψ` by `ψ(z) - ψ(a)`, so landing back in the cone forces
`ψ(z) - ψ(a) ≥ 0`.  Repeat at the `χ`-minimiser.  Those two inequalities *are* `hapex`.
Changing `b'` cannot rescue a negative coordinate, because every `b'` is itself above the
minimum.  Thickness of `B` is the wrong resource: the obstruction is at the cone's **apex
corner**, which no amount of bulk removes.

⚠ This also matches the integrator's own retraction at `LineIndex.lean:147-166`: `hapex`
forces the vertex `a` to be level-**maximal** and the translates to move *down*.  The
dispatch asked for `a` level-**minimal** (`exists_strict_argmin_of_no_edge_parallel`), which
is the extremum that retraction ruled out — with `a` level-minimal, `hapex` fails at once, so
by §3 `hfit` fails too.

## 🟢 What *does* produce the dispatched conclusion: the shear, not envelopedness

`exists_shear_hfit` (§4) delivers the conclusion shape verbatim, unconditionally, for every
nonempty `S`:

```
∃ K, ∃ a ∈ S, ∀ w ∈ coneRegion B vl (u' - K•vl),
                ∀ z ∈ S.erase a, z + (w - a) ∈ coneRegion B vl (u' - K•vl).
```

The input is `L1StraddleWedge.exists_corner_shear` (`:424`), whose two conjuncts are exactly
`ψ'' (z - a) ≥ 0` and `χ'' (z - a) ≥ 0` in the sheared basis — i.e. `hapex` at `u' - K•vl`.
This is the same ruling as the previous round's `hapex` question: the proposition is false at
a *pinned* `u'` and true after a shear, and `u'` is a free data field of `WedgeResidualR`
(`L1Claim.lean:930`) whose only constraint `hunimod` is shear-invariant (`det_shear_right`).

**原文对应**：`coneRegion` = `𝓡_{ι-1}` (`b3_colle2.txt:780`); the translation of `𝒮_{φ_ι}` so
that its extreme vertex sits at `w` is `:794-798` (Figure 10); `hapex` ↔ "every other point
falls inside the cone" of the same passage.  No quantifier here is ours: §3 and §4 are
theorems about the *existing* `coneRegion`/`hapex` pair, and introduce no new `Prop`.
-/

namespace Nivat.EnvFit

open Nivat Nivat.LE2 Nivat.ColleReg Nivat.ConeRegion Nivat.L1Line0

variable {u' vl : ℤ × ℤ}

/-! ## §1  The two dual coordinates of the unimodular basis `(vl, u')` -/

/-- `ψ := dot (expNormal u' vl) ·` reads off the `vl`-coordinate: it is `1` on `vl` and `0`
on `u'`, so a cone point `b + s•vl + t•u'` has `ψ = ψ b + s`. -/
theorem dot_expNormal_add (hunimod : det u' vl = 1 ∨ det u' vl = -1) (b : ℤ × ℤ) (s t : ℤ) :
    dot (expNormal u' vl) (b + s • vl + t • u') = dot (expNormal u' vl) b + s := by
  rw [dot_add, dot_add, dot_zsmul, dot_zsmul, Nivat.ColleReg.dot_expNormal_vl hunimod,
    Nivat.ColleReg.dot_expNormal_u']
  ring

/-- `χ := uCoord u' vl 0 ·` is additive. -/
theorem uCoord_zero_add_hom (x y : ℤ × ℤ) :
    uCoord u' vl 0 (x + y) = uCoord u' vl 0 x + uCoord u' vl 0 y := by
  simp only [uCoord, det, Prod.fst_add, Prod.snd_add, sub_zero]
  ring

/-- `χ := uCoord u' vl 0 ·` respects subtraction. -/
theorem uCoord_zero_sub_hom (x y : ℤ × ℤ) :
    uCoord u' vl 0 (x - y) = uCoord u' vl 0 x - uCoord u' vl 0 y := by
  simp only [uCoord, det, Prod.fst_sub, Prod.snd_sub, sub_zero]
  ring

/-- `χ` reads off the `u'`-coordinate: it is `0` on `vl` and `1` on `u'` (the latter needs
unimodularity), so a cone point `b + s•vl + t•u'` has `χ = χ b + t`. -/
theorem uCoord_zero_add (hunimod : det u' vl = 1 ∨ det u' vl = -1) (b : ℤ × ℤ) (s t : ℤ) :
    uCoord u' vl 0 (b + s • vl + t • u') = uCoord u' vl 0 b + t := by
  have hsq := det_sq hunimod
  simp only [uCoord, det, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul, sub_zero] at hsq ⊢
  linear_combination t * hsq

/-- **The coordinate decomposition.**  Every `z` is `b₀` plus its two coordinate differences,
with no existential left: `z = b₀ + (ψ z − ψ b₀)•vl + (χ z − χ b₀)•u'`.  This is
`L1Line0.exists_decomp` with both coefficients identified. -/
theorem eq_add_coords (hunimod : det u' vl = 1 ∨ det u' vl = -1) (b₀ z : ℤ × ℤ) :
    z = b₀ + (dot (expNormal u' vl) z - dot (expNormal u' vl) b₀) • vl
          + (uCoord u' vl 0 z - uCoord u' vl 0 b₀) • u' := by
  obtain ⟨A, C, hz, -⟩ := exists_decomp hunimod b₀ z
  have hA : dot (expNormal u' vl) z = dot (expNormal u' vl) b₀ + A := by
    rw [hz, dot_expNormal_add hunimod]
  have hC : uCoord u' vl 0 z = uCoord u' vl 0 b₀ + C := by
    rw [hz, uCoord_zero_add hunimod]
  have h1 : dot (expNormal u' vl) z - dot (expNormal u' vl) b₀ = A := by omega
  have h2 : uCoord u' vl 0 z - uCoord u' vl 0 b₀ = C := by omega
  rw [h1, h2]
  exact hz

/-- Left-associated `a + X + Y` shifted to a difference.  Stated with `X`, `Y` opaque so that
the rewrite cannot loop when they mention `z` (the self-referential-`rw` trap). -/
theorem sub_eq_of_eq_add {a z X Y : ℤ × ℤ} (h : z = a + X + Y) : z - a = X + Y := by
  rw [h]; abel

/-- The shear `u' ↦ u' − K•vl` does not move the determinant, so `hunimod` transfers. -/
theorem det_shear_right (K : ℤ) : det (u' - K • vl) vl = det u' vl := by
  simp only [det, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-! ## §2  The cone in coordinates: a union of quadrants -/

/-- **Coordinate membership criterion for the cone.**

`x ∈ coneRegion B vl u'` iff some `b ∈ B` is below `x` in *both* dual coordinates.  This is
the exact sense in which `𝓡_{ι-1}` (`b3_colle2.txt:780`) is a union of translated quadrants,
and it is the lemma that makes §3 possible: the `∃ b` is over a set on which each coordinate
attains a minimum, so neither coordinate can be pushed below that minimum by any choice of
base point. -/
theorem mem_coneRegion_iff_coords {B : Set (ℤ × ℤ)}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) {z : ℤ × ℤ} :
    z ∈ coneRegion B vl u' ↔
      ∃ b ∈ B, dot (expNormal u' vl) b ≤ dot (expNormal u' vl) z ∧
        uCoord u' vl 0 b ≤ uCoord u' vl 0 z := by
  rw [mem_coneRegion_iff]
  constructor
  · rintro ⟨b, hb, s, t, rfl⟩
    refine ⟨b, hb, ?_, ?_⟩
    · have hs : (0 : ℤ) ≤ (s : ℤ) := Int.natCast_nonneg s
      rw [dot_expNormal_add hunimod]
      omega
    · have ht : (0 : ℤ) ≤ (t : ℤ) := Int.natCast_nonneg t
      rw [uCoord_zero_add hunimod]
      omega
  · rintro ⟨b, hb, h1, h2⟩
    refine ⟨b, hb, (dot (expNormal u' vl) z - dot (expNormal u' vl) b).toNat,
      (uCoord u' vl 0 z - uCoord u' vl 0 b).toNat, ?_⟩
    rw [Int.toNat_of_nonneg (by omega : (0:ℤ) ≤ dot (expNormal u' vl) z -
        dot (expNormal u' vl) b),
      Int.toNat_of_nonneg (by omega : (0:ℤ) ≤ uCoord u' vl 0 z - uCoord u' vl 0 b)]
    exact eq_add_coords hunimod b z

/-! ## §3  `hfit ↔ hapex`: envelopedness is irrelevant -/

/-- **The refutation of the envelopedness route.**  `hfit → hapex`, for *every* finite
nonempty `B` — no `Enveloped`, no `IsLatticeConvexRegion`, no edge-length hypothesis.

Take `w` at the `ψ`-minimiser of `B`.  By `hfit`, `z + (w - a)` is back in the cone, so by
`mem_coneRegion_iff_coords` some `b ∈ B` has `ψ b ≤ ψ z + ψ w - ψ a`; but `ψ w ≤ ψ b` by
minimality, whence `ψ z - ψ a ≥ 0`.  The `χ`-minimiser gives `χ z - χ a ≥ 0` the same way.
`eq_add_coords` turns the two inequalities into `z - a = s•vl + t•u'` with `s t : ℕ`.

**Consequence.**  Any hypothesis `H` on `B` that does not already imply `hapex` (which
mentions no `B`) cannot produce `hfit`.  Definition 3.2 envelopedness (`:402`) is such an
`H`, so the `:777` "`B` is `E(𝒮_φ)`-enveloped" reading cannot be what closes this. -/
theorem hapex_of_hfit {B : Set (ℤ × ℤ)} {S : Finset (ℤ × ℤ)} {a : ℤ × ℤ}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) (hBfin : B.Finite) (hBne : B.Nonempty)
    (hfit : ∀ w ∈ coneRegion B vl u', ∀ z ∈ S.erase a,
      z + (w - a) ∈ coneRegion B vl u') :
    ∀ z ∈ S.erase a, ∃ s t : ℕ, z - a = (s : ℤ) • vl + (t : ℤ) • u' := by
  classical
  obtain ⟨b₀, hb₀⟩ := hBne
  have hFne : (hBfin.toFinset).Nonempty := ⟨b₀, hBfin.mem_toFinset.mpr hb₀⟩
  obtain ⟨bψ, hbψF, hbψmin⟩ :=
    hBfin.toFinset.exists_min_image (fun x => dot (expNormal u' vl) x) hFne
  obtain ⟨bχ, hbχF, hbχmin⟩ :=
    hBfin.toFinset.exists_min_image (fun x => uCoord u' vl 0 x) hFne
  have hbψ : bψ ∈ B := hBfin.mem_toFinset.mp hbψF
  have hbχ : bχ ∈ B := hBfin.mem_toFinset.mp hbχF
  intro z hz
  have hσ : 0 ≤ dot (expNormal u' vl) z - dot (expNormal u' vl) a := by
    have hw : bψ ∈ coneRegion B vl u' :=
      mem_coneRegion_iff.mpr ⟨bψ, hbψ, 0, 0, by simp⟩
    obtain ⟨b, hb, h1, -⟩ := (mem_coneRegion_iff_coords hunimod).mp (hfit bψ hw z hz)
    have hmin : dot (expNormal u' vl) bψ ≤ dot (expNormal u' vl) b :=
      hbψmin b (hBfin.mem_toFinset.mpr hb)
    have hval : dot (expNormal u' vl) (z + (bψ - a)) =
        dot (expNormal u' vl) z + (dot (expNormal u' vl) bψ - dot (expNormal u' vl) a) := by
      rw [dot_add, dot_sub]
    rw [hval] at h1
    omega
  have hτ : 0 ≤ uCoord u' vl 0 z - uCoord u' vl 0 a := by
    have hw : bχ ∈ coneRegion B vl u' :=
      mem_coneRegion_iff.mpr ⟨bχ, hbχ, 0, 0, by simp⟩
    obtain ⟨b, hb, -, h2⟩ := (mem_coneRegion_iff_coords hunimod).mp (hfit bχ hw z hz)
    have hmin : uCoord u' vl 0 bχ ≤ uCoord u' vl 0 b :=
      hbχmin b (hBfin.mem_toFinset.mpr hb)
    have hval : uCoord u' vl 0 (z + (bχ - a)) =
        uCoord u' vl 0 z + (uCoord u' vl 0 bχ - uCoord u' vl 0 a) := by
      rw [uCoord_zero_add_hom, uCoord_zero_sub_hom]
    rw [hval] at h2
    omega
  refine ⟨(dot (expNormal u' vl) z - dot (expNormal u' vl) a).toNat,
    (uCoord u' vl 0 z - uCoord u' vl 0 a).toNat, ?_⟩
  rw [Int.toNat_of_nonneg hσ, Int.toNat_of_nonneg hτ]
  exact sub_eq_of_eq_add (eq_add_coords hunimod a z)

/-- **The easy direction**, `hapex → hfit`: `LineIndex.translate_window_mem_coneRegion`
(`:46`) with the `∀ w` moved to the front.  Holds for every `B`, finite or not. -/
theorem hfit_of_hapex {B : Set (ℤ × ℤ)} {S : Finset (ℤ × ℤ)} {a : ℤ × ℤ}
    (hapex : ∀ z ∈ S.erase a, ∃ s t : ℕ, z - a = (s : ℤ) • vl + (t : ℤ) • u') :
    ∀ w ∈ coneRegion B vl u', ∀ z ∈ S.erase a, z + (w - a) ∈ coneRegion B vl u' :=
  fun _ hw => Nivat.LE2.translate_window_mem_coneRegion hapex hw

/-- **`hfit ↔ hapex`.**  The dispatched goal is not a weakening of `hapex`; it is `hapex`.

Read this together with `Nivat.ApexUnique.not_exists_apex_of_no_edge_parallel`
(`ApexUnique.lean:256`), which exhibits a lattice-convex `S` admitting **no** apex at a pinned
`(vl, u')`: for that `S`, `hfit` is false at every `a` and every finite nonempty `B`.

**`:798` is two claims, and only one of them is this one.**  The sentence at `b3_colle2.txt:796`
— "the knowledge of `T^u η` on `H_B(ℓ)` determines uniquely `T^u η` on `A₁`" — is a
*determination* claim, and it is generating-set, not geometric: it is the `IsGeneratingSet`
binder of `SweepLines.hbase_at_of_sweep_lines`, and nothing here bears on it.  What Figure 10
(`:794-798`) additionally asserts is a *placement*: all but one point of the translated
`𝒮_{φ_ι}` must already lie in the known region.  That second claim is `hwinL` and nothing else,
and it is the one this file is about.  So envelopedness cannot be ruled out by observing that
`:798` is a generating-set argument — if it enters, it enters on the placement side, which is
precisely where §3 shows it is powerless and §6–§9 show the level restriction relocates the
obligation to `hstrip`. -/
theorem hfit_iff_hapex {B : Set (ℤ × ℤ)} {S : Finset (ℤ × ℤ)} {a : ℤ × ℤ}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) (hBfin : B.Finite) (hBne : B.Nonempty) :
    (∀ w ∈ coneRegion B vl u', ∀ z ∈ S.erase a, z + (w - a) ∈ coneRegion B vl u') ↔
      (∀ z ∈ S.erase a, ∃ s t : ℕ, z - a = (s : ℤ) • vl + (t : ℤ) • u') :=
  ⟨hapex_of_hfit hunimod hBfin hBne, hfit_of_hapex⟩

/-! ## §3.5  The refutation made concrete, on a named witness -/

/-- **A seed with no apex has no `hfit` either**, at any finite nonempty `B`.  Contrapositive
of `hapex_of_hfit`, packaged so that an existing `¬ ∃ a, hapex` witness composes directly. -/
theorem not_exists_hfit_of_not_exists_hapex {B : Set (ℤ × ℤ)} {S : Finset (ℤ × ℤ)}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) (hBfin : B.Finite) (hBne : B.Nonempty)
    (hno : ¬ ∃ a ∈ S, ∀ z ∈ S.erase a, ∃ s t : ℕ, z - a = (s : ℤ) • vl + (t : ℤ) • u') :
    ¬ ∃ a ∈ S, ∀ w ∈ coneRegion B vl u', ∀ z ∈ S.erase a,
        z + (w - a) ∈ coneRegion B vl u' := by
  rintro ⟨a, ha, hfit⟩
  exact hno ⟨a, ha, hapex_of_hfit hunimod hBfin hBne hfit⟩

/-- **`hfit` is false on a named witness, at a pinned unimodular basis.**

`S = Sap = {(0,0), (-1,1), (-1,2)}`, `vl = (1,0)`, `u' = (0,1)`, `B = {(0,0)}`.  Every
hypothesis of the refuted statement is discharged in the kernel on this witness
(`PROTOCOL.md` §7): `S` is nonempty, lattice-convex and of positive area, `det u' vl = -1`,
`B` is finite and nonempty, and Lemma 2.6's conclusion `hno` (`b3_colle2.txt:792`, no edge
parallel to `±ℓ`) holds — all inherited from
`Nivat.ApexUnique.not_exists_apex_of_no_edge_parallel` (`ApexUnique.lean:256`), where they
are each proved, `hstrict` included.

So the dispatched `hfit` is not merely unproved from envelopedness: it is **false** for a
seed satisfying every geometric hypothesis the paper puts on `𝒮_{φ_ι}` at that basis.  What
rescues it is the shear (§4), not a hypothesis on `B`. -/
theorem not_exists_hfit_pinned :
    ∃ (S : Finset (ℤ × ℤ)) (vl u' : ℤ × ℤ) (B : Set (ℤ × ℤ)),
      S.Nonempty ∧ LatticeConvex S ∧ PosArea (↑S : Set (ℤ × ℤ)) ∧
      det u' vl = -1 ∧ B.Finite ∧ B.Nonempty ∧
      (∀ n ∈ E (↑S : Set (ℤ × ℤ)), dot n vl ≠ 0) ∧
      ¬ ∃ a ∈ S, ∀ w ∈ coneRegion B vl u', ∀ z ∈ S.erase a,
          z + (w - a) ∈ coneRegion B vl u' := by
  obtain ⟨S, vl, u', m, hne, hlc, harea, -, -, -, hdet, -, -, hno, -, hnoapex⟩ :=
    Nivat.ApexUnique.not_exists_apex_of_no_edge_parallel
  exact ⟨S, vl, u', {(0, 0)}, hne, hlc, harea, hdet, Set.finite_singleton _,
    Set.singleton_nonempty _, hno,
    not_exists_hfit_of_not_exists_hapex (Or.inr hdet) (Set.finite_singleton _)
      (Set.singleton_nonempty _) hnoapex⟩

/-! ## §4  The dispatched conclusion, produced — by the shear -/

/-- **`hapex` at the sheared `u'`, unconditionally.**  `exists_corner_shear`'s two conjuncts
are precisely `ψ''(z - a) ≥ 0` and `χ''(z - a) ≥ 0` in the basis `(vl, u' - K•vl)`; by
`eq_add_coords` that is `hapex`. -/
theorem exists_shear_hapex {S : Finset (ℤ × ℤ)} (hS : S.Nonempty)
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) :
    ∃ K : ℤ, ∃ a ∈ S, ∀ z ∈ S.erase a,
      ∃ s t : ℕ, z - a = (s : ℤ) • vl + (t : ℤ) • (u' - K • vl) := by
  obtain ⟨K, a, ha, hc⟩ := Nivat.L1StraddleWedge.exists_corner_shear (u' := u') (vl := vl) hS
  have hu'' : det (u' - K • vl) vl = 1 ∨ det (u' - K • vl) vl = -1 := by
    rw [det_shear_right]; exact hunimod
  refine ⟨K, a, ha, fun z hz => ?_⟩
  obtain ⟨h1, h2⟩ := hc z (Finset.mem_erase.mp hz).2
  refine ⟨(dot (expNormal (u' - K • vl) vl) (z - a)).toNat,
    (uCoord (u' - K • vl) vl a z).toNat, ?_⟩
  rw [Int.toNat_of_nonneg h1, Int.toNat_of_nonneg h2,
    dot_sub, Nivat.L1StraddleWedge.uCoord_eq_sub a z]
  exact sub_eq_of_eq_add (eq_add_coords hu'' a z)

/-- **The dispatched conclusion, verbatim, at the sheared `u'`.**

For every nonempty `S` and every `B` whatsoever:
`∃ K, ∃ a ∈ S, ∀ w ∈ coneRegion B vl (u' − K•vl), ∀ z ∈ S.erase a,
  z + (w − a) ∈ coneRegion B vl (u' − K•vl)`.

No hypothesis on `B` at all — not finiteness, not envelopedness.  This is the producer the
dispatch was looking for; it just is not the one the dispatch proposed.  `u'` is free data
(`L1Claim.lean:930`) constrained only by `hunimod`, which `det_shear_right` shows the shear
preserves, so a consumer may take the sheared `u'` as its own. -/
theorem exists_shear_hfit {B : Set (ℤ × ℤ)} {S : Finset (ℤ × ℤ)} (hS : S.Nonempty)
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) :
    ∃ K : ℤ, ∃ a ∈ S, ∀ w ∈ coneRegion B vl (u' - K • vl), ∀ z ∈ S.erase a,
      z + (w - a) ∈ coneRegion B vl (u' - K • vl) := by
  obtain ⟨K, a, ha, hapex⟩ := exists_shear_hapex (u' := u') (vl := vl) hS hunimod
  exact ⟨K, a, ha, hfit_of_hapex hapex⟩

/-! ## §5  The level functional `nℓ` of the line `ℓ`, in the same two coordinates

原文：b3_colle2.txt:414 — `H_B(ℓ) := {g + t·v⃗_ℓ : g ∈ B, t ∈ ℤ_+}`.  Since `v⃗_ℓ` spans `ℓ`,
the normal `nℓ` kills it, so the half-strip occupies exactly the `nℓ`-levels of `B`; the
consumer's `cz` is the bottom of that band and `ctop = suppVal B nℓ` its top.

The point of this section is that `nℓ` is **not a third coordinate**: in the unimodular basis
`(vl, u')` with `dot nℓ vl = 0` and `dot nℓ u' = -1` — the exact normalisation
`ApexUnique.not_exists_apex_of_no_edge_parallel` already carries — one has `dot nℓ = -χ`
identically.  Every level statement below is therefore a statement about `χ` alone, and the
`ψ`/`χ` split of §2 applies verbatim. -/

/-- **`nℓ` is `−χ`.**  A covector vanishing on `vl` and taking `-1` on `u'` is determined on
all of `ℤ²` once `(vl, u')` is a basis, and `χ = uCoord u' vl 0 ·` is the dual coordinate of
`u'`.  No finiteness, no hypothesis on `B`. -/
theorem dot_eq_neg_uCoord {nℓ : ℤ × ℤ} (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hnvl : dot nℓ vl = 0) (hnu : dot nℓ u' = -1) (x : ℤ × ℤ) :
    dot nℓ x = - uCoord u' vl 0 x := by
  obtain ⟨A, C, hx, hC⟩ := exists_decomp hunimod (0 : ℤ × ℤ) x
  rw [← hC, hx, dot_add, dot_add, dot_zsmul, dot_zsmul, hnvl, hnu]
  simp [dot]

/-- **The level restriction never empties the hypothesis set.**  For *every* threshold `c` the
cone contains points strictly below it, obtained by pushing any `b ∈ B` along `u'` (which
lowers `dot nℓ` by one per step, since `dot nℓ u' = -1`).

This is what makes §6 and §8 refutations rather than vacuities: `hcone`/`hstrip` are
quantified over a nonempty set of `w`, and `PROTOCOL.md` §7 is satisfied on that side too. -/
theorem exists_mem_coneRegion_dot_lt {B : Set (ℤ × ℤ)} {nℓ : ℤ × ℤ}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hnvl : dot nℓ vl = 0) (hnu : dot nℓ u' = -1) (hBne : B.Nonempty) (c : ℤ) :
    ∃ w ∈ coneRegion B vl u', dot nℓ w < c := by
  have hχ : ∀ x : ℤ × ℤ, dot nℓ x = - uCoord u' vl 0 x :=
    dot_eq_neg_uCoord hunimod hnvl hnu
  obtain ⟨b, hb⟩ := hBne
  set t : ℕ := (-c + 1 - uCoord u' vl 0 b).toNat with htdef
  refine ⟨b + (0 : ℤ) • vl + (t : ℤ) • u', mem_coneRegion_iff.mpr ⟨b, hb, 0, t, rfl⟩, ?_⟩
  rw [hχ, uCoord_zero_add hunimod]
  omega

/-! ## §6  `hcone` under the level restriction: exactly the `ψ`-half of `hapex`

The consumer never applies the residual at an arbitrary `w`: it applies it at `w` **strictly
below the known strip**, `dot nℓ w < cz`.  That restriction excludes every point of `B`
(each has `dot nℓ b ≥ cz`), hence excludes the `ψ`- and `χ`-minimisers of `B` that
`hapex_of_hfit` (§3) used as its two test points.  So §3 does **not** apply, and the question
is genuinely reopened.

Answer: **half of it survives, and exactly half.**  The `ψ`-minimiser can be pushed up along
`u'` — which changes `χ` without changing `ψ` — until it is admissible, so the `ψ` argument
of §3 goes through unchanged.  The `χ` argument does not: pushing `w` up in `χ` also relaxes
the `χ`-constraint on the translate by the same amount, and the two cancel. -/

/-- **The easy half of §6**, and the one with no hypothesis on `B` whatsoever: if the seed is
`ψ`-dominated by `a`, the restricted `hcone` holds.

The proof is the cancellation just described: the base point `b` witnessing `w ∈ coneRegion`
witnesses the translate too, because its `χ`-obligation is discharged by the level hypothesis
`dot nℓ (z + (w - a)) < cz` rather than by anything about `z`. -/
theorem hcone_of_psi_nonneg {B : Set (ℤ × ℤ)} {S : Finset (ℤ × ℤ)} {a nℓ : ℤ × ℤ} {cz : ℤ}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hnvl : dot nℓ vl = 0) (hnu : dot nℓ u' = -1)
    (hcz : ∀ b ∈ B, cz ≤ dot nℓ b)
    (hψ : ∀ z ∈ S.erase a, 0 ≤ dot (expNormal u' vl) (z - a)) :
    ∀ w ∈ coneRegion B vl u', dot nℓ w < cz → ∀ z ∈ S.erase a,
      dot nℓ (z + (w - a)) < cz → z + (w - a) ∈ coneRegion B vl u' := by
  intro w hw _ z hz hlow2
  have hχ : ∀ x : ℤ × ℤ, dot nℓ x = - uCoord u' vl 0 x :=
    dot_eq_neg_uCoord hunimod hnvl hnu
  obtain ⟨b, hb, h1, -⟩ := (mem_coneRegion_iff_coords hunimod).mp hw
  refine (mem_coneRegion_iff_coords hunimod).mpr ⟨b, hb, ?_, ?_⟩
  · have hzd := hψ z hz
    rw [dot_sub] at hzd
    have hval : dot (expNormal u' vl) (z + (w - a)) =
        dot (expNormal u' vl) z + (dot (expNormal u' vl) w - dot (expNormal u' vl) a) := by
      rw [dot_add, dot_sub]
    omega
  · have hbb := hcz b hb
    rw [hχ b] at hbb
    have hval := hχ (z + (w - a))
    omega

/-- **The restricted `hcone` is *equivalent* to `0 ≤ ψ(z − a)` on the seed.**

原文：b3_colle2.txt:780 (`𝓡_{ι-1}`), `:796` (the translate of Figure 10).  Quantifier
correspondence: `w` ↔ the point of `𝓡_{ι-1}` being conquered, `z` ↔ the other points of
`𝒮_{φ_ι}`, `cz` ↔ the bottom level of `H_B(ℓ)` (`:414`).

**Reading (this is the answer to "does the equivalence survive").**  It does not.  §3's
`hfit ↔ hapex` had `hapex` on the right: *both* coordinates nonnegative.  Under the level
restriction only the `ψ` coordinate is forced.  And since the right-hand side mentions no
`B` at all, the conclusion of §3 survives in the form that matters: **envelopedness still
cannot help `hcone`** — but it no longer needs to, because §7 satisfies `hcone`
unconditionally. -/
theorem hcone_iff_psi_nonneg {B : Set (ℤ × ℤ)} {S : Finset (ℤ × ℤ)} {a nℓ : ℤ × ℤ} {cz : ℤ}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hBfin : B.Finite) (hBne : B.Nonempty)
    (hnvl : dot nℓ vl = 0) (hnu : dot nℓ u' = -1)
    (hcz : ∀ b ∈ B, cz ≤ dot nℓ b) :
    (∀ w ∈ coneRegion B vl u', dot nℓ w < cz → ∀ z ∈ S.erase a,
        dot nℓ (z + (w - a)) < cz → z + (w - a) ∈ coneRegion B vl u') ↔
      (∀ z ∈ S.erase a, 0 ≤ dot (expNormal u' vl) (z - a)) := by
  classical
  refine ⟨?_, hcone_of_psi_nonneg hunimod hnvl hnu hcz⟩
  intro hcone z hz
  have hχ : ∀ x : ℤ × ℤ, dot nℓ x = - uCoord u' vl 0 x :=
    dot_eq_neg_uCoord hunimod hnvl hnu
  obtain ⟨b₀, hb₀⟩ := hBne
  have hFne : (hBfin.toFinset).Nonempty := ⟨b₀, hBfin.mem_toFinset.mpr hb₀⟩
  obtain ⟨bψ, hbψF, hbψmin⟩ :=
    hBfin.toFinset.exists_min_image (fun x => dot (expNormal u' vl) x) hFne
  have hbψ : bψ ∈ B := hBfin.mem_toFinset.mp hbψF
  have hbψtop : uCoord u' vl 0 bψ ≤ -cz := by
    have := hcz bψ hbψ; rw [hχ bψ] at this; omega
  -- `D` is the `χ`-defect of `z` relative to `a`; `t` pushes `w` past it along `u'`.
  set D : ℤ := uCoord u' vl 0 z - uCoord u' vl 0 a with hDdef
  set t : ℕ := (-cz + 1 - uCoord u' vl 0 bψ + (-D).toNat).toNat with htdef
  have htval : (t : ℤ) = -cz + 1 - uCoord u' vl 0 bψ + (-D).toNat := by
    rw [htdef]; omega
  set w : ℤ × ℤ := bψ + (0 : ℤ) • vl + (t : ℤ) • u' with hwdef
  have hwcone : w ∈ coneRegion B vl u' := by
    rw [hwdef, mem_coneRegion_iff]
    exact ⟨bψ, hbψ, 0, t, by push_cast; ring_nf⟩
  have hwχ : uCoord u' vl 0 w = uCoord u' vl 0 bψ + (t : ℤ) := by
    rw [hwdef, uCoord_zero_add hunimod]
  have hwψ : dot (expNormal u' vl) w = dot (expNormal u' vl) bψ := by
    rw [hwdef, dot_expNormal_add hunimod]; ring
  have hwlow : dot nℓ w < cz := by rw [hχ w]; omega
  have hχt : uCoord u' vl 0 (z + (w - a)) = D + uCoord u' vl 0 w := by
    rw [uCoord_zero_add_hom, uCoord_zero_sub_hom, hDdef]; ring
  have hDt : 0 ≤ D + ((-D).toNat : ℤ) := by omega
  have hlow2 : dot nℓ (z + (w - a)) < cz := by rw [hχ, hχt]; omega
  obtain ⟨b, hb, h1, -⟩ :=
    (mem_coneRegion_iff_coords hunimod).mp (hcone w hwcone hwlow z hz hlow2)
  have hmin : dot (expNormal u' vl) bψ ≤ dot (expNormal u' vl) b :=
    hbψmin b (hBfin.mem_toFinset.mpr hb)
  have hval : dot (expNormal u' vl) (z + (w - a)) =
      dot (expNormal u' vl) z + (dot (expNormal u' vl) bψ - dot (expNormal u' vl) a) := by
    rw [dot_add, dot_sub, hwψ]
  rw [hval] at h1
  rw [dot_sub]
  omega

/-! ## §7  `hcone` is free: it holds at the `ψ`-minimal vertex of the seed -/

/-- **There is always an `a` for which the restricted `hcone` holds** — at *every* `B`, with
no finiteness, no convexity and no envelopedness, and with no shear.

Take `a` to be a `ψ`-minimal point of `S`; then `0 ≤ ψ(z − a)` for every `z ∈ S` by
minimality, and `hcone_of_psi_nonneg` applies.  Contrast §4, where producing the *unrestricted*
`hfit` needed the shear `u' ↦ u' − K•vl`: under the level restriction even that is unnecessary,
because only one of the two coordinates is constrained.

⚠ **This does not say the leaf is closed.**  The consumer needs *one* `a` serving `hcone`,
`hstrip` and the sweep's own level-minimality at once; §8–§9 say what the other two cost. -/
theorem exists_hcone {B : Set (ℤ × ℤ)} {S : Finset (ℤ × ℤ)} {nℓ : ℤ × ℤ} {cz : ℤ}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) (hS : S.Nonempty)
    (hnvl : dot nℓ vl = 0) (hnu : dot nℓ u' = -1)
    (hcz : ∀ b ∈ B, cz ≤ dot nℓ b) :
    ∃ a ∈ S, ∀ w ∈ coneRegion B vl u', dot nℓ w < cz → ∀ z ∈ S.erase a,
      dot nℓ (z + (w - a)) < cz → z + (w - a) ∈ coneRegion B vl u' := by
  classical
  obtain ⟨a, haS, hamin⟩ := S.exists_min_image (fun x => dot (expNormal u' vl) x) hS
  refine ⟨a, haS, hcone_of_psi_nonneg hunimod hnvl hnu hcz ?_⟩
  intro z hz
  have := hamin z (Finset.mem_of_mem_erase hz)
  rw [dot_sub]
  omega

/-! ## §8  The answer, on a named witness: the equivalence does **not** survive -/

/-- **`hcone` (restricted) does not imply `hapex`, at any `B`.**

Witness `S = Sap = {(0,0), (-1,1), (-1,2)}`, `vl = (1,0)`, `u' = (0,1)`, `nℓ = (0,-1)` —
the same seed on which `ApexUnique.not_exists_apex_of_no_edge_parallel` (`ApexUnique.lean:256`)
shows **no** point of `S` is an apex.  Every hypothesis the refuted implication could carry on
the seed side is discharged there in the kernel (`PROTOCOL.md` §7): nonempty, `LatticeConvex`,
`PosArea`, `det u' vl = -1`, `dot nℓ vl = 0`, `dot nℓ u' = -1`, and Lemma 2.6's conclusion
`∀ n ∈ E S, dot n vl ≠ 0` (`b3_colle2.txt:792`).

On the `B` side nothing is discharged because **nothing is assumed**: the `hcone` clause below
is universally quantified over `B` and over every valid bottom level `cz`.  In particular the
witness is not a singleton-`B` artefact — it holds for the enveloped, lattice-convex,
positive-area `B` of the intended application just as it does for any other. -/
theorem not_hapex_of_hcone :
    ∃ (S : Finset (ℤ × ℤ)) (vl u' nℓ : ℤ × ℤ),
      S.Nonempty ∧ LatticeConvex S ∧ PosArea (↑S : Set (ℤ × ℤ)) ∧
      det u' vl = -1 ∧ dot nℓ vl = 0 ∧ dot nℓ u' = -1 ∧
      (∀ n ∈ E (↑S : Set (ℤ × ℤ)), dot n vl ≠ 0) ∧
      (∀ (B : Set (ℤ × ℤ)) (cz : ℤ), (∀ b ∈ B, cz ≤ dot nℓ b) →
        ∃ a ∈ S, ∀ w ∈ coneRegion B vl u', dot nℓ w < cz → ∀ z ∈ S.erase a,
          dot nℓ (z + (w - a)) < cz → z + (w - a) ∈ coneRegion B vl u') ∧
      ¬ ∃ a ∈ S, ∀ z ∈ S.erase a, ∃ s t : ℕ, z - a = (s : ℤ) • vl + (t : ℤ) • u' := by
  obtain ⟨S, vl, u', nℓ, hne, hlc, harea, -, -, -, hdet, hnvl, hnu, hno, -, hnoapex⟩ :=
    Nivat.ApexUnique.not_exists_apex_of_no_edge_parallel
  exact ⟨S, vl, u', nℓ, hne, hlc, harea, hdet, hnvl, hnu, hno,
    fun B cz hcz => exists_hcone (B := B) (Or.inr hdet) hne hnvl hnu hcz, hnoapex⟩

/-! ## §9  `hstrip`: the whole remaining obligation, as an explicit condition on `B`

`hstrip` is the *other* branch of the same case split — the translate lands at or above the
bottom of the known strip, and must then be in `H_B(ℓ)` itself (`:414`).  Unlike `hcone` it is
a genuine condition on `B`, and §9 computes exactly which one.

Note first that `hstrip` is **vacuous when `hapex` holds at `a`**: its two level hypotheses are
`χ(w) > −cz` and `χ(z−a) + χ(w) ≤ −cz`, which together force `χ(z−a) < 0`.  So all of its
content lives precisely where `hapex` fails, and it is the exact price of dropping the `χ`-half
that §6 showed `hcone` no longer pays. -/

/-- Membership in the half-strip, in the two dual coordinates: `x ∈ H_B(ℓ)` iff some `b ∈ B`
sits at the **same `χ`-level** as `x` and no further along `vl`.  The `ψ` inequality is the
`t ∈ ℤ_+` of `:414`; the `χ` equality is `dot nℓ vl = 0`. -/
theorem mem_halfStrip_iff_coords {B : Set (ℤ × ℤ)}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) {x : ℤ × ℤ} :
    x ∈ Nivat.LE2.halfStrip B vl ↔
      ∃ b ∈ B, uCoord u' vl 0 b = uCoord u' vl 0 x ∧
        dot (expNormal u' vl) b ≤ dot (expNormal u' vl) x := by
  constructor
  · rintro ⟨b, hb, s, rfl⟩
    have hrw : b + (s : ℤ) • vl = b + (s : ℤ) • vl + (0 : ℤ) • u' := by simp
    refine ⟨b, hb, ?_, ?_⟩
    · rw [hrw, uCoord_zero_add hunimod]; ring
    · rw [hrw, dot_expNormal_add hunimod]
      have : (0 : ℤ) ≤ (s : ℤ) := Int.natCast_nonneg s
      omega
  · rintro ⟨b, hb, h1, h2⟩
    refine ⟨b, hb, (dot (expNormal u' vl) x - dot (expNormal u' vl) b).toNat, ?_⟩
    rw [Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ dot (expNormal u' vl) x -
      dot (expNormal u' vl) b)]
    have hzero : uCoord u' vl 0 x - uCoord u' vl 0 b = 0 := by omega
    calc x = b + (dot (expNormal u' vl) x - dot (expNormal u' vl) b) • vl
              + (uCoord u' vl 0 x - uCoord u' vl 0 b) • u' := eq_add_coords hunimod b x
      _ = b + (dot (expNormal u' vl) x - dot (expNormal u' vl) b) • vl := by
            rw [hzero]; simp

/-- **`hstrip`, in closed form.**

With `bψ` a `ψ`-minimal point of `B`, the restricted `hstrip` at `a` is *equivalent* to:

> for each seed point `z` and each level `lev` in the window
> `(−cz + χ(z−a), −cz]`, the set `B` contains a point `g` at level `lev`
> whose `ψ` is at most `ψ(z−a) + ψ(bψ)`.

Both quantifiers are forced: the window's width is `−χ(z−a) = dot nℓ (z − a)`, the amount by
which `z` hangs below `a`, and the `ψ` bound is attained by the admissible `w` of least `ψ`,
which is `bψ` pushed up along `u'` (pushing along `u'` moves `χ` and fixes `ψ`).

原文：b3_colle2.txt:414 (`H_B(ℓ)`), `:780` (`𝓡_{ι-1}`), `:796`.

**Reading.**  This is two conditions on `B`, not one.  The `lev` range is a *height*
condition — `B` must reach `dot nℓ (z − a)` levels below its own top — and that is the
`suppVal` inequality of `height_le_of_hstrip` below.  The `ψ` clause is a *width* condition
in the transverse direction: at every one of those levels `B` must already be as far back
along `vl` as its global `ψ`-minimum, up to `ψ(z − a)`.  A bound on the `nℓ`-height alone
therefore does **not** suffice to produce `hstrip`. -/
theorem hstrip_iff_levels {B : Set (ℤ × ℤ)} {S : Finset (ℤ × ℤ)} {a nℓ bψ : ℤ × ℤ} {cz : ℤ}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hnvl : dot nℓ vl = 0) (hnu : dot nℓ u' = -1)
    (hcz : ∀ b ∈ B, cz ≤ dot nℓ b)
    (hbψ : bψ ∈ B)
    (hbψmin : ∀ b ∈ B, dot (expNormal u' vl) bψ ≤ dot (expNormal u' vl) b) :
    (∀ w ∈ coneRegion B vl u', dot nℓ w < cz → ∀ z ∈ S.erase a,
        cz ≤ dot nℓ (z + (w - a)) → z + (w - a) ∈ Nivat.LE2.halfStrip B vl) ↔
      (∀ z ∈ S.erase a, ∀ lev : ℤ,
        -cz + uCoord u' vl 0 (z - a) < lev → lev ≤ -cz →
        ∃ g ∈ B, uCoord u' vl 0 g = lev ∧
          dot (expNormal u' vl) g ≤
            dot (expNormal u' vl) (z - a) + dot (expNormal u' vl) bψ) := by
  classical
  have hχ : ∀ x : ℤ × ℤ, dot nℓ x = - uCoord u' vl 0 x :=
    dot_eq_neg_uCoord hunimod hnvl hnu
  have hbψtop : uCoord u' vl 0 bψ ≤ -cz := by
    have := hcz bψ hbψ; rw [hχ bψ] at this; omega
  constructor
  · intro hstrip z hz lev hlo hhi
    -- the admissible `w` of least `ψ` at `χ`-level `lev − χ(z−a)`
    set D : ℤ := uCoord u' vl 0 (z - a) with hDdef
    set t : ℕ := (lev - D - uCoord u' vl 0 bψ).toNat with htdef
    have htval : (t : ℤ) = lev - D - uCoord u' vl 0 bψ := by rw [htdef]; omega
    set w : ℤ × ℤ := bψ + (0 : ℤ) • vl + (t : ℤ) • u' with hwdef
    have hwcone : w ∈ coneRegion B vl u' := by
      rw [hwdef, mem_coneRegion_iff]
      exact ⟨bψ, hbψ, 0, t, by push_cast; ring_nf⟩
    have hwχ : uCoord u' vl 0 w = uCoord u' vl 0 bψ + (t : ℤ) := by
      rw [hwdef, uCoord_zero_add hunimod]
    have hwψ : dot (expNormal u' vl) w = dot (expNormal u' vl) bψ := by
      rw [hwdef, dot_expNormal_add hunimod]; ring
    have hwlow : dot nℓ w < cz := by rw [hχ w]; omega
    have hsum : uCoord u' vl 0 (z + (w - a)) = D + uCoord u' vl 0 w := by
      rw [uCoord_zero_add_hom, uCoord_zero_sub_hom, hDdef, uCoord_zero_sub_hom]; ring
    have hhi2 : cz ≤ dot nℓ (z + (w - a)) := by rw [hχ, hsum]; omega
    obtain ⟨g, hg, hg1, hg2⟩ :=
      (mem_halfStrip_iff_coords hunimod).mp (hstrip w hwcone hwlow z hz hhi2)
    have hψsum : dot (expNormal u' vl) (z + (w - a)) =
        dot (expNormal u' vl) (z - a) + dot (expNormal u' vl) bψ := by
      rw [dot_add, dot_sub, hwψ, dot_sub]; ring
    refine ⟨g, hg, ?_, ?_⟩
    · rw [hg1, hsum]; omega
    · rw [hψsum] at hg2; exact hg2
  · intro hlev w hw hwlow z hz hhi2
    obtain ⟨b, hb, h1, -⟩ := (mem_coneRegion_iff_coords hunimod).mp hw
    have hwψmin : dot (expNormal u' vl) bψ ≤ dot (expNormal u' vl) w :=
      le_trans (hbψmin b hb) h1
    have hsum : uCoord u' vl 0 (z + (w - a)) =
        uCoord u' vl 0 (z - a) + uCoord u' vl 0 w := by
      rw [uCoord_zero_add_hom, uCoord_zero_sub_hom, uCoord_zero_sub_hom]; ring
    have hψsum : dot (expNormal u' vl) (z + (w - a)) =
        dot (expNormal u' vl) (z - a) + dot (expNormal u' vl) w := by
      rw [dot_add, dot_sub, dot_sub]; ring
    have hwtop : -cz < uCoord u' vl 0 w := by have := hχ w; omega
    have hlevhi : uCoord u' vl 0 (z + (w - a)) ≤ -cz := by
      have := hχ (z + (w - a)); omega
    obtain ⟨g, hg, hg1, hg2⟩ :=
      hlev z hz (uCoord u' vl 0 (z + (w - a))) (by omega) hlevhi
    exact (mem_halfStrip_iff_coords hunimod).mpr ⟨g, hg, hg1, by omega⟩

/-- **The necessary height condition, in `suppVal` form.**

`hstrip` forces the seed's `nℓ`-drop below `a` to be at most `1 +` the `nℓ`-height of `B`:

`dot nℓ (z − a) ≤ suppVal B nℓ + suppVal B (−nℓ) + 1`.

This is the arithmetic `h_S ≤ h_B + 1` verbatim, with `cz = −suppVal B (−nℓ)` as its bottom
level and `ctop = suppVal B nℓ` as its top (`b3_colle2.txt:414`).  It is **necessary, not
sufficient** — `hstrip_iff_levels` shows the `ψ` clause is a second, transverse requirement
that this inequality says nothing about. -/
theorem height_le_of_hstrip {B : Set (ℤ × ℤ)} {S : Finset (ℤ × ℤ)} {a nℓ bψ : ℤ × ℤ} {cz : ℤ}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hBfin : B.Finite) (hBne : B.Nonempty)
    (hnvl : dot nℓ vl = 0) (hnu : dot nℓ u' = -1)
    (hczdef : cz = -suppVal B (-nℓ))
    (hbψ : bψ ∈ B)
    (hbψmin : ∀ b ∈ B, dot (expNormal u' vl) bψ ≤ dot (expNormal u' vl) b)
    (hstrip : ∀ w ∈ coneRegion B vl u', dot nℓ w < cz → ∀ z ∈ S.erase a,
        cz ≤ dot nℓ (z + (w - a)) → z + (w - a) ∈ Nivat.LE2.halfStrip B vl) :
    ∀ z ∈ S.erase a, dot nℓ (z - a) ≤ suppVal B nℓ + suppVal B (-nℓ) + 1 := by
  classical
  have hχ : ∀ x : ℤ × ℤ, dot nℓ x = - uCoord u' vl 0 x :=
    dot_eq_neg_uCoord hunimod hnvl hnu
  have hcz : ∀ b ∈ B, cz ≤ dot nℓ b := by
    intro b hb
    have := le_suppVal hBfin hBne (n := -nℓ) hb
    rw [dot_neg_left] at this
    omega
  have hlev := (hstrip_iff_levels hunimod hnvl hnu hcz hbψ hbψmin).mp hstrip
  intro z hz
  by_cases hd : dot nℓ (z - a) ≤ 0
  · have h1 := le_suppVal hBfin hBne (n := nℓ) hbψ
    have h2 := le_suppVal hBfin hBne (n := -nℓ) hbψ
    rw [dot_neg_left] at h2
    omega
  · obtain ⟨g, hg, hg1, -⟩ :=
      hlev z hz (-cz + uCoord u' vl 0 (z - a) + 1) (by omega) (by
        have := hχ (z - a); omega)
    have hgtop := le_suppVal hBfin hBne (n := nℓ) hg
    rw [hχ g] at hgtop
    have := hχ (z - a)
    omega

/-! ## §10  The shear dictionary, and why it cannot reach `hmono`

`hmono : ∀ b ∈ B, ∀ t : ℕ, cz ≤ dot nℓ b − t → b + t•u'' ∈ H_B(ℓ)` (`:796`, the cover step of
Claim 4.6) splits in these coordinates into two independent obligations, and the shear
`u'' := u' − K•vl` reaches exactly one of them:

* **occupancy** — `B` must have a point at `χ`-level `χ b + t`.  `χ` is *shear-invariant*
  (`uCoord_shear`), so **no `K` changes this**.
* **monotone profile** — that point must satisfy `ψ'' g ≤ ψ'' b`.  Here `ψ'' = ψ + K·χ`
  (`dot_expNormal_shear`), so `K` does move this one.

§10.2 shows occupancy is a *consequence* of `hmono` at any shear, and §10.3 exhibits a finite,
nonempty, positive-area, **lattice-convex** `B` with an empty level strictly inside its own
band.  So `exists_shear_hmono` is false, and false for a reason the shear cannot touch. -/

/-- **The `u'`-coordinate is shear-invariant.**  `uCoord u' vl 0 z = −(det u' vl)·det vl z`
depends on `u'` only through `det u' vl`, which `det_shear_right` fixes. -/
theorem uCoord_shear (K : ℤ) (x : ℤ × ℤ) :
    uCoord (u' - K • vl) vl 0 x = uCoord u' vl 0 x := by
  simp only [uCoord, det_shear_right]

/-- **The `vl`-coordinate shears by `K·χ`.**  `ψ'' = ψ + K·χ`, the other half of the shear
dictionary: `ψ''(vl) = 1` and `ψ''(u') = K`. -/
theorem dot_expNormal_shear (hunimod : det u' vl = 1 ∨ det u' vl = -1) (K : ℤ) (x : ℤ × ℤ) :
    dot (expNormal (u' - K • vl) vl) x
      = dot (expNormal u' vl) x + K * uCoord u' vl 0 x := by
  have hunimod' : det (u' - K • vl) vl = 1 ∨ det (u' - K • vl) vl = -1 := by
    rw [det_shear_right]; exact hunimod
  have hzero : ∀ n : ℤ × ℤ, dot n (0 : ℤ × ℤ) = 0 := by intro n; simp [dot]
  obtain ⟨A, C, hx, hC⟩ := exists_decomp hunimod (0 : ℤ × ℤ) x
  have hu'val : dot (expNormal (u' - K • vl) vl) u' = K := by
    have h0 : dot (expNormal (u' - K • vl) vl) (u' - K • vl) = 0 :=
      Nivat.ColleReg.dot_expNormal_u'
    have h1 : dot (expNormal (u' - K • vl) vl) vl = 1 :=
      Nivat.ColleReg.dot_expNormal_vl hunimod'
    have h2 : dot (expNormal (u' - K • vl) vl) (u' - K • vl)
        = dot (expNormal (u' - K • vl) vl) u' - K * dot (expNormal (u' - K • vl) vl) vl := by
      rw [dot_sub, dot_zsmul]
    rw [h0, h1] at h2
    omega
  have hψ : dot (expNormal u' vl) x = A := by
    rw [hx, dot_expNormal_add hunimod, hzero]; ring
  have hgoal : dot (expNormal (u' - K • vl) vl) x = A + C * K := by
    rw [hx, dot_add, dot_add, dot_zsmul, dot_zsmul,
      Nivat.ColleReg.dot_expNormal_vl hunimod', hu'val, hzero]
    ring
  rw [hgoal, hψ, ← hC]
  ring

/-! ### §10.2  Occupancy is necessary, at every shear -/

/-- **`hmono` at any shear forces `B` to occupy every `χ`-level it is asked about.**

No hypothesis on `nℓ` or `cz` is used: they ride along inside the side condition.  The point
is that the conclusion is stated in the *unsheared* `χ`, by `uCoord_shear` — so a lane that
refutes occupancy has refuted `hmono` at **every** `K` at once. -/
theorem occupancy_of_hmono {B : Set (ℤ × ℤ)} {nℓ : ℤ × ℤ} {cz K : ℤ}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hmono : ∀ b ∈ B, ∀ t : ℕ, cz ≤ dot nℓ b - t →
      b + (t : ℤ) • (u' - K • vl) ∈ Nivat.LE2.halfStrip B vl) :
    ∀ b ∈ B, ∀ t : ℕ, cz ≤ dot nℓ b - t →
      ∃ g ∈ B, uCoord u' vl 0 g = uCoord u' vl 0 b + (t : ℤ) := by
  intro b hb t ht
  have hunimod' : det (u' - K • vl) vl = 1 ∨ det (u' - K • vl) vl = -1 := by
    rw [det_shear_right]; exact hunimod
  obtain ⟨g, hg, hg1, -⟩ :=
    (mem_halfStrip_iff_coords (u' := u' - K • vl) hunimod').mp (hmono b hb t ht)
  refine ⟨g, hg, ?_⟩
  have e1 : uCoord u' vl 0 g = uCoord (u' - K • vl) vl 0 g := (uCoord_shear K g).symm
  have e2 : uCoord (u' - K • vl) vl 0 (b + (t : ℤ) • (u' - K • vl))
      = uCoord u' vl 0 b + (t : ℤ) := by
    have hrw : b + (t : ℤ) • (u' - K • vl)
        = b + (0 : ℤ) • vl + (t : ℤ) • (u' - K • vl) := by simp
    rw [hrw, uCoord_zero_add hunimod', uCoord_shear]
  rw [e1, hg1, e2]

/-! ### §10.3  A lattice-convex `B` with a hole in its own level band -/

/-- The triangle `conv{(0,0), (1,3), (2,3)}` intersected with `ℤ²`, written as its own
`H`-representation so that lattice-convexity is immediate.

Its lattice points are exactly `(0,0), (1,2), (1,3), (2,3)`: at `y = 1` the horizontal slice
is `x ∈ [1/3, 2/3]`, which contains **no** integer.  Pick's formula agrees — area `3/2`,
three boundary points, so exactly one interior point, namely `(1,2)`. -/
def Bgap : Set (ℤ × ℤ) :=
  {q : ℤ × ℤ | 0 ≤ 3 * q.1 - q.2 ∧ 3 * q.1 - 2 * q.2 ≤ 0 ∧ q.2 ≤ 3}

theorem mem_Bgap {q : ℤ × ℤ} :
    q ∈ Bgap ↔ (0 ≤ 3 * q.1 - q.2 ∧ 3 * q.1 - 2 * q.2 ≤ 0 ∧ q.2 ≤ 3) := Iff.rfl

/-- `Bgap` is the four-point set `{(0,0), (1,2), (1,3), (2,3)}`. -/
theorem Bgap_eq : Bgap = (↑({(0, 0), (1, 2), (1, 3), (2, 3)} : Finset (ℤ × ℤ))) := by
  ext ⟨x, y⟩
  simp only [mem_Bgap, Finset.coe_insert, Set.mem_insert_iff, Finset.coe_singleton,
    Set.mem_singleton_iff, Prod.mk.injEq]
  omega

theorem finite_Bgap : Bgap.Finite := by rw [Bgap_eq]; exact (Finset.finite_toSet _)

theorem nonempty_Bgap : Bgap.Nonempty := ⟨(0, 0), by rw [mem_Bgap]; norm_num⟩

theorem posArea_Bgap : PosArea Bgap := by
  refine ⟨(0, 0), by rw [mem_Bgap]; norm_num,
    (1, 3), by rw [mem_Bgap]; norm_num,
    (2, 3), by rw [mem_Bgap]; norm_num, ?_⟩
  decide

theorem isLatticeConvexRegion_Bgap : IsLatticeConvexRegion Bgap := by
  refine ⟨{p : ℝ × ℝ | 0 ≤ 3 * p.1 - p.2 ∧ 3 * p.1 - 2 * p.2 ≤ 0 ∧ p.2 ≤ 3}, ?_, ?_, ?_⟩
  · intro y hy z hz a b ha hb hab
    obtain ⟨hy1, hy2, hy3⟩ := hy
    obtain ⟨hz1, hz2, hz3⟩ := hz
    refine ⟨?_, ?_, ?_⟩ <;>
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;>
      nlinarith
  · have he : {p : ℝ × ℝ | 0 ≤ 3 * p.1 - p.2 ∧ 3 * p.1 - 2 * p.2 ≤ 0 ∧ p.2 ≤ 3}
        = {p : ℝ × ℝ | 0 ≤ 3 * p.1 - p.2} ∩
            ({p : ℝ × ℝ | 3 * p.1 - 2 * p.2 ≤ 0} ∩ {p : ℝ × ℝ | p.2 ≤ 3}) := rfl
    rw [he]
    exact (isClosed_le continuous_const
        ((continuous_const.mul continuous_fst).sub continuous_snd)).inter
      ((isClosed_le ((continuous_const.mul continuous_fst).sub
          (continuous_const.mul continuous_snd)) continuous_const).inter
        (isClosed_le continuous_snd continuous_const))
  · ext z
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, toReal, mem_Bgap]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨by exact_mod_cast h1, by exact_mod_cast h2, by exact_mod_cast h3⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨by exact_mod_cast h1, by exact_mod_cast h2, by exact_mod_cast h3⟩

/-- **The hole.**  No point of `Bgap` sits at level `y = 1`, although `y = 0` and `y = 3` are
both occupied.  This is the obstruction: it is a statement about `B` alone, with no `u'` in
it, so it survives every shear. -/
theorem not_level_one_Bgap : ∀ g ∈ Bgap, g.2 ≠ 1 := by
  rintro g ⟨h1, h2, h3⟩
  omega

/-! ### §10.4  The verdict -/

/-- **`exists_shear_hmono` is false.**

Witness `B = Bgap`, `vl = (1,0)`, `u' = (0,1)`, `nℓ = (0,-1)`, `cz = -3`, at `b = (0,0)` and
`t = 1`.  Every hypothesis of the dispatched statement is discharged in the kernel on this
witness (`PROTOCOL.md` §7) — `det u' vl = -1`, `B` finite, nonempty, of positive area and
**lattice-convex**, `dot nℓ vl = 0`, `dot nℓ u' = -1` — and two further hypotheses are
discharged that the dispatch did not even ask for, namely that `cz` is a genuine lower bound
for `dot nℓ` on `B` **and is attained** (so `cz = infVal B nℓ`, the reading of
`b3_colle2.txt:405`/`:796`; without pinning `cz` the statement is false for the cheaper reason
that `cz` could sit arbitrarily far below the band).

The side condition holds: `cz = -3 ≤ 0 - 1 = dot nℓ b - t`.  The conclusion fails at **every**
`K`, because `b + 1•(u' − K•vl) = (−K, 1)` sits at level `1` and `H_B(ℓ)` is a union of
`vl`-rays from `B`, which occupies only the levels of `B` — and `Bgap` has none at `1`.

**What this does not refute.**  The monotone-profile obligation is untouched; it may well be
attainable by a shear exactly as described.  What fails is occupancy, and by
`occupancy_of_hmono` occupancy is `hmono`'s consequence at every `K`, so no choice of `K`
repairs it. -/
theorem not_exists_shear_hmono :
    ∃ (B : Set (ℤ × ℤ)) (vl u' nℓ : ℤ × ℤ) (cz : ℤ),
      (det u' vl = 1 ∨ det u' vl = -1) ∧
      B.Finite ∧ B.Nonempty ∧ PosArea B ∧ IsLatticeConvexRegion B ∧
      dot nℓ vl = 0 ∧ dot nℓ u' = -1 ∧
      (∀ b ∈ B, cz ≤ dot nℓ b) ∧ (∃ b ∈ B, dot nℓ b = cz) ∧
      ¬ ∃ K : ℤ, ∀ b ∈ B, ∀ t : ℕ, cz ≤ dot nℓ b - t →
          b + (t : ℤ) • (u' - K • vl) ∈ Nivat.LE2.halfStrip B vl := by
  refine ⟨Bgap, (1, 0), (0, 1), (0, -1), -3, Or.inr (by decide),
    finite_Bgap, nonempty_Bgap, posArea_Bgap, isLatticeConvexRegion_Bgap,
    by decide, by decide, ?_, ⟨(1, 3), by rw [mem_Bgap]; norm_num, by norm_num [dot]⟩, ?_⟩
  · rintro b ⟨-, -, h3⟩
    simp only [dot]
    omega
  · rintro ⟨K, hK⟩
    have hb : ((0 : ℤ), (0 : ℤ)) ∈ Bgap := by rw [mem_Bgap]; norm_num
    have hside : (-3 : ℤ) ≤ dot (0, -1) ((0 : ℤ), (0 : ℤ)) - (1 : ℕ) := by
      simp only [dot]; norm_num
    obtain ⟨g, hg, s, hgs⟩ := hK _ hb 1 hside
    have h2 : g.2 = 1 := by
      have := congrArg Prod.snd hgs
      simp only [Prod.snd_add, Prod.smul_snd, Prod.snd_sub, smul_eq_mul] at this
      omega
    exact not_level_one_Bgap g hg h2


/-! ## §11  Occupancy from the two edge hypotheses — and the shear that §10 refuted

§10 killed the unrestricted shear existence with a witness (`Bgap`) whose minimum-level
face is a **single point**.  Definition 3.2 (`b3_colle2.txt:402`) excludes that witness:
the generating set `𝒮` of `b3_colle2.txt:774` — *"which according to Lemma 2.3 has an edge
parallel to `ℓ` and another one parallel to `−ℓ`"* — has **edges** at both extremes, and
`Enveloped.E_eq` (`LatticeEdges.lean:1657`) carries `E ↑𝒮_φ = E B` onto the enveloped `B`
of `b3_colle2.txt:777`.  This section re-runs the question with those two edges assumed,
and the answer flips: **the shear exists** (`exists_shear_hmono_of_edges`).

逐个量词对应原文（硬规矩 7）:

* `hEtop : nl ∈ E B` ↔ `:774` "an edge parallel to `ℓ`" — the edge with outer normal `nℓ`;
* `hEbot : -nl ∈ E B` ↔ `:774` "another one parallel to `−ℓ`";
* `hconv : IsLatticeConvexRegion B` ↔ Definition 3.2's *"A **convex** set `𝒯 ⊂ ℤ²`"*
  (`:402`) — literally the first conjunct of this repo's `WeaklyEnveloped`, so it is free
  from `Enveloped ↑𝒮_φ B` (`henv.1.1`);
* `hvl : Primitive vl` ↔ `vl` is the primitive direction of the rational line `ℓ`
  (`:405`); under `hunimod` it is not even a hypothesis (`prim_of_unimod`).

Nothing here is stronger than the source: no `∀ K`, no ordering of `B`, no enumeration.
The one place lattice convexity is used is the four-point convex combination inside
`mem_of_convex_combo`; the one place the edges are used is to make both extreme slices
**at least one `vl`-step long**.
-/

/-- A lattice vector orthogonal to `nl` is an integer multiple of any primitive `vl`
orthogonal to `nl`. -/
theorem exists_zsmul_of_dot_eq_zero {nl m : ℤ × ℤ} (hn : nl ≠ 0) (hvl : Prim vl)
    (hperp : dot nl vl = 0) (hm : dot nl m = 0) : ∃ a : ℤ, m = a • vl := by
  obtain ⟨a, ha⟩ := exists_smul_of_det_eq_zero hvl (det_eq_zero_of_dot_eq_zero hn hperp hm)
  exact ⟨a, by rw [ha]; simp [Prod.ext_iff]⟩

/-- Two distinct points of a set on which `dot nl` is constant give a **positive** step
`k • vl` inside that set. -/
theorem exists_pos_step {R : Set (ℤ × ℤ)} {nl : ℤ × ℤ}
    (hn : nl ≠ 0) (hvl : Prim vl) (hperp : dot nl vl = 0)
    (hlev : ∀ x ∈ R, ∀ y ∈ R, dot nl (y - x) = 0) (hnt : R.Nontrivial) :
    ∃ p ∈ R, ∃ k : ℤ, 0 < k ∧ p + k • vl ∈ R := by
  obtain ⟨x, hx, y, hy, hxy⟩ := hnt
  obtain ⟨a, ha⟩ := exists_zsmul_of_dot_eq_zero hn hvl hperp (hlev x hx y hy)
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply hxy
    have h0 : y - x = 0 := by rw [ha]; simp
    exact (sub_eq_zero.mp h0).symm
  rcases lt_or_gt_of_ne ha0 with h | h
  · refine ⟨y, hy, -a, by omega, ?_⟩
    have he : y + (-a) • vl = x := by rw [neg_smul, ← ha]; abel
    rw [he]; exact hx
  · refine ⟨x, hx, a, h, ?_⟩
    have he : x + a • vl = y := by rw [← ha]; abel
    rw [he]; exact hy

/-- Scalar identity behind the four-point convex combination. -/
private theorem combo_coord {NR aR bR kR mR r1R r2R P Q V G : ℝ}
    (ha : 0 < aR) (hb : 0 < bR) (hk : 0 < kR) (hm : 0 < mR) (hN : NR = aR + bR)
    (hG : NR * G = bR * P + aR * Q + (r1R + r2R) * V) :
    G = bR / NR * ((1 - r1R / (bR * kR)) * P + r1R / (bR * kR) * (P + kR * V))
      + aR / NR * ((1 - r2R / (aR * mR)) * Q + r2R / (aR * mR) * (Q + mR * V)) := by
  have hN0 : NR ≠ 0 := by rw [hN]; positivity
  have hbk : bR * kR ≠ 0 := ne_of_gt (mul_pos hb hk)
  have ham : aR * mR ≠ 0 := ne_of_gt (mul_pos ha hm)
  have ha0 : aR ≠ 0 := ne_of_gt ha
  have hb0 : bR ≠ 0 := ne_of_gt hb
  have e1 : (1 - r1R / (bR * kR)) * P + r1R / (bR * kR) * (P + kR * V)
      = P + r1R / bR * V := by field_simp; ring
  have e2 : (1 - r2R / (aR * mR)) * Q + r2R / (aR * mR) * (Q + mR * V)
      = Q + r2R / aR * V := by field_simp; ring
  have e3 : bR / NR * (P + r1R / bR * V) + aR / NR * (Q + r2R / aR * V)
      = (bR * P + aR * Q + (r1R + r2R) * V) / NR := by field_simp; ring
  rw [e1, e2, e3, eq_div_iff hN0]
  linarith [hG]

/-- **The four-point convex combination.**  If `N • g = β•p + α•q + (r₁+r₂)•vl` with the
weights in range, then `g` lies in any convex `C` containing `p`, `p + k•vl`, `q`,
`q + m•vl`. -/
private theorem mem_of_convex_combo {C : Set (ℝ × ℝ)} (hC : Convex ℝ C)
    {p q g : ℤ × ℤ} {al be N r₁ r₂ k m : ℤ}
    (hpC : toReal p ∈ C) (hpkC : toReal (p + k • vl) ∈ C)
    (hqC : toReal q ∈ C) (hqmC : toReal (q + m • vl) ∈ C)
    (hal : 0 < al) (hbe : 0 < be) (hk : 0 < k) (hm : 0 < m) (hN : N = al + be)
    (hr₁ : 0 ≤ r₁) (hr₁b : r₁ ≤ be * k) (hr₂ : 0 ≤ r₂) (hr₂b : r₂ ≤ al * m)
    (hg : N • g = be • p + al • q + (r₁ + r₂) • vl) :
    toReal g ∈ C := by
  have hal' : (0:ℝ) < (al:ℝ) := by exact_mod_cast hal
  have hbe' : (0:ℝ) < (be:ℝ) := by exact_mod_cast hbe
  have hk' : (0:ℝ) < (k:ℝ) := by exact_mod_cast hk
  have hm' : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
  have hN' : ((N:ℤ):ℝ) = (al:ℝ) + (be:ℝ) := by exact_mod_cast hN
  have hNpos : (0:ℝ) < (N:ℝ) := by rw [hN']; linarith
  have hr₁0 : (0:ℝ) ≤ (r₁:ℝ) := by exact_mod_cast hr₁
  have hr₂0 : (0:ℝ) ≤ (r₂:ℝ) := by exact_mod_cast hr₂
  have hr₁b' : (r₁:ℝ) ≤ (be:ℝ) * (k:ℝ) := by exact_mod_cast hr₁b
  have hr₂b' : (r₂:ℝ) ≤ (al:ℝ) * (m:ℝ) := by exact_mod_cast hr₂b
  have hθ₁0 : (0:ℝ) ≤ (r₁:ℝ) / ((be:ℝ) * (k:ℝ)) := div_nonneg hr₁0 (mul_pos hbe' hk').le
  have hθ₂0 : (0:ℝ) ≤ (r₂:ℝ) / ((al:ℝ) * (m:ℝ)) := div_nonneg hr₂0 (mul_pos hal' hm').le
  have hθ₁1 : (r₁:ℝ) / ((be:ℝ) * (k:ℝ)) ≤ 1 := (div_le_one (mul_pos hbe' hk')).mpr hr₁b'
  have hθ₂1 : (r₂:ℝ) / ((al:ℝ) * (m:ℝ)) ≤ 1 := (div_le_one (mul_pos hal' hm')).mpr hr₂b'
  have hA := hC hpC hpkC (by linarith : (0:ℝ) ≤ 1 - (r₁:ℝ) / ((be:ℝ) * (k:ℝ))) hθ₁0
    (by ring : (1 - (r₁:ℝ) / ((be:ℝ) * (k:ℝ))) + (r₁:ℝ) / ((be:ℝ) * (k:ℝ)) = 1)
  have hD := hC hqC hqmC (by linarith : (0:ℝ) ≤ 1 - (r₂:ℝ) / ((al:ℝ) * (m:ℝ))) hθ₂0
    (by ring : (1 - (r₂:ℝ) / ((al:ℝ) * (m:ℝ))) + (r₂:ℝ) / ((al:ℝ) * (m:ℝ)) = 1)
  have hsum : (be:ℝ) / (N:ℝ) + (al:ℝ) / (N:ℝ) = 1 := by
    field_simp
    rw [hN']
    ring
  have hG := hC hA hD (div_nonneg hbe'.le hNpos.le) (div_nonneg hal'.le hNpos.le) hsum
  have h1 : (N:ℝ) * (g.1:ℝ)
      = (be:ℝ) * (p.1:ℝ) + (al:ℝ) * (q.1:ℝ) + ((r₁:ℝ) + (r₂:ℝ)) * (vl.1:ℝ) := by
    have h := congrArg Prod.fst hg
    simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul] at h
    exact_mod_cast h
  have h2 : (N:ℝ) * (g.2:ℝ)
      = (be:ℝ) * (p.2:ℝ) + (al:ℝ) * (q.2:ℝ) + ((r₁:ℝ) + (r₂:ℝ)) * (vl.2:ℝ) := by
    have h := congrArg Prod.snd hg
    simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul] at h
    exact_mod_cast h
  have hkey : toReal g
      = ((be:ℝ) / (N:ℝ)) • (((1 - (r₁:ℝ) / ((be:ℝ) * (k:ℝ))) • toReal p
            + ((r₁:ℝ) / ((be:ℝ) * (k:ℝ))) • toReal (p + k • vl)))
        + ((al:ℝ) / (N:ℝ)) • (((1 - (r₂:ℝ) / ((al:ℝ) * (m:ℝ))) • toReal q
            + ((r₂:ℝ) / ((al:ℝ) * (m:ℝ))) • toReal (q + m • vl))) := by
    apply Prod.ext
    · simp only [toReal, Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      push_cast
      exact combo_coord hal' hbe' hk' hm' hN' h1
    · simp only [toReal, Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      push_cast
      exact combo_coord hal' hbe' hk' hm' hN' h2
  rw [hkey]
  exact hG





theorem occupancy_of_edges {B : Set (ℤ × ℤ)} {nl : ℤ × ℤ}
    (hconv : IsLatticeConvexRegion B) (hvl : Primitive vl) (hperp : dot nl vl = 0)
    (hEbot : -nl ∈ E B) (hEtop : nl ∈ E B) :
    ∀ c : ℤ, (∃ b ∈ B, dot nl b ≤ c) → (∃ b ∈ B, c ≤ dot nl b) →
      ∃ b ∈ B, dot nl b = c := by
  classical
  obtain ⟨C, hCconv, -, hBC⟩ := hconv
  obtain ⟨hprim, htop⟩ := hEtop
  obtain ⟨-, hbot⟩ := hEbot
  have hvlP : Prim vl := prim_iff_primitive.mpr hvl
  have hn0 : nl ≠ 0 := hprim.ne_zero
  have hlevtop : ∀ x ∈ face B nl, ∀ y ∈ face B nl, dot nl (y - x) = 0 := by
    intro x hx y hy
    rw [dot_sub, dot_eq_of_mem_face hy hx, sub_self]
  have hlevbot : ∀ x ∈ face B (-nl), ∀ y ∈ face B (-nl), dot nl (y - x) = 0 := by
    intro x hx y hy
    have h := dot_eq_of_mem_face hy hx
    rw [dot_neg_left, dot_neg_left] at h
    rw [dot_sub]; omega
  obtain ⟨p, hp, k, hk, hpk⟩ := exists_pos_step hn0 hvlP hperp hlevbot hbot
  obtain ⟨q, hq, m, hm, hqm⟩ := exists_pos_step hn0 hvlP hperp hlevtop htop
  have hpB : p ∈ B := face_subset _ _ hp
  have hqB : q ∈ B := face_subset _ _ hq
  have hpkB : p + k • vl ∈ B := face_subset _ _ hpk
  have hqmB : q + m • vl ∈ B := face_subset _ _ hqm
  have hpmin : ∀ y ∈ B, dot nl p ≤ dot nl y := by
    intro y hy
    have h := hp.2 y hy
    rw [dot_neg_left, dot_neg_left] at h
    omega
  have hqmax : ∀ y ∈ B, dot nl y ≤ dot nl q := fun y hy => hq.2 y hy
  intro c hc1 hc2
  obtain ⟨b1, hb1, hb1le⟩ := hc1
  obtain ⟨b2, hb2, hb2ge⟩ := hc2
  have hcbc : dot nl p ≤ c := le_trans (hpmin b1 hb1) hb1le
  have hcct : c ≤ dot nl q := le_trans hb2ge (hqmax b2 hb2)
  rcases eq_or_lt_of_le hcbc with h | hlt1
  · exact ⟨p, hpB, h⟩
  rcases eq_or_lt_of_le hcct with h | hlt2
  · exact ⟨q, hqB, h.symm⟩
  obtain ⟨x0, y0, hxy⟩ := Int.isCoprime_iff_gcd_eq_one.mpr hprim
  obtain ⟨z0, hz0⟩ : ∃ z0 : ℤ × ℤ, dot nl z0 = c :=
    ⟨(c * x0, c * y0), by simp only [dot]; linear_combination c * hxy⟩
  have hw0 : dot nl ((dot nl q - c) • p + (c - dot nl p) • q
      - (dot nl q - dot nl p) • z0) = 0 := by
    rw [dot_sub, dot_add, dot_zsmul, dot_zsmul, dot_zsmul, hz0]; ring
  obtain ⟨M, hM⟩ := exists_zsmul_of_dot_eq_zero hn0 hvlP hperp hw0
  have hNpos : 0 < dot nl q - dot nl p := by omega
  have hNne : (dot nl q - dot nl p) ≠ 0 := by omega
  have hdiv := Int.mul_ediv_add_emod (-M) (dot nl q - dot nl p)
  obtain ⟨r, hrdef⟩ : ∃ r : ℤ, r = (-M) % (dot nl q - dot nl p) := ⟨_, rfl⟩
  have hr0 : 0 ≤ r := by rw [hrdef]; exact Int.emod_nonneg _ hNne
  have hrN : r < dot nl q - dot nl p := by rw [hrdef]; exact Int.emod_lt_of_pos _ hNpos
  obtain ⟨g, hgdef⟩ : ∃ g : ℤ × ℤ, g = z0 + (-((-M) / (dot nl q - dot nl p))) • vl := ⟨_, rfl⟩
  have hNJ : (dot nl q - dot nl p) * (-((-M) / (dot nl q - dot nl p))) = M + r := by
    rw [hrdef]; linarith [hdiv]
  have hz0eq : (dot nl q - dot nl p) • z0
      = (dot nl q - c) • p + (c - dot nl p) • q - M • vl := by
    rw [← hM]; abel
  have hgN : (dot nl q - dot nl p) • g
      = (dot nl q - c) • p + (c - dot nl p) • q + r • vl := by
    rw [hgdef, smul_add, smul_smul, hNJ, hz0eq, add_smul]
    abel
  refine ⟨g, ?_, ?_⟩
  · rw [hBC] at hpB hqB hpkB hqmB ⊢
    have hbek : dot nl q - c ≤ (dot nl q - c) * k :=
      le_mul_of_one_le_right (by omega) (by omega)
    have halm : c - dot nl p ≤ (c - dot nl p) * m :=
      le_mul_of_one_le_right (by omega) (by omega)
    have hr1b : min r (dot nl q - c) ≤ (dot nl q - c) * k :=
      le_trans (min_le_right _ _) hbek
    have hr2b : r - min r (dot nl q - c) ≤ (c - dot nl p) * m :=
      le_trans (by omega) halm
    refine Set.mem_preimage.mpr
      (mem_of_convex_combo (vl := vl) hCconv hpB hpkB hqB hqmB
        (al := c - dot nl p) (be := dot nl q - c) (N := dot nl q - dot nl p)
        (r₁ := min r (dot nl q - c)) (r₂ := r - min r (dot nl q - c))
        (by omega) (by omega) hk hm (by omega) (by omega) hr1b (by omega) hr2b ?_)
    rw [show min r (dot nl q - c) + (r - min r (dot nl q - c)) = r from by omega]
    exact hgN
  · rw [hgdef, dot_add, dot_zsmul, hperp, hz0]; ring





theorem prim_of_unimod (hunimod : det u' vl = 1 ∨ det u' vl = -1) : Prim vl := by
  rcases hunimod with h | h
  · exact Int.isCoprime_iff_gcd_eq_one.mp ⟨-u'.2, u'.1, by simp only [det] at h; linarith⟩
  · exact Int.isCoprime_iff_gcd_eq_one.mp ⟨u'.2, -u'.1, by simp only [det] at h; linarith⟩

/-! ### §11c  `hmono` with `K` as a parameter

The consumer (`RegionSteps.lean`, `wedgeResidualR_of_cone_hmono_at_shear_of_argmax`) states
`hmono` and `hcorner` at the *same* `K`, so an existential `K` is unusable there.  This is
the same proof with `K` taken as a parameter and the bound it must satisfy made explicit.

`hK` is spelled as "`K` is at most every `ψ`-difference across `B`", i.e.
`K ≤ ψ x − ψ y` for all `x, y ∈ B`.  Taking `x = y` this **forces `K ≤ 0`**; taking
`x` a `ψ`-minimiser and `y` a `ψ`-maximiser it is exactly `K ≤ −(ψmax − ψmin)`.  Stated
this way it needs no finiteness of `B` to make sense and no `argmax`/`argmin` to use.

⚠ The sign is not an artifact of the proof: `no_nonneg_shear_hmono` below exhibits a
finite, lattice-convex, positive-area `B` carrying **both** `:774` edges for which no
`K ≥ 0` satisfies the conclusion. -/
theorem exists_shear_hmono_of_edges_of_le {B : Set (ℤ × ℤ)} {nl : ℤ × ℤ} {cz K : ℤ}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (_hBfin : B.Finite) (_hBne : B.Nonempty) (hBlc : IsLatticeConvexRegion B)
    (hnvl : dot nl vl = 0) (hnu : dot nl u' = -1)
    (hEbot : -nl ∈ E B) (hEtop : nl ∈ E B)
    (hczB : ∃ b₀ ∈ B, dot nl b₀ ≤ cz)
    (hK : ∀ x ∈ B, ∀ y ∈ B, K ≤ dot (expNormal u' vl) x - dot (expNormal u' vl) y) :
    ∀ b ∈ B, ∀ t : ℕ, cz ≤ dot nl b - t →
      b + (t : ℤ) • (u' - K • vl) ∈ Nivat.LE2.halfStrip B vl := by
  classical
  have hvlP : Primitive vl := prim_iff_primitive.mp (prim_of_unimod hunimod)
  have hocc := occupancy_of_edges (vl := vl) (nl := nl) hBlc hvlP hnvl hEbot hEtop
  have hχ : ∀ x : ℤ × ℤ, dot nl x = - uCoord u' vl 0 x :=
    dot_eq_neg_uCoord hunimod hnvl hnu
  have hunimod' : det (u' - K • vl) vl = 1 ∨ det (u' - K • vl) vl = -1 := by
    rw [det_shear_right]; exact hunimod
  intro b hb t ht
  rcases Nat.eq_zero_or_pos t with rfl | htpos
  · exact ⟨b, hb, 0, by simp⟩
  obtain ⟨b₀, hb₀, hb₀le⟩ := hczB
  obtain ⟨g, hgB, hglev⟩ :=
    hocc (dot nl b - (t : ℤ)) ⟨b₀, hb₀, le_trans hb₀le ht⟩ ⟨b, hb, by omega⟩
  have hχx : uCoord u' vl 0 (b + (t : ℤ) • (u' - K • vl)) = uCoord u' vl 0 b + (t : ℤ) := by
    rw [← uCoord_shear (u' := u') (vl := vl) K (b + (t : ℤ) • (u' - K • vl))]
    have hrw : b + (t : ℤ) • (u' - K • vl)
        = b + (0 : ℤ) • vl + (t : ℤ) • (u' - K • vl) := by simp
    rw [hrw, uCoord_zero_add hunimod', uCoord_shear]
  have hψx : dot (expNormal u' vl) (b + (t : ℤ) • (u' - K • vl))
      = dot (expNormal u' vl) b - (t : ℤ) * K := by
    rw [dot_add, dot_zsmul, dot_sub, dot_zsmul, Nivat.ColleReg.dot_expNormal_u',
      Nivat.ColleReg.dot_expNormal_vl hunimod]
    ring
  refine (mem_halfStrip_iff_coords (u' := u') hunimod).mpr ⟨g, hgB, ?_, ?_⟩
  · rw [hχx]
    have h1 := hχ g
    have h2 := hχ b
    omega
  · rw [hψx]
    have h1 : (1 : ℤ) ≤ (t : ℤ) := by exact_mod_cast htpos
    have h2 := hK b hb g hgB
    have h3 : K ≤ 0 := by have := hK b hb b hb; linarith
    have h5 : (t : ℤ) * K ≤ K := by nlinarith
    linarith

/-- The existential form, unchanged, now a corollary of the parameterised one: the
`ψ`-extremes of a finite nonempty `B` produce a legal `K`. -/
theorem exists_shear_hmono_of_edges {B : Set (ℤ × ℤ)} {nl : ℤ × ℤ} {cz : ℤ}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hBfin : B.Finite) (hBne : B.Nonempty) (hBlc : IsLatticeConvexRegion B)
    (hnvl : dot nl vl = 0) (hnu : dot nl u' = -1)
    (hEbot : -nl ∈ E B) (hEtop : nl ∈ E B)
    (hczB : ∃ b₀ ∈ B, dot nl b₀ ≤ cz) :
    ∃ K : ℤ, ∀ b ∈ B, ∀ t : ℕ, cz ≤ dot nl b - t →
      b + (t : ℤ) • (u' - K • vl) ∈ Nivat.LE2.halfStrip B vl := by
  classical
  have hBne' : hBfin.toFinset.Nonempty := by
    obtain ⟨b, hb⟩ := hBne
    exact ⟨b, hBfin.mem_toFinset.mpr hb⟩
  obtain ⟨bmax, hbmaxF, hbmax⟩ :=
    hBfin.toFinset.exists_max_image (fun z => dot (expNormal u' vl) z) hBne'
  obtain ⟨bmin, hbminF, hbmin⟩ :=
    hBfin.toFinset.exists_min_image (fun z => dot (expNormal u' vl) z) hBne'
  refine ⟨-(dot (expNormal u' vl) bmax - dot (expNormal u' vl) bmin),
    exists_shear_hmono_of_edges_of_le hunimod hBfin hBne hBlc hnvl hnu hEbot hEtop hczB
      ?_⟩
  intro x hx y hy
  have h1 := hbmin x (hBfin.mem_toFinset.mpr hx)
  have h2 := hbmax y (hBfin.mem_toFinset.mpr hy)
  linarith

/-- **The dispatched signature of the occupancy lemma.**  `_hfin` and `_hne` are *not*
used: the two edge hypotheses already give attainment of both extreme levels, so no
finiteness of `B` is needed anywhere in the argument. -/
theorem occupancy_of_enveloped {B : Set (ℤ × ℤ)} {nl : ℤ × ℤ}
    (_hfin : B.Finite) (_hne : B.Nonempty) (hconv : IsLatticeConvexRegion B)
    (hvl : Primitive vl) (hperp : dot nl vl = 0)
    (hEbot : -nl ∈ E B) (hEtop : nl ∈ E B) :
    ∀ c : ℤ, (∃ b ∈ B, dot nl b ≤ c) → (∃ b ∈ B, c ≤ dot nl b) →
      ∃ b ∈ B, dot nl b = c :=
  occupancy_of_edges hconv hvl hperp hEbot hEtop

/-- **The shear existence with `cz` read off the bottom support value**, which is the form
the consumer has (`cz = -suppVal B (-nℓ)`, i.e. `infVal B nℓ`; see `height_le_of_hstrip`
in §9 for the same convention). -/
theorem exists_shear_hmono_of_edges_of_suppVal {B : Set (ℤ × ℤ)} {nl : ℤ × ℤ} {cz : ℤ}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hBfin : B.Finite) (hBne : B.Nonempty) (hBlc : IsLatticeConvexRegion B)
    (hnvl : dot nl vl = 0) (hnu : dot nl u' = -1)
    (hEbot : -nl ∈ E B) (hEtop : nl ∈ E B)
    (hczdef : cz = -suppVal B (-nl)) :
    ∃ K : ℤ, ∀ b ∈ B, ∀ t : ℕ, cz ≤ dot nl b - t →
      b + (t : ℤ) • (u' - K • vl) ∈ Nivat.LE2.halfStrip B vl := by
  refine exists_shear_hmono_of_edges hunimod hBfin hBne hBlc hnvl hnu hEbot hEtop ?_
  obtain ⟨b₀, hb₀, hb₀eq⟩ := exists_suppVal_eq hBfin hBne (-nl)
  rw [dot_neg_left] at hb₀eq
  exact ⟨b₀, hb₀, by omega⟩

/-- **Envelopedness form.**  This is the statement as `b3_colle2.txt:774`+`:777` deliver
it: the two edges are hypotheses on the *generating set* `S`, and `Enveloped.E_eq` moves
them to the enveloped `B`.  `IsLatticeConvexRegion B` is not a hypothesis here — it is the
first conjunct of Definition 3.2. -/
theorem exists_shear_hmono_of_enveloped {S B : Set (ℤ × ℤ)} {nl : ℤ × ℤ} {cz : ℤ}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hBfin : B.Finite) (hBne : B.Nonempty)
    (hESfin : (E S).Finite) (henv : Enveloped S B)
    (hnvl : dot nl vl = 0) (hnu : dot nl u' = -1)
    (hEbot : -nl ∈ E S) (hEtop : nl ∈ E S)
    (hczB : ∃ b₀ ∈ B, dot nl b₀ ≤ cz) :
    ∃ K : ℤ, ∀ b ∈ B, ∀ t : ℕ, cz ≤ dot nl b - t →
      b + (t : ℤ) • (u' - K • vl) ∈ Nivat.LE2.halfStrip B vl :=
  exists_shear_hmono_of_edges hunimod hBfin hBne henv.1.1 hnvl hnu
    (by rw [Enveloped.E_eq hESfin henv]; exact hEbot)
    (by rw [Enveloped.E_eq hESfin henv]; exact hEtop) hczB

/-! ### §11b  `b3_colle2.txt:774` reaches `B`

`:774` says the `η`-generating set `𝒮` "has an edge parallel to `ℓ` and another one
parallel to `−ℓ`", and `:777` says `B` is `E(𝒮_φ)`-**enveloped**.  The two are joined by
`Enveloped.E_eq` (`LatticeEdges.lean:1657`), which needs only `(E 𝒮).Finite`.  So the
edge pair is *not* an extra assumption on `B`: it is `:774` transported along `:777`.

Quantifier correspondence (hard rule 7):

* `htop : nℓ ∈ E S` ↔ `:774` "an edge parallel to `ℓ`";
* `hbot : -nℓ ∈ E S` ↔ `:774` "another one parallel to `−ℓ`";
* `h : Enveloped S B` ↔ `:777` "`B ⊂ ℤ²` an `E(𝒮_φ)`-enveloped set";
* `hSfin : (E S).Finite` — not in the source, because there `𝒮` is a finite generating
  set (`:774` "as in Lemma 2.4") and `E` of a finite set is finite.  It is a hypothesis
  here only because this lemma does not carry `S.Finite`.
-/

/-- **The `:774` edge pair transports from the generating set to the enveloped set.**
Two rewrites off `Enveloped.E_eq`. -/
theorem both_edges_of_enveloped {S B : Set (ℤ × ℤ)} {nl : ℤ × ℤ}
    (hSfin : (E S).Finite) (h : Nivat.LE2.Enveloped S B)
    (htop : nl ∈ E S) (hbot : -nl ∈ E S) : nl ∈ E B ∧ -nl ∈ E B := by
  rw [Enveloped.E_eq hSfin h]
  exact ⟨htop, hbot⟩

/-- Same statement with the `EnvOf` spelling used by the `Env` field of `ChainData`
(`EnvOf U = Enveloped U`, `LatticeEdges.lean:2433`). -/
theorem both_edges_of_envOf {S B : Set (ℤ × ℤ)} {nl : ℤ × ℤ}
    (hSfin : (E S).Finite) (h : Nivat.LE2.EnvOf S B)
    (htop : nl ∈ E S) (hbot : -nl ∈ E S) : nl ∈ E B ∧ -nl ∈ E B :=
  both_edges_of_enveloped hSfin (envOf_iff.mp h) htop hbot

/-- **Occupancy in the source form**: the edge hypotheses sit on the generating set `S`
and `IsLatticeConvexRegion B` is not assumed — it is the first conjunct of Definition 3.2
(`:402`), hence free from `Enveloped S B`. -/
theorem occupancy_of_envOf {S B : Set (ℤ × ℤ)} {nl : ℤ × ℤ}
    (hSfin : (E S).Finite) (henv : Nivat.LE2.Enveloped S B)
    (hvl : Primitive vl) (hperp : dot nl vl = 0)
    (hEbot : -nl ∈ E S) (hEtop : nl ∈ E S) :
    ∀ c : ℤ, (∃ b ∈ B, dot nl b ≤ c) → (∃ b ∈ B, c ≤ dot nl b) →
      ∃ b ∈ B, dot nl b = c :=
  let hE := both_edges_of_enveloped hSfin henv hEtop hEbot
  occupancy_of_edges henv.1.1 hvl hperp hE.2 hE.1

def Bsq : Set (ℤ × ℤ) := {q : ℤ × ℤ | 0 ≤ q.1 ∧ q.1 ≤ 1 ∧ 0 ≤ q.2 ∧ q.2 ≤ 1}

theorem mem_Bsq {q : ℤ × ℤ} : q ∈ Bsq ↔ (0 ≤ q.1 ∧ q.1 ≤ 1 ∧ 0 ≤ q.2 ∧ q.2 ≤ 1) := Iff.rfl

theorem Bsq_eq : Bsq = (↑({(0, 0), (0, 1), (1, 0), (1, 1)} : Finset (ℤ × ℤ))) := by
  ext ⟨x, y⟩
  simp only [mem_Bsq, Finset.coe_insert, Set.mem_insert_iff, Finset.coe_singleton,
    Set.mem_singleton_iff, Prod.mk.injEq]
  omega

theorem finite_Bsq : Bsq.Finite := by rw [Bsq_eq]; exact Finset.finite_toSet _

theorem nonempty_Bsq : Bsq.Nonempty := ⟨(0, 0), by rw [mem_Bsq]; norm_num⟩

theorem isLatticeConvexRegion_Bsq : IsLatticeConvexRegion Bsq := by
  refine ⟨{p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1}, ?_, ?_, ?_⟩
  · intro y hy z hz a b ha hb hab
    obtain ⟨hy1, hy2, hy3, hy4⟩ := hy
    obtain ⟨hz1, hz2, hz3, hz4⟩ := hz
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;>
      nlinarith
  · have he : {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1}
        = {p : ℝ × ℝ | 0 ≤ p.1} ∩ ({p : ℝ × ℝ | p.1 ≤ 1}
          ∩ ({p : ℝ × ℝ | 0 ≤ p.2} ∩ {p : ℝ × ℝ | p.2 ≤ 1})) := rfl
    rw [he]
    exact (isClosed_le continuous_const continuous_fst).inter
      ((isClosed_le continuous_fst continuous_const).inter
        ((isClosed_le continuous_const continuous_snd).inter
          (isClosed_le continuous_snd continuous_const)))
  · ext z
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, toReal, mem_Bsq]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨by exact_mod_cast h1, by exact_mod_cast h2, by exact_mod_cast h3,
        by exact_mod_cast h4⟩
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨by exact_mod_cast h1, by exact_mod_cast h2, by exact_mod_cast h3,
        by exact_mod_cast h4⟩

/-- The hypothesis bundle of `exists_shear_hmono_of_edges` is **satisfiable**: the unit
square meets every one of them. -/
theorem hyps_satisfiable :
    ∃ (B : Set (ℤ × ℤ)) (vl u' nl : ℤ × ℤ) (cz : ℤ),
      (det u' vl = 1 ∨ det u' vl = -1) ∧
      B.Finite ∧ B.Nonempty ∧ PosArea B ∧ IsLatticeConvexRegion B ∧
      dot nl vl = 0 ∧ dot nl u' = -1 ∧ -nl ∈ E B ∧ nl ∈ E B ∧
      (∃ b₀ ∈ B, dot nl b₀ ≤ cz) ∧ (∀ b ∈ B, cz ≤ dot nl b) := by
  refine ⟨Bsq, (1, 0), (0, 1), (0, -1), -1, Or.inr (by decide), finite_Bsq, nonempty_Bsq,
    ⟨(0, 0), by rw [mem_Bsq]; norm_num, (1, 0), by rw [mem_Bsq]; norm_num,
      (0, 1), by rw [mem_Bsq]; norm_num, by decide⟩,
    isLatticeConvexRegion_Bsq, by decide, by decide, ⟨by decide, ?_⟩, ⟨by decide, ?_⟩,
    ⟨(0, 1), by rw [mem_Bsq]; norm_num, by norm_num [dot]⟩, ?_⟩
  · refine ⟨(0, 1), ⟨by rw [mem_Bsq]; norm_num, ?_⟩, (1, 1),
      ⟨by rw [mem_Bsq]; norm_num, ?_⟩, by decide⟩ <;>
    · rintro y ⟨-, -, -, h4⟩
      simp only [dot, Prod.fst_neg, Prod.snd_neg]
      omega
  · refine ⟨(0, 0), ⟨by rw [mem_Bsq]; norm_num, ?_⟩, (1, 0),
      ⟨by rw [mem_Bsq]; norm_num, ?_⟩, by decide⟩ <;>
    · rintro y ⟨-, -, h3, -⟩
      simp only [dot]
      omega
  · rintro b ⟨-, -, -, h4⟩
    simp only [dot]
    omega

/-! ### §11d  The sign of `K` is forced — a both-edges witness admitting no `K ≥ 0`

`Bslant` is the six-point lattice parallelogram `{(x,y) | 0 ≤ y ≤ 1, y ≤ x ≤ y+2}`:

```
      . 1 2 3        level y = 1 :  x ∈ {1,2,3}
      0 1 2 .        level y = 0 :  x ∈ {0,1,2}
```

It is finite, nonempty, positive-area, lattice-convex, and — unlike `Bgap` (§10) and
unlike Wlines' `sliver` — it carries **both** `b3_colle2.txt:774` edges: its bottom face
(normal `nℓ = (0,−1)`) and its top face (normal `−nℓ = (0,1)`) are each three points long.
So every hypothesis of `exists_shear_hmono_of_edges_of_le` except `hK` is met.

Nevertheless no `K ≥ 0` satisfies the conclusion: `b = (0,0)`, `t = 1` sends `b` to
`(−K, 1)`, and `halfStrip` only ever moves *forward* along `vl = (1,0)`, while every
point of `B` at level `1` has `x ≥ 1 > 0 ≥ −K`.  The `ψ`-minimum of `B` **increases**
with the level here, and `hmono` is exactly the requirement that it not increase faster
than `−K`.  Hence the sign in `hK` is necessary, not an artifact.
-/

def Bslant : Set (ℤ × ℤ) := {q : ℤ × ℤ | 0 ≤ q.2 ∧ q.2 ≤ 1 ∧ q.2 ≤ q.1 ∧ q.1 ≤ q.2 + 2}

theorem mem_Bslant {q : ℤ × ℤ} :
    q ∈ Bslant ↔ (0 ≤ q.2 ∧ q.2 ≤ 1 ∧ q.2 ≤ q.1 ∧ q.1 ≤ q.2 + 2) := Iff.rfl

theorem Bslant_eq :
    Bslant = (↑({(0, 0), (1, 0), (2, 0), (1, 1), (2, 1), (3, 1)} : Finset (ℤ × ℤ))) := by
  ext q
  simp only [mem_Bslant, Finset.coe_insert, Set.mem_insert_iff, Finset.coe_singleton,
    Set.mem_singleton_iff, Prod.ext_iff]
  obtain ⟨x, y⟩ := q
  simp only
  omega

theorem finite_Bslant : Bslant.Finite := by rw [Bslant_eq]; exact Finset.finite_toSet _

theorem nonempty_Bslant : Bslant.Nonempty := ⟨(0, 0), by rw [mem_Bslant]; norm_num⟩

theorem posArea_Bslant : PosArea Bslant :=
  ⟨(0, 0), by rw [mem_Bslant]; norm_num, (1, 0), by rw [mem_Bslant]; norm_num,
    (1, 1), by rw [mem_Bslant]; norm_num, by decide⟩

theorem isLatticeConvexRegion_Bslant : IsLatticeConvexRegion Bslant := by
  refine ⟨{p : ℝ × ℝ | 0 ≤ p.2 ∧ p.2 ≤ 1 ∧ p.2 ≤ p.1 ∧ p.1 ≤ p.2 + 2}, ?_, ?_, ?_⟩
  · intro y hy z hz a b ha hb hab
    obtain ⟨hy1, hy2, hy3, hy4⟩ := hy
    obtain ⟨hz1, hz2, hz3, hz4⟩ := hz
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;>
      nlinarith
  · have he : {p : ℝ × ℝ | 0 ≤ p.2 ∧ p.2 ≤ 1 ∧ p.2 ≤ p.1 ∧ p.1 ≤ p.2 + 2}
        = {p : ℝ × ℝ | 0 ≤ p.2} ∩ ({p : ℝ × ℝ | p.2 ≤ 1}
          ∩ ({p : ℝ × ℝ | p.2 ≤ p.1} ∩ {p : ℝ × ℝ | p.1 ≤ p.2 + 2})) := rfl
    rw [he]
    exact (isClosed_le continuous_const continuous_snd).inter
      ((isClosed_le continuous_snd continuous_const).inter
        ((isClosed_le continuous_snd continuous_fst).inter
          (isClosed_le continuous_fst (continuous_snd.add continuous_const))))
  · ext z
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, toReal, mem_Bslant]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨by exact_mod_cast h1, by exact_mod_cast h2, by exact_mod_cast h3,
        by exact_mod_cast h4⟩
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨by exact_mod_cast h1, by exact_mod_cast h2, by exact_mod_cast h3,
        by exact_mod_cast h4⟩

theorem bot_edge_Bslant : -((0, -1) : ℤ × ℤ) ∈ E Bslant := by
  refine ⟨by decide, (1, 1), ⟨by rw [mem_Bslant]; norm_num, ?_⟩, (2, 1),
    ⟨by rw [mem_Bslant]; norm_num, ?_⟩, by decide⟩ <;>
  · rintro y ⟨-, h2, -, -⟩
    simp only [dot, Prod.fst_neg, Prod.snd_neg]
    omega

theorem top_edge_Bslant : ((0, -1) : ℤ × ℤ) ∈ E Bslant := by
  refine ⟨by decide, (0, 0), ⟨by rw [mem_Bslant]; norm_num, ?_⟩, (1, 0),
    ⟨by rw [mem_Bslant]; norm_num, ?_⟩, by decide⟩ <;>
  · rintro y ⟨h1, -, -, -⟩
    simp only [dot]
    omega

/-- **No `K ≥ 0` gives `hmono` on `Bslant`.**  Both `:774` edges are present
(`bot_edge_Bslant`, `top_edge_Bslant`), so this is not a hypothesis-weakening artifact. -/
theorem not_hmono_Bslant {K : ℤ} (hK : 0 ≤ K) :
    ¬ ∀ b ∈ Bslant, ∀ t : ℕ, (-1 : ℤ) ≤ dot ((0, -1) : ℤ × ℤ) b - (t : ℤ) →
        b + (t : ℤ) • (((0, 1) : ℤ × ℤ) - K • ((1, 0) : ℤ × ℤ))
          ∈ Nivat.LE2.halfStrip Bslant ((1, 0) : ℤ × ℤ) := by
  intro h
  obtain ⟨g, hg, s, hs⟩ :=
    h (0, 0) (by rw [mem_Bslant]; norm_num) 1 (by simp only [dot]; norm_num)
  rw [mem_Bslant] at hg
  have h1 := congrArg Prod.fst hs
  have h2 := congrArg Prod.snd hs
  simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul, Nat.cast_one] at h1 h2
  have h3 : (0 : ℤ) ≤ (s : ℤ) := Int.natCast_nonneg s
  omega

/-- **The answer to "is the sign of `K` necessary?": yes.**  Every hypothesis of
`exists_shear_hmono_of_edges_of_le` other than `hK` is satisfiable simultaneously with
"`hmono` fails for every `K ≥ 0`".  In particular no common `K` can be shared with
`L1StraddleWedge.exists_corner_shear`, whose `K` is `max M 0 ≥ 0`. -/
theorem no_nonneg_shear_hmono :
    ∃ (B : Set (ℤ × ℤ)) (vl u' nl : ℤ × ℤ) (cz : ℤ),
      (det u' vl = 1 ∨ det u' vl = -1) ∧
      B.Finite ∧ B.Nonempty ∧ PosArea B ∧ IsLatticeConvexRegion B ∧
      dot nl vl = 0 ∧ dot nl u' = -1 ∧ -nl ∈ E B ∧ nl ∈ E B ∧
      (∃ b₀ ∈ B, dot nl b₀ ≤ cz) ∧
      ∀ K : ℤ, 0 ≤ K → ¬ ∀ b ∈ B, ∀ t : ℕ, cz ≤ dot nl b - (t : ℤ) →
        b + (t : ℤ) • (u' - K • vl) ∈ Nivat.LE2.halfStrip B vl :=
  ⟨Bslant, (1, 0), (0, 1), (0, -1), -1, Or.inr (by decide), finite_Bslant, nonempty_Bslant,
    posArea_Bslant, isLatticeConvexRegion_Bslant, by decide, by decide,
    bot_edge_Bslant, top_edge_Bslant,
    ⟨(1, 1), by rw [mem_Bslant]; norm_num, by norm_num [dot]⟩,
    fun _ hK => not_hmono_Bslant hK⟩

/-! ### §11e  `hstrip` from occupancy, under a named height hypothesis

This closes `hstrip` (the binder of `RegionSteps.lean:2836`
`wedgeResidualR_of_cone_hmono_at_shear_of_argmax`) on top of **one** named debt,
`hheight`, and delivers it in the `∀ K ≤ K₀` form so that it composes with `hmono`.

**Where the two clauses of `hstrip` go.**  `hstrip_iff_levels` (§9) splits `hstrip` into a
*height* requirement and a *transverse `ψ`* requirement.

* the **height** clause is `hheight`, taken here as a hypothesis — see the warning below;
* the **`ψ`** clause dies under a sufficiently negative shear.  Writing `ψ_K = ψ + K·χ`
  (`dot_expNormal_shear`), the obligation at level `lev` is
  `ψ g + K·lev ≤ (ψ(z−a) + K·χ(z−a)) + (ψ bψ + K·χ bψ)`, and `hstrip_iff_levels`'s own
  window bound `−cz + χ(z−a) < lev` forces the coefficient of `K` on the right to be at
  least `1` smaller than on the left.  So for `K ≤ 0` the `K`-terms contribute at least
  `−K`, which swallows the bounded `ψ`-spread once `K` is negative enough.  This is the
  same mechanism as `exists_shear_hmono_of_edges_of_le` (§11c), which is why one `K₀`
  serves both.

⚠ **`hheight` is a hypothesis here; its producer is located but not landed.**  It is
`height_le_of_hstrip` (§9) read backwards: that lemma proves it is *necessary*, nothing in
this tree proves it.  It is **not** a Definition 3.2 consequence — `:402` compares
*parallel edge lengths* (`|w ∩ 𝒰| ≤ |ϖ ∩ 𝒯|`) and the `nℓ`-height of `B` is not an edge
length.  原文：`b3_colle2.txt:474-476`, item (ii) — "`B_i` contains both `A_{i-1}` and
`[-i+1,i-1]² ∩ ℋ(ℓ^{(-)})`", for **every** `i`.  So the producer is a *chain-construction*
fact (leaf A), not an envelope fact: `hheight` says `B` reaches far enough below its own top
to cover the occupancy window, and item (ii) is what makes `B_i` do that.  Left as a
hypothesis rather than weakened to something provable (hard rule 10).

⚠ **This route is superseded.**  At `K = 0` the companion hypothesis `hK` demands
`ψ(z−a) ≥ ψ`-width of `B`, i.e. `S` wider than `B`, which item (ii) itself makes false for
large `B`; and `no_nonneg_shear_hmono` (§11d) shows `hcorner`'s `K ≥ 0` cannot be met by a
negative shear.  The shear-free route is §11g/§11i.  Kept as the sharpest statement of how
far the shear does reach (`PROTOCOL.md` §14).

原文：`b3_colle2.txt:414` (`H_B(ℓ)`), `:780` (`𝓡_{ι-1}`), `:796`; `:774` for the two edges.
-/

/-- The scalar core of the `ψ` clause: the window bound `C + X < lev` makes the `K`-terms
contribute at least `−K`, and `hKz` is the requirement that `−K` cover the `ψ`-spread. -/
private theorem hstrip_arith {psiG psiZ psiB psiMin psiMax K X P lev C : ℤ}
    (hK0 : K ≤ 0) (hlo : C + X < lev) (hP : P ≤ C)
    (hg : psiG ≤ psiMax) (hb : psiMin ≤ psiB)
    (hKz : K ≤ psiZ + psiMin - psiMax) :
    psiG + K * lev ≤ (psiZ + K * X) + (psiB + K * P) := by
  have hs : X + P - lev ≤ -1 := by omega
  nlinarith [mul_nonneg (neg_nonneg.mpr hK0) (by linarith : (0 : ℤ) ≤ -(X + P - lev) - 1)]

/-- **`hstrip` at a parameterised shear.**  Every hypothesis except `hheight` is one this
file already discharges elsewhere; `hK0`/`hK` are the "`K` negative enough" bound, in the
same pointwise spelling as `exists_shear_hmono_of_edges_of_le`. -/
theorem hstrip_of_edges_of_height_of_le {B : Set (ℤ × ℤ)} {S : Finset (ℤ × ℤ)}
    {a nl : ℤ × ℤ} {cz K : ℤ}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hBfin : B.Finite) (hBne : B.Nonempty) (hBlc : IsLatticeConvexRegion B)
    (hnvl : dot nl vl = 0) (hnu : dot nl u' = -1)
    (hEbot : -nl ∈ E B) (hEtop : nl ∈ E B)
    (hczdef : cz = -suppVal B (-nl))
    (hheight : ∀ z ∈ S.erase a, dot nl (z - a) ≤ suppVal B nl + suppVal B (-nl) + 1)
    (hK0 : K ≤ 0)
    (hK : ∀ z ∈ S.erase a, ∀ x ∈ B, ∀ y ∈ B,
      K ≤ dot (expNormal u' vl) (z - a) + dot (expNormal u' vl) x
            - dot (expNormal u' vl) y) :
    ∀ w ∈ coneRegion B vl (u' - K • vl), dot nl w < cz →
      ∀ z ∈ S.erase a, cz ≤ dot nl (z + (w - a)) →
        z + (w - a) ∈ Nivat.LE2.halfStrip B vl := by
  classical
  have hvlP : Primitive vl := prim_iff_primitive.mp (prim_of_unimod hunimod)
  have hocc := occupancy_of_edges (vl := vl) (nl := nl) hBlc hvlP hnvl hEbot hEtop
  have hunimod' : det (u' - K • vl) vl = 1 ∨ det (u' - K • vl) vl = -1 := by
    rw [det_shear_right]; exact hunimod
  have hnu' : dot nl (u' - K • vl) = -1 := by
    rw [dot_sub, dot_zsmul, hnvl, hnu]; ring
  have hχ : ∀ x : ℤ × ℤ, dot nl x = - uCoord u' vl 0 x :=
    dot_eq_neg_uCoord hunimod hnvl hnu
  have hcz : ∀ b ∈ B, cz ≤ dot nl b := by
    intro b hb
    have h := le_suppVal hBfin hBne (n := -nl) hb
    rw [dot_neg_left] at h
    omega
  have hBne' : hBfin.toFinset.Nonempty := by
    obtain ⟨b, hb⟩ := hBne
    exact ⟨b, hBfin.mem_toFinset.mpr hb⟩
  obtain ⟨bmax, hbmaxF, hbmax⟩ :=
    hBfin.toFinset.exists_max_image (fun z => dot (expNormal u' vl) z) hBne'
  obtain ⟨bmin, hbminF, hbmin⟩ :=
    hBfin.toFinset.exists_min_image (fun z => dot (expNormal u' vl) z) hBne'
  obtain ⟨bψ, hbψF, hbψmin⟩ :=
    hBfin.toFinset.exists_min_image (fun z => dot (expNormal (u' - K • vl) vl) z) hBne'
  refine (hstrip_iff_levels (u' := u' - K • vl) (bψ := bψ) (a := a) (S := S)
    hunimod' hnvl hnu' hcz (hBfin.mem_toFinset.mp hbψF)
    (fun b hb => hbψmin b (hBfin.mem_toFinset.mpr hb))).mpr ?_
  intro z hz lev hlo hhi
  rw [uCoord_shear] at hlo
  obtain ⟨btop, hbtop, hbtopval⟩ := exists_suppVal_eq hBfin hBne (-nl)
  obtain ⟨bbot, hbbot, hbbotval⟩ := exists_suppVal_eq hBfin hBne nl
  rw [dot_neg_left] at hbtopval
  have h1 : ∃ b ∈ B, dot nl b ≤ -lev := ⟨btop, hbtop, by omega⟩
  have h2 : ∃ b ∈ B, -lev ≤ dot nl b := by
    refine ⟨bbot, hbbot, ?_⟩
    have hz' := hheight z hz
    have hza := hχ (z - a)
    omega
  obtain ⟨g, hgB, hgval⟩ := hocc (-lev) h1 h2
  have hgχ : uCoord u' vl 0 g = lev := by have := hχ g; omega
  refine ⟨g, hgB, by rw [uCoord_shear]; exact hgχ, ?_⟩
  rw [dot_expNormal_shear hunimod K g, dot_expNormal_shear hunimod K (z - a),
    dot_expNormal_shear hunimod K bψ, hgχ]
  have hbψB : bψ ∈ B := hBfin.mem_toFinset.mp hbψF
  have hPle : uCoord u' vl 0 bψ ≤ -cz := by
    have h := hcz bψ hbψB
    have := hχ bψ
    omega
  exact hstrip_arith hK0 hlo hPle (hbmax g (hBfin.mem_toFinset.mpr hgB))
    (hbmin bψ (hBfin.mem_toFinset.mpr hbψB))
    (hK z hz bmin (hBfin.mem_toFinset.mp hbminF) bmax (hBfin.mem_toFinset.mp hbmaxF))

/-- **`hmono` in `∀ K ≤ K₀` form.**  Same content as `exists_shear_hmono_of_edges_of_le`,
packaged so that it composes with `exists_shear_hstrip_of_edges_of_height`. -/
theorem exists_shear_hmono_forall_le {B : Set (ℤ × ℤ)} {nl : ℤ × ℤ} {cz : ℤ}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hBfin : B.Finite) (hBne : B.Nonempty) (hBlc : IsLatticeConvexRegion B)
    (hnvl : dot nl vl = 0) (hnu : dot nl u' = -1)
    (hEbot : -nl ∈ E B) (hEtop : nl ∈ E B)
    (hczB : ∃ b₀ ∈ B, dot nl b₀ ≤ cz) :
    ∃ K₀ : ℤ, ∀ K ≤ K₀, ∀ b ∈ B, ∀ t : ℕ, cz ≤ dot nl b - t →
      b + (t : ℤ) • (u' - K • vl) ∈ Nivat.LE2.halfStrip B vl := by
  classical
  have hBne' : hBfin.toFinset.Nonempty := by
    obtain ⟨b, hb⟩ := hBne
    exact ⟨b, hBfin.mem_toFinset.mpr hb⟩
  obtain ⟨bmax, hbmaxF, hbmax⟩ :=
    hBfin.toFinset.exists_max_image (fun z => dot (expNormal u' vl) z) hBne'
  obtain ⟨bmin, hbminF, hbmin⟩ :=
    hBfin.toFinset.exists_min_image (fun z => dot (expNormal u' vl) z) hBne'
  refine ⟨dot (expNormal u' vl) bmin - dot (expNormal u' vl) bmax, fun K hKle => ?_⟩
  refine exists_shear_hmono_of_edges_of_le hunimod hBfin hBne hBlc hnvl hnu hEbot hEtop
    hczB ?_
  intro x hx y hy
  have h1 := hbmin x (hBfin.mem_toFinset.mpr hx)
  have h2 := hbmax y (hBfin.mem_toFinset.mpr hy)
  linarith

/-- **The dispatched shape**: `hstrip` for every sufficiently negative shear, with the
height debt isolated in `hheight`.  The `∀ K ≤ K₀` form is what lets a single shear serve
`hstrip` and `hmono` at once — see `exists_shear_hstrip_and_hmono_of_height`. -/
theorem exists_shear_hstrip_of_edges_of_height {B : Set (ℤ × ℤ)} {S : Finset (ℤ × ℤ)}
    {a nl : ℤ × ℤ} {cz : ℤ}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hBfin : B.Finite) (hBne : B.Nonempty) (hBlc : IsLatticeConvexRegion B)
    (hnvl : dot nl vl = 0) (hnu : dot nl u' = -1)
    (hEbot : -nl ∈ E B) (hEtop : nl ∈ E B)
    (hczdef : cz = -suppVal B (-nl))
    (hheight : ∀ z ∈ S.erase a, dot nl (z - a) ≤ suppVal B nl + suppVal B (-nl) + 1) :
    ∃ K₀ : ℤ, ∀ K ≤ K₀,
      ∀ w ∈ coneRegion B vl (u' - K • vl), dot nl w < cz →
        ∀ z ∈ S.erase a, cz ≤ dot nl (z + (w - a)) →
          z + (w - a) ∈ Nivat.LE2.halfStrip B vl := by
  classical
  have hBne' : hBfin.toFinset.Nonempty := by
    obtain ⟨b, hb⟩ := hBne
    exact ⟨b, hBfin.mem_toFinset.mpr hb⟩
  obtain ⟨bmax, hbmaxF, hbmax⟩ :=
    hBfin.toFinset.exists_max_image (fun z => dot (expNormal u' vl) z) hBne'
  obtain ⟨bmin, hbminF, hbmin⟩ :=
    hBfin.toFinset.exists_min_image (fun z => dot (expNormal u' vl) z) hBne'
  rcases (S.erase a).eq_empty_or_nonempty with hemp | hSne
  · refine ⟨0, fun K _ w _ _ z hz => ?_⟩
    rw [hemp] at hz
    simp at hz
  obtain ⟨zmin, hzminF, hzmin⟩ :=
    (S.erase a).exists_min_image (fun z => dot (expNormal u' vl) (z - a)) hSne
  refine ⟨min 0 (dot (expNormal u' vl) (zmin - a) + dot (expNormal u' vl) bmin
      - dot (expNormal u' vl) bmax), fun K hKle => ?_⟩
  have hK0 : K ≤ 0 := le_trans hKle (min_le_left _ _)
  refine hstrip_of_edges_of_height_of_le hunimod hBfin hBne hBlc hnvl hnu hEbot hEtop
    hczdef hheight hK0 ?_
  intro z hz x hx y hy
  have h0 := le_trans hKle (min_le_right _ _)
  have h1 := hzmin z hz
  have h2 := hbmin x (hBfin.mem_toFinset.mpr hx)
  have h3 := hbmax y (hBfin.mem_toFinset.mpr hy)
  linarith

/-- **One shear serving both.**  The composite the consumer wants: a single `K` at which
`hstrip` and `hmono` hold simultaneously, given the height debt. -/
theorem exists_shear_hstrip_and_hmono_of_height {B : Set (ℤ × ℤ)} {S : Finset (ℤ × ℤ)}
    {a nl : ℤ × ℤ} {cz : ℤ}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hBfin : B.Finite) (hBne : B.Nonempty) (hBlc : IsLatticeConvexRegion B)
    (hnvl : dot nl vl = 0) (hnu : dot nl u' = -1)
    (hEbot : -nl ∈ E B) (hEtop : nl ∈ E B)
    (hczdef : cz = -suppVal B (-nl))
    (hheight : ∀ z ∈ S.erase a, dot nl (z - a) ≤ suppVal B nl + suppVal B (-nl) + 1) :
    ∃ K : ℤ,
      (∀ w ∈ coneRegion B vl (u' - K • vl), dot nl w < cz →
        ∀ z ∈ S.erase a, cz ≤ dot nl (z + (w - a)) →
          z + (w - a) ∈ Nivat.LE2.halfStrip B vl) ∧
      (∀ b ∈ B, ∀ t : ℕ, cz ≤ dot nl b - t →
        b + (t : ℤ) • (u' - K • vl) ∈ Nivat.LE2.halfStrip B vl) := by
  have hczB : ∃ b₀ ∈ B, dot nl b₀ ≤ cz := by
    obtain ⟨b₀, hb₀, hb₀eq⟩ := exists_suppVal_eq hBfin hBne (-nl)
    rw [dot_neg_left] at hb₀eq
    exact ⟨b₀, hb₀, by omega⟩
  obtain ⟨K₁, hK₁⟩ := exists_shear_hstrip_of_edges_of_height hunimod hBfin hBne hBlc
    hnvl hnu hEbot hEtop hczdef hheight
  obtain ⟨K₂, hK₂⟩ := exists_shear_hmono_forall_le hunimod hBfin hBne hBlc
    hnvl hnu hEbot hEtop hczB
  exact ⟨min K₁ K₂, hK₁ _ (min_le_left _ _), hK₂ _ (min_le_right _ _)⟩

/-! ### §11f  `hmono` at `K = 0` — what `hlean` does and does not give

`hlean` says `B`'s `μ`-leftmost point is attained at the `u'`-far level `cz`
(`μ := expNormal u' vl`, which is constant along `u'`-steps by `dot_expNormal_u'`).
Unfolding `mem_halfStrip_iff_coords`, `hmono` at `K = 0` is exactly

> for every `b ∈ B` and every level `L'` between `χ b` and `-cz`,
> `B` has a point at level `L'` with `μ` at most `μ b`.

**`hlean` alone does not give this**, because it says nothing about levels *existing*:
`Bcliff` below is finite, positive-area and lattice-convex, satisfies `hlean` exactly, and
still fails `hmono` at `K = 0` — its level `2` is **empty**.  A lattice-convex set may skip
a level (the slice interval there is shorter than `1` and misses every integer), and no
amount of `μ`-leaning repairs that.

The missing hypothesis is the one `:774` supplies and that `Bcliff` violates: its top face
is the single point `(0,3)`, so `-nℓ ∉ E Bcliff` (`not_top_edge_Bcliff`).  With both edges
present, occupancy (`occupancy_of_edges`) fills every level and the argument closes —
`hmono_of_lean_of_edges` below.  So `hlean` is the right idea and `Bcliff` locates the
exact gap in the dispatched signature, not in the idea.

原文：`b3_colle2.txt:774` (both edges), `:777` (`B` is `E(𝒮_φ)`-enveloped).
-/

def Bcliff : Set (ℤ × ℤ) :=
  {q : ℤ × ℤ | 0 ≤ q.2 ∧ 3 ≤ 3 * q.1 + q.2 ∧ 3 * q.1 + 2 * q.2 ≤ 6}

theorem mem_Bcliff {q : ℤ × ℤ} :
    q ∈ Bcliff ↔ (0 ≤ q.2 ∧ 3 ≤ 3 * q.1 + q.2 ∧ 3 * q.1 + 2 * q.2 ≤ 6) := Iff.rfl

theorem Bcliff_eq :
    Bcliff = (↑({(1, 0), (2, 0), (1, 1), (0, 3)} : Finset (ℤ × ℤ))) := by
  ext q
  simp only [mem_Bcliff, Finset.coe_insert, Set.mem_insert_iff, Finset.coe_singleton,
    Set.mem_singleton_iff, Prod.ext_iff]
  obtain ⟨x, y⟩ := q
  simp only
  omega

theorem finite_Bcliff : Bcliff.Finite := by rw [Bcliff_eq]; exact Finset.finite_toSet _

theorem nonempty_Bcliff : Bcliff.Nonempty := ⟨(1, 0), by rw [mem_Bcliff]; norm_num⟩

theorem posArea_Bcliff : PosArea Bcliff :=
  ⟨(1, 0), by rw [mem_Bcliff]; norm_num, (2, 0), by rw [mem_Bcliff]; norm_num,
    (0, 3), by rw [mem_Bcliff]; norm_num, by decide⟩

theorem isLatticeConvexRegion_Bcliff : IsLatticeConvexRegion Bcliff := by
  refine ⟨{p : ℝ × ℝ | 0 ≤ p.2 ∧ 3 ≤ 3 * p.1 + p.2 ∧ 3 * p.1 + 2 * p.2 ≤ 6}, ?_, ?_, ?_⟩
  · intro y hy z hz a b ha hb hab
    obtain ⟨hy1, hy2, hy3⟩ := hy
    obtain ⟨hz1, hz2, hz3⟩ := hz
    refine ⟨?_, ?_, ?_⟩ <;>
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;>
      nlinarith
  · have he : {p : ℝ × ℝ | 0 ≤ p.2 ∧ 3 ≤ 3 * p.1 + p.2 ∧ 3 * p.1 + 2 * p.2 ≤ 6}
        = {p : ℝ × ℝ | 0 ≤ p.2} ∩ ({p : ℝ × ℝ | 3 ≤ 3 * p.1 + p.2}
          ∩ {p : ℝ × ℝ | 3 * p.1 + 2 * p.2 ≤ 6}) := rfl
    rw [he]
    exact (isClosed_le continuous_const continuous_snd).inter
      ((isClosed_le continuous_const
          ((continuous_const.mul continuous_fst).add continuous_snd)).inter
        (isClosed_le ((continuous_const.mul continuous_fst).add
          (continuous_const.mul continuous_snd)) continuous_const))
  · ext z
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, toReal, mem_Bcliff]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨by exact_mod_cast h1, by exact_mod_cast h2, by exact_mod_cast h3⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨by exact_mod_cast h1, by exact_mod_cast h2, by exact_mod_cast h3⟩

/-- `μ = expNormal (0,1) (1,0) = (1,0)`, so `μ` is the first coordinate. -/
theorem dot_expNormal_cliff (q : ℤ × ℤ) :
    dot (expNormal ((0, 1) : ℤ × ℤ) ((1, 0) : ℤ × ℤ)) q = q.1 := by
  simp only [expNormal, det, dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- `Bcliff` satisfies `hlean` at `cz = -3`: `(0,3)` is its `μ`-minimum and sits at the
`u'`-far level. -/
theorem hlean_Bcliff :
    ∃ b ∈ Bcliff, dot ((0, -1) : ℤ × ℤ) b = -3 ∧
      ∀ c ∈ Bcliff, dot (expNormal ((0, 1) : ℤ × ℤ) ((1, 0) : ℤ × ℤ)) b
        ≤ dot (expNormal ((0, 1) : ℤ × ℤ) ((1, 0) : ℤ × ℤ)) c := by
  refine ⟨(0, 3), by rw [mem_Bcliff]; norm_num, by simp only [dot]; norm_num, ?_⟩
  intro c hc
  rw [mem_Bcliff] at hc
  rw [dot_expNormal_cliff, dot_expNormal_cliff]
  omega

/-- The hypothesis `Bcliff` violates: its top face is the single point `(0,3)`. -/
theorem not_top_edge_Bcliff : -((0, -1) : ℤ × ℤ) ∉ E Bcliff := by
  rintro ⟨-, x, hx, y, hy, hxy⟩
  have hx1 : x ∈ Bcliff := hx.1
  have hy1 : y ∈ Bcliff := hy.1
  have hx2 := hx.2 (0, 3) (by rw [mem_Bcliff]; norm_num)
  have hy2 := hy.2 (0, 3) (by rw [mem_Bcliff]; norm_num)
  rw [mem_Bcliff] at hx1 hy1
  simp only [dot, Prod.fst_neg, Prod.snd_neg] at hx2 hy2
  exact hxy (Prod.ext (by omega) (by omega))

/-- **`hmono` at `K = 0` fails on `Bcliff`**: level `2` is empty, so `(1,0) + 2•u'` has no
witness at all. -/
theorem not_hmono_Bcliff :
    ¬ ∀ b ∈ Bcliff, ∀ t : ℕ, (-3 : ℤ) ≤ dot ((0, -1) : ℤ × ℤ) b - (t : ℤ) →
        b + (t : ℤ) • ((0, 1) : ℤ × ℤ) ∈ Nivat.LE2.halfStrip Bcliff ((1, 0) : ℤ × ℤ) := by
  intro h
  obtain ⟨g, hg, s, hs⟩ :=
    h (1, 0) (by rw [mem_Bcliff]; norm_num) 2 (by simp only [dot]; norm_num)
  rw [mem_Bcliff] at hg
  have h1 := congrArg Prod.fst hs
  have h2 := congrArg Prod.snd hs
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h1 h2
  have h3 : (0 : ℤ) ≤ (s : ℤ) := Int.natCast_nonneg s
  omega

/-- **The dispatched `hmono_of_lean` signature is false as stated.**  Every hypothesis of it
is met by `Bcliff` — finite, lattice-convex, unimodular frame, `hperp`, `hstep`, `hlean` —
and the conclusion fails.  The hypothesis that is missing is `-nℓ ∈ E B`
(`not_top_edge_Bcliff`), i.e. exactly one half of `b3_colle2.txt:774`; with it, occupancy
holds and `hmono_of_lean_of_edges` goes through. -/
theorem not_hmono_of_lean :
    ∃ (B : Set (ℤ × ℤ)) (vl u' nl : ℤ × ℤ) (cz : ℤ),
      B.Finite ∧ B.Nonempty ∧ PosArea B ∧ IsLatticeConvexRegion B ∧
      (det u' vl = 1 ∨ det u' vl = -1) ∧
      dot nl vl = 0 ∧ dot nl u' = -1 ∧
      (∃ b ∈ B, dot nl b = cz ∧
        ∀ c ∈ B, dot (expNormal u' vl) b ≤ dot (expNormal u' vl) c) ∧
      ¬ ∀ b ∈ B, ∀ t : ℕ, cz ≤ dot nl b - (t : ℤ) →
          b + (t : ℤ) • u' ∈ Nivat.LE2.halfStrip B vl :=
  ⟨Bcliff, (1, 0), (0, 1), (0, -1), -3, finite_Bcliff, nonempty_Bcliff, posArea_Bcliff,
    isLatticeConvexRegion_Bcliff, Or.inr (by decide), by decide, by decide,
    hlean_Bcliff, not_hmono_Bcliff⟩

/-- `Bslant` fails `hlean`, as expected: its `μ`-minimum `(0,0)` sits at level `0`, while
`cz = -1` is the level `y = 1`.  So §11d and §11f are consistent — the two witnesses
refute different statements. -/
theorem not_hlean_Bslant :
    ¬ ∃ b ∈ Bslant, dot ((0, -1) : ℤ × ℤ) b = -1 ∧
      ∀ c ∈ Bslant, dot (expNormal ((0, 1) : ℤ × ℤ) ((1, 0) : ℤ × ℤ)) b
        ≤ dot (expNormal ((0, 1) : ℤ × ℤ) ((1, 0) : ℤ × ℤ)) c := by
  rintro ⟨b, hb, hlev, hmin⟩
  have h := hmin (0, 0) (by rw [mem_Bslant]; norm_num)
  rw [mem_Bslant] at hb
  rw [dot_expNormal_cliff, dot_expNormal_cliff] at h
  simp only [dot] at hlev
  omega

/-! ### §11g  `hmono` at `K = 0`, from `hlean` and the two `:774` edges

This is the shear-free `hmono`.  The two ingredients are exactly the two the witnesses of
§11d/§11f isolate:

* `hEbot`/`hEtop` (`b3_colle2.txt:774`, transported to `B` by `both_edges_of_enveloped`)
  make every level between the extremes non-empty (`occupancy_of_edges`);
* `hlean` (`B`'s `μ`-minimum sits at the `u'`-far level `cz`) makes the occupant's `μ`
  small enough.

**Proof.**  Fix `b` and `t ≥ 1`; write `μ` for `dot (expNormal u' vl)` and `χ` for the
`u'`-coordinate.  Occupancy gives `g₀ ∈ B` at the target level `χ b + t`.  If `μ g₀ ≤ μ b`
we are done.  Otherwise `μ g₀ > μ b`, and the target point `b + t•u'` — which has `χ` equal
to the target level and `μ` equal to `μ b`, because `dot μ u' = 0` — is an explicit convex
combination of `b`, `b*` and `g₀` with non-negative integer weights
`((Ls-Lb-t)·d, t·d, t·(μ b - μ b*))` over `N = t·(μ b - μ b*) + (Ls-Lb)·d`, `d = μ g₀ - μ b`.
Lattice convexity then puts it in `B` itself.  No boundary walk, no `⌈·⌉`, and no shear.
-/

/-- The scalar identity behind a three-point convex combination, grouped as
`(x,y)` first and then `z`. -/
private theorem combo3_coord {NR aR bR cR X Y Z G : ℝ}
    (hab : 0 < aR + bR) (hNpos : 0 < NR)
    (hG : NR * G = aR * X + bR * Y + cR * Z) :
    G = ((aR + bR) / NR) * ((aR / (aR + bR)) * X + (bR / (aR + bR)) * Y)
      + (cR / NR) * Z := by
  have h1 : aR + bR ≠ 0 := ne_of_gt hab
  have h2 : NR ≠ 0 := ne_of_gt hNpos
  have e1 : ((aR + bR) / NR) * ((aR / (aR + bR)) * X + (bR / (aR + bR)) * Y)
      + (cR / NR) * Z = (aR * X + bR * Y + cR * Z) / NR := by field_simp
  rw [e1, eq_div_iff h2]
  linarith [hG]

/-- Three-point version of `mem_of_convex_combo`. -/
private theorem mem_of_convex_combo3 {C : Set (ℝ × ℝ)} (hC : Convex ℝ C)
    {x y z g : ℤ × ℤ} {al be ga N : ℤ}
    (hx : toReal x ∈ C) (hy : toReal y ∈ C) (hz : toReal z ∈ C)
    (hal : 0 ≤ al) (hbe : 0 ≤ be) (hga : 0 ≤ ga) (hab : 0 < al + be)
    (hN : N = al + be + ga)
    (hg : N • g = al • x + be • y + ga • z) :
    toReal g ∈ C := by
  have hNpos : 0 < N := by omega
  have hab' : (0 : ℝ) < (al : ℝ) + (be : ℝ) := by exact_mod_cast hab
  have hN' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
  have hal' : (0 : ℝ) ≤ (al : ℝ) := by exact_mod_cast hal
  have hbe' : (0 : ℝ) ≤ (be : ℝ) := by exact_mod_cast hbe
  have hga' : (0 : ℝ) ≤ (ga : ℝ) := by exact_mod_cast hga
  have hNeq : (N : ℝ) = (al : ℝ) + (be : ℝ) + (ga : ℝ) := by exact_mod_cast hN
  have hR1 : ((al : ℝ) / ((al : ℝ) + (be : ℝ))) • toReal x
      + ((be : ℝ) / ((al : ℝ) + (be : ℝ))) • toReal y ∈ C :=
    hC hx hy (div_nonneg hal' (le_of_lt hab')) (div_nonneg hbe' (le_of_lt hab'))
      (by field_simp)
  have hR2 : (((al : ℝ) + (be : ℝ)) / (N : ℝ)) •
        (((al : ℝ) / ((al : ℝ) + (be : ℝ))) • toReal x
          + ((be : ℝ) / ((al : ℝ) + (be : ℝ))) • toReal y)
      + ((ga : ℝ) / (N : ℝ)) • toReal z ∈ C :=
    hC hR1 hz (div_nonneg (le_of_lt hab') (le_of_lt hN'))
      (div_nonneg hga' (le_of_lt hN')) (by field_simp; linarith [hNeq])
  have h1 := congrArg Prod.fst hg
  have h2 := congrArg Prod.snd hg
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h1 h2
  have hkey : toReal g = (((al : ℝ) + (be : ℝ)) / (N : ℝ)) •
        (((al : ℝ) / ((al : ℝ) + (be : ℝ))) • toReal x
          + ((be : ℝ) / ((al : ℝ) + (be : ℝ))) • toReal y)
      + ((ga : ℝ) / (N : ℝ)) • toReal z := by
    refine Prod.ext ?_ ?_
    · simp only [toReal, Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      exact combo3_coord hab' hN' (by exact_mod_cast h1)
    · simp only [toReal, Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      exact combo3_coord hab' hN' (by exact_mod_cast h2)
  rw [hkey]
  exact hR2

/-- **`hmono` at `K = 0`.**  The `hlean` route, with the hypothesis `Bcliff` showed to be
missing (`-nℓ ∈ E B`) restored.  `hBfin` is not needed: the edge hypotheses already give
attainment at both extremes. -/
theorem hmono_of_lean_of_edges {B : Set (ℤ × ℤ)} {nl : ℤ × ℤ} {cz : ℤ}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hBlc : IsLatticeConvexRegion B)
    (hnvl : dot nl vl = 0) (hnu : dot nl u' = -1)
    (hEbot : -nl ∈ E B) (hEtop : nl ∈ E B)
    (hlean : ∃ bs ∈ B, dot nl bs = cz ∧
      ∀ c ∈ B, dot (expNormal u' vl) bs ≤ dot (expNormal u' vl) c) :
    ∀ b ∈ B, ∀ t : ℕ, cz ≤ dot nl b - t →
      b + (t : ℤ) • u' ∈ Nivat.LE2.halfStrip B vl := by
  classical
  obtain ⟨bs, hbsB, hbslev, hbsmin⟩ := hlean
  have hvlP : Primitive vl := prim_iff_primitive.mp (prim_of_unimod hunimod)
  have hocc := occupancy_of_edges (vl := vl) (nl := nl) hBlc hvlP hnvl hEbot hEtop
  have hχ : ∀ x : ℤ × ℤ, dot nl x = - uCoord u' vl 0 x :=
    dot_eq_neg_uCoord hunimod hnvl hnu
  intro b hb t ht
  rcases Nat.eq_zero_or_pos t with rfl | htpos
  · exact ⟨b, hb, 0, by simp⟩
  have h1 : ∃ c ∈ B, dot nl c ≤ dot nl b - (t : ℤ) := ⟨bs, hbsB, by omega⟩
  have h2 : ∃ c ∈ B, dot nl b - (t : ℤ) ≤ dot nl c := ⟨b, hb, by omega⟩
  obtain ⟨g0, hg0B, hg0lev⟩ := hocc (dot nl b - (t : ℤ)) h1 h2
  have hχT : uCoord u' vl 0 (b + (t : ℤ) • u') = uCoord u' vl 0 b + (t : ℤ) := by
    have hrw : b + (t : ℤ) • u' = b + (0 : ℤ) • vl + (t : ℤ) • u' := by simp
    rw [hrw, uCoord_zero_add hunimod]
  have hψT : dot (expNormal u' vl) (b + (t : ℤ) • u') = dot (expNormal u' vl) b := by
    have hrw : b + (t : ℤ) • u' = b + (0 : ℤ) • vl + (t : ℤ) • u' := by simp
    rw [hrw, dot_expNormal_add hunimod]
    ring
  by_cases hcase : dot (expNormal u' vl) g0 ≤ dot (expNormal u' vl) b
  · refine (mem_halfStrip_iff_coords (u' := u') hunimod).mpr ⟨g0, hg0B, ?_, ?_⟩
    · rw [hχT]
      have ha := hχ g0
      have hbb := hχ b
      omega
    · rw [hψT]; exact hcase
  rw [not_le] at hcase
  -- the target point is itself in `B`
  set p := dot (expNormal u' vl) b with hp
  set ps := dot (expNormal u' vl) bs with hps
  set p0 := dot (expNormal u' vl) g0 with hp0
  set Lb := uCoord u' vl 0 b with hLb
  set Ls := uCoord u' vl 0 bs with hLs
  have hL0 : uCoord u' vl 0 g0 = Lb + (t : ℤ) := by
    have ha := hχ g0
    have hbb := hχ b
    omega
  have hAt : (t : ℤ) ≤ Ls - Lb := by
    have ha := hχ bs
    have hbb := hχ b
    omega
  have ht1 : (1 : ℤ) ≤ (t : ℤ) := by exact_mod_cast htpos
  have hd2 : 0 < p0 - p := by omega
  have hga0 : 0 ≤ p - ps := by
    have := hbsmin b hb
    omega
  have hbseq : bs = b + (ps - p) • vl + (Ls - Lb) • u' := eq_add_coords hunimod b bs
  have hg0eq : g0 = b + (p0 - p) • vl + (Lb + (t : ℤ) - Lb) • u' := by
    have h := eq_add_coords hunimod b g0
    rw [hL0] at h
    exact h
  have hcomb : ((t : ℤ) * (p - ps) + (Ls - Lb) * (p0 - p)) • (b + (t : ℤ) • u')
      = ((Ls - Lb - (t : ℤ)) * (p0 - p)) • b + ((t : ℤ) * (p0 - p)) • bs
        + ((t : ℤ) * (p - ps)) • g0 := by
    rw [hbseq, hg0eq]
    match_scalars <;> ring
  obtain ⟨C, hCconv, -, hBC⟩ := hBlc
  have hTB : b + (t : ℤ) • u' ∈ B := by
    rw [hBC] at hb hbsB hg0B ⊢
    refine Set.mem_preimage.mpr (mem_of_convex_combo3 hCconv hb hbsB hg0B
      (al := (Ls - Lb - (t : ℤ)) * (p0 - p)) (be := (t : ℤ) * (p0 - p))
      (ga := (t : ℤ) * (p - ps))
      (N := (t : ℤ) * (p - ps) + (Ls - Lb) * (p0 - p))
      (mul_nonneg (by omega) (by omega)) (mul_nonneg (by omega) (by omega))
      (mul_nonneg (by omega) (by omega)) ?_ (by ring) hcomb)
    have he : (Ls - Lb - (t : ℤ)) * (p0 - p) + (t : ℤ) * (p0 - p)
        = (Ls - Lb) * (p0 - p) := by ring
    rw [he]
    exact mul_pos (by omega) (by omega)
  exact ⟨b + (t : ℤ) • u', hTB, 0, by simp⟩

/-- **Envelopedness form of `hmono` at `K = 0`.**  The two edges sit on the generating set
`S` where `b3_colle2.txt:774` puts them, and `both_edges_of_enveloped` moves them to `B`;
`IsLatticeConvexRegion B` is the first conjunct of Definition 3.2, so it is `henv.1.1`.

⚠ `hlean` is a hypothesis **here**; it is no longer an orphan.  原文：`b3_colle2.txt:764`
(the `ℓ_i` enumerate the edge directions of `𝒮_φ`, `ℓ_{ι-1}` the cyclic predecessor of
`ℓ_ι = ℓ`) + `:777` (`B` is `E(𝒮_φ)`-enveloped) + `:402` (Definition 3.2, `|E(𝒯)| = |E(𝒰)|`),
which give `E B = E 𝒮_φ`.  §11i turns exactly that into `hlean`:
`hmono_of_adjacent_of_enveloped` is this theorem with `hlean` **produced** rather than
assumed.  Kept in this form for call sites that already have `hlean` on hand. -/
theorem hmono_of_lean_of_enveloped {S B : Set (ℤ × ℤ)} {nl : ℤ × ℤ} {cz : ℤ}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hESfin : (E S).Finite) (henv : Nivat.LE2.Enveloped S B)
    (hnvl : dot nl vl = 0) (hnu : dot nl u' = -1)
    (hEbot : -nl ∈ E S) (hEtop : nl ∈ E S)
    (hlean : ∃ bs ∈ B, dot nl bs = cz ∧
      ∀ c ∈ B, dot (expNormal u' vl) bs ≤ dot (expNormal u' vl) c) :
    ∀ b ∈ B, ∀ t : ℕ, cz ≤ dot nl b - t →
      b + (t : ℤ) • u' ∈ Nivat.LE2.halfStrip B vl :=
  let hE := both_edges_of_enveloped hESfin henv hEtop hEbot
  hmono_of_lean_of_edges hunimod henv.1.1 hnvl hnu hE.2 hE.1 hlean

/-! ## §11h  The `hmono` ladder, reduced to a single step

`mem_halfStrip_iff_coords` (§4) says membership in `H_B(ℓ)` is two coordinate conditions.
Specialised to the points `b + t•u'` that `hmono` is about, and with `dot nℓ = −χ`
(`dot_eq_neg_uCoord`, §2), it becomes a statement purely about the **per-level `ψ`-minimum**
`m(L) := min {ψ g : g ∈ B, dot nℓ g = L}`:

> `hmono` ⟺ `m(L − t) ≤ m(L)` for every level `L` of `B` and every `t` with `cz ≤ L − t`.

So the whole ladder is generated by its `t = 1` rung, and `levelDescend_of_step` is that
generation.  This is the reduction, landed on its own: it holds for *any* `B`, with no
convexity, no edges and no `hlean`, and it is what lets a single-step geometric input
(`level_step_of_lean`) produce the full `hmono` that
`RegionSteps.lean:2793 wedgeResidualR_of_cone_hmono_at_shear` binds. -/

/-- **`hmono`, decoded.**  `b + t•u' ∈ H_B(ℓ)` exactly when `B` already has a point `t`
levels lower whose `ψ` does not exceed `ψ b`.  No hypothesis on `B` at all: this is the
coordinate dictionary of §1–§2 and nothing else. -/
theorem mem_halfStrip_iff_level {B : Set (ℤ × ℤ)} {nl : ℤ × ℤ}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hnvl : dot nl vl = 0) (hnu : dot nl u' = -1) {b : ℤ × ℤ} {t : ℤ} :
    b + t • u' ∈ Nivat.LE2.halfStrip B vl ↔
      ∃ b' ∈ B, dot nl b' = dot nl b - t ∧
        dot (expNormal u' vl) b' ≤ dot (expNormal u' vl) b := by
  have hrw : b + t • u' = b + (0 : ℤ) • vl + t • u' := by simp
  have hχT : uCoord u' vl 0 (b + t • u') = uCoord u' vl 0 b + t := by
    rw [hrw, uCoord_zero_add hunimod]
  have hψT : dot (expNormal u' vl) (b + t • u') = dot (expNormal u' vl) b := by
    rw [hrw, dot_expNormal_add hunimod]; ring
  rw [mem_halfStrip_iff_coords hunimod, hχT, hψT]
  have hb2 := dot_eq_neg_uCoord hunimod hnvl hnu b
  constructor
  · rintro ⟨b', hb', h1, h2⟩
    exact ⟨b', hb', by have ha := dot_eq_neg_uCoord hunimod hnvl hnu b'; omega, h2⟩
  · rintro ⟨b', hb', h1, h2⟩
    exact ⟨b', hb', by have ha := dot_eq_neg_uCoord hunimod hnvl hnu b'; omega, h2⟩

/-- **The ladder from its rung.**  A single-step level descent generates the whole of
`hmono`'s level statement by induction on `t`.  Pure bookkeeping — no geometry. -/
theorem levelDescend_of_step {B : Set (ℤ × ℤ)} {nl : ℤ × ℤ} {cz : ℤ}
    (hstep : ∀ b ∈ B, cz ≤ dot nl b - 1 →
      ∃ b' ∈ B, dot nl b' = dot nl b - 1 ∧
        dot (expNormal u' vl) b' ≤ dot (expNormal u' vl) b) :
    ∀ b ∈ B, ∀ t : ℕ, cz ≤ dot nl b - (t : ℤ) →
      ∃ b' ∈ B, dot nl b' = dot nl b - (t : ℤ) ∧
        dot (expNormal u' vl) b' ≤ dot (expNormal u' vl) b := by
  intro b hb t
  induction t with
  | zero => intro _; exact ⟨b, hb, by simp, le_refl _⟩
  | succ k ih =>
      intro ht
      push_cast at ht
      obtain ⟨b', hb', hlev, hpsi⟩ := ih (by omega)
      obtain ⟨b'', hb'', hlev', hpsi'⟩ := hstep b' hb' (by omega)
      exact ⟨b'', hb'', by push_cast; omega, le_trans hpsi' hpsi⟩

/-- **The ladder, re-encoded.**  `levelDescend_of_step`'s conclusion is `hmono`. -/
theorem hmono_of_levelDescend {B : Set (ℤ × ℤ)} {nl : ℤ × ℤ} {cz : ℤ}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hnvl : dot nl vl = 0) (hnu : dot nl u' = -1)
    (hdesc : ∀ b ∈ B, ∀ t : ℕ, cz ≤ dot nl b - (t : ℤ) →
      ∃ b' ∈ B, dot nl b' = dot nl b - (t : ℤ) ∧
        dot (expNormal u' vl) b' ≤ dot (expNormal u' vl) b) :
    ∀ b ∈ B, ∀ t : ℕ, cz ≤ dot nl b - (t : ℤ) →
      b + (t : ℤ) • u' ∈ Nivat.LE2.halfStrip B vl := fun b hb t ht =>
  (mem_halfStrip_iff_level hunimod hnvl hnu).mpr (hdesc b hb t ht)

/-- **The rung itself, from `hlean`.**  The one step `L → L − 1`, which is where all the
geometry sits: `occupancy_of_edges` fills level `L − 1`, and if the point it produces is
too far along `vl` then `b + u'` is itself an integer convex combination of `b`, the
`ψ`-minimal `bs` of `hlean` and that point, hence in `B` by lattice convexity.

`hEbot`/`hEtop` are the `:774` edge pair; `hlean` is `:764`+`:777`, see
`hlean_of_noEdgeBetween` (§11i) for its producer. -/
theorem level_step_of_lean {B : Set (ℤ × ℤ)} {nl : ℤ × ℤ} {cz : ℤ}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hBlc : IsLatticeConvexRegion B)
    (hnvl : dot nl vl = 0) (hnu : dot nl u' = -1)
    (hEbot : -nl ∈ E B) (hEtop : nl ∈ E B)
    (hlean : ∃ bs ∈ B, dot nl bs = cz ∧
      ∀ c ∈ B, dot (expNormal u' vl) bs ≤ dot (expNormal u' vl) c) :
    ∀ b ∈ B, cz ≤ dot nl b - 1 →
      ∃ b' ∈ B, dot nl b' = dot nl b - 1 ∧
        dot (expNormal u' vl) b' ≤ dot (expNormal u' vl) b := by
  classical
  obtain ⟨bs, hbsB, hbslev, hbsmin⟩ := hlean
  have hvlP : Primitive vl := prim_iff_primitive.mp (prim_of_unimod hunimod)
  have hocc := occupancy_of_edges (vl := vl) (nl := nl) hBlc hvlP hnvl hEbot hEtop
  have hχ : ∀ x : ℤ × ℤ, dot nl x = - uCoord u' vl 0 x :=
    dot_eq_neg_uCoord hunimod hnvl hnu
  intro b hb ht
  have h1 : ∃ c ∈ B, dot nl c ≤ dot nl b - 1 := ⟨bs, hbsB, by omega⟩
  have h2 : ∃ c ∈ B, dot nl b - 1 ≤ dot nl c := ⟨b, hb, by omega⟩
  obtain ⟨g0, hg0B, hg0lev⟩ := hocc (dot nl b - 1) h1 h2
  by_cases hcase : dot (expNormal u' vl) g0 ≤ dot (expNormal u' vl) b
  · exact ⟨g0, hg0B, hg0lev, hcase⟩
  rw [not_le] at hcase
  set p := dot (expNormal u' vl) b with hp
  set ps := dot (expNormal u' vl) bs with hps
  set p0 := dot (expNormal u' vl) g0 with hp0
  set Lb := uCoord u' vl 0 b with hLb
  set Ls := uCoord u' vl 0 bs with hLs
  have hL0 : uCoord u' vl 0 g0 = Lb + 1 := by
    have ha := hχ g0
    have hbb := hχ b
    omega
  have hAt : (1 : ℤ) ≤ Ls - Lb := by
    have ha := hχ bs
    have hbb := hχ b
    omega
  have hd2 : 0 < p0 - p := by omega
  have hga0 : 0 ≤ p - ps := by
    have := hbsmin b hb
    omega
  have hbseq : bs = b + (ps - p) • vl + (Ls - Lb) • u' := eq_add_coords hunimod b bs
  have hg0eq : g0 = b + (p0 - p) • vl + (Lb + 1 - Lb) • u' := by
    have h := eq_add_coords hunimod b g0
    rw [hL0] at h
    exact h
  have hcomb : ((1 : ℤ) * (p - ps) + (Ls - Lb) * (p0 - p)) • (b + (1 : ℤ) • u')
      = ((Ls - Lb - 1) * (p0 - p)) • b + ((1 : ℤ) * (p0 - p)) • bs
        + ((1 : ℤ) * (p - ps)) • g0 := by
    rw [hbseq, hg0eq]
    match_scalars <;> ring
  obtain ⟨C, hCconv, -, hBC⟩ := hBlc
  have hTB : b + (1 : ℤ) • u' ∈ B := by
    rw [hBC] at hb hbsB hg0B ⊢
    refine Set.mem_preimage.mpr (mem_of_convex_combo3 hCconv hb hbsB hg0B
      (al := (Ls - Lb - 1) * (p0 - p)) (be := (1 : ℤ) * (p0 - p))
      (ga := (1 : ℤ) * (p - ps))
      (N := (1 : ℤ) * (p - ps) + (Ls - Lb) * (p0 - p))
      (mul_nonneg (by omega) (by omega)) (mul_nonneg (by omega) (by omega))
      (mul_nonneg (by omega) (by omega)) ?_ (by ring) hcomb)
    have he : (Ls - Lb - 1) * (p0 - p) + (1 : ℤ) * (p0 - p)
        = (Ls - Lb) * (p0 - p) := by ring
    rw [he]
    exact mul_pos (by omega) (by omega)
  have hrw : b + (1 : ℤ) • u' = b + (0 : ℤ) • vl + (1 : ℤ) • u' := by simp
  refine ⟨b + (1 : ℤ) • u', hTB, ?_, ?_⟩
  · have ha := hχ (b + (1 : ℤ) • u')
    have hbb := hχ b
    have hc : uCoord u' vl 0 (b + (1 : ℤ) • u') = Lb + 1 := by
      rw [hrw, uCoord_zero_add hunimod]
    omega
  · rw [hrw, dot_expNormal_add hunimod]
    omega

/-- **`hmono` at `K = 0`, factored through the single rung.**  Same statement as
`hmono_of_lean_of_edges`, proved the other way round: one geometric step plus the
induction of `levelDescend_of_step`.  Kept alongside the direct proof deliberately —
two independent routes to the same closure. -/
theorem hmono_of_lean_of_edges_via_step {B : Set (ℤ × ℤ)} {nl : ℤ × ℤ} {cz : ℤ}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hBlc : IsLatticeConvexRegion B)
    (hnvl : dot nl vl = 0) (hnu : dot nl u' = -1)
    (hEbot : -nl ∈ E B) (hEtop : nl ∈ E B)
    (hlean : ∃ bs ∈ B, dot nl bs = cz ∧
      ∀ c ∈ B, dot (expNormal u' vl) bs ≤ dot (expNormal u' vl) c) :
    ∀ b ∈ B, ∀ t : ℕ, cz ≤ dot nl b - (t : ℤ) →
      b + (t : ℤ) • u' ∈ Nivat.LE2.halfStrip B vl :=
  hmono_of_levelDescend hunimod hnvl hnu
    (levelDescend_of_step (level_step_of_lean hunimod hBlc hnvl hnu hEbot hEtop hlean))

/-! ## §11i  `hlean` from the adjacency of `:764` — the producer, located

原文：`b3_colle2.txt:764` (verbatim, restated at `:424` and `:541`):

> "Suppose `ℓ₁,…,ℓ_{2m} ⊂ ℝ²` is an enumeration of the oriented lines through the origin
> parallels to the edges of `𝒮_φ` where the edge parallel to `ℓ_{i+1}` is a **successor**
> of the edge parallel to `ℓ_i` and indices are taken modulo `2m`."

together with `:777` (`B` is `E(𝒮_φ)`-enveloped) and Definition 3.2 at `:402`
(`|E(𝒯)| = |E(𝒰)|`), which through `Enveloped.E_eq` give `E B = E 𝒮_φ`.

**Quantifier correspondence** (hard rule 7), for `hadj` below.  The indexing sentence says
`ℓ_{ι-1}` is the cyclic *predecessor* of `ℓ_ι = ℓ`: between the edge with normal `-nℓ`
(the `ℓ`-edge, at the bottom level `cz`) and the edge with direction `u' = v_{ℓ_{ι-1}}`
(normal `-μ`, the `ψ`-minimal edge) there is **no third edge of `𝒮_φ`**, hence — `E B = E 𝒮_φ`
— no third edge of `B`.  A normal strictly between the two is exactly an
`n = a•(-μ) + b•(-nℓ)` with `a, b > 0`, and in the dual basis that reads
`dot n vl = -a < 0` and `dot n u' = b > 0`.  So:

* `∀ n` ↔ "`E(𝒮_φ)` is enumerated by the `ℓ_i`, all `2m` of them";
* `dot n vl < 0 ∧ 0 < dot n u'` ↔ "strictly between `ℓ_{ι-1}` and `ℓ_ι`";
* `(face B n).Subsingleton` ↔ "is not an edge" (`IsEdge` is `Prim ∧ face.Nontrivial`).

No quantifier here is ours.  `noEdgeBetween_of_E` below is the bridge from the `E B`
spelling to the `face`-spelling used in the proof: they differ only by the primitive part.

**What this section buys.**  `hlean` stops being an orphan hypothesis: `hmono_of_adjacent`
derives it, so the `K = 0` route runs from Collé's own hypotheses.  Note that the derivation
needs **no convexity and no edge pair** — only finiteness and `hadj`. -/

/-- `dot` is additive in the *normal* argument. -/
private theorem dot_add_left (a b x : ℤ × ℤ) : dot (a + b) x = dot a x + dot b x := by
  simp only [dot, Prod.fst_add, Prod.snd_add]; ring

/-- Pairing differences read off in the two dual coordinates of `(vl, u')`:
`⟨f, z⟩ − ⟨f, z₀⟩ = (ψ z − ψ z₀)·⟨f, vl⟩ + (χ z − χ z₀)·⟨f, u'⟩`. -/
private theorem dot_sub_coords (hunimod : det u' vl = 1 ∨ det u' vl = -1) (f z z₀ : ℤ × ℤ) :
    dot f z - dot f z₀
      = (dot (expNormal u' vl) z - dot (expNormal u' vl) z₀) * dot f vl
        + (uCoord u' vl 0 z - uCoord u' vl 0 z₀) * dot f u' := by
  have h := eq_add_coords hunimod z₀ z
  set p := dot (expNormal u' vl) z with hp
  set p0 := dot (expNormal u' vl) z₀ with hp0
  set c := uCoord u' vl 0 z with hc
  set c0 := uCoord u' vl 0 z₀ with hc0
  conv_lhs => rw [h]
  rw [dot_add, dot_add, dot_zsmul, dot_zsmul]
  ring

/-- **The `E B` spelling of `hadj` implies the `face` spelling.**  A normal strictly between
the two edges has the same face as its primitive part, and the primitive part is still
strictly between; so if the face were an edge it would be an edge of `B` in the forbidden
cone. -/
theorem noEdgeBetween_of_E {B : Set (ℤ × ℤ)}
    (hE : ∀ n ∈ E B, ¬ (dot n vl < 0 ∧ 0 < dot n u')) :
    ∀ n : ℤ × ℤ, dot n vl < 0 → 0 < dot n u' → (face B n).Subsingleton := by
  intro n h1 h2
  by_contra hcon
  rw [Set.not_subsingleton_iff] at hcon
  have hn0 : n ≠ 0 := by
    intro h
    rw [h] at h2
    simp only [dot_zero_left] at h2
    exact lt_irrefl 0 h2
  obtain ⟨hp, g, hg, hgeq⟩ := primPart_spec hn0
  set m := primPart n with hm
  have hface : face B n = face B m := by
    calc face B n = face B (g • m) := by rw [← hgeq]
      _ = face B m := face_smul hg _
  have hvl : dot n vl = g * dot m vl := by rw [hgeq, dot_smul]
  have hu : dot n u' = g * dot m u' := by rw [hgeq, dot_smul]
  have h1' : dot m vl < 0 := by
    by_contra hcc
    rw [not_lt] at hcc
    nlinarith
  have h2' : 0 < dot m u' := by
    by_contra hcc
    rw [not_lt] at hcc
    nlinarith
  exact hE m ⟨hp, hface ▸ hcon⟩ ⟨h1', h2'⟩

/-- **`hlean`, produced.**  If no edge of `B` lies strictly between the `ℓ`-edge and the
`u'`-edge (`hadj`, the adjacency of `:764`), then the point of `B` at the bottom level
carrying the least `ψ` is a **global** `ψ`-minimum.

The proof is the "first edge counterclockwise" argument made finite: `v` is the bottom-level
point of least `ψ`; if some point has smaller `ψ`, pick among those the one `zs` minimising
the slope `(⟨nℓ,z⟩ − cz)/(ψ v − ψ z)`; the integer normal `f := (−d₂)•μ + (−d₁)•nℓ` with
`d₁ = ψ v − ψ zs`, `d₂ = ⟨nℓ,zs⟩ − cz` then attains its maximum over `B` at both `v` and
`zs`, so `face B f` is not a subsingleton — and `f` lies strictly in the forbidden cone,
since `⟨f,vl⟩ = −d₂ < 0` and `⟨f,u'⟩ = d₁ > 0`.

No convexity, no edge pair, no `PosArea`: finiteness and `hadj` alone. -/
theorem exists_lean_point_of_noEdgeBetween {B : Set (ℤ × ℤ)} {nl : ℤ × ℤ}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hBfin : B.Finite) (hBne : B.Nonempty)
    (hnvl : dot nl vl = 0) (hnu : dot nl u' = -1)
    (hadj : ∀ n : ℤ × ℤ, dot n vl < 0 → 0 < dot n u' → (face B n).Subsingleton) :
    ∃ bs ∈ B, (∀ c ∈ B, dot nl bs ≤ dot nl c) ∧
      (∀ c ∈ B, dot (expNormal u' vl) bs ≤ dot (expNormal u' vl) c) := by
  classical
  have hmemF : ∀ x : ℤ × ℤ, x ∈ hBfin.toFinset ↔ x ∈ B := fun x => hBfin.mem_toFinset
  have hFne : (hBfin.toFinset).Nonempty := by
    obtain ⟨x, hx⟩ := hBne
    exact ⟨x, (hmemF x).mpr hx⟩
  obtain ⟨v0, hv0F, hv0min0⟩ := (hBfin.toFinset).exists_min_image (fun z => dot nl z) hFne
  have hv0min : ∀ z ∈ hBfin.toFinset, dot nl v0 ≤ dot nl z := hv0min0
  obtain ⟨v, hvT, hvmin0⟩ :=
    ((hBfin.toFinset).filter (fun z => dot nl z = dot nl v0)).exists_min_image
      (fun z => dot (expNormal u' vl) z) ⟨v0, Finset.mem_filter.mpr ⟨hv0F, rfl⟩⟩
  have hvmin : ∀ z ∈ (hBfin.toFinset).filter (fun z => dot nl z = dot nl v0),
      dot (expNormal u' vl) v ≤ dot (expNormal u' vl) z := hvmin0
  obtain ⟨hvF, hvlev0⟩ := Finset.mem_filter.mp hvT
  have hvlev : dot nl v = dot nl v0 := hvlev0
  have hχ : ∀ x : ℤ × ℤ, dot nl x = - uCoord u' vl 0 x :=
    dot_eq_neg_uCoord hunimod hnvl hnu
  refine ⟨v, (hmemF v).mp hvF, fun c hc => ?_, fun c hc => ?_⟩
  · have h := hv0min c ((hmemF c).mpr hc); omega
  by_contra hlt0
  rw [not_le] at hlt0
  -- the set of points with smaller `ψ` is nonempty
  obtain ⟨zs, hzsS, hzsmin0⟩ :=
    ((hBfin.toFinset).filter
        (fun z => dot (expNormal u' vl) z < dot (expNormal u' vl) v)).exists_min_image
      (fun z => ((dot nl z - dot nl v0 : ℤ) : ℚ)
        / ((dot (expNormal u' vl) v - dot (expNormal u' vl) z : ℤ) : ℚ))
      ⟨c, Finset.mem_filter.mpr ⟨(hmemF c).mpr hc, hlt0⟩⟩
  obtain ⟨hzsF, hzslt0⟩ := Finset.mem_filter.mp hzsS
  have hzslt : dot (expNormal u' vl) zs < dot (expNormal u' vl) v := hzslt0
  -- `zs` is strictly above the bottom level: otherwise `hvmin` contradicts `hzslt`
  have hzsD : 0 < dot nl zs - dot nl v0 := by
    have hge := hv0min zs hzsF
    rcases lt_or_eq_of_le hge with h | h
    · omega
    · have := hvmin zs (Finset.mem_filter.mpr ⟨hzsF, h.symm⟩)
      omega
  -- the slope comparison, cross-multiplied into `ℤ`
  have hratio : ∀ z ∈ hBfin.toFinset,
      dot (expNormal u' vl) z < dot (expNormal u' vl) v →
      (dot nl zs - dot nl v0) * (dot (expNormal u' vl) v - dot (expNormal u' vl) z)
        ≤ (dot nl z - dot nl v0) * (dot (expNormal u' vl) v - dot (expNormal u' vl) zs) := by
    intro z hzF hzlt
    have h : ((dot nl zs - dot nl v0 : ℤ) : ℚ)
          / ((dot (expNormal u' vl) v - dot (expNormal u' vl) zs : ℤ) : ℚ)
        ≤ ((dot nl z - dot nl v0 : ℤ) : ℚ)
          / ((dot (expNormal u' vl) v - dot (expNormal u' vl) z : ℤ) : ℚ) :=
      hzsmin0 z (Finset.mem_filter.mpr ⟨hzF, hzlt⟩)
    have hden1 : (0 : ℚ) < ((dot (expNormal u' vl) v - dot (expNormal u' vl) zs : ℤ) : ℚ) := by
      have hh : (0 : ℤ) < dot (expNormal u' vl) v - dot (expNormal u' vl) zs := by omega
      exact_mod_cast hh
    have hden2 : (0 : ℚ) < ((dot (expNormal u' vl) v - dot (expNormal u' vl) z : ℤ) : ℚ) := by
      have hh : (0 : ℤ) < dot (expNormal u' vl) v - dot (expNormal u' vl) z := by omega
      exact_mod_cast hh
    rw [div_le_div_iff₀ hden1 hden2] at h
    exact_mod_cast h
  set d1 : ℤ := dot (expNormal u' vl) v - dot (expNormal u' vl) zs with hd1def
  set d2 : ℤ := dot nl zs - dot nl v0 with hd2def
  have hd1 : 0 < d1 := by omega
  have hd2 : 0 < d2 := hzsD
  set f : ℤ × ℤ := (-d2) • expNormal u' vl + (-d1) • nl with hfdef
  have hfvl : dot f vl = -d2 := by
    rw [hfdef, dot_add_left, dot_smul, dot_smul, Nivat.ColleReg.dot_expNormal_vl hunimod, hnvl]
    ring
  have hfu : dot f u' = d1 := by
    rw [hfdef, dot_add_left, dot_smul, dot_smul, Nivat.ColleReg.dot_expNormal_u', hnu]
    ring
  -- `f` is maximised at `v`
  have hmax : ∀ z ∈ B, dot f z ≤ dot f v := by
    intro z hz
    have hzF : z ∈ hBfin.toFinset := (hmemF z).mpr hz
    have hD : 0 ≤ dot nl z - dot nl v0 := by
      have h := hv0min z hzF; omega
    have hkey := dot_sub_coords hunimod f z v
    rw [hfvl, hfu] at hkey
    have hchi : uCoord u' vl 0 z - uCoord u' vl 0 v = -(dot nl z - dot nl v0) := by
      have ha := hχ z
      have hb := hχ v
      omega
    rw [hchi] at hkey
    rcases le_or_gt (dot (expNormal u' vl) v) (dot (expNormal u' vl) z) with hcase | hcase
    · have hA : 0 ≤ d2 * (dot (expNormal u' vl) z - dot (expNormal u' vl) v) :=
        mul_nonneg (by omega) (by omega)
      have hB : 0 ≤ d1 * (dot nl z - dot nl v0) := mul_nonneg (by omega) hD
      linarith [hkey, hA, hB]
    · linarith [hkey, hratio z hzF hcase]
  -- and `zs` attains the same value
  have hzseq : dot f zs = dot f v := by
    have hkey := dot_sub_coords hunimod f zs v
    rw [hfvl, hfu] at hkey
    have hchi : uCoord u' vl 0 zs - uCoord u' vl 0 v = -d2 := by
      have ha := hχ zs
      have hb := hχ v
      omega
    have e1 : dot (expNormal u' vl) zs - dot (expNormal u' vl) v = -d1 := by omega
    rw [hchi, e1] at hkey
    linarith [hkey]
  have hvface : v ∈ face B f := ⟨(hmemF v).mp hvF, fun y hy => hmax y hy⟩
  have hzsface : zs ∈ face B f :=
    ⟨(hmemF zs).mp hzsF, fun y hy => by rw [hzseq]; exact hmax y hy⟩
  have hne : zs ≠ v := by
    intro h
    rw [h] at hzslt
    exact lt_irrefl _ hzslt
  exact hne (hadj f (by omega) (by omega) hzsface hvface)

/-- **`hlean` in the shape `hmono_of_lean_of_edges` binds it.**  `cz` is any level that is a
minimum of `dot nℓ` on `B` and is attained. -/
theorem hlean_of_noEdgeBetween {B : Set (ℤ × ℤ)} {nl : ℤ × ℤ} {cz : ℤ}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hBfin : B.Finite) (hBne : B.Nonempty)
    (hnvl : dot nl vl = 0) (hnu : dot nl u' = -1)
    (hcz : ∀ c ∈ B, cz ≤ dot nl c) (hczmem : ∃ b ∈ B, dot nl b = cz)
    (hadj : ∀ n : ℤ × ℤ, dot n vl < 0 → 0 < dot n u' → (face B n).Subsingleton) :
    ∃ bs ∈ B, dot nl bs = cz ∧
      ∀ c ∈ B, dot (expNormal u' vl) bs ≤ dot (expNormal u' vl) c := by
  obtain ⟨bs, hbsB, hbsmin, hbspsi⟩ :=
    exists_lean_point_of_noEdgeBetween hunimod hBfin hBne hnvl hnu hadj
  obtain ⟨b0, hb0B, hb0lev⟩ := hczmem
  exact ⟨bs, hbsB, le_antisymm (by have := hbsmin b0 hb0B; omega) (hcz bs hbsB), hbspsi⟩

/-- **`hmono` at `K = 0` from Collé's hypotheses, with no orphan left.**  The `:774` edge
pair, the `:764` adjacency, and lattice convexity; `hlean` is produced, not assumed.

This is the statement `RegionSteps.lean:2793 wedgeResidualR_of_cone_hmono_at_shear` binds as
`hmono`, at `K = 0` (no shear). -/
theorem hmono_of_adjacent_of_edges {B : Set (ℤ × ℤ)} {nl : ℤ × ℤ} {cz : ℤ}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hBfin : B.Finite) (hBne : B.Nonempty) (hBlc : IsLatticeConvexRegion B)
    (hnvl : dot nl vl = 0) (hnu : dot nl u' = -1)
    (hEbot : -nl ∈ E B) (hEtop : nl ∈ E B)
    (hcz : ∀ c ∈ B, cz ≤ dot nl c) (hczmem : ∃ b ∈ B, dot nl b = cz)
    (hadj : ∀ n ∈ E B, ¬ (dot n vl < 0 ∧ 0 < dot n u')) :
    ∀ b ∈ B, ∀ t : ℕ, cz ≤ dot nl b - (t : ℤ) →
      b + (t : ℤ) • u' ∈ Nivat.LE2.halfStrip B vl :=
  hmono_of_lean_of_edges hunimod hBlc hnvl hnu hEbot hEtop
    (hlean_of_noEdgeBetween hunimod hBfin hBne hnvl hnu hcz hczmem (noEdgeBetween_of_E hadj))

/-- **Envelopedness form.**  The `:774` edge pair and the `:764` adjacency both live on the
generating set `𝒮_φ`; `E B = E 𝒮_φ` (`Enveloped.E_eq`, via `:402`) moves them to `B`. -/
theorem hmono_of_adjacent_of_enveloped {S B : Set (ℤ × ℤ)} {nl : ℤ × ℤ} {cz : ℤ}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hESfin : (E S).Finite) (henv : Nivat.LE2.Enveloped S B)
    (hBfin : B.Finite) (hBne : B.Nonempty)
    (hnvl : dot nl vl = 0) (hnu : dot nl u' = -1)
    (hEbot : -nl ∈ E S) (hEtop : nl ∈ E S)
    (hcz : ∀ c ∈ B, cz ≤ dot nl c) (hczmem : ∃ b ∈ B, dot nl b = cz)
    (hadj : ∀ n ∈ E S, ¬ (dot n vl < 0 ∧ 0 < dot n u')) :
    ∀ b ∈ B, ∀ t : ℕ, cz ≤ dot nl b - (t : ℤ) →
      b + (t : ℤ) • u' ∈ Nivat.LE2.halfStrip B vl := by
  have hEeq : E B = E S := Nivat.LE2.Enveloped.E_eq hESfin henv
  have hE := both_edges_of_enveloped hESfin henv hEtop hEbot
  exact hmono_of_adjacent_of_edges hunimod hBfin hBne henv.1.1 hnvl hnu hE.2 hE.1 hcz hczmem
    (fun n hn => hadj n (hEeq ▸ hn))

/-! ### §11j  The consistency check: `hadj` is exactly what `Bslant` violates

`not_hlean_Bslant` (§11f) says `Bslant` fails `hlean`.  `exists_lean_point_of_noEdgeBetween`
proves `hlean` from `hadj` alone, so `Bslant` **must** violate `hadj` — and it does, at the
edge `(-1,1)` running from `(0,0)` to `(1,1)`, which is strictly between the `ℓ`-edge and
the `u'`-edge.  Two things follow, both of them kernel facts rather than readings:

* `hadj` is not vacuous — it excludes a set that satisfies every other hypothesis of
  `hmono_of_adjacent_of_edges`, including the `:774` edge pair;
* the `Bslant` witness and §11i are consistent: they are statements about different sets of
  hypotheses, the second of which `Bslant` fails. -/

/-- `(-1,1)` is an edge of `Bslant`: `-x + y` is maximal (`= 0`) exactly on `(0,0)`, `(1,1)`. -/
theorem edge_between_Bslant : ((-1, 1) : ℤ × ℤ) ∈ E Bslant := by
  refine ⟨by decide, (0, 0), ⟨by rw [mem_Bslant]; norm_num, ?_⟩, (1, 1),
    ⟨by rw [mem_Bslant]; norm_num, ?_⟩, by decide⟩ <;>
  · rintro y ⟨-, -, h3, -⟩
    simp only [dot]
    omega

/-- **`Bslant` violates `hadj`.**  With `vl = (1,0)`, `u' = (0,1)` — the instantiation of
`not_hlean_Bslant` — the normal `(-1,1)` lies strictly in the forbidden cone
(`dot n vl = -1 < 0`, `dot n u' = 1 > 0`) and exposes an edge. -/
theorem not_noEdgeBetween_Bslant :
    ¬ ∀ n : ℤ × ℤ, dot n ((1, 0) : ℤ × ℤ) < 0 → 0 < dot n ((0, 1) : ℤ × ℤ) →
      (face Bslant n).Subsingleton := by
  intro h
  have hsub := h (-1, 1) (by simp only [dot]; norm_num) (by simp only [dot]; norm_num)
  obtain ⟨-, a, ha, b, hb, hab⟩ := edge_between_Bslant
  exact hab (hsub ha hb)

/-! ### §11k  The unimodular frame attached to the line `ℓ`

`RegionSteps.wedgeResidualR_of_case1_of_cone` binds `hprim`, `hperp`, `hnu` and `hunimod`
together.  All four are lattice arithmetic once `vl` is primitive, and the Bézout step is
already in the tree — `Primitive.exists_dual` (`Defs/Config.lean:163`) and
`eq_or_neg_of_prim_of_det_eq_zero` (`LatticeEdges.lean:133`).  Nothing below re-proves either;
`exists_frame_det_one` uses the Bézout pair of `Primitive vl` directly, which is the same
three-line argument `Primitive.exists_dual` performs, specialised to the sign we need.

**The sign question, answered.**  The four conditions do *not* leave the branch of `hunimod`
free.  With `Prim vl` and `Prim nℓ`, `dot nℓ vl = 0` forces `nℓ = ±(-vl.2, vl.1)`, and then
`dot nℓ u' = -1` pins the branch, because

```
dot (-vl.2, vl.1) u' = -vl.2 * u'.1 + vl.1 * u'.2 = -(u'.1 * vl.2 - u'.2 * vl.1) = -det u' vl.
```

That identity is exact, not up to sign: `dot nℓ u' = -1` and `det u' vl = 1` are the *same*
equation when `nℓ = (-vl.2, vl.1)`.  Hence

* `nℓ = (-vl.2, vl.1)`   ⟹  `det u' vl = 1`  (and this `nℓ` is `perp vl` in the usual
  counterclockwise convention);
* `nℓ = (vl.2, -vl.1)`   ⟹  `det u' vl = -1`.

So the branch is decided by the **orientation of `nℓ` relative to `vl`**, never by the choice
of `u'`: shearing `u' ↦ u' - K•vl` moves neither `dot nℓ u'` (because `dot nℓ vl = 0`) nor
`det u' vl` (`det_shear_right`).  `exists_frame` is free to choose `nℓ`, so it takes the first
row and lands the `det u' vl = 1` branch — **that is the branch the consumer will see.**
`exists_u'_of_perp` keeps the caller's `nℓ`, which on the chain is the edge normal of `ℓ` and
is *not* ours to choose, so it can only report the disjunction.

No new `Prop` is introduced here (so hard rule 7 has nothing to bind): `vl`, `nℓ`, `u'` are the
existing `ℓ`-direction, `ℓ`-normal and complement of `b3_colle2.txt:607` and `:780`; this
section supplies witnesses for hypotheses that are already stated elsewhere. -/

/-- **The frame in the orientation that gives `det u' vl = 1`.**  For primitive `vl`, the
normal `(-vl.2, vl.1)` admits a `u'` with `dot (-vl.2, vl.1) u' = -1` *and* `det u' vl = 1`.
The two conclusions are the same equation (see the section note); both are stated because the
consumer's binders are spelled separately. -/
theorem exists_frame_det_one {vl : ℤ × ℤ} (hvl_prim : Primitive vl) :
    ∃ u' : ℤ × ℤ, dot ((-vl.2, vl.1) : ℤ × ℤ) u' = -1 ∧ det u' vl = 1 := by
  obtain ⟨c, d, hcd⟩ := hvl_prim
  refine ⟨(d, -c), ?_, ?_⟩
  · show -vl.2 * d + vl.1 * -c = -1
    linear_combination -hcd
  · show d * vl.2 - -c * vl.1 = 1
    linear_combination hcd

/-- **The frame at a *given* edge normal.**  If `nℓ` is primitive and orthogonal to the
primitive direction `vl`, some `u'` completes it: `dot nℓ u' = -1` with `det u' vl = ±1`.

Keeping `nℓ` fixed is what the chain needs — there `nℓ` is the edge normal of `ℓ`, pinned by
`Case1`, so a lemma that manufactures its own `nℓ` would be proving a different statement
(hard rule 10).  The price of not choosing `nℓ` is the disjunction: which branch holds is
decided by `nℓ`'s orientation, as recorded in the section note. -/
theorem exists_u'_of_perp {vl nℓ : ℤ × ℤ} (hvl_prim : Primitive vl) (hnprim : Prim nℓ)
    (hperp : dot nℓ vl = 0) :
    ∃ u' : ℤ × ℤ, dot nℓ u' = -1 ∧ (det u' vl = 1 ∨ det u' vl = -1) := by
  obtain ⟨u', hnu, hdet⟩ := exists_frame_det_one hvl_prim
  have hp : Prim ((-vl.2, vl.1) : ℤ × ℤ) := prim_iff_primitive.mpr hvl_prim.symm.neg_left
  have hperp' : nℓ.1 * vl.1 + nℓ.2 * vl.2 = 0 := hperp
  have hd : det ((-vl.2, vl.1) : ℤ × ℤ) nℓ = 0 := by
    show -vl.2 * nℓ.2 - vl.1 * nℓ.1 = 0
    linear_combination -hperp'
  rcases eq_or_neg_of_prim_of_det_eq_zero hp hnprim hd with h | h
  · exact ⟨u', by rw [h]; exact hnu, Or.inl hdet⟩
  · have h1 : nℓ.1 = vl.2 := by rw [h]; simp
    have h2 : nℓ.2 = -vl.1 := by rw [h]; simp
    have hnu' : -vl.2 * u'.1 + vl.1 * u'.2 = -1 := hnu
    have hdet' : u'.1 * vl.2 - u'.2 * vl.1 = 1 := hdet
    refine ⟨-u', ?_, Or.inr ?_⟩
    · show nℓ.1 * -u'.1 + nℓ.2 * -u'.2 = -1
      linear_combination hnu' - u'.1 * h1 - u'.2 * h2
    · show -u'.1 * vl.2 - -u'.2 * vl.1 = -1
      linear_combination -hdet'

/-- **`hprim` / `hperp` / `hnu` / `hunimod`, all four at once, from `Primitive vl` alone.**

Consumer: `Nivat.ColleReg.wedgeResidualR_of_case1_of_cone` (`RegionSteps.lean`), which binds
exactly these four.  The witness is `nℓ = (-vl.2, vl.1)`, so the `hunimod` branch that actually
occurs is `det u' vl = 1` — see `exists_frame_det_one` if the consumer wants it without the
disjunction. -/
theorem exists_frame {vl : ℤ × ℤ} (hvl_prim : Primitive vl) :
    ∃ u' nℓ : ℤ × ℤ, Prim nℓ ∧ dot nℓ vl = 0 ∧ dot nℓ u' = -1 ∧
      (det u' vl = 1 ∨ det u' vl = -1) := by
  obtain ⟨u', hnu, hdet⟩ := exists_frame_det_one hvl_prim
  refine ⟨u', (-vl.2, vl.1), prim_iff_primitive.mpr hvl_prim.symm.neg_left, ?_, hnu, Or.inl hdet⟩
  show -vl.2 * vl.1 + vl.1 * vl.2 = 0
  ring

/-! ### §11l  `hadj` at a free `u'` is a shear normalisation

`hadj` — the binder of `hmono_of_adjacent_of_edges` / `_of_enveloped` (§11i) — says no edge
normal of `S` lies strictly inside the cone `{dot · vl < 0} ∩ {0 < dot · u'}`.  At a **pinned**
`u'` that is a real geometric restriction: §11j exhibits `Bslant`, which satisfies every other
hypothesis and fails `hadj` at the edge `(-1,1)`.  But `u'` is constrained only by `hunimod`,
which the shear `u' ↦ u' − K•vl` preserves (`det_shear_right`, `:140`), and by `hnu`, which the
shear preserves too whenever `dot nℓ vl = 0` (`dot_shear_right`, below).  Under the shear the
cone rotates, and once `K` is negative enough every edge normal on the `dot n vl < 0` side
leaves it:

```
dot n (u0 − K•vl) = dot n u0 − K · dot n vl,   and on that branch  dot n vl ≤ −1,
```

so bounding `dot n u0` above by some `M ≥ 0` over the finite set `E S` makes every `K ≤ −M`
work.  Finiteness of `E S` is the entire content; no geometry enters.

**The `K` is not canonical, and that is the useful part.**  The admissible set is a
*downward-closed half-line* `{K : K ≤ K₀}`, and `adjacent_of_shear_le` is stated that way on
purpose: §11c's bound `hK` (`exists_shear_hmono_of_edges_of_le`, `:1123`) is downward-closed in
`K` as well, so the two can be met at one `K` by taking the smaller — which is exactly the
"`hmono` and `hcorner` at the same `K`" obstruction §11c was written for.  A bare `∃ K` would
have lost that.

⚠ **Read this together with `not_exists_shear_hmono` (`:855`).**  Shearing is not a universal
solvent: occupancy is shear-*invariant* (`uCoord_shear`, `:712`), so the unrestricted
`∃ K, hmono` is false.  What the shear can normalise is the `ψ`-side condition only, which is
what `hadj` is.

原文：no new `Prop`.  `b3_colle2.txt:764` fixes `ℓ_{ι-1}` as the cyclic *predecessor* edge of
`ℓ_ι`; `hadj` is that adjacency written without a cyclic order (§11i), and the shear is how a
*free* `u'` is moved onto the predecessor side.  ⚠ The shear is the only available reading:
`u'` cannot literally be `v_{ℓ_{ι-1}}`, because for a pinned predecessor direction `hunimod`
fails outright — the reading recorded at `L1Assemble.lean:2115-2126` gives `vl = (2,1)`,
`v_{ℓ_{ι-1}} = (-1,2)`, `det = -5`.  So `hadj` can never be "`u'` *is* the adjacent edge"; it
is at most "`u'` is on the adjacent side", and that is a normalisation. -/

/-- The shear `u' ↦ u' − K•vl` does not move `dot nℓ ·` when `nℓ ⟂ vl`, so `hnu` transfers.
Companion to `det_shear_right` (`:140`), which does the same for `hunimod`. -/
theorem dot_shear_right {nl : ℤ × ℤ} (hnvl : dot nl vl = 0) (u0 : ℤ × ℤ) (K : ℤ) :
    dot nl (u0 - K • vl) = dot nl u0 := by
  have hs : dot nl (K • vl) = K * dot nl vl := by
    simp only [dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
  rw [dot_sub, hs, hnvl, mul_zero, sub_zero]

/-- **`hadj` holds at every sufficiently negative shear.**  `M` is any nonnegative upper bound
for `dot · u0` on `E S`; every `K ≤ −M` then puts all of `E S` outside the cone.

Stated with `K` as a parameter and the bound explicit — *not* as `∃ K` — because the admissible
`K` form a downward-closed half-line, and the consumer must satisfy §11c's `hK` at the same
`K`.  See the section note. -/
theorem adjacent_of_shear_le {S : Set (ℤ × ℤ)} {u0 : ℤ × ℤ} {M K : ℤ}
    (hM0 : 0 ≤ M) (hM : ∀ n ∈ E S, dot n vl < 0 → dot n u0 ≤ M) (hK : K ≤ -M) :
    ∀ n ∈ E S, ¬ (dot n vl < 0 ∧ 0 < dot n (u0 - K • vl)) := by
  rintro n hn ⟨h1, h2⟩
  have hexp : dot n (u0 - K • vl) = dot n u0 - K * dot n vl := by
    simp only [dot, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  rw [hexp] at h2
  have ha := hM n hn h1
  have step1 : -M * dot n vl ≤ K * dot n vl :=
    mul_le_mul_of_nonpos_right hK (le_of_lt h1)
  have step2 : (0 : ℤ) ≤ M * (-dot n vl - 1) := mul_nonneg hM0 (by omega)
  linarith

/-- **The downward-closed shear statement.**  Only `(E S).Finite` is used. -/
theorem exists_shear_adjacent_le {S : Set (ℤ × ℤ)} {u0 : ℤ × ℤ} (hESfin : (E S).Finite) :
    ∃ K₀ : ℤ, ∀ K : ℤ, K ≤ K₀ →
      ∀ n ∈ E S, ¬ (dot n vl < 0 ∧ 0 < dot n (u0 - K • vl)) := by
  obtain ⟨M0, hM0⟩ :=
    (((hESfin.subset (Set.sep_subset (E S) (fun n => dot n vl < 0))).image
      (fun n => dot n u0))).bddAbove
  refine ⟨-(max 0 M0), fun K hK => adjacent_of_shear_le (le_max_left _ _) (fun n hn h1 => ?_) hK⟩
  exact le_trans (hM0 ⟨n, ⟨hn, h1⟩, rfl⟩) (le_max_right _ _)

/-- **The dispatched signature.**  The bare existential, a corollary of the downward-closed
form.  Prefer `exists_shear_adjacent_le` when the same `K` has to serve another constraint. -/
theorem exists_shear_adjacent {S : Set (ℤ × ℤ)} {u0 : ℤ × ℤ} (hESfin : (E S).Finite) :
    ∃ K : ℤ, ∀ n ∈ E S, ¬ (dot n vl < 0 ∧ 0 < dot n (u0 - K • vl)) := by
  obtain ⟨K₀, hK₀⟩ := exists_shear_adjacent_le (vl := vl) (u0 := u0) hESfin
  exact ⟨K₀, hK₀ K₀ le_rfl⟩

/-! ### §11m  One shear serving `hmono` and `hadj` at once

Both constraints on `K` are downward-closed, so `min` meets them together.  This is the
declaration the §11l note described and did not state.

🔴 **The `K` produced here is `≤ 0`, and it is therefore NOT shareable with
`L1StraddleWedge.exists_corner_shear`.**  This is not a limitation of the proof; the two
constraints run in *opposite* directions and the clash is exact:

* `hmono` is **downward**-closed — `exists_shear_hmono_forall_le` (`:1585`) returns
  `K₀ = ψ bmin − ψ bmax ≤ 0`, so every `K` it licenses is `≤ 0`, with equality only when `B`
  is `ψ`-constant;
* `hadj` is **downward**-closed — `adjacent_of_shear_le` needs `K ≤ −M` with `M ≥ 0`;
* `hcorner` is **upward**-closed — `L1StraddleWedge.exists_corner_shear_of_le` (`:466`) is
  literally `∃ M a, a ∈ S ∧ ∀ K, M ≤ K → …`, and its `M` is `max _ 0 ≥ 0`; the non-`_of_le`
  form `exists_corner_shear` (`:424`) instantiates it at `max _ 0`.

So the admissible sets are `[M, ∞)` with `M ≥ 0` against `(−∞, −M']` with `M' ≥ 0`.  They
intersect only if `M = M' = 0`, and `no_nonneg_shear_hmono` (`:1452`) is a kernel witness that
`K = 0` fails for `hmono` on a `B` satisfying *every* hypothesis of the present lemma
(`hunimod`, finiteness, nonemptiness, `PosArea`, `IsLatticeConvexRegion`, `hnvl`, `hnu`, both
`:774` edges, `hczB`).  **So a consumer that needs `hcorner` and `hmono` at one `K` cannot use
this lemma**; what it gives is a common shear for `hmono` and `hadj` only.

⚠ For `hadj` + `hcorner` the same interval argument gives `K = 0` and `M' = 0`, and `M' = 0`
says `dot n u' ≤ 0` for every `n ∈ E S` on the branch `dot n vl < 0` — i.e. `hadj` at the
*unsheared* `u'`.  **The shear buys nothing for that pair.**  This does *not* show the pair is
unsatisfiable: `hadj` and `hcorner` may both hold at some `u'` for reasons having nothing to do
with shearing.  It shows only that the shear route cannot produce both.

⚠ Scope of `S`: it enters only through `hESfin : (E S).Finite` and through the `∀ n ∈ E S` of
the conclusion.  The `:774` edge hypotheses `hEbot`/`hEtop` are on `E B`, **not** on `E S`, so
this lemma asserts nothing about whether `S` has an edge parallel to `±ℓ`.  It is therefore
insensitive to which of `𝒮` / `𝒮_{φ_ι}` the consumer substitutes (`OPEN.md #15`): both are
finite, which is all that is used. -/

/-- **`hmono` and `hadj` at one shear, in `∀ K ≤ K₀` form.**  The `∀ K ≤ K₀` packaging is kept
(rather than a bare `∃ K`) so the result can absorb a third downward-closed constraint, as
`exists_shear_hstrip_and_hmono_of_height` does for `hstrip`. -/
theorem exists_shear_hmono_and_adjacent_forall_le {B S : Set (ℤ × ℤ)} {nl : ℤ × ℤ} {cz : ℤ}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hBfin : B.Finite) (hBne : B.Nonempty) (hBlc : IsLatticeConvexRegion B)
    (hnvl : dot nl vl = 0) (hnu : dot nl u' = -1)
    (hEbot : -nl ∈ E B) (hEtop : nl ∈ E B)
    (hczB : ∃ b₀ ∈ B, dot nl b₀ ≤ cz)
    (hESfin : (E S).Finite) :
    ∃ K₀ : ℤ, ∀ K ≤ K₀,
      (∀ b ∈ B, ∀ t : ℕ, cz ≤ dot nl b - t →
        b + (t : ℤ) • (u' - K • vl) ∈ Nivat.LE2.halfStrip B vl) ∧
      (∀ n ∈ E S, ¬ (dot n vl < 0 ∧ 0 < dot n (u' - K • vl))) := by
  obtain ⟨K₀, hK₀⟩ :=
    exists_shear_hmono_forall_le hunimod hBfin hBne hBlc hnvl hnu hEbot hEtop hczB
  obtain ⟨K₁, hK₁⟩ := exists_shear_adjacent_le (vl := vl) (u0 := u') hESfin
  exact ⟨min K₀ K₁, fun K hK =>
    ⟨hK₀ K (le_trans hK (min_le_left _ _)), hK₁ K (le_trans hK (min_le_right _ _))⟩⟩

/-- **The dispatched shape.**  `∃ K` serving both, a corollary of the `∀ K ≤ K₀` form.
See the section note: this `K` is `≤ 0` and cannot also serve `hcorner`. -/
theorem exists_shear_hmono_and_adjacent {B S : Set (ℤ × ℤ)} {nl : ℤ × ℤ} {cz : ℤ}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hBfin : B.Finite) (hBne : B.Nonempty) (hBlc : IsLatticeConvexRegion B)
    (hnvl : dot nl vl = 0) (hnu : dot nl u' = -1)
    (hEbot : -nl ∈ E B) (hEtop : nl ∈ E B)
    (hczB : ∃ b₀ ∈ B, dot nl b₀ ≤ cz)
    (hESfin : (E S).Finite) :
    ∃ K : ℤ,
      (∀ b ∈ B, ∀ t : ℕ, cz ≤ dot nl b - t →
        b + (t : ℤ) • (u' - K • vl) ∈ Nivat.LE2.halfStrip B vl) ∧
      (∀ n ∈ E S, ¬ (dot n vl < 0 ∧ 0 < dot n (u' - K • vl))) := by
  obtain ⟨K₀, hK₀⟩ := exists_shear_hmono_and_adjacent_forall_le hunimod hBfin hBne hBlc
    hnvl hnu hEbot hEtop hczB hESfin
  exact ⟨K₀, hK₀ K₀ le_rfl⟩

/-! ### §11n  洞 2：锥的第二方向 `u'` 与 `:764` 的相邻性

消费者：`RegionSteps.lean` 的 `exists_wedgeResidualR` 骨架中的**洞 2**（`:1866` 那条
`sorry`），`nℓ` / `hprim` / `hperp` 由洞 1 供给，在这里当 binder 收下。

**原文：b3_colle2.txt:764**
> "`ℓ_1, …, ℓ_{2m} ⊂ ℝ²` is an enumeration of the oriented lines through the origin parallels
> to the edges of `𝒮_φ` **where the edge parallel to `ℓ_{i+1}` is a successor of the edge
> parallel to `ℓ_i`** and indices are taken modulo `2m`."

逐量词对应（硬规矩 7）：

* `vl` = `v_ℓ`，`ℓ = ℓ_ι`（`:772` "we will write `-ℓ_ι = -ℓ` and `ℓ_ι = ℓ`"）。
* `nℓ` = `ℓ` 的本原法向。`Prim nℓ` + `dot nℓ vl = 0` 合起来就是「本原、与 `ℓ` 正交」；
  本文件**不自造** `nℓ`（硬规矩 10，与 `exists_u'_of_perp` 同一理由：链上的 `nℓ` 由 `Case1`
  钉住）。
* `u'` = `v_{ℓ_{ι-1}}`，`:780` 的 `𝓡_{ι-1} := {g + t·v_{ℓ_{ι-1}} : g ∈ H_B(ℓ), t ∈ ℤ₊}`
  的第二方向。
* 第三合取（`hadj`）= `:764` 的 "successor"：`ℓ_{ι-1}` 的边与 `ℓ_ι` 的边在 `𝒮_φ` 的边法向
  圈上**相邻**，逐字译成「没有边法向落进开锥 `{dot · vl < 0} ∩ {0 < dot · u'}`」。

**数值实例**（派工要求；这一段是纸算，**读法非内核事实**，内核事实是下面两条定理）：
`vl = (1,0)`、`nℓ = (0,-1)`。`dot nℓ u' = -1` 把 `u'` 钉在 `u'.2 = 1` 上，于是
`u' = (k,1)`，且 `det u' vl = -1` —— **幺模不是额外条件，它由 `hnu` 自动给出**
（`nℓ` 本原且 `⟂ vl` ⟹ `nℓ = ±(-vl.2, vl.1)` ⟹ `dot nℓ u' = ∓ det u' vl`）。
取 `𝒮_φ = supp((X^{(1,0)}-1)(X^{(1,2)}-1)) = {(0,0),(1,0),(1,2),(2,2)}`：满足
`dot n vl < 0` 的边法向只有 `n = (-2,1)`，而 `dot n u' = -2k+1 ≤ 0 ⟺ k ≥ 1`，
所以 `k = 1`（`u' = (1,1)`）就满足 `hadj`。一般情形见下：`E S` 有限，每条
`dot n vl < 0` 的边法向都随 `k` 增大被压到 `≤ 0`。

🔴 **但这个 `u'` 与洞 4 的 `hcorner` 不相容**，见本节末 `not_exists_adjacent_and_corner`：
同一个 `𝒮_φ` 上，`hadj` 要 `k ≥ 1`、`hcorner` 要 `k ≤ 0`，两条在**任何**幺模 `u'` 上都不能
同时成立（**这一句是内核事实**）。另一半是读法、非内核事实：上面那个 `𝒮_φ` 的真正
`v_{ℓ_{ι-1}}` 是 `(1,2)`，纸算下 `hadj ∧ hcorner` 在它上面都成立，而
`det (1,2) (1,0) = -2` —— 不幺模。这正是 `L1Assemble.lean:2105` 早就记下的那条：
把 `u'` 钉成 `v_{ℓ_{ι-1}}` 会让 `det u' vl = ±1` 一般地为假。 -/

/-- **洞 2，一般形。**  `S` 取任何边法向有限的集合；链上的实例是 `↑d.Sphi`（下一条）。

证明 = §11k 的幺模框架 + §11l 的下闭剪切：`exists_u'_of_perp` 给出满足前两条合取的 `u₀`
（`nℓ` 由调用者钉住，不自造），`exists_shear_adjacent_le` 把它沿 `vl` 平移到足够远，而
`det_shear_right`（`:140`）与 `dot_shear_right`（`:2580`）说明前两条合取对该平移免疫。

⚠ 这里**不是**「给定 `u'` 再剪切」那条被 §11m 堵死的老路。结论是 `∃ u'`：`dot nℓ u' = -1`
只把 `u'` 钉在一条 `vl`-平移族上（`nℓ ⟂ vl`），族内的那个自由参数就是这里用掉的剪切量。 -/
theorem exists_cone_direction_adjacent {S : Set (ℤ × ℤ)} {nℓ : ℤ × ℤ}
    (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (hESfin : (E S).Finite) :
    ∃ u' : ℤ × ℤ, (det u' vl = 1 ∨ det u' vl = -1) ∧ dot nℓ u' = -1 ∧
      ∀ n ∈ E S, ¬ (dot n vl < 0 ∧ 0 < dot n u') := by
  obtain ⟨u₀, hnu, hunimod⟩ := exists_u'_of_perp hvl_prim hprim hperp
  obtain ⟨K₀, hK₀⟩ := exists_shear_adjacent_le (vl := vl) (u0 := u₀) hESfin
  refine ⟨u₀ - K₀ • vl, ?_, ?_, hK₀ K₀ le_rfl⟩
  · rw [det_shear_right]; exact hunimod
  · rw [dot_shear_right hperp]; exact hnu

open Nivat.Colle35 in
/-- **洞 2，链上形。**  与派工单逐字一致的签名。`(E ↑𝒮_φ).Finite` 是免费的
（`finite_E_of_finite` + `Finset.finite_toSet`），所以洞 2 **不需要任何新前提**。 -/
theorem exists_cone_direction_adjacent_Sphi {ξ : Config ℤ} (d : DecompDataZ ξ)
    {nℓ : ℤ × ℤ} (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0) :
    ∃ u' : ℤ × ℤ, (det u' vl = 1 ∨ det u' vl = -1) ∧ dot nℓ u' = -1 ∧
      ∀ n ∈ E (↑d.toDecompData.Sphi : Set (ℤ × ℤ)),
        ¬ (dot n vl < 0 ∧ 0 < dot n u') :=
  exists_cone_direction_adjacent hvl_prim hprim hperp
    (finite_E_of_finite d.toDecompData.Sphi.finite_toSet)

/-- **洞 2 ∧ 洞 4 在同一个 `u'` 上不可满足** —— 在 `Sw := 𝒮_φ` ＋ `0 ≤ uCoord` 这一版上。

🔴 **2026-09-20 改判，本条保留不动（§14）**：它证的是**原符号 ＋ 集合取 `𝒮_φ`** 那一版，
仍然为真，而且正是促成改判的证据。现在认为洞 4 两处都写错了——集合应取 `𝒮_{φ_ι}`、
第二合取应是 `uCoord ≤ 0`。改判后的两条内核事实见 §11o：
`exists_adjacent_and_corner_le`（正面见证：换集合＋换符号后两洞相容）与
`not_exists_adjacent_and_corner_nonneg_on_Sw`（只换集合、不换符号仍无解）。

骨架里洞 2 产出的 `u'` 正是洞 4（`hcorner`）用的那个 `u'`。本定理是内核见证：存在一个
合法的 `𝒮_φ` 与 `vl`，使得**没有**幺模 `u'` 同时满足

* `hadj`（洞 2 第三合取，`:764` 的相邻性），与
* `hcorner`（洞 4：`∃ a ∈ 𝒮_φ, ∀ b ∈ 𝒮_φ, 0 ≤ ψ(b-a) ∧ 0 ≤ uCoord a b`，即
  `𝒮_φ ⊆ a + ℤ₊·vl + ℤ₊·u'`）。

见证：`𝒮_φ := supp((X^{(1,0)}-1)(X^{(1,2)}-1)) = {(0,0),(1,0),(1,2),(2,2)}`，`vl := (1,0)`
（`vl` 是 `𝒮_φ` 的一条边的方向，底边 `(0,0)–(1,0)`，正是 `:764` 对 `ℓ_ι` 的要求）。
`nℓ` 不出现在陈述里：幺模 `hunimod` 比「存在合法 `nℓ` 且 `dot nℓ u' = -1`」更弱
（后者蕴含前者），所以这条否定对**两个** `nℓ` 定向同时有效。

算术（内核已验，这里记读法）：`det u (1,0) = -u.2`，故 `hunimod ⟺ u.2 = ±1`；
`uCoord u (1,0) a b = u.2·(b.2-a.2)`、`ψ(b-a) = u.2²(b.1-a.1) - u.2·u.1·(b.2-a.2)`。
`(-2,1) ∈ E 𝒮_φ`（面 `{(0,0),(1,2)}`），`dot (-2,1) (1,0) = -2 < 0`，于是 `hadj` 逼出
`-2u.1 + u.2 ≤ 0`。`u.2 = 1` 时 `hcorner` 的 `uCoord` 分量逼 `a.2 = 0`，再在 `b = (1,2)` 上
逼 `u.1 ≤ 0`，与 `u.1 ≥ 1` 冲突；`u.2 = -1` 时对称地逼 `a.2 = 2` 再在 `b = (0,0)` 上冲突。

⚠ **本定理不涉及 `DecompDataZ`**：它证的是几何层的不可满足性（给定 `𝒮_φ` 的形状与 `vl`），
没有构造 `ξ : Config ℤ` 与 `d` 使 `d.Sphi` 等于这个集合。所以它说明的是
「洞 2 与洞 4 之间**没有**纯几何的共同解」，不是「骨架当场为假」。
补一句读法（非内核）：把内点 `(1,1)` 加进来（使该集合格凸）不改变上面任何一步。 -/
theorem not_exists_adjacent_and_corner :
    ∃ (Sph : Finset (ℤ × ℤ)) (v : ℤ × ℤ),
      Primitive v ∧ PosArea (↑Sph : Set (ℤ × ℤ)) ∧
      ¬ ∃ u : ℤ × ℤ, (det u v = 1 ∨ det u v = -1) ∧
          (∀ n ∈ E (↑Sph : Set (ℤ × ℤ)), ¬ (dot n v < 0 ∧ 0 < dot n u)) ∧
          (∃ a ∈ Sph, ∀ b ∈ Sph,
            0 ≤ dot (expNormal u v) (b - a) ∧ 0 ≤ uCoord u v a b) := by
  classical
  refine ⟨{(0,0), (1,0), (1,2), (2,2)}, (1,0), isCoprime_one_left, ?_, ?_⟩
  · exact ⟨(0,0), Finset.mem_coe.mpr (by decide), (1,0), Finset.mem_coe.mpr (by decide),
      (1,2), Finset.mem_coe.mpr (by decide), by decide⟩
  · rintro ⟨u, hunimod, hadj, a, ha, hcor⟩
    have hle : ∀ y ∈ (↑({(0,0), (1,0), (1,2), (2,2)} : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)),
        dot ((-2, 1) : ℤ × ℤ) y ≤ 0 := by
      intro y hy
      have hy' : y ∈ ({(0,0), (1,0), (1,2), (2,2)} : Finset (ℤ × ℤ)) := hy
      fin_cases hy' <;> decide
    have hE : ((-2, 1) : ℤ × ℤ) ∈
        E (↑({(0,0), (1,0), (1,2), (2,2)} : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) := by
      refine ⟨by decide, ⟨(0,0), ⟨Finset.mem_coe.mpr (by decide), fun y hy => ?_⟩,
        (1,2), ⟨Finset.mem_coe.mpr (by decide), fun y hy => ?_⟩, by decide⟩⟩
      · have h0 : dot ((-2, 1) : ℤ × ℤ) ((0,0) : ℤ × ℤ) = 0 := by decide
        rw [h0]; exact hle y hy
      · have h0 : dot ((-2, 1) : ℤ × ℤ) ((1,2) : ℤ × ℤ) = 0 := by decide
        rw [h0]; exact hle y hy
    have hadjn : dot ((-2, 1) : ℤ × ℤ) u ≤ 0 :=
      not_lt.mp (fun h => hadj ((-2, 1) : ℤ × ℤ) hE ⟨by decide, h⟩)
    have hdet : det u ((1,0) : ℤ × ℤ) = -u.2 := by simp [det]
    have hu2 : u.2 = -1 ∨ u.2 = 1 := by
      rcases hunimod with h | h <;> rw [hdet] at h <;> omega
    have hb00 := hcor (0,0) (by decide)
    have hb12 := hcor (1,2) (by decide)
    have hacases : a = (0,0) ∨ a = (1,0) ∨ a = (1,2) ∨ a = (2,2) := by
      fin_cases ha <;> simp
    simp only [dot] at hadjn
    rcases hu2 with h2 | h2 <;> rcases hacases with rfl | rfl | rfl | rfl <;>
      simp [expNormal, uCoord, det, dot, h2] at hb00 hb12 <;> omega

/-! ### §11o  洞 4 的集合与符号：`Sw = 𝒮_{φ_ι}`，第二合取是 `uCoord ≤ 0`

实例（`b3_colle2.txt:766` 的 `φ(X) := (X^{h₁}-1)⋯(X^{h_m}-1)`，取 `m = 3`）：
`h₁ = (1,0)`、`h₂ = (1,1)`、`h₃ = (0,1)`，`ι = 3`、`ι₀ = 3`（`:788` "let `1 ≤ ι₀ ≤ m` be such
that `ι₀ = ι mod m`"），于是 `vl = v_ℓ = h₃ = (0,1)`，原文的 `u' = v_{ℓ_{ι-1}} = h₂ = (1,1)`，
且 `det u' vl = 1` —— 这个实例里原文的 `u'` **恰好**幺模，所以它能同时测洞 2 和洞 4。

* `𝒮_φ = hexPhi`（六边形）。⚠ 中心 `(1,1)` **不在** `𝒮_φ` 里：它的两个子集和表示
  `{h₂}` 与 `{h₁,h₃}` 在 `∏(X^{h_i}-1)` 展开里符号相反，系数相消。
* `𝒮_{φ_ι} = zonoSw`（`:790` 的 `φ_ι(X) := ∏_{i≠ι₀}(X^{h_i}-1)`，这里 `= (X^{h₁}-1)(X^{h₂}-1)`）。

两条内核事实：`hadj`（在 `E ↑𝒮_φ` 上）与 `uCoord ≤ 0`（在 `𝒮_{φ_ι}` 上）在 `u' = (1,1)`、
`a = (2,1)` 同时成立；而 `hadj` 与**原符号** `0 ≤ uCoord`（同样在 `𝒮_{φ_ι}` 上）对**任何**
幺模 `u'` 都无解。合起来：换集合是必要的但不够，符号也必须换。 -/

/-- `𝒮_φ` for `φ = (X^{(1,0)}-1)(X^{(1,1)}-1)(X^{(0,1)}-1)`：三条线段的 zonotope 的支撑集，
一个六边形。中心 `(1,1)` 因系数相消而**不在**支撑集里。 -/
def hexPhi : Finset (ℤ × ℤ) := {(0,0), (1,0), (2,1), (2,2), (1,2), (0,1)}

/-- `𝒮_{φ_ι}` for `φ_ι = (X^{(1,0)}-1)(X^{(1,1)}-1)`（`b3_colle2.txt:790`）。 -/
def zonoSw : Finset (ℤ × ℤ) := {(0,0), (1,0), (1,1), (2,1)}

/-- **正面见证：换集合＋换符号之后，洞 2 与洞 4 相容。**

`vl = (0,1)`、`u' = (1,1)`（= 原文的 `v_{ℓ_{ι-1}}`，此实例中幺模）、`a = (2,1)`。六条合取依次是
`Primitive vl`、`PosArea 𝒮_φ`、`hunimod`、`a ∈ 𝒮_{φ_ι}`、`hadj`、以及**改号后**的 `hcorner`。

`hadj` 的证明不靠枚举 `E 𝒮_φ`：设 `n ∈ E ↑𝒮_φ` 同时满足 `dot n vl < 0`（即 `n.2 < 0`）与
`0 < dot n u'`（即 `0 < n.1 + n.2`），则 `(2,1)` 是 `dot n ·` 在 `𝒮_φ` 上的**严格**最大点，
面是单点，与 `n` 是边（面非平凡）矛盾。

⚠ 这一条**推翻**了「两洞不相容」的一般读法：`not_exists_adjacent_and_corner` 的不相容来自
`Sw := 𝒮_φ` ＋ 原符号这两处，不是本质的。

⚠ 仍未构造 `ξ : Config ℤ` 与 `d : DecompDataZ ξ` 使 `d.Sphi = hexPhi`：本条停在几何层。 -/
theorem exists_adjacent_and_corner_le :
    Primitive ((0,1) : ℤ × ℤ) ∧ PosArea (↑hexPhi : Set (ℤ × ℤ)) ∧
      det ((1,1) : ℤ × ℤ) ((0,1) : ℤ × ℤ) = 1 ∧
      ((2,1) : ℤ × ℤ) ∈ zonoSw ∧
      (∀ n ∈ E (↑hexPhi : Set (ℤ × ℤ)),
        ¬ (dot n ((0,1) : ℤ × ℤ) < 0 ∧ 0 < dot n ((1,1) : ℤ × ℤ))) ∧
      (∀ b ∈ zonoSw,
        0 ≤ dot (expNormal ((1,1) : ℤ × ℤ) ((0,1) : ℤ × ℤ)) (b - ((2,1) : ℤ × ℤ)) ∧
          uCoord ((1,1) : ℤ × ℤ) ((0,1) : ℤ × ℤ) ((2,1) : ℤ × ℤ) b ≤ 0) := by
  classical
  refine ⟨isCoprime_one_right, ⟨(0,0), ?_, (1,0), ?_, (0,1), ?_, by decide⟩, by decide,
    by decide, ?_, ?_⟩
  · exact Finset.mem_coe.mpr (by decide)
  · exact Finset.mem_coe.mpr (by decide)
  · exact Finset.mem_coe.mpr (by decide)
  · rintro n ⟨-, x, hx, y, hy, hxy⟩ ⟨hv, hu⟩
    have hn2 : n.2 < 0 := by simpa [dot] using hv
    have hn12 : 0 < n.1 + n.2 := by simpa [dot] using hu
    have hC : ((2,1) : ℤ × ℤ) ∈ (↑hexPhi : Set (ℤ × ℤ)) := Finset.mem_coe.mpr (by decide)
    have key : ∀ z ∈ face (↑hexPhi : Set (ℤ × ℤ)) n, z = ((2,1) : ℤ × ℤ) := by
      rintro z ⟨hzS, hzmax⟩
      have h1 := hzmax _ hC
      have hzS' : z ∈ hexPhi := hzS
      have hz6 : z = (0,0) ∨ z = (1,0) ∨ z = (2,1) ∨ z = (2,2) ∨ z = (1,2) ∨ z = (0,1) := by
        simpa [hexPhi] using hzS'
      rcases hz6 with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [dot] at h1 ⊢ <;> omega
    exact hxy ((key x hx).trans (key y hy).symm)
  · intro b hb
    have hb4 : b = (0,0) ∨ b = (1,0) ∨ b = (1,1) ∨ b = (2,1) := by simpa [zonoSw] using hb
    rcases hb4 with rfl | rfl | rfl | rfl <;>
      simp [expNormal, uCoord, det, dot]

/-- **只换集合、不换符号，仍然无解。**

同一个实例（`𝒮_φ = hexPhi`、`vl = (0,1)`、`Sw = zonoSw`）上，`hadj` 与**原符号**
`0 ≤ uCoord` 对**任何**幺模 `u'` 都不能同时成立。与 `exists_adjacent_and_corner_le` 合起来，
这把「集合换成 `𝒮_{φ_ι}` 就够了」钉死：符号也必须换。

机制：`(0,-1)` 与 `(1,-1)` 都是 `𝒮_φ` 的边（面分别是 `{(0,0),(1,0)}`、`{(1,0),(2,1)}`），
两条都满足 `dot n vl = n.2 = -1 < 0`，于是 `hadj` 逼出 `0 ≤ u.2` 与 `u.1 ≤ u.2`；
`hunimod` 给 `u.1 = ±1`（`det u (0,1) = u.1`）。
`u.1 = 1` 时 `0 ≤ uCoord = u.1·(b.1-a.1)` 逼 `a = (0,0)`，再在 `b = (1,0)` 上逼 `u.2 ≤ 0`，
与 `1 = u.1 ≤ u.2` 冲突；`u.1 = -1` 时逼 `a = (2,1)`，再在 `b = (0,0)` 上逼 `2u.2 + 1 ≤ 0`，
与 `0 ≤ u.2` 冲突。 -/
theorem not_exists_adjacent_and_corner_nonneg_on_Sw :
    ¬ ∃ u : ℤ × ℤ, (det u ((0,1) : ℤ × ℤ) = 1 ∨ det u ((0,1) : ℤ × ℤ) = -1) ∧
        (∀ n ∈ E (↑hexPhi : Set (ℤ × ℤ)), ¬ (dot n ((0,1) : ℤ × ℤ) < 0 ∧ 0 < dot n u)) ∧
        (∃ a ∈ zonoSw, ∀ b ∈ zonoSw,
          0 ≤ dot (expNormal u ((0,1) : ℤ × ℤ)) (b - a) ∧
            0 ≤ uCoord u ((0,1) : ℤ × ℤ) a b) := by
  classical
  rintro ⟨u, hunimod, hadj, a, ha, hcor⟩
  have hmem : ∀ y ∈ (↑hexPhi : Set (ℤ × ℤ)),
      y = (0,0) ∨ y = (1,0) ∨ y = (2,1) ∨ y = (2,2) ∨ y = (1,2) ∨ y = (0,1) := by
    intro y hy
    have hy' : y ∈ hexPhi := hy
    simpa [hexPhi] using hy'
  have hE0 : ((0,-1) : ℤ × ℤ) ∈ E (↑hexPhi : Set (ℤ × ℤ)) := by
    refine ⟨by decide, ⟨(0,0), ⟨Finset.mem_coe.mpr (by decide), fun y hy => ?_⟩,
      (1,0), ⟨Finset.mem_coe.mpr (by decide), fun y hy => ?_⟩, by decide⟩⟩ <;>
      rcases hmem y hy with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hE1 : ((1,-1) : ℤ × ℤ) ∈ E (↑hexPhi : Set (ℤ × ℤ)) := by
    refine ⟨by decide, ⟨(1,0), ⟨Finset.mem_coe.mpr (by decide), fun y hy => ?_⟩,
      (2,1), ⟨Finset.mem_coe.mpr (by decide), fun y hy => ?_⟩, by decide⟩⟩ <;>
      rcases hmem y hy with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have ha0 : 0 ≤ u.2 := by
    have := not_lt.mp (fun h => hadj ((0,-1) : ℤ × ℤ) hE0 ⟨by decide, h⟩)
    simp only [dot] at this; omega
  have ha1 : u.1 ≤ u.2 := by
    have := not_lt.mp (fun h => hadj ((1,-1) : ℤ × ℤ) hE1 ⟨by decide, h⟩)
    simp only [dot] at this; omega
  have hdet : det u ((0,1) : ℤ × ℤ) = u.1 := by simp [det]
  have hu1 : u.1 = 1 ∨ u.1 = -1 := by
    rcases hunimod with h | h <;> rw [hdet] at h <;> omega
  have hb00 := hcor (0,0) (by decide)
  have hb10 := hcor (1,0) (by decide)
  have hb21 := hcor (2,1) (by decide)
  have hacases : a = (0,0) ∨ a = (1,0) ∨ a = (1,1) ∨ a = (2,1) := by simpa [zonoSw] using ha
  rcases hu1 with h1 | h1 <;> rcases hacases with rfl | rfl | rfl | rfl <;>
    simp [expNormal, uCoord, det, dot, h1] at hb00 hb10 hb21 <;> omega

/-- **改号之后，两洞在整条 `vl`-平移族上同时成立**（不只在原文那个 `u' = (1,1)` 上）。

`u' = (1,t)` 就是 `hnu`/`hunimod` 允许的那条族（`vl = (0,1)`，`det (1,t) (0,1) = 1` 对每个 `t`），
而 `t` 正是 `exists_cone_direction_adjacent` 用掉的那个剪切自由度。本条说：`t ≥ 1` 时
`hadj` 与**改号后**的 `hcorner`（`a = (2,1)` 固定）**同时**成立。

🔑 这就是符号为什么要改：原符号下 `hcorner` 对剪切**下闭**、`hadj` **上闭**，只能交于一点，
`not_exists_adjacent_and_corner` 与 `not_exists_adjacent_and_corner_nonneg_on_Sw` 是这件事的两个
内核实例；改号后两者**同向上闭**，于是 `exists_cone_direction_adjacent` 产出的那个「足够大的
剪切」不但不妨碍洞 4，反而正好落在洞 4 要的那一侧。`t = 1` 即原文的 `v_{ℓ_{ι-1}} = h₂`。

⚠ 只是一个实例：本条不证一般情形，也没有构造 `DecompDataZ`。 -/
theorem adjacent_and_corner_le_forall_shear (t : ℤ) (ht : 1 ≤ t) :
    (∀ n ∈ E (↑hexPhi : Set (ℤ × ℤ)),
        ¬ (dot n ((0,1) : ℤ × ℤ) < 0 ∧ 0 < dot n ((1,t) : ℤ × ℤ))) ∧
      (∀ b ∈ zonoSw,
        0 ≤ dot (expNormal ((1,t) : ℤ × ℤ) ((0,1) : ℤ × ℤ)) (b - ((2,1) : ℤ × ℤ)) ∧
          uCoord ((1,t) : ℤ × ℤ) ((0,1) : ℤ × ℤ) ((2,1) : ℤ × ℤ) b ≤ 0) := by
  classical
  constructor
  · rintro n ⟨-, x, hx, y, hy, hxy⟩ ⟨hv, hu⟩
    have hn2 : n.2 < 0 := by simpa [dot] using hv
    have hu' : 0 < n.1 + n.2 * t := by simpa [dot] using hu
    have hstep : n.2 * t ≤ n.2 := by
      linarith [mul_nonneg (sub_nonneg.mpr ht) (neg_nonneg.mpr hn2.le)]
    have hn12 : 0 < n.1 + n.2 := by linarith
    have hC : ((2,1) : ℤ × ℤ) ∈ (↑hexPhi : Set (ℤ × ℤ)) := Finset.mem_coe.mpr (by decide)
    have key : ∀ z ∈ face (↑hexPhi : Set (ℤ × ℤ)) n, z = ((2,1) : ℤ × ℤ) := by
      rintro z ⟨hzS, hzmax⟩
      have h1 := hzmax _ hC
      have hzS' : z ∈ hexPhi := hzS
      have hz6 : z = (0,0) ∨ z = (1,0) ∨ z = (2,1) ∨ z = (2,2) ∨ z = (1,2) ∨ z = (0,1) := by
        simpa [hexPhi] using hzS'
      rcases hz6 with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [dot] at h1 ⊢ <;> omega
    exact hxy ((key x hx).trans (key y hy).symm)
  · intro b hb
    have hb4 : b = (0,0) ∨ b = (1,0) ∨ b = (1,1) ∨ b = (2,1) := by simpa [zonoSw] using hb
    rcases hb4 with rfl | rfl | rfl | rfl <;>
      simp [expNormal, uCoord, det, dot] <;> omega

/-! ## §11p  洞 4 的第二合取 **就是** 洞 3 的 `nℓ`-层，逐字

原文：b3_colle2.txt:414（`H_B(ℓ) := {g + t·v⃗_ℓ : g ∈ B, t ∈ ℤ_+}`，`nℓ` 是杀掉 `v⃗_ℓ` 的法向）
＋ :777-780（`𝓡_{ι-1} := {g + t·v_{ℓ_{ι-1}} : g ∈ H_B(ℓ), t ∈ ℤ₊}`）。

本条**不是新命题**，是一条恒等式：在 `hunimod`、`hperp : dot nℓ vl = 0`、`hnu : dot nℓ u' = -1`
之下，`(vl, u')` 是 `ℤ²` 的基，写 `b - a = β•vl + α•u'`，则 `uCoord u' vl a b = α` 而
`dot nℓ (b - a) = -α`。逐个量词：`vl = v⃗_ℓ`（:414 的 `v⃗_ℓ`）、`u' = v_{ℓ_{ι-1}}`（:779）、
`nℓ` = `ℓ` 的本原法向、`a` = 放置窗口的参考点、`b` 跑遍窗口。**没有一个量词是我们发明的**：
三条前提全部来自已有签名，结论两边都是已有定义。

数学内容全在 §5 的 `dot_eq_neg_uCoord`（`dot nℓ = -χ`，基点 `0`）里；本条只是把基点从 `0`
搬到 `a`，用 `L1StraddleWedge.uCoord_eq_sub`。

🔑 **读法（非内核事实，仅记录动机）**：洞 4 的第二合取 `0 ≤ uCoord u' vl a b` 由此等价于
`dot nℓ b ≤ dot nℓ a`，即「`a` 是窗口的 `nℓ`-极大点」；而洞 3 的 `hstrict` 说的是
`a₀` 为 `nℓ`-**严格极小**。两洞因此是同一根坐标轴的两端，不需要各自找生产者。
`not_exists_adjacent_and_corner`（§11n）与 `not_exists_adjacent_and_corner_nonneg_on_Sw`
（§11o）仍然为真，它们证伪的正是「两端同时取极小」那一版；§14，保留不动。

**消费者**：`RegionSteps.lean:1951`（洞 4），由集成者接线。 -/
theorem uCoord_eq_neg_dot_of_basis {nℓ a b : ℤ × ℤ}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hperp : dot nℓ vl = 0) (hnu : dot nℓ u' = -1) :
    uCoord u' vl a b = - dot nℓ (b - a) := by
  rw [Nivat.L1StraddleWedge.uCoord_eq_sub (u' := u') (vl := vl) a b, dot_sub,
    dot_eq_neg_uCoord hunimod hperp hnu b, dot_eq_neg_uCoord hunimod hperp hnu a]
  ring

/-- **等价形式（现行符号）**：洞 4 的第二合取 `0 ≤ uCoord u' vl a b` ⟺ `a` 是窗口的
`nℓ`-**极大**点。与洞 3 的 `hstrict`（`a₀` 为 `nℓ`-严格**极小**）方向相反。 -/
theorem uCoord_nonneg_iff_dot_le {nℓ a b : ℤ × ℤ}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hperp : dot nℓ vl = 0) (hnu : dot nℓ u' = -1) :
    0 ≤ uCoord u' vl a b ↔ dot nℓ b ≤ dot nℓ a := by
  rw [uCoord_eq_neg_dot_of_basis (u' := u') (vl := vl) hunimod hperp hnu, dot_sub]
  omega

/-- **等价形式（改号后）**：`uCoord u' vl a b ≤ 0` ⟺ `a` 是窗口的 `nℓ`-**极小**点。
这一侧才是洞 3 的 `hstrict` 直接给得出的那一侧（`hstrict` 蕴含它的非严格版）。 -/
theorem uCoord_nonpos_iff_dot_le {nℓ a b : ℤ × ℤ}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hperp : dot nℓ vl = 0) (hnu : dot nℓ u' = -1) :
    uCoord u' vl a b ≤ 0 ↔ dot nℓ a ≤ dot nℓ b := by
  rw [uCoord_eq_neg_dot_of_basis (u' := u') (vl := vl) hunimod hperp hnu, dot_sub]
  omega

end Nivat.EnvFit

section Receipts
/-! Standing `#print axioms` receipts.  Deletable as a block. -/

#print axioms Nivat.EnvFit.dot_expNormal_add
#print axioms Nivat.EnvFit.uCoord_zero_add_hom
#print axioms Nivat.EnvFit.uCoord_zero_sub_hom
#print axioms Nivat.EnvFit.uCoord_zero_add
#print axioms Nivat.EnvFit.eq_add_coords
#print axioms Nivat.EnvFit.sub_eq_of_eq_add
#print axioms Nivat.EnvFit.det_shear_right
#print axioms Nivat.EnvFit.mem_coneRegion_iff_coords
#print axioms Nivat.EnvFit.hapex_of_hfit
#print axioms Nivat.EnvFit.hfit_of_hapex
#print axioms Nivat.EnvFit.hfit_iff_hapex
#print axioms Nivat.EnvFit.not_exists_hfit_of_not_exists_hapex
#print axioms Nivat.EnvFit.not_exists_hfit_pinned
#print axioms Nivat.EnvFit.exists_shear_hapex
#print axioms Nivat.EnvFit.exists_shear_hfit
#print axioms Nivat.EnvFit.dot_eq_neg_uCoord
#print axioms Nivat.EnvFit.exists_mem_coneRegion_dot_lt
#print axioms Nivat.EnvFit.hcone_of_psi_nonneg
#print axioms Nivat.EnvFit.hcone_iff_psi_nonneg
#print axioms Nivat.EnvFit.exists_hcone
#print axioms Nivat.EnvFit.not_hapex_of_hcone
#print axioms Nivat.EnvFit.mem_halfStrip_iff_coords
#print axioms Nivat.EnvFit.hstrip_iff_levels
#print axioms Nivat.EnvFit.height_le_of_hstrip
#print axioms Nivat.EnvFit.uCoord_shear
#print axioms Nivat.EnvFit.dot_expNormal_shear
#print axioms Nivat.EnvFit.occupancy_of_hmono
#print axioms Nivat.EnvFit.Bgap_eq
#print axioms Nivat.EnvFit.finite_Bgap
#print axioms Nivat.EnvFit.nonempty_Bgap
#print axioms Nivat.EnvFit.posArea_Bgap
#print axioms Nivat.EnvFit.isLatticeConvexRegion_Bgap
#print axioms Nivat.EnvFit.not_level_one_Bgap
#print axioms Nivat.EnvFit.not_exists_shear_hmono
#print axioms Nivat.EnvFit.exists_zsmul_of_dot_eq_zero
#print axioms Nivat.EnvFit.exists_pos_step
#print axioms Nivat.EnvFit.occupancy_of_edges
#print axioms Nivat.EnvFit.occupancy_of_enveloped
#print axioms Nivat.EnvFit.prim_of_unimod
#print axioms Nivat.EnvFit.exists_shear_hmono_of_edges
#print axioms Nivat.EnvFit.exists_shear_hmono_of_edges_of_suppVal
#print axioms Nivat.EnvFit.exists_shear_hmono_of_enveloped
#print axioms Nivat.EnvFit.both_edges_of_enveloped
#print axioms Nivat.EnvFit.both_edges_of_envOf
#print axioms Nivat.EnvFit.occupancy_of_envOf
#print axioms Nivat.EnvFit.Bsq_eq
#print axioms Nivat.EnvFit.finite_Bsq
#print axioms Nivat.EnvFit.nonempty_Bsq
#print axioms Nivat.EnvFit.isLatticeConvexRegion_Bsq
#print axioms Nivat.EnvFit.hyps_satisfiable
#print axioms Nivat.EnvFit.exists_shear_hmono_of_edges_of_le
#print axioms Nivat.EnvFit.Bslant_eq
#print axioms Nivat.EnvFit.finite_Bslant
#print axioms Nivat.EnvFit.nonempty_Bslant
#print axioms Nivat.EnvFit.posArea_Bslant
#print axioms Nivat.EnvFit.isLatticeConvexRegion_Bslant
#print axioms Nivat.EnvFit.bot_edge_Bslant
#print axioms Nivat.EnvFit.top_edge_Bslant
#print axioms Nivat.EnvFit.not_hmono_Bslant
#print axioms Nivat.EnvFit.no_nonneg_shear_hmono
#print axioms Nivat.EnvFit.hstrip_of_edges_of_height_of_le
#print axioms Nivat.EnvFit.exists_shear_hmono_forall_le
#print axioms Nivat.EnvFit.exists_shear_hstrip_of_edges_of_height
#print axioms Nivat.EnvFit.exists_shear_hstrip_and_hmono_of_height
#print axioms Nivat.EnvFit.Bcliff_eq
#print axioms Nivat.EnvFit.finite_Bcliff
#print axioms Nivat.EnvFit.nonempty_Bcliff
#print axioms Nivat.EnvFit.posArea_Bcliff
#print axioms Nivat.EnvFit.isLatticeConvexRegion_Bcliff
#print axioms Nivat.EnvFit.dot_expNormal_cliff
#print axioms Nivat.EnvFit.hlean_Bcliff
#print axioms Nivat.EnvFit.not_top_edge_Bcliff
#print axioms Nivat.EnvFit.not_hmono_Bcliff
#print axioms Nivat.EnvFit.not_hmono_of_lean
#print axioms Nivat.EnvFit.not_hlean_Bslant
#print axioms Nivat.EnvFit.hmono_of_lean_of_edges
#print axioms Nivat.EnvFit.hmono_of_lean_of_enveloped

#print axioms Nivat.EnvFit.mem_halfStrip_iff_level
#print axioms Nivat.EnvFit.levelDescend_of_step
#print axioms Nivat.EnvFit.hmono_of_levelDescend
#print axioms Nivat.EnvFit.level_step_of_lean
#print axioms Nivat.EnvFit.hmono_of_lean_of_edges_via_step
#print axioms Nivat.EnvFit.noEdgeBetween_of_E
#print axioms Nivat.EnvFit.exists_lean_point_of_noEdgeBetween
#print axioms Nivat.EnvFit.hlean_of_noEdgeBetween
#print axioms Nivat.EnvFit.hmono_of_adjacent_of_edges
#print axioms Nivat.EnvFit.hmono_of_adjacent_of_enveloped
#print axioms Nivat.EnvFit.edge_between_Bslant
#print axioms Nivat.EnvFit.not_noEdgeBetween_Bslant

#print axioms Nivat.EnvFit.exists_frame_det_one
#print axioms Nivat.EnvFit.exists_u'_of_perp
#print axioms Nivat.EnvFit.exists_frame

#print axioms Nivat.EnvFit.dot_shear_right
#print axioms Nivat.EnvFit.adjacent_of_shear_le
#print axioms Nivat.EnvFit.exists_shear_adjacent_le
#print axioms Nivat.EnvFit.exists_shear_adjacent

#print axioms Nivat.EnvFit.exists_shear_hmono_and_adjacent_forall_le
#print axioms Nivat.EnvFit.exists_shear_hmono_and_adjacent

#print axioms Nivat.EnvFit.exists_cone_direction_adjacent
#print axioms Nivat.EnvFit.exists_cone_direction_adjacent_Sphi
#print axioms Nivat.EnvFit.not_exists_adjacent_and_corner
#print axioms Nivat.EnvFit.exists_adjacent_and_corner_le
#print axioms Nivat.EnvFit.not_exists_adjacent_and_corner_nonneg_on_Sw
#print axioms Nivat.EnvFit.adjacent_and_corner_le_forall_shear
#print axioms Nivat.EnvFit.uCoord_eq_neg_dot_of_basis
#print axioms Nivat.EnvFit.uCoord_nonneg_iff_dot_le
#print axioms Nivat.EnvFit.uCoord_nonpos_iff_dot_le

end Receipts

