/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.ChainCanon
import Nivat.External.Colle.ANormal

/-!
# Leaf A's residual obligation: `ChainCanonData.envA` for `canonA`, unfolded

`ChainCanon.lean`'s `ChainCanonData` (`:114-163`) discharges four of `ChainData`'s
obligations (`subStrip`, `agreeA`, `AhatEq`, `maximalHat`) for free by taking `A i` to be
the canonical agreement set `canonA η xper vl B u i` rather than free data. What is left is
`envA : ∀ i, Env (canonA η xper vl B u i)` (`ChainCanon.lean:134`). Team-lead's framing
(2026-09-18): "债是搬家不是消失" — this file unfolds that one remaining debt into a
`ChainCanonData`-free statement, quoting every definition it touches verbatim, per PROTOCOL
§20/§3 (grep before claiming "no source", quote before claiming "unfolded").

## Orphan scan (`PROTOCOL.md` §20), raw output, pasted verbatim

```
Nivat.External.Colle.ANormal
Nivat.External.Colle.BottomNotEventual
Nivat.External.Colle.ChainCanon
Nivat.External.Colle.Claim36
Nivat.External.Colle.Claim43Refutation
Nivat.External.Colle.Claim47Bridge
Nivat.External.Colle.ConeCounterexample
Nivat.External.Colle.ConvexForcesRefuted
Nivat.External.Colle.CosetPigeonhole
Nivat.External.Colle.CyrKra224
Nivat.External.Colle.EnvelopedConvex
Nivat.External.Colle.HalfPlaneDoublyPeriodic
Nivat.External.Colle.HalfPlaneShells
Nivat.External.Colle.KMProp18
Nivat.External.Colle.L1Complexity
Nivat.External.Colle.L1Fields
Nivat.External.Colle.L3Band
Nivat.External.Colle.Notation14
Nivat.External.Colle.ONEDRational
Nivat.External.Colle.OrderThree
Nivat.External.Colle.PeriodExtraction
Nivat.External.Colle.RegionClassification
Nivat.External.Colle.RegionCut
Nivat.External.Colle.RegionCutGE
Nivat.External.Colle.RegionHalfPlaneOrientation
Nivat.External.Colle.Step3Clause2
Nivat.External.Colle.StepHypSeam
Nivat.External.Colle.StepMultiplicity
Nivat.External.Colle.Step_ChainData
Nivat.External.Colle.Step_LatConvex
Nivat.External.Colle.Step_NotPeriodic
Nivat.External.Colle.Step_PeriodsRays
Nivat.External.Colle.Step_PeriodsRays2
Nivat.External.Colle.UniformBound
Nivat.External.Colle.ZonoDirection
Nivat.External.Colle.ZonotopeDiverge
Nivat.Laurent.BinomialCoprime
Nivat.Laurent.CRTSpan
Nivat.Laurent.SupportContainment
Nivat.OrbitTransfer
Nivat.Section8.Main
```
(42 modules; `ChainCanon` itself is one of them — nothing but `All.lean` imports it yet.
`ChainRecursion.lean` was checked separately, see below, and is **not** relevant: its
`envA_chain` (`:120-121`) is `EnvOf S A` unwrapped straight out of the `StepHyp` existential
hypothesis, not a proof that any concrete formula satisfies `EnvOf` — same difficulty as this
file's goal, not a discharge of it.)

## `grep -rn "envA\|EnvOf\|Enveloped" Nivat/ --include=*.lean`, relevant hits only

The full dump covers ~20 files; the only load-bearing ones for this task are `LatticeEdges.lean`
(the definitions, quoted below) and `ChainCanon.lean` (`canonA`, `envA`, quoted below).
`ChainRecursion.lean:121` (`envA_chain`) is the one candidate that looked promising and was
ruled out above. No other hit constructs `EnvOf U T` for a *concrete* `T`; every other
occurrence either restates the definition, or consumes an `EnvOf`/`Env` hypothesis that is
already in scope (e.g. `RegionSteps.lean:1202-1204`, `:1229-1231`), never discharges one from
nothing.

## The definitions, quoted verbatim

`Section8/HalfPlane.lean:174-175`:
```
def IsLatticeConvexRegion (R : Set (ℤ × ℤ)) : Prop :=
  ∃ C : Set (ℝ × ℝ), Convex ℝ C ∧ IsClosed C ∧ R = toReal ⁻¹' C
```

`LatticeEdges.lean:217` and `:160`:
```
def E (R : Set (ℤ × ℤ)) : Set (ℤ × ℤ) := {n | IsEdge R n}
def face (R : Set (ℤ × ℤ)) (n : ℤ × ℤ) : Set (ℤ × ℤ) := ...
```

`LatticeEdges.lean:624-629`:
```
def WeaklyEnveloped (U T : Set (ℤ × ℤ)) : Prop :=
  IsLatticeConvexRegion T ∧ ∀ n ∈ E T, n ∈ E U ∧ (face U n).encard ≤ (face T n).encard

def Enveloped (U T : Set (ℤ × ℤ)) : Prop :=
  WeaklyEnveloped U T ∧ (E T).encard = (E U).encard
```

`LatticeEdges.lean`（`def EnvOf`）:
```
def EnvOf (U : Set (ℤ × ℤ)) : Set (ℤ × ℤ) → Prop := fun T => Enveloped U T
```

`ChainCanon.lean:58-60`:
```
def canonA (η xper : Config α) (vl : ℤ × ℤ) (B : ℕ → Set (ℤ × ℤ)) (u : ℕ → ℤ × ℤ)
    (i : ℕ) : Set (ℤ × ℤ) :=
  {w | w ∈ halfStrip (B i) vl ∧ η (w + u i) = xper w}
```

`halfStrip` (`LatticeEdges.lean`, the `def halfStrip` — §85: 按标识符名找，不写行号；
旧批注写 `:1810-1811`，已烂，实际当时在 `:1884`):
```
def halfStrip (B : Set (ℤ × ℤ)) (v : ℤ × ℤ) : Set (ℤ × ℤ) :=
  {g | ∃ b ∈ B, ∃ t : ℕ, g = b + (t : ℤ) • v}
```

## Where the real content sits

`halfStrip (B i) vl` is a Minkowski sum `B i + rayℕ vl`; it is lattice-convex whenever `B i` is
(convex + convex is convex). The agreement predicate `η (w + u i) = xper w` carries **no**
convexity information at all — it is a level set of an equality on a totally unconstrained
`Config`. So `canonA`'s `IsLatticeConvexRegion` is not free from the two ingredients
separately; it is exactly Collé's geometric claim, and every other clause of `Enveloped`
(`E`-equality, face `encard` domination) rides on top of it. This is the leaf's real content,
not bookkeeping — matching `ChainCanon.lean`'s own module docstring (`:33-42`).
-/

set_option autoImplicit false

namespace Nivat.AEnv

open Nivat Nivat.LE2 Nivat.Colle35

variable {α : Type*}

/-- **`ChainCanonData.envA`, unfolded to a `ChainCanonData`-free statement.**
Exactly `ChainCanonData.envA` (`ChainCanon.lean:134`) specialised to `Env := EnvOf (↑S)`
(the leaf's real envelope predicate, `RegionSteps.lean`'s `d.Sphi` role played here by `S`),
quantifying directly over `η xper vl S B u` with no `ChainCanonData` in sight. -/
def envACanon (η xper : Config α) (vl : ℤ × ℤ) (S : Finset (ℤ × ℤ))
    (B : ℕ → Set (ℤ × ℤ)) (u : ℕ → ℤ × ℤ) : Prop :=
  ∀ i : ℕ, EnvOf (↑S : Set (ℤ × ℤ)) (canonA η xper vl B u i)

/-- **`envACanon`, unfolded one layer further** — `EnvOf`/`Enveloped`/`WeaklyEnveloped`
expanded in place, so the statement mentions only `IsLatticeConvexRegion`, `E`, `face`, and
`encard`. -/
def envACanon_unfolded (η xper : Config α) (vl : ℤ × ℤ) (S : Finset (ℤ × ℤ))
    (B : ℕ → Set (ℤ × ℤ)) (u : ℕ → ℤ × ℤ) : Prop :=
  ∀ i : ℕ,
    (IsLatticeConvexRegion (canonA η xper vl B u i) ∧
      ∀ n ∈ E (canonA η xper vl B u i),
        n ∈ E (↑S : Set (ℤ × ℤ)) ∧
          (face (↑S : Set (ℤ × ℤ)) n).encard ≤ (face (canonA η xper vl B u i) n).encard) ∧
    (E (canonA η xper vl B u i)).encard = (E (↑S : Set (ℤ × ℤ))).encard

/-- The two forms say the same thing: pure `dsimp`/`rfl` unfolding through `EnvOf`,
`Enveloped`, `WeaklyEnveloped`, no lemma content consumed. -/
theorem envACanon_iff_unfolded {η xper : Config α} {vl : ℤ × ℤ} {S : Finset (ℤ × ℤ)}
    {B : ℕ → Set (ℤ × ℤ)} {u : ℕ → ℤ × ℤ} :
    envACanon η xper vl S B u ↔ envACanon_unfolded η xper vl S B u := Iff.rfl

/-- **The sub-lemma the reduction isolates**: lattice-convexity of the agreement-set-inside-
half-strip, with no reference to edges/faces/`encard` at all. This is the piece that is *not*
free from `halfStrip`'s convexity and `Config` equality separately (see the module docstring);
every other clause of `envACanon_unfolded` rides on top of it via `IsLatticeConvexRegion.*`
lemmas already in `Section8/HalfPlane.lean`. -/
def canonA_latticeConvex (η xper : Config α) (vl : ℤ × ℤ)
    (B : ℕ → Set (ℤ × ℤ)) (u : ℕ → ℤ × ℤ) : Prop :=
  ∀ i : ℕ, IsLatticeConvexRegion (canonA η xper vl B u i)

/-- `envACanon` needs `canonA_latticeConvex` as its first ingredient: unfolding `EnvOf` at any
single `i` and taking `.1.1` (via `WeaklyEnveloped.latticeConvex`) already extracts it, with no
extra hypothesis. So `canonA_latticeConvex` is *necessary*, not merely a convenient sub-goal. -/
theorem canonA_latticeConvex_of_envACanon {η xper : Config α} {vl : ℤ × ℤ} {S : Finset (ℤ × ℤ)}
    {B : ℕ → Set (ℤ × ℤ)} {u : ℕ → ℤ × ℤ}
    (h : envACanon η xper vl S B u) : canonA_latticeConvex η xper vl B u :=
  fun i => (h i).1.1

/-! ## Specialising `S := d.Sphi`, using the new seam

Team-lead's `tmp/vSeamA.lean` seam (2026-09-18) supplies, for `d : DecompData η`,
`DecompData.mem_E_Sphi_iff : n ∈ E ↑d.Sphi ↔ Prim n ∧ ∃ i, dot n (d.h i) = 0`
(`ANormal.lean:396`). That rewrites the *target*-side membership clause of
`envACanon_unfolded` (`n ∈ E (↑S)` with `S := d.Sphi`) into a decidable form built only from
`d.h`. It does **not** touch `canonA_latticeConvex` or `E (canonA ...)`: those depend solely
on `canonA`'s own construction (`B`, `u`, `η`, `xper`, `vl`), which the seam says nothing
about — `d.Sphi`'s zonotope structure (`E_Sphi_eq`, `mem_E_Sphi_iff`) characterises the
*right*-hand side of the envelope relation, not the left. So this is a genuine but partial
simplification: one clause gets a decision procedure, the still-open lattice-convexity
obstacle is unaffected. -/

/-- `envACanon_unfolded` specialised to `S := d.Sphi`, with the membership clause on the
`d.Sphi` side rewritten via `mem_E_Sphi_iff` into `Prim n ∧ ∃ i, dot n (d.h i) = 0`. Still
`ChainCanonData`-free; still leaves `IsLatticeConvexRegion (canonA ...)` and
`E (canonA ...)` opaque, exactly as `canonA_latticeConvex` above. -/
def envACanon_unfolded_atSphi {η' : Config ℤ} (d : DecompData η') (η xper : Config α)
    (vl : ℤ × ℤ) (B : ℕ → Set (ℤ × ℤ)) (u : ℕ → ℤ × ℤ) : Prop :=
  ∀ i : ℕ,
    (IsLatticeConvexRegion (canonA η xper vl B u i) ∧
      ∀ n ∈ E (canonA η xper vl B u i),
        (Prim n ∧ ∃ j, dot n (d.h j) = 0) ∧
          (face (↑d.Sphi : Set (ℤ × ℤ)) n).encard ≤ (face (canonA η xper vl B u i) n).encard) ∧
    (E (canonA η xper vl B u i)).encard = (E (↑d.Sphi : Set (ℤ × ℤ))).encard

theorem envACanon_unfolded_atSphi_iff {η' : Config ℤ} (d : DecompData η')
    {η xper : Config α} {vl : ℤ × ℤ} {B : ℕ → Set (ℤ × ℤ)} {u : ℕ → ℤ × ℤ} :
    envACanon_unfolded_atSphi d η xper vl B u ↔ envACanon_unfolded η xper vl d.Sphi B u := by
  unfold envACanon_unfolded_atSphi envACanon_unfolded
  simp only [d.mem_E_Sphi_iff]

/-! ## Refuting `canonA_latticeConvex`

Team-lead's task: prove `canonA_latticeConvex`, or refute it. A prior lane already flagged
(`EnvelopedConvex.lean:529-537`, module "Status" section) that the agreement locus
`{z | η (z + u) = xper z}` is not convex, calling this "a statement-level gap ... not a
missing proof." The counterexample below cashes that out as a **compiled refutation**:
`canonA_latticeConvex` is false for arbitrary `η xper vl B u`, with no hypothesis on
`η`/`xper` beyond what `ChainCanonData` already carries (none) making it true.

Construction: `vl := (1,0)`, `B _ := {(0,0)}`, `u _ := (0,0)`, so
`halfStrip (B 0) vl = {(t,0) : t : ℕ}` (the ray). `η`/`xper : Config Bool` are rigged so the
agreement locus is exactly the two points `{(0,0),(2,0)}` — both on the ray, hence
`canonA _ _ _ _ _ 0 = {(0,0),(2,0)}`. That two-point set is not lattice-convex: any convex
`C` containing `(0,0)` and `(2,0)` contains their real midpoint `(1,0)`, which is an integer
point, so `(1,0)` would have to lie in the set — but it doesn't. This is the same "punch a
hole out of a convex set" mechanism as `EnvelopedConvex.lean`'s `punct`, specialised to the
two-point case, which is the sharpest instance of "the agreement locus is not convex." -/

section Refutation

private def hitSet : Set (ℤ × ℤ) := {((0 : ℤ), (0 : ℤ)), ((2 : ℤ), (0 : ℤ))}

private def ηex : Config Bool :=
  fun w => if w = ((0 : ℤ), (0 : ℤ)) ∨ w = ((2 : ℤ), (0 : ℤ)) then true else false

private def xperex : Config Bool := fun _ => true

private theorem canonA_ex_eq :
    canonA ηex xperex ((1 : ℤ), (0 : ℤ)) (fun _ : ℕ => ({((0 : ℤ), (0 : ℤ))} : Set (ℤ × ℤ)))
      (fun _ : ℕ => ((0 : ℤ), (0 : ℤ))) 0 = hitSet := by
  have hu : ∀ w : ℤ × ℤ, w + ((0 : ℤ), (0 : ℤ)) = w := fun w => by simp
  ext w
  simp only [canonA, Set.mem_ofPred_eq, hitSet, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨_, hagree⟩
    rw [hu w] at hagree
    unfold ηex xperex at hagree
    by_cases hc : w = ((0 : ℤ), (0 : ℤ)) ∨ w = ((2 : ℤ), (0 : ℤ))
    · exact hc
    · rw [if_neg hc] at hagree
      exact absurd hagree (by decide)
  · rintro (rfl | rfl)
    · refine ⟨⟨(0, 0), rfl, 0, by simp⟩, ?_⟩
      decide
    · refine ⟨⟨(0, 0), rfl, 2, ?_⟩, ?_⟩
      · show ((2 : ℤ), (0 : ℤ)) = (0, 0) + ((2 : ℕ) : ℤ) • ((1 : ℤ), (0 : ℤ))
        simp
      · decide

private theorem not_latticeConvex_hitSet : ¬ IsLatticeConvexRegion hitSet := by
  rintro ⟨C, hCconv, _hCclosed, hCeq⟩
  have h0 : ((0 : ℝ), (0 : ℝ)) ∈ C := by
    have hmem : ((0 : ℤ), (0 : ℤ)) ∈ hitSet := Or.inl rfl
    rw [hCeq] at hmem
    simpa [toReal] using hmem
  have h2 : ((2 : ℝ), (0 : ℝ)) ∈ C := by
    have hmem : ((2 : ℤ), (0 : ℤ)) ∈ hitSet := Or.inr rfl
    rw [hCeq] at hmem
    simpa [toReal] using hmem
  have hmid : ((1 : ℝ), (0 : ℝ)) ∈ C := by
    have hcombo := hCconv h0 h2 (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 : ℝ) / 2 + 1 / 2 = 1)
    have heq : (1 / 2 : ℝ) • ((0 : ℝ), (0 : ℝ)) + (1 / 2 : ℝ) • ((2 : ℝ), (0 : ℝ))
        = ((1 : ℝ), (0 : ℝ)) := by
      apply Prod.ext <;> simp
    rwa [heq] at hcombo
  have hmem : ((1 : ℤ), (0 : ℤ)) ∈ hitSet := by
    rw [hCeq]
    simpa [toReal] using hmid
  simp only [hitSet, Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with h | h <;> exact absurd h (by decide)

/-- **`canonA_latticeConvex` is false in general** — the compiled refutation. No hypothesis
on `η xper vl B u` beyond `ChainCanonData`'s existing fields rescues it: this witness uses
only a constant `B`, a constant `u = 0`, and an unconstrained `η`/`xper`, none of which
`ChainCanonData` restricts. -/
theorem not_canonA_latticeConvex :
    ¬ canonA_latticeConvex ηex xperex ((1 : ℤ), (0 : ℤ))
        (fun _ : ℕ => ({((0 : ℤ), (0 : ℤ))} : Set (ℤ × ℤ))) (fun _ : ℕ => ((0 : ℤ), (0 : ℤ))) := by
  intro h
  exact not_latticeConvex_hitSet (canonA_ex_eq ▸ h 0)

end Refutation

/-! ## A sufficient condition: `AgreeContig`

Team-lead's candidate (2026-09-18): the agreement locus is contiguous ("no gaps") along the
ray direction `vl`. The counterexample above violates this at `t = 1`, between the agreeing
points `t = 0` and `t = 2`. Below: for the single-base-point, constant-`u` shape the
counterexample already uses (`B i = {b}`, `u i = u`), `AgreeContig` together with
`Primitive vl` and explicit endpoint witnesses is proved **sufficient** for
`IsLatticeConvexRegion` of the agreement set. `Primitive vl` is needed for the same reason
`ChainGeom.lean:127`'s docstring flags it: without it (e.g. `vl = (2,0)`) the real segment
between two agreeing lattice points would contain extra integer points not of the form
`b + t • vl`, and the theorem would be false. -/

section AgreeContig

variable {α : Type*}

/-- The agreement predicate along the ray `b + t • vl`, `t : ℕ`, for constant `u`. -/
def AgreeAt (η xper : Config α) (b vl u : ℤ × ℤ) (t : ℕ) : Prop :=
  η (b + (t : ℤ) • vl + u) = xper (b + (t : ℤ) • vl)

/-- **No gaps**: if agreement holds at `t1` and `t2`, it holds everywhere between. -/
def AgreeContig (η xper : Config α) (b vl u : ℤ × ℤ) : Prop :=
  ∀ t1 t2 : ℕ, t1 ≤ t2 → AgreeAt η xper b vl u t1 → AgreeAt η xper b vl u t2 →
    ∀ t : ℕ, t1 ≤ t → t ≤ t2 → AgreeAt η xper b vl u t

/-- `canonA` at a single index, specialised to `B i = {b}`, `u i = u` (the counterexample's
shape), matches the ray-parametrised agreement set. -/
theorem canonA_singleton (η xper : Config α) (vl b u : ℤ × ℤ) :
    canonA η xper vl (fun _ : ℕ => ({b} : Set (ℤ × ℤ))) (fun _ : ℕ => u) 0
      = {w : ℤ × ℤ | ∃ t : ℕ, w = b + (t : ℤ) • vl ∧ AgreeAt η xper b vl u t} := by
  ext w
  simp only [canonA, Set.mem_ofPred_eq, Nivat.Colle35.halfStrip, Set.mem_singleton_iff, AgreeAt]
  constructor
  · rintro ⟨⟨b', rfl, t, rfl⟩, hag⟩
    exact ⟨t, rfl, hag⟩
  · rintro ⟨t, rfl, hag⟩
    exact ⟨⟨b, rfl, t, rfl⟩, hag⟩

/-- **The sufficiency theorem.** `Primitive vl`, endpoint witnesses `t1 ≤ t2` at which
agreement holds, minimality/maximality of those endpoints among agreeing indices, and
`AgreeContig` together force the agreement set to be exactly the lattice segment
`{b + t • vl : t1 ≤ t ≤ t2}`, which is lattice-convex (real convex hull = the compact segment
`f '' Icc t1 t2` for the affine parametrisation `f s = b + s • vl`). -/
theorem latticeConvex_of_agreeContig {η xper : Config α} {b vl u : ℤ × ℤ} {t1 t2 : ℕ}
    (hvl : Primitive vl) (h1 : AgreeAt η xper b vl u t1) (h2 : AgreeAt η xper b vl u t2)
    (h12 : t1 ≤ t2) (hc : AgreeContig η xper b vl u)
    (hmin : ∀ t, AgreeAt η xper b vl u t → t1 ≤ t)
    (hmax : ∀ t, AgreeAt η xper b vl u t → t ≤ t2) :
    IsLatticeConvexRegion
      {w : ℤ × ℤ | ∃ t : ℕ, w = b + (t : ℤ) • vl ∧ AgreeAt η xper b vl u t} := by
  have hvl' : IsCoprime vl.1 vl.2 := hvl
  obtain ⟨p, q, hpq⟩ := hvl'
  set f : ℝ → ℝ × ℝ := fun s => ((b.1 : ℝ) + s * (vl.1 : ℝ), (b.2 : ℝ) + s * (vl.2 : ℝ)) with hf
  set C : Set (ℝ × ℝ) := f '' Set.Icc (t1 : ℝ) (t2 : ℝ) with hC
  have hfcont : Continuous f := by fun_prop
  refine ⟨C, ?_, (isCompact_Icc.image hfcont).isClosed, ?_⟩
  · rintro x ⟨sx, hsx, rfl⟩ y ⟨sy, hsy, rfl⟩ a c ha hc' habc
    have hc1 : c = 1 - a := by linarith
    subst hc1
    refine ⟨a * sx + (1 - a) * sy, ⟨?_, ?_⟩, ?_⟩
    · nlinarith [hsx.1, hsy.1]
    · nlinarith [hsx.2, hsy.2]
    · show f (a * sx + (1 - a) * sy) = a • f sx + (1 - a) • f sy
      simp only [hf, Prod.smul_def, Prod.mk_add_mk, smul_eq_mul]
      apply Prod.ext <;> ring
  · ext w
    show (w ∈ {w : ℤ × ℤ | ∃ t : ℕ, w = b + (t : ℤ) • vl ∧ AgreeAt η xper b vl u t}) ↔
        toReal w ∈ C
    rw [hC]
    constructor
    · rintro ⟨t, rfl, hag⟩
      refine ⟨(t : ℝ), ⟨by exact_mod_cast hmin t hag, by exact_mod_cast hmax t hag⟩, ?_⟩
      show f (t : ℝ) = toReal (b + (t : ℤ) • vl)
      apply Prod.ext
      · show (b.1 : ℝ) + (t : ℝ) * (vl.1 : ℝ) = ((b + (t : ℤ) • vl).1 : ℝ)
        have hfst : (b + (t : ℤ) • vl).1 = b.1 + (t : ℤ) * vl.1 := by simp [Prod.smul_def]
        rw [hfst]; push_cast; ring
      · show (b.2 : ℝ) + (t : ℝ) * (vl.2 : ℝ) = ((b + (t : ℤ) • vl).2 : ℝ)
        have hsnd : (b + (t : ℤ) • vl).2 = b.2 + (t : ℤ) * vl.2 := by simp [Prod.smul_def]
        rw [hsnd]; push_cast; ring
    · rintro ⟨s, ⟨hs1, hs2⟩, heq⟩
      have heq' : ((b.1 : ℝ) + s * (vl.1 : ℝ), (b.2 : ℝ) + s * (vl.2 : ℝ)) = toReal w := heq
      have hcomp1 : (w.1 : ℝ) - (b.1 : ℝ) = s * (vl.1 : ℝ) := by
        have h := congrArg Prod.fst heq'
        simp only [toReal] at h
        linarith [h]
      have hcomp2 : (w.2 : ℝ) - (b.2 : ℝ) = s * (vl.2 : ℝ) := by
        have h := congrArg Prod.snd heq'
        simp only [toReal] at h
        linarith [h]
      have hpqR : (p : ℝ) * (vl.1 : ℝ) + (q : ℝ) * (vl.2 : ℝ) = 1 := by exact_mod_cast hpq
      set c : ℤ := p * (w.1 - b.1) + q * (w.2 - b.2) with hcdef
      have hsc : s = (c : ℝ) := by
        have heq2 : s = s * ((p : ℝ) * (vl.1 : ℝ) + (q : ℝ) * (vl.2 : ℝ)) := by rw [hpqR]; ring
        rw [heq2]
        have hexpand : s * ((p : ℝ) * (vl.1 : ℝ) + (q : ℝ) * (vl.2 : ℝ))
            = (p : ℝ) * (s * (vl.1 : ℝ)) + (q : ℝ) * (s * (vl.2 : ℝ)) := by ring
        rw [hexpand, ← hcomp1, ← hcomp2, hcdef]
        push_cast
        ring
      have ht1c : (t1 : ℝ) ≤ (c : ℝ) := hsc ▸ hs1
      have ht2c : (c : ℝ) ≤ (t2 : ℝ) := hsc ▸ hs2
      have ht1c' : (t1 : ℤ) ≤ c := by exact_mod_cast ht1c
      have ht2c' : c ≤ (t2 : ℤ) := by exact_mod_cast ht2c
      have hc_nonneg : 0 ≤ c := le_trans (by exact_mod_cast Nat.zero_le t1) ht1c'
      set t : ℕ := c.toNat with htdef
      have htc : (t : ℤ) = c := Int.toNat_of_nonneg hc_nonneg
      have ht1t : t1 ≤ t := by exact_mod_cast (htc ▸ ht1c' : (t1 : ℤ) ≤ (t : ℤ))
      have ht2t : t ≤ t2 := by exact_mod_cast (htc ▸ ht2c' : (t : ℤ) ≤ (t2 : ℤ))
      have ht_eq_s : (t : ℝ) = s := by
        have hts : (t : ℝ) = (c : ℝ) := by exact_mod_cast htc
        rw [hts, hsc]
      have hweq : w = b + (t : ℤ) • vl := by
        apply Prod.ext
        · show w.1 = b.1 + (t : ℤ) * vl.1
          have key1 : ((b.1 + (t : ℤ) * vl.1 : ℤ) : ℝ) = (w.1 : ℝ) := by
            push_cast
            rw [ht_eq_s]
            linarith [hcomp1]
          exact_mod_cast key1.symm
        · show w.2 = b.2 + (t : ℤ) * vl.2
          have key2 : ((b.2 + (t : ℤ) * vl.2 : ℤ) : ℝ) = (w.2 : ℝ) := by
            push_cast
            rw [ht_eq_s]
            linarith [hcomp2]
          exact_mod_cast key2.symm
      refine ⟨t, hweq, ?_⟩
      exact hc t1 t2 h12 h1 h2 t ht1t ht2t

end AgreeContig

end Nivat.AEnv
