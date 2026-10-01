/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.ChainExhaust

/-!
# What `Exhausts` needs, and what is already a witness (lane Aitem2, 2026-09-19)

Team-lead's follow-up to leaf A's third escape valve dying (`OPEN.md #14`): leaf A's
`exists_chainData` still needs a producer for `Exhausts` (Collé item (ii)'s consequence,
`b3_colle2.txt:498`), which is now proved **not** obtainable from `ChainRecursion`'s
finite-seed half-strip construction (`ItemII.lean`, `not_itemII_chainB`). This file asks: what
does `Exhausts` actually cost, and can it be satisfied at all?

## §0. Exact shapes (`#check`, not guessed from names — `PROTOCOL.md` §23)

```
Nivat.Colle35.Exhausts (A : ℕ → Set (ℤ × ℤ)) (nℓ : ℤ × ℤ) (cz : ℤ) : Prop :=
  (⋃ i, A i) = {z | cz ≤ dot nℓ z}
Nivat.Colle35.ItemII (B : ℕ → Set (ℤ × ℤ)) (nℓ : ℤ × ℤ) (cz : ℤ) : Prop :=
  ∀ i, ∀ z, |z.1| ≤ (i:ℤ)-1 → |z.2| ≤ (i:ℤ)-1 → cz ≤ dot nℓ z → z ∈ B i
```
and `ChainDataGeom.ofPartsExhausts`'s consumed hypothesis (`ChainExhaust.lean:96`) is literally
`(hexh : Exhausts A nℓ cz)` — the *same* `A` that is one of `ofParts`'s data fields, not `B`,
not `Ahat`. So the producer's job is exactly: supply `A : ℕ → Set (ℤ × ℤ)` with
`⋃ i, A i = {z | cz ≤ dot nℓ z}`, alongside the other 24 `ofPartsExhausts` binders (`envB`,
`maxA`, `subBA`, `subAB`, `AhatMono`, `hEnv = EnvOf ↑S`, etc. — unrelated to `Exhausts` itself).

## §1. Necessary condition, `not_itemII_of_halfStrip_finite`'s mechanism turned around

`not_itemII_of_halfStrip_finite` (`ItemII.lean:367`) refutes `ItemII` for a chain trapped in a
single finite half-strip. Read as a *constraint on producers* rather than a refutation of one
candidate chain: **any `A` with `Exhausts A nℓ cz` cannot have all its `A i` inside one fixed
`halfStrip B0 vl` for finite `B0`** — `Exhausts.not_halfStrip_trapped` below, proved directly
from `Exhausts` (not routed through `ItemII`, since `Exhausts` alone is what `ofPartsExhausts`
needs and it is *weaker* than `ItemII` — `exhausts_of_itemII` only needs `ItemII` because that
is how the producer is expected to *build* `Exhausts`, not because `Exhausts` itself requires
the box growth). This is the necessary condition item 2 of the task asked for: `A` must, in
every direction transverse to `vl`, eventually leave every finite half-strip. Equivalently
(`ChainAsm.det_bounded_on_halfStrip`'s contrapositive): `det vl (·)` is **unbounded** on
`⋃ i, A i`.

`ItemII.exists_le_encard` (`ItemII.lean:346`) already gives the complementary "size" necessary
condition **for `ItemII`** (`(B i).encard → ∞`); it is not re-derived here since it is not
`Exhausts`'s own hypothesis and the task's §20 orphan-scan discipline says find, don't rewrite.

## §2. Satisfiability: `Exhausts` alone already has a witness — `RecVJModel`

`Nivat.Colle35.RecVJModel.exhausts_Aw` (`ItemII.lean:667`) is a concrete, kernel-checked
witness of `Exhausts Aw (-1,1) 0` (with `Aw i := Âh i + (2i,2i)`, `Âh` the wedge
`{-3i ≤ z.1 ≤ -2, z.1 ≤ z.2 ≤ 0} ∪ {(0,0)}`), together with `vectors_Aw` supplying the
vector-side facts (`vl ≠ 0`, `det p vl = 0`, `det p vJ ≠ 0`, `Primitive nℓ`, `nℓ ⊥ vl`, …).
So **`Exhausts` by itself is satisfiable, with an explicit non-half-strip-trapped, unboundedly
growing family** — §1's necessary condition is not vacuous, and it is met by this witness
(`Exhausts.not_halfStrip_trapped` applied to it, `RecVJModel.not_halfStrip_trapped_Aw` below).

⚠ **What this witness does *not* do** (reading, not a kernel fact until checked): it was built
to refute `rec_vJ` (§7 of `ItemII.lean`), not to be `EnvOf`-enveloped for any generating set
`S`, and `RecVJModel` is not shown lattice-convex. `ofPartsExhausts`'s other 24 binders —
`hEnv : Env = EnvOf ↑S`, `maxA`, `subAB`, `shellEnv`, `fillCover`, … — are a **disjoint, much
harder** geometric obligation that `Exhausts` does not touch and that this file does not
attempt. The gap flagged in the previous report stands: no witness, partial or full, exists yet
for the *whole* `ChainData`/`ChainDataGeom` structure (28 fields) — only for the two isolated
predicates `Exhausts` / `ItemII` in isolation from `Env`.

🔴 No `ChainRecursion`-based route touched (`OPEN.md #14`). Every witness here is a bare
function `ℕ → Set (ℤ × ℤ)` written by hand, not a recursion.
-/

set_option autoImplicit false

namespace Nivat.Colle35

open Nivat Nivat.LE2

variable {α : Type*}

/-! ## §1: necessary condition -/

/-- **Necessary condition for `Exhausts`**: the exhausting family cannot be trapped inside the
half-strip of a single finite set. Same mechanism as `not_itemII_of_halfStrip_finite`
(`ItemII.lean:367`), applied directly to `Exhausts` rather than routed through `ItemII` — the
point `t • nℓ` at large enough `t` is forced into `⋃ i, A i` by `hexh`, hence into some `A i`,
hence (by the trapping hypothesis) into `halfStrip B0 vl`, where `det vl` is bounded
(`ChainAsm.det_bounded_on_halfStrip`); but `det vl (t • nℓ) = t * det vl nℓ` is unbounded in
`t` since `nℓ ⊥ vl` and `nℓ, vl ≠ 0` force `det vl nℓ ≠ 0`. -/
theorem Exhausts.not_halfStrip_trapped {A : ℕ → Set (ℤ × ℤ)} {B0 : Set (ℤ × ℤ)} {vl nℓ : ℤ × ℤ}
    {cz : ℤ} (hexh : Exhausts A nℓ cz) (hB0 : B0.Finite) (hvl : vl ≠ 0)
    (hperp : dot nℓ vl = 0) (hn : nℓ ≠ 0) (hstrip : ∀ i, A i ⊆ halfStrip B0 vl) : False := by
  obtain ⟨M, hM⟩ := ChainAsm.det_bounded_on_halfStrip hB0 vl
  have hN : 0 < dot nℓ nℓ := ColleReg.dot_self_pos hn
  have hd : det nℓ vl ≠ 0 := ColleReg.det_ne_zero_of_dot hvl hperp hN.ne'
  have hd' : det vl nℓ ≠ 0 := by
    intro h; apply hd; simp only [det] at h ⊢; linarith
  set t : ℤ := |cz| + |M| + 1 with ht
  have ht0 : 0 ≤ t := by rw [ht]; positivity
  have hz : cz ≤ dot nℓ (t • nℓ) := by
    rw [ColleReg.dot_zsmul_right]
    have := le_mul_of_one_le_right ht0 hN
    linarith [le_abs_self cz, abs_nonneg M]
  have hmem : t • nℓ ∈ ⋃ i, A i := by rw [hexh]; exact hz
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hmem
  obtain ⟨hlo, hhi⟩ := hM _ (hstrip i hi)
  rw [ColleReg.det_smul_right] at hlo hhi
  rcases lt_or_gt_of_ne hd' with hneg | hpos
  · have h1 : t * det vl nℓ ≤ t * (-1) := mul_le_mul_of_nonneg_left (by omega) ht0
    linarith [le_abs_self M, abs_nonneg cz]
  · have h1 : t * 1 ≤ t * det vl nℓ := mul_le_mul_of_nonneg_left (by omega) ht0
    linarith [le_abs_self M, abs_nonneg cz]

/-- Packaged as a non-existence statement: no finite `B0` traps every `A i` in its half-strip. -/
theorem Exhausts.not_exists_halfStrip_trapped {A : ℕ → Set (ℤ × ℤ)} {vl nℓ : ℤ × ℤ} {cz : ℤ}
    (hexh : Exhausts A nℓ cz) (hvl : vl ≠ 0) (hperp : dot nℓ vl = 0) (hn : nℓ ≠ 0) :
    ¬ ∃ B0 : Set (ℤ × ℤ), B0.Finite ∧ ∀ i, A i ⊆ halfStrip B0 vl := by
  rintro ⟨B0, hB0, hstrip⟩
  exact hexh.not_halfStrip_trapped hB0 hvl hperp hn hstrip

/-! ## §2: satisfiability, on `RecVJModel`'s existing witness -/

/-- `RecVJModel.Aw` meets §1's necessary condition: it is not trapped in any single finite
half-strip. Sanity check that the necessary condition is non-vacuous and is actually met by
the one witness on hand. -/
theorem RecVJModel.not_halfStrip_trapped_Aw :
    ¬ ∃ B0 : Set (ℤ × ℤ), B0.Finite ∧ ∀ i, RecVJModel.Aw i ⊆ halfStrip B0 (1, 1) :=
  RecVJModel.exhausts_Aw.not_exists_halfStrip_trapped
    (by decide) (by decide) (by decide)

#print axioms Nivat.Colle35.Exhausts.not_halfStrip_trapped
#print axioms Nivat.Colle35.Exhausts.not_exists_halfStrip_trapped
#print axioms Nivat.Colle35.RecVJModel.not_halfStrip_trapped_Aw

/-! ## §3: elaborator-derived binder count of `ofPartsExhausts` (team-lead request,
2026-09-19).  `forallTelescope` walks the declaration's own type and counts the Pi-binders
mechanically — not a hand count of the source text. -/

open Lean Meta in
run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let some info := env.find? ``Nivat.Colle35.ChainDataGeom.ofPartsExhausts
    | throwError "declaration not found"
  forallTelescope info.type fun xs _ => do
    logInfo m!"ofPartsExhausts: {xs.size} total Pi-binders (elaborator count)"

/-! ## §4: does `ItemII` contradict `ChainData`'s actual fields? (team-lead correction,
2026-09-19 — the earlier "escape valve is dead" reading was wrong: `not_itemII_of_chain` /
`not_itemII_chainB` (`ItemII.lean:396,422`) both take `hchain : ∀ i, B (i+1) ⊆ halfStrip (A i)
vl` as an *explicit extra hypothesis*, and `hchain` is **not** a `ChainData` field — `ChainData`
only has the reverse-direction field `subAB : A i ⊆ B (i+1)` (`Lemma35.lean:720`). `hchain` is
exactly `ChainRecursion`'s construction choice `B (i+1) := A i`, already ruled dead
(`OPEN.md #14`). So the refutation is of "`ChainData` + finite seed + `hchain`", not of
`ChainData`'s field table. This section answers the reopened question directly, on the three
real relational fields (`subBA`, `subAB`, `subStrip` — the `Env`/shell/fill fields are untouched,
same scope caveat as §2).

**Answer: consistent, not contradictory.** A single box family, taken as both `B` and `A`
(so `subBA` is `⊆`-refl and `subStrip` is `subset_halfStrip` with `t = 0`), satisfies `ItemII`
together with `subBA`/`subAB`/`subStrip`, while `hchain` provably **fails** for it — so this
witness is not disguised `ChainRecursion` output, and item (ii) is not excluded by the three
real fields alone. This does not settle the full 28-field `ChainData`/`ChainDataGeom` structure
(the `Env`/shell/fill obligations are a disjoint, harder gap, per §2's caveat) — it settles only
the `subBA`/`subAB`/`subStrip` triple, which is exactly what `not_itemII_of_chain`'s hypotheses
touch. -/

namespace FieldWitness

/-- The box `|z.1| ≤ i`, `0 ≤ z.2 ≤ i` — grows to cover any given quadrant-restricted region,
same shape as `ItemII.exists_le_encard`'s witness sets, but written out as an explicit family
rather than extracted from a `Finset.sup`. -/
def Bw (i : ℕ) : Set (ℤ × ℤ) := {z | |z.1| ≤ (i : ℤ) ∧ 0 ≤ z.2 ∧ z.2 ≤ (i : ℤ)}

theorem itemII_Bw : ItemII Bw (0, 1) 0 := by
  intro i z h1 h2 hz
  simp only [Bw, Set.mem_ofPred_eq, dot] at hz ⊢
  rw [abs_le] at h1 h2
  refine ⟨abs_le.mpr ?_, ?_, ?_⟩ <;> omega

/-- `Bw` is monotone, so it serves as `subAB` (`A i ⊆ B (i+1)`, taking `A := Bw`). -/
theorem subAB_Bw : ∀ i, Bw i ⊆ Bw (i + 1) := by
  intro i z hz
  simp only [Bw, Set.mem_ofPred_eq] at hz ⊢
  have : (i : ℤ) ≤ (i : ℤ) + 1 := by linarith
  refine ⟨hz.1.trans this, hz.2.1, hz.2.2.trans this⟩

/-- `hchain` fails for this witness: `Bw 1` reaches `y = 1`, but `halfStrip (Bw 0) (1,0)` is
pinned at `y = 0` (`Bw 0 = {(0,0)}`, and the strip direction `(1,0)` cannot change `y`). So this
witness is not `ChainRecursion`'s `B (i+1) := A i` in disguise. -/
theorem not_hchain_Bw : ¬ ∀ i, Bw (i + 1) ⊆ halfStrip (Bw i) (1, 0) := by
  intro h
  have hmem : ((0 : ℤ), (1 : ℤ)) ∈ Bw 1 := by simp [Bw]
  obtain ⟨b, hb, t, ht⟩ := h 0 hmem
  simp only [Bw, Set.mem_ofPred_eq] at hb
  simp only [Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul, mul_one, mul_zero] at ht
  omega

/-- **The positive half of §4's question**: `ItemII` together with the three real `ChainData`
fields (`subBA`, `subAB`, `subStrip`) is jointly satisfiable, by a witness that is provably not
`ChainRecursion`'s construction. -/
theorem fields_consistent_with_itemII :
    ItemII Bw (0, 1) 0 ∧
      (∀ i, Bw i ⊆ Bw i) ∧
      (∀ i, Bw i ⊆ Bw (i + 1)) ∧
      (∀ i, Bw i ⊆ halfStrip (Bw i) (1, 0)) ∧
      ¬ (∀ i, Bw (i + 1) ⊆ halfStrip (Bw i) (1, 0)) :=
  ⟨itemII_Bw, fun _ => Set.Subset.refl _, subAB_Bw, fun _ => subset_halfStrip _ _,
    not_hchain_Bw⟩

end FieldWitness

/-! ## §5: `ItemII` itself is never half-strip-trapped (sub-question 2 — the strongest
consequence on `B`'s own shape, applied directly rather than routed through `Exhausts`'s derived
`A`). Trivial corollaries of the existing `not_itemII_of_halfStrip_finite`
(`ItemII.lean:367`), stated in the contrapositive shape that a *producer of `B`* needs: whatever
`B` a construction supplies for item (ii), it cannot be half-strip-trapped, on top of
`ItemII.exists_le_encard`'s cardinality bound — together, item (ii) forces both unbounded size
**and** unbounded reach transverse to `vl`. -/

theorem ItemII.not_halfStrip_trapped {B : ℕ → Set (ℤ × ℤ)} {B0 : Set (ℤ × ℤ)} {vl nℓ : ℤ × ℤ}
    {cz : ℤ} (hII : ItemII B nℓ cz) (hB0 : B0.Finite) (hvl : vl ≠ 0)
    (hperp : dot nℓ vl = 0) (hn : nℓ ≠ 0) (hstrip : ∀ i, B i ⊆ halfStrip B0 vl) : False :=
  not_itemII_of_halfStrip_finite hB0 hvl hperp hn hstrip cz hII

theorem ItemII.not_exists_halfStrip_trapped {B : ℕ → Set (ℤ × ℤ)} {vl nℓ : ℤ × ℤ} {cz : ℤ}
    (hII : ItemII B nℓ cz) (hvl : vl ≠ 0) (hperp : dot nℓ vl = 0) (hn : nℓ ≠ 0) :
    ¬ ∃ B0 : Set (ℤ × ℤ), B0.Finite ∧ ∀ i, B i ⊆ halfStrip B0 vl := by
  rintro ⟨B0, hB0, hstrip⟩
  exact hII.not_halfStrip_trapped hB0 hvl hperp hn hstrip

end Nivat.Colle35

#print axioms Nivat.Colle35.FieldWitness.itemII_Bw
#print axioms Nivat.Colle35.FieldWitness.subAB_Bw
#print axioms Nivat.Colle35.FieldWitness.not_hchain_Bw
#print axioms Nivat.Colle35.FieldWitness.fields_consistent_with_itemII
#print axioms Nivat.Colle35.ItemII.not_halfStrip_trapped
#print axioms Nivat.Colle35.ItemII.not_exists_halfStrip_trapped
