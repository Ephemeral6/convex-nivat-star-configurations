/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.Lemma35
import Nivat.External.Colle.LatticeEdges
import Nivat.External.Colle.GenClosureWeaken

/-!
# Wiring LatticeEdges to Lemma35 ChainData

This file connects `Nivat.LE2.EnvOf` from `LatticeEdges.lean` (the real predicate
"is an `E(U)`-enveloped set", Colle Definition 3.2) to the `ChainData` structure in
`Lemma35.lean` (`Lemma35.lean:695-758`: 8 data fields + 19 proof obligations).

## Status (2026-09-13)

### What is proved here

1. **Box toolkit** (`finite_box`, `box_mono`, `two_le_face_box_*`, `envOf_sq1_box`,
   `box_subset_halfStrip`).  The workhorse is `envOf_sq1_box`: *every* non-degenerate
   lattice box is `E(sq1)`-enveloped.  It discharges `envB`, `envA` and `shellEnv`
   for any box-shaped witness.

2. `chainData_wired_but_incomplete` — the `sq1 ⊊ sq2` witness with `Env := EnvOf sq1`,
   **withdrawn 2026-09-16**.  Its statement is literally that of the proved, sorry-free
   `nonempty_chainData` (`Lemma35.lean:768-770`), so its `sorry` was closable in one
   line; what was worth keeping is the refutation in item 3, which stands alone.  See
   the withdrawal note at §"Witness (A)".

3. `maximalHat_wired_refuted` — **the remaining `sorry` is FALSE, not merely hard**.
   Any `ChainData` at these parameters whose data agrees with the wired witness on
   `Env`, `B 0`, `Ahat 0`, `kk 0`, `u 0` is contradictory: `box (0,0) (2,1)` is
   `E(sq1)`-enveloped, contains `sq1`, sits inside `H_{sq1}(ℓ)`, satisfies the
   agreement clause, and is not contained in `sq1`.  The obstruction is structural:
   `η` and `x_per` here differ at exactly ONE lattice point, so the agreement clause
   of `maximalHat` can forbid only one point, while nothing else in `Enveloped` pins
   the set down at that point — a finite enveloped set inside an infinite half-strip
   can always be enlarged past a single forbidden point.  `nonempty_chainData` escapes
   this only by taking `Env := fun T => T ⊆ {0,(1,0)}`, which is an ad-hoc
   bounded-subset predicate, not `EnvOf U` for any `U`.

   *Correction 2026-09-16:* the sentence above used to read "while `Enveloped` has no
   convexity requirement".  That clause became false when convexity was added back to
   `WeaklyEnveloped` (commit `ea5bbc5`), and it was flagged as possibly making this
   refutation stale.  **It does not.**  The witness is `box (0,0) (2,1)`, and a box is
   convex, so it survives the convexity clause untouched; `#print axioms
   Nivat.Colle35.maximalHat_wired_refuted` measures
   `[propext, Classical.choice, Quot.sound]`.  Only the explanatory clause was wrong,
   never the theorem.

   An independent audit argues the obstruction is not specific to the data chosen here:
   `Enveloped sq1 T` forces `T` bounded in all four axis directions, hence finite; and
   adjoining `(m,0),(m,1)` for large `m` to any finite `E(sq1)`-enveloped `T` keeps it
   `E(sq1)`-enveloped (no new edge normal is created), keeps it in the half-strip
   whenever `0 ∈ B i`, and avoids the single forbidden point.  So NO choice of `Ahat`
   can satisfy `maximalHat` at these `η, x_per` with `Env := EnvOf sq1`.
   **That general claim is argued on paper only — it is NOT formalised here.**  What is
   machine-checked is the special case `maximalHat_wired_refuted`.

4. `chainB` — **a COMPLETE, `sorry`-free, genuinely non-degenerate `ChainData`**, at a
   different parameter point (`η := fun z => decide (2 ≤ z.1)`, window
   `S := {(0,0),(1,0)}`, `gen := (1,0)`).  All 19 obligations are proved, with
   `Env := EnvOf sq1` (the real envelope predicate), a strictly growing chain
   `B i = box (0,0) (1+i, 1)` running along `v_ℓ = (1,0)` exactly as in Colle, and
   shells `Â_i^{(ε)} = box (0,0) (1+i+ε, 1)` thickening along `ℓ`.
   Non-degeneracy is itself machine-checked:
   * `chainB_strict_growth`  : `B i ⊊ B (i+1)` for every `i` (real chain growth);
   * `chainB_env_restrictive`: `Env` refuses a point, so it is not `fun _ => True`;
   * `chainB_window_nonvacuous` : `S.erase gen = {0} ≠ ∅`, so `fillStep` is not vacuous;
   * `chainB_maximalHat_nonvacuous` : `maximalHat`'s hypotheses are satisfiable, so the
     field is not vacuously true;
   * `chainB_disagrees_on_shell` : `η ≠ x_per` on `Â_i^{(1)} \ Â_i`, which is Colle's
     (3.1) and what makes `maximalHat` and `shellProper` jointly satisfiable.

### Known weaknesses of `chainB`, stated honestly

* `kk ≡ 0`, so the normalisation `Â_i := A_i - k_i v_ℓ` is trivial and `A i = Â i`.
  Colle's `k_i → ∞`; nothing in `ChainData` forces that.
* `A i = B i`, so `subBA`/`subAB` are satisfied by a chain with only one strict
  inclusion per step rather than Colle's `B_i ⊊ A_i ⊊ B_{i+1}`.
* `maximalHat` is proved WITHOUT using the `Env Tset` hypothesis: for this witness
  `Â_i` is maximal among *all* sets meeting the strip and agreement constraints.
  That is a stronger statement, but it means the convex geometry is not exercised.
* `GeneratesAt η S gen` (an extra hypothesis of `lemma35`, not of `ChainData`) is not
  proved for these parameters.

### What is still NOT proved anywhere

A `ChainData` arising from Colle's actual construction — chain exhausting a half plane,
`k_i → ∞`, maximality genuinely among `E(S_φ)`-enveloped sets — is Lemma 3.5 in full and
is out of scope.
-/

namespace Nivat.Colle35

open Nivat.LE2

/-- Demonstrate that `Nivat.LE2.EnvOf ↑S` can be used as the `Env` field.
This is a type-checking witness, not a full proof. -/
example {α : Type*} (_η _xper : Config α) (_vl : ℤ × ℤ) (S : Finset (ℤ × ℤ))
    (_gen : ℤ × ℤ) : (Set (ℤ × ℤ) → Prop) :=
  EnvOf (↑S : Set (ℤ × ℤ))

/-- The `halfStrip` from `LatticeEdges.lean` and `Lemma35.lean` are definitionally equal. -/
example : @Nivat.LE2.halfStrip = @Nivat.Colle35.halfStrip := rfl

/-! ## A box toolkit for `ChainData` witnesses -/

/-- A lattice box is finite. -/
theorem finite_box (p q : ℤ × ℤ) : (box p q).Finite := by
  have h : box p q ⊆ Set.Icc p q := by
    rintro z ⟨h1, h2, h3, h4⟩
    exact Set.mem_Icc.mpr ⟨⟨h1, h3⟩, ⟨h2, h4⟩⟩
  exact (Set.finite_Icc p q).subset h

/-- Monotonicity of boxes. -/
theorem box_mono {p q p' q' : ℤ × ℤ} (h1 : p'.1 ≤ p.1) (h2 : q.1 ≤ q'.1)
    (h3 : p'.2 ≤ p.2) (h4 : q.2 ≤ q'.2) : box p q ⊆ box p' q' := by
  rintro z ⟨a1, a2, a3, a4⟩
  exact ⟨by omega, by omega, by omega, by omega⟩

theorem two_le_face_box_right {p q : ℤ × ℤ} (hp : p.1 ≤ q.1) (hq : p.2 < q.2) :
    2 ≤ (face (box p q) (1, 0)).encard := by
  rw [face_box_right hp]
  refine two_le_encard_of_pair (a := (q.1, p.2)) (b := (q.1, q.2))
    ⟨rfl, le_rfl, hq.le⟩ ⟨rfl, hq.le, le_rfl⟩ ?_
  intro h; rw [Prod.ext_iff] at h; omega

theorem two_le_face_box_left {p q : ℤ × ℤ} (hp : p.1 ≤ q.1) (hq : p.2 < q.2) :
    2 ≤ (face (box p q) (-1, 0)).encard := by
  rw [face_box_left hp]
  refine two_le_encard_of_pair (a := (p.1, p.2)) (b := (p.1, q.2))
    ⟨rfl, le_rfl, hq.le⟩ ⟨rfl, hq.le, le_rfl⟩ ?_
  intro h; rw [Prod.ext_iff] at h; omega

theorem two_le_face_box_top {p q : ℤ × ℤ} (hq : p.2 ≤ q.2) (hp : p.1 < q.1) :
    2 ≤ (face (box p q) (0, 1)).encard := by
  rw [face_box_top hq]
  refine two_le_encard_of_pair (a := (p.1, q.2)) (b := (q.1, q.2))
    ⟨le_rfl, hp.le, rfl⟩ ⟨hp.le, le_rfl, rfl⟩ ?_
  intro h; rw [Prod.ext_iff] at h; omega

theorem two_le_face_box_bot {p q : ℤ × ℤ} (hq : p.2 ≤ q.2) (hp : p.1 < q.1) :
    2 ≤ (face (box p q) (0, -1)).encard := by
  rw [face_box_bot hq]
  refine two_le_encard_of_pair (a := (p.1, p.2)) (b := (q.1, p.2))
    ⟨le_rfl, hp.le, rfl⟩ ⟨hp.le, le_rfl, rfl⟩ ?_
  intro h; rw [Prod.ext_iff] at h; omega

/-- **Every non-degenerate lattice box is `E(sq1)`-enveloped.**  This is the workhorse:
it discharges `envB`, `envA` and `shellEnv` for any box-shaped `ChainData` witness. -/
theorem envOf_sq1_box {p q : ℤ × ℤ} (hp : p.1 < q.1) (hq : p.2 < q.2) :
    EnvOf sq1 (box p q) := by
  refine envOf_of_E_eq (isLatticeConvexRegion_box p q) (by rw [E_box hp hq, E_sq1]) ?_
  intro n hn
  rw [E_sq1] at hn
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
  rcases hn with rfl | rfl | rfl | rfl
  · rw [encard_face_sq1_right]; exact two_le_face_box_right hp.le hq
  · rw [encard_face_sq1_left]; exact two_le_face_box_left hp.le hq
  · rw [encard_face_sq1_top]; exact two_le_face_box_top hq.le hp
  · rw [encard_face_sq1_bot]; exact two_le_face_box_bot hq.le hp

/-- A box sits in the half-strip `H_B(ℓ)` of a box with the same vertical extent and the
same left edge, in the direction `v_ℓ = (1,0)`. -/
theorem box_subset_halfStrip {a b c : ℤ} (hac : 0 ≤ c) :
    box (0, 0) (a, b) ⊆ Nivat.Colle35.halfStrip (box (0, 0) (c, b)) (1, 0) := by
  rintro z ⟨h1, h2, h3, h4⟩
  refine ⟨(0, z.2), ⟨le_rfl, hac, h3, h4⟩, z.1.toNat, ?_⟩
  have : ((z.1.toNat : ℤ)) = z.1 := Int.toNat_of_nonneg h1
  apply Prod.ext <;> simp [this]

/-! ## Witness (A): the `sq1 ⊊ sq2` chain wired to `EnvOf` — withdrawn 2026-09-16

A theorem `chainData_wired_but_incomplete` stood here: the `sq1 ⊊ sq2` witness with
`Env := EnvOf sq1`, discharging 18 of `ChainData`'s 19 obligations and leaving
`maximalHat` as a `sorry`.  It was **withdrawn**, for two reasons that together leave it
no role:

* Its statement is not open.  It is *literally* the statement of `nonempty_chainData`
  (`Lemma35.lean:768-770`) — same parameters, same type — which is proved and, measured
  2026-09-16, depends only on `[propext, Classical.choice, Quot.sound]`.  So the `sorry`
  was closable in one line, and the name and docstring were the only thing asserting
  otherwise.
* Its informative content already stands on its own.  What was worth recording is that
  *this particular wiring* cannot work, and that is exactly
  `maximalHat_wired_refuted` below, which takes the `ChainData` as a hypothesis and
  derives `False` from the wired data.  It never depended on the withdrawn theorem.

The helper lemmas `chainA_subset_sq2`, `chainA_env` and `shellA_env` went with it; they
had no other user.  `chainB` and its certificates are untouched. -/

/-- **The `maximalHat` obligation of the withdrawn wired witness is FALSE.**

No `ChainData` at these parameters can have `Env = EnvOf sq1` together with
`B 0 = Ahat 0 = sq1`, `kk 0 = 0` and `u 0 = (10,0)`: the box `[0,2] × [0,1]` is
`E(sq1)`-enveloped, contains `sq1`, lies in `H_{sq1}(ℓ) - 0·v_ℓ`, satisfies the
agreement clause (`η` and `x_per` differ only at `(1,0)`, and `z + (10,0) ≠ (1,0)`
for `z.1 ≥ 0`), yet contains `(2,0) ∉ sq1`.

The statement is proved by applying the actual `maximalHat` field, so there is no
transcription risk. -/
theorem maximalHat_wired_refuted
    (c : ChainData (fun z : ℤ × ℤ => decide (z = ((1 : ℤ), (0 : ℤ))))
      (fun _ : ℤ × ℤ => false) ((1 : ℤ), (0 : ℤ)) {0} 0)
    (hEnv : c.Env = EnvOf sq1) (hB : c.B 0 = sq1) (hAhat : c.Ahat 0 = sq1)
    (hkk : c.kk 0 = 0) (hu : c.u 0 = ((10 : ℤ), (0 : ℤ))) : False := by
  have h := c.maximalHat 0 (box ((0 : ℤ), (0 : ℤ)) ((2 : ℤ), (1 : ℤ))) ?_ ?_ ?_ ?_
  · have h2 := h (show ((2 : ℤ), (0 : ℤ)) ∈ box ((0 : ℤ), (0 : ℤ)) ((2 : ℤ), (1 : ℤ)) by
      refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num)
    rw [hAhat, sq1] at h2
    obtain ⟨_, hb, _, _⟩ := h2
    simp only at hb
    omega
  · rw [hEnv]
    exact envOf_sq1_box (by norm_num) (by norm_num)
  · rw [hAhat, sq1]
    exact box_mono (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · rw [hkk, hB, sq1]
    simp only [Nat.cast_zero, zero_smul, add_zero]
    exact box_subset_halfStrip (by norm_num)
  · rw [hkk, hu]
    rintro z ⟨h1, _, _, _⟩
    simp only at h1
    simp only [Nat.cast_zero, zero_smul, zero_add, add_zero, decide_eq_false_iff_not,
      Prod.ext_iff, Prod.fst_add, Prod.snd_add]
    omega

/-! ## Witness (B): a COMPLETE, non-degenerate `ChainData`

Here `η := fun z => decide (2 ≤ z.1)` is the indicator of a half plane, so `η` and
`x_per ≡ false` disagree on a whole *wall*, not at a single point.  That wall is what
pins `Â_i` down and makes `maximalHat` true; the chain `B i = box (0,0) (1+i, 1)` grows
along `v_ℓ = (1,0)` and the translations `u i = (-i, 0)` move the wall out of the way
one column at a time, exactly Colle's picture.  The window is `S = {(0,0),(1,0)}` with
distinguished point `gen = (1,0)`, so the `fillStep` filtration fills one column per
step and is *not* vacuous. -/

/-- A genuinely non-degenerate `ChainData`: all 19 obligations proved, no `sorry`. -/
def chainB : ChainData (fun z : ℤ × ℤ => decide ((2 : ℤ) ≤ z.1))
      (fun _ : ℤ × ℤ => false) ((1 : ℤ), (0 : ℤ))
      {((0 : ℤ), (0 : ℤ)), ((1 : ℤ), (0 : ℤ))} ((1 : ℤ), (0 : ℤ)) := by
  classical
  refine {
    Env := EnvOf sq1
    B := fun i => box (0, 0) (1 + (i : ℤ), 1)
    A := fun i => box (0, 0) (1 + (i : ℤ), 1)
    u := fun i => (-(i : ℤ), 0)
    kk := fun _ => 0
    Ahat := fun i => box (0, 0) (1 + (i : ℤ), 1)
    shell := fun i ε => box (0, 0) (1 + (i : ℤ) + (ε : ℤ), 1)
    shellInf := fun ε => ⋃ i : ℕ, box (0, 0) (1 + (i : ℤ) + (ε : ℤ), 1)
    fill := fun i i₀ ε n =>
      (box (0, 0) (1 + (i : ℤ), 1) ∪ box (0, 0) (1 + (i₀ : ℤ) + (ε : ℤ), 1)) ∪
        box (0, 0) ((n : ℤ), 1)
    envB := ?_, envA := ?_, subBA := ?_, subAB := ?_, subStrip := ?_, agreeA := ?_
    AhatEq := ?_, AhatMono := ?_, maximalHat := ?_, shellFinite := ?_, subShell := ?_
    shellSubInf := ?_, shellInfZero := ?_, shellSubStrip := ?_, shellProper := ?_
    -- `I₀`（第 162 轮，`b3_colle2.txt:520`）：本实例的 shell 字段都不看 `i` 的下界，取 0。
    I₀ := 0
    shellEnv := ?_, fillZero := ?_, fillStep := ?_, fillCover := ?_ }
  · -- envB
    exact fun i => envOf_sq1_box (by simp; omega) (by norm_num)
  · -- envA
    exact fun i => envOf_sq1_box (by simp; omega) (by norm_num)
  · -- subBA
    exact fun _ => subset_rfl
  · -- subAB
    intro i
    exact box_mono (by norm_num) (by push_cast; omega) (by norm_num) (by norm_num)
  · -- subStrip
    exact fun i => Nivat.Colle35.subset_halfStrip _ _
  · -- agreeA
    rintro i z ⟨h1, h2, h3, h4⟩
    simp only at h1 h2
    simp only [decide_eq_false_iff_not, not_le, Prod.fst_add]
    omega
  · -- AhatEq
    intro i; ext z; simp
  · -- AhatMono
    intro i j hij
    exact box_mono (by norm_num) (by simp; omega) (by norm_num) (by norm_num)
  · -- maximalHat: GENUINE.  The half-plane wall `{z.1 ≥ 2}`, pulled back by `u i`,
    -- caps any admissible `Tset` at `z.1 ≤ 1 + i`; the half-strip caps `z.2 ∈ [0,1]`
    -- and `z.1 ≥ 0`.  Together that is exactly `Â_i`.
    intro i Tset _ _ hstrip hagree z hz
    have hs := hstrip hz
    simp only [Nat.cast_zero, zero_smul, add_zero, Set.mem_setOf_eq] at hs
    obtain ⟨b, hb, t, hzt⟩ := hs
    obtain ⟨hb1, hb2, hb3, hb4⟩ := hb
    simp only at hb1 hb2 hb3 hb4
    have hz1 : z.1 = b.1 + (t : ℤ) := by rw [hzt]; simp
    have hz2 : z.2 = b.2 := by rw [hzt]; simp
    have hag := hagree z hz
    simp only [Nat.cast_zero, zero_smul, zero_add, add_zero, decide_eq_false_iff_not,
      not_le, Prod.fst_add] at hag
    have ht : (0 : ℤ) ≤ (t : ℤ) := Int.natCast_nonneg t
    exact ⟨by simp; omega, by simp; omega, by simp; omega, by simp; omega⟩
  · -- shellFinite
    exact fun i ε => finite_box _ _
  · -- subShell
    intro i ε
    exact box_mono (by norm_num) (by simp) (by norm_num) (by norm_num)
  · -- shellSubInf
    exact fun i ε => Set.subset_iUnion (fun j : ℕ => box (0, 0) (1 + (j : ℤ) + (ε : ℤ), 1)) i
  · -- shellInfZero
    intro z hz
    obtain ⟨_, ⟨i, rfl⟩, hz⟩ := hz
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    simp only [Nat.cast_zero, add_zero] at hz
    exact hz
  · -- shellSubStrip
    intro ε _ _ _ i _
    simp only [Nat.cast_zero, zero_smul, add_zero]
    exact box_subset_halfStrip (by omega)
  · -- shellProper: GENUINE, the ε-shell is strictly larger than Â_i
    intro ε _i₀ hε _hEnv i _hi hsub
    have hmem : ((1 + (i : ℤ) + (ε : ℤ), (0 : ℤ)) : ℤ × ℤ) ∈
        box ((0 : ℤ), (0 : ℤ)) (1 + (i : ℤ) + (ε : ℤ), 1) := by
      refine ⟨?_, ?_, ?_, ?_⟩ <;> simp <;> omega
    have h2 := hsub hmem
    obtain ⟨_, hb, _, _⟩ := h2
    simp only at hb
    omega
  · -- shellEnv
    exact ⟨1, 0, by norm_num, fun i _ => envOf_sq1_box (by simp; omega) (by norm_num)⟩
  · -- fillZero
    intro i i₀ ε
    refine Set.union_subset subset_rfl ?_
    simp only [Nat.cast_zero]
    exact fun z hz => Or.inl (box_mono (by norm_num) (by simp; omega)
      (by norm_num) (by norm_num) hz)
  · -- fillStep: GENUINE.  `S.erase gen = {(0,0)}`, so filling `z` requires `z - (1,0)`
    -- to be already filled: one new column per step.
    intro i i₀ ε n z hz
    rcases hz with hz | hz
    · exact Or.inl (Or.inl hz)
    · obtain ⟨h1, h2, h3, h4⟩ := hz
      simp only [Nat.cast_add, Nat.cast_one] at h1 h2 h3 h4
      by_cases hn : z.1 ≤ (n : ℤ)
      · exact Or.inl (Or.inr ⟨by simpa using h1, by simpa using hn,
          by simpa using h3, by simpa using h4⟩)
      · refine Or.inr ⟨z - ((1 : ℤ), (0 : ℤ)), by abel, ?_⟩
        intro b hb
        simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hb
        have hb0 : b = ((0 : ℤ), (0 : ℤ)) := by
          rcases hb.2 with h | h
          · exact h
          · exact absurd h hb.1
        subst hb0
        refine Or.inr ⟨?_, ?_, ?_, ?_⟩ <;>
          simp only [zero_add, Prod.fst_sub, Prod.snd_sub] <;> simp <;> omega
  · -- fillCover.  Round 80 (`Lemma35.lean:765`) rephrased this field against the unrestricted
    -- `Colle37.GenClosure`; `genFill_of_abstract_fill` (`GenClosureWeaken.lean:116`) converts
    -- the filtration argument above into it, consuming only the `fillZero`/`fillStep` scripts
    -- re-run here at the fixed `(i, i₀, ε)`.  Its `hconv` is `S.erase gen = {(0,0)}`, which is
    -- lattice convex as a singleton — the one genuinely new side condition, and it holds.
    intro ε i₀ _hε _hEnv i _hi z hz
    have herase : ({((0 : ℤ), (0 : ℤ)), ((1 : ℤ), (0 : ℤ))} : Finset (ℤ × ℤ)).erase
        ((1 : ℤ), (0 : ℤ)) = {((0 : ℤ), (0 : ℤ))} := by decide
    refine Nivat.GenClosureWeaken.genFill_of_abstract_fill
      (S := {((0 : ℤ), (0 : ℤ)), ((1 : ℤ), (0 : ℤ))}) (gen := ((1 : ℤ), (0 : ℤ)))
      (fill := fun n =>
        (box (0, 0) (1 + (i : ℤ), 1) ∪ box (0, 0) (1 + (i₀ : ℤ) + (ε : ℤ), 1)) ∪
          box (0, 0) ((n : ℤ), 1))
      (by decide) ?_ ?_ ?_ (1 + (i : ℤ) + (ε : ℤ)).toNat z ?_
    · rw [herase]; exact Nivat.Colle37.latticeConvex_singleton _
    · -- fillZero at this `(i, i₀, ε)`
      refine Set.union_subset subset_rfl ?_
      simp only [Nat.cast_zero]
      exact fun z hz => Or.inl (box_mono (by norm_num) (by simp; omega)
        (by norm_num) (by norm_num) hz)
    · -- fillStep at this `(i, i₀, ε)`
      intro n z hz
      rcases hz with hz | hz
      · exact Or.inl (Or.inl hz)
      · obtain ⟨h1, h2, h3, h4⟩ := hz
        simp only [Nat.cast_add, Nat.cast_one] at h1 h2 h3 h4
        by_cases hn : z.1 ≤ (n : ℤ)
        · exact Or.inl (Or.inr ⟨by simpa using h1, by simpa using hn,
            by simpa using h3, by simpa using h4⟩)
        · refine Or.inr ⟨z - ((1 : ℤ), (0 : ℤ)), by abel, ?_⟩
          intro b hb
          rw [herase, Finset.mem_singleton] at hb
          subst hb
          refine Or.inr ⟨?_, ?_, ?_, ?_⟩ <;>
            simp only [zero_add, Prod.fst_sub, Prod.snd_sub] <;> simp <;> omega
    · -- `z` is reached at filtration index `(1 + i + ε).toNat`
      refine Or.inr ?_
      obtain ⟨h1, h2, h3, h4⟩ := hz
      simp only at h1 h2 h3 h4
      have hcast : (((1 + (i : ℤ) + (ε : ℤ)).toNat : ℕ) : ℤ) = 1 + (i : ℤ) + (ε : ℤ) :=
        Int.toNat_of_nonneg (by omega)
      exact ⟨by simpa using h1, by rw [hcast]; simpa using h2, by simpa using h3,
        by simpa using h4⟩

/-! ### Machine-checked non-degeneracy certificates for `chainB` -/

/-- The chain of `chainB` STRICTLY increases at every step — unlike `nonempty_chainData`,
whose `B`, `A`, `Ahat` are all the constant family `fun _ => {0}`. -/
theorem chainB_strict_growth (i : ℕ) : chainB.B i ⊂ chainB.B (i + 1) := by
  constructor
  · exact box_mono (by norm_num) (by push_cast; omega) (by norm_num) (by norm_num)
  · intro hsub
    have hmem : ((1 + ((i : ℤ) + 1), (0 : ℤ)) : ℤ × ℤ) ∈ chainB.B (i + 1) := by
      refine ⟨?_, ?_, ?_, ?_⟩ <;> (try push_cast) <;> (try simp) <;> (try omega)
    obtain ⟨_, hb, _, _⟩ := hsub hmem
    simp only at hb
    omega

/-- `chainB.Env` is a genuinely restrictive predicate: it refuses a single point.
So it is not the vacuous `fun _ => True`, and not an ad-hoc predicate tailored to the
data the way `nonempty_chainData`'s `fun T => T ⊆ {0,(1,0)}` is. -/
theorem chainB_env_restrictive : ¬ chainB.Env ({0} : Set (ℤ × ℤ)) := by
  intro h
  have hE : E ({0} : Set (ℤ × ℤ)) = ∅ := by
    ext n
    simp only [mem_E_iff, Set.mem_empty_iff_false, iff_false, not_and]
    intro _ hnt
    exact Set.not_nontrivial_singleton (hnt.mono (face_subset _ _))
  have h2 := h.2
  rw [hE, Set.encard_empty] at h2
  have h3 : E sq1 = ∅ := Set.encard_eq_zero.mp h2.symm
  rw [E_sq1] at h3
  have hcon : ((1 : ℤ), (0 : ℤ)) ∈ (∅ : Set (ℤ × ℤ)) := h3 ▸ Set.mem_insert _ _
  simpa using hcon

/-- The window of `chainB` really constrains `fillStep`: `S.erase gen = {(0,0)} ≠ ∅`.
Contrast `nonempty_chainData`, where `S = {0}` and `gen = 0` give `S.erase gen = ∅`,
making `fillStep` satisfiable by ANY `fill` family whatsoever. -/
theorem chainB_window_nonvacuous :
    (({((0 : ℤ), (0 : ℤ)), ((1 : ℤ), (0 : ℤ))} : Finset (ℤ × ℤ)).erase
      ((1 : ℤ), (0 : ℤ))) = {((0 : ℤ), (0 : ℤ))} := by decide

/-- `maximalHat` is not vacuously true for `chainB`: its hypotheses are satisfiable,
witnessed at `Tset := Ahat i`. -/
theorem chainB_maximalHat_nonvacuous (i : ℕ) :
    chainB.Env (chainB.Ahat i) ∧ chainB.Ahat i ⊆ chainB.Ahat i ∧
      chainB.Ahat i ⊆ {z | z + ((chainB.kk i : ℕ) : ℤ) • ((1 : ℤ), (0 : ℤ)) ∈
        Nivat.Colle35.halfStrip (chainB.B i) ((1 : ℤ), (0 : ℤ))} := by
  refine ⟨envOf_sq1_box (by simp; omega) (by norm_num), subset_rfl, ?_⟩
  intro z hz
  simp only [Set.mem_setOf_eq]
  have : (chainB.kk i : ℕ) = 0 := rfl
  rw [this]
  simp only [Nat.cast_zero, zero_smul, add_zero]
  exact Nivat.Colle35.subset_halfStrip _ _ hz

/-- `η` really disagrees with `x_per` on the outer shell `Â_i^{(1)} \ Â_i`.  This is
Colle's (3.1), and it is exactly what makes `maximalHat` and `shellProper` jointly
satisfiable: without it the two fields would be contradictory. -/
theorem chainB_disagrees_on_shell (i : ℕ) :
    ∃ z ∈ chainB.shell i 1, (decide ((2 : ℤ) ≤ (z + (((chainB.kk i : ℕ) : ℤ) •
      ((1 : ℤ), (0 : ℤ)) + chainB.u i)).1) : Bool) ≠ (false : Bool) := by
  refine ⟨((1 + (i : ℤ) + 1, (0 : ℤ)) : ℤ × ℤ), ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩ <;> simp <;> omega
  · have hk : (chainB.kk i : ℕ) = 0 := rfl
    have hu : chainB.u i = (-(i : ℤ), 0) := rfl
    rw [hk, hu]
    simp only [Nat.cast_zero, zero_smul, zero_add, ne_eq, decide_eq_false_iff_not,
      not_not, Prod.fst_add]
    omega

/-- **`ChainData` is satisfiable non-degenerately.**  Unlike `nonempty_chainData`, this
witness has a strictly growing chain, the genuine envelope predicate `EnvOf sq1`, a
non-vacuous generation window, and a non-vacuous `maximalHat`. -/
theorem chainData_nondegenerate :
    Nonempty (ChainData (fun z : ℤ × ℤ => decide ((2 : ℤ) ≤ z.1))
      (fun _ : ℤ × ℤ => false) ((1 : ℤ), (0 : ℤ))
      {((0 : ℤ), (0 : ℤ)), ((1 : ℤ), (0 : ℤ))} ((1 : ℤ), (0 : ℤ))) := ⟨chainB⟩

end Nivat.Colle35
