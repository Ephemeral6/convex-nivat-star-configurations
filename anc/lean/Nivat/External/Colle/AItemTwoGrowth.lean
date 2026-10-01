/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.ChainAssemble
import Nivat.External.Colle.ItemII
import Nivat.External.Colle.LatticeEdges
import Nivat.External.Colle.HbaseFlatSeed
import Nivat.External.Colle.L1Line0
import Nivat.External.Colle.AbsorbEnv
import Nivat.External.Colle.MaximalEnveloped

/-!
# Collé item (ii), transcribed fresh against `b3_colle2.txt:464-488` (lane Aitem2, 2026-09-20)

Leaf A's last surviving escape hatch. `ChainAsm.not_chainDataGeom_of_chainRecursion`
(`ChainAssemble.lean:520`) shows `ChainRecursion`'s specific step `B (i+1) := A i` produces no
`ChainDataGeom` from a finite seed, independent of `kk`/`u`/`p`/shell/fill. The question is
whether Collé's actual growth condition — item (ii) — rescues the recursion, or whether the
same obstruction survives once item (ii) is imposed.

## §0. The source text, quoted in full (`b3_colle2.txt:464-476`)

```
The assumption on item (i) allows us to construct a sequence of E(S_φ)-enveloped sets

  B' ⊂ B_1 ⊂ A_1 ⊂ B_2 ⊂ A_2 ⊂ ⋯ ⊂ B_i ⊂ A_i ⊂ ⋯

such that, for each i ∈ ℕ:

(i)   B_i ⊂ ℤ² is an E(S_φ)-enveloped set with B_i ∩ ℓ_{B_i} ⊂ ℓ^(-),
(ii)  B_i contains both A_{i-1} and [-i+1,i-1]² ∩ H(ℓ^(-)),
(iii) (T^{u_i}η)|B_i = x_per|B_i for some u_i ∈ ℤ², but
      (T^{u_i}η)|H_{B_i}(ℓ) ≠ x_per|H_{B_i}(ℓ),
(iv)  fixed a sequence (u_i) fulfilling the previous item, A_i is a maximal set … among all
      E(S_φ)-enveloped sets 𝒯 ⊂ ℤ² such that B_i ⊂ 𝒯 ⊂ H_{B_i}(ℓ) and
      (T^{u_i}η)|𝒯 = x_per|𝒯.
```

Item (ii) is a **conjunction of two containments**: `A_{i-1} ⊆ B_i` and
`[-i+1,i-1]² ∩ H(ℓ^(-)) ⊆ B_i`. `ItemII` (`ItemII.lean:80`) transcribes only the second
containment — the box half — on the stated ground that the first is `ChainData.subAB`
(`Lemma35.lean:720`, `A i ⊆ B (i+1)`, the same containment after the index shift). This file
re-derives that claim rather than assuming it: `GrowsII` below states **both** conjuncts, taking
`A` as an explicit argument exactly as the paper does, so nothing is assumed about where `A`
comes from.

## §1. Index convention

The paper's chain is indexed by `i ∈ ℕ = {1, 2, …}`, starting from the seed `B'`. Our `ℕ`
includes `0`. Reusing the convention already ruled on for `ItemII` (`ItemII.lean:60-67`,
"index convention, team-lead ruling 2026-09-19") **exactly**, so the two files stay
term-for-term comparable: Lean's `B 0` is the paper's seed `B'`, so paper's `B_i` is Lean's
`B i` directly (no shift), and the box bound `[-i+1,i-1]²` is Lean's `|z.1| ≤ i-1`. Paper's
`A_{i-1}` is then Lean's `A (i-1)` (natural subtraction; the `i = 0` instance is vacuous on
both conjuncts — box bound `≤ -1` is unsatisfiable, and the containment degenerates to
`A 0 ⊆ B 0`, an extra, faithfully-harmless stipulation matching Lean's `i-1` truncation to `0`).


## §2. Verdict

**Item (ii) rescues the recursion from this specific obstruction.** The finite-seed
counterexample (`not_chainDataGeom_of_chainRecursion`) routes entirely through
`ChainDataGeom.false_of_chain_halfStrip`, whose only chain-shape input is
`hchain : ∀ i, B (i+1) ⊆ halfStrip (A i) vl` — `ChainRecursion`'s construction choice, not a
`ChainData` field. `not_growsII_of_chain` below shows the *same* obstruction (`hchain` + finite
seed) is **already incompatible with `GrowsII`** on its own (extending `not_itemII_of_chain`,
`ItemII.lean:396`, to the two-conjunct transcription, confirming no drift): so a chain built to
satisfy item (ii) cannot be `ChainRecursion`'s chain in the first place. And
`growsII_fields_consistent` exhibits a witness where `GrowsII` holds together with the three
real `ChainData` relational fields (`subBA`, `subAB`, `subStrip`) while `hchain` **fails** — so
the trap this counterexample depends on is not forced by item (ii); it is `ChainRecursion`'s
extra, avoidable choice. This does **not** construct a full `ChainDataGeom` (the `Env`/shell/fill
25 fields are untouched, same scope caveat as `ExhaustsProbe.lean` §2/§4) — it shows the
finite-seed counterexample does not survive as a general obstruction to *every* item
(ii)-honouring construction, only to `ChainRecursion`'s specific one.

🔴 No `ChainRecursion`-based route touched as a construction target (`OPEN.md #14`); it is only
cited here as the thing being refuted, per `not_chainDataGeom_of_chainRecursion`'s own use.
-/

set_option autoImplicit false

namespace Nivat.Colle35

open Nivat Nivat.LE2

/-! ## §3: `GrowsII`, the full two-conjunct transcription -/

/-- **Collé item (ii), both conjuncts** (`b3_colle2.txt:474`), verbatim: "`B_i` contains both
`A_{i-1}` and `[-i+1,i-1]² ∩ H(ℓ^(−))`". Indices per §1: paper's `(B_i, A_{i-1})` is Lean's
`(B i, A (i-1))`, matching `ItemII`'s own convention exactly. Unlike `ItemII`, `A` is an
explicit parameter and both containments are required. -/
def GrowsII (B A : ℕ → Set (ℤ × ℤ)) (nℓ : ℤ × ℤ) (cz : ℤ) : Prop :=
  ∀ i : ℕ,
    A (i - 1) ⊆ B i ∧
      ∀ z : ℤ × ℤ, |z.1| ≤ (i : ℤ) - 1 → |z.2| ≤ (i : ℤ) - 1 → cz ≤ dot nℓ z → z ∈ B i

/-- The box conjunct alone, **literally** `ItemII` — no reindexing needed, confirming §1's
convention lines up with `ItemII.lean`'s. -/
theorem itemII_of_growsII {B A : ℕ → Set (ℤ × ℤ)} {nℓ : ℤ × ℤ} {cz : ℤ}
    (h : GrowsII B A nℓ cz) : ItemII B nℓ cz :=
  fun i z h1 h2 hz => (h i).2 z h1 h2 hz

/-- The containment conjunct alone: `A (i-1) ⊆ B i`, exactly `ChainData.subAB` after the
index shift `i ↦ i - 1`. -/
theorem subAB_of_growsII {B A : ℕ → Set (ℤ × ℤ)} {nℓ : ℤ × ℤ} {cz : ℤ}
    (h : GrowsII B A nℓ cz) : ∀ i, A (i - 1) ⊆ B i :=
  fun i => (h i).1

/-! ## §4: does the finite-seed obstruction survive `GrowsII`? -/

/-- **`GrowsII` is already incompatible with a chain trapped by `hchain` in a finite seed** —
same mechanism as `not_itemII_of_chain` (`ItemII.lean:396`), extended to the full two-conjunct
transcription (only the box conjunct is used in the proof; the containment conjunct is carried
for faithfulness but not needed for this particular contradiction). This confirms
`not_chainDataGeom_of_chainRecursion`'s obstruction is not an accident of the box-only
`ItemII`: strengthening the hypothesis to the literal two-conjunct item (ii) does not change
the outcome for `hchain`-shaped chains — they are refuted either way. -/
theorem not_growsII_of_chain {B A : ℕ → Set (ℤ × ℤ)} {vl nℓ : ℤ × ℤ}
    (hB0 : (B 0).Finite) (hvl : vl ≠ 0) (hperp : dot nℓ vl = 0) (hn : nℓ ≠ 0)
    (subStrip : ∀ i, A i ⊆ halfStrip (B i) vl)
    (hchain : ∀ i, B (i + 1) ⊆ halfStrip (A i) vl) (cz : ℤ) : ¬ GrowsII B A nℓ cz := by
  intro h
  exact not_itemII_of_chain hB0 hvl hperp hn subStrip hchain cz (itemII_of_growsII h)

/-! ## §5: `GrowsII` is consistent with the real `ChainData` fields, with `hchain` failing —
so the obstruction is `ChainRecursion`'s to own, not item (ii)'s. Same box-family idea as
`ExhaustsProbe.lean §4`, extended to supply the `A_{i-1} ⊆ B_i` conjunct as well. -/

namespace GrowsFieldWitness

/-- The box `|z.1| ≤ i`, `0 ≤ z.2 ≤ i`. -/
def Bw (i : ℕ) : Set (ℤ × ℤ) := {z | |z.1| ≤ (i : ℤ) ∧ 0 ≤ z.2 ∧ z.2 ≤ (i : ℤ)}

theorem mono_Bw : ∀ i, Bw i ⊆ Bw (i + 1) := by
  intro i z hz
  simp only [Bw, Set.mem_ofPred_eq] at hz ⊢
  have : (i : ℤ) ≤ (i : ℤ) + 1 := by linarith
  exact ⟨hz.1.trans this, hz.2.1, hz.2.2.trans this⟩

/-- **`GrowsII` holds for `Bw` taken as both `B` and `A`**: the box conjunct is `Bw`'s defining
property (same computation as `ExhaustsProbe.lean`'s `itemII_Bw`), and the containment conjunct
`A (i-1) ⊆ B i` is `mono_Bw` at `i - 1` (`Nat.sub_add_cancel` handles `i ≥ 1`; `i = 0` is
`Bw 0 ⊆ Bw 0`, refl). -/
theorem growsII_Bw : GrowsII Bw Bw (0, 1) 0 := by
  intro i
  refine ⟨?_, ?_⟩
  · cases i with
    | zero => exact Set.Subset.refl _
    | succ i => simpa using mono_Bw i
  · intro z h1 h2 hz
    simp only [Bw, Set.mem_ofPred_eq, dot] at hz ⊢
    rw [abs_le] at h1 h2
    refine ⟨abs_le.mpr ?_, ?_, ?_⟩ <;> omega

/-- `hchain` fails for this witness: `Bw 1` reaches `y = 1`, but `halfStrip (Bw 0) (1,0)` is
pinned at `y = 0` (`Bw 0 = {(0,0)}`, and the strip direction `(1,0)` cannot change `y`). So a
`GrowsII`-honouring family need not be, and here provably is not, `ChainRecursion`'s
`B (i+1) := A i` in disguise. -/
theorem not_hchain_Bw : ¬ ∀ i, Bw (i + 1) ⊆ halfStrip (Bw i) (1, 0) := by
  intro h
  have hmem : ((0 : ℤ), (1 : ℤ)) ∈ Bw 1 := by simp [Bw]
  obtain ⟨b, hb, t, ht⟩ := h 0 hmem
  simp only [Bw, Set.mem_ofPred_eq] at hb
  simp only [Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul, mul_one, mul_zero] at ht
  omega

/-- **The positive half of §5**: `GrowsII` together with the three real `ChainData` fields
(`subBA`, `subAB`, `subStrip`, all with `A := Bw` too) is jointly satisfiable, by a witness
that is provably not `ChainRecursion`'s construction. -/
theorem growsII_fields_consistent :
    GrowsII Bw Bw (0, 1) 0 ∧
      (∀ i, Bw i ⊆ Bw i) ∧
      (∀ i, Bw i ⊆ Bw (i + 1)) ∧
      (∀ i, Bw i ⊆ halfStrip (Bw i) (1, 0)) ∧
      ¬ (∀ i, Bw (i + 1) ⊆ halfStrip (Bw i) (1, 0)) :=
  ⟨growsII_Bw, fun _ => Set.Subset.refl _, mono_Bw, fun _ => subset_halfStrip _ _,
    not_hchain_Bw⟩

end GrowsFieldWitness

/-! ## §6: does `envB` allow item (ii)'s growth at all? (team-lead dispatch, 2026-09-20)

Team-lead's question: can a lattice-convex region with edge-normal set exactly `E(𝒮_φ)`,
satisfying item (i)'s `B_i ∩ ℓ_{B_i} ⊆ ℓ⁽⁻⁾`, contain `[-N,N]² ∩ H(ℓ⁽⁻⁾)` for arbitrarily large
`N`?  Measured here for the concrete, non-degenerate case `E(𝒮_φ) = E(sq1)` — the axis-aligned
unit square (`LatticeEdges.lean:1999`, `E_sq1 : E sq1 = {(1,0),(-1,0),(0,1),(0,-1)}`) — with
`nℓ = (0,1)`, i.e. `ℓ` one of `sq1`'s own four edge directions.

**Measured answer: yes, by an exact match, not merely a bound.**  `LE2.envOf_sq1_box`
(`LatticeEdges.lean:2492`) already proves *every* non-degenerate axis-aligned box is
`E(sq1)`-enveloped, for corners of any size — so a family of boxes growing without bound is
automatically `envB`-compatible at every stage, with no extra work. `growBox i := box (-i,0)
(i,i)` realises this: `envOf_growBox` shows `EnvOf sq1 (growBox i)` for every `i ≥ 1`, and
`growBox_eq_box_inter_halfPlane` shows `growBox i` is *exactly* `[-i,i]² ∩ H((0,1))`, i.e. the
`H(ℓ⁽⁻⁾)`-side of item (ii)'s target region — no slack, the box doesn't merely contain the
target, it equals it.

**Characterisation (why `sq1` was chosen, not an arbitrary shape).**  `envOf_sq1_box`'s proof
goes through `E_box`, which needs the box non-degenerate on *both* axes (`p.1 < q.1 ∧ p.2 <
q.2`); this is what forces `nℓ` to be one of `sq1`'s own four edge directions `(±1,0), (0,±1)`
— for those four directions the growing-box family is a legitimate `E(𝒮_φ)`-enveloped set at
every size, because `sq1`'s edge-normal set already contains exactly the directions needed to
bound a box.  A shape whose `E(𝒮_φ)` is *not* closed under the box's four directions (e.g. only
one pair of parallel edges) would not have `IsLatticeConvexRegion` witnesses shaped like boxes at
all, and the question would need a different family — that case is not measured here.

⚠ **Scope limit, filed rather than guessed (`nivat-definition-audit` step 3, rather than
transcribed against a fresh line-range this session).**  This measures only item (ii)'s
*box-growth* clause against `envB`.  Item (i)'s own clause `B_i ∩ ℓ_{B_i} ⊆ ℓ⁽⁻⁾` uses a notation
`ℓ_{B_i}` — a line *associated to* `B_i` itself, subscripted by `B_i` — that is not obviously the
same object as the fixed `ℓ⁽⁻⁾ = outerLine nℓ cz` (`LatticeEdges.lean:1782`) without a dedicated
transcription pass against `b3_colle2.txt`; guessing its shape here would repeat exactly the
class of error this project's two rewrites trace to, so it is left unstated rather than assumed.
The witness family's own boundary is compatible with the natural reading (`growBox i`'s bottom
edge sits *on* `ℓ = {z.2 = 0}`, not strictly inside `H(ℓ⁽⁻⁾)`), but that compatibility is not
claimed as a proof of item (i). **This does not settle "does item (ii) hold", only "is item
(ii)'s growth clause compatible with `envB`" for this one shape** — the full leaf-A question
still needs `hchain`-style compatibility with a genuine `ChainDataGeom` recursion, untouched
here. -/

/-- The witness family: growing axis-aligned boxes, corner at `(-i,0)` to `(i,i)`, sitting with
their bottom edge on `ℓ = {z.2 = 0}` and everything else inside `H((0,1)) = {z.2 ≥ 0}`. -/
def growBox (i : ℕ) : Set (ℤ × ℤ) :=
  Nivat.LE2.box (-(i : ℤ), 0) ((i : ℤ), (i : ℤ))

/-- **`envB` holds along the whole family.**  Direct instance of `LE2.envOf_sq1_box`: the two
non-degeneracy side conditions are exactly `i ≥ 1`. -/
theorem envOf_growBox (i : ℕ) (hi : 1 ≤ i) :
    Nivat.LE2.EnvOf Nivat.LE2.sq1 (growBox i) := by
  unfold growBox
  exact Nivat.LE2.envOf_sq1_box (show -(i : ℤ) < (i : ℤ) by omega)
    (show (0 : ℤ) < (i : ℤ) by omega)

/-- **Item (ii)'s box clause holds with equality**: the box `[-i,i]²` intersected with the
upper half-plane `H((0,1))` is exactly `growBox i`, for every `i`. -/
theorem growBox_eq_box_inter_halfPlane (i : ℕ) :
    growBox i =
      Nivat.LE2.box (-(i : ℤ), -(i : ℤ)) ((i : ℤ), (i : ℤ)) ∩ Nivat.LE2.halfPlaneGE (0, 1) 0 := by
  ext z
  simp only [growBox, Nivat.LE2.mem_box, Set.mem_inter_iff, Nivat.LE2.halfPlaneGE,
    Set.mem_ofPred_eq, Nivat.LE2.dot_e2]
  omega

/-- **Consistency, stated as the team-lead's exact question, for `E(sq1)` and `nℓ = (0,1)`.**
There is a family `B : ℕ → Set (ℤ × ℤ)` that is `E(sq1)`-enveloped from `i = 1` on, and at every
stage `N` contains (in fact equals, restricted to `H((0,1))`) the box `[-N,N]² ∩ H((0,1))` — so
item (ii)'s growth clause does not contradict `envB` for this shape. -/
theorem exists_envOf_containing_growing_box :
    ∃ B : ℕ → Set (ℤ × ℤ), (∀ i, 1 ≤ i → Nivat.LE2.EnvOf Nivat.LE2.sq1 (B i)) ∧
      ∀ N : ℕ, Nivat.LE2.box (-(N : ℤ), -(N : ℤ)) ((N : ℤ), (N : ℤ)) ∩
          Nivat.LE2.halfPlaneGE (0, 1) 0 ⊆ B N :=
  ⟨growBox, envOf_growBox, fun N => (growBox_eq_box_inter_halfPlane N).symm.subset⟩

/-! ## §7: item (i), transcribed from source, and the joint witness (team-lead dispatch,
2026-09-20, second half)

**The quote, `b3_colle2.txt:472-474` verbatim** (numbers (i)–(iv) inside the proof of Lemma 3.5,
distinct from the lemma's own (i)/(ii) alternative hypotheses quoted in §0):

```
(i)   B_i ⊂ ℤ² is an E(𝒮_φ)-enveloped set with B_i ∩ ℓ_{B_i} ⊂ ℓ^(-),
```

**What `ℓ_{B_i}` is, settled from the source rather than guessed.**  Two lines above Lemma 3.5's
statement (`b3_colle2.txt:420`): *"In the next lemma, `(ℓ_ι)_{B'} = (ℓ_ι)_B` means that the
support lines of `B'` and `B` determined by `ℓ_ι` coincide."*  So `ℓ_{B_i}` is **the support line
of `B_i` determined by `ℓ`** (`ℓ = ℓ_ι` throughout the proof, fixed once at `b3_colle2.txt:464`:
*"we will write `ℓ = ℓ_ι`"*). The proof's own base case pins this down further
(`b3_colle2.txt:464`): the seed `B'` is chosen with *"the support line of `B'` determined by
`ℓ` coincides with `ℓ^(-)`"* — i.e. item (i) for `i = 1, 2, …` is exactly the seed's own defining
property, propagated down the chain. Since `B_i` is `E(𝒮_φ)`-enveloped it has an edge parallel to
`ℓ` (`ℓ` is one of the `2m` directions `ℓ_1,…,ℓ_{2m}` "parallels to the edges of `𝒮_φ`",
Lemma 3.5's own statement, `b3_colle2.txt:424`), so
`B_i ∩ ℓ_{B_i}` is nonempty and item (i) forces the *line containing that edge* to be `ℓ^(-)`
itself, on the side facing away from the growth direction — i.e. the face of `B_i` at the
**outer** normal `-n` (opposite the inner normal `n` of `ℓ`, `LatticeEdges.lean:1759-1761`'s
`ℋ(ℓ) = {⟨n,·⟩ ≥ c}` convention), matching `face` (`LatticeEdges.lean:160`)'s own outer-normal
convention exactly, no reindexing needed.

**Transcription.**  `n` is `ℓ`'s inner normal at level `c` (so `ℓ = {dot n · = c}`,
`H(ℓ) = halfPlaneGE n c`, `ℓ⁽⁻⁾ = outerLine n c`, `LatticeEdges.lean:1757/1782`). -/

/-- **Collé item (i)** (`b3_colle2.txt:472`, proof of Lemma 3.5), transcribed against the
source's own gloss of `ℓ_{B_i}` (`b3_colle2.txt:420`) rather than inferred from our Lean
encoding: the outer face of `B_i` (normal `-n`, the side facing `ℓ⁽⁻⁾`, not the growth side) sits
on the line `ℓ⁽⁻⁾`. `E(𝒮_φ)`-envelopedness itself is `hEnv`, kept as a hypothesis rather than
baked into the predicate so this composes with `Nivat.LE2.EnvOf` at the call site exactly as
`ChainData.envB` does. -/
def ItemI (B : ℕ → Set (ℤ × ℤ)) (n : ℤ × ℤ) (c : ℤ) : Prop :=
  ∀ i : ℕ, Nivat.LE2.face (B i) (-n) ⊆ Nivat.LE2.outerLine n c

/-- **The box conjunct of item (ii), with `ℓ⁽⁻⁾` correctly distinguished from `ℓ`.**  `§6` used
`halfPlaneGE (0,1) 0` directly as "`H(ℓ⁽⁻⁾)`"; done precisely, `ℓ` sits at level `c` and
`ℓ⁽⁻⁾ = outerLine n c` at level `c - 1`, so `H(ℓ⁽⁻⁾) = halfPlaneGE n (c - 1)`
(`Notation 3.3`, same `n`, one level further out). -/
def ItemIIBox (B : ℕ → Set (ℤ × ℤ)) (n : ℤ × ℤ) (c : ℤ) : Prop :=
  ∀ i : ℕ, {z : ℤ × ℤ | |z.1| ≤ (i : ℤ) - 1 ∧ |z.2| ≤ (i : ℤ) - 1} ∩
      Nivat.LE2.halfPlaneGE n (c - 1) ⊆ B i

/-- **`growBox` satisfies item (i) exactly**, at `n = (0,1)`, `c = 1` (so `ℓ = {z.2 = 1}`,
`ℓ⁽⁻⁾ = outerLine (0,1) 1 = {z.2 = 0}`, matching `face_box_bot`'s pinned edge on the nose): the
outer face (normal `(0,-1) = -n`) of `growBox i` is `{-i ≤ z.1 ≤ i, z.2 = 0}` for **every** `i`,
the bottom edge that never moves as the box grows upward and sideways — literally the seed
property from `b3_colle2.txt:464`, propagated. -/
theorem itemI_growBox : ItemI growBox (0, 1) 1 := by
  intro i
  rw [growBox, show (-(0, 1) : ℤ × ℤ) = (0, -1) by decide,
    Nivat.LE2.face_box_bot (by omega : (-(i:ℤ), (0:ℤ)).2 ≤ ((i:ℤ), (i:ℤ)).2)]
  intro z hz
  simp only [Set.mem_ofPred_eq] at hz
  simp only [Nivat.LE2.outerLine, Set.mem_ofPred_eq, Nivat.LE2.dot]
  omega

/-- **`growBox` satisfies the box conjunct of item (ii)**, at the same `n = (0,1)`, `c = 1`: the
box `[-i+1,i-1]²` (Colle's own index shift, no reindexing) intersected with `H(ℓ⁽⁻⁾)` sits inside
`growBox i` — in fact inside `growBox (i-1)` already, since `[-i+1,i-1] ⊆ [-(i-1),i-1]`. -/
theorem itemIIBox_growBox : ItemIIBox growBox (0, 1) 1 := by
  intro i z hz
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Nivat.LE2.halfPlaneGE, Nivat.LE2.dot] at hz
  rw [abs_le, abs_le] at hz
  simp only [growBox, Nivat.LE2.mem_box]
  omega

/-- **Headline: `growBox` witnesses the joint consistency of item (i) and item (ii)'s box
clause with `envB`, simultaneously, exactly matching the source's `ℓ` vs `ℓ⁽⁻⁾` distinction.**
Packages `envOf_growBox`, `itemI_growBox`, `itemIIBox_growBox`. This is strictly more than §6:
§6 conflated `ℓ` and `ℓ⁽⁻⁾`; here they are the two distinct levels `c = 1` / `c - 1 = 0` that
`Notation 3.3` requires, and item (i) — left unstated in §6 as a scope limit — is now proved,
not merely flagged. -/
theorem exists_family_satisfying_itemI_and_itemIIBox :
    ∃ B : ℕ → Set (ℤ × ℤ), (∀ i, 1 ≤ i → Nivat.LE2.EnvOf Nivat.LE2.sq1 (B i)) ∧
      ItemI B (0, 1) 1 ∧ ItemIIBox B (0, 1) 1 :=
  ⟨growBox, envOf_growBox, itemI_growBox, itemIIBox_growBox⟩

/-! ### `ItemI` versus Definition 2.1's nonemptiness clause — stated, not assumed

Collé's actual Definition 2.1 (`b3_colle2.txt:259`, verbatim): *"the support line of `S`
determined by `ℓ`... is defined as the oriented line `ℓ'` parallel to `ℓ` such that `S ⊂ H(ℓ')`
**and `ℓ' ∩ S ≠ ∅`**."*  `ItemI` above encodes only the first conjunct — the containment/pinning
half `face (B i) (-n) ⊆ outerLine n c` — and says nothing about `(face (B i) (-n)).Nonempty`. Read
literally, **`ItemI` is strictly weaker than "the support line of `B_i` coincides with `ℓ⁽⁻⁾`."**

This does not create a gap at any call site that also carries `E(𝒮_φ)`-envelopedness, because the
missing half is a free corollary of `hEnv`, not an extra assumption: an `EnvOf`-enveloped set is
both finite (`Nivat.HbaseFlatSeed.finite_of_envOf_Sphi`, `HbaseFlatSeed.lean:804`) and nonempty
(`Nivat.L1Line0.nonempty_of_enveloped_Sphi`, `L1Line0.lean:639`), and a finite nonempty set has a
nonempty face in **every** direction, not just directions known to lie in `E(𝒮_φ)`
(`Nivat.LE2.face_nonempty`, `LatticeEdges.lean:339`). So no argument that `-n ∈ E(𝒮_φ)` is needed
at all — `face_nonempty` doesn't ask for it. -/

/-- **The nonemptiness half of Definition 2.1, supplied separately from `ItemI`.**  For any
`i` with `B i` `E(𝒮_φ)`-enveloped, `face (B i) (-n)` is automatically nonempty, for *any* `n`
(not just `ℓ`'s inner normal) — so `ItemI hEnv` together with this theorem, applied pointwise,
recovers the full "support line coincides with `ℓ⁽⁻⁾`" statement of Definition 2.1. `ItemI` is
kept as the containment-only predicate (not strengthened to bundle this in) so it stays the exact
shape consumed at call sites that already carry `hEnv` as a separate hypothesis, matching
`ChainData.envB`'s own split. -/
theorem face_nonempty_of_envOf_Sphi {ξ : Config ℤ} (d : Nivat.Colle35.DecompDataZ ξ)
    {B : Set (ℤ × ℤ)} (hEnv : Nivat.LE2.EnvOf (d.Sphi : Set (ℤ × ℤ)) B) (n : ℤ × ℤ) :
    (Nivat.LE2.face B n).Nonempty :=
  Nivat.LE2.face_nonempty (Nivat.HbaseFlatSeed.finite_of_envOf_Sphi d.toDecompData hEnv)
    (Nivat.L1Line0.nonempty_of_enveloped_Sphi d hEnv) n

/-! **On generalising beyond `E(sq1)` (task item 1) — update.**  `E(sq1) = {(±1,0),(0,±1)}` is
shared by *every* non-degenerate axis-aligned box (`E_box`, `LatticeEdges.lean`), not just the
unit square, so the witness above already covers the whole class of axis-aligned `𝒮_φ` shapes,
not one instance — `envOf_sq1_box` takes arbitrary corners. The non-axis-aligned case is **no
longer unmeasured**: `Nivat.Absorb.exists_enveloped_absorbing` (`AbsorbEnv.lean:396`, lane
Aenvfix, zero consumers) already gives, for *arbitrary* lattice-convex `U`, an `E(U)`-enveloped
`B₁ ⊇ B ∪ F` (any prescribed finite `F` inside `B`'s own `n`-support half plane) **with the exact
same `n`-support level**, `suppVal B₁ n = suppVal B n` — via `Nivat.Absorb.E_dil` (`:268`),
dilating about the midpoint of two points already on the pinned edge (not about the origin), so
the pinning line does not move. This is a joint witness for item (i) *and* item (ii)'s box
clause for general `𝒮_φ`; see the iteration built below. -/

/-! ### Wiring `exists_enveloped_absorbing` against `ItemI`/`ItemIIBox` — the two gates

Team-lead's two checks, done before any chain is built (2026-09-20).

**Gate 1 — is half-strip confinement forced by the chain's own fields, making the escape
illusory?**  No. Enumerated every field of `ChainData` (`Lemma35.lean:695`, `envB envA subBA
subAB subStrip agreeA AhatEq AhatMono maximalHat`), `ChainDataWithShell` (`ChainShell.lean:49`,
adds `shellInf_eq ahat_nonempty ahat_halfPlane`), and `ChainDataGeomParts`
(`ChainPartsFeed.lean:277`, adds the shell/face/region fields `hsweep hfin hhp hswept
ahat_nonempty shellSubStrip escape shellEnv fillCover … bottom rec_p dot_nJ_p … nfp_L`). The
only field relating `A i` to `B (i+1)` at all is `subAB : ∀ i, A i ⊆ B (i + 1)` — a *lower*
bound, no upper bound. `subStrip : ∀ i, A i ⊆ halfStrip (B i) vl` confines `A i` to `B i`'s own
strip (same index), derived from `maxA`'s maximality (`subStrip_of_max`, `ChainMax.lean:96`) —
it says nothing about `B (i+1)`. `shellSubStrip`/`hhp`/`hswept` confine the *shell* objects
(`hatOf A kk vl i`, tied to the transverse pair `vJ1, nJ`) — a different geometric direction
from `vl`, and again indexed at `i`, not `i+1`. **`hchain : B (i+1) ⊆ halfStrip (A i) vl`**
(`ItemII.lean:399`, the hypothesis `not_itemII_of_chain` needs) **is a property specific to
`ChainRecursion`'s definitional choice `B (i+1) := A i`** (`ChainData.chain_of_ChainRecursion`,
`:420`: "is exactly the `hchain`"), not a consequence of any `ChainDataGeom` field. A
hand-built `B (i+1)` from `exists_enveloped_absorbing` — which only has to satisfy `subAB`
(`A i ⊆ B (i+1)`, guaranteed since `hF`'s absorbed set can be taken to include `A i`) and
`envB (i+1)` (guaranteed: `EnvOf U B₁`) — is free to violate `hchain` without violating any
chain obligation. The escape is real, not illusory.

**Gate 2 — does `hF` fail once the box outgrows the fixed pinning level?**  No: `hF`'s bound and
item (ii)'s box are the *same* half plane, exactly, not merely compatible. Checked below as a
compiled theorem rather than assumed. -/

/-- **`hF` holds automatically, for every `i`, at the exact fixed level `ItemI` pins.**  With
`n_absorb := -n` (`AbsorbEnv`'s outer-normal convention matches `ItemI`'s `-n` pinned face) and
`B i` finite nonempty, `ItemI`'s own outer face gives `suppVal (B i) (-n) = -(c - 1)` (via
`suppVal_eq` on any point of that face, which `outerLine` pins to level `c - 1` on `n`). Item
(ii)'s box already intersects with `halfPlaneGE n (c - 1)` — i.e. `dot n f ≥ c - 1` for every
`f ∈ F` — which is *exactly* `dot (-n) f ≤ -(c-1) = suppVal (B i) (-n)`, `exists_enveloped_absorbing`'s
`hF`. No growing-past-the-level failure mode: the box's *size* grows with `i`, but the half
plane it is intersected with never moves, because `ItemI`'s pinning level `c` is fixed once,
not re-chosen per `i`. -/
theorem hF_of_itemI {B : ℕ → Set (ℤ × ℤ)} {n : ℤ × ℤ} {c : ℤ} (i : ℕ)
    (hfin : (B i).Finite) (hne : (B i).Nonempty) (hI : ItemI B n c) :
    ∀ f ∈ {z : ℤ × ℤ | |z.1| ≤ (i : ℤ) - 1 ∧ |z.2| ≤ (i : ℤ) - 1} ∩
        Nivat.LE2.halfPlaneGE n (c - 1),
      Nivat.LE2.dot (-n) f ≤ Nivat.LE2.suppVal (B i) (-n) := by
  intro f hf
  obtain ⟨t, ht⟩ := Nivat.LE2.face_nonempty hfin hne (-n)
  have ht' : t ∈ Nivat.LE2.outerLine n c := hI i ht
  rw [Nivat.LE2.suppVal_eq ht, Nivat.LE2.dot_neg_left, Nivat.LE2.dot_neg_left]
  simp only [Nivat.LE2.outerLine, Set.mem_ofPred_eq] at ht'
  simp only [Set.mem_inter_iff, Nivat.LE2.halfPlaneGE, Set.mem_ofPred_eq] at hf
  omega

/-! ## §8: Step 2 — the general chain, iterating `exists_enveloped_absorbing`

Team-lead's Step 2: build the ℕ-indexed chain by iterating `exists_enveloped_absorbing` with
`F_i` growing, landed against `ItemI`/`ItemIIBox`. Unlike §6/§7's `growBox` witness (specific to
`E(sq1)`, axis-aligned), this is generic in `U`: any lattice-convex `U` with `E U` finite and (for
the finiteness/positive-area side conditions `exists_enveloped_absorbing` and its friends need)
two independent antipodal edge-normal pairs. -/

/-- The `Finset` box `[-k,k]²`, used to build item (ii)'s target region as a `Finset` (needed
because `exists_enveloped_absorbing`'s `F` is a `Finset`, not a `Set`). -/
noncomputable def boxFinset (k : ℤ) : Finset (ℤ × ℤ) := (Finset.Icc (-k) k) ×ˢ (Finset.Icc (-k) k)

theorem mem_boxFinset {k : ℤ} {z : ℤ × ℤ} : z ∈ boxFinset k ↔ |z.1| ≤ k ∧ |z.2| ≤ k := by
  simp only [boxFinset, Finset.mem_product, Finset.mem_Icc, abs_le]

/-- The `Finset` version of item (ii)'s target region at stage `i`, pinned direction `n`, level
`c`: `[-i+1,i-1]² ∩ H(ℓ⁽⁻⁾)`, `Ffin`'s coercion is exactly `ItemIIBox`'s defining set
(`coe_Ffin` below). -/
noncomputable def Ffin (i : ℕ) (n : ℤ × ℤ) (c : ℤ) : Finset (ℤ × ℤ) :=
  (boxFinset ((i : ℤ) - 1)).filter (fun z => c - 1 ≤ Nivat.LE2.dot n z)

theorem coe_Ffin (i : ℕ) (n : ℤ × ℤ) (c : ℤ) :
    (↑(Ffin i n c) : Set (ℤ × ℤ)) =
      {z : ℤ × ℤ | |z.1| ≤ (i : ℤ) - 1 ∧ |z.2| ≤ (i : ℤ) - 1} ∩
        Nivat.LE2.halfPlaneGE n (c - 1) := by
  ext z
  simp only [Ffin, Finset.coe_filter, mem_boxFinset, Set.mem_inter_iff, Set.mem_ofPred_eq,
    Nivat.LE2.halfPlaneGE]

/-- Single-index form of `hF_of_itemI`'s bound, stated directly against `Ffin` rather than
`ItemI`'s whole-family predicate — the loop invariant `exists_absorbing_step` below needs at one
index at a time. Same proof as `hF_of_itemI`, factored out. -/
theorem hF_of_pin_Ffin {B : Set (ℤ × ℤ)} {n : ℤ × ℤ} {c : ℤ} (i : ℕ)
    (hfin : B.Finite) (hne : B.Nonempty)
    (hpin : Nivat.LE2.face B (-n) ⊆ Nivat.LE2.outerLine n c) :
    ∀ f ∈ Ffin i n c, Nivat.LE2.dot (-n) f ≤ Nivat.LE2.suppVal B (-n) := by
  intro f hf
  simp only [Ffin, Finset.mem_filter, mem_boxFinset] at hf
  obtain ⟨t, ht⟩ := Nivat.LE2.face_nonempty hfin hne (-n)
  have ht' : t ∈ Nivat.LE2.outerLine n c := hpin ht
  rw [Nivat.LE2.suppVal_eq ht, Nivat.LE2.dot_neg_left, Nivat.LE2.dot_neg_left]
  simp only [Nivat.LE2.outerLine, Set.mem_ofPred_eq] at ht'
  omega

/-- `hF_of_itemI` refactored to call the single-index form, confirming they agree. -/
theorem hF_of_itemI' {B : ℕ → Set (ℤ × ℤ)} {n : ℤ × ℤ} {c : ℤ} (i : ℕ)
    (hfin : (B i).Finite) (hne : (B i).Nonempty) (hI : ItemI B n c) :
    ∀ f ∈ Ffin i n c, Nivat.LE2.dot (-n) f ≤ Nivat.LE2.suppVal (B i) (-n) :=
  hF_of_pin_Ffin i hfin hne (hI i)

/-- **The absorbing enlargement transfers `ItemI`'s pin.** If `face B (-n) ⊆ outerLine n c` and
the enlargement `B₁` keeps `suppVal (-n)` fixed (`exists_enveloped_absorbing`'s own conclusion),
the pin transfers to `B₁` unchanged. -/
theorem itemI_step_of_suppVal_eq {B B1 : Set (ℤ × ℤ)} {n : ℤ × ℤ} {c : ℤ}
    (hBfin : B.Finite) (hBne : B.Nonempty)
    (hpin : Nivat.LE2.face B (-n) ⊆ Nivat.LE2.outerLine n c)
    (hsupp : Nivat.LE2.suppVal B1 (-n) = Nivat.LE2.suppVal B (-n)) :
    Nivat.LE2.face B1 (-n) ⊆ Nivat.LE2.outerLine n c := by
  intro z hz
  obtain ⟨t, ht⟩ := Nivat.LE2.face_nonempty hBfin hBne (-n)
  have htc : t ∈ Nivat.LE2.outerLine n c := hpin ht
  have e1 : Nivat.LE2.dot (-n) z = Nivat.LE2.suppVal B1 (-n) := (Nivat.LE2.suppVal_eq hz).symm
  have e2 : Nivat.LE2.dot (-n) t = Nivat.LE2.suppVal B (-n) := (Nivat.LE2.suppVal_eq ht).symm
  have e3 : Nivat.LE2.dot (-n) z = Nivat.LE2.dot (-n) t := by rw [e1, hsupp, e2]
  rw [Nivat.LE2.dot_neg_left, Nivat.LE2.dot_neg_left] at e3
  simp only [Nivat.LE2.outerLine, Set.mem_ofPred_eq] at htc ⊢
  omega

/-- **The fixed data of the iteration**: the enveloping shape `U`, the pinned direction `n` (with
`m` a transverse direction needed only for the finiteness/positive-area side conditions), and the
pinning level `c`. Bundled into a structure so the recursive construction below does not have to
thread eight separate hypotheses through every step. -/
structure StepEnv where
  U : Set (ℤ × ℤ)
  n : ℤ × ℤ
  m : ℤ × ℤ
  c : ℤ
  hEU : (Nivat.LE2.E U).Finite
  hdet : det n m ≠ 0
  hn : n ∈ Nivat.LE2.E U
  hn' : -n ∈ Nivat.LE2.E U
  hm : m ∈ Nivat.LE2.E U
  hm' : -m ∈ Nivat.LE2.E U
  hne_nn' : n ≠ -n
  hne_nm : n ≠ m
  hne_n'm : (-n : ℤ × ℤ) ≠ m

/-- The loop invariant: `B` is `E U`-enveloped, finite, nonempty, and pinned at `-n` on
`outerLine n c` — exactly `ItemI`'s single-index content plus the side conditions
`exists_enveloped_absorbing` needs. -/
def StepInv (E : StepEnv) (B : Set (ℤ × ℤ)) : Prop :=
  B.Finite ∧ B.Nonempty ∧ Nivat.LE2.EnvOf E.U B ∧
    Nivat.LE2.face B (-E.n) ⊆ Nivat.LE2.outerLine E.n E.c

/-- **The single step**: given a stage `B` satisfying the invariant, absorb `Ffin i E.n E.c` into
an enlargement `B₁` that still satisfies the invariant. -/
theorem exists_absorbing_step (E : StepEnv) {B : Set (ℤ × ℤ)} (hB : StepInv E B) (i : ℕ) :
    ∃ B1, StepInv E B1 ∧ B ⊆ B1 ∧ (↑(Ffin i E.n E.c) : Set (ℤ × ℤ)) ⊆ B1 := by
  obtain ⟨hBfin, hBne, hEnv, hpin⟩ := hB
  have hposB : Nivat.LE2.PosArea B :=
    Nivat.LE2.posArea_of_envOf E.hn E.hn' E.hm E.hne_nn' E.hne_nm E.hne_n'm E.hEU hEnv
  have hFbound : ∀ f ∈ Ffin i E.n E.c, Nivat.LE2.dot (-E.n) f ≤ Nivat.LE2.suppVal B (-E.n) :=
    hF_of_pin_Ffin i hBfin hBne hpin
  obtain ⟨B1, henv, hsub, hFsub, hsupp⟩ :=
    Nivat.Absorb.exists_enveloped_absorbing E.hEU hEnv hBfin hBne hposB E.hn'
      (Ffin i E.n E.c) hFbound
  refine ⟨B1, ⟨?_, ?_, henv, ?_⟩, hsub, hFsub⟩
  · exact Nivat.MaxEnv.finite_of_envOf E.hEU E.hdet E.hn E.hn' E.hm E.hm' henv
  · obtain ⟨x, hx⟩ := hBne; exact ⟨x, hsub hx⟩
  · exact itemI_step_of_suppVal_eq hBfin hBne hpin hsupp

/-- **The chain itself**, built by iterating `exists_absorbing_step` from a seed `B0`. -/
noncomputable def familySig (E : StepEnv) {B0 : Set (ℤ × ℤ)} (hB0 : StepInv E B0) :
    ℕ → {B : Set (ℤ × ℤ) // StepInv E B}
  | 0 => ⟨B0, hB0⟩
  | (i + 1) =>
      ⟨(exists_absorbing_step E (familySig E hB0 i).2 (i + 1)).choose,
        (exists_absorbing_step E (familySig E hB0 i).2 (i + 1)).choose_spec.1⟩

/-- The underlying `ℕ`-indexed family of sets. -/
noncomputable def family (E : StepEnv) {B0 : Set (ℤ × ℤ)} (hB0 : StepInv E B0) (i : ℕ) :
    Set (ℤ × ℤ) := (familySig E hB0 i).1

theorem stepInv_family (E : StepEnv) {B0 : Set (ℤ × ℤ)} (hB0 : StepInv E B0) (i : ℕ) :
    StepInv E (family E hB0 i) := (familySig E hB0 i).2

theorem subset_family_succ (E : StepEnv) {B0 : Set (ℤ × ℤ)} (hB0 : StepInv E B0) (i : ℕ) :
    family E hB0 i ⊆ family E hB0 (i + 1) :=
  (exists_absorbing_step E (familySig E hB0 i).2 (i + 1)).choose_spec.2.1

theorem Ffin_subset_family_succ (E : StepEnv) {B0 : Set (ℤ × ℤ)} (hB0 : StepInv E B0) (i : ℕ) :
    (↑(Ffin (i + 1) E.n E.c) : Set (ℤ × ℤ)) ⊆ family E hB0 (i + 1) :=
  (exists_absorbing_step E (familySig E hB0 i).2 (i + 1)).choose_spec.2.2

/-- **Headline: the chain satisfies `ItemI` at every index.** -/
theorem itemI_family (E : StepEnv) {B0 : Set (ℤ × ℤ)} (hB0 : StepInv E B0) :
    ItemI (family E hB0) E.n E.c :=
  fun i => (stepInv_family E hB0 i).2.2.2

/-- **Headline: the chain satisfies item (ii)'s box clause at every index `≥ 1`; index `0`'s box
is empty** (`|z.1| ≤ -1` is unsatisfiable), so the statement holds vacuously there too — matching
§1's index-convention note that `i = 0` is harmless truncation, not a real case. -/
theorem itemIIBox_family (E : StepEnv) {B0 : Set (ℤ × ℤ)} (hB0 : StepInv E B0) :
    ItemIIBox (family E hB0) E.n E.c := by
  intro i
  cases i with
  | zero =>
    intro z hz
    exfalso
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Nat.cast_zero] at hz
    have := abs_nonneg z.1
    omega
  | succ i =>
    rw [← coe_Ffin]
    exact Ffin_subset_family_succ E hB0 i

/-- **Headline: the chain is `E U`-enveloped at every index.** -/
theorem envOf_family (E : StepEnv) {B0 : Set (ℤ × ℤ)} (hB0 : StepInv E B0) (i : ℕ) :
    Nivat.LE2.EnvOf E.U (family E hB0 i) := (stepInv_family E hB0 i).2.2.1

/-- **The support-value pin survives the whole iteration**: `suppVal (B i) (-n)` stays constant
across all stages, equal to the seed's support value at `-n`. This is why `hF_of_pin_Ffin` composes:
at every step `i`, the box `Ffin i n c` satisfies the bound needed for `exists_enveloped_absorbing`
to absorb it without violating the pin. -/
theorem suppVal_family_eq (E : StepEnv) {B0 : Set (ℤ × ℤ)} (hB0 : StepInv E B0) (i : ℕ) :
    Nivat.LE2.suppVal (family E hB0 i) (-E.n) = Nivat.LE2.suppVal B0 (-E.n) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have hstep := (exists_absorbing_step E (familySig E hB0 i).2 (i + 1)).choose_spec
    obtain ⟨⟨_, _, _, hpin_succ⟩, _, _⟩ := hstep
    have hBfin := (stepInv_family E hB0 i).1
    have hBne := (stepInv_family E hB0 i).2.1
    have hpin := (stepInv_family E hB0 i).2.2.2
    obtain ⟨t, ht⟩ := Nivat.LE2.face_nonempty hBfin hBne (-E.n)
    have htc : t ∈ Nivat.LE2.outerLine E.n E.c := hpin ht
    have hsucc_fin : (family E hB0 (i + 1)).Finite := (stepInv_family E hB0 (i + 1)).1
    have hsucc_ne : (family E hB0 (i + 1)).Nonempty := (stepInv_family E hB0 (i + 1)).2.1
    obtain ⟨s, hs⟩ := Nivat.LE2.face_nonempty hsucc_fin hsucc_ne (-E.n)
    have hsc : s ∈ Nivat.LE2.outerLine E.n E.c := hpin_succ hs
    have et : Nivat.LE2.dot (-E.n) t = Nivat.LE2.suppVal B0 (-E.n) := by
      rw [← Nivat.LE2.suppVal_eq ht]; exact ih
    rw [Nivat.LE2.suppVal_eq hs]
    rw [Nivat.LE2.dot_neg_left] at et ⊢
    simp only [Nivat.LE2.outerLine, Set.mem_ofPred_eq] at htc hsc
    omega

/-- **The construction, packaged**: from any seed satisfying the invariant, item (i) and item
(ii)'s box clause hold together, at every stage, for the whole `ℕ`-indexed chain — the general
(not merely axis-aligned) case Step 2 asked for. -/
theorem exists_chain_satisfying_itemI_and_itemIIBox (E : StepEnv) {B0 : Set (ℤ × ℤ)}
    (hB0 : StepInv E B0) :
    ∃ B : ℕ → Set (ℤ × ℤ), (∀ i, Nivat.LE2.EnvOf E.U (B i)) ∧
      ItemI B E.n E.c ∧ ItemIIBox B E.n E.c :=
  ⟨family E hB0, envOf_family E hB0, itemI_family E hB0, itemIIBox_family E hB0⟩

end Nivat.Colle35

#print axioms Nivat.Colle35.ItemI
#print axioms Nivat.Colle35.ItemIIBox
#print axioms Nivat.Colle35.itemI_growBox
#print axioms Nivat.Colle35.itemIIBox_growBox
#print axioms Nivat.Colle35.exists_family_satisfying_itemI_and_itemIIBox
#print axioms Nivat.Colle35.face_nonempty_of_envOf_Sphi

#print axioms Nivat.Colle35.itemII_of_growsII
#print axioms Nivat.Colle35.subAB_of_growsII
#print axioms Nivat.Colle35.not_growsII_of_chain
#print axioms Nivat.Colle35.GrowsFieldWitness.mono_Bw
#print axioms Nivat.Colle35.GrowsFieldWitness.growsII_Bw
#print axioms Nivat.Colle35.GrowsFieldWitness.not_hchain_Bw
#print axioms Nivat.Colle35.GrowsFieldWitness.growsII_fields_consistent
#print axioms Nivat.Colle35.envOf_growBox
#print axioms Nivat.Colle35.growBox_eq_box_inter_halfPlane
#print axioms Nivat.Colle35.exists_envOf_containing_growing_box
#print axioms Nivat.Colle35.hF_of_itemI
#print axioms Nivat.Colle35.mem_boxFinset
#print axioms Nivat.Colle35.coe_Ffin
#print axioms Nivat.Colle35.hF_of_pin_Ffin
#print axioms Nivat.Colle35.hF_of_itemI'
#print axioms Nivat.Colle35.itemI_step_of_suppVal_eq
#print axioms Nivat.Colle35.exists_absorbing_step
#print axioms Nivat.Colle35.stepInv_family
#print axioms Nivat.Colle35.subset_family_succ
#print axioms Nivat.Colle35.Ffin_subset_family_succ
#print axioms Nivat.Colle35.itemI_family
#print axioms Nivat.Colle35.itemIIBox_family
#print axioms Nivat.Colle35.envOf_family
#print axioms Nivat.Colle35.suppVal_family_eq
#print axioms Nivat.Colle35.exists_chain_satisfying_itemI_and_itemIIBox
