/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.LatticeEdges

/-!
# `WDescent` / `UpperCutW`: the `w`-sweep obligation of `Â_i^{(ε)}` and its cut form

Lane `lane-leafa-gen`, 2026-09-24 (round 167).  Landed from
`tmp/wip/lane-leafa-gen-fillcover-depth.lean` §23 / §27 / §28.

## What this file is for

`b3_colle2.txt:518` defines the `ε`-shell of a layer by sweeping backwards along the chain
successor direction,

  `Â_i^{(ε)} := {g - t·v⃗_{ℓ_{J+1}} ∈ Â_∞^{(ε)} : g ∈ Â_i, t ∈ ℤ_+}`,

and then uses `Â_i^{(ε)}` as if the swept points were still governed by layer `i`.  Making that
step honest is one obligation, stated here as `WDescent` (§1).  §2 gives a *sufficient*
condition for it in terms of an upper-cut representation of the tower (`UpperCut` /
`UpperCutW`), and §3 shows that the sign condition inside `UpperCutW` is not an extra
quantifier we invented: it is forced back out by `WDescent` itself.

## ⛔ FROZEN, no consumer (team-lead ruling, round 172)

All three `Prop`s below are **our own** intermediate shapes; none transcribes a sentence of
`b3_colle2.txt`.  The file stays in the main repo (0 sorry, axioms clean) but is **frozen**:
§5 and beyond are not to be opened, and nothing here has a main-repo consumer
(`grep -rn "WDescent\|UpperCutW\|UpperCutG" Nivat/` outside this file: rc=1, zero hits).
In particular `fillCover` (`ChainExhaustInter.lean`) does **not** depend on `WDescent`.

## Source correspondence (rewritten 2026-09-24 — the previous version was wrong)

The earlier text here claimed "`WDescent` is the only `Prop` here with a direct source
counterpart".  **That is false and is retracted.**  The warning that should have travelled with
the landing — `tmp/wip/lane-leafa-gen-fillcover-depth.lean:1887`, "⚠ 原文没有主张 `WDescent`" —
was lost in the move.  Quantifier-by-quantifier:

* Quantifiers 1–3 of `WDescent` (`∀ i`, `∀ g ∈ Â_i`, `∀ t : ℤ_+`) do match `:518`.
* Quantifier 4 matches the trim in the same display **but with the wrong set** — see the table
  on `WDescent` below.
* Quantifier 5 has no counterpart at all; `:518`'s only floor is the `cJ - ε` carried by
  `Â_∞^{(ε)}` (`MaximalEnveloped.lean:564`), not `cJ`.
* The **conclusion** `g + t•w ∈ Â_i` has no counterpart in `:512-530`.  `:520` only says
  `Â_i^{(ε)}` is `E(𝒮_φ)`-enveloped and sandwiched; `:530` needs `Â_i^{(ε)} ⊋ Â_i`.

⚠ **Do not read this as "the source's step is false".**  `:518` is a `:=`; the `∈ Â_∞^{(ε)}` in
it is a *filter on the element*, not the antecedent of an implication, so it asserts only
`Â_i^{(ε)} ⊆ Â_∞^{(ε)}`.  Turning it into an implication would give `Â_i^{(ε)} ⊆ Â_i`, i.e. "the
construction adds nothing" — and `:530` ("contradicts the maximality of `Â_i`", with `:492` for
the maximality and `:520` for enveloped-ness) **requires that to be false**.  A kernel receipt
for the strict inclusion the source needs is `lane-tower-hlev`'s `shellProper_of_escape`
(`tmp/wip/lane-tower-hlev-wsep.lean`, ex-`not_wDescentShell_of_escape`); the main repo already
carries the same fact as `Nivat.ChainAsm.shellProperInter_of` (`ChainAssembleInter.lean:119`),
which feeds the `shellProper` field at `ChainAssembleInter.lean:274`.  Reading a `:=` as a
proposition is the root cause recorded in `NOTATION.md`; it is the same failure mode as the
point `a` that never existed in `:806-870` (hole 3).

`UpperCut` / `UpperCutW` are **our** finitary reading of `b3_colle2.txt:506` ("`Â_∞` is an
`(ℓ, ℓ_J)`-region", i.e. its own walls do not move with `i`, the tower only grows along the two
semi-infinite edges).  They are tools for producing `WDescent`, never obligations in their own
right.

`ε` is typed `0 < ε` throughout, per `:512`; the source is itself inconsistent (`:512` `ℤ_+`,
`:516`/`:520` `ℕ`) and we align with the claim being proved, not with the mid-construction
notation (team-lead ruling, round 172).  Not a debt.

## What `WDescent` does say

It is the collar-restricted form of "the construction adds nothing": by `hhp` + `hswept`,
`shell ∩ {cJ ≤ ⟪n_J,·⟫} = ⋃ⱼÂⱼ` exactly, so all of the growth `:530` needs happens strictly
**below** the `ℓ_J` floor, inside the `ε`-collar `cJ - ε ≤ ⟪n_J,·⟫ < cJ`.  That is consistent
with `:530`, not in tension with it.  Receipts for the collar statement:
`lane-tower-hlev`'s `escape_below_floor` (`tmp/wip/lane-tower-hlev-wsep.lean:402`) and
`escape_in_band` (`:424`).

Any future consumer must check it is not smuggling in `Â_i^{(ε)} = Â_i`; that would kill `:530`.

Two deliberate design points, both recorded because they were paid for:

* `UpperCutW` quantifies `cut` **existentially**.  A fixed-`cut` version is strictly stronger
  and false in general: adding a redundant half-plane to `cut` preserves `UpperCut` while
  breaking the sign condition (kernel witness pair in
  `tmp/wip/lane-leafa-gen-fillcover-depth.lean` §27, `hex_upperCut_redundant` /
  `hex_upperCut_redundant_breaks_hw`).  The existential is what makes the sign condition a
  constraint on the *choice* of representation rather than on the tower.
* `cut i` carries **no** finiteness constraint, by ruling (team-lead, round 167).  Dropping it
  is what lets a producer take "all `w`-nonpositive valid inequalities" as its cut.

## Naming caution (`NOTATION.md`, one name two objects)

The normals in `cut i` are face normals of the tower layer `Â_i`.  They are **not** the normals
in `E ↑𝒮_φ` that the envelope obligations range over, and they are not `E (⋃ⱼ Âⱼ)` either.  On a
particular tower the three sets can share labels by accident; a label carries no information
across towers.  The only meaningful statement is the sign of a given normal against *that
tower's own* `w`.

Note also that `nJ` is an **inner** normal (`hhp : hatOf A kk vl i ⊆ halfPlaneGE nJ cJ`,
`ChainExhaustInter.lean`, and `halfPlaneGE n c = {z | c ≤ dot n z}`), whereas the normals in
`cut i` are **outer** (the cut reads `dot mc.1 z ≤ mc.2`).  Every inner product against `w` in
this file is taken against an outer normal; the one inner-normal inequality, `cJ ≤ dot nJ ·`,
never meets `w`.
-/

namespace Nivat.WCut

open Nivat Nivat.LE2

variable {Ahat : ℕ → Set (ℤ × ℤ)} {nJ w : ℤ × ℤ} {cJ : ℤ}

private theorem dot_add_zsmul (m z d : ℤ × ℤ) (t : ℤ) :
    dot m (z + t • d) = dot m z + t * dot m d := by
  obtain ⟨d1, d2⟩ := d
  simp only [dot, Prod.fst_add, Prod.snd_add, Prod.smul_mk, smul_eq_mul]
  ring

/-! ## §1.  The obligation itself -/

/-- **`w`-descent closure**: a point of `Â_i` pushed out along `w` is still in the *same* layer
`Â_i`, provided it (i) is still in `Â_∞` and (ii) has not fallen below the `n_J`-floor `cJ`.

⛔ **This `Prop` is ours, not Collé's** — see the file header.  Quantifiers, against
`b3_colle2.txt:518`
(`Â_i^{(ε)} := {g - t·v⃗_{ℓ_{J+1}} ∈ Â_∞^{(ε)} : g ∈ Â_i, t ∈ ℤ_+}`):

| here | source | match? |
|---|---|---|
| `∀ i` | the tower index | ✅ |
| `∀ g ∈ Ahat i` | `g ∈ Â_i` | ✅ |
| `∀ t : ℕ` | `t ∈ ℤ_+` | ✅ |
| `g + t•w ∈ ⋃ j, Ahat j` | the trim `∈ Â_∞^{(ε)}` in the same display | ⚠ **wrong set**: `⋃ⱼÂⱼ` is `Â_∞`, the source's is the shell `Â_∞^{(ε)}`.  The two differ by the collar `cJ - ε ≤ ⟪n_J,·⟫ < cJ` (`:440`) |
| `cJ ≤ dot nJ (g + t•w)` | **none** | ❌ `:518`'s only floor is `cJ - ε`, carried by `Â_∞^{(ε)}` (`MaximalEnveloped.lean:564`).  `cJ` is ours |
| conclusion `g + t•w ∈ Ahat i` | **none** in `:512-530` | ❌ see the file header |

The floor guard (row 5) is moreover *vacuous on the chain*: `hhp` (`ChainExhaustInter.lean`)
puts all of `⋃ⱼÂⱼ` above `cJ`, so row 4 already implies it.  Kernel receipt:
`lane-tower-hlev`'s `wDescent_iff_unguarded_of_hhp` (`tmp/wip/lane-tower-hlev-wsep.lean:936`).
It was not added to make a proof go through — `wDescent_of_upperCut` discards it as `_` — it was
added by symmetry with the consumers, and it buys nothing.

There is no sixth quantifier — **and that sentence compares against our own §19/§20 `hwall`
family**, not against the source.  Those earlier shapes additionally quantified over wall
normals `n ∈ E ↑𝒮_φ` and over `ε`; they were killed by `hex_hwall_false`
(`tmp/wip/lane-leafa-gen-fillcover-depth.lean` §22) and the present shape was pinned by
`wDescent_iff` (same file, `:1931`).  In particular this `Prop` mentions neither `ε` nor the
shape normals nor `v_{J1}`; the `ε`-dependent consumers are obtained from it, not the other way
round. -/
def WDescent (Ahat : ℕ → Set (ℤ × ℤ)) (nJ w : ℤ × ℤ) (cJ : ℤ) : Prop :=
  ∀ i : ℕ, ∀ g ∈ Ahat i, ∀ t : ℕ, g + (t : ℤ) • w ∈ (⋃ j, Ahat j) →
    cJ ≤ dot nJ (g + (t : ℤ) • w) → g + (t : ℤ) • w ∈ Ahat i

/-! ## §2.  The upper-cut representation, and why it suffices -/

/-- **Upper-cut representation**: layer `i` is `Â_∞` intersected with a family of upper
half-planes.  An element of `cut i` is a (normal, bound) pair read as `dot mc.1 z ≤ mc.2`, so the
normals here are **outer**.

This `Prop` has no source counterpart of its own; it is our finitary reading of
`b3_colle2.txt:506` ("`Â_∞` is an `(ℓ, ℓ_J)`-region", hence its own walls are `i`-independent and
only the walls transverse to the two semi-infinite edges move with `i`).  Recorded as our added
obligation per 硬规矩 5; `wDescent_of_upperCut` is what makes it legitimate to assume. -/
def UpperCut (Ahat : ℕ → Set (ℤ × ℤ)) (cut : ℕ → Set ((ℤ × ℤ) × ℤ)) : Prop :=
  ∀ i : ℕ, Ahat i = {z | z ∈ (⋃ j, Ahat j) ∧ ∀ mc ∈ cut i, dot mc.1 z ≤ mc.2}

/-- **The packaged sufficient condition**: *some* upper-cut representation exists whose every
(outer) normal is non-increasing along `w`.

The two clauses and their provenance:

* `UpperCut Ahat cut` — our reading of `b3_colle2.txt:506`, see `UpperCut`;
* `∀ i, ∀ mc ∈ cut i, dot mc.1 w ≤ 0` — the sign clause.  Its source is `b3_colle2.txt:518`
  (`w = -v⃗_{ℓ_{J+1}}`, the chain **successor** direction) together with the chain order, which
  places the moving walls clockwise of `ν_{J+1}`; the boundary case `⟪ν_{J+1}, w⟫ = 0` is an
  identity (`⟪ν, -dir ν⟫ = 0`).  This file does **not** prove the chain-order half — that is the
  producer's job — but §3 shows the clause is forced, so it is not a strengthening.

The existential over `cut` is deliberate and is the whole content of the packaging: see the file
header. -/
def UpperCutW (Ahat : ℕ → Set (ℤ × ℤ)) (w : ℤ × ℤ) : Prop :=
  ∃ cut : ℕ → Set ((ℤ × ℤ) × ℤ),
    UpperCut Ahat cut ∧ ∀ i : ℕ, ∀ mc ∈ cut i, dot mc.1 w ≤ 0

/-- Upper-cut representation + every cut normal non-increasing along `w` ⟹ `WDescent`.

Note the floor hypothesis `cJ ≤ dot nJ ·` of `WDescent` is *not used* here (it appears as `_` in
the proof), so this route proves slightly more than `WDescent` asks for. -/
theorem wDescent_of_upperCut {cut : ℕ → Set ((ℤ × ℤ) × ℤ)}
    (hcut : UpperCut Ahat cut) (hw : ∀ i : ℕ, ∀ mc ∈ cut i, dot mc.1 w ≤ 0) :
    WDescent Ahat nJ w cJ := by
  intro i g hg t hmem _
  have hgi := (Set.ext_iff.mp (hcut i) g).mp hg
  refine (Set.ext_iff.mp (hcut i) (g + (t : ℤ) • w)).mpr ⟨hmem, fun mc hmc => ?_⟩
  rw [dot_add_zsmul]
  have h1 : (t : ℤ) * dot mc.1 w ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg t) (hw i mc hmc)
  have h2 := hgi.2 mc hmc
  omega

/-- The packaged form of `wDescent_of_upperCut`. -/
theorem wDescent_of_upperCutW (h : UpperCutW Ahat w) : WDescent Ahat nJ w cJ := by
  obtain ⟨cut, hcut, hw⟩ := h
  exact wDescent_of_upperCut hcut hw

/-! ### §2.1  Pruning: redundant cuts, in particular the walls of `Â_∞` itself -/

/-- **An upper-cut family may be pruned**: if every dropped entry already holds on all of `Â_∞`,
the smaller family still represents the tower. -/
theorem upperCut_prune {cut keep : ℕ → Set ((ℤ × ℤ) × ℤ)}
    (hcut : UpperCut Ahat cut) (hsub : ∀ i : ℕ, keep i ⊆ cut i)
    (hbdd : ∀ i : ℕ, ∀ mc ∈ cut i, mc ∉ keep i →
      ∀ z ∈ (⋃ j, Ahat j), dot mc.1 z ≤ mc.2) :
    UpperCut Ahat keep := by
  intro i
  ext z
  constructor
  · intro hz
    obtain ⟨hinf, hall⟩ := (Set.ext_iff.mp (hcut i) z).mp hz
    exact ⟨hinf, fun mc hmc => hall mc (hsub i hmc)⟩
  · rintro ⟨hinf, hall⟩
    refine (Set.ext_iff.mp (hcut i) z).mpr ⟨hinf, fun mc hmc => ?_⟩
    by_cases hk : mc ∈ keep i
    · exact hall mc hk
    · exact hbdd i mc hmc hk z hinf

/-- **A wall of `Â_∞` itself never has to appear in `cut`.**

This is the general reason an "escape wall" cannot obstruct `UpperCutW`.  An escape wall is by
construction a normal `ν ∈ E (⋃ⱼ Âⱼ)`, and membership in `E` means the supremum of `⟪ν, ·⟫` over
`Â_∞` is *attained*, hence finite; taking `mc₀ = (ν, that supremum)` satisfies `hbdd`, so the
entry drops out.  Geometrically this is `b3_colle2.txt:506`: the walls of `Â_∞` are
`i`-independent, so they are carried by the `z ∈ ⋃ⱼ Âⱼ` conjunct of `UpperCut` and the cut family
never needs to restate them. -/
theorem upperCut_drop_iUnion_wall {cut : ℕ → Set ((ℤ × ℤ) × ℤ)}
    (hcut : UpperCut Ahat cut) {mc₀ : (ℤ × ℤ) × ℤ}
    (hbdd : ∀ z ∈ (⋃ j, Ahat j), dot mc₀.1 z ≤ mc₀.2) :
    UpperCut Ahat (fun i => cut i \ {mc₀}) := by
  refine upperCut_prune hcut (fun _ _ h => h.1) ?_
  intro i mc hmc hnk
  have hmc₀ : mc = mc₀ := by
    by_contra hne
    exact hnk ⟨hmc, fun h => hne h⟩
  subst hmc₀
  exact hbdd

/-- Prune first, then discharge the sign clause on the smaller family. -/
theorem upperCutW_of_prune {cut keep : ℕ → Set ((ℤ × ℤ) × ℤ)}
    (hcut : UpperCut Ahat cut) (hsub : ∀ i : ℕ, keep i ⊆ cut i)
    (hbdd : ∀ i : ℕ, ∀ mc ∈ cut i, mc ∉ keep i →
      ∀ z ∈ (⋃ j, Ahat j), dot mc.1 z ≤ mc.2)
    (hw : ∀ i : ℕ, ∀ mc ∈ keep i, dot mc.1 w ≤ 0) :
    UpperCutW Ahat w :=
  ⟨keep, upperCut_prune hcut hsub hbdd, hw⟩

/-! ## §3.  The sign clause is forced, not assumed

§2 says the sign clause suffices.  This section says it is also unavoidable: on a tower that
satisfies `WDescent`, a cut that actually bites must have a `w`-nonpositive normal.  Together
with `upperCut_prune` (a cut that does not bite can be deleted) this pins `UpperCutW` from both
sides, so nothing here is stronger than `WDescent` in an avoidable way (硬规矩 5). -/

/-- One `w`-step from a point of `Â_i` still satisfies every cut of layer `i`, provided it stays
in `Â_∞` and above the floor. -/
theorem dot_le_of_wDescent {cut : ℕ → Set ((ℤ × ℤ) × ℤ)}
    (hcut : UpperCut Ahat cut) (hwd : WDescent Ahat nJ w cJ)
    {i : ℕ} {mc : (ℤ × ℤ) × ℤ} (hmc : mc ∈ cut i) {g : ℤ × ℤ} (hg : g ∈ Ahat i)
    (hmem : g + w ∈ ⋃ j, Ahat j) (hlev : cJ ≤ dot nJ (g + w)) :
    dot mc.1 g + dot mc.1 w ≤ mc.2 := by
  have hone : g + ((1 : ℕ) : ℤ) • w = g + w := by push_cast; rw [one_smul]
  have hstep : g + w ∈ Ahat i := by
    have h := hwd i g hg 1 (by rwa [hone]) (by rwa [hone])
    rwa [hone] at h
  have h2 := ((Set.ext_iff.mp (hcut i) (g + w)).mp hstep).2 mc hmc
  rwa [dot_add] at h2

/-- **Necessity of the sign clause.**  If a cut is *tight* at layer `i` — it has a boundary point
`g ∈ Â_i` with `mc.2 ≤ ⟪m, g⟫` — and that boundary point's `w`-step stays in `Â_∞` and above the
floor, then `⟪m, w⟫ ≤ 0` is forced by `WDescent`. -/
theorem dot_w_nonpos_of_tight {cut : ℕ → Set ((ℤ × ℤ) × ℤ)}
    (hcut : UpperCut Ahat cut) (hwd : WDescent Ahat nJ w cJ)
    {i : ℕ} {mc : (ℤ × ℤ) × ℤ} (hmc : mc ∈ cut i) {g : ℤ × ℤ} (hg : g ∈ Ahat i)
    (htight : mc.2 ≤ dot mc.1 g)
    (hmem : g + w ∈ ⋃ j, Ahat j) (hlev : cJ ≤ dot nJ (g + w)) :
    dot mc.1 w ≤ 0 := by
  have h := dot_le_of_wDescent hcut hwd hmc hg hmem hlev
  omega

/-- **The dichotomy, in one statement.**  On a `WDescent` tower a cut with `0 < ⟪m, w⟫` has no
boundary point that can be swept further: each of its boundary points leaves `Â_∞` or drops below
the floor after one `w`-step.  Such a cut therefore does nothing inside the layer and is a
candidate for `upperCut_prune`. -/
theorem tight_or_blocked_of_wDescent {cut : ℕ → Set ((ℤ × ℤ) × ℤ)}
    (hcut : UpperCut Ahat cut) (hwd : WDescent Ahat nJ w cJ)
    {i : ℕ} {mc : (ℤ × ℤ) × ℤ} (hmc : mc ∈ cut i) (hpos : 0 < dot mc.1 w) :
    ∀ g ∈ Ahat i, mc.2 ≤ dot mc.1 g →
      g + w ∉ (⋃ j, Ahat j) ∨ dot nJ (g + w) < cJ := by
  intro g hg htight
  by_cases hmem : g + w ∈ (⋃ j, Ahat j)
  · by_cases hlev : cJ ≤ dot nJ (g + w)
    · have h := dot_w_nonpos_of_tight hcut hwd hmc hg htight hmem hlev
      omega
    · exact Or.inr (not_le.mp hlev)
  · exact Or.inl hmem

/-! ## §4.  The floor is load-bearing: when `UpperCutW` is unreachable, and what replaces it

⛔ **§4.2 is dead weight (retracted 2026-09-24).**  §4 was built on the premise that the fifth
quantifier of `WDescent` (`cJ ≤ dot nJ (g + t•w)`) is load-bearing.  It is not: `hhp`
(`ChainExhaustInter.lean`) makes it vacuous on the chain — kernel receipts,
`lane-tower-hlev`'s `floor_free_on_iUnion` / `wDescent_iff_unguarded_of_hhp` /
`wSeparatedG_iff_wSeparated_of_hhp` (`tmp/wip/lane-tower-hlev-wsep.lean:928`/`:936`/`:948`,
axiom-free).  So on the chain `UpperCutG ⟺ UpperCut` and `UpperCutGW ⟺ UpperCutW`, and the six
§4.2 declarations are pure bookkeeping (硬规矩 5).  They are **kept, not deleted**, per the
round-172 freeze ("不删不扩"): they compile, their axioms are clean, and the mathematics is
correct — only the motivation is gone.  Do not build on them.

§4.1 is unaffected and stays: `not_upperCutW_of_escape` is a real fact about `UpperCutW`.
⚠ But note what it can and cannot reach: its hypothesis `hmem` demands `a + t•w ∈ ⋃ⱼÂⱼ`, and the
witness produced by `escapeW` (`ChainExhaustInter.lean`) lies in the **collar**, hence not in
`⋃ⱼÂⱼ` (`not_mem_iUnion_of_below_floor`, `tmp/wip/lane-tower-hlev-wsep.lean:1070`).  So this
theorem does **not** show `UpperCutW` is unreachable on the chain.  An earlier claim to the
contrary is retracted.

§2 and §3 pin `UpperCutW` between "sufficient for `WDescent`" and "forced by `WDescent` on
biting cuts".  Neither says the hypothesis is *attainable*.
-/

/-! ### §4.1  An escape configuration kills `UpperCutW` -/

/-- **An escape configuration kills `UpperCutW`.**

If some layer `Â_i` has a point `a` whose `w`-translate `a + t·w` is still in `Â_∞` but has left
`Â_i`, then *no* upper-cut representation of the tower can have all its normals
`w`-nonincreasing.

No geometry is used.  The cut entry `mc` that expels `a + t·w` from layer `i` would have to
satisfy `dot mc.1 a ≤ mc.2 < dot mc.1 a + t * dot mc.1 w`, hence `0 < dot mc.1 w`; so under the
sign clause no such entry exists and `a + t·w` is back in the layer, contradicting `hout`.

What this does **not** say: `wDescent_of_upperCutW` is correct and unaffected, and `WDescent`
itself is untouched — under `WDescent` the configuration above can only occur **below the
floor**, `dot nJ (a + t•w) < cJ`.  Kernel receipts for that collar statement:
`lane-tower-hlev`'s `escape_below_floor` (`tmp/wip/lane-tower-hlev-wsep.lean:402`) and the
banded form `escape_in_band` (`:424`, `cJ - ε ≤ ⟪nJ,·⟫ ≤ cJ - 1`).
⚠ Consequently this theorem cannot be applied to `escapeW`'s witness — see the §4 header.

Credit: lane-tower-hlev, round 168, who derived it via his `WSeparated` characterisation.  The
proof here is the second, independent route, read straight off `UpperCut` (PROTOCOL §13). -/
theorem not_upperCutW_of_escape {i : ℕ} {a : ℤ × ℤ} (ha : a ∈ Ahat i) {t : ℕ}
    (hmem : a + (t : ℤ) • w ∈ (⋃ j, Ahat j)) (hout : a + (t : ℤ) • w ∉ Ahat i) :
    ¬ UpperCutW Ahat w := by
  rintro ⟨cut, hcut, hw⟩
  refine hout ((Set.ext_iff.mp (hcut i) _).mpr ⟨hmem, fun mc hmc => ?_⟩)
  have h1 : dot mc.1 a ≤ mc.2 := ((Set.ext_iff.mp (hcut i) a).mp ha).2 mc hmc
  have h2 : (t : ℤ) * dot mc.1 w ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg t) (hw i mc hmc)
  rw [dot_add_zsmul]
  omega

/-! ### §4.2  The floor-guarded replacement -/

/-- **Floor-guarded upper cut**: the cut family only has to represent the layer *above the
`n_J`-floor*.  Below the floor the tower may do whatever it likes.

Same provenance as `UpperCut` (`b3_colle2.txt:506`), with the floor of `hhp`
(`ChainExhaustInter.lean`) added as a guard.  It is **weaker** than `UpperCut`
(`upperCutG_of_upperCut`), so assuming it is never a strengthening (硬规矩 5). -/
def UpperCutG (Ahat : ℕ → Set (ℤ × ℤ)) (nJ : ℤ × ℤ) (cJ : ℤ)
    (cut : ℕ → Set ((ℤ × ℤ) × ℤ)) : Prop :=
  ∀ i : ℕ, ∀ z ∈ (⋃ j, Ahat j), cJ ≤ dot nJ z →
    (z ∈ Ahat i ↔ ∀ mc ∈ cut i, dot mc.1 z ≤ mc.2)

/-- The packaged floor-guarded condition, the intended replacement for `UpperCutW`. -/
def UpperCutGW (Ahat : ℕ → Set (ℤ × ℤ)) (nJ w : ℤ × ℤ) (cJ : ℤ) : Prop :=
  ∃ cut : ℕ → Set ((ℤ × ℤ) × ℤ),
    UpperCutG Ahat nJ cJ cut ∧ ∀ i : ℕ, ∀ mc ∈ cut i, dot mc.1 w ≤ 0

/-- `UpperCutG` is weaker than `UpperCut`: the guard is only ever dropped, never used. -/
theorem upperCutG_of_upperCut {cut : ℕ → Set ((ℤ × ℤ) × ℤ)} (hcut : UpperCut Ahat cut) :
    UpperCutG Ahat nJ cJ cut := by
  refine fun i z hz _ => ⟨fun h => ((Set.ext_iff.mp (hcut i) z).mp h).2, fun h => ?_⟩
  exact (Set.ext_iff.mp (hcut i) z).mpr ⟨hz, h⟩

/-- **The floor-guarded route to `WDescent`.**

Beyond the two clauses of `UpperCutGW` this needs one extra inequality, `dot nJ w ≤ 0`.  That is
not a new obligation: it is `hsweepW : dot nJ w < 0` (`ChainExhaustInter.lean`), which by
`dot_neg_dir_neg_lt_iff` (`LatticeEdges.lean`) is exactly `0 < det ν_J ν_{J+1}`, i.e. "`ℓ_{J+1}`
is the counter-clockwise successor of `ℓ_J`" (`b3_colle2.txt:424`).

It is used for one step only: `hlev` guards `g + t•w`, and `dot nJ w ≤ 0` propagates the guard
*backwards* to `g`, which is where the cut representation has to be applied. -/
theorem wDescent_of_upperCutG {cut : ℕ → Set ((ℤ × ℤ) × ℤ)}
    (hcut : UpperCutG Ahat nJ cJ cut) (hnw : dot nJ w ≤ 0)
    (hw : ∀ i : ℕ, ∀ mc ∈ cut i, dot mc.1 w ≤ 0) :
    WDescent Ahat nJ w cJ := by
  intro i g hg t hmem hlev
  have hglev : cJ ≤ dot nJ g := by
    have h2 : (t : ℤ) * dot nJ w ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg t) hnw
    rw [dot_add_zsmul] at hlev
    omega
  have hgi := (hcut i g (Set.mem_iUnion.mpr ⟨i, hg⟩) hglev).mp hg
  refine (hcut i (g + (t : ℤ) • w) hmem hlev).mpr fun mc hmc => ?_
  have h1 := hgi mc hmc
  have h2 : (t : ℤ) * dot mc.1 w ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg t) (hw i mc hmc)
  rw [dot_add_zsmul]
  omega

/-- The packaged form. -/
theorem wDescent_of_upperCutGW (h : UpperCutGW Ahat nJ w cJ) (hnw : dot nJ w ≤ 0) :
    WDescent Ahat nJ w cJ := by
  obtain ⟨cut, hcut, hw⟩ := h
  exact wDescent_of_upperCutG hcut hnw hw

/-- `UpperCutW` still implies the guarded form, so §2's producers are not invalidated — they are
subsumed. -/
theorem upperCutGW_of_upperCutW (h : UpperCutW Ahat w) : UpperCutGW Ahat nJ w cJ := by
  obtain ⟨cut, hcut, hw⟩ := h
  exact ⟨cut, upperCutG_of_upperCut hcut, hw⟩

end Nivat.WCut

#print axioms Nivat.WCut.WDescent
#print axioms Nivat.WCut.UpperCut
#print axioms Nivat.WCut.UpperCutW
#print axioms Nivat.WCut.wDescent_of_upperCut
#print axioms Nivat.WCut.wDescent_of_upperCutW
#print axioms Nivat.WCut.upperCut_prune
#print axioms Nivat.WCut.upperCut_drop_iUnion_wall
#print axioms Nivat.WCut.upperCutW_of_prune
#print axioms Nivat.WCut.dot_le_of_wDescent
#print axioms Nivat.WCut.dot_w_nonpos_of_tight
#print axioms Nivat.WCut.tight_or_blocked_of_wDescent
#print axioms Nivat.WCut.not_upperCutW_of_escape
#print axioms Nivat.WCut.UpperCutG
#print axioms Nivat.WCut.UpperCutGW
#print axioms Nivat.WCut.upperCutG_of_upperCut
#print axioms Nivat.WCut.wDescent_of_upperCutG
#print axioms Nivat.WCut.wDescent_of_upperCutGW
#print axioms Nivat.WCut.upperCutGW_of_upperCutW

