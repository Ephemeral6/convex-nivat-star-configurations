/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.L1Assemble
import Nivat.External.Colle.L1StraddleMax
import Nivat.External.Colle.L1RegionBuild
import Nivat.External.Colle.L1Prim
import Nivat.External.Colle.L1CoverWedge
import Nivat.External.Colle.HbaseBridge
import Nivat.External.Colle.L1LevelSpan

/-!
# The producer for `exists_L1MaxBResidual` (leaf L1), conclusion verbatim

Lane Cclaim's file (exclusive, 2026-09-19).  Target: `Nivat.ColleReg.exists_L1MaxBResidual`
(`RegionSteps.lean`, one of the two remaining `sorry`s), whose conclusion is

    ∃ (e u u' v : ℤ × ℤ) (c τ : ℤ) (ε : Bool) (S₁ : Finset (ℤ × ℤ))
      (F : Nivat.L1Region.RegionFamily (T e ξ) u u' c),
      S₁ = S.image (· + v) ∧
      Nivat.ColleReg.L1Data.MaxBResidual (ξ := ξ) ε u u' c τ S₁ F

Same discipline as `RegionClaim411.lean` for leaf C: every theorem below ends in that
existential **byte for byte** (`tmp/l1claim_receipt.lean` restates the leaf's exact binder list
and conclusion and closes it with one application), so that wiring is a one-line body once the
hypotheses are in hand.  Nothing here is new mathematics; the file is the assembly point that
chooses the data Collé chooses and discharges every field the leaf's own binders can discharge.

## What the leaf's binders pay for, and what they do not

With `u := vl` (Collé's `h ∥ ℓ`, `b3_colle2.txt:806`; `Primitive vl` is `hvl_prim`):

| `MaxBResidual` field | discharged by | from |
|---|---|---|
| `det'  : det vl u' ≠ 0` | hypothesis `det'` | the producer's choice of `u'` |
| `prim  : Primitive u'` | hypothesis `prim` | same |
| `c0    : c ≠ 0` | hypothesis `c0` | Claim 4.6's period `h = c • vl` |
| `line0` | `L1Data.line_of_seed` | one seed row `t = τ` at the selected index |
| `base0` | `L1Data.MaxBResidual.base0_of_faces` | **leaf binders only**: `hSgen hℓ_nel hℓ_neg hvl_prim hdet_ℓ` + `det' prim` |
| `straddle` | `RegionFamily.straddle_tail` | one `Straddle` across `(N, N+1)`, or Figure 11(B)'s cover |

So of the six fields the leaf pays `base0` outright (Lemma 2.3 through `two_le_min_faces_of_nel`
and the recession cone through `exists_translate_subset_of_isRegion`, both `L1Assemble.lean`),
three are data constraints on the producer's `u'` and `c`, and two — `line0` and `straddle` —
are the residual content, stated here at the **selected** index `N` only.  Together with the
family `F` itself (`RegionFamily`'s four fields, produced by lane L1B's `ofWedge`,
`L1RegionBuild.lean`) that is the whole of what leaf L1 still owes.

## Why the family is handed over with its maximal index

`MaxBResidual` states `line0`/`base0` on `F.R 0` and `straddle` at every maximal index; read
together they pin index `0` to the selected `N` (`L1Assemble.lean`, section "The tail of the
family": `line0` puts `Q` in `R 0 ⊆ R N`, `straddle` at `N` needs the top face outside `R N`).
Collé chooses `N` first and places `𝒯` after (`b3_colle2.txt:820-824`).  So the producer supplies
the full family `F`, the maximal `N` (`hN`, `hN1` — the two outputs of `exists_greatest_periodOn`),
and the two membership facts **at `N`**; the witness handed back is `F.tail N hN`.  Two shapes:

* `exists_L1MaxBResidual_of_tail` — `N` explicit, `Straddle` given.
* `exists_L1MaxBResidual_of_family` — `N` implicit: the caller gives `line`/`Straddle` at every
  maximal index and the greatest one is selected here.  This is the shape for a producer that
  builds Collé's whole chain `𝓡^n_I` and cannot name `N` in advance.
* `exists_L1MaxBResidual_of_cover` — as `_of_tail`, but with `Straddle` replaced by Figure
  11(B)'s `genClosure` cover (`L1StraddleMax.straddle_of_cover`, lane Cconv).  The generating
  point may be the leaf's own `hgen : GeneratesAt ξ S gen`.

⚠ None of these reduces `sorry TOTAL` by itself (`CLAUDE.md` hard rule 1).  What they fix is the
*shape* of the residual, so that L1B's family and the two membership facts plug in with no
adapter.  In the three abstract-`F` theorems no hypothesis of the form
`IsMinimalCounterexample ξ → _` appears; `hξ`, `d`, `hdef`, `hcase1`, `hxper`, `hp_mem` are not
consumed there — `hdef` is consumed downstream by `L1Data.ofMaxB`, and `hcase1` is where `e` and
Claim 4.6's `base` come from, which is the family producer's business, not this file's.  The
concrete composite `exists_L1MaxBResidual_of_wedgeAt` does take `hξ` and `d`, for one purpose
only: Afill's `hinf_of_ge` spends them (through Prop 2.12) to prove `ofWedgeAt`'s `hinf`.
-/

set_option autoImplicit false

namespace Nivat.ColleReg.L1Claim

open Nivat Nivat.Colle41 Nivat.ColleReg.L1Data

variable {ξ : Config ℤ} {vl ℓ : ℤ × ℤ} {S : Finset (ℤ × ℤ)}

/-- **`exists_L1MaxBResidual`'s conclusion from the family at its maximal index.**

`u := vl`.  The leaf binders `hℓ_nel hℓ_neg hSgen hvl_prim hdet_ℓ` pay `base0` (Lemma 2.3 +
recession cone, `MaxBResidual.base0_of_faces`); `det' prim c0` are the producer's data choices;
`line` is conjunct 14 at its seed row `t = τ` (propagated by `line_of_seed`); `straddle` is
conjunct 15 across `(N, N+1)` (transported to the tail by `straddle_tail`).  The witness family
is `F.tail N hN`. -/
theorem exists_L1MaxBResidual_of_tail
    (hℓ_nel : ℓ ∈ Colle45.NonExpansiveLine ξ)
    (hℓ_neg : Colle45.IsOneSidedNonexpansive ξ (-ℓ))
    (hSgen : Nivat.Colle.IsGeneratingSet ξ S)
    (hvl_prim : Primitive vl) (hdet_ℓ : Nivat.LE2.dot ℓ vl = 0)
    {e u' v : ℤ × ℤ} {c τ : ℤ} (ε : Bool)
    (det' : det vl u' ≠ 0) (prim : Primitive u') (c0 : c ≠ 0)
    (F : Nivat.L1Region.RegionFamily (T e ξ) vl u' c) (N : ℕ)
    (hN : PeriodOn (T e ξ) (F.R N) (c • vl))
    (hN1 : ¬ PeriodOn (T e ξ) (F.R (N + 1)) (c • vl))
    (line : ∀ z ∈ derivedQ ε u' (S.image (· + v)),
      τ • u' + z ∈ F.R N ∧ τ • u' + z + c • vl ∈ F.R N)
    (straddle : Nivat.L1Region.Straddle (T e ξ) (F.R N) (F.R (N + 1)) (S.image (· + v))
      (derivedQ ε u' (S.image (· + v))) vl u' c τ) :
    ∃ (e u u' v : ℤ × ℤ) (c τ : ℤ) (ε : Bool) (S₁ : Finset (ℤ × ℤ))
      (F : Nivat.L1Region.RegionFamily (T e ξ) u u' c),
      S₁ = S.image (· + v) ∧
      Nivat.ColleReg.L1Data.MaxBResidual (ξ := ξ) ε u u' c τ S₁ F :=
  ⟨e, vl, u', v, c, τ, ε, S.image (· + v), F.tail N hN, rfl,
    MaxBResidual.ofFive ε (F.tail N hN) (isGeneratingSet_image hSgen v) hℓ_nel hℓ_neg hvl_prim
      hdet_ℓ det' prim c0 (line_of_seed (F.isRegion N) line)
      (Nivat.L1Region.RegionFamily.straddle_tail F N hN hN1 straddle)⟩

/-- **The same, with `N` selected here.**  For a producer that builds Collé's whole chain
`𝓡^n_I` and supplies the two membership facts at *every* maximal index (`b3_colle2.txt:820`:
`N` is only known after the chain exists).  `exists_greatest_periodOn` picks `N`. -/
theorem exists_L1MaxBResidual_of_family
    (hℓ_nel : ℓ ∈ Colle45.NonExpansiveLine ξ)
    (hℓ_neg : Colle45.IsOneSidedNonexpansive ξ (-ℓ))
    (hSgen : Nivat.Colle.IsGeneratingSet ξ S)
    (hvl_prim : Primitive vl) (hdet_ℓ : Nivat.LE2.dot ℓ vl = 0)
    {e u' v : ℤ × ℤ} {c τ : ℤ} (ε : Bool)
    (det' : det vl u' ≠ 0) (prim : Primitive u') (c0 : c ≠ 0)
    (F : Nivat.L1Region.RegionFamily (T e ξ) vl u' c)
    (hmax : ∀ N : ℕ, PeriodOn (T e ξ) (F.R N) (c • vl) →
      ¬ PeriodOn (T e ξ) (F.R (N + 1)) (c • vl) →
      (∀ z ∈ derivedQ ε u' (S.image (· + v)),
        τ • u' + z ∈ F.R N ∧ τ • u' + z + c • vl ∈ F.R N) ∧
      Nivat.L1Region.Straddle (T e ξ) (F.R N) (F.R (N + 1)) (S.image (· + v))
        (derivedQ ε u' (S.image (· + v))) vl u' c τ) :
    ∃ (e u u' v : ℤ × ℤ) (c τ : ℤ) (ε : Bool) (S₁ : Finset (ℤ × ℤ))
      (F : Nivat.L1Region.RegionFamily (T e ξ) u u' c),
      S₁ = S.image (· + v) ∧
      Nivat.ColleReg.L1Data.MaxBResidual (ξ := ξ) ε u u' c τ S₁ F := by
  obtain ⟨N, hN, hN1⟩ :=
    Nivat.L1Region.exists_greatest_periodOn F.monotone F.base F.union_not
  obtain ⟨line, straddle⟩ := hmax N hN hN1
  exact exists_L1MaxBResidual_of_tail hℓ_nel hℓ_neg hSgen hvl_prim hdet_ℓ ε det' prim c0 F N hN
    hN1 line straddle

/-- **The same, with `Straddle` replaced by Figure 11(B)'s cover** (`b3_colle2.txt:848-856`,
`L1StraddleMax.straddle_of_cover`).  `hgen : GeneratesAt ξ Sφ a` may be the leaf's own
`hgen : GeneratesAt ξ S gen`; `hcover` says the overlap of `F.R (N+1)` with its `c•vl`-shift is
`Sφ`-generated from the overlap of `F.R N` together with the edge point's forward `u'`-ray. -/
theorem exists_L1MaxBResidual_of_cover
    (hℓ_nel : ℓ ∈ Colle45.NonExpansiveLine ξ)
    (hℓ_neg : Colle45.IsOneSidedNonexpansive ξ (-ℓ))
    (hSgen : Nivat.Colle.IsGeneratingSet ξ S)
    (hvl_prim : Primitive vl) (hdet_ℓ : Nivat.LE2.dot ℓ vl = 0)
    {e u' v : ℤ × ℤ} {c τ : ℤ} (ε : Bool)
    (det' : det vl u' ≠ 0) (prim : Primitive u') (c0 : c ≠ 0)
    (F : Nivat.L1Region.RegionFamily (T e ξ) vl u' c) (N : ℕ)
    (hN : PeriodOn (T e ξ) (F.R N) (c • vl))
    (hN1 : ¬ PeriodOn (T e ξ) (F.R (N + 1)) (c • vl))
    (line : ∀ z ∈ derivedQ ε u' (S.image (· + v)),
      τ • u' + z ∈ F.R N ∧ τ • u' + z + c • vl ∈ F.R N)
    {Sφ : Finset (ℤ × ℤ)} {a : ℤ × ℤ} (hgen : Nivat.Colle.GeneratesAt ξ Sφ a)
    (hcover : ∀ g ∈ S.image (· + v), g ∉ derivedQ ε u' (S.image (· + v)) → ∀ t₀ : ℤ, τ ≤ t₀ →
      Nivat.L1StraddleMax.overlap (F.R (N + 1)) (c • vl) ⊆
        Nivat.MaxEnv.genClosure Sφ a
          (Nivat.L1StraddleMax.overlap (F.R N) (c • vl) ∪ Nivat.L1StraddleMax.ray g u' t₀)) :
    ∃ (e u u' v : ℤ × ℤ) (c τ : ℤ) (ε : Bool) (S₁ : Finset (ℤ × ℤ))
      (F : Nivat.L1Region.RegionFamily (T e ξ) u u' c),
      S₁ = S.image (· + v) ∧
      Nivat.ColleReg.L1Data.MaxBResidual (ξ := ξ) ε u u' c τ S₁ F :=
  exists_L1MaxBResidual_of_tail hℓ_nel hℓ_neg hSgen hvl_prim hdet_ℓ ε det' prim c0 F N hN hN1
    line (Nivat.L1StraddleMax.straddle_of_cover (T_mem_orbitClosure ξ e) hgen hcover)

/-! ## The composite on L1B's concrete family (2026-09-19, team-lead's request)

`exists_L1MaxBResidual_of_tail` above takes `N` as an argument; but on a concrete family the
maximal index is produced *from* the family by `exists_greatest_periodOn`, so `N` cannot be
named before `F` exists and `_of_tail` cannot sit at the top of the composite (lane Aface,
`tmp/Aface_l1_skeleton.lean`, receipt not landed: the `_of_tail`-topped version elaborates
`hline` against a metavariable).  `exists_L1MaxBResidual_of_wedgeAt` below is the composite
with `F := L1RegionBuild.ofWedgeAt …` (`L1RegionBuild.lean:384`, base at an arbitrary index
`k`) and `N` selected inside, so that its binder list is **exactly** what leaf L1 still owes.

Discharged in the body, each by an already-compiled declaration:

| was a binder of `ofWedgeAt` / `_of_tail` | killed by |
|---|---|
| `hB : IsLatticeConvexRegion B` | `isLatticeConvexRegion_of_envOf` (`L1RegionBuild.lean:410`); the binder is now `hEnv : EnvOf U B`, which is `hcase1`'s first component (`CaseSplit.lean:82`) |
| `hu' : Primitive u'` | from `hunimod` inline: `Primitive` is `IsCoprime` (`Config.lean:156`) and `det u' vl = ±1` is a Bézout witness `(±vl.2, ∓vl.1)` |
| `det' : det vl u' ≠ 0` | `L1Data.det_ne_zero_of_unimod` (`L1Assemble.lean:2107`) |
| `hinf : ¬ PeriodOn (T e ξ) (wedgeFull B vl u') (c • vl)` | `hinf_of_ge` (`L1CoverWedge.lean:237`, lane Afill): `ψ := expNormal vl u'` (arguments swapped) has `dot ψ vl = 0`, `dot ψ u' = 1`, so the half-plane `{z ∣ dot ψ b₀ ≤ dot ψ z}` sits inside `wedgeFull B vl u'` with no boundedness or minimality of `B`; Prop 2.12 (`L1Region.union_not_of_halfPlane_cover`, `hnp := hξ.1.2.2.1`) then forbids the period.  Costs `hξ`, `d` (both leaf binders, free at the call site) and `c • vl ≠ 0` (below) |
| `c • vl ≠ 0` | `smul_ne_zero c0 hvl_prim.ne_zero` (`Primitive.ne_zero`, `Config.lean:158`) |
| `base0` | `MaxBResidual.ofFive` inside `_of_tail` (leaf binders `hSgen hℓ_nel hℓ_neg hvl_prim hdet_ℓ`) |
| `N`, `hN`, `hN1` | `exists_greatest_periodOn F.monotone F.base F.union_not` (`L1Region.lean:102`) |

⚠ `c0 : c ≠ 0` **came back as a binder** when `hinf` left.  The 14:32 version derived it from
`hinf` (`L1Prim.ne_zero_of_not_periodOn_smul`, `L1Prim.lean:529`, lane Aface — `c = 0` makes
`c • vl = 0`, and `PeriodOn _ _ 0` holds on every set); that derivation is only available while
`hinf` is *assumed*.  Once `hinf` is *proved* (`hinf_of_ge`) the dependency runs the other way:
`hinf` is false at `c = 0`, so its proof must consume `c • vl ≠ 0`.  Net effect of wiring
`hinf_of_ge`: the residual loses `hinf` and gains `c0`.  ⚠ `c0` alone is trivially satisfiable
(`c := 1`), but `c` is shared with `hbase`, and `hbase` at `c = 0` is trivially *true*
(`PeriodOn _ _ 0`).  So `c0` is not a free data constraint like `hunimod`: it is the
"non-zero" in Claim 4.6's non-zero period, and it falls to whoever proves `hbase` to produce the
pair `(hbase, c0)` together.  One owner, two binders.

Not discharged — the residual:

* `hunimod : det u' vl = ±1` — a **data constraint** naming `u'`, not a residual: satisfiable
  outright by `Primitive.exists_dual hvl_prim` (`Config.lean:164`).  It stays a binder only
  because every residual below mentions `u'`; choosing `u'` here would force them under
  `∀ u'` (the shape of L1asm's former `exists_L1MaxBResidual_of_normal`, deleted 2026-09-19 —
  see the "§14 / §20 record" block in `L1Assemble.lean`).  ⚠ Shared variable, same class as
  `c0`: `hbase`/`hline`/`hstraddle` must all be proved at *one* `u'` with `det u' vl = ±1`.
  Collé's `u' = v_{ℓ'}`, `ℓ' = ℓ_I`, comes from `d`'s line chain (`b3_colle2.txt:812-814`) and
  is not unimodular against `vl` in general; his `d_n` (`:816`) enumerates the *attained*
  levels, which `chainFull`'s consecutive `expLevel` replaces.  Reading, not measured (§15).
* `c0 : c ≠ 0` — paired with `hbase` (AnfpL): Claim 4.6's period is non-zero, see above.
  The sign of `c` is free (team-lead 2026-09-19, from Cprobe: `p ↦ -p` keeps `Per` an
  `AddSubgroup`, flips `det p vl`, and moves `hbase` across `periodOn_neg_zsmul`), so WLOG
  `0 < c`.  ⚠ Reading, not measured here (§15): `periodOn_neg_zsmul` has no declaration under
  `Nivat/` at the time of writing, and no field of `WedgeResidual` assumes `0 < c`.
* `hlev : LevelInterval B vl` — `B` is the **wedge seed** (the `Set` behind
  `wedgeFull`/`chainFull`; Collé's Case-1 `B`, `b3_colle2.txt:778/784`), not Lemma 4.1's
  `maxB … : Finset` — the two are tabulated in `OPEN.md #10`'s retraction (2026-09-19).  `B` is
  chosen by the proof of `hbase` together with `b₀ k c e u'`, and `hlev` is a constraint on
  that one choice (`OPEN.md #10`).  It is not free from lattice convexity alone
  (`RegionSweep.lean:396` `isLatticeConvexRegion_pair` + `:447` `not_levelInterval_pair` on
  `{(0,0),(1,2)}`; `L1CoverWedge.lean:329` `case1_and_not_levelInterval` closes the
  `hcase1` route too), and `hEnv` adds nothing beyond convexity when `U` is free
  (`∃ U, EnvOf U B ↔ IsLatticeConvexRegion B`, `tmp/l1claim_receipt.lean`, via `enveloped_refl`).
* `hbase` — periodicity on `chainFull … k` (AnfpL; Collé Claim 4.6).
* `hsel` — at the maximal index: the `line0` seed (Cprobe) and one `Straddle` (Cconv), with
  `τ` chosen *after* `N` (`b3_colle2.txt:820-824`), shifted by `k`.  This is the shape of
  L1asm's former `MaxBResidual.exists_of_wedge` (deleted 2026-09-19, §14 / §20 record in
  `L1Assemble.lean`; its content is this theorem's body).  `exists_L1MaxBResidual_of_wedgeAt_split`
  below splits `hsel` into Cprobe's `hline` and Cconv's `hstraddle` sharing the one `τ`.

`exists_greatest_periodOn` returns *some* maximal index; Aface's
`L1Prim.maximal_index_unique` (`L1Prim.lean:633`, landed, `[propext, Classical.choice,
Quot.sound]`; the `tmp/Aface_l1_skeleton.lean` copy stays in place, §14) proves the maximal index is **unique**
(`PeriodOn.mono` + `F.monotone` make `{n | PeriodOn (F.R n) _}` downward closed), so `hsel`'s
`∀ N` ranges over a single index and the two residual shapes — "at every maximal index"
(`_of_family`, this theorem) and "at the named index" (`_of_tail`) — are **equivalent**, not
one stronger than the other.  Nobody owes `line`/`Straddle` at more than one index.  ⚠ Split, not reduction: `sorry TOTAL` is
unchanged (`CLAUDE.md` hard rule 1); what changes is that the residual is a kernel-checked
binder list rather than prose. -/

/-- **`exists_L1MaxBResidual`'s conclusion, verbatim, from `ofWedgeAt` and the residual.**
See the section docstring for what each former binder was discharged by.  `hξ`, `d` are the
leaf's own first two binders; they pay `hinf` through `hinf_of_ge`. -/
theorem exists_L1MaxBResidual_of_wedgeAt
    (hξ : IsMinimalCounterexample ξ) (d : Nivat.Colle35.DecompDataZ ξ)
    (hℓ_nel : ℓ ∈ Colle45.NonExpansiveLine ξ)
    (hℓ_neg : Colle45.IsOneSidedNonexpansive ξ (-ℓ))
    (hSgen : Nivat.Colle.IsGeneratingSet ξ S)
    (hvl_prim : Primitive vl) (hdet_ℓ : Nivat.LE2.dot ℓ vl = 0)
    {e u' v b₀ : ℤ × ℤ} {c : ℤ} (ε : Bool) {U B : Set (ℤ × ℤ)}
    (hEnv : Nivat.LE2.EnvOf U B) (hb₀ : b₀ ∈ B)
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) (c0 : c ≠ 0)
    (hlev : Nivat.RegionSweep.LevelInterval B vl) (k : ℕ)
    (hbase : PeriodOn (T e ξ) (chainFull B vl u' b₀ k) (c • vl))
    (hsel : ∀ N : ℕ, PeriodOn (T e ξ) (chainFull B vl u' b₀ (k + N)) (c • vl) →
      ¬ PeriodOn (T e ξ) (chainFull B vl u' b₀ (k + (N + 1))) (c • vl) →
      ∃ τ : ℤ,
        (∀ z ∈ derivedQ ε u' (S.image (· + v)),
          τ • u' + z ∈ chainFull B vl u' b₀ (k + N) ∧
          τ • u' + z + c • vl ∈ chainFull B vl u' b₀ (k + N)) ∧
        Nivat.L1Region.Straddle (T e ξ) (chainFull B vl u' b₀ (k + N))
          (chainFull B vl u' b₀ (k + (N + 1))) (S.image (· + v))
          (derivedQ ε u' (S.image (· + v))) vl u' c τ) :
    ∃ (e u u' v : ℤ × ℤ) (c τ : ℤ) (ε : Bool) (S₁ : Finset (ℤ × ℤ))
      (F : Nivat.L1Region.RegionFamily (T e ξ) u u' c),
      S₁ = S.image (· + v) ∧
      Nivat.ColleReg.L1Data.MaxBResidual (ξ := ξ) ε u u' c τ S₁ F := by
  have hB : IsLatticeConvexRegion B := isLatticeConvexRegion_of_envOf hEnv
  have hu' : Primitive u' := by
    show IsCoprime u'.1 u'.2
    rcases hunimod with h | h
    · exact ⟨vl.2, -vl.1, by simp only [det] at h; linear_combination h⟩
    · exact ⟨-vl.2, vl.1, by simp only [det] at h; linear_combination -h⟩
  have hinf : ¬ PeriodOn (T e ξ) (wedgeFull B vl u') (c • vl) :=
    hinf_of_ge e hξ d hb₀ hunimod (smul_ne_zero c0 hvl_prim.ne_zero)
  let F : Nivat.L1Region.RegionFamily (T e ξ) vl u' c :=
    ofWedgeAt hb₀ hB hvl_prim hu' hlev hunimod k hbase hinf
  have hR : ∀ n, F.R n = chainFull B vl u' b₀ (k + n) := fun _ => rfl
  obtain ⟨N, hN, hN1⟩ :=
    Nivat.L1Region.exists_greatest_periodOn F.monotone F.base F.union_not
  obtain ⟨τ, hline, hstr⟩ := hsel N (by rw [← hR]; exact hN) (by rw [← hR]; exact hN1)
  exact exists_L1MaxBResidual_of_tail hℓ_nel hℓ_neg hSgen hvl_prim hdet_ℓ ε
    (det_ne_zero_of_unimod hunimod) hu' c0 F N hN hN1
    (by rw [hR]; exact hline) (by rw [hR, hR]; exact hstr)

/-- **`hsel` split into the two slots it was dispatched on** (lane L1asm's receipt
`tmp/l1asm_wedge_entry.lean`, moved here).  `hsel` packs `∃ τ, line τ ∧ Straddle τ` at the
maximal index; the two cannot be independent `∀ N …` binders because `τ` is chosen *after* `N`
and shared — `line` is what fixes `τ` (the placement of `𝒯` with `𝒯 ∖ ℓ'_𝒯 ⊂ 𝓡^N_I`,
`b3_colle2.txt:820-824`), `Straddle` is stated for that `τ`.  So `hstraddle` is handed the `τ`
and the `line` fact that `hline` produced:

* `hline`     — Cprobe: at the maximal index, *some* `τ` places the window.
* `hstraddle` — Cconv: at the maximal index, for *any* `τ` that places the window, the
                straddle holds at `τ`.  (A proof that never uses the `line` fact may ignore that
                hypothesis; a `Straddle` for every `τ` is stronger.) -/
theorem exists_L1MaxBResidual_of_wedgeAt_split
    (hξ : IsMinimalCounterexample ξ) (d : Nivat.Colle35.DecompDataZ ξ)
    (hℓ_nel : ℓ ∈ Colle45.NonExpansiveLine ξ)
    (hℓ_neg : Colle45.IsOneSidedNonexpansive ξ (-ℓ))
    (hSgen : Nivat.Colle.IsGeneratingSet ξ S)
    (hvl_prim : Primitive vl) (hdet_ℓ : Nivat.LE2.dot ℓ vl = 0)
    {e u' v b₀ : ℤ × ℤ} {c : ℤ} (ε : Bool) {U B : Set (ℤ × ℤ)}
    (hEnv : Nivat.LE2.EnvOf U B) (hb₀ : b₀ ∈ B)
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) (c0 : c ≠ 0)
    (hlev : Nivat.RegionSweep.LevelInterval B vl) (k : ℕ)
    (hbase : PeriodOn (T e ξ) (chainFull B vl u' b₀ k) (c • vl))
    -- Cprobe's slot (`line0` seed): at the maximal index, some `τ` places the window.
    (hline : ∀ N : ℕ, PeriodOn (T e ξ) (chainFull B vl u' b₀ (k + N)) (c • vl) →
      ¬ PeriodOn (T e ξ) (chainFull B vl u' b₀ (k + (N + 1))) (c • vl) →
      ∃ τ : ℤ, ∀ z ∈ derivedQ ε u' (S.image (· + v)),
        τ • u' + z ∈ chainFull B vl u' b₀ (k + N) ∧
        τ • u' + z + c • vl ∈ chainFull B vl u' b₀ (k + N))
    -- Cconv's slot (conjunct 15): at the maximal index, for any `τ` that places the window.
    (hstraddle : ∀ N : ℕ, PeriodOn (T e ξ) (chainFull B vl u' b₀ (k + N)) (c • vl) →
      ¬ PeriodOn (T e ξ) (chainFull B vl u' b₀ (k + (N + 1))) (c • vl) →
      ∀ τ : ℤ,
        (∀ z ∈ derivedQ ε u' (S.image (· + v)),
          τ • u' + z ∈ chainFull B vl u' b₀ (k + N) ∧
          τ • u' + z + c • vl ∈ chainFull B vl u' b₀ (k + N)) →
        Nivat.L1Region.Straddle (T e ξ) (chainFull B vl u' b₀ (k + N))
          (chainFull B vl u' b₀ (k + (N + 1))) (S.image (· + v))
          (derivedQ ε u' (S.image (· + v))) vl u' c τ) :
    ∃ (e u u' v : ℤ × ℤ) (c τ : ℤ) (ε : Bool) (S₁ : Finset (ℤ × ℤ))
      (F : Nivat.L1Region.RegionFamily (T e ξ) u u' c),
      S₁ = S.image (· + v) ∧
      Nivat.ColleReg.L1Data.MaxBResidual (ξ := ξ) ε u u' c τ S₁ F :=
  exists_L1MaxBResidual_of_wedgeAt hξ d hℓ_nel hℓ_neg hSgen hvl_prim hdet_ℓ ε hEnv hb₀ hunimod
    c0 hlev k hbase fun N hN hN1 =>
      let ⟨τ, hl⟩ := hline N hN hN1
      ⟨τ, hl, hstraddle N hN hN1 τ hl⟩

/-! ## The wedge route as a `structure` (2026-09-19 16:4x, team-lead's request; `ChainCanon.lean`
is the template)

`exists_L1MaxBResidual_of_wedgeAt_split` above is a 20-binder theorem.  `WedgeResidual` below is
the same binder list as a `structure`, so that (a) each obligation is a named field the kernel
checks on its own, (b) the data (`e u' v b₀ c ε B k`) and the constraints on that data
(`hB hb₀ hunimod c0`) are visibly one package chosen once — not eight independent choices —
and (c) the three genuinely open fields `hlev` / `hbase` / (`hline` + `hstraddle`) are
**fields, not `sorry`s**: building a `WedgeResidual` is exactly leaf L1's remaining work.
The point of (b): the data `B b₀ k c e u'` is chosen by **one** person, and `hbase`, `hline`,
`hstraddle` must all be proved at that one choice — the three are not independent obligations
to hand to three lanes.  Before this structure that fact lived only in a table; here it is in
the type.

`hB : IsLatticeConvexRegion B` replaces `_of_wedgeAt`'s `hEnv : EnvOf U B`: with `U` free the
two are equivalent (`enveloped_refl`, `LatticeEdges.lean:641`; kernel check in
`tmp/l1claim_receipt.lean`), and the honest one is the weaker.

`WedgeResidual.ofSweep` then discharges `hbase` through `HbaseBridge` (`HbaseBridge.lean:185`,
`hbase_at_of_sweep_of_isGeneratingSet`) at `k := 0` with Afill's covering
`enum := coverEnum vl u' b₀` (`L1CoverWedge.lean:387`): of the bridge's four holes, `hgen` is
paid by `hSgen` plus a vertex `a` of `S` (`ha`, `hconv` — AnfpL's
`VertexFromEdge.exists_generatesAt_of_not_isEdge`, `VertexFromEdge.lean:79`, produces one), `hK`
by `hK_of_coverEnum` (`L1CoverWedge.lean:432`, index `0` only — `HbaseBridge.lean` §8 shows
index `1` is false, §7 that index `0` costs nothing), leaving `hD` (producer:
`HbaseBridge.hD_of_halfStrip`, `:277`, from a `q`-step periodicity on a half-strip) and `hwin`.

⚠ `hlev` may be false for every admissible `B` (`OPEN.md #10`, L1B measuring).  Making it a
field is what makes that visible: if it is, no `WedgeResidual` exists and the whole route is
dead at one named field, not somewhere inside a 20-binder theorem. -/

/-- **Leaf L1's remaining work, as a structure.**  Data first, then the constraints on the
data, then the three open obligations.  Every field statement is copied verbatim from
`exists_L1MaxBResidual_of_wedgeAt_split`'s binders. -/
structure WedgeResidual (ξ : Config ℤ) (S : Finset (ℤ × ℤ)) (vl : ℤ × ℤ) where
  /-- `ξ' = T e ξ` (`Case1`'s translation). -/
  e : ℤ × ℤ
  /-- `u' = v_{ℓ'}`, the sweep direction of the wedge. -/
  u' : ℤ × ℤ
  /-- The translation of the window: `S₁ = S.image (· + v)`. -/
  v : ℤ × ℤ
  /-- The base point of the chain's level cut. -/
  b₀ : ℤ × ℤ
  /-- The period multiplier, `h = c • vl`. -/
  c : ℤ
  /-- Which side of `S₁` is the top face. -/
  ε : Bool
  /-- The wedge seed — Collé's Case-1 `B` (`b3_colle2.txt:778`), **not** Lemma 4.1's `maxB`. -/
  B : Set (ℤ × ℤ)
  /-- The base index of the family. -/
  k : ℕ
  /-- `B` is lattice-convex (all `hEnv : EnvOf U B` gives, `isLatticeConvexRegion_of_envOf`). -/
  hB : IsLatticeConvexRegion B
  hb₀ : b₀ ∈ B
  /-- `u'` is unimodular against `vl` (satisfiable: `L1Data.exists_u'_unimod`,
  `L1Assemble.lean:2127`). -/
  hunimod : det u' vl = 1 ∨ det u' vl = -1
  /-- Claim 4.6's period is non-zero.  Forced by `hinf_of_ge`; see the section docstring of
  `exists_L1MaxBResidual_of_wedgeAt`. -/
  c0 : c ≠ 0
  /-- **Open** (`OPEN.md #10`, L1B). -/
  hlev : Nivat.RegionSweep.LevelInterval B vl
  /-- **Open** (AnfpL; Claim 4.6).  Split into the sweep's holes by `ofSweep`. -/
  hbase : PeriodOn (T e ξ) (chainFull B vl u' b₀ k) (c • vl)
  /-- **Open** (Cprobe): at the maximal index, some `τ` places the window. -/
  hline : ∀ N : ℕ, PeriodOn (T e ξ) (chainFull B vl u' b₀ (k + N)) (c • vl) →
    ¬ PeriodOn (T e ξ) (chainFull B vl u' b₀ (k + (N + 1))) (c • vl) →
    ∃ τ : ℤ, ∀ z ∈ derivedQ ε u' (S.image (· + v)),
      τ • u' + z ∈ chainFull B vl u' b₀ (k + N) ∧
      τ • u' + z + c • vl ∈ chainFull B vl u' b₀ (k + N)
  /-- **Open** (Cconv): at the maximal index, for any `τ` that places the window. -/
  hstraddle : ∀ N : ℕ, PeriodOn (T e ξ) (chainFull B vl u' b₀ (k + N)) (c • vl) →
    ¬ PeriodOn (T e ξ) (chainFull B vl u' b₀ (k + (N + 1))) (c • vl) →
    ∀ τ : ℤ,
      (∀ z ∈ derivedQ ε u' (S.image (· + v)),
        τ • u' + z ∈ chainFull B vl u' b₀ (k + N) ∧
        τ • u' + z + c • vl ∈ chainFull B vl u' b₀ (k + N)) →
      Nivat.L1Region.Straddle (T e ξ) (chainFull B vl u' b₀ (k + N))
        (chainFull B vl u' b₀ (k + (N + 1))) (S.image (· + v))
        (derivedQ ε u' (S.image (· + v))) vl u' c τ

/-- **`exists_L1MaxBResidual`'s conclusion, verbatim, from a `WedgeResidual`.**  The seven
leaf binders are the only other inputs. -/
theorem exists_L1MaxBResidual_of_wedgeResidual
    (hξ : IsMinimalCounterexample ξ) (d : Nivat.Colle35.DecompDataZ ξ)
    (hℓ_nel : ℓ ∈ Colle45.NonExpansiveLine ξ)
    (hℓ_neg : Colle45.IsOneSidedNonexpansive ξ (-ℓ))
    (hSgen : Nivat.Colle.IsGeneratingSet ξ S)
    (hvl_prim : Primitive vl) (hdet_ℓ : Nivat.LE2.dot ℓ vl = 0)
    (r : WedgeResidual ξ S vl) :
    ∃ (e u u' v : ℤ × ℤ) (c τ : ℤ) (ε : Bool) (S₁ : Finset (ℤ × ℤ))
      (F : Nivat.L1Region.RegionFamily (T e ξ) u u' c),
      S₁ = S.image (· + v) ∧
      Nivat.ColleReg.L1Data.MaxBResidual (ξ := ξ) ε u u' c τ S₁ F :=
  exists_L1MaxBResidual_of_wedgeAt_split hξ d hℓ_nel hℓ_neg hSgen hvl_prim hdet_ℓ r.ε
    (Nivat.LE2.enveloped_refl r.B r.hB) r.hb₀ r.hunimod r.c0 r.hlev r.k r.hbase r.hline
    r.hstraddle

/-- **`hbase` paid by the sweep.**  `k := 0`, `enum := coverEnum vl u' b₀`; `hgen` from
`hSgen` and the vertex `(a, ha, hconv)`, `hK` from `hK_of_coverEnum`.  What remains of
`hbase` is `hD` and `hwin`.  `hline`/`hstraddle` are stated at index `N` (not `0 + N`) and
transported. -/
noncomputable def WedgeResidual.ofSweep
    (hSgen : Nivat.Colle.IsGeneratingSet ξ S)
    {e u' v b₀ : ℤ × ℤ} {c : ℤ} (ε : Bool) {B : Set (ℤ × ℤ)}
    (hB : IsLatticeConvexRegion B) (hb₀ : b₀ ∈ B)
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) (c0 : c ≠ 0)
    (hlev : Nivat.RegionSweep.LevelInterval B vl)
    -- `hgen`'s vertex: `IsGeneratingSet` hands out `GeneratesAt` exactly here
    -- (`Generating.lean:58`).
    {a : ℤ × ℤ} (ha : a ∈ S) (hconv : Nivat.LatticeConvex (S.erase a))
    -- `hD`: the seed of (4.4).
    {D : Set (ℤ × ℤ)} (hD : ∀ z ∈ D, (T e ξ) z = T (c • vl) (T e ξ) z)
    -- `hwin`: every punctured window translate along `coverEnum` lands in the seed or earlier.
    (hwin : ∀ i j : ℕ, ∀ z ∈ S.erase a,
      z + (coverEnum vl u' b₀ i j - a) ∈
        D ∪ (⋃ i' ∈ {i' | i' < i}, Set.range (coverEnum vl u' b₀ i')) ∪
          (coverEnum vl u' b₀ i '' {j' | j' < j}))
    (hline : ∀ N : ℕ, PeriodOn (T e ξ) (chainFull B vl u' b₀ N) (c • vl) →
      ¬ PeriodOn (T e ξ) (chainFull B vl u' b₀ (N + 1)) (c • vl) →
      ∃ τ : ℤ, ∀ z ∈ derivedQ ε u' (S.image (· + v)),
        τ • u' + z ∈ chainFull B vl u' b₀ N ∧
        τ • u' + z + c • vl ∈ chainFull B vl u' b₀ N)
    (hstraddle : ∀ N : ℕ, PeriodOn (T e ξ) (chainFull B vl u' b₀ N) (c • vl) →
      ¬ PeriodOn (T e ξ) (chainFull B vl u' b₀ (N + 1)) (c • vl) →
      ∀ τ : ℤ,
        (∀ z ∈ derivedQ ε u' (S.image (· + v)),
          τ • u' + z ∈ chainFull B vl u' b₀ N ∧
          τ • u' + z + c • vl ∈ chainFull B vl u' b₀ N) →
        Nivat.L1Region.Straddle (T e ξ) (chainFull B vl u' b₀ N)
          (chainFull B vl u' b₀ (N + 1)) (S.image (· + v))
          (derivedQ ε u' (S.image (· + v))) vl u' c τ) :
    WedgeResidual ξ S vl where
  e := e
  u' := u'
  v := v
  b₀ := b₀
  c := c
  ε := ε
  B := B
  k := 0
  hB := hB
  hb₀ := hb₀
  hunimod := hunimod
  c0 := c0
  hlev := hlev
  hbase := Nivat.HbaseBridge.hbase_at_of_sweep_of_isGeneratingSet hSgen ha hconv 0 hD
    (coverEnum vl u' b₀) hwin (hK_of_coverEnum hunimod)
  hline := fun N hN hN1 => by
    simp only [Nat.zero_add] at hN hN1 ⊢
    exact hline N hN hN1
  hstraddle := fun N hN hN1 τ hl => by
    simp only [Nat.zero_add] at hN hN1 hl ⊢
    exact hstraddle N hN hN1 τ hl

/-! ## §4  The fringe of the chain and its two sides (team-lead's dispatch, 2026-09-19 17:xx)

Aface's row order (`HbaseBridge.lean` §13–§15) reduces `hwin` to one binder,
`hfringe : ∀ k ∈ R, ∀ z ∈ S.erase a, z + (k - a) ∈ R ∪ D` with `R := chainFull B vl u' b₀ 0`:
a window translate that leaves `R` must land in the seed `D`.  The dispatch asked for
(1) the fringe as a set, (2) a proof that its `vl` side is covered by `halfStrip B vl`
(`LatticeEdges.lean:1810`, the seed shape `hD_of_halfStrip` produces) once `B` is `d` deep along
`vl`, and (3) the `u'` side as a named hypothesis, not attempted.

**Which side is which.**  `R = wedgeFull B vl u' ∩ {w ∣ dot m b₀ ≤ dot m w}` for
`m := expNormal u' vl` (`chainFull`, `L1RegionBuild.lean:305`; `cut`, `L1Region.lean:197`), and
`wedgeFull` sweeps `B` by *all* of `ℤ • vl` before the forward `u'`-sweep (`fullSweep`,
`L1RegionBuild.lean:164`).  So `R` has no boundary at all in the `+vl` direction; its only
`vl`-transverse boundary is the cut line `dot m w = dot m b₀`, crossed by moving `-vl`
(`dot m vl = 1`).  Afill's `not_mem_chainFull_iff` (`L1CoverWedge.lean:646`) is exactly this
split: `w ∉ R ↔ w ∉ wedgeFull B vl u' ∨ dot m w < dot m b₀`.  Hence

* `cutFringe` — the **`vl` side**: window translates that drop below the cut;
* `frontFringe` — the **`u'` side**: window translates that leave `wedgeFull` (fall off the
  `ℕ`-indexed `u'`-sweep).

**Item (2) is refuted, twice over, and the second reason is the one that matters.**

* *Sign* (the failure the dispatch anticipated).  A point of `cutFringe` sits at
  `dot m w ∈ [dot m b₀ - cutWidth, dot m b₀ - 1]` — a *negative* `vl`-offset from the cut.
  `halfStrip B' vl` reaches only `+ℕ • vl` from its base, so covering it needs base points
  *below* the cut: `B` extended backwards, in the dispatch's words.
* *Extent* (fatal for any finite base, backwards extension or not).  `cutFringe` is closed under
  `+ u'` (`cutFringe_add_nsmul_u'`: `dot m u' = 0` keeps the level, `cutBand_ray_u'` keeps
  `k ∈ R`), so `dot (expNormal vl u')` is unbounded above on it; on `halfStrip B' vl` that
  functional is constant along `vl` and bounded by its values on `B'`.  A finite base cannot
  contain a `u'`-ray.  `not_cutFringe_subset_halfStrip` is the theorem; it holds for every finite
  `B'` — including `B` itself with any number of consecutive `vl`-translates inside it — as
  soon as `cutFringe` is nonempty, and `cutFringe_nonempty_iff` says when that is: **exactly
  when some `z ∈ S.erase a` lies below `a` in the `m`-level**, i.e. unless `a` is an
  `m`-minimiser of `S`.  ⚠ Aface's `a` is the argmax of a generic `n` with `0 < dot n vl`
  (`exists_vertex_and_row_order`, `HbaseBridge.lean:1023`), which pushes `a` *up* in the
  `m`-level and makes `cutFringe` as large as it can be.  Reading, not measured (§15): whether
  an `m`-minimising vertex is compatible with `hbot` is Aface's question, not answered here.
  `not_item2_instance` is a concrete instance (finite `B` two `vl`-steps deep, `S` of `vl`-extent
  `1`) certifying the hypotheses of (2) are jointly satisfiable while its conclusion fails —
  so this is a refutation of (2) as stated, not of a strengthening.

The on-chain `B` *is* finite: every `E(𝒮_φ)`-enveloped set is (`L1Sfin.hSfin_of_decompDataZ`,
`SfinBound.lean:49`), and `hcase1`'s `B` is one.  So the refutation applies to the only `B`
the leaf can ever be handed.

**What is true instead, and why it does not help.**  `cutFringe` (minus the `u'` side) is
contained in the chain *re-based* `cutWidth` steps back along `vl`
(`cutFringe_subset_rebased`): `chainFull B vl u' (b₀ - d • vl) 0`.  But the whole picture is
`vl`-translation-invariant (`chainFull_zero_add_zsmul_vl`, `cutFringe_add_zsmul_vl`): the
re-based chain has the *same* fringe one slab lower.  The cut band is not a seed to be
covered once; it is the induction step of Collé's line-by-line extension.  That is a reading
of what the kernel facts below add up to (§15); the theorems themselves are only the
invariance and the containment.

**Item (3).**  The `u'` side is `frontFringe … ⊆ D`; `frontFringe_subset_iff` gives it in binder
form.  Nothing below discharges it, per the dispatch.  `hfringe_of_sides` shows the two sides
together are Aface's `hfringe` verbatim (feed-in term in `tmp/l1claim_receipt.lean`, §27). -/

section Fringe

open Nivat.LE2

variable {B : Set (ℤ × ℤ)} {vl u' b₀ : ℤ × ℤ} {S : Finset (ℤ × ℤ)} {a : ℤ × ℤ}

/-- **The fringe** (item (1), verbatim from the dispatch): window translates of `K` that leave
`K`.  `k + (z - a)` as written there; Aface's `hfringe` writes `z + (k - a)` — `abel`-equal,
see `fringe_subset_iff`. -/
def fringe (K : Set (ℤ × ℤ)) (S : Finset (ℤ × ℤ)) (a : ℤ × ℤ) : Set (ℤ × ℤ) :=
  {w | ∃ k ∈ K, ∃ z ∈ S.erase a, w = k + (z - a)} \ K

/-- `fringe K S a ⊆ D` is exactly Aface's `hfringe` binder
(`HbaseBridge.hwin_of_level_rows`, `HbaseBridge.lean:700`). -/
theorem fringe_subset_iff {K D : Set (ℤ × ℤ)} :
    fringe K S a ⊆ D ↔ ∀ k ∈ K, ∀ z ∈ S.erase a, z + (k - a) ∈ K ∪ D := by
  constructor
  · intro h k hk z hz
    by_cases hw : z + (k - a) ∈ K
    · exact Or.inl hw
    · exact Or.inr (h ⟨⟨k, hk, z, hz, by abel⟩, hw⟩)
  · rintro h w ⟨⟨k, hk, z, hz, rfl⟩, hw⟩
    have := h k hk z hz
    rw [show z + (k - a) = k + (z - a) by abel] at this
    exact this.resolve_left hw

/-- The **`vl` side** of the fringe of `chainFull B vl u' b₀ 0`: translates that drop below
the cut `dot (expNormal u' vl) · = dot (expNormal u' vl) b₀`. -/
noncomputable def cutFringe (B : Set (ℤ × ℤ)) (vl u' b₀ : ℤ × ℤ) (S : Finset (ℤ × ℤ))
    (a : ℤ × ℤ) : Set (ℤ × ℤ) :=
  {w | w ∈ fringe (chainFull B vl u' b₀ 0) S a ∧
    dot (expNormal u' vl) w < dot (expNormal u' vl) b₀}

/-- The **`u'` side** of the fringe of `chainFull B vl u' b₀ 0`: translates that leave
`wedgeFull B vl u'` itself.  **Named, not discharged** (item (3)). -/
noncomputable def frontFringe (B : Set (ℤ × ℤ)) (vl u' b₀ : ℤ × ℤ) (S : Finset (ℤ × ℤ))
    (a : ℤ × ℤ) : Set (ℤ × ℤ) :=
  {w | w ∈ fringe (chainFull B vl u' b₀ 0) S a ∧ w ∉ wedgeFull B vl u'}

/-- The two sides exhaust the fringe (Afill's `not_mem_chainFull_iff`, `L1CoverWedge.lean:646`).
Not disjoint: a translate may fail both ways at once. -/
theorem fringe_chainFull_eq (B : Set (ℤ × ℤ)) (vl u' b₀ : ℤ × ℤ) (S : Finset (ℤ × ℤ))
    (a : ℤ × ℤ) :
    fringe (chainFull B vl u' b₀ 0) S a =
      cutFringe B vl u' b₀ S a ∪ frontFringe B vl u' b₀ S a := by
  ext w
  constructor
  · intro hw
    rcases not_mem_chainFull_iff.mp hw.2 with h | h
    · exact Or.inr ⟨hw, h⟩
    · exact Or.inl ⟨hw, by simpa [expLevel] using h⟩
  · rintro (h | h) <;> exact h.1

/-- **Both sides in `D` give Aface's `hfringe` verbatim.**  This is the shape
`HbaseBridge.exists_enum_hwin_hK` (`HbaseBridge.lean:1000`) takes. -/
theorem hfringe_of_sides {D : Set (ℤ × ℤ)}
    (hcut : cutFringe B vl u' b₀ S a ⊆ D) (hfront : frontFringe B vl u' b₀ S a ⊆ D) :
    ∀ k ∈ chainFull B vl u' b₀ 0, ∀ z ∈ S.erase a,
      z + (k - a) ∈ chainFull B vl u' b₀ 0 ∪ D := by
  rw [← fringe_subset_iff, fringe_chainFull_eq]
  exact Set.union_subset hcut hfront

/-- **Item (3), binder form.**  The `u'`-side hypothesis, unfolded: every window translate of
a chain point that falls off the `u'`-sweep lies in `D`.  (Leaving `wedgeFull` already implies
leaving the chain, so the fringe clause is redundant and dropped.) -/
theorem frontFringe_subset_iff {D : Set (ℤ × ℤ)} :
    frontFringe B vl u' b₀ S a ⊆ D ↔
      ∀ k ∈ chainFull B vl u' b₀ 0, ∀ z ∈ S.erase a,
        k + (z - a) ∉ wedgeFull B vl u' → k + (z - a) ∈ D := by
  constructor
  · intro h k hk z hz hnw
    exact h ⟨⟨⟨k, hk, z, hz, rfl⟩, fun hm => hnw hm.1⟩, hnw⟩
  · rintro h w ⟨⟨⟨k, hk, z, hz, rfl⟩, -⟩, hnw⟩
    exact h k hk z hz hnw

/-- The `vl`-side hypothesis, unfolded the same way. -/
theorem cutFringe_subset_iff {D : Set (ℤ × ℤ)} :
    cutFringe B vl u' b₀ S a ⊆ D ↔
      ∀ k ∈ chainFull B vl u' b₀ 0, ∀ z ∈ S.erase a,
        dot (expNormal u' vl) (k + (z - a)) < dot (expNormal u' vl) b₀ →
          k + (z - a) ∈ D := by
  constructor
  · intro h k hk z hz hlt
    refine h ⟨⟨⟨k, hk, z, hz, rfl⟩, ?_⟩, hlt⟩
    intro hm
    have h2 : expLevel u' vl b₀ 0 ≤ dot (expNormal u' vl) (k + (z - a)) := hm.2
    simp only [expLevel, Nat.cast_zero, sub_zero] at h2
    omega
  · rintro h w ⟨⟨⟨k, hk, z, hz, rfl⟩, -⟩, hlt⟩
    exact h k hk z hz hlt

/-- **The `vl` side is a `u'`-ray-closed set.**  `dot (expNormal u' vl) u' = 0` keeps the level;
`HbaseBridge.cutBand_ray_u'` keeps the chain point in the chain. -/
theorem cutFringe_add_nsmul_u' (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    {w : ℤ × ℤ} (hw : w ∈ cutFringe B vl u' b₀ S a) (i : ℕ) :
    w + (i : ℤ) • u' ∈ cutFringe B vl u' b₀ S a := by
  obtain ⟨⟨⟨k, hk, z, hz, rfl⟩, -⟩, hlt⟩ := hw
  have hmu' : dot (expNormal u' vl) u' = 0 := dot_expNormal_u'
  have hdot : dot (expNormal u' vl) (k + (z - a) + (i : ℤ) • u')
      = dot (expNormal u' vl) (k + (z - a)) := by
    rw [dot_add, dot_smul_right, hmu', mul_zero, add_zero]
  refine ⟨⟨⟨k + (i : ℤ) • u', (Nivat.HbaseBridge.cutBand_ray_u' hunimod hk i).1, z, hz,
    by abel⟩, ?_⟩, by rw [hdot]; exact hlt⟩
  intro hm
  have h2 : expLevel u' vl b₀ 0 ≤ dot (expNormal u' vl) (k + (z - a) + (i : ℤ) • u') := hm.2
  simp only [expLevel, Nat.cast_zero, sub_zero] at h2
  rw [hdot] at h2
  omega

/-- **When the `vl` side is nonempty**: exactly when some `z ∈ S.erase a` sits below `a` in
the `expNormal u' vl`-level.  The witness is the translate of `b₀` itself. -/
theorem cutFringe_nonempty_iff (hb₀ : b₀ ∈ B) :
    (cutFringe B vl u' b₀ S a).Nonempty ↔
      ∃ z ∈ S.erase a, dot (expNormal u' vl) z < dot (expNormal u' vl) a := by
  constructor
  · rintro ⟨w, ⟨⟨k, hk, z, hz, rfl⟩, -⟩, hlt⟩
    refine ⟨z, hz, ?_⟩
    have hk2 : expLevel u' vl b₀ 0 ≤ dot (expNormal u' vl) k := hk.2
    simp only [expLevel, Nat.cast_zero, sub_zero] at hk2
    rw [dot_add, dot_sub] at hlt
    omega
  · rintro ⟨z, hz, hlt⟩
    have hb₀K : b₀ ∈ chainFull B vl u' b₀ 0 := by
      refine ⟨⟨b₀, mem_fullSweep_iff.mpr ⟨b₀, hb₀, 0, by simp⟩, 0, by simp⟩, ?_⟩
      show expLevel u' vl b₀ 0 ≤ dot (expNormal u' vl) b₀
      simp [expLevel]
    refine ⟨b₀ + (z - a), ⟨⟨b₀, hb₀K, z, hz, rfl⟩, ?_⟩, ?_⟩
    · intro hm
      have h2 : expLevel u' vl b₀ 0 ≤ dot (expNormal u' vl) (b₀ + (z - a)) := hm.2
      simp only [expLevel, Nat.cast_zero, sub_zero, dot_add, dot_sub] at h2
      omega
    · rw [dot_add, dot_sub]; omega

/-- `dot (expNormal vl u')` is bounded above on a `vl`-half-strip over a finite base: it is
constant along `vl` (`dot (expNormal vl u') vl = 0`). -/
theorem exists_bound_halfStrip {B' : Set (ℤ × ℤ)} (hfin : B'.Finite) :
    ∃ M : ℤ, ∀ w ∈ Nivat.LE2.halfStrip B' vl, dot (expNormal vl u') w ≤ M := by
  obtain ⟨M, hM⟩ := (hfin.image (dot (expNormal vl u'))).bddAbove
  refine ⟨M, ?_⟩
  rintro _ ⟨b, hb, t, rfl⟩
  have hm'vl : dot (expNormal vl u') vl = 0 := dot_expNormal_u'
  rw [dot_add, dot_smul_right, hm'vl, mul_zero, add_zero]
  exact hM (Set.mem_image_of_mem _ hb)

/-- **Item (2), refuted for every finite base.**  A nonempty `vl` side is never inside a
`vl`-half-strip over a finite base — whatever the base, however deep along `vl`. -/
theorem not_cutFringe_subset_halfStrip (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    {B' : Set (ℤ × ℤ)} (hfin : B'.Finite) (hne : (cutFringe B vl u' b₀ S a).Nonempty) :
    ¬ cutFringe B vl u' b₀ S a ⊆ Nivat.LE2.halfStrip B' vl := by
  intro hsub
  obtain ⟨w, hw⟩ := hne
  obtain ⟨M, hM⟩ := exists_bound_halfStrip (vl := vl) (u' := u') hfin
  have hm'u' : dot (expNormal vl u') u' = 1 :=
    dot_expNormal_vl (Nivat.HbaseBridge.det_swap hunimod)
  have hval : ∀ i : ℕ, dot (expNormal vl u') w + (i : ℤ) ≤ M := by
    intro i
    have := hM _ (hsub (cutFringe_add_nsmul_u' hunimod hw i))
    rwa [dot_add, dot_smul_right, hm'u', mul_one] at this
  have hnn : 0 ≤ M - dot (expNormal vl u') w + 1 := by have := hval 0; omega
  have := hval (M - dot (expNormal vl u') w + 1).toNat
  rw [Int.toNat_of_nonneg hnn] at this
  omega

/-- **Item (2) fails as stated, on a concrete instance.**  `vl = (1,0)`, `u' = (0,1)`,
`B = {(0,0), (1,0)}` (two consecutive `vl`-translates of `b = (0,0)`, i.e. `d = 1`),
`S = {(0,0), (-1,0)}`, `a = b₀ = (0,0)` (so `S` has `vl`-extent `1 = d`).  All hypotheses of
(2) hold — the first two conjuncts — and its conclusion fails — the third. -/
theorem not_item2_instance :
    (∀ t : ℕ, t ≤ 1 → ((0 : ℤ), (0 : ℤ)) + (t : ℤ) • ((1 : ℤ), (0 : ℤ)) ∈
        (↑({((0 : ℤ), (0 : ℤ)), ((1 : ℤ), (0 : ℤ))} : Finset (ℤ × ℤ)) : Set (ℤ × ℤ))) ∧
    (∀ z ∈ ({((0 : ℤ), (0 : ℤ)), ((-1 : ℤ), (0 : ℤ))} : Finset (ℤ × ℤ)),
        (dot (expNormal ((0 : ℤ), (1 : ℤ)) ((1 : ℤ), (0 : ℤ))) (z - ((0 : ℤ), (0 : ℤ)))).natAbs
          ≤ 1) ∧
    ¬ cutFringe (↑({((0 : ℤ), (0 : ℤ)), ((1 : ℤ), (0 : ℤ))} : Finset (ℤ × ℤ)))
        ((1 : ℤ), (0 : ℤ)) ((0 : ℤ), (1 : ℤ)) ((0 : ℤ), (0 : ℤ))
        ({((0 : ℤ), (0 : ℤ)), ((-1 : ℤ), (0 : ℤ))} : Finset (ℤ × ℤ)) ((0 : ℤ), (0 : ℤ))
      ⊆ Nivat.LE2.halfStrip
          (↑({((0 : ℤ), (0 : ℤ)), ((1 : ℤ), (0 : ℤ))} : Finset (ℤ × ℤ))) ((1 : ℤ), (0 : ℤ)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    interval_cases t <;> simp
  · simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro z (rfl | rfl) <;> norm_num [expNormal, Nivat.det, Nivat.LE2.dot]
  · refine not_cutFringe_subset_halfStrip (by right; norm_num [Nivat.det])
      (Finset.finite_toSet _) ?_
    rw [cutFringe_nonempty_iff (by simp)]
    exact ⟨((-1 : ℤ), (0 : ℤ)), by simp, by norm_num [expNormal, Nivat.det, Nivat.LE2.dot]⟩

/-- **`vl`-translation invariance of the chain**: shifting the base point shifts the chain. -/
theorem chainFull_zero_add_zsmul_vl (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    {w : ℤ × ℤ} (hw : w ∈ chainFull B vl u' b₀ 0) (s : ℤ) :
    w + s • vl ∈ chainFull B vl u' (b₀ + s • vl) 0 := by
  obtain ⟨b, hb, s', t, rfl⟩ := Nivat.HbaseBridge.rep_of_mem_chainFull_zero hw
  have hk2 : expLevel u' vl b₀ 0
      ≤ dot (expNormal u' vl) (b + s' • vl + (t : ℤ) • u') := hw.2
  have hmvl : dot (expNormal u' vl) vl = 1 := dot_expNormal_vl hunimod
  have hmu' : dot (expNormal u' vl) u' = 0 := dot_expNormal_u'
  rw [show b + s' • vl + (t : ℤ) • u' + s • vl = b + (s' + s) • vl + (t : ℤ) • u' by module]
  refine Nivat.HbaseBridge.mem_chainFull_zero_of_rep hb (s' + s) t ?_
  simp only [expLevel, Nat.cast_zero, sub_zero, dot_add, dot_smul_right, hmvl, hmu', mul_one,
    mul_zero, add_zero] at hk2 ⊢
  omega

/-- **The `vl` side moves with the cut.**  Re-basing the chain along `vl` re-bases its `vl`-side
fringe by the same shift: the cut band is invariant, not absorbable. -/
theorem cutFringe_add_zsmul_vl (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    {w : ℤ × ℤ} (hw : w ∈ cutFringe B vl u' b₀ S a) (s : ℤ) :
    w + s • vl ∈ cutFringe B vl u' (b₀ + s • vl) S a := by
  obtain ⟨⟨⟨k, hk, z, hz, rfl⟩, hnot⟩, hlt⟩ := hw
  have hmvl : dot (expNormal u' vl) vl = 1 := dot_expNormal_vl hunimod
  refine ⟨⟨⟨k + s • vl, chainFull_zero_add_zsmul_vl hunimod hk s, z, hz, by abel⟩, ?_⟩, ?_⟩
  · intro hm
    apply hnot
    have := chainFull_zero_add_zsmul_vl hunimod hm (-s)
    simpa only [neg_smul, add_neg_cancel_right] using this
  · simp only [dot_add, dot_smul_right, hmvl, mul_one] at hlt ⊢
    omega

/-- **What is true instead of item (2)**: away from the `u'` side, the `vl`-side fringe lies in
the chain re-based `d ≥ cutWidth` steps back along `vl`.  ⚠ Feeding that chain to `ofWedgeAt`
needs `b₀ - d • vl ∈ B` (its `hb₀`), i.e. `B` extended *backwards* — and by
`cutFringe_add_zsmul_vl` the re-based chain has the same fringe one slab lower. -/
theorem cutFringe_subset_rebased (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    {d : ℕ} (hd : Nivat.HbaseBridge.cutWidth S a u' vl ≤ d) :
    cutFringe B vl u' b₀ S a ⊆
      chainFull B vl u' (b₀ - (d : ℤ) • vl) 0 ∪ frontFringe B vl u' b₀ S a := by
  rintro w ⟨hwf, hlt⟩
  by_cases hwedge : w ∈ wedgeFull B vl u'
  · left
    obtain ⟨⟨k, hk, z, hz, rfl⟩, -⟩ := hwf
    refine ⟨hwedge, ?_⟩
    show expLevel u' vl (b₀ - (d : ℤ) • vl) 0 ≤ dot (expNormal u' vl) (k + (z - a))
    have hk2 : expLevel u' vl b₀ 0 ≤ dot (expNormal u' vl) k := hk.2
    have hβ := Nivat.HbaseBridge.neg_cutWidth_le (u' := u') (vl := vl) hz
    have hmvl : dot (expNormal u' vl) vl = 1 := dot_expNormal_vl hunimod
    have hd' : (Nivat.HbaseBridge.cutWidth S a u' vl : ℤ) ≤ d := by exact_mod_cast hd
    simp only [expLevel, Nat.cast_zero, sub_zero, dot_add, dot_sub, dot_smul_right, hmvl,
      mul_one] at hk2 hβ ⊢
    omega
  · exact Or.inr ⟨hwf, hwedge⟩

end Fringe


/-! ## §5. Route A: the region's convexity as a binder, `hlev` gone (2026-09-19, team-lead's
dispatch after `OPEN.md #10` and L1B's `isLatticeConvexRegion_wedgeFull_of_unimod`)

`hlev` entered the leaf only through `isRegion_wedgeFull` (`L1RegionBuild.lean:271`), which is
the `isRegion` component of the `RegionFamily` built by `ofWedgeAt`.  Nothing else in
`exists_L1MaxBResidual_of_wedgeAt` consumes `hlev`, `hB`, or `hEnv` — measured, not read:
`ofWedgeAtConvex` below is `ofWedgeAt` with `IsLatticeConvexRegion (wedgeFull B vl u')` taken as
a binder, and `exists_L1MaxBResidual_of_convex_split` elaborates with those three binders
deleted.  L1B's `L1Data.isLatticeConvexRegion_wedgeFull_of_unimod` (`L1LevelSpan.lean:811`)
then pays that binder from `hunimod` alone (no finiteness, no nonemptiness, either
orientation), so `exists_L1MaxBResidual_of_unimod_split` carries **no shape hypothesis on `B`**
except `hb₀ : b₀ ∈ B`.

§14: `exists_L1MaxBResidual_of_wedgeAt_split` and `WedgeResidual` are kept as they were;
`exists_L1MaxBResidual_of_wedgeAt_split'` and `WedgeResidualR.ofWedgeResidual` are the
receipts that the old route is a corollary of the new one.

`sorry TOTAL` is unchanged by this section (hard rule 1): the obligation `hlev` did not get
discharged, it turned out never to have been needed. -/

section RouteA

noncomputable def ofWedgeAtConvex {e u' b₀ : ℤ × ℤ} {c : ℤ} {B : Set (ℤ × ℤ)}
    (hb₀ : b₀ ∈ B) (hconv : IsLatticeConvexRegion (wedgeFull B vl u'))
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) (k : ℕ)
    (hbase : PeriodOn (T e ξ) (chainFull B vl u' b₀ k) (c • vl))
    (hinf : ¬ PeriodOn (T e ξ) (wedgeFull B vl u') (c • vl)) :
    Nivat.L1Region.RegionFamily (T e ξ) vl u' c :=
  have hb' : b₀ ∈ wedgeFull B vl u' :=
    ⟨b₀, mem_fullSweep_iff.mpr ⟨b₀, hb₀, 0, by simp⟩, 0, by simp⟩
  have hreg : Colle41.IsRegion (wedgeFull B vl u') vl u' :=
    ⟨hconv, ⟨b₀, rayIn_wedgeFull_left hb'⟩, ⟨b₀, rayIn_wedgeFull_right hb'⟩⟩
  Nivat.HalfPlaneFamily.ofSomeIndex k
    (Nivat.L1Region.cut_ssubset (expLevel_antitone u' vl b₀) (expLevel_gap hb₀ hunimod))
    (Nivat.L1Region.isRegion_cut hreg dot_expNormal_u'
      (by rw [dot_expNormal_vl hunimod]; exact one_pos) (expLevel u' vl b₀))
    hbase
    (by rw [Nivat.L1Region.iUnion_cut (expLevel_exhaustive u' vl b₀)]; exact hinf)

theorem ofWedgeAtConvex_R {e u' b₀ : ℤ × ℤ} {c : ℤ} {B : Set (ℤ × ℤ)}
    (hb₀ : b₀ ∈ B) (hconv : IsLatticeConvexRegion (wedgeFull B vl u'))
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) (k : ℕ)
    (hbase : PeriodOn (T e ξ) (chainFull B vl u' b₀ k) (c • vl))
    (hinf : ¬ PeriodOn (T e ξ) (wedgeFull B vl u') (c • vl)) (n : ℕ) :
    (ofWedgeAtConvex hb₀ hconv hunimod k hbase hinf).R n = chainFull B vl u' b₀ (k + n) :=
  rfl

theorem exists_L1MaxBResidual_of_convex_split
    (hξ : IsMinimalCounterexample ξ) (d : Nivat.Colle35.DecompDataZ ξ)
    (hℓ_nel : ℓ ∈ Colle45.NonExpansiveLine ξ)
    (hℓ_neg : Colle45.IsOneSidedNonexpansive ξ (-ℓ))
    (hSgen : Nivat.Colle.IsGeneratingSet ξ S)
    (hvl_prim : Primitive vl) (hdet_ℓ : Nivat.LE2.dot ℓ vl = 0)
    {e u' v b₀ : ℤ × ℤ} {c : ℤ} (ε : Bool) {B : Set (ℤ × ℤ)}
    (hb₀ : b₀ ∈ B) (hconv : IsLatticeConvexRegion (wedgeFull B vl u'))
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) (c0 : c ≠ 0) (k : ℕ)
    (hbase : PeriodOn (T e ξ) (chainFull B vl u' b₀ k) (c • vl))
    (hline : ∀ N : ℕ, PeriodOn (T e ξ) (chainFull B vl u' b₀ (k + N)) (c • vl) →
      ¬ PeriodOn (T e ξ) (chainFull B vl u' b₀ (k + (N + 1))) (c • vl) →
      ∃ τ : ℤ, ∀ z ∈ derivedQ ε u' (S.image (· + v)),
        τ • u' + z ∈ chainFull B vl u' b₀ (k + N) ∧
        τ • u' + z + c • vl ∈ chainFull B vl u' b₀ (k + N))
    (hstraddle : ∀ N : ℕ, PeriodOn (T e ξ) (chainFull B vl u' b₀ (k + N)) (c • vl) →
      ¬ PeriodOn (T e ξ) (chainFull B vl u' b₀ (k + (N + 1))) (c • vl) →
      ∀ τ : ℤ,
        (∀ z ∈ derivedQ ε u' (S.image (· + v)),
          τ • u' + z ∈ chainFull B vl u' b₀ (k + N) ∧
          τ • u' + z + c • vl ∈ chainFull B vl u' b₀ (k + N)) →
        Nivat.L1Region.Straddle (T e ξ) (chainFull B vl u' b₀ (k + N))
          (chainFull B vl u' b₀ (k + (N + 1))) (S.image (· + v))
          (derivedQ ε u' (S.image (· + v))) vl u' c τ) :
    ∃ (e u u' v : ℤ × ℤ) (c τ : ℤ) (ε : Bool) (S₁ : Finset (ℤ × ℤ))
      (F : Nivat.L1Region.RegionFamily (T e ξ) u u' c),
      S₁ = S.image (· + v) ∧
      Nivat.ColleReg.L1Data.MaxBResidual (ξ := ξ) ε u u' c τ S₁ F := by
  have hu' : Primitive u' := by
    show IsCoprime u'.1 u'.2
    rcases hunimod with h | h
    · exact ⟨vl.2, -vl.1, by simp only [det] at h; linear_combination h⟩
    · exact ⟨-vl.2, vl.1, by simp only [det] at h; linear_combination -h⟩
  have hinf : ¬ PeriodOn (T e ξ) (wedgeFull B vl u') (c • vl) :=
    hinf_of_ge e hξ d hb₀ hunimod (smul_ne_zero c0 hvl_prim.ne_zero)
  let F : Nivat.L1Region.RegionFamily (T e ξ) vl u' c :=
    ofWedgeAtConvex hb₀ hconv hunimod k hbase hinf
  have hR : ∀ n, F.R n = chainFull B vl u' b₀ (k + n) := fun _ => rfl
  obtain ⟨N, hN, hN1⟩ :=
    Nivat.L1Region.exists_greatest_periodOn F.monotone F.base F.union_not
  obtain ⟨τ, hl⟩ := hline N (by rw [← hR]; exact hN) (by rw [← hR]; exact hN1)
  exact exists_L1MaxBResidual_of_tail hℓ_nel hℓ_neg hSgen hvl_prim hdet_ℓ ε
    (det_ne_zero_of_unimod hunimod) hu' c0 F N hN hN1
    (by rw [hR]; exact hl)
    (by rw [hR, hR]; exact hstraddle N (by rw [← hR]; exact hN) (by rw [← hR]; exact hN1) τ hl)

/-- §14 receipt: the old split theorem is a corollary of the new one. -/
theorem exists_L1MaxBResidual_of_wedgeAt_split'
    (hξ : IsMinimalCounterexample ξ) (d : Nivat.Colle35.DecompDataZ ξ)
    (hℓ_nel : ℓ ∈ Colle45.NonExpansiveLine ξ)
    (hℓ_neg : Colle45.IsOneSidedNonexpansive ξ (-ℓ))
    (hSgen : Nivat.Colle.IsGeneratingSet ξ S)
    (hvl_prim : Primitive vl) (hdet_ℓ : Nivat.LE2.dot ℓ vl = 0)
    {e u' v b₀ : ℤ × ℤ} {c : ℤ} (ε : Bool) {U B : Set (ℤ × ℤ)}
    (hEnv : Nivat.LE2.EnvOf U B) (hb₀ : b₀ ∈ B)
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) (c0 : c ≠ 0)
    (hlev : Nivat.RegionSweep.LevelInterval B vl) (k : ℕ)
    (hbase : PeriodOn (T e ξ) (chainFull B vl u' b₀ k) (c • vl))
    (hline : ∀ N : ℕ, PeriodOn (T e ξ) (chainFull B vl u' b₀ (k + N)) (c • vl) →
      ¬ PeriodOn (T e ξ) (chainFull B vl u' b₀ (k + (N + 1))) (c • vl) →
      ∃ τ : ℤ, ∀ z ∈ derivedQ ε u' (S.image (· + v)),
        τ • u' + z ∈ chainFull B vl u' b₀ (k + N) ∧
        τ • u' + z + c • vl ∈ chainFull B vl u' b₀ (k + N))
    (hstraddle : ∀ N : ℕ, PeriodOn (T e ξ) (chainFull B vl u' b₀ (k + N)) (c • vl) →
      ¬ PeriodOn (T e ξ) (chainFull B vl u' b₀ (k + (N + 1))) (c • vl) →
      ∀ τ : ℤ,
        (∀ z ∈ derivedQ ε u' (S.image (· + v)),
          τ • u' + z ∈ chainFull B vl u' b₀ (k + N) ∧
          τ • u' + z + c • vl ∈ chainFull B vl u' b₀ (k + N)) →
        Nivat.L1Region.Straddle (T e ξ) (chainFull B vl u' b₀ (k + N))
          (chainFull B vl u' b₀ (k + (N + 1))) (S.image (· + v))
          (derivedQ ε u' (S.image (· + v))) vl u' c τ) :
    ∃ (e u u' v : ℤ × ℤ) (c τ : ℤ) (ε : Bool) (S₁ : Finset (ℤ × ℤ))
      (F : Nivat.L1Region.RegionFamily (T e ξ) u u' c),
      S₁ = S.image (· + v) ∧
      Nivat.ColleReg.L1Data.MaxBResidual (ξ := ξ) ε u u' c τ S₁ F := by
  have hu' : Primitive u' := by
    show IsCoprime u'.1 u'.2
    rcases hunimod with h | h
    · exact ⟨vl.2, -vl.1, by simp only [det] at h; linear_combination h⟩
    · exact ⟨-vl.2, vl.1, by simp only [det] at h; linear_combination -h⟩
  exact exists_L1MaxBResidual_of_convex_split hξ d hℓ_nel hℓ_neg hSgen hvl_prim hdet_ℓ ε hb₀
    (isLatticeConvexRegion_wedgeFull (isLatticeConvexRegion_of_envOf hEnv) hvl_prim hu' hlev
      hunimod)
    hunimod c0 k hbase hline hstraddle

structure WedgeResidualR (ξ : Config ℤ) (S : Finset (ℤ × ℤ)) (vl : ℤ × ℤ) where
  e : ℤ × ℤ
  u' : ℤ × ℤ
  v : ℤ × ℤ
  b₀ : ℤ × ℤ
  c : ℤ
  ε : Bool
  B : Set (ℤ × ℤ)
  k : ℕ
  hb₀ : b₀ ∈ B
  hunimod : det u' vl = 1 ∨ det u' vl = -1
  c0 : c ≠ 0
  hconv : IsLatticeConvexRegion (wedgeFull B vl u')
  hbase : PeriodOn (T e ξ) (chainFull B vl u' b₀ k) (c • vl)
  hline : ∀ N : ℕ, PeriodOn (T e ξ) (chainFull B vl u' b₀ (k + N)) (c • vl) →
    ¬ PeriodOn (T e ξ) (chainFull B vl u' b₀ (k + (N + 1))) (c • vl) →
    ∃ τ : ℤ, ∀ z ∈ derivedQ ε u' (S.image (· + v)),
      τ • u' + z ∈ chainFull B vl u' b₀ (k + N) ∧
      τ • u' + z + c • vl ∈ chainFull B vl u' b₀ (k + N)
  hstraddle : ∀ N : ℕ, PeriodOn (T e ξ) (chainFull B vl u' b₀ (k + N)) (c • vl) →
    ¬ PeriodOn (T e ξ) (chainFull B vl u' b₀ (k + (N + 1))) (c • vl) →
    ∀ τ : ℤ,
      (∀ z ∈ derivedQ ε u' (S.image (· + v)),
        τ • u' + z ∈ chainFull B vl u' b₀ (k + N) ∧
        τ • u' + z + c • vl ∈ chainFull B vl u' b₀ (k + N)) →
      Nivat.L1Region.Straddle (T e ξ) (chainFull B vl u' b₀ (k + N))
        (chainFull B vl u' b₀ (k + (N + 1))) (S.image (· + v))
        (derivedQ ε u' (S.image (· + v))) vl u' c τ

theorem exists_L1MaxBResidual_of_wedgeResidualR
    (hξ : IsMinimalCounterexample ξ) (d : Nivat.Colle35.DecompDataZ ξ)
    (hℓ_nel : ℓ ∈ Colle45.NonExpansiveLine ξ)
    (hℓ_neg : Colle45.IsOneSidedNonexpansive ξ (-ℓ))
    (hSgen : Nivat.Colle.IsGeneratingSet ξ S)
    (hvl_prim : Primitive vl) (hdet_ℓ : Nivat.LE2.dot ℓ vl = 0)
    (r : WedgeResidualR ξ S vl) :
    ∃ (e u u' v : ℤ × ℤ) (c τ : ℤ) (ε : Bool) (S₁ : Finset (ℤ × ℤ))
      (F : Nivat.L1Region.RegionFamily (T e ξ) u u' c),
      S₁ = S.image (· + v) ∧
      Nivat.ColleReg.L1Data.MaxBResidual (ξ := ξ) ε u u' c τ S₁ F :=
  exists_L1MaxBResidual_of_convex_split hξ d hℓ_nel hℓ_neg hSgen hvl_prim hdet_ℓ r.ε
    r.hb₀ r.hconv r.hunimod r.c0 r.k r.hbase r.hline r.hstraddle

/-! ## §5  `CutResidualR` — the same residual in **Collé's own** stage-2 frame

原文：`b3_colle2.txt:806-856`.  `WedgeResidualR` above encodes stage 2 as the quadrant
`chainFull B vl u₂ b₀ k`; `OPEN.md #21` records the measurement that this is the paper's
`𝓡^n_I` **only at the top of the tower**:

* `chainFull B vl u' b₀ k = wedgeFull B vl u' ∩ {dot (expNormal u' vl) · ≥ lev k}` has its cut
  lines parallel to `u'` and its level measured along `vl`, so raising `k` exposes new layers
  in the direction `-vl`;
* `:818`'s `𝓡^n_I` has its cut lines parallel to `ℓ' = ℓ_I` and grows along `v⃗_{ℓ_{I-1}}`.

Under the dictionary "our `u'` ↔ paper `v⃗_{ℓ_I}`, our `-vl` ↔ paper `v⃗_{ℓ_{I-1}}`" the two
agree exactly when `I = ι-m+1`, i.e. at the top of the tower `:812`; `:814` picks `I` by
minimality and says nothing of the sort.  So `WedgeResidualR` is **strictly stronger** than
what `:806-856` delivers whenever `m ≥ 3` and `I > ι-m+1` (hard rule 7: 比原文强 = 债).

`CutResidualR` below is the paper's own data instead, and it is assembled by the existing,
kernel-clean `Nivat.L1Region.ofCut` (`L1Region.lean:240`) — the abstract half-plane slicing
that was written for `:816` and has been sitting without a producer.

**Two hypotheses `WedgeResidualR` carries and this one does not**, both artifacts of the
quadrant encoding:

* `hunimod : det u' vl = ±1`.  `u' := v⃗_{ℓ_I}` is a **primitive edge direction** (`:816`),
  which gives `Primitive u'` and `det vl u' ≠ 0`; unimodularity is a property of the *pair*
  and the paper never asserts it for `(vl, v⃗_{ℓ_I})`.
* the corner clause `∀ b ∈ 𝒮_φ, 0 ≤ ⟪expNormal u' vl, b - a⟫ ∧ 0 ≤ uCoord u' vl a b`.
  Claim 4.7 (`:824`) places `𝒯` by `𝒯 ∖ ℓ'_𝒯 ⊂ 𝓡^N_I`, `𝒯 ⊄ 𝓡^N_I` — a *placement*, not a
  corner; `CornerAdjClash.det_eq_zero_of_adj_of_corner` is what killed the corner version in
  stage 1's frame and it never applied to this one. -/

/-- **Collé's stage-2 data** (`b3_colle2.txt:806-856`), field by field.

* `e` — the translate: everything in `:778-856` is about `T^u η`, here `T e ξ`.
* `u'` — `v⃗_{ℓ_I}` (`:816`, `ℓ_I = ℓ'`), the direction of the cutting line.
* `v` — the translation of `𝒮` in Claim 4.7 (`:824`, "any translation `𝒯` of `𝒮`"); `S₁` is
  `S.image (· + v)`.
* `m` — an integer normal of `ℓ'`, so `dist(·, ℓ'_{𝓡_I})` of `:818` is `dot m ·` up to sign.
* `c` — `h = c • vl` is the period of `:806` ("a period for `(T^u η)|𝓡_{ι-1}` parallel to `ℓ`").
* `τ` — the `t₀ ∈ ℤ₊` of `:826`.
* `Rinf` — `𝓡_{I-1}` (`:808` at `i = I-1`), the union of the family (`:820`).
* `lev` — `-d_n` (`:816`: `0 = d₀ < d₁ < ⋯`, the **attained** distances).
* `Sφ`, `a`, `hgen` — the generating set behind Figure 11(B)'s cover (`:848-856`).
-/
structure CutResidualR (ξ : Config ℤ) (S : Finset (ℤ × ℤ)) (vl : ℤ × ℤ) where
  e : ℤ × ℤ
  u' : ℤ × ℤ
  v : ℤ × ℤ
  m : ℤ × ℤ
  c : ℤ
  τ : ℤ
  ε : Bool
  Rinf : Set (ℤ × ℤ)
  lev : ℕ → ℤ
  Sφ : Finset (ℤ × ℤ)
  a : ℤ × ℤ
  /-- `:848-856`, Figure 11(B): the cover is taken inside the generated closure of `𝒮_φ`. -/
  hgen : Nivat.Colle.GeneratesAt ξ Sφ a
  /-- `v⃗_{ℓ_I}` is not parallel to `ℓ` (`:816`: `ℓ_I ≠ ℓ` because `I ≤ ι-1`). -/
  det' : det vl u' ≠ 0
  /-- `:816`, `v⃗_{ℓ_I}` is an edge direction, hence primitive. -/
  prim : Primitive u'
  /-- `h = c • vl` is a period, so `c ≠ 0` (`:806`). -/
  c0 : c ≠ 0
  /-- `:808` — `𝓡_{I-1}` is a `(-ℓ, ℓ_{I-1})`-region (Definition 3.1, `:386`), read here in the
  two ray directions `vl` and `u'`. -/
  hR : Colle41.IsRegion Rinf vl u'
  /-- The cutting line of `:818` runs along `ℓ' = ℓ_I`, i.e. along `u'`. -/
  hmu' : Nivat.LE2.dot m u' = 0
  /-- The family grows in the direction in which `vl` raises the level (`:818`, `t ∈ ℤ₊`). -/
  hmu : 0 < Nivat.LE2.dot m vl
  /-- `d_n` increases, so `lev = -d_n` decreases (`:816`). -/
  hlev : Antitone lev
  /-- `⋃_n 𝓡^n_I = 𝓡_{I-1}` (`:820`): the `d_n` are unbounded. -/
  hexh : ∀ b : ℤ, ∃ n, lev n ≤ b
  /-- The `d_n` are the distances that are **attained** (`:816`), which is what makes each
  inclusion `𝓡^n_I ⊂ 𝓡^{n+1}_I` strict. -/
  hgap : ∀ n, ∃ z ∈ Rinf, lev (n + 1) ≤ Nivat.LE2.dot m z ∧ Nivat.LE2.dot m z < lev n
  /-- `𝓡^0_I = 𝓡_I` is `h`-periodic — this is the defining property of `I` (`:814`). -/
  hbase : PeriodOn (T e ξ) (Nivat.L1Region.cut Rinf m lev 0) (c • vl)
  /-- `I` is the **smallest** such index (`:814`), so `𝓡_{I-1}` is not `h`-periodic. -/
  hinf : ¬ PeriodOn (T e ξ) Rinf (c • vl)
  /-- Claim 4.7's placement at the maximal index (`:820`, `:824`): the translate's non-edge
  part sits inside `𝓡^N_I`, together with its `h`-shift. -/
  hline : ∀ N : ℕ,
    PeriodOn (T e ξ) (Nivat.L1Region.cut Rinf m lev N) (c • vl) →
    ¬ PeriodOn (T e ξ) (Nivat.L1Region.cut Rinf m lev (N + 1)) (c • vl) →
    ∀ z ∈ derivedQ ε u' (S.image (· + v)),
      τ • u' + z ∈ Nivat.L1Region.cut Rinf m lev N ∧
      τ • u' + z + c • vl ∈ Nivat.L1Region.cut Rinf m lev N
  /-- Figure 11(B) (`:848-856`): `𝓡^{N+1}_I` is generated from `𝓡^N_I` together with the
  forward `ℓ'`-ray at the edge point. -/
  hcover : ∀ N : ℕ,
    PeriodOn (T e ξ) (Nivat.L1Region.cut Rinf m lev N) (c • vl) →
    ¬ PeriodOn (T e ξ) (Nivat.L1Region.cut Rinf m lev (N + 1)) (c • vl) →
    ∀ g ∈ S.image (· + v), g ∉ derivedQ ε u' (S.image (· + v)) → ∀ t₀ : ℤ, τ ≤ t₀ →
      Nivat.L1StraddleMax.overlap (Nivat.L1Region.cut Rinf m lev (N + 1)) (c • vl) ⊆
        Nivat.MaxEnv.genClosure Sφ a
          (Nivat.L1StraddleMax.overlap (Nivat.L1Region.cut Rinf m lev N) (c • vl) ∪
            Nivat.L1StraddleMax.ray g u' t₀)

/-- **`exists_L1MaxBResidual`'s conclusion from `CutResidualR`.**

The family is `Nivat.L1Region.ofCut` (`L1Region.lean:240`) — Collé's `𝓡^n_I` verbatim — and
`N` is `exists_greatest_periodOn` (`L1Region.lean:102`), which is `:820`'s "greatest integer
`N`".  `hline`/`hcover` are then read at that `N` and handed to
`exists_L1MaxBResidual_of_cover` (`:145`).

Consumer: `RegionSteps.exists_L1MaxBResidual` (`RegionSteps.lean:2657`). -/
theorem exists_L1MaxBResidual_of_cutResidualR
    (hℓ_nel : ℓ ∈ Colle45.NonExpansiveLine ξ)
    (hℓ_neg : Colle45.IsOneSidedNonexpansive ξ (-ℓ))
    (hSgen : Nivat.Colle.IsGeneratingSet ξ S)
    (hvl_prim : Primitive vl) (hdet_ℓ : Nivat.LE2.dot ℓ vl = 0)
    (r : CutResidualR ξ S vl) :
    ∃ (e u u' v : ℤ × ℤ) (c τ : ℤ) (ε : Bool) (S₁ : Finset (ℤ × ℤ))
      (F : Nivat.L1Region.RegionFamily (T e ξ) u u' c),
      S₁ = S.image (· + v) ∧
      Nivat.ColleReg.L1Data.MaxBResidual (ξ := ξ) ε u u' c τ S₁ F := by
  classical
  set F : Nivat.L1Region.RegionFamily (T r.e ξ) vl r.u' r.c :=
    Nivat.L1Region.ofCut r.hR r.hmu' r.hmu r.hlev r.hexh r.hgap r.hbase r.hinf with hF
  have hFR : F.R = Nivat.L1Region.cut r.Rinf r.m r.lev := rfl
  obtain ⟨N, hN, hN1⟩ :=
    Nivat.L1Region.exists_greatest_periodOn F.monotone F.base F.union_not
  exact exists_L1MaxBResidual_of_cover hℓ_nel hℓ_neg hSgen hvl_prim hdet_ℓ r.ε r.det' r.prim
    r.c0 F N hN hN1 (r.hline N hN hN1) r.hgen (r.hcover N hN hN1)

/-- Old ⇒ new. -/
noncomputable def WedgeResidualR.ofWedgeResidual (hvl_prim : Primitive vl)
    (r : WedgeResidual ξ S vl) : WedgeResidualR ξ S vl where
  e := r.e
  u' := r.u'
  v := r.v
  b₀ := r.b₀
  c := r.c
  ε := r.ε
  B := r.B
  k := r.k
  hb₀ := r.hb₀
  hunimod := r.hunimod
  c0 := r.c0
  hconv := by
    have hu' : Primitive r.u' := by
      show IsCoprime r.u'.1 r.u'.2
      rcases r.hunimod with h | h
      · exact ⟨vl.2, -vl.1, by simp only [det] at h; linear_combination h⟩
      · exact ⟨-vl.2, vl.1, by simp only [det] at h; linear_combination -h⟩
    exact isLatticeConvexRegion_wedgeFull r.hB hvl_prim hu' r.hlev r.hunimod
  hbase := r.hbase
  hline := r.hline
  hstraddle := r.hstraddle

/-- `hconv` paid by L1B from `hunimod` alone (`isLatticeConvexRegion_wedgeFull_of_unimod`). -/
noncomputable def WedgeResidualR.ofUnimod
    {e u' v b₀ : ℤ × ℤ} {c : ℤ} (ε : Bool) {B : Set (ℤ × ℤ)}
    (hb₀ : b₀ ∈ B) (hunimod : det u' vl = 1 ∨ det u' vl = -1) (c0 : c ≠ 0) (k : ℕ)
    (hbase : PeriodOn (T e ξ) (chainFull B vl u' b₀ k) (c • vl))
    (hline : ∀ N : ℕ, PeriodOn (T e ξ) (chainFull B vl u' b₀ (k + N)) (c • vl) →
      ¬ PeriodOn (T e ξ) (chainFull B vl u' b₀ (k + (N + 1))) (c • vl) →
      ∃ τ : ℤ, ∀ z ∈ derivedQ ε u' (S.image (· + v)),
        τ • u' + z ∈ chainFull B vl u' b₀ (k + N) ∧
        τ • u' + z + c • vl ∈ chainFull B vl u' b₀ (k + N))
    (hstraddle : ∀ N : ℕ, PeriodOn (T e ξ) (chainFull B vl u' b₀ (k + N)) (c • vl) →
      ¬ PeriodOn (T e ξ) (chainFull B vl u' b₀ (k + (N + 1))) (c • vl) →
      ∀ τ : ℤ,
        (∀ z ∈ derivedQ ε u' (S.image (· + v)),
          τ • u' + z ∈ chainFull B vl u' b₀ (k + N) ∧
          τ • u' + z + c • vl ∈ chainFull B vl u' b₀ (k + N)) →
        Nivat.L1Region.Straddle (T e ξ) (chainFull B vl u' b₀ (k + N))
          (chainFull B vl u' b₀ (k + (N + 1))) (S.image (· + v))
          (derivedQ ε u' (S.image (· + v))) vl u' c τ) :
    WedgeResidualR ξ S vl where
  e := e
  u' := u'
  v := v
  b₀ := b₀
  c := c
  ε := ε
  B := B
  k := k
  hb₀ := hb₀
  hunimod := hunimod
  c0 := c0
  hconv := Nivat.ColleReg.L1Data.isLatticeConvexRegion_wedgeFull_of_unimod hunimod
  hbase := hbase
  hline := hline
  hstraddle := hstraddle

/-- The leaf's conclusion with **no `B`-shape hypothesis at all**: `hlev`, `hB`, `hEnv` gone. -/
theorem exists_L1MaxBResidual_of_unimod_split
    (hξ : IsMinimalCounterexample ξ) (d : Nivat.Colle35.DecompDataZ ξ)
    (hℓ_nel : ℓ ∈ Colle45.NonExpansiveLine ξ)
    (hℓ_neg : Colle45.IsOneSidedNonexpansive ξ (-ℓ))
    (hSgen : Nivat.Colle.IsGeneratingSet ξ S)
    (hvl_prim : Primitive vl) (hdet_ℓ : Nivat.LE2.dot ℓ vl = 0)
    {e u' v b₀ : ℤ × ℤ} {c : ℤ} (ε : Bool) {B : Set (ℤ × ℤ)}
    (hb₀ : b₀ ∈ B) (hunimod : det u' vl = 1 ∨ det u' vl = -1) (c0 : c ≠ 0) (k : ℕ)
    (hbase : PeriodOn (T e ξ) (chainFull B vl u' b₀ k) (c • vl))
    (hline : ∀ N : ℕ, PeriodOn (T e ξ) (chainFull B vl u' b₀ (k + N)) (c • vl) →
      ¬ PeriodOn (T e ξ) (chainFull B vl u' b₀ (k + (N + 1))) (c • vl) →
      ∃ τ : ℤ, ∀ z ∈ derivedQ ε u' (S.image (· + v)),
        τ • u' + z ∈ chainFull B vl u' b₀ (k + N) ∧
        τ • u' + z + c • vl ∈ chainFull B vl u' b₀ (k + N))
    (hstraddle : ∀ N : ℕ, PeriodOn (T e ξ) (chainFull B vl u' b₀ (k + N)) (c • vl) →
      ¬ PeriodOn (T e ξ) (chainFull B vl u' b₀ (k + (N + 1))) (c • vl) →
      ∀ τ : ℤ,
        (∀ z ∈ derivedQ ε u' (S.image (· + v)),
          τ • u' + z ∈ chainFull B vl u' b₀ (k + N) ∧
          τ • u' + z + c • vl ∈ chainFull B vl u' b₀ (k + N)) →
        Nivat.L1Region.Straddle (T e ξ) (chainFull B vl u' b₀ (k + N))
          (chainFull B vl u' b₀ (k + (N + 1))) (S.image (· + v))
          (derivedQ ε u' (S.image (· + v))) vl u' c τ) :
    ∃ (e u u' v : ℤ × ℤ) (c τ : ℤ) (ε : Bool) (S₁ : Finset (ℤ × ℤ))
      (F : Nivat.L1Region.RegionFamily (T e ξ) u u' c),
      S₁ = S.image (· + v) ∧
      Nivat.ColleReg.L1Data.MaxBResidual (ξ := ξ) ε u u' c τ S₁ F :=
  exists_L1MaxBResidual_of_wedgeResidualR hξ d hℓ_nel hℓ_neg hSgen hvl_prim hdet_ℓ
    (WedgeResidualR.ofUnimod ε hb₀ hunimod c0 k hbase hline hstraddle)

/-- `ofSweep` analogue. -/
noncomputable def WedgeResidualR.ofSweep
    (hSgen : Nivat.Colle.IsGeneratingSet ξ S)
    {e u' v b₀ : ℤ × ℤ} {c : ℤ} (ε : Bool) {B : Set (ℤ × ℤ)}
    (hb₀ : b₀ ∈ B) (hconv : IsLatticeConvexRegion (wedgeFull B vl u'))
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) (c0 : c ≠ 0)
    {a : ℤ × ℤ} (ha : a ∈ S) (hconvS : Nivat.LatticeConvex (S.erase a))
    {D : Set (ℤ × ℤ)} (hD : ∀ z ∈ D, (T e ξ) z = T (c • vl) (T e ξ) z)
    (hwin : ∀ i j : ℕ, ∀ z ∈ S.erase a,
      z + (coverEnum vl u' b₀ i j - a) ∈
        D ∪ (⋃ i' ∈ {i' | i' < i}, Set.range (coverEnum vl u' b₀ i')) ∪
          (coverEnum vl u' b₀ i '' {j' | j' < j}))
    (hline : ∀ N : ℕ, PeriodOn (T e ξ) (chainFull B vl u' b₀ N) (c • vl) →
      ¬ PeriodOn (T e ξ) (chainFull B vl u' b₀ (N + 1)) (c • vl) →
      ∃ τ : ℤ, ∀ z ∈ derivedQ ε u' (S.image (· + v)),
        τ • u' + z ∈ chainFull B vl u' b₀ N ∧
        τ • u' + z + c • vl ∈ chainFull B vl u' b₀ N)
    (hstraddle : ∀ N : ℕ, PeriodOn (T e ξ) (chainFull B vl u' b₀ N) (c • vl) →
      ¬ PeriodOn (T e ξ) (chainFull B vl u' b₀ (N + 1)) (c • vl) →
      ∀ τ : ℤ,
        (∀ z ∈ derivedQ ε u' (S.image (· + v)),
          τ • u' + z ∈ chainFull B vl u' b₀ N ∧
          τ • u' + z + c • vl ∈ chainFull B vl u' b₀ N) →
        Nivat.L1Region.Straddle (T e ξ) (chainFull B vl u' b₀ N)
          (chainFull B vl u' b₀ (N + 1)) (S.image (· + v))
          (derivedQ ε u' (S.image (· + v))) vl u' c τ) :
    WedgeResidualR ξ S vl where
  e := e
  u' := u'
  v := v
  b₀ := b₀
  c := c
  ε := ε
  B := B
  k := 0
  hb₀ := hb₀
  hunimod := hunimod
  c0 := c0
  hconv := hconv
  hbase := Nivat.HbaseBridge.hbase_at_of_sweep_of_isGeneratingSet hSgen ha hconvS 0 hD
    (coverEnum vl u' b₀) hwin (hK_of_coverEnum hunimod)
  hline := fun N hN hN1 => by
    simp only [Nat.zero_add] at hN hN1 ⊢
    exact hline N hN hN1
  hstraddle := fun N hN hN1 τ hl => by
    simp only [Nat.zero_add] at hN hN1 hl ⊢
    exact hstraddle N hN hN1 τ hl

/-- Aface's `HbaseBridge.cutBand` (`HbaseBridge.lean:1598`) is `cutFringe` with `fringe`
unfolded; the two are definitionally equal (import direction forbids stating this there). -/
theorem cutBand_eq_cutFringe (B : Set (ℤ × ℤ)) (vl u' b₀ : ℤ × ℤ) (S : Finset (ℤ × ℤ))
    (a : ℤ × ℤ) :
    Nivat.HbaseBridge.cutBand B vl u' b₀ S a = cutFringe B vl u' b₀ S a :=
  rfl

/-- §18 transcribed: `cutFringe` escapes `chainFull ∪ wedgeFull` iff some `z ∈ S.erase a` is
strictly lower than `a` in **both** `expNormal u' vl` and `expNormal vl u'`. -/
theorem not_cutFringe_subset_wedgeFull_iff {B : Finset (ℤ × ℤ)} (hBne : B.Nonempty)
    {u' b₀ a : ℤ × ℤ} {S : Finset (ℤ × ℤ)}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) :
    (¬ cutFringe (↑B : Set (ℤ × ℤ)) vl u' b₀ S a ⊆
        chainFull (↑B : Set (ℤ × ℤ)) vl u' b₀ 0 ∪ wedgeFull (↑B : Set (ℤ × ℤ)) vl u') ↔
      ∃ z ∈ S.erase a,
        Nivat.LE2.dot (expNormal u' vl) z < Nivat.LE2.dot (expNormal u' vl) a ∧
        Nivat.LE2.dot (expNormal vl u') z < Nivat.LE2.dot (expNormal vl u') a := by
  rw [← cutBand_eq_cutFringe]
  exact Nivat.HbaseBridge.not_cutBand_subset_wedgeFull_iff hBne hunimod

end RouteA

end Nivat.ColleReg.L1Claim

section Receipts
/-! Standing `#print axioms` receipts.  Deletable as a block. -/

#print axioms Nivat.ColleReg.L1Claim.exists_L1MaxBResidual_of_tail
#print axioms Nivat.ColleReg.L1Claim.exists_L1MaxBResidual_of_family
#print axioms Nivat.ColleReg.L1Claim.exists_L1MaxBResidual_of_cover
#print axioms Nivat.ColleReg.L1Claim.exists_L1MaxBResidual_of_wedgeAt
#print axioms Nivat.ColleReg.L1Claim.exists_L1MaxBResidual_of_wedgeAt_split
#print axioms Nivat.ColleReg.L1Claim.exists_L1MaxBResidual_of_wedgeResidual
#print axioms Nivat.ColleReg.L1Claim.WedgeResidual.ofSweep
#print axioms Nivat.ColleReg.L1Claim.fringe_subset_iff
#print axioms Nivat.ColleReg.L1Claim.fringe_chainFull_eq
#print axioms Nivat.ColleReg.L1Claim.hfringe_of_sides
#print axioms Nivat.ColleReg.L1Claim.frontFringe_subset_iff
#print axioms Nivat.ColleReg.L1Claim.cutFringe_subset_iff
#print axioms Nivat.ColleReg.L1Claim.cutFringe_add_nsmul_u'
#print axioms Nivat.ColleReg.L1Claim.cutFringe_nonempty_iff
#print axioms Nivat.ColleReg.L1Claim.exists_bound_halfStrip
#print axioms Nivat.ColleReg.L1Claim.not_cutFringe_subset_halfStrip
#print axioms Nivat.ColleReg.L1Claim.not_item2_instance
#print axioms Nivat.ColleReg.L1Claim.chainFull_zero_add_zsmul_vl
#print axioms Nivat.ColleReg.L1Claim.cutFringe_add_zsmul_vl
#print axioms Nivat.ColleReg.L1Claim.cutFringe_subset_rebased
#print axioms Nivat.ColleReg.L1Claim.ofWedgeAtConvex
#print axioms Nivat.ColleReg.L1Claim.ofWedgeAtConvex_R
#print axioms Nivat.ColleReg.L1Claim.exists_L1MaxBResidual_of_convex_split
#print axioms Nivat.ColleReg.L1Claim.exists_L1MaxBResidual_of_wedgeAt_split'
#print axioms Nivat.ColleReg.L1Claim.exists_L1MaxBResidual_of_wedgeResidualR
#print axioms Nivat.ColleReg.L1Claim.WedgeResidualR.ofWedgeResidual
#print axioms Nivat.ColleReg.L1Claim.WedgeResidualR.ofUnimod
#print axioms Nivat.ColleReg.L1Claim.exists_L1MaxBResidual_of_unimod_split
#print axioms Nivat.ColleReg.L1Claim.WedgeResidualR.ofSweep
#print axioms Nivat.ColleReg.L1Claim.cutBand_eq_cutFringe
#print axioms Nivat.ColleReg.L1Claim.not_cutFringe_subset_wedgeFull_iff
#print axioms Nivat.ColleReg.L1Claim.exists_L1MaxBResidual_of_cutResidualR

end Receipts
