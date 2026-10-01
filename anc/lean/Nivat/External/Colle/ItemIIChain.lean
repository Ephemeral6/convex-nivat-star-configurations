/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.ItemIIRec
import Nivat.External.Colle.ChainPartsFeed

/-!
# `exists_itemII_chain`: Collé's chain `B₁ ⊂ A₁ ⊂ B₂ ⊂ …` with item (ii), as an `∃`

Lane LeafA-itemII, 2026-09-21.  **Consumer**: `exists_chainData` (`RegionSteps.lean`), through
the four chain fields `envB` / `maxA` / `subBA` / `subAB` of
`ChainAsm.Aparts.ChainDataGeomParts` (`ChainPartsFeed.lean`) and `Colle35.ChainDataGeom.ofParts`
(`ChainAssemble.lean`).  This file is upstream of `RegionSteps.lean`: it imports `ItemIIRec`
(closure `ChainAssemble` + `ItemII` + `AbsorbEnv`) and `ChainPartsFeed` (already imported by
`RegionSteps`, and whose closure already contains `ItemIIRec`), so `RegionSteps` can `import`
this file without enlarging its closure by anything but this module.

## What is here and what is not

The recursion itself is **not** built here — it is `AenvfixProbe.chain` (`ItemIIRec.lean`),
landed 2026-09-20, which already discharges every conjunct below (`envB_ch` / `maxA_ch` /
`subBA_ch` / `subAB_ch` / `itemII_ch` / `exhausts_ch`, `ItemIIRec.lean:174-219`).  What was
missing (PROTOCOL §20 orphan scan, 2026-09-21: `grep AenvfixProbe Nivat/` finds no consumer of
the chain) is the **existential packaging with the standing hypotheses discharged**: `ItemIIRec`
takes a `Ctx` record whose fields `hstep` / `hfin` / `harea` are *themselves* theorems
(`TLSeam.stepHyp_of_case2`, `MaxEnv.finite_of_envOf`, `LE2.posArea_of_envOf`), all needing the
same five edge-normal facts about `𝒮_φ`.  `exists_itemII_chain` below takes exactly those facts
and `Case2`, and returns the chain as `∃ B A u, …`.

## Alignment with `b3_colle2.txt` (hard rule 7: every quantifier traced)

The conclusion's conjuncts, in order, and the line of the source each transcribes:

| conjunct | source |
|---|---|
| `∀ i, EnvOf ↑S (B i)` | `:472` item (i), "`B_i ⊂ ℤ²` is an `E(𝒮_φ)`-enveloped set" |
| `∀ i, (B i).Finite` | Definition 3.2 (`:402`) is stated for finite `𝒰`; finiteness of enveloped sets is `MaxEnv.finite_of_envOf` from two antipodal edge pairs |
| `∀ i, suppVal (B i) (-nℓ) = -cz` | `:472` item (i), "with `B_i ∩ ℓ_{B_i} ⊂ ℓ^(−)`" — the `ℓ`-support line of `B_i` is `ℓ^(−)`.  Convention: `ℋ(ℓ^(−)) = {cz ≤ ⟪nℓ,·⟫}` (`ItemII.lean`), so the `⟪-nℓ,·⟫`-maximising face sits at `-cz` |
| `∀ i, ∀ z ∈ B i, cz ≤ dot nℓ z` | the inequality half of the same clause, `B_i ⊆ ℋ(ℓ^(−))` |
| `∀ i, IsMaxEnvIn (EnvOf ↑S) (canonA …) (A i)` | `:484` item (iv), verbatim shape (`ChainMax.lean`) |
| `∀ i, B i ⊆ A i` | `:466` "`B_i ⊂ A_i`" |
| `∀ i, A i ⊆ B (i + 1)` | `:474` item (ii), first half: "`B_i` contains … `A_{i-1}`" |
| `∀ i z, ‖z‖∞ ≤ i → z ∈ ℋ → z ∈ B (i + 1)` | `:474` item (ii), second half: "… and `[-i+1, i-1]² ∩ ℋ(ℓ^(−))`", under the convention Lean `B 0` = paper `B'` (seed), Lean `B (i+1)` = paper `B_{i+1}` ⊇ `[-i,i]²∩ℋ`.  This is the **shifted** (faithful) form that `Colle35.itemII_shift` asks producers for |
| `ItemII B nℓ cz` | the same, in the shape `ItemII.lean`'s consumers take |
| `Exhausts A nℓ cz` | `:498` "Since `⋃ A_i = ℋ(ℓ^(−))`" |

Item (iii) (`:480`, "`(T^{u_i}η)|B_i = x_per|B_i` for some `u_i`") is not a separate conjunct:
it is `B i ⊆ A i ⊆ canonA …`, i.e. `subBA` + `maxA`, and the "but ≠ on `H_{B_i}(ℓ)`" half is
the `Case2` hypothesis itself (`CaseSplit.lean:69`, `:758`).

The hypotheses, and where the consumer gets them:

| hypothesis | source / producer at `exists_chainData` |
|---|---|
| `hS : LatticeConvex S`, `hSne : S.Nonempty` | `𝒮_φ` is convex (`:424`); `DecompDataZ.Sphi_conv` |
| `hxper : xper ∈ orbitClosure ξ` | "`x_per ∈ X_η`" (`:426`); binder of `exists_chainData` |
| `hprim : Primitive nℓ`, `hperp : dot nℓ vl = 0` | `nℓ` is the primitive normal of `ℓ_ι`, `v_ℓ ∥ ℓ_ι`; both in `hpartner` |
| `hnℓ' : -nℓ ∈ E ↑S` | `ℓ_ι` is parallel to an edge of `𝒮_φ` (`:447`), and `-nℓ` is the outer normal of the edge on the `ℓ^(−)` side (the face of `B_i` that `:472` pins).  `𝒮_φ` is a zonotope, so both signs are edges — `ONEDRational.mem_E_Sphi_and_neg_mem_E_Sphi_of_biONED` |
| `hn hn' hm hm' : ±n, ±m ∈ E ↑S`, `hdet : det n m ≠ 0` | two non-parallel edge directions of `𝒮_φ` (`m ≥ 2`, `:424`, "vectors in pairwise distinct directions"); same binder list as `TLSeam.stepHyp_of_case2` and `MaxEnv.finite_of_envOf`; produced from `EdgeNormals.exists_two_nonparallel_edge_normals` the way `L1Sfin.hSfin_of_decompDataZ` (`SfinBound.lean`) does |
| `hcase2 : Case2 ξ xper S vl` | `:758` Case 2; binder of `exists_chainData` |

`cz : ℤ` is free: the seed is *placed* so that its `ℓ`-support line is the level line
`{⟪nℓ,·⟫ = cz}` (`:464`, "the support line of `B'` determined by `ℓ` coincides with `ℓ^(−)`"),
using `Primitive nℓ` (`dot_surjective`).  The consumer will take `cz` from `hpartner`, so that
`ℋ(ℓ^(−))` is the half plane on which `x_per` and `y_per` agree.

## Why this chain escapes `false_of_chain_halfStrip`

`ChainAssemble.lean` §5 proves the recursion `B (i+1) := A i` can never reach a `ChainDataGeom`:
`subStrip` then traps every `A i` in `halfStrip (B 0) vl`.  The chain here is *not* trapped —
`not_hchain_of_itemII` below is the kernel statement: any chain satisfying `subStrip` and the
box clause of item (ii) with a finite seed **violates** `∀ i, B (i+1) ⊆ halfStrip (A i) vl`, the
premise of `ChainDataGeom.false_of_chain_halfStrip`.  So the refutation's premise fails on the
output of `exists_itemII_chain` (`not_hchain_of_exists_itemII_chain`), and item (ii) is exactly
the mechanism by which it fails.
-/

set_option autoImplicit false

namespace Nivat.ItemIIChain

open Nivat Nivat.LE2 Nivat.Colle35 Nivat.ColleReg4 Nivat.ChainAsm Nivat.AenvfixProbe

/-- Three distinct edge normals of `S` from one antipodal pair and one non-parallel normal:
`n ≠ -n` because `n ≠ 0` (edge normals are primitive); `±n ≠ m` because `det n m ≠ 0`.
This supplies Definition 3.2's positive-area clause (`:402`) for every `E(S)`-enveloped set,
in the shape `AbsorbEnv.exists_enveloped_absorbing` consumes. -/
theorem posArea_of_envOf_of_pair {S : Finset (ℤ × ℤ)} {n m : ℤ × ℤ}
    (hn : n ∈ E (↑S : Set (ℤ × ℤ))) (hn' : -n ∈ E (↑S : Set (ℤ × ℤ)))
    (hm : m ∈ E (↑S : Set (ℤ × ℤ))) (hdet : det n m ≠ 0)
    {B : Set (ℤ × ℤ)} (hB : EnvOf (↑S : Set (ℤ × ℤ)) B) : PosArea B := by
  have hne : n ≠ 0 := (mem_E_iff.mp hn).1.ne_zero
  refine posArea_of_envOf hn hn' hm ?_ ?_ ?_ (finite_E_of_finite S.finite_toSet) hB
  · intro h
    apply hne
    have h2 : n + n = 0 := by
      calc n + n = n + -n := by rw [← h]
        _ = 0 := add_neg_cancel n
    rw [Prod.ext_iff] at h2 ⊢
    simp only [Prod.fst_add, Prod.snd_add, Prod.fst_zero, Prod.snd_zero] at h2 ⊢
    omega
  · intro h
    apply hdet
    rw [h, det_self]
  · intro h
    apply hdet
    have : det (-n) m = 0 := by rw [h, det_self]
    simp only [det, Prod.fst_neg, Prod.snd_neg] at this ⊢
    linarith

/-- **Collé's chain with item (ii)** (`b3_colle2.txt:466-498`, table in the module docstring).

From `Case2` and the edge-normal facts of `𝒮_φ`, there is a chain `(B, A, u)` that is
`E(𝒮_φ)`-enveloped at every stage (`:472`), `:484`-maximal (`maxA`), nested (`:466`, `:474`),
absorbs the boxes `[-i,i]² ∩ ℋ(ℓ^(−))` (`:474`), keeps its `ℓ`-support line on `ℓ^(−)` (`:472`),
and exhausts the half plane (`:498`). -/
theorem exists_itemII_chain {ξ xper : Config ℤ} {S : Finset (ℤ × ℤ)} {vl nℓ : ℤ × ℤ}
    (cz : ℤ) (hS : LatticeConvex S) (hSne : S.Nonempty)
    (hxper : xper ∈ orbitClosure ξ)
    (hprim : Primitive nℓ) (hperp : dot nℓ vl = 0)
    (hnℓ' : -nℓ ∈ E (↑S : Set (ℤ × ℤ)))
    {n m : ℤ × ℤ} (hdet : det n m ≠ 0)
    (hn : n ∈ E (↑S : Set (ℤ × ℤ))) (hn' : -n ∈ E (↑S : Set (ℤ × ℤ)))
    (hm : m ∈ E (↑S : Set (ℤ × ℤ))) (hm' : -m ∈ E (↑S : Set (ℤ × ℤ)))
    (hcase2 : Nivat.ColleReg.Case2 ξ xper S vl) :
    ∃ (B A : ℕ → Set (ℤ × ℤ)) (u : ℕ → ℤ × ℤ),
      (∀ i, EnvOf (↑S : Set (ℤ × ℤ)) (B i)) ∧
      (∀ i, (B i).Finite) ∧
      (∀ i, suppVal (B i) (-nℓ) = -cz) ∧
      (∀ i, ∀ z ∈ B i, cz ≤ dot nℓ z) ∧
      (∀ i, IsMaxEnvIn (EnvOf (↑S : Set (ℤ × ℤ))) (canonA ξ xper vl B u i) (A i)) ∧
      (∀ i, B i ⊆ A i) ∧
      (∀ i, A i ⊆ B (i + 1)) ∧
      (∀ i : ℕ, ∀ z : ℤ × ℤ, |z.1| ≤ (i : ℤ) → |z.2| ≤ (i : ℤ) → cz ≤ dot nℓ z →
        z ∈ B (i + 1)) ∧
      ItemII B nℓ cz ∧
      Exhausts A nℓ cz := by
  have hU : (E (↑S : Set (ℤ × ℤ))).Finite := finite_E_of_finite S.finite_toSet
  -- the standing hypotheses of `ItemIIRec`'s recursion
  have c : Ctx ξ xper S vl nℓ :=
    Ctx.mk_of_mem_E
      (fun u₀ => Nivat.TLSeam.stepHyp_of_case2 hU hdet hn hn' hm hm' hcase2)
      hnℓ'
      (fun B hB => Nivat.MaxEnv.finite_of_envOf hU hdet hn hn' hm hm' hB)
      (fun B hB => posArea_of_envOf_of_pair hn hn' hm hdet hB)
      hxper hperp
  -- the seed `B'` (`:462-464`), placed with its `ℓ`-support line on `{⟪nℓ,·⟫ = cz}`
  obtain ⟨s₀⟩ := exists_seed' (ξ := ξ) (xper := xper) (cz := cz) hS hSne hprim hxper
  refine ⟨chB c s₀, chA c s₀, chU c s₀, envB_ch c s₀, finB_ch c s₀, ?_, le_dot_B_ch c s₀,
    maxA_ch c s₀, subBA_ch c s₀, subAB_ch c s₀, ?_, itemII_ch c s₀, exhausts_ch c s₀⟩
  · intro i
    exact (chain c s₀ i).supp
  · intro i z h1 h2 hz
    rw [chB_succ]
    refine (stepB_spec c _ i).2.2.1 ?_
    rw [Finset.mem_coe, mem_boxHP]
    refine ⟨?_, ?_, hz⟩ <;> constructor <;>
      linarith [abs_le.mp h1, abs_le.mp h2, le_abs_self z.1, neg_abs_le z.1, le_abs_self z.2,
        neg_abs_le z.2]

/-! ## The escape from `false_of_chain_halfStrip`, in the kernel -/

/-- **A chain with the box clause of item (ii) is not trapped in `halfStrip (A i) vl`.**
Contrapositive of `Colle35.not_itemII_of_chain` (`ItemII.lean`): `subStrip` + `hchain` would
confine every `B i` to `halfStrip (B 0) vl`, on which `det vl` is bounded, while the boxes of
item (ii) are unbounded along `nℓ`.  `nℓ ≠ 0` is from `Primitive nℓ`. -/
theorem not_hchain_of_itemII {B A : ℕ → Set (ℤ × ℤ)} {vl nℓ : ℤ × ℤ} {cz : ℤ}
    (hB0 : (B 0).Finite) (hvl : vl ≠ 0) (hprim : Primitive nℓ) (hperp : dot nℓ vl = 0)
    (subStrip : ∀ i, A i ⊆ Colle35.halfStrip (B i) vl)
    (hII : ItemII B nℓ cz) :
    ¬ ∀ i, B (i + 1) ⊆ Colle35.halfStrip (A i) vl :=
  fun hchain =>
    Colle35.not_itemII_of_chain hB0 hvl hperp (prim_iff_primitive.mpr hprim).ne_zero
      subStrip hchain cz hII

/-- **The output of `exists_itemII_chain` violates the premise of
`ChainDataGeom.false_of_chain_halfStrip`** (`ChainAssemble.lean`).  `subStrip` is
`subStrip_of_max` from the `maxA` conjunct; the seed is finite by the second conjunct.  This is
the kernel check that the item-(ii) chain is a different object from `ChainRecursion.chainB`, not
the same dead end renamed. -/
theorem not_hchain_of_exists_itemII_chain {ξ xper : Config ℤ} {S : Finset (ℤ × ℤ)}
    {vl nℓ : ℤ × ℤ} (cz : ℤ) (hS : LatticeConvex S) (hSne : S.Nonempty)
    (hxper : xper ∈ orbitClosure ξ)
    (hprim : Primitive nℓ) (hperp : dot nℓ vl = 0) (hvl : vl ≠ 0)
    (hnℓ' : -nℓ ∈ E (↑S : Set (ℤ × ℤ)))
    {n m : ℤ × ℤ} (hdet : det n m ≠ 0)
    (hn : n ∈ E (↑S : Set (ℤ × ℤ))) (hn' : -n ∈ E (↑S : Set (ℤ × ℤ)))
    (hm : m ∈ E (↑S : Set (ℤ × ℤ))) (hm' : -m ∈ E (↑S : Set (ℤ × ℤ)))
    (hcase2 : Nivat.ColleReg.Case2 ξ xper S vl) :
    ∃ (B A : ℕ → Set (ℤ × ℤ)) (u : ℕ → ℤ × ℤ),
      (∀ i, IsMaxEnvIn (EnvOf (↑S : Set (ℤ × ℤ))) (canonA ξ xper vl B u i) (A i)) ∧
      ¬ ∀ i, B (i + 1) ⊆ Colle35.halfStrip (A i) vl := by
  obtain ⟨B, A, u, -, hfin, -, -, maxA, -, -, -, hII, -⟩ :=
    exists_itemII_chain cz hS hSne hxper hprim hperp hnℓ' hdet hn hn' hm hm' hcase2
  exact ⟨B, A, u, maxA, not_hchain_of_itemII (hfin 0) hvl hprim hperp (subStrip_of_max maxA) hII⟩

/-! ## Feeding the consumer: `ChainDataGeomParts` from the chain plus its residual

`ChainAsm.Aparts.ChainDataGeomParts` (`ChainPartsFeed.lean`) is the 24-field split of
`ChainDataGeom.ofParts`'s residual at the `exists_chainData` layer.  The constructor below shows
what `exists_itemII_chain` pays for and what it does not: **its binder list is the residual**
(hard rule 3 — no hand-written table).  Paid by the chain: `B A u envB maxA subBA subAB`, plus
`envShift` (free, `Colle35.envOf_shift_mem`) and `hfin` (free from `∀ i, (B i).Finite` and
`subAB`, via `ChainAsm.hatOf_finite`).  Everything else — `kk` / `AhatMono`, the shell block,
the face block, `bottom` / `rec_p` / `dot_nJ_p`, and the `ℓ_ι` side — is a hypothesis here,
stated verbatim as `ChainDataGeomParts` states it. -/

/-- **`ChainDataGeomParts` from an item-(ii) chain and the residual obligations.**  The five
chain-side inputs `envB finB maxA subBA subAB` are conjuncts of `exists_itemII_chain` (same
shapes); the rest are `ChainDataGeomParts`'s own fields. -/
noncomputable def chainDataGeomParts_of_chain
    (ξ xper : Config ℤ) (vl p : ℤ × ℤ) (S : Finset (ℤ × ℤ)) (gen : ℤ × ℤ)
    (B A : ℕ → Set (ℤ × ℤ)) (u : ℕ → ℤ × ℤ)
    (envB : ∀ i, EnvOf (↑S : Set (ℤ × ℤ)) (B i))
    (finB : ∀ i, (B i).Finite)
    (maxA : ∀ i, IsMaxEnvIn (EnvOf (↑S : Set (ℤ × ℤ))) (canonA ξ xper vl B u i) (A i))
    (subBA : ∀ i, B i ⊆ A i) (subAB : ∀ i, A i ⊆ B (i + 1))
    (kk : ℕ → ℕ)
    (AhatMono : ∀ i j, i ≤ j → hatOf A kk vl i ⊆ hatOf A kk vl j)
    (vJ1 nJ : ℤ × ℤ) (cJ : ℤ)
    (hsweep : dot nJ vJ1 < 0)
    (hhp : ∀ i, hatOf A kk vl i ⊆ halfPlaneGE nJ cJ)
    (hswept : MaxEnv.SweptClosed (⋃ i, hatOf A kk vl i) vJ1 nJ cJ)
    (ahat_nonempty : (⋃ i, hatOf A kk vl i).Nonempty)
    -- **2026-09-25 (B) 栈迁移（集成者）**：以下六条跟着 `ChainDataGeomParts`
    -- （`ChainPartsFeed.lean`）一起换到 `b3_colle2.txt:518` 的交集对象上。`w` 是原文的
    -- `−v_{ℓ_{J+1}}`，与 `vJ1` 是两份数据且必须横截（`w := vJ1` 被
    -- `ShellMink.lean:588` ＋ `FillCoverWitness.lean` §1 合成的反例否掉）；`I₀` 是 `:520` 的
    -- 第二个常数（`:524`「`i ≥ max{i₀, I₀}`」）。旧的 `escape` binder 已删，换成 `escapeW`。
    (w : ℤ × ℤ) (hsweepW : dot nJ w < 0) (I₀ : ℕ)
    (escapeW : ∀ ε i₀ : ℕ, 0 < ε →
      (∀ i, i₀ ≤ i → EnvOf (↑S : Set (ℤ × ℤ)) (ShellMink.shellInter (hatOf A kk vl i)
        (MaxEnv.shell (⋃ i, hatOf A kk vl i) vJ1 nJ cJ ε) w)) →
      ∀ i, max i₀ I₀ ≤ i → ∃ g ∈ hatOf A kk vl i, ∃ t : ℕ,
      g + (t : ℤ) • w ∈ MaxEnv.shell (⋃ i, hatOf A kk vl i) vJ1 nJ cJ ε ∧
      g + (t : ℤ) • w ∉ hatOf A kk vl i)
    (shellSubStrip : ∀ ε i₀ : ℕ, 0 < ε →
      (∀ i, i₀ ≤ i → EnvOf (↑S : Set (ℤ × ℤ)) (ShellMink.shellInter (hatOf A kk vl i)
        (MaxEnv.shell (⋃ i, hatOf A kk vl i) vJ1 nJ cJ ε) w)) →
      ∀ i, max i₀ I₀ ≤ i →
      ShellMink.shellInter (hatOf A kk vl i)
          (MaxEnv.shell (⋃ i, hatOf A kk vl i) vJ1 nJ cJ ε) w ⊆
        {z | z + (kk i : ℤ) • vl ∈ Colle35.halfStrip (B i) vl})
    (shellEnv : ∃ ε i₀, 0 < ε ∧
      ∀ i, i₀ ≤ i → EnvOf (↑S : Set (ℤ × ℤ)) (ShellMink.shellInter (hatOf A kk vl i)
        (MaxEnv.shell (⋃ i, hatOf A kk vl i) vJ1 nJ cJ ε) w))
    (fillCover : ∀ ε i₀ : ℕ, 0 < ε →
      (∀ i, i₀ ≤ i → EnvOf (↑S : Set (ℤ × ℤ)) (ShellMink.shellInter (hatOf A kk vl i)
        (MaxEnv.shell (⋃ i, hatOf A kk vl i) vJ1 nJ cJ ε) w)) →
      ∀ i, max i₀ I₀ ≤ i →
      ShellMink.shellInter (hatOf A kk vl i)
          (MaxEnv.shell (⋃ i, hatOf A kk vl i) vJ1 nJ cJ ε) w ⊆
        {z | Colle37.GenClosure S (hatOf A kk vl i ∪
          ShellMink.shellInter (hatOf A kk vl i₀)
            (MaxEnv.shell (⋃ i, hatOf A kk vl i) vJ1 nJ cJ ε) w) z})
    (vJ : ℤ × ℤ) (F : Colle35.FaceBlock S nJ vJ)
    (gen_eq : gen = F.a') (vJ_prim : Primitive vJ) (nJ_prim : Primitive nJ)
    (bottom : ∀ ε : ℕ, ∃ (z₀ : ℤ × ℤ) (L : ℤ),
      dot nJ z₀ = cJ - (ε : ℤ) - 1 ∧
      (∀ k : ℤ, L ≤ k → z₀ + k • vJ ∈ MaxEnv.reachSet (⋃ i, hatOf A kk vl i) vJ1) ∧
      (∀ b ∈ S, ∀ k : ℤ, L ≤ k →
        z₀ + k • vJ + (b - F.a) ∈ MaxEnv.reachSet (⋃ i, hatOf A kk vl i) vJ1) ∧
      (∀ z ∈ MaxEnv.shell (⋃ i, hatOf A kk vl i) vJ1 nJ cJ (ε + 1),
        z ∈ MaxEnv.shell (⋃ i, hatOf A kk vl i) vJ1 nJ cJ ε ∨ ∃ k : ℤ, L ≤ k ∧ z = z₀ + k • vJ))
    (rec_p : ∀ g ∈ ⋃ i, hatOf A kk vl i, g + p ∈ ⋃ i, hatOf A kk vl i)
    (dot_nJ_p : dot nJ p ≠ 0)
    (cL : ℤ)
    (ahat_halfPlane_L : ∀ g ∈ ⋃ i, hatOf A kk vl i, cL ≤ dot (det p vJ • (-p.2, p.1)) g)
    (ahat_attained_L : ∃ g ∈ ⋃ i, hatOf A kk vl i, dot (det p vJ • (-p.2, p.1)) g = cL)
    (nfp_L : ¬ ∃ h h' : ℤ × ℤ, det h h' ≠ 0 ∧
      PeriodicOnWith xper {z | cL ≤ dot (det p vJ • (-p.2, p.1)) z} h ∧
      PeriodicOnWith xper {z | cL ≤ dot (det p vJ • (-p.2, p.1)) z} h') :
    Nivat.ChainAsm.Aparts.ChainDataGeomParts ξ xper vl p S gen where
  B := B
  A := A
  u := u
  kk := kk
  envShift := fun v Tset hT => Colle35.envOf_shift_mem _ v Tset hT
  envB := envB
  maxA := maxA
  subBA := subBA
  subAB := subAB
  AhatMono := AhatMono
  vJ1 := vJ1
  nJ := nJ
  cJ := cJ
  hsweep := hsweep
  hfin := hatOf_finite kk vl (fun i => (finB (i + 1)).subset (subAB i))
  hhp := hhp
  hswept := hswept
  ahat_nonempty := ahat_nonempty
  w := w
  hsweepW := hsweepW
  I₀ := I₀
  escapeW := escapeW
  shellSubStrip := shellSubStrip
  shellEnv := shellEnv
  fillCover := fillCover
  vJ := vJ
  F := F
  gen_eq := gen_eq
  vJ_prim := vJ_prim
  nJ_prim := nJ_prim
  bottom := bottom
  rec_p := rec_p
  dot_nJ_p := dot_nJ_p
  cL := cL
  ahat_halfPlane_L := ahat_halfPlane_L
  ahat_attained_L := ahat_attained_L
  nfp_L := nfp_L

end Nivat.ItemIIChain

#print axioms Nivat.ItemIIChain.posArea_of_envOf_of_pair
#print axioms Nivat.ItemIIChain.exists_itemII_chain
#print axioms Nivat.ItemIIChain.not_hchain_of_itemII
#print axioms Nivat.ItemIIChain.not_hchain_of_exists_itemII_chain
#print axioms Nivat.ItemIIChain.chainDataGeomParts_of_chain
