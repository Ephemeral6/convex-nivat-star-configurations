import Nivat.External.Colle.ChainAssemble
import Nivat.External.Colle.ItemII
import Nivat.External.Colle.AbsorbEnv

/-!
Aenvfix probe (2026-09-19, `tmp/`, not landed): **the item-(ii) recursion, as assembly.**

`b3_colle2.txt:474`: *"`B_i` contains both `A_{i-1}` and `[-i+1,i-1]² ∩ ℋ(ℓ^(−))`"*, together
with `:472` *"`B_i ∩ ℓ_{B_i} ⊂ ℓ^(−)`"* (the `ℓ`-support line stays on `ℓ^(−)`) and `:484`
(`A_i` maximal in `H_{B_i}(ℓ)` under agreement).  The recursion is therefore

    A i     := the `StepHyp`-maximal set over `(B i, u i)`                       -- `:484`
    B (i+1) := an `E(𝒮_φ)`-enveloped set ⊇ A i ∪ ([-i,i]² ∩ ℋ(ℓ^(−)))
               with the same `ℓ^(−)` support line                                -- `:472`/`:474`
    u (i+1) := a shift on which `η` agrees with `x_per` on the finite `B (i+1)`   -- `:480`

The one non-`StepHyp` ingredient is the **absorbing enlargement** at fixed support level.
It is not importable from `tmp/` (not a module), so it is taken here as the hypothesis
`Ctx.habs` — stated byte-for-byte as the conclusion of
`Nivat.Absorb.exists_enveloped_absorbing` (`tmp/absorb_3bprime.lean:389`, `check1.sh` EXIT=0,
axioms clean, 2026-09-18, never landed).  Convention: that lemma's `face` is `⟪n,·⟫`-maximising,
so `ℋ(ℓ^(−)) = {cz ≤ ⟪nℓ,·⟫}` (Amink's `ItemII`) is the half plane `{⟪-nℓ,·⟫ ≤ -cz}`, and
"support line on `ℓ^(−)`" is `suppVal B (-nℓ) = -cz`.

What is proved: from `∀ u₀, StepHyp`, `AbsorbHyp`, finiteness and positive area of enveloped
sets, and `x_per ∈ X_η`, a chain `(B, A, u)` exists satisfying **`ItemII B nℓ cz`** and the
chain-side binders of `ChainDataGeom.ofParts` (`envShift` aside): `envB`, `maxA`, `subBA`,
`subAB`, plus `∀ i, (B i).Finite` and `∀ i z ∈ B i, cz ≤ ⟪nℓ,z⟫` (the two side facts
`exhausts_of_itemII` / `placement_of_exhausts` consume).  So `Exhausts A nℓ cz` follows and,
through `ItemII.lean`, `nfp_L` and the placement `cL = k·cz`.

What is **not** proved here: anything about `kk` / `Ahat` / `AhatMono` / the shell block.
`AhatMono` under this recursion is a genuine claim, not free.  The strict-growth conjunct
`∀ i, B i ⊂ B (i+1)` of `exists_chainData` is also not here (reading: `ItemII.exists_le_encard`
+ monotonicity gives `⊂` along a subsequence, not at every step; the exact conjunct may need
the box side to grow by one *point* per step, which `boxHP` does not guarantee).
-/

set_option autoImplicit false

namespace Nivat.AenvfixProbe

open Nivat Nivat.LE2 Nivat.Colle35 Nivat.ColleReg4 Nivat.ChainAsm

/-- The conclusion shape of `Nivat.Absorb.exists_enveloped_absorbing_bounded`
(`AbsorbEnv.lean:403`), quantified over `B` and `F`, as a `Prop` so the recursion can consume
it.  Beyond the plain absorbing enlargement (`EnvOf`/`⊆`/`suppVal`), this also exposes the
dilation parameter `K` and the growth bound `dot m f - dot m b ≤ K` (`f ∈ F`, `m ∈ E U`, `b ∈ B`
fixed) that `stepB_growth` below needs to bound how the chain's `B (i+1)` grows with `i`. -/
def AbsorbHyp (U : Set (ℤ × ℤ)) (n : ℤ × ℤ) : Prop :=
  ∀ B : Set (ℤ × ℤ), EnvOf U B → B.Finite → B.Nonempty → PosArea B →
    ∀ F : Finset (ℤ × ℤ), (∀ f ∈ F, dot n f ≤ suppVal B n) →
      ∃ (B₁ : Set (ℤ × ℤ)) (K : ℤ) (b : ℤ × ℤ), 1 ≤ K ∧ b ∈ B ∧
        EnvOf U B₁ ∧ B ⊆ B₁ ∧ (↑F : Set (ℤ × ℤ)) ⊆ B₁ ∧
        suppVal B₁ n = suppVal B n ∧
        (∀ f ∈ F, ∀ m ∈ Nivat.LE2.E U, dot m f - dot m b ≤ K)

/-- The standing hypotheses of the recursion, bundled.  `hstep` is what L3band's probe (3b)
gets from `d hℓ_nel hℓ_pos hℓ_neg hcase2`; `hfin` is `tmp/L1_hSfin.lean`; `harea` is
`posArea_of_envOf` from three distinct edges of `𝒮_φ`; `hxper`, `hperp` are `exists_chainData`
binders (`hperp` from `hpartner`). -/
structure Ctx (ξ xper : Config ℤ) (S : Finset (ℤ × ℤ)) (vl nℓ : ℤ × ℤ) : Prop where
  hstep : ∀ u₀, StepHyp ξ xper S vl u₀
  habs : AbsorbHyp (↑S : Set (ℤ × ℤ)) (-nℓ)
  hfin : ∀ B : Set (ℤ × ℤ), EnvOf (↑S : Set (ℤ × ℤ)) B → B.Finite
  harea : ∀ B : Set (ℤ × ℤ), EnvOf (↑S : Set (ℤ × ℤ)) B → PosArea B
  hxper : xper ∈ orbitClosure ξ
  hperp : dot nℓ vl = 0

/-- One stage of the chain: an enveloped, finite, nonempty `B` whose `ℓ`-support line is
`ℓ^(−)` (`:472`), with a shift `u` on which `η` agrees with `x_per` on `B` (`:480`). -/
structure St (ξ xper : Config ℤ) (S : Finset (ℤ × ℤ)) (nℓ : ℤ × ℤ) (cz : ℤ) where
  B : Set (ℤ × ℤ)
  env : EnvOf (↑S : Set (ℤ × ℤ)) B
  fin : B.Finite
  ne : B.Nonempty
  supp : suppVal B (-nℓ) = -cz
  u : ℤ × ℤ
  agree : ∀ z ∈ B, T u ξ z = xper z

variable {ξ xper : Config ℤ} {S : Finset (ℤ × ℤ)} {vl nℓ : ℤ × ℤ} {cz : ℤ}

theorem St.le_dot (s : St ξ xper S nℓ cz) {z : ℤ × ℤ} (hz : z ∈ s.B) : cz ≤ dot nℓ z := by
  have h := le_suppVal s.fin s.ne (n := -nℓ) hz
  rw [s.supp, dot_neg_left] at h
  linarith

/-- The box `[-i,i]² ∩ ℋ(ℓ^(−))` as a `Finset`. -/
noncomputable def boxHP (nℓ : ℤ × ℤ) (cz : ℤ) (i : ℕ) : Finset (ℤ × ℤ) := by
  classical
  exact ((Finset.Icc (-(i : ℤ)) i) ×ˢ (Finset.Icc (-(i : ℤ)) i)).filter (fun z => cz ≤ dot nℓ z)

theorem mem_boxHP {i : ℕ} {z : ℤ × ℤ} :
    z ∈ boxHP nℓ cz i ↔ (-(i : ℤ) ≤ z.1 ∧ z.1 ≤ i) ∧ (-(i : ℤ) ≤ z.2 ∧ z.2 ≤ i) ∧
      cz ≤ dot nℓ z := by
  classical
  simp only [boxHP, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  tauto

section Step

variable (c : Ctx ξ xper S vl nℓ)

/-- `A_i` (`:484`): the `StepHyp`-maximal set over the current stage. -/
noncomputable def stepA (s : St ξ xper S nℓ cz) : Set (ℤ × ℤ) :=
  Classical.choose (c.hstep s.u s.B s.env s.agree)

theorem stepA_spec (s : St ξ xper S nℓ cz) :
    EnvOf (↑S : Set (ℤ × ℤ)) (stepA c s) ∧ s.B ⊆ stepA c s ∧
    stepA c s ⊆ Colle35.halfStrip s.B vl ∧ (∀ z ∈ stepA c s, T s.u ξ z = xper z) ∧
    (∀ Tset, EnvOf (↑S : Set (ℤ × ℤ)) Tset → s.B ⊆ Tset → Tset ⊆ Colle35.halfStrip s.B vl →
      (∀ z ∈ Tset, T s.u ξ z = xper z) → stepA c s ⊆ Tset → Tset = stepA c s) :=
  Classical.choose_spec (c.hstep s.u s.B s.env s.agree)

/-- `A_i` keeps the support line: `H_{B_i}(ℓ)` does not change `⟪nℓ,·⟫` (`nℓ ⊥ v_ℓ`). -/
theorem suppVal_stepA (s : St ξ xper S nℓ cz) : suppVal (stepA c s) (-nℓ) = -cz := by
  obtain ⟨henv, hBA, hstrip, -, -⟩ := stepA_spec c s
  have hAfin : (stepA c s).Finite := c.hfin _ henv
  have hAne : (stepA c s).Nonempty := s.ne.mono hBA
  apply le_antisymm
  · obtain ⟨v, hv, hveq⟩ := exists_suppVal_eq hAfin hAne (-nℓ)
    rw [← hveq, dot_neg_left]
    have : cz ≤ dot nℓ v :=
      halfStrip_subset_halfPlane c.hperp (fun z hz => s.le_dot hz) (hstrip hv)
    linarith
  · obtain ⟨b, hb, hbeq⟩ := exists_suppVal_eq s.fin s.ne (-nℓ)
    rw [s.supp] at hbeq
    rw [← hbeq]
    exact le_suppVal hAfin hAne (hBA hb)

/-- The box points are admissible for absorption at level `-cz`. -/
theorem boxHP_le_suppVal (s : St ξ xper S nℓ cz) (i : ℕ) :
    ∀ f ∈ boxHP nℓ cz i, dot (-nℓ) f ≤ suppVal (stepA c s) (-nℓ) := by
  intro f hf
  rw [suppVal_stepA c s, dot_neg_left]
  linarith [(mem_boxHP.mp hf).2.2]

/-- `B_{i+1}` (`:474`): absorb `A_i ∪ ([-i,i]² ∩ ℋ(ℓ^(−)))` at the same support line. -/
noncomputable def stepB (s : St ξ xper S nℓ cz) (i : ℕ) : Set (ℤ × ℤ) :=
  Classical.choose (c.habs (stepA c s) (stepA_spec c s).1 (c.hfin _ (stepA_spec c s).1)
    (s.ne.mono (stepA_spec c s).2.1) (c.harea _ (stepA_spec c s).1) (boxHP nℓ cz i)
    (boxHP_le_suppVal c s i))

theorem stepB_spec (s : St ξ xper S nℓ cz) (i : ℕ) :
    EnvOf (↑S : Set (ℤ × ℤ)) (stepB c s i) ∧ stepA c s ⊆ stepB c s i ∧
    (↑(boxHP nℓ cz i) : Set (ℤ × ℤ)) ⊆ stepB c s i ∧
    suppVal (stepB c s i) (-nℓ) = suppVal (stepA c s) (-nℓ) := by
  obtain ⟨K, b, hK1, hb, henv, hsub, hFsub, hsupp, hbnd⟩ :=
    Classical.choose_spec (c.habs (stepA c s) (stepA_spec c s).1 (c.hfin _ (stepA_spec c s).1)
      (s.ne.mono (stepA_spec c s).2.1) (c.harea _ (stepA_spec c s).1) (boxHP nℓ cz i)
      (boxHP_le_suppVal c s i))
  exact ⟨henv, hsub, hFsub, hsupp⟩

/-- **`K_i`'s growth bound.**  The dilation parameter `K` used to build `B_{i+1} = stepB c s i`
from `A_i = stepA c s` satisfies `dot m f - dot m b ≤ K` for every `f` in the absorbed box
`boxHP nℓ cz i` and every edge normal `m ∈ E(𝒮_φ)`, with `b ∈ A_i` a fixed edge point
independent of `i`.  Since `boxHP nℓ cz i`'s coordinates are pinned to `±i` (`mem_boxHP`), this
is the fact that turns into "`K` grows at most linearly in `i`" once `m`/`b` are bounded (both
independent of `i`, since only `A_i` — the *current* stage — enters, not `i` itself). -/
theorem stepB_growth (s : St ξ xper S nℓ cz) (i : ℕ) :
    ∃ (K : ℤ) (b : ℤ × ℤ), 1 ≤ K ∧ b ∈ stepA c s ∧
      (∀ f ∈ boxHP nℓ cz i, ∀ m ∈ Nivat.LE2.E (↑S : Set (ℤ × ℤ)), dot m f - dot m b ≤ K) := by
  obtain ⟨K, b, hK1, hb, -, -, -, -, hbnd⟩ :=
    Classical.choose_spec (c.habs (stepA c s) (stepA_spec c s).1 (c.hfin _ (stepA_spec c s).1)
      (s.ne.mono (stepA_spec c s).2.1) (c.harea _ (stepA_spec c s).1) (boxHP nℓ cz i)
      (boxHP_le_suppVal c s i))
  exact ⟨K, b, hK1, hb, hbnd⟩

/-- The next stage. -/
noncomputable def step (s : St ξ xper S nℓ cz) (i : ℕ) : St ξ xper S nℓ cz where
  B := stepB c s i
  env := (stepB_spec c s i).1
  fin := c.hfin _ (stepB_spec c s i).1
  ne := s.ne.mono ((stepA_spec c s).2.1.trans (stepB_spec c s i).2.1)
  supp := by rw [(stepB_spec c s i).2.2.2]; exact suppVal_stepA c s
  u := Classical.choose (Nivat.Colle36.exists_shift_agreeing_on_finite c.hxper
    (c.hfin _ (stepB_spec c s i).1))
  agree := Classical.choose_spec (Nivat.Colle36.exists_shift_agreeing_on_finite c.hxper
    (c.hfin _ (stepB_spec c s i).1))

/-- The chain of stages from a seed. -/
noncomputable def chain (s₀ : St ξ xper S nℓ cz) : ℕ → St ξ xper S nℓ cz
  | 0 => s₀
  | i + 1 => step c (chain s₀ i) i

/-- `B_i`, `A_i`, `u_i` of the chain. -/
noncomputable def chB (s₀ : St ξ xper S nℓ cz) (i : ℕ) : Set (ℤ × ℤ) := (chain c s₀ i).B
noncomputable def chA (s₀ : St ξ xper S nℓ cz) (i : ℕ) : Set (ℤ × ℤ) := stepA c (chain c s₀ i)
noncomputable def chU (s₀ : St ξ xper S nℓ cz) (i : ℕ) : ℤ × ℤ := (chain c s₀ i).u

theorem chB_succ (s₀ : St ξ xper S nℓ cz) (i : ℕ) :
    chB c s₀ (i + 1) = stepB c (chain c s₀ i) i := rfl

/-! ### The chain-side binders of `ofParts`, and item (ii) -/

theorem envB_ch (s₀ : St ξ xper S nℓ cz) (i : ℕ) : EnvOf (↑S : Set (ℤ × ℤ)) (chB c s₀ i) :=
  (chain c s₀ i).env

theorem finB_ch (s₀ : St ξ xper S nℓ cz) (i : ℕ) : (chB c s₀ i).Finite := (chain c s₀ i).fin

theorem le_dot_B_ch (s₀ : St ξ xper S nℓ cz) (i : ℕ) : ∀ z ∈ chB c s₀ i, cz ≤ dot nℓ z :=
  fun _ hz => (chain c s₀ i).le_dot hz

theorem subBA_ch (s₀ : St ξ xper S nℓ cz) (i : ℕ) : chB c s₀ i ⊆ chA c s₀ i :=
  (stepA_spec c _).2.1

theorem subAB_ch (s₀ : St ξ xper S nℓ cz) (i : ℕ) : chA c s₀ i ⊆ chB c s₀ (i + 1) := by
  rw [chB_succ]
  exact (stepB_spec c _ i).2.1

theorem subStrip_ch (s₀ : St ξ xper S nℓ cz) (i : ℕ) :
    chA c s₀ i ⊆ Colle35.halfStrip (chB c s₀ i) vl :=
  (stepA_spec c _).2.2.1

/-- `ofParts.maxA`, verbatim shape, from `isMaxEnvIn_of_stepHyp`. -/
theorem maxA_ch (s₀ : St ξ xper S nℓ cz) (i : ℕ) :
    IsMaxEnvIn (EnvOf (↑S : Set (ℤ × ℤ))) (canonA ξ xper vl (chB c s₀) (chU c s₀) i)
      (chA c s₀ i) :=
  isMaxEnvIn_of_stepHyp (c.hstep _) (chain c s₀ i).env (chain c s₀ i).agree

/-- **Collé item (ii)** for the chain: `[-i+1,i-1]² ∩ ℋ(ℓ^(−)) ⊆ B_i`. -/
theorem itemII_ch (s₀ : St ξ xper S nℓ cz) : ItemII (chB c s₀) nℓ cz := by
  intro i z h1 h2 hz
  cases i with
  | zero =>
    exfalso
    simp only [Nat.cast_zero, zero_sub] at h1
    linarith [abs_nonneg z.1]
  | succ i =>
    rw [chB_succ]
    refine (stepB_spec c _ i).2.2.1 ?_
    rw [Finset.mem_coe, mem_boxHP]
    push_cast at h1 h2
    refine ⟨?_, ?_, hz⟩ <;> constructor <;>
      linarith [abs_le.mp h1, abs_le.mp h2, le_abs_self z.1, neg_abs_le z.1, le_abs_self z.2,
        neg_abs_le z.2]

/-- `:495`, `⋃ A_i = ℋ(ℓ^(−))`, via Amink's `exhausts_of_itemII`. -/
theorem exhausts_ch (s₀ : St ξ xper S nℓ cz) : Exhausts (chA c s₀) nℓ cz :=
  exhausts_of_itemII c.hperp (le_dot_B_ch c s₀) (subBA_ch c s₀) (subStrip_ch c s₀)
    (itemII_ch c s₀)

end Step

/-! ### The seed

`:462`: an enveloped `B'` whose `ℓ`-support line is `ℓ^(−)`.  `𝒮_φ` itself, translated so that
its `⟪nℓ,·⟫`-minimum sits at level `cz`, qualifies; the translation exists because `nℓ` is
primitive (`dot_surjective`).  This is where `Primitive nℓ` enters — and the only place. -/

theorem suppVal_shift' {X : Set (ℤ × ℤ)} (hfin : X.Finite) (hne : X.Nonempty) (v m : ℤ × ℤ) :
    suppVal (shift v X) m = suppVal X m + dot m v := by
  obtain ⟨y, hy⟩ := face_nonempty hfin hne m
  have hmem : y + v ∈ face (shift v X) m := by
    rw [face_shift]
    show (y + v) - v ∈ face X m
    simpa using hy
  rw [suppVal_eq hmem, dot_add, suppVal_eq hy]

theorem exists_seed' (hS : LatticeConvex S) (hne : S.Nonempty) (hprim : Primitive nℓ)
    (hxper : xper ∈ orbitClosure ξ) : Nonempty (St ξ xper S nℓ cz) := by
  obtain ⟨w, hw⟩ := dot_surjective (prim_iff_primitive.mpr hprim)
    (cz + suppVal (↑S : Set (ℤ × ℤ)) (-nℓ))
  set B₀ : Set (ℤ × ℤ) := shift w (↑S : Set (ℤ × ℤ)) with hB₀
  have hfin : B₀.Finite := by
    rw [hB₀, shift_eq_image]; exact S.finite_toSet.image _
  obtain ⟨u₀, hu₀⟩ := Nivat.Colle36.exists_shift_agreeing_on_finite hxper hfin
  refine ⟨⟨B₀, envOf_shift w (envOf_coe_self hS), hfin, ?_, ?_, u₀, hu₀⟩⟩
  · obtain ⟨s, hs⟩ := hne
    exact ⟨s + w, by rw [hB₀, mem_shift_iff]; simpa using hs⟩
  · rw [hB₀, suppVal_shift' S.finite_toSet (by simpa using hne), dot_neg_left, hw]
    ring

end Nivat.AenvfixProbe

/-! ## Discharging `AbsorbHyp` via `Nivat.Absorb.exists_enveloped_absorbing`

原文：b3_colle2.txt:474 (item (ii), `B_i` grows in all directions while support line stays fixed).

The recursion's sole non-`StepHyp` ingredient is the absorbing enlargement at fixed support level.
`Nivat.Absorb.exists_enveloped_absorbing` (`Absorb.lean:389`, axioms clean, team-lead verified)
provides exactly this, with two additional edge conditions `hEU` and `hn` that are free from
finiteness and edge membership. -/

namespace Nivat.AenvfixProbe

open Nivat Nivat.LE2 Nivat.Colle35 Nivat.ColleReg4 Nivat.ChainAsm

/-- `AbsorbHyp` follows from `Nivat.Absorb.exists_enveloped_absorbing_bounded`.
原文：b3_colle2.txt:474 (item (ii), `B_i` grows absorbing prescribed finite sets). -/
theorem absorbHyp_of_mem_E {S : Finset (ℤ × ℤ)} {n : ℤ × ℤ}
    (hn : n ∈ Nivat.LE2.E (↑S : Set (ℤ × ℤ))) :
    AbsorbHyp (↑S : Set (ℤ × ℤ)) n :=
  fun B hEnv hfin hne harea F hF =>
    Nivat.Absorb.exists_enveloped_absorbing_bounded
      (Nivat.LE2.finite_E_of_finite S.finite_toSet) hEnv hfin hne harea hn F hF

/-- Smart constructor for `Ctx` with `habs` discharged via `absorbHyp_of_mem_E`.
原文：b3_colle2.txt:462-480 (items (i)+(ii)+(iii), the recursion hypotheses). -/
theorem Ctx.mk_of_mem_E {ξ xper : Config ℤ} {S : Finset (ℤ × ℤ)} {vl nℓ : ℤ × ℤ}
    (hstep : ∀ u₀, StepHyp ξ xper S vl u₀)
    (hnE : -nℓ ∈ Nivat.LE2.E (↑S : Set (ℤ × ℤ)))
    (hfin : ∀ B, EnvOf (↑S : Set (ℤ × ℤ)) B → B.Finite)
    (harea : ∀ B, EnvOf (↑S : Set (ℤ × ℤ)) B → PosArea B)
    (hxper : xper ∈ orbitClosure ξ)
    (hperp : dot nℓ vl = 0) :
    Ctx ξ xper S vl nℓ :=
  ⟨hstep, absorbHyp_of_mem_E hnE, hfin, harea, hxper, hperp⟩

/-! ## `AhatMono` from endpoint alignment

原文：b3_colle2.txt:488-492 (`g₁` is the final point of `A₁ ∩ ℓ⁻` along `ℓ⁻`, and `k_i` aligns
`Â_i`'s final point with `g₁`).

The "easy to see" (:492) that `Â_i ⊆ Â_j` for `i ≤ j` relies on endpoint alignment: all `Â_i`
have their `ℓ⁻`-intersection anchored at the same `g₁`, and extend in the `-v_ℓ` direction.
Combined with `A_i ⊆ A_j` (from `subBA`/`subAB`), this gives the monotonicity.

**Status**: The geometric intuition is clear, but the formal proof requires additional structure
that the recursion does not currently provide. See definition and gap analysis below. -/

/-- **Endpoint alignment** (原文:488): `g₁ ∈ A₁` is the final point of `A₁ ∩ ℓ⁻` w.r.t. the
orientation of `ℓ⁻`, and for each `i`, `k_i` is chosen so that the final point of
`(A_i - k_i v_ℓ) ∩ ℓ⁻` coincides with `g₁`.

Formally: `g₁` is on the support line `ℓ⁻ = {z | dot nℓ z = cz}`, lies in `Â₁ = hatOf A kk vl 1`,
and for each `i`, any point in `Â_i ∩ ℓ⁻` that is ahead of `g₁` along `+v_ℓ` direction does not
exist (i.e., `g₁` is maximal along `v_ℓ` within `Â_i ∩ ℓ⁻`). -/
def EndpointAligned (A : ℕ → Set (ℤ × ℤ)) (kk : ℕ → ℕ) (vl nℓ : ℤ × ℤ) (cz : ℤ) (g₁ : ℤ × ℤ) : Prop :=
  dot nℓ g₁ = cz ∧ g₁ ∈ hatOf A kk vl 1 ∧
  ∀ i, ∀ t : ℤ, (0 < t ∧ g₁ + t • vl ∈ hatOf A kk vl i ∧ dot nℓ (g₁ + t • vl) = cz) → False

/-- **Ray closure along `-v_ℓ`**: if `A` contains a point and a point further back along `-v_ℓ`,
it contains the entire segment between them.

⚠ **撤回 (2026-09-20, 集成者)：这条不是 `AhatMono` 的缺口，它在链上等价于 `A = ∅`。**
原稿 docstring 写它是 `ahatMono_of_endpointAligned` 的 missing geometric property——错了。
`Nivat.AhatMono.not_finite_of_rayClosedNeg`（`AhatMono.lean:291`，内核已证）表明：取 `s = 0`
时前提 `a - 0 • vl ∈ A` 自动成立，于是 `RayClosedNeg` 强制 `A` 含一条完整的 `-v_ℓ` 无穷射线，
与链上 `(A i).Finite` 矛盾。**不要再派工去生产这条。**

`AhatMono` 的真缺口由 `Nivat.AhatMono.ahatMono_iff_fwdAbsorb`（`AhatMono.lean:131`）给出，
是**前向**吸收 `∀ i ≤ j, ∀ z ∈ A i, z + ((kk j : ℤ) - kk i) • vl ∈ A j`（等价，不只是充分），
其生产路线走 `:402` Definition 3.2 的**尺寸**条款（同法扇 + 边长占优），不走射线闭包。 -/
def RayClosedNeg (A : Set (ℤ × ℤ)) (vl : ℤ × ℤ) : Prop :=
  ∀ a : ℤ × ℤ, a ∈ A → ∀ s t : ℕ, a - (s : ℤ) • vl ∈ A → s ≤ t → a - (t : ℤ) • vl ∈ A

end Nivat.AenvfixProbe

#print axioms Nivat.AenvfixProbe.suppVal_stepA
#print axioms Nivat.AenvfixProbe.maxA_ch
#print axioms Nivat.AenvfixProbe.itemII_ch
#print axioms Nivat.AenvfixProbe.exhausts_ch
#print axioms Nivat.AenvfixProbe.exists_seed'
#print axioms Nivat.AenvfixProbe.absorbHyp_of_mem_E
#print axioms Nivat.AenvfixProbe.Ctx.mk_of_mem_E
#print axioms Nivat.AenvfixProbe.stepB_spec
#print axioms Nivat.AenvfixProbe.stepB_growth
