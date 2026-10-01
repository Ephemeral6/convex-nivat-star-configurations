/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.ChainMax
import Nivat.External.Colle.ItemIIRec
import Nivat.External.Colle.ShellSweep
import Nivat.External.Colle.EnvTranslate
import Nivat.Defs.Config

/-!
# `AhatMono` — is `Â_i ⊆ Â_j` supplied by `b3_colle2.txt:486-500`?

`Nivat.ChainAsm.Aparts.ChainDataGeom.ofParts` (`ChainAssemble.lean:186`) carries the binder

    AhatMono : ∀ i j, i ≤ j → hatOf A kk vl i ⊆ hatOf A kk vl j

with no producer anywhere in the tree.

## Source reading (the question the task asked to settle first)

The paragraph `:486-500` says, verbatim:

* `:486` (Figure 5 caption) — `B₁ ⊂ A₁ ⊂ B₂ ⊂ A₂ ⊂ ⋯`, i.e. **monotonicity of the
  unshifted family `A`**;
* `:488` — the definition of `g₁` (final point of `A₁ ∩ ℓ⁻`), of `k_i` (the shift making the
  final point of `(A_i − k_i v⃗_ℓ) ∩ ℓ⁻` coincide with `g₁`), and `Â_i := A_i − k_i v⃗_ℓ`,
  `k₁ = 0` — i.e. **endpoint alignment**, formalized and produced by
  `Nivat.AItemFour.exists_endpoint_shift` (`AItemFour.lean:329`);
* `:490` — the agreement chain `(T^{k_i v⃗_ℓ + u_i}η)|Â_i = ⋯ = (T^{k_i v⃗_ℓ}x_per)|Â_i`;
* `:492-494` — "It is easy to see that each `Â_i` is a **maximal** set among all
  `E(𝒮_φ)`-enveloped sets `𝒯` such that `B_i − k_i v⃗_ℓ ⊂ 𝒯 ⊂ H_{B_i}(ℓ) − k_i v⃗_ℓ` and
  `(T^{k_i v⃗_ℓ + u_i}η)|𝒯 = (T^{k_i v⃗_ℓ}x_per)|𝒯`".  This is an assertion about
  **maximality of `Â_i`**, not about `Â_i ⊆ Â_j`; it is already formalized as
  `Nivat.Colle35.maximalHat_of_max` (`ChainMax.lean:118`);
* `:496` — passage to a subsequence on which `T^{k v⃗_ℓ}x_per = T^{k_i v⃗_ℓ}x_per`;
* `:498-506` — the edge-growth index `J`, and `Â_∞ := ⋃ Â_i`.

**`Â_i ⊆ Â_j` appears exactly once in the whole paper, in the Figure 6 caption at `:508`**
(`B₁ ⊂ Â₁ ⊂ Â₂ ⊂ ⋯ ⊂ Â_∞`).  It is stated in no sentence of the running text and argued
nowhere.  Its two downstream uses — `:506` ("`Â_∞` is a weakly `E(𝒮_φ)`-enveloped set") and
`:510` ("`ϑ_{i'}|Â_i = ϑ_i|Â_i` for all `i ≤ i'`") — both consume it.

So the task's alternative **(b)** holds: `:486-500` does not supply `AhatMono`.

## What is proved here

1. `kk_le_of_endpointAligned` — endpoint alignment plus monotone `A` does give **`kk` monotone**
   (`k_i ≤ k_j` for `1 ≤ i ≤ j`).  This is the part of the picture that is free, and it is the
   only consequence of `:488` that bears on `:508`.
2. `ahatMono_iff_fwdAbsorb` — `AhatMono` is **equivalent** to forward-shift absorption
   `∀ i ≤ j, ∀ z ∈ A i, z + (k_j − k_i) • v⃗_ℓ ∈ A j`.  Combined with (1) (`k_j − k_i ≥ 0`),
   this pins the missing ingredient exactly: `A_j` must absorb the `+v⃗_ℓ`-translate of `A_i`
   by the endpoint gap.  Plain `A_i ⊆ A_j` is the case `k_i = k_j`.
3. `not_ahatMono_of_enveloped` — a **kernel counterexample inside the hypotheses**.  Every
   `A i` is `EnvOf U`-enveloped for the concrete unit hexagon `U = ShellMink.hexA` (finite,
   `PosArea`), proved in the kernel via `ShellSweep.enveloped_hexShape`, and each `A i` is
   even `IsMaxEnvIn (EnvOf U) (A i) (A i)`.  On top of that, every hypothesis *and* every
   conclusion of `exists_endpoint_shift` holds — and `AhatMono` still fails.

   **Why the square fan is not a counterexample and the hexagon fan is.**  Write `h_i(n)` for
   the support number of `A_i`.  `A_i ⊆ A_j ⟺ h_i ≤ h_j` pointwise, and
   `Â_i ⊆ Â_j ⟺ h_i(n) − h_j(n) ≤ (k_i − k_j)·⟪n, v⃗_ℓ⟫` for every `n ∈ E(𝒮_φ)`.  For normals
   with `⟪n, v⃗_ℓ⟫ ≤ 0` the right side is `≥ 0` and the left is `≤ 0`, so those are free.
   Endpoint alignment pins exactly **one** normal on the `+v⃗_ℓ` side: the one adjacent to the
   `ℓ⁻` edge at `g₁`.  A box (`E = {±(1,0), ±(0,1)}`, `v⃗_ℓ = (1,0)`) has only that one normal
   with `⟪n, v⃗_ℓ⟫ > 0`, so `AhatMono` does hold there.  A hexagon has a **second** one, and it
   is unconstrained.  Here `v⃗_ℓ = (1,0)`, the pinned normal is `(1,-1)` (support `d`) and the
   free one is `(1,0)` (support `a`); the counterexample grows `d` without growing `a`.
4. `not_ahatMono_dropping_envelopedness` — the earlier, *off-target* version (superseded by 3,
   kept per `PROTOCOL.md` §14).  Its witness `{(0,0),(0,1)}` is a two-point segment, which is
   **not** `E(𝒮_φ)`-enveloped for any `𝒮_φ` of positive area, so it drops `ofParts`'s
   `maxA : ∀ i, IsMaxEnvIn Env (canonA …) (A i)` binder (`ChainAssemble.lean:180`).  Its name
   now says so.  It still shows that `A_i ⊆ A_j` alone never gives `AhatMono`.
5. `not_finite_of_rayClosedNeg` — the pre-existing candidate property
   `Nivat.AenvfixProbe.RayClosedNeg` (`ItemIIRec.lean:317`) is **unusable on this chain**: on a
   nonempty set it forces an infinite `−v⃗_ℓ` ray, whereas every `A_i` is finite
   (`exists_endpoint_shift`'s `hfin`).  It is therefore not the minimal extra hypothesis.

No new `Prop` or `structure` is introduced: (2)'s hypothesis is stated inline, and
`ceA`/`ceKK`/`eA`/`eKK` are counterexample data.
-/

namespace Nivat.AhatMono

open Nivat Nivat.LE2 Nivat.Colle35

/-! ## 1. What endpoint alignment does give: `kk` is monotone -/

/-- 原文：b3_colle2.txt:488

**`k_i ≤ k_j` for `1 ≤ i ≤ j`.**

> let `k_i ∈ ℕ` be such that the final point of `(A_i − k_i v⃗_ℓ) ∩ ℓ⁻` with respect to the
> orientation of `ℓ⁻` coincides with `g₁`

量词对应原文:
* `A`, `kk`, `vl`, `nℓ`, `cz`, `g₁` ↔ `A_i`, `k_i`, `v⃗_ℓ`, the normal of `ℓ⁻`, its level, `g₁`;
* `hperp` ↔ `v⃗_ℓ` is the direction of `ℓ`, so it is `nℓ`-orthogonal (`:488` uses `v⃗_ℓ` to
  translate *along* `ℓ⁻`);
* `hmono` ↔ `:486` Figure 5, `A₁ ⊂ A₂ ⊂ ⋯`;
* `halign` ↔ "the final point of `Â_i ∩ ℓ⁻` coincides with `g₁`", i.e. the conclusion of
  `Nivat.AItemFour.exists_endpoint_shift` (`AItemFour.lean:329`), verbatim.

No quantifier here is ours: the statement is a consequence of two source clauses only.
`:488`'s own "`k_i ∈ ℕ`" (rather than `∈ ℤ`) is the `i = 1` case, since `k₁ = 0`. -/
theorem kk_le_of_endpointAligned
    {A : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ} {vl nℓ g₁ : ℤ × ℤ} {cz : ℤ}
    (hperp : dot nℓ vl = 0) (hg₁ : dot nℓ g₁ = cz)
    (hmono : ∀ i j, i ≤ j → A i ⊆ A j)
    (halign : ∀ i, 1 ≤ i →
      IsGreatest {t : ℤ | g₁ + t • vl ∈ hatOf A kk vl i ∧ dot nℓ (g₁ + t • vl) = cz} 0)
    {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j) : kk i ≤ kk j := by
  have hexp : ∀ t : ℤ, dot nℓ (g₁ + t • vl) = dot nℓ g₁ + t * dot nℓ vl := by
    intro t
    simp only [dot, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  have hlev : ∀ t : ℤ, dot nℓ (g₁ + t • vl) = cz := by
    intro t
    rw [hexp, hperp, mul_zero, add_zero, hg₁]
  -- `g₁ ∈ Â_i`, i.e. `g₁ + k_i v⃗_ℓ ∈ A_i`.
  have h0 : g₁ + (0 : ℤ) • vl + (kk i : ℤ) • vl ∈ A i := (halign i hi).1.1
  have h1 : g₁ + (kk i : ℤ) • vl ∈ A i := by simpa using h0
  have h2 : g₁ + (kk i : ℤ) • vl ∈ A j := hmono i j hij h1
  -- Hence `g₁ + (k_i − k_j) v⃗_ℓ ∈ Â_j`, and it lies on `ℓ⁻`.
  have h3 : g₁ + ((kk i : ℤ) - (kk j : ℤ)) • vl ∈ hatOf A kk vl j := by
    show g₁ + ((kk i : ℤ) - (kk j : ℤ)) • vl + (kk j : ℤ) • vl ∈ A j
    have he : g₁ + ((kk i : ℤ) - (kk j : ℤ)) • vl + (kk j : ℤ) • vl
        = g₁ + (kk i : ℤ) • vl := by module
    rw [he]; exact h2
  have h4 : ((kk i : ℤ) - (kk j : ℤ)) ≤ 0 :=
    (halign j (le_trans hi hij)).2 ⟨h3, hlev _⟩
  omega

/-! ## 2. The exact missing ingredient -/

/-- 原文：b3_colle2.txt:508 (Figure 6 caption), the only occurrence of `Â_i ⊂ Â_j` in the paper.

**`AhatMono` ⟺ forward-shift absorption.**  Since `Â_i = A_i − k_i v⃗_ℓ`, the containment
`Â_i ⊆ Â_j` says exactly that `A_j` contains the translate of `A_i` by the endpoint gap
`(k_j − k_i) v⃗_ℓ`, which is a *forward* (`+v⃗_ℓ`) translate by `kk_le_of_endpointAligned`.

量词对应原文: both sides are pure restatements of `Â_i := A_i − k_i v⃗_ℓ` (`:488`) and of the
caption's `⊂`; nothing is added.  The caption's `B₁ ⊂ Â₁` is the `i = 1` instance combined
with `B₁ ⊂ A₁` (`:486`).

The right-hand side is strictly stronger than `A_i ⊆ A_j` (`:486`), which is the special case
`k_i = k_j`; `not_ahatMono_of_endpointAligned` below shows the gap is real. -/
theorem ahatMono_iff_fwdAbsorb (A : ℕ → Set (ℤ × ℤ)) (kk : ℕ → ℕ) (vl : ℤ × ℤ) :
    (∀ i j, i ≤ j → hatOf A kk vl i ⊆ hatOf A kk vl j) ↔
      (∀ i j, i ≤ j → ∀ z ∈ A i, z + ((kk j : ℤ) - (kk i : ℤ)) • vl ∈ A j) := by
  constructor
  · intro h i j hij z hz
    have hw : z - (kk i : ℤ) • vl ∈ hatOf A kk vl i := by
      show z - (kk i : ℤ) • vl + (kk i : ℤ) • vl ∈ A i
      simpa using hz
    have h2 : z - (kk i : ℤ) • vl + (kk j : ℤ) • vl ∈ A j := h i j hij hw
    have he : z - (kk i : ℤ) • vl + (kk j : ℤ) • vl
        = z + ((kk j : ℤ) - (kk i : ℤ)) • vl := by module
    rwa [he] at h2
  · intro h i j hij z hz
    have hz' : z + (kk i : ℤ) • vl ∈ A i := hz
    have h2 := h i j hij _ hz'
    show z + (kk j : ℤ) • vl ∈ A j
    have he : z + (kk i : ℤ) • vl + ((kk j : ℤ) - (kk i : ℤ)) • vl
        = z + (kk j : ℤ) • vl := by module
    rwa [he] at h2

/-! ## 3. The off-target counterexample (superseded by §5; kept per `PROTOCOL.md` §14)

`v⃗_ℓ = (1,0)`, `ℓ⁻ = {z | ⟪(0,1), z⟫ = 0}` is the `x`-axis, `g₁ = (0,0)`.

    A 0 = A 1 = {(0,0), (0,1)}          k₁ = 0      Â₁ = {(0,0), (0,1)}
    A i = {(0,0), (1,0), (0,1)}  (i ≥ 2) kᵢ = 1      Âᵢ = {(-1,0), (0,0), (-1,1)}

⚠ **This witness is not `E(𝒮_φ)`-enveloped.**  `A 1` is a two-point segment, so `PosArea (A 1)`
is false (`LatticeEdges.lean:235`) and Definition 3.2 (`:402`) cannot be met against any `𝒮_φ`
of positive area.  It therefore refutes only the statement with `ofParts`'s
`maxA : ∀ i, IsMaxEnvIn Env (canonA η xper vl B u i) (A i)` (`ChainAssemble.lean:180`) deleted —
hence the name.  `not_ahatMono_of_enveloped` (§5) is the version inside the hypotheses. -/

/-- Counterexample family for `AhatMono`.  `2 ≤ i` adds the extra `ℓ⁻`-point `(1,0)`. -/
def ceA : ℕ → Set (ℤ × ℤ) := fun i =>
  {z | (z.1 = 0 ∧ z.2 = 0) ∨ (z.1 = 0 ∧ z.2 = 1) ∨ (2 ≤ i ∧ z.1 = 1 ∧ z.2 = 0)}

/-- The endpoint shifts forced by `ceA`: `k₁ = 0`, `k_i = 1` for `i ≥ 2`. -/
def ceKK : ℕ → ℕ := fun i => if i ≤ 1 then 0 else 1

theorem mem_ceA (i : ℕ) (a b : ℤ) :
    ((a, b) : ℤ × ℤ) ∈ ceA i ↔
      ((a = 0 ∧ b = 0) ∨ (a = 0 ∧ b = 1) ∨ (2 ≤ i ∧ a = 1 ∧ b = 0)) := Iff.rfl

theorem ce_shift (z : ℤ × ℤ) (s : ℤ) :
    z + s • ((1 : ℤ), (0 : ℤ)) = (z.1 + s, z.2) := by
  refine Prod.ext ?_ ?_ <;> simp

theorem ceKK_le (i : ℕ) : (ceKK i : ℤ) = if i ≤ 1 then 0 else 1 := by
  unfold ceKK; split_ifs <;> simp

/-- 原文：b3_colle2.txt:486-500 supply monotone `A` (`:486`) and endpoint alignment (`:488`);
`Â_i ⊆ Â_j` is asserted only in the `:508` figure caption.

⚠ **Scope, stated in the name**: this drops `ofParts`'s `maxA` binder
(`ChainAssemble.lean:180`), i.e. it does **not** assume the `A i` are `E(𝒮_φ)`-enveloped, and
the witness in fact is not.  What it does establish is that `:486` (`A_i ⊆ A_j`) plus `:488`
alone never suffice.  For the version that keeps envelopment see
`not_ahatMono_of_enveloped`.

量词对应原文 (every conjunct below is a hypothesis or conclusion of `exists_endpoint_shift`,
`AItemFour.lean:329`, unchanged): `hfin`/`hne`/`hnℓ`/`hperp`/`hvl`/`hprim`/`hmono` are its
hypotheses, `kk 1 = 0` / `dot nℓ g₁ = cz` / the `IsGreatest` family are its conclusions.
The extra `v⃗_ℓ`-segment conjunct is **weaker** than `E(𝒮_φ)`-envelopment (`:402`); it does not
substitute for it. -/
theorem not_ahatMono_dropping_envelopedness :
    ∃ (A : ℕ → Set (ℤ × ℤ)) (kk : ℕ → ℕ) (g₁ vl nℓ : ℤ × ℤ) (cz : ℤ),
      (∀ i, (A i).Finite) ∧
      (∀ i, (A i ∩ {z | dot nℓ z = cz}).Nonempty) ∧
      nℓ ≠ 0 ∧ dot nℓ vl = 0 ∧ vl ≠ 0 ∧ Primitive vl ∧
      (∀ i j, i ≤ j → A i ⊆ A j) ∧
      kk 1 = 0 ∧ dot nℓ g₁ = cz ∧
      (∀ i, 1 ≤ i →
        IsGreatest {t : ℤ | g₁ + t • vl ∈ hatOf A kk vl i ∧ dot nℓ (g₁ + t • vl) = cz} 0) ∧
      (∀ i, ∀ z : ℤ × ℤ, ∀ s r t : ℤ, s ≤ r → r ≤ t →
        z + s • vl ∈ A i → z + t • vl ∈ A i → z + r • vl ∈ A i) ∧
      ¬ (∀ i j, i ≤ j → hatOf A kk vl i ⊆ hatOf A kk vl j) := by
  classical
  refine ⟨ceA, ceKK, ((0 : ℤ), (0 : ℤ)), ((1 : ℤ), (0 : ℤ)), ((0 : ℤ), (1 : ℤ)), 0,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- finiteness
  · intro i
    refine Set.Finite.subset
      (Set.toFinite ({((0 : ℤ), (0 : ℤ)), ((0 : ℤ), (1 : ℤ)), ((1 : ℤ), (0 : ℤ))} :
        Set (ℤ × ℤ))) ?_
    rintro z (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨-, h1, h2⟩) <;>
      simp [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.ext_iff, h1, h2]
  -- each `A i` meets `ℓ⁻`
  · intro i
    exact ⟨((0 : ℤ), (0 : ℤ)), Or.inl ⟨rfl, rfl⟩, by simp [dot]⟩
  -- `nℓ ≠ 0`
  · simp [Prod.ext_iff]
  -- `⟪nℓ, v⃗_ℓ⟫ = 0`
  · simp [dot]
  -- `v⃗_ℓ ≠ 0`
  · simp [Prod.ext_iff]
  -- `v⃗_ℓ` primitive
  · exact isCoprime_one_left
  -- monotone
  · rintro i j hij z (h | h | ⟨hi2, h⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨le_trans hi2 hij, h⟩)
  -- `k₁ = 0`
  · rfl
  -- `g₁` on `ℓ⁻`
  · simp [dot]
  -- endpoint alignment at every `i ≥ 1`
  · intro i hi
    have hpt : ∀ t : ℤ,
        ((0 : ℤ), (0 : ℤ)) + t • ((1 : ℤ), (0 : ℤ)) + (ceKK i : ℤ) • ((1 : ℤ), (0 : ℤ))
          = ((t + (ceKK i : ℤ) : ℤ), (0 : ℤ)) := by
      intro t; rw [ce_shift, ce_shift]; simp
    have hlev : ∀ t : ℤ,
        dot ((0 : ℤ), (1 : ℤ)) (((0 : ℤ), (0 : ℤ)) + t • ((1 : ℤ), (0 : ℤ))) = 0 := by
      intro t; rw [ce_shift]; simp [dot]
    have hmem : ∀ t : ℤ,
        (((0 : ℤ), (0 : ℤ)) + t • ((1 : ℤ), (0 : ℤ)) ∈ hatOf ceA ceKK ((1 : ℤ), (0 : ℤ)) i) ↔
          (t + (ceKK i : ℤ) = 0 ∨ (2 ≤ i ∧ t + (ceKK i : ℤ) = 1)) := by
      intro t
      show (((0 : ℤ), (0 : ℤ)) + t • ((1 : ℤ), (0 : ℤ))
        + (ceKK i : ℤ) • ((1 : ℤ), (0 : ℤ)) ∈ ceA i) ↔ _
      rw [hpt t, mem_ceA]
      constructor
      · rintro (⟨h1, -⟩ | ⟨-, h2⟩ | ⟨hi2, h1, -⟩)
        · exact Or.inl h1
        · exact absurd h2 (by norm_num)
        · exact Or.inr ⟨hi2, h1⟩
      · rintro (h1 | ⟨hi2, h1⟩)
        · exact Or.inl ⟨h1, rfl⟩
        · exact Or.inr (Or.inr ⟨hi2, h1, rfl⟩)
    have hk : (ceKK i : ℤ) = if i ≤ 1 then 0 else 1 := ceKK_le i
    constructor
    · refine ⟨(hmem 0).mpr ?_, hlev 0⟩
      rw [hk]
      split_ifs with h
      · exact Or.inl (by simp)
      · exact Or.inr ⟨by omega, by norm_num⟩
    · rintro t ⟨ht, -⟩
      have := (hmem t).mp ht
      rw [hk] at this
      split_ifs at this with h <;> omega
  -- `v⃗_ℓ`-segment closure of each `A i`
  · intro i z s r t hsr hrt hs ht
    rw [ce_shift] at hs ht ⊢
    rw [mem_ceA] at hs ht ⊢
    omega
  -- `AhatMono` fails: `(0,1) ∈ Â₁ \ Â₂`
  · intro h
    have h1 : ((0 : ℤ), (1 : ℤ)) ∈ hatOf ceA ceKK ((1 : ℤ), (0 : ℤ)) 1 := by
      show ((0 : ℤ), (1 : ℤ)) + (ceKK 1 : ℤ) • ((1 : ℤ), (0 : ℤ)) ∈ ceA 1
      rw [ce_shift, mem_ceA]
      norm_num [ceKK]
    have h2 := h 1 2 (by norm_num) h1
    have h3 : ((0 : ℤ), (1 : ℤ)) + (ceKK 2 : ℤ) • ((1 : ℤ), (0 : ℤ)) ∈ ceA 2 := h2
    rw [ce_shift, mem_ceA] at h3
    norm_num [ceKK] at h3

/-! ## 4. `RayClosedNeg` is not the missing hypothesis -/

/-- `Nivat.AenvfixProbe.RayClosedNeg` (`ItemIIRec.lean:317`) is recorded there as "the missing
geometric property for `ahatMono_of_endpointAligned`".  It is not usable: taking `s = 0` in its
statement makes the premise `a - 0 • v⃗_ℓ ∈ A` free, so a nonempty `A` must contain the whole
backward ray `{a - t v⃗_ℓ : t ∈ ℕ}`, which is infinite.  Every `A i` on the chain is finite
(`exists_endpoint_shift`'s `hfin`, from `:472`/`:484`), so `RayClosedNeg (A i) v⃗_ℓ` forces
`A i = ∅`. -/
theorem not_finite_of_rayClosedNeg {A : Set (ℤ × ℤ)} {vl : ℤ × ℤ}
    (hvl : vl ≠ 0) (hA : A.Nonempty)
    (h : Nivat.AenvfixProbe.RayClosedNeg A vl) : ¬ A.Finite := by
  obtain ⟨a, ha⟩ := hA
  have hall : ∀ t : ℕ, a - (t : ℤ) • vl ∈ A := by
    intro t
    refine h a ha 0 t ?_ (Nat.zero_le t)
    simpa using ha
  have hinj : Function.Injective (fun t : ℕ => a - (t : ℤ) • vl) := by
    intro s t hst
    simp only [sub_right_inj] at hst
    have hz : ((s : ℤ) - (t : ℤ)) • vl = 0 := by rw [sub_smul, hst, sub_self]
    rcases smul_eq_zero.mp hz with h' | h'
    · exact_mod_cast sub_eq_zero.mp h'
    · exact absurd h' hvl
  exact Set.infinite_of_injective_forall_mem hinj hall

/-! ## 5. The counterexample **inside** the envelopment hypotheses

Everything here uses `Nivat.ShellSweep.hexShape a b c d e = {0 ≤ x ≤ a, -e ≤ y ≤ b,
-c ≤ x - y ≤ d}` (`ShellSweep.lean:101`) and its kernel envelopment producer
`Nivat.ShellSweep.enveloped_hexShape` (`ShellSweep.lean:266`).

    U   := ShellMink.hexA = hexShape 2 2 1 1 0     the unit hexagon, 7 lattice points
    A 0 = A 1 := hexShape 3 3 2 1 0                 {0≤x≤3, 0≤y≤3, -2 ≤ x-y ≤ 1}
    A i       := hexShape 3 3 2 2 0   (i ≥ 2)       {0≤x≤3, 0≤y≤3, -2 ≤ x-y ≤ 2}

`nℓ = (0,1)`, `cz = 0`, so `ℓ⁻ = {y = 0}`; `v⃗_ℓ = (1,0)` is the direction of that bottom edge.
`A 1 ∩ ℓ⁻ = [0,1]×{0}` and `A 2 ∩ ℓ⁻ = [0,2]×{0}`, so `g₁ = (1,0)`, `k₁ = 0`, `k₂ = 1`.
Only the parameter `d` (the support number of the normal `(1,-1)`) grows; `a` (the support
number of `(1,0)`) does not.  Endpoint alignment pins `d`, so the shift `k₂ = 1` moves the
whole set back by `(1,0)` while `a` stays put:

    (3,3) ∈ Â₁ = A 1   but   (3,3) + (1,0) = (4,3) ∉ A 2 = Â₂ + (1,0).

Both parameter tuples are `Nondeg` (every edge carries ≥ 2 lattice points), which is what
Definition 3.2's `|w ∩ 𝒰| ≤ |ϖ ∩ 𝒯|` demands against the unit hexagon. -/

/-- Counterexample family for `AhatMono`, **enveloped** by the unit hexagon. -/
def eA : ℕ → Set (ℤ × ℤ) := fun i =>
  if i ≤ 1 then Nivat.ShellSweep.hexShape 3 3 2 1 0 else Nivat.ShellSweep.hexShape 3 3 2 2 0

/-- The endpoint shifts forced by `eA`: `k₁ = 0`, `k_i = 1` for `i ≥ 2`. -/
def eKK : ℕ → ℕ := fun i => if i ≤ 1 then 0 else 1

theorem finite_hexShape (a b c d e : ℤ) : (Nivat.ShellSweep.hexShape a b c d e).Finite := by
  refine Set.Finite.subset ((Set.finite_Icc (0 : ℤ) a).prod (Set.finite_Icc (-e) b)) ?_
  rintro z ⟨h1, h2, h3, h4, -, -⟩
  exact Set.mem_prod.mpr ⟨Set.mem_Icc.mpr ⟨h1, h2⟩, Set.mem_Icc.mpr ⟨h3, h4⟩⟩

theorem finite_hexA : (Nivat.ShellMink.hexA).Finite := by
  rw [Nivat.ShellSweep.hexA_eq_hexShape]; exact finite_hexShape 2 2 1 1 0

/-- `conv(U)` has positive area, as Definition 3.2 (`b3_colle2.txt:402`) requires of `𝒮_φ`. -/
theorem posArea_hexA : PosArea (Nivat.ShellMink.hexA) := by
  rw [Nivat.ShellSweep.hexA_eq_hexShape]
  refine ⟨((0 : ℤ), (0 : ℤ)), by simp only [Nivat.ShellSweep.mem_hexShape]; omega,
    ((1 : ℤ), (0 : ℤ)), by simp only [Nivat.ShellSweep.mem_hexShape]; omega,
    ((1 : ℤ), (1 : ℤ)), by simp only [Nivat.ShellSweep.mem_hexShape]; omega, ?_⟩
  simp [det]

theorem nondeg_eA1 : Nivat.ShellSweep.Nondeg 3 3 2 1 0 :=
  ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

theorem nondeg_eA2 : Nivat.ShellSweep.Nondeg 3 3 2 2 0 :=
  ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- **Every member of the family is `E(hexA)`-enveloped**, in the kernel, via
`ShellSweep.enveloped_hexShape`. -/
theorem enveloped_eA (i : ℕ) : EnvOf (Nivat.ShellMink.hexA) (eA i) := by
  unfold eA
  split_ifs
  · exact Nivat.ShellSweep.enveloped_hexShape nondeg_eA1
      Nivat.ShellSweep.E_hexA_eq Nivat.ShellSweep.encard_face_hexA_le
  · exact Nivat.ShellSweep.enveloped_hexShape nondeg_eA2
      Nivat.ShellSweep.E_hexA_eq Nivat.ShellSweep.encard_face_hexA_le

theorem mem_eA (i : ℕ) (z : ℤ × ℤ) :
    z ∈ eA i ↔
      (0 ≤ z.1 ∧ z.1 ≤ 3 ∧ 0 ≤ z.2 ∧ z.2 ≤ 3 ∧ -2 ≤ z.1 - z.2 ∧
        z.1 - z.2 ≤ (if i ≤ 1 then 1 else 2)) := by
  unfold eA
  split_ifs with h <;> simp only [Nivat.ShellSweep.mem_hexShape] <;> constructor <;>
    intro hz <;> omega

theorem eKK_cast (i : ℕ) : (eKK i : ℤ) = if i ≤ 1 then 0 else 1 := by
  unfold eKK; split_ifs <;> simp

/-- 原文：b3_colle2.txt:486-500 (`:486` monotone `A`, `:488` endpoint alignment) together with
`:402`/`:484` (`A_i` is `E(𝒮_φ)`-enveloped).  **All of them hold here and `AhatMono` still
fails.**

量词对应原文, conjunct by conjunct:
* `U.Finite`, `PosArea U` ↔ Definition 3.2's "`𝒰 ⊂ ℤ²` a finite, convex set such that
  `conv(𝒰)` has positive area" (`:402`);
* `∀ i, EnvOf U (A i)` ↔ "`A_i` is … among all `E(𝒮_φ)`-enveloped sets" (`:484`), the
  envelopedness half of `ofParts`'s `maxA` binder (`ChainAssemble.lean:180`);
* `∀ i, IsMaxEnvIn (EnvOf U) (A i) (A i)` ↔ "`A_i` is a **maximal** set … among all …"
  (`:484`).  ⚠ The constraint set here is `A i` itself, not `canonA η x_per v⃗_ℓ B u i`; see
  the file report — pinning `canonA` needs `η`, `x_per`, `B`, `u` and is not done;
* the remaining conjuncts are, verbatim, the hypotheses and the conclusions of
  `Nivat.AItemFour.exists_endpoint_shift` (`AItemFour.lean:329`).

Nothing is strengthened relative to the source; the only gap the other way is the `canonA`
clause noted above. -/
theorem not_ahatMono_of_enveloped :
    ∃ (U : Set (ℤ × ℤ)) (A : ℕ → Set (ℤ × ℤ)) (kk : ℕ → ℕ) (g₁ vl nℓ : ℤ × ℤ) (cz : ℤ),
      U.Finite ∧ PosArea U ∧
      (∀ i, EnvOf U (A i)) ∧
      (∀ i, IsMaxEnvIn (EnvOf U) (A i) (A i)) ∧
      (∀ i, (A i).Finite) ∧
      (∀ i, (A i ∩ {z | dot nℓ z = cz}).Nonempty) ∧
      nℓ ≠ 0 ∧ dot nℓ vl = 0 ∧ vl ≠ 0 ∧ Primitive vl ∧
      (∀ i j, i ≤ j → A i ⊆ A j) ∧
      kk 1 = 0 ∧ dot nℓ g₁ = cz ∧
      (∀ i, 1 ≤ i →
        IsGreatest {t : ℤ | g₁ + t • vl ∈ hatOf A kk vl i ∧ dot nℓ (g₁ + t • vl) = cz} 0) ∧
      ¬ (∀ i j, i ≤ j → hatOf A kk vl i ⊆ hatOf A kk vl j) := by
  classical
  refine ⟨Nivat.ShellMink.hexA, eA, eKK, ((1 : ℤ), (0 : ℤ)), ((1 : ℤ), (0 : ℤ)),
    ((0 : ℤ), (1 : ℤ)), 0, finite_hexA, posArea_hexA, enveloped_eA, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  -- maximal in its own constraint set
  · exact fun i => ⟨enveloped_eA i, subset_rfl, fun _ _ _ hTA => hTA⟩
  -- finiteness
  · intro i; unfold eA; split_ifs <;> exact finite_hexShape _ _ _ _ _
  -- each `A i` meets `ℓ⁻`
  · intro i
    exact ⟨((0 : ℤ), (0 : ℤ)), (mem_eA i _).mpr (by split_ifs <;> norm_num), by simp [dot]⟩
  -- `nℓ ≠ 0`
  · simp [Prod.ext_iff]
  -- `⟪nℓ, v⃗_ℓ⟫ = 0`
  · simp [dot]
  -- `v⃗_ℓ ≠ 0`
  · simp [Prod.ext_iff]
  -- `v⃗_ℓ` primitive
  · exact isCoprime_one_left
  -- monotone
  · intro i j hij z hz
    rw [mem_eA] at hz ⊢
    split_ifs at hz ⊢ <;> omega
  -- `k₁ = 0`
  · rfl
  -- `g₁` on `ℓ⁻`
  · simp [dot]
  -- endpoint alignment at every `i ≥ 1`
  · intro i hi
    have hmem : ∀ t : ℤ,
        (((1 : ℤ), (0 : ℤ)) + t • ((1 : ℤ), (0 : ℤ)) ∈ hatOf eA eKK ((1 : ℤ), (0 : ℤ)) i) ↔
          (0 ≤ 1 + t + (eKK i : ℤ) ∧ 1 + t + (eKK i : ℤ) ≤ 3 ∧
            -2 ≤ 1 + t + (eKK i : ℤ) ∧
            1 + t + (eKK i : ℤ) ≤ (if i ≤ 1 then 1 else 2)) := by
      intro t
      show (((1 : ℤ), (0 : ℤ)) + t • ((1 : ℤ), (0 : ℤ))
        + (eKK i : ℤ) • ((1 : ℤ), (0 : ℤ)) ∈ eA i) ↔ _
      rw [ce_shift, ce_shift, mem_eA]
      constructor <;> intro hz <;> simp only at * <;> omega
    have hlev : ∀ t : ℤ,
        dot ((0 : ℤ), (1 : ℤ)) (((1 : ℤ), (0 : ℤ)) + t • ((1 : ℤ), (0 : ℤ))) = 0 := by
      intro t; rw [ce_shift]; simp [dot]
    have hk : (eKK i : ℤ) = if i ≤ 1 then 0 else 1 := eKK_cast i
    constructor
    · refine ⟨(hmem 0).mpr ?_, hlev 0⟩
      rw [hk]; split_ifs <;> norm_num
    · rintro t ⟨ht, -⟩
      have h5 := (hmem t).mp ht
      rw [hk] at h5
      split_ifs at h5 <;> omega
  -- `AhatMono` fails: `(3,3) ∈ Â₁ \ Â₂`
  · intro h
    have h1 : ((3 : ℤ), (3 : ℤ)) ∈ hatOf eA eKK ((1 : ℤ), (0 : ℤ)) 1 := by
      show ((3 : ℤ), (3 : ℤ)) + (eKK 1 : ℤ) • ((1 : ℤ), (0 : ℤ)) ∈ eA 1
      rw [ce_shift, mem_eA]
      norm_num [eKK]
    have h2 := h 1 2 (by norm_num) h1
    have h3 : ((3 : ℤ), (3 : ℤ)) + (eKK 2 : ℤ) • ((1 : ℤ), (0 : ℤ)) ∈ eA 2 := h2
    rw [ce_shift, mem_eA] at h3
    norm_num [eKK] at h3

/-! ## 6. The normal-by-normal reduction: only `0 < ⟪n, v⃗_ℓ⟫` is at issue

`ahatMono_iff_fwdAbsorb` turns `AhatMono` into `z + c • v⃗_ℓ ∈ A j` for `z ∈ A i` and
`c = k_j − k_i ≥ 0` (`kk_le_of_endpointAligned`).  Feeding that through
`Nivat.LE2.mem_of_dot_le_suppVal` (`LatticeEdges.lean:1393`) leaves, for each edge normal
`n ∈ E (A j)`,

    dot n z + c * dot n v⃗_ℓ ≤ suppVal (A j) n.

For `dot n v⃗_ℓ ≤ 0` the added term is `≤ 0` and `dot n z ≤ suppVal (A i) n ≤ suppVal (A j) n`
closes it (`le_suppVal` + `suppVal_mono` on `A i ⊆ A j`).  This covers both the `= 0` case
(`n = ±nℓ`, by `AItemFour.det_eq_zero_of_dot_eq_zero`) and the `< 0` case, so the trichotomy
collapses to two branches.  Only `0 < dot n v⃗_ℓ` survives. -/

/-- **The reduction.**  `AhatMono` follows from slack on the `+v⃗_ℓ` normals alone.

原文：b3_colle2.txt:488 (`k_i`, used only through `hkk : kk` monotone, which is
`kk_le_of_endpointAligned`) and `:486` (`hmono`).  `hslack` has no counterpart in the paper —
it is the residual obligation, not a transcription, and `suppVal_slack_fails_at_enveloped`
below shows it is **not** free. -/
theorem ahatMono_of_suppVal_slack
    {A : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ} {vl : ℤ × ℤ}
    (hfin : ∀ i, (A i).Finite) (hne : ∀ i, (A i).Nonempty)
    (harea : ∀ i, PosArea (A i)) (hlc : ∀ i, IsLatticeConvexRegion (A i))
    (hmono : ∀ i j, i ≤ j → A i ⊆ A j)
    (hkk : ∀ i j, i ≤ j → kk i ≤ kk j)
    (hslack : ∀ i j, i ≤ j → ∀ n ∈ E (A j), 0 < dot n vl →
      suppVal (A i) n + ((kk j : ℤ) - (kk i : ℤ)) * dot n vl ≤ suppVal (A j) n) :
    ∀ i j, i ≤ j → hatOf A kk vl i ⊆ hatOf A kk vl j := by
  refine (ahatMono_iff_fwdAbsorb A kk vl).mpr ?_
  intro i j hij z hz
  set c : ℤ := (kk j : ℤ) - (kk i : ℤ) with hc
  have hc0 : 0 ≤ c := by have := hkk i j hij; omega
  refine mem_of_dot_le_suppVal (hfin j) (hne j) (harea j) (hlc j) ?_
  intro n hn
  have hexp : dot n (z + c • vl) = dot n z + c * dot n vl := by
    simp only [dot, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  have hzi : dot n z ≤ suppVal (A i) n := le_suppVal (hfin i) (hne i) hz
  rw [hexp]
  rcases le_or_gt (dot n vl) 0 with hsign | hsign
  · -- `⟪n, v⃗_ℓ⟫ ≤ 0`: the shift term is `≤ 0`, monotonicity of `suppVal` does the rest.
    have hterm : c * dot n vl ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc0 hsign
    have hij' : suppVal (A i) n ≤ suppVal (A j) n :=
      suppVal_mono (hfin i) (hne i) (hfin j) (hne j) (hmono i j hij) n
    omega
  · -- `0 < ⟪n, v⃗_ℓ⟫`: the residual hypothesis.
    have := hslack i j hij n hn hsign
    nlinarith [hzi, this]

/-- The same reduction with the normals ranged over a **fixed** `E U` rather than `E (A j)`.
This is the form a consumer wants: by `Nivat.LE2.Enveloped.E_eq` (`LatticeEdges.lean:1656`)
envelopedness (`b3_colle2.txt:484`, `ofParts`'s `maxA`) makes every `A i` share the edge set of
`𝒮_φ`, so `hslack` is a condition on finitely many normals independent of `i` and `j`. -/
theorem ahatMono_of_suppVal_slack_enveloped
    {U : Set (ℤ × ℤ)} {A : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ} {vl : ℤ × ℤ}
    (hEU : (E U).Finite) (henv : ∀ i, Enveloped U (A i))
    (hfin : ∀ i, (A i).Finite) (hne : ∀ i, (A i).Nonempty)
    (harea : ∀ i, PosArea (A i)) (hlc : ∀ i, IsLatticeConvexRegion (A i))
    (hmono : ∀ i j, i ≤ j → A i ⊆ A j)
    (hkk : ∀ i j, i ≤ j → kk i ≤ kk j)
    (hslack : ∀ i j, i ≤ j → ∀ n ∈ E U, 0 < dot n vl →
      suppVal (A i) n + ((kk j : ℤ) - (kk i : ℤ)) * dot n vl ≤ suppVal (A j) n) :
    ∀ i j, i ≤ j → hatOf A kk vl i ⊆ hatOf A kk vl j :=
  ahatMono_of_suppVal_slack hfin hne harea hlc hmono hkk
    (fun i j hij n hn => hslack i j hij n (by rwa [← (henv j).E_eq hEU]))

/-! ## 7. The residual case is not free

`not_ahatMono_of_enveloped` (§5) already settles the question the reduction leaves open: the
`0 < dot n v⃗_ℓ` branch **can fail on an `E(𝒮_φ)`-enveloped family**.  The two theorems below
make the connection explicit, at the offending normal `n = (1,0)` (which is the free `+v⃗_ℓ`
normal of the hexagon fan, the pinned one being `(1,-1)`). -/

theorem suppVal_eA_one_zero (i : ℕ) : suppVal (eA i) ((1 : ℤ), (0 : ℤ)) = 3 := by
  have hmem : ((3 : ℤ), (3 : ℤ)) ∈ face (eA i) ((1 : ℤ), (0 : ℤ)) := by
    refine ⟨(mem_eA i _).mpr (by split_ifs <;> norm_num), fun y hy => ?_⟩
    rw [mem_eA] at hy
    simp only [dot]
    split_ifs at hy <;> omega
  rw [suppVal_eq hmem]
  simp [dot]

/-- **The residual hypothesis of `ahatMono_of_suppVal_slack` fails on an enveloped family.**
At `i = 1`, `j = 2`, `n = v⃗_ℓ = (1,0)`: `suppVal (A 1) n = suppVal (A 2) n = 3` while the shift
term is `(k₂ − k₁) · ⟪n, v⃗_ℓ⟫ = 1`, so the inequality reads `4 ≤ 3`. -/
theorem suppVal_slack_fails_at_enveloped :
    0 < dot ((1 : ℤ), (0 : ℤ)) ((1 : ℤ), (0 : ℤ)) ∧
      ¬ (suppVal (eA 1) ((1 : ℤ), (0 : ℤ))
          + ((eKK 2 : ℤ) - (eKK 1 : ℤ)) * dot ((1 : ℤ), (0 : ℤ)) ((1 : ℤ), (0 : ℤ))
        ≤ suppVal (eA 2) ((1 : ℤ), (0 : ℤ))) := by
  rw [suppVal_eA_one_zero, suppVal_eA_one_zero]
  norm_num [dot, eKK]

/-! ## 8. `maxA` does **not** kill the witness

原文：b3_colle2.txt:484 —

> `A_i` is a maximal set with respect to partial ordering by inclusion among all
> `E(𝒮_φ)`-enveloped sets `𝒯 ⊂ ℤ²` such that `B_i ⊂ 𝒯 ⊂ H_{B_i}(ℓ)` and
> `(T^{u_i}η)|𝒯 = x_per|𝒯`

— transcribed in the build as `IsMaxEnvIn Env (canonA η x_per v⃗_ℓ B u i) (A i)`
(`ChainMax.lean:62`, `ChainCanon.lean:86`), which is `ofParts`'s `maxA` binder
(`ChainAssemble.lean:184`).  §5 left that binder undischarged; this section discharges it on
the **same** family `eA`, so `AhatMono` is not recoverable from the chain-side binders of
`ofParts`.

**How the maximality is met.**  Take `B_i := A_i` and separate the agreement windows along
the direction transverse to `v⃗_ℓ`: `u_i := (0, 100 i)`, `x_per :≡ true`, and `η` the indicator
of `⋃_j (A_j + u_j)`.  Every `A_j + u_j` lives in the horizontal band `0 ≤ y − 100 j ≤ 3`, and
`H_{B_i}(ℓ) + u_i` lives in `0 ≤ y − 100 i ≤ 3` because `v⃗_ℓ = (1,0)` does not move `y`; the
bands are 100 apart, so only `j = i` contributes and `canonA … i = A_i` **exactly**
(`canonA_eq`).  With the constraint set equal to `A_i`, `:484` maximality is immediate.

**量词对应原文** — no new `Prop` is introduced here; `canonA`, `IsMaxEnvIn`, `halfStrip` are
the existing transcriptions of `:484` and Definition 3.4, and the witnesses instantiate the
quantifiers `A_i`, `B_i`, `u_i`, `η`, `x_per` of that sentence.

⚠ **Binders NOT discharged, named explicitly** (the discipline this round is enforcing):
`ofParts` leaves `η` and `x_per` free — it carries **no** `x_per ∈ X_η` binder, and no binder
saying `η` is a minimal counterexample.  Those live upstream, in `exists_chainData`.  The
witness below uses that freedom: `x_per :≡ true` is **not** in `orbitClosure eEta` (arbitrarily
large all-`true` windows do not occur in `eEta`, whose support is a union of sets of diameter
`≤ 4` spaced 100 apart).  So what is refuted is exactly "the chain-side binders of
`ofParts` imply `AhatMono`", not "`exists_chainData` is unsatisfiable".  The shell/face/region
binders of `ofParts` are likewise not discharged. -/

/-- The shifts `u_i` of `:480`, chosen 100 apart transversally to `v⃗_ℓ = (1,0)` so that the
agreement windows of distinct stages cannot meet. -/
def eU : ℕ → ℤ × ℤ := fun i => ((0 : ℤ), 100 * (i : ℤ))

/-- `x_per` of `:484`, constant. -/
def eXper : Config Bool := fun _ => true

open Classical in
/-- `η` of `:484`: the indicator of `⋃_j (A_j + u_j)`. -/
noncomputable def eEta : Config Bool :=
  fun z => if ∃ j : ℕ, z - eU j ∈ eA j then true else false

theorem eEta_true_iff (z : ℤ × ℤ) : eEta z = true ↔ ∃ j : ℕ, z - eU j ∈ eA j := by
  classical
  unfold eEta
  split_ifs with h
  · simp [h]
  · simp [h]

theorem eU_sub_snd (w : ℤ × ℤ) (i j : ℕ) :
    (w + eU i - eU j).2 = w.2 + 100 * (i : ℤ) - 100 * (j : ℤ) := by
  simp [eU]

theorem finite_eA (i : ℕ) : (eA i).Finite := by
  unfold eA; split_ifs <;> exact finite_hexShape _ _ _ _ _

theorem mono_eA {i j : ℕ} (hij : i ≤ j) : eA i ⊆ eA j := by
  intro z hz
  rw [mem_eA] at hz ⊢
  split_ifs at hz ⊢ <;> omega

theorem meets_line_eA (i : ℕ) :
    (eA i ∩ {z : ℤ × ℤ | dot ((0 : ℤ), (1 : ℤ)) z = 0}).Nonempty :=
  ⟨((0 : ℤ), (0 : ℤ)), (mem_eA i _).mpr (by split_ifs <;> norm_num), by simp [dot]⟩

/-- `:488` endpoint alignment for the family, extracted from `not_ahatMono_of_enveloped`'s
proof so that §8 can reuse it. -/
theorem endpointAligned_eA (i : ℕ) (_hi : 1 ≤ i) :
    IsGreatest {t : ℤ | ((1 : ℤ), (0 : ℤ)) + t • ((1 : ℤ), (0 : ℤ)) ∈
        hatOf eA eKK ((1 : ℤ), (0 : ℤ)) i ∧
      dot ((0 : ℤ), (1 : ℤ)) (((1 : ℤ), (0 : ℤ)) + t • ((1 : ℤ), (0 : ℤ))) = 0} 0 := by
  have hmem : ∀ t : ℤ,
      (((1 : ℤ), (0 : ℤ)) + t • ((1 : ℤ), (0 : ℤ)) ∈ hatOf eA eKK ((1 : ℤ), (0 : ℤ)) i) ↔
        (0 ≤ 1 + t + (eKK i : ℤ) ∧ 1 + t + (eKK i : ℤ) ≤ 3 ∧
          -2 ≤ 1 + t + (eKK i : ℤ) ∧
          1 + t + (eKK i : ℤ) ≤ (if i ≤ 1 then 1 else 2)) := by
    intro t
    show (((1 : ℤ), (0 : ℤ)) + t • ((1 : ℤ), (0 : ℤ))
      + (eKK i : ℤ) • ((1 : ℤ), (0 : ℤ)) ∈ eA i) ↔ _
    rw [ce_shift, ce_shift, mem_eA]
    constructor <;> intro hz <;> simp only at * <;> omega
  have hlev : ∀ t : ℤ,
      dot ((0 : ℤ), (1 : ℤ)) (((1 : ℤ), (0 : ℤ)) + t • ((1 : ℤ), (0 : ℤ))) = 0 := by
    intro t; rw [ce_shift]; simp [dot]
  have hk : (eKK i : ℤ) = if i ≤ 1 then 0 else 1 := eKK_cast i
  constructor
  · refine ⟨(hmem 0).mpr ?_, hlev 0⟩
    rw [hk]; split_ifs <;> norm_num
  · rintro t ⟨ht, -⟩
    have h5 := (hmem t).mp ht
    rw [hk] at h5
    split_ifs at h5 <;> omega

/-- `AhatMono` fails on the family: `(3,3) ∈ Â₁` but `(3,3) + (1,0) = (4,3) ∉ A₂`. -/
theorem not_ahatMono_eA :
    ¬ (∀ i j, i ≤ j → hatOf eA eKK ((1 : ℤ), (0 : ℤ)) i ⊆
        hatOf eA eKK ((1 : ℤ), (0 : ℤ)) j) := by
  intro h
  have h1 : ((3 : ℤ), (3 : ℤ)) ∈ hatOf eA eKK ((1 : ℤ), (0 : ℤ)) 1 := by
    show ((3 : ℤ), (3 : ℤ)) + (eKK 1 : ℤ) • ((1 : ℤ), (0 : ℤ)) ∈ eA 1
    rw [ce_shift, mem_eA]
    norm_num [eKK]
  have h3 : ((3 : ℤ), (3 : ℤ)) + (eKK 2 : ℤ) • ((1 : ℤ), (0 : ℤ)) ∈ eA 2 :=
    h 1 2 (by norm_num) h1
  rw [ce_shift, mem_eA] at h3
  norm_num [eKK] at h3

/-- **The constraint set of `:484` is exactly `A_i`.**  This is the whole content of §8: the
agreement clause `(T^{u_i}η)|𝒯 = x_per|𝒯` cuts the (infinite) half-strip `H_{B_i}(ℓ)` back
down to `A_i`, because the windows of distinct stages are 100 apart transversally to `v⃗_ℓ`. -/
theorem canonA_eq (i : ℕ) :
    Nivat.Colle35.canonA eEta eXper ((1 : ℤ), (0 : ℤ)) eA eU i = eA i := by
  ext w
  simp only [Nivat.Colle35.canonA, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hstrip, hagree⟩
    have hw2 : 0 ≤ w.2 ∧ w.2 ≤ 3 := by
      obtain ⟨b, hb, s, hws⟩ := hstrip
      rw [ce_shift] at hws
      have hb' := (mem_eA i b).mp hb
      subst hws
      exact ⟨hb'.2.2.1, hb'.2.2.2.1⟩
    have hagree' : eEta (w + eU i) = true := hagree
    obtain ⟨j, hj⟩ := (eEta_true_iff _).mp hagree'
    have hj' := (mem_eA j _).mp hj
    have hy : 0 ≤ (w + eU i - eU j).2 ∧ (w + eU i - eU j).2 ≤ 3 :=
      ⟨hj'.2.2.1, hj'.2.2.2.1⟩
    rw [eU_sub_snd] at hy
    have hij : i = j := by omega
    subst hij
    simpa using hj
  · intro hw
    refine ⟨Nivat.Colle35.subset_halfStrip _ _ hw, ?_⟩
    show eEta (w + eU i) = true
    rw [eEta_true_iff]
    exact ⟨i, by simpa using hw⟩

/-- **`:484` maximality holds on the counterexample family.**  With the constraint set equal
to `A_i` (`canonA_eq`), `IsMaxEnvIn` reduces to envelopedness of `A_i`. -/
theorem isMaxEnvIn_canonA_eA (i : ℕ) :
    Nivat.Colle35.IsMaxEnvIn (EnvOf (Nivat.ShellMink.hexA))
      (Nivat.Colle35.canonA eEta eXper ((1 : ℤ), (0 : ℤ)) eA eU i) (eA i) := by
  rw [canonA_eq i]
  exact ⟨enveloped_eA i, subset_rfl, fun _ _ _ hTC => hTC⟩

/-- **The chain-side binders of `ChainDataGeom.ofParts` do not imply `AhatMono`.**

原文：b3_colle2.txt:484 (`maxA`), `:486` (`subBA`/`subAB`, `A_i ⊆ A_j`), `:488` (endpoint
alignment, the producer of `kk`), `:402` (Definition 3.2, `U.Finite`/`PosArea U`/`EnvOf U`).
The conjuncts are, in order, `ofParts`'s `envShift`, `envB`, `maxA`, `subBA`, `subAB`
(`ChainAssemble.lean:181-186`), followed by the hypotheses of
`Nivat.AItemFour.exists_endpoint_shift` (`AItemFour.lean:329`) and its conclusions, and finally
the negation of `ofParts`'s `AhatMono` binder (`ChainAssemble.lean:187`).

Nothing is strengthened relative to the source.  What is **weaker** than the real producer is
named in the section docstring above: `η` and `x_per` are unconstrained here, exactly as in
`ofParts`, whereas `exists_chainData` additionally has `x_per ∈ X_η`. -/
theorem not_ahatMono_of_ofParts_chain_binders :
    ∃ (U : Set (ℤ × ℤ)) (η xper : Config Bool) (vl nℓ g₁ : ℤ × ℤ) (cz : ℤ)
      (B A : ℕ → Set (ℤ × ℤ)) (u : ℕ → ℤ × ℤ) (kk : ℕ → ℕ),
      U.Finite ∧ PosArea U ∧
      (∀ (v : ℤ × ℤ) (T : Set (ℤ × ℤ)), EnvOf U T → EnvOf U {z | z + v ∈ T}) ∧
      (∀ i, EnvOf U (B i)) ∧
      (∀ i, Nivat.Colle35.IsMaxEnvIn (EnvOf U)
        (Nivat.Colle35.canonA η xper vl B u i) (A i)) ∧
      (∀ i, B i ⊆ A i) ∧ (∀ i, A i ⊆ B (i + 1)) ∧
      (∀ i, EnvOf U (A i)) ∧ (∀ i, (A i).Finite) ∧
      (∀ i j, i ≤ j → A i ⊆ A j) ∧
      (∀ i, (A i ∩ {z | dot nℓ z = cz}).Nonempty) ∧
      nℓ ≠ 0 ∧ dot nℓ vl = 0 ∧ vl ≠ 0 ∧ Primitive vl ∧
      kk 1 = 0 ∧ dot nℓ g₁ = cz ∧
      (∀ i, 1 ≤ i →
        IsGreatest {t : ℤ | g₁ + t • vl ∈ hatOf A kk vl i ∧ dot nℓ (g₁ + t • vl) = cz} 0) ∧
      ¬ (∀ i j, i ≤ j → hatOf A kk vl i ⊆ hatOf A kk vl j) :=
  ⟨Nivat.ShellMink.hexA, eEta, eXper, ((1 : ℤ), (0 : ℤ)), ((0 : ℤ), (1 : ℤ)),
    ((1 : ℤ), (0 : ℤ)), 0, eA, eA, eU, eKK,
    finite_hexA, posArea_hexA, Nivat.Colle35.envOf_shift_mem _, enveloped_eA,
    isMaxEnvIn_canonA_eA, fun _ => subset_rfl, fun i => mono_eA (Nat.le_succ i),
    enveloped_eA, finite_eA, fun _ _ hij => mono_eA hij, meets_line_eA,
    by simp [Prod.ext_iff], by simp [dot], by simp [Prod.ext_iff], isCoprime_one_left, rfl,
    by simp [dot], endpointAligned_eA, not_ahatMono_eA⟩

/-! ## 9. Exhaustion does not force `AhatMono` either

原文：b3_colle2.txt:474 (item (ii), `B_i ⊇ [-i+1,i-1]² ∩ ℋ(ℓ^(−))`) and `:498`
(`⋃_{i=1}^∞ A_i = ℋ(ℓ^(−))`).  §5/§8's family is trapped in `[0,3]²`, so it says nothing about
a chain that grows.  This section rebuilds the refutation on a family that **does** grow in
every direction and exhausts the half plane, and `AhatMono` still fails.

**The family.**  With `n := max i 1`, stage `i` is the hexagon with

    x ∈ [-(n+1), Rx n],  y ∈ [0, 6n+6],  x - y ∈ [-(6n+6), n],   Rx n := if n ≤ 3 then 2n else 2n-2

— i.e. `hexShape (Rx n + n + 1) (6n+6) (5n+5) (2n+1) 0` translated by `(-(n+1), 0)`.  Five of
the six bounds grow linearly; the sixth, the right edge `Rx`, **stalls once**: `Rx 3 = Rx 4 = 6`.
Everything else keeps moving, so item (ii) and `:498` hold at every index.

**Why it breaks.**  The bottom edge at `y = 0` runs to `min (Rx n) n = n`, so
`k_i = n − 1` and `Δk = 1` across the stall — endpoint alignment reads the *slant* bound `n`,
which moved, while the *right* bound `Rx`, which did not, is what has to absorb the shift.
The point `(6,3) ∈ A_3` sits on the stalled right edge, and `(6,3) + (1,0) = (7,3) ∉ A_4`.

**The general reason, and this is the finding.**  Exhaustion is **centre-anchored**: it asks
`⋃ A_i` to cover every box around the origin, and any one stage may lag in any one direction as
long as a later one catches up.  `Â_i ⊆ Â_j` is **corner-anchored**: it asks `A_j` to contain a
translate of `A_i` pushed flush against the right end of `A_j`'s bottom edge — a target that
moves with `j`.  A family can satisfy the first at every index and fail the second at any index
where the bottom edge advances further than the right edge.  The two conditions are
independent, and `:474` does not imply the Figure 6 caption.

**量词对应原文** — no new `Prop`; `ItemII` (`ItemII.lean:80`) and `Exhausts` (`:96`) are the
existing transcriptions of `:474` and `:498`, and the witnesses instantiate `A_i`, `B_i`, `u_i`,
`k_i` of `:474`–`:498`.  As in §8, `η` and `x_per` are unconstrained — `ofParts` carries no
`x_per ∈ X_η` binder; that one is still not discharged. -/

/-- The right edge of stage `n`.  **It stalls once**: `xRx 3 = xRx 4 = 6`. -/
def xRx (n : ℕ) : ℤ := if n ≤ 3 then 2 * (n : ℤ) else 2 * (n : ℤ) - 2

/-- Stage index, floored at `1` so that stage `0` is a copy of stage `1` (`Nondeg` fails at
`n = 0`). -/
def xN (i : ℕ) : ℕ := max i 1

theorem one_le_xN (i : ℕ) : 1 ≤ xN i := le_max_right i 1

theorem xN_le_succ (i : ℕ) : xN i ≤ i + 1 := by unfold xN; omega

theorem xN_eq {i : ℕ} (hi : 1 ≤ i) : xN i = i := by unfold xN; omega

theorem xN_le_xRx (i : ℕ) : (xN i : ℤ) ≤ xRx (xN i) := by
  have h := one_le_xN i
  unfold xRx; split_ifs <;> omega

/-- The growing, exhausting counterexample family. -/
def xA (i : ℕ) : Set (ℤ × ℤ) :=
  Nivat.LE2.shift ((-((xN i : ℤ) + 1), (0 : ℤ)))
    (Nivat.ShellSweep.hexShape (xRx (xN i) + (xN i : ℤ) + 1) (6 * (xN i : ℤ) + 6)
      (5 * (xN i : ℤ) + 5) (2 * (xN i : ℤ) + 1) 0)

/-- The endpoint shifts: the bottom edge of stage `i` ends at `x = xN i`, so `k_i = xN i - 1`. -/
def xKK (i : ℕ) : ℕ := if i ≤ 1 then 0 else i - 1

theorem xKK_cast {i : ℕ} (hi : 1 ≤ i) : (xKK i : ℤ) = (i : ℤ) - 1 := by
  unfold xKK; split_ifs <;> omega

theorem mem_xA (i : ℕ) (z : ℤ × ℤ) :
    z ∈ xA i ↔
      (-((xN i : ℤ) + 1) ≤ z.1 ∧ z.1 ≤ xRx (xN i) ∧ 0 ≤ z.2 ∧ z.2 ≤ 6 * (xN i : ℤ) + 6 ∧
        -(6 * (xN i : ℤ) + 6) ≤ z.1 - z.2 ∧ z.1 - z.2 ≤ (xN i : ℤ)) := by
  simp only [xA, Nivat.LE2.mem_shift_iff, Nivat.ShellSweep.mem_hexShape, Prod.fst_sub,
    Prod.snd_sub]
  omega

theorem nondeg_xA (i : ℕ) :
    Nivat.ShellSweep.Nondeg (xRx (xN i) + (xN i : ℤ) + 1) (6 * (xN i : ℤ) + 6)
      (5 * (xN i : ℤ) + 5) (2 * (xN i : ℤ) + 1) 0 := by
  have h : 1 ≤ xN i := one_le_xN i
  have hc : (1 : ℤ) ≤ (xN i : ℤ) := by exact_mod_cast h
  unfold xRx
  split_ifs with hle
  · exact ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
  · have h4 : (4 : ℤ) ≤ (xN i : ℤ) := by
      have : 4 ≤ xN i := by omega
      exact_mod_cast this
    exact ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩

theorem enveloped_xA (i : ℕ) : EnvOf (Nivat.ShellMink.hexA) (xA i) :=
  Nivat.LE2.envOf_shift _ (Nivat.ShellSweep.enveloped_hexShape (nondeg_xA i)
    Nivat.ShellSweep.E_hexA_eq Nivat.ShellSweep.encard_face_hexA_le)

theorem finite_xA (i : ℕ) : (xA i).Finite := by
  refine Set.Finite.subset ((Set.finite_Icc (-((xN i : ℤ) + 1)) (xRx (xN i))).prod
    (Set.finite_Icc (0 : ℤ) (6 * (xN i : ℤ) + 6))) ?_
  intro z hz
  rw [mem_xA] at hz
  exact Set.mem_prod.mpr ⟨Set.mem_Icc.mpr ⟨hz.1, hz.2.1⟩, Set.mem_Icc.mpr ⟨hz.2.2.1, hz.2.2.2.1⟩⟩

theorem mono_xA {i j : ℕ} (hij : i ≤ j) : xA i ⊆ xA j := by
  intro z hz
  rw [mem_xA] at hz ⊢
  have hn : xN i ≤ xN j := by unfold xN; omega
  have hc : (xN i : ℤ) ≤ (xN j : ℤ) := by exact_mod_cast hn
  have h1 : 1 ≤ xN i := one_le_xN i
  have hc1 : (1 : ℤ) ≤ (xN i : ℤ) := by exact_mod_cast h1
  have hR : xRx (xN i) ≤ xRx (xN j) := by
    unfold xRx
    split_ifs with ha hb hb
    · omega
    · have : 4 ≤ xN j := by omega
      have : (4 : ℤ) ≤ (xN j : ℤ) := by exact_mod_cast this
      omega
    · omega
    · omega
  omega

/-- **Collé item (ii)** (`:474`) holds at every index: `[-i+1, i-1]² ∩ ℋ(ℓ^(−)) ⊆ A_i`. -/
theorem itemII_xA : ItemII xA ((0 : ℤ), (1 : ℤ)) 0 := by
  intro i z h1 h2 hz
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · exact absurd h1 (by push_cast; linarith [abs_nonneg z.1])
  · have hz' : (0 : ℤ) ≤ z.2 := by simpa [dot] using hz
    have hn : xN i = i := xN_eq hi
    have hci : (1 : ℤ) ≤ (i : ℤ) := by exact_mod_cast hi
    have hR : (i : ℤ) ≤ xRx i := by
      have h := xN_le_xRx i
      rwa [hn] at h
    rw [mem_xA, hn]
    have hb1 := abs_le.mp h1
    have hb2 := abs_le.mp h2
    refine ⟨by omega, by omega, hz', by omega, by omega, by omega⟩

/-- **`:498`**: the family exhausts the half plane `ℋ(ℓ^(−)) = {y ≥ 0}`. -/
theorem exhausts_xA : Exhausts xA ((0 : ℤ), (1 : ℤ)) 0 := by
  refine Set.Subset.antisymm ?_ itemII_xA.halfPlane_subset_iUnion
  intro z hz
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
  rw [mem_xA] at hi
  show (0 : ℤ) ≤ dot ((0 : ℤ), (1 : ℤ)) z
  simp only [dot]
  omega

theorem meets_line_xA (i : ℕ) :
    (xA i ∩ {z : ℤ × ℤ | dot ((0 : ℤ), (1 : ℤ)) z = 0}).Nonempty := by
  refine ⟨((0 : ℤ), (0 : ℤ)), ?_, by simp [dot]⟩
  rw [mem_xA]
  have h1 : 1 ≤ xN i := one_le_xN i
  have hc : (1 : ℤ) ≤ (xN i : ℤ) := by exact_mod_cast h1
  have hR := xN_le_xRx i
  exact ⟨by omega, by omega, le_refl _, by omega, by omega, by omega⟩

/-- `:488` endpoint alignment for the growing family: the bottom edge of `Â_i` ends at `g₁`. -/
theorem endpointAligned_xA (i : ℕ) (hi : 1 ≤ i) :
    IsGreatest {t : ℤ | ((1 : ℤ), (0 : ℤ)) + t • ((1 : ℤ), (0 : ℤ)) ∈
        hatOf xA xKK ((1 : ℤ), (0 : ℤ)) i ∧
      dot ((0 : ℤ), (1 : ℤ)) (((1 : ℤ), (0 : ℤ)) + t • ((1 : ℤ), (0 : ℤ))) = 0} 0 := by
  have hn : xN i = i := xN_eq hi
  have hk : (xKK i : ℤ) = (i : ℤ) - 1 := xKK_cast hi
  have hci : (1 : ℤ) ≤ (i : ℤ) := by exact_mod_cast hi
  have hR : (i : ℤ) ≤ xRx i := by
    have h := xN_le_xRx i
    rwa [hn] at h
  have hmem : ∀ t : ℤ,
      (((1 : ℤ), (0 : ℤ)) + t • ((1 : ℤ), (0 : ℤ)) ∈ hatOf xA xKK ((1 : ℤ), (0 : ℤ)) i) ↔
        (-((xN i : ℤ) + 1) ≤ 1 + t + (xKK i : ℤ) ∧ 1 + t + (xKK i : ℤ) ≤ xRx (xN i) ∧
          (0 : ℤ) ≤ 0 ∧ (0 : ℤ) ≤ 6 * (xN i : ℤ) + 6 ∧
          -(6 * (xN i : ℤ) + 6) ≤ 1 + t + (xKK i : ℤ) ∧ 1 + t + (xKK i : ℤ) ≤ (xN i : ℤ)) := by
    intro t
    show (((1 : ℤ), (0 : ℤ)) + t • ((1 : ℤ), (0 : ℤ))
      + (xKK i : ℤ) • ((1 : ℤ), (0 : ℤ)) ∈ xA i) ↔ _
    rw [ce_shift, ce_shift, mem_xA]
    constructor <;> intro hz <;> simp only at * <;> omega
  have hlev : ∀ t : ℤ,
      dot ((0 : ℤ), (1 : ℤ)) (((1 : ℤ), (0 : ℤ)) + t • ((1 : ℤ), (0 : ℤ))) = 0 := by
    intro t; rw [ce_shift]; simp [dot]
  constructor
  · exact ⟨(hmem 0).mpr (by rw [hn, hk]; refine ⟨by omega, by omega, le_refl _, by omega,
      by omega, by omega⟩), hlev 0⟩
  · rintro t ⟨ht, -⟩
    have h5 := (hmem t).mp ht
    rw [hn, hk] at h5
    omega

/-- `AhatMono` fails across the stall: `(6,3) ∈ A_3` sits on the stalled right edge and
`(6,3) + (1,0) = (7,3) ∉ A_4`. -/
theorem not_ahatMono_xA :
    ¬ (∀ i j, i ≤ j → hatOf xA xKK ((1 : ℤ), (0 : ℤ)) i ⊆
        hatOf xA xKK ((1 : ℤ), (0 : ℤ)) j) := by
  have hN3 : xN 3 = 3 := rfl
  have hN4 : xN 4 = 4 := rfl
  have hR3 : xRx 3 = 6 := by unfold xRx; norm_num
  have hR4 : xRx 4 = 6 := by unfold xRx; norm_num
  intro h
  have h1 : ((4 : ℤ), (3 : ℤ)) ∈ hatOf xA xKK ((1 : ℤ), (0 : ℤ)) 3 := by
    show ((4 : ℤ), (3 : ℤ)) + (xKK 3 : ℤ) • ((1 : ℤ), (0 : ℤ)) ∈ xA 3
    rw [ce_shift, mem_xA, hN3, hR3]
    norm_num [xKK]
  have h3 : ((4 : ℤ), (3 : ℤ)) + (xKK 4 : ℤ) • ((1 : ℤ), (0 : ℤ)) ∈ xA 4 :=
    h 3 4 (by norm_num) h1
  rw [ce_shift, mem_xA, hN4, hR4] at h3
  norm_num [xKK] at h3

/-! ### The `maxA` block for the growing family

The stages now have unbounded transverse extent (`y ≤ 6n+6`), so §8's fixed 100-apart window
separation no longer works; the offsets have to grow quadratically. -/

/-- The shifts `u_i`, quadratic so that the bands `[u_i.2, u_i.2 + 6·xN i + 6]` stay disjoint
even though the stages grow. -/
def xU : ℕ → ℤ × ℤ := fun i => ((0 : ℤ), 100 * (i : ℤ) * (i : ℤ))

def xXper : Config Bool := fun _ => true

open Classical in
noncomputable def xEta : Config Bool :=
  fun z => if ∃ j : ℕ, z - xU j ∈ xA j then true else false

theorem xEta_true_iff (z : ℤ × ℤ) : xEta z = true ↔ ∃ j : ℕ, z - xU j ∈ xA j := by
  classical
  unfold xEta
  split_ifs with h
  · simp [h]
  · simp [h]

theorem xU_sub_snd (w : ℤ × ℤ) (i j : ℕ) :
    (w + xU i - xU j).2 = w.2 + 100 * (i : ℤ) * (i : ℤ) - 100 * (j : ℤ) * (j : ℤ) := by
  simp [xU]

/-- **The bands are disjoint.**  This is the quadratic separation: a transverse coordinate
`t ≤ 6i+12` cannot survive the offset `100i² − 100j²` unless `i = j`. -/
theorem xU_sep {i j : ℕ} {t : ℤ} (h0 : 0 ≤ t) (h1 : t ≤ 6 * (i : ℤ) + 12)
    (h2 : 0 ≤ t + 100 * (i : ℤ) * (i : ℤ) - 100 * (j : ℤ) * (j : ℤ))
    (h3 : t + 100 * (i : ℤ) * (i : ℤ) - 100 * (j : ℤ) * (j : ℤ) ≤ 6 * (j : ℤ) + 12) :
    i = j := by
  by_contra hne
  have hi0 : (0 : ℤ) ≤ (i : ℤ) := Int.natCast_nonneg i
  have hj0 : (0 : ℤ) ≤ (j : ℤ) := Int.natCast_nonneg j
  rcases Nat.lt_or_ge i j with hlt | hge
  · have hij : (i : ℤ) + 1 ≤ (j : ℤ) := by exact_mod_cast hlt
    have key : 100 * (i : ℤ) * (i : ℤ) + 200 * (i : ℤ) + 100 ≤ 100 * (j : ℤ) * (j : ℤ) := by
      nlinarith [mul_nonneg (by linarith : (0 : ℤ) ≤ (j : ℤ) - (i : ℤ) - 1)
        (by linarith : (0 : ℤ) ≤ (j : ℤ) + (i : ℤ) + 1)]
    linarith
  · have hlt : j < i := lt_of_le_of_ne hge (fun h => hne h.symm)
    have hij : (j : ℤ) + 1 ≤ (i : ℤ) := by exact_mod_cast hlt
    have key : 100 * (j : ℤ) * (j : ℤ) + 200 * (j : ℤ) + 100 ≤ 100 * (i : ℤ) * (i : ℤ) := by
      nlinarith [mul_nonneg (by linarith : (0 : ℤ) ≤ (i : ℤ) - (j : ℤ) - 1)
        (by linarith : (0 : ℤ) ≤ (i : ℤ) + (j : ℤ) + 1)]
    linarith

/-- **The constraint set of `:484` is exactly `A_i`, for the growing family too.** -/
theorem canonA_eq_xA (i : ℕ) :
    Nivat.Colle35.canonA xEta xXper ((1 : ℤ), (0 : ℤ)) xA xU i = xA i := by
  ext w
  simp only [Nivat.Colle35.canonA, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hstrip, hagree⟩
    have hN : (xN i : ℤ) ≤ (i : ℤ) + 1 := by exact_mod_cast xN_le_succ i
    have hw2 : 0 ≤ w.2 ∧ w.2 ≤ 6 * (xN i : ℤ) + 6 := by
      obtain ⟨b, hb, s, hws⟩ := hstrip
      rw [ce_shift] at hws
      have hb' := (mem_xA i b).mp hb
      subst hws
      exact ⟨hb'.2.2.1, hb'.2.2.2.1⟩
    have hagree' : xEta (w + xU i) = true := hagree
    obtain ⟨j, hj⟩ := (xEta_true_iff _).mp hagree'
    have hj' := (mem_xA j _).mp hj
    have hNj : (xN j : ℤ) ≤ (j : ℤ) + 1 := by exact_mod_cast xN_le_succ j
    have hy : 0 ≤ (w + xU i - xU j).2 ∧ (w + xU i - xU j).2 ≤ 6 * (xN j : ℤ) + 6 :=
      ⟨hj'.2.2.1, hj'.2.2.2.1⟩
    rw [xU_sub_snd] at hy
    have hij : i = j := xU_sep hw2.1 (by omega) hy.1 (by omega)
    subst hij
    simpa using hj
  · intro hw
    refine ⟨Nivat.Colle35.subset_halfStrip _ _ hw, ?_⟩
    show xEta (w + xU i) = true
    rw [xEta_true_iff]
    exact ⟨i, by simpa using hw⟩

theorem isMaxEnvIn_canonA_xA (i : ℕ) :
    Nivat.Colle35.IsMaxEnvIn (EnvOf (Nivat.ShellMink.hexA))
      (Nivat.Colle35.canonA xEta xXper ((1 : ℤ), (0 : ℤ)) xA xU i) (xA i) := by
  rw [canonA_eq_xA i]
  exact ⟨enveloped_xA i, subset_rfl, fun _ _ _ hTC => hTC⟩

/-- **Exhaustion does not force `AhatMono`.**

原文: `:402` (Definition 3.2), `:474` (item (ii)), `:484` (`maxA`), `:486` (`A_i ⊆ A_j`),
`:488` (endpoint alignment), `:498` (`⋃ A_i = ℋ(ℓ^(−))`).  Every one of them holds on the
witness, in the kernel, and `AhatMono` — which the source asserts only in the caption of
Figure 6 — fails at `i = 3`, `j = 4`.

The conjuncts are, in order: Definition 3.2's conditions on `𝒰`; `ofParts`'s `envShift`,
`envB`, `maxA`, `subBA`, `subAB` (`ChainAssemble.lean:181-186`); envelopedness, finiteness and
monotonicity of the `A_i`; **`ItemII`** (`:474`) and **`Exhausts`** (`:498`); the hypotheses of
`Nivat.AItemFour.exists_endpoint_shift` (`AItemFour.lean:329`) and its conclusions; and the
negation of `AhatMono` (`ChainAssemble.lean:187`).

⚠ Not discharged, same as §8: `ofParts` has no `x_per ∈ X_η` binder, and `xXper ≡ true` is not
in `orbitClosure xEta`. -/
theorem not_ahatMono_of_exhausting_chain :
    ∃ (U : Set (ℤ × ℤ)) (η xper : Config Bool) (vl nℓ g₁ : ℤ × ℤ) (cz : ℤ)
      (B A : ℕ → Set (ℤ × ℤ)) (u : ℕ → ℤ × ℤ) (kk : ℕ → ℕ),
      U.Finite ∧ PosArea U ∧
      (∀ (v : ℤ × ℤ) (T : Set (ℤ × ℤ)), EnvOf U T → EnvOf U {z | z + v ∈ T}) ∧
      (∀ i, EnvOf U (B i)) ∧
      (∀ i, Nivat.Colle35.IsMaxEnvIn (EnvOf U)
        (Nivat.Colle35.canonA η xper vl B u i) (A i)) ∧
      (∀ i, B i ⊆ A i) ∧ (∀ i, A i ⊆ B (i + 1)) ∧
      (∀ i, EnvOf U (A i)) ∧ (∀ i, (A i).Finite) ∧
      (∀ i j, i ≤ j → A i ⊆ A j) ∧
      ItemII B nℓ cz ∧ Exhausts A nℓ cz ∧
      (∀ i, (A i ∩ {z | dot nℓ z = cz}).Nonempty) ∧
      nℓ ≠ 0 ∧ dot nℓ vl = 0 ∧ vl ≠ 0 ∧ Primitive vl ∧
      kk 1 = 0 ∧ dot nℓ g₁ = cz ∧
      (∀ i, 1 ≤ i →
        IsGreatest {t : ℤ | g₁ + t • vl ∈ hatOf A kk vl i ∧ dot nℓ (g₁ + t • vl) = cz} 0) ∧
      ¬ (∀ i j, i ≤ j → hatOf A kk vl i ⊆ hatOf A kk vl j) :=
  ⟨Nivat.ShellMink.hexA, xEta, xXper, ((1 : ℤ), (0 : ℤ)), ((0 : ℤ), (1 : ℤ)),
    ((1 : ℤ), (0 : ℤ)), 0, xA, xA, xU, xKK,
    finite_hexA, posArea_hexA, Nivat.Colle35.envOf_shift_mem _, enveloped_xA,
    isMaxEnvIn_canonA_xA, fun _ => subset_rfl, fun i => mono_xA (Nat.le_succ i),
    enveloped_xA, finite_xA, fun _ _ hij => mono_xA hij, itemII_xA, exhausts_xA,
    meets_line_xA, by simp [Prod.ext_iff], by simp [dot], by simp [Prod.ext_iff],
    isCoprime_one_left, rfl, by simp [dot], endpointAligned_xA, not_ahatMono_xA⟩

/-! ## §10. The orbit-closure binder does not save `AhatMono` either

`ofParts` (`ChainAssemble.lean:176`) carries no constraint tying `η` to `x_per`; that constraint
lives one level up, in `exists_chainData`, as `x_per ∈ X_η` (`b3_colle2.txt:459`, "let `x_per` be
a doubly periodic configuration of `X_η`").  §8 and §9 leave it undischarged, which is the one
place a reader could still object that the counterexamples are about our encoding rather than
about the paper.  This section removes that objection.

**The obstruction, and the repair.**  `x_per ≡ true` belongs to `orbitClosure η` exactly when
`η` has arbitrarily large all-`true` windows (`Orbit.lean:43`: every finite `W` must be matched
by some translate).  §9's `xEta` has none — its `true` set is the union of the stages
`A_j + u_j`, each of transverse extent `≤ 6j+12`, and a large square must cross a band.

The repair is **not** to enlarge the stages but to exploit that §9's offsets are already
quadratic: the gap between band `j` and band `j+1` has height `≥ 194j+88`, which is *unbounded*.
So a `(k+1) × (k+1)` all-`true` square fits inside the `k`-th gap, for every `k`, and
`x_per ≡ true ∈ X_η` follows.  Constant spacing could not do this; the growing gap is the
load-bearing property, not a convenience.

Nothing else moves: `v⃗_ℓ = (1,0)` does not change `y`, so `H_{B_i}(ℓ) + u_i` stays inside its own
band, and `blk_sep` shows the bands and the squares are disjoint.  `canonA` is therefore still
cut down to exactly `A_i`, and `maxA` still holds.

**Reading.**  `AhatMono` is not a consequence of Definition 3.2, of `:484` maximality, of
endpoint alignment `:488`, of `A_i ⊆ A_j` `:486`, of item (ii) `:474` / `:498`, or of
`x_per ∈ X_η` `:459` — singly or jointly.  It is an independent assertion, and the source states
it only in the caption of Figure 6. -/

/-- The floor of the `k`-th gap: strictly above band `k`'s top (`100k²+6k+12`) and strictly
below band `k+1`'s bottom (`100(k+1)² = 100k²+200k+100`), with room for `k+1` rows. -/
def gapY (k : ℕ) : ℤ := 100 * (k : ℤ) * (k : ℤ) + 6 * (k : ℤ) + 13

/-- The `k`-th all-`true` square: `(k+1) × (k+1)`, parked in the `k`-th gap. -/
def blk (k : ℕ) : Set (ℤ × ℤ) :=
  {z | 0 ≤ z.1 ∧ z.1 ≤ (k : ℤ) ∧ gapY k ≤ z.2 ∧ z.2 ≤ gapY k + (k : ℤ)}

theorem mem_blk (k : ℕ) (z : ℤ × ℤ) :
    z ∈ blk k ↔ 0 ≤ z.1 ∧ z.1 ≤ (k : ℤ) ∧ gapY k ≤ z.2 ∧ z.2 ≤ gapY k + (k : ℤ) := Iff.rfl

/-- **The squares miss every band.**  A transverse coordinate `t ≤ 6i+12` offset by `100i²`
never lands in `[gapY k, gapY k + k]`. -/
theorem blk_sep {i k : ℕ} {t : ℤ} (h0 : 0 ≤ t) (h1 : t ≤ 6 * (i : ℤ) + 12)
    (h2 : gapY k ≤ t + 100 * (i : ℤ) * (i : ℤ))
    (h3 : t + 100 * (i : ℤ) * (i : ℤ) ≤ gapY k + (k : ℤ)) : False := by
  unfold gapY at h2 h3
  have hi0 : (0 : ℤ) ≤ (i : ℤ) := Int.natCast_nonneg i
  have hk0 : (0 : ℤ) ≤ (k : ℤ) := Int.natCast_nonneg k
  rcases lt_trichotomy i k with hlt | heq | hgt
  · have hik : (i : ℤ) + 1 ≤ (k : ℤ) := by exact_mod_cast hlt
    have key : 100 * (i : ℤ) * (i : ℤ) + 200 * (i : ℤ) + 100 ≤ 100 * (k : ℤ) * (k : ℤ) := by
      nlinarith [mul_nonneg (by linarith : (0 : ℤ) ≤ (k : ℤ) - (i : ℤ) - 1)
        (by linarith : (0 : ℤ) ≤ (k : ℤ) + (i : ℤ) + 1)]
    linarith
  · subst heq; linarith
  · have hki : (k : ℤ) + 1 ≤ (i : ℤ) := by exact_mod_cast hgt
    have key : 100 * (k : ℤ) * (k : ℤ) + 200 * (k : ℤ) + 100 ≤ 100 * (i : ℤ) * (i : ℤ) := by
      nlinarith [mul_nonneg (by linarith : (0 : ℤ) ≤ (i : ℤ) - (k : ℤ) - 1)
        (by linarith : (0 : ℤ) ≤ (i : ℤ) + (k : ℤ) + 1)]
    linarith

open Classical in
/-- The repaired `η`: §9's stages, plus one all-`true` square per gap. -/
noncomputable def yEta : Config Bool :=
  fun z => if (∃ j : ℕ, z - xU j ∈ xA j) ∨ (∃ k : ℕ, z ∈ blk k) then true else false

theorem yEta_true_iff (z : ℤ × ℤ) :
    yEta z = true ↔ (∃ j : ℕ, z - xU j ∈ xA j) ∨ (∃ k : ℕ, z ∈ blk k) := by
  classical
  unfold yEta
  split_ifs with h
  · simp [h]
  · simp [h]

/-- **`x_per ≡ true` is in the orbit closure of `yEta`.**

原文：b3_colle2.txt:459 — `x_per ∈ X_η`.  Unwinding `Nivat.orbitClosure` (`Orbit.lean:43`):
every finite window `W` must occur as a window of a translate of `η`.  Since `x_per` is
constantly `true`, this says `η` has an all-`true` copy of every finite shape, and the square
`blk (2m)` — where `m` bounds `W` in both coordinates — is one. -/
theorem xXper_mem_orbitClosure_yEta : xXper ∈ orbitClosure yEta := by
  classical
  intro W
  obtain ⟨m, hm⟩ : ∃ m : ℕ, ∀ w ∈ W, w.1.natAbs ≤ m ∧ w.2.natAbs ≤ m := by
    refine ⟨W.sup (fun w => max w.1.natAbs w.2.natAbs), fun w hw => ?_⟩
    have h := Finset.le_sup (f := fun w : ℤ × ℤ => max w.1.natAbs w.2.natAbs) hw
    exact ⟨le_trans (le_max_left _ _) h, le_trans (le_max_right _ _) h⟩
  refine ⟨((m : ℤ), gapY (2 * m) + (m : ℤ)), fun w hw => ?_⟩
  obtain ⟨h1, h2⟩ := hm w hw
  have hc : ((2 * m : ℕ) : ℤ) = 2 * (m : ℤ) := by push_cast; ring
  show (true : Bool) = yEta _
  symm
  rw [yEta_true_iff]
  refine Or.inr ⟨2 * m, ?_⟩
  rw [mem_blk]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Prod.fst_add, Prod.snd_add, hc] <;> omega

/-- **`:484`'s constraint set is still exactly `A_i`** — the added squares are invisible to it. -/
theorem canonA_eq_yA (i : ℕ) :
    Nivat.Colle35.canonA yEta xXper ((1 : ℤ), (0 : ℤ)) xA xU i = xA i := by
  ext w
  simp only [Nivat.Colle35.canonA, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hstrip, hagree⟩
    have hN : (xN i : ℤ) ≤ (i : ℤ) + 1 := by exact_mod_cast xN_le_succ i
    have hw2 : 0 ≤ w.2 ∧ w.2 ≤ 6 * (xN i : ℤ) + 6 := by
      obtain ⟨b, hb, s, hws⟩ := hstrip
      rw [ce_shift] at hws
      have hb' := (mem_xA i b).mp hb
      subst hws
      exact ⟨hb'.2.2.1, hb'.2.2.2.1⟩
    have hsnd : (w + xU i).2 = w.2 + 100 * (i : ℤ) * (i : ℤ) := by simp [xU]
    have hagree' : yEta (w + xU i) = true := hagree
    rcases (yEta_true_iff _).mp hagree' with ⟨j, hj⟩ | ⟨k, hk⟩
    · have hj' := (mem_xA j _).mp hj
      have hNj : (xN j : ℤ) ≤ (j : ℤ) + 1 := by exact_mod_cast xN_le_succ j
      have hy : 0 ≤ (w + xU i - xU j).2 ∧ (w + xU i - xU j).2 ≤ 6 * (xN j : ℤ) + 6 :=
        ⟨hj'.2.2.1, hj'.2.2.2.1⟩
      rw [xU_sub_snd] at hy
      have hij : i = j := xU_sep hw2.1 (by omega) hy.1 (by omega)
      subst hij
      simpa using hj
    · exact absurd ((mem_blk k _).mp hk) (by
        rintro ⟨-, -, hlo, hhi⟩
        rw [hsnd] at hlo hhi
        exact blk_sep hw2.1 (by omega) hlo hhi)
  · intro hw
    refine ⟨Nivat.Colle35.subset_halfStrip _ _ hw, ?_⟩
    show yEta (w + xU i) = true
    rw [yEta_true_iff]
    exact Or.inl ⟨i, by simpa using hw⟩

theorem isMaxEnvIn_canonA_yA (i : ℕ) :
    Nivat.Colle35.IsMaxEnvIn (EnvOf (Nivat.ShellMink.hexA))
      (Nivat.Colle35.canonA yEta xXper ((1 : ℤ), (0 : ℤ)) xA xU i) (xA i) := by
  rw [canonA_eq_yA i]
  exact ⟨enveloped_xA i, subset_rfl, fun _ _ _ hTC => hTC⟩

/-- **`AhatMono` fails on a chain satisfying every binder, `x_per ∈ X_η` included.**

原文: `:402` (Definition 3.2), `:459` (`x_per ∈ X_η`), `:474` (item (ii)), `:484` (`maxA`),
`:486` (`A_i ⊆ A_j`), `:488` (endpoint alignment), `:498` (`⋃ A_i = ℋ(ℓ^(−))`).  Each holds on
this witness in the kernel; `AhatMono` — asserted in the source only in the caption of Figure 6,
and consumed at `:506`/`:510` — fails at `i = 3`, `j = 4`.

The conjuncts are, in order: `x_per ∈ X_η` (`Orbit.lean:43`); Definition 3.2's conditions on
`𝒰`; `ofParts`'s `envShift`, `envB`, `maxA`, `subBA`, `subAB` (`ChainAssemble.lean:181-186`);
envelopedness, finiteness and monotonicity of the `A_i`; `ItemII` (`ItemII.lean:80`) and
`Exhausts` (`:96`); the hypotheses and conclusions of `Nivat.AItemFour.exists_endpoint_shift`
(`AItemFour.lean:329`); and the negation of `AhatMono` (`ChainAssemble.lean:187`).

⚠ **Binders not discharged**, named rather than merely omitted: `η` here is an arbitrary
`Config Bool`, so nothing forces it to be a *minimal counterexample* in the sense of
`IsMinimalCounterexample` — the complexity bound `P_η(n,m) ≤ nm` of `:459`'s ambient hypothesis
is not asserted.  That is the only hypothesis of `exists_chainData` this witness does not meet;
it is also not a hypothesis of `ofParts`, and it constrains `η` alone, not the chain. -/
theorem not_ahatMono_of_ofParts_chain_binders_with_xper :
    ∃ (U : Set (ℤ × ℤ)) (η xper : Config Bool) (vl nℓ g₁ : ℤ × ℤ) (cz : ℤ)
      (B A : ℕ → Set (ℤ × ℤ)) (u : ℕ → ℤ × ℤ) (kk : ℕ → ℕ),
      xper ∈ orbitClosure η ∧
      U.Finite ∧ PosArea U ∧
      (∀ (v : ℤ × ℤ) (T : Set (ℤ × ℤ)), EnvOf U T → EnvOf U {z | z + v ∈ T}) ∧
      (∀ i, EnvOf U (B i)) ∧
      (∀ i, Nivat.Colle35.IsMaxEnvIn (EnvOf U)
        (Nivat.Colle35.canonA η xper vl B u i) (A i)) ∧
      (∀ i, B i ⊆ A i) ∧ (∀ i, A i ⊆ B (i + 1)) ∧
      (∀ i, EnvOf U (A i)) ∧ (∀ i, (A i).Finite) ∧
      (∀ i j, i ≤ j → A i ⊆ A j) ∧
      ItemII B nℓ cz ∧ Exhausts A nℓ cz ∧
      (∀ i, (A i ∩ {z | dot nℓ z = cz}).Nonempty) ∧
      nℓ ≠ 0 ∧ dot nℓ vl = 0 ∧ vl ≠ 0 ∧ Primitive vl ∧
      kk 1 = 0 ∧ dot nℓ g₁ = cz ∧
      (∀ i, 1 ≤ i →
        IsGreatest {t : ℤ | g₁ + t • vl ∈ hatOf A kk vl i ∧ dot nℓ (g₁ + t • vl) = cz} 0) ∧
      ¬ (∀ i j, i ≤ j → hatOf A kk vl i ⊆ hatOf A kk vl j) :=
  ⟨Nivat.ShellMink.hexA, yEta, xXper, ((1 : ℤ), (0 : ℤ)), ((0 : ℤ), (1 : ℤ)),
    ((1 : ℤ), (0 : ℤ)), 0, xA, xA, xU, xKK,
    xXper_mem_orbitClosure_yEta,
    finite_hexA, posArea_hexA, Nivat.Colle35.envOf_shift_mem _, enveloped_xA,
    isMaxEnvIn_canonA_yA, fun _ => subset_rfl, fun i => mono_xA (Nat.le_succ i),
    enveloped_xA, finite_xA, fun _ _ hij => mono_xA hij, itemII_xA, exhausts_xA,
    meets_line_xA, by simp [Prod.ext_iff], by simp [dot], by simp [Prod.ext_iff],
    isCoprime_one_left, rfl, by simp [dot], endpointAligned_xA, not_ahatMono_xA⟩

/-! ## §11. `AhatMono` along the `:498-504` subsequence

**Source, verbatim (`b3_colle2.txt:498-504`).**  Let `w_i(j) ∈ E(Â_i)` be the edge of `Â_i`
parallel to `ℓ_j`.  "Since `⋃ A_i = ℋ(ℓ⁻)`, let `ι+1 ≤ J ≤ ι+m-1` be the **smallest** integer
such that `|Â_i ∩ w_i(J)| < |Â_{i+1} ∩ w_{i+1}(J)|` for infinitely many `i`.  By passing to a
subsequence, we can assume this holds for all `i`.  If `J > ι+1`, we also may assume that
`|Â_i ∩ w_i(j)| = |Â_{i+1} ∩ w_{i+1}(j)|` for every `ι+1 ≤ j ≤ J-1` and all `i`."

So the paper does extract, and it extracts **before** the Figure 6 caption.  §8-§10 refute
`AhatMono` for the chain as given; this section asks the sharper question, whether it survives
the extraction.  For the fan all four counterexamples use, **it does**, and the reason is
structural rather than accidental.

**The mechanism.**  `ι+1` is the edge adjacent to the `ℓ`-edge at `g_1`, so the extraction
constrains the slant edge first.  Write `â_i` for the `(1,0)`-support of `Â_i`.

* Whichever `J` is, the extraction makes the slant-edge cardinality `|Â_i ∩ w_i(ι+1)|`
  **non-decreasing** in `i`: strictly increasing if `J = ι+1` (`:500`), constant if `J > ι+1`
  (`:504`, minimality of `J`).
* That cardinality **is** `â_i` (`encard_face_hatShape_slant`): the slant edge runs from the
  pinned vertex `g_1` to the vertex with the `(1,0)`-edge, so its length reads off `â_i`.
* `hexE` has exactly **two** normals with `⟪n, v⃗_ℓ⟫ > 0`, namely `(1,0)` and `(1,-1)`
  (`dot_vl_pos_hexE`).  `(1,-1)` is pinned by endpoint alignment `:488`, so `â_i` is the only
  free coordinate, and the extraction is exactly the hypothesis that closes it
  (`ahatMono_of_slantPinned`).

**Scope, stated as a limitation and not as a result.**  The last bullet is a fact about *this*
fan.  For a fan carrying three or more normals on the `+v⃗_ℓ` side, the extraction still freezes
the chain `n_ι … n_J` and still forces growth at `n_{J+1}`, but a normal at `n_{J+2}` or beyond
would be left free — and the counterexamples of §8-§10 exploit precisely a free `+v⃗_ℓ` normal.
`hexE` is centrally symmetric with `m = 6`, so it has exactly `m/2 - 1 = 2`, which is one too
few to reach `n_{J+2}`.  Whether an eight-normal fan defeats the extracted statement is
**untested**; no counterexample is claimed here, and none is implied by §8-§10. -/

/-- **The extraction kills the §9/§10 witness** — and does so by a single index shift.

`xRx` stalls exactly once (`xRx 3 = xRx 4 = 6`), so `σ i := i + 4` avoids the stall outright and
the subsequence satisfies `AhatMono`.  The other binders survive the shift for free: `xA` is
monotone, so `itemII_xA` and `exhausts_xA` transfer.

The honest reading: **`not_ahatMono_xA` (`:953`) does not refute the source's extracted
statement**, and neither do the witnesses of §8 or §10, which share this family. -/
theorem ahatMono_shift4_xA :
    ∀ i j, i ≤ j →
      hatOf (fun n => xA (n + 4)) (fun n => xKK (n + 4)) ((1 : ℤ), (0 : ℤ)) i
        ⊆ hatOf (fun n => xA (n + 4)) (fun n => xKK (n + 4)) ((1 : ℤ), (0 : ℤ)) j := by
  have hN : ∀ n : ℕ, xN (n + 4) = n + 4 := fun n => by unfold xN; omega
  have hR : ∀ n : ℕ, xRx (n + 4) = 2 * (n : ℤ) + 6 := by
    intro n; unfold xRx; split_ifs with h
    · omega
    · push_cast; ring
  have hK : ∀ n : ℕ, (xKK (n + 4) : ℤ) = (n : ℤ) + 3 := by
    intro n; unfold xKK; split_ifs with h
    · omega
    · push_cast; omega
  intro i j hij z hz
  have hcij : (i : ℤ) ≤ (j : ℤ) := by exact_mod_cast hij
  have hz' : z + (xKK (i + 4) : ℤ) • ((1 : ℤ), (0 : ℤ)) ∈ xA (i + 4) := hz
  show z + (xKK (j + 4) : ℤ) • ((1 : ℤ), (0 : ℤ)) ∈ xA (j + 4)
  rw [ce_shift, mem_xA, hN, hR, hK] at hz'
  rw [ce_shift, mem_xA, hN, hR, hK]
  push_cast at hz' ⊢
  omega

/-- **The hexagon fan has exactly two normals on the `+v⃗_ℓ` side, for `v⃗_ℓ = (1,0)`.**

原文：b3_colle2.txt:402 (Definition 3.2 — `E(𝒯) = E(𝒮_φ)`, so every stage shares this fan) and
`:488` (endpoint alignment pins the one adjacent to the `ℓ`-edge at `g_1`).

This is the reason the extraction suffices here: after `:488` pins `(1,-1)`, the residual
hypothesis of `ahatMono_of_suppVal_slack_enveloped` (`:546`) has a single normal left. -/
theorem dot_vl_pos_hexE {n : ℤ × ℤ} (hn : n ∈ Nivat.ShellSweep.hexE)
    (hpos : 0 < dot n ((1 : ℤ), (0 : ℤ))) :
    n = ((1 : ℤ), (0 : ℤ)) ∨ n = ((1 : ℤ), (-1 : ℤ)) := by
  simp only [Nivat.ShellSweep.hexE, Set.mem_insert_iff, Set.mem_singleton_iff] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact absurd hpos (by norm_num [dot])
  · exact absurd hpos (by norm_num [dot])
  · exact absurd hpos (by norm_num [dot])
  · exact Or.inr rfl
  · exact absurd hpos (by norm_num [dot])

/-- **`AhatMono` reduces to one scalar once `:488` is in force.**

原文：b3_colle2.txt:488 (`hpin` — the `(1,-1)`-support of `Â_i` is the constant `c₀`, which is
what "the final point of `Â_i ∩ ℓ⁻` coincides with `g₁`" says for this fan) and `:500`/`:504`
(`hgrow` — the `(1,0)`-support of `Â_i` is non-decreasing).

量词对应原文: `hpin` ↔ `:488`'s `k_i` clause, one equation per `i`; `hgrow` ↔ the extracted
edge-cardinality condition, transported to a support value by `encard_face_hatShape_slant`;
`henv` ↔ `:484`'s `E(𝒮_φ)`-envelopedness; `hmono` ↔ `:486`; `hkk` ↔ `kk_le_of_endpointAligned`
(`:105`), itself a consequence of `:486` + `:488`.  No quantifier is ours. -/
theorem ahatMono_of_slantPinned
    {A : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ} {c₀ : ℤ}
    (henv : ∀ i, Enveloped (Nivat.ShellMink.hexA) (A i))
    (hfin : ∀ i, (A i).Finite) (hne : ∀ i, (A i).Nonempty)
    (harea : ∀ i, PosArea (A i)) (hlc : ∀ i, IsLatticeConvexRegion (A i))
    (hmono : ∀ i j, i ≤ j → A i ⊆ A j)
    (hkk : ∀ i j, i ≤ j → kk i ≤ kk j)
    (hpin : ∀ i, suppVal (A i) ((1 : ℤ), (-1 : ℤ)) = c₀ + (kk i : ℤ))
    (hgrow : ∀ i j, i ≤ j →
      suppVal (A i) ((1 : ℤ), (0 : ℤ)) - (kk i : ℤ)
        ≤ suppVal (A j) ((1 : ℤ), (0 : ℤ)) - (kk j : ℤ)) :
    ∀ i j, i ≤ j →
      hatOf A kk ((1 : ℤ), (0 : ℤ)) i ⊆ hatOf A kk ((1 : ℤ), (0 : ℤ)) j := by
  refine ahatMono_of_suppVal_slack_enveloped ?_ henv hfin hne harea hlc hmono hkk ?_
  · exact Nivat.LE2.finite_E_of_finite finite_hexA
  · intro i j hij n hn hsign
    rw [Nivat.ShellSweep.E_hexA_eq] at hn
    rcases dot_vl_pos_hexE hn hsign with rfl | rfl
    · have hg := hgrow i j hij
      simp only [dot]
      omega
    · have h1 := hpin i
      have h2 := hpin j
      simp only [dot]
      omega

/-! ### The slant edge is `â`

The stages of §8-§10 are `hexShape`s; `hatShape` is the same object in the coordinates where
`:488` has already been applied — bottom edge on `ℓ⁻` at `y = 0` and slant support pinned to
`1`, so that `g₁ = (1,0)` for every `i`.  The only free coordinates are `a` (right), `b` (top),
`c` (upper-left) and `r` (left). -/

/-- `Â_i` in endpoint-aligned coordinates: `g₁ = (1,0)` is forced, and `a` is the one
`+v⃗_ℓ` support left free. -/
def hatShape (a b c r : ℤ) : Set (ℤ × ℤ) :=
  {z | -r ≤ z.1 ∧ z.1 ≤ a ∧ 0 ≤ z.2 ∧ z.2 ≤ b ∧ -c ≤ z.1 - z.2 ∧ z.1 - z.2 ≤ 1}

theorem mem_hatShape (a b c r : ℤ) (z : ℤ × ℤ) :
    z ∈ hatShape a b c r ↔
      -r ≤ z.1 ∧ z.1 ≤ a ∧ 0 ≤ z.2 ∧ z.2 ≤ b ∧ -c ≤ z.1 - z.2 ∧ z.1 - z.2 ≤ 1 := Iff.rfl

theorem hatShape_eq_shift (a b c r : ℤ) :
    hatShape a b c r = Nivat.LE2.shift ((-r : ℤ), (0 : ℤ))
      (Nivat.ShellSweep.hexShape (a + r) b (c - r) (1 + r) 0) := by
  ext z
  simp only [mem_hatShape, Nivat.LE2.mem_shift_iff, Nivat.ShellSweep.mem_hexShape,
    Prod.fst_sub, Prod.snd_sub]
  omega

theorem enveloped_hatShape {a b c r : ℤ}
    (h : Nivat.ShellSweep.Nondeg (a + r) b (c - r) (1 + r) 0) :
    EnvOf (Nivat.ShellMink.hexA) (hatShape a b c r) := by
  rw [hatShape_eq_shift]
  exact Nivat.LE2.envOf_shift _ (Nivat.ShellSweep.enveloped_hexShape h
    Nivat.ShellSweep.E_hexA_eq Nivat.ShellSweep.encard_face_hexA_le)

theorem two_le_of_nondeg_hatShape {a b c r : ℤ}
    (h : Nivat.ShellSweep.Nondeg (a + r) b (c - r) (1 + r) 0) : 2 ≤ a := by
  have := h.lr; omega

/-- **The slant edge of `Â_i` is `{(x, x-1) : 1 ≤ x ≤ a}`** — it runs from the pinned vertex
`g₁ = (1,0)` to the vertex it shares with the `(1,0)`-edge. -/
theorem face_hatShape_slant {a b c r : ℤ}
    (h : Nivat.ShellSweep.Nondeg (a + r) b (c - r) (1 + r) 0) :
    face (hatShape a b c r) ((1 : ℤ), (-1 : ℤ))
      = (fun x : ℤ => (x, x - 1)) '' (Set.Icc 1 a) := by
  obtain ⟨hbot, hlr, hright, htop, hul, hleft⟩ := h
  have h10 : ((1 : ℤ), (0 : ℤ)) ∈ hatShape a b c r := by
    rw [mem_hatShape]; refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
  ext z
  constructor
  · rintro ⟨hz, hmax⟩
    have hd := hmax _ h10
    rw [mem_hatShape] at hz
    simp only [dot] at hd
    refine ⟨z.1, ?_, ?_⟩
    · simp only [Set.mem_Icc]; omega
    · have hz2 : z.2 = z.1 - 1 := by omega
      show ((z.1, z.1 - 1) : ℤ × ℤ) = z
      rw [← hz2]
  · rintro ⟨x, hx, rfl⟩
    simp only [Set.mem_Icc] at hx
    refine ⟨?_, ?_⟩
    · rw [mem_hatShape]
      refine ⟨by simp; omega, by simp; omega, by simp; omega, by simp; omega,
        by simp; omega, by simp⟩
    · intro y hy
      rw [mem_hatShape] at hy
      simp only [dot]
      omega

theorem encard_face_hatShape_slant {a b c r : ℤ}
    (h : Nivat.ShellSweep.Nondeg (a + r) b (c - r) (1 + r) 0) :
    (face (hatShape a b c r) ((1 : ℤ), (-1 : ℤ))).encard = (a.toNat : ℕ∞) := by
  have hinj : Set.InjOn (fun x : ℤ => (x, x - 1)) (Set.Icc 1 a) :=
    fun x _ y _ hxy => by simpa using congrArg Prod.fst hxy
  rw [face_hatShape_slant h, hinj.encard_image, ← Finset.coe_Icc,
    Set.encard_coe_eq_coe_finsetCard, Int.card_Icc]
  norm_num

/-- **The extraction's edge condition is exactly `â_i ≤ â_j`.**

原文：b3_colle2.txt:500 (`|Â_i ∩ w_i(J)| < |Â_{i+1} ∩ w_{i+1}(J)|`, case `J = ι+1`) and `:504`
(`|Â_i ∩ w_i(j)| = |Â_{i+1} ∩ w_{i+1}(j)|` for `ι+1 ≤ j ≤ J-1`, case `J > ι+1`).  Both give
`≤` on the slant-edge cardinality, which is the hypothesis here. -/
theorem le_of_encard_face_slant_le {a b c r a' b' c' r' : ℤ}
    (h : Nivat.ShellSweep.Nondeg (a + r) b (c - r) (1 + r) 0)
    (h' : Nivat.ShellSweep.Nondeg (a' + r') b' (c' - r') (1 + r') 0)
    (hle : (face (hatShape a b c r) ((1 : ℤ), (-1 : ℤ))).encard
      ≤ (face (hatShape a' b' c' r') ((1 : ℤ), (-1 : ℤ))).encard) :
    a ≤ a' := by
  rw [encard_face_hatShape_slant h, encard_face_hatShape_slant h'] at hle
  have hnat : a.toNat ≤ a'.toNat := by exact_mod_cast hle
  have h2 := two_le_of_nondeg_hatShape h
  have h2' := two_le_of_nondeg_hatShape h'
  omega

/-- **The conclusion of §11.**  A stage family in endpoint-aligned coordinates whose
slant-edge cardinalities are non-decreasing — which is what `:500`/`:504` deliver, whichever
value `J` takes — satisfies `Â_i ⊆ Â_j`.

The other three coordinates ride along for free, and it is worth saying why they need no
extraction hypothesis: `b`, `c`, `r` are the supports at `(0,1)`, `(-1,1)`, `(-1,0)`, whose
`v⃗_ℓ`-dot products are `0`, `-1`, `-1` — non-positive, so `A_i ⊆ A_j` (`:486`) already forces
the hatted versions to grow (`dot_vl_pos_hexE` is the statement that these are all of them). -/
theorem hatShape_subset_of_extraction {a b c r a' b' c' r' : ℤ}
    (h : Nivat.ShellSweep.Nondeg (a + r) b (c - r) (1 + r) 0)
    (h' : Nivat.ShellSweep.Nondeg (a' + r') b' (c' - r') (1 + r') 0)
    (hb : b ≤ b') (hc : c ≤ c') (hr : r ≤ r')
    (hext : (face (hatShape a b c r) ((1 : ℤ), (-1 : ℤ))).encard
      ≤ (face (hatShape a' b' c' r') ((1 : ℤ), (-1 : ℤ))).encard) :
    hatShape a b c r ⊆ hatShape a' b' c' r' := by
  have ha := le_of_encard_face_slant_le h h' hext
  intro z hz
  rw [mem_hatShape] at hz ⊢
  omega

/-- The pinned `+v⃗_ℓ` support: `:488` fixes it at `1` for every stage, independently of
`a`, `b`, `c`, `r`.  This is `ahatMono_of_slantPinned`'s `hpin` on the hatted side. -/
theorem suppVal_hatShape_slant {a b c r : ℤ}
    (h : Nivat.ShellSweep.Nondeg (a + r) b (c - r) (1 + r) 0) :
    suppVal (hatShape a b c r) ((1 : ℤ), (-1 : ℤ)) = 1 := by
  obtain ⟨hbot, hlr, hright, htop, hul, hleft⟩ := h
  have hmem : ((1 : ℤ), (0 : ℤ)) ∈ face (hatShape a b c r) ((1 : ℤ), (-1 : ℤ)) := by
    refine ⟨?_, fun y hy => ?_⟩
    · rw [mem_hatShape]; refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
    · rw [mem_hatShape] at hy; simp only [dot]; omega
  rw [suppVal_eq hmem]; simp [dot]

/-- The free `+v⃗_ℓ` support: `a`.  This is the scalar `ahatMono_of_slantPinned`'s `hgrow`
constrains, and `encard_face_hatShape_slant` is what ties it to `:500`/`:504`. -/
theorem suppVal_hatShape_right {a b c r : ℤ}
    (h : Nivat.ShellSweep.Nondeg (a + r) b (c - r) (1 + r) 0) :
    suppVal (hatShape a b c r) ((1 : ℤ), (0 : ℤ)) = a := by
  obtain ⟨hbot, hlr, hright, htop, hul, hleft⟩ := h
  have hmem : ((a : ℤ), (a - 1 : ℤ)) ∈ face (hatShape a b c r) ((1 : ℤ), (0 : ℤ)) := by
    refine ⟨?_, fun y hy => ?_⟩
    · rw [mem_hatShape]; refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
    · rw [mem_hatShape] at hy; simp only [dot]; omega
  rw [suppVal_eq hmem]; simp [dot]

/-- `hatOf` of a family presented in endpoint-aligned coordinates is that family. -/
theorem hatOf_shift_smul (S : ℕ → Set (ℤ × ℤ)) (kk : ℕ → ℕ) (vl : ℤ × ℤ) (i : ℕ) :
    hatOf (fun n => Nivat.LE2.shift ((kk n : ℤ) • vl) (S n)) kk vl i = S i := by
  ext z
  show z + (kk i : ℤ) • vl ∈ Nivat.LE2.shift ((kk i : ℤ) • vl) (S i) ↔ _
  rw [Nivat.LE2.mem_shift_iff]
  simp

/-! ## 12. The extraction closes exactly one inequality, and it closes it by an identity

集成者 2026-09-20 的告诫（记录在案，是对的）：「我们这一族存在躲开停顿的子列」与
「原文按边长计数取的子列恰好躲开它」**是两个命题**，前者不能顶替后者。
`ahatMono_shift4_xA` (`:1320`) 只是前者。本节是后者：结论对**每一个**满足 `:498-504` 的
族成立，不只对 `xA`。

**答「`ahatMono_iff_fwdAbsorb` 的哪一步被抽子列关掉」**：`ahatMono_of_suppVal_slack`
(`:520`) 把整条不等式按 `dot n vl` 的符号劈成两支。`dot n vl ≤ 0` 那支 (`:533-537`) 从
`A_i ⊆ A_j` (`:486`) 免费得到，抽不抽子列都成立。**欠的从头到尾只有 `0 < dot n vl` 那支**
(`:538-540`)，而 `dot_vl_pos_hexE` (`:1349`) 说六边形扇上这支只有两个法向：`(1,-1)` 由
`:488` 钉死（`suppVal_hatShape_slant`，常数 `1`），`(1,0)` 自由。
`suppVal_slack_fails_at_enveloped` (`:578`) 证伪的正是 `(1,0)` 这一条，§5/§8/§9/§10 四代
反例全部只打这一个数。

**抽子列关掉它，靠的是一个恒等式而不是新几何**：`encard_face_slant_eq_suppVal_right`
下面说，`(1,-1)` 边上的**格点个数**与 `(1,0)` 方向的**支撑值**是同一个整数 `a`。
所以 `:500`/`:504` 的「边长不减」与 `hslack` 在 `n = (1,0)` 处的那条不等式**逐字同义**。
这也解释了为什么四代反例都能构造出来：它们把 `a` 停住一次，而 `AhatMono` 的
`∀ i j` 不许，`:498-504` 的子列许——抽完就不许了。

⚠ **范围限定，不要外推**：以上只对 `hexA` 这个扇成立，理由是计数（`m = 6` 中心对称
⟹ 正侧恰好 `m/2 − 1 = 2` 个法向，一个被 `:488` 钉死，一个被抽子列钉死，没有第三个）。
`m = 8` 的扇正侧有三个法向，第三个自由——那正是 §8–§10 用的自由度。**我没有八边形反例，
也不断言它存在**：要有见证得先造 `enveloped_hexShape` / `E_hexA_eq` / `encard_face_hexA_le`
的八法向版本，那是独立一摊活。
🟢 **2026-09-20 晚：已造出，见 §18 `not_ahatMono_octagon`**（`enveloped_octShape` /
`E_oct1` / `encard_face_oct1_le` 就是上面点名的三条八法向版本）。上一段按 §14 保留。 -/

/-- **恒等式：抽子列管的边长 = `hslack` 管的支撑值。**

原文：b3_colle2.txt:500 数的是 `|Â_i ∩ w_i(J)|`（边上的格点个数）；
`ahatMono_of_suppVal_slack` 的 `hslack` 管的是 `suppVal (A i) (1,0)`。在 `:488` 归一化后的
坐标里这两个数相等，所以 `:500`/`:504` 与残余不等式不是「蕴含」，是同一句话。 -/
theorem encard_face_slant_eq_suppVal_right {a b c r : ℤ}
    (h : Nivat.ShellSweep.Nondeg (a + r) b (c - r) (1 + r) 0) :
    (face (hatShape a b c r) ((1 : ℤ), (-1 : ℤ))).encard
      = ((suppVal (hatShape a b c r) ((1 : ℤ), (0 : ℤ))).toNat : ℕ∞) := by
  rw [encard_face_hatShape_slant h, suppVal_hatShape_right h]

/-- **§12 的结论：抽子列之后 `AhatMono` 为真，对六边形扇上的每一个族。**

不是对 `xA`，也不是「存在某个子列」——binder 里的 `a b c r kk` 是任意的，
前提只有 `:498-504` 的边长不减（`hext`）、`:486` 给的另外三个自由坐标单调
（`hb`/`hc`/`hr`，它们是 `dot n vl ≤ 0` 的那支，本来就免费），和每级的非退化。

所以：**四代反例都活不过抽子列，而且死因不是我们没找对族，是这个扇上没有可停的数。**

量词对应原文:
- `i ≤ j` ↔ `:502` "we can assume that this holds for all `i`"（抽完子列后对所有 `i`）
- `hext` ↔ `:500` 的 `|Â_i ∩ w_i(J)| < |Â_{i+1} ∩ w_{i+1}(J)|` 与 `:504` 的等号合起来
  给出的 `≤`（`J` 取哪个值都一样，见 `le_of_encard_face_slant_le` 的 docstring）
- `hb`/`hc`/`hr` ↔ `:486` 的 `A_i ⊂ A_{i+1}` 在非正法向上的分量

**未兑现的 binder（按落地纪律具名）**：本条不假设 `Enveloped`（由 `enveloped_hatShape`
`:1421` 免费，但这里不需要），不假设 `ofParts` 的 `maxA` / `ItemII` / `Exhausts`，
也不假设 `hatShape` 穷尽了 `hexA`-enveloped 的格凸区域——最后这条为真的理由（`E` 相等
⟹ 同六条半平面切出）**没有在内核里验过**，不许当结论用。 -/
theorem ahatMono_of_extraction {a b c r : ℕ → ℤ} {kk : ℕ → ℕ}
    (h : ∀ i, Nivat.ShellSweep.Nondeg (a i + r i) (b i) (c i - r i) (1 + r i) 0)
    (hb : ∀ i j, i ≤ j → b i ≤ b j)
    (hc : ∀ i j, i ≤ j → c i ≤ c j)
    (hr : ∀ i j, i ≤ j → r i ≤ r j)
    (hext : ∀ i j, i ≤ j →
      (face (hatShape (a i) (b i) (c i) (r i)) ((1 : ℤ), (-1 : ℤ))).encard
        ≤ (face (hatShape (a j) (b j) (c j) (r j)) ((1 : ℤ), (-1 : ℤ))).encard) :
    ∀ i j, i ≤ j →
      hatOf (fun n => Nivat.LE2.shift ((kk n : ℤ) • ((1 : ℤ), (0 : ℤ)))
          (hatShape (a n) (b n) (c n) (r n))) kk ((1 : ℤ), (0 : ℤ)) i
        ⊆ hatOf (fun n => Nivat.LE2.shift ((kk n : ℤ) • ((1 : ℤ), (0 : ℤ)))
          (hatShape (a n) (b n) (c n) (r n))) kk ((1 : ℤ), (0 : ℤ)) j := by
  intro i j hij
  rw [hatOf_shift_smul, hatOf_shift_smul]
  exact hatShape_subset_of_extraction (h i) (h j) (hb i j hij) (hc i j hij) (hr i j hij)
    (hext i j hij)

/-- **反向，说明 `hext` 不是白写的**：抽子列的边长条件**等价于** `a` 不减，
所以 §12 的结论在去掉 `hext` 之后为假（§5/§8/§9/§10 就是见证）。
这条排除「`hext` 恰好恒真所以定理空洞」的读法。 -/
theorem encard_face_slant_le_iff {a b c r a' b' c' r' : ℤ}
    (h : Nivat.ShellSweep.Nondeg (a + r) b (c - r) (1 + r) 0)
    (h' : Nivat.ShellSweep.Nondeg (a' + r') b' (c' - r') (1 + r') 0) :
    (face (hatShape a b c r) ((1 : ℤ), (-1 : ℤ))).encard
      ≤ (face (hatShape a' b' c' r') ((1 : ℤ), (-1 : ℤ))).encard ↔ a ≤ a' := by
  refine ⟨le_of_encard_face_slant_le h h', fun hle => ?_⟩
  rw [encard_face_hatShape_slant h, encard_face_hatShape_slant h']
  exact_mod_cast Int.toNat_le_toNat hle

/-! ## 13. What a revised `ofParts` would consume

集成者 2026-09-20 裁决：走 (ii)。本节交付两样东西——重指标化真正需要的那条并集引理，
以及**按 `ofParts` 的字段形状**写出的 `AhatMono` 生产者。每条的消费者在 docstring 里点名。

⚠ **本节不碰 `ChainAssemble.lean`**（非本 lane 所有）。§13.2 末条的结论逐字等于
`ofParts` 的 `AhatMono` binder（`ChainAssemble.lean:186`），所以接线只是把 `AhatMono`
这一个 binder 换成 `hshape`/`hext`，其余 binder 不动。

### §13.1 重指标化真正需要的前提

集成者给的候选前提是 `Function.Bijective σ`（或 `Surjective`）。**两个都不对**，理由在
`eq_id_of_strictMono_of_surjective` 里给了内核证明：ℕ 上严格单调的满射只有恒等映射，
所以那一版对抽子列恒为空谈。抽子列要的是 `StrictMono σ`，而 `StrictMono` **单靠自己
推不出并集相等**——反过来需要 `Ahat` 单调，也就是 `AhatMono` 本身。
这正是 pre-GO 报告里那条循环：`iUnion_reindex_of_mono` 的第一个前提就是它。 -/

/-- ℕ 上严格单调映射满足 `i ≤ σ i`。自证以避免 Mathlib 名字漂移。 -/
theorem le_apply_of_strictMono {σ : ℕ → ℕ} (hσ : StrictMono σ) : ∀ i, i ≤ σ i := by
  intro i
  induction i with
  | zero => exact Nat.zero_le _
  | succ n ih => exact Nat.succ_le_of_lt (lt_of_le_of_lt ih (hσ (Nat.lt_succ_self n)))

/-- **`Surjective` 是错的前提。**  ℕ 上严格单调的满射是恒等映射，所以以 `Bijective σ`
（或 `StrictMono` + `Surjective`）为前提的重指标化引理对抽子列**恒为空谈**：唯一满足
前提的 `σ` 不改变任何指标。 -/
theorem eq_id_of_strictMono_of_surjective {σ : ℕ → ℕ} (hσ : StrictMono σ)
    (hsur : Function.Surjective σ) : ∀ n, σ n = n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    obtain ⟨j, hj⟩ := hsur n
    have hjn : j ≤ n := hj ▸ le_apply_of_strictMono hσ j
    rcases lt_or_eq_of_le hjn with hlt | rfl
    · have := ih j hlt
      omega
    · exact hj

/-- **重指标化只需要的那条并集引理。**

消费者：`ChainDataGeom` 里七个提到 `⋃ i, Ahat i` 且方向上**并集会变小**的字段——
`ChainData.shellInfZero`（`Lemma35.lean:741`）、`ChainDataWithShell.shellInf_eq`
（`ChainShell.lean:58`）、`ahat_nonempty`（`ChainShell.lean:61`）、`ChainDataGeom.bottom`
（`ChainGeom.lean:128`，前两个合取在 `reachSet` 里）、`rec_p`（`ChainGeom.lean:136`）、
`rec_vJ`（`ChainGeom.lean:163`）、`ahat_attained_L`（`ChainGeom.lean:185`）。
另外两条 `ahat_halfPlane`（`ChainShell.lean:63`）与 `ahat_halfPlane_L`
（`ChainGeom.lean:180`）是 `∀ g ∈ ⋃`，定义域变小，不需要本引理。

🔴 **第一个前提就是 `AhatMono`。** 所以本引理**搬运** `AhatMono`，不生产它；
想靠重指标化拿到 `AhatMono` 是循环的。生产者是 §13.2。 -/
theorem iUnion_reindex_of_mono {S : ℕ → Set (ℤ × ℤ)} {σ : ℕ → ℕ}
    (hmono : ∀ i j, i ≤ j → S i ⊆ S j) (hσ : ∀ i, i ≤ σ i) :
    (⋃ i, S (σ i)) = ⋃ i, S i := by
  apply Set.Subset.antisymm
  · exact Set.iUnion_subset fun i => Set.subset_iUnion S (σ i)
  · exact Set.iUnion_subset fun i =>
      subset_trans (hmono i (σ i) (hσ i)) (Set.subset_iUnion (fun k => S (σ k)) i)

/-- `StrictMono` 版，供抽子列直接引用。 -/
theorem iUnion_reindex_of_strictMono {S : ℕ → Set (ℤ × ℤ)} {σ : ℕ → ℕ}
    (hmono : ∀ i j, i ≤ j → S i ⊆ S j) (hσ : StrictMono σ) :
    (⋃ i, S (σ i)) = ⋃ i, S i :=
  iUnion_reindex_of_mono hmono (le_apply_of_strictMono hσ)

/-! ### §13.2 `ofParts` 形状的 `AhatMono` 生产者

下面最后一条的结论**逐字**是 `ChainAssemble.lean:186` 的
`AhatMono : ∀ i j, i ≤ j → hatOf A kk vl i ⊆ hatOf A kk vl j`（在 `vl = (1,0)` 处），
`A` 与 `kk` 是自由变量——不是 §12 那个 `shift`-包装过的特殊形状。 -/

/-- `Â_i` 是 `A i` 按 `-(k_i) v⃗_ℓ` 的平移。`Colle35.hatOf_eq_shift`
（`ChainAssemble.lean:301`）是同一条，本文件重证一份是为了**不 import `ChainAssemble`**
——集成者要把本文件 import 进 `ChainAssemble`，反向 import 会成环。 -/
theorem hatOf_eq_shift_neg (A : ℕ → Set (ℤ × ℤ)) (kk : ℕ → ℕ) (vl : ℤ × ℤ) (i : ℕ) :
    hatOf A kk vl i = Nivat.LE2.shift (-(kk i : ℤ) • vl) (A i) := by
  ext z
  show z + (kk i : ℤ) • vl ∈ A i ↔ z - -(kk i : ℤ) • vl ∈ A i
  rw [neg_smul, sub_neg_eq_add]

theorem dot_smul_right (n : ℤ × ℤ) (t : ℤ) (v : ℤ × ℤ) : dot n (t • v) = t * dot n v := by
  simp only [dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

/-- 平移保持有限性。`Nivat.LE2` 里只有 `suppVal_shift`（`EnvTranslate.lean:40`），没有这条。 -/
theorem finite_shift {v : ℤ × ℤ} {R : Set (ℤ × ℤ)} (h : R.Finite) :
    (Nivat.LE2.shift v R).Finite := by
  have hrw : Nivat.LE2.shift v R = (fun z => z + v) '' R := by
    ext z
    simp only [Nivat.LE2.mem_shift_iff, Set.mem_image]
    constructor
    · intro hz
      exact ⟨z - v, hz, by abel⟩
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
  rw [hrw]
  exact h.image _

/-- 反向：`A_i` 是 `Â_i` 按 `+k_i v⃗_ℓ` 的平移。集成者接线时用得上——`ofParts` 的
`hfin` binder（`ChainAssemble.lean:189`）写在 `hatOf` 上，而
`ahatMono_ofParts_of_extraction` 的 `hfin` / `hne` 写在 `A` 上（它们经 `suppVal_hatOf`
传给 `suppVal_shift`，后者要的就是 `A i`）。下面两条把两种写法对接，无需新数学。 -/
theorem eq_shift_hatOf (A : ℕ → Set (ℤ × ℤ)) (kk : ℕ → ℕ) (vl : ℤ × ℤ) (i : ℕ) :
    A i = Nivat.LE2.shift ((kk i : ℤ) • vl) (hatOf A kk vl i) := by
  ext z
  show z ∈ A i ↔ (z - (kk i : ℤ) • vl) + (kk i : ℤ) • vl ∈ A i
  simp

theorem finite_of_finite_hatOf {A : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ} {vl : ℤ × ℤ} {i : ℕ}
    (h : (hatOf A kk vl i).Finite) : (A i).Finite := by
  rw [eq_shift_hatOf A kk vl i]; exact finite_shift h

theorem nonempty_of_nonempty_hatOf {A : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ} {vl : ℤ × ℤ} {i : ℕ}
    (h : (hatOf A kk vl i).Nonempty) : (A i).Nonempty := by
  obtain ⟨z, hz⟩ := h
  exact ⟨z + (kk i : ℤ) • vl, hz⟩

/-- `Â_i` 的支撑值：`h_{Â_i}(n) = h_{A_i}(n) − k_i ⟪n, v⃗_ℓ⟫`。这是 §7 那条残余不等式的
坐标形式（`ahatMono_of_suppVal_slack`, `:520`）。 -/
theorem suppVal_hatOf {A : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ} {vl : ℤ × ℤ} {i : ℕ}
    (hfin : (A i).Finite) (hne : (A i).Nonempty) (n : ℤ × ℤ) :
    suppVal (hatOf A kk vl i) n = suppVal (A i) n - (kk i : ℤ) * dot n vl := by
  rw [hatOf_eq_shift_neg, Nivat.LE2.suppVal_shift hfin hne, dot_smul_right]
  ring

/-- **非正法向那一支是免费的**，逐字对应 `ahatMono_of_suppVal_slack` 的 `:533-537` 分支：
`A_i ⊆ A_j`（`b3_colle2.txt:486`）加上 `k_i ≤ k_j`（`kk_le_of_endpointAligned`, `:105`）
就够，抽子列在这里不起任何作用。 -/
theorem suppVal_hatOf_mono_of_nonpos {A : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ} {vl : ℤ × ℤ}
    (hfin : ∀ i, (A i).Finite) (hne : ∀ i, (A i).Nonempty)
    (hmono : ∀ i j, i ≤ j → A i ⊆ A j) (hkk : ∀ i j, i ≤ j → kk i ≤ kk j)
    {n : ℤ × ℤ} (hn : dot n vl ≤ 0) {i j : ℕ} (hij : i ≤ j) :
    suppVal (hatOf A kk vl i) n ≤ suppVal (hatOf A kk vl j) n := by
  rw [suppVal_hatOf (hfin i) (hne i), suppVal_hatOf (hfin j) (hne j)]
  have hA : suppVal (A i) n ≤ suppVal (A j) n :=
    suppVal_mono (hfin i) (hne i) (hfin j) (hne j) (hmono i j hij) n
  have hk : (kk i : ℤ) ≤ (kk j : ℤ) := by exact_mod_cast hkk i j hij
  nlinarith [mul_nonneg (by linarith : (0 : ℤ) ≤ (kk j : ℤ) - (kk i : ℤ))
    (by linarith : (0 : ℤ) ≤ -dot n vl)]

/-- 顶边支撑值。`hatShape` 的 `(0,1)` 面在 `y = b`，见证顶点 `(a, b)`。 -/
theorem suppVal_hatShape_top {a b c r : ℤ}
    (h : Nivat.ShellSweep.Nondeg (a + r) b (c - r) (1 + r) 0) :
    suppVal (hatShape a b c r) ((0 : ℤ), (1 : ℤ)) = b := by
  obtain ⟨hbot, hlr, hright, htop, hul, hleft⟩ := h
  have hmem : ((a : ℤ), (b : ℤ)) ∈ face (hatShape a b c r) ((0 : ℤ), (1 : ℤ)) := by
    refine ⟨?_, fun y hy => ?_⟩
    · rw [mem_hatShape]; refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
    · rw [mem_hatShape] at hy; simp only [dot]; omega
  rw [suppVal_eq hmem]; simp [dot]

/-- 左边支撑值。`hatShape` 的 `(-1,0)` 面在 `x = -r`，见证顶点 `(-r, 0)`。 -/
theorem suppVal_hatShape_left {a b c r : ℤ}
    (h : Nivat.ShellSweep.Nondeg (a + r) b (c - r) (1 + r) 0) :
    suppVal (hatShape a b c r) ((-1 : ℤ), (0 : ℤ)) = r := by
  obtain ⟨hbot, hlr, hright, htop, hul, hleft⟩ := h
  have hmem : ((-r : ℤ), (0 : ℤ)) ∈ face (hatShape a b c r) ((-1 : ℤ), (0 : ℤ)) := by
    refine ⟨?_, fun y hy => ?_⟩
    · rw [mem_hatShape]; refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
    · rw [mem_hatShape] at hy; simp only [dot]; omega
  rw [suppVal_eq hmem]; simp [dot]

/-- 左上支撑值。`hatShape` 的 `(-1,1)` 面在 `x - y = -c`，见证顶点 `(-r, c - r)`。 -/
theorem suppVal_hatShape_ul {a b c r : ℤ}
    (h : Nivat.ShellSweep.Nondeg (a + r) b (c - r) (1 + r) 0) :
    suppVal (hatShape a b c r) ((-1 : ℤ), (1 : ℤ)) = c := by
  obtain ⟨hbot, hlr, hright, htop, hul, hleft⟩ := h
  have hmem : ((-r : ℤ), (c - r : ℤ)) ∈ face (hatShape a b c r) ((-1 : ℤ), (1 : ℤ)) := by
    refine ⟨?_, fun y hy => ?_⟩
    · rw [mem_hatShape]; refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
    · rw [mem_hatShape] at hy; simp only [dot]; omega
  rw [suppVal_eq hmem]; simp [dot]

/-- 底边支撑值。`hatShape` 的 `(0,-1)` 面在 `y = 0`，见证顶点 `g₁ = (1,0)`。
这一条与 `suppVal_hatShape_slant`（`= 1`）就是 §14 的两条归一化 `hbot` / `hpin`
在 `hatShape` 上的取值，消费者用它们检查自己的候选确实已归一化。 -/
theorem suppVal_hatShape_bot {a b c r : ℤ}
    (h : Nivat.ShellSweep.Nondeg (a + r) b (c - r) (1 + r) 0) :
    suppVal (hatShape a b c r) ((0 : ℤ), (-1 : ℤ)) = 0 := by
  obtain ⟨hbot, hlr, hright, htop, hul, hleft⟩ := h
  have hmem : ((1 : ℤ), (0 : ℤ)) ∈ face (hatShape a b c r) ((0 : ℤ), (-1 : ℤ)) := by
    refine ⟨?_, fun y hy => ?_⟩
    · rw [mem_hatShape]; refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
    · rw [mem_hatShape] at hy; simp only [dot]; omega
  rw [suppVal_eq hmem]; simp [dot]

/-! ### §14 `hshape` 的生产者：共用法锥 ⟹ 同六条半平面切出 ⟹ `hatShape`

§13 的 `ahatMono_ofParts_of_extraction` 把「每级 `Â_i` 在 `:488` 归一化坐标下是六边形」
留成**前提** `hshape`，并在 docstring 里标明「这一步没有在内核里验过」。本节把它证掉，
路线正是当时写下的那条：

1. `Enveloped.E_eq`（`LatticeEdges.lean:1657`）+ `ShellSweep.E_hexA_eq`（`:306`）
   ⟹ 每级共用同一个法锥 `E (Â_i) = hexE`；
2. 二维 H-表示的格点形式（`LE2.mem_of_dot_le_suppVal`，`LatticeEdges.lean:1393`，
   与 `LE2.le_suppVal`，`:749`）⟹ 共用法锥的集合**就是**那六条半平面的交；
3. 六个支撑值里，`(0,−1)` 与 `(1,−1)` 两个被 `:488` 钉死，剩下四个就是
   `hatShape` 的 `a b c r`；
4. `Nondeg` 的六条不等式 = 六个法向各自的面上有两个不同格点，即 `E (Â_i) = hexE`
   的 `IsEdge` 分量（`LatticeEdges.lean:214`，`(face R n).Nontrivial`）。

原文对应（逐个量词）：
* `henv` ↔ `:484` item (iv)：`A_i` 是 `E(𝒮_φ)`-enveloped 的极大集（经 `maxA` / `envA_of_max`）。
  `Enveloped` 对平移不变（`enveloped_shift_right`），所以 `Â_i = A_i − k_i v⃗_ℓ` 照样是。
* `hbot` ↔ `:494` 的 `Â_i ⊂ H_{B_i}(ℓ) − k_i v⃗_ℓ`：`v⃗_ℓ ∥ ℓ`，平移不动半平面，
  于是在把 `ℓ⁻` 取成 `{y = 0}`、`v⃗_ℓ = (1,0)` 的坐标里这就是 `h_{Â_i}(0,−1) = 0`。
* `hpin` ↔ `:488` 「`(A_i − k_i v⃗_ℓ) ∩ ℓ⁻` 的终点与 `g₁` 重合」：同一坐标里 `g₁ = (1,0)`，
  而 `Â_i ∩ {y = 0}` 的终点横坐标是 `min (h(1,0)) (h(1,−1))`，由 `lr`（`2 ≤ a`）取到后者，
  故 `h_{Â_i}(1,−1) = 1`。

⚠ **范围限定，与 §11–§13 完全相同，没有放宽**：`hexE` 是 `E(𝒮_φ)` 恰好六个法向时的样子。
法向更多时 `hatShape` 这个正规形**根本不存在**，本节全部作废；这不是本节新增的债，
是 §11 docstring 已经登记过的那一条（`+v⃗_ℓ` 侧多于两个法向 ⟹ `n_{J+2}` 自由）。 -/

/-- **一条边给出两个把支撑值取到的不同格点。**  这是 `IsEdge` 的 `Nontrivial` 分量
（`LatticeEdges.lean:214`）加 `suppVal_eq`（`:745`），下面六条 `Nondeg` 不等式全部由它产出。 -/
theorem exists_pair_dot_eq_suppVal {T : Set (ℤ × ℤ)} {n : ℤ × ℤ} (hn : n ∈ E T) :
    ∃ p ∈ T, ∃ q ∈ T, p ≠ q ∧ dot n p = suppVal T n ∧ dot n q = suppVal T n := by
  obtain ⟨-, hnt⟩ := mem_E_iff.mp hn
  obtain ⟨p, hp, q, hq, hpq⟩ := hnt
  exact ⟨p, hp.1, q, hq.1, hpq, (suppVal_eq hp).symm, (suppVal_eq hq).symm⟩

/-- `hexE` 是六个点的集合，有限。 -/
theorem finite_hexE : (Nivat.ShellSweep.hexE).Finite := by
  unfold Nivat.ShellSweep.hexE
  exact (((((Set.finite_singleton _).insert _).insert _).insert _).insert _).insert _

/-- **`hshape`，证出来的那一版。**

一个有限的、`E(U)`-enveloped 的格凸集，只要 `U` 的法锥恰是 `hexE`，在 `:488` 的两条归一化下
**就是**一个 `hatShape`，而且是非退化的。四个参数不是选出来的，是它自己的四个支撑值。

⚠ **2026-09-20：`U` 从 `ShellMink.hexA` 放宽成「任意 `E U = hexE` 的 `U`」。** 这不是为了
一般性好看，是**为了让 `henv` 能从 `ofParts` 的 `maxA` 免费拿到**：链上给的是
`IsMaxEnvIn (EnvOf ↑S) _ (A i)`，即 `Enveloped (↑S) (A i)`，`↑S` 是生成窗口 𝒮_φ，
它**不是** `hexA`。原证明只用到 `hexA` 的三件事（`E` 有限、`E = hexE`、三个不同法向），
全部由 `hEU` 给出，所以放宽是零代价的。付出的代价换成了一条具名等式 `E (↑S) = hexE`，
见 §15。

未兑现的 binder：无。`hfin` 由 `A_i` 有限给出，其余三条见本节小标题下的原文对应。 -/
theorem eq_hatShape_of_E_eq_hexE {U T : Set (ℤ × ℤ)}
    (hEU : E U = Nivat.ShellSweep.hexE) (hfin : T.Finite)
    (henv : Enveloped U T)
    (hbot : suppVal T ((0 : ℤ), (-1 : ℤ)) = 0)
    (hpin : suppVal T ((1 : ℤ), (-1 : ℤ)) = 1) :
    Nivat.ShellSweep.Nondeg
        (suppVal T ((1 : ℤ), (0 : ℤ)) + suppVal T ((-1 : ℤ), (0 : ℤ)))
        (suppVal T ((0 : ℤ), (1 : ℤ)))
        (suppVal T ((-1 : ℤ), (1 : ℤ)) - suppVal T ((-1 : ℤ), (0 : ℤ)))
        (1 + suppVal T ((-1 : ℤ), (0 : ℤ))) 0
      ∧ T = hatShape (suppVal T ((1 : ℤ), (0 : ℤ))) (suppVal T ((0 : ℤ), (1 : ℤ)))
          (suppVal T ((-1 : ℤ), (1 : ℤ))) (suppVal T ((-1 : ℤ), (0 : ℤ))) := by
  have hEfin : (E U).Finite := by rw [hEU]; exact finite_hexE
  have hE : E T = Nivat.ShellSweep.hexE := by
    rw [Enveloped.E_eq hEfin henv, hEU]
  have hm1 : ((1 : ℤ), (0 : ℤ)) ∈ E U := by
    rw [hEU]; simp [Nivat.ShellSweep.hexE]
  have hm2 : ((0 : ℤ), (1 : ℤ)) ∈ E U := by
    rw [hEU]; simp [Nivat.ShellSweep.hexE]
  have hm3 : ((1 : ℤ), (-1 : ℤ)) ∈ E U := by
    rw [hEU]; simp [Nivat.ShellSweep.hexE]
  have harea : PosArea T :=
    posArea_of_envOf hm1 hm2 hm3 (by simp) (by simp) (by simp) hEfin henv
  have hne : T.Nonempty := by obtain ⟨p, hp, -⟩ := harea; exact ⟨p, hp⟩
  have hlc : IsLatticeConvexRegion T := henv.1.1
  -- 正向：任何点满足六条支撑不等式，其中两条被 `hbot` / `hpin` 钉死
  have hfwd : ∀ z : ℤ × ℤ, z ∈ T →
      -suppVal T ((-1 : ℤ), (0 : ℤ)) ≤ z.1 ∧ z.1 ≤ suppVal T ((1 : ℤ), (0 : ℤ)) ∧
        0 ≤ z.2 ∧ z.2 ≤ suppVal T ((0 : ℤ), (1 : ℤ)) ∧
        -suppVal T ((-1 : ℤ), (1 : ℤ)) ≤ z.1 - z.2 ∧ z.1 - z.2 ≤ 1 := by
    intro z hz
    have h1 := le_suppVal hfin hne (n := ((1 : ℤ), (0 : ℤ))) hz
    have h2 := le_suppVal hfin hne (n := ((-1 : ℤ), (0 : ℤ))) hz
    have h3 := le_suppVal hfin hne (n := ((0 : ℤ), (1 : ℤ))) hz
    have h4 := le_suppVal hfin hne (n := ((0 : ℤ), (-1 : ℤ))) hz
    have h5 := le_suppVal hfin hne (n := ((1 : ℤ), (-1 : ℤ))) hz
    have h6 := le_suppVal hfin hne (n := ((-1 : ℤ), (1 : ℤ))) hz
    rw [hbot] at h4
    rw [hpin] at h5
    simp only [dot] at h1 h2 h3 h4 h5 h6
    exact ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
  -- 反向：H-表示，`E T = hexE` 保证这六条就是全部
  have hshape : T = hatShape (suppVal T ((1 : ℤ), (0 : ℤ))) (suppVal T ((0 : ℤ), (1 : ℤ)))
      (suppVal T ((-1 : ℤ), (1 : ℤ))) (suppVal T ((-1 : ℤ), (0 : ℤ))) := by
    ext z
    rw [mem_hatShape]
    refine ⟨hfwd z, fun hz => ?_⟩
    refine mem_of_dot_le_suppVal hfin hne harea hlc ?_
    intro n hn
    rw [hE] at hn
    simp only [Nivat.ShellSweep.hexE, Set.mem_insert_iff, Set.mem_singleton_iff] at hn
    obtain ⟨g1, g2, g3, g4, g5, g6⟩ := hz
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl
    · simp only [dot]; omega
    · simp only [dot]; omega
    · simp only [dot]; omega
    · rw [hbot]; simp only [dot]; omega
    · rw [hpin]; simp only [dot]; omega
    · simp only [dot]; omega
  refine ⟨?_, hshape⟩
  -- `Nondeg` 的六条 = 六个法向的面上各有两个不同格点
  obtain ⟨p1, hp1, q1, hq1, hd1, hs1, ht1⟩ := exists_pair_dot_eq_suppVal
    (T := T) (n := ((1 : ℤ), (0 : ℤ))) (by rw [hE]; simp [Nivat.ShellSweep.hexE])
  obtain ⟨p2, hp2, q2, hq2, hd2, hs2, ht2⟩ := exists_pair_dot_eq_suppVal
    (T := T) (n := ((-1 : ℤ), (0 : ℤ))) (by rw [hE]; simp [Nivat.ShellSweep.hexE])
  obtain ⟨p3, hp3, q3, hq3, hd3, hs3, ht3⟩ := exists_pair_dot_eq_suppVal
    (T := T) (n := ((0 : ℤ), (1 : ℤ))) (by rw [hE]; simp [Nivat.ShellSweep.hexE])
  obtain ⟨p4, hp4, q4, hq4, hd4, hs4, ht4⟩ := exists_pair_dot_eq_suppVal
    (T := T) (n := ((0 : ℤ), (-1 : ℤ))) (by rw [hE]; simp [Nivat.ShellSweep.hexE])
  obtain ⟨p5, hp5, q5, hq5, hd5, hs5, ht5⟩ := exists_pair_dot_eq_suppVal
    (T := T) (n := ((1 : ℤ), (-1 : ℤ))) (by rw [hE]; simp [Nivat.ShellSweep.hexE])
  obtain ⟨p6, hp6, q6, hq6, hd6, hs6, ht6⟩ := exists_pair_dot_eq_suppVal
    (T := T) (n := ((-1 : ℤ), (1 : ℤ))) (by rw [hE]; simp [Nivat.ShellSweep.hexE])
  have P1 := hfwd _ hp1; have Q1 := hfwd _ hq1
  have P2 := hfwd _ hp2; have Q2 := hfwd _ hq2
  have P3 := hfwd _ hp3; have Q3 := hfwd _ hq3
  have P4 := hfwd _ hp4; have Q4 := hfwd _ hq4
  have P5 := hfwd _ hp5; have Q5 := hfwd _ hq5
  have P6 := hfwd _ hp6; have Q6 := hfwd _ hq6
  simp only [dot] at hs1 ht1 hs2 ht2 hs3 ht3 hs4 ht4 hs5 ht5 hs6 ht6
  rw [ne_eq, Prod.ext_iff] at hd1 hd2 hd3 hd4 hd5 hd6
  exact ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩

/-- `U := ShellMink.hexA` 的特例，签名与 2026-09-20 之前完全一致（`ChainPartsFeed` 的接线
不受放宽影响）。 -/
theorem eq_hatShape_of_enveloped {T : Set (ℤ × ℤ)} (hfin : T.Finite)
    (henv : Enveloped (Nivat.ShellMink.hexA) T)
    (hbot : suppVal T ((0 : ℤ), (-1 : ℤ)) = 0)
    (hpin : suppVal T ((1 : ℤ), (-1 : ℤ)) = 1) :
    Nivat.ShellSweep.Nondeg
        (suppVal T ((1 : ℤ), (0 : ℤ)) + suppVal T ((-1 : ℤ), (0 : ℤ)))
        (suppVal T ((0 : ℤ), (1 : ℤ)))
        (suppVal T ((-1 : ℤ), (1 : ℤ)) - suppVal T ((-1 : ℤ), (0 : ℤ)))
        (1 + suppVal T ((-1 : ℤ), (0 : ℤ))) 0
      ∧ T = hatShape (suppVal T ((1 : ℤ), (0 : ℤ))) (suppVal T ((0 : ℤ), (1 : ℤ)))
          (suppVal T ((-1 : ℤ), (1 : ℤ))) (suppVal T ((-1 : ℤ), (0 : ℤ))) :=
  eq_hatShape_of_E_eq_hexE Nivat.ShellSweep.E_hexA_eq hfin henv hbot hpin

/-- **`hshape` 在链上的形式，放宽版。**  逐级套用 `eq_hatShape_of_E_eq_hexE`；
`Enveloped` 与有限性都对平移不变，所以前提写在 `A i` 上而不是 `Â_i` 上。 -/
theorem hshape_of_E_eq_hexE {U : Set (ℤ × ℤ)} {A : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ}
    (hEU : E U = Nivat.ShellSweep.hexE)
    (hfin : ∀ i, (A i).Finite)
    (henv : ∀ i, Enveloped U (A i))
    (hbot : ∀ i, suppVal (hatOf A kk ((1 : ℤ), (0 : ℤ)) i) ((0 : ℤ), (-1 : ℤ)) = 0)
    (hpin : ∀ i, suppVal (hatOf A kk ((1 : ℤ), (0 : ℤ)) i) ((1 : ℤ), (-1 : ℤ)) = 1) :
    ∀ i, ∃ a b c r : ℤ,
      Nivat.ShellSweep.Nondeg (a + r) b (c - r) (1 + r) 0 ∧
      hatOf A kk ((1 : ℤ), (0 : ℤ)) i = hatShape a b c r := by
  intro i
  have hfin' : (hatOf A kk ((1 : ℤ), (0 : ℤ)) i).Finite := by
    rw [hatOf_eq_shift_neg]; exact finite_shift (hfin i)
  have henv' : Enveloped U (hatOf A kk ((1 : ℤ), (0 : ℤ)) i) := by
    rw [hatOf_eq_shift_neg]
    exact (Nivat.LE2.enveloped_shift_right _).mpr (henv i)
  obtain ⟨hnd, heq⟩ := eq_hatShape_of_E_eq_hexE hEU hfin' henv' (hbot i) (hpin i)
  exact ⟨_, _, _, _, hnd, heq⟩

/-- **`hshape` 在链上的形式。**  `U := ShellMink.hexA` 的特例，签名不变。 -/
theorem hshape_of_enveloped {A : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ}
    (hfin : ∀ i, (A i).Finite)
    (henv : ∀ i, Enveloped (Nivat.ShellMink.hexA) (A i))
    (hbot : ∀ i, suppVal (hatOf A kk ((1 : ℤ), (0 : ℤ)) i) ((0 : ℤ), (-1 : ℤ)) = 0)
    (hpin : ∀ i, suppVal (hatOf A kk ((1 : ℤ), (0 : ℤ)) i) ((1 : ℤ), (-1 : ℤ)) = 1) :
    ∀ i, ∃ a b c r : ℤ,
      Nivat.ShellSweep.Nondeg (a + r) b (c - r) (1 + r) 0 ∧
      hatOf A kk ((1 : ℤ), (0 : ℤ)) i = hatShape a b c r :=
  hshape_of_E_eq_hexE Nivat.ShellSweep.E_hexA_eq hfin henv hbot hpin

/-- **交付物：`ofParts` 的 `AhatMono` binder，由抽子列的边长条件生产。**

结论逐字等于 `ChainAssemble.lean:186` 在 `vl = (1,0)` 处的
`AhatMono : ∀ i j, i ≤ j → hatOf A kk vl i ⊆ hatOf A kk vl j`。

前提里，除 `hEU` / `hext` 外在 `ofParts` 现有 binder 里**已经有或免费**：
* `henv` — 每级 `A_i` 是 `E(U)`-enveloped，即 `:484` item (iv) 的前半句。🟢 **2026-09-20
  下午：这条现在免费**——`U := ↑S` 时它就是 `maxA` 的第一合取，见 `enveloped_of_isMaxEnvIn`
  （§15）与 `envA_of_max`（`ChainMax.lean:106`）。上一版写成 `Enveloped hexA (A i)`，
  而链上给的是 `Enveloped (↑S) (A i)`，**那个形状在链上拿不到**。
* `hEU` — 🔴 **代价搬到了这里，这是本条唯一「我们加的、原文没有的」前提**：
  `E U = hexE`，即生成窗口恰好是六法向的六边形。原文的 𝒮_φ 不受此限。
  见 §15 小标题下的说明。
* `hbot` / `hpin` — `:494` + `:488` 的两条归一化，见 §14 小标题下的逐条原文对应。
  ⚠ `hbot` 是两半：`≤ 0` 来自 `:494` 的 `Â_i ⊂ H_{B_i}(ℓ) − k_i v⃗_ℓ`，
  `≥ 0` 来自 `:488`（`g₁ ∈ Â_i ∩ ℓ⁻`，所以交非空）。单靠 `:494` 只给不等号。
* `hfin` / `hne` — `exists_endpoint_shift` 的 `hfin`，与 `A_i ⊇ B_i ≠ ∅`。
* `hmono` — `b3_colle2.txt:486`，由 `ofParts` 的 `subBA` + `subAB` 复合而得
  （`B i ⊆ A i ⊆ B (i+1)`），已由 `ChainPartsFeed.A_mono_of_subBA_subAB` 落地。
* `hkk` — `kk_le_of_endpointAligned`（`:105`），已在本文件证好。
* `hext` — `b3_colle2.txt:500`/`:504` 抽完子列后的边长不减，**仍无生产者，但已非活口**
  （第 200 轮）：`ChainDataGeomParts`（`ChainPartsFeed.lean`）把 `AhatMono` 直接列成**字段**，
  37 个字段里没有 `hext`，所以 `exists_chainData` 的 populator **不经过本定理**。
  ⚠ 第 246 轮：字段数由「34」订正为 **37**（唯一口径是内核 `getStructureFields`，
  见 `ChainPartsFeed.lean:189-197`）。本条的 `hext` **0 命中**结论不受影响——订正只是补上
  `I₀` 等字段，没有一个叫 `hext`。
  `hext` 是本定理的形参，不是链上义务。要它有生产者，得先有人把本定理接上消费者。

量词对应原文:
* `∀ i j, i ≤ j` ↔ `:502` "we can assume that this holds for all `i`"；
* `hext` ↔ `:500` 的严格不等号与 `:504` 的等号合起来给的 `≤`；
* 结论 ↔ `:508` 图 6 说明里的 `Â_1 ⊂ Â_2 ⊂ ⋯`，即 `:506` 需要的有向性。

**未兑现的 binder（具名）**：`hEU`（六边形窗口，我们加的）、`hext`（`:500`/`:504`）、
`hbot`、`hpin`。前一版这里写「无」，指的是「没有未登记的读法型缺口」，不是「没有前提」——
措辞已改，避免误读。本条不涉及 `ofParts` 的 `ItemII` / `Exhausts`，也**不需要递归终止**
——`hmono` 只用到 `subBA`/`subAB` 这两个包含关系，与 `ChainRecursion` 的 `B (i+1) := A i` 无关。 -/
theorem ahatMono_ofParts_of_extraction_of_E {U : Set (ℤ × ℤ)} {A : ℕ → Set (ℤ × ℤ)}
    {kk : ℕ → ℕ}
    (hEU : E U = Nivat.ShellSweep.hexE)
    (henv : ∀ i, Enveloped U (A i))
    (hfin : ∀ i, (A i).Finite) (hne : ∀ i, (A i).Nonempty)
    (hmono : ∀ i j, i ≤ j → A i ⊆ A j) (hkk : ∀ i j, i ≤ j → kk i ≤ kk j)
    (hbot : ∀ i, suppVal (hatOf A kk ((1 : ℤ), (0 : ℤ)) i) ((0 : ℤ), (-1 : ℤ)) = 0)
    (hpin : ∀ i, suppVal (hatOf A kk ((1 : ℤ), (0 : ℤ)) i) ((1 : ℤ), (-1 : ℤ)) = 1)
    (hext : ∀ i j, i ≤ j →
      (face (hatOf A kk ((1 : ℤ), (0 : ℤ)) i) ((1 : ℤ), (-1 : ℤ))).encard
        ≤ (face (hatOf A kk ((1 : ℤ), (0 : ℤ)) j) ((1 : ℤ), (-1 : ℤ))).encard) :
    ∀ i j, i ≤ j →
      hatOf A kk ((1 : ℤ), (0 : ℤ)) i ⊆ hatOf A kk ((1 : ℤ), (0 : ℤ)) j := by
  have hshape := hshape_of_E_eq_hexE hEU hfin henv hbot hpin
  intro i j hij
  obtain ⟨a, b, c, r, hnd, heq⟩ := hshape i
  obtain ⟨a', b', c', r', hnd', heq'⟩ := hshape j
  have hfree : ∀ n : ℤ × ℤ, dot n ((1 : ℤ), (0 : ℤ)) ≤ 0 →
      suppVal (hatShape a b c r) n ≤ suppVal (hatShape a' b' c' r') n := by
    intro n hn
    have hmm := suppVal_hatOf_mono_of_nonpos hfin hne hmono hkk
      (vl := ((1 : ℤ), (0 : ℤ))) hn hij
    rwa [heq, heq'] at hmm
  have hb : b ≤ b' := by
    have hbb := hfree ((0 : ℤ), (1 : ℤ)) (by simp [dot])
    rwa [suppVal_hatShape_top hnd, suppVal_hatShape_top hnd'] at hbb
  have hc : c ≤ c' := by
    have hcc := hfree ((-1 : ℤ), (1 : ℤ)) (by simp [dot])
    rwa [suppVal_hatShape_ul hnd, suppVal_hatShape_ul hnd'] at hcc
  have hr : r ≤ r' := by
    have hrr := hfree ((-1 : ℤ), (0 : ℤ)) (by simp [dot])
    rwa [suppVal_hatShape_left hnd, suppVal_hatShape_left hnd'] at hrr
  have hE := hext i j hij
  rw [heq, heq'] at hE ⊢
  exact hatShape_subset_of_extraction hnd hnd' hb hc hr hE

/-- `U := ShellMink.hexA` 的特例。**签名与 2026-09-20 之前逐字一致**，
`ChainPartsFeed.lean:290` 的接线不因放宽而改。 -/
theorem ahatMono_ofParts_of_extraction {A : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ}
    (henv : ∀ i, Enveloped (Nivat.ShellMink.hexA) (A i))
    (hfin : ∀ i, (A i).Finite) (hne : ∀ i, (A i).Nonempty)
    (hmono : ∀ i j, i ≤ j → A i ⊆ A j) (hkk : ∀ i j, i ≤ j → kk i ≤ kk j)
    (hbot : ∀ i, suppVal (hatOf A kk ((1 : ℤ), (0 : ℤ)) i) ((0 : ℤ), (-1 : ℤ)) = 0)
    (hpin : ∀ i, suppVal (hatOf A kk ((1 : ℤ), (0 : ℤ)) i) ((1 : ℤ), (-1 : ℤ)) = 1)
    (hext : ∀ i j, i ≤ j →
      (face (hatOf A kk ((1 : ℤ), (0 : ℤ)) i) ((1 : ℤ), (-1 : ℤ))).encard
        ≤ (face (hatOf A kk ((1 : ℤ), (0 : ℤ)) j) ((1 : ℤ), (-1 : ℤ))).encard) :
    ∀ i j, i ≤ j →
      hatOf A kk ((1 : ℤ), (0 : ℤ)) i ⊆ hatOf A kk ((1 : ℤ), (0 : ℤ)) j :=
  ahatMono_ofParts_of_extraction_of_E Nivat.ShellSweep.E_hexA_eq henv hfin hne hmono hkk
    hbot hpin hext

/-! ### §15 `henv` 的生产者：`maxA` 的第一合取

§14 放宽之后，`henv` 这条前提在链上是**免费**的。`ChainDataGeomParts.maxA`
（`ChainPartsFeed.lean:295`）的类型是

    ∀ i, IsMaxEnvIn (EnvOf (↑S : Set (ℤ × ℤ))) (canonA η xper vl B u i) (A i)

而 `IsMaxEnvIn Env C A` 的第一合取就是 `Env A`（`ChainMax.lean:62`），
`EnvOf U T` 按定义就是 `Enveloped U T`（`LatticeEdges.lean:2433`，`envOf_iff` 是 `Iff.rfl`）。
所以 `henv := fun i => (maxA i).1`，原文对应是 `:484` item (iv) 那句
"`A_i` is a maximal set … among all `E(𝒮_φ)`-enveloped sets `𝒯`" 的**前半句**
（"is `E(𝒮_φ)`-enveloped"），极大性一点没用到。

🔴 **代价搬到哪儿去了，明说**：`U` 现在是 `↑S = 𝒮_φ`，于是 §14 的 `hEU` 变成

    E (↑S : Set (ℤ × ℤ)) = Nivat.ShellSweep.hexE

即「生成窗口恰好是六边形，且六个法向就是 `hexE` 那六个」。这**不是**原文的假设，
原文的 𝒮_φ 是任意生成集（`b3_colle2.txt:777` 起全篇不限制边数）。所以 §11–§14 的
范围限定没有消失，只是从「`A_i` 被 `hexA` 包络」这个**不可能从链上拿到**的形状，
换成了一条**关于 `S` 的具名等式**——它至少可以在调用点被判定、被证伪、被当作分支条件。
法向多于六个时 `hatShape` 这个正规形根本不存在，本路线全部作废，这一条未变。 -/

/-- **`henv`，从 `maxA` 拿。**  `IsMaxEnvIn` 的第一合取，极大性未用。

原文：`b3_colle2.txt:484` item (iv)，"`A_i` is a maximal set with respect to partial ordering
by inclusion among all `E(𝒮_φ)`-enveloped sets `𝒯 ⊂ ℤ²` such that …"。
逐个量词：`∀ i` ↔ 原文的 `A_i` 对每个 `i`；`U` ↔ `𝒮_φ`；结论 ↔ "is `E(𝒮_φ)`-enveloped"。
`C` 在这里完全自由，因为约束集（`B_i ⊂ 𝒯 ⊂ H_{B_i}(ℓ)` 加上一致性）只被极大性用到。 -/
theorem enveloped_of_isMaxEnvIn {U : Set (ℤ × ℤ)} {C A : ℕ → Set (ℤ × ℤ)}
    (hmax : ∀ i, Nivat.Colle35.IsMaxEnvIn (Nivat.LE2.EnvOf U) (C i) (A i)) :
    ∀ i, Enveloped U (A i) :=
  fun i => (hmax i).1

/-- 同一条，`Env` 还没被 `hEnv` 消掉时的形状（`ofParts` 的通用签名用得上）。 -/
theorem enveloped_of_isMaxEnvIn_of_eq {U : Set (ℤ × ℤ)} {Env : Set (ℤ × ℤ) → Prop}
    {C A : ℕ → Set (ℤ × ℤ)} (hEnv : Env = Nivat.LE2.EnvOf U)
    (hmax : ∀ i, Nivat.Colle35.IsMaxEnvIn Env (C i) (A i)) :
    ∀ i, Enveloped U (A i) := by
  intro i
  have h := (hmax i).1
  rw [hEnv] at h
  exact h

/-- **一次调用的交付物：从 `maxA` 直接到 `ofParts` 的 `AhatMono` binder。**

这是集成者要接的那一条：`henv` 已经被 `maxA` 吃掉，剩下的前提全部是**具名的**——
`hES`（六边形窗口，§15 小标题下已说明这是我们加的、不是原文的）、
`hbot` / `hpin`（`:494` + `:488` 的两条归一化）、`hext`（`:500`/`:504`），
其余四条 `hfin` / `hne` / `hmono` / `hkk` 在 `ChainDataGeomParts` 里是免费的。 -/
theorem ahatMono_ofParts_of_maxA {α : Type*} {η xper : Nivat.Config α} {vl : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} {B A : ℕ → Set (ℤ × ℤ)} {u : ℕ → ℤ × ℤ} {kk : ℕ → ℕ}
    (hES : E (↑S : Set (ℤ × ℤ)) = Nivat.ShellSweep.hexE)
    (hmax : ∀ i, Nivat.Colle35.IsMaxEnvIn (Nivat.LE2.EnvOf (↑S : Set (ℤ × ℤ)))
      (Nivat.Colle35.canonA η xper vl B u i) (A i))
    (hfin : ∀ i, (A i).Finite) (hne : ∀ i, (A i).Nonempty)
    (hmono : ∀ i j, i ≤ j → A i ⊆ A j) (hkk : ∀ i j, i ≤ j → kk i ≤ kk j)
    (hbot : ∀ i, suppVal (hatOf A kk ((1 : ℤ), (0 : ℤ)) i) ((0 : ℤ), (-1 : ℤ)) = 0)
    (hpin : ∀ i, suppVal (hatOf A kk ((1 : ℤ), (0 : ℤ)) i) ((1 : ℤ), (-1 : ℤ)) = 1)
    (hext : ∀ i j, i ≤ j →
      (face (hatOf A kk ((1 : ℤ), (0 : ℤ)) i) ((1 : ℤ), (-1 : ℤ))).encard
        ≤ (face (hatOf A kk ((1 : ℤ), (0 : ℤ)) j) ((1 : ℤ), (-1 : ℤ))).encard) :
    ∀ i j, i ≤ j →
      hatOf A kk ((1 : ℤ), (0 : ℤ)) i ⊆ hatOf A kk ((1 : ℤ), (0 : ℤ)) j :=
  ahatMono_ofParts_of_extraction_of_E hES (enveloped_of_isMaxEnvIn hmax) hfin hne hmono hkk
    hbot hpin hext

/-! ### §16 `hbot` / `hpin` 的生产者：`:494` 的半平面 + `:488` 的端点对齐

§14/§15 之后剩下的三条前提里，`hbot` 与 `hpin` 本节打掉，换成它们在原文里的**原始形态**：

* `hhp` ↔ `b3_colle2.txt:494`：`Â_i ⊂ H_{B_i}(ℓ) − k_i v⃗_ℓ`。`v⃗_ℓ ∥ ℓ` 所以平移不动那个半平面，
  在把 `ℓ⁻` 取成 `{y = 0}`、`v⃗_ℓ = (1,0)` 的坐标里它就是 `∀ z ∈ Â_i, 0 ≤ z.2`。
* `halign` ↔ `b3_colle2.txt:488`：「`g₁` 是 `A₁ ∩ ℓ⁻` 的终点，`k_i` 使得
  `(A_i − k_i v⃗_ℓ) ∩ ℓ⁻` 的终点与 `g₁` 重合」。同一坐标里 `g₁ = (1,0)`，
  写成 `IsGreatest {t | g₁ + t•v⃗_ℓ ∈ Â_i ∧ …} 0`，**与 `kk_le_of_endpointAligned`（`:105`）
  用的是同一条前提**，所以生产者只需给一次。它有生产者：
  `Nivat.AItemFour.exists_endpoint_shift`（`AItemFour.lean:329`）。

为什么 `hpin` 不是自由的、又为什么它能被证出来：`suppVal Â_i (1,−1) ≥ 1` 只要 `g₁ ∈ Â_i`；
难的是 `≤ 1`，它需要「`(1,−1)` 方向的支撑值在 `y = 0` 这条线上被取到」。
本节用二维 H-表示直接**造出**那个点：令 `s := suppVal Â_i (1,−1)`，验证 `(s, 0)` 满足六条边
不等式（这一步要 `hbot`、`hhp` 和 `E Â_i = hexE`），于是 `(s,0) ∈ Â_i`；
再由 `halign` 得 `s − 1 ≤ 0`。**不循环**：这里没有用到 `Â_i` 是 `hatShape`，
用的是 `mem_of_dot_le_suppVal`（`LatticeEdges.lean:1393`）本身。

⚠ 范围限定不变：`hEU`（六法向）仍是我们加的，见 §15。 -/

/-- `suppVal` 的上界形态。`LatticeEdges.lean` 只有 `le_suppVal`（`:749`），没有这条。 -/
theorem suppVal_le_of_forall {T : Set (ℤ × ℤ)} (hfin : T.Finite) (hne : T.Nonempty)
    {n : ℤ × ℤ} {c : ℤ} (h : ∀ z ∈ T, dot n z ≤ c) : suppVal T n ≤ c := by
  obtain ⟨v, hv, hveq⟩ := exists_suppVal_eq hfin hne n
  rw [← hveq]
  exact h v hv

/-- **`hbot`。**  原文：`:494`（半平面，给 `≤ 0`）+ `:488`（`g₁ ∈ Â_i ∩ ℓ⁻`，给 `≥ 0`）。
单靠 `:494` 只有不等号——这是 2026-09-20 对上一版归属的订正。 -/
theorem suppVal_bot_of_halfPlane {T : Set (ℤ × ℤ)} (hfin : T.Finite)
    (hhp : ∀ z ∈ T, 0 ≤ z.2) (hg : ((1 : ℤ), (0 : ℤ)) ∈ T) :
    suppVal T ((0 : ℤ), (-1 : ℤ)) = 0 := by
  have hne : T.Nonempty := ⟨_, hg⟩
  refine le_antisymm (suppVal_le_of_forall hfin hne ?_) ?_
  · intro z hz
    have := hhp z hz
    simp only [dot]
    omega
  · have := le_suppVal hfin hne (n := ((0 : ℤ), (-1 : ℤ))) hg
    simpa [dot] using this

/-- **`hpin`。**  原文：`:488` 的端点条件。见本节小标题下的「不循环」说明。 -/
theorem suppVal_slant_of_align {U T : Set (ℤ × ℤ)}
    (hEU : E U = Nivat.ShellSweep.hexE) (hfin : T.Finite) (henv : Enveloped U T)
    (hhp : ∀ z ∈ T, 0 ≤ z.2) (hg : ((1 : ℤ), (0 : ℤ)) ∈ T)
    (halign : ∀ t : ℤ, 0 < t → ((1 : ℤ) + t, (0 : ℤ)) ∉ T) :
    suppVal T ((1 : ℤ), (-1 : ℤ)) = 1 := by
  have hne : T.Nonempty := ⟨_, hg⟩
  have hEfin : (E U).Finite := by rw [hEU]; exact finite_hexE
  have hE : E T = Nivat.ShellSweep.hexE := by rw [Enveloped.E_eq hEfin henv, hEU]
  have hm1 : ((1 : ℤ), (0 : ℤ)) ∈ E U := by rw [hEU]; simp [Nivat.ShellSweep.hexE]
  have hm2 : ((0 : ℤ), (1 : ℤ)) ∈ E U := by rw [hEU]; simp [Nivat.ShellSweep.hexE]
  have hm3 : ((1 : ℤ), (-1 : ℤ)) ∈ E U := by rw [hEU]; simp [Nivat.ShellSweep.hexE]
  have harea : PosArea T :=
    posArea_of_envOf hm1 hm2 hm3 (by simp) (by simp) (by simp) hEfin henv
  have hlc : IsLatticeConvexRegion T := henv.1.1
  have hbot : suppVal T ((0 : ℤ), (-1 : ℤ)) = 0 := suppVal_bot_of_halfPlane hfin hhp hg
  set s := suppVal T ((1 : ℤ), (-1 : ℤ)) with hsdef
  have hs1 : 1 ≤ s := by
    have := le_suppVal hfin hne (n := ((1 : ℤ), (-1 : ℤ))) hg
    simpa [dot] using this
  -- `(1,-1)` 的最大点纵坐标非负，故其横坐标 ≥ s，于是 `suppVal (1,0) ≥ s`
  obtain ⟨v, hv, hveq⟩ := exists_suppVal_eq hfin hne ((1 : ℤ), (-1 : ℤ))
  have hvy : 0 ≤ v.2 := hhp v hv
  simp only [dot] at hveq
  have hr : s ≤ suppVal T ((1 : ℤ), (0 : ℤ)) := by
    have := le_suppVal hfin hne (n := ((1 : ℤ), (0 : ℤ))) hv
    simp only [dot] at this
    omega
  have hl : (-1 : ℤ) ≤ suppVal T ((-1 : ℤ), (0 : ℤ)) := by
    have := le_suppVal hfin hne (n := ((-1 : ℤ), (0 : ℤ))) hg
    simpa [dot] using this
  have ht : (0 : ℤ) ≤ suppVal T ((0 : ℤ), (1 : ℤ)) := by
    have := le_suppVal hfin hne (n := ((0 : ℤ), (1 : ℤ))) hg
    simpa [dot] using this
  have hu : (-1 : ℤ) ≤ suppVal T ((-1 : ℤ), (1 : ℤ)) := by
    have := le_suppVal hfin hne (n := ((-1 : ℤ), (1 : ℤ))) hg
    simpa [dot] using this
  -- H-表示造点：`(s, 0) ∈ T`
  have hmem : ((s : ℤ), (0 : ℤ)) ∈ T := by
    refine mem_of_dot_le_suppVal hfin hne harea hlc ?_
    intro n hn
    rw [hE] at hn
    simp only [Nivat.ShellSweep.hexE, Set.mem_insert_iff, Set.mem_singleton_iff] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl
    · simp only [dot]; omega
    · simp only [dot]; omega
    · simp only [dot]; omega
    · rw [hbot]; simp only [dot]; omega
    · simp only [dot]; omega
    · simp only [dot]; omega
  by_contra hcon
  have h2 : 1 < s := lt_of_le_of_ne hs1 (Ne.symm hcon)
  refine halign (s - 1) (by omega) ?_
  have hrw : ((1 : ℤ) + (s - 1), (0 : ℤ)) = ((s : ℤ), (0 : ℤ)) := by
    simp only [Prod.mk.injEq]
    exact ⟨by ring, trivial⟩
  rw [hrw]
  exact hmem

/-- **链上形态：一条 `:488` 前提同时给出 `hbot` 与 `hpin`。**

`halign` 与 `kk_le_of_endpointAligned`（`:105`）的第四个前提**逐字同型**，所以生产者
（`AItemFour.exists_endpoint_shift`）供一次即可同时喂 `hkk`、`hbot`、`hpin`。 -/
theorem bot_pin_of_endpointAligned {U : Set (ℤ × ℤ)} {A : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ}
    (hEU : E U = Nivat.ShellSweep.hexE)
    (hfin : ∀ i, (A i).Finite)
    (henv : ∀ i, Enveloped U (A i))
    (hhp : ∀ i, ∀ z ∈ hatOf A kk ((1 : ℤ), (0 : ℤ)) i, 0 ≤ z.2)
    (halign : ∀ i, IsGreatest {t : ℤ |
        ((1 : ℤ), (0 : ℤ)) + t • ((1 : ℤ), (0 : ℤ)) ∈ hatOf A kk ((1 : ℤ), (0 : ℤ)) i
          ∧ dot ((0 : ℤ), (-1 : ℤ))
              (((1 : ℤ), (0 : ℤ)) + t • ((1 : ℤ), (0 : ℤ))) = 0} 0) :
    (∀ i, suppVal (hatOf A kk ((1 : ℤ), (0 : ℤ)) i) ((0 : ℤ), (-1 : ℤ)) = 0)
      ∧ (∀ i, suppVal (hatOf A kk ((1 : ℤ), (0 : ℤ)) i) ((1 : ℤ), (-1 : ℤ)) = 1) := by
  have key : ∀ i, ((1 : ℤ), (0 : ℤ)) ∈ hatOf A kk ((1 : ℤ), (0 : ℤ)) i ∧
      ∀ t : ℤ, 0 < t → ((1 : ℤ) + t, (0 : ℤ)) ∉ hatOf A kk ((1 : ℤ), (0 : ℤ)) i := by
    intro i
    constructor
    · have h := (halign i).1.1
      simpa using h
    · intro t ht hmem
      have hin : t ∈ {t : ℤ |
          ((1 : ℤ), (0 : ℤ)) + t • ((1 : ℤ), (0 : ℤ)) ∈ hatOf A kk ((1 : ℤ), (0 : ℤ)) i
            ∧ dot ((0 : ℤ), (-1 : ℤ))
                (((1 : ℤ), (0 : ℤ)) + t • ((1 : ℤ), (0 : ℤ))) = 0} := by
        refine ⟨?_, ?_⟩
        · simpa using hmem
        · simp [dot]
      have := (halign i).2 hin
      omega
  have hfin' : ∀ i, (hatOf A kk ((1 : ℤ), (0 : ℤ)) i).Finite := by
    intro i; rw [hatOf_eq_shift_neg]; exact finite_shift (hfin i)
  have henv' : ∀ i, Enveloped U (hatOf A kk ((1 : ℤ), (0 : ℤ)) i) := by
    intro i
    rw [hatOf_eq_shift_neg]
    exact (Nivat.LE2.enveloped_shift_right _).mpr (henv i)
  exact ⟨fun i => suppVal_bot_of_halfPlane (hfin' i) (hhp i) (key i).1,
    fun i => suppVal_slant_of_align hEU (hfin' i) (henv' i) (hhp i) (key i).1 (key i).2⟩

/-- **交付物：`ofParts` 的 `AhatMono` binder，前提全部是原文条款。**

`henv` 被 `maxA` 吃掉（§15），`hbot` / `hpin` 被 `hhp` + `halign` 吃掉（§16）。
剩下的未兑现 binder 有四条（前一版写「三条」，数的是项目符号个数，名字是四个——第 200 轮订正），
全部具名：
* `hES : E (↑S) = hexE` — 🔴 **我们加的**，原文无此限制，见 §15。
  ⚠ 这条与上面 `ahatMono_ofParts_of_extraction_of_E` 的 `hEU` 是**两条不同的债**：那条约束的是
  抽象的 `U`，这条约束的是具体的 `↑S`。别把两者当同一条销账。
* `hhp` — `:494`；`halign` — `:488`（有生产者 `AItemFour.exists_endpoint_shift`）；
* `hext` — `:500`/`:504`，**仍无生产者，但已非活口**（第 200 轮）：理由同
  `ahatMono_ofParts_of_extraction_of_E`——`ChainDataGeomParts` 的 37 个字段里
  直接就有 `AhatMono`，没有 `hext`，本定理不在 `exists_chainData` 的生产路径上。
  ⚠ 第 246 轮：字段数由「34」订正为 **37**（内核口径，`ChainPartsFeed.lean:189-197`）；
  `hext` **0 命中**这一点不受影响。 -/
theorem ahatMono_ofParts_of_maxA_of_aligned {α : Type*} {η xper : Nivat.Config α}
    {vl : ℤ × ℤ} {S : Finset (ℤ × ℤ)} {B A : ℕ → Set (ℤ × ℤ)} {u : ℕ → ℤ × ℤ} {kk : ℕ → ℕ}
    (hES : E (↑S : Set (ℤ × ℤ)) = Nivat.ShellSweep.hexE)
    (hmax : ∀ i, Nivat.Colle35.IsMaxEnvIn (Nivat.LE2.EnvOf (↑S : Set (ℤ × ℤ)))
      (Nivat.Colle35.canonA η xper vl B u i) (A i))
    (hfin : ∀ i, (A i).Finite) (hne : ∀ i, (A i).Nonempty)
    (hmono : ∀ i j, i ≤ j → A i ⊆ A j) (hkk : ∀ i j, i ≤ j → kk i ≤ kk j)
    (hhp : ∀ i, ∀ z ∈ hatOf A kk ((1 : ℤ), (0 : ℤ)) i, 0 ≤ z.2)
    (halign : ∀ i, IsGreatest {t : ℤ |
        ((1 : ℤ), (0 : ℤ)) + t • ((1 : ℤ), (0 : ℤ)) ∈ hatOf A kk ((1 : ℤ), (0 : ℤ)) i
          ∧ dot ((0 : ℤ), (-1 : ℤ))
              (((1 : ℤ), (0 : ℤ)) + t • ((1 : ℤ), (0 : ℤ))) = 0} 0)
    (hext : ∀ i j, i ≤ j →
      (face (hatOf A kk ((1 : ℤ), (0 : ℤ)) i) ((1 : ℤ), (-1 : ℤ))).encard
        ≤ (face (hatOf A kk ((1 : ℤ), (0 : ℤ)) j) ((1 : ℤ), (-1 : ℤ))).encard) :
    ∀ i j, i ≤ j →
      hatOf A kk ((1 : ℤ), (0 : ℤ)) i ⊆ hatOf A kk ((1 : ℤ), (0 : ℤ)) j := by
  have henv := enveloped_of_isMaxEnvIn hmax
  obtain ⟨hbot, hpin⟩ := bot_pin_of_endpointAligned hES hfin henv hhp halign
  exact ahatMono_ofParts_of_extraction_of_E hES henv hfin hne hmono hkk hbot hpin hext

/-! ## 17. What survives when `E U` is an arbitrary finite fan

集成者 2026-09-20 的问题：`hES : E (↑S) = hexE` 是我们加的，原文不限制 𝒮_φ 的边数。
去掉它之后还剩什么？本节给内核答案，**三条都不含 `hexE`、不含 `(1,0)`**：

1. `eq_hrep_of_enveloped` — 正规形本身对任意有限 `E U` 成立：`T` 就是它在 `E U` 各法向上
   支撑半平面的交（H-表示）。`hatShape` 只是 `E U = hexE` 时把这个交写成六个参数。
2. `subset_iff_suppVal_le_of_enveloped` — 同一扇上两个 enveloped 集的包含关系**等价于**
   逐法向的支撑值不等式。
3. `ahatMono_iff_fwd_suppVal_enveloped` — `AhatMono` **等价于** `hslack`
   （`ahatMono_of_suppVal_slack_enveloped` 的残余前提）。原来只有 `⇐`；补上 `⇒` 之后
   `hslack` 从「充分条件」变成「恰好欠的那条」：正法向（`0 < ⟪n, v⃗_ℓ⟫`）上的支撑值
   在扣掉 `k_i ⟪n, v⃗_ℓ⟫` 之后不减。

所以六边形限定真正买到的只有一件事：正法向恰好两个（`dot_vl_pos_hexE`），一个由 `:488`
钉死、一个由 `:500`/`:504` 控制。§18 造八边形见证，说明正法向到三个时 `:500`/`:504` 的
字面陈述控制不住第三个。 -/

/-- **H-表示，任意有限扇。**  原文：`b3_colle2.txt:402`（Definition 3.2，`E(𝒯) = E(𝒮_φ)`）。
`hatShape` 正规形（`eq_hatShape_of_E_eq_hexE`）是本条在 `E U = hexE` 处的展开。

量词对应：`U` ↔ 𝒮_φ；`T` ↔ 一个 `E(𝒮_φ)`-enveloped 集；`n ∈ E U` ↔ 𝒮_φ 的每条边的法向。
`harea` 是 Definition 3.2 对 𝒯 的 "positive area" 要求（`:402`）。 -/
theorem eq_hrep_of_enveloped {U T : Set (ℤ × ℤ)} (hEU : (E U).Finite) (hfin : T.Finite)
    (harea : PosArea T) (henv : Enveloped U T) :
    T = {z | ∀ n ∈ E U, dot n z ≤ suppVal T n} := by
  have hne : T.Nonempty := by obtain ⟨p, hp, -⟩ := harea; exact ⟨p, hp⟩
  have hE : E T = E U := Enveloped.E_eq hEU henv
  ext z
  constructor
  · intro hz n _
    exact le_suppVal hfin hne hz
  · intro hz
    refine mem_of_dot_le_suppVal hfin hne harea henv.1.1 ?_
    intro n hn
    rw [hE] at hn
    exact hz n hn

/-- **同扇上的包含 ⟺ 逐法向支撑不等式。**  只有右边需要 enveloped（H-表示用在 `T'` 上）。 -/
theorem subset_iff_suppVal_le_of_enveloped {U T T' : Set (ℤ × ℤ)} (hEU : (E U).Finite)
    (hfin : T.Finite) (hne : T.Nonempty) (hfin' : T'.Finite) (harea' : PosArea T')
    (henv' : Enveloped U T') :
    T ⊆ T' ↔ ∀ n ∈ E U, suppVal T n ≤ suppVal T' n := by
  have hne' : T'.Nonempty := by obtain ⟨p, hp, -⟩ := harea'; exact ⟨p, hp⟩
  constructor
  · intro hsub n _
    exact suppVal_mono hfin hne hfin' hne' hsub n
  · intro h z hz
    rw [eq_hrep_of_enveloped hEU hfin' harea' henv']
    intro n hn
    exact le_trans (le_suppVal hfin hne hz) (h n hn)

theorem hatOf_nonempty {A : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ} {vl : ℤ × ℤ} {i : ℕ}
    (h : (A i).Nonempty) : (hatOf A kk vl i).Nonempty := by
  obtain ⟨z, hz⟩ := h
  refine ⟨z - (kk i : ℤ) • vl, ?_⟩
  show z - (kk i : ℤ) • vl + (kk i : ℤ) • vl ∈ A i
  simpa using hz

/-- **`AhatMono` 恰好等价于正法向上的支撑松弛。**  任意 `vl`、任意有限扇。

原文：`b3_colle2.txt:508`（图 6 说明，`Â_i ⊂ Â_j` 唯一出现处）与 `:488`（`Â_i := A_i − k_i v⃗_ℓ`）。
`⇐` 是 `ahatMono_of_suppVal_slack_enveloped`；`⇒` 是 `suppVal_mono` 加 `suppVal_hatOf`。
右边在 `⟪n, v⃗_ℓ⟫ ≤ 0` 的法向上由 `:486` + `kk_le_of_endpointAligned` 免费成立
（`suppVal_hatOf_mono_of_nonpos`），所以限制到 `0 < ⟪n, v⃗_ℓ⟫` 不丢信息。 -/
theorem ahatMono_iff_fwd_suppVal_enveloped
    {U : Set (ℤ × ℤ)} {A : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ} {vl : ℤ × ℤ}
    (hEU : (E U).Finite) (henv : ∀ i, Enveloped U (A i))
    (hfin : ∀ i, (A i).Finite) (hne : ∀ i, (A i).Nonempty)
    (harea : ∀ i, PosArea (A i))
    (hmono : ∀ i j, i ≤ j → A i ⊆ A j)
    (hkk : ∀ i j, i ≤ j → kk i ≤ kk j) :
    (∀ i j, i ≤ j → hatOf A kk vl i ⊆ hatOf A kk vl j) ↔
      (∀ i j, i ≤ j → ∀ n ∈ E U, 0 < dot n vl →
        suppVal (A i) n + ((kk j : ℤ) - (kk i : ℤ)) * dot n vl ≤ suppVal (A j) n) := by
  constructor
  · intro h i j hij n _ _
    have hfi : (hatOf A kk vl i).Finite := by
      rw [hatOf_eq_shift_neg]; exact finite_shift (hfin i)
    have hfj : (hatOf A kk vl j).Finite := by
      rw [hatOf_eq_shift_neg]; exact finite_shift (hfin j)
    have hm := suppVal_mono hfi (hatOf_nonempty (hne i)) hfj (hatOf_nonempty (hne j))
      (h i j hij) n
    rw [suppVal_hatOf (hfin i) (hne i), suppVal_hatOf (hfin j) (hne j)] at hm
    linarith
  · intro h
    exact ahatMono_of_suppVal_slack_enveloped hEU henv hfin hne harea
      (fun i => (henv i).1.1) hmono hkk h

/-! ## 18. 八边形见证：正法向三个时，`:500`/`:504` 的字面陈述控制不住第三个

§12 末尾（`:1563-1567`）写着「`m = 8` 的扇正侧有三个法向，第三个自由——我没有八边形反例，
也不断言它存在」。本节把它造出来。

**几何（`v⃗_ℓ = (1,0)`，`ℓ⁻ = {y = 0}`，`g₁ = (1,0)`）。**  八边形扇
`octE = {±(1,0), ±(0,1), ±(1,1), ±(1,-1)}` 的正法向是 `(1,-1)`、`(1,0)`、`(1,1)`。
从 `g₁` 逆时针走：`(1,-1)`-边方向 `(1,1)` 长 `ℓ₁`，到顶点 `(1+ℓ₁, ℓ₁)`；`(1,0)`-边方向 `(0,1)`
长 `ℓ₂`，到顶点 `(1+ℓ₁, ℓ₁+ℓ₂)`。于是

    h(1,-1) = 1（`:488` 钉死）,  h(1,0) = 1 + ℓ₁,  h(1,1) = 1 + 2ℓ₁ + ℓ₂.

`:498-500` 取 `J` 为最小的、边长无穷次严格增长的指标。见证里 `ℓ₁ = i` 每步严格增长，所以
`J = ι+1`，`:504` 空真，**`ℓ₂` 不受任何原文条款约束**。取 `ℓ₂ : 5 ↦ 2`，则 `h(1,1)` 从 `8`
降到 `7`，`(2,6) ∈ Â₁ \ Â₂`。`:486`（`A_i ⊆ A_{i+1}`）由 `k_i = 10·i` 吸收：`Â_i` 左移 `10` 后
落进 `Â_{i+1}`，只要左侧三个支撑值每步长 `10`。

**这说明什么、不说明什么。**  被证伪的是「`ahatMono_ofParts_of_maxA_of_aligned` 的前提表
把 `hES : E U = hexE` 换成 `E U = octE`」——即本文件这条路线在八边形上不成立，
`hES` 不是装饰。它**不**说明 Collé 的论证在八边形上有洞：`maxA` 的极大性（`:484` 后半句）
在这里只用了 enveloped 那一半（`enveloped_of_isMaxEnvIn` 丢掉极大性），见证没有兑现极大性
——§8 的手法（`B_i := A_i`、横向隔开的 `u_i`）可以兑现，但那是下一轮的活，本轮不做、不断言。
未兑现的 binder 逐条见 `not_ahatMono_octagon` 的 docstring。 -/

/-- 八边形 `{x ≤ a, x+y ≤ s, y ≤ b, −x+y ≤ c, −x ≤ r, −x−y ≤ t, −y ≤ e, x−y ≤ d}`。
顶点逆时针（从右下起）：`(d−e,−e), (a,a−d), (a,s−a), (s−b,b), (b−c,b), (−r,c−r), (−r,r−t),
(e−t,−e)`。`ShellSweep.hexShape` 的八法向版本。 -/
def octShape (a s b c r t e d : ℤ) : Set (ℤ × ℤ) :=
  {z | z.1 ≤ a ∧ z.1 + z.2 ≤ s ∧ z.2 ≤ b ∧ -z.1 + z.2 ≤ c ∧ -z.1 ≤ r ∧ -z.1 - z.2 ≤ t ∧
    -z.2 ≤ e ∧ z.1 - z.2 ≤ d}

theorem mem_octShape {a s b c r t e d : ℤ} {z : ℤ × ℤ} :
    z ∈ octShape a s b c r t e d ↔
      z.1 ≤ a ∧ z.1 + z.2 ≤ s ∧ z.2 ≤ b ∧ -z.1 + z.2 ≤ c ∧ -z.1 ≤ r ∧ -z.1 - z.2 ≤ t ∧
        -z.2 ≤ e ∧ z.1 - z.2 ≤ d := Iff.rfl

/-- 八边形扇的八个法向。 -/
def octE : Set (ℤ × ℤ) :=
  {((1 : ℤ), (0 : ℤ)), ((1 : ℤ), (1 : ℤ)), ((0 : ℤ), (1 : ℤ)), ((-1 : ℤ), (1 : ℤ)),
    ((-1 : ℤ), (0 : ℤ)), ((-1 : ℤ), (-1 : ℤ)), ((0 : ℤ), (-1 : ℤ)), ((1 : ℤ), (-1 : ℤ))}

theorem finite_octE : octE.Finite := by
  unfold octE
  exact (((((((Set.finite_singleton _).insert _).insert _).insert _).insert _).insert _).insert
    _).insert _

/-- 原文：`b3_colle2.txt:402`（Definition 3.2 的 `|w ∩ 𝒰| ≤ |ϖ ∩ 𝒯|`；对单位八边形 `oct1`
这就是「𝒯 的每条边至少两个格点」）。八个字段 = 八条边各长 `≥ 1`，按顶点顺序。
与 `ShellSweep.Nondeg`（六边形）同构，不是新的量词。 -/
structure Nondeg8 (a s b c r t e d : ℤ) : Prop where
  bot : 1 ≤ d + t - 2 * e
  lr : 1 ≤ a - d + e
  right : 1 ≤ s - 2 * a + d
  ur : 1 ≤ b - s + a
  top : 1 ≤ s + c - 2 * b
  ul : 1 ≤ b - c + r
  left : 1 ≤ c + t - 2 * r
  ll : 1 ≤ e - t + r

section OctFaces

variable {a s b c r t e d : ℤ} (h : Nondeg8 a s b c r t e d)
include h

/-- 八个法向的面上各有两个不同格点（相邻两个顶点）。 -/
theorem face_pair_octShape (n : ℤ × ℤ) (hn : n ∈ octE) :
    ∃ z ∈ face (octShape a s b c r t e d) n,
      ∃ z' ∈ face (octShape a s b c r t e d) n, z ≠ z' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  simp only [octE, Set.mem_insert_iff, Set.mem_singleton_iff] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨(a, a - d), ⟨?_, ?_⟩, (a, s - a), ⟨?_, ?_⟩, ?_⟩
    · simp only [mem_octShape]; omega
    · intro y hy; simp only [mem_octShape] at hy; simp only [dot]; omega
    · simp only [mem_octShape]; omega
    · intro y hy; simp only [mem_octShape] at hy; simp only [dot]; omega
    · intro hh; rw [Prod.ext_iff] at hh; omega
  · refine ⟨(a, s - a), ⟨?_, ?_⟩, (s - b, b), ⟨?_, ?_⟩, ?_⟩
    · simp only [mem_octShape]; omega
    · intro y hy; simp only [mem_octShape] at hy; simp only [dot]; omega
    · simp only [mem_octShape]; omega
    · intro y hy; simp only [mem_octShape] at hy; simp only [dot]; omega
    · intro hh; rw [Prod.ext_iff] at hh; omega
  · refine ⟨(s - b, b), ⟨?_, ?_⟩, (b - c, b), ⟨?_, ?_⟩, ?_⟩
    · simp only [mem_octShape]; omega
    · intro y hy; simp only [mem_octShape] at hy; simp only [dot]; omega
    · simp only [mem_octShape]; omega
    · intro y hy; simp only [mem_octShape] at hy; simp only [dot]; omega
    · intro hh; rw [Prod.ext_iff] at hh; omega
  · refine ⟨(b - c, b), ⟨?_, ?_⟩, (-r, c - r), ⟨?_, ?_⟩, ?_⟩
    · simp only [mem_octShape]; omega
    · intro y hy; simp only [mem_octShape] at hy; simp only [dot]; omega
    · simp only [mem_octShape]; omega
    · intro y hy; simp only [mem_octShape] at hy; simp only [dot]; omega
    · intro hh; rw [Prod.ext_iff] at hh; omega
  · refine ⟨(-r, c - r), ⟨?_, ?_⟩, (-r, r - t), ⟨?_, ?_⟩, ?_⟩
    · simp only [mem_octShape]; omega
    · intro y hy; simp only [mem_octShape] at hy; simp only [dot]; omega
    · simp only [mem_octShape]; omega
    · intro y hy; simp only [mem_octShape] at hy; simp only [dot]; omega
    · intro hh; rw [Prod.ext_iff] at hh; omega
  · refine ⟨(-r, r - t), ⟨?_, ?_⟩, (e - t, -e), ⟨?_, ?_⟩, ?_⟩
    · simp only [mem_octShape]; omega
    · intro y hy; simp only [mem_octShape] at hy; simp only [dot]; omega
    · simp only [mem_octShape]; omega
    · intro y hy; simp only [mem_octShape] at hy; simp only [dot]; omega
    · intro hh; rw [Prod.ext_iff] at hh; omega
  · refine ⟨(e - t, -e), ⟨?_, ?_⟩, (d - e, -e), ⟨?_, ?_⟩, ?_⟩
    · simp only [mem_octShape]; omega
    · intro y hy; simp only [mem_octShape] at hy; simp only [dot]; omega
    · simp only [mem_octShape]; omega
    · intro y hy; simp only [mem_octShape] at hy; simp only [dot]; omega
    · intro hh; rw [Prod.ext_iff] at hh; omega
  · refine ⟨(d - e, -e), ⟨?_, ?_⟩, (a, a - d), ⟨?_, ?_⟩, ?_⟩
    · simp only [mem_octShape]; omega
    · intro y hy; simp only [mem_octShape] at hy; simp only [dot]; omega
    · simp only [mem_octShape]; omega
    · intro y hy; simp only [mem_octShape] at hy; simp only [dot]; omega
    · intro hh; rw [Prod.ext_iff] at hh; omega

/-- `octE` 之外的本原法向，面是单点：八个开锥，各由相邻两条约束钉住一个顶点
（`ShellSweep.face_subset_singleton_of_cone`）。 -/
theorem face_subsingleton_octShape {n : ℤ × ℤ} (hp : Prim n) (hn : n ∉ octE) :
    ∃ v, face (octShape a s b c r t e d) n ⊆ {v} := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  have hne : n.1 ≠ 0 ∧ n.2 ≠ 0 ∧ n.1 + n.2 ≠ 0 ∧ n.1 - n.2 ≠ 0 := by
    refine ⟨fun h0 => hn ?_, fun h0 => hn ?_, fun h0 => hn ?_, fun h0 => hn ?_⟩
    · rcases prim_eq_of_fst_eq_zero hp h0 with rfl | rfl <;> simp [octE]
    · rcases prim_eq_of_snd_eq_zero hp h0 with rfl | rfl <;> simp [octE]
    · rcases Nivat.ShellSweep.prim_eq_of_coord_eq_neg hp (by omega) with rfl | rfl <;>
        simp [octE]
    · rcases prim_eq_of_coord_eq hp (by omega) with rfl | rfl <;> simp [octE]
  obtain ⟨hp0, hq0, hpq0, hpq0'⟩ := hne
  have cR : ∀ z ∈ octShape a s b c r t e d, dot ((1 : ℤ), (0 : ℤ)) z ≤ a := by
    intro z hz; simp only [mem_octShape] at hz; simp only [dot]; omega
  have cS : ∀ z ∈ octShape a s b c r t e d, dot ((1 : ℤ), (1 : ℤ)) z ≤ s := by
    intro z hz; simp only [mem_octShape] at hz; simp only [dot]; omega
  have cT : ∀ z ∈ octShape a s b c r t e d, dot ((0 : ℤ), (1 : ℤ)) z ≤ b := by
    intro z hz; simp only [mem_octShape] at hz; simp only [dot]; omega
  have cUL : ∀ z ∈ octShape a s b c r t e d, dot ((-1 : ℤ), (1 : ℤ)) z ≤ c := by
    intro z hz; simp only [mem_octShape] at hz; simp only [dot]; omega
  have cL : ∀ z ∈ octShape a s b c r t e d, dot ((-1 : ℤ), (0 : ℤ)) z ≤ r := by
    intro z hz; simp only [mem_octShape] at hz; simp only [dot]; omega
  have cLL : ∀ z ∈ octShape a s b c r t e d, dot ((-1 : ℤ), (-1 : ℤ)) z ≤ t := by
    intro z hz; simp only [mem_octShape] at hz; simp only [dot]; omega
  have cB : ∀ z ∈ octShape a s b c r t e d, dot ((0 : ℤ), (-1 : ℤ)) z ≤ e := by
    intro z hz; simp only [mem_octShape] at hz; simp only [dot]; omega
  have cLR : ∀ z ∈ octShape a s b c r t e d, dot ((1 : ℤ), (-1 : ℤ)) z ≤ d := by
    intro z hz; simp only [mem_octShape] at hz; simp only [dot]; omega
  rcases lt_or_gt_of_ne hp0 with hp | hp <;> rcases lt_or_gt_of_ne hq0 with hq | hq
  · -- p < 0, q < 0: split on `p − q`
    rcases lt_or_gt_of_ne hpq0' with hpq | hpq
    · -- p < q < 0: between `(-1,0)` and `(-1,-1)`, vertex `(-r, r-t)`
      exact ⟨(-r, r - t), Nivat.ShellSweep.face_subset_singleton_of_cone (α := n.2 - n.1)
        (β := -n.2) (by omega) (by omega) (fun z => by simp only [dot]; ring) (by decide) cL cLL
        (by simp only [mem_octShape]; omega) (by simp [dot]) (by simp [dot])⟩
    · -- q < p < 0: between `(-1,-1)` and `(0,-1)`, vertex `(e-t, -e)`
      exact ⟨(e - t, -e), Nivat.ShellSweep.face_subset_singleton_of_cone (α := -n.1)
        (β := n.1 - n.2) (by omega) (by omega) (fun z => by simp only [dot]; ring) (by decide)
        cLL cB (by simp only [mem_octShape]; omega) (by simp [dot]) (by simp [dot])⟩
  · -- p < 0, q > 0: split on `p + q`
    rcases lt_or_gt_of_ne hpq0 with hpq | hpq
    · -- p + q < 0: between `(-1,1)` and `(-1,0)`, vertex `(-r, c-r)`
      exact ⟨(-r, c - r), Nivat.ShellSweep.face_subset_singleton_of_cone (α := n.2)
        (β := -n.1 - n.2) (by omega) (by omega) (fun z => by simp only [dot]; ring) (by decide)
        cUL cL (by simp only [mem_octShape]; omega) (by simp [dot]) (by simp [dot])⟩
    · -- p + q > 0: between `(0,1)` and `(-1,1)`, vertex `(b-c, b)`
      exact ⟨(b - c, b), Nivat.ShellSweep.face_subset_singleton_of_cone (α := n.1 + n.2)
        (β := -n.1) (by omega) (by omega) (fun z => by simp only [dot]; ring) (by decide)
        cT cUL (by simp only [mem_octShape]; omega) (by simp [dot]) (by simp [dot])⟩
  · -- p > 0, q < 0: split on `p + q`
    rcases lt_or_gt_of_ne hpq0 with hpq | hpq
    · -- p + q < 0: between `(0,-1)` and `(1,-1)`, vertex `(d-e, -e)`
      exact ⟨(d - e, -e), Nivat.ShellSweep.face_subset_singleton_of_cone (α := -n.1 - n.2)
        (β := n.1) (by omega) (by omega) (fun z => by simp only [dot]; ring) (by decide)
        cB cLR (by simp only [mem_octShape]; omega) (by simp [dot]) (by simp [dot])⟩
    · -- p + q > 0: between `(1,-1)` and `(1,0)`, vertex `(a, a-d)`
      exact ⟨(a, a - d), Nivat.ShellSweep.face_subset_singleton_of_cone (α := -n.2)
        (β := n.1 + n.2) (by omega) (by omega) (fun z => by simp only [dot]; ring) (by decide)
        cLR cR (by simp only [mem_octShape]; omega) (by simp [dot]) (by simp [dot])⟩
  · -- p > 0, q > 0: split on `p − q`
    rcases lt_or_gt_of_ne hpq0' with hpq | hpq
    · -- p < q: between `(1,1)` and `(0,1)`, vertex `(s-b, b)`
      exact ⟨(s - b, b), Nivat.ShellSweep.face_subset_singleton_of_cone (α := n.1)
        (β := n.2 - n.1) (by omega) (by omega) (fun z => by simp only [dot]; ring) (by decide)
        cS cT (by simp only [mem_octShape]; omega) (by simp [dot]) (by simp [dot])⟩
    · -- p > q: between `(1,0)` and `(1,1)`, vertex `(a, s-a)`
      exact ⟨(a, s - a), Nivat.ShellSweep.face_subset_singleton_of_cone (α := n.1 - n.2)
        (β := n.2) (by omega) (by omega) (fun z => by simp only [dot]; ring) (by decide)
        cR cS (by simp only [mem_octShape]; omega) (by simp [dot]) (by simp [dot])⟩

/-- **非退化八边形的边集恰是 `octE`。**  `ShellSweep.E_hexShape` 的八法向版本。 -/
theorem E_octShape : E (octShape a s b c r t e d) = octE := by
  ext n
  constructor
  · rintro ⟨hp, hnt⟩
    by_contra hn
    obtain ⟨v, hv⟩ := face_subsingleton_octShape h hp hn
    exact Set.not_nontrivial_singleton (hnt.mono hv)
  · intro hn
    have hprim : Prim n := by
      simp only [octE, Set.mem_insert_iff, Set.mem_singleton_iff] at hn
      rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    obtain ⟨z, hz, z', hz', hzz'⟩ := face_pair_octShape h n hn
    exact ⟨hprim, z, hz, z', hz', hzz'⟩

theorem two_le_encard_face_octShape (n : ℤ × ℤ) (hn : n ∈ octE) :
    2 ≤ (face (octShape a s b c r t e d) n).encard := by
  obtain ⟨z, hz, z', hz', hzz'⟩ := face_pair_octShape h n hn
  exact two_le_encard_of_pair hz hz' hzz'

end OctFaces

/-- 八个有理半平面的交，故格凸。 -/
theorem isLatticeConvexRegion_octShape (a s b c r t e d : ℤ) :
    IsLatticeConvexRegion (octShape a s b c r t e d) := by
  have heq : octShape a s b c r t e d =
      (((((((Set.univ ∩ halfPlaneLE ((1 : ℤ), (0 : ℤ)) a) ∩ halfPlaneLE ((1 : ℤ), (1 : ℤ)) s) ∩
        halfPlaneLE ((0 : ℤ), (1 : ℤ)) b) ∩ halfPlaneLE ((-1 : ℤ), (1 : ℤ)) c) ∩
        halfPlaneLE ((-1 : ℤ), (0 : ℤ)) r) ∩ halfPlaneLE ((-1 : ℤ), (-1 : ℤ)) t) ∩
        halfPlaneLE ((0 : ℤ), (-1 : ℤ)) e) ∩ halfPlaneLE ((1 : ℤ), (-1 : ℤ)) d := by
    ext z
    simp only [mem_octShape, Set.mem_inter_iff, Set.mem_univ, halfPlaneLE, Set.mem_ofPred_eq,
      dot, true_and]
    omega
  rw [heq]
  iterate 8 refine isLatticeConvexRegion_inter_halfPlaneLE _ _ ?_
  exact Nivat.Colle41.isLatticeConvexRegion_univ

theorem finite_octShape (a s b c r t e d : ℤ) : (octShape a s b c r t e d).Finite := by
  refine Set.Finite.subset ((Set.finite_Icc (-r) a).prod (Set.finite_Icc (-e) b)) ?_
  rintro z ⟨h1, -, h3, -, h5, -, h7, -⟩
  exact Set.mem_prod.mpr ⟨Set.mem_Icc.mpr ⟨by omega, h1⟩, Set.mem_Icc.mpr ⟨by omega, h3⟩⟩

/-- **非退化八边形被任何边集为 `octE`、每边至多两点的 `U` 包络。**
`ShellSweep.enveloped_hexShape` 的八法向版本。 -/
theorem enveloped_octShape {U : Set (ℤ × ℤ)} {a s b c r t e d : ℤ} (h : Nondeg8 a s b c r t e d)
    (hEU : E U = octE) (hU2 : ∀ n ∈ octE, (face U n).encard ≤ 2) :
    Enveloped U (octShape a s b c r t e d) := by
  refine ⟨⟨isLatticeConvexRegion_octShape a s b c r t e d, fun n hn => ?_⟩, ?_⟩
  · rw [E_octShape h] at hn
    exact ⟨by rw [hEU]; exact hn, le_trans (hU2 n hn) (two_le_encard_face_octShape h n hn)⟩
  · rw [E_octShape h, hEU]

/-- 单位八边形：顶点 `(1,0),(2,1),(2,2),(1,3),(0,3),(-1,2),(-1,1),(0,0)`，每边恰两个格点。
这是 Definition 3.2（`:402`）里 𝒰 = 𝒮_φ 的角色。 -/
def oct1 : Set (ℤ × ℤ) := octShape 2 4 3 3 1 0 0 1

theorem nondeg_oct1 : Nondeg8 2 4 3 3 1 0 0 1 :=
  ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num⟩

theorem E_oct1 : E oct1 = octE := E_octShape nondeg_oct1

theorem finite_oct1 : oct1.Finite := finite_octShape _ _ _ _ _ _ _ _

theorem posArea_oct1 : PosArea oct1 := by
  refine ⟨((0 : ℤ), (0 : ℤ)), by simp only [oct1, mem_octShape]; omega,
    ((1 : ℤ), (0 : ℤ)), by simp only [oct1, mem_octShape]; omega,
    ((2 : ℤ), (1 : ℤ)), by simp only [oct1, mem_octShape]; omega, ?_⟩
  simp [det]

/-- **单位八边形每条边恰两个格点。**  `ShellSweep.encard_face_hexA_le` 的八法向版本。 -/
theorem encard_face_oct1_le (n : ℤ × ℤ) (hn : n ∈ octE) : (face oct1 n).encard ≤ 2 := by
  have key : ∀ (v v' : ℤ × ℤ), face oct1 n ⊆ {v, v'} → (face oct1 n).encard ≤ 2 :=
    fun v v' h =>
      le_trans (Set.encard_mono h) (le_trans (Set.encard_insert_le _ _) (by norm_num))
  simp only [octE, Set.mem_insert_iff, Set.mem_singleton_iff] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine key (2, 1) (2, 2) fun z hz => ?_
    have := hz.2 (2, 2) (by simp only [oct1, mem_octShape]; omega)
    obtain ⟨hz1, -⟩ := hz
    obtain ⟨x, y⟩ := z
    simp only [oct1, mem_octShape] at hz1; simp only [dot] at this
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.ext_iff]; omega
  · refine key (2, 2) (1, 3) fun z hz => ?_
    have := hz.2 (2, 2) (by simp only [oct1, mem_octShape]; omega)
    obtain ⟨hz1, -⟩ := hz
    obtain ⟨x, y⟩ := z
    simp only [oct1, mem_octShape] at hz1; simp only [dot] at this
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.ext_iff]; omega
  · refine key (1, 3) (0, 3) fun z hz => ?_
    have := hz.2 (1, 3) (by simp only [oct1, mem_octShape]; omega)
    obtain ⟨hz1, -⟩ := hz
    obtain ⟨x, y⟩ := z
    simp only [oct1, mem_octShape] at hz1; simp only [dot] at this
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.ext_iff]; omega
  · refine key (0, 3) (-1, 2) fun z hz => ?_
    have := hz.2 (0, 3) (by simp only [oct1, mem_octShape]; omega)
    obtain ⟨hz1, -⟩ := hz
    obtain ⟨x, y⟩ := z
    simp only [oct1, mem_octShape] at hz1; simp only [dot] at this
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.ext_iff]; omega
  · refine key (-1, 2) (-1, 1) fun z hz => ?_
    have := hz.2 (-1, 2) (by simp only [oct1, mem_octShape]; omega)
    obtain ⟨hz1, -⟩ := hz
    obtain ⟨x, y⟩ := z
    simp only [oct1, mem_octShape] at hz1; simp only [dot] at this
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.ext_iff]; omega
  · refine key (-1, 1) (0, 0) fun z hz => ?_
    have := hz.2 (-1, 1) (by simp only [oct1, mem_octShape]; omega)
    obtain ⟨hz1, -⟩ := hz
    obtain ⟨x, y⟩ := z
    simp only [oct1, mem_octShape] at hz1; simp only [dot] at this
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.ext_iff]; omega
  · refine key (0, 0) (1, 0) fun z hz => ?_
    have := hz.2 (0, 0) (by simp only [oct1, mem_octShape]; omega)
    obtain ⟨hz1, -⟩ := hz
    obtain ⟨x, y⟩ := z
    simp only [oct1, mem_octShape] at hz1; simp only [dot] at this
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.ext_iff]; omega
  · refine key (1, 0) (2, 1) fun z hz => ?_
    have := hz.2 (1, 0) (by simp only [oct1, mem_octShape]; omega)
    obtain ⟨hz1, -⟩ := hz
    obtain ⟨x, y⟩ := z
    simp only [oct1, mem_octShape] at hz1; simp only [dot] at this
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.ext_iff]; omega

/-! ### §18.2 见证族

端点对齐坐标（`v⃗_ℓ = (1,0)`，`g₁ = (1,0)`，底边在 `y = 0`）下第 `i` 级是

    Â_i = octShape (1 + N) (1 + 2N + ℓ₂) B (2B) (B+1) B 0 1,   N = xN i, B = 10N + 3,

`ℓ₂ = oL i`（第一级 `5`，之后 `2`），`k_i = 10 N`。`A_i := Â_i + k_i (1,0)`。 -/

theorem xN_mono {i j : ℕ} (hij : i ≤ j) : xN i ≤ xN j := max_le_max hij le_rfl

theorem xN_of_le_one {i : ℕ} (hi : i ≤ 1) : xN i = 1 := by unfold xN; omega

/-- 左侧三个支撑值的公共尺度 `B_i = 10·xN i + 3`；每级长 `10`，恰好吸收 `k_{i+1} − k_i`。 -/
def oB (i : ℕ) : ℤ := 10 * (xN i : ℤ) + 3

/-- `(1,0)`-边的长度 `ℓ₂`：第一级 `5`，之后 `2`。**原文没有任何条款约束这个数**（`J = ι+1`
时 `:504` 空真）。 -/
def oL (i : ℕ) : ℤ := if i ≤ 1 then 5 else 2

/-- 第 `i` 级，端点对齐坐标。`(1,-1)`-边长 `xN i`，每步严格增长。 -/
def oA (i : ℕ) : Set (ℤ × ℤ) :=
  octShape (1 + (xN i : ℤ)) (1 + 2 * (xN i : ℤ) + oL i) (oB i) (2 * oB i) (oB i + 1) (oB i) 0 1

/-- `k_i = 10·xN i`。 -/
def oKK (i : ℕ) : ℕ := 10 * xN i

/-- 未对齐的族 `A_i = Â_i + k_i (1,0)`。 -/
def oAA : ℕ → Set (ℤ × ℤ) := fun n => Nivat.LE2.shift ((oKK n : ℤ) • ((1 : ℤ), (0 : ℤ))) (oA n)

theorem mem_oA (i : ℕ) (z : ℤ × ℤ) :
    z ∈ oA i ↔
      z.1 ≤ 1 + (xN i : ℤ) ∧ z.1 + z.2 ≤ 1 + 2 * (xN i : ℤ) + oL i ∧ z.2 ≤ oB i ∧
        -z.1 + z.2 ≤ 2 * oB i ∧ -z.1 ≤ oB i + 1 ∧ -z.1 - z.2 ≤ oB i ∧ -z.2 ≤ 0 ∧
        z.1 - z.2 ≤ 1 := Iff.rfl

theorem oL_cases (i : ℕ) : oL i = 5 ∨ oL i = 2 := by
  unfold oL; split_ifs <;> simp

/-- `ℓ₂` 的下降被 `k` 的增量盖住：`oL i ≤ oL j + 10 (xN j − xN i)`。这是 `:486` 在
`(1,1)` 法向上的全部要求。 -/
theorem oL_le {i j : ℕ} (hij : i ≤ j) :
    oL i ≤ oL j + 10 * ((xN j : ℤ) - (xN i : ℤ)) := by
  have hN := xN_mono hij
  by_cases hi : i ≤ 1 <;> by_cases hj : j ≤ 1
  · simp only [oL, hi, hj, if_true]; omega
  · rw [xN_of_le_one hi, xN_eq (by omega : 1 ≤ j)]
    simp only [oL, hi, hj, if_true, if_false]; omega
  · omega
  · simp only [oL, hi, hj, if_false]; omega

theorem oKK_cast (n : ℕ) : (oKK n : ℤ) = 10 * (xN n : ℤ) := by unfold oKK; push_cast; ring

theorem nondeg_oA (i : ℕ) :
    Nondeg8 (1 + (xN i : ℤ)) (1 + 2 * (xN i : ℤ) + oL i) (oB i) (2 * oB i) (oB i + 1) (oB i)
      0 1 := by
  have h1 := one_le_xN i
  rcases oL_cases i with h | h <;> unfold oB <;>
    exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

theorem enveloped_oA (i : ℕ) : Enveloped oct1 (oA i) :=
  enveloped_octShape (nondeg_oA i) E_oct1 encard_face_oct1_le

theorem finite_oA (i : ℕ) : (oA i).Finite := finite_octShape _ _ _ _ _ _ _ _

theorem g1_mem_oA (i : ℕ) : ((1 : ℤ), (0 : ℤ)) ∈ oA i := by
  have h1 := one_le_xN i
  rw [mem_oA]; simp only [oB]
  rcases oL_cases i with h | h <;> omega

theorem hhp_oA (i : ℕ) (z : ℤ × ℤ) (hz : z ∈ oA i) : 0 ≤ z.2 := by
  rw [mem_oA] at hz; omega

/-- `:486` 在对齐坐标下：`Â_i` 左移 `k_j − k_i = 10 (xN j − xN i)` 后落进 `Â_j`。 -/
theorem mono_oA_shift {i j : ℕ} (hij : i ≤ j) {z : ℤ × ℤ} (hz : z ∈ oA i) :
    (z.1 - 10 * ((xN j : ℤ) - (xN i : ℤ)), z.2) ∈ oA j := by
  have hN := xN_mono hij
  have hL := oL_le hij
  rw [mem_oA] at hz ⊢
  simp only [oB] at hz ⊢
  omega

theorem sub_smul_e1 (z : ℤ × ℤ) (s : ℤ) :
    z - s • ((1 : ℤ), (0 : ℤ)) = (z.1 - s, z.2) := by
  refine Prod.ext ?_ ?_ <;> simp

theorem hatOf_oAA (i : ℕ) : hatOf oAA oKK ((1 : ℤ), (0 : ℤ)) i = oA i :=
  hatOf_shift_smul oA oKK _ i

theorem enveloped_oAA (i : ℕ) : Enveloped oct1 (oAA i) :=
  Nivat.LE2.envOf_shift _ (enveloped_oA i)

theorem finite_oAA (i : ℕ) : (oAA i).Finite := finite_shift (finite_oA i)

theorem nonempty_oAA (i : ℕ) : (oAA i).Nonempty := by
  refine ⟨((1 : ℤ), (0 : ℤ)) + (oKK i : ℤ) • ((1 : ℤ), (0 : ℤ)), ?_⟩
  show ((1 : ℤ), (0 : ℤ)) + (oKK i : ℤ) • ((1 : ℤ), (0 : ℤ)) - (oKK i : ℤ) • ((1 : ℤ), (0 : ℤ))
    ∈ oA i
  rw [add_sub_cancel_right]
  exact g1_mem_oA i

theorem mono_oAA {i j : ℕ} (hij : i ≤ j) : oAA i ⊆ oAA j := by
  intro z hz
  change z - (oKK i : ℤ) • ((1 : ℤ), (0 : ℤ)) ∈ oA i at hz
  change z - (oKK j : ℤ) • ((1 : ℤ), (0 : ℤ)) ∈ oA j
  rw [sub_smul_e1] at hz ⊢
  have h := mono_oA_shift hij hz
  have e : z.1 - (oKK j : ℤ) = z.1 - (oKK i : ℤ) - 10 * ((xN j : ℤ) - (xN i : ℤ)) := by
    rw [oKK_cast, oKK_cast]; ring
  rw [e]
  exact h

/-- `:488`：`Â_i ∩ ℓ⁻` 的终点是 `g₁ = (1,0)`，对每个 `i`。 -/
theorem endpointAligned_oA (i : ℕ) :
    IsGreatest {t : ℤ | ((1 : ℤ), (0 : ℤ)) + t • ((1 : ℤ), (0 : ℤ)) ∈ oA i ∧
      dot ((0 : ℤ), (-1 : ℤ)) (((1 : ℤ), (0 : ℤ)) + t • ((1 : ℤ), (0 : ℤ))) = 0} 0 := by
  have h1 := one_le_xN i
  have hmem : ∀ t : ℤ, (((1 : ℤ), (0 : ℤ)) + t • ((1 : ℤ), (0 : ℤ)) ∈ oA i) ↔
      (-(oB i) - 1 ≤ t ∧ t ≤ 0) := by
    intro t
    rw [ce_shift, mem_oA]
    simp only [oB]
    rcases oL_cases i with hL | hL <;> constructor <;> intro hz <;> omega
  have hlev : ∀ t : ℤ,
      dot ((0 : ℤ), (-1 : ℤ)) (((1 : ℤ), (0 : ℤ)) + t • ((1 : ℤ), (0 : ℤ))) = 0 := by
    intro t; rw [ce_shift]; simp [dot]
  constructor
  · exact ⟨(hmem 0).mpr ⟨by unfold oB; omega, le_rfl⟩, hlev 0⟩
  · rintro t ⟨ht, -⟩
    exact ((hmem t).mp ht).2

/-- `(1,-1)`-边是 `{(y+1, y) : 0 ≤ y ≤ xN i}`。 -/
theorem face_oA_slant (i : ℕ) :
    face (oA i) ((1 : ℤ), (-1 : ℤ)) = (fun y : ℤ => (y + 1, y)) '' Set.Icc 0 (xN i : ℤ) := by
  have h1 := one_le_xN i
  have h10 := g1_mem_oA i
  ext z
  constructor
  · rintro ⟨hz, hmax⟩
    have hd := hmax _ h10
    rw [mem_oA] at hz
    simp only [oB] at hz
    simp only [dot] at hd
    refine ⟨z.2, ?_, ?_⟩
    · simp only [Set.mem_Icc]; omega
    · have hz1 : z.1 = z.2 + 1 := by omega
      show ((z.2 + 1, z.2) : ℤ × ℤ) = z
      rw [← hz1]
  · rintro ⟨y, hy, rfl⟩
    simp only [Set.mem_Icc] at hy
    refine ⟨?_, ?_⟩
    · rw [mem_oA]; simp only [oB]
      rcases oL_cases i with hL | hL <;> omega
    · intro w hw
      rw [mem_oA] at hw
      simp only [oB] at hw
      simp only [dot]
      omega

theorem encard_face_oA_slant (i : ℕ) :
    (face (oA i) ((1 : ℤ), (-1 : ℤ))).encard = ((xN i + 1 : ℕ) : ℕ∞) := by
  have hinj : Set.InjOn (fun y : ℤ => (y + 1, y)) (Set.Icc 0 (xN i : ℤ)) :=
    fun x _ y _ hxy => by simpa using congrArg Prod.snd hxy
  rw [face_oA_slant, hinj.encard_image, ← Finset.coe_Icc, Set.encard_coe_eq_coe_finsetCard,
    Int.card_Icc]
  congr 1

theorem xN_one : xN 1 = 1 := xN_eq le_rfl

theorem xN_two : xN 2 = 2 := xN_eq (by norm_num)

theorem mem_oA_one : ((2 : ℤ), (6 : ℤ)) ∈ oA 1 := by
  rw [mem_oA]; simp only [oB, xN_one]; norm_num [oL]

theorem not_mem_oA_two : ((2 : ℤ), (6 : ℤ)) ∉ oA 2 := by
  rw [mem_oA]; simp only [oB, xN_two]; norm_num [oL]

/-- **八边形扇上，本文件这条路线的前提表不蕴含 `AhatMono`。**

原文对应（逐合取）：
* `U.Finite`、`PosArea U`、`E U = octE` ↔ Definition 3.2 的 𝒰（`:402`）取单位八边形——
  `hES : E U = hexE` 的八法向替身；
* `Enveloped U (A i)` ↔ `:484` "`E(𝒮_φ)`-enveloped"；`IsMaxEnvIn (EnvOf U) (A i) (A i)` ↔
  `:484` 的极大性，**但约束集是 `A i` 自身而非 `canonA …`**（同 `not_ahatMono_of_enveloped`）；
* `hfin`/`hne`/`hmono`/`hkk` ↔ `exists_endpoint_shift` 的前提与 `:486`；
* `hhp` ↔ `:494`（`Â_i ⊂ H_{B_i}(ℓ) − k_i v⃗_ℓ`）；`halign` ↔ `:488`；
* 严格增长 ↔ `:500` **字面**（`|Â_i ∩ w_i(J)| < |Â_{i+1} ∩ w_{i+1}(J)|` 对所有 `i ≥ 1`，
  `J = ι+1`，即 `(1,-1)`-边；`:504` 的范围 `ι+1 ≤ j ≤ J−1` 为空）；
* `≤` 版 ↔ `ahatMono_ofParts_of_maxA_of_aligned` 的 `hext`，逐字；
* 结论的否定 ↔ `:508` 图 6 说明的 `Â_1 ⊂ Â_2`，在 `(2,6)` 处失败。

**未兑现的 binder（具名）**：`maxA` 的约束集 `canonA η xper vl B u i`（需要 `η`、`x_per`、
`B`、`u`；§8 的手法可兑现，本轮未做）；`ItemII` / `Exhausts` / shell / fill 等 `ofParts`
其余字段；`x_per ∈ X_η`。这条证伪的是 **`hES` 换成八法向后的路线**，不是 Collé 的论证。 -/
theorem not_ahatMono_octagon :
    ∃ (U : Set (ℤ × ℤ)) (A : ℕ → Set (ℤ × ℤ)) (kk : ℕ → ℕ),
      U.Finite ∧ PosArea U ∧ E U = octE ∧
      (∀ i, Enveloped U (A i)) ∧
      (∀ i, IsMaxEnvIn (EnvOf U) (A i) (A i)) ∧
      (∀ i, (A i).Finite) ∧ (∀ i, (A i).Nonempty) ∧
      (∀ i j, i ≤ j → A i ⊆ A j) ∧
      (∀ i j, i ≤ j → kk i ≤ kk j) ∧
      (∀ i, ∀ z ∈ hatOf A kk ((1 : ℤ), (0 : ℤ)) i, 0 ≤ z.2) ∧
      (∀ i, IsGreatest {t : ℤ |
          ((1 : ℤ), (0 : ℤ)) + t • ((1 : ℤ), (0 : ℤ)) ∈ hatOf A kk ((1 : ℤ), (0 : ℤ)) i
            ∧ dot ((0 : ℤ), (-1 : ℤ))
                (((1 : ℤ), (0 : ℤ)) + t • ((1 : ℤ), (0 : ℤ))) = 0} 0) ∧
      (∀ i, 1 ≤ i →
        (face (hatOf A kk ((1 : ℤ), (0 : ℤ)) i) ((1 : ℤ), (-1 : ℤ))).encard
          < (face (hatOf A kk ((1 : ℤ), (0 : ℤ)) (i + 1)) ((1 : ℤ), (-1 : ℤ))).encard) ∧
      (∀ i j, i ≤ j →
        (face (hatOf A kk ((1 : ℤ), (0 : ℤ)) i) ((1 : ℤ), (-1 : ℤ))).encard
          ≤ (face (hatOf A kk ((1 : ℤ), (0 : ℤ)) j) ((1 : ℤ), (-1 : ℤ))).encard) ∧
      ¬ (∀ i j, i ≤ j →
          hatOf A kk ((1 : ℤ), (0 : ℤ)) i ⊆ hatOf A kk ((1 : ℤ), (0 : ℤ)) j) := by
  refine ⟨oct1, oAA, oKK, finite_oct1, posArea_oct1, E_oct1, enveloped_oAA, ?_, finite_oAA,
    nonempty_oAA, fun i j hij => mono_oAA hij, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- maximal in its own constraint set
  · exact fun i => ⟨enveloped_oAA i, subset_rfl, fun _ _ _ hTA => hTA⟩
  -- `k` monotone
  · intro i j hij
    exact Nat.mul_le_mul_left _ (xN_mono hij)
  -- `hhp`
  · intro i z hz
    rw [hatOf_oAA] at hz
    exact hhp_oA i z hz
  -- `halign`
  · intro i
    simp only [hatOf_oAA]
    exact endpointAligned_oA i
  -- `:500`, strict
  · intro i hi
    rw [hatOf_oAA, hatOf_oAA, encard_face_oA_slant, encard_face_oA_slant, xN_eq hi,
      xN_eq (by omega : 1 ≤ i + 1)]
    exact_mod_cast (by omega : i + 1 < i + 1 + 1)
  -- `hext`, the `≤` form
  · intro i j hij
    rw [hatOf_oAA, hatOf_oAA, encard_face_oA_slant, encard_face_oA_slant]
    have := xN_mono hij
    exact_mod_cast (by omega : xN i + 1 ≤ xN j + 1)
  -- `AhatMono` fails at `(2,6)`
  · intro h
    have h1 : ((2 : ℤ), (6 : ℤ)) ∈ hatOf oAA oKK ((1 : ℤ), (0 : ℤ)) 1 := by
      rw [hatOf_oAA]; exact mem_oA_one
    have h2 := h 1 2 (by norm_num) h1
    rw [hatOf_oAA] at h2
    exact not_mem_oA_two h2

/-! ## 19. The generic form at the shape the chain consumes

The consumer is `Nivat.ChainAsm.Aparts.ahatMono_field_of_extraction` (`ChainPartsFeed.lean:292`),
which today routes through `ahatMono_ofParts_of_extraction` and so carries `hES` (the hexagonal
normalisation §18 shows is load-bearing).  This section exposes the `←` direction of
`ahatMono_iff_fwd_suppVal_enveloped` (§17) with **every** side condition either derived or
named, so the chain can call it with `U := ↑𝒮_φ` and its own `vl`.

Side-condition ledger (each one: what it is, where it comes from on the chain):

* `henv : ∀ i, Enveloped U (A i)` — `:484` (`A_i` is `E(𝒮_φ)`-enveloped); on the chain it is the
  first conjunct of `ChainDataGeomParts.maxA` (`ChainPartsFeed.lean:295`), since
  `EnvOf U T` is `Enveloped U T` by `Iff.rfl` (`LatticeEdges.lean:2433`).
* `hfin : ∀ i, (A i).Finite` — free from `ChainDataGeomParts.hfin` (`:305`, the `hatOf` form)
  by `finite_of_hatOf_finite` below, or from `hfin_from_subAB` (`ChainPartsFeed.lean:260`).
* `hmono : ∀ i j, i ≤ j → A i ⊆ A j` — `:486` (`A₁ ⊂ A₂ ⊂ ⋯`); free via
  `A_mono_of_subBA_subAB` (`ChainPartsFeed.lean`，⚠ 第 201 轮删号留名：原记 `:445`，实测
  声明头在 `:310`).  ⚠ It **cannot** be dropped: the proof
  uses it on every normal with `⟪n, v⃗_ℓ⟫ ≤ 0`, where `hsupp` says nothing
  (`ahatMono_of_suppVal_slack`, `:513`).  Kernel fact: `not_ahatMono_of_fwd_suppVal_without_mono`
  below — with `kk ≡ 0` and `A i` a translate of `A 0` in the `+v⃗_ℓ` direction, every other
  hypothesis holds and the conclusion fails — so the brief's signature without `hmono` is false,
  and `hmono` is kept.
* `hkk : ∀ i j, i ≤ j → kk i ≤ kk j` — `:488` (`k_i`); `kk_le_of_endpointAligned` (`:105`).
* `hUfin : U.Finite` — `:402` ("finite"); free, `U = ↑S` with `S : Finset`.
* `hUarea : PosArea U` — `:402` ("`conv(𝒰)` has positive area").  🔴 **No on-chain producer
  for `U = ↑𝒮_φ`** (grep `PosArea (↑` over `Nivat/External/Colle`: only the concrete windows
  `Sap`/`Shex`/`sliver`).  It is what supplies `PosArea (A i)` (via `posArea_of_enveloped`) and
  `(A i).Nonempty`, both of which `mem_of_dot_le_suppVal` (`LatticeEdges.lean:1393`) needs;
  §17's `eq_hrep_of_enveloped` needs the same.  This is a genuine hypothesis of Definition 3.2,
  not ours — but it is **owed** on the chain.
* `(E U).Finite`, `IsLatticeConvexRegion (A i)`, `PosArea (A i)`, `(A i).Nonempty` — all
  **derived** below, no binder.
* `hsupp` — the residual (`:500`/`:504` on the forward normals); `ahatMono_iff_fwd_suppVal_enveloped`
  shows it is exactly `AhatMono`, not merely sufficient. -/

/-- `(A i).Finite` from the chain's `hfin` shape `(hatOf A kk vl i).Finite`
(`ChainDataGeomParts.hfin`, `ChainPartsFeed.lean:305`). -/
theorem finite_of_hatOf_finite {A : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ} {vl : ℤ × ℤ} {i : ℕ}
    (h : (hatOf A kk vl i).Finite) : (A i).Finite := by
  refine (h.image (fun z => z + (kk i : ℤ) • vl)).subset ?_
  intro a ha
  refine ⟨a - (kk i : ℤ) • vl, ?_, sub_add_cancel _ _⟩
  show a - (kk i : ℤ) • vl + (kk i : ℤ) • vl ∈ A i
  rwa [sub_add_cancel]

/-- **Positive area transfers along envelopedness.**  原文：`b3_colle2.txt:402`
（Definition 3.2 的前提「`conv(𝒰)` has positive area」）+ `E(𝒯) = E(𝒰)`.
Two non-parallel edges of `U` (`exists_mem_E_dot_ne_zero` twice) are edges of `T`
(`Enveloped.E_eq`), and two non-parallel edges force positive area (`posArea_of_edges`). -/
theorem posArea_of_enveloped {U T : Set (ℤ × ℤ)} (hUfin : U.Finite) (hUarea : PosArea U)
    (henv : Enveloped U T) : PosArea T := by
  have hUne : U.Nonempty := by obtain ⟨p, hp, -⟩ := hUarea; exact ⟨p, hp⟩
  have hEU : (E U).Finite := finite_E_of_finite hUfin
  obtain ⟨n₁, hn₁, -⟩ :=
    exists_mem_E_dot_ne_zero hUfin hUne hUarea (w := ((1 : ℤ), (0 : ℤ))) (by simp [Prod.ext_iff])
  have hn₁0 : n₁ ≠ 0 := hn₁.1.ne_zero
  have hperp0 : (-n₁.2, n₁.1) ≠ (0 : ℤ × ℤ) := by
    intro h
    apply hn₁0
    have h1 : n₁.1 = 0 := congrArg Prod.snd h
    have h2 : -n₁.2 = 0 := congrArg Prod.fst h
    exact Prod.ext h1 (neg_eq_zero.mp h2)
  obtain ⟨n₂, hn₂, hd⟩ := exists_mem_E_dot_ne_zero hUfin hUne hUarea hperp0
  have hE : E T = E U := Enveloped.E_eq hEU henv
  refine posArea_of_edges (hE ▸ hn₁) (hE ▸ hn₂) ?_ ?_
  · rintro rfl
    apply hd
    simp only [dot]; ring
  · rintro rfl
    apply hd
    simp only [dot, Prod.fst_neg, Prod.snd_neg]; ring

/-- **`AhatMono` from the forward-normal support inequality, chain shape.**
原文：`b3_colle2.txt:484`（`henv`）、`:486`（`hmono`）、`:488`（`hkk`）、`:402`（`hUfin`、`hUarea`）；
`hsupp` 是 `:500`/`:504` 在 `⟪n, v⃗_ℓ⟫ > 0` 的法向上的支撑形式（无原文对应物，是残余义务，
`ahatMono_iff_fwd_suppVal_enveloped` 证明它恰好等价于结论）。任意 `vl`、任意有限扇 —— 不含 `hES`。
Side-condition ledger in the section header; `hUarea` is the one binder with no on-chain producer. -/
theorem ahatMono_of_fwd_suppVal {U : Set (ℤ × ℤ)} {A : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ}
    {vl : ℤ × ℤ}
    (hUfin : U.Finite) (hUarea : PosArea U)
    (henv : ∀ i, Enveloped U (A i))
    (hfin : ∀ i, (A i).Finite)
    (hmono : ∀ i j, i ≤ j → A i ⊆ A j)
    (hkk : ∀ i j, i ≤ j → kk i ≤ kk j)
    (hsupp : ∀ i j, i ≤ j → ∀ n ∈ E U, 0 < dot n vl →
      suppVal (A i) n + ((kk j : ℤ) - (kk i : ℤ)) * dot n vl ≤ suppVal (A j) n) :
    ∀ i j, i ≤ j → hatOf A kk vl i ⊆ hatOf A kk vl j := by
  have harea : ∀ i, PosArea (A i) := fun i => posArea_of_enveloped hUfin hUarea (henv i)
  have hne : ∀ i, (A i).Nonempty := fun i => by
    obtain ⟨p, hp, -⟩ := harea i; exact ⟨p, hp⟩
  exact ahatMono_of_suppVal_slack_enveloped (finite_E_of_finite hUfin) henv hfin hne harea
    (fun i => (henv i).1.1) hmono hkk hsupp

/-- The same with `U := ↑S` for a `Finset`, which is the chain's `𝒮_φ`
(`ChainDataGeomParts` pins `Env` to `EnvOf (↑S : Set (ℤ × ℤ))`, `ChainPartsFeed.lean:272`),
`henv` in the `EnvOf` spelling of `maxA`'s first conjunct, and `hfin` in the `hatOf` shape of
`ChainDataGeomParts.hfin`.  Only `hUarea : PosArea ↑S` is not free. -/
theorem ahatMono_of_fwd_suppVal_finset {S : Finset (ℤ × ℤ)} {A : ℕ → Set (ℤ × ℤ)}
    {kk : ℕ → ℕ} {vl : ℤ × ℤ}
    (hUarea : PosArea (↑S : Set (ℤ × ℤ)))
    (henv : ∀ i, EnvOf (↑S : Set (ℤ × ℤ)) (A i))
    (hfin : ∀ i, (hatOf A kk vl i).Finite)
    (hmono : ∀ i j, i ≤ j → A i ⊆ A j)
    (hkk : ∀ i j, i ≤ j → kk i ≤ kk j)
    (hsupp : ∀ i j, i ≤ j → ∀ n ∈ E (↑S : Set (ℤ × ℤ)), 0 < dot n vl →
      suppVal (A i) n + ((kk j : ℤ) - (kk i : ℤ)) * dot n vl ≤ suppVal (A j) n) :
    ∀ i j, i ≤ j → hatOf A kk vl i ⊆ hatOf A kk vl j :=
  ahatMono_of_fwd_suppVal S.finite_toSet hUarea henv (fun i => finite_of_hatOf_finite (hfin i))
    hmono hkk hsupp

/-- **`hmono` cannot be dropped from `ahatMono_of_fwd_suppVal`** (the brief's signature omitted
it).  Witness: `U = oct1`, `A i = oA 0 + (i, 0)` (translates of one octagon in the `+v⃗_ℓ`
direction), `kk ≡ 0`, `vl = (1,0)`.  Every other hypothesis of `ahatMono_of_fwd_suppVal` holds —
`hsupp` because translating in the `+v⃗_ℓ` direction only raises the forward supports — and the
conclusion fails at `(-14, 1) ∈ Â₀ \ Â₁`.  This is not a statement about Collé: `:486`
(`A₁ ⊂ A₂ ⊂ ⋯`) is exactly the dropped hypothesis, and on the chain it is free
(`A_mono_of_subBA_subAB`, `ChainPartsFeed.lean`，⚠ 第 201 轮删号留名：原记 `:445`，
实测在 `:310`). -/
theorem not_ahatMono_of_fwd_suppVal_without_mono :
    ∃ (U : Set (ℤ × ℤ)) (A : ℕ → Set (ℤ × ℤ)) (kk : ℕ → ℕ) (vl : ℤ × ℤ),
      U.Finite ∧ PosArea U ∧ (∀ i, Enveloped U (A i)) ∧ (∀ i, (A i).Finite) ∧
      (∀ i j, i ≤ j → kk i ≤ kk j) ∧
      (∀ i j, i ≤ j → ∀ n ∈ E U, 0 < dot n vl →
        suppVal (A i) n + ((kk j : ℤ) - (kk i : ℤ)) * dot n vl ≤ suppVal (A j) n) ∧
      ¬ (∀ i j, i ≤ j → hatOf A kk vl i ⊆ hatOf A kk vl j) := by
  refine ⟨oct1, fun i => Nivat.LE2.shift ((i : ℤ) • ((1 : ℤ), (0 : ℤ))) (oA 0), fun _ => 0,
    ((1 : ℤ), (0 : ℤ)), finite_oct1, posArea_oct1, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact Nivat.LE2.envOf_shift _ (enveloped_oA 0)
  · intro i
    exact finite_shift (finite_oA 0)
  · intro i j _
    exact le_rfl
  · intro i j hij n _ hn
    have hne0 : (oA 0).Nonempty := ⟨_, g1_mem_oA 0⟩
    show suppVal (Nivat.LE2.shift ((i : ℤ) • ((1 : ℤ), (0 : ℤ))) (oA 0)) n
        + (((0 : ℕ) : ℤ) - ((0 : ℕ) : ℤ)) * dot n ((1 : ℤ), (0 : ℤ))
        ≤ suppVal (Nivat.LE2.shift ((j : ℤ) • ((1 : ℤ), (0 : ℤ))) (oA 0)) n
    rw [Nivat.LE2.suppVal_shift (finite_oA 0) hne0, Nivat.LE2.suppVal_shift (finite_oA 0) hne0,
      dot_smul_right, dot_smul_right]
    have hij' : (i : ℤ) ≤ (j : ℤ) := by exact_mod_cast hij
    nlinarith
  · intro h
    have h1 : ((-14 : ℤ), (1 : ℤ)) ∈ hatOf (fun i => Nivat.LE2.shift ((i : ℤ) • ((1 : ℤ), (0 : ℤ)))
        (oA 0)) (fun _ => 0) ((1 : ℤ), (0 : ℤ)) 0 := by
      show ((-14 : ℤ), (1 : ℤ)) + (((0 : ℕ) : ℤ)) • ((1 : ℤ), (0 : ℤ))
        - ((0 : ℕ) : ℤ) • ((1 : ℤ), (0 : ℤ)) ∈ oA 0
      rw [mem_oA]
      simp [oB, oL, xN]
    have h2 := h 0 1 (by norm_num) h1
    have h3 : ((-14 : ℤ), (1 : ℤ)) + (((0 : ℕ) : ℤ)) • ((1 : ℤ), (0 : ℤ))
        - ((1 : ℕ) : ℤ) • ((1 : ℤ), (0 : ℤ)) ∈ oA 0 := h2
    rw [mem_oA] at h3
    simp [oB, xN] at h3

/-! ## 20. `PosArea (↑𝒮_φ)`, the one debt of §19

`ahatMono_of_fwd_suppVal` (`:3048`) needs `PosArea U`; on the chain `U = ↑d.Sphi`.
No new imports: `ANormal` and `FaceDistinct` are already in this file's import closure
(via `ItemIIRec`), so nothing downstream of `AhatMono` sees a new module. -/

/-- **`𝒮_φ` has positive area** whenever the decomposition has at least two components.

原文：`b3_colle2.txt:424` — the standing hypothesis of the whole `𝒮_φ`/`ℓ_1…ℓ_{2m}` setup is
"`h_1,…,h_m ∈ ℤ²`, **with `m ≥ 2`**, are vectors in pairwise distinct directions".  So `m ≥ 2`
is Collé's, not ours.  **Answer to the question asked**: yes, and `m = 1` is disposed of
separately, at `:379` — "If `m = 1` there is nothing to argue.  Thus we may consider `m ≥ 2`"
(inside the proof of Lemma 2.7, the `ℓ ∈ nexpd(η)` reduction).  The decomposition order is also
`m ≥ 2` by hypothesis at `:176` (Theorem 1.15) and `:230`.  **Reading, not a kernel fact**: for
`m = 1` the conclusion below would be false, `𝒮_φ` being the segment `{0, h_1}` — but that case
is not expressible here, `DecompData` having no `m = 1` inhabitant (see `hm` below), so the
remark is about the source, not about this statement.

`hm` is a binder here as instructed, but on the chain it is **free**: `DecompData` already
carries the field `hm : 2 ≤ m` (`DecompData.lean:88`, docstring "At least 2 components (needed
for the argument)"), which is what `DecompData.exists_index_det_ne_zero` (`ANormal.lean:117`)
already spends.  `posArea_Sphi` below is the unconditional form.

Proof: `h_dir` (`DecompData.lean:104`) makes `h 0` and `h 1` non-parallel; take the primitive
normal of each (`exists_prim_dot_zero_dot_ne_zero`, `ANormal.lean:125`), which lands in
`E ↑d.Sphi` by `DecompData.mem_E_Sphi_of_dot_eq_zero` (`FaceDistinct.lean:146`); the two normals
are neither equal nor antipodal because each is non-orthogonal to the other's generator, so
`posArea_of_edges` (`LatticeEdges.lean:1718`) applies. -/
theorem posArea_Sphi_of_two_le_m {α : Type*} [AddCommMonoid α] {η : Config α}
    (d : DecompData η) (hm : 2 ≤ d.m) : PosArea (↑d.Sphi : Set (ℤ × ℤ)) := by
  have hne01 : (⟨0, by omega⟩ : Fin d.m) ≠ (⟨1, by omega⟩ : Fin d.m) := by
    simp [Fin.ext_iff]
  -- `n₁ ⟂ h 0`, transverse to `h 1`
  obtain ⟨n₁, hp₁, hd₁, hne₁⟩ :=
    exists_prim_dot_zero_dot_ne_zero (d.h_ne ⟨0, by omega⟩)
      (d.h_dir _ _ hne01.symm)
  -- `n₂ ⟂ h 1`, transverse to `h 0`
  obtain ⟨n₂, hp₂, hd₂, hne₂⟩ :=
    exists_prim_dot_zero_dot_ne_zero (d.h_ne ⟨1, by omega⟩)
      (d.h_dir _ _ hne01)
  have hm₁ : n₁ ∈ E (↑d.Sphi : Set (ℤ × ℤ)) :=
    d.mem_E_Sphi_of_dot_eq_zero (prim_iff_primitive.mpr hp₁) _ hd₁
  have hm₂ : n₂ ∈ E (↑d.Sphi : Set (ℤ × ℤ)) :=
    d.mem_E_Sphi_of_dot_eq_zero (prim_iff_primitive.mpr hp₂) _ hd₂
  refine posArea_of_edges hm₁ hm₂ ?_ ?_
  · rintro rfl; exact hne₁ hd₂
  · rintro rfl
    exact hne₁ (by rw [dot_neg_left] at hd₂; omega)

/-- The unconditional form: `DecompData.hm` (`DecompData.lean:88`) discharges the binder. -/
theorem posArea_Sphi {α : Type*} [AddCommMonoid α] {η : Config α} (d : DecompData η) :
    PosArea (↑d.Sphi : Set (ℤ × ℤ)) :=
  posArea_Sphi_of_two_le_m d d.hm

/-- **§19 at the chain's `U = ↑𝒮_φ`, with no `PosArea` binder left.**  This is the form the
`EnvOf (↑d.Sphi) ·` consumers want: every side condition of `ahatMono_of_fwd_suppVal` is now
either free from `DecompData` or a fact about the chain (`:484`/`:486`/`:488`), and `hsupp`
is the sole residual. -/
theorem ahatMono_of_fwd_suppVal_Sphi {α : Type*} [AddCommMonoid α] {η : Config α}
    (d : DecompData η) {A : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ} {vl : ℤ × ℤ}
    (henv : ∀ i, EnvOf (↑d.Sphi : Set (ℤ × ℤ)) (A i))
    (hfin : ∀ i, (hatOf A kk vl i).Finite)
    (hmono : ∀ i j, i ≤ j → A i ⊆ A j)
    (hkk : ∀ i j, i ≤ j → kk i ≤ kk j)
    (hsupp : ∀ i j, i ≤ j → ∀ n ∈ E (↑d.Sphi : Set (ℤ × ℤ)), 0 < dot n vl →
      suppVal (A i) n + ((kk j : ℤ) - (kk i : ℤ)) * dot n vl ≤ suppVal (A j) n) :
    ∀ i j, i ≤ j → hatOf A kk vl i ⊆ hatOf A kk vl j :=
  ahatMono_of_fwd_suppVal_finset (posArea_Sphi d) henv hfin hmono hkk hsupp

end Nivat.AhatMono

#print axioms Nivat.AhatMono.kk_le_of_endpointAligned
#print axioms Nivat.AhatMono.ahatMono_iff_fwdAbsorb
#print axioms Nivat.AhatMono.mem_ceA
#print axioms Nivat.AhatMono.ce_shift
#print axioms Nivat.AhatMono.ceKK_le
#print axioms Nivat.AhatMono.not_ahatMono_dropping_envelopedness
#print axioms Nivat.AhatMono.not_finite_of_rayClosedNeg
#print axioms Nivat.AhatMono.finite_hexShape
#print axioms Nivat.AhatMono.finite_hexA
#print axioms Nivat.AhatMono.posArea_hexA
#print axioms Nivat.AhatMono.nondeg_eA1
#print axioms Nivat.AhatMono.nondeg_eA2
#print axioms Nivat.AhatMono.enveloped_eA
#print axioms Nivat.AhatMono.mem_eA
#print axioms Nivat.AhatMono.eKK_cast
#print axioms Nivat.AhatMono.not_ahatMono_of_enveloped
#print axioms Nivat.AhatMono.ahatMono_of_suppVal_slack
#print axioms Nivat.AhatMono.ahatMono_of_suppVal_slack_enveloped
#print axioms Nivat.AhatMono.suppVal_eA_one_zero
#print axioms Nivat.AhatMono.suppVal_slack_fails_at_enveloped
#print axioms Nivat.AhatMono.eEta_true_iff
#print axioms Nivat.AhatMono.eU_sub_snd
#print axioms Nivat.AhatMono.finite_eA
#print axioms Nivat.AhatMono.mono_eA
#print axioms Nivat.AhatMono.meets_line_eA
#print axioms Nivat.AhatMono.endpointAligned_eA
#print axioms Nivat.AhatMono.not_ahatMono_eA
#print axioms Nivat.AhatMono.canonA_eq
#print axioms Nivat.AhatMono.isMaxEnvIn_canonA_eA
#print axioms Nivat.AhatMono.not_ahatMono_of_ofParts_chain_binders
#print axioms Nivat.AhatMono.one_le_xN
#print axioms Nivat.AhatMono.xN_le_xRx
#print axioms Nivat.AhatMono.mem_xA
#print axioms Nivat.AhatMono.nondeg_xA
#print axioms Nivat.AhatMono.enveloped_xA
#print axioms Nivat.AhatMono.finite_xA
#print axioms Nivat.AhatMono.mono_xA
#print axioms Nivat.AhatMono.itemII_xA
#print axioms Nivat.AhatMono.exhausts_xA
#print axioms Nivat.AhatMono.meets_line_xA
#print axioms Nivat.AhatMono.endpointAligned_xA
#print axioms Nivat.AhatMono.not_ahatMono_xA
#print axioms Nivat.AhatMono.xU_sep
#print axioms Nivat.AhatMono.canonA_eq_xA
#print axioms Nivat.AhatMono.isMaxEnvIn_canonA_xA
#print axioms Nivat.AhatMono.not_ahatMono_of_exhausting_chain
#print axioms Nivat.AhatMono.mem_blk
#print axioms Nivat.AhatMono.blk_sep
#print axioms Nivat.AhatMono.yEta_true_iff
#print axioms Nivat.AhatMono.xXper_mem_orbitClosure_yEta
#print axioms Nivat.AhatMono.canonA_eq_yA
#print axioms Nivat.AhatMono.isMaxEnvIn_canonA_yA
#print axioms Nivat.AhatMono.not_ahatMono_of_ofParts_chain_binders_with_xper
#print axioms Nivat.AhatMono.ahatMono_shift4_xA
#print axioms Nivat.AhatMono.dot_vl_pos_hexE
#print axioms Nivat.AhatMono.ahatMono_of_slantPinned
#print axioms Nivat.AhatMono.mem_hatShape
#print axioms Nivat.AhatMono.hatShape_eq_shift
#print axioms Nivat.AhatMono.enveloped_hatShape
#print axioms Nivat.AhatMono.face_hatShape_slant
#print axioms Nivat.AhatMono.encard_face_hatShape_slant
#print axioms Nivat.AhatMono.le_of_encard_face_slant_le
#print axioms Nivat.AhatMono.hatShape_subset_of_extraction
#print axioms Nivat.AhatMono.suppVal_hatShape_slant
#print axioms Nivat.AhatMono.suppVal_hatShape_right
#print axioms Nivat.AhatMono.hatOf_shift_smul
#print axioms Nivat.AhatMono.encard_face_slant_eq_suppVal_right
#print axioms Nivat.AhatMono.ahatMono_of_extraction
#print axioms Nivat.AhatMono.encard_face_slant_le_iff
#print axioms Nivat.AhatMono.le_apply_of_strictMono
#print axioms Nivat.AhatMono.eq_id_of_strictMono_of_surjective
#print axioms Nivat.AhatMono.iUnion_reindex_of_mono
#print axioms Nivat.AhatMono.iUnion_reindex_of_strictMono
#print axioms Nivat.AhatMono.hatOf_eq_shift_neg
#print axioms Nivat.AhatMono.dot_smul_right
#print axioms Nivat.AhatMono.suppVal_hatOf
#print axioms Nivat.AhatMono.suppVal_hatOf_mono_of_nonpos
#print axioms Nivat.AhatMono.suppVal_hatShape_top
#print axioms Nivat.AhatMono.suppVal_hatShape_left
#print axioms Nivat.AhatMono.suppVal_hatShape_ul
#print axioms Nivat.AhatMono.ahatMono_ofParts_of_extraction
#print axioms Nivat.AhatMono.hatOf_shift_smul
#print axioms Nivat.AhatMono.finite_shift
#print axioms Nivat.AhatMono.exists_pair_dot_eq_suppVal
#print axioms Nivat.AhatMono.eq_hatShape_of_enveloped
#print axioms Nivat.AhatMono.hshape_of_enveloped
#print axioms Nivat.AhatMono.suppVal_hatShape_bot
#print axioms Nivat.AhatMono.eq_shift_hatOf
#print axioms Nivat.AhatMono.finite_of_finite_hatOf
#print axioms Nivat.AhatMono.nonempty_of_nonempty_hatOf
#print axioms Nivat.AhatMono.finite_hexE
#print axioms Nivat.AhatMono.eq_hatShape_of_E_eq_hexE
#print axioms Nivat.AhatMono.hshape_of_E_eq_hexE
#print axioms Nivat.AhatMono.ahatMono_ofParts_of_extraction_of_E
#print axioms Nivat.AhatMono.enveloped_of_isMaxEnvIn
#print axioms Nivat.AhatMono.enveloped_of_isMaxEnvIn_of_eq
#print axioms Nivat.AhatMono.ahatMono_ofParts_of_maxA
#print axioms Nivat.AhatMono.suppVal_le_of_forall
#print axioms Nivat.AhatMono.suppVal_bot_of_halfPlane
#print axioms Nivat.AhatMono.suppVal_slant_of_align
#print axioms Nivat.AhatMono.bot_pin_of_endpointAligned
#print axioms Nivat.AhatMono.ahatMono_ofParts_of_maxA_of_aligned
#print axioms Nivat.AhatMono.eq_hrep_of_enveloped
#print axioms Nivat.AhatMono.subset_iff_suppVal_le_of_enveloped
#print axioms Nivat.AhatMono.hatOf_nonempty
#print axioms Nivat.AhatMono.ahatMono_iff_fwd_suppVal_enveloped
#print axioms Nivat.AhatMono.face_pair_octShape
#print axioms Nivat.AhatMono.face_subsingleton_octShape
#print axioms Nivat.AhatMono.E_octShape
#print axioms Nivat.AhatMono.isLatticeConvexRegion_octShape
#print axioms Nivat.AhatMono.finite_octShape
#print axioms Nivat.AhatMono.enveloped_octShape
#print axioms Nivat.AhatMono.E_oct1
#print axioms Nivat.AhatMono.posArea_oct1
#print axioms Nivat.AhatMono.encard_face_oct1_le
#print axioms Nivat.AhatMono.oL_le
#print axioms Nivat.AhatMono.nondeg_oA
#print axioms Nivat.AhatMono.enveloped_oA
#print axioms Nivat.AhatMono.mono_oA_shift
#print axioms Nivat.AhatMono.mono_oAA
#print axioms Nivat.AhatMono.endpointAligned_oA
#print axioms Nivat.AhatMono.face_oA_slant
#print axioms Nivat.AhatMono.encard_face_oA_slant
#print axioms Nivat.AhatMono.mem_oA_one
#print axioms Nivat.AhatMono.not_mem_oA_two
#print axioms Nivat.AhatMono.not_ahatMono_octagon
#print axioms Nivat.AhatMono.finite_of_hatOf_finite
#print axioms Nivat.AhatMono.posArea_of_enveloped
#print axioms Nivat.AhatMono.ahatMono_of_fwd_suppVal
#print axioms Nivat.AhatMono.ahatMono_of_fwd_suppVal_finset
#print axioms Nivat.AhatMono.not_ahatMono_of_fwd_suppVal_without_mono
#print axioms Nivat.AhatMono.posArea_Sphi_of_two_le_m
#print axioms Nivat.AhatMono.posArea_Sphi
#print axioms Nivat.AhatMono.ahatMono_of_fwd_suppVal_Sphi
#print axioms Nivat.Colle35.DecompDataZ.of_minimalCounterexample
