/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.LeafAItemII
import Nivat.External.Colle.LeafAPigeonhole
import Nivat.External.Colle.LeafALimit
import Nivat.External.Colle.LeafAStabilize

/-!
# Leaf A: the stitching step (`b3_colle2.txt:487-510`)

Lane `lane-leafa`, 2026-09-22.  Assembles the pieces team-lead named ("common `k` + `hmono` +
`agreeA_of_max` → exact stabilisation → `exists_limit_agreeing_along_growing_windows`") into the
paper's `:510` conclusion `ϑ|_{Â_∞} = x̂_per|_{Â_∞}`.

## Two gaps closed here

1. `stabilize_of_mono_agree` (`LeafAStabilize.lean`) only handles a **constant** exponent `k`
   in `hatOf A (fun _ => k) vl i`; the paper's `Â_i := A_i − k_i v⃗_ℓ` (`:488`) keeps each
   stage's own, *varying* `k_i`, and the stabilisation identity
   `ϑ_{i'}|_{Â_i} = ϑ_i|_{Â_i}` for `i ≤ i'` (`:497`) is stated on the **original**, private
   `kk`.  `stabilize_of_ahatMono_agree` below generalises it: given `AhatMono` directly
   (`hatOf A kk vl i ⊆ hatOf A kk vl j` — free along `LeafAItemII.exists_subseq_chain`'s
   subsequence, refuted on the raw index by `AhatMono.lean`) and `kk i ≡ kk j (mod h)`, the
   same `hagree`-based argument as `stabilize_of_mono_agree` goes through, with
   `T_smul_eq_of_mod_eq` (`LeafAStabilize.lean:14`) bridging the two private exponents through
   `xper`'s period instead of requiring them to be literally equal.

2. `exists_accum_point_agree_hatOf` chains: `exists_strictMono_const_mod`
   (pigeonhole `kk i ≡ r (mod h)` along a subsequence `σ`, `:496`/`:500`/`:504`) →
   `exists_limit_agreeing_along_growing_windows` (diagonal accumulation point `θinf`, agreeing
   with `θseq (n i)` on the growing window `hatOf A kk vl (σ i)`) → `stabilize_of_ahatMono_agree`
   (upgrades that to agreement with `θseq i` itself, since `n i ≥ i`) → `hagree` + the pigeonholed
   residue `r` (upgrades `θseq i`'s value to `xper` shifted by the *common* `r`, `x̂_per := T^{r•vl}
   xper`).  The result is exactly Collé's `:510`: `ϑ|_{Â_∞} = x̂_per|_{Â_∞}`, read along the
   subsequence `σ` (every `Â_i` in the original indexing appears as `hatOf A kk vl (σ i)` here;
   the caller composes with `LeafAItemII.exists_subseq_chain`'s own `σ` if a further reindexing of
   `A`/`B`/`kk` themselves is also needed upstream — this file's `σ` is independent of that one
   and only re-threads the *pigeonhole* residue class, not `AhatMono` itself, which is already a
   hypothesis here). -/

set_option autoImplicit false

namespace Nivat

open Nivat.Colle35

/-- **Stabilisation along `AhatMono` with a varying, but mod-`h`-constant, exponent.**
Generalises `stabilize_of_mono_agree` (constant `k`) to the paper's actual `Â_i := A_i − k_i v⃗_ℓ`
with private, only mod-`h`-constant `k_i` (`:488`, `:496`). `hAhatMono` is `ChainAssemble.lean`'s
`AhatMono` binder read directly (free along `LeafAItemII.exists_subseq_chain`'s subsequence);
`hmod` is the pigeonholed residue fact (`exists_strictMono_const_mod`, composed at the two
indices in play); `hagree` is `agreeA_of_max`'s content, unfolded to `A`/`u`. -/
theorem stabilize_of_ahatMono_agree {α : Type*} {η xper : Config α} {vl : ℤ × ℤ} {h : ℕ}
    (hper : (h : ℤ) • vl ∈ Per xper)
    {A : ℕ → Set (ℤ × ℤ)} {u : ℕ → ℤ × ℤ} {kk : ℕ → ℕ} {i j : ℕ}
    (hAhatMono_ij : hatOf A kk vl i ⊆ hatOf A kk vl j)
    (hmod_ij : kk i % h = kk j % h)
    (hagree : ∀ i, ∀ z ∈ A i, η (z + u i) = xper z) :
    ∀ z ∈ hatOf A kk vl i,
      T ((kk i : ℤ) • vl + u i) η z = T ((kk j : ℤ) • vl + u j) η z := by
  intro z hz
  have hzj : z ∈ hatOf A kk vl j := hAhatMono_ij hz
  have hz' : z + (kk i : ℤ) • vl ∈ A i := hz
  have hzj' : z + (kk j : ℤ) • vl ∈ A j := hzj
  have hi := hagree i _ hz'
  have hj := hagree j _ hzj'
  have hxeq : xper (z + (kk i : ℤ) • vl) = xper (z + (kk j : ℤ) • vl) := by
    have hT := congrFun (T_smul_eq_of_mod_eq hper hmod_ij) z
    simpa [T_apply] using hT
  show η (z + ((kk i : ℤ) • vl + u i)) = η (z + ((kk j : ℤ) • vl + u j))
  rw [show z + ((kk i : ℤ) • vl + u i) = (z + (kk i : ℤ) • vl) + u i by abel,
      show z + ((kk j : ℤ) • vl + u j) = (z + (kk j : ℤ) • vl) + u j by abel]
  rw [hi, hxeq, ← hj]

/-- **The `:510` accumulation point, exactly agreeing with the (periodically shifted)
`xper` on every growing window `hatOf A kk vl (σ i)`.**  `σ` is the pigeonhole subsequence
(`exists_strictMono_const_mod`); the residue `r` it produces gives the common shift
`x̂_per := T^{r•vl} xper` matching Collé's normalisation (`:487-490`). `hAhatMono` and `hfin`
are `ChainDataGeom.ofParts`'s own binders (the former free along
`LeafAItemII.exists_subseq_chain`'s reindexing); `hagree` is `agreeA_of_max`. -/
theorem exists_accum_point_agree_hatOf
    {α : Type*} [Finite α] {η xper : Config α} {vl : ℤ × ℤ} {h : ℕ} (hh : 0 < h)
    (hper : (h : ℤ) • vl ∈ Per xper)
    {A : ℕ → Set (ℤ × ℤ)} {u : ℕ → ℤ × ℤ} {kk : ℕ → ℕ}
    (hAhatMono : ∀ i j, i ≤ j → hatOf A kk vl i ⊆ hatOf A kk vl j)
    (hagree : ∀ i, ∀ z ∈ A i, η (z + u i) = xper z)
    (hfin : ∀ i, (A i).Finite) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ r : ℕ, ∃ θ ∈ orbitClosure η,
      ∀ i, ∀ z ∈ hatOf A kk vl (σ i), θ z = T ((r : ℤ) • vl) xper z := by
  classical
  obtain ⟨σ, hσ, r, hmodr⟩ := exists_strictMono_const_mod hh kk
  have hr_lt : r < h := by
    have := Nat.mod_lt (kk (σ 0)) hh
    rwa [hmodr 0] at this
  have hmodr' : ∀ i j, kk (σ i) % h = kk (σ j) % h := by
    intro i j; rw [hmodr i, hmodr j]
  set θseq : ℕ → Config α := fun i => T ((kk (σ i) : ℤ) • vl + u (σ i)) η with hθseq
  have hθseq_mem : ∀ i, θseq i ∈ orbitClosure η := fun i => T_mem_orbitClosure η _
  set W : ℕ → Finset (ℤ × ℤ) := fun i => (Nivat.LeafAItemII.finite_hatOf (hfin (σ i))).toFinset
    with hW
  obtain ⟨θinf, hmem, n, hnmono, hagreeW⟩ :=
    exists_limit_agreeing_along_growing_windows θseq hθseq_mem W
  refine ⟨σ, hσ, r, θinf, hmem, fun i z hz => ?_⟩
  have hzW : z ∈ W i := by rw [hW]; simpa using hz
  have hle : i ≤ n i := hnmono.le_apply
  have hσle : σ i ≤ σ (n i) := hσ.monotone hle
  have hmodσ : kk (σ i) % h = kk (σ (n i)) % h := hmodr' i (n i)
  have hstab' : θseq i z = θseq (n i) z := by
    have := stabilize_of_ahatMono_agree (A := A) (u := u) (η := η) (xper := xper)
      hper (hAhatMono (σ i) (σ (n i)) hσle) hmodσ hagree z hz
    simpa [hθseq] using this
  have hW' := hagreeW i z hzW
  have hz' : z + (kk (σ i) : ℤ) • vl ∈ A (σ i) := hz
  have hbase := hagree (σ i) _ hz'
  have hxper_shift : xper (z + (kk (σ i) : ℤ) • vl) = xper (z + (r : ℤ) • vl) := by
    have hmodri : kk (σ i) % h = r % h := by
      rw [hmodr i]; exact (Nat.mod_eq_of_lt hr_lt).symm
    have hT := congrFun (T_smul_eq_of_mod_eq hper hmodri) z
    simpa [T_apply] using hT
  calc θinf z = θseq (n i) z := hW'
    _ = θseq i z := hstab'.symm
    _ = η (z + ((kk (σ i) : ℤ) • vl + u (σ i))) := by rw [hθseq]; simp [T_apply]
    _ = η ((z + (kk (σ i) : ℤ) • vl) + u (σ i)) := by rw [show z + ((kk (σ i) : ℤ) • vl + u (σ i))
          = (z + (kk (σ i) : ℤ) • vl) + u (σ i) by abel]
    _ = xper (z + (kk (σ i) : ℤ) • vl) := hbase
    _ = xper (z + (r : ℤ) • vl) := hxper_shift
    _ = T ((r : ℤ) • vl) xper z := by simp [T_apply]

end Nivat

#print axioms Nivat.stabilize_of_ahatMono_agree
#print axioms Nivat.exists_accum_point_agree_hatOf
