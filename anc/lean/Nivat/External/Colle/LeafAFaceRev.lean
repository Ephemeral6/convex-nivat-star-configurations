/-
Copyright (c) 2026. Released under Apache 2.0 license.
Authors: lane-chaindata-lead
-/
import Nivat.External.Colle.ANormal

/-!
# `FaceBlock.reverse` — the same face, walked the other way

Lane `lane-chaindata-lead`, 2026-09-23.

## Why this exists

`ofPartsExhaustsInter` (`ChainExhaustInter.lean`) takes `vJ` together with
`F : FaceBlock S nJ vJ`, and `FaceBlock` carries `dot_nJ_vJ : dot n v = 0`
(`ANormal.lean:610`).  With `vJ_prim`/`nJ_prim` both `Primitive` and `nJ = -J`, that pins

```
vJ = dir (-J) = -(dir J)      or      vJ = -(dir (-J)) = dir J
```

and nothing else.  Which of the two is correct is **orientation-dependent**, because the
surviving direction is the one the `J`-face recedes along:

* ccw branch (`dir (-nℓ) = vl`): `exists_gJ_pinned_ccw` pins the face *start* at `g_J`, and
  `hgrow_of_pinned_ccw` (`LeafAJSelect.lean:631`) produces `g_J + t • dir J ∈ Ahat (σ i)`.
  So `+dir J` is in the recession cone of `⋃ i, hatOf A kk vl i` and `-dir J` is not.
* cw branch (`dir (-nℓ) = -vl`): `exists_gJ_pinned_cw` pins the face *end*, and
  `hgrow_of_pinned_cw` (`LeafAJSelect.lean:693`) produces `g_J - t • dir J`.  The surviving
  direction is `-dir J`.

But the only producer, `DecompDataZ.exists_faceBlock_at` (`LeafAFaceAt.lean:46`), always
returns `v := dir ν` at `ν := nJ = -J`, i.e. `vJ = -(dir J)` — right for cw, wrong for ccw.

`FaceBlock` turns out to be exactly symmetric under `v ↦ -v` with the two distinguished
vertices swapped, so the ccw branch can just reverse the block the producer hands it.  Each
reversed field is the *other* field of the original, verbatim:

| reversed field | is the original's |
|---|---|
| `lex` at `a := F.a'`, direction `-v` | `lex'` (`dot (-(-v)) = dot v`) |
| `lex'` at `a' := F.a`, direction `-v` | `lex` |
| `edge`: `b = F.a' + j • (-v)` | `edge'`: `b = F.a' - j • v` |
| `edge'`: `b = F.a - j • (-v)` | `edge`: `b = F.a + j • v` |

No new content, no choice: this is the observation that a segment has two endpoints and the
structure names them in a direction-dependent way.

## Downstream effect at the call site

`ofPartsExhaustsInter` also takes `gen_eq : gen = F.a'`, and `exists_chainData`'s first
existential component is that same `gen`.  Reversing therefore moves the generator from `F.a'`
to `F.a`; that is harmless because `gen` is existentially quantified in the goal and
`FaceBlock.generatesAt_a'` (`ChainAssemble.lean:294`) is stated generically — applied to the
reversed block it yields `GeneratesAt ξ S (F.reverse).a' = GeneratesAt ξ S F.a`, via
`(F.reverse).lex' = F.lex`.
-/

set_option autoImplicit false

namespace Nivat.Colle35

open Nivat Nivat.LE2

variable {S : Finset (ℤ × ℤ)} {n v : ℤ × ℤ}

/-- **The same face block, traversed in the opposite direction.**  Swaps the two distinguished
vertices and negates the edge direction; every field is the original's mirror field. -/
def FaceBlock.reverse (F : FaceBlock S n v) : FaceBlock S n (-v) where
  a := F.a'
  a' := F.a
  r := F.r
  latticeConvex_S := F.latticeConvex_S
  a_mem := F.a'_mem
  a'_mem := F.a_mem
  lex := by
    intro b hb
    have := F.lex' b hb
    rwa [neg_neg]
  lex' := by
    intro b hb
    exact F.lex b hb
  edge := by
    intro b hb
    rcases F.edge' b hb with ⟨j, hj1, hj2, hbeq⟩ | hge
    · exact Or.inl ⟨j, hj1, hj2, by rw [hbeq, smul_neg, ← sub_eq_add_neg]⟩
    · exact Or.inr hge
  edge' := by
    intro b hb
    rcases F.edge b hb with ⟨j, hj1, hj2, hbeq⟩ | hge
    · exact Or.inl ⟨j, hj1, hj2, by rw [hbeq, smul_neg, sub_neg_eq_add]⟩
    · exact Or.inr hge
  dot_nJ_vJ := by
    have h := F.dot_nJ_vJ
    obtain ⟨n1, n2⟩ := n
    obtain ⟨v1, v2⟩ := v
    simp only [dot, Prod.fst_neg, Prod.snd_neg] at h ⊢
    linarith

@[simp] theorem FaceBlock.reverse_a (F : FaceBlock S n v) : (F.reverse).a = F.a' := rfl

@[simp] theorem FaceBlock.reverse_a' (F : FaceBlock S n v) : (F.reverse).a' = F.a := rfl

@[simp] theorem FaceBlock.reverse_r (F : FaceBlock S n v) : (F.reverse).r = F.r := rfl

/-- The endpoint equation transported across `reverse`: if `a' = a + r • v` then, in the
reversed block, `a' = a + r • (-v)` reads `F.a = F.a' - r • v`. -/
theorem FaceBlock.reverse_endpoint (F : FaceBlock S n v)
    (h : F.a' = F.a + (F.r : ℤ) • v) :
    (F.reverse).a' = (F.reverse).a + ((F.reverse).r : ℤ) • (-v) := by
  show F.a = F.a' + (F.r : ℤ) • (-v)
  rw [h, smul_neg]
  abel

end Nivat.Colle35

#print axioms Nivat.Colle35.FaceBlock.reverse
#print axioms Nivat.Colle35.FaceBlock.reverse_endpoint
