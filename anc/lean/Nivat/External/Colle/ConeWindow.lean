/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.RegionSweep
import Nivat.External.Colle.LatticeEdges

set_option autoImplicit false

/-!
# Half-strip absorption under fan adjacency

**原文：b3_colle2.txt:770, 778, 794-798, Figure 10**

This file proves that the half-strip `H_B(ℓ) = {b + t•vl : b ∈ B, t ∈ ℤ₊}` absorbs
a `u'`-step when `u'` is an adjacent edge direction in the normal fan of an
enveloped set `B`.

**Key mechanism (from Definition 3.2, line 402)**: When `EnvOf S B` holds with
`(E B).Finite` and `(E B).encard = (E S).encard`, we have `E B ⊆ E S` and equal
cardinality, hence `E B = E S`. Thus `B` and `S` share the same normal fan.

The fan adjacency condition (line 770: "the edge parallel to ℓ_{i+1} is a successor
of the edge parallel to ℓ_i") ensures that a `u'`-step landing at or above the
`ℓ_B` support line stays within the half-strip.

-/

open Nivat.LE2 Nivat.RegionSweep

namespace Nivat.ConeWindow

/-- **Counterexample: window translation fails when `B` is not enveloped**

**Binder dropped**: The statement omits `EnvOf S B` (Definition 3.2, b3_colle2.txt:402).

This theorem shows that without the enveloped hypothesis, a translate of a
generating set can poke out of the cone region near the apex. The witness
`B := {(0,0)}` is a singleton, which has no edges and fails `PosArea` (`:240`),
so it cannot be enveloped for any `S`.

**Witness**:
- `B := {(0,0)}` (NOT enveloped — singleton with no edges)
- `S := {(0,1), (1,0)}`
- `vl := (1,0)`, `u' := (0,1)`
- `n := (0,-1)` (so `dot n vl = 0`, `dot n u' = -1`)
- `a := (0,1)` (strict argmin: `dot n (0,1) = -1 < 0 = dot n (1,0)`)
- `w := (0,0)` (cone apex, `s=0, t=0`)

The non-argmin point `z = (1,0)` translates to `z + (w - a) = (1,0) + (0,-1) = (1,-1)`.
To be in the cone, `(1,-1) = (0,0) + s•(1,0) + t•(0,1)` requires `s=1, t=-1`.
But `t=-1 < 0`, so `(1,-1) ∉ sweep (sweep B vl) u'`. ✗

-/
theorem not_translate_window_in_cone_when_not_enveloped :
    ∃ (B : Set (ℤ × ℤ)) (S : Finset (ℤ × ℤ)) (vl u' n a w : ℤ × ℤ),
      B.Finite ∧ B.Nonempty ∧
      dot n vl = 0 ∧ dot n u' = -1 ∧
      a ∈ S ∧ (∀ z ∈ S.erase a, dot n a < dot n z) ∧
      w ∈ sweep (sweep B vl) u' ∧
      ∃ z ∈ S.erase a, z + (w - a) ∉ sweep (sweep B vl) u' := by
  refine ⟨{(0, 0)}, {(0, 1), (1, 0)}, (1, 0), (0, 1), (0, -1), (0, 1), (0, 0),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Set.toFinite _
  · exact ⟨(0, 0), rfl⟩
  · simp [dot]
  · simp [dot]
  · simp [Finset.mem_insert, Finset.mem_singleton]
  · intro z hz
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hz
    obtain ⟨hne, hz'⟩ := hz
    rcases hz' with rfl | rfl
    · contradiction
    · simp [dot]
  · refine ⟨(0, 0), ⟨(0, 0), rfl, 0, by simp⟩, 0, by simp⟩
  · refine ⟨(1, 0), ?_, ?_⟩
    · simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
      decide
    · intro ⟨g, ⟨b, hb, s, hgs⟩, t, heq⟩
      simp at hb
      rw [hb] at hgs
      simp at hgs
      obtain ⟨rfl⟩ := hgs
      simp at heq

/-! ## 撤回 (2026-09-20, 集成者)：`FanAdjacent` 与 `halfStrip_absorb_uStep` 的 `sorry` 桩

两条都带 `sorry` 落进主仓（红线违例），已删。`FanAdjacent` 的 `sorry` 在 **`def` 体内**，
是最坏的一种——它让下游每一条引用该定义的陈述都静默地依赖 `sorryAx`，而
`check1.sh` 只报一个 `EXIT`，不会把这件事顶到眼前；`halfStrip_absorb_uStep` 更把
`(sorry : ℤ × ℤ)` 写进了**binder**，于是那条定理连陈述的是什么都不确定。

**欠的东西说清楚，留给有编译权限的 lane。** 需要的不是 `hstepIn` 那种对整条半带的条件，
而是 lane Wlines 在 `ConeLines.lean:431` 归约出来的**有限**条件

    hBstep : ∀ b ∈ B, cz ≤ dot nℓ (b + u') → ∃ b' ∈ B, ∃ k : ℤ, b + u' = b' + k • vl

（`stepIn_fullSweep`，`ConeLines.lean:409`，把它抬成 seed-step 前提；`hperp` 在那里才
真正用上：`ℤ·vl` 的尾巴不动 `nℓ`-层级，所以层级测试落回 `b ∈ B` 这个有限条件）。

**它归约成一句可判定的几何话**：`dot nℓ (b + u') = dot nℓ b - 1`，即 `b + u'` 恰好低一层；
而同一层上的两点相差 `vl` 的整数倍（`nℓ` 本原且 `⊥ vl`，见
`AItemFour.det_eq_zero_of_dot_eq_zero` + `exists_coord_on_line`）。所以 `hBstep`
**等价于**：`B` 在 `cz` 与 `suppVal B nℓ` 之间的**每一层都非空**。

⚠ **这一步不是自动的，不要当成显然。** 对一般格凸集为假：`B = {(0,0), (1,2)}`、
`nℓ = (0,1)` 是格凸的（`conv B` 的格点只有这两个，`gcd(1,2)=1`），层 `0` 与 `2` 非空而层 `1` 空。
该见证的 `PosArea` 为假，所以**正面命题要带 `PosArea B`**（由 `EnvOf` 经
`posArea_of_envOf` 免费得到）。正面方向是否成立、以及证法，是真数学，没测过之前
不许写进任何文档当结论（`PROTOCOL.md` §15）。

`b3_colle2.txt:770` 的扇邻接（"the edge parallel to `ℓ_{i+1}` is a successor of the edge
parallel to `ℓ_i`"）不需要先建法向的循环序——上面那条层级陈述已经把它替掉了。 -/

end Nivat.ConeWindow

#print axioms Nivat.ConeWindow.not_translate_window_in_cone_when_not_enveloped
