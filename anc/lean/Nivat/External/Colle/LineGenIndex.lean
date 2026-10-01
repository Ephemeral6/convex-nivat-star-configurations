/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.Lemma45
import Nivat.External.Colle.DecompData
import Nivat.External.Colle.DirectionRigidity
import Nivat.External.Colle.LatticeEdges

/-!
# Lemma 2.6 at the ℤ-minimal decomposition: `ℓ` contains some `h_i`

原文：b3_colle2.txt:309（Lemma 2.6）、:766（`ι` 的定义）。

从 `RegionSteps.lean` 原样搬出（2026-09-22，集成者），使 leaf A 的组装文件
（`LeafAAssemble.lean`，不许 import `RegionSteps`）也能取到 `nℓ` 平行于某个生成元的事实，
从而得到 `−nℓ ∈ E 𝒮_φ`（配 `ZonoEdgeGen.mem_E_zonoF`）。`RegionSteps` 改为 import 本文件。
-/

set_option autoImplicit false

namespace Nivat.ColleReg

open Nivat Nivat.Colle35

variable {ξ : Config ℤ} {vl ℓ : ℤ × ℤ}


/-- **洞 1 of `exists_wedgeResidualR`，按原文自己的路线关闭**（2026-09-20，集成者之手）。

原文：`b3_colle2.txt:939`「Due to Lemma 2.6, we know that `ℓ` contains some vector `h_i`,
which means that `ℓ = ℓ_ι` for some `1 ≤ ι ≤ 2m`」，配 `:788`「let `ι₀` be such that
`ι₀ = ι mod m`」。

**为什么成立（硬规矩 10）**：Lemma 2.6（`:309`）对**任意**形如 `∏(X^{h_i}−1)` 的零化子成立，
只要 `h_i` 两两不平行；这里取 `d` 自己的 `φ`（`d.ann`，`:424`；`d.h_dir` 给两两不平行），
半平面歧义由 `hℓ_pos` 提供。内核形式是
`Nivat.Colle.exists_tangent_of_orbit_halfPlane_ambiguity`（`DirectionRigidity.lean:79`），
它与 `Step_BiONED.exists_biONED_direction` 用的是同一条——那里作用在 Kari–Szabados 的乘积上，
这里作用在 ℤ-极小分解的乘积上，**两个乘积没有任何关系**，所以 `ℓ ∥ h_i` 不能从 `ℓ` 的
选取继承，必须在这里重新用一次 Lemma 2.6。

**逐个量词（硬规矩 7）**：`∃ i` = 原文的 `ι₀`；`dot nℓ (h i) = 0` = 「`ℓ` contains `h_i`」
（`h_i ∥ ℓ`，经 `det_eq_zero_of_dot_eq_zero`：`h_i ⊥ ℓ`、`v⃗_ℓ ⊥ ℓ`、`ℓ ≠ 0` ⟹ `h_i ∥ v⃗_ℓ`）；
`nℓ := (vl.2, −vl.1)` 是 `ℓ` 的本原法向，`Prim nℓ` 由 `Primitive vl` 直接给出。
**不需要** `nℓ ∈ E(𝒮_φ)`：原文的 `ι` 就是由「`ℓ` 含哪个 `h_i`」**定义**的，
`:766` 的重命名条款只是把这个 `i` 记作 `ι`。`OPEN.md #15` 的「`vl` 是 `𝒮_φ` 的边方向」
半边因此**不是欠账**——它在 `:939` 里是 Lemma 2.6 的结论，不是前提。 -/
theorem exists_nℓ_and_index_of_oneSided (d : DecompDataZ ξ)
    (hℓ_pos : Colle45.IsOneSidedNonexpansive ξ ℓ)
    (hℓ_ne : ℓ ≠ 0) (hvl_prim : Primitive vl)
    (hdet_ℓ : Nivat.LE2.dot ℓ vl = 0) :
    ∃ nℓ : ℤ × ℤ, Nivat.LE2.Prim nℓ ∧ Nivat.LE2.dot nℓ vl = 0 ∧
      ∃ i : Fin d.toDecompData.m, Nivat.LE2.dot nℓ (d.toDecompData.h i) = 0 := by
  -- Lemma 2.6 (`:309`) at `d.ann`: the line `ℓ` contains some `h i`.
  obtain ⟨x, y, hx, hy, hne, hagree⟩ := hℓ_pos
  have hnp : Pairwise fun i j => det (d.toDecompData.h i) (d.toDecompData.h j) ≠ 0 :=
    fun i j hij => d.toDecompData.h_dir i j hij
  have hcast : ∀ z : ℤ × ℤ,
      inner2 (-((ℓ.1 : ℝ), (ℓ.2 : ℝ))) z = -((Nivat.LE2.dot ℓ z : ℤ) : ℝ) := by
    intro z
    simp only [inner2, Nivat.LE2.dot, Prod.fst_neg, Prod.snd_neg]
    push_cast
    ring
  have hagree' : ∀ z : ℤ × ℤ, (0 : ℝ) ≤ inner2 (-((ℓ.1 : ℝ), (ℓ.2 : ℝ))) z → x z = y z := by
    intro z hz
    apply hagree z
    rw [hcast] at hz
    have : ((Nivat.LE2.dot ℓ z : ℤ) : ℝ) ≤ 0 := by linarith
    exact_mod_cast this
  obtain ⟨i, hi⟩ :=
    Nivat.Colle.exists_tangent_of_orbit_halfPlane_ambiguity hnp d.ann hx hy hne hagree'
  have hℓh : Nivat.LE2.dot ℓ (d.toDecompData.h i) = 0 := by
    rw [hcast] at hi
    have : ((Nivat.LE2.dot ℓ (d.toDecompData.h i) : ℤ) : ℝ) = 0 := by linarith
    exact_mod_cast this
  -- `h i ⊥ ℓ` and `vl ⊥ ℓ` with `ℓ ≠ 0` ⟹ `h i ∥ vl`.
  have hdet : det (d.toDecompData.h i) vl = 0 :=
    Nivat.LE2.det_eq_zero_of_dot_eq_zero hℓ_ne hℓh hdet_ℓ
  -- The primitive normal of `ℓ`, expressed through `vl`.
  refine ⟨(vl.2, -vl.1), ?_, ?_, i, ?_⟩
  · rw [Nivat.LE2.prim_iff_primitive]
    obtain ⟨a, b, hab⟩ := hvl_prim
    exact ⟨b, -a, by linear_combination hab⟩
  · simp only [Nivat.LE2.dot]; ring
  · simp only [det] at hdet
    simp only [Nivat.LE2.dot]
    linear_combination hdet

end Nivat.ColleReg
