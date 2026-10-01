/-
Copyright (c) 2026. Released under Apache 2.0 license.
Authors: integrator
-/
import Nivat.External.Colle.LeafAShellBottomParts

set_option autoImplicit false

/-!
# `ShellFeed` 与 `EnvOf` 是同一个谓词（第 244 轮，集成者）

lane-leafa-shell 在 `LeafAShellBottomParts.lean` 的三处（`:36` / `:141` / `:410`）写
「`ShellFeed` 即消费者自己的 `shellEnv` 那一格」。**那条读数不对**，但比它本身更有用的是
**正确的对应关系**，本文件把它钉进内核。

## §1 `shellEnv` 是字段，不是债

`ChainPartsFeed.lean:337` 逐字：

    shellEnv : ∃ ε i₀, 0 < ε ∧
      ∀ i, i₀ ≤ i → EnvOf ↑S (ShellMink.shellInter (hatOf A kk vl i)
        (MaxEnv.shell (⋃ i, hatOf A kk vl i) vJ1 nJ cJ ε) w)

与 `ShellFeed`（`LeafAShellBottomParts.lean:237`）逐条对比，**四处不同**：

1. 量词：`shellEnv` 是 `∃ ε i₀`；`ShellFeed` 是 `∀ ε ∀ z₀`。方向相反。
2. 载体：`shellEnv` 说派生交 `shellInter (hatOf A kk vl i) (shell …) w`（带 `w`、带 `i`）；
   `ShellFeed` 说**存在某个有限 `P`** 落在壳里。
3. 谓词：`shellEnv` 用 `EnvOf ↑S`；`ShellFeed` 用 `E P = E ↑𝒮_φ ∧ 面长不等式` 拆开写。
4. `shellEnv` 里有字段 `w`（`:308`，`hsweepW : dot nJ w < 0`），`ShellFeed` 没有。

⟹ 两者不是同一条，**`ShellFeed` 严格更强**（`∀ ε` vs `∃ ε`）。三处散文按 §57 应更正。

## §2 但第 3 条差别是**表面的**：`ShellFeed` 的后三条合取逐字就是 `EnvOf ↑𝒮_φ P`

`LatticeEdges.lean:2514` `LE2.envOf_of_E_eq` 逐字：

    (hT : IsLatticeConvexRegion T) (hE : E T = E U)
    (hle : ∀ n ∈ E U, (face U n).encard ≤ (face T n).encard) → EnvOf U T

而 `ShellFeed` 的八条合取里有 `IsLatticeConvexRegion P`、`E P = E ↑𝒮_φ`、
`∀ n ∈ E P, (face ↑𝒮_φ n).encard ≤ (face P n).encard`。⚠ **第三条的量词跑在 `E P` 上，
而 `envOf_of_E_eq` 要的跑在 `E U` 上** —— 但有 `hE : E P = E ↑𝒮_φ` 在手，两者逐字互化。

⟹ `shellFeed_envOf`（本文件）：`ShellFeed` 的每个 `(ε, z₀)` 实例产出一个
**`E(𝒮_φ)`-包络的有限凸 `P`**，即 `EnvOf ↑𝒮_φ P`。反向 `envOf_shellFeed` 亦成立。

**这条的用处**：`ShellFeed` 不必当成「全树没有的 `AhatMono` 量级形状收敛定理」去正面攻，
它是一条 `EnvOf` 命题，而 `EnvOf` 正是 `maxA` / `envB` / `shellEnv` 三个字段说的同一个谓词。
⟹ 产者应当从**字段侧**接，不是从形状收敛侧造。

## §3 射程自限（PROTOCOL §50）

本文件**不**主张：`ShellFeed` 在链上成立；`shellEnv` 蕴含 `ShellFeed`；两者量词可互换。
只主张 §2 那条**定义层的**互化，以及 §4 那条把 `P` 的存在性接到 `EnvOf` 现货上的判据。
-/

namespace Nivat.IntegShellFeedEnvOf

open Nivat.LE2 Nivat.MaxEnv Nivat.Colle35
open Nivat.LeafAShellBottomParts

variable {α : Type*} {η : Nivat.Config ℤ}

/-- ⭐ **`ShellFeed` 的后三条合取 ＝ `EnvOf ↑𝒮_φ P`。**

正方向：从 `ShellFeed` 的一个实例读出 `EnvOf`。量词转换用 `hE` 改写。 -/
theorem shellFeed_envOf (d : Nivat.Colle35.DecompDataZ η) {T : Set (ℤ × ℤ)}
    {vJ1 nJ : ℤ × ℤ} {cJ : ℤ}
    (hSF : ShellFeed d T vJ1 nJ cJ) (ε : ℕ) (z₀ : ℤ × ℤ)
    (hz₀ : z₀ ∈ MaxEnv.shell T vJ1 nJ cJ (ε + 1))
    (hdz : dot nJ z₀ = cJ - (ε : ℤ) - 1) :
    ∃ P : Set (ℤ × ℤ), P.Finite ∧ P.Nonempty ∧ PosArea P ∧
      P ⊆ MaxEnv.shell T vJ1 nJ cJ (ε + 1) ∧ z₀ ∈ P ∧
      EnvOf (↑d.toDecompData.Sphi : Set (ℤ × ℤ)) P := by
  obtain ⟨P, hfin, hne, harea, hlc, hsub, hmem, hE, hle⟩ := hSF ε z₀ hz₀ hdz
  refine ⟨P, hfin, hne, harea, hsub, hmem, ?_⟩
  refine Nivat.LE2.envOf_of_E_eq hlc hE ?_
  intro n hn
  exact hle n (hE ▸ hn)

/-- ⭐ **反方向：`EnvOf` ＋ 有限性等四条 ⟹ `ShellFeed` 的一个实例的全部八条合取。**

`E P = E ↑𝒮_φ` 由 `Enveloped.E_eq` 从 `EnvOf` 读出（要 `(E ↑𝒮_φ).Finite`），
面长不等式由 `WeaklyEnveloped` 的第二条读出。 -/
theorem shellFeed_conjuncts_of_envOf (d : Nivat.Colle35.DecompDataZ η)
    {P : Set (ℤ × ℤ)}
    (hEfin : (E (↑d.toDecompData.Sphi : Set (ℤ × ℤ))).Finite)
    (henv : EnvOf (↑d.toDecompData.Sphi : Set (ℤ × ℤ)) P) :
    IsLatticeConvexRegion P ∧
      E P = E (↑d.toDecompData.Sphi : Set (ℤ × ℤ)) ∧
      (∀ n ∈ E P, (face (↑d.toDecompData.Sphi : Set (ℤ × ℤ)) n).encard ≤ (face P n).encard) := by
  have hE : E P = E (↑d.toDecompData.Sphi : Set (ℤ × ℤ)) :=
    Nivat.LE2.Enveloped.E_eq hEfin henv
  refine ⟨henv.1.1, hE, ?_⟩
  intro n hn
  exact (henv.1.2 n hn).2

/-- ⭐⭐⭐ **判据形：`ShellFeed` 逐字等价于「每个壳底点被某个 `E(𝒮_φ)`-包络的有限正面积 `P` 罩住」。**

这是本文件的主结论。它把 `ShellFeed` 从「八条合取的新 `Prop`」还原成一条**关于 `EnvOf` 的存在命题**
—— 而 `EnvOf` 正是 `ChainDataGeomParts` 的 `maxA` / `envB` / `shellEnv` 三个字段所用的同一个谓词
（`ChainPartsFeed.lean:229` / `:228` / `:337`）。

⟹ **派工含义**：`ShellFeed` 的产者应从字段侧接（`c.shellEnv` 给的就是一族 `EnvOf`），
不必造 `ShellSubStrip.lean` 自评里那条「全树没有的 `AhatMono` 量级形状收敛定理」。 -/
theorem shellFeed_iff_envOf_cover (d : Nivat.Colle35.DecompDataZ η) {T : Set (ℤ × ℤ)}
    {vJ1 nJ : ℤ × ℤ} {cJ : ℤ}
    (hEfin : (E (↑d.toDecompData.Sphi : Set (ℤ × ℤ))).Finite) :
    ShellFeed d T vJ1 nJ cJ ↔
      ∀ (ε : ℕ) (z₀ : ℤ × ℤ), z₀ ∈ MaxEnv.shell T vJ1 nJ cJ (ε + 1) →
        dot nJ z₀ = cJ - (ε : ℤ) - 1 →
        ∃ P : Set (ℤ × ℤ), P.Finite ∧ P.Nonempty ∧ PosArea P ∧
          P ⊆ MaxEnv.shell T vJ1 nJ cJ (ε + 1) ∧ z₀ ∈ P ∧
          EnvOf (↑d.toDecompData.Sphi : Set (ℤ × ℤ)) P := by
  constructor
  · intro hSF ε z₀ hz₀ hdz
    exact shellFeed_envOf d hSF ε z₀ hz₀ hdz
  · intro h ε z₀ hz₀ hdz
    obtain ⟨P, hfin, hne, harea, hsub, hmem, henv⟩ := h ε z₀ hz₀ hdz
    obtain ⟨hlc, hE, hle⟩ := shellFeed_conjuncts_of_envOf d hEfin henv
    exact ⟨P, hfin, hne, harea, hlc, hsub, hmem, hE, hle⟩

/-- ⭐ **`hEfin` 不是债**：`𝒮_φ` 是 `Finset` ⟹ `(E ↑𝒮_φ).Finite` 由
`LE2.finite_E_of_finite` ＋ `Finset.finite_toSet` 白送，不需要 `PosArea`。 -/
theorem eFinite_Sphi (d : Nivat.Colle35.DecompDataZ η) :
    (E (↑d.toDecompData.Sphi : Set (ℤ × ℤ))).Finite :=
  Nivat.LE2.finite_E_of_finite d.toDecompData.Sphi.finite_toSet

/-- ⭐⭐⭐ **判据的无 binder 形**：`hEfin` 消掉之后，`ShellFeed` 与「`EnvOf` 罩住每个壳底点」
**逐字等价，零前提**。 -/
theorem shellFeed_iff_envOf_cover' (d : Nivat.Colle35.DecompDataZ η) {T : Set (ℤ × ℤ)}
    {vJ1 nJ : ℤ × ℤ} {cJ : ℤ} :
    ShellFeed d T vJ1 nJ cJ ↔
      ∀ (ε : ℕ) (z₀ : ℤ × ℤ), z₀ ∈ MaxEnv.shell T vJ1 nJ cJ (ε + 1) →
        dot nJ z₀ = cJ - (ε : ℤ) - 1 →
        ∃ P : Set (ℤ × ℤ), P.Finite ∧ P.Nonempty ∧ PosArea P ∧
          P ⊆ MaxEnv.shell T vJ1 nJ cJ (ε + 1) ∧ z₀ ∈ P ∧
          EnvOf (↑d.toDecompData.Sphi : Set (ℤ × ℤ)) P :=
  shellFeed_iff_envOf_cover d (eFinite_Sphi d)

end Nivat.IntegShellFeedEnvOf

#print axioms Nivat.IntegShellFeedEnvOf.shellFeed_envOf
#print axioms Nivat.IntegShellFeedEnvOf.shellFeed_conjuncts_of_envOf
#print axioms Nivat.IntegShellFeedEnvOf.shellFeed_iff_envOf_cover
#print axioms Nivat.IntegShellFeedEnvOf.eFinite_Sphi
#print axioms Nivat.IntegShellFeedEnvOf.shellFeed_iff_envOf_cover'
