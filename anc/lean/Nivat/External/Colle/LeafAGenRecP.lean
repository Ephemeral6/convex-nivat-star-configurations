import Nivat.External.Colle.LeafARecP
import Nivat.External.Colle.ChainAssemble
import Nivat.External.Colle.AhatMono

/-!
# lane-leafa-gen：`rec_p`（`p = -vl`）的**最后一个洞已经是自由的**

`Nivat.LeafARecP.rec_p_of_anchor`（`LeafARecP.lean:97`）把 `rec_p` 归约到 7 条前提，
其 docstring 自述唯一未兑现的是 `hAhatConv : IsLatticeConvexRegion (⋃ i, hatOf A kk vl i)`
（`rec_p_wired`（`:183`）把它留成显式假设）。

**本文件的内容一句话：那条不是洞。** `ChainAssemble.latticeConvex_iUnion_hatOf`
（`ChainAssemble.lean:338`）从 `Env = EnvOf ↑S` ＋ `maxA` ＋ `hfin` ＋ `AhatMono` 就给出它，
而这四条在 `ChainDataGeomParts`（`ChainPartsFeed.lean:198`）里**逐条是字段**
（`maxA` `:209` 把 `Env` 写死成 `EnvOf ↑S`，`hfin` `:219`，`AhatMono` `:212`），
在 `exists_normalised_chain`（`ChainKK.lean:92`）里是输出合取项 4 / 7 / 13。

⚠ 同理 `hAconv : ∀ i, IsLatticeConvexRegion (A i)` 也从 `maxA` 免费
（`envA_of_max` → `Enveloped.1.1`），`rec_p_of_anchor` 的 docstring 已经这么写了，
本文件只是把它兑现在内核里。

## 剩下真正的三条（本文件把它们留作 binder，逐条写明来路）

| binder | 来路 | 状态 |
|---|---|---|
| `hg₁0 : g₁ ∈ A 0` | `b3_colle2.txt:488`「Let `g₁ ∈ A₁`」 | 链侧未接 |
| `hg₁_reach : ∀ i, g₁ + kk i • vl ∈ A i` | `:488` `k_i` 的定义性质；= `exists_normalised_chain` 输出合取项 12 的 `.1.1` | 链侧**有**，未接 |
| `hkk_max : ∀ i t, g₁ + t•vl ∈ A i → t ≤ kk i` | `:488`「**final** point」；= 合取项 12 的 `.2`（`IsGreatest`） | 链侧**有**，未接 |

⟹ 三条全是 `exists_normalised_chain` 的**同一个** `IsGreatest` 合取项（`ChainKK.lean:115`）
拆出来的，加上 `g₁ ∈ A 0`。**`rec_p` 在 `p = -vl` 上不欠新几何义务。**

## ⚠ 本文件答不了什么

* 只做 `p = -vl`。`ChainDataGeomParts.rec_p`（`:249`）的 `p` 是自由参数；
  `RegionSteps.lean:1359` 的 `hp_neg` 给的是 `p = -(c:ℤ)•vl`（**禁入模块，我没读源，转述自 team-lead**，§50）。
  `c ≥ 2` 的情形本文件**没做**。
* 不主张这条路比 `tmp/wip/leafagen-chaindata.lean` 的 `rec_p_of_kk_step` 好——
  两条前提集不可比：这条要锚点 `g₁`，那条要 `kk` 的 `+c` 步可达。
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Nivat.LaneLeafAGenRecP

open Nivat Nivat.LE2 Nivat.Colle35 Nivat.ChainAsm

variable {α : Type*}

/-- **`rec_p`（`p = -vl`）只剩锚点三条。**

对比 `LeafARecP.rec_p_of_anchor`（`LeafARecP.lean:97`）：它的 `hAconv` 与 `hAhatConv`
在这里都被 `maxA` / `hfin` / `AhatMono` 兑现掉了，不再是 binder。 -/
theorem rec_p_of_chain_fields (η xper : Config α) (vl : ℤ × ℤ) (S : Finset (ℤ × ℤ))
    {B A : ℕ → Set (ℤ × ℤ)} {u : ℕ → ℤ × ℤ} {kk : ℕ → ℕ} {g₁ : ℤ × ℤ}
    (maxA : ∀ i, IsMaxEnvIn (EnvOf (↑S : Set (ℤ × ℤ))) (canonA η xper vl B u i) (A i))
    (hfin : ∀ i, (hatOf A kk vl i).Finite)
    (AhatMono : ∀ i j, i ≤ j → hatOf A kk vl i ⊆ hatOf A kk vl j)
    (subBA : ∀ i, B i ⊆ A i)
    (subAB : ∀ i, A i ⊆ B (i + 1))
    (hg₁0 : g₁ ∈ A 0)
    (hg₁_reach : ∀ i, g₁ + (kk i : ℤ) • vl ∈ A i)
    (hkk_unbounded : ∀ N : ℕ, ∃ i, N ≤ kk i) :
    ∀ g ∈ ⋃ i, hatOf A kk vl i, g + (-vl) ∈ ⋃ i, hatOf A kk vl i := by
  have hAconv : ∀ i, IsLatticeConvexRegion (A i) := fun i => (envA_of_max maxA i).1.1
  exact Nivat.LeafARecP.rec_p_of_anchor hAconv subBA subAB hg₁0 hg₁_reach hkk_unbounded
    (latticeConvex_iUnion_hatOf η xper vl S (EnvOf (↑S : Set (ℤ × ℤ))) B A u kk rfl
      maxA hfin AhatMono)

/-- **`hkk_unbounded` 也不是洞**：`LeafARecP.kk_unbounded_of_itemII`（`LeafARecP.lean:144`）
从 `ItemII` ＋ `hkk_max` 给出它，两条都是链输出。本条把上面那条再收紧一格，
⟹ **`rec_p`（`p = -vl`）的全部残差 = 锚点三条 `hg₁0` / `hg₁_reach` / `hkk_max`。** -/
theorem rec_p_of_chain_fields_itemII (η xper : Config α) (vl : ℤ × ℤ) (S : Finset (ℤ × ℤ))
    {B A : ℕ → Set (ℤ × ℤ)} {u : ℕ → ℤ × ℤ} {kk : ℕ → ℕ} {g₁ nℓ : ℤ × ℤ} {cz : ℤ}
    (hperp : dot nℓ vl = 0)
    (maxA : ∀ i, IsMaxEnvIn (EnvOf (↑S : Set (ℤ × ℤ))) (canonA η xper vl B u i) (A i))
    (hfin : ∀ i, (hatOf A kk vl i).Finite)
    (AhatMono : ∀ i j, i ≤ j → hatOf A kk vl i ⊆ hatOf A kk vl j)
    (subBA : ∀ i, B i ⊆ A i)
    (subAB : ∀ i, A i ⊆ B (i + 1))
    (hII : ItemII B nℓ cz)
    (hg₁0 : g₁ ∈ A 0)
    (hg₁_level : cz ≤ dot nℓ g₁)
    (hg₁_reach : ∀ i, g₁ + (kk i : ℤ) • vl ∈ A i)
    (hkk_max : ∀ i t : ℕ, g₁ + (t : ℤ) • vl ∈ A i → t ≤ kk i) :
    ∀ g ∈ ⋃ i, hatOf A kk vl i, g + (-vl) ∈ ⋃ i, hatOf A kk vl i :=
  rec_p_of_chain_fields η xper vl S maxA hfin AhatMono subBA subAB hg₁0 hg₁_reach
    (Nivat.LeafARecP.kk_unbounded_of_itemII hperp hII subBA hg₁_level hkk_max)

/-! ## §2 锚点三条里，**两条已经是 `exists_normalised_chain` 的输出**

合取项 12（`ChainKK.lean:115`）逐字是

```
∀ i, IsGreatest {t : ℤ | g₁ + t • vl ∈ hatOf A kk vl i ∧ dot nℓ (g₁ + t • vl) = cz} 0
```

下面两条把它拆成 `rec_p_of_anchor` 要的形状。⟹ 三条残差里只剩 `hg₁0` 真的没有来路。
-/

/-- **`hg₁_reach` ⟸ 合取项 12 的 `.1.1`**（`0 ∈ S` 那一半）。 -/
theorem hg₁_reach_of_isGreatest {A : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ} {vl g₁ nℓ : ℤ × ℤ} {cz : ℤ}
    (halign : ∀ i, IsGreatest
      {t : ℤ | g₁ + t • vl ∈ hatOf A kk vl i ∧ dot nℓ (g₁ + t • vl) = cz} 0) :
    ∀ i, g₁ + (kk i : ℤ) • vl ∈ A i := by
  intro i
  have h := (halign i).1.1
  rw [zero_smul, add_zero] at h
  exact h

/-- **`hkk_max` ⟸ 合取项 12 的 `.2`**（上界那一半），取 `t := s - kk i`。

`dot nℓ (g₁ + t•vl) = cz` 由 `hperp` ＋ `hg₁cz`（合取项 11）兑现。 -/
theorem hkk_max_of_isGreatest {A : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ} {vl g₁ nℓ : ℤ × ℤ} {cz : ℤ}
    (hperp : dot nℓ vl = 0) (hg₁cz : dot nℓ g₁ = cz)
    (halign : ∀ i, IsGreatest
      {t : ℤ | g₁ + t • vl ∈ hatOf A kk vl i ∧ dot nℓ (g₁ + t • vl) = cz} 0) :
    ∀ i s : ℕ, g₁ + (s : ℤ) • vl ∈ A i → s ≤ kk i := by
  intro i s hs
  have hlev : ∀ t : ℤ, dot nℓ (g₁ + t • vl) = cz := fun t => by
    rw [Colle35.dot_add_zsmul_of_perp hperp g₁ t, hg₁cz]
  have hmem : g₁ + ((s : ℤ) - (kk i : ℤ)) • vl ∈ hatOf A kk vl i := by
    show g₁ + ((s : ℤ) - (kk i : ℤ)) • vl + (kk i : ℤ) • vl ∈ A i
    have : g₁ + ((s : ℤ) - (kk i : ℤ)) • vl + (kk i : ℤ) • vl = g₁ + (s : ℤ) • vl := by
      rw [sub_smul]; abel
    rw [this]; exact hs
  have hle : (s : ℤ) - (kk i : ℤ) ≤ 0 := (halign i).2 ⟨hmem, hlev _⟩
  omega

/-! ## §3 端到端：把 `exists_normalised_chain` 的输出直接喂进去

下面这条只留一条 binder 是链外的：**`hg₁0 : g₁ ∈ A 0`**。
其余全部来自 `ChainKK.exists_normalised_chain`（`ChainKK.lean:92`）的输出合取项：
4（`maxA`）／5（`subBA`）／6（`subAB`）／7（`(A i).Finite`）／8（`ItemII`）／
11（`dot nℓ g₁ = cz`）／12（`IsGreatest`）／13（`AhatMono`）。

⚠ `hfin` 由合取项 7 经 `AhatMono.finite_shift` ＋ `hatOf_eq_shift` 兑现（平移双射）。

⛔ **`hg₁0` 为什么还欠**：原文 `b3_colle2.txt:488` 明写 `k₁ = 0`，于是 `g₁ ∈ Â_1 = A_1`；
但 `exists_normalised_chain` 做了**尾移 ＋ 子列**两次重标号，`kk 0 = 0` 在输出里**没有被导出**。
⟹ 这是重标号吃掉的一条信息，不是新几何义务。**判定归集成者。**
-/

/-- **`rec_p`（`p = -vl`）端到端：只欠 `hg₁0`。** -/
theorem rec_p_of_normalised_output (η xper : Config α) (vl : ℤ × ℤ) (S : Finset (ℤ × ℤ))
    {B A : ℕ → Set (ℤ × ℤ)} {u : ℕ → ℤ × ℤ} {kk : ℕ → ℕ} {g₁ nℓ : ℤ × ℤ} {cz : ℤ}
    (hperp : dot nℓ vl = 0)
    (maxA : ∀ i, IsMaxEnvIn (EnvOf (↑S : Set (ℤ × ℤ))) (canonA η xper vl B u i) (A i))
    (subBA : ∀ i, B i ⊆ A i)
    (subAB : ∀ i, A i ⊆ B (i + 1))
    (hAfin : ∀ i, (A i).Finite)
    (hII : ItemII B nℓ cz)
    (hg₁cz : dot nℓ g₁ = cz)
    (halign : ∀ i, IsGreatest
      {t : ℤ | g₁ + t • vl ∈ hatOf A kk vl i ∧ dot nℓ (g₁ + t • vl) = cz} 0)
    (AhatMono : ∀ i j, i ≤ j → hatOf A kk vl i ⊆ hatOf A kk vl j)
    (hg₁0 : g₁ ∈ A 0) :
    ∀ g ∈ ⋃ i, hatOf A kk vl i, g + (-vl) ∈ ⋃ i, hatOf A kk vl i := by
  have hfin : ∀ i, (hatOf A kk vl i).Finite := fun i => by
    rw [hatOf_eq_shift]
    exact Nivat.AhatMono.finite_shift (hAfin i)
  exact rec_p_of_chain_fields_itemII η xper vl S hperp maxA hfin AhatMono subBA subAB hII
    hg₁0 (le_of_eq hg₁cz.symm) (hg₁_reach_of_isGreatest halign)
    (hkk_max_of_isGreatest hperp hg₁cz halign)

/-! ## §4 ⭐ `hg₁0` 也不需要 —— 残差降到 **0**

§3 把残差记成一条 `hg₁0 : g₁ ∈ A 0`。**那条是 `LeafARecP.rec_p_of_anchor` 的证法造成的，
不是命题需要的。** 它用 `g₁ ∈ A i`（即 `g₁ + 0•vl ∈ A i`）当格凸区间的**下端点**；
但 `mem_of_between`（`RegionCut.lean:201`）的下端点 `s` 是**自由参数**，
换成 `s := kk 0` 就行——而 `g₁ + kk 0 • vl ∈ A 0 ⊆ A i` 正是 `hg₁_reach 0` ＋ 链单调。

代价只是把 `hkk_unbounded` 用在 `k + kk 0` 而不是 `k` 上，而它是「∀ N」的，不多花钱。

⟹ **`rec_p`（`p = -vl`）在 `exists_normalised_chain` 的输出上是白给的，一条链外假设都不欠。**
-/

/-- **`rec_p`（`p = -vl`），零链外假设。**

对比 §3 的 `rec_p_of_normalised_output`：`hg₁0` 不再出现。
binder 逐条对 `ChainKK.exists_normalised_chain`（`ChainKK.lean:92`）的输出合取项：
4（`maxA`）／5（`subBA`）／6（`subAB`）／7（`hAfin`）／8（`hII`）／11（`hg₁cz`）／
12（`halign`）／13（`AhatMono`），`hperp` 是构造器自己的常设假设。 -/
theorem rec_p_free (η xper : Config α) (vl : ℤ × ℤ) (S : Finset (ℤ × ℤ))
    {B A : ℕ → Set (ℤ × ℤ)} {u : ℕ → ℤ × ℤ} {kk : ℕ → ℕ} {g₁ nℓ : ℤ × ℤ} {cz : ℤ}
    (hperp : dot nℓ vl = 0)
    (maxA : ∀ i, IsMaxEnvIn (EnvOf (↑S : Set (ℤ × ℤ))) (canonA η xper vl B u i) (A i))
    (subBA : ∀ i, B i ⊆ A i)
    (subAB : ∀ i, A i ⊆ B (i + 1))
    (hAfin : ∀ i, (A i).Finite)
    (hII : ItemII B nℓ cz)
    (hg₁cz : dot nℓ g₁ = cz)
    (halign : ∀ i, IsGreatest
      {t : ℤ | g₁ + t • vl ∈ hatOf A kk vl i ∧ dot nℓ (g₁ + t • vl) = cz} 0)
    (AhatMono : ∀ i j, i ≤ j → hatOf A kk vl i ⊆ hatOf A kk vl j) :
    ∀ g ∈ ⋃ i, hatOf A kk vl i, g + (-vl) ∈ ⋃ i, hatOf A kk vl i := by
  have hg₁_reach : ∀ i, g₁ + (kk i : ℤ) • vl ∈ A i := hg₁_reach_of_isGreatest halign
  have hkk_unbounded : ∀ N : ℕ, ∃ i, N ≤ kk i :=
    Nivat.LeafARecP.kk_unbounded_of_itemII hperp hII subBA (le_of_eq hg₁cz.symm)
      (hkk_max_of_isGreatest hperp hg₁cz halign)
  have hAconv : ∀ i, IsLatticeConvexRegion (A i) := fun i => (envA_of_max maxA i).1.1
  have hfin : ∀ i, (hatOf A kk vl i).Finite := fun i => by
    rw [hatOf_eq_shift]; exact Nivat.AhatMono.finite_shift (hAfin i)
  have hAmono : ∀ i j, i ≤ j → A i ⊆ A j := by
    intro i j hij
    induction j, hij using Nat.le_induction with
    | base => exact subset_rfl
    | succ n _ ih => exact ih.trans ((subAB n).trans (subBA (n + 1)))
  -- 下端点取 `kk 0`（而不是 `0`），于是不需要 `g₁ ∈ A 0`。
  have hray : ∀ k : ℕ, g₁ + (k : ℤ) • (-vl) ∈ ⋃ i, hatOf A kk vl i := by
    intro k
    obtain ⟨i, hi⟩ := hkk_unbounded (k + kk 0)
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    show g₁ + (k : ℤ) • (-vl) + (kk i : ℤ) • vl ∈ A i
    have hs : g₁ + (kk 0 : ℤ) • vl ∈ A i := hAmono 0 i (Nat.zero_le i) (hg₁_reach 0)
    have hu : g₁ + (kk i : ℤ) • vl ∈ A i := hg₁_reach i
    have hik : (k : ℤ) + (kk 0 : ℤ) ≤ (kk i : ℤ) := by exact_mod_cast hi
    have h1 : (kk 0 : ℤ) ≤ (kk i : ℤ) - (k : ℤ) := by omega
    have h2 : (kk i : ℤ) - (k : ℤ) ≤ (kk i : ℤ) := by omega
    have hmem := Nivat.LE2.mem_of_between (hAconv i) hs hu h1 h2
    have heq : g₁ + (k : ℤ) • (-vl) + (kk i : ℤ) • vl
        = g₁ + ((kk i : ℤ) - (k : ℤ)) • vl := by
      rw [sub_smul, smul_neg]; abel
    rw [heq]
    exact hmem
  exact Nivat.Colle35.rec_of_ray
    (latticeConvex_iUnion_hatOf η xper vl S (EnvOf (↑S : Set (ℤ × ℤ))) B A u kk rfl
      maxA hfin AhatMono) hray

/-! ## §5 一般的 `p = -(c:ℤ) • vl`

§4 做的是 `c = 1`。字段 `rec_p`（`ChainPartsFeed.lean:249`）的 `p` 是自由参数，
而 `RegionSteps.lean:1359` 的 `hp_neg` 给的是 `p = -(c:ℤ)•vl`（⚠ 禁入模块，转述自集成者，§50）。

机理不变：把 `-vl` 方向的射线整体抽出来（`ray_neg_vl`），
再对 `d := -(c:ℤ)•vl` 取它的第 `k*c` 个点。⟹ `c` 取任何自然数都过，含 `c = 0`（此时 `p = 0`，平凡）。
-/

/-- **`-vl` 方向的整条射线在 `Â_∞` 里**，从链输出免费。§4 与 §5 共用它。 -/
theorem ray_neg_vl (η xper : Config α) (vl : ℤ × ℤ) (S : Finset (ℤ × ℤ))
    {B A : ℕ → Set (ℤ × ℤ)} {u : ℕ → ℤ × ℤ} {kk : ℕ → ℕ} {g₁ nℓ : ℤ × ℤ} {cz : ℤ}
    (hperp : dot nℓ vl = 0)
    (maxA : ∀ i, IsMaxEnvIn (EnvOf (↑S : Set (ℤ × ℤ))) (canonA η xper vl B u i) (A i))
    (subBA : ∀ i, B i ⊆ A i)
    (subAB : ∀ i, A i ⊆ B (i + 1))
    (hII : ItemII B nℓ cz)
    (hg₁cz : dot nℓ g₁ = cz)
    (halign : ∀ i, IsGreatest
      {t : ℤ | g₁ + t • vl ∈ hatOf A kk vl i ∧ dot nℓ (g₁ + t • vl) = cz} 0) :
    ∀ m : ℕ, g₁ + (-(m : ℤ)) • vl ∈ ⋃ i, hatOf A kk vl i := by
  have hg₁_reach : ∀ i, g₁ + (kk i : ℤ) • vl ∈ A i := hg₁_reach_of_isGreatest halign
  have hkk_unbounded : ∀ N : ℕ, ∃ i, N ≤ kk i :=
    Nivat.LeafARecP.kk_unbounded_of_itemII hperp hII subBA (le_of_eq hg₁cz.symm)
      (hkk_max_of_isGreatest hperp hg₁cz halign)
  have hAconv : ∀ i, IsLatticeConvexRegion (A i) := fun i => (envA_of_max maxA i).1.1
  have hAmono : ∀ i j, i ≤ j → A i ⊆ A j := by
    intro i j hij
    induction j, hij using Nat.le_induction with
    | base => exact subset_rfl
    | succ n _ ih => exact ih.trans ((subAB n).trans (subBA (n + 1)))
  intro m
  obtain ⟨i, hi⟩ := hkk_unbounded (m + kk 0)
  refine Set.mem_iUnion.mpr ⟨i, ?_⟩
  show g₁ + (-(m : ℤ)) • vl + (kk i : ℤ) • vl ∈ A i
  have hs : g₁ + (kk 0 : ℤ) • vl ∈ A i := hAmono 0 i (Nat.zero_le i) (hg₁_reach 0)
  have hu : g₁ + (kk i : ℤ) • vl ∈ A i := hg₁_reach i
  have hik : (m : ℤ) + (kk 0 : ℤ) ≤ (kk i : ℤ) := by exact_mod_cast hi
  have hmem := Nivat.LE2.mem_of_between (hAconv i) hs hu
    (show (kk 0 : ℤ) ≤ (kk i : ℤ) - (m : ℤ) by omega)
    (show (kk i : ℤ) - (m : ℤ) ≤ (kk i : ℤ) by omega)
  have heq : g₁ + (-(m : ℤ)) • vl + (kk i : ℤ) • vl = g₁ + ((kk i : ℤ) - (m : ℤ)) • vl := by
    rw [sub_smul, neg_smul]; abel
  rw [heq]
  exact hmem

/-- **`rec_p` 的一般形 `p = -(c:ℤ) • vl`，零链外假设。**

逐字是 `ChainDataGeomParts.rec_p`（`ChainPartsFeed.lean:249`）在 `p := -(c:ℤ)•vl` 上的实例，
也是 `chainDataGeomParts_of_chain`（`ItemIIChain.lean:245`）的那条 binder。 -/
theorem rec_p_free_smul (η xper : Config α) (vl : ℤ × ℤ) (S : Finset (ℤ × ℤ)) (c : ℕ)
    {B A : ℕ → Set (ℤ × ℤ)} {u : ℕ → ℤ × ℤ} {kk : ℕ → ℕ} {g₁ nℓ p : ℤ × ℤ} {cz : ℤ}
    (hp : p = -(c : ℤ) • vl)
    (hperp : dot nℓ vl = 0)
    (maxA : ∀ i, IsMaxEnvIn (EnvOf (↑S : Set (ℤ × ℤ))) (canonA η xper vl B u i) (A i))
    (subBA : ∀ i, B i ⊆ A i)
    (subAB : ∀ i, A i ⊆ B (i + 1))
    (hAfin : ∀ i, (A i).Finite)
    (hII : ItemII B nℓ cz)
    (hg₁cz : dot nℓ g₁ = cz)
    (halign : ∀ i, IsGreatest
      {t : ℤ | g₁ + t • vl ∈ hatOf A kk vl i ∧ dot nℓ (g₁ + t • vl) = cz} 0)
    (AhatMono : ∀ i j, i ≤ j → hatOf A kk vl i ⊆ hatOf A kk vl j) :
    ∀ g ∈ ⋃ i, hatOf A kk vl i, g + p ∈ ⋃ i, hatOf A kk vl i := by
  have hfin : ∀ i, (hatOf A kk vl i).Finite := fun i => by
    rw [hatOf_eq_shift]; exact Nivat.AhatMono.finite_shift (hAfin i)
  refine Nivat.Colle35.rec_of_ray
    (latticeConvex_iUnion_hatOf η xper vl S (EnvOf (↑S : Set (ℤ × ℤ))) B A u kk rfl
      maxA hfin AhatMono) (z₀ := g₁) (d := p) ?_
  intro k
  have h := ray_neg_vl η xper vl S hperp maxA subBA subAB hII hg₁cz halign (k * c)
  have heq : g₁ + (k : ℤ) • p = g₁ + (-((k * c : ℕ) : ℤ)) • vl := by
    rw [hp]
    push_cast
    rw [smul_smul]
    ring_nf
  rw [heq]
  exact h

end Nivat.LaneLeafAGenRecP

#print axioms Nivat.LaneLeafAGenRecP.rec_p_of_chain_fields
#print axioms Nivat.LaneLeafAGenRecP.rec_p_of_chain_fields_itemII
#print axioms Nivat.LaneLeafAGenRecP.hg₁_reach_of_isGreatest
#print axioms Nivat.LaneLeafAGenRecP.hkk_max_of_isGreatest
#print axioms Nivat.LaneLeafAGenRecP.rec_p_of_normalised_output
#print axioms Nivat.LaneLeafAGenRecP.rec_p_free
#print axioms Nivat.LaneLeafAGenRecP.ray_neg_vl
#print axioms Nivat.LaneLeafAGenRecP.rec_p_free_smul
