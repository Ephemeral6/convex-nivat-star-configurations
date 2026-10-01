/-
Copyright (c) 2026. Released under Apache 2.0 license.
Authors: lane-tower-hlev
-/
import Nivat.External.Colle.RecVJ
import Nivat.External.Colle.ChainKK

/-!
# `hkk` is false on the normalised chain

派工：集成者 2026-09-25，「`hbox` + `hkk` 是 `bottom` 合取 1 绕环的唯一剩余候选，先做可行性判定」。

## 一名两物（`CLAUDE.md` 硬规矩 8 / `PROTOCOL §97`）

短名 `hkk` 在仓里承载两个命题（lane-tower-hbase 在 `tmp/wip/hbase_hkk.lean` 的模块 docstring
里先钉的，本文件沿用他的记号）：

* **(α) `kk` 单调**：`∀ i j, i ≤ j → kk i ≤ kk j`。它是 `AhatMono` 那一侧要的。
* **(β) 盒穷竭**：`∀ z, ∃ i, |(z + kk (i+1) • vl).1| ≤ i ∧ |(z + kk (i+1) • vl).2| ≤ i`。
  全树只有 `iUnion_hatOf_eq_halfPlane` 与 `rec_vJ_of_halfPlane`（皆在 `RecVJ.lean`）拿它当 binder。

**本文件只讲 (β)。**

## 结论

`not_hkk_of_chain`：只要链同时给出

1. `hperp : dot nℓ vl = 0`、`hvl : vl ≠ 0`（`exists_normalised_chain` 的自有 binder）；
2. `ItemII B nℓ cz`（`exists_normalised_chain` 输出的第 8 合取，即盒吸收）；
3. `subBA : ∀ i, B i ⊆ A i`（第 5 合取）；
4. `hg₁ : dot nℓ g₁ = cz`（第 11 合取）与 `hpin`（第 12 合取，`IsGreatest … 0` 归一化），

**(β) 就为假**。

⟹ `iUnion_hatOf_eq_halfPlane` / `rec_vJ_of_halfPlane` 的前提集在链上**互相矛盾**，
这两条在链上**空真**，不是 `rec_vJ` 的产者。

## 为什么（一句话）

盒吸收把 `A i` 的 `cz`-层面沿 `+vl` 顶到距原点 `≈ i` 处；归一化 `IsGreatest … 0` 要求
`g₁` 正是 `hatOf A kk vl i` 在那一层沿 `vl` 的**最大**点 ⟹ 平移量 `kk i` 必须**线性增长**
（`kk_ge_of_itemII`）。而 (β) 逐字是 `kk` 的**次线性上界**（hbase 的 `hkk_necessary_of_axis`
已把这一点从反方向钉住）。两者对撞。取 `z := (supN g₁ + supN vl + 1) • vl` 即得矛盾。

## 鉴别力（`PROTOCOL §84`）

分母 = 本定理的 5 条前提。`premises_minus_hpin_satisfiable` 给出一个模型
（`A = B = ℋ`、`kk ≡ 0`、`nℓ = (0,1)`、`vl = (1,0)`）使 `hperp`/`ItemII`/`subBA`/(β) **同时成立**
⟹ 去掉 `hpin` 后本定理为假 ⟹ `hpin` 是承重的那一条，杀死 (β) 的是**归一化**，不是盒吸收。
（推论：该模型必然不满足 `hpin`——否则与 `not_hkk_of_chain` 直接矛盾。这一步不另证。）

⚠ 未主张（`PROTOCOL §85`）：本文件**不**说 `⋃ hatOf A kk vl i` 是什么，只说它不是
`iUnion_hatOf_eq_halfPlane` 用 (β) 推出来的那个半平面。`b3_colle2.txt:506` 把 `Â_∞` 说成
带两条半无限边的 `(ℓ,ℓ_J)`-region，与半平面的落差归 lane-leafa-shell，本文件不裁。

## 原文锚

`kk` 是 `b3_colle2.txt:488` 的 `k_i`；盒吸收是 `:474`/`:476`；`:506` 是 `Â_∞` 的形状。
(β) 本身**在原文里没有对应句**（`RecVJ.lean` 的 `iUnion_hatOf_eq_halfPlane` docstring
自称 honest residual）——按硬规矩 5，它是我们加的量词，现在它被链上的其它量词否掉。
-/

set_option autoImplicit false

open Nivat.LE2 Nivat.Colle35

namespace Nivat.LaneTowerHlevHkk

/-! ## §1. sup-范数与两条纯算术引理 -/

/-- 整点的 sup-范数（自然数值）。 -/
def supN (z : ℤ × ℤ) : ℕ := max z.1.natAbs z.2.natAbs

theorem natAbs_fst_le_supN (z : ℤ × ℤ) : z.1.natAbs ≤ supN z := le_max_left _ _

theorem natAbs_snd_le_supN (z : ℤ × ℤ) : z.2.natAbs ≤ supN z := le_max_right _ _

theorem one_le_supN {z : ℤ × ℤ} (h : z ≠ 0) : 1 ≤ supN z := by
  by_contra hc
  have h0 : supN z = 0 := by omega
  have h1 : z.1.natAbs ≤ 0 := h0 ▸ natAbs_fst_le_supN z
  have h2 : z.2.natAbs ≤ 0 := h0 ▸ natAbs_snd_le_supN z
  have e1 : z.1 = 0 := Int.natAbs_eq_zero.mp (by omega)
  have e2 : z.2 = 0 := Int.natAbs_eq_zero.mp (by omega)
  exact h (Prod.ext_iff.mpr ⟨e1, e2⟩)

/-- 展开 `(z + (k : ℤ) • vl).1`。 -/
theorem fst_add_zsmul (z vl : ℤ × ℤ) (k : ℤ) :
    (z + k • vl).1 = z.1 + k * vl.1 := by
  simp [Prod.fst_add]

/-- 展开 `(z + (k : ℤ) • vl).2`。 -/
theorem snd_add_zsmul (z vl : ℤ × ℤ) (k : ℤ) :
    (z + k • vl).2 = z.2 + k * vl.2 := by
  simp [Prod.snd_add]

/-- 展开 `(k • z).1`。 -/
theorem fst_zsmul (z : ℤ × ℤ) (k : ℤ) : (k • z).1 = k * z.1 := by simp

/-- 展开 `(k • z).2`。 -/
theorem snd_zsmul (z : ℤ × ℤ) (k : ℤ) : (k • z).2 = k * z.2 := by simp

/-- 单坐标的三角不等式，落到 `ItemII` 的盒界 `≤ (i : ℤ) - 1`。 -/
theorem abs_add_mul_le {x y : ℤ} {m b i k : ℕ}
    (hx : x.natAbs ≤ m) (hy : y.natAbs ≤ b) (hi : m + k * b + 1 ≤ i) :
    |x + (k : ℤ) * y| ≤ (i : ℤ) - 1 := by
  have hxa : |x| ≤ (m : ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast hx
  have hya : |y| ≤ (b : ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast hy
  have hiz : (m : ℤ) + (k : ℤ) * (b : ℤ) + 1 ≤ (i : ℤ) := by exact_mod_cast hi
  have hk : (0 : ℤ) ≤ (k : ℤ) := Int.natCast_nonneg k
  obtain ⟨hx1, hx2⟩ := abs_le.mp hxa
  obtain ⟨hy1, hy2⟩ := abs_le.mp hya
  rw [abs_le]
  constructor <;> nlinarith [hk, hx1, hx2, hy1, hy2, hiz]

/-- 从 `|k * y| ≤ i`（`k` 是自然数的 cast）读出 `k * |y| ≤ i`。 -/
theorem natAbs_mul_le_of_abs {k i : ℕ} {y : ℤ} (h : |(k : ℤ) * y| ≤ (i : ℤ)) :
    k * y.natAbs ≤ i := by
  have hz : ((k * y.natAbs : ℕ) : ℤ) ≤ (i : ℤ) := by
    have he : ((k * y.natAbs : ℕ) : ℤ) = |(k : ℤ) * y| := by
      rw [abs_mul, abs_of_nonneg (Int.natCast_nonneg k), Int.abs_eq_natAbs]
      push_cast
      ring
    rw [he]
    exact h
  exact_mod_cast hz

/-- 两个坐标的界合成 sup-范数的界。 -/
theorem mul_supN_le {k i : ℕ} {y : ℤ × ℤ}
    (h1 : k * y.1.natAbs ≤ i) (h2 : k * y.2.natAbs ≤ i) : k * supN y ≤ i := by
  rcases le_total y.1.natAbs y.2.natAbs with h | h
  · rw [supN, max_eq_right h]; exact h2
  · rw [supN, max_eq_left h]; exact h1

/-! ## §2. ⭐ 盒吸收 ＋ 归一化 ⟹ `kk` 线性增长 -/

/-- **`kk` 的线性下界。**

`ItemII` 把 `g₁ + s • vl` 放进 `B i`（只要它落在半径 `i - 1` 的盒里），`subBA` 把它送进 `A i`；
于是 `t := s - kk i` 属于 `hpin` 的那个集合，`IsGreatest … 0` 立刻给 `t ≤ 0`。

原文：`b3_colle2.txt:474`（盒吸收）+ `:488`（`k_i`）。 -/
theorem kk_ge_of_itemII {A B : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ} {vl nℓ g₁ : ℤ × ℤ} {cz : ℤ}
    (hperp : dot nℓ vl = 0)
    (hII : ItemII B nℓ cz)
    (subBA : ∀ i, B i ⊆ A i)
    (hg₁ : dot nℓ g₁ = cz)
    (hpin : ∀ i, IsGreatest {t : ℤ | g₁ + t • vl ∈ hatOf A kk vl i ∧
      dot nℓ (g₁ + t • vl) = cz} 0)
    (i s : ℕ) (hi : supN g₁ + s * supN vl + 1 ≤ i) :
    s ≤ kk i := by
  have hdot : ∀ t : ℤ, dot nℓ (g₁ + t • vl) = cz :=
    fun t => (Colle35.dot_add_zsmul_of_perp hperp g₁ t).trans hg₁
  have hmem : g₁ + (s : ℤ) • vl ∈ A i := by
    refine subBA i (hII i _ ?_ ?_ (hdot (s : ℤ)).ge)
    · rw [fst_add_zsmul]
      exact abs_add_mul_le (natAbs_fst_le_supN g₁) (natAbs_fst_le_supN vl) hi
    · rw [snd_add_zsmul]
      exact abs_add_mul_le (natAbs_snd_le_supN g₁) (natAbs_snd_le_supN vl) hi
  have ht : ((s : ℤ) - (kk i : ℤ)) ∈
      {t : ℤ | g₁ + t • vl ∈ hatOf A kk vl i ∧ dot nℓ (g₁ + t • vl) = cz} := by
    refine ⟨?_, hdot _⟩
    rw [Nivat.RecVJ.mem_hatOf_iff]
    have hrw : g₁ + ((s : ℤ) - (kk i : ℤ)) • vl + (kk i : ℤ) • vl = g₁ + (s : ℤ) • vl := by
      rw [add_assoc, ← add_smul]; ring_nf
    rw [hrw]
    exact hmem
  have hle : (s : ℤ) - (kk i : ℤ) ≤ 0 := (hpin i).2 ht
  omega

/-! ## §3. ⭐ 主结论：(β) 在链上为假 -/

/-- **(β) 与链上的盒吸收 ＋ 归一化不相容。**

取 `z := (supN g₁ + supN vl + 1) • vl`。(β) 给出某个 `i` 使 `(N + kk (i+1)) * supN vl ≤ i`；
`kk_ge_of_itemII` 在 `s := kk (i+1) + 1` 上给出 `kk (i+1) + 1 ≤ kk (i+1)`。

⟹ `RecVJ.iUnion_hatOf_eq_halfPlane` 与 `RecVJ.rec_vJ_of_halfPlane` 在链上前件为假。 -/
theorem not_hkk_of_chain {A B : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ} {vl nℓ g₁ : ℤ × ℤ} {cz : ℤ}
    (hperp : dot nℓ vl = 0) (hvl : vl ≠ 0)
    (hII : ItemII B nℓ cz)
    (subBA : ∀ i, B i ⊆ A i)
    (hg₁ : dot nℓ g₁ = cz)
    (hpin : ∀ i, IsGreatest {t : ℤ | g₁ + t • vl ∈ hatOf A kk vl i ∧
      dot nℓ (g₁ + t • vl) = cz} 0) :
    ¬ (∀ z : ℤ × ℤ, ∃ i : ℕ,
        |(z + (kk (i + 1) : ℤ) • vl).1| ≤ (i : ℤ) ∧
        |(z + (kk (i + 1) : ℤ) • vl).2| ≤ (i : ℤ)) := by
  intro hkk
  have hb : 1 ≤ supN vl := one_le_supN hvl
  set M : ℕ := supN g₁ with hM
  set b : ℕ := supN vl with hbdef
  set N : ℕ := M + b + 1 with hN
  obtain ⟨i, h1, h2⟩ := hkk ((N : ℤ) • vl)
  set K : ℕ := kk (i + 1) with hK
  -- the two coordinate bounds, rewritten as `(N + K) * |vl.j| ≤ i`
  rw [fst_add_zsmul, fst_zsmul] at h1
  rw [snd_add_zsmul, snd_zsmul] at h2
  have hcast : (((N + K : ℕ)) : ℤ) = (N : ℤ) + (K : ℤ) := by push_cast; ring
  have g1 : |((N + K : ℕ) : ℤ) * vl.1| ≤ (i : ℤ) := by rw [hcast, add_mul]; exact h1
  have g2 : |((N + K : ℕ) : ℤ) * vl.2| ≤ (i : ℤ) := by rw [hcast, add_mul]; exact h2
  have c1 : (N + K) * vl.1.natAbs ≤ i := natAbs_mul_le_of_abs g1
  have c2 : (N + K) * vl.2.natAbs ≤ i := natAbs_mul_le_of_abs g2
  have hc : (N + K) * b ≤ i := mul_supN_le c1 c2
  -- arithmetic: `(M + b + 1 + K) * b ≤ i` gives `M + (K+1) * b + 1 ≤ i + 1`
  have hexp : (N + K) * b = M * b + b * b + b + K * b := by rw [hN]; ring
  have hMb : M ≤ M * b := Nat.le_mul_of_pos_right M hb
  have hbb : b ≤ b * b := Nat.le_mul_of_pos_right b hb
  have hKb : (K + 1) * b = K * b + b := by ring
  have hgoal : M + (K + 1) * b + 1 ≤ i + 1 := by rw [hKb]; linarith [hexp ▸ hc, hMb, hbb]
  have := kk_ge_of_itemII hperp hII subBA hg₁ hpin (i + 1) (K + 1) hgoal
  omega

/-! ## §4. ⭐ 接线见证：直接吃 `exists_normalised_chain` 的输出

（集成者的方法立法：「凡是『我说形状对得上』，都给见证，不给描述」。）
-/

/-- **(β) 在 `exists_normalised_chain` 产出的链上为假**，内核见证。

本条不描述「合取 5/8/11/12 的形状和 `not_hkk_of_chain` 的前提对得上」，而是让内核检查这件事：
`obtain` 的模式逐位对齐 13 条合取，`hperp`/`hvl` 是 `exists_normalised_chain` 自己的 binder。

⟹ `RecVJ.iUnion_hatOf_eq_halfPlane` 与 `RecVJ.rec_vJ_of_halfPlane` 在这条链上**前件为假**，
故它们**不是** `ChainDataGeom.ofParts` 第 25 条前提 `rec_vJ` 的产者。 -/
theorem hkk_false_on_normalised_chain {ξ xper : Config ℤ} {S : Finset (ℤ × ℤ)} {vl nℓ : ℤ × ℤ}
    (cz : ℤ) (hS : LatticeConvex S) (hSne : S.Nonempty)
    (hxper : xper ∈ orbitClosure ξ)
    (hvl : vl ≠ 0) (hvl_prim : Primitive vl)
    (hprim : Primitive nℓ) (hperp : dot nℓ vl = 0)
    (hnℓ' : -nℓ ∈ E (↑S : Set (ℤ × ℤ)))
    {n m : ℤ × ℤ} (hdet : det n m ≠ 0)
    (hn : n ∈ E (↑S : Set (ℤ × ℤ))) (hn' : -n ∈ E (↑S : Set (ℤ × ℤ)))
    (hm : m ∈ E (↑S : Set (ℤ × ℤ))) (hm' : -m ∈ E (↑S : Set (ℤ × ℤ)))
    (hcase2 : Nivat.ColleReg.Case2 ξ xper S vl) :
    ∃ (B A : ℕ → Set (ℤ × ℤ)) (kk : ℕ → ℕ) (g₁ : ℤ × ℤ),
      (∀ i, B i ⊆ A i) ∧ ItemII B nℓ cz ∧ Exhausts A nℓ cz ∧
      (∀ i j, i ≤ j → kk i ≤ kk j) ∧ dot nℓ g₁ = cz ∧
      (∀ i, IsGreatest {t : ℤ | g₁ + t • vl ∈ hatOf A kk vl i ∧
        dot nℓ (g₁ + t • vl) = cz} 0) ∧
      ¬ (∀ z : ℤ × ℤ, ∃ i : ℕ,
          |(z + (kk (i + 1) : ℤ) • vl).1| ≤ (i : ℤ) ∧
          |(z + (kk (i + 1) : ℤ) • vl).2| ≤ (i : ℤ)) := by
  obtain ⟨B, A, -, kk, g₁, -, -, -, -, subBA, -, -, hII, hexh, hmono, hg₁, hpin, -⟩ :=
    Nivat.ChainKK.exists_normalised_chain cz hS hSne hxper hvl hvl_prim hprim hperp hnℓ' hdet
      hn hn' hm hm' hcase2
  exact ⟨B, A, kk, g₁, subBA, hII, hexh, hmono, hg₁, hpin,
    not_hkk_of_chain hperp hvl hII subBA hg₁ hpin⟩

/-! ## §5. 鉴别力见证（`PROTOCOL §84`）：`hpin` 是承重的那一条 -/

/-- 台架的半平面：`nℓ = (0,1)`、`cz = 0`。 -/
def rigHP : Set (ℤ × ℤ) := {z : ℤ × ℤ | (0 : ℤ) ≤ dot ((0 : ℤ), (1 : ℤ)) z}

/-- **去掉 `hpin` 后 `not_hkk_of_chain` 为假。**

`A = B ≡ ℋ`、`kk ≡ 0`、`nℓ = (0,1)`、`vl = (1,0)` 上，`hperp`/`hvl`/`ItemII`/`subBA` 与 (β)
**同时成立** ⟹ `not_hkk_of_chain` 的其余四条前提不足以否掉 (β)，承重的是 `hpin`。

⚠ 未主张：本条**不**证「该模型不满足 `hpin`」——那是 `not_hkk_of_chain` 的直接推论，不另证。 -/
theorem premises_minus_hpin_satisfiable :
    dot ((0 : ℤ), (1 : ℤ)) ((1 : ℤ), (0 : ℤ)) = 0 ∧
    ((1 : ℤ), (0 : ℤ)) ≠ (0 : ℤ × ℤ) ∧
    ItemII (fun _ : ℕ => rigHP) ((0 : ℤ), (1 : ℤ)) 0 ∧
    (∀ i : ℕ, (fun _ : ℕ => rigHP) i ⊆ (fun _ : ℕ => rigHP) i) ∧
    (∀ z : ℤ × ℤ, ∃ i : ℕ,
      |(z + (((fun _ : ℕ => (0 : ℕ)) (i + 1) : ℕ) : ℤ) • ((1 : ℤ), (0 : ℤ))).1| ≤ (i : ℤ) ∧
      |(z + (((fun _ : ℕ => (0 : ℕ)) (i + 1) : ℕ) : ℤ) • ((1 : ℤ), (0 : ℤ))).2| ≤ (i : ℤ)) := by
  refine ⟨by decide, by decide, ?_, fun _ => subset_rfl, ?_⟩
  · intro i z _ _ hz
    exact hz
  · intro z
    refine ⟨supN z, ?_, ?_⟩
    · simp only [Nat.cast_zero, zero_smul, add_zero]
      rw [Int.abs_eq_natAbs]
      exact_mod_cast natAbs_fst_le_supN z
    · simp only [Nat.cast_zero, zero_smul, add_zero]
      rw [Int.abs_eq_natAbs]
      exact_mod_cast natAbs_snd_le_supN z

end Nivat.LaneTowerHlevHkk

#print axioms Nivat.LaneTowerHlevHkk.one_le_supN
#print axioms Nivat.LaneTowerHlevHkk.abs_add_mul_le
#print axioms Nivat.LaneTowerHlevHkk.natAbs_mul_le_of_abs
#print axioms Nivat.LaneTowerHlevHkk.mul_supN_le
#print axioms Nivat.LaneTowerHlevHkk.kk_ge_of_itemII
#print axioms Nivat.LaneTowerHlevHkk.not_hkk_of_chain
#print axioms Nivat.LaneTowerHlevHkk.premises_minus_hpin_satisfiable
#print axioms Nivat.LaneTowerHlevHkk.hkk_false_on_normalised_chain
