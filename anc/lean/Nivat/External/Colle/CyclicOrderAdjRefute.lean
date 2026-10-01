/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.NormalCycle

/-!
# ⛔ `hadj : det vJ vJ1 = ±1` **不是** `b3_colle2.txt:424` 的推论（lane-env-refute，内核反例）

## §0 被否掉的是哪一句

team-lead 第 228 轮派工的理由原话是「**`E ↑𝒮_φ` 的相邻边法向在环序里是 unimodular 的**」。
本文件在**正是那张表**上给出内核反例：存在一条 `NormalCycle N 3 1`（`:424` 的逐字转录，
`NormalCycle.lean:172`）与一个下标 `k`，使得

* `nprevJ := ν_k` 与 `nJ := ν_{k+1}` 在环序里**真的相邻**（`step` 给 `0 < det`，
  `hnoArc` 给「两者之间没有第三条边法向」——这正是链上 `Arc nprevJ nJ = ∅` 的环序对应物）；
* `vJ := dir nJ`、`vJ1 := -(dir nprevJ)` 满足链上 `hadj` 周围的**全部**前提：
  `Primitive nJ`、`Primitive vJ`、`Primitive vJ1`、`dot nJ vJ = 0`、`dot nJ vJ1 < 0`；
* 而 `det vJ vJ1 = 2`。

⟹ **`hadj` 在 `:424` 这张表上为假。** 它若为真，理由必须来自 `:424` **之外**。

## §1 被否的是哪一版签名，带了哪些前提（PROTOCOL §11 / 纪律 7）

被否的命题逐字是 `Nivat.TowerHbase.unit_sweep_of_adjacent`（`TowerHbaseUnitSweep.lean`）
的那个 `hadj` 形参：

```
hadj : det vJ vJ1 = 1 ∨ det vJ vJ1 = -1
```

本文件的见证**带全了**约束目标中各对象的前提，而且**比链上要求的更多**：

| 前提 | 链上出处 | 本见证 |
|---|---|---|
| `Primitive nJ` | 字段 `nJ_prim`（`ChainPartsFeed.lean:286`） | ✅ `(-2,1)` |
| `Primitive vJ` | 字段 `vJ_prim`（`ChainPartsFeed.lean:285`） | ✅ `(-1,-2)` |
| `dot nJ vJ = 0` | `FaceBlock.dot_nJ_vJ`（`ANormal.lean:616`） | ✅ |
| `dot nJ vJ1 < 0` | 字段 `hsweep`（`ChainPartsFeed.lean:218`） | ✅ `= -2` |
| `nprevJ`/`nJ` 环序相邻 | `Arc nprevJ nJ = ∅`（`DNonnegWindow.lean:54`） | ✅ `hnoArc` |
| `Primitive vJ1` | **Lean 字段表里没有这条**（见下） | ✅ 仍然满足 |
| `vJ1 = ±dir nprevJ` | **链上没有这条**（`vJ1` 是自由字段，只受 `hsweep` 约束） | ✅ 仍然满足 |

最后两行是**额外**满足的：链上的 `vJ1` 比这里更自由，所以反例只会更容易，不会更难。

⚠ **2026-09-25 补正（`Primitive vJ1` 那一行）**：说「链上没有这条」只对 **Lean 字段表**成立 ——
`ChainDataGeomParts` 只有 `vJ_prim` 与 `nJ_prim`，`vJ1` 是裸数据、唯一约束是 `hsweep`。
但 `TowerHbaseUnitSweep.lean` 的模块注释记原文 `b3_colle2.txt:351` 把 `v⃗_ℓ` 定成
「平行于 `ℓ` 且模最小的非零向量」⟹ **原文供得出 `Primitive vJ1`**，补成字段是合法的
（该原文读数为 lane-tower-hbase 所报，我未复核）。⟹ 不许把这一行读成「这条永远拿不到」。
⭐ 对本文件的反例无影响：本见证的 `vJ1 := -(dir nprevJ)` **本来就本原**，所以补不补该字段，
`hadj` 在 `:424` 这张表上照样为假。同一结论的另一处见证见 `EnvRefuteFaceNormal.lean` 的
`unit_dot_nJ_vl_not_of_face_binders_prim`（把 `Primitive vJ1` 直接写进前提）。

⚠ **本反例不为空真**：`adj_premises_hold` 把七条前提逐条内核判定，没有一条是靠假前提过关的。

## §2 这不是 `m = 2` 的退化

`adjHexN` 是一个**中心对称格六边形**的边法向集，`m = 3`（`adjHexCycle.hm` 给 `2 ≤ 3`）。
`m = 2` 那条退化线（正方形，`CyclicOrderDPos.lean` §3 记的 `D = 0`）在这里不适用：
本环上 `0 < D` 处处成立（`NormalCycle.D_pos`，`3 ≤ m`）。⟹ 不能用「排掉 `m = 2`」来救 `hadj`。

## §3 这个六边形不是人造的：它是一个合法 `𝒮_φ` 的形状

中心对称格六边形恒为三条线段的 Minkowski 和（zonotope）。本例的三条生成元可取
`h = (0,1), (1,0), (1,2)`：三条都非零、两两不平行，正是 `DecompData` 的
`h_ne` / `h_dir`（`DecompData.lean:104`）所要求的全部。它们的 `genPerp'` 就是
`adjHexN` 的三对 ±（`adj_generators_nondegenerate` 只把「非零 ＋ 两两不平行」内核判定；
⚠ **本文件不构造 `DecompData`，也不主张 `E ↑𝒮_φ = adjHexN`**——那要过 `zonoF`，
不在本文件射程内，写成主张就是比原文强）。

## §4 后果（要读的就是这两条）

1. ⛔ **`hadj` 不能从环序派工。** 谁要证它，必须指出 `:424` 之外的那条前提是什么、原文哪一行。
2. ⭐ **与 hbase 的 `unit_sweep_iff_unimodular` 完全一致，不是冲突。** 那条说
   `dot nJ vJ1 = -1 ↔ det vJ vJ1 = ±1`（`TowerHbaseUnitSweep.lean:163`）。本例两边同时为假：
   `dot nJ vJ1 = -2` 且 `det vJ vJ1 = 2`。⟹ 「步长债 = 相邻性债」这个等价**成立**，
   本文件否掉的是**那个共同的值**，不是那条等价。
   ⟹ 顺带：`dot nJ vJ1 = -1` 同样不是 `:424` 的推论。

## §5 来源与授权

六边形台架逐字复制自 `tmp/wip/lane-env-refute-hexcycle.lean`（本 lane 自己第 179 轮的文件，
`hex6N` / `hex6Base` / `hex6Cycle`）。`tmp/wip/` 不在模块路径上、不能 `import`，故照 `PROTOCOL §16`
**复制**并改名（`adjHex*`，避开盲区 2 的撞名）。原文件不动（纪律 33）。
-/

set_option autoImplicit false

namespace Nivat.CyclicOrderAdjRefute

open Nivat Nivat.LE2 Nivat.LaneTowerHlevNormalCycle

/-! ## §6  台架：中心对称格六边形的边法向环，`m = 3` -/

/-- 六条边法向。 -/
def adjHexN : Set (ℤ × ℤ) :=
  {((1 : ℤ), (0 : ℤ)), ((0 : ℤ), (1 : ℤ)), ((-2 : ℤ), (1 : ℤ)),
   ((-1 : ℤ), (0 : ℤ)), ((0 : ℤ), (-1 : ℤ)), ((2 : ℤ), (-1 : ℤ))}

/-- 逆时针一个周期。 -/
def adjHexBase : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | 1 => (0, 1)
  | 2 => (-2, 1)
  | 3 => (-1, 0)
  | 4 => (0, -1)
  | 5 => (2, -1)
  | _ => (1, 0)

def adjHexCcw (k : ℕ) : ℤ × ℤ := adjHexBase (k % 6)

theorem adjHex_mod6_add (k s : ℕ) (hs : s < 6) : (k + s) % 6 = (k % 6 + s) % 6 := by
  rw [Nat.add_mod, Nat.mod_eq_of_lt hs]

theorem adjHex_mod6_lt (k : ℕ) : k % 6 < 6 := Nat.mod_lt _ (by norm_num)

/-- ⭐ **台架本体**：八个字段全部内核判定，`m = 3`、`σ = 1`。 -/
def adjHexCycle : NormalCycle adjHexN 3 1 where
  hm := by norm_num
  hsigma := Or.inl rfl
  nu := adjHexCcw
  mem := by
    intro k
    have key : ∀ r : ℕ, r < 6 → adjHexBase r ∈ adjHexN := by
      intro r hr
      interval_cases r <;>
        simp only [adjHexBase, adjHexN, Set.mem_insert_iff, Set.mem_singleton_iff] <;> norm_num
    exact key _ (adjHex_mod6_lt k)
  ne_zero := by
    intro k
    have key : ∀ r : ℕ, r < 6 → adjHexBase r ≠ 0 := by
      intro r hr; interval_cases r <;> decide
    exact key _ (adjHex_mod6_lt k)
  anti := by
    intro k
    have key : ∀ r : ℕ, r < 6 → adjHexBase ((r + 3) % 6) = -(adjHexBase r) := by
      intro r hr; interval_cases r <;> decide
    simp only [adjHexCcw, adjHex_mod6_add k 3 (by norm_num)]
    exact key _ (adjHex_mod6_lt k)
  step := by
    intro k
    have key : ∀ r : ℕ, r < 6 → 0 < (1 : ℤ) * det (adjHexBase r) (adjHexBase ((r + 1) % 6)) := by
      intro r hr; interval_cases r <;> decide
    simp only [adjHexCcw, adjHex_mod6_add k 1 (by norm_num)]
    exact key _ (adjHex_mod6_lt k)
  hnoArc := by
    intro k y hy
    have key : ∀ r : ℕ, r < 6 → ∀ z ∈ adjHexN,
        ¬ (0 < (1 : ℤ) * det (adjHexBase r) z ∧
           0 < (1 : ℤ) * det z (adjHexBase ((r + 1) % 6))) := by
      intro r hr z hz
      simp only [adjHexN, Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      interval_cases r <;>
        rcases hz with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    simp only [adjHexCcw, adjHex_mod6_add k 1 (by norm_num)]
    exact key _ (adjHex_mod6_lt k) y hy
  indep := by
    intro k s hs1 hs3
    have key : ∀ r : ℕ, r < 6 → ∀ t : ℕ, 1 ≤ t → t < 3 →
        det (adjHexBase r) (adjHexBase ((r + t) % 6)) ≠ 0 := by
      intro r hr t ht1 ht3
      interval_cases r <;> interval_cases t <;> decide
    simp only [adjHexCcw, adjHex_mod6_add k s (by omega)]
    exact key _ (adjHex_mod6_lt k) s hs1 hs3

/-! ## §7  见证点：`k = 1` 处的相邻法向对 -/

/-- `ν_1`，扮演链上的 `ν_{J-1}`（`nprevJ`）。 -/
def adjNprev : ℤ × ℤ := (0, 1)

/-- `ν_2`，扮演链上的 `ν_J`（`nJ`）。 -/
def adjNJ : ℤ × ℤ := (-2, 1)

/-- `v_{ℓ_J} = dir ν_J`。 -/
def adjVJ : ℤ × ℤ := (-1, -2)

/-- `v_{ℓ_{J-1}} = -(dir ν_{J-1})`；取负号是为了满足 `hsweep : dot nJ vJ1 < 0`
（另一支 `+dir ν_{J-1}` 给 `dot = +2 > 0`，不合链上的扫向）。 -/
def adjVJ1 : ℤ × ℤ := (1, 0)

theorem adj_nu_one : adjHexCycle.nu 1 = adjNprev := rfl

theorem adj_nu_two : adjHexCycle.nu 2 = adjNJ := rfl

theorem adj_vJ_eq_dir : adjVJ = dir adjNJ := rfl

theorem adj_vJ1_eq_neg_dir : adjVJ1 = -(dir adjNprev) := rfl

/-- **相邻性**：`ν_1` 与 `ν_2` 之间没有第三条边法向。这是链上 `Arc nprevJ nJ = ∅`
在 `:424` 环序里的对应物，由台架的 `hnoArc` 字段直接给出。 -/
theorem adj_no_edge_between :
    ∀ y ∈ adjHexN, ¬ (0 < det adjNprev y ∧ 0 < det y adjNJ) := by
  intro y hy
  have h := adjHexCycle.hnoArc 1 y hy
  simpa [adj_nu_one, adj_nu_two, one_mul] using h

/-- 相邻法向对的行列式是 `2`，不是 `1`。 -/
theorem adj_e_eq_two : det adjNprev adjNJ = 2 := by decide

/-- ⭐ **结论的数值形**：`det vJ vJ1 = 2`。 -/
theorem adj_det_vJ_vJ1 : det adjVJ adjVJ1 = 2 := by decide

/-- 步长同步失败：`dot nJ vJ1 = -2`，不是 `-1`。与 `adj_det_vJ_vJ1` 一起，
逐字印证 hbase 的 `unit_sweep_iff_unimodular`（两边同时为假）。 -/
theorem adj_dot_nJ_vJ1 : dot adjNJ adjVJ1 = -2 := by decide

/-! ## §8  七条前提逐条内核判定（非空真） -/

/-- ⚠ **非空真**：约束目标中各对象的前提**全部成立**，被否掉的只有结论。 -/
theorem adj_premises_hold :
    Primitive adjNJ ∧ Primitive adjVJ ∧ Primitive adjVJ1 ∧
    dot adjNJ adjVJ = 0 ∧ dot adjNJ adjVJ1 < 0 ∧
    0 < det adjNprev adjNJ ∧
    (∀ y ∈ adjHexN, ¬ (0 < det adjNprev y ∧ 0 < det y adjNJ)) := by
  refine ⟨prim_iff_primitive.mp (by decide), prim_iff_primitive.mp (by decide),
    prim_iff_primitive.mp (by decide), by decide, by decide, by decide, adj_no_edge_between⟩

/-! ## §9  否定形 -/

/-- ⛔ **`hadj` 不是 `:424` 的推论。**  存在形：一条 `NormalCycle`、一个下标、一组满足
链上全部前提的 `(nJ, vJ, vJ1)`，而 `det vJ vJ1 ∉ {1, -1}`。 -/
theorem exists_adjacent_pair_not_unimodular :
    ∃ (N : Set (ℤ × ℤ)) (C : NormalCycle N 3 1) (k : ℕ) (nprevJ nJ vJ vJ1 : ℤ × ℤ),
      nprevJ = C.nu k ∧ nJ = C.nu (k + 1) ∧
      Primitive nJ ∧ Primitive vJ ∧ Primitive vJ1 ∧
      dot nJ vJ = 0 ∧ dot nJ vJ1 < 0 ∧
      vJ = dir nJ ∧ vJ1 = -(dir nprevJ) ∧
      (∀ y ∈ N, ¬ (0 < det nprevJ y ∧ 0 < det y nJ)) ∧
      ¬ (det vJ vJ1 = 1 ∨ det vJ vJ1 = -1) := by
  refine ⟨adjHexN, adjHexCycle, 1, adjNprev, adjNJ, adjVJ, adjVJ1,
    adj_nu_one.symm, adj_nu_two.symm,
    prim_iff_primitive.mp (by decide), prim_iff_primitive.mp (by decide),
    prim_iff_primitive.mp (by decide),
    by decide, by decide, adj_vJ_eq_dir, adj_vJ1_eq_neg_dir, adj_no_edge_between, ?_⟩
  rw [adj_det_vJ_vJ1]
  rintro (h | h) <;> omega

/-- ⛔ **可引用的否定形**：没有任何只吃「环序 ＋ 链上 `hadj` 周边前提」的定理能给出 `hadj`。 -/
theorem hadj_not_from_cyclic_order :
    ¬ (∀ (N : Set (ℤ × ℤ)) (C : NormalCycle N 3 1) (k : ℕ) (nprevJ nJ vJ vJ1 : ℤ × ℤ),
        nprevJ = C.nu k → nJ = C.nu (k + 1) →
        Primitive nJ → Primitive vJ → Primitive vJ1 →
        dot nJ vJ = 0 → dot nJ vJ1 < 0 →
        vJ = dir nJ → vJ1 = -(dir nprevJ) →
        (∀ y ∈ N, ¬ (0 < det nprevJ y ∧ 0 < det y nJ)) →
        (det vJ vJ1 = 1 ∨ det vJ vJ1 = -1)) := by
  intro h
  have := h adjHexN adjHexCycle 1 adjNprev adjNJ adjVJ adjVJ1
    adj_nu_one.symm adj_nu_two.symm
    (prim_iff_primitive.mp (by decide)) (prim_iff_primitive.mp (by decide))
    (prim_iff_primitive.mp (by decide))
    (by decide) (by decide) adj_vJ_eq_dir adj_vJ1_eq_neg_dir adj_no_edge_between
  rw [adj_det_vJ_vJ1] at this
  rcases this with h1 | h1 <;> omega

/-- ⛔ **步长形的同一条**：`dot nJ vJ1 = -1` 同样不是 `:424` 的推论。 -/
theorem unit_sweep_not_from_cyclic_order :
    ¬ (∀ (N : Set (ℤ × ℤ)) (C : NormalCycle N 3 1) (k : ℕ) (nprevJ nJ vJ vJ1 : ℤ × ℤ),
        nprevJ = C.nu k → nJ = C.nu (k + 1) →
        Primitive nJ → Primitive vJ → Primitive vJ1 →
        dot nJ vJ = 0 → dot nJ vJ1 < 0 →
        vJ = dir nJ → vJ1 = -(dir nprevJ) →
        (∀ y ∈ N, ¬ (0 < det nprevJ y ∧ 0 < det y nJ)) →
        dot nJ vJ1 = -1) := by
  intro h
  have := h adjHexN adjHexCycle 1 adjNprev adjNJ adjVJ adjVJ1
    adj_nu_one.symm adj_nu_two.symm
    (prim_iff_primitive.mp (by decide)) (prim_iff_primitive.mp (by decide))
    (prim_iff_primitive.mp (by decide))
    (by decide) (by decide) adj_vJ_eq_dir adj_vJ1_eq_neg_dir adj_no_edge_between
  rw [adj_dot_nJ_vJ1] at this
  omega

/-! ## §10  这不是 `m = 2` 的退化 -/

/-- `0 < D` 在本环上处处成立（`3 ≤ m`），故不能用「排掉 `m = 2`」来救 `hadj`。 -/
theorem adj_D_pos (k : ℕ) : 0 < det (adjHexCycle.nu k) (adjHexCycle.nu (k + 2)) := by
  have h := NormalCycle.D_pos adjHexCycle (by norm_num) k
  simpa using h

/-! ## §11  生成元侧的非退化（§3 的内核部分） -/

/-- 三条生成元 `(0,1)`、`(1,0)`、`(1,2)` 非零、两两不平行——即 `DecompData` 的
`h_ne` / `h_dir` 所要求的全部。⚠ 本条**不**主张 `E ↑𝒮_φ = adjHexN`。 -/
theorem adj_generators_nondegenerate :
    ((0 : ℤ), (1 : ℤ)) ≠ 0 ∧ ((1 : ℤ), (0 : ℤ)) ≠ 0 ∧ ((1 : ℤ), (2 : ℤ)) ≠ 0 ∧
    det ((0 : ℤ), (1 : ℤ)) ((1 : ℤ), (0 : ℤ)) ≠ 0 ∧
    det ((0 : ℤ), (1 : ℤ)) ((1 : ℤ), (2 : ℤ)) ≠ 0 ∧
    det ((1 : ℤ), (0 : ℤ)) ((1 : ℤ), (2 : ℤ)) ≠ 0 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

end Nivat.CyclicOrderAdjRefute

#print axioms Nivat.CyclicOrderAdjRefute.adjHexN
#print axioms Nivat.CyclicOrderAdjRefute.adjHexBase
#print axioms Nivat.CyclicOrderAdjRefute.adjHexCcw
#print axioms Nivat.CyclicOrderAdjRefute.adjHex_mod6_add
#print axioms Nivat.CyclicOrderAdjRefute.adjHex_mod6_lt
#print axioms Nivat.CyclicOrderAdjRefute.adjHexCycle
#print axioms Nivat.CyclicOrderAdjRefute.adjNprev
#print axioms Nivat.CyclicOrderAdjRefute.adjNJ
#print axioms Nivat.CyclicOrderAdjRefute.adjVJ
#print axioms Nivat.CyclicOrderAdjRefute.adjVJ1
#print axioms Nivat.CyclicOrderAdjRefute.adj_nu_one
#print axioms Nivat.CyclicOrderAdjRefute.adj_nu_two
#print axioms Nivat.CyclicOrderAdjRefute.adj_vJ_eq_dir
#print axioms Nivat.CyclicOrderAdjRefute.adj_vJ1_eq_neg_dir
#print axioms Nivat.CyclicOrderAdjRefute.adj_no_edge_between
#print axioms Nivat.CyclicOrderAdjRefute.adj_e_eq_two
#print axioms Nivat.CyclicOrderAdjRefute.adj_det_vJ_vJ1
#print axioms Nivat.CyclicOrderAdjRefute.adj_dot_nJ_vJ1
#print axioms Nivat.CyclicOrderAdjRefute.adj_premises_hold
#print axioms Nivat.CyclicOrderAdjRefute.exists_adjacent_pair_not_unimodular
#print axioms Nivat.CyclicOrderAdjRefute.hadj_not_from_cyclic_order
#print axioms Nivat.CyclicOrderAdjRefute.unit_sweep_not_from_cyclic_order
#print axioms Nivat.CyclicOrderAdjRefute.adj_D_pos
#print axioms Nivat.CyclicOrderAdjRefute.adj_generators_nondegenerate
