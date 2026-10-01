/-
# `lex` 推不出全局 `vJ`-极小：一般形反例（lane-tower-hlev）

**派工逐字**（team-lead，本轮）：「把 (2) 送进内核，一般形，不要台架」，目标形状他逐字给了
（见 `lex_not_imp_global_vJ_min` 的签名，一字未改）。**消费者**：`exists_chainData`
（`RegionSteps.lean`，声明 `exists_chainData`）造 `F` 的那一侧，即集成者本人；它对 populator
是**硬约束**——造 `F` 时不能指望从 `lex` 白拿全局 `vJ`-极小。

## 起源（记账用，不是本文件的证据）

`ChainDataGeomParts.bottom`（`ChainPartsFeed.lean`，字段 `bottom`）的第三＋第四合取在
`tmp/wip/hlev-2d-fields.lean` 的二维台架上反向夹住 `L`，合起来逼出 `∀ b ∈ S, F.a.1 ≤ b.1`，
即 `F.a` 必须是 `S` 的全局 `vJ`-极小点。`FaceBlock.lex`（`ANormal.lean`，结构 `FaceBlock`）
只给「`nJ`-面上的 lex-极小」。台架上两者碰巧重合 ⟹ 那里只看得到「巧合」。
team-lead 用精确整数脚本算出错配**一般存在**并给了见证集；本文件把它送进内核。
⛔ 本文件**不**主张「`bottom` 一般地逼出全局极小」——那条留在台架里，按 §51 无主张。

## 见证集与方向约定

`lexS = {(1,0),(2,0),(0,1),(1,1),(2,1)}`（team-lead 脚本里的 `S1`），`n := (0,1)`、`v := (1,0)`。
它的实凸包是四边形 `(1,0)-(2,0)-(2,1)-(0,1)`，格点恰为这五个（`(0,0)` 被 `1 ≤ x + y` 切掉）。

`FaceBlock.lex`（`ANormal.lean`，结构 `FaceBlock` 的字段 `lex`）逐字是

    ∀ b ∈ S.erase a, dot (-n) b < dot (-n) a ∨ (dot (-n) b = dot (-n) a ∧ dot (-v) b < dot (-v) a)

⟹ `a` 最大化 `dot (-n)` ⟺ **最小化 `dot n`**；`n = (0,1)` 上 `dot n z = z.2` ⟹ `a` 落在
`y` **最小**那条面 `{(1,0),(2,0)}`；并列时 `dot (-v) b < dot (-v) a ⟺ dot v a < dot v b`
⟹ 面上取 `dot v = x` 最小者 ⟹ `a = (1,0)`。
而 `lexS` 上 `dot v` 的**全局**极小是 `0`，在 `(0,1)` 处（那点不在 `y = 0` 面上）。⟹ 错配。

## 四条读数（`PROTOCOL.md §84`：「成立」与「鉴别力」分两行；§71 三条自查）

**一、team-lead 逐字要的那条**：`lex_not_imp_global_vJ_min`。成立。

**二、比他要的强一档 —— 整条 `FaceBlock` 都兑现，不只是 `lex`。**
`lexFB : FaceBlock lexS (0,1) (1,0)` 的 11 个字段全给（`a = (1,0)`、`a' = (2,0)`、`r = 1`），
⟹ `faceBlock_not_imp_global_vJ_min`：结论从「`lex` 不够」升级成「**整个 `FaceBlock` 都不够**」。
这是 team-lead 派工里标「能加分但不必须」的那一格，兑现了，没有卡在任何字段上。

**三、错配对 `a` 的选取不敏感（§71 二：结论鉴别）。**
`faceBlock_a_lexS` 证得**任意** `F : FaceBlock lexS (0,1) (1,0)` 都有 `F.a = (1,0)`
（`a_mem` 五点分情形，每个非 `(1,0)` 的候选都被 `lex` 在 `b = (1,0)` 处当场否掉）⟹
`faceBlock_a_not_global_vJ_min` 对任意 `F` 成立。⛔ 所以这**不是**「我挑了个坏 `a`」。

**四、被否的谓词在这座 `S` 上非空真（§71 三：限定非空）。**
`global_vJ_min_exists_in_lexS`：`∀ b ∈ lexS, dot v (0,1) ≤ dot v b` —— 全局 `vJ`-极小点在
`lexS` 上**存在**（在 `(0,1)`）。⟹「`F.a` 不是它」是真错配，不是谓词整体退化为假。
这一格同时是**反哨兵**：同一个谓词在同一座 `S` 上既有真实例（`(0,1)`）又有假实例（`F.a`），
所以本文件的测试能出负，不是恒假。

## ⛔ 六条不许的读法

1. ⛔ **不是**「`FaceBlock` 的签名错了」。`lex` 从来没号称给全局极小（`ANormal.lean` 结构
   `FaceBlock` 的 `a` 字段 docstring 写的是「The `v`-minimal endpoint of the **face**」，
   辖域词是 **face**）。本文件否的是「从 `lex` 推出全局极小」这个**推理**，不是字段本身。
2. ⛔ **不是**「`bottom` 为假」。`bottom` 在二维台架上成立（`tmp/wip/hlev-2d-fields.lean`）。
   本文件只说 populator 不能从 `lex` 白拿 `bottom` 第三合取要的那个极小性。
3. ⛔ **不是**「链上 `S = d.Sphi` 不是 `lexS` 这类」。`lexS` 不中心对称，链上的 `S` 侧是否
   zonotope 这笔账在别处（lane-tower-hbase 本轮的 `latticeConvex` 筛差额），本文件不碰。
   一般形的 `∃` 不需要 `lexS` 像链上的 `S`——它否的是**蕴含**，反例只要合法就够。
4. ⛔ **不是**链上可满足性见证。`|lexS| = 5`、`m` 无定义，按常设纪律 1（台架至少 `m = 4`）
   与 §90，本文件不产生任何「链上存在」型主张。
5. ⛔ `lexFB` **不是**「链上存在 `FaceBlock`」。它是自由参数 `S n v` 上的一个实例，
   与 `DecompDataZ.exists_faceBlock`（`ANormal.lean`，标识符引）无关。
6. ⛔ 别把读数三记成「`lexS` 上 `FaceBlock` 唯一」。`faceBlock_a_lexS` 只钉 `a`，
   没钉 `a'` / `r` / 其余字段。

## §91 分工（谁已经有过什么）

* `Nivat.TowerHlev2DFields.faceBlock_a_hex`（`tmp/wip/hlev-2d-fields.lean`，同 lane，**不
  import**，`PROTOCOL.md §16`）钉的是 `hexF` 上的 `F.a = (0,0)`，那里全局极小与面上极小
  **重合** ⟹ 看不到错配。本文件的 `faceBlock_a_lexS` 是同款证法换一座 `S`，
  ⛔ 证法**不是**首创，新的只有「换到一座能分离的 `S` 上」这件事本身。
* `Nivat.FillCoverWit.faceBlock_a_sqF` / `faceBlock_a'_sqF`（`FillCoverWitness.lean`，
  lane-leafa-gen 本轮落的）钉的是 `sqF`，同样是重合的那一类。
* team-lead 的精确整数脚本（`tmp/_lead248_lexmin.py`）先算出错配一般存在；本文件是把那条
  读数送进内核，**发现权不在我**，我只做内核化 ＋ 升级到整条 `FaceBlock` ＋ 对任意 `F`。

## import 表（与 `grep -n "^import"` 逐字一致）

    Nivat.External.Colle.ANormal

`ANormal` 的 `grep -n "^import"`：`FaceDistinct`、`FaceData`、`Claim47Core`、`EdgeNormals`、
`ONEDRational` —— 四个禁区文件（`RegionSteps` / `ColleRegion` / `Case2WindowProbe` /
`NfpLPreamble`）一个都不在其闭包里（实算，见报告）⟹ 不成环。
-/
import Nivat.External.Colle.ANormal

namespace Nivat.TowerHlevLexMin

open Nivat Nivat.LE2 Nivat.Colle35

/-! ## §0. 取证：本文件用到的主仓现货，先 `#check`（olean 侧，不信转述） -/

#check @Nivat.Colle35.FaceBlock
#check @Nivat.LatticeConvex
#check @Nivat.Conv
#check @Nivat.toReal

/-! ## §1. 见证集与它的格凸性 -/

/-- **team-lead 脚本里的 `S1`**：`{(1,0),(2,0),(0,1),(1,1),(2,1)}`。
`(0,0)` 不在里面，这正是错配的来源（面在 `y = 0` 上，而 `x` 的全局极小在 `y = 1` 上）。 -/
def lexS : Finset (ℤ × ℤ) :=
  {((1 : ℤ), (0 : ℤ)), ((2 : ℤ), (0 : ℤ)), ((0 : ℤ), (1 : ℤ)), ((1 : ℤ), (1 : ℤ)),
    ((2 : ℤ), (1 : ℤ))}

/-- `lexS` 的实凸包所在的四条半平面 `0 ≤ y`、`y ≤ 1`、`x ≤ 2`、`1 ≤ x + y`，其交在 `ℝ²`
里是凸的。⚠ `1 ≤ x + y` 是**切掉 `(0,0)`** 的那一条，去掉它整性就不成立了。 -/
theorem convex_lexR :
    Convex ℝ {q : ℝ × ℝ | 0 ≤ q.2 ∧ q.2 ≤ 1 ∧ q.1 ≤ 2 ∧ 1 ≤ q.1 + q.2} := by
  rintro x ⟨hx1, hx2, hx3, hx4⟩ y ⟨hy1, hy2, hy3, hy4⟩ a b ha hb hab
  simp only [Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith

/-- **`lexS` 是格凸的。**  四条半平面 ⟹ `0 ≤ y ≤ 1`、`x ≤ 2`、`1 ≤ x + y`，`omega` 穷举出
恰好五个格点。 -/
theorem latticeConvex_lexS : LatticeConvex lexS := by
  intro z hz
  have hsub : Conv lexS ⊆ {q : ℝ × ℝ | 0 ≤ q.2 ∧ q.2 ≤ 1 ∧ q.1 ≤ 2 ∧ 1 ≤ q.1 + q.2} := by
    apply convexHull_min _ convex_lexR
    rintro _ ⟨w, hw, rfl⟩
    rw [Finset.mem_coe] at hw
    simp only [lexS, Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl <;>
      refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num [toReal]
  obtain ⟨h1, h2, h3, h4⟩ := hsub hz
  simp only [toReal] at h1 h2 h3 h4
  have e1 : (0 : ℤ) ≤ z.2 := by exact_mod_cast h1
  have e2 : z.2 ≤ 1 := by exact_mod_cast h2
  have e3 : z.1 ≤ 2 := by exact_mod_cast h3
  have e4 : (1 : ℤ) ≤ z.1 + z.2 := by exact_mod_cast h4
  have hcase : z = ((1 : ℤ), (0 : ℤ)) ∨ z = ((2 : ℤ), (0 : ℤ)) ∨ z = ((0 : ℤ), (1 : ℤ)) ∨
      z = ((1 : ℤ), (1 : ℤ)) ∨ z = ((2 : ℤ), (1 : ℤ)) := by
    obtain ⟨a, b⟩ := z
    simp only [Prod.ext_iff] at *
    omega
  rcases hcase with rfl | rfl | rfl | rfl | rfl <;> decide

/-! ## §2. team-lead 逐字要的那条 -/

/-- ⭐ **`lex` 推不出全局 `vJ`-极小。**  签名逐字抄自 team-lead 本轮的派工，一字未改。
见证：`S := lexS`、`n := (0,1)`、`v := (1,0)`、`a := (1,0)`；全局 `dot v`-极小是 `0`，
在 `(0,1)` 处。⚠ 第三个合取（`lex`）在这里对一切 `b ≠ a` **严格**成立，不靠并列项含糊。 -/
theorem lex_not_imp_global_vJ_min :
    ∃ (S : Finset (ℤ × ℤ)) (n v a : ℤ × ℤ),
      LatticeConvex S ∧ a ∈ S ∧
      (∀ b ∈ S.erase a, dot (-n) b < dot (-n) a ∨
        (dot (-n) b = dot (-n) a ∧ dot (-v) b < dot (-v) a)) ∧
      ¬ (∀ b ∈ S, dot v a ≤ dot v b) :=
  ⟨lexS, ((0 : ℤ), (1 : ℤ)), ((1 : ℤ), (0 : ℤ)), ((1 : ℤ), (0 : ℤ)),
    latticeConvex_lexS, by decide, by decide, by decide⟩

/-! ## §3. 升级：整条 `FaceBlock` 都不够 -/

/-- ⭐⭐ **`lexS` 上一条完整的 `FaceBlock`**（11 个字段全给）。
`a = (1,0)`、`a' = (2,0)`、`r = 1`：`nJ = (0,1)` 的底面就是 `{(1,0),(2,0)}`，两点一线。 -/
def lexFB : Nivat.Colle35.FaceBlock lexS ((0 : ℤ), (1 : ℤ)) ((1 : ℤ), (0 : ℤ)) where
  a := ((1 : ℤ), (0 : ℤ))
  a' := ((2 : ℤ), (0 : ℤ))
  r := 1
  latticeConvex_S := latticeConvex_lexS
  a_mem := by decide
  a'_mem := by decide
  lex := by decide
  lex' := by decide
  edge := by
    intro b hb
    have hne : b ≠ ((1 : ℤ), (0 : ℤ)) := Finset.ne_of_mem_erase hb
    have hb' : b ∈ lexS := Finset.mem_of_mem_erase hb
    simp only [lexS, Finset.mem_insert, Finset.mem_singleton] at hb'
    rcases hb' with rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl hne
    · exact Or.inl ⟨1, le_rfl, le_rfl, by decide⟩
    · exact Or.inr (by decide)
    · exact Or.inr (by decide)
    · exact Or.inr (by decide)
  edge' := by
    intro b hb
    have hne : b ≠ ((2 : ℤ), (0 : ℤ)) := Finset.ne_of_mem_erase hb
    have hb' : b ∈ lexS := Finset.mem_of_mem_erase hb
    simp only [lexS, Finset.mem_insert, Finset.mem_singleton] at hb'
    rcases hb' with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨1, le_rfl, le_rfl, by decide⟩
    · exact absurd rfl hne
    · exact Or.inr (by decide)
    · exact Or.inr (by decide)
    · exact Or.inr (by decide)
  dot_nJ_vJ := by decide

/-- ⭐ **整个 `FaceBlock` 都推不出全局 `vJ`-极小。**  team-lead 派工里标「能加分但不必须」的
那一格：不是只有 `lex` 不够，是 11 个字段一起也不够。 -/
theorem faceBlock_not_imp_global_vJ_min :
    ∃ (S : Finset (ℤ × ℤ)) (n v : ℤ × ℤ) (F : Nivat.Colle35.FaceBlock S n v),
      ¬ (∀ b ∈ S, dot v F.a ≤ dot v b) :=
  ⟨lexS, ((0 : ℤ), (1 : ℤ)), ((1 : ℤ), (0 : ℤ)), lexFB, by decide⟩

/-! ## §4. 错配对 `a` 的选取不敏感 -/

/-- **任意** `F : FaceBlock lexS (0,1) (1,0)` 都有 `F.a = (1,0)`。
证法：`a_mem` 的五点分情形，每个非 `(1,0)` 的候选都被 `F.lex` 在 `b = (1,0)` 处当场否掉
（`(2,0)` 那支靠并列项 `dot (-v)`，其余三支靠 `dot (-n)`）。 -/
theorem faceBlock_a_lexS (F : Nivat.Colle35.FaceBlock lexS ((0 : ℤ), (1 : ℤ))
    ((1 : ℤ), (0 : ℤ))) : F.a = ((1 : ℤ), (0 : ℤ)) := by
  have hm := F.a_mem
  simp only [lexS, Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with h | h | h | h | h
  · exact h
  all_goals
    (exfalso
     have hz := F.lex ((1 : ℤ), (0 : ℤ)) (by rw [h]; decide)
     rw [h] at hz
     revert hz
     decide)

/-- ⭐ **对任意 `FaceBlock`，`F.a` 都不是 `lexS` 的全局 `vJ`-极小点。**
⛔ 所以读数三不是「我挑了个坏 `a`」。 -/
theorem faceBlock_a_not_global_vJ_min (F : Nivat.Colle35.FaceBlock lexS ((0 : ℤ), (1 : ℤ))
    ((1 : ℤ), (0 : ℤ))) :
    ¬ (∀ b ∈ lexS, dot ((1 : ℤ), (0 : ℤ)) F.a ≤ dot ((1 : ℤ), (0 : ℤ)) b) := by
  rw [faceBlock_a_lexS F]
  decide

/-! ## §5. 被否的谓词非空真（§71 三）＋ 反哨兵 -/

/-- **全局 `vJ`-极小点在 `lexS` 上存在**，在 `(0,1)` 处。⟹「`F.a` 不是它」是真错配，
不是谓词整体退化为假；同时这一格是反哨兵：同一谓词在同一座 `S` 上既有真实例又有假实例。 -/
theorem global_vJ_min_exists_in_lexS :
    ∀ b ∈ lexS, dot ((1 : ℤ), (0 : ℤ)) ((0 : ℤ), (1 : ℤ)) ≤ dot ((1 : ℤ), (0 : ℤ)) b := by
  decide

/-- 错配的**数值大小**：面上的 `dot v` 是 `1`，全局极小是 `0`，差 `1`。
（写出来是为了让「错配」不只是一个 `¬`，而是一个可复算的数。） -/
theorem lexS_gap :
    dot ((1 : ℤ), (0 : ℤ)) lexFB.a = 1 ∧
      dot ((1 : ℤ), (0 : ℤ)) ((0 : ℤ), (1 : ℤ)) = 0 := by
  constructor <;> decide

/-- **`(0,1)` 不在 `nJ`-面上**，这就是错配的几何原因：`dot nJ (0,1) = 1 > 0 = dot nJ F.a`。 -/
theorem min_point_off_face :
    dot ((0 : ℤ), (1 : ℤ)) lexFB.a = 0 ∧
      dot ((0 : ℤ), (1 : ℤ)) ((0 : ℤ), (1 : ℤ)) = 1 := by
  constructor <;> decide

end Nivat.TowerHlevLexMin

#print axioms Nivat.TowerHlevLexMin.lexS
#print axioms Nivat.TowerHlevLexMin.convex_lexR
#print axioms Nivat.TowerHlevLexMin.latticeConvex_lexS
#print axioms Nivat.TowerHlevLexMin.lex_not_imp_global_vJ_min
#print axioms Nivat.TowerHlevLexMin.lexFB
#print axioms Nivat.TowerHlevLexMin.faceBlock_not_imp_global_vJ_min
#print axioms Nivat.TowerHlevLexMin.faceBlock_a_lexS
#print axioms Nivat.TowerHlevLexMin.faceBlock_a_not_global_vJ_min
#print axioms Nivat.TowerHlevLexMin.global_vJ_min_exists_in_lexS
#print axioms Nivat.TowerHlevLexMin.lexS_gap
#print axioms Nivat.TowerHlevLexMin.min_point_off_face
