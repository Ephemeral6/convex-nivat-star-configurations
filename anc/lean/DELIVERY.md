# Nivat 猜想的 Lean 4 形式化：交付说明

包根目录即 Lean 工程根。主定理：`Nivat.nivat_conjecture`（`Nivat/Section8/Main.lean`）。
主要参考文献：Pan, *The Convex Nivat Conjecture*（§8 顶层组装、§1–§7 主体，源文件注释中逐节引用）；
外部输入 Collé, *On periodic decompositions, one-sided nonexpansive directions and Nivat's conjecture*（arXiv 1909.08195，
文本 `scratch/b3_colle2.txt`）、Kari–Szabados、Boyle–Lind、Cyr–Kra，均在仓库内证明（见 §3）。

## 0. 包内容

本包是工作仓库（分支 `fix/def32-convexity`，导出时的 commit 见压缩包文件名）的精简导出，只含构建与检查所需文件：

- `Nivat.lean`、`Nivat/`（449 个模块）：全部 Lean 源码；
- `lean-toolchain`、`lakefile.toml`、`lake-manifest.json`：工具链与依赖锁定；
- `scripts/sorries.sh`、`scripts/check_axioms.sh`、`scripts/check_axioms.lean`：§2 的检查脚本；
- 本文件 `DELIVERY.md`。

未包含：工作仓库的 `blueprint/`（工作记录）、`tmp/`（草稿与 python 数值台架）、`scratch/b3_colle2.txt`
（Collé 论文 arXiv 1909.08195 的文本提取）及其余脚本。本文与源码注释中引用这些路径之处（包括大量
`b3_colle2.txt:行号` 形式的原文定位）在包内无法直接打开，需要时可另行索取。

## 1. 证明了什么

### 1.1 主定理（逐字摘自 `Nivat/Section8/Main.lean`）

```lean
theorem nivat_conjecture {α : Type*} [Finite α] {ξ : Config α} {n k : ℕ} (hn : 0 < n)
    (hk : 0 < k) (hP : P ξ (rectangle n k) ≤ n * k) : IsPeriodic ξ :=
  convex_nivat (rectangle_nonempty hn hk) (latticeConvex_rectangle n k)
    (by rwa [card_rectangle])
```

读法：有限字母表 `α` 上的二维格点构型 `ξ : ℤ² → α`，若存在 `n, k ≥ 1` 使 `[1,n]×[1,k]` 窗口内不同 pattern 数
`P ξ (rectangle n k) ≤ n·k`，则 `ξ` 有非零周期。这正是 Nivat 猜想（二维、有限字母表）。

它由更一般的凸版本得到（同文件）：

```lean
theorem convex_nivat {α : Type*} [Finite α] {ξ : Config α} {S : Finset (ℤ × ℤ)}
    (hne : S.Nonempty) (hS : LatticeConvex S) (hP : P ξ S ≤ S.card) : IsPeriodic ξ
```

### 1.2 statement 依赖的定义（逐字）

`rectangle`（`Nivat/Section8/Main.lean`）：窗口 `{1..n} × {1..k}`（`card_rectangle : (rectangle n k).card = n * k` 已证）。

```lean
noncomputable def rectangle (n k : ℕ) : Finset (ℤ × ℤ) :=
  Finset.Icc 1 (n : ℤ) ×ˢ Finset.Icc 1 (k : ℤ)
```

`Config`、`T`、`Per`、`IsPeriodic`（`Nivat/Defs/Config.lean`）：

```lean
/-- A configuration on the integer lattice with values in `α`. -/
abbrev Config (α : Type*) : Type _ := ℤ × ℤ → α

/-- Translation of configurations: `(T u f) z = f (z + u)`.  Paper §0.3. -/
def T {α : Type*} (u : ℤ × ℤ) (f : Config α) : Config α := fun z => f (z + u)

/-- The period group of a configuration: the set of `u` with `T u f = f`.  Paper §0.1. -/
def Per {α : Type*} (f : Config α) : AddSubgroup (ℤ × ℤ) where
  carrier := {u | T u f = f}
  add_mem' := by
    intro u v hu hv
    simp only [Set.mem_ofPred_eq, T, funext_iff] at *
    intro z
    rw [show z + (u + v) = z + v + u by abel, hu (z + v), hv z]
  zero_mem' := by simp
  neg_mem' := by
    intro u hu
    simp only [Set.mem_ofPred_eq, T, funext_iff] at *
    intro z
    have h := hu (z + -u)
    rw [show z + -u + u = z by abel] at h
    exact h.symm

/-- A configuration is *periodic* if its period group contains a non-zero vector. -/
def IsPeriodic {α : Type*} (f : Config α) : Prop := ∃ u ∈ Per f, u ≠ 0
```

读法：`Config α` 是 `ℤ²` 上的 `α` 值函数；`T u f` 是平移 `z ↦ f(z+u)`；`Per f = {u | T u f = f}` 是周期群（子群，
`add_mem'/neg_mem'` 的证明只是验证子群性）；`IsPeriodic f` 即存在非零周期向量（单向周期即可，不要求双周期）。

`pattern`、`patterns`、`P`（`Nivat/Defs/Complexity.lean`）：

```lean
def pattern (θ : Config α) (Q : Finset (ℤ × ℤ)) (u : ℤ × ℤ) : Q → α :=
  fun q => θ (u + (q : ℤ × ℤ))

def patterns (θ : Config α) (Q : Finset (ℤ × ℤ)) : Set (Q → α) :=
  Set.range (pattern θ Q)

noncomputable def P (θ : Config α) (Q : Finset (ℤ × ℤ)) : ℕ :=
  (patterns θ Q).ncard
```

读法：`pattern θ Q u` 是 `θ` 在平移窗口 `u+Q` 上的限制；`patterns θ Q` 是所有 `u ∈ ℤ²` 上出现的不同 pattern 之集；
`P θ Q` 是其基数（`Set.ncard`）。审计提示：`Set.ncard` 对无限集取 0，但 `[Finite α]` 下 `patterns` 必有限
（`Nivat.patterns_finite`，同文件已证），故此处无空真风险。

`LatticeConvex`（`convex_nivat` 用，`rectangle` 的凸性由 `latticeConvex_rectangle` 证明）：
`∀ z, toReal z ∈ Conv S → z ∈ S`，其中 `Conv S` 是 `S` 在 `ℝ²` 中的凸包（`Nivat/Defs/Complexity.lean`）。

## 2. 如何检查

- 工具链：`lean-toolchain` = `leanprover/lean4:v4.33.1`。
- mathlib：`lakefile.toml` 中 `rev = "v4.33.1"`；`lake-manifest.json` 锁定 commit
  `0df444a360eaa60ab8c11dca51a86af692955474`。
- `lakefile.toml` 中 `lean_lib Nivat` 设 `globs = ["Nivat", "Nivat.+"]`，保证 `lake build` 编译 `Nivat/` 下全部模块
  （不设则只编译根文件传递 import 的子集）。`Nivat/All.lean` 由 `scripts/gen_all.py`（未随包）生成，import 全部模块。
- 环境：需要 [elan](https://github.com/leanprover/elan)（会按 `lean-toolchain` 自动装对应 Lean）、`bash`、`git`；
  `sorries.sh` 还需要 `gawk`（macOS 可 `brew install gawk`）。`lake exe cache get` 需联网下载 mathlib 预编译缓存；
  `Nivat` 本身从源码编译，`LEAN_NUM_THREADS=2` 时约 40 分钟量级。

```
lake exe cache get
LEAN_NUM_THREADS=2 lake build
bash scripts/sorries.sh
bash scripts/check_axioms.sh Nivat.nivat_conjecture
```

期望：

| 检查 | 期望 |
|---|---|
| `lake build` | rc=0，无 error |
| `bash scripts/sorries.sh` | `TOTAL: 0` |
| `bash scripts/check_axioms.sh Nivat.nivat_conjecture` | `[propext, Classical.choice, Quot.sound]`，无 `sorryAx`；脚本白名单仅此三条（`scripts/check_axioms.lean`），不在白名单则退出码 1 |

说明：`check_axioms.sh` 通过 `lake env lean --run scripts/check_axioms.lean` 导入 `Nivat.All`，读已构建的 `.olean`，故需先 `lake build`。
`sorries.sh` 先剥离注释再匹配 `sorry` 记号，只统计真实 `sorry`；它只覆盖「零 sorry」，公理干净由 `check_axioms.sh` 覆盖，两者都要看。

### 已有读数（本机 2026-09-30 读数，仓库 CLAUDE.md §4 / `blueprint/OPEN.md` §1 记录）

`BUILD_RC=0`，3368 jobs；`scripts/sorries.sh` `TOTAL: 0`；`#print axioms Nivat.nivat_conjecture` =
`[propext, Classical.choice, Quot.sound]`；`stale_scan.sh` FRESH；`gen_all.py --check` 通过（449 个模块）。
这些是仓库内记录的读数，不是本文撰写时重跑的。

### 独立验证（2026-09-30 本机重跑）

- 全新 clone 上从零构建：`git clone E:/nivat-repo E:/nivat-fresh`，检出 `ae5164c`（无本地改动）。
  `lake exe cache get` `CACHE_RC=0`（mathlib 等依赖的 `.olean` 取自本机 `~/.cache/mathlib`，`Nivat` 全部从源码编译）。
  `LEAN_NUM_THREADS=2 lake build`：第一次运行在 `[3329/3368]` 处因会话中断被杀，原地续跑（增量，未清 `.lake/`）得
  `Build completed successfully (3368 jobs)`，`BUILD_RC=0`，日志无 `error`；`.lake/build/lib/lean/Nivat/**/*.olean`
  449 个，与 `Nivat/**/*.lean` 449 个一致。随后同一 clone 上：`bash scripts/sorries.sh` → `TOTAL: 0`；
  `bash scripts/check_axioms.sh Nivat.nivat_conjecture` → `Nivat.nivat_conjecture depends on: [propext, Classical.choice, Quot.sound]`，
  退出码 0。
- lean4checker（独立内核重检，2026-09-30 本机）：使用 v4.33.1 工具链自带的 `leanchecker`
（`~/.elan/toolchains/leanprover--lean4---v4.33.1/bin/leanchecker.exe`，源码 `src/lean/LeanChecker.lean`，
与 `lean-toolchain` 完全一致）。
  - `LEAN_NUM_THREADS=2 lake env leanchecker -v Nivat`：前缀模式，逐模块用内核重放该模块自己的声明，
    共 451 个模块（`All.lean` 的 449 个 + `Nivat.All` + 一个无源码的残留 olean），`CHECK_RC=0`，0 处报错。
  - `LEAN_NUM_THREADS=2 lake env leanchecker -v --fresh Nivat.Section8.Main`：把整个环境（Lean 核心、Mathlib、
    Nivat）从空环境逐常量重放，覆盖 `Nivat.nivat_conjecture`，`CHECK_RC=0`，0 处报错。
  - 说明：`leanchecker` 是内核重放，不检查公理；公理闭包另由 `check_axioms.sh` 检查。

## 3. 证明结构

### 3.1 顶层链（均在 `Nivat/Section8/`）

`nivat_conjecture`（`Main.lean`）→ `convex_nivat`（`Main.lean`，Theorem 8.18）。`convex_nivat` 反证：

1. `exists_intEncoding`（`Main.lean`）：字母表嵌入 `ℤ_{>0}`，pattern 数与周期性不变。
2. `exists_minimalCounterexample`（`External.lean`）：取阶最小的反例（Remark 8.3）。
3. `structure_input`（`Normalisation.lean`）：由最小反例得到素数 `p` 下的结构输入（`𝔽_p` 上的分解、半平面 `Uᵢ, Vᵢ`、
   窗口 `W` 及 `P_ζ(W) ≤ |W|`），汇集 §8.1–§8.5：`HalfPlane.lean`、`FirstHalfPlane.lean`、`SecondHalfPlane.lean`、
   `ConeGeom.lean`、`RegionUpgrade.lean`、`SubseqFinite.lean`。
4. `exists_starConfig_of_admissible`（`Normalisation.lean`，Lemma 8.17）：化为 star 构型。
5. `star_complexity_lower_bound`（`Nivat/MainTheorem.lean`，Theorem 7.3 = Theorem A）：`P ≥ |W| + 1`，与第 3 步矛盾。
   自包含部分 §1–§7 在 `Nivat/` 根下（`Laurent/`、`Lattice/`、`Chord.lean`、`ZonotopePair.lean`、`MainTheorem.lean` 等）。

### 3.2 外部结果（在仓库内证明，非假设）

论文中以文献形式引用的结果均已在仓库内证明：

- Kari–Szabados 分解：`Nivat/External/KSAnnihilator.lean`、`KSDecomposition.lean`（`kari_szabados_decomp'`）、
  `KSCorollary.lean`（`kari_szabados_prodShift'`），及 `Nivat/External/KS/{Nullstellensatz,Lemma3,Lemma4,Theorem31}.lean`。
- Collé Theorem 1.14（全周期性）：`Nivat/External/Colle/Theorem114Final.lean`（`theorem114`），其中 Boyle–Lind：
  `Colle/BoyleLind.lean`（`boyleLind`）；Cyr–Kra：`Colle/Prop210.lean`（`cyrKra_downward_induction`）、`Colle/CyrKra224.lean`。
- Collé 区域构造（Theorem 8.7 所用）：`Nivat/External/Colle/ColleRegion.lean`（`colle_region`），依赖 Lemma 3.5
  （`Colle/Lemma35.lean`，`lemma35`）、Claim 4.3、Lemma 4.5 等，共约 40 个 `Colle/` 模块；接入主链的证明版本见
  `Section8/ExternalDischarged.lean`（`exists_mem_ONED'`、`exists_fullyPeriodic_region'`）。

本文撰写时核对的内容：

- 对 `Nivat/**/*.lean`（449 个文件）加 `Nivat.lean`，先剥离块注释/行注释/字符串字面量，再搜索 `axiom`、`opaque`、
  `native_decide`、`implemented_by`、`unsafe`、`sorry`、`admit`、`extern`：**零命中**。
  （不剥离注释时 `grep axiom` 会命中若干文档字符串里的行首 `axiom`，均为叙述性文字。）
- 公理闭包为 `[propext, Classical.choice, Quot.sound]`：已在全新 clone 上重跑 `check_axioms.sh` 确认（见 §2「独立验证」）。
  该读数意味着上述外部结果确实被证明，而非以 `axiom` 引入；`scripts/check_axioms.lean` 白名单注释记录了
  `kari_szabados_prodShift`、`colle_doublyPeriodic`、`colle_region` 三条曾经的项目公理已于 2026-09-18 被证明并删除。

## 4. 与论文的偏离（Collé Lemma 3.5(i) 的证明）

范围：只涉及 Collé 论文 Lemma 3.5(i) 证明中的一步。Lemma 3.5 本身的陈述、以及其余全部结果的陈述均未改动。

**论文的构造**（`scratch/b3_colle2.txt` 第 516–524 行）：在反证假设下，取 `Â_∞^{(ε)}`，并定义

`Â_i^{(ε)} := { g − t·v⃗_{ℓ_{J+1}} ∈ Â_∞^{(ε)} : g ∈ Â_i, t ∈ ℤ_+ }`（第 518 行，沿 `−v⃗_{ℓ_{J+1}}` 扫掠）。

论文断言（第 516–520 行）：(a) 对适当固定的 `ε` 及充分大的 `i`，该集合是 `E(𝒮_φ)`-enveloped 集；
(b) `B_i − k_i v⃗_ℓ ⊂ Â_i^{(ε)} ⊂ H_{B_i}(ℓ) − k_i v⃗_ℓ`。论文对 (a) 没有给出论证（只有 "Note that"，
见 `blueprint/LEAF-A.md`「`shellEnv` 是原文的缺口」条、`blueprint/CLAUDE-ARCHIVE-2026-09-18.md`「`shellEnv` 是原文的缺口」条）。

**形式化发现**：在 `(ℓ, ℓ_J)`-region 的 zonotope 数值模型上，上述扫掠集合的 (a) 或 (b) 一般不成立。
对照脚本 `tmp/wip/hole1-qshell-sweep-control.py`（本文撰写时只读重跑）：10 个生成元族、各 `ι, J`、`ε ∈ {1,2,3}`、`i = 3..6`，
共 2448 个实例中 enveloped 性失败 1083 个、strip 包含关系失败 768 个、二者同时成立仅 1140 个（1308 个至少有一条失败）。
这是数值模型上的反例统计，不是 Lean 中的否定定理；反例族的具体描述见该脚本。
（`blueprint/OPEN.md` §1 记录了同一结论：「`:518` 扫掠 shell 路线」被弃用。）

**Lean 中采用的替代**：`Nivat/External/Colle/Hole1PushShell.lean` 中定理 `Nivat.ColleReg.exists_chainData_closed`
（binder 与结论与 `Nivat/External/Colle/RegionSteps.lean` 的 `exists_chainData` 逐字相同，`RegionSteps.lean` 中的
`exists_chainData` 直接 `exact exists_chainData_closed …`）。`ChainData.shell` 是自由数据，构造为：对每层 `Â_i`
只把它的 `J` 面向外推出 `L = det prev J · det J next` 个格点层（`Hole1QShell.pushShell`），阈值以下用一个非格凸的
填充集；逐条验证 `ChainData` 的七条 shell 义务（`Hole1QShell.PinTower.shell_pack`）。该模块 docstring 的原话：
"This repairs the paper's proof of Lemma 3.5(i); the statement of `exists_chainData` is unchanged."
即：只有 Lemma 3.5(i) 证明中 shell 的构造不同，陈述不变。

**其他已记录的偏离/缺口**（仅列出有文件依据者；未做逐条复核）：

- `AhatMono`（`Â_i ⊆ Â_j`）：论文只在 Figure 6 图注（`b3_colle2.txt:508`）出现，正文无论证，而第 510 行的紧致性取极限需要它。
  见 `Nivat/External/Colle/AhatMono.lean` 模块 docstring、`blueprint/LEAF-A.md` 「`AhatMono` 的原文出处一直是错的」条。
- 以上两条只说明论文该处论证不完整；形式化如何处理它们以代码为准（主定理公理闭包干净即说明均已闭合）。
  `blueprint/` 下另有大量「比原文强」「原文缺口」类历史条目，本文未逐条核查，除以上两条外：**未系统核查**。

## 5. 非数学层面的说明

- `Nivat/External/Colle/Hole1PushShell.lean`（3423 行）是三个草稿文件的拼接
  （文件内有 `===== begin/end` 标记），含 `quadrant_mem` 等少量重复与一个 `Bench` 非空性小节；文件末尾留有
  `#check`/`#print axioms` 检查行，构建日志里会看到它们的输出。可择机拆分去重，不影响正确性。
- `Nivat/` 下有一些不在主定理依赖链上的模块（复核、反例、台架用），同样被 `lake build` 编译检查、同样零 `sorry`。
- 源码注释是长期工作记录，其中引用的 `blueprint/`、`tmp/`、`PROTOCOL.md` 等不随包（见 §0）。
  主链上的状态段落已于 2026-09-30 更新为「已闭合」并注明日期（`Section8/Main.lean`、`Section8/External.lean`、
  `Section8/ExternalDischarged.lean`、`External/Colle/ColleRegion.lean`、`External/Colle/RegionSteps.lean`），
  其中保留的 `sorryAx` 读数均标为历史。其余约 20 个 `External/Colle/` 模块的 docstring 仍有写于闭合前的
  「still open」「remaining `sorry`」「`sorryAx`」等工作记录，均已过时未改：
  **状态以 `lake build`、`sorries.sh`、`#print axioms` 的实际输出为准，不要读 docstring。**
