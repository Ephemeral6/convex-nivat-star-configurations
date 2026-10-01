/-
Lane lane-shell, 2026-09-22 round 25.  `tmp/wip/`, sorries allowed (none used below).

**Purpose**: team-lead's consumer ruling (`ofPartsExhaustsInter`, `ChainExhaustInter.lean`)
names the missing input for the `w`-sextet (`w`, `hsweepW`, `escapeW`, `shellSubStrip`,
`shellEnv`, `fillCover`) as the fan-successor of `J` — `ν_{J+1}`, "the neighbour on the far
side from `ℓ`" — mirroring lane-recp's `exists_fan_pred` (`LeafAJSelect.lean:803`, which finds
`nprevJ`, the fan-*predecessor* of `J` inside `Arc ℓ J`).

**Key observation**: `nprevJ`'s construction needs a *second* fan point to bound the search
(`ℓ` itself, sitting `Arc`-before `J`).  For the *successor*, the natural second point closing
the search on "the far side from `ℓ`" is `-ℓ` — exactly `π` away from `ℓ`, splitting the fan
into the half containing `J` (`Arc ℓ (-ℓ)`) and the other half.  Since `0 < det ℓ J` (`J` is
ccw-after `ℓ`), `0 < det J (-ℓ)` **follows automatically** (`det J (-ℓ) = -det J ℓ = det ℓ J`,
`det_neg_right` + `det_skew`), so `exists_fan_pred_cw` (`LeafAJSelect.lean:943`, already landed
0-sorry) applies *verbatim* with its own `ℓ`-binder instantiated to `-ℓ` — no new fan-geometry
argument is needed, only the sign bookkeeping making `-ℓ` a legal second endpoint.  This
theorem is `exists_nnextJ`, the wrapper record of that fact under the naming team-lead asked
for (`νJ1`), plus the two consumers `w := -dir νJ1` and `hsweepW := hsweepW_of_fan_adjacent`
that `ofPartsExhaustsInter`'s `w`/`hsweepW` binders (`ChainExhaustInter.lean`) need.
-/
import Nivat.External.Colle.LeafAJSelect
import Nivat.External.Colle.ShellRegionJ

set_option autoImplicit false

namespace Nivat.LeafAShellNNext

open Nivat Nivat.LE2 Nivat.PolyChainSum

variable {Sphi : Finset (ℤ × ℤ)}

/-- **`ν_{J+1}` exists**: the fan-adjacent successor of `J`, found inside `Arc J (-ℓ)` (or `= -ℓ`
when that set is empty), by instantiating `LeafAJSelect.exists_fan_pred_cw` at its own `ℓ`-slot
with `-ℓ`.  `0 < det J (-ℓ)` (the hypothesis `exists_fan_pred_cw` needs) follows from
`0 < det ℓ J` alone: `det J (-ℓ) = -det J ℓ = det ℓ J` (`det_neg_right`, `det_skew`). -/
theorem exists_nnextJ {ℓ J : ℤ × ℤ}
    (hnegℓE : (-ℓ) ∈ E (↑Sphi : Set (ℤ × ℤ))) (hJE : J ∈ E (↑Sphi : Set (ℤ × ℤ)))
    (hℓJ : 0 < det ℓ J) :
    ∃ νJ1, νJ1 ∈ E (↑Sphi : Set (ℤ × ℤ)) ∧ 0 < det J νJ1 ∧
      Arc (Sphi.finite_toSet) J νJ1 = ∅ ∧
      (νJ1 = -ℓ ∨ νJ1 ∈ Arc (Sphi.finite_toSet) J (-ℓ)) := by
  have hJnegℓ : 0 < det J (-ℓ) := by
    have h1 : det J (-ℓ) = -det J ℓ := det_neg_right J ℓ
    have h2 : det J ℓ = -det ℓ J := det_skew J ℓ
    omega
  exact Nivat.LeafAJSelect.exists_fan_pred_cw hnegℓE hJE hJnegℓ

/-- **`w` and `hsweepW`, assembled from `exists_nnextJ`.**  Collé's `w := -v_{ℓ_{J+1}} =
-dir νJ1`; `hsweepW : dot nJ w < 0` with `nJ := -J` is `ShellRegionJ.hsweepW_of_fan_adjacent`
fed the `0 < det J νJ1` tag `exists_nnextJ` produces.

**⚠ 本条是 `w` 的指定生产者。第 162 轮起标注「主仓零消费者，别当死代码删」——
✅ 第 181 轮起不再是 orphan**：`Nivat.WFanWiring.exists_w_fan_dichotomy`
（`WFanWiring.lean`）是它在主仓的第一个**项级**消费者，把下面被下游丢掉的那两项真正用掉。
`ChainDataGeom.ofPartsExhaustsInter`（`ChainExhaustInter.lean`）对 `w` 的唯一约束是
`hsweepW : dot nJ w < 0`。**仅凭符号，它的 `shellEnv` binder 为假**：
`Nivat.LaneEnvShellEnvRefute.not_shellEnv`（`tmp/wip/lane-env-shellenv-refute.lean:252`）
在 `w = (-1,-1)` 上内核否掉，同一实例换成扇后继 `w = (-1,0)` 则为真（`shellEnv_fan`，`:525`）。
补上这个缺口的，正是本结论里被下游丢掉的那两项：

* `Arc (Sphi.finite_toSet) J νJ1 = ∅` —— 扇形相邻性（`J` 与 `νJ1` 之间没有别的边法向）；
* `w = -(dir νJ1)` —— 把相邻性钉到 `w` 上。

原文 `b3_colle2.txt:518` 的 `w := −v⃗_{ℓ_{J+1}}`；`NOTATION.md:213`「`J` 另一侧的扇邻居」，
`nJ = -J`（`NOTATION.md:175,208`）。

**消费点不在 `ofPartsExhaustsInter` 的 binder 表里**：`shellEnv` / `shellSubStrip` /
`fillCover` 都是调用方供给的 binder，调用方证它们时这两项本来就在作用域里，所以往表里加
等于加一组没有消费者的 binder（纯债，硬规矩 5）。⟹ 接法是在**调用方一侧**把这两项用掉，
这已由 `WFanWiring.lean` 做出（第 181 轮，集成者）：
`exists_w_fan_dichotomy` 消掉 `LaneCdSubstrip.w_eq_vl_or_dot_nl_w_neg` 的 `hor` 假设，
`fan_w_shellSubStrip_or_finite` 把两支接到 `shellSubStrip_of_w_eq_vl_of_max` /
`shellInter_finite_of_level` 上。⚠ 那里**不主张 `shellEnv`**，缺口仍在。 -/
theorem exists_w_hsweepW {ℓ J : ℤ × ℤ}
    (hnegℓE : (-ℓ) ∈ E (↑Sphi : Set (ℤ × ℤ))) (hJE : J ∈ E (↑Sphi : Set (ℤ × ℤ)))
    (hℓJ : 0 < det ℓ J) :
    ∃ νJ1 w : ℤ × ℤ, νJ1 ∈ E (↑Sphi : Set (ℤ × ℤ)) ∧ 0 < det J νJ1 ∧
      Arc (Sphi.finite_toSet) J νJ1 = ∅ ∧
      (νJ1 = -ℓ ∨ νJ1 ∈ Arc (Sphi.finite_toSet) J (-ℓ)) ∧
      w = -(dir νJ1) ∧ dot (-J) w < 0 := by
  obtain ⟨νJ1, hE, hpos, hempty, hor⟩ := exists_nnextJ (Sphi := Sphi) hnegℓE hJE hℓJ
  exact ⟨νJ1, -(dir νJ1), hE, hpos, hempty, hor, rfl,
    Nivat.ShellRegionJ.hsweepW_of_fan_adjacent J νJ1 hpos⟩

end Nivat.LeafAShellNNext

#print axioms Nivat.LeafAShellNNext.exists_nnextJ
#print axioms Nivat.LeafAShellNNext.exists_w_hsweepW
