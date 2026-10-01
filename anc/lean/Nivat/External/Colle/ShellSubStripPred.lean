/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.ShellMink
import Nivat.External.Colle.ChainMax
import Nivat.External.Colle.PolyChainSum
import Nivat.External.Colle.ShellSubStrip
import Nivat.External.Colle.LeafAJSelect
import Nivat.External.Colle.ShellRegionJ

/-!
# `shellSubStrip` at the predecessor selection of `ν_{J+1}`

Lane `lane-tower-hbase`, landed round 163.  This file discharges the `shellSubStrip` binder of
`Nivat.Colle35.ChainDataGeom.ofPartsExhaustsInter` (`ChainExhaustInter.lean`) under a
**producer-side reselection** of `ν_{J+1}`, and supplies the reselection itself.

## The selection

`LeafAShellNNext.exists_w_hsweepW` (`LeafAShellNNext.lean:70`) picks `ν_{J+1}` as the ccw
**successor of `J`** inside the fan `E ↑𝒮_φ`, i.e. with the tag `Arc _ J ν_{J+1} = ∅`.
`exists_w_hsweepW_pred` below picks the ccw **predecessor of `n_ℓ`** instead, i.e. with the tag
`Arc _ ν_{J+1} (-ℓ) = ∅`, keeping every other output of that lemma unchanged: the same `ν_{J+1} ∈
E ↑𝒮_φ`, the same `0 < det J ν_{J+1}`, the same `w = -(dir ν_{J+1})`, the same
`dot (-J) w < 0`.  Both selections live in `Arc _ J n_ℓ ∪ {n_ℓ}`; they differ only in which end
of that arc is taken, and they coincide whenever that arc has at most one element.

## Why the reselection

`w = -(dir ν_{J+1})` escapes the half-strip `halfStrip (B i) v⃗_ℓ` along a normal `ν` exactly when
`dot ν v⃗_ℓ ≤ 0 < dot ν w`, i.e. (with `v⃗_ℓ = dir (-n_ℓ)`) when `-ν ∈ Arc _ ν_{J+1} n_ℓ` or
`ν = -n_ℓ`.  The tag `Arc _ ν_{J+1} n_ℓ = ∅` removes the first family outright
(`no_strict_wall_escape`), leaving `ν = -n_ℓ` as the only escaping wall
(`escaping_wall_eq_neg_nl`), and that one is closed by the level bound `cz ≤ dot n_ℓ ·` that
`Â_∞` carries.

## The positive half of the strip

"No normal escapes" is a family of half-plane bounds, while `halfStrip B v⃗_ℓ = B + ℕ·v⃗_ℓ` is not
a half-plane intersection on the nose.  The bridge is already in the tree:
`LaneCdSubstrip.reachSet_eq_hrep_of_E` (`ShellSubStrip.lean` §12) is the H-representation

> `z ∈ halfStrip (B i) v⃗_ℓ ↔ ∀ ν ∈ E (B i), dot ν v⃗_ℓ ≤ 0 → dot ν z ≤ suppVal (B i) ν`,

`Colle35.halfStrip B v⃗_ℓ` and `ShellLine.reachSet B v⃗_ℓ` being the same term (`Lemma35.lean:404`,
`ShellLine.lean:35`).

⚠ **Not covered**: the degenerate branch `ν_{J+1} = n_ℓ` of `exists_nnextJ_pred` (there
`0 < det ν_{J+1} n_ℓ` is false, and `w = v⃗_ℓ`).  It does not need to be covered here:
`LaneCdSubstrip.shellSubStrip_of_w_eq_vl_of_max` (`ShellSubStrip.lean:299`) closes the binder
outright on that branch.

⚠ **Not settled here**: whether the sibling binder `shellEnv` (`ChainExhaustInter.lean`) survives
the reselection.  That is `lane-leafa-shell`'s object; his `wedge_eq_J` consumes the *successor*
tag `Arc _ J ν_{J+1} = ∅` verbatim.
-/

set_option autoImplicit false

namespace Nivat.ShellSubStripPred

open Nivat Nivat.LE2 Nivat.MaxEnv Nivat.Colle35 Nivat.PolyChainSum

/-! ## §1.  The wall condition, read off the fan

`dot ν (-(dir ν₀)) = -det ν₀ ν` is `Nivat.LaneCdFan.dot_neg_dir` (`ShellSubStrip.lean:2669`);
it is used unchanged below rather than restated. -/

/-- **One tag removes every strict wall at once.**  If `Arc ν₀ (-ℓ) = ∅` — i.e. `ν₀` is the ccw
**predecessor** of `-ℓ`, not merely the successor of `J` — then `w := -(dir ν₀)` has the right
sign against *every* normal of `E S` that is a strict wall of `halfStrip B v⃗_ℓ`, the floor normal
`ℓ` itself excepted; that one is handled by the level bound `cz ≤ dot n_ℓ ·`.

Only the `±`-symmetry of `E S` is used (`Colle35.Sphi_negSymm`, `DecompData.lean:417`: `E ↑𝒮_φ`
is the edge-normal set of a zonotope, hence `±`-symmetric). -/
theorem wall_of_arc_empty {S : Set (ℤ × ℤ)} {hfin : S.Finite} {ℓ ν₀ ν : ℤ × ℤ}
    (hsym : ∀ μ ∈ E S, -μ ∈ E S) (harc : Arc hfin ν₀ (-ℓ) = ∅)
    (hν : ν ∈ E S) (hstrict : det ℓ ν < 0) :
    dot ν (-(dir ν₀)) ≤ 0 := by
  rw [Nivat.LaneCdFan.dot_neg_dir]
  by_contra hpos
  have hlt : det ν₀ ν < 0 := by linarith
  have hmem : (-ν) ∈ E S := hsym ν hν
  have h1 : (0 : ℤ) < det ν₀ (-ν) := by
    have : det ν₀ (-ν) = - det ν₀ ν := by
      simp only [det, Prod.fst_neg, Prod.snd_neg]; ring
    rw [this]; linarith
  have h2 : (0 : ℤ) < det (-ν) (-ℓ) := by
    have : det (-ν) (-ℓ) = - det ℓ ν := by
      simp only [det, Prod.fst_neg, Prod.snd_neg]; ring
    rw [this]; linarith
  have : (-ν) ∈ Arc hfin ν₀ (-ℓ) := mem_Arc.mpr ⟨hmem, h1, h2⟩
  rw [harc] at this
  exact absurd this (Finset.notMem_empty _)

/-- The floor normal `+n_ℓ` is the one exception to `wall_of_arc_empty`, and it does **not**
escape: at `ν := -ℓ` one has `dot (-ℓ) w = -det ν₀ (-ℓ) = -det ℓ ν₀ < 0`, which is
`exists_w_hsweepW`'s own `0 < det J ν_{J+1}` chained past `0 < det ℓ J`. -/
theorem wall_at_nl {ℓ ν₀ : ℤ × ℤ} (h : (0 : ℤ) < det ℓ ν₀) :
    dot (-ℓ) (-(dir ν₀)) < 0 := by
  rw [Nivat.LaneCdFan.dot_neg_dir]
  have : det ν₀ (-ℓ) = det ℓ ν₀ := by
    simp only [det, Prod.fst_neg, Prod.snd_neg]; ring
  rw [this]; linarith

/-! ## §2.  The producer fix: `ν_{J+1}` := the ccw predecessor of `n_ℓ` -/

/-- `Arc n n = ∅`: no normal is both strictly ccw of `n` and strictly ccw *to* `n`. -/
theorem arc_self_empty {S : Set (ℤ × ℤ)} (hfin : S.Finite) (n : ℤ × ℤ) :
    Arc hfin n n = ∅ := by
  classical
  by_contra hne
  obtain ⟨μ, hμ⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  obtain ⟨-, h1, h2⟩ := mem_Arc.mp hμ
  have hs : det μ n = - det n μ := det_skew μ n
  omega

/-- **The repaired selection.**  `ν_{J+1}` is the ccw predecessor of `n_ℓ` inside `Arc J n_ℓ`, or
`n_ℓ` itself when that arc is empty.  Both output tags survive: `0 < det J ν_{J+1}` (so
`ShellRegionJ.hsweepW_of_fan_adjacent` still gives `hsweepW`) and `Arc ν_{J+1} n_ℓ = ∅` (so
`wall_of_arc_empty` kills every strict wall).  One call to `LeafAJSelect.exists_fan_pred`
(`LeafAJSelect.lean:803`) with its endpoint slots instantiated `ℓ := J`, `J := n_ℓ`. -/
theorem exists_nnextJ_pred {Sphi : Finset (ℤ × ℤ)} {J nℓ : ℤ × ℤ}
    (hnlE : nℓ ∈ E (↑Sphi : Set (ℤ × ℤ))) (hJE : J ∈ E (↑Sphi : Set (ℤ × ℤ)))
    (hJnl : 0 < det J nℓ) :
    ∃ νJ1, νJ1 ∈ E (↑Sphi : Set (ℤ × ℤ)) ∧ 0 < det J νJ1 ∧
      Arc (Sphi.finite_toSet) νJ1 nℓ = ∅ ∧
      (νJ1 = nℓ ∨ νJ1 ∈ Arc (Sphi.finite_toSet) J nℓ) := by
  classical
  rcases (Arc (Sphi.finite_toSet) J nℓ).eq_empty_or_nonempty with hTe | hTne
  · exact ⟨nℓ, hnlE, hJnl, arc_self_empty _ nℓ, Or.inl rfl⟩
  · obtain ⟨ν, hνE, -, hempty, hor⟩ :=
      Nivat.LeafAJSelect.exists_fan_pred (Sphi := Sphi) hJE hnlE hJnl
    rcases hor with rfl | hmem
    · exact absurd hempty (Finset.nonempty_iff_ne_empty.mp hTne)
    · exact ⟨ν, hνE, (mem_Arc.mp hmem).2.1, hempty, Or.inr hmem⟩

/-- **`exists_w_hsweepW`, with the predecessor selection.**  Same shape as
`LeafAShellNNext.exists_w_hsweepW` (`LeafAShellNNext.lean:70`) — same binders, same `w`, same
`dot (-J) w < 0` — with the fan tag `Arc _ J ν_{J+1} = ∅` traded for `Arc _ ν_{J+1} (-ℓ) = ∅`.
The `0 < det J (-ℓ)` that the selection needs is `0 < det ℓ J` rewritten, exactly as in
`exists_nnextJ` (`LeafAShellNNext.lean:43-46`). -/
theorem exists_w_hsweepW_pred {Sphi : Finset (ℤ × ℤ)} {ℓ J : ℤ × ℤ}
    (hnegℓE : (-ℓ) ∈ E (↑Sphi : Set (ℤ × ℤ))) (hJE : J ∈ E (↑Sphi : Set (ℤ × ℤ)))
    (hℓJ : 0 < det ℓ J) :
    ∃ νJ1 w : ℤ × ℤ, νJ1 ∈ E (↑Sphi : Set (ℤ × ℤ)) ∧ 0 < det J νJ1 ∧
      Arc (Sphi.finite_toSet) νJ1 (-ℓ) = ∅ ∧
      (νJ1 = -ℓ ∨ νJ1 ∈ Arc (Sphi.finite_toSet) J (-ℓ)) ∧
      w = -(dir νJ1) ∧ dot (-J) w < 0 := by
  have hJnegℓ : 0 < det J (-ℓ) := by
    have h1 : det J (-ℓ) = -det J ℓ := det_neg_right J ℓ
    have h2 : det J ℓ = -det ℓ J := det_skew J ℓ
    omega
  obtain ⟨νJ1, hE, hpos, hempty, hor⟩ :=
    exists_nnextJ_pred (Sphi := Sphi) hnegℓE hJE hJnegℓ
  exact ⟨νJ1, -(dir νJ1), hE, hpos, hempty, hor, rfl,
    Nivat.ShellRegionJ.hsweepW_of_fan_adjacent J νJ1 hpos⟩

/-- **What the repaired selection buys, stated on `v⃗_ℓ` and `w` directly.**  Under
`Arc ν_{J+1} n_ℓ = ∅`, no normal of `E S` is both a strict wall of `halfStrip B v⃗_ℓ` and an escape
direction for `w`.  This is §1's `wall_of_arc_empty` with `ℓ := -n_ℓ`, so that `-ℓ = n_ℓ`,
`v⃗_ℓ = dir (-n_ℓ)` and `det (-n_ℓ) ν < 0 ↔ dot ν v⃗_ℓ < 0` are the same statement. -/
theorem no_strict_wall_escape {S : Set (ℤ × ℤ)} {hfin : S.Finite} {nℓ νJ1 vl w ν : ℤ × ℤ}
    (hsym : ∀ μ ∈ E S, -μ ∈ E S) (harc : Arc hfin νJ1 nℓ = ∅)
    (hvl : vl = dir (-nℓ)) (hw : w = -(dir νJ1))
    (hν : ν ∈ E S) (hwall : dot ν vl < 0) :
    dot ν w ≤ 0 := by
  have hstrict : det (-nℓ) ν < 0 := by
    rw [hvl, dot_dir_right] at hwall; exact hwall
  have harc' : Arc hfin νJ1 (-(-nℓ)) = ∅ := by rw [neg_neg]; exact harc
  rw [hw]
  exact wall_of_arc_empty (hfin := hfin) hsym harc' hν hstrict

/-! ## §3.  `-n_ℓ` is the only escaping wall left -/

/-- **The surviving escaping wall is `-n_ℓ`.**  §2 removes every strict wall (`dot ν v⃗_ℓ < 0`);
the non-strict ones (`dot ν v⃗_ℓ = 0`) are `ν = ±n_ℓ` by primitivity, and of those `+n_ℓ` does not
escape (`wall_at_nl`).

Binders: `hsym` is `Colle35.Sphi_negSymm` (`DecompData.lean:417`); `harc` is §2's output tag;
`hJnl : 0 < det ν_{J+1} n_ℓ` is the second `Arc` component of `exists_nnextJ_pred`'s
non-degenerate branch; `hνprim` / `hnlprim` are `IsEdge`'s `Prim` field and the bundle's
`hprim`. -/
theorem escaping_wall_eq_neg_nl {S : Set (ℤ × ℤ)} {hfin : S.Finite} {nℓ νJ1 vl w ν : ℤ × ℤ}
    (hsym : ∀ μ ∈ E S, -μ ∈ E S) (harc : Arc hfin νJ1 nℓ = ∅)
    (hvl : vl = dir (-nℓ)) (hw : w = -(dir νJ1))
    (hnlprim : Primitive nℓ) (hνprim : Primitive ν) (hJnl : 0 < det νJ1 nℓ)
    (hν : ν ∈ E S) (hwall : dot ν vl ≤ 0) (hesc : 0 < dot ν w) :
    ν = -nℓ := by
  have hneg : det (-nℓ) ν = - det nℓ ν := by
    simp only [det, Prod.fst_neg, Prod.snd_neg]; ring
  have hdotvl : dot ν vl = - det nℓ ν := by rw [hvl, dot_dir_right, hneg]
  have hd : det nℓ ν = 0 := by
    rcases lt_or_eq_of_le (by omega : (0 : ℤ) ≤ det nℓ ν) with hlt | heq
    · exact absurd (no_strict_wall_escape (hfin := hfin) hsym harc hvl hw hν (by omega)) (by omega)
    · omega
  rcases eq_or_eq_neg_of_det_eq_zero hnlprim hνprim hd with hp | h
  · exfalso
    have hJ : (0 : ℤ) < det (-nℓ) νJ1 := by
      have h1 : det nℓ νJ1 = - det νJ1 nℓ := det_skew nℓ νJ1
      have h2 : det (-nℓ) νJ1 = - det nℓ νJ1 := by
        simp only [det, Prod.fst_neg, Prod.snd_neg]; ring
      omega
    have hlt := wall_at_nl (ℓ := -nℓ) (ν₀ := νJ1) hJ
    rw [neg_neg] at hlt
    rw [hw, hp] at hesc
    omega
  · exact h

/-! ## §4.  `shellSubStrip`'s body

For `z = g + t•w` with `g ∈ Â_i`: `dot ν (z + k_i v⃗_ℓ) = dot ν (g + k_i v⃗_ℓ) + t·dot ν w`, the
first summand is already `≤ suppVal (B i) ν` because `A i ⊆ halfStrip (B i) v⃗_ℓ` (`subStrip`),
and the second is `≤ 0` for every wall except `ν = -n_ℓ` (§2/§3).  At `ν = -n_ℓ` the bound is
the level bound instead: `suppVal (B i) (-n_ℓ) = -cz` by item (i) (`B i` sits in `ℋ(ℓ^(−))` **and
touches its boundary line**, `b3_colle2.txt:474`), while `z ∈ Ainf ⊆ {cz ≤ dot n_ℓ ·}` and
`dot n_ℓ v⃗_ℓ = 0` give `dot (-n_ℓ) (z + k_i v⃗_ℓ) = -dot n_ℓ z ≤ -cz`.

Every binder is free at the call site:
* `hBfin hBne harea hlc hnlE hnnlE hEsub` — from `envB i : EnvOf ↑𝒮_φ (B i)`
  (`Enveloped.finite`, `Enveloped.E_eq` `LatticeEdges.lean:1657`) and `n_ℓ, -n_ℓ ∈ E ↑𝒮_φ`;
* `hnlprim hvlprim hperp` — `ofPartsExhaustsInter`'s `hprim`, `Primitive vl`, `hperp`;
* `hsym` — `Colle35.Sphi_negSymm` (`DecompData.lean:417`);
* `harc hvl hw hJnl` — §2's selection (`exists_nnextJ_pred`, non-degenerate branch);
* `hsubA` — `subStrip`, i.e. `Colle35.subStrip_of_max` from `maxA i`;
* `hfloorLow`/`hfloorAtt` — item (i), via `floor_of_itemI` (§6);
* `hlevAinf` — `hexh` plus `dot n_ℓ v⃗_ℓ = 0`. -/

/-- **`shellSubStrip`'s body, proved at one index `i`.**  See the section docstring for where
each binder comes from.  The `ε`/`i₀`/guard prefix of the binder is not used: the statement
holds for every `i` and every ambient `Ainf` satisfying the level bound. -/
theorem shellSubStrip_body_of_pred {A B : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ}
    {Ainf S : Set (ℤ × ℤ)} {hfinS : S.Finite} {nℓ νJ1 vl w : ℤ × ℤ} {cz : ℤ} {i : ℕ}
    (hBfin : (B i).Finite) (hBne : (B i).Nonempty) (harea : PosArea (B i))
    (hlc : IsLatticeConvexRegion (B i))
    (hnlprim : Prim nℓ) (hvlprim : Prim vl) (hperp : dot nℓ vl = 0)
    (hnlE : nℓ ∈ E (B i)) (hnnlE : -nℓ ∈ E (B i)) (hEsub : ∀ ν ∈ E (B i), ν ∈ E S)
    (hsym : ∀ μ ∈ E S, -μ ∈ E S) (harc : Arc hfinS νJ1 nℓ = ∅)
    (hvl : vl = dir (-nℓ)) (hw : w = -(dir νJ1)) (hJnl : 0 < det νJ1 nℓ)
    (hsubA : A i ⊆ Nivat.Colle35.halfStrip (B i) vl)
    (hfloorLow : ∀ b ∈ B i, cz ≤ dot nℓ b) (hfloorAtt : ∃ b ∈ B i, dot nℓ b = cz)
    (hlevAinf : ∀ z ∈ Ainf, cz ≤ dot nℓ z) :
    Nivat.ShellMink.shellInter (Nivat.Colle35.hatOf A kk vl i) Ainf w ⊆
      {z | z + (kk i : ℤ) • vl ∈ Nivat.Colle35.halfStrip (B i) vl} := by
  have hrep : Nivat.Colle35.halfStrip (B i) vl =
      {z | ∀ n ∈ E (B i), dot n vl ≤ 0 → dot n z ≤ suppVal (B i) n} :=
    Nivat.LaneCdSubstrip.reachSet_eq_hrep_of_E hBfin hBne harea hlc hnlprim hvlprim hperp
      hnlE hnnlE
  rintro z ⟨⟨g, hg, t, rfl⟩, hzAinf⟩
  simp only [Set.mem_setOf_eq, hrep]
  intro ν hνE hνvl
  have hXstrip : g + (kk i : ℤ) • vl ∈ Nivat.Colle35.halfStrip (B i) vl := hsubA hg
  rw [hrep] at hXstrip
  have hXbound : dot ν (g + (kk i : ℤ) • vl) ≤ suppVal (B i) ν := hXstrip ν hνE hνvl
  have hsplit : dot ν (g + (t : ℤ) • w + (kk i : ℤ) • vl)
      = dot ν (g + (kk i : ℤ) • vl) + (t : ℤ) * dot ν w := by
    rw [dot_add, dot_add, dot_add, Nivat.ColleReg.dot_zsmul_right]; ring
  rcases le_or_gt (dot ν w) 0 with hwle | hwgt
  · have hle : (t : ℤ) * dot ν w ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg t) hwle
    omega
  · have hνeq : ν = -nℓ :=
      escaping_wall_eq_neg_nl (hfin := hfinS) hsym harc hvl hw
        (prim_iff_primitive.mp hnlprim) (prim_iff_primitive.mp (mem_E_iff.mp hνE).1)
        hJnl (hEsub ν hνE) hνvl hwgt
    subst hνeq
    obtain ⟨b, hbB, hblev⟩ := hfloorAtt
    have hface : b ∈ face (B i) (-nℓ) := by
      refine ⟨hbB, fun y hy => ?_⟩
      have := hfloorLow y hy
      simp only [dot_neg_left]
      omega
    have hsupp : suppVal (B i) (-nℓ) = -cz := by
      rw [suppVal_eq hface, dot_neg_left, hblev]
    have hlev : cz ≤ dot nℓ (g + (t : ℤ) • w) := hlevAinf _ hzAinf
    have hval : dot (-nℓ) (g + (t : ℤ) • w + (kk i : ℤ) • vl)
        = - dot nℓ (g + (t : ℤ) • w) := by
      rw [dot_neg_left, dot_add, Nivat.ColleReg.dot_zsmul_right, hperp]; ring
    omega

/-! ## §5.  The binder, character for character

`shellSubStrip_of_pred` is the `shellSubStrip` binder (`ChainExhaustInter.lean`) with the
guard prefix taken and
discarded (it is not needed: §4 holds for every `i` and every `ε`) and with the tail
`∀ i, i₀ ≤ i →`, which is **stronger** than the binder's `∀ i, max i₀ I₀ ≤ i →` and is trimmed
to it by `le_max_left`.  The ambient level bound is discharged here from `hlevUnion` (`hexh` +
`dot n_ℓ v⃗_ℓ = 0`) and `hnlvJ1 : 0 ≤ dot n_ℓ v_{J+1}` (`ShellSubStrip.lean` §1
`dot_nl_vJ1_nonneg`). -/

/-- **`ofPartsExhaustsInter`'s `shellSubStrip` binder**, at the §2 selection of `ν_{J+1}`. -/
theorem shellSubStrip_of_pred {A B : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ} {S : Set (ℤ × ℤ)}
    {hfinS : S.Finite} {nℓ νJ1 vl w vJ1 nJ : ℤ × ℤ} {cJ cz : ℤ} {Env : Set (ℤ × ℤ) → Prop}
    (hBfin : ∀ i, (B i).Finite) (hBne : ∀ i, (B i).Nonempty) (harea : ∀ i, PosArea (B i))
    (hlc : ∀ i, IsLatticeConvexRegion (B i))
    (hnlprim : Prim nℓ) (hvlprim : Prim vl) (hperp : dot nℓ vl = 0)
    (hnlE : ∀ i, nℓ ∈ E (B i)) (hnnlE : ∀ i, -nℓ ∈ E (B i))
    (hEsub : ∀ i, ∀ ν ∈ E (B i), ν ∈ E S)
    (hsym : ∀ μ ∈ E S, -μ ∈ E S) (harc : Arc hfinS νJ1 nℓ = ∅)
    (hvl : vl = dir (-nℓ)) (hw : w = -(dir νJ1)) (hJnl : 0 < det νJ1 nℓ)
    (hsubA : ∀ i, A i ⊆ Nivat.Colle35.halfStrip (B i) vl)
    (hfloorLow : ∀ i, ∀ b ∈ B i, cz ≤ dot nℓ b)
    (hfloorAtt : ∀ i, ∃ b ∈ B i, dot nℓ b = cz)
    (hlevUnion : ∀ z ∈ ⋃ j, Nivat.Colle35.hatOf A kk vl j, cz ≤ dot nℓ z)
    (hnlvJ1 : 0 ≤ dot nℓ vJ1) :
    ∀ ε i₀ : ℕ, 0 < ε →
      (∀ i, i₀ ≤ i → Env (Nivat.ShellMink.shellInter (Nivat.Colle35.hatOf A kk vl i)
        (Nivat.MaxEnv.shell (⋃ i, Nivat.Colle35.hatOf A kk vl i) vJ1 nJ cJ ε) w)) →
      ∀ i, i₀ ≤ i →
      Nivat.ShellMink.shellInter (Nivat.Colle35.hatOf A kk vl i)
          (Nivat.MaxEnv.shell (⋃ i, Nivat.Colle35.hatOf A kk vl i) vJ1 nJ cJ ε) w ⊆
        {z | z + (kk i : ℤ) • vl ∈ Nivat.Colle35.halfStrip (B i) vl} := by
  intro ε i₀ _ _ i _
  refine shellSubStrip_body_of_pred (hfinS := hfinS) (hBfin i) (hBne i) (harea i) (hlc i)
    hnlprim hvlprim hperp (hnlE i) (hnnlE i) (hEsub i) hsym harc hvl hw hJnl (hsubA i)
    (hfloorLow i) (hfloorAtt i) ?_
  rintro z ⟨g, hg, s, rfl, -⟩
  have h1 : cz ≤ dot nℓ g := hlevUnion g hg
  have h2 : (0 : ℤ) ≤ (s : ℤ) * dot nℓ vJ1 :=
    mul_nonneg (Int.natCast_nonneg s) hnlvJ1
  rw [dot_add, Nivat.ColleReg.dot_zsmul_right]
  omega

/-! ## §6.  The two floor binders are item (i), not new debt

`hfloorLow` / `hfloorAtt` of §4–§5 are exactly Collé's item (i) (`b3_colle2.txt:474`,
«`B_i ∩ ℓ_{B_i} ⊂ ℓ^(−)`»), already encoded as `AItemTwoGrowth.ItemI B n c :
∀ i, face (B i) (-n) ⊆ outerLine n c` with `outerLine n c = {z | dot n z = c - 1}`
(`LatticeEdges.lean:1782`), i.e. `cz = c - 1`.  The nonemptiness side condition is free from
envelopedness (`AItemTwoGrowth.face_nonempty_of_envOf_Sphi`).  So §4/§5 ask for nothing the
chain does not already carry. -/

/-- **Item (i) gives both floor facts.**  `B` lies in `ℋ(ℓ^(−))` and touches its boundary
line. -/
theorem floor_of_itemI {B : Set (ℤ × ℤ)} {nℓ : ℤ × ℤ} {c : ℤ}
    (hI : face B (-nℓ) ⊆ outerLine nℓ c) (hne : (face B (-nℓ)).Nonempty) :
    (∀ b ∈ B, c - 1 ≤ dot nℓ b) ∧ (∃ b ∈ B, dot nℓ b = c - 1) := by
  obtain ⟨b, hb⟩ := hne
  have hlev : dot nℓ b = c - 1 := hI hb
  refine ⟨fun y hy => ?_, ⟨b, hb.1, hlev⟩⟩
  have hle := hb.2 y hy
  rw [dot_neg_left, dot_neg_left] at hle
  omega

end Nivat.ShellSubStripPred
