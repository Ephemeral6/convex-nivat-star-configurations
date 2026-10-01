/-
Copyright (c) 2026. Released under Apache 2.0 license.
Authors: lane-hole3-cone
-/
import Nivat.External.Colle.ShellSubStrip
import Nivat.External.Colle.LeafAJSelect
import Nivat.External.Colle.RegionConvex
import Nivat.External.Colle.CyrKra224
import Nivat.External.Colle.ItemII
import Nivat.External.Colle.SweepOppEdge

/-!
# `hlcT`, wired: `hreachA` + `hreachInf` ⟹ `shellEnv_of_wedge`'s `hlcT`

Lane `lane-hole3-cone`, round 2026-09-24 (team-lead: "现货对现货，先做"; promoted to the main
tree, team-lead approval, round 2026-09-24).  Consumer: `shellEnv_of_wedge`'s `hlcT` binder
(`tmp/wip/lane-leafa-shell-shellenv.lean:740-741`, not yet on the main tree — the integrator
wires the actual call once that file lands):
`∀ i, i₀ ≤ i → IsLatticeConvexRegion (Nivat.LaneCdSite.shellT A kk vl vJ1 nJ w cJ ε i)`.

**No new mathematics here** — the main-tree lemma
`Nivat.LaneCdHlc.isLatticeConvexRegion_shellInter` (`ShellSubStrip.lean:3524-3529`) already
reduces `hlcT` to *exactly* two convexity facts:

* `hreachA i : IsLatticeConvexRegion (reachSet (hatOf A kk vl i) w)`
* `hreachInf : IsLatticeConvexRegion (reachSet (⋃ j, hatOf A kk vl j) vJ1)`

via `shellT_eq` (`ShellSubStrip.lean:3839-3843`, `rfl`) unfolding `shellT` to
`ShellMink.shellInter (hatOf A kk vl i) (MaxEnv.shell (⋃j,…) vJ1 nJ cJ ε) w`, which is
literally `isLatticeConvexRegion_shellInter`'s conclusion shape.  `§1` below is that one-line
bridge, stated generically (any producer of `hreachA`/`hreachInf` plugs in).

`§2` instantiates the bridge with this lane's own already-landed producers, restated here
verbatim (not cross-`tmp/wip`-imported — no established precedent for that import form in
this project, and `check1.sh` is a single-file checker, so restating keeps this file
self-verifying): `reachSet_hatOf_latticeConvex_of_wJ` (`hreachA`, `cw`/`ccw`-orientation-blind
— it only needs `wJ = -dir νJ1`, `νJ1 ∈ E`, `E` negation-symmetric) and
`ahatUnion_reachSet_latticeConvex_of_pinned_cw` (`hreachInf`, the `cw` case) from
`tmp/wip/lane-hole3-cone-hreachInf-cw.lean:61-224`. The `ccw` mirror
(`tmp/wip/lane-shellenv-edgeJ1.lean`'s `ahatUnion_reachSet_latticeConvex_of_pinned_ccw`) plugs
into the same `§1` bridge with the same call shape, since `§1` only consumes the conclusion
type, not which case produced it.

**On the `:517` clipping (team-lead's round-163 check).** `§1`'s conclusion is
`shellT = ShellMink.shellInter (hatOf A kk vl i) (MaxEnv.shell (⋃j,…) vJ1 nJ cJ ε) w`, and
`ShellMink.shellInter Ahat Ainf w := reachSet Ahat w ∩ Ainf` (`ShellMink.lean:508-509`) —
the second factor `Ainf` here is already the *clipped* shell `MaxEnv.shell (⋃j,…) vJ1 nJ cJ ε`,
not the tower `⋃j,…` itself, so the `∩` in `:517`'s `{g - t·v⃗_{ℓ_{J+1}} ∈ Â_∞^{(ε)} : …}` is
present verbatim in `shellT`'s own definition; `§1` does not bypass it. Nor does `hreachInf`
assert an unclipped fact: `isLatticeConvexRegion_shell_of_reach`
(`ShellSubStrip.lean:3516-3520`) proves convexity of `MaxEnv.shell Ainf v n c ε`, and
`MaxEnv.shell`'s own definition (`MaximalEnveloped.lean:564`) carries the floor
`c - ε ≤ dot n z` as a *per-point membership conjunct*, not as a downstream consequence of an
unclipped closure claim — the `hreachInf` hypothesis only asks `reachSet Ainf v` (the raw,
unclipped ray-union) to be lattice-*convex*, a shape fact true of any half-cone regardless of
whether it crosses some external half-plane; `isLatticeConvexRegion_inter_halfPlaneGE`
(`RegionCutGE.lean:24`) then intersects that cone with the floor to get `MaxEnv.shell`'s own
convexity. This is a different statement from `hclosed : ∀ g ∈ ⋃ⱼ Â_j, g + w ∈ ⋃ⱼ Â_j`
(refuted unconditionally, `tmp/hclosed_false.lean`, `Nivat.HclosedFalse.hclosed_false`) — that
claim is about the *tower* being forward-closed under `+w` (an equality/closure assertion that
the floor-punch-through argument kills), whereas `hreachA`/`hreachInf` here only ever assert
*convexity* of a reach set, never closure of a base set under repeated addition. Neither `§1`
nor `§2` binds, uses, or needs `hclosed` anywhere. -/

set_option autoImplicit false

namespace Nivat.LaneHole3ConeHlcTWire

open Nivat Nivat.LE2 Nivat.MaxEnv Nivat.Colle35 Classical

/-! ### §1. The bridge: `hreachA` + `hreachInf` ⟹ `hlcT` -/

/-- **`hlcT`, wired.** Direct corollary of `Nivat.LaneCdHlc.isLatticeConvexRegion_shellInter`
plus `Nivat.LaneCdSite.shellT_eq`; holds for *every* `i` (the `i₀ ≤ i` guard in
`shellEnv_of_wedge`'s binder is never used on this side). -/
theorem hlcT_of_reach
    {A : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ} {vl vJ1 nJ w : ℤ × ℤ} {cJ : ℤ} {ε i₀ : ℕ}
    (hreachA : ∀ i, IsLatticeConvexRegion (Nivat.MaxEnv.reachSet (hatOf A kk vl i) w))
    (hreachInf :
      IsLatticeConvexRegion (Nivat.MaxEnv.reachSet (⋃ j, hatOf A kk vl j) vJ1)) :
    ∀ i, i₀ ≤ i →
      IsLatticeConvexRegion (Nivat.LaneCdSite.shellT A kk vl vJ1 nJ w cJ ε i) := by
  intro i _
  rw [Nivat.LaneCdSite.shellT_eq]
  exact Nivat.LaneCdHlc.isLatticeConvexRegion_shellInter (hreachA i) hreachInf

end Nivat.LaneHole3ConeHlcTWire

#print axioms Nivat.LaneHole3ConeHlcTWire.hlcT_of_reach

/-! ### §2. Fully instantiated: this lane's `hreachA`/`hreachInf` producers plugged in -/

namespace Nivat.LaneHole3ConeHlcTWire

open Nivat Nivat.LE2 Nivat.MaxEnv Nivat.Colle35 Nivat.PolyChain Nivat.PolyChainSum Classical

/-- `dir` is odd (restated locally, matching `lane-hole3-cone-hreachInf-cw.lean`'s
`dir_neg'`). -/
private theorem dir_neg'' (n : ℤ × ℤ) : dir (-n) = -(dir n) := by
  simp only [dir, Prod.fst_neg, Prod.snd_neg, Prod.neg_mk, neg_neg]

/-- **`hreachA`, instantiated**: free from `wJ = -dir νJ1` plus `E`-membership and
negation-symmetry, verbatim `reachSet_hatOf_latticeConvex_of_wJ`
(`tmp/wip/lane-hole3-cone-hreachInf-cw.lean:208-224`) restated in this file's namespace. -/
theorem hreachA_of_wJ
    {Sphi : Finset (ℤ × ℤ)} {A : ℕ → Set (ℤ × ℤ)} {νJ1 wJ : ℤ × ℤ}
    (hSfin : (E (↑Sphi : Set (ℤ × ℤ))).Finite)
    (hAfin : ∀ i, (A i).Finite) (hAne : ∀ i, (A i).Nonempty)
    (hAarea : ∀ i, PosArea (A i)) (hAlc : ∀ i, IsLatticeConvexRegion (A i))
    (hAenv : ∀ i, Enveloped (↑Sphi : Set (ℤ × ℤ)) (A i))
    (hνJ1E : νJ1 ∈ E (↑Sphi : Set (ℤ × ℤ)))
    (hnegSymm : ∀ n ∈ E (↑Sphi : Set (ℤ × ℤ)), -n ∈ E (↑Sphi : Set (ℤ × ℤ)))
    (hwJ_eq : wJ = -dir νJ1) :
    ∀ i, IsLatticeConvexRegion (Nivat.MaxEnv.reachSet (A i) wJ) := by
  intro i
  have hn : (-νJ1) ∈ E (↑Sphi : Set (ℤ × ℤ)) := hnegSymm νJ1 hνJ1E
  have h_n : -(-νJ1) ∈ E (↑Sphi : Set (ℤ × ℤ)) := by rwa [neg_neg]
  have hwdir : wJ = dir (-νJ1) := by rw [hwJ_eq, dir_neg'']
  rw [hwdir]
  exact Nivat.LaneCdOppEdge.isLatticeConvexRegion_reachSet_dir_of_mem_E hSfin (hAfin i)
    (hAne i) (hAarea i) (hAlc i) (hAenv i) hn h_n

/-- **`a₀_mem`/`prev_mem`, `cw` case** — inlined verbatim from `a0_prev_mem_of_pinned_cw`
(`tmp/wip/lane-hole3-cone-hreachInf-cw.lean:61-106`; not imported cross-`tmp/wip` since that
import form has no established precedent in this project, so the already-verified proof is
restated here instead). -/
theorem a0_prev_mem_of_pinned_cw
    {Sphi : Finset (ℤ × ℤ)} {Ahat : ℕ → Set (ℤ × ℤ)} {J nprevJ g_J vJ1 : ℤ × ℤ}
    (hfin : ∀ i, (Ahat i).Finite)
    (hlc : ∀ i, IsLatticeConvexRegion (Ahat i))
    (henv : ∀ i, Enveloped (↑Sphi : Set (ℤ × ℤ)) (Ahat i))
    (hSfin : (E (↑Sphi : Set (ℤ × ℤ))).Finite) (hSarea : PosArea (↑Sphi : Set (ℤ × ℤ)))
    (hnprevE : nprevJ ∈ E (↑Sphi : Set (ℤ × ℤ))) (hJE : J ∈ E (↑Sphi : Set (ℤ × ℤ)))
    (hdet : 0 < det J nprevJ)
    (hempty : Arc (Sphi.finite_toSet) J nprevJ = ∅)
    {σ : ℕ → ℕ} {i₀ : ℕ}
    (hg : faceStart (Ahat (σ i₀)) J + (faceLen (Ahat (σ i₀)) J : ℤ) • dir J = g_J)
    (hvJ1 : vJ1 = -dir nprevJ) :
    g_J ∈ ⋃ i, Ahat i ∧ g_J - vJ1 ∈ ⋃ i, Ahat i := by
  have hEnp : nprevJ ∈ E (Ahat (σ i₀)) := by
    rw [Nivat.AhatEnv.E_eq_of_enveloped hSfin hSarea (henv (σ i₀))]; exact hnprevE
  have hEJ : J ∈ E (Ahat (σ i₀)) := by
    rw [Nivat.AhatEnv.E_eq_of_enveloped hSfin hSarea (henv (σ i₀))]; exact hJE
  have hadj : ∀ μ ∈ E (Ahat (σ i₀)), ¬ (0 < det J μ ∧ 0 < det μ nprevJ) := by
    intro μ hμ hcon
    have hμE : μ ∈ E (↑Sphi : Set (ℤ × ℤ)) := by
      rw [← Nivat.AhatEnv.E_eq_of_enveloped hSfin hSarea (henv (σ i₀))]; exact hμ
    have hμmem : μ ∈ Arc (Sphi.finite_toSet) J nprevJ :=
      mem_Arc.mpr ⟨hμE, hcon.1, hcon.2⟩
    rw [hempty] at hμmem
    exact absurd hμmem (by simp)
  have hshared := adjacent_shared_vertex (hfin (σ i₀)) (hlc (σ i₀)) hEJ hEnp hdet hadj
  rw [hg] at hshared
  refine ⟨?_, ?_⟩
  · have hmem : g_J ∈ face (Ahat (σ i₀)) nprevJ :=
      hshared.symm ▸ faceStart_mem (hfin (σ i₀)) hEnp
    exact Set.mem_iUnion.mpr ⟨σ i₀, face_subset _ _ hmem⟩
  · have hlen1 : 1 ≤ faceLen (Ahat (σ i₀)) nprevJ := one_le_faceLen (hfin (σ i₀)) hEnp
    have hstep : faceStart (Ahat (σ i₀)) nprevJ + (1 : ℤ) • dir nprevJ
        ∈ face (Ahat (σ i₀)) nprevJ := by
      apply mem_face_of_between (hlc (σ i₀)) (s := 0) (t := 1)
        (u := faceLen (Ahat (σ i₀)) nprevJ)
      · exact Nat.zero_le _
      · exact_mod_cast hlen1
      · simpa using faceStart_mem (hfin (σ i₀)) hEnp
      · exact faceEnd_mem (hlc (σ i₀)) (hfin (σ i₀)) hEnp
    have heq : faceStart (Ahat (σ i₀)) nprevJ + (1 : ℤ) • dir nprevJ = g_J - vJ1 := by
      rw [hvJ1, one_smul, hshared]
      abel
    rw [heq] at hstep
    exact Set.mem_iUnion.mpr ⟨σ i₀, face_subset _ _ hstep⟩

/-- **`hreachInf`, `cw` case, inlined** from `ahatUnion_reachSet_latticeConvex_of_pinned_cw`
(`tmp/wip/lane-hole3-cone-hreachInf-cw.lean:124-186`), same reason as above. -/
theorem hreachInf_of_pinned_cw
    {Sphi : Finset (ℤ × ℤ)} {T : ℕ → Set (ℤ × ℤ)} {J nprevJ g_J vJ1 eJ nJ : ℤ × ℤ} {cJ : ℤ}
    (hfin : ∀ i, (T i).Finite)
    (hlc : ∀ i, IsLatticeConvexRegion (T i))
    (henv : ∀ i, Enveloped (↑Sphi : Set (ℤ × ℤ)) (T i))
    (hSfin : (E (↑Sphi : Set (ℤ × ℤ))).Finite) (hSarea : PosArea (↑Sphi : Set (ℤ × ℤ)))
    (hnprevE : nprevJ ∈ E (↑Sphi : Set (ℤ × ℤ))) (hJE : J ∈ E (↑Sphi : Set (ℤ × ℤ)))
    (hdet : 0 < det J nprevJ)
    (hempty : Arc (Sphi.finite_toSet) J nprevJ = ∅)
    {σ : ℕ → ℕ} {i₀ : ℕ}
    (hg : faceStart (T (σ i₀)) J + (faceLen (T (σ i₀)) J : ℤ) • dir J = g_J)
    (hvJ1 : vJ1 = -dir nprevJ)
    (hAhatConvU : IsLatticeConvexRegion (⋃ i, T i))
    (hhp_all : ∀ i, T i ⊆ Nivat.CK224.halfPlaneGE nJ cJ)
    (hswept_all : Nivat.MaxEnv.SweptClosed (⋃ i, T i) vJ1 nJ cJ)
    (hcJ_def : cJ = dot nJ g_J)
    (heJ_prim : Primitive eJ)
    (hray : ∀ k : ℕ, g_J + (k : ℤ) • eJ ∈ ⋃ i, T i)
    (hdoteJ : dot nJ eJ = 0)
    (hsweep : dot nJ vJ1 < 0)
    (hsupp_prev_U : ∀ z ∈ ⋃ i, T i, dot nprevJ z ≤ dot nprevJ g_J)
    (hnpvJ1 : dot nprevJ vJ1 = 0)
    (hnpeJ : dot nprevJ eJ < 0) :
    IsLatticeConvexRegion (Nivat.MaxEnv.reachSet (⋃ i, T i) vJ1) := by
  obtain ⟨ha₀mem, hprevmem⟩ :=
    a0_prev_mem_of_pinned_cw (Ahat := T) (Sphi := Sphi) hfin hlc henv hSfin hSarea
      hnprevE hJE hdet hempty (σ := σ) (i₀ := i₀) hg hvJ1
  have hnJ1ne : (-nprevJ : ℤ × ℤ) ≠ 0 := by
    intro h0
    have h0' : nprevJ = 0 := by
      have := congrArg (fun z : ℤ × ℤ => -z) h0
      simpa using this
    rw [h0', Nivat.LE2.dot_zero_left] at hnpeJ
    exact absurd hnpeJ (by norm_num)
  have hdotnJ1v : dot (-nprevJ) vJ1 = 0 := by
    rw [Nivat.LE2.dot_neg_left, hnpvJ1]; ring
  have hsupport : ∀ g ∈ ⋃ i, T i, dot (-nprevJ) g_J ≤ dot (-nprevJ) g := by
    intro g hg'
    rw [Nivat.LE2.dot_neg_left, Nivat.LE2.dot_neg_left]
    exact neg_le_neg (hsupp_prev_U g hg')
  have e : Nivat.Colle35.EdgeJ1Data (⋃ i, T i) vJ1 nJ cJ :=
    { a₀ := g_J
      a₀_mem := ha₀mem
      a₀_on := hcJ_def.symm
      prev_mem := hprevmem
      nJ1 := -nprevJ
      dot_nJ1_v := hdotnJ1v
      nJ1_ne := hnJ1ne
      support := hsupport }
  have hAhalf : ∀ g ∈ ⋃ i, T i, cJ ≤ dot nJ g := by
    intro g hg'
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hg'
    exact hhp_all i hi
  have hzero : Nivat.MaxEnv.reachSet (⋃ i, T i) vJ1 ∩ Nivat.CK224.halfPlaneGE nJ cJ
      ⊆ ⋃ i, T i := by
    rintro z ⟨⟨g, hg', t, rfl⟩, hlev⟩
    exact hswept_all g hg' t hlev
  have hrec : ∀ g ∈ (⋃ i, T i), g + eJ ∈ ⋃ i, T i :=
    Nivat.Colle35.rec_of_ray hAhatConvU hray
  exact Nivat.Colle35.EdgeJ1Data.isLatticeConvexRegion_reachSet e hAhatConvU hAhalf hzero
    hrec hdoteJ hsweep heJ_prim.ne_zero

/-- **`hlcT`, fully assembled**: plug `hreachA_of_wJ` and `hreachInf_of_pinned_cw` (both
above, `cw` case) into the `§1` bridge. Binder list is exactly the union of both producers'
hypotheses; nothing added, nothing weakened. -/
theorem hlcT_of_pinned_cw
    {Sphi : Finset (ℤ × ℤ)} {A : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ} {vl : ℤ × ℤ}
    {J nprevJ g_J vJ1 eJ nJ w : ℤ × ℤ} {cJ : ℤ} {ε i₀ : ℕ}
    -- `hreachA_of_wJ`'s hypotheses, specialized to `T i := hatOf A kk vl i`:
    (hSfin : (E (↑Sphi : Set (ℤ × ℤ))).Finite)
    (hAfin : ∀ i, (hatOf A kk vl i).Finite) (hAne : ∀ i, (hatOf A kk vl i).Nonempty)
    (hAarea : ∀ i, PosArea (hatOf A kk vl i))
    (hAlc : ∀ i, IsLatticeConvexRegion (hatOf A kk vl i))
    (hAenv : ∀ i, Enveloped (↑Sphi : Set (ℤ × ℤ)) (hatOf A kk vl i))
    (hνJ1E : nprevJ ∈ E (↑Sphi : Set (ℤ × ℤ)))
    (hnegSymm : ∀ n ∈ E (↑Sphi : Set (ℤ × ℤ)), -n ∈ E (↑Sphi : Set (ℤ × ℤ)))
    (hwJ_eq : w = -dir nprevJ)
    -- `hreachInf_of_pinned_cw`'s remaining hypotheses:
    (hJE : J ∈ E (↑Sphi : Set (ℤ × ℤ)))
    (hSarea : PosArea (↑Sphi : Set (ℤ × ℤ)))
    (hdet : 0 < det J nprevJ)
    (hempty : Arc (Sphi.finite_toSet) J nprevJ = ∅)
    {σ : ℕ → ℕ} {i₀' : ℕ}
    (hg : faceStart (hatOf A kk vl (σ i₀')) J
      + (faceLen (hatOf A kk vl (σ i₀')) J : ℤ) • dir J = g_J)
    (hvJ1 : vJ1 = -dir nprevJ)
    (hAhatConvU : IsLatticeConvexRegion (⋃ i, hatOf A kk vl i))
    (hhp_all : ∀ i, hatOf A kk vl i ⊆ Nivat.CK224.halfPlaneGE nJ cJ)
    (hswept_all : Nivat.MaxEnv.SweptClosed (⋃ i, hatOf A kk vl i) vJ1 nJ cJ)
    (hcJ_def : cJ = dot nJ g_J)
    (heJ_prim : Primitive eJ)
    (hray : ∀ k : ℕ, g_J + (k : ℤ) • eJ ∈ ⋃ i, hatOf A kk vl i)
    (hdoteJ : dot nJ eJ = 0)
    (hsweep : dot nJ vJ1 < 0)
    (hsupp_prev_U : ∀ z ∈ ⋃ i, hatOf A kk vl i, dot nprevJ z ≤ dot nprevJ g_J)
    (hnpvJ1 : dot nprevJ vJ1 = 0)
    (hnpeJ : dot nprevJ eJ < 0) :
    ∀ i, i₀ ≤ i →
      IsLatticeConvexRegion (Nivat.LaneCdSite.shellT A kk vl vJ1 nJ w cJ ε i) :=
  hlcT_of_reach
    (hreachA_of_wJ (Sphi := Sphi) (A := fun i => hatOf A kk vl i) hSfin hAfin hAne hAarea
      hAlc hAenv hνJ1E hnegSymm hwJ_eq)
    (hreachInf_of_pinned_cw (T := fun i => hatOf A kk vl i) (Sphi := Sphi) hAfin hAlc hAenv
      hSfin hSarea hνJ1E hJE hdet hempty (σ := σ) (i₀ := i₀') hg hvJ1 hAhatConvU hhp_all
      hswept_all hcJ_def heJ_prim hray hdoteJ hsweep hsupp_prev_U hnpvJ1 hnpeJ)

/-! ### §3. `ccw` twin

Team-lead assignment, round 2026-09-24 ("授权你写 `hlcT_of_pinned_ccw`"): the shared `J`-package
existential in `tmp/wip/LeafAAssemble.lean`'s `hadj_or` binder is an *unsplit* disjunction with
zero downstream consumers (confirmed independently by both lane-hole3-cone and team-lead via
repo-wide `grep -rn "hadj_or"`, `OPEN.md #21`) — so a caller reaching the `shellEnv`/`bottom`
obligations may be in either the `cw` disjunct (`0 < det J nprevJ`, §2 above) or the `ccw`
disjunct (`0 < det nprevJ J`), and only the latter had no main-tree witness for the
`hg`/`hdet`/`hempty`/`adjacent_shared_vertex` route (as opposed to `ShellHreachInf.lean`'s
abstract-`R` route, which lane-leafa-shell already covers both signs of — this section supplies
the *other* interface, for whichever consumer already has `σ`/`i₀`/`hg`-shaped facts rather than
abstract-`R` ones).

Mirrors §2 exactly, swapping the three orientation-carrying binders:
* `hdet : 0 < det J nprevJ` (cw) ↦ `hdet : 0 < det nprevJ J` (ccw)
* `hempty : Arc (Sphi.finite_toSet) J nprevJ = ∅` (cw) ↦
  `hempty : Arc (Sphi.finite_toSet) nprevJ J = ∅` (ccw)
* `hvJ1 : vJ1 = -dir nprevJ` (cw) ↦ `hvJ1 : vJ1 = dir nprevJ` (ccw)

and, since `adjacent_shared_vertex`'s two arguments swap roles, `hg`'s statement swaps from
"`g_J` is `J`'s own `faceEnd`" (cw) to "`g_J` is `nprevJ`'s own `faceEnd`" (ccw) — not an added
quantifier, the same "`g_J` closes off the earlier-fan-edge's face" fact stated against whichever
edge is *first* in the `hadj_or` disjunct actually in force.  `hreachA_of_wJ` (§2) is reused
unchanged: it is orientation-blind. -/

/-- **`a₀_mem`/`prev_mem`, `ccw` case.** Mirror of `a0_prev_mem_of_pinned_cw`:
`adjacent_shared_vertex` is invoked with `(nprevJ, J)` instead of `(J, nprevJ)`, so the shared
vertex comes out as `faceStart T nprevJ + faceLen T nprevJ • dir nprevJ = faceStart T J`, i.e.
`g_J` (pinned by `hg` to `nprevJ`'s own `faceEnd`) equals `J`'s `faceStart` — the mirror image
of the `cw` case, where `g_J` (pinned to `J`'s `faceEnd`) equals `nprevJ`'s `faceStart`. -/
theorem a0_prev_mem_of_pinned_ccw
    {Sphi : Finset (ℤ × ℤ)} {Ahat : ℕ → Set (ℤ × ℤ)} {J nprevJ g_J vJ1 : ℤ × ℤ}
    (hfin : ∀ i, (Ahat i).Finite)
    (hlc : ∀ i, IsLatticeConvexRegion (Ahat i))
    (henv : ∀ i, Enveloped (↑Sphi : Set (ℤ × ℤ)) (Ahat i))
    (hSfin : (E (↑Sphi : Set (ℤ × ℤ))).Finite) (hSarea : PosArea (↑Sphi : Set (ℤ × ℤ)))
    (hnprevE : nprevJ ∈ E (↑Sphi : Set (ℤ × ℤ))) (hJE : J ∈ E (↑Sphi : Set (ℤ × ℤ)))
    (hdet : 0 < det nprevJ J)
    (hempty : Arc (Sphi.finite_toSet) nprevJ J = ∅)
    {σ : ℕ → ℕ} {i₀ : ℕ}
    (hg : faceStart (Ahat (σ i₀)) nprevJ + (faceLen (Ahat (σ i₀)) nprevJ : ℤ) • dir nprevJ = g_J)
    (hvJ1 : vJ1 = dir nprevJ) :
    g_J ∈ ⋃ i, Ahat i ∧ g_J - vJ1 ∈ ⋃ i, Ahat i := by
  have hEnp : nprevJ ∈ E (Ahat (σ i₀)) := by
    rw [Nivat.AhatEnv.E_eq_of_enveloped hSfin hSarea (henv (σ i₀))]; exact hnprevE
  have hEJ : J ∈ E (Ahat (σ i₀)) := by
    rw [Nivat.AhatEnv.E_eq_of_enveloped hSfin hSarea (henv (σ i₀))]; exact hJE
  have hadj : ∀ μ ∈ E (Ahat (σ i₀)), ¬ (0 < det nprevJ μ ∧ 0 < det μ J) := by
    intro μ hμ hcon
    have hμE : μ ∈ E (↑Sphi : Set (ℤ × ℤ)) := by
      rw [← Nivat.AhatEnv.E_eq_of_enveloped hSfin hSarea (henv (σ i₀))]; exact hμ
    have hμmem : μ ∈ Arc (Sphi.finite_toSet) nprevJ J :=
      mem_Arc.mpr ⟨hμE, hcon.1, hcon.2⟩
    rw [hempty] at hμmem
    exact absurd hμmem (by simp)
  have hshared := adjacent_shared_vertex (hfin (σ i₀)) (hlc (σ i₀)) hEnp hEJ hdet hadj
  rw [hg] at hshared
  have hlen1 : 1 ≤ faceLen (Ahat (σ i₀)) nprevJ := one_le_faceLen (hfin (σ i₀)) hEnp
  refine ⟨?_, ?_⟩
  · have hmem : g_J ∈ face (Ahat (σ i₀)) J :=
      hshared.symm ▸ faceStart_mem (hfin (σ i₀)) hEJ
    exact Set.mem_iUnion.mpr ⟨σ i₀, face_subset _ _ hmem⟩
  · have hstep : faceStart (Ahat (σ i₀)) nprevJ
        + ((faceLen (Ahat (σ i₀)) nprevJ - 1 : ℕ) : ℤ) • dir nprevJ
        ∈ face (Ahat (σ i₀)) nprevJ := by
      apply mem_face_of_between (hlc (σ i₀)) (s := 0)
        (t := faceLen (Ahat (σ i₀)) nprevJ - 1) (u := faceLen (Ahat (σ i₀)) nprevJ)
      · exact Nat.zero_le _
      · exact Nat.sub_le _ _
      · simpa using faceStart_mem (hfin (σ i₀)) hEnp
      · exact faceEnd_mem (hlc (σ i₀)) (hfin (σ i₀)) hEnp
    have hcast : ((faceLen (Ahat (σ i₀)) nprevJ - 1 : ℕ) : ℤ)
        = (faceLen (Ahat (σ i₀)) nprevJ : ℤ) - 1 := by
      have h := Nat.cast_sub (R := ℤ) hlen1
      simpa using h
    have heq : faceStart (Ahat (σ i₀)) nprevJ
        + ((faceLen (Ahat (σ i₀)) nprevJ - 1 : ℕ) : ℤ) • dir nprevJ = g_J - vJ1 := by
      rw [hcast, sub_smul, one_smul, hvJ1, ← hg]
      abel
    rw [heq] at hstep
    exact Set.mem_iUnion.mpr ⟨σ i₀, face_subset _ _ hstep⟩

/-- **`hreachInf`, `ccw` case.** Body is identical to `hreachInf_of_pinned_cw` downstream of the
`a0_prev_mem` call — the `EdgeJ1Data` construction only ever uses `nJ1 := -nprevJ` and
`hnpvJ1 : dot nprevJ vJ1 = 0`, neither of which mentions `vJ1`'s sign convention, so nothing
past that call changes. -/
theorem hreachInf_of_pinned_ccw
    {Sphi : Finset (ℤ × ℤ)} {T : ℕ → Set (ℤ × ℤ)} {J nprevJ g_J vJ1 eJ nJ : ℤ × ℤ} {cJ : ℤ}
    (hfin : ∀ i, (T i).Finite)
    (hlc : ∀ i, IsLatticeConvexRegion (T i))
    (henv : ∀ i, Enveloped (↑Sphi : Set (ℤ × ℤ)) (T i))
    (hSfin : (E (↑Sphi : Set (ℤ × ℤ))).Finite) (hSarea : PosArea (↑Sphi : Set (ℤ × ℤ)))
    (hnprevE : nprevJ ∈ E (↑Sphi : Set (ℤ × ℤ))) (hJE : J ∈ E (↑Sphi : Set (ℤ × ℤ)))
    (hdet : 0 < det nprevJ J)
    (hempty : Arc (Sphi.finite_toSet) nprevJ J = ∅)
    {σ : ℕ → ℕ} {i₀ : ℕ}
    (hg : faceStart (T (σ i₀)) nprevJ + (faceLen (T (σ i₀)) nprevJ : ℤ) • dir nprevJ = g_J)
    (hvJ1 : vJ1 = dir nprevJ)
    (hAhatConvU : IsLatticeConvexRegion (⋃ i, T i))
    (hhp_all : ∀ i, T i ⊆ Nivat.CK224.halfPlaneGE nJ cJ)
    (hswept_all : Nivat.MaxEnv.SweptClosed (⋃ i, T i) vJ1 nJ cJ)
    (hcJ_def : cJ = dot nJ g_J)
    (heJ_prim : Primitive eJ)
    (hray : ∀ k : ℕ, g_J + (k : ℤ) • eJ ∈ ⋃ i, T i)
    (hdoteJ : dot nJ eJ = 0)
    (hsweep : dot nJ vJ1 < 0)
    (hsupp_prev_U : ∀ z ∈ ⋃ i, T i, dot nprevJ z ≤ dot nprevJ g_J)
    (hnpvJ1 : dot nprevJ vJ1 = 0)
    (hnpeJ : dot nprevJ eJ < 0) :
    IsLatticeConvexRegion (Nivat.MaxEnv.reachSet (⋃ i, T i) vJ1) := by
  obtain ⟨ha₀mem, hprevmem⟩ :=
    a0_prev_mem_of_pinned_ccw (Ahat := T) (Sphi := Sphi) hfin hlc henv hSfin hSarea
      hnprevE hJE hdet hempty (σ := σ) (i₀ := i₀) hg hvJ1
  have hnJ1ne : (-nprevJ : ℤ × ℤ) ≠ 0 := by
    intro h0
    have h0' : nprevJ = 0 := by
      have := congrArg (fun z : ℤ × ℤ => -z) h0
      simpa using this
    rw [h0', Nivat.LE2.dot_zero_left] at hnpeJ
    exact absurd hnpeJ (by norm_num)
  have hdotnJ1v : dot (-nprevJ) vJ1 = 0 := by
    rw [Nivat.LE2.dot_neg_left, hnpvJ1]; ring
  have hsupport : ∀ g ∈ ⋃ i, T i, dot (-nprevJ) g_J ≤ dot (-nprevJ) g := by
    intro g hg'
    rw [Nivat.LE2.dot_neg_left, Nivat.LE2.dot_neg_left]
    exact neg_le_neg (hsupp_prev_U g hg')
  have e : Nivat.Colle35.EdgeJ1Data (⋃ i, T i) vJ1 nJ cJ :=
    { a₀ := g_J
      a₀_mem := ha₀mem
      a₀_on := hcJ_def.symm
      prev_mem := hprevmem
      nJ1 := -nprevJ
      dot_nJ1_v := hdotnJ1v
      nJ1_ne := hnJ1ne
      support := hsupport }
  have hAhalf : ∀ g ∈ ⋃ i, T i, cJ ≤ dot nJ g := by
    intro g hg'
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hg'
    exact hhp_all i hi
  have hzero : Nivat.MaxEnv.reachSet (⋃ i, T i) vJ1 ∩ Nivat.CK224.halfPlaneGE nJ cJ
      ⊆ ⋃ i, T i := by
    rintro z ⟨⟨g, hg', t, rfl⟩, hlev⟩
    exact hswept_all g hg' t hlev
  have hrec : ∀ g ∈ (⋃ i, T i), g + eJ ∈ ⋃ i, T i :=
    Nivat.Colle35.rec_of_ray hAhatConvU hray
  exact Nivat.Colle35.EdgeJ1Data.isLatticeConvexRegion_reachSet e hAhatConvU hAhalf hzero
    hrec hdoteJ hsweep heJ_prim.ne_zero

/-- **`hlcT`, fully assembled, `ccw` case.** Mirror of `hlcT_of_pinned_cw`: plug `hreachA_of_wJ`
(§2, orientation-blind, unchanged) and `hreachInf_of_pinned_ccw` (above) into the `§1` bridge. -/
theorem hlcT_of_pinned_ccw
    {Sphi : Finset (ℤ × ℤ)} {A : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ} {vl : ℤ × ℤ}
    {J nprevJ g_J vJ1 eJ nJ w : ℤ × ℤ} {cJ : ℤ} {ε i₀ : ℕ}
    (hSfin : (E (↑Sphi : Set (ℤ × ℤ))).Finite)
    (hAfin : ∀ i, (hatOf A kk vl i).Finite) (hAne : ∀ i, (hatOf A kk vl i).Nonempty)
    (hAarea : ∀ i, PosArea (hatOf A kk vl i))
    (hAlc : ∀ i, IsLatticeConvexRegion (hatOf A kk vl i))
    (hAenv : ∀ i, Enveloped (↑Sphi : Set (ℤ × ℤ)) (hatOf A kk vl i))
    (hνJ1E : nprevJ ∈ E (↑Sphi : Set (ℤ × ℤ)))
    (hnegSymm : ∀ n ∈ E (↑Sphi : Set (ℤ × ℤ)), -n ∈ E (↑Sphi : Set (ℤ × ℤ)))
    (hwJ_eq : w = -dir nprevJ)
    (hJE : J ∈ E (↑Sphi : Set (ℤ × ℤ)))
    (hSarea : PosArea (↑Sphi : Set (ℤ × ℤ)))
    (hdet : 0 < det nprevJ J)
    (hempty : Arc (Sphi.finite_toSet) nprevJ J = ∅)
    {σ : ℕ → ℕ} {i₀' : ℕ}
    (hg : faceStart (hatOf A kk vl (σ i₀')) nprevJ
      + (faceLen (hatOf A kk vl (σ i₀')) nprevJ : ℤ) • dir nprevJ = g_J)
    (hvJ1 : vJ1 = dir nprevJ)
    (hAhatConvU : IsLatticeConvexRegion (⋃ i, hatOf A kk vl i))
    (hhp_all : ∀ i, hatOf A kk vl i ⊆ Nivat.CK224.halfPlaneGE nJ cJ)
    (hswept_all : Nivat.MaxEnv.SweptClosed (⋃ i, hatOf A kk vl i) vJ1 nJ cJ)
    (hcJ_def : cJ = dot nJ g_J)
    (heJ_prim : Primitive eJ)
    (hray : ∀ k : ℕ, g_J + (k : ℤ) • eJ ∈ ⋃ i, hatOf A kk vl i)
    (hdoteJ : dot nJ eJ = 0)
    (hsweep : dot nJ vJ1 < 0)
    (hsupp_prev_U : ∀ z ∈ ⋃ i, hatOf A kk vl i, dot nprevJ z ≤ dot nprevJ g_J)
    (hnpvJ1 : dot nprevJ vJ1 = 0)
    (hnpeJ : dot nprevJ eJ < 0) :
    ∀ i, i₀ ≤ i →
      IsLatticeConvexRegion (Nivat.LaneCdSite.shellT A kk vl vJ1 nJ w cJ ε i) :=
  hlcT_of_reach
    (hreachA_of_wJ (Sphi := Sphi) (A := fun i => hatOf A kk vl i) hSfin hAfin hAne hAarea
      hAlc hAenv hνJ1E hnegSymm hwJ_eq)
    (hreachInf_of_pinned_ccw (T := fun i => hatOf A kk vl i) (Sphi := Sphi) hAfin hAlc hAenv
      hSfin hSarea hνJ1E hJE hdet hempty (σ := σ) (i₀ := i₀') hg hvJ1 hAhatConvU hhp_all
      hswept_all hcJ_def heJ_prim hray hdoteJ hsweep hsupp_prev_U hnpvJ1 hnpeJ)

end Nivat.LaneHole3ConeHlcTWire

#print axioms Nivat.LaneHole3ConeHlcTWire.hreachA_of_wJ
#print axioms Nivat.LaneHole3ConeHlcTWire.hreachInf_of_pinned_cw
#print axioms Nivat.LaneHole3ConeHlcTWire.hlcT_of_pinned_cw
#print axioms Nivat.LaneHole3ConeHlcTWire.a0_prev_mem_of_pinned_ccw
#print axioms Nivat.LaneHole3ConeHlcTWire.hreachInf_of_pinned_ccw
#print axioms Nivat.LaneHole3ConeHlcTWire.hlcT_of_pinned_ccw
