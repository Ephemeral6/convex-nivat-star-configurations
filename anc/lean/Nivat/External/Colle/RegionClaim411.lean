/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.ChainGeom
import Nivat.External.Colle.Lemma41
import Nivat.External.Colle.Claim47Core
import Nivat.External.Colle.NotPeriodicShell
import Nivat.External.Colle.L1Complexity
import Nivat.Lattice.Primitive
import Nivat.External.Colle.RegionCutGE
import Nivat.External.Colle.L1Cut

/-!
# Collé's Claim 4.11 over a `ChainDataGeom`

`scratch/b3_colle2.txt:900-902`, verbatim:

> **Claim 4.11.** `ϑ` is an `(ℓ', 𝒯, +)`-semi-ambiguous configuration for any translation `𝒯`
> of `𝒮` where `𝒯 \ ℓ'_𝒯 ⊂ Â_∞^(ε)`, but `𝒯 ⊄ Â_∞^(ε)`.
>
> Indeed, let `h ∈ ℤ²` denote a period for `ϑ|Â_∞^(ε)` parallel to `−ℓ`.  Since, due to (4.6),
> `ϑ|Â_∞^(ε+1)` is not periodic of period `h`, the proof is identical to that one of Claim 4.7.

⚠ This is **not** the Claim 4.11 of `Lemma45.lean` (`claim411`, refuted at `claim411_false`);
that one is the Szabados-direction claim.  Nothing here is imported from `Lemma45.lean`.

## What is proved here

The Lean Claim 4.7, `ColleReg.case1_claim47_semiAmbiguous` (`RegionSteps.lean:1021`), runs on
three inputs that are *external* to the window bookkeeping: the period on the small region
(`hRper`), its failure on the one-step enlargement (`hnonper_R'`), and the Figure 11(B) upgrade
(`hR'_step`).  Collé's sentence above says that for Claim 4.11 all three come from (4.6) and
the chain.  This file discharges each from `ChainDataGeom` fields:

* `periodOn_shellInf_p` — `hRper` for `R := Â_∞^(ε)`, `h := p`, from `hshell_ε` and `hp_per`.
* `not_periodOn_shellInf_succ_p` — `hnonper_R'` for `R' := Â_∞^(ε+1)`, from (4.6).  The step
  that makes (4.6) bite is `add_p_mem_shellInf`: `+p` carries layer `ε+1` into layer `ε`
  (`rec_p`, `dot_nJ_p`, `ahat_halfPlane`, `shellInf_eq`).
* `shellInf_succ_step` — `hR'_step`: agreement of `ϑ` with `T h ϑ` on `Â_∞^(ε)` plus on one
  forward `v_J`-ray of the new line propagates to all of `Â_∞^(ε+1)`.  This is
  `cg.genLayers` (the `S_φ`-generation of the new line from a sliding window) together with
  `cg.bottom` (the new line is `{z₀ + k•v_J : k ≥ L}`), and needs `IsGeneratingSet ξ S_φ`.
* `claim411_semiAmbiguous` — Claim 4.11 itself, by the proof of Claim 4.7 with the three slots
  filled as above.  The window placement — Collé's *"`𝒯 \ ℓ'_𝒯 ⊂ Â_∞^(ε)` but `𝒯 ⊄ Â_∞^(ε)`"* —
  is taken as the two hypotheses `hQR` and `hface`, sharpened to *"the `ℓ'`-edge of `𝒯` sits
  on the new line"*, which is what the ray upgrade needs.

## What is not proved here

* ~~The *production* of the straddling translate `𝒯`~~ — **done in §8** (`exists_straddle`):
  from `cg.bottom`, `rec_p`, `rec_vJ`, `hRconv` and the primitivity fields, for every window
  `W` with the Lemma 2.4 deficit.  What §8 does *not* produce is `hline` — Collé's (4.1), a
  run of `|face| - 1` consecutive `v_J`-points inside `Q` — see §9.
* The sweep (Collé's Claim 4.3) that Lemma 4.1 consumes as `hsweep`.  Claim 4.11 is the
  `hamb` input of `Colle41.lemma41_of_sweep`, not its `hsweep` input.  What *is* proved
  (`window_add_p_subset_shellInf`, §5) is the Case 2 form of the sweep's seed — Case 1's
  conjunct 16, `∃ b, ∀ z ∈ S₁, b + z ∈ R` (`RegionSteps.lean:1012`): one `p`-step behind
  any straddling position, the whole window is inside `Â_∞^(ε)`.  No chain field beyond
  `rec_p` / `dot_nJ_p` / `ahat_halfPlane` / `shellInf_eq` is used for it.
* ~~`IsLatticeConvexRegion (Â_∞^(ε))`~~ — refuted in §10 here and, at every `ε` and under
  `hRconv`, by `ShellConvex.not_forall_isLatticeConvexRegion_shellInf_of_hRconv`.  §11 sidesteps
  it: the region `case1_sweep` sweeps is `shiftRegion cg s ε`, a *sub*region of the shell that
  is a `(p, v_J)`-region from `hRconv` alone (`isRegion_shiftRegion`).
* Collé's (4.1) run, `hrun` of `exists_case2_window_core` (§11) — the `B`-width question that
  L1/L3 own.  With it, `exists_case2_window`'s nine conjuncts are produced
  (`exists_case2_window_of_run_of_height`, needing the window height `≥ ε + 2 - c_J` for the
  literal `b ∈ B` in `hbase`; `exists_case2_window_weak_of_run`, needing nothing more if
  `hbase` is read as `B.Nonempty ∧ ∃ b, b + S₁ ⊆ R`).
-/

namespace Nivat.ColleReg.Claim411

open Nivat Nivat.LE2 Nivat.MaxEnv Nivat.Colle Nivat.Colle35 Nivat.Colle37 Nivat.Colle41

variable {ξ xper ϑ : Config ℤ} {vl p : ℤ × ℤ} {S : Finset (ℤ × ℤ)} {gen : ℤ × ℤ}

/-! ## §1 The shells and the recession direction `p` -/

/-- `⟪n_J, p⟫ > 0`: the recession direction points into the half-plane `ℓ_J` supports. -/
theorem dot_nJ_p_pos (cg : ChainDataGeom ξ xper vl p S gen) : 0 < dot cg.nJ p :=
  pos_dot_of_rec cg.ahat_nonempty cg.rec_p cg.ahat_halfPlane cg.dot_nJ_p

/-- `Â_∞^(ε) ⊆ Â_∞^(ε+1)`. -/
theorem shellInf_mono_succ (cg : ChainDataGeom ξ xper vl p S gen) (ε : ℕ) :
    cg.toChainData.shellInf ε ⊆ cg.toChainData.shellInf (ε + 1) := by
  rw [cg.shellInf_eq, cg.shellInf_eq]
  exact shell_mono_eps (Nat.le_succ ε)

/-- **`+p` carries layer `ε+1` into layer `ε`.**  This is the geometric fact behind Collé's
*"due to (4.6), `ϑ|Â_∞^(ε+1)` is not periodic of period `h`"*. -/
theorem add_p_mem_shellInf (cg : ChainDataGeom ξ xper vl p S gen) (ε : ℕ)
    {z : ℤ × ℤ} (hz : z ∈ cg.toChainData.shellInf (ε + 1)) :
    z + p ∈ cg.toChainData.shellInf ε := by
  rw [cg.shellInf_eq] at hz ⊢
  obtain ⟨g, hg, t, rfl, hd⟩ := hz
  refine ⟨g + p, cg.rec_p g hg, t, by abel, ?_⟩
  have hpos := dot_nJ_p_pos cg
  rw [dot_add]
  push_cast at hd
  omega

/-- Each layer is closed under `+p`. -/
theorem add_p_mem_shellInf_self (cg : ChainDataGeom ξ xper vl p S gen) (ε : ℕ)
    {z : ℤ × ℤ} (hz : z ∈ cg.toChainData.shellInf ε) :
    z + p ∈ cg.toChainData.shellInf ε := by
  rw [cg.shellInf_eq] at hz ⊢
  obtain ⟨g, hg, t, rfl, hd⟩ := hz
  refine ⟨g + p, cg.rec_p g hg, t, by abel, ?_⟩
  have hpos := dot_nJ_p_pos cg
  rw [dot_add]
  omega

/-! ## §2 The period pair of Claim 4.11 -/

/-- **`hRper` slot.**  On `Â_∞^(ε)`, `ϑ = x̂_per` and `p ∈ Per x_per`, so `p` is a period of
`ϑ|Â_∞^(ε)` (Definition 2.11). -/
theorem periodOn_shellInf_p (cg : ChainDataGeom ξ xper vl p S gen) (hp_per : p ∈ Per xper)
    {K ε : ℕ}
    (hshell : ∀ z ∈ cg.toChainData.shellInf ε, ϑ z = T ((K : ℤ) • vl) xper z) :
    PeriodOn ϑ (cg.toChainData.shellInf ε) p := by
  intro z hz hz'
  rw [hshell z hz, hshell _ hz']
  exact Per.apply (per_translate hp_per) z

/-- **`hnonper_R'` slot — (4.6) makes `ϑ|Â_∞^(ε+1)` non-periodic of period `p`.**

If it were, every `z` of layer `ε+1` would satisfy `ϑ z = ϑ (z + p)` with `z + p` in layer `ε`
(`add_p_mem_shellInf`), where `ϑ = x̂_per`; and `x̂_per` has period `p`; so `ϑ = x̂_per` on all
of layer `ε+1`, against the second half of (4.6). -/
theorem not_periodOn_shellInf_succ_p (cg : ChainDataGeom ξ xper vl p S gen)
    (hp_per : p ∈ Per xper) {K ε : ℕ}
    (hshell : ∀ z ∈ cg.toChainData.shellInf ε, ϑ z = T ((K : ℤ) • vl) xper z)
    (hshell_not :
      ¬ (∀ z ∈ cg.toChainData.shellInf (ε + 1), ϑ z = T ((K : ℤ) • vl) xper z)) :
    ¬ PeriodOn ϑ (cg.toChainData.shellInf (ε + 1)) p := by
  intro hper
  apply hshell_not
  intro z hz
  have hzp : z + p ∈ cg.toChainData.shellInf ε := add_p_mem_shellInf cg ε hz
  have hzp' : z + p ∈ cg.toChainData.shellInf (ε + 1) := shellInf_mono_succ cg ε hzp
  rw [← hper z hz hzp', hshell _ hzp, Per.apply (per_translate hp_per) z]

/-! ## §3 The Figure 11(B) upgrade: from `Â_∞^(ε)` plus one ray to `Â_∞^(ε+1)` -/

/-- The new line of `cg.bottom ε` lies in layer `ε+1`. -/
theorem bottom_mem_shellInf_succ (cg : ChainDataGeom ξ xper vl p S gen) (ε : ℕ)
    {z₀ : ℤ × ℤ} {L : ℤ} (hdz : dot cg.nJ z₀ = cg.cJ - (ε : ℤ) - 1)
    (hline : ∀ k : ℤ, L ≤ k → z₀ + k • cg.vJ ∈ reachSet (⋃ i, cg.toChainData.Ahat i) cg.vJ1)
    {k : ℤ} (hk : L ≤ k) :
    z₀ + k • cg.vJ ∈ cg.toChainData.shellInf (ε + 1) := by
  rw [cg.shellInf_eq]
  obtain ⟨g, hg, t, ht⟩ := hline k hk
  refine ⟨g, hg, t, ht, ?_⟩
  rw [dot_add, dot_zsmul_right, cg.dot_nJ_vJ, hdz]
  push_cast
  omega

/-- A point of the sliding window `winS i (t • v_J)` on the line `z₀ + ℤ • v_J` has parameter
`k ≥ t - (i + |z₀.1| + |z₀.2|)`. -/
theorem param_lower_bound_of_mem_winS {vJ z₀ : ℤ × ℤ} (hvJ : vJ ≠ 0) {i : ℕ} {t k : ℤ}
    (hw : z₀ + k • vJ ∈ winS i (t • vJ)) :
    t - ((i : ℤ) + |z₀.1| + |z₀.2|) ≤ k := by
  rw [mem_winS] at hw
  obtain ⟨⟨h1l, h1u⟩, ⟨h2l, h2u⟩⟩ := hw
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h1l h1u h2l h2u
  have hb1 : |(k - t) * vJ.1| ≤ (i : ℤ) + |z₀.1| := by
    rw [abs_le]
    constructor <;> nlinarith [neg_abs_le z₀.1, le_abs_self z₀.1]
  have hb2 : |(k - t) * vJ.2| ≤ (i : ℤ) + |z₀.2| := by
    rw [abs_le]
    constructor <;> nlinarith [neg_abs_le z₀.2, le_abs_self z₀.2]
  have hkt : |k - t| ≤ (i : ℤ) + |z₀.1| + |z₀.2| := by
    rcases eq_or_ne vJ.1 0 with h1 | h1
    · have h2 : vJ.2 ≠ 0 := fun h2 => hvJ (Prod.ext h1 h2)
      have : |k - t| ≤ |(k - t) * vJ.2| := by
        rw [abs_mul]
        exact le_mul_of_one_le_right (abs_nonneg _) (Int.one_le_abs h2)
      linarith [abs_nonneg z₀.1]
    · have : |k - t| ≤ |(k - t) * vJ.1| := by
        rw [abs_mul]
        exact le_mul_of_one_le_right (abs_nonneg _) (Int.one_le_abs h1)
      linarith [abs_nonneg z₀.2]
  have := (abs_le.mp hkt).1
  linarith

/-- **`hR'_step` slot — Figure 11(B) for the chain.**

If `ϑ` and `T h ϑ` agree on `Â_∞^(ε)` and on the forward `v_J`-ray from a point `g₁` of the
new line `Â_∞^(ε+1) \ Â_∞^(ε)`, they agree on all of `Â_∞^(ε+1)`.

`cg.genLayers ε` says that, for the window `winS i (t • v_J)` slid far enough, every point of
layer `ε+1` is `S_φ`-generated from layer `ε` together with the window's part of layer `ε+1`;
`cg.bottom ε` says that part is a block of the line `{z₀ + k • v_J : k ≥ L}`, which the ray
covers once `t` is large.  `agree_on_genClosure` (Collé's *"since `S_φ` is `η`-generating"*)
then transports the agreement. -/
theorem shellInf_succ_step (cg : ChainDataGeom ξ xper vl p S gen)
    (hS : IsGeneratingSet ξ S) (hϑ_mem : ϑ ∈ orbitClosure ξ) {ε : ℕ} {h g₁ : ℤ × ℤ}
    (hg₁ : g₁ ∈ cg.toChainData.shellInf (ε + 1)) (hg₁' : g₁ ∉ cg.toChainData.shellInf ε)
    (hagree : ∀ z ∈ cg.toChainData.shellInf ε, ϑ (z + h) = ϑ z)
    (hray : ∀ s : ℕ, ϑ ((s : ℤ) • cg.vJ + g₁ + h) = ϑ ((s : ℤ) • cg.vJ + g₁)) :
    ∀ z ∈ cg.toChainData.shellInf (ε + 1), ϑ (z + h) = ϑ z := by
  classical
  obtain ⟨i, M, hgen⟩ := cg.genLayers ε
  obtain ⟨z₀, L, hdz, hline, -, hsplit⟩ := cg.bottom ε
  -- `g₁` is on the new line: `g₁ = z₀ + kg • v_J`.
  obtain ⟨kg, -, hkg⟩ : ∃ k : ℤ, L ≤ k ∧ g₁ = z₀ + k • cg.vJ :=
    (hsplit g₁ hg₁).resolve_left hg₁'
  -- Slide the window far enough that its part of the new line is behind the ray's start.
  set C : ℤ := (i : ℤ) + |z₀.1| + |z₀.2| with hC
  set t : ℕ := M + (C + kg).toNat with ht
  have htM : M ≤ t := by omega
  have htC : C + kg ≤ (t : ℤ) := by
    have : C + kg ≤ ((C + kg).toNat : ℤ) := Int.self_le_toNat _
    omega
  -- The agreement set.
  set D : Set (ℤ × ℤ) := cg.toChainData.shellInf ε ∪
    (cg.toChainData.shellInf (ε + 1) ∩ winS i ((t : ℤ) • cg.vJ)) with hD
  have hDagree : ∀ w ∈ D, ϑ w = T h ϑ w := by
    intro w hw
    show ϑ w = ϑ (w + h)
    rcases hw with hw | ⟨hw1, hw2⟩
    · exact (hagree w hw).symm
    · rcases hsplit w hw1 with hw | ⟨k, -, rfl⟩
      · exact (hagree w hw).symm
      · -- `w = z₀ + k • v_J` with `k ≥ t - C ≥ kg`, so `w` is on the ray from `g₁`.
        have hk : t - C ≤ k := param_lower_bound_of_mem_winS cg.vJ_ne hw2
        have hkkg : kg ≤ k := by omega
        have hs : ((k - kg).toNat : ℤ) = k - kg := Int.toNat_of_nonneg (by omega)
        have hw' : z₀ + k • cg.vJ = ((k - kg).toNat : ℤ) • cg.vJ + g₁ := by
          rw [hs, hkg, sub_smul]; abel
        rw [hw']
        exact (hray _).symm
  intro z hz
  have hgc := hgen t htM z hz
  exact (agree_on_genClosure hS hϑ_mem (T_mem_of_mem_orbitClosure hϑ_mem h) hDagree z hgc).symm

/-! ## §4 Claim 4.11 -/

/-- **Collé, Claim 4.11** (`b3_colle2.txt:900-902`), by the proof of Claim 4.7.

Binders, read against Collé:

* `cg`, `hS` — the chain and *"`S_φ` is `η`-generating"* (`hS` is `d.isGeneratingSet` at the
  call site `ColleRegion.lean:408`; ⚠ **not** among `region_periods_and_rays`'s binders).
* `hp_per`, `hshell_ε`, `hshell_not_εp1` — `p ∈ Per x_per` and (4.6).
* `S₁`, `hS₁`, `Q`, `hQS`, `hQ_edge` — the translation `𝒯` of `𝒮`, its `ℓ'`-edge `S₁ \ Q`
  with `ℓ' ∥ v_J`, exactly as `case1_claim47_semiAmbiguous` takes them.
* `hQR`, `hface` — *"`𝒯 \ ℓ'_𝒯 ⊂ Â_∞^(ε)` but `𝒯 ⊄ Â_∞^(ε)`"*, for the window at every
  position `t ≥ τ`, with the edge placed on the new line `Â_∞^(ε+1) \ Â_∞^(ε)`.

The `hRper` / `hnonper_R'` / `hR'_step` inputs of Claim 4.7 are §2–§3 above; the window
bookkeeping is Claim 4.7's, line for line. -/
theorem claim411_semiAmbiguous (cg : ChainDataGeom ξ xper vl p S gen)
    (hS : IsGeneratingSet ξ S) (hϑ_mem : ϑ ∈ orbitClosure ξ) (hp_per : p ∈ Per xper)
    {K ε : ℕ}
    (hshell_ε : ∀ z ∈ cg.toChainData.shellInf ε, ϑ z = T ((K : ℤ) • vl) xper z)
    (hshell_not_εp1 :
      ¬ (∀ z ∈ cg.toChainData.shellInf (ε + 1), ϑ z = T ((K : ℤ) • vl) xper z))
    {S₁ Q : Finset (ℤ × ℤ)} {τ : ℤ} (hS₁ : IsGeneratingSet ξ S₁) (hQS : Q ⊆ S₁)
    (hQ_edge : ∃ (n : ℝ × ℝ) (cmax : ℝ),
      n ≠ 0 ∧
      inner2 n cg.vJ = 0 ∧
      (∀ z ∈ S₁, inner2 n z ≤ cmax) ∧
      (Nivat.R2.face S₁ n cmax).Nonempty ∧
      Q = S₁.filter fun z => inner2 n z < cmax)
    (hQR : ∀ t : ℤ, τ ≤ t → ∀ z ∈ Q, t • cg.vJ + z ∈ cg.toChainData.shellInf ε)
    (hface : ∀ g ∈ S₁, g ∉ Q → ∀ t : ℤ, τ ≤ t →
      t • cg.vJ + g ∈ cg.toChainData.shellInf (ε + 1) ∧
      t • cg.vJ + g ∉ cg.toChainData.shellInf ε) :
    SemiAmbiguousAlong ξ ϑ S₁ Q cg.vJ τ := by
  classical
  intro t₀ ht₀
  by_contra hcon
  push Not at hcon
  -- The period pair, with `c := 1`, `u := p`.
  have hRper : PeriodOn ϑ (cg.toChainData.shellInf ε) ((1 : ℤ) • p) := by
    rw [one_smul]; exact periodOn_shellInf_p cg hp_per hshell_ε
  have hQR' : ∀ t : ℤ, τ ≤ t → ∀ z ∈ Q,
      t • cg.vJ + z ∈ cg.toChainData.shellInf ε ∧
      t • cg.vJ + z + (1 : ℤ) • p ∈ cg.toChainData.shellInf ε := by
    intro t ht z hz
    refine ⟨hQR t ht z hz, ?_⟩
    rw [one_smul]; exact add_p_mem_shellInf_self cg ε (hQR t ht z hz)
  -- (4.5) at `t₀`: the whole `S₁`-window of `ϑ` there is `p`-periodic.
  have hbase := Nivat.Claim47.window_period_of_not_ambiguous hϑ_mem hQS hRper hQR' ht₀ hcon
  -- The edge `S₁ \ Q`, with an integral normal.
  obtain ⟨n, cmax, hn, hnu, hle, hfacene, hQdef⟩ := hQ_edge
  obtain ⟨nI, hnI0, hnIu, g₀, hg₀S, hg₀max, hQiff⟩ :=
    Nivat.Claim47.edge_integral_normal cg.vJ_prim.ne_zero hn hnu hle hfacene hQdef
  -- Its `+v_J`-end `g`.
  obtain ⟨g, hgS, hgerase, hgtop, hgedge⟩ :=
    Nivat.ColleReg.exists_face_end_data_gen hS₁.1 hS₁.2.1 cg.vJ_prim hnI0 hnIu
  have hlevel : dot nI g = dot nI g₀ := le_antisymm (hg₀max g hgS) (hgtop g₀ hg₀S)
  have hgQ : g ∉ Q := by
    intro hmem
    have h := (hQiff g hgS).mp hmem
    rw [hlevel] at h
    exact lt_irrefl _ h
  have hedge : ∀ z ∈ S₁, z ∉ Q → ∃ k : ℕ, z = g - (k : ℤ) • cg.vJ := by
    intro z hzS hzQ
    have hge : dot nI g₀ ≤ dot nI z := not_lt.mp fun h => hzQ ((hQiff z hzS).mpr h)
    rw [← hlevel] at hge
    exact hgedge z hzS (le_antisymm (hgtop z hzS) hge)
  have hgen : GeneratesAt ξ S₁ g := hS₁.2.2 g hgS hgerase
  have hSseg := Nivat.Claim47.hSseg_of_latticeConvex (u' := cg.vJ) hS₁.2.1 hgS
  -- Figure 11(A): the `p`-periodicity propagates along the forward `v_J`-ray through `g`.
  have hray :=
    Nivat.Claim47.ray_period_of_window_period hϑ_mem hgen hedge hSseg hRper hQR' ht₀ hbase
  -- Figure 11(B): that ray upgrades `Â_∞^(ε)` to `Â_∞^(ε+1)`, against (4.6).
  apply not_periodOn_shellInf_succ_p cg hp_per hshell_ε hshell_not_εp1
  intro z hz _
  obtain ⟨hg₁, hg₁'⟩ := hface g hgS hgQ t₀ ht₀
  refine shellInf_succ_step cg hS hϑ_mem (h := p) hg₁ hg₁' ?_ ?_ z hz
  · intro w hw
    have h := hRper w hw (by rw [one_smul]; exact add_p_mem_shellInf_self cg ε hw)
    rwa [one_smul] at h
  · intro s
    have h := hray (t₀ + (s : ℤ)) (by omega)
    rw [one_smul] at h
    have e : (t₀ + (s : ℤ)) • cg.vJ + g = (s : ℤ) • cg.vJ + (t₀ • cg.vJ + g) := by
      rw [add_smul]; abel
    rw [e] at h
    exact h

/-! ## §5 The sweep seed, Case 2 form

Case 1 hands its sweep the conjunct `∃ b ∈ B, ∀ z ∈ S₁, b + z ∈ R` (`RegionSteps.lean:1012`,
`case1_sweep`'s `hB_covers_window`).  In Case 2 the same fact is one `p`-step behind any
straddling position of the window: `+p` carries the edge from layer `ε+1` into layer `ε`
(`add_p_mem_shellInf`) and keeps `Q` there (`add_p_mem_shellInf_self`). -/

/-- Behind a straddling position the whole window lies in `Â_∞^(ε)`. -/
theorem window_add_p_subset_shellInf (cg : ChainDataGeom ξ xper vl p S gen) {ε : ℕ}
    {S₁ Q : Finset (ℤ × ℤ)} {τ : ℤ}
    (hQR : ∀ t : ℤ, τ ≤ t → ∀ z ∈ Q, t • cg.vJ + z ∈ cg.toChainData.shellInf ε)
    (hface : ∀ g ∈ S₁, g ∉ Q → ∀ t : ℤ, τ ≤ t →
      t • cg.vJ + g ∈ cg.toChainData.shellInf (ε + 1) ∧
      t • cg.vJ + g ∉ cg.toChainData.shellInf ε)
    {t : ℤ} (ht : τ ≤ t) :
    ∀ z ∈ S₁, t • cg.vJ + p + z ∈ cg.toChainData.shellInf ε := by
  intro z hz
  have e : t • cg.vJ + p + z = t • cg.vJ + z + p := by abel
  rw [e]
  by_cases hzQ : z ∈ Q
  · exact add_p_mem_shellInf_self cg ε (hQR t ht z hzQ)
  · exact add_p_mem_shellInf cg ε (hface z hz hzQ t ht).1

/-! ## §6 Assembly: Claim 4.11 into Lemma 4.1

`b3_colle2.txt:904`: *"Due to Claim 4.11 and Lemma 4.1, there exists an `(ℓ, ℓ')`-region
`𝒦 ⊂ Â_∞^(ε)` such that `ϑ|𝒦` is fully periodic with a period parallel to `ℓ` and another one
parallel to `ℓ'`."*

The theorem below is that sentence with Lemma 4.1 taken as `Colle41.lemma41_colle_region_shape_parallel`
and Claim 4.11 as `claim411_semiAmbiguous`.  Its conclusion is `region_periods_and_rays`'
(`RegionSteps.lean:1528-1535`) **except** that the region is inside `Â_∞^(ε)`, which is
Collé's `𝒦 ⊂ Â_∞^(ε)`, rather than inside `Â_∞ = Â_∞^(0)`.  What it still takes as
hypotheses — and therefore what leaf C owes beyond Claim 4.11 — is exactly:

* the straddling translate `𝒯` (`hS₁`, `hQS`, `hQ_edge`, `hQR`, `hface`);
* Claim 4.2's deficit `hdef` and its line seed `hline` for a finite `B`;
* the sweep `hsweep`, Collé's Claim 4.3 (`b3_colle2.txt:680-700`), the same obligation as
  Case 1's `case1_sweep`.

`h' = n • cg.vJ` with `0 < n` and `det h h' ≠ 0` come out of Lemma 4.1 for free once
`u' := cg.vJ`, `u := p`, `c := 1`: `det p v_J ≠ 0` is `det_ne_zero_of_dot` on the bundle. -/
theorem region_of_claim411_of_sweep (cg : ChainDataGeom ξ xper vl p S gen)
    (hfin : (Set.range ξ).Finite)
    (hS : IsGeneratingSet ξ S) (hϑ_mem : ϑ ∈ orbitClosure ξ) (hp_per : p ∈ Per xper)
    {K ε : ℕ}
    (hshell_ε : ∀ z ∈ cg.toChainData.shellInf ε, ϑ z = T ((K : ℤ) • vl) xper z)
    (hshell_not_εp1 :
      ¬ (∀ z ∈ cg.toChainData.shellInf (ε + 1), ϑ z = T ((K : ℤ) • vl) xper z))
    {S₁ Q : Finset (ℤ × ℤ)} {τ : ℤ} (hS₁ : IsGeneratingSet ξ S₁) (hQS : Q ⊆ S₁)
    (hQ_edge : ∃ (n : ℝ × ℝ) (cmax : ℝ),
      n ≠ 0 ∧
      inner2 n cg.vJ = 0 ∧
      (∀ z ∈ S₁, inner2 n z ≤ cmax) ∧
      (Nivat.R2.face S₁ n cmax).Nonempty ∧
      Q = S₁.filter fun z => inner2 n z < cmax)
    (hQR : ∀ t : ℤ, τ ≤ t → ∀ z ∈ Q, t • cg.vJ + z ∈ cg.toChainData.shellInf ε)
    (hface : ∀ g ∈ S₁, g ∉ Q → ∀ t : ℤ, τ ≤ t →
      t • cg.vJ + g ∈ cg.toChainData.shellInf (ε + 1) ∧
      t • cg.vJ + g ∉ cg.toChainData.shellInf ε)
    {pw : ℕ} (hdef : P ξ S₁ ≤ P ξ Q + pw)
    {B : Finset (ℤ × ℤ)} (hline : ∀ g ∈ B, ∀ i : ℕ, i < pw → g + (i : ℤ) • cg.vJ ∈ Q)
    (hsweep : ∀ q : ℕ, 0 < q →
      (∀ g ∈ B, ∀ t : ℤ, τ + (pw : ℤ) ≤ t →
        ϑ (g + (t + (q : ℤ)) • cg.vJ) = ϑ (g + t • cg.vJ)) →
      ∃ K : Set (ℤ × ℤ), K ⊆ cg.toChainData.shellInf ε ∧ Colle41.IsRegion K p cg.vJ ∧ K.Nonempty ∧
        ∃ t₀ : ℕ, 0 < t₀ ∧ PeriodOn ϑ K (((t₀ * q : ℕ) : ℤ) • cg.vJ)) :
    ∃ R : Set (ℤ × ℤ), R ⊆ cg.toChainData.shellInf ε ∧
      IsLatticeConvexRegion R ∧ R.Nonempty ∧
      ∃ h h' z₀ z₀' : ℤ × ℤ, det h h' ≠ 0 ∧
        (∀ k : ℕ, z₀ + (k : ℤ) • h ∈ R) ∧
        (∀ k : ℕ, z₀' + (k : ℤ) • h' ∈ R) ∧
        (∀ z ∈ R, z + h ∈ R → ϑ (z + h) = ϑ z) ∧
        (∀ z ∈ R, z + h' ∈ R → ϑ (z + h') = ϑ z) ∧
        ∃ n : ℕ, 0 < n ∧ h' = (n : ℤ) • cg.vJ := by
  have hdet : det p cg.vJ ≠ 0 := det_ne_zero_of_dot cg.vJ_ne cg.dot_nJ_vJ cg.dot_nJ_p
  have hamb := claim411_semiAmbiguous cg hS hϑ_mem hp_per hshell_ε hshell_not_εp1 hS₁ hQS
    hQ_edge hQR hface
  have hRper : PeriodOn ϑ (cg.toChainData.shellInf ε) ((1 : ℤ) • p) := by
    rw [one_smul]; exact periodOn_shellInf_p cg hp_per hshell_ε
  exact lemma41_colle_region_shape_parallel hfin hϑ_mem hQS hdet hdef hline hamb one_ne_zero
    hRper hsweep

/-! ## §7 Absorption into `Â_∞` along `v_J`

`Â_∞` recedes in `p` (`rec_p`) and in `v_J` (`rec_vJ`), and is lattice-convex (`hRconv`, a
binder of `region_periods_and_rays`, `RegionSteps.lean:1549`).  So its recession cone contains
the real cone spanned by `p` and `v_J`, and any lattice vector `w` with `⟪n_J, w⟫ ≥ 1` lands
in that cone after a push of `|det p w|` steps along `v_J`.  This is the geometric input to
`hQR` in §8: the `Q`-part of the window, one level *above* its edge, is inside `Â_∞` once the
window has slid far enough. -/

/-- A lattice-convex region receding in `p` and `v` absorbs every lattice vector of the real
cone they span. -/
theorem add_mem_of_nonneg_comb {R : Set (ℤ × ℤ)} (hR : IsLatticeConvexRegion R)
    {p v : ℤ × ℤ} (hp : ∀ g ∈ R, g + p ∈ R) (hv : ∀ g ∈ R, g + v ∈ R)
    {g : ℤ × ℤ} (hg : g ∈ R) {w : ℤ × ℤ} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hw : toReal w = a • toReal p + b • toReal v) : g + w ∈ R := by
  have hp' : toReal p ∈ recCone R := toReal_mem_recCone hp
  have hv' : toReal v ∈ recCone R := toReal_mem_recCone hv
  have hw' : toReal w ∈ recCone R := by
    rw [hw]
    exact add_mem_recCone (smul_mem_recCone ha hp') (smul_mem_recCone hb hv')
  exact add_mem_of_mem_recCone hR hw' hg

/-- Cramer: `det p v • w = det w v • p + det p w • v`, over `ℝ`. -/
theorem toReal_cramer (p v w : ℤ × ℤ) :
    ((det p v : ℤ) : ℝ) • toReal w
      = ((det w v : ℤ) : ℝ) • toReal p + ((det p w : ℤ) : ℝ) • toReal v := by
  ext <;> simp only [toReal, det, Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add,
    smul_eq_mul] <;> push_cast <;> ring

theorem div_nonneg_of_mul_nonneg_int {x D : ℤ} (hD : D ≠ 0) (h : 0 ≤ x * D) :
    0 ≤ (x : ℝ) / D := by
  rcases lt_or_gt_of_ne hD with hD' | hD'
  · have hx : x ≤ 0 := by nlinarith
    exact div_nonneg_of_nonpos (by exact_mod_cast hx) (by exact_mod_cast hD'.le)
  · have hx : 0 ≤ x := by nlinarith
    exact div_nonneg (by exact_mod_cast hx) (by exact_mod_cast hD'.le)

theorem shifted_coeff_nonneg {X D k : ℤ} (hD : D ≠ 0) (hk : (X.natAbs : ℤ) ≤ k) :
    0 ≤ (X + k * D) * D := by
  set M : ℤ := (X.natAbs : ℤ) with hM
  have hMabs : |X| = M := by rw [hM, Int.natCast_natAbs]
  have hM0 : 0 ≤ M := by omega
  have h1 : 1 ≤ |D| := Int.one_le_abs hD
  have h3 : -(M * |D|) ≤ X * D := by rw [← hMabs, ← abs_mul]; exact neg_abs_le _
  have h4 : D * D = |D| * |D| := (abs_mul_abs_self D).symm
  have h5 : M * |D| ≤ M * (|D| * |D|) :=
    mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (abs_nonneg _) h1) hM0
  have h6 : M * (D * D) ≤ k * (D * D) := mul_le_mul_of_nonneg_right hk (mul_self_nonneg D)
  rw [h4] at h6
  nlinarith

/-- **Pushing far enough along `v_J` brings `g + w` back into `Â_∞`** whenever `w` points into
the half-plane (`1 ≤ ⟪n_J, w⟫`); `k ≥ |det p w|` suffices. -/
theorem add_add_zsmul_vJ_mem_ahat (cg : ChainDataGeom ξ xper vl p S gen)
    (hRconv : IsLatticeConvexRegion (⋃ i, cg.toChainData.Ahat i))
    {w : ℤ × ℤ} (hw : 1 ≤ dot cg.nJ w) {g : ℤ × ℤ} (hg : g ∈ ⋃ i, cg.toChainData.Ahat i)
    {k : ℤ} (hk : ((det p w).natAbs : ℤ) ≤ k) :
    g + (w + k • cg.vJ) ∈ ⋃ i, cg.toChainData.Ahat i := by
  have hD : det p cg.vJ ≠ 0 := det_ne_zero_of_dot cg.vJ_ne cg.dot_nJ_vJ cg.dot_nJ_p
  have hDr : ((det p cg.vJ : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hD
  have hpos := dot_nJ_p_pos cg
  -- `det w v_J · det p v_J ≥ 0`, because `det w v_J · ⟪n_J, p⟫ = det p v_J · ⟪n_J, w⟫`.
  have hid : det w cg.vJ * dot cg.nJ p = det p cg.vJ * dot cg.nJ w := by
    have h := cg.dot_nJ_vJ
    simp only [det, dot] at h ⊢
    linear_combination (w.1 * p.2 - w.2 * p.1) * h
  have ha0 : 0 ≤ det w cg.vJ * det p cg.vJ := by
    have hsq : 0 ≤ det p cg.vJ * det p cg.vJ * dot cg.nJ w :=
      mul_nonneg (mul_self_nonneg _) (by omega)
    have : det w cg.vJ * det p cg.vJ * dot cg.nJ p
        = det p cg.vJ * det p cg.vJ * dot cg.nJ w := by
      linear_combination det p cg.vJ * hid
    nlinarith
  have hb0 : 0 ≤ (det p w + k * det p cg.vJ) * det p cg.vJ := shifted_coeff_nonneg hD hk
  refine add_mem_of_nonneg_comb hRconv cg.rec_p cg.rec_vJ hg
    (a := ((det w cg.vJ : ℤ) : ℝ) / (det p cg.vJ : ℤ))
    (b := (((det p w + k * det p cg.vJ : ℤ)) : ℝ) / (det p cg.vJ : ℤ))
    (div_nonneg_of_mul_nonneg_int hD ha0) (div_nonneg_of_mul_nonneg_int hD hb0) ?_
  have hcr := toReal_cramer p cg.vJ (w + k • cg.vJ)
  have e1 : det (w + k • cg.vJ) cg.vJ = det w cg.vJ := by
    simp only [det, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
  have e2 : det p (w + k • cg.vJ) = det p w + k * det p cg.vJ := by
    simp only [det, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
  rw [e1, e2] at hcr
  calc toReal (w + k • cg.vJ)
      = ((det p cg.vJ : ℤ) : ℝ)⁻¹ • (((det p cg.vJ : ℤ) : ℝ) • toReal (w + k • cg.vJ)) := by
        rw [smul_smul, inv_mul_cancel₀ hDr, one_smul]
    _ = _ := by
        rw [hcr, smul_add, smul_smul, smul_smul, div_eq_inv_mul, div_eq_inv_mul]

/-! ## §8 Producing the straddling translate `𝒯`

Collé, `b3_colle2.txt:900`: *"any translation `𝒯` of `𝒮` where `𝒯 \ ℓ'_𝒯 ⊂ Â_∞^(ε)`, but
`𝒯 ⊄ Â_∞^(ε)`"*.  The translate is built from the bottom line of `cg.bottom ε`:

* `a₀` — the `⟪n_J, ·⟫`-minimal point of the window `W`; its level set is the `ℓ'`-face of
  `W` (with `ℓ' ∥ v_J`, normal `-n_J`), and `Q := W \ face`.
* `v := z₀ + K • v_J - a₀` with `K := L + M`, `M` the diameter of `W`.  This puts `a₀` on the
  new line `{z₀ + k • v_J : k ≥ L}` far enough along that the whole face lands on it too
  (`hface`, using `vJ_prim` and `nJ_prim` to write a face point as `a₀ + c • v_J`).
* `τ := max_{w ∈ W} |det p (w - a₀)|` — after that many `v_J`-steps every `Q`-point, which sits
  at least one level above the new line, is inside `Â_∞` (§7), hence in `Â_∞^(ε)` via the
  sweep (`hQR`).
* The Lemma 2.4 deficit `hdef` transports along the translation by `P_translate` and
  `L1Complexity.face_card_image_add`, pinned at the width `|face| - 1`.

`htrans` is `L1Data.isGeneratingSet_image` (`L1Assemble.lean:500`); taken as a hypothesis here
because that module is not yet in the oleans this file is checked against. -/

/-- On the line `⟪n_J, ·⟫ = 0` every lattice vector is a multiple of the primitive `v_J`. -/
theorem eq_zsmul_vJ_of_dot_eq_zero (cg : ChainDataGeom ξ xper vl p S gen)
    {y : ℤ × ℤ} (hy : dot cg.nJ y = 0) : ∃ c : ℤ, y = c • cg.vJ := by
  apply eq_zsmul_of_det_eq_zero cg.vJ_prim
  have hn := cg.nJ_prim.ne_zero
  have h := cg.dot_nJ_vJ
  have h1 : cg.nJ.1 * det cg.vJ y = 0 := by
    simp only [det, dot] at h hy ⊢
    linear_combination y.2 * h - cg.vJ.2 * hy
  have h2 : cg.nJ.2 * det cg.vJ y = 0 := by
    simp only [det, dot] at h hy ⊢
    linear_combination -y.1 * h + cg.vJ.1 * hy
  by_contra hd
  apply hn
  exact Prod.ext ((mul_eq_zero.mp h1).resolve_right hd) ((mul_eq_zero.mp h2).resolve_right hd)

theorem abs_coeff_le {vJ : ℤ × ℤ} (hv : vJ ≠ 0) (c : ℤ) :
    |c| ≤ |(c • vJ).1| + |(c • vJ).2| := by
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, abs_mul]
  have hc := abs_nonneg c
  rcases eq_or_ne vJ.1 0 with h1 | h1
  · have h2 : vJ.2 ≠ 0 := fun h2 => hv (Prod.ext h1 h2)
    have := le_mul_of_one_le_right hc (Int.one_le_abs h2)
    have := mul_nonneg hc (abs_nonneg vJ.1)
    linarith
  · have := le_mul_of_one_le_right hc (Int.one_le_abs h1)
    have := mul_nonneg hc (abs_nonneg vJ.2)
    linarith

/-- **The straddling translate exists**, with its `ℓ'`-edge on the new line of layer `ε + 1`.
The conclusion is exactly the `S₁ / Q / hQ_edge / hQR / hface` block of `claim411_semiAmbiguous`
together with `hdef` at the pinned width `|face| - 1`. -/
theorem exists_straddle (cg : ChainDataGeom ξ xper vl p S gen)
    (hRconv : IsLatticeConvexRegion (⋃ i, cg.toChainData.Ahat i))
    {W : Finset (ℤ × ℤ)} (hW : IsGeneratingSet ξ W)
    (htrans : ∀ v : ℤ × ℤ, IsGeneratingSet ξ (W.image (· + v)))
    (hdef : ∀ (n : ℝ × ℝ) (cmax cmin : ℝ),
      (∀ z ∈ W, inner2 n z ≤ cmax) → (Nivat.R2.face W n cmax).Nonempty →
      (∀ z ∈ W, cmin ≤ inner2 n z) → (Nivat.R2.face W n cmin).Nonempty →
        P ξ W - P ξ (W.filter fun z => inner2 n z < cmax) ≤
          (Nivat.R2.face W n cmax).card - 1 ∧
        P ξ W - P ξ (W.filter fun z => cmin < inner2 n z) ≤
          (Nivat.R2.face W n cmin).card - 1)
    (ε : ℕ) :
    ∃ (v : ℤ × ℤ) (Q : Finset (ℤ × ℤ)) (τ : ℤ),
      IsGeneratingSet ξ (W.image (· + v)) ∧ Q ⊆ W.image (· + v) ∧
      (∃ (n : ℝ × ℝ) (cmax : ℝ),
        n ≠ 0 ∧
        inner2 n cg.vJ = 0 ∧
        (∀ z ∈ W.image (· + v), inner2 n z ≤ cmax) ∧
        (Nivat.R2.face (W.image (· + v)) n cmax).Nonempty ∧
        Q = (W.image (· + v)).filter (fun z => inner2 n z < cmax) ∧
        P ξ (W.image (· + v)) ≤ P ξ Q + ((Nivat.R2.face (W.image (· + v)) n cmax).card - 1)) ∧
      (∀ t : ℤ, τ ≤ t → ∀ z ∈ Q, t • cg.vJ + z ∈ cg.toChainData.shellInf ε) ∧
      (∀ g ∈ W.image (· + v), g ∉ Q → ∀ t : ℤ, τ ≤ t →
        t • cg.vJ + g ∈ cg.toChainData.shellInf (ε + 1) ∧
        t • cg.vJ + g ∉ cg.toChainData.shellInf ε) := by
  classical
  obtain ⟨z₀, L, hdz, hline, -, -⟩ := cg.bottom ε
  obtain ⟨a₀, ha₀W, hmin⟩ := W.exists_min_image (fun w => dot cg.nJ w) hW.1
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = W.sup (fun w => (w - a₀).1.natAbs + (w - a₀).2.natAbs) :=
    ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K : ℤ, K = L + (M : ℤ) := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v : ℤ × ℤ, v = z₀ + K • cg.vJ - a₀ := ⟨_, rfl⟩
  obtain ⟨τ, hτ⟩ : ∃ τ : ℤ, τ = ((W.sup (fun w => (det p (w - a₀)).natAbs) : ℕ) : ℤ) :=
    ⟨_, rfl⟩
  obtain ⟨n, hn⟩ : ∃ n : ℝ × ℝ, n = toReal (-cg.nJ) := ⟨_, rfl⟩
  obtain ⟨cmax, hcmax⟩ : ∃ cmax : ℝ, cmax = -((dot cg.nJ (a₀ + v) : ℤ) : ℝ) := ⟨_, rfl⟩
  have hinner : ∀ z, inner2 n z = -((dot cg.nJ z : ℤ) : ℝ) := by
    intro z; rw [hn, inner2_toReal, dot_neg_left, Int.cast_neg]
  obtain ⟨g₀, hg₀, s, hs⟩ := hline K (by omega)
  -- the strict-side test, as an integer inequality
  have hlt_iff : ∀ w, inner2 n (w + v) < cmax ↔ dot cg.nJ a₀ < dot cg.nJ w := by
    intro w
    rw [hinner, hcmax, dot_add, dot_add]
    push_cast
    constructor
    · intro h
      have : (dot cg.nJ a₀ : ℝ) < dot cg.nJ w := by linarith
      exact_mod_cast this
    · intro h
      have : (dot cg.nJ a₀ : ℝ) < dot cg.nJ w := by exact_mod_cast h
      linarith
  refine ⟨v, (W.image (· + v)).filter (fun z => inner2 n z < cmax), τ, htrans v,
    Finset.filter_subset _ _, ⟨n, cmax, ?_, ?_, ?_, ?_, rfl, ?_⟩, ?_, ?_⟩
  · -- `n ≠ 0`
    intro h
    rw [hn] at h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only [toReal, Prod.fst_neg, Prod.snd_neg, Int.cast_neg, Prod.fst_zero, Prod.snd_zero,
      neg_eq_zero, Int.cast_eq_zero] at h1 h2
    exact cg.nJ_prim.ne_zero (Prod.ext h1 h2)
  · rw [hinner, cg.dot_nJ_vJ]; simp
  · intro z hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
    rw [hinner, hcmax, dot_add, dot_add]
    push_cast
    have := (Int.cast_le (R := ℝ)).mpr (hmin w hw)
    linarith
  · exact ⟨a₀ + v, Nivat.R2.mem_face.mpr ⟨Finset.mem_image_of_mem _ ha₀W, by rw [hinner, hcmax]⟩⟩
  · -- `hdef`, transported along the translation
    have hle₀ : ∀ z ∈ W, inner2 n z ≤ -((dot cg.nJ a₀ : ℤ) : ℝ) := by
      intro z hz
      rw [hinner]
      have := (Int.cast_le (R := ℝ)).mpr (hmin z hz)
      linarith
    have hfne₀ : (Nivat.R2.face W n (-((dot cg.nJ a₀ : ℤ) : ℝ))).Nonempty :=
      ⟨a₀, Nivat.R2.mem_face.mpr ⟨ha₀W, by rw [hinner]⟩⟩
    obtain ⟨zmin, hzminW, hzmin⟩ := W.exists_min_image (fun z => inner2 n z) hW.1
    have hd := (hdef n _ (inner2 n zmin) hle₀ hfne₀ hzmin
      ⟨zmin, Nivat.R2.mem_face.mpr ⟨hzminW, rfl⟩⟩).1
    have hcm : cmax - inner2 n v = -((dot cg.nJ a₀ : ℤ) : ℝ) := by
      rw [hcmax, hinner, dot_add]; push_cast; ring
    have hQ : (W.image (· + v)).filter (fun z => inner2 n z < cmax)
        = (W.filter fun z => inner2 n z < -((dot cg.nJ a₀ : ℤ) : ℝ)).image (· + v) := by
      rw [Finset.filter_image]
      congr 1
      refine Finset.filter_congr fun z _ => ?_
      rw [inner2_add, ← hcm]
      constructor <;> intro h <;> linarith
    have hfc : (Nivat.R2.face (W.image (· + v)) n cmax).card
        = (Nivat.R2.face W n (-((dot cg.nJ a₀ : ℤ) : ℝ))).card := by
      rw [Nivat.L1Complexity.face_card_image_add, hcm]
    rw [hQ, hfc, P_translate, P_translate]
    omega
  · -- `hQR`
    intro t ht z hz
    obtain ⟨hzS, hzlt⟩ := Finset.mem_filter.mp hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hzS
    have hgt : dot cg.nJ a₀ < dot cg.nJ w := (hlt_iff w).mp hzlt
    have hw1 : 1 ≤ dot cg.nJ (w - a₀) := by rw [dot_sub]; omega
    have hτ' : ((det p (w - a₀)).natAbs : ℤ) ≤ t := by
      have h : (det p (w - a₀)).natAbs ≤ W.sup (fun w => (det p (w - a₀)).natAbs) :=
        Finset.le_sup (f := fun w => (det p (w - a₀)).natAbs) hw
      omega
    have hmem := add_add_zsmul_vJ_mem_ahat cg hRconv hw1 hg₀ hτ'
    rw [cg.shellInf_eq]
    refine ⟨g₀ + ((w - a₀) + t • cg.vJ), hmem, s, ?_, ?_⟩
    · calc t • cg.vJ + (w + v) = (z₀ + K • cg.vJ) + ((w - a₀) + t • cg.vJ) := by rw [hv]; abel
        _ = g₀ + ((w - a₀) + t • cg.vJ) + (s : ℤ) • cg.vJ1 := by rw [hs]; abel
    · rw [hv]
      simp only [dot_add, dot_sub, dot_zsmul_right, cg.dot_nJ_vJ, hdz, mul_zero]
      omega
  · -- `hface`
    intro g hgS hgQ t ht
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hgS
    have hnotlt : ¬ inner2 n (w + v) < cmax := fun h => hgQ (Finset.mem_filter.mpr ⟨hgS, h⟩)
    have heq : dot cg.nJ w = dot cg.nJ a₀ := by
      have h1 := hmin w hw
      have h2 : ¬ dot cg.nJ a₀ < dot cg.nJ w := fun h => hnotlt ((hlt_iff w).mpr h)
      omega
    obtain ⟨c, hc⟩ := eq_zsmul_vJ_of_dot_eq_zero cg (y := w - a₀) (by rw [dot_sub, heq, sub_self])
    have hcM : -(M : ℤ) ≤ c := by
      have h1 := abs_coeff_le cg.vJ_ne c
      rw [← hc] at h1
      simp only [Int.abs_eq_natAbs] at h1
      have h2 : (w - a₀).1.natAbs + (w - a₀).2.natAbs
          ≤ W.sup (fun w => (w - a₀).1.natAbs + (w - a₀).2.natAbs) :=
        Finset.le_sup (f := fun w => (w - a₀).1.natAbs + (w - a₀).2.natAbs) hw
      omega
    have hw' : w = a₀ + c • cg.vJ := by rw [← hc]; abel
    have hpt : t • cg.vJ + (w + v) = z₀ + (K + c + t) • cg.vJ := by
      rw [hw', hv, add_smul, add_smul]; abel
    have hk : L ≤ K + c + t := by omega
    refine ⟨?_, ?_⟩
    · rw [hpt]; exact bottom_mem_shellInf_succ cg ε hdz hline hk
    · rw [hpt, cg.shellInf_eq]
      rintro ⟨-, -, -, -, hd⟩
      rw [dot_add, dot_zsmul_right, cg.dot_nJ_vJ, hdz] at hd
      omega

/-! ## §9 Assembly with the straddle produced

`region_of_claim411_of_sweep` with §8 plugged in.  Two inputs stay open and are stated as
hypotheses, both quantified over the straddle data §8 produces so that a generic result can be
instantiated:

* `hrun` — Collé's (4.1): the produced `Q` contains a run of `|face| - 1` consecutive
  `v_J`-points.  `L1Data.exists_side_with_run_of_latticeConvex` (`L1Fields.lean:633`) gives such
  a run on *one of the two* `ℓ'`-sides of a lattice-convex window; §8 fixes the side (the
  `⟪n_J, ·⟫`-minimal face is the one that sits on the new line), so the side it returns is not
  under our control.  This is Collé's *"we will suppose initially that ... ≤ ..."* WLOG at
  `b3_colle2.txt:627`, which the Lean tree has not yet resolved for Case 2.
* `hsweep` — Claim 4.3, the same obligation as Case 1's `case1_sweep`
  (`RegionSteps.lean:1097`), in the instance `u := p`, `u' := cg.vJ`, `c := 1`,
  `R := shellInf ε`, `ξ' := ϑ`. -/
theorem region_of_claim411_of_straddle (cg : ChainDataGeom ξ xper vl p S gen)
    (hfin : (Set.range ξ).Finite)
    (hS : IsGeneratingSet ξ S) (hϑ_mem : ϑ ∈ orbitClosure ξ) (hp_per : p ∈ Per xper)
    (hRconv : IsLatticeConvexRegion (⋃ i, cg.toChainData.Ahat i))
    {K ε : ℕ}
    (hshell_ε : ∀ z ∈ cg.toChainData.shellInf ε, ϑ z = T ((K : ℤ) • vl) xper z)
    (hshell_not_εp1 :
      ¬ (∀ z ∈ cg.toChainData.shellInf (ε + 1), ϑ z = T ((K : ℤ) • vl) xper z))
    {W : Finset (ℤ × ℤ)} (hW : IsGeneratingSet ξ W)
    (htrans : ∀ v : ℤ × ℤ, IsGeneratingSet ξ (W.image (· + v)))
    (hdef : ∀ (n : ℝ × ℝ) (cmax cmin : ℝ),
      (∀ z ∈ W, inner2 n z ≤ cmax) → (Nivat.R2.face W n cmax).Nonempty →
      (∀ z ∈ W, cmin ≤ inner2 n z) → (Nivat.R2.face W n cmin).Nonempty →
        P ξ W - P ξ (W.filter fun z => inner2 n z < cmax) ≤
          (Nivat.R2.face W n cmax).card - 1 ∧
        P ξ W - P ξ (W.filter fun z => cmin < inner2 n z) ≤
          (Nivat.R2.face W n cmin).card - 1)
    (hrun : ∀ (S₁ : Finset (ℤ × ℤ)) (n : ℝ × ℝ) (cmax : ℝ),
      IsGeneratingSet ξ S₁ → n ≠ 0 → inner2 n cg.vJ = 0 →
      (∀ z ∈ S₁, inner2 n z ≤ cmax) → (Nivat.R2.face S₁ n cmax).Nonempty →
      ∃ B : Finset (ℤ × ℤ), ∀ g ∈ B, ∀ i : ℕ, i < (Nivat.R2.face S₁ n cmax).card - 1 →
        g + (i : ℤ) • cg.vJ ∈ S₁.filter (fun z => inner2 n z < cmax))
    (hsweep : ∀ (S₁ Q B : Finset (ℤ × ℤ)) (τ : ℤ) (pw : ℕ),
      IsGeneratingSet ξ S₁ → Q ⊆ S₁ →
      (∀ g ∈ B, ∀ i : ℕ, i < pw → g + (i : ℤ) • cg.vJ ∈ Q) →
      (∀ t : ℤ, τ ≤ t → ∀ z ∈ Q, t • cg.vJ + z ∈ cg.toChainData.shellInf ε) →
      SemiAmbiguousAlong ξ ϑ S₁ Q cg.vJ τ →
      ∀ q : ℕ, 0 < q →
        (∀ g ∈ B, ∀ t : ℤ, τ + (pw : ℤ) ≤ t →
          ϑ (g + (t + (q : ℤ)) • cg.vJ) = ϑ (g + t • cg.vJ)) →
        ∃ K : Set (ℤ × ℤ), K ⊆ cg.toChainData.shellInf ε ∧ Colle41.IsRegion K p cg.vJ ∧
          K.Nonempty ∧ ∃ t₀ : ℕ, 0 < t₀ ∧ PeriodOn ϑ K (((t₀ * q : ℕ) : ℤ) • cg.vJ)) :
    ∃ R : Set (ℤ × ℤ), R ⊆ cg.toChainData.shellInf ε ∧
      IsLatticeConvexRegion R ∧ R.Nonempty ∧
      ∃ h h' z₀ z₀' : ℤ × ℤ, det h h' ≠ 0 ∧
        (∀ k : ℕ, z₀ + (k : ℤ) • h ∈ R) ∧
        (∀ k : ℕ, z₀' + (k : ℤ) • h' ∈ R) ∧
        (∀ z ∈ R, z + h ∈ R → ϑ (z + h) = ϑ z) ∧
        (∀ z ∈ R, z + h' ∈ R → ϑ (z + h') = ϑ z) ∧
        ∃ n : ℕ, 0 < n ∧ h' = (n : ℤ) • cg.vJ := by
  classical
  obtain ⟨v, Q, τ, hS₁, hQS, ⟨n, cmax, hn, hnu, hle, hfne, hQdef, hPQ⟩, hQR, hface⟩ :=
    exists_straddle cg hRconv hW htrans hdef ε
  obtain ⟨B, hB⟩ := hrun _ n cmax hS₁ hn hnu hle hfne
  rw [← hQdef] at hB
  have hQ_edge : ∃ (n : ℝ × ℝ) (cmax : ℝ), n ≠ 0 ∧ inner2 n cg.vJ = 0 ∧
      (∀ z ∈ W.image (· + v), inner2 n z ≤ cmax) ∧
      (Nivat.R2.face (W.image (· + v)) n cmax).Nonempty ∧
      Q = (W.image (· + v)).filter fun z => inner2 n z < cmax :=
    ⟨n, cmax, hn, hnu, hle, hfne, hQdef⟩
  have hamb := claim411_semiAmbiguous cg hS hϑ_mem hp_per hshell_ε hshell_not_εp1 hS₁ hQS
    hQ_edge hQR hface
  exact region_of_claim411_of_sweep cg hfin hS hϑ_mem hp_per hshell_ε hshell_not_εp1 hS₁ hQS
    hQ_edge hQR hface hPQ hB (hsweep _ Q B τ _ hS₁ hQS hB hQR hamb)

/-! ## §10 `IsLatticeConvexRegion (Â_∞^(ε))` does not follow from the shell formula

Collé asserts at `b3_colle2.txt:440` that each `Â_∞^(ε)` *is* an `(ℓ_ι, ℓ_J)`-region.  The
bundle records the shell only through the formula `shellInf_eq` (`ChainShell.lean:58`), and
the sweep direction `v_{J-1}` only through `dot nJ vJ1 < 0` (forced,
`ChainDataGeom.dot_nJ_vJ1_neg`, `ANormal.lean:747`).  That is not enough: sweeping the
lattice-convex cone `{0 ≤ z.2, 3 z.2 ≤ z.1}` (receding in `p = (3,1)` and `v_J = (1,0)`) along
the primitive `v_{J-1} = (1,-2)` gives a layer `ε = 2` containing `(3,0)` and `(1,-2)` but not
their midpoint `(2,-1)`, while every layer increment is still a `v_J`-half-line as `bottom`
demands.  So convexity of the shell is a **placement** obligation on the producer of `Â_∞`
(leaf A: `exists_chainData`, `RegionSteps.lean:811`), not a consequence of the fields.

⚠ Not a refutation of `bottom` or of any `ChainDataGeom` statement; it is a refutation of the
implication *"shell formula + shell-side fields ⟹ lattice-convex shell"*.  The existing
refutations `AEnv.not_canonA_latticeConvex`, `ConeCounterexample.not_isLatticeConvexRegion_iUnion_Tset`
and `EnvelopedConvex.not_isLatticeConvexRegion_punct` concern other sets. -/

namespace ShellCx

def cone : Set (ℤ × ℤ) := {z | 0 ≤ z.2 ∧ 3 * z.2 ≤ z.1}
def pC : ℤ × ℤ := (3, 1)
def vJC : ℤ × ℤ := (1, 0)
def nJC : ℤ × ℤ := (0, 1)
def vJ1C : ℤ × ℤ := (1, -2)

theorem cone_latticeConvex : IsLatticeConvexRegion cone := by
  refine ⟨{x : ℝ × ℝ | 0 ≤ x.2 ∧ 3 * x.2 ≤ x.1}, ?_, ?_, ?_⟩
  · intro u hu v hv a b ha hb _
    refine ⟨?_, ?_⟩
    · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      exact add_nonneg (mul_nonneg ha hu.1) (mul_nonneg hb hv.1)
    · simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      nlinarith [hu.2, hv.2]
  · have he : {x : ℝ × ℝ | 0 ≤ x.2 ∧ 3 * x.2 ≤ x.1}
        = {x : ℝ × ℝ | 0 ≤ x.2} ∩ {x : ℝ × ℝ | 3 * x.2 ≤ x.1} := rfl
    rw [he]
    exact (isClosed_le continuous_const continuous_snd).inter
      (isClosed_le (continuous_const.mul continuous_snd) continuous_fst)
  · ext z
    simp only [cone, Set.mem_preimage, Set.mem_ofPred_eq, toReal]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩

theorem mem_shell2_30 : ((3 : ℤ), (0 : ℤ)) ∈ shell cone vJ1C nJC 0 2 :=
  ⟨(3, 0), ⟨le_refl _, by norm_num⟩, 0, by simp, by simp [dot, nJC]⟩

theorem mem_shell2_1m2 : ((1 : ℤ), (-2 : ℤ)) ∈ shell cone vJ1C nJC 0 2 :=
  ⟨(0, 0), ⟨le_refl _, le_refl _⟩, 1, by simp [vJ1C], by simp [dot, nJC]⟩

theorem not_mem_shell2_2m1 : ((2 : ℤ), (-1 : ℤ)) ∉ shell cone vJ1C nJC 0 2 := by
  rintro ⟨g, ⟨hg1, hg2⟩, t, ht, -⟩
  have h1 := congrArg Prod.fst ht
  have h2 := congrArg Prod.snd ht
  simp only [vJ1C, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h1 h2
  omega

theorem not_isLatticeConvexRegion_shell2 :
    ¬ IsLatticeConvexRegion (shell cone vJ1C nJC 0 2) := by
  rintro ⟨C, hconv, -, heq⟩
  have h0 := mem_shell2_30
  have h2 := mem_shell2_1m2
  rw [heq] at h0 h2
  have hmid := hconv (Set.mem_preimage.mp h0) (Set.mem_preimage.mp h2)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  have hcalc : (1 / 2 : ℝ) • toReal ((3 : ℤ), (0 : ℤ)) +
      (1 / 2 : ℝ) • toReal ((1 : ℤ), (-2 : ℤ)) = toReal ((2 : ℤ), (-1 : ℤ)) := by
    simp only [toReal, Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk]
    norm_num
  rw [hcalc] at hmid
  have hmem : ((2 : ℤ), (-1 : ℤ)) ∈ shell cone vJ1C nJC 0 2 := by
    rw [heq]
    exact Set.mem_preimage.mpr hmid
  exact not_mem_shell2_2m1 hmem

/-- The layer increment `2 \ 1` is still a `v_J`-half-line, as `bottom`'s last conjunct asks. -/
theorem shell2_split : ∀ z ∈ shell cone vJ1C nJC 0 2,
    z ∈ shell cone vJ1C nJC 0 1 ∨ ∃ k : ℤ, 0 ≤ k ∧ z = ((1 : ℤ), (-2 : ℤ)) + k • vJC := by
  rintro z ⟨g, ⟨hg1, hg2⟩, t, rfl, hd⟩
  simp only [dot, nJC, vJ1C, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul] at hd ⊢
  by_cases h : (0 : ℤ) - 1 ≤ 0 * (g.1 + t * 1) + 1 * (g.2 + t * -2)
  · left
    exact ⟨g, ⟨hg1, hg2⟩, t, rfl, by simpa [dot, nJC, vJ1C] using h⟩
  · right
    refine ⟨g.1 + t - 1, by omega, ?_⟩
    simp only [vJC, Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk, mul_one, mul_zero, add_zero]
    refine Prod.ext ?_ ?_ <;> simp; omega

end ShellCx

/-- **Lattice-convexity of a shell is not a consequence of the shell-side data.**  Every
hypothesis a `ChainDataGeom` puts on `(Â_∞, v_{J-1}, n_J, v_J, p, c_J)` that the shell formula
can see is listed; the conclusion fails at `ε = 2`. -/
theorem not_isLatticeConvexRegion_shell_of_formula :
    ∃ (A : Set (ℤ × ℤ)) (vJ1 nJ vJ p : ℤ × ℤ) (cJ : ℤ),
      IsLatticeConvexRegion A ∧ A.Nonempty ∧
      (∀ g ∈ A, cJ ≤ dot nJ g) ∧ (∀ g ∈ A, g + p ∈ A) ∧ (∀ g ∈ A, g + vJ ∈ A) ∧
      dot nJ vJ = 0 ∧ dot nJ p ≠ 0 ∧ dot nJ vJ1 < 0 ∧
      Primitive vJ ∧ Primitive nJ ∧ Primitive vJ1 ∧
      (∀ z ∈ shell A vJ1 nJ cJ 2,
        z ∈ shell A vJ1 nJ cJ 1 ∨ ∃ k : ℤ, 0 ≤ k ∧ z = ((1 : ℤ), (-2 : ℤ)) + k • vJ) ∧
      ¬ IsLatticeConvexRegion (shell A vJ1 nJ cJ 2) := by
  refine ⟨ShellCx.cone, ShellCx.vJ1C, ShellCx.nJC, ShellCx.vJC, ShellCx.pC, 0,
    ShellCx.cone_latticeConvex, ⟨(0, 0), le_refl _, le_refl _⟩, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ShellCx.shell2_split, ShellCx.not_isLatticeConvexRegion_shell2⟩
  · rintro g ⟨h1, -⟩; simp only [dot, ShellCx.nJC]; omega
  · rintro g ⟨h1, h2⟩
    simp only [ShellCx.cone, ShellCx.pC, Prod.fst_add, Prod.snd_add, Set.mem_ofPred_eq]; omega
  · rintro g ⟨h1, h2⟩
    simp only [ShellCx.cone, ShellCx.vJC, Prod.fst_add, Prod.snd_add, Set.mem_ofPred_eq]; omega
  · simp [dot, ShellCx.nJC, ShellCx.vJC]
  · simp [dot, ShellCx.nJC, ShellCx.pC]
  · simp [dot, ShellCx.nJC, ShellCx.vJ1C]
  · show IsCoprime (1 : ℤ) 0; exact isCoprime_one_left
  · show IsCoprime (0 : ℤ) 1; exact isCoprime_one_right
  · show IsCoprime (1 : ℤ) (-2); exact isCoprime_one_left

/-! ## §11 `exists_case2_window` from a Lemma 2.4 window, a (4.1) run, and nothing else

`ColleReg.exists_case2_window` (`RegionSteps.lean`) asks for `S₁ Q B τ pw R` with nine
conjuncts.  §8 produced everything about the window; what was still open was the region `R`
(neither `Â_∞^(ε)` — `ShellConvex.not_forall_isLatticeConvexRegion_shellInf_of_hRconv` — nor
`Â_∞`, one layer too high) and the seed pair `hline` / `hbase`.

**`R`.**  Take the sweep witness `s` of the point `z₀ + K • v_J` on the new line
(`cg.bottom ε`, conjunct (ii)) and set

  `shiftRegion cg s ε := (Â_∞ + s • v_{J-1}) ∩ {⟪n_J, ·⟫ ≥ c_J - ε}`.

It is inside `Â_∞^(ε)` by the shell formula (`shiftRegion_subset_shellInf`), and it is a
`(p, v_J)`-region (`isRegion_shiftRegion`): a translate of the lattice-convex `Â_∞` cut by an
integral half-plane whose boundary is parallel to `v_J` (`cg.dot_nJ_vJ`) and into which `p`
points (`dot_nJ_p_pos`) — `LE2.isRegion_inter_halfPlaneGE` (`RegionCutGE.lean`) does that.
The absorption lemma of §7 lands the swept `Q`, and every translate of the window by a window
point at absolute level `≥ 1`, inside it.

**The seed.**  `exists_case2_window_core` takes Collé's (4.1) as `hrun`: a point `q` of `W`
strictly above the `⟪n_J,·⟫`-minimal face with `|face| - 1` consecutive `v_J`-points in `W`.
This is the first disjunct of `L1Data.exists_side_with_run_of_latticeConvex`
(`L1Fields.lean:633`) at `n := toReal (-n_J)`; the *other* disjunct is the wrong side here,
because the face on the new line is forced to be the `n_J`-minimal one.  Then `B := {q + v}`
and `pw := |face| - 1` give `hline`, and `hdef` transports by `P_translate`.

**`hbase` is the one conjunct with an absolute-position cost.**  With `b ∈ B ⊆ Q ⊆ S₁` and
`b + S₁ ⊆ R ⊆ Â_∞^(ε)`, `b` is both a window point (level `≥ c_J - ε`) and a translation
vector carrying the face (level `c_J - ε - 1`) into the shell (level `≥ 1`), so the window
must be at least `ε + 2 - c_J` levels tall — `Case2WindowProbe.window_height` proves this is
forced by the conjuncts.  `exists_case2_window_of_run_of_height` shows it is also sufficient.
`exists_case2_window_weak_of_run` shows that *without* `b ∈ B` — i.e. with `hbase` split into
`B.Nonempty ∧ ∃ b, ∀ z ∈ S₁, b + z ∈ R`, which is all `case1_sweep`'s consumers read
(`pos_pw_of_case1_hyps` uses `B.Nonempty`; `L3Band.exists_band_repeat_callsite` destructures
`⟨b, -, hbR⟩`) — no height condition is needed at all: the base point `τ₂ • v_J + p` sits far
out along the line.  ⚠ Which of the two the consumer wants is a signature decision on
`RegionSteps.lean`, not made here. -/

theorem isLatticeConvexRegion_sub_mem {A : Set (ℤ × ℤ)} (hA : IsLatticeConvexRegion A)
    (w : ℤ × ℤ) : IsLatticeConvexRegion {z | z - w ∈ A} := by
  obtain ⟨C, hCc, hCcl, hAC⟩ := hA
  refine ⟨(fun x : ℝ × ℝ => x + -toReal w) ⁻¹' C, hCc.translate_preimage_left _,
    hCcl.preimage (continuous_add_const _), ?_⟩
  ext z
  show z - w ∈ A ↔ toReal z + -toReal w ∈ C
  rw [hAC, ← sub_eq_add_neg, ← toReal_sub]
  exact Iff.rfl

theorem add_nsmul_mem_of_rec {A : Set (ℤ × ℤ)} {v : ℤ × ℤ} (hrec : ∀ g ∈ A, g + v ∈ A)
    {g : ℤ × ℤ} (hg : g ∈ A) (k : ℕ) : g + (k : ℤ) • v ∈ A := by
  induction k with
  | zero => simpa using hg
  | succ m ih =>
    have h := hrec _ ih
    have e : g + (m : ℤ) • v + v = g + ((m + 1 : ℕ) : ℤ) • v := by
      push_cast
      rw [add_smul, one_smul]
      abel
    rwa [e] at h

def shiftRegion (cg : ChainDataGeom ξ xper vl p S gen) (s ε : ℕ) : Set (ℤ × ℤ) :=
  {z | z - (s : ℤ) • cg.vJ1 ∈ ⋃ i, cg.toChainData.Ahat i} ∩
    halfPlaneGE cg.nJ (cg.cJ - (ε : ℤ))

theorem mem_shiftRegion (cg : ChainDataGeom ξ xper vl p S gen) {s ε : ℕ} {z : ℤ × ℤ} :
    z ∈ shiftRegion cg s ε ↔
      z - (s : ℤ) • cg.vJ1 ∈ ⋃ i, cg.toChainData.Ahat i ∧ cg.cJ - (ε : ℤ) ≤ dot cg.nJ z :=
  Iff.rfl

theorem shiftRegion_subset_shellInf (cg : ChainDataGeom ξ xper vl p S gen) (s ε : ℕ) :
    shiftRegion cg s ε ⊆ cg.toChainData.shellInf ε := by
  intro z hz
  rw [mem_shiftRegion] at hz
  rw [cg.shellInf_eq]
  exact ⟨z - (s : ℤ) • cg.vJ1, hz.1, s, by abel, hz.2⟩

theorem add_p_mem_shiftRegion (cg : ChainDataGeom ξ xper vl p S gen) {s ε : ℕ} {z : ℤ × ℤ}
    (hz : z ∈ shiftRegion cg s ε) : z + p ∈ shiftRegion cg s ε := by
  rw [mem_shiftRegion] at hz ⊢
  have hpos := dot_nJ_p_pos cg
  refine ⟨?_, ?_⟩
  · have e : z + p - (s : ℤ) • cg.vJ1 = (z - (s : ℤ) • cg.vJ1) + p := by abel
    rw [e]; exact cg.rec_p _ hz.1
  · rw [dot_add]; omega

theorem isRegion_shiftRegion (cg : ChainDataGeom ξ xper vl p S gen)
    (hRconv : IsLatticeConvexRegion (⋃ i, cg.toChainData.Ahat i)) (s ε : ℕ) :
    Colle41.IsRegion (shiftRegion cg s ε) p cg.vJ := by
  obtain ⟨g₀, hg₀⟩ := cg.ahat_nonempty
  have hR₀ : Colle41.IsRegion {z | z - (s : ℤ) • cg.vJ1 ∈ ⋃ i, cg.toChainData.Ahat i} cg.vJ p := by
    refine ⟨isLatticeConvexRegion_sub_mem hRconv _,
      ⟨g₀ + (s : ℤ) • cg.vJ1, fun k => ?_⟩, ⟨g₀ + (s : ℤ) • cg.vJ1, fun k => ?_⟩⟩
    · change g₀ + (s : ℤ) • cg.vJ1 + (k : ℤ) • cg.vJ - (s : ℤ) • cg.vJ1 ∈
        ⋃ i, cg.toChainData.Ahat i
      have e : g₀ + (s : ℤ) • cg.vJ1 + (k : ℤ) • cg.vJ - (s : ℤ) • cg.vJ1
          = g₀ + (k : ℤ) • cg.vJ := by abel
      rw [e]; exact add_nsmul_mem_of_rec cg.rec_vJ hg₀ k
    · change g₀ + (s : ℤ) • cg.vJ1 + (k : ℤ) • p - (s : ℤ) • cg.vJ1 ∈
        ⋃ i, cg.toChainData.Ahat i
      have e : g₀ + (s : ℤ) • cg.vJ1 + (k : ℤ) • p - (s : ℤ) • cg.vJ1
          = g₀ + (k : ℤ) • p := by abel
      rw [e]; exact add_nsmul_mem_of_rec cg.rec_p hg₀ k
  have h := isRegion_inter_halfPlaneGE hR₀ cg.nJ (cg.cJ - (ε : ℤ)) cg.dot_nJ_vJ (dot_nJ_p_pos cg)
  exact ⟨h.1, h.2.2, h.2.1⟩

/-- `n_J` is parallel to `perp v_J`: both are primitive and both are orthogonal to `v_J`. -/
theorem nJ_eq_perp_or_neg (cg : ChainDataGeom ξ xper vl p S gen) :
    cg.nJ = perp cg.vJ ∨ cg.nJ = -perp cg.vJ := by
  have hprim : Primitive (perp cg.vJ) := by
    have h := cg.vJ_prim
    unfold Primitive at h ⊢
    exact h.symm.neg_left
  refine eq_or_eq_neg_of_det_eq_zero hprim cg.nJ_prim ?_
  have h := cg.dot_nJ_vJ
  simp only [det, perp, dot] at h ⊢
  linarith

/-- The normal `toReal (-n_J)` used by §11's window is one of L1's two cut normals. -/
theorem exists_cutNormal_eq (cg : ChainDataGeom ξ xper vl p S gen) :
    ∃ e : Bool, L1Data.cutNormal e cg.vJ = toReal (-cg.nJ) := by
  rcases nJ_eq_perp_or_neg cg with h | h
  · exact ⟨false, by unfold L1Data.cutNormal; rw [h]; rfl⟩
  · exact ⟨true, by unfold L1Data.cutNormal; rw [h, neg_neg]; rfl⟩

theorem exists_case2_window_core (cg : ChainDataGeom ξ xper vl p S gen)
    (hRconv : IsLatticeConvexRegion (⋃ i, cg.toChainData.Ahat i))
    {W : Finset (ℤ × ℤ)} (hW : IsGeneratingSet ξ W)
    (htrans : ∀ v : ℤ × ℤ, IsGeneratingSet ξ (W.image (· + v)))
    (hdef : ∀ (n : ℝ × ℝ) (cmax cmin : ℝ),
      (∀ z ∈ W, inner2 n z ≤ cmax) → (Nivat.R2.face W n cmax).Nonempty →
      (∀ z ∈ W, cmin ≤ inner2 n z) → (Nivat.R2.face W n cmin).Nonempty →
        P ξ W - P ξ (W.filter fun z => inner2 n z < cmax) ≤
          (Nivat.R2.face W n cmax).card - 1 ∧
        P ξ W - P ξ (W.filter fun z => cmin < inner2 n z) ≤
          (Nivat.R2.face W n cmin).card - 1)
    (ε : ℕ)
    {a₀ : ℤ × ℤ} (ha₀W : a₀ ∈ W) (hmin : ∀ w ∈ W, dot cg.nJ a₀ ≤ dot cg.nJ w)
    {q : ℤ × ℤ} (hqgt : dot cg.nJ a₀ < dot cg.nJ q)
    (hrun : ∀ i : ℕ, i < (W.filter fun w => dot cg.nJ w = dot cg.nJ a₀).card - 1 →
      q + (i : ℤ) • cg.vJ ∈ W) :
    ∃ (v : ℤ × ℤ) (Q : Finset (ℤ × ℤ)) (τ : ℤ) (pw : ℕ) (R : Set (ℤ × ℤ)),
      IsGeneratingSet ξ (W.image (· + v)) ∧
      Q ⊆ W.image (· + v) ∧
      (∃ (n : ℝ × ℝ) (cmax : ℝ),
        n ≠ 0 ∧
        inner2 n cg.vJ = 0 ∧
        (∀ z ∈ W.image (· + v), inner2 n z ≤ cmax) ∧
        (Nivat.R2.face (W.image (· + v)) n cmax).Nonempty ∧
        Q = (W.image (· + v)).filter fun z => inner2 n z < cmax) ∧
      (∀ g ∈ W.image (· + v), g ∉ Q → ∀ t : ℤ, τ ≤ t →
        t • cg.vJ + g ∈ cg.toChainData.shellInf (ε + 1) ∧
        t • cg.vJ + g ∉ cg.toChainData.shellInf ε) ∧
      P ξ (W.image (· + v)) ≤ P ξ Q + pw ∧
      (∀ g ∈ ({q + v} : Finset (ℤ × ℤ)), ∀ i : ℕ, i < pw → g + (i : ℤ) • cg.vJ ∈ Q) ∧
      R ⊆ cg.toChainData.shellInf ε ∧
      Colle41.IsRegion R p cg.vJ ∧
      (∀ t : ℤ, τ ≤ t → ∀ z ∈ Q,
        t • cg.vJ + z ∈ R ∧ t • cg.vJ + z + (1 : ℤ) • p ∈ R) ∧
      -- extras
      dot cg.nJ (q + v) = cg.cJ - (ε : ℤ) - 1 + (dot cg.nJ q - dot cg.nJ a₀) ∧
      (∀ b ∈ W.image (· + v), 1 ≤ dot cg.nJ b → ∀ z ∈ W.image (· + v), b + z ∈ R) ∧
      (∃ b : ℤ × ℤ, ∀ z ∈ W.image (· + v), b + z ∈ R) ∧
      (q ∈ W → q + v ∈ Q) ∧
      (∃ e : Bool, pw = (L1Data.topFace e cg.vJ (W.image (· + v))).card - 1 ∧
        Q = L1Data.derivedQ e cg.vJ (W.image (· + v))) := by
  classical
  obtain ⟨z₀, L, hdz, hline, -, -⟩ := cg.bottom ε
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = W.sup (fun w => (w - a₀).1.natAbs + (w - a₀).2.natAbs) :=
    ⟨_, rfl⟩
  obtain ⟨Df, hDf⟩ : ∃ Df : (ℤ × ℤ) × (ℤ × ℤ) → ℕ,
      Df = fun qw => (det p (z₀ + (qw.1 - a₀) + (qw.2 - a₀))).natAbs := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ℕ, D = (W ×ˢ W).sup Df := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K : ℤ, K = (L.natAbs : ℤ) + (M : ℤ) + (D : ℤ) := ⟨_, rfl⟩
  have hLabs : L ≤ (L.natAbs : ℤ) := Int.le_natAbs
  have hLK : L ≤ K := by omega
  obtain ⟨v, hv⟩ : ∃ v : ℤ × ℤ, v = z₀ + K • cg.vJ - a₀ := ⟨_, rfl⟩
  obtain ⟨τ, hτ⟩ : ∃ τ : ℤ, τ = ((W.sup (fun w => (det p (w - a₀)).natAbs) : ℕ) : ℤ) :=
    ⟨_, rfl⟩
  obtain ⟨n, hn⟩ : ∃ n : ℝ × ℝ, n = toReal (-cg.nJ) := ⟨_, rfl⟩
  obtain ⟨cmax, hcmax⟩ : ∃ cmax : ℝ, cmax = -((dot cg.nJ (a₀ + v) : ℤ) : ℝ) := ⟨_, rfl⟩
  have hinner : ∀ z, inner2 n z = -((dot cg.nJ z : ℤ) : ℝ) := by
    intro z; rw [hn, inner2_toReal, dot_neg_left, Int.cast_neg]
  obtain ⟨g₀, hg₀, s, hs⟩ := hline K hLK
  have hg₀' : g₀ = z₀ + K • cg.vJ - (s : ℤ) • cg.vJ1 := by rw [hs]; abel
  have hdv : dot cg.nJ v = cg.cJ - (ε : ℤ) - 1 - dot cg.nJ a₀ := by
    rw [hv, dot_sub, dot_add, dot_zsmul_right, cg.dot_nJ_vJ, hdz]; ring
  -- the strict-side test, as an integer inequality
  have hlt_iff : ∀ w, inner2 n (w + v) < cmax ↔ dot cg.nJ a₀ < dot cg.nJ w := by
    intro w
    rw [hinner, hcmax, dot_add, dot_add]
    push_cast
    constructor
    · intro h
      have : (dot cg.nJ a₀ : ℝ) < dot cg.nJ w := by linarith
      exact_mod_cast this
    · intro h
      have : (dot cg.nJ a₀ : ℝ) < dot cg.nJ w := by exact_mod_cast h
      linarith
  have hcm : cmax - inner2 n v = -((dot cg.nJ a₀ : ℤ) : ℝ) := by
    rw [hcmax, hinner, dot_add]; push_cast; ring
  -- the `ℓ'`-face of the translate has the cardinality of the `n_J`-minimal level set of `W`
  have hfc₀ : (Nivat.R2.face (W.image (· + v)) n cmax).card
      = (Nivat.R2.face W n (-((dot cg.nJ a₀ : ℤ) : ℝ))).card := by
    rw [Nivat.L1Complexity.face_card_image_add, hcm]
  have hfaceW : Nivat.R2.face W n (-((dot cg.nJ a₀ : ℤ) : ℝ))
      = W.filter fun w => dot cg.nJ w = dot cg.nJ a₀ := by
    unfold Nivat.R2.face
    refine Finset.filter_congr fun w _ => ?_
    rw [hinner]
    constructor
    · intro h; exact_mod_cast neg_inj.mp h
    · intro h; rw [h]
  have hfc : (Nivat.R2.face (W.image (· + v)) n cmax).card
      = (W.filter fun w => dot cg.nJ w = dot cg.nJ a₀).card := by
    rw [hfc₀, hfaceW]
  -- the general membership test for `R`
  have hmemR : ∀ (y : ℤ × ℤ) (k : ℤ), 1 ≤ dot cg.nJ y → ((det p y).natAbs : ℤ) + K ≤ k →
      z₀ + y + k • cg.vJ ∈ shiftRegion cg s ε := by
    intro y k hy hk
    have hmem := add_add_zsmul_vJ_mem_ahat cg hRconv hy hg₀ (k := k - K) (by omega)
    rw [mem_shiftRegion]
    refine ⟨?_, ?_⟩
    · have e : z₀ + y + k • cg.vJ - (s : ℤ) • cg.vJ1 = g₀ + (y + (k - K) • cg.vJ) := by
        rw [hg₀', sub_smul]; abel
      rw [e]; exact hmem
    · rw [dot_add, dot_add, dot_zsmul_right, cg.dot_nJ_vJ, mul_zero, hdz]; omega
  refine ⟨v, (W.image (· + v)).filter (fun z => inner2 n z < cmax), τ,
    (Nivat.R2.face (W.image (· + v)) n cmax).card - 1, shiftRegion cg s ε,
    htrans v, Finset.filter_subset _ _, ⟨n, cmax, ?_, ?_, ?_, ?_, rfl⟩, ?_, ?_, ?_,
    shiftRegion_subset_shellInf cg s ε, isRegion_shiftRegion cg hRconv s ε, ?_, ?_, ?_, ?_, ?_,
    ?_⟩
  · -- `n ≠ 0`
    intro h
    rw [hn] at h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only [toReal, Prod.fst_neg, Prod.snd_neg, Int.cast_neg, Prod.fst_zero, Prod.snd_zero,
      neg_eq_zero, Int.cast_eq_zero] at h1 h2
    exact cg.nJ_prim.ne_zero (Prod.ext h1 h2)
  · rw [hinner, cg.dot_nJ_vJ]; simp
  · intro z hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
    rw [hinner, hcmax, dot_add, dot_add]
    push_cast
    have := (Int.cast_le (R := ℝ)).mpr (hmin w hw)
    linarith
  · exact ⟨a₀ + v, Nivat.R2.mem_face.mpr ⟨Finset.mem_image_of_mem _ ha₀W, by rw [hinner, hcmax]⟩⟩
  · -- `hface`
    intro g hgS hgQ t ht
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hgS
    have hnotlt : ¬ inner2 n (w + v) < cmax := fun h => hgQ (Finset.mem_filter.mpr ⟨hgS, h⟩)
    have heq : dot cg.nJ w = dot cg.nJ a₀ := by
      have h1 := hmin w hw
      have h2 : ¬ dot cg.nJ a₀ < dot cg.nJ w := fun h => hnotlt ((hlt_iff w).mpr h)
      omega
    obtain ⟨c, hc⟩ := eq_zsmul_vJ_of_dot_eq_zero cg (y := w - a₀) (by rw [dot_sub, heq, sub_self])
    have hcM : -(M : ℤ) ≤ c := by
      have h1 := abs_coeff_le cg.vJ_ne c
      rw [← hc] at h1
      simp only [Int.abs_eq_natAbs] at h1
      have h2 : (w - a₀).1.natAbs + (w - a₀).2.natAbs
          ≤ W.sup (fun w => (w - a₀).1.natAbs + (w - a₀).2.natAbs) :=
        Finset.le_sup (f := fun w => (w - a₀).1.natAbs + (w - a₀).2.natAbs) hw
      omega
    have hw' : w = a₀ + c • cg.vJ := by rw [← hc]; abel
    have hpt : t • cg.vJ + (w + v) = z₀ + (K + c + t) • cg.vJ := by
      rw [hw', hv, add_smul, add_smul]; abel
    have hk : L ≤ K + c + t := by omega
    refine ⟨?_, ?_⟩
    · rw [hpt]; exact bottom_mem_shellInf_succ cg ε hdz hline hk
    · rw [hpt, cg.shellInf_eq]
      rintro ⟨-, -, -, -, hd⟩
      rw [dot_add, dot_zsmul_right, cg.dot_nJ_vJ, hdz] at hd
      omega
  · -- `hdef`, transported along the translation
    have hle₀ : ∀ z ∈ W, inner2 n z ≤ -((dot cg.nJ a₀ : ℤ) : ℝ) := by
      intro z hz
      rw [hinner]
      have := (Int.cast_le (R := ℝ)).mpr (hmin z hz)
      linarith
    have hfne₀ : (Nivat.R2.face W n (-((dot cg.nJ a₀ : ℤ) : ℝ))).Nonempty :=
      ⟨a₀, Nivat.R2.mem_face.mpr ⟨ha₀W, by rw [hinner]⟩⟩
    obtain ⟨zmin, hzminW, hzmin⟩ := W.exists_min_image (fun z => inner2 n z) hW.1
    have hd := (hdef n _ (inner2 n zmin) hle₀ hfne₀ hzmin
      ⟨zmin, Nivat.R2.mem_face.mpr ⟨hzminW, rfl⟩⟩).1
    have hQ : (W.image (· + v)).filter (fun z => inner2 n z < cmax)
        = (W.filter fun z => inner2 n z < -((dot cg.nJ a₀ : ℤ) : ℝ)).image (· + v) := by
      rw [Finset.filter_image]
      congr 1
      refine Finset.filter_congr fun z _ => ?_
      rw [inner2_add, ← hcm]
      constructor <;> intro h <;> linarith
    rw [hQ, hfc₀, P_translate, P_translate]
    omega
  · -- `hline`: the run from `q + v`
    intro g hg i hi
    rw [Finset.mem_singleton] at hg
    subst hg
    rw [hfc] at hi
    have hmem := hrun i hi
    have e : q + v + (i : ℤ) • cg.vJ = (q + (i : ℤ) • cg.vJ) + v := by abel
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · rw [e]; exact Finset.mem_image_of_mem _ hmem
    · rw [e, hlt_iff, dot_add, dot_zsmul_right, cg.dot_nJ_vJ, mul_zero, add_zero]
      exact hqgt
  · -- `hQR`
    intro t ht z hz
    obtain ⟨hzS, hzlt⟩ := Finset.mem_filter.mp hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hzS
    have hgt : dot cg.nJ a₀ < dot cg.nJ w := (hlt_iff w).mp hzlt
    have hw1 : 1 ≤ dot cg.nJ (w - a₀) := by rw [dot_sub]; omega
    have hτ' : ((det p (w - a₀)).natAbs : ℤ) ≤ t := by
      have h : (det p (w - a₀)).natAbs ≤ W.sup (fun w => (det p (w - a₀)).natAbs) :=
        Finset.le_sup (f := fun w => (det p (w - a₀)).natAbs) hw
      omega
    have hin : t • cg.vJ + (w + v) ∈ shiftRegion cg s ε := by
      have e : t • cg.vJ + (w + v) = z₀ + (w - a₀) + (K + t) • cg.vJ := by
        rw [hv, add_smul]; abel
      rw [e]; exact hmemR (w - a₀) (K + t) hw1 (by omega)
    exact ⟨hin, by rw [one_smul]; exact add_p_mem_shiftRegion cg hin⟩
  · -- level of the seed point
    rw [dot_add, hdv]; ring
  · -- `hself`: a window point at absolute level `≥ 1` carries the window into `R`
    intro b hb hb1 z hz
    obtain ⟨q', hq', rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
    have hw0 := hmin w hw
    rw [dot_add, hdv] at hb1
    have hy1 : 1 ≤ dot cg.nJ (z₀ + (q' - a₀) + (w - a₀)) := by
      rw [dot_add, dot_add, dot_sub, dot_sub, hdz]; omega
    have hDle : ((det p (z₀ + (q' - a₀) + (w - a₀))).natAbs : ℤ) ≤ K := by
      have hmemP : (q', w) ∈ W ×ˢ W := Finset.mem_product.mpr ⟨hq', hw⟩
      have h : Df (q', w) ≤ (W ×ˢ W).sup Df := Finset.le_sup (f := Df) hmemP
      have hval : Df (q', w) = (det p (z₀ + (q' - a₀) + (w - a₀))).natAbs := by rw [hDf]
      omega
    have e : q' + v + (w + v) = z₀ + (z₀ + (q' - a₀) + (w - a₀)) + (K + K) • cg.vJ := by
      rw [hv, add_smul]; abel
    rw [e]; exact hmemR _ (K + K) hy1 (by omega)
  · -- `hfar`: a base point far out along `v_J`, one `p`-step up
    obtain ⟨τ₂, hτ₂⟩ : ∃ τ₂ : ℤ, τ₂ = ((W.sup (fun w => (det p (w - a₀ + p)).natAbs) : ℕ) : ℤ) :=
      ⟨_, rfl⟩
    refine ⟨τ₂ • cg.vJ + p, ?_⟩
    intro z hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
    have hw0 := hmin w hw
    have hpos := dot_nJ_p_pos cg
    have hy1 : 1 ≤ dot cg.nJ (w - a₀ + p) := by rw [dot_add, dot_sub]; omega
    have hle : ((det p (w - a₀ + p)).natAbs : ℤ) + K ≤ K + τ₂ := by
      have h : (det p (w - a₀ + p)).natAbs ≤ W.sup (fun w => (det p (w - a₀ + p)).natAbs) :=
        Finset.le_sup (f := fun w => (det p (w - a₀ + p)).natAbs) hw
      omega
    have e : τ₂ • cg.vJ + p + (w + v) = z₀ + (w - a₀ + p) + (K + τ₂) • cg.vJ := by
      rw [hv, add_smul]; abel
    rw [e]; exact hmemR _ (K + τ₂) hy1 hle
  · -- the run seed is in `Q`
    intro hqW
    exact Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ hqW, (hlt_iff q).mpr hqgt⟩
  · -- conjunct 11's shape: `Q` and `pw` are L1's derived cut and top-face width
    obtain ⟨e, he⟩ := exists_cutNormal_eq cg
    have hne : (W.image (· + v)).Nonempty := ⟨a₀ + v, Finset.mem_image_of_mem _ ha₀W⟩
    have hbound : ∀ z ∈ W.image (· + v), inner2 n z ≤ cmax := by
      intro z hz
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
      rw [hinner, hcmax, dot_add, dot_add]
      push_cast
      have := (Int.cast_le (R := ℝ)).mpr (hmin w hw)
      linarith
    have hlev : L1Data.levelMax (W.image (· + v)) n = cmax := by
      unfold L1Data.levelMax
      rw [dif_pos hne]
      apply le_antisymm
      · exact Finset.sup'_le hne _ hbound
      · have h := Finset.le_sup' (fun z => inner2 n z) (Finset.mem_image_of_mem (· + v) ha₀W)
        have hc : cmax = inner2 n (a₀ + v) := by rw [hinner, hcmax]
        rw [hc]; exact h
    refine ⟨e, ?_, ?_⟩
    · unfold L1Data.topFace; rw [he, ← hn, hlev]
    · unfold L1Data.derivedQ; rw [he, ← hn, hlev]

theorem exists_case2_window_of_run_of_height (cg : ChainDataGeom ξ xper vl p S gen)
    (hRconv : IsLatticeConvexRegion (⋃ i, cg.toChainData.Ahat i))
    {W : Finset (ℤ × ℤ)} (hW : IsGeneratingSet ξ W)
    (htrans : ∀ v : ℤ × ℤ, IsGeneratingSet ξ (W.image (· + v)))
    (hdef : ∀ (n : ℝ × ℝ) (cmax cmin : ℝ),
      (∀ z ∈ W, inner2 n z ≤ cmax) → (Nivat.R2.face W n cmax).Nonempty →
      (∀ z ∈ W, cmin ≤ inner2 n z) → (Nivat.R2.face W n cmin).Nonempty →
        P ξ W - P ξ (W.filter fun z => inner2 n z < cmax) ≤
          (Nivat.R2.face W n cmax).card - 1 ∧
        P ξ W - P ξ (W.filter fun z => cmin < inner2 n z) ≤
          (Nivat.R2.face W n cmin).card - 1)
    (ε : ℕ)
    {a₀ : ℤ × ℤ} (ha₀W : a₀ ∈ W) (hmin : ∀ w ∈ W, dot cg.nJ a₀ ≤ dot cg.nJ w)
    {q : ℤ × ℤ} (hqW : q ∈ W) (hqgt : dot cg.nJ a₀ < dot cg.nJ q)
    (hrun : ∀ i : ℕ, i < (W.filter fun w => dot cg.nJ w = dot cg.nJ a₀).card - 1 →
      q + (i : ℤ) • cg.vJ ∈ W)
    (hheight : (ε : ℤ) + 2 - cg.cJ ≤ dot cg.nJ q - dot cg.nJ a₀) :
    ∃ (S₁ Q B : Finset (ℤ × ℤ)) (τ : ℤ) (pw : ℕ) (R : Set (ℤ × ℤ)),
      IsGeneratingSet ξ S₁ ∧
      Q ⊆ S₁ ∧
      (∃ (n : ℝ × ℝ) (cmax : ℝ),
        n ≠ 0 ∧
        inner2 n cg.vJ = 0 ∧
        (∀ z ∈ S₁, inner2 n z ≤ cmax) ∧
        (Nivat.R2.face S₁ n cmax).Nonempty ∧
        Q = S₁.filter fun z => inner2 n z < cmax) ∧
      (∀ g ∈ S₁, g ∉ Q → ∀ t : ℤ, τ ≤ t →
        t • cg.vJ + g ∈ cg.toChainData.shellInf (ε + 1) ∧
        t • cg.vJ + g ∉ cg.toChainData.shellInf ε) ∧
      P ξ S₁ ≤ P ξ Q + pw ∧
      (∀ g ∈ B, ∀ i : ℕ, i < pw → g + (i : ℤ) • cg.vJ ∈ Q) ∧
      R ⊆ cg.toChainData.shellInf ε ∧
      Colle41.IsRegion R p cg.vJ ∧
      (∀ t : ℤ, τ ≤ t → ∀ z ∈ Q,
        t • cg.vJ + z ∈ R ∧ t • cg.vJ + z + (1 : ℤ) • p ∈ R) ∧
      (∃ b ∈ B, ∀ z ∈ S₁, b + z ∈ R) := by
  obtain ⟨v, Q, τ, pw, R, h1, h2, h3, h4, h5, h6, h7, h8, h9, hlev, hself, -, -, -⟩ :=
    exists_case2_window_core cg hRconv hW htrans hdef ε ha₀W hmin hqgt hrun
  refine ⟨W.image (· + v), Q, {q + v}, τ, pw, R, h1, h2, h3, h4, h5, h6, h7, h8, h9,
    q + v, Finset.mem_singleton_self _, ?_⟩
  exact hself (q + v) (Finset.mem_image_of_mem _ hqW) (by rw [hlev]; omega)

theorem exists_case2_window_weak_of_run (cg : ChainDataGeom ξ xper vl p S gen)
    (hRconv : IsLatticeConvexRegion (⋃ i, cg.toChainData.Ahat i))
    {W : Finset (ℤ × ℤ)} (hW : IsGeneratingSet ξ W)
    (htrans : ∀ v : ℤ × ℤ, IsGeneratingSet ξ (W.image (· + v)))
    (hdef : ∀ (n : ℝ × ℝ) (cmax cmin : ℝ),
      (∀ z ∈ W, inner2 n z ≤ cmax) → (Nivat.R2.face W n cmax).Nonempty →
      (∀ z ∈ W, cmin ≤ inner2 n z) → (Nivat.R2.face W n cmin).Nonempty →
        P ξ W - P ξ (W.filter fun z => inner2 n z < cmax) ≤
          (Nivat.R2.face W n cmax).card - 1 ∧
        P ξ W - P ξ (W.filter fun z => cmin < inner2 n z) ≤
          (Nivat.R2.face W n cmin).card - 1)
    (ε : ℕ)
    {a₀ : ℤ × ℤ} (ha₀W : a₀ ∈ W) (hmin : ∀ w ∈ W, dot cg.nJ a₀ ≤ dot cg.nJ w)
    {q : ℤ × ℤ} (hqgt : dot cg.nJ a₀ < dot cg.nJ q)
    (hrun : ∀ i : ℕ, i < (W.filter fun w => dot cg.nJ w = dot cg.nJ a₀).card - 1 →
      q + (i : ℤ) • cg.vJ ∈ W) :
    ∃ (S₁ Q B : Finset (ℤ × ℤ)) (τ : ℤ) (pw : ℕ) (R : Set (ℤ × ℤ)),
      IsGeneratingSet ξ S₁ ∧
      Q ⊆ S₁ ∧
      (∃ (n : ℝ × ℝ) (cmax : ℝ),
        n ≠ 0 ∧
        inner2 n cg.vJ = 0 ∧
        (∀ z ∈ S₁, inner2 n z ≤ cmax) ∧
        (Nivat.R2.face S₁ n cmax).Nonempty ∧
        Q = S₁.filter fun z => inner2 n z < cmax) ∧
      (∀ g ∈ S₁, g ∉ Q → ∀ t : ℤ, τ ≤ t →
        t • cg.vJ + g ∈ cg.toChainData.shellInf (ε + 1) ∧
        t • cg.vJ + g ∉ cg.toChainData.shellInf ε) ∧
      P ξ S₁ ≤ P ξ Q + pw ∧
      (∀ g ∈ B, ∀ i : ℕ, i < pw → g + (i : ℤ) • cg.vJ ∈ Q) ∧
      R ⊆ cg.toChainData.shellInf ε ∧
      Colle41.IsRegion R p cg.vJ ∧
      (∀ t : ℤ, τ ≤ t → ∀ z ∈ Q,
        t • cg.vJ + z ∈ R ∧ t • cg.vJ + z + (1 : ℤ) • p ∈ R) ∧
      B.Nonempty ∧ (∃ b : ℤ × ℤ, ∀ z ∈ S₁, b + z ∈ R) := by
  obtain ⟨v, Q, τ, pw, R, h1, h2, h3, h4, h5, h6, h7, h8, h9, -, -, hfar, -, -⟩ :=
    exists_case2_window_core cg hRconv hW htrans hdef ε ha₀W hmin hqgt hrun
  exact ⟨W.image (· + v), Q, {q + v}, τ, pw, R, h1, h2, h3, h4, h5, h6, h7, h8, h9,
    Finset.singleton_nonempty _, hfar⟩

/-- **The eleven-conjunct producer.**  Same inputs as `exists_case2_window_of_run_of_height`;
the conclusion is `exists_case2_window`'s (`RegionSteps.lean`, 2026-09-19 eleven-conjunct
form) verbatim.  `B` is L1's maximal baseline `maxB (derivedQ e v_J S₁) v_J pw`, which contains
the run seed `q + v` by `hrun`, so `hline` is `maxB_hBQ` and `hbase` keeps the witness `q + v`.
The normal `toReal (-n_J)` is `cutNormal e v_J` for the `e` chosen by `exists_cutNormal_eq`.

⚠ **Superseded 2026-09-19 by `exists_case2_window_maxB_weak_of_run`** (kept per `PROTOCOL.md`
§14): `exists_case2_window`'s conjunct 9 was weakened to `B.Nonempty ∧ ∃ b, ∀ z ∈ S₁, b + z ∈ R`
precisely because the strong form `∃ b ∈ B, …` used here forces `hheight` — an absolute
window-height condition on Lemma 2.4's `𝒮` that nothing in the tree produces
(`Case2WindowProbe.window_height` shows it is forced, not an artefact of this proof). -/
theorem exists_case2_window_maxB_of_run_of_height (cg : ChainDataGeom ξ xper vl p S gen)
    (hRconv : IsLatticeConvexRegion (⋃ i, cg.toChainData.Ahat i))
    {W : Finset (ℤ × ℤ)} (hW : IsGeneratingSet ξ W)
    (htrans : ∀ v : ℤ × ℤ, IsGeneratingSet ξ (W.image (· + v)))
    (hdef : ∀ (n : ℝ × ℝ) (cmax cmin : ℝ),
      (∀ z ∈ W, inner2 n z ≤ cmax) → (Nivat.R2.face W n cmax).Nonempty →
      (∀ z ∈ W, cmin ≤ inner2 n z) → (Nivat.R2.face W n cmin).Nonempty →
        P ξ W - P ξ (W.filter fun z => inner2 n z < cmax) ≤
          (Nivat.R2.face W n cmax).card - 1 ∧
        P ξ W - P ξ (W.filter fun z => cmin < inner2 n z) ≤
          (Nivat.R2.face W n cmin).card - 1)
    (ε : ℕ)
    {a₀ : ℤ × ℤ} (ha₀W : a₀ ∈ W) (hmin : ∀ w ∈ W, dot cg.nJ a₀ ≤ dot cg.nJ w)
    {q : ℤ × ℤ} (hqW : q ∈ W) (hqgt : dot cg.nJ a₀ < dot cg.nJ q)
    (hrun : ∀ i : ℕ, i < (W.filter fun w => dot cg.nJ w = dot cg.nJ a₀).card - 1 →
      q + (i : ℤ) • cg.vJ ∈ W)
    (hheight : (ε : ℤ) + 2 - cg.cJ ≤ dot cg.nJ q - dot cg.nJ a₀) :
    ∃ (S₁ Q B : Finset (ℤ × ℤ)) (τ : ℤ) (pw : ℕ) (R : Set (ℤ × ℤ)),
      IsGeneratingSet ξ S₁ ∧
      Q ⊆ S₁ ∧
      (∃ (n : ℝ × ℝ) (cmax : ℝ),
        n ≠ 0 ∧
        inner2 n cg.vJ = 0 ∧
        (∀ z ∈ S₁, inner2 n z ≤ cmax) ∧
        (Nivat.R2.face S₁ n cmax).Nonempty ∧
        Q = S₁.filter fun z => inner2 n z < cmax) ∧
      (∀ g ∈ S₁, g ∉ Q → ∀ t : ℤ, τ ≤ t →
        t • cg.vJ + g ∈ cg.toChainData.shellInf (ε + 1) ∧
        t • cg.vJ + g ∉ cg.toChainData.shellInf ε) ∧
      P ξ S₁ ≤ P ξ Q + pw ∧
      (∀ g ∈ B, ∀ i : ℕ, i < pw → g + (i : ℤ) • cg.vJ ∈ Q) ∧
      R ⊆ cg.toChainData.shellInf ε ∧
      Colle41.IsRegion R p cg.vJ ∧
      (∀ t : ℤ, τ ≤ t → ∀ z ∈ Q,
        t • cg.vJ + z ∈ R ∧ t • cg.vJ + z + (1 : ℤ) • p ∈ R) ∧
      (∃ b ∈ B, ∀ z ∈ S₁, b + z ∈ R) ∧
      (∃ e : Bool, pw = (L1Data.topFace e cg.vJ S₁).card - 1 ∧
        B = L1Data.maxB (L1Data.derivedQ e cg.vJ S₁) cg.vJ pw) := by
  obtain ⟨v, Q, τ, pw, R, h1, h2, h3, h4, h5, h6, h7, h8, h9, hlev, hself, -, hqQ, e, hpw,
    hQd⟩ := exists_case2_window_core cg hRconv hW htrans hdef ε ha₀W hmin hqgt hrun
  subst hQd
  have hqvB : q + v ∈ L1Data.maxB (L1Data.derivedQ e cg.vJ (W.image (· + v))) cg.vJ pw :=
    L1Data.mem_maxB.mpr ⟨hqQ hqW, h6 (q + v) (Finset.mem_singleton_self _)⟩
  refine ⟨W.image (· + v), _, L1Data.maxB (L1Data.derivedQ e cg.vJ (W.image (· + v))) cg.vJ pw,
    τ, pw, R, h1, h2, h3, h4, h5, L1Data.maxB_hBQ _ _ _, h7, h8, h9,
    ⟨q + v, hqvB, hself (q + v) (Finset.mem_image_of_mem _ hqW) (by rw [hlev]; omega)⟩,
    e, hpw, rfl⟩

/-- **The eleven-conjunct producer, weak-`hbase` form (2026-09-19, after the integrator weakened
conjunct 9 to `B.Nonempty ∧ ∃ b, ∀ z ∈ S₁, b + z ∈ R`).**  No height hypothesis: `B.Nonempty`
is witnessed by the run seed `q + v ∈ maxB …`, and the covering base point is the far-out
`τ₂ • v_J + p` of `exists_case2_window_core`'s `hfar`, which need not lie in `B`.  This is the
form whose conclusion is `exists_case2_window`'s, verbatim, as of `RegionSteps.lean` today. -/
theorem exists_case2_window_maxB_weak_of_run (cg : ChainDataGeom ξ xper vl p S gen)
    (hRconv : IsLatticeConvexRegion (⋃ i, cg.toChainData.Ahat i))
    {W : Finset (ℤ × ℤ)} (hW : IsGeneratingSet ξ W)
    (htrans : ∀ v : ℤ × ℤ, IsGeneratingSet ξ (W.image (· + v)))
    (hdef : ∀ (n : ℝ × ℝ) (cmax cmin : ℝ),
      (∀ z ∈ W, inner2 n z ≤ cmax) → (Nivat.R2.face W n cmax).Nonempty →
      (∀ z ∈ W, cmin ≤ inner2 n z) → (Nivat.R2.face W n cmin).Nonempty →
        P ξ W - P ξ (W.filter fun z => inner2 n z < cmax) ≤
          (Nivat.R2.face W n cmax).card - 1 ∧
        P ξ W - P ξ (W.filter fun z => cmin < inner2 n z) ≤
          (Nivat.R2.face W n cmin).card - 1)
    (ε : ℕ)
    {a₀ : ℤ × ℤ} (ha₀W : a₀ ∈ W) (hmin : ∀ w ∈ W, dot cg.nJ a₀ ≤ dot cg.nJ w)
    {q : ℤ × ℤ} (hqW : q ∈ W) (hqgt : dot cg.nJ a₀ < dot cg.nJ q)
    (hrun : ∀ i : ℕ, i < (W.filter fun w => dot cg.nJ w = dot cg.nJ a₀).card - 1 →
      q + (i : ℤ) • cg.vJ ∈ W) :
    ∃ (S₁ Q B : Finset (ℤ × ℤ)) (τ : ℤ) (pw : ℕ) (R : Set (ℤ × ℤ)),
      IsGeneratingSet ξ S₁ ∧
      Q ⊆ S₁ ∧
      (∃ (n : ℝ × ℝ) (cmax : ℝ),
        n ≠ 0 ∧
        inner2 n cg.vJ = 0 ∧
        (∀ z ∈ S₁, inner2 n z ≤ cmax) ∧
        (Nivat.R2.face S₁ n cmax).Nonempty ∧
        Q = S₁.filter fun z => inner2 n z < cmax) ∧
      (∀ g ∈ S₁, g ∉ Q → ∀ t : ℤ, τ ≤ t →
        t • cg.vJ + g ∈ cg.toChainData.shellInf (ε + 1) ∧
        t • cg.vJ + g ∉ cg.toChainData.shellInf ε) ∧
      P ξ S₁ ≤ P ξ Q + pw ∧
      (∀ g ∈ B, ∀ i : ℕ, i < pw → g + (i : ℤ) • cg.vJ ∈ Q) ∧
      R ⊆ cg.toChainData.shellInf ε ∧
      Colle41.IsRegion R p cg.vJ ∧
      (∀ t : ℤ, τ ≤ t → ∀ z ∈ Q,
        t • cg.vJ + z ∈ R ∧ t • cg.vJ + z + (1 : ℤ) • p ∈ R) ∧
      (B.Nonempty ∧ ∃ b, ∀ z ∈ S₁, b + z ∈ R) ∧
      (∃ e : Bool, pw = (L1Data.topFace e cg.vJ S₁).card - 1 ∧
        B = L1Data.maxB (L1Data.derivedQ e cg.vJ S₁) cg.vJ pw) := by
  obtain ⟨v, Q, τ, pw, R, h1, h2, h3, h4, h5, h6, h7, h8, h9, -, -, hfar, hqQ, e, hpw,
    hQd⟩ := exists_case2_window_core cg hRconv hW htrans hdef ε ha₀W hmin hqgt hrun
  subst hQd
  have hqvB : q + v ∈ L1Data.maxB (L1Data.derivedQ e cg.vJ (W.image (· + v))) cg.vJ pw :=
    L1Data.mem_maxB.mpr ⟨hqQ hqW, h6 (q + v) (Finset.mem_singleton_self _)⟩
  exact ⟨W.image (· + v), _, L1Data.maxB (L1Data.derivedQ e cg.vJ (W.image (· + v))) cg.vJ pw,
    τ, pw, R, h1, h2, h3, h4, h5, L1Data.maxB_hBQ _ _ _, h7, h8, h9, ⟨⟨q + v, hqvB⟩, hfar⟩,
    e, hpw, rfl⟩

end Nivat.ColleReg.Claim411
