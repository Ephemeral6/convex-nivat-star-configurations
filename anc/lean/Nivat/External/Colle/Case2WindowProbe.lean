/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.RegionSteps
import Nivat.External.Colle.ShellConvex

/-!
# Probe: is the conclusion of `exists_case2_window` satisfiable?

`ColleReg.exists_case2_window` (`RegionSteps.lean`; body `sorry` until 2026-09-19 ~10:50, now wired
to `Claim411.exists_case2_window_maxB_weak_of_run` + `exists_case2_run`, see §7) promises eleven conjuncts (ten, plus
the `hBmax` conjunct added 2026-09-19) about a window `S₁`, its sublevel part `Q`, a seed `B`, a height `τ`, a width `pw` and a region `R`.
A `sorry` body compiles whatever the conjuncts say, so this file asks the kernel two things:

1. **What do the conjuncts force?** (§1, over an *arbitrary* `ChainDataGeom` and arbitrary
   witnesses.)  The face `S₁ \ Q` sits at level exactly `c_J - ε - 1`; `Q` sits at levels
   `≥ c_J - ε`; once `0 < pw`, `B ⊆ Q`; and the `hbase` witness `b ∈ B` then satisfies
   `1 ≤ ⟪n_J, b⟫`.  So the window must contain a point at absolute level `≥ 1` *and* a point at
   absolute level `c_J - ε - 1`: its `n_J`-height is at least `ε + 2 - c_J`.  In the context of
   `region_periods_and_rays` (which also has `hp_per`), `0 < pw` is itself forced
   (`pos_pw_of_conclusion`).
2. **Is there a model at all?** (§2.)  Yes: on `Nivat.ShellConvex.cgc` at `ε = 1` the window
   `{2,3} × {-2,…,1}` with `Q = {2,3} × {-1,0,1}`, `B = Q`, `pw = 1`, `τ = 10`,
   `R = Â_∞^{(1)}` satisfies all eleven conjuncts (`window_model`); §5's `target_type_eq` is what
   identifies that statement with the conclusion of `exists_case2_window` at `cgc` (the theorem's
   own hypotheses are known-false for `etaC`, so nothing here is a satisfaction result for the
   *theorem*, only for its conclusion).  ⚠ `ξ = etaC` has
   infinite range, so `P etaC W = 0` for every nonempty `W` (`P_etaC_eq_zero`) and the deficit
   conjunct is trivial in this model.

§0 records that neither `cgc` nor `cgn` satisfies the binder `hSφ : IsGeneratingSet ξ S`
(`not_isGeneratingSet_etaC_Sw`): both have `S = {0}`, and `{0}` generates nothing.

3. **Is there a model with a generating `S_φ`?** (§3.)  Yes.  `Gen.cgg` is a third
   `ChainDataGeom` — `ξ = x mod 2`, `Â_∞ = {0 ≤ y ≤ x}`, `v_ℓ = (1,-1)`, `S_φ = {0, (-1,1)}` —
   whose `S_φ` **is** generating (`Gen.isGeneratingSet_Sg`), whose every shell is
   lattice-convex (`Gen.isLatticeConvexRegion_shellInf_cgg`), and on which all eleven conjuncts
   hold at `ε = 0` with a **finite-range** `ξ` (`Gen.window_model_gen`; `P ξ W ≤ 2` is
   `Gen.P_ξg_le_two`, so the deficit conjunct is no longer the `P = 0` degeneracy).  Every
   binder of `exists_case2_window` except the vacuous `hξ` is discharged by a kernel term
   (`isGeneratingSet_Sg`, `hRconv_cgg`, `cgg.ahat_nonempty`, `hshell_zero`, `hshell_not_one`).
4. **At which `ε`?** (§4.)  The *conclusion* holds on `cgg` at **every** `ε`
   (`Gen.window_model_gen_all`, window `{3+ε, 4+ε} × [-ε-1, 1]`, no conjunct breaks), but the
   *binder* `hshell_ε` is unsatisfiable on `cgg` for every `ε ≥ 1`, every `K` and every
   `ϑ ∈ X_ξ` (`Gen.not_hshell_of_pos`): on this bundle the switch layer is `ε = 0` and nothing
   else.  So the `ε`-uniformity is a statement about the conclusion, not about the theorem.
5. **Is the shape-match real?** (§5.)  Yes, now.  `WindowConclusion cg ε` names the eleven-conjunct
   conclusion over an arbitrary bundle, and `target_type_eq : type_of% @exists_case2_window =
   (∀ binders, WindowConclusion cg ε)` is `rfl` with **no hypotheses** — the identification
   between "the shape" and the live `sorry` target no longer hides behind an uninhabited binder.
   `windowConclusion_cgg ε` / `windowConclusion_cgc_one` are §2–§4 restated against that name.
   The three earlier `*_shape_matches_target` theorems (unification checks behind uninhabited
   binders) were **deleted 2026-09-19** once `target_type_eq` subsumed them.
   ⚠ Confidence, not progress: `sorry TOTAL` is unchanged, and the target must hold for every
   minimal-counterexample bundle, not for one model.
6. **The eleventh conjunct** (`hBmax`, added 2026-09-19; §1b).  On every model here `v_J = (1,0)`
   and the window has width 2, so `pw = |face| - 1` is pinned to **`1`**, and
   `B = maxB (derivedQ …) v_J 1 = Q`.  The original `pw = 2`, `B = {one point}` witnesses
   **fail** the eleventh conjunct; the repair `pw := 1`, `B := Q`, `e := false` satisfies all
   eleven on `cgc` at `ε = 1` and on `cgg` at every `ε` (the deficit becomes `P S₁ ≤ P Q + 1`,
   fine since `P ξg W ≤ 2 ≤ P ξg Q + 1` once `Q ≠ ∅`).  `e = true` is the wrong sign: it cuts
   the top row and `hline` would put the face row into `Q`.
7. **What `cgg` carries jointly** (§6).  Against the neighbouring obligations of
   `region_periods_and_rays` and Claim 4.11's producer: `hagree`, `hc_grow`, and the producer's
   `hqgt`/`hrun` on the model window all **hold**; `hc_env` (`Env = EnvOf S`), Cconv's
   `prev_mem`, and — found by `omega`, not by reading — **`hp_per` for every transverse `p`**
   all **fail** (`x_per` has only horizontal periods, `per_xperg_snd_eq_zero`).  So `cgg` is a
   model of the leaf and of the chain-growth binders, not of the caller's period structure;
   in particular §1's `0 < pw` forcing does not apply to it.
8. **`exists_case2_run` on `cgg`** (§7; the target was wired 2026-09-19 ~10:50 and this run
   statement is what remained — but it is **already closed** by `C11Bridge.exists_run`, kernel-clean,
   so nothing here can refute it).  Its conclusion **holds** on `Sgen := S_φ` (vacuously, run length
   `0`) and on `Sgen := S₁g` (run length `1`); the "`|face| ≤ 1` ⟹ trivial" claim is proved for any
   `Sgen` with a second point (`run_trivial_of_face_card_le_one`), with the flat case as the
   boundary (`not_run_of_flat`).  And `cgg` is **not an instance** the statement is about: `hdet_vl`
   fails (`det p v_ℓ = -2`) and `ξ = x mod 2` has no one-sided nonexpansive direction at all
   (`not_isOneSidedNonexpansive_ξg`, `not_mem_nonExpansiveLine_ξg`), so `hℓ_nel/hℓ_pos/hℓ_neg` all
   fail for every `ℓ`.  §1 is also restated against the weak `hbase`
   (`pos_pw_of_conclusion_weak`, `window_height_weak`).
-/

set_option autoImplicit false

namespace Nivat.Case2WindowProbe

open Nivat Nivat.LE2 Nivat.MaxEnv Nivat.Colle Nivat.Colle35 Nivat.ColleReg

variable {ξ xper ϑ : Config ℤ} {vl p : ℤ × ℤ} {S : Finset (ℤ × ℤ)} {gen : ℤ × ℤ}

/-! ## §0 The existing witnesses do not satisfy `hSφ` -/

/-- `{0}` is not a generating set for `etaC`: `etaC` and `T (1,0) etaC` are both in the orbit
closure, agree on `{0}.erase 0 = ∅`, and differ at `0`.  Both `cgc` and `cgn` have
`S = Nivat.ColleStep.PeriodsRays2.Sw = {0}`, so neither satisfies `exists_case2_window`'s
binder `hSφ`. -/
theorem not_isGeneratingSet_etaC_Sw :
    ¬ IsGeneratingSet Nivat.ColleStep.PeriodsRays2.etaC Nivat.ColleStep.PeriodsRays2.Sw := by
  rintro ⟨-, -, h⟩
  have h0 : (0 : ℤ × ℤ) ∈ Nivat.ColleStep.PeriodsRays2.Sw := by
    simp [Nivat.ColleStep.PeriodsRays2.Sw]
  have hconv : LatticeConvex (Nivat.ColleStep.PeriodsRays2.Sw.erase 0) := by
    intro z hz
    have he : Nivat.ColleStep.PeriodsRays2.Sw.erase (0 : ℤ × ℤ) = ∅ := by
      simp [Nivat.ColleStep.PeriodsRays2.Sw]
    rw [he] at hz
    simp [Conv] at hz
  obtain ⟨-, hgen⟩ := h 0 h0 hconv
  have := hgen _ (self_mem_orbitClosure _) _
    (T_mem_orbitClosure Nivat.ColleStep.PeriodsRays2.etaC ((1 : ℤ), (0 : ℤ)))
    (by intro z hz; simp [Nivat.ColleStep.PeriodsRays2.Sw] at hz)
  simp [Nivat.ColleStep.PeriodsRays2.etaC, T] at this

/-! ## §1 What the conjuncts force, over an arbitrary bundle -/

/-- `⟪n_J, t • v_J + g⟫ = ⟪n_J, g⟫`: sliding along `v_J` does not change the layer. -/
theorem dot_nJ_smul_vJ_add (cg : ChainDataGeom ξ xper vl p S gen) (t : ℤ) (g : ℤ × ℤ) :
    dot cg.nJ (t • cg.vJ + g) = dot cg.nJ g := by
  have h := cg.dot_nJ_vJ
  simp only [dot, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h ⊢
  linear_combination t * h

/-- Every point of `Â_∞^{(ε)}` is at level `≥ c_J - ε`. -/
theorem level_of_mem_shellInf (cg : ChainDataGeom ξ xper vl p S gen) {ε : ℕ} {z : ℤ × ℤ}
    (hz : z ∈ cg.toChainData.shellInf ε) : cg.cJ - (ε : ℤ) ≤ dot cg.nJ z := by
  rw [cg.shellInf_eq] at hz
  obtain ⟨-, -, -, -, hd⟩ := hz
  exact hd

/-- A point of layer `ε + 1` that is not in layer `ε` sits at level **exactly** `c_J - ε - 1`:
the sweep witness `(g, t)` is the same for both layers, so only the level test can fail. -/
theorem level_of_mem_succ_not_mem (cg : ChainDataGeom ξ xper vl p S gen) {ε : ℕ} {z : ℤ × ℤ}
    (h1 : z ∈ cg.toChainData.shellInf (ε + 1)) (h2 : z ∉ cg.toChainData.shellInf ε) :
    dot cg.nJ z = cg.cJ - (ε : ℤ) - 1 := by
  rw [cg.shellInf_eq] at h1 h2
  obtain ⟨g, hg, t, hzt, hd⟩ := h1
  have hlt : dot cg.nJ z < cg.cJ - (ε : ℤ) := by
    by_contra hge
    exact h2 ⟨g, hg, t, hzt, not_lt.mp hge⟩
  push_cast at hd
  omega

/-- **The face is pinned to level `c_J - ε - 1`.**  From `hface` alone (at `t = τ`). -/
theorem face_level (cg : ChainDataGeom ξ xper vl p S gen) {ε : ℕ}
    {S₁ Q : Finset (ℤ × ℤ)} {τ : ℤ}
    (hface : ∀ g ∈ S₁, g ∉ Q → ∀ t : ℤ, τ ≤ t →
      t • cg.vJ + g ∈ cg.toChainData.shellInf (ε + 1) ∧
      t • cg.vJ + g ∉ cg.toChainData.shellInf ε)
    {g : ℤ × ℤ} (hg : g ∈ S₁) (hgQ : g ∉ Q) :
    dot cg.nJ g = cg.cJ - (ε : ℤ) - 1 := by
  obtain ⟨h1, h2⟩ := hface g hg hgQ τ le_rfl
  have := level_of_mem_succ_not_mem cg h1 h2
  rwa [dot_nJ_smul_vJ_add] at this

/-- **`Q` is pinned to levels `≥ c_J - ε`.**  From `hQR` and `R ⊆ Â_∞^{(ε)}`. -/
theorem Q_level (cg : ChainDataGeom ξ xper vl p S gen) {ε : ℕ}
    {Q : Finset (ℤ × ℤ)} {τ : ℤ} {R : Set (ℤ × ℤ)}
    (hRsub : R ⊆ cg.toChainData.shellInf ε)
    (hQR : ∀ t : ℤ, τ ≤ t → ∀ z ∈ Q,
      t • cg.vJ + z ∈ R ∧ t • cg.vJ + z + (1 : ℤ) • p ∈ R)
    {z : ℤ × ℤ} (hz : z ∈ Q) : cg.cJ - (ε : ℤ) ≤ dot cg.nJ z := by
  have := level_of_mem_shellInf cg (hRsub (hQR τ le_rfl z hz).1)
  rwa [dot_nJ_smul_vJ_add] at this

/-- **Once `0 < pw`, `B ⊆ Q`**: `hline` at `i = 0`. -/
theorem B_subset_Q_of_pos {vJ : ℤ × ℤ} {B Q : Finset (ℤ × ℤ)} {pw : ℕ} (hpw : 0 < pw)
    (hline : ∀ g ∈ B, ∀ i : ℕ, i < pw → g + (i : ℤ) • vJ ∈ Q) : B ⊆ Q := by
  intro g hg
  simpa using hline g hg 0 hpw

/-- **The `hbase` witness sits at level `≥ 1`.**  `b + g ∈ R ⊆ Â_∞^{(ε)}` for a face point `g`
(level `c_J - ε - 1`) forces `⟪n_J, b⟫ + c_J - ε - 1 ≥ c_J - ε`. -/
theorem base_level (cg : ChainDataGeom ξ xper vl p S gen) {ε : ℕ}
    {S₁ Q : Finset (ℤ × ℤ)} {τ : ℤ} {R : Set (ℤ × ℤ)}
    (hRsub : R ⊆ cg.toChainData.shellInf ε)
    (hface : ∀ g ∈ S₁, g ∉ Q → ∀ t : ℤ, τ ≤ t →
      t • cg.vJ + g ∈ cg.toChainData.shellInf (ε + 1) ∧
      t • cg.vJ + g ∉ cg.toChainData.shellInf ε)
    {g : ℤ × ℤ} (hg : g ∈ S₁) (hgQ : g ∉ Q)
    {b : ℤ × ℤ} (hb : ∀ z ∈ S₁, b + z ∈ R) : 1 ≤ dot cg.nJ b := by
  have h1 := level_of_mem_shellInf cg (hRsub (hb g hg))
  have h2 := face_level cg hface hg hgQ
  rw [dot_add, h2] at h1
  omega

/-- The edge conjunct makes the face nonempty as a subset of `S₁ \ Q`. -/
theorem exists_face_point {S₁ Q : Finset (ℤ × ℤ)} {vJ : ℤ × ℤ}
    (hQ_edge : ∃ (n : ℝ × ℝ) (cmax : ℝ),
      n ≠ 0 ∧ inner2 n vJ = 0 ∧ (∀ z ∈ S₁, inner2 n z ≤ cmax) ∧
      (Nivat.R2.face S₁ n cmax).Nonempty ∧ Q = S₁.filter fun z => inner2 n z < cmax) :
    ∃ g ∈ S₁, g ∉ Q := by
  obtain ⟨n, cmax, -, -, -, ⟨g, hg⟩, hQ⟩ := hQ_edge
  rw [Nivat.R2.mem_face] at hg
  refine ⟨g, hg.1, ?_⟩
  rw [hQ, Finset.mem_filter, hg.2]
  exact fun h => lt_irrefl _ h.2

/-- **The height constraint.**  Under the edge conjunct, `hface`, `hline` with `0 < pw`,
`R ⊆ Â_∞^{(ε)}` and `hbase`, the window `S₁` has a point at level `c_J - ε - 1` and a point of
`Q` at level `≥ 1`.  Its `n_J`-height is therefore at least `ε + 2 - c_J` — an
**absolute-position** requirement that a translate of a fixed generating set can meet only if
the set is tall enough relative to where `Â_∞` sits.

⚠ **Retired shape (2026-09-19), kept per `PROTOCOL.md` §14.**  The `hbase` binder below is the
strong conjunct 9 that the live target no longer has; this theorem is true but does **not** apply
to `exists_case2_window` as stated.  The surviving statement is `window_height_weak` (§1 restated),
and the absolute-height bound is exactly the part that does **not** survive. -/
theorem window_height (cg : ChainDataGeom ξ xper vl p S gen) {ε : ℕ}
    {S₁ Q B : Finset (ℤ × ℤ)} {τ : ℤ} {pw : ℕ} {R : Set (ℤ × ℤ)}
    (hQ_edge : ∃ (n : ℝ × ℝ) (cmax : ℝ),
      n ≠ 0 ∧ inner2 n cg.vJ = 0 ∧ (∀ z ∈ S₁, inner2 n z ≤ cmax) ∧
      (Nivat.R2.face S₁ n cmax).Nonempty ∧ Q = S₁.filter fun z => inner2 n z < cmax)
    (hface : ∀ g ∈ S₁, g ∉ Q → ∀ t : ℤ, τ ≤ t →
      t • cg.vJ + g ∈ cg.toChainData.shellInf (ε + 1) ∧
      t • cg.vJ + g ∉ cg.toChainData.shellInf ε)
    (hpw : 0 < pw)
    (hline : ∀ g ∈ B, ∀ i : ℕ, i < pw → g + (i : ℤ) • cg.vJ ∈ Q)
    (hRsub : R ⊆ cg.toChainData.shellInf ε)
    (hbase : ∃ b ∈ B, ∀ z ∈ S₁, b + z ∈ R) :
    (∃ g ∈ S₁, dot cg.nJ g = cg.cJ - (ε : ℤ) - 1) ∧ ∃ b ∈ Q, 1 ≤ dot cg.nJ b := by
  obtain ⟨g, hg, hgQ⟩ := exists_face_point hQ_edge
  obtain ⟨b, hbB, hb⟩ := hbase
  exact ⟨⟨g, hg, face_level cg hface hg hgQ⟩,
    ⟨b, B_subset_Q_of_pos hpw hline hbB, base_level cg hRsub hface hg hgQ hb⟩⟩

/-- **`pw` is bounded by `|Q|`** once `B` is nonempty: `hline` embeds `{0, …, pw-1}` into `Q`
along the primitive (hence nonzero) `v_J`. -/
theorem pw_le_card_Q {vJ : ℤ × ℤ} (hvJ : vJ ≠ 0) {B Q : Finset (ℤ × ℤ)} {pw : ℕ}
    (hline : ∀ g ∈ B, ∀ i : ℕ, i < pw → g + (i : ℤ) • vJ ∈ Q) (hB : B.Nonempty) :
    pw ≤ Q.card := by
  obtain ⟨g, hg⟩ := hB
  have h := Finset.card_le_card_of_injOn (fun i : ℕ => g + (i : ℤ) • vJ)
    (s := Finset.range pw) (t := Q)
    (fun i hi => hline g hg i (Finset.mem_range.mp hi))
    (by
      intro i _ j _ hij
      have h' : ((i : ℤ) - j) • vJ = 0 := by
        rw [sub_smul, sub_eq_zero]
        exact add_left_cancel hij
      rcases smul_eq_zero.mp h' with h0 | h0
      · exact_mod_cast sub_eq_zero.mp h0
      · exact absurd h0 hvJ)
  simpa using h

/-- **The `pw` coupling, made precise.**  `hdef` pushes `pw` up to `P ξ S₁ - P ξ Q`; `hline`
with `B ≠ ∅` caps it at `|Q|`.  Jointly they say `P ξ S₁ ≤ P ξ Q + |Q|` — a constraint on `ξ`
and the window, not a contradiction (the model in §2 has `P = 0`). -/
theorem P_le_of_conclusion {ξ : Config ℤ} {vJ : ℤ × ℤ} (hvJ : vJ ≠ 0)
    {S₁ Q B : Finset (ℤ × ℤ)} {pw : ℕ}
    (hdef : P ξ S₁ ≤ P ξ Q + pw)
    (hline : ∀ g ∈ B, ∀ i : ℕ, i < pw → g + (i : ℤ) • vJ ∈ Q) (hB : B.Nonempty) :
    P ξ S₁ ≤ P ξ Q + Q.card :=
  hdef.trans (Nat.add_le_add_left (pw_le_card_Q hvJ hline hB) _)

/-- **`0 < pw` is forced by the conclusion** in the context of `region_periods_and_rays`
(which additionally has `hp_per` and `hξ.1.1 : (Set.range ξ).Finite`): Claim 4.11 gives
semi-ambiguity, `hbase` gives `B.Nonempty`, and `pos_pw_of_case1_hyps` does the rest.  So the
height constraint of `window_height` is not optional there.

⚠ **Retired shape (2026-09-19), kept per `PROTOCOL.md` §14.**  Same reason as `window_height`:
the `hbase` binder is the strong conjunct 9.  Here the content **does** survive verbatim — see
`pos_pw_of_conclusion_weak`, whose proof is this one with `⟨b, hb⟩` read off `B.Nonempty`. -/
theorem pos_pw_of_conclusion (cg : ChainDataGeom ξ xper vl p S gen)
    (hfin : (Set.range ξ).Finite)
    (hSφ : IsGeneratingSet ξ S) (hϑ_mem : ϑ ∈ orbitClosure ξ) (hp_per : p ∈ Per xper)
    {K ε : ℕ}
    (hshell_ε : ∀ z ∈ cg.toChainData.shellInf ε, ϑ z = T ((K : ℤ) • vl) xper z)
    (hshell_not_εp1 :
      ¬ (∀ z ∈ cg.toChainData.shellInf (ε + 1), ϑ z = T ((K : ℤ) • vl) xper z))
    {S₁ Q B : Finset (ℤ × ℤ)} {τ : ℤ} {pw : ℕ} {R : Set (ℤ × ℤ)}
    (hS₁ : IsGeneratingSet ξ S₁) (hQS : Q ⊆ S₁)
    (hQ_edge : ∃ (n : ℝ × ℝ) (cmax : ℝ),
      n ≠ 0 ∧ inner2 n cg.vJ = 0 ∧ (∀ z ∈ S₁, inner2 n z ≤ cmax) ∧
      (Nivat.R2.face S₁ n cmax).Nonempty ∧ Q = S₁.filter fun z => inner2 n z < cmax)
    (hface : ∀ g ∈ S₁, g ∉ Q → ∀ t : ℤ, τ ≤ t →
      t • cg.vJ + g ∈ cg.toChainData.shellInf (ε + 1) ∧
      t • cg.vJ + g ∉ cg.toChainData.shellInf ε)
    (hdef : P ξ S₁ ≤ P ξ Q + pw)
    (hline : ∀ g ∈ B, ∀ i : ℕ, i < pw → g + (i : ℤ) • cg.vJ ∈ Q)
    (hRsub : R ⊆ cg.toChainData.shellInf ε)
    (hQR_R : ∀ t : ℤ, τ ≤ t → ∀ z ∈ Q,
      t • cg.vJ + z ∈ R ∧ t • cg.vJ + z + (1 : ℤ) • p ∈ R)
    (hbase : ∃ b ∈ B, ∀ z ∈ S₁, b + z ∈ R) : 0 < pw := by
  have hQR : ∀ t : ℤ, τ ≤ t → ∀ z ∈ Q, t • cg.vJ + z ∈ cg.toChainData.shellInf ε :=
    fun t ht z hz => hRsub (hQR_R t ht z hz).1
  have hamb := Claim411.claim411_semiAmbiguous cg hSφ hϑ_mem hp_per hshell_ε hshell_not_εp1
    hS₁ hQS hQ_edge hQR hface
  obtain ⟨b, hb, -⟩ := hbase
  exact pos_pw_of_case1_hyps hfin hϑ_mem hQS hdef hline ⟨b, hb⟩ hamb

/-! ### §1 restated against the weak `hbase` (2026-09-19)

Conjunct 9 of the target was weakened on 2026-09-19 from `∃ b ∈ B, ∀ z ∈ S₁, b + z ∈ R` to
`B.Nonempty ∧ ∃ b, ∀ z ∈ S₁, b + z ∈ R`.  `pos_pw_of_conclusion` and `window_height` above are
still true theorems, but their `hbase` binder is the **retired** strong form, so they no longer
apply to the live conclusion as stated.  The two restatements below are what survives:

* `pos_pw_of_conclusion_weak` — unchanged in content; the proof only ever used `B.Nonempty`.
* `window_height_weak` — the face point at level `c_J - ε - 1` and the base point at level `≥ 1`
  both survive, but the base point is now **not** a point of `Q ⊆ S₁`, so the absolute-height
  bound on the window (`ε + 2 - c_J`) that `window_height` extracted is **gone**.  That bound is
  exactly what Cclaim showed Lemma 2.4 cannot pay, and its disappearance is the reason for the
  weakening; the restatement records that the probe agrees. -/

/-- **`0 < pw` is still forced** under the weak `hbase`: only `B.Nonempty` was ever used. -/
theorem pos_pw_of_conclusion_weak (cg : ChainDataGeom ξ xper vl p S gen)
    (hfin : (Set.range ξ).Finite)
    (hSφ : IsGeneratingSet ξ S) (hϑ_mem : ϑ ∈ orbitClosure ξ) (hp_per : p ∈ Per xper)
    {K ε : ℕ}
    (hshell_ε : ∀ z ∈ cg.toChainData.shellInf ε, ϑ z = T ((K : ℤ) • vl) xper z)
    (hshell_not_εp1 :
      ¬ (∀ z ∈ cg.toChainData.shellInf (ε + 1), ϑ z = T ((K : ℤ) • vl) xper z))
    {S₁ Q B : Finset (ℤ × ℤ)} {τ : ℤ} {pw : ℕ} {R : Set (ℤ × ℤ)}
    (hS₁ : IsGeneratingSet ξ S₁) (hQS : Q ⊆ S₁)
    (hQ_edge : ∃ (n : ℝ × ℝ) (cmax : ℝ),
      n ≠ 0 ∧ inner2 n cg.vJ = 0 ∧ (∀ z ∈ S₁, inner2 n z ≤ cmax) ∧
      (Nivat.R2.face S₁ n cmax).Nonempty ∧ Q = S₁.filter fun z => inner2 n z < cmax)
    (hface : ∀ g ∈ S₁, g ∉ Q → ∀ t : ℤ, τ ≤ t →
      t • cg.vJ + g ∈ cg.toChainData.shellInf (ε + 1) ∧
      t • cg.vJ + g ∉ cg.toChainData.shellInf ε)
    (hdef : P ξ S₁ ≤ P ξ Q + pw)
    (hline : ∀ g ∈ B, ∀ i : ℕ, i < pw → g + (i : ℤ) • cg.vJ ∈ Q)
    (hRsub : R ⊆ cg.toChainData.shellInf ε)
    (hQR_R : ∀ t : ℤ, τ ≤ t → ∀ z ∈ Q,
      t • cg.vJ + z ∈ R ∧ t • cg.vJ + z + (1 : ℤ) • p ∈ R)
    (hbase : B.Nonempty ∧ ∃ b, ∀ z ∈ S₁, b + z ∈ R) : 0 < pw := by
  have hQR : ∀ t : ℤ, τ ≤ t → ∀ z ∈ Q, t • cg.vJ + z ∈ cg.toChainData.shellInf ε :=
    fun t ht z hz => hRsub (hQR_R t ht z hz).1
  have hamb := Claim411.claim411_semiAmbiguous cg hSφ hϑ_mem hp_per hshell_ε hshell_not_εp1
    hS₁ hQS hQ_edge hQR hface
  exact pos_pw_of_case1_hyps hfin hϑ_mem hQS hdef hline hbase.1 hamb

/-- **What is left of the height constraint** under the weak `hbase`: a face point of `S₁` at
level `c_J - ε - 1`, and a base point at level `≥ 1` — which is **no longer a point of `S₁`**, so
no lower bound on the height of `S₁` follows.  (Compare `window_height`, whose second half put the
base point in `Q`.) -/
theorem window_height_weak (cg : ChainDataGeom ξ xper vl p S gen) {ε : ℕ}
    {S₁ Q : Finset (ℤ × ℤ)} {τ : ℤ} {R : Set (ℤ × ℤ)}
    (hQ_edge : ∃ (n : ℝ × ℝ) (cmax : ℝ),
      n ≠ 0 ∧ inner2 n cg.vJ = 0 ∧ (∀ z ∈ S₁, inner2 n z ≤ cmax) ∧
      (Nivat.R2.face S₁ n cmax).Nonempty ∧ Q = S₁.filter fun z => inner2 n z < cmax)
    (hface : ∀ g ∈ S₁, g ∉ Q → ∀ t : ℤ, τ ≤ t →
      t • cg.vJ + g ∈ cg.toChainData.shellInf (ε + 1) ∧
      t • cg.vJ + g ∉ cg.toChainData.shellInf ε)
    (hRsub : R ⊆ cg.toChainData.shellInf ε)
    (hbase : ∃ b, ∀ z ∈ S₁, b + z ∈ R) :
    (∃ g ∈ S₁, dot cg.nJ g = cg.cJ - (ε : ℤ) - 1) ∧
      ∃ b, 1 ≤ dot cg.nJ b ∧ ∀ z ∈ S₁, b + z ∈ R := by
  obtain ⟨g, hg, hgQ⟩ := exists_face_point hQ_edge
  obtain ⟨b, hb⟩ := hbase
  exact ⟨⟨g, hg, face_level cg hface hg hgQ⟩, ⟨b, base_level cg hRsub hface hg hgQ hb, hb⟩⟩

/-! ## §1b The eleventh conjunct: `derivedQ` / `topFace` / `maxB` on box windows

`exists_case2_window` gained an eleventh conjunct on 2026-09-19 (`case1_sweep`'s `hBmax`):
`∃ e : Bool, pw = (topFace e v_J S₁).card - 1 ∧ B = maxB (derivedQ e v_J S₁) v_J pw`.
`derivedQ`, `topFace`, `maxB` (`L1Cut.lean`) are noncomputable (real `inner2`, classical
filters), so nothing about them is `decide`-able; these lemmas turn them into integer
conditions.  On a box `[a,b] × [c,d]` with `v_J = (1,0)` and `e = false` the cut normal is
`(0,-1)`, the "top" face is the **bottom row** `[a,b] × {c}`, `derivedQ` is the box minus that
row, and `maxB Q v_J 1 = Q`.  So on a width-2 window the conjunct **pins `pw = 1`** — which is
why the `pw = 2`, `B = {one point}` witnesses of the original ten-conjunct models had to be
re-chosen (see §2–§4). -/

section EleventhConjunct

open Nivat.ColleReg.L1Data

/-- The integer vector behind `cutNormal`. -/
def wcut (e : Bool) (u' : ℤ × ℤ) : ℤ × ℤ := if e then perp u' else -perp u'

theorem cutNormal_eq (e : Bool) (u' : ℤ × ℤ) : cutNormal e u' = toReal (wcut e u') := rfl

theorem mem_derivedQ_iff {e : Bool} {u' : ℤ × ℤ} {S₁ : Finset (ℤ × ℤ)} {z : ℤ × ℤ} :
    z ∈ derivedQ e u' S₁ ↔
      z ∈ S₁ ∧ ∃ y ∈ S₁, dot (wcut e u') z < dot (wcut e u') y := by
  unfold derivedQ
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨hz, hlt⟩
    refine ⟨hz, ?_⟩
    unfold levelMax at hlt
    rw [dif_pos ⟨z, hz⟩] at hlt
    obtain ⟨y, hy, hy'⟩ := Finset.exists_mem_eq_sup' ⟨z, hz⟩ (fun z => inner2 (cutNormal e u') z)
    rw [hy'] at hlt
    refine ⟨y, hy, ?_⟩
    rw [cutNormal_eq, inner2_toReal, inner2_toReal] at hlt
    exact_mod_cast hlt
  · rintro ⟨hz, y, hy, hlt⟩
    refine ⟨hz, ?_⟩
    unfold levelMax
    rw [dif_pos ⟨z, hz⟩]
    have h1 : inner2 (cutNormal e u') y ≤ S₁.sup' ⟨z, hz⟩ (fun z => inner2 (cutNormal e u') z) :=
      Finset.le_sup' (fun z => inner2 (cutNormal e u') z) hy
    have h2 : inner2 (cutNormal e u') z < inner2 (cutNormal e u') y := by
      rw [cutNormal_eq, inner2_toReal, inner2_toReal]
      exact_mod_cast hlt
    exact lt_of_lt_of_le h2 h1

theorem mem_topFace_iff {e : Bool} {u' : ℤ × ℤ} {S₁ : Finset (ℤ × ℤ)} {z : ℤ × ℤ} :
    z ∈ topFace e u' S₁ ↔
      z ∈ S₁ ∧ ∀ y ∈ S₁, dot (wcut e u') y ≤ dot (wcut e u') z := by
  unfold topFace
  rw [Nivat.R2.mem_face]
  constructor
  · rintro ⟨hz, heq⟩
    refine ⟨hz, fun y hy => ?_⟩
    have h := le_levelMax (n := cutNormal e u') ⟨z, hz⟩ y hy
    rw [← heq, cutNormal_eq, inner2_toReal, inner2_toReal] at h
    exact_mod_cast h
  · rintro ⟨hz, hle⟩
    refine ⟨hz, le_antisymm (le_levelMax ⟨z, hz⟩ z hz) ?_⟩
    unfold levelMax
    rw [dif_pos ⟨z, hz⟩]
    apply Finset.sup'_le
    intro y hy
    rw [cutNormal_eq, inner2_toReal, inner2_toReal]
    exact_mod_cast hle y hy

/-- `e = false`, `u' = (1,0)`: the cut vector is `(0,-1)`. -/
theorem dot_wcut_false_e1 (z : ℤ × ℤ) : dot (wcut false ((1 : ℤ), (0 : ℤ))) z = -z.2 := by
  simp [wcut, perp, dot]

/-- On a box `[a,b] × [c,d]`, the `e = false` face along `(1,0)` is the bottom row. -/
theorem topFace_false_box {S₁ : Finset (ℤ × ℤ)} {a b c d : ℤ}
    (hS : ∀ z, z ∈ S₁ ↔ (a ≤ z.1 ∧ z.1 ≤ b) ∧ (c ≤ z.2 ∧ z.2 ≤ d)) (hab : a ≤ b) (hcd : c ≤ d) :
    topFace false ((1 : ℤ), (0 : ℤ)) S₁ = Finset.Icc a b ×ˢ {c} := by
  ext z
  rw [mem_topFace_iff, Finset.mem_product, Finset.mem_Icc, Finset.mem_singleton, hS]
  simp only [dot_wcut_false_e1]
  constructor
  · rintro ⟨⟨h1, h2⟩, hmin⟩
    have := hmin (a, c) ((hS _).mpr ⟨⟨le_rfl, hab⟩, le_rfl, hcd⟩)
    simp only at this
    exact ⟨h1, by omega⟩
  · rintro ⟨h1, h2⟩
    refine ⟨⟨h1, by omega⟩, ?_⟩
    intro y hy
    rw [hS] at hy
    omega

theorem card_topFace_false_box {S₁ : Finset (ℤ × ℤ)} {a b c d : ℤ}
    (hS : ∀ z, z ∈ S₁ ↔ (a ≤ z.1 ∧ z.1 ≤ b) ∧ (c ≤ z.2 ∧ z.2 ≤ d)) (hab : a ≤ b) (hcd : c ≤ d) :
    (topFace false ((1 : ℤ), (0 : ℤ)) S₁).card = (b + 1 - a).toNat := by
  rw [topFace_false_box hS hab hcd, Finset.card_product, Finset.card_singleton, Int.card_Icc,
    mul_one]

/-- On a box, `derivedQ` with `e = false` along `(1,0)` is the box minus its bottom row. -/
theorem derivedQ_false_box {S₁ : Finset (ℤ × ℤ)} {a b c d : ℤ}
    (hS : ∀ z, z ∈ S₁ ↔ (a ≤ z.1 ∧ z.1 ≤ b) ∧ (c ≤ z.2 ∧ z.2 ≤ d)) (hab : a ≤ b) (hcd : c ≤ d) :
    derivedQ false ((1 : ℤ), (0 : ℤ)) S₁ = S₁.filter (fun z => c < z.2) := by
  ext z
  rw [mem_derivedQ_iff, Finset.mem_filter]
  simp only [dot_wcut_false_e1]
  constructor
  · rintro ⟨hz, y, hy, hlt⟩
    rw [hS] at hy
    exact ⟨hz, by omega⟩
  · rintro ⟨hz, hlt⟩
    exact ⟨hz, (a, c), (hS _).mpr ⟨⟨le_rfl, hab⟩, le_rfl, hcd⟩, by simp only; omega⟩

/-- `maxB Q u' 1 = Q`: a run of length one is a point. -/
theorem maxB_one (Q : Finset (ℤ × ℤ)) (u' : ℤ × ℤ) : maxB Q u' 1 = Q := by
  ext g
  rw [mem_maxB]
  constructor
  · exact fun h => h.1
  · intro hg
    refine ⟨hg, fun i hi => ?_⟩
    have : i = 0 := by omega
    subst this
    simpa using hg

end EleventhConjunct

/-! ## §2 A model of all eleven conjuncts on `cgc` at `ε = 1`

`cgc` (`ShellConvex.lean`): `Â_∞ = {0 ≤ y, 2y ≤ x}`, `n_J = (0,1)`, `c_J = 0`, `v_J = (1,0)`,
`p = (2,1)`, sweep direction `(1,-2)`.  Then `Â_∞^{(1)} = Â_∞ ∪ {y = -1, x ≥ 3}` — which **is**
lattice-convex (rows start at `3, 0, 2, 4, …`), unlike `Â_∞^{(2)}` — and
`Â_∞^{(2)} ⊇ {y = -2, x ≥ 1}`.  The face must sit at level `c_J - ε - 1 = -2`, `Q` at
levels `≥ -1`, and the `hbase` witness at level `≥ 1` (§1), so the window needs rows
`-2, -1, 0, 1`: take `S₁ = {2,3} × {-2,…,1}`. -/

namespace Model

open Nivat.ShellConvex Nivat.ColleStep.PeriodsRays2

/-- `𝒯 = {2,3} × {-2,-1,0,1}`. -/
def S₁w : Finset (ℤ × ℤ) := ({2, 3} : Finset ℤ) ×ˢ ({-2, -1, 0, 1} : Finset ℤ)
/-- `𝒯 ∖ ℓ'_𝒯 = {2,3} × {-1,0,1}`. -/
def Qw : Finset (ℤ × ℤ) := ({2, 3} : Finset ℤ) ×ˢ ({-1, 0, 1} : Finset ℤ)
/-- The seed of the **retired** ten-conjunct model: one base point, whose forward `v_J`-run of
length `pw = 2` is `(2,1), (3,1) ⊆ Q`.  Kept for the record; `window_model` now uses `B := Qw`,
`pw := 1`, because the eleventh conjunct pins both (§1b). -/
def Bw : Finset (ℤ × ℤ) := {((2 : ℤ), (1 : ℤ))}
/-- `ϑ = T (0,1) etaC`: agrees with `x_per` on `{y ≥ -1}`, not on `{y ≥ -2}`. -/
def ϑw : Config ℤ := T ((0 : ℤ), (1 : ℤ)) etaC

theorem mem_S₁w {z : ℤ × ℤ} : z ∈ S₁w ↔ (2 ≤ z.1 ∧ z.1 ≤ 3) ∧ (-2 ≤ z.2 ∧ z.2 ≤ 1) := by
  simp only [S₁w, Finset.mem_product, Finset.mem_insert, Finset.mem_singleton]
  omega

theorem mem_Qw {z : ℤ × ℤ} : z ∈ Qw ↔ (2 ≤ z.1 ∧ z.1 ≤ 3) ∧ (-1 ≤ z.2 ∧ z.2 ≤ 1) := by
  simp only [Qw, Finset.mem_product, Finset.mem_insert, Finset.mem_singleton]
  omega

theorem cgc_vJ : cgc.vJ = ((1 : ℤ), (0 : ℤ)) := rfl

/-- Sliding along `v_J = (1,0)`, coordinatewise. -/
theorem smul_vJ_add (t : ℤ) (g : ℤ × ℤ) : t • cgc.vJ + g = (t + g.1, g.2) := by
  rw [cgc_vJ]; ext <;> simp

/-- `Â_∞^{(1)}` of `cgc`, solved for the sweep parameter. -/
theorem mem_shellInf_one {z : ℤ × ℤ} :
    z ∈ cgc.toChainData.shellInf 1 ↔ -1 ≤ z.2 ∧ 2 * z.2 ≤ z.1 ∧ -3 * z.2 ≤ z.1 := by
  show z ∈ ShInfc 1 ↔ _
  rw [mem_ShInfc]
  constructor
  · rintro ⟨t, h1, h2, h3⟩
    push_cast at h3
    omega
  · rintro ⟨h1, h2, h3⟩
    rcases le_or_gt 0 z.2 with h | h
    · exact ⟨0, by omega, by omega, by push_cast; omega⟩
    · exact ⟨1, by omega, by omega, by push_cast; omega⟩

/-- `Â_∞^{(1)}` of `cgc` **is** lattice-convex: it is `{-1 ≤ y, 2y ≤ x, -3y ≤ x} ∩ ℤ²`. -/
theorem isLatticeConvexRegion_shellInf_one :
    IsLatticeConvexRegion (cgc.toChainData.shellInf 1) := by
  refine ⟨{q : ℝ × ℝ | -1 ≤ q.2 ∧ 2 * q.2 ≤ q.1 ∧ -3 * q.2 ≤ q.1}, ?_, ?_, ?_⟩
  · intro u hu v hv a b ha hb hab
    obtain ⟨hu1, hu2, hu3⟩ := hu
    obtain ⟨hv1, hv2, hv3⟩ := hv
    simp only [Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul]
    have e1 := mul_le_mul_of_nonneg_left hu1 ha
    have e2 := mul_le_mul_of_nonneg_left hv1 hb
    have e3 := mul_le_mul_of_nonneg_left hu2 ha
    have e4 := mul_le_mul_of_nonneg_left hv2 hb
    have e5 := mul_le_mul_of_nonneg_left hu3 ha
    have e6 := mul_le_mul_of_nonneg_left hv3 hb
    refine ⟨?_, ?_, ?_⟩ <;> nlinarith
  · have he : {q : ℝ × ℝ | -1 ≤ q.2 ∧ 2 * q.2 ≤ q.1 ∧ -3 * q.2 ≤ q.1}
        = {q : ℝ × ℝ | -1 ≤ q.2} ∩ ({q : ℝ × ℝ | 2 * q.2 ≤ q.1} ∩ {q : ℝ × ℝ | -3 * q.2 ≤ q.1}) :=
      rfl
    rw [he]
    exact (isClosed_le continuous_const continuous_snd).inter
      ((isClosed_le (continuous_const.mul continuous_snd) continuous_fst).inter
        (isClosed_le (continuous_const.mul continuous_snd) continuous_fst))
  · ext z
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, toReal, mem_shellInf_one]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨by exact_mod_cast h1, by exact_mod_cast h2, by exact_mod_cast h3⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨by exact_mod_cast h1, by exact_mod_cast h2, by exact_mod_cast h3⟩

theorem isRegion_shellInf_one : Colle41.IsRegion (cgc.toChainData.shellInf 1) p2 cgc.vJ :=
  (cgc.isRegion_shellInf_iff 1).mpr isLatticeConvexRegion_shellInf_one

/-- The real box `[2,3] × [-2,1]` is convex. -/
theorem convex_box :
    Convex ℝ {q : ℝ × ℝ | 2 ≤ q.1 ∧ q.1 ≤ 3 ∧ -2 ≤ q.2 ∧ q.2 ≤ 1} := by
  intro u hu v hv a b ha hb hab
  obtain ⟨hu1, hu2, hu3, hu4⟩ := hu
  obtain ⟨hv1, hv2, hv3, hv4⟩ := hv
  simp only [Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith

/-- `Conv 𝒯 ⊆ [2,3] × [-2,1]`, hence lattice convexity. -/
theorem latticeConvex_S₁w : LatticeConvex S₁w := by
  intro z hz
  have hsub : Conv S₁w ⊆ {q : ℝ × ℝ | 2 ≤ q.1 ∧ q.1 ≤ 3 ∧ -2 ≤ q.2 ∧ q.2 ≤ 1} := by
    apply convexHull_min _ convex_box
    rintro _ ⟨w, hw, rfl⟩
    rw [Finset.mem_coe, mem_S₁w] at hw
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hw
    simp only [Set.mem_ofPred_eq, toReal]
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2, by exact_mod_cast h3,
      by exact_mod_cast h4⟩
  have hz' := hsub hz
  simp only [Set.mem_ofPred_eq, toReal] at hz'
  obtain ⟨h1, h2, h3, h4⟩ := hz'
  rw [mem_S₁w]
  exact ⟨⟨by exact_mod_cast h1, by exact_mod_cast h2⟩,
    by exact_mod_cast h3, by exact_mod_cast h4⟩

/-- `𝒯` is `etaC`-generating: every row of `𝒯` has two points, and `shift_inv` says every
member of the orbit closure has first difference `1` along `(1,0)`. -/
theorem isGeneratingSet_S₁w : IsGeneratingSet etaC S₁w := by
  refine ⟨⟨((2 : ℤ), (-2 : ℤ)), mem_S₁w.mpr (by norm_num)⟩, latticeConvex_S₁w, ?_⟩
  intro a ha _
  refine ⟨ha, ?_⟩
  intro x hx y hy hagr
  rw [mem_S₁w] at ha
  -- the horizontal partner of `a` in its row
  have ha' : ((5 - a.1, a.2) : ℤ × ℤ) ∈ S₁w.erase a := by
    rw [Finset.mem_erase, mem_S₁w]
    refine ⟨?_, by simp only; omega, by simp only; omega⟩
    intro h
    have := congrArg Prod.fst h
    simp only at this
    omega
  have hxy := hagr _ ha'
  rcases (show a.1 = 2 ∨ a.1 = 3 by omega) with h2 | h3
  · have e : ((5 - a.1, a.2) : ℤ × ℤ) = a + ((1 : ℤ), (0 : ℤ)) := by
      ext <;> simp
      omega
    rw [e, shift_inv hx, shift_inv hy] at hxy
    omega
  · have e : ((5 - a.1, a.2) : ℤ × ℤ) + ((1 : ℤ), (0 : ℤ)) = a := by
      ext <;> simp
      omega
    have hx' := shift_inv hx ((5 - a.1, a.2) : ℤ × ℤ)
    have hy' := shift_inv hy ((5 - a.1, a.2) : ℤ × ℤ)
    rw [e] at hx' hy'
    omega

/-- ⚠ `etaC` has infinite range, so every nonempty window has infinitely many patterns and
`P etaC W = 0` (`Set.ncard` of an infinite set).  This is what makes the deficit conjunct
`P ξ S₁ ≤ P ξ Q + pw` trivial in the model below. -/
theorem P_etaC_eq_zero {W : Finset (ℤ × ℤ)} (hW : W.Nonempty) : P etaC W = 0 := by
  obtain ⟨z, hz⟩ := hW
  apply Set.Infinite.ncard
  refine Set.infinite_of_injective_forall_mem (f := fun m : ℤ => pattern etaC W (m, 0)) ?_ ?_
  · intro m m' h
    have := congrFun h ⟨z, hz⟩
    simp only [pattern, etaC, Prod.fst_add, Prod.snd_add] at this
    split_ifs at this <;> omega
  · intro m
    exact ⟨(m, 0), rfl⟩

theorem hshell_one :
    ∀ z ∈ cgc.toChainData.shellInf 1, ϑw z = T (((0 : ℕ) : ℤ) • vl2) xperC z := by
  intro z hz
  rw [mem_shellInf_one] at hz
  simp only [ϑw, T, etaC, xperC, Prod.fst_add, Prod.snd_add, Nat.cast_zero, zero_smul, add_zero]
  rw [if_neg (by omega)]
  ring

theorem hshell_not_two :
    ¬ (∀ z ∈ cgc.toChainData.shellInf (1 + 1), ϑw z = T (((0 : ℕ) : ℤ) • vl2) xperC z) := by
  intro h
  have := h ((1 : ℤ), (-2 : ℤ)) mem_1m2_shellInf_cgc_two
  simp [ϑw, T, etaC, xperC] at this

theorem ϑw_mem : ϑw ∈ orbitClosure etaC := T_mem_orbitClosure _ _

/-- **All eleven conjuncts of `exists_case2_window` hold on `cgc` at `ε = 1`.**  Stated verbatim
(with `cg := cgc`, `ξ := etaC`, `ε := 1`); `target_type_eq` (§5) identifies the shape with the
live target.  This theorem has **no hypotheses**: it is a bare existential, and is the only
satisfaction result in this section.

Witnesses after the eleventh conjunct (2026-09-19): `B := Q`, `pw := 1`, `e := false`.  The
original ten-conjunct model had `pw = 2`, `B = {(2,1)}`; the eleventh conjunct pins
`pw = |bottom row| - 1 = 1` on a width-2 window and `B = maxB Q v_J 1 = Q`. -/
theorem window_model :
    ∃ (S₁ Q B : Finset (ℤ × ℤ)) (τ : ℤ) (pw : ℕ) (R : Set (ℤ × ℤ)),
      IsGeneratingSet etaC S₁ ∧
      Q ⊆ S₁ ∧
      (∃ (n : ℝ × ℝ) (cmax : ℝ),
        n ≠ 0 ∧
        inner2 n cgc.vJ = 0 ∧
        (∀ z ∈ S₁, inner2 n z ≤ cmax) ∧
        (Nivat.R2.face S₁ n cmax).Nonempty ∧
        Q = S₁.filter fun z => inner2 n z < cmax) ∧
      (∀ g ∈ S₁, g ∉ Q → ∀ t : ℤ, τ ≤ t →
        t • cgc.vJ + g ∈ cgc.toChainData.shellInf (1 + 1) ∧
        t • cgc.vJ + g ∉ cgc.toChainData.shellInf 1) ∧
      P etaC S₁ ≤ P etaC Q + pw ∧
      (∀ g ∈ B, ∀ i : ℕ, i < pw → g + (i : ℤ) • cgc.vJ ∈ Q) ∧
      R ⊆ cgc.toChainData.shellInf 1 ∧
      Colle41.IsRegion R p2 cgc.vJ ∧
      (∀ t : ℤ, τ ≤ t → ∀ z ∈ Q,
        t • cgc.vJ + z ∈ R ∧ t • cgc.vJ + z + (1 : ℤ) • p2 ∈ R) ∧
      (B.Nonempty ∧ ∃ b, ∀ z ∈ S₁, b + z ∈ R) ∧
      (∃ e : Bool, pw = (L1Data.topFace e cgc.vJ S₁).card - 1 ∧
        B = L1Data.maxB (L1Data.derivedQ e cgc.vJ S₁) cgc.vJ pw) := by
  refine ⟨S₁w, Qw, Qw, 10, 1, cgc.toChainData.shellInf 1, isGeneratingSet_S₁w, ?_, ?_, ?_, ?_,
    ?_, subset_rfl, isRegion_shellInf_one, ?_, ?_, ?_⟩
  · -- `Q ⊆ S₁`
    intro z hz
    rw [mem_Qw] at hz
    rw [mem_S₁w]
    omega
  · -- the edge: normal `(0,-1) = toReal (-n_J)`, level `2`
    refine ⟨((0 : ℝ), (-1 : ℝ)), 2, ?_, ?_, ?_, ?_, ?_⟩
    · simp [Prod.ext_iff]
    · show inner2 _ vJv = 0
      simp [inner2, vJv]
    · intro z hz
      rw [mem_S₁w] at hz
      have : (-2 : ℝ) ≤ z.2 := by exact_mod_cast hz.2.1
      simp only [inner2]
      linarith
    · refine ⟨((2 : ℤ), (-2 : ℤ)), ?_⟩
      rw [Nivat.R2.mem_face]
      refine ⟨mem_S₁w.mpr (by norm_num), ?_⟩
      norm_num [inner2]
    · ext z
      rw [Finset.mem_filter, mem_Qw, mem_S₁w]
      simp only [inner2]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨⟨h1, by omega, by omega⟩, ?_⟩
        have : (-2 : ℝ) < z.2 := by exact_mod_cast (show (-2 : ℤ) < z.2 by omega)
        linarith
      · rintro ⟨⟨h1, h2, h3⟩, h4⟩
        have : (-2 : ℝ) < z.2 := by linarith
        have : (-2 : ℤ) < z.2 := by exact_mod_cast this
        exact ⟨h1, by omega, h3⟩
  · -- `hface`: the bottom row `y = -2`, slid to `x ≥ 12`, is in layer `2` and not in layer `1`
    intro g hg hgQ t ht
    rw [mem_S₁w] at hg
    rw [mem_Qw] at hgQ
    have hg2 : g.2 = -2 := by omega
    rw [smul_vJ_add]
    constructor
    · show ((t + g.1, g.2) : ℤ × ℤ) ∈ ShInfc (1 + 1)
      rw [mem_ShInfc]
      refine ⟨1, ?_, ?_, ?_⟩ <;> simp only <;> push_cast <;> omega
    · rw [mem_shellInf_one]
      simp only
      omega
  · -- the deficit: trivial, `P etaC _ = 0`
    rw [P_etaC_eq_zero ⟨((2 : ℤ), (-2 : ℤ)), mem_S₁w.mpr (by norm_num)⟩]
    exact Nat.zero_le _
  · -- `hline`: `pw = 1`, so this is `B = Q ⊆ Q`
    intro g hg i hi
    have : i = 0 := by omega
    subst this
    simpa using hg
  · -- `hQR`
    intro t ht z hz
    rw [mem_Qw] at hz
    rw [smul_vJ_add]
    constructor
    · rw [mem_shellInf_one]
      simp only
      omega
    · rw [mem_shellInf_one]
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, p2, smul_eq_mul,
        one_mul]
      omega
  · -- `hbase`: `B = Q ∋ (2,1)`, and `(2,1) + 𝒯 = {4,5} × {-1,…,2} ⊆ Â_∞^{(1)}`
    refine ⟨⟨((2 : ℤ), (1 : ℤ)), mem_Qw.mpr (by norm_num)⟩, ((2 : ℤ), (1 : ℤ)), ?_⟩
    intro z hz
    rw [mem_S₁w] at hz
    rw [mem_shellInf_one]
    simp only [Prod.fst_add, Prod.snd_add]
    omega
  · -- the eleventh conjunct: `e = false`, bottom row `{2,3} × {-2}` has card 2, `maxB Q v_J 1 = Q`
    refine ⟨false, ?_, ?_⟩
    · rw [cgc_vJ, card_topFace_false_box (fun z => mem_S₁w) (by norm_num) (by norm_num)]
      rfl
    · rw [cgc_vJ, derivedQ_false_box (fun z => mem_S₁w) (by norm_num) (by norm_num), maxB_one]
      ext z
      rw [Finset.mem_filter, mem_S₁w, mem_Qw]
      omega

end Model

/-! ## §3 A model on a bundle whose `S` **is** generating

`cgc`/`cgn` fail the leaf binder `hSφ` (§0).  This section builds a third bundle `cgg` whose
window `S = {0, (-1,1)}` is `ξ`-generating, and re-runs the ten-conjunct model on it.

* `ξ = x mod 2` (finite range `{0,1}`, so `P ξ W ≤ 2` is a real bound, not the `P = 0`
  degeneracy of §2), `x_per = ξ` on `y ≥ 0` and `ξ + 1` on `y < 0`.
* `Â_∞ = {0 ≤ y ≤ x}`, sweep direction `v_ℓ = (1,-1)`, `p = (1,1)`, `n_J = (0,1)`, `c_J = 0`,
  `v_J = (1,0)`.  Because `x + y` is invariant under `v_ℓ`, the shells are
  `Â_∞^{(ε)} = {-ε ≤ y, 0 ≤ x + y, y ≤ x}`, lattice-convex for **every** `ε`
  (`isLatticeConvexRegion_shellInf_cgg`) — unlike `cgc`, whose parity gap kills `ε = 2`.
* `S = {0, (-1,1)}`: `ShellMink.ChainDataGeom.a_eq_a'` forces `a = a'` on every bundle, and
  `lex'` then forbids a second point on `a`'s `n_J`-level, so `S` must be `a` plus points
  strictly above; `(-1,1) = -v_ℓ` is chosen so that `fillStep` can fill each new shell row
  from the row above it. -/

namespace Gen

/-- `ξ = x mod 2`. -/
def ξg : Config ℤ := fun z => z.1 % 2
/-- `x_per`: agrees with `ξ` on `y ≥ 0`, flipped on `y < 0`. -/
def xperg : Config ℤ := fun z => (z.1 + (if z.2 < 0 then 1 else 0)) % 2
/-- `v_ℓ = (1,-1)`. -/
def vlg : ℤ × ℤ := (1, -1)
/-- `p = (1,1)`. -/
def pg : ℤ × ℤ := (1, 1)
/-- `v_J = (1,0)`. -/
def vJg : ℤ × ℤ := (1, 0)
/-- `n_J = (0,1)`. -/
def nJg : ℤ × ℤ := (0, 1)
/-- `S_φ = {0, (-1,1)}`. -/
def Sg : Finset (ℤ × ℤ) := {0, ((-1 : ℤ), (1 : ℤ))}
/-- The distinguished point of `S_φ`. -/
def geng : ℤ × ℤ := 0
/-- `Â_∞ = {0 ≤ y ≤ x}`. -/
def Kg : Set (ℤ × ℤ) := {z | 0 ≤ z.2 ∧ z.2 ≤ z.1}
/-- `Â_i = A_i = B_i = Â_∞ ∩ {x + y ≤ i}`. -/
def Ag (i : ℕ) : Set (ℤ × ℤ) := {z | 0 ≤ z.2 ∧ z.2 ≤ z.1 ∧ z.1 + z.2 ≤ i}
/-- `Â_i^{(ε)}`, by the shell formula. -/
def Shg (i ε : ℕ) : Set (ℤ × ℤ) := MaxEnv.shell (Ag i) vlg nJg 0 ε
/-- `Â_∞^{(ε)}`, by the shell formula. -/
def ShInfg (ε : ℕ) : Set (ℤ × ℤ) := MaxEnv.shell Kg vlg nJg 0 ε
/-- The filtration: the shell rows `y = -1, -2, …` are filled one at a time from above. -/
def Filg (i i₀ ε n : ℕ) : Set (ℤ × ℤ) :=
  Ag i ∪ Shg i₀ ε ∪ (Shg i ε ∩ {z | -(n : ℤ) ≤ z.2})

theorem dot_nJg (z : ℤ × ℤ) : dot nJg z = z.2 := by simp [dot, nJg]

/-- `Sg.erase geng = {(-1,1)}`, hence lattice convex — the side condition
`Colle37.GenClosure.step` carries and the old `fillStep` field did not. -/
theorem latticeConvex_Sg_erase : LatticeConvex (Sg.erase geng) := by
  have hE : Sg.erase geng = {((-1 : ℤ), (1 : ℤ))} := by decide
  rw [hE]
  exact Nivat.Colle37.latticeConvex_singleton _


theorem mem_Kg {z : ℤ × ℤ} : z ∈ Kg ↔ 0 ≤ z.2 ∧ z.2 ≤ z.1 := Iff.rfl

theorem mem_Sg {b : ℤ × ℤ} : b ∈ Sg ↔ b = 0 ∨ b = ((-1 : ℤ), (1 : ℤ)) := by
  simp [Sg]

theorem mem_Sg_erase_zero {b : ℤ × ℤ} : b ∈ Sg.erase 0 ↔ b = ((-1 : ℤ), (1 : ℤ)) := by
  rw [Finset.mem_erase, mem_Sg]
  constructor
  · rintro ⟨h1, h2 | h2⟩
    · exact absurd h2 h1
    · exact h2
  · rintro rfl
    exact ⟨by simp [Prod.ext_iff], Or.inr rfl⟩

theorem iUnion_Ag : (⋃ i, Ag i) = Kg := by
  ext z
  constructor
  · intro hz
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
    exact ⟨hi.1, hi.2.1⟩
  · rintro ⟨h1, h2⟩
    refine Set.mem_iUnion.mpr ⟨(z.1 + z.2).toNat, h1, h2, ?_⟩
    have h : ((z.1 + z.2).toNat : ℤ) = z.1 + z.2 := Int.toNat_of_nonneg (by omega)
    omega

/-- Membership in `Â_i^{(ε)}`: `x + y` is `v_ℓ`-invariant, so the shell is a slab. -/
theorem mem_Shg {i ε : ℕ} {z : ℤ × ℤ} :
    z ∈ Shg i ε ↔ -(ε : ℤ) ≤ z.2 ∧ 0 ≤ z.1 + z.2 ∧ z.2 ≤ z.1 ∧ z.1 + z.2 ≤ i := by
  constructor
  · rintro ⟨g, hg, t, rfl, hd⟩
    obtain ⟨h1, h2, h3⟩ := hg
    rw [dot_nJg] at hd
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, vlg, smul_eq_mul,
      mul_one, mul_neg] at hd ⊢
    omega
  · rintro ⟨h1, h2, h3, h4⟩
    rcases le_or_gt 0 z.2 with h | h
    · refine ⟨z, ⟨h, h3, h4⟩, 0, by simp, ?_⟩
      rw [dot_nJg]; omega
    · refine ⟨(z.1 + z.2, 0), ⟨le_rfl, by simp only; omega, by simp only; omega⟩,
        (-z.2).toNat, ?_, ?_⟩
      · have ht : (((-z.2).toNat : ℕ) : ℤ) = -z.2 := Int.toNat_of_nonneg (by omega)
        rw [ht]
        refine Prod.ext ?_ ?_ <;>
          simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, vlg,
            smul_eq_mul] <;> omega
      · rw [dot_nJg]; omega

/-- `ChainData.fillZero` for `Filg`, factored out so `fillCover` can reuse it. -/
theorem Filg_zero (i i₀ ε : ℕ) : Filg i i₀ ε 0 ⊆ Ag i ∪ Shg i₀ ε := by
  intro z hz
  rcases hz with hz | ⟨hz1, hz2⟩
  · exact hz
  · obtain ⟨-, -, h3, h4⟩ := mem_Shg.mp hz1
    have h0 : (0 : ℤ) ≤ z.2 := by simpa using hz2
    exact Or.inl ⟨h0, h3, h4⟩

/-- `ChainData.fillStep` for `Filg`, factored out so `fillCover` can reuse it. -/
theorem Filg_step (i i₀ ε : ℕ) : ∀ n : ℕ, ∀ z ∈ Filg i i₀ ε (n + 1),
    z ∈ Filg i i₀ ε n ∨ ∃ t : ℤ × ℤ, z = geng + t ∧
      ∀ b ∈ Sg.erase geng, b + t ∈ Filg i i₀ ε n := by
  intro n z hz
  rcases hz with hz | ⟨hz1, hz2⟩
  · exact Or.inl (Or.inl hz)
  · have hz2' : -((n : ℤ) + 1) ≤ z.2 := by simpa using hz2
    rcases le_or_gt (-(n : ℤ)) z.2 with h | h
    · exact Or.inl (Or.inr ⟨hz1, h⟩)
    · refine Or.inr ⟨z, (zero_add z).symm, ?_⟩
      intro b hb
      rw [show geng = 0 from rfl, mem_Sg_erase_zero] at hb
      subst hb
      obtain ⟨h1, h2, h3, h4⟩ := mem_Shg.mp hz1
      refine Or.inr ⟨mem_Shg.mpr ⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;>
        simp only [Prod.fst_add, Prod.snd_add, Set.mem_ofPred_eq] <;> omega

/-- Membership in `Â_∞^{(ε)}`. -/
theorem mem_ShInfg {ε : ℕ} {z : ℤ × ℤ} :
    z ∈ ShInfg ε ↔ -(ε : ℤ) ≤ z.2 ∧ 0 ≤ z.1 + z.2 ∧ z.2 ≤ z.1 := by
  constructor
  · rintro ⟨g, hg, t, rfl, hd⟩
    obtain ⟨h1, h2⟩ := hg
    rw [dot_nJg] at hd
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, vlg, smul_eq_mul,
      mul_one, mul_neg] at hd ⊢
    omega
  · rintro ⟨h1, h2, h3⟩
    rcases le_or_gt 0 z.2 with h | h
    · refine ⟨z, ⟨h, h3⟩, 0, by simp, ?_⟩
      rw [dot_nJg]; omega
    · refine ⟨(z.1 + z.2, 0), ⟨le_rfl, by simp only; omega⟩, (-z.2).toNat, ?_, ?_⟩
      · have ht : (((-z.2).toNat : ℕ) : ℤ) = -z.2 := Int.toNat_of_nonneg (by omega)
        rw [ht]
        refine Prod.ext ?_ ?_ <;>
          simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, vlg,
            smul_eq_mul] <;> omega
      · rw [dot_nJg]; omega

/-- The swept set `reachSet Â_∞ v_ℓ = {0 ≤ x + y, y ≤ x}`. -/
theorem mem_reachSet_Kg {z : ℤ × ℤ} (h2 : 0 ≤ z.1 + z.2) (h3 : z.2 ≤ z.1) :
    z ∈ reachSet Kg vlg := by
  rcases le_or_gt 0 z.2 with h | h
  · exact ⟨z, ⟨h, h3⟩, 0, by simp⟩
  · refine ⟨(z.1 + z.2, 0), ⟨le_rfl, by simp only; omega⟩, (-z.2).toNat, ?_⟩
    have ht : (((-z.2).toNat : ℕ) : ℤ) = -z.2 := Int.toNat_of_nonneg (by omega)
    rw [ht]
    refine Prod.ext ?_ ?_ <;>
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, vlg,
        smul_eq_mul] <;> omega

/-- The `ℓ_ι`-normal of `ChainGeom.lean`, at `p = (1,1)`, `v_J = (1,0)`. -/
def nLg : ℤ × ℤ := det pg vJg • ((-pg.2, pg.1) : ℤ × ℤ)

theorem nLg_eq : nLg = ((1 : ℤ), (-1 : ℤ)) := by
  simp [nLg, det, pg, vJg]

theorem dot_nLg (z : ℤ × ℤ) : dot nLg z = z.1 - z.2 := by
  rw [nLg_eq]; simp [dot]; ring

/-- Every period of `x_per` on the half plane `{x - y ≥ 0}` is horizontal: the column
`x = N` sees `x_per` flip between rows `0` and `-1`. -/
theorem period_snd_eq_zero {h : ℤ × ℤ}
    (hh : ∀ g ∈ {z : ℤ × ℤ | (0 : ℤ) ≤ dot nLg z},
      g + h ∈ {z : ℤ × ℤ | (0 : ℤ) ≤ dot nLg z} → xperg (g + h) = xperg g) : h.2 = 0 := by
  have hm : ∀ w : ℤ × ℤ, (0 : ℤ) ≤ w.1 - w.2 → w ∈ {z : ℤ × ℤ | (0 : ℤ) ≤ dot nLg z} := by
    intro w hw
    show (0 : ℤ) ≤ dot nLg w
    rw [dot_nLg]; exact hw
  obtain ⟨N, hN1, hN2⟩ : ∃ N : ℤ, 0 ≤ N ∧ h.2 - h.1 ≤ N :=
    ⟨max 0 (h.2 - h.1), le_max_left _ _, le_max_right _ _⟩
  have e0 := hh (N, 0) (hm _ (by simp only; omega))
    (hm _ (by simp only [Prod.fst_add, Prod.snd_add]; omega))
  have e1 := hh (N, -1) (hm _ (by simp only; omega))
    (hm _ (by simp only [Prod.fst_add, Prod.snd_add]; omega))
  simp only [xperg, Prod.fst_add, Prod.snd_add] at e0 e1
  split_ifs at e0 e1 <;> omega

/-- The real segment from `(-1,1)` to `0` is convex. -/
theorem convex_segg : Convex ℝ {q : ℝ × ℝ | q.1 + q.2 = 0 ∧ -1 ≤ q.1 ∧ q.1 ≤ 0} := by
  intro u hu v hv a b ha hb hab
  obtain ⟨hu1, hu2, hu3⟩ := hu
  obtain ⟨hv1, hv2, hv3⟩ := hv
  simp only [Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul]
  refine ⟨?_, ?_, ?_⟩
  · linear_combination a * hu1 + b * hv1
  · nlinarith
  · nlinarith

theorem latticeConvex_Sg : LatticeConvex Sg := by
  intro z hz
  have hsub : Conv Sg ⊆ {q : ℝ × ℝ | q.1 + q.2 = 0 ∧ -1 ≤ q.1 ∧ q.1 ≤ 0} := by
    apply convexHull_min _ convex_segg
    rintro _ ⟨w, hw, rfl⟩
    rw [Finset.mem_coe, mem_Sg] at hw
    rcases hw with rfl | rfl <;>
      exact ⟨by norm_num [toReal], by norm_num [toReal], by norm_num [toReal]⟩
  obtain ⟨h1, h2, h3⟩ := hsub hz
  simp only [toReal] at h1 h2 h3
  have e1 : z.1 + z.2 = 0 := by exact_mod_cast h1
  have e2 : (-1 : ℤ) ≤ z.1 := by exact_mod_cast h2
  have e3 : z.1 ≤ 0 := by exact_mod_cast h3
  rw [mem_Sg]
  rcases (show z.1 = 0 ∨ z.1 = -1 by omega) with h | h
  · left; ext <;> simp <;> omega
  · right; ext <;> simp <;> omega

/-- **The bundle.** -/
def cgg : ChainDataGeom ξg xperg vlg pg Sg geng where
  Env := fun _ => True
  B := Ag
  A := Ag
  u := fun _ => 0
  kk := fun _ => 0
  Ahat := Ag
  shell := Shg
  shellInf := ShInfg
  envB := fun _ => trivial
  envA := fun _ => trivial
  subBA := fun _ => subset_rfl
  subAB := by
    intro i z hz
    obtain ⟨h1, h2, h3⟩ := hz
    exact ⟨h1, h2, by push_cast; omega⟩
  subStrip := fun i => Colle35.subset_halfStrip _ _
  agreeA := by
    intro i z hz
    have hnn : ¬ (z.2 < 0) := by have := hz.1; omega
    simp only [ξg, xperg, add_zero, if_neg hnn]
  AhatEq := by
    intro i
    ext z
    simp
  AhatMono := by
    intro i j hij z hz
    obtain ⟨h1, h2, h3⟩ := hz
    have hc : (i : ℤ) ≤ (j : ℤ) := by exact_mod_cast hij
    exact ⟨h1, h2, by omega⟩
  maximalHat := by
    intro i Tset _ _ hstrip hagr z hz
    obtain ⟨b, hb, t, hbt⟩ := hstrip hz
    obtain ⟨hb1, hb2, hb3⟩ := hb
    have hf : z.1 = b.1 + (t : ℤ) := by
      have h := congrArg Prod.fst hbt
      simp [vlg] at h
      omega
    have hs : z.2 = b.2 - (t : ℤ) := by
      have h := congrArg Prod.snd hbt
      simp [vlg] at h
      omega
    have hzz : ξg z = xperg z := by simpa using hagr z hz
    have hnn : (0 : ℤ) ≤ z.2 := by
      by_contra hc
      have hc' : z.2 < 0 := not_le.mp hc
      simp only [ξg, xperg] at hzz
      rw [if_pos hc'] at hzz
      omega
    exact ⟨hnn, by omega, by omega⟩
  shellFinite := by
    intro i ε
    have hfin : ((Set.Icc (-(ε : ℤ)) ((i : ℤ) + (ε : ℤ))) ×ˢ
        (Set.Icc (-(ε : ℤ)) (i : ℤ))).Finite :=
      (Set.finite_Icc _ _).prod (Set.finite_Icc _ _)
    refine hfin.subset ?_
    intro z hz
    obtain ⟨h1, h2, h3, h4⟩ := mem_Shg.mp hz
    exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩
  subShell := by
    intro i ε z hz
    obtain ⟨h1, h2, h3⟩ := hz
    exact mem_Shg.mpr ⟨by omega, by omega, h2, h3⟩
  shellSubInf := by
    intro i ε z hz
    obtain ⟨h1, h2, h3, -⟩ := mem_Shg.mp hz
    exact mem_ShInfg.mpr ⟨h1, h2, h3⟩
  shellInfZero := by
    intro z hz
    obtain ⟨h1, h2, h3⟩ := mem_ShInfg.mp hz
    rw [iUnion_Ag]
    exact ⟨by simpa using h1, h3⟩
  -- `I₀`（第 162 轮，`b3_colle2.txt:520`）：本实例的 shell 字段都不看 `i` 的下界，取 0。
  I₀ := 0
  shellSubStrip := by
    intro ε _ _ _ i _ z hz
    obtain ⟨g, hg, t, rfl, -⟩ := hz
    exact ⟨g, hg, t, by simp⟩
  shellProper := by
    intro ε _i₀ hε _hEnv i _hi hsub
    have hε' : (1 : ℤ) ≤ (ε : ℤ) := by exact_mod_cast hε
    have hmem : ((1 : ℤ), (-1 : ℤ)) ∈ Shg i ε :=
      mem_Shg.mpr ⟨by omega, by norm_num, by norm_num, by simp⟩
    obtain ⟨h1, -, -⟩ := hsub hmem
    simp at h1
  shellEnv := ⟨1, 0, one_pos, fun _ _ => trivial⟩
  fill := Filg
  fillZero := Filg_zero
  fillStep := fun i i₀ ε n => Filg_step i i₀ ε n
  -- Round 80 (`Lemma35.lean:765`) rephrased `fillCover` against `Colle37.GenClosure`;
  -- `genFill_of_abstract_fill` (`GenClosureWeaken.lean:116`) turns `Filg_zero` / `Filg_step`
  -- into it, at the same filtration index `ε` the old `⋃ n` witness used.
  fillCover := by
    intro ε i₀ _hε _hEnv i _hi z hz
    exact Nivat.GenClosureWeaken.genFill_of_abstract_fill (S := Sg) (gen := geng)
      (fill := Filg i i₀ ε) (by decide) latticeConvex_Sg_erase (Filg_zero i i₀ ε)
      (Filg_step i i₀ ε) ε z (Or.inr ⟨hz, (mem_Shg.mp hz).1⟩)
  -- ChainDataWithShell
  vJ1 := vlg
  nJ := nJg
  cJ := 0
  shellInf_eq := by
    intro ε
    rw [iUnion_Ag]
    rfl
  ahat_nonempty := by
    refine ⟨((0 : ℤ), (0 : ℤ)), ?_⟩
    rw [iUnion_Ag]
    exact ⟨le_rfl, le_rfl⟩
  ahat_halfPlane := by
    intro g hg
    rw [iUnion_Ag] at hg
    rw [dot_nJg]
    exact hg.1
  -- ChainDataGeom
  vJ := vJg
  a := 0
  a' := 0
  r := 0
  latticeConvex_S := latticeConvex_Sg
  a_mem := by simp [Sg]
  a'_mem := by simp [Sg]
  lex := by
    intro b hb
    rw [mem_Sg_erase_zero] at hb
    subst hb
    left
    simp [dot, nJg]
  lex' := by
    intro b hb
    rw [mem_Sg_erase_zero] at hb
    subst hb
    left
    simp [dot, nJg]
  edge := by
    intro b hb
    rw [mem_Sg_erase_zero] at hb
    subst hb
    right
    simp [dot, nJg]
  edge' := by
    intro b hb
    rw [mem_Sg_erase_zero] at hb
    subst hb
    right
    simp [dot, nJg]
  dot_nJ_vJ := by simp [dot, nJg, vJg]
  bottom := by
    intro ε
    refine ⟨((ε : ℤ) + 1, -(ε : ℤ) - 1), 0, ?_, ?_, ?_, ?_⟩
    · rw [dot_nJg]
      show -(ε : ℤ) - 1 = 0 - (ε : ℤ) - 1
      ring
    · intro k hk
      rw [iUnion_Ag]
      refine mem_reachSet_Kg ?_ ?_ <;>
        simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, vJg, smul_eq_mul,
          mul_one, mul_zero, add_zero] <;> omega
    · intro b hb k hk
      rw [iUnion_Ag]
      rcases mem_Sg.mp hb with hb0 | hb0
      · subst hb0
        refine mem_reachSet_Kg ?_ ?_ <;>
          simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, vJg,
            smul_eq_mul, mul_one, mul_zero, add_zero, sub_self] <;> omega
      · subst hb0
        refine mem_reachSet_Kg ?_ ?_ <;>
          simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, vJg,
            smul_eq_mul, mul_one, mul_zero, add_zero, sub_zero] <;> omega
    · intro z hz
      obtain ⟨h1, h2, h3⟩ := mem_ShInfg.mp hz
      push_cast at h1
      rcases le_or_gt (-(ε : ℤ)) z.2 with h | h
      · exact Or.inl (mem_ShInfg.mpr ⟨h, h2, h3⟩)
      · refine Or.inr ⟨z.1 - ((ε : ℤ) + 1), by omega, ?_⟩
        refine Prod.ext ?_ ?_ <;>
          simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, vJg,
            smul_eq_mul, mul_one, mul_zero, add_zero] <;> omega
  rec_p := by
    intro g hg
    rw [iUnion_Ag, mem_Kg] at hg ⊢
    obtain ⟨h1, h2⟩ := hg
    simp only [Prod.fst_add, Prod.snd_add, pg]
    omega
  dot_nJ_p := by simp [dot, nJg, pg]
  vJ_ne := by simp [vJg, Prod.ext_iff]
  vJ_prim := by
    show IsCoprime ((1 : ℤ)) ((0 : ℤ))
    exact isCoprime_one_left
  rec_vJ := by
    intro g hg
    rw [iUnion_Ag, mem_Kg] at hg ⊢
    obtain ⟨h1, h2⟩ := hg
    simp only [Prod.fst_add, Prod.snd_add, vJg]
    omega
  cL := 0
  ahat_halfPlane_L := by
    intro g hg
    rw [iUnion_Ag, mem_Kg] at hg
    show (0 : ℤ) ≤ dot nLg g
    rw [dot_nLg]
    omega
  ahat_attained_L := by
    refine ⟨((0 : ℤ), (0 : ℤ)), ?_, ?_⟩
    · rw [iUnion_Ag]; exact ⟨le_rfl, le_rfl⟩
    · show dot nLg ((0 : ℤ), (0 : ℤ)) = 0
      rw [dot_nLg]; norm_num
  nJ_prim := by
    show IsCoprime (0 : ℤ) (1 : ℤ)
    exact isCoprime_one_right
  nfp_L := by
    rintro ⟨h, h', hdet, ⟨-, hh⟩, ⟨-, hh'⟩⟩
    have e1 := period_snd_eq_zero hh
    have e2 := period_snd_eq_zero hh'
    apply hdet
    simp [det, e1, e2]

/-! ### The binders of `exists_case2_window` on `cgg` -/

/-- Every member of `X_ξ` is `w ↦ (u + w.1) % 2` on any two given sites. -/
theorem orbit_pair {x : Config ℤ} (hx : x ∈ orbitClosure ξg) (w w' : ℤ × ℤ) :
    ∃ u : ℤ, x w = (u + w.1) % 2 ∧ x w' = (u + w'.1) % 2 := by
  obtain ⟨u, hu⟩ := hx {w, w'}
  refine ⟨u.1, ?_, ?_⟩
  · have := hu w (by simp)
    simpa [ξg] using this
  · have := hu w' (by simp)
    simpa [ξg] using this

/-- **`S_φ = {0, (-1,1)}` is `ξ`-generating** — the leaf binder `hSφ` that `cgc`/`cgn` fail. -/
theorem isGeneratingSet_Sg : IsGeneratingSet ξg Sg := by
  refine ⟨⟨0, by simp [Sg]⟩, latticeConvex_Sg, ?_⟩
  intro a ha _
  refine ⟨ha, ?_⟩
  intro x hx y hy hagr
  rcases mem_Sg.mp ha with rfl | rfl
  · have hb : ((-1 : ℤ), (1 : ℤ)) ∈ Sg.erase 0 := mem_Sg_erase_zero.mpr rfl
    have h := hagr _ hb
    obtain ⟨u, hu1, hu2⟩ := orbit_pair hx 0 ((-1 : ℤ), (1 : ℤ))
    obtain ⟨u', hu1', hu2'⟩ := orbit_pair hy 0 ((-1 : ℤ), (1 : ℤ))
    rw [hu2, hu2'] at h
    rw [hu1, hu1']
    simp only [Prod.fst_zero, add_zero] at h ⊢
    omega
  · have hb : (0 : ℤ × ℤ) ∈ Sg.erase ((-1 : ℤ), (1 : ℤ)) :=
      Finset.mem_erase.mpr ⟨by simp [Prod.ext_iff], by simp [Sg]⟩
    have h := hagr _ hb
    obtain ⟨u, hu1, hu2⟩ := orbit_pair hx ((-1 : ℤ), (1 : ℤ)) 0
    obtain ⟨u', hu1', hu2'⟩ := orbit_pair hy ((-1 : ℤ), (1 : ℤ)) 0
    rw [hu2, hu2'] at h
    rw [hu1, hu1']
    simp only [Prod.fst_zero, add_zero] at h ⊢
    omega

theorem cgg_vJ : cgg.vJ = ((1 : ℤ), (0 : ℤ)) := rfl

theorem smul_vJ_add_cgg (t : ℤ) (g : ℤ × ℤ) : t • cgg.vJ + g = (t + g.1, g.2) := by
  rw [cgg_vJ]; ext <;> simp

theorem mem_shellInf_cgg {ε : ℕ} {z : ℤ × ℤ} :
    z ∈ cgg.toChainData.shellInf ε ↔ -(ε : ℤ) ≤ z.2 ∧ 0 ≤ z.1 + z.2 ∧ z.2 ≤ z.1 :=
  mem_ShInfg

/-- **Every shell of `cgg` is lattice-convex** — contrast `cgc` (`ε = 2` refuted) and `cgn`
(every `ε` refuted).  So `R := Â_∞^{(ε)}` is a live choice on this bundle at every `ε`. -/
theorem isLatticeConvexRegion_shellInf_cgg (ε : ℕ) :
    IsLatticeConvexRegion (cgg.toChainData.shellInf ε) := by
  refine ⟨{q : ℝ × ℝ | -(ε : ℝ) ≤ q.2 ∧ 0 ≤ q.1 + q.2 ∧ q.2 ≤ q.1}, ?_, ?_, ?_⟩
  · intro u hu v hv a b ha hb hab
    obtain ⟨hu1, hu2, hu3⟩ := hu
    obtain ⟨hv1, hv2, hv3⟩ := hv
    simp only [Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul]
    have e1 := mul_le_mul_of_nonneg_left hu1 ha
    have e2 := mul_le_mul_of_nonneg_left hv1 hb
    have e3 := mul_le_mul_of_nonneg_left hu2 ha
    have e4 := mul_le_mul_of_nonneg_left hv2 hb
    have e5 := mul_le_mul_of_nonneg_left hu3 ha
    have e6 := mul_le_mul_of_nonneg_left hv3 hb
    have hsum : a * (-(ε : ℝ)) + b * (-(ε : ℝ)) = -(ε : ℝ) := by
      rw [← add_mul, hab, one_mul]
    refine ⟨?_, ?_, ?_⟩ <;> nlinarith
  · have he : {q : ℝ × ℝ | -(ε : ℝ) ≤ q.2 ∧ 0 ≤ q.1 + q.2 ∧ q.2 ≤ q.1}
        = {q : ℝ × ℝ | -(ε : ℝ) ≤ q.2} ∩
          ({q : ℝ × ℝ | 0 ≤ q.1 + q.2} ∩ {q : ℝ × ℝ | q.2 ≤ q.1}) := rfl
    rw [he]
    exact (isClosed_le continuous_const continuous_snd).inter
      ((isClosed_le continuous_const (continuous_fst.add continuous_snd)).inter
        (isClosed_le continuous_snd continuous_fst))
  · ext z
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, toReal, mem_shellInf_cgg]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨by exact_mod_cast h1, by exact_mod_cast h2, by exact_mod_cast h3⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨by exact_mod_cast h1, by exact_mod_cast h2, by exact_mod_cast h3⟩

theorem isRegion_shellInf_cgg (ε : ℕ) :
    Colle41.IsRegion (cgg.toChainData.shellInf ε) pg cgg.vJ :=
  (cgg.isRegion_shellInf_iff ε).mpr (isLatticeConvexRegion_shellInf_cgg ε)

/-- `hRconv` for `cgg`: `Â_∞ = Â_∞^{(0)}`. -/
theorem hRconv_cgg : IsLatticeConvexRegion (⋃ i, cgg.toChainData.Ahat i) := by
  have hU : (⋃ i, cgg.toChainData.Ahat i) = cgg.toChainData.shellInf 0 := by
    show (⋃ i, Ag i) = ShInfg 0
    rw [iUnion_Ag]
    ext z
    rw [mem_Kg, mem_ShInfg]
    simp only [Nat.cast_zero, neg_zero]
    omega
  rw [hU]
  exact isLatticeConvexRegion_shellInf_cgg 0

/-- `hshell_ε` at `ε = 0`, `K = 0`, `ϑ = ξ`: `ξ = x_per` on `y ≥ 0`. -/
theorem hshell_zero :
    ∀ z ∈ cgg.toChainData.shellInf 0, ξg z = T (((0 : ℕ) : ℤ) • vlg) xperg z := by
  intro z hz
  obtain ⟨h1, -, -⟩ := mem_shellInf_cgg.mp hz
  have hnn : ¬ (z.2 < 0) := by push_cast at h1; omega
  simp [T, ξg, xperg, hnn]

/-- `hshell_not_εp1` at `ε = 0`: `ξ (1,-1) = 1 ≠ 0 = x_per (1,-1)`. -/
theorem hshell_not_one :
    ¬ (∀ z ∈ cgg.toChainData.shellInf (0 + 1), ξg z = T (((0 : ℕ) : ℤ) • vlg) xperg z) := by
  intro h
  have := h ((1 : ℤ), (-1 : ℤ))
    (mem_shellInf_cgg.mpr ⟨by norm_num, by norm_num, by norm_num⟩)
  norm_num [T, ξg, xperg] at this

/-! ### The eleven conjuncts on `cgg` at `ε = 0` -/

/-- `𝒯 = {3,4} × {-1,0,1}`: rows `-1` (the face), `0`, `1`. -/
def S₁g : Finset (ℤ × ℤ) := ({3, 4} : Finset ℤ) ×ˢ ({-1, 0, 1} : Finset ℤ)
/-- `𝒯 ∖ ℓ'_𝒯 = {3,4} × {0,1}`. -/
def Qg : Finset (ℤ × ℤ) := ({3, 4} : Finset ℤ) ×ˢ ({0, 1} : Finset ℤ)
/-- The seed `{(3,1)}`; its run `(3,1), (4,1)` is in `Q`, and `(3,1) + 𝒯 ⊆ Â_∞`. -/
def Bg : Finset (ℤ × ℤ) := {((3 : ℤ), (1 : ℤ))}

theorem mem_S₁g {z : ℤ × ℤ} : z ∈ S₁g ↔ (3 ≤ z.1 ∧ z.1 ≤ 4) ∧ (-1 ≤ z.2 ∧ z.2 ≤ 1) := by
  simp only [S₁g, Finset.mem_product, Finset.mem_insert, Finset.mem_singleton]
  omega

theorem mem_Qg {z : ℤ × ℤ} : z ∈ Qg ↔ (3 ≤ z.1 ∧ z.1 ≤ 4) ∧ (0 ≤ z.2 ∧ z.2 ≤ 1) := by
  simp only [Qg, Finset.mem_product, Finset.mem_insert, Finset.mem_singleton]
  omega

/-- The real box `[3,4] × [-1,1]` is convex. -/
theorem convex_boxg :
    Convex ℝ {q : ℝ × ℝ | 3 ≤ q.1 ∧ q.1 ≤ 4 ∧ -1 ≤ q.2 ∧ q.2 ≤ 1} := by
  intro u hu v hv a b ha hb hab
  obtain ⟨hu1, hu2, hu3, hu4⟩ := hu
  obtain ⟨hv1, hv2, hv3, hv4⟩ := hv
  simp only [Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith

theorem latticeConvex_S₁g : LatticeConvex S₁g := by
  intro z hz
  have hsub : Conv S₁g ⊆ {q : ℝ × ℝ | 3 ≤ q.1 ∧ q.1 ≤ 4 ∧ -1 ≤ q.2 ∧ q.2 ≤ 1} := by
    apply convexHull_min _ convex_boxg
    rintro _ ⟨w, hw, rfl⟩
    rw [Finset.mem_coe, mem_S₁g] at hw
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hw
    simp only [Set.mem_ofPred_eq, toReal]
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2, by exact_mod_cast h3,
      by exact_mod_cast h4⟩
  have hz' := hsub hz
  simp only [Set.mem_ofPred_eq, toReal] at hz'
  obtain ⟨h1, h2, h3, h4⟩ := hz'
  rw [mem_S₁g]
  exact ⟨⟨by exact_mod_cast h1, by exact_mod_cast h2⟩,
    by exact_mod_cast h3, by exact_mod_cast h4⟩

/-- `𝒯` is `ξ`-generating: every vertex has a horizontal partner in its row. -/
theorem isGeneratingSet_S₁g : IsGeneratingSet ξg S₁g := by
  refine ⟨⟨((3 : ℤ), (-1 : ℤ)), mem_S₁g.mpr (by norm_num)⟩, latticeConvex_S₁g, ?_⟩
  intro a ha _
  refine ⟨ha, ?_⟩
  intro x hx y hy hagr
  rw [mem_S₁g] at ha
  have ha' : ((7 - a.1, a.2) : ℤ × ℤ) ∈ S₁g.erase a := by
    rw [Finset.mem_erase, mem_S₁g]
    refine ⟨?_, by simp only; omega, by simp only; omega⟩
    intro h
    have := congrArg Prod.fst h
    simp only at this
    omega
  have h := hagr _ ha'
  obtain ⟨u, hu1, hu2⟩ := orbit_pair hx a (7 - a.1, a.2)
  obtain ⟨u', hu1', hu2'⟩ := orbit_pair hy a (7 - a.1, a.2)
  rw [hu2, hu2'] at h
  rw [hu1, hu1']
  simp only at h
  omega

/-- Every pattern of `ξ = x mod 2` is one of two: `ξ` has only two translates. -/
theorem pattern_ξg (W : Finset (ℤ × ℤ)) (u : ℤ × ℤ) :
    pattern ξg W u = pattern ξg W (u.1 % 2, 0) := by
  funext q
  simp only [pattern, ξg, Prod.fst_add]
  omega

/-- `P ξ W ≤ 2` for every window — a genuine (finite-range) complexity bound, unlike the
`P etaC W = 0` degeneracy of §2. -/
theorem P_ξg_le_two (W : Finset (ℤ × ℤ)) : P ξg W ≤ 2 := by
  have hsub : patterns ξg W ⊆ {pattern ξg W (0, 0), pattern ξg W (1, 0)} := by
    rintro _ ⟨u, rfl⟩
    have hu := pattern_ξg W u
    rcases (show u.1 % 2 = 0 ∨ u.1 % 2 = 1 by omega) with h | h <;> rw [h] at hu <;>
      rw [hu] <;> simp
  calc P ξg W = (patterns ξg W).ncard := rfl
    _ ≤ ({pattern ξg W (0, 0), pattern ξg W (1, 0)} : Set _).ncard :=
        Set.ncard_le_ncard hsub ((Set.finite_singleton _).insert _)
    _ ≤ ({pattern ξg W (1, 0)} : Set _).ncard + 1 := Set.ncard_insert_le _ _
    _ = 2 := by rw [Set.ncard_singleton]

/-- **All eleven conjuncts of `exists_case2_window` hold on `cgg` at `ε = 0`, with a generating
`S_φ`.**  Stated verbatim (with `cg := cgg`, `ξ := ξg`, `p := pg`, `ε := 0`); no hypotheses.
Witnesses after the eleventh conjunct: `B := Q`, `pw := 1`, `e := false` (the original
`pw = 2`, `B = {(3,1)}` fails the eleventh, which pins `pw = |bottom row| - 1 = 1`). -/
theorem window_model_gen :
    ∃ (S₁ Q B : Finset (ℤ × ℤ)) (τ : ℤ) (pw : ℕ) (R : Set (ℤ × ℤ)),
      IsGeneratingSet ξg S₁ ∧
      Q ⊆ S₁ ∧
      (∃ (n : ℝ × ℝ) (cmax : ℝ),
        n ≠ 0 ∧
        inner2 n cgg.vJ = 0 ∧
        (∀ z ∈ S₁, inner2 n z ≤ cmax) ∧
        (Nivat.R2.face S₁ n cmax).Nonempty ∧
        Q = S₁.filter fun z => inner2 n z < cmax) ∧
      (∀ g ∈ S₁, g ∉ Q → ∀ t : ℤ, τ ≤ t →
        t • cgg.vJ + g ∈ cgg.toChainData.shellInf (0 + 1) ∧
        t • cgg.vJ + g ∉ cgg.toChainData.shellInf 0) ∧
      P ξg S₁ ≤ P ξg Q + pw ∧
      (∀ g ∈ B, ∀ i : ℕ, i < pw → g + (i : ℤ) • cgg.vJ ∈ Q) ∧
      R ⊆ cgg.toChainData.shellInf 0 ∧
      Colle41.IsRegion R pg cgg.vJ ∧
      (∀ t : ℤ, τ ≤ t → ∀ z ∈ Q,
        t • cgg.vJ + z ∈ R ∧ t • cgg.vJ + z + (1 : ℤ) • pg ∈ R) ∧
      (B.Nonempty ∧ ∃ b, ∀ z ∈ S₁, b + z ∈ R) ∧
      (∃ e : Bool, pw = (L1Data.topFace e cgg.vJ S₁).card - 1 ∧
        B = L1Data.maxB (L1Data.derivedQ e cgg.vJ S₁) cgg.vJ pw) := by
  refine ⟨S₁g, Qg, Qg, 10, 1, cgg.toChainData.shellInf 0, isGeneratingSet_S₁g, ?_, ?_, ?_, ?_,
    ?_, subset_rfl, isRegion_shellInf_cgg 0, ?_, ?_, ?_⟩
  · -- `Q ⊆ S₁`
    intro z hz
    rw [mem_Qg] at hz
    rw [mem_S₁g]
    omega
  · -- the edge: normal `(0,-1) = toReal (-n_J)`, level `1`
    refine ⟨((0 : ℝ), (-1 : ℝ)), 1, ?_, ?_, ?_, ?_, ?_⟩
    · simp [Prod.ext_iff]
    · show inner2 _ vJg = 0
      simp [inner2, vJg]
    · intro z hz
      rw [mem_S₁g] at hz
      have : (-1 : ℝ) ≤ z.2 := by exact_mod_cast hz.2.1
      simp only [inner2]
      linarith
    · refine ⟨((3 : ℤ), (-1 : ℤ)), ?_⟩
      rw [Nivat.R2.mem_face]
      refine ⟨mem_S₁g.mpr (by norm_num), ?_⟩
      norm_num [inner2]
    · ext z
      rw [Finset.mem_filter, mem_Qg, mem_S₁g]
      simp only [inner2]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨⟨h1, by omega, by omega⟩, ?_⟩
        have : (-1 : ℝ) < z.2 := by exact_mod_cast (show (-1 : ℤ) < z.2 by omega)
        linarith
      · rintro ⟨⟨h1, h2, h3⟩, h4⟩
        have : (-1 : ℝ) < z.2 := by linarith
        have : (-1 : ℤ) < z.2 := by exact_mod_cast this
        exact ⟨h1, by omega, h3⟩
  · -- `hface`: the row `y = -1`, slid to `x ≥ 13`, is in layer `1` and not in layer `0`
    intro g hg hgQ t ht
    rw [mem_S₁g] at hg
    rw [mem_Qg] at hgQ
    have hg2 : g.2 = -1 := by omega
    rw [smul_vJ_add_cgg]
    constructor
    · rw [mem_shellInf_cgg]
      simp only
      push_cast
      omega
    · rw [mem_shellInf_cgg]
      simp only
      push_cast
      omega
  · -- the deficit: `P ξ 𝒯 ≤ 2 ≤ P ξ Q + 1` (`Q` is nonempty and `ξ` has finite range)
    have hQ : 1 ≤ P ξg Qg := by
      have hfin : (patterns ξg Qg).Finite := by
        refine Set.Finite.subset (Set.toFinite {pattern ξg Qg (0, 0), pattern ξg Qg (1, 0)}) ?_
        rintro _ ⟨u, rfl⟩
        have hu := pattern_ξg Qg u
        rcases (show u.1 % 2 = 0 ∨ u.1 % 2 = 1 by omega) with h | h <;> rw [h] at hu <;>
          rw [hu] <;> simp
      exact (Set.ncard_pos hfin).mpr ⟨_, ⟨(0, 0), rfl⟩⟩
    exact (P_ξg_le_two _).trans (by omega)
  · -- `hline`: `pw = 1`, so this is `B = Q ⊆ Q`
    intro g hg i hi
    have : i = 0 := by omega
    subst this
    simpa using hg
  · -- `hQR`
    intro t ht z hz
    rw [mem_Qg] at hz
    rw [smul_vJ_add_cgg]
    constructor
    · rw [mem_shellInf_cgg]
      simp only
      omega
    · rw [mem_shellInf_cgg]
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, pg, smul_eq_mul,
        one_mul]
      omega
  · -- `hbase`: `B = Q ∋ (3,1)`, and `(3,1) + 𝒯 = {6,7} × {0,1,2} ⊆ Â_∞`
    refine ⟨⟨((3 : ℤ), (1 : ℤ)), mem_Qg.mpr (by norm_num)⟩, ((3 : ℤ), (1 : ℤ)), ?_⟩
    intro z hz
    rw [mem_S₁g] at hz
    rw [mem_shellInf_cgg]
    simp only [Prod.fst_add, Prod.snd_add]
    omega
  · -- the eleventh conjunct: `e = false`, bottom row `{3,4} × {-1}` has card 2, `maxB Q v_J 1 = Q`
    refine ⟨false, ?_, ?_⟩
    · rw [cgg_vJ, card_topFace_false_box (fun z => mem_S₁g) (by norm_num) (by norm_num)]
      rfl
    · rw [cgg_vJ, derivedQ_false_box (fun z => mem_S₁g) (by norm_num) (by norm_num), maxB_one]
      ext z
      rw [Finset.mem_filter, mem_S₁g, mem_Qg]
      omega

/-! ### §4 The eleven conjuncts at **every** `ε` — and why `ε ≥ 1` is out of reach on `cgg`

`ε` is not a free parameter of `exists_case2_window`: it is pinned by the two binders
`hshell_ε` / `hshell_not_εp1` (the switch layer of `lemma35`).  So "does `cgg` still satisfy the
conjuncts at `ε = 1, 2`" splits into two questions with different answers:

* **The conclusion, at every `ε`** (`window_model_gen_all`): yes, uniformly.  The window is the
  `2 × (ε + 3)` box `{3+ε, 4+ε} × [-ε-1, 1]` — `window_height` (§1) forces height `≥ ε + 2`,
  and the columns are shifted by `ε` so that `(3+ε, 1) + 𝒯 ⊆ Â_∞^{(ε)}` (`hbase`; with fixed
  columns `{3,4}` that containment fails from `ε = 7` on).  `τ = 10`, `pw = 2`,
  `R = Â_∞^{(ε)}` are the same at every `ε`.  **No conjunct breaks at any `ε`.**
* **The binders, at `ε ≥ 1`** (`not_hshell_of_pos`): `hshell_ε` is unsatisfiable on `cgg` for
  every `ϑ ∈ X_ξ` and every `K`.  `X_ξ = {z ↦ (u + z.1) % 2}`, while `T (K v_ℓ) x_per` flips
  parity on rows `< K` and not on rows `≥ K`; `Â_∞^{(ε)}` contains the row `-ε < 0 ≤ K` as
  soon as `ε ≥ 1`.  So on `cgg` the instance `exists_case2_window cgg` has content **only at
  `ε = 0`**; at `ε ≥ 1` it is vacuous for a reason independent of `hξ`.

Hand-read, not proved: the second point is structural for bundles with `Env := fun _ => True`.
`maximalHat` then makes `Â_i` maximal among *all* sets in the half-strip on which `η` and
`x_per` agree, so agreement on a shell of positive thickness contradicts maximality and the
switch must happen at `ε = 0`.  A bundle whose switch layer is `ε ≥ 1` needs a genuinely
restrictive `Env` (`E(S_φ)`-envelopedness), which none of `cgw`, `cgn`, `cgc`, `cgg` has. -/

/-- The `2 × (ε + 3)` window `{3+ε, 4+ε} × [-ε-1, 1]`. -/
noncomputable def S₁e (ε : ℕ) : Finset (ℤ × ℤ) :=
  ({(3 : ℤ) + ε, (4 : ℤ) + ε} : Finset ℤ) ×ˢ Finset.Icc (-(ε : ℤ) - 1) 1
/-- `𝒯 ∖ ℓ'_𝒯 = {3+ε, 4+ε} × [-ε, 1]`. -/
noncomputable def Qe (ε : ℕ) : Finset (ℤ × ℤ) :=
  ({(3 : ℤ) + ε, (4 : ℤ) + ε} : Finset ℤ) ×ˢ Finset.Icc (-(ε : ℤ)) 1
/-- The seed `{(3+ε, 1)}`. -/
def Be (ε : ℕ) : Finset (ℤ × ℤ) := {((3 : ℤ) + ε, (1 : ℤ))}

theorem mem_S₁e {ε : ℕ} {z : ℤ × ℤ} :
    z ∈ S₁e ε ↔ (3 + (ε : ℤ) ≤ z.1 ∧ z.1 ≤ 4 + ε) ∧ (-(ε : ℤ) - 1 ≤ z.2 ∧ z.2 ≤ 1) := by
  simp only [S₁e, Finset.mem_product, Finset.mem_insert, Finset.mem_singleton, Finset.mem_Icc]
  omega

theorem mem_Qe {ε : ℕ} {z : ℤ × ℤ} :
    z ∈ Qe ε ↔ (3 + (ε : ℤ) ≤ z.1 ∧ z.1 ≤ 4 + ε) ∧ (-(ε : ℤ) ≤ z.2 ∧ z.2 ≤ 1) := by
  simp only [Qe, Finset.mem_product, Finset.mem_insert, Finset.mem_singleton, Finset.mem_Icc]
  omega

/-- A real box is convex. -/
theorem convex_box (x₀ x₁ y₀ y₁ : ℝ) :
    Convex ℝ {q : ℝ × ℝ | x₀ ≤ q.1 ∧ q.1 ≤ x₁ ∧ y₀ ≤ q.2 ∧ q.2 ≤ y₁} := by
  intro u hu v hv a b ha hb hab
  obtain ⟨hu1, hu2, hu3, hu4⟩ := hu
  obtain ⟨hv1, hv2, hv3, hv4⟩ := hv
  simp only [Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul]
  have e1 := mul_le_mul_of_nonneg_left hu1 ha
  have e2 := mul_le_mul_of_nonneg_left hv1 hb
  have e3 := mul_le_mul_of_nonneg_left hu2 ha
  have e4 := mul_le_mul_of_nonneg_left hv2 hb
  have e5 := mul_le_mul_of_nonneg_left hu3 ha
  have e6 := mul_le_mul_of_nonneg_left hv3 hb
  have e7 := mul_le_mul_of_nonneg_left hu4 ha
  have e8 := mul_le_mul_of_nonneg_left hv4 hb
  have hx₀ : a * x₀ + b * x₀ = x₀ := by rw [← add_mul, hab, one_mul]
  have hx₁ : a * x₁ + b * x₁ = x₁ := by rw [← add_mul, hab, one_mul]
  have hy₀ : a * y₀ + b * y₀ = y₀ := by rw [← add_mul, hab, one_mul]
  have hy₁ : a * y₁ + b * y₁ = y₁ := by rw [← add_mul, hab, one_mul]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

/-- An integer box (given by its membership predicate) is lattice-convex. -/
theorem latticeConvex_of_box {W : Finset (ℤ × ℤ)} {x₀ x₁ y₀ y₁ : ℤ}
    (hW : ∀ z, z ∈ W ↔ (x₀ ≤ z.1 ∧ z.1 ≤ x₁) ∧ (y₀ ≤ z.2 ∧ z.2 ≤ y₁)) : LatticeConvex W := by
  intro z hz
  have hsub : Conv W ⊆
      {q : ℝ × ℝ | (x₀ : ℝ) ≤ q.1 ∧ q.1 ≤ x₁ ∧ (y₀ : ℝ) ≤ q.2 ∧ q.2 ≤ y₁} := by
    apply convexHull_min _ (convex_box _ _ _ _)
    rintro _ ⟨w, hw, rfl⟩
    rw [Finset.mem_coe, hW] at hw
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hw
    simp only [Set.mem_ofPred_eq, toReal]
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2, by exact_mod_cast h3,
      by exact_mod_cast h4⟩
  have hz' := hsub hz
  simp only [Set.mem_ofPred_eq, toReal] at hz'
  obtain ⟨h1, h2, h3, h4⟩ := hz'
  rw [hW]
  exact ⟨⟨by exact_mod_cast h1, by exact_mod_cast h2⟩,
    by exact_mod_cast h3, by exact_mod_cast h4⟩

/-- `𝒯_ε` is `ξ`-generating: every vertex has a horizontal partner in its row. -/
theorem isGeneratingSet_S₁e (ε : ℕ) : IsGeneratingSet ξg (S₁e ε) := by
  refine ⟨⟨((3 : ℤ) + ε, (1 : ℤ)),
      mem_S₁e.mpr (by simp only; omega)⟩,
    latticeConvex_of_box (fun _ => mem_S₁e), ?_⟩
  intro a ha _
  refine ⟨ha, ?_⟩
  intro x hx y hy hagr
  rw [mem_S₁e] at ha
  have ha' : ((7 + 2 * (ε : ℤ) - a.1, a.2) : ℤ × ℤ) ∈ (S₁e ε).erase a := by
    rw [Finset.mem_erase, mem_S₁e]
    refine ⟨?_, by simp only; omega, by simp only; omega⟩
    intro h
    have := congrArg Prod.fst h
    simp only at this
    omega
  have h := hagr _ ha'
  obtain ⟨u, hu1, hu2⟩ := orbit_pair hx a (7 + 2 * (ε : ℤ) - a.1, a.2)
  obtain ⟨u', hu1', hu2'⟩ := orbit_pair hy a (7 + 2 * (ε : ℤ) - a.1, a.2)
  rw [hu2, hu2'] at h
  rw [hu1, hu1']
  simp only at h
  omega

/-- **All eleven conjuncts of `exists_case2_window` hold on `cgg` at every `ε`.**  Stated
verbatim (with `cg := cgg`, `ξ := ξg`, `p := pg`); no hypotheses.  `window_model_gen` is the
`ε = 0` instance with the same witnesses.  Witnesses after the eleventh conjunct: `B := Q`,
`pw := 1`, `e := false` (see §1b). -/
theorem window_model_gen_all (ε : ℕ) :
    ∃ (S₁ Q B : Finset (ℤ × ℤ)) (τ : ℤ) (pw : ℕ) (R : Set (ℤ × ℤ)),
      IsGeneratingSet ξg S₁ ∧
      Q ⊆ S₁ ∧
      (∃ (n : ℝ × ℝ) (cmax : ℝ),
        n ≠ 0 ∧
        inner2 n cgg.vJ = 0 ∧
        (∀ z ∈ S₁, inner2 n z ≤ cmax) ∧
        (Nivat.R2.face S₁ n cmax).Nonempty ∧
        Q = S₁.filter fun z => inner2 n z < cmax) ∧
      (∀ g ∈ S₁, g ∉ Q → ∀ t : ℤ, τ ≤ t →
        t • cgg.vJ + g ∈ cgg.toChainData.shellInf (ε + 1) ∧
        t • cgg.vJ + g ∉ cgg.toChainData.shellInf ε) ∧
      P ξg S₁ ≤ P ξg Q + pw ∧
      (∀ g ∈ B, ∀ i : ℕ, i < pw → g + (i : ℤ) • cgg.vJ ∈ Q) ∧
      R ⊆ cgg.toChainData.shellInf ε ∧
      Colle41.IsRegion R pg cgg.vJ ∧
      (∀ t : ℤ, τ ≤ t → ∀ z ∈ Q,
        t • cgg.vJ + z ∈ R ∧ t • cgg.vJ + z + (1 : ℤ) • pg ∈ R) ∧
      (B.Nonempty ∧ ∃ b, ∀ z ∈ S₁, b + z ∈ R) ∧
      (∃ e : Bool, pw = (L1Data.topFace e cgg.vJ S₁).card - 1 ∧
        B = L1Data.maxB (L1Data.derivedQ e cgg.vJ S₁) cgg.vJ pw) := by
  refine ⟨S₁e ε, Qe ε, Qe ε, 10, 1, cgg.toChainData.shellInf ε, isGeneratingSet_S₁e ε, ?_, ?_,
    ?_, ?_, ?_, subset_rfl, isRegion_shellInf_cgg ε, ?_, ?_, ?_⟩
  · -- `Q ⊆ S₁`
    intro z hz
    rw [mem_Qe] at hz
    rw [mem_S₁e]
    omega
  · -- the edge: normal `(0,-1) = toReal (-n_J)`, level `ε + 1`
    refine ⟨((0 : ℝ), (-1 : ℝ)), (ε : ℝ) + 1, ?_, ?_, ?_, ?_, ?_⟩
    · simp [Prod.ext_iff]
    · show inner2 _ vJg = 0
      simp [inner2, vJg]
    · intro z hz
      rw [mem_S₁e] at hz
      have : (-(ε : ℝ) - 1) ≤ z.2 := by exact_mod_cast hz.2.1
      simp only [inner2]
      linarith
    · refine ⟨((3 : ℤ) + ε, -(ε : ℤ) - 1), ?_⟩
      rw [Nivat.R2.mem_face]
      refine ⟨mem_S₁e.mpr (by simp only; omega), ?_⟩
      simp only [inner2]
      push_cast
      ring
    · ext z
      rw [Finset.mem_filter, mem_Qe, mem_S₁e]
      simp only [inner2]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨⟨h1, by omega, by omega⟩, ?_⟩
        have : (-(ε : ℝ)) ≤ z.2 := by exact_mod_cast h2.1
        linarith
      · rintro ⟨⟨h1, h2, h3⟩, h4⟩
        have : (-(ε : ℝ) - 1) < z.2 := by linarith
        have : (-(ε : ℤ) - 1) < z.2 := by exact_mod_cast this
        exact ⟨h1, by omega, h3⟩
  · -- `hface`: the row `y = -ε-1`, slid far enough right, is in layer `ε+1` and not in `ε`
    intro g hg hgQ t ht
    rw [mem_S₁e] at hg
    rw [mem_Qe] at hgQ
    have hg2 : g.2 = -(ε : ℤ) - 1 := by omega
    rw [smul_vJ_add_cgg]
    constructor
    · rw [mem_shellInf_cgg]
      simp only
      push_cast
      omega
    · rw [mem_shellInf_cgg]
      simp only
      omega
  · -- the deficit: `P ξ 𝒯 ≤ 2 ≤ P ξ Q + 1`
    have hQ : 1 ≤ P ξg (Qe ε) := by
      have hfin : (patterns ξg (Qe ε)).Finite := by
        refine Set.Finite.subset
          (Set.toFinite {pattern ξg (Qe ε) (0, 0), pattern ξg (Qe ε) (1, 0)}) ?_
        rintro _ ⟨u, rfl⟩
        have hu := pattern_ξg (Qe ε) u
        rcases (show u.1 % 2 = 0 ∨ u.1 % 2 = 1 by omega) with h | h <;> rw [h] at hu <;>
          rw [hu] <;> simp
      exact (Set.ncard_pos hfin).mpr ⟨_, ⟨(0, 0), rfl⟩⟩
    exact (P_ξg_le_two _).trans (by omega)
  · -- `hline`: `pw = 1`, so this is `B = Q ⊆ Q`
    intro g hg i hi
    have : i = 0 := by omega
    subst this
    simpa using hg
  · -- `hQR`
    intro t ht z hz
    rw [mem_Qe] at hz
    rw [smul_vJ_add_cgg]
    constructor
    · rw [mem_shellInf_cgg]
      simp only
      omega
    · rw [mem_shellInf_cgg]
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, pg, smul_eq_mul,
        one_mul]
      omega
  · -- `hbase`: `B = Q ∋ (3+ε,1)`, and `(3+ε,1) + 𝒯_ε ⊆ Â_∞^{(ε)}`
    refine ⟨⟨((3 : ℤ) + ε, (1 : ℤ)), mem_Qe.mpr (by simp only; omega)⟩, ((3 : ℤ) + ε, (1 : ℤ)),
      ?_⟩
    intro z hz
    rw [mem_S₁e] at hz
    rw [mem_shellInf_cgg]
    simp only [Prod.fst_add, Prod.snd_add]
    omega
  · -- the eleventh conjunct: `e = false`, bottom row `{3+ε,4+ε} × {-ε-1}` has card 2
    refine ⟨false, ?_, ?_⟩
    · rw [cgg_vJ, card_topFace_false_box (fun z => mem_S₁e) (by omega) (by omega)]
      have : (4 + (ε : ℤ) + 1 - (3 + ε)).toNat = 2 := by omega
      rw [this]
    · rw [cgg_vJ, derivedQ_false_box (fun z => mem_S₁e) (by omega) (by omega), maxB_one]
      ext z
      rw [Finset.mem_filter, mem_S₁e, mem_Qe]
      omega

/-- **The binder `hshell_ε` is unsatisfiable on `cgg` for every `ε ≥ 1`**, for every
`ϑ ∈ X_ξ` and every `K`.  `Â_∞^{(ε)}` contains both `(ε+K, -ε)` (a row `< 0 ≤ K`, where
`T (K v_ℓ) x_per` carries the parity flip) and `(ε+K, K)` (row `K`, where it does not), while
every `ϑ ∈ X_ξ` is `z ↦ (u + z.1) % 2` with one `u` (`orbit_pair`).  Consequence: on `cgg`,
`exists_case2_window` has content only at `ε = 0`; `window_model_gen_all` at `ε ≥ 1` certifies
the conclusion on a bundle where the hypotheses cannot be met. -/
theorem not_hshell_of_pos {ε : ℕ} (hε : 1 ≤ ε) (K : ℕ) {ϑ : Config ℤ}
    (hϑ : ϑ ∈ orbitClosure ξg) :
    ¬ (∀ z ∈ cgg.toChainData.shellInf ε, ϑ z = T ((K : ℤ) • vlg) xperg z) := by
  intro h
  have h1 := h (((ε : ℤ) + K, -(ε : ℤ)))
    (mem_shellInf_cgg.mpr (by refine ⟨?_, ?_, ?_⟩ <;> simp only <;> omega))
  have h2 := h (((ε : ℤ) + K, (K : ℤ)))
    (mem_shellInf_cgg.mpr (by refine ⟨?_, ?_, ?_⟩ <;> simp only <;> omega))
  obtain ⟨u, hu1, hu2⟩ := orbit_pair hϑ ((ε : ℤ) + K, -(ε : ℤ)) ((ε : ℤ) + K, (K : ℤ))
  rw [hu1] at h1
  rw [hu2] at h2
  simp only [T, xperg, vlg, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul] at h1 h2
  split_ifs at h1 h2 <;> omega

end Gen

/-! ## §5 The shape, named — and the shape-match made non-vacuous

The file used to carry three `*_shape_matches_target` theorems, each **with binders** (`hξ`,
`hsh`, …) and each proved by `type_of% (exists_case2_window …)` unifying with a model; as
propositions they were vacuous and all they certified was one successful unification inside
their own elaboration.  They were deleted on 2026-09-19 (integrator's ruling) in favour of a
statement with **no hypotheses at all**:

* `WindowConclusion cg ε` is the eleven-conjunct conclusion of `exists_case2_window`, copied
  verbatim, as a `Prop`-valued `def` over an *arbitrary* bundle.
* `target_type_eq` says that the **type of the live declaration** `exists_case2_window`
  — the very `sorry` C still owes — is literally `∀ binders, WindowConclusion cg ε`, by `rfl`.
  It quantifies over nothing, mentions no proof of `exists_case2_window`, and so has neither
  `sorryAx` nor an uninhabited binder to hide behind.  If someone edits the target, this line
  stops compiling.
* `windowConclusion_cgg` / `windowConclusion_cgc_one` are the models of §2–§4 restated against
  that name.

⚠ **Confidence, not progress.**  `cgg ⊨ WindowConclusion cgg ε` for every `ε` shows the shape
C must hit is *satisfiable* and does not degenerate (`P ξ W ≤ 2`, not `0`).  It does not
touch `sorry TOTAL` (3 as of 2026-09-19; C's own `sorry` is one of them), and `exists_case2_window` must hold for **every** minimal
counterexample bundle, not for one model.  What it buys is that "the conclusion" now has a
name that is kernel-identified with the target, so a future proof of `exists_case2_window`
can be written as `WindowConclusion cg ε` and checked against `cgg` as it goes. -/

/-- The eleven-conjunct conclusion of `exists_case2_window` at `cg`, `ε`, verbatim.  `ϑ`, `K`,
`Sgen` and the binders do not occur in it, which `target_type_eq` makes a kernel fact. -/
def WindowConclusion (cg : ChainDataGeom ξ xper vl p S gen) (ε : ℕ) : Prop :=
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
      B = L1Data.maxB (L1Data.derivedQ e cg.vJ S₁) cg.vJ pw)

/-- **The live target is `WindowConclusion`, as a kernel fact with no hypotheses.**  Left side:
the type of `ColleReg.exists_case2_window` as it stands in `RegionSteps.lean` (not its proof —
`type_of%` never touches the `sorry` body, so `#print axioms` is clean).  Right side: its
binders (ten since 2026-09-19: `hSgen`/`hdef` were threaded in the same round as the eleventh
conjunct) followed by `WindowConclusion cg ε`.  Proved by `rfl`. -/
theorem target_type_eq :
    type_of% @exists_case2_window =
      (∀ {ξ xper ϑ : Config ℤ} {vl p ℓ : ℤ × ℤ} {S : Finset (ℤ × ℤ)} {gen : ℤ × ℤ}
        (cg : ChainDataGeom ξ xper vl p S gen),
        IsMinimalCounterexample ξ →
        IsGeneratingSet ξ S →
        ϑ ∈ orbitClosure ξ →
        IsLatticeConvexRegion (⋃ i, cg.toChainData.Ahat i) →
        (⋃ i, cg.toChainData.Ahat i).Nonempty →
        ∀ {Sgen : Finset (ℤ × ℤ)}, IsGeneratingSet ξ Sgen →
        (∀ (n : ℝ × ℝ) (cmax cmin : ℝ),
          (∀ z ∈ Sgen, inner2 n z ≤ cmax) → (Nivat.R2.face Sgen n cmax).Nonempty →
          (∀ z ∈ Sgen, cmin ≤ inner2 n z) → (Nivat.R2.face Sgen n cmin).Nonempty →
            P ξ Sgen - P ξ (Sgen.filter fun z => inner2 n z < cmax) ≤
              (Nivat.R2.face Sgen n cmax).card - 1 ∧
            P ξ Sgen - P ξ (Sgen.filter fun z => cmin < inner2 n z) ≤
              (Nivat.R2.face Sgen n cmin).card - 1) →
        ∀ {K ε : ℕ},
        (∀ z ∈ cg.toChainData.shellInf ε, ϑ z = T ((K : ℤ) • vl) xper z) →
        ¬ (∀ z ∈ cg.toChainData.shellInf (ε + 1), ϑ z = T ((K : ℤ) • vl) xper z) →
        Primitive vl →
        det p vl = 0 →
        ℓ ∈ Colle45.NonExpansiveLine ξ →
        Colle45.IsOneSidedNonexpansive ξ ℓ →
        Colle45.IsOneSidedNonexpansive ξ (-ℓ) →
        Nivat.LE2.dot ℓ vl = 0 →
        WindowConclusion cg ε) :=
  rfl

/-- `cgg` satisfies the conclusion at every `ε`, no hypotheses (§4 restated). -/
theorem windowConclusion_cgg (ε : ℕ) : WindowConclusion Gen.cgg ε :=
  Gen.window_model_gen_all ε

/-- `cgc` satisfies the conclusion at `ε = 1`, no hypotheses (§2 restated; recall `P etaC W = 0`
there, so this instance is degenerate where `cgg` is not). -/
theorem windowConclusion_cgc_one : WindowConclusion Nivat.ShellConvex.cgc 1 :=
  Model.window_model

/-! ## §6 What `cgg` can and cannot carry **jointly**

`Gen.window_model_gen_all` discharges the eleven-conjunct *conclusion* at every `ε`, and
§3 discharges every *binder* of `exists_case2_window` except `hξ` at `ε = 0`.  This section
asks the complementary question the integrator posed: on the same bundle, which of the
neighbouring obligations — the ones `region_periods_and_rays` (`RegionSteps.lean:2074`) and
Claim 4.11's producer (`RegionClaim411.exists_case2_window_core`, `:1002`) also demand — hold
*at the same time*?  Everything below is at the kernel; the labels in the docstrings say what
each result does and does not mean.

Summary (kernel facts, each a theorem below):

| obligation | on `cgg` | witness |
|---|---|---|
| `hp_per : p ∈ Per xper` | **fails**, for **every** `p` with `dot nJ p ≠ 0` | `not_hp_per_cgg` |
| `hxper_dp : DoublyPeriodic xper` | **fails** — all periods of `x_per` are horizontal | `not_doublyPeriodic_xperg` |
| `hagree` on all of `Â_∞` (`K = 0`, `ϑ = ξ`) | **holds** | `hagree_cgg` |
| `hc_grow : ∀ i, B i ⊂ B (i+1)` | **holds** | `hc_grow_cgg` |
| `hc_env : Env = EnvOf S` | **fails** — `Env := fun _ => True` | `not_hc_env_cgg` |
| `EdgeJ1Data`'s `prev_mem : a₀ - v ∈ Â_∞` at the `ℓ_J`-vertex | **fails** for `a₀ = 0` | `not_prev_mem_cgg` |
| `hqgt ∧ hrun` on `S_φ = Sg` | run length is `0` — `Sg` has one point per `n_J`-level | `not_hqgt_hrun_Sg` |
| `hqgt ∧ hrun` on `S₁g` (the model window) | **holds** | `hqgt_hrun_S₁g` |

So the honest map is: `cgg` is a **complete** model of `exists_case2_window`'s binders and
conclusion, and of the two chain-growth binders of `region_periods_and_rays` (`hagree`,
`hc_grow`), but **not** of three things that sit *upstream* of C's `sorry`:

* **`hp_per` / `hxper_dp`** — and this one was found by the kernel, not by me: I had written
  `pg ∈ Per xperg` as a theorem and `omega` returned the counterexample.  `x_per = (x + [y<0])
  mod 2` has only horizontal periods (`per_xperg_snd_eq_zero`), while `ChainDataGeom.dot_nJ_p`
  needs `p` transverse to `ℓ_J = {y = 0}`.  **No `p` can serve both**, so `cgg`'s `hshell`
  agreement is with an `x_per` that lacks the transverse period Collé's always has.  Everything
  in the tree that consumes `hp_per` — `pos_pw_of_conclusion` (§1), `Claim411.periodOn_shellInf_p`,
  `not_periodOn_shellInf_succ_p` — is silent on `cgg`.  ⚠ Read: the `0 < pw` forcing of §1
  item 1 does **not** apply to `cgg`; the model's `pw = 1 > 0` is a choice, not a consequence.
* **`hc_env`** — `region_periods_and_rays` pins `Env` to `EnvOf S`, the Definition 3.2
  envelope.  `cgg` has `Env := fun _ => True`, which is what lets `maximalHat` make `Â_∞` the
  whole cone.  This is the same reason `not_hshell_of_pos` holds (§4).  ⚠ Read: `cgg`
  models the *leaf*, not the *caller*; nothing here says the leaf's conclusion is reachable
  from a genuine `EnvOf` chain.
* **`prev_mem`** — Cconv's `EdgeJ1Data` (in `tmp/edge_kcprime.lean` today, headed for
  `RegionConvex.lean`) asks for a second lattice point of the `ℓ_{J-1}`-edge one `v_ℓ`-step
  behind the `ℓ_J`-vertex.  `cgg`'s cone `{0 ≤ y ≤ x}` has its `ℓ_J`-vertex at `0`, and
  `0 - v_ℓ = (-1, 1) ∉ Â_∞`.  This is **not** a defect of the conjuncts: `cgg` has `r = 0`
  (`a = a' = 0`), its `ℓ_J`-face is the single point `0`, and the `ℓ_{J-1}`-edge is the ray
  `{(t, t)}`, whose lattice points all lie on the *other* side of `0`.  A bundle with a genuine
  `ℓ_J`-edge (`cgwA`, `ShellMink.lean:1824`) is where `prev_mem` should be tested; `cgg` was
  never built for it.

The `hqgt`/`hrun` row is the one that matters for C's producer.  `exists_case2_window_core`
takes `W` (Lemma 2.4's `𝒮`), an `n_J`-minimal `a₀ ∈ W`, and a `q` **strictly above** `a₀`
whose forward `v_J`-run of length `|W ∩ ℓ_{a₀}| - 1` stays in `W`.  On `Sg = {0, (-1,1)}` no
such `q` exists with a nontrivial run — but the run length is `|{0}| - 1 = 0`, so `hrun` is
vacuous and `hqgt` alone is satisfiable by `q = (-1,1)`; what **fails** is the stronger
`hqW ∧ hqgt ∧ (0 < run length)` that would make `B` nonempty by `hrun`.  On the model
window `S₁g` (`{3,4} × {-1,0,1}`) all of `hqW`, `hqgt`, `hrun` hold with `q = (3, 0)` and run
length `1`.  Read: the producer's inputs are **satisfiable on the leaf's own window**, and
the `S_φ` of the bundle is too small to be that window — which is exactly why
`exists_case2_window` takes a separate `Sgen`. -/

namespace Gen

/-- **Every period of `x_per` is horizontal.**  Compare `xperg` at `0` and at `(0,-1)`: the
`y < 0` indicator differs between them, so a period `h` with `h.2 ≠ 0` would need `h.1` to be
both even and odd. -/
theorem per_xperg_snd_eq_zero {h : ℤ × ℤ} (hh : h ∈ Per xperg) : h.2 = 0 := by
  rw [mem_Per_iff] at hh
  have e0 := congrFun hh ((0 : ℤ), (0 : ℤ))
  have e1 := congrFun hh ((0 : ℤ), (-1 : ℤ))
  simp only [T, xperg, Prod.fst_add, Prod.snd_add, zero_add] at e0 e1
  split_ifs at e0 e1 <;> omega

/-- **`hp_per` fails on `cgg`, and unrepairably so.**  `region_periods_and_rays`
(`RegionSteps.lean:2137`) needs `p ∈ Per xper` while `ChainDataGeom` needs `dot nJ p ≠ 0`
(`ChainGeom.lean:138`); on `cgg` no `p` satisfies both, because every period of `x_per` is
horizontal and `n_J = (0,1)`.  ⚠ Read: `cgg`'s agreement `ϑ = x_per` on `Â_∞` (`hshell_zero`)
is with an `x_per` that has **no** period transverse to `ℓ_J` — Collé's `x_per` always does.
So `cgg` models the leaf's binders, but not the period structure its caller lives in;
`pos_pw_of_conclusion` (§1) and `Claim411.periodOn_shellInf_p` do not apply to it. -/
theorem not_hp_per_cgg (q : ℤ × ℤ) (hq : dot nJg q ≠ 0) : q ∉ Per xperg := by
  intro hper
  apply hq
  rw [dot_nJg]
  exact per_xperg_snd_eq_zero hper

theorem not_pg_mem_Per_xperg : pg ∉ Per xperg :=
  not_hp_per_cgg pg (by simp [dot_nJg, pg])

/-- **`hxper_dp` fails on `cgg`**: two horizontal vectors have determinant `0`. -/
theorem not_doublyPeriodic_xperg : ¬ DoublyPeriodic xperg := by
  rintro ⟨u, hu, v, hv, hdet⟩
  apply hdet
  have hu2 := per_xperg_snd_eq_zero hu
  have hv2 := per_xperg_snd_eq_zero hv
  simp [det, hu2, hv2]

/-- **`hagree` on `cgg`** at `K = 0`, `ϑ = ξ`: `ξ = x_per` on all of `Â_∞ = {0 ≤ y ≤ x}`. -/
theorem hagree_cgg :
    ∀ z ∈ ⋃ i, cgg.toChainData.Ahat i, ξg z = T (((0 : ℕ) : ℤ) • vlg) xperg z := by
  intro z hz
  rw [show (⋃ i, cgg.toChainData.Ahat i) = Kg from iUnion_Ag] at hz
  have hnn : ¬ (z.2 < 0) := by have := hz.1; omega
  simp [T, ξg, xperg, hnn]

/-- **`hc_grow` on `cgg`.**  `B i = {0 ≤ y ≤ x, x + y ≤ i}`; `(i+1, 0)` is new at stage `i+1`. -/
theorem hc_grow_cgg : ∀ i, cgg.toChainData.B i ⊂ cgg.toChainData.B (i + 1) := by
  intro i
  rw [Set.ssubset_def]
  refine ⟨fun z hz => ?_, fun h => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := hz
    exact ⟨h1, h2, by push_cast; omega⟩
  · have hmem : (((i : ℤ) + 1, (0 : ℤ)) : ℤ × ℤ) ∈ cgg.toChainData.B (i + 1) := by
      refine ⟨le_rfl, ?_, ?_⟩ <;> simp only <;> push_cast <;> omega
    obtain ⟨-, -, h3⟩ := h hmem
    simp only at h3
    omega

/-- A two-point set with a lattice gap is not a lattice-convex region: any convex `C` through
`toReal 0` and `toReal (2,0)` contains `toReal (1,0)`. -/
theorem not_isLatticeConvexRegion_pair :
    ¬ IsLatticeConvexRegion ({0, ((2 : ℤ), (0 : ℤ))} : Set (ℤ × ℤ)) := by
  rintro ⟨C, hC, -, hR⟩
  have h0 : toReal (0 : ℤ × ℤ) ∈ C := by
    have : (0 : ℤ × ℤ) ∈ ({0, ((2 : ℤ), (0 : ℤ))} : Set (ℤ × ℤ)) := by simp
    rwa [hR] at this
  have h2 : toReal (((2 : ℤ), (0 : ℤ)) : ℤ × ℤ) ∈ C := by
    have : (((2 : ℤ), (0 : ℤ)) : ℤ × ℤ) ∈ ({0, ((2 : ℤ), (0 : ℤ))} : Set (ℤ × ℤ)) := by simp
    rwa [hR] at this
  have hmid := hC h0 h2 (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num)
  have he : (1 / 2 : ℝ) • toReal (0 : ℤ × ℤ) + (1 / 2 : ℝ) • toReal (((2 : ℤ), (0 : ℤ)) : ℤ × ℤ)
      = toReal (((1 : ℤ), (0 : ℤ)) : ℤ × ℤ) := by
    ext <;> simp [toReal]
  rw [he] at hmid
  have : (((1 : ℤ), (0 : ℤ)) : ℤ × ℤ) ∈ ({0, ((2 : ℤ), (0 : ℤ))} : Set (ℤ × ℤ)) := by
    rw [hR]; exact hmid
  simp [Prod.ext_iff] at this

/-- **`hc_env` fails on `cgg`.**  `region_periods_and_rays` (`RegionSteps.lean:2134`) pins
`cg.Env = EnvOf S`, and `EnvOf S T` (`LatticeEdges.lean:2433`, `= Enveloped S T`) begins with
`IsLatticeConvexRegion T` (`WeaklyEnveloped`, `:624`).  `cgg.Env = fun _ => True` accepts the
non-region `{0, (2,0)}`.  ⚠ Read: `cgg` is a model of the **leaf** `exists_case2_window`, not
of its **caller**; this row is what separates the two. -/
theorem not_hc_env_cgg : cgg.toChainData.Env ≠ Nivat.LE2.EnvOf (Sg : Set (ℤ × ℤ)) := by
  intro h
  have h1 : cgg.toChainData.Env ({0, ((2 : ℤ), (0 : ℤ))} : Set (ℤ × ℤ)) := trivial
  rw [h] at h1
  exact not_isLatticeConvexRegion_pair (h1 : Nivat.LE2.Enveloped _ _).1.1

/-- **`prev_mem` fails on `cgg`** at the `ℓ_J`-vertex `a₀ = 0`: `0 - v_ℓ = (-1, 1)` has `y > x`.
This is the field of Cconv's `EdgeJ1Data` (`tmp/edge_kcprime.lean:32`); `cgg` has `r = 0` and
its `ℓ_J`-face is a single point, so no `EdgeJ1Data cgg.Â_∞ vlg nJg 0` can have `a₀ = 0`. -/
theorem not_prev_mem_cgg : (0 : ℤ × ℤ) - vlg ∉ ⋃ i, cgg.toChainData.Ahat i := by
  rw [show (⋃ i, cgg.toChainData.Ahat i) = Kg from iUnion_Ag, mem_Kg]
  simp [vlg]

/-- The `ℓ_J`-vertex of `cgg` is unique: `0` is the only point of `Â_∞` on `ℓ_J = {y = 0}`
with the minimal `n_{J-1}`-value, so `a₀ = 0` is forced for any `EdgeJ1Data` on this bundle
whose `a₀` is the `ℓ_J`-vertex in the sense of `support` with `nJ1 = (1, -1)`. -/
theorem vertex_cgg_unique {a₀ : ℤ × ℤ} (ha₀ : a₀ ∈ ⋃ i, cgg.toChainData.Ahat i)
    (hon : dot nJg a₀ = 0)
    (hsup : ∀ g ∈ ⋃ i, cgg.toChainData.Ahat i, dot nLg a₀ ≤ dot nLg g) : a₀ = 0 := by
  rw [show (⋃ i, cgg.toChainData.Ahat i) = Kg from iUnion_Ag] at ha₀ hsup
  rw [dot_nJg] at hon
  have h0 := hsup 0 (mem_Kg.mpr ⟨le_rfl, le_rfl⟩)
  rw [dot_nLg, dot_nLg] at h0
  obtain ⟨h1, h2⟩ := mem_Kg.mp ha₀
  ext <;> simp only [Prod.fst_zero, Prod.snd_zero] at h0 ⊢ <;> omega

/-- **`hqgt` with a nonempty run fails on `S_φ = Sg`.**  The `n_J`-minimal level of `Sg` is
`{0}`, of cardinality `1`, so the run length `|Sg ∩ ℓ_{a₀}| - 1 = 0`; no `q ∈ Sg` strictly
above `a₀ = 0` carries a run of positive length.  Stated as: for every `q ∈ Sg` above the
minimum, the run-length bound is `0`. -/
theorem not_hqgt_hrun_Sg :
    (Sg.filter fun w => dot nJg w = dot nJg 0).card - 1 = 0 := by
  have : Sg.filter (fun w => dot nJg w = dot nJg 0) = {0} := by
    ext w
    rw [Finset.mem_filter, mem_Sg, Finset.mem_singleton]
    simp only [dot_nJg]
    constructor
    · rintro ⟨h | h, hw⟩
      · exact h
      · subst h; simp at hw
    · rintro rfl; exact ⟨Or.inl rfl, rfl⟩
  rw [this, Finset.card_singleton]

/-- **`hqgt ∧ hrun` hold on the model window `S₁g`** with `a₀ = (3, -1)`, `q = (3, 0)`:
the bottom row `{3,4} × {-1}` has two points, so the run length is `1`, and `(3,0) + 0•v_J ∈ S₁g`. -/
theorem hqgt_hrun_S₁g :
    ((3 : ℤ), (-1 : ℤ)) ∈ S₁g ∧
    (∀ w ∈ S₁g, dot nJg ((3 : ℤ), (-1 : ℤ)) ≤ dot nJg w) ∧
    ((3 : ℤ), (0 : ℤ)) ∈ S₁g ∧
    dot nJg ((3 : ℤ), (-1 : ℤ)) < dot nJg ((3 : ℤ), (0 : ℤ)) ∧
    (∀ i : ℕ, i < (S₁g.filter fun w => dot nJg w = dot nJg ((3 : ℤ), (-1 : ℤ))).card - 1 →
      ((3 : ℤ), (0 : ℤ)) + (i : ℤ) • vJg ∈ S₁g) := by
  refine ⟨mem_S₁g.mpr (by norm_num), ?_, mem_S₁g.mpr (by norm_num), by simp [dot_nJg], ?_⟩
  · intro w hw
    rw [mem_S₁g] at hw
    simp only [dot_nJg]
    omega
  · intro i hi
    have hrow : S₁g.filter (fun w => dot nJg w = dot nJg ((3 : ℤ), (-1 : ℤ)))
        = ({3, 4} : Finset ℤ) ×ˢ ({-1} : Finset ℤ) := by
      ext w
      rw [Finset.mem_filter, mem_S₁g, Finset.mem_product, Finset.mem_insert,
        Finset.mem_singleton, Finset.mem_singleton]
      simp only [dot_nJg]
      omega
    rw [hrow, Finset.card_product, Finset.card_singleton, Finset.card_pair (by norm_num)] at hi
    have : i = 0 := by omega
    subst this
    rw [mem_S₁g]
    norm_num [vJg]

end Gen

/-! ## §7 `exists_case2_run` measured on `cgg` (2026-09-19, after the wiring)

`exists_case2_window` was wired on 2026-09-19 ~10:50 to `Claim411.exists_case2_window_maxB_weak_of_run`
plus one new statement, `ColleReg.exists_case2_run` (Collé's (4.1) run: a `q ∈ Sgen` strictly above
the `n_J`-minimal face carrying `|face| - 1` consecutive `v_J`-points).  The integrator asked for
that hypothesis to be measured on `cgg`, the one bundle in the tree with a generating `S_φ`.

**Status of the target at the time of writing (shadow-compiled off disk, `tmp/cprobe_run_receipt.lean`):**
`exists_case2_run` is **already closed** — its body is `C11Bridge.exists_run`
(`C11Bridge.lean:126`), and `#print axioms` on both is `[propext, Classical.choice, Quot.sound]`.
So a refutation on any legitimate instance is impossible; what a finite-set measurement can still
do is (i) confirm the conclusion on a concrete `Sgen` as a sanity check on the *statement*, and
(ii) say whether `cgg` is an instance the statement is about at all.  Both are done below.

### General facts (arbitrary `n_J`, `v_J`, `Sgen`)

* `run_of_face_card_le_one` — with a bottom face of `≤ 1` point the run condition is **vacuous**,
  so the conclusion is exactly "some `q ∈ Sgen` lies strictly above `a₀`".
* `exists_above_of_face_card_lt` — such a `q` exists as soon as the face is a **proper** subset
  of `Sgen`.
* `run_trivial_of_face_card_le_one` — the two combined: face `≤ 1`, `Sgen` with `≥ 2` points
  ⟹ the conclusion holds outright.  This is the integrator's item 2, at the kernel.
* `not_run_of_flat` — the boundary: if `Sgen` lies in a single `n_J`-level, the conclusion is
  **false** for every run length, because `hqgt` cannot be met.  ⚠ Read: the "`≤ 1` case is
  trivial" statement needs `Sgen` not flat; under the live binders that is supplied (hand-read,
  **(c)**) by `C11Bridge.two_le_faces_vl` — a flat `Sgen` on a `v_J`-line has single-point
  `v_ℓ`-faces because `det v_ℓ v_J ≠ 0` — but this file does not prove that step.

### On `cgg`

* `run_cgg_Sg` — with `Sgen := S_φ = {0, (-1,1)}`, `a₀ := 0` (`n_J`-minimal, `nJ_min_Sg`): the
  conclusion **holds**, with `q = (-1,1)` and run length `|{0}| - 1 = 0` (`card_face_Sg`).  It is
  the vacuous case of `run_trivial_of_face_card_le_one`, nothing more.
* `run_cgg_S₁g` — with `Sgen := S₁g = {3,4} × {-1,0,1}`, `a₀ := (3,-1)`: the conclusion **holds**
  with `q = (3,0)` and run length `1` (§6's `hqgt_hrun_S₁g`, restated in the target's shape).
* **`cgg` is not an instance of the situation (4.1) is stated about**, for two independent
  kernel reasons, each a live binder of `exists_case2_run`:
  - `not_hdet_vl_cgg : det pg vlg ≠ 0` — the bundle's `p = (1,1)` is not parallel to its sweep
    direction `v_ℓ = (1,-1)`, so `hdet_vl` fails.
  - `not_isOneSidedNonexpansive_ξg : ∀ ℓ, ¬ IsOneSidedNonexpansive ξg ℓ` — `ξ = x mod 2` has
    **no** one-sided nonexpansive direction at all: `X_ξ` has two elements and they differ at
    every site, so no two distinct members agree on any half-plane (the half-plane always contains
    `0`).  Hence `hℓ_pos`, `hℓ_neg` fail for every `ℓ`, and (`not_mem_nonExpansiveLine_ξg`)
    `NonExpansiveLine ξg = ∅` so `hℓ_nel` fails too.  This is the same fact as "`ξg` is doubly
    periodic, hence not a counterexample", seen from Lemma 2.3's side.

So the honest reading of item 1 is: **no refutation, and none was possible** — the conclusion
holds on both finite sets tried, but `cgg` fails three of the six bi-oriented binders that were
threaded into `exists_case2_run` precisely so that (4.1) would have its Lemma 2.3 input.  A model
that has no nonexpansive direction cannot test a statement whose content is "both `v_ℓ`-faces
are edges".  The bundle that could test it would need a genuinely non-periodic `ξ` with
`±ℓ ∈ nexpd(ξ)`; none exists in the tree. -/

/-- With a bottom face of at most one point the run condition is vacuous. -/
theorem run_of_face_card_le_one {nJ vJ : ℤ × ℤ} {Sgen : Finset (ℤ × ℤ)} {a₀ : ℤ × ℤ}
    (hcard : (Sgen.filter fun w => dot nJ w = dot nJ a₀).card ≤ 1)
    {q : ℤ × ℤ} (hq : q ∈ Sgen) (hgt : dot nJ a₀ < dot nJ q) :
    ∃ q ∈ Sgen, dot nJ a₀ < dot nJ q ∧
      ∀ i : ℕ, i < (Sgen.filter fun w => dot nJ w = dot nJ a₀).card - 1 →
        q + (i : ℤ) • vJ ∈ Sgen :=
  ⟨q, hq, hgt, fun _ hi => absurd hi (by omega)⟩

/-- A point strictly above the `n_J`-minimal face exists iff the face is a proper subset. -/
theorem exists_above_of_face_card_lt {nJ : ℤ × ℤ} {Sgen : Finset (ℤ × ℤ)} {a₀ : ℤ × ℤ}
    (hmin : ∀ w ∈ Sgen, dot nJ a₀ ≤ dot nJ w)
    (hlt : (Sgen.filter fun w => dot nJ w = dot nJ a₀).card < Sgen.card) :
    ∃ q ∈ Sgen, dot nJ a₀ < dot nJ q := by
  obtain ⟨q, hq, hqn⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  refine ⟨q, hq, lt_of_le_of_ne (hmin q hq) fun h => ?_⟩
  exact hqn (Finset.mem_filter.mpr ⟨hq, h.symm⟩)

/-- **Item 2, at the kernel**: bottom face `≤ 1` and `Sgen` not a single point ⟹ the conclusion
of `exists_case2_run` holds outright. -/
theorem run_trivial_of_face_card_le_one {nJ vJ : ℤ × ℤ} {Sgen : Finset (ℤ × ℤ)} {a₀ : ℤ × ℤ}
    (hmin : ∀ w ∈ Sgen, dot nJ a₀ ≤ dot nJ w)
    (hcard : (Sgen.filter fun w => dot nJ w = dot nJ a₀).card ≤ 1)
    (h2 : 2 ≤ Sgen.card) :
    ∃ q ∈ Sgen, dot nJ a₀ < dot nJ q ∧
      ∀ i : ℕ, i < (Sgen.filter fun w => dot nJ w = dot nJ a₀).card - 1 →
        q + (i : ℤ) • vJ ∈ Sgen := by
  obtain ⟨q, hq, hgt⟩ := exists_above_of_face_card_lt hmin (by omega)
  exact run_of_face_card_le_one hcard hq hgt

/-- **The boundary**: a flat `Sgen` (one `n_J`-level) never satisfies the conclusion. -/
theorem not_run_of_flat {nJ vJ : ℤ × ℤ} {Sgen : Finset (ℤ × ℤ)} {a₀ : ℤ × ℤ}
    (hflat : ∀ w ∈ Sgen, dot nJ w = dot nJ a₀) :
    ¬ ∃ q ∈ Sgen, dot nJ a₀ < dot nJ q ∧
      ∀ i : ℕ, i < (Sgen.filter fun w => dot nJ w = dot nJ a₀).card - 1 →
        q + (i : ℤ) • vJ ∈ Sgen := by
  rintro ⟨q, hq, hgt, -⟩
  rw [hflat q hq] at hgt
  exact lt_irrefl _ hgt

namespace Gen

theorem cgg_nJ : cgg.nJ = nJg := rfl

theorem cgg_vJ' : cgg.vJ = vJg := rfl

/-- `0` is the `n_J`-minimal point of `S_φ` (levels `0` and `1`). -/
theorem nJ_min_Sg : (0 : ℤ × ℤ) ∈ Sg ∧ ∀ w ∈ Sg, dot nJg 0 ≤ dot nJg w := by
  refine ⟨mem_Sg.mpr (Or.inl rfl), fun w hw => ?_⟩
  rcases mem_Sg.mp hw with rfl | rfl <;> simp [dot_nJg]

/-- The bottom face of `S_φ` is the single point `0`. -/
theorem card_face_Sg : (Sg.filter fun w => dot nJg w = dot nJg 0).card = 1 := by
  have : Sg.filter (fun w => dot nJg w = dot nJg 0) = {0} := by
    ext w
    rw [Finset.mem_filter, mem_Sg, Finset.mem_singleton]
    simp only [dot_nJg]
    constructor
    · rintro ⟨h | h, hw⟩
      · exact h
      · subst h; simp at hw
    · rintro rfl; exact ⟨Or.inl rfl, rfl⟩
  rw [this, Finset.card_singleton]

/-- **The conclusion of `exists_case2_run` at `cg := cgg`, `Sgen := S_φ`, `a₀ := 0` holds** —
vacuously: `q = (-1,1)` is above `0`, and the run length is `0`. -/
theorem run_cgg_Sg :
    ∃ q ∈ Sg, dot cgg.nJ (0 : ℤ × ℤ) < dot cgg.nJ q ∧
      ∀ i : ℕ, i < (Sg.filter fun w => dot cgg.nJ w = dot cgg.nJ (0 : ℤ × ℤ)).card - 1 →
        q + (i : ℤ) • cgg.vJ ∈ Sg := by
  rw [cgg_nJ, cgg_vJ']
  refine run_of_face_card_le_one (by rw [card_face_Sg]) (mem_Sg.mpr (Or.inr rfl)) ?_
  simp [dot_nJg]

/-- **The conclusion at `cg := cgg`, `Sgen := S₁g`, `a₀ := (3,-1)` holds** with a run of length
`1` (§6's `hqgt_hrun_S₁g` in the target's shape). -/
theorem run_cgg_S₁g :
    ∃ q ∈ S₁g, dot cgg.nJ ((3 : ℤ), (-1 : ℤ)) < dot cgg.nJ q ∧
      ∀ i : ℕ, i < (S₁g.filter fun w => dot cgg.nJ w = dot cgg.nJ ((3 : ℤ), (-1 : ℤ))).card - 1 →
        q + (i : ℤ) • cgg.vJ ∈ S₁g := by
  rw [cgg_nJ, cgg_vJ']
  obtain ⟨-, -, hq, hgt, hrun⟩ := hqgt_hrun_S₁g
  exact ⟨_, hq, hgt, hrun⟩

/-- **`hdet_vl` fails on `cgg`**: `p = (1,1)` is not parallel to `v_ℓ = (1,-1)`. -/
theorem not_hdet_vl_cgg : det pg vlg ≠ 0 := by
  simp [det, pg, vlg]

/-- **`ξ = x mod 2` has no one-sided nonexpansive direction.**  Any two members of `X_ξ` either
coincide or differ at every site, and every half-plane `{⟪ℓ, ·⟫ ≤ 0}` contains `0`. -/
theorem not_isOneSidedNonexpansive_ξg (ℓ : ℤ × ℤ) : ¬ Colle45.IsOneSidedNonexpansive ξg ℓ := by
  rintro ⟨x, y, hx, hy, hne, hagr⟩
  apply hne
  funext z
  have h0 := hagr 0 (by simp [dot])
  obtain ⟨u, hu1, hu2⟩ := orbit_pair hx 0 z
  obtain ⟨u', hu1', hu2'⟩ := orbit_pair hy 0 z
  rw [hu1, hu1'] at h0
  rw [hu2, hu2']
  simp only [Prod.fst_zero, add_zero] at h0
  omega

/-- **`NonExpansiveLine ξg = ∅`**, by the same argument (the half-plane `halfPlaneLE v 0` contains
`0`). -/
theorem not_mem_nonExpansiveLine_ξg (v : ℤ × ℤ) : v ∉ Colle45.NonExpansiveLine ξg := by
  rintro ⟨-, x, y, hx, hy, hne, hagr⟩
  apply hne
  funext z
  have h0 := hagr 0 (by show dot v 0 ≤ 0; simp [dot])
  obtain ⟨u, hu1, hu2⟩ := orbit_pair hx 0 z
  obtain ⟨u', hu1', hu2'⟩ := orbit_pair hy 0 z
  rw [hu1, hu1'] at h0
  rw [hu2, hu2']
  simp only [Prod.fst_zero, add_zero] at h0
  omega

end Gen

end Nivat.Case2WindowProbe

#print axioms Nivat.Case2WindowProbe.not_isGeneratingSet_etaC_Sw
#print axioms Nivat.Case2WindowProbe.face_level
#print axioms Nivat.Case2WindowProbe.Q_level
#print axioms Nivat.Case2WindowProbe.B_subset_Q_of_pos
#print axioms Nivat.Case2WindowProbe.base_level
#print axioms Nivat.Case2WindowProbe.window_height
#print axioms Nivat.Case2WindowProbe.pw_le_card_Q
#print axioms Nivat.Case2WindowProbe.P_le_of_conclusion
#print axioms Nivat.Case2WindowProbe.pos_pw_of_conclusion
#print axioms Nivat.Case2WindowProbe.topFace_false_box
#print axioms Nivat.Case2WindowProbe.card_topFace_false_box
#print axioms Nivat.Case2WindowProbe.derivedQ_false_box
#print axioms Nivat.Case2WindowProbe.maxB_one
#print axioms Nivat.Case2WindowProbe.Model.isLatticeConvexRegion_shellInf_one
#print axioms Nivat.Case2WindowProbe.Model.isGeneratingSet_S₁w
#print axioms Nivat.Case2WindowProbe.Model.P_etaC_eq_zero
#print axioms Nivat.Case2WindowProbe.Model.hshell_one
#print axioms Nivat.Case2WindowProbe.Model.hshell_not_two
#print axioms Nivat.Case2WindowProbe.Model.window_model
#print axioms Nivat.Case2WindowProbe.Gen.cgg
#print axioms Nivat.Case2WindowProbe.Gen.isGeneratingSet_Sg
#print axioms Nivat.Case2WindowProbe.Gen.isLatticeConvexRegion_shellInf_cgg
#print axioms Nivat.Case2WindowProbe.Gen.isRegion_shellInf_cgg
#print axioms Nivat.Case2WindowProbe.Gen.hRconv_cgg
#print axioms Nivat.Case2WindowProbe.Gen.hshell_zero
#print axioms Nivat.Case2WindowProbe.Gen.hshell_not_one
#print axioms Nivat.Case2WindowProbe.Gen.isGeneratingSet_S₁g
#print axioms Nivat.Case2WindowProbe.Gen.P_ξg_le_two
#print axioms Nivat.Case2WindowProbe.Gen.window_model_gen
#print axioms Nivat.Case2WindowProbe.Gen.isGeneratingSet_S₁e
#print axioms Nivat.Case2WindowProbe.Gen.window_model_gen_all
#print axioms Nivat.Case2WindowProbe.Gen.not_hshell_of_pos
#print axioms Nivat.Case2WindowProbe.target_type_eq
#print axioms Nivat.Case2WindowProbe.windowConclusion_cgg
#print axioms Nivat.Case2WindowProbe.windowConclusion_cgc_one
#print axioms Nivat.Case2WindowProbe.Gen.per_xperg_snd_eq_zero
#print axioms Nivat.Case2WindowProbe.Gen.not_hp_per_cgg
#print axioms Nivat.Case2WindowProbe.Gen.not_pg_mem_Per_xperg
#print axioms Nivat.Case2WindowProbe.Gen.not_doublyPeriodic_xperg
#print axioms Nivat.Case2WindowProbe.Gen.hagree_cgg
#print axioms Nivat.Case2WindowProbe.Gen.hc_grow_cgg
#print axioms Nivat.Case2WindowProbe.Gen.not_isLatticeConvexRegion_pair
#print axioms Nivat.Case2WindowProbe.Gen.not_hc_env_cgg
#print axioms Nivat.Case2WindowProbe.Gen.not_prev_mem_cgg
#print axioms Nivat.Case2WindowProbe.Gen.vertex_cgg_unique
#print axioms Nivat.Case2WindowProbe.Gen.not_hqgt_hrun_Sg
#print axioms Nivat.Case2WindowProbe.Gen.hqgt_hrun_S₁g
#print axioms Nivat.Case2WindowProbe.pos_pw_of_conclusion_weak
#print axioms Nivat.Case2WindowProbe.window_height_weak
#print axioms Nivat.Case2WindowProbe.run_of_face_card_le_one
#print axioms Nivat.Case2WindowProbe.exists_above_of_face_card_lt
#print axioms Nivat.Case2WindowProbe.run_trivial_of_face_card_le_one
#print axioms Nivat.Case2WindowProbe.not_run_of_flat
#print axioms Nivat.Case2WindowProbe.Gen.nJ_min_Sg
#print axioms Nivat.Case2WindowProbe.Gen.card_face_Sg
#print axioms Nivat.Case2WindowProbe.Gen.run_cgg_Sg
#print axioms Nivat.Case2WindowProbe.Gen.run_cgg_S₁g
#print axioms Nivat.Case2WindowProbe.Gen.not_hdet_vl_cgg
#print axioms Nivat.Case2WindowProbe.Gen.not_isOneSidedNonexpansive_ξg
#print axioms Nivat.Case2WindowProbe.Gen.not_mem_nonExpansiveLine_ξg
