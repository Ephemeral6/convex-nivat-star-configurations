/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.LeafAJSelect
import Nivat.External.Colle.SweepCriterion
import Nivat.External.Colle.MaximalEnveloped

/-!
# Lane `lane-cd-swept`: `SweptClosed` for `Â_∞` past `ℓ_J`

Discharges the `hswept` binder of `Nivat.Colle35.ChainDataGeom.ofPartsExhaustsInter`
(`Nivat/External/Colle/ChainExhaustInter.lean`), unblocking
`tmp/wip/LeafAAssemble.lean:387`'s `-- GAP: SweptClosed's definition not yet consulted
this round`.

## Paper anchor

`b3_colle2.txt:800-806` (Claim 4.6's proof and the paragraph right after it): the region
is built by *sweeping*,

> `𝓡_i := {g + t·v⃗_{ℓ_i} ∈ ℤ² : g ∈ 𝓡_{i+1}, t ∈ ℤ₊}`

i.e. `𝓡_{J-1}` is `𝓡_J` (my `T := ⋃ i, Ahat i`, playing the role of `𝓡_J`/`ℋ(ℓ_J)` in the
chain `𝓡_{ι-1} ⊂ 𝓡_{ι-2} ⊂ ⋯`) swept along `v⃗_{ℓ_{J-1}}` (my `vJ1`). `SweptClosed`'s own
docstring (`MaximalEnveloped.lean:602-605`) is the Lean-side restatement: *"This holds for
Colle's `Â_∞`, whose support line in the direction `ℓ_J` is exactly `{⟨n,·⟩ = c}` and whose
recession cone contains `v_{ℓ_{J-1}}` on that side."* Every premise of that sentence is a
binder below: `hcJ` gives the support line (`cJ = dot nJ g_J`, `g_J` = the pinned point on
`ℓ_J`'s face, from `LeafAJSelect.exists_gJ_pinned_ccw`); `hgrow` gives "the recession cone
contains `v_{ℓ_{J-1}}`" *at* `g_J` (a ray `g_J + t • dir J`, the ccw pinning's own witnessed
ray shape, from `LeafAJSelect.hgrow_of_pinned_ccw`); `hsupp_prev`/`hnprevdet`/`hdotnprevvJ1`
supply the fan-adjacency data (`ℓ_{J-1} = nprevJ`, from `LeafAJSelect.exists_nprevJ_vJ1`)
that pins the sliding parameter to be nonnegative, mirroring the sweep-only-forward
direction `t ∈ ℤ₊` in the paper's own definition of `𝓡_i`.

## Binder design (deviates from the initial 5-step real-geometry sketch)

Rather than re-deriving ray-existence from `hJunb`/`AhatMono`/`hlc`/`hfin`/`hne`/`henv` from
scratch, this file consumes `LeafAJSelect.hgrow_of_pinned_ccw` and `LeafAJSelect.hsupp_prev`'s
*exact output shapes* as binders — both are already 0-`sorry` theorems in `Nivat/`. The caller
(`LeafAAssemble.lean`) supplies them by applying those two theorems with its own `σ'`:
`ChainExhaustInter`'s `Ahat` argument here is meant to *already* be the caller's
post-reindexing tower `fun i => hatOf A kk vl (σ' i)`, so `σ` is composed away before it
reaches this file — matching `LeafAJSelect.hgrow_of_pinned_ccw`'s own conclusion type
`∀ N, ∃ i, ∀ t ≤ N, g_J + t • dir J ∈ Ahat (σ i)`, read with `Ahat (σ ·)` folded into a
single tower argument, and likewise for `hsupp_prev`. This keeps this file's binder list free
of the `S`/`Sphi`/`Enveloped`/`Arc` machinery entirely, since that's all already discharged
inside `hgrow_of_pinned_ccw` and `hsupp_prev`'s own proofs.

## Sign bookkeeping (the "heart of the argument", verified below both symbolically and on a
worked numeric instance)

* `hsweep : dot nJ vJ1 < 0` (`nJ = -J`) — sliding along `vJ1` *decreases* `dot nJ`, so the
  hypothesis `cJ ≤ dot nJ (g + t • vJ1)` bounds `t` from *above* by a real number `s`.
* `dot nJ (dir J) = 0` — `dir J` sits exactly on the `nJ`-level line through `g_J`, so the
  real point `q` where the `vJ1`-ray from `g` crosses that level line is `g_J + c • dir J`
  for a *real* `c` (`SweepCrit.exists_smul_of_ip_zero`, the collinearity step).
* `hnprevdet : 0 < det nprevJ J` together with `dot_dir_left`/`det_skew` gives
  `dot nprevJ (dir J) = det J nprevJ = -det nprevJ J < 0`. Combined with `hsupp_prev`
  (`dot nprevJ g ≤ dot nprevJ g_J`, preserved along `vJ1` since `hdotnprevvJ1`), this forces
  `c ≥ 0` — dividing an inequality by a *negative* number flips it. This is the sign check
  the task flagged as the project's most common failure mode; it is re-verified by
  explicit `have`s/`nlinarith` below, not glossed over.

### Numeric wedge (worked by hand)

`J := (1,0)`, so `nJ = -J = (-1,0)`, `dir J = (0,1)`. `nprevJ := (0,-1)`, so
`vJ1 = dir nprevJ = (1,0)` and:

* `det nprevJ J = nprevJ.1*J.2 - nprevJ.2*J.1 = 0*0 - (-1)*1 = 1 > 0` ✓ (`hnprevdet`).
* `dot nJ vJ1 = (-1)*1 + 0*0 = -1 < 0` ✓ (`hsweep`).
* `dot nprevJ vJ1 = 0*1 + (-1)*0 = 0` ✓ (`hdotnprevvJ1`).
* `dot nprevJ (dir J) = dot (0,-1) (0,1) = -1 = -(det nprevJ J)` ✓ (the forcing sign).

Take `g_J := (5,5)`, `cJ := dot nJ g_J = -5`, and `T := {z : ℤ × ℤ | 5 ≤ z.2}` (a half-plane;
`hsupp_prev`'s conclusion `dot nprevJ z ≤ dot nprevJ g_J` reads `-z.2 ≤ -5`, i.e. `z.2 ≥ 5`,
so *any* valid `T` must sit inside this half-plane — `T` itself realizes the tight case).
Take `Ahat i := T` for all `i` (`hgrow` and `hTconv` trivial). Pick `g := (0,6) ∈ T`; then
for `t := 3`: `cJ ≤ dot nJ (g + 3•vJ1) = dot (-1,0) (3,6) = -3` — indeed `-5 ≤ -3`. The real
crossing point is `s = (cJ - dot nJ g)/(dot nJ vJ1) = (-5 - 0)/(-1) = 5`, `q = (0,6) + 5•(1,0)
= (5,6) = g_J + 1 • dir J`, so `c = 1 ≥ 0` as predicted, `k0 = 1`, and `g_J`, `g_J + dir J =
(5,6)` are both in `T` (`hgrow 1`), giving `q ∈ convHullOf T` by convexity, and finally
`g + 3•vJ1 = (3,6) ∈ T` by convexity again (also directly visible since `T` only constrains
the `y`-coordinate here — the example is deliberately simple to isolate the sign checks;
`T`'s shape in the real application is far from a half-plane, but the argument never uses
more than convexity + the four sign facts above). -/

set_option autoImplicit false

namespace Nivat.LaneCdSwept

open Nivat Nivat.LE2 Nivat.MaxEnv

/-- **`SweptClosed` for the exhausted tower `⋃ i, Ahat i`, past `ℓ_J`.**

`Ahat` here is already the caller's post-`σ`-reindexing tower (see the module docstring).
`J`/`nprevJ`/`g_J` are `LeafAJSelect`'s ccw-pinning data; `nJ := -J`; `hcJ` ties `cJ` to
`g_J`'s support value on `ℓ_J`. -/
theorem sweptClosed_of_pinned_ccw
    {Ahat : ℕ → Set (ℤ × ℤ)} {J nprevJ g_J vJ1 nJ : ℤ × ℤ} {cJ : ℤ}
    (hJne0 : J ≠ 0)
    (hnJ : nJ = -J)
    (hcJ : cJ = dot nJ g_J)
    (hsweep : dot nJ vJ1 < 0)
    (hnprevdet : 0 < det nprevJ J)
    (hdotnprevvJ1 : dot nprevJ vJ1 = 0)
    (hgrow : ∀ N : ℕ, ∃ i, ∀ t : ℕ, t ≤ N → g_J + (t : ℤ) • dir J ∈ Ahat i)
    (hsupp_prev : ∀ i, ∀ z ∈ Ahat i, dot nprevJ z ≤ dot nprevJ g_J)
    (hTconv : IsLatticeConvexRegion (⋃ i, Ahat i)) :
    SweptClosed (⋃ i, Ahat i) vJ1 nJ cJ := by
  classical
  -- `ip n (toReal z)` unfolds to the cast of `dot n z`; a single reusable helper.
  have ip_toReal : ∀ n z : ℤ × ℤ, Nivat.Colle35.ip n (toReal z) = (dot n z : ℝ) := by
    intro n z; unfold Nivat.Colle35.ip; exact dot_cast_toReal n z
  have ip_sub : ∀ (n : ℤ × ℤ) (a b : ℝ × ℝ),
      Nivat.Colle35.ip n (a - b) = Nivat.Colle35.ip n a - Nivat.Colle35.ip n b := by
    intro n a b; simp only [Nivat.Colle35.ip, Prod.fst_sub, Prod.snd_sub]; ring
  set T : Set (ℤ × ℤ) := ⋃ i, Ahat i with hT
  set Cset : Set (ℝ × ℝ) := convHullOf T with hCset
  have hTeq : T = toReal ⁻¹' Cset := by rw [hCset]; exact eq_preimage_convHullOf hTconv
  have hdirJne : dir J ≠ ((0 : ℤ), (0 : ℤ)) := by
    intro h
    apply hJne0
    have h1 : J.1 = 0 := by
      have := congrArg Prod.snd h
      simpa [dir] using this
    have h2 : J.2 = 0 := by
      have := congrArg Prod.fst h
      simpa [dir] using this
    exact Prod.ext h1 h2
  have hdotnJdirJ : dot nJ (dir J) = 0 := by
    rw [hnJ, dot_neg_left]; simp [dot_dir]
  -- `dot nprevJ (dir J) = det J nprevJ = -det nprevJ J < 0`.
  have hdot_nprev_dirJ : dot nprevJ (dir J) = det J nprevJ := by
    rw [dot_comm nprevJ (dir J)]; exact Nivat.PolyChainSum.dot_dir_left J nprevJ
  have hdet_skew : det J nprevJ = -det nprevJ J := Nivat.LE2.det_skew J nprevJ
  have hdot_nprev_dirJ_neg : dot nprevJ (dir J) < 0 := by
    rw [hdot_nprev_dirJ, hdet_skew]; omega
  have hnJne : nJ ≠ 0 := by rw [hnJ]; simpa using hJne0
  unfold SweptClosed
  intro g hgT t ht
  obtain ⟨i1, hgi1⟩ := Set.mem_iUnion.mp hgT
  rcases Nat.eq_zero_or_pos t with rfl | htpos
  · simpa using hgT
  -- General case: `t ≥ 1`.
  set m : ℝ := (dot nJ vJ1 : ℝ) with hm
  have hmneg : m < 0 := by rw [hm]; exact_mod_cast hsweep
  have hmne : m ≠ 0 := ne_of_lt hmneg
  set s : ℝ := ((cJ : ℝ) - (dot nJ g : ℝ)) / m with hs_def
  have hsm : s * m = (cJ : ℝ) - (dot nJ g : ℝ) := (eq_div_iff hmne).mp hs_def
  have hcast : (cJ : ℝ) - (dot nJ g : ℝ) ≤ (t : ℝ) * m := by
    have hint : (cJ : ℤ) ≤ dot nJ (g + (t : ℤ) • vJ1) := ht
    have hexp : dot nJ (g + (t : ℤ) • vJ1) = dot nJ g + t * dot nJ vJ1 := by
      rw [dot_add, dot_comm nJ ((t : ℤ) • vJ1), dot_smul, dot_comm vJ1 nJ]
    rw [hexp] at hint
    have : (cJ : ℝ) ≤ (dot nJ g : ℝ) + (t : ℝ) * (dot nJ vJ1 : ℝ) := by exact_mod_cast hint
    linarith
  have hts : (t : ℝ) ≤ s := by
    by_contra hcon
    push_neg at hcon
    have hflip : t * m < s * m := by
      nlinarith [mul_pos (sub_pos.mpr hcon) (neg_pos.mpr hmneg)]
    rw [hsm] at hflip
    linarith
  have htpos' : (0 : ℝ) < (t : ℝ) := by exact_mod_cast htpos
  have hspos : (0 : ℝ) < s := lt_of_lt_of_le htpos' hts
  set G : ℝ × ℝ := toReal g with hG
  set W : ℝ × ℝ := toReal vJ1 with hW
  set Q0 : ℝ × ℝ := toReal g_J with hQ0
  set q : ℝ × ℝ := G + s • W with hq_def
  have hip_nJ_q_sub_Q0 : Nivat.Colle35.ip nJ (q - Q0) = 0 := by
    have hipG : Nivat.Colle35.ip nJ G = (dot nJ g : ℝ) := by rw [hG]; exact ip_toReal nJ g
    have hipW : Nivat.Colle35.ip nJ W = m := by rw [hW]; exact ip_toReal nJ vJ1
    have hipQ0 : Nivat.Colle35.ip nJ Q0 = (dot nJ g_J : ℝ) := by rw [hQ0]; exact ip_toReal nJ g_J
    have hipq : Nivat.Colle35.ip nJ q = (cJ : ℝ) := by
      rw [hq_def, Nivat.Colle35.ip_add, Nivat.Colle35.ip_smul, hipG, hipW]
      linarith [hsm]
    rw [ip_sub, hipq, hipQ0, hcJ]; ring
  obtain ⟨c, hc⟩ :=
    Nivat.SweepCrit.exists_smul_of_ip_zero hnJne hdirJne hdotnJdirJ hip_nJ_q_sub_Q0
  have hqQ0 : q = Q0 + c • toReal (dir J) := by
    rw [← hc]; module
  -- `c ≥ 0`, via `hsupp_prev` and the `nprevJ`-sign check.
  have hc_nonneg : 0 ≤ c := by
    have hipnp_G : Nivat.Colle35.ip nprevJ G = (dot nprevJ g : ℝ) := by
      rw [hG]; exact ip_toReal nprevJ g
    have hipnp_W : Nivat.Colle35.ip nprevJ W = 0 := by
      rw [hW, ip_toReal nprevJ vJ1, hdotnprevvJ1]; norm_num
    have hipnp_Q0 : Nivat.Colle35.ip nprevJ Q0 = (dot nprevJ g_J : ℝ) := by
      rw [hQ0]; exact ip_toReal nprevJ g_J
    have hipnp_q : Nivat.Colle35.ip nprevJ q = (dot nprevJ g : ℝ) := by
      rw [hq_def, Nivat.Colle35.ip_add, Nivat.Colle35.ip_smul, hipnp_G, hipnp_W]; ring
    have hle : (dot nprevJ g : ℝ) ≤ (dot nprevJ g_J : ℝ) := by
      exact_mod_cast hsupp_prev i1 g hgi1
    have hipnp_dirJ : Nivat.Colle35.ip nprevJ (toReal (dir J)) = (dot nprevJ (dir J) : ℝ) :=
      ip_toReal nprevJ (dir J)
    have hqsub_le : Nivat.Colle35.ip nprevJ (q - Q0) ≤ 0 := by
      rw [ip_sub, hipnp_q, hipnp_Q0]; linarith
    have hqsub_eq : Nivat.Colle35.ip nprevJ (q - Q0) = c * (dot nprevJ (dir J) : ℝ) := by
      rw [hqQ0]
      have : Nivat.Colle35.ip nprevJ (Q0 + c • toReal (dir J) - Q0)
          = Nivat.Colle35.ip nprevJ (c • toReal (dir J)) := by
        congr 1; abel
      rw [this, Nivat.Colle35.ip_smul, hipnp_dirJ]
    have hxneg : (dot nprevJ (dir J) : ℝ) < 0 := by exact_mod_cast hdot_nprev_dirJ_neg
    by_contra hcneg
    push_neg at hcneg
    have hpos : 0 < c * (dot nprevJ (dir J) : ℝ) := mul_pos_of_neg_of_neg hcneg hxneg
    rw [← hqsub_eq] at hpos
    linarith [hqsub_le]
  -- `k0 := ⌈c⌉₊`; `hgrow k0` supplies the two lattice endpoints of the ray we need.
  set k0 : ℕ := ⌈c⌉₊ with hk0
  have hck0 : c ≤ (k0 : ℝ) := Nat.le_ceil c
  obtain ⟨i2, hi2⟩ := hgrow k0
  have hQ0mem : g_J ∈ Ahat i2 := by simpa using hi2 0 (Nat.zero_le k0)
  have hQk0mem : g_J + (k0 : ℤ) • dir J ∈ Ahat i2 := hi2 k0 (le_refl k0)
  have hQ0T : g_J ∈ T := Set.mem_iUnion.mpr ⟨i2, hQ0mem⟩
  have hQk0T : g_J + (k0 : ℤ) • dir J ∈ T := Set.mem_iUnion.mpr ⟨i2, hQk0mem⟩
  have hQ0Cset : Q0 ∈ Cset := by rw [hQ0, hCset]; exact toReal_mem_convHullOf hQ0T
  have hQk0Cset' : toReal (g_J + (k0 : ℤ) • dir J) ∈ Cset := by
    rw [hCset]; exact toReal_mem_convHullOf hQk0T
  have hQk0eq : toReal (g_J + (k0 : ℤ) • dir J) = Q0 + (k0 : ℝ) • toReal (dir J) := by
    rw [hQ0]; exact Nivat.SweepCrit.toReal_add_nsmul g_J (dir J) k0
  have hQk0Cset : Q0 + (k0 : ℝ) • toReal (dir J) ∈ Cset := hQk0eq ▸ hQk0Cset'
  have hCconv : Convex ℝ Cset := by rw [hCset]; exact Nivat.LE2.convex_convHullOf T
  have hqCset : q ∈ Cset := by
    rcases Nat.eq_zero_or_pos k0 with hk00 | hk0pos
    · have hc0 : c = 0 := by
        have : c ≤ (0 : ℝ) := by rw [hk00] at hck0; exact_mod_cast hck0
        linarith
      have hqeq : q = Q0 := by rw [hqQ0, hc0]; module
      rw [hqeq]; exact hQ0Cset
    · have hk0pos' : (0 : ℝ) < (k0 : ℝ) := by exact_mod_cast hk0pos
      have hk0ne : (k0 : ℝ) ≠ 0 := ne_of_gt hk0pos'
      set lam : ℝ := c / (k0 : ℝ) with hlam
      have hlam0 : 0 ≤ lam := div_nonneg hc_nonneg hk0pos'.le
      have hlam1 : lam ≤ 1 := by rw [hlam, div_le_one hk0pos']; exact hck0
      have hsum : (1 - lam) + lam = 1 := by ring
      have hmem := hCconv hQ0Cset hQk0Cset (by linarith : (0:ℝ) ≤ 1 - lam) hlam0 hsum
      have hlamk0 : lam * (k0 : ℝ) = c := by
        rw [hlam]; field_simp
      have heq : (1 - lam) • Q0 + lam • (Q0 + (k0 : ℝ) • toReal (dir J)) = q := by
        rw [hqQ0, ← hlamk0]; module
      rwa [heq] at hmem
  rw [hTeq]
  show toReal (g + (t : ℤ) • vJ1) ∈ Cset
  have hGCset : G ∈ Cset := by rw [hG, hCset]; exact toReal_mem_convHullOf hgT
  set lam2 : ℝ := (t : ℝ) / s with hlam2
  have hlam2_0 : 0 ≤ lam2 := div_nonneg htpos'.le hspos.le
  have hlam2_1 : lam2 ≤ 1 := by rw [hlam2, div_le_one hspos]; exact hts
  have hsum2 : (1 - lam2) + lam2 = 1 := by ring
  have hmem2 := hCconv hGCset hqCset (by linarith : (0:ℝ) ≤ 1 - lam2) hlam2_0 hsum2
  have hsne : s ≠ 0 := ne_of_gt hspos
  have hlam2s : lam2 * s = (t : ℝ) := by rw [hlam2]; field_simp
  have heq2 : (1 - lam2) • G + lam2 • q = toReal (g + (t : ℤ) • vJ1) := by
    rw [hq_def, Nivat.SweepCrit.toReal_add_nsmul, ← hG, ← hW, ← hlam2s]
    module
  rwa [heq2] at hmem2

end Nivat.LaneCdSwept

#print axioms Nivat.LaneCdSwept.sweptClosed_of_pinned_ccw
