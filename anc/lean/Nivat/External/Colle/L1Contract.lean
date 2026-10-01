/-
`L1Contract.lean` — Lane L1asm, 2026-09-19 18:1x.  Integrator-approved new file (own lane).

The `exists_L1MaxBResidual` **contract** for the wedge route: the residual shape handed to the
three producers (`hbase` / `hlev` / `hsel`), fixed by the kernel rather than by prose.

Why a separate file (measured, not read): `L1Claim.lean:4` is
`import Nivat.External.Colle.L1Assemble`, and every theorem below calls
`L1Claim.exists_L1MaxBResidual_of_wedgeAt`, so these cannot live in `L1Assemble.lean`
(import cycle).  `RegionSteps.lean:6-24` imports `L1Assemble` but not `L1Claim`, so the contract
sits *downstream* of `L1Claim`; the `sorry` body in `RegionSteps.lean:1127` imports this file
when it is filled.

Bodies are verbatim from the adopted receipt `tmp/l1asm_leaf_wire.lean:183-254`.
-/
import Nivat.External.Colle.L1Claim

/-! # The `exists_L1MaxBResidual` contract (wedge route)

Three kernel facts that fix the shape handed to the three residual producers
(`hbase` / `hlev` / `hsel`):

* `leaf_wire_packed'` — the official residual shape: one binder `hres`, quantified over the
  envelope `B` that `hcase1 : Case1 ξ xper d.Sphi vl` (`CaseSplit.lean:82`) exhibits, and
  conditioned on **both** halves of `Case1` (the `EnvOf` half and the `halfStrip` agreement
  half).  Closes `exists_L1MaxBResidual`'s conclusion in one application of
  `L1Claim.exists_L1MaxBResidual_of_wedgeAt`.
* `leaf_wire_packed_of_packed'` — the earlier, unconditioned shape (`hres` without the
  agreement premise) implies the official one, so nothing proved against it is lost.
* `hres_forces_levelInterval_on_Sphi` — why the unconditioned shape over-charges: through
  `enveloped_refl` (`LatticeEdges.lean:641`) it demands `LevelInterval` on the generating set
  `↑d.Sphi` itself, a pure lattice-geometry proposition about `d.Sphi`, not about `hcase1`'s
  envelope.  This is the motivation statement for L1B's two-dimensional gap verdict
  (`OPEN.md #10`).

Reading discipline (§27): each theorem's body is one term-mode application, no `rw`/`convert`;
the unused-variables linter is the non-vacuity oracle (no warning fires on `hres`/`hcase1`).
-/

namespace Nivat.ColleReg

open Nivat Nivat.Colle35 Nivat.Colle41

variable {ξ xper : Config ℤ} {vl ℓ : ℤ × ℤ} {S : Finset (ℤ × ℤ)}

/-- **Official residual shape for `exists_L1MaxBResidual` (wedge route).**  `B` and `hEnv` are
read off `hcase1`; the residual `hres` is a single binder over that `B`, conditioned on both
components of `Case1` (envelope + `halfStrip` agreement).  Closed by one application of
`L1Claim.exists_L1MaxBResidual_of_wedgeAt`. -/
theorem leaf_wire_packed'
    (hξ : IsMinimalCounterexample ξ) (d : DecompDataZ ξ)
    (hℓ_nel : ℓ ∈ Colle45.NonExpansiveLine ξ)
    (hℓ_neg : Colle45.IsOneSidedNonexpansive ξ (-ℓ))
    (hSgen : Nivat.Colle.IsGeneratingSet ξ S)
    (hvl_prim : Primitive vl) (hdet_ℓ : Nivat.LE2.dot ℓ vl = 0)
    (hcase1 : Case1 ξ xper d.Sphi vl)
    -- The residual, conditioned on everything `hcase1` says about its `B`.
    (hres : ∀ B : Set (ℤ × ℤ), Nivat.LE2.EnvOf (d.Sphi : Set (ℤ × ℤ)) B →
      (∃ u : ℤ × ℤ, ∀ z ∈ Nivat.LE2.halfStrip B vl, T u ξ z = xper z) →
      ∃ (e u' v b₀ : ℤ × ℤ) (c : ℤ) (ε : Bool) (k : ℕ),
        b₀ ∈ B ∧ (det u' vl = 1 ∨ det u' vl = -1) ∧ c ≠ 0 ∧
        Nivat.RegionSweep.LevelInterval B vl ∧
        PeriodOn (T e ξ) (chainFull B vl u' b₀ k) (c • vl) ∧
        ∀ N : ℕ, PeriodOn (T e ξ) (chainFull B vl u' b₀ (k + N)) (c • vl) →
          ¬ PeriodOn (T e ξ) (chainFull B vl u' b₀ (k + (N + 1))) (c • vl) →
          ∃ τ : ℤ,
            (∀ z ∈ L1Data.derivedQ ε u' (S.image (· + v)),
              τ • u' + z ∈ chainFull B vl u' b₀ (k + N) ∧
              τ • u' + z + c • vl ∈ chainFull B vl u' b₀ (k + N)) ∧
            Nivat.L1Region.Straddle (T e ξ) (chainFull B vl u' b₀ (k + N))
              (chainFull B vl u' b₀ (k + (N + 1))) (S.image (· + v))
              (L1Data.derivedQ ε u' (S.image (· + v))) vl u' c τ) :
    ∃ (e u u' v : ℤ × ℤ) (c τ : ℤ) (ε : Bool) (S₁ : Finset (ℤ × ℤ))
      (F : Nivat.L1Region.RegionFamily (T e ξ) u u' c),
      S₁ = S.image (· + v) ∧
      Nivat.ColleReg.L1Data.MaxBResidual (ξ := ξ) ε u u' c τ S₁ F := by
  obtain ⟨B, hEnv, hagree⟩ := hcase1
  obtain ⟨e, u', v, b₀, c, ε, k, hb₀, hunimod, c0, hlev, hbase, hsel⟩ := hres B hEnv hagree
  exact L1Claim.exists_L1MaxBResidual_of_wedgeAt hξ d hℓ_nel hℓ_neg hSgen hvl_prim hdet_ℓ ε
    hEnv hb₀ hunimod c0 hlev k hbase hsel

/-- The unconditioned shape (no `halfStrip` agreement premise) implies the official one, so
nothing already proved against it is lost. -/
theorem leaf_wire_packed_of_packed'
    (hξ : IsMinimalCounterexample ξ) (d : DecompDataZ ξ)
    (hℓ_nel : ℓ ∈ Colle45.NonExpansiveLine ξ)
    (hℓ_neg : Colle45.IsOneSidedNonexpansive ξ (-ℓ))
    (hSgen : Nivat.Colle.IsGeneratingSet ξ S)
    (hvl_prim : Primitive vl) (hdet_ℓ : Nivat.LE2.dot ℓ vl = 0)
    (hcase1 : Case1 ξ xper d.Sphi vl)
    (hres : ∀ B : Set (ℤ × ℤ), Nivat.LE2.EnvOf (d.Sphi : Set (ℤ × ℤ)) B →
      ∃ (e u' v b₀ : ℤ × ℤ) (c : ℤ) (ε : Bool) (k : ℕ),
        b₀ ∈ B ∧ (det u' vl = 1 ∨ det u' vl = -1) ∧ c ≠ 0 ∧
        Nivat.RegionSweep.LevelInterval B vl ∧
        PeriodOn (T e ξ) (chainFull B vl u' b₀ k) (c • vl) ∧
        ∀ N : ℕ, PeriodOn (T e ξ) (chainFull B vl u' b₀ (k + N)) (c • vl) →
          ¬ PeriodOn (T e ξ) (chainFull B vl u' b₀ (k + (N + 1))) (c • vl) →
          ∃ τ : ℤ,
            (∀ z ∈ L1Data.derivedQ ε u' (S.image (· + v)),
              τ • u' + z ∈ chainFull B vl u' b₀ (k + N) ∧
              τ • u' + z + c • vl ∈ chainFull B vl u' b₀ (k + N)) ∧
            Nivat.L1Region.Straddle (T e ξ) (chainFull B vl u' b₀ (k + N))
              (chainFull B vl u' b₀ (k + (N + 1))) (S.image (· + v))
              (L1Data.derivedQ ε u' (S.image (· + v))) vl u' c τ) :
    ∃ (e u u' v : ℤ × ℤ) (c τ : ℤ) (ε : Bool) (S₁ : Finset (ℤ × ℤ))
      (F : Nivat.L1Region.RegionFamily (T e ξ) u u' c),
      S₁ = S.image (· + v) ∧
      Nivat.ColleReg.L1Data.MaxBResidual (ξ := ξ) ε u u' c τ S₁ F :=
  leaf_wire_packed' hξ d hℓ_nel hℓ_neg hSgen hvl_prim hdet_ℓ hcase1
    (fun B hEnv _ => hres B hEnv)

/-- The unconditioned shape over-charges: whenever `d.Sphi` is a lattice-convex region, a
residual of the form `∀ B, EnvOf ↑d.Sphi B → LevelInterval B vl` already demands
`LevelInterval` on the generating set `↑d.Sphi` itself (`enveloped_refl`,
`LatticeEdges.lean:641`) — a claim about `d.Sphi`, not about `hcase1`'s envelope. -/
theorem hres_forces_levelInterval_on_Sphi
    (d : DecompDataZ ξ)
    (hS : IsLatticeConvexRegion (d.Sphi : Set (ℤ × ℤ)))
    (hres : ∀ B : Set (ℤ × ℤ), Nivat.LE2.EnvOf (d.Sphi : Set (ℤ × ℤ)) B →
      Nivat.RegionSweep.LevelInterval B vl) :
    Nivat.RegionSweep.LevelInterval (d.Sphi : Set (ℤ × ℤ)) vl :=
  hres _ (Nivat.LE2.enveloped_refl _ hS)

/-! ## Route A: the contract without the `LevelInterval` conjunct

Cclaim's Route A (`L1Claim.ofWedgeAtConvex`, section `RouteA`) builds the family from
`hconv : IsLatticeConvexRegion (wedgeFull B vl u')` instead of `hlev`, and L1B pays `hconv`
from `hunimod` alone (`L1Data.isLatticeConvexRegion_wedgeFull_of_unimod`, `L1LevelSpan.lean`).
So the residual shape loses its `LevelInterval B vl` conjunct and nothing else.  The body
below is `L1Claim.exists_L1MaxBResidual_of_wedgeAt`'s body with `ofWedgeAt` replaced by
`ofWedgeAtConvex`; `hsel` is consumed **unsplit**, exactly as that theorem consumes it.

§14: `leaf_wire_packed'` above is kept as it was; `leaf_wire_packed'_of_unimod` is the receipt
that the old shape is a corollary of the new one (the conjunct is dropped, the rest is passed
through).  `sorry TOTAL` is unchanged by this section (hard rule 1). -/

/-- **Route A residual shape** — `leaf_wire_packed'` minus `Nivat.RegionSweep.LevelInterval B vl`.
This is the shape to hand to the `hbase` / `hsel` producers. -/
theorem leaf_wire_packed_unimod
    (hξ : IsMinimalCounterexample ξ) (d : DecompDataZ ξ)
    (hℓ_nel : ℓ ∈ Colle45.NonExpansiveLine ξ)
    (hℓ_neg : Colle45.IsOneSidedNonexpansive ξ (-ℓ))
    (hSgen : Nivat.Colle.IsGeneratingSet ξ S)
    (hvl_prim : Primitive vl) (hdet_ℓ : Nivat.LE2.dot ℓ vl = 0)
    (hcase1 : Case1 ξ xper d.Sphi vl)
    (hres : ∀ B : Set (ℤ × ℤ), Nivat.LE2.EnvOf (d.Sphi : Set (ℤ × ℤ)) B →
      (∃ u : ℤ × ℤ, ∀ z ∈ Nivat.LE2.halfStrip B vl, T u ξ z = xper z) →
      ∃ (e u' v b₀ : ℤ × ℤ) (c : ℤ) (ε : Bool) (k : ℕ),
        b₀ ∈ B ∧ (det u' vl = 1 ∨ det u' vl = -1) ∧ c ≠ 0 ∧
        PeriodOn (T e ξ) (chainFull B vl u' b₀ k) (c • vl) ∧
        ∀ N : ℕ, PeriodOn (T e ξ) (chainFull B vl u' b₀ (k + N)) (c • vl) →
          ¬ PeriodOn (T e ξ) (chainFull B vl u' b₀ (k + (N + 1))) (c • vl) →
          ∃ τ : ℤ,
            (∀ z ∈ L1Data.derivedQ ε u' (S.image (· + v)),
              τ • u' + z ∈ chainFull B vl u' b₀ (k + N) ∧
              τ • u' + z + c • vl ∈ chainFull B vl u' b₀ (k + N)) ∧
            Nivat.L1Region.Straddle (T e ξ) (chainFull B vl u' b₀ (k + N))
              (chainFull B vl u' b₀ (k + (N + 1))) (S.image (· + v))
              (L1Data.derivedQ ε u' (S.image (· + v))) vl u' c τ) :
    ∃ (e u u' v : ℤ × ℤ) (c τ : ℤ) (ε : Bool) (S₁ : Finset (ℤ × ℤ))
      (F : Nivat.L1Region.RegionFamily (T e ξ) u u' c),
      S₁ = S.image (· + v) ∧
      Nivat.ColleReg.L1Data.MaxBResidual (ξ := ξ) ε u u' c τ S₁ F := by
  obtain ⟨B, hEnv, hagree⟩ := hcase1
  obtain ⟨e, u', v, b₀, c, ε, k, hb₀, hunimod, c0, hbase, hsel⟩ := hres B hEnv hagree
  have hu' : Primitive u' := by
    show IsCoprime u'.1 u'.2
    rcases hunimod with h | h
    · exact ⟨vl.2, -vl.1, by simp only [det] at h; linear_combination h⟩
    · exact ⟨-vl.2, vl.1, by simp only [det] at h; linear_combination -h⟩
  have hinf : ¬ PeriodOn (T e ξ) (wedgeFull B vl u') (c • vl) :=
    hinf_of_ge e hξ d hb₀ hunimod (smul_ne_zero c0 hvl_prim.ne_zero)
  let F : Nivat.L1Region.RegionFamily (T e ξ) vl u' c :=
    L1Claim.ofWedgeAtConvex hb₀ (L1Data.isLatticeConvexRegion_wedgeFull_of_unimod hunimod)
      hunimod k hbase hinf
  have hR : ∀ n, F.R n = chainFull B vl u' b₀ (k + n) := fun _ => rfl
  obtain ⟨N, hN, hN1⟩ :=
    Nivat.L1Region.exists_greatest_periodOn F.monotone F.base F.union_not
  obtain ⟨τ, hline, hstr⟩ := hsel N (by rw [← hR]; exact hN) (by rw [← hR]; exact hN1)
  exact L1Claim.exists_L1MaxBResidual_of_tail hℓ_nel hℓ_neg hSgen hvl_prim hdet_ℓ ε
    (L1Data.det_ne_zero_of_unimod hunimod) hu' c0 F N hN hN1
    (by rw [hR]; exact hline) (by rw [hR, hR]; exact hstr)

/-- §14 receipt: the official shape `leaf_wire_packed'` (with its `LevelInterval` conjunct) is a
corollary of the Route A shape — the conjunct is dropped, everything else passes through. -/
theorem leaf_wire_packed'_of_unimod
    (hξ : IsMinimalCounterexample ξ) (d : DecompDataZ ξ)
    (hℓ_nel : ℓ ∈ Colle45.NonExpansiveLine ξ)
    (hℓ_neg : Colle45.IsOneSidedNonexpansive ξ (-ℓ))
    (hSgen : Nivat.Colle.IsGeneratingSet ξ S)
    (hvl_prim : Primitive vl) (hdet_ℓ : Nivat.LE2.dot ℓ vl = 0)
    (hcase1 : Case1 ξ xper d.Sphi vl)
    (hres : ∀ B : Set (ℤ × ℤ), Nivat.LE2.EnvOf (d.Sphi : Set (ℤ × ℤ)) B →
      (∃ u : ℤ × ℤ, ∀ z ∈ Nivat.LE2.halfStrip B vl, T u ξ z = xper z) →
      ∃ (e u' v b₀ : ℤ × ℤ) (c : ℤ) (ε : Bool) (k : ℕ),
        b₀ ∈ B ∧ (det u' vl = 1 ∨ det u' vl = -1) ∧ c ≠ 0 ∧
        Nivat.RegionSweep.LevelInterval B vl ∧
        PeriodOn (T e ξ) (chainFull B vl u' b₀ k) (c • vl) ∧
        ∀ N : ℕ, PeriodOn (T e ξ) (chainFull B vl u' b₀ (k + N)) (c • vl) →
          ¬ PeriodOn (T e ξ) (chainFull B vl u' b₀ (k + (N + 1))) (c • vl) →
          ∃ τ : ℤ,
            (∀ z ∈ L1Data.derivedQ ε u' (S.image (· + v)),
              τ • u' + z ∈ chainFull B vl u' b₀ (k + N) ∧
              τ • u' + z + c • vl ∈ chainFull B vl u' b₀ (k + N)) ∧
            Nivat.L1Region.Straddle (T e ξ) (chainFull B vl u' b₀ (k + N))
              (chainFull B vl u' b₀ (k + (N + 1))) (S.image (· + v))
              (L1Data.derivedQ ε u' (S.image (· + v))) vl u' c τ) :
    ∃ (e u u' v : ℤ × ℤ) (c τ : ℤ) (ε : Bool) (S₁ : Finset (ℤ × ℤ))
      (F : Nivat.L1Region.RegionFamily (T e ξ) u u' c),
      S₁ = S.image (· + v) ∧
      Nivat.ColleReg.L1Data.MaxBResidual (ξ := ξ) ε u u' c τ S₁ F :=
  leaf_wire_packed_unimod hξ d hℓ_nel hℓ_neg hSgen hvl_prim hdet_ℓ hcase1
    (fun B hEnv hagree =>
      let ⟨e, u', v, b₀, c, ε, k, hb₀, hunimod, c0, _, hbase, hsel⟩ := hres B hEnv hagree
      ⟨e, u', v, b₀, c, ε, k, hb₀, hunimod, c0, hbase, hsel⟩)

end Nivat.ColleReg

#print axioms Nivat.ColleReg.leaf_wire_packed'
#print axioms Nivat.ColleReg.leaf_wire_packed_of_packed'
#print axioms Nivat.ColleReg.hres_forces_levelInterval_on_Sphi
#print axioms Nivat.ColleReg.leaf_wire_packed_unimod
#print axioms Nivat.ColleReg.leaf_wire_packed'_of_unimod
