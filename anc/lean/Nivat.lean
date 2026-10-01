/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.Defs.Config
import Nivat.Defs.Complexity
import Nivat.Defs.StarConfig
import Nivat.Defs.Orbit
import Nivat.Chord
import Nivat.Words
import Nivat.MorseHedlund
import Nivat.PeriodCount
import Nivat.SubseqLimit
import Nivat.OrbitTransfer
import Nivat.RayOrder
import Nivat.Laurent.Basic
import Nivat.Laurent.UFD
import Nivat.Laurent.Newton
import Nivat.Laurent.Ostrowski
import Nivat.Laurent.SublatticeBasis
import Nivat.Lattice.Primitive
import Nivat.Lattice.Zonotope
import Nivat.Lattice.Unimodular
import Nivat.Dichotomy
import Nivat.Spectrum
import Nivat.Background
import Nivat.Witness
import Nivat.BiRecursion
import Nivat.Laurent.BinomialCoprime
import Nivat.Laurent.MonoShift
import Nivat.Laurent.QuotientGlue
import Nivat.ZonotopePair
import Nivat.MainTheorem
import Nivat.AppendixD
import Nivat.Section8.HalfPlane
import Nivat.Section8.ConeGeom
import Nivat.Section8.External
import Nivat.Section8.FirstHalfPlane
import Nivat.Section8.SubseqFinite
import Nivat.Section8.SecondHalfPlane
import Nivat.Section8.Normalisation
import Nivat.Section8.Main
import Nivat.External.Colle.Interfaces
import Nivat.External.Colle.RegionTranslate
import Nivat.External.Colle.CosetPigeonhole
import Nivat.External.Colle.StepMultiplicity
import Nivat.External.Colle.PeriodTransport
import Nivat.External.Colle.FaceData
import Nivat.External.Colle.ChainRecursion
import Nivat.External.Colle.EnvBound
import Nivat.External.Colle.OrderThree

/-!
# The Convex Nivat Conjecture

A formalisation of *The Convex Nivat Conjecture: A complexity lower bound for star
configurations, and a reduction from low convex complexity to star configurations*, by
Guancheng Pan (12 September 2026).

The imported development follows the paper section by section and compiles. It is
unconditional: no project axiom remains. Kernel dependency checks give
`propext`, `Classical.choice`, `Quot.sound` only, and no `sorryAx`, for

* `Nivat.star_complexity_lower_bound` (Theorem A, §7) and `Nivat.isPeriodic_of_add`
  (Theorem D.1);
* `Nivat.convex_nivat` (Theorem 8.18) and `Nivat.nivat_conjecture` (Corollary 8.19).
  Re-checked on 2026-10-01 from a fresh build of the exported package (see `DELIVERY.md`).

| File | Paper |
|---|---|
| `Nivat.Defs.Config` | §0.1, §0.3 — configurations, `T^u`, `Per`, `π_i` |
| `Nivat.Defs.Complexity` | §0.2 — `P_θ(Q)`, lattice convexity |
| `Nivat.Defs.StarConfig` | §0.1, §0.3 — the axioms (S1)–(S3), `Γ`, `κ_i`, `H_i` |
| `Nivat.Defs.Orbit` | §2.1, §8 — orbit closures, local functions, subsequential limits |
| `Nivat.Chord` | lattice geometry of chords of a lattice-convex set (Appendix D) |
| `Nivat.Words` | one-dimensional words: the two-sided finite-state lemma |
| `Nivat.MorseHedlund` | one-dimensional words: Morse–Hedlund, `P(n) ≤ n → periodic` |
| `Nivat.PeriodCount` | the trace `Tr(y)` and finiteness of `{y : Tr(y) ≤ P}` (§8.4) |
| `Nivat.SubseqLimit` | existence of subsequential limits along a cofinal set (§8.4) |
| `Nivat.OrbitTransfer` | transfer of pointwise properties along `orbitClosure` |
| `Nivat.RayOrder` | planar angular order: `det₂`, `InFirstHalf`, angular minima (§8.4) |
| `Nivat.Laurent.*` | `ℂ[T₁^±, T₂^±]`: domain, UFD, Newton polygons, Ostrowski; the monomial spanning set of `R/(A, B)` (`SublatticeBasis`, Lemma 5.2 Step 2), the coprimality tools of `BinomialCoprime` (Lemma 5.2 Step 1), the CRT-shaped ideal arithmetic of `QuotientGlue` (Lemma 5.2 Step 3) and the monomial bookkeeping of `MonoShift` (Proposition 5.3) |
| `Nivat.Lattice.*` | primitive vectors, zonotopes, `R_Z(S)`, unimodular triangulation |
| `Nivat.Dichotomy` | §1 — Lemmas 1.1, 1.2, Proposition 1.3, hypothesis (1.1) |
| `Nivat.Spectrum` | §2 — spectral projections, `A(T)`, `Z`, the encoding, `U_S` |
| `Nivat.Background` | §3 — the doubly periodic background `A(T) e = b` |
| `Nivat.Witness` | §4 — `f_i = Q_i ψ ≠ 0`, the two-point witness `J(d, ·) ≠ 0` |
| `Nivat.BiRecursion` | §5 — the bi-recursion, `R/(a, c)`, the witness lands in `Z − Z` |
| `Nivat.ZonotopePair` | §6 — `(Z − Z) ∩ ℤ² = (Z ∩ ℤ²) − (Z ∩ ℤ²)` |
| `Nivat.MainTheorem` | §7 — **Theorem A**, `Nivat.star_complexity_lower_bound` |
| `Nivat.AppendixD` | Appendix D — Theorem D.1, the `𝔽_p`/convex form of Szabados' theorem |
| `Nivat.Section8.*` | §8 — the reduction, ending in `Nivat.nivat_conjecture` |
| `Nivat.External.Colle.*` | Proved prerequisites: generating sets, ambiguity counting, half-plane uniqueness, directional rigidity and Proposition 2.12 |

The three results the paper quotes from the literature were formerly declared as axioms:
the Kari–Szabados product-shift theorem (`kari_szabados_prodShift`) and Colle's two structure
theorems (`colle_doublyPeriodic`, `colle_region`).  All three are now proved in the repository
and their axiom declarations are gone: Kari–Szabados in `KSAnnihilator`, `KSDecomposition` and
`KSCorollary`; Colle under `Nivat.External.Colle` (`Theorem114Final`, `ColleRegion`), wired into
the main chain by `Nivat.Section8.ExternalDischarged`.  `lakefile.toml` builds every module
under `Nivat/` (`globs = ["Nivat", "Nivat.+"]`), and the whole tree has zero `sorry`.

The statements have been compared against the preprints (Kari–Szabados, arXiv:1605.05929;
Colle, arXiv:1909.08195v4):
`colle_region` is deliberately weakened, dropping the source's `(ℓ, ℓ')`-region structure in
favour of the more general `IsLatticeConvexRegion`. The numbering in the cited published
version differs from the preprint; comparing only the preprint cannot certify that mapping:

* Theorem 8.6 cites "[2, Theorem 1.9]".  In the preprint that statement is **Theorem 1.14**
  ("if for every line through the origin at least one of the two orientations fails to be a
  one-sided nonexpansive direction, then the configuration is fully periodic"); the preprint's
  own Theorem 1.9 is an unrelated Kari–Moutot result.
* Theorem 8.7 cites "[2, proof of Lemma 4.6]".  The preprint has **no standalone Lemma 4.6** —
  beware, "4.6" does occur there, but as a *Claim* inside a proof.  The `(ℓ, ℓ')`-region is
  constructed in the proof of the preprint's **Lemma 4.5**, by Claim 4.6 in its Case 1 and the
  symmetric Claim 4.11 in its Case 2.

The present Colle formalization uses the explicit arXiv v4 numbering. Published-version
retrieval and citation checks are recorded separately from mathematical proof certification.

Note for contributors: `lake env lean <file>` does **not** apply the `[leanOptions]` of
`lakefile.toml`, so it typechecks with `autoImplicit := true` and can accept a file that
`lake build` then rejects.  Verify with
`lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false <file>`.

Second note, the more expensive one: **never leave a file in a non-compiling state** — stub the
unfinished proof with `sorry` instead.  A `lake build` that fails on a module *deletes that
module's `.olean`*, which breaks every file importing it; and because `lake env lean` itself
triggers a dependency build, each such attempt re-fails and re-deletes.  Restoring the artifact
from a backup therefore cannot win that race: the only recovery is source that compiles.
Relatedly, `lake env lean` writes no `.olean` (it has no `-o`), so "my file elaborates clean"
does not refresh what importers read — only `lake build` does.
-/
