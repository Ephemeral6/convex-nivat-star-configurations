# A proof of Nivat's conjecture in its convex form

> **A proof of Nivat's conjecture in its convex form**
> Guancheng Pan (1 October 2026)

This repository contains the paper, its LaTeX source, the numerical
verification scripts, and the complete **Lean 4 formalisation** of the proof.

## The theorem

Let `A` be a finite alphabet and `ξ : Z² → A`. For a finite window `S ⊂ Z²`,
`P_ξ(S)` is the number of distinct patterns `ξ|_{u+S}`, `u ∈ Z²`.

**Theorem (convex Nivat conjecture).** If `P_ξ(S) ≤ |S|` for some non-empty
finite lattice-convex window `S`, that is one with `S = Conv(S) ∩ Z²`, then `ξ`
is periodic.

Rectangles are lattice-convex, so this contains **Nivat's conjecture** (1997):
if `P_ξ(m,n) ≤ mn` for some `m, n ≥ 1`, then `ξ` is periodic.

Convexity is exactly the right hypothesis. By Khetan's counterexample the
statement fails for a non-convex window of full affine span. The convex form is
the natural general statement, and it is the one proved here.

## Formally verified in Lean 4

The whole proof is formalised in Lean 4 with Mathlib (`anc/lean`). The
formalisation includes every result the paper quotes from the literature: the
Kari–Szabados annihilator and decomposition theorems, and Colle's results on
one-sided nonexpansive directions and regional full periodicity, together with
Boyle–Lind and Cyr–Kra.

```lean
theorem Nivat.convex_nivat {α : Type*} [Finite α] {ξ : Config α} {S : Finset (ℤ × ℤ)}
    (hne : S.Nonempty) (hS : LatticeConvex S) (hP : P ξ S ≤ S.card) : IsPeriodic ξ

theorem Nivat.nivat_conjecture {α : Type*} [Finite α] {ξ : Config α} {n k : ℕ}
    (hn : 0 < n) (hk : 0 < k) (hP : P ξ (rectangle n k) ≤ n * k) : IsPeriodic ξ
```

- `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for both
  theorems. These are the axioms of Lean's own logic. There is no `sorry`, and
  the development declares no axiom of its own.
- The development has 449 modules and about 216,000 lines. About 192,000 of
  those lines prove the results quoted from the literature.
- An independent rebuild from a clean copy completed all 3368 jobs. Kernel
  replay with `leanchecker` reported no error, both module by module and from
  an empty environment up to the main theorem.
- Formalising Colle's argument exposed one step that does not go through as
  written: the shell sweep in the proof of Lemma 3.5(i) of the arXiv version.
  The formalisation replaces it with a different construction, and the lemma
  itself stands. Appendix E of the paper has the details.

To check it yourself (needs [elan](https://github.com/leanprover/elan), `git`,
`bash` and `gawk`):

```sh
cd anc/lean
lake exe cache get
LEAN_NUM_THREADS=2 lake build
bash scripts/sorries.sh                                  # TOTAL: 0
bash scripts/check_axioms.sh Nivat.nivat_conjecture      # propext, Classical.choice, Quot.sound
```

Use a small `LEAN_NUM_THREADS` on machines with limited memory; a few modules
are large. `anc/lean/DELIVERY.md` maps every definition the statement uses to
its Lean source.

## The proof in one paragraph

**Theorem A** (§§0–7, self-contained) is a complexity lower bound:
`P_θ(S) ≥ |S| + 1` for every *star configuration* `θ = Σᵢ Fᵢ : Z² → F_p` and
every non-empty finite lattice-convex `S`. The proof attaches to `θ` an
exceptional spectrum of roots of unity in each direction, a Laurent polynomial
`A = Πᵢ Aᵢ(T^{vᵢ})` dividing every annihilator, and the zonotope
`Z = Newt(A)`. The zonotope appears twice with opposite signs: as the exact cost
of the affine relations a window carries, and as the exact capacity of a family
of quadratic characters independent of them. The two cancel. **§8** turns a
minimal counterexample to the convex conjecture into a star configuration. It
uses Kari–Szabados and Colle, then proves the two half-planes (Proposition 8.9
and Theorem 8.12) and normalises (Lemma 8.17), contradicting Theorem A.

## How the work was done

The paper and the formalisation were produced by the author together with a
personal AI research system. The system is an orchestration of language-model
agents (Claude Opus 5, with Claude Fable 5.1 on two lanes) running in Claude
Code. It used parallel formalisation lanes, a single integrating agent,
dedicated refutation agents and independent auditors. Appendix F of the paper
records the timeline, the organisation, and every significant error the system
made and how it was caught.

## Contents

| Path | |
|---|---|
| `nivat.tex` | LaTeX source (amsart, inline bibliography, no BibTeX) |
| `nivat.pdf` | compiled paper, 41 pages |
| `anc/lean/` | the Lean 4 formalisation (`DELIVERY.md` explains how to check it) |
| `anc/star.py` | star configurations, spectra, annihilators, zonotopes, affine relations |
| `anc/verify.py`, `anc/verify2.py` | the two randomised experiments of the numerical appendix |
| `anc/lemma31.py` | the counterexample to the over-generalised intermediate lemma |
| `anc/*_output.txt` | the output of the runs reported in the paper |

The scripts need Python 3 and `numpy`. Build the PDF with
`pdflatex nivat.tex` twice.

## Versions

This repository holds the version of 1 October 2026. Earlier versions remain in
the git history.

## License

- The paper, `nivat.tex` and `nivat.pdf`, is licensed under
  [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/). See `LICENSE`.
- The Python scripts under `anc/` are licensed under the MIT License. See
  `anc/LICENSE`.
- The Lean source under `anc/lean/` is released under the Apache 2.0 license,
  as stated in its file headers.

## Citing

```bibtex
@misc{Pan2026nivat,
  author       = {Pan, Guancheng},
  title        = {A proof of {N}ivat's conjecture in its convex form},
  year         = {2026},
  note         = {Preprint, with a Lean 4 formalisation},
  howpublished = {\url{https://github.com/Ephemeral6/convex-nivat-star-configurations}}
}
```
