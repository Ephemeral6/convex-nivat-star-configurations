# The convex Nivat conjecture: a complexity lower bound for star configurations

Source, compiled PDF and verification scripts for the paper

> **The convex Nivat conjecture: a complexity lower bound for star
> configurations, and a reduction from low convex complexity to star
> configurations**
> Guancheng Pan, Chengsong You, Junwei Zhou, Yongchao Chen (11 September 2026)

Nivat's conjecture asserts that a configuration `ξ : Z² → A` over a finite
alphabet with `P_ξ(m,n) ≤ mn` for some `m, n ≥ 1` is periodic. Its *convex* form
replaces the rectangle by an arbitrary non-empty finite lattice-convex window
`S`, that is one with `S = Conv(S) ∩ Z²`.

## Two results

**Theorem T: a lower bound for star configurations** (§§0–7, self-contained).
Call `θ = Σᵢ Fᵢ : Z² → F_p` a *star configuration* when each `Fᵢ` has a non-zero
period `kᵢvᵢ`, is not doubly periodic, and agrees with doubly periodic fields on
the two half-planes `{π_i < ℓ_i}` and `{π_i > r_i}`, the primitive directions
`vᵢ` being pairwise non-parallel. Then

```
P_θ(S) ≥ |S| + 1     for every non-empty finite lattice-convex S.
```

The proof attaches to `θ` an exceptional spectrum of roots of unity in each
direction, a Laurent polynomial `A = Πᵢ Aᵢ(T^{vᵢ})` dividing every annihilator of
`θ` modulo constants, and the zonotope `Z = Newt(A)`. The zonotope then appears
twice with opposite signs — as the exact cost of the affine relations carried by
a window, and as the exact capacity of a family of quadratic characters
independent modulo those relations — and the two cancel for every `S` and
every `Z`.

**Theorem B: the reduction** (§8). A counterexample to the convex conjecture can
be turned into a star configuration, so Theorem T settles the conjecture, and
with it Nivat's. The chain is

```
[KS], [Colle23a] --(Prop 8.9)--> U_i --(Thm 8.12)--> V_i
      --(Lem 8.17)--> star configuration --(Thm T)--> convex Nivat ==> Nivat
```

Both half-planes are proved here. Proposition 8.9 gives the first, by extending
the full periodicity on a region to a doubly periodic field, isolating the
component with a difference operator `Qᵢ`, and closing with a finite-state
argument. Theorem 8.12 gives the second: pushing the configuration to the limit
along the direction of another component, the limit is a sum of two periodic
configurations with different directions, hence periodic by Theorem D.1, so every
limit on the far side of the component under consideration is doubly periodic;
since there are only finitely many such limits, the far side itself coincides
with a doubly periodic field. Theorem 8.1 (each component fully periodic on two
disjoint half-planes) coincides formally with the structure theorem of [CG]; the
proof here is different and uses no minimality of the decomposition.

Apart from the annihilator and periodic decomposition theorem of Kari and
Szabados, and Colle's Theorem 1.9 and Lemma 4.6, every step is proved in the
paper. Appendix D proves in full the `F_p` and convex form of Szabados'
theorem — stated with a sketch as [CG, Theorem 2.8] — using nothing beyond the
one-dimensional Morse–Hedlund theorem.

## Contents

| Path | |
|---|---|
| `nivat.tex` | LaTeX source (amsart, no BibTeX run: the bibliography is inline) |
| `nivat.pdf` | compiled paper, 36 pages |
| `anc/star.py` | the mechanism: star configurations, spectra, annihilators, zonotopes, affine relations |
| `anc/verify.py` | Appendix C.2, Experiment 1 (default `N = 84`, `seed = 1`) |
| `anc/verify2.py` | Appendix C.2, Experiment 2 (default `N = 157`, `seed = 7`) |
| `anc/lemma31.py` | the counterexample of Appendix C.3 |
| `anc/*_output.txt` | the actual output of the runs reported in Appendix C |

`anc/` is the directory uploaded to arXiv as ancillary files.

## Reproducing the numerical appendix

The scripts need Python 3 and `numpy`, nothing else.

```sh
cd anc
python verify.py              # 84 configurations, seed 1
python verify2.py             # 157 configurations, seed 7
python lemma31.py             # the Appendix C.3 counterexample
```

Both experiments accept `N` and `seed` as positional arguments. Across the 241
configurations of the two experiments, on eight windows each, every instance
satisfied `P_θ(S) ≥ |S| + 1`, and the pattern counts were unchanged when the
enumeration box was doubled in radius. The numbers printed in Appendix C are
those of the shipped `*_output.txt` files; where they differ from an earlier
draft, the appendix reports the discrepancy.

## Building the PDF

```sh
pdflatex nivat.tex
pdflatex nivat.tex
pdflatex nivat.tex
```

Three passes, no BibTeX. The preamble sets pdfTeX's reproducibility flags, so
repeated builds of an unchanged source agree byte for byte.

## Status

The paper is a preprint, prepared for arXiv submission; it has not been
refereed. Corrections and counterexamples are welcome; please open an issue.

## License

- The paper, `nivat.tex` and `nivat.pdf`, is licensed under
  [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/). See `LICENSE`.
- The scripts under `anc/` are licensed under the MIT License. See `anc/LICENSE`.

## Citing

```bibtex
@misc{PYZC2026convexnivat,
  author = {Pan, Guancheng and You, Chengsong and Zhou, Junwei and Chen, Yongchao},
  title  = {The convex {N}ivat conjecture: a complexity lower bound for star
            configurations, and a reduction from low convex complexity to star
            configurations},
  year   = {2026},
  note   = {Preprint},
  howpublished = {\url{https://github.com/Ephemeral6/convex-nivat-star-configurations}}
}
```
