# The convex Nivat conjecture: a complexity lower bound for star configurations

Source, compiled PDF and verification scripts for the paper

> **The convex Nivat conjecture: a complexity lower bound for star
> configurations, and a reduction that depends on Colle–Garibaldi at one step
> only**
> Guancheng Pan, Chengsong You, Junwei Zhou, Yongchao Chen (11 September 2026)

Nivat's conjecture asserts that a configuration `ξ : Z² → A` over a finite
alphabet with `P_ξ(m,n) ≤ mn` for some `m, n ≥ 1` is periodic. Its *convex* form
replaces the rectangle by an arbitrary non-empty finite lattice-convex window
`S`, that is one with `S = Conv(S) ∩ Z²`.

## Two results, at two different levels

**Theorem T is unconditional and self-contained** (§§0–7 of the paper). Call
`θ = Σᵢ Fᵢ : Z² → F_p` a *star configuration* when each `Fᵢ` has a non-zero
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

**Theorem 8.15 and Corollary 8.16 are conditional, and the condition is carried
in their statements.** The only hypothesis they assume is a weak form of

> [CG, Proposition 3.1(ii)] — C. F. Colle and E. Garibaldi, *A modular structure
> theorem for minimal periodic decompositions and periodicity of configurations
> with `P_η(4,n) ≤ 4n`*, preprint, `arXiv:2606.10193v1` (8 June 2026),

which supplies the *second* of the two half-planes on which each component of a
minimal periodic decomposition is fully periodic. **That preprint has not been
refereed.** The first half-plane is no longer assumed: Proposition 8.9 proves it
here, from Kari–Szabados and from Colle's two published papers, by a one-sided
finite-state argument. What the reduction then contributes is Lemma 8.14: any
decomposition of that shape can be normalised into a star configuration, with no
appeal to `F_p`-minimality or to the distinctness of the directions. Under the
one remaining assumption the paper derives the convex Nivat conjecture, and with
it Nivat's conjecture.

The chain is

```
[KS], [Colle23a] --(Prop 8.9)--> U_i --(Asm 8.12, [CG])--> V_i
      --(Lem 8.14)--> star configuration --(Thm T)--> convex Nivat ==> Nivat
```

Appendix D proves [CG, Theorem 2.8] — the `F_p` and convex form of Szabados'
theorem — in full, that being the one link behind Proposition 3.1(ii) for which
the source gives a sketch rather than a proof. The appendix uses nothing beyond
the one-dimensional Morse–Hedlund theorem. Remark 8.17 records how far a route
avoiding [CG] altogether currently gets, and exactly which propagation lemma is
still missing.

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
refereed. The reading of [CG] reported in Remarks 8.11 and 8.13 — including the
six items (a)–(f) and the checks against Colle's two published papers — is the
authors' own audit record, and is reproduced in the paper as such. Corrections
and counterexamples are welcome; please open an issue.

## License

- The paper, `nivat.tex` and `nivat.pdf`, is licensed under
  [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/). See `LICENSE`.
- The scripts under `anc/` are licensed under the MIT License. See `anc/LICENSE`.

## Citing

```bibtex
@misc{PYZC2026convexnivat,
  author = {Pan, Guancheng and You, Chengsong and Zhou, Junwei and Chen, Yongchao},
  title  = {The convex {N}ivat conjecture: a complexity lower bound for star
            configurations, and a reduction that depends on
            {C}olle--{G}aribaldi at one step only},
  year   = {2026},
  note   = {Preprint},
  howpublished = {\url{https://github.com/Ephemeral6/convex-nivat-star-configurations}}
}
```
