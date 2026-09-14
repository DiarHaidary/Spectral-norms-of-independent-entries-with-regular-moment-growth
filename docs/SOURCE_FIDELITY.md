# Correspondence with MI-32

This is a formalization of the informal proof checkpoint of 13–14 September
2026. The original target is retained verbatim and is proved in Lean:
`MI32.main_upper` has no proof gap and its transitive axiom audit reports only
`propext`, `Classical.choice` and `Quot.sound`. The earlier agent reviews and
exact numerical suites are not part of that evidence.

Problem source: [MI-32, Open Problems in NLA](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/main/matrix-inequalities-and-norms/MI-32/README.md),
read on 14 September 2026. The source still labels the problem partially
resolved. Its target is the upper bound; the reverse bound is a credited
existing theorem, not part of the selected Lean target.

| Source requirement | Lean statement |
|---|---|
| Every alpha at least one | `main_upper (α : ℝ) (hα : 1 ≤ α)` |
| Positive constant independent of dimension and laws | `∃ C, 0 < C ∧ UpperBoundAt α C`; all matrix/law quantifiers occur inside `UpperBoundAt` |
| Arbitrary probability space | An arbitrary type `Ω`, measurable space and probability measure; no finite-outcome assumption |
| n at least one | `∀ n, 1 ≤ n → ...` |
| Independent original ordered entries | `iIndepFun` indexed by `Fin n × Fin n` |
| Mean zero | Each entry's Bochner integral is zero |
| All absolute moments finite | Integrability of `|X_ij|^p` for every positive real p |
| Regularity at every real r at least one | `moment μ (2*r) ... ≤ α * moment μ r ...` |
| Euclidean spectral norm | Norm of `Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap` |
| Row and column variance maxima | Two suprema over the finite index type in `varianceScale` |
| Same deterministic deletion set | `deletedBilinear` uses the identical `I` in both sums |
| Supremum outside moment | `weakMoment` takes a real supremum of scalar moment values over deterministic unit-ball vectors |
| Min over sets of cardinality at most k | The `sInf` in `deletionScale` |
| Max over 1 ≤ k ≤ n | The outer `sSup` in `deletionScale` |
| Literal log(k+1), including log 2 < 1 | `Real.log (k + 1 : ℕ)` and the real-power moment functional |
| No symmetry or identical distribution | Neither assumption occurs in `RegularEntries` |

The finite maxima/minima use ordinary real `sSup`/`sInf`, not an
algorithmically chosen deletion set. Their boundedness and attainment are
proved in `WeakMomentBasics`. Integrability in the hypotheses prevents the
entry moments from being silently represented by the default value of an
undefined Bochner integral, and the integrability of the matrix norm is
derived, not assumed, in `SymmetricDeletion.integrable_and_mean_spectralNorm_le`.

`StatementChecks.lean` checks the Euclidean norm identification, the
subunit first exponent, and that deleting all original indices gives
zero weak moment for every positive exponent. `RegularWitness.lean` adds a
non-vacuity check: an independent fair-sign matrix on a product of fair coins
satisfies `RegularEntries` at the extreme parameter `α = 1` and has
`varianceScale = sqrt n > 0`, so the universally quantified hypothesis class is
neither empty nor confined to laws with a zero right-hand side. These are
statement checks; neither is used in the proof of the upper estimate.

## Two deliberate divergences from the informal draft

The formal deletion argument does not follow the draft step for step. Both
changes are strengthenings of the formal development's self-containedness, and
neither weakens the statement being proved.

1. **The far remainder avoids an external matrix theorem.** The draft's
   remainder step invokes a variance-envelope estimate derived from
   [Latała–van Handel–Youssef, Theorem 4.4](https://web.math.princeton.edu/~rvan/dimfr180821.pdf#page=32),
   following [Latała–Świątkowski, Remark 4.5](https://arxiv.org/html/2106.03139v2#S4).
   Formalizing that route would require a one-sided version of a
   Gaussian-comparison theorem with two-sided polynomial moment growth, which
   the regular entries here need not have. The Lean proof instead raises the
   per-coordinate screening threshold from `b^2` to `b^3`, which makes the
   off-diagonal Gram pair energies summable, and bounds the far part by an
   elementary centered Gram second moment
   (`GramEntryMoments`, `FarRemainderMoment`). Nothing from that paper is
   formalized or assumed.
2. **No matrix-symmetric dilation.** The draft performs the deletion argument
   on `H_Y`, whose reflected entries repeat variables, and then pays a paired
   dilation budget. The Lean proof performs the whole decomposition on the
   original rectangular matrix, using one shared deterministic index family on
   both axes — which is exactly what the source functional `deletionScale`
   already quantifies over. Every entry family used is therefore genuinely
   independent, the `k = 1` dilation endpoint never arises, and
   `SymmetrizationReduction.upperBoundAt_of_symmetric` is applied directly.

The explicit constant `SymmetricDeletion.deletionConstant (2 * α) * exp 1` is
conservative and not optimized; the source problem asks only for existence of
a constant depending on `α`.

## Analytic sources, and what is not formalized

- Latała and Strzelecka, [Comparison of weak and strong moments for vectors
  with independent coordinates](https://arxiv.org/abs/1612.02407), Theorem
  1.1: cited by the informal draft. It is **not** formalized here and **not**
  used: `HilbertComparison.lean` proves the direct
  independent-coordinate comparison the argument actually needs.
- Latała and Świątkowski, [Norms of randomized circulant matrices](https://arxiv.org/abs/2106.03139):
  Remark 4.5 is the structural model for the deletion reduction, and
  Theorem 4.1 is the known lower estimate. Neither is formalized; the lower
  estimate is credited and is not part of the selected target.
- Latała, van Handel and Youssef, [Theorem 4.4](https://web.math.princeton.edu/~rvan/dimfr180821.pdf#page=32):
  cited by the draft, avoided by the formal proof as described above. Not
  formalized, not assumed.
- Latała, [On the spectral norm of Rademacher matrices](https://arxiv.org/abs/2405.13656),
  and Meller, [Spectral norm of matrices with independent entries up to
  polyloglog](https://arxiv.org/abs/2512.23673): comparison points discussed
  in the bundled informal source. Not used.
- Scalar Boolean fourth-moment hypercontractivity is reused from the supplied
  GraphMatrices Lean development, with source hashes and licence. Its Hilbert
  extension is proved here.

This package makes no publication-priority, independent human refereeing,
Palomar acceptance, or novelty claim. Comparator and NanoDa have not been run
(they require `landrun` and `systemd-run`, absent on this host). Matching
moments are not used to claim matching quantiles.
