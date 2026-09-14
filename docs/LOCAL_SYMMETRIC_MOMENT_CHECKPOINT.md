# The local symmetric-law operator theorem is formalized

> **Superseded.** `MI32.main_upper` is now proved with no proof gap and no
> added axiom; see [`../README.md`](../README.md) and
> `verification/status.json`. This file is kept as a record of the
> development at the time it was written, and its status lines below are
> historical.

Date: 14 September 2026. The full selected MI-32 theorem remains incomplete.
The [newer deletion checkpoint](DELETION_REDUCTION_CHECKPOINT.md) adds the
exact local logarithmic order and the proved general-law copy reduction.
The exact compiled source hashes and transitive axiom results are recorded in
`verification/status.json`; local success is not a Palomar submission.

## Proved statement

`MI32.LocalSymmetricMoment.operator_moment_le` proves the following for a
finite rectangular matrix X with original row and column sets R and C, on
an arbitrary probability space. The original entries are measurable,
independent, symmetric, have every positive absolute moment finite, and
satisfy the original alpha-regular rooted moment condition, with alpha >= 1.
Let q >= 1 be an integer. Suppose B >= 0 bounds every row and column variance
square root, and W >= 0 bounds every deterministic Euclidean unit-bilinear
moment of the same X at order 2q. Then

\[
\boxed{
\bigl\|\,\|X\|_{\mathrm{op}}\,\bigr\|_{2q}
\le (|R|+|C|)^{1/(2q)}
\,4\,5^{1/4}\sqrt3\,\alpha^2\bigl(B+6\alpha^4W\bigr).
}
\]

The theorem also proves integrability of the original operator norm to power
2q. No intermediate operator, sector, or vacuum estimate is assumed. The
matrix norm is the literal Euclidean operator norm, and empty axes are allowed.

## Formal proof chain

The direct Hilbert comparison and finite Euclidean net prove the original-law
thin-matrix bound. Exact count labels derive the applicable thin axes.
Holder is applied to the original random polynomial, with its actual Lr norm,
and the output parity projection is an L2 contraction.

`RawCreatorContraction` and `RawAnnihilatorContraction` discharge every sector
estimate and sum exact original-law energies. Unreachable grades vanish
coefficient by coefficient using parity cardinality <= raw degree.
`RawMultiplicationContraction` adds the two actual directional vectors in L2.

`TransposedPolynomialContraction` reindexes, without resampling, the same
original entries and exponents for the reverse direction.
`BipartiteConeContraction` combines the two rectangular actions by orthogonal
row/column energy addition, with no further factor.

`PositiveVacuumWords` constructs actual ordered matrix-power polynomials,
proves nonnegative raw coefficients and exact degree, and uses the same edge
variable in both orientations. `BipartiteVacuumIteration` applies the proved
cone estimate at every prefix and proves the actual vacuum energy bound.
`VacuumNormBound` derives the norm-power/basis-energy inequality and its
integrability and moment consequences. `BipartiteNorm` transfers to the
original rectangular operator with constant one.

## Quantitative differences from the informal draft

The weak-moment order is 2q here; the draft uses 4q with an unspecified general
strong/weak constant. The formal proof instead supplies an explicit constant
through the direct Hilbert comparison.

The formal dimension factor counts both sides of the lift. For an n-by-n
matrix it is (2n)^(1/(2q)), whereas the source uses n^(1/(2q)) after an exact
factor-two trace cancellation. Thus this formal version pays an additional
2^(1/(2q)) <= sqrt(2). This loss is explicit and absolute; the argument does
not claim the source's sharper normalization. At q comparable to log(|R|+|C|)
the displayed dimension factor is absolute.

An independent read-only agent review checked the local statement, original
variable identities, assumptions, and these quantitative differences. It
found no missing analytic premise. This is not independent human peer review
or proof of the remaining deletion theorem.

## Remaining full target

`MI32.main_upper` still has one real Solution hole. The completed local theorem
does not yet prove the deterministic shared-index deletion bound. The scalar
logarithmic endpoints and independent-copy passage are now proved. Continue
the actual local-to-deletion decomposition and paired original index budgets.
Do not add the desired deletion estimate as a premise of the final target.

Continue from the frozen `docs/source/regular_law_deletion.md` and the focused
`Continued/mi32_analytic_recheck_2026-09-14.md`; the index-order repair in that
recheck must be incorporated, with all losses charged. Preserve the original
target and the completed core's separation from Solution and Challenge.

This completes the local symmetric analytic mechanism in the MI-32 branch.
It does not establish the full MI-32 target, a lower/quantile theorem, or
unification across the three original models. No novelty claim is made.
