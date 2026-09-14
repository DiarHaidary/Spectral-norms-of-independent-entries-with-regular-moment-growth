# Checked work and the proof ledger

The target is `MI32.main_upper`, unchanged from the source problem.
`Solution.lean` now proves it, with no `sorry` and no added axiom: the
transitive audit reports `propext`, `Classical.choice` and `Quot.sound`
only. This file lists the components in the order they were built. Being
listed here is not itself evidence; `verification/status.json` records
which files and declarations Lean actually checked, at their recorded
source hashes.

## Implemented components

1. `MI32/Statement.lean`: the full general-law statement and quantities.
2. `MI32/StatementChecks.lean`: Euclidean norm and deletion-endpoint checks.
3. `MI32/MomentDoubling.lean`: actual integer moments recovered from the
   source's rooted moments; the exact regularity condition implies
   natural-power doubling.
4. `MI32/PositivePolynomial.lean`: original exponent vectors; exact
   multiplication; independence gives actual tensor moment factorization
   and mixed integrability; positive coefficients give the degree-based
   second-moment bound. The scalar Cauchy–Schwarz proof derives the
   pair-moment inequality from doubling.
5. `MI32/HilbertWalsh.lean`: dimension-free Hilbert Boolean fourth moments,
   proved from scalar hypercontractivity and actual pairwise
   Cauchy–Schwarz, without assuming a vector estimate.
6. `MI32/ParityGeometry.lean`: exact row-count creation and column-count
   annihilation labels, grade compressions, coefficients and action sums,
   active-axis bounds, and creator Gram vanishing between distinct
   sectors. Arbitrary amplitudes retain all spectator magnitudes.
7. `MI32/PositiveCone.lean`: the positive energy polynomial is explicitly
   constructed, with positivity and degree accounting; Parseval and
   integrability give the combined sign/magnitude fourth-moment estimate.
8. `MI32/RawParity.lean`: exact expansion of the original polynomial,
   parity-degree bound, and symmetric-difference update under raw exponent
   addition. Original exponents are never replaced by parity alone.
9. `MI32/RawPositiveCone.lean`: the assembled theorem for literal raw
   positive polynomials evaluated at independent signs times original
   magnitudes. All moment assumptions are the actual rooted scalar
   regularity assumption, through `RegularPositiveCone.lean`.

10. `MI32/SymmetricLaw.lean` and `MI32/SymmetricPositiveCone.lean`:
    exact transfer of the full independent symmetric joint law, including
    atoms at zero; the positive-polynomial fourth-moment theorem is stated
    for the original arbitrary symmetric law and the actual Euclidean norm.
11. `MI32/ConeInterpolation.lean`: weighted Holder proves interpolation
    to `2p/(p-2)`, including integrability and the uniform factor at `p=4q`.
12. `MI32/FiniteNet.lean` and `MI32/ThinNetMoment.lean`: construct the
    half-net with cardinality at most `5^dim`; derive the operator integral
    bound with cost `2^p 5^dim` from fixed-vector moments.
13. `MI32/MatrixImages.lean` and `MI32/IndependentColumns.lean`: exact
    centered second moments, the original row variance budget, constant-one
    expectation bound, and genuine independence and symmetry of column sums.
14. `MI32/PositiveLinearPowers.lean`: exact finite-word expansion and
    scalar sum doubling `||S||_(4q) <= sqrt(3) alpha^2 ||S||_(2q)` for
    arbitrary real coefficients in the sign/magnitude representation.
15. `MI32/PositiveMomentComparison.lean` and
    `MI32/SymmetricMomentComparison.lean`: odd moments vanish under actual
    distributional symmetry, and coordinate even-moment comparison
    tensorizes to sums under the actual independent laws.
16. `MI32/CopySymmetrization.lean` and `MI32/HilbertConditioning.lean`:
    Jensen comparison with an actual independent copy, and conditioning
    of the decoupled inner product against deterministic weak moment tests.
    Integrability is derived in both statements.
17. `MI32/DiagonalCopyComparison.lean` and `MI32/HilbertComparison.lean`:
    full independent-coordinate Hilbert comparison from original scalar
    regularity, using actual independent copies. No external vector
    comparison estimate is assumed.
18. `MI32/MomentTools.lean`, `MI32/SymmetricLinearRegularity.lean`,
    `MI32/ThinMomentRoot.lean`, and `MI32/SymmetricConeInterpolation.lean`:
    rooted moment calculus, original-law scalar sum doubling, the explicit
    rooted net cost, and the original-law cone interpolation interface.
19. `ThinMatrix`, `AxisRestriction`, `RestrictedThinMatrix`, and
    `ThinTranspose`: actual original-law thin-matrix moments, exact original
    weak-test restriction, and the direct output-column operator estimate.
20. `MultiplicationHolder`, `ThinPolynomialInteraction`,
    `SupportedPolynomialInteraction`, and `OutputPolynomialInteraction`:
    actual dependent polynomial multiplication, with all original variables
    retained and integrability derived.
21. `PolynomialSectorMasks`, `PolynomialSectorEnergy`, and
    `MaskedPolynomialAction`: raw orthogonal projections and exact partitions
    under the original law, followed by actual multiplication and projection.
22. `ActiveCountSectors`, `CreationSectorContraction`, and
    `AnnihilationSectorContraction`: the active row/column budget follows from
    the count mask; both projected sector contractions are proved directly.
23. `PositiveWordExtension`, `RawDirectionalActions`, `RawCountBlocks`, and
    `ParityWalshCompression`: exact raw multiplication and parity updates,
    original directional Walsh coefficients, and count/grade block identities.
24. `RawSectorNorms`: exact vector/norm identification of the bounded
    projected sectors with the original raw creator and annihilator.
    `PolynomialEnergyAssembly` supplies the intermediate finite-sector
    energy comparison.
25. `RawCreatorContraction` and `RawAnnihilatorContraction`: every sector
    premise is discharged from the actual directional estimates, and
    unreachable grades vanish. Orthogonal energy assembly proves the full
    creator and annihilator bounds without a sector-count loss.
26. `RawMultiplicationContraction`, `TransposedPolynomialContraction`, and
    `BipartiteConeContraction`: actual full multiplication and both matrix
    directions use the same original variables. Orthogonal assembly of the
    bipartite directions incurs no additional factor.
27. `PositiveVacuumWords` and `BipartiteVacuumIteration`: actual matrix-power
    polynomials have nonnegative coefficients and the exact raw degree.
    Applying the contraction at every reachable prefix proves their vacuum
    energy bounds, with integrability derived.
28. `VacuumNormBound`, `BipartiteNorm`, and `LocalSymmetricMoment`: the
    self-adjoint lift's basis energies bound its operator moment and hence
    the original rectangular matrix moment. The full local symmetric-law
    theorem is proved from the original assumptions. Its dimension factor
    counts both sides of the lift; see the quantitative differences in
    [the local theorem checkpoint](LOCAL_SYMMETRIC_MOMENT_CHECKPOINT.md).
29. `SymmetricLinearAllOrders` and `LocalLogMoment`: original scalar sums
    double uniformly down to log 2. The literal local operator mean bound
    uses exactly log(n+1), with variance and weak budgets derived from the
    definitions and all constants explicit. That literal endpoint,
    `LocalLogMoment.mean_spectralNorm_le_literal`, is a companion corollary and
    is not a step in the proof of `MI32.main_upper`: the deletion decomposition
    applies `LocalSymmetricMoment.operator_moment_le` directly at each block's
    scheduled order, and uses only `linearForm_eq_bilinear` and
    `integrable_and_mean_le_even_moment` from this module.
30. `WeakMomentBasics`, `DeletionMomentEndpoints`, and `CopyDeletionScale`:
    actual deterministic minimizers, bounded weak-test sets at every
    positive order, and the exact same-set bound D(X-X') <= e D(X), including
    the first logarithmic order below one.
31. `MatrixCopySymmetrization`, `GeneralLawCopy`, `VarianceScaleBasics`, and
    `SymmetrizationReduction`: original-copy independence and symmetry,
    regularity at 2 alpha, exact variance factor sqrt(2), and the Euclidean
    operator-mean comparison are derived. The full general-law target now
    follows from the still-unproved symmetric deletion theorem.
32. `BipartiteWeakMoment` and `DeletionVarianceSelection`: constant-one lift
    weak-test comparison at p>=1, plus explicit shared original-index
    selection with the proved cardinality and surviving variance bounds.
33. `BlockMomentMaximum`, `BlockDiagonalNorm`, and `BlockDiagonalMoment`: increasing block moments
    control the mean maximum with constant three; the actual block-diagonal
    Euclidean norm is bounded by the maximum block norm without a count loss.
    The actual random block-diagonal norm is integrable and has mean <=3L
    from the explicit individual block moment premises. The decomposition
    still needs to supply those premises for its actual blocks.

34. `DeletionScheduleArithmetic` and `BlockOrderArithmetic`: the explicit
    schedule `budget k = 2^(5^k) - 1`, its order `order k = 5^k log 2`, the
    two-sided step cardinality bound, geometric growth, the finite horizon
    `n <= budget n`, and the scheduled block order
    `blockOrder a = ceil (2 * order (a+1))` with `2 * blockOrder a <= 2^10 *
    order (a-2)`, `a + 2 <= 2 * blockOrder a`, and the absolute bipartite
    dimension factor.
35. `NestedShells`, `WeakDeletionMonotonicity` and `NestedDeletionFamily`: the
    first-shell level of every original index, the exact four-mask pointwise
    partition, deletion monotonicity of the literal weak moment at every
    positive order including below one, and the instantiated nested family with
    its cardinality bound, exhaustion, both variance screens in divided form,
    and one uniform weak screen covering the first stage through the
    budget-one minimizer at exactly `log 2`.
36. `MaskedEntryLaw`: a deterministic zero-one entry mask preserves
    measurability, independence, distributional symmetry, centering, every
    positive absolute moment, the rooted regularity at every real order, the
    unrooted fourth-moment budget, and both variance budgets.
37. `FiberBlockNorm`, `FrobeniusMean` and `BlockMaskMoment`: a matrix supported
    on the diagonal blocks of a fiber partition has operator norm at most the
    maximum block norm, with no factor in the number of blocks; a two-colour
    off-diagonal part of a block is dominated by the block; the rectangular
    Euclidean norm is at most the Frobenius energy; and growing block moment
    orders give the block maximum a mean bound of three times the common
    rooted bound, for a merely nonnegative bound.
38. `CenteredGramNorm`, `GramEntryMoments`, `GradedVarianceEnergy` and
    `FarRemainderMoment`: the operator norm through `Y^T Y`, the centered Gram
    second moments computed from the original independent centered entries and
    their fourth moments, the deterministic summability of the graded variance
    overlaps under the cubic screening threshold, and the resulting far
    estimate `E||Y|| <= B sqrt(1 + sqrt 2 alpha^2)` with derived
    integrability. No general matrix fourth-moment inequality is used.
39. `BilinearHighOrder`, `RestrictedBlockFamily` and `NearBlockMoment`:
    `k`-fold scalar doubling for a deterministic bilinear test; the restriction
    of the original law to a fiber block together with the zero extension that
    identifies a block bilinear test with an original deleted bilinear test;
    and the resulting per-block moment estimate at the scheduled order, with
    the weak input supplied by `deletionScale` through ten doublings.
40. `DeletionMasks`, `NearMaskMean`, `FarMaskMean` and `SymmetricDeletion`: the
    five deterministic masks and their exact partition, the three near means
    and the two far means, and their assembly into the symmetric-law deletion
    theorem at the explicit constant `SymmetricDeletion.deletionConstant`.
    Composing with the previously checked
    `SymmetrizationReduction.upperBoundAt_of_symmetric` discharges
    `MI32.main_upper`.

41. `RegularWitness`: a non-vacuity check on the target's hypothesis class. An
    independent fair-sign matrix on a product of fair coins satisfies
    `RegularEntries` at `alpha = 1` — independence from `iIndepFun_pi`,
    centering from the fair coin, and every absolute moment equal to one — and
    has `varianceScale = sqrt n > 0`. Nothing in this module is used by the
    proof of `MI32.main_upper`.

The machine record in `verification/status.json` identifies which files
and declarations were successfully checked at its recorded source hashes.
Ongoing additions are not certified merely by being mentioned here.

## The chain that closed the gap

1. Two-sided deterministic selection at the explicit schedule, its cardinality
   calculation, exhaustion at the finite horizon, and weak-set monotonicity:
   `NestedDeletionFamily`.
2. The exact shell masks and the disjoint near/far partition, the
   maximal-shell common support condition, and the finite pair count and
   summability of the graded overlaps: `NestedShells`, `GradedVarianceEnergy`.
3. Original independent-entry Gram means, the centered second moments and
   their integrability, with nothing about the final Gram estimate assumed:
   `GramEntryMoments`.
4. Euclidean operator-to-Frobenius comparison and the centered Gram transfer,
   including norm integrability: `CenteredGramNorm`, `FarRemainderMoment`.
5. The near blocks reindexed into the checked local theorem with their masks
   and variables preserved, the fixed logarithmic ratio charged through ten
   doublings, the initial block handled separately by its entry energy, and
   the growing-order block maximum assembled: `NearBlockMoment`,
   `NearMaskMean`.
6. A constant depending only on `alpha`, and `MI32.main_upper` discharged
   without `sorryAx` or any extra axiom: `SymmetricDeletion`, `Solution`.

The paired dilation deletion and its separate `k = 1` case, listed as
obligations in the earlier plan, are **not** part of the final proof: the
decomposition is performed directly on the original rectangular matrix with
one shared index family on both axes, so the dilation is never formed. See
[the fidelity account](SOURCE_FIDELITY.md).

## Simplification discovered during formalization

Write `m(r) = E Z^r` for nonnegative Z. For positive integers u,v,
Cauchy–Schwarz and moment doubling give

\[
m(u+v)^2 \le m(2u)m(2v)
 \le \alpha^{2(u+v)}m(u)^2m(v)^2.
\]

Thus `m(u+v) ≤ α^(u+v) m(u)m(v)`, stronger than the draft's
`α^(2(u+v))` bound. Zero exponents follow from probability normalization.
This avoids the entropy argument in the draft. The existing polynomial
constant is retained conservatively; the old source is preserved verbatim.

## Palomar completion gate

The layout follows the [current contribution policy](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md),
checked 14 September 2026. The local proof gate has passed: `lake build`,
`lake env lean Audit.lean`, `lake build Challenge Solution` and
`lake env lean FullTargetAudit.lean` all succeed, the audit reports only the
three standard foundations, and `scripts/validate_metadata.py` passes against
the pinned public metadata contract.

Comparator and NanoDa have **not** been run: both require `landrun` and
`systemd-run`, which do not exist on this Windows host. Rendering, editorial
review, registration and submission have not been requested or performed, and
no human peer review of the mathematics has taken place. A successful local
build and axiom audit is a strictly weaker statement than any of those.

What was checked locally in place of Comparator: `Challenge.lean` is
byte-compatible with the prefix of `MI32/Statement.lean` (enforced by
`scripts/verify.py`), and all eight target definitions plus the type of
`MI32.main_upper` elaborate to identical terms in the Challenge and Solution
environments. This does not replace a Comparator run.
