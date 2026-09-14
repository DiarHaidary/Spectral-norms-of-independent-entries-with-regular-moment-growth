# Exact local order and general-law reduction checkpoint

> **Superseded.** This file records the state before the deletion chain was
> completed. `MI32.main_upper` is now proved; the frontier described in the
> last section was closed as specified in
> [`REMAINING_CHAIN_SPEC.md`](REMAINING_CHAIN_SPEC.md), except that the
> variance-envelope route and the paired dilation budget were deliberately
> replaced rather than formalized (see
> [`SOURCE_FIDELITY.md`](SOURCE_FIDELITY.md)). The local-estimate and
> reduction statements below are unchanged and still accurate.

Date: 14 September 2026. The compiled hashes and axiom checks are in
`verification/status.json`; a local Lean result is not a completed Palomar
submission.

## Exact local estimate

`LocalLogMoment.mean_spectralNorm_le_literal` proves, for original independent
symmetric alpha-regular entries on an arbitrary probability space, n >= 1,

\[
\mathbb E\|X\|_{\rm op}
\le C_\alpha\left(M(X)+6\alpha^4J_\alpha^3
 R_{X,\varnothing}(\log(n+1))\right),
\quad C_\alpha=4e5^{1/4}\sqrt3\alpha^2,
\quad J_\alpha=(\sqrt3\alpha^2)^7.
\]

M and R are exactly `Statement.varianceScale` and `Statement.weakMoment`.
The proof derives the variance and weak budgets, all order comparisons,
and operator-norm integrability from the original assumptions.
`SymmetricLinearAllOrders` proves scalar sum doubling at every real
p >= log 2, using actual Holder interpolation at small orders.
This extends the completed [local moment theorem](LOCAL_SYMMETRIC_MOMENT_CHECKPOINT.md).
The constants are conservative, not optimized.

The local right side uses the undeleted weak moment, not `deletionScale`.
Replacing it by the smaller deletion functional is not justified by this
theorem; that is the remaining matrix problem.

## Actual independent-copy passage

On the original product probability space, Y=X-X' has independent symmetric
centered entries, every positive moment finite, and regularity parameter
2 alpha. `GeneralLawCopy` derives all these fields from `RegularEntries`.
`MatrixCopySymmetrization` proves E||X|| <= E||Y|| and both norm integrability
statements, for the literal Euclidean operator.

`VarianceScaleBasics` gives exact finite variance maxima, and
`SymmetrizationReduction.varianceScale_copy` proves M(Y)=sqrt(2) M(X).
`DeletionMomentEndpoints` proves the scalar copy comparison down to log 2.
`WeakMomentBasics` supplies bounded weak-test sets and actual finite
minimizers. `CopyDeletionScale` then proves

\[
D(Y)\le eD(X)
\]

using the same original deterministic minimizing set at every exact budget.
No interchange of minimum and supremum or separate row/column choices occurs.

`SymmetrizationReduction.upperBoundAt_of_symmetric` consequently proves:
a symmetric-law deletion bound at parameter 2 alpha with constant C implies
the full original general-law bound with constant eC. Its symmetric-law
deletion premise remains unproved. It ranges over independent entries
symmetric in distribution, not matrices satisfying X=X^T; it cannot be
applied directly to a lift whose reflected entries repeat variables.

## Ingredients for the remaining decomposition

- `BipartiteWeakMoment`: the actual lift inherits the weak-test bound with
  constant one for p >= 1, with no independence assumption between its two
  bilinear sums. No below-one identity is asserted.
- `DeletionVarianceSelection`: one explicit original set T contains S,
  has cardinality at most |S|+|S|t, and ensures (t+1)v(i,j)<=B^2 for marked
  columns and rows outside T. The selection is monotone in S and covers
  t=0 and B=0; its matrix wrapper uses actual entry second moments.
- `BlockMomentMaximum`: nonnegative block norms with orders p_i>=i+2 and
  a common rooted bound L>0 have mean maximum at most 3L. Integrability is
  derived, with no independence between blocks. The individual block
  estimates are intermediate premises still to be discharged.
- `BlockDiagonalNorm` and `BlockDiagonalMoment`: actual Euclidean block
  diagonal norm is controlled by the maximum block norm. The random block
  matrix is integrable and has mean <=3L under those block moment premises,
  including dependent finite block axes and empty blocks.

Only modules in a successful combined verification record are certified
at their recorded hashes. These block lemmas must still be assembled with
the actual decomposition before strengthening this claim.

## Remaining frontier

Formalize the nested deterministic selection, exact matrix partition,
estimates for the actual blocks and masks, and the remaining matrix piece.
Charge the corrected block moment orders, adjacent deletion budgets, finite
endpoints and all constants. The variance-weighted remainder estimate is a
substantial analytic dependency. The published outline is
[Remark 4.5](https://arxiv.org/html/2106.03139v2#S4), including estimate (29);
its citation is not an available Lean theorem.

Incorporate the earlier block-order correction from the focused analytic
recheck rather than copying its displayed index literally. Paired dilation
deletion and the separate k=1 case also need to be assembled with the original
budget. Prove this symmetric deletion result before applying the checked
general-law reduction to `Solution.lean`.

A separate agent reviewed the local and reduction interfaces and confirmed
these distinctions; this is not a review or proof of the remaining theorem.
Comparator/NanoDa and the other Palomar gates remain separate. No full MI-32,
lower-bound, quantile, novelty, submission or three-model-unification claim
is made.
