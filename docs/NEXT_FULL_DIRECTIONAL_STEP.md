# Completed target: the full raw directional contractions

This step, bipartite assembly, and actual vacuum iteration are now proved.
Continue from `LOCAL_SYMMETRIC_MOMENT_CHECKPOINT.md`. The derivation below
is retained as a guide to the formal proof; it is no longer unfinished work.

The original theorem remains `MI32.main_upper`. Do not restart the thin
estimate or the individual count-sector estimates: they are now proved.
This next step discharges the intermediate premises of
`PolynomialEnergyAssembly.second_moment_le_of_all_sectors`.

Use the same rectangular original matrix X, raw coefficient array
c : R -> K -> Real with c >= 0, and exponents nu : R -> K -> R x C -> Nat.
Assume every raw degree is at most d < q and q >= 1. Keep the original-law
independence, symmetry, regularity, and all-positive-moment assumptions.
Let M = 2*5^(1/4)*(B + 6*alpha^4*W)*(sqrt(3)*alpha^2), with the applicable
original row or column variance budget B and bilinear weak moment bound W
at order 2q. M is nonnegative under the existing premises.

## Creation

The output polynomial has coefficients `RawDirectionalActions.creationCoeff
c nu` and exponents `RawDirectionalActions.actionExponent nu`. Use label type
Nat x (R -> Nat), with

- input label (i,S) = (S.card+1, creationLabel i S);
- output label (j,T) = (T.card, rowCount T).

For each label (m,delta), prove its output second energy is at most M^2 times
the corresponding input second energy.

If m = k+1, `RawCountBlocks.creation_count_block` identifies the masked
output coefficients with creationCoeff applied to
`maskCoeff (ActiveCountSectors.creationMask k delta) c nu`.
`RawSectorNorms.creation_sectorAction_eq` then identifies its actual vector
with the one bounded by `CreationSectorContraction.sectorAction_l2_le`.
For k < q that theorem gives the rooted moment inequality. Square it using
nonnegativity and `MI32.moment_nat_pow` at order 2 to obtain the required
second-integral inequality.

For k >= q the input mask is identically zero: a surviving parity S has
cardinality at most the old raw degree, at most d < q. Use
`RawParity.parity_card_le_degree` at each original term. The exact count-block
identity makes the output sector zero too. This is a coefficient argument,
not a probabilistic bound.

For m = 0 the input label is impossible, and creation cannot produce empty
parity: the original appended edge was absent, so the new parity contains
it. Prove both masked coefficient arrays vanish directly.

Apply `PolynomialEnergyAssembly.second_moment_le_of_all_sectors` to conclude
the full raw creator L2 bound with factor M and no sector-count loss.

## Direct annihilation

Use the raw annihilation coefficient array and the same updated exponents.
The label type is Nat x (C -> Nat), with

- input label (i,S) = (S.card, colCount S);
- output label (j,T) = (T.card+1, annihilationLabel j T).

For label (k,delta), `RawCountBlocks.annihilation_count_block` identifies the
masked output with the raw annihilator applied to annihilationMask k delta.
`RawSectorNorms.norm_raw_annihilation_eq_sectorAction` identifies its full
norm with the selected-column norm controlled by
`AnnihilationSectorContraction.sectorAction_l2_le`. The latter allows k <= q;
it derives the active-column budget itself and also handles k = 0.

For k > q use the same old raw-degree argument to prove the input mask zero;
the count-block identity again makes the output mask zero. Square the checked
rooted inequalities and apply the exact finite-sector energy assembly.
Do not transfer the creator cone estimate by taking adjoints.

## After these two estimates

The raw product is the sum of the raw creator and annihilator by
`RawDirectionalActions.evaluate_product_split`. Their L2 triangle inequality
pays at most the sum of the row and column constants. Opposite bipartite
directions have orthogonal output coordinate spaces; formalize this before
iterating actual matrix powers.

`PositiveWordExtension` supplies exact raw degree increment and nonnegative
coefficient closure under each actual ordered multiplication. Its linear-entry
version handles zero blocks of the dilation without inventing an original
edge. Use these facts for the actual vacuum prefixes and then the trace bound.
The deletion, logarithmic endpoint, dilation-budget and general-law copy
symmetrization steps still follow afterward; do not replace them by desired
estimate hypotheses.
