# The original-law sector contraction checkpoint

> **Superseded.** `MI32.main_upper` is now proved with no proof gap and no
> added axiom; see [`../README.md`](../README.md) and
> `verification/status.json`. This file is kept as a record of the
> development at the time it was written, and its status lines below are
> historical.

This checkpoint has been extended through full directional summation,
bipartite assembly, actual vacuum iteration, and the local operator-moment
theorem. See `LOCAL_SYMMETRIC_MOMENT_CHECKPOINT.md` for current status.
The remaining-chain discussion below records the earlier sector checkpoint.

Date: 14 September 2026. The selected full theorem is still
`MI32.main_upper`, with its explicit Solution hole. The verification record
identifies the exact compiled and audited source snapshot. This note describes
the new proof chain; it does not assert completion of MI-32.

## The corrected norm comparison

Write U for the conditional Walsh transform, f for the amplitude vector, and
F = U inverse f for the original random polynomial. Parseval identifies only
their L2 norms. Holder must be applied to F, with all original sign and
magnitude variables present. A general Lr norm of f is not interchangeable
with that of F.

Let q be a positive integer, d < q, and let the original independent symmetric
entries X have all positive absolute moments finite and alpha-regular rooted
moments, with alpha >= 1. Let B bound the applicable row or column variance
square root, and W bound every original deterministic bilinear test at order
2q. Define

\[
M_\alpha(B,W)=2\,5^{1/4}(B+6\alpha^4 W)\sqrt3\,\alpha^2.
\]

The actual thin operator has L(4q) norm at most
2*5^(1/4)*(B+6*alpha^4*W). Holder's partner is
r = 2*(4q)/(4q-2). The original positive polynomial of degree d has Lr norm
at most sqrt(3)*alpha^2 times its L2 norm. No independence between the matrix
and the polynomial is used. These are proved in `ThinMatrix`,
`MultiplicationHolder`, `SymmetricConeInterpolation`, and
`ThinPolynomialInteraction`; the direct Hilbert argument discharges the
vector comparison, rather than assuming an external theorem.

## Exact active-axis geometry and projections

`AxisRestriction`, `RestrictedThinMatrix`, and `ThinTranspose` preserve the
original entries, independence, weak tests, and Euclidean norm under the
required row/column restrictions. Adjoint isometry is used for the ordinary
finite matrix transpose norm; it is not used to infer a positive-cone
annihilator estimate from a creator estimate.

For creation, the input mask keeps parity grade k and
delta = rowCount(S) + e_i. Its active rows are the positive coordinates of
delta. Every surviving input row lies there, and there are at most k+1 rows.
`ActiveCountSectors` proves this for the actual raw masks.
`SupportedPolynomialInteraction` restricts only the polynomial's output
coordinates; every exponent still ranges over every original matrix entry.

For annihilation, the input mask keeps grade k and delta = colCount(S).
Its active output columns number at most k. `OutputPolynomialInteraction`
proves the original matrix action into those selected columns directly,
with the full input row space and all original polynomial variables.

`PolynomialSectorMasks` and `PolynomialSectorEnergy` prove that coordinate
and parity masks are exact orthogonal projections for the original-law L2
energy, including signed coefficients. They derive all needed integrability.
Their exact partition identities incur no factor for the number of sectors.
`MaskedPolynomialAction` applies this projection after the literal matrix
product in the original variables.

`CreationSectorContraction.sectorAction_l2_le` and
`AnnihilationSectorContraction.sectorAction_l2_le` combine these results:
each projected sector action has L2 norm at most M_alpha(B,W) times the
original masked input's L2 norm. The active-axis cardinality is derived from
the input grade. An oversized label forces the whole input sector to vanish.
No desired sector or restricted operator estimate is an added hypothesis.

## Preservation under further interactions

`PositiveWordExtension` appends an occurrence of the actual original edge.
It retains the input coordinate and previous term label, adds one to raw
degree, and toggles only the separate sign parity. Later raw masks preserve
coefficient positivity and every original exponent. The linear-entry version
also handles zero entries without choosing an artificial variable.

`RawDirectionalActions` separates absent/present old edge parity in this same
term family. Both directions multiply by the original variable; annihilation
does not reduce raw polynomial degree. The module identifies the conditional
Walsh coefficients with the existing creationApply and annihilationApply.
`RawCountBlocks` identifies the output grade/count projections of actual
extension with those raw directional formulas coefficient by coefficient.
`RawSectorNorms` proves the remaining exact vector/norm identification:
the creator sector is the raw creator, and zero extension recovers the full
raw annihilator from the selected output columns with no norm loss. These
identities do not need positivity or probabilistic hypotheses.

## What remains before the full theorem

The next assembly must use the exact directional identifications with the
sector bounds and sum over their orthogonal labels and grades. The input raw
degree ensures that only grades below q occur. The general finite energy
partition and its finite-sector comparison are available in
`PolynomialEnergyAssembly`; its intermediate sector inequalities must still
be discharged for the exact creator and annihilator. Its existence alone
is not the assembled full directional inequality.

Then formalize the bipartite action, actual positive vacuum prefixes, the
trace/operator moment estimate, and arbitrary-law integrability. The exact
local-to-deletion reduction, shared-index budget, log 2 endpoint, and
independent-copy symmetrization remain substantial obligations. Do not turn
any of them into an assumed desired estimate.

This advances the analytic MI-32 branch and formal verification of its
occupation mechanism. It does not yet unify all three original models or
prove a lower or quantile theorem. The component inequalities are used with
explicit losses; no originality claim is made.
