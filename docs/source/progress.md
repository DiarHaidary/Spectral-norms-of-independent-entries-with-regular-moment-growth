# Continued research: cyclic interfaces, parity counts, and MI-32

Checkpoint started 2026-09-13 and continued 2026-09-14. The full MI-32
proof draft passed its independent analytic reviews, all six bounded
exact suites, and the joint integrity audit.
The authoritative statement and short reading path are in
[MI32_solution.md](MI32_solution.md). This progress note explains the
mathematical changes, their relation to the original three proofs, and
the exact boundaries of the results.

## 1. The shared bottleneck and the change in scope

The preceding [occupied-profile checkpoint](../mi32_profile_2026-09-13/README.md)
left arbitrary interacting short cycles and a sharp full-law amplitude
contraction open. Its heavy bounds required forests, high girth, or a
supplied feedback budget; its static three-point proxies failed the
Gaussian-star calibration. Those statements and counterexamples remain
preserved as historical checkpoints.

The present work started with the SAME original K_(a,2) family across
three tasks: exact cycle geometry, an extension-sensitive Parseval/SRHT
transfer, and original-entry moment multiplicities. The exact rung
analysis exposed an occupation-count invariant that extends to arbitrary
bipartite support. Combined with established strong/weak vector moments
and a small-row net, it supplied the weighted-sign local theorem.

The general-law extension retains parity as the orthogonal coordinate
and keeps all magnitude powers in the coefficients. A positive-cone
moment inequality then controls the actual vacuum walks. This resolves
the old obstruction without discarding it: it avoids a uniform norm on
the full Jacobi polynomial span and does not use a static moment proxy.

## 2. Recovery map for the original analytic motivation

The motivating proofs remain the four original TeX sources named by the
user; none has been edited. The existing archive contains the detailed
original recovery map. The following map states what THIS checkpoint
adds and what it does not claim.

| Original mechanism | Information that must survive | Current usable bridge | Remaining scope |
| --- | --- | --- | --- |
| SparseStack's shared-factor Gram and additive dimension--occupation dependence | The actual Parseval coefficient Gram and original exceptional/ordinary occupation swaps | The marked rung interface is an exact weighted Boolean inclusion map; its collective norm and positive predecessor-difference budget survive with the actual coefficient blocks | The hypotheses on supplied marks and Parseval rows are explicit; the result is not a theorem for arbitrary nonlinear coefficient updates |
| Two-round SRHT's collective rows and positive selector assembly | Original consumed row maps, child occupations, and distinct child-pair Grams | The same inclusion operator appears after the actual consumed maps; the squared allowance is (s+1)^2/n^2 times the primitive allowance; an exact next-creation/row-equality example tests the retained boundary | Equality of original row inputs does not identify different original random entries or different child-pair maps |
| Graph Matrices' original-edge creations and cancellations | Original edge identity, current vertex, ordered coefficient products, and the relevant occupation constraints | Exact simple-cycle boundaries, rung Gram blocks, and arbitrary-support count localization; a sharp independent-entry norm application follows | This does not claim a new proof of every connected-creation cancellation or separator theorem for all polynomial graph matrices |

The substantive two-model lemma is in
[cycle_transfer.md](cycle_transfer.md). For the supplied normalized rung
coefficients a_i^2+b_i^2=1, both the original graph interface and the
marked Parseval cross contain the SAME weighted inclusion operator
D_q(kappa), kappa_i=a_i b_i, acting from q exceptional half-rungs to
q-1 exceptional half-rungs while the total number M of half-rungs stays fixed.
Its collective estimate is
\[
 \|D_q(\kappa)\|^2\le
       \min(q,M-q+1)\sum_{i=1}^M\kappa_i^2.
\]
For equal absolute kappa the exact squared norm is
q(M-q+1)kappa^2. This is derived from the original operators, rather than
assumed as a model-specific target bound. On the consumed child vacuum
with all rows, the exact scale is ||D_q||^2/n^2; at child grade s the
positive allowance is (s+1)^2/n^2 times the primitive one.

The permitted continuation keeps the actual child-pair Gram. In the
Walsh-four example, the next two creations and equality of the original
row inputs give H_21=-H_30 and ||H_21||^2=1/8. The primitive matching-plus
input is killed, whereas the actual continued operator has squared norm
36/625 on that matching-plus input with a suitable unit row vector.
No finite scalar multiple of the primitive pair
Gram can upper-bound this new Gram. This is an explicit obstruction to
the wrong retained descriptor, on the same original variables.

## 3. Exact cycle geometry and its arbitrary-support consequence

[cycle_fiber_geometry.md](cycle_fiber_geometry.md) derives all-grade
K_(a,2) output and input Grams, with full/half rungs and their actual
parity sectors. Adjacent Boolean layers carry the off-diagonal
inclusion operator. For equal unit rungs the relevant two-layer
Gram has top eigenvalue f+n+1, with the stated return masks handled
separately. The raw-state classifications are not presented as one
common rooted family; the root-distance calibration keeps connector
costs explicit.

Even all-positive coefficients do not justify folding different
occupation columns together. The note gives the exact lost positive
channel and a weighted example where uniform folding reduces the norm.
It also treats a genuine Parseval row insertion R: R*R=I alone does
not preserve the output count blocks. On the unit K_(a,2) vacuum,
R(1)=(1,...,1)/sqrt(a) gives a factor-a failure of output-count pinching.
The legitimate budget follows instead from RR*<=I, or a supplied
diagonal majorant RR*<=diag(g_i), before applying the creator.

The key general consequence is exact. In a row-to-column creation
output Gram, two outputs share a predecessor only by exchanging two
edges in the SAME original row. The full row-count vector is invariant.
A grade-k block therefore involves at most k+1 original rows, and is
an actual submatrix-creator compression. The transposed direction
localizes columns. No copies of edge variables or probabilistic union
over row subsets are introduced.

For weighted signs, [weighted_sign_localization.md](weighted_sign_localization.md)
then proves
\[
 \|C_k(B)\|\le A\{\sigma(B)+R_B(4(k+1))\}.
\]
At a common horizon q and k<q it also supplies
\[
 C_k^*C_k\preceq4A^2\{V_B+R_B(4q)^2I\}.
\]
The latter follows by normalizing the actual input row or column
variance. It keeps the positive boundary needed under a subsequent
input congruence and supplies the preceding heavy-profile bridge for
arbitrary weighted-sign support. This removes the forest/girth/feedback
restriction for that input class.

## 4. The full regular-law contraction

[regular_law_positive_cone.md](regular_law_positive_cone.md) proves the
new local estimate. For symmetric original entries Y_e=epsilon_e Z_e,
write each vector polynomial as sum_S epsilon_S F_S(Z). All original
magnitude exponents remain; sign annihilation still MULTIPLIES by Z_e
and raises the ordinary polynomial degree.

For independent alpha-regular magnitudes and nonnegative monomial
coefficients, moment doubling implies
\[
 m_e(u+v)\le\alpha^{2(u+v)}m_e(u)m_e(v).
\]
Together with conditional Boolean hypercontractivity this yields
\[
 \|F\|_4\le(\sqrt3\alpha^2)^d\|F\|_2
\]
for degree-d coordinatewise positive-coefficient polynomials. Parity,
current-coordinate and occupation-count projections preserve this
cone and its total-degree bound. Orthogonality comes from signs; it
does not require magnitude monomials on different rows to be orthogonal.

Creation uses the occupied ROW count of its output. Annihilation uses
the occupied COLUMN count of its input. Each direction thus reduces
to multiplication by a matrix with at most q original rows or columns
on degree<q input polynomials. A deterministic net on that small axis,
the independent-coordinate strong/weak theorem, and Holder give a
constant cost at p=4q. Squared energies sum over exact orthogonal
sectors; there is no amplitude-selected maximum moved through an
expectation. The separate
[conditioning note](full_law_conditioning_frontier.md) explains why
that alternative exchange would be false.

Only the actual positive vacuum iterates are contracted. This proves
\[
 (\mathbb E\|Y\|^{2q})^{1/(2q)}
 \le C_\alpha n^{1/(2q)}\{\sigma(Y)+R_Y(4q)\}.
\]
The [final reduction](regular_law_deletion.md) converts this into the
EXACT MI-32 mean estimate. It verifies the published symmetric-matrix
local-to-deletion implication, pays for deleting both copies of an
original index in a dilation, handles log 2 explicitly, and treats
mean-zero nonsymmetric entry laws by X-X'. The regularity constant
becomes at most 2alpha, M becomes sqrt(2)M, and D increases by at most e.
All constants therefore depend only on the original alpha.

The existing source lower theorem supplies the other inequality for
the SAME original matrix. No matching quantile conclusion is inferred.

## 5. The cycle and multiplicity work retained alongside the endpoint

[ordered_cycle_boundary.md](ordered_cycle_boundary.md) proves the exact
off-diagonal simple-cycle boundary A tensor W+(A tensor W)*, with
W*W=P_-, WW*=P_+, W^2=0. Its norm is ||A|| on the stated uncompressed
tensor block, and its absolute value is the corresponding positive
block budget. Masks and arbitrary input congruences are charged.
Chronological identification of formerly distinct original labels
must be reevaluated: a square word becomes a vacuum projector in the
explicit identified example. This is not an algebra quotient of the
old distinct-label relations. The underlying nilpotent numerical-radius
fact is standard and is credited.

[cycle_multiplicity.md](cycle_multiplicity.md) retains the exact product
tilt by original entry powers. Repeated square excursions update each
used entry's count, and overlapping cycles share that updated count.
The rooted length-eight square has ten chronological words, giving
the stated conditional variance-profile budget. Gaussian row stars
recover product_h(d+2h), whereas forgetting a repeated rung loses
factors 9, 81, and larger repeated-cycle moments. These results remain
useful exact diagnostics even though the endpoint proof no longer
requires a separate cycle-by-cycle classification.

## 6. Ambitions, useful regime, and limits

The full MI-32 theorem advances the PRIMARY analytic ambition on all
independent real entries with the stated regular moment growth. Its
useful moment regime includes q comparable to log n. It removes the
remaining iterated-logarithmic loss in the local estimate and explains
which occupation information makes the contraction possible.

The original graph/Parseval inclusion bridge advances the same ambition
on a supplied marked interface and records its permitted continuations.
It does not require enumerating the entire state space, and it also
exhibits an explicit failure of a proposed simpler retained Gram.

The exact suites advance the SUPPORTING computational ambition by
checking the precise original-label identities, cone bookkeeping and
continuation witnesses that the proofs use. No efficient algorithm
for evaluating D(X), R_X(p), or the whole polynomial state space is
claimed. No fresh tractable subclass has been substituted for the
primary analytic goal.

Arbitrary noncommuting coefficient insertions can destroy coordinatewise
monomial positivity. The theorem therefore does not complete every
aspect of the broad three-model calculus, all lower-witness constructions,
or quantile estimates. Those are separate possible future research tasks;
they are not prerequisites for the stated MI-32 mean theorem.

## 7. Verification and preservation

The [joint audit](verification_audit.json) records all analytic reviews,
each exact suite's scope and source hashes, the new artifact hashes, and
ten earlier checkpoint integrity checks. Its status is the authority
for the final combined verification. Finite examples do not establish
the universal theorem; the complete analytic arguments and their primary
dependencies are the proof.

The original four TeX sources, the restart guide and the preceding
frozen research checkpoints have been preserved. LATEST.md is the
mutable navigation pointer and is excluded from immutable hashes.
No archive-wide rereading, external posting, or shutdown was performed.
