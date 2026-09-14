# MI-32: a proof through parity counts and positive walk polynomials

Research checkpoint: 2026-09-13--14. Status: complete proof draft;
independent analytic reviews, six bounded exact suites, and the joint
integrity audit passed. The statement below is the original general-law
target, including nonsymmetric entry laws. These are research reviews,
not journal peer review or a formal proof-assistant certification.

Let X=(X_ij) be a real n-by-n matrix with independent mean-zero entries,
all absolute moments finite, and
\[
 \|X_{ij}\|_{2r}\le\alpha\|X_{ij}\|_r\qquad(r\ge1).
\]
Define
\[
 M(X)=\max_i\Big(\sum_j\mathbb EX_{ij}^2\Big)^{1/2}
      +\max_j\Big(\sum_i\mathbb EX_{ij}^2\Big)^{1/2},
\]
\[
 D(X)=\max_{1\le k\le n}\min_{I\subset[n],\ |I|\le k}
       \sup_{\|s\|_2,\|t\|_2\le1}
       \left\|\sum_{i,j\notin I}X_{ij}s_it_j\right\|_{\log(k+1)}.
\]
The same deterministic I deletes rows and columns. The exponent at
k=1 is log 2, with its actual subunit moment functional. Then
\[
 \boxed{c_\alpha\{M(X)+D(X)\}\le\mathbb E\|X\|
                         \le C_\alpha\{M(X)+D(X)\}.}
\]
The new contribution is the upper bound. The lower bound is the
established Theorem 4.1 of
[Latala--Swiatkowski, Norms of Randomized Circulant Matrices](https://arxiv.org/html/2106.03139v2).
The exact statement is also recorded in the
[MI-32 problem](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/main/matrix-inequalities-and-norms/MI-32/README.md).

## The complete reading path

1. [Positive-cone local theorem](regular_law_positive_cone.md) proves
   the new analytic estimate, retaining every original magnitude and
   variable identity. It includes proofs of the cone moment inequality,
   the two occupation decompositions, and the vacuum iteration.
2. [Exact deletion and nonsymmetric-law reduction](regular_law_deletion.md)
   verifies the published local-to-deletion implication for these inputs,
   preserves the original index budget and log(k+1), and removes law
   symmetry with constants depending only on alpha.
3. [Joint verification record](verification_audit.json) records independent
   analytic reviews, the scopes of exact finite checks, source hashes,
   and preservation of the preceding checkpoints. These checks are
   supporting evidence, not a formal proof-assistant certification.

## The substantive contraction

For symmetric entries write Y_e=epsilon_e Z_e in law, with independent
original signs and magnitudes. Keep the signs as parity flags and leave
ALL magnitude powers in the polynomial coefficients. A current-row to
current-column creation block fixes the row counts of its OUTPUT flags;
it involves at most k+1 original rows at parity grade k. An annihilation
block instead fixes the column counts of its INPUT flags and involves
at most k original columns. Both are exact orthogonal decompositions in
conditional sign Fourier coordinates. Magnitude spectators outside those
rows or columns are retained.

A vector polynomial F of degree d with nonnegative coefficients in the
ORIGINAL monomial basis satisfies
\[
 \|F\|_{L_4(\ell_2)}\le(\sqrt3\alpha^2)^d\|F\|_{L_2(\ell_2)}.
\]
Interpolation makes the loss absolute in the horizon at the Holder
exponent used with p=4q and d<q. A net only on the at-most-q selected
rows or columns has constant cost at that p. The established
independent-coordinate strong/weak moment theorem bounds each fixed
vector image through its variance and the SAME matrix's weak moment.

Consequently, on this degree-limited cone,
\[
 \|T F\|_2\le C_\alpha\{\sigma(Y)+R_Y(4q)\}\|F\|_2,
 \qquad \deg F<q.
\]
Every actual vacuum iterate T^j e_v is in the cone: it is an ordered
walk polynomial with nonnegative integer coefficients. Iterating the
bound and taking the exact vacuum trace yields
\[
 (\mathbb E\|Y\|^{2q})^{1/(2q)}
   \le C_\alpha n^{1/(2q)}\{\sigma(Y)+R_Y(4q)\}.
\]
At q comparable to log n this is the required local estimate. The final
reduction supplies the exact deletion formulation above.

## What this establishes for the original research motivation

This is an analytic advance obtained from the same mechanism as the
original project: exact randomness, occupation localization, and a
contraction that is justified on the states reached by subsequent
interactions. The state space may be enormous; its enumeration is not
part of the proof or claimed to be efficient.

For weighted signs, the separate
[count-localization theorem](weighted_sign_localization.md) gives a
full creator norm bound and a positive vertex-variance Gram budget,
which survives later input maps by its actual congruence. The
[cycle interface bridge](cycle_transfer.md) identifies the SAME weighted
Boolean inclusion operator in an original graph lift and a marked
Parseval/consumed-SRHT interface. It also shows exactly why distinct
child-pair Grams must remain after a later creation and row equality.

The general-law proof requires nonnegative original polynomial
coefficients. Arbitrary noncommuting coefficient insertions need not
preserve this cone. Thus the theorem does not declare the complete
three-model analytic calculus finished, nor does it infer matching
quantiles from the moment estimate. The prior Jacobi-cutoff and static
proxy counterexamples remain valid: the proof uses neither reduction.

## Comparison with existing methods

The comparison is against the precise local upper target stated in
[Latala's weighted-sign paper](https://arxiv.org/html/2405.13656v2) and
the general-law formulation in the MI-32 source. The former proves
binary weights and retains an iterated-logarithmic loss for arbitrary
weights; [Meller's extension](https://arxiv.org/html/2512.23673v2) retains
an iterated-logarithmic loss for general symmetric regular entries.
The new proof supplies the local estimate with constants depending only
on alpha. Boolean hypercontractivity, strong/weak moment comparison,
the published deletion reduction, and the existing lower estimate are
credited dependencies. No exhaustive priority or publication claim is
made for the present draft.
