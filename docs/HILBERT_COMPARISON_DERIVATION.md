# Direct independent-coordinate Hilbert moment comparison

This is a complete analytic derivation, recorded on 14 September 2026.
The finite even-order bound (1) is now proved in Lean as
`MI32.HilbertComparison.independent_coordinate_moment_le`, together with
the actual independent-copy and symmetric-sum ingredients below. Its
transitive axiom audit uses only standard foundations. The real-order
extension at the end remains an analytic derivation, not a claimed Lean
theorem. No originality claim is made, and full MI-32 remains unfinished.

The result needed for the thin-matrix argument is a comparison for a
Euclidean vector with **independent coordinates**. It does not require
the strong–weak comparison for arbitrary Banach-space images or arbitrary
index sets. The coordinate restriction is used in the even-moment
expansion below.

## Exact finite-order statement

Let J be a finite set, let (Omega, mu) be an arbitrary probability space,
and let V_j be measurable real random variables indexed by J. Assume:

1. The family (V_j) is independent.
2. Each V_j has a symmetric distribution: V_j and -V_j have the same law.
3. Fix an integer q >= 1. Every absolute moment of V_j of order at most
   4q is finite. It suffices to assume the moment of order 4q is finite,
   since the measure is a probability measure.
4. For some beta >= 0 and every integer 1 <= r <= q,

   \[
   \|V_j\|_{4r}\le\beta\|V_j\|_{2r}.
   \]

Here \(\|Z\|_s=(\mathbb E|Z|^s)^{1/s}\). Set

\[
R=\left(\sum_jV_j^2\right)^{1/2},\qquad
\sigma^2=\sum_j\mathbb EV_j^2,
\]

and, for s >= 1, set

\[
W_s=\sup_{\sum_jt_j^2\le1}
       \left\|\sum_jt_jV_j\right\|_s.
\]

Then

\[
\boxed{\quad \|R\|_{4q}\le\sigma+2\beta^2W_{2q}.\quad} \tag{1}
\]

There are no dimension factors. The finite-order assumptions contain
neither the conclusion nor any vector moment estimate.

All these quantities are finite. Indeed, R <= sum_j |V_j| pointwise,
and Minkowski controls the latter in every needed order. Every unit-ball
coefficient satisfies |t_j| <= 1, so

\[
0\le W_s\le\sum_j\|V_j\|_s<\infty.
\]

The supremum set is nonempty because t = 0 is admissible. It is a
supremum of deterministic real numbers; no measurability of a random
supremum is required. If J is empty, all quantities are zero and (1)
holds. The following proof also covers this case with the usual empty
sum conventions.

## Independent symmetric even-moment comparison

Suppose (A_j) and (B_j) are two independent families of symmetric real
random variables, each having the required moments through order 2q.
The two families may be defined on different spaces, or on the same
space with arbitrary dependence **between** the families. Assume c >= 0
and

\[
\mathbb E A_j^{2r}\le c^{2r}\mathbb E B_j^{2r}
\qquad(1\le r\le q).
\]

Then

\[
\mathbb E\left(\sum_jA_j\right)^{2q}
\le c^{2q}\mathbb E\left(\sum_jB_j\right)^{2q}. \tag{2}
\]

To prove this, expand the ordinary integer power by the multinomial
formula. Independence factors each monomial expectation into
\(\prod_j\mathbb E A_j^{k_j}\). Symmetry and integrability make every
odd scalar moment zero. The surviving k_j are all even, their scalar
moments are nonnegative, and each multinomial coefficient is a
nonnegative integer. Multiply the coordinate inequalities for these
terms. Exponent-zero factors are one by probability normalization,
and the powers of c multiply to c^(sum_j k_j) = c^(2q).
Summing proves (2). No comparison of absolute coefficient expansions
is being substituted for this calculation: the odd terms vanish
exactly, and the remaining terms are nonnegative.

All monomials in this calculation are integrable. This follows either
from independence and integrability of the individual powers or from
the finite-order Holder inequality, since sum_j k_j = 2q. In particular,
the expansion is an equality of ordinary finite real integrals.

## Proof of (1)

Work on the product probability space carrying an independent copy
(V'_j) of the entire vector (V_j), and define

\[
A_j=V_j^2-(V'_j)^2,\qquad B_j=V_jV'_j.
\]

The coordinate pairs (V_j, V'_j) are independent as j varies. Hence the
A_j are independent, and the B_j are independent. Each A_j is symmetric
by exchange of the two copies. Each B_j is symmetric because the law of
V_j is symmetric and its copy is independent. These are distributional
arguments; there need not be a measure-preserving sign-flip map on the
original sample space.

For every integer 1 <= r <= q, Minkowski and coordinate regularity give

\[
\begin{aligned}
\|A_j\|_{2r}
&\le 2\|V_j^2\|_{2r}
 =2\|V_j\|_{4r}^{\,2}\\
&\le 2\beta^2\|V_j\|_{2r}^{\,2}
 =2\beta^2\|B_j\|_{2r}.
\end{aligned} \tag{3}
\]

The last equality is exact independence factorization of the two
copies. Raising (3) to power 2r and applying (2) with c = 2 beta^2 yields

\[
\left\|\sum_j A_j\right\|_{2q}
\le2\beta^2\left\|\sum_jB_j\right\|_{2q}. \tag{4}
\]

The A_j have all moments required here because V_j has moments through
4q. The B_j have moments through 2q by product independence (or Holder
using moments through 4q). Thus every use of Minkowski and moment
factorization in (3)–(4) has finite integrals.

Put S = sum_j V_j^2 and S' = sum_j (V'_j)^2. Since E S' = sigma^2,
Jensen applied in the copy coordinate to the convex function
z -> |z|^(2q), followed by integration in the first coordinate, gives

\[
\|S-\sigma^2\|_{2q}
\le\|S-S'\|_{2q}
=\left\|\sum_jA_j\right\|_{2q}. \tag{5}
\]

The needed sections are integrable: S and S' have moment 2q and
|S-S'|^(2q) is bounded by a fixed finite multiple of
|S|^(2q) + |S'|^(2q). Fubini/Tonelli is therefore legitimate.

For a fixed deterministic vector v', homogeneity in the definition of
W_(2q) implies

\[
\left\|\sum_jv'_jV_j\right\|_{2q}
\le W_{2q}\,\|v'\|_2. \tag{6}
\]

If v' = 0, both sides of (6) are zero. Otherwise take
t = v'/||v'||_2, which has Euclidean norm one, and pull the positive
scalar ||v'||_2 outside the scalar moment. Raise (6) to power 2q,
integrate over the independent copy, and take the 2q-th root:

\[
\left\|\sum_jB_j\right\|_{2q}
\le W_{2q}\,\|R\|_{2q}. \tag{7}
\]

This step is integration of a deterministic scalar moment bound, not
a use of a coefficient chosen using the first copy of V. The two
copies are independent, and the inner law is always the original law
of V. The integrand is a measurable finite polynomial before taking
absolute powers; product integrability follows, for example, from
|sum_j V_j V'_j| <= R R' and finite moments of R and R'.

Let x = ||R||_(4q) and y = ||R||_(2q). Both are nonnegative. The identity
||S||_(2q) = x^2, Minkowski, (4), (5), and (7) show

\[
x^2
\le\sigma^2+2\beta^2 W_{2q}y
\le\sigma^2+2\beta^2 W_{2q}x, \tag{8}
\]

where the last inequality is monotonicity of probability-space moments
y <= x. All root and power identities hold also when a moment is zero.

For nonnegative x, sigma, and a, the inequality x^2 <= sigma^2 + ax
implies x <= sigma + a. Indeed, if x > sigma + a, then
x(x-a) > sigma^2, contradicting the assumed inequality; this also
covers sigma = 0 or a = 0. Apply this with a = 2 beta^2 W_(2q) to obtain
(1). No division by x, sigma, W_(2q), or an individual moment is used.

## Every real order p >= 2

Assume all positive coordinate moments are finite and

\[
\|V_j\|_{2r}\le\beta\|V_j\|_r
\qquad\text{for every real }r\ge2.
\]

For a given real p >= 2, choose the positive integer q = ceil(p/4).
Then 4q >= p and 2q <= p. For 2 <= p <= 4 one has q = 1. For p >= 4,
the bound q <= p/4 + 1 gives 2q <= p/2 + 2 <= p. Applying (1) and
moment monotonicity therefore yields

\[
\boxed{\quad \|R\|_p\le\sigma+2\beta^2W_p,
       \qquad p\ge2.\quad} \tag{9}
\]

Only regularity at the even integer orders 2, 4, ..., 2q was used for
this particular p. The stated all-real-order assumption is convenient
for reuse and is supplied by the scalar regularity step. In the usual
single-constant format, (9) gives
||R||_p <= max(1, 2 beta^2) (sigma + W_p). For beta >= 1 this is
2 beta^2 (sigma + W_p).

## Why the coordinate theorem suffices for thin matrices

For a model with independent, symmetrically distributed matrix entries
and a fixed deterministic row vector s, set

\[
V_j=\sum_i s_i X_{ij}.
\]

Different V_j depend on disjoint sets of independent entries and are
therefore independent. Their laws are symmetric. Once scalar-sum
regularity has been proved with constant beta depending only on the
original entry regularity parameter, (9) applies. Centering and entry
independence give

\[
\sigma^2
=\sum_{i,j}s_i^2\mathbb E X_{ij}^2
\le\|s\|_2^2\max_i\sum_j\mathbb E X_{ij}^2.
\]

For ||s||_2 <= 1, W_p is at most the original matrix's bilinear weak
p-moment, since its test vectors t are precisely an admissible slice
of that supremum. A finite net over s can then be handled separately.
This explanation does not assert that the net argument, scalar-sum
regularity, symmetry transfer, or full MI-32 bound is already formally
complete.

## Minimal proof obligations for the Lean implementation

1. Factor finite polynomial moments of independent scalar variables and
   prove odd moments vanish under equality of the laws of Z and -Z.
2. Derive (2) from the finite multinomial expansion; it is useful to
   permit the A and B families to live on distinct probability spaces.
3. Construct the independent copy using a product measure and prove
   independence of the paired coordinate family.
4. Prove the scalar copy-symmetrization inequality (5), either by Jensen
   in a product coordinate or by the corresponding Lp contraction for
   conditional averaging.
5. Integrate the normalized deterministic weak bound (6), with its
   explicit zero-vector case, to obtain (7).
6. Assemble (8), its elementary quadratic consequence, and the real-p
   rounding argument. Track ordinary moment integrability throughout.

This route replaces the need to formalize an arbitrary-index-set
strong–weak theorem for this independent-coordinate Hilbert step. It
does not replace the other unresolved parts of the MI-32 proof.
