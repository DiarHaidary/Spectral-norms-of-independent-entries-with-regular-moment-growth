# The full regular-law shared-index deletion bound

Date: 2026-09-14. Status: detailed reduction proved from the companion
positive-cone local theorem and the published local-to-deletion implication;
this reduction passed two independent complete analytic reviews. The
companion local proof has separately passed this author's complete analytic
review. Earlier checkpoints remain unchanged.

## 1. Exact statement and dependency boundary

Let X=(X_ij) be a real n-by-n matrix, n>=1, with independent mean-zero
entries, all absolute moments finite, and

\[
 \|X_{ij}\|_{2p}\le\alpha\|X_{ij}\|_p,\qquad p\ge1.
 \tag{1}
\]

Put

\[
 \sigma_r(X)=\max_i\Big(\sum_j\mathbb EX_{ij}^2\Big)^{1/2},\quad
 \sigma_c(X)=\max_j\Big(\sum_i\mathbb EX_{ij}^2\Big)^{1/2},\quad
 M(X)=\sigma_r(X)+\sigma_c(X),\quad
 \sigma(X)=\max(\sigma_r(X),\sigma_c(X)).
\]

For a deterministic set I subset [n] and any p>0 define

\[
 R_{X,I}(p)=\sup_{\|s\|_2,\|t\|_2\le1}
   \Big\|\sum_{i,j\notin I}X_{ij}s_it_j\Big\|_p,
 \qquad R_X(p)=R_{X,\varnothing}(p),
\]
\[
 \boxed{D(X)=\max_{1\le k\le n}\ 
   \min_{I\subset[n],\ |I|\le k}R_{X,I}(\log(k+1)).}
 \tag{2}
\]

All logarithms are natural. The SAME original set I deletes rows and
columns. The minimum is outside the deterministic-vector supremum;
it is attained because the set of possible I is finite. The k=n term
is zero, and the k=1 exponent remains log 2, strictly below one. L_p
at that exponent denotes the stated moment functional, not a norm.

The conclusion is

\[
 \boxed{c_\alpha\{M(X)+D(X)\}
       \le\mathbb E\|X\|
       \le C_\alpha\{M(X)+D(X)\}.}
 \tag{3}
\]

The lower inequality is the existing Theorem 4.1 of
[Latala and Swiatkowski, Norms of Randomized Circulant Matrices, v2](https://arxiv.org/html/2106.03139v2).
The upper inequality follows below from the symmetric local theorem in
[regular_law_positive_cone.md](regular_law_positive_cone.md). The only
additional matrix-level input is the established local-to-deletion
implication in Remark 4.5 of the same primary source. We verify its
hypotheses, matrix symmetry convention, and exact original-index
conversion explicitly. We do not use a general-law statement merely
because the weighted-sign special case was proved.

## 2. Uniform scalar moment doubling down to log 2

Let S=sum_e a_e Z_e, where the Z_e are independent mean-zero variables
obeying (1), and the coefficients a_e are deterministic real numbers.
There is a constant J_alpha depending only on alpha such that

\[
 \|S\|_{2p}\le J_\alpha\|S\|_p,
 \qquad p\ge p_*:=\log 2.
 \tag{4}
\]

Here is a proof covering the small exponents as well. Set
K_alpha=max(3,alpha^4) and v=E S^2. Independence and zero means imply

\[
 \mathbb ES^4
 =\sum_e a_e^4\mathbb EZ_e^4
   +6\sum_{e<f}a_e^2a_f^2\mathbb EZ_e^2\mathbb EZ_f^2
 \le K_\alpha v^2.
 \tag{5}
\]

This expansion does not require symmetry: terms with an exponent one
vanish. Regularity at p=2 bounds each fourth moment by alpha^4 times
the squared variance. If v=0, (4) is immediate. Otherwise
Paley-Zygmund applied to S^2 gives

\[
 \mathbb P\{|S|\ge\sqrt{v/2}\}\ge(4K_\alpha)^{-1},\qquad
 \|S\|_p\ge2^{-1/2}(4K_\alpha)^{-1/p_*}\sqrt v
       \quad(p\ge p_*).
 \tag{6}
\]

For p in [p_*,2], monotonicity and (5) yield

\[
 \|S\|_{2p}\le\|S\|_4
 \le\sqrt2 K_\alpha^{1/4}(4K_\alpha)^{1/p_*}\|S\|_p.
 \tag{7}
\]

For p>=2, apply Corollary 1.4 of
[Latala and Strzelecka, Comparison of weak and strong moments for vectors with independent coordinates](https://arxiv.org/pdf/1612.02407)
to the singleton set consisting of the coefficient vector of S. It
gives (4) with C_3(alpha)2^beta, beta=max(1/2,log_2 alpha). Thus one
may take J_alpha to be the maximum of this constant, the constant in
(7), and one. This scalar use of the primary theorem requires only
regularity at orders at least two.

Taking the supremum in (4) over bilinear coefficients, on any fixed
original submatrix, gives

\[
 R_{X,I}(2p)\le J_\alpha R_{X,I}(p),\qquad p\ge\log2.
 \tag{8}
\]

The assertion is uniform in I, n, and all the entry laws. No exchange
of a minimum and a supremum is used.

## 3. From the positive-cone moment theorem to the exact local order

First let Y have independent symmetric entries satisfying (1). The
companion theorem gives, for each integer q>=1,

\[
 (\mathbb E\|Y\|^{2q})^{1/(2q)}
 \le2B_\alpha n^{1/(2q)}\{\sigma(Y)+R_Y(4q)\}.
 \tag{9}
\]

For n>=2 set p_n=log(n+1)>1 and q=ceil(p_n). Then
q>=log n, q<=2p_n, and 4q<=8p_n. Consequently n^{1/(2q)}<=sqrt(e),
and three applications of (8) imply

\[
 \mathbb E\|Y\|
 \le L_\alpha\{\sigma(Y)+R_Y(\log(n+1))\},
 \quad L_\alpha=2B_\alpha\sqrt e\max(1,J_\alpha^3).
 \tag{10}
\]

For n=1, E|Y_11|<=sigma(Y), so increasing L_alpha to at least one
makes the same bound valid. Deleting deterministic rows and columns
preserves independence, symmetry, and (1), so this local theorem
applies to every square submatrix with its own dimension and weak
moment. Rectangular matrices may also be padded with deterministic
zero entries when needed.

## 4. The matrix-symmetric version required by the source implication

The proof of Remark 4.5 uses matrix-symmetric inputs. We now establish
the local hypothesis for that convention, rather than identifying
independent transposed variables. Let A=A^T be m-by-m, with the
upper-triangular variables including the diagonal independent and
symmetric in law, all satisfying (1). The lower triangular entry is
the SAME variable as its upper triangular reflection. Put

\[
 a(A)=\max_i\Big(\sum_j\mathbb EA_{ij}^2\Big)^{1/2},\qquad
 \mathcal R_A(p)=\sup_{\|s\|_2,\|t\|_2\le1}\|s^TAt\|_p.
\]

Write A=U+U^T+D_0, where U is strictly upper triangular and D_0 is
diagonal. U has independent entries (including deterministic zeros),
and both its maximum row and column standard deviations are at most
a(A). For p>=1,

\[
 R_U(p)\le\mathcal R_A(p).
 \tag{11}
\]

To verify (11), fix s,t. Independence and symmetry allow the signs of
the coefficients s_i t_j, i<j, to be absorbed in the corresponding
independent upper-triangular variables. Increase their absolute
coefficients from |s_i t_j| to
|s_i||t_j|+|s_j||t_i|, and include the diagonal coefficients
|s_i||t_i|. Scalar symmetric contraction for the convex function
|x|^p shows that the resulting L_p moment does not decrease. The
resulting sum is exactly |s|^T A |t|, whose moment is at most
mathcal R_A(p). This contraction follows directly by conditioning
on every magnitude and averaging its independent sign. It needs
p>=1; it will not be used at log 2.

For m>=2, p_m=log(m+1)>1, and

\[
 \mathbb E\|D_0\|=\mathbb E\max_i|A_{ii}|
 \le m^{1/p_m}\max_i\|A_{ii}\|_{p_m}
 \le e\mathcal R_A(p_m).
 \tag{12}
\]

Thus (10)--(12) and ||U^T||=||U|| give

\[
 \mathbb E\|A\|
 \le2L_\alpha a(A)+(2L_\alpha+e)\mathcal R_A(\log(m+1)).
 \tag{13}
\]

In (10) we used sigma(U)<=a(A), so no extra factor two is needed
for the two variance maxima. For m=1 the direct bound
E|A_11|<=a(A) applies. Every principal submatrix satisfies the same
argument, with its own a and weak moment.

In fact the local hypothesis also holds for any square submatrix
A[P,Q], even when P differs from Q, if the source phrase "any square
submatrix" is read literally. Split it according to original indices
i<j, i>j, and i=j. Each strict piece has independent entries.
For a fixed bilinear coefficient, its absolute coefficient on an
unordered pair is at most the coefficient of |s|^T A[P,Q]|t|;
the latter includes the two reflected positions whenever both are
present. The same conditional symmetric contraction proves the
needed weak-moment domination. Its row and column variances are
bounded by those of the full submatrix. The diagonal piece is a
partial matching, so its norm is the maximum of at most m original
diagonal magnitudes and is handled by (12). The one-by-one case is
again direct. The principal version alone suffices for the diagonal
blocks in the source decomposition. If one of those blocks carries a
symmetric zero-one entry mask, it is still a matrix with independent
upper-triangular entries and the same regularity parameter. The same
absolute-coefficient contraction proves that its weak moment is at
most that of the unmasked block for p>=1; its variances also decrease.

## 5. Applying the published local-to-deletion implication

For a matrix-symmetric A with independent upper-triangular entries,
define its deletion functional by the exact expression (2), using
mathcal R rather than R. Remark 4.5 of
[the v2 primary source](https://arxiv.org/html/2106.03139v2)
establishes that the local estimate with order log(m+1), valid on
the square submatrices, implies

\[
 \mathbb E\|A\|\le Q_\alpha\{a(A)+D_{\rm sym}(A)\}.
 \tag{14}
\]

Its auxiliary moment and variance estimates are stated for independent
mean-zero upper-triangular entries with (1). Our symmetric-law class
is a subclass. Equation (13), including the random diagonal bound,
establishes the missing local hypothesis for this exact class. No
Rademacher-only result is invoked in (14).

For clarity about applicability of the source argument: its
permutation selects nested deterministic deleted sets, its two large
pieces consist of principal diagonal blocks, and its remainder is
controlled using entry standard deviations and regular moment growth.
The blocks inherit (1), and their strong moments follow from the
same primary strong/weak theorem used in the companion proof.
When passing from block dimension to moment order one may choose
each block moment order proportional to log of its dimension; those
orders grow geometrically. The adjacent deleted-set logarithm differs
by only an absolute factor, handled by (8). Summing the resulting
tail bounds has an absolute cost. Thus this application does not
require a local theorem uniform in arbitrary input polynomials, nor
any parity structure for the matrix-symmetric A itself.

The constant Q_alpha may depend on L_alpha and the regularity
constant, and therefore only on alpha. We use the published
implication as a matrix-level theorem; the new local input and the
original-index conversion below are proved separately here.

## 6. Dilation preserves the original variables and the original D

Return to a matrix Y with independent symmetric entries, and form
its actual symmetric dilation

\[
 \mathcal A_Y=\begin{pmatrix}0&Y\\Y^T&0\end{pmatrix}.
 \tag{15}
\]

This is 2n-by-2n. Its independent upper-triangular nonzero variables
are precisely the original Y_ij; its lower half repeats each variable
only in its own symmetric reflection. In particular
||mathcal A_Y||=||Y|| and a(mathcal A_Y)=sigma(Y).
Equations (13)--(14) apply and give

\[
 \mathbb E\|Y\|\le Q_\alpha
       \{\sigma(Y)+D_{\rm sym}(\mathcal A_Y)\}.
 \tag{16}
\]

For any random rectangular matrix Z, including dependent entries,
the weak moments of its dilation satisfy

\[
 \mathcal R_{\mathcal A_Z}(p)=R_Z(p),\qquad p\ge1.
 \tag{17}
\]

The lower bound selects the opposite coordinate halves. For the
upper bound, write s=(s_r,s_c), t=(t_r,t_c). Minkowski bounds the
two bilinear sums by

\[
 R_Z(p)\{\|s_r\|_2\|t_c\|_2+\|t_r\|_2\|s_c\|_2\}
 \le R_Z(p)\|s\|_2\|t\|_2.
\]

No independence between the two sums is assumed. We do not assert
(17) below one.

Fix a dilation deletion budget k>=2 and let ell=floor(k/2). Choose
an original minimizer I with |I|<=ell for
R_{Y,I}(log(ell+1)). Delete BOTH copies of I in the dilation:
I_tilde=I union (n+I), with |I_tilde|<=2ell<=k. The surviving matrix
is exactly the dilation of Y[I^c,I^c]. Since

\[
 \log(k+1)\le\log(2\ell+2)\le2\log(\ell+1),
\]

(17), monotonicity, and (8) imply

\[
 \min_{|J|\le k}
   \mathcal R_{\mathcal A_Y[J^c,J^c]}(\log(k+1))
 \le J_\alpha R_{Y,I}(\log(\ell+1))
 \le J_\alpha D(Y).
 \tag{18}
\]

The moment on the dilation side is at least log 3>1; the original
comparison moment may be log 2, which is why Section 2 was necessary.
Here 1<=ell<=n, including the endpoint ell=n where deletion of all
original indices gives zero.

For the remaining dilation budget k=1, simply choose no deletion
and use monotonicity followed by (17) at p=2:

\[
 \min_{|J|\le1}
  \mathcal R_{\mathcal A_Y[J^c,J^c]}(\log2)
 \le\mathcal R_{\mathcal A_Y}(2)
 =R_Y(2)
 =\max_{i,j}(\mathbb EY_{ij}^2)^{1/2}
 \le\sigma(Y).
 \tag{19}
\]

The exact equality for R_Y(2) uses independence and zero means,
followed by maximizing sum_ij E Y_ij^2 s_i^2 t_j^2. Combining
(18)--(19) proves

\[
 D_{\rm sym}(\mathcal A_Y)
 \le\max\{\sigma(Y),J_\alpha D(Y)\}.
 \tag{20}
\]

Therefore the full exact deletion upper bound holds for symmetric
entry laws:

\[
 \mathbb E\|Y\|\le C_\alpha\{M(Y)+D(Y)\}.
 \tag{21}
\]

Only the original set I is used in D(Y). The intermediate cost of
deleting both dilation copies is explicitly paid by moment doubling;
it is not silently changed to separate original row and column
deletions.

## 7. Mean-zero entry laws without symmetry

Let X' be an independent copy of the full original matrix X and set
Y=X-X'. Then Y has independent symmetric entries. For every p>=1,
conditional Jensen and the triangle inequality give

\[
 \|X_{ij}\|_p\le\|X_{ij}-X'_{ij}\|_p,\qquad
 \|Y_{ij}\|_{2p}\le2\alpha\|Y_{ij}\|_p.
 \tag{22}
\]

Thus its regularity constant is at most 2alpha. Also
M(Y)=sqrt(2)M(X), and conditional Jensen for the operator norm gives
E||X||<=E||Y||.

For a fixed I,s,t, let S=sum_(i,j notin I) X_ij s_i t_j and let S'
be its independent copy. For p>=1, ||S-S'||_p<=2||S||_p. For
p in [log2,1), the pointwise inequality |a-b|^p<=|a|^p+|b|^p gives

\[
 \|S-S'\|_p\le2^{1/p}\|S\|_p\le e\|S\|_p.
\]

Both ranges consequently imply, at every deletion exponent,

\[
 R_{Y,I}(\log(k+1))\le e R_{X,I}(\log(k+1)),\qquad
 D(Y)\le eD(X).
 \tag{23}
\]

The same original deterministic I is used on both sides. Applying
(21) with regularity parameter 2alpha yields

\[
 \mathbb E\|X\|\le\mathbb E\|Y\|
 \le C_{2\alpha}\{\sqrt2 M(X)+eD(X)\}
 \le C'_\alpha\{M(X)+D(X)\}.
 \tag{24}
\]

This is the upper inequality in (3). The independently sourced lower
inequality from Theorem 4.1 applies directly to X, with its original
alpha, so no reverse symmetrization of the subunit moment is needed.

## 8. Endpoints, conclusion, and scope

For n=1, D(X)=0 and E||X||=E|X_11|. The upper bound is Jensen;
regularity at p=1 gives ||X_11||_2<=alpha E|X_11|, hence the lower
bound as well, with M(X)=2||X_11||_2. For n=2, the only possibly
nonzero deletion term is k=1. It concerns a surviving single original
entry and is at most its L_2 norm, hence at most sigma(X). All local
orders used above are at least log 3, and (6)--(8), (19), and (23)
explicitly handle the separate log 2 term. Zero matrices and zero
submatrices satisfy every step directly.

Equation (3) is exactly the mean-norm formulation with original shared
index deletion and constant depending only on alpha in the
[live MI-32 statement](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/main/matrix-inequalities-and-norms/MI-32/README.md).
Its upper half is obtained from the new positive-cone local proof;
its lower half and the local-to-deletion implication are existing
primary results. The argument does not assert matching quantiles,
an efficient algorithm to evaluate D, automatic transfer through
arbitrary coefficient identifications, or a priority claim.

The full mathematical dependency chain is: original-variable positive
cone moment contraction; local mean estimate at log(n+1); the verified
matrix-symmetric local hypothesis; the published full regular-law
local-to-deletion implication; paired dilation deletion; and
symmetrization with its exact small-exponent control. The status at
the top records whether independent review of this final chain has
been completed. No numerical test of a finite family is presented
as a proof of the universal implication.
