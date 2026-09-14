# Occupation-count localization for arbitrary weighted signs

Date: 2026-09-13. Status: proof passed three independent analytic reviews;
bounded original-support geometry checks passed in the companion suite.
This note concerns independent Rademacher entries with deterministic real
weights. It does not assert the general-law MI-32 conjecture.

## 1. Statement and notation

Let B be a real a-by-b matrix and X=(b_ij epsilon_ij), with one independent
Rademacher sign per original nonzero entry. Put

\[
 \sigma_r=\max_i(\sum_j b_{ij}^2)^{1/2},\qquad
 \sigma_c=\max_j(\sum_i b_{ij}^2)^{1/2},\qquad
 \sigma=\max(\sigma_r,\sigma_c),
\]
\[
 R_B(p)=\sup_{\|s\|_2,\|t\|_2\le1}
       \|\sum_{ij}b_{ij}\varepsilon_{ij}s_it_j\|_{L_p}.
\]
All vectors and operators in this note can be taken real. Independent
signs at transposed positions of a square matrix remain distinct.

On current-vertex and original-edge-occupation states, define
\[
 T_B|v,S\rangle=\sum_{w:vw\in E}b_{vw}|w,S\triangle\{vw\}\rangle,
 \qquad C_k=P_{k+1}T_BP_k.
 \tag{1}
\]
The row and column vertex sets of the dilation are disjoint. P_k selects
sets S with exactly k occupied edges; it imposes no reachability condition.
The coefficient on either direction of an edge is the same original b_ij.

The main bound is
\[
 \boxed{\|C_k\|\le A\{\sigma+R_B(4(k+1))\},\quad k\ge0,}
 \tag{2}
\]
with an absolute constant A. More uniformly, for every q>=1 and k<q,
the right side may use R_B(4q), with the same A.

For a square n-by-n matrix, the consequence is
\[
 (\mathbb E\|X\|^{2q})^{1/(2q)}
 \le 2A n^{1/(2q)}\{\sigma+R_B(4q)\},\quad q\ge1.
 \tag{3}
\]
Thus q=max(1,ceil(log n)) yields the weighted-sign local upper
bound E||X|| <= C(sigma_r+sigma_c+R_B(max(1,log n))).
The moment-order replacement uses ordinary scalar Rademacher moment
comparison, with an absolute factor because the order ratio is bounded.
No matching quantile statement is asserted.

## 2. Exact original-row-count blocks

Write C_k^{r->c} for creation from a current row to a current column.
For an output (j,T), define the complete row-count vector
d(T)=(d_i(T))_i, where d_i(T)=|T intersect ({i} times [b])|.
In its output Gram, two states (j,T),(j',T') have a nonzero common
predecessor only if, for an original row i and a k-edge set S,
\[
 T=S\cup\{(i,j)\},\quad T'=S\cup\{(i,j')\},
 \qquad (i,j),(i,j')\notin S.
 \tag{4}
\]
In particular d(T)=d(T'). The conclusion includes j=j'; these give
the ordinary diagonal terms. Therefore C_k^{r->c}(C_k^{r->c})* is a
direct sum in the FULL row-count vector, with no coefficient estimates.

Fix a nonzero block d and set I={i:d_i>0}. Since sum_i d_i=k+1,
|I|<=k+1. Every occupied edge of every output T lies in I times [b].
Every predecessor (i,T minus {(i,j)}) has i in I and all its flags in
that same original submatrix. Identify its edge labels with the
corresponding labels of B_I=B[I,:], without copying any random variable.
Then the factor producing this entire output block is EXACTLY an output
compression of C_k^{r->c}(B_I). All additional domain states of this
submatrix creator have zero entries on the selected outputs unless they
are one of the original predecessors already described.

Consequently
\[
 \|C_k^{r\to c}(B)\|
 \le\max_{I\subset[a],\ |I|\le k+1}
                \|C_k^{r\to c}(B[I,:])\|.
 \tag{5}
\]
The analogous input-current-column creator obeys the same bound using
at most k+1 original columns. Its domain and range are orthogonal to
those of C_k^{r->c}, so ||C_k|| is the maximum of the two directional
norms. There is no union bound over the possible subsets I: (5) is an
operator direct-sum maximum before any probabilistic estimate.

Diagonal availability or rooted-reachability masks are further
compressions. Non-diagonal equality/identification maps require their
actual congruence and must not be treated as free masks.

## 3. A small-row Rademacher matrix has the required strong moment

The established strong/weak moment theorem for a Banach-valued
Rademacher sum Z states
\[
 \|\|Z\|\|_{L_p}
 \le C_{SW}\left(\mathbb E\|Z\|
       +\sup_{\|f\|_{E^*}\le1}\|f(Z)\|_{L_p}\right),\quad p\ge1.
 \tag{6}
\]
Here C_SW is absolute. This follows from Corollary 3 of
[Dilworth and Montgomery-Smith, The distribution of vector-valued
Rademacher series](https://arxiv.org/pdf/math/9206201), using its scalar
case to identify the weak K-functional with the weak L_p moment.
Finite-dimensional Hilbert spaces are a particular case; no matrix-norm
conjecture is being assumed in this use of (6).

Let |I|=r and fix a deterministic unit s in R^r. The Hilbert-valued
Rademacher sum Z_s=X_I* s has
\[
 \mathbb E\|Z_s\|_2
 \le(\sum_{i\in I}s_i^2\sum_jb_{ij}^2)^{1/2}\le\sigma_r,
 \qquad \sup_{\|t\|_2\le1}\|\langle Z_s,t\rangle\|_{L_p}
       \le R_B(p).
 \tag{7}
\]
Thus (6) bounds its strong moment by C_SW(sigma_r+R_B(p)).
Choose a deterministic 1/2-net N in the row unit sphere, of cardinality
at most 5^r. For EVERY realization, ||X_I||<=2 max_{s in N}||X_I* s||_2.
Therefore, for every p>=1,
\[
 \|\|X_I\|\|_{L_p}
 \le 2\left(\sum_{s\in N}\mathbb E\|X_I^*s\|_2^p\right)^{1/p}
 \le 2\,5^{r/p}C_{SW}\{\sigma_r+R_B(p)\}.
 \tag{8}
\]
The column dimension has not entered the net. When r<=q and p=4q,
its cost is at most 5^{1/4}. Applied to the transpose, the same argument
uses sigma_c for a submatrix with at most q columns.

## 4. Boolean hypercontractivity controls the creator

Boolean Fourier transform sends (1) to multiplication by the
self-adjoint dilation of X. For the directional creator of B_I,
it sends C_k^{r->c} to P_{k+1} M_{X_I*} P_k.
For every Hilbert-valued polynomial f of degree at most k,
\[
 \|f\|_{L_u(\ell_2)}\le(u-1)^{k/2}\|f\|_{L_2(\ell_2)},\quad u\ge2.
 \tag{9}
\]
Indeed the scalar Boolean noise operator is positive and averaging,
so ||N_rho f||<=N_rho||f|| pointwise. Apply scalar hypercontractivity
to the norm of the inverse-noise-scaled f, and use Hilbert Fourier
orthogonality to bound its L_2 norm by rho^{-k}||f||_2. This proves
(9) without a cost in the Hilbert-space dimension. The scalar theorem
used here is [O'Donnell, Lecture 16, Theorem 1.1](https://www.cs.cmu.edu/~odonnell/boolean-analysis/lecture16.pdf).

For p>2 and a unit grade-k f, the output projection is an L_2
contraction and Holder's inequality gives
\[
 \|C_k^{r\to c}(B_I)f\|_2
 \le\|M_{X_I^*}f\|_2
 \le \|\|X_I\|\|_{L_p}\|f\|_{L_{2p/(p-2)}(\ell_2)}
 \le\left(\frac{p+2}{p-2}\right)^{k/2}\|\|X_I\|\|_{L_p}.
 \tag{10}
\]
For p=4q and k<q, the displayed factor is at most sqrt(e):
its logarithm is at most 2k/(4q-2)<1/2.
Combining (5), (8), and (10) gives (2), uniformly with p=4q,
with the explicit admissible constant
\[
 A=2\sqrt e\,5^{1/4}C_{SW}.
 \tag{11}
\]
The other directional creator uses sigma_c instead of sigma_r.

## 5. Exact vacuum moments and the local mean bound

Let K_q=P_{<=q}T_BP_{<=q}. It equals C+C*, where C is the sum of
C_k for 0<=k<q. These grade blocks have orthogonal domains and ranges,
so ||C||=max_{k<q}||C_k|| and ||K_q||<=2 max_{k<q}||C_k||.
Every intermediate state in q iterations from a vacuum root has grade
at most q. Thus K_q^q|v,empty>=T_B^q|v,empty>, including all ordered
coefficient sums with their original variable identities. Fourier
diagonalization gives
\[
 2\mathbb E\operatorname{tr}(XX^*)^q
 =\sum_{v=1}^{2n}\|T_B^q|v,\varnothing\rangle\|^2
 \le 2n\|K_q\|^{2q}.
 \tag{12}
\]
Together with ||X||^{2q}<=tr(XX*)^q this proves (3).
For L=max(1,log n) and q=ceil(L), n^{1/(2q)}<=sqrt(e) and 4q<=8L.
Scalar Rademacher hypercontractivity gives R_B(4q)<=sqrt(15)R_B(L)
when L>=2; for 1<=L<2 one can use the L_1-to-L_2 Khintchine
comparison followed by hypercontractivity to get another absolute
constant. This yields the stated local mean upper bound.

## 6. A vertex-variance Gram budget

The scalar norm argument also yields a positive input budget. Write
V_B(v,S)=sum_{e incident to v}b_e^2 for the diagonal vertex-variance
operator. Fix q>=1, k<q, p=4q, and s=R_B(p). Then
\[
 \boxed{C_k^*C_k\preceq4A^2\{V_B+s^2I\}.}
 \tag{13}
\]
If B=0 this is immediate. Otherwise s>0. For the row-to-column
direction set D_i=sum_j b_ij^2+s^2 and define the ORIGINAL row-scaled
coefficient matrix b'_ij=b_ij/sqrt(D_i). Its maximum row variance
is at most one. Its weak p moment is at most one as well, since
\[
 \|D^{-1/2}\|\le1/s,\qquad
 R_{B'}(p)\le\|D^{-1/2}\|R_B(p)\le1.
\]
The directional proof of (2) uses only the maximum row variance,
so ||C_k^{r->c}(B')||<=2A. The actual operator is
C_k^{r->c}(B')=C_k^{r->c}(B)D^{-1/2}, with D acting on the current
input row, identically in every occupation state. Congruence gives
the row-current part of (13). Normalize original columns for the other
direction and combine the orthogonal input blocks. This proves (13).

For any subsequent bounded input map L, its full positive budget
therefore survives as L*C_k*C_kL <=4A^2(L*V_BL+s^2L*L).
One must retain these actual congruences; an arbitrary L need not
preserve the original count sectors or turn the budget into a scalar
multiple of the same unmodified V_B. An output contraction is harmless
before this input congruence. This is precisely the form needed to
supply the heavy input Gram in the preceding occupied-output-profile
bridge, now without a forest, girth, or feedback-edge hypothesis on a
weighted-sign heavy support. No additional variable identification is
implicit in the row or column normalization.

## 7. Scope, comparison, and verification

The target is exactly the arbitrary-weight local upper bound (1.4) in
[Latala, On the spectral norm of Rademacher matrices, v2](https://arxiv.org/html/2405.13656v2).
That source proves the binary-weight case and an upper bound with a
triple-logarithmic loss for arbitrary weights. Its introduction explains
the standard local-to-shared-index-deletion implication. The argument
above gives the local upper bound without that loss for weighted signs.
The separate deletion-form derivation should be read before invoking
the complete weighted-sign two-sided formulation.

The substantive step is the original count-block reduction (5)
followed by the small-row vector moment argument (8). The auxiliary
occupation space can be enormous. No enumeration cost is claimed to be
small: this is an analytic bound uniform over that space.

Preserved information: all original edge labels, coefficient products,
row/column current direction, and the full output occupation-count
vector. Permitted continuations: further creation uses the next grade
and repeats the same exact decomposition; annihilation is its adjoint;
ordinary basis masks are contractions. Equality identifications and
noncommuting consumed coefficient interfaces need their own positive
Gram treatment, as in the adjacent cycle notes.

This result advances the primary analytic ambition for the graph
lift and the MI-32 weighted-sign input class at moment order comparable
to log n. It does not by itself recover every original Parseval
contraction, nor prove matching quantiles. For arbitrary regular entry
laws, Boolean hypercontractivity in (9) is unavailable in this form;
the frozen raw-Jacobi obstruction remains relevant. The separate
[positive-cone argument](regular_law_positive_cone.md) supplies a
different contraction on the actual full-law vacuum polynomials,
and [the final reduction](regular_law_deletion.md) addresses MI-32.

The three analytic reviews separately checked (4)--(12), the primary
strong/weak theorem, the small-row net, the Hilbert-valued noise step,
all dimension and moment-order factors, and the vacuum normalization.
The vertex-variance addition (13) has a separate review recorded in
the joint audit.

The [companion geometry note](cycle_fiber_geometry.md), Section 9, and
[its exact report](cycle_fiber_geometry_checks.json) test the original
count blocks on a signed, unequally weighted three-by-four support at
grades zero through four: 5,904 count-invariance assertions, 118 blocks,
118 independently rebuilt output sets, and 2,062 exact factor rows.
They do not numerically certify the universal strong/weak or
hypercontractive theorems. Those are analytic dependencies with the
primary sources given above. No full-law or quantile inference is
included in these reviews.
