# A parity-amplitude contraction on positive walk polynomials

Date: 2026-09-13--14. Status: proof passed three independent analytic
reviews; bounded exact verification is recorded separately.
This note addresses the general symmetric regular-law local MI-32 bound.
It uses the actual entry magnitudes, without a static proxy or an
orthogonal-polynomial cutoff. The separate
[final reduction](regular_law_deletion.md) treats mean-zero nonsymmetric
entries and the exact shared-index deletion formulation. The
[joint audit](verification_audit.json) records the complete proof chain.

## 1. Input, quantities, and theorem

Let Y=(Y_ij) be a real n-by-n matrix of independent symmetric entries.
Assume all absolute moments are finite and
\[
 \|Y_{ij}\|_{2r}\le\alpha\|Y_{ij}\|_r,\qquad r\ge1.
 \tag{1}
\]
Zero entries may be omitted. Write
\[
 \sigma_r=\max_i(\sum_j\mathbb EY_{ij}^2)^{1/2},\quad
 \sigma_c=\max_j(\sum_i\mathbb EY_{ij}^2)^{1/2},\quad
 \sigma=\max(\sigma_r,\sigma_c),
\]
\[
 R_Y(p)=\sup_{\|s\|_2,\|t\|_2\le1}
             \|\sum_{ij}Y_{ij}s_it_j\|_p.
 \tag{2}
\]
The local moment theorem is, for every integer q>=1,
\[
 \boxed{(\mathbb E\|Y\|^{2q})^{1/(2q)}
 \le 2B_\alpha n^{1/(2q)}\{\sigma+R_Y(4q)\},}
 \tag{3}
\]
where
\[
 H_\alpha=\sqrt3\,\alpha^2,\qquad
 B_\alpha=2\,5^{1/4}C_{SW}(\alpha)H_\alpha.
 \tag{4}
\]
Here C_SW(alpha) is the constant in the established strong/weak moment
theorem for independent centered coordinates satisfying (1), stated
precisely in Section 3. It is independent of n, q, and the entry laws.

## 2. Positive-coefficient hypercontractivity

Let W_1,...,W_N be independent symmetric variables obeying (1), and
let F(W) be a polynomial of total degree at most d with values in a
finite-dimensional REAL Euclidean space. Suppose EVERY coordinate
of F has nonnegative coefficients in the ordinary monomial basis of
the ORIGINAL variables W. Then
\[
 \|F\|_{L_4(\ell_2)}\le H_\alpha^d\|F\|_{L_2(\ell_2)},
 \tag{5}
\]
and, for p>=4,
\[
 \|F\|_{L_{2p/(p-2)}(\ell_2)}
 \le H_\alpha^{4d/p}\|F\|_{L_2(\ell_2)}.
 \tag{6}
\]
These estimates are restricted to the stated cone. They are false
with this uniformity for arbitrary signed polynomial coefficients.

Here is a proof with the entry-law constants explicit. Put Z_e=|W_e|
and m_e(u)=E Z_e^u for nonnegative integers u, with m_e(0)=1. If u,v>=1
and beta=log_2(alpha), moment doubling gives
\[
 \|Z_e\|_{u+v}\le\alpha((u+v)/u)^\beta\|Z_e\|_u
\]
and the analogous bound with v. Raise the first inequality to u and
the second to v. The elementary entropy bound
\[
 ((u+v)/u)^u((u+v)/v)^v\le2^{u+v}
\]
therefore proves
\[
 m_e(u+v)\le\alpha^{2(u+v)}m_e(u)m_e(v).
 \tag{7}
\]
If either exponent is zero, (7) follows directly. If Z_e is identically
zero, monomials involving it can simply be removed before the argument.

For a scalar polynomial G(Z)=sum_nu a_nu Z^nu with a_nu>=0 and total
degree at most D, independence and (7), term by term in G^2, give
\[
 \mathbb E G^2\le\alpha^{4D}(\mathbb EG)^2.
 \tag{8}
\]
No centering or orthogonalization of these magnitude monomials occurs.

Represent the original joint law exactly as W_e=epsilon_e Z_e,
where all signs are independent and independent of all Z_e. This is
valid also when a magnitude has an atom at zero. Write
\[
 F(\varepsilon Z)=\sum_{S\subset[N]}\varepsilon_S F_S(Z).
 \tag{9}
\]
Each coordinate of F_S is a nonnegative-coefficient polynomial, every
monomial in it has exponent parity S, and |S|<=d. Conditional Hilbert
Boolean hypercontractivity gives
\[
 \mathbb E_\varepsilon\|F(\varepsilon Z)\|_2^4
 \le3^{2d}\left(\sum_S\|F_S(Z)\|_2^2\right)^2.
 \tag{10}
\]
The scalar polynomial G(Z)=sum_S||F_S(Z)||_2^2 has nonnegative
coefficients and degree at most 2d. Moreover
E G=E||F||_2^2 by conditional sign orthogonality. Applying (8) with
D=2d in (10) proves
E||F||_2^4 <=3^{2d}alpha^{8d}(E||F||_2^2)^2, which is (5).
Interpolation between L_2 and L_4, with parameter 4/p, proves (6).
For d=0 these are identities.

The Boolean theorem is standard; a primary exposition with its proof
is [O'Donnell, Lecture 16, Theorem 1.1](https://www.cs.cmu.edu/~odonnell/boolean-analysis/lecture16.pdf).
Its Hilbert version follows from positivity of the noise operator and
Hilbert Fourier orthogonality, as detailed in the companion
[weighted-sign proof](weighted_sign_localization.md), Section 4.
The additional argument (7)--(10) concerns the positive polynomial cone.

## 3. Strong moments of a matrix with few original rows or columns

Theorem 1.1 of [Latala and Strzelecka, Comparison of weak and strong
moments for vectors with independent coordinates](https://arxiv.org/pdf/1612.02407)
states, under the weaker requirement of (1) for r>=2, that
\[
 \|\|\sum_e W_e x_e\|\|_p
 \le C_{SW}(\alpha)\left(\mathbb E\|\sum_e W_e x_e\|
       +\sup_{\|\phi\|_*\le1}\|\sum_e W_e\phi(x_e)\|_p\right)
 \tag{11}
\]
for every p>=1 in any finite-dimensional normed space. Applying its
supremum-of-linear-forms formulation to the dual unit ball gives
exactly this finite-dimensional statement.

For a fixed original row set I and a unit s in R^I, the Hilbert random
vector Y[I,:]*s satisfies
\[
 \mathbb E\|Y[I,:]^*s\|_2\le\sigma_r,\qquad
 \sup_{\|t\|_2\le1}\|\langle Y[I,:]^*s,t\rangle\|_p\le R_Y(p).
\]
The first assertion uses independence and zero means when taking the
second moment; symmetry is not otherwise needed here. A deterministic
1/2-net of the row unit sphere has at most 5^{|I|} elements, so (11)
and the pointwise net inequality give
\[
 \|\|Y[I,:]\|\|_p
 \le2\,5^{|I|/p}C_{SW}(\alpha)\{\sigma_r+R_Y(p)\}.
 \tag{12}
\]
For a fixed column set J, the transposed argument gives
\[
 \|\|Y[:,J]\|\|_p
 \le2\,5^{|J|/p}C_{SW}(\alpha)\{\sigma_c+R_Y(p)\}.
 \tag{13}
\]
The subsets are deterministic. Later they will index orthogonal
operator sectors, and no probabilistic union bound over the subsets
will be taken.

## 4. Parity and amplitudes: the actual state space

Let the bipartite vertex sets be original rows and original columns,
and E the original nonzero ordered entries. On
L_2(Z;ell_2(vertices times subsets of E)), use the norm
\[
 \|f\|^2=\mathbb E_Z\sum_{v,S}|f_{v,S}(Z)|^2.
 \tag{14}
\]
Conditional Boolean Fourier transform identifies this with
L_2(epsilon,Z;ell_2(vertices)). The amplitudes may depend on EVERY
original magnitude, even those outside the currently occupied flags.

Multiplication by the dilation H_Y=[[0,Y],[Y*,0]] acts exactly as
\[
 (T f)_{w,T_0}(Z)
    =\sum_{e=vw}Z_e f_{v,T_0\triangle\{e\}}(Z).
 \tag{15}
\]
Split it into C_+ (e absent on input, parity creation) and C_-
(e present on input, parity annihilation). Both multiply by Z_e;
neither reduces the ordinary polynomial degree. Their sum is (15).
This is an exact original-randomness representation, rather than the
Jacobi recurrence in total polynomial degree.

The cone in this representation consists of the images of vector
polynomials F(Y) with nonnegative original monomial coefficients.
For a component with sign parity S, its magnitude coefficient has
only exponent vectors nu satisfying nu mod 2=S. A projection that
keeps specified pairs (current vertex, S) simply discards original
monomials. It preserves both the cone and the total-degree bound.
Conditional sign orthogonality makes disjoint such projections
orthogonal in (14), although even magnitude spectators can overlap.

## 5. Creation localizes original rows; annihilation localizes columns

First restrict to the current-row to current-column direction.
Fix an input parity grade k.

For creation, define the input label for (i,S) by
\[
 d=\operatorname{rowcounts}(S)+e_i.
 \tag{16}
\]
Every allowed creation e=(i,j) sends it to (j,T_0=S union {e}) with
rowcounts(T_0)=d. These labels partition both input and output states.
For a fixed d, the set I={i:d_i>0} has size at most k+1. All input
current rows and all input/output parity flags lie in I times [n].
The factor on this sector is exactly an input and output parity/count
compression of multiplication by Y[I,:]*. Multiplication terms of
the wrong parity grade are removed by the output projection.

For annihilation the correct labels are different. For an input
(i,T_0) of grade k, define
\[
 d=\operatorname{colcounts}(T_0).
 \tag{17}
\]
An allowed annihilation e=(i,j) sends it to (j,S=T_0 minus {e}), and
its output label colcounts(S)+e_j equals d. Again these give orthogonal
partitions of both input and output states. The set J={j:d_j>0}
has size at most k. All parity flags lie in [n] times J, and every
output current column lies in J. The factor is exactly an input and
output compression of multiplication by Y[:,J]*, restricted to
parity grade k-1 on output. Creation terms cannot survive that grade
projection. For k=0 this annihilator is zero.

These are decompositions in PARITY counts, not in magnitude degrees.
The latter would fail, for example because E(Y_11^2 Y_21^2)>0.
All even magnitude dependence is retained inside f. This does not
affect either conditional sign orthogonality or the multiplication
compression, and Holder's inequality below needs no independence
between f and the matrix multiplying it.

For the current-column to current-row direction, transpose the
description: creation localizes columns and annihilation localizes
rows. The two directions have orthogonal domains and ranges. As k
varies, the output grades k+1 of C_+ are orthogonal, as are the
output grades k-1 of C_-. Input grades are orthogonal as well.

## 6. The cone contraction, with all sector costs charged

Fix q>=1 and p=4q. Let f be in the cone and have total degree at most
q-1. Decompose a direction and parity grade using Section 5. Every
sector input f_d remains in the cone with the same total-degree bound.
For a creator sector, |I|<=k+1<=q. Because its output projection is
an L_2 contraction, (6), (12), and Holder give
\[
 \|C_{+,d}f_d\|_2
 \le\|Y[I,:]^*f_d\|_{L_2}
 \le\|\|Y[I,:]\|\|_p\|f_d\|_{L_{2p/(p-2)}}
 \le B_\alpha\{\sigma_r+R_Y(4q)\}\|f_d\|_2.
 \tag{18}
\]
Here 5^{|I|/p}<=5^{1/4} and the cone factor in (6) is at most
H_alpha. Magnitude spectators outside I are still present in f_d
on both sides of (18).

For annihilation, use |J|<=k<=q-1 and (13), obtaining the analogous
bound with sigma_c. The transposed maps exchange these variances.
Sum the SQUARED bounds over the orthogonal sectors and grades, then
take a square root. There is no factor for their number. It follows
that
\[
 \|C_+f\|_2,\ \|C_-f\|_2
       \le B_\alpha\{\sigma+R_Y(4q)\}\|f\|_2,
\]
and hence
\[
 \boxed{\|Tf\|_2\le2B_\alpha\{\sigma+R_Y(4q)\}\|f\|_2
       \quad\text{on the stated degree-limited positive cone}.}
 \tag{19}
\]
This is not an operator norm bound on the complete polynomial span.
In particular its proof does not use an adjoint argument to infer
the annihilator bound from the creator bound: (17) proves that bound
directly, on the same cone.

## 7. Iterate the actual vacuum walks

For a vacuum basis vector e_v, H_Y^j e_v is a vector of homogeneous
ordinary polynomials of degree j with nonnegative coefficients:
each coordinate is the sum of products of original entries along
ordered length-j walks. Every coefficient is a nonnegative integer.
The signs of entry values are inside Y_e, and the two orientations
of an edge use the SAME variable. No word or variable is resampled.

Consequently each prefix with j<q lies in the cone allowed in (19).
Iterating gives
\[
 \|H_Y^q e_v\|_{L_2}\le
          [2B_\alpha\{\sigma+R_Y(4q)\}]^q.
 \tag{20}
\]
Since H_Y is the actual symmetric dilation,
\[
 2\mathbb E\operatorname{tr}(YY^*)^q
   =\sum_{v=1}^{2n}\mathbb E\|H_Y^q e_v\|_2^2.
 \tag{21}
\]
Equations (20)--(21) prove (3). No infinite-basis completeness,
self-adjoint extension, cutoff norm, or exact state enumeration is
assumed. For q comparable to log n the factor n^{1/(2q)} is absolute.

## 8. Scope, relation to the archive, and verification

This gives a sharp analytic contraction for arbitrary
independent symmetric regular entries. The preserved information is
the original parity, all magnitude multiplicities in each coefficient,
current-side labels, and coefficientwise positivity in the ORIGINAL
monomial basis. Additional steps of the actual matrix walk preserve
that positivity. Coordinate/parity/count projections preserve it as
well. A general noncommuting coefficient insertion with negative
entries may not; this note does not impose the cone on the original
SparseStack or SRHT proofs without checking their coefficient algebra.

The frozen single-entry Jacobi obstruction remains correct. Its bad
directions are arbitrary linear combinations in an orthogonal-polynomial
span; they need not have nonnegative original monomial coefficients.
The present argument never takes a uniform norm on that span. Likewise,
the Gaussian-star failure of static moment proxies remains correct:
all powers of every original magnitude are retained in (9), (14), and
the actual vacuum iterates. Moment information is not converted into
a matching-quantile claim.

The [live MI-32 statement](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/main/matrix-inequalities-and-norms/MI-32/README.md)
also permits nonsymmetric entry laws and uses the exact same-index
deletion functional with exponent log(k+1), including k=1. These final
steps are proved in [the deletion note](regular_law_deletion.md).

Three independent analytic reviews checked the cone moment inequality,
its interpolation, both exact parity-count decompositions, the primary
strong/weak theorem's hypotheses, all dimensional and moment-order
costs, and the vacuum trace normalization. The bounded
[positive-cone checks](positive_cone_checks.json) and
[parity-amplitude checks](regular_law_parity_checks.json) record finite
supporting evidence. They are not the proof of the uniform theorem.
The joint audit distinguishes these scopes and pins the reviewed files.
