# Fixed-support amplitude transfer and the selection boundary

Checkpoint: 2026-09-13; continued 2026-09-14. Status: proved fixed-support
lemma, a counterexample to exchanging selection and expectation, and an
explicit lossy bound for adaptive selection; independent analytic review
passed. This note does not itself prove an amplitude-transfer endpoint or
full MI-32. The separate
[positive-polynomial/parity proof](regular_law_positive_cone.md) avoids the
exchange studied here; an obstruction to this exchange is not an
obstruction to that proof.

## 1. A fixed thin matrix transfers without an amplitude loss

Let Y=(Y_ij) be an a-by-b family of independent symmetric variables, with
all moments finite and ||Y_ij||_(2u)<=alpha ||Y_ij||_u for u>=1. Set

\[
 \sigma_r=\max_i(\sum_j\mathbb EY_{ij}^2)^{1/2},\qquad
 R_Y(p)=\sup_{\|s\|_2,\|t\|_2\le1}
       \|\sum_{ij}s_it_jY_{ij}\|_p.
\]

Write Y=law Z circ epsilon, with Z=|Y| and independent original-entry
Rademacher signs independent of Z. For a DETERMINISTIC row set I of size r
and p>=1, define

\[
 F_I(Z;p)=\big(\mathbb E_\varepsilon
                  \|Z[I,:]\circ\varepsilon\|^p\big)^{1/p}.
\]

Then, for a constant C_alpha depending only on alpha,

\[
 \boxed{\quad
 \mathbb E_Z F_I(Z;p)
 \le\|\|Y[I,:]\|\|_p
 \le2\,5^{r/p}C_\alpha\{\sigma_r+R_Y(p)\}.
 \quad}                                                     \tag{1}
\]

The first inequality is Jensen, including equality when p=1. For the
second, fix a deterministic unit vector s supported on I. The Hilbert
vector Y[I,:]*s has expected norm at most sigma_r by its second moment.
Its weak p moment is at most R_Y(p). Apply the independent-coordinate
strong/weak theorem to this Hilbert vector. A deterministic one-half net
of the row unit sphere has size at most 5^r, and
||Y[I,:]||<=2 max_s ||Y[I,:]*s||_2 pointwise. Taking the p moment of this
finite maximum proves (1).

The precise source used is Theorem 1.1 of
[Latała and Strzelecka, Comparison of weak and strong moments for vectors
with independent coordinates](https://arxiv.org/pdf/1612.02407).
It assumes independent centered coordinates and regular growth at
orders u>=2, so the present assumptions suffice. It applies to the
Hilbert norm of a linear image of those coordinates. No matrix mean-norm
estimate is imported at this step.

In particular the conditional weak matrix moment of this fixed submatrix
is pointwise bounded by F_I(Z;p), so it satisfies the same expectation
bound. When r<=c p the net costs only 5^c. The transpose gives the analogous
statement for a fixed thin column set, using the maximum column variance.

## 2. The maximum over thin sets cannot be moved through expectation

Even in the Gaussian class there is no absolute constant K such that

\[
 \mathbb E_Z\max_{|I|\le r}F_I(Z;p)
 \le K\max_{|I|\le r}\mathbb E_ZF_I(Z;p)                     \tag{2}
\]

uniformly when r=ceil(log n) and p>=1. Take the n-by-n diagonal matrix
Y=diag(g_1,...,g_n) with independent standard Gaussians. Off-diagonal
entries are identically zero. Conditional on Z, signs do not affect the
norm of any row restriction, hence

\[
 F_I(Z;p)=\max_{i\in I}|g_i|,\qquad
 \max_{|I|\le r}F_I(Z;p)=\max_{i\le n}|g_i|.                 \tag{3}
\]

For every deterministic I of size at most r, the exponential moment
bound E exp(t|g|)<=2 exp(t^2/2) gives

\[
 \mathbb E\max_{i\in I}|g_i|\le\sqrt{2\log(2r)}.             \tag{4}
\]

For all sufficiently large n, put t=sqrt(log n)/2. Integration of the
Gaussian density over [t,t+1/t] and its negative image gives
P(|g|>=t)>=n^(-1/4). Independence therefore gives
P(max_(i<=n)|g_i|>=t)>=1-exp(-n^(3/4))>=1/2, and consequently

\[
 \mathbb E\max_{i\le n}|g_i|\ge\tfrac14\sqrt{\log n}.        \tag{5}
\]

The ratio of (5) to (4) diverges for r=ceil(log n). This is a counterexample
to (2), not to a variance-plus-weak-moment transfer. Indeed this diagonal
family has sigma_r=sigma_c=1 and R_Y(p)=||g||_p, which has order sqrt(p)
for p>=2. Its own logarithmic weak moment therefore covers (5).

For comparison, the frozen
[general-law reduction](../mi32_frontier_2026-09-13/general_law_reduction.md),
Section 5, uses a dense Gaussian family to disprove the different,
stronger claim that the conditional weak descriptor transfers with no
variance term. Neither counterexample refutes the full MI-32 target.

## 3. Charging the selection explicitly

There is a valid bound that records the missing selection cost. Assume
1<=r<=a and set N=binom(a,r). By augmenting a row set, the maximum over
sets of size at most r equals the maximum over sets of size exactly r.
For any P>=p>=1,

\[
 \begin{split}
 \mathbb E_Z\max_{|I|\le r}F_I(Z;p)
 &\le\left(\sum_{|I|=r}
               \mathbb E_Z F_I(Z;P)^P\right)^{1/P}\\
 &=\left(\sum_{|I|=r}\mathbb E\|Y[I,:]\|^P\right)^{1/P}\\
 &\le2N^{1/P}5^{r/P}C_\alpha
                   \{\sigma_r+R_Y(P)\}.
 \end{split}                                               \tag{6}
\]

Thus P=max{p,4r,log N,2} makes the explicit selection and net factors at
most e and 5^(1/4). At r comparable to p and p comparable to log a, this
elementary argument may use P of order (log a)^2 instead of log a.
For p>=2, Corollary 1.4 of the same primary source bounds the weak moment
increase by

\[
 R_Y(P)\le C'_\alpha(P/p)^\beta R_Y(p),\qquad
 \beta=\max\{1/2,\log_2\alpha\}.                            \tag{7}
\]

Apply that corollary to each scalar bilinear combination and then take
the supremum. The potential loss from (6)--(7) is a power of log a.
This does not improve the existing iterated-logarithmic full-law upper
bound in
[Meller, Spectral norm of matrices with independent entries up to polyloglog,
v2](https://arxiv.org/html/2512.23673v2).
The purpose of (6) is to make the failed free exchange quantitatively
reviewable, not to substitute a weaker endpoint for MI-32.

## 4. The distinction needed by a direct parity proof

For fixed realized amplitudes, the weighted-sign creator has exact
occupation-count blocks. Bounding the expected maximum of their random
operator norms and then invoking (1) would encounter (2). There is another
logical possibility: keep amplitude functions inside each polynomial
state, project only its sign parity and current vertex, and estimate each
block in the JOINT sign/amplitude L_2 space before summing its energy.
Such a proof would require a degree-controlled moment inequality on a
class preserved by those projections and by actual multiplication.
It does not exchange either maximum with expectation in (2).

The positive-polynomial proof uses precisely this different
order of operations. All amplitude spectators remain in the state;
Hölder needs no independence between that state and the thin-matrix
multiplier. Annihilation of a parity flag still multiplies the original
variable and raises its polynomial degree, retaining its even-multiplicity
cost. This explanatory distinction is not, by itself, a proof of that
route; its complete cone inequality, exact count compressions, and vacuum
iteration are supplied in the separate formal argument linked above.

No executable or numerical validation is claimed for this note. Its
content is the analytic inequalities (1), (3)--(7) and the counterexample
to (2). It asserts no general expected-norm or quantile comparison from
finite moment matching.
