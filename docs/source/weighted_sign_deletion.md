# The weighted-sign localization bound implies the exact same-index deletion estimate

Date: 2026-09-13. Status: proved consequence of the companion weighted-sign localization theorem and the published local-to-deletion implication; this detailed implication passed independent analytic review. Only independent Rademacher entries with deterministic real coefficients are considered. General regular entry laws are not covered by this note.

## 1. Exact statement, with the original convention retained

Let \(B=(b_{ij})_{i,j\le n}\) be real and \(X_{ij}=b_{ij}\varepsilon_{ij}\), with one independent fair sign at each original nonzero ordered entry. Put
\[
 M(B)=\max_i\Big(\sum_jb_{ij}^2\Big)^{1/2}
              +\max_j\Big(\sum_i b_{ij}^2\Big)^{1/2},
 \qquad \sigma=\max(\sigma_r,\sigma_c).
\]
For a deterministic index set \(I\subset[n]\), let
\[
 R_{B,I}(p)=\sup_{\|s\|_2,\|t\|_2\le1}
       \left(\mathbb E\left|\sum_{i,j\notin I}b_{ij}\varepsilon_{ij}s_it_j\right|^p\right)^{1/p},
 \qquad p>0,
\]
and define exactly
\[
 \boxed{\quad D(B)=\max_{1\le k\le n}
       \min_{I\subset[n],\ |I|\le k}R_{B,I}(\log(k+1)).\quad}
 \tag{1}
\]
All logarithms are natural. The *same* set \(I\) is deleted from the original row and column labels. It is chosen deterministically from the coefficient data, before signs are sampled. Transposed entries remain independent original variables. The \(k=n\) term is zero. The \(k=1\) exponent is \(\log2\), and is not silently replaced by one or by a logarithm of the ambient matrix size.

The conclusion is
\[
 \boxed{\qquad c\{M(B)+D(B)\}\le\mathbb E\|X\|
                  \le C\{M(B)+D(B)\},\qquad}
 \tag{2}
\]
with absolute constants. The new input to the upper implication is the companion [occupation-count localization theorem](weighted_sign_localization.md). The lower estimate is already [Latała--Świątkowski, Theorem 1.1](https://arxiv.org/html/2106.03139v2). It is not a new lower-bound argument in this note.

## 2. The published implication and its hypotheses

We use [Latała--Świątkowski, Remark 4.5](https://arxiv.org/html/2106.03139v2), specifically its displayed local hypothesis (28), its symmetric reduction, and its deletion quantity with \(\log(k+1)\). The implication says that a uniform local mean estimate, valid on every actual square submatrix at its own size, yields the mean upper bound with that same-index deletion quantity. Its proof uses a simultaneous permutation/decomposition. The factor involving the original regularity constant is absolute for weighted signs.

The remaining sections verify the applicability and conventions explicitly. In particular, they supply the symmetric local estimate required in that proof without pretending that the two occurrences of a symmetric entry are independent, and compare deletion in the symmetric dilation with deletion in the original ordered matrix.

From the companion theorem, every ordered-entry independent weighted-sign matrix \(Z\) of size \(m\) satisfies
\[
 \mathbb E\|Z\|\le C_0\{\sigma_r(Z)+\sigma_c(Z)
                         +R_Z(\max(1,\log m))\}.
 \tag{3}
\]
For \(m\ge2\), \(\max(1,\log m)\le\log(m+1)\); monotonicity of scalar moments therefore gives the precise local order required by (28). The case \(m=1\) is bounded directly by its deterministic entry magnitude. The constant is uniform in \(m\), the positions of retained indices, and all coefficients.

## 3. Symmetric matrices are handled with their original shared entries

Let \(Y\) be a symmetric weighted-sign matrix with independent entries on and above the diagonal; the lower triangular entry is the *same* variable as its upper triangular partner. Set
\[
 a(Y)=\max_i\Big(\sum_j\mathbb E Y_{ij}^2\Big)^{1/2}.
\]
Write \(Y=U+U^*+D_0\), where \(U\) is strictly upper triangular and \(D_0\) is diagonal. The entries of \(U\), including deterministic zeros, meet the independence hypothesis of (3). Both its row and column variance maxima are at most \(a(Y)\), and \(\|D_0\|\le a(Y)\) deterministically.

For \(p\ge1\), its weak moment satisfies
\[
 R_U(p)\le R_Y(p).
 \tag{4}
\]
To check this without a triangular-projection assumption, fix real unit vectors \(s,t\). The coefficient of one independent upper-triangular sign in \(\langle Us,t\rangle\), with the vector order renamed if necessary, has magnitude \(|b_{ij}s_i t_j|\). In the symmetric bilinear form at \((|s|,|t|)\), that sign has coefficient magnitude
\[
 |b_{ij}|\bigl(|s_i||t_j|+|s_j||t_i|\bigr)
                         \ge |b_{ij}s_i t_j|.
\]
Signs of the deterministic coefficients can be absorbed into the independent upper-triangular signs. The scalar Rademacher contraction inequality for the convex function \(|\cdot|^p\) proves (4); diagonal coefficients can be contracted to zero. The two vector norms are unchanged.

Applying (3) to \(U\), using (4), and then the triangle inequality gives, for every \(m\ge2\),
\[
 \mathbb E\|Y\|\le C_1\{a(Y)+R_Y(\log(m+1))\}.
 \tag{5}
\]
The same argument applies to every symmetric principal submatrix at its own actual dimension. For \(m=1\), the variance term alone suffices. Thus (5) supplies the symmetric local hypothesis used by the published permutation/decomposition implication.

No step of this argument replaces a symmetric sign by an independent lower-triangular copy. It is an application of the independent-entry local theorem to the actual upper-triangular part, followed by scalar coefficient contraction.

## 4. Dilation preserves the original deletion rule up to an absolute constant

For the original independent-entry square matrix \(X\), form its symmetric dilation
\[
 \mathcal X=\begin{pmatrix}0&X\\X^*&0\end{pmatrix}.
 \tag{6}
\]
Its upper-triangular nonzero variables are exactly the original variables \(X_{ij}\); its lower part repeats them. It therefore belongs to the symmetric class of §3. Also
\[
 \|\mathcal X\|=\|X\|,\qquad a(\mathcal X)=\sigma.
 \tag{7}
\]
Let \(D_{\rm sym}(\mathcal X)\) use the definition (1) on its \(2n\) coordinate labels. The published implication, with (5) now supplied, gives
\[
 \mathbb E\|X\|\le C_2\{\sigma+D_{\rm sym}(\mathcal X)\}.
 \tag{8}
\]

For any original \(I\subset[n]\), delete both coordinate copies,
\(\widetilde I=I\cup(n+I)\). This uses exactly \(2|I|\) dilation indices. The surviving matrix is the dilation of the actual original submatrix \(X[I^c,I^c]\).

For any real random matrix \(Z\) and \(p\ge1\), its dilation has exactly the same weak bilinear moment:
\[
 R_{\left(\begin{smallmatrix}0&Z\\Z^*&0\end{smallmatrix}\right)}(p)=R_Z(p).
 \tag{9}
\]
The lower inequality uses vectors in opposite coordinate halves. For the upper inequality, write the unit vectors as \((s_r,s_c)\) and \((t_r,t_c)\), apply Minkowski to the two bilinear forms, and use
\[
 \|s_r\|\|t_c\|+\|t_r\|\|s_c\|
 \le\sqrt{\|s_r\|^2+\|s_c\|^2}
     \sqrt{\|t_c\|^2+\|t_r\|^2}\le1.
\]
There is no independence assumption between the two terms in this calculation.

For a dilation deletion budget \(k\ge2\), put \(\ell=\lfloor k/2\rfloor\). Then \(1\le\ell\le n\), and a minimizing original set of size at most \(\ell\) can be deleted in both copies at cost at most \(k\). Moreover
\[
 \log(k+1)\le\log(2\ell+2)\le2\log(\ell+1).
 \tag{10}
\]
There is one absolute scalar Rademacher constant \(C_R\) such that
\[
 \|S\|_{2p}\le C_R\|S\|_p\quad\text{for every Rademacher sum and }p\ge\log2.
 \tag{11}
\]
For completeness, at \(p\ge2\) scalar hypercontractivity gives \(C_R\le\sqrt3\). On \([\log2,2]\), \(\|S\|_{2p}\le\|S\|_4\le3^{1/4}\|S\|_2\). Paley--Zygmund applied to \(S^2\), using \(\mathbb ES^4\le3(\mathbb ES^2)^2\), gives
\(\|S\|_p\ge2^{-1/2}12^{-1/\log2}\|S\|_2\).
These bounds supply an explicit absolute constant in (11), including the otherwise delicate exponent \(\log2<1\).

Equations (9)--(11), followed by the original minimum and maximum in (1), imply that every \(k\ge2\) term of \(D_{\rm sym}\) is at most \(C_RD(B)\). For \(k=1\), use instead monotonicity up to moment two:
\[
 R_{\mathcal X}(\log2)\le R_{\mathcal X}(2)
       =R_B(2)=\max_{i,j}|b_{ij}|\le\sigma.
\]
The equality \(R_B(2)=\max|b_{ij}|\) follows by independence and a coordinate witness. Hence
\[
 \boxed{\quad D_{\rm sym}(\mathcal X)
                 \le\max\{\sigma,C_RD(B)\}.\quad}
 \tag{12}
\]
Combining (8) and (12) proves the upper bound in (2), since \(\sigma\le M(B)\). This proves the exact original same-index statement; it has not substituted independent row/column deletions, a global moment order on a smaller matrix, or an uncharged dimension change.

## 5. What is established and what is not

The upper implication uses the newly derived weighted-sign local theorem, the established local-to-deletion implication, and the explicit symmetric/dilation checks above. The lower implication is the existing Theorem 1.1. These combine into (2) for every finite deterministic real coefficient matrix with independent original Rademacher signs. Empty supports and \(n=1\) are included by their direct variance bounds.

The equality of the two dilation occurrences of an entry is kept throughout. It does not authorize identifying two *different* original entries in a later interaction. The minimization in (1) remains a deterministic mathematical descriptor; no efficient algorithm for its exact evaluation is asserted.

This establishes the weighted-sign mean comparison only. It does not replace the original-law amplitude or multiplicity data for general independent regular variables, does not provide a quantile theorem, and does not settle the full general-law MI-32 objective. No priority claim is made for the published deletion implication or lower estimate.
