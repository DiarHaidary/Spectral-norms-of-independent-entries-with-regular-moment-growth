# Remainder plan: stronger selection and an elementary centered Gram estimate

> **Superseded.** `MI32.main_upper` is now proved with no proof gap and no
> added axiom; see [`../README.md`](../README.md) and
> `verification/status.json`. This file is kept as a record of the
> development at the time it was written, and its status lines below are
> historical.

Date: 2026-09-14. Status: mathematical derivation checked below and independently
reviewed for its entry independence and shell indices; the new Gram/remainder
assembly is **not yet Lean-certified**. Existing verification snapshots retain
their original scope. This does not prove the general estimate (29), the full
deletion theorem, or a novelty claim.

The recommended route is to bypass (29) for the particular remainder we
construct. Increase the number of selected entries per marked coordinate from
`b²` to `b³`. The resulting fourth-power budget growth remains compatible with
all logarithmic-order comparisons, and makes a centered Gram second moment
summable. No general Gaussian or Latała fourth-moment matrix bound is required.

## Published dependency being avoided

[Latała–Świątkowski, Remark 4.5, (29)–(30)](https://arxiv.org/html/2106.03139v2#S4)
uses a variance-weighted general matrix estimate on the far remainder, after
deterministic nested selection. The original local estimate handles the near
blocks; it does not directly remove the ambient dimension from the remainder.

The cited [Latała–van Handel–Youssef paper, Theorem 4.4 and its proof, pp. 32–34](https://web.math.princeton.edu/~rvan/dimfr180821.pdf#page=32)
uses moment/tail comparison, a Gaussian-product comparator, the conditional
Gaussian norm theorem, and mixed-norm Gaussian estimates. Its stated theorem
has two-sided polynomial moment growth. The upper-only adaptation invoked in
Remark 4.5 needs a one-sided version of that comparison; our regular entries
need not have the stated lower growth. Formalizing this route would require
substantial additional results. The following derivation instead uses only
finite independence identities, fourth moments, and elementary operator norms.

## Exact original family and nested sets

Let the original ordered entries `X_ij` be independent and centered, with
finite fourth moments. Symmetry in distribution and alpha-regularity are used
elsewhere in the local proof; here it suffices that, for `alpha >= 1`,

\[
v_{ij}=\mathbb E X_{ij}^{2},\qquad
\mathbb E X_{ij}^{4}\le\alpha^{4}v_{ij}^{2},\qquad
\sum_i v_{ij}\le B^{2},\quad\sum_j v_{ij}\le B^{2},\quad B\ge0.
\tag{A}
\]

The fourth-moment assumption follows from the original doubling at order two.
All masks below are deterministic and retain the same original random entries.

Fix `b_0 >= 1` and

\[
t_r=b_r^{3},\qquad b_{r+1}=(b_r+1)^{5}-1.
\tag{B}
\]

Maintain `S_r subset S_(r+1)`, `|S_r| <= b_r`. At stage `r`, select the `t_r`
largest variances in each column marked by `S_r`, and the `t_r` largest in
each row marked by `S_r`. Include all their opposite endpoints, the old set,
and an original shared-index deletion minimizer at budget **b_r**, not b_(r+1).
The union has size at most

\[
b_r+2b_rt_r+b_r=2b_r^4+2b_r\le(b_r+1)^5-1.
\tag{C}
\]

Thus one common set controls both orientations:

\[
i\notin S_{r+1},\ j\in S_r
\quad\Longrightarrow\quad
v_{ij},v_{ji}\le B^2/(t_r+1).
\tag{D}
\]

The included minimizer gives the unchanged deletion bound outside S_(r+1)
at order log(b_r+1), whenever b_r <= n. Terminate explicitly at `S_L=[n]`
as soon as the next scheduled budget permits it; oversized-budget minimizers
alone do not guarantee exhaustion. Subsequent sets may be defined as `[n]`.
If n <= b_0, start with the full set. The initial set can otherwise be a
minimizer at budget b_0. No actual deletion budget in the target is enlarged.

## Shell indices and the two far pieces

Use `H_0=S_0` and `H_r=S_r minus S_(r-1)` for r>=1, so the H_r partition
the original coordinates, including possibly empty shells. Let h(i) be the
unique shell of i. Define

\[
Y_{ij}=X_{ij}\mathbf1_{\{h(i)\ge h(j)+2\}},\qquad
Z_{ij}=X_{ij}\mathbf1_{\{h(j)\ge h(i)+2\}}.
\tag{E}
\]

Both are deterministic original-entry masks. Apply the argument below to Y
and to Z^T separately; their dependence on each other is immaterial.

For a pair of columns j,l put r=max(h(j),h(l)). If both masked entries in
row i are nonzero, then i is outside S_(r+1), while j,l are in S_r. Hence
(D) applies at precisely stage r to both original columns. In the alternative
indexing `H_(k+1)=S_(k+1) minus S_k`, the selected marked set is S_(k+1)
and the supporting rows are outside S_(k+2). This one-stage shift is essential.

Put `w_ij=E Y_ij²`. For every ordered pair with maximum shell r,

\[
\sum_i w_{ij}w_{il}
\le {B^2\over t_r+1}\sum_i w_{il}
\le {B^4\over t_r+1}.
\tag{F}
\]

This remains true if a shell or the common support is empty. The number of
ordered pairs having maximum shell r is exactly
`|S_r|²-|S_(r-1)|²`, with S_(-1) empty, and is at most b_r².

## Centered Gram calculation, with every term accounted for

Let `D=E(Y^T Y)=diag_j(sum_i w_ij)` and `G=Y^T Y-D`. Distinct original
entries are independent, and masking preserves this. For j != l,

\[
\mathbb E G_{jl}=0,\qquad
\mathbb E G_{jl}^{2}=\sum_i w_{ij}w_{il}.
\tag{G1}
\]

The terms involving different rows contain distinct centered original
coordinates and vanish; the same-row term factors into the two variances.
For j=l, independent centered squares give

\[
\mathbb E G_{jj}^{2}
=\sum_i\big(\mathbb E Y_{ij}^{4}-w_{ij}^{2}\big)
\le\alpha^{4}\sum_i w_{ij}^{2}.
\tag{G2}
\]

No independence among Gram entries is asserted or needed. Since alpha>=1,
(G1), (G2), and (F) imply

\[
\mathbb E\|G\|_F^2
\le\alpha^4 B^4\sum_{r=0}^{L}{b_r^2\over b_r^3+1}
\le\alpha^4 B^4\sum_{r=0}^{L}{1\over b_r}
\le {2\alpha^4B^4\over b_0}.
\tag{H}
\]

The last step uses b_(r+1)>=2b_r and a finite geometric sum. In particular
the sum is at most 2 for b_0>=1, and at most 1 if b_0>=2.

The deterministic norm inequalities now do all remaining matrix work:

\[
\|Y\|_{\rm op}^2=\|Y^TY\|_{\rm op}
\le\|D\|_{\rm op}+\|G\|_{\rm op}
\le B^2+\|G\|_F.
\]

Integrating, applying scalar Cauchy–Schwarz twice, and using (H) gives

\[
\mathbb E\|Y\|_{\rm op}
\le\big(\mathbb E\|Y\|_{\rm op}^2\big)^{1/2}
\le B\sqrt{1+\alpha^2\sqrt{2/b_0}}.
\tag{I}
\]

All needed integrability follows from the finitely many original fourth
moments: Y has finite squared Frobenius norm, and G has finite squared
Frobenius norm. There is no division by B, so B=0 is included. Applying (I)
to Z^T uses the second orientation of (D) and the original row variance
budget. Therefore the entire far remainder obeys

\[
\mathbb E\|Y+Z\|_{\rm op}
\le2B\sqrt{1+\sqrt2\alpha^2}
\quad(b_0\ge1).
\tag{J}
\]

Why the stronger threshold matters: t_r=b_r² suffices to sum the individual
fourth moments, but (H) then has one order-one contribution per shell from
the off-diagonal Gram pairs. A general fourth-moment matrix inequality would
still be needed for that route. t_r=b_r³ absorbs these pairs directly.

## Near bands and compatibility with the exact deletion order

The remaining interactions have |h(i)-h(j)|<=1. Split them into two disjoint
block-diagonal masks: full blocks on H_0 union H_1, H_2 union H_3, etc.; and
off-diagonal cross blocks on H_1 union H_2, H_3 union H_4, etc. Terminal
unpaired shells are handled by adjoining an empty shell. This decomposition
does not require X=X^T or resampling.

An off-diagonal two-shell block O of a full block M satisfies
`O=(M-D_s M D_s)/2`, where D_s acts as +1 and -1 on the two shells. Thus
||O||<=||M|| pointwise by the isometry of D_s. Alternatively its two rectangular
weak tests are controlled by Minkowski and Euclidean two-component
Cauchy–Schwarz at the high order p>=1. Do not use Minkowski at log 2.

For a noninitial pair H_r union H_(r+1), r>=2, the block lies outside
S_(r-1), whose recorded deletion order is log(b_(r-2)+1). Its dimension is
at most b_(r+1), and (B) gives the exact logarithmic ratio 5³=125. Choose the
local norm moment order using the **scheduled** budget,
`q_r=ceil(2 log(b_(r+1)+1))`. Then the dimension factor is absolute and
`2q_r <= 1000 log(b_(r-2)+1)`; ten scalar doublings suffice. These orders
grow even when actual blocks are tiny, so the checked growing-moment maximum
lemma applies. The first one or two fixed-budget blocks are handled separately
by variance/Frobenius bounds, or by the initial minimizing S_0. Their constants
are absolute. Means alone must not be substituted for the growing moments.

## Remaining precise formal obligations

1. Two-sided deterministic selection, the old-budget minimizer, cardinal
   calculation (C), explicit exhaustion, and original weak-set monotonicity.
2. Exact shell masks, disjoint near/far partition, the maximal-shell common
   support condition (F), and the finite pair count/summability in (H).
3. Original independent-entry Gram means, centered second moments (G1/G2),
   and their integrability; no assumption of the final Gram estimate.
4. Euclidean operator-to-Frobenius comparison and the centered Gram transfer
   (H)->(I), including actual norm integrability.
5. Reindex near blocks into the checked local theorem, preserve original
   masks/variables, charge the fixed logarithmic ratio and initial blocks,
   then use the checked block maximum assembly and triangle inequality.

The local moment theorem is needed for the near bands, not for the elementary
far estimate. Completing these obligations would avoid dilation in the
symmetric-law deletion proof and would feed the already-checked original-law
symmetrization reduction. None of those remaining assemblies is claimed
complete by this note.
