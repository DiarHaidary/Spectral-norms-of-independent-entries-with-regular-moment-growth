# Completed formal step: the original thin-matrix moment

The target below is now proved by
`MI32.ThinMatrix.transposeOperator_moment_four_mul_le`. Original row and
column restrictions, transpose norm equality, and multiplication against
the actual dependent polynomial are also proved. Continue with
`docs/SECTOR_CONTRACTION_DERIVATION.md`; do not restart this step.

Let X be a rectangular matrix with finite row index I and column index J,
on an arbitrary probability space. Assume the original entries are
independent, symmetric, have all positive absolute moments finite, and
satisfy the existing rooted alpha-regularity, alpha >= 1. Fix q >= 1,
with |I| <= q. Suppose B >= 0 and R >= 0 satisfy

\[
\sum_j\mathbb E X_{ij}^2\le B^2\quad(i\in I),\qquad
\sup_{\|s\|_2,\|t\|_2\le1}
\left\|\sum_{i,j}s_iX_{ij}t_j\right\|_{2q}\le R.
\]

The immediate target is the actual Euclidean operator estimate

\[
\boxed{\quad
\|\,\|X\|_{\rm op}\,\|_{4q}
\le 2\,5^{1/4}\bigl(B+6\alpha^4R\bigr).
\quad}
\]

This is a theorem in the project. The following ingredients explain its
proof and retain the original random law:

1. `IndependentColumns.independent_columnLinearForm` and
   `symmetric_columnLinearForm` apply to V_j = sum_i s_i X_ij for a
   deterministic unit row vector s. Establish centering from symmetry or
   use the original mean-zero hypothesis where already available.
2. `SymmetricLinearRegularity.columnLinearForm_even_root_doubling`
   gives beta = sqrt(3) alpha^2 at the required natural even orders.
3. `MatrixImages.integral_matrix_image_sq_le` bounds E||V||_2^2 by B^2
   with constant one. Use the actual Euclidean norm identity; there is
   no supremum-coordinate norm substitution.
4. `HilbertComparison.independent_coordinate_moment_le` gives
   |||V|||_(4q) <= B + 2 beta^2 R = B + 6 alpha^4 R.
   Its weak tests are deterministic Euclidean inner products at order 2q;
   convert these exactly to the same original matrix bilinear form.
5. `ThinMomentRoot.opNorm_moment_four_mul_le_of_images` pays precisely
   2*5^(1/4), since the domain dimension is |I| <= q. Establish the
   concrete rectangular transpose operator, its measurability, and the
   coordinate identity with `MatrixImages.matrixRowImage`. All power
   integrability is already available through finite coordinate `MemLp`.

For later occupation blocks, embed an active-axis subtype into the original
row/column space isometrically and compare its weak tests with the original
matrix's weak moment. This must keep the same original entries and shared
variable identities. Swapping axes gives the column version.

The positive-polynomial input for Holder is now directly available as
`SymmetricConeInterpolation.moment_four_q_le`. It applies to the original
random polynomial after inverse Walsh transform, with raw degree d < q,
and loses only sqrt(3) alpha^2. It must not be applied to a coefficient
vector in a different L_r space.

After the thin estimate, the remaining substantive work is the actual
orthogonal count-sector operator bound, reachable vacuum iteration and
trace estimate, then the exact deletion reduction, logarithmic endpoint,
dilation and general-law symmetrization. `MI32.main_upper` in `Solution.lean`
remains unproved until this full chain is assembled.

This milestone advances the computational support and analytic MI-32
branch for independent regular entries. The formal Hilbert comparison
removes the need to import a much more general comparison theorem for this
step. No new lower bound, quantile result, or originality claim follows.
