# Specification of the remaining symmetric-deletion chain

Date: 14 September 2026. **Implemented.** Every section below was carried out
and `MI32.main_upper` is now proved with no proof gap and no added axiom. This
file is still only a description: nothing in it is proof evidence; only modules
in a successful verification record at their recorded hashes are checked. The
module names in the section headings are the files that were written, and the
statements are close to, but not always literally, their final signatures —
read the modules for those. Deviations agreed during implementation are listed
at the end of the corresponding agent reports and summarised in
[`SOURCE_FIDELITY.md`](SOURCE_FIDELITY.md).

It refines [the remainder plan](NEXT_REMAINDER_ANALYTIC_PLAN.md) into exact
Lean statements. The target is

```
MI32.SymmetrizationReduction.SymmetricUpperBoundAt (2 * alpha) C
```

for an explicit `C = C alpha`, which the already-checked
`upperBoundAt_of_symmetric` turns into `UpperBoundAt alpha (C * exp 1)` and
hence discharges `MI32.main_upper`.

Throughout: `alpha >= 1`, `n >= 1`, arbitrary probability space `mu`,
`X : Omega -> Matrix (Fin n) (Fin n) R` with `RegularEntries mu alpha X` and
every entry symmetric in distribution. Write

* `B = varianceScale mu X` (so every row and column variance sum is `<= B^2`,
  by `VarianceScaleBasics.row_variance_le_sq` / `col_variance_le_sq`),
* `D = deletionScale mu X`,
* `J = SymmetricLinearAllOrders.doublingConstant alpha = (sqrt 3 * alpha^2)^7`,
* `v i j = integral of (X w i j)^2`.

## 0. Schedule, nested sets, shells

`DeletionScheduleArithmetic`: `budget k = 2^(5^k) - 1`, `order k = 5^k log 2`.
Already checked there: `budget_add_one`, `budget_succ`, `step_card_le`,
`budget_ge_two_pow`, `finite_terminal_bound` (`n <= budget n`), `order_eq`,
`order_succ`, `log_two_le_order`.

Nested sets (`NestedDeletionSelection.twoSidedSets`) with

```
S 0     := NestedDeletionSelection.minimizingSet mu X 1
S (r+1) := twoSidedNextSet mu X B (S r) (budget r) (budget r ^ 3)
```

Derived facts (from already-checked lemmas plus `step_card_le`):

* `(S r).card <= budget r` (induction; `S 0` has card `<= 1 = budget 0`)
* `Monotone S`
* `S (n+1) = univ` (`twoSidedSets_succ_eq_univ` with `n <= budget n`)
* column screen: `j in S r -> i notin S s -> r+1 <= s -> (budget r ^ 3 + 1) * v i j <= B^2`
* row screen: `i in S r -> j notin S s -> r+1 <= s -> (budget r ^ 3 + 1) * v i j <= B^2`
* weak screen, **for every `a >= 1`**:
  `weakMoment mu X (S (a-1)) (order (a-2)) <= D`, with natural subtraction.
  For `a = 1`, `S 0` is a minimizer at budget 1 and `order 0 = log 2`, so use
  `minimizingSet_le_deletionScale_of_pos`.
  For `a >= 2`, use `twoSidedSets_weakMoment_le_scale_of_le` with `r = a-2`,
  `s = a-1` (note `r+1 = a-1 <= s`).

`NestedShells` with horizon `N = n+1`: `level i : Fin (N+1)` is the first `r`
with `i in S r`; `filter (level . <= r) = S r`; the shells partition `Fin n`;
`entry_partition` splits every entry into `nearEven + nearOdd + farLower +
farUpper` for `label = fun i => (level i).val`.

## 1. `MI32/FiberBlockNorm.lean` -- deterministic block norms

`V`, `K` fintypes with decidable equality, `c : V -> K`.

```
def blockSub (A : Matrix V V R) (c : V -> K) (k : K) :
    Matrix {v // c v = k} {v // c v = k} R := A.submatrix Subtype.val Subtype.val

theorem norm_le_of_fiber_supported (A : Matrix V V R)
    (hA : forall i j, c i <> c j -> A i j = 0) (L : R) (hL : 0 <= L)
    (h : forall k, ||blockSub A c k|| <= L) : ||A|| <= L

theorem norm_le_pi_blockSub (A : Matrix V V R)
    (hA : forall i j, c i <> c j -> A i j = 0) :
    ||A|| <= || fun k => ||blockSub A c k|| ||
```

Proof: for `x : EuclideanSpace R V` let `x k` be its restriction to the fiber
`{v // c v = k}`. Then `||x||^2 = sum over k of ||x k||^2` by
`Fintype.sum_fiberwise`, and `A x` restricted to fiber `k` equals
`blockSub A c k` applied to `x k`, because `A i j = 0` off the diagonal blocks.
Then mirror `BlockDiagonalNorm.norm_blockDiagonal_le`.

Also, used for the odd family:

```
theorem norm_offDiagonal_le {W : Type*} [Fintype W] [DecidableEq W]
    (M : Matrix W W R) (s : W -> Bool) :
    ||Matrix.of (fun i j => if s i = s j then 0 else M i j)|| <= ||M||
```

Proof: with `d i = if s i then (1:R) else -1`, the masked matrix equals
`(M - diagonal d * M * diagonal d) / 2`; `||diagonal d|| <= 1` by
`Matrix.l2_opNorm_diagonal`, then `Matrix.l2_opNorm_mul` twice.

## 2. `MI32/FrobeniusMean.lean` -- small-block mean by entry energy

```
theorem mean_norm_le_sqrt_entry_energy (A : Omega -> Matrix V W R)
    (hA : forall i j, Measurable (fun w => A w i j))
    (hInt : forall i j, Integrable (fun w => A w i j ^ 2) mu)
    (K : R) (hK : 0 <= K)
    (hBound : (sum over i, sum over j, integral of (A w i j)^2) <= K^2) :
    Integrable (fun w => ||A w||) mu and (integral of ||A w||) <= K
```

This is `CenteredGramNorm.gram_mean_le` with `A` in place of the Gram matrix;
that proof only needs the entrywise bound `norm_sq_le_entryEnergy`, which holds
for rectangular `A` as well, so restate both for `Matrix V W R`.

## 3. `MI32/GramEntryMoments.lean` -- centered Gram second moments

Family `Y : R -> C -> Omega -> R`, independent, centered, all moments finite,
`w i j = integral of (Y i j)^2`, and the fourth-moment budget
`hfour : forall i j, integral of (Y i j)^4 <= alpha^4 * (w i j)^2`.

```
theorem integral_gram_sq_offdiag (j k : C) (hjk : j <> k) :
    integral of (sum over i, Y i j w * Y i k w)^2 = sum over i, w i j * w i k

theorem integral_gram_sq_diag (j : C) :
    integral of (sum over i, ((Y i j w)^2 - w i j))^2 <= alpha^4 * sum over i, (w i j)^2

theorem total_gram_energy_le (E : R)
    (hE : (sum over j, sum over k, sum over i, w i j * w i k) <= E) :
    (sum over j, sum over k, integral of (centeredGram ... j k)^2) <= alpha^4 * E
```

Here `centeredGram` is `CenteredGramNorm.centeredGram (fun i j => Y i j w)
(fun j => sum over i, w i j)`, whose `(j,k)` entry is
`(sum over i, Y i j w * Y i k w) - (if j = k then sum over i, w i j else 0)`.

Method for the two second moments: each is `sum over i, Z i` for a family `Z`
that is independent in `i`, centered, and square integrable, so apply the
already-checked `MatrixImages.integral_linear_sum_sq` with all coefficients
equal to `1`. Independence in `i` comes from
`IndependentColumns.independent_column_vectors` applied to the transposed
family (rows are jointly independent as vectors), then `iIndepFun.comp` with
`fun x => x j * x k` resp. `fun x => x j ^ 2 - w i j`, then
`iIndepFun.indepFun`. Centering of `Y i j * Y i k` for `j <> k` uses
`iIndepFun.indepFun` on the entry family at `(i,j) <> (i,k)` together with
`IndepFun.integral_mul`. The same product rule gives
`integral of (Y i j)^2 * (Y i k)^2 = w i j * w i k`, and the diagonal term is
`integral of (Y i j)^4 - (w i j)^2 <= alpha^4 * (w i j)^2`. Since `alpha >= 1`,
the diagonal `j = k` contributions are charged to the same triple sum.

## 4. `MI32/FarRemainderMoment.lean` -- the far orientations

Inputs: independent centered `X` on `Fin n`, `alpha >= 1`, the fourth-moment
budget, the column budget `sum over i, v i j <= B^2`, a label
`label : Fin n -> Fin L`, budgets `b : Fin L -> Nat` with `2 ^ r.val <= b r`,
cumulative counts `(filter (label . <= r)).card <= b r`, and the screen

```
forall i j k, label j <= label k -> (masked entry at (i,k) nonzero) ->
    v i j <= B^2 / (b (label k) ^ 3 + 1)
```

Conclusion for `Y w i j = if label j + 1 < label i then X w i j else 0`:

```
Integrable (fun w => ||Y w||) mu and
  (integral of ||Y w||) <= B * sqrt (1 + sqrt 2 * alpha^2)
```

Assembly: `GradedVarianceEnergy.total_energy_le_two` gives
`sum over j, sum over k, sum over i, w i j * w i k <= 2 B^4`; section 3 gives
Gram energy `<= 2 alpha^4 B^4`; `CenteredGramNorm.mean_norm_le` with
`d j = sum over i, w i j`, `|d j| <= B^2` and `K = sqrt 2 * alpha^2 * B^2`
gives `integral of ||Y|| <= sqrt (B^2 + sqrt 2 alpha^2 B^2)`.

`farUpper` is handled by applying the same theorem to the transposed family
and `Matrix.l2_opNorm_conjTranspose` (over the reals, the conjugate transpose
is the transpose), using the row screen in place of the column screen.

## 5. `MI32/BilinearHighOrder.lean` -- `k` scalar doublings

```
theorem bilinear_moment_le_pow ... (k : Nat) (p r : R)
    (hp : log 2 <= p) (hr : 0 < r) (hrp : r <= 2 ^ k * p) :
    moment mu r (ThinMatrix.bilinear X s t) <=
      J ^ k * moment mu p (ThinMatrix.bilinear X s t)
```

Induction on `k` for `moment mu (2^k * p) <= J^k * moment mu p`, using the
already-checked `SymmetricLinearAllOrders.linear_root_doubling` through
`LocalLogMoment.linearForm_eq_bilinear`, then one application of
`MomentTools.mono_exponent_of_integrable` (integrability at `2^k p` from
`SymmetricLinearRegularity.integrable_abs_rpow_linearForm`). This is the
`k`-fold analogue of the existing `LocalLogMoment.bilinear_moment_le_eight`.

## 6. `MI32/BlockMaskMoment.lean` -- block maximum with a nonnegative bound

```
theorem mean_norm_le_of_block_moments (A : Omega -> Matrix V V R) (c : V -> Fin m)
    (hA : forall i j, Measurable (fun w => A w i j))
    (hsupp : forall w i j, c i <> c j -> A w i j = 0)
    (p : Fin m -> Nat) (hp : forall k, k.val + 2 <= p k)
    (hPow : forall k, Integrable (fun w => ||blockSub (A w) c k|| ^ p k) mu)
    (L : R) (hL : 0 <= L)
    (hBound : forall k, integral of ||blockSub (A w) c k|| ^ p k <= L ^ p k) :
    Integrable (fun w => ||A w||) mu and (integral of ||A w||) <= 3 * L
```

Proof: `FiberBlockNorm.norm_le_pi_blockSub` pointwise plus
`BlockMomentMaximum.mean_max_le`. The strict positivity `0 < L` required there
is removed by running the lemma at `L + eps` for every `eps > 0` and closing
with `le_of_forall_pos_le_add`. Block-norm integrability at order one follows
from integrability at order `p k >= 2`.

## 7. `MI32/NearBlockMoment.lean` -- one two-shell block

For `a >= 1` put `q a = Nat.ceil (2 * order (a+1))`. Arithmetic facts:

* `1 <= q a`,
* `2 * (q a : R) <= 2^10 * order (a - 2)` (natural subtraction; uses
  `5 ^ (a+1) <= 125 * 5 ^ (a-2)` for `a >= 1` and `order k = 5^k log 2`),
* `a + 2 <= 2 * q a`,
* `((d + d : Nat) : R) ^ (1 / (2 * (q a : R))) <= exp 1` whenever
  `d <= budget (a+1)`; the case `d = 0` is the rpow of zero.

Block statement: let `c : Fin n -> K`, `k : K`, and suppose every `i` in the
fiber satisfies `level i = a or level i = a + 1`. Then

```
Integrable (fun w => ||blockSub (X w) c k|| ^ (2 * q a)) mu and
  moment mu (2 * (q a : R)) (fun w => ||blockSub (X w) c k||) <=
    exp 1 * RawMultiplicationContraction.contractionConstant alpha B (J^10 * D)
```

Ingredients:

* fiber is contained in `S (a+1)` and disjoint from `S (a-1)`, from
  `NestedShells.level_le_iff`; hence the fiber card is `<= budget (a+1)`;
* independence, symmetry, regularity and integrability for the restricted
  family by `iIndepFun.precomp` with the injection
  `{i // c i = k} x {i // c i = k} -> Fin n x Fin n` plus restriction of the
  other fields;
* `hrow` and `hcol` for the restricted family from the `B^2` budgets, since
  they are sub-sums of nonnegative terms;
* weak input: for unit `s`, `t` on the fiber, extend by zero to `s'`, `t'` on
  `Fin n` (the norm is preserved), then
  `ThinMatrix.bilinear Z s t = deletedBilinear X (S (a-1)) s' t'`, so section 5
  with `k = 10` and `p = order (a-2)` (legal since
  `log 2 <= order (a-2)` by `log_two_le_order`) gives
  `moment mu (2 * q a) (bilinear Z s t) <= J^10 * weakMoment mu X (S (a-1)) (order (a-2)) <= J^10 * D`;
* `LocalSymmetricMoment.operator_moment_le` plus the dimension-factor bound.

## 8. `MI32/SymmetricDeletion.lean` -- assembly

Masks, with `label i = (level i).val`, `cEven i = label i / 2`,
`cOdd i = (label i + 1) / 2`, both valued in `Fin (N+2)`:

```
nearLow  w i j = if cEven i = 0 and cEven j = 0 then X w i j else 0
nearHigh w i j = if cEven i = cEven j and cEven i <> 0 then X w i j else 0
nearOdd  w i j = if cOdd i = cOdd j and label i <> label j then X w i j else 0
```

Then `nearLow + nearHigh = NestedShells.nearEven` and `nearOdd` agrees with
`NestedShells.nearOdd`, so `NestedShells.entry_partition` gives

```
||X w|| <= ||nearLow w|| + ||nearHigh w|| + ||nearOdd w|| + ||farLower w|| + ||farUpper w||.
```

Bounds:

* `nearLow` is supported on `S 1 x S 1` with `(S 1).card <= budget 1 = 31`, so
  section 2 gives `integral of ||nearLow|| <= sqrt 31 * B`;
* `nearHigh`: section 6 with `c = cEven` and `p k = 2 * q (2 * k.val)`. Block
  `0` is the zero matrix; block `k >= 1` is `blockSub X cEven k` at
  `a = 2 * k.val >= 2`, estimated by section 7. Gives `<= 3 L`;
* `nearOdd`: section 6 with `c = cOdd` and `p k = 2 * q (2 * k.val - 1)`.
  Block `0` is zero; block `k >= 1` is the off-diagonal part of
  `blockSub X cOdd k` for `s i = decide (label i % 2 = 1)`, so
  `||.|| <= ||blockSub X cOdd k||` by section 1 and section 7 applies at
  `a = 2 * k.val - 1 >= 1`. Gives `<= 3 L`;
* `farLower`, `farUpper`: section 4, each `<= B * sqrt (1 + sqrt 2 alpha^2)`.

With `L = exp 1 * contractionConstant alpha B (J^10 * D)`, which equals
`LocalLogMoment.meanConstant alpha * (B + 6 alpha^4 * J^10 * D)`, the total is
`<= C alpha * (B + D)` for an explicit `C alpha`, and `varianceScale` and
`deletionScale` are exactly `B` and `D`. This proves
`SymmetricUpperBoundAt alpha (C alpha)` for every `alpha >= 1`; instantiating
at `2 alpha` and applying
`SymmetrizationReduction.upperBoundAt_of_symmetric` gives
`UpperBoundAt alpha (C (2 alpha) * exp 1)`, that is, `MI32.main_upper`.

## Deliberate divergence from the source draft

The draft's remainder step cites
[Latala--van Handel--Youssef, Theorem 4.4](https://web.math.princeton.edu/~rvan/dimfr180821.pdf#page=32)
through a variance-envelope estimate. This chain replaces that citation by the
elementary centered-Gram argument of
[the remainder plan](NEXT_REMAINDER_ANALYTIC_PLAN.md): the per-coordinate
selection threshold is raised from `b^2` to `b^3`, which makes the
off-diagonal Gram pair energies summable and removes the need for a general
fourth-moment matrix inequality.

The draft also routes the deletion argument through the matrix-symmetric
dilation `H_Y`, whose reflected entries repeat variables. This chain instead
performs the whole decomposition on the original rectangular matrix with one
shared index family on both axes, so every entry family used is genuinely
independent and the paired dilation budget is not needed. Both changes are
recorded in `docs/SOURCE_FIDELITY.md`.
