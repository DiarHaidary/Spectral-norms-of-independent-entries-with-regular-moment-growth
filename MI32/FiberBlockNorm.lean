import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Data.Matrix.Block
import Mathlib.Tactic

/-!
# Euclidean norms of fiber-supported matrices

A matrix on `V × V` supported on the diagonal blocks of the partition of `V`
by the fibers of a colouring `c : V → K` has Euclidean operator norm at most
the largest norm of its fiber blocks, with no factor in the number of
fibers. The fiber blocks keep the original entries and the original axes,
so no reindexing of `V` is needed. The module also records the two-colour
off-diagonal contraction: masking out the entries whose row and column carry
the same Boolean colour does not increase the operator norm.

Everything here is deterministic; no probability is involved.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace MI32.FiberBlockNorm

variable {V K : Type*} [Fintype V] [DecidableEq V] [Fintype K] [DecidableEq K]

/-- The original entries of one fiber block, with no reindexing of the ambient axes. -/
def blockSub (A : Matrix V V ℝ) (c : V → K) (k : K) :
    Matrix {v // c v = k} {v // c v = k} ℝ := A.submatrix Subtype.val Subtype.val

omit [Fintype V] [DecidableEq V] [Fintype K] [DecidableEq K] in
/-- Entries of a fiber block are the original entries. -/
@[simp] theorem blockSub_apply (A : Matrix V V ℝ) (c : V → K) (k : K)
    (i j : {v // c v = k}) : blockSub A c k i j = A i.val j.val := rfl

/-- The original coordinates of a Euclidean vector along one fiber. -/
def fiberSection (c : V → K) (x : EuclideanSpace ℝ V) (k : K) :
    EuclideanSpace ℝ {v // c v = k} :=
  WithLp.toLp 2 (fun v => x v.val)

omit [DecidableEq V] in
/-- Exact orthogonal splitting of the squared Euclidean norm along the fibers;
the sum includes any empty fibers. -/
theorem norm_sq_eq_sum_fiberSections (c : V → K) (x : EuclideanSpace ℝ V) :
    ‖x‖ ^ 2 = ∑ k, ‖fiberSection c x k‖ ^ 2 := by
  simp only [EuclideanSpace.real_norm_sq_eq, fiberSection]
  rw [← Fintype.sum_fiberwise c (fun v => x v ^ 2)]

/-- The genuine Euclidean operator associated with one original matrix. -/
def matrixOperator {W : Type*} [Fintype W] [DecidableEq W] (A : Matrix W W ℝ) :
    EuclideanSpace ℝ W →L[ℝ] EuclideanSpace ℝ W :=
  (Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap) A

/-- For a fiber-supported matrix, applying the full operator and then restricting
to a fiber is the action of the fiber block on the restricted input. -/
theorem fiberSection_matrixOperator (A : Matrix V V ℝ) (c : V → K)
    (hA : ∀ i j, c i ≠ c j → A i j = 0) (x : EuclideanSpace ℝ V) (k : K) :
    fiberSection c (matrixOperator A x) k =
      matrixOperator (blockSub A c k) (fiberSection c x k) := by
  ext i
  change (∑ v : V, A i.val v * x v) = ∑ j : {v // c v = k}, A i.val j.val * x j.val
  rw [← Fintype.sum_fiberwise c (fun v => A i.val v * x v), Finset.sum_eq_single k]
  · intro l _ hl
    apply Finset.sum_eq_zero
    intro j _
    rw [hA _ _ (by rw [i.2, j.2]; exact Ne.symm hl), zero_mul]
  · simp

/-- A common bound on the Euclidean norms of the fiber blocks of a
fiber-supported matrix bounds the whole operator with constant one. -/
theorem norm_le_of_fiber_supported (A : Matrix V V ℝ) (c : V → K)
    (hA : ∀ i j, c i ≠ c j → A i j = 0) (L : ℝ) (hL : 0 ≤ L)
    (h : ∀ k, ‖blockSub A c k‖ ≤ L) : ‖A‖ ≤ L := by
  change ‖matrixOperator A‖ ≤ L
  apply (matrixOperator A).opNorm_le_bound hL
  intro x
  have hblock (k : K) :
      ‖matrixOperator (blockSub A c k) (fiberSection c x k)‖ ≤ L * ‖fiberSection c x k‖ :=
    ((matrixOperator (blockSub A c k)).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (h k) (norm_nonneg _))
  have hsq : ‖matrixOperator A x‖ ^ 2 ≤ (L * ‖x‖) ^ 2 := by
    calc
      _ = ∑ k, ‖matrixOperator (blockSub A c k) (fiberSection c x k)‖ ^ 2 := by
        rw [norm_sq_eq_sum_fiberSections c]
        simp only [fiberSection_matrixOperator A c hA]
      _ ≤ ∑ k, (L * ‖fiberSection c x k‖) ^ 2 :=
        Finset.sum_le_sum fun k _ => pow_le_pow_left₀ (norm_nonneg _) (hblock k) 2
      _ = L ^ 2 * ∑ k, ‖fiberSection c x k‖ ^ 2 := by
        simp only [mul_pow, Finset.mul_sum]
      _ = (L * ‖x‖) ^ 2 := by rw [← norm_sq_eq_sum_fiberSections c, mul_pow]
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hL (norm_nonneg _))).mp hsq

/-- The Pi norm of the fiber block norms bounds a fiber-supported matrix; it is
the maximum of the block norms (zero for an empty fiber family) and incurs no
factor in the number of fibers. -/
theorem norm_le_pi_blockSub (A : Matrix V V ℝ) (c : V → K)
    (hA : ∀ i j, c i ≠ c j → A i j = 0) :
    ‖A‖ ≤ ‖fun k => ‖blockSub A c k‖‖ := by
  apply norm_le_of_fiber_supported A c hA _ (norm_nonneg _)
  intro k
  simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using
    norm_le_pi_norm (fun k => ‖blockSub A c k‖) k

omit [Fintype V] [DecidableEq V] [Fintype K] in
/-- A matrix defined by a mask of the form `c i = c j ∧ P i j` is fiber-supported. -/
theorem fiber_supported_of_mask (c : V → K) (P : V → V → Prop) [∀ i j, Decidable (P i j)]
    (X : V → V → ℝ) :
    ∀ i j, c i ≠ c j →
      Matrix.of (fun i j => if c i = c j ∧ P i j then X i j else 0) i j = 0 := by
  intro i j hij
  simp [hij]

/-- Sign vector of a Boolean colouring: `1` on `true`, `-1` on `false`. -/
def signVector {W : Type*} (σ : W → Bool) : W → ℝ := fun i => if σ i then 1 else -1

omit [Fintype V] [DecidableEq V] [Fintype K] [DecidableEq K] in
/-- The masked entry as a combination of the entry and its two-sided sign conjugate. -/
theorem offDiagonal_entry_eq {W : Type*} (M : Matrix W W ℝ) (σ : W → Bool) (i j : W) :
    (if σ i = σ j then (0 : ℝ) else M i j) =
      (2 : ℝ)⁻¹ * (M i j - signVector σ i * M i j * signVector σ j) := by
  simp only [signVector]
  cases σ i <;> cases σ j <;> simp <;> ring

/-- The two-colour off-diagonal mask is a contraction in Euclidean operator norm:
masking out the same-colour entries does not increase `‖M‖`. -/
theorem norm_offDiagonal_le {W : Type*} [Fintype W] [DecidableEq W]
    (M : Matrix W W ℝ) (σ : W → Bool) :
    ‖Matrix.of (fun i j => if σ i = σ j then (0 : ℝ) else M i j)‖ ≤ ‖M‖ := by
  set d : W → ℝ := signVector σ with hd
  have hd_norm : ‖d‖ ≤ 1 := by
    rw [pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    simp only [hd, signVector, Real.norm_eq_abs]
    cases σ i <;> simp
  have hdiag : ‖Matrix.diagonal d‖ ≤ 1 := by
    rw [Matrix.l2_opNorm_diagonal]
    exact hd_norm
  have heq : Matrix.of (fun i j => if σ i = σ j then (0 : ℝ) else M i j) =
      (2 : ℝ)⁻¹ • (M - Matrix.diagonal d * M * Matrix.diagonal d) := by
    ext i j
    simp only [Matrix.of_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.mul_diagonal,
      Matrix.diagonal_mul, smul_eq_mul, hd]
    exact offDiagonal_entry_eq M σ i j
  have hprod : ‖Matrix.diagonal d * M * Matrix.diagonal d‖ ≤ ‖M‖ := by
    calc ‖Matrix.diagonal d * M * Matrix.diagonal d‖
        ≤ ‖Matrix.diagonal d * M‖ * ‖Matrix.diagonal d‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ ‖Matrix.diagonal d‖ * ‖M‖ * ‖Matrix.diagonal d‖ := by
        gcongr
        exact Matrix.l2_opNorm_mul _ _
      _ ≤ 1 * ‖M‖ * 1 := by gcongr
      _ = ‖M‖ := by ring
  rw [heq, norm_smul, Real.norm_eq_abs, abs_inv, abs_two]
  calc (2 : ℝ)⁻¹ * ‖M - Matrix.diagonal d * M * Matrix.diagonal d‖
      ≤ (2 : ℝ)⁻¹ * (‖M‖ + ‖M‖) := by
        gcongr
        exact (norm_sub_le _ _).trans (by gcongr)
    _ = ‖M‖ := by ring

end MI32.FiberBlockNorm
