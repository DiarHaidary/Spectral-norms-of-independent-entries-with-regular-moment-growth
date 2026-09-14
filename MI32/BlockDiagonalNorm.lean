import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Data.Matrix.Block
import Mathlib.Tactic

/-!
# Euclidean norms of finite block-diagonal matrices

The block axes may depend on the block index and may be empty. The exact
splitting of squared Euclidean norms proves that a common bound on the
actual block norms bounds the full operator without a block-count factor.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace MI32.BlockDiagonalNorm

variable {K : Type*} [Fintype K] [DecidableEq K]
    {I : K → Type*} [∀ k, Fintype (I k)] [∀ k, DecidableEq (I k)]

/-- The original coordinates in one dependent block. -/
def sectionVector (x : EuclideanSpace ℝ (Σ k, I k)) (k : K) : EuclideanSpace ℝ (I k) :=
  WithLp.toLp 2 (fun i => x ⟨k, i⟩)

omit [DecidableEq K] [∀ k, DecidableEq (I k)] in
/-- Exact orthogonal splitting; the sum includes any empty blocks. -/
theorem norm_sq_eq_sum_sections (x : EuclideanSpace ℝ (Σ k, I k)) :
    ‖x‖ ^ 2 = ∑ k, ‖sectionVector x k‖ ^ 2 := by
  simp only [EuclideanSpace.real_norm_sq_eq, sectionVector, Fintype.sum_sigma]

/-- The genuine Euclidean operator associated with one original matrix. -/
def matrixOperator {V : Type*} [Fintype V] [DecidableEq V] (A : Matrix V V ℝ) :
    EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V :=
  (Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap) A

/-- Applying the full operator and then selecting a block is exactly the
action of that original block on the selected input coordinates. -/
theorem section_matrixOperator_blockDiagonal
    (A : ∀ k, Matrix (I k) (I k) ℝ) (x : EuclideanSpace ℝ (Σ k, I k)) (k : K) :
    sectionVector (matrixOperator (Matrix.blockDiagonal' A) x) k =
      matrixOperator (A k) (sectionVector x k) := by
  ext i
  change (∑ v : Σ k, I k, Matrix.blockDiagonal' A ⟨k, i⟩ v * x v) =
    ∑ j : I k, A k i j * x ⟨k, j⟩
  rw [Fintype.sum_sigma, Finset.sum_eq_single k]
  · simp only [Matrix.blockDiagonal'_apply_eq]
  · intro l _ hl
    apply Finset.sum_eq_zero
    intro j _
    rw [Matrix.blockDiagonal'_apply_ne A i j (Ne.symm hl), zero_mul]
  · simp

/-- A common bound on the actual Euclidean block norms bounds the whole
block-diagonal operator with constant one, including empty block families. -/
theorem norm_blockDiagonal_le (A : ∀ k, Matrix (I k) (I k) ℝ)
    (L : ℝ) (hL : 0 ≤ L) (hA : ∀ k, ‖A k‖ ≤ L) :
    ‖Matrix.blockDiagonal' A‖ ≤ L := by
  change ‖matrixOperator (Matrix.blockDiagonal' A)‖ ≤ L
  apply (matrixOperator (Matrix.blockDiagonal' A)).opNorm_le_bound hL
  intro x
  have hblock (k : K) :
      ‖matrixOperator (A k) (sectionVector x k)‖ ≤ L * ‖sectionVector x k‖ :=
    ((matrixOperator (A k)).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hA k) (norm_nonneg _))
  have hsq : ‖matrixOperator (Matrix.blockDiagonal' A) x‖ ^ 2 ≤ (L * ‖x‖) ^ 2 := by
    calc
      _ = ∑ k, ‖matrixOperator (A k) (sectionVector x k)‖ ^ 2 := by
        rw [norm_sq_eq_sum_sections]
        simp only [section_matrixOperator_blockDiagonal]
      _ ≤ ∑ k, (L * ‖sectionVector x k‖) ^ 2 :=
        Finset.sum_le_sum fun k _ => pow_le_pow_left₀ (norm_nonneg _) (hblock k) 2
      _ = L ^ 2 * ∑ k, ‖sectionVector x k‖ ^ 2 := by
        simp only [mul_pow, Finset.mul_sum]
      _ = (L * ‖x‖) ^ 2 := by rw [← norm_sq_eq_sum_sections, mul_pow]
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hL (norm_nonneg _))).mp hsq

/-- The right-hand Pi norm is the maximum of the nonnegative block norms.
It is zero for an empty index family and incurs no factor in its cardinality. -/
theorem norm_blockDiagonal_le_max (A : ∀ k, Matrix (I k) (I k) ℝ) :
    ‖Matrix.blockDiagonal' A‖ ≤ ‖fun k => ‖A k‖‖ := by
  apply norm_blockDiagonal_le A _ (norm_nonneg _)
  intro k
  simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using
    norm_le_pi_norm (fun k => ‖A k‖) k

end MI32.BlockDiagonalNorm
