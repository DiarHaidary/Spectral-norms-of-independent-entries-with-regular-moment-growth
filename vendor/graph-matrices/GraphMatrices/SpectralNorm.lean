import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic
import GraphMatrices.Basic
import GraphMatrices.CrossedEdges

/-!
# Explicit Euclidean operator norms

The norm below is defined through continuous linear maps of Euclidean spaces.
It never uses an unqualified/default norm on matrices.
-/

namespace GraphMatrices

noncomputable section

open scoped BigOperators RealInnerProductSpace
open WithLp

variable {m n k p q : Type*}
variable [Fintype m] [Fintype n] [Fintype k] [Fintype p] [Fintype q]
variable [DecidableEq n] [DecidableEq k] [DecidableEq p] [DecidableEq q]

/-- The actual linear operator between Euclidean coordinate spaces. -/
def euclideanOperator (A : Matrix m n ℝ) : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ m :=
  (Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap) A

/-- The spectral/operator norm, explicitly fixed to Euclidean input and output. -/
def spectralNorm (A : Matrix m n ℝ) : ℝ := ‖euclideanOperator A‖

@[simp] theorem euclideanOperator_apply (A : Matrix m n ℝ) (x : EuclideanSpace ℝ n)
    (i : m) : euclideanOperator A x i = ∑ j, A i j * x j := rfl

theorem spectralNorm_nonneg (A : Matrix m n ℝ) : 0 ≤ spectralNorm A := norm_nonneg _

@[simp] theorem spectralNorm_zero : spectralNorm (0 : Matrix m n ℝ) = 0 := by
  simp [spectralNorm, euclideanOperator]

open scoped Matrix.Norms.L2Operator in
/-- A checked bridge to Mathlib's explicitly scoped L2 operator norm. -/
theorem spectralNorm_eq_l2Operator (A : Matrix m n ℝ) : spectralNorm A = ‖A‖ := rfl

theorem euclideanOperator_le (A : Matrix m n ℝ) (x : EuclideanSpace ℝ n) :
    ‖euclideanOperator A x‖ ≤ spectralNorm A * ‖x‖ :=
  (euclideanOperator A).le_opNorm x

/-- A bilinear test vector gives a certified lower bound on the spectral norm. -/
theorem bilinear_le_spectralNorm (A : Matrix m n ℝ)
    (x : EuclideanSpace ℝ m) (y : EuclideanSpace ℝ n) :
    |⟪x, euclideanOperator A y⟫| ≤ ‖x‖ * spectralNorm A * ‖y‖ := by
  calc
    _ ≤ ‖x‖ * ‖euclideanOperator A y‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖x‖ * (spectralNorm A * ‖y‖) :=
      mul_le_mul_of_nonneg_left (euclideanOperator_le A y) (norm_nonneg x)
    _ = _ := by ring

theorem unit_bilinear_le_spectralNorm (A : Matrix m n ℝ)
    (x : EuclideanSpace ℝ m) (y : EuclideanSpace ℝ n)
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    |⟪x, euclideanOperator A y⟫| ≤ spectralNorm A := by
  simpa [hx, hy] using bilinear_le_spectralNorm A x y

open scoped Matrix.Norms.L2Operator in
theorem spectralNorm_mul (A : Matrix m n ℝ) (B : Matrix n k ℝ) :
    spectralNorm (A * B) ≤ spectralNorm A * spectralNorm B :=
  Matrix.l2_opNorm_mul A B

variable [DecidableEq m]

open scoped Matrix.Norms.L2Operator in
theorem spectralNorm_transpose (A : Matrix m n ℝ) : spectralNorm A.transpose = spectralNorm A := by
  simpa only [spectralNorm_eq_l2Operator, Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.l2_opNorm_conjTranspose A

/-- Restriction to an injectively chosen list of coordinates. -/
def restrictionMatrix (e : m ↪ n) : Matrix m n ℝ :=
  Matrix.of (fun i j => if e i = j then 1 else 0)

omit [Fintype m] [Fintype n] [DecidableEq m] in
@[simp] theorem restrictionMatrix_apply (e : m ↪ n) (i : m) (j : n) :
    restrictionMatrix e i j = if e i = j then 1 else 0 := rfl

omit [DecidableEq m] in
@[simp] theorem restrictionOperator_apply (e : m ↪ n) (x : EuclideanSpace ℝ n) (i : m) :
    euclideanOperator (restrictionMatrix e) x i = x (e i) := by
  simp [euclideanOperator_apply, restrictionMatrix, ite_mul]

omit [DecidableEq m] in
/-- Coordinate restriction does not increase Euclidean norm. -/
theorem restrictionOperator_norm_le (e : m ↪ n) (x : EuclideanSpace ℝ n) :
    ‖euclideanOperator (restrictionMatrix e) x‖ ≤ ‖x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  simp only [restrictionOperator_apply]
  calc
    ∑ i : m, ‖x (e i)‖ ^ 2 = ∑ j ∈ Finset.univ.image e, ‖x j‖ ^ 2 := by
      rw [Finset.sum_image]
      intro i _ j _ hij
      exact e.injective hij
    _ ≤ ∑ j : n, ‖x j‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun j _ _ => sq_nonneg ‖x j‖)

omit [DecidableEq m] in
theorem restrictionMatrix_spectralNorm_le (e : m ↪ n) : spectralNorm (restrictionMatrix e) ≤ 1 := by
  apply (euclideanOperator (restrictionMatrix e)).opNorm_le_bound zero_le_one
  intro x
  simpa using restrictionOperator_norm_le e x

omit [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q] in
/-- Submatrix restriction is multiplication by coordinate restriction matrices. -/
theorem submatrix_eq_restrictions (A : Matrix m n ℝ) (e : p ↪ m) (f : q ↪ n) :
    A.submatrix e f = restrictionMatrix e * A * (restrictionMatrix f).transpose := by
  ext i j
  simp [Matrix.mul_apply, restrictionMatrix, Matrix.transpose_apply, ite_mul, mul_ite]

omit [DecidableEq p] in
/-- Every injective row/column compression has smaller Euclidean operator norm. -/
theorem spectralNorm_submatrix_le (A : Matrix m n ℝ) (e : p ↪ m) (f : q ↪ n) :
    spectralNorm (A.submatrix e f) ≤ spectralNorm A := by
  rw [submatrix_eq_restrictions]
  calc
    spectralNorm (restrictionMatrix e * A * (restrictionMatrix f).transpose) ≤
        spectralNorm (restrictionMatrix e * A) * spectralNorm (restrictionMatrix f).transpose :=
      spectralNorm_mul _ _
    _ ≤ (spectralNorm (restrictionMatrix e) * spectralNorm A) *
        spectralNorm (restrictionMatrix f).transpose :=
      mul_le_mul_of_nonneg_right (spectralNorm_mul _ _) (spectralNorm_nonneg _)
    _ ≤ (1 * spectralNorm A) * 1 := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right (restrictionMatrix_spectralNorm_le e)
          (spectralNorm_nonneg A)
      · rw [spectralNorm_transpose]
        exact restrictionMatrix_spectralNorm_le f
      · exact spectralNorm_nonneg _
      · exact mul_nonneg zero_le_one (spectralNorm_nonneg A)
    _ = _ := by ring

/-- The localized matrix in report 63 is an actual operator compression. -/
theorem crossed_localized_norm_le {N : ℕ} (W : Matrix (Fin N) (Fin N) ℝ) (a d : Fin N) :
    spectralNorm (CrossedEdges.localizedMatrix W a d) ≤
      spectralNorm (CrossedEdges.crossedMatrix W) := by
  let e : CrossedEdges.BlockIndex a d ↪ Fin N × Fin N :=
    ⟨fun b => (a, b.val), fun _ _ h => Subtype.ext (Prod.mk.inj h).2⟩
  let f : CrossedEdges.BlockIndex a d ↪ Fin N × Fin N :=
    ⟨fun c => (c.val, d), fun _ _ h => Subtype.ext (Prod.mk.inj h).1⟩
  exact spectralNorm_submatrix_le (CrossedEdges.crossedMatrix W) e f

/-- A two-vertex crossed-edges matrix vanishes because its boundaries cannot be injective. -/
theorem crossed_two_vertices_zero (W : Matrix (Fin 2) (Fin 2) ℝ) :
    CrossedEdges.crossedMatrix W = 0 := by
  ext ⟨a, b⟩ ⟨c, d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [CrossedEdges.crossedMatrix, CrossedEdges.BoundaryDistinct]

/-- The lower bound (n-3)(L-2) needs a size qualification: at n=2 its
right side is 2 while the actual crossed-edges norm is zero. -/
theorem crossed_lower_bound_small_size_counterexample :
    let W : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of (fun i j => if i = j then 0 else 1)
    IsSignMatrix W ∧ spectralNorm (CrossedEdges.crossedMatrix W) = 0 ∧
      ((2 : ℝ) - 3) * (max |(W * W) 0 1| |(W * W) 1 0| - 2) = 2 := by
  dsimp only
  constructor
  · constructor
    · intro i j
      change (if i = j then 0 else 1 : ℝ) = if j = i then 0 else 1
      simp [eq_comm]
    · intro i
      change (if i = i then 0 else 1 : ℝ) = 0
      simp
    · intro i j hij
      change (if i = j then 0 else 1 : ℝ) * (if i = j then 0 else 1 : ℝ) = 1
      simp [hij]
  constructor
  · rw [crossed_two_vertices_zero, spectralNorm_zero]
  · norm_num [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.of]
    change max |(0 : ℝ) * 1 + 1 * 0| |1 * 0 + 0 * 1| = 0
    norm_num

end

end GraphMatrices
