import MI32.PositiveVacuumWords
import MI32.ThinMatrix
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Original rectangular operator inside its symmetric bipartite lift

All matrix norms in this file are the actual Euclidean operator norm through
`Matrix.Norms.L2Operator`. Canonical left/right embeddings preserve Euclidean
norms, and the lift acts on a right-supported vector by the original matrix.
The proof works when either or both original index types are empty.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open MeasureTheory

namespace MI32.BipartiteNorm

open PositiveVacuumWords

variable {R C : Type*} [Fintype R] [Fintype C] [DecidableEq R] [DecidableEq C]

/-- Original rectangular entries, in the original row/column orientation. -/
def rectangular (z : R × C → ℝ) : Matrix R C ℝ := fun i j => z (i, j)

/-- Canonical left-side Euclidean embedding, zero on every right coordinate. -/
def left (s : EuclideanSpace ℝ R) : EuclideanSpace ℝ (Sum R C) :=
  WithLp.toLp 2 (Sum.elim s (fun _ => 0))

/-- Canonical right-side Euclidean embedding, zero on every left coordinate. -/
def right (t : EuclideanSpace ℝ C) : EuclideanSpace ℝ (Sum R C) :=
  WithLp.toLp 2 (Sum.elim (fun _ => 0) t)

omit [DecidableEq R] [DecidableEq C] in
@[simp] theorem norm_left (s : EuclideanSpace ℝ R) : ‖left (C := C) s‖ = ‖s‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp [EuclideanSpace.real_norm_sq_eq, left, Fintype.sum_sum_type]

omit [DecidableEq R] [DecidableEq C] in
@[simp] theorem norm_right (t : EuclideanSpace ℝ C) : ‖right (R := R) t‖ = ‖t‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp [EuclideanSpace.real_norm_sq_eq, right, Fintype.sum_sum_type]

/-- The left inclusion as an isometry, including empty coordinate spaces. -/
def leftIsometry : EuclideanSpace ℝ R →ₗᵢ[ℝ] EuclideanSpace ℝ (Sum R C) where
  toFun := left
  map_add' s t := by ext v; cases v <;> simp [left]
  map_smul' a s := by ext v; cases v <;> simp [left]
  norm_map' := norm_left

/-- The right inclusion as an isometry, including empty coordinate spaces. -/
def rightIsometry : EuclideanSpace ℝ C →ₗᵢ[ℝ] EuclideanSpace ℝ (Sum R C) where
  toFun := right
  map_add' s t := by ext v; cases v <;> simp [right]
  map_smul' a s := by ext v; cases v <;> simp [right]
  norm_map' := norm_right

def rectangularOperator (z : R × C → ℝ) : EuclideanSpace ℝ C →L[ℝ] EuclideanSpace ℝ R :=
  (Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap) (rectangular z)

def bipartiteOperator (z : R × C → ℝ) :
    EuclideanSpace ℝ (Sum R C) →L[ℝ] EuclideanSpace ℝ (Sum R C) :=
  (Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap) (matrix bipartiteWeight z)

/-- Exact action on one original side. Both block orientations continue to
use the same original variable `z(i,j)`. -/
theorem bipartiteOperator_apply_right (z : R × C → ℝ) (t : EuclideanSpace ℝ C) :
    bipartiteOperator z (right t) = left (rectangularOperator z t) := by
  ext v
  cases v with
  | inl i =>
    change (∑ v, matrix bipartiteWeight z (.inl i) v * right t v) =
      ∑ j, z (i, j) * t j
    rw [Fintype.sum_sum_type]
    simp [right]
  | inr j =>
    change (∑ v, matrix bipartiteWeight z (.inr j) v * right t v) = 0
    rw [Fintype.sum_sum_type]
    simp [right]

/-- The actual original rectangular operator incurs no factor when embedded
in its symmetric bipartite matrix. No nonempty-axis condition is required. -/
theorem rectangular_norm_le_bipartite (z : R × C → ℝ) :
    ‖rectangular z‖ ≤ ‖matrix bipartiteWeight z‖ := by
  change ‖rectangularOperator z‖ ≤ ‖bipartiteOperator z‖
  apply (rectangularOperator z).opNorm_le_bound (norm_nonneg _)
  intro t
  calc
    ‖rectangularOperator z t‖ = ‖left (C := C) (rectangularOperator z t)‖ :=
      (norm_left _).symm
    _ = ‖bipartiteOperator z (right t)‖ := by rw [bipartiteOperator_apply_right]
    _ ≤ ‖bipartiteOperator z‖ * ‖right (R := R) t‖ :=
      (bipartiteOperator z).le_opNorm _
    _ = ‖bipartiteOperator z‖ * ‖t‖ := by rw [norm_right]

/-- The lift is self-adjoint in the actual real matrix star algebra. -/
theorem bipartite_isSelfAdjoint (z : R × C → ℝ) :
    IsSelfAdjoint (matrix bipartiteWeight z) := by
  change star (matrix bipartiteWeight z) = matrix bipartiteWeight z
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
  exact bipartite_matrix_transpose z

section Measurable

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Norm measurability follows directly from measurability of the original entries. -/
theorem measurable_bipartite_norm (X : R → C → Ω → ℝ)
    (hX : ∀ i j, Measurable (X i j)) :
    Measurable (fun ω => ‖matrix bipartiteWeight (fun e => X e.1 e.2 ω)‖) := by
  have hentry (v u : Sum R C) : Measurable
      (fun ω => matrix bipartiteWeight (fun e => X e.1 e.2 ω) u v) := by
    unfold matrix
    fun_prop
  exact ThinMatrix.measurable_norm_transposeOperator
    (fun v u ω => matrix bipartiteWeight (fun e => X e.1 e.2 ω) u v) hentry

omit [DecidableEq R] in
/-- The same measurability bridge for the original rectangular Euclidean norm. -/
theorem measurable_rectangular_norm (X : R → C → Ω → ℝ)
    (hX : ∀ i j, Measurable (X i j)) :
    Measurable (fun ω => ‖rectangular (fun e => X e.1 e.2 ω)‖) :=
  ThinMatrix.measurable_norm_transposeOperator (fun j i => X i j) (fun j i => hX i j)

end Measurable

end MI32.BipartiteNorm
