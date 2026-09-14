import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Actual finite graph matrices, with ordered boundaries and globally injective labels.
No matrix norm is introduced here: the default norm on matrices is not silently
identified with the Euclidean operator norm. -/

namespace GraphMatrices

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {n r s : ℕ}

noncomputable def edgeWeight (W : Matrix (Fin n) (Fin n) ℝ)
    (hW : ∀ i j, W i j = W j i) (φ : α → Fin n) : Sym2 α → ℝ :=
  Sym2.lift ⟨fun a b => W (φ a) (φ b), fun a b => hW (φ a) (φ b)⟩

omit [Fintype α] [DecidableEq α] in
@[simp] theorem edgeWeight_mk (W : Matrix (Fin n) (Fin n) ℝ)
    (hW : ∀ i j, W i j = W j i) (φ : α → Fin n) (a b : α) :
    edgeWeight W hW φ s(a, b) = W (φ a) (φ b) := by
  simp [edgeWeight]

noncomputable def graphMatrix (G : SimpleGraph α)
    (left : Fin r ↪ α) (right : Fin s ↪ α)
    (W : Matrix (Fin n) (Fin n) ℝ) (hW : ∀ i j, W i j = W j i) :
    Matrix (Fin r → Fin n) (Fin s → Fin n) ℝ := by
  classical
  exact fun row col =>
    ∑ φ : α → Fin n,
      if Function.Injective φ ∧
          (∀ i, φ (left i) = row i) ∧ (∀ j, φ (right j) = col j)
      then ∏ e ∈ G.edgeFinset, edgeWeight W hW φ e
      else 0

theorem graphMatrix_zero_of_row_not_injective (G : SimpleGraph α)
    (left : Fin r ↪ α) (right : Fin s ↪ α)
    (W : Matrix (Fin n) (Fin n) ℝ) (hW : ∀ i j, W i j = W j i)
    (row : Fin r → Fin n) (col : Fin s → Fin n)
    (hrow : ¬ Function.Injective row) :
    graphMatrix G left right W hW row col = 0 := by
  classical
  unfold graphMatrix
  apply Finset.sum_eq_zero
  intro φ _
  split_ifs with h
  · exfalso
    apply hrow
    intro i j hij
    apply left.injective
    apply h.1
    simpa only [h.2.1 i, h.2.1 j] using hij
  · rfl

theorem graphMatrix_zero_of_col_not_injective (G : SimpleGraph α)
    (left : Fin r ↪ α) (right : Fin s ↪ α)
    (W : Matrix (Fin n) (Fin n) ℝ) (hW : ∀ i j, W i j = W j i)
    (row : Fin r → Fin n) (col : Fin s → Fin n)
    (hcol : ¬ Function.Injective col) :
    graphMatrix G left right W hW row col = 0 := by
  classical
  unfold graphMatrix
  apply Finset.sum_eq_zero
  intro φ _
  split_ifs with h
  · exfalso
    apply hcol
    intro i j hij
    apply right.injective
    apply h.1
    simpa only [h.2.2 i, h.2.2 j] using hij
  · rfl

/-- Distinct shape vertices on opposite boundaries cannot share an ambient label. -/
theorem graphMatrix_zero_of_cross_collision (G : SimpleGraph α)
    (left : Fin r ↪ α) (right : Fin s ↪ α)
    (W : Matrix (Fin n) (Fin n) ℝ) (hW : ∀ i j, W i j = W j i)
    (row : Fin r → Fin n) (col : Fin s → Fin n)
    (i : Fin r) (j : Fin s) (hdistinct : left i ≠ right j)
    (hcollision : row i = col j) :
    graphMatrix G left right W hW row col = 0 := by
  classical
  unfold graphMatrix
  apply Finset.sum_eq_zero
  intro φ _
  split_ifs with h
  · exfalso
    apply hdistinct
    apply h.1
    simpa only [h.2.1 i, h.2.2 j] using hcollision
  · rfl

/-- Common shape vertices must have the same label in both boundaries. -/
theorem graphMatrix_zero_of_shared_vertex_mismatch (G : SimpleGraph α)
    (left : Fin r ↪ α) (right : Fin s ↪ α)
    (W : Matrix (Fin n) (Fin n) ℝ) (hW : ∀ i j, W i j = W j i)
    (row : Fin r → Fin n) (col : Fin s → Fin n)
    (i : Fin r) (j : Fin s) (hsame : left i = right j)
    (hmismatch : row i ≠ col j) :
    graphMatrix G left right W hW row col = 0 := by
  classical
  unfold graphMatrix
  apply Finset.sum_eq_zero
  intro φ _
  split_ifs with h
  · exfalso
    apply hmismatch
    rw [← h.2.1 i, ← h.2.2 j, hsame]
  · rfl

end GraphMatrices
