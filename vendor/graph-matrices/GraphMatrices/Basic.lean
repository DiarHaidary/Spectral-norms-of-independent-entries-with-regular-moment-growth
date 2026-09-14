import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic

/-! Basic shared conventions for the graph-matrix formalization. -/
namespace GraphMatrices

/-- A symmetric sign input with zero diagonal. Independence is a separate probabilistic property. -/
structure IsSignMatrix {ι : Type*} (W : Matrix ι ι ℝ) : Prop where
  symmetric : ∀ i j, W i j = W j i
  diagonal : ∀ i, W i i = 0
  sign_sq : ∀ i j, i ≠ j → W i j * W i j = 1

end GraphMatrices
