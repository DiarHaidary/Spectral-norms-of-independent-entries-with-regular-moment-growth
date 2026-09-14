import MI32.RestrictedThinMatrix

/-!
# Euclidean transpose duality and output-restricted thin matrices

Transposition is exactly Euclidean adjunction, hence preserves the operator
norm even when an axis is empty. The thin active-column estimate therefore
controls the operator with its output in the selected original columns,
which is the form used by direct annihilation.
-/

noncomputable section
open scoped BigOperators InnerProductSpace
open MeasureTheory ProbabilityTheory

namespace MI32.ThinTranspose

variable {Ω I J : Type*} [MeasurableSpace Ω] [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] {μ : Measure Ω}

omit [MeasurableSpace Ω] in
/-- The transpose of the original rectangular family gives the Euclidean
adjoint, with no nonemptiness hypothesis on either coordinate space. -/
theorem transposeOperator_transpose_eq_adjoint (X : I → J → Ω → ℝ) (ω : Ω) :
    ThinMatrix.transposeOperator (fun j i => X i j) ω =
      (ThinMatrix.transposeOperator X ω).adjoint := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro s t
  rw [real_inner_comm]
  simp only [ThinMatrix.transposeOperator_apply, ThinMatrix.inner_matrixRowImage_eq_bilinear]
  exact congrFun (AxisRestriction.thin_bilinear_transpose X s t) ω

omit [MeasurableSpace Ω] in
/-- Exact operator norm invariance under transposition on arbitrary finite axes. -/
theorem norm_transposeOperator_transpose (X : I → J → Ω → ℝ) (ω : Ω) :
    ‖ThinMatrix.transposeOperator (fun j i => X i j) ω‖ =
      ‖ThinMatrix.transposeOperator X ω‖ := by
  rw [transposeOperator_transpose_eq_adjoint]
  exact ContinuousLinearMap.adjoint.norm_map _

variable [IsProbabilityMeasure μ]

/-- The norm estimate for the actual map from all original rows into a selected
set of original columns. Only the original law, variance budget and original
weak tests occur in the hypotheses; integrability is also derived. -/
theorem output_cols_moment_four_mul_le
    (X : I → J → Ω → ℝ) (hX : ∀ i j, Measurable (X i j))
    (hind : iIndepFun (fun e : I × J => X e.1 e.2) μ)
    (hsym : ∀ i j, IdentDistrib (X i j) (fun ω => -X i j ω) μ μ)
    (hint : ∀ i j (p : ℝ), 0 < p → Integrable (fun ω => |X i j ω| ^ p) μ)
    (α : ℝ) (hα : 1 ≤ α)
    (hregular : ∀ i j (r : ℝ), 1 ≤ r →
      moment μ (2 * r) (X i j) ≤ α * moment μ r (X i j))
    (q : ℕ) (hq : 1 ≤ q) (T : Finset J) (hthin : T.card ≤ q)
    (B : ℝ) (hB : 0 ≤ B)
    (hcol : ∀ j, (∑ i, ∫ ω, X i j ω ^ 2 ∂μ) ≤ B ^ 2)
    (W : ℝ) (hW : 0 ≤ W)
    (hweak : ∀ s : EuclideanSpace ℝ I, ‖s‖ ≤ 1 →
      ∀ t : EuclideanSpace ℝ J, ‖t‖ ≤ 1 →
        moment μ (2 * (q : ℝ)) (ThinMatrix.bilinear X s t) ≤ W) :
    Integrable
      (fun ω => ‖ThinMatrix.transposeOperator (fun i (j : T) => X i j) ω‖ ^ (4 * q)) μ ∧
      moment μ (4 * (q : ℝ))
        (fun ω => ‖ThinMatrix.transposeOperator (fun i (j : T) => X i j) ω‖) ≤
        (2 : ℝ) * (5 : ℝ) ^ (1 / 4 : ℝ) * (B + 6 * α ^ 4 * W) := by
  have hnorm (ω : Ω) :
      ‖ThinMatrix.transposeOperator (fun i (j : T) => X i j) ω‖ =
        ‖ThinMatrix.transposeOperator (fun (j : T) i => X i j) ω‖ :=
    (norm_transposeOperator_transpose (fun i (j : T) => X i j) ω).symm
  simp_rw [hnorm]
  exact RestrictedThinMatrix.cols_moment_four_mul_le X hX hind hsym hint α hα hregular
    q hq T hthin B hB hcol W hW hweak

end MI32.ThinTranspose
