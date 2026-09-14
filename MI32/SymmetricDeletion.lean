import MI32.NearMaskMean
import MI32.FarMaskMean
import MI32.SymmetrizationReduction

/-!
# The symmetric-law deletion theorem

The five deterministic masks of `DeletionMasks` are estimated separately: the
initial block by its entry energy, the two two-shell block families by the
scheduled local moments, and the two far orientations by the elementary
centered Gram argument. Their sum is the original operator mean, so the
symmetric-law deletion bound follows with an explicit constant depending only
on the regularity parameter. Composing with the already-proved original-copy
symmetrization reduction gives the full general-law upper bound.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory

namespace MI32.SymmetricDeletion

universe u

/-- The variance coefficient: the initial block, the two far orientations, and
the variance part of the two block families. -/
def varianceCoeff (α : ℝ) : ℝ :=
  Real.sqrt 31 + 2 * Real.sqrt (1 + Real.sqrt 2 * α ^ 2)
    + 24 * Real.exp 1 * (5 : ℝ) ^ (1 / 4 : ℝ) * Real.sqrt 3 * α ^ 2

/-- The deletion coefficient: the weak-moment part of the two block families,
after the ten scalar doublings that raise the exact logarithmic order to the
scheduled one. -/
def deletionCoeff (α : ℝ) : ℝ :=
  144 * Real.exp 1 * (5 : ℝ) ^ (1 / 4 : ℝ) * Real.sqrt 3 * α ^ 6
    * SymmetricLinearAllOrders.doublingConstant α ^ 10

/-- The explicit constant of the symmetric-law deletion estimate. -/
def deletionConstant (α : ℝ) : ℝ := varianceCoeff α + deletionCoeff α

theorem varianceCoeff_pos (α : ℝ) : 0 < varianceCoeff α := by
  unfold varianceCoeff
  positivity

theorem deletionCoeff_nonneg (α : ℝ) : 0 ≤ deletionCoeff α := by
  unfold deletionCoeff SymmetricLinearAllOrders.doublingConstant
  positivity

theorem deletionConstant_pos (α : ℝ) : 0 < deletionConstant α :=
  add_pos_of_pos_of_nonneg (varianceCoeff_pos α) (deletionCoeff_nonneg α)

/-- The five mask bounds combine into the two literal budgets. Every
coefficient is nonnegative, so the separate variance and deletion parts are
absorbed into one constant. -/
theorem five_masks_le (α B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D) :
    Real.sqrt 31 * B + 3 * NearBlockMoment.blockBound α B D
        + 3 * NearBlockMoment.blockBound α B D
        + B * Real.sqrt (1 + Real.sqrt 2 * α ^ 2)
        + B * Real.sqrt (1 + Real.sqrt 2 * α ^ 2)
      ≤ deletionConstant α * (B + D) := by
  have hv : (0 : ℝ) ≤ varianceCoeff α := (varianceCoeff_pos α).le
  have hd : (0 : ℝ) ≤ deletionCoeff α := deletionCoeff_nonneg α
  have hEq : Real.sqrt 31 * B + 3 * NearBlockMoment.blockBound α B D
        + 3 * NearBlockMoment.blockBound α B D
        + B * Real.sqrt (1 + Real.sqrt 2 * α ^ 2)
        + B * Real.sqrt (1 + Real.sqrt 2 * α ^ 2)
      = varianceCoeff α * B + deletionCoeff α * D := by
    unfold varianceCoeff deletionCoeff NearBlockMoment.blockBound
      RawMultiplicationContraction.contractionConstant
    ring
  rw [hEq, deletionConstant]
  nlinarith [mul_nonneg hv hD, mul_nonneg hd hB]

section Bound

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {n : ℕ}

/-- The symmetric-law deletion estimate on an arbitrary probability space, with
the literal `varianceScale` and `deletionScale` of the source problem. The
operator-norm integrability is derived from the five mask estimates. -/
theorem integrable_and_mean_spectralNorm_le (hn : 1 ≤ n)
    (X : Ω → Matrix (Fin n) (Fin n) ℝ) (α : ℝ) (hα : 1 ≤ α)
    (hReg : RegularEntries μ α X)
    (hsym : ∀ i j, IdentDistrib (fun ω => X ω i j) (fun ω => -X ω i j) μ μ) :
    Integrable (fun ω => spectralNorm (X ω)) μ ∧
      (∫ ω, spectralNorm (X ω) ∂μ) ≤
        deletionConstant α * (varianceScale μ X + deletionScale μ X) := by
  obtain ⟨hLowI, hLow⟩ := NearMaskMean.mean_nearLow_le hn X α hReg
  obtain ⟨hHighI, hHigh⟩ := NearMaskMean.mean_nearHigh_le hn X α hα hReg hsym
  obtain ⟨hCrossI, hCross⟩ := NearMaskMean.mean_nearCross_le hn X α hα hReg hsym
  obtain ⟨hFarLowI, hFarLow⟩ := FarMaskMean.mean_farLow_le hn X α hα hReg
  obtain ⟨hFarUpI, hFarUp⟩ := FarMaskMean.mean_farUp_le hn X α hα hReg
  have h12 : Integrable (fun ω =>
      ‖DeletionMasks.nearLow μ X ω‖ + ‖DeletionMasks.nearHigh μ X ω‖) μ := hLowI.add hHighI
  have h123 : Integrable (fun ω =>
      ‖DeletionMasks.nearLow μ X ω‖ + ‖DeletionMasks.nearHigh μ X ω‖
        + ‖DeletionMasks.nearCross μ X ω‖) μ := h12.add hCrossI
  have h1234 : Integrable (fun ω =>
      ‖DeletionMasks.nearLow μ X ω‖ + ‖DeletionMasks.nearHigh μ X ω‖
        + ‖DeletionMasks.nearCross μ X ω‖ + ‖DeletionMasks.farLow μ X ω‖) μ :=
    h123.add hFarLowI
  have hT : Integrable (fun ω =>
      ‖DeletionMasks.nearLow μ X ω‖ + ‖DeletionMasks.nearHigh μ X ω‖
        + ‖DeletionMasks.nearCross μ X ω‖ + ‖DeletionMasks.farLow μ X ω‖
        + ‖DeletionMasks.farUp μ X ω‖) μ := h1234.add hFarUpI
  have hmeas : Measurable (fun ω => ‖X ω‖) :=
    BlockMaskMoment.measurable_norm X hReg.1
  have hdom := DeletionMasks.norm_le_masks (μ := μ) X
  have hXI : Integrable (fun ω => ‖X ω‖) μ :=
    hT.mono' hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
        exact hdom ω)
  have hsplit : (∫ ω,
        (‖DeletionMasks.nearLow μ X ω‖ + ‖DeletionMasks.nearHigh μ X ω‖
          + ‖DeletionMasks.nearCross μ X ω‖ + ‖DeletionMasks.farLow μ X ω‖
          + ‖DeletionMasks.farUp μ X ω‖) ∂μ)
      = (∫ ω, ‖DeletionMasks.nearLow μ X ω‖ ∂μ)
        + (∫ ω, ‖DeletionMasks.nearHigh μ X ω‖ ∂μ)
        + (∫ ω, ‖DeletionMasks.nearCross μ X ω‖ ∂μ)
        + (∫ ω, ‖DeletionMasks.farLow μ X ω‖ ∂μ)
        + (∫ ω, ‖DeletionMasks.farUp μ X ω‖ ∂μ) := by
    rw [integral_add h1234 hFarUpI, integral_add h123 hFarLowI,
      integral_add h12 hCrossI, integral_add hLowI hHighI]
  refine ⟨hXI, ?_⟩
  calc
    (∫ ω, spectralNorm (X ω) ∂μ) = ∫ ω, ‖X ω‖ ∂μ := rfl
    _ ≤ ∫ ω,
        (‖DeletionMasks.nearLow μ X ω‖ + ‖DeletionMasks.nearHigh μ X ω‖
          + ‖DeletionMasks.nearCross μ X ω‖ + ‖DeletionMasks.farLow μ X ω‖
          + ‖DeletionMasks.farUp μ X ω‖) ∂μ := integral_mono hXI hT hdom
    _ = _ := hsplit
    _ ≤ Real.sqrt 31 * varianceScale μ X
        + 3 * NearBlockMoment.blockBound α (varianceScale μ X) (deletionScale μ X)
        + 3 * NearBlockMoment.blockBound α (varianceScale μ X) (deletionScale μ X)
        + varianceScale μ X * Real.sqrt (1 + Real.sqrt 2 * α ^ 2)
        + varianceScale μ X * Real.sqrt (1 + Real.sqrt 2 * α ^ 2) :=
      add_le_add (add_le_add (add_le_add (add_le_add hLow hHigh) hCross) hFarLow) hFarUp
    _ ≤ deletionConstant α * (varianceScale μ X + deletionScale μ X) :=
      five_masks_le α _ _ (VarianceScaleBasics.varianceScale_nonneg X hn)
        (WeakMomentBasics.deletionScale_nonneg μ X)

end Bound

/-- The remaining premise of the checked symmetrization reduction: the original
upper bound for independent symmetric regular entries, with one shared
deterministic deletion set on both axes and the literal subunit order. -/
theorem symmetricUpperBoundAt (α : ℝ) (hα : 1 ≤ α) :
    SymmetrizationReduction.SymmetricUpperBoundAt.{u} α (deletionConstant α) := by
  intro n hn Ω mΩ μ hμ X hReg hsym
  let : MeasurableSpace Ω := mΩ
  let : IsProbabilityMeasure μ := hμ
  exact (integrable_and_mean_spectralNorm_le hn X α hα hReg hsym).2

/-- The full original general-law upper bound at an explicit constant. -/
theorem upperBoundAt (α : ℝ) (hα : 1 ≤ α) :
    UpperBoundAt.{u} α (deletionConstant (2 * α) * Real.exp 1) :=
  SymmetrizationReduction.upperBoundAt_of_symmetric α (deletionConstant (2 * α)) hα
    (deletionConstant_pos _).le (symmetricUpperBoundAt (2 * α) (by linarith))

/-- The existential form of the original MI-32 upper conjecture. -/
theorem exists_upperBoundAt (α : ℝ) (hα : 1 ≤ α) :
    ∃ C : ℝ, 0 < C ∧ UpperBoundAt.{u} α C :=
  ⟨deletionConstant (2 * α) * Real.exp 1,
    mul_pos (deletionConstant_pos _) (Real.exp_pos 1), upperBoundAt α hα⟩

end MI32.SymmetricDeletion
