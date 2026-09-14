import MI32.GeneralLawCopy
import MI32.CopyDeletionScale
import MI32.VarianceScaleBasics

/-!
# Reduction of the exact general-law target to its symmetric-law case

All copy, regularity, operator, variance and same-set deletion comparisons
are proved from the original law. The remaining symmetric deletion theorem
is explicitly a premise here. This modular reduction does not prove that
remaining theorem or discharge `MI32.main_upper` by itself.
-/

noncomputable section
open MeasureTheory ProbabilityTheory

namespace MI32.SymmetrizationReduction

universe u

/-- The original upper-bound assertion restricted to symmetric entry laws.
This is the remaining matrix estimate, not an assumption on individual inputs. -/
def SymmetricUpperBoundAt (α C : ℝ) : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (Ω : Type u) (mΩ : MeasurableSpace Ω)
    (μ : @Measure Ω mΩ), @IsProbabilityMeasure Ω mΩ μ →
    ∀ (X : Ω → Matrix (Fin n) (Fin n) ℝ),
      @RegularEntries Ω mΩ n μ α X →
      (∀ i j, @IdentDistrib Ω Ω ℝ mΩ mΩ inferInstance
        (fun ω => X ω i j) (fun ω => -X ω i j) μ μ) →
      (∫ ω, spectralNorm (X ω) ∂μ) ≤
        C * (varianceScale μ X + deletionScale μ X)

theorem varianceScale_copy {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {n : ℕ}
    (α : ℝ) (X : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hX : RegularEntries μ α X) (hn : 1 ≤ n) :
    varianceScale (μ.prod μ) (GeneralLawCopy.matrixCopy X) =
      Real.sqrt 2 * varianceScale μ X :=
  VarianceScaleBasics.varianceScale_of_entry_second_moments
    X (GeneralLawCopy.matrixCopy X) hn 2 (by norm_num)
    (GeneralLawCopy.integral_copy_entry_sq α X hX)

theorem deletionScale_copy {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {n : ℕ}
    (α : ℝ) (X : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hX : RegularEntries μ α X) (hn : 1 ≤ n) :
    deletionScale (μ.prod μ) (GeneralLawCopy.matrixCopy X) ≤
      Real.exp 1 * deletionScale μ X :=
  CopyDeletionScale.deletionScale_copy_le X hX.1 hX.2.2.2.1 hn

/-- Once the symmetric deletion bound at parameter `2 * α` is supplied,
the literal full target follows with the explicit further factor `exp 1`.
In particular the subunit deletion order and shared original index budget
are preserved by this reduction. -/
theorem upperBoundAt_of_symmetric (α C : ℝ) (hα : 1 ≤ α) (hC : 0 ≤ C)
    (hSym : SymmetricUpperBoundAt.{u} (2 * α) C) :
    UpperBoundAt.{u} α (C * Real.exp 1) := by
  intro n hn Ω mΩ μ hμ X hX
  let : MeasurableSpace Ω := mΩ
  let : IsProbabilityMeasure μ := hμ
  have hcopy := GeneralLawCopy.regular_entries α hα X hX
  have hbound := hSym n hn (Ω × Ω) inferInstance (μ.prod μ) inferInstance
    (GeneralLawCopy.matrixCopy X) hcopy (GeneralLawCopy.entry_symmetric α X hX)
  have hnorm := (GeneralLawCopy.spectral_mean_le_copy α X hX).2.2
  have hvar := varianceScale_copy α X hX hn
  have hdel := deletionScale_copy α X hX hn
  have hM := VarianceScaleBasics.varianceScale_nonneg (μ := μ) X hn
  have he : (2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hsqrt : Real.sqrt 2 ≤ Real.exp 1 :=
    (show Real.sqrt 2 ≤ 2 by norm_num).trans he
  calc
    (∫ ω, spectralNorm (X ω) ∂μ) ≤
        ∫ z, spectralNorm (GeneralLawCopy.matrixCopy X z) ∂(μ.prod μ) := hnorm
    _ ≤ C * (varianceScale (μ.prod μ) (GeneralLawCopy.matrixCopy X) +
        deletionScale (μ.prod μ) (GeneralLawCopy.matrixCopy X)) := hbound
    _ ≤ C * (Real.exp 1 * varianceScale μ X + Real.exp 1 * deletionScale μ X) := by
      apply mul_le_mul_of_nonneg_left _ hC
      rw [hvar]
      exact add_le_add (mul_le_mul_of_nonneg_right hsqrt hM) hdel
    _ = C * Real.exp 1 * (varianceScale μ X + deletionScale μ X) := by ring

end MI32.SymmetrizationReduction
