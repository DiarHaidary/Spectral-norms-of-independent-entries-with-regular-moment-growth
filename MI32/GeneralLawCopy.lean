import MI32.DeletionMomentEndpoints
import MI32.MatrixCopySymmetrization

/-!
# The actual symmetric copy of an original regular-entry matrix

The copied matrix is exactly `X(ω) - X(ω')` on the product of the original
probability law with itself. Its independent, centered, symmetric entries
and its regularity parameter `2 * α` are derived from the literal original
`RegularEntries` assumptions. The public Euclidean operator mean is
dominated by that of this actual copy, with no replacement of the indices.
-/

noncomputable section
open MeasureTheory ProbabilityTheory

namespace MI32.GeneralLawCopy

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ}

/-- The actual independent-copy matrix, with the original row and column indices. -/
def matrixCopy (X : Ω → Matrix (Fin n) (Fin n) ℝ) (z : Ω × Ω) :
    Matrix (Fin n) (Fin n) ℝ := X z.1 - X z.2

omit [MeasurableSpace Ω] in
@[simp] theorem matrixCopy_apply (X : Ω → Matrix (Fin n) (Fin n) ℝ)
    (z : Ω × Ω) (i j : Fin n) : matrixCopy X z i j = X z.1 i j - X z.2 i j := rfl

/-- The requested original entry integrability follows from its p=1
absolute-moment hypothesis, rather than being supplied separately. -/
theorem integrable_entry (α : ℝ) (X : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hX : RegularEntries μ α X) (i j : Fin n) : Integrable (fun ω => X ω i j) μ := by
  have hmem := MomentTools.memLp_of_integrable_abs_rpow 1 zero_lt_one
    (fun ω => X ω i j) (hX.1 i j).aestronglyMeasurable
    (hX.2.2.2.1 i j 1 zero_lt_one)
  exact hmem.integrable (by norm_num)

/-- Reflection symmetry is furnished by interchanging the two original copies. -/
theorem entry_symmetric (α : ℝ) (X : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hX : RegularEntries μ α X) (i j : Fin n) :
    IdentDistrib (fun z => matrixCopy X z i j) (fun z => -matrixCopy X z i j)
      (μ.prod μ) (μ.prod μ) :=
  MatrixCopySymmetrization.symmetric_difference
    (fun e : Fin n × Fin n => fun ω => X ω e.1 e.2) (fun e => hX.1 e.1 e.2) (i, j)

/-- The copied entry law meets the entire original regular-entry definition
with doubling parameter `2 * α`. The lower comparison in this proof is the
proved real-order Jensen inequality for the original centered variable. -/
theorem regular_entries (α : ℝ) (hα : 1 ≤ α)
    (X : Ω → Matrix (Fin n) (Fin n) ℝ) (hX : RegularEntries μ α X) :
    RegularEntries (μ.prod μ) (2 * α) (matrixCopy X) := by
  rcases hX with ⟨hmeas, hind, hmean, hint, hregular⟩
  have hi : ∀ i j, Integrable (fun ω => X ω i j) μ :=
    integrable_entry α X ⟨hmeas, hind, hmean, hint, hregular⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    exact MatrixCopySymmetrization.measurable_difference
      (fun e : Fin n × Fin n => fun ω => X ω e.1 e.2) (fun e => hmeas e.1 e.2) (i, j)
  · exact MatrixCopySymmetrization.independent_differences
      (fun e : Fin n × Fin n => fun ω => X ω e.1 e.2) (fun e => hmeas e.1 e.2) hind
  · intro i j
    exact MatrixCopySymmetrization.integral_difference
      (fun e : Fin n × Fin n => fun ω => X ω e.1 e.2) (fun e => hi e.1 e.2) (i, j)
  · intro i j p hp
    exact MatrixCopySymmetrization.integrable_difference_abs_rpow
      (fun e : Fin n × Fin n => fun ω => X ω e.1 e.2)
      (fun e => hmeas e.1 e.2) (fun e => hint e.1 e.2) (i, j) p hp
  · intro i j r hr
    have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
    have hupper := DeletionMomentEndpoints.copy_moment_le_two
      (fun ω => X ω i j) (hmeas i j) (2 * r) (by linarith) (hint i j (2 * r) (by positivity))
    have hlower := DeletionMomentEndpoints.mean_zero_moment_le_copy
      (fun ω => X ω i j) (hmeas i j) (hmean i j) r hr (hint i j r hr0)
    calc
      _ ≤ 2 * moment μ (2 * r) (fun ω => X ω i j) := hupper
      _ ≤ 2 * (α * moment μ r (fun ω => X ω i j)) :=
        mul_le_mul_of_nonneg_left (hregular i j r hr) (by norm_num)
      _ = (2 * α) * moment μ r (fun ω => X ω i j) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hlower (by positivity)

/-- Centering makes the copied second moment exactly twice the original
second moment, with both original integrability conditions derived. -/
theorem integral_copy_entry_sq (α : ℝ) (X : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hX : RegularEntries μ α X) (i j : Fin n) :
    (∫ z, (matrixCopy X z i j) ^ 2 ∂(μ.prod μ)) =
      2 * ∫ ω, (X ω i j) ^ 2 ∂μ := by
  apply MatrixCopySymmetrization.integral_difference_sq (fun ω => X ω i j)
    (integrable_entry α X hX i j) _ (hX.2.2.1 i j)
  simpa only [Real.rpow_two, sq_abs] using hX.2.2.2.1 i j 2 (by norm_num)

/-- Symmetrization of the original public spectral mean, including
integrability of the original and copied operator norms. -/
theorem spectral_mean_le_copy (α : ℝ) (X : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hX : RegularEntries μ α X) :
    Integrable (fun ω => spectralNorm (X ω)) μ ∧
      Integrable (fun z => spectralNorm (matrixCopy X z)) (μ.prod μ) ∧
      (∫ ω, spectralNorm (X ω) ∂μ) ≤
        ∫ z, spectralNorm (matrixCopy X z) ∂(μ.prod μ) :=
  MatrixCopySymmetrization.spectral_mean_le_copy X (integrable_entry α X hX) hX.2.2.1

end MI32.GeneralLawCopy
