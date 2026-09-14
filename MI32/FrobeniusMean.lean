import MI32.CenteredGramNorm

/-!
# Frobenius energy controls the rectangular operator mean

The Euclidean operator norm of a rectangular real matrix is at most the square
root of its total entry energy. For a random rectangular matrix, the sum of
the second entry moments therefore controls the mean operator norm, with the
integrability of that norm derived rather than assumed. This is the estimate
for the one small initial block of the decomposition, where no deletion budget
is available.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open MeasureTheory

namespace MI32.FrobeniusMean

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

/-- Total squared entry energy of a rectangular original matrix. -/
def entryEnergy (A : Matrix V W ℝ) : ℝ := ∑ i, ∑ j, A i j ^ 2

omit [DecidableEq V] [DecidableEq W] in
/-- The entry energy is a sum of squares. -/
theorem entryEnergy_nonneg (A : Matrix V W ℝ) : 0 ≤ entryEnergy A :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

omit [DecidableEq V] in
/-- The squared Euclidean norm of every image is at most the entry energy times
the squared input norm, by the discrete Cauchy-Schwarz inequality on each row. -/
theorem norm_image_sq_le (A : Matrix V W ℝ) (x : EuclideanSpace ℝ W) :
    ‖(Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap) A x‖ ^ 2 ≤
      entryEnergy A * ‖x‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  change ∑ i, (∑ j, A i j * x j) ^ 2 ≤ entryEnergy A * ∑ j, x j ^ 2
  unfold entryEnergy
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun i _ => Finset.sum_mul_sq_le_sq_mul_sq _ _ _

omit [DecidableEq V] in
/-- The Euclidean operator norm never exceeds the square root of the Frobenius
energy, also for rectangular original axes. -/
theorem norm_le_sqrt_entryEnergy (A : Matrix V W ℝ) :
    ‖A‖ ≤ Real.sqrt (entryEnergy A) := by
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_
  rw [← Real.sqrt_sq (norm_nonneg x), ← Real.sqrt_mul (entryEnergy_nonneg A)]
  exact Real.le_sqrt_of_sq_le (norm_image_sq_le A x)

omit [DecidableEq V] in
/-- The Euclidean operator norm never exceeds the Frobenius energy, also for
rectangular original axes. -/
theorem norm_sq_le_entryEnergy (A : Matrix V W ℝ) : ‖A‖ ^ 2 ≤ entryEnergy A := by
  have h := norm_le_sqrt_entryEnergy A
  calc
    ‖A‖ ^ 2 ≤ Real.sqrt (entryEnergy A) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = entryEnergy A := Real.sq_sqrt (entryEnergy_nonneg A)

section Probability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [DecidableEq V] in
/-- Second entry moments alone control the actual operator mean, with derived
integrability. There is no positivity requirement on the bound. -/
theorem integrable_and_mean_norm_le (A : Ω → Matrix V W ℝ)
    (hA : ∀ i j, Measurable (fun ω => A ω i j))
    (hInt : ∀ i j, Integrable (fun ω => A ω i j ^ 2) μ)
    (K : ℝ) (hK : 0 ≤ K)
    (hBound : (∑ i, ∑ j, ∫ ω, A ω i j ^ 2 ∂μ) ≤ K ^ 2) :
    Integrable (fun ω => ‖A ω‖) μ ∧ (∫ ω, ‖A ω‖ ∂μ) ≤ K := by
  have hNorm : Measurable (fun ω => ‖A ω‖) :=
    ThinMatrix.measurable_norm_transposeOperator (fun j i ω => A ω i j) (fun j i => hA i j)
  have hEnergyInt : Integrable (fun ω => entryEnergy (A ω)) μ :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hInt i j
  have hNormInt : Integrable (fun ω => ‖A ω‖ ^ 2) μ :=
    hEnergyInt.mono' (hNorm.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact norm_sq_le_entryEnergy (A ω))
  apply CenteredGramNorm.mean_le_of_second_moment _ hNorm (fun _ => norm_nonneg _) hNormInt K hK
  calc
    (∫ ω, ‖A ω‖ ^ 2 ∂μ) ≤ ∫ ω, entryEnergy (A ω) ∂μ :=
      integral_mono hNormInt hEnergyInt (fun ω => norm_sq_le_entryEnergy (A ω))
    _ = ∑ i, ∑ j, ∫ ω, A ω i j ^ 2 ∂μ := by
      unfold entryEnergy
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => hInt i j)]
      apply Finset.sum_congr rfl
      intro i _
      exact integral_finsetSum _ (fun j _ => hInt i j)
    _ ≤ K ^ 2 := hBound

omit [DecidableEq V] in
/-- A masked original matrix supported on a finite index set has its mean norm
controlled by the surviving variance budget and that set's cardinality. -/
theorem mean_norm_le_of_row_budget (A : Ω → Matrix V W ℝ)
    (hA : ∀ i j, Measurable (fun ω => A ω i j))
    (hInt : ∀ i j, Integrable (fun ω => A ω i j ^ 2) μ)
    (T : Finset V) (hsupp : ∀ ω i j, i ∉ T → A ω i j = 0)
    (B : ℝ) (hB : 0 ≤ B)
    (hrow : ∀ i, (∑ j, ∫ ω, A ω i j ^ 2 ∂μ) ≤ B ^ 2)
    (d : ℕ) (hd : T.card ≤ d) :
    Integrable (fun ω => ‖A ω‖) μ ∧
      (∫ ω, ‖A ω‖ ∂μ) ≤ Real.sqrt (d : ℝ) * B := by
  apply integrable_and_mean_norm_le A hA hInt _ (mul_nonneg (Real.sqrt_nonneg _) hB)
  have hzero : ∀ i ∈ Finset.univ, i ∉ T → (∑ j, ∫ ω, A ω i j ^ 2 ∂μ) = 0 := by
    intro i _ hi
    apply Finset.sum_eq_zero
    intro j _
    simp only [hsupp _ i j hi, zero_pow two_ne_zero, integral_zero]
  calc
    (∑ i, ∑ j, ∫ ω, A ω i j ^ 2 ∂μ) = ∑ i ∈ T, ∑ j, ∫ ω, A ω i j ^ 2 ∂μ :=
      (Finset.sum_subset (Finset.subset_univ T) hzero).symm
    _ ≤ ∑ _i ∈ T, B ^ 2 := Finset.sum_le_sum fun i _ => hrow i
    _ = (T.card : ℝ) * B ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (d : ℝ) * B ^ 2 :=
      mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hd) (sq_nonneg B)
    _ = (Real.sqrt (d : ℝ) * B) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg d)]

end Probability
end MI32.FrobeniusMean
