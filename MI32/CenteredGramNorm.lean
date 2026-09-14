import MI32.VacuumNormBound
import MI32.LocalLogMoment
import MI32.ThinMatrix

/-!
# Operator mean from the actual centered Gram energy

The Euclidean norm is controlled through `Y.transpose * Y`. A deterministic
diagonal and the sum of squared centered Gram entries suffice. No independence
of Gram entries is used. The probabilistic Gram energy premise is an explicit
intermediate obligation, discharged separately from original entry laws.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open MeasureTheory

namespace MI32.CenteredGramNorm

variable {R C : Type*} [Fintype R] [Fintype C] [DecidableEq R] [DecidableEq C]

def centeredGram (Y : Matrix R C ℝ) (d : C → ℝ) : Matrix C C ℝ :=
  Y.transpose * Y - Matrix.diagonal d

def entryEnergy (G : Matrix C C ℝ) : ℝ := ∑ j, ∑ k, G j k ^ 2

theorem entryEnergy_nonneg (G : Matrix C C ℝ) : 0 ≤ entryEnergy G :=
  Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => sq_nonneg _

theorem norm_sq_le_entryEnergy (G : Matrix C C ℝ) : ‖G‖ ^ 2 ≤ entryEnergy G := by
  have h := VacuumNormBound.opNorm_sq_le_basis_energy
    (Matrix.toEuclideanCLM (n := C) (𝕜 := ℝ) G)
  rw [VacuumNormBound.sum_vacuum_norm_sq_eq_trace] at h
  change ‖G‖ ^ 2 ≤ ∑ j, ∑ k, G k j * G k j at h
  rw [Finset.sum_comm] at h
  simpa only [entryEnergy, pow_two] using h

theorem norm_diagonal_le (d : C → ℝ) (B : ℝ)
    (hd : ∀ j, |d j| ≤ B ^ 2) : ‖Matrix.diagonal d‖ ≤ B ^ 2 := by
  rw [Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg (sq_nonneg B)).mpr fun j => by
    simpa only [Real.norm_eq_abs] using hd j

theorem norm_sq_le_diagonal_add_centeredGram (Y : Matrix R C ℝ)
    (d : C → ℝ) (B : ℝ) (hd : ∀ j, |d j| ≤ B ^ 2) :
    ‖Y‖ ^ 2 ≤ B ^ 2 + ‖centeredGram Y d‖ := by
  have hGram : ‖Y.transpose * Y‖ = ‖Y‖ ^ 2 := by
    have h := Matrix.l2_opNorm_conjTranspose_mul_self Y
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial, ← pow_two] at h
  rw [← hGram]
  calc
    ‖Y.transpose * Y‖ = ‖centeredGram Y d + Matrix.diagonal d‖ := by
      rw [centeredGram, sub_add_cancel]
    _ ≤ ‖centeredGram Y d‖ + ‖Matrix.diagonal d‖ := norm_add_le _ _
    _ ≤ ‖centeredGram Y d‖ + B ^ 2 := add_le_add le_rfl (norm_diagonal_le d B hd)
    _ = _ := add_comm _ _

section Probability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Second-moment control derives both first-moment integrability and its
bound, including zero bounds. -/
theorem mean_le_of_second_moment (f : Ω → ℝ) (hf : Measurable f)
    (hnonneg : ∀ ω, 0 ≤ f ω) (hInt : Integrable (fun ω => f ω ^ 2) μ)
    (K : ℝ) (hK : 0 ≤ K) (hBound : (∫ ω, f ω ^ 2 ∂μ) ≤ K ^ 2) :
    Integrable f μ ∧ (∫ ω, f ω ∂μ) ≤ K := by
  obtain ⟨hi, hm⟩ := LocalLogMoment.integrable_and_mean_le_even_moment
    f hf hnonneg 1 (by omega) (by simpa using hInt)
  refine ⟨hi, hm.trans ?_⟩
  have hr := MomentTools.nat_root_le (∫ ω, f ω ^ 2 ∂μ) 1 K
    (integral_nonneg fun ω => sq_nonneg _) zero_le_one hK 2 (by omega)
    (by simpa using hBound)
  simpa only [Nat.cast_one, Nat.cast_ofNat, mul_one, Real.one_rpow, moment,
    abs_of_nonneg (hnonneg _), Real.rpow_two] using hr

/-- Entrywise centered Gram energy controls its operator mean. -/
theorem gram_mean_le (G : Ω → Matrix C C ℝ)
    (hG : ∀ j k, Measurable (fun ω => G ω j k))
    (hInt : ∀ j k, Integrable (fun ω => G ω j k ^ 2) μ)
    (K : ℝ) (hK : 0 ≤ K)
    (hBound : (∑ j, ∑ k, ∫ ω, G ω j k ^ 2 ∂μ) ≤ K ^ 2) :
    Integrable (fun ω => ‖G ω‖) μ ∧ (∫ ω, ‖G ω‖ ∂μ) ≤ K := by
  have hNorm : Measurable (fun ω => ‖G ω‖) :=
    ThinMatrix.measurable_norm_transposeOperator (fun k j ω => G ω j k) (fun k j => hG j k)
  have hEnergyInt : Integrable (fun ω => entryEnergy (G ω)) μ :=
    integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => hInt j k
  have hNormInt : Integrable (fun ω => ‖G ω‖ ^ 2) μ :=
    hEnergyInt.mono' (hNorm.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact norm_sq_le_entryEnergy (G ω))
  apply mean_le_of_second_moment _ hNorm (fun _ => norm_nonneg _) hNormInt K hK
  calc
    (∫ ω, ‖G ω‖ ^ 2 ∂μ) ≤ ∫ ω, entryEnergy (G ω) ∂μ :=
      integral_mono hNormInt hEnergyInt (fun ω => norm_sq_le_entryEnergy (G ω))
    _ = ∑ j, ∑ k, ∫ ω, G ω j k ^ 2 ∂μ := by
      unfold entryEnergy
      rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ fun k _ => hInt j k)]
      apply Finset.sum_congr rfl
      intro j _
      exact integral_finsetSum _ (fun k _ => hInt j k)
    _ ≤ K ^ 2 := hBound

/-- The original rectangular operator mean follows from the actual centered
Gram energy, with all norm integrability derived. The energy bound itself
must be established from the original independent laws in the application. -/
theorem mean_norm_le (Y : Ω → Matrix R C ℝ)
    (hY : ∀ i j, Measurable (fun ω => Y ω i j))
    (d : C → ℝ) (B : ℝ) (hd : ∀ j, |d j| ≤ B ^ 2)
    (hInt : ∀ j k, Integrable (fun ω => centeredGram (Y ω) d j k ^ 2) μ)
    (K : ℝ) (hK : 0 ≤ K)
    (hBound : (∑ j, ∑ k, ∫ ω, centeredGram (Y ω) d j k ^ 2 ∂μ) ≤ K ^ 2) :
    Integrable (fun ω => ‖Y ω‖) μ ∧
      (∫ ω, ‖Y ω‖ ∂μ) ≤ Real.sqrt (B ^ 2 + K) := by
  have hG : ∀ j k, Measurable (fun ω => centeredGram (Y ω) d j k) := by
    intro j k
    simp only [centeredGram, Matrix.sub_apply, Matrix.mul_apply, Matrix.transpose_apply]
    fun_prop
  obtain ⟨hGramInt, hGramBound⟩ := gram_mean_le (fun ω => centeredGram (Y ω) d)
    hG hInt K hK hBound
  have hNorm : Measurable (fun ω => ‖Y ω‖) :=
    ThinMatrix.measurable_norm_transposeOperator (fun j i ω => Y ω i j) (fun j i => hY i j)
  have hDom := (integrable_const (B ^ 2)).add hGramInt
  have hNormSq : Integrable (fun ω => ‖Y ω‖ ^ 2) μ :=
    hDom.mono' (hNorm.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact norm_sq_le_diagonal_add_centeredGram (Y ω) d B hd)
  apply mean_le_of_second_moment _ hNorm (fun _ => norm_nonneg _) hNormSq
    (Real.sqrt (B ^ 2 + K)) (Real.sqrt_nonneg _)
  rw [Real.sq_sqrt (add_nonneg (sq_nonneg B) hK)]
  calc
    (∫ ω, ‖Y ω‖ ^ 2 ∂μ) ≤ ∫ ω, B ^ 2 + ‖centeredGram (Y ω) d‖ ∂μ :=
      integral_mono hNormSq hDom (fun ω => norm_sq_le_diagonal_add_centeredGram (Y ω) d B hd)
    _ = B ^ 2 + ∫ ω, ‖centeredGram (Y ω) d‖ ∂μ := by
      rw [integral_add (integrable_const _) hGramInt]
      simp
    _ ≤ B ^ 2 + K := add_le_add le_rfl hGramBound

end Probability
end MI32.CenteredGramNorm
