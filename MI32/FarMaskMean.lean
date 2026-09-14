import MI32.DeletionMasks
import MI32.FarRemainderMoment
import MI32.MaskedEntryLaw
import MI32.NestedDeletionFamily
import MI32.DeletionScheduleArithmetic
import MI32.GradedVarianceEnergy
import MI32.VarianceScaleBasics

/-!
# The two far orientations of the deletion decomposition

Both far masks of the shell decomposition are deterministic zero-one masks of
the original entry family, the lower one directly and the upper one after a
transposition. The masked law lemmas transfer measurability, independence,
centering, all positive absolute moments and the unrooted fourth-moment
budget from the original entries; the nested selection supplies the graded
variance cap through its two screens, and the scheduled budgets supply both
the cumulative column counts and the geometric growth. Feeding these into
`FarRemainderMoment.mean_norm_le_of_graded` gives the two mean operator-norm
bounds `varianceScale μ X * √(1 + √2 * α^2)`, with no dimensional factor.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory

namespace MI32.FarMaskMean

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {n : ℕ}

/-- The deterministic mask of the lower far orientation. -/
def farMask (μ : Measure Ω) (X : Ω → Matrix (Fin n) (Fin n) ℝ) (a b : Fin n) : Bool :=
  decide (DeletionMasks.label μ X b + 1 < DeletionMasks.label μ X a)

omit [IsProbabilityMeasure μ] in
/-- Cumulative shell counts are exactly the graded column counts of the
nested family. -/
theorem card_columnsThrough_le (X : Ω → Matrix (Fin n) (Fin n) ℝ) (r : Fin (n + 2)) :
    (GradedVarianceEnergy.columnsThrough (NestedDeletionFamily.level μ X) r).card
      ≤ DeletionScheduleArithmetic.budget r.val := by
  have hset : GradedVarianceEnergy.columnsThrough (NestedDeletionFamily.level μ X) r
      = Finset.univ.filter
        (fun i : Fin n => (NestedDeletionFamily.level μ X i).val ≤ r.val) := by
    simp only [GradedVarianceEnergy.columnsThrough, Fin.le_def]
  rw [hset]
  exact NestedDeletionFamily.card_filter_level_le r.val

/-- The lower far orientation. -/
theorem mean_farLow_le (hn : 1 ≤ n) (X : Ω → Matrix (Fin n) (Fin n) ℝ) (α : ℝ) (hα : 1 ≤ α)
    (hReg : RegularEntries μ α X) :
    Integrable (fun ω => ‖DeletionMasks.farLow μ X ω‖) μ ∧
      (∫ ω, ‖DeletionMasks.farLow μ X ω‖ ∂μ) ≤
        varianceScale μ X * Real.sqrt (1 + Real.sqrt 2 * α ^ 2) := by
  obtain ⟨hX, hind, hzero, hint, hregular⟩ := hReg
  set m : Fin n → Fin n → Bool := farMask μ X with hm
  set Z : Fin n → Fin n → Ω → ℝ := fun a b ω => X ω a b with hZ
  set Y : Fin n → Fin n → Ω → ℝ := MaskedEntryLaw.masked m Z with hY
  have hB : 0 ≤ varianceScale μ X := VarianceScaleBasics.varianceScale_nonneg X hn
  -- the graded variance cap
  have hcap : ∀ (i j k : Fin n), NestedDeletionFamily.level μ X j
        ≤ NestedDeletionFamily.level μ X k →
      (∫ ω, Y i k ω ^ 2 ∂μ) ≠ 0 →
      (∫ ω, Y i j ω ^ 2 ∂μ) ≤ varianceScale μ X ^ 2 /
        ((DeletionScheduleArithmetic.budget
          (NestedDeletionFamily.level μ X k).val : ℝ) ^ 3 + 1) := by
    intro i j k hjk hne
    have htrue : m i k = true := MaskedEntryLaw.mask_of_integral_sq_masked_ne_zero m Z hne
    have hlt : DeletionMasks.label μ X k + 1 < DeletionMasks.label μ X i := by
      simpa only [hm, farMask, decide_eq_true_eq] using htrue
    have hi : i ∉ NestedDeletionFamily.sets μ X (DeletionMasks.label μ X k + 1) := by
      intro hmem
      exact absurd ((DeletionMasks.label_le_iff (μ := μ) (X := X) _ i).mpr hmem) (by omega)
    have hj : j ∈ NestedDeletionFamily.sets μ X (DeletionMasks.label μ X k) :=
      (DeletionMasks.label_le_iff (μ := μ) (X := X) _ j).mp (Fin.le_def.mp hjk)
    have hscreen := NestedDeletionFamily.column_screen (μ := μ) (X := X)
      (DeletionMasks.label μ X k) (DeletionMasks.label μ X k + 1) le_rfl j hj i hi
    exact (MaskedEntryLaw.integral_sq_masked_le m Z i j).trans hscreen
  obtain ⟨hInt, hMean⟩ := FarRemainderMoment.mean_norm_le_of_graded (μ := μ) Y
    (MaskedEntryLaw.measurable_masked m Z hX)
    (MaskedEntryLaw.independent_masked m Z hX hind)
    (MaskedEntryLaw.integral_masked_eq_zero m Z hzero)
    (MaskedEntryLaw.integrable_masked_abs_rpow m Z hint)
    α (varianceScale μ X) hα hB
    (fun i j => MaskedEntryLaw.integral_fourth_masked_le m Z α hregular i j)
    (fun j => (MaskedEntryLaw.sum_col_sq_masked_le m Z j).trans
      (VarianceScaleBasics.col_variance_le_sq (μ := μ) X j))
    (NestedDeletionFamily.level μ X)
    (fun r => DeletionScheduleArithmetic.budget r.val)
    (card_columnsThrough_le X)
    (fun r => DeletionScheduleArithmetic.budget_ge_two_pow r.val)
    hcap
  have hEq : ∀ ω : Ω, (Matrix.of (fun i j => Y i j ω) : Matrix (Fin n) (Fin n) ℝ)
      = DeletionMasks.farLow μ X ω := by
    intro ω
    ext i j
    exact (DeletionMasks.farLow_eq_masked (μ := μ) X ω i j).symm
  simp only [hEq] at hInt hMean
  exact ⟨hInt, hMean⟩

omit [IsProbabilityMeasure μ] in
/-- Independence of the original ordered-pair entry family survives the
transposition of the two index axes. -/
theorem independent_transposed (X : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hind : iIndepFun (fun e : Fin n × Fin n => fun ω => X ω e.1 e.2) μ) :
    iIndepFun (fun e : Fin n × Fin n => fun ω => X ω e.2 e.1) μ := by
  have h := hind.precomp (g := (Prod.swap : Fin n × Fin n → Fin n × Fin n))
    Prod.swap_injective
  exact h

/-- The upper far orientation, through the transposed original family. -/
theorem mean_farUp_le (hn : 1 ≤ n) (X : Ω → Matrix (Fin n) (Fin n) ℝ) (α : ℝ) (hα : 1 ≤ α)
    (hReg : RegularEntries μ α X) :
    Integrable (fun ω => ‖DeletionMasks.farUp μ X ω‖) μ ∧
      (∫ ω, ‖DeletionMasks.farUp μ X ω‖ ∂μ) ≤
        varianceScale μ X * Real.sqrt (1 + Real.sqrt 2 * α ^ 2) := by
  obtain ⟨hX, hind, hzero, hint, hregular⟩ := hReg
  set m : Fin n → Fin n → Bool := farMask μ X with hm
  set Z : Fin n → Fin n → Ω → ℝ := fun a b ω => X ω b a with hZ
  set Y : Fin n → Fin n → Ω → ℝ := MaskedEntryLaw.masked m Z with hY
  have hB : 0 ≤ varianceScale μ X := VarianceScaleBasics.varianceScale_nonneg X hn
  have hXZ : ∀ i j, Measurable (Z i j) := fun i j => hX j i
  have hindZ : iIndepFun (fun e : Fin n × Fin n => Z e.1 e.2) μ :=
    independent_transposed X hind
  have hzeroZ : ∀ i j, (∫ ω, Z i j ω ∂μ) = 0 := fun i j => hzero j i
  have hintZ : ∀ i j (p : ℝ), 0 < p → Integrable (fun ω => |Z i j ω| ^ p) μ :=
    fun i j p hp => hint j i p hp
  have hregZ : ∀ i j (r : ℝ), 1 ≤ r →
      moment μ (2 * r) (Z i j) ≤ α * moment μ r (Z i j) :=
    fun i j r hr => hregular j i r hr
  -- the graded variance cap, now through the row screen
  have hcap : ∀ (i j k : Fin n), NestedDeletionFamily.level μ X j
        ≤ NestedDeletionFamily.level μ X k →
      (∫ ω, Y i k ω ^ 2 ∂μ) ≠ 0 →
      (∫ ω, Y i j ω ^ 2 ∂μ) ≤ varianceScale μ X ^ 2 /
        ((DeletionScheduleArithmetic.budget
          (NestedDeletionFamily.level μ X k).val : ℝ) ^ 3 + 1) := by
    intro i j k hjk hne
    have htrue : m i k = true := MaskedEntryLaw.mask_of_integral_sq_masked_ne_zero m Z hne
    have hlt : DeletionMasks.label μ X k + 1 < DeletionMasks.label μ X i := by
      simpa only [hm, farMask, decide_eq_true_eq] using htrue
    have hi : i ∉ NestedDeletionFamily.sets μ X (DeletionMasks.label μ X k + 1) := by
      intro hmem
      exact absurd ((DeletionMasks.label_le_iff (μ := μ) (X := X) _ i).mpr hmem) (by omega)
    have hj : j ∈ NestedDeletionFamily.sets μ X (DeletionMasks.label μ X k) :=
      (DeletionMasks.label_le_iff (μ := μ) (X := X) _ j).mp (Fin.le_def.mp hjk)
    have hscreen := NestedDeletionFamily.row_screen (μ := μ) (X := X)
      (DeletionMasks.label μ X k) (DeletionMasks.label μ X k + 1) le_rfl j hj i hi
    exact (MaskedEntryLaw.integral_sq_masked_le m Z i j).trans hscreen
  obtain ⟨hInt, hMean⟩ := FarRemainderMoment.mean_norm_le_of_graded (μ := μ) Y
    (MaskedEntryLaw.measurable_masked m Z hXZ)
    (MaskedEntryLaw.independent_masked m Z hXZ hindZ)
    (MaskedEntryLaw.integral_masked_eq_zero m Z hzeroZ)
    (MaskedEntryLaw.integrable_masked_abs_rpow m Z hintZ)
    α (varianceScale μ X) hα hB
    (fun i j => MaskedEntryLaw.integral_fourth_masked_le m Z α hregZ i j)
    (fun j => (MaskedEntryLaw.sum_col_sq_masked_le m Z j).trans
      (VarianceScaleBasics.row_variance_le_sq (μ := μ) X j))
    (NestedDeletionFamily.level μ X)
    (fun r => DeletionScheduleArithmetic.budget r.val)
    (card_columnsThrough_le X)
    (fun r => DeletionScheduleArithmetic.budget_ge_two_pow r.val)
    hcap
  have hEq : ∀ ω : Ω, ‖(Matrix.of (fun i j => Y i j ω) : Matrix (Fin n) (Fin n) ℝ)‖
      = ‖DeletionMasks.farUp μ X ω‖ := by
    intro ω
    have hT : DeletionMasks.farUp μ X ω
        = (Matrix.of (fun i j => Y i j ω) : Matrix (Fin n) (Fin n) ℝ).transpose := by
      ext i j
      exact DeletionMasks.farUp_eq_masked_transpose (μ := μ) X ω i j
    rw [hT, FarRemainderMoment.norm_transpose_eq]
  simp only [hEq] at hInt hMean
  exact ⟨hInt, hMean⟩

end MI32.FarMaskMean
