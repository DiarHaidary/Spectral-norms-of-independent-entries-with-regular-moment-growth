import MI32.DeletionMasks
import MI32.NearBlockMoment
import MI32.BlockMaskMoment
import MI32.FrobeniusMean
import MI32.VarianceScaleBasics
import MI32.WeakMomentBasics

/-!
# The three near-band mean bounds of the deletion decomposition

The near band of the shell decomposition consists of three deterministic
masks. The initial mask `nearLow` lives on the first two shells, whose index
set has absolutely bounded cardinality, so its mean operator norm is
controlled by the Frobenius energy alone: no deletion budget is needed. The
two remaining masks `nearHigh` and `nearCross` are supported on the diagonal
blocks of the even and odd two-shell colourings, and each of their fiber
blocks obeys the scheduled local moment estimate of
`MI32.NearBlockMoment`. The growing-order block maximum of
`MI32.BlockMaskMoment` converts those per-block moments into a mean bound for
the whole mask, with no factor in the number of blocks.

All three bounds carry their own integrability, derived rather than assumed.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory

namespace MI32.NearMaskMean

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {n : ℕ}

/-! ### Entry measurability of the three near masks -/

omit [IsProbabilityMeasure μ] in
/-- Entry measurability of the initial mask follows from the original entries. -/
theorem measurable_nearLow (X : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hX : ∀ i j, Measurable (fun ω => X ω i j)) (i j : Fin n) :
    Measurable (fun ω => DeletionMasks.nearLow μ X ω i j) := by
  by_cases h : DeletionMasks.cEven μ X i = 0 ∧ DeletionMasks.cEven μ X j = 0
  · simp only [DeletionMasks.nearLow, Matrix.of_apply, if_pos h]
    exact hX i j
  · simp only [DeletionMasks.nearLow, Matrix.of_apply, if_neg h]
    exact measurable_const

omit [IsProbabilityMeasure μ] in
/-- Entry measurability of the even two-shell mask follows from the original entries. -/
theorem measurable_nearHigh (X : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hX : ∀ i j, Measurable (fun ω => X ω i j)) (i j : Fin n) :
    Measurable (fun ω => DeletionMasks.nearHigh μ X ω i j) := by
  by_cases h : DeletionMasks.cEven μ X i = DeletionMasks.cEven μ X j ∧
      DeletionMasks.cEven μ X i ≠ 0
  · simp only [DeletionMasks.nearHigh, Matrix.of_apply, if_pos h]
    exact hX i j
  · simp only [DeletionMasks.nearHigh, Matrix.of_apply, if_neg h]
    exact measurable_const

omit [IsProbabilityMeasure μ] in
/-- Entry measurability of the odd two-shell mask follows from the original entries. -/
theorem measurable_nearCross (X : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hX : ∀ i j, Measurable (fun ω => X ω i j)) (i j : Fin n) :
    Measurable (fun ω => DeletionMasks.nearCross μ X ω i j) := by
  by_cases h : (DeletionMasks.label μ X i + 1) / 2 = (DeletionMasks.label μ X j + 1) / 2 ∧
      DeletionMasks.label μ X i ≠ DeletionMasks.label μ X j
  · simp only [DeletionMasks.nearCross, Matrix.of_apply, NestedShells.nearOdd, if_pos h]
    exact hX i j
  · simp only [DeletionMasks.nearCross, Matrix.of_apply, NestedShells.nearOdd, if_neg h]
    exact measurable_const

/-! ### The initial mask only shrinks the entry second moments -/

omit [IsProbabilityMeasure μ] in
/-- Squared entries of the initial mask stay integrable. -/
theorem integrable_sq_nearLow (X : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hsq : ∀ i j, Integrable (fun ω => X ω i j ^ 2) μ) (i j : Fin n) :
    Integrable (fun ω => DeletionMasks.nearLow μ X ω i j ^ 2) μ := by
  by_cases h : DeletionMasks.cEven μ X i = 0 ∧ DeletionMasks.cEven μ X j = 0
  · simp only [DeletionMasks.nearLow, Matrix.of_apply, if_pos h]
    exact hsq i j
  · simp only [DeletionMasks.nearLow, Matrix.of_apply, if_neg h]
    simp

set_option linter.unusedVariables false in
omit [IsProbabilityMeasure μ] in
/-- The initial mask only shrinks the entry second moments. -/
theorem integral_sq_nearLow_le (X : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hsq : ∀ i j, Integrable (fun ω => X ω i j ^ 2) μ) (i j : Fin n) :
    (∫ ω, DeletionMasks.nearLow μ X ω i j ^ 2 ∂μ) ≤ ∫ ω, X ω i j ^ 2 ∂μ := by
  by_cases h : DeletionMasks.cEven μ X i = 0 ∧ DeletionMasks.cEven μ X j = 0
  · simp only [DeletionMasks.nearLow, Matrix.of_apply, if_pos h]
    exact le_rfl
  · simp only [DeletionMasks.nearLow, Matrix.of_apply, if_neg h, zero_pow two_ne_zero,
      integral_zero]
    exact integral_nonneg fun ω => sq_nonneg _

/-! ### The scheduled budget of the initial block -/

/-- The first scheduled deletion budget is thirty-one. -/
theorem budget_one : DeletionScheduleArithmetic.budget 1 = 31 := by
  norm_num [DeletionScheduleArithmetic.budget, DeletionScheduleArithmetic.size]

/-- The initial two shells form a block of absolutely bounded dimension, so
its mean is controlled by the surviving variance budget alone. -/
theorem mean_nearLow_le (hn : 1 ≤ n) (X : Ω → Matrix (Fin n) (Fin n) ℝ) (α : ℝ)
    (hReg : RegularEntries μ α X) :
    Integrable (fun ω => ‖DeletionMasks.nearLow μ X ω‖) μ ∧
      (∫ ω, ‖DeletionMasks.nearLow μ X ω‖ ∂μ) ≤ Real.sqrt 31 * varianceScale μ X := by
  obtain ⟨hX, -, -, hint, -⟩ := hReg
  have hsq : ∀ i j, Integrable (fun ω => X ω i j ^ 2) μ := fun i j => by
    simpa only [Real.rpow_two, sq_abs] using hint i j 2 (by norm_num)
  have hcard : (NestedDeletionFamily.sets μ X 1).card ≤ 31 := by
    have h := NestedDeletionFamily.card_sets_le (μ := μ) (X := X) 1
    rwa [budget_one] at h
  have hmain := FrobeniusMean.mean_norm_le_of_row_budget
    (μ := μ) (fun ω => DeletionMasks.nearLow μ X ω)
    (measurable_nearLow X hX) (integrable_sq_nearLow X hsq)
    (NestedDeletionFamily.sets μ X 1)
    (fun ω i j hi => DeletionMasks.nearLow_support X ω i j hi)
    (varianceScale μ X) (VarianceScaleBasics.varianceScale_nonneg (μ := μ) X hn)
    (fun i => le_trans (Finset.sum_le_sum fun j _ => integral_sq_nearLow_le X hsq i j)
      (VarianceScaleBasics.row_variance_le_sq (μ := μ) X i))
    31 hcard
  refine ⟨hmain.1, hmain.2.trans_eq ?_⟩
  norm_num

/-! ### The common two-shell block-family estimate -/

/-- A deterministic mask supported on the diagonal blocks of a two-shell
colouring, whose initial fiber block vanishes and whose later fiber blocks are
dominated by the corresponding fiber blocks of the original matrix, has its
mean operator norm controlled by the scheduled block bound. The scheduled
order of each block is supplied by `a`, and the growing-order requirement of
the block maximum is the hypothesis `hp`. -/
theorem mean_mask_le (hn : 1 ≤ n) (X : Ω → Matrix (Fin n) (Fin n) ℝ) (α : ℝ) (hα : 1 ≤ α)
    (hReg : RegularEntries μ α X)
    (hsym : ∀ i j, IdentDistrib (fun ω => X ω i j) (fun ω => -X ω i j) μ μ)
    (M : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hM : ∀ i j, Measurable (fun ω => M ω i j))
    (c : Fin n → Fin (n + 2))
    (hsupp : ∀ ω i j, c i ≠ c j → M ω i j = 0)
    (a : Fin (n + 2) → ℕ)
    (hp : ∀ k : Fin (n + 2), k.val + 2 ≤ 2 * BlockOrderArithmetic.blockOrder (a k))
    (hzero : ∀ ω, FiberBlockNorm.blockSub (M ω) c 0 = 0)
    (ha : ∀ k : Fin (n + 2), k ≠ 0 → 1 ≤ a k)
    (hdom : ∀ (ω : Ω) (k : Fin (n + 2)), k ≠ 0 →
      ‖FiberBlockNorm.blockSub (M ω) c k‖ ≤ ‖FiberBlockNorm.blockSub (X ω) c k‖)
    (hfiber : ∀ k : Fin (n + 2), k ≠ 0 → ∀ i, c i = k →
      (NestedDeletionFamily.level μ X i).val = a k ∨
        (NestedDeletionFamily.level μ X i).val = a k + 1) :
    Integrable (fun ω => ‖M ω‖) μ ∧
      (∫ ω, ‖M ω‖ ∂μ) ≤
        3 * NearBlockMoment.blockBound α (varianceScale μ X) (deletionScale μ X) := by
  have hL : 0 ≤ NearBlockMoment.blockBound α (varianceScale μ X) (deletionScale μ X) :=
    NearBlockMoment.blockBound_nonneg _ _ _
      (VarianceScaleBasics.varianceScale_nonneg (μ := μ) X hn)
      (WeakMomentBasics.deletionScale_nonneg μ X)
  have hblock : ∀ k : Fin (n + 2),
      Integrable (fun ω => ‖FiberBlockNorm.blockSub (M ω) c k‖ ^
        (2 * BlockOrderArithmetic.blockOrder (a k))) μ ∧
      (∫ ω, ‖FiberBlockNorm.blockSub (M ω) c k‖ ^
          (2 * BlockOrderArithmetic.blockOrder (a k)) ∂μ) ≤
        NearBlockMoment.blockBound α (varianceScale μ X) (deletionScale μ X) ^
          (2 * BlockOrderArithmetic.blockOrder (a k)) := by
    intro k
    by_cases hk : k = 0
    · subst hk
      have hne : 2 * BlockOrderArithmetic.blockOrder (a 0) ≠ 0 := by
        have := BlockOrderArithmetic.one_le_blockOrder (a 0); omega
      have hz : ∀ ω, ‖FiberBlockNorm.blockSub (M ω) c 0‖ ^
          (2 * BlockOrderArithmetic.blockOrder (a 0)) = 0 := fun ω => by
        rw [hzero ω, norm_zero, zero_pow hne]
      refine ⟨?_, ?_⟩
      · simp only [hz]
        exact integrable_zero _ _ _
      · simp only [hz, integral_zero]
        exact pow_nonneg hL _
    · exact NearBlockMoment.integral_pow_le_of_dominated
        (fun ω => ‖FiberBlockNorm.blockSub (M ω) c k‖)
        (fun ω => ‖FiberBlockNorm.blockSub (X ω) c k‖)
        (BlockMaskMoment.measurable_blockSub_norm M hM c k)
        (fun _ => norm_nonneg _) (fun ω => hdom ω k hk)
        (2 * BlockOrderArithmetic.blockOrder (a k))
        (NearBlockMoment.block_moment_le hn X α hα hReg hsym c k (a k) (ha k hk)
          (hfiber k hk)).1
        (NearBlockMoment.blockBound α (varianceScale μ X) (deletionScale μ X))
        (NearBlockMoment.block_integral_pow_le hn X α hα hReg hsym c k (a k) (ha k hk)
          (hfiber k hk))
  exact BlockMaskMoment.mean_norm_le_of_block_moments M hM c hsupp
    (fun k => 2 * BlockOrderArithmetic.blockOrder (a k)) hp (fun k => (hblock k).1)
    (NearBlockMoment.blockBound α (varianceScale μ X) (deletionScale μ X)) hL
    (fun k => (hblock k).2)

/-! ### The two two-shell block families -/

/-- The even two-shell family, at the orders scheduled by the even blocks. -/
theorem mean_nearHigh_le (hn : 1 ≤ n) (X : Ω → Matrix (Fin n) (Fin n) ℝ) (α : ℝ) (hα : 1 ≤ α)
    (hReg : RegularEntries μ α X)
    (hsym : ∀ i j, IdentDistrib (fun ω => X ω i j) (fun ω => -X ω i j) μ μ) :
    Integrable (fun ω => ‖DeletionMasks.nearHigh μ X ω‖) μ ∧
      (∫ ω, ‖DeletionMasks.nearHigh μ X ω‖ ∂μ) ≤
        3 * NearBlockMoment.blockBound α (varianceScale μ X) (deletionScale μ X) := by
  refine mean_mask_le hn X α hα hReg hsym (fun ω => DeletionMasks.nearHigh μ X ω)
    (measurable_nearHigh X hReg.1) (DeletionMasks.cEven μ X)
    (fun ω i j h => DeletionMasks.nearHigh_fiber_supported X ω i j h)
    (fun k => 2 * k.val) (fun k => ?_) (fun ω => DeletionMasks.blockSub_nearHigh_zero X ω)
    (fun k hk => ?_)
    (fun ω k hk => le_of_eq (congrArg norm (DeletionMasks.blockSub_nearHigh_eq X ω k hk)))
    (fun k _ i hi => ?_)
  · have h := BlockOrderArithmetic.index_add_two_le_two_blockOrder (2 * k.val)
    omega
  · have hkv : k.val ≠ 0 := fun hz => hk (by ext; simpa using hz)
    omega
  · have h := DeletionMasks.cEven_fiber_label X k i hi
    have hlab : DeletionMasks.label μ X i = (NestedDeletionFamily.level μ X i).val := rfl
    omega

/-- The odd two-shell family, through the two-colour off-diagonal contraction. -/
theorem mean_nearCross_le (hn : 1 ≤ n) (X : Ω → Matrix (Fin n) (Fin n) ℝ) (α : ℝ) (hα : 1 ≤ α)
    (hReg : RegularEntries μ α X)
    (hsym : ∀ i j, IdentDistrib (fun ω => X ω i j) (fun ω => -X ω i j) μ μ) :
    Integrable (fun ω => ‖DeletionMasks.nearCross μ X ω‖) μ ∧
      (∫ ω, ‖DeletionMasks.nearCross μ X ω‖ ∂μ) ≤
        3 * NearBlockMoment.blockBound α (varianceScale μ X) (deletionScale μ X) := by
  refine mean_mask_le hn X α hα hReg hsym (fun ω => DeletionMasks.nearCross μ X ω)
    (measurable_nearCross X hReg.1) (DeletionMasks.cOdd μ X)
    (fun ω i j h => DeletionMasks.nearCross_fiber_supported X ω i j h)
    (fun k => 2 * k.val - 1) (fun k => ?_)
    (fun ω => DeletionMasks.blockSub_nearCross_zero X ω) (fun k hk => ?_)
    (fun ω k _ => DeletionMasks.norm_blockSub_nearCross_le X ω k) (fun k hk i hi => ?_)
  · have h := BlockOrderArithmetic.index_add_two_le_two_blockOrder (2 * k.val - 1)
    omega
  · have hkv : k.val ≠ 0 := fun hz => hk (by ext; simpa using hz)
    omega
  · have h := DeletionMasks.cOdd_fiber_label X k hk i hi
    have hkv : k.val ≠ 0 := fun hz => hk (by ext; simpa using hz)
    have hlab : DeletionMasks.label μ X i = (NestedDeletionFamily.level μ X i).val := rfl
    omega

end MI32.NearMaskMean
