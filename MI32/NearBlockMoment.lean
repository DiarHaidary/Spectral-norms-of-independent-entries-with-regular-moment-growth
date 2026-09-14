import MI32.RestrictedBlockFamily
import MI32.BilinearHighOrder
import MI32.BlockOrderArithmetic
import MI32.NestedDeletionFamily
import MI32.LocalSymmetricMoment
import MI32.VarianceScaleBasics
import MI32.MomentDoubling

/-!
# One two-shell fiber block at the scheduled moment order

The local symmetric-law moment theorem is applied to a single fiber block of
the *original* matrix, at the moment order scheduled for that block. Three
things have to be supplied.

* The block's index set sits inside the next scheduled deletion set and misses
  the previous one, because every index in the fiber has first-selection level
  `a` or `a + 1`. The first inclusion caps the block dimension by the scheduled
  budget, the second makes the block's bilinear tests literal *deleted*
  bilinear tests of the original matrix.
* Hence the original deletion functional bounds the block's weak input after
  ten scalar doublings, which is exactly the budget the scheduled order can
  afford (`BlockOrderArithmetic.two_blockOrder_le`).
* The bipartite dimension loss of the local theorem is absolute at the
  scheduled order (`BlockOrderArithmetic.dimension_factor_le_exp`), so it is
  absorbed into the constant `Real.exp 1`.

The resulting bound is uniform in the block: it involves only the regularity
parameter, the variance scale and the deletion scale of the original matrix.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory

namespace MI32.NearBlockMoment

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {n : ℕ}
  {K : Type*} [Fintype K] [DecidableEq K]

/-- The scheduled block bound: the local theorem's constant at the block's
weak budget, with the bipartite dimension factor already absorbed. -/
def blockBound (α B D : ℝ) : ℝ :=
  Real.exp 1 * RawMultiplicationContraction.contractionConstant α B
    (SymmetricLinearAllOrders.doublingConstant α ^ 10 * D)

/-- The doubling constant is nonnegative for every parameter. -/
theorem doublingConstant_nonneg (α : ℝ) :
    (0 : ℝ) ≤ SymmetricLinearAllOrders.doublingConstant α := by
  unfold SymmetricLinearAllOrders.doublingConstant
  positivity

/-- The scheduled block bound is nonnegative. -/
theorem blockBound_nonneg (α B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D) : 0 ≤ blockBound α B D := by
  have hW : (0 : ℝ) ≤ SymmetricLinearAllOrders.doublingConstant α ^ 10 * D :=
    mul_nonneg (pow_nonneg (doublingConstant_nonneg α) 10) hD
  have h1 : (0 : ℝ) ≤ B + 6 * α ^ 4 *
      (SymmetricLinearAllOrders.doublingConstant α ^ 10 * D) :=
    add_nonneg hB (mul_nonneg (by positivity) hW)
  unfold blockBound RawMultiplicationContraction.contractionConstant
  refine mul_nonneg (Real.exp_pos 1).le (mul_nonneg (mul_nonneg (by norm_num) ?_) (by positivity))
  exact mul_nonneg (by positivity) h1

omit [Fintype K] in
/-- One two-shell fiber block of the original matrix obeys the local moment
estimate at the scheduled order, with an absolute dimension factor. -/
theorem block_moment_le (hn : 1 ≤ n)
    (X : Ω → Matrix (Fin n) (Fin n) ℝ) (α : ℝ) (hα : 1 ≤ α)
    (hReg : RegularEntries μ α X)
    (hsym : ∀ i j, ProbabilityTheory.IdentDistrib (fun ω => X ω i j) (fun ω => -X ω i j) μ μ)
    (c : Fin n → K) (k : K) (a : ℕ) (ha : 1 ≤ a)
    (hfiber : ∀ i, c i = k →
      (NestedDeletionFamily.level μ X i).val = a ∨
        (NestedDeletionFamily.level μ X i).val = a + 1) :
    Integrable (fun ω => ‖FiberBlockNorm.blockSub (X ω) c k‖ ^
        (2 * BlockOrderArithmetic.blockOrder a)) μ ∧
      moment μ (2 * (BlockOrderArithmetic.blockOrder a : ℝ))
          (fun ω => ‖FiberBlockNorm.blockSub (X ω) c k‖) ≤
        blockBound α (varianceScale μ X) (deletionScale μ X) := by
  obtain ⟨hX, hind, _, hint, hregular⟩ := hReg
  set q := BlockOrderArithmetic.blockOrder a with hqdef
  set Z := RestrictedBlockFamily.blockEntries X c k with hZdef
  have hqpos : 0 < q := BlockOrderArithmetic.one_le_blockOrder a
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hqpos
  -- structural hypotheses of the restricted family
  have hZmeas : ∀ i j, Measurable (Z i j) :=
    RestrictedBlockFamily.measurable_blockEntries (X := X) (c := c) (k := k) hX
  have hZind : iIndepFun
      (fun e : {v : Fin n // c v = k} × {v : Fin n // c v = k} => Z e.1 e.2) μ :=
    RestrictedBlockFamily.independent_blockEntries (X := X) (c := c) (k := k) hind
  have hZsym : ∀ i j, IdentDistrib (Z i j) (fun ω => -Z i j ω) μ μ :=
    RestrictedBlockFamily.symmetric_blockEntries (X := X) (c := c) (k := k) hsym
  have hZint : ∀ i j (p : ℝ), 0 < p → Integrable (fun ω => |Z i j ω| ^ p) μ :=
    RestrictedBlockFamily.integrable_blockEntries (X := X) (c := c) (k := k) hint
  have hZreg : ∀ i j (r : ℝ), 1 ≤ r →
      moment μ (2 * r) (Z i j) ≤ α * moment μ r (Z i j) :=
    RestrictedBlockFamily.regular_blockEntries (X := X) (c := c) (k := k) α hregular
  have hZrow : ∀ i, (∑ j, ∫ ω, Z i j ω ^ 2 ∂μ) ≤ varianceScale μ X ^ 2 :=
    RestrictedBlockFamily.row_budget_blockEntries (X := X) (c := c) (k := k) _
      (fun i => VarianceScaleBasics.row_variance_le_sq (μ := μ) X i)
  have hZcol : ∀ j, (∑ i, ∫ ω, Z i j ω ^ 2 ∂μ) ≤ varianceScale μ X ^ 2 :=
    RestrictedBlockFamily.col_budget_blockEntries (X := X) (c := c) (k := k) _
      (fun j => VarianceScaleBasics.col_variance_le_sq (μ := μ) X j)
  -- (1) the fiber sits inside the next scheduled set and misses the previous one
  have hcard : Fintype.card {v : Fin n // c v = k} ≤
      DeletionScheduleArithmetic.budget (a + 1) := by
    rw [Fintype.card_subtype]
    refine (Finset.card_le_card ?_).trans
      (NestedDeletionFamily.card_filter_level_le (μ := μ) (X := X) (a + 1))
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    rcases hfiber i hi with h | h <;> omega
  have hI : ∀ i, c i = k → i ∉ NestedDeletionFamily.sets μ X (a - 1) := by
    intro i hi hmem
    have hle := (NestedDeletionFamily.level_le_iff (μ := μ) (X := X) (a - 1) i).mpr hmem
    rcases hfiber i hi with h | h <;> omega
  -- (2) the weak input of the block, through ten scalar doublings
  have hweak : ∀ s : EuclideanSpace ℝ {v : Fin n // c v = k}, ‖s‖ ≤ 1 →
      ∀ t : EuclideanSpace ℝ {v : Fin n // c v = k}, ‖t‖ ≤ 1 →
        moment μ (2 * (q : ℝ)) (ThinMatrix.bilinear Z s t) ≤
          SymmetricLinearAllOrders.doublingConstant α ^ 10 * deletionScale μ X := by
    intro s hs t ht
    have hJ : (0 : ℝ) ≤ SymmetricLinearAllOrders.doublingConstant α ^ 10 :=
      pow_nonneg (doublingConstant_nonneg α) 10
    have hdouble := BilinearHighOrder.bilinear_moment_le_pow Z hZmeas hZind hZsym hZint
      α hα hZreg s t 10 (DeletionScheduleArithmetic.order (a - 2)) (2 * (q : ℝ))
      (DeletionScheduleArithmetic.log_two_le_order (a - 2)) (by linarith)
      (BlockOrderArithmetic.two_blockOrder_le a ha)
    have hlocal := RestrictedBlockFamily.moment_bilinear_blockEntries_le_weakMoment
      X hX hint c k (NestedDeletionFamily.sets μ X (a - 1)) hI
      (DeletionScheduleArithmetic.order (a - 2))
      (DeletionScheduleArithmetic.order_pos (a - 2)) s t hs ht
    have hscreen := NestedDeletionFamily.weak_screen (μ := μ) (X := X) hX hint a ha
    calc
      moment μ (2 * (q : ℝ)) (ThinMatrix.bilinear Z s t)
          ≤ SymmetricLinearAllOrders.doublingConstant α ^ 10 *
              moment μ (DeletionScheduleArithmetic.order (a - 2))
                (ThinMatrix.bilinear Z s t) := hdouble
      _ ≤ SymmetricLinearAllOrders.doublingConstant α ^ 10 *
              weakMoment μ X (NestedDeletionFamily.sets μ X (a - 1))
                (DeletionScheduleArithmetic.order (a - 2)) :=
        mul_le_mul_of_nonneg_left hlocal hJ
      _ ≤ SymmetricLinearAllOrders.doublingConstant α ^ 10 * deletionScale μ X :=
        mul_le_mul_of_nonneg_left hscreen hJ
  have hWnn : (0 : ℝ) ≤ SymmetricLinearAllOrders.doublingConstant α ^ 10 * deletionScale μ X :=
    le_trans (MomentTools.nonneg _ _) (hweak 0 (by simp) 0 (by simp))
  -- (3) the local symmetric-law moment theorem on the block
  have hloc := LocalSymmetricMoment.operator_moment_le Z hZmeas hZind hZsym hZint α hα hZreg
    q hqpos (varianceScale μ X) (VarianceScaleBasics.varianceScale_nonneg (μ := μ) X hn)
    hZrow hZcol _ hWnn hweak
  -- (4) identify the block and absorb the dimension factor
  simp only [hZdef, RestrictedBlockFamily.rectangular_blockEntries] at hloc
  obtain ⟨hInt, hBound⟩ := hloc
  refine ⟨hInt, hBound.trans ?_⟩
  have hCnn : (0 : ℝ) ≤ RawMultiplicationContraction.contractionConstant α
      (varianceScale μ X)
      (SymmetricLinearAllOrders.doublingConstant α ^ 10 * deletionScale μ X) := by
    unfold RawMultiplicationContraction.contractionConstant
    have h1 : (0 : ℝ) ≤ varianceScale μ X + 6 * α ^ 4 *
        (SymmetricLinearAllOrders.doublingConstant α ^ 10 * deletionScale μ X) :=
      add_nonneg (VarianceScaleBasics.varianceScale_nonneg (μ := μ) X hn)
        (mul_nonneg (by positivity) hWnn)
    refine mul_nonneg (mul_nonneg (by norm_num) ?_) (by positivity)
    exact mul_nonneg (by positivity) h1
  exact mul_le_mul_of_nonneg_right
    (BlockOrderArithmetic.dimension_factor_le_exp a _ hcard) hCnn

omit [Fintype K] in
/-- The same estimate in the unrooted form consumed by the block-maximum
assembly. -/
theorem block_integral_pow_le (hn : 1 ≤ n)
    (X : Ω → Matrix (Fin n) (Fin n) ℝ) (α : ℝ) (hα : 1 ≤ α)
    (hReg : RegularEntries μ α X)
    (hsym : ∀ i j, ProbabilityTheory.IdentDistrib (fun ω => X ω i j) (fun ω => -X ω i j) μ μ)
    (c : Fin n → K) (k : K) (a : ℕ) (ha : 1 ≤ a)
    (hfiber : ∀ i, c i = k →
      (NestedDeletionFamily.level μ X i).val = a ∨
        (NestedDeletionFamily.level μ X i).val = a + 1) :
    (∫ ω, ‖FiberBlockNorm.blockSub (X ω) c k‖ ^ (2 * BlockOrderArithmetic.blockOrder a) ∂μ)
      ≤ blockBound α (varianceScale μ X) (deletionScale μ X) ^
          (2 * BlockOrderArithmetic.blockOrder a) := by
  obtain ⟨_, hmom⟩ := block_moment_le hn X α hα hReg hsym c k a ha hfiber
  have hqpos : 0 < 2 * BlockOrderArithmetic.blockOrder a := by
    have := BlockOrderArithmetic.one_le_blockOrder a; omega
  have hpow := MI32.moment_nat_pow μ (fun ω => ‖FiberBlockNorm.blockSub (X ω) c k‖)
    (2 * BlockOrderArithmetic.blockOrder a) hqpos
  have hcast : ((2 * BlockOrderArithmetic.blockOrder a : ℕ) : ℝ)
      = 2 * (BlockOrderArithmetic.blockOrder a : ℝ) := by push_cast; ring
  rw [hcast] at hpow
  calc
    (∫ ω, ‖FiberBlockNorm.blockSub (X ω) c k‖ ^ (2 * BlockOrderArithmetic.blockOrder a) ∂μ)
        = ∫ ω, |‖FiberBlockNorm.blockSub (X ω) c k‖| ^
            (2 * BlockOrderArithmetic.blockOrder a) ∂μ := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
      simp only [abs_norm]
    _ = moment μ (2 * (BlockOrderArithmetic.blockOrder a : ℝ))
          (fun ω => ‖FiberBlockNorm.blockSub (X ω) c k‖) ^
          (2 * BlockOrderArithmetic.blockOrder a) := hpow.symm
    _ ≤ blockBound α (varianceScale μ X) (deletionScale μ X) ^
          (2 * BlockOrderArithmetic.blockOrder a) :=
      pow_le_pow_left₀ (MomentTools.nonneg _ _) hmom _

omit [IsProbabilityMeasure μ] [Fintype K] [DecidableEq K] in
/-- A pointwise dominated nonnegative observable inherits an unrooted moment
bound, with its integrability derived. -/
theorem integral_pow_le_of_dominated (F G : Ω → ℝ) (hF : Measurable F)
    (hFnn : ∀ ω, 0 ≤ F ω) (hFG : ∀ ω, F ω ≤ G ω) (q : ℕ)
    (hG : Integrable (fun ω => G ω ^ q) μ) (L : ℝ)
    (hbound : (∫ ω, G ω ^ q ∂μ) ≤ L ^ q) :
    Integrable (fun ω => F ω ^ q) μ ∧ (∫ ω, F ω ^ q ∂μ) ≤ L ^ q := by
  have hpt : ∀ ω, F ω ^ q ≤ G ω ^ q := fun ω => pow_le_pow_left₀ (hFnn ω) (hFG ω) q
  have hIntF : Integrable (fun ω => F ω ^ q) μ :=
    hG.mono' ((hF.pow_const q).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hFnn ω) q)]
        exact hpt ω)
  exact ⟨hIntF, (integral_mono hIntF hG hpt).trans hbound⟩

end MI32.NearBlockMoment
