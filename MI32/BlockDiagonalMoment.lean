import MI32.BlockDiagonalNorm
import MI32.BlockMomentMaximum
import MI32.ThinMatrix

/-!
# Actual block-diagonal mean from growing block moments

This combines the exact Euclidean block norm bound with the finite growing
moment maximum estimate. Block norms and their powers are intermediate
local-theorem inputs. Measurability, integrability and the final norm bound
of the actual block-diagonal matrix are derived. Blocks need not be independent.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open MeasureTheory

namespace MI32.BlockDiagonalMoment

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {m : ℕ}
    {I : Fin m → Type*} [∀ i, Fintype (I i)] [∀ i, DecidableEq (I i)]

/-- The full block-diagonal norm is measurable directly from the original
block entries, also for empty dependent block axes. -/
theorem measurable_blockDiagonal_norm
    (A : ∀ i, Ω → Matrix (I i) (I i) ℝ)
    (hA : ∀ i j k, Measurable (fun ω => A i ω j k)) :
    Measurable (fun ω => ‖Matrix.blockDiagonal' (fun i => A i ω)‖) := by
  have hentry (u v : Σ i, I i) :
      Measurable (fun ω => Matrix.blockDiagonal' (fun i => A i ω) u v) := by
    rcases u with ⟨i, u⟩
    rcases v with ⟨j, v⟩
    by_cases h : i = j
    · subst j
      simpa only [Matrix.blockDiagonal'_apply_eq] using hA i u v
    · simpa only [Matrix.blockDiagonal'_apply_ne _ _ _ h] using
        (measurable_const : Measurable (fun _ : Ω => (0 : ℝ)))
  exact ThinMatrix.measurable_norm_transposeOperator
    (fun v u ω => Matrix.blockDiagonal' (fun i => A i ω) u v)
    (fun v u => hentry u v)

variable [IsProbabilityMeasure μ]

/-- Actual block-diagonal operator mean bounded by three times a common
rooted block-moment bound. Increasing orders absorb the number of blocks;
there is no independence assumption and no remaining full-operator premise. -/
theorem integrable_and_mean_norm_le
    (A : ∀ i, Ω → Matrix (I i) (I i) ℝ)
    (hA : ∀ i j k, Measurable (fun ω => A i ω j k))
    (hInt : ∀ i, Integrable (fun ω => ‖A i ω‖) μ)
    (p : Fin m → ℕ) (hp : ∀ i, i.val + 2 ≤ p i)
    (hPow : ∀ i, Integrable (fun ω => ‖A i ω‖ ^ p i) μ)
    (L : ℝ) (hL : 0 < L)
    (hBound : ∀ i, (∫ ω, ‖A i ω‖ ^ p i ∂μ) ≤ L ^ p i) :
    Integrable (fun ω => ‖Matrix.blockDiagonal' (fun i => A i ω)‖) μ ∧
      (∫ ω, ‖Matrix.blockDiagonal' (fun i => A i ω)‖ ∂μ) ≤ 3 * L := by
  obtain ⟨hMaxInt, hMaxBound⟩ := BlockMomentMaximum.mean_max_le
    (fun i ω => ‖A i ω‖) hInt (fun _ _ => norm_nonneg _) p hp hPow L hL hBound
  have hDom (ω : Ω) : ‖Matrix.blockDiagonal' (fun i => A i ω)‖ ≤ ‖fun i => ‖A i ω‖‖ :=
    BlockDiagonalNorm.norm_blockDiagonal_le_max (fun i => A i ω)
  have hDiagInt : Integrable (fun ω => ‖Matrix.blockDiagonal' (fun i => A i ω)‖) μ :=
    hMaxInt.mono' (measurable_blockDiagonal_norm A hA).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
        exact hDom ω)
  exact ⟨hDiagInt, (integral_mono hDiagInt hMaxInt hDom).trans hMaxBound⟩

end MI32.BlockDiagonalMoment
