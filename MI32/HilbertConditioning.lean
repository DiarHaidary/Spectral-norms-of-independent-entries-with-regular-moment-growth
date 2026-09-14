import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
# Conditioning an inner product on an independent copy

A bound on deterministic Euclidean unit-vector tests is extended by actual
homogeneity to arbitrary vectors. Fubini then conditions on the second
independent copy. The original weak moment stays outside the random test
vector, and the zero-vector case is handled explicitly.
-/

noncomputable section
open scoped InnerProductSpace
open MeasureTheory

namespace MI32.HilbertConditioning

/-- Extend a unit-vector moment bound homogeneously, without requiring
a random choice of a unit vector in the definition of the weak moment. -/
theorem integral_inner_pow_le_of_unit
    {Ω J : Type*} [MeasurableSpace Ω] [Fintype J]
    {μ : Measure Ω} (V : Ω → EuclideanSpace ℝ J) (p : ℕ) (hp : p ≠ 0)
    (B : ℝ)
    (hunit : ∀ t : EuclideanSpace ℝ J, ‖t‖ ≤ 1 →
      (∫ ω, |⟪t, V ω⟫_ℝ| ^ p ∂μ) ≤ B)
    (t : EuclideanSpace ℝ J) :
    (∫ ω, |⟪t, V ω⟫_ℝ| ^ p ∂μ) ≤ B * ‖t‖ ^ p := by
  by_cases ht : t = 0
  · simp [ht, hp]
  have ht0 : 0 < ‖t‖ := norm_pos_iff.mpr ht
  have hnorm : ‖‖t‖⁻¹ • t‖ = 1 := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr ht0.le)]
    exact inv_mul_cancel₀ ht0.ne'
  have heq (ω : Ω) :
      |⟪t, V ω⟫_ℝ| ^ p =
        ‖t‖ ^ p * |⟪‖t‖⁻¹ • t, V ω⟫_ℝ| ^ p := by
    rw [real_inner_smul_left, abs_mul, abs_of_nonneg (inv_nonneg.mpr ht0.le)]
    rw [mul_pow, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ ht0.ne', one_pow, one_mul]
  simp_rw [heq]
  rw [integral_const_mul, mul_comm B]
  exact mul_le_mul_of_nonneg_left (hunit _ hnorm.le) (pow_nonneg (norm_nonneg _) _)

/-- The decoupled inner product has moment at most the original weak
moment budget times the same-order moment of the random Euclidean norm.
The product moment's integrability is proved by Cauchy--Schwarz. -/
theorem integral_copy_inner_pow_le
    {Ω J : Type*} [MeasurableSpace Ω] [Fintype J]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (V : Ω → EuclideanSpace ℝ J) (hV : Measurable V)
    (p : ℕ) (hp : p ≠ 0)
    (hint : Integrable (fun ω => ‖V ω‖ ^ p) μ)
    (B : ℝ)
    (hunit : ∀ t : EuclideanSpace ℝ J, ‖t‖ ≤ 1 →
      (∫ ω, |⟪t, V ω⟫_ℝ| ^ p ∂μ) ≤ B) :
    Integrable (fun z : Ω × Ω => |⟪V z.1, V z.2⟫_ℝ| ^ p) (μ.prod μ) ∧
      (∫ z : Ω × Ω, |⟪V z.1, V z.2⟫_ℝ| ^ p ∂(μ.prod μ)) ≤
        B * ∫ ω, ‖V ω‖ ^ p ∂μ := by
  have hprod : Integrable
      (fun z : Ω × Ω => |⟪V z.1, V z.2⟫_ℝ| ^ p) (μ.prod μ) := by
    refine (hint.mul_prod hint).mono' (by fun_prop) ?_
    apply Filter.Eventually.of_forall
    intro z
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg _) _), ← mul_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (abs_real_inner_le_norm _ _) _
  refine ⟨hprod, ?_⟩
  calc
    (∫ z : Ω × Ω, |⟪V z.1, V z.2⟫_ℝ| ^ p ∂(μ.prod μ)) =
        ∫ η, ∫ ω, |⟪V ω, V η⟫_ℝ| ^ p ∂μ ∂μ := integral_prod_symm _ hprod
    _ ≤ ∫ η, B * ‖V η‖ ^ p ∂μ := by
      apply integral_mono hprod.integral_prod_right (hint.const_mul B)
      intro η
      simpa only [real_inner_comm] using
        integral_inner_pow_le_of_unit V p hp B hunit (V η)
    _ = B * ∫ ω, ‖V ω‖ ^ p ∂μ := integral_const_mul _ _

end MI32.HilbertConditioning
