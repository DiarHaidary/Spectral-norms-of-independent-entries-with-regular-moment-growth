import MI32.MomentDoubling
import MI32.PositivePolynomial

noncomputable section
open MeasureTheory ProbabilityTheory

namespace MI32

/-- Equation (8) under the actual rooted moment-doubling assumption, on an
arbitrary probability space. There is no assumed mixed-moment or polynomial
inequality in this statement. Original nonnegative variables can be magnitudes. -/
theorem positive_polynomial_second_moment_of_regular
    {Ω ι κ : Type*} [MeasurableSpace Ω] [Fintype ι] [Fintype κ]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (Z : ι → Ω → ℝ) (hZ : ∀ i, Measurable (Z i))
    (hind : iIndepFun Z μ) (hnonneg : ∀ i ω, 0 ≤ Z i ω)
    (hint : ∀ i (p : ℝ), 0 < p → Integrable (fun ω => |Z i ω| ^ p) μ)
    (α : ℝ) (hα : 1 ≤ α)
    (hregular : ∀ i (r : ℝ), 1 ≤ r →
      moment μ (2 * r) (Z i) ≤ α * moment μ r (Z i))
    (c : κ → ℝ) (ν : κ → ι → ℕ) (hc : ∀ t, 0 ≤ c t)
    (D : ℕ) (hdegree : ∀ t, PositivePolynomial.degree (ν t) ≤ D) :
    (∫ ω, PositivePolynomial.evaluate c ν (fun i => Z i ω) ^ 2 ∂μ) ≤
      α ^ (4 * D) *
        (∫ ω, PositivePolynomial.evaluate c ν (fun i => Z i ω) ∂μ) ^ 2 := by
  have hnat (i : ι) (r : ℕ) : Integrable (fun ω => Z i ω ^ r) μ := by
    by_cases hr : r = 0
    · simp only [hr, pow_zero]
      exact integrable_const 1
    · have hp : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hr)
      simpa only [Real.rpow_natCast, abs_of_nonneg (hnonneg i _)] using hint i r hp
  apply PositivePolynomial.integral_evaluate_sq_le_of_doubling
    Z hZ hind hnat (fun i => Filter.Eventually.of_forall (hnonneg i)) α hα _ c ν hc D hdegree
  intro i r hr
  simpa only [abs_of_nonneg (hnonneg i _)] using
    integral_pow_doubling μ (Z i) α (hregular i) r hr

end MI32
