import MI32.PositivePolynomial

/-!
# Tensorization of actual coordinate moment comparisons

An independent symmetric family has nonnegative natural-power moments:
odd moments vanish and even moments are nonnegative. Consequently a
coordinate comparison propagates through a positive homogeneous polynomial.
This file proves the tensorization, including the original-law integrals
and mixed integrability; symmetry will discharge the scalar hypotheses in
the separate even-moment comparison.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace MI32.PositiveMomentComparison
open PositivePolynomial

/-- Exact first moment of a positive or signed polynomial under its original
independent coordinate law. -/
theorem integral_evaluate_eq
    {Ω E K : Type*} [MeasurableSpace Ω] [Fintype E] [Fintype K]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : E → Ω → ℝ) (hX : ∀ e, Measurable (X e))
    (hind : iIndepFun X μ)
    (hint : ∀ e r, Integrable (fun ω => X e ω ^ r) μ)
    (c : K → ℝ) (ν : K → E → ℕ) :
    (∫ ω, evaluate c ν (fun e => X e ω) ∂μ) =
      ∑ k, c k * tensorMoment (fun e r => ∫ ω, X e ω ^ r ∂μ) (ν k) := by
  classical
  unfold evaluate
  rw [integral_finsetSum _ (fun k _ =>
    (integrable_monomial X hX hind hint (ν k)).const_mul (c k))]
  apply Finset.sum_congr rfl
  intro k hk
  rw [integral_const_mul, integral_monomial X hX hind]

/-- A coordinate moment comparison costs only `C^p` on a homogeneous
positive polynomial of degree `p`, with no factor for the number of
coordinates or monomials. Both sides are expectations of the actual laws. -/
theorem integral_evaluate_le_of_moments
    {Ω Ω' E K : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [Fintype E] [Fintype K]
    {μ : Measure Ω} {μ' : Measure Ω'} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure μ']
    (X : E → Ω → ℝ) (Y : E → Ω' → ℝ)
    (hX : ∀ e, Measurable (X e)) (hY : ∀ e, Measurable (Y e))
    (hindX : iIndepFun X μ) (hindY : iIndepFun Y μ')
    (hintX : ∀ e r, Integrable (fun ω => X e ω ^ r) μ)
    (hintY : ∀ e r, Integrable (fun ω => Y e ω ^ r) μ')
    (hnonneg : ∀ e r, 0 ≤ ∫ ω, X e ω ^ r ∂μ)
    (C : ℝ)
    (hcomp : ∀ e r, (∫ ω, X e ω ^ r ∂μ) ≤
      C ^ r * ∫ ω, Y e ω ^ r ∂μ')
    (c : K → ℝ) (ν : K → E → ℕ) (hc : ∀ k, 0 ≤ c k)
    (p : ℕ) (hdegree : ∀ k, degree (ν k) = p) :
    (∫ ω, evaluate c ν (fun e => X e ω) ∂μ) ≤
      C ^ p * ∫ ω, evaluate c ν (fun e => Y e ω) ∂μ' := by
  classical
  rw [integral_evaluate_eq X hX hindX hintX,
    integral_evaluate_eq Y hY hindY hintY, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  have hmono :
      tensorMoment (fun e r => ∫ ω, X e ω ^ r ∂μ) (ν k) ≤
        C ^ p * tensorMoment (fun e r => ∫ ω, Y e ω ^ r ∂μ') (ν k) := by
    calc
      _ ≤ ∏ e, C ^ ν k e * ∫ ω, Y e ω ^ ν k e ∂μ' :=
        Finset.prod_le_prod (fun e _ => hnonneg e _) (fun e _ => hcomp e _)
      _ = C ^ p * tensorMoment (fun e r => ∫ ω, Y e ω ^ r ∂μ') (ν k) := by
        rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
        rw [show (∑ e, ν k e) = p from hdegree k]
        rfl
  calc
    _ ≤ c k * (C ^ p * tensorMoment (fun e r => ∫ ω, Y e ω ^ r ∂μ') (ν k)) :=
      mul_le_mul_of_nonneg_left hmono (hc k)
    _ = _ := by ring

end MI32.PositiveMomentComparison
