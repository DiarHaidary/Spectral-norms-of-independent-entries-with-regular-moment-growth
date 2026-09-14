import MI32.SymmetricPositiveCone
import MI32.ConeInterpolation
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-!
# Original-law interpolation for the positive polynomial cone

This is the direct interface for a count-sector polynomial after inverse
Walsh transformation. Every norm is the norm of the actual random
polynomial. There is no identification of coefficient-space and polynomial
`L_r` norms outside `L_2`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory

namespace MI32.SymmetricConeInterpolation
open PositivePolynomial SymmetricPositiveCone

def coneConstant (α : ℝ) : ℝ := Real.sqrt 3 * α ^ 2

theorem one_le_coneConstant (α : ℝ) (hα : 1 ≤ α) : 1 ≤ coneConstant α := by
  have hs : 1 ≤ Real.sqrt (3 : ℝ) := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg (3 : ℝ)]
  have ha : 1 ≤ α ^ 2 := by nlinarith
  exact one_le_mul_of_one_le_of_one_le hs ha

theorem coneConstant_pow (α : ℝ) (d : ℕ) :
    coneConstant α ^ (4 * d) = (9 : ℝ) ^ d * α ^ (8 * d) := by
  have hs : (Real.sqrt (3 : ℝ)) ^ 4 = 9 := by
    calc
      _ = ((Real.sqrt (3 : ℝ)) ^ 2) ^ 2 := by ring
      _ = 9 := by rw [Real.sq_sqrt (by norm_num)]; norm_num
  unfold coneConstant
  rw [mul_pow, pow_mul, hs]
  congr 1
  rw [← pow_mul]
  congr 1
  omega

variable {Ω E A κ : Type*} [MeasurableSpace Ω] [Fintype E] [DecidableEq E]
  [Fintype A] [Fintype κ] {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [DecidableEq E] [IsProbabilityMeasure μ] in
@[fun_prop] theorem measurable_polynomial_norm
    (W : E → Ω → ℝ) (hW : ∀ e, Measurable (W e))
    (c : A → κ → ℝ) (ν : A → κ → E → ℕ) :
    Measurable (fun ω => ‖evaluateHilbert c ν (fun e => W e ω)‖) := by
  unfold evaluateHilbert evaluate monomial
  fun_prop

/-- All hypotheses concern the original scalar law and the raw coefficients.
The interpolation factor is independent of the number of coordinates/terms. -/
theorem moment_holder_order_le
    (W : E → Ω → ℝ) (hW : ∀ e, Measurable (W e)) (hind : iIndepFun W μ)
    (hsym : ∀ e, IdentDistrib (W e) (fun ω => -W e ω) μ μ)
    (hint : ∀ e (p : ℝ), 0 < p → Integrable (fun ω => |W e ω| ^ p) μ)
    (α : ℝ) (hα : 1 ≤ α)
    (hregular : ∀ e (r : ℝ), 1 ≤ r →
      moment μ (2 * r) (W e) ≤ α * moment μ r (W e))
    (c : A → κ → ℝ) (ν : A → κ → E → ℕ) (hc : ∀ a t, 0 ≤ c a t)
    (d : ℕ) (hdegree : ∀ a t, degree (ν a t) ≤ d)
    (p : ℝ) (hp : 4 ≤ p) :
    moment μ (2 * p / (p - 2)) (fun ω => ‖evaluateHilbert c ν (fun e => W e ω)‖) ≤
      coneConstant α ^ (4 * (d : ℝ) / p) *
        moment μ 2 (fun ω => ‖evaluateHilbert c ν (fun e => W e ω)‖) := by
  have h4 : Integrable (fun ω => ‖evaluateHilbert c ν (fun e => W e ω)‖ ^ 4) μ := by
    simpa only [evaluateHilbert_norm_fourth] using integrable_normSq_sq W hW hind hint c ν
  have hb := fourth_norm_moment W hW hind hsym hint α hα hregular c ν hc d hdegree
  rw [← coneConstant_pow] at hb
  exact ConeInterpolation.moment_holder_order_le _ (measurable_polynomial_norm W hW c ν)
    (fun _ => norm_nonneg _) h4 (coneConstant α) (one_le_coneConstant α hα) d hb p hp

/-- Reachable degree below q gives the uniform factor `sqrt(3) alpha^2`
at the Holder partner of p=4q. -/
theorem moment_four_q_le
    (W : E → Ω → ℝ) (hW : ∀ e, Measurable (W e)) (hind : iIndepFun W μ)
    (hsym : ∀ e, IdentDistrib (W e) (fun ω => -W e ω) μ μ)
    (hint : ∀ e (p : ℝ), 0 < p → Integrable (fun ω => |W e ω| ^ p) μ)
    (α : ℝ) (hα : 1 ≤ α)
    (hregular : ∀ e (r : ℝ), 1 ≤ r →
      moment μ (2 * r) (W e) ≤ α * moment μ r (W e))
    (c : A → κ → ℝ) (ν : A → κ → E → ℕ) (hc : ∀ a t, 0 ≤ c a t)
    (d q : ℕ) (hdegree : ∀ a t, degree (ν a t) ≤ d) (hdq : d < q) :
    moment μ (2 * (4 * (q : ℝ)) / (4 * (q : ℝ) - 2))
      (fun ω => ‖evaluateHilbert c ν (fun e => W e ω)‖) ≤
      coneConstant α * moment μ 2 (fun ω => ‖evaluateHilbert c ν (fun e => W e ω)‖) := by
  have h4 : Integrable (fun ω => ‖evaluateHilbert c ν (fun e => W e ω)‖ ^ 4) μ := by
    simpa only [evaluateHilbert_norm_fourth] using integrable_normSq_sq W hW hind hint c ν
  have hb := fourth_norm_moment W hW hind hsym hint α hα hregular c ν hc d hdegree
  rw [← coneConstant_pow] at hb
  exact ConeInterpolation.moment_four_q_le _ (measurable_polynomial_norm W hW c ν)
    (fun _ => norm_nonneg _) h4 (coneConstant α) (one_le_coneConstant α hα)
    d q (by omega) hdq hb

end MI32.SymmetricConeInterpolation
