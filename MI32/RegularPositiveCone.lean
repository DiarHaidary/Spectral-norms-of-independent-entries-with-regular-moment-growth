import MI32.MomentDoubling
import MI32.PositiveCone

/-!
# Positive-cone fourth moments from the original regularity hypothesis

The public theorem assumes the source's rooted moment-doubling condition on
the original magnitude variables. Natural-power integrability, unrooted
doubling, and the pair-moment inequality used by the positive energy argument
are all derived. No polynomial moment bound is a hypothesis.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory GraphMatrices

namespace MI32

/-- The conditional-sign positive-cone estimate under actual rooted moment
regularity. The magnitude probability space is arbitrary. The signs use their
complete independent uniform law. Walsh coefficient polynomials retain full
original exponents and may depend on all original magnitudes.

The input explicitly supplies the Walsh coefficient family; its identification
with the parity expansion of a given raw polynomial is a separate algebraic lemma. -/
theorem positive_cone_fourth_moment_of_regular
    {Ω E A κ : Type*} [MeasurableSpace Ω]
    [Fintype E] [DecidableEq E] [Fintype A] [Fintype κ]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (Z : E → Ω → ℝ) (hZ : ∀ e, Measurable (Z e))
    (hind : iIndepFun Z μ) (hnonneg : ∀ e ω, 0 ≤ Z e ω)
    (hint : ∀ e (p : ℝ), 0 < p → Integrable (fun ω => |Z e ω| ^ p) μ)
    (α : ℝ) (hα : 1 ≤ α)
    (hregular : ∀ e (r : ℝ), 1 ≤ r →
      moment μ (2 * r) (Z e) ≤ α * moment μ r (Z e))
    (I : Finset (Finset E)) (c : A → Finset E → κ → ℝ)
    (ν : A → Finset E → κ → E → ℕ)
    (hc : ∀ a S, S ∈ I → ∀ t, 0 ≤ c a S t)
    (d : ℕ) (hparity : ∀ S ∈ I, S.card ≤ d)
    (hdegree : ∀ a S, S ∈ I → ∀ t, PositivePolynomial.degree (ν a S t) ≤ d) :
    (∫ ω, independentSignLaw.expect
      (fun σ => (∑ a, Walsh.polynomial I
        (fun S => PositivePolynomial.evaluate (c a S) (ν a S)
          (fun e => Z e ω)) σ ^ 2) ^ 2) ∂μ) ≤
      (9 : ℝ) ^ d * α ^ (8 * d) *
        (∫ ω, independentSignLaw.expect
          (fun σ => ∑ a, Walsh.polynomial I
            (fun S => PositivePolynomial.evaluate (c a S) (ν a S)
              (fun e => Z e ω)) σ ^ 2) ∂μ) ^ 2 := by
  have hnat (e : E) (r : ℕ) : Integrable (fun ω => Z e ω ^ r) μ := by
    by_cases hr : r = 0
    · simp only [hr, pow_zero]
      exact integrable_const 1
    · have hp : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hr)
      simpa only [Real.rpow_natCast, abs_of_nonneg (hnonneg e _)] using hint e r hp
  have hnonneg_ae (e : E) : ∀ᵐ ω ∂μ, 0 ≤ Z e ω :=
    Filter.Eventually.of_forall (hnonneg e)
  have hdouble (e : E) (r : ℕ) (hr : 1 ≤ r) :
      (∫ ω, Z e ω ^ (2 * r) ∂μ) ≤
        α ^ (2 * r) * (∫ ω, Z e ω ^ r ∂μ) ^ 2 := by
    simpa only [abs_of_nonneg (hnonneg e _)] using
      integral_pow_doubling μ (Z e) α (hregular e) r hr
  have hstep (e : E) (u v : ℕ) :
      (∫ ω, Z e ω ^ (u + v) ∂μ) ≤
        α ^ (2 * (u + v)) * (∫ ω, Z e ω ^ u ∂μ) * (∫ ω, Z e ω ^ v ∂μ) := by
    refine (PositivePolynomial.moment_add_le_of_doubling (Z e) (hnat e)
      (hnonneg_ae e) α hα (hdouble e) u v).trans ?_
    apply mul_le_mul_of_nonneg_right _
      (integral_nonneg fun ω => pow_nonneg (hnonneg e ω) v)
    apply mul_le_mul_of_nonneg_right _
      (integral_nonneg fun ω => pow_nonneg (hnonneg e ω) u)
    exact pow_le_pow_right₀ hα (by omega)
  exact PositiveCone.integrated_walsh_fourth_le Z hZ hind hnat hnonneg_ae
    α hα hstep I c ν hc d hparity hdegree

end MI32
