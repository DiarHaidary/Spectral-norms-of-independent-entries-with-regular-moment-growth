import MI32.RawParity
import MI32.RegularPositiveCone

/-!
# Fourth moments of actual raw positive polynomials

This is the positive-polynomial analytic lemma used by the informal MI-32
argument, for the explicit independent-sign/nonnegative-magnitude model.
No Walsh expansion, energy inequality, mixed moment factorization, or
polynomial hypercontractivity is assumed: all are proved in the imported core.

The remaining transfer from arbitrary symmetric entry laws to this exact
sign/magnitude model is a measure-theoretic proof obligation of the full MI-32
development. This theorem itself concerns literal evaluations at `ε_e Z_e`.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory GraphMatrices

namespace MI32

/-- Dimension-free fourth-moment bound for a finite-dimensional real vector
of positive original-variable polynomials of degree at most d. The magnitude
space is arbitrary; signs are averaged over their actual independent uniform
law. Raw powers and shared original variable identities are retained. -/
theorem raw_positive_polynomial_fourth_moment
    {Ω E A κ : Type*} [MeasurableSpace Ω]
    [Fintype E] [DecidableEq E] [Fintype A] [Fintype κ]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (Z : E → Ω → ℝ) (hZ : ∀ e, Measurable (Z e))
    (hind : iIndepFun Z μ) (hnonneg : ∀ e ω, 0 ≤ Z e ω)
    (hint : ∀ e (p : ℝ), 0 < p → Integrable (fun ω => |Z e ω| ^ p) μ)
    (α : ℝ) (hα : 1 ≤ α)
    (hregular : ∀ e (r : ℝ), 1 ≤ r →
      moment μ (2 * r) (Z e) ≤ α * moment μ r (Z e))
    (c : A → κ → ℝ) (ν : A → κ → E → ℕ)
    (hc : ∀ a t, 0 ≤ c a t)
    (d : ℕ) (hdegree : ∀ a t, PositivePolynomial.degree (ν a t) ≤ d) :
    (∫ ω, independentSignLaw.expect
      (fun σ => (∑ a, PositivePolynomial.evaluate (c a) (ν a)
        (fun e => Walsh.sign (σ e) * Z e ω) ^ 2) ^ 2) ∂μ) ≤
      (9 : ℝ) ^ d * α ^ (8 * d) *
        (∫ ω, independentSignLaw.expect
          (fun σ => ∑ a, PositivePolynomial.evaluate (c a) (ν a)
            (fun e => Walsh.sign (σ e) * Z e ω) ^ 2) ∂μ) ^ 2 := by
  have h := positive_cone_fourth_moment_of_regular Z hZ hind hnonneg hint α hα hregular
    (RawParity.cutoff d)
    (fun a S => RawParity.sectionCoeff (c a) (ν a) S)
    (fun a _ => ν a)
    (fun a S _ t => RawParity.sectionCoeff_nonneg (c a) (ν a) (hc a) S t)
    d (fun S hS => (RawParity.mem_cutoff d S).mp hS)
    (fun a _ _ t => hdegree a t)
  have hexpand (a : A) (ω : Ω) (σ : E → Bool) :
      Walsh.polynomial (RawParity.cutoff d)
        (fun S => PositivePolynomial.evaluate (RawParity.sectionCoeff (c a) (ν a) S)
          (ν a) (fun e => Z e ω)) σ =
      PositivePolynomial.evaluate (c a) (ν a)
        (fun e => Walsh.sign (σ e) * Z e ω) :=
    (RawParity.evaluate_sign_eq_cutoff (c a) (ν a) d (hdegree a) σ (fun e => Z e ω)).symm
  simpa only [hexpand] using h

end MI32
