import MI32.HilbertWalsh
import MI32.PositivePolynomial

/-!
# Conditional-sign positive-polynomial fourth moments

This file assembles the actual positive energy polynomial and combines
independent original-coordinate magnitude moments with Hilbert Boolean
hypercontractivity. The magnitude space is an arbitrary probability space.
The signs are averaged over their complete finite uniform law.

The input supplies a finite family of positive raw-monomial polynomials as
Walsh coefficients. Identifying these coefficients with the parity expansion
of a given raw polynomial is a separate algebraic step.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory GraphMatrices

namespace MI32.PositiveCone

open PositivePolynomial

variable {E A κ : Type*} [Fintype E] [DecidableEq E] [Fintype A] [Fintype κ]

/-- Energy terms retain the coordinate, parity, and both original monomial labels. -/
abbrev EnergyTerm (I : Finset (Finset E)) := A × I × κ × κ

def energyCoeff (I : Finset (Finset E)) (c : A → Finset E → κ → ℝ)
    (t : EnergyTerm (A := A) (κ := κ) I) : ℝ :=
  c t.1 t.2.1 t.2.2.1 * c t.1 t.2.1 t.2.2.2

def energyExponent (I : Finset (Finset E)) (ν : A → Finset E → κ → E → ℕ)
    (t : EnergyTerm (A := A) (κ := κ) I) : E → ℕ :=
  ν t.1 t.2.1 t.2.2.1 + ν t.1 t.2.1 t.2.2.2

omit [DecidableEq E] in
/-- The sum of coefficient squares is an explicit positive raw polynomial. -/
theorem evaluate_energy (I : Finset (Finset E)) (c : A → Finset E → κ → ℝ)
    (ν : A → Finset E → κ → E → ℕ) (z : E → ℝ) :
    evaluate (energyCoeff I c) (energyExponent I ν) z =
      ∑ a, ∑ S ∈ I, (evaluate (c a S) (ν a S) z) ^ 2 := by
  simp only [evaluate_sq]
  simp only [evaluate, energyCoeff, energyExponent, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  exact Finset.sum_coe_sort I (fun S : Finset E =>
    ∑ t, ∑ s, c a S t * c a S s * monomial z (ν a S t + ν a S s))

omit [Fintype E] [DecidableEq E] [Fintype A] [Fintype κ] in
theorem energyCoeff_nonneg (I : Finset (Finset E)) (c : A → Finset E → κ → ℝ)
    (hc : ∀ a S, S ∈ I → ∀ t, 0 ≤ c a S t)
    (t : EnergyTerm (A := A) (κ := κ) I) : 0 ≤ energyCoeff I c t :=
  mul_nonneg (hc t.1 t.2.1 t.2.1.property t.2.2.1)
    (hc t.1 t.2.1 t.2.1.property t.2.2.2)

omit [DecidableEq E] [Fintype A] [Fintype κ] in
theorem energyExponent_degree_le (I : Finset (Finset E))
    (ν : A → Finset E → κ → E → ℕ) (d : ℕ)
    (hν : ∀ a S, S ∈ I → ∀ t, degree (ν a S t) ≤ d)
    (t : EnergyTerm (A := A) (κ := κ) I) :
    degree (energyExponent I ν t) ≤ 2 * d := by
  unfold energyExponent
  rw [degree_add]
  have h₁ := hν t.1 t.2.1 t.2.1.property t.2.2.1
  have h₂ := hν t.1 t.2.1 t.2.1.property t.2.2.2
  omega

/-- Conditional sign second moment equals the actual positive energy polynomial. -/
theorem walsh_second_eq_energy (I : Finset (Finset E))
    (c : A → Finset E → κ → ℝ) (ν : A → Finset E → κ → E → ℕ)
    (z : E → ℝ) :
    independentSignLaw.expect
      (fun σ => ∑ a, Walsh.polynomial I (fun S => evaluate (c a S) (ν a S) z) σ ^ 2) =
      evaluate (energyCoeff I c) (energyExponent I ν) z := by
  rw [MI32.finite_expect_sum, evaluate_energy]
  apply Finset.sum_congr rfl
  intro a _
  rw [independentSignLaw_expect_eq_walsh]
  simpa only [pow_two] using Walsh.polynomial_pairing I
    (fun S => evaluate (c a S) (ν a S) z)
    (fun S => evaluate (c a S) (ν a S) z)

section Probability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [DecidableEq E] in
/-- Integrability of the square of every finite raw polynomial, with arbitrary
real coefficients, follows from independent coordinate power moments. -/
theorem integrable_evaluate_sq (Z : E → Ω → ℝ) (hZ : ∀ e, Measurable (Z e))
    (hind : iIndepFun Z μ) (hint : ∀ e r, Integrable (fun ω => Z e ω ^ r) μ)
    {τ : Type*} [Fintype τ] (c : τ → ℝ) (ν : τ → E → ℕ) :
    Integrable (fun ω => evaluate c ν (fun e => Z e ω) ^ 2) μ := by
  simp_rw [evaluate_sq]
  exact integrable_finsetSum _ fun t _ => integrable_finsetSum _ fun s _ =>
    (integrable_monomial Z hZ hind hint (ν t + ν s)).const_mul (c t * c s)

/-- The positive-cone fourth-moment estimate for actual finite Walsh coefficient
polynomials. Every magnitude moment assumption remains one-coordinate; the
energy polynomial estimate and its integrability are proved inside the theorem.
There is no loss in the number of Hilbert coordinates, monomials, or original variables. -/
theorem integrated_walsh_fourth_le (Z : E → Ω → ℝ) (hZ : ∀ e, Measurable (Z e))
    (hind : iIndepFun Z μ) (hint : ∀ e r, Integrable (fun ω => Z e ω ^ r) μ)
    (hnonneg : ∀ e, ∀ᵐ ω ∂μ, 0 ≤ Z e ω)
    (α : ℝ) (hα : 1 ≤ α)
    (hstep : ∀ e u v, (∫ ω, Z e ω ^ (u + v) ∂μ) ≤
      α ^ (2 * (u + v)) * (∫ ω, Z e ω ^ u ∂μ) * (∫ ω, Z e ω ^ v ∂μ))
    (I : Finset (Finset E)) (c : A → Finset E → κ → ℝ)
    (ν : A → Finset E → κ → E → ℕ)
    (hc : ∀ a S, S ∈ I → ∀ t, 0 ≤ c a S t)
    (d : ℕ) (hparity : ∀ S ∈ I, S.card ≤ d)
    (hdegree : ∀ a S, S ∈ I → ∀ t, degree (ν a S t) ≤ d) :
    (∫ ω, independentSignLaw.expect
      (fun σ => (∑ a, Walsh.polynomial I
        (fun S => evaluate (c a S) (ν a S) (fun e => Z e ω)) σ ^ 2) ^ 2) ∂μ) ≤
      (9 : ℝ) ^ d * α ^ (8 * d) *
        (∫ ω, independentSignLaw.expect
          (fun σ => ∑ a, Walsh.polynomial I
            (fun S => evaluate (c a S) (ν a S) (fun e => Z e ω)) σ ^ 2) ∂μ) ^ 2 := by
  let G : Ω → ℝ := fun ω =>
    evaluate (energyCoeff I c) (energyExponent I ν) (fun e => Z e ω)
  let Q : Ω → ℝ := fun ω => independentSignLaw.expect
    (fun σ => (∑ a, Walsh.polynomial I
      (fun S => evaluate (c a S) (ν a S) (fun e => Z e ω)) σ ^ 2) ^ 2)
  have hGint : Integrable (fun ω => G ω ^ 2) μ :=
    integrable_evaluate_sq Z hZ hind hint (energyCoeff I c) (energyExponent I ν)
  have hpoint (ω : Ω) : Q ω ≤ (9 : ℝ) ^ d * G ω ^ 2 := by
    have h := MI32.hilbert_walsh_fourth_le I
      (fun a S => evaluate (c a S) (ν a S) (fun e => Z e ω)) d hparity
    rw [walsh_second_eq_energy] at h
    exact h
  have hQmeas : AEStronglyMeasurable Q μ := by
    apply Measurable.aestronglyMeasurable
    dsimp [Q, FiniteLaw.expect, Walsh.polynomial, evaluate, monomial]
    fun_prop
  have hQnonneg (ω : Ω) : 0 ≤ Q ω :=
    FiniteLaw.expect_nonneg _ (fun _ => sq_nonneg _)
  have hQint : Integrable Q μ :=
    (hGint.const_mul ((9 : ℝ) ^ d)).mono' hQmeas
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hQnonneg ω)]
        exact hpoint ω)
  have hintegrated : (∫ ω, Q ω ∂μ) ≤ (9 : ℝ) ^ d * (∫ ω, G ω ^ 2 ∂μ) := by
    rw [← integral_const_mul]
    exact integral_mono hQint (hGint.const_mul _) hpoint
  have henergy := integral_evaluate_sq_le Z hZ hind hint hnonneg α hα hstep
    (energyCoeff I c) (energyExponent I ν) (energyCoeff_nonneg I c hc)
    (2 * d) (energyExponent_degree_le I ν d hdegree)
  have hpower : 4 * (2 * d) = 8 * d := by omega
  rw [hpower] at henergy
  have hscaled := mul_le_mul_of_nonneg_left henergy (show 0 ≤ (9 : ℝ) ^ d by positivity)
  simp_rw [walsh_second_eq_energy]
  exact hintegrated.trans (by simpa only [G, mul_assoc] using hscaled)

end Probability

end MI32.PositiveCone
