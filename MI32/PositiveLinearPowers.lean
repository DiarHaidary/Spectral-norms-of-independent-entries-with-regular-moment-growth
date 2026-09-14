import MI32.RawPositiveCone
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Positive word expansion of powers of linear forms

Each term is an actual word `Fin q → E`; no original variable is copied.
Coefficients retain the product of the original scalar coefficients, while
exponents count the occurrences of every original coordinate in that word.
The raw positive-polynomial theorem then yields even-order scalar moment
doubling in the exact independent-sign/original-magnitude model.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory GraphMatrices

namespace MI32.PositiveLinearPowers

variable {E : Type*} [Fintype E] [DecidableEq E]

def wordCoeff (a : E → ℝ) {q : ℕ} (w : Fin q → E) : ℝ :=
  ∏ r, a (w r)

/-- Raw occurrence counts, without reduction modulo two. -/
def wordExponent {q : ℕ} (w : Fin q → E) (e : E) : ℕ :=
  ∑ r, if w r = e then 1 else 0

omit [Fintype E] [DecidableEq E] in
theorem wordCoeff_nonneg (a : E → ℝ) (ha : ∀ e, 0 ≤ a e)
    {q : ℕ} (w : Fin q → E) : 0 ≤ wordCoeff a w :=
  Finset.prod_nonneg fun r _ => ha (w r)

theorem wordExponent_degree {q : ℕ} (w : Fin q → E) :
    PositivePolynomial.degree (wordExponent w) = q := by
  unfold PositivePolynomial.degree wordExponent
  rw [Finset.sum_comm]
  simp

theorem monomial_wordExponent (y : E → ℝ) {q : ℕ} (w : Fin q → E) :
    PositivePolynomial.monomial y (wordExponent w) = ∏ r, y (w r) := by
  unfold PositivePolynomial.monomial wordExponent
  simp_rw [← Finset.prod_pow_eq_pow_sum]
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro r _
  simp

/-- Full finite word expansion of the actual power of a linear form. -/
theorem evaluate_words (a y : E → ℝ) (q : ℕ) :
    PositivePolynomial.evaluate (wordCoeff a : (Fin q → E) → ℝ)
      wordExponent y = (∑ e, a e * y e) ^ q := by
  rw [Fintype.sum_pow]
  unfold PositivePolynomial.evaluate
  apply Finset.sum_congr rfl
  intro w _
  rw [monomial_wordExponent, wordCoeff, Finset.prod_mul_distrib]

/-- The literal signed linear form, with one sign per original coordinate. -/
def signedLinearForm {Ω : Type*} (a : E → ℝ) (Z : E → Ω → ℝ)
    (ω : Ω) (σ : E → Bool) : ℝ :=
  ∑ e, a e * (Walsh.sign (σ e) * Z e ω)

def negativeMask (a : E → ℝ) : E → Bool := fun e => decide (a e < 0)

omit [DecidableEq E] in
/-- Absolute scalar coefficients are absorbed by a deterministic flip of
the existing original signs, without introducing fresh variables. -/
theorem signedLinearForm_abs_flip {Ω : Type*} (a : E → ℝ) (Z : E → Ω → ℝ)
    (ω : Ω) (σ : E → Bool) :
    signedLinearForm (fun e => |a e|) Z ω
      (MatrixAverageContraction.xorFlip (negativeMask a) σ) =
      signedLinearForm a Z ω σ := by
  unfold signedLinearForm
  apply Finset.sum_congr rfl
  intro e _
  by_cases he : a e < 0
  · cases hσ : σ e <;>
      simp [MatrixAverageContraction.xorFlip, negativeMask, he,
        abs_of_neg he, Walsh.sign, hσ]
  · cases hσ : σ e <;>
      simp [MatrixAverageContraction.xorFlip, negativeMask, he,
        abs_of_nonneg (le_of_not_gt he), Walsh.sign, hσ]

/-- Every observable of the signed linear sum has exactly the same finite
sign expectation after taking absolute values of its deterministic coefficients. -/
theorem expect_signedLinearForm_abs {Ω : Type*} (a : E → ℝ) (Z : E → Ω → ℝ)
    (ω : Ω) (Φ : ℝ → ℝ) :
    independentSignLaw.expect (fun σ => Φ (signedLinearForm (fun e => |a e|) Z ω σ)) =
      independentSignLaw.expect (fun σ => Φ (signedLinearForm a Z ω σ)) := by
  have h := MatrixAverageContraction.independent_expect_xorFlip (negativeMask a)
    (fun σ => Φ (signedLinearForm (fun e => |a e|) Z ω σ))
  simpa only [signedLinearForm_abs_flip] using h.symm

/-- Elementary rooted form of a uniform even-power estimate. -/
theorem even_root_le (I J C : ℝ) (hI : 0 ≤ I) (hJ : 0 ≤ J) (hC : 0 ≤ C)
    (q : ℕ) (hq : 1 ≤ q) (h : I ≤ C ^ (4 * q) * J ^ 2) :
    I ^ (1 / (4 * (q : ℝ))) ≤ C * J ^ (1 / (2 * (q : ℝ))) := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hq)
  have h4q : (0 : ℝ) < 4 * (q : ℝ) := by positivity
  have he : (1 / (2 * (q : ℝ))) * (4 * (q : ℝ)) = 2 := by field_simp; norm_num
  have hp : (C * J ^ (1 / (2 * (q : ℝ)))) ^ (4 * (q : ℝ)) =
      C ^ (4 * q) * J ^ 2 := by
    rw [Real.mul_rpow hC (Real.rpow_nonneg hJ _), ← Real.rpow_mul hJ,
      he, Real.rpow_two]
    congr 1
    rw [← Real.rpow_natCast C (4 * q)]
    push_cast
    rfl
  rw [one_div]
  apply (Real.rpow_inv_le_iff_of_pos hI
    (mul_nonneg hC (Real.rpow_nonneg hJ (1 / (2 * (q : ℝ))))) h4q).mpr
  rw [hp]
  exact h

section Probability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The positive word expansion gives uniform even-order doubling of a
signed linear sum. This imports no separate scalar regularity theorem. -/
theorem signed_linear_even_moment_doubling
    (Z : E → Ω → ℝ) (hZ : ∀ e, Measurable (Z e))
    (hind : iIndepFun Z μ) (hnonneg : ∀ e ω, 0 ≤ Z e ω)
    (hint : ∀ e (p : ℝ), 0 < p → Integrable (fun ω => |Z e ω| ^ p) μ)
    (α : ℝ) (hα : 1 ≤ α)
    (hregular : ∀ e (r : ℝ), 1 ≤ r →
      moment μ (2 * r) (Z e) ≤ α * moment μ r (Z e))
    (a : E → ℝ) (ha : ∀ e, 0 ≤ a e) (q : ℕ) :
    (∫ ω, independentSignLaw.expect (fun σ => signedLinearForm a Z ω σ ^ (4 * q)) ∂μ) ≤
      (9 : ℝ) ^ q * α ^ (8 * q) *
        (∫ ω, independentSignLaw.expect (fun σ => signedLinearForm a Z ω σ ^ (2 * q)) ∂μ) ^ 2 := by
  have h := raw_positive_polynomial_fourth_moment Z hZ hind hnonneg hint α hα hregular
    (fun (_ : Unit) => (wordCoeff a : (Fin q → E) → ℝ))
    (fun (_ : Unit) => (wordExponent : (Fin q → E) → E → ℕ))
    (fun _ w => wordCoeff_nonneg a ha w)
    q (fun _ w => le_of_eq (wordExponent_degree w))
  have hp2 (x : ℝ) : (x ^ q) ^ 2 = x ^ (2 * q) := by
    rw [← pow_mul, Nat.mul_comm q 2]
  have hp4 (x : ℝ) : (x ^ (2 * q)) ^ 2 = x ^ (4 * q) := by
    rw [← pow_mul]
    congr 1
    omega
  simpa only [Fintype.sum_unique, evaluate_words, hp2, hp4, signedLinearForm] using h

/-- Arbitrary real deterministic coefficients satisfy the same even-order
comparison, by exact invariance of the original independent sign law. -/
theorem signed_linear_even_moment_doubling_real_coeff
    (Z : E → Ω → ℝ) (hZ : ∀ e, Measurable (Z e))
    (hind : iIndepFun Z μ) (hnonneg : ∀ e ω, 0 ≤ Z e ω)
    (hint : ∀ e (p : ℝ), 0 < p → Integrable (fun ω => |Z e ω| ^ p) μ)
    (α : ℝ) (hα : 1 ≤ α)
    (hregular : ∀ e (r : ℝ), 1 ≤ r →
      moment μ (2 * r) (Z e) ≤ α * moment μ r (Z e))
    (a : E → ℝ) (q : ℕ) :
    (∫ ω, independentSignLaw.expect (fun σ => signedLinearForm a Z ω σ ^ (4 * q)) ∂μ) ≤
      (9 : ℝ) ^ q * α ^ (8 * q) *
        (∫ ω, independentSignLaw.expect (fun σ => signedLinearForm a Z ω σ ^ (2 * q)) ∂μ) ^ 2 := by
  have h := signed_linear_even_moment_doubling Z hZ hind hnonneg hint α hα hregular
    (fun e => |a e|) (fun e => abs_nonneg _) q
  have he (ω : Ω) (n : ℕ) :
      independentSignLaw.expect (fun σ => signedLinearForm (fun e => |a e|) Z ω σ ^ n) =
        independentSignLaw.expect (fun σ => signedLinearForm a Z ω σ ^ n) :=
    expect_signedLinearForm_abs a Z ω (fun x => x ^ n)
  simpa only [he] using h

/-- The rooted comparison is uniform in the even moment order and all
original scalar coefficients: `||S||_(4q) ≤ √3 α² ||S||_(2q)`. -/
theorem signed_linear_even_root_doubling
    (Z : E → Ω → ℝ) (hZ : ∀ e, Measurable (Z e))
    (hind : iIndepFun Z μ) (hnonneg : ∀ e ω, 0 ≤ Z e ω)
    (hint : ∀ e (p : ℝ), 0 < p → Integrable (fun ω => |Z e ω| ^ p) μ)
    (α : ℝ) (hα : 1 ≤ α)
    (hregular : ∀ e (r : ℝ), 1 ≤ r →
      moment μ (2 * r) (Z e) ≤ α * moment μ r (Z e))
    (a : E → ℝ) (q : ℕ) (hq : 1 ≤ q) :
    (∫ ω, independentSignLaw.expect
      (fun σ => signedLinearForm a Z ω σ ^ (4 * q)) ∂μ) ^ (1 / (4 * (q : ℝ))) ≤
      (Real.sqrt 3 * α ^ 2) *
        (∫ ω, independentSignLaw.expect
          (fun σ => signedLinearForm a Z ω σ ^ (2 * q)) ∂μ) ^ (1 / (2 * (q : ℝ))) := by
  have heven (r : ℕ) :
      0 ≤ ∫ ω, independentSignLaw.expect
        (fun σ => signedLinearForm a Z ω σ ^ (2 * r)) ∂μ := by
    apply integral_nonneg
    intro ω
    apply FiniteLaw.expect_nonneg
    intro σ
    rw [pow_mul]
    exact pow_nonneg (sq_nonneg _) _
  have hI : 0 ≤ ∫ ω, independentSignLaw.expect
      (fun σ => signedLinearForm a Z ω σ ^ (4 * q)) ∂μ := by
    have he : 2 * (2 * q) = 4 * q := by omega
    simpa only [he] using heven (2 * q)
  have hC : 0 ≤ Real.sqrt 3 * α ^ 2 := mul_nonneg (Real.sqrt_nonneg _) (sq_nonneg _)
  have hs : (Real.sqrt (3 : ℝ)) ^ 4 = 9 := by
    calc
      _ = ((Real.sqrt (3 : ℝ)) ^ 2) ^ 2 := by ring_nf
      _ = 9 := by rw [Real.sq_sqrt (by norm_num)]; norm_num
  have hconst : (Real.sqrt 3 * α ^ 2) ^ (4 * q) = (9 : ℝ) ^ q * α ^ (8 * q) := by
    rw [mul_pow, pow_mul, hs]
    congr 1
    rw [← pow_mul]
    congr 1
    omega
  apply even_root_le _ _ _ hI (heven q) hC q hq
  rw [hconst]
  exact signed_linear_even_moment_doubling_real_coeff Z hZ hind hnonneg hint
    α hα hregular a q

end Probability

end MI32.PositiveLinearPowers
