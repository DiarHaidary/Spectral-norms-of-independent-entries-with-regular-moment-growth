import MI32.PositiveMomentComparison
import MI32.PositiveLinearPowers
import Mathlib.Probability.IdentDistrib

/-!
# Even-moment comparison of independent symmetric sums

Odd coordinate moments vanish by actual equality in distribution under
negation. Even moments are nonnegative. These facts allow the positive
finite word expansion to tensorize coordinate even-moment comparisons
without replacing the original independent laws or assuming a mixed-moment
comparison. The two families can live on different probability spaces.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace MI32.SymmetricMomentComparison

variable {Ω Ω' E : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  [Fintype E] [DecidableEq E] {μ : Measure Ω} {μ' : Measure Ω'}

omit [Fintype E] [DecidableEq E] in
/-- Symmetry forces every odd natural-power integral to vanish. -/
theorem integral_odd_power_eq_zero (X : Ω → ℝ)
    (hsym : IdentDistrib X (fun ω => -X ω) μ μ)
    (n : ℕ) (hn : Odd n) : (∫ ω, X ω ^ n ∂μ) = 0 := by
  have h := (hsym.comp (measurable_id.pow_const n)).integral_eq
  simp only [Function.comp_apply, id_eq, hn.neg_pow, integral_neg] at h
  linarith

omit [Fintype E] [DecidableEq E] in
/-- All natural coordinate moments of a symmetric real variable are nonnegative. -/
theorem integral_power_nonneg (X : Ω → ℝ)
    (hsym : IdentDistrib X (fun ω => -X ω) μ μ) (n : ℕ) :
    0 ≤ ∫ ω, X ω ^ n ∂μ := by
  rcases Nat.even_or_odd n with hn | hn
  · exact integral_nonneg fun ω => hn.pow_nonneg (X ω)
  · rw [integral_odd_power_eq_zero X hsym n hn]

omit [Fintype E] [DecidableEq E] in
/-- Coordinate even-power comparisons imply comparisons at every natural
power because both families' odd moments are zero. -/
theorem coordinate_all_power_comparison
    (X : E → Ω → ℝ) (Y : E → Ω' → ℝ)
    (hsymX : ∀ e, IdentDistrib (X e) (fun ω => -X e ω) μ μ)
    (hsymY : ∀ e, IdentDistrib (Y e) (fun ω => -Y e ω) μ' μ')
    (C : ℝ)
    (hcomp : ∀ e r, (∫ ω, X e ω ^ (2 * r) ∂μ) ≤
      C ^ (2 * r) * ∫ ω, Y e ω ^ (2 * r) ∂μ') :
    ∀ e n, (∫ ω, X e ω ^ n ∂μ) ≤ C ^ n * ∫ ω, Y e ω ^ n ∂μ' := by
  intro e n
  rcases Nat.even_or_odd n with hn | hn
  · rcases hn with ⟨r, hr⟩
    have he : n = 2 * r := by omega
    rw [he]
    exact hcomp e r
  · rw [integral_odd_power_eq_zero (X e) (hsymX e) n hn,
      integral_odd_power_eq_zero (Y e) (hsymY e) n hn, mul_zero]

section Probability

variable [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']

omit [Fintype E] [DecidableEq E] in
/-- Rooted even-order coordinate comparisons give the ordinary even-power
comparisons used by tensorization. The zeroth order follows from probability normalization. -/
theorem even_power_comparison_of_moment_comparison
    (X : E → Ω → ℝ) (Y : E → Ω' → ℝ) (C : ℝ)
    (hcomp : ∀ e (r : ℕ), 1 ≤ r →
      moment μ (2 * (r : ℝ)) (X e) ≤ C * moment μ' (2 * (r : ℝ)) (Y e)) :
    ∀ e r, (∫ ω, X e ω ^ (2*r) ∂μ) ≤ C ^ (2*r) * ∫ ω, Y e ω ^ (2*r) ∂μ' := by
  intro e r
  by_cases hr : r = 0
  · simp [hr]
  · have hrpos : 0 < 2*r := by omega
    have hx : moment μ (2 * (r : ℝ)) (X e) ^ (2*r) =
        ∫ ω, X e ω ^ (2*r) ∂μ := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat, pow_abs_two_mul] using
        moment_nat_pow μ (X e) (2*r) hrpos
    have hy : moment μ' (2 * (r : ℝ)) (Y e) ^ (2*r) =
        ∫ ω, Y e ω ^ (2*r) ∂μ' := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat, pow_abs_two_mul] using
        moment_nat_pow μ' (Y e) (2*r) hrpos
    have hn : 0 ≤ moment μ (2 * (r : ℝ)) (X e) :=
      Real.rpow_nonneg (integral_nonneg fun _ => Real.rpow_nonneg (abs_nonneg _) _) _
    have h := pow_le_pow_left₀ hn (hcomp e r (by omega)) (2*r)
    rwa [hx, mul_pow, hy] at h

/-- Actual-law comparison of the even moments of sums of independent symmetric
coordinates. No mixed-coordinate inequality is assumed. -/
theorem sum_even_power_le
    (X : E → Ω → ℝ) (Y : E → Ω' → ℝ)
    (hX : ∀ e, Measurable (X e)) (hY : ∀ e, Measurable (Y e))
    (hindX : iIndepFun X μ) (hindY : iIndepFun Y μ')
    (hintX : ∀ e r, Integrable (fun ω => X e ω ^ r) μ)
    (hintY : ∀ e r, Integrable (fun ω => Y e ω ^ r) μ')
    (hsymX : ∀ e, IdentDistrib (X e) (fun ω => -X e ω) μ μ)
    (hsymY : ∀ e, IdentDistrib (Y e) (fun ω => -Y e ω) μ' μ')
    (C : ℝ)
    (hcomp : ∀ e r, (∫ ω, X e ω ^ (2 * r) ∂μ) ≤
      C ^ (2 * r) * ∫ ω, Y e ω ^ (2 * r) ∂μ')
    (q : ℕ) :
    (∫ ω, (∑ e, X e ω) ^ (2 * q) ∂μ) ≤
      C ^ (2 * q) * ∫ ω, (∑ e, Y e ω) ^ (2 * q) ∂μ' := by
  have h := PositiveMomentComparison.integral_evaluate_le_of_moments X Y hX hY hindX hindY
    hintX hintY (fun e n => integral_power_nonneg (X e) (hsymX e) n) C
    (coordinate_all_power_comparison X Y hsymX hsymY C hcomp)
    (PositiveLinearPowers.wordCoeff (fun _ : E => 1) : (Fin (2*q) → E) → ℝ)
    PositiveLinearPowers.wordExponent
    (PositiveLinearPowers.wordCoeff_nonneg _ (fun _ => zero_le_one))
    (2*q) PositiveLinearPowers.wordExponent_degree
  simpa only [PositiveLinearPowers.evaluate_words, one_mul] using h

/-- The rooted comparison follows with exactly the same factor `C`. -/
theorem sum_even_moment_le
    (X : E → Ω → ℝ) (Y : E → Ω' → ℝ)
    (hX : ∀ e, Measurable (X e)) (hY : ∀ e, Measurable (Y e))
    (hindX : iIndepFun X μ) (hindY : iIndepFun Y μ')
    (hintX : ∀ e r, Integrable (fun ω => X e ω ^ r) μ)
    (hintY : ∀ e r, Integrable (fun ω => Y e ω ^ r) μ')
    (hsymX : ∀ e, IdentDistrib (X e) (fun ω => -X e ω) μ μ)
    (hsymY : ∀ e, IdentDistrib (Y e) (fun ω => -Y e ω) μ' μ')
    (C : ℝ) (hC : 0 ≤ C)
    (hcomp : ∀ e r, (∫ ω, X e ω ^ (2 * r) ∂μ) ≤
      C ^ (2 * r) * ∫ ω, Y e ω ^ (2 * r) ∂μ')
    (q : ℕ) (hq : 1 ≤ q) :
    moment μ (2 * (q : ℝ)) (fun ω => ∑ e, X e ω) ≤
      C * moment μ' (2 * (q : ℝ)) (fun ω => ∑ e, Y e ω) := by
  let I : ℝ := ∫ ω, (∑ e, X e ω) ^ (2*q) ∂μ
  let J : ℝ := ∫ ω, (∑ e, Y e ω) ^ (2*q) ∂μ'
  have hI : 0 ≤ I := integral_nonneg fun _ => (even_two_mul q).pow_nonneg _
  have hJ : 0 ≤ J := integral_nonneg fun _ => (even_two_mul q).pow_nonneg _
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hq)
  have h2q : (0 : ℝ) < 2 * (q : ℝ) := by positivity
  have hp : (C * J ^ (1 / (2 * (q : ℝ)))) ^ (2 * (q : ℝ)) = C ^ (2*q) * J := by
    rw [Real.mul_rpow hC (Real.rpow_nonneg hJ _), one_div,
      Real.rpow_inv_rpow hJ h2q.ne']
    congr 1
    rw [← Real.rpow_natCast C (2*q)]
    push_cast
    rfl
  have hroot : I ^ (1 / (2 * (q : ℝ))) ≤ C * J ^ (1 / (2 * (q : ℝ))) := by
    have hbound : I ≤ (C * J ^ (1 / (2 * (q : ℝ)))) ^ (2 * (q : ℝ)) := by
      rw [hp]
      exact sum_even_power_le X Y hX hY hindX hindY hintX hintY hsymX hsymY C hcomp q
    simpa only [one_div] using (Real.rpow_inv_le_iff_of_pos hI
      (mul_nonneg hC (Real.rpow_nonneg hJ (1 / (2 * (q : ℝ))))) h2q).mpr hbound
  have hpow (x : ℝ) : |x| ^ (2 * (q : ℝ)) = x ^ (2*q) := by
    have he : (2 : ℝ) * (q : ℝ) = ((2*q : ℕ) : ℝ) := by push_cast; rfl
    rw [he, Real.rpow_natCast, pow_abs_two_mul]
  simpa only [moment, hpow, I, J] using hroot

/-- Ready-to-use rooted comparison of symmetric sums from rooted comparisons
of the original coordinates, with the same constant and no dimension loss. -/
theorem sum_even_moment_le_of_coordinate_moments
    (X : E → Ω → ℝ) (Y : E → Ω' → ℝ)
    (hX : ∀ e, Measurable (X e)) (hY : ∀ e, Measurable (Y e))
    (hindX : iIndepFun X μ) (hindY : iIndepFun Y μ')
    (hintX : ∀ e r, Integrable (fun ω => X e ω ^ r) μ)
    (hintY : ∀ e r, Integrable (fun ω => Y e ω ^ r) μ')
    (hsymX : ∀ e, IdentDistrib (X e) (fun ω => -X e ω) μ μ)
    (hsymY : ∀ e, IdentDistrib (Y e) (fun ω => -Y e ω) μ' μ')
    (C : ℝ) (hC : 0 ≤ C)
    (hcomp : ∀ e (r : ℕ), 1 ≤ r →
      moment μ (2 * (r : ℝ)) (X e) ≤ C * moment μ' (2 * (r : ℝ)) (Y e))
    (q : ℕ) (hq : 1 ≤ q) :
    moment μ (2 * (q : ℝ)) (fun ω => ∑ e, X e ω) ≤
      C * moment μ' (2 * (q : ℝ)) (fun ω => ∑ e, Y e ω) :=
  sum_even_moment_le X Y hX hY hindX hindY hintX hintY hsymX hsymY C hC
    (even_power_comparison_of_moment_comparison X Y C hcomp) q hq

end Probability

end MI32.SymmetricMomentComparison
