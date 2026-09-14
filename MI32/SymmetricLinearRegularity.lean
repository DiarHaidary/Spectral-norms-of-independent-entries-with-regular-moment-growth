import MI32.PositiveLinearPowers
import MI32.SymmetricLaw
import MI32.IndependentColumns

/-!
# Even-order regularity of linear forms in the original symmetric variables

The signed positive-word calculation is transferred through the proved exact
joint law of the original variables. The resulting constant is uniform in the
number of coordinates, the real deterministic coefficients, and the even order.
No conditional sign law or separate linear-form regularity premise is assumed.
-/

noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory GraphMatrices

namespace MI32.SymmetricLinearRegularity

variable {Ω E : Type*} [MeasurableSpace Ω] [Fintype E]
    {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- A linear form in the original random variables, with arbitrary real coefficients. -/
def linearForm (W : E → Ω → ℝ) (a : E → ℝ) (ω : Ω) : ℝ :=
  ∑ e, a e * W e ω

@[fun_prop] theorem measurable_linearForm (W : E → Ω → ℝ)
    (hW : ∀ e, Measurable (W e)) (a : E → ℝ) : Measurable (linearForm W a) := by
  unfold linearForm
  fun_prop

omit [IsProbabilityMeasure μ] in
/-- Every positive absolute moment of a finite linear form is integrable. -/
theorem integrable_abs_rpow_linearForm (W : E → Ω → ℝ)
    (hW : ∀ e, Measurable (W e))
    (hint : ∀ e (p : ℝ), 0 < p → Integrable (fun ω => |W e ω| ^ p) μ)
    (a : E → ℝ) (p : ℝ) (hp : 0 < p) :
    Integrable (fun ω => |linearForm W a ω| ^ p) μ :=
  IndependentColumns.integrable_abs_rpow_columnLinearForm
    (fun e (_ : Unit) => W e) (fun e _ => hW e) (fun e _ => hint e) a () p hp

/-- Natural powers, including zero, are integrable before the exact law transfer. -/
theorem integrable_pow_linearForm (W : E → Ω → ℝ)
    (hW : ∀ e, Measurable (W e))
    (hint : ∀ e (p : ℝ), 0 < p → Integrable (fun ω => |W e ω| ^ p) μ)
    (a : E → ℝ) (n : ℕ) : Integrable (fun ω => linearForm W a ω ^ n) μ := by
  by_cases hn : n = 0
  · simp only [hn, pow_zero]
    exact integrable_const 1
  · have hp : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hnorm : Integrable (fun ω => ‖linearForm W a ω ^ n‖) μ := by
      simpa only [Real.norm_eq_abs, abs_pow, Real.rpow_natCast] using
        integrable_abs_rpow_linearForm W hW hint a n hp
    exact (integrable_norm_iff
      ((measurable_linearForm W hW a).pow_const n).aestronglyMeasurable).mp hnorm

omit [IsProbabilityMeasure μ] in
/-- The absolute rooted even moment is the root of the ordinary even-power integral. -/
theorem moment_even_eq (S : Ω → ℝ) (r : ℕ) :
    moment μ (2 * (r : ℝ)) S =
      (∫ ω, S ω ^ (2 * r) ∂μ) ^ (1 / (2 * (r : ℝ))) := by
  unfold moment
  congr 1
  apply integral_congr_ae
  filter_upwards [] with ω
  rw [show (2 : ℝ) * (r : ℝ) = ((2 * r : ℕ) : ℝ) by push_cast; rfl,
    Real.rpow_natCast, pow_mul, pow_mul, sq_abs]

variable [DecidableEq E]

/-- Exact transfer of each ordinary moment of the original linear form to the
finite sign average of that same form evaluated on the original magnitudes. -/
theorem integral_pow_eq_signedAbs (W : E → Ω → ℝ)
    (hW : ∀ e, Measurable (W e)) (hind : iIndepFun W μ)
    (hsym : ∀ e, IdentDistrib (W e) (fun ω => -W e ω) μ μ)
    (hint : ∀ e (p : ℝ), 0 < p → Integrable (fun ω => |W e ω| ^ p) μ)
    (a : E → ℝ) (n : ℕ) :
    (∫ ω, linearForm W a ω ^ n ∂μ) =
      ∫ ω, independentSignLaw.expect (fun σ =>
        PositiveLinearPowers.signedLinearForm a (fun e ω => |W e ω|) ω σ ^ n) ∂μ := by
  simp_rw [independentSignLaw_expect_eq_walsh]
  exact SymmetricLaw.integral_eq_walsh_signedAbs W hW hind hsym
    (fun z => (∑ e, a e * z e) ^ n) (by fun_prop)
    (integrable_pow_linearForm W hW hint a n)

/-- Uniform even-order doubling for the actual original linear form:
`||∑ aₑWₑ||_(4r) ≤ √3 α² ||∑ aₑWₑ||_(2r)` for every natural `r ≥ 1`.
The hypotheses concern only the independent symmetric original coordinates. -/
theorem linear_even_root_doubling
    (W : E → Ω → ℝ) (hW : ∀ e, Measurable (W e)) (hind : iIndepFun W μ)
    (hsym : ∀ e, IdentDistrib (W e) (fun ω => -W e ω) μ μ)
    (hint : ∀ e (p : ℝ), 0 < p → Integrable (fun ω => |W e ω| ^ p) μ)
    (α : ℝ) (hα : 1 ≤ α)
    (hregular : ∀ e (r : ℝ), 1 ≤ r →
      moment μ (2 * r) (W e) ≤ α * moment μ r (W e))
    (a : E → ℝ) (r : ℕ) (hr : 1 ≤ r) :
    moment μ (4 * (r : ℝ)) (linearForm W a) ≤
      (Real.sqrt 3 * α ^ 2) * moment μ (2 * (r : ℝ)) (linearForm W a) := by
  have h := PositiveLinearPowers.signed_linear_even_root_doubling
    (fun e ω => |W e ω|) (fun e => by fun_prop)
    (SymmetricLaw.independent_abs W hind) (fun e ω => abs_nonneg _)
    (fun e p hp => by simpa only [abs_abs] using hint e p hp) α hα
    (fun e p hp => by simpa only [moment, abs_abs] using hregular e p hp) a r hr
  rw [← integral_pow_eq_signedAbs W hW hind hsym hint a (4 * r),
    ← integral_pow_eq_signedAbs W hW hind hsym hint a (2 * r)] at h
  have h4 : moment μ (4 * (r : ℝ)) (linearForm W a) =
      (∫ ω, linearForm W a ω ^ (4 * r) ∂μ) ^ (1 / (4 * (r : ℝ))) := by
    have hnat : 2 * (2 * r) = 4 * r := by omega
    have hreal : (2 : ℝ) * (2 * (r : ℝ)) = 4 * (r : ℝ) := by ring
    simpa only [Nat.cast_mul, Nat.cast_ofNat, hnat, hreal] using
      moment_even_eq (μ := μ) (linearForm W a) (2 * r)
  rw [h4, moment_even_eq]
  exact h

section Columns

variable {J : Type*}

/-- Each fixed-vector column image inherits the same even-order regularity,
directly from the independent original matrix entries. -/
theorem columnLinearForm_even_root_doubling
    (X : E → J → Ω → ℝ) (hX : ∀ e j, Measurable (X e j))
    (hind : iIndepFun (fun e : E × J => X e.1 e.2) μ)
    (hsym : ∀ e j, IdentDistrib (X e j) (fun ω => -X e j ω) μ μ)
    (hint : ∀ e j (p : ℝ), 0 < p → Integrable (fun ω => |X e j ω| ^ p) μ)
    (α : ℝ) (hα : 1 ≤ α)
    (hregular : ∀ e j (r : ℝ), 1 ≤ r →
      moment μ (2 * r) (X e j) ≤ α * moment μ r (X e j))
    (s : E → ℝ) (j : J) (r : ℕ) (hr : 1 ≤ r) :
    moment μ (4 * (r : ℝ)) (IndependentColumns.columnLinearForm X s j) ≤
      (Real.sqrt 3 * α ^ 2) *
        moment μ (2 * (r : ℝ)) (IndependentColumns.columnLinearForm X s j) :=
  linear_even_root_doubling (fun e => X e j) (fun e => hX e j)
    (IndependentColumns.independent_within_column X hind j) (fun e => hsym e j)
    (fun e => hint e j) α hα (fun e => hregular e j) s r hr

end Columns

end MI32.SymmetricLinearRegularity
