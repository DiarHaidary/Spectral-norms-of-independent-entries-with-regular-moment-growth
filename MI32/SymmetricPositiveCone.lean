import MI32.RawPositiveCone
import MI32.SymmetricLaw
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Positive-polynomial fourth moments under the original symmetric laws

The theorem in this file concerns the original independent real variables themselves.
The exact sign/magnitude law transfer is proved in `SymmetricLaw`; the parity expansion,
positive magnitude comparison, and Hilbert Boolean estimate are proved in the imported
analytic core. No conditional sign model remains in the final theorem statement.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory GraphMatrices

namespace MI32.SymmetricPositiveCone

open PositivePolynomial

variable {Ω E A κ : Type*} [MeasurableSpace Ω] [Fintype E] [DecidableEq E]
    [Fintype A] [Fintype κ] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The squared Euclidean norm, expressed in the original raw polynomial coordinates. -/
def normSq (c : A → κ → ℝ) (ν : A → κ → E → ℕ) (z : E → ℝ) : ℝ :=
  ∑ a, evaluate (c a) (ν a) z ^ 2

omit [DecidableEq E] in
@[fun_prop] theorem measurable_normSq (c : A → κ → ℝ) (ν : A → κ → E → ℕ) :
    Measurable (normSq c ν) := by
  unfold normSq evaluate monomial
  fun_prop

omit [Fintype E] [DecidableEq E] in
/-- All natural powers of a signed variable are integrable when its positive
absolute moments are finite; no symmetry is needed for this step. -/
theorem integrable_nat_powers (W : E → Ω → ℝ) (hW : ∀ e, Measurable (W e))
    (hint : ∀ e (p : ℝ), 0 < p → Integrable (fun ω => |W e ω| ^ p) μ)
    (e : E) (r : ℕ) : Integrable (fun ω => W e ω ^ r) μ := by
  by_cases hr : r = 0
  · simp only [hr, pow_zero]
    exact integrable_const 1
  · have hp : (0 : ℝ) < (r : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hr
    have hnorm : Integrable (fun ω => ‖W e ω ^ r‖) μ := by
      simpa only [Real.norm_eq_abs, abs_pow, Real.rpow_natCast] using hint e r hp
    exact (integrable_norm_iff ((hW e).pow_const r).aestronglyMeasurable).mp hnorm

omit [DecidableEq E] in
/-- Integrability of the squared Euclidean polynomial norm under the original law. -/
theorem integrable_normSq (W : E → Ω → ℝ) (hW : ∀ e, Measurable (W e))
    (hind : iIndepFun W μ)
    (hint : ∀ e (p : ℝ), 0 < p → Integrable (fun ω => |W e ω| ^ p) μ)
    (c : A → κ → ℝ) (ν : A → κ → E → ℕ) :
    Integrable (fun ω => normSq c ν (fun e => W e ω)) μ := by
  exact integrable_finsetSum _ fun a _ =>
    PositiveCone.integrable_evaluate_sq W hW hind
      (integrable_nat_powers W hW hint) (c a) (ν a)

omit [DecidableEq E] in
/-- The fourth Euclidean moment is integrable without a sign-model assumption.
Its energy is expanded into a finite family retaining both original term labels. -/
theorem integrable_normSq_sq (W : E → Ω → ℝ) (hW : ∀ e, Measurable (W e))
    (hind : iIndepFun W μ)
    (hint : ∀ e (p : ℝ), 0 < p → Integrable (fun ω => |W e ω| ^ p) μ)
    (c : A → κ → ℝ) (ν : A → κ → E → ℕ) :
    Integrable (fun ω => normSq c ν (fun e => W e ω) ^ 2) μ := by
  let C : A × κ × κ → ℝ := fun t => c t.1 t.2.1 * c t.1 t.2.2
  let V : A × κ × κ → E → ℕ := fun t => ν t.1 t.2.1 + ν t.1 t.2.2
  have henergy (z : E → ℝ) : evaluate C V z = normSq c ν z := by
    simp only [normSq, evaluate_sq]
    simp only [evaluate, C, V, Fintype.sum_prod_type]
  simp_rw [← henergy]
  exact PositiveCone.integrable_evaluate_sq W hW hind
    (integrable_nat_powers W hW hint) C V

/-- Dimension-free positive-polynomial hypercontractivity for the *original*
independent symmetric real variables on an arbitrary probability space.
Every moment and regularity assumption is one-coordinate. Raw degree, coefficient
positivity, and every original variable identity are explicit. -/
theorem fourth_moment
    (W : E → Ω → ℝ) (hW : ∀ e, Measurable (W e)) (hind : iIndepFun W μ)
    (hsym : ∀ e, IdentDistrib (W e) (fun ω => -W e ω) μ μ)
    (hint : ∀ e (p : ℝ), 0 < p → Integrable (fun ω => |W e ω| ^ p) μ)
    (α : ℝ) (hα : 1 ≤ α)
    (hregular : ∀ e (r : ℝ), 1 ≤ r →
      moment μ (2 * r) (W e) ≤ α * moment μ r (W e))
    (c : A → κ → ℝ) (ν : A → κ → E → ℕ)
    (hc : ∀ a t, 0 ≤ c a t)
    (d : ℕ) (hdegree : ∀ a t, degree (ν a t) ≤ d) :
    (∫ ω, normSq c ν (fun e => W e ω) ^ 2 ∂μ) ≤
      (9 : ℝ) ^ d * α ^ (8 * d) *
        (∫ ω, normSq c ν (fun e => W e ω) ∂μ) ^ 2 := by
  have hZ : ∀ e, Measurable (fun ω => |W e ω|) := fun e => by fun_prop
  have hindZ := SymmetricLaw.independent_abs W hind
  have hintZ : ∀ e (p : ℝ), 0 < p → Integrable (fun ω => abs (abs (W e ω)) ^ p) μ := by
    intro e p hp
    simpa only [abs_abs] using hint e p hp
  have hregularZ : ∀ e (r : ℝ), 1 ≤ r →
      moment μ (2 * r) (fun ω => |W e ω|) ≤
        α * moment μ r (fun ω => |W e ω|) := by
    intro e r hr
    simpa only [moment, abs_abs] using hregular e r hr
  have hbound := raw_positive_polynomial_fourth_moment
    (fun e ω => |W e ω|) hZ hindZ (fun e ω => abs_nonneg _) hintZ
    α hα hregularZ c ν hc d hdegree
  simp_rw [independentSignLaw_expect_eq_walsh] at hbound
  have hsecond := SymmetricLaw.integral_eq_walsh_signedAbs W hW hind hsym
    (normSq c ν) (measurable_normSq c ν) (integrable_normSq W hW hind hint c ν)
  have hfourth := SymmetricLaw.integral_eq_walsh_signedAbs W hW hind hsym
    (fun z => normSq c ν z ^ 2) ((measurable_normSq c ν).pow_const 2)
    (integrable_normSq_sq W hW hind hint c ν)
  rw [hfourth, hsecond]
  exact hbound





/-- The polynomial evaluated in the actual finite-dimensional real Euclidean space. -/
def evaluateHilbert (c : A → κ → ℝ) (ν : A → κ → E → ℕ) (z : E → ℝ) :
    EuclideanSpace ℝ A := WithLp.toLp 2 (fun a => evaluate (c a) (ν a) z)

omit [DecidableEq E] in
/-- The retained energy is exactly the squared Hilbert norm, not a comparison descriptor. -/
theorem evaluateHilbert_norm_sq (c : A → κ → ℝ) (ν : A → κ → E → ℕ) (z : E → ℝ) :
    ‖evaluateHilbert c ν z‖ ^ 2 = normSq c ν z := by
  exact EuclideanSpace.real_norm_sq_eq (evaluateHilbert c ν z)

omit [DecidableEq E] in
theorem evaluateHilbert_norm_fourth (c : A → κ → ℝ) (ν : A → κ → E → ℕ) (z : E → ℝ) :
    ‖evaluateHilbert c ν z‖ ^ 4 = normSq c ν z ^ 2 := by
  calc
    _ = (‖evaluateHilbert c ν z‖ ^ 2) ^ 2 := by ring
    _ = _ := by rw [evaluateHilbert_norm_sq]

/-- The same original-law theorem expressed using the actual Euclidean norm. -/
theorem fourth_norm_moment
    (W : E → Ω → ℝ) (hW : ∀ e, Measurable (W e)) (hind : iIndepFun W μ)
    (hsym : ∀ e, IdentDistrib (W e) (fun ω => -W e ω) μ μ)
    (hint : ∀ e (p : ℝ), 0 < p → Integrable (fun ω => |W e ω| ^ p) μ)
    (α : ℝ) (hα : 1 ≤ α)
    (hregular : ∀ e (r : ℝ), 1 ≤ r →
      moment μ (2 * r) (W e) ≤ α * moment μ r (W e))
    (c : A → κ → ℝ) (ν : A → κ → E → ℕ)
    (hc : ∀ a t, 0 ≤ c a t)
    (d : ℕ) (hdegree : ∀ a t, degree (ν a t) ≤ d) :
    (∫ ω, ‖evaluateHilbert c ν (fun e => W e ω)‖ ^ 4 ∂μ) ≤
      (9 : ℝ) ^ d * α ^ (8 * d) *
        (∫ ω, ‖evaluateHilbert c ν (fun e => W e ω)‖ ^ 2 ∂μ) ^ 2 := by
  simp only [evaluateHilbert_norm_fourth, evaluateHilbert_norm_sq]
  exact fourth_moment W hW hind hsym hint α hα hregular c ν hc d hdegree

end MI32.SymmetricPositiveCone
