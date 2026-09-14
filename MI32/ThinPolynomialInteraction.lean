import MI32.ThinMatrix
import MI32.MultiplicationHolder
import MI32.SymmetricConeInterpolation

/-!
# One dependent thin-matrix interaction with an original positive polynomial

Both the random matrix and the polynomial are evaluated on the same original
probability space. The polynomial may retain an arbitrary finite family of
original variables, including variables outside the matrix's active axes.
No independence between the matrix and the polynomial variable family is used.
The comparison concerns the actual random polynomial, not a different norm
on its Walsh coefficients.
-/

noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory

namespace MI32.ThinPolynomialInteraction

open PositivePolynomial SymmetricPositiveCone

variable {Ω I J E κ : Type*} [MeasurableSpace Ω]
    [Fintype I] [Fintype J] [Fintype E] [Fintype κ]
    [DecidableEq I] [DecidableEq J] [DecidableEq E]
    {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The original raw polynomial with every original variable and exponent retained. -/
def polynomialVector (W : E → Ω → ℝ) (c : I → κ → ℝ) (ν : I → κ → E → ℕ)
    (ω : Ω) : EuclideanSpace ℝ I :=
  evaluateHilbert c ν (fun e => W e ω)

/-- Actual multiplication on the same sample, allowing all dependence between
the operator entries and the polynomial's original variables. -/
def action (X : I → J → Ω → ℝ) (W : E → Ω → ℝ)
    (c : I → κ → ℝ) (ν : I → κ → E → ℕ) (ω : Ω) : EuclideanSpace ℝ J :=
  ThinMatrix.transposeOperator X ω (polynomialVector W c ν ω)

omit [Fintype I] [DecidableEq I] [DecidableEq J] [DecidableEq E] [IsProbabilityMeasure μ] in
@[fun_prop] theorem measurable_polynomialVector (W : E → Ω → ℝ)
    (hW : ∀ e, Measurable (W e)) (c : I → κ → ℝ) (ν : I → κ → E → ℕ) :
    Measurable (polynomialVector W c ν) := by
  unfold polynomialVector evaluateHilbert evaluate monomial
  fun_prop

omit [DecidableEq J] [DecidableEq E] [IsProbabilityMeasure μ] in
@[fun_prop] theorem measurable_action (X : I → J → Ω → ℝ)
    (hX : ∀ i j, Measurable (X i j)) (W : E → Ω → ℝ)
    (hW : ∀ e, Measurable (W e)) (c : I → κ → ℝ) (ν : I → κ → E → ℕ) :
    Measurable (action X W c ν) := by
  unfold action
  simp_rw [ThinMatrix.transposeOperator_apply]
  unfold matrixRowImage polynomialVector evaluateHilbert evaluate monomial
  fun_prop

omit [DecidableEq J] in
/-- One original-law interaction. The original matrix and polynomial may share
all their randomness; internal coordinate independence is required separately
only for the already proved thin-matrix and positive-polynomial estimates.
In particular the polynomial can retain original spectator coordinates outside
the active thin matrix. The action's squared norm integrability is derived. -/
theorem action_l2_le
    (X : I → J → Ω → ℝ) (hX : ∀ i j, Measurable (X i j))
    (hindX : iIndepFun (fun e : I × J => X e.1 e.2) μ)
    (hsymX : ∀ i j, IdentDistrib (X i j) (fun ω => -X i j ω) μ μ)
    (hintX : ∀ i j (p : ℝ), 0 < p → Integrable (fun ω => |X i j ω| ^ p) μ)
    (W : E → Ω → ℝ) (hW : ∀ e, Measurable (W e)) (hindW : iIndepFun W μ)
    (hsymW : ∀ e, IdentDistrib (W e) (fun ω => -W e ω) μ μ)
    (hintW : ∀ e (p : ℝ), 0 < p → Integrable (fun ω => |W e ω| ^ p) μ)
    (α : ℝ) (hα : 1 ≤ α)
    (hregularX : ∀ i j (r : ℝ), 1 ≤ r →
      moment μ (2 * r) (X i j) ≤ α * moment μ r (X i j))
    (hregularW : ∀ e (r : ℝ), 1 ≤ r →
      moment μ (2 * r) (W e) ≤ α * moment μ r (W e))
    (q : ℕ) (hq : 1 ≤ q) (hthin : Fintype.card I ≤ q)
    (B : ℝ) (hB : 0 ≤ B)
    (hrow : ∀ i, (∑ j, ∫ ω, X i j ω ^ 2 ∂μ) ≤ B ^ 2)
    (R : ℝ) (hR : 0 ≤ R)
    (hweak : ∀ s : EuclideanSpace ℝ I, ‖s‖ ≤ 1 →
      ∀ t : EuclideanSpace ℝ J, ‖t‖ ≤ 1 →
        moment μ (2 * (q : ℝ)) (ThinMatrix.bilinear X s t) ≤ R)
    (c : I → κ → ℝ) (ν : I → κ → E → ℕ) (hc : ∀ i t, 0 ≤ c i t)
    (d : ℕ) (hdegree : ∀ i t, degree (ν i t) ≤ d) (hdq : d < q) :
    Integrable (fun ω => ‖action X W c ν ω‖ ^ 2) μ ∧
      moment μ 2 (fun ω => ‖action X W c ν ω‖) ≤
        ((2 : ℝ) * (5 : ℝ) ^ (1 / 4 : ℝ) * (B + 6 * α ^ 4 * R)) *
          (Real.sqrt 3 * α ^ 2) * moment μ 2 (fun ω => ‖polynomialVector W c ν ω‖) := by
  have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hp : (2 : ℝ) < 4 * (q : ℝ) := by linarith
  have hden : (0 : ℝ) < 4 * (q : ℝ) - 2 := by linarith
  have hr0 : 0 < 2 * (4 * (q : ℝ)) / (4 * (q : ℝ) - 2) := by positivity
  have hr4 : 2 * (4 * (q : ℝ)) / (4 * (q : ℝ) - 2) ≤ (4 : ℝ) := by
    apply (div_le_iff₀ hden).mpr
    linarith
  obtain ⟨hAint, hAbound⟩ := ThinMatrix.transposeOperator_moment_four_mul_le
    X hX hindX hsymX hintX α hα hregularX q hq hthin B hB hrow R hR hweak
  have hAmem : MemLp (fun ω => ‖ThinMatrix.transposeOperator X ω‖)
      (ENNReal.ofReal (4 * (q : ℝ))) μ := by
    have h := MomentTools.memLp_of_integrable_even_pow
      (fun ω => ‖ThinMatrix.transposeOperator X ω‖)
      (ThinMatrix.measurable_norm_transposeOperator X hX).aestronglyMeasurable
      (4 * q) (by omega) (show Even (4 * q) from ⟨2 * q, by omega⟩) hAint
    simpa using h
  have hFmeas : Measurable (fun ω => ‖polynomialVector W c ν ω‖) :=
    (measurable_polynomialVector W hW c ν).norm
  have hF4 : Integrable (fun ω => ‖polynomialVector W c ν ω‖ ^ 4) μ := by
    simpa only [polynomialVector, evaluateHilbert_norm_fourth] using
      integrable_normSq_sq W hW hindW hintW c ν
  have hFmem : MemLp (fun ω => ‖polynomialVector W c ν ω‖)
      (ENNReal.ofReal (2 * (4 * (q : ℝ)) / (4 * (q : ℝ) - 2))) μ :=
    ConeInterpolation.memLp_of_fourth _ hFmeas (fun _ => norm_nonneg _) hF4 _ hr0 hr4
  have hFbound := SymmetricConeInterpolation.moment_four_q_le W hW hindW hsymW hintW
    α hα hregularW c ν hc d q hdegree hdq
  change moment μ (2 * (4 * (q : ℝ)) / (4 * (q : ℝ) - 2))
      (fun ω => ‖polynomialVector W c ν ω‖) ≤
    (Real.sqrt 3 * α ^ 2) * moment μ 2 (fun ω => ‖polynomialVector W c ν ω‖) at hFbound
  obtain ⟨hactint, hactbound⟩ := MultiplicationHolder.operator_action_l2_le
    (ThinMatrix.transposeOperator X) (polynomialVector W c ν) (4 * (q : ℝ)) hp
    hAmem hFmem (measurable_action X hX W hW c ν).norm.aestronglyMeasurable
  refine ⟨hactint, hactbound.trans ?_⟩
  have hgain := mul_le_mul hAbound hFbound
    (MomentTools.nonneg (μ := μ) _ (fun ω => ‖polynomialVector W c ν ω‖))
    (le_trans (MomentTools.nonneg (μ := μ) _ (fun ω => ‖ThinMatrix.transposeOperator X ω‖)) hAbound)
  simpa only [mul_assoc] using hgain

/-- Specialization where every polynomial variable is exactly one of the
original matrix entries, with its ordered-pair identity retained. -/
theorem same_entries_action_l2_le
    (X : I → J → Ω → ℝ) (hX : ∀ i j, Measurable (X i j))
    (hind : iIndepFun (fun e : I × J => X e.1 e.2) μ)
    (hsym : ∀ i j, IdentDistrib (X i j) (fun ω => -X i j ω) μ μ)
    (hint : ∀ i j (p : ℝ), 0 < p → Integrable (fun ω => |X i j ω| ^ p) μ)
    (α : ℝ) (hα : 1 ≤ α)
    (hregular : ∀ i j (r : ℝ), 1 ≤ r →
      moment μ (2 * r) (X i j) ≤ α * moment μ r (X i j))
    (q : ℕ) (hq : 1 ≤ q) (hthin : Fintype.card I ≤ q)
    (B : ℝ) (hB : 0 ≤ B)
    (hrow : ∀ i, (∑ j, ∫ ω, X i j ω ^ 2 ∂μ) ≤ B ^ 2)
    (R : ℝ) (hR : 0 ≤ R)
    (hweak : ∀ s : EuclideanSpace ℝ I, ‖s‖ ≤ 1 →
      ∀ t : EuclideanSpace ℝ J, ‖t‖ ≤ 1 →
        moment μ (2 * (q : ℝ)) (ThinMatrix.bilinear X s t) ≤ R)
    (c : I → κ → ℝ) (ν : I → κ → I × J → ℕ) (hc : ∀ i t, 0 ≤ c i t)
    (d : ℕ) (hdegree : ∀ i t, degree (ν i t) ≤ d) (hdq : d < q) :
    Integrable (fun ω => ‖action X (fun e : I × J => X e.1 e.2) c ν ω‖ ^ 2) μ ∧
      moment μ 2 (fun ω => ‖action X (fun e : I × J => X e.1 e.2) c ν ω‖) ≤
        ((2 : ℝ) * (5 : ℝ) ^ (1 / 4 : ℝ) * (B + 6 * α ^ 4 * R)) *
          (Real.sqrt 3 * α ^ 2) *
            moment μ 2 (fun ω => ‖polynomialVector (fun e : I × J => X e.1 e.2) c ν ω‖) :=
  action_l2_le X hX hind hsym hint (fun e : I × J => X e.1 e.2)
    (fun e => hX e.1 e.2) hind (fun e => hsym e.1 e.2) (fun e => hint e.1 e.2)
    α hα hregular (fun e => hregular e.1 e.2) q hq hthin B hB hrow R hR hweak
    c ν hc d hdegree hdq

end MI32.ThinPolynomialInteraction
