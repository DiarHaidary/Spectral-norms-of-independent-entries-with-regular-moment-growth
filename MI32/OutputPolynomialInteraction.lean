import MI32.ThinTranspose
import MI32.ThinPolynomialInteraction

/-!
# Direct output-restricted interaction with the original polynomial cone

The polynomial input has every original row coordinate and may use every
original random variable, including entries outside the selected output
columns. The matrix and polynomial are evaluated on the same sample;
Holder introduces no independence assumption between them. Only the number
of selected output columns, not the input dimension, is bounded by `q`.
-/

noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory

namespace MI32.OutputPolynomialInteraction

open PositivePolynomial SymmetricPositiveCone
open ThinPolynomialInteraction (polynomialVector measurable_polynomialVector)

variable {Ω I J E κ : Type*} [MeasurableSpace Ω]
    [Fintype I] [Fintype J] [Fintype E] [Fintype κ]
    [DecidableEq I] [DecidableEq J] [DecidableEq E]
    {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The original transpose action with only the output coordinates restricted. -/
def action (X : I → J → Ω → ℝ) (T : Finset J) (W : E → Ω → ℝ)
    (c : I → κ → ℝ) (ν : I → κ → E → ℕ) (ω : Ω) : EuclideanSpace ℝ T :=
  ThinMatrix.transposeOperator (fun i (j : T) => X i j) ω (polynomialVector W c ν ω)

omit [Fintype J] [DecidableEq J] [DecidableEq E] [IsProbabilityMeasure μ] in
@[fun_prop] theorem measurable_action (X : I → J → Ω → ℝ)
    (hX : ∀ i j, Measurable (X i j)) (T : Finset J) (W : E → Ω → ℝ)
    (hW : ∀ e, Measurable (W e)) (c : I → κ → ℝ) (ν : I → κ → E → ℕ) :
    Measurable (action X T W c ν) :=
  ThinPolynomialInteraction.measurable_action (fun i (j : T) => X i j)
    (fun i j => hX i j) W hW c ν

/-- Direct annihilation-facing Holder bound. The original polynomial is
retained on all input rows and original variables. Its squared output norm
is integrable, with no dimension hypothesis on the full input axis. -/
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
    (q : ℕ) (hq : 1 ≤ q) (T : Finset J) (hthin : T.card ≤ q)
    (B : ℝ) (hB : 0 ≤ B)
    (hcol : ∀ j, (∑ i, ∫ ω, X i j ω ^ 2 ∂μ) ≤ B ^ 2)
    (R : ℝ) (hR : 0 ≤ R)
    (hweak : ∀ s : EuclideanSpace ℝ I, ‖s‖ ≤ 1 →
      ∀ t : EuclideanSpace ℝ J, ‖t‖ ≤ 1 →
        moment μ (2 * (q : ℝ)) (ThinMatrix.bilinear X s t) ≤ R)
    (c : I → κ → ℝ) (ν : I → κ → E → ℕ) (hc : ∀ i t, 0 ≤ c i t)
    (d : ℕ) (hdegree : ∀ i t, degree (ν i t) ≤ d) (hdq : d < q) :
    Integrable (fun ω => ‖action X T W c ν ω‖ ^ 2) μ ∧
      moment μ 2 (fun ω => ‖action X T W c ν ω‖) ≤
        ((2 : ℝ) * (5 : ℝ) ^ (1 / 4 : ℝ) * (B + 6 * α ^ 4 * R)) *
          (Real.sqrt 3 * α ^ 2) * moment μ 2 (fun ω => ‖polynomialVector W c ν ω‖) := by
  have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hp : (2 : ℝ) < 4 * (q : ℝ) := by linarith
  have hden : (0 : ℝ) < 4 * (q : ℝ) - 2 := by linarith
  have hr0 : 0 < 2 * (4 * (q : ℝ)) / (4 * (q : ℝ) - 2) := by positivity
  have hr4 : 2 * (4 * (q : ℝ)) / (4 * (q : ℝ) - 2) ≤ (4 : ℝ) := by
    apply (div_le_iff₀ hden).mpr
    linarith
  obtain ⟨hAint, hAbound⟩ := ThinTranspose.output_cols_moment_four_mul_le
    X hX hindX hsymX hintX α hα hregularX q hq T hthin B hB hcol R hR hweak
  have hAmem : MemLp
      (fun ω => ‖ThinMatrix.transposeOperator (fun i (j : T) => X i j) ω‖)
      (ENNReal.ofReal (4 * (q : ℝ))) μ := by
    have h := MomentTools.memLp_of_integrable_even_pow
      (fun ω => ‖ThinMatrix.transposeOperator (fun i (j : T) => X i j) ω‖)
      (ThinMatrix.measurable_norm_transposeOperator (fun i (j : T) => X i j)
        (fun i j => hX i j)).aestronglyMeasurable
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
    (ThinMatrix.transposeOperator (fun i (j : T) => X i j)) (polynomialVector W c ν)
    (4 * (q : ℝ)) hp hAmem hFmem
    (measurable_action X hX T W hW c ν).norm.aestronglyMeasurable
  refine ⟨hactint, hactbound.trans ?_⟩
  have hgain := mul_le_mul hAbound hFbound
    (MomentTools.nonneg (μ := μ) _ (fun ω => ‖polynomialVector W c ν ω‖))
    (le_trans (MomentTools.nonneg (μ := μ) _
      (fun ω => ‖ThinMatrix.transposeOperator (fun i (j : T) => X i j) ω‖)) hAbound)
  simpa only [mul_assoc] using hgain

/-- In the original-entry specialization the sole random coordinates are the
original ordered pairs. Entries outside `T` remain available to the polynomial. -/
theorem same_entries_action_l2_le
    (X : I → J → Ω → ℝ) (hX : ∀ i j, Measurable (X i j))
    (hind : iIndepFun (fun e : I × J => X e.1 e.2) μ)
    (hsym : ∀ i j, IdentDistrib (X i j) (fun ω => -X i j ω) μ μ)
    (hint : ∀ i j (p : ℝ), 0 < p → Integrable (fun ω => |X i j ω| ^ p) μ)
    (α : ℝ) (hα : 1 ≤ α)
    (hregular : ∀ i j (r : ℝ), 1 ≤ r →
      moment μ (2 * r) (X i j) ≤ α * moment μ r (X i j))
    (q : ℕ) (hq : 1 ≤ q) (T : Finset J) (hthin : T.card ≤ q)
    (B : ℝ) (hB : 0 ≤ B)
    (hcol : ∀ j, (∑ i, ∫ ω, X i j ω ^ 2 ∂μ) ≤ B ^ 2)
    (R : ℝ) (hR : 0 ≤ R)
    (hweak : ∀ s : EuclideanSpace ℝ I, ‖s‖ ≤ 1 →
      ∀ t : EuclideanSpace ℝ J, ‖t‖ ≤ 1 →
        moment μ (2 * (q : ℝ)) (ThinMatrix.bilinear X s t) ≤ R)
    (c : I → κ → ℝ) (ν : I → κ → I × J → ℕ) (hc : ∀ i t, 0 ≤ c i t)
    (d : ℕ) (hdegree : ∀ i t, degree (ν i t) ≤ d) (hdq : d < q) :
    Integrable (fun ω => ‖action X T (fun e : I × J => X e.1 e.2) c ν ω‖ ^ 2) μ ∧
      moment μ 2 (fun ω => ‖action X T (fun e : I × J => X e.1 e.2) c ν ω‖) ≤
        ((2 : ℝ) * (5 : ℝ) ^ (1 / 4 : ℝ) * (B + 6 * α ^ 4 * R)) *
          (Real.sqrt 3 * α ^ 2) *
            moment μ 2 (fun ω => ‖polynomialVector (fun e : I × J => X e.1 e.2) c ν ω‖) :=
  action_l2_le X hX hind hsym hint (fun e : I × J => X e.1 e.2)
    (fun e => hX e.1 e.2) hind (fun e => hsym e.1 e.2) (fun e => hint e.1 e.2)
    α hα hregular (fun e => hregular e.1 e.2) q hq T hthin B hB hcol R hR hweak
    c ν hc d hdegree hdq

end MI32.OutputPolynomialInteraction
