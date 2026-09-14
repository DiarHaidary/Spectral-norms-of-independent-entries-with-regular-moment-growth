import MI32.ThinPolynomialInteraction
import MI32.RestrictedThinMatrix

/-!
# Full original-matrix action on a polynomial supported on thin rows

Only the output coordinates of the input polynomial are restricted. Every
raw exponent still refers to the full original matrix-entry family, including
all spectators outside the deterministic row set. Zero extension gives exact
action and Euclidean norm identities; the resulting comparison requires no
restricted independence, restricted weak test, or operator norm premise.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace MI32.SupportedPolynomialInteraction

open PositivePolynomial SymmetricPositiveCone ThinPolynomialInteraction

variable {Ω R C E K : Type*} [Fintype R] [Fintype C] [Fintype E] [Fintype K]
    [DecidableEq R] [DecidableEq C] [DecidableEq E]

omit [Fintype R] [DecidableEq E] in
/-- Restricting the polynomial's output coordinates and then extending by zero
recovers exactly the original polynomial. All original exponents are unchanged. -/
theorem zeroExtend_evaluateHilbert (c : R → K → ℝ) (ν : R → K → E → ℕ)
    (S : Finset R) (hsupport : ∀ i, i ∉ S → ∀ k, c i k = 0) (z : E → ℝ) :
    AxisRestriction.zeroExtend S
        (evaluateHilbert (fun i : S => c i) (fun i : S => ν i) z) =
      evaluateHilbert c ν z := by
  ext i
  by_cases hi : i ∈ S
  · rw [AxisRestriction.zeroExtend_apply_mem S _ i hi]
    rfl
  · rw [AxisRestriction.zeroExtend_apply_not_mem S _ i hi]
    change 0 = evaluate (c i) (ν i) z
    simp [evaluate, hsupport i hi]

omit [DecidableEq E] in
/-- Euclidean norm is unchanged by the supported-coordinate restriction. -/
theorem norm_evaluateHilbert_restrict (c : R → K → ℝ) (ν : R → K → E → ℕ)
    (S : Finset R) (hsupport : ∀ i, i ∉ S → ∀ k, c i k = 0) (z : E → ℝ) :
    ‖evaluateHilbert (fun i : S => c i) (fun i : S => ν i) z‖ =
      ‖evaluateHilbert c ν z‖ := by
  simpa only [AxisRestriction.norm_zeroExtend] using
    congrArg norm (zeroExtend_evaluateHilbert c ν S hsupport z)

omit [DecidableEq E] in
/-- The actual original-variable polynomial norm is preserved sample by sample. -/
theorem norm_polynomialVector_restrict (U : E → Ω → ℝ)
    (c : R → K → ℝ) (ν : R → K → E → ℕ)
    (S : Finset R) (hsupport : ∀ i, i ∉ S → ∀ k, c i k = 0) (ω : Ω) :
    ‖polynomialVector U (fun i : S => c i) (fun i : S => ν i) ω‖ =
      ‖polynomialVector U c ν ω‖ :=
  norm_evaluateHilbert_restrict c ν S hsupport (fun e => U e ω)

omit [DecidableEq C] [DecidableEq E] in
/-- The restricted operator acting on the restricted polynomial is literally
the full original operator acting on the original supported polynomial. -/
theorem action_restrict_rows (X : R → C → Ω → ℝ) (U : E → Ω → ℝ)
    (c : R → K → ℝ) (ν : R → K → E → ℕ)
    (S : Finset R) (hsupport : ∀ i, i ∉ S → ∀ k, c i k = 0) (ω : Ω) :
    action (fun i : S => X i) U (fun i : S => c i) (fun i : S => ν i) ω =
      action X U c ν ω := by
  unfold action polynomialVector
  rw [AxisRestriction.transposeOperator_restrict_rows]
  change ThinMatrix.transposeOperator X ω
      (AxisRestriction.zeroExtend S
        (evaluateHilbert (fun i : S => c i) (fun i : S => ν i) (fun e => U e ω))) = _
  rw [zeroExtend_evaluateHilbert c ν S hsupport]

section Probability

variable [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- A polynomial supported on at most `q` original rows satisfies the thin
interaction estimate for the full original matrix action. The polynomial
continues to depend on all original `R × C` variables, with degree below `q`.
Every distributional and weak-moment hypothesis refers to the original matrix.
The action's squared norm integrability is derived as part of the conclusion. -/
theorem action_l2_le
    (X : R → C → Ω → ℝ) (hX : ∀ i j, Measurable (X i j))
    (hind : iIndepFun (fun e : R × C => X e.1 e.2) μ)
    (hsym : ∀ i j, IdentDistrib (X i j) (fun ω => -X i j ω) μ μ)
    (hint : ∀ i j (p : ℝ), 0 < p → Integrable (fun ω => |X i j ω| ^ p) μ)
    (α : ℝ) (hα : 1 ≤ α)
    (hregular : ∀ i j (r : ℝ), 1 ≤ r →
      moment μ (2 * r) (X i j) ≤ α * moment μ r (X i j))
    (q : ℕ) (hq : 1 ≤ q) (S : Finset R) (hthin : S.card ≤ q)
    (B : ℝ) (hB : 0 ≤ B)
    (hrow : ∀ i, (∑ j, ∫ ω, X i j ω ^ 2 ∂μ) ≤ B ^ 2)
    (W : ℝ) (hW : 0 ≤ W)
    (hweak : ∀ s : EuclideanSpace ℝ R, ‖s‖ ≤ 1 →
      ∀ t : EuclideanSpace ℝ C, ‖t‖ ≤ 1 →
        moment μ (2 * (q : ℝ)) (ThinMatrix.bilinear X s t) ≤ W)
    (c : R → K → ℝ) (ν : R → K → R × C → ℕ)
    (hc : ∀ i k, 0 ≤ c i k) (hsupport : ∀ i, i ∉ S → ∀ k, c i k = 0)
    (d : ℕ) (hdegree : ∀ i k, degree (ν i k) ≤ d) (hdq : d < q) :
    Integrable (fun ω => ‖action X (fun e : R × C => X e.1 e.2) c ν ω‖ ^ 2) μ ∧
      moment μ 2 (fun ω => ‖action X (fun e : R × C => X e.1 e.2) c ν ω‖) ≤
        ((2 : ℝ) * (5 : ℝ) ^ (1 / 4 : ℝ) * (B + 6 * α ^ 4 * W)) *
          (Real.sqrt 3 * α ^ 2) *
            moment μ 2 (fun ω => ‖polynomialVector (fun e : R × C => X e.1 e.2) c ν ω‖) := by
  have h := ThinPolynomialInteraction.action_l2_le
    (fun i : S => X i) (fun i j => hX i j)
    (RestrictedThinMatrix.independent_restrict_rows X hind S)
    (fun i j => hsym i j) (fun i j p hp => hint i j p hp)
    (fun e : R × C => X e.1 e.2) (fun e => hX e.1 e.2) hind
    (fun e => hsym e.1 e.2) (fun e => hint e.1 e.2)
    α hα (fun i j r hr => hregular i j r hr) (fun e => hregular e.1 e.2)
    q hq (by simpa only [Fintype.card_coe] using hthin) B hB (fun i => hrow i) W hW
    (AxisRestriction.thin_weak_test_restrict_rows μ (2 * (q : ℝ)) W X hweak S)
    (fun i : S => c i) (fun i : S => ν i) (fun i k => hc i k)
    d (fun i k => hdegree i k) hdq
  simpa only [action_restrict_rows X _ c ν S hsupport,
    norm_polynomialVector_restrict _ c ν S hsupport] using h

end Probability

end MI32.SupportedPolynomialInteraction
