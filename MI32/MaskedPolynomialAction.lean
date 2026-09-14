import MI32.PositiveWordExtension
import MI32.PolynomialSectorEnergy
import MI32.ThinPolynomialInteraction

/-!
# An actual matrix action followed by a raw parity projection

The output projection contracts the original-law L2 moment. It is implemented
by discarding raw terms after the exact original-variable multiplication;
there is no assertion that Walsh transformation preserves any other Lp norm.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace MI32.MaskedPolynomialAction
open PositivePolynomial PositiveWordExtension PolynomialSectorMasks
open SymmetricPositiveCone ThinPolynomialInteraction

variable {Ω E I J K : Type*} [MeasurableSpace Ω]
    [Fintype E] [Fintype I] [Fintype J] [Fintype K]
    [DecidableEq E] [DecidableEq I] [DecidableEq J]
    {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [MeasurableSpace Ω] [DecidableEq J] in
/-- Exact raw representation of an original-entry matrix action. -/
theorem evaluateHilbert_extend_eq_action
    (W : E → Ω → ℝ) (edge : I → J → E)
    (c : I → K → ℝ) (ν : I → K → E → ℕ) (ω : Ω) :
    evaluateHilbert (extendCoeff (fun _ _ => 1) c) (extendExponent edge ν)
        (fun e => W e ω) =
      action (fun i j => W (edge i j)) W c ν ω := by
  rw [action, ThinMatrix.transposeOperator_apply]
  ext j
  change evaluate (extendCoeff (fun _ _ => 1) c j) (extendExponent edge ν j)
      (fun e => W e ω) = ∑ i, evaluate (c i) (ν i) (fun e => W e ω) * W (edge i j) ω
  rw [evaluate_extend_original_entries]
  apply Finset.sum_congr rfl
  intro i hi
  exact mul_comm _ _

/-- Keep specified output coordinates and parities after actual multiplication. -/
def maskedAction (W : E → Ω → ℝ) (edge : I → J → E)
    (P : J → Finset E → Prop) (c : I → K → ℝ) (ν : I → K → E → ℕ)
    (ω : Ω) : EuclideanSpace ℝ J :=
  evaluateHilbert
    (maskCoeff P (extendCoeff (fun _ _ => 1) c) (extendExponent edge ν))
    (extendExponent edge ν) (fun e => W e ω)

omit [DecidableEq J] in
/-- The raw output mask is a contraction for the actual original-law action.
Coefficients may be signed; integrability is derived from entry moments. -/
theorem maskedAction_moment_le
    (W : E → Ω → ℝ) (hW : ∀ e, Measurable (W e)) (hind : iIndepFun W μ)
    (hsym : ∀ e, IdentDistrib (W e) (fun ω => -W e ω) μ μ)
    (hint : ∀ e (p : ℝ), 0 < p → Integrable (fun ω => |W e ω| ^ p) μ)
    (edge : I → J → E) (P : J → Finset E → Prop)
    (c : I → K → ℝ) (ν : I → K → E → ℕ) :
    Integrable (fun ω => ‖maskedAction W edge P c ν ω‖ ^ 2) μ ∧
      moment μ 2 (fun ω => ‖maskedAction W edge P c ν ω‖) ≤
        moment μ 2 (fun ω => ‖action (fun i j => W (edge i j)) W c ν ω‖) := by
  refine ⟨PolynomialSectorEnergy.integrable_original_norm_sq W hW hind hint _ _, ?_⟩
  have h := PolynomialSectorEnergy.masked_second_energy_le W hW hind hsym hint P
    (extendCoeff (fun _ _ => 1) c) (extendExponent edge ν)
  simp only [evaluateHilbert_extend_eq_action] at h
  exact MomentTools.even_moment_mono_of_integral_le _ _ 2 (by omega)
    (by exact ⟨1, rfl⟩) h

end MI32.MaskedPolynomialAction
