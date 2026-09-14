import MI32.ActiveCountSectors
import MI32.MaskedPolynomialAction
import MI32.SupportedPolynomialInteraction
import MI32.StatementChecks

/-!
# An original-law creation-sector contraction

The input is selected by its exact original row-count label and parity grade.
The deterministic thin row set and its cardinality bound are derived from
that selection. The output is the next-grade, same-count projection of actual
matrix multiplication. All original exponents and magnitude spectators remain.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace MI32.CreationSectorContraction
open PositivePolynomial PolynomialSectorMasks ActiveCountSectors ParityGeometry
open SymmetricPositiveCone ThinPolynomialInteraction MaskedPolynomialAction

variable {Ω R C K : Type*} [MeasurableSpace Ω]
    [Fintype R] [Fintype C] [Fintype K] [DecidableEq R] [DecidableEq C]
    {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Original multiplication with the exact creation input and output masks. -/
def sectorAction (X : R → C → Ω → ℝ) (k : ℕ) (δ : R → ℕ)
    (c : R → K → ℝ) (ν : R → K → R × C → ℕ) (ω : Ω) : EuclideanSpace ℝ C :=
  maskedAction (fun e : R × C => X e.1 e.2) Prod.mk
    (fun _ S => S.card = k + 1 ∧ rowCount S = δ)
    (maskCoeff (creationMask k δ) c ν) ν ω

/-- Uniform creation-sector bound. No active-row cardinality, restricted law,
restricted norm estimate, or independence from the polynomial is assumed.
Empty sectors, including labels with too many positive coordinates, vanish. -/
theorem sectorAction_l2_le
    (X : R → C → Ω → ℝ) (hX : ∀ i j, Measurable (X i j))
    (hind : iIndepFun (fun e : R × C => X e.1 e.2) μ)
    (hsym : ∀ i j, IdentDistrib (X i j) (fun ω => -X i j ω) μ μ)
    (hint : ∀ i j (p : ℝ), 0 < p → Integrable (fun ω => |X i j ω| ^ p) μ)
    (α : ℝ) (hα : 1 ≤ α)
    (hregular : ∀ i j (r : ℝ), 1 ≤ r →
      moment μ (2 * r) (X i j) ≤ α * moment μ r (X i j))
    (q : ℕ) (hq : 1 ≤ q)
    (B : ℝ) (hB : 0 ≤ B)
    (hrow : ∀ i, (∑ j, ∫ ω, X i j ω ^ 2 ∂μ) ≤ B ^ 2)
    (W : ℝ) (hW : 0 ≤ W)
    (hweak : ∀ s : EuclideanSpace ℝ R, ‖s‖ ≤ 1 →
      ∀ t : EuclideanSpace ℝ C, ‖t‖ ≤ 1 →
        moment μ (2 * (q : ℝ)) (ThinMatrix.bilinear X s t) ≤ W)
    (c : R → K → ℝ) (ν : R → K → R × C → ℕ) (hc : ∀ i t, 0 ≤ c i t)
    (d : ℕ) (hdegree : ∀ i t, degree (ν i t) ≤ d) (hdq : d < q)
    (k : ℕ) (hkq : k < q) (δ : R → ℕ) :
    Integrable (fun ω => ‖sectorAction X k δ c ν ω‖ ^ 2) μ ∧
      moment μ 2 (fun ω => ‖sectorAction X k δ c ν ω‖) ≤
        ((2 : ℝ) * (5 : ℝ) ^ (1 / 4 : ℝ) * (B + 6 * α ^ 4 * W)) *
          (Real.sqrt 3 * α ^ 2) *
            moment μ 2 (fun ω => ‖polynomialVector (fun e : R × C => X e.1 e.2)
              (maskCoeff (creationMask k δ) c ν) ν ω‖) := by
  obtain ⟨hInt, hMask⟩ := maskedAction_moment_le
    (fun e : R × C => X e.1 e.2) (fun e => hX e.1 e.2) hind
    (fun e => hsym e.1 e.2) (fun e => hint e.1 e.2)
    Prod.mk (fun _ S => S.card = k + 1 ∧ rowCount S = δ)
    (maskCoeff (creationMask k δ) c ν) ν
  refine ⟨hInt, ?_⟩
  by_cases hthin : (support δ).card ≤ q
  · obtain ⟨_, hBound⟩ := SupportedPolynomialInteraction.action_l2_le
      X hX hind hsym hint α hα hregular q hq (support δ) hthin B hB hrow W hW hweak
      (maskCoeff (creationMask k δ) c ν) ν
      (maskCoeff_nonneg _ c ν hc) (creation_maskCoeff_eq_zero k δ c ν)
      d hdegree hdq
    exact hMask.trans hBound
  · have hz : maskCoeff (creationMask k δ) c ν = fun _ _ => 0 := by
      funext i t
      by_contra hn
      exact hthin ((creation_support_card_le_of_coeff_ne_zero k δ c ν i t hn).trans
        (by omega))
    have hInput (ω : Ω) : polynomialVector (fun e : R × C => X e.1 e.2)
        (maskCoeff (creationMask k δ) c ν) ν ω = 0 := by
      ext i
      simp [polynomialVector, evaluateHilbert, evaluate, hz]
    have hAction (ω : Ω) : action X (fun e : R × C => X e.1 e.2)
        (maskCoeff (creationMask k δ) c ν) ν ω = 0 := by
      simp [action, hInput]
    have hMask0 : moment μ 2 (fun ω => ‖sectorAction X k δ c ν ω‖) ≤ 0 := by
      simpa only [sectorAction, hAction, norm_zero,
        moment_zero μ (by norm_num : (0 : ℝ) < 2)] using hMask
    simpa only [hInput, norm_zero, moment_zero μ (by norm_num : (0 : ℝ) < 2), mul_zero]
      using hMask0

end MI32.CreationSectorContraction
