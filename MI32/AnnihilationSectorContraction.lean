import MI32.ActiveCountSectors
import MI32.MaskedPolynomialAction
import MI32.OutputPolynomialInteraction

/-!
# Direct annihilation count-sector contraction

The input mask retains all original rows and raw exponents. Its original
column-count label determines the selected output columns. The annihilation
output projection is applied after literal multiplication by the original
entries, and contracts L2. A label with more than `q` active columns has
identically zero masked input when the input parity grade is at most `q`.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace MI32.AnnihilationSectorContraction

open PositivePolynomial PolynomialSectorMasks ActiveCountSectors ParityGeometry
open SymmetricPositiveCone ThinPolynomialInteraction

variable {Ω R C K : Type*} [MeasurableSpace Ω]
    [Fintype R] [Fintype C] [Fintype K] [DecidableEq R] [DecidableEq C]
    {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The complete original-row polynomial coefficient array of an input sector. -/
def inputCoeff (k : ℕ) (δ : C → ℕ) (c : R → K → ℝ)
    (ν : R → K → R × C → ℕ) : R → K → ℝ :=
  maskCoeff (annihilationMask k δ) c ν

/-- Grade drops by one and the current output column restores the input count. -/
def outputMask (k : ℕ) (δ : C → ℕ) (j : support δ) (S : Finset (R × C)) : Prop :=
  S.card + 1 = k ∧ annihilationLabel (j : C) S = δ

/-- Actual multiplication and output parity projection in the original variables. -/
def sectorAction (X : R → C → Ω → ℝ) (k : ℕ) (δ : C → ℕ)
    (c : R → K → ℝ) (ν : R → K → R × C → ℕ) (ω : Ω) :
    EuclideanSpace ℝ (support δ) :=
  MaskedPolynomialAction.maskedAction (fun e : R × C => X e.1 e.2)
    (fun i (j : support δ) => (i, (j : C))) (outputMask k δ) (inputCoeff k δ c ν) ν ω

omit [MeasurableSpace Ω] [Fintype K] [DecidableEq R] [IsProbabilityMeasure μ] in
/-- An impossible active-column budget forces every original raw coefficient to zero. -/
theorem inputCoeff_eq_zero_of_support_card_gt (k q : ℕ) (hkq : k ≤ q)
    (δ : C → ℕ) (hthick : q < (support δ).card)
    (c : R → K → ℝ) (ν : R → K → R × C → ℕ) :
    inputCoeff k δ c ν = fun _ _ => 0 := by
  funext i t
  by_contra hn
  have h := annihilation_support_card_le_of_coeff_ne_zero k δ c ν i t hn
  omega

omit [MeasurableSpace Ω] [DecidableEq R] [IsProbabilityMeasure μ] in
/-- Vanishing masked coefficients imply pointwise vanishing of the original input polynomial. -/
theorem input_polynomial_eq_zero (X : R → C → Ω → ℝ)
    (k : ℕ) (δ : C → ℕ) (c : R → K → ℝ) (ν : R → K → R × C → ℕ)
    (hc : inputCoeff k δ c ν = fun _ _ => 0) (ω : Ω) :
    polynomialVector (fun e : R × C => X e.1 e.2) (inputCoeff k δ c ν) ν ω = 0 := by
  rw [hc]
  ext i
  simp [polynomialVector, evaluateHilbert, evaluate]

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
/-- The raw projected action also vanishes pointwise for an impossible sector. -/
theorem sectorAction_eq_zero (X : R → C → Ω → ℝ)
    (k : ℕ) (δ : C → ℕ) (c : R → K → ℝ) (ν : R → K → R × C → ℕ)
    (hc : inputCoeff k δ c ν = fun _ _ => 0) (ω : Ω) :
    sectorAction X k δ c ν ω = 0 := by
  unfold sectorAction MaskedPolynomialAction.maskedAction
  rw [hc]
  ext j
  simp [evaluateHilbert, evaluate, maskCoeff, PositiveWordExtension.extendCoeff]

/-- Direct annihilation of one original count sector. The thin support budget
is derived from the masked input grade; no restricted law or weak-test premise
is assumed. All raw variables and the full original input axis survive. -/
theorem sectorAction_l2_le
    (X : R → C → Ω → ℝ) (hX : ∀ i j, Measurable (X i j))
    (hind : iIndepFun (fun e : R × C => X e.1 e.2) μ)
    (hsym : ∀ i j, IdentDistrib (X i j) (fun ω => -X i j ω) μ μ)
    (hint : ∀ i j (p : ℝ), 0 < p → Integrable (fun ω => |X i j ω| ^ p) μ)
    (α : ℝ) (hα : 1 ≤ α)
    (hregular : ∀ i j (r : ℝ), 1 ≤ r →
      moment μ (2 * r) (X i j) ≤ α * moment μ r (X i j))
    (q : ℕ) (hq : 1 ≤ q) (k : ℕ) (hkq : k ≤ q) (δ : C → ℕ)
    (B : ℝ) (hB : 0 ≤ B)
    (hcol : ∀ j, (∑ i, ∫ ω, X i j ω ^ 2 ∂μ) ≤ B ^ 2)
    (W : ℝ) (hW : 0 ≤ W)
    (hweak : ∀ s : EuclideanSpace ℝ R, ‖s‖ ≤ 1 →
      ∀ t : EuclideanSpace ℝ C, ‖t‖ ≤ 1 →
        moment μ (2 * (q : ℝ)) (ThinMatrix.bilinear X s t) ≤ W)
    (c : R → K → ℝ) (ν : R → K → R × C → ℕ) (hc : ∀ i t, 0 ≤ c i t)
    (d : ℕ) (hdegree : ∀ i t, degree (ν i t) ≤ d) (hdq : d < q) :
    Integrable (fun ω => ‖sectorAction X k δ c ν ω‖ ^ 2) μ ∧
      moment μ 2 (fun ω => ‖sectorAction X k δ c ν ω‖) ≤
        ((2 : ℝ) * (5 : ℝ) ^ (1 / 4 : ℝ) * (B + 6 * α ^ 4 * W)) *
          (Real.sqrt 3 * α ^ 2) *
            moment μ 2 (fun ω =>
              ‖polynomialVector (fun e : R × C => X e.1 e.2) (inputCoeff k δ c ν) ν ω‖) := by
  obtain ⟨hprojint, hproj⟩ := MaskedPolynomialAction.maskedAction_moment_le
    (fun e : R × C => X e.1 e.2) (fun e => hX e.1 e.2) hind
    (fun e => hsym e.1 e.2) (fun e => hint e.1 e.2)
    (fun i (j : support δ) => (i, (j : C))) (outputMask k δ) (inputCoeff k δ c ν) ν
  refine ⟨hprojint, ?_⟩
  by_cases hthin : (support δ).card ≤ q
  · have hcin : ∀ i t, 0 ≤ inputCoeff k δ c ν i t :=
      maskCoeff_nonneg (annihilationMask k δ) c ν hc
    have hact := OutputPolynomialInteraction.same_entries_action_l2_le
      X hX hind hsym hint α hα hregular q hq (support δ) hthin
      B hB hcol W hW hweak (inputCoeff k δ c ν) ν hcin d hdegree hdq
    exact hproj.trans hact.2
  · have hzero := inputCoeff_eq_zero_of_support_card_gt k q hkq δ
      (Nat.lt_of_not_ge hthin) c ν
    have hin := input_polynomial_eq_zero X k δ c ν hzero
    have hout := sectorAction_eq_zero X k δ c ν hzero
    simp only [hout, hin, norm_zero, moment, abs_zero, Real.zero_rpow (by norm_num : (2 : ℝ) ≠ 0),
      integral_zero, Real.zero_rpow (by norm_num : (1 / (2 : ℝ)) ≠ 0), mul_zero, le_refl]

end MI32.AnnihilationSectorContraction
