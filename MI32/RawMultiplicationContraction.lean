import MI32.RawCreatorContraction
import MI32.RawAnnihilatorContraction

/-!
# Full original matrix multiplication on the positive polynomial cone

The actual transpose action is the sum of the exact raw creator and raw
annihilator. Their proved full contractions and the genuine L2 triangle
inequality give one complete multiplication step. Every coefficient,
original variable and raw exponent belongs to the same original matrix;
no directional or sector estimate is assumed by the final theorem.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace MI32.RawMultiplicationContraction

open PositivePolynomial PositiveWordExtension RawDirectionalActions
open SymmetricPositiveCone ThinPolynomialInteraction

variable {Ω R C K : Type*} [Fintype R] [Fintype C] [Fintype K]
    [DecidableEq R] [DecidableEq C]

/-- The actual operator action equals the sum of its two original raw
directional polynomials, as a vector identity for every sample. -/
theorem action_eq_creation_add_annihilation
    (X : R → C → Ω → ℝ) (c : R → K → ℝ) (ν : R → K → R × C → ℕ) (ω : Ω) :
    action X (fun e : R × C => X e.1 e.2) c ν ω =
      evaluateHilbert (creationCoeff c ν) (actionExponent ν) (fun e => X e.1 e.2 ω) +
        evaluateHilbert (annihilationCoeff c ν) (actionExponent ν) (fun e => X e.1 e.2 ω) := by
  calc
    _ = evaluateHilbert (extendCoeff (fun _ _ => 1) c) (actionExponent ν)
        (fun e => X e.1 e.2 ω) :=
      (MaskedPolynomialAction.evaluateHilbert_extend_eq_action
        (fun e : R × C => X e.1 e.2) Prod.mk c ν ω).symm
    _ = _ := by
      ext j
      change evaluate (extendCoeff (fun _ _ => 1) c j) (actionExponent ν j)
        (fun e => X e.1 e.2 ω) =
        evaluate (creationCoeff c ν j) (actionExponent ν j) (fun e => X e.1 e.2 ω) +
          evaluate (annihilationCoeff c ν j) (actionExponent ν j) (fun e => X e.1 e.2 ω)
      exact (evaluate_extend_original_entries Prod.mk c ν j (fun e => X e.1 e.2 ω)).trans
        (evaluate_product_split c ν j (fun e => X e.1 e.2 ω))

/-- The sum of the row and column directional constants under a common budget. -/
def contractionConstant (α B W : ℝ) : ℝ :=
  (2 : ℝ) * ((2 : ℝ) * (5 : ℝ) ^ (1 / 4 : ℝ) * (B + 6 * α ^ 4 * W)) *
    (Real.sqrt 3 * α ^ 2)

section Measure

variable [MeasurableSpace Ω] {μ : Measure Ω}

/-- Actual L2 triangle for vector-valued random functions, with sum
integrability derived from the two original squared-norm integrals. -/
theorem vector_sum_l2_le {V : Type*} [NormedAddCommGroup V]
    (f g : Ω → V) (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hfi : Integrable (fun ω => ‖f ω‖ ^ 2) μ)
    (hgi : Integrable (fun ω => ‖g ω‖ ^ 2) μ) :
    Integrable (fun ω => ‖f ω + g ω‖ ^ 2) μ ∧
      moment μ 2 (fun ω => ‖f ω + g ω‖) ≤
        moment μ 2 (fun ω => ‖f ω‖) + moment μ 2 (fun ω => ‖g ω‖) := by
  have hfn : MemLp (fun ω => ‖f ω‖) 2 μ :=
    MomentTools.memLp_of_integrable_even_pow _ hf.norm 2 (by omega) (by decide) hfi
  have hgn : MemLp (fun ω => ‖g ω‖) 2 μ :=
    MomentTools.memLp_of_integrable_even_pow _ hg.norm 2 (by omega) (by decide) hgi
  have hfm : MemLp f 2 μ := (memLp_norm_iff hf).mp hfn
  have hgm : MemLp g 2 μ := (memLp_norm_iff hg).mp hgn
  have hsum : MemLp (f + g) 2 μ := hfm.add hgm
  refine ⟨hsum.norm.integrable_sq, ?_⟩
  change moment μ 2 (fun ω => ‖(f + g) ω‖) ≤
    moment μ 2 (fun ω => ‖f ω‖) + moment μ 2 (fun ω => ‖g ω‖)
  rw [MomentTools.eq_lpNorm 2 (by norm_num) _ hsum.norm.aestronglyMeasurable,
    MomentTools.eq_lpNorm 2 (by norm_num) _ hf.norm,
    MomentTools.eq_lpNorm 2 (by norm_num) _ hg.norm]
  simp only [ENNReal.ofReal_ofNat, lpNorm_norm (hf.add hg), lpNorm_norm hf, lpNorm_norm hg]
  exact lpNorm_add_le hfm (by norm_num)

variable [IsProbabilityMeasure μ]

/-- One full original-law matrix multiplication on the positive raw cone.
The original row and column variance budgets and deterministic weak tests
give the complete bound; all directional comparisons and integrability are proved. -/
theorem action_l2_le
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
    (hcol : ∀ j, (∑ i, ∫ ω, X i j ω ^ 2 ∂μ) ≤ B ^ 2)
    (W : ℝ) (hW : 0 ≤ W)
    (hweak : ∀ s : EuclideanSpace ℝ R, ‖s‖ ≤ 1 →
      ∀ t : EuclideanSpace ℝ C, ‖t‖ ≤ 1 →
        moment μ (2 * (q : ℝ)) (ThinMatrix.bilinear X s t) ≤ W)
    (c : R → K → ℝ) (ν : R → K → R × C → ℕ) (hc : ∀ i t, 0 ≤ c i t)
    (d : ℕ) (hdegree : ∀ i t, degree (ν i t) ≤ d) (hdq : d < q) :
    Integrable (fun ω => ‖action X (fun e : R × C => X e.1 e.2) c ν ω‖ ^ 2) μ ∧
      moment μ 2 (fun ω => ‖action X (fun e : R × C => X e.1 e.2) c ν ω‖) ≤
        contractionConstant α B W *
          moment μ 2 (fun ω => ‖polynomialVector (fun e : R × C => X e.1 e.2) c ν ω‖) := by
  obtain ⟨hcint, hcbound⟩ := RawCreatorContraction.creator_l2_le
    X hX hind hsym hint α hα hregular q hq B hB hrow W hW hweak c ν hc d hdegree hdq
  obtain ⟨haint, habound⟩ := RawAnnihilatorContraction.annihilator_l2_le
    X hX hind hsym hint α hα hregular q hq B hB hcol W hW hweak c ν hc d hdegree hdq
  have hcmeas : Measurable (fun ω =>
      evaluateHilbert (creationCoeff c ν) (actionExponent ν) (fun e => X e.1 e.2 ω)) :=
    measurable_polynomialVector (fun e : R × C => X e.1 e.2) (fun e => hX e.1 e.2)
      (creationCoeff c ν) (actionExponent ν)
  have hameas : Measurable (fun ω =>
      evaluateHilbert (annihilationCoeff c ν) (actionExponent ν) (fun e => X e.1 e.2 ω)) :=
    measurable_polynomialVector (fun e : R × C => X e.1 e.2) (fun e => hX e.1 e.2)
      (annihilationCoeff c ν) (actionExponent ν)
  obtain ⟨hsumint, hsumbound⟩ := vector_sum_l2_le _ _
    hcmeas.aestronglyMeasurable hameas.aestronglyMeasurable hcint haint
  simp_rw [action_eq_creation_add_annihilation]
  refine ⟨hsumint, hsumbound.trans ?_⟩
  calc
    _ ≤ RawCreatorContraction.contractionConstant α B W *
        moment μ 2 (fun ω => ‖evaluateHilbert c ν (fun e => X e.1 e.2 ω)‖) +
        RawAnnihilatorContraction.contractionConstant α B W *
        moment μ 2 (fun ω => ‖evaluateHilbert c ν (fun e => X e.1 e.2 ω)‖) :=
      add_le_add hcbound habound
    _ = _ := by
      unfold contractionConstant RawCreatorContraction.contractionConstant
        RawAnnihilatorContraction.contractionConstant polynomialVector
      ring

end Measure
end MI32.RawMultiplicationContraction
