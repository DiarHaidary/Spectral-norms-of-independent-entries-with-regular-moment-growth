import MI32.RawSectorNorms
import MI32.PolynomialEnergyAssembly

/-!
# Full original-law raw annihilator contraction

Exact column-count sectors assemble without a sector-count loss. Every
sector estimate is derived from original matrix hypotheses. Sectors above
the raw degree vanish coefficient by coefficient, and all original rows,
columns and variables remain in the resulting full annihilator polynomial.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace MI32.RawAnnihilatorContraction

open PositivePolynomial PolynomialSectorMasks ActiveCountSectors ParityGeometry
open RawParity RawDirectionalActions RawCountBlocks SymmetricPositiveCone

variable {Ω R C K : Type*} [MeasurableSpace Ω]
    [Fintype R] [Fintype C] [Fintype K] [DecidableEq R] [DecidableEq C]
    {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Original input parity grade and original column count. -/
def inputLabel (_i : R) (S : Finset (R × C)) : ℕ × (C → ℕ) :=
  (S.card, colCount S)

/-- The output grade and count label restore the removed current-column flag. -/
def outputLabel (j : C) (S : Finset (R × C)) : ℕ × (C → ℕ) :=
  (S.card + 1, annihilationLabel j S)

/-- The constant from the thin output restriction and positive-cone interpolation. -/
def contractionConstant (α B W : ℝ) : ℝ :=
  ((2 : ℝ) * (5 : ℝ) ^ (1 / 4 : ℝ) * (B + 6 * α ^ 4 * W)) *
    (Real.sqrt 3 * α ^ 2)

omit [MeasurableSpace Ω] [Fintype K] [DecidableEq R] [IsProbabilityMeasure μ] in
/-- A parity sector above the original raw degree has no surviving coefficient. -/
theorem input_mask_eq_zero_of_degree_lt
    (c : R → K → ℝ) (ν : R → K → R × C → ℕ)
    (d k : ℕ) (hdegree : ∀ i t, degree (ν i t) ≤ d) (hdk : d < k) (δ : C → ℕ) :
    maskCoeff (annihilationMask k δ) c ν = fun _ _ => 0 := by
  classical
  funext i t
  have hn : ¬ annihilationMask k δ i (parity (ν i t)) := by
    intro hm
    have hpar := parity_card_le_degree (ν i t)
    have hdeg := hdegree i t
    have hgrade := hm.1
    omega
  exact if_neg hn

/-- The complete raw annihilator obeys the uniform L2 comparison. All sector
premises are discharged, and no restricted law or support estimate is assumed. -/
theorem annihilator_l2_le
    (X : R → C → Ω → ℝ) (hX : ∀ i j, Measurable (X i j))
    (hind : iIndepFun (fun e : R × C => X e.1 e.2) μ)
    (hsym : ∀ i j, IdentDistrib (X i j) (fun ω => -X i j ω) μ μ)
    (hint : ∀ i j (p : ℝ), 0 < p → Integrable (fun ω => |X i j ω| ^ p) μ)
    (α : ℝ) (hα : 1 ≤ α)
    (hregular : ∀ i j (r : ℝ), 1 ≤ r →
      moment μ (2 * r) (X i j) ≤ α * moment μ r (X i j))
    (q : ℕ) (hq : 1 ≤ q)
    (B : ℝ) (hB : 0 ≤ B)
    (hcol : ∀ j, (∑ i, ∫ ω, X i j ω ^ 2 ∂μ) ≤ B ^ 2)
    (W : ℝ) (hW : 0 ≤ W)
    (hweak : ∀ s : EuclideanSpace ℝ R, ‖s‖ ≤ 1 →
      ∀ t : EuclideanSpace ℝ C, ‖t‖ ≤ 1 →
        moment μ (2 * (q : ℝ)) (ThinMatrix.bilinear X s t) ≤ W)
    (c : R → K → ℝ) (ν : R → K → R × C → ℕ) (hc : ∀ i t, 0 ≤ c i t)
    (d : ℕ) (hdegree : ∀ i t, degree (ν i t) ≤ d) (hdq : d < q) :
    Integrable (fun ω =>
      ‖evaluateHilbert (annihilationCoeff c ν) (actionExponent ν) (fun e => X e.1 e.2 ω)‖ ^ 2) μ ∧
      moment μ 2 (fun ω =>
        ‖evaluateHilbert (annihilationCoeff c ν) (actionExponent ν) (fun e => X e.1 e.2 ω)‖) ≤
        contractionConstant α B W *
          moment μ 2 (fun ω => ‖evaluateHilbert c ν (fun e => X e.1 e.2 ω)‖) := by
  classical
  have hM : 0 ≤ contractionConstant α B W := by
    unfold contractionConstant
    positivity
  have hsector : ∀ label : ℕ × (C → ℕ),
      (∫ ω, ‖evaluateHilbert
        (maskCoeff (fun j S => outputLabel j S = label) (annihilationCoeff c ν) (actionExponent ν))
        (actionExponent ν) (fun e => X e.1 e.2 ω)‖ ^ 2 ∂μ) ≤
      contractionConstant α B W ^ 2 * ∫ ω, ‖evaluateHilbert
        (maskCoeff (fun i S => inputLabel i S = label) c ν) ν (fun e => X e.1 e.2 ω)‖ ^ 2 ∂μ := by
    rintro ⟨k, δ⟩
    simp only [inputLabel, outputLabel, Prod.mk.injEq]
    change (∫ ω, ‖evaluateHilbert
      (maskCoeff (annihilationOutputMask k δ) (annihilationCoeff c ν) (actionExponent ν))
      (actionExponent ν) (fun e => X e.1 e.2 ω)‖ ^ 2 ∂μ) ≤
      contractionConstant α B W ^ 2 * ∫ ω, ‖evaluateHilbert
        (maskCoeff (annihilationMask k δ) c ν) ν (fun e => X e.1 e.2 ω)‖ ^ 2 ∂μ
    rw [annihilation_count_block]
    by_cases hkq : k ≤ q
    · have hbound := AnnihilationSectorContraction.sectorAction_l2_le
        X hX hind hsym hint α hα hregular q hq k hkq δ B hB hcol W hW hweak
        c ν hc d hdegree hdq
      have hb : moment μ 2 (fun ω =>
          ‖evaluateHilbert (annihilationCoeff (maskCoeff (annihilationMask k δ) c ν) ν)
            (actionExponent ν) (fun e => X e.1 e.2 ω)‖) ≤
          contractionConstant α B W * moment μ 2 (fun ω =>
            ‖evaluateHilbert (maskCoeff (annihilationMask k δ) c ν) ν (fun e => X e.1 e.2 ω)‖) := by
        simpa only [RawSectorNorms.norm_raw_annihilation_eq_sectorAction,
          ThinPolynomialInteraction.polynomialVector, AnnihilationSectorContraction.inputCoeff,
          contractionConstant] using hbound.2
      have hsq := pow_le_pow_left₀ (MomentTools.nonneg (μ := μ) 2
        (fun ω => ‖evaluateHilbert
          (annihilationCoeff (maskCoeff (annihilationMask k δ) c ν) ν)
          (actionExponent ν) (fun e => X e.1 e.2 ω)‖)) hb 2
      have hout : moment μ 2 (fun ω => ‖evaluateHilbert
          (annihilationCoeff (maskCoeff (annihilationMask k δ) c ν) ν)
          (actionExponent ν) (fun e => X e.1 e.2 ω)‖) ^ 2 = ∫ ω,
          ‖evaluateHilbert (annihilationCoeff (maskCoeff (annihilationMask k δ) c ν) ν)
            (actionExponent ν) (fun e => X e.1 e.2 ω)‖ ^ 2 ∂μ := by
        simpa only [Nat.cast_ofNat, abs_of_nonneg (norm_nonneg _)] using
          moment_nat_pow μ (fun ω => ‖evaluateHilbert
            (annihilationCoeff (maskCoeff (annihilationMask k δ) c ν) ν)
            (actionExponent ν) (fun e => X e.1 e.2 ω)‖) 2 (by norm_num)
      have hin : moment μ 2 (fun ω =>
          ‖evaluateHilbert (maskCoeff (annihilationMask k δ) c ν) ν (fun e => X e.1 e.2 ω)‖) ^ 2 =
          ∫ ω, ‖evaluateHilbert (maskCoeff (annihilationMask k δ) c ν) ν
            (fun e => X e.1 e.2 ω)‖ ^ 2 ∂μ := by
        simpa only [Nat.cast_ofNat, abs_of_nonneg (norm_nonneg _)] using
          moment_nat_pow μ (fun ω => ‖evaluateHilbert (maskCoeff (annihilationMask k δ) c ν) ν
            (fun e => X e.1 e.2 ω)‖) 2 (by norm_num)
      rwa [mul_pow, hout, hin] at hsq
    · have hz := input_mask_eq_zero_of_degree_lt c ν d k hdegree (by omega) δ
      have hin (ω : Ω) :
          evaluateHilbert (maskCoeff (annihilationMask k δ) c ν) ν (fun e => X e.1 e.2 ω) = 0 := by
        ext i
        simp [evaluateHilbert, evaluate, hz]
      have hout (ω : Ω) : evaluateHilbert
          (annihilationCoeff (maskCoeff (annihilationMask k δ) c ν) ν)
          (actionExponent ν) (fun e => X e.1 e.2 ω) = 0 := by
        ext j
        simp [evaluateHilbert, evaluate, hz, annihilationCoeff]
      simp only [hin, hout, norm_zero, zero_pow (by omega : 2 ≠ 0), integral_zero,
        mul_zero, le_refl]
  refine ⟨PolynomialSectorEnergy.integrable_original_norm_sq
    (fun e : R × C => X e.1 e.2) (fun e => hX e.1 e.2) hind
    (fun e => hint e.1 e.2) (annihilationCoeff c ν) (actionExponent ν), ?_⟩
  exact PolynomialEnergyAssembly.second_moment_le_of_all_sectors
    (fun e : R × C => X e.1 e.2) (fun e => hX e.1 e.2) hind
    (fun e => hsym e.1 e.2) (fun e => hint e.1 e.2) c ν
    (annihilationCoeff c ν) (actionExponent ν) inputLabel outputLabel
    (contractionConstant α B W) hM hsector

end MI32.RawAnnihilatorContraction
