import MI32.PolynomialEnergyAssembly
import MI32.RawSectorNorms

/-!
# Full original-law raw creator contraction

The proof assembles the established original-law creation-sector contractions
using exact parity/count energy partitions. Every inaccessible input grade
and the zero output grade vanish by explicit raw coefficient identities.
No sector norm estimate, active-axis size, or independent-copy premise remains.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace MI32.RawCreatorContraction

open PositivePolynomial RawParity PolynomialSectorMasks ActiveCountSectors
open ParityGeometry RawDirectionalActions RawCountBlocks SymmetricPositiveCone
attribute [local instance] Classical.propDecidable

variable {Ω R C K : Type*} [Fintype R] [Fintype C] [Fintype K]
    [DecidableEq R] [DecidableEq C]

/-- The output grade is stored in both labels, aligning creation blocks. -/
def inputLabel (i : R) (S : Finset (R × C)) : ℕ × (R → ℕ) :=
  (S.card + 1, creationLabel i S)

def outputLabel (_j : C) (S : Finset (R × C)) : ℕ × (R → ℕ) :=
  (S.card, rowCount S)

/-- The completely explicit original-law one-step creator constant. -/
def contractionConstant (α B W : ℝ) : ℝ :=
  ((2 : ℝ) * (5 : ℝ) ^ (1 / 4 : ℝ) * (B + 6 * α ^ 4 * W)) *
    (Real.sqrt 3 * α ^ 2)

theorem contractionConstant_nonneg (α B W : ℝ) (hB : 0 ≤ B) (hW : 0 ≤ W) :
    0 ≤ contractionConstant α B W := by
  unfold contractionConstant
  positivity

omit [Fintype K] [DecidableEq C] in
theorem input_mask_succ (c : R → K → ℝ) (ν : R → K → R × C → ℕ)
    (k : ℕ) (δ : R → ℕ) :
    maskCoeff (fun i S => inputLabel i S = (k + 1, δ)) c ν =
      maskCoeff (creationMask k δ) c ν := by
  have h : (fun (i : R) (S : Finset (R × C)) => inputLabel i S = (k + 1, δ)) =
      creationMask k δ := by
    funext i S
    apply propext
    simp only [inputLabel, Prod.mk.injEq, Nat.add_left_inj, creationMask]
  rw [h]

omit [Fintype K] [DecidableEq C] in
theorem output_mask_succ (c : C → R × K → ℝ) (ν : C → R × K → R × C → ℕ)
    (k : ℕ) (δ : R → ℕ) :
    maskCoeff (fun j S => outputLabel j S = (k + 1, δ)) c ν =
      maskCoeff (creationOutputMask k δ) c ν := by
  have h : (fun (j : C) (S : Finset (R × C)) => outputLabel j S = (k + 1, δ)) =
      creationOutputMask k δ := by
    funext j S
    apply propext
    simp only [outputLabel, Prod.mk.injEq, creationOutputMask]
  rw [h]

omit [Fintype K] [DecidableEq C] in
/-- No input creation label has zero output grade. -/
theorem input_mask_zero (c : R → K → ℝ) (ν : R → K → R × C → ℕ)
    (δ : R → ℕ) :
    maskCoeff (fun i S => inputLabel i S = (0, δ)) c ν = fun _ _ => 0 := by
  classical
  funext i t
  simp [maskCoeff, inputLabel]

omit [Fintype K] in
/-- A creator cannot output empty parity: its appended original edge was absent. -/
theorem output_creation_mask_zero (c : R → K → ℝ) (ν : R → K → R × C → ℕ)
    (δ : R → ℕ) :
    maskCoeff (fun j S => outputLabel j S = (0, δ))
        (creationCoeff c ν) (actionExponent ν) = fun _ _ => 0 := by
  classical
  funext j t
  by_cases he : (t.1, j) ∉ parity (ν t.1 t.2)
  · have hg : (parity (actionExponent ν j t)).card ≠ 0 := by
      rw [parity_actionExponent, toggle, if_neg he, creation_grade _ _ _ he]
      omega
    simp only [maskCoeff, outputLabel, Prod.mk.injEq, hg, false_and, if_false]
  · simp only [maskCoeff, creationCoeff, if_neg he, ite_self]

omit [Fintype K] [DecidableEq C] in
/-- A parity grade above the original raw degree is absent coefficient by coefficient. -/
theorem creation_mask_zero_of_degree (c : R → K → ℝ) (ν : R → K → R × C → ℕ)
    (d : ℕ) (hdegree : ∀ i t, degree (ν i t) ≤ d)
    (k : ℕ) (hdk : d < k) (δ : R → ℕ) :
    maskCoeff (creationMask k δ) c ν = fun _ _ => 0 := by
  classical
  funext i t
  have hn : ¬ creationMask k δ i (parity (ν i t)) := by
    intro h
    have hp := parity_card_le_degree (ν i t)
    have hd := hdegree i t
    have hg := h.1
    omega
  exact if_neg hn

omit [Fintype K] in
theorem creationCoeff_zero (ν : R → K → R × C → ℕ) :
    creationCoeff (fun _ _ => 0) ν = fun _ _ => 0 := by
  funext j t
  simp only [creationCoeff, ite_self]

private theorem evaluateHilbert_zero {A H E : Type*} [Fintype A] [Fintype H] [Fintype E]
    (ν : A → H → E → ℕ) (z : E → ℝ) :
    evaluateHilbert (fun _ _ => 0) ν z = 0 := by
  ext a
  simp [evaluateHilbert, evaluate]

section Probability

variable [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
private theorem integral_sq_le_of_second_moment_le (f g : Ω → ℝ)
    (hf : ∀ ω, 0 ≤ f ω) (hg : ∀ ω, 0 ≤ g ω) (M : ℝ)
    (h : moment μ 2 f ≤ M * moment μ 2 g) :
    (∫ ω, f ω ^ 2 ∂μ) ≤ M ^ 2 * ∫ ω, g ω ^ 2 ∂μ := by
  have hs := pow_le_pow_left₀ (MomentTools.nonneg (μ := μ) 2 f) h 2
  have hf2 : moment μ 2 f ^ 2 = ∫ ω, f ω ^ 2 ∂μ := by
    simpa only [Nat.cast_ofNat, abs_of_nonneg (hf _)] using moment_nat_pow μ f 2 (by norm_num)
  have hg2 : moment μ 2 g ^ 2 = ∫ ω, g ω ^ 2 ∂μ := by
    simpa only [Nat.cast_ofNat, abs_of_nonneg (hg _)] using moment_nat_pow μ g 2 (by norm_num)
  rwa [mul_pow, hf2, hg2] at hs

/-- Full creator contraction for positive raw polynomials in the original matrix
entries. The original sample space is arbitrary, all exponent identities are
preserved, and the exact sector assembly introduces no sector-count factor. -/
theorem creator_l2_le
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
    (d : ℕ) (hdegree : ∀ i t, degree (ν i t) ≤ d) (hdq : d < q) :
    Integrable (fun ω => ‖evaluateHilbert (creationCoeff c ν) (actionExponent ν)
      (fun e => X e.1 e.2 ω)‖ ^ 2) μ ∧
      moment μ 2 (fun ω => ‖evaluateHilbert (creationCoeff c ν) (actionExponent ν)
        (fun e => X e.1 e.2 ω)‖) ≤
        contractionConstant α B W *
          moment μ 2 (fun ω => ‖evaluateHilbert c ν (fun e => X e.1 e.2 ω)‖) := by
  classical
  have hInt : Integrable (fun ω => ‖evaluateHilbert (creationCoeff c ν) (actionExponent ν)
      (fun e => X e.1 e.2 ω)‖ ^ 2) μ := by
    simpa only [evaluateHilbert_norm_sq] using integrable_normSq
      (fun e : R × C => X e.1 e.2) (fun e => hX e.1 e.2) hind
      (fun e => hint e.1 e.2) (creationCoeff c ν) (actionExponent ν)
  refine ⟨hInt, ?_⟩
  apply PolynomialEnergyAssembly.second_moment_le_of_all_sectors
    (fun e : R × C => X e.1 e.2) (fun e => hX e.1 e.2) hind
    (fun e => hsym e.1 e.2) (fun e => hint e.1 e.2)
    c ν (creationCoeff c ν) (actionExponent ν) inputLabel outputLabel
    (contractionConstant α B W) (contractionConstant_nonneg α B W hB hW)
  rintro ⟨m, δ⟩
  cases m with
  | zero =>
    rw [input_mask_zero, output_creation_mask_zero]
    simp only [evaluateHilbert_zero, norm_zero, zero_pow (by decide : 2 ≠ 0),
      integral_zero, mul_zero, le_refl]
  | succ k =>
    rw [input_mask_succ, output_mask_succ, creation_count_block]
    by_cases hkq : k < q
    · obtain ⟨_, hb⟩ := CreationSectorContraction.sectorAction_l2_le X hX hind hsym hint
        α hα hregular q hq B hB hrow W hW hweak c ν hc d hdegree hdq k hkq δ
      simp_rw [RawSectorNorms.creation_sectorAction_eq] at hb
      apply integral_sq_le_of_second_moment_le _ _ (fun _ => norm_nonneg _)
        (fun _ => norm_nonneg _) (contractionConstant α B W)
      exact hb
    · have hz := creation_mask_zero_of_degree c ν d hdegree k (by omega) δ
      rw [hz, creationCoeff_zero]
      simp only [evaluateHilbert_zero, norm_zero, zero_pow (by decide : 2 ≠ 0),
        integral_zero, mul_zero, le_refl]

end Probability

end MI32.RawCreatorContraction
