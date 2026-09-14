import MI32.PositiveVacuumWords
import MI32.ThinPolynomialInteraction
import MI32.RawMultiplicationContraction
import MI32.TransposedPolynomialContraction

/-!
# One full symmetric bipartite action on the original positive cone

Both off-diagonal blocks use the same original matrix entries. The row and
column outputs occupy orthogonal coordinate spaces, so their squared energies
add exactly. The full action retains the same contraction factor as either
complete rectangular action, without a further square-root-of-two loss.
-/

noncomputable section
open scoped BigOperators Matrix
open MeasureTheory ProbabilityTheory

namespace MI32.BipartiteConeContraction

open PositivePolynomial PositiveWordExtension SymmetricPositiveCone

variable {Ω R C K : Type*} [Fintype R] [Fintype C] [Fintype K]
    [DecidableEq R] [DecidableEq C]

/-- The output raw polynomial is the literal positive linear-entry extension
of the input, with every exponent still over the original family `R × C`. -/
def action (X : R → C → Ω → ℝ) (c : Sum R C → K → ℝ)
    (ν : Sum R C → K → R × C → ℕ) (ω : Ω) : EuclideanSpace ℝ (Sum R C) :=
  evaluateHilbert (linearExtendCoeff PositiveVacuumWords.bipartiteWeight c)
    (linearExtendExponent ν) (fun e => X e.1 e.2 ω)

/-- Exact equality with the actual symmetric bipartite matrix multiplying
the original polynomial vector on the same sample. -/
theorem action_eq_matrix_mulVec (X : R → C → Ω → ℝ) (c : Sum R C → K → ℝ)
    (ν : Sum R C → K → R × C → ℕ) (ω : Ω) :
    action X c ν ω = WithLp.toLp 2
      ((PositiveVacuumWords.matrix PositiveVacuumWords.bipartiteWeight
        (fun e => X e.1 e.2 ω)) *ᵥ
        (fun v => evaluate (c v) (ν v) (fun e => X e.1 e.2 ω))) := by
  ext v
  exact evaluate_linearExtend PositiveVacuumWords.bipartiteWeight c ν v
    (fun e => X e.1 e.2 ω)

theorem action_apply_inl (X : R → C → Ω → ℝ) (c : Sum R C → K → ℝ)
    (ν : Sum R C → K → R × C → ℕ) (ω : Ω) (i : R) :
    action X c ν ω (.inl i) =
      ∑ j, X i j ω * evaluate (c (.inr j)) (ν (.inr j)) (fun e => X e.1 e.2 ω) := by
  rw [action_eq_matrix_mulVec]
  change (∑ v, PositiveVacuumWords.matrix PositiveVacuumWords.bipartiteWeight
      (fun e => X e.1 e.2 ω) (.inl i) v *
        evaluate (c v) (ν v) (fun e => X e.1 e.2 ω)) = _
  rw [Fintype.sum_sum_type]
  simp only [PositiveVacuumWords.bipartite_matrix_inl_inl, zero_mul, Finset.sum_const_zero,
    PositiveVacuumWords.bipartite_matrix_inl_inr, zero_add]

theorem action_apply_inr (X : R → C → Ω → ℝ) (c : Sum R C → K → ℝ)
    (ν : Sum R C → K → R × C → ℕ) (ω : Ω) (j : C) :
    action X c ν ω (.inr j) =
      ∑ i, X i j ω * evaluate (c (.inl i)) (ν (.inl i)) (fun e => X e.1 e.2 ω) := by
  rw [action_eq_matrix_mulVec]
  change (∑ v, PositiveVacuumWords.matrix PositiveVacuumWords.bipartiteWeight
      (fun e => X e.1 e.2 ω) (.inr j) v *
        evaluate (c v) (ν v) (fun e => X e.1 e.2 ω)) = _
  rw [Fintype.sum_sum_type]
  simp only [PositiveVacuumWords.bipartite_matrix_inr_inr, zero_mul, Finset.sum_const_zero,
    PositiveVacuumWords.bipartite_matrix_inr_inl, add_zero]

/-- Row outputs are exactly the reverse rectangular action with the full
original-variable polynomial. -/
theorem action_inl_eq (X : R → C → Ω → ℝ) (c : Sum R C → K → ℝ)
    (ν : Sum R C → K → R × C → ℕ) (ω : Ω) :
    WithLp.toLp 2 (fun i => action X c ν ω (.inl i)) =
      ThinPolynomialInteraction.action (fun j i => X i j) (fun e : R × C => X e.1 e.2)
        (fun j => c (.inr j)) (fun j => ν (.inr j)) ω := by
  ext i
  change action X c ν ω (.inl i) = _
  rw [action_apply_inl]
  rfl

/-- Column outputs are exactly the forward rectangular action. -/
theorem action_inr_eq (X : R → C → Ω → ℝ) (c : Sum R C → K → ℝ)
    (ν : Sum R C → K → R × C → ℕ) (ω : Ω) :
    WithLp.toLp 2 (fun j => action X c ν ω (.inr j)) =
      ThinPolynomialInteraction.action X (fun e : R × C => X e.1 e.2)
        (fun i => c (.inl i)) (fun i => ν (.inl i)) ω := by
  ext j
  change action X c ν ω (.inr j) = _
  rw [action_apply_inr]
  rfl

omit [DecidableEq R] [DecidableEq C] in
/-- Exact orthogonal splitting of the original input polynomial energy. -/
theorem polynomial_norm_sq_eq (c : Sum R C → K → ℝ)
    (ν : Sum R C → K → R × C → ℕ) (z : R × C → ℝ) :
    ‖evaluateHilbert c ν z‖ ^ 2 =
      ‖evaluateHilbert (fun i => c (.inl i)) (fun i => ν (.inl i)) z‖ ^ 2 +
        ‖evaluateHilbert (fun j => c (.inr j)) (fun j => ν (.inr j)) z‖ ^ 2 := by
  simp only [evaluateHilbert_norm_sq, normSq, Fintype.sum_sum_type]

/-- Exact orthogonal splitting of the actual output energy; no inequality
or dimension factor is used in this identity. -/
theorem action_norm_sq_eq (X : R → C → Ω → ℝ) (c : Sum R C → K → ℝ)
    (ν : Sum R C → K → R × C → ℕ) (ω : Ω) :
    ‖action X c ν ω‖ ^ 2 =
      ‖ThinPolynomialInteraction.action (fun j i => X i j)
        (fun e : R × C => X e.1 e.2) (fun j => c (.inr j))
        (fun j => ν (.inr j)) ω‖ ^ 2 +
      ‖ThinPolynomialInteraction.action X (fun e : R × C => X e.1 e.2)
        (fun i => c (.inl i)) (fun i => ν (.inl i)) ω‖ ^ 2 := by
  rw [← action_inl_eq, ← action_inr_eq]
  simp only [EuclideanSpace.real_norm_sq_eq, Fintype.sum_sum_type]

omit [Fintype K] in
/-- A vacuum-word successor is exactly this same bipartite raw action. -/
theorem action_vacuum_eq (X : R → C → Ω → ℝ) (v : Sum R C) (k : ℕ) (ω : Ω) :
    action X (PositiveVacuumWords.coeff PositiveVacuumWords.bipartiteWeight v k)
      (PositiveVacuumWords.exponent k) ω =
      evaluateHilbert (PositiveVacuumWords.coeff PositiveVacuumWords.bipartiteWeight v (k + 1))
        (PositiveVacuumWords.exponent (k + 1)) (fun e => X e.1 e.2 ω) := rfl

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

/-- One complete symmetric bipartite step on the positive original-variable
polynomial cone. The two rectangular actions have the same proved constant;
orthogonal energy assembly keeps that constant with no additional loss.
All original-law integrability and directional estimates are derived. -/
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
    (c : Sum R C → K → ℝ) (ν : Sum R C → K → R × C → ℕ)
    (hc : ∀ v t, 0 ≤ c v t)
    (d : ℕ) (hdegree : ∀ v t, degree (ν v t) ≤ d) (hdq : d < q) :
    Integrable (fun ω => ‖action X c ν ω‖ ^ 2) μ ∧
      moment μ 2 (fun ω => ‖action X c ν ω‖) ≤
        RawMultiplicationContraction.contractionConstant α B W *
          moment μ 2 (fun ω => ‖evaluateHilbert c ν (fun e => X e.1 e.2 ω)‖) := by
  obtain ⟨hfint, hfbound⟩ := RawMultiplicationContraction.action_l2_le
    X hX hind hsym hint α hα hregular q hq B hB hrow hcol W hW hweak
    (fun i => c (.inl i)) (fun i => ν (.inl i)) (fun i t => hc (.inl i) t)
    d (fun i t => hdegree (.inl i) t) hdq
  obtain ⟨hrint, hrbound⟩ := TransposedPolynomialContraction.action_l2_le
    X hX hind hsym hint α hα hregular q hq B hB hrow hcol W hW hweak
    (fun j => c (.inr j)) (fun j => ν (.inr j)) (fun j t => hc (.inr j) t)
    d (fun j t => hdegree (.inr j) t) hdq
  have hinL : Integrable (fun ω =>
      ‖evaluateHilbert (fun i => c (.inl i)) (fun i => ν (.inl i))
        (fun e => X e.1 e.2 ω)‖ ^ 2) μ := by
    simpa only [evaluateHilbert_norm_sq] using integrable_normSq
      (fun e : R × C => X e.1 e.2) (fun e => hX e.1 e.2) hind
      (fun e => hint e.1 e.2) (fun i => c (.inl i)) (fun i => ν (.inl i))
  have hinR : Integrable (fun ω =>
      ‖evaluateHilbert (fun j => c (.inr j)) (fun j => ν (.inr j))
        (fun e => X e.1 e.2 ω)‖ ^ 2) μ := by
    simpa only [evaluateHilbert_norm_sq] using integrable_normSq
      (fun e : R × C => X e.1 e.2) (fun e => hX e.1 e.2) hind
      (fun e => hint e.1 e.2) (fun j => c (.inr j)) (fun j => ν (.inr j))
  have hfullint : Integrable (fun ω => ‖action X c ν ω‖ ^ 2) μ := by
    simp_rw [action_norm_sq_eq]
    exact hrint.add hfint
  refine ⟨hfullint, ?_⟩
  have hN : 0 ≤ RawMultiplicationContraction.contractionConstant α B W := by
    unfold RawMultiplicationContraction.contractionConstant
    positivity
  apply MomentTools.even_moment_le_of_integral_le _ _
    (RawMultiplicationContraction.contractionConstant α B W) hN 2 (by norm_num) (by decide)
  have hr := integral_sq_le_of_second_moment_le _ _ (fun _ => norm_nonneg _)
    (fun _ => norm_nonneg _) _ hrbound
  have hf := integral_sq_le_of_second_moment_le _ _ (fun _ => norm_nonneg _)
    (fun _ => norm_nonneg _) _ hfbound
  simp_rw [action_norm_sq_eq, polynomial_norm_sq_eq]
  rw [integral_add hrint hfint, integral_add hinL hinR, mul_add]
  simpa only [ThinPolynomialInteraction.polynomialVector, add_comm] using add_le_add hr hf

end Probability

end MI32.BipartiteConeContraction
