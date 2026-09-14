import MI32.BipartiteConeContraction

/-!
# Actual bipartite vacuum powers from positive raw words

The length-k polynomial has exact raw degree k and nonnegative deterministic
coefficients, so the proved bipartite contraction applies at every prefix
below q. Induction bounds its original-law L2 norm by C^k. The polynomial is
exactly the original symmetric bipartite matrix power on a coordinate vacuum;
the resulting squared vacuum energies are ready for the operator trace step.
-/

noncomputable section
open scoped BigOperators Matrix
open MeasureTheory ProbabilityTheory

namespace MI32.BipartiteVacuumIteration

open PositiveVacuumWords PositivePolynomial SymmetricPositiveCone

variable {Ω R C : Type*} [Fintype R] [Fintype C] [DecidableEq R] [DecidableEq C]

/-- The literal symmetric bipartite matrix, with both orientations sharing
each original entry and with identically zero diagonal blocks. -/
def lift (X : R → C → Ω → ℝ) (ω : Ω) : Matrix (Sum R C) (Sum R C) ℝ :=
  PositiveVacuumWords.matrix bipartiteWeight (fun e => X e.1 e.2 ω)

/-- The explicit positive original-variable word polynomial from a coordinate vacuum. -/
def vacuum (X : R → C → Ω → ℝ) (v : Sum R C) (k : ℕ) (ω : Ω) :
    EuclideanSpace ℝ (Sum R C) :=
  evaluateHilbert (coeff bipartiteWeight v k) (exponent k) (fun e => X e.1 e.2 ω)

/-- The explicit raw polynomial is exactly the actual matrix power on the
original Euclidean coordinate vacuum, including empty opposite axes. -/
theorem vacuum_eq_matrix_power (X : R → C → Ω → ℝ) (v : Sum R C) (k : ℕ) (ω : Ω) :
    vacuum X v k ω = Matrix.toEuclideanCLM (n := Sum R C) (𝕜 := ℝ) (lift X ω ^ k)
      (EuclideanSpace.basisFun (Sum R C) ℝ v) := by
  rw [vacuum, evaluateHilbert_eq_pow_mulVec]
  simp only [EuclideanSpace.basisFun_apply, PiLp.single, Matrix.toEuclideanCLM_toLp]
  rfl

@[simp] theorem vacuum_zero (X : R → C → Ω → ℝ) (v : Sum R C) (ω : Ω) :
    vacuum X v 0 ω = EuclideanSpace.basisFun (Sum R C) ℝ v := by
  rw [vacuum_eq_matrix_power]
  simp

/-- One checked word extension is the actual bipartite action on the preceding prefix. -/
theorem vacuum_succ (X : R → C → Ω → ℝ) (v : Sum R C) (k : ℕ) (ω : Ω) :
    vacuum X v (k + 1) ω = BipartiteConeContraction.action X
      (coeff bipartiteWeight v k) (exponent k) ω := rfl

section Probability

variable [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Every reachable prefix has integrable squared norm and original-law
L2 norm at most C^k. Positivity and degree are derived from the explicit words. -/
theorem vacuum_l2_le
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
    (v : Sum R C) (k : ℕ) (hkq : k ≤ q) :
    Integrable (fun ω => ‖vacuum X v k ω‖ ^ 2) μ ∧
      moment μ 2 (fun ω => ‖vacuum X v k ω‖) ≤
        RawMultiplicationContraction.contractionConstant α B W ^ k := by
  have hN : 0 ≤ RawMultiplicationContraction.contractionConstant α B W := by
    unfold RawMultiplicationContraction.contractionConstant
    positivity
  revert hkq
  induction k with
  | zero =>
    intro _
    constructor
    · simpa only [vacuum_zero, OrthonormalBasis.norm_eq_one, one_pow] using
        (integrable_const (1 : ℝ) : Integrable (fun _ : Ω => (1 : ℝ)) μ)
    · simp only [vacuum_zero, OrthonormalBasis.norm_eq_one, pow_zero]
      exact le_of_eq (by simpa only [abs_one] using MomentTools.const (μ := μ) 2 (by norm_num) 1)
  | succ k ih =>
    intro hkq
    obtain ⟨_, hprevious⟩ := ih (by omega)
    obtain ⟨hInt, hStep⟩ := BipartiteConeContraction.action_l2_le
      X hX hind hsym hint α hα hregular q hq B hB hrow hcol W hW hweak
      (coeff bipartiteWeight v k) (exponent k)
      (coeff_nonneg bipartiteWeight bipartiteWeight_nonneg v k)
      k (fun j t => (degree_exponent k j t).le) (by omega)
    refine ⟨hInt, hStep.trans ?_⟩
    calc
      _ ≤ RawMultiplicationContraction.contractionConstant α B W *
          RawMultiplicationContraction.contractionConstant α B W ^ k :=
        mul_le_mul_of_nonneg_left hprevious hN
      _ = RawMultiplicationContraction.contractionConstant α B W ^ (k + 1) :=
        (pow_succ' _ _).symm

/-- At the endpoint each actual original matrix-power vacuum has energy
at most C^(2q), with its integrability proved by the same iteration. -/
theorem vacuum_energies
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
        moment μ (2 * (q : ℝ)) (ThinMatrix.bilinear X s t) ≤ W) :
    ∀ v : Sum R C,
      Integrable (fun ω => ‖Matrix.toEuclideanCLM (n := Sum R C) (𝕜 := ℝ) (lift X ω ^ q)
        (EuclideanSpace.basisFun (Sum R C) ℝ v)‖ ^ 2) μ ∧
      (∫ ω, ‖Matrix.toEuclideanCLM (n := Sum R C) (𝕜 := ℝ) (lift X ω ^ q)
        (EuclideanSpace.basisFun (Sum R C) ℝ v)‖ ^ 2 ∂μ) ≤
        RawMultiplicationContraction.contractionConstant α B W ^ (2 * q) := by
  intro v
  obtain ⟨hInt, hBound⟩ := vacuum_l2_le X hX hind hsym hint α hα hregular
    q hq B hB hrow hcol W hW hweak v q le_rfl
  refine ⟨by simpa only [vacuum_eq_matrix_power] using hInt, ?_⟩
  have hsq := pow_le_pow_left₀ (MomentTools.nonneg (μ := μ) 2
    (fun ω => ‖vacuum X v q ω‖)) hBound 2
  have hroot : moment μ 2 (fun ω => ‖vacuum X v q ω‖) ^ 2 =
      ∫ ω, ‖vacuum X v q ω‖ ^ 2 ∂μ := by
    simpa only [Nat.cast_ofNat, abs_of_nonneg (norm_nonneg _)] using
      moment_nat_pow μ (fun ω => ‖vacuum X v q ω‖) 2 (by norm_num)
  rw [hroot, ← pow_mul, Nat.mul_comm q 2] at hsq
  simpa only [vacuum_eq_matrix_power] using hsq

end Probability
end MI32.BipartiteVacuumIteration
