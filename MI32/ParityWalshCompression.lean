import MI32.ParityGeometry
import GraphMatrices.Walsh

/-!
# Exact conditional Walsh multiplication and parity compression

Magnitudes are arbitrary fixed real values on the original edges `R × C`.
Amplitudes are arbitrary real coefficients: pointwise applications may
depend on every original magnitude, including spectator coordinates.
The actual finite uniform sign expectation recovers the original
parity multiplication entries and their creation/annihilation compressions.
-/

noncomputable section
open scoped BigOperators symmDiff
open GraphMatrices

namespace MI32.ParityWalshCompression

section Scalar

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- Actual conditional Walsh coefficient under the complete uniform sign law. -/
def coefficient (g : (E → Bool) → ℝ) (T : Finset E) : ℝ :=
  Walsh.expectation (fun σ => g σ * Walsh.character T σ)

theorem character_singleton (e : E) (σ : E → Bool) :
    Walsh.character {e} σ = Walsh.sign (σ e) := by
  simp [Walsh.character]

theorem coefficient_character (S T : Finset E) :
    coefficient (Walsh.character S) T = if S = T then 1 else 0 :=
  Walsh.character_orthogonality S T

theorem coefficient_finsetSum {I : Type*} (inputs : Finset I)
    (g : I → (E → Bool) → ℝ) (T : Finset E) :
    coefficient (fun σ => ∑ i ∈ inputs, g i σ) T =
      ∑ i ∈ inputs, coefficient (g i) T := by
  simp only [coefficient, Finset.sum_mul]
  exact Walsh.expectation_finset_sum inputs _

theorem coefficient_const_mul (c : ℝ) (g : (E → Bool) → ℝ) (T : Finset E) :
    coefficient (fun σ => c * g σ) T = c * coefficient g T := by
  simp only [coefficient, mul_assoc]
  exact Walsh.expectation_const_mul c _

/-- Coefficient extraction is exact, including outside an explicit finite support. -/
theorem coefficient_polynomial (I : Finset (Finset E)) (f : Finset E → ℝ)
    (T : Finset E) :
    coefficient (Walsh.polynomial I f) T = if T ∈ I then f T else 0 := by
  unfold Walsh.polynomial
  rw [coefficient_finsetSum]
  simp_rw [coefficient_const_mul, coefficient_character]
  simp

/-- Multiplication by one original sign toggles exactly its one Walsh flag. -/
theorem coefficient_sign_mul (e : E) (g : (E → Bool) → ℝ) (T : Finset E) :
    coefficient (fun σ => Walsh.sign (σ e) * g σ) T = coefficient g (T ∆ {e}) := by
  unfold coefficient
  congr 1
  funext σ
  rw [← Walsh.character_mul, character_singleton]
  ring

end Scalar

section Matrix

variable {R C : Type*} [Fintype R] [Fintype C] [DecidableEq R] [DecidableEq C]

omit [Fintype R] [Fintype C] in
theorem toggle_eq_symmDiff (e : R × C) (S : Finset (R × C)) :
    ParityGeometry.toggle e S = S ∆ {e} := by
  ext a
  by_cases he : e ∈ S <;> by_cases ha : a = e <;>
    simp [ParityGeometry.toggle, Finset.mem_symmDiff, he, ha]

omit [Fintype R] [Fintype C] in
theorem toggle_toggle (e : R × C) (S : Finset (R × C)) :
    ParityGeometry.toggle e (ParityGeometry.toggle e S) = S := by
  simp only [toggle_eq_symmDiff, symmDiff_symmDiff_cancel_right]

theorem sign_mul_character (e : R × C) (S : Finset (R × C)) (σ : R × C → Bool) :
    Walsh.sign (σ e) * Walsh.character S σ = Walsh.character (ParityGeometry.toggle e S) σ := by
  rw [toggle_eq_symmDiff, ← Walsh.character_mul, character_singleton]
  ring

/-- Inverse Walsh expansion of each current-row amplitude. -/
def inputPolynomial (f : R × Finset (R × C) → ℝ) (i : R) (σ : R × C → Bool) : ℝ :=
  Walsh.polynomial Finset.univ (fun S => f (i, S)) σ

/-- Multiplication by the literal signed original matrix, in row-to-column direction. -/
def matrixApply (z : R × C → ℝ) (f : R × Finset (R × C) → ℝ)
    (j : C) (σ : R × C → Bool) : ℝ :=
  ∑ i, z (i, j) * (Walsh.sign (σ (i, j)) * inputPolynomial f i σ)

/-- Every output coefficient keeps the same original magnitude factor
and toggles only its sign-parity label. -/
theorem coefficient_matrixApply (z : R × C → ℝ) (f : R × Finset (R × C) → ℝ)
    (j : C) (T : Finset (R × C)) :
    coefficient (matrixApply z f j) T =
      ∑ i, z (i, j) * f (i, ParityGeometry.toggle (i, j) T) := by
  unfold matrixApply inputPolynomial
  rw [coefficient_finsetSum]
  simp_rw [coefficient_const_mul, coefficient_sign_mul,
    coefficient_polynomial]
  simp only [Finset.mem_univ, if_true, toggle_eq_symmDiff]

/-- Restriction of coefficients, with no restriction on their dependence on magnitudes. -/
def inputMask (P : R × Finset (R × C) → Prop) [DecidablePred P]
    (f : R × Finset (R × C) → ℝ) (input : R × Finset (R × C)) : ℝ :=
  if P input then f input else 0

/-- The same literal matrix product written over an explicit finite input set. -/
def finiteMatrixApply (z : R × C → ℝ) (inputs : Finset (R × Finset (R × C)))
    (f : R × Finset (R × C) → ℝ) (j : C) (σ : R × C → Bool) : ℝ :=
  ∑ input ∈ inputs, (z (input.1, j) * f input) *
    (Walsh.sign (σ (input.1, j)) * Walsh.character input.2 σ)

/-- The explicit finite sum is precisely the original signed matrix
acting on the inverse Walsh expansion of the masked input. -/
theorem finiteMatrixApply_eq_matrixApply (z : R × C → ℝ)
    (inputs : Finset (R × Finset (R × C))) (f : R × Finset (R × C) → ℝ)
    (j : C) (σ : R × C → Bool) :
    finiteMatrixApply z inputs f j σ =
      matrixApply z (inputMask (fun input => input ∈ inputs) f) j σ := by
  symm
  calc
    _ = ∑ input : R × Finset (R × C), if input ∈ inputs then
        (z (input.1, j) * f input) *
          (Walsh.sign (σ (input.1, j)) * Walsh.character input.2 σ) else 0 := by
      simp only [matrixApply, inputPolynomial, Walsh.polynomial, Finset.mul_sum,
        Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro S _
      by_cases h : (i, S) ∈ inputs
      · simp [inputMask, h]
        ring
      · simp [inputMask, h]
    _ = _ := by simp [finiteMatrixApply]

/-- The probabilistic Walsh coefficient equals the already defined
original-coordinate multiplication-entry action. -/
theorem coefficient_finiteMatrixApply (z : R × C → ℝ)
    (inputs : Finset (R × Finset (R × C))) (f : R × Finset (R × C) → ℝ)
    (output : C × Finset (R × C)) :
    coefficient (finiteMatrixApply z inputs f output.1) output.2 =
      ∑ input ∈ inputs, ParityGeometry.multiplicationEntry z input output * f input := by
  unfold finiteMatrixApply
  simp_rw [sign_mul_character]
  rw [coefficient_finsetSum]
  simp_rw [coefficient_const_mul, coefficient_character]
  apply Finset.sum_congr rfl
  intro input _
  by_cases h : output.2 = ParityGeometry.toggle (input.1, output.1) input.2 <;>
    simp [ParityGeometry.multiplicationEntry, h, eq_comm]

/-- Original multiplication splits exactly into the two directional
parity actions, on the same amplitudes and the same magnitude values. -/
theorem coefficient_eq_creation_add_annihilation (z : R × C → ℝ)
    (inputs : Finset (R × Finset (R × C))) (f : R × Finset (R × C) → ℝ)
    (output : C × Finset (R × C)) :
    coefficient (finiteMatrixApply z inputs f output.1) output.2 =
      ParityGeometry.creationApply z inputs f output + ParityGeometry.annihilationApply z inputs f output := by
  rw [coefficient_finiteMatrixApply]
  simp only [ParityGeometry.multiplicationEntry_eq_creation_add_annihilation,
    add_mul, Finset.sum_add_distrib, ParityGeometry.creationApply, ParityGeometry.annihilationApply]

/-- For an input occupation grade, creation is the next-grade projection
of the actual conditional Walsh coefficient. -/
theorem creationApply_eq_grade_compression (z : R × C → ℝ)
    (inputs : Finset (R × Finset (R × C))) (f : R × Finset (R × C) → ℝ)
    (d : ℕ) (hgrade : ∀ input ∈ inputs, input.2.card = d)
    (output : C × Finset (R × C)) :
    ParityGeometry.creationApply z inputs f output =
      if output.2.card = d + 1
      then coefficient (finiteMatrixApply z inputs f output.1) output.2 else 0 := by
  rw [coefficient_finiteMatrixApply]
  unfold ParityGeometry.creationApply
  by_cases h : output.2.card = d + 1
  · simp [h]
    apply Finset.sum_congr rfl
    intro input hi
    rw [ParityGeometry.creationEntry_eq_grade_compression, hgrade input hi, if_pos h]
  · simp only [h, if_false]
    apply Finset.sum_eq_zero
    intro input hi
    rw [ParityGeometry.creationEntry_eq_grade_compression, hgrade input hi, if_neg h, zero_mul]

/-- Annihilation is the previous-grade projection of the same actual
conditional Walsh multiplication; original magnitude powers are retained. -/
theorem annihilationApply_eq_grade_compression (z : R × C → ℝ)
    (inputs : Finset (R × Finset (R × C))) (f : R × Finset (R × C) → ℝ)
    (d : ℕ) (hgrade : ∀ input ∈ inputs, input.2.card = d)
    (output : C × Finset (R × C)) :
    ParityGeometry.annihilationApply z inputs f output =
      if output.2.card + 1 = d
      then coefficient (finiteMatrixApply z inputs f output.1) output.2 else 0 := by
  rw [coefficient_finiteMatrixApply]
  unfold ParityGeometry.annihilationApply
  by_cases h : output.2.card + 1 = d
  · simp only [h, if_true]
    apply Finset.sum_congr rfl
    intro input hi
    rw [ParityGeometry.annihilationEntry_eq_grade_compression, hgrade input hi, if_pos h]
  · simp only [h, if_false]
    apply Finset.sum_eq_zero
    intro input hi
    rw [ParityGeometry.annihilationEntry_eq_grade_compression, hgrade input hi, if_neg h, zero_mul]

omit [Fintype C] in
/-- A creator output uses exactly its matching input row-count sector. -/
theorem creationApply_eq_inputSectorMask (z : R × C → ℝ)
    (inputs : Finset (R × Finset (R × C))) (f : R × Finset (R × C) → ℝ)
    (output : C × Finset (R × C)) :
    ParityGeometry.creationApply z inputs f output =
      ParityGeometry.creationApply z inputs
        (inputMask (fun input => ParityGeometry.creationLabel input.1 input.2 =
          ParityGeometry.rowCount output.2) f) output := by
  classical
  rw [ParityGeometry.creationApply_eq_label_sum]
  unfold ParityGeometry.creationApply
  apply Finset.sum_congr rfl
  intro input _
  by_cases h : ParityGeometry.creationLabel input.1 input.2 = ParityGeometry.rowCount output.2 <;>
    simp [inputMask, h]

omit [Fintype R] in
/-- The annihilator uses the original input column-count sector directly. -/
theorem annihilationApply_eq_inputSectorMask (z : R × C → ℝ)
    (inputs : Finset (R × Finset (R × C))) (f : R × Finset (R × C) → ℝ)
    (output : C × Finset (R × C)) :
    ParityGeometry.annihilationApply z inputs f output =
      ParityGeometry.annihilationApply z inputs
        (inputMask (fun input => ParityGeometry.colCount input.2 =
          ParityGeometry.annihilationLabel output.1 output.2) f) output := by
  classical
  rw [ParityGeometry.annihilationApply_eq_label_sum]
  unfold ParityGeometry.annihilationApply
  apply Finset.sum_congr rfl
  intro input _
  by_cases h : ParityGeometry.colCount input.2 =
      ParityGeometry.annihilationLabel output.1 output.2 <;> simp [inputMask, h]

/-- For one input grade and creation sector, both required output masks
are literal projections of the actual conditional Walsh multiplication. -/
theorem creationApply_eq_sector_grade_compression (z : R × C → ℝ)
    (inputs : Finset (R × Finset (R × C))) (f : R × Finset (R × C) → ℝ)
    (d : ℕ) (hgrade : ∀ input ∈ inputs, input.2.card = d)
    (label : R → ℕ)
    (hlabel : ∀ input ∈ inputs, ParityGeometry.creationLabel input.1 input.2 = label)
    (output : C × Finset (R × C)) :
    ParityGeometry.creationApply z inputs f output =
      if output.2.card = d + 1 ∧ ParityGeometry.rowCount output.2 = label
      then coefficient (finiteMatrixApply z inputs f output.1) output.2 else 0 := by
  classical
  by_cases hout : ParityGeometry.rowCount output.2 = label
  · simpa only [hout, and_true] using creationApply_eq_grade_compression z inputs f d hgrade output
  · have hzero : ParityGeometry.creationApply z inputs f output = 0 := by
      unfold ParityGeometry.creationApply
      apply Finset.sum_eq_zero
      intro input hi
      rw [ParityGeometry.creationEntry_eq_zero_of_label_ne, zero_mul]
      rw [hlabel input hi]
      exact Ne.symm hout
    simp only [hzero, hout, and_false, if_false]

/-- The direct annihilation sector has its own column-count output label;
the same original signed matrix is projected to the preceding grade. -/
theorem annihilationApply_eq_sector_grade_compression (z : R × C → ℝ)
    (inputs : Finset (R × Finset (R × C))) (f : R × Finset (R × C) → ℝ)
    (d : ℕ) (hgrade : ∀ input ∈ inputs, input.2.card = d)
    (label : C → ℕ)
    (hlabel : ∀ input ∈ inputs, ParityGeometry.colCount input.2 = label)
    (output : C × Finset (R × C)) :
    ParityGeometry.annihilationApply z inputs f output =
      if output.2.card + 1 = d ∧ ParityGeometry.annihilationLabel output.1 output.2 = label
      then coefficient (finiteMatrixApply z inputs f output.1) output.2 else 0 := by
  classical
  by_cases hout : ParityGeometry.annihilationLabel output.1 output.2 = label
  · simpa only [hout, and_true] using annihilationApply_eq_grade_compression z inputs f d hgrade output
  · have hzero : ParityGeometry.annihilationApply z inputs f output = 0 := by
      unfold ParityGeometry.annihilationApply
      apply Finset.sum_eq_zero
      intro input hi
      rw [ParityGeometry.annihilationEntry_eq_zero_of_label_ne, zero_mul]
      rw [hlabel input hi]
      exact Ne.symm hout
    simp only [hzero, hout, and_false, if_false]

/-- Exact rowwise Parseval identity for arbitrary coefficient amplitudes. -/
theorem inputPolynomial_parseval (f : R × Finset (R × C) → ℝ) :
    Walsh.expectation (fun σ => ∑ i, inputPolynomial f i σ ^ 2) =
      ∑ i, ∑ S, f (i, S) ^ 2 := by
  rw [Walsh.expectation_finset_sum]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [inputPolynomial, pow_two] using
    Walsh.polynomial_pairing Finset.univ (fun S => f (i, S)) (fun S => f (i, S))

/-- Every deterministic coefficient mask, including grades and exact
occupation-count sectors, contracts the conditional sign L2 energy. -/
theorem inputMask_L2_contraction (P : R × Finset (R × C) → Prop) [DecidablePred P]
    (f : R × Finset (R × C) → ℝ) :
    Walsh.expectation (fun σ => ∑ i, inputPolynomial (inputMask P f) i σ ^ 2) ≤
      Walsh.expectation (fun σ => ∑ i, inputPolynomial f i σ ^ 2) := by
  rw [inputPolynomial_parseval, inputPolynomial_parseval]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro S _
  by_cases h : P (i, S)
  · simp [inputMask, h]
  · simpa [inputMask, h] using sq_nonneg (f (i, S))

/-- Reconstruct the actual matrix output from its actual Walsh coefficients.
The proof sums the exact finite expansion and merges only identical parity labels. -/
theorem finiteMatrixApply_eq_polynomial_coeff (z : R × C → ℝ)
    (inputs : Finset (R × Finset (R × C))) (f : R × Finset (R × C) → ℝ)
    (j : C) (σ : R × C → Bool) :
    finiteMatrixApply z inputs f j σ =
      Walsh.polynomial Finset.univ (coefficient (finiteMatrixApply z inputs f j)) σ := by
  symm
  unfold Walsh.polynomial
  have hcoeff (T : Finset (R × C)) := coefficient_finiteMatrixApply z inputs f (j, T)
  simp_rw [hcoeff]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  unfold finiteMatrixApply
  apply Finset.sum_congr rfl
  intro input _
  simp [ParityGeometry.multiplicationEntry, sign_mul_character]

/-- Parseval for the actual signed-matrix output, not an assumed coefficient model. -/
theorem finiteMatrixApply_parseval (z : R × C → ℝ)
    (inputs : Finset (R × Finset (R × C))) (f : R × Finset (R × C) → ℝ) (j : C) :
    Walsh.expectation (fun σ => finiteMatrixApply z inputs f j σ ^ 2) =
      ∑ T, coefficient (finiteMatrixApply z inputs f j) T ^ 2 := by
  have hfun : (fun σ => finiteMatrixApply z inputs f j σ ^ 2) =
      (fun σ => Walsh.polynomial Finset.univ
        (coefficient (finiteMatrixApply z inputs f j)) σ ^ 2) := by
    funext σ
    exact congrArg (fun x : ℝ => x ^ 2) (finiteMatrixApply_eq_polynomial_coeff z inputs f j σ)
  rw [hfun]
  simpa only [pow_two] using Walsh.polynomial_pairing Finset.univ
    (coefficient (finiteMatrixApply z inputs f j)) (coefficient (finiteMatrixApply z inputs f j))

/-- Any output grade/sector coefficient mask is a contraction of the
actual signed matrix output in conditional L2. -/
theorem outputMask_L2_contraction (z : R × C → ℝ)
    (inputs : Finset (R × Finset (R × C))) (f : R × Finset (R × C) → ℝ)
    (P : C × Finset (R × C) → Prop) [DecidablePred P] :
    (∑ j, ∑ T, (if P (j, T) then coefficient (finiteMatrixApply z inputs f j) T else 0) ^ 2) ≤
      Walsh.expectation (fun σ => ∑ j, finiteMatrixApply z inputs f j σ ^ 2) := by
  rw [Walsh.expectation_finset_sum]
  simp_rw [finiteMatrixApply_parseval]
  apply Finset.sum_le_sum
  intro j _
  apply Finset.sum_le_sum
  intro T _
  by_cases h : P (j, T)
  · simp [h]
  · simpa only [h, if_false, zero_pow (by decide : (2 : ℕ) ≠ 0)] using
    sq_nonneg (coefficient (finiteMatrixApply z inputs f j) T)

/-- The existing creator action is a conditional L2 contraction of
actual original multiplication on any one input occupation grade. -/
theorem creationApply_L2_le (z : R × C → ℝ)
    (inputs : Finset (R × Finset (R × C))) (f : R × Finset (R × C) → ℝ)
    (d : ℕ) (hgrade : ∀ input ∈ inputs, input.2.card = d) :
    (∑ j, ∑ T, ParityGeometry.creationApply z inputs f (j, T) ^ 2) ≤
      Walsh.expectation (fun σ => ∑ j, finiteMatrixApply z inputs f j σ ^ 2) := by
  have hcoeff (j : C) (T : Finset (R × C)) :=
    creationApply_eq_grade_compression z inputs f d hgrade (j, T)
  simp_rw [hcoeff]
  exact outputMask_L2_contraction z inputs f (fun output => output.2.card = d + 1)

/-- The same contraction holds for the direct annihilator, keeping
every original magnitude factor rather than replacing it by an adjoint model. -/
theorem annihilationApply_L2_le (z : R × C → ℝ)
    (inputs : Finset (R × Finset (R × C))) (f : R × Finset (R × C) → ℝ)
    (d : ℕ) (hgrade : ∀ input ∈ inputs, input.2.card = d) :
    (∑ j, ∑ T, ParityGeometry.annihilationApply z inputs f (j, T) ^ 2) ≤
      Walsh.expectation (fun σ => ∑ j, finiteMatrixApply z inputs f j σ ^ 2) := by
  have hcoeff (j : C) (T : Finset (R × C)) :=
    annihilationApply_eq_grade_compression z inputs f d hgrade (j, T)
  simp_rw [hcoeff]
  exact outputMask_L2_contraction z inputs f (fun output => output.2.card + 1 = d)

end Matrix

end MI32.ParityWalshCompression
