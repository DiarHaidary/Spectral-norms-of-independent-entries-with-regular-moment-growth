import MI32.PositiveWordExtension
import MI32.ParityWalshCompression

/-!
# Exact raw-polynomial creation and annihilation

Both directions use the same original term family `R × K` and append
one occurrence of the original edge `(i,j)`. Their coefficients select
absence or presence in the OLD sign parity. Removing an occupied flag
does not remove a magnitude factor or lower the original raw degree.
The conditional Walsh coefficients are identified with the existing
directional actions on the complete original magnitude polynomials.
-/

noncomputable section
open scoped BigOperators symmDiff
open GraphMatrices

namespace MI32.RawDirectionalActions

open PositivePolynomial RawParity PositiveWordExtension PolynomialSectorMasks
open ParityWalshCompression

variable {R C K : Type*} [Fintype R] [Fintype C] [Fintype K]
    [DecidableEq R] [DecidableEq C]

/-- Creation keeps an old term precisely when its original edge flag is absent. -/
def creationCoeff (c : R → K → ℝ) (ν : R → K → R × C → ℕ)
    (j : C) (t : R × K) : ℝ :=
  if (t.1, j) ∉ parity (ν t.1 t.2) then c t.1 t.2 else 0

/-- Annihilation keeps an old term precisely when its original edge flag is present. -/
def annihilationCoeff (c : R → K → ℝ) (ν : R → K → R × C → ℕ)
    (j : C) (t : R × K) : ℝ :=
  if (t.1, j) ∈ parity (ν t.1 t.2) then c t.1 t.2 else 0

/-- The same full raw exponent update is used in both directions. -/
def actionExponent (ν : R → K → R × C → ℕ) (j : C) (t : R × K) : R × C → ℕ :=
  extendExponent (fun i j => (i, j)) ν j t

omit [Fintype K] in
theorem creationCoeff_nonneg (c : R → K → ℝ) (ν : R → K → R × C → ℕ)
    (hc : ∀ i k, 0 ≤ c i k) (j : C) (t : R × K) : 0 ≤ creationCoeff c ν j t := by
  have ht := hc t.1 t.2
  unfold creationCoeff
  split_ifs <;> positivity

omit [Fintype K] in
theorem annihilationCoeff_nonneg (c : R → K → ℝ) (ν : R → K → R × C → ℕ)
    (hc : ∀ i k, 0 ≤ c i k) (j : C) (t : R × K) : 0 ≤ annihilationCoeff c ν j t := by
  unfold annihilationCoeff
  split_ifs
  · exact hc t.1 t.2
  · exact le_rfl

omit [Fintype K] in
/-- Every retained raw word has one additional original variable occurrence. -/
theorem degree_actionExponent (ν : R → K → R × C → ℕ) (j : C) (t : R × K) :
    degree (actionExponent ν j t) = degree (ν t.1 t.2) + 1 :=
  degree_extendExponent (fun i j => (i, j)) ν j t

omit [Fintype K] in
theorem degree_actionExponent_le (ν : R → K → R × C → ℕ)
    (d : ℕ) (hdegree : ∀ i k, degree (ν i k) ≤ d) (j : C) (t : R × K) :
    degree (actionExponent ν j t) ≤ d + 1 :=
  degree_extendExponent_le (fun i j => (i, j)) ν d hdegree j t

omit [Fintype K] in
theorem parity_actionExponent (ν : R → K → R × C → ℕ) (j : C) (t : R × K) :
    parity (actionExponent ν j t) = ParityGeometry.toggle (t.1, j) (parity (ν t.1 t.2)) := by
  rw [toggle_eq_symmDiff]
  exact parity_extendExponent (fun i j => (i, j)) ν j t

omit [Fintype K] in
/-- No term is lost or counted twice in the raw directional split. -/
theorem creationCoeff_add_annihilationCoeff (c : R → K → ℝ)
    (ν : R → K → R × C → ℕ) (j : C) (t : R × K) :
    creationCoeff c ν j t + annihilationCoeff c ν j t = extendCoeff (fun _ _ => 1) c j t := by
  by_cases h : (t.1, j) ∈ parity (ν t.1 t.2) <;>
    simp [creationCoeff, annihilationCoeff, extendCoeff, h]

/-- Literal original-entry multiplication splits into the two raw polynomials.
The algebraic identity allows arbitrary signed coefficients. -/
theorem evaluate_product_split (c : R → K → ℝ) (ν : R → K → R × C → ℕ)
    (j : C) (z : R × C → ℝ) :
    (∑ i, z (i, j) * evaluate (c i) (ν i) z) =
      evaluate (creationCoeff c ν j) (actionExponent ν j) z +
        evaluate (annihilationCoeff c ν j) (actionExponent ν j) z := by
  rw [← evaluate_extend_original_entries (fun i j => (i, j)) c ν j z]
  unfold evaluate
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _
  rw [← add_mul, creationCoeff_add_annihilationCoeff]
  rfl

/-- Complete original magnitude amplitude for one row and sign-parity set. -/
def sectionAmplitude (c : R → K → ℝ) (ν : R → K → R × C → ℕ)
    (z : R × C → ℝ) (input : R × Finset (R × C)) : ℝ :=
  evaluate (sectionCoeff (c input.1) (ν input.1) input.2) (ν input.1) z

theorem evaluate_signed_eq_inputPolynomial (c : R → K → ℝ)
    (ν : R → K → R × C → ℕ) (z : R × C → ℝ) (i : R) (σ : R × C → Bool) :
    evaluate (c i) (ν i) (fun e => Walsh.sign (σ e) * z e) =
      inputPolynomial (sectionAmplitude c ν z) i σ :=
  evaluate_sign_eq_walsh (c i) (ν i) Finset.univ (fun _ => Finset.mem_univ _) σ z

open scoped Classical in
theorem sectionAmplitude_mask (P : R → Finset (R × C) → Prop)
    (c : R → K → ℝ) (ν : R → K → R × C → ℕ) (z : R × C → ℝ) :
    sectionAmplitude (maskCoeff P c ν) ν z =
      inputMask (fun input => P input.1 input.2) (sectionAmplitude c ν z) := by
  classical
  funext input
  exact sectionCoeff_mask P c ν input.1 input.2 z

/-- Creation is original-entry multiplication of the OLD absent-flag raw mask. -/
theorem evaluate_creation (c : R → K → ℝ) (ν : R → K → R × C → ℕ)
    (j : C) (z : R × C → ℝ) :
    evaluate (creationCoeff c ν j) (actionExponent ν j) z =
      ∑ i, z (i, j) * evaluate (maskCoeff (fun i S => (i, j) ∉ S) c ν i) (ν i) z := by
  have hc : creationCoeff c ν j =
      extendCoeff (fun _ _ => 1) (maskCoeff (fun i S => (i, j) ∉ S) c ν) j := by
    funext t
    simp [creationCoeff, extendCoeff, maskCoeff]
  rw [hc]
  exact evaluate_extend_original_entries (fun i j => (i, j))
    (maskCoeff (fun i S => (i, j) ∉ S) c ν) ν j z

/-- Annihilation is original-entry multiplication of the OLD present-flag raw mask. -/
theorem evaluate_annihilation (c : R → K → ℝ) (ν : R → K → R × C → ℕ)
    (j : C) (z : R × C → ℝ) :
    evaluate (annihilationCoeff c ν j) (actionExponent ν j) z =
      ∑ i, z (i, j) * evaluate (maskCoeff (fun i S => (i, j) ∈ S) c ν i) (ν i) z := by
  have hc : annihilationCoeff c ν j =
      extendCoeff (fun _ _ => 1) (maskCoeff (fun i S => (i, j) ∈ S) c ν) j := by
    funext t
    simp [annihilationCoeff, extendCoeff, maskCoeff]
  rw [hc]
  exact evaluate_extend_original_entries (fun i j => (i, j))
    (maskCoeff (fun i S => (i, j) ∈ S) c ν) ν j z

/-- Exact signed evaluation in the creator's original coefficient model. -/
theorem evaluate_creation_signed (c : R → K → ℝ) (ν : R → K → R × C → ℕ)
    (j : C) (z : R × C → ℝ) (σ : R × C → Bool) :
    evaluate (creationCoeff c ν j) (actionExponent ν j) (fun e => Walsh.sign (σ e) * z e) =
      matrixApply z (inputMask (fun input => (input.1, j) ∉ input.2) (sectionAmplitude c ν z)) j σ := by
  rw [evaluate_creation]
  simp_rw [evaluate_signed_eq_inputPolynomial, sectionAmplitude_mask]
  unfold matrixApply
  apply Finset.sum_congr rfl
  intro i _
  simp only [inputPolynomial, Walsh.polynomial, inputMask, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  by_cases h : (i, j) ∈ S
  · simp [h]
  · simp [h]
    ring

/-- Exact signed evaluation for the direct annihilator, including the original
new magnitude occurrence on already occupied edges. -/
theorem evaluate_annihilation_signed (c : R → K → ℝ) (ν : R → K → R × C → ℕ)
    (j : C) (z : R × C → ℝ) (σ : R × C → Bool) :
    evaluate (annihilationCoeff c ν j) (actionExponent ν j) (fun e => Walsh.sign (σ e) * z e) =
      matrixApply z (inputMask (fun input => (input.1, j) ∈ input.2) (sectionAmplitude c ν z)) j σ := by
  rw [evaluate_annihilation]
  simp_rw [evaluate_signed_eq_inputPolynomial, sectionAmplitude_mask]
  unfold matrixApply
  apply Finset.sum_congr rfl
  intro i _
  simp only [inputPolynomial, Walsh.polynomial, inputMask, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  by_cases h : (i, j) ∈ S
  · simp [h]
    ring
  · simp [h]

private theorem coefficient_matrixApply_mask (z : R × C → ℝ)
    (P : R × Finset (R × C) → Prop) [DecidablePred P]
    (f : R × Finset (R × C) → ℝ) (output : C × Finset (R × C)) :
    coefficient (matrixApply z (inputMask P f) output.1) output.2 =
      ∑ input : R × Finset (R × C),
        if P input then ParityGeometry.multiplicationEntry z input output * f input else 0 := by
  have hf : inputMask (fun input => input ∈ Finset.univ.filter P) f = inputMask P f := by
    funext input
    simp [inputMask]
  have hg : matrixApply z (inputMask P f) output.1 = finiteMatrixApply z (Finset.univ.filter P) f output.1 := by
    funext σ
    rw [finiteMatrixApply_eq_matrixApply, hf]
  rw [hg, coefficient_finiteMatrixApply, Finset.sum_filter]

/-- The conditional Walsh coefficient of the new raw creator polynomial is
exactly the established creator action on ALL original section amplitudes. -/
theorem coefficient_creation (c : R → K → ℝ) (ν : R → K → R × C → ℕ)
    (z : R × C → ℝ) (output : C × Finset (R × C)) :
    coefficient
      (fun σ => evaluate (creationCoeff c ν output.1) (actionExponent ν output.1)
        (fun e => Walsh.sign (σ e) * z e)) output.2 =
      ParityGeometry.creationApply z Finset.univ (sectionAmplitude c ν z) output := by
  have heq := funext (evaluate_creation_signed c ν output.1 z)
  rw [heq, coefficient_matrixApply_mask]
  unfold ParityGeometry.creationApply
  apply Finset.sum_congr rfl
  intro input _
  by_cases h : (input.1, output.1) ∈ input.2 <;>
    simp [ParityGeometry.creationEntry, ParityGeometry.multiplicationEntry, ParityGeometry.toggle, h]

/-- The conditional Walsh coefficient of the new raw annihilator polynomial
is the established direct annihilation action, with every magnitude retained. -/
theorem coefficient_annihilation (c : R → K → ℝ) (ν : R → K → R × C → ℕ)
    (z : R × C → ℝ) (output : C × Finset (R × C)) :
    coefficient
      (fun σ => evaluate (annihilationCoeff c ν output.1) (actionExponent ν output.1)
        (fun e => Walsh.sign (σ e) * z e)) output.2 =
      ParityGeometry.annihilationApply z Finset.univ (sectionAmplitude c ν z) output := by
  have heq := funext (evaluate_annihilation_signed c ν output.1 z)
  rw [heq, coefficient_matrixApply_mask]
  unfold ParityGeometry.annihilationApply
  apply Finset.sum_congr rfl
  intro input _
  by_cases h : (input.1, output.1) ∈ input.2 <;>
    simp [ParityGeometry.annihilationEntry, ParityGeometry.multiplicationEntry, ParityGeometry.toggle, h]

/-- Actual Walsh coefficient extraction for any original raw scalar polynomial. -/
theorem coefficient_evaluate_signed {L : Type*} [Fintype L]
    (c : L → ℝ) (ν : L → R × C → ℕ) (z : R × C → ℝ) (T : Finset (R × C)) :
    coefficient (fun σ => evaluate c ν (fun e => Walsh.sign (σ e) * z e)) T =
      evaluate (sectionCoeff c ν T) ν z := by
  have heq := funext (fun σ => evaluate_sign_eq_walsh c ν Finset.univ
    (fun _ => Finset.mem_univ _) σ z)
  rw [heq, coefficient_polynomial]
  simp

/-- Raw output sections and the creator action are the same coefficient family. -/
theorem creation_section_eq (c : R → K → ℝ) (ν : R → K → R × C → ℕ)
    (z : R × C → ℝ) (output : C × Finset (R × C)) :
    evaluate (sectionCoeff (creationCoeff c ν output.1) (actionExponent ν output.1) output.2)
      (actionExponent ν output.1) z =
        ParityGeometry.creationApply z Finset.univ (sectionAmplitude c ν z) output := by
  rw [← coefficient_evaluate_signed]
  exact coefficient_creation c ν z output

/-- Raw output sections and the direct annihilator action are the same coefficient family. -/
theorem annihilation_section_eq (c : R → K → ℝ) (ν : R → K → R × C → ℕ)
    (z : R × C → ℝ) (output : C × Finset (R × C)) :
    evaluate (sectionCoeff (annihilationCoeff c ν output.1) (actionExponent ν output.1) output.2)
      (actionExponent ν output.1) z =
        ParityGeometry.annihilationApply z Finset.univ (sectionAmplitude c ν z) output := by
  rw [← coefficient_evaluate_signed]
  exact coefficient_annihilation c ν z output

end MI32.RawDirectionalActions
