import MI32.ActiveCountSectors
import MI32.PositiveWordExtension
import MI32.ParityWalshCompression
import MI32.RawDirectionalActions

/-!
# Exact count-sector identities for raw directional polynomial actions

The predicates below track only the original sign parity and original row or
column counts. The raw exponent family is not changed by any mask. Creation
and annihilation both append the same original variable to the raw word.
-/

noncomputable section
open scoped BigOperators symmDiff

namespace MI32.RawCountBlocks

open PositivePolynomial RawParity PositiveWordExtension
open PolynomialSectorMasks ActiveCountSectors ParityGeometry
open RawDirectionalActions
attribute [local instance] Classical.propDecidable

variable {R C K : Type*} [Fintype R] [Fintype C] [DecidableEq R] [DecidableEq C]

/-- The creator output carries grade `k+1` and its original row-count label. -/
def creationOutputMask (k : ℕ) (δ : R → ℕ) (_j : C) (S : Finset (R × C)) : Prop :=
  S.card = k + 1 ∧ rowCount S = δ

/-- The annihilator output carries the predecessor grade and the original
column count recovered by reinstating its current output column. -/
def annihilationOutputMask (k : ℕ) (δ : C → ℕ) (j : C) (S : Finset (R × C)) : Prop :=
  S.card + 1 = k ∧ annihilationLabel j S = δ

omit [Fintype R] [Fintype C] in
theorem creationOutputMask_toggle_iff (k : ℕ) (δ : R → ℕ)
    (i : R) (j : C) (S : Finset (R × C)) (h : (i, j) ∉ S) :
    creationOutputMask k δ j (toggle (i, j) S) ↔ creationMask k δ i S := by
  simp only [creationOutputMask, creationMask, toggle, if_neg h,
    creation_grade S i j h, rowCount_insert S i j h, Nat.add_left_inj]

omit [Fintype R] [Fintype C] in
theorem annihilationOutputMask_toggle_iff (k : ℕ) (δ : C → ℕ)
    (i : R) (j : C) (S : Finset (R × C)) (h : (i, j) ∈ S) :
    annihilationOutputMask k δ j (toggle (i, j) S) ↔ annihilationMask k δ i S := by
  simp only [annihilationOutputMask, annihilationMask, toggle, if_pos h,
    annihilation_grade S i j h, ← colCount_erase S i j h]

omit [Fintype R] [Fintype C] in
/-- At one fixed input grade, raising the parity grade is precisely creation. -/
theorem toggle_grade_up_iff (k : ℕ) (i : R) (j : C) (S : Finset (R × C))
    (hS : S.card = k) : (toggle (i, j) S).card = k + 1 ↔ (i, j) ∉ S := by
  by_cases h : (i, j) ∈ S
  · have hc := annihilation_grade S i j h
    rw [toggle, if_pos h]
    constructor
    · intro he
      omega
    · intro hn
      exact False.elim (hn h)
  · rw [toggle, if_neg h, creation_grade S i j h, hS]
    exact iff_of_true rfl h

omit [Fintype R] [Fintype C] in
/-- At one fixed input grade, lowering the parity grade is precisely annihilation.
The `card+1=k` form also handles the empty input grade without truncation issues. -/
theorem toggle_grade_down_iff (k : ℕ) (i : R) (j : C) (S : Finset (R × C))
    (hS : S.card = k) : (toggle (i, j) S).card + 1 = k ↔ (i, j) ∈ S := by
  by_cases h : (i, j) ∈ S
  · rw [toggle, if_pos h, annihilation_grade S i j h, hS]
    exact iff_of_true rfl h
  · have hc := creation_grade S i j h
    rw [toggle, if_neg h]
    constructor
    · intro he
      omega
    · intro hm
      exact False.elim (h hm)

/-- A creator output block is exactly the creator applied to its matching
input creation-count sector. The equality is at every original raw term. -/
theorem creation_count_block (c : R → K → ℝ) (ν : R → K → R × C → ℕ)
    (k : ℕ) (δ : R → ℕ) :
    maskCoeff (creationOutputMask k δ) (creationCoeff c ν) (actionExponent ν) =
      creationCoeff (maskCoeff (creationMask k δ) c ν) ν := by
  funext j t
  by_cases h : (t.1, j) ∉ parity (ν t.1 t.2)
  · have hm := creationOutputMask_toggle_iff k δ t.1 j (parity (ν t.1 t.2)) h
    simp only [maskCoeff, creationCoeff, parity_actionExponent, if_pos h, hm]
  · simp only [maskCoeff, creationCoeff, if_neg h, ite_self]

/-- The annihilator's matching input sector is selected by original column
counts. Its output count label reinstates the current column. -/
theorem annihilation_count_block (c : R → K → ℝ) (ν : R → K → R × C → ℕ)
    (k : ℕ) (δ : C → ℕ) :
    maskCoeff (annihilationOutputMask k δ) (annihilationCoeff c ν) (actionExponent ν) =
      annihilationCoeff (maskCoeff (annihilationMask k δ) c ν) ν := by
  funext j t
  by_cases h : (t.1, j) ∈ parity (ν t.1 t.2)
  · have hm := annihilationOutputMask_toggle_iff k δ t.1 j (parity (ν t.1 t.2)) h
    simp only [maskCoeff, annihilationCoeff, parity_actionExponent, if_pos h, hm]
  · simp [maskCoeff, annihilationCoeff, h]

/-- On one creation input sector, the next-grade projection of full original
multiplication is precisely the raw creator. No magnitude variable is removed. -/
theorem creation_grade_compression (c : R → K → ℝ) (ν : R → K → R × C → ℕ)
    (k : ℕ) (δ : R → ℕ) :
    maskCoeff (fun (_j : C) T => T.card = k + 1)
        (extendCoeff (fun _ _ => 1) (maskCoeff (creationMask k δ) c ν)) (actionExponent ν) =
      creationCoeff (maskCoeff (creationMask k δ) c ν) ν := by
  funext j t
  by_cases h : creationMask k δ t.1 (parity (ν t.1 t.2))
  · have hg := toggle_grade_up_iff k t.1 j (parity (ν t.1 t.2)) h.1
    simp only [maskCoeff, extendCoeff, one_mul, creationCoeff, parity_actionExponent,
      if_pos h, hg]
  · simp [maskCoeff, extendCoeff, creationCoeff, h]

/-- On one annihilation input sector, the previous-grade projection of full
original multiplication is precisely the raw annihilator. -/
theorem annihilation_grade_compression (c : R → K → ℝ) (ν : R → K → R × C → ℕ)
    (k : ℕ) (δ : C → ℕ) :
    maskCoeff (fun (_j : C) T => T.card + 1 = k)
        (extendCoeff (fun _ _ => 1) (maskCoeff (annihilationMask k δ) c ν)) (actionExponent ν) =
      annihilationCoeff (maskCoeff (annihilationMask k δ) c ν) ν := by
  funext j t
  by_cases h : annihilationMask k δ t.1 (parity (ν t.1 t.2))
  · have hg := toggle_grade_down_iff k t.1 j (parity (ν t.1 t.2)) h.1
    simp only [maskCoeff, extendCoeff, one_mul, annihilationCoeff, parity_actionExponent,
      if_pos h, hg]
  · simp [maskCoeff, extendCoeff, annihilationCoeff, h]

/-- The matching creation count label is automatic after the raw creation
step on its input sector; the output mask removes no additional term. -/
theorem creation_output_mask_invariant (c : R → K → ℝ) (ν : R → K → R × C → ℕ)
    (k : ℕ) (δ : R → ℕ) :
    maskCoeff (creationOutputMask k δ)
        (creationCoeff (maskCoeff (creationMask k δ) c ν) ν) (actionExponent ν) =
      creationCoeff (maskCoeff (creationMask k δ) c ν) ν := by
  rw [creation_count_block, maskCoeff_comp]
  simp only [and_self]

/-- The matching annihilation count label is likewise automatic on its sector. -/
theorem annihilation_output_mask_invariant (c : R → K → ℝ) (ν : R → K → R × C → ℕ)
    (k : ℕ) (δ : C → ℕ) :
    maskCoeff (annihilationOutputMask k δ)
        (annihilationCoeff (maskCoeff (annihilationMask k δ) c ν) ν) (actionExponent ν) =
      annihilationCoeff (maskCoeff (annihilationMask k δ) c ν) ν := by
  rw [annihilation_count_block, maskCoeff_comp]
  simp only [and_self]

/-- The full-multiplication output block is the raw creator on its input sector,
with both the next grade and the matching count label imposed explicitly. -/
theorem creation_full_block (c : R → K → ℝ) (ν : R → K → R × C → ℕ)
    (k : ℕ) (δ : R → ℕ) :
    maskCoeff (creationOutputMask k δ)
        (extendCoeff (fun _ _ => 1) (maskCoeff (creationMask k δ) c ν)) (actionExponent ν) =
      creationCoeff (maskCoeff (creationMask k δ) c ν) ν := by
  rw [← creation_output_mask_invariant c ν k δ, ← creation_grade_compression,
    maskCoeff_comp]
  funext j t
  by_cases hg : (parity (actionExponent ν j t)).card = k + 1 <;>
    simp only [maskCoeff, creationOutputMask, hg, true_and, false_and, if_false]

/-- The corresponding full-multiplication block is the raw annihilator,
with both the previous grade and the matching column label imposed explicitly. -/
theorem annihilation_full_block (c : R → K → ℝ) (ν : R → K → R × C → ℕ)
    (k : ℕ) (δ : C → ℕ) :
    maskCoeff (annihilationOutputMask k δ)
        (extendCoeff (fun _ _ => 1) (maskCoeff (annihilationMask k δ) c ν)) (actionExponent ν) =
      annihilationCoeff (maskCoeff (annihilationMask k δ) c ν) ν := by
  rw [← annihilation_output_mask_invariant c ν k δ, ← annihilation_grade_compression,
    maskCoeff_comp]
  funext j t
  by_cases hg : (parity (actionExponent ν j t)).card + 1 = k <;>
    simp only [maskCoeff, annihilationOutputMask, hg, true_and, false_and, if_false]

end MI32.RawCountBlocks
