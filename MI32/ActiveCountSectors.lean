import MI32.ParityGeometry
import MI32.PolynomialSectorMasks

/-!
# Active original axes of a count sector

The active set is determined by the count label, not by the magnitude
polynomial. Creation inputs have at most grade + 1 active original rows;
annihilation inputs have at most grade active original columns. Raw masks
retain every exponent, including even powers outside the active axes.
-/

noncomputable section
open scoped BigOperators

namespace MI32.ActiveCountSectors
open ParityGeometry PolynomialSectorMasks PositivePolynomial RawParity
attribute [local instance] Classical.propDecidable

variable {R C K : Type*} [Fintype R] [Fintype C] [Fintype K]
    [DecidableEq R] [DecidableEq C]

/-- Positive coordinates of a deterministic occupation-count label. -/
def support {A : Type*} [Fintype A] (d : A → ℕ) : Finset A :=
  Finset.univ.filter (fun a => 0 < d a)

@[simp] theorem mem_support {A : Type*} [Fintype A] (d : A → ℕ) (a : A) :
    a ∈ support d ↔ 0 < d a := by simp [support]

omit [Fintype C] [DecidableEq C] in
theorem support_rowCount (S : Finset (R × C)) :
    support (rowCount S) = activeRows S := by
  ext r
  simp only [mem_support, rowCount_pos_iff]

omit [Fintype R] [DecidableEq R] in
theorem support_colCount (S : Finset (R × C)) :
    support (colCount S) = activeCols S := by
  ext j
  simp only [mem_support, colCount_pos_iff]

omit [Fintype C] [DecidableEq C] in
theorem support_creationLabel (i : R) (S : Finset (R × C)) :
    support (creationLabel i S) = creationRows i S := by
  ext r
  simp only [mem_support, creationLabel_pos_iff]

omit [Fintype R] [DecidableEq R] in
theorem support_annihilationLabel (j : C) (S : Finset (R × C)) :
    support (annihilationLabel j S) = insert j (activeCols S) := by
  ext c
  simp only [mem_support, annihilationLabel_pos_iff]

omit [Fintype C] [DecidableEq C] in
/-- A nonempty creation sector uses at most one more row than its input grade. -/
theorem creation_support_card_le (d : R → ℕ) (k : ℕ)
    (hwitness : ∃ (i : R) (S : Finset (R × C)), S.card = k ∧ creationLabel i S = d) :
    (support d).card ≤ k + 1 := by
  obtain ⟨i, S, hS, rfl⟩ := hwitness
  rw [support_creationLabel, ← hS]
  exact creationRows_card_le i S

omit [Fintype R] [DecidableEq R] in
/-- The annihilation column budget is the input parity grade itself. -/
theorem annihilation_support_card_le (d : C → ℕ) (k : ℕ)
    (hwitness : ∃ S : Finset (R × C), S.card = k ∧ colCount S = d) :
    (support d).card ≤ k := by
  obtain ⟨S, hS, rfl⟩ := hwitness
  rw [support_colCount, ← hS]
  exact activeCols_card_le S

omit [Fintype C] [DecidableEq C] in
theorem creation_current_mem (i : R) (S : Finset (R × C)) (d : R → ℕ)
    (hd : creationLabel i S = d) : i ∈ support d := by
  rw [← hd, support_creationLabel]
  exact current_mem_creationRows i S

omit [Fintype R] [DecidableEq R] in
theorem annihilation_current_mem (j : C) (S : Finset (R × C)) (d : C → ℕ)
    (hd : annihilationLabel j S = d) : j ∈ support d := by
  rw [← hd, support_annihilationLabel]
  exact Finset.mem_insert_self _ _

/-- A creation sector and its input grade select original raw monomials. -/
def creationMask (k : ℕ) (d : R → ℕ) (i : R) (S : Finset (R × C)) : Prop :=
  S.card = k ∧ creationLabel i S = d

/-- The direct annihilation input mask uses original column counts. -/
def annihilationMask (k : ℕ) (d : C → ℕ) (_i : R) (S : Finset (R × C)) : Prop :=
  S.card = k ∧ colCount S = d

omit [Fintype K] [DecidableEq C] in
/-- No coefficient of a creation sector occurs at a row outside its active set. -/
theorem creation_maskCoeff_eq_zero (k : ℕ) (d : R → ℕ)
    (c : R → K → ℝ) (ν : R → K → R × C → ℕ)
    (i : R) (hi : i ∉ support d) (t : K) :
    maskCoeff (creationMask k d) c ν i t = 0 := by
  have hn : ¬ creationMask k d i (parity (ν i t)) := by
    intro h
    exact hi (creation_current_mem i _ d h.2)
  exact if_neg hn

omit [DecidableEq C] in
/-- The actual random polynomial is supported on the same original row set.
The magnitude variables themselves have not been restricted. -/
theorem creation_evaluate_eq_zero (k : ℕ) (d : R → ℕ)
    (c : R → K → ℝ) (ν : R → K → R × C → ℕ)
    (i : R) (hi : i ∉ support d) (z : R × C → ℝ) :
    evaluate (maskCoeff (creationMask k d) c ν i) (ν i) z = 0 := by
  unfold evaluate
  apply Finset.sum_eq_zero
  intro t ht
  rw [creation_maskCoeff_eq_zero k d c ν i hi t, zero_mul]

omit [Fintype K] [DecidableEq C] in
/-- If a creation raw mask is nonzero, its active row set meets the thin budget. -/
theorem creation_support_card_le_of_coeff_ne_zero (k : ℕ) (d : R → ℕ)
    (c : R → K → ℝ) (ν : R → K → R × C → ℕ)
    (i : R) (t : K) (h : maskCoeff (creationMask k d) c ν i t ≠ 0) :
    (support d).card ≤ k + 1 := by
  have hm : creationMask k d i (parity (ν i t)) := by
    by_contra hn
    exact h (if_neg hn)
  exact creation_support_card_le d k ⟨i, parity (ν i t), hm⟩

omit [Fintype K] [DecidableEq R] in
/-- If an annihilation input raw mask is nonzero, its columns meet the thin budget. -/
theorem annihilation_support_card_le_of_coeff_ne_zero (k : ℕ) (d : C → ℕ)
    (c : R → K → ℝ) (ν : R → K → R × C → ℕ)
    (i : R) (t : K) (h : maskCoeff (annihilationMask k d) c ν i t ≠ 0) :
    (support d).card ≤ k := by
  have hm : annihilationMask k d i (parity (ν i t)) := by
    by_contra hn
    exact h (if_neg hn)
  exact annihilation_support_card_le d k ⟨parity (ν i t), hm⟩

end MI32.ActiveCountSectors
