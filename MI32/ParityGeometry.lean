import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.SplitIfs

/-!
# Exact parity-count localization

Edges are the **original ordered pairs** `R × C`. An occurrence in the
opposite direction of the bipartite dilation does not create a new edge.
These results prove the discrete sector geometry of Sections 4–5 of
`docs/source/regular_law_positive_cone.md`. They are not a matrix-norm
estimate. No probability law, moment comparison, or analytic contraction
is assumed here.

Both creation and annihilation carry the same original coefficient `z (i,j)`.
Annihilation removes a parity flag, not a magnitude factor; in particular it
does not assert that ordinary polynomial degree decreases.
-/

namespace MI32.ParityGeometry

variable {R C : Type*} [DecidableEq R] [DecidableEq C]

/-- Number of original occupied edges in row `r`. -/
def rowCount (S : Finset (R × C)) (r : R) : ℕ :=
  ∑ e ∈ S, if e.1 = r then 1 else 0

/-- Number of original occupied edges in column `c`. -/
def colCount (S : Finset (R × C)) (c : C) : ℕ :=
  ∑ e ∈ S, if e.2 = c then 1 else 0

/-- Input sector label for creation from a current row. -/
def creationLabel (i : R) (S : Finset (R × C)) : R → ℕ :=
  fun r => rowCount S r + if i = r then 1 else 0

/-- Output sector label for annihilation into a current column. -/
def annihilationLabel (j : C) (S : Finset (R × C)) : C → ℕ :=
  fun c => colCount S c + if j = c then 1 else 0

def activeRows (S : Finset (R × C)) : Finset R := S.image Prod.fst

def activeCols (S : Finset (R × C)) : Finset C := S.image Prod.snd

/-- All rows needed by a creation input, including the current row. -/
def creationRows (i : R) (S : Finset (R × C)) : Finset R :=
  insert i (activeRows S)

private theorem nat_indicator_pos (p : Prop) [Decidable p] :
    0 < (if p then (1 : ℕ) else 0) ↔ p := by
  split_ifs <;> simp_all

omit [DecidableEq C] in
theorem rowCount_pos_iff (S : Finset (R × C)) (r : R) :
    0 < rowCount S r ↔ r ∈ activeRows S := by
  simp [rowCount, Finset.sum_pos_iff, activeRows, nat_indicator_pos]

omit [DecidableEq R] in
theorem colCount_pos_iff (S : Finset (R × C)) (c : C) :
    0 < colCount S c ↔ c ∈ activeCols S := by
  simp [colCount, Finset.sum_pos_iff, activeCols, nat_indicator_pos]

omit [DecidableEq C] in
theorem creationLabel_pos_iff (i : R) (S : Finset (R × C)) (r : R) :
    0 < creationLabel i S r ↔ r ∈ creationRows i S := by
  simp [creationLabel, creationRows, nat_indicator_pos,
    rowCount_pos_iff, eq_comm, or_comm]

omit [DecidableEq R] in
theorem annihilationLabel_pos_iff (j : C) (S : Finset (R × C)) (c : C) :
    0 < annihilationLabel j S c ↔ c ∈ insert j (activeCols S) := by
  simp [annihilationLabel, nat_indicator_pos, colCount_pos_iff, eq_comm, or_comm]

theorem rowCount_insert (S : Finset (R × C)) (i : R) (j : C)
    (h : (i, j) ∉ S) : rowCount (insert (i, j) S) = creationLabel i S := by
  funext r
  simp [rowCount, creationLabel, Finset.sum_insert, h, Nat.add_comm]

theorem colCount_insert (S : Finset (R × C)) (i : R) (j : C)
    (h : (i, j) ∉ S) : colCount (insert (i, j) S) = annihilationLabel j S := by
  funext c
  simp [colCount, annihilationLabel, Finset.sum_insert, h, Nat.add_comm]

theorem colCount_erase (T : Finset (R × C)) (i : R) (j : C)
    (h : (i, j) ∈ T) : colCount T = annihilationLabel j (T.erase (i, j)) := by
  simpa only [Finset.insert_erase h] using
    colCount_insert (T.erase (i, j)) i j (Finset.notMem_erase (i, j) T)

theorem activeRows_insert (S : Finset (R × C)) (i : R) (j : C) :
    activeRows (insert (i, j) S) = creationRows i S := by
  simp [activeRows, creationRows]

omit [DecidableEq C] in
theorem activeRows_card_le (S : Finset (R × C)) : (activeRows S).card ≤ S.card :=
  Finset.card_image_le

omit [DecidableEq R] in
theorem activeCols_card_le (S : Finset (R × C)) : (activeCols S).card ≤ S.card :=
  Finset.card_image_le

omit [DecidableEq C] in
theorem creationRows_card_le (i : R) (S : Finset (R × C)) :
    (creationRows i S).card ≤ S.card + 1 :=
  (Finset.card_insert_le i (activeRows S)).trans (Nat.add_le_add_right
    (activeRows_card_le S) 1)

omit [DecidableEq C] in
theorem current_mem_creationRows (i : R) (S : Finset (R × C)) :
    i ∈ creationRows i S := Finset.mem_insert_self i (activeRows S)

omit [DecidableEq C] in
theorem edge_row_mem_activeRows {S : Finset (R × C)} {e : R × C} (h : e ∈ S) :
    e.1 ∈ activeRows S := Finset.mem_image_of_mem Prod.fst h

omit [DecidableEq R] in
theorem edge_col_mem_activeCols {S : Finset (R × C)} {e : R × C} (h : e ∈ S) :
    e.2 ∈ activeCols S := Finset.mem_image_of_mem Prod.snd h

omit [DecidableEq C] in
theorem creation_input_support {S : Finset (R × C)} (i : R) {e : R × C}
    (h : e ∈ S) : e.1 ∈ creationRows i S :=
  Finset.mem_insert_of_mem (edge_row_mem_activeRows h)

theorem creation_output_support {S : Finset (R × C)} (i : R) (j : C)
    {e : R × C} (h : e ∈ insert (i, j) S) : e.1 ∈ creationRows i S := by
  rw [← activeRows_insert S i j]
  exact edge_row_mem_activeRows h

theorem annihilation_output_support {T : Finset (R × C)} (i : R) (j : C)
    {e : R × C} (h : e ∈ T.erase (i, j)) : e.2 ∈ activeCols T :=
  edge_col_mem_activeCols (Finset.mem_of_mem_erase h)

omit [DecidableEq R] in
theorem annihilation_current_support {T : Finset (R × C)} (i : R) (j : C)
    (h : (i, j) ∈ T) : j ∈ activeCols T := edge_col_mem_activeCols h

theorem creation_grade (S : Finset (R × C)) (i : R) (j : C)
    (h : (i, j) ∉ S) : (insert (i, j) S).card = S.card + 1 :=
  Finset.card_insert_of_notMem h

theorem annihilation_grade (T : Finset (R × C)) (i : R) (j : C)
    (h : (i, j) ∈ T) : (T.erase (i, j)).card + 1 = T.card :=
  Finset.card_erase_add_one h

/-- Entry of the directional creator, with the original magnitude coefficient. -/
def creationEntry (z : R × C → ℝ) (input : R × Finset (R × C))
    (output : C × Finset (R × C)) : ℝ :=
  if (input.1, output.1) ∉ input.2 ∧
      output.2 = insert (input.1, output.1) input.2
  then z (input.1, output.1) else 0

/-- Entry of the directional annihilator; it too multiplies by `z (i,j)`. -/
def annihilationEntry (z : R × C → ℝ) (input : R × Finset (R × C))
    (output : C × Finset (R × C)) : ℝ :=
  if (input.1, output.1) ∈ input.2 ∧
      output.2 = input.2.erase (input.1, output.1)
  then z (input.1, output.1) else 0

theorem creationEntry_exact (z : R × C → ℝ) (S : Finset (R × C))
    (i : R) (j : C) (h : (i, j) ∉ S) :
    creationEntry z (i, S) (j, insert (i, j) S) = z (i, j) := by
  simp [creationEntry, h]

theorem annihilationEntry_exact (z : R × C → ℝ) (T : Finset (R × C))
    (i : R) (j : C) (h : (i, j) ∈ T) :
    annihilationEntry z (i, T) (j, T.erase (i, j)) = z (i, j) := by
  simp [annihilationEntry, h]

/-- Creation is block diagonal between its exact input and output labels. -/
theorem creationEntry_eq_zero_of_label_ne (z : R × C → ℝ)
    (input : R × Finset (R × C)) (output : C × Finset (R × C))
    (h : creationLabel input.1 input.2 ≠ rowCount output.2) :
    creationEntry z input output = 0 := by
  unfold creationEntry
  split_ifs with htransition
  · exfalso
    apply h
    rw [htransition.2, rowCount_insert _ _ _ htransition.1]
  · rfl

/-- Annihilation has a distinct column-count decomposition, proved directly. -/
theorem annihilationEntry_eq_zero_of_label_ne (z : R × C → ℝ)
    (input : R × Finset (R × C)) (output : C × Finset (R × C))
    (h : colCount input.2 ≠ annihilationLabel output.1 output.2) :
    annihilationEntry z input output = 0 := by
  unfold annihilationEntry
  split_ifs with htransition
  · exfalso
    apply h
    rw [htransition.2]
    exact colCount_erase _ _ _ htransition.1
  · rfl

/-- Every output Gram block between distinct row-count labels vanishes,
even after an arbitrary finite domain restriction. -/
theorem creationGram_eq_zero_of_rowCount_ne (z : R × C → ℝ)
    (inputs : Finset (R × Finset (R × C)))
    (a b : C × Finset (R × C)) (h : rowCount a.2 ≠ rowCount b.2) :
    (∑ input ∈ inputs, creationEntry z input a * creationEntry z input b) = 0 := by
  apply Finset.sum_eq_zero
  intro input _
  by_cases ha : creationLabel input.1 input.2 = rowCount a.2
  · have hb : creationLabel input.1 input.2 ≠ rowCount b.2 := by
      rwa [ha]
    rw [creationEntry_eq_zero_of_label_ne z input b hb, mul_zero]
  · rw [creationEntry_eq_zero_of_label_ne z input a ha, zero_mul]

/-- Masking original rows keeps the coefficient on those rows exactly. -/
def restrictRows (z : R × C → ℝ) (I : Finset R) : R × C → ℝ :=
  fun e => if e.1 ∈ I then z e else 0

/-- Masking original columns keeps the coefficient on those columns exactly. -/
def restrictCols (z : R × C → ℝ) (J : Finset C) : R × C → ℝ :=
  fun e => if e.2 ∈ J then z e else 0

/-- The entire creator output block is unchanged by restriction to its
original active rows; this is an exact coefficient identity. -/
theorem creationEntry_restrictRows (z : R × C → ℝ) (I : Finset R)
    (input : R × Finset (R × C)) (output : C × Finset (R × C))
    (hI : activeRows output.2 ⊆ I) :
    creationEntry (restrictRows z I) input output = creationEntry z input output := by
  unfold creationEntry
  split_ifs with htransition
  · have hi : input.1 ∈ I := hI <| by
      rw [htransition.2, activeRows_insert]
      exact current_mem_creationRows _ _
    simp [restrictRows, hi]
  · rfl

/-- The annihilator block is unchanged by restriction to the columns of
its input flags. This is proved directly, without an adjoint argument. -/
theorem annihilationEntry_restrictCols (z : R × C → ℝ) (J : Finset C)
    (input : R × Finset (R × C)) (output : C × Finset (R × C))
    (hJ : activeCols input.2 ⊆ J) :
    annihilationEntry (restrictCols z J) input output =
      annihilationEntry z input output := by
  unfold annihilationEntry
  split_ifs with htransition
  · have hj : output.1 ∈ J := hJ (edge_col_mem_activeCols htransition.1)
    simp [restrictCols, hj]
  · rfl

/-- Toggling one original sign parity: magnitude factors are untouched. -/
def toggle (e : R × C) (S : Finset (R × C)) : Finset (R × C) :=
  if e ∈ S then S.erase e else insert e S

/-- The directional entry of actual original-coordinate multiplication
after sign parity expansion. This defines the coefficient formula; the
probabilistic Fourier equivalence is a separate analytic obligation. -/
def multiplicationEntry (z : R × C → ℝ) (input : R × Finset (R × C))
    (output : C × Finset (R × C)) : ℝ :=
  if output.2 = toggle (input.1, output.1) input.2
  then z (input.1, output.1) else 0

theorem multiplicationEntry_eq_creation_add_annihilation (z : R × C → ℝ)
    (input : R × Finset (R × C)) (output : C × Finset (R × C)) :
    multiplicationEntry z input output =
      creationEntry z input output + annihilationEntry z input output := by
  by_cases h : (input.1, output.1) ∈ input.2 <;>
    simp [multiplicationEntry, toggle, creationEntry, annihilationEntry, h]

/-- Creation is exactly the projection to the next parity grade of the
original multiplication entry. -/
theorem creationEntry_eq_grade_compression (z : R × C → ℝ)
    (input : R × Finset (R × C)) (output : C × Finset (R × C)) :
    creationEntry z input output =
      if output.2.card = input.2.card + 1
      then multiplicationEntry z input output else 0 := by
  by_cases he : (input.1, output.1) ∈ input.2
  · have hc : creationEntry z input output = 0 := by simp [creationEntry, he]
    rw [hc]
    by_cases hg : output.2.card = input.2.card + 1
    · have hne : output.2 ≠ input.2.erase (input.1, output.1) := by
        intro hEq
        have hc := annihilation_grade input.2 input.1 output.1 he
        rw [← hEq] at hc
        omega
      simp [hg, multiplicationEntry, toggle, he, hne]
    · simp [hg]
  · by_cases ht : output.2 = insert (input.1, output.1) input.2
    · have hg : output.2.card = input.2.card + 1 := by
        rw [ht]
        exact creation_grade _ _ _ he
      rw [if_pos hg]
      simp [creationEntry, multiplicationEntry, toggle, he, ht]
    · simp [creationEntry, multiplicationEntry, toggle, he, ht]

/-- Annihilation is exactly the previous-parity-grade projection; no
claim about decreasing original polynomial degree is made. -/
theorem annihilationEntry_eq_grade_compression (z : R × C → ℝ)
    (input : R × Finset (R × C)) (output : C × Finset (R × C)) :
    annihilationEntry z input output =
      if output.2.card + 1 = input.2.card
      then multiplicationEntry z input output else 0 := by
  by_cases he : (input.1, output.1) ∈ input.2
  · by_cases ht : output.2 = input.2.erase (input.1, output.1)
    · have hg : output.2.card + 1 = input.2.card := by
        rw [ht]
        exact annihilation_grade _ _ _ he
      rw [if_pos hg]
      simp [annihilationEntry, multiplicationEntry, toggle, he, ht]
    · simp [annihilationEntry, multiplicationEntry, toggle, he, ht]
  · have hc : annihilationEntry z input output = 0 := by simp [annihilationEntry, he]
    rw [hc]
    by_cases hg : output.2.card + 1 = input.2.card
    · have hne : output.2 ≠ insert (input.1, output.1) input.2 := by
        intro hEq
        have hc := creation_grade input.2 input.1 output.1 he
        rw [← hEq] at hc
        omega
      simp [hg, multiplicationEntry, toggle, he, hne]
    · simp [hg]

/-- Exact finite creator action. Amplitudes are arbitrary: in particular,
when applied pointwise they can depend on every original magnitude. -/
def creationApply (z : R × C → ℝ) (inputs : Finset (R × Finset (R × C)))
    (f : R × Finset (R × C) → ℝ) (output : C × Finset (R × C)) : ℝ :=
  ∑ input ∈ inputs, creationEntry z input output * f input

def annihilationApply (z : R × C → ℝ) (inputs : Finset (R × Finset (R × C)))
    (f : R × Finset (R × C) → ℝ) (output : C × Finset (R × C)) : ℝ :=
  ∑ input ∈ inputs, annihilationEntry z input output * f input

open scoped Classical in
/-- The complete creator sum keeps exactly the input sector belonging
to the output row-count label. This is an identity, not an estimate. -/
theorem creationApply_eq_label_sum (z : R × C → ℝ)
    (inputs : Finset (R × Finset (R × C)))
    (f : R × Finset (R × C) → ℝ) (output : C × Finset (R × C)) :
    creationApply z inputs f output =
      ∑ input ∈ inputs, if creationLabel input.1 input.2 = rowCount output.2
        then creationEntry z input output * f input else 0 := by
  unfold creationApply
  apply Finset.sum_congr rfl
  intro input _
  by_cases h : creationLabel input.1 input.2 = rowCount output.2
  · simp [h]
  · simp [h, creationEntry_eq_zero_of_label_ne z input output h]

open scoped Classical in
/-- The direct annihilator action keeps the column-count sector. -/
theorem annihilationApply_eq_label_sum (z : R × C → ℝ)
    (inputs : Finset (R × Finset (R × C)))
    (f : R × Finset (R × C) → ℝ) (output : C × Finset (R × C)) :
    annihilationApply z inputs f output =
      ∑ input ∈ inputs, if colCount input.2 = annihilationLabel output.1 output.2
        then annihilationEntry z input output * f input else 0 := by
  unfold annihilationApply
  apply Finset.sum_congr rfl
  intro input _
  by_cases h : colCount input.2 = annihilationLabel output.1 output.2
  · simp [h]
  · simp [h, annihilationEntry_eq_zero_of_label_ne z input output h]

theorem creationApply_restrictRows (z : R × C → ℝ) (I : Finset R)
    (inputs : Finset (R × Finset (R × C)))
    (f : R × Finset (R × C) → ℝ) (output : C × Finset (R × C))
    (hI : activeRows output.2 ⊆ I) :
    creationApply (restrictRows z I) inputs f output =
      creationApply z inputs f output := by
  unfold creationApply
  apply Finset.sum_congr rfl
  intro input _
  rw [creationEntry_restrictRows z I input output hI]

theorem annihilationApply_restrictCols (z : R × C → ℝ) (J : Finset C)
    (inputs : Finset (R × Finset (R × C)))
    (f : R × Finset (R × C) → ℝ) (output : C × Finset (R × C))
    (hJ : ∀ input ∈ inputs, activeCols input.2 ⊆ J) :
    annihilationApply (restrictCols z J) inputs f output =
      annihilationApply z inputs f output := by
  unfold annihilationApply
  apply Finset.sum_congr rfl
  intro input hinput
  rw [annihilationEntry_restrictCols z J input output (hJ input hinput)]

end MI32.ParityGeometry
