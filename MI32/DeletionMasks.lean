import MI32.NestedDeletionFamily
import MI32.NestedShells
import MI32.FiberBlockNorm
import MI32.MaskedEntryLaw

/-!
# The four deterministic entry masks of the symmetric deletion decomposition

Every original index carries the shell label of the explicit nested deletion
family. The label splits the entries of the original matrix into five
deterministic masks: the full block on the first two shells, the remaining
even two-shell diagonal blocks, the odd two-shell cross rectangles, and the
two far orientations. The split is an exact pointwise identity, so the
original operator norm is bounded by the sum of the five mask norms.

The two near masks are supported on the diagonal blocks of the fibers of the
even and odd block colourings, and each fiber block is identified with a fiber
block of the original matrix: exactly on the even side away from the initial
block, and up to a two-colour off-diagonal contraction on the odd side.

Everything in this module is deterministic bookkeeping about the shell
labels. No probabilistic estimate appears.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open MeasureTheory

namespace MI32.DeletionMasks

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {n : ℕ}
  (X : Ω → Matrix (Fin n) (Fin n) ℝ)

/-! ### The shell label and the two block colourings -/

/-- The shell label of an original index. -/
def label (μ : Measure Ω) (X : Ω → Matrix (Fin n) (Fin n) ℝ) (i : Fin n) : ℕ :=
  (NestedDeletionFamily.level μ X i).val

/-- The shell label never exceeds the finite horizon. -/
theorem label_lt (μ : Measure Ω) (X : Ω → Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    label μ X i < n + 2 :=
  (NestedDeletionFamily.level μ X i).isLt

/-- Cumulative shell membership is exactly the scheduled nested set. -/
theorem label_le_iff (r : ℕ) (i : Fin n) :
    label μ X i ≤ r ↔ i ∈ NestedDeletionFamily.sets μ X r :=
  NestedDeletionFamily.level_le_iff r i

/-- The block index of the even two-shell family. -/
def cEven (μ : Measure Ω) (X : Ω → Matrix (Fin n) (Fin n) ℝ) (i : Fin n) : Fin (n + 2) :=
  ⟨label μ X i / 2, by have h := label_lt μ X i; omega⟩

/-- The block index of the odd two-shell family. -/
def cOdd (μ : Measure Ω) (X : Ω → Matrix (Fin n) (Fin n) ℝ) (i : Fin n) : Fin (n + 2) :=
  ⟨(label μ X i + 1) / 2, by have h := label_lt μ X i; omega⟩

/-- The value of the even block index. -/
@[simp] theorem val_cEven (i : Fin n) : (cEven μ X i).val = label μ X i / 2 := rfl

/-- The value of the odd block index. -/
@[simp] theorem val_cOdd (i : Fin n) : (cOdd μ X i).val = (label μ X i + 1) / 2 := rfl

/-- Two indices share an even block exactly when their halved labels agree. -/
theorem cEven_eq_iff (i j : Fin n) :
    cEven μ X i = cEven μ X j ↔ label μ X i / 2 = label μ X j / 2 := by
  rw [← Fin.val_inj, val_cEven, val_cEven]

/-- Two indices share an odd block exactly when their shifted halved labels agree. -/
theorem cOdd_eq_iff (i j : Fin n) :
    cOdd μ X i = cOdd μ X j ↔ (label μ X i + 1) / 2 = (label μ X j + 1) / 2 := by
  rw [← Fin.val_inj, val_cOdd, val_cOdd]

/-- The initial even block collects exactly the first two shells. -/
theorem cEven_eq_zero_iff (i : Fin n) : cEven μ X i = 0 ↔ label μ X i ≤ 1 := by
  rw [← Fin.val_inj, val_cEven]
  simp only [Fin.val_zero]
  omega

/-- The initial odd block collects exactly the first shell. -/
theorem cOdd_eq_zero_iff (i : Fin n) : cOdd μ X i = 0 ↔ label μ X i = 0 := by
  rw [← Fin.val_inj, val_cOdd]
  simp only [Fin.val_zero]
  omega

/-! ### The five deterministic masks -/

/-- The initial full block on the first two shells. -/
def nearLow (μ : Measure Ω) (X : Ω → Matrix (Fin n) (Fin n) ℝ) (ω : Ω) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of (fun i j => if cEven μ X i = 0 ∧ cEven μ X j = 0 then X ω i j else 0)

/-- The remaining even two-shell blocks. -/
def nearHigh (μ : Measure Ω) (X : Ω → Matrix (Fin n) (Fin n) ℝ) (ω : Ω) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of (fun i j => if cEven μ X i = cEven μ X j ∧ cEven μ X i ≠ 0 then X ω i j else 0)

/-- The odd family: only the cross rectangles of two adjacent shells. -/
def nearCross (μ : Measure Ω) (X : Ω → Matrix (Fin n) (Fin n) ℝ) (ω : Ω) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of (NestedShells.nearOdd (label μ X) (X ω))

/-- The lower far orientation. -/
def farLow (μ : Measure Ω) (X : Ω → Matrix (Fin n) (Fin n) ℝ) (ω : Ω) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of (NestedShells.farLower (label μ X) (X ω))

/-- The upper far orientation. -/
def farUp (μ : Measure Ω) (X : Ω → Matrix (Fin n) (Fin n) ℝ) (ω : Ω) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of (NestedShells.farUpper (label μ X) (X ω))

/-! ### The exact pointwise partition -/

/-- The even two-shell mask is the sum of the initial block and the remaining blocks. -/
theorem nearEven_split (ω : Ω) (i j : Fin n) :
    NestedShells.nearEven (label μ X) (X ω) i j
      = nearLow μ X ω i j + nearHigh μ X ω i j := by
  simp only [nearLow, nearHigh, Matrix.of_apply, NestedShells.nearEven, ne_eq,
    cEven_eq_iff, cEven_eq_zero_iff]
  split_ifs <;> first | omega | ring

/-- Exact pointwise partition of the original entries. -/
theorem entry_sum (ω : Ω) (i j : Fin n) :
    X ω i j = nearLow μ X ω i j + nearHigh μ X ω i j + nearCross μ X ω i j
      + farLow μ X ω i j + farUp μ X ω i j := by
  conv_lhs => rw [NestedShells.entry_partition (label μ X) (X ω) i j]
  rw [nearEven_split X ω i j]
  simp only [nearCross, farLow, farUp, Matrix.of_apply]

/-- The original matrix is the sum of the five deterministic masks. -/
theorem matrix_sum (ω : Ω) :
    X ω = nearLow μ X ω + nearHigh μ X ω + nearCross μ X ω + farLow μ X ω
      + farUp μ X ω := by
  ext i j
  simp only [Matrix.add_apply]
  exact entry_sum X ω i j

/-- Consequently the original norm splits into the five deterministic masks. -/
theorem norm_le_masks (ω : Ω) :
    ‖X ω‖ ≤ ‖nearLow μ X ω‖ + ‖nearHigh μ X ω‖ + ‖nearCross μ X ω‖
      + ‖farLow μ X ω‖ + ‖farUp μ X ω‖ := by
  rw [matrix_sum X ω]
  have h2 : ‖nearLow μ X ω + nearHigh μ X ω‖ ≤ ‖nearLow μ X ω‖ + ‖nearHigh μ X ω‖ :=
    norm_add_le _ _
  have h3 : ‖nearLow μ X ω + nearHigh μ X ω + nearCross μ X ω‖
      ≤ ‖nearLow μ X ω‖ + ‖nearHigh μ X ω‖ + ‖nearCross μ X ω‖ :=
    (norm_add_le _ _).trans (add_le_add h2 le_rfl)
  have h4 : ‖nearLow μ X ω + nearHigh μ X ω + nearCross μ X ω + farLow μ X ω‖
      ≤ ‖nearLow μ X ω‖ + ‖nearHigh μ X ω‖ + ‖nearCross μ X ω‖ + ‖farLow μ X ω‖ :=
    (norm_add_le _ _).trans (add_le_add h3 le_rfl)
  exact (norm_add_le _ _).trans (add_le_add h4 le_rfl)

/-! ### Support properties -/

/-- The initial block lives on the first selected set. -/
theorem nearLow_support (ω : Ω) (i j : Fin n)
    (hi : i ∉ NestedDeletionFamily.sets μ X 1) : nearLow μ X ω i j = 0 := by
  have h : ¬ label μ X i ≤ 1 := fun hle => hi ((label_le_iff (μ := μ) X 1 i).mp hle)
  have hc : ¬ (cEven μ X i = 0 ∧ cEven μ X j = 0) :=
    fun hcc => h ((cEven_eq_zero_iff X i).mp hcc.1)
  simp only [nearLow, Matrix.of_apply, if_neg hc]

/-- The remaining even family is supported on the diagonal blocks of its fibers. -/
theorem nearHigh_fiber_supported (ω : Ω) (i j : Fin n) (h : cEven μ X i ≠ cEven μ X j) :
    nearHigh μ X ω i j = 0 := by
  have hc : ¬ (cEven μ X i = cEven μ X j ∧ cEven μ X i ≠ 0) := fun hcc => h hcc.1
  simp only [nearHigh, Matrix.of_apply, if_neg hc]

/-- The odd family is supported on the diagonal blocks of its fibers. -/
theorem nearCross_fiber_supported (ω : Ω) (i j : Fin n) (h : cOdd μ X i ≠ cOdd μ X j) :
    nearCross μ X ω i j = 0 := by
  have hne : ¬ (label μ X i + 1) / 2 = (label μ X j + 1) / 2 := fun he =>
    h ((cOdd_eq_iff X i j).mpr he)
  have hc : ¬ ((label μ X i + 1) / 2 = (label μ X j + 1) / 2
      ∧ label μ X i ≠ label μ X j) := fun hcc => hne hcc.1
  simp only [nearCross, Matrix.of_apply, NestedShells.nearOdd, if_neg hc]

/-! ### Admissible labels inside a fiber -/

/-- The admissible labels inside an even fiber. -/
theorem cEven_fiber_label (k : Fin (n + 2)) (i : Fin n) (h : cEven μ X i = k) :
    label μ X i = 2 * k.val ∨ label μ X i = 2 * k.val + 1 := by
  have h1 : label μ X i / 2 = k.val := by rw [← val_cEven X i, h]
  omega

/-- The admissible labels inside an odd fiber, away from the initial one. -/
theorem cOdd_fiber_label (k : Fin (n + 2)) (hk : k ≠ 0) (i : Fin n) (h : cOdd μ X i = k) :
    label μ X i = 2 * k.val - 1 ∨ label μ X i = 2 * k.val := by
  have h1 : (label μ X i + 1) / 2 = k.val := by rw [← val_cOdd X i, h]
  have h2 : k.val ≠ 0 := fun hz => hk (by ext; simpa using hz)
  omega

/-! ### Identification of the near fiber blocks -/

/-- Away from the initial block the even family's fiber block is the original one. -/
theorem blockSub_nearHigh_eq (ω : Ω) (k : Fin (n + 2)) (hk : k ≠ 0) :
    FiberBlockNorm.blockSub (nearHigh μ X ω) (cEven μ X) k
      = FiberBlockNorm.blockSub (X ω) (cEven μ X) k := by
  ext i j
  have hc : cEven μ X i.val = cEven μ X j.val ∧ cEven μ X i.val ≠ 0 :=
    ⟨i.2.trans j.2.symm, by rw [i.2]; exact hk⟩
  simp only [FiberBlockNorm.blockSub_apply, nearHigh, Matrix.of_apply, if_pos hc]

/-- The initial even fiber block of the remaining family vanishes. -/
theorem blockSub_nearHigh_zero (ω : Ω) :
    FiberBlockNorm.blockSub (nearHigh μ X ω) (cEven μ X) 0 = 0 := by
  ext i j
  have hc : ¬ (cEven μ X i.val = cEven μ X j.val ∧ cEven μ X i.val ≠ 0) :=
    fun hcc => hcc.2 i.2
  simp only [FiberBlockNorm.blockSub_apply, nearHigh, Matrix.of_apply, if_neg hc,
    Matrix.zero_apply]

/-- The initial odd fiber block of the cross family vanishes. -/
theorem blockSub_nearCross_zero (ω : Ω) :
    FiberBlockNorm.blockSub (nearCross μ X ω) (cOdd μ X) 0 = 0 := by
  ext i j
  have hi : label μ X i.val = 0 := (cOdd_eq_zero_iff X i.val).mp i.2
  have hj : label μ X j.val = 0 := (cOdd_eq_zero_iff X j.val).mp j.2
  have hc : ¬ ((label μ X i.val + 1) / 2 = (label μ X j.val + 1) / 2
      ∧ label μ X i.val ≠ label μ X j.val) := by omega
  simp only [FiberBlockNorm.blockSub_apply, nearCross, Matrix.of_apply,
    NestedShells.nearOdd, if_neg hc, Matrix.zero_apply]

/-- Each odd fiber block is the two-colour off-diagonal part of the original
fiber block, the colour being the parity of the shell label. -/
theorem blockSub_nearCross_eq (ω : Ω) (k : Fin (n + 2)) :
    FiberBlockNorm.blockSub (nearCross μ X ω) (cOdd μ X) k
      = Matrix.of (fun i j : {v : Fin n // cOdd μ X v = k} =>
          if decide (label μ X i.val % 2 = 1) = decide (label μ X j.val % 2 = 1)
          then (0 : ℝ) else FiberBlockNorm.blockSub (X ω) (cOdd μ X) k i j) := by
  ext i j
  have hi : (label μ X i.val + 1) / 2 = k.val := by rw [← val_cOdd X i.val, i.2]
  have hj : (label μ X j.val + 1) / 2 = k.val := by rw [← val_cOdd X j.val, j.2]
  simp only [FiberBlockNorm.blockSub_apply, nearCross, Matrix.of_apply,
    NestedShells.nearOdd, decide_eq_decide, ne_eq]
  split_ifs <;> first | omega | rfl

/-- Each odd fiber block is a two-colour off-diagonal part of the original
fiber block, so its norm is not larger. -/
theorem norm_blockSub_nearCross_le (ω : Ω) (k : Fin (n + 2)) :
    ‖FiberBlockNorm.blockSub (nearCross μ X ω) (cOdd μ X) k‖
      ≤ ‖FiberBlockNorm.blockSub (X ω) (cOdd μ X) k‖ := by
  rw [blockSub_nearCross_eq X ω k]
  exact FiberBlockNorm.norm_offDiagonal_le _
    (fun v : {v : Fin n // cOdd μ X v = k} => decide (label μ X v.val % 2 = 1))

/-! ### The far masks as deterministic zero-one masks -/

/-- The lower far mask is a deterministic zero-one mask of the original entries. -/
theorem farLow_eq_masked (ω : Ω) (i j : Fin n) :
    farLow μ X ω i j =
      MaskedEntryLaw.masked (fun a b => decide (label μ X b + 1 < label μ X a))
        (fun a b ω => X ω a b) i j ω := by
  simp only [farLow, Matrix.of_apply, NestedShells.farLower, MaskedEntryLaw.masked,
    decide_eq_true_eq]

/-- The upper far mask is the transpose of a deterministic zero-one mask of the
original entries. -/
theorem farUp_eq_masked_transpose (ω : Ω) (i j : Fin n) :
    farUp μ X ω i j =
      MaskedEntryLaw.masked (fun a b => decide (label μ X b + 1 < label μ X a))
        (fun a b ω => X ω b a) j i ω := by
  simp only [farUp, Matrix.of_apply, NestedShells.farUpper, MaskedEntryLaw.masked,
    decide_eq_true_eq]

end MI32.DeletionMasks
