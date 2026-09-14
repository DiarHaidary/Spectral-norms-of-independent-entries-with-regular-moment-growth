import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Matrix.Hadamard
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Finite crossed-edges identities

These lemmas formalize the injective entries and exact label exclusions in
Sections 1 and 3 of report 63. They do not assert the probabilistic norm limit.
-/

namespace GraphMatrices.CrossedEdges

open scoped BigOperators

/-- All four ordered boundary labels are distinct. -/
def BoundaryDistinct {n : ℕ} (a b c d : Fin n) : Prop :=
  a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d

instance {n : ℕ} (a b c d : Fin n) : Decidable (BoundaryDistinct a b c d) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

/-- The interior-label sum, excluding every boundary label. -/
def interiorSum {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) (a b c d : Fin n) : ℝ :=
  ∑ e : Fin n, if e ≠ a ∧ e ≠ b ∧ e ≠ c ∧ e ≠ d then W a e * W e d else 0

/-- The actual crossed-edges matrix, padded by zero on noninjective boundaries. -/
def crossedMatrix {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n × Fin n) (Fin n × Fin n) ℝ :=
  fun r s => if BoundaryDistinct r.1 r.2 s.1 s.2 then
    W r.1 s.1 * W r.2 s.2 * interiorSum W r.1 r.2 s.1 s.2 else 0

/-- Excluding the four boundary labels subtracts exactly the two nonzero terms. -/
theorem interiorSum_eq_square_sub {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ)
    (hdiag : ∀ i, W i i = 0) (a b c d : Fin n)
    (h : BoundaryDistinct a b c d) :
    interiorSum W a b c d = (W * W) a d - W a b * W b d - W a c * W c d := by
  rcases h with ⟨hab, hac, had, hbc, hbd, hcd⟩
  have hpoint (e : Fin n) :
      (if e ≠ a ∧ e ≠ b ∧ e ≠ c ∧ e ≠ d then W a e * W e d else 0) +
      (if e = b then W a b * W b d else 0) +
      (if e = c then W a c * W c d else 0) = W a e * W e d := by
    by_cases hea : e = a
    · subst e
      simp [hdiag, hab, hac]
    by_cases heb : e = b
    · subst e
      simp [hbc]
    by_cases hec : e = c
    · subst e
      simp [Ne.symm hbc]
    by_cases hed : e = d
    · subst e
      simp [hdiag, Ne.symm hbd, Ne.symm hcd]
    simp [hea, heb, hec, hed]
  have hs := congrArg (fun f : Fin n → ℝ => ∑ e, f e) (funext hpoint)
  simp only [Finset.sum_add_distrib] at hs
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true] at hs
  change interiorSum W a b c d + W a b * W b d + W a c * W c d =
    (W * W) a d at hs
  linarith

/-- Entry formula before the sign-square simplifications. -/
theorem crossedMatrix_entry {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ)
    (hdiag : ∀ i, W i i = 0) (a b c d : Fin n)
    (h : BoundaryDistinct a b c d) :
    crossedMatrix W (a, b) (c, d) = W a c * W b d *
      ((W * W) a d - W a b * W b d - W a c * W c d) := by
  simp only [crossedMatrix, h, if_true]
  rw [interiorSum_eq_square_sub W hdiag a b c d h]

/-- The sign assumptions cancel the two excluded-edge squares. -/
theorem crossedMatrix_entry_sign {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ)
    (hdiag : ∀ i, W i i = 0) (hsign : ∀ i j, i ≠ j → (W i j) ^ 2 = 1)
    (a b c d : Fin n) (h : BoundaryDistinct a b c d) :
    crossedMatrix W (a, b) (c, d) =
      W a c * W b d * (W * W) a d - W a b * W a c - W c d * W b d := by
  rw [crossedMatrix_entry W hdiag a b c d h]
  have hac := hsign a c h.2.1
  have hbd := hsign b d h.2.2.2.2.1
  calc
    _ = W a c * W b d * (W * W) a d -
        (W a b * W a c) * (W b d) ^ 2 -
        (W c d * W b d) * (W a c) ^ 2 := by ring
    _ = _ := by rw [hac, hbd]; ring

/-- Fixed endpoints give the localized block in report 63, with its diagonal
deleted because the remaining row and column labels must also be distinct. -/
theorem localized_block_entry {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ)
    (hdiag : ∀ i, W i i = 0) (hsign : ∀ i j, i ≠ j → (W i j) ^ 2 = 1)
    (a b c d : Fin n) (had : a ≠ d) (hba : b ≠ a) (hbd : b ≠ d)
    (hca : c ≠ a) (hcd : c ≠ d) :
    crossedMatrix W (a, b) (c, d) = if b = c then 0 else
      (W * W) a d * W b d * W a c - W a b * W a c - W b d * W c d := by
  by_cases hbc : b = c
  · subst c
    simp [crossedMatrix, BoundaryDistinct]
  · rw [if_neg hbc, crossedMatrix_entry_sign W hdiag hsign a b c d
      ⟨Ne.symm hba, Ne.symm hca, had, hbc, hbd, hcd⟩]
    ring

/-- Labels available to a localized block with fixed distinct endpoints. -/
abbrev BlockIndex {n : ℕ} (a d : Fin n) := {i : Fin n // i ≠ a ∧ i ≠ d}

/-- The actual restriction to rows (a,b) and columns (c,d). -/
def localizedMatrix {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) (a d : Fin n) :
    Matrix (BlockIndex a d) (BlockIndex a d) ℝ :=
  fun b c => crossedMatrix W (a, b.val) (c.val, d)

/-- Equation (3.2) as an equality of matrices, with no omitted label collisions. -/
theorem localized_block_matrix {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ)
    (hdiag : ∀ i, W i i = 0) (hsign : ∀ i j, i ≠ j → (W i j) ^ 2 = 1)
    (a d : Fin n) (had : a ≠ d) :
    let x : BlockIndex a d → ℝ := fun i => W i.val d
    let y : BlockIndex a d → ℝ := fun i => W a i.val
    let mask : Matrix (BlockIndex a d) (BlockIndex a d) ℝ :=
      Matrix.of (fun i j => if i = j then 0 else 1)
    localizedMatrix W a d =
      (W * W) a d • (Matrix.diagonal x * mask * Matrix.diagonal y) -
      Matrix.diagonal y * mask * Matrix.diagonal y -
      Matrix.diagonal x * mask * Matrix.diagonal x := by
  dsimp only
  ext b c
  change crossedMatrix W (a, b.val) (c.val, d) = _
  rw [localized_block_entry W hdiag hsign a b.val c.val d had
    b.property.1 b.property.2 c.property.1 c.property.2]
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.of_apply]
  by_cases hbc : b = c
  · subst c
    simp
  · have hval : b.val ≠ c.val := fun h => hbc (Subtype.ext h)
    simp [hbc, hval]
    ring

/-- Off-diagonal part of W²; using this definition does not require signs. -/
def offDiagonalSquare {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun a d => if a = d then 0 else (W * W) a d

/-- Symmetric zero-diagonal sign matrices have diagonal W² equal to n-1. -/
theorem square_diagonal {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ)
    (hdiag : ∀ i, W i i = 0) (hsymm : ∀ i j, W i j = W j i)
    (hsign : ∀ i j, i ≠ j → (W i j) ^ 2 = 1) (a : Fin n) :
    (W * W) a a = (n : ℝ) - 1 := by
  calc
    (W * W) a a = ∑ e : Fin n, (if e = a then 0 else 1 : ℝ) := by
      rw [Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro e _
      by_cases hea : e = a
      · subst e
        simp [hdiag]
      · rw [if_neg hea, hsymm e a]
        simpa only [pow_two] using hsign a e (Ne.symm hea)
    _ = (∑ _e : Fin n, (1 : ℝ)) - ∑ e : Fin n, (if e = a then 1 else 0 : ℝ) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro e _
      by_cases hea : e = a <;> simp [hea]
    _ = _ := by simp

/-- The Q used in the operator identities is exactly W²-(n-1)I in the sign model. -/
theorem offDiagonalSquare_eq {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ)
    (hdiag : ∀ i, W i i = 0) (hsymm : ∀ i j, W i j = W j i)
    (hsign : ∀ i j, i ≠ j → (W i j) ^ 2 = 1) :
    offDiagonalSquare W = W * W - ((n : ℝ) - 1) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  ext a d
  by_cases had : a = d
  · subst d
    simp [offDiagonalSquare, square_diagonal W hdiag hsymm hsign]
  · simp [offDiagonalSquare, had]

/-- The coefficient of T - N - N' before the last two collision removals. -/
def reducedCoefficient {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) (a b c d : Fin n) : ℝ :=
  W a c * W b d * offDiagonalSquare W a d -
    W a b * W a c * (if b = d then 0 else 1) -
    (if a = c then 0 else 1) * W c d * W b d

/-- Zero padding on the row and column pair diagonals. -/
def pairCoefficient {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) (a b c d : Fin n) : ℝ :=
  if a ≠ b ∧ c ≠ d then reducedCoefficient W a b c d else 0

/-- Inclusion-exclusion removes precisely the remaining cross-boundary
collisions. Every index is retained; this is an equality of actual entries. -/
theorem collision_decomposition {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ)
    (hdiag : ∀ i, W i i = 0) (hsign : ∀ i j, i ≠ j → (W i j) ^ 2 = 1)
    (a b c d : Fin n) :
    crossedMatrix W (a, b) (c, d) = pairCoefficient W a b c d -
      (if a = d then pairCoefficient W a b c d else 0) -
      (if b = c then pairCoefficient W a b c d else 0) +
      (if a = d ∧ b = c then pairCoefficient W a b c d else 0) := by
  by_cases hab : a = b
  · subst b
    simp [crossedMatrix, BoundaryDistinct, pairCoefficient]
  by_cases hcd : c = d
  · subst d
    simp [crossedMatrix, BoundaryDistinct, pairCoefficient]
  by_cases had : a = d
  · subst d
    simp [crossedMatrix, BoundaryDistinct]
  by_cases hbc : b = c
  · subst c
    simp [crossedMatrix, BoundaryDistinct, had]
  by_cases hac : a = c
  · subst c
    simp [crossedMatrix, BoundaryDistinct, pairCoefficient, reducedCoefficient,
      hdiag, hab, hcd, hbc]
  by_cases hbd : b = d
  · subst d
    simp [crossedMatrix, BoundaryDistinct, pairCoefficient, reducedCoefficient,
      hdiag, hab, hcd, hbc, hac]
  rw [crossedMatrix_entry_sign W hdiag hsign a b c d
    ⟨hab, hac, had, hbc, hbd, hcd⟩]
  simp [pairCoefficient, reducedCoefficient, offDiagonalSquare, hab, hac, had,
    hbc, hbd, hcd]

/-- The a=d collision is the rank-one coefficient -2 W_ab W_ac. -/
theorem endpoint_collision {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ)
    (hsymm : ∀ i j, W i j = W j i) (a b c : Fin n)
    (hba : b ≠ a) (hca : c ≠ a) :
    reducedCoefficient W a b c a = -2 * W a b * W a c := by
  simp [reducedCoefficient, offDiagonalSquare, hba, Ne.symm hca,
    hsymm c a, hsymm b a]
  ring

/-- The b=c collision is a diagonally signed copy of Q minus a constant block. -/
theorem middle_collision {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ)
    (hsign : ∀ i j, i ≠ j → (W i j) ^ 2 = 1)
    (a b d : Fin n) (hab : a ≠ b) (hbd : b ≠ d) :
    reducedCoefficient W a b b d =
      W a b * offDiagonalSquare W a d * W b d - 2 := by
  simp only [reducedCoefficient, if_neg hab, if_neg hbd, mul_one, one_mul]
  have habs := hsign a b hab
  have hbds := hsign b d hbd
  nlinarith

/-- The intersection of the two collision supports has coefficient -2. -/
theorem double_collision {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ)
    (hsign : ∀ i j, i ≠ j → (W i j) ^ 2 = 1)
    (a b : Fin n) (hab : a ≠ b) :
    reducedCoefficient W a b b a = -2 := by
  rw [middle_collision W hsign a b a hab (Ne.symm hab)]
  simp [offDiagonalSquare]

/-- A coordinate matrix, used to identify coefficients of array operators. -/
def coordinateMatrix {n : ℕ} (c d : Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if i = c ∧ j = d then 1 else 0

/-- J-I, with J the all-ones matrix. -/
def offDiagonalOnes (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if i = j then 0 else 1

def principalAction {n : ℕ} (W X : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.hadamard (offDiagonalSquare W) (W * X) * W

def subtractLeftAction {n : ℕ} (W X : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.hadamard W ((W * X) * offDiagonalOnes n)

def subtractRightAction {n : ℕ} (W X : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (offDiagonalOnes n * Matrix.hadamard W X) * W

theorem mul_coordinateMatrix {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ)
    (a j c d : Fin n) :
    (W * coordinateMatrix c d) a j = if j = d then W a c else 0 := by
  by_cases hj : j = d
  · subst j
    simp [Matrix.mul_apply, coordinateMatrix, mul_ite]
  · simp [Matrix.mul_apply, coordinateMatrix, hj]

theorem hadamard_coordinateMatrix_mul {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ)
    (j b c d : Fin n) :
    (Matrix.hadamard W (coordinateMatrix c d) * W) j b =
      if j = c then W c d * W d b else 0 := by
  by_cases hj : j = c
  · subst j
    simp [Matrix.mul_apply, coordinateMatrix, Matrix.hadamard_apply, mul_ite, ite_mul]
  · simp [Matrix.mul_apply, coordinateMatrix, Matrix.hadamard_apply, hj]

/-- The coefficient calculation is tied to the actual matrix products in T. -/
theorem principalAction_coefficient {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ)
    (hsymm : ∀ i j, W i j = W j i) (a b c d : Fin n) :
    principalAction W (coordinateMatrix c d) a b =
      W a c * W b d * offDiagonalSquare W a d := by
  change (∑ j, (offDiagonalSquare W a j * (W * coordinateMatrix c d) a j) * W j b) = _
  simp_rw [mul_coordinateMatrix, mul_ite, ite_mul]
  simp [hsymm d b]
  ring

theorem subtractLeftAction_coefficient {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ)
    (a b c d : Fin n) :
    subtractLeftAction W (coordinateMatrix c d) a b =
      W a b * W a c * (if b = d then 0 else 1) := by
  change W a b * (∑ j, (W * coordinateMatrix c d) a j * offDiagonalOnes n j b) = _
  simp_rw [mul_coordinateMatrix, ite_mul]
  simp [offDiagonalOnes, eq_comm]

theorem subtractRightAction_coefficient {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ)
    (hsymm : ∀ i j, W i j = W j i) (a b c d : Fin n) :
    subtractRightAction W (coordinateMatrix c d) a b =
      (if a = c then 0 else 1) * W c d * W b d := by
  unfold subtractRightAction
  rw [Matrix.mul_assoc]
  change (∑ j, offDiagonalOnes n a j *
    (Matrix.hadamard W (coordinateMatrix c d) * W) j b) = _
  simp_rw [hadamard_coordinateMatrix_mul, mul_ite]
  simp [offDiagonalOnes, hsymm d b]

/-- Equation (3.4): the three genuine array operators have the claimed
coefficient, including both zero-diagonal correction factors. -/
theorem reducedCoefficient_eq_actions {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ)
    (hsymm : ∀ i j, W i j = W j i) (a b c d : Fin n) :
    reducedCoefficient W a b c d =
      principalAction W (coordinateMatrix c d) a b -
      subtractLeftAction W (coordinateMatrix c d) a b -
      subtractRightAction W (coordinateMatrix c d) a b := by
  rw [principalAction_coefficient W hsymm, subtractLeftAction_coefficient W,
    subtractRightAction_coefficient W hsymm]
  rfl

end GraphMatrices.CrossedEdges

namespace GraphMatrices.CrossedEdges

/-- A finite identity behind the failure of the claim that disjoint endpoint
pairs produce independent entries of W². This is the actual 4 by 4 model. -/
theorem four_vertex_square_dependence (W : Matrix (Fin 4) (Fin 4) ℝ)
    (hdiag : ∀ i, W i i = 0) (hsymm : ∀ i j, W i j = W j i)
    (hsign : ∀ i j, i ≠ j → (W i j) ^ 2 = 1) :
    ((W * W) 0 1) ^ 2 = ((W * W) 2 3) ^ 2 := by
  have h01 : (W * W) 0 1 = W 0 2 * W 1 2 + W 0 3 * W 1 3 := by
    simp [Matrix.mul_apply, Fin.sum_univ_succ, hdiag, hsymm 2 1, hsymm 3 1]
  have h23 : (W * W) 2 3 = W 0 2 * W 0 3 + W 1 2 * W 1 3 := by
    simp [Matrix.mul_apply, Fin.sum_univ_succ, hdiag, hsymm 2 0, hsymm 2 1]
  have h02 := hsign 0 2 (by decide)
  have h03 := hsign 0 3 (by decide)
  have h12 := hsign 1 2 (by decide)
  have h13 := hsign 1 3 (by decide)
  rw [h01, h23]
  calc
    _ = (W 0 2)^2 * (W 1 2)^2 + (W 0 3)^2 * (W 1 3)^2 +
        2 * W 0 2 * W 0 3 * W 1 2 * W 1 3 := by ring
    _ = 2 + 2 * W 0 2 * W 0 3 * W 1 2 * W 1 3 := by
      rw [h02, h03, h12, h13]; ring
    _ = (W 0 2)^2 * (W 0 3)^2 + (W 1 2)^2 * (W 1 3)^2 +
        2 * W 0 2 * W 0 3 * W 1 2 * W 1 3 := by
      rw [h02, h03, h12, h13]; ring
    _ = _ := by ring

end GraphMatrices.CrossedEdges
