import MI32.PositiveWordExtension
import MI32.SymmetricPositiveCone
import Mathlib.Data.Matrix.Mul

/-!
# Exact positive original-variable words from a vacuum vector

The recursive finite term type records every intermediate vertex and every
appended original variable. Starting with a coordinate vacuum, one extension
is exactly ordered multiplication by a matrix of original linear forms.
Every raw exponent is retained, including repeated use of the same variable
in opposite orientations. Zero entries require no chosen original variable.

This is an exact polynomial representation. It makes no claim that enumerating
the term type is economical, and assumes no probability or norm estimate.
-/

noncomputable section
open scoped BigOperators Matrix

namespace MI32.PositiveVacuumWords

open PositivePolynomial PositiveWordExtension
universe u v

/-- Full provenance of an ordered word. The next extension records its
input vertex, actual original variable, and entire previous term. -/
def Term (V : Type u) (E : Type v) : ℕ → Type (max u v)
  | 0 => PUnit
  | k + 1 => V × E × Term V E k

instance instFintypeTerm {V : Type u} {E : Type v} [Fintype V] [Fintype E] :
    (k : ℕ) → Fintype (Term V E k)
  | 0 => inferInstanceAs (Fintype PUnit)
  | k + 1 =>
    letI : Fintype (Term V E k) := instFintypeTerm k
    inferInstanceAs (Fintype (V × E × Term V E k))

variable {V : Type u} {E : Type v} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

/-- The entry with output `j` and input `i` uses the same original variable
family at every step and every orientation. -/
def matrix (w : V → V → E → ℝ) (z : E → ℝ) : Matrix V V ℝ :=
  fun j i => ∑ e, w i j e * z e

/-- The length-zero vector is the coordinate vacuum at `v`. Later
coefficients are obtained by the checked positive linear-entry extension. -/
def coeff (w : V → V → E → ℝ) (v : V) : (k : ℕ) → V → Term V E k → ℝ
  | 0 => fun j _ => if j = v then 1 else 0
  | k + 1 => linearExtendCoeff w (coeff w v k)

/-- Full occurrence counts in the original variables. They are never
replaced by parity and do not distinguish copies of an original variable. -/
def exponent : (k : ℕ) → V → Term V E k → E → ℕ
  | 0 => fun _ _ => 0
  | k + 1 => linearExtendExponent (exponent k)

omit [Fintype V] [Fintype E] [DecidableEq E] in
@[simp] theorem coeff_zero (w : V → V → E → ℝ) (v j : V) (t : Term V E 0) :
    coeff w v 0 j t = if j = v then 1 else 0 := rfl

omit [Fintype V] [Fintype E] [DecidableEq V] in
@[simp] theorem exponent_zero (j : V) (t : Term V E 0) :
    exponent 0 j t = (0 : E → ℕ) := rfl

omit [Fintype V] [Fintype E] [DecidableEq E] in
/-- The exact successor coefficient identity is available before any
integration or contraction. -/
theorem coeff_succ (w : V → V → E → ℝ) (v : V) (k : ℕ) :
    coeff w v (k + 1) = linearExtendCoeff w (coeff w v k) := rfl

omit [Fintype V] [Fintype E] [DecidableEq V] in
/-- The successor retains the old raw exponent and adds one actual
original-variable occurrence. -/
theorem exponent_succ (k : ℕ) :
    exponent (V := V) (E := E) (k + 1) = linearExtendExponent (exponent k) := rfl

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem coeff_nonneg (w : V → V → E → ℝ) (hw : ∀ i j e, 0 ≤ w i j e)
    (v : V) (k : ℕ) (j : V) (t : Term V E k) : 0 ≤ coeff w v k j t := by
  induction k generalizing j with
  | zero => simp only [coeff_zero]; split_ifs <;> norm_num
  | succ k ih =>
    exact linearExtendCoeff_nonneg w (coeff w v k) hw ih j t

omit [Fintype V] [DecidableEq V] in
/-- Even zero-coefficient labels have the exact raw degree of the word.
The proof counts repeated occurrences separately. -/
theorem degree_exponent (k : ℕ) (j : V) (t : Term V E k) :
    degree (exponent k j t) = k := by
  induction k generalizing j with
  | zero => simp [exponent, degree]
  | succ k ih =>
    change V × E × Term V E k at t
    rw [exponent_succ, degree_linearExtendExponent, ih]

omit [DecidableEq V] [DecidableEq E] in
/-- The explicit word count is exponential in the length; no computational
cost improvement is asserted by this representation. -/
theorem card_term (k : ℕ) :
    Fintype.card (Term V E k) = (Fintype.card V * Fintype.card E) ^ k := by
  induction k with
  | zero =>
    change Fintype.card PUnit = 1
    exact Fintype.card_punit
  | succ k ih =>
    change Fintype.card (V × E × Term V E k) = _
    simp only [Fintype.card_prod, ih, pow_succ]
    ring

@[simp] theorem evaluate_zero (w : V → V → E → ℝ) (v j : V) (z : E → ℝ) :
    evaluate (coeff w v 0 j) (exponent 0 j) z = if j = v then 1 else 0 := by
  simp only [evaluate, coeff_zero, exponent_zero, monomial, Pi.zero_apply, pow_zero,
    Finset.prod_const_one, mul_one, Finset.sum_const, Finset.card_univ, card_term, one_nsmul]

/-- Exact ordered extension of the original polynomial vector, valid for
arbitrary signed weights and arbitrary values of the original variables. -/
theorem evaluate_succ (w : V → V → E → ℝ) (v : V) (k : ℕ) (j : V) (z : E → ℝ) :
    evaluate (coeff w v (k + 1) j) (exponent (k + 1) j) z =
      ∑ i, matrix w z j i * evaluate (coeff w v k i) (exponent k i) z := by
  exact evaluate_linearExtend w (coeff w v k) (exponent k) j z

/-- Literal equality with the original matrix power applied to its starting
coordinate vacuum. Neither coefficients nor random variables are changed. -/
theorem evaluate_eq_pow_mulVec (w : V → V → E → ℝ) (v : V) (k : ℕ) (z : E → ℝ) :
    (fun j => evaluate (coeff w v k j) (exponent k j) z) =
      (matrix w z ^ k) *ᵥ Pi.single v 1 := by
  induction k with
  | zero =>
    ext j
    simp only [evaluate_zero, pow_zero, Matrix.one_mulVec]
    by_cases h : j = v
    · subst j
      simp
    · simp [h]
  | succ k ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ← ih]
    ext j
    exact evaluate_succ w v k j z

/-- The same polynomial is the corresponding entry of the actual matrix power. -/
theorem evaluate_eq_pow_entry (w : V → V → E → ℝ) (v : V) (k : ℕ)
    (j : V) (z : E → ℝ) :
    evaluate (coeff w v k j) (exponent k j) z = (matrix w z ^ k) j v := by
  have h := congrFun (evaluate_eq_pow_mulVec w v k z) j
  simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using h

/-- The Hilbert-valued raw polynomial used by the cone inequalities is
the actual matrix power applied to the coordinate vacuum. -/
theorem evaluateHilbert_eq_pow_mulVec (w : V → V → E → ℝ) (v : V) (k : ℕ)
    (z : E → ℝ) :
    SymmetricPositiveCone.evaluateHilbert (coeff w v k) (exponent k) z =
      WithLp.toLp 2 ((matrix w z ^ k) *ᵥ Pi.single v 1) := by
  unfold SymmetricPositiveCone.evaluateHilbert
  rw [evaluate_eq_pow_mulVec]

section Bipartite

variable {R C : Type*} [Fintype R] [Fintype C] [DecidableEq R] [DecidableEq C]

/-- A concrete symmetric bipartite lift. Both orientations of an edge
append the same original variable `(i,j)`; diagonal blocks have zero weights. -/
def bipartiteWeight : Sum R C → Sum R C → R × C → ℝ
  | .inl i, .inr j, e => if e = (i, j) then 1 else 0
  | .inr j, .inl i, e => if e = (i, j) then 1 else 0
  | _, _, _ => 0

omit [Fintype R] [Fintype C] in
theorem bipartiteWeight_nonneg (i j : Sum R C) (e : R × C) :
    0 ≤ bipartiteWeight i j e := by
  cases i <;> cases j <;> simp only [bipartiteWeight] <;> positivity

@[simp] theorem bipartite_matrix_inl_inl (z : R × C → ℝ) (i i' : R) :
    matrix bipartiteWeight z (.inl i) (.inl i') = 0 := by
  simp [matrix, bipartiteWeight]

@[simp] theorem bipartite_matrix_inr_inr (z : R × C → ℝ) (j j' : C) :
    matrix bipartiteWeight z (.inr j) (.inr j') = 0 := by
  simp [matrix, bipartiteWeight]

@[simp] theorem bipartite_matrix_inl_inr (z : R × C → ℝ) (i : R) (j : C) :
    matrix bipartiteWeight z (.inl i) (.inr j) = z (i, j) := by
  simp [matrix, bipartiteWeight]

@[simp] theorem bipartite_matrix_inr_inl (z : R × C → ℝ) (i : R) (j : C) :
    matrix bipartiteWeight z (.inr j) (.inl i) = z (i, j) := by
  simp [matrix, bipartiteWeight]

/-- The lift is symmetric for every value of the shared original variables. -/
theorem bipartite_matrix_transpose (z : R × C → ℝ) :
    (matrix bipartiteWeight z).transpose = matrix bipartiteWeight z := by
  ext i j
  cases i <;> cases j <;> simp [Matrix.transpose_apply]

end Bipartite

end MI32.PositiveVacuumWords
