import MI32.PolynomialSectorMasks

/-!
# Exact positive raw-word extension under ordered matrix multiplication

Every new term retains its old input coordinate and term label, and appends
one occurrence of the actual original variable. Original exponents are added
in ℕ; only the separate sign-parity descriptor toggles. Deterministic positive
weights and any subsequent output/parity mask preserve the positive cone.
The linear-entry variant also represents identically zero matrix entries
without selecting an artificial original variable.
-/

noncomputable section
open scoped BigOperators symmDiff

namespace MI32.PositiveWordExtension

open PositivePolynomial RawParity PolynomialSectorMasks
attribute [local instance] Classical.propDecidable

variable {E I J K : Type*} [Fintype E] [DecidableEq E]

/-- One occurrence of an actual original variable. -/
def unitExponent (e : E) : E → ℕ := fun f => if f = e then 1 else 0

omit [Fintype E] in
@[simp] theorem unitExponent_self (e : E) : unitExponent e e = 1 := by
  simp [unitExponent]

omit [Fintype E] in
@[simp] theorem unitExponent_of_ne (e f : E) (h : f ≠ e) : unitExponent e f = 0 := by
  simp [unitExponent, h]

@[simp] theorem degree_unitExponent (e : E) : degree (unitExponent e) = 1 := by
  simp [degree, unitExponent]

@[simp] theorem monomial_unitExponent (z : E → ℝ) (e : E) :
    monomial z (unitExponent e) = z e := by
  simp [monomial, unitExponent]

@[simp] theorem parity_unitExponent (e : E) : parity (unitExponent e) = {e} := by
  ext f
  by_cases h : f = e <;> simp [mem_parity, unitExponent, h]

/-- Updated coefficients retain the previous input coordinate and term label. -/
def extendCoeff (w : I → J → ℝ) (c : I → K → ℝ) (j : J) (t : I × K) : ℝ :=
  w t.1 j * c t.1 t.2

/-- Appending the selected original variable adds a raw occurrence, even
when that variable already occurs in the input word. -/
def extendExponent (edge : I → J → E) (ν : I → K → E → ℕ)
    (j : J) (t : I × K) : E → ℕ :=
  ν t.1 t.2 + unitExponent (edge t.1 j)

omit [Fintype E] in
theorem extendExponent_self (edge : I → J → E) (ν : I → K → E → ℕ)
    (j : J) (t : I × K) :
    extendExponent edge ν j t (edge t.1 j) = ν t.1 t.2 (edge t.1 j) + 1 := by
  simp [extendExponent]

omit [Fintype E] in
theorem extendExponent_other (edge : I → J → E) (ν : I → K → E → ℕ)
    (j : J) (t : I × K) (e : E) (he : e ≠ edge t.1 j) :
    extendExponent edge ν j t e = ν t.1 t.2 e := by
  simp [extendExponent, unitExponent, he]

/-- Exact raw degree increases by one, regardless of the previous parity. -/
theorem degree_extendExponent (edge : I → J → E) (ν : I → K → E → ℕ)
    (j : J) (t : I × K) :
    degree (extendExponent edge ν j t) = degree (ν t.1 t.2) + 1 := by
  simp only [extendExponent, degree_add, degree_unitExponent]

/-- The sign coordinate toggles while the full raw exponent is retained. -/
theorem parity_extendExponent (edge : I → J → E) (ν : I → K → E → ℕ)
    (j : J) (t : I × K) :
    parity (extendExponent edge ν j t) = parity (ν t.1 t.2) ∆ {edge t.1 j} := by
  simp only [extendExponent, parity_add, parity_unitExponent]

theorem extendCoeff_nonneg (w : I → J → ℝ) (c : I → K → ℝ)
    (hw : ∀ i j, 0 ≤ w i j) (hc : ∀ i k, 0 ≤ c i k) (j : J) (t : I × K) :
    0 ≤ extendCoeff w c j t :=
  mul_nonneg (hw t.1 j) (hc t.1 t.2)

/-- Literal ordered matrix multiplication of the original polynomial vector.
The identity itself permits arbitrary real deterministic weights and coefficients. -/
theorem evaluate_extend [Fintype I] [Fintype K] (edge : I → J → E) (w : I → J → ℝ)
    (c : I → K → ℝ) (ν : I → K → E → ℕ) (j : J) (z : E → ℝ) :
    evaluate (extendCoeff w c j) (extendExponent edge ν j) z =
      ∑ i, w i j * z (edge i j) * evaluate (c i) (ν i) z := by
  simp only [evaluate, Fintype.sum_prod_type, extendCoeff, extendExponent,
    monomial_add, monomial_unitExponent, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Direct original-entry multiplication is the unit-weight case. -/
theorem evaluate_extend_original_entries [Fintype I] [Fintype K] (edge : I → J → E)
    (c : I → K → ℝ) (ν : I → K → E → ℕ) (j : J) (z : E → ℝ) :
    evaluate (extendCoeff (fun _ _ => 1) c j) (extendExponent edge ν j) z =
      ∑ i, z (edge i j) * evaluate (c i) (ν i) z := by
  simpa only [one_mul] using evaluate_extend edge (fun _ _ => 1) c ν j z

theorem degree_extendExponent_le (edge : I → J → E) (ν : I → K → E → ℕ)
    (d : ℕ) (hdegree : ∀ i k, degree (ν i k) ≤ d) (j : J) (t : I × K) :
    degree (extendExponent edge ν j t) ≤ d + 1 := by
  rw [degree_extendExponent]
  exact Nat.add_le_add_right (hdegree t.1 t.2) 1

/-- An arbitrary later grade/count mask preserves positive coefficients and
the raw degree bound, retaining the same expanded term family and exponents. -/
theorem masked_extension_positive_degree
    (P : J → Finset E → Prop) (edge : I → J → E) (w : I → J → ℝ)
    (c : I → K → ℝ) (ν : I → K → E → ℕ)
    (hw : ∀ i j, 0 ≤ w i j) (hc : ∀ i k, 0 ≤ c i k)
    (d : ℕ) (hdegree : ∀ i k, degree (ν i k) ≤ d) :
    (∀ j t, 0 ≤ maskCoeff P (extendCoeff w c) (extendExponent edge ν) j t) ∧
      (∀ j t, degree (extendExponent edge ν j t) ≤ d + 1) :=
  ⟨maskCoeff_nonneg P _ _ (extendCoeff_nonneg w c hw hc),
    degree_extendExponent_le edge ν d hdegree⟩

/-- Successive masks compose on the updated parity without modifying raw exponents. -/
theorem masked_extension_comp (P Q : J → Finset E → Prop)
    (edge : I → J → E) (w : I → J → ℝ)
    (c : I → K → ℝ) (ν : I → K → E → ℕ) :
    maskCoeff Q (maskCoeff P (extendCoeff w c) (extendExponent edge ν))
        (extendExponent edge ν) =
      maskCoeff (fun j S => P j S ∧ Q j S) (extendCoeff w c) (extendExponent edge ν) :=
  maskCoeff_comp P Q _ _

/-- The later mask tests exactly the toggled original parity of each new term. -/
theorem evaluate_masked_extend [Fintype I] [Fintype K] (P : J → Finset E → Prop)
    (edge : I → J → E) (w : I → J → ℝ)
    (c : I → K → ℝ) (ν : I → K → E → ℕ) (j : J) (z : E → ℝ) :
    evaluate (maskCoeff P (extendCoeff w c) (extendExponent edge ν) j)
        (extendExponent edge ν j) z =
      ∑ i, ∑ k, if P j (parity (ν i k) ∆ {edge i j}) then
        w i j * z (edge i j) * (c i k * monomial z (ν i k)) else 0 := by
  classical
  simp only [evaluate, Fintype.sum_prod_type, maskCoeff, parity_extendExponent]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  by_cases h : P j (parity (ν i k) ∆ {edge i j})
  · simp only [h, if_pos, extendCoeff, extendExponent, monomial_add, monomial_unitExponent]
    ring
  · simp [h]

section LinearEntries

/-- A matrix entry may be a positive linear combination of original variables.
The explicit label retains the input coordinate, appended variable, and old term. -/
def linearExtendCoeff (w : I → J → E → ℝ) (c : I → K → ℝ)
    (j : J) (t : I × E × K) : ℝ :=
  w t.1 j t.2.1 * c t.1 t.2.2

def linearExtendExponent (ν : I → K → E → ℕ)
    (_j : J) (t : I × E × K) : E → ℕ :=
  ν t.1 t.2.2 + unitExponent t.2.1

theorem degree_linearExtendExponent (ν : I → K → E → ℕ)
    (j : J) (t : I × E × K) :
    degree (linearExtendExponent ν j t) = degree (ν t.1 t.2.2) + 1 := by
  simp only [linearExtendExponent, degree_add, degree_unitExponent]

theorem parity_linearExtendExponent (ν : I → K → E → ℕ)
    (j : J) (t : I × E × K) :
    parity (linearExtendExponent ν j t) = parity (ν t.1 t.2.2) ∆ {t.2.1} := by
  simp only [linearExtendExponent, parity_add, parity_unitExponent]

omit [Fintype E] [DecidableEq E] in
theorem linearExtendCoeff_nonneg (w : I → J → E → ℝ) (c : I → K → ℝ)
    (hw : ∀ i j e, 0 ≤ w i j e) (hc : ∀ i k, 0 ≤ c i k) (j : J) (t : I × E × K) :
    0 ≤ linearExtendCoeff w c j t :=
  mul_nonneg (hw t.1 j t.2.1) (hc t.1 t.2.2)

/-- Exact multiplication by a matrix of original linear forms; zero entries
use all-zero weights and need no chosen original edge. -/
theorem evaluate_linearExtend [Fintype I] [Fintype K] (w : I → J → E → ℝ)
    (c : I → K → ℝ) (ν : I → K → E → ℕ) (j : J) (z : E → ℝ) :
    evaluate (linearExtendCoeff w c j) (linearExtendExponent ν j) z =
      ∑ i, (∑ e, w i j e * z e) * evaluate (c i) (ν i) z := by
  simp only [evaluate, Fintype.sum_prod_type, linearExtendCoeff, linearExtendExponent,
    monomial_add, monomial_unitExponent, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Linear-form entries also remain in the positive raw cone under every
subsequent grade/count mask, with exactly one additional raw occurrence. -/
theorem masked_linearExtension_positive_degree
    (P : J → Finset E → Prop) (w : I → J → E → ℝ)
    (c : I → K → ℝ) (ν : I → K → E → ℕ)
    (hw : ∀ i j e, 0 ≤ w i j e) (hc : ∀ i k, 0 ≤ c i k)
    (d : ℕ) (hdegree : ∀ i k, degree (ν i k) ≤ d) :
    (∀ j t, 0 ≤ maskCoeff P (linearExtendCoeff w c) (linearExtendExponent ν) j t) ∧
      (∀ (j : J) t, degree (linearExtendExponent ν j t) ≤ d + 1) := by
  refine ⟨maskCoeff_nonneg P _ _ (linearExtendCoeff_nonneg w c hw hc), ?_⟩
  intro j t
  rw [degree_linearExtendExponent]
  exact Nat.add_le_add_right (hdegree t.1 t.2.2) 1

end LinearEntries

end MI32.PositiveWordExtension
