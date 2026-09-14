import MI32.PositivePolynomial
import GraphMatrices.Walsh

/-!
# Exact parity expansion of original-variable polynomials

All identities retain full natural exponent vectors in the magnitude polynomial.
Only the independent signs are reduced modulo two. Coefficient restrictions select
original terms and introduce neither cancellations nor an orthogonal magnitude basis.
-/

noncomputable section
open scoped BigOperators symmDiff
open GraphMatrices

namespace MI32.RawParity

open PositivePolynomial

variable {E κ : Type*} [Fintype E] [DecidableEq E] [Fintype κ]

/-- Occupied sign coordinates of a full original exponent vector. -/
def parity (ν : E → ℕ) : Finset E := Finset.univ.filter fun e => Odd (ν e)

omit [DecidableEq E] in
@[simp] theorem mem_parity (ν : E → ℕ) (e : E) : e ∈ parity ν ↔ Odd (ν e) := by
  simp [parity]

omit [DecidableEq E] in
/-- Parity occupation is bounded by raw degree, even for repeated original variables. -/
theorem parity_card_le_degree (ν : E → ℕ) : (parity ν).card ≤ degree ν := by
  unfold parity degree
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_le_sum
  intro e _
  by_cases he : Odd (ν e)
  · simp only [he, ite_true]
    obtain ⟨r, hr⟩ := he
    omega
  · simp [he]

/-- A sign power depends on parity; its magnitude exponent has not been changed. -/
theorem sign_pow (b : Bool) (r : ℕ) :
    Walsh.sign b ^ r = if Odd r then Walsh.sign b else 1 := by
  cases b
  · by_cases hr : Odd r
    · simp [Walsh.sign, hr, hr.neg_one_pow]
    · simp [Walsh.sign, hr, (Nat.not_odd_iff_even.mp hr).neg_one_pow]
  · simp [Walsh.sign]

/-- Exact raw monomial factorization into a Walsh character and its full magnitude monomial. -/
theorem monomial_sign (σ : E → Bool) (z : E → ℝ) (ν : E → ℕ) :
    monomial (fun e => Walsh.sign (σ e) * z e) ν =
      Walsh.character (parity ν) σ * monomial z ν := by
  simp only [monomial, mul_pow, Finset.prod_mul_distrib, Walsh.character, mem_parity,
    sign_pow]

/-- One Walsh coefficient, represented by the original term family with zeros elsewhere. -/
def sectionCoeff (c : κ → ℝ) (ν : κ → E → ℕ) (S : Finset E) (t : κ) : ℝ :=
  if parity (ν t) = S then c t else 0

omit [Fintype κ] in
/-- Restricting to one parity class preserves every coefficient's nonnegativity. -/
theorem sectionCoeff_nonneg (c : κ → ℝ) (ν : κ → E → ℕ)
    (hc : ∀ t, 0 ≤ c t) (S : Finset E) (t : κ) : 0 ≤ sectionCoeff c ν S t := by
  unfold sectionCoeff
  split_ifs
  · exact hc t
  · exact le_rfl

/-- Exact Walsh expansion over any set containing all actual parity classes.
No positivity assumption is required for this algebraic identity. -/
theorem evaluate_sign_eq_walsh (c : κ → ℝ) (ν : κ → E → ℕ)
    (I : Finset (Finset E)) (hI : ∀ t, parity (ν t) ∈ I)
    (σ : E → Bool) (z : E → ℝ) :
    evaluate c ν (fun e => Walsh.sign (σ e) * z e) =
      Walsh.polynomial I (fun S => evaluate (sectionCoeff c ν S) ν z) σ := by
  simp only [evaluate, monomial_sign, Walsh.polynomial, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  simp [sectionCoeff, hI t, mul_comm, mul_left_comm]

/-- All occupation sets reachable by a raw polynomial of degree at most `d`. -/
def cutoff (d : ℕ) : Finset (Finset E) := Finset.univ.filter fun S => S.card ≤ d

omit [DecidableEq E] in
@[simp] theorem mem_cutoff (d : ℕ) (S : Finset E) : S ∈ cutoff d ↔ S.card ≤ d := by
  simp [cutoff]

omit [DecidableEq E] in
/-- The degree cutoff supplies the required Walsh support without assuming an expansion. -/
theorem parity_mem_cutoff (ν : E → ℕ) (d : ℕ) (hν : degree ν ≤ d) :
    parity ν ∈ cutoff d :=
  (mem_cutoff d _).mpr ((parity_card_le_degree ν).trans hν)

/-- Exact parity expansion at the degree cutoff of the original polynomial. -/
theorem evaluate_sign_eq_cutoff (c : κ → ℝ) (ν : κ → E → ℕ)
    (d : ℕ) (hν : ∀ t, degree (ν t) ≤ d) (σ : E → Bool) (z : E → ℝ) :
    evaluate c ν (fun e => Walsh.sign (σ e) * z e) =
      Walsh.polynomial (cutoff d) (fun S => evaluate (sectionCoeff c ν S) ν z) σ :=
  evaluate_sign_eq_walsh c ν (cutoff d) (fun t => parity_mem_cutoff (ν t) d (hν t)) σ z



/-- Multiplication keeps raw exponents additive while occupied sign coordinates toggle. -/
theorem parity_add (ν η : E → ℕ) : parity (ν + η) = parity ν ∆ parity η := by
  ext e
  simp only [mem_parity, Pi.add_apply, Finset.mem_symmDiff]
  rw [Nat.odd_add, ← Nat.not_odd_iff_even]
  tauto

end MI32.RawParity

