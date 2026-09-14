import MI32.RawParity
import MI32.PositiveCone

/-!
# Raw polynomial sector masks and exact conditional orthogonality

A mask selects terms by their output coordinate and sign parity. Every
original exponent is retained, including even powers of spectator variables.
Nonnegative raw coefficients survive any further such mask. Conditional
Parseval proves exact energy partition, with no sector-count loss.
-/

noncomputable section
open scoped BigOperators
open GraphMatrices MeasureTheory ProbabilityTheory

namespace MI32.PolynomialSectorMasks
open PositivePolynomial RawParity
attribute [local instance] Classical.propDecidable

variable {E A K : Type*} [Fintype E] [DecidableEq E] [Fintype A] [Fintype K]

/-- Select original raw terms using only the output coordinate and sign parity. -/
def maskCoeff (P : A → Finset E → Prop) (c : A → K → ℝ)
    (ν : A → K → E → ℕ) (a : A) (k : K) : ℝ := by
  classical
  exact if P a (parity (ν a k)) then c a k else 0

omit [DecidableEq E] [Fintype A] [Fintype K] in
theorem maskCoeff_nonneg (P : A → Finset E → Prop)
    (c : A → K → ℝ) (ν : A → K → E → ℕ) (hc : ∀ a k, 0 ≤ c a k)
    (a : A) (k : K) : 0 ≤ maskCoeff P c ν a k := by
  classical
  unfold maskCoeff
  split_ifs
  · exact hc a k
  · exact le_rfl

omit [DecidableEq E] [Fintype A] [Fintype K] in
/-- A subsequent interaction mask preserves the original raw representation. -/
theorem maskCoeff_comp (P Q : A → Finset E → Prop)
    (c : A → K → ℝ) (ν : A → K → E → ℕ) :
    maskCoeff Q (maskCoeff P c ν) ν = maskCoeff (fun a S => P a S ∧ Q a S) c ν := by
  classical
  funext a k
  by_cases hp : P a (parity (ν a k)) <;> by_cases hq : Q a (parity (ν a k)) <;>
    simp [maskCoeff, hp, hq]

omit [Fintype A] in
/-- The conditional Walsh coefficient is exactly masked, with its entire
original magnitude polynomial still present. -/
theorem sectionCoeff_mask (P : A → Finset E → Prop)
    (c : A → K → ℝ) (ν : A → K → E → ℕ)
    (a : A) (S : Finset E) (z : E → ℝ) :
    evaluate (sectionCoeff (maskCoeff P c ν a) (ν a) S) (ν a) z =
      if P a S then evaluate (sectionCoeff (c a) (ν a) S) (ν a) z else 0 := by
  classical
  by_cases hp : P a S
  · rw [if_pos hp]
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hs : parity (ν a k) = S <;> simp [sectionCoeff, maskCoeff, hs, hp]
  · rw [if_neg hp]
    apply Finset.sum_eq_zero
    intro k hk
    by_cases hs : parity (ν a k) = S <;> simp [sectionCoeff, maskCoeff, hs, hp]

/-- The actual sign-averaged squared Euclidean polynomial norm. -/
def conditionalEnergy (c : A → K → ℝ) (ν : A → K → E → ℕ) (z : E → ℝ) : ℝ :=
  Walsh.expectation (fun σ : E → Bool =>
    ∑ a, evaluate (c a) (ν a) (fun e => Walsh.sign (σ e) * z e) ^ 2)

/-- Parseval with all original raw coefficients, with no degree or
positivity premise needed for the identity. -/
theorem conditionalEnergy_eq (c : A → K → ℝ) (ν : A → K → E → ℕ) (z : E → ℝ) :
    conditionalEnergy c ν z =
      ∑ a, ∑ S : Finset E, evaluate (sectionCoeff (c a) (ν a) S) (ν a) z ^ 2 := by
  classical
  unfold conditionalEnergy
  rw [Walsh.expectation_finset_sum]
  apply Finset.sum_congr rfl
  intro a ha
  have he (σ : E → Bool) := evaluate_sign_eq_walsh (c a) (ν a)
    Finset.univ (fun _ => Finset.mem_univ _) σ z
  simp_rw [he]
  simpa only [pow_two] using Walsh.polynomial_pairing Finset.univ
    (fun S => evaluate (sectionCoeff (c a) (ν a) S) (ν a) z)
    (fun S => evaluate (sectionCoeff (c a) (ν a) S) (ν a) z)

/-- A sector mask is an exact conditional orthogonal projection. -/
theorem conditionalEnergy_mask_eq (P : A → Finset E → Prop)
    (c : A → K → ℝ) (ν : A → K → E → ℕ) (z : E → ℝ) :
    conditionalEnergy (maskCoeff P c ν) ν z =
      ∑ a, ∑ S : Finset E,
        if P a S then evaluate (sectionCoeff (c a) (ν a) S) (ν a) z ^ 2 else 0 := by
  classical
  rw [conditionalEnergy_eq]
  simp_rw [sectionCoeff_mask]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro S hS
  by_cases hp : P a S <;> simp [hp]

/-- The mask has norm at most one conditionally on every original magnitude vector. -/
theorem conditionalEnergy_mask_le (P : A → Finset E → Prop)
    (c : A → K → ℝ) (ν : A → K → E → ℕ) (z : E → ℝ) :
    conditionalEnergy (maskCoeff P c ν) ν z ≤ conditionalEnergy c ν z := by
  classical
  rw [conditionalEnergy_mask_eq, conditionalEnergy_eq]
  apply Finset.sum_le_sum
  intro a ha
  apply Finset.sum_le_sum
  intro S hS
  by_cases hp : P a S <;> simp [hp, sq_nonneg]

/-- Any finite cover of the actual labels yields an exact energy partition.
There is no factor for the number of sectors, including after later masks. -/
theorem sum_conditionalEnergy_sectors {D : Type*} [DecidableEq D]
    (label : A → Finset E → D) (L : Finset D)
    (hL : ∀ a S, label a S ∈ L)
    (c : A → K → ℝ) (ν : A → K → E → ℕ) (z : E → ℝ) :
    (∑ d ∈ L, conditionalEnergy (maskCoeff (fun a S => label a S = d) c ν) ν z) =
      conditionalEnergy c ν z := by
  classical
  simp_rw [conditionalEnergy_mask_eq]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := L)]
  rw [conditionalEnergy_eq]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro S hS
  rw [Finset.sum_eq_single (label a S)]
  · simp
  · intro d hd hne
    exact if_neg hne.symm
  · intro hnot
    exact False.elim (hnot (hL a S))

end MI32.PolynomialSectorMasks
