import GraphMatrices.FiniteL2
import GraphMatrices.Walsh
import GraphMatrices.SignGraphDegree

/-! A complete finite Walsh basis and its exact matrix-valued vacuum identity. -/

namespace GraphMatrices.Walsh

noncomputable section

open scoped BigOperators

variable {E : Type*} [Fintype E] [DecidableEq E]

theorem character_eq_prod (S : Finset E) (σ : E → Bool) :
    character S σ = ∏ i ∈ S, sign (σ i) := by
  simp [character]

theorem sum_character_products (σ τ : E → Bool) :
    (∑ S : Finset E, character S σ * character S τ) =
      if σ = τ then (2 : ℝ) ^ Fintype.card E else 0 := by
  classical
  have hprod := Fintype.prod_add
    (fun i : E => sign (σ i) * sign (τ i)) (fun _ : E => (1 : ℝ))
  simp only [Finset.prod_const_one, mul_one] at hprod
  have hexpand :
      (∑ S : Finset E, character S σ * character S τ) =
        ∏ i : E, (sign (σ i) * sign (τ i) + 1) := by
    rw [hprod]
    apply Finset.sum_congr rfl
    intro S _
    rw [character_eq_prod, character_eq_prod, Finset.prod_mul_distrib]
  rw [hexpand]
  by_cases hστ : σ = τ
  · subst τ
    norm_num
  · rw [if_neg hστ]
    obtain ⟨i, hi⟩ : ∃ i, σ i ≠ τ i := Function.ne_iff.mp hστ
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    cases hs : σ i <;> cases ht : τ i <;> simp_all [sign]

theorem expectation_eq_weighted_sum (f : (E → Bool) → ℝ) :
    expectation f = ∑ σ, ((2 : ℝ) ^ Fintype.card E)⁻¹ * f σ := by
  rw [← Finset.mul_sum]
  simp only [expectation, div_eq_mul_inv, mul_comm]

theorem character_reconstruction (f : (E → Bool) → ℝ) (σ : E → Bool) :
    f σ = ∑ S : Finset E, expectation (fun τ => character S τ * f τ) * character S σ := by
  classical
  simp only [expectation_eq_weighted_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  have hinner (τ : E → Bool) :
      (∑ S : Finset E,
        (((2 : ℝ) ^ Fintype.card E)⁻¹ * (character S τ * f τ)) * character S σ) =
        (((2 : ℝ) ^ Fintype.card E)⁻¹ * f τ) *
          (∑ S : Finset E, character S τ * character S σ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro S _
    ring
  simp_rw [hinner, sum_character_products]
  simp [mul_assoc, mul_left_comm, mul_comm]

def weightedONBasis : FiniteL2.WeightedONBasis (E → Bool) (Finset E) where
  weight _ := ((2 : ℝ) ^ Fintype.card E)⁻¹
  weight_nonneg _ := by positivity
  sum_weight := by simp [Fintype.card_fun]
  basis := character
  orthonormal_same S := by
    have h := character_orthogonality S S
    rw [expectation_eq_weighted_sum] at h
    simpa [mul_assoc] using h
  orthonormal_ne S T hST := by
    have h := character_orthogonality S T
    rw [expectation_eq_weighted_sum] at h
    simpa [hST, mul_assoc] using h
  reconstruction f σ := by
    simpa only [expectation_eq_weighted_sum, mul_assoc] using character_reconstruction f σ
  vacuum := ∅
  vacuum_eq_one := character_empty

theorem weightedONBasis_expect (f : (E → Bool) → ℝ) :
    (weightedONBasis (E := E)).expect f = independentSignLaw.expect f := by
  rw [independentSignLaw_expect_eq_walsh, expectation_eq_weighted_sum]
  rfl

theorem matrix_vacuum_moment_independent
    {A : Type*} [Fintype A] [DecidableEq A]
    (M : (E → Bool) → Matrix A A ℝ) (k : ℕ) :
    (∑ a, ((weightedONBasis (E := E)).matrixMulOp M ^ k) (a, ∅) (a, ∅)) =
      independentSignLaw.expect (fun σ => Matrix.trace (M σ ^ k)) := by
  rw [← weightedONBasis_expect]
  exact (weightedONBasis (E := E)).matrix_vacuum_moment M k

end
end GraphMatrices.Walsh
