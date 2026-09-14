import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! Exact Walsh orthogonality for all finite independent uniform sign assignments.
These are finite sums, not an assumed probabilistic moment formula. -/

namespace GraphMatrices.Walsh

open scoped symmDiff

variable {E : Type*} [Fintype E] [DecidableEq E]

def sign (b : Bool) : ℝ := if b then 1 else -1

@[simp] theorem sign_mul_self (b : Bool) : sign b * sign b = 1 := by
  cases b <;> norm_num [sign]

def character (S : Finset E) (σ : E → Bool) : ℝ :=
  ∏ i, if i ∈ S then sign (σ i) else 1

@[simp] theorem character_empty (σ : E → Bool) : character ∅ σ = 1 := by
  simp [character]

theorem character_mul (S T : Finset E) (σ : E → Bool) :
    character S σ * character T σ = character (S ∆ T) σ := by
  classical
  unfold character
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hs : i ∈ S <;> by_cases ht : i ∈ T <;>
    simp [hs, ht, Finset.mem_symmDiff]

theorem sum_character (S : Finset E) :
    (∑ σ : E → Bool, character S σ) =
      if S = ∅ then (2 : ℝ) ^ Fintype.card E else 0 := by
  classical
  have hfactor :
      (∑ σ : E → Bool, character S σ) =
        ∏ i : E, ∑ b : Bool, if i ∈ S then sign b else 1 := by
    exact (Fintype.prod_sum (fun i (b : Bool) => if i ∈ S then sign b else 1)).symm
  rw [hfactor]
  by_cases hS : S = ∅
  · simp [hS]
  · rw [if_neg hS]
    obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hS
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi, sign]

/-- Expectation for the full finite uniform sign law. -/
noncomputable def expectation (f : (E → Bool) → ℝ) : ℝ :=
  (∑ σ, f σ) / (2 : ℝ) ^ Fintype.card E

theorem expectation_character (S : Finset E) :
    expectation (character S) = if S = ∅ then 1 else 0 := by
  unfold expectation
  rw [sum_character]
  split_ifs <;> simp

theorem character_orthogonality (S T : Finset E) :
    expectation (fun σ => character S σ * character T σ) =
      if S = T then 1 else 0 := by
  simp_rw [character_mul]
  rw [expectation_character]
  simp

theorem expectation_finset_sum {ι : Type*} (I : Finset ι)
    (f : ι → (E → Bool) → ℝ) :
    expectation (fun σ => ∑ i ∈ I, f i σ) =
      ∑ i ∈ I, expectation (f i) := by
  unfold expectation
  rw [Finset.sum_comm, Finset.sum_div]

theorem expectation_const_mul (c : ℝ) (f : (E → Bool) → ℝ) :
    expectation (fun σ => c * f σ) = c * expectation f := by
  simp only [expectation, ← Finset.mul_sum, mul_div_assoc]

/-- A finite Walsh expansion, with an explicit finite set of coefficients. -/
def polynomial (I : Finset (Finset E)) (c : Finset E → ℝ) (σ : E → Bool) : ℝ :=
  ∑ S ∈ I, c S * character S σ

/-- Exact Parseval pairing under the full uniform sign law. -/
theorem polynomial_pairing (I : Finset (Finset E)) (c d : Finset E → ℝ) :
    expectation (fun σ => polynomial I c σ * polynomial I d σ) =
      ∑ S ∈ I, c S * d S := by
  have hexpand (σ : E → Bool) :
      polynomial I c σ * polynomial I d σ =
        ∑ S ∈ I, ∑ T ∈ I, (c S * d T) * (character S σ * character T σ) := by
    unfold polynomial
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro S _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro T _
    ring
  simp_rw [hexpand]
  rw [expectation_finset_sum]
  simp_rw [expectation_finset_sum, expectation_const_mul, character_orthogonality]
  apply Finset.sum_congr rfl
  intro S hS
  simp [hS]

end GraphMatrices.Walsh
