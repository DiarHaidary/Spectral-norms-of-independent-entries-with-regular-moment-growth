import MI32.Statement
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Tactic

/-! # Finite variance maxima in the literal MI-32 statement -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace MI32.VarianceScaleBasics

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {n : ℕ}

def rowStd (X : Ω → Matrix (Fin n) (Fin n) ℝ) (i : Fin n) : ℝ :=
  Real.sqrt (∑ j, ∫ ω, X ω i j ^ 2 ∂μ)

def colStd (X : Ω → Matrix (Fin n) (Fin n) ℝ) (j : Fin n) : ℝ :=
  Real.sqrt (∑ i, ∫ ω, X ω i j ^ 2 ∂μ)

theorem varianceScale_eq (X : Ω → Matrix (Fin n) (Fin n) ℝ) :
    varianceScale μ X = sSup (Set.range (rowStd (μ := μ) X)) +
      sSup (Set.range (colStd (μ := μ) X)) := rfl

theorem finite_sup_nonneg {I : Type*} [Fintype I] [Nonempty I]
    (f : I → ℝ) (hf : ∀ i, 0 ≤ f i) : 0 ≤ sSup (Set.range f) := by
  obtain ⟨i⟩ := ‹Nonempty I›
  exact (hf i).trans (le_csSup (Set.finite_range f).bddAbove (Set.mem_range_self i))

theorem finite_sup_mul {I : Type*} [Fintype I] [Nonempty I]
    (f : I → ℝ) (c : ℝ) (hc : 0 ≤ c) :
    sSup (Set.range (fun i => c * f i)) = c * sSup (Set.range f) := by
  have hmono : Monotone (fun x : ℝ => c * x) := fun _ _ h =>
    mul_le_mul_of_nonneg_left h hc
  have hm := Set.Finite.map_sSup_of_monotone hmono (Set.range_nonempty f) (Set.finite_range f)
  simpa only [← Set.range_comp, Function.comp_def] using hm.symm

theorem varianceScale_nonneg (X : Ω → Matrix (Fin n) (Fin n) ℝ) (hn : 1 ≤ n) :
    0 ≤ varianceScale μ X := by
  let : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  rw [varianceScale_eq]
  exact add_nonneg (finite_sup_nonneg _ fun _ => Real.sqrt_nonneg _)
    (finite_sup_nonneg _ fun _ => Real.sqrt_nonneg _)

theorem rowStd_le_varianceScale (X : Ω → Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    rowStd (μ := μ) X i ≤ varianceScale μ X := by
  let : Nonempty (Fin n) := ⟨i⟩
  rw [varianceScale_eq]
  exact (le_csSup (Set.finite_range _).bddAbove (Set.mem_range_self i)).trans
    (le_add_of_nonneg_right (finite_sup_nonneg _ fun _ => Real.sqrt_nonneg _))

theorem colStd_le_varianceScale (X : Ω → Matrix (Fin n) (Fin n) ℝ) (j : Fin n) :
    colStd (μ := μ) X j ≤ varianceScale μ X := by
  let : Nonempty (Fin n) := ⟨j⟩
  rw [varianceScale_eq]
  exact (le_csSup (Set.finite_range _).bddAbove (Set.mem_range_self j)).trans
    (le_add_of_nonneg_left (finite_sup_nonneg _ fun _ => Real.sqrt_nonneg _))

theorem row_variance_le_sq (X : Ω → Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    (∑ j, ∫ ω, X ω i j ^ 2 ∂μ) ≤ varianceScale μ X ^ 2 := by
  have hnonneg : 0 ≤ ∑ j, ∫ ω, X ω i j ^ 2 ∂μ :=
    Finset.sum_nonneg fun j _ => integral_nonneg fun ω => sq_nonneg _
  have h := pow_le_pow_left₀ (Real.sqrt_nonneg _) (rowStd_le_varianceScale (μ := μ) X i) 2
  simpa only [rowStd, Real.sq_sqrt hnonneg] using h

theorem col_variance_le_sq (X : Ω → Matrix (Fin n) (Fin n) ℝ) (j : Fin n) :
    (∑ i, ∫ ω, X ω i j ^ 2 ∂μ) ≤ varianceScale μ X ^ 2 := by
  have hnonneg : 0 ≤ ∑ i, ∫ ω, X ω i j ^ 2 ∂μ :=
    Finset.sum_nonneg fun i _ => integral_nonneg fun ω => sq_nonneg _
  have h := pow_le_pow_left₀ (Real.sqrt_nonneg _) (colStd_le_varianceScale (μ := μ) X j) 2
  simpa only [colStd, Real.sq_sqrt hnonneg] using h

/-- Exact transfer of the literal finite variance maxima from entrywise
second-moment scaling, on arbitrary original and target probability spaces. -/
theorem varianceScale_of_entry_second_moments
    {Ω' : Type*} [MeasurableSpace Ω'] {ν : Measure Ω'}
    (X : Ω → Matrix (Fin n) (Fin n) ℝ) (Y : Ω' → Matrix (Fin n) (Fin n) ℝ)
    (hn : 1 ≤ n) (c : ℝ) (hc : 0 ≤ c)
    (hentry : ∀ i j, (∫ ω, Y ω i j ^ 2 ∂ν) = c * ∫ ω, X ω i j ^ 2 ∂μ) :
    varianceScale ν Y = Real.sqrt c * varianceScale μ X := by
  let : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hrow (i : Fin n) : rowStd (μ := ν) Y i = Real.sqrt c * rowStd (μ := μ) X i := by
    simp only [rowStd, hentry, ← Finset.mul_sum, Real.sqrt_mul hc]
  have hcol (j : Fin n) : colStd (μ := ν) Y j = Real.sqrt c * colStd (μ := μ) X j := by
    simp only [colStd, hentry, ← Finset.mul_sum, Real.sqrt_mul hc]
  rw [varianceScale_eq, varianceScale_eq]
  rw [funext hrow, funext hcol]
  rw [finite_sup_mul _ _ (Real.sqrt_nonneg c), finite_sup_mul _ _ (Real.sqrt_nonneg c)]
  ring

end MI32.VarianceScaleBasics
