import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# Summable original-variance overlaps under graded support caps

The cap is pointwise on the original deterministic nonnegative variances:
when the later column is supported at a row, each earlier column's variance
there is small. No pair-energy or Gram estimate is assumed. The actual
nested-mask construction must discharge this support cap before applying
the resulting energy theorem.
-/

noncomputable section
open scoped BigOperators

namespace MI32.GradedVarianceEnergy

variable {R C : Type*} [Fintype R] [Fintype C] {L : ℕ}

/-- Columns in the original axes with grade at most the given label. -/
def columnsThrough (label : C → Fin L) (r : Fin L) : Finset C :=
  Finset.univ.filter (fun j => label j ≤ r)

/-- Ordered original column pairs, grouped by their maximum grade. -/
def columnPairsAt (label : C → Fin L) (r : Fin L) : Finset (C × C) :=
  Finset.univ.filter (fun jk => max (label jk.1) (label jk.2) = r)

theorem columnPairsAt_subset (label : C → Fin L) (r : Fin L) :
    columnPairsAt label r ⊆ (columnsThrough label r).product (columnsThrough label r) := by
  intro jk hjk
  have h := (Finset.mem_filter.mp hjk).2
  simp only [Finset.product_eq_sprod, Finset.mem_product, columnsThrough,
    Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨(le_max_left _ _).trans_eq h, (le_max_right _ _).trans_eq h⟩

/-- Counting ordered pairs costs the square of the cumulative column budget. -/
theorem card_columnPairsAt_le (label : C → Fin L) (b : Fin L → ℕ)
    (hcard : ∀ r, (columnsThrough label r).card ≤ b r) (r : Fin L) :
    (columnPairsAt label r).card ≤ b r ^ 2 := by
  have h := Finset.card_le_card (columnPairsAt_subset label r)
  rw [Finset.product_eq_sprod, Finset.card_product] at h
  have hc := hcard r
  nlinarith

/-- Exact finite partition by the maximum of the two original labels. -/
theorem sum_pair_weights_eq (label : C → Fin L) (f : Fin L → ℝ) :
    (∑ j, ∑ k, f (max (label j) (label k))) =
      ∑ r, ((columnPairsAt label r).card : ℝ) * f r := by
  simpa only [columnPairsAt, Finset.sum_const, nsmul_eq_mul, Fintype.sum_prod_type] using
    (Finset.sum_fiberwise' (Finset.univ : Finset (C × C))
      (fun jk => max (label jk.1) (label jk.2)) f).symm

omit [Fintype C] in
/-- The cap on shared original support gives a quantitative column-pair overlap. -/
theorem pair_energy_le_of_label_le
    (v : R → C → ℝ) (hv : ∀ i j, 0 ≤ v i j)
    (B : ℝ) (hcol : ∀ j, (∑ i, v i j) ≤ B ^ 2)
    (label : C → Fin L) (b : Fin L → ℕ)
    (hcap : ∀ i j k, label j ≤ label k → v i k ≠ 0 →
      v i j ≤ B ^ 2 / ((b (label k) : ℝ) ^ 3 + 1))
    (j k : C) (hjk : label j ≤ label k) :
    (∑ i, v i j * v i k) ≤ B ^ 4 / ((b (label k) : ℝ) ^ 3 + 1) := by
  have hden : 0 < (b (label k) : ℝ) ^ 3 + 1 := by positivity
  calc
    _ ≤ ∑ i, (B ^ 2 / ((b (label k) : ℝ) ^ 3 + 1)) * v i k := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : v i k = 0
      · simp [hi]
      · exact mul_le_mul_of_nonneg_right (hcap i j k hjk hi) (hv i k)
    _ = (B ^ 2 / ((b (label k) : ℝ) ^ 3 + 1)) * ∑ i, v i k :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ (B ^ 2 / ((b (label k) : ℝ) ^ 3 + 1)) * B ^ 2 :=
      mul_le_mul_of_nonneg_left (hcol k) (div_nonneg (sq_nonneg B) hden.le)
    _ = _ := by ring

omit [Fintype C] in
/-- Either ordering of two labels gives the bound at their maximum label. -/
theorem pair_energy_le
    (v : R → C → ℝ) (hv : ∀ i j, 0 ≤ v i j)
    (B : ℝ) (hcol : ∀ j, (∑ i, v i j) ≤ B ^ 2)
    (label : C → Fin L) (b : Fin L → ℕ)
    (hcap : ∀ i j k, label j ≤ label k → v i k ≠ 0 →
      v i j ≤ B ^ 2 / ((b (label k) : ℝ) ^ 3 + 1))
    (j k : C) :
    (∑ i, v i j * v i k) ≤
      B ^ 4 / ((b (max (label j) (label k)) : ℝ) ^ 3 + 1) := by
  rcases le_total (label j) (label k) with hjk | hkj
  · simpa only [max_eq_right hjk] using
      pair_energy_le_of_label_le v hv B hcol label b hcap j k hjk
  · simpa only [max_eq_left hkj, mul_comm] using
      pair_energy_le_of_label_le v hv B hcol label b hcap k j hkj

/-- The ordered-pair energy follows from actual pointwise support caps and
cumulative counts, not an assumed pair or total energy bound. -/
theorem total_energy_le
    (v : R → C → ℝ) (hv : ∀ i j, 0 ≤ v i j)
    (B : ℝ) (hcol : ∀ j, (∑ i, v i j) ≤ B ^ 2)
    (label : C → Fin L) (b : Fin L → ℕ)
    (hcard : ∀ r, (columnsThrough label r).card ≤ b r)
    (hcap : ∀ i j k, label j ≤ label k → v i k ≠ 0 →
      v i j ≤ B ^ 2 / ((b (label k) : ℝ) ^ 3 + 1)) :
    (∑ j, ∑ k, ∑ i, v i j * v i k) ≤
      B ^ 4 * ∑ r, (b r : ℝ) ^ 2 / ((b r : ℝ) ^ 3 + 1) := by
  calc
    _ ≤ ∑ j, ∑ k, B ^ 4 / ((b (max (label j) (label k)) : ℝ) ^ 3 + 1) :=
      Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ =>
        pair_energy_le v hv B hcol label b hcap j k
    _ = ∑ r, ((columnPairsAt label r).card : ℝ) *
        (B ^ 4 / ((b r : ℝ) ^ 3 + 1)) :=
      sum_pair_weights_eq label (fun r => B ^ 4 / ((b r : ℝ) ^ 3 + 1))
    _ ≤ ∑ r, (b r : ℝ) ^ 2 * (B ^ 4 / ((b r : ℝ) ^ 3 + 1)) := by
      apply Finset.sum_le_sum
      intro r _
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast card_columnPairsAt_le label b hcard r
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      ring

/-- The cubic denominator beats the squared count by one reciprocal factor. -/
theorem budget_ratio_le_reciprocal (b : ℕ) (hb : 1 ≤ b) :
    (b : ℝ) ^ 2 / ((b : ℝ) ^ 3 + 1) ≤ 1 / (b : ℝ) := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  apply (div_le_div_iff₀ (by positivity) hb0).mpr
  nlinarith

/-- Geometric growth of the deterministic budgets makes the total count
loss at most two, including an empty grade type. -/
theorem budget_ratio_sum_le_two (b : Fin L → ℕ)
    (hgrowth : ∀ r, 2 ^ r.val ≤ b r) :
    (∑ r, (b r : ℝ) ^ 2 / ((b r : ℝ) ^ 3 + 1)) ≤ 2 := by
  calc
    _ ≤ ∑ r : Fin L, (1 / (2 : ℝ)) ^ r.val := by
      apply Finset.sum_le_sum
      intro r _
      have hpow : 0 < (2 : ℕ) ^ r.val := by positivity
      have hb : 1 ≤ b r := by have := hgrowth r; omega
      apply (budget_ratio_le_reciprocal (b r) hb).trans
      have hgrowthR : (2 : ℝ) ^ r.val ≤ b r := by exact_mod_cast hgrowth r
      have h := one_div_le_one_div_of_le (by positivity : 0 < (2 : ℝ) ^ r.val) hgrowthR
      simpa only [one_div_pow] using h
    _ ≤ 2 := by
      simpa only [Fin.sum_univ_eq_sum_range] using sum_geometric_two_le L

/-- Final deterministic variance-overlap estimate for the graded original
columns. The actual-mask support cap remains visible and must be discharged. -/
theorem total_energy_le_two
    (v : R → C → ℝ) (hv : ∀ i j, 0 ≤ v i j)
    (B : ℝ) (hcol : ∀ j, (∑ i, v i j) ≤ B ^ 2)
    (label : C → Fin L) (b : Fin L → ℕ)
    (hcard : ∀ r, (columnsThrough label r).card ≤ b r)
    (hgrowth : ∀ r, 2 ^ r.val ≤ b r)
    (hcap : ∀ i j k, label j ≤ label k → v i k ≠ 0 →
      v i j ≤ B ^ 2 / ((b (label k) : ℝ) ^ 3 + 1)) :
    (∑ j, ∑ k, ∑ i, v i j * v i k) ≤ 2 * B ^ 4 := by
  calc
    _ ≤ B ^ 4 * ∑ r, (b r : ℝ) ^ 2 / ((b r : ℝ) ^ 3 + 1) :=
      total_energy_le v hv B hcol label b hcard hcap
    _ ≤ B ^ 4 * 2 := mul_le_mul_of_nonneg_left (budget_ratio_sum_le_two b hgrowth) (by positivity)
    _ = _ := mul_comm _ _

end MI32.GradedVarianceEnergy
