import MI32.DeletionVarianceSelection
import MI32.WeakMomentBasics
import MI32.WeakDeletionMonotonicity

/-!
# Nested deterministic deletion sets from the original matrix law

At each step the previous original index set is enlarged by its explicit
variance-threshold selection and by an actual minimizing deletion set at
the new budget. All sets are deterministic functions of the original law;
the same set deletes both original axes. The schedule is explicit input,
and this construction assumes no final deletion bound or permutation theorem.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace MI32.NestedDeletionSelection

variable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}

/-- Choose an actual finite-budget minimizer at exactly the source's
logarithmic moment order. This choice is independent of the random sample. -/
def minimizingSet (μ : Measure Ω) (X : Ω → Matrix (Fin n) (Fin n) ℝ)
    (b : ℕ) : Finset (Fin n) :=
  Classical.choose (WeakMomentBasics.exists_minimizing_set μ X b (Real.log (b + 1 : ℕ)))

theorem minimizingSet_spec (μ : Measure Ω) (X : Ω → Matrix (Fin n) (Fin n) ℝ) (b : ℕ) :
    (minimizingSet μ X b).card ≤ b ∧
      weakMoment μ X (minimizingSet μ X b) (Real.log (b + 1 : ℕ)) =
        sInf {w : ℝ | ∃ J : Finset (Fin n), J.card ≤ b ∧
          w = weakMoment μ X J (Real.log (b + 1 : ℕ))} ∧
      ∀ J : Finset (Fin n), J.card ≤ b →
        weakMoment μ X (minimizingSet μ X b) (Real.log (b + 1 : ℕ)) ≤
          weakMoment μ X J (Real.log (b + 1 : ℕ)) :=
  Classical.choose_spec (WeakMomentBasics.exists_minimizing_set μ X b (Real.log (b + 1 : ℕ)))

theorem minimizingSet_le_deletionScale (μ : Measure Ω)
    (X : Ω → Matrix (Fin n) (Fin n) ℝ) (b : ℕ) (hb : 1 ≤ b) (hbn : b ≤ n) :
    weakMoment μ X (minimizingSet μ X b) (Real.log (b + 1 : ℕ)) ≤ deletionScale μ X :=
  (minimizingSet_spec μ X b).2.1.trans_le (WeakMomentBasics.minimum_le_deletionScale μ X b hb hbn)

/-- Budgets above the dimension are harmless: full deletion is feasible
and has zero weak moment. Thus every positive budget minimizer is bounded
by the literal deletion scale, without an upper bound on its budget. -/
theorem minimizingSet_le_deletionScale_of_pos (μ : Measure Ω)
    (X : Ω → Matrix (Fin n) (Fin n) ℝ) (b : ℕ) (hb : 1 ≤ b) :
    weakMoment μ X (minimizingSet μ X b) (Real.log (b + 1 : ℕ)) ≤ deletionScale μ X := by
  by_cases hbn : b ≤ n
  · exact minimizingSet_le_deletionScale μ X b hb hbn
  · have hfull := (minimizingSet_spec μ X b).2.2 Finset.univ
      (by simpa using (show n ≤ b by omega))
    rw [WeakMomentBasics.weakMoment_full_deletion_eq_zero μ X _
      (WeakMomentBasics.log_budget_pos b hb)] at hfull
    exact hfull.trans (WeakMomentBasics.deletionScale_nonneg μ X)

/-- The actual original second-integral weights, with no relabeling of either axis. -/
def varianceWeights (μ : Measure Ω) (X : Ω → Matrix (Fin n) (Fin n) ℝ)
    (i j : Fin n) : ℝ := ∫ ω, (X ω i j) ^ 2 ∂μ

theorem varianceWeights_nonneg (μ : Measure Ω)
    (X : Ω → Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    0 ≤ varianceWeights μ X i j := integral_nonneg fun ω => sq_nonneg (X ω i j)

/-- Enlarge the previous original set by the threshold selection and by
an actual minimizer for the next logarithmic budget. -/
def nextSet (μ : Measure Ω) (X : Ω → Matrix (Fin n) (Fin n) ℝ)
    (B : ℝ) (S : Finset (Fin n)) (b t : ℕ) : Finset (Fin n) :=
  DeletionVarianceSelection.selection (varianceWeights μ X) S B t ∪ minimizingSet μ X b

theorem subset_nextSet (μ : Measure Ω) (X : Ω → Matrix (Fin n) (Fin n) ℝ)
    (B : ℝ) (S : Finset (Fin n)) (b t : ℕ) : S ⊆ nextSet μ X B S b t :=
  (DeletionVarianceSelection.subset_selection (varianceWeights μ X) S B t).trans
    Finset.subset_union_left

theorem minimizingSet_subset_nextSet (μ : Measure Ω)
    (X : Ω → Matrix (Fin n) (Fin n) ℝ) (B : ℝ) (S : Finset (Fin n)) (b t : ℕ) :
    minimizingSet μ X b ⊆ nextSet μ X B S b t := Finset.subset_union_right

theorem card_nextSet_le (μ : Measure Ω) (X : Ω → Matrix (Fin n) (Fin n) ℝ)
    (B : ℝ) (S : Finset (Fin n)) (b t : ℕ)
    (hcol : ∀ j ∈ S, (∑ i, varianceWeights μ X i j) ≤ B ^ 2) :
    (nextSet μ X B S b t).card ≤ S.card * (t + 1) + b := by
  calc
    _ ≤ (DeletionVarianceSelection.selection (varianceWeights μ X) S B t).card +
        (minimizingSet μ X b).card := Finset.card_union_le _ _
    _ ≤ (S.card + S.card * t) + b := Nat.add_le_add
      (DeletionVarianceSelection.card_selection_le (varianceWeights μ X)
        (varianceWeights_nonneg μ X) S B t hcol) (minimizingSet_spec μ X b).1
    _ = _ := by ring

/-- Every surviving original row has controlled variance against each
previously marked original column, after both enlargement operations. -/
theorem nextSet_surviving_entry_le (μ : Measure Ω)
    (X : Ω → Matrix (Fin n) (Fin n) ℝ) (B : ℝ) (S : Finset (Fin n)) (b t : ℕ)
    (j : Fin n) (hj : j ∈ S) (i : Fin n) (hi : i ∉ nextSet μ X B S b t) :
    ((t : ℝ) + 1) * (∫ ω, (X ω i j) ^ 2 ∂μ) ≤ B ^ 2 :=
  DeletionVarianceSelection.surviving_entry_le (varianceWeights μ X) S B t j hj i
    (fun h => hi (Finset.mem_union_left _ h))

/-- An arbitrary prescribed initial original set and natural schedules
produce a fully specified nested sequence of deterministic original sets. -/
def sets (μ : Measure Ω) (X : Ω → Matrix (Fin n) (Fin n) ℝ) (B : ℝ)
    (b t : ℕ → ℕ) (S₀ : Finset (Fin n)) : ℕ → Finset (Fin n)
  | 0 => S₀
  | r + 1 => nextSet μ X B (sets μ X B b t S₀ r) (b r) (t r)

@[simp] theorem sets_zero (μ : Measure Ω) (X : Ω → Matrix (Fin n) (Fin n) ℝ)
    (B : ℝ) (b t : ℕ → ℕ) (S₀ : Finset (Fin n)) : sets μ X B b t S₀ 0 = S₀ := rfl

theorem sets_succ (μ : Measure Ω) (X : Ω → Matrix (Fin n) (Fin n) ℝ)
    (B : ℝ) (b t : ℕ → ℕ) (S₀ : Finset (Fin n)) (r : ℕ) :
    sets μ X B b t S₀ (r + 1) = nextSet μ X B (sets μ X B b t S₀ r) (b r) (t r) := rfl

theorem sets_subset_succ (μ : Measure Ω) (X : Ω → Matrix (Fin n) (Fin n) ℝ)
    (B : ℝ) (b t : ℕ → ℕ) (S₀ : Finset (Fin n)) (r : ℕ) :
    sets μ X B b t S₀ r ⊆ sets μ X B b t S₀ (r + 1) :=
  subset_nextSet μ X B (sets μ X B b t S₀ r) (b r) (t r)

theorem sets_mono (μ : Measure Ω) (X : Ω → Matrix (Fin n) (Fin n) ℝ)
    (B : ℝ) (b t : ℕ → ℕ) (S₀ : Finset (Fin n)) : Monotone (sets μ X B b t S₀) :=
  monotone_nat_of_le_succ (sets_subset_succ μ X B b t S₀)

theorem sets_card_succ_le (μ : Measure Ω) (X : Ω → Matrix (Fin n) (Fin n) ℝ)
    (B : ℝ) (b t : ℕ → ℕ) (S₀ : Finset (Fin n))
    (hcol : ∀ j, (∑ i, ∫ ω, (X ω i j) ^ 2 ∂μ) ≤ B ^ 2) (r : ℕ) :
    (sets μ X B b t S₀ (r + 1)).card ≤ (sets μ X B b t S₀ r).card * (t r + 1) + b r :=
  card_nextSet_le μ X B (sets μ X B b t S₀ r) (b r) (t r) (fun j _ => hcol j)

theorem sets_surviving_entry_le (μ : Measure Ω)
    (X : Ω → Matrix (Fin n) (Fin n) ℝ) (B : ℝ) (b t : ℕ → ℕ) (S₀ : Finset (Fin n))
    (r : ℕ) (j : Fin n) (hj : j ∈ sets μ X B b t S₀ r)
    (i : Fin n) (hi : i ∉ sets μ X B b t S₀ (r + 1)) :
    ((t r : ℝ) + 1) * (∫ ω, (X ω i j) ^ 2 ∂μ) ≤ B ^ 2 :=
  nextSet_surviving_entry_le μ X B (sets μ X B b t S₀ r) (b r) (t r) j hj i hi

/-- Future enlargements preserve every already-established marked-column
variance bound at its original threshold. -/
theorem sets_surviving_entry_le_of_le (μ : Measure Ω)
    (X : Ω → Matrix (Fin n) (Fin n) ℝ) (B : ℝ) (b t : ℕ → ℕ) (S₀ : Finset (Fin n))
    (r s : ℕ) (hrs : r + 1 ≤ s) (j : Fin n) (hj : j ∈ sets μ X B b t S₀ r)
    (i : Fin n) (hi : i ∉ sets μ X B b t S₀ s) :
    ((t r : ℝ) + 1) * (∫ ω, (X ω i j) ^ 2 ∂μ) ≤ B ^ 2 :=
  sets_surviving_entry_le μ X B b t S₀ r j hj i
    (fun h => hi (sets_mono μ X B b t S₀ hrs h))

/-- The next exact original set inherits the actual minimizing weak
bound by compressing both deterministic test vectors to its complement. -/
theorem nextSet_weakMoment_le_scale {μ : Measure Ω}
    (X : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hX : ∀ i j, Measurable (fun ω => X ω i j))
    (hint : ∀ i j (p : ℝ), 0 < p → Integrable (fun ω => |X ω i j| ^ p) μ)
    (B : ℝ) (S : Finset (Fin n)) (b t : ℕ) (hb : 1 ≤ b) :
    weakMoment μ X (nextSet μ X B S b t) (Real.log (b + 1 : ℕ)) ≤ deletionScale μ X :=
  (WeakDeletionMonotonicity.weakMoment_antitone X hX hint _ _
    (minimizingSet_subset_nextSet μ X B S b t) _ (WeakMomentBasics.log_budget_pos b hb)).trans
      (minimizingSet_le_deletionScale_of_pos μ X b hb)

theorem sets_weakMoment_succ_le_scale {μ : Measure Ω}
    (X : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hX : ∀ i j, Measurable (fun ω => X ω i j))
    (hint : ∀ i j (p : ℝ), 0 < p → Integrable (fun ω => |X ω i j| ^ p) μ)
    (B : ℝ) (b t : ℕ → ℕ) (S₀ : Finset (Fin n)) (r : ℕ) (hb : 1 ≤ b r) :
    weakMoment μ X (sets μ X B b t S₀ (r + 1)) (Real.log (b r + 1 : ℕ)) ≤
      deletionScale μ X :=
  nextSet_weakMoment_le_scale X hX hint B (sets μ X B b t S₀ r) (b r) (t r) hb

/-- Subsequent enlargements preserve the weak bound at its original exact
logarithmic order. No moment-order replacement is made. -/
theorem sets_weakMoment_le_scale_of_le {μ : Measure Ω}
    (X : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hX : ∀ i j, Measurable (fun ω => X ω i j))
    (hint : ∀ i j (p : ℝ), 0 < p → Integrable (fun ω => |X ω i j| ^ p) μ)
    (B : ℝ) (b t : ℕ → ℕ) (S₀ : Finset (Fin n))
    (r s : ℕ) (hrs : r + 1 ≤ s) (hb : 1 ≤ b r) :
    weakMoment μ X (sets μ X B b t S₀ s) (Real.log (b r + 1 : ℕ)) ≤ deletionScale μ X :=
  (WeakDeletionMonotonicity.weakMoment_antitone X hX hint _ _
    (sets_mono μ X B b t S₀ hrs) _ (WeakMomentBasics.log_budget_pos (b r) hb)).trans
      (sets_weakMoment_succ_le_scale X hX hint B b t S₀ r hb)

section TwoSided

/-- Both variance orientations use one original deletion set. Once the
budget reaches the original dimension, select the full original set. -/
def twoSidedNextSet (μ : Measure Ω) (X : Ω → Matrix (Fin n) (Fin n) ℝ)
    (B : ℝ) (S : Finset (Fin n)) (b t : ℕ) : Finset (Fin n) :=
  if n ≤ b then Finset.univ else nextSet μ X B S b t ∪
    DeletionVarianceSelection.selection (fun i j => varianceWeights μ X j i) S B t

theorem twoSidedNextSet_eq_univ (μ : Measure Ω)
    (X : Ω → Matrix (Fin n) (Fin n) ℝ) (B : ℝ) (S : Finset (Fin n))
    (b t : ℕ) (hb : n ≤ b) : twoSidedNextSet μ X B S b t = Finset.univ := by
  simp [twoSidedNextSet, hb]

theorem subset_twoSidedNextSet (μ : Measure Ω) (X : Ω → Matrix (Fin n) (Fin n) ℝ)
    (B : ℝ) (S : Finset (Fin n)) (b t : ℕ) : S ⊆ twoSidedNextSet μ X B S b t := by
  unfold twoSidedNextSet
  split_ifs
  · exact Finset.subset_univ _
  · exact (subset_nextSet μ X B S b t).trans Finset.subset_union_left

theorem minimizingSet_subset_twoSidedNextSet (μ : Measure Ω)
    (X : Ω → Matrix (Fin n) (Fin n) ℝ) (B : ℝ) (S : Finset (Fin n)) (b t : ℕ) :
    minimizingSet μ X b ⊆ twoSidedNextSet μ X B S b t := by
  unfold twoSidedNextSet
  split_ifs
  · exact Finset.subset_univ _
  · exact (minimizingSet_subset_nextSet μ X B S b t).trans Finset.subset_union_left

/-- The size cost charges both original variance selections and the
actual weak minimizer; overlaps can only improve this bound. -/
theorem card_twoSidedNextSet_le (μ : Measure Ω)
    (X : Ω → Matrix (Fin n) (Fin n) ℝ) (B : ℝ) (S : Finset (Fin n)) (b t : ℕ)
    (hcol : ∀ j ∈ S, (∑ i, varianceWeights μ X i j) ≤ B ^ 2)
    (hrow : ∀ i ∈ S, (∑ j, varianceWeights μ X i j) ≤ B ^ 2) :
    (twoSidedNextSet μ X B S b t).card ≤ 2 * S.card * (t + 1) + b := by
  by_cases hb : n ≤ b
  · rw [twoSidedNextSet_eq_univ μ X B S b t hb, Finset.card_univ, Fintype.card_fin]
    omega
  · rw [twoSidedNextSet, if_neg hb]
    calc
      _ ≤ (nextSet μ X B S b t).card +
          (DeletionVarianceSelection.selection (fun i j => varianceWeights μ X j i) S B t).card :=
        Finset.card_union_le _ _
      _ ≤ (S.card * (t + 1) + b) + (S.card + S.card * t) := Nat.add_le_add
        (card_nextSet_le μ X B S b t hcol)
        (DeletionVarianceSelection.card_selection_le (fun i j => varianceWeights μ X j i)
          (fun i j => varianceWeights_nonneg μ X j i) S B t hrow)
      _ = _ := by ring

theorem twoSidedNextSet_surviving_column_le (μ : Measure Ω)
    (X : Ω → Matrix (Fin n) (Fin n) ℝ) (B : ℝ) (S : Finset (Fin n)) (b t : ℕ)
    (j : Fin n) (hj : j ∈ S) (i : Fin n) (hi : i ∉ twoSidedNextSet μ X B S b t) :
    ((t : ℝ) + 1) * (∫ ω, (X ω i j) ^ 2 ∂μ) ≤ B ^ 2 := by
  by_cases hb : n ≤ b
  · simp [twoSidedNextSet, hb] at hi
  · apply nextSet_surviving_entry_le μ X B S b t j hj i
    intro h
    exact hi (by simp only [twoSidedNextSet, if_neg hb]; exact Finset.mem_union_left _ h)

theorem twoSidedNextSet_surviving_row_le (μ : Measure Ω)
    (X : Ω → Matrix (Fin n) (Fin n) ℝ) (B : ℝ) (S : Finset (Fin n)) (b t : ℕ)
    (i : Fin n) (hi : i ∈ S) (j : Fin n) (hj : j ∉ twoSidedNextSet μ X B S b t) :
    ((t : ℝ) + 1) * (∫ ω, (X ω i j) ^ 2 ∂μ) ≤ B ^ 2 := by
  by_cases hb : n ≤ b
  · simp [twoSidedNextSet, hb] at hj
  · apply DeletionVarianceSelection.surviving_entry_le
      (fun a b => varianceWeights μ X b a) S B t i hi j
    intro h
    exact hj (by simp only [twoSidedNextSet, if_neg hb]; exact Finset.mem_union_right _ h)

theorem twoSidedNextSet_weakMoment_le_scale {μ : Measure Ω}
    (X : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hX : ∀ i j, Measurable (fun ω => X ω i j))
    (hint : ∀ i j (p : ℝ), 0 < p → Integrable (fun ω => |X ω i j| ^ p) μ)
    (B : ℝ) (S : Finset (Fin n)) (b t : ℕ) (hb : 1 ≤ b) :
    weakMoment μ X (twoSidedNextSet μ X B S b t) (Real.log (b + 1 : ℕ)) ≤ deletionScale μ X :=
  (WeakDeletionMonotonicity.weakMoment_antitone X hX hint _ _
    (minimizingSet_subset_twoSidedNextSet μ X B S b t) _ (WeakMomentBasics.log_budget_pos b hb)).trans
      (minimizingSet_le_deletionScale_of_pos μ X b hb)

/-- A nested sequence controlling both original variance orientations. -/
def twoSidedSets (μ : Measure Ω) (X : Ω → Matrix (Fin n) (Fin n) ℝ) (B : ℝ)
    (b t : ℕ → ℕ) (S₀ : Finset (Fin n)) : ℕ → Finset (Fin n)
  | 0 => S₀
  | r + 1 => twoSidedNextSet μ X B (twoSidedSets μ X B b t S₀ r) (b r) (t r)

@[simp] theorem twoSidedSets_zero (μ : Measure Ω) (X : Ω → Matrix (Fin n) (Fin n) ℝ)
    (B : ℝ) (b t : ℕ → ℕ) (S₀ : Finset (Fin n)) : twoSidedSets μ X B b t S₀ 0 = S₀ := rfl

theorem twoSidedSets_succ (μ : Measure Ω) (X : Ω → Matrix (Fin n) (Fin n) ℝ)
    (B : ℝ) (b t : ℕ → ℕ) (S₀ : Finset (Fin n)) (r : ℕ) :
    twoSidedSets μ X B b t S₀ (r + 1) =
      twoSidedNextSet μ X B (twoSidedSets μ X B b t S₀ r) (b r) (t r) := rfl

theorem twoSidedSets_mono (μ : Measure Ω) (X : Ω → Matrix (Fin n) (Fin n) ℝ)
    (B : ℝ) (b t : ℕ → ℕ) (S₀ : Finset (Fin n)) : Monotone (twoSidedSets μ X B b t S₀) :=
  monotone_nat_of_le_succ (fun r =>
    subset_twoSidedNextSet μ X B (twoSidedSets μ X B b t S₀ r) (b r) (t r))

theorem twoSidedSets_card_succ_le (μ : Measure Ω)
    (X : Ω → Matrix (Fin n) (Fin n) ℝ) (B : ℝ) (b t : ℕ → ℕ) (S₀ : Finset (Fin n))
    (hcol : ∀ j, (∑ i, ∫ ω, (X ω i j) ^ 2 ∂μ) ≤ B ^ 2)
    (hrow : ∀ i, (∑ j, ∫ ω, (X ω i j) ^ 2 ∂μ) ≤ B ^ 2) (r : ℕ) :
    (twoSidedSets μ X B b t S₀ (r + 1)).card ≤
      2 * (twoSidedSets μ X B b t S₀ r).card * (t r + 1) + b r :=
  card_twoSidedNextSet_le μ X B (twoSidedSets μ X B b t S₀ r) (b r) (t r)
    (fun j _ => hcol j) (fun i _ => hrow i)

theorem twoSidedSets_surviving_column_le_of_le (μ : Measure Ω)
    (X : Ω → Matrix (Fin n) (Fin n) ℝ) (B : ℝ) (b t : ℕ → ℕ) (S₀ : Finset (Fin n))
    (r s : ℕ) (hrs : r + 1 ≤ s) (j : Fin n) (hj : j ∈ twoSidedSets μ X B b t S₀ r)
    (i : Fin n) (hi : i ∉ twoSidedSets μ X B b t S₀ s) :
    ((t r : ℝ) + 1) * (∫ ω, (X ω i j) ^ 2 ∂μ) ≤ B ^ 2 :=
  twoSidedNextSet_surviving_column_le μ X B (twoSidedSets μ X B b t S₀ r) (b r) (t r) j hj i
    (fun h => hi (twoSidedSets_mono μ X B b t S₀ hrs h))

theorem twoSidedSets_surviving_row_le_of_le (μ : Measure Ω)
    (X : Ω → Matrix (Fin n) (Fin n) ℝ) (B : ℝ) (b t : ℕ → ℕ) (S₀ : Finset (Fin n))
    (r s : ℕ) (hrs : r + 1 ≤ s) (i : Fin n) (hi : i ∈ twoSidedSets μ X B b t S₀ r)
    (j : Fin n) (hj : j ∉ twoSidedSets μ X B b t S₀ s) :
    ((t r : ℝ) + 1) * (∫ ω, (X ω i j) ^ 2 ∂μ) ≤ B ^ 2 :=
  twoSidedNextSet_surviving_row_le μ X B (twoSidedSets μ X B b t S₀ r) (b r) (t r) i hi j
    (fun h => hj (twoSidedSets_mono μ X B b t S₀ hrs h))

theorem twoSidedSets_weakMoment_succ_le_scale {μ : Measure Ω}
    (X : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hX : ∀ i j, Measurable (fun ω => X ω i j))
    (hint : ∀ i j (p : ℝ), 0 < p → Integrable (fun ω => |X ω i j| ^ p) μ)
    (B : ℝ) (b t : ℕ → ℕ) (S₀ : Finset (Fin n)) (r : ℕ) (hb : 1 ≤ b r) :
    weakMoment μ X (twoSidedSets μ X B b t S₀ (r + 1)) (Real.log (b r + 1 : ℕ)) ≤
      deletionScale μ X :=
  twoSidedNextSet_weakMoment_le_scale X hX hint B (twoSidedSets μ X B b t S₀ r) (b r) (t r) hb

theorem twoSidedSets_weakMoment_le_scale_of_le {μ : Measure Ω}
    (X : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hX : ∀ i j, Measurable (fun ω => X ω i j))
    (hint : ∀ i j (p : ℝ), 0 < p → Integrable (fun ω => |X ω i j| ^ p) μ)
    (B : ℝ) (b t : ℕ → ℕ) (S₀ : Finset (Fin n))
    (r s : ℕ) (hrs : r + 1 ≤ s) (hb : 1 ≤ b r) :
    weakMoment μ X (twoSidedSets μ X B b t S₀ s) (Real.log (b r + 1 : ℕ)) ≤ deletionScale μ X :=
  (WeakDeletionMonotonicity.weakMoment_antitone X hX hint _ _
    (twoSidedSets_mono μ X B b t S₀ hrs) _ (WeakMomentBasics.log_budget_pos (b r) hb)).trans
      (twoSidedSets_weakMoment_succ_le_scale X hX hint B b t S₀ r hb)

/-- The sequence reaches the full original set as soon as a scheduled
budget reaches the original dimension. -/
theorem twoSidedSets_succ_eq_univ (μ : Measure Ω)
    (X : Ω → Matrix (Fin n) (Fin n) ℝ) (B : ℝ) (b t : ℕ → ℕ) (S₀ : Finset (Fin n))
    (r : ℕ) (hb : n ≤ b r) : twoSidedSets μ X B b t S₀ (r + 1) = Finset.univ :=
  twoSidedNextSet_eq_univ μ X B (twoSidedSets μ X B b t S₀ r) (b r) (t r) hb

theorem twoSidedSets_eq_univ_of_le (μ : Measure Ω)
    (X : Ω → Matrix (Fin n) (Fin n) ℝ) (B : ℝ) (b t : ℕ → ℕ) (S₀ : Finset (Fin n))
    (r s : ℕ) (hrs : r + 1 ≤ s) (hb : n ≤ b r) : twoSidedSets μ X B b t S₀ s = Finset.univ := by
  apply Finset.Subset.antisymm (Finset.subset_univ _) _
  rw [← twoSidedSets_succ_eq_univ μ X B b t S₀ r hb]
  exact twoSidedSets_mono μ X B b t S₀ hrs

end TwoSided

end MI32.NestedDeletionSelection
