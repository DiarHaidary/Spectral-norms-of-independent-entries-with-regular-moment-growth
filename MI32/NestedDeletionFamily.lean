import MI32.NestedDeletionSelection
import MI32.DeletionScheduleArithmetic
import MI32.NestedShells
import MI32.VarianceScaleBasics
import MI32.WeakDeletionMonotonicity

/-!
# The explicit nested deletion family at the doubly exponential schedule

The nested two-sided deterministic deletion construction is instantiated
at the explicit schedule `budget r = 2^(5^r) - 1` with threshold parameter
`budget r ^ 3`, started from an actual weak-moment minimizer at budget one.
This packages the facts the block decomposition needs: the scheduled
cardinality bound, exhaustion of the original indices at the horizon
`n + 1`, both variance screens in divided form, and one uniform
weak-moment screen covering the initial stage. The first-shell level of
every original index is specialised to this family.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace MI32.NestedDeletionFamily

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {n : ℕ}
  {X : Ω → Matrix (Fin n) (Fin n) ℝ}

/-- The explicit nested deterministic original deletion family. -/
def sets (μ : Measure Ω) (X : Ω → Matrix (Fin n) (Fin n) ℝ) : ℕ → Finset (Fin n) :=
  NestedDeletionSelection.twoSidedSets μ X (varianceScale μ X)
    DeletionScheduleArithmetic.budget
    (fun r => DeletionScheduleArithmetic.budget r ^ 3)
    (NestedDeletionSelection.minimizingSet μ X 1)

/-- The initial set is the actual minimizer at budget one. -/
@[simp] theorem sets_zero : sets μ X 0 = NestedDeletionSelection.minimizingSet μ X 1 := rfl

/-- Successive sets are the two-sided enlargements at the scheduled budgets. -/
theorem sets_succ (r : ℕ) :
    sets μ X (r + 1) = NestedDeletionSelection.twoSidedNextSet μ X (varianceScale μ X)
      (sets μ X r) (DeletionScheduleArithmetic.budget r)
      (DeletionScheduleArithmetic.budget r ^ 3) := rfl

/-- The family is nested. -/
theorem sets_mono : Monotone (sets μ X) :=
  NestedDeletionSelection.twoSidedSets_mono μ X _ _ _ _

/-- The scheduled budgets are respected at every stage. -/
theorem card_sets_le (r : ℕ) :
    (sets μ X r).card ≤ DeletionScheduleArithmetic.budget r := by
  induction r with
  | zero =>
    rw [sets_zero, DeletionScheduleArithmetic.budget_zero]
    exact (NestedDeletionSelection.minimizingSet_spec μ X 1).1
  | succ r ih =>
    have h1 := NestedDeletionSelection.twoSidedSets_card_succ_le μ X (varianceScale μ X)
      DeletionScheduleArithmetic.budget (fun r => DeletionScheduleArithmetic.budget r ^ 3)
      (NestedDeletionSelection.minimizingSet μ X 1)
      (fun j => VarianceScaleBasics.col_variance_le_sq (μ := μ) X j)
      (fun i => VarianceScaleBasics.row_variance_le_sq (μ := μ) X i) r
    have h2 := DeletionScheduleArithmetic.step_card_le r (sets μ X r).card ih
    calc
      (sets μ X (r + 1)).card
          ≤ 2 * (sets μ X r).card * (DeletionScheduleArithmetic.budget r ^ 3 + 1) +
            DeletionScheduleArithmetic.budget r := h1
      _ = 2 * ((sets μ X r).card + (sets μ X r).card * DeletionScheduleArithmetic.budget r ^ 3) +
            DeletionScheduleArithmetic.budget r := by ring
      _ ≤ _ := h2

/-- The family exhausts the original indices at the explicit finite horizon. -/
theorem sets_horizon_eq_univ : sets μ X (n + 1) = Finset.univ :=
  NestedDeletionSelection.twoSidedSets_succ_eq_univ μ X _ _ _ _ n
    (DeletionScheduleArithmetic.finite_terminal_bound n)

/-- Marked original column against a surviving row. -/
theorem column_screen (r s : ℕ) (hrs : r + 1 ≤ s)
    (j : Fin n) (hj : j ∈ sets μ X r) (i : Fin n) (hi : i ∉ sets μ X s) :
    (∫ ω, X ω i j ^ 2 ∂μ)
      ≤ varianceScale μ X ^ 2 / ((DeletionScheduleArithmetic.budget r : ℝ) ^ 3 + 1) := by
  have h := NestedDeletionSelection.twoSidedSets_surviving_column_le_of_le μ X
    (varianceScale μ X) DeletionScheduleArithmetic.budget
    (fun r => DeletionScheduleArithmetic.budget r ^ 3)
    (NestedDeletionSelection.minimizingSet μ X 1) r s hrs j hj i hi
  have hpos : (0 : ℝ) < (DeletionScheduleArithmetic.budget r : ℝ) ^ 3 + 1 := by positivity
  rw [le_div_iff₀ hpos, mul_comm]
  simpa only [Nat.cast_pow] using h

/-- Marked original row against a surviving column. -/
theorem row_screen (r s : ℕ) (hrs : r + 1 ≤ s)
    (i : Fin n) (hi : i ∈ sets μ X r) (j : Fin n) (hj : j ∉ sets μ X s) :
    (∫ ω, X ω i j ^ 2 ∂μ)
      ≤ varianceScale μ X ^ 2 / ((DeletionScheduleArithmetic.budget r : ℝ) ^ 3 + 1) := by
  have h := NestedDeletionSelection.twoSidedSets_surviving_row_le_of_le μ X
    (varianceScale μ X) DeletionScheduleArithmetic.budget
    (fun r => DeletionScheduleArithmetic.budget r ^ 3)
    (NestedDeletionSelection.minimizingSet μ X 1) r s hrs i hi j hj
  have hpos : (0 : ℝ) < (DeletionScheduleArithmetic.budget r : ℝ) ^ 3 + 1 := by positivity
  rw [le_div_iff₀ hpos, mul_comm]
  simpa only [Nat.cast_pow] using h

/-- One uniform weak-moment screen, including the first stage where the
minimizer at budget one supplies the exact order log 2. -/
theorem weak_screen
    (hX : ∀ i j, Measurable (fun ω => X ω i j))
    (hint : ∀ i j (p : ℝ), 0 < p → Integrable (fun ω => |X ω i j| ^ p) μ)
    (a : ℕ) (ha : 1 ≤ a) :
    weakMoment μ X (sets μ X (a - 1)) (DeletionScheduleArithmetic.order (a - 2))
      ≤ deletionScale μ X := by
  rcases Nat.lt_or_ge a 2 with h2 | h2
  · have ha1 : a = 1 := by omega
    subst ha1
    show weakMoment μ X (NestedDeletionSelection.minimizingSet μ X 1)
      (Real.log (DeletionScheduleArithmetic.budget 0 + 1 : ℕ)) ≤ _
    rw [DeletionScheduleArithmetic.budget_zero]
    exact NestedDeletionSelection.minimizingSet_le_deletionScale_of_pos μ X 1 le_rfl
  · obtain ⟨k, rfl⟩ : ∃ k, a = k + 2 := ⟨a - 2, by omega⟩
    show weakMoment μ X (sets μ X (k + 1))
      (Real.log (DeletionScheduleArithmetic.budget k + 1 : ℕ)) ≤ _
    exact NestedDeletionSelection.twoSidedSets_weakMoment_le_scale_of_le X hX hint
      (varianceScale μ X) DeletionScheduleArithmetic.budget
      (fun r => DeletionScheduleArithmetic.budget r ^ 3)
      (NestedDeletionSelection.minimizingSet μ X 1) k (k + 1) le_rfl
      (DeletionScheduleArithmetic.budget_pos k)

/-- The first stage at which an original index is selected. -/
def level (μ : Measure Ω) (X : Ω → Matrix (Fin n) (Fin n) ℝ) (i : Fin n) : Fin (n + 2) :=
  NestedShells.level (sets μ X) (n + 1) sets_horizon_eq_univ i

/-- Cumulative first-level membership is exactly the scheduled nested set. -/
theorem level_le_iff (r : ℕ) (i : Fin n) :
    (level μ X i).val ≤ r ↔ i ∈ sets μ X r :=
  NestedShells.level_le_iff (sets μ X) sets_mono (n + 1) sets_horizon_eq_univ i r

/-- The cumulative level sets respect the scheduled budgets. -/
theorem card_filter_level_le (r : ℕ) :
    (Finset.univ.filter (fun i : Fin n => (level μ X i).val ≤ r)).card
      ≤ DeletionScheduleArithmetic.budget r := by
  refine (Finset.card_le_card ?_).trans (card_sets_le (μ := μ) (X := X) r)
  intro i hi
  rw [Finset.mem_filter] at hi
  exact (level_le_iff r i).mp hi.2

end MI32.NestedDeletionFamily
