import MI32.Statement
import Mathlib.Tactic

/-!
# Finite same-index variance selection

For each marked original column, remove every original row whose variance
is strictly above the threshold `B²/(t+1)`. There are at most `t` such rows
per marked column. The one selected set contains the original marked set
and every removed row, so the same original index set can delete both axes.
The construction and all bounds include `t = 0` and `B = 0`.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace MI32.DeletionVarianceSelection

attribute [local instance] Classical.propDecidable

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Original rows strictly above the variance threshold in a fixed column.
Strict inequality is essential for the exact cardinal bound `t`. -/
def largeRows (v : I → I → ℝ) (B : ℝ) (t : ℕ) (j : I) : Finset I :=
  Finset.univ.filter (fun i => B ^ 2 < ((t : ℝ) + 1) * v i j)

omit [DecidableEq I] in
@[simp] theorem mem_largeRows (v : I → I → ℝ) (B : ℝ) (t : ℕ) (i j : I) :
    i ∈ largeRows v B t j ↔ B ^ 2 < ((t : ℝ) + 1) * v i j := by
  simp [largeRows]

omit [DecidableEq I] in
/-- A nonnegative column with total weight at most `B²` has at most `t`
entries strictly above `B²/(t+1)`. No positivity of `B` is required. -/
theorem card_largeRows_le (v : I → I → ℝ) (hv : ∀ i j, 0 ≤ v i j)
    (B : ℝ) (t : ℕ) (j : I) (hcol : (∑ i, v i j) ≤ B ^ 2) :
    (largeRows v B t j).card ≤ t := by
  by_contra hcard
  have hcardN : t + 1 ≤ (largeRows v B t j).card := by omega
  have hne : (largeRows v B t j).Nonempty := Finset.card_pos.mp (by omega)
  have hstrict : ((largeRows v B t j).card : ℝ) * B ^ 2 <
      ((t : ℝ) + 1) * ∑ i ∈ largeRows v B t j, v i j := by
    calc
      _ = ∑ _i ∈ largeRows v B t j, B ^ 2 := by simp
      _ < ∑ i ∈ largeRows v B t j, ((t : ℝ) + 1) * v i j :=
        Finset.sum_lt_sum_of_nonempty hne (fun i hi => (mem_largeRows v B t i j).mp hi)
      _ = _ := (Finset.mul_sum _ _ _).symm
  have hsum : (∑ i ∈ largeRows v B t j, v i j) ≤ B ^ 2 := by
    apply le_trans _ hcol
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun i _ _ => hv i j)
  have hupper := mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ (t : ℝ) + 1)
  have hcardR : (t : ℝ) + 1 ≤ ((largeRows v B t j).card : ℝ) := by exact_mod_cast hcardN
  have hlower := mul_le_mul_of_nonneg_right hcardR (sq_nonneg B)
  linarith

/-- One deterministic original index set retains the marked set and removes
every large row found in any marked original column. -/
def selection (v : I → I → ℝ) (S : Finset I) (B : ℝ) (t : ℕ) : Finset I :=
  S ∪ S.biUnion (largeRows v B t)

theorem subset_selection (v : I → I → ℝ) (S : Finset I) (B : ℝ) (t : ℕ) :
    S ⊆ selection v S B t := Finset.subset_union_left

theorem largeRows_subset_selection (v : I → I → ℝ) (S : Finset I) (B : ℝ)
    (t : ℕ) (j : I) (hj : j ∈ S) : largeRows v B t j ⊆ selection v S B t := by
  intro i hi
  exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j, hj, hi⟩)

/-- At most `card(S) * t` additional original indices are selected. -/
theorem card_selection_le (v : I → I → ℝ) (hv : ∀ i j, 0 ≤ v i j)
    (S : Finset I) (B : ℝ) (t : ℕ) (hcol : ∀ j ∈ S, (∑ i, v i j) ≤ B ^ 2) :
    (selection v S B t).card ≤ S.card + S.card * t := by
  calc
    _ ≤ S.card + (S.biUnion (largeRows v B t)).card := Finset.card_union_le _ _
    _ ≤ S.card + ∑ j ∈ S, (largeRows v B t j).card :=
      Nat.add_le_add_left Finset.card_biUnion_le _
    _ ≤ S.card + ∑ _j ∈ S, t := Nat.add_le_add_left
      (Finset.sum_le_sum fun j hj => card_largeRows_le v hv B t j (hcol j hj)) _
    _ = _ := by simp

/-- Every surviving original row is below the threshold in every marked
original column. This statement holds for the explicit selected set. -/
theorem surviving_entry_le (v : I → I → ℝ) (S : Finset I) (B : ℝ) (t : ℕ)
    (j : I) (hj : j ∈ S) (i : I) (hi : i ∉ selection v S B t) :
    ((t : ℝ) + 1) * v i j ≤ B ^ 2 := by
  by_contra h
  exact hi (largeRows_subset_selection v S B t j hj
    ((mem_largeRows v B t i j).mpr (lt_of_not_ge h)))

theorem surviving_entry_le_div (v : I → I → ℝ) (S : Finset I) (B : ℝ) (t : ℕ)
    (j : I) (hj : j ∈ S) (i : I) (hi : i ∉ selection v S B t) :
    v i j ≤ B ^ 2 / ((t : ℝ) + 1) := by
  apply (le_div_iff₀ (by positivity : 0 < (t : ℝ) + 1)).mpr
  simpa only [mul_comm] using surviving_entry_le v S B t j hj i hi

/-- Enlarging the marked original set enlarges its selection. Thus the
selection can be used compatibly with nested original index families. -/
theorem selection_mono (v : I → I → ℝ) (S S' : Finset I) (hS : S ⊆ S')
    (B : ℝ) (t : ℕ) : selection v S B t ⊆ selection v S' B t := by
  intro i hi
  rcases Finset.mem_union.mp hi with hi | hi
  · exact Finset.mem_union_left _ (hS hi)
  · rcases Finset.mem_biUnion.mp hi with ⟨j, hj, hij⟩
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j, hS hj, hij⟩)

/-- At t=0 no additional index is needed or selected. -/
theorem selection_zero (v : I → I → ℝ) (hv : ∀ i j, 0 ≤ v i j)
    (S : Finset I) (B : ℝ) (hcol : ∀ j ∈ S, (∑ i, v i j) ≤ B ^ 2) :
    selection v S B 0 = S := by
  exact (Finset.eq_of_subset_of_card_le (subset_selection v S B 0)
    (by simpa using card_selection_le v hv S B 0 hcol)).symm

/-- A zero variance budget makes every marked column zero, so selection
adds no index at any value of t. -/
theorem selection_zero_budget (v : I → I → ℝ) (hv : ∀ i j, 0 ≤ v i j)
    (S : Finset I) (t : ℕ) (hcol : ∀ j ∈ S, (∑ i, v i j) ≤ 0) :
    selection v S 0 t = S := by
  have hz (j : I) (hj : j ∈ S) (i : I) : v i j = 0 := by
    apply le_antisymm _ (hv i j)
    exact (Finset.single_le_sum (fun a _ => hv a j) (Finset.mem_univ i)).trans (hcol j hj)
  apply Finset.Subset.antisymm _ (subset_selection v S 0 t)
  intro i hi
  rcases Finset.mem_union.mp hi with hi | hi
  · exact hi
  · rcases Finset.mem_biUnion.mp hi with ⟨j, hj, hij⟩
    have hlt := (mem_largeRows v 0 t i j).mp hij
    norm_num [hz j hj i] at hlt

/-- Deterministic finite selection with the exact requested size and
surviving-entry guarantees. No order statistics or permutation is assumed. -/
theorem exists_selection (v : I → I → ℝ) (hv : ∀ i j, 0 ≤ v i j)
    (S : Finset I) (B : ℝ) (t : ℕ) (hcol : ∀ j ∈ S, (∑ i, v i j) ≤ B ^ 2) :
    ∃ T : Finset I, S ⊆ T ∧ T.card ≤ S.card + S.card * t ∧
      ∀ j ∈ S, ∀ i ∉ T, ((t : ℝ) + 1) * v i j ≤ B ^ 2 :=
  ⟨selection v S B t, subset_selection v S B t, card_selection_le v hv S B t hcol,
    surviving_entry_le v S B t⟩

/-- The same deterministic construction applied to the actual original
second-integral weights. Moment finiteness belongs to the surrounding
probabilistic hypotheses; the finite selection itself uses only these weights. -/
theorem exists_variance_selection {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → Matrix I I ℝ) (S : Finset I) (B : ℝ) (t : ℕ)
    (hcol : ∀ j ∈ S, (∑ i, ∫ ω, (X ω i j) ^ 2 ∂μ) ≤ B ^ 2) :
    ∃ T : Finset I, S ⊆ T ∧ T.card ≤ S.card + S.card * t ∧
      ∀ j ∈ S, ∀ i ∉ T, ((t : ℝ) + 1) * (∫ ω, (X ω i j) ^ 2 ∂μ) ≤ B ^ 2 :=
  exists_selection (fun i j => ∫ ω, (X ω i j) ^ 2 ∂μ)
    (fun i j => integral_nonneg fun ω => sq_nonneg (X ω i j)) S B t hcol

end MI32.DeletionVarianceSelection
