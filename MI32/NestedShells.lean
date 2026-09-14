import Mathlib.Data.Nat.Find
import Mathlib.Tactic

/-!
# First shells and exact entry masks on the original axes

Every original index receives its first membership level in a deterministic
nested family which covers all indices at the prescribed finite horizon.
The initial set may be nonempty. The four entry masks form an exact
partition: even adjacent blocks, odd off-diagonal adjacent blocks, and
the two far orientations. No probabilistic law or relabeling is used.
-/

noncomputable section
open scoped BigOperators

namespace MI32.NestedShells

attribute [local instance] Classical.propDecidable

variable {I : Type*} [Fintype I]

private theorem exists_membership (S : ℕ → Finset I) (N : ℕ)
    (hcover : S N = Finset.univ) (i : I) : ∃ r, i ∈ S r :=
  ⟨N, by rw [hcover]; exact Finset.mem_univ i⟩

/-- The first shell level of an original index, bounded by the given horizon. -/
def level (S : ℕ → Finset I) (N : ℕ) (hcover : S N = Finset.univ) (i : I) : Fin (N + 1) :=
  ⟨Nat.find (exists_membership S N hcover i),
    Nat.lt_succ_of_le (Nat.find_min' (exists_membership S N hcover i)
      (show i ∈ S N by rw [hcover]; exact Finset.mem_univ i))⟩

/-- The first level actually contains the original index. -/
theorem mem_level (S : ℕ → Finset I) (N : ℕ) (hcover : S N = Finset.univ) (i : I) :
    i ∈ S (level S N hcover i).val :=
  Nat.find_spec (exists_membership S N hcover i)

theorem level_le_of_mem (S : ℕ → Finset I) (N : ℕ) (hcover : S N = Finset.univ)
    (i : I) (r : ℕ) (hi : i ∈ S r) : (level S N hcover i).val ≤ r :=
  Nat.find_min' (exists_membership S N hcover i) hi

/-- Cumulative first-shell membership is exactly the original nested set.
The equivalence remains true after the horizon by monotonicity. -/
theorem level_le_iff (S : ℕ → Finset I) (hmono : Monotone S)
    (N : ℕ) (hcover : S N = Finset.univ) (i : I) (r : ℕ) :
    (level S N hcover i).val ≤ r ↔ i ∈ S r :=
  ⟨fun h => hmono h (mem_level S N hcover i), level_le_of_mem S N hcover i r⟩

/-- Exact cumulative level set, retaining the original coordinates. -/
theorem cumulative_eq (S : ℕ → Finset I) (hmono : Monotone S)
    (N : ℕ) (hcover : S N = Finset.univ) (r : ℕ) :
    Finset.univ.filter (fun i => (level S N hcover i).val ≤ r) = S r := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, level_le_iff S hmono N hcover]

theorem cumulative_card_eq (S : ℕ → Finset I) (hmono : Monotone S)
    (N : ℕ) (hcover : S N = Finset.univ) (r : ℕ) :
    (Finset.univ.filter (fun i => (level S N hcover i).val ≤ r)).card = (S r).card := by
  rw [cumulative_eq S hmono N hcover]

/-- One exact first shell; levels above the horizon give the empty set. -/
def shell (S : ℕ → Finset I) (N : ℕ) (hcover : S N = Finset.univ) (r : ℕ) : Finset I :=
  Finset.univ.filter (fun i => (level S N hcover i).val = r)

theorem shell_zero (S : ℕ → Finset I) (hmono : Monotone S)
    (N : ℕ) (hcover : S N = Finset.univ) : shell S N hcover 0 = S 0 := by
  ext i
  simp only [shell, Finset.mem_filter, Finset.mem_univ, true_and,
    ← Nat.le_zero, level_le_iff S hmono N hcover]

/-- Later shells are the exact successive set differences. -/
theorem shell_succ (S : ℕ → Finset I) (hmono : Monotone S)
    (N : ℕ) (hcover : S N = Finset.univ) (r : ℕ) :
    shell S N hcover (r + 1) = S (r + 1) \ S r := by
  ext i
  simp only [shell, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff,
    ← level_le_iff S hmono N hcover]
  omega

theorem shell_disjoint (S : ℕ → Finset I) (N : ℕ) (hcover : S N = Finset.univ)
    (r s : ℕ) (hrs : r ≠ s) : Disjoint (shell S N hcover r) (shell S N hcover s) := by
  apply Finset.disjoint_left.mpr
  intro i hir his
  simp only [shell, Finset.mem_filter, Finset.mem_univ, true_and] at hir his
  exact hrs (hir.symm.trans his)

/-- Every original index lies in exactly its own bounded first shell. -/
theorem mem_own_shell (S : ℕ → Finset I) (N : ℕ) (hcover : S N = Finset.univ) (i : I) :
    i ∈ shell S N hcover (level S N hcover i).val := by simp [shell]

theorem exists_unique_shell (S : ℕ → Finset I) (N : ℕ)
    (hcover : S N = Finset.univ) (i : I) :
    ∃! r : Fin (N + 1), i ∈ shell S N hcover r.val := by
  refine ⟨level S N hcover i, mem_own_shell S N hcover i, ?_⟩
  intro r hr
  simp only [shell, Finset.mem_filter, Finset.mem_univ, true_and] at hr
  exact Fin.ext hr.symm

section EntryMasks

variable {A : Type*}

/-- The lower far orientation has a row at least two shells later than its column. -/
def farLower (label : A → ℕ) (X : A → A → ℝ) (i j : A) : ℝ :=
  if label j + 1 < label i then X i j else 0

/-- The upper far orientation, with the original row and column reversed. -/
def farUpper (label : A → ℕ) (X : A → A → ℝ) (i j : A) : ℝ :=
  if label i + 1 < label j then X i j else 0

/-- Full diagonal blocks on shell pairs (0,1), (2,3), and so on. -/
def nearEven (label : A → ℕ) (X : A → A → ℝ) (i j : A) : ℝ :=
  if label i / 2 = label j / 2 then X i j else 0

/-- Only the off-diagonal rectangles on shell pairs (1,2), (3,4), and so on. -/
def nearOdd (label : A → ℕ) (X : A → A → ℝ) (i j : A) : ℝ :=
  if (label i + 1) / 2 = (label j + 1) / 2 ∧ label i ≠ label j then X i j else 0

/-- The two alternating adjacent-block conditions are exactly shell distance at most one. -/
theorem near_iff (a b : ℕ) :
    (a / 2 = b / 2 ∨ ((a + 1) / 2 = (b + 1) / 2 ∧ a ≠ b)) ↔
      a ≤ b + 1 ∧ b ≤ a + 1 := by omega

theorem near_masks_disjoint (a b : ℕ) :
    ¬ (a / 2 = b / 2 ∧ (a + 1) / 2 = (b + 1) / 2 ∧ a ≠ b) := by omega

/-- Exact pointwise entry partition, including initial and terminal shells. -/
theorem entry_partition (label : A → ℕ) (X : A → A → ℝ) (i j : A) :
    X i j = nearEven label X i j + nearOdd label X i j +
      farLower label X i j + farUpper label X i j := by
  unfold nearEven nearOdd farLower farUpper
  split_ifs <;> (first | omega | ring)

theorem farUpper_eq_transpose_farLower (label : A → ℕ) (X : A → A → ℝ) (i j : A) :
    farUpper label X i j = farLower label (fun i j => X j i) j i := rfl

theorem farLower_nonzero (label : A → ℕ) (X : A → A → ℝ) (i j : A)
    (h : farLower label X i j ≠ 0) : label j + 1 < label i ∧ X i j ≠ 0 := by
  by_cases hij : label j + 1 < label i
  · exact ⟨hij, by simpa only [farLower, if_pos hij] using h⟩
  · simp only [farLower, if_neg hij, ne_eq, not_true_eq_false] at h

end EntryMasks

/-- A supported lower-far original entry lies outside the next selected set
of its column's first level. No extra horizon assumption is necessary. -/
theorem farLower_nonzero_outside (S : ℕ → Finset I) (hmono : Monotone S)
    (N : ℕ) (hcover : S N = Finset.univ) (X : I → I → ℝ) (i k : I)
    (h : farLower (fun j => (level S N hcover j).val) X i k ≠ 0) :
    i ∉ S ((level S N hcover k).val + 1) := by
  intro hi
  have hle := (level_le_iff S hmono N hcover i _).mpr hi
  have hlt := (farLower_nonzero _ X i k h).1
  omega

/-- Earlier labeled original columns already lie in the later column's marked set. -/
theorem mem_of_level_le (S : ℕ → Finset I) (hmono : Monotone S)
    (N : ℕ) (hcover : S N = Finset.univ) (j k : I)
    (hjk : level S N hcover j ≤ level S N hcover k) :
    j ∈ S (level S N hcover k).val :=
  (level_le_iff S hmono N hcover j _).mp hjk

/-- Both ingredients needed by the same-set marked-column variance selection. -/
theorem farLower_common_support (S : ℕ → Finset I) (hmono : Monotone S)
    (N : ℕ) (hcover : S N = Finset.univ) (X : I → I → ℝ) (i j k : I)
    (hjk : level S N hcover j ≤ level S N hcover k)
    (hik : farLower (fun a => (level S N hcover a).val) X i k ≠ 0) :
    j ∈ S (level S N hcover k).val ∧ i ∉ S ((level S N hcover k).val + 1) :=
  ⟨mem_of_level_le S hmono N hcover j k hjk,
    farLower_nonzero_outside S hmono N hcover X i k hik⟩

end MI32.NestedShells
