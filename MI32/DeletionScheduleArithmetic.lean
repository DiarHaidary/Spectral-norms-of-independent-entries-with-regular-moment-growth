import MI32.Statement
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Exact budgets and logarithmic orders for nested deletion

The budget is `2^(5^k)-1`. Two-sided selection with threshold parameter
`b^3`, preserving at most `b` marked indices, then adding a minimizer of
budget `b`, fits inside the next budget. Logarithmic orders grow by five,
including the initial order log 2. These are arithmetic facts, not matrix estimates.
-/

noncomputable section

namespace MI32.DeletionScheduleArithmetic

def size (k : ℕ) : ℕ := 2 ^ (5 ^ k)
def budget (k : ℕ) : ℕ := size k - 1
def order (k : ℕ) : ℝ := Real.log (budget k + 1 : ℕ)

theorem size_pos (k : ℕ) : 0 < size k := by
  unfold size
  positivity

theorem size_ge_two (k : ℕ) : 2 ≤ size k := by
  have h : 1 ≤ 5 ^ k := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega))
  simpa only [size, pow_one] using Nat.pow_le_pow_right (by omega : 1 ≤ 2) h

theorem budget_add_one (k : ℕ) : budget k + 1 = size k :=
  Nat.sub_add_cancel (size_pos k)

@[simp] theorem budget_zero : budget 0 = 1 := by norm_num [budget, size]

theorem budget_pos (k : ℕ) : 1 ≤ budget k := by
  have h := size_ge_two k
  unfold budget
  omega

theorem size_succ (k : ℕ) : size (k + 1) = size k ^ 5 := by
  simp only [size, pow_succ, pow_mul]

/-- Exact expansion of the next budget. -/
theorem budget_succ (k : ℕ) : budget (k + 1) = budget k ^ 5 +
    5 * budget k ^ 4 + 10 * budget k ^ 3 + 10 * budget k ^ 2 + 5 * budget k := by
  have hs := size_succ k
  have h0 := budget_add_one k
  have h1 := budget_add_one (k + 1)
  apply Nat.add_right_cancel (m := 1)
  calc
    budget (k + 1) + 1 = (budget k + 1) ^ 5 := by rw [h1, hs, h0]
    _ = _ := by ring

theorem step_card_le (k a : ℕ) (ha : a ≤ budget k) :
    2 * (a + a * budget k ^ 3) + budget k ≤ budget (k + 1) := by
  rw [budget_succ]
  have hm := Nat.mul_le_mul_right (budget k ^ 3) ha
  calc
    _ ≤ 2 * (budget k + budget k * budget k ^ 3) + budget k :=
      Nat.add_le_add_right (Nat.mul_le_mul_left 2 (Nat.add_le_add ha hm)) _
    _ = 2 * budget k ^ 4 + 3 * budget k := by ring
    _ ≤ _ := by omega

theorem budget_strictMono : StrictMono budget := by
  apply strictMono_nat_of_lt_succ
  intro k
  rw [budget_succ]
  have h := budget_pos k
  omega

theorem budget_ge_two_pow (k : ℕ) : 2 ^ k ≤ budget k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [budget_succ, pow_succ]
    omega

theorem finite_terminal_bound (n : ℕ) : n ≤ budget n := by
  have hsmall : n + 1 ≤ 2 ^ n := Nat.lt_two_pow_self
  have hbase : 2 ^ n ≤ 5 ^ n := Nat.pow_le_pow_left (by omega : 2 ≤ 5) n
  have hexp : 2 ^ n ≤ 2 ^ (5 ^ n) :=
    Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega : n ≤ 5 ^ n)
  have hb := budget_add_one n
  change budget n + 1 = 2 ^ (5 ^ n) at hb
  omega

theorem order_eq (k : ℕ) : order k = (5 : ℝ) ^ k * Real.log 2 := by
  rw [order, budget_add_one]
  simp only [size, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]

@[simp] theorem order_zero : order 0 = Real.log 2 := by simp [order_eq]

theorem order_pos (k : ℕ) : 0 < order k := by
  rw [order_eq]
  exact mul_pos (by positivity) (Real.log_pos (by norm_num))

theorem log_two_le_order (k : ℕ) : Real.log 2 ≤ order k := by
  rw [order_eq]
  have hp : (1 : ℝ) ≤ (5 : ℝ) ^ k := one_le_pow₀ (by norm_num)
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hp (Real.log_pos (by norm_num)).le

theorem order_succ (k : ℕ) : order (k + 1) = 5 * order k := by
  simp only [order_eq, pow_succ]
  ring

theorem order_add (k r : ℕ) : order (k + r) = (5 : ℝ) ^ r * order k := by
  simp only [order_eq, pow_add]
  ring

end MI32.DeletionScheduleArithmetic
