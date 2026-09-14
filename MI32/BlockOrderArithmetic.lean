import MI32.DeletionScheduleArithmetic
import Mathlib.Tactic

/-!
# Arithmetic of the per-block moment order

The moment order used on a scheduled block is chosen from the scheduled
budget, not from the actual block dimension, so it keeps growing even for
tiny blocks. This module records the purely numeric facts about that order:
it is at least one, it is dominated by `2 ^ 10` times the logarithmic order
two steps earlier, it grows at least linearly in the block index, and the
doubled-dimension factor of the bipartite lift is absolute at this order.
No probability and no matrices appear here.
-/

noncomputable section
open scoped BigOperators

namespace MI32.BlockOrderArithmetic

open DeletionScheduleArithmetic

/-- The block moment order is chosen from the scheduled budget, not from the
actual block dimension, so that it grows even for tiny blocks. -/
def blockOrder (a : ℕ) : ℕ := ⌈2 * order (a + 1)⌉₊

/-- The natural logarithm of two exceeds one half. -/
theorem half_lt_log_two : (1 / 2 : ℝ) < Real.log 2 := by
  have h := Real.log_lt_sub_one_of_pos (show (0 : ℝ) < 1 / 2 by norm_num) (by norm_num)
  rw [one_div, Real.log_inv] at h
  linarith

/-- The natural logarithm of two is below one. -/
theorem log_two_lt_one : Real.log 2 < 1 := by
  have h := Real.log_lt_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num) (by norm_num)
  linarith

/-- The block order dominates twice the scheduled logarithmic order. -/
theorem two_order_le_blockOrder (a : ℕ) : 2 * order (a + 1) ≤ (blockOrder a : ℝ) :=
  Nat.le_ceil _

/-- The block order is below twice the scheduled logarithmic order plus one. -/
theorem blockOrder_lt (a : ℕ) : (blockOrder a : ℝ) < 2 * order (a + 1) + 1 :=
  Nat.ceil_lt_add_one (by have := order_pos (a + 1); linarith)

/-- The block order is at least one. -/
theorem one_le_blockOrder (a : ℕ) : 1 ≤ blockOrder a := by
  apply Nat.one_le_ceil_iff.mpr
  have := order_pos (a + 1)
  linarith

/-- Natural-subtraction power comparison: `5 ^ (a + 1) ≤ 125 * 5 ^ (a - 2)` for `1 ≤ a`. -/
theorem pow_succ_le_pow_sub_two (a : ℕ) (ha : 1 ≤ a) : 5 ^ (a + 1) ≤ 125 * 5 ^ (a - 2) := by
  rcases a with _ | _ | a
  · omega
  · norm_num
  · have : a + 1 + 1 - 2 = a := by omega
    rw [this, show a + 1 + 1 + 1 = a + 3 by omega, pow_add, mul_comm]
    norm_num

/-- Two times the block order is below the available logarithmic order times
2 ^ 10, so ten scalar doublings suffice. -/
theorem two_blockOrder_le (a : ℕ) (ha : 1 ≤ a) :
    2 * (blockOrder a : ℝ) ≤ 2 ^ 10 * order (a - 2) := by
  have hlt := blockOrder_lt a
  have hlog := half_lt_log_two
  have hl2 := log_two_le_order (a - 2)
  have hpos := order_pos (a - 2)
  have hpow : ((5 : ℝ) ^ (a + 1)) ≤ 125 * (5 : ℝ) ^ (a - 2) := by
    exact_mod_cast pow_succ_le_pow_sub_two a ha
  have h4 : 4 * order (a + 1) ≤ 500 * order (a - 2) := by
    rw [order_eq, order_eq]
    have hl : (0 : ℝ) ≤ Real.log 2 := by linarith
    nlinarith
  linarith

/-- Linear growth of the power: `a + 2 ≤ 5 ^ (a + 1)`. -/
theorem index_add_two_le_pow (a : ℕ) : a + 2 ≤ 5 ^ (a + 1) := by
  induction a with
  | zero => norm_num
  | succ a ih =>
    rw [pow_succ]
    omega

/-- The orders grow fast enough for the geometric block-maximum assembly. -/
theorem index_add_two_le_two_blockOrder (a : ℕ) : a + 2 ≤ 2 * blockOrder a := by
  have hle := two_order_le_blockOrder a
  have hlog := half_lt_log_two
  have hpow : ((a : ℝ) + 2) ≤ (5 : ℝ) ^ (a + 1) := by
    exact_mod_cast index_add_two_le_pow a
  have hp : (0 : ℝ) ≤ (5 : ℝ) ^ (a + 1) := by positivity
  have h1 : ((a : ℝ) + 2) ≤ (blockOrder a : ℝ) := by
    rw [order_eq] at hle
    nlinarith
  have h2 : (a : ℝ) + 2 ≤ 2 * (blockOrder a : ℝ) := by
    have : (0 : ℝ) ≤ (blockOrder a : ℝ) := by positivity
    linarith
  exact_mod_cast h2

/-- The doubled dimension factor of the bipartite lift is absolute at this
order, including an empty block. -/
theorem dimension_factor_le_exp (a d : ℕ) (hd : d ≤ budget (a + 1)) :
    ((d + d : ℕ) : ℝ) ^ (1 / (2 * (blockOrder a : ℝ))) ≤ Real.exp 1 := by
  have hqpos : (0 : ℝ) < (blockOrder a : ℝ) := by
    exact_mod_cast (show 0 < blockOrder a from one_le_blockOrder a)
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · subst hd0
    simp only [Nat.add_zero, Nat.cast_zero]
    rw [Real.zero_rpow (by positivity)]
    exact (Real.exp_pos 1).le
  have hnpos : (0 : ℝ) < ((d + d : ℕ) : ℝ) := by
    have : (0 : ℝ) < d := by exact_mod_cast hdpos
    push_cast; linarith
  have hdR : (d : ℝ) ≤ (budget (a + 1) : ℝ) := by exact_mod_cast hd
  have hlog : Real.log ((d + d : ℕ) : ℝ) ≤ 2 * order (a + 1) := by
    have h := Real.log_le_log hnpos
      (show ((d + d : ℕ) : ℝ) ≤ ((budget (a + 1) + 1 : ℕ) : ℝ) ^ 2 by
        push_cast; nlinarith)
    unfold order
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  have hq := two_order_le_blockOrder a
  rw [Real.rpow_def_of_pos hnpos]
  apply Real.exp_le_exp.mpr
  have hdiv : Real.log ((d + d : ℕ) : ℝ) / (2 * (blockOrder a : ℝ)) ≤ 1 := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  simpa only [div_eq_mul_inv, one_div, one_mul] using hdiv

end MI32.BlockOrderArithmetic
