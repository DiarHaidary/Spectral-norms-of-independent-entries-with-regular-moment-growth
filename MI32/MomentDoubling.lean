import MI32.Statement
import Mathlib.Tactic

noncomputable section
open MeasureTheory

namespace MI32

/-- Recover the actual integer moment from its positive-order root. -/
theorem moment_nat_pow {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z : Ω → ℝ) (r : ℕ) (hr : 0 < r) :
    moment μ (r : ℝ) Z ^ r = ∫ ω, |Z ω| ^ r ∂μ := by
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hr)
  have hn : 0 ≤ ∫ ω, |Z ω| ^ (r : ℝ) ∂μ :=
    integral_nonneg (fun _ => Real.rpow_nonneg (abs_nonneg _) _)
  rw [moment, ← Real.rpow_natCast, ← Real.rpow_mul hn,
    one_div_mul_cancel hr0, Real.rpow_one]
  simp only [Real.rpow_natCast]

/-- The source's L_r doubling entails the unrooted integer-moment inequality
used in the scalar Cauchy--Schwarz step. -/
theorem integral_pow_doubling {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z : Ω → ℝ) (α : ℝ)
    (hregular : ∀ r : ℝ, 1 ≤ r → moment μ (2 * r) Z ≤ α * moment μ r Z)
    (r : ℕ) (hr : 1 ≤ r) :
    (∫ ω, |Z ω| ^ (2 * r) ∂μ) ≤
      α ^ (2 * r) * (∫ ω, |Z ω| ^ r ∂μ) ^ 2 := by
  have hrpos : 0 < r := by omega
  have hd : moment μ ((2 * r : ℕ) : ℝ) Z ≤ α * moment μ (r : ℝ) Z := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      hregular (r : ℝ) (by exact_mod_cast hr)
  have hn : 0 ≤ moment μ ((2 * r : ℕ) : ℝ) Z :=
    Real.rpow_nonneg (integral_nonneg (fun _ => Real.rpow_nonneg (abs_nonneg _) _)) _
  calc
    _ = moment μ ((2 * r : ℕ) : ℝ) Z ^ (2 * r) :=
      (moment_nat_pow μ Z (2 * r) (by omega)).symm
    _ ≤ (α * moment μ (r : ℝ) Z) ^ (2 * r) := pow_le_pow_left₀ hn hd _
    _ = α ^ (2 * r) * (∫ ω, |Z ω| ^ r ∂μ) ^ 2 := by
      rw [mul_pow]
      congr 1
      rw [Nat.mul_comm 2 r, pow_mul, moment_nat_pow μ Z r hrpos]

end MI32
