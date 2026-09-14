import MI32.SymmetricLinearRegularity
import MI32.SymmetricConeInterpolation
import MI32.MomentTools
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# All positive real orders needed by the symmetric deletion reduction

The natural even-order comparison for a linear form in the original variables
is extended to every real order at least `log 2`. Orders below two are handled
by an actual Hölder interpolation with the half moment. No reverse moment
monotonicity or additional linear-form regularity hypothesis is assumed.
-/

noncomputable section
open MeasureTheory ProbabilityTheory

namespace MI32.SymmetricLinearAllOrders

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Hölder between orders one half and four, with integer powers after rooting. -/
theorem integral_two_pow_seven_le (S : Ω → ℝ) (hS : Measurable S)
    (hh : Integrable (fun ω => |S ω| ^ (1 / 2 : ℝ)) μ)
    (h4 : Integrable (fun ω => |S ω| ^ (4 : ℝ)) μ) :
    (∫ ω, |S ω| ^ (2 : ℝ) ∂μ) ^ 7 ≤
      (∫ ω, |S ω| ^ (1 / 2 : ℝ) ∂μ) ^ 4 *
        (∫ ω, |S ω| ^ (4 : ℝ) ∂μ) ^ 3 := by
  have h := ConeInterpolation.integral_mul_rpow_le
    (fun ω => |S ω| ^ (1 / 2 : ℝ)) (fun ω => |S ω| ^ (4 : ℝ))
    (by fun_prop) (by fun_prop)
    (fun ω => Real.rpow_nonneg (abs_nonneg _) _)
    (fun ω => Real.rpow_nonneg (abs_nonneg _) _) hh h4
    (4 / 7) (3 / 7) (by norm_num) (by norm_num) (by norm_num)
  have heq (ω : Ω) :
      (|S ω| ^ (1 / 2 : ℝ)) ^ (4 / 7 : ℝ) *
        (|S ω| ^ (4 : ℝ)) ^ (3 / 7 : ℝ) = |S ω| ^ (2 : ℝ) := by
    rw [← Real.rpow_mul (abs_nonneg _), ← Real.rpow_mul (abs_nonneg _),
      ← Real.rpow_add_of_nonneg (abs_nonneg _) (by norm_num) (by norm_num)]
    norm_num
  simp_rw [heq] at h
  have hp := pow_le_pow_left₀
    (integral_nonneg fun ω => Real.rpow_nonneg (abs_nonneg _) _) h 7
  rw [mul_pow] at hp
  have hhalf0 : 0 ≤ ∫ ω, |S ω| ^ (1 / 2 : ℝ) ∂μ :=
    integral_nonneg fun ω => Real.rpow_nonneg (abs_nonneg _) _
  have hfour0 : 0 ≤ ∫ ω, |S ω| ^ (4 : ℝ) ∂μ :=
    integral_nonneg fun ω => Real.rpow_nonneg (abs_nonneg _) _
  have hpow (x : ℝ) (hx : 0 ≤ x) (n : ℕ) :
      (x ^ ((n : ℝ) / 7)) ^ (7 : ℕ) = x ^ n := by
    calc
      _ = x ^ (((n : ℝ) / 7) * (7 : ℝ)) := by
        simpa only [Real.rpow_ofNat] using
          (Real.rpow_mul hx ((n : ℝ) / 7) (7 : ℝ)).symm
      _ = x ^ n := by rw [div_mul_cancel₀ _ (by norm_num), Real.rpow_natCast]
  have hpow4 := hpow _ hhalf0 4
  have hpow3 := hpow _ hfour0 3
  norm_num only [Nat.cast_ofNat] at hpow4 hpow3
  rwa [hpow4, hpow3] at hp

/-- A fourth-to-second comparison controls the second moment by the half
moment. The factor `β⁶` follows from Hölder and cancellation, including the
zero second-moment case. -/
theorem moment_two_le_half (S : Ω → ℝ) (hS : Measurable S)
    (hh : Integrable (fun ω => |S ω| ^ (1 / 2 : ℝ)) μ)
    (h4 : Integrable (fun ω => |S ω| ^ (4 : ℝ)) μ)
    (β : ℝ) (_hβ : 0 ≤ β)
    (hfour : moment μ 4 S ≤ β * moment μ 2 S) :
    moment μ 2 S ≤ β ^ 6 * moment μ (1 / 2) S := by
  let A := ∫ ω, |S ω| ^ (2 : ℝ) ∂μ
  let H := ∫ ω, |S ω| ^ (1 / 2 : ℝ) ∂μ
  let D := ∫ ω, |S ω| ^ (4 : ℝ) ∂μ
  have hA : 0 ≤ A := integral_nonneg fun ω => Real.rpow_nonneg (abs_nonneg _) _
  have hH : 0 ≤ H := integral_nonneg fun ω => Real.rpow_nonneg (abs_nonneg _) _
  have hD : 0 ≤ D := integral_nonneg fun ω => Real.rpow_nonneg (abs_nonneg _) _
  have hm2 : moment μ 2 S ^ 2 = A := by
    simpa only [A, Real.rpow_ofNat, Nat.cast_ofNat] using
      moment_nat_pow μ S 2 (by norm_num)
  have hm4 : moment μ 4 S ^ 4 = D := by
    simpa only [D, Real.rpow_ofNat, Nat.cast_ofNat] using
      moment_nat_pow μ S 4 (by norm_num)
  have hmhalf : moment μ (1 / 2) S = H ^ 2 := by
    norm_num [moment, H]
  have hDle : D ≤ β ^ 4 * A ^ 2 := by
    have h := pow_le_pow_left₀ (MomentTools.nonneg (μ := μ) 4 S) hfour 4
    rw [hm4, mul_pow, show moment μ 2 S ^ 4 = (moment μ 2 S ^ 2) ^ 2 by ring,
      hm2] at h
    exact h
  have hA7 : A ^ 7 ≤ H ^ 4 * D ^ 3 := integral_two_pow_seven_le S hS hh h4
  have hAle : A ≤ β ^ 12 * H ^ 4 := by
    by_cases hAz : A = 0
    · rw [hAz]
      positivity
    · have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hAz)
      have h := calc
        A ^ 6 * A = A ^ 7 := by ring
        _ ≤ H ^ 4 * D ^ 3 := hA7
        _ ≤ H ^ 4 * (β ^ 4 * A ^ 2) ^ 3 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hD hDle 3) (by positivity)
        _ = A ^ 6 * (β ^ 12 * H ^ 4) := by ring
      exact le_of_mul_le_mul_left h (pow_pos hApos 6)
  rw [hmhalf]
  have hright : 0 ≤ β ^ 6 * H ^ 2 := by positivity
  have hrightsq : (β ^ 6 * H ^ 2) ^ 2 = β ^ 12 * H ^ 4 := by ring
  nlinarith [MomentTools.nonneg (μ := μ) 2 S]

section Probability

variable [IsProbabilityMeasure μ]

/-- The proved even-order comparison extends to all real orders at least one
half. The small-order part uses Hölder; the large-order part rounds down to
an even order and uses the given comparison twice. -/
theorem real_doubling_of_even_doubling (S : Ω → ℝ) (hS : Measurable S)
    (hint : ∀ p : ℝ, 0 < p → Integrable (fun ω => |S ω| ^ p) μ)
    (β : ℝ) (hβ : 1 ≤ β)
    (heven : ∀ r : ℕ, 1 ≤ r →
      moment μ (4 * (r : ℝ)) S ≤ β * moment μ (2 * (r : ℝ)) S)
    (p : ℝ) (hp : 1 / 2 ≤ p) :
    moment μ (2 * p) S ≤ β ^ 7 * moment μ p S := by
  have hp0 : 0 < p := by linarith
  have hβ0 : 0 ≤ β := le_trans zero_le_one hβ
  have hmono (u v : ℝ) (hu : 0 < u) (huv : u ≤ v) :
      moment μ u S ≤ moment μ v S :=
    MomentTools.mono_exponent_of_integrable u v hu huv S hS.aestronglyMeasurable
      (hint v (hu.trans_le huv))
  by_cases hp2 : p ≤ 2
  · have hfour : moment μ 4 S ≤ β * moment μ 2 S := by
      simpa using heven 1 (by norm_num)
    have hhalf := moment_two_le_half S hS (hint (1 / 2) (by norm_num))
      (hint 4 (by norm_num)) β hβ0 hfour
    calc
      moment μ (2 * p) S ≤ moment μ 4 S := hmono _ _ (by positivity) (by linarith)
      _ ≤ β * moment μ 2 S := hfour
      _ ≤ β * (β ^ 6 * moment μ (1 / 2) S) := mul_le_mul_of_nonneg_left hhalf hβ0
      _ = β ^ 7 * moment μ (1 / 2) S := by ring
      _ ≤ β ^ 7 * moment μ p S := mul_le_mul_of_nonneg_left
        (hmono _ _ (by norm_num) hp) (by positivity)
  · let r : ℕ := ⌊p / 2⌋₊
    have hr : 1 ≤ r := (Nat.one_le_floor_iff _).mpr (by linarith)
    have hrR : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    have hrlower : 2 * (r : ℝ) ≤ p := by
      have h := Nat.floor_le (show 0 ≤ p / 2 by positivity)
      change (r : ℝ) ≤ p / 2 at h
      linarith
    have hrupper : p ≤ 4 * (r : ℝ) := by
      have h := Nat.lt_floor_add_one (p / 2)
      change p / 2 < (r : ℝ) + 1 at h
      linarith
    have h8 : moment μ (8 * (r : ℝ)) S ≤ β * moment μ (4 * (r : ℝ)) S := by
      convert heven (2 * r) (by omega) using 1 <;> push_cast <;> ring_nf
    calc
      moment μ (2 * p) S ≤ moment μ (8 * (r : ℝ)) S :=
        hmono _ _ (by positivity) (by linarith)
      _ ≤ β * moment μ (4 * (r : ℝ)) S := h8
      _ ≤ β * (β * moment μ (2 * (r : ℝ)) S) :=
        mul_le_mul_of_nonneg_left (heven r hr) hβ0
      _ = β ^ 2 * moment μ (2 * (r : ℝ)) S := by ring
      _ ≤ β ^ 2 * moment μ p S := mul_le_mul_of_nonneg_left
        (hmono _ _ (by linarith) hrlower) (sq_nonneg β)
      _ ≤ β ^ 7 * moment μ p S := mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ hβ (by norm_num)) (MomentTools.nonneg _ _)

/-- An explicit dimension-free doubling constant for original symmetric
linear forms. It is deliberately uniform down to order `log 2`. -/
def doublingConstant (α : ℝ) : ℝ := (Real.sqrt 3 * α ^ 2) ^ 7

theorem one_le_doublingConstant (α : ℝ) (hα : 1 ≤ α) :
    1 ≤ doublingConstant α := by
  exact one_le_pow₀ (SymmetricConeInterpolation.one_le_coneConstant α hα)

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- Uniform real-order doubling for a deterministic linear form in the same
original independent symmetric variables. Every analytic hypothesis concerns
the original coordinates; none concerns the desired linear-form estimate. -/
theorem linear_root_doubling
    (W : E → Ω → ℝ) (hW : ∀ e, Measurable (W e)) (hind : iIndepFun W μ)
    (hsym : ∀ e, IdentDistrib (W e) (fun ω => -W e ω) μ μ)
    (hint : ∀ e (p : ℝ), 0 < p → Integrable (fun ω => |W e ω| ^ p) μ)
    (α : ℝ) (hα : 1 ≤ α)
    (hregular : ∀ e (r : ℝ), 1 ≤ r →
      moment μ (2 * r) (W e) ≤ α * moment μ r (W e))
    (a : E → ℝ) (p : ℝ) (hp : Real.log 2 ≤ p) :
    moment μ (2 * p) (SymmetricLinearRegularity.linearForm W a) ≤
      doublingConstant α * moment μ p (SymmetricLinearRegularity.linearForm W a) := by
  have hlog : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at h ⊢
    linarith
  exact real_doubling_of_even_doubling _
    (SymmetricLinearRegularity.measurable_linearForm W hW a)
    (SymmetricLinearRegularity.integrable_abs_rpow_linearForm W hW hint a)
    _ (SymmetricConeInterpolation.one_le_coneConstant α hα)
    (SymmetricLinearRegularity.linear_even_root_doubling W hW hind hsym hint α hα hregular a)
    p (hlog.trans hp)

/-- The all-order comparison includes the actual finiteness of both moments. -/
theorem linear_integrable_and_root_doubling
    (W : E → Ω → ℝ) (hW : ∀ e, Measurable (W e)) (hind : iIndepFun W μ)
    (hsym : ∀ e, IdentDistrib (W e) (fun ω => -W e ω) μ μ)
    (hint : ∀ e (p : ℝ), 0 < p → Integrable (fun ω => |W e ω| ^ p) μ)
    (α : ℝ) (hα : 1 ≤ α)
    (hregular : ∀ e (r : ℝ), 1 ≤ r →
      moment μ (2 * r) (W e) ≤ α * moment μ r (W e))
    (a : E → ℝ) (p : ℝ) (hp : Real.log 2 ≤ p) :
    Integrable (fun ω => |SymmetricLinearRegularity.linearForm W a ω| ^ p) μ ∧
    Integrable (fun ω => |SymmetricLinearRegularity.linearForm W a ω| ^ (2 * p)) μ ∧
    moment μ (2 * p) (SymmetricLinearRegularity.linearForm W a) ≤
      doublingConstant α * moment μ p (SymmetricLinearRegularity.linearForm W a) := by
  have hp0 : 0 < p := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans_le hp
  exact ⟨SymmetricLinearRegularity.integrable_abs_rpow_linearForm W hW hint a p hp0,
    SymmetricLinearRegularity.integrable_abs_rpow_linearForm W hW hint a (2 * p) (by positivity),
    linear_root_doubling W hW hind hsym hint α hα hregular a p hp⟩

end Probability

end MI32.SymmetricLinearAllOrders
