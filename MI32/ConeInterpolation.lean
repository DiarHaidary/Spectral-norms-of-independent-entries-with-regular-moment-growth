import MI32.MomentDoubling
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# Interpolation of the positive-cone fourth-moment estimate

The interpolation is applied to the norm of the original random polynomial
after inverse Walsh transformation, not to its parity-amplitude vector in a
different `L_r` space. The generic results below use actual scalar integrals
on arbitrary measure spaces; the probability-space applications require no
additional interpolation hypothesis.
-/

noncomputable section
open MeasureTheory

namespace MI32.ConeInterpolation

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Weighted Hölder for actual real nonnegative integrals, including zero
weights. The only finiteness hypotheses concern the two endpoint integrals. -/
theorem integral_mul_rpow_le (f g : Ω → ℝ)
    (hf : Measurable f) (hg : Measurable g)
    (hf0 : ∀ ω, 0 ≤ f ω) (hg0 : ∀ ω, 0 ≤ g ω)
    (hfi : Integrable f μ) (hgi : Integrable g μ)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    (∫ ω, f ω ^ a * g ω ^ b ∂μ) ≤
      (∫ ω, f ω ∂μ) ^ a * (∫ ω, g ω ∂μ) ^ b := by
  have hfl : (∫⁻ ω, ENNReal.ofReal (f ω) ∂μ) < ⊤ :=
    (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hf0)).mp hfi.hasFiniteIntegral
  have hgl : (∫⁻ ω, ENNReal.ofReal (g ω) ∂μ) < ⊤ :=
    (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hg0)).mp hgi.hasFiniteIntegral
  have hholder := ENNReal.lintegral_mul_norm_pow_le (μ := μ)
    hf.ennreal_ofReal.aemeasurable hg.ennreal_ofReal.aemeasurable ha hb hab
  have hfinite :
      (∫⁻ ω, ENNReal.ofReal (f ω) ∂μ) ^ a *
        (∫⁻ ω, ENNReal.ofReal (g ω) ∂μ) ^ b ≠ ⊤ :=
    ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_nonneg ha hfl.ne)
      (ENNReal.rpow_ne_top_of_nonneg hb hgl.ne)
  have hreal := ENNReal.toReal_mono hfinite hholder
  rw [integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun ω =>
        mul_nonneg (Real.rpow_nonneg (hf0 ω) _) (Real.rpow_nonneg (hg0 ω) _))
      (by fun_prop),
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hf0)
      hf.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hg0)
      hg.aestronglyMeasurable]
  simpa only [ENNReal.ofReal_mul (Real.rpow_nonneg (hf0 _) _),
    ENNReal.ofReal_rpow_of_nonneg (hf0 _) ha,
    ENNReal.ofReal_rpow_of_nonneg (hg0 _) hb,
    ENNReal.toReal_mul, ENNReal.toReal_rpow] using hreal

/-- Log-convexity of the unrooted moment between orders two and four,
proved directly by weighted Hölder. -/
theorem integral_rpow_interpolate_two_four (f : Ω → ℝ)
    (hf : Measurable f) (hf0 : ∀ ω, 0 ≤ f ω)
    (h2 : Integrable (fun ω => f ω ^ 2) μ)
    (h4 : Integrable (fun ω => f ω ^ 4) μ)
    (r : ℝ) (hr2 : 2 ≤ r) (hr4 : r ≤ 4) :
    (∫ ω, f ω ^ r ∂μ) ≤
      (∫ ω, f ω ^ 2 ∂μ) ^ ((4 - r) / 2) *
      (∫ ω, f ω ^ 4 ∂μ) ^ ((r - 2) / 2) := by
  have ha : 0 ≤ (4 - r) / 2 := by linarith
  have hb : 0 ≤ (r - 2) / 2 := by linarith
  have h := integral_mul_rpow_le (fun ω => f ω ^ 2) (fun ω => f ω ^ 4)
    (hf.pow_const 2) (hf.pow_const 4) (fun _ => sq_nonneg _)
    (fun ω => pow_nonneg (hf0 ω) _) h2 h4 ((4-r)/2) ((r-2)/2)
    ha hb (by ring_nf)
  have heq (ω : Ω) : (f ω ^ 2) ^ ((4-r)/2) * (f ω ^ 4) ^ ((r-2)/2) = f ω ^ r := by
    rw [← Real.rpow_natCast (f ω) 2, ← Real.rpow_natCast (f ω) 4,
      ← Real.rpow_mul (hf0 ω), ← Real.rpow_mul (hf0 ω),
      ← Real.rpow_add_of_nonneg (hf0 ω) (by positivity) (by positivity)]
    congr 1
    ring_nf
  simpa only [heq] using h

/-- Interpolate a fourth-power bound directly. In particular, the coefficient
`K` is the coefficient in the proved fourth-moment inequality, not a new
analytic assumption about intermediate moments. -/
theorem moment_le_of_fourth (f : Ω → ℝ)
    (hf : Measurable f) (hf0 : ∀ ω, 0 ≤ f ω)
    (h2 : Integrable (fun ω => f ω ^ 2) μ)
    (h4 : Integrable (fun ω => f ω ^ 4) μ)
    (K : ℝ) (hK : 0 ≤ K)
    (hfourth : (∫ ω, f ω ^ 4 ∂μ) ≤ K * (∫ ω, f ω ^ 2 ∂μ) ^ 2)
    (r : ℝ) (hr2 : 2 ≤ r) (hr4 : r ≤ 4) :
    moment μ r f ≤ K ^ ((r - 2) / (2 * r)) * moment μ 2 f := by
  let A : ℝ := ∫ ω, f ω ^ 2 ∂μ
  let B : ℝ := ∫ ω, f ω ^ 4 ∂μ
  let a : ℝ := (4 - r) / 2
  let b : ℝ := (r - 2) / 2
  have hA : 0 ≤ A := integral_nonneg fun _ => sq_nonneg _
  have hB : 0 ≤ B := integral_nonneg fun ω => pow_nonneg (hf0 ω) _
  have ha : 0 ≤ a := by dsimp [a]; linarith
  have hb : 0 ≤ b := by dsimp [b]; linarith
  have hr : 0 < r := by linarith
  have hraw : (∫ ω, f ω ^ r ∂μ) ≤ K ^ b * A ^ (r / 2) := by
    calc
      _ ≤ A ^ a * B ^ b := integral_rpow_interpolate_two_four f hf hf0 h2 h4 r hr2 hr4
      _ ≤ A ^ a * (K * A ^ 2) ^ b := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hB hfourth hb) (Real.rpow_nonneg hA _)
      _ = K ^ b * A ^ (r / 2) := by
        rw [Real.mul_rpow hK (sq_nonneg A), ← Real.rpow_natCast A 2,
          ← Real.rpow_mul hA]
        calc
          _ = K ^ b * (A ^ a * A ^ ((2 : ℝ) * b)) := by ring_nf
          _ = K ^ b * A ^ (r / 2) := by
            rw [← Real.rpow_add_of_nonneg hA ha (by positivity)]
            congr 2
            dsimp [a, b]
            ring_nf
  have hroot := Real.rpow_le_rpow
    (integral_nonneg fun ω => Real.rpow_nonneg (hf0 ω) r)
    hraw (one_div_nonneg.mpr hr.le)
  have hexp₁ : b * (1 / r) = (r - 2) / (2 * r) := by dsimp [b]; ring_nf
  have hexp₂ : (r / 2) * (1 / r) = 1 / 2 := by field_simp
  rw [Real.mul_rpow (Real.rpow_nonneg hK _) (Real.rpow_nonneg hA _),
    ← Real.rpow_mul hK, ← Real.rpow_mul hA, hexp₁, hexp₂] at hroot
  simpa only [moment, abs_of_nonneg (hf0 _), Real.rpow_two, A] using hroot

section Probability

variable [IsProbabilityMeasure μ]

/-- Fourth-moment integrability supplies every needed intermediate power. -/
theorem integrable_rpow_of_fourth (f : Ω → ℝ)
    (hf : Measurable f) (hf0 : ∀ ω, 0 ≤ f ω)
    (h4 : Integrable (fun ω => f ω ^ 4) μ)
    (r : ℝ) (hr0 : 0 ≤ r) (hr4 : r ≤ 4) :
    Integrable (fun ω => f ω ^ r) μ := by
  have h4' : Integrable (fun ω => ‖f ω‖ ^ (4 : ℝ)) μ := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hf0 _), Real.rpow_ofNat] using h4
  have h := integrable_norm_rpow_of_le hf.aestronglyMeasurable hr0
    (show (0 : ℝ) ≤ 4 by norm_num) hr4 h4'
  simpa only [Real.norm_eq_abs, abs_of_nonneg (hf0 _)] using h

/-- The intermediate `MemLp` hypothesis needed by subsequent Hölder steps
is a consequence of the fourth moment. -/
theorem memLp_of_fourth (f : Ω → ℝ)
    (hf : Measurable f) (hf0 : ∀ ω, 0 ≤ f ω)
    (h4 : Integrable (fun ω => f ω ^ 4) μ)
    (r : ℝ) (hr0 : 0 < r) (hr4 : r ≤ 4) :
    MemLp f (ENNReal.ofReal r) μ := by
  apply (integrable_norm_rpow_iff hf.aestronglyMeasurable
    (by simp [hr0]) ENNReal.ofReal_ne_top).mp
  simpa only [ENNReal.toReal_ofReal hr0.le, Real.norm_eq_abs,
    abs_of_nonneg (hf0 _)] using integrable_rpow_of_fourth f hf hf0 h4 r hr0.le hr4

/-- Equation (6), in the actual moment functional, from the proved fourth-power
inequality. Only fourth-moment integrability is required as an integrability input. -/
theorem moment_holder_order_le (f : Ω → ℝ)
    (hf : Measurable f) (hf0 : ∀ ω, 0 ≤ f ω)
    (h4 : Integrable (fun ω => f ω ^ 4) μ)
    (H : ℝ) (hH : 1 ≤ H) (d : ℕ)
    (hfourth : (∫ ω, f ω ^ 4 ∂μ) ≤ H ^ (4 * d) * (∫ ω, f ω ^ 2 ∂μ) ^ 2)
    (p : ℝ) (hp : 4 ≤ p) :
    moment μ (2 * p / (p - 2)) f ≤ H ^ (4 * (d : ℝ) / p) * moment μ 2 f := by
  have hp0 : 0 < p := by linarith
  have hp2 : 0 < p - 2 := by linarith
  have hr2 : (2 : ℝ) ≤ 2 * p / (p - 2) := by
    apply (le_div_iff₀ hp2).mpr
    linarith
  have hr4 : 2 * p / (p - 2) ≤ (4 : ℝ) := by
    apply (div_le_iff₀ hp2).mpr
    linarith
  have h2 : Integrable (fun ω => f ω ^ 2) μ := by
    simpa only [Real.rpow_two] using
      integrable_rpow_of_fourth f hf hf0 h4 2 (by norm_num) (by norm_num)
  have h := moment_le_of_fourth f hf hf0 h2 h4 (H ^ (4 * d))
    (pow_nonneg (le_trans zero_le_one hH) _) hfourth (2*p/(p-2)) hr2 hr4
  have he : ((2 * p / (p - 2) - 2) / (2 * (2 * p / (p - 2)))) = 1 / p := by
    field_simp
    ring_nf
  rw [he, ← Real.rpow_natCast H (4 * d),
    ← Real.rpow_mul (le_trans zero_le_one hH)] at h
  have he' : ((4 * d : ℕ) : ℝ) * (1 / p) = 4 * (d : ℝ) / p := by push_cast; ring_nf
  rwa [he'] at h

omit [IsProbabilityMeasure μ] in
/-- Rooted `L4 ≤ H^d L2` also entails the required fourth-power shape. -/
theorem fourth_power_bound_of_moment_bound (f : Ω → ℝ)
    (hf0 : ∀ ω, 0 ≤ f ω) (H : ℝ) (d : ℕ)
    (hfourth : moment μ 4 f ≤ H ^ d * moment μ 2 f) :
    (∫ ω, f ω ^ 4 ∂μ) ≤ H ^ (4 * d) * (∫ ω, f ω ^ 2 ∂μ) ^ 2 := by
  have hm4 : 0 ≤ moment μ 4 f := Real.rpow_nonneg
    (integral_nonneg fun ω => Real.rpow_nonneg (abs_nonneg _) _) _
  have h := pow_le_pow_left₀ hm4 hfourth 4
  have htwo : moment μ 2 f ^ 2 = ∫ ω, f ω ^ 2 ∂μ := by
    simpa only [Nat.cast_ofNat, abs_of_nonneg (hf0 _)] using moment_nat_pow μ f 2 (by norm_num)
  have hfour : moment μ 4 f ^ 4 = ∫ ω, f ω ^ 4 ∂μ := by
    simpa only [Nat.cast_ofNat, abs_of_nonneg (hf0 _)] using moment_nat_pow μ f 4 (by norm_num)
  rw [hfour, mul_pow, ← pow_mul, Nat.mul_comm d 4] at h
  have hp : moment μ 2 f ^ 4 = (moment μ 2 f ^ 2) ^ 2 := by ring_nf
  rwa [hp, htwo] at h

/-- Interpolation in the rooted form used in the analytic proof. -/
theorem moment_holder_order_le_of_moment_bound (f : Ω → ℝ)
    (hf : Measurable f) (hf0 : ∀ ω, 0 ≤ f ω)
    (h4 : Integrable (fun ω => f ω ^ 4) μ)
    (H : ℝ) (hH : 1 ≤ H) (d : ℕ)
    (hfourth : moment μ 4 f ≤ H ^ d * moment μ 2 f)
    (p : ℝ) (hp : 4 ≤ p) :
    moment μ (2 * p / (p - 2)) f ≤ H ^ (4 * (d : ℝ) / p) * moment μ 2 f :=
  moment_holder_order_le f hf hf0 h4 H hH d
    (fourth_power_bound_of_moment_bound f hf0 H d hfourth) p hp

/-- At horizon `q`, the cone interpolation factor is uniformly at most `H`.
The strict degree hypothesis is the actual prefix condition `d < q`. -/
theorem moment_four_q_le (f : Ω → ℝ)
    (hf : Measurable f) (hf0 : ∀ ω, 0 ≤ f ω)
    (h4 : Integrable (fun ω => f ω ^ 4) μ)
    (H : ℝ) (hH : 1 ≤ H) (d q : ℕ) (hq : 1 ≤ q) (hd : d < q)
    (hfourth : (∫ ω, f ω ^ 4 ∂μ) ≤ H ^ (4 * d) * (∫ ω, f ω ^ 2 ∂μ) ^ 2) :
    moment μ (2 * (4 * (q : ℝ)) / (4 * (q : ℝ) - 2)) f ≤ H * moment μ 2 f := by
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hp : (4 : ℝ) ≤ 4 * (q : ℝ) := by linarith
  have h := moment_holder_order_le f hf hf0 h4 H hH d (4 * (q : ℝ)) hp
    (hfourth := hfourth)
  have hd' : (d : ℝ) ≤ (q : ℝ) := by exact_mod_cast hd.le
  have he : 4 * (d : ℝ) / (4 * (q : ℝ)) ≤ 1 := by
    apply (div_le_iff₀ (by positivity : 0 < 4 * (q : ℝ))).mpr
    linarith
  have hfactor : H ^ (4 * (d : ℝ) / (4 * (q : ℝ))) ≤ H := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hH he
  exact h.trans (mul_le_mul_of_nonneg_right hfactor
    (Real.rpow_nonneg (integral_nonneg fun _ => Real.rpow_nonneg (abs_nonneg _) _) _))

end Probability

end MI32.ConeInterpolation

