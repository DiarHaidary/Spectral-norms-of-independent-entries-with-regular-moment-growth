import MI32.MomentTools
import MI32.CopySymmetrization
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Scalar independent-copy endpoints for the same deletion set

These comparisons use the literal original moment functional and the actual
product of the original probability law with itself. The range from log(2)
to one is handled by subadditivity of positive powers, separately from
Minkowski's inequality. Centering is compared with the independent-copy
difference by Jensen's inequality for every real order at least one.
-/

noncomputable section
open MeasureTheory

namespace MI32.DeletionMomentEndpoints

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Finiteness of one positive original moment gives finiteness of that
same moment of the actual independent-copy difference. -/
theorem integrable_copy_abs_rpow (S : Ω → ℝ) (hS : Measurable S)
    (p : ℝ) (hp : 0 < p) (hint : Integrable (fun ω => |S ω| ^ p) μ) :
    Integrable (fun z : Ω × Ω => |S z.1 - S z.2| ^ p) (μ.prod μ) := by
  have hmem := MomentTools.memLp_of_integrable_abs_rpow p hp S hS.aestronglyMeasurable hint
  exact MomentTools.integrable_abs_rpow_of_memLp p hp _
    ((hmem.comp_fst μ).sub (hmem.comp_snd μ))

theorem moment_copy_fst (S : Ω → ℝ) (p : ℝ)
    (hint : Integrable (fun ω => |S ω| ^ p) μ) :
    moment (μ.prod μ) p (fun z : Ω × Ω => S z.1) = moment μ p S := by
  unfold moment
  rw [integral_prod _ (hint.comp_fst μ)]
  simp [integral_const]

theorem moment_copy_snd (S : Ω → ℝ) (p : ℝ)
    (hint : Integrable (fun ω => |S ω| ^ p) μ) :
    moment (μ.prod μ) p (fun z : Ω × Ω => S z.2) = moment μ p S := by
  unfold moment
  rw [integral_prod _ (hint.comp_snd μ)]
  simp [integral_const]

/-- Minkowski's independent-copy upper comparison at all real orders at least one. -/
theorem copy_moment_le_two (S : Ω → ℝ) (hS : Measurable S)
    (p : ℝ) (hp : 1 ≤ p) (hint : Integrable (fun ω => |S ω| ^ p) μ) :
    moment (μ.prod μ) p (fun z : Ω × Ω => S z.1 - S z.2) ≤ 2 * moment μ p S := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hmem := MomentTools.memLp_of_integrable_abs_rpow p hp0 S hS.aestronglyMeasurable hint
  have hpEN : (1 : ENNReal) ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.mpr hp
  calc
    _ ≤ moment (μ.prod μ) p (fun z : Ω × Ω => S z.1) +
        moment (μ.prod μ) p (fun z : Ω × Ω => S z.2) := by
      change moment (μ.prod μ) p ((fun z : Ω × Ω => S z.1) - (fun z => S z.2)) ≤ _
      rw [MomentTools.eq_lpNorm p hp0 _
        ((hmem.comp_fst μ).sub (hmem.comp_snd μ)).aestronglyMeasurable,
        MomentTools.eq_lpNorm p hp0 _ (hmem.comp_fst μ).aestronglyMeasurable,
        MomentTools.eq_lpNorm p hp0 _ (hmem.comp_snd μ).aestronglyMeasurable]
      exact lpNorm_sub_le (hmem.comp_fst μ) hpEN
    _ = _ := by rw [moment_copy_fst S p hint, moment_copy_snd S p hint]; ring

/-- For orders at most one, subadditivity controls the actual power integral.
No triangle inequality for an Lp norm is used in this range. -/
theorem copy_integral_le_two_of_le_one (S : Ω → ℝ) (hS : Measurable S)
    (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (hint : Integrable (fun ω => |S ω| ^ p) μ) :
    (∫ z : Ω × Ω, |S z.1 - S z.2| ^ p ∂(μ.prod μ)) ≤
      2 * ∫ ω, |S ω| ^ p ∂μ := by
  calc
    _ ≤ ∫ z : Ω × Ω, (|S z.1| ^ p + |S z.2| ^ p) ∂(μ.prod μ) := by
      apply integral_mono (integrable_copy_abs_rpow S hS p hp hint)
        ((hint.comp_fst μ).add (hint.comp_snd μ))
      intro z
      have ha : |S z.1 - S z.2| ≤ |S z.1| + |S z.2| := by
        simpa only [Real.norm_eq_abs] using norm_sub_le (S z.1) (S z.2)
      exact (Real.rpow_le_rpow (abs_nonneg _) ha hp.le).trans
        (Real.rpow_add_le_add_rpow (abs_nonneg _) (abs_nonneg _) hp.le hp1)
    _ = _ := by
      rw [integral_add (hint.comp_fst μ) (hint.comp_snd μ),
        integral_prod _ (hint.comp_fst μ), integral_prod _ (hint.comp_snd μ)]
      simp [integral_const, two_mul]

/-- The rooted subunit comparison exposes its actual factor `2^(1/p)`. -/
theorem copy_moment_le_two_rpow_of_le_one (S : Ω → ℝ) (hS : Measurable S)
    (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (hint : Integrable (fun ω => |S ω| ^ p) μ) :
    moment (μ.prod μ) p (fun z : Ω × Ω => S z.1 - S z.2) ≤
      (2 : ℝ) ^ (1 / p) * moment μ p S := by
  have h := Real.rpow_le_rpow
    (integral_nonneg fun z : Ω × Ω => Real.rpow_nonneg (abs_nonneg (S z.1 - S z.2)) p)
    (copy_integral_le_two_of_le_one S hS p hp hp1 hint) (one_div_nonneg.mpr hp.le)
  simpa only [moment, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2)
    (integral_nonneg fun ω => Real.rpow_nonneg (abs_nonneg (S ω)) p)] using h

/-- For every real `p ≥ log(2)`, the original-copy difference has at most
`exp(1)` times the original moment. Only finiteness at the requested order
is needed, so all-positive-moment assumptions immediately supply the input. -/
theorem copy_moment_le_exp (S : Ω → ℝ) (hS : Measurable S)
    (p : ℝ) (hp : Real.log 2 ≤ p) (hint : Integrable (fun ω => |S ω| ^ p) μ) :
    Integrable (fun z : Ω × Ω => |S z.1 - S z.2| ^ p) (μ.prod μ) ∧
      moment (μ.prod μ) p (fun z : Ω × Ω => S z.1 - S z.2) ≤
        Real.exp 1 * moment μ p S := by
  have hp0 : 0 < p := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans_le hp
  refine ⟨integrable_copy_abs_rpow S hS p hp0 hint, ?_⟩
  by_cases hp1 : 1 ≤ p
  · apply (copy_moment_le_two S hS p hp1 hint).trans
    exact mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp 1])
      (MomentTools.nonneg p S)
  · apply (copy_moment_le_two_rpow_of_le_one S hS p hp0 (le_of_not_ge hp1) hint).trans
    apply mul_le_mul_of_nonneg_right _ (MomentTools.nonneg p S)
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    apply Real.exp_le_exp.mpr
    rw [mul_one_div]
    exact (div_le_iff₀ hp0).mpr (by simpa using hp)

/-- Jensen centering at an arbitrary real order at least one, with both
power integrability statements derived on the actual original/copy laws. -/
theorem centered_moment_le_copy (S : Ω → ℝ) (hS : Measurable S)
    (p : ℝ) (hp : 1 ≤ p) (hint : Integrable (fun ω => |S ω| ^ p) μ) :
    Integrable (fun ω => |S ω - ∫ η, S η ∂μ| ^ p) μ ∧
      Integrable (fun z : Ω × Ω => |S z.1 - S z.2| ^ p) (μ.prod μ) ∧
      moment μ p (fun ω => S ω - ∫ η, S η ∂μ) ≤
        moment (μ.prod μ) p (fun z : Ω × Ω => S z.1 - S z.2) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hpEN : (1 : ENNReal) ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.mpr hp
  have hmem := MomentTools.memLp_of_integrable_abs_rpow p hp0 S hS.aestronglyMeasurable hint
  have hS1 : Integrable S μ := hmem.integrable hpEN
  have hcent : Integrable (fun ω => |S ω - ∫ η, S η ∂μ| ^ p) μ :=
    MomentTools.integrable_abs_rpow_of_memLp p hp0 _ (hmem.sub (memLp_const _))
  have hcopy := integrable_copy_abs_rpow S hS p hp0 hint
  refine ⟨hcent, hcopy, ?_⟩
  have hpoint (ω : Ω) : |S ω - ∫ η, S η ∂μ| ^ p ≤
      ∫ η, |S ω - S η| ^ p ∂μ := by
    have hshift1 : Integrable (fun η => S ω - S η) μ := (integrable_const _).sub hS1
    have hshiftp : Integrable (fun η => |S ω - S η| ^ p) μ :=
      MomentTools.integrable_abs_rpow_of_memLp p hp0 _ ((memLp_const _).sub hmem)
    have hn : |S ω - ∫ η, S η ∂μ| ≤ ∫ η, |S ω - S η| ∂μ := by
      have h := norm_integral_le_integral_norm (f := fun η => S ω - S η) (μ := μ)
      simpa only [Real.norm_eq_abs, integral_sub (integrable_const _) hS1,
        integral_const, probReal_univ, one_smul] using h
    have hj := (convexOn_rpow hp).map_integral_le
      (μ := μ) (f := fun η => |S ω - S η|)
      (Real.continuous_rpow_const hp0.le).continuousOn isClosed_Ici
      (Filter.Eventually.of_forall fun η => abs_nonneg (S ω - S η)) hshift1.abs hshiftp
    exact (Real.rpow_le_rpow (abs_nonneg _) hn hp0.le).trans hj
  apply Real.rpow_le_rpow
    (integral_nonneg fun ω => Real.rpow_nonneg (abs_nonneg (S ω - ∫ η, S η ∂μ)) p)
    _ (one_div_nonneg.mpr hp0.le)
  calc
    _ ≤ ∫ ω, ∫ η, |S ω - S η| ^ p ∂μ ∂μ :=
      integral_mono hcent hcopy.integral_prod_left hpoint
    _ = _ := (integral_prod _ hcopy).symm

/-- For a mean-zero original variable, the same real-order Jensen bound
compares the original moment directly with the actual copied difference. -/
theorem mean_zero_moment_le_copy (S : Ω → ℝ) (hS : Measurable S)
    (hmean : ∫ ω, S ω ∂μ = 0) (p : ℝ) (hp : 1 ≤ p)
    (hint : Integrable (fun ω => |S ω| ^ p) μ) :
    moment μ p S ≤ moment (μ.prod μ) p (fun z : Ω × Ω => S z.1 - S z.2) := by
  simpa only [hmean, sub_zero] using (centered_moment_le_copy S hS p hp hint).2.2

end MI32.DeletionMomentEndpoints
