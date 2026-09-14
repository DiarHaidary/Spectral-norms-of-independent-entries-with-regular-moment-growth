import MI32.ThinNetMoment
import MI32.MomentTools
import MI32.MomentDoubling

/-!
# Rooted thin-operator moments with explicit dimension cost

The constructed half-net gives the factor `2 * 5^(dim / p)` from actual
fixed-vector rooted moments. Finiteness of the operator moment is derived
from the supplied fixed-vector integrability. No strong--weak comparison
is assumed beyond the displayed intermediate fixed-vector bound.
-/

noncomputable section
open MeasureTheory

namespace MI32.ThinMomentRoot

variable {Ω E F : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The exact root of the half-net cost at a positive natural moment order. -/
theorem net_factor_pow (d p : ℕ) (hp : 1 ≤ p) :
    ((2 : ℝ) * (5 : ℝ) ^ ((d : ℝ) / (p : ℝ))) ^ p =
      (2 : ℝ) ^ p * (5 : ℝ) ^ d := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_zero_of_lt hp
  rw [mul_pow]
  congr 1
  rw [← Real.rpow_natCast _ p, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 5),
    div_mul_cancel₀ _ hp0, Real.rpow_natCast]

/-- Rooted fixed-vector moments control the actual operator-norm moment
with the explicit factor `2 * 5^(dim E / p)`. The measure is arbitrary. -/
theorem opNorm_moment_le_of_images
    (μ : Measure Ω) (A : Ω → E →L[ℝ] F)
    (hA : Measurable (fun ω => ‖A ω‖)) (p : ℕ) (hp : 1 ≤ p)
    (hint : ∀ x : E, ‖x‖ ≤ 1 → Integrable (fun ω => ‖A ω x‖ ^ p) μ)
    (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ x : E, ‖x‖ ≤ 1 → moment μ (p : ℝ) (fun ω => ‖A ω x‖) ≤ M) :
    Integrable (fun ω => ‖A ω‖ ^ p) μ ∧
      moment μ (p : ℝ) (fun ω => ‖A ω‖) ≤
        (2 : ℝ) * (5 : ℝ) ^ ((Module.finrank ℝ E : ℝ) / (p : ℝ)) * M := by
  have hpN : 0 < p := by omega
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpN
  have hpow (x : E) (hx : ‖x‖ ≤ 1) : (∫ ω, ‖A ω x‖ ^ p ∂μ) ≤ M ^ p := by
    have h := pow_le_pow_left₀ (MomentTools.nonneg (μ := μ) (p : ℝ)
      (fun ω => ‖A ω x‖)) (hbound x hx) p
    simpa only [moment_nat_pow μ (fun ω => ‖A ω x‖) p hpN,
      abs_of_nonneg (norm_nonneg _)] using h
  obtain ⟨hopint, hopbound⟩ := integral_opNorm_pow_le_of_images μ A hA p hint
    (M ^ p) (pow_nonneg hM _) hpow
  refine ⟨hopint, ?_⟩
  have hfactor : 0 ≤ (2 : ℝ) * (5 : ℝ) ^ ((Module.finrank ℝ E : ℝ) / (p : ℝ)) :=
    mul_nonneg (by norm_num) (Real.rpow_nonneg (by norm_num) _)
  rw [← net_factor_pow (Module.finrank ℝ E) p hp] at hopbound
  have hroot := MomentTools.nat_root_le _ (M ^ p) _
    (integral_nonneg fun ω => pow_nonneg (norm_nonneg _) p)
    (pow_nonneg hM _) hfactor p hp hopbound
  rw [← Real.rpow_natCast M p, ← Real.rpow_mul hM,
    mul_one_div_cancel hpR.ne', Real.rpow_one] at hroot
  simpa only [moment, abs_of_nonneg (norm_nonneg _), Real.rpow_natCast] using hroot

/-- If the input dimension is at most `q`, the `4q` operator moment costs
at most the numerical factor `2 * 5^(1/4)` times the fixed-vector bound. -/
theorem opNorm_moment_four_mul_le_of_images
    (μ : Measure Ω) (A : Ω → E →L[ℝ] F)
    (hA : Measurable (fun ω => ‖A ω‖)) (q : ℕ) (hq : 1 ≤ q)
    (hdim : Module.finrank ℝ E ≤ q)
    (hint : ∀ x : E, ‖x‖ ≤ 1 → Integrable (fun ω => ‖A ω x‖ ^ (4 * q)) μ)
    (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ x : E, ‖x‖ ≤ 1 →
      moment μ (4 * (q : ℝ)) (fun ω => ‖A ω x‖) ≤ M) :
    Integrable (fun ω => ‖A ω‖ ^ (4 * q)) μ ∧
      moment μ (4 * (q : ℝ)) (fun ω => ‖A ω‖) ≤
        (2 : ℝ) * (5 : ℝ) ^ (1 / 4 : ℝ) * M := by
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hq
  have hdimR : (Module.finrank ℝ E : ℝ) ≤ (q : ℝ) := by exact_mod_cast hdim
  obtain ⟨hopint, hopbound⟩ := opNorm_moment_le_of_images μ A hA (4 * q) (by omega)
    hint M hM (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hbound)
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hopbound
  refine ⟨hopint, hopbound.trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ hM
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 5)
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * (q : ℝ))).mpr
  linarith

end MI32.ThinMomentRoot
