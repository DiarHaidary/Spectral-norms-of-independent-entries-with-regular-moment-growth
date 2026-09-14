import MI32.Statement
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace MI32

theorem moment_zero {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {p : ℝ} (hp : 0 < p) : moment μ p (fun _ => 0) = 0 := by
  simp [moment, Real.zero_rpow (ne_of_gt hp),
    Real.zero_rpow (inv_ne_zero (ne_of_gt hp))]

theorem deletedBilinear_univ {Ω : Type*} {n : ℕ}
    (X : Ω → Matrix (Fin n) (Fin n) ℝ)
    (s t : EuclideanSpace ℝ (Fin n)) (ω : Ω) :
    deletedBilinear X Finset.univ s t ω = 0 := by
  simp [deletedBilinear]

/-- Deleting every original index annihilates the weak moment, including
subunit positive exponents. No replacement of the exponent by one is used. -/
theorem weakMoment_univ {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (X : Ω → Matrix (Fin n) (Fin n) ℝ)
    {p : ℝ} (hp : 0 < p) : weakMoment μ X Finset.univ p = 0 := by
  have hset : {v : ℝ | ∃ s t : EuclideanSpace ℝ (Fin n),
      ‖s‖ ≤ 1 ∧ ‖t‖ ≤ 1 ∧ v = moment μ p (deletedBilinear X Finset.univ s t)} =
      {0} := by
    ext v
    constructor
    · rintro ⟨s, t, _, _, hv⟩
      simpa only [Set.mem_singleton_iff, funext (deletedBilinear_univ X s t),
        moment_zero μ hp] using hv
    · intro hv
      have hv0 : v = 0 := Set.mem_singleton_iff.mp hv
      subst v
      refine ⟨0, 0, by simp, by simp, ?_⟩
      simp only [funext (deletedBilinear_univ X 0 0), moment_zero μ hp]
  simp only [weakMoment, hset, csSup_singleton]

open scoped Matrix.Norms.L2Operator in
/-- Check that the public statement uses Mathlib's Euclidean operator norm. -/
theorem spectralNorm_eq_l2_operator {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    spectralNorm A = ‖A‖ := rfl

/-- The first deletion exponent is strictly between zero and one. -/
theorem first_deletion_exponent : 0 < Real.log 2 ∧ Real.log 2 < 1 := by
  constructor
  · exact Real.log_pos (by norm_num)
  · have h := Real.log_lt_sub_one_of_pos (x := (2 : ℝ)) (by norm_num) (by norm_num)
    linarith

end MI32
