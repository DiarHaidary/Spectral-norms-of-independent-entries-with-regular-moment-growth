import MI32.FiniteNet
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# From fixed-vector moments to thin-operator moments

The finite net is constructed internally with its dimension cost.
The input fixed-vector moment bound is an explicit intermediate hypothesis;
the separate strong--weak comparison must discharge it in the MI-32 proof.
This lemma is not advertised as a proof of that comparison or the main theorem.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace MI32

/-- A fixed-vector p-th moment bound gives the net cost `2^p * 5^dim`.
Integrability of the operator moment is proved by the constructed finite net.
The dimension is the input dimension, regardless of the output dimension. -/
theorem integral_opNorm_pow_le_of_images
    {Ω E F : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (μ : Measure Ω) (A : Ω → E →L[ℝ] F)
    (hA : Measurable (fun ω => ‖A ω‖)) (p : ℕ)
    (hint : ∀ x : E, ‖x‖ ≤ 1 → Integrable (fun ω => ‖A ω x‖ ^ p) μ)
    (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ x : E, ‖x‖ ≤ 1 → (∫ ω, ‖A ω x‖ ^ p ∂μ) ≤ B) :
    Integrable (fun ω => ‖A ω‖ ^ p) μ ∧
      (∫ ω, ‖A ω‖ ^ p ∂μ) ≤
        (2 : ℝ) ^ p * (5 : ℝ) ^ Module.finrank ℝ E * B := by
  classical
  obtain ⟨N, hN, hcard, hnorm, hcover⟩ := exists_half_net E
  have hcover' (x : E) (hx : ‖x‖ = 1) :
      ∃ y ∈ N, ‖x - y‖ ≤ (1 : ℝ) / 2 := by
    obtain ⟨y, hy, hxy⟩ := hcover x hx.le
    exact ⟨y, hy, hxy.le⟩
  have hpoint (ω : Ω) :
      ‖A ω‖ ^ p ≤ (2 : ℝ) ^ p * ∑ y ∈ N, ‖A ω y‖ ^ p :=
    opNorm_pow_le_net_sum N hN hcover' (A ω) p
  have hsum : Integrable (fun ω => ∑ y ∈ N, ‖A ω y‖ ^ p) μ :=
    integrable_finsetSum _ (fun y hy => hint y (hnorm y hy))
  have hnormint : Integrable (fun ω => ‖A ω‖ ^ p) μ :=
    (hsum.const_mul ((2 : ℝ) ^ p)).mono' (hA.pow_const p).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg _) p)]
        exact hpoint ω)
  refine ⟨hnormint, ?_⟩
  calc
    (∫ ω, ‖A ω‖ ^ p ∂μ) ≤
        ∫ ω, (2 : ℝ) ^ p * ∑ y ∈ N, ‖A ω y‖ ^ p ∂μ :=
      integral_mono hnormint (hsum.const_mul _) hpoint
    _ = (2 : ℝ) ^ p * ∑ y ∈ N, ∫ ω, ‖A ω y‖ ^ p ∂μ := by
      rw [integral_const_mul, integral_finsetSum N (fun y hy => hint y (hnorm y hy))]
    _ ≤ (2 : ℝ) ^ p * ∑ _y ∈ N, B :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum (fun y hy => hbound y (hnorm y hy))) (by positivity)
    _ = (2 : ℝ) ^ p * N.card * B := by simp [mul_assoc]
    _ ≤ (2 : ℝ) ^ p * (5 : ℝ) ^ Module.finrank ℝ E * B := by
      apply mul_le_mul_of_nonneg_right _ hB
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact_mod_cast hcard

end MI32
