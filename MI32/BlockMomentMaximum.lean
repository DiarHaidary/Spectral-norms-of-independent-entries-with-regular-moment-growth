import MI32.MomentTools
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Assembling block means from increasing moments

A finite family of nonnegative block norms with moment orders at least
`i + 2` has mean maximum at most three times the common rooted moment
bound. No independence between blocks is needed. The block estimates are
explicit intermediate hypotheses to be discharged by the local theorem.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace MI32.BlockMomentMaximum

theorem scalar_le_threshold_add_power (z t : ℝ) (hz : 0 ≤ z) (ht : 0 < t)
    (p : ℕ) (hp : 1 ≤ p) : z ≤ t + z ^ p / t ^ (p - 1) := by
  by_cases hzt : z ≤ t
  · exact hzt.trans (le_add_of_nonneg_right (div_nonneg (pow_nonneg hz _) (pow_nonneg ht.le _)))
  · have htz : t ≤ z := (lt_of_not_ge hzt).le
    have hpow := pow_le_pow_left₀ ht.le htz (p - 1)
    have hmul := mul_le_mul_of_nonneg_left hpow hz
    have hpEq : p - 1 + 1 = p := by omega
    have hzle : z ≤ z ^ p / t ^ (p - 1) := by
      apply (le_div_iff₀ (pow_pos ht _)).mpr
      simpa only [← pow_succ', hpEq] using hmul
    exact hzle.trans (le_add_of_nonneg_left ht.le)

theorem tail_term_eq (L : ℝ) (hL : 0 < L) (p : ℕ) (hp : 1 ≤ p) :
    L ^ p / (2 * L) ^ (p - 1) = L * (1 / (2 : ℝ)) ^ (p - 1) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : p ≠ 0)
  simp only [Nat.succ_sub_one, pow_succ, mul_pow, div_pow]
  field_simp
  ring

theorem geometric_weights_le_one (m : ℕ) (p : Fin m → ℕ)
    (hp : ∀ i, i.val + 2 ≤ p i) :
    (∑ i, (1 / (2 : ℝ)) ^ (p i - 1)) ≤ 1 := by
  calc
    (∑ i, (1 / (2 : ℝ)) ^ (p i - 1)) ≤ ∑ i : Fin m, (1 / (2 : ℝ)) ^ (i.val + 1) := by
      apply Finset.sum_le_sum
      intro i _
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by have := hp i; omega)
    _ = (1 / (2 : ℝ)) * ∑ k ∈ Finset.range m, (1 / (2 : ℝ)) ^ k := by
      simp only [pow_succ, ← Finset.sum_mul, Fin.sum_univ_eq_sum_range]
      ring
    _ ≤ (1 / (2 : ℝ)) * 2 :=
      mul_le_mul_of_nonneg_left (sum_geometric_two_le m) (by norm_num)
    _ = 1 := by norm_num

/-- Dimension-free assembly of actual block norms. The Pi norm is their
maximum, and the theorem also derives its integrability. -/
theorem mean_max_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {m : ℕ}
    (Z : Fin m → Ω → ℝ) (hZ : ∀ i, Integrable (Z i) μ)
    (hnonneg : ∀ i ω, 0 ≤ Z i ω) (p : Fin m → ℕ)
    (hp : ∀ i, i.val + 2 ≤ p i)
    (hpow : ∀ i, Integrable (fun ω => Z i ω ^ p i) μ)
    (L : ℝ) (hL : 0 < L)
    (hbound : ∀ i, (∫ ω, Z i ω ^ p i ∂μ) ≤ L ^ p i) :
    Integrable (fun ω => ‖fun i => Z i ω‖) μ ∧
      (∫ ω, ‖fun i => Z i ω‖ ∂μ) ≤ 3 * L := by
  have hmax := (Integrable.of_eval hZ).norm
  have ht : 0 < 2 * L := by positivity
  let T : Ω → ℝ := fun ω => 2 * L + ∑ i, Z i ω ^ p i / (2 * L) ^ (p i - 1)
  have hT : Integrable T μ := (integrable_const _).add
    (integrable_finsetSum _ fun i _ => (hpow i).div_const _)
  have hpoint (ω : Ω) : ‖fun i => Z i ω‖ ≤ T ω := by
    have hTnonneg : 0 ≤ T ω := by
      dsimp [T]
      exact add_nonneg ht.le (Finset.sum_nonneg fun i _ =>
        div_nonneg (pow_nonneg (hnonneg i ω) _) (pow_nonneg ht.le _))
    apply (pi_norm_le_iff_of_nonneg hTnonneg).mpr
    intro i
    rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg i ω)]
    have hsingle : Z i ω ^ p i / (2 * L) ^ (p i - 1) ≤
        ∑ j, Z j ω ^ p j / (2 * L) ^ (p j - 1) := by
      exact Finset.single_le_sum
        (f := fun j : Fin m => Z j ω ^ p j / (2 * L) ^ (p j - 1))
        (s := Finset.univ) (a := i)
        (fun j _ => div_nonneg (pow_nonneg (hnonneg j ω) (p j))
          (pow_nonneg ht.le (p j - 1))) (Finset.mem_univ i)
    exact (scalar_le_threshold_add_power (Z i ω) (2 * L) (hnonneg i ω) ht
      (p i) (by have := hp i; omega)).trans (add_le_add le_rfl hsingle)
  refine ⟨hmax, (integral_mono hmax hT hpoint).trans ?_⟩
  have hgeometric := geometric_weights_le_one m p hp
  calc
    (∫ ω, T ω ∂μ) = 2 * L + ∑ i, (∫ ω, Z i ω ^ p i ∂μ) / (2 * L) ^ (p i - 1) := by
      dsimp only [T]
      rw [integral_add (f := fun _ => 2 * L)
        (g := fun ω => ∑ i, Z i ω ^ p i / (2 * L) ^ (p i - 1))
        (integrable_const _) (integrable_finsetSum _ fun i _ => (hpow i).div_const _),
        integral_const, integral_finsetSum _ (fun i _ => (hpow i).div_const _)]
      simp [integral_div]
    _ ≤ 2 * L + ∑ i, L ^ p i / (2 * L) ^ (p i - 1) := by
      apply add_le_add le_rfl
      exact Finset.sum_le_sum fun i _ => div_le_div_of_nonneg_right (hbound i) (pow_nonneg ht.le _)
    _ = 2 * L + L * ∑ i, (1 / (2 : ℝ)) ^ (p i - 1) := by
      have htEq (i : Fin m) : L ^ p i / (2 * L) ^ (p i - 1) =
          L * (1 / (2 : ℝ)) ^ (p i - 1) :=
        tail_term_eq L hL (p i) (by have := hp i; omega)
      simp_rw [htEq]
      rw [Finset.mul_sum]
    _ ≤ 2 * L + L * 1 := add_le_add le_rfl (mul_le_mul_of_nonneg_left hgeometric hL.le)
    _ = 3 * L := by ring

end MI32.BlockMomentMaximum
