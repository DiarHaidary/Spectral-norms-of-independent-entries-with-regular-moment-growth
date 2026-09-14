import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Mul
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
# Independent-copy symmetrization at even orders

The copied probability space is the actual product of the original law
with itself. Jensen's inequality proves the centered-moment comparison;
all moment and Fubini integrability is derived from the original `MemLp`
assumption. This is the symmetrization step for the diagonal Hilbert
comparison, applied there to the sum of original coordinate squares.
-/

noncomputable section
open MeasureTheory

namespace MI32.CopySymmetrization

theorem integrable_even_pow {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {S : Ω → ℝ} {p : ℕ} (hp : p ≠ 0) (heven : Even p)
    (hS : MemLp S p μ) : Integrable (fun ω => S ω ^ p) μ := by
  simpa only [Real.norm_eq_abs, heven.pow_abs] using hS.integrable_norm_pow hp

/-- Centering a real variable is dominated, at every even moment, by
subtracting an actual independent copy. -/
theorem centered_even_moment_le_copy
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (S : Ω → ℝ) (p : ℕ) (hp : 1 ≤ p) (heven : Even p)
    (hS : MemLp S p μ) :
    Integrable (fun ω => (S ω - ∫ η, S η ∂μ) ^ p) μ ∧
      Integrable (fun z : Ω × Ω => (S z.1 - S z.2) ^ p) (μ.prod μ) ∧
      (∫ ω, (S ω - ∫ η, S η ∂μ) ^ p ∂μ) ≤
        ∫ z : Ω × Ω, (S z.1 - S z.2) ^ p ∂(μ.prod μ) := by
  have hp0 : p ≠ 0 := by omega
  have hS1 : Integrable S μ := hS.integrable (by exact_mod_cast hp)
  have hcent : Integrable (fun ω => (S ω - ∫ η, S η ∂μ) ^ p) μ :=
    integrable_even_pow hp0 heven (hS.sub (memLp_const _))
  have hcopy : Integrable (fun z : Ω × Ω => (S z.1 - S z.2) ^ p) (μ.prod μ) :=
    integrable_even_pow hp0 heven ((hS.comp_fst μ).sub (hS.comp_snd μ))
  refine ⟨hcent, hcopy, ?_⟩
  have hpoint (ω : Ω) :
      (S ω - ∫ η, S η ∂μ) ^ p ≤ ∫ η, (S ω - S η) ^ p ∂μ := by
    have hshift : Integrable (fun η => (S ω - S η) ^ p) μ :=
      integrable_even_pow hp0 heven ((memLp_const (S ω)).sub hS)
    have hj := heven.convexOn_pow.map_integral_le
      (μ := μ) (f := fun η => S ω - S η)
      (by fun_prop) isClosed_univ
      (Filter.Eventually.of_forall fun _ => Set.mem_univ _)
      ((integrable_const _).sub hS1) hshift
    simpa [integral_sub (integrable_const _) hS1, integral_const] using hj
  calc
    (∫ ω, (S ω - ∫ η, S η ∂μ) ^ p ∂μ) ≤
        ∫ ω, ∫ η, (S ω - S η) ^ p ∂μ ∂μ :=
      integral_mono hcent hcopy.integral_prod_left hpoint
    _ = ∫ z : Ω × Ω, (S z.1 - S z.2) ^ p ∂(μ.prod μ) :=
      (integral_prod _ hcopy).symm

end MI32.CopySymmetrization
