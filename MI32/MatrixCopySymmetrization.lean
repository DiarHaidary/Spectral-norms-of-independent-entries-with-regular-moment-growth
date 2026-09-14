import MI32.Statement
import MI32.MomentTools
import MI32.DiagonalCopyComparison
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# The actual matrix and its independent copy

The product probability space keeps the original coordinates and their
independent copies explicit. Reflection symmetry, independence and second
moments are derived. The operator-mean comparison uses the literal
Euclidean operator from the public statement.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace MI32.MatrixCopySymmetrization

variable {Ω E : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ]

def difference (V : E → Ω → ℝ) (e : E) (z : Ω × Ω) : ℝ :=
  V e z.1 - V e z.2

@[fun_prop] theorem measurable_difference (V : E → Ω → ℝ)
    (hV : ∀ e, Measurable (V e)) (e : E) : Measurable (difference V e) := by
  unfold difference
  fun_prop

theorem independent_differences [Fintype E] (V : E → Ω → ℝ)
    (hV : ∀ e, Measurable (V e)) (hind : iIndepFun V μ) :
    iIndepFun (difference V) (μ.prod μ) := by
  exact (DiagonalCopyComparison.independent_coordinatePairs V hV hind).comp
    (fun _ (p : ℝ × ℝ) => p.1 - p.2) (fun _ => by fun_prop)

theorem symmetric_difference (V : E → Ω → ℝ)
    (hV : ∀ e, Measurable (V e)) (e : E) :
    IdentDistrib (difference V e) (fun z => -difference V e z)
      (μ.prod μ) (μ.prod μ) := by
  refine ⟨(measurable_difference V hV e).aemeasurable,
    (measurable_difference V hV e).neg.aemeasurable, ?_⟩
  have hswap := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).map_eq
  calc
    (μ.prod μ).map (difference V e) =
        ((μ.prod μ).map Prod.swap).map (difference V e) := by rw [hswap]
    _ = (μ.prod μ).map (fun z => -difference V e z) := by
      rw [Measure.map_map (measurable_difference V hV e) measurable_swap]
      congr 1
      funext z
      simp [difference]

theorem integrable_difference_abs_rpow (V : E → Ω → ℝ)
    (hV : ∀ e, Measurable (V e))
    (hint : ∀ e (p : ℝ), 0 < p → Integrable (fun ω => |V e ω| ^ p) μ)
    (e : E) (p : ℝ) (hp : 0 < p) :
    Integrable (fun z => |difference V e z| ^ p) (μ.prod μ) := by
  have h := MomentTools.memLp_of_integrable_abs_rpow p hp (V e)
    (hV e).aestronglyMeasurable (hint e p hp)
  exact MomentTools.integrable_abs_rpow_of_memLp p hp _
    ((h.comp_fst μ).sub (h.comp_snd μ))

theorem integral_difference (V : E → Ω → ℝ)
    (hint : ∀ e, Integrable (V e) μ) (e : E) :
    (∫ z, difference V e z ∂(μ.prod μ)) = 0 := by
  unfold difference
  rw [integral_sub ((hint e).comp_fst μ) ((hint e).comp_snd μ)]
  simp [integral_fun_fst, integral_fun_snd]

theorem integral_difference_sq (S : Ω → ℝ)
    (hS : Integrable S μ) (hS2 : Integrable (fun ω => S ω ^ 2) μ)
    (hmean : ∫ ω, S ω ∂μ = 0) :
    (∫ z : Ω × Ω, (S z.1 - S z.2) ^ 2 ∂(μ.prod μ)) =
      2 * ∫ ω, S ω ^ 2 ∂μ := by
  have hprod := hS.mul_prod hS
  have hident : (fun z : Ω × Ω => (S z.1 - S z.2) ^ 2) =
      fun z => S z.1 ^ 2 + S z.2 ^ 2 - 2 * (S z.1 * S z.2) := by
    funext z
    ring
  rw [hident, integral_sub (f := fun z : Ω × Ω => S z.1 ^ 2 + S z.2 ^ 2)
    ((hS2.comp_fst μ).add (hS2.comp_snd μ))
    (hprod.const_mul 2), integral_add (hS2.comp_fst μ) (hS2.comp_snd μ),
    integral_const_mul, integral_prod_mul]
  rw [integral_fun_fst (fun ω => S ω ^ 2), integral_fun_snd (fun ω => S ω ^ 2)]
  simp [hmean]
  ring

/-- Norm Jensen after conditioning on the first copy, with all Bochner
integrability supplied by the actual original vector. -/
theorem integral_norm_le_copy {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] (f : Ω → F)
    (hf : Integrable f μ) (hmean : ∫ ω, f ω ∂μ = 0) :
    Integrable (fun z : Ω × Ω => ‖f z.1 - f z.2‖) (μ.prod μ) ∧
      (∫ ω, ‖f ω‖ ∂μ) ≤ ∫ z : Ω × Ω, ‖f z.1 - f z.2‖ ∂(μ.prod μ) := by
  have hc := ((hf.comp_fst μ).sub (hf.comp_snd μ)).norm
  refine ⟨hc, ?_⟩
  have hp (ω : Ω) : ‖f ω‖ ≤ ∫ η, ‖f ω - f η‖ ∂μ := by
    have hj := norm_integral_le_integral_norm (fun η => f ω - f η) (μ := μ)
    simpa [integral_sub (integrable_const _) hf, hmean] using hj
  calc
    (∫ ω, ‖f ω‖ ∂μ) ≤ ∫ ω, ∫ η, ‖f ω - f η‖ ∂μ ∂μ :=
      integral_mono hf.norm hc.integral_prod_left hp
    _ = ∫ z : Ω × Ω, ‖f z.1 - f z.2‖ ∂(μ.prod μ) :=
      (integral_prod _ hc).symm

section Matrix

open scoped Matrix.Norms.Elementwise

variable {n : ℕ}

/-- The matrix map is continuous from the finite entry space to its actual
Euclidean operator, independently of a chosen matrix norm notation. -/
def operatorMap : Matrix (Fin n) (Fin n) ℝ →L[ℝ]
    (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :=
  (Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap).toLinearMap.toContinuousLinearMap

theorem norm_operatorMap (A : Matrix (Fin n) (Fin n) ℝ) :
    ‖operatorMap A‖ = spectralNorm A := rfl

omit [IsProbabilityMeasure μ] in
theorem integrable_operator (X : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hint : ∀ i j, Integrable (fun ω => X ω i j) μ) :
    Integrable (fun ω => operatorMap (X ω)) μ := by
  exact operatorMap.integrable_comp (Integrable.of_eval fun i => Integrable.of_eval (hint i))

omit [IsProbabilityMeasure μ] in
theorem integral_operator_zero (X : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hint : ∀ i j, Integrable (fun ω => X ω i j) μ)
    (hmean : ∀ i j, ∫ ω, X ω i j ∂μ = 0) :
    (∫ ω, operatorMap (X ω) ∂μ) = 0 := by
  have hX := Integrable.of_eval fun i => Integrable.of_eval (hint i)
  have hz : (∫ ω, (fun i j => X ω i j) ∂μ) = 0 := by
    ext i j
    rw [eval_integral (fun i => Integrable.of_eval (hint i)), eval_integral (hint i)]
    exact hmean i j
  change (∫ ω, X ω ∂μ) = 0 at hz
  have heq := operatorMap.integral_comp_comm hX
  rw [hz] at heq
  exact heq.trans (map_zero operatorMap)

/-- Symmetrization of the original statement's Euclidean operator mean.
The copied matrix uses the same original indices in both coordinates. -/
theorem spectral_mean_le_copy (X : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hint : ∀ i j, Integrable (fun ω => X ω i j) μ)
    (hmean : ∀ i j, ∫ ω, X ω i j ∂μ = 0) :
    Integrable (fun ω => spectralNorm (X ω)) μ ∧
      Integrable (fun z : Ω × Ω => spectralNorm (X z.1 - X z.2)) (μ.prod μ) ∧
      (∫ ω, spectralNorm (X ω) ∂μ) ≤
        ∫ z : Ω × Ω, spectralNorm (X z.1 - X z.2) ∂(μ.prod μ) := by
  have hi := integrable_operator X hint
  have hc := integral_norm_le_copy (fun ω => operatorMap (X ω)) hi
    (integral_operator_zero X hint hmean)
  simpa only [← map_sub, norm_operatorMap] using And.intro hi.norm hc

end Matrix
end MI32.MatrixCopySymmetrization
