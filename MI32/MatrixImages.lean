import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Tactic

/-!
# Exact second moments of fixed matrix images

The variance scale in the thin-matrix argument is derived from the original
entries, with their original independence. No comparison estimate is assumed.
The first lemma needs only pairwise independence and is reusable for either
matrix axis.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace MI32

/-- The second moment of a centered independent linear form, keeping every
original coefficient and entry variance. -/
theorem integral_linear_sum_sq
    {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    {μ : Measure Ω} (X : I → Ω → ℝ)
    (hX : ∀ i, MemLp (X i) 2 μ)
    (hind : Pairwise (fun i j => IndepFun (X i) (X j) μ))
    (hmean : ∀ i, (∫ ω, X i ω ∂μ) = 0) (s : I → ℝ) :
    (∫ ω, (∑ i, s i * X i ω) ^ 2 ∂μ) =
      ∑ i, s i ^ 2 * ∫ ω, X i ω ^ 2 ∂μ := by
  classical
  have hprod (i j : I) :
      Integrable (fun ω => (s i * X i ω) * (s j * X j ω)) μ := by
    convert ((hX i).integrable_mul (hX j)).const_mul (s i * s j) using 1
    ext ω
    simp only [Pi.mul_apply]
    ring
  have hexpand (ω : Ω) :
      (∑ i, s i * X i ω) ^ 2 =
        ∑ i, ∑ j, (s i * X i ω) * (s j * X j ω) := by
    rw [pow_two, Finset.sum_mul]
    simp only [Finset.mul_sum]
  simp_rw [hexpand]
  rw [integral_finsetSum _ (fun i _ =>
    integrable_finsetSum _ (fun j _ => hprod i j))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finsetSum _ (fun j _ => hprod i j)]
  calc
    (∑ j, ∫ ω, (s i * X i ω) * (s j * X j ω) ∂μ) =
        ∫ ω, (s i * X i ω) * (s i * X i ω) ∂μ := by
      apply Finset.sum_eq_single i
      · intro j hj hji
        have hzero : (∫ ω, X i ω * X j ω ∂μ) = 0 := by
          rw [(hind hji.symm).integral_fun_mul_eq_mul_integral
            (hX i).aestronglyMeasurable (hX j).aestronglyMeasurable, hmean i,
            zero_mul]
        calc
          (∫ ω, (s i * X i ω) * (s j * X j ω) ∂μ) =
              (s i * s j) * ∫ ω, X i ω * X j ω ∂μ := by
            rw [← integral_const_mul]
            congr 1
            ext ω
            ring
          _ = 0 := by rw [hzero, mul_zero]
      · simp
    _ = s i ^ 2 * ∫ ω, X i ω ^ 2 ∂μ := by
      rw [← integral_const_mul]
      congr 1
      ext ω
      ring

/-- Exact squared Euclidean image moment for a fixed row vector. The same
lemma applies to a column vector after swapping the matrix axes. -/
theorem integral_matrix_image_sq
    {Ω I J : Type*} [MeasurableSpace Ω] [Fintype I] [Fintype J]
    {μ : Measure Ω} (X : I → J → Ω → ℝ)
    (hX : ∀ i j, MemLp (X i j) 2 μ)
    (hind : iIndepFun (fun e : I × J => X e.1 e.2) μ)
    (hmean : ∀ i j, (∫ ω, X i j ω ∂μ) = 0) (s : I → ℝ) :
    (∫ ω, ∑ j, (∑ i, s i * X i j ω) ^ 2 ∂μ) =
      ∑ i, s i ^ 2 * ∑ j, ∫ ω, X i j ω ^ 2 ∂μ := by
  classical
  have himage (j : J) : MemLp (fun ω => ∑ i, s i * X i j ω) 2 μ :=
    memLp_finsetSum _ (fun i _ => (hX i j).const_mul (s i))
  rw [integral_finsetSum _ (fun j _ => (himage j).integrable_sq)]
  calc
    (∑ j, ∫ ω, (∑ i, s i * X i j ω) ^ 2 ∂μ) =
        ∑ j, ∑ i, s i ^ 2 * ∫ ω, X i j ω ^ 2 ∂μ := by
      apply Finset.sum_congr rfl
      intro j hj
      exact integral_linear_sum_sq (fun i => X i j) (fun i => hX i j)
        (fun i i' hij => hind.indepFun (i := (i, j)) (j := (i', j))
          (fun h => hij (congrArg Prod.fst h))) (fun i => hmean i j) s
    _ = ∑ i, s i ^ 2 * ∑ j, ∫ ω, X i j ω ^ 2 ∂μ := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]

/-- A unit row vector incurs precisely the maximum row variance budget;
there is no dimension or moment-order factor at this step. -/
theorem integral_matrix_image_sq_le
    {Ω I J : Type*} [MeasurableSpace Ω] [Fintype I] [Fintype J]
    {μ : Measure Ω} (X : I → J → Ω → ℝ)
    (hX : ∀ i j, MemLp (X i j) 2 μ)
    (hind : iIndepFun (fun e : I × J => X e.1 e.2) μ)
    (hmean : ∀ i j, (∫ ω, X i j ω ∂μ) = 0)
    (s : I → ℝ) (hs : ∑ i, s i ^ 2 ≤ 1)
    (B : ℝ) (hB : 0 ≤ B)
    (hrow : ∀ i, (∑ j, ∫ ω, X i j ω ^ 2 ∂μ) ≤ B) :
    (∫ ω, ∑ j, (∑ i, s i * X i j ω) ^ 2 ∂μ) ≤ B := by
  rw [integral_matrix_image_sq X hX hind hmean s]
  calc
    (∑ i, s i ^ 2 * ∑ j, ∫ ω, X i j ω ^ 2 ∂μ) ≤ ∑ i, s i ^ 2 * B :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hrow i) (sq_nonneg _))
    _ = (∑ i, s i ^ 2) * B := by rw [Finset.sum_mul]
    _ ≤ B := by nlinarith

/-- The literal Euclidean image of the original matrix transpose. -/
def matrixRowImage {Ω I J : Type*} [Fintype I]
    (X : I → J → Ω → ℝ) (s : I → ℝ) (ω : Ω) : EuclideanSpace ℝ J :=
  WithLp.toLp 2 (fun j => ∑ i, s i * X i j ω)

/-- The coordinate formula is compatible with the Euclidean norm used in
the finite-net theorem, rather than the supremum norm on coordinate tuples. -/
theorem matrixRowImage_norm_sq {Ω I J : Type*} [Fintype I] [Fintype J]
    (X : I → J → Ω → ℝ) (s : I → ℝ) (ω : Ω) :
    ‖matrixRowImage X s ω‖ ^ 2 = ∑ j, (∑ i, s i * X i j ω) ^ 2 :=
  EuclideanSpace.real_norm_sq_eq _

/-- The expectation term in the fixed-vector strong--weak comparison is
bounded by the original row variance scale, with constant one. -/
theorem integral_matrixRowImage_norm_le
    {Ω I J : Type*} [MeasurableSpace Ω] [Fintype I] [Fintype J]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (X : I → J → Ω → ℝ)
    (hXm : ∀ i j, Measurable (X i j)) (hX : ∀ i j, MemLp (X i j) 2 μ)
    (hind : iIndepFun (fun e : I × J => X e.1 e.2) μ)
    (hmean : ∀ i j, (∫ ω, X i j ω ∂μ) = 0)
    (s : I → ℝ) (hs : ∑ i, s i ^ 2 ≤ 1)
    (B : ℝ) (hB : 0 ≤ B)
    (hrow : ∀ i, (∑ j, ∫ ω, X i j ω ^ 2 ∂μ) ≤ B) :
    Integrable (fun ω => ‖matrixRowImage X s ω‖) μ ∧
      (∫ ω, ‖matrixRowImage X s ω‖ ∂μ) ≤ Real.sqrt B := by
  classical
  have hm : Measurable (fun ω => ‖matrixRowImage X s ω‖) := by
    unfold matrixRowImage
    fun_prop
  have hint : Integrable (fun ω => ‖matrixRowImage X s ω‖ ^ 2) μ := by
    simp_rw [matrixRowImage_norm_sq]
    exact integrable_finsetSum _ (fun j _ =>
      (memLp_finsetSum _ (fun i _ => (hX i j).const_mul (s i))).integrable_sq)
  have hlp : MemLp (fun ω => ‖matrixRowImage X s ω‖) 2 μ :=
    (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr hint
  refine ⟨hlp.integrable (by norm_num), ?_⟩
  have hsecond : (∫ ω, ‖matrixRowImage X s ω‖ ^ 2 ∂μ) ≤ B := by
    simp_rw [matrixRowImage_norm_sq]
    exact integral_matrix_image_sq_le X hX hind hmean s hs B hB hrow
  have hvar := variance_nonneg (fun ω => ‖matrixRowImage X s ω‖) μ
  rw [variance_eq_sub hlp] at hvar
  simp only [Pi.pow_apply] at hvar
  have hsqrt := Real.sq_sqrt hB
  have hsqrt0 := Real.sqrt_nonneg B
  nlinarith

end MI32
