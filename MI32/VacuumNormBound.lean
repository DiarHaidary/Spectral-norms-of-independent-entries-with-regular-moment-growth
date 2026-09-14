import MI32.MomentTools
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Deterministic operator bounds from actual vacuum powers

Positive integer powers of a self-adjoint operator retain the exact norm
power. A finite Euclidean basis then bounds the operator moment by the sum
of the actual squared vacuum norms. This is a deterministic inequality;
it does not assume a probabilistic vacuum or trace estimate.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open MeasureTheory

namespace MI32.VacuumNormBound

/-- The C-star square identity yields the norm of every positive integer
power, without requiring the underlying space or ring to be nontrivial. -/
theorem norm_pow_of_selfAdjoint {A : Type*} [NormedRing A] [StarRing A] [CStarRing A]
    (a : A) (ha : IsSelfAdjoint a) (q : ℕ) (hq : 1 ≤ q) : ‖a ^ q‖ = ‖a‖ ^ q := by
  by_cases hz : a = 0
  · simp [hz, Nat.ne_zero_of_lt hq]
  have hn : 0 < ‖a‖ := norm_pos_iff.mpr hz
  have hqN : q < 2 ^ q := q.lt_two_pow_self
  apply le_antisymm (norm_pow_le' a (by omega))
  apply (mul_le_mul_iff_right₀ (pow_pos hn (2 ^ q - q))).mp
  calc
    ‖a‖ ^ (2 ^ q - q) * ‖a‖ ^ q = ‖a‖ ^ (2 ^ q) := by
      rw [← pow_add]
      congr 1
      omega
    _ = ‖a ^ (2 ^ q)‖ := (ha.norm_pow_two_pow q).symm
    _ = ‖a ^ (2 ^ q - q) * a ^ q‖ := by
      rw [← pow_add]
      congr 2
      omega
    _ ≤ ‖a ^ (2 ^ q - q)‖ * ‖a ^ q‖ := norm_mul_le _ _
    _ ≤ ‖a‖ ^ (2 ^ q - q) * ‖a ^ q‖ :=
      mul_le_mul_of_nonneg_right (norm_pow_le' a (by omega)) (norm_nonneg _)

section Basis
variable {V E : Type*} [Fintype V] [DecidableEq V]
    [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [DecidableEq V] in
/-- A finite real Euclidean operator is bounded by its actual basis images.
The proof is the triangle inequality followed by scalar Cauchy--Schwarz. -/
theorem action_norm_le_sqrt_basis_energy (A : EuclideanSpace ℝ V →L[ℝ] E)
    (x : EuclideanSpace ℝ V) :
    ‖A x‖ ≤ Real.sqrt (∑ i, ‖A (EuclideanSpace.basisFun V ℝ i)‖ ^ 2) * ‖x‖ := by
  have hx : (∑ i, x i • A (EuclideanSpace.basisFun V ℝ i)) = A x := by
    simpa only [map_sum, map_smul, EuclideanSpace.basisFun_repr] using
      congrArg A ((EuclideanSpace.basisFun V ℝ).sum_repr x)
  calc
    ‖A x‖ = ‖∑ i, x i • A (EuclideanSpace.basisFun V ℝ i)‖ := by rw [hx]
    _ ≤ ∑ i, ‖x i • A (EuclideanSpace.basisFun V ℝ i)‖ := norm_sum_le _ _
    _ = ∑ i, |x i| * ‖A (EuclideanSpace.basisFun V ℝ i)‖ := by
      simp only [norm_smul, Real.norm_eq_abs]
    _ ≤ Real.sqrt (∑ i, |x i| ^ 2) *
        Real.sqrt (∑ i, ‖A (EuclideanSpace.basisFun V ℝ i)‖ ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = _ := by
      simp only [sq_abs, ← EuclideanSpace.real_norm_sq_eq x,
        Real.sqrt_sq (norm_nonneg x), mul_comm]

omit [DecidableEq V] in
theorem opNorm_sq_le_basis_energy (A : EuclideanSpace ℝ V →L[ℝ] E) :
    ‖A‖ ^ 2 ≤ ∑ i, ‖A (EuclideanSpace.basisFun V ℝ i)‖ ^ 2 := by
  have h := A.opNorm_le_bound (Real.sqrt_nonneg _)
    (action_norm_le_sqrt_basis_energy A)
  have hs := pow_le_pow_left₀ (norm_nonneg A) h 2
  simpa only [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)] using hs

end Basis

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The squared vacuum norms are exactly the Frobenius energy, in original
Euclidean coordinates. The equality includes an empty coordinate type. -/
theorem sum_vacuum_norm_sq_eq_trace (A : Matrix V V ℝ) :
    (∑ i, ‖Matrix.toEuclideanCLM (n := V) (𝕜 := ℝ) A
      (EuclideanSpace.basisFun V ℝ i)‖ ^ 2) = (A.transpose * A).trace := by
  simp only [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.basisFun_apply,
    PiLp.single, Matrix.toEuclideanCLM_toLp]
  change (∑ i, ∑ j, ((A.mulVec (Pi.single i 1)) j) ^ 2) = ∑ i, ∑ j, A j i * A j i
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  simp [Matrix.mulVec_single, pow_two]

/-- Every self-adjoint positive-order operator moment is controlled by the
same actual vacuum powers, with no factor introduced at this step. -/
theorem norm_even_pow_le_vacuum_sum (A : Matrix V V ℝ) (hA : IsSelfAdjoint A)
    (q : ℕ) (hq : 1 ≤ q) :
    ‖A‖ ^ (2 * q) ≤
      ∑ i, ‖Matrix.toEuclideanCLM (n := V) (𝕜 := ℝ) (A ^ q)
        (EuclideanSpace.basisFun V ℝ i)‖ ^ 2 := by
  calc
    ‖A‖ ^ (2 * q) = (‖A‖ ^ q) ^ 2 := by rw [← pow_mul, Nat.mul_comm]
    _ = ‖A ^ q‖ ^ 2 := by rw [norm_pow_of_selfAdjoint A hA q hq]
    _ = ‖Matrix.toEuclideanCLM (n := V) (𝕜 := ℝ) (A ^ q)‖ ^ 2 := rfl
    _ ≤ _ := opNorm_sq_le_basis_energy _

section Probability
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Integrability and the operator power bound follow from the actual vacuum
energies. This intermediate interface does not assume an operator estimate. -/
theorem integral_norm_even_pow_le_vacuum_sum
    (A : Ω → Matrix V V ℝ) (hNorm : Measurable (fun ω => ‖A ω‖))
    (hA : ∀ ω, IsSelfAdjoint (A ω)) (q : ℕ) (hq : 1 ≤ q)
    (hVac : ∀ i, Integrable (fun ω =>
      ‖Matrix.toEuclideanCLM (n := V) (𝕜 := ℝ) (A ω ^ q)
        (EuclideanSpace.basisFun V ℝ i)‖ ^ 2) μ) :
    Integrable (fun ω => ‖A ω‖ ^ (2 * q)) μ ∧
      (∫ ω, ‖A ω‖ ^ (2 * q) ∂μ) ≤
        ∑ i, ∫ ω, ‖Matrix.toEuclideanCLM (n := V) (𝕜 := ℝ) (A ω ^ q)
          (EuclideanSpace.basisFun V ℝ i)‖ ^ 2 ∂μ := by
  have hsum := integrable_finsetSum Finset.univ (fun i _ => hVac i)
  have hpoint (ω : Ω) := norm_even_pow_le_vacuum_sum (A ω) (hA ω) q hq
  have hInt : Integrable (fun ω => ‖A ω‖ ^ (2 * q)) μ :=
    hsum.mono' (hNorm.pow_const _).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg _) _)]
        exact hpoint ω)
  refine ⟨hInt, ?_⟩
  calc
    _ ≤ ∫ ω, ∑ i, ‖Matrix.toEuclideanCLM (n := V) (𝕜 := ℝ) (A ω ^ q)
        (EuclideanSpace.basisFun V ℝ i)‖ ^ 2 ∂μ := integral_mono hInt hsum hpoint
    _ = _ := integral_finsetSum _ (fun i _ => hVac i)

/-- After each actual vacuum energy is bounded, the only dimension loss is
card(V)^(1/(2q)). The preceding analytic iteration must supply `hBound`. -/
theorem norm_moment_le_of_vacuum_energies
    (A : Ω → Matrix V V ℝ) (hNorm : Measurable (fun ω => ‖A ω‖))
    (hA : ∀ ω, IsSelfAdjoint (A ω)) (q : ℕ) (hq : 1 ≤ q)
    (hVac : ∀ i, Integrable (fun ω =>
      ‖Matrix.toEuclideanCLM (n := V) (𝕜 := ℝ) (A ω ^ q)
        (EuclideanSpace.basisFun V ℝ i)‖ ^ 2) μ)
    (L : ℝ) (hL : 0 ≤ L)
    (hBound : ∀ i, (∫ ω,
      ‖Matrix.toEuclideanCLM (n := V) (𝕜 := ℝ) (A ω ^ q)
        (EuclideanSpace.basisFun V ℝ i)‖ ^ 2 ∂μ) ≤ L ^ (2 * q)) :
    Integrable (fun ω => ‖A ω‖ ^ (2 * q)) μ ∧
      moment μ (2 * (q : ℝ)) (fun ω => ‖A ω‖) ≤
        (Fintype.card V : ℝ) ^ (1 / (2 * (q : ℝ))) * L := by
  obtain ⟨hInt, hSum⟩ := integral_norm_even_pow_le_vacuum_sum A hNorm hA q hq hVac
  have hI : (∫ ω, ‖A ω‖ ^ (2 * q) ∂μ) ≤ L ^ (2 * q) * (Fintype.card V : ℝ) := by
    calc
      _ ≤ ∑ i : V, L ^ (2 * q) := hSum.trans (Finset.sum_le_sum fun i _ => hBound i)
      _ = _ := by simp [mul_comm]
  refine ⟨hInt, ?_⟩
  have hRoot := MomentTools.nat_root_le _ (Fintype.card V : ℝ) L
    (integral_nonneg fun ω => pow_nonneg (norm_nonneg _) _) (by positivity) hL
    (2 * q) (by omega) hI
  simpa only [moment, Nat.cast_mul, Nat.cast_ofNat, abs_of_nonneg (norm_nonneg _),
    ← Real.rpow_natCast, mul_comm] using hRoot

end Probability

end MI32.VacuumNormBound
