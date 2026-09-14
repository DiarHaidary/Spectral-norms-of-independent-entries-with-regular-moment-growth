import MI32.BipartiteVacuumIteration
import MI32.BipartiteNorm
import Mathlib.Analysis.Normed.Module.RCLike.Real

/-!
# Constant-one weak tests for the actual symmetric bipartite lift

At every real order p at least one, the two off-diagonal scalar tests obey
Minkowski. Euclidean Cauchy--Schwarz on the row and column norm parts keeps
the original weak-test constant unchanged. The sums may share all their
randomness. No claim is made here about orders below one.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace MI32.BipartiteWeakMoment

variable {Ω R C : Type*} [Fintype R] [Fintype C] [DecidableEq R] [DecidableEq C]

def rowPart (s : EuclideanSpace ℝ (Sum R C)) : EuclideanSpace ℝ R :=
  WithLp.toLp 2 (fun i => s (.inl i))

def colPart (s : EuclideanSpace ℝ (Sum R C)) : EuclideanSpace ℝ C :=
  WithLp.toLp 2 (fun j => s (.inr j))

omit [DecidableEq R] [DecidableEq C] in
theorem norm_sq_parts (s : EuclideanSpace ℝ (Sum R C)) :
    ‖s‖ ^ 2 = ‖rowPart s‖ ^ 2 + ‖colPart s‖ ^ 2 := by
  simp only [EuclideanSpace.real_norm_sq_eq, rowPart, colPart,
    Fintype.sum_sum_type]

omit [DecidableEq R] [DecidableEq C] in
/-- Two-dimensional Cauchy--Schwarz for the opposite-side norm products. -/
theorem cross_norm_parts_le (s t : EuclideanSpace ℝ (Sum R C)) :
    ‖rowPart s‖ * ‖colPart t‖ + ‖rowPart t‖ * ‖colPart s‖ ≤ ‖s‖ * ‖t‖ := by
  apply (sq_le_sq₀ (by positivity) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, norm_sq_parts s, norm_sq_parts t]
  nlinarith [sq_nonneg (‖rowPart s‖ * ‖rowPart t‖ - ‖colPart s‖ * ‖colPart t‖)]

/-- Exact decomposition using the same original matrix in both orientations. -/
theorem lift_bilinear_eq (X : R → C → Ω → ℝ)
    (s t : EuclideanSpace ℝ (Sum R C)) :
    ThinMatrix.bilinear (fun a b ω => BipartiteVacuumIteration.lift X ω a b) s t =
      fun ω => ThinMatrix.bilinear X (rowPart s) (colPart t) ω +
        ThinMatrix.bilinear X (rowPart t) (colPart s) ω := by
  funext ω
  unfold ThinMatrix.bilinear
  simp only [Fintype.sum_sum_type, BipartiteVacuumIteration.lift,
    PositiveVacuumWords.bipartite_matrix_inl_inl,
    PositiveVacuumWords.bipartite_matrix_inr_inr,
    PositiveVacuumWords.bipartite_matrix_inl_inr,
    PositiveVacuumWords.bipartite_matrix_inr_inl, mul_zero, zero_mul,
    Finset.sum_const_zero, zero_add, add_zero, rowPart, colPart, PiLp.toLp_apply]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The original scalar test embeds exactly by placing its vectors on opposite sides. -/
theorem lift_bilinear_left_right (X : R → C → Ω → ℝ)
    (s : EuclideanSpace ℝ R) (t : EuclideanSpace ℝ C) :
    ThinMatrix.bilinear (fun a b ω => BipartiteVacuumIteration.lift X ω a b)
      (BipartiteNorm.left s) (BipartiteNorm.right t) = ThinMatrix.bilinear X s t := by
  rw [lift_bilinear_eq]
  funext ω
  simp [ThinMatrix.bilinear, rowPart, colPart, BipartiteNorm.left, BipartiteNorm.right]

omit [DecidableEq R] [DecidableEq C] in
/-- Deterministic scaling is outside the actual original scalar random variable. -/
theorem bilinear_smul (X : R → C → Ω → ℝ)
    (s : EuclideanSpace ℝ R) (t : EuclideanSpace ℝ C) (a b : ℝ) :
    ThinMatrix.bilinear X (a • s) (b • t) =
      fun ω => (a * b) * ThinMatrix.bilinear X s t ω := by
  funext ω
  simp only [ThinMatrix.bilinear, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem norm_smul_normalized {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (s : V) : ‖s‖ • (‖s‖⁻¹ • s) = s := by
  by_cases hs : s = 0
  · simp [hs]
  · rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hs), one_smul]

section Measure

variable [MeasurableSpace Ω] {μ : Measure Ω}

omit [DecidableEq R] [DecidableEq C] in
/-- Integrability of finite original bilinear forms, requiring no coordinate independence. -/
theorem memLp_bilinear (X : R → C → Ω → ℝ) (hX : ∀ i j, Measurable (X i j))
    (hint : ∀ i j (p : ℝ), 0 < p → Integrable (fun ω => |X i j ω| ^ p) μ)
    (p : ℝ) (hp : 0 < p) (s : EuclideanSpace ℝ R) (t : EuclideanSpace ℝ C) :
    MemLp (ThinMatrix.bilinear X s t) (ENNReal.ofReal p) μ := by
  unfold ThinMatrix.bilinear
  apply memLp_finsetSum
  intro i _
  apply memLp_finsetSum
  intro j _
  exact ((MomentTools.memLp_of_integrable_abs_rpow p hp (X i j)
    (hX i j).aestronglyMeasurable (hint i j p hp)).const_mul (s i)).mul_const (t j)

omit [DecidableEq R] [DecidableEq C] in
/-- Unit-test control is homogeneous in the two deterministic Euclidean vectors. -/
theorem bilinear_moment_le_norms (X : R → C → Ω → ℝ) (p : ℝ) (hp : 0 < p) (W : ℝ)
    (hweak : ∀ s : EuclideanSpace ℝ R, ‖s‖ ≤ 1 →
      ∀ t : EuclideanSpace ℝ C, ‖t‖ ≤ 1 → moment μ p (ThinMatrix.bilinear X s t) ≤ W)
    (s : EuclideanSpace ℝ R) (t : EuclideanSpace ℝ C) :
    moment μ p (ThinMatrix.bilinear X s t) ≤ W * (‖s‖ * ‖t‖) := by
  have hs : ‖‖s‖⁻¹ • s‖ ≤ 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using inv_norm_smul_mem_unitClosedBall s
  have ht : ‖‖t‖⁻¹ • t‖ ≤ 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using inv_norm_smul_mem_unitClosedBall t
  have hrep : ThinMatrix.bilinear X s t =
      fun ω => (‖s‖ * ‖t‖) * ThinMatrix.bilinear X (‖s‖⁻¹ • s) (‖t‖⁻¹ • t) ω := by
    simpa only [norm_smul_normalized] using bilinear_smul X (‖s‖⁻¹ • s) (‖t‖⁻¹ • t) ‖s‖ ‖t‖
  rw [hrep, MomentTools.const_mul p hp,
    abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  exact (mul_le_mul_of_nonneg_left (hweak _ hs _ ht)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))).trans_eq (mul_comm _ _)

/-- For p at least one, every deterministic unit test of the actual lift
has finite p-th absolute moment and is bounded by the original weak-test constant.
There is no independence hypothesis between the two off-diagonal sums. -/
theorem lift_unit_test_moment_le
    (X : R → C → Ω → ℝ) (hX : ∀ i j, Measurable (X i j))
    (hint : ∀ i j (p : ℝ), 0 < p → Integrable (fun ω => |X i j ω| ^ p) μ)
    (p : ℝ) (hp : 1 ≤ p) (W : ℝ)
    (hweak : ∀ s : EuclideanSpace ℝ R, ‖s‖ ≤ 1 →
      ∀ t : EuclideanSpace ℝ C, ‖t‖ ≤ 1 → moment μ p (ThinMatrix.bilinear X s t) ≤ W)
    (s t : EuclideanSpace ℝ (Sum R C)) (hs : ‖s‖ ≤ 1) (ht : ‖t‖ ≤ 1) :
    Integrable (fun ω =>
      |ThinMatrix.bilinear (fun a b ω => BipartiteVacuumIteration.lift X ω a b) s t ω| ^ p) μ ∧
      moment μ p (ThinMatrix.bilinear
        (fun a b ω => BipartiteVacuumIteration.lift X ω a b) s t) ≤ W := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hW : 0 ≤ W := (MomentTools.nonneg (μ := μ) p (ThinMatrix.bilinear X 0 0)).trans
    (hweak 0 (by simp) 0 (by simp))
  have hmem1 := memLp_bilinear X hX hint p hp0 (rowPart s) (colPart t)
  have hmem2 := memLp_bilinear X hX hint p hp0 (rowPart t) (colPart s)
  rw [lift_bilinear_eq]
  refine ⟨MomentTools.integrable_abs_rpow_of_memLp p hp0 _ (hmem1.add hmem2), ?_⟩
  calc
    _ ≤ moment μ p (ThinMatrix.bilinear X (rowPart s) (colPart t)) +
        moment μ p (ThinMatrix.bilinear X (rowPart t) (colPart s)) :=
      MomentTools.add_le p hp _ _ hmem1 hmem2
    _ ≤ W * (‖rowPart s‖ * ‖colPart t‖) + W * (‖rowPart t‖ * ‖colPart s‖) :=
      add_le_add (bilinear_moment_le_norms X p hp0 W hweak _ _)
        (bilinear_moment_le_norms X p hp0 W hweak _ _)
    _ = W * (‖rowPart s‖ * ‖colPart t‖ + ‖rowPart t‖ * ‖colPart s‖) := (mul_add _ _ _).symm
    _ ≤ W * (‖s‖ * ‖t‖) := mul_le_mul_of_nonneg_left (cross_norm_parts_le s t) hW
    _ ≤ W * (1 * 1) :=
      mul_le_mul_of_nonneg_left (mul_le_mul hs ht (norm_nonneg _) zero_le_one) hW
    _ = W := by ring

end Measure
end MI32.BipartiteWeakMoment
