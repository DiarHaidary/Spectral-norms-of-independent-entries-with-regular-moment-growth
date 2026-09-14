import MI32.LocalLogMoment

/-!
# Arbitrarily many scalar doublings of a deterministic bilinear test

`LocalLogMoment.bilinear_moment_le_eight` iterates the all-order scalar
doubling three times. Here the same single doubling step, namely
`SymmetricLinearAllOrders.linear_root_doubling` read through
`LocalLogMoment.linearForm_eq_bilinear`, is iterated `k` times by induction,
and one exponent monotonicity step then controls every smaller positive order.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory

namespace MI32.BilinearHighOrder

variable {Ω R C : Type*} [MeasurableSpace Ω] [Fintype R] [Fintype C]
    [DecidableEq R] [DecidableEq C] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- One scalar doubling for a deterministic bilinear test in the original
independent symmetric coordinates. -/
theorem bilinear_moment_doubling
    (X : R → C → Ω → ℝ) (hX : ∀ i j, Measurable (X i j))
    (hind : iIndepFun (fun e : R × C => X e.1 e.2) μ)
    (hsym : ∀ i j, IdentDistrib (X i j) (fun ω => -X i j ω) μ μ)
    (hint : ∀ i j (p : ℝ), 0 < p → Integrable (fun ω => |X i j ω| ^ p) μ)
    (α : ℝ) (hα : 1 ≤ α)
    (hregular : ∀ i j (r : ℝ), 1 ≤ r →
      moment μ (2 * r) (X i j) ≤ α * moment μ r (X i j))
    (s : EuclideanSpace ℝ R) (t : EuclideanSpace ℝ C)
    (u : ℝ) (hu : Real.log 2 ≤ u) :
    moment μ (2 * u) (ThinMatrix.bilinear X s t) ≤
      SymmetricLinearAllOrders.doublingConstant α *
        moment μ u (ThinMatrix.bilinear X s t) := by
  simpa only [LocalLogMoment.linearForm_eq_bilinear] using
    SymmetricLinearAllOrders.linear_root_doubling (fun e : R × C => X e.1 e.2)
      (fun e => hX e.1 e.2) hind (fun e => hsym e.1 e.2)
      (fun e => hint e.1 e.2) α hα (fun e => hregular e.1 e.2)
      (fun e => s e.1 * t e.2) u hu

/-- Repeated scalar doubling for one deterministic bilinear test in the original
independent symmetric coordinates. -/
theorem bilinear_moment_doubling_pow
    (X : R → C → Ω → ℝ) (hX : ∀ i j, Measurable (X i j))
    (hind : iIndepFun (fun e : R × C => X e.1 e.2) μ)
    (hsym : ∀ i j, IdentDistrib (X i j) (fun ω => -X i j ω) μ μ)
    (hint : ∀ i j (p : ℝ), 0 < p → Integrable (fun ω => |X i j ω| ^ p) μ)
    (α : ℝ) (hα : 1 ≤ α)
    (hregular : ∀ i j (r : ℝ), 1 ≤ r →
      moment μ (2 * r) (X i j) ≤ α * moment μ r (X i j))
    (s : EuclideanSpace ℝ R) (t : EuclideanSpace ℝ C)
    (k : ℕ) (p : ℝ) (hp : Real.log 2 ≤ p) :
    moment μ (2 ^ k * p) (ThinMatrix.bilinear X s t) ≤
      SymmetricLinearAllOrders.doublingConstant α ^ k *
        moment μ p (ThinMatrix.bilinear X s t) := by
  let J := SymmetricLinearAllOrders.doublingConstant α
  have hJ : 0 ≤ J := le_trans zero_le_one
    (SymmetricLinearAllOrders.one_le_doublingConstant α hα)
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  induction k with
  | zero => simp
  | succ k ih =>
    have hk : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    have hu : Real.log 2 ≤ 2 ^ k * p := by nlinarith
    calc
      moment μ (2 ^ (k + 1) * p) (ThinMatrix.bilinear X s t)
          = moment μ (2 * (2 ^ k * p)) (ThinMatrix.bilinear X s t) := by ring_nf
      _ ≤ J * moment μ (2 ^ k * p) (ThinMatrix.bilinear X s t) :=
        bilinear_moment_doubling X hX hind hsym hint α hα hregular s t _ hu
      _ ≤ J * (J ^ k * moment μ p (ThinMatrix.bilinear X s t)) :=
        mul_le_mul_of_nonneg_left ih hJ
      _ = J ^ (k + 1) * moment μ p (ThinMatrix.bilinear X s t) := by ring

/-- Any smaller positive order is controlled by `k` doublings from the original
exact order. -/
theorem bilinear_moment_le_pow
    (X : R → C → Ω → ℝ) (hX : ∀ i j, Measurable (X i j))
    (hind : iIndepFun (fun e : R × C => X e.1 e.2) μ)
    (hsym : ∀ i j, IdentDistrib (X i j) (fun ω => -X i j ω) μ μ)
    (hint : ∀ i j (p : ℝ), 0 < p → Integrable (fun ω => |X i j ω| ^ p) μ)
    (α : ℝ) (hα : 1 ≤ α)
    (hregular : ∀ i j (r : ℝ), 1 ≤ r →
      moment μ (2 * r) (X i j) ≤ α * moment μ r (X i j))
    (s : EuclideanSpace ℝ R) (t : EuclideanSpace ℝ C)
    (k : ℕ) (p r : ℝ) (hp : Real.log 2 ≤ p) (hr : 0 < r) (hrp : r ≤ 2 ^ k * p) :
    moment μ r (ThinMatrix.bilinear X s t) ≤
      SymmetricLinearAllOrders.doublingConstant α ^ k *
        moment μ p (ThinMatrix.bilinear X s t) := by
  have hp0 : 0 < p := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans_le hp
  have hInt : Integrable (fun ω => |ThinMatrix.bilinear X s t ω| ^ (2 ^ k * p)) μ := by
    simpa only [LocalLogMoment.linearForm_eq_bilinear] using
      SymmetricLinearRegularity.integrable_abs_rpow_linearForm
        (fun e : R × C => X e.1 e.2) (fun e => hX e.1 e.2)
        (fun e => hint e.1 e.2) (fun e => s e.1 * t e.2) (2 ^ k * p) (by positivity)
  have hmeas : Measurable (ThinMatrix.bilinear X s t) := by
    unfold ThinMatrix.bilinear
    fun_prop
  calc
    moment μ r (ThinMatrix.bilinear X s t)
        ≤ moment μ (2 ^ k * p) (ThinMatrix.bilinear X s t) :=
      MomentTools.mono_exponent_of_integrable r (2 ^ k * p) hr hrp _
        hmeas.aestronglyMeasurable hInt
    _ ≤ _ := bilinear_moment_doubling_pow X hX hind hsym hint α hα hregular s t k p hp

end MI32.BilinearHighOrder
