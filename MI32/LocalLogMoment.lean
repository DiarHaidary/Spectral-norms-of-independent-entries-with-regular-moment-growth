import MI32.LocalSymmetricMoment
import MI32.SymmetricLinearAllOrders
import MI32.VarianceScaleBasics
import MI32.WeakMomentBasics

/-!
# Local mean bounds at the exact logarithmic weak moment

The local matrix estimate is evaluated at `2 * ceil (2 * log (n + 1))`.
This order dominates the mean, keeps the dimension loss absolute, and is
at most eight times the requested logarithmic order, including `n = 1`.
Three proved scalar doublings supply the entire weak-moment comparison.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory

namespace MI32.LocalLogMoment

/-- The integer order used by the actual vacuum estimate. -/
def momentOrder (n : ℕ) : ℕ := ⌈2 * Real.log (n + 1 : ℕ)⌉₊

theorem log_two_le_log_dimension (n : ℕ) (hn : 1 ≤ n) :
    Real.log 2 ≤ Real.log (n + 1 : ℕ) := by
  apply Real.log_le_log (by norm_num)
  exact_mod_cast (show 2 ≤ n + 1 by omega)

theorem half_le_log_dimension (n : ℕ) (hn : 1 ≤ n) :
    (1 / 2 : ℝ) ≤ Real.log (n + 1 : ℕ) := by
  have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
  have hl := log_two_le_log_dimension n hn
  norm_num at h
  linarith

theorem one_le_momentOrder (n : ℕ) (hn : 1 ≤ n) : 1 ≤ momentOrder n := by
  apply Nat.one_le_ceil_iff.mpr
  have := half_le_log_dimension n hn
  linarith

theorem twice_momentOrder_le_eight_log (n : ℕ) (hn : 1 ≤ n) :
    2 * (momentOrder n : ℝ) ≤ 8 * Real.log (n + 1 : ℕ) := by
  have hp := half_le_log_dimension n hn
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ 2 * Real.log (n + 1 : ℕ) by linarith)
  change (momentOrder n : ℝ) < _ at hceil
  linarith

theorem dimension_factor_le_exp (n : ℕ) (hn : 1 ≤ n) :
    ((n + n : ℕ) : ℝ) ^ (1 / (2 * (momentOrder n : ℝ))) ≤ Real.exp 1 := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < ((n + n : ℕ) : ℝ) := by push_cast; linarith
  have hlog : Real.log ((n + n : ℕ) : ℝ) ≤ 2 * Real.log (n + 1 : ℕ) := by
    have h := Real.log_le_log hnpos
      (show ((n + n : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ 2 by push_cast; nlinarith)
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  have hq : 2 * Real.log (n + 1 : ℕ) ≤ (momentOrder n : ℝ) := Nat.le_ceil _
  have hqpos : (0 : ℝ) < (momentOrder n : ℝ) := by
    exact_mod_cast (show 0 < momentOrder n from one_le_momentOrder n hn)
  rw [Real.rpow_def_of_pos hnpos]
  apply Real.exp_le_exp.mpr
  have hdiv : Real.log ((n + n : ℕ) : ℝ) / (2 * (momentOrder n : ℝ)) ≤ 1 := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  simpa only [div_eq_mul_inv, one_div, one_mul] using hdiv

variable {Ω R C : Type*} [MeasurableSpace Ω] [Fintype R] [Fintype C]
    [DecidableEq R] [DecidableEq C] {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [MeasurableSpace Ω] [DecidableEq R] [DecidableEq C] in
/-- A bilinear test is one deterministic scalar linear form in the original
entries, with all original coordinate identities preserved. -/
theorem linearForm_eq_bilinear (X : R → C → Ω → ℝ)
    (s : EuclideanSpace ℝ R) (t : EuclideanSpace ℝ C) :
    SymmetricLinearRegularity.linearForm (fun e : R × C => X e.1 e.2)
      (fun e => s e.1 * t e.2) = ThinMatrix.bilinear X s t := by
  funext ω
  simp only [SymmetricLinearRegularity.linearForm, ThinMatrix.bilinear, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Three applications of the all-order scalar theorem control any smaller
positive order by eight times the original exact weak order. -/
theorem bilinear_moment_le_eight
    (X : R → C → Ω → ℝ) (hX : ∀ i j, Measurable (X i j))
    (hind : iIndepFun (fun e : R × C => X e.1 e.2) μ)
    (hsym : ∀ i j, IdentDistrib (X i j) (fun ω => -X i j ω) μ μ)
    (hint : ∀ i j (p : ℝ), 0 < p → Integrable (fun ω => |X i j ω| ^ p) μ)
    (α : ℝ) (hα : 1 ≤ α)
    (hregular : ∀ i j (r : ℝ), 1 ≤ r →
      moment μ (2 * r) (X i j) ≤ α * moment μ r (X i j))
    (s : EuclideanSpace ℝ R) (t : EuclideanSpace ℝ C)
    (p r : ℝ) (hp : Real.log 2 ≤ p) (hr : 0 < r) (hrp : r ≤ 8 * p) :
    moment μ r (ThinMatrix.bilinear X s t) ≤
      SymmetricLinearAllOrders.doublingConstant α ^ 3 *
        moment μ p (ThinMatrix.bilinear X s t) := by
  let J := SymmetricLinearAllOrders.doublingConstant α
  have hJ : 0 ≤ J := le_trans zero_le_one
    (SymmetricLinearAllOrders.one_le_doublingConstant α hα)
  have hp0 : 0 < p := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans_le hp
  have hdouble (u : ℝ) (hu : Real.log 2 ≤ u) :
      moment μ (2 * u) (ThinMatrix.bilinear X s t) ≤ J * moment μ u (ThinMatrix.bilinear X s t) := by
    simpa only [linearForm_eq_bilinear, J] using
      SymmetricLinearAllOrders.linear_root_doubling (fun e : R × C => X e.1 e.2)
        (fun e => hX e.1 e.2) hind (fun e => hsym e.1 e.2)
        (fun e => hint e.1 e.2) α hα (fun e => hregular e.1 e.2)
        (fun e => s e.1 * t e.2) u hu
  have hInt : Integrable (fun ω => |ThinMatrix.bilinear X s t ω| ^ (8 * p)) μ := by
    simpa only [linearForm_eq_bilinear] using
      SymmetricLinearRegularity.integrable_abs_rpow_linearForm
        (fun e : R × C => X e.1 e.2) (fun e => hX e.1 e.2)
        (fun e => hint e.1 e.2) (fun e => s e.1 * t e.2) (8 * p) (by positivity)
  have h1 := hdouble p hp
  have h2 := hdouble (2 * p) (by linarith)
  have h4 := hdouble (4 * p) (by linarith)
  have hmeas : Measurable (ThinMatrix.bilinear X s t) := by
    unfold ThinMatrix.bilinear
    fun_prop
  calc
    moment μ r (ThinMatrix.bilinear X s t) ≤ moment μ (8 * p) (ThinMatrix.bilinear X s t) :=
      MomentTools.mono_exponent_of_integrable r (8 * p) hr hrp _ hmeas.aestronglyMeasurable hInt
    _ ≤ J * moment μ (4 * p) (ThinMatrix.bilinear X s t) := by
      simpa only [show 2 * (4 * p) = 8 * p by ring] using h4
    _ ≤ J * (J * moment μ (2 * p) (ThinMatrix.bilinear X s t)) := by
      apply mul_le_mul_of_nonneg_left _ hJ
      simpa only [show 2 * (2 * p) = 4 * p by ring] using h2
    _ ≤ J * (J * (J * moment μ p (ThinMatrix.bilinear X s t))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 hJ) hJ
    _ = _ := by change _ = J ^ 3 * _; ring

/-- A positive even moment yields actual mean integrability and controls the
mean on the original probability space. -/
theorem integrable_and_mean_le_even_moment (f : Ω → ℝ) (hf : Measurable f)
    (hf0 : ∀ ω, 0 ≤ f ω) (q : ℕ) (hq : 1 ≤ q)
    (hInt : Integrable (fun ω => f ω ^ (2 * q)) μ) :
    Integrable f μ ∧ (∫ ω, f ω ∂μ) ≤ moment μ (2 * (q : ℝ)) f := by
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hIntR : Integrable (fun ω => |f ω| ^ (2 * (q : ℝ))) μ := by
    simpa only [show 2 * (q : ℝ) = ((2 * q : ℕ) : ℝ) by push_cast; rfl,
      Real.rpow_natCast, abs_of_nonneg (hf0 _)] using hInt
  have hm := MomentTools.memLp_of_integrable_abs_rpow (2 * (q : ℝ)) (by linarith)
    f hf.aestronglyMeasurable hIntR
  have hfi : Integrable f μ := hm.integrable (by
    simpa using ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ 2 * (q : ℝ) by linarith))
  refine ⟨hfi, ?_⟩
  have h := MomentTools.mono_exponent_of_integrable 1 (2 * (q : ℝ))
    (by norm_num) (by linarith) f hf.aestronglyMeasurable hIntR
  simpa only [moment, abs_of_nonneg (hf0 _), one_div_one, Real.rpow_one] using h

/-- The explicit prefactor in the local mean theorem. -/
def meanConstant (α : ℝ) : ℝ :=
  Real.exp 1 * 4 * (5 : ℝ) ^ (1 / 4 : ℝ) * (Real.sqrt 3 * α ^ 2)

theorem meanConstant_nonneg (α : ℝ) : 0 ≤ meanConstant α := by
  unfold meanConstant
  positivity

/-- Local mean bound for the actual square matrix, using only original-law
hypotheses and deterministic bilinear moments at exactly `log (n + 1)`.
The finite norm moment, scalar order comparisons, and integrability are all
derived, with no local matrix comparison among the input assumptions. -/
theorem mean_spectralNorm_le {n : ℕ} (hn : 1 ≤ n)
    (X : Fin n → Fin n → Ω → ℝ) (hX : ∀ i j, Measurable (X i j))
    (hind : iIndepFun (fun e : Fin n × Fin n => X e.1 e.2) μ)
    (hsym : ∀ i j, IdentDistrib (X i j) (fun ω => -X i j ω) μ μ)
    (hint : ∀ i j (p : ℝ), 0 < p → Integrable (fun ω => |X i j ω| ^ p) μ)
    (α : ℝ) (hα : 1 ≤ α)
    (hregular : ∀ i j (r : ℝ), 1 ≤ r →
      moment μ (2 * r) (X i j) ≤ α * moment μ r (X i j))
    (B : ℝ) (hB : 0 ≤ B)
    (hrow : ∀ i, (∑ j, ∫ ω, X i j ω ^ 2 ∂μ) ≤ B ^ 2)
    (hcol : ∀ j, (∑ i, ∫ ω, X i j ω ^ 2 ∂μ) ≤ B ^ 2)
    (W : ℝ) (hW : 0 ≤ W)
    (hweak : ∀ s : EuclideanSpace ℝ (Fin n), ‖s‖ ≤ 1 →
      ∀ t : EuclideanSpace ℝ (Fin n), ‖t‖ ≤ 1 →
        moment μ (Real.log (n + 1 : ℕ)) (ThinMatrix.bilinear X s t) ≤ W) :
    Integrable (fun ω => spectralNorm (fun i j => X i j ω)) μ ∧
      (∫ ω, spectralNorm (fun i j => X i j ω) ∂μ) ≤
        meanConstant α * (B + 6 * α ^ 4 *
          SymmetricLinearAllOrders.doublingConstant α ^ 3 * W) := by
  let J := SymmetricLinearAllOrders.doublingConstant α
  let q := momentOrder n
  let f : Ω → ℝ := fun ω => ‖BipartiteNorm.rectangular (fun e : Fin n × Fin n => X e.1 e.2 ω)‖
  have hq : 1 ≤ q := one_le_momentOrder n hn
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hJ : 0 ≤ J := le_trans zero_le_one
    (SymmetricLinearAllOrders.one_le_doublingConstant α hα)
  have hJW : 0 ≤ J ^ 3 * W := by positivity
  have hweak' : ∀ s : EuclideanSpace ℝ (Fin n), ‖s‖ ≤ 1 →
      ∀ t : EuclideanSpace ℝ (Fin n), ‖t‖ ≤ 1 →
        moment μ (2 * (q : ℝ)) (ThinMatrix.bilinear X s t) ≤ J ^ 3 * W := by
    intro s hs t ht
    calc
      _ ≤ J ^ 3 * moment μ (Real.log (n + 1 : ℕ)) (ThinMatrix.bilinear X s t) :=
        bilinear_moment_le_eight X hX hind hsym hint α hα hregular s t
          (Real.log (n + 1 : ℕ)) (2 * (q : ℝ))
          (log_two_le_log_dimension n hn) (by linarith)
          (twice_momentOrder_le_eight_log n hn)
      _ ≤ J ^ 3 * W := mul_le_mul_of_nonneg_left (hweak s hs t ht) (by positivity)
  obtain ⟨hInt, hBound⟩ := LocalSymmetricMoment.operator_moment_le
    X hX hind hsym hint α hα hregular q hq B hB hrow hcol (J ^ 3 * W) hJW hweak'
  have hf : Measurable f := BipartiteNorm.measurable_rectangular_norm X hX
  obtain ⟨hfi, hmean⟩ := integrable_and_mean_le_even_moment f hf (fun _ => norm_nonneg _) q hq hInt
  have hConstant : 0 ≤ RawMultiplicationContraction.contractionConstant α B (J ^ 3 * W) := by
    unfold RawMultiplicationContraction.contractionConstant
    positivity
  change Integrable f μ ∧ (∫ ω, f ω ∂μ) ≤ _
  refine ⟨hfi, hmean.trans ?_⟩
  calc
    moment μ (2 * (q : ℝ)) f ≤
        ((n + n : ℕ) : ℝ) ^ (1 / (2 * (q : ℝ))) *
          RawMultiplicationContraction.contractionConstant α B (J ^ 3 * W) := by
      simpa only [Fintype.card_fin] using hBound
    _ ≤ Real.exp 1 * RawMultiplicationContraction.contractionConstant α B (J ^ 3 * W) :=
      mul_le_mul_of_nonneg_right (dimension_factor_le_exp n hn) hConstant
    _ = meanConstant α * (B + 6 * α ^ 4 * J ^ 3 * W) := by
      unfold meanConstant RawMultiplicationContraction.contractionConstant
      ring

omit [MeasurableSpace Ω] in
/-- With no deleted indices, the literal statement observable is exactly the
same original bilinear form as in the local contraction theorem. -/
theorem bilinear_eq_deletedBilinear_empty {n : ℕ}
    (X : Ω → Matrix (Fin n) (Fin n) ℝ)
    (s t : EuclideanSpace ℝ (Fin n)) :
    ThinMatrix.bilinear (fun i j ω => X ω i j) s t = deletedBilinear X ∅ s t := by
  funext ω
  simp only [ThinMatrix.bilinear, deletedBilinear, Finset.sdiff_empty]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Literal-statement local theorem. Both variance and weak budgets are
derived from the original definitions, with the exact logarithmic weak
moment and no deleted indices. Symmetry is the only extra original-law
hypothesis beyond `RegularEntries`. -/
theorem mean_spectralNorm_le_literal {n : ℕ} (hn : 1 ≤ n)
    (X : Ω → Matrix (Fin n) (Fin n) ℝ) (α : ℝ) (hα : 1 ≤ α)
    (hReg : RegularEntries μ α X)
    (hsym : ∀ i j, IdentDistrib (fun ω => X ω i j) (fun ω => -X ω i j) μ μ) :
    Integrable (fun ω => spectralNorm (X ω)) μ ∧
      (∫ ω, spectralNorm (X ω) ∂μ) ≤ meanConstant α *
        (varianceScale μ X + 6 * α ^ 4 *
          SymmetricLinearAllOrders.doublingConstant α ^ 3 *
            weakMoment μ X ∅ (Real.log (n + 1 : ℕ))) := by
  rcases hReg with ⟨hX, hind, _, hint, hregular⟩
  apply mean_spectralNorm_le hn (fun i j ω => X ω i j)
    hX hind hsym hint α hα hregular
    (varianceScale μ X) (VarianceScaleBasics.varianceScale_nonneg X hn)
    (VarianceScaleBasics.row_variance_le_sq X)
    (VarianceScaleBasics.col_variance_le_sq X)
    (weakMoment μ X ∅ (Real.log (n + 1 : ℕ)))
    (WeakMomentBasics.weakMoment_nonneg μ X ∅ _)
  intro s hs t ht
  rw [bilinear_eq_deletedBilinear_empty]
  exact WeakMomentBasics.moment_le_weakMoment X hX hint ∅ _
    (WeakMomentBasics.log_budget_pos n hn) s t hs ht

end MI32.LocalLogMoment
