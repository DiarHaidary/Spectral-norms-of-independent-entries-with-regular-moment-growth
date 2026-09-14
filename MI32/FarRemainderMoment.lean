import MI32.GramEntryMoments
import MI32.GradedVarianceEnergy
import MI32.CenteredGramNorm

/-!
# The far remainder: mean operator norm from a graded variance cap

The far part of the deletion decomposition is estimated without any general
variance-envelope matrix theorem. Only three already-established ingredients
are used:

* `GradedVarianceEnergy.total_energy_le_two`, a deterministic statement about
  the second moments `v i j = ∫ (Y i j)^2` alone, which turns the graded
  support cap and the geometric column budgets into the ordered-pair variance
  overlap bound `∑ j, ∑ k, ∑ i, v i j * v i k ≤ 2 * B^4`;
* `GramEntryMoments.total_centeredGram_energy_le`, the single genuinely
  probabilistic step, which converts that deterministic overlap into the total
  second moment of the centered Gram entries at the cost of `α^4`;
* `CenteredGramNorm.mean_norm_le`, which converts a centered Gram energy bound
  into a bound on the mean Euclidean operator norm.

The composition plus one square-root factorisation gives the mean operator
norm bound `B * √(1 + √2 * α^2)`: an absolute multiple of the variance scale
`B`, with no dimensional factor. The transposed statement is available through
`norm_transpose_eq`, so the same theorem covers the upper far orientation when
applied to the transposed family.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open MeasureTheory

namespace MI32.FarRemainderMoment

variable {Ω R C : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [Fintype R] [Fintype C] [DecidableEq R] [DecidableEq C] {L : ℕ}

/-- Over the reals the transpose is an isometry for the Euclidean operator norm. -/
theorem norm_transpose_eq (A : Matrix R C ℝ) : ‖A.transpose‖ = ‖A‖ := by
  rw [← Matrix.conjTranspose_eq_transpose_of_trivial A]
  exact Matrix.l2_opNorm_conjTranspose A

/-- The square of the intermediate Gram scale `√2 * α^2 * B^2`. -/
theorem gram_scale_sq (α B : ℝ) :
    (Real.sqrt 2 * α ^ 2 * B ^ 2) ^ 2 = α ^ 4 * (2 * B ^ 4) := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [mul_pow, mul_pow, h2]
  ring

/-- The square-root factorisation that produces the final absolute constant. -/
theorem sqrt_scale_eq (α B : ℝ) (hB : 0 ≤ B) :
    Real.sqrt (B ^ 2 + Real.sqrt 2 * α ^ 2 * B ^ 2)
      = B * Real.sqrt (1 + Real.sqrt 2 * α ^ 2) := by
  rw [show B ^ 2 + Real.sqrt 2 * α ^ 2 * B ^ 2 = B ^ 2 * (1 + Real.sqrt 2 * α ^ 2) by ring,
    Real.sqrt_mul (sq_nonneg B), Real.sqrt_sq hB]

/-- The far remainder estimate. Only original independence, centering, the
regular fourth-moment budget, the surviving column budget and the graded
variance cap are used; no general matrix comparison theorem is assumed. -/
theorem mean_norm_le_of_graded
    (Y : R → C → Ω → ℝ) (hY : ∀ i j, Measurable (Y i j))
    (hind : ProbabilityTheory.iIndepFun (fun e : R × C => Y e.1 e.2) μ)
    (hmean : ∀ i j, (∫ ω, Y i j ω ∂μ) = 0)
    (hint : ∀ i j (p : ℝ), 0 < p → Integrable (fun ω => |Y i j ω| ^ p) μ)
    (α B : ℝ) (hα : 1 ≤ α) (hB : 0 ≤ B)
    (hfour : ∀ i j, (∫ ω, Y i j ω ^ 4 ∂μ) ≤ α ^ 4 * (∫ ω, Y i j ω ^ 2 ∂μ) ^ 2)
    (hcol : ∀ j, (∑ i, ∫ ω, Y i j ω ^ 2 ∂μ) ≤ B ^ 2)
    (label : C → Fin L) (b : Fin L → ℕ)
    (hcard : ∀ r, (GradedVarianceEnergy.columnsThrough label r).card ≤ b r)
    (hgrowth : ∀ r, 2 ^ r.val ≤ b r)
    (hcap : ∀ i j k, label j ≤ label k → (∫ ω, Y i k ω ^ 2 ∂μ) ≠ 0 →
      (∫ ω, Y i j ω ^ 2 ∂μ) ≤ B ^ 2 / ((b (label k) : ℝ) ^ 3 + 1)) :
    Integrable (fun ω => ‖(Matrix.of (fun i j => Y i j ω) : Matrix R C ℝ)‖) μ ∧
      (∫ ω, ‖(Matrix.of (fun i j => Y i j ω) : Matrix R C ℝ)‖ ∂μ)
        ≤ B * Real.sqrt (1 + Real.sqrt 2 * α ^ 2) := by
  -- The deterministic second moments of the entries.
  have hvnn : ∀ (i : R) (j : C), 0 ≤ ∫ ω, Y i j ω ^ 2 ∂μ :=
    fun _i _j => integral_nonneg fun _ω => sq_nonneg _
  -- Step 1: the deterministic graded variance overlap.
  have hEnergy :
      (∑ j, ∑ k, ∑ i, (∫ ω, Y i j ω ^ 2 ∂μ) * (∫ ω, Y i k ω ^ 2 ∂μ)) ≤ 2 * B ^ 4 :=
    GradedVarianceEnergy.total_energy_le_two (fun i j => ∫ ω, Y i j ω ^ 2 ∂μ)
      hvnn B hcol label b hcard hgrowth hcap
  -- Step 2: the probabilistic centered Gram energy.
  have hGram := GramEntryMoments.total_centeredGram_energy_le
    (μ := μ) (Y := Y) hY hind hmean hint α hα hfour (2 * B ^ 4) hEnergy
  -- The deterministic diagonal is bounded by the column budget.
  have hd : ∀ j : C, |∑ i, ∫ ω, Y i j ω ^ 2 ∂μ| ≤ B ^ 2 := by
    intro j
    rw [abs_of_nonneg (Finset.sum_nonneg fun i _ => hvnn i j)]
    exact hcol j
  have hBound : (∑ j, ∑ k, ∫ ω, CenteredGramNorm.centeredGram
        (Matrix.of (fun i j => Y i j ω) : Matrix R C ℝ)
        (fun j => ∑ i, ∫ ω', Y i j ω' ^ 2 ∂μ) j k ^ 2 ∂μ)
      ≤ (Real.sqrt 2 * α ^ 2 * B ^ 2) ^ 2 := by
    rw [gram_scale_sq]
    exact hGram
  -- Step 3: the operator mean from the centered Gram energy.
  obtain ⟨hInt, hMean⟩ := CenteredGramNorm.mean_norm_le (μ := μ)
    (fun ω => (Matrix.of (fun i j => Y i j ω) : Matrix R C ℝ))
    (fun i j => hY i j) (fun j => ∑ i, ∫ ω, Y i j ω ^ 2 ∂μ) B hd
    (fun j k => GramEntryMoments.integrable_centeredGram_sq hY hint j k)
    (Real.sqrt 2 * α ^ 2 * B ^ 2) (by positivity) hBound
  -- Step 4: the square-root algebra.
  exact ⟨hInt, hMean.trans (le_of_eq (sqrt_scale_eq α B hB))⟩

end MI32.FarRemainderMoment
