import MI32.HilbertComparison
import MI32.SymmetricLinearRegularity
import MI32.MatrixImages
import MI32.IndependentColumns
import MI32.ThinMomentRoot
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap

/-!
# Thin rectangular matrices under the original independent symmetric laws

The operator is the literal transpose action on Euclidean coordinate spaces.
The proof derives its fixed-vector comparison from the original entries and
then uses the constructed finite net. All weak tests are deterministic
bilinear forms in those same original entries.
-/

noncomputable section
open scoped BigOperators InnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory

namespace MI32.ThinMatrix

variable {Ω I J : Type*} [MeasurableSpace Ω] [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] {μ : Measure Ω}

/-- The actual rectangular transpose operator, with input indexed by the rows. -/
def transposeOperator (X : I → J → Ω → ℝ) (ω : Ω) :
    EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ J :=
  (Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap) (fun j i => X i j ω)

omit [MeasurableSpace Ω] [DecidableEq J] in
/-- Exact equality with the coordinate image used in the second-moment calculation. -/
theorem transposeOperator_apply (X : I → J → Ω → ℝ)
    (s : EuclideanSpace ℝ I) (ω : Ω) :
    transposeOperator X ω s = matrixRowImage X s ω := by
  change WithLp.toLp 2 (fun j => ∑ i, X i j ω * s i) =
    WithLp.toLp 2 (fun j => ∑ i, s i * X i j ω)
  simp only [mul_comm]

omit [DecidableEq J] in
@[fun_prop] theorem measurable_transposeOperator (X : I → J → Ω → ℝ)
    (hX : ∀ i j, Measurable (X i j)) : Measurable (transposeOperator X) := by
  let L : (J → I → ℝ) →ₗ[ℝ] (EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ J) :=
    (Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap).toLinearMap
  exact L.continuous_of_finiteDimensional.measurable.comp (by fun_prop)

omit [DecidableEq J] in
@[fun_prop] theorem measurable_norm_transposeOperator (X : I → J → Ω → ℝ)
    (hX : ∀ i j, Measurable (X i j)) : Measurable (fun ω => ‖transposeOperator X ω‖) :=
  (measurable_transposeOperator X hX).norm

/-- The original deterministic bilinear observable, with both original indices. -/
def bilinear (X : I → J → Ω → ℝ) (s : EuclideanSpace ℝ I)
    (t : EuclideanSpace ℝ J) (ω : Ω) : ℝ :=
  ∑ i, ∑ j, s i * X i j ω * t j

omit [MeasurableSpace Ω] [DecidableEq I] [DecidableEq J] in
theorem inner_matrixRowImage_eq_bilinear (X : I → J → Ω → ℝ)
    (s : EuclideanSpace ℝ I) (t : EuclideanSpace ℝ J) (ω : Ω) :
    ⟪t, matrixRowImage X s ω⟫_ℝ = bilinear X s t ω := by
  change (∑ j, (∑ i, s i * X i j ω) * t j) = _
  simp only [Finset.sum_mul, bilinear]
  exact Finset.sum_comm

omit [DecidableEq I] [DecidableEq J] in
theorem memLp_matrixRowImage (X : I → J → Ω → ℝ) (p : ℝ≥0∞)
    (hX : ∀ i j, MemLp (X i j) p μ) (s : I → ℝ) :
    MemLp (matrixRowImage X s) p μ := by
  apply memLp_piLp_iff.mpr
  intro j
  exact IndependentColumns.memLp_columnLinearForm X p hX s j

omit [DecidableEq I] [DecidableEq J] in
/-- Positive absolute moments give every positive natural norm-power integrability
needed for the operator net. This step needs neither symmetry nor independence. -/
theorem integrable_matrixRowImage_norm_pow
    (X : I → J → Ω → ℝ) (hX : ∀ i j, Measurable (X i j))
    (hint : ∀ i j (p : ℝ), 0 < p → Integrable (fun ω => |X i j ω| ^ p) μ)
    (s : I → ℝ) (p : ℕ) (hp : 1 ≤ p) :
    Integrable (fun ω => ‖matrixRowImage X s ω‖ ^ p) μ := by
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hp
  have hentry (i : I) (j : J) : MemLp (X i j) (p : ℝ≥0∞) μ := by
    simpa only [ENNReal.ofReal_natCast] using
      MomentTools.memLp_of_integrable_abs_rpow (p : ℝ) hpR (X i j)
        (hX i j).aestronglyMeasurable (hint i j p hpR)
  exact (memLp_matrixRowImage X p hentry s).integrable_norm_pow (by omega)

section Probability

variable [IsProbabilityMeasure μ]

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] [IsProbabilityMeasure μ] in
/-- Symmetry entails centering for the original scalar laws. -/
theorem integral_entry_eq_zero (X : I → J → Ω → ℝ)
    (hsym : ∀ i j, IdentDistrib (X i j) (fun ω => -X i j ω) μ μ) (i : I) (j : J) :
    (∫ ω, X i j ω ∂μ) = 0 := by
  have h := (hsym i j).integral_eq
  rw [integral_neg] at h
  linarith

omit [DecidableEq J] in
/-- A fixed deterministic unit row vector incurs the original row variance
budget and the original bilinear weak moment, with no dimension loss. -/
theorem matrixRowImage_moment_four_mul_le
    (X : I → J → Ω → ℝ) (hX : ∀ i j, Measurable (X i j))
    (hind : iIndepFun (fun e : I × J => X e.1 e.2) μ)
    (hsym : ∀ i j, IdentDistrib (X i j) (fun ω => -X i j ω) μ μ)
    (hint : ∀ i j (p : ℝ), 0 < p → Integrable (fun ω => |X i j ω| ^ p) μ)
    (α : ℝ) (hα : 1 ≤ α)
    (hregular : ∀ i j (r : ℝ), 1 ≤ r →
      moment μ (2 * r) (X i j) ≤ α * moment μ r (X i j))
    (q : ℕ) (hq : 1 ≤ q) (B : ℝ) (hB : 0 ≤ B)
    (hrow : ∀ i, (∑ j, ∫ ω, X i j ω ^ 2 ∂μ) ≤ B ^ 2)
    (R : ℝ) (hR : 0 ≤ R)
    (hweak : ∀ s : EuclideanSpace ℝ I, ‖s‖ ≤ 1 →
      ∀ t : EuclideanSpace ℝ J, ‖t‖ ≤ 1 →
        moment μ (2 * (q : ℝ)) (bilinear X s t) ≤ R)
    (s : EuclideanSpace ℝ I) (hs : ‖s‖ ≤ 1) :
    moment μ (4 * (q : ℝ)) (fun ω => ‖matrixRowImage X s ω‖) ≤
      B + 6 * α ^ 4 * R := by
  have hVpow (j : J) (n : ℕ) :
      Integrable (fun ω => IndependentColumns.columnLinearForm X s j ω ^ n) μ :=
    SymmetricLinearRegularity.integrable_pow_linearForm
      (fun i => X i j) (fun i => hX i j) (fun i => hint i j) s n
  have hVregular (j : J) (r : ℕ) (hr : 1 ≤ r) :
      moment μ (4 * r : ℕ) (IndependentColumns.columnLinearForm X s j) ≤
        (Real.sqrt 3 * α ^ 2) *
          moment μ (2 * r : ℕ) (IndependentColumns.columnLinearForm X s j) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      SymmetricLinearRegularity.columnLinearForm_even_root_doubling X hX hind hsym hint
        α hα hregular s j r hr
  have hVweak (t : EuclideanSpace ℝ J) (ht : ‖t‖ ≤ 1) :
      moment μ (2 * q : ℕ) (fun ω =>
        ⟪t, WithLp.toLp 2 (fun j => IndependentColumns.columnLinearForm X s j ω)⟫_ℝ) ≤ R := by
    change moment μ (2 * q : ℕ) (fun ω => ⟪t, matrixRowImage X s ω⟫_ℝ) ≤ R
    simp_rw [inner_matrixRowImage_eq_bilinear]
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hweak s hs t ht
  have hcompare := HilbertComparison.independent_coordinate_moment_le
    (IndependentColumns.columnLinearForm X s)
    (IndependentColumns.measurable_columnLinearForm X hX s)
    (IndependentColumns.independent_columnLinearForm X hX hind s)
    (IndependentColumns.symmetric_columnLinearForm X hind hsym s)
    hVpow (Real.sqrt 3 * α ^ 2) hVregular q hq R hR hVweak
  change moment μ (4 * q : ℕ) (fun ω => ‖matrixRowImage X s ω‖) ≤
    Real.sqrt (∫ ω, ‖matrixRowImage X s ω‖ ^ 2 ∂μ) +
      2 * (Real.sqrt 3 * α ^ 2) ^ 2 * R at hcompare
  have hentry2 (i : I) (j : J) : MemLp (X i j) 2 μ := by
    simpa using MomentTools.memLp_of_integrable_abs_rpow 2 (by norm_num) (X i j)
      (hX i j).aestronglyMeasurable (hint i j 2 (by norm_num))
  have hs2 : ∑ i, s i ^ 2 ≤ 1 := by
    rw [← EuclideanSpace.real_norm_sq_eq]
    nlinarith [norm_nonneg s]
  have hsecond : (∫ ω, ‖matrixRowImage X s ω‖ ^ 2 ∂μ) ≤ B ^ 2 := by
    simp_rw [matrixRowImage_norm_sq]
    exact integral_matrix_image_sq_le X hentry2 hind (integral_entry_eq_zero X hsym)
      s hs2 (B ^ 2) (sq_nonneg B) hrow
  have hroot : Real.sqrt (∫ ω, ‖matrixRowImage X s ω‖ ^ 2 ∂μ) ≤ B := by
    simpa only [Real.sqrt_sq hB] using Real.sqrt_le_sqrt hsecond
  have hconstant : 2 * (Real.sqrt 3 * α ^ 2) ^ 2 = 6 * α ^ 4 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    ring
  rw [hconstant] at hcompare
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hcompare
  linarith

omit [DecidableEq J] in
/-- The actual thin rectangular operator estimate. All hypotheses refer to
the original independent symmetric entries, their scalar regularity, the row
variance budget, and deterministic bilinear tests. Integrability is derived.
The only dimension restriction is on the row/input index set. -/
theorem transposeOperator_moment_four_mul_le
    (X : I → J → Ω → ℝ) (hX : ∀ i j, Measurable (X i j))
    (hind : iIndepFun (fun e : I × J => X e.1 e.2) μ)
    (hsym : ∀ i j, IdentDistrib (X i j) (fun ω => -X i j ω) μ μ)
    (hint : ∀ i j (p : ℝ), 0 < p → Integrable (fun ω => |X i j ω| ^ p) μ)
    (α : ℝ) (hα : 1 ≤ α)
    (hregular : ∀ i j (r : ℝ), 1 ≤ r →
      moment μ (2 * r) (X i j) ≤ α * moment μ r (X i j))
    (q : ℕ) (hq : 1 ≤ q) (hthin : Fintype.card I ≤ q)
    (B : ℝ) (hB : 0 ≤ B)
    (hrow : ∀ i, (∑ j, ∫ ω, X i j ω ^ 2 ∂μ) ≤ B ^ 2)
    (R : ℝ) (hR : 0 ≤ R)
    (hweak : ∀ s : EuclideanSpace ℝ I, ‖s‖ ≤ 1 →
      ∀ t : EuclideanSpace ℝ J, ‖t‖ ≤ 1 →
        moment μ (2 * (q : ℝ)) (bilinear X s t) ≤ R) :
    Integrable (fun ω => ‖transposeOperator X ω‖ ^ (4 * q)) μ ∧
      moment μ (4 * (q : ℝ)) (fun ω => ‖transposeOperator X ω‖) ≤
        (2 : ℝ) * (5 : ℝ) ^ (1 / 4 : ℝ) * (B + 6 * α ^ 4 * R) := by
  apply ThinMomentRoot.opNorm_moment_four_mul_le_of_images μ (transposeOperator X)
    (measurable_norm_transposeOperator X hX) q hq
    (by simpa only [finrank_euclideanSpace] using hthin)
  · intro s _
    simp_rw [transposeOperator_apply]
    exact integrable_matrixRowImage_norm_pow X hX hint s (4 * q) (by omega)
  · exact add_nonneg hB (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg (by linarith) _)) hR)
  · intro s hs
    simp_rw [transposeOperator_apply]
    exact matrixRowImage_moment_four_mul_le X hX hind hsym hint α hα hregular
      q hq B hB hrow R hR hweak s hs

end Probability

end MI32.ThinMatrix
