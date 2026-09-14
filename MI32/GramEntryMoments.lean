import MI32.CenteredGramNorm
import MI32.MatrixImages
import MI32.IndependentColumns
import MI32.MomentTools

/-!
# Centered Gram second moments of an independent centered family

This is the only genuinely probabilistic ingredient of the far remainder
estimate. No matrix operator norm occurs; every statement below is an integral
of entries of the original family `Y`.

Two exact second moments are computed. For two distinct original columns the
Gram entry `∑ i, Y i j * Y i k` is a sum of independent centered products, so
its second moment is exactly the variance overlap `∑ i, w i j * w i k`, where
`w i j = ∫ (Y i j)^2`. For a single original column the centered squared sum
`∑ i, ((Y i j)^2 - w i j)` has second moment `∑ i, (∫ (Y i j)^4 - (w i j)^2)`,
which the regular fourth-moment budget bounds by `α^4 * ∑ i, (w i j)^2`.

Independence in the row index is derived from the joint law of the original
ordered-pair coordinates through `IndependentColumns.independent_column_vectors`
applied to the transposed family; no separate row law is imposed.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace MI32.GramEntryMoments

/-- Second moment of a centered variable: an algebraic identity on a
probability space, with both integrability hypotheses explicit. -/
theorem integral_sub_mean_sq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (f : Ω → ℝ) (hf : Integrable f μ)
    (hf2 : Integrable (fun ω => f ω ^ 2) μ) :
    (∫ ω, (f ω - ∫ η, f η ∂μ) ^ 2 ∂μ)
      = (∫ ω, f ω ^ 2 ∂μ) - (∫ ω, f ω ∂μ) ^ 2 := by
  have hi1 : Integrable (fun ω => f ω ^ 2 - (2 * (∫ η, f η ∂μ)) * f ω) μ :=
    hf2.sub (hf.const_mul _)
  have hrw : (fun ω => (f ω - ∫ η, f η ∂μ) ^ 2)
      = fun ω => (f ω ^ 2 - (2 * (∫ η, f η ∂μ)) * f ω) + (∫ η, f η ∂μ) ^ 2 := by
    funext ω; ring
  have hconst : (∫ _ω : Ω, ((∫ η, f η ∂μ) ^ 2) ∂μ) = (∫ η, f η ∂μ) ^ 2 := by simp
  rw [hrw, integral_add hi1 (integrable_const _), hconst,
    integral_sub hf2 (hf.const_mul _), integral_const_mul]
  ring

/-- The entries of a centered Gram matrix, for an arbitrary rectangular matrix
and an arbitrary deterministic diagonal. -/
theorem centeredGram_entry {R C : Type*} [Fintype R] [DecidableEq C]
    (A : Matrix R C ℝ) (d : C → ℝ) (j k : C) :
    CenteredGramNorm.centeredGram A d j k
      = (∑ i, A i j * A i k) - (if j = k then d j else 0) := by
  simp only [CenteredGramNorm.centeredGram, Matrix.sub_apply, Matrix.mul_apply,
    Matrix.transpose_apply, Matrix.diagonal_apply]

variable {Ω R C : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {Y : R → C → Ω → ℝ}
    (hY : ∀ i j, Measurable (Y i j))
    (hind : iIndepFun (fun e : R × C => Y e.1 e.2) μ)
    (hmean : ∀ i j, (∫ ω, Y i j ω ∂μ) = 0)
    (hint : ∀ i j (p : ℝ), 0 < p → Integrable (fun ω => |Y i j ω| ^ p) μ)

section Moments

include hY hint

/-- Every entry lies in every finite `Lp` class of positive exponent. -/
theorem entry_memLp (i : R) (j : C) (p : ℝ) (hp : 0 < p) :
    MemLp (Y i j) (ENNReal.ofReal p) μ :=
  MomentTools.memLp_of_integrable_abs_rpow p hp _
    (hY i j).aestronglyMeasurable (hint i j p hp)

/-- Square integrability of every entry. -/
theorem entry_memLp_two (i : R) (j : C) : MemLp (Y i j) 2 μ := by
  have h := entry_memLp hY hint i j 2 (by norm_num)
  rwa [show ENNReal.ofReal (2 : ℝ) = 2 by simp] at h

/-- Fourth-power integrability of every entry. -/
theorem entry_memLp_four (i : R) (j : C) : MemLp (Y i j) 4 μ := by
  have h := entry_memLp hY hint i j 4 (by norm_num)
  rwa [show ENNReal.ofReal (4 : ℝ) = 4 by simp] at h

/-- The squared entries are themselves square integrable. -/
theorem sq_memLp_two (i : R) (j : C) : MemLp (fun ω => Y i j ω ^ 2) 2 μ := by
  have h := MomentTools.memLp_square 2 (by norm_num) (Y i j)
    (by rw [show (2 : ℝ) * 2 = 4 by norm_num,
          show ENNReal.ofReal (4 : ℝ) = 4 by simp]
        exact entry_memLp_four hY hint i j)
  rwa [show ENNReal.ofReal (2 : ℝ) = 2 by simp] at h

/-- Second moments of the entries are finite. -/
theorem integrable_sq (i : R) (j : C) : Integrable (fun ω => Y i j ω ^ 2) μ :=
  (entry_memLp_two hY hint i j).integrable_sq

/-- Fourth moments of the entries are finite. -/
theorem integrable_pow_four (i : R) (j : C) :
    Integrable (fun ω => Y i j ω ^ 4) μ := by
  have h := (sq_memLp_two hY hint i j).integrable_sq
  simpa only [← pow_mul] using h

/-- Any product of two entries taken from the same row is square integrable. -/
theorem prod_memLp_two (i : R) (j k : C) :
    MemLp (fun ω => Y i j ω * Y i k ω) 2 μ := by
  have hm : Measurable (fun ω => Y i j ω * Y i k ω) := (hY i j).mul (hY i k)
  refine (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr ?_
  have h := (sq_memLp_two hY hint i j).integrable_mul (sq_memLp_two hY hint i k)
  refine h.congr ?_
  filter_upwards with ω
  simp only [Pi.mul_apply]
  ring

end Moments

section Independence

include hY hind

/-- Entire rows of the original family are jointly independent as vectors.
This is a consequence of the joint law of the ordered-pair coordinates, not a
separately imposed row law. -/
theorem independent_rows :
    iIndepFun (fun (i : R) (ω : Ω) => fun j : C => Y i j ω) μ :=
  IndependentColumns.independent_column_vectors (fun (a : C) (b : R) => Y b a)
    (fun a b => hY b a) (hind.precomp Prod.swap_injective)

/-- Products of two entries taken from a fixed pair of columns are independent
across rows. -/
theorem indepFun_prod_rows (j k : C) :
    Pairwise (fun i i' =>
      IndepFun (fun ω => Y i j ω * Y i k ω) (fun ω => Y i' j ω * Y i' k ω) μ) := by
  have h := (independent_rows hY hind).comp
    (fun _ : R => fun x : C → ℝ => x j * x k) (fun _ => by fun_prop)
  intro i i' hii
  exact h.indepFun hii

/-- Centered squares from a fixed column are independent across rows. The
centering constants are allowed to depend on the row. -/
theorem indepFun_centered_sq_rows (j : C) (c : R → ℝ) :
    Pairwise (fun i i' =>
      IndepFun (fun ω => Y i j ω ^ 2 - c i) (fun ω => Y i' j ω ^ 2 - c i') μ) := by
  have h := (independent_rows hY hind).comp
    (fun i : R => fun x : C → ℝ => x j ^ 2 - c i) (fun _ => by fun_prop)
  intro i i' hii
  exact h.indepFun hii

/-- Two entries in the same row and distinct columns have a product mean equal
to the product of their means. -/
theorem integral_prod_eq (i : R) (j k : C) (hjk : j ≠ k) :
    (∫ ω, Y i j ω * Y i k ω ∂μ) = (∫ ω, Y i j ω ∂μ) * ∫ ω, Y i k ω ∂μ :=
  (hind.indepFun (i := (i, j)) (j := (i, k))
      (by simpa using hjk)).integral_fun_mul_eq_mul_integral
    (hY i j).aestronglyMeasurable (hY i k).aestronglyMeasurable

/-- The same product rule for the squared entries. -/
theorem integral_prod_sq_eq (i : R) (j k : C) (hjk : j ≠ k) :
    (∫ ω, Y i j ω ^ 2 * Y i k ω ^ 2 ∂μ)
      = (∫ ω, Y i j ω ^ 2 ∂μ) * ∫ ω, Y i k ω ^ 2 ∂μ := by
  have hpair : IndepFun (Y i j) (Y i k) μ :=
    hind.indepFun (i := (i, j)) (j := (i, k)) (by simpa using hjk)
  have hsq := hpair.comp (φ := fun x : ℝ => x ^ 2) (ψ := fun x : ℝ => x ^ 2)
    (measurable_id.pow_const 2) (measurable_id.pow_const 2)
  have h := hsq.integral_fun_mul_eq_mul_integral
    ((hY i j).pow_const 2).aestronglyMeasurable
    ((hY i k).pow_const 2).aestronglyMeasurable
  simpa only [Function.comp_def] using h

end Independence

section OffDiagonal

variable [Fintype R]

include hY hind hmean hint

/-- Distinct original columns: the off-diagonal Gram entry is a sum of
independent centered products, so its second moment is the variance overlap. -/
theorem integral_column_product_sq (j k : C) (hjk : j ≠ k) :
    (∫ ω, (∑ i, Y i j ω * Y i k ω) ^ 2 ∂μ)
      = ∑ i, (∫ ω, Y i j ω ^ 2 ∂μ) * (∫ ω, Y i k ω ^ 2 ∂μ) := by
  have hzero (i : R) : (∫ ω, Y i j ω * Y i k ω ∂μ) = 0 := by
    rw [integral_prod_eq hY hind i j k hjk, hmean i j, zero_mul]
  have h := MI32.integral_linear_sum_sq (μ := μ) (fun i ω => Y i j ω * Y i k ω)
    (fun i => prod_memLp_two hY hint i j k) (indepFun_prod_rows hY hind j k)
    hzero (fun _ => 1)
  simp only [one_mul, one_pow] at h
  rw [h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← integral_prod_sq_eq hY hind i j k hjk]
  congr 1
  funext ω
  ring

end OffDiagonal

section Diagonal

variable [Fintype R] [IsProbabilityMeasure μ]

include hY hind hint

/-- A single original column: the centered squared-sum second moment is given
by the fourth moments, hence at most the regular fourth-moment budget. -/
theorem integral_centered_square_sum_sq (α : ℝ)
    (hfour : ∀ i j, (∫ ω, Y i j ω ^ 4 ∂μ) ≤ α ^ 4 * (∫ ω, Y i j ω ^ 2 ∂μ) ^ 2)
    (j : C) :
    (∫ ω, (∑ i, (Y i j ω ^ 2 - ∫ ω', Y i j ω' ^ 2 ∂μ)) ^ 2 ∂μ)
      ≤ α ^ 4 * ∑ i, (∫ ω, Y i j ω ^ 2 ∂μ) ^ 2 := by
  have hmemc (i : R) :
      MemLp (fun ω => Y i j ω ^ 2 - ∫ ω', Y i j ω' ^ 2 ∂μ) 2 μ :=
    (sq_memLp_two hY hint i j).sub (memLp_const _)
  have hzero (i : R) : (∫ ω, (Y i j ω ^ 2 - ∫ ω', Y i j ω' ^ 2 ∂μ) ∂μ) = 0 := by
    rw [integral_sub (integrable_sq hY hint i j) (integrable_const _)]
    simp
  have hexact := MI32.integral_linear_sum_sq (μ := μ)
    (fun i ω => Y i j ω ^ 2 - ∫ ω', Y i j ω' ^ 2 ∂μ) hmemc
    (indepFun_centered_sq_rows hY hind j (fun i => ∫ ω', Y i j ω' ^ 2 ∂μ))
    hzero (fun _ => 1)
  simp only [one_mul, one_pow] at hexact
  rw [hexact]
  have hterm (i : R) :
      (∫ ω, (Y i j ω ^ 2 - ∫ ω', Y i j ω' ^ 2 ∂μ) ^ 2 ∂μ)
        ≤ α ^ 4 * (∫ ω, Y i j ω ^ 2 ∂μ) ^ 2 := by
    have hid : (∫ ω, (Y i j ω ^ 2 - ∫ ω', Y i j ω' ^ 2 ∂μ) ^ 2 ∂μ)
        = (∫ ω, Y i j ω ^ 4 ∂μ) - (∫ ω, Y i j ω ^ 2 ∂μ) ^ 2 := by
      have h := integral_sub_mean_sq (μ := μ) (fun ω => Y i j ω ^ 2)
        (integrable_sq hY hint i j) ((sq_memLp_two hY hint i j).integrable_sq)
      rw [h]
      congr 1
      exact integral_congr_ae (Filter.Eventually.of_forall fun ω => by ring)
    rw [hid]
    nlinarith [hfour i j, sq_nonneg (∫ ω, Y i j ω ^ 2 ∂μ)]
  calc
    (∑ i, ∫ ω, (Y i j ω ^ 2 - ∫ ω', Y i j ω' ^ 2 ∂μ) ^ 2 ∂μ)
        ≤ ∑ i, α ^ 4 * (∫ ω, Y i j ω ^ 2 ∂μ) ^ 2 :=
      Finset.sum_le_sum fun i _ => hterm i
    _ = α ^ 4 * ∑ i, (∫ ω, Y i j ω ^ 2 ∂μ) ^ 2 := by rw [Finset.mul_sum]

end Diagonal

section GramEntries

variable [Fintype R] [DecidableEq C]

/-- The exact entries of the centered Gram matrix in the original coordinates. -/
theorem centeredGram_apply (ω : Ω) (j k : C) :
    CenteredGramNorm.centeredGram (fun i j => Y i j ω)
        (fun j => ∑ i, ∫ ω', Y i j ω' ^ 2 ∂μ) j k
      = (∑ i, Y i j ω * Y i k ω)
        - (if j = k then ∑ i, ∫ ω', Y i j ω' ^ 2 ∂μ else 0) :=
  centeredGram_entry _ _ j k

/-- The diagonal centered Gram entry is the centered squared sum of a column. -/
theorem centeredGram_apply_diag (ω : Ω) (j : C) :
    CenteredGramNorm.centeredGram (fun i j => Y i j ω)
        (fun j => ∑ i, ∫ ω', Y i j ω' ^ 2 ∂μ) j j
      = ∑ i, (Y i j ω ^ 2 - ∫ ω', Y i j ω' ^ 2 ∂μ) := by
  rw [centeredGram_apply, if_pos rfl, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← pow_two]

/-- The off-diagonal centered Gram entry carries no deterministic correction. -/
theorem centeredGram_apply_offdiag (ω : Ω) (j k : C) (hjk : j ≠ k) :
    CenteredGramNorm.centeredGram (fun i j => Y i j ω)
        (fun j => ∑ i, ∫ ω', Y i j ω' ^ 2 ∂μ) j k
      = ∑ i, Y i j ω * Y i k ω := by
  rw [centeredGram_apply, if_neg hjk, sub_zero]

end GramEntries

section GramIntegrability

variable [Fintype R] [DecidableEq C] [IsProbabilityMeasure μ]

include hY hint

/-- Every centered Gram entry lies in `L²`. -/
theorem memLp_centeredGram_two (j k : C) :
    MemLp (fun ω => CenteredGramNorm.centeredGram (fun i j => Y i j ω)
      (fun j => ∑ i, ∫ ω', Y i j ω' ^ 2 ∂μ) j k) 2 μ := by
  have hrw : (fun ω => CenteredGramNorm.centeredGram (fun i j => Y i j ω)
      (fun j => ∑ i, ∫ ω', Y i j ω' ^ 2 ∂μ) j k)
      = fun ω => (∑ i, Y i j ω * Y i k ω)
        - (if j = k then ∑ i, ∫ ω', Y i j ω' ^ 2 ∂μ else 0) := by
    funext ω
    exact centeredGram_apply ω j k
  rw [hrw]
  exact (memLp_finsetSum _ fun i _ => prod_memLp_two hY hint i j k).sub
    (memLp_const _)

/-- Every centered Gram entry is square integrable. -/
theorem integrable_centeredGram_sq (j k : C) :
    Integrable (fun ω => CenteredGramNorm.centeredGram (fun i j => Y i j ω)
      (fun j => ∑ i, ∫ ω', Y i j ω' ^ 2 ∂μ) j k ^ 2) μ :=
  (memLp_centeredGram_two hY hint j k).integrable_sq

end GramIntegrability

section TotalEnergy

variable [Fintype R] [DecidableEq C] [IsProbabilityMeasure μ]

include hY hind hmean hint

/-- Every centered Gram entry has second moment at most `α^4` times the
corresponding variance overlap. The diagonal is charged to the same expression
because the regularity constant is at least one. -/
theorem integral_centeredGram_sq_le (α : ℝ) (hα : 1 ≤ α)
    (hfour : ∀ i j, (∫ ω, Y i j ω ^ 4 ∂μ) ≤ α ^ 4 * (∫ ω, Y i j ω ^ 2 ∂μ) ^ 2)
    (j k : C) :
    (∫ ω, CenteredGramNorm.centeredGram (fun i j => Y i j ω)
        (fun j => ∑ i, ∫ ω', Y i j ω' ^ 2 ∂μ) j k ^ 2 ∂μ)
      ≤ α ^ 4 * ∑ i, (∫ ω, Y i j ω ^ 2 ∂μ) * (∫ ω, Y i k ω ^ 2 ∂μ) := by
  have hone : (1 : ℝ) ≤ α ^ 4 := one_le_pow₀ hα
  by_cases hjk : j = k
  · subst hjk
    have hrw : (fun ω => CenteredGramNorm.centeredGram (fun i j => Y i j ω)
        (fun j => ∑ i, ∫ ω', Y i j ω' ^ 2 ∂μ) j j ^ 2)
        = fun ω => (∑ i, (Y i j ω ^ 2 - ∫ ω', Y i j ω' ^ 2 ∂μ)) ^ 2 := by
      funext ω
      rw [centeredGram_apply_diag]
    rw [hrw]
    refine (integral_centered_square_sum_sq hY hind hint α hfour j).trans ?_
    refine mul_le_mul_of_nonneg_left (le_of_eq ?_) (by positivity)
    exact Finset.sum_congr rfl fun i _ => pow_two _
  · have hrw : (fun ω => CenteredGramNorm.centeredGram (fun i j => Y i j ω)
        (fun j => ∑ i, ∫ ω', Y i j ω' ^ 2 ∂μ) j k ^ 2)
        = fun ω => (∑ i, Y i j ω * Y i k ω) ^ 2 := by
      funext ω
      rw [centeredGram_apply_offdiag ω j k hjk]
    rw [hrw, integral_column_product_sq hY hind hmean hint j k hjk]
    have hnn : (0 : ℝ) ≤ ∑ i, (∫ ω, Y i j ω ^ 2 ∂μ) * (∫ ω, Y i k ω ^ 2 ∂μ) :=
      Finset.sum_nonneg fun i _ => mul_nonneg
        (integral_nonneg fun _ω => sq_nonneg _)
        (integral_nonneg fun _ω => sq_nonneg _)
    nlinarith

variable [Fintype C]

/-- Total centered Gram energy from the deterministic variance overlaps. The
diagonal is charged to the same triple sum because the regularity constant is
at least one. -/
theorem total_centeredGram_energy_le (α : ℝ) (hα : 1 ≤ α)
    (hfour : ∀ i j, (∫ ω, Y i j ω ^ 4 ∂μ) ≤ α ^ 4 * (∫ ω, Y i j ω ^ 2 ∂μ) ^ 2)
    (E : ℝ)
    (hE : (∑ j, ∑ k, ∑ i, (∫ ω, Y i j ω ^ 2 ∂μ) * (∫ ω, Y i k ω ^ 2 ∂μ)) ≤ E) :
    (∑ j, ∑ k, ∫ ω, CenteredGramNorm.centeredGram (fun i j => Y i j ω)
        (fun j => ∑ i, ∫ ω', Y i j ω' ^ 2 ∂μ) j k ^ 2 ∂μ) ≤ α ^ 4 * E := by
  have hα4 : (0 : ℝ) ≤ α ^ 4 := by positivity
  calc
    (∑ j, ∑ k, ∫ ω, CenteredGramNorm.centeredGram (fun i j => Y i j ω)
        (fun j => ∑ i, ∫ ω', Y i j ω' ^ 2 ∂μ) j k ^ 2 ∂μ)
        ≤ ∑ j : C, ∑ k : C,
            α ^ 4 * ∑ i, (∫ ω, Y i j ω ^ 2 ∂μ) * (∫ ω, Y i k ω ^ 2 ∂μ) :=
      Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ =>
        integral_centeredGram_sq_le hY hind hmean hint α hα hfour j k
    _ = α ^ 4 * ∑ j : C, ∑ k : C, ∑ i,
          (∫ ω, Y i j ω ^ 2 ∂μ) * (∫ ω, Y i k ω ^ 2 ∂μ) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [Finset.mul_sum]
    _ ≤ α ^ 4 * E := mul_le_mul_of_nonneg_left hE hα4

end TotalEnergy

end MI32.GramEntryMoments
