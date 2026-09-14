import Mathlib.Probability.IdentDistribIndep
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Tactic

/-!
# Independent column linear forms from the original matrix entries

The independent random coordinates are the original ordered pairs `(i,j)`.
Regrouping them into columns is justified through the exact joint product law.
The subsequent deterministic linear map may have arbitrary signed coefficients.
-/

noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory

namespace MI32.IndependentColumns

variable {Ω I J : Type*} [MeasurableSpace Ω] [Fintype I]
    {μ : Measure Ω}

/-- The j-th coordinate of the actual matrix image of a fixed row vector. -/
def columnLinearForm (X : I → J → Ω → ℝ) (s : I → ℝ) (j : J) (ω : Ω) : ℝ :=
  ∑ i, s i * X i j ω

@[fun_prop] theorem measurable_columnLinearForm
    (X : I → J → Ω → ℝ) (hX : ∀ i j, Measurable (X i j)) (s : I → ℝ) (j : J) :
    Measurable (columnLinearForm X s j) := by
  unfold columnLinearForm
  fun_prop

omit [Fintype I] in
/-- Restricting original ordered-pair coordinates to one column preserves their independence. -/
theorem independent_within_column (X : I → J → Ω → ℝ)
    (hind : iIndepFun (fun e : I × J => X e.1 e.2) μ) (j : J) :
    iIndepFun (fun i => X i j) μ :=
  hind.precomp (show Function.Injective (fun i : I => (i, j)) from
    fun _ _ h => congrArg Prod.fst h)

omit [Fintype I] in
/-- Entire original column vectors are jointly independent. This is a statement
about the original probability space, not a separately imposed column law. -/
theorem independent_column_vectors (X : I → J → Ω → ℝ)
    (hX : ∀ i j, Measurable (X i j))
    (hind : iIndepFun (fun e : I × J => X e.1 e.2) μ) :
    iIndepFun (fun j ω i => X i j ω) μ := by
  have : IsProbabilityMeasure μ := hind.isProbabilityMeasure
  have hswap : iIndepFun (fun e : J × I => X e.2 e.1) μ :=
    hind.precomp Prod.swap_injective
  have hμ (j : J) (i : I) : IsProbabilityMeasure (μ.map (X i j)) :=
    Measure.isProbabilityMeasure_map (hX i j).aemeasurable
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map (fun j => by fun_prop)]
  change μ.map ((MeasurableEquiv.curry J I ℝ) ∘
    (fun ω (e : J × I) => X e.2 e.1 ω)) = _
  have hjoint : μ.map (fun ω (e : J × I) => X e.2 e.1 ω) =
      Measure.infinitePi (fun e : J × I => μ.map (X e.2 e.1)) :=
    hswap.map_fun_eq_infinitePi_map (fun e => hX e.2 e.1)
  rw [← Measure.map_map (by fun_prop) (by fun_prop), hjoint,
    Measure.infinitePi_map_curry (fun j i => μ.map (X i j))]
  congr 1
  funext j
  exact ((independent_within_column X hind j).map_fun_eq_infinitePi_map
    (fun i => hX i j)).symm

/-- Actual fixed-vector column sums are jointly independent, with no assumptions
on the signs of the deterministic coefficient vector. -/
theorem independent_columnLinearForm (X : I → J → Ω → ℝ)
    (hX : ∀ i j, Measurable (X i j))
    (hind : iIndepFun (fun e : I × J => X e.1 e.2) μ) (s : I → ℝ) :
    iIndepFun (columnLinearForm X s) μ := by
  exact (independent_column_vectors X hX hind).comp
    (fun _ => fun x : I → ℝ => ∑ i, s i * x i) (fun _ => by fun_prop)

/-- A linear form in independent symmetric original coordinates is itself symmetric.
Both joint laws are derived from the original independent coordinate family. -/
theorem symmetric_columnLinearForm (X : I → J → Ω → ℝ)
    (hind : iIndepFun (fun e : I × J => X e.1 e.2) μ)
    (hsym : ∀ i j, IdentDistrib (X i j) (fun ω => -X i j ω) μ μ)
    (s : I → ℝ) (j : J) :
    IdentDistrib (columnLinearForm X s j) (fun ω => -columnLinearForm X s j ω) μ μ := by
  have hcol := independent_within_column X hind j
  have hneg : iIndepFun (fun i ω => -X i j ω) μ :=
    hcol.comp (fun _ => fun x : ℝ => -x) (fun _ => by fun_prop)
  have hpi := IdentDistrib.pi (fun i => hsym i j) hcol hneg
  have hlin : Measurable (fun x : I → ℝ => ∑ i, s i * x i) := by fun_prop
  change IdentDistrib (fun ω => ∑ i, s i * X i j ω)
    (fun ω => -(∑ i, s i * X i j ω)) μ μ
  simpa only [Function.comp_def, mul_neg, Finset.sum_neg_distrib] using hpi.comp hlin

/-- Finite linear forms preserve every `MemLp` class, also for exponents below one. -/
theorem memLp_columnLinearForm (X : I → J → Ω → ℝ) (p : ℝ≥0∞)
    (hX : ∀ i j, MemLp (X i j) p μ) (s : I → ℝ) (j : J) :
    MemLp (columnLinearForm X s j) p μ :=
  memLp_finsetSum _ fun i _ => (hX i j).const_mul (s i)

/-- Positive absolute moments of column sums follow from the original scalar moments.
This integrability statement does not require independence or symmetry. -/
theorem integrable_abs_rpow_columnLinearForm (X : I → J → Ω → ℝ)
    (hX : ∀ i j, Measurable (X i j))
    (hint : ∀ i j (p : ℝ), 0 < p → Integrable (fun ω => |X i j ω| ^ p) μ)
    (s : I → ℝ) (j : J) (p : ℝ) (hp : 0 < p) :
    Integrable (fun ω => |columnLinearForm X s j ω| ^ p) μ := by
  have hp0 : ENNReal.ofReal p ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hp
  have hmem (i : I) (j' : J) : MemLp (X i j') (ENNReal.ofReal p) μ := by
    apply (integrable_norm_rpow_iff (hX i j').aestronglyMeasurable hp0
      ENNReal.ofReal_ne_top).mp
    simpa only [ENNReal.toReal_ofReal hp.le, Real.norm_eq_abs] using hint i j' p hp
  have h := (memLp_columnLinearForm X (ENNReal.ofReal p) hmem s j).integrable_norm_rpow
    hp0 ENNReal.ofReal_ne_top
  simpa only [ENNReal.toReal_ofReal hp.le, Real.norm_eq_abs] using h

/-- Centering of the original entries passes to every fixed-vector column sum. -/
theorem integral_columnLinearForm_eq_zero (X : I → J → Ω → ℝ)
    (hint : ∀ i j, Integrable (X i j) μ)
    (hzero : ∀ i j, (∫ ω, X i j ω ∂μ) = 0) (s : I → ℝ) (j : J) :
    (∫ ω, columnLinearForm X s j ω ∂μ) = 0 := by
  unfold columnLinearForm
  rw [integral_finsetSum _ fun i _ => (hint i j).const_mul (s i)]
  simp only [integral_const_mul, hzero, mul_zero, Finset.sum_const_zero]

end MI32.IndependentColumns




