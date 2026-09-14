import MI32.DiagonalCopyComparison
import MI32.SymmetricMomentComparison
import MI32.CopySymmetrization
import MI32.HilbertConditioning
import MI32.MomentTools
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-!
# Direct strong--weak comparison for independent Euclidean coordinates

The proof uses the actual product of the original probability space with
itself. Square-difference symmetrization, even-moment tensorization, and
conditioning give a quadratic inequality for the original norm moment.
No vector comparison estimate or mixed-coordinate estimate is an input.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators InnerProductSpace

namespace MI32.HilbertComparison

private theorem quadratic_bound (x s a : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a)
    (h : x ^ 2 ≤ s ^ 2 + a * x) : x ≤ s + a := by
  by_contra! hbad
  have hp := mul_pos (show 0 < x - s - a by linarith) (show 0 < x + s by linarith)
  nlinarith [mul_nonneg ha hs]

/-- The original Euclidean norm's `4q` moment is controlled by its second
moment and its deterministic scalar weak `2q` moment, uniformly in the
number of independent coordinates. The original sample space is arbitrary.
Only scalar regularity at even natural orders is assumed. -/
theorem independent_coordinate_moment_le
    {Ω E : Type*} [MeasurableSpace Ω] [Fintype E]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (V : E → Ω → ℝ) (hV : ∀ j, Measurable (V j))
    (hind : iIndepFun V μ)
    (hsym : ∀ j, IdentDistrib (V j) (fun ω => -V j ω) μ μ)
    (hint : ∀ j r, Integrable (fun ω => V j ω ^ r) μ)
    (β : ℝ)
    (hregular : ∀ j (r : ℕ), 1 ≤ r →
      moment μ (4 * r : ℕ) (V j) ≤ β * moment μ (2 * r : ℕ) (V j))
    (q : ℕ) (hq : 1 ≤ q) (W : ℝ) (hW : 0 ≤ W)
    (hweak : ∀ t : EuclideanSpace ℝ E, ‖t‖ ≤ 1 →
      moment μ (2 * q : ℕ)
        (fun ω => ⟪t, WithLp.toLp 2 (fun j => V j ω)⟫_ℝ) ≤ W) :
    moment μ (4 * q : ℕ) (fun ω => ‖WithLp.toLp 2 (fun j => V j ω)‖) ≤
      Real.sqrt (∫ ω, ‖WithLp.toLp 2 (fun j => V j ω)‖ ^ 2 ∂μ) + 2 * β ^ 2 * W := by
  classical
  let U : Ω → EuclideanSpace ℝ E := fun ω => WithLp.toLp 2 (fun j => V j ω)
  let R : Ω → ℝ := fun ω => ‖U ω‖
  let C : ℝ := 2 * β ^ 2
  have hC : 0 ≤ C := mul_nonneg (by norm_num) (sq_nonneg β)
  have hq2 : 1 ≤ 2 * q := by omega
  have hq20 : (0 : ℝ) < ((2 * q : ℕ) : ℝ) := by exact_mod_cast (show 0 < 2 * q by omega)
  have heven2 : Even (2 * q) := even_two_mul q
  have heven4 : Even (4 * q) := ⟨2 * q, by omega⟩
  have hp_eq : (2 : ℝ) * ((2 * q : ℕ) : ℝ) = ((4 * q : ℕ) : ℝ) := by
    push_cast
    ring
  have hU : Measurable U :=
    (WithLp.measurable_toLp 2 (E → ℝ)).comp (measurable_pi_lambda _ hV)
  have hU4 : MemLp U (4 * q : ℕ) μ := by
    apply memLp_piLp_iff.mpr
    intro j
    change MemLp (V j) (4 * q : ℕ) μ
    exact MomentTools.memLp_of_integrable_even_pow (V j) (hV j).aestronglyMeasurable
      (4 * q) (by omega) heven4 (hint j (4 * q))
  have hR4 : MemLp R (ENNReal.ofReal ((4 * q : ℕ) : ℝ)) μ := by
    simpa only [ENNReal.ofReal_natCast] using hU4.norm
  have hU2 : MemLp U (2 * q : ℕ) μ :=
    hU4.mono_exponent (by exact_mod_cast (show 2 * q ≤ 4 * q by omega))
  have hR2int : Integrable (fun ω => R ω ^ (2 * q)) μ :=
    hU2.integrable_norm_pow (by omega)
  have hS2 : MemLp (fun ω => R ω ^ 2) (2 * q : ℕ) μ := by
    have h := MomentTools.memLp_square ((2 * q : ℕ) : ℝ) hq20 R
      (by rw [hp_eq]; exact hR4)
    simpa only [ENNReal.ofReal_natCast] using h

  have hsumA : (fun z : Ω × Ω => ∑ j, DiagonalCopyComparison.squareDifference V j z) =
      (fun z => R z.1 ^ 2 - R z.2 ^ 2) := by
    funext z
    simp [DiagonalCopyComparison.squareDifference, R, U,
      EuclideanSpace.real_norm_sq_eq, Finset.sum_sub_distrib]
  have hsumB : (fun z : Ω × Ω => ∑ j, DiagonalCopyComparison.copyProduct V j z) =
      (fun z => ⟪U z.1, U z.2⟫_ℝ) := by
    funext z
    simp [DiagonalCopyComparison.copyProduct, U, EuclideanSpace.inner_toLp_toLp,
      dotProduct, mul_comm]

  have hcopy := CopySymmetrization.centered_even_moment_le_copy
    (fun ω => R ω ^ 2) (2 * q) hq2 heven2 hS2
  have hcenter := MomentTools.even_moment_mono_of_integral_le
    (fun ω => R ω ^ 2 - ∫ η, R η ^ 2 ∂μ)
    (fun z : Ω × Ω => R z.1 ^ 2 - R z.2 ^ 2)
    (2 * q) hq2 heven2 hcopy.2.2
  have hsum0 := SymmetricMomentComparison.sum_even_moment_le
    (DiagonalCopyComparison.squareDifference V) (DiagonalCopyComparison.copyProduct V)
    (DiagonalCopyComparison.measurable_squareDifference V hV)
    (DiagonalCopyComparison.measurable_copyProduct V hV)
    (DiagonalCopyComparison.independent_squareDifferences V hV hind)
    (DiagonalCopyComparison.independent_copyProducts V hV hind)
    (DiagonalCopyComparison.integrable_squareDifference_pow V hV hint)
    (DiagonalCopyComparison.integrable_copyProduct_pow V hint)
    (DiagonalCopyComparison.symmetric_squareDifference V hV)
    (DiagonalCopyComparison.symmetric_copyProduct V hV hsym) C hC
    (fun j r => DiagonalCopyComparison.coordinate_even_moment_le_nat V hV hint β j r
      (hregular j r)) q hq
  have hsum : moment (μ.prod μ) (2 * q : ℕ)
      (fun z : Ω × Ω => R z.1 ^ 2 - R z.2 ^ 2) ≤
      C * moment (μ.prod μ) (2 * q : ℕ) (fun z => ⟪U z.1, U z.2⟫_ℝ) := by
    rw [hsumA, hsumB] at hsum0
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hsum0

  have hunit : ∀ t : EuclideanSpace ℝ E, ‖t‖ ≤ 1 →
      (∫ ω, |⟪t, U ω⟫_ℝ| ^ (2 * q) ∂μ) ≤ W ^ (2 * q) := by
    intro t ht
    have h := pow_le_pow_left₀
      (MomentTools.nonneg (μ := μ) (2 * q : ℕ) (fun ω => ⟪t, U ω⟫_ℝ))
      (hweak t ht) (2 * q)
    rwa [moment_nat_pow μ (fun ω => ⟪t, U ω⟫_ℝ) (2 * q) (by omega)] at h
  have hcond := HilbertConditioning.integral_copy_inner_pow_le U hU (2 * q)
    (by omega) hR2int (W ^ (2 * q)) hunit
  have hcond' : (∫ z : Ω × Ω, ⟪U z.1, U z.2⟫_ℝ ^ (2 * q) ∂(μ.prod μ)) ≤
      W ^ (2 * q) * ∫ ω, R ω ^ (2 * q) ∂μ := by
    simpa only [heven2.pow_abs] using hcond.2
  have hcondRoot := MomentTools.even_moment_le_of_integral_le
    (fun z : Ω × Ω => ⟪U z.1, U z.2⟫_ℝ) R W hW (2 * q) hq2 heven2 hcond'
  have hcenterBound : moment μ (2 * q : ℕ)
      (fun ω => R ω ^ 2 - ∫ η, R η ^ 2 ∂μ) ≤
      (C * W) * moment μ (2 * q : ℕ) R := by
    calc
      _ ≤ moment (μ.prod μ) (2 * q : ℕ) (fun z : Ω × Ω => R z.1 ^ 2 - R z.2 ^ 2) := hcenter
      _ ≤ C * moment (μ.prod μ) (2 * q : ℕ) (fun z : Ω × Ω => ⟪U z.1, U z.2⟫_ℝ) := hsum
      _ ≤ C * (W * moment μ (2 * q : ℕ) R) := mul_le_mul_of_nonneg_left hcondRoot hC
      _ = _ := by ring

  have hmono := MomentTools.mono_exponent ((2 * q : ℕ) : ℝ) ((4 * q : ℕ) : ℝ)
    hq20 (by exact_mod_cast (show 2 * q ≤ 4 * q by omega)) R hR4
  have hquad0 := MomentTools.two_order_square_le_mean_add_centered_square
    ((2 * q : ℕ) : ℝ) (by exact_mod_cast hq2) R (by rw [hp_eq]; exact hR4)
  rw [hp_eq] at hquad0
  have hquad : moment μ (4 * q : ℕ) R ^ 2 ≤ (∫ ω, R ω ^ 2 ∂μ) +
      (C * W) * moment μ (4 * q : ℕ) R := by
    have hgain := mul_le_mul_of_nonneg_left hmono (mul_nonneg hC hW)
    linarith
  have hmean : 0 ≤ ∫ ω, R ω ^ 2 ∂μ := integral_nonneg fun _ => sq_nonneg _
  have hfinal := quadratic_bound (moment μ (4 * q : ℕ) R)
    (Real.sqrt (∫ ω, R ω ^ 2 ∂μ)) (C * W)
    (Real.sqrt_nonneg _) (mul_nonneg hC hW) (by rwa [Real.sq_sqrt hmean])
  exact hfinal

end MI32.HilbertComparison
