import MI32.MomentDoubling
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The actual independent copy in the diagonal Hilbert comparison

Coordinate pairs are formed on the product of the original probability
space with itself. No distributional comparison or vector estimate is
assumed: independence and reflection symmetry of the new coordinates
are derived from the original laws.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace MI32.DiagonalCopyComparison

variable {Ω E : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Difference of the two original coordinate squares. -/
def squareDifference (V : E → Ω → ℝ) (j : E) (z : Ω × Ω) : ℝ :=
  V j z.1 ^ 2 - V j z.2 ^ 2

/-- Product of the original coordinate with its independent copy. -/
def copyProduct (V : E → Ω → ℝ) (j : E) (z : Ω × Ω) : ℝ :=
  V j z.1 * V j z.2

@[fun_prop] theorem measurable_squareDifference (V : E → Ω → ℝ)
    (hV : ∀ j, Measurable (V j)) (j : E) : Measurable (squareDifference V j) := by
  unfold squareDifference
  fun_prop

@[fun_prop] theorem measurable_copyProduct (V : E → Ω → ℝ)
    (hV : ∀ j, Measurable (V j)) (j : E) : Measurable (copyProduct V j) := by
  unfold copyProduct
  fun_prop

/-- The law of a coordinate pair is exactly the product of its original marginals. -/
theorem map_coordinatePair (V : Ω → ℝ) (hV : Measurable V) :
    (μ.prod μ).map (fun z : Ω × Ω => (V z.1, V z.2)) =
      (μ.map V).prod (μ.map V) := by
  exact (Measure.map_prod_map μ μ hV hV).symm

/-- Pairing independent copies preserves independence across the original coordinates. -/
theorem independent_coordinatePairs [Fintype E] (V : E → Ω → ℝ)
    (hV : ∀ j, Measurable (V j)) (hind : iIndepFun V μ) :
    iIndepFun (fun j (z : Ω × Ω) => (V j z.1, V j z.2)) (μ.prod μ) := by
  have hvec : Measurable (fun ω j => V j ω) := measurable_pi_lambda _ hV
  have hpair := measurePreserving_arrowProdEquivProdArrow ℝ ℝ E
    (fun j => μ.map (V j)) (fun j => μ.map (V j))
  have hinv := MeasurePreserving.symm
    (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ E) hpair
  apply (iIndepFun_iff_map_fun_eq_pi_map (fun j =>
    ((hV j).comp measurable_fst |>.prodMk ((hV j).comp measurable_snd)).aemeasurable)).mpr
  have hmarg (j : E) := map_coordinatePair (μ := μ) (V j) (hV j)
  simp only [Function.comp_def]
  simp_rw [hmarg]
  calc
    (μ.prod μ).map (fun z : Ω × Ω => fun j => (V j z.1, V j z.2)) =
        ((μ.map (fun ω j => V j ω)).prod (μ.map (fun ω j => V j ω))).map
          (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ E).symm := by
      rw [Measure.map_prod_map μ μ hvec hvec,
        Measure.map_map (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ E).symm.measurable
          (hvec.prodMap hvec)]
      rfl
    _ = Measure.pi (fun j => (μ.map (V j)).prod (μ.map (V j))) := by
      rw [hind.map_fun_eq_pi_map (fun j => (hV j).aemeasurable)]
      exact hinv.map_eq

theorem independent_squareDifferences [Fintype E] (V : E → Ω → ℝ)
    (hV : ∀ j, Measurable (V j)) (hind : iIndepFun V μ) :
    iIndepFun (squareDifference V) (μ.prod μ) := by
  exact (independent_coordinatePairs V hV hind).comp
    (fun _ (p : ℝ × ℝ) => p.1 ^ 2 - p.2 ^ 2) (fun _ => by fun_prop)

theorem independent_copyProducts [Fintype E] (V : E → Ω → ℝ)
    (hV : ∀ j, Measurable (V j)) (hind : iIndepFun V μ) :
    iIndepFun (copyProduct V) (μ.prod μ) := by
  exact (independent_coordinatePairs V hV hind).comp
    (fun _ (p : ℝ × ℝ) => p.1 * p.2) (fun _ => by fun_prop)

/-- Exchange of the two copies makes the square difference symmetric,
even without symmetry of the original variable. -/
theorem symmetric_squareDifference (V : E → Ω → ℝ)
    (hV : ∀ j, Measurable (V j)) (j : E) :
    IdentDistrib (squareDifference V j) (fun z => -squareDifference V j z)
      (μ.prod μ) (μ.prod μ) := by
  refine ⟨(measurable_squareDifference V hV j).aemeasurable,
    (measurable_squareDifference V hV j).neg.aemeasurable, ?_⟩
  have hswap := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).map_eq
  calc
    (μ.prod μ).map (squareDifference V j) =
        ((μ.prod μ).map Prod.swap).map (squareDifference V j) := by rw [hswap]
    _ = (μ.prod μ).map (fun z => -squareDifference V j z) := by
      rw [Measure.map_map (measurable_squareDifference V hV j) measurable_swap]
      congr 1
      funext z
      simp [squareDifference]

/-- Multiplication by an independent copy preserves the original reflection symmetry. -/
theorem symmetric_copyProduct (V : E → Ω → ℝ)
    (hV : ∀ j, Measurable (V j))
    (hsym : ∀ j, IdentDistrib (V j) (fun ω => -V j ω) μ μ) (j : E) :
    IdentDistrib (copyProduct V j) (fun z => -copyProduct V j z)
      (μ.prod μ) (μ.prod μ) := by
  have hpair : IdentDistrib
      (fun z : Ω × Ω => (V j z.1, V j z.2))
      (fun z : Ω × Ω => (-V j z.1, V j z.2)) (μ.prod μ) (μ.prod μ) := by
    refine ⟨(by fun_prop), (by fun_prop), ?_⟩
    rw [map_coordinatePair (V j) (hV j)]
    rw [show (fun z : Ω × Ω => (-V j z.1, V j z.2)) =
      Prod.map (fun ω => -V j ω) (V j) from rfl]
    calc
      _ = (μ.map (fun ω => -V j ω)).prod (μ.map (V j)) := by rw [(hsym j).map_eq]
      _ = _ := Measure.map_prod_map μ μ
        (show Measurable (fun ω => -V j ω) from (hV j).neg) (hV j)
  change IdentDistrib (fun z : Ω × Ω => V j z.1 * V j z.2)
    (fun z : Ω × Ω => -(V j z.1 * V j z.2)) _ _
  simpa only [Function.comp_def, neg_mul] using
    hpair.comp (by fun_prop : Measurable (fun p : ℝ × ℝ => p.1 * p.2))

/-- The difference of nonnegative squares has no larger power than the
sum of the two corresponding even powers. -/
theorem abs_squareDifference_pow_le (a b : ℝ) (r : ℕ) :
    |a ^ 2 - b ^ 2| ^ r ≤ a ^ (2 * r) + b ^ (2 * r) := by
  rcases le_total (a ^ 2) (b ^ 2) with hab | hba
  · rw [abs_of_nonpos (sub_nonpos.mpr hab), neg_sub]
    calc
      (b ^ 2 - a ^ 2) ^ r ≤ (b ^ 2) ^ r :=
        pow_le_pow_left₀ (sub_nonneg.mpr hab) (by nlinarith [sq_nonneg a]) r
      _ = b ^ (2 * r) := (pow_mul b 2 r).symm
      _ ≤ _ := le_add_of_nonneg_left ((even_two_mul r).pow_nonneg a)
  · rw [abs_of_nonneg (sub_nonneg.mpr hba)]
    calc
      (a ^ 2 - b ^ 2) ^ r ≤ (a ^ 2) ^ r :=
        pow_le_pow_left₀ (sub_nonneg.mpr hba) (by nlinarith [sq_nonneg b]) r
      _ = a ^ (2 * r) := (pow_mul a 2 r).symm
      _ ≤ _ := le_add_of_nonneg_right ((even_two_mul r).pow_nonneg b)

omit [IsProbabilityMeasure μ] in
/-- All natural moments of the original coordinates supply the actual
mixed-product integrability needed by the even-sum expansion. -/
theorem integrable_copyProduct_pow (V : E → Ω → ℝ)
    (hint : ∀ j r, Integrable (fun ω => V j ω ^ r) μ) (j : E) (r : ℕ) :
    Integrable (fun z => copyProduct V j z ^ r) (μ.prod μ) := by
  simpa only [copyProduct, mul_pow] using (hint j r).mul_prod (hint j r)

theorem integrable_squareDifference_pow (V : E → Ω → ℝ)
    (hV : ∀ j, Measurable (V j))
    (hint : ∀ j r, Integrable (fun ω => V j ω ^ r) μ) (j : E) (r : ℕ) :
    Integrable (fun z => squareDifference V j z ^ r) (μ.prod μ) := by
  have hdom := ((hint j (2 * r)).comp_fst μ).add ((hint j (2 * r)).comp_snd μ)
  refine hdom.mono' ((measurable_squareDifference V hV j).pow_const r).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun z => by
    simpa only [Real.norm_eq_abs, abs_pow, squareDifference, Pi.add_apply] using
      abs_squareDifference_pow_le (V j z.1) (V j z.2) r

/-- Product factorization is an equality for the actual original marginal moments. -/
theorem integral_copyProduct_pow (V : E → Ω → ℝ) (j : E) (r : ℕ) :
    (∫ z, copyProduct V j z ^ r ∂(μ.prod μ)) = (∫ ω, V j ω ^ r ∂μ) ^ 2 := by
  simp only [copyProduct, mul_pow]
  rw [integral_prod_mul (fun ω => V j ω ^ r) (fun ω => V j ω ^ r)]
  ring

/-- The original rooted scalar regularity gives the needed unrooted
even moment comparison for square differences and decoupled products. -/
theorem coordinate_even_moment_le (V : E → Ω → ℝ)
    (hV : ∀ j, Measurable (V j))
    (hint : ∀ j r, Integrable (fun ω => V j ω ^ r) μ)
    (β : ℝ) (j : E) (r : ℕ) (hr : 1 ≤ r)
    (hregular : moment μ (4 * r : ℕ) (V j) ≤ β * moment μ (2 * r : ℕ) (V j)) :
    (∫ z, squareDifference V j z ^ (2 * r) ∂(μ.prod μ)) ≤
      (2 * β ^ 2) ^ (2 * r) * ∫ z, copyProduct V j z ^ (2 * r) ∂(μ.prod μ) := by
  have hr2 : 0 < 2 * r := by omega
  have hr4 : 0 < 4 * r := by omega
  have heven2 : Even (2 * r) := even_two_mul r
  have heven4 : Even (4 * r) := by exact ⟨2 * r, by omega⟩
  have hroot : 0 ≤ moment μ (4 * r : ℕ) (V j) := by
    unfold moment
    positivity
  have hd := pow_le_pow_left₀ hroot hregular (4 * r)
  have hdoubling : (∫ ω, V j ω ^ (4 * r) ∂μ) ≤
      β ^ (4 * r) * (∫ ω, V j ω ^ (2 * r) ∂μ) ^ 2 := by
    calc
      _ = moment μ (4 * r : ℕ) (V j) ^ (4 * r) := by
        rw [moment_nat_pow μ (V j) (4 * r) hr4]
        simp only [heven4.pow_abs]
      _ ≤ (β * moment μ (2 * r : ℕ) (V j)) ^ (4 * r) := hd
      _ = _ := by
        rw [mul_pow]
        congr 1
        rw [show 4 * r = (2 * r) * 2 by omega, pow_mul,
          moment_nat_pow μ (V j) (2 * r) hr2]
        simp only [heven2.pow_abs]
  have hdom := ((hint j (4 * r)).comp_fst μ).add ((hint j (4 * r)).comp_snd μ)
  have hpre : (∫ z, squareDifference V j z ^ (2 * r) ∂(μ.prod μ)) ≤
      2 * ∫ ω, V j ω ^ (4 * r) ∂μ := by
    calc
      _ ≤ ∫ z : Ω × Ω, (V j z.1 ^ (4 * r) + V j z.2 ^ (4 * r)) ∂(μ.prod μ) := by
        apply integral_mono (integrable_squareDifference_pow V hV hint j (2 * r)) hdom
        intro z
        simpa only [squareDifference, Pi.add_apply, heven2.pow_abs,
          show 2 * (2 * r) = 4 * r by omega] using
          abs_squareDifference_pow_le (V j z.1) (V j z.2) (2 * r)
      _ = _ := by
        rw [integral_add ((hint j (4 * r)).comp_fst μ) ((hint j (4 * r)).comp_snd μ)]
        rw [integral_fun_fst (fun ω => V j ω ^ (4 * r)),
          integral_fun_snd (fun ω => V j ω ^ (4 * r))]
        simp [measureReal_def, two_mul]
  have htwo : (2 : ℝ) ≤ 2 ^ (2 * r) := by
    simpa using pow_le_pow_right₀ (show (1 : ℝ) ≤ 2 by norm_num) (show 1 ≤ 2 * r by omega)
  calc
    _ ≤ 2 * ∫ ω, V j ω ^ (4 * r) ∂μ := hpre
    _ ≤ 2 * (β ^ (4 * r) * (∫ ω, V j ω ^ (2 * r) ∂μ) ^ 2) :=
      mul_le_mul_of_nonneg_left hdoubling (by norm_num)
    _ ≤ 2 ^ (2 * r) * (β ^ (4 * r) * (∫ ω, V j ω ^ (2 * r) ∂μ) ^ 2) :=
      mul_le_mul_of_nonneg_right htwo
        (mul_nonneg (heven4.pow_nonneg β) (sq_nonneg _))
    _ = _ := by
      rw [integral_copyProduct_pow, mul_pow, ← pow_mul,
        show 2 * (2 * r) = 4 * r by omega]
      ring

/-- The zero exponent is normalized exactly and needs no regularity input. -/
theorem coordinate_even_moment_le_nat (V : E → Ω → ℝ)
    (hV : ∀ j, Measurable (V j))
    (hint : ∀ j r, Integrable (fun ω => V j ω ^ r) μ)
    (β : ℝ) (j : E) (r : ℕ)
    (hregular : 1 ≤ r →
      moment μ (4 * r : ℕ) (V j) ≤ β * moment μ (2 * r : ℕ) (V j)) :
    (∫ z, squareDifference V j z ^ (2 * r) ∂(μ.prod μ)) ≤
      (2 * β ^ 2) ^ (2 * r) * ∫ z, copyProduct V j z ^ (2 * r) ∂(μ.prod μ) := by
  by_cases hr : r = 0
  · simp [hr]
  · exact coordinate_even_moment_le V hV hint β j r (by omega) (hregular (by omega))

/-- Convenient all-integer form when real-order scalar regularity is available. -/
theorem coordinate_even_moment_le_of_regular (V : E → Ω → ℝ)
    (hV : ∀ j, Measurable (V j))
    (hint : ∀ j r, Integrable (fun ω => V j ω ^ r) μ)
    (β : ℝ)
    (hregular : ∀ j (s : ℝ), 2 ≤ s →
      moment μ (2 * s) (V j) ≤ β * moment μ s (V j)) (j : E) (r : ℕ) :
    (∫ z, squareDifference V j z ^ (2 * r) ∂(μ.prod μ)) ≤
      (2 * β ^ 2) ^ (2 * r) * ∫ z, copyProduct V j z ^ (2 * r) ∂(μ.prod μ) := by
  by_cases hr : r = 0
  · simp [hr]
  · apply coordinate_even_moment_le V hV hint β j r (by omega)
    have h := hregular j (2 * r : ℕ) (by exact_mod_cast (show 2 ≤ 2 * r by omega))
    have heq : ((4 * r : ℕ) : ℝ) = 2 * ((2 * r : ℕ) : ℝ) := by push_cast; ring
    rw [heq]
    exact h

end MI32.DiagonalCopyComparison
