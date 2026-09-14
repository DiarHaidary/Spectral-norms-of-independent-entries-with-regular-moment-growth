import MI32.MomentDoubling
import Mathlib.Probability.IdentDistrib

/-!
# The law of a deterministically masked original entry family

A deterministic zero-one mask keeps an original entry exactly where the mask
holds and puts a literal zero elsewhere. Measurability, joint independence of
the original ordered-pair coordinates, reflection symmetry, centering, every
positive absolute moment and the real-order doubling constant all transfer to
the masked family, and the masked second-moment budget is dominated entrywise
by the original one. The fourth-moment budget is recorded in the unrooted form
the Gram computation uses. Nothing here is a new probabilistic assumption:
every conclusion is derived from the corresponding original-entry hypothesis.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace MI32.MaskedEntryLaw

/-- The original entry, retained exactly where the deterministic mask holds. -/
def masked {Ω I J : Type*} (m : I → J → Bool) (X : I → J → Ω → ℝ)
    (i : I) (j : J) (ω : Ω) : ℝ :=
  if m i j then X i j ω else 0

variable {Ω I J : Type*} [MeasurableSpace Ω] [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] {μ : Measure Ω}
variable (m : I → J → Bool) (X : I → J → Ω → ℝ)

/-! ### Pointwise description of the mask -/

omit [MeasurableSpace Ω] [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
/-- Where the deterministic mask holds the masked entry is the original entry. -/
@[simp] theorem masked_apply_true {i : I} {j : J} (h : m i j = true) (ω : Ω) :
    masked m X i j ω = X i j ω := by
  simp [masked, h]

omit [MeasurableSpace Ω] [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
/-- Where the deterministic mask fails the masked entry is the literal zero. -/
@[simp] theorem masked_apply_false {i : I} {j : J} (h : m i j = false) (ω : Ω) :
    masked m X i j ω = 0 := by
  simp [masked, h]

omit [MeasurableSpace Ω] [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
/-- A retained coordinate of the masked family is the original random variable. -/
theorem masked_eq_of_true {i : I} {j : J} (h : m i j = true) :
    masked m X i j = X i j := by
  funext ω
  simp [masked, h]

omit [MeasurableSpace Ω] [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
/-- A discarded coordinate of the masked family is the zero random variable. -/
theorem masked_eq_zero_of_false {i : I} {j : J} (h : m i j = false) :
    masked m X i j = fun _ : Ω => (0 : ℝ) := by
  funext ω
  simp [masked, h]

/-! ### Pointwise contraction -/

omit [MeasurableSpace Ω] [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
/-- Masking never increases the absolute value of an entry. -/
theorem abs_masked_le (i : I) (j : J) (ω : Ω) :
    |masked m X i j ω| ≤ |X i j ω| := by
  by_cases h : m i j = true
  · simp [masked_apply_true m X h]
  · have h' : m i j = false := by simpa using h
    simp [masked_apply_false m X h']

omit [MeasurableSpace Ω] [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
/-- Masking never increases the square of an entry. -/
theorem masked_sq_le (i : I) (j : J) (ω : Ω) :
    masked m X i j ω ^ 2 ≤ X i j ω ^ 2 := by
  by_cases h : m i j = true
  · simp [masked_apply_true m X h]
  · have h' : m i j = false := by simpa using h
    simpa [masked_apply_false m X h'] using sq_nonneg (X i j ω)

/-! ### Measurability, independence and symmetry -/

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
/-- A deterministic mask preserves measurability of every entry. -/
theorem measurable_masked (hX : ∀ i j, Measurable (X i j)) :
    ∀ i j, Measurable (masked m X i j) := by
  intro i j
  by_cases h : m i j = true
  · rw [masked_eq_of_true m X h]
    exact hX i j
  · rw [masked_eq_zero_of_false m X (by simpa using h)]
    exact measurable_const

set_option linter.unusedVariables false in
omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
/-- A deterministic mask preserves joint independence of the original
ordered-pair coordinates: each masked entry is a fixed measurable function of
the single original entry at the same pair. -/
theorem independent_masked (hX : ∀ i j, Measurable (X i j))
    (hind : iIndepFun (fun e : I × J => X e.1 e.2) μ) :
    iIndepFun (fun e : I × J => masked m X e.1 e.2) μ := by
  have hg : ∀ e : I × J, Measurable (fun x : ℝ => if m e.1 e.2 then x else 0) := by
    intro e
    by_cases hm : m e.1 e.2 = true
    · have hfun : (fun x : ℝ => if m e.1 e.2 then x else 0) = fun x : ℝ => x := by
        funext x
        simp [hm]
      rw [hfun]
      exact measurable_id
    · have hfun : (fun x : ℝ => if m e.1 e.2 then x else 0) = fun _ : ℝ => (0 : ℝ) := by
        funext x
        simp [hm]
      rw [hfun]
      exact measurable_const
  have key := hind.comp (fun (e : I × J) (x : ℝ) => if m e.1 e.2 then x else 0) hg
  have hEq : (fun e : I × J =>
        (fun x : ℝ => if m e.1 e.2 then x else 0) ∘ (X e.1 e.2)) =
      fun e : I × J => masked m X e.1 e.2 := by
    funext e ω
    rfl
  rw [hEq] at key
  exact key

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
/-- A deterministic mask preserves reflection symmetry of every entry: a
retained coordinate keeps the original symmetry and a discarded coordinate is
the zero variable, which is its own negative. -/
theorem symmetric_masked
    (hsym : ∀ i j, IdentDistrib (X i j) (fun ω => -X i j ω) μ μ) :
    ∀ i j, IdentDistrib (masked m X i j) (fun ω => -masked m X i j ω) μ μ := by
  intro i j
  by_cases h : m i j = true
  · rw [masked_eq_of_true m X h]
    exact hsym i j
  · have hz : masked m X i j = fun _ : Ω => (0 : ℝ) :=
      masked_eq_zero_of_false m X (by simpa using h)
    simp only [hz, neg_zero]
    exact IdentDistrib.refl measurable_const.aemeasurable

/-! ### Centering and absolute moments -/

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
/-- A deterministic mask preserves centering of every entry. -/
theorem integral_masked_eq_zero (hzero : ∀ i j, (∫ ω, X i j ω ∂μ) = 0) :
    ∀ i j, (∫ ω, masked m X i j ω ∂μ) = 0 := by
  intro i j
  by_cases h : m i j = true
  · simp only [masked_apply_true m X h]
    exact hzero i j
  · simp [masked_apply_false m X (by simpa using h)]

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
/-- A deterministic mask preserves finiteness of every positive absolute
moment, including the orders below one. -/
theorem integrable_masked_abs_rpow
    (hint : ∀ i j (p : ℝ), 0 < p → Integrable (fun ω => |X i j ω| ^ p) μ) :
    ∀ i j (p : ℝ), 0 < p → Integrable (fun ω => |masked m X i j ω| ^ p) μ := by
  intro i j p hp
  by_cases h : m i j = true
  · simp only [masked_apply_true m X h]
    exact hint i j p hp
  · simp [masked_apply_false m X (by simpa using h), Real.zero_rpow hp.ne']

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
/-- Every nonzero-order absolute moment of the zero random variable vanishes. -/
theorem moment_zero_fun (p : ℝ) (hp : p ≠ 0) :
    moment μ p (fun _ : Ω => (0 : ℝ)) = 0 := by
  rw [moment]
  simp only [abs_zero, Real.zero_rpow hp, integral_zero]
  exact Real.zero_rpow (one_div_ne_zero hp)

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
/-- A deterministic mask preserves the real-order doubling constant at every
order `r ≥ 1`: a retained coordinate keeps the original inequality and on a
discarded coordinate both sides are zero. -/
theorem regular_masked (α : ℝ)
    (hregular : ∀ i j (r : ℝ), 1 ≤ r →
      moment μ (2 * r) (X i j) ≤ α * moment μ r (X i j)) :
    ∀ i j (r : ℝ), 1 ≤ r →
      moment μ (2 * r) (masked m X i j) ≤ α * moment μ r (masked m X i j) := by
  intro i j r hr
  have hr0 : (0 : ℝ) < r := lt_of_lt_of_le zero_lt_one hr
  by_cases h : m i j = true
  · rw [masked_eq_of_true m X h]
    exact hregular i j r hr
  · rw [masked_eq_zero_of_false m X (by simpa using h),
      moment_zero_fun (μ := μ) (2 * r) (by positivity),
      moment_zero_fun (μ := μ) r (ne_of_gt hr0), mul_zero]

/-! ### The unrooted fourth-moment budget -/

/-- The exact regularity assumption at order two gives the unrooted
fourth-moment budget. -/
theorem integral_fourth_le_of_regular (Z : Ω → ℝ) (α : ℝ)
    (hregular : ∀ r : ℝ, 1 ≤ r → moment μ (2 * r) Z ≤ α * moment μ r Z) :
    (∫ ω, Z ω ^ 4 ∂μ) ≤ α ^ 4 * (∫ ω, Z ω ^ 2 ∂μ) ^ 2 := by
  have habs4 : ∀ x : ℝ, |x| ^ (4 : ℕ) = x ^ (4 : ℕ) := by
    intro x
    rw [← abs_pow, abs_of_nonneg (by positivity : (0 : ℝ) ≤ x ^ 4)]
  have hraw := MI32.integral_pow_doubling μ Z α hregular 2 (by norm_num)
  have h : (∫ ω, |Z ω| ^ (4 : ℕ) ∂μ) ≤
      α ^ (4 : ℕ) * (∫ ω, |Z ω| ^ (2 : ℕ) ∂μ) ^ 2 := hraw
  calc (∫ ω, Z ω ^ 4 ∂μ) = ∫ ω, |Z ω| ^ (4 : ℕ) ∂μ := by
        simp only [habs4]
    _ ≤ α ^ (4 : ℕ) * (∫ ω, |Z ω| ^ (2 : ℕ) ∂μ) ^ 2 := h
    _ = α ^ 4 * (∫ ω, Z ω ^ 2 ∂μ) ^ 2 := by simp only [sq_abs]

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
/-- Masking preserves the unrooted fourth-moment budget. -/
theorem integral_fourth_masked_le (α : ℝ)
    (hregular : ∀ i j (r : ℝ), 1 ≤ r →
      moment μ (2 * r) (X i j) ≤ α * moment μ r (X i j))
    (i : I) (j : J) :
    (∫ ω, masked m X i j ω ^ 4 ∂μ) ≤
      α ^ 4 * (∫ ω, masked m X i j ω ^ 2 ∂μ) ^ 2 :=
  integral_fourth_le_of_regular (masked m X i j) α
    (fun r hr => regular_masked m X α hregular i j r hr)

/-! ### The second-moment budget and the support of the mask -/

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
/-- The masked second moment of an entry is nonnegative. -/
theorem integral_sq_masked_nonneg (i : I) (j : J) :
    0 ≤ ∫ ω, masked m X i j ω ^ 2 ∂μ :=
  integral_nonneg fun _ω => sq_nonneg _

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
/-- A discarded coordinate carries no second-moment budget. -/
theorem integral_sq_masked_eq_zero_of_not {i : I} {j : J} (h : m i j = false) :
    (∫ ω, masked m X i j ω ^ 2 ∂μ) = 0 := by
  simp [masked_apply_false m X h]

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
/-- Only retained coordinates can carry second-moment budget. -/
theorem mask_of_integral_sq_masked_ne_zero {i : I} {j : J}
    (h : (∫ ω, masked m X i j ω ^ 2 ∂μ) ≠ 0) : m i j = true := by
  by_contra hc
  exact h (integral_sq_masked_eq_zero_of_not m X (by simpa using hc))

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
/-- Masking never increases the second-moment budget of an entry. -/
theorem integral_sq_masked_le (i : I) (j : J) :
    (∫ ω, masked m X i j ω ^ 2 ∂μ) ≤ ∫ ω, X i j ω ^ 2 ∂μ := by
  by_cases h : m i j = true
  · rw [masked_eq_of_true m X h]
  · rw [integral_sq_masked_eq_zero_of_not m X (show m i j = false by simpa using h)]
    exact integral_nonneg fun _ω => sq_nonneg _

omit [Fintype I] [DecidableEq I] [DecidableEq J] in
/-- Masking never increases a row second-moment budget. -/
theorem sum_row_sq_masked_le (i : I) :
    (∑ j, ∫ ω, masked m X i j ω ^ 2 ∂μ) ≤ ∑ j, ∫ ω, X i j ω ^ 2 ∂μ :=
  Finset.sum_le_sum fun j _ => integral_sq_masked_le m X i j

omit [Fintype J] [DecidableEq I] [DecidableEq J] in
/-- Masking never increases a column second-moment budget. -/
theorem sum_col_sq_masked_le (j : J) :
    (∑ i, ∫ ω, masked m X i j ω ^ 2 ∂μ) ≤ ∑ i, ∫ ω, X i j ω ^ 2 ∂μ :=
  Finset.sum_le_sum fun i _ => integral_sq_masked_le m X i j

end MI32.MaskedEntryLaw
