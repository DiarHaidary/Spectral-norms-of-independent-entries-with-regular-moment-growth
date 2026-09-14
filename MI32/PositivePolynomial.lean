import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FunProp
import Lean.Elab.Tactic.Omega

open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace MI32
namespace PositivePolynomial

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Original-variable monomial. Exponents are never replaced by parity. -/
def monomial (z : ι → ℝ) (ν : ι → ℕ) : ℝ := ∏ i, z i ^ ν i

/-- Total degree in the original variables. -/
def degree (ν : ι → ℕ) : ℕ := ∑ i, ν i

/-- Product of the original coordinate moments, retaining every exponent. -/
def tensorMoment (m : ι → ℕ → ℝ) (ν : ι → ℕ) : ℝ := ∏ i, m i (ν i)

lemma monomial_add (z : ι → ℝ) (ν η : ι → ℕ) :
    monomial z (ν + η) = monomial z ν * monomial z η := by
  simp [monomial, Pi.add_apply, pow_add, Finset.prod_mul_distrib]

lemma degree_add (ν η : ι → ℕ) : degree (ν + η) = degree ν + degree η := by
  simp [degree, Pi.add_apply, Finset.sum_add_distrib]

lemma tensorMoment_nonneg (m : ι → ℕ → ℝ) (hm : ∀ i r, 0 ≤ m i r)
    (ν : ι → ℕ) : 0 ≤ tensorMoment m ν :=
  Finset.prod_nonneg fun i _ => hm i (ν i)

/-- Coordinate moment comparison tensorizes without a loss in the number of variables. -/
theorem tensorMoment_add_le (m : ι → ℕ → ℝ) (α : ℝ)
    (hm : ∀ i r, 0 ≤ m i r)
    (hstep : ∀ i u v, m i (u + v) ≤ α ^ (2 * (u + v)) * m i u * m i v)
    (ν η : ι → ℕ) :
    tensorMoment m (ν + η) ≤
      α ^ (2 * (degree ν + degree η)) * tensorMoment m ν * tensorMoment m η := by
  calc
    tensorMoment m (ν + η) ≤
        ∏ i, (α ^ (2 * (ν i + η i)) * m i (ν i) * m i (η i)) := by
      exact Finset.prod_le_prod (fun i _ => hm i _) (fun i _ => hstep i _ _)
    _ = α ^ (2 * (degree ν + degree η)) * tensorMoment m ν * tensorMoment m η := by
      simp only [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, tensorMoment]
      rw [← Finset.mul_sum, Finset.sum_add_distrib]
      rfl

/-- The raw exponent cutoff produces the `α^(4D)` bound for every pair of monomials. -/
theorem tensorMoment_add_le_of_degree (m : ι → ℕ → ℝ) (α : ℝ) (hα : 1 ≤ α)
    (hm : ∀ i r, 0 ≤ m i r)
    (hstep : ∀ i u v, m i (u + v) ≤ α ^ (2 * (u + v)) * m i u * m i v)
    (ν η : ι → ℕ) (D : ℕ) (hν : degree ν ≤ D) (hη : degree η ≤ D) :
    tensorMoment m (ν + η) ≤ α ^ (4 * D) * tensorMoment m ν * tensorMoment m η := by
  refine (tensorMoment_add_le m α hm hstep ν η).trans ?_
  apply mul_le_mul_of_nonneg_right _ (tensorMoment_nonneg m hm η)
  apply mul_le_mul_of_nonneg_right _ (tensorMoment_nonneg m hm ν)
  exact pow_le_pow_right₀ hα (by omega)

/-- A finite positive sum in the original monomial basis. Duplicate exponents are permitted,
so multiplication and later identifications need not discard the provenance of a term. -/
def evaluate (c : κ → ℝ) (ν : κ → ι → ℕ) (z : ι → ℝ) : ℝ :=
  ∑ t, c t * monomial z (ν t)

/-- Algebraic heart of equation (8): coefficient signs and full exponent sums are retained.
The number of terms and number of independent coordinates introduce no additional factor. -/
theorem positive_sum_second_moment_le (m : ι → ℕ → ℝ) (α : ℝ) (hα : 1 ≤ α)
    (hm : ∀ i r, 0 ≤ m i r)
    (hstep : ∀ i u v, m i (u + v) ≤ α ^ (2 * (u + v)) * m i u * m i v)
    (c : κ → ℝ) (ν : κ → ι → ℕ) (hc : ∀ t, 0 ≤ c t)
    (D : ℕ) (hdegree : ∀ t, degree (ν t) ≤ D) :
    (∑ t, ∑ s, c t * c s * tensorMoment m (ν t + ν s)) ≤
      α ^ (4 * D) * (∑ t, c t * tensorMoment m (ν t)) ^ 2 := by
  calc
    _ ≤ ∑ t, ∑ s, c t * c s *
        (α ^ (4 * D) * tensorMoment m (ν t) * tensorMoment m (ν s)) := by
      apply Finset.sum_le_sum
      intro t _
      apply Finset.sum_le_sum
      intro s _
      exact mul_le_mul_of_nonneg_left
        (tensorMoment_add_le_of_degree m α hα hm hstep (ν t) (ν s) D
          (hdegree t) (hdegree s)) (mul_nonneg (hc t) (hc s))
    _ = _ := by
      simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      apply Finset.sum_congr rfl
      intro s _
      ring





section Probability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
/-- Product moments are consequences of independence of the original random variables. -/
theorem integral_monomial (Z : ι → Ω → ℝ) (hZ : ∀ i, Measurable (Z i))
    (hind : iIndepFun Z μ) (ν : ι → ℕ) :
    (∫ ω, monomial (fun i => Z i ω) ν ∂μ) =
      tensorMoment (fun i r => ∫ ω, Z i ω ^ r ∂μ) ν := by
  exact hind.integral_fun_prod_comp (fun i => (hZ i).aemeasurable)
    (fun i => (measurable_id.pow_const (ν i)).aestronglyMeasurable)

/-- Finite coordinate power moments imply integrability of every original monomial.
This uses the joint-law factorization, rather than postulating mixed-moment integrability. -/
theorem integrable_monomial (Z : ι → Ω → ℝ) (hZ : ∀ i, Measurable (Z i))
    (hind : iIndepFun Z μ) (hint : ∀ i r, Integrable (fun ω => Z i ω ^ r) μ)
    (ν : ι → ℕ) : Integrable (fun ω => monomial (fun i => Z i ω) ν) μ := by
  have hp : ∀ i, Integrable (fun x : ℝ => x ^ ν i) (μ.map (Z i)) := by
    intro i
    exact (integrable_map_measure (measurable_id.pow_const (ν i)).aestronglyMeasurable
      (hZ i).aemeasurable).mpr (hint i (ν i))
  have hprod := Integrable.fintype_prod hp
  rw [← hind.map_fun_eq_pi_map (fun i => (hZ i).aemeasurable)] at hprod
  exact hprod.comp_measurable (by fun_prop)

lemma evaluate_sq (c : κ → ℝ) (ν : κ → ι → ℕ) (z : ι → ℝ) :
    evaluate c ν z ^ 2 = ∑ t, ∑ s, (c t * c s) * monomial z (ν t + ν s) := by
  simp only [evaluate, pow_two, Finset.sum_mul, Finset.mul_sum, monomial_add]
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro s _
  ring

/-- Equation (8) on an arbitrary probability space, for independent nonnegative coordinates.
The sole analytic input is the explicitly displayed *one-coordinate* moment comparison.
The theorem proves independence factorization, mixed-moment integrability, and the entire
positive-coefficient assembly. Its loss `α^(4D)` is independent of both finite index sizes. -/
theorem integral_evaluate_sq_le (Z : ι → Ω → ℝ) (hZ : ∀ i, Measurable (Z i))
    (hind : iIndepFun Z μ) (hint : ∀ i r, Integrable (fun ω => Z i ω ^ r) μ)
    (hnonneg : ∀ i, ∀ᵐ ω ∂μ, 0 ≤ Z i ω)
    (α : ℝ) (hα : 1 ≤ α)
    (hstep : ∀ i u v, (∫ ω, Z i ω ^ (u + v) ∂μ) ≤
      α ^ (2 * (u + v)) * (∫ ω, Z i ω ^ u ∂μ) * (∫ ω, Z i ω ^ v ∂μ))
    (c : κ → ℝ) (ν : κ → ι → ℕ) (hc : ∀ t, 0 ≤ c t)
    (D : ℕ) (hdegree : ∀ t, degree (ν t) ≤ D) :
    (∫ ω, evaluate c ν (fun i => Z i ω) ^ 2 ∂μ) ≤
      α ^ (4 * D) * (∫ ω, evaluate c ν (fun i => Z i ω) ∂μ) ^ 2 := by
  have hmono := integrable_monomial Z hZ hind hint
  have hmean : (∫ ω, evaluate c ν (fun i => Z i ω) ∂μ) =
      ∑ t, c t * tensorMoment (fun i r => ∫ ω, Z i ω ^ r ∂μ) (ν t) := by
    simp only [evaluate]
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro t _
      rw [integral_const_mul, integral_monomial Z hZ hind]
    · intro t _
      exact (hmono (ν t)).const_mul (c t)
  have hsquare : (∫ ω, evaluate c ν (fun i => Z i ω) ^ 2 ∂μ) =
      ∑ t, ∑ s, c t * c s *
        tensorMoment (fun i r => ∫ ω, Z i ω ^ r ∂μ) (ν t + ν s) := by
    simp_rw [evaluate_sq]
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro t _
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro s _
        rw [integral_const_mul, integral_monomial Z hZ hind]
      · intro s _
        exact (hmono (ν t + ν s)).const_mul (c t * c s)
    · intro t _
      exact integrable_finsetSum _ fun s _ =>
        (hmono (ν t + ν s)).const_mul (c t * c s)
  rw [hsquare, hmean]
  apply positive_sum_second_moment_le _ α hα _ hstep c ν hc D hdegree
  intro i r
  exact integral_nonneg_of_ae ((hnonneg i).mono fun ω hω => pow_nonneg hω r)

end Probability






section Algebra

variable {τ : Type*} [Fintype τ]

/-- Addition concatenates the original positive families without merging their terms. -/
theorem evaluate_add (c : κ → ℝ) (ν : κ → ι → ℕ)
    (d : τ → ℝ) (η : τ → ι → ℕ) (z : ι → ℝ) :
    evaluate (Sum.elim c d) (Sum.elim ν η) z = evaluate c ν z + evaluate d η z := by
  simp [evaluate, Fintype.sum_sum_type]

/-- Multiplication retains the ordered pair of source terms and adds full raw exponents. -/
theorem evaluate_mul (c : κ → ℝ) (ν : κ → ι → ℕ)
    (d : τ → ℝ) (η : τ → ι → ℕ) (z : ι → ℝ) :
    evaluate (fun t : κ × τ => c t.1 * d t.2)
        (fun t => ν t.1 + η t.2) z = evaluate c ν z * evaluate d η z := by
  simp only [evaluate, Fintype.sum_prod_type, monomial_add,
    Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro s _
  ring

omit [Fintype κ] [Fintype τ] in
/-- A product of positive families remains positive coefficient by coefficient. -/
lemma mul_coeff_nonneg (c : κ → ℝ) (d : τ → ℝ)
    (hc : ∀ t, 0 ≤ c t) (hd : ∀ s, 0 ≤ d s) (t : κ × τ) :
    0 ≤ c t.1 * d t.2 := mul_nonneg (hc t.1) (hd t.2)

omit [Fintype κ] [Fintype τ] in
/-- Raw degree is charged additively when another interaction is multiplied in. -/
lemma mul_degree_le (ν : κ → ι → ℕ) (η : τ → ι → ℕ) (D E : ℕ)
    (hν : ∀ t, degree (ν t) ≤ D) (hη : ∀ s, degree (η s) ≤ E) (t : κ × τ) :
    degree (ν t.1 + η t.2) ≤ D + E := by
  rw [degree_add]
  exact Nat.add_le_add (hν t.1) (hη t.2)

omit [Fintype κ] in
/-- Any restriction of the original term set preserves coefficient positivity.
In particular, selecting one original exponent-parity class is permitted. -/
lemma restrict_coeff_nonneg (c : κ → ℝ) (hc : ∀ t, 0 ≤ c t)
    (P : κ → Prop) [DecidablePred P] (t : κ) : 0 ≤ if P t then c t else 0 := by
  split_ifs
  · exact hc t
  · exact le_rfl

/-- Positive coefficients evaluated at nonnegative magnitudes are nonnegative. -/
lemma evaluate_nonneg (c : κ → ℝ) (ν : κ → ι → ℕ) (z : ι → ℝ)
    (hc : ∀ t, 0 ≤ c t) (hz : ∀ i, 0 ≤ z i) : 0 ≤ evaluate c ν z := by
  apply Finset.sum_nonneg
  intro t _
  exact mul_nonneg (hc t) (Finset.prod_nonneg fun i _ => pow_nonneg (hz i) _)

end Algebra





section ScalarDoubling

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Cauchy--Schwarz in a form involving ordinary integrals and natural squares. -/
theorem integral_mul_sq_le (f g : Ω → ℝ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ ω, f ω * g ω ∂μ) ^ 2 ≤
      (∫ ω, f ω ^ 2 ∂μ) * (∫ ω, g ω ^ 2 ∂μ) := by
  have hi (a b : Ω → ℝ) (ha : MemLp a 2 μ) (hb : MemLp b 2 μ) :
      inner ℝ (ha.toLp a) (hb.toLp b) = ∫ ω, a ω * b ω ∂μ := by
    apply integral_congr_ae
    filter_upwards [ha.coeFn_toLp, hb.coeFn_toLp] with ω hωa hωb
    simp [hωa, hωb, mul_comm]
  have hcs := real_inner_mul_inner_self_le (hf.toLp f) (hg.toLp g)
  rw [hi f g hf hg, hi f f hf hf, hi g g hg hg] at hcs
  simpa only [pow_two] using hcs

variable [IsProbabilityMeasure μ]

/-- Natural-power doubling yields a stronger pair-moment bound than equation (7).
Cauchy--Schwarz avoids both the logarithmic interpolation and entropy estimate in the source. -/
theorem moment_add_le_of_doubling (Z : Ω → ℝ)
    (hint : ∀ r : ℕ, Integrable (fun ω => Z ω ^ r) μ)
    (hnonneg : ∀ᵐ ω ∂μ, 0 ≤ Z ω) (α : ℝ) (hα : 1 ≤ α)
    (hdouble : ∀ r : ℕ, 1 ≤ r → (∫ ω, Z ω ^ (2 * r) ∂μ) ≤
      α ^ (2 * r) * (∫ ω, Z ω ^ r ∂μ) ^ 2) (u v : ℕ) :
    (∫ ω, Z ω ^ (u + v) ∂μ) ≤
      α ^ (u + v) * (∫ ω, Z ω ^ u ∂μ) * (∫ ω, Z ω ^ v ∂μ) := by
  have hm (r : ℕ) : 0 ≤ ∫ ω, Z ω ^ r ∂μ :=
    integral_nonneg_of_ae (hnonneg.mono fun ω hω => pow_nonneg hω r)
  have hd (r : ℕ) : (∫ ω, Z ω ^ (2 * r) ∂μ) ≤
      α ^ (2 * r) * (∫ ω, Z ω ^ r ∂μ) ^ 2 := by
    by_cases hr : r = 0
    · simp [hr]
    · exact hdouble r (by omega)
  have hp (r : ℕ) : MemLp (fun ω => Z ω ^ r) 2 μ := by
    apply (memLp_two_iff_integrable_sq (hint r).aestronglyMeasurable).mpr
    simpa only [← pow_mul, Nat.mul_comm r 2] using hint (2 * r)
  have hcs := integral_mul_sq_le (fun ω => Z ω ^ u) (fun ω => Z ω ^ v) (hp u) (hp v)
  simp only [← pow_add, ← pow_mul, Nat.mul_comm u 2, Nat.mul_comm v 2] at hcs
  have hprod := mul_le_mul (hd u) (hd v) (hm (2 * v))
    (mul_nonneg (pow_nonneg (le_trans zero_le_one hα) _) (sq_nonneg _))
  have hsq : (∫ ω, Z ω ^ (u + v) ∂μ) ^ 2 ≤
      (α ^ (u + v) * (∫ ω, Z ω ^ u ∂μ) * (∫ ω, Z ω ^ v ∂μ)) ^ 2 := by
    refine (hcs.trans hprod).trans_eq ?_
    have he (r : ℕ) : α ^ (2 * r) = (α ^ r) ^ 2 := by
      rw [Nat.mul_comm 2 r, pow_mul]
    rw [he u, he v, pow_add]
    ring
  exact (sq_le_sq₀ (hm (u + v))
    (mul_nonneg (mul_nonneg (pow_nonneg (le_trans zero_le_one hα) _) (hm u)) (hm v))).mp hsq

/-- The complete positive-polynomial second-moment step from scalar natural-power doubling.
Unlike `integral_evaluate_sq_le`, this theorem does not assume a pair-moment comparison. -/
theorem integral_evaluate_sq_le_of_doubling (Z : ι → Ω → ℝ)
    (hZ : ∀ i, Measurable (Z i)) (hind : iIndepFun Z μ)
    (hint : ∀ i r, Integrable (fun ω => Z i ω ^ r) μ)
    (hnonneg : ∀ i, ∀ᵐ ω ∂μ, 0 ≤ Z i ω) (α : ℝ) (hα : 1 ≤ α)
    (hdouble : ∀ i r, 1 ≤ r → (∫ ω, Z i ω ^ (2 * r) ∂μ) ≤
      α ^ (2 * r) * (∫ ω, Z i ω ^ r ∂μ) ^ 2)
    (c : κ → ℝ) (ν : κ → ι → ℕ) (hc : ∀ t, 0 ≤ c t)
    (D : ℕ) (hdegree : ∀ t, degree (ν t) ≤ D) :
    (∫ ω, evaluate c ν (fun i => Z i ω) ^ 2 ∂μ) ≤
      α ^ (4 * D) * (∫ ω, evaluate c ν (fun i => Z i ω) ∂μ) ^ 2 := by
  apply integral_evaluate_sq_le Z hZ hind hint hnonneg α hα _ c ν hc D hdegree
  intro i u v
  refine (moment_add_le_of_doubling (Z i) (hint i) (hnonneg i) α hα (hdouble i) u v).trans ?_
  apply mul_le_mul_of_nonneg_right _
    (integral_nonneg_of_ae ((hnonneg i).mono fun ω hω => pow_nonneg hω v))
  apply mul_le_mul_of_nonneg_right _
    (integral_nonneg_of_ae ((hnonneg i).mono fun ω hω => pow_nonneg hω u))
  exact pow_le_pow_right₀ hα (by omega)

end ScalarDoubling

end PositivePolynomial
end MI32

