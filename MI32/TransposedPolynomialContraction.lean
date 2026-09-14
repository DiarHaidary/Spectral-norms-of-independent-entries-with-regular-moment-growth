import MI32.ThinPolynomialInteraction
import MI32.AxisRestriction
import MI32.RawMultiplicationContraction

/-!
# Opposite matrix direction on the same original polynomial variables

Transposing the matrix only reindexes the original random coordinates by
`Prod.swap`. The raw exponent reindexing preserves exact evaluation and degree;
it neither resamples a variable nor introduces an independent transpose law.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace MI32.TransposedPolynomialContraction

open PositivePolynomial SymmetricPositiveCone ThinPolynomialInteraction

section Reindex

variable {E D A K : Type*} [Fintype E] [Fintype D] [Fintype K]

/-- Reindexing by a bijection preserves the original monomial exactly. -/
theorem monomial_reindex (e : D ≃ E) (z : E → ℝ) (ν : E → ℕ) :
    monomial (fun f => z (e f)) (fun f => ν (e f)) = monomial z ν := by
  exact e.prod_comp (fun f => z f ^ ν f)

/-- Total raw degree is invariant under a bijective renaming of original coordinates. -/
theorem degree_reindex (e : D ≃ E) (ν : E → ℕ) :
    degree (fun f => ν (e f)) = degree ν :=
  e.sum_comp ν

/-- The same original finite polynomial, with all coefficients retained. -/
theorem evaluate_reindex (e : D ≃ E) (c : K → ℝ) (ν : K → E → ℕ) (z : E → ℝ) :
    evaluate c (fun k f => ν k (e f)) (fun f => z (e f)) = evaluate c ν z := by
  simp only [evaluate, monomial_reindex]

/-- Actual Euclidean polynomial evaluation is unchanged by the variable reindexing. -/
theorem evaluateHilbert_reindex (e : D ≃ E) (c : A → K → ℝ)
    (ν : A → K → E → ℕ) (z : E → ℝ) :
    evaluateHilbert c (fun a k f => ν a k (e f)) (fun f => z (e f)) =
      evaluateHilbert c ν z := by
  ext a
  exact evaluate_reindex e (c a) (ν a) z

variable {Ω J : Type*} [Fintype A] [Fintype J] [DecidableEq A]

omit [Fintype A] [DecidableEq A] in
theorem polynomialVector_reindex (e : D ≃ E) (U : E → Ω → ℝ)
    (c : A → K → ℝ) (ν : A → K → E → ℕ) (ω : Ω) :
    polynomialVector (fun f => U (e f)) c (fun a k f => ν a k (e f)) ω =
      polynomialVector U c ν ω :=
  evaluateHilbert_reindex e c ν (fun f => U f ω)

/-- The original matrix action is unchanged by reindexing only the polynomial variables. -/
theorem action_reindex (e : D ≃ E) (X : A → J → Ω → ℝ) (U : E → Ω → ℝ)
    (c : A → K → ℝ) (ν : A → K → E → ℕ) (ω : Ω) :
    action X (fun f => U (e f)) c (fun a k f => ν a k (e f)) ω =
      action X U c ν ω := by
  unfold action
  rw [polynomialVector_reindex]

end Reindex

section OriginalEntries

variable {Ω R C K : Type*} [MeasurableSpace Ω] [Fintype R] [Fintype C] [Fintype K]
    [DecidableEq R] [DecidableEq C] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Full original exponent vectors are swapped together with the original entry labels. -/
def swapExponent (ν : C → K → R × C → ℕ) (j : C) (k : K) (e : C × R) : ℕ :=
  ν j k (e.2, e.1)

omit [Fintype K] [DecidableEq R] [DecidableEq C] in
theorem degree_swapExponent (ν : C → K → R × C → ℕ) (j : C) (k : K) :
    degree (swapExponent ν j k) = degree (ν j k) :=
  degree_reindex (Equiv.prodComm C R) (ν j k)

omit [MeasurableSpace Ω] [DecidableEq R] [DecidableEq C] in
theorem polynomialVector_swap (X : R → C → Ω → ℝ)
    (c : C → K → ℝ) (ν : C → K → R × C → ℕ) (ω : Ω) :
    polynomialVector (fun e : C × R => X e.2 e.1) c (swapExponent ν) ω =
      polynomialVector (fun e : R × C => X e.1 e.2) c ν ω :=
  polynomialVector_reindex (Equiv.prodComm C R) (fun e : R × C => X e.1 e.2) c ν ω

omit [MeasurableSpace Ω] [DecidableEq R] in
theorem action_swap (X : R → C → Ω → ℝ)
    (c : C → K → ℝ) (ν : C → K → R × C → ℕ) (ω : Ω) :
    action (fun j i => X i j) (fun e : C × R => X e.2 e.1) c (swapExponent ν) ω =
      action (fun j i => X i j) (fun e : R × C => X e.1 e.2) c ν ω :=
  action_reindex (Equiv.prodComm C R) (fun j i => X i j)
    (fun e : R × C => X e.1 e.2) c ν ω

/-- Full opposite-direction action on a polynomial in the same original entry
family. Independence, scalar regularity, and weak tests for the transposed
indexing are all derived from the original hypotheses. No second law is used. -/
theorem action_l2_le
    (X : R → C → Ω → ℝ) (hX : ∀ i j, Measurable (X i j))
    (hind : iIndepFun (fun e : R × C => X e.1 e.2) μ)
    (hsym : ∀ i j, IdentDistrib (X i j) (fun ω => -X i j ω) μ μ)
    (hint : ∀ i j (p : ℝ), 0 < p → Integrable (fun ω => |X i j ω| ^ p) μ)
    (α : ℝ) (hα : 1 ≤ α)
    (hregular : ∀ i j (r : ℝ), 1 ≤ r →
      moment μ (2 * r) (X i j) ≤ α * moment μ r (X i j))
    (q : ℕ) (hq : 1 ≤ q)
    (B : ℝ) (hB : 0 ≤ B)
    (hrow : ∀ i, (∑ j, ∫ ω, X i j ω ^ 2 ∂μ) ≤ B ^ 2)
    (hcol : ∀ j, (∑ i, ∫ ω, X i j ω ^ 2 ∂μ) ≤ B ^ 2)
    (W : ℝ) (hW : 0 ≤ W)
    (hweak : ∀ s : EuclideanSpace ℝ R, ‖s‖ ≤ 1 →
      ∀ t : EuclideanSpace ℝ C, ‖t‖ ≤ 1 →
        moment μ (2 * (q : ℝ)) (ThinMatrix.bilinear X s t) ≤ W)
    (c : C → K → ℝ) (ν : C → K → R × C → ℕ) (hc : ∀ j t, 0 ≤ c j t)
    (d : ℕ) (hdegree : ∀ j t, degree (ν j t) ≤ d) (hdq : d < q) :
    Integrable (fun ω => ‖action (fun j i => X i j)
      (fun e : R × C => X e.1 e.2) c ν ω‖ ^ 2) μ ∧
      moment μ 2 (fun ω => ‖action (fun j i => X i j)
        (fun e : R × C => X e.1 e.2) c ν ω‖) ≤
        RawMultiplicationContraction.contractionConstant α B W *
          moment μ 2 (fun ω => ‖polynomialVector (fun e : R × C => X e.1 e.2) c ν ω‖) := by
  have hindT : iIndepFun (fun e : C × R => X e.2 e.1) μ :=
    hind.precomp Prod.swap_injective
  have hweakT : ∀ s : EuclideanSpace ℝ C, ‖s‖ ≤ 1 →
      ∀ t : EuclideanSpace ℝ R, ‖t‖ ≤ 1 →
        moment μ (2 * (q : ℝ)) (ThinMatrix.bilinear (fun j i => X i j) s t) ≤ W := by
    intro s hs t ht
    rw [AxisRestriction.thin_bilinear_transpose]
    exact hweak t ht s hs
  have hdegreeT : ∀ j t, degree (swapExponent ν j t) ≤ d := by
    intro j t
    rw [degree_swapExponent]
    exact hdegree j t
  have h := RawMultiplicationContraction.action_l2_le
    (fun j i => X i j) (fun j i => hX i j) hindT (fun j i => hsym i j)
    (fun j i p hp => hint i j p hp) α hα (fun j i r hr => hregular i j r hr)
    q hq B hB hcol hrow W hW hweakT c (swapExponent ν) hc d hdegreeT hdq
  simpa only [action_swap, polynomialVector_swap] using h

end OriginalEntries

end MI32.TransposedPolynomialContraction
