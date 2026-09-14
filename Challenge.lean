import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The original general-law MI-32 target

These are ordinary definitions of the quantities in the source problem.
In particular `moment` is meaningful below exponent one, the norm is the
Euclidean operator norm, and one deterministic set deletes both axes.
No analytic estimate or comparison theorem is part of an input structure.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace MI32

universe u

/-- The absolute moment functional, including positive exponents below one. -/
def moment {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω)
    (p : ℝ) (Z : Ω → ℝ) : ℝ :=
  (∫ ω, |Z ω| ^ p ∂μ) ^ (1 / p)

/-- The spectral norm through the actual operator on Euclidean coordinate spaces. -/
def spectralNorm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ‖(Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap) A‖

/-- Sum of the maximum row and column standard-deviation scales. -/
def varianceScale {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (X : Ω → Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  sSup (Set.range (fun i : Fin n =>
    Real.sqrt (∑ j, ∫ ω, (X ω i j) ^ 2 ∂μ))) +
  sSup (Set.range (fun j : Fin n =>
    Real.sqrt (∑ i, ∫ ω, (X ω i j) ^ 2 ∂μ)))

/-- Bilinear form after deleting the same fixed index set from both axes. -/
def deletedBilinear {Ω : Type u} {n : ℕ}
    (X : Ω → Matrix (Fin n) (Fin n) ℝ) (I : Finset (Fin n))
    (s t : EuclideanSpace ℝ (Fin n)) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.univ \ I, ∑ j ∈ Finset.univ \ I, X ω i j * s i * t j

/-- The supremum is over deterministic Euclidean unit-ball test vectors,
outside the random-variable moment. -/
def weakMoment {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (X : Ω → Matrix (Fin n) (Fin n) ℝ)
    (I : Finset (Fin n)) (p : ℝ) : ℝ :=
  sSup {v : ℝ | ∃ s t : EuclideanSpace ℝ (Fin n),
    ‖s‖ ≤ 1 ∧ ‖t‖ ≤ 1 ∧ v = moment μ p (deletedBilinear X I s t)}

/-- The literal max-min weak moment in MI-32. At k=1 the exponent is log 2.
The finite minimum is over deterministic original index sets of size at most k. -/
def deletionScale {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (X : Ω → Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  sSup {v : ℝ | ∃ k : ℕ, 1 ≤ k ∧ k ≤ n ∧
    v = sInf {w : ℝ | ∃ I : Finset (Fin n), I.card ≤ k ∧
      w = weakMoment μ X I (Real.log (k + 1 : ℕ))}}

/-- Original independent centered real entries, with all positive absolute
moments finite and the stipulated doubling at every real order r≥1.
This imposes neither identical distribution nor symmetry of entry laws. -/
def RegularEntries {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (α : ℝ) (X : Ω → Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ i j, Measurable (fun ω => X ω i j)) ∧
  ProbabilityTheory.iIndepFun (fun e : Fin n × Fin n => fun ω => X ω e.1 e.2) μ ∧
  (∀ i j, ∫ ω, X ω i j ∂μ = 0) ∧
  (∀ i j (p : ℝ), 0 < p → Integrable (fun ω => |X ω i j| ^ p) μ) ∧
  (∀ i j (r : ℝ), 1 ≤ r →
    moment μ (2 * r) (fun ω => X ω i j) ≤
      α * moment μ r (fun ω => X ω i j))

/-- The full dimension- and law-uniform upper-bound assertion at given constants.
The probability space is arbitrary; it is not restricted to finite laws. -/
def UpperBoundAt (α C : ℝ) : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (Ω : Type u) (mΩ : MeasurableSpace Ω)
    (μ : @Measure Ω mΩ), @IsProbabilityMeasure Ω mΩ μ →
    ∀ (X : Ω → Matrix (Fin n) (Fin n) ℝ),
      @RegularEntries Ω mΩ n μ α X →
      (∫ ω, spectralNorm (X ω) ∂μ) ≤
        C * (varianceScale μ X + deletionScale μ X)

/-- **MI-32: spectral norms of independent entries with regular moment growth,
upper bound.** For every regularity parameter `α ≥ 1` there is a constant
`C > 0`, depending only on `α` and not on the dimension or on the individual
entry laws, such that every `n × n` random matrix `X` with independent
mean-zero real entries whose absolute moments double regularly, meaning
`moment μ (2 * r) (X i j) ≤ α * moment μ r (X i j)` at every real order
`r ≥ 1`, satisfies

`∫ ‖X‖ ≤ C * (varianceScale μ X + deletionScale μ X)`.

Here `‖·‖` is the Euclidean operator norm, `varianceScale` is the sum of the
largest row and the largest column standard deviation, and `deletionScale` is
the max-min weak moment of the source problem: the maximum over budgets
`1 ≤ k ≤ n` of the minimum, over deterministic index sets `I` of cardinality at
most `k`, of the bilinear weak moment at order `Real.log (k + 1)` after deleting
`I` from both axes. The probability space is arbitrary rather than finite, one
and the same deterministic set deletes rows and columns, and the `k = 1` order
`Real.log 2 < 1` is kept literally, so `moment` is used below exponent one.

The `sorry` below is the **intentional Challenge hole**. This module states the
result and deliberately proves nothing; it is the small statement of record that
a mathematical reader is expected to audit. The corresponding `MI32.main_upper`
in the selected Solution module is **not** a hole: it is completed and
mechanically verified, carrying a full proof whose transitive axiom audit
reports only `propext`, `Classical.choice` and `Quot.sound`. Nothing in this
file is evidence for that proof; the comparison of the two declarations is what
establishes that the Solution proves this statement. -/
theorem main_upper (α : ℝ) (hα : 1 ≤ α) :
    ∃ C : ℝ, 0 < C ∧ UpperBoundAt.{u} α C := by
  sorry

end MI32
