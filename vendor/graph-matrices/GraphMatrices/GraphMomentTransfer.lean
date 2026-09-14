import GraphMatrices.FiniteLocalMoments
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Mul

/-!
# Exact limited-marginal transfer for finite matrix trace moments

Each matrix entry is assumed to have a bounded local interaction degree.
From that entrywise property, this module proves the degree of matrix products,
Gram powers, traces, and squared traces. It then proves expectation matching
under matching local marginals. The desired trace-moment identity is a
conclusion, never a hypothesis. The graph-specific entry-degree proof is a
separate bridge in `SignGraphDegree.lean`.
-/

open scoped BigOperators
open GraphMatrices.FiniteLocalMoments

namespace GraphMatrices.GraphMomentTransfer

noncomputable section

variable {κ β I J K : Type*} [DecidableEq κ]

/-- An entrywise local-degree condition on an actual matrix-valued observable. -/
def HasEntryDegree (d : ℕ) (A : (κ → β) → Matrix I J ℝ) : Prop :=
  ∀ i j, HasLocalDegree d (fun x => A x i j)

namespace HasEntryDegree

theorem mono {d e : ℕ} {A : (κ → β) → Matrix I J ℝ}
    (hA : HasEntryDegree d A) (hde : d ≤ e) : HasEntryDegree e A := by
  intro i j
  exact (hA i j).mono hde

theorem transpose {d : ℕ} {A : (κ → β) → Matrix I J ℝ}
    (hA : HasEntryDegree d A) :
    HasEntryDegree d (fun x => (A x).transpose) := by
  intro j i
  exact hA i j

/-- Matrix multiplication adds entry degrees; the intermediate index is summed. -/
theorem mul [Fintype J] {d e : ℕ}
    {A : (κ → β) → Matrix I J ℝ} {B : (κ → β) → Matrix J K ℝ}
    (hA : HasEntryDegree d A) (hB : HasEntryDegree e B) :
    HasEntryDegree (d + e) (fun x => A x * B x) := by
  intro i k
  simpa only [Matrix.mul_apply] using
    HasLocalDegree.sum_fintype (fun j x => A x i j * B x j k)
      (fun j => (hA i j).mul (hB j k))

/-- Every entry of a natural matrix power has at most `q*d` local degree. -/
theorem pow [Fintype I] [DecidableEq I] {d : ℕ}
    {A : (κ → β) → Matrix I I ℝ} (hA : HasEntryDegree d A) (q : ℕ) :
    HasEntryDegree (q * d) (fun x => (A x) ^ q) := by
  induction q with
  | zero =>
    intro i j
    simpa only [Nat.zero_mul, pow_zero] using
      (HasLocalDegree.constant (ι := κ) (α := β) 0 ((1 : Matrix I I ℝ) i j))
  | succ q ih =>
    simpa only [Nat.succ_mul, pow_succ] using ih.mul hA

/-- Taking the trace does not increase local degree. -/
theorem trace [Fintype I] {d : ℕ}
    {A : (κ → β) → Matrix I I ℝ} (hA : HasEntryDegree d A) :
    HasLocalDegree d (fun x => (A x).trace) := by
  simpa only [Matrix.trace, Matrix.diag_apply] using
    HasLocalDegree.sum_fintype (fun i x => A x i i) (fun i => hA i i)

/-- The row Gram matrix has entry degree at most twice the original degree. -/
theorem gram [Fintype J] {d : ℕ}
    {A : (κ → β) → Matrix I J ℝ} (hA : HasEntryDegree d A) :
    HasEntryDegree (2 * d) (fun x => A x * (A x).transpose) := by
  simpa only [two_mul] using hA.mul hA.transpose

/-- The column Gram matrix has the same degree bound. -/
theorem transposeGram [Fintype I] {d : ℕ}
    {A : (κ → β) → Matrix I J ℝ} (hA : HasEntryDegree d A) :
    HasEntryDegree (2 * d) (fun x => (A x).transpose * A x) := by
  simpa only [two_mul] using hA.transpose.mul hA

end HasEntryDegree

/-- Ordinary trace powers have local degree at most `q*d`. -/
theorem tracePower_degree [Fintype I] [DecidableEq I]
    {A : (κ → β) → Matrix I I ℝ} {d : ℕ}
    (hA : HasEntryDegree d A) (q : ℕ) :
    HasLocalDegree (q * d) (fun x => ((A x) ^ q).trace) :=
  (hA.pow q).trace

/-- Every entry of `(A Aᵀ)^q` has local degree at most `2*q*d`. -/
theorem gramPower_entry_degree [Fintype I] [Fintype J] [DecidableEq I]
    {A : (κ → β) → Matrix I J ℝ} {d : ℕ}
    (hA : HasEntryDegree d A) (q : ℕ) :
    HasEntryDegree (2 * q * d) (fun x => (A x * (A x).transpose) ^ q) := by
  have h := hA.gram.pow q
  have hdegree : q * (2 * d) = 2 * q * d := by ring
  simpa only [hdegree] using h

/-- The actual row-Gram trace moment has local degree at most `2*q*d`. -/
theorem gramTracePower_degree [Fintype I] [Fintype J] [DecidableEq I]
    {A : (κ → β) → Matrix I J ℝ} {d : ℕ}
    (hA : HasEntryDegree d A) (q : ℕ) :
    HasLocalDegree (2 * q * d)
      (fun x => ((A x * (A x).transpose) ^ q).trace) :=
  (gramPower_entry_degree hA q).trace

/-- The actual column-Gram trace moment has the same degree bound. -/
theorem transposeGramTracePower_degree [Fintype I] [Fintype J] [DecidableEq J]
    {A : (κ → β) → Matrix I J ℝ} {d : ℕ}
    (hA : HasEntryDegree d A) (q : ℕ) :
    HasLocalDegree (2 * q * d)
      (fun x => (((A x).transpose * A x) ^ q).trace) := by
  have h := (hA.transposeGram.pow q).trace
  have hdegree : q * (2 * d) = 2 * q * d := by ring
  simpa only [hdegree] using h

/-- Squared row-Gram traces have degree `4*q*d`, the variance-transfer budget. -/
theorem gramTracePower_square_degree [Fintype I] [Fintype J] [DecidableEq I]
    {A : (κ → β) → Matrix I J ℝ} {d : ℕ}
    (hA : HasEntryDegree d A) (q : ℕ) :
    HasLocalDegree (4 * q * d)
      (fun x => (((A x * (A x).transpose) ^ q).trace) ^ 2) := by
  have h := (gramTracePower_degree hA q).mul (gramTracePower_degree hA q)
  have hdegree : 2 * q * d + 2 * q * d = 4 * q * d := by ring
  simpa only [hdegree, pow_two] using h

/-- Subtracting a deterministic center leaves the same squared-trace budget. -/
theorem gramTracePower_centered_square_degree [Fintype I] [Fintype J] [DecidableEq I]
    {A : (κ → β) → Matrix I J ℝ} {d : ℕ}
    (hA : HasEntryDegree d A) (q : ℕ) (c : ℝ) :
    HasLocalDegree (4 * q * d)
      (fun x => (((A x * (A x).transpose) ^ q).trace - c) ^ 2) := by
  have hc := (gramTracePower_degree hA q).sub (HasLocalDegree.constant (2 * q * d) c)
  have h := hc.mul hc
  have hdegree : 2 * q * d + 2 * q * d = 4 * q * d := by ring
  simpa only [hdegree, pow_two] using h

section ExpectationTransfer

variable [Fintype κ] [Fintype β]

/-- Exact transfer of ordinary trace-power expectations under local marginals. -/
theorem expect_tracePower_eq [Fintype I] [DecidableEq I]
    {μ ν : FiniteLaw (κ → β)} {A : (κ → β) → Matrix I I ℝ} {d q : ℕ}
    (hA : HasEntryDegree d A) (hmatch : MatchesUpTo μ ν (q * d)) :
    μ.expect (fun x => ((A x) ^ q).trace) =
      ν.expect (fun x => ((A x) ^ q).trace) :=
  HasLocalDegree.expect_eq_of_matchesUpTo hmatch (tracePower_degree hA q)

/--
Matching all coordinate marginals of order at most `2*q*d` transfers the actual
trace of the `q`th row-Gram power. No moment-matching premise is used.
-/
theorem expect_gramTracePower_eq [Fintype I] [Fintype J] [DecidableEq I]
    {μ ν : FiniteLaw (κ → β)} {A : (κ → β) → Matrix I J ℝ} {d q : ℕ}
    (hA : HasEntryDegree d A) (hmatch : MatchesUpTo μ ν (2 * q * d)) :
    μ.expect (fun x => ((A x * (A x).transpose) ^ q).trace) =
      ν.expect (fun x => ((A x * (A x).transpose) ^ q).trace) :=
  HasLocalDegree.expect_eq_of_matchesUpTo hmatch (gramTracePower_degree hA q)

/-- The `AᵀA` convention used in singular-value moments transfers as well. -/
theorem expect_transposeGramTracePower_eq [Fintype I] [Fintype J] [DecidableEq J]
    {μ ν : FiniteLaw (κ → β)} {A : (κ → β) → Matrix I J ℝ} {d q : ℕ}
    (hA : HasEntryDegree d A) (hmatch : MatchesUpTo μ ν (2 * q * d)) :
    μ.expect (fun x => (((A x).transpose * A x) ^ q).trace) =
      ν.expect (fun x => (((A x).transpose * A x) ^ q).trace) :=
  HasLocalDegree.expect_eq_of_matchesUpTo hmatch (transposeGramTracePower_degree hA q)

/-- Matching twice as many marginals transfers the second moment of the trace. -/
theorem expect_gramTracePower_square_eq [Fintype I] [Fintype J] [DecidableEq I]
    {μ ν : FiniteLaw (κ → β)} {A : (κ → β) → Matrix I J ℝ} {d q : ℕ}
    (hA : HasEntryDegree d A) (hmatch : MatchesUpTo μ ν (4 * q * d)) :
    μ.expect (fun x => (((A x * (A x).transpose) ^ q).trace) ^ 2) =
      ν.expect (fun x => (((A x * (A x).transpose) ^ q).trace) ^ 2) :=
  HasLocalDegree.expect_eq_of_matchesUpTo hmatch (gramTracePower_square_degree hA q)

/--
The variance of the trace transfers exactly. Both the means and centered second
moments are derived from marginal matching; equality of variances is not assumed.
-/
theorem variance_gramTracePower_eq [Fintype I] [Fintype J] [DecidableEq I]
    {μ ν : FiniteLaw (κ → β)} {A : (κ → β) → Matrix I J ℝ} {d q : ℕ}
    (hA : HasEntryDegree d A) (hmatch : MatchesUpTo μ ν (4 * q * d)) :
    μ.expect (fun x => (((A x * (A x).transpose) ^ q).trace -
      μ.expect (fun y => ((A y * (A y).transpose) ^ q).trace)) ^ 2) =
    ν.expect (fun x => (((A x * (A x).transpose) ^ q).trace -
      ν.expect (fun y => ((A y * (A y).transpose) ^ q).trace)) ^ 2) := by
  have hbudget : 2 * q * d ≤ 4 * q * d :=
    Nat.mul_le_mul_right d (Nat.mul_le_mul_right q (by decide : 2 ≤ 4))
  have hmean := expect_gramTracePower_eq hA (matchesUpTo_mono hmatch hbudget)
  rw [hmean]
  exact HasLocalDegree.expect_eq_of_matchesUpTo hmatch
    (gramTracePower_centered_square_degree hA q
      (ν.expect (fun y => ((A y * (A y).transpose) ^ q).trace)))

end ExpectationTransfer

end

end GraphMatrices.GraphMomentTransfer
