import GraphMatrices.GraphMatrix
import GraphMatrices.Walsh
import GraphMatrices.Basic
import GraphMatrices.FiniteLocalMoments
import GraphMatrices.GraphMomentTransfer

/-! Actual coordinate-degree bounds for injective sign graph matrices.
The primitive coordinates are unordered pairs; diagonal coordinates are unused. -/

namespace GraphMatrices

noncomputable section

variable {n r s : ℕ}

def fairBitLaw : FiniteLaw Bool where
  weight _ := 1 / 2
  weight_nonneg _ := by norm_num
  sum_weight := by norm_num

/-- Full independent signs, encoded by independent fair bits on unordered pairs. -/
def independentSignLaw {E : Type*} [Fintype E] [DecidableEq E] : FiniteLaw (E → Bool) :=
  FiniteLaw.independentProduct (fun _ => fairBitLaw)

theorem independentSignLaw_expect_eq_walsh {E : Type*} [Fintype E] [DecidableEq E]
    (f : (E → Bool) → ℝ) :
    independentSignLaw.expect f = Walsh.expectation f := by
  simp [FiniteLaw.expect, independentSignLaw, FiniteLaw.independentProduct,
    fairBitLaw, Walsh.expectation, div_eq_mul_inv, mul_comm]
  rw [← Finset.sum_mul, mul_comm]

def signInput (σ : Sym2 (Fin n) → Bool) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of (fun i j => if i = j then 0 else Walsh.sign (σ s(i, j)))

theorem signInput_symmetric (σ : Sym2 (Fin n) → Bool) :
    ∀ i j, signInput σ i j = signInput σ j i := by
  intro i j
  by_cases h : i = j
  · subst j
    rfl
  · simp only [signInput, Matrix.of_apply, if_neg h, if_neg (Ne.symm h), Sym2.eq_swap]

theorem signInput_isSignMatrix (σ : Sym2 (Fin n) → Bool) : IsSignMatrix (signInput σ) := by
  refine ⟨signInput_symmetric σ, ?_, ?_⟩
  · intro i
    simp [signInput]
  · intro i j hij
    simp [signInput, hij]

variable {α : Type*} [Fintype α] [DecidableEq α]

def signGraphMatrix (G : SimpleGraph α) (left : Fin r ↪ α) (right : Fin s ↪ α)
    (σ : Sym2 (Fin n) → Bool) :
    Matrix (Fin r → Fin n) (Fin s → Fin n) ℝ :=
  graphMatrix G left right (signInput σ) (signInput_symmetric σ)

open FiniteLocalMoments

def shapeEdgeCount (G : SimpleGraph α) : ℕ := by
  classical
  exact G.edgeFinset.card

/-- Each actual injective graph-matrix entry is a sum of observables depending
on at most the number of shape edges. This proves the entry-degree hypothesis
used by the generic matrix moment-transfer theorem. -/
theorem signGraphMatrix_entry_localDegree (G : SimpleGraph α)
    (left : Fin r ↪ α) (right : Fin s ↪ α)
    (row : Fin r → Fin n) (col : Fin s → Fin n) :
    HasLocalDegree (shapeEdgeCount G) (fun σ => signGraphMatrix G left right σ row col) := by
  classical
  unfold shapeEdgeCount
  unfold signGraphMatrix graphMatrix
  apply HasLocalDegree.sum_fintype
  intro φ
  apply HasLocalDegree.atom (G.edgeFinset.image (Sym2.map φ))
  · exact Finset.card_image_le
  · intro x y hxy
    split_ifs with h
    · apply Finset.prod_congr rfl
      intro e he
      have heq := hxy (Sym2.map φ e) (Finset.mem_image.mpr ⟨e, he, rfl⟩)
      induction e using Sym2.inductionOn with
      | _ a b =>
        simp only [edgeWeight_mk, Sym2.map_mk] at *
        simp only [signInput, Matrix.of_apply, heq]
    · rfl

def signGraphGramMoment (G : SimpleGraph α)
    (left : Fin r ↪ α) (right : Fin s ↪ α) (q : ℕ)
    (σ : Sym2 (Fin n) → Bool) : ℝ :=
  let A := signGraphMatrix G left right σ
  ((A * A.transpose) ^ q).trace

/-- Matching at most 2*q*e coordinate marginals transfers the actual
qth Gram trace moment of every finite injective sign graph matrix. -/
theorem signGraphMatrix_moment_transfer (G : SimpleGraph α)
    (left : Fin r ↪ α) (right : Fin s ↪ α) (q : ℕ)
    {μ ν : FiniteLaw (Sym2 (Fin n) → Bool)}
    (hmatch : MatchesUpTo μ ν (2 * q * shapeEdgeCount G)) :
    μ.expect (signGraphGramMoment G left right q) =
      ν.expect (signGraphGramMoment G left right q) := by
  exact GraphMomentTransfer.expect_gramTracePower_eq
    (fun row col => signGraphMatrix_entry_localDegree G left right row col) hmatch

/-- The fully independent sign baseline is a constructed product law, not an
assumed moment functional. -/
theorem signGraphMatrix_moment_eq_independent (G : SimpleGraph α)
    (left : Fin r ↪ α) (right : Fin s ↪ α) (q : ℕ)
    {μ : FiniteLaw (Sym2 (Fin n) → Bool)}
    (hmatch : MatchesUpTo μ independentSignLaw (2 * q * shapeEdgeCount G)) :
    μ.expect (signGraphGramMoment G left right q) =
      (independentSignLaw (E := Sym2 (Fin n))).expect (signGraphGramMoment G left right q) :=
  signGraphMatrix_moment_transfer G left right q hmatch

/-- Matching 4*q*e marginals also transfers the variance of the trace moment. -/
theorem signGraphMatrix_variance_transfer (G : SimpleGraph α)
    (left : Fin r ↪ α) (right : Fin s ↪ α) (q : ℕ)
    {μ ν : FiniteLaw (Sym2 (Fin n) → Bool)}
    (hmatch : MatchesUpTo μ ν (4 * q * shapeEdgeCount G)) :
    μ.expect (fun σ => (signGraphGramMoment G left right q σ -
      μ.expect (signGraphGramMoment G left right q)) ^ 2) =
    ν.expect (fun σ => (signGraphGramMoment G left right q σ -
      ν.expect (signGraphGramMoment G left right q)) ^ 2) := by
  exact GraphMomentTransfer.variance_gramTracePower_eq
    (fun row col => signGraphMatrix_entry_localDegree G left right row col) hmatch

end
end GraphMatrices
