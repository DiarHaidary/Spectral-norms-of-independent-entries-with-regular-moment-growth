import GraphMatrices.GraphMatrix
import GraphMatrices.FiniteProbability
import GraphMatrices.SpectralNorm
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! Exact random-role coloring of globally injective graph embeddings. -/

open scoped BigOperators

namespace GraphMatrices.RoleColoring

noncomputable section

variable {α β : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [Fintype β] [DecidableEq β]

/-- Uniform probability on a nonempty finite set of colors. -/
def uniformLaw (α : Type*) [Fintype α] [Nonempty α] : FiniteLaw α where
  weight _ := (Fintype.card α : ℝ)⁻¹
  weight_nonneg _ := inv_nonneg.mpr (Nat.cast_nonneg _)
  sum_weight := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

/-- Each ambient label receives an independent uniform role color. -/
def colorLaw : FiniteLaw (β → α) :=
  FiniteLaw.independentProduct (fun _ => uniformLaw α)

/-- A label assignment has exactly its prescribed role colors. -/
def RespectsColors (φ : α → β) (χ : β → α) : Prop := ∀ x, χ (φ x) = x

/-- The exact coloring mass of every injective assignment. -/
theorem probability_respectsColors (φ : α → β) (hφ : Function.Injective φ) :
    colorLaw.prob {χ : β → α | RespectsColors φ χ} =
      ((Fintype.card α : ℝ)⁻¹) ^ Fintype.card α := by
  classical
  let event : β → Set α := fun j =>
    if j ∈ Set.range φ then {Function.invFun φ j} else Set.univ
  have hinv := Function.leftInverse_invFun hφ
  have hevent : {χ : β → α | RespectsColors φ χ} = FiniteLaw.cylinder event := by
    ext χ
    constructor
    · intro hc j
      by_cases hj : j ∈ Set.range φ
      · obtain ⟨x, rfl⟩ := hj
        simpa [event, hinv x, Set.mem_range_self] using hc x
      · change χ j ∈ (if j ∈ Set.range φ then _ else Set.univ)
        rw [if_neg hj]
        trivial
    · intro hc x
      have hx := hc (φ x)
      simpa [event, hinv x, Set.mem_range_self] using hx
  rw [hevent, colorLaw, FiniteLaw.prob_independentProduct_cylinder]
  have hprod :
      (∏ x : α, (Fintype.card α : ℝ)⁻¹) =
      ∏ j : β, (uniformLaw α).prob (event j) := by
    apply Fintype.prod_of_injective φ hφ
    · intro j hj
      change (uniformLaw α).prob (if j ∈ Set.range φ then _ else Set.univ) = 1
      rw [if_neg hj, FiniteLaw.prob_univ]
    · intro x
      simp [event, FiniteLaw.prob_singleton, uniformLaw]
  rw [← hprod]
  simp

omit [Fintype α] [DecidableEq α] [Nonempty α] [Fintype β] [DecidableEq β] in
theorem respectsColors_injective {φ : α → β} {χ : β → α}
    (h : RespectsColors φ χ) : Function.Injective φ := by
  intro x y hxy
  calc x = χ (φ x) := (h x).symm
       _ = χ (φ y) := congrArg χ hxy
       _ = y := h y

variable {n r s : ℕ}

/-- The colored matrix lives in the same ambient boundary spaces as the original. -/
def coloredGraphMatrix (G : SimpleGraph α)
    (left : Fin r ↪ α) (right : Fin s ↪ α)
    (W : Matrix (Fin n) (Fin n) ℝ) (hW : ∀ i j, W i j = W j i)
    (χ : Fin n → α) : Matrix (Fin r → Fin n) (Fin s → Fin n) ℝ := by
  classical
  exact fun row col => ∑ φ : α → Fin n,
    if Function.Injective φ ∧
        (∀ i, φ (left i) = row i) ∧ (∀ j, φ (right j) = col j)
    then (∏ e ∈ G.edgeFinset, edgeWeight W hW φ e) *
      FiniteLaw.indicator {χ | RespectsColors φ χ} χ
    else 0

/-- Entrywise expected colored matrix; the probability space is explicit. -/
theorem expect_coloredGraphMatrix (G : SimpleGraph α)
    (left : Fin r ↪ α) (right : Fin s ↪ α)
    (W : Matrix (Fin n) (Fin n) ℝ) (hW : ∀ i j, W i j = W j i)
    (row : Fin r → Fin n) (col : Fin s → Fin n) :
    colorLaw.expect (fun χ => coloredGraphMatrix G left right W hW χ row col) =
      ((Fintype.card α : ℝ)⁻¹) ^ Fintype.card α *
        graphMatrix G left right W hW row col := by
  classical
  simp only [coloredGraphMatrix, FiniteLaw.expect, Finset.mul_sum]
  rw [Finset.sum_comm]
  rw [graphMatrix, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro φ _
  by_cases h : Function.Injective φ ∧
      (∀ i, φ (left i) = row i) ∧ (∀ j, φ (right j) = col j)
  · simp only [if_pos h]
    calc
      _ = (∏ e ∈ G.edgeFinset, edgeWeight W hW φ e) *
          colorLaw.prob {χ : Fin n → α | RespectsColors φ χ} := by
        simp only [FiniteLaw.prob, FiniteLaw.expect, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro χ _
        ring
      _ = _ := by rw [probability_respectsColors φ h.1]; ring
  · simp [h]

/-- Report 96, identity (3.1), without any asymptotic or norm hypothesis. -/
theorem graphMatrix_eq_card_pow_expect_colored (G : SimpleGraph α)
    (left : Fin r ↪ α) (right : Fin s ↪ α)
    (W : Matrix (Fin n) (Fin n) ℝ) (hW : ∀ i j, W i j = W j i)
    (row : Fin r → Fin n) (col : Fin s → Fin n) :
    graphMatrix G left right W hW row col =
      (Fintype.card α : ℝ) ^ Fintype.card α *
        colorLaw.expect (fun χ => coloredGraphMatrix G left right W hW χ row col) := by
  rw [expect_coloredGraphMatrix, ← mul_assoc, ← mul_pow]
  simp [Nat.cast_ne_zero.mpr Fintype.card_ne_zero]

section NormAverages

variable {Ω ι κ : Type*} [Fintype Ω] [Fintype ι] [Fintype κ]
  [DecidableEq ι] [DecidableEq κ]

/-- Matrix expectation is a literal weighted finite sum. -/
def matrixExpect (μ : FiniteLaw Ω) (A : Ω → Matrix ι κ ℝ) : Matrix ι κ ℝ :=
  ∑ ω, μ.weight ω • A ω

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
@[simp] theorem matrixExpect_apply (μ : FiniteLaw Ω) (A : Ω → Matrix ι κ ℝ)
    (i : ι) (j : κ) : matrixExpect μ A i j = μ.expect (fun ω => A ω i j) := by
  simp [matrixExpect, FiniteLaw.expect, Matrix.sum_apply, Matrix.smul_apply]

omit [DecidableEq ι] in
open scoped Matrix.Norms.L2Operator in
/-- Genuine Euclidean operator-norm contraction of finite expectation. -/
theorem spectralNorm_matrixExpect_le (μ : FiniteLaw Ω) (A : Ω → Matrix ι κ ℝ) :
    spectralNorm (matrixExpect μ A) ≤ μ.expect (fun ω => spectralNorm (A ω)) := by
  simp only [spectralNorm_eq_l2Operator, matrixExpect, FiniteLaw.expect]
  calc
    ‖∑ ω, μ.weight ω • A ω‖ ≤ ∑ ω, ‖μ.weight ω • A ω‖ := norm_sum_le _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro ω _
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (μ.weight_nonneg ω)]

/-- Real-power Jensen under an explicit finite law, with all sign conditions stated. -/
theorem expect_rpow_le (μ : FiniteLaw Ω) (f : Ω → ℝ) (hf : ∀ ω, 0 ≤ f ω)
    (p : ℝ) (hp : 1 ≤ p) : (μ.expect f) ^ p ≤ μ.expect (fun ω => (f ω) ^ p) := by
  simpa only [FiniteLaw.expect, smul_eq_mul] using
    (convexOn_rpow hp).map_sum_le (t := Finset.univ) (w := μ.weight) (p := f)
      (fun ω _ => μ.weight_nonneg ω) μ.sum_weight (fun ω _ => hf ω)

end NormAverages

theorem graphMatrix_eq_card_pow_matrixExpect (G : SimpleGraph α)
    (left : Fin r ↪ α) (right : Fin s ↪ α)
    (W : Matrix (Fin n) (Fin n) ℝ) (hW : ∀ i j, W i j = W j i) :
    graphMatrix G left right W hW =
      (Fintype.card α : ℝ) ^ Fintype.card α •
        matrixExpect colorLaw (coloredGraphMatrix G left right W hW) := by
  ext row col
  simpa only [Matrix.smul_apply, smul_eq_mul, matrixExpect_apply] using
    graphMatrix_eq_card_pow_expect_colored G left right W hW row col

open scoped Matrix.Norms.L2Operator in
/-- The exact coloring identity implies the expected operator-norm upper comparison. -/
theorem spectralNorm_graphMatrix_le_expect_colored (G : SimpleGraph α)
    (left : Fin r ↪ α) (right : Fin s ↪ α)
    (W : Matrix (Fin n) (Fin n) ℝ) (hW : ∀ i j, W i j = W j i) :
    spectralNorm (graphMatrix G left right W hW) ≤
      (Fintype.card α : ℝ) ^ Fintype.card α *
        colorLaw.expect (fun χ => spectralNorm (coloredGraphMatrix G left right W hW χ)) := by
  rw [graphMatrix_eq_card_pow_matrixExpect]
  simp only [spectralNorm_eq_l2Operator, norm_smul, Real.norm_eq_abs]
  rw [abs_of_nonneg (pow_nonneg (Nat.cast_nonneg _) _)]
  exact mul_le_mul_of_nonneg_left
    (spectralNorm_matrixExpect_le colorLaw (coloredGraphMatrix G left right W hW))
    (pow_nonneg (Nat.cast_nonneg _) _)

/-- Real-power moment comparison for every `p ≥ 1`, before averaging the signs. -/
theorem spectralNorm_graphMatrix_rpow_le_expect_colored (G : SimpleGraph α)
    (left : Fin r ↪ α) (right : Fin s ↪ α)
    (W : Matrix (Fin n) (Fin n) ℝ) (hW : ∀ i j, W i j = W j i)
    (p : ℝ) (hp : 1 ≤ p) :
    spectralNorm (graphMatrix G left right W hW) ^ p ≤
      ((Fintype.card α : ℝ) ^ Fintype.card α) ^ p *
        colorLaw.expect (fun χ => spectralNorm (coloredGraphMatrix G left right W hW χ) ^ p) := by
  have hc : 0 ≤ (Fintype.card α : ℝ) ^ Fintype.card α :=
    pow_nonneg (Nat.cast_nonneg _) _
  have hf (χ : Fin n → α) :
      0 ≤ spectralNorm (coloredGraphMatrix G left right W hW χ) := spectralNorm_nonneg _
  calc
    _ ≤ ((Fintype.card α : ℝ) ^ Fintype.card α *
        colorLaw.expect (fun χ => spectralNorm (coloredGraphMatrix G left right W hW χ))) ^ p :=
      Real.rpow_le_rpow (spectralNorm_nonneg _)
        (spectralNorm_graphMatrix_le_expect_colored G left right W hW) (by linarith)
    _ = ((Fintype.card α : ℝ) ^ Fintype.card α) ^ p *
        (colorLaw.expect (fun χ => spectralNorm (coloredGraphMatrix G left right W hW χ))) ^ p :=
      Real.mul_rpow hc (colorLaw.expect_nonneg hf)
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (expect_rpow_le colorLaw _ hf p hp) (Real.rpow_nonneg hc p)

/-- The two finite expectations commute; no independence or integrability is implicit. -/
theorem expect_expect_comm {Ω Θ : Type*} [Fintype Ω] [Fintype Θ]
    (μ : FiniteLaw Ω) (ν : FiniteLaw Θ) (f : Ω → Θ → ℝ) :
    μ.expect (fun ω => ν.expect (f ω)) = ν.expect (fun θ => μ.expect (fun ω => f ω θ)) := by
  simp only [FiniteLaw.expect, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro θ _
  apply Finset.sum_congr rfl
  intro ω _
  ring

/-- Uniform colored `p`-moment upper bounds transfer to the actual uncolored model. -/
theorem expect_spectralNorm_graphMatrix_rpow_le_colored
    {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω) (G : SimpleGraph α)
    (left : Fin r ↪ α) (right : Fin s ↪ α)
    (W : Ω → Matrix (Fin n) (Fin n) ℝ) (hW : ∀ ω i j, W ω i j = W ω j i)
    (p : ℝ) (hp : 1 ≤ p) :
    μ.expect (fun ω => spectralNorm (graphMatrix G left right (W ω) (hW ω)) ^ p) ≤
      ((Fintype.card α : ℝ) ^ Fintype.card α) ^ p *
        colorLaw.expect (fun χ => μ.expect (fun ω =>
          spectralNorm (coloredGraphMatrix G left right (W ω) (hW ω) χ) ^ p)) := by
  calc
    _ ≤ μ.expect (fun ω => ((Fintype.card α : ℝ) ^ Fintype.card α) ^ p *
        colorLaw.expect (fun χ =>
          spectralNorm (coloredGraphMatrix G left right (W ω) (hW ω) χ) ^ p)) := by
      apply μ.expect_mono
      intro ω
      exact spectralNorm_graphMatrix_rpow_le_expect_colored G left right (W ω) (hW ω) p hp
    _ = _ := by rw [μ.expect_smul, expect_expect_comm]

end

end GraphMatrices.RoleColoring
