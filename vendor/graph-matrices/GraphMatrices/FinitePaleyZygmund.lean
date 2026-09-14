import GraphMatrices.FiniteProbability
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Finite probability inequalities used in the lower-bound argument. -/

namespace GraphMatrices.FiniteLaw

noncomputable section

open scoped BigOperators

variable {α : Type*} [Fintype α]

theorem expect_mul_sq_le (μ : FiniteLaw α) (f g : α → ℝ) :
    (μ.expect (fun x => f x * g x)) ^ 2 ≤
      μ.expect (fun x => f x ^ 2) * μ.expect (fun x => g x ^ 2) := by
  have hs (x : α) : Real.sqrt (μ.weight x) ^ 2 = μ.weight x :=
    Real.sq_sqrt (μ.weight_nonneg x)
  have h := Finset.sum_mul_sq_le_sq_mul_sq (s := Finset.univ)
    (f := fun x => Real.sqrt (μ.weight x) * f x)
    (g := fun x => Real.sqrt (μ.weight x) * g x)
  have heq (x : α) :
      (Real.sqrt (μ.weight x) * f x) * (Real.sqrt (μ.weight x) * g x) =
        μ.weight x * (f x * g x) := by
    calc
      _ = Real.sqrt (μ.weight x) ^ 2 * (f x * g x) := by ring
      _ = _ := by rw [hs x]
  have hf (x : α) :
      (Real.sqrt (μ.weight x) * f x) ^ 2 = μ.weight x * f x ^ 2 := by
    rw [mul_pow, hs x]
  have hg (x : α) :
      (Real.sqrt (μ.weight x) * g x) ^ 2 = μ.weight x * g x ^ 2 := by
    rw [mul_pow, hs x]
  simpa only [heq, hf, hg, expect] using h

theorem expect_restrict_sq_le (μ : FiniteLaw α) (f : α → ℝ) (s : Set α) :
    (μ.expect (fun x => f x * indicator s x)) ^ 2 ≤
      μ.expect (fun x => f x ^ 2) * μ.prob s := by
  classical
  have hi (x : α) : indicator s x ^ 2 = indicator s x := by
    by_cases hx : x ∈ s <;> simp [indicator, hx]
  simpa only [hi, prob] using μ.expect_mul_sq_le f (indicator s)

theorem paley_zygmund_mul (μ : FiniteLaw α) (f : α → ℝ)
    (hf : ∀ x, 0 ≤ f x) {a : ℝ} (ha : 0 ≤ a) (ham : a ≤ μ.expect f) :
    (μ.expect f - a) ^ 2 ≤
      μ.expect (fun x => f x ^ 2) * μ.prob {x | a ≤ f x} := by
  classical
  let s : Set α := {x | a ≤ f x}
  have hsplit : μ.expect f ≤ a + μ.expect (fun x => f x * indicator s x) := by
    calc
      μ.expect f ≤ μ.expect (fun x => a + f x * indicator s x) := by
        apply μ.expect_mono
        intro x
        by_cases hx : a ≤ f x
        · simpa [indicator, s, hx] using (show f x ≤ a + f x by linarith)
        · simp [indicator, s, hx, le_of_lt (lt_of_not_ge hx)]
      _ = _ := by rw [μ.expect_add, μ.expect_const]
  have hnonneg : 0 ≤ μ.expect (fun x => f x * indicator s x) := by
    apply μ.expect_nonneg
    intro x
    by_cases hx : x ∈ s <;> simp [indicator, hx, hf x]
  calc
    (μ.expect f - a) ^ 2 ≤
        (μ.expect (fun x => f x * indicator s x)) ^ 2 := by
      nlinarith
    _ ≤ _ := μ.expect_restrict_sq_le f s

theorem probability_large_of_moments (μ : FiniteLaw α) (f : α → ℝ)
    (hf : ∀ x, 0 ≤ f x) {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hfirst : A ≤ μ.expect f) (hsecond : μ.expect (fun x => f x ^ 2) ≤ B) :
    A ^ 2 / (4 * B) ≤ μ.prob {x | A / 2 ≤ f x} := by
  have h := μ.paley_zygmund_mul f hf (a := A / 2) (by positivity) (by linarith)
  have hp := μ.prob_nonneg {x | A / 2 ≤ f x}
  have hprod := mul_le_mul_of_nonneg_right hsecond hp
  apply (div_le_iff₀ (by positivity : 0 < 4 * B)).2
  nlinarith [sq_nonneg (μ.expect f - A)]

theorem rpow_moment_lower_of_event (μ : FiniteLaw α) (f : α → ℝ)
    (hf : ∀ x, 0 ≤ f x) {a p : ℝ} (ha : 0 ≤ a) (hp : 0 < p) :
    a ^ p * μ.prob {x | a ≤ f x} ≤ μ.expect (fun x => (f x) ^ p) := by
  classical
  rw [prob, ← μ.expect_smul]
  apply μ.expect_mono
  intro x
  by_cases hx : a ≤ f x
  · simpa [indicator, hx] using Real.rpow_le_rpow ha hx hp.le
  · simpa [indicator, hx] using Real.rpow_nonneg (hf x) p

theorem rpow_moment_lower_of_first_second (μ : FiniteLaw α) (f : α → ℝ)
    (hf : ∀ x, 0 ≤ f x) {A B p : ℝ} (hA : 0 < A) (hB : 0 < B) (hp : 0 < p)
    (hfirst : A ≤ μ.expect f) (hsecond : μ.expect (fun x => f x ^ 2) ≤ B) :
    (A / 2) ^ p * (A ^ 2 / (4 * B)) ≤ μ.expect (fun x => (f x) ^ p) := by
  calc
    _ ≤ (A / 2) ^ p * μ.prob {x | A / 2 ≤ f x} :=
      mul_le_mul_of_nonneg_left
        (μ.probability_large_of_moments f hf hA hB hfirst hsecond)
        (Real.rpow_nonneg (by positivity) p)
    _ ≤ _ := μ.rpow_moment_lower_of_event f hf (by positivity) hp

end
end GraphMatrices.FiniteLaw
