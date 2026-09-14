import GraphMatrices.WalshFourthMoment

/-!
# Hilbert-valued Boolean fourth moments

The squared Euclidean norm is written as the sum of coordinate squares.
The theorem follows from scalar Boolean hypercontractivity and an actual
Cauchy--Schwarz argument for each pair of coordinates. No positivity assumption
is imposed on the Walsh coefficients. This is the conditional-sign part of
the positive-cone argument; it is not the regular-magnitude estimate.
-/

noncomputable section
open scoped BigOperators

namespace MI32

open GraphMatrices
open GraphMatrices.MatrixAverageContraction

theorem finite_expect_sum {Ω A : Type*} [Fintype Ω] [Fintype A]
    (μ : FiniteLaw Ω) (f : A → Ω → ℝ) :
    μ.expect (fun ω => ∑ a, f a ω) = ∑ a, μ.expect (f a) := by
  simp only [FiniteLaw.expect, Finset.mul_sum]
  exact Finset.sum_comm

/-- Scalar fourth-moment estimates combine without a loss in the number of
coordinates. This is the finite-dimensional real Hilbert extension. -/
theorem fourth_sum_squares_le {Ω A : Type*} [Fintype Ω] [Fintype A]
    (μ : FiniteLaw Ω) (f : A → Ω → ℝ) (b : A → ℝ)
    (hb : ∀ a, 0 ≤ b a)
    (hfourth : ∀ a, μ.expect (fun ω => f a ω ^ 4) ≤ b a ^ 2) :
    μ.expect (fun ω => (∑ a, f a ω ^ 2) ^ 2) ≤ (∑ a, b a) ^ 2 := by
  have hcross (a a' : A) :
      μ.expect (fun ω => f a ω ^ 2 * f a' ω ^ 2) ≤ b a * b a' := by
    have hcs := μ.expect_mul_sq_le (fun ω => f a ω ^ 2) (fun ω => f a' ω ^ 2)
    have hp4 (z : ℝ) : (z ^ 2) ^ 2 = z ^ 4 := by ring
    simp only [hp4] at hcs
    have hn : 0 ≤ μ.expect (fun ω => f a' ω ^ 4) :=
      μ.expect_nonneg (fun _ => by positivity)
    have hprod := mul_le_mul (hfourth a) (hfourth a') hn (sq_nonneg (b a))
    have hbb := mul_nonneg (hb a) (hb a')
    nlinarith [sq_nonneg (μ.expect (fun ω => f a ω ^ 2 * f a' ω ^ 2) - b a * b a')]
  have hexpand (ω : Ω) : (∑ a, f a ω ^ 2) ^ 2 =
      ∑ a, ∑ a', f a ω ^ 2 * f a' ω ^ 2 := by
    simp only [pow_two, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_comm
  rw [μ.expect_congr hexpand, finite_expect_sum]
  simp_rw [finite_expect_sum]
  calc
    _ ≤ ∑ a, ∑ a', b a * b a' :=
      Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun a' _ => hcross a a'))
    _ = (∑ a, b a) ^ 2 := by
      simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_comm

/-- Dimension-free Hilbert Boolean 2-to-4 hypercontractivity, as a fourth-power
inequality. The coordinates can have arbitrary real Walsh coefficients. -/
theorem hilbert_walsh_fourth_le {E A : Type*}
    [Fintype E] [DecidableEq E] [Fintype A]
    (I : Finset (Finset E)) (c : A → Finset E → ℝ)
    (d : ℕ) (hdeg : ∀ S ∈ I, S.card ≤ d) :
    independentSignLaw.expect
      (fun σ => (∑ a, Walsh.polynomial I (c a) σ ^ 2) ^ 2) ≤
      (9 : ℝ) ^ d *
        (independentSignLaw.expect
          (fun σ => ∑ a, Walsh.polynomial I (c a) σ ^ 2)) ^ 2 := by
  let f : A → (E → Bool) → ℝ := fun a => Walsh.polynomial I (c a)
  let b : A → ℝ := fun a => (3 : ℝ) ^ d *
    independentSignLaw.expect (fun σ => f a σ ^ 2)
  have hb (a : A) : 0 ≤ b a :=
    mul_nonneg (by positivity) (FiniteLaw.expect_nonneg _ (fun _ => sq_nonneg _))
  have hfourth (a : A) :
      independentSignLaw.expect (fun σ => f a σ ^ 4) ≤ b a ^ 2 := by
    have h := Walsh.polynomial_fourth_le_nine_pow I (c a) d hdeg
    have hp : ((3 : ℝ) ^ d) ^ 2 = (9 : ℝ) ^ d := by
      rw [← pow_mul, Nat.mul_comm d 2, pow_mul]
      norm_num
    simpa only [b, f, mul_pow, hp] using h
  have h := fourth_sum_squares_le independentSignLaw f b hb hfourth
  have hbSum : (∑ a, b a) = (3 : ℝ) ^ d *
      independentSignLaw.expect (fun σ => ∑ a, f a σ ^ 2) := by
    rw [finite_expect_sum, Finset.mul_sum]
  have hp : ((3 : ℝ) ^ d) ^ 2 = (9 : ℝ) ^ d := by
    rw [← pow_mul, Nat.mul_comm d 2, pow_mul]
    norm_num
  rw [hbSum, mul_pow, hp] at h
  exact h

end MI32

