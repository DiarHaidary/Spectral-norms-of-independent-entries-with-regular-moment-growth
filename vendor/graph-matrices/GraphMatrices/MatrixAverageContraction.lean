import GraphMatrices.RoleColoring
import GraphMatrices.OffDiagonalModel

/-! Signed averages of explicitly measure-preserving sign flips contract mean norms. -/

namespace GraphMatrices.MatrixAverageContraction

noncomputable section
open scoped BigOperators

variable {Ω Θ ι κ : Type*} [Fintype Ω] [Fintype Θ]
  [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem expect_equiv (μ : FiniteLaw Ω) (e : Ω ≃ Ω)
    (hw : ∀ x, μ.weight (e x) = μ.weight x) (f : Ω → ℝ) :
    μ.expect (fun x => f (e x)) = μ.expect f := by
  unfold FiniteLaw.expect
  have heq : (∑ x, μ.weight (e x) * f (e x)) = ∑ x, μ.weight x * f x :=
    Equiv.sum_comp e (fun x => μ.weight x * f x)
  simpa only [hw] using heq

theorem signed_average_mean_norm_le
    (μ : FiniteLaw Ω) (ν : FiniteLaw Θ)
    (T : Θ → Ω ≃ Ω) (hw : ∀ θ x, μ.weight (T θ x) = μ.weight x)
    (c : Θ → ℝ) (hc : ∀ θ, |c θ| ≤ 1)
    (A : Ω → Matrix ι κ ℝ) :
    μ.expect (fun x => spectralNorm
      (RoleColoring.matrixExpect ν (fun θ => c θ • A (T θ x)))) ≤
        μ.expect (fun x => spectralNorm (A x)) := by
  have hpoint (x : Ω) :
      spectralNorm (RoleColoring.matrixExpect ν (fun θ => c θ • A (T θ x))) ≤
        ν.expect (fun θ => spectralNorm (A (T θ x))) := by
    calc
      _ ≤ ν.expect (fun θ => spectralNorm (c θ • A (T θ x))) :=
        RoleColoring.spectralNorm_matrixExpect_le _ _
      _ ≤ _ := by
        apply ν.expect_mono
        intro θ
        open scoped Matrix.Norms.L2Operator in
          simpa only [spectralNorm_eq_l2Operator, norm_smul, Real.norm_eq_abs, one_mul]
            using mul_le_mul_of_nonneg_right (hc θ) (spectralNorm_nonneg (A (T θ x)))
  calc
    _ ≤ μ.expect (fun x => ν.expect (fun θ => spectralNorm (A (T θ x)))) :=
      μ.expect_mono hpoint
    _ = ν.expect (fun θ => μ.expect (fun x => spectralNorm (A (T θ x)))) :=
      RoleColoring.expect_expect_comm μ ν _
    _ = ν.expect (fun _ => μ.expect (fun x => spectralNorm (A x))) := by
      apply ν.expect_congr
      intro θ
      exact expect_equiv μ (T θ) (hw θ) (fun x => spectralNorm (A x))
    _ = _ := ν.expect_const _

/-- Signed averages contract every real power moment of order at least one. -/
theorem signed_average_mean_norm_rpow_le
    (μ : FiniteLaw Ω) (ν : FiniteLaw Θ)
    (T : Θ → Ω ≃ Ω) (hw : ∀ θ x, μ.weight (T θ x) = μ.weight x)
    (c : Θ → ℝ) (hc : ∀ θ, |c θ| ≤ 1)
    (A : Ω → Matrix ι κ ℝ) (p : ℝ) (hp : 1 ≤ p) :
    μ.expect (fun x => spectralNorm
      (RoleColoring.matrixExpect ν (fun θ => c θ • A (T θ x))) ^ p) ≤
        μ.expect (fun x => spectralNorm (A x) ^ p) := by
  have hpoint (x : Ω) :
      spectralNorm (RoleColoring.matrixExpect ν (fun θ => c θ • A (T θ x))) ≤
        ν.expect (fun θ => spectralNorm (A (T θ x))) := by
    calc
      _ ≤ ν.expect (fun θ => spectralNorm (c θ • A (T θ x))) :=
        RoleColoring.spectralNorm_matrixExpect_le _ _
      _ ≤ _ := by
        apply ν.expect_mono
        intro θ
        open scoped Matrix.Norms.L2Operator in
          simpa only [spectralNorm_eq_l2Operator, norm_smul, Real.norm_eq_abs, one_mul]
            using mul_le_mul_of_nonneg_right (hc θ) (spectralNorm_nonneg (A (T θ x)))
  have hpower (x : Ω) :
      spectralNorm (RoleColoring.matrixExpect ν (fun θ => c θ • A (T θ x))) ^ p ≤
        ν.expect (fun θ => spectralNorm (A (T θ x)) ^ p) :=
    (Real.rpow_le_rpow (spectralNorm_nonneg _) (hpoint x) (by linarith)).trans
      (RoleColoring.expect_rpow_le ν _ (fun θ => spectralNorm_nonneg _) p hp)
  calc
    _ ≤ μ.expect (fun x => ν.expect (fun θ => spectralNorm (A (T θ x)) ^ p)) :=
      μ.expect_mono hpower
    _ = ν.expect (fun θ => μ.expect (fun x => spectralNorm (A (T θ x)) ^ p)) :=
      RoleColoring.expect_expect_comm μ ν _
    _ = ν.expect (fun _ => μ.expect (fun x => spectralNorm (A x) ^ p)) := by
      apply ν.expect_congr
      intro θ
      exact expect_equiv μ (T θ) (hw θ) (fun x => spectralNorm (A x) ^ p)
    _ = _ := ν.expect_const _

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- Flip precisely the coordinates on which the Boolean mask is true. -/
def xorFlip (mask : E → Bool) : (E → Bool) ≃ (E → Bool) where
  toFun σ i := Bool.xor (mask i) (σ i)
  invFun σ i := Bool.xor (mask i) (σ i)
  left_inv σ := by
    funext i
    change Bool.xor (mask i) (Bool.xor (mask i) (σ i)) = σ i
    cases mask i <;> cases σ i <;> rfl
  right_inv σ := by
    funext i
    change Bool.xor (mask i) (Bool.xor (mask i) (σ i)) = σ i
    cases mask i <;> cases σ i <;> rfl

theorem independent_weight_xorFlip (mask σ : E → Bool) :
    (independentSignLaw (E := E)).weight (xorFlip mask σ) =
      (independentSignLaw (E := E)).weight σ := by
  simp [independentSignLaw, FiniteLaw.independentProduct, fairBitLaw]

theorem independent_expect_xorFlip (mask : E → Bool) (f : (E → Bool) → ℝ) :
    independentSignLaw.expect (fun σ => f (xorFlip mask σ)) =
      independentSignLaw.expect f :=
  expect_equiv independentSignLaw (xorFlip mask) (independent_weight_xorFlip mask) f

/-- Concrete contraction for arbitrary block/coordinate masks under the
actual independent sign law; no law-invariance assumption remains. -/
theorem signed_signFlip_average_mean_norm_le
    (ν : FiniteLaw Θ) (mask : Θ → E → Bool)
    (c : Θ → ℝ) (hc : ∀ θ, |c θ| ≤ 1)
    (A : (E → Bool) → Matrix ι κ ℝ) :
    independentSignLaw.expect (fun σ => spectralNorm
      (RoleColoring.matrixExpect ν (fun θ => c θ • A (xorFlip (mask θ) σ)))) ≤
        independentSignLaw.expect (fun σ => spectralNorm (A σ)) :=
  signed_average_mean_norm_le independentSignLaw ν (fun θ => xorFlip (mask θ))
    (fun θ => independent_weight_xorFlip (mask θ)) c hc A

theorem signed_signFlip_average_mean_norm_rpow_le
    (ν : FiniteLaw Θ) (mask : Θ → E → Bool)
    (c : Θ → ℝ) (hc : ∀ θ, |c θ| ≤ 1)
    (A : (E → Bool) → Matrix ι κ ℝ) (p : ℝ) (hp : 1 ≤ p) :
    independentSignLaw.expect (fun σ => spectralNorm
      (RoleColoring.matrixExpect ν (fun θ => c θ • A (xorFlip (mask θ) σ))) ^ p) ≤
        independentSignLaw.expect (fun σ => spectralNorm (A σ) ^ p) :=
  signed_average_mean_norm_rpow_le independentSignLaw ν (fun θ => xorFlip (mask θ))
    (fun θ => independent_weight_xorFlip (mask θ)) c hc A p hp

end
end GraphMatrices.MatrixAverageContraction
