import MI32.BipartiteNorm
import MI32.VacuumNormBound
import MI32.BipartiteVacuumIteration

/-!
# Original matrix moments from the actual symmetric bipartite lift

The lift uses the same original entry in both directions. Its Euclidean
operator norm bounds the original rectangular norm with constant one.
The full symmetric-law local moment theorem is assembled below from the
proved positive-cone vacuum iteration, without a vacuum-bound premise.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory

namespace MI32.LocalSymmetricMoment

variable {Ω R C : Type*} [MeasurableSpace Ω] [Fintype R] [Fintype C]
    [DecidableEq R] [DecidableEq C] {μ : Measure Ω}

/-- Constant-one transfer from the literal bipartite norm, including the
derived original operator power integrability. -/
theorem moment_rectangular_le_bipartite
    (X : R → C → Ω → ℝ) (hX : ∀ i j, Measurable (X i j))
    (q : ℕ) (hq : 1 ≤ q)
    (hInt : Integrable (fun ω =>
      ‖PositiveVacuumWords.matrix PositiveVacuumWords.bipartiteWeight
        (fun e : R × C => X e.1 e.2 ω)‖ ^ (2 * q)) μ) :
    Integrable (fun ω => ‖BipartiteNorm.rectangular (fun e : R × C => X e.1 e.2 ω)‖ ^ (2 * q)) μ ∧
      moment μ (2 * (q : ℝ)) (fun ω => ‖BipartiteNorm.rectangular
        (fun e : R × C => X e.1 e.2 ω)‖) ≤
      moment μ (2 * (q : ℝ)) (fun ω =>
        ‖PositiveVacuumWords.matrix PositiveVacuumWords.bipartiteWeight
          (fun e : R × C => X e.1 e.2 ω)‖) := by
  have hpoint (ω : Ω) := pow_le_pow_left₀
    (norm_nonneg (BipartiteNorm.rectangular (fun e : R × C => X e.1 e.2 ω)))
    (BipartiteNorm.rectangular_norm_le_bipartite (fun e : R × C => X e.1 e.2 ω)) (2 * q)
  have hOriginal : Integrable (fun ω =>
      ‖BipartiteNorm.rectangular (fun e : R × C => X e.1 e.2 ω)‖ ^ (2 * q)) μ :=
    hInt.mono' ((BipartiteNorm.measurable_rectangular_norm X hX).pow_const _).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg _) _)]
        exact hpoint ω)
  refine ⟨hOriginal, ?_⟩
  have hm := MomentTools.even_moment_mono_of_integral_le _ _ (2 * q) (by omega)
    (show Even (2 * q) from ⟨q, by omega⟩) (integral_mono hOriginal hInt hpoint)
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using hm

variable [IsProbabilityMeasure μ]

/-- The local norm moment theorem for original independent symmetric regular
entries. Every count-sector and actual vacuum estimate is discharged.
The displayed dimension loss counts both sides of the bipartite lift; it is
absolute at orders comparable to the logarithm of the total dimension. -/
theorem operator_moment_le
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
        moment μ (2 * (q : ℝ)) (ThinMatrix.bilinear X s t) ≤ W) :
    Integrable (fun ω => ‖BipartiteNorm.rectangular (fun e : R × C => X e.1 e.2 ω)‖ ^ (2 * q)) μ ∧
      moment μ (2 * (q : ℝ)) (fun ω => ‖BipartiteNorm.rectangular
        (fun e : R × C => X e.1 e.2 ω)‖) ≤
        ((Fintype.card R + Fintype.card C : ℕ) : ℝ) ^ (1 / (2 * (q : ℝ))) *
          RawMultiplicationContraction.contractionConstant α B W := by
  have hVac := BipartiteVacuumIteration.vacuum_energies
    X hX hind hsym hint α hα hregular q hq B hB hrow hcol W hW hweak
  have hConstant : 0 ≤ RawMultiplicationContraction.contractionConstant α B W := by
    unfold RawMultiplicationContraction.contractionConstant
    positivity
  obtain ⟨hLiftInt, hLiftBound⟩ := VacuumNormBound.norm_moment_le_of_vacuum_energies
    (BipartiteVacuumIteration.lift X) (BipartiteNorm.measurable_bipartite_norm X hX)
    (fun ω => BipartiteNorm.bipartite_isSelfAdjoint (fun e : R × C => X e.1 e.2 ω))
    q hq (fun v => (hVac v).1) (RawMultiplicationContraction.contractionConstant α B W)
    hConstant (fun v => (hVac v).2)
  obtain ⟨hInt, hCompare⟩ := moment_rectangular_le_bipartite X hX q hq hLiftInt
  refine ⟨hInt, hCompare.trans ?_⟩
  simpa only [Fintype.card_sum, BipartiteVacuumIteration.lift] using hLiftBound

end MI32.LocalSymmetricMoment
