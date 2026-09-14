import MI32.FiberBlockNorm
import MI32.BlockMomentMaximum
import MI32.ThinMatrix
import MI32.MomentTools

/-!
# Fiber-supported means from growing block moments

A random matrix supported on the diagonal blocks of a colouring `c : V → Fin m`
is controlled by the maximum of its fiber block norms, with no factor in the
number of blocks. Combining the deterministic bound of
`MI32.FiberBlockNorm.norm_le_pi_blockSub` with the growing-order maximum
estimate of `MI32.BlockMomentMaximum.mean_max_le` turns per-block rooted moment
bounds of order at least `k + 2` into a mean bound for the whole matrix.

The common bound is only assumed nonnegative: the strict positivity needed by
`mean_max_le` is supplied by an arbitrarily small perturbation `L + ε`, which is
removed at the end. Measurability and integrability of the actual operator norm
are derived, not assumed. The degenerate case `m = 0` needs no special
treatment: the fiber support hypothesis then forces `V` to be empty.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open MeasureTheory

namespace MI32.BlockMaskMoment

variable {Ω V : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [Fintype V] [DecidableEq V] {m : ℕ}

/-- The fiber block norm is measurable in the original entries. -/
theorem measurable_blockSub_norm (A : Ω → Matrix V V ℝ)
    (hA : ∀ i j, Measurable (fun ω => A ω i j)) (c : V → Fin m) (k : Fin m) :
    Measurable (fun ω => ‖FiberBlockNorm.blockSub (A ω) c k‖) :=
  ThinMatrix.measurable_norm_transposeOperator
    (fun v u ω => FiberBlockNorm.blockSub (A ω) c k u v)
    (fun v u => hA u.val v.val)

/-- The operator norm of the original matrix is measurable in its entries. -/
theorem measurable_norm (A : Ω → Matrix V V ℝ)
    (hA : ∀ i j, Measurable (fun ω => A ω i j)) :
    Measurable (fun ω => ‖A ω‖) :=
  ThinMatrix.measurable_norm_transposeOperator (fun v u ω => A ω u v) (fun v u => hA u v)

/-- A nonnegative quantity with an integrable power of order at least one is
itself integrable, since it is dominated by `1` plus that power. -/
theorem integrable_of_integrable_pow (f : Ω → ℝ) (hf : Measurable f)
    (hnonneg : ∀ ω, 0 ≤ f ω) (q : ℕ) (hq : q ≠ 0)
    (hpow : Integrable (fun ω => f ω ^ q) μ) [IsProbabilityMeasure μ] :
    Integrable f μ := by
  refine ((integrable_const (1 : ℝ)).add hpow).mono' hf.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg ω)]
  rcases le_or_gt (f ω) 1 with h | h
  · exact h.trans (le_add_of_nonneg_right (pow_nonneg (hnonneg ω) _))
  · exact (le_self_pow₀ h.le hq).trans (le_add_of_nonneg_left zero_le_one)

/-- A nonnegative common rooted bound on growing block moments controls the
actual fiber-supported operator mean, with derived integrability and no
dependence on the number of blocks. -/
theorem mean_norm_le_of_block_moments [IsProbabilityMeasure μ] (A : Ω → Matrix V V ℝ)
    (hA : ∀ i j, Measurable (fun ω => A ω i j)) (c : V → Fin m)
    (hsupp : ∀ ω i j, c i ≠ c j → A ω i j = 0)
    (p : Fin m → ℕ) (hp : ∀ k, k.val + 2 ≤ p k)
    (hPow : ∀ k, Integrable (fun ω => ‖FiberBlockNorm.blockSub (A ω) c k‖ ^ p k) μ)
    (L : ℝ) (hL : 0 ≤ L)
    (hBound : ∀ k, (∫ ω, ‖FiberBlockNorm.blockSub (A ω) c k‖ ^ p k ∂μ) ≤ L ^ p k) :
    Integrable (fun ω => ‖A ω‖) μ ∧ (∫ ω, ‖A ω‖ ∂μ) ≤ 3 * L := by
  have hZint : ∀ k, Integrable (fun ω => ‖FiberBlockNorm.blockSub (A ω) c k‖) μ := fun k =>
    integrable_of_integrable_pow _ (measurable_blockSub_norm A hA c k)
      (fun _ => norm_nonneg _) (p k) (by have := hp k; omega) (hPow k)
  have hdom : ∀ ω, ‖A ω‖ ≤ ‖fun k => ‖FiberBlockNorm.blockSub (A ω) c k‖‖ := fun ω =>
    FiberBlockNorm.norm_le_pi_blockSub (A ω) c (hsupp ω)
  have hdomNorm : ∀ ω, ‖(‖A ω‖)‖ ≤ ‖fun k => ‖FiberBlockNorm.blockSub (A ω) c k‖‖ := by
    intro ω
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact hdom ω
  have hstep : ∀ ε : ℝ, 0 < ε →
      Integrable (fun ω => ‖fun k => ‖FiberBlockNorm.blockSub (A ω) c k‖‖) μ ∧
        (∫ ω, ‖fun k => ‖FiberBlockNorm.blockSub (A ω) c k‖‖ ∂μ) ≤ 3 * (L + ε) := by
    intro ε hε
    refine BlockMomentMaximum.mean_max_le
      (fun k ω => ‖FiberBlockNorm.blockSub (A ω) c k‖) hZint (fun _ _ => norm_nonneg _)
      p hp hPow (L + ε) (by linarith) fun k => ?_
    exact (hBound k).trans (pow_le_pow_left₀ hL (by linarith) _)
  have hAint : Integrable (fun ω => ‖A ω‖) μ :=
    (hstep 1 one_pos).1.mono' (measurable_norm A hA).aestronglyMeasurable
      (Filter.Eventually.of_forall hdomNorm)
  refine ⟨hAint, ?_⟩
  by_contra hcon
  have hlt : 3 * L < ∫ ω, ‖A ω‖ ∂μ := lt_of_not_ge hcon
  obtain ⟨hInt, hBnd⟩ := hstep (((∫ ω, ‖A ω‖ ∂μ) - 3 * L) / 6) (by linarith)
  have hmono := (integral_mono hAint hInt hdom).trans hBnd
  linarith

end MI32.BlockMaskMoment
