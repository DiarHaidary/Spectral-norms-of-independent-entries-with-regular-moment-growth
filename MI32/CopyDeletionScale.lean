import MI32.WeakMomentBasics
import MI32.DeletionMomentEndpoints

/-!
# Independent-copy deletion comparison with the same original set

For each original deterministic set, its deleted bilinear form commutes
exactly with the actual copy difference. Scalar positive-order copy bounds
then compare the literal weak suprema. Choosing an original minimizing set
at each budget controls the copied infimum with that same set, and hence
the literal deletion supremum. No entry independence or centering is needed.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace MI32.CopyDeletionScale

open WeakMomentBasics

variable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} {μ : Measure Ω}

omit [MeasurableSpace Ω] in
/-- Both copies use precisely the same original deletion set and test vectors. -/
theorem deletedBilinear_copy_eq (X : Ω → Matrix (Fin n) (Fin n) ℝ)
    (I : Finset (Fin n)) (s t : EuclideanSpace ℝ (Fin n)) (z : Ω × Ω) :
    deletedBilinear (fun z : Ω × Ω => X z.1 - X z.2) I s t z =
      deletedBilinear X I s t z.1 - deletedBilinear X I s t z.2 := by
  simp only [deletedBilinear, Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib]

variable [IsProbabilityMeasure μ]

/-- Actual copied tests have finite p-th absolute moments and obey the scalar
copy comparison, at every original order p at least log(2). -/
theorem test_moment_copy_le_exp (X : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hX : ∀ i j, Measurable (fun ω => X ω i j))
    (hint : ∀ i j (p : ℝ), 0 < p → Integrable (fun ω => |X ω i j| ^ p) μ)
    (I : Finset (Fin n)) (p : ℝ) (hp : Real.log 2 ≤ p)
    (s t : EuclideanSpace ℝ (Fin n)) (hs : ‖s‖ ≤ 1) (ht : ‖t‖ ≤ 1) :
    Integrable (fun z : Ω × Ω =>
      |deletedBilinear (fun z : Ω × Ω => X z.1 - X z.2) I s t z| ^ p) (μ.prod μ) ∧
      moment (μ.prod μ) p (deletedBilinear (fun z : Ω × Ω => X z.1 - X z.2) I s t) ≤
        Real.exp 1 * moment μ p (deletedBilinear X I s t) := by
  have hp0 : 0 < p := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans_le hp
  have heq : deletedBilinear (fun z : Ω × Ω => X z.1 - X z.2) I s t =
      fun z : Ω × Ω => deletedBilinear X I s t z.1 - deletedBilinear X I s t z.2 :=
    funext (deletedBilinear_copy_eq X I s t)
  rw [heq]
  exact DeletionMomentEndpoints.copy_moment_le_exp (deletedBilinear X I s t)
    (measurable_deletedBilinear X hX I s t) p hp
    (integrable_deletedBilinear_abs_rpow X hX hint I p hp0 s t hs ht)

/-- The literal copied weak moment is bounded by the original weak moment
for exactly the same deterministic set, also at subunit logarithmic orders. -/
theorem weakMoment_copy_le (X : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hX : ∀ i j, Measurable (fun ω => X ω i j))
    (hint : ∀ i j (p : ℝ), 0 < p → Integrable (fun ω => |X ω i j| ^ p) μ)
    (I : Finset (Fin n)) (p : ℝ) (hp : Real.log 2 ≤ p) :
    weakMoment (μ.prod μ) (fun z : Ω × Ω => X z.1 - X z.2) I p ≤
      Real.exp 1 * weakMoment μ X I p := by
  apply csSup_le (weak_test_set_nonempty (μ.prod μ)
    (fun z : Ω × Ω => X z.1 - X z.2) I p)
  rintro v ⟨s, t, hs, ht, rfl⟩
  have hp0 : 0 < p := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans_le hp
  exact (test_moment_copy_le_exp X hX hint I p hp s t hs ht).2.trans
    (mul_le_mul_of_nonneg_left (moment_le_weakMoment X hX hint I p hp0 s t hs ht)
      (Real.exp_pos 1).le)

/-- An actual original minimizer remains a feasible copied set, and its
copied value is bounded using that same original minimizing value. -/
theorem exists_same_set_budget_comparison (X : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hX : ∀ i j, Measurable (fun ω => X ω i j))
    (hint : ∀ i j (p : ℝ), 0 < p → Integrable (fun ω => |X ω i j| ^ p) μ)
    (k : ℕ) (p : ℝ) (hp : Real.log 2 ≤ p) :
    ∃ I : Finset (Fin n), I.card ≤ k ∧
      weakMoment μ X I p = sInf {w : ℝ | ∃ J : Finset (Fin n),
        J.card ≤ k ∧ w = weakMoment μ X J p} ∧
      weakMoment (μ.prod μ) (fun z : Ω × Ω => X z.1 - X z.2) I p ≤
        Real.exp 1 * sInf {w : ℝ | ∃ J : Finset (Fin n),
          J.card ≤ k ∧ w = weakMoment μ X J p} := by
  obtain ⟨I, hI, hmin, _⟩ := exists_minimizing_set μ X k p
  refine ⟨I, hI, hmin, ?_⟩
  rw [← hmin]
  exact weakMoment_copy_le X hX hint I p hp

/-- Comparison of literal budget infima, witnessed by an original minimizer. -/
theorem budget_minimum_copy_le (X : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hX : ∀ i j, Measurable (fun ω => X ω i j))
    (hint : ∀ i j (p : ℝ), 0 < p → Integrable (fun ω => |X ω i j| ^ p) μ)
    (k : ℕ) (p : ℝ) (hp : Real.log 2 ≤ p) :
    sInf {w : ℝ | ∃ I : Finset (Fin n), I.card ≤ k ∧
      w = weakMoment (μ.prod μ) (fun z : Ω × Ω => X z.1 - X z.2) I p} ≤
      Real.exp 1 * sInf {w : ℝ | ∃ I : Finset (Fin n), I.card ≤ k ∧
        w = weakMoment μ X I p} := by
  obtain ⟨I, hI, _, hcopy⟩ := exists_same_set_budget_comparison X hX hint k p hp
  exact (csInf_le (budget_value_set_finite (μ.prod μ)
    (fun z : Ω × Ω => X z.1 - X z.2) k p).bddBelow ⟨I, hI, rfl⟩).trans hcopy

/-- The literal copied deletion scale is at most exp(1) times the original
scale. Every budget keeps its exact order log(k+1) and its original minimizer. -/
theorem deletionScale_copy_le (X : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hX : ∀ i j, Measurable (fun ω => X ω i j))
    (hint : ∀ i j (p : ℝ), 0 < p → Integrable (fun ω => |X ω i j| ^ p) μ)
    (hn : 1 ≤ n) :
    deletionScale (μ.prod μ) (fun z : Ω × Ω => X z.1 - X z.2) ≤
      Real.exp 1 * deletionScale μ X := by
  apply csSup_le
  · exact ⟨_, 1, le_rfl, hn, rfl⟩
  · rintro v ⟨k, hk, hkn, rfl⟩
    have hp : Real.log 2 ≤ Real.log (k + 1 : ℕ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast (show 2 ≤ k + 1 by omega))
    exact (budget_minimum_copy_le X hX hint k (Real.log (k + 1 : ℕ)) hp).trans
      (mul_le_mul_of_nonneg_left (minimum_le_deletionScale μ X k hk hkn) (Real.exp_pos 1).le)

end MI32.CopyDeletionScale
