import MI32.MomentTools
import MI32.StatementChecks
import Mathlib.Order.ConditionallyCompleteLattice.Finset

/-!
# Finiteness and deterministic minimizers of the literal deletion quantities

The weak tests, supremum, budget infimum and deletion supremum are exactly
those in `Statement.lean`. Positive orders below one are included. Analytic
boundedness follows from an integrable sum of absolute original entries;
the budget minimizers are actual deterministic original index sets.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace MI32.WeakMomentBasics

variable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} {μ : Measure Ω}

/-- A finite integrable envelope for every original deterministic unit test. -/
def entryAbsSum (X : Ω → Matrix (Fin n) (Fin n) ℝ) (ω : Ω) : ℝ :=
  ∑ i, ∑ j, |X ω i j|

omit [MeasurableSpace Ω] in
theorem entryAbsSum_nonneg (X : Ω → Matrix (Fin n) (Fin n) ℝ) (ω : Ω) :
    0 ≤ entryAbsSum X ω := by
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _

@[fun_prop] theorem measurable_entryAbsSum (X : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hX : ∀ i j, Measurable (fun ω => X ω i j)) : Measurable (entryAbsSum X) := by
  unfold entryAbsSum
  fun_prop

@[fun_prop] theorem measurable_deletedBilinear (X : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hX : ∀ i j, Measurable (fun ω => X ω i j)) (I : Finset (Fin n))
    (s t : EuclideanSpace ℝ (Fin n)) : Measurable (deletedBilinear X I s t) := by
  unfold deletedBilinear
  fun_prop

/-- The envelope has every stipulated positive moment, also below one. -/
theorem memLp_entryAbsSum (X : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hX : ∀ i j, Measurable (fun ω => X ω i j))
    (hint : ∀ i j (p : ℝ), 0 < p → Integrable (fun ω => |X ω i j| ^ p) μ)
    (p : ℝ) (hp : 0 < p) : MemLp (entryAbsSum X) (ENNReal.ofReal p) μ := by
  unfold entryAbsSum
  apply memLp_finsetSum
  intro i _
  apply memLp_finsetSum
  intro j _
  simpa only [Real.norm_eq_abs] using
    (MomentTools.memLp_of_integrable_abs_rpow p hp (fun ω => X ω i j)
      (hX i j).aestronglyMeasurable (hint i j p hp)).norm

omit [MeasurableSpace Ω] in
theorem abs_deletedBilinear_le_entryAbsSum (X : Ω → Matrix (Fin n) (Fin n) ℝ)
    (I : Finset (Fin n)) (s t : EuclideanSpace ℝ (Fin n))
    (hs : ‖s‖ ≤ 1) (ht : ‖t‖ ≤ 1) (ω : Ω) :
    |deletedBilinear X I s t ω| ≤ entryAbsSum X ω := by
  have hsi (i : Fin n) : |s i| ≤ 1 := by
    simpa only [Real.norm_eq_abs] using (PiLp.norm_apply_le s i).trans hs
  have htj (j : Fin n) : |t j| ≤ 1 := by
    simpa only [Real.norm_eq_abs] using (PiLp.norm_apply_le t j).trans ht
  have hentry (i j : Fin n) : |X ω i j * s i * t j| ≤ |X ω i j| := by
    rw [abs_mul, abs_mul]
    exact (mul_le_of_le_one_right (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (htj j)).trans
      (mul_le_of_le_one_right (abs_nonneg _) (hsi i))
  unfold deletedBilinear entryAbsSum
  calc
    _ ≤ ∑ i ∈ Finset.univ \ I, |∑ j ∈ Finset.univ \ I, X ω i j * s i * t j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.univ \ I, ∑ j ∈ Finset.univ \ I, |X ω i j| := by
      apply Finset.sum_le_sum
      intro i _
      exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => hentry i j)
    _ ≤ ∑ i ∈ Finset.univ \ I, ∑ j, |X ω i j| :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_univ_sum_of_nonneg (fun j => abs_nonneg _)
    _ ≤ _ := Finset.sum_le_univ_sum_of_nonneg
      (fun i => Finset.sum_nonneg fun j _ => abs_nonneg _)

/-- Every unit test has an actual finite positive-order absolute moment. -/
theorem integrable_deletedBilinear_abs_rpow (X : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hX : ∀ i j, Measurable (fun ω => X ω i j))
    (hint : ∀ i j (p : ℝ), 0 < p → Integrable (fun ω => |X ω i j| ^ p) μ)
    (I : Finset (Fin n)) (p : ℝ) (hp : 0 < p)
    (s t : EuclideanSpace ℝ (Fin n)) (hs : ‖s‖ ≤ 1) (ht : ‖t‖ ≤ 1) :
    Integrable (fun ω => |deletedBilinear X I s t ω| ^ p) μ := by
  apply MomentTools.integrable_abs_rpow_of_memLp p hp
  exact (memLp_entryAbsSum X hX hint p hp).of_le_mul (c := 1)
    (measurable_deletedBilinear X hX I s t).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => by
      simpa only [one_mul, Real.norm_eq_abs, abs_of_nonneg (entryAbsSum_nonneg X ω)] using
        abs_deletedBilinear_le_entryAbsSum X I s t hs ht ω)

theorem moment_deletedBilinear_le_entryAbsSum (X : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hX : ∀ i j, Measurable (fun ω => X ω i j))
    (hint : ∀ i j (p : ℝ), 0 < p → Integrable (fun ω => |X ω i j| ^ p) μ)
    (I : Finset (Fin n)) (p : ℝ) (hp : 0 < p)
    (s t : EuclideanSpace ℝ (Fin n)) (hs : ‖s‖ ≤ 1) (ht : ‖t‖ ≤ 1) :
    moment μ p (deletedBilinear X I s t) ≤ moment μ p (entryAbsSum X) := by
  rw [MomentTools.eq_lpNorm p hp _ (measurable_deletedBilinear X hX I s t).aestronglyMeasurable,
    MomentTools.eq_lpNorm p hp _ (measurable_entryAbsSum X hX).aestronglyMeasurable]
  exact lpNorm_mono_real (memLp_entryAbsSum X hX hint p hp) (fun ω => by
    simpa only [Real.norm_eq_abs] using abs_deletedBilinear_le_entryAbsSum X I s t hs ht ω)

theorem weak_test_set_nonempty (μ : Measure Ω) (X : Ω → Matrix (Fin n) (Fin n) ℝ)
    (I : Finset (Fin n)) (p : ℝ) :
    {v : ℝ | ∃ s t : EuclideanSpace ℝ (Fin n),
      ‖s‖ ≤ 1 ∧ ‖t‖ ≤ 1 ∧ v = moment μ p (deletedBilinear X I s t)}.Nonempty := by
  exact ⟨_, 0, 0, by simp, by simp, rfl⟩

/-- Boundedness of the literal unit-test set, without replacing its supremum. -/
theorem weak_test_set_bddAbove (X : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hX : ∀ i j, Measurable (fun ω => X ω i j))
    (hint : ∀ i j (p : ℝ), 0 < p → Integrable (fun ω => |X ω i j| ^ p) μ)
    (I : Finset (Fin n)) (p : ℝ) (hp : 0 < p) :
    BddAbove {v : ℝ | ∃ s t : EuclideanSpace ℝ (Fin n),
      ‖s‖ ≤ 1 ∧ ‖t‖ ≤ 1 ∧ v = moment μ p (deletedBilinear X I s t)} := by
  refine ⟨moment μ p (entryAbsSum X), ?_⟩
  rintro v ⟨s, t, hs, ht, rfl⟩
  exact moment_deletedBilinear_le_entryAbsSum X hX hint I p hp s t hs ht

theorem moment_le_weakMoment (X : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hX : ∀ i j, Measurable (fun ω => X ω i j))
    (hint : ∀ i j (p : ℝ), 0 < p → Integrable (fun ω => |X ω i j| ^ p) μ)
    (I : Finset (Fin n)) (p : ℝ) (hp : 0 < p)
    (s t : EuclideanSpace ℝ (Fin n)) (hs : ‖s‖ ≤ 1) (ht : ‖t‖ ≤ 1) :
    moment μ p (deletedBilinear X I s t) ≤ weakMoment μ X I p :=
  le_csSup (weak_test_set_bddAbove X hX hint I p hp) ⟨s, t, hs, ht, rfl⟩

theorem weakMoment_le_entryAbsSum (X : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hX : ∀ i j, Measurable (fun ω => X ω i j))
    (hint : ∀ i j (p : ℝ), 0 < p → Integrable (fun ω => |X ω i j| ^ p) μ)
    (I : Finset (Fin n)) (p : ℝ) (hp : 0 < p) :
    weakMoment μ X I p ≤ moment μ p (entryAbsSum X) := by
  apply csSup_le (weak_test_set_nonempty μ X I p)
  rintro v ⟨s, t, hs, ht, rfl⟩
  exact moment_deletedBilinear_le_entryAbsSum X hX hint I p hp s t hs ht

/-- Nonnegativity is a property of the literal supremum of absolute moments. -/
theorem weakMoment_nonneg (μ : Measure Ω) (X : Ω → Matrix (Fin n) (Fin n) ℝ)
    (I : Finset (Fin n)) (p : ℝ) : 0 ≤ weakMoment μ X I p := by
  apply Real.sSup_nonneg
  rintro v ⟨s, t, _, _, rfl⟩
  exact MomentTools.nonneg p _

/-- The literal feasible-value set is finite because the original index set is finite. -/
theorem budget_value_set_finite (μ : Measure Ω) (X : Ω → Matrix (Fin n) (Fin n) ℝ)
    (k : ℕ) (p : ℝ) :
    {w : ℝ | ∃ I : Finset (Fin n), I.card ≤ k ∧ w = weakMoment μ X I p}.Finite := by
  apply (Set.finite_range (fun I : Finset (Fin n) => weakMoment μ X I p)).subset
  rintro w ⟨I, _, hw⟩
  exact ⟨I, hw.symm⟩

theorem budget_value_set_nonempty (μ : Measure Ω) (X : Ω → Matrix (Fin n) (Fin n) ℝ)
    (k : ℕ) (p : ℝ) :
    {w : ℝ | ∃ I : Finset (Fin n), I.card ≤ k ∧ w = weakMoment μ X I p}.Nonempty := by
  exact ⟨_, ∅, by simp, rfl⟩

/-- The budget infimum is attained by an actual deterministic original set,
and that set minimizes every other feasible value at the same literal order. -/
theorem exists_minimizing_set (μ : Measure Ω) (X : Ω → Matrix (Fin n) (Fin n) ℝ)
    (k : ℕ) (p : ℝ) :
    ∃ I : Finset (Fin n), I.card ≤ k ∧
      weakMoment μ X I p = sInf {w : ℝ | ∃ J : Finset (Fin n),
        J.card ≤ k ∧ w = weakMoment μ X J p} ∧
      ∀ J : Finset (Fin n), J.card ≤ k → weakMoment μ X I p ≤ weakMoment μ X J p := by
  have hf := budget_value_set_finite μ X k p
  obtain ⟨I, hI, hvalue⟩ := (budget_value_set_nonempty μ X k p).csInf_mem hf
  refine ⟨I, hI, hvalue.symm, ?_⟩
  intro J hJ
  rw [← hvalue]
  exact csInf_le hf.bddBelow ⟨J, hJ, rfl⟩

/-- This nonnegativity does not need a probabilistic normalization assumption. -/
theorem budget_minimum_nonneg (μ : Measure Ω) (X : Ω → Matrix (Fin n) (Fin n) ℝ)
    (k : ℕ) (p : ℝ) :
    0 ≤ sInf {w : ℝ | ∃ I : Finset (Fin n), I.card ≤ k ∧ w = weakMoment μ X I p} := by
  apply Real.sInf_nonneg
  rintro w ⟨I, _, rfl⟩
  exact weakMoment_nonneg μ X I p

/-- The literal deletion supremum ranges over finitely many integer budgets. -/
theorem deletion_value_set_finite (μ : Measure Ω) (X : Ω → Matrix (Fin n) (Fin n) ℝ) :
    {v : ℝ | ∃ k : ℕ, 1 ≤ k ∧ k ≤ n ∧
      v = sInf {w : ℝ | ∃ I : Finset (Fin n), I.card ≤ k ∧
        w = weakMoment μ X I (Real.log (k + 1 : ℕ))}}.Finite := by
  let f (k : ℕ) : ℝ := sInf {w : ℝ | ∃ I : Finset (Fin n), I.card ≤ k ∧
    w = weakMoment μ X I (Real.log (k + 1 : ℕ))}
  apply ((Set.finite_Icc (1 : ℕ) n).image f).subset
  rintro v ⟨k, hk, hkn, rfl⟩
  exact ⟨k, ⟨hk, hkn⟩, rfl⟩

theorem deletion_value_set_bddAbove (μ : Measure Ω) (X : Ω → Matrix (Fin n) (Fin n) ℝ) :
    BddAbove {v : ℝ | ∃ k : ℕ, 1 ≤ k ∧ k ≤ n ∧
      v = sInf {w : ℝ | ∃ I : Finset (Fin n), I.card ≤ k ∧
        w = weakMoment μ X I (Real.log (k + 1 : ℕ))}} :=
  (deletion_value_set_finite μ X).bddAbove

/-- Every admissible deterministic budget minimum is bounded by the
unchanged deletion supremum appearing in the original problem statement. -/
theorem minimum_le_deletionScale (μ : Measure Ω) (X : Ω → Matrix (Fin n) (Fin n) ℝ)
    (k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    sInf {w : ℝ | ∃ I : Finset (Fin n), I.card ≤ k ∧
      w = weakMoment μ X I (Real.log (k + 1 : ℕ))} ≤ deletionScale μ X :=
  le_csSup (deletion_value_set_bddAbove μ X) ⟨k, hk, hkn, rfl⟩

/-- A minimizing original deletion set at the exact logarithmic order.
The minimizer is deterministic and achieves a value at most `deletionScale`. -/
theorem exists_deletion_minimizer_le_scale
    (μ : Measure Ω) (X : Ω → Matrix (Fin n) (Fin n) ℝ)
    (k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    ∃ I : Finset (Fin n), I.card ≤ k ∧
      weakMoment μ X I (Real.log (k + 1 : ℕ)) ≤ deletionScale μ X ∧
      ∀ J : Finset (Fin n), J.card ≤ k →
        weakMoment μ X I (Real.log (k + 1 : ℕ)) ≤
          weakMoment μ X J (Real.log (k + 1 : ℕ)) := by
  obtain ⟨I, hI, hmin, hopt⟩ := exists_minimizing_set μ X k (Real.log (k + 1 : ℕ))
  exact ⟨I, hI, hmin.trans_le (minimum_le_deletionScale μ X k hk hkn), hopt⟩

/-- The literal deletion scale is nonnegative, also in the degenerate empty dimension. -/
theorem deletionScale_nonneg (μ : Measure Ω) (X : Ω → Matrix (Fin n) (Fin n) ℝ) :
    0 ≤ deletionScale μ X := by
  apply Real.sSup_nonneg
  rintro v ⟨k, _, _, rfl⟩
  exact budget_minimum_nonneg μ X k _

theorem log_budget_pos (k : ℕ) (hk : 1 ≤ k) : 0 < Real.log (k + 1 : ℕ) := by
  apply Real.log_pos
  exact_mod_cast (show 1 < k + 1 by omega)

/-- Full deletion gives zero at every actual positive order. -/
theorem weakMoment_full_deletion_eq_zero (μ : Measure Ω)
    (X : Ω → Matrix (Fin n) (Fin n) ℝ) (p : ℝ) (hp : 0 < p) :
    weakMoment μ X Finset.univ p = 0 := MI32.weakMoment_univ μ X hp

end MI32.WeakMomentBasics
