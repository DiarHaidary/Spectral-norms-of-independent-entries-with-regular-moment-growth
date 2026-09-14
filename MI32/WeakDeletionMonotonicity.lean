import MI32.WeakMomentBasics

/-!
# Exact monotonicity of the shared original deletion set

Both deterministic test vectors are masked on the same original indices.
The resulting scalar random variable is exactly the smaller undeleted
bilinear form. This proves deletion monotonicity at every positive order,
including orders below one, without independence or symmetry assumptions.
Order monotonicity separately uses the probability normalization.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace MI32.WeakDeletionMonotonicity

variable {Ω : Type*} {n : ℕ}

/-- Set the deleted original coordinates to zero without changing the ambient axes. -/
def mask (I : Finset (Fin n)) (s : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun i => if i ∈ I then 0 else s i)

@[simp] theorem mask_apply_mem (I : Finset (Fin n)) (s : EuclideanSpace ℝ (Fin n))
    (i : Fin n) (hi : i ∈ I) : mask I s i = 0 := by simp [mask, hi]

@[simp] theorem mask_apply_not_mem (I : Finset (Fin n)) (s : EuclideanSpace ℝ (Fin n))
    (i : Fin n) (hi : i ∉ I) : mask I s i = s i := by simp [mask, hi]

/-- The exact retained Euclidean energy on the original coordinate complement. -/
theorem norm_mask_sq (I : Finset (Fin n)) (s : EuclideanSpace ℝ (Fin n)) :
    ‖mask I s‖ ^ 2 = ∑ i ∈ Finset.univ \ I, (s i) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  have hfin : Finset.univ \ I = Finset.univ.filter (fun i : Fin n => i ∉ I) := by
    ext i
    simp
  rw [hfin, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i ∈ I <;> simp [mask, hi]

/-- Masking deterministic coordinates is a Euclidean contraction. -/
theorem norm_mask_le (I : Finset (Fin n)) (s : EuclideanSpace ℝ (Fin n)) :
    ‖mask I s‖ ≤ ‖s‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_mask_sq, EuclideanSpace.real_norm_sq_eq]
  exact Finset.sum_le_univ_sum_of_nonneg fun i => sq_nonneg (s i)

private theorem sum_compl_mask (I J : Finset (Fin n)) (hIJ : I ⊆ J)
    (f : Fin n → ℝ) :
    (∑ i ∈ Finset.univ \ I, if i ∈ J then 0 else f i) =
      ∑ i ∈ Finset.univ \ J, f i := by
  have hfin : Finset.univ \ J = (Finset.univ \ I).filter (fun i => i ∉ J) := by
    ext i
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_filter]
    exact ⟨fun hi => ⟨fun h => hi (hIJ h), hi⟩, fun hi => hi.2⟩
  rw [hfin, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i ∈ J <;> simp [hi]

/-- The same enlarged original deletion set is represented by masking both
test vectors inside the old deleted form. The equality is of actual random variables. -/
theorem deletedBilinear_mask (X : Ω → Matrix (Fin n) (Fin n) ℝ)
    (I J : Finset (Fin n)) (hIJ : I ⊆ J)
    (s t : EuclideanSpace ℝ (Fin n)) :
    deletedBilinear X I (mask J s) (mask J t) = deletedBilinear X J s t := by
  funext ω
  unfold deletedBilinear
  calc
    _ = ∑ i ∈ Finset.univ \ I, if i ∈ J then 0 else
        ∑ j ∈ Finset.univ \ I, if j ∈ J then 0 else X ω i j * s i * t j := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i ∈ J
      · simp [hi]
      · simp only [hi, ↓reduceIte, mask_apply_not_mem J s i hi]
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : j ∈ J <;> simp [hj]
    _ = _ := by
      rw [sum_compl_mask I J hIJ]
      apply Finset.sum_congr rfl
      intro i _
      exact sum_compl_mask I J hIJ _

section Measure

variable [MeasurableSpace Ω] {μ : Measure Ω}

/-- Enlarging a shared deterministic deletion set can only decrease the
literal weak moment. No triangle inequality or exponent-one threshold is used. -/
theorem weakMoment_antitone
    (X : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hX : ∀ i j, Measurable (fun ω => X ω i j))
    (hint : ∀ i j (p : ℝ), 0 < p → Integrable (fun ω => |X ω i j| ^ p) μ)
    (I J : Finset (Fin n)) (hIJ : I ⊆ J) (p : ℝ) (hp : 0 < p) :
    weakMoment μ X J p ≤ weakMoment μ X I p := by
  apply csSup_le (WeakMomentBasics.weak_test_set_nonempty μ X J p)
  rintro v ⟨s, t, hs, ht, rfl⟩
  rw [← deletedBilinear_mask X I J hIJ s t]
  exact WeakMomentBasics.moment_le_weakMoment X hX hint I p hp
    (mask J s) (mask J t) ((norm_mask_le J s).trans hs) ((norm_mask_le J t).trans ht)

variable [IsProbabilityMeasure μ]

/-- Monotonicity in the actual positive real moment order on a probability
space. Integrability at the higher order follows from original entry moments. -/
theorem weakMoment_mono_order
    (X : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hX : ∀ i j, Measurable (fun ω => X ω i j))
    (hint : ∀ i j (p : ℝ), 0 < p → Integrable (fun ω => |X ω i j| ^ p) μ)
    (I : Finset (Fin n)) (p q : ℝ) (hp : 0 < p) (hpq : p ≤ q) :
    weakMoment μ X I p ≤ weakMoment μ X I q := by
  apply csSup_le (WeakMomentBasics.weak_test_set_nonempty μ X I p)
  rintro v ⟨s, t, hs, ht, rfl⟩
  exact (MomentTools.mono_exponent_of_integrable p q hp hpq (deletedBilinear X I s t)
    (WeakMomentBasics.measurable_deletedBilinear X hX I s t).aestronglyMeasurable
    (WeakMomentBasics.integrable_deletedBilinear_abs_rpow X hX hint I q
      (hp.trans_le hpq) s t hs ht)).trans
    (WeakMomentBasics.moment_le_weakMoment X hX hint I q (hp.trans_le hpq) s t hs ht)

/-- The two monotonicities compose while keeping the original shared axes. -/
theorem weakMoment_le_of_subset_of_order
    (X : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hX : ∀ i j, Measurable (fun ω => X ω i j))
    (hint : ∀ i j (p : ℝ), 0 < p → Integrable (fun ω => |X ω i j| ^ p) μ)
    (I J : Finset (Fin n)) (hIJ : I ⊆ J) (p q : ℝ) (hp : 0 < p) (hpq : p ≤ q) :
    weakMoment μ X J p ≤ weakMoment μ X I q :=
  (weakMoment_antitone X hX hint I J hIJ p hp).trans
    (weakMoment_mono_order X hX hint I p q hp hpq)

end Measure
end MI32.WeakDeletionMonotonicity
