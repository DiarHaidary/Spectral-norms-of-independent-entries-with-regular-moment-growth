import MI32.FiberBlockNorm
import MI32.BipartiteNorm
import MI32.ThinMatrix
import MI32.WeakMomentBasics

/-!
# Restricting the original entry family to one fiber block

The entries of one fiber block of the original matrix form an entry family
indexed by that fiber, on the same probability space and with the same
random variables. Every structural hypothesis of the local moment theorem --
measurability, joint independence, entrywise symmetry, all-order
integrability, entrywise regularity and the two `B ^ 2` variance budgets --
is inherited, the independence by an injective reindexing of ordered pairs
and the budgets because a fiber sum is a sub-sum of nonnegative integrals.

Deterministic tests transport as well: zero extension of a fiber test vector
to the original axes is a Euclidean isometry, and the block bilinear form is
*literally* an original deleted bilinear form whenever the deletion set misses
the fiber. Hence the original deleted weak moment bounds every block test with
no loss.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory

namespace MI32.RestrictedBlockFamily

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {n : ℕ}
  {K : Type*} [Fintype K] [DecidableEq K]

/-- The original entries restricted to one fiber block, indexed by that fiber. -/
def blockEntries (X : Ω → Matrix (Fin n) (Fin n) ℝ) (c : Fin n → K) (k : K) :
    {v : Fin n // c v = k} → {v : Fin n // c v = k} → Ω → ℝ :=
  fun i j ω => X ω i.val j.val

omit [MeasurableSpace Ω] [Fintype K] [DecidableEq K] in
/-- The restricted family uses the original random variables, unchanged. -/
@[simp] theorem blockEntries_apply (X : Ω → Matrix (Fin n) (Fin n) ℝ) (c : Fin n → K) (k : K)
    (i j : {v : Fin n // c v = k}) (ω : Ω) :
    blockEntries X c k i j ω = X ω i.val j.val := rfl

omit [MeasurableSpace Ω] [Fintype K] [DecidableEq K] in
/-- The rectangular matrix of the restricted family is exactly the original fiber block. -/
theorem rectangular_blockEntries (X : Ω → Matrix (Fin n) (Fin n) ℝ) (c : Fin n → K) (k : K)
    (ω : Ω) :
    BipartiteNorm.rectangular
        (fun e : {v : Fin n // c v = k} × {v : Fin n // c v = k} => blockEntries X c k e.1 e.2 ω)
      = FiberBlockNorm.blockSub (X ω) c k := rfl

section Transport

variable {X : Ω → Matrix (Fin n) (Fin n) ℝ} {c : Fin n → K} {k : K}

omit [Fintype K] [DecidableEq K] in
/-- Measurability is inherited entrywise. -/
theorem measurable_blockEntries (hX : ∀ i j, Measurable (fun ω => X ω i j)) :
    ∀ i j, Measurable (blockEntries X c k i j) :=
  fun i j => hX i.val j.val

omit [Fintype K] [DecidableEq K] in
/-- Joint independence is inherited because the fiber pairs are an injective
family of original ordered pairs. -/
theorem independent_blockEntries
    (hind : iIndepFun (fun e : Fin n × Fin n => fun ω => X ω e.1 e.2) μ) :
    iIndepFun
      (fun e : {v : Fin n // c v = k} × {v : Fin n // c v = k} => blockEntries X c k e.1 e.2) μ := by
  refine hind.precomp
    (show Function.Injective
      (fun e : {v : Fin n // c v = k} × {v : Fin n // c v = k} => (e.1.val, e.2.val)) from ?_)
  intro a b h
  apply Prod.ext
  · exact Subtype.ext (congrArg (fun e : Fin n × Fin n => e.1) h)
  · exact Subtype.ext (congrArg (fun e : Fin n × Fin n => e.2) h)

omit [Fintype K] [DecidableEq K] in
/-- Entrywise symmetry in distribution is inherited. -/
theorem symmetric_blockEntries
    (hsym : ∀ i j, IdentDistrib (fun ω => X ω i j) (fun ω => -X ω i j) μ μ) :
    ∀ i j, IdentDistrib (blockEntries X c k i j)
      (fun ω => -blockEntries X c k i j ω) μ μ :=
  fun i j => hsym i.val j.val

omit [Fintype K] [DecidableEq K] in
/-- All-order absolute integrability is inherited. -/
theorem integrable_blockEntries
    (hint : ∀ i j (p : ℝ), 0 < p → Integrable (fun ω => |X ω i j| ^ p) μ) :
    ∀ i j (p : ℝ), 0 < p → Integrable (fun ω => |blockEntries X c k i j ω| ^ p) μ :=
  fun i j p hp => hint i.val j.val p hp

omit [Fintype K] [DecidableEq K] in
/-- Entrywise moment regularity is inherited with the same constant. -/
theorem regular_blockEntries (α : ℝ)
    (hregular : ∀ i j (r : ℝ), 1 ≤ r →
      moment μ (2 * r) (fun ω => X ω i j) ≤ α * moment μ r (fun ω => X ω i j)) :
    ∀ i j (r : ℝ), 1 ≤ r →
      moment μ (2 * r) (blockEntries X c k i j) ≤ α * moment μ r (blockEntries X c k i j) :=
  fun i j r hr => hregular i.val j.val r hr

omit [Fintype K] in
/-- The surviving row budget of a fiber block is inherited from the original one. -/
theorem row_budget_blockEntries (B : ℝ)
    (hrow : ∀ i, (∑ j, ∫ ω, X ω i j ^ 2 ∂μ) ≤ B ^ 2) (i : {v : Fin n // c v = k}) :
    (∑ j, ∫ ω, blockEntries X c k i j ω ^ 2 ∂μ) ≤ B ^ 2 := by
  simp only [blockEntries_apply]
  rw [← Finset.sum_subtype (Finset.univ.filter (fun v => c v = k)) (by simp)
    (fun j => ∫ ω, X ω i.val j ^ 2 ∂μ)]
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_)
    (hrow i.val)
  intro j _ _
  exact integral_nonneg (fun _ => sq_nonneg _)

omit [Fintype K] in
/-- Likewise for columns. -/
theorem col_budget_blockEntries (B : ℝ)
    (hcol : ∀ j, (∑ i, ∫ ω, X ω i j ^ 2 ∂μ) ≤ B ^ 2) (j : {v : Fin n // c v = k}) :
    (∑ i, ∫ ω, blockEntries X c k i j ω ^ 2 ∂μ) ≤ B ^ 2 := by
  simp only [blockEntries_apply]
  rw [← Finset.sum_subtype (Finset.univ.filter (fun v => c v = k)) (by simp)
    (fun i => ∫ ω, X ω i j.val ^ 2 ∂μ)]
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_)
    (hcol j.val)
  intro i _ _
  exact integral_nonneg (fun _ => sq_nonneg _)

end Transport

/-- Zero extension of a deterministic fiber test vector to the original axes. -/
def fiberExtend (c : Fin n → K) (k : K) (s : EuclideanSpace ℝ {v : Fin n // c v = k}) :
    EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun i => if h : c i = k then s ⟨i, h⟩ else 0)

omit [Fintype K] in
/-- On its fiber the extension keeps the original coordinate. -/
theorem fiberExtend_apply_of_eq (c : Fin n → K) (k : K)
    (s : EuclideanSpace ℝ {v : Fin n // c v = k}) (i : Fin n) (h : c i = k) :
    fiberExtend c k s i = s ⟨i, h⟩ := dif_pos h

omit [Fintype K] in
/-- Off its fiber the extension vanishes. -/
theorem fiberExtend_apply_of_ne (c : Fin n → K) (k : K)
    (s : EuclideanSpace ℝ {v : Fin n // c v = k}) (i : Fin n) (h : ¬ c i = k) :
    fiberExtend c k s i = 0 := dif_neg h

omit [Fintype K] in
/-- A full original sum of a fiber-supported dependent term is the fiber sum. -/
theorem sum_fiber_dite (c : Fin n → K) (k : K) (g : {v : Fin n // c v = k} → ℝ) :
    (∑ i : Fin n, if h : c i = k then g ⟨i, h⟩ else 0) = ∑ i : {v : Fin n // c v = k}, g i := by
  have hfull : (∑ i : Fin n, if h : c i = k then g ⟨i, h⟩ else 0)
      = ∑ i ∈ Finset.univ.filter (fun v => c v = k),
          if h : c i = k then g ⟨i, h⟩ else 0 := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro x _ hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    exact dif_neg hx
  rw [hfull, Finset.sum_subtype (p := fun v => c v = k)
    (Finset.univ.filter (fun v => c v = k)) (by simp)
    (fun i => if h : c i = k then g ⟨i, h⟩ else 0)]
  exact Finset.sum_congr rfl fun a _ => dif_pos a.2

omit [Fintype K] in
/-- Zero extension of a fiber test vector preserves the Euclidean norm exactly. -/
@[simp] theorem norm_fiberExtend (c : Fin n → K) (k : K)
    (s : EuclideanSpace ℝ {v : Fin n // c v = k}) : ‖fiberExtend c k s‖ = ‖s‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  calc
    (∑ i : Fin n, (fiberExtend c k s i) ^ 2)
        = ∑ i : Fin n, if h : c i = k then (s ⟨i, h⟩) ^ 2 else 0 := by
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hi : c i = k
      · rw [dif_pos hi, fiberExtend_apply_of_eq c k s i hi]
      · rw [dif_neg hi, fiberExtend_apply_of_ne c k s i hi]
        norm_num
    _ = ∑ i : {v : Fin n // c v = k}, (s i) ^ 2 :=
      sum_fiber_dite c k (fun i => (s i) ^ 2)

omit [MeasurableSpace Ω] [Fintype K] in
/-- A fiber block's deterministic bilinear test is exactly an original deleted
bilinear test, whenever the deletion set misses that fiber. -/
theorem bilinear_blockEntries_eq_deletedBilinear
    (X : Ω → Matrix (Fin n) (Fin n) ℝ) (c : Fin n → K) (k : K)
    (I : Finset (Fin n)) (hI : ∀ i, c i = k → i ∉ I)
    (s t : EuclideanSpace ℝ {v : Fin n // c v = k}) :
    ThinMatrix.bilinear (blockEntries X c k) s t
      = deletedBilinear X I (fiberExtend c k s) (fiberExtend c k t) := by
  funext ω
  have hzeros : ∀ i ∈ I, fiberExtend c k s i = 0 := fun i hi =>
    fiberExtend_apply_of_ne c k s i (fun h => hI i h hi)
  have hzerot : ∀ j ∈ I, fiberExtend c k t j = 0 := fun j hj =>
    fiberExtend_apply_of_ne c k t j (fun h => hI j h hj)
  have hfull : deletedBilinear X I (fiberExtend c k s) (fiberExtend c k t) ω
      = ∑ i : Fin n, ∑ j : Fin n,
          X ω i j * fiberExtend c k s i * fiberExtend c k t j := by
    unfold deletedBilinear
    rw [Finset.sum_subset (Finset.subset_univ (Finset.univ \ I))]
    · refine Finset.sum_congr rfl fun i _ => ?_
      refine Finset.sum_subset (Finset.subset_univ _) ?_
      intro j _ hj
      rw [hzerot j (by simpa using hj), mul_zero]
    · intro i _ hi
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [hzeros i (by simpa using hi), mul_zero, zero_mul]
  rw [hfull]
  symm
  calc
    (∑ i : Fin n, ∑ j : Fin n, X ω i j * fiberExtend c k s i * fiberExtend c k t j)
        = ∑ i : Fin n, if h : c i = k then
            (∑ j : {v : Fin n // c v = k}, X ω i j.val * s ⟨i, h⟩ * t j) else 0 := by
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hi : c i = k
      · rw [dif_pos hi, fiberExtend_apply_of_eq c k s i hi,
          ← sum_fiber_dite c k (fun j => X ω i j.val * s ⟨i, hi⟩ * t j)]
        refine Finset.sum_congr rfl fun j _ => ?_
        by_cases hj : c j = k
        · rw [dif_pos hj, fiberExtend_apply_of_eq c k t j hj]
        · rw [dif_neg hj, fiberExtend_apply_of_ne c k t j hj, mul_zero]
      · rw [dif_neg hi]
        refine Finset.sum_eq_zero fun j _ => ?_
        rw [fiberExtend_apply_of_ne c k s i hi, mul_zero, zero_mul]
    _ = ∑ i : {v : Fin n // c v = k}, ∑ j : {v : Fin n // c v = k},
          X ω i.val j.val * s i * t j :=
      sum_fiber_dite c k
        (fun i => ∑ j : {v : Fin n // c v = k}, X ω i.val j.val * s i * t j)
    _ = ThinMatrix.bilinear (blockEntries X c k) s t ω := by
      unfold ThinMatrix.bilinear
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [blockEntries_apply]
      ring

omit [Fintype K] in
/-- Consequently the original deleted weak moment bounds every fiber block test. -/
theorem moment_bilinear_blockEntries_le_weakMoment
    (X : Ω → Matrix (Fin n) (Fin n) ℝ) (hX : ∀ i j, Measurable (fun ω => X ω i j))
    (hint : ∀ i j (p : ℝ), 0 < p → Integrable (fun ω => |X ω i j| ^ p) μ)
    (c : Fin n → K) (k : K) (I : Finset (Fin n)) (hI : ∀ i, c i = k → i ∉ I)
    (p : ℝ) (hp : 0 < p)
    (s t : EuclideanSpace ℝ {v : Fin n // c v = k}) (hs : ‖s‖ ≤ 1) (ht : ‖t‖ ≤ 1) :
    moment μ p (ThinMatrix.bilinear (blockEntries X c k) s t) ≤ weakMoment μ X I p := by
  rw [bilinear_blockEntries_eq_deletedBilinear X c k I hI s t]
  exact WeakMomentBasics.moment_le_weakMoment X hX hint I p hp _ _
    (by rw [norm_fiberExtend]; exact hs) (by rw [norm_fiberExtend]; exact ht)

end MI32.RestrictedBlockFamily
