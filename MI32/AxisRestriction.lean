import MI32.Statement
import MI32.ThinMatrix
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Restriction to original Euclidean axes

Zero extension embeds a finite set of original coordinates isometrically.
Restricting either matrix axis gives exactly the original bilinear form tested
against the extended vector. Consequently every original-law weak test bound
passes to a restriction, without changing entries or introducing a new law.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace MI32.AxisRestriction

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

/-- The canonical extension by zero on the original coordinate set. -/
def zeroExtend (S : Finset I) (s : EuclideanSpace ℝ S) : EuclideanSpace ℝ I :=
  WithLp.toLp 2 (fun i => if hi : i ∈ S then s ⟨i, hi⟩ else 0)

omit [Fintype I] in
@[simp] theorem zeroExtend_apply_mem (S : Finset I) (s : EuclideanSpace ℝ S)
    (i : I) (hi : i ∈ S) : zeroExtend S s i = s ⟨i, hi⟩ := by
  simp [zeroExtend, hi]

omit [Fintype I] in
@[simp] theorem zeroExtend_apply_not_mem (S : Finset I) (s : EuclideanSpace ℝ S)
    (i : I) (hi : i ∉ S) : zeroExtend S s i = 0 := by
  simp [zeroExtend, hi]

/-- A finite sum of a zero-extended coordinate function equals its subtype sum. -/
theorem sum_extend (S : Finset I) (f : S → ℝ) :
    (∑ i : I, if hi : i ∈ S then f ⟨i, hi⟩ else 0) = ∑ i : S, f i := by
  simpa only [← Finset.univ_eq_attach] using
    (Finset.sum_attach_eq_sum_dite S f).symm

@[simp] theorem norm_zeroExtend (S : Finset I) (s : EuclideanSpace ℝ S) :
    ‖zeroExtend S s‖ = ‖s‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  calc
    ∑ i : I, (zeroExtend S s i) ^ 2 =
        ∑ i : I, if hi : i ∈ S then (s ⟨i, hi⟩) ^ 2 else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i ∈ S <;> simp [zeroExtend, hi]
    _ = ∑ i : S, (s i) ^ 2 := sum_extend S (fun i => (s i) ^ 2)

/-- Zero extension as a real linear isometry. -/
def zeroExtendIsometry (S : Finset I) :
    EuclideanSpace ℝ S →ₗᵢ[ℝ] EuclideanSpace ℝ I where
  toFun := zeroExtend S
  map_add' s t := by
    ext i
    by_cases hi : i ∈ S <;> simp [zeroExtend, hi]
  map_smul' c s := by
    ext i
    by_cases hi : i ∈ S <;> simp [zeroExtend, hi]
  norm_map' := norm_zeroExtend S

/-- The bilinear test uses the actual original entries, in their original order. -/
def bilinear (X : Matrix I J ℝ) (s : EuclideanSpace ℝ I)
    (t : EuclideanSpace ℝ J) : ℝ :=
  ∑ i, ∑ j, X i j * s i * t j

omit [DecidableEq J] in
/-- Restricting rows is exactly testing the original matrix after zero extension. -/
theorem bilinear_restrict_rows (X : Matrix I J ℝ) (S : Finset I)
    (s : EuclideanSpace ℝ S) (t : EuclideanSpace ℝ J) :
    bilinear (fun i : S => X i) s t = bilinear X (zeroExtend S s) t := by
  unfold bilinear
  symm
  calc
    ∑ i : I, ∑ j : J, X i j * zeroExtend S s i * t j =
        ∑ i : I, if hi : i ∈ S then ∑ j : J, X i j * s ⟨i, hi⟩ * t j else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i ∈ S <;> simp [zeroExtend, hi]
    _ = ∑ i : S, ∑ j : J, X i j * s i * t j :=
      sum_extend S (fun i => ∑ j : J, X i j * s i * t j)

omit [DecidableEq I] in
/-- Restricting columns has the same exact original-coordinate identity. -/
theorem bilinear_restrict_cols (X : Matrix I J ℝ) (T : Finset J)
    (s : EuclideanSpace ℝ I) (t : EuclideanSpace ℝ T) :
    bilinear (fun i (j : T) => X i j) s t = bilinear X s (zeroExtend T t) := by
  unfold bilinear
  apply Finset.sum_congr rfl
  intro i _
  symm
  calc
    ∑ j : J, X i j * s i * zeroExtend T t j =
        ∑ j : J, if hj : j ∈ T then X i j * s i * t ⟨j, hj⟩ else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : j ∈ T <;> simp [zeroExtend, hj]
    _ = ∑ j : T, X i j * s i * t j :=
      sum_extend T (fun j => X i j * s i * t j)

/-- Both restrictions can be performed together, preserving original entry identities. -/
theorem bilinear_restrict_axes (X : Matrix I J ℝ) (S : Finset I) (T : Finset J)
    (s : EuclideanSpace ℝ S) (t : EuclideanSpace ℝ T) :
    bilinear (fun (i : S) (j : T) => X i j) s t =
      bilinear X (zeroExtend S s) (zeroExtend T t) := by
  exact (bilinear_restrict_rows (fun i (j : T) => X i j) S s t).trans
    (bilinear_restrict_cols X T (zeroExtend S s) t)

variable {Ω : Type*} [MeasurableSpace Ω]

omit [DecidableEq J] in
/-- This moment identity is valid for every exponent and every original measure. -/
theorem moment_restrict_rows (μ : Measure Ω) (p : ℝ) (X : Ω → Matrix I J ℝ)
    (S : Finset I) (s : EuclideanSpace ℝ S) (t : EuclideanSpace ℝ J) :
    moment μ p (fun ω => bilinear (fun i : S => X ω i) s t) =
      moment μ p (fun ω => bilinear (X ω) (zeroExtend S s) t) := by
  congr 1
  funext ω
  exact bilinear_restrict_rows (X ω) S s t

omit [DecidableEq I] in
theorem moment_restrict_cols (μ : Measure Ω) (p : ℝ) (X : Ω → Matrix I J ℝ)
    (T : Finset J) (s : EuclideanSpace ℝ I) (t : EuclideanSpace ℝ T) :
    moment μ p (fun ω => bilinear (fun i (j : T) => X ω i j) s t) =
      moment μ p (fun ω => bilinear (X ω) s (zeroExtend T t)) := by
  congr 1
  funext ω
  exact bilinear_restrict_cols (X ω) T s t

theorem moment_restrict_axes (μ : Measure Ω) (p : ℝ) (X : Ω → Matrix I J ℝ)
    (S : Finset I) (T : Finset J) (s : EuclideanSpace ℝ S) (t : EuclideanSpace ℝ T) :
    moment μ p (fun ω => bilinear (fun (i : S) (j : T) => X ω i j) s t) =
      moment μ p (fun ω => bilinear (X ω) (zeroExtend S s) (zeroExtend T t)) := by
  congr 1
  funext ω
  exact bilinear_restrict_axes (X ω) S T s t

omit [DecidableEq J] in
/-- Any bound for deterministic original unit-ball tests applies to the same law
after restricting rows. In particular this covers every positive moment order. -/
theorem weak_test_restrict_rows (μ : Measure Ω) (p W : ℝ) (X : Ω → Matrix I J ℝ)
    (hW : ∀ s : EuclideanSpace ℝ I, ∀ t : EuclideanSpace ℝ J,
      ‖s‖ ≤ 1 → ‖t‖ ≤ 1 → moment μ p (fun ω => bilinear (X ω) s t) ≤ W)
    (S : Finset I) (s : EuclideanSpace ℝ S) (t : EuclideanSpace ℝ J)
    (hs : ‖s‖ ≤ 1) (ht : ‖t‖ ≤ 1) :
    moment μ p (fun ω => bilinear (fun i : S => X ω i) s t) ≤ W := by
  rw [moment_restrict_rows]
  exact hW _ _ (by simpa using hs) ht

omit [DecidableEq I] in
/-- The corresponding active-column weak test transfer. -/
theorem weak_test_restrict_cols (μ : Measure Ω) (p W : ℝ) (X : Ω → Matrix I J ℝ)
    (hW : ∀ s : EuclideanSpace ℝ I, ∀ t : EuclideanSpace ℝ J,
      ‖s‖ ≤ 1 → ‖t‖ ≤ 1 → moment μ p (fun ω => bilinear (X ω) s t) ≤ W)
    (T : Finset J) (s : EuclideanSpace ℝ I) (t : EuclideanSpace ℝ T)
    (hs : ‖s‖ ≤ 1) (ht : ‖t‖ ≤ 1) :
    moment μ p (fun ω => bilinear (fun i (j : T) => X ω i j) s t) ≤ W := by
  rw [moment_restrict_cols]
  exact hW _ _ hs (by simpa using ht)

theorem weak_test_restrict_axes (μ : Measure Ω) (p W : ℝ) (X : Ω → Matrix I J ℝ)
    (hW : ∀ s : EuclideanSpace ℝ I, ∀ t : EuclideanSpace ℝ J,
      ‖s‖ ≤ 1 → ‖t‖ ≤ 1 → moment μ p (fun ω => bilinear (X ω) s t) ≤ W)
    (S : Finset I) (T : Finset J) (s : EuclideanSpace ℝ S) (t : EuclideanSpace ℝ T)
    (hs : ‖s‖ ≤ 1) (ht : ‖t‖ ≤ 1) :
    moment μ p (fun ω => bilinear (fun (i : S) (j : T) => X ω i j) s t) ≤ W := by
  rw [moment_restrict_axes]
  exact hW _ _ (by simpa using hs) (by simpa using ht)

omit [MeasurableSpace Ω] [DecidableEq J] in
/-- The row identity in the exact convention of the thin-matrix theorem. -/
theorem thin_bilinear_restrict_rows (X : I → J → Ω → ℝ) (S : Finset I)
    (s : EuclideanSpace ℝ S) (t : EuclideanSpace ℝ J) :
    ThinMatrix.bilinear (fun i : S => X i) s t =
      ThinMatrix.bilinear X (zeroExtend S s) t := by
  funext ω
  simpa only [ThinMatrix.bilinear, bilinear, mul_comm] using
    bilinear_restrict_rows (fun i j => X i j ω) S s t

omit [MeasurableSpace Ω] [DecidableEq I] in
theorem thin_bilinear_restrict_cols (X : I → J → Ω → ℝ) (T : Finset J)
    (s : EuclideanSpace ℝ I) (t : EuclideanSpace ℝ T) :
    ThinMatrix.bilinear (fun i (j : T) => X i j) s t =
      ThinMatrix.bilinear X s (zeroExtend T t) := by
  funext ω
  simpa only [ThinMatrix.bilinear, bilinear, mul_comm] using
    bilinear_restrict_cols (fun i j => X i j ω) T s t

omit [DecidableEq J] in
/-- An original weak bound supplies precisely the row-restricted hypothesis of
`ThinMatrix.transposeOperator_moment_four_mul_le`, with no loss. -/
theorem thin_weak_test_restrict_rows (μ : Measure Ω) (p W : ℝ)
    (X : I → J → Ω → ℝ)
    (hW : ∀ s : EuclideanSpace ℝ I, ‖s‖ ≤ 1 →
      ∀ t : EuclideanSpace ℝ J, ‖t‖ ≤ 1 → moment μ p (ThinMatrix.bilinear X s t) ≤ W)
    (S : Finset I) (s : EuclideanSpace ℝ S) (hs : ‖s‖ ≤ 1)
    (t : EuclideanSpace ℝ J) (ht : ‖t‖ ≤ 1) :
    moment μ p (ThinMatrix.bilinear (fun i : S => X i) s t) ≤ W := by
  rw [thin_bilinear_restrict_rows]
  exact hW _ (by simpa using hs) t ht

omit [DecidableEq I] in
theorem thin_weak_test_restrict_cols (μ : Measure Ω) (p W : ℝ)
    (X : I → J → Ω → ℝ)
    (hW : ∀ s : EuclideanSpace ℝ I, ‖s‖ ≤ 1 →
      ∀ t : EuclideanSpace ℝ J, ‖t‖ ≤ 1 → moment μ p (ThinMatrix.bilinear X s t) ≤ W)
    (T : Finset J) (s : EuclideanSpace ℝ I) (hs : ‖s‖ ≤ 1)
    (t : EuclideanSpace ℝ T) (ht : ‖t‖ ≤ 1) :
    moment μ p (ThinMatrix.bilinear (fun i (j : T) => X i j) s t) ≤ W := by
  rw [thin_bilinear_restrict_cols]
  exact hW s hs _ (by simpa using ht)

omit [MeasurableSpace Ω] [DecidableEq J] in
/-- The restricted transpose is literally the original operator preceded by
the zero-extension isometry, as an equality of continuous linear maps. -/
theorem transposeOperator_restrict_rows (X : I → J → Ω → ℝ) (S : Finset I) (ω : Ω) :
    ThinMatrix.transposeOperator (fun i : S => X i) ω =
      (ThinMatrix.transposeOperator X ω).comp (zeroExtendIsometry S).toContinuousLinearMap := by
  ext s j
  change (∑ i : S, X i j ω * s i) =
    ∑ i : I, X i j ω * zeroExtend S s i
  symm
  calc
    ∑ i : I, X i j ω * zeroExtend S s i =
        ∑ i : I, if hi : i ∈ S then X i j ω * s ⟨i, hi⟩ else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i ∈ S <;> simp [zeroExtend, hi]
    _ = ∑ i : S, X i j ω * s i := sum_extend S (fun i => X i j ω * s i)

omit [MeasurableSpace Ω] [DecidableEq I] [DecidableEq J] in
/-- Transposition only swaps the deterministic test vectors in the same scalar law. -/
theorem thin_bilinear_transpose (X : I → J → Ω → ℝ)
    (s : EuclideanSpace ℝ J) (t : EuclideanSpace ℝ I) :
    ThinMatrix.bilinear (fun j i => X i j) s t = ThinMatrix.bilinear X t s := by
  funext ω
  unfold ThinMatrix.bilinear
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

omit [DecidableEq I] in
/-- The active-column estimate can use the thin-row theorem on the transpose;
the weak tests are still bounded by the original matrix tests without a loss. -/
theorem thin_weak_test_transposed_cols (μ : Measure Ω) (p W : ℝ)
    (X : I → J → Ω → ℝ)
    (hW : ∀ s : EuclideanSpace ℝ I, ‖s‖ ≤ 1 →
      ∀ t : EuclideanSpace ℝ J, ‖t‖ ≤ 1 → moment μ p (ThinMatrix.bilinear X s t) ≤ W)
    (T : Finset J) (s : EuclideanSpace ℝ T) (hs : ‖s‖ ≤ 1)
    (t : EuclideanSpace ℝ I) (ht : ‖t‖ ≤ 1) :
    moment μ p (ThinMatrix.bilinear (fun (j : T) i => X i j) s t) ≤ W := by
  rw [thin_bilinear_transpose]
  exact thin_weak_test_restrict_cols μ p W X hW T t ht s hs

end MI32.AxisRestriction
