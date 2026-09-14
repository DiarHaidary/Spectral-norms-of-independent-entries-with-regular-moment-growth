import MI32.AxisRestriction

/-!
# Thin restrictions of one original random matrix

Both estimates below use the original ordered-pair coordinates and the
original probability space. Independence of a restriction is proved by an
injective reindexing; weak tests are transported by the zero-extension
isometry. Neither restriction requires a new independence or weak-bound
certificate.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace MI32.RestrictedThinMatrix

variable {Ω I J : Type*} [MeasurableSpace Ω] [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] {μ : Measure Ω}

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
/-- The restricted row coordinates are an injective family of original pairs. -/
theorem independent_restrict_rows (X : I → J → Ω → ℝ)
    (hind : iIndepFun (fun e : I × J => X e.1 e.2) μ) (S : Finset I) :
    iIndepFun (fun e : S × J => X e.1 e.2) μ := by
  exact hind.precomp (show Function.Injective (fun e : S × J => ((e.1 : I), e.2)) from by
    intro a b h
    apply Prod.ext
    · exact Subtype.ext (congrArg (fun e : I × J => e.1) h)
    · exact congrArg (fun e : I × J => e.2) h)

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
/-- A column restriction followed by transposition still uses distinct original pairs. -/
theorem independent_transposed_cols (X : I → J → Ω → ℝ)
    (hind : iIndepFun (fun e : I × J => X e.1 e.2) μ) (T : Finset J) :
    iIndepFun (fun e : T × I => X e.2 e.1) μ := by
  exact hind.precomp (show Function.Injective (fun e : T × I => (e.2, (e.1 : J))) from by
    intro a b h
    apply Prod.ext
    · exact Subtype.ext (congrArg (fun e : I × J => e.2) h)
    · exact congrArg (fun e : I × J => e.1) h)

variable [IsProbabilityMeasure μ]

omit [DecidableEq J] in
/-- A deterministic set of at most `q` original rows has the thin transpose
estimate with the original row variance budget and original weak tests.
The fourth-`q` norm power is integrable as part of the conclusion. -/
theorem rows_moment_four_mul_le
    (X : I → J → Ω → ℝ) (hX : ∀ i j, Measurable (X i j))
    (hind : iIndepFun (fun e : I × J => X e.1 e.2) μ)
    (hsym : ∀ i j, IdentDistrib (X i j) (fun ω => -X i j ω) μ μ)
    (hint : ∀ i j (p : ℝ), 0 < p → Integrable (fun ω => |X i j ω| ^ p) μ)
    (α : ℝ) (hα : 1 ≤ α)
    (hregular : ∀ i j (r : ℝ), 1 ≤ r →
      moment μ (2 * r) (X i j) ≤ α * moment μ r (X i j))
    (q : ℕ) (hq : 1 ≤ q) (S : Finset I) (hthin : S.card ≤ q)
    (B : ℝ) (hB : 0 ≤ B)
    (hrow : ∀ i, (∑ j, ∫ ω, X i j ω ^ 2 ∂μ) ≤ B ^ 2)
    (W : ℝ) (hW : 0 ≤ W)
    (hweak : ∀ s : EuclideanSpace ℝ I, ‖s‖ ≤ 1 →
      ∀ t : EuclideanSpace ℝ J, ‖t‖ ≤ 1 →
        moment μ (2 * (q : ℝ)) (ThinMatrix.bilinear X s t) ≤ W) :
    Integrable (fun ω => ‖ThinMatrix.transposeOperator (fun i : S => X i) ω‖ ^ (4 * q)) μ ∧
      moment μ (4 * (q : ℝ))
        (fun ω => ‖ThinMatrix.transposeOperator (fun i : S => X i) ω‖) ≤
        (2 : ℝ) * (5 : ℝ) ^ (1 / 4 : ℝ) * (B + 6 * α ^ 4 * W) := by
  exact ThinMatrix.transposeOperator_moment_four_mul_le
    (fun i : S => X i) (fun i j => hX i j) (independent_restrict_rows X hind S)
    (fun i j => hsym i j) (fun i j p hp => hint i j p hp)
    α hα (fun i j r hr => hregular i j r hr)
    q hq (by simpa only [Fintype.card_coe] using hthin)
    B hB (fun i => hrow i) W hW
    (AxisRestriction.thin_weak_test_restrict_rows μ (2 * (q : ℝ)) W X hweak S)

omit [DecidableEq I] in
/-- The symmetric active-column estimate is the thin transpose theorem applied
to the transpose of the original column restriction. Its operator maps the
selected column coordinates into the full original row space. -/
theorem cols_moment_four_mul_le
    (X : I → J → Ω → ℝ) (hX : ∀ i j, Measurable (X i j))
    (hind : iIndepFun (fun e : I × J => X e.1 e.2) μ)
    (hsym : ∀ i j, IdentDistrib (X i j) (fun ω => -X i j ω) μ μ)
    (hint : ∀ i j (p : ℝ), 0 < p → Integrable (fun ω => |X i j ω| ^ p) μ)
    (α : ℝ) (hα : 1 ≤ α)
    (hregular : ∀ i j (r : ℝ), 1 ≤ r →
      moment μ (2 * r) (X i j) ≤ α * moment μ r (X i j))
    (q : ℕ) (hq : 1 ≤ q) (T : Finset J) (hthin : T.card ≤ q)
    (B : ℝ) (hB : 0 ≤ B)
    (hcol : ∀ j, (∑ i, ∫ ω, X i j ω ^ 2 ∂μ) ≤ B ^ 2)
    (W : ℝ) (hW : 0 ≤ W)
    (hweak : ∀ s : EuclideanSpace ℝ I, ‖s‖ ≤ 1 →
      ∀ t : EuclideanSpace ℝ J, ‖t‖ ≤ 1 →
        moment μ (2 * (q : ℝ)) (ThinMatrix.bilinear X s t) ≤ W) :
    Integrable
      (fun ω => ‖ThinMatrix.transposeOperator (fun (j : T) i => X i j) ω‖ ^ (4 * q)) μ ∧
      moment μ (4 * (q : ℝ))
        (fun ω => ‖ThinMatrix.transposeOperator (fun (j : T) i => X i j) ω‖) ≤
        (2 : ℝ) * (5 : ℝ) ^ (1 / 4 : ℝ) * (B + 6 * α ^ 4 * W) := by
  exact ThinMatrix.transposeOperator_moment_four_mul_le
    (fun (j : T) i => X i j) (fun j i => hX i j) (independent_transposed_cols X hind T)
    (fun j i => hsym i j) (fun j i p hp => hint i j p hp)
    α hα (fun j i r hr => hregular i j r hr)
    q hq (by simpa only [Fintype.card_coe] using hthin)
    B hB (fun j => hcol j) W hW
    (AxisRestriction.thin_weak_test_transposed_cols μ (2 * (q : ℝ)) W X hweak T)

end MI32.RestrictedThinMatrix
