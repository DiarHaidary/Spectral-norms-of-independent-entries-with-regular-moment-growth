import MI32.Statement
import MI32.VarianceScaleBasics
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic

/-!
# A nontrivial witness for the source hypothesis class

`Statement.UpperBoundAt` quantifies over every law satisfying
`Statement.RegularEntries`, so the proved upper bound would say nothing if that
class were empty or contained only degenerate laws. This module rules that out
with an explicit witness: an independent fair-sign (Rademacher) matrix on a
product of fair coins. It satisfies the regularity condition at the extreme
parameter `α = 1` and has strictly positive variance scale, so the right-hand
side of the target inequality is not identically zero on the class.

Nothing here is used by the proof of `MI32.main_upper`; it is a statement check.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace MI32.RegularWitness

/-- One half, as a point of the unit interval. -/
def half : unitInterval := ⟨1 / 2, by constructor <;> norm_num⟩

@[simp] theorem coe_half : (half : ℝ) = 1 / 2 := rfl

/-- The fair coin on `Bool`. -/
def coin : Measure Bool := ProbabilityTheory.bernoulliMeasure true false half

instance : IsProbabilityMeasure coin := by
  unfold coin; infer_instance

/-- The sign carried by one coin value. -/
def sign (b : Bool) : ℝ := if b then 1 else -1

@[simp] theorem abs_sign (b : Bool) : |sign b| = 1 := by
  cases b <;> norm_num [sign]

/-- Every absolute power of a sign is one. -/
@[simp] theorem abs_sign_rpow (b : Bool) (p : ℝ) : |sign b| ^ p = 1 := by
  simp

@[simp] theorem sign_sq (b : Bool) : sign b ^ 2 = 1 := by
  cases b <;> norm_num [sign]

@[fun_prop] theorem measurable_sign : Measurable sign := by
  unfold sign; fun_prop

/-- The fair coin centres the sign. -/
theorem integral_sign : (∫ b, sign b ∂coin) = 0 := by
  rw [coin, ProbabilityTheory.integral_bernoulliMeasure]
  norm_num [sign]

/-- The independent fair-coin sample space on the original ordered pairs. -/
abbrev Space (n : ℕ) : Type := (Fin n × Fin n) → Bool

/-- The product of fair coins, one for every original entry. -/
def coinLaw (n : ℕ) : Measure (Space n) := Measure.pi (fun _ => coin)

instance (n : ℕ) : IsProbabilityMeasure (coinLaw n) := by
  unfold coinLaw; infer_instance

/-- The explicit independent sign matrix. -/
def signMatrix {n : ℕ} (ω : Space n) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of (fun i j => sign (ω (i, j)))

@[simp] theorem signMatrix_apply {n : ℕ} (ω : Space n) (i j : Fin n) :
    signMatrix ω i j = sign (ω (i, j)) := rfl

theorem measurable_entry {n : ℕ} (i j : Fin n) :
    Measurable (fun ω : Space n => signMatrix ω i j) :=
  measurable_sign.comp (measurable_pi_apply (i, j))

/-- The original ordered entries are jointly independent, being distinct
coordinates of a product measure. -/
theorem independent_entries (n : ℕ) :
    iIndepFun (fun e : Fin n × Fin n => fun ω : Space n => signMatrix ω e.1 e.2) (coinLaw n) :=
  ProbabilityTheory.iIndepFun_pi (X := fun _ : Fin n × Fin n => sign)
    (fun _ => measurable_sign.aemeasurable)

/-- Integrals of a coordinate observable reduce to the single fair coin. -/
theorem integral_coordinate {n : ℕ} (e : Fin n × Fin n) (g : Bool → ℝ) (hg : Measurable g) :
    (∫ ω, g (ω e) ∂(coinLaw n)) = ∫ b, g b ∂coin := by
  have hmp := MeasureTheory.measurePreserving_eval (μ := fun _ : Fin n × Fin n => coin) e
  calc
    (∫ ω, g (ω e) ∂(coinLaw n)) = ∫ b, g b ∂((coinLaw n).map (Function.eval e)) :=
      (integral_map (measurable_pi_apply e).aemeasurable hg.aestronglyMeasurable).symm
    _ = ∫ b, g b ∂coin := by rw [coinLaw, hmp.map_eq]

theorem integral_entry {n : ℕ} (i j : Fin n) :
    (∫ ω, signMatrix ω i j ∂(coinLaw n)) = 0 := by
  simpa only [signMatrix_apply] using
    (integral_coordinate (i, j) sign measurable_sign).trans integral_sign

theorem integrable_entry_abs_rpow {n : ℕ} (i j : Fin n) (p : ℝ) :
    Integrable (fun ω : Space n => |signMatrix ω i j| ^ p) (coinLaw n) := by
  simpa only [signMatrix_apply, abs_sign_rpow] using
    (integrable_const (1 : ℝ) : Integrable (fun _ : Space n => (1 : ℝ)) (coinLaw n))

/-- Every absolute moment of a sign entry is one, so the source's doubling
condition holds at the extreme parameter one. -/
theorem moment_entry {n : ℕ} (i j : Fin n) (p : ℝ) :
    moment (coinLaw n) p (fun ω => signMatrix ω i j) = 1 := by
  simp only [moment, signMatrix_apply, abs_sign_rpow]
  simp

theorem regular_entry {n : ℕ} (i j : Fin n) (r : ℝ) :
    moment (coinLaw n) (2 * r) (fun ω => signMatrix ω i j) ≤
      1 * moment (coinLaw n) r (fun ω => signMatrix ω i j) := by
  rw [moment_entry i j (2 * r), moment_entry i j r]
  norm_num

/-- The witness satisfies the literal source hypothesis at `α = 1`. -/
theorem regularEntries_signMatrix (n : ℕ) :
    RegularEntries (coinLaw n) 1 (fun ω : Space n => signMatrix ω) :=
  ⟨fun i j => measurable_entry i j, independent_entries n, fun i j => integral_entry i j,
    fun i j p _ => integrable_entry_abs_rpow i j p, fun i j r _ => regular_entry i j r⟩

theorem integral_entry_sq {n : ℕ} (i j : Fin n) :
    (∫ ω, signMatrix ω i j ^ 2 ∂(coinLaw n)) = 1 := by
  simp only [signMatrix_apply, sign_sq]
  simp

theorem rowStd_signMatrix {n : ℕ} (i : Fin n) :
    VarianceScaleBasics.rowStd (μ := coinLaw n) (fun ω : Space n => signMatrix ω) i
      = Real.sqrt (n : ℝ) := by
  simp only [VarianceScaleBasics.rowStd, integral_entry_sq, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

/-- The witness has strictly positive variance scale, so the target's
right-hand side is not identically zero on the hypothesis class. -/
theorem varianceScale_pos (n : ℕ) (hn : 1 ≤ n) :
    0 < varianceScale (coinLaw n) (fun ω : Space n => signMatrix ω) := by
  let hi : Fin n := ⟨0, by omega⟩
  have hlt : (0 : ℝ) < Real.sqrt (n : ℝ) := by
    apply Real.sqrt_pos.mpr
    exact_mod_cast hn
  calc
    (0 : ℝ) < Real.sqrt (n : ℝ) := hlt
    _ = VarianceScaleBasics.rowStd (μ := coinLaw n) (fun ω : Space n => signMatrix ω) hi :=
      (rowStd_signMatrix hi).symm
    _ ≤ varianceScale (coinLaw n) (fun ω : Space n => signMatrix ω) :=
      VarianceScaleBasics.rowStd_le_varianceScale _ hi

/-- The source problem's hypothesis class is nonempty at the extreme
regularity parameter one and admits a law with strictly positive variance
scale. The proved upper bound is therefore a genuine constraint, not a
statement about an empty or degenerate class. -/
theorem exists_regularEntries (n : ℕ) (hn : 1 ≤ n) :
    ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (μ : @Measure Ω mΩ)
      (_ : @IsProbabilityMeasure Ω mΩ μ) (X : Ω → Matrix (Fin n) (Fin n) ℝ),
      @RegularEntries Ω mΩ n μ 1 X ∧ 0 < varianceScale μ X :=
  ⟨Space n, inferInstance, coinLaw n, inferInstance, fun ω => signMatrix ω,
    regularEntries_signMatrix n, varianceScale_pos n hn⟩

end MI32.RegularWitness
