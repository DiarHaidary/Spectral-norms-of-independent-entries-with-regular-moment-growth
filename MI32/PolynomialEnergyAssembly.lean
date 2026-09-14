import MI32.PolynomialSectorEnergy
import MI32.MomentTools

/-!
# Exact finite-sector assembly of original polynomial energies

This is an intermediate assembly step. Its premises are individual
sector energy estimates, to be supplied by the separately proved sector
contractions. It does not prove those estimates or the full MI-32 bound.
The exact original-law energy partitions introduce no sector-count loss.
Input and output coordinate and term types may differ, while every
polynomial uses the same original independent symmetric random family.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace MI32.PolynomialEnergyAssembly

open PolynomialSectorMasks PolynomialSectorEnergy SymmetricPositiveCone

section Covers

variable {E A B D : Type*} [Fintype E] [DecidableEq E]
    [Fintype A] [Fintype B] [DecidableEq D]

/-- Explicit finite cover of both actual coordinate/parity label ranges.
Its construction is finite; no small-cardinality claim is implicit. -/
def commonLabelCover (labelIn : A → Finset E → D) (labelOut : B → Finset E → D) : Finset D :=
  (Finset.univ.image (fun p : A × Finset E => labelIn p.1 p.2)) ∪
    (Finset.univ.image (fun p : B × Finset E => labelOut p.1 p.2))

omit [DecidableEq E] in
theorem mem_commonLabelCover_in (labelIn : A → Finset E → D) (labelOut : B → Finset E → D)
    (a : A) (S : Finset E) : labelIn a S ∈ commonLabelCover labelIn labelOut := by
  exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ (a, S)))

omit [DecidableEq E] in
theorem mem_commonLabelCover_out (labelIn : A → Finset E → D) (labelOut : B → Finset E → D)
    (b : B) (S : Finset E) : labelOut b S ∈ commonLabelCover labelIn labelOut := by
  exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ (b, S)))

omit [DecidableEq E] in
/-- The explicit cover costs no more than the number of input and output
coordinate/parity pairs. The analytic assembly below does not pay this factor. -/
theorem commonLabelCover_card_le
    (labelIn : A → Finset E → D) (labelOut : B → Finset E → D) :
    (commonLabelCover labelIn labelOut).card ≤
      Fintype.card (A × Finset E) + Fintype.card (B × Finset E) := by
  unfold commonLabelCover
  exact (Finset.card_union_le _ _).trans (Nat.add_le_add
    (Finset.card_image_le.trans_eq (Finset.card_univ))
    (Finset.card_image_le.trans_eq (Finset.card_univ)))

end Covers

section OriginalLaw

variable {Ω E A B K H D : Type*} [MeasurableSpace Ω]
    [Fintype E] [DecidableEq E] [Fintype A] [Fintype B] [Fintype K] [Fintype H]
    [DecidableEq D] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Assemble proved estimates on a common finite set of exact sectors.
The conclusion concerns the actual original Hilbert polynomial energies;
signed coefficients are allowed and no global operator estimate is assumed. -/
theorem second_energy_le
    (W : E → Ω → ℝ) (hW : ∀ e, Measurable (W e)) (hind : iIndepFun W μ)
    (hsym : ∀ e, IdentDistrib (W e) (fun ω => -W e ω) μ μ)
    (hint : ∀ e (p : ℝ), 0 < p → Integrable (fun ω => |W e ω| ^ p) μ)
    (cIn : A → K → ℝ) (νIn : A → K → E → ℕ)
    (cOut : B → H → ℝ) (νOut : B → H → E → ℕ)
    (labelIn : A → Finset E → D) (labelOut : B → Finset E → D)
    (L : Finset D) (hIn : ∀ a S, labelIn a S ∈ L) (hOut : ∀ b S, labelOut b S ∈ L)
    (M : ℝ)
    (hsector : ∀ d ∈ L,
      (∫ ω, ‖evaluateHilbert (maskCoeff (fun b S => labelOut b S = d) cOut νOut)
        νOut (fun e => W e ω)‖ ^ 2 ∂μ) ≤
      M ^ 2 * ∫ ω, ‖evaluateHilbert (maskCoeff (fun a S => labelIn a S = d) cIn νIn)
        νIn (fun e => W e ω)‖ ^ 2 ∂μ) :
    (∫ ω, ‖evaluateHilbert cOut νOut (fun e => W e ω)‖ ^ 2 ∂μ) ≤
      M ^ 2 * ∫ ω, ‖evaluateHilbert cIn νIn (fun e => W e ω)‖ ^ 2 ∂μ := by
  calc
    _ = ∑ d ∈ L, ∫ ω,
        ‖evaluateHilbert (maskCoeff (fun b S => labelOut b S = d) cOut νOut)
          νOut (fun e => W e ω)‖ ^ 2 ∂μ :=
      (sum_sector_second_energies W hW hind hsym hint labelOut L hOut cOut νOut).symm
    _ ≤ ∑ d ∈ L, M ^ 2 * ∫ ω,
        ‖evaluateHilbert (maskCoeff (fun a S => labelIn a S = d) cIn νIn)
          νIn (fun e => W e ω)‖ ^ 2 ∂μ := Finset.sum_le_sum hsector
    _ = M ^ 2 * ∑ d ∈ L, ∫ ω,
        ‖evaluateHilbert (maskCoeff (fun a S => labelIn a S = d) cIn νIn)
          νIn (fun e => W e ω)‖ ^ 2 ∂μ := (Finset.mul_sum _ _ _).symm
    _ = _ := by rw [sum_sector_second_energies W hW hind hsym hint labelIn L hIn cIn νIn]

/-- The actual second-moment comparison follows with the same factor M,
after the finite sector energy estimates have been established. -/
theorem second_moment_le
    (W : E → Ω → ℝ) (hW : ∀ e, Measurable (W e)) (hind : iIndepFun W μ)
    (hsym : ∀ e, IdentDistrib (W e) (fun ω => -W e ω) μ μ)
    (hint : ∀ e (p : ℝ), 0 < p → Integrable (fun ω => |W e ω| ^ p) μ)
    (cIn : A → K → ℝ) (νIn : A → K → E → ℕ)
    (cOut : B → H → ℝ) (νOut : B → H → E → ℕ)
    (labelIn : A → Finset E → D) (labelOut : B → Finset E → D)
    (L : Finset D) (hIn : ∀ a S, labelIn a S ∈ L) (hOut : ∀ b S, labelOut b S ∈ L)
    (M : ℝ) (hM : 0 ≤ M)
    (hsector : ∀ d ∈ L,
      (∫ ω, ‖evaluateHilbert (maskCoeff (fun b S => labelOut b S = d) cOut νOut)
        νOut (fun e => W e ω)‖ ^ 2 ∂μ) ≤
      M ^ 2 * ∫ ω, ‖evaluateHilbert (maskCoeff (fun a S => labelIn a S = d) cIn νIn)
        νIn (fun e => W e ω)‖ ^ 2 ∂μ) :
    moment μ 2 (fun ω => ‖evaluateHilbert cOut νOut (fun e => W e ω)‖) ≤
      M * moment μ 2 (fun ω => ‖evaluateHilbert cIn νIn (fun e => W e ω)‖) := by
  exact MomentTools.even_moment_le_of_integral_le
    (fun ω => ‖evaluateHilbert cOut νOut (fun e => W e ω)‖)
    (fun ω => ‖evaluateHilbert cIn νIn (fun e => W e ω)‖) M hM 2 (by norm_num)
    (by decide) (second_energy_le W hW hind hsym hint cIn νIn cOut νOut
      labelIn labelOut L hIn hOut M hsector)

/-- Bounds valid for every exact label automatically assemble over the
finite union of actual input/output label ranges. No finite label type is required. -/
theorem second_moment_le_of_all_sectors
    (W : E → Ω → ℝ) (hW : ∀ e, Measurable (W e)) (hind : iIndepFun W μ)
    (hsym : ∀ e, IdentDistrib (W e) (fun ω => -W e ω) μ μ)
    (hint : ∀ e (p : ℝ), 0 < p → Integrable (fun ω => |W e ω| ^ p) μ)
    (cIn : A → K → ℝ) (νIn : A → K → E → ℕ)
    (cOut : B → H → ℝ) (νOut : B → H → E → ℕ)
    (labelIn : A → Finset E → D) (labelOut : B → Finset E → D)
    (M : ℝ) (hM : 0 ≤ M)
    (hsector : ∀ d,
      (∫ ω, ‖evaluateHilbert (maskCoeff (fun b S => labelOut b S = d) cOut νOut)
        νOut (fun e => W e ω)‖ ^ 2 ∂μ) ≤
      M ^ 2 * ∫ ω, ‖evaluateHilbert (maskCoeff (fun a S => labelIn a S = d) cIn νIn)
        νIn (fun e => W e ω)‖ ^ 2 ∂μ) :
    moment μ 2 (fun ω => ‖evaluateHilbert cOut νOut (fun e => W e ω)‖) ≤
      M * moment μ 2 (fun ω => ‖evaluateHilbert cIn νIn (fun e => W e ω)‖) :=
  second_moment_le W hW hind hsym hint cIn νIn cOut νOut labelIn labelOut
    (commonLabelCover labelIn labelOut) (mem_commonLabelCover_in labelIn labelOut)
    (mem_commonLabelCover_out labelIn labelOut) M hM (fun d _ => hsector d)

end OriginalLaw

end MI32.PolynomialEnergyAssembly
