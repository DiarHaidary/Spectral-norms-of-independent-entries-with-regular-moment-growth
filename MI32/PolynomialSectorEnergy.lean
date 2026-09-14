import MI32.PolynomialSectorMasks
import MI32.SymmetricPositiveCone

/-!
# Orthogonal sector energies under the actual original symmetric laws

The raw polynomial coefficients may be signed. Exact joint-law transfer
and conditional Walsh orthogonality give actual-law energy contractions
and exact finite sector partitions. Original exponents, shared variables,
and all spectator magnitudes are retained by every mask. Integrability
is established before every interchange of finite sums and expectations.
-/

noncomputable section
open scoped BigOperators InnerProductSpace
open MeasureTheory ProbabilityTheory GraphMatrices

namespace MI32.PolynomialSectorEnergy

open PositivePolynomial PolynomialSectorMasks SymmetricPositiveCone

variable {Ω E A K : Type*} [MeasurableSpace Ω]
    [Fintype E] [DecidableEq E] [Fintype A] [Fintype K]
    {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [DecidableEq E] in
/-- Original polynomial second energies are integrable, including for signed
coefficients and any raw coefficient mask. -/
theorem integrable_original_norm_sq
    (W : E → Ω → ℝ) (hW : ∀ e, Measurable (W e)) (hind : iIndepFun W μ)
    (hint : ∀ e (p : ℝ), 0 < p → Integrable (fun ω => |W e ω| ^ p) μ)
    (c : A → K → ℝ) (ν : A → K → E → ℕ) :
    Integrable (fun ω => ‖evaluateHilbert c ν (fun e => W e ω)‖ ^ 2) μ := by
  simpa only [evaluateHilbert_norm_sq] using integrable_normSq W hW hind hint c ν

/-- Fubini integrability of the exact conditional sign energy follows from
the integrable original-law polynomial energy and exact sign/magnitude law transfer. -/
theorem integrable_conditionalEnergy
    (W : E → Ω → ℝ) (hW : ∀ e, Measurable (W e)) (hind : iIndepFun W μ)
    (hsym : ∀ e, IdentDistrib (W e) (fun ω => -W e ω) μ μ)
    (hint : ∀ e (p : ℝ), 0 < p → Integrable (fun ω => |W e ω| ^ p) μ)
    (c : A → K → ℝ) (ν : A → K → E → ℕ) :
    Integrable (fun ω => conditionalEnergy c ν (fun e => |W e ω|)) μ := by
  have hident := (SymmetricLaw.identDistrib_independent_signedAbs W hW hind hsym).comp
    (measurable_normSq c ν)
  have hprod : Integrable
      (fun p : (E → Bool) × Ω => normSq c ν
        (fun e => Walsh.sign (p.1 e) * |W e p.2|)) ((SymmetricLaw.fairSigns (E := E)).prod μ) :=
    hident.integrable_snd (integrable_normSq W hW hind hint c ν)
  have hcond : Integrable
      (fun ω => ∫ σ, normSq c ν (fun e => Walsh.sign (σ e) * |W e ω|)
        ∂(SymmetricLaw.fairSigns (E := E))) μ := hprod.integral_prod_right
  convert hcond using 1
  funext ω
  exact (SymmetricLaw.integral_fairSigns
    (fun σ => normSq c ν (fun e => Walsh.sign (σ e) * |W e ω|))).symm

/-- Exact second-energy transfer for the original Hilbert polynomial.
No positivity, regularity, or vector-norm comparison is assumed. -/
theorem integral_norm_sq_eq_conditionalEnergy
    (W : E → Ω → ℝ) (hW : ∀ e, Measurable (W e)) (hind : iIndepFun W μ)
    (hsym : ∀ e, IdentDistrib (W e) (fun ω => -W e ω) μ μ)
    (hint : ∀ e (p : ℝ), 0 < p → Integrable (fun ω => |W e ω| ^ p) μ)
    (c : A → K → ℝ) (ν : A → K → E → ℕ) :
    (∫ ω, ‖evaluateHilbert c ν (fun e => W e ω)‖ ^ 2 ∂μ) =
      ∫ ω, conditionalEnergy c ν (fun e => |W e ω|) ∂μ := by
  simp only [evaluateHilbert_norm_sq]
  exact SymmetricLaw.integral_eq_walsh_signedAbs W hW hind hsym
    (normSq c ν) (measurable_normSq c ν) (integrable_normSq W hW hind hint c ν)

/-- Every output-coordinate/parity mask contracts the second energy of
the original Hilbert polynomial, with exact constant one. -/
theorem masked_second_energy_le
    (W : E → Ω → ℝ) (hW : ∀ e, Measurable (W e)) (hind : iIndepFun W μ)
    (hsym : ∀ e, IdentDistrib (W e) (fun ω => -W e ω) μ μ)
    (hint : ∀ e (p : ℝ), 0 < p → Integrable (fun ω => |W e ω| ^ p) μ)
    (P : A → Finset E → Prop) (c : A → K → ℝ) (ν : A → K → E → ℕ) :
    (∫ ω, ‖evaluateHilbert (maskCoeff P c ν) ν (fun e => W e ω)‖ ^ 2 ∂μ) ≤
      ∫ ω, ‖evaluateHilbert c ν (fun e => W e ω)‖ ^ 2 ∂μ := by
  rw [integral_norm_sq_eq_conditionalEnergy W hW hind hsym hint,
    integral_norm_sq_eq_conditionalEnergy W hW hind hsym hint]
  exact integral_mono
    (integrable_conditionalEnergy W hW hind hsym hint (maskCoeff P c ν) ν)
    (integrable_conditionalEnergy W hW hind hsym hint c ν)
    (fun ω => conditionalEnergy_mask_le P c ν (fun e => |W e ω|))

/-- A finite cover of the exact coordinate/parity labels partitions the
original polynomial's second energy with no loss in the number of sectors. -/
theorem sum_sector_second_energies
    {D : Type*} [DecidableEq D]
    (W : E → Ω → ℝ) (hW : ∀ e, Measurable (W e)) (hind : iIndepFun W μ)
    (hsym : ∀ e, IdentDistrib (W e) (fun ω => -W e ω) μ μ)
    (hint : ∀ e (p : ℝ), 0 < p → Integrable (fun ω => |W e ω| ^ p) μ)
    (label : A → Finset E → D) (L : Finset D) (hL : ∀ a S, label a S ∈ L)
    (c : A → K → ℝ) (ν : A → K → E → ℕ) :
    (∑ d ∈ L, ∫ ω,
      ‖evaluateHilbert (maskCoeff (fun a S => label a S = d) c ν) ν (fun e => W e ω)‖ ^ 2 ∂μ) =
      ∫ ω, ‖evaluateHilbert c ν (fun e => W e ω)‖ ^ 2 ∂μ := by
  simp_rw [integral_norm_sq_eq_conditionalEnergy W hW hind hsym hint]
  rw [← integral_finsetSum L (fun d _ =>
    integrable_conditionalEnergy W hW hind hsym hint (maskCoeff (fun a S => label a S = d) c ν) ν)]
  exact integral_congr_ae (Filter.Eventually.of_forall fun ω =>
    sum_conditionalEnergy_sectors label L hL c ν (fun e => |W e ω|))

/-- Conditional cross energy vanishes for disjoint coordinate/parity masks,
with all original magnitude polynomials retained in both factors. -/
theorem conditional_disjoint_mask_inner_eq_zero
    (P Q : A → Finset E → Prop) (hdisj : ∀ a S, P a S → ¬Q a S)
    (c : A → K → ℝ) (ν : A → K → E → ℕ) (z : E → ℝ) :
    Walsh.expectation (fun σ : E → Bool =>
      ⟪evaluateHilbert (maskCoeff P c ν) ν (fun e => Walsh.sign (σ e) * z e),
        evaluateHilbert (maskCoeff Q c ν) ν (fun e => Walsh.sign (σ e) * z e)⟫_ℝ) = 0 := by
  classical
  simp only [evaluateHilbert, EuclideanSpace.inner_toLp_toLp, dotProduct, star_trivial]
  rw [Walsh.expectation_finset_sum]
  apply Finset.sum_eq_zero
  intro a _
  have hp (σ : E → Bool) := RawParity.evaluate_sign_eq_walsh (maskCoeff P c ν a) (ν a)
    Finset.univ (fun _ => Finset.mem_univ _) σ z
  have hq (σ : E → Bool) := RawParity.evaluate_sign_eq_walsh (maskCoeff Q c ν a) (ν a)
    Finset.univ (fun _ => Finset.mem_univ _) σ z
  simp_rw [hp, hq]
  rw [Walsh.polynomial_pairing]
  simp_rw [sectionCoeff_mask]
  apply Finset.sum_eq_zero
  intro S _
  by_cases hP : P a S
  · simp [hP, hdisj a S hP]
  · simp [hP]

omit [DecidableEq E] in
/-- Mixed original polynomial energies are integrable by actual scalar L2
integrability in each coordinate, before any expectation identity is used. -/
theorem integrable_polynomial_inner
    (W : E → Ω → ℝ) (hW : ∀ e, Measurable (W e)) (hind : iIndepFun W μ)
    (hint : ∀ e (p : ℝ), 0 < p → Integrable (fun ω => |W e ω| ^ p) μ)
    (c d : A → K → ℝ) (ν : A → K → E → ℕ) :
    Integrable (fun ω =>
      ⟪evaluateHilbert c ν (fun e => W e ω), evaluateHilbert d ν (fun e => W e ω)⟫_ℝ) μ := by
  have hLp (b : A → K → ℝ) (a : A) :
      MemLp (fun ω => evaluate (b a) (ν a) (fun e => W e ω)) 2 μ := by
    apply (memLp_two_iff_integrable_sq (by unfold evaluate monomial; fun_prop)).mpr
    exact PositiveCone.integrable_evaluate_sq W hW hind
      (integrable_nat_powers W hW hint) (b a) (ν a)
  simp only [evaluateHilbert, EuclideanSpace.inner_toLp_toLp, dotProduct, star_trivial]
  exact integrable_finsetSum _ (fun a _ => (hLp d a).integrable_mul (hLp c a))

/-- Distinct retained sectors are orthogonal under the actual original
independent symmetric laws, not just under an assumed conditional model. -/
theorem integral_disjoint_mask_inner_eq_zero
    (W : E → Ω → ℝ) (hW : ∀ e, Measurable (W e)) (hind : iIndepFun W μ)
    (hsym : ∀ e, IdentDistrib (W e) (fun ω => -W e ω) μ μ)
    (hint : ∀ e (p : ℝ), 0 < p → Integrable (fun ω => |W e ω| ^ p) μ)
    (P Q : A → Finset E → Prop) (hdisj : ∀ a S, P a S → ¬Q a S)
    (c : A → K → ℝ) (ν : A → K → E → ℕ) :
    (∫ ω, ⟪evaluateHilbert (maskCoeff P c ν) ν (fun e => W e ω),
      evaluateHilbert (maskCoeff Q c ν) ν (fun e => W e ω)⟫_ℝ ∂μ) = 0 := by
  have hm : Measurable (fun z : E → ℝ =>
      ⟪evaluateHilbert (maskCoeff P c ν) ν z, evaluateHilbert (maskCoeff Q c ν) ν z⟫_ℝ) := by
    simp only [evaluateHilbert, EuclideanSpace.inner_toLp_toLp, dotProduct, star_trivial]
    unfold evaluate monomial
    fun_prop
  rw [SymmetricLaw.integral_eq_walsh_signedAbs W hW hind hsym _ hm
    (integrable_polynomial_inner W hW hind hint (maskCoeff P c ν) (maskCoeff Q c ν) ν)]
  simp_rw [conditional_disjoint_mask_inner_eq_zero P Q hdisj c ν]
  simp

end MI32.PolynomialSectorEnergy
