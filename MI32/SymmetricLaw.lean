import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Independence.Integration
import GraphMatrices.Walsh

/-!
# Exact symmetric-law sign--magnitude transfer

Fair signs are supplied on an independent product space. Magnitudes are absolute
values of the original variables, including at zero; no positivity away from zero
or density assumption is introduced.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MI32.SymmetricLaw

/-- The fair two-point law, written as a measure rather than a finite-law certificate. -/
def fairBool : Measure Bool :=
  (1 / 2 : ℝ≥0∞) • Measure.dirac true + (1 / 2 : ℝ≥0∞) • Measure.dirac false

instance fairBool_isProbabilityMeasure : IsProbabilityMeasure fairBool := by
  constructor
  norm_num [fairBool, Measure.add_apply, Measure.smul_apply, ENNReal.inv_two_add_inv_two]

/-- Folding and reflecting a real measure counts the two signs exactly, including at zero. -/
theorem map_abs_add_map_neg_abs (ν : Measure ℝ) :
    ν.map abs + ν.map (fun x => -|x|) = ν + ν.map (fun x => -x) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_add_measure, lintegral_add_measure]
  rw [lintegral_map hf (by fun_prop : Measurable (abs : ℝ → ℝ)), lintegral_map hf (by fun_prop),
    lintegral_map hf (by fun_prop)]
  have habs : Measurable (fun x : ℝ => f |x|) := hf.comp (by fun_prop)
  rw [← lintegral_add_left habs (fun x => f (-|x|)),
    ← lintegral_add_left hf (fun x => f (-x))]
  apply lintegral_congr
  intro x
  by_cases hx : 0 ≤ x
  · simp [abs_of_nonneg hx]
  · simp [abs_of_neg (lt_of_not_ge hx), add_comm]

/-- Reconstruction map on a fair sign and a real input whose magnitude is retained. -/
def signedAbs (bx : Bool × ℝ) : ℝ := GraphMatrices.Walsh.sign bx.1 * |bx.2|

@[fun_prop] theorem measurable_signedAbs : Measurable signedAbs := by
  have hsign : Measurable GraphMatrices.Walsh.sign := Measurable.of_discrete
  exact (hsign.comp measurable_fst).mul (by fun_prop)

/-- The actual pushforward of an independent fair sign times the input magnitude. -/
theorem map_signedAbs (ν : Measure ℝ) [SigmaFinite ν] :
    (fairBool.prod ν).map signedAbs =
      (1 / 2 : ℝ≥0∞) • ν.map abs + (1 / 2 : ℝ≥0∞) • ν.map (fun x => -|x|) := by
  unfold fairBool
  rw [Measure.add_prod, Measure.map_add _ _ measurable_signedAbs]
  simp only [Measure.prod_smul_left, Measure.map_smul, Measure.dirac_prod,
    Measure.map_map measurable_signedAbs measurable_prodMk_left]
  simp [signedAbs, GraphMatrices.Walsh.sign, Function.comp_def]

/-- Exact scalar law transfer under the explicit reflection-symmetry hypothesis. -/
theorem map_signedAbs_eq (ν : Measure ℝ) [SigmaFinite ν]
    (hsym : ν.map (fun x => -x) = ν) :
    (fairBool.prod ν).map signedAbs = ν := by
  rw [map_signedAbs, ← smul_add, map_abs_add_map_neg_abs, hsym, smul_add, ← add_smul]
  norm_num [ENNReal.inv_two_add_inv_two]





section Joint

variable {E : Type*} [Fintype E]

/-- Independent fair signs, one for each original variable. -/
def fairSigns : Measure (E → Bool) := Measure.pi fun _ => fairBool

instance fairSigns_isProbabilityMeasure : IsProbabilityMeasure (fairSigns (E := E)) := by
  unfold fairSigns
  infer_instance

/-- The coordinatewise reconstruction map on independent sign and original-value vectors. -/
def signedAbsVector (p : (E → Bool) × (E → ℝ)) : E → ℝ :=
  fun e => GraphMatrices.Walsh.sign (p.1 e) * |p.2 e|

omit [Fintype E] in
@[fun_prop] theorem measurable_signedAbsVector : Measurable (signedAbsVector (E := E)) := by
  apply measurable_pi_lambda
  intro e
  have hp : Measurable (fun p : (E → Bool) × (E → ℝ) => (p.1 e, p.2 e)) := by fun_prop
  exact measurable_signedAbs.comp hp

/-- The scalar exact law tensorizes through the genuine product of original marginal laws. -/
theorem map_signedAbsVector_eq (ν : E → Measure ℝ) [∀ e, SigmaFinite (ν e)]
    (hsym : ∀ e, (ν e).map (fun x => -x) = ν e) :
    ((fairSigns (E := E)).prod (Measure.pi ν)).map signedAbsVector = Measure.pi ν := by
  have hpair := measurePreserving_arrowProdEquivProdArrow Bool ℝ E
    (fun _ => fairBool) ν
  change ((Measure.pi fun _ : E => fairBool).prod (Measure.pi ν)).map _ = _
  rw [← hpair.map_eq, Measure.map_map measurable_signedAbsVector hpair.measurable]
  change (Measure.pi fun e => fairBool.prod (ν e)).map
    (fun x e => signedAbs (x e)) = Measure.pi ν
  exact (measurePreserving_pi (fun e => fairBool.prod (ν e)) ν
    (fun e => ⟨measurable_signedAbs, map_signedAbs_eq (ν e) (hsym e)⟩)).map_eq

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [Fintype E] [IsProbabilityMeasure μ] in
/-- Absolute values retain independence of the original coordinate family. -/
theorem independent_abs (W : E → Ω → ℝ) (hind : iIndepFun W μ) :
    iIndepFun (fun e ω => |W e ω|) μ := by
  exact hind.comp (fun _ => abs) (fun _ => by fun_prop)

/-- An actual jointly independent symmetric family has exactly the same joint law as
independent fair signs times its original absolute values on the product probability space. -/
theorem map_independent_signedAbs_eq_original (W : E → Ω → ℝ)
    (hW : ∀ e, Measurable (W e)) (hind : iIndepFun W μ)
    (hsym : ∀ e, IdentDistrib (W e) (fun ω => -W e ω) μ μ) :
    ((fairSigns (E := E)).prod μ).map
      (fun p : (E → Bool) × Ω => fun e => GraphMatrices.Walsh.sign (p.1 e) * |W e p.2|) =
      μ.map (fun ω e => W e ω) := by
  have hvec : Measurable (fun ω e => W e ω) := measurable_pi_lambda _ hW
  have hmarg (e : E) : (μ.map (W e)).map (fun x => -x) = μ.map (W e) := by
    rw [Measure.map_map (by fun_prop) (hW e)]
    exact (hsym e).map_eq.symm
  have hpush : ((fairSigns (E := E)).prod μ).map
      (fun p : (E → Bool) × Ω => (p.1, fun e => W e p.2)) =
      (fairSigns (E := E)).prod (μ.map (fun ω e => W e ω)) := by
    have heq : Prod.map (id : (E → Bool) → (E → Bool)) (fun ω e => W e ω) =
        (fun p : (E → Bool) × Ω => (p.1, fun e => W e p.2)) := rfl
    simpa only [Measure.map_id, heq] using
      (Measure.map_prod_map (fairSigns (E := E)) μ measurable_id hvec).symm
  calc
    _ = ((fairSigns (E := E)).prod (μ.map (fun ω e => W e ω))).map signedAbsVector := by
      rw [← hpush, Measure.map_map measurable_signedAbsVector (by fun_prop)]
      rfl
    _ = _ := by
      rw [hind.map_fun_eq_pi_map (fun e => (hW e).aemeasurable)]
      exact map_signedAbsVector_eq (fun e => μ.map (W e)) hmarg





/-- Identical joint distributions, with the original family on the left. -/
theorem identDistrib_independent_signedAbs (W : E → Ω → ℝ)
    (hW : ∀ e, Measurable (W e)) (hind : iIndepFun W μ)
    (hsym : ∀ e, IdentDistrib (W e) (fun ω => -W e ω) μ μ) :
    IdentDistrib (fun ω e => W e ω)
      (fun p : (E → Bool) × Ω => fun e => GraphMatrices.Walsh.sign (p.1 e) * |W e p.2|)
      μ ((fairSigns (E := E)).prod μ) := by
  have hvec : Measurable (fun ω e => W e ω) := measurable_pi_lambda _ hW
  have hp : Measurable (fun p : (E → Bool) × Ω => (p.1, fun e => W e p.2)) := by fun_prop
  exact ⟨hvec.aemeasurable, (measurable_signedAbsVector.comp hp).aemeasurable,
    (map_independent_signedAbs_eq_original W hW hind hsym).symm⟩

/-- Every measurable observable has the same ordinary integral under the exact law transfer. -/
theorem integral_eq_signedAbs (W : E → Ω → ℝ)
    (hW : ∀ e, Measurable (W e)) (hind : iIndepFun W μ)
    (hsym : ∀ e, IdentDistrib (W e) (fun ω => -W e ω) μ μ)
    (f : (E → ℝ) → ℝ) (hf : Measurable f) :
    (∫ ω, f (fun e => W e ω) ∂μ) =
      ∫ p : (E → Bool) × Ω,
        f (fun e => GraphMatrices.Walsh.sign (p.1 e) * |W e p.2|)
        ∂((fairSigns (E := E)).prod μ) :=
  ((identDistrib_independent_signedAbs W hW hind hsym).comp hf).integral_eq

end Joint

section FiniteSignIntegral

open scoped BigOperators
variable {E : Type*} [Fintype E] [DecidableEq E]

@[simp] theorem fairBool_singleton (b : Bool) : fairBool {b} = (1 / 2 : ℝ≥0∞) := by
  cases b <;> norm_num [fairBool, Measure.add_apply, Measure.smul_apply]

omit [DecidableEq E] in
@[simp] theorem fairSigns_singleton (σ : E → Bool) :
    (fairSigns (E := E)) {σ} = (1 / 2 : ℝ≥0∞) ^ Fintype.card E := by
  simp [fairSigns, Measure.pi_singleton]

omit [DecidableEq E] in
@[simp] theorem fairSigns_real_singleton (σ : E → Bool) :
    (fairSigns (E := E)).real {σ} = (1 / 2 : ℝ) ^ Fintype.card E := by
  simp [measureReal_def]

/-- The actual product measure agrees with the complete finite Walsh sign average. -/
theorem integral_fairSigns (f : (E → Bool) → ℝ) :
    (∫ σ, f σ ∂(fairSigns (E := E))) = GraphMatrices.Walsh.expectation f := by
  rw [integral_fintype Integrable.of_finite]
  simp only [fairSigns_real_singleton, smul_eq_mul, GraphMatrices.Walsh.expectation,
    div_eq_mul_inv, one_mul, inv_pow, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro σ _
  exact mul_comm _ _

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [SFinite μ]

/-- Fubini connects the probability-space sign construction to the finite averages
used by the parity and positive-cone modules; integrability is explicitly charged. -/
theorem integral_prod_fairSigns (f : (E → Bool) × Ω → ℝ)
    (hint : Integrable f ((fairSigns (E := E)).prod μ)) :
    (∫ p, f p ∂((fairSigns (E := E)).prod μ)) =
      ∫ ω, GraphMatrices.Walsh.expectation (fun σ => f (σ, ω)) ∂μ := by
  rw [integral_prod_symm f hint]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun ω => integral_fairSigns (fun σ => f (σ, ω))

end FiniteSignIntegral




section ObservableTransfer

variable {E Ω : Type*} [Fintype E] [DecidableEq E] [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Complete transfer to the exact conditional finite-sign average used in the
positive-cone proof. Only the original observable's integrability is assumed;
product-space integrability follows from identical distributions. -/
theorem integral_eq_walsh_signedAbs (W : E → Ω → ℝ)
    (hW : ∀ e, Measurable (W e)) (hind : iIndepFun W μ)
    (hsym : ∀ e, IdentDistrib (W e) (fun ω => -W e ω) μ μ)
    (f : (E → ℝ) → ℝ) (hf : Measurable f)
    (hint : Integrable (fun ω => f (fun e => W e ω)) μ) :
    (∫ ω, f (fun e => W e ω) ∂μ) =
      ∫ ω, GraphMatrices.Walsh.expectation
        (fun σ => f (fun e => GraphMatrices.Walsh.sign (σ e) * |W e ω|)) ∂μ := by
  have hident := (identDistrib_independent_signedAbs W hW hind hsym).comp hf
  refine (integral_eq_signedAbs W hW hind hsym f hf).trans ?_
  exact integral_prod_fairSigns _ (hident.integrable_snd hint)

end ObservableTransfer

end MI32.SymmetricLaw
