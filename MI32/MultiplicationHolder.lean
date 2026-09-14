import MI32.MomentTools
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Holder for multiplication by a dependent random operator

The operator and its input may depend on exactly the same original
variables. Holder uses moment bounds, not independence. These statements
concern the original random functions, not their Walsh coefficient vectors.
-/

noncomputable section
open MeasureTheory

namespace MI32.MultiplicationHolder

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The exponents used by the reachable-cone argument form an actual
Holder triple. The conclusion requires no probability normalization. -/
theorem holder_partner (p : ℝ) (hp : 2 < p) :
    p.HolderTriple (2 * p / (p - 2)) 2 := by
  have hp0 : 0 < p := by linarith
  have hd0 : 0 < p - 2 := by linarith
  refine ⟨?_, hp0, by positivity⟩
  field_simp
  ring

/-- Scalar Holder in the source's rooted moment functional, with explicit
finiteness and the product's `MemLp` conclusion. -/
theorem product_moment_le (p r : ℝ) (hpr : p.HolderTriple r 2)
    (f g : Ω → ℝ) (hf : MemLp f (ENNReal.ofReal p) μ)
    (hg : MemLp g (ENNReal.ofReal r) μ) :
    MemLp (fun ω => f ω * g ω) 2 μ ∧
      moment μ 2 (fun ω => f ω * g ω) ≤ moment μ p f * moment μ r g := by
  have : ENNReal.HolderTriple (ENNReal.ofReal p) (ENNReal.ofReal r) 2 := by
    simpa using hpr.ennrealOfReal
  have hfg : MemLp (fun ω => f ω * g ω) 2 μ := hg.mul' hf
  refine ⟨hfg, ?_⟩
  have he := eLpNorm_smul_le_mul_eLpNorm (p := ENNReal.ofReal p)
    (q := ENNReal.ofReal r) (r := 2) hg.aestronglyMeasurable hf.aestronglyMeasurable
  have hr := ENNReal.toReal_mono (ENNReal.mul_ne_top hf.eLpNorm_ne_top hg.eLpNorm_ne_top) he
  rw [ENNReal.toReal_mul, toReal_eLpNorm hf.aestronglyMeasurable,
    toReal_eLpNorm hg.aestronglyMeasurable,
    toReal_eLpNorm (hf.aestronglyMeasurable.smul hg.aestronglyMeasurable)] at hr
  have hmul : (f • g : Ω → ℝ) = (fun ω => f ω * g ω) := by
    ext ω
    rfl
  rw [hmul] at hr
  rw [MomentTools.eq_lpNorm 2 (by norm_num) _ hfg.aestronglyMeasurable,
    MomentTools.eq_lpNorm p hpr.pos f hf.aestronglyMeasurable,
    MomentTools.eq_lpNorm r hpr.symm.pos g hg.aestronglyMeasurable]
  simpa only [ENNReal.ofReal_ofNat] using hr

/-- A pointwise multiplicative norm bound gives the corresponding L2
bound, even when all three random quantities share their original law. -/
theorem dominated_product_moment_le (p r : ℝ) (hpr : p.HolderTriple r 2)
    (f g h : Ω → ℝ) (hf : MemLp f (ENNReal.ofReal p) μ)
    (hg : MemLp g (ENNReal.ofReal r) μ)
    (hh : AEStronglyMeasurable h μ)
    (hf0 : ∀ ω, 0 ≤ f ω) (hg0 : ∀ ω, 0 ≤ g ω)
    (hbound : ∀ ω, |h ω| ≤ f ω * g ω) :
    MemLp h 2 μ ∧ moment μ 2 h ≤ moment μ p f * moment μ r g := by
  obtain ⟨hfg, hprod⟩ := product_moment_le p r hpr f g hf hg
  have hm : MemLp h 2 μ := hfg.of_le_mul (c := 1) hh
    (Filter.Eventually.of_forall fun ω => by
      simpa only [one_mul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hf0 ω) (hg0 ω))]
        using hbound ω)
  refine ⟨hm, ?_⟩
  have hmono : moment μ 2 h ≤ moment μ 2 (fun ω => f ω * g ω) := by
    rw [MomentTools.eq_lpNorm 2 (by norm_num) _ hh,
      MomentTools.eq_lpNorm 2 (by norm_num) _ hfg.aestronglyMeasurable]
    exact lpNorm_mono_real (by simpa using hfg) (fun ω => by simpa using hbound ω)
  exact hmono.trans hprod

/-- The original random operator acts on an input depending on the same
variables. No independent-copy replacement occurs in this estimate. -/
theorem operator_action_l2_le
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : Ω → E →L[ℝ] F) (x : Ω → E)
    (p : ℝ) (hp : 2 < p)
    (hA : MemLp (fun ω => ‖A ω‖) (ENNReal.ofReal p) μ)
    (hx : MemLp (fun ω => ‖x ω‖) (ENNReal.ofReal (2 * p / (p - 2))) μ)
    (hAx : AEStronglyMeasurable (fun ω => ‖A ω (x ω)‖) μ) :
    Integrable (fun ω => ‖A ω (x ω)‖ ^ 2) μ ∧
      moment μ 2 (fun ω => ‖A ω (x ω)‖) ≤
        moment μ p (fun ω => ‖A ω‖) *
          moment μ (2 * p / (p - 2)) (fun ω => ‖x ω‖) := by
  obtain ⟨hm, hb⟩ := dominated_product_moment_le p _ (holder_partner p hp)
    (fun ω => ‖A ω‖) (fun ω => ‖x ω‖) (fun ω => ‖A ω (x ω)‖)
    hA hx hAx (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    (fun ω => by simpa only [abs_of_nonneg (norm_nonneg _)] using (A ω).le_opNorm (x ω))
  exact ⟨hm.integrable_sq, hb⟩

end MI32.MultiplicationHolder
