import MI32.Statement
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Tactic

/-!
# Calculus for the actual MI-32 moment functional

The definitions use ordinary real integrals. The bridges to `MemLp` make
all finiteness assumptions explicit before applying Minkowski or monotonicity.
Algebraic identities hold on arbitrary measure spaces; normalization of
constants and comparison of moment orders use probability measures.
-/

noncomputable section
open MeasureTheory

namespace MI32.MomentTools

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem nonneg (p : ℝ) (f : Ω → ℝ) : 0 ≤ moment μ p f :=
  Real.rpow_nonneg (integral_nonneg fun _ => Real.rpow_nonneg (abs_nonneg _) _) _

/-- Pure root algebra for an ordinary positive natural-power comparison. -/
theorem nat_root_le (I J C : ℝ) (hI : 0 ≤ I) (hJ : 0 ≤ J) (hC : 0 ≤ C)
    (n : ℕ) (hn : 1 ≤ n) (h : I ≤ C ^ n * J) :
    I ^ (1 / (n : ℝ)) ≤ C * J ^ (1 / (n : ℝ)) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hroot := Real.rpow_le_rpow hI h (one_div_nonneg.mpr hn0.le)
  rw [Real.mul_rpow (pow_nonneg hC _) hJ, ← Real.rpow_natCast C n,
    ← Real.rpow_mul hC, mul_one_div_cancel hn0.ne', Real.rpow_one] at hroot
  exact hroot

/-- Root an actual even-power integral comparison across arbitrary measure
spaces. No integrability assumption is needed for this algebraic step. -/
theorem even_moment_le_of_integral_le
    {Ω' : Type*} [MeasurableSpace Ω'] {ν : Measure Ω'}
    (f : Ω → ℝ) (g : Ω' → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (n : ℕ) (hn : 1 ≤ n) (heven : Even n)
    (h : (∫ ω, f ω ^ n ∂μ) ≤ C ^ n * ∫ η, g η ^ n ∂ν) :
    moment μ (n : ℝ) f ≤ C * moment ν (n : ℝ) g := by
  have hroot := nat_root_le _ _ C
    (integral_nonneg fun ω => heven.pow_nonneg (f ω))
    (integral_nonneg fun η => heven.pow_nonneg (g η)) hC n hn h
  simpa only [moment, Real.rpow_natCast, heven.pow_abs] using hroot

theorem even_moment_mono_of_integral_le
    {Ω' : Type*} [MeasurableSpace Ω'] {ν : Measure Ω'}
    (f : Ω → ℝ) (g : Ω' → ℝ) (n : ℕ) (hn : 1 ≤ n) (heven : Even n)
    (h : (∫ ω, f ω ^ n ∂μ) ≤ ∫ η, g η ^ n ∂ν) :
    moment μ (n : ℝ) f ≤ moment ν (n : ℝ) g := by
  simpa only [one_mul] using even_moment_le_of_integral_le f g 1 zero_le_one
    n hn heven (by simpa only [one_pow, one_mul] using h)

/-- The source's positive-order moment is the real `Lp` norm, with the same
actual integrals and no replacement of the law. -/
theorem eq_lpNorm (p : ℝ) (hp : 0 < p) (f : Ω → ℝ)
    (hf : AEStronglyMeasurable f μ) :
    moment μ p f = lpNorm f (ENNReal.ofReal p) μ := by
  symm
  simpa only [moment, ENNReal.toReal_ofReal hp.le, Real.norm_eq_abs, one_div] using
    lpNorm_eq_integral_norm_rpow_toReal (p := ENNReal.ofReal p)
      (by simp [hp]) ENNReal.ofReal_ne_top hf

theorem memLp_of_integrable_abs_rpow (p : ℝ) (hp : 0 < p) (f : Ω → ℝ)
    (hf : AEStronglyMeasurable f μ)
    (hint : Integrable (fun ω => |f ω| ^ p) μ) : MemLp f (ENNReal.ofReal p) μ := by
  apply (integrable_norm_rpow_iff hf (by simp [hp]) ENNReal.ofReal_ne_top).mp
  simpa only [ENNReal.toReal_ofReal hp.le, Real.norm_eq_abs] using hint

theorem integrable_abs_rpow_of_memLp (p : ℝ) (hp : 0 < p) (f : Ω → ℝ)
    (hf : MemLp f (ENNReal.ofReal p) μ) : Integrable (fun ω => |f ω| ^ p) μ := by
  simpa only [ENNReal.toReal_ofReal hp.le, Real.norm_eq_abs] using
    hf.integrable_norm_rpow (by simp [hp]) ENNReal.ofReal_ne_top

/-- An integrable even natural power gives the precise `MemLp` hypothesis
needed for its rooted moment. -/
theorem memLp_of_integrable_even_pow (f : Ω → ℝ)
    (hf : AEStronglyMeasurable f μ) (n : ℕ) (hn : n ≠ 0) (heven : Even n)
    (hint : Integrable (fun ω => f ω ^ n) μ) : MemLp f n μ := by
  apply (integrable_norm_rpow_iff hf (by exact_mod_cast hn) (by simp)).mp
  simpa only [ENNReal.toReal_natCast, Real.rpow_natCast, Real.norm_eq_abs,
    heven.pow_abs] using hint

theorem neg (p : ℝ) (f : Ω → ℝ) :
    moment μ p (fun ω => -f ω) = moment μ p f := by simp only [moment, abs_neg]

theorem abs (p : ℝ) (f : Ω → ℝ) :
    moment μ p (fun ω => |f ω|) = moment μ p f := by simp only [moment, abs_abs]

/-- Scaling in the actual rooted moment functional. -/
theorem const_mul (p : ℝ) (hp : 0 < p) (c : ℝ) (f : Ω → ℝ) :
    moment μ p (fun ω => c * f ω) = |c| * moment μ p f := by
  unfold moment
  simp_rw [abs_mul, Real.mul_rpow (abs_nonneg c) (abs_nonneg _)]
  rw [integral_const_mul, Real.mul_rpow (Real.rpow_nonneg (abs_nonneg c) _)
    (integral_nonneg fun _ => Real.rpow_nonneg (abs_nonneg _) _),
    ← Real.rpow_mul (abs_nonneg c), mul_one_div_cancel hp.ne', Real.rpow_one]

theorem mul_const (p : ℝ) (hp : 0 < p) (f : Ω → ℝ) (c : ℝ) :
    moment μ p (fun ω => f ω * c) = |c| * moment μ p f := by
  simpa only [mul_comm] using const_mul p hp c f

/-- Squaring the scalar input doubles the moment order and squares its root. -/
theorem square (p : ℝ) (hp : 0 < p) (f : Ω → ℝ) :
    moment μ p (fun ω => f ω ^ 2) = moment μ (2*p) f ^ 2 := by
  have hpoint (ω : Ω) : |f ω ^ 2| ^ p = |f ω| ^ (2*p) := by
    rw [abs_pow, ← Real.rpow_natCast |f ω| 2, ← Real.rpow_mul (abs_nonneg _)]
    norm_num
  have hA : 0 ≤ ∫ ω, |f ω| ^ (2*p) ∂μ :=
    integral_nonneg fun _ => Real.rpow_nonneg (abs_nonneg _) _
  unfold moment
  simp_rw [hpoint]
  rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hA]
  congr 1
  field_simp
  norm_num

/-- The corresponding finiteness bridge for the squared scalar input. -/
theorem memLp_square (p : ℝ) (hp : 0 < p) (f : Ω → ℝ)
    (hf : MemLp f (ENNReal.ofReal (2*p)) μ) :
    MemLp (fun ω => f ω ^ 2) (ENNReal.ofReal p) μ := by
  apply memLp_of_integrable_abs_rpow p hp _
    ((hf.aestronglyMeasurable.aemeasurable.pow_const 2).aestronglyMeasurable)
  have h := integrable_abs_rpow_of_memLp (2*p) (by positivity) f hf
  have hpoint (ω : Ω) : |f ω ^ 2| ^ p = |f ω| ^ (2*p) := by
    rw [abs_pow, ← Real.rpow_natCast |f ω| 2, ← Real.rpow_mul (abs_nonneg _)]
    norm_num
  simpa only [hpoint] using h

/-- Minkowski in the source's moment notation. Both finite `Lp` hypotheses
are explicit, so the real integral convention at infinity cannot hide a gap. -/
theorem add_le (p : ℝ) (hp : 1 ≤ p) (f g : Ω → ℝ)
    (hf : MemLp f (ENNReal.ofReal p) μ) (hg : MemLp g (ENNReal.ofReal p) μ) :
    moment μ p (fun ω => f ω + g ω) ≤ moment μ p f + moment μ p g := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  change moment μ p (f + g) ≤ moment μ p f + moment μ p g
  rw [eq_lpNorm p hp0 (f + g) (hf.aestronglyMeasurable.add hg.aestronglyMeasurable),
    eq_lpNorm p hp0 f hf.aestronglyMeasurable, eq_lpNorm p hp0 g hg.aestronglyMeasurable]
  exact lpNorm_add_le hf (by simpa using ENNReal.ofReal_le_ofReal hp)

theorem sub_le (p : ℝ) (hp : 1 ≤ p) (f g : Ω → ℝ)
    (hf : MemLp f (ENNReal.ofReal p) μ) (hg : MemLp g (ENNReal.ofReal p) μ) :
    moment μ p (fun ω => f ω - g ω) ≤ moment μ p f + moment μ p g := by
  simpa only [sub_eq_add_neg, neg] using add_le p hp f (fun ω => -g ω) hf hg.neg

theorem add_le_of_integrable (p : ℝ) (hp : 1 ≤ p) (f g : Ω → ℝ)
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hfi : Integrable (fun ω => |f ω| ^ p) μ)
    (hgi : Integrable (fun ω => |g ω| ^ p) μ) :
    moment μ p (fun ω => f ω + g ω) ≤ moment μ p f + moment μ p g :=
  add_le p hp f g
    (memLp_of_integrable_abs_rpow p (lt_of_lt_of_le zero_lt_one hp) f hf hfi)
    (memLp_of_integrable_abs_rpow p (lt_of_lt_of_le zero_lt_one hp) g hg hgi)

section Probability

variable [IsProbabilityMeasure μ]

theorem const (p : ℝ) (hp : 0 < p) (c : ℝ) :
    moment μ p (fun _ : Ω => c) = |c| := by
  unfold moment
  simp only [integral_const, probReal_univ, one_smul]
  rw [← Real.rpow_mul (abs_nonneg c), mul_one_div_cancel hp.ne', Real.rpow_one]

/-- Monotonicity in the positive moment order, with finiteness at the higher order. -/
theorem mono_exponent (p q : ℝ) (hp : 0 < p) (hpq : p ≤ q) (f : Ω → ℝ)
    (hq : MemLp f (ENNReal.ofReal q) μ) : moment μ p f ≤ moment μ q f := by
  have hq0 : 0 < q := hp.trans_le hpq
  rw [eq_lpNorm p hp f hq.aestronglyMeasurable,
    eq_lpNorm q hq0 f hq.aestronglyMeasurable,
    ← toReal_eLpNorm hq.aestronglyMeasurable, ← toReal_eLpNorm hq.aestronglyMeasurable]
  exact ENNReal.toReal_mono hq.eLpNorm_ne_top
    (eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal hpq) hq.aestronglyMeasurable)

theorem mono_exponent_of_integrable (p q : ℝ) (hp : 0 < p) (hpq : p ≤ q)
    (f : Ω → ℝ) (hf : AEStronglyMeasurable f μ)
    (hq : Integrable (fun ω => |f ω| ^ q) μ) : moment μ p f ≤ moment μ q f :=
  mono_exponent p q hp hpq f (memLp_of_integrable_abs_rpow q (hp.trans_le hpq) f hf hq)

/-- A variable is its mean plus its centered part. -/
theorem le_abs_mean_add_centered (p : ℝ) (hp : 1 ≤ p) (f : Ω → ℝ)
    (hf : MemLp f (ENNReal.ofReal p) μ) :
    moment μ p f ≤ |∫ ω, f ω ∂μ| + moment μ p (fun ω => f ω - ∫ η, f η ∂μ) := by
  have hc : MemLp (fun _ : Ω => ∫ ω, f ω ∂μ) (ENNReal.ofReal p) μ := memLp_const _
  have h := add_le p hp (fun _ : Ω => ∫ ω, f ω ∂μ)
    (fun ω => f ω - ∫ η, f η ∂μ) hc (hf.sub hc)
  simpa only [add_sub_cancel, const p (lt_of_lt_of_le zero_lt_one hp)] using h

theorem centered_le (p : ℝ) (hp : 1 ≤ p) (f : Ω → ℝ)
    (hf : MemLp f (ENNReal.ofReal p) μ) :
    moment μ p (fun ω => f ω - ∫ η, f η ∂μ) ≤ moment μ p f + |∫ ω, f ω ∂μ| := by
  have h := sub_le p hp f (fun _ : Ω => ∫ ω, f ω ∂μ) hf (memLp_const _)
  simpa only [const p (lt_of_lt_of_le zero_lt_one hp)] using h

/-- First step of the Hilbert norm assembly: the doubled-order moment
squared is bounded by its second moment plus the centered-square moment. -/
theorem two_order_square_le_mean_add_centered_square (p : ℝ) (hp : 1 ≤ p)
    (f : Ω → ℝ) (hf : MemLp f (ENNReal.ofReal (2*p)) μ) :
    moment μ (2*p) f ^ 2 ≤ (∫ ω, f ω ^ 2 ∂μ) +
      moment μ p (fun ω => f ω ^ 2 - ∫ η, f η ^ 2 ∂μ) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have h := le_abs_mean_add_centered p hp (fun ω => f ω ^ 2) (memLp_square p hp0 f hf)
  rwa [square p hp0 f, abs_of_nonneg (integral_nonneg fun _ => sq_nonneg _)] at h

end Probability

end MI32.MomentTools
