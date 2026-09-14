import MI32.CreationSectorContraction
import MI32.AnnihilationSectorContraction
import MI32.RawCountBlocks

/-!
# Exact raw actions behind the sector estimates

The projected-multiplication creator is exactly the raw creator on its
matching input sector. The direct raw annihilator vanishes outside the
active original columns, and its restriction is exactly the projected
annihilation action. These are pointwise polynomial identities for signed
coefficients, with every original variable and updated exponent retained.
-/

noncomputable section
open scoped BigOperators

namespace MI32.RawSectorNorms

open PositivePolynomial PolynomialSectorMasks ActiveCountSectors ParityGeometry
open RawParity RawDirectionalActions RawCountBlocks PositiveWordExtension
open SymmetricPositiveCone

variable {Ω R C K : Type*} [Fintype R] [Fintype C] [Fintype K]
    [DecidableEq R] [DecidableEq C]

/-- The creator controlled by the analytic sector estimate is literally the
original raw creator, with arbitrary signed coefficients. -/
theorem creation_sectorAction_eq (X : R → C → Ω → ℝ) (k : ℕ) (δ : R → ℕ)
    (c : R → K → ℝ) (ν : R → K → R × C → ℕ) (ω : Ω) :
    CreationSectorContraction.sectorAction X k δ c ν ω =
      evaluateHilbert (creationCoeff (maskCoeff (creationMask k δ) c ν) ν)
        (actionExponent ν) (fun e => X e.1 e.2 ω) := by
  change evaluateHilbert
      (maskCoeff (creationOutputMask k δ)
        (extendCoeff (fun _ _ => 1) (maskCoeff (creationMask k δ) c ν)) (actionExponent ν))
      (actionExponent ν) (fun e => X e.1 e.2 ω) = _
  rw [creation_full_block]

omit [Fintype K] in
/-- An occupied original edge must end at an active column of its original
input count label. Thus every raw annihilation coefficient outside that set is zero. -/
theorem annihilationCoeff_eq_zero_outside_support (k : ℕ) (δ : C → ℕ)
    (c : R → K → ℝ) (ν : R → K → R × C → ℕ)
    (j : C) (hj : j ∉ support δ) (t : R × K) :
    annihilationCoeff (maskCoeff (annihilationMask k δ) c ν) ν j t = 0 := by
  by_cases he : (t.1, j) ∈ parity (ν t.1 t.2)
  · have hn : ¬ annihilationMask k δ t.1 (parity (ν t.1 t.2)) := by
      intro hm
      apply hj
      rw [← hm.2, support_colCount]
      exact edge_col_mem_activeCols he
    simp [annihilationCoeff, he, maskCoeff, hn]
  · simp [annihilationCoeff, he]

/-- Each selected output coordinate of the projected multiplication equals
the full raw annihilator coordinate; only its Euclidean output index is restricted. -/
theorem annihilation_sectorAction_eq_restrict (X : R → C → Ω → ℝ)
    (k : ℕ) (δ : C → ℕ) (c : R → K → ℝ) (ν : R → K → R × C → ℕ) (ω : Ω) :
    AnnihilationSectorContraction.sectorAction X k δ c ν ω =
      evaluateHilbert
        (fun j : support δ => annihilationCoeff (maskCoeff (annihilationMask k δ) c ν) ν j)
        (fun j : support δ => actionExponent ν j) (fun e => X e.1 e.2 ω) := by
  change evaluateHilbert
      (fun j : support δ => maskCoeff (annihilationOutputMask k δ)
        (extendCoeff (fun _ _ => 1) (maskCoeff (annihilationMask k δ) c ν))
        (actionExponent ν) (j : C))
      (fun j : support δ => actionExponent ν j) (fun e => X e.1 e.2 ω) = _
  rw [annihilation_full_block]

/-- The full raw annihilator is recovered by canonical zero extension of the
selected-output sector action, pointwise in the original random variables. -/
theorem zeroExtend_annihilation_sectorAction (X : R → C → Ω → ℝ)
    (k : ℕ) (δ : C → ℕ) (c : R → K → ℝ) (ν : R → K → R × C → ℕ) (ω : Ω) :
    AxisRestriction.zeroExtend (support δ)
        (AnnihilationSectorContraction.sectorAction X k δ c ν ω) =
      evaluateHilbert (annihilationCoeff (maskCoeff (annihilationMask k δ) c ν) ν)
        (actionExponent ν) (fun e => X e.1 e.2 ω) := by
  rw [annihilation_sectorAction_eq_restrict]
  exact SupportedPolynomialInteraction.zeroExtend_evaluateHilbert
    (annihilationCoeff (maskCoeff (annihilationMask k δ) c ν) ν) (actionExponent ν)
    (support δ) (annihilationCoeff_eq_zero_outside_support k δ c ν) _

/-- No norm loss or variable deletion occurs when transferring the selected-output
annihilation estimate to the full original raw annihilator. -/
theorem norm_raw_annihilation_eq_sectorAction (X : R → C → Ω → ℝ)
    (k : ℕ) (δ : C → ℕ) (c : R → K → ℝ) (ν : R → K → R × C → ℕ) (ω : Ω) :
    ‖evaluateHilbert (annihilationCoeff (maskCoeff (annihilationMask k δ) c ν) ν)
        (actionExponent ν) (fun e => X e.1 e.2 ω)‖ =
      ‖AnnihilationSectorContraction.sectorAction X k δ c ν ω‖ := by
  rw [annihilation_sectorAction_eq_restrict]
  exact (SupportedPolynomialInteraction.norm_evaluateHilbert_restrict
    (annihilationCoeff (maskCoeff (annihilationMask k δ) c ν) ν) (actionExponent ν)
    (support δ) (annihilationCoeff_eq_zero_outside_support k δ c ν) _).symm

end MI32.RawSectorNorms
