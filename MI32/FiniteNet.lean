import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Tactic

/-! Finite Euclidean-net costs used in the thin-row estimate.
The net is constructed, and its exponential-in-input-dimension cardinality
is proved by a volume packing bound. No net or cardinality certificate is assumed. -/

noncomputable section
open scoped BigOperators

namespace MI32

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem separated_half_card_le (s : Finset E)
    (hs : ∀ x ∈ s, ‖x‖ ≤ 1)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → (1 : ℝ) / 2 ≤ ‖x - y‖) :
    s.card ≤ 5 ^ Module.finrank ℝ E := by
  classical
  let g : E → E := fun x => (2 : ℝ) • x
  have hg : Function.Injective g := smul_right_injective E (by norm_num : (2 : ℝ) ≠ 0)
  have h := Besicovitch.card_le_of_separated (s.image g) ?_ ?_
  · simpa only [Finset.card_image_of_injective _ hg] using h
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    simpa only [g, norm_smul, Real.norm_ofNat, mul_one] using mul_le_mul_of_nonneg_left (hs a ha) (by norm_num : (0 : ℝ) ≤ 2)
  · intro x hx y hy hxy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    have hab : a ≠ b := fun h => hxy (congrArg g h)
    have hd := hsep a ha b hb hab
    dsimp [g]
    rw [← smul_sub, norm_smul]
    norm_num
    linarith

/-- A half-net of the closed unit ball, with at most `5^dim` points in that ball.
This also handles the zero-dimensional domain. -/
theorem exists_half_net (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] :
    ∃ N : Finset E, N.Nonempty ∧ N.card ≤ 5 ^ Module.finrank ℝ E ∧
      (∀ y ∈ N, ‖y‖ ≤ 1) ∧
      (∀ x : E, ‖x‖ ≤ 1 → ∃ y ∈ N, ‖x - y‖ < (1 : ℝ) / 2) := by
  classical
  let P : ℕ → Prop := fun k => ∃ s : Finset E, s.card = k ∧
    (∀ x ∈ s, ‖x‖ ≤ 1) ∧
    (∀ x ∈ s, ∀ y ∈ s, x ≠ y → (1 : ℝ) / 2 ≤ ‖x - y‖)
  have hzero : P 0 := ⟨∅, by simp⟩
  obtain ⟨N, hcard, hnorm, hsep⟩ :=
    Nat.findGreatest_spec (P := P) (Nat.zero_le (5 ^ Module.finrank ℝ E)) hzero
  have hcover (x : E) (hx : ‖x‖ ≤ 1) :
      ∃ y ∈ N, ‖x - y‖ < (1 : ℝ) / 2 := by
    by_contra h
    push Not at h
    have hxN : x ∉ N := by
      intro hmem
      have hh := h x hmem
      simp only [sub_self, norm_zero] at hh
      norm_num at hh
    have hnorm' : ∀ y ∈ insert x N, ‖y‖ ≤ 1 := by
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact hx
      · exact hnorm y hy
    have hsep' : ∀ a ∈ insert x N, ∀ b ∈ insert x N, a ≠ b →
        (1 : ℝ) / 2 ≤ ‖a - b‖ := by
      intro a ha b hb hab
      by_cases hax : a = x
      · subst a
        have hbN : b ∈ N := (Finset.mem_insert.mp hb).resolve_left (Ne.symm hab)
        exact h b hbN
      · have haN : a ∈ N := (Finset.mem_insert.mp ha).resolve_left hax
        by_cases hbx : b = x
        · subst b
          simpa only [norm_sub_rev] using h a haN
        · exact hsep a haN b ((Finset.mem_insert.mp hb).resolve_left hbx) hab
    have hi := Nat.le_findGreatest
      (separated_half_card_le (insert x N) hnorm' hsep')
      (show P (insert x N).card from ⟨insert x N, rfl, hnorm', hsep'⟩)
    rw [Finset.card_insert_of_notMem hxN, hcard] at hi
    omega
  have hne : N.Nonempty := by
    obtain ⟨y, hy, _⟩ := hcover 0 (by simp)
    exact ⟨y, hy⟩
  exact ⟨N, hne, separated_half_card_le N hnorm hsep, hnorm, hcover⟩

omit [FiniteDimensional ℝ E] in
/-- A bound on a half-net controls the actual continuous-linear-map norm. -/
theorem opNorm_le_two_of_half_net (N : Finset E)
    (hcover : ∀ x : E, ‖x‖ = 1 → ∃ y ∈ N, ‖x - y‖ ≤ (1 : ℝ) / 2)
    (T : E →L[ℝ] F) (B : ℝ) (hB : 0 ≤ B)
    (hnet : ∀ y ∈ N, ‖T y‖ ≤ B) : ‖T‖ ≤ 2 * B := by
  have hnorm : ‖T‖ ≤ ‖T‖ / 2 + B := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hcover x hx
    calc
      ‖T x‖ = ‖T (x - y) + T y‖ := by rw [← map_add]; congr 2; abel
      _ ≤ ‖T (x - y)‖ + ‖T y‖ := norm_add_le _ _
      _ ≤ ‖T‖ * ‖x - y‖ + B := add_le_add (T.le_opNorm _) (hnet y hy)
      _ ≤ ‖T‖ / 2 + B := by nlinarith [norm_nonneg T]
  linarith

omit [FiniteDimensional ℝ E] in
/-- The net power-sum estimate used before taking expectations. -/
theorem opNorm_pow_le_net_sum (N : Finset E) (hN : N.Nonempty)
    (hcover : ∀ x : E, ‖x‖ = 1 → ∃ y ∈ N, ‖x - y‖ ≤ (1 : ℝ) / 2)
    (T : E →L[ℝ] F) (p : ℕ) :
    ‖T‖ ^ p ≤ (2 : ℝ) ^ p * ∑ y ∈ N, ‖T y‖ ^ p := by
  classical
  obtain ⟨y, hy, hmax⟩ := N.exists_max_image (fun y => ‖T y‖) hN
  have hT := opNorm_le_two_of_half_net N hcover T ‖T y‖ (norm_nonneg _) hmax
  calc
    ‖T‖ ^ p ≤ (2 * ‖T y‖) ^ p := pow_le_pow_left₀ (norm_nonneg T) hT p
    _ = (2 : ℝ) ^ p * ‖T y‖ ^ p := mul_pow _ _ _
    _ ≤ (2 : ℝ) ^ p * ∑ y ∈ N, ‖T y‖ ^ p :=
      mul_le_mul_of_nonneg_left
        (Finset.single_le_sum (fun z _ => pow_nonneg (norm_nonneg _) _) hy) (by positivity)

end MI32
