import GraphMatrices.SignGraphDegree

/-!
# Off-diagonal sign coordinates and event-level limited independence

The primitive coordinates in the graph model below are precisely the
unordered pairs of distinct ambient vertices. No diagonal random bits are
part of the sample space. Finite Boolean cylinder matching is proved equivalent
to observable marginal matching, and the actual graph moments transfer from
the event-level t-wise fair-bit hypothesis.
-/

open scoped BigOperators
open GraphMatrices.FiniteLocalMoments

namespace GraphMatrices.OffDiagonalModel

noncomputable section

section BooleanCylinders

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- A specified bit assignment on a finite set of named coordinates. -/
def bitCylinder (S : Finset E) (a : E → Bool) : Set (E → Bool) :=
  {x | ∀ i ∈ S, x i = a i}

/-- Event-level equality of coordinate marginals through order `k`. -/
def CylinderMatchesUpTo (μ ν : FiniteLaw (E → Bool)) (k : ℕ) : Prop :=
  ∀ S : Finset E, S.card ≤ k → ∀ a : E → Bool,
    μ.prob (bitCylinder S a) = ν.prob (bitCylinder S a)

/-- A partial bit assignment extended by fixed false bits off its domain. -/
def fillAssignment (S : Finset E) (a : S → Bool) : E → Bool :=
  fun i => if hi : i ∈ S then a ⟨i, hi⟩ else false

omit [Fintype E] in
theorem cylinder_iff_partial_eq (S : Finset E) (a : S → Bool) (x : E → Bool) :
    x ∈ bitCylinder S (fillAssignment S a) ↔ a = fun i : S => x i := by
  constructor
  · intro hx
    funext i
    have hi := hx i i.property
    simpa only [fillAssignment, dif_pos i.property] using hi.symm
  · intro ha
    subst a
    intro i hi
    simp only [fillAssignment, dif_pos hi]

omit [Fintype E] in
/-- Expansion of a local observable in point-cylinder indicators. -/
theorem local_observable_expansion (S : Finset E) (f : (E → Bool) → ℝ)
    (hf : DependsOn S f) (x : E → Bool) :
    f x = ∑ a : S → Bool, f (fillAssignment S a) *
      FiniteLaw.indicator (bitCylinder S (fillAssignment S a)) x := by
  have hind (a : S → Bool) :
      FiniteLaw.indicator (bitCylinder S (fillAssignment S a)) x =
        if a = (fun i : S => x i) then 1 else 0 := by
    simp only [FiniteLaw.indicator, cylinder_iff_partial_eq]
  simp_rw [hind, mul_ite, mul_one, mul_zero]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  apply hf x (fillAssignment S (fun i : S => x i))
  intro i hi
  simp only [fillAssignment, dif_pos hi]

theorem expect_local_observable_expansion (μ : FiniteLaw (E → Bool))
    (S : Finset E) (f : (E → Bool) → ℝ) (hf : DependsOn S f) :
    μ.expect f = ∑ a : S → Bool, f (fillAssignment S a) *
      μ.prob (bitCylinder S (fillAssignment S a)) := by
  calc
    μ.expect f = μ.expect (fun x => ∑ a : S → Bool, f (fillAssignment S a) *
        FiniteLaw.indicator (bitCylinder S (fillAssignment S a)) x) :=
      μ.expect_congr (local_observable_expansion S f hf)
    _ = ∑ a : S → Bool, μ.expect (fun x => f (fillAssignment S a) *
        FiniteLaw.indicator (bitCylinder S (fillAssignment S a)) x) := by
      simp only [FiniteLaw.expect, Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      rw [μ.expect_smul]
      rfl

/-- Event-cylinder matching and observable marginal matching are equivalent. -/
theorem cylinderMatchesUpTo_iff_matchesUpTo
    (μ ν : FiniteLaw (E → Bool)) (k : ℕ) :
    CylinderMatchesUpTo μ ν k ↔ MatchesUpTo μ ν k := by
  constructor
  · intro h S hS f hf
    rw [expect_local_observable_expansion μ S f hf,
      expect_local_observable_expansion ν S f hf]
    apply Finset.sum_congr rfl
    intro a _
    rw [h S hS (fillAssignment S a)]
  · intro h S hS a
    exact prob_cylinder_eq_of_matchesUpTo h S hS a

/-- The usual fair-bit t-wise independence hypothesis, stated by event masses. -/
def TWiseFair (μ : FiniteLaw (E → Bool)) (t : ℕ) : Prop :=
  ∀ S : Finset E, S.card ≤ t → ∀ a : E → Bool,
    μ.prob (bitCylinder S a) = (1 / 2 : ℝ) ^ S.card

theorem independentSignLaw_prob_bitCylinder (S : Finset E) (a : E → Bool) :
    (independentSignLaw (E := E)).prob (bitCylinder S a) = (1 / 2 : ℝ) ^ S.card := by
  classical
  let events : E → Set Bool := fun i => if i ∈ S then {a i} else Set.univ
  have hevent : bitCylinder S a = FiniteLaw.cylinder events := by
    ext x
    constructor
    · intro hx i
      by_cases hi : i ∈ S
      · simpa [events, hi] using hx i hi
      · simp [events, hi]
    · intro hx i hi
      simpa [events, hi] using hx i
  rw [hevent]
  change (FiniteLaw.independentProduct (fun _ : E => fairBitLaw)).prob
    (FiniteLaw.cylinder events) = _
  rw [FiniteLaw.prob_independentProduct_cylinder]
  have hprob (i : E) : fairBitLaw.prob (events i) = if i ∈ S then (1 / 2 : ℝ) else 1 := by
    by_cases hi : i ∈ S
    · simp [events, hi, FiniteLaw.prob_singleton, fairBitLaw]
    · simp only [events, if_neg hi, FiniteLaw.prob_univ]
  simp_rw [hprob]
  simp

/-- The standard event-level definition has exactly the required matching content. -/
theorem tWiseFair_iff_matchesUpTo (μ : FiniteLaw (E → Bool)) (t : ℕ) :
    TWiseFair μ t ↔ MatchesUpTo μ (independentSignLaw (E := E)) t := by
  rw [← cylinderMatchesUpTo_iff_matchesUpTo]
  constructor
  · intro h S hS a
    rw [h S hS a, independentSignLaw_prob_bitCylinder]
  · intro h S hS a
    rw [h S hS a, independentSignLaw_prob_bitCylinder]

theorem TWiseFair.mono {μ : FiniteLaw (E → Bool)} {k t : ℕ}
    (h : TWiseFair μ t) (hkt : k ≤ t) : TWiseFair μ k := by
  intro S hS a
  exact h S (hS.trans hkt) a

end BooleanCylinders

section OffDiagonalCoordinates

variable {n r s : ℕ}

/-- Exactly one coordinate for each unordered pair of distinct vertices. -/
abbrev EdgeCoordinate (n : ℕ) := {e : Sym2 (Fin n) // ¬ e.IsDiag}

/-- Fixed diagonal fillers let us reuse the previously verified graph definition. -/
def extendSigns (σ : EdgeCoordinate n → Bool) : Sym2 (Fin n) → Bool :=
  fun e => if he : e.IsDiag then false else σ ⟨e, he⟩

/-- Discard the unused diagonal coordinates of a full assignment. -/
def restrictSigns (η : Sym2 (Fin n) → Bool) : EdgeCoordinate n → Bool :=
  fun e => η e.val

@[simp] theorem extendSigns_nondiagonal (σ : EdgeCoordinate n → Bool)
    (e : EdgeCoordinate n) : extendSigns σ e.val = σ e := by
  simp [extendSigns, e.property]

@[simp] theorem restrict_extendSigns (σ : EdgeCoordinate n → Bool) :
    restrictSigns (extendSigns σ) = σ := by
  funext e
  exact extendSigns_nondiagonal σ e

def offDiagonalInput (σ : EdgeCoordinate n → Bool) : Matrix (Fin n) (Fin n) ℝ :=
  signInput (extendSigns σ)

theorem offDiagonalInput_isSignMatrix (σ : EdgeCoordinate n → Bool) :
    IsSignMatrix (offDiagonalInput σ) := signInput_isSignMatrix _

theorem offDiagonalInput_apply_ne (σ : EdgeCoordinate n → Bool)
    (i j : Fin n) (hij : i ≠ j) :
    offDiagonalInput σ i j =
      Walsh.sign (σ ⟨s(i, j), by simpa only [Sym2.mk_isDiag_iff] using hij⟩) := by
  simp [offDiagonalInput, signInput, extendSigns, hij, Sym2.mk_isDiag_iff]

/-- Arbitrary diagonal bits have no effect on the actual primitive matrix. -/
theorem offDiagonalInput_restrictSigns (η : Sym2 (Fin n) → Bool) :
    offDiagonalInput (restrictSigns η) = signInput η := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [offDiagonalInput, signInput]
  · simp [offDiagonalInput, signInput, extendSigns, restrictSigns,
      hij, Sym2.mk_isDiag_iff]

/-- Fixing unused coordinates does not increase local interaction degree. -/
theorem localDegree_extendSigns {k : ℕ} {f : (Sym2 (Fin n) → Bool) → ℝ}
    (hf : HasLocalDegree k f) :
    HasLocalDegree k (fun σ : EdgeCoordinate n → Bool => f (extendSigns σ)) := by
  classical
  induction hf with
  | atom S f hcard hdep =>
    apply HasLocalDegree.atom (S.subtype (fun e => ¬ e.IsDiag))
    · rw [Finset.card_subtype]
      exact (Finset.card_filter_le _ _).trans hcard
    · intro x y hxy
      apply hdep
      intro e he
      by_cases hed : e.IsDiag
      · simp only [extendSigns, dif_pos hed]
      · simp only [extendSigns, dif_neg hed]
        exact hxy ⟨e, hed⟩ (Finset.mem_subtype.mpr he)
  | zero => exact HasLocalDegree.zero
  | add hf hg ihf ihg => exact ihf.add ihg
  | smul c hf ih => exact HasLocalDegree.smul c ih

variable {α : Type*} [Fintype α] [DecidableEq α]

def offDiagonalGraphMatrix (G : SimpleGraph α)
    (left : Fin r ↪ α) (right : Fin s ↪ α) (σ : EdgeCoordinate n → Bool) :
    Matrix (Fin r → Fin n) (Fin s → Fin n) ℝ :=
  signGraphMatrix G left right (extendSigns σ)

/-- Restricting to off-diagonal coordinates preserves every graph-matrix entry. -/
theorem offDiagonalGraphMatrix_restrictSigns (G : SimpleGraph α)
    (left : Fin r ↪ α) (right : Fin s ↪ α) (η : Sym2 (Fin n) → Bool) :
    offDiagonalGraphMatrix G left right (restrictSigns η) = signGraphMatrix G left right η := by
  unfold offDiagonalGraphMatrix signGraphMatrix
  congr 1
  exact offDiagonalInput_restrictSigns η

theorem offDiagonalGraphMatrix_entry_localDegree (G : SimpleGraph α)
    (left : Fin r ↪ α) (right : Fin s ↪ α)
    (row : Fin r → Fin n) (col : Fin s → Fin n) :
    HasLocalDegree (shapeEdgeCount G)
      (fun σ : EdgeCoordinate n → Bool => offDiagonalGraphMatrix G left right σ row col) :=
  localDegree_extendSigns (signGraphMatrix_entry_localDegree G left right row col)

def offDiagonalGraphMoment (G : SimpleGraph α)
    (left : Fin r ↪ α) (right : Fin s ↪ α) (q : ℕ)
    (σ : EdgeCoordinate n → Bool) : ℝ :=
  let A := offDiagonalGraphMatrix G left right σ
  ((A * A.transpose) ^ q).trace

theorem offDiagonalGraphMoment_restrictSigns (G : SimpleGraph α)
    (left : Fin r ↪ α) (right : Fin s ↪ α) (q : ℕ) (η : Sym2 (Fin n) → Bool) :
    offDiagonalGraphMoment G left right q (restrictSigns η) =
      signGraphGramMoment G left right q η := by
  simp only [offDiagonalGraphMoment, signGraphGramMoment, offDiagonalGraphMatrix_restrictSigns]

/--
The actual injective graph-matrix Gram moment transfers from event-level
t-wise independence on off-diagonal primitive coordinates only.
-/
theorem offDiagonalGraph_moment_eq_independent (G : SimpleGraph α)
    (left : Fin r ↪ α) (right : Fin s ↪ α) (q : ℕ)
    {μ : FiniteLaw (EdgeCoordinate n → Bool)} {t : ℕ}
    (hμ : TWiseFair μ t) (hbudget : 2 * q * shapeEdgeCount G ≤ t) :
    μ.expect (offDiagonalGraphMoment G left right q) =
      (independentSignLaw (E := EdgeCoordinate n)).expect
        (offDiagonalGraphMoment G left right q) := by
  exact GraphMomentTransfer.expect_gramTracePower_eq
    (fun row col => offDiagonalGraphMatrix_entry_localDegree G left right row col)
    ((tWiseFair_iff_matchesUpTo μ _).mp (hμ.mono hbudget))

/-- The centered trace variance requires the event-level budget `4*q*e`. -/
theorem offDiagonalGraph_variance_eq_independent (G : SimpleGraph α)
    (left : Fin r ↪ α) (right : Fin s ↪ α) (q : ℕ)
    {μ : FiniteLaw (EdgeCoordinate n → Bool)} {t : ℕ}
    (hμ : TWiseFair μ t) (hbudget : 4 * q * shapeEdgeCount G ≤ t) :
    μ.expect (fun σ => (offDiagonalGraphMoment G left right q σ -
      μ.expect (offDiagonalGraphMoment G left right q)) ^ 2) =
    (independentSignLaw (E := EdgeCoordinate n)).expect (fun σ =>
      (offDiagonalGraphMoment G left right q σ -
      (independentSignLaw (E := EdgeCoordinate n)).expect
        (offDiagonalGraphMoment G left right q)) ^ 2) := by
  exact GraphMomentTransfer.variance_gramTracePower_eq
    (fun row col => offDiagonalGraphMatrix_entry_localDegree G left right row col)
    ((tWiseFair_iff_matchesUpTo μ _).mp (hμ.mono hbudget))

end OffDiagonalCoordinates

end

end GraphMatrices.OffDiagonalModel
