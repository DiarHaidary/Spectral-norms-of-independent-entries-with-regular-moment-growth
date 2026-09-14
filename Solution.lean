import MI32

/-!
# The full MI-32 solution

This file selects the original general-law upper bound as the Comparator
target. Its proof is the chain assembled in the project modules: the parity
and positive-polynomial local moment theorem, the exact logarithmic local
order, the nested deterministic deletion decomposition with its far
centered-Gram remainder and near two-shell block families, and the
original-copy symmetrization reduction.

The Challenge module is never imported into the Solution environment.
-/

namespace MI32
universe u

/-- Full original target: for every regularity parameter at least one there is
a dimension- and law-uniform constant bounding the mean Euclidean operator
norm by the variance scale plus the shared-index deletion scale. -/
theorem main_upper (α : ℝ) (hα : 1 ≤ α) :
    ∃ C : ℝ, 0 < C ∧ UpperBoundAt.{u} α C :=
  SymmetricDeletion.exists_upperBoundAt α hα

end MI32
