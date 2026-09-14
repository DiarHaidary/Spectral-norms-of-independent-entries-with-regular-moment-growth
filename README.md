# MI-32 Lean development

This folder formalizes the MI-32 proof draft in the sibling
`mi32_cycles_2026-09-13` research checkpoint. The original target is now
proved: `MI32.main_upper` in [`Solution.lean`](Solution.lean) contains no
`sorry`, and its transitive axiom audit reports exactly `propext`,
`Classical.choice` and `Quot.sound`.

**It is not registered with Palomar.** A submission has been made; its AI
editorial review returned requested changes on classification and provenance
metadata and on the Challenge documentation, which this revision addresses.
Comparator and NanoDa cannot run on this Windows host (they need `landrun` and
`systemd-run`), so the mechanical checks recorded here are local Lean evidence
only and mechanical verification of the submission is Palomar's own step.
Registration has not been requested, no human peer review of the mathematics
has taken place, and no novelty or priority claim is made.

## The statement that is proved

The target is unchanged from [`MI32/Statement.lean`](MI32/Statement.lean) and
[`Challenge.lean`](Challenge.lean): arbitrary probability spaces, independent
mean-zero real entries, every real moment order in the regularity assumption,
the Euclidean operator norm, one deterministic deletion set for both axes, and
the actual subunit moment at `log 2`.

```lean
theorem MI32.main_upper (α : ℝ) (hα : 1 ≤ α) :
    ∃ C : ℝ, 0 < C ∧ UpperBoundAt α C
```

with

```lean
def UpperBoundAt (α C : ℝ) : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (Ω : Type u) (mΩ : MeasurableSpace Ω)
    (μ : @Measure Ω mΩ), @IsProbabilityMeasure Ω mΩ μ →
    ∀ (X : Ω → Matrix (Fin n) (Fin n) ℝ),
      @RegularEntries Ω mΩ n μ α X →
      (∫ ω, spectralNorm (X ω) ∂μ) ≤ C * (varianceScale μ X + deletionScale μ X)
```

No finite-law substitute, conditional comparison, or assumed contraction is
used anywhere, and no estimate is taken as an input hypothesis or a custom
axiom.

The hypothesis class is not empty or degenerate:
[`RegularWitness.lean`](MI32/RegularWitness.lean) exhibits an independent
fair-sign matrix on a product of fair coins that satisfies `RegularEntries` at
the extreme parameter `α = 1` and has `varianceScale = sqrt n > 0`. That module
is a statement check and is not used by the proof.

## Shape of the proof

1. **Scalar and Boolean inputs.** Moment doubling, positive-coefficient
   polynomial comparison, dimension-free Hilbert Boolean fourth moments, and
   a direct independent-coordinate Hilbert comparison
   ([`HilbertComparison.lean`](MI32/HilbertComparison.lean)) that replaces the
   draft's use of the published strong/weak theorem.
2. **Parity geometry and the positive cone.** Exact creation/annihilation
   count sectors, grade compressions, the positive energy polynomial, and
   interpolation to the Hölder exponent.
3. **The local symmetric-law theorem.**
   `LocalSymmetricMoment.operator_moment_le` bounds every even operator moment
   of a symmetric regular matrix by the variance scale plus its undeleted weak
   moment, with a dimension factor that is absolute at logarithmic orders;
   `LocalLogMoment.mean_spectralNorm_le_literal` states it at exactly
   `log (n+1)`.
4. **The deletion decomposition.** A nested deterministic family
   `NestedDeletionFamily.sets` at the explicit schedule
   `budget k = 2^(5^k) - 1` screens both orientations with threshold
   `budget k ^ 3` and absorbs a weak-moment minimizer at each stage. The shell
   labels split the matrix into five deterministic masks
   ([`DeletionMasks.lean`](MI32/DeletionMasks.lean)): one initial block, two
   two-shell block families, and two far orientations.
   * the initial block has dimension at most `31`, so
     [`FrobeniusMean.lean`](MI32/FrobeniusMean.lean) bounds it by
     `sqrt 31 * varianceScale`;
   * the far orientations are bounded by an elementary centered-Gram second
     moment ([`FarRemainderMoment.lean`](MI32/FarRemainderMoment.lean)),
     giving `varianceScale * sqrt (1 + sqrt 2 * α^2)` each;
   * each two-shell block is a fiber block outside an earlier selected set, so
     ten scalar doublings raise the recorded logarithmic order to the scheduled
     one and the local theorem applies
     ([`NearBlockMoment.lean`](MI32/NearBlockMoment.lean)); the growing orders
     make the block maximum cost a factor three, not the number of blocks.
5. **Symmetrization.** `SymmetrizationReduction.upperBoundAt_of_symmetric`
   passes from the symmetric-law bound to the general law through an
   independent copy, at the cost of `exp 1` and parameter `2 α`.

The explicit constant is `SymmetricDeletion.deletionConstant (2 * α) * exp 1`.
It is conservative and not optimized.

## Read first

- [The remaining-chain specification, as implemented](docs/REMAINING_CHAIN_SPEC.md)
- [Checked work and the proof ledger](docs/PROOF_OBLIGATIONS.md)
- [Correspondence with the source problem, including two deliberate divergences](docs/SOURCE_FIDELITY.md)
- [Provenance and reused Lean code](docs/PROVENANCE.md)
- [Original informal proof draft](docs/source/MI32_solution.md)
- [Verification record](verification/status.json)

## Build

Lean: `leanprover/lean4:v4.33.0`. Mathlib is pinned by an exact public Git
commit in both Lakefile and manifest.

```text
lake exe cache get
lake build
lake env lean Audit.lean
lake build Challenge Solution
lake env lean FullTargetAudit.lean
```

`FullTargetAudit.lean` prints the transitive axioms of the selected target and
must report only the three standard foundations. `scripts/verify.py` records
every status and exits `0` only when the local proof gate passes; it does not
contact or submit to Palomar. `scripts/validate_metadata.py` runs the pinned
public metadata contract against a local checkout of
`PalomarRegistry/PalomarSubmission` at commit `ef2fa1ea`.

The local `.lake/packages` directories are cache junctions to an existing
commit-identical checkout on this machine. They are excluded from source
packaging; the submitted dependency declarations use public Git URLs and exact
commits, with no local-path dependencies. If those junctions are missing,
`lake build` fails with a `git` error rather than silently skipping work —
recreate them, or run `lake exe cache get` against a fresh clone.

## Palomar layout

The Challenge imports Mathlib only; Solution uses the project modules. They
define the same qualified target in separate environments; all eight target
definitions elaborate to identical terms in both, and the two `main_upper`
types print identically. That is a local check, not a Comparator run. The
Challenge carries the intentional hole by design, and its theorem
documentation says so and distinguishes it from the completed Solution.
The manifest, exact toolchain, Comparator configuration, licence, metadata,
and source-fidelity account are included for eventual submission.

The original checkpoint and all supplied reference projects are unchanged.
