# State of the MI-32 formalization

Read `README.md`, `docs/PROOF_OBLIGATIONS.md`, `docs/REMAINING_CHAIN_SPEC.md`
and `verification/status.json`. The original research checkpoint is unchanged.
Do not reread the whole research archive.

## What is done

`MI32.main_upper` is **proved**. `Solution.lean` has no `sorry`, and
`lake env lean FullTargetAudit.lean` reports

```text
'MI32.main_upper' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`python scripts/verify.py` exits `0` with `status = local_proof_gate_passed`.
The target statement in `MI32/Statement.lean` and `Challenge.lean` was never
edited; all eight of its definitions elaborate to identical terms in the
Challenge and Solution environments.

The chain added to close the gap, in dependency order:

`DeletionScheduleArithmetic`, `BlockOrderArithmetic`, `GradedVarianceEnergy`,
`NestedShells`, `WeakDeletionMonotonicity`, `NestedDeletionSelection`,
`NestedDeletionFamily`, `MaskedEntryLaw`, `FiberBlockNorm`, `FrobeniusMean`,
`CenteredGramNorm`, `GramEntryMoments`, `FarRemainderMoment`,
`BilinearHighOrder`, `RestrictedBlockFamily`, `BlockMaskMoment`,
`NearBlockMoment`, `DeletionMasks`, `NearMaskMean`, `FarMaskMean`,
`SymmetricDeletion`.

`MI32/RegularWitness.lean` is a separate statement check, not part of the
proof: it exhibits an independent fair-sign matrix satisfying `RegularEntries`
at `α = 1` with `varianceScale = sqrt n > 0`, so the universally quantified
hypothesis class is neither empty nor degenerate.

`docs/REMAINING_CHAIN_SPEC.md` documents each of these as a numbered section
and records the two deliberate divergences from the informal draft: the far
remainder avoids the Latała-van Handel-Youssef variance-envelope input by
raising the screening threshold from `b^2` to `b^3` and using an elementary
centered-Gram estimate, and the whole decomposition runs on the original
rectangular matrix rather than the matrix-symmetric dilation, so no reflected
entry repeats a variable and the paired dilation budget is not needed.

## What is NOT done, and must not be claimed

- **Comparator and NanoDa have not been run locally.** They require `landrun`
  and `systemd-run`; neither exists on this Windows host. A local checkout of
  the Comparator source is on the machine but is unbuilt and unusable here.
  Mechanical verification of a submission is Palomar's own step.
- A Palomar submission has been made and its AI editorial review returned
  requested changes (classification, provenance, Challenge documentation),
  addressed in this revision. Registration has not been requested and the
  project is not registered.
- No human peer review of the mathematics. Agent review is not peer review.
- No novelty, priority, lower-bound or quantile claim. The lower comparison is
  a credited existing theorem and is not formalized or selected here.
- Constants are explicit but conservative; nothing is optimized.

## Build environment caveat

`.lake/packages/*` are directory junctions to a commit-identical checkout
elsewhere on this machine. They were found missing (empty directories) at the
start of the completing session, which made `lake build` fail with a `git`
error while a previous `verification/status.json` still recorded a passing
core. If the junctions are missing again, recreate them or run
`lake exe cache get` on a fresh clone; do not trust a stale status file.
`MI32/CenteredGramNorm.lean` also did not compile at that point and was
repaired (two Lean-technical errors, no mathematical change).

## If you extend this

`lake build` builds the proof core; `lake build Challenge Solution` elaborates
both target environments. Keep `Challenge.lean` byte-compatible with the
prefix of `MI32/Statement.lean` — `scripts/verify.py` enforces it. Never add a
desired estimate as an input hypothesis or a custom axiom, and never let the
core import `Challenge` or `Solution`.
