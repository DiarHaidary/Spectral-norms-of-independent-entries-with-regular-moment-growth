# Provenance

The human requester and project owner is Diar Heidary. The Lean code,
packaging and checks were produced with substantial agent assistance on
14 September 2026: the local moment theorem, the scalar and parity machinery
and the packaging in earlier OpenAI Codex sessions, and the remaining
deletion chain (the modules listed in `CONTINUE_HERE.md`) in a later
Anthropic Claude Code session driven by Claude Opus 5, which specified the
chain in `docs/REMAINING_CHAIN_SPEC.md` and implemented it with parallel
subagents. Every completed declaration was rechecked by the local Lean 4.33.0
kernel, module by module and then by a full `lake build` plus the transitive
axiom audit. Human ownership and direction do not mean manual authorship or
independent human verification of every proof.

That later session also repaired the build environment, which was broken on
arrival: the `.lake/packages` cache junctions were missing, so `lake build`
failed with a `git` error while an earlier `verification/status.json` still
recorded a passing core, and `MI32/CenteredGramNorm.lean` did not compile. The
junctions were recreated against a commit-identical local checkout and the two
Lean-technical errors in that module were fixed; no statement was changed.

The informal mathematical source is the sibling research checkpoint
`mi32_cycles_2026-09-13`. Bundled copies are under `docs/source`; the
originals were not edited. They describe an agent-reviewed proof draft,
not an existing Lean certification. The new package records its own
more limited formal coverage.

The supplied projects examined for reuse were:

- `F:/Sandbox/SRHT Project/Palomar`
- `F:/Sandbox/Graph Matrices/Palomar`
- `F:/Project/nelson-nguyen-sparse-fock-extension-publish/formal`

Only the necessary source closure of `GraphMatrices.WalshFourthMoment`
was copied into `vendor/graph-matrices`, from the public commit
`DiarHaidary/Sharp-Bounds-for-Graph-Matrices@01994362f8543743d556e7544d2538e93c62c02b`,
which `vendor/graph-matrices/manifest.json` now records alongside the per-file
hashes. That project is a prior formalization reused as a Lean dependency, not
a mathematical source, and it is recorded in `related_formalizations` rather
than `sources`. Its modules retain their
original bytes, namespaces and MIT licence. `vendor/graph-matrices/manifest.json`
records exact SHA-256 hashes. That source includes generic material
previously ported from the SparseFock formalization; its original notices
are retained. The source closure is broader than the scalar inequality
because of the existing module import structure. No graph-matrix
application is claimed as a newly proved result here.

The existing projects' finite-law probability and Walsh machinery does
not imply that their arbitrary-measure analogues, strong–weak comparison,
or MI-32 are already proved. In particular the old
`IndependentFrameMeasure.lean` scaffold is not used as an analytic theorem.

The ordinary Challenge/Solution layout and manifest pinning follow the
supplied Palomar projects and the public Palomar policy. The current
policy was read online; local metadata validation, when recorded, uses
the separately identified pinned PalomarSubmission tool. Neither a
policy-conforming folder nor an ordinary Lean build is a registry result.
