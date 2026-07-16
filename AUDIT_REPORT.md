# Audit report

## Verdict

No important flaw was found in the revised formalization.

The Lean development formalizes the paper's self-contained contribution:

> A finite loopless cubic edge-indexed multigraph carrying a nowhere-zero
> \(\mathbb F_2^3\)-flow has a cycle double cover.

The final all-graphs theorem is explicitly conditional on two named theorem interfaces imported
by the paper:

1. existence of a nowhere-zero \(\mathbb F_2^3\)-flow under `EveryEdgeInCycle`;
2. reduction from the general case to loopless cubic multigraphs.

Neither external theorem is represented by a project axiom. They are ordinary parameters of the
conditional assembly theorem. The project does not misleadingly declare an unconditional theorem
named `cycleDoubleCoverConjecture`.

## What was checked

### Statement fidelity

* Parallel edges have distinct edge identities.
* A loop counts twice in degree.
* The core theorem assumes looplessness and cubicity.
* `IsCycle` requires a nonempty, connected edge set with degree zero or two at each vertex.
* A cycle double cover is a finite indexed family of such cycles, with every edge counted exactly
  twice; repeated cycles are allowed.
* The project uses the honest name `EveryEdgeInCycle` and does not claim to have formalized its
  equivalence with a separate cut-edge definition.
* The two principal theorem interfaces and the conditional global theorem are universe-polymorphic.

### Proof architecture

The development contains formal versions of:

* decomposition of every loopless degree-0-or-2 edge set into connected cycles;
* Lemma 2.1, converting locally even two-element pair labels into a cycle double cover;
* the local triangle identity for the three pair sets;
* the finite-dimensional annihilator/range criterion;
* coordinate decomposition of dual functionals on `E -> Gamma`;
* the edge and vertex dual constraints in equation (5);
* the local dual-parity argument corresponding to equations (7)--(9);
* Lemma 2.2, solvability of the gluing system;
* endpoint independence of the pair labels;
* the self-contained core theorem.

The formerly brute-force proofs of `pairSet_card`, `pairSet_eq_iff`, and
`local_evenness_count` are now structural. Uses of `decide` remaining in the project are confined
to small finite bookkeeping, concrete regression examples, or simplification support; there is no
`native_decide`.

### Independent finite checks

`audit/finite_algebra_check.py` independently exhausts the finite algebra at the proof's crux:

* all 512 triples for the pair-set equality criterion and nonzero-cardinality claim;
* all 2,688 admissible local-evenness cases;
* all 336 admissible cases of the local dual-parity identity.

These checks are supplementary; the Lean kernel proof is the authoritative proof artifact.

### Source audit

The curated source contains no occurrence of:

* `sorry`;
* `admit`;
* a project `axiom` declaration;
* `native_decide`;
* `@[implemented_by]`;
* unsafe proof-producing declarations;
* `exact?` placeholders.

`RequestProject/Audit.lean` checks the two principal declarations and invokes `#print axioms` on
each. The Aristotle build report states that both depend only on `propext`, `Classical.choice`, and
`Quot.sound`, not on a project-defined postulate.

## Build-verification status

The supplied Aristotle report records a clean build with Lean `v4.28.0` and Mathlib `v4.28.0`
(commit `8f9d9cff6bd728b17a24e163c9402775d9e6a365`). The original audit environment did not contain Lean
and had no network access with which to install the pinned toolchain, so that build was not independently
rerun there.

This GitHub repository contains an automated workflow which verifies the canonical source archive,
extracts it, runs the independent audits, and invokes the pinned Lean build.

## Curatorial changes relative to Aristotle's raw archive

The Lean proof source is unchanged except for one comment-only correction in `Duality.lean`:
the cubic-vertex identity `x + y + z = 0` is described as unnumbered, consistently with the paper
and `DEPENDENCY_MAP.md`.

The raw `ARISTOTLE_SUMMARY.md` was not copied into the curated Lean project because it concatenated
two runs and its older section contained obsolete declaration names and an obsolete Petersen-test
claim. The exact original archive is retained inside the canonical source archive under `provenance/`.

## Scope limitation

This is a genuine formalization of the paper's new reduction and linear-algebra argument, conditional
on the two cited external graph-theoretic results. It is not a formalization of those two external
results, nor of the equivalence between `EveryEdgeInCycle` and a separately defined no-bridge
predicate. The README and theorem names state these limitations explicitly.
