# Cycle Double Cover formalization

[![Verify formalization](https://github.com/JoseBrox/cycle-double-cover-formalization/actions/workflows/lean.yml/badge.svg)](https://github.com/JoseBrox/cycle-double-cover-formalization/actions/workflows/lean.yml)

This repository contains a Lean 4 formalization of the self-contained argument in
*A Proof of the Cycle Double Cover Conjecture*. Aristotle produced the Lean development;
ChatGPT was used to prepare the source material, direct the formalization, and perform the
critical audit recorded in [`AUDIT_REPORT.md`](AUDIT_REPORT.md).

## Result and exact scope

The fully proved core theorem is

```lean
CycleDoubleCover.OrientedMultiGraph.cycleDoubleCover_of_nowhereZero_gammaFlow
```

It states that a finite loopless cubic edge-indexed multigraph carrying a nowhere-zero flow in

```text
Gamma = (ZMod 2)^3
```

has a cycle double cover.

The all-graphs assembly theorem is deliberately conditional:

```lean
CycleDoubleCover.OrientedMultiGraph.cycleDoubleCoverConjecture_of_gammaFlow_of_cubicReduction
```

It takes two classical results cited by the paper as explicit parameters:

1. the Kilpatrick--Jaeger theorem giving a nowhere-zero `Gamma`-flow;
2. Jaeger's reduction to loopless cubic multigraphs.

Those two external results are not formalized here and are not introduced as project axioms.
The development also uses the explicit hypothesis `EveryEdgeInCycle`; it does not claim to have
formalized its equivalence with a separately defined cut-edge notion of bridgelessness.

## How the proof is organized

The formalization follows the paper's argument rather than replacing it with a finite search.

1. [`Cycles.lean`](RequestProject/Cycles.lean) defines genuine connected cycles and cycle double
   covers for finite edge-indexed multigraphs.
2. [`CycleDecomposition.lean`](RequestProject/CycleDecomposition.lean) proves that a loopless
   degree-`0`-or-`2` edge set splits into connected cycles.
3. [`PairLabels.lean`](RequestProject/PairLabels.lean) formalizes Lemma 2.1 and the local
   three-pair triangle argument.
4. [`LinAlgDual.lean`](RequestProject/LinAlgDual.lean),
   [`DualParity.lean`](RequestProject/DualParity.lean), and
   [`Duality.lean`](RequestProject/Duality.lean) formalize the annihilator criterion, the local
   parity calculation, and Lemma 2.2.
5. [`Core.lean`](RequestProject/Core.lean) constructs the pair labels and proves the
   self-contained core theorem.
6. [`EightFlow.lean`](RequestProject/EightFlow.lean),
   [`CubicReduction.lean`](RequestProject/CubicReduction.lean), and
   [`Global.lean`](RequestProject/Global.lean) state the two imported theorem interfaces and
   assemble the conditional global conclusion.

[`DEPENDENCY_MAP.md`](DEPENDENCY_MAP.md) gives the detailed correspondence between the paper's
numbered equations and Lean declarations. The internal module path `RequestProject` is retained
from the audited Aristotle output; [`CycleDoubleCover.lean`](CycleDoubleCover.lean) is the public
root module.

## Verification

The project is pinned to Lean `v4.28.0` and Mathlib `v4.28.0` at commit
`8f9d9cff6bd728b17a24e163c9402775d9e6a365`.

On a networked machine with `elan`, run:

```bash
./VERIFY.sh
```

This command verifies the recorded source hashes, scans for forbidden proof placeholders and
proof-producing escape hatches, runs independent exhaustive checks of the finite `F_2^3`
identities, executes `lake build`, and prints the axioms of the two principal declarations.

GitHub Actions performs those checks on every push, pull request, and manual dispatch. It also
runs Lean's bundled `leanchecker` environment recheck. The authoritative Lean axiom audit is in
[`RequestProject/Audit.lean`](RequestProject/Audit.lean).

The reconstructed paper source is available at [`paper/cdc_proof.tex`](paper/cdc_proof.tex).

## Provenance and editorial policy

The directly browsable source tree is the audited formalization artifact. Git records every file
and every subsequent change; [`SHA256SUMS`](SHA256SUMS) provides an additional content manifest.

The mathematical declarations and proof terms are those produced in the audited Aristotle
revision. The publication pass changed only documentation and one obsolete prompt-style comment
in `PairLabels.lean`; it did not refactor proof scripts merely for appearance.

The source project requests the following attribution when the formalization is reused:

```text
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```

## License status

No software license was supplied with the formalization. The repository is public for inspection
and verification, but no additional reuse license is asserted here.
