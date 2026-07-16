# Cycle Double Cover formalization

Lean 4 formalization of the self-contained argument in *A Proof of the Cycle Double Cover Conjecture*. The formalization was produced by [Aristotle](https://aristotle.harmonic.fun) and curated and audited through a ChatGPT orchestration workflow.

## Precisely what is formalized

The unconditional core theorem proves that a finite loopless cubic edge-indexed multigraph with a nowhere-zero flow in

```text
Gamma = (ZMod 2)^3
```

has a cycle double cover:

```lean
CycleDoubleCover.OrientedMultiGraph.cycleDoubleCover_of_nowhereZero_gammaFlow
```

The theorem for all finite graphs is intentionally **conditional**:

```lean
CycleDoubleCover.OrientedMultiGraph.cycleDoubleCoverConjecture_of_gammaFlow_of_cubicReduction
```

It takes two ordinary parameters representing the external results cited in the paper:

1. the Kilpatrick–Jaeger nowhere-zero `Gamma`-flow theorem;
2. Jaeger's reduction to loopless cubic multigraphs.

Those two external results are not formalized in this repository. They are not introduced as project axioms; they are explicit hypotheses of the conditional assembly theorem. There is therefore deliberately no unconditional declaration named simply `cycleDoubleCoverConjecture`.

## Graph model

`OrientedMultiGraph V E` stores `src, dst : E → V`. Distinct edge identities represent parallel edges faithfully, loops are allowed by the model, and orientation is auxiliary. The project proves orientation invariance for the relevant graph-theoretic predicates.

A cycle is a nonempty connected edge set with degree zero or two at every vertex. Thus two parallel edges form a cycle, while a disconnected even subgraph does not. A cycle double cover is a finite indexed family of cycles in which every edge occurs exactly twice; repeated cycles are allowed.

The project uses the explicit predicate `EveryEdgeInCycle` rather than silently identifying it with a separately formalized cut-edge definition.

## Reproducible verification

The project is pinned to Lean `v4.28.0` and Mathlib `v4.28.0`, commit `8f9d9cff6bd728b17a24e163c9402775d9e6a365`.

On a networked machine with `elan`, run:

```bash
./VERIFY.sh
```

This command:

1. verifies all recorded SHA-256 hashes;
2. scans the source for forbidden proof placeholders and escape hatches;
3. runs independent exhaustive checks of the finite `F_2^3` identities at the proof's crux;
4. executes `lake build`;
5. checks and prints the axioms of the two principal declarations.

GitHub Actions runs the Lean build and source audit on every push and pull request.

## Repository layout

- `CycleDoubleCover.lean` — public root module.
- `RequestProject/` — complete Lean development.
- `DEPENDENCY_MAP.md` — correspondence between paper equations and Lean declarations.
- `AUDIT_REPORT.md` — critical audit, exact scope, and limitations.
- `audit/` — source scan and independent finite-algebra checks.
- `paper/` — supplied paper PDF and reconstructed LaTeX source.
- `provenance/` — exact revised Aristotle response archive.
- `VERIFY.sh` and `SHA256SUMS` — reproducibility and integrity checks.

## Attribution

The source project requests the following Aristotle attribution when reusing the formalization:

```text
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```

The paper's own statement of AI use is preserved in `paper/cdc_proof.pdf` and `paper/cdc_proof.tex`.

## License status

No software license was supplied with the formalization. The repository is public for inspection and verification, but no additional reuse license is asserted here.
