# Cycle Double Cover formalization

This public repository preserves the audited Lean 4 formalization of the self-contained argument in *A Proof of the Cycle Double Cover Conjecture*.

The formalization was produced by [Aristotle](https://aristotle.harmonic.fun), with preparation, orchestration, and critical audit performed through ChatGPT. The repository description supplied by the owner is preserved.

## Canonical proof artifact

The complete, exact, reproducible project is stored in:

```text
formalization-source.tar.gz
```

Its SHA-256 digest is:

```text
2d710dab7d08c26051b469d98ab59ec0e4a3c155ea4ee2c47b7e164e16611395
```

To inspect and verify it:

```bash
sha256sum -c FORMALIZATION_SHA256.txt
mkdir formalization
 tar -xzf formalization-source.tar.gz -C formalization
cd formalization
./VERIFY.sh
```

The archive contains:

- the complete Lean sources under `RequestProject/`;
- the public root module `CycleDoubleCover.lean`;
- pinned Lean and Mathlib metadata;
- the dependency map linking the paper to Lean declarations;
- source and finite-algebra audits;
- the reconstructed paper source;
- the exact revised Aristotle response archive;
- the full critical audit report.

GitHub Actions independently verifies the archive digest, extracts the project, runs the source scan and finite checks, and invokes the pinned Lean build.

## Precisely what is formalized

The unconditional core theorem is:

```lean
CycleDoubleCover.OrientedMultiGraph.cycleDoubleCover_of_nowhereZero_gammaFlow
```

It proves that a finite loopless cubic edge-indexed multigraph carrying a nowhere-zero flow in `Gamma = (ZMod 2)^3` has a cycle double cover.

The all-graphs assembly theorem is intentionally conditional:

```lean
CycleDoubleCover.OrientedMultiGraph.cycleDoubleCoverConjecture_of_gammaFlow_of_cubicReduction
```

It takes the two external results cited by the paper as explicit parameters: the Kilpatrick–Jaeger nowhere-zero `Gamma`-flow theorem and Jaeger's cubic reduction. Those two cited results are not formalized here and are not introduced as project axioms.

## Audit status

No important flaw was found in the revised formalization. See [`AUDIT_REPORT.md`](AUDIT_REPORT.md) for the exact scope, checks, and limitations.

The project contains no `sorry`, `admit`, project `axiom`, `native_decide`, `@[implemented_by]`, unsafe proof-producing declaration, or `exact?` placeholder. Independent exhaustive checks cover the finite algebra at the proof's crux.

## Attribution

The source project requests the following attribution:

```text
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```

## License status

No software license was supplied with the formalization. The repository is public for inspection and verification, but no additional reuse license is asserted here.
