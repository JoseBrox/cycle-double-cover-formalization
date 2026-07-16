# Cycle Double Cover dependency map

## Versions and validation

* Lean `v4.28.0`.
* Mathlib `v4.28.0` (`8f9d9cff6bd728b17a24e163c9402775d9e6a365`).
* Build command: `lake build`.
* Audit command: `lake env lean RequestProject/Audit.lean`.

## Paper numbering

| Paper item | Lean declarations |
|---|---|
| Equation (1): local pair-label multiplicity condition | `OrientedMultiGraph.pairLabeling_gives_cycleDoubleCover`; condition constructed by `pairLabel_local_evenness` |
| Equation (2): local correction `g` | `OrientedMultiGraph.gLocal`, `gLocal_ord0`, `gLocal_ord1`, `gLocal_ord2` |
| Equation (3): local family of pair sets / triangle evenness | `pairSet`, `local_evenness_count` |
| Equation (4): gluing system | `OrientedMultiGraph.Lmap`, `dEdge`, `glue_system_solvable` |
| Equation (5): dual constraints | `dual_constraint_edge`, `dual_constraint_vertex` |
| Equation (6): required annihilation of `d` | final annihilation calculation in `glue_system_solvable`, using `sum_endpoints_eq_sum_incident` and `vertex_dual_identity` |
| Equations (7)--(9): local dual parity | `local_dual_parity`, `vertex_dual_identity` |
| Lemma 2.1 | `OrientedMultiGraph.pairLabeling_gives_cycleDoubleCover` |
| Lemma 2.2 | `OrientedMultiGraph.glue_system_solvable` |
| Self-contained core | `OrientedMultiGraph.cycleDoubleCover_of_nowhereZero_gammaFlow` |

The cubic-vertex identity `x + y + z = 0` is an **unnumbered** identity in the paper. It is
represented by `vertex_incident_sum` and `vertex_flow_values`; it is not equation (1).

## Graph-theoretic support

`exists_cycle_partition_of_degree_zero_or_two` proves that an even edge set decomposes into
genuine connected cycles. `SameEndpoints.isCycle`, `.hasCycleDoubleCover`, `.loopless`,
`.cubic`, and `.everyEdgeInCycle` establish orientation invariance.

The publication API uses `EveryEdgeInCycle`. It does not claim that a conventional cut-edge
predicate and its equivalence have been formalized.

## External interfaces and conditional theorem

`NowhereZeroGammaFlowTheorem` and `CubicReductionTheorem` are universe-polymorphic named
propositions supplied as ordinary parameters. The conditional assembly theorem is
`cycleDoubleCoverConjecture_of_gammaFlow_of_cubicReduction`. No unqualified theorem named
`cycleDoubleCoverConjecture` is declared.

## Regression examples

`Examples.lean` contains only compiling Lean regressions: a two-parallel-edge cycle, orientation
invariance for that graph, and a three-edge dipole with a concrete nowhere-zero `Gamma` flow.
No Petersen-graph formalization is claimed.
