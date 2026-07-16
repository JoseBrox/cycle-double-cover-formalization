import RequestProject.CubicReduction
import RequestProject.EightFlow

open scoped BigOperators

set_option autoImplicit false

namespace CycleDoubleCover

universe u v

namespace OrientedMultiGraph

/-!
# The cycle double cover conjecture

The paper's argument has three ingredients:

* the **self-contained core reduction** — a loopless cubic multigraph with a nowhere-zero
  `Γ = 𝔽₂³`-flow has a cycle double cover
  (`OrientedMultiGraph.cycleDoubleCover_of_nowhereZero_gammaFlow`), which is fully proved in
  this project without proof placeholders or project postulates;
* the **nowhere-zero `Γ`-flow theorem** of Kilpatrick–Jaeger
  (`OrientedMultiGraph.NowhereZeroGammaFlowTheorem`);
* **Jaeger's cubic reduction** (`OrientedMultiGraph.CubicReductionTheorem`).

The latter two are deep classical results imported by the paper (not part of its new argument)
and are not currently in Mathlib; here they appear as explicit named hypotheses rather than project-level postulates or
proof placeholders.  The theorem below assembles the full conclusion from them together with
the fully-proved core.
-/

/-- **Conditional theorem.** Assuming the Kilpatrick–Jaeger flow interface `hFlow` and
Jaeger's cubic-reduction interface `hReduce`, every finite multigraph satisfying
`EveryEdgeInCycle` has a cycle double cover. -/
theorem cycleDoubleCoverConjecture_of_gammaFlow_of_cubicReduction
    (hFlow : NowhereZeroGammaFlowTheorem.{u, v})
    (hReduce : CubicReductionTheorem.{u, v})
    {V : Type u} {E : Type v} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : OrientedMultiGraph V E) (hbridge : G.EveryEdgeInCycle) :
    G.HasCycleDoubleCover := by
  refine hReduce ?_ G hbridge
  intro V' E' _ _ _ _ H hl hc hbr
  obtain ⟨f, hflow, hnz⟩ := hFlow H hbr
  exact H.cycleDoubleCover_of_nowhereZero_gammaFlow hl hc f hflow hnz

end OrientedMultiGraph

end CycleDoubleCover
