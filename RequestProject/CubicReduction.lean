import RequestProject.Core

open scoped BigOperators

set_option autoImplicit false

namespace CycleDoubleCover

universe u v

namespace OrientedMultiGraph

/-!
# Reduction to loopless cubic multigraphs (Jaeger)

The paper imports the standard reduction that it suffices to prove the cycle double cover
conjecture for loopless cubic multigraphs (Jaeger, Proposition 4 of the survey).  This is an
elementary but lengthy vertex-expansion argument; it is not part of the paper's new argument
and is not currently available in Mathlib.

We isolate its exact statement here as a `Prop`: an imported theorem interface supplied
explicitly by the caller. Its proof (via vertex expansion and cycle projection) is outside
this formalization.
-/

/-- Imported Jaeger cubic-reduction interface, stated using `EveryEdgeInCycle`. -/
def CubicReductionTheorem : Prop :=
  (∀ {V : Type u} {E : Type v} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
      (H : OrientedMultiGraph V E), H.Loopless → H.Cubic → H.EveryEdgeInCycle → H.HasCycleDoubleCover) →
  (∀ {V : Type u} {E : Type v} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
      (G : OrientedMultiGraph V E), G.EveryEdgeInCycle → G.HasCycleDoubleCover)

end OrientedMultiGraph

end CycleDoubleCover
