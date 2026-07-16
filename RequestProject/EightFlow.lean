import RequestProject.Core

open scoped BigOperators

set_option autoImplicit false

namespace CycleDoubleCover

universe u v

namespace OrientedMultiGraph

/-!
# The nowhere-zero `Γ = 𝔽₂³`-flow theorem (Kilpatrick–Jaeger)

The paper imports the theorem that every finite bridgeless graph carries a nowhere-zero
`Γ = 𝔽₂³`-flow (equivalently, by Tutte's group-flow theorem, a nowhere-zero `8`-flow).  This
is a deep classical result of Kilpatrick and Jaeger; it is **not** part of the paper's new
argument and is not currently available in Mathlib.

We isolate its exact statement here as a `Prop`: an imported theorem interface supplied
explicitly by the caller. Its proof is outside this formalization.
-/

/-- Imported Kilpatrick–Jaeger nowhere-zero `Γ`-flow interface, stated using
`EveryEdgeInCycle`. -/
def NowhereZeroGammaFlowTheorem : Prop :=
  ∀ {V : Type u} {E : Type v} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : OrientedMultiGraph V E), G.EveryEdgeInCycle → ∃ f : E → Gamma, G.IsFlow f ∧ NowhereZero f

end OrientedMultiGraph

end CycleDoubleCover
