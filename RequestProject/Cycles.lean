import RequestProject.BasicMultigraph

open scoped BigOperators

set_option autoImplicit false

namespace CycleDoubleCover

namespace OrientedMultiGraph

variable {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E] [Fintype E]

/-- Auxiliary simple graph on the *edges* of `F`: two distinct edges of `F` are adjacent
when they share an endpoint.  Its vertices are edge identities, so parallel edges of the
original multigraph remain distinct. -/
def edgeAdj (G : OrientedMultiGraph V E) (F : Finset E) : SimpleGraph {e : E // e ∈ F} where
  Adj a b := a ≠ b ∧ ∃ v : V, G.EdgeIncident v a.1 ∧ G.EdgeIncident v b.1
  symm := by
    rintro a b ⟨hne, v, ha, hb⟩
    exact ⟨hne.symm, v, hb, ha⟩
  loopless := ⟨by rintro a ⟨hne, _⟩; exact hne rfl⟩

instance (G : OrientedMultiGraph V E) (F : Finset E) : DecidableRel (G.edgeAdj F).Adj :=
  fun a b => by unfold edgeAdj; infer_instance

/-- `F` is a (genuine, connected) cycle: it is nonempty, every vertex has degree `0` or `2`
in `F`, and the edge-adjacency graph of `F` is connected (so it is a single cycle, not a
disjoint union of several). -/
def IsCycle (G : OrientedMultiGraph V E) (F : Finset E) : Prop :=
  F.Nonempty ∧ (∀ v, G.degreeIn F v = 0 ∨ G.degreeIn F v = 2) ∧ (G.edgeAdj F).Connected

/-- A cycle double cover: a finite indexed family of cycles covering every edge exactly twice
(repeated cycles allowed). -/
def HasCycleDoubleCover (G : OrientedMultiGraph V E) : Prop :=
  ∃ (n : ℕ) (C : Fin n → Finset E),
    (∀ i, G.IsCycle (C i)) ∧
    (∀ e : E, (∑ i, if e ∈ C i then 1 else 0) = 2)

/-- Every edge belongs to a genuine cycle. This publication revision deliberately uses the
explicit name `EveryEdgeInCycle`: it does not claim that equivalence with a separately defined
cut-edge predicate has been formalized. The imported theorem interfaces are stated using this
predicate. -/
def EveryEdgeInCycle (G : OrientedMultiGraph V E) : Prop :=
  ∀ e : E, ∃ F : Finset E, G.IsCycle F ∧ e ∈ F

end OrientedMultiGraph

end CycleDoubleCover
