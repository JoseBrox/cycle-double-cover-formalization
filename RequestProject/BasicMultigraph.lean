import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.CharP.Pi
import Mathlib.Algebra.CharP.Two
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Tactic

open scoped BigOperators

set_option autoImplicit false

namespace CycleDoubleCover

/-!
# Finite edge-indexed oriented multigraphs

We use a custom finite edge-indexed multigraph model, with a fixed arbitrary orientation
carried as data.  Distinct elements of `E` may have the same endpoints, so parallel edges
are represented faithfully.  The orientation is used only to define flows; all cycle and
incidence notions are orientation-independent (they only refer to the unordered endpoints).
-/

/-- A finite oriented multigraph: each edge `e : E` has a source and destination vertex. -/
structure OrientedMultiGraph (V E : Type*) where
  src : E → V
  dst : E → V

namespace OrientedMultiGraph

variable {V E : Type*} [DecidableEq V]

/-- The number of times vertex `v` is an endpoint of edge `e` (counting a loop twice). -/
def endpointMultiplicity (G : OrientedMultiGraph V E) (v : V) (e : E) : ℕ :=
  (if G.src e = v then 1 else 0) + (if G.dst e = v then 1 else 0)

/-- The degree of `v` in the sub-multigraph carried by the edge set `F` (a loop counts twice). -/
def degreeIn [Fintype E] (G : OrientedMultiGraph V E) (F : Finset E) (v : V) : ℕ :=
  ∑ e ∈ F, G.endpointMultiplicity v e

/-- `v` is an endpoint of `e`. -/
def EdgeIncident (G : OrientedMultiGraph V E) (v : V) (e : E) : Prop :=
  G.src e = v ∨ G.dst e = v

instance (G : OrientedMultiGraph V E) (v : V) (e : E) :
    Decidable (G.EdgeIncident v e) := by
  unfold EdgeIncident; infer_instance

/-- The finite set of edges incident to `v`. -/
def incidentEdges [Fintype E] [DecidableEq V] (G : OrientedMultiGraph V E) (v : V) : Finset E :=
  Finset.univ.filter (fun e => G.EdgeIncident v e)

/-- `G` is loopless if no edge has equal endpoints. -/
def Loopless (G : OrientedMultiGraph V E) : Prop := ∀ e, G.src e ≠ G.dst e

/-- `G` is cubic if every vertex has degree `3`. -/
def Cubic [Fintype V] [Fintype E] (G : OrientedMultiGraph V E) : Prop :=
  ∀ v, G.degreeIn Finset.univ v = 3

variable [Fintype E]

lemma mem_incidentEdges {G : OrientedMultiGraph V E} {v : V} {e : E} :
    e ∈ G.incidentEdges v ↔ G.EdgeIncident v e := by
  simp [incidentEdges]

omit [Fintype E] in
/-- On a loopless graph the endpoint multiplicity is `0` or `1`, and `1` exactly on incident edges. -/
lemma endpointMultiplicity_loopless {G : OrientedMultiGraph V E} (hl : G.Loopless)
    (v : V) (e : E) :
    G.endpointMultiplicity v e = (if G.EdgeIncident v e then 1 else 0) := by
  unfold endpointMultiplicity EdgeIncident
  by_cases hs : G.src e = v <;> by_cases hd : G.dst e = v
  · exact absurd (hs.trans hd.symm) (hl e)
  · simp [hs, hd]
  · simp [hs, hd]
  · simp [hs, hd]

/-- On a loopless graph, degree in `F` counts the incident edges of `F`. -/
lemma degreeIn_loopless {G : OrientedMultiGraph V E} (hl : G.Loopless) (F : Finset E) (v : V) :
    G.degreeIn F v = (F.filter (fun e => G.EdgeIncident v e)).card := by
  unfold degreeIn
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  rw [endpointMultiplicity_loopless hl]

end OrientedMultiGraph

end CycleDoubleCover
