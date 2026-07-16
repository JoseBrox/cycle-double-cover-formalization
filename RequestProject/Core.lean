import RequestProject.PairLabels
import RequestProject.Duality

open scoped BigOperators
open scoped Classical

set_option autoImplicit false

namespace CycleDoubleCover

namespace OrientedMultiGraph

variable {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E] [Fintype E]
variable (G : OrientedMultiGraph V E)

/-- The pair label of an edge computed from the `src` endpoint (equation after Lemma 2.2). -/
noncomputable def pairLabel (hl : G.Loopless) (hc : G.Cubic) (f : E → Gamma) (t : V → Gamma)
    (e : E) : Finset Gamma :=
  pairSet (t (G.src e) + G.gLocal hl hc f (G.src e) e) (f e)

/-
Endpoint independence of the pair label (given a solution of the gluing system).
-/
lemma pairLabel_frame (hl : G.Loopless) (hc : G.Cubic) (f : E → Gamma) (t : V → Gamma)
    (ε : E → F2)
    (hglue : ∀ e : E, t (G.src e) + t (G.dst e) + ε e • f e = G.dEdge hl hc f e)
    {v : V} {e : E} (hinc : G.EdgeIncident v e) :
    G.pairLabel hl hc f t e = pairSet (t v + G.gLocal hl hc f v e) (f e) := by
  rcases hinc with ( h | h );
  · unfold pairLabel; aesop;
  · have h_eq : t (G.src e) + G.gLocal hl hc f (G.src e) e + (t v + G.gLocal hl hc f v e) = ε e • f e := by
      simp_all +decide [ add_comm, add_left_comm, add_assoc, eq_sub_iff_add_eq ];
      simp_all +decide [ ← add_assoc, dEdge ];
      grind +ring;
    apply pairSet_eq_iff.mpr;
    cases' Fin.exists_fin_two.mp ⟨ ε e, rfl ⟩ with h h <;> simp_all +decide

/-
Local evenness of the pair labeling (equation (3) transported to the graph).
-/
lemma pairLabel_local_evenness (hl : G.Loopless) (hc : G.Cubic) (f : E → Gamma)
    (hflow : G.IsFlow f) (hnz : NowhereZero f) (t : V → Gamma) (ε : E → F2)
    (hglue : ∀ e : E, t (G.src e) + t (G.dst e) + ε e • f e = G.dEdge hl hc f e)
    (v : V) (s : Gamma) :
    ((G.incidentEdges v).filter (fun e => s ∈ G.pairLabel hl hc f t e)).card = 0 ∨
    ((G.incidentEdges v).filter (fun e => s ∈ G.pairLabel hl hc f t e)).card = 2 := by
  obtain ⟨x, y, z, hx, hy, hz, hsum⟩ : ∃ x y z : Gamma, f (G.edgeOrd hl hc v 0) = x ∧ f (G.edgeOrd hl hc v 1) = y ∧ f (G.edgeOrd hl hc v 2) = z ∧ x + y + z = 0 ∧ x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0 := by
    exact ⟨ _, _, _, rfl, rfl, rfl, G.vertex_incident_sum hl hc f hflow v, hnz _, hnz _, hnz _ ⟩;
  rw [ G.incidentEdges_eq_ordered hl hc v ];
  rw [ Finset.filter_insert, Finset.filter_insert, Finset.filter_singleton ];
  have h_pairLabels : G.pairLabel hl hc f t (G.edgeOrd hl hc v 0) = pairSet (t v) x ∧ G.pairLabel hl hc f t (G.edgeOrd hl hc v 1) = pairSet (t v + x) y ∧ G.pairLabel hl hc f t (G.edgeOrd hl hc v 2) = pairSet (t v) z := by
    have h_pairLabels : ∀ i : Fin 3, G.pairLabel hl hc f t (G.edgeOrd hl hc v i) = pairSet (t v + G.gLocal hl hc f v (G.edgeOrd hl hc v i)) (f (G.edgeOrd hl hc v i)) := by
      exact fun i => G.pairLabel_frame hl hc f t ε hglue ( G.edgeOrd_incident hl hc v i );
    simp_all +decide [ G.gLocal_ord0, G.gLocal_ord1, G.gLocal_ord2 ];
  have := local_evenness_count ( t v ) x y z s ( by
    grind +splitIndPred ) hsum.2.1 hsum.2.2.1 hsum.2.2.2;
  grind

/-- **Self-contained core theorem.** A loopless cubic multigraph with a nowhere-zero
`Γ = 𝔽₂³`-flow has a cycle double cover. -/
theorem cycleDoubleCover_of_nowhereZero_gammaFlow
    (hl : G.Loopless) (hc : G.Cubic) (f : E → Gamma)
    (hflow : G.IsFlow f) (hnz : NowhereZero f) :
    G.HasCycleDoubleCover := by
  obtain ⟨t, ε, hglue⟩ := G.glue_system_solvable hl hc f hflow hnz
  refine G.pairLabeling_gives_cycleDoubleCover hl (G.pairLabel hl hc f t) ?_ ?_
  · intro e; exact pairSet_card (hnz e)
  · intro v s
    exact G.pairLabel_local_evenness hl hc f hflow hnz t ε hglue v s

end OrientedMultiGraph

end CycleDoubleCover
