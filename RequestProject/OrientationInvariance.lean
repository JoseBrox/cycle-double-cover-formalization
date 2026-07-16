import RequestProject.Cycles

open scoped BigOperators

set_option autoImplicit false

namespace CycleDoubleCover

namespace OrientedMultiGraph

variable {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E] [Fintype E]

/-- Two orientations of the same underlying multigraph: every edge has the same unordered pair
of endpoints (possibly with `src`/`dst` swapped). -/
def SameEndpoints (G G' : OrientedMultiGraph V E) : Prop :=
  ∀ e, (G.src e = G'.src e ∧ G.dst e = G'.dst e) ∨ (G.src e = G'.dst e ∧ G.dst e = G'.src e)

variable {G G' : OrientedMultiGraph V E}

lemma SameEndpoints.symm (h : SameEndpoints G G') : SameEndpoints G' G := by
  intro e; rcases h e with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h1.symm, h2.symm⟩
  · exact Or.inr ⟨h2.symm, h1.symm⟩

lemma SameEndpoints.edgeIncident (h : SameEndpoints G G') (v : V) (e : E) :
    G.EdgeIncident v e ↔ G'.EdgeIncident v e := by
  unfold EdgeIncident
  rcases h e with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> tauto

lemma SameEndpoints.endpointMultiplicity (h : SameEndpoints G G') (v : V) (e : E) :
    G.endpointMultiplicity v e = G'.endpointMultiplicity v e := by
  unfold OrientedMultiGraph.endpointMultiplicity
  rcases h e with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2]; ring

lemma SameEndpoints.degreeIn (h : SameEndpoints G G') (F : Finset E) (v : V) :
    G.degreeIn F v = G'.degreeIn F v := by
  unfold OrientedMultiGraph.degreeIn
  exact Finset.sum_congr rfl (fun e _ => h.endpointMultiplicity v e)

lemma SameEndpoints.edgeAdj (h : SameEndpoints G G') (F : Finset E) :
    G.edgeAdj F = G'.edgeAdj F := by
  ext a b
  simp only [OrientedMultiGraph.edgeAdj]
  refine and_congr_right (fun _ => ?_)
  constructor <;> rintro ⟨w, hw1, hw2⟩ <;>
    first
      | exact ⟨w, (h.edgeIncident w _).mp hw1, (h.edgeIncident w _).mp hw2⟩
      | exact ⟨w, (h.edgeIncident w _).mpr hw1, (h.edgeIncident w _).mpr hw2⟩

lemma SameEndpoints.isCycle (h : SameEndpoints G G') (F : Finset E) :
    G.IsCycle F ↔ G'.IsCycle F := by
  unfold IsCycle
  rw [h.edgeAdj F]
  refine and_congr Iff.rfl (and_congr ?_ Iff.rfl)
  constructor <;> intro hd v <;> [rw [← h.degreeIn]; rw [h.degreeIn]] <;> exact hd v

lemma SameEndpoints.loopless (h : SameEndpoints G G') : G.Loopless ↔ G'.Loopless := by
  constructor <;> intro hl e <;> rcases h e with hsame | hswap
  · simpa [hsame.1, hsame.2] using hl e
  · intro heq
    apply hl e
    rw [hswap.1, hswap.2]
    exact heq.symm
  · simpa [hsame.1, hsame.2] using hl e
  · intro heq
    apply hl e
    rw [← hswap.1, ← hswap.2]
    exact heq.symm

lemma SameEndpoints.cubic (h : SameEndpoints G G') : G.Cubic ↔ G'.Cubic := by
  constructor <;> intro hc v
  · rw [← h.degreeIn]
    exact hc v
  · rw [h.degreeIn]
    exact hc v

lemma SameEndpoints.everyEdgeInCycle (h : SameEndpoints G G') :
    G.EveryEdgeInCycle ↔ G'.EveryEdgeInCycle := by
  constructor <;> intro hb e
  · obtain ⟨F, hF, he⟩ := hb e
    exact ⟨F, (h.isCycle F).mp hF, he⟩
  · obtain ⟨F, hF, he⟩ := hb e
    exact ⟨F, (h.isCycle F).mpr hF, he⟩

/-- Having a cycle double cover depends only on the unordered endpoints (the orientation is
auxiliary). -/
theorem SameEndpoints.hasCycleDoubleCover (h : SameEndpoints G G') :
    G.HasCycleDoubleCover ↔ G'.HasCycleDoubleCover := by
  unfold HasCycleDoubleCover
  constructor <;> rintro ⟨n, C, hcyc, hcov⟩ <;> exact ⟨n, C,
    fun i => by first | exact (h.isCycle _).mp (hcyc i) | exact (h.isCycle _).mpr (hcyc i), hcov⟩

end OrientedMultiGraph

end CycleDoubleCover
