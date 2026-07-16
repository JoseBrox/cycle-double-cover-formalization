import RequestProject.Cycles

open scoped BigOperators
open scoped Classical

set_option autoImplicit false

namespace CycleDoubleCover

namespace OrientedMultiGraph

variable {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E] [Fintype E]
variable (G : OrientedMultiGraph V E)

/-- The edges of `F` lying in a fixed connected component `c` of the edge-adjacency graph. -/
noncomputable def componentEdges (F : Finset E)
    (c : (G.edgeAdj F).ConnectedComponent) : Finset E :=
  (Finset.univ.filter
    (fun a : {e : E // e ∈ F} => (G.edgeAdj F).connectedComponentMk a = c)).image Subtype.val

variable {G}

lemma mem_componentEdges {F : Finset E} {c : (G.edgeAdj F).ConnectedComponent} {e : E} :
    e ∈ G.componentEdges F c ↔
      ∃ h : e ∈ F, (G.edgeAdj F).connectedComponentMk ⟨e, h⟩ = c := by
  unfold componentEdges
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Subtype.exists]
  constructor
  · rintro ⟨e', h', hc, rfl⟩; exact ⟨h', hc⟩
  · rintro ⟨h, hc⟩; exact ⟨e, h, hc, rfl⟩

lemma componentEdges_subset {F : Finset E} (c : (G.edgeAdj F).ConnectedComponent) :
    G.componentEdges F c ⊆ F := by
  intro e he
  rw [mem_componentEdges] at he
  obtain ⟨h, _⟩ := he
  exact h

/-- Two distinct edges of `F` incident to a common vertex lie in the same component. -/
lemma sameComponent_of_shared_vertex {F : Finset E} {e₁ e₂ : E}
    (h₁ : e₁ ∈ F) (h₂ : e₂ ∈ F) (hne : e₁ ≠ e₂) {v : V}
    (hv₁ : G.EdgeIncident v e₁) (hv₂ : G.EdgeIncident v e₂) :
    (G.edgeAdj F).connectedComponentMk ⟨e₁, h₁⟩ =
      (G.edgeAdj F).connectedComponentMk ⟨e₂, h₂⟩ := by
  apply SimpleGraph.ConnectedComponent.eq.mpr
  apply SimpleGraph.Adj.reachable
  exact ⟨by simpa [Subtype.ext_iff] using hne, v, hv₁, hv₂⟩

/-
Every vertex has degree `0` or `2` in each component.
-/
lemma componentEdges_degree {F : Finset E} (hl : G.Loopless)
    (hdeg : ∀ v, G.degreeIn F v = 0 ∨ G.degreeIn F v = 2)
    (c : (G.edgeAdj F).ConnectedComponent) (v : V) :
    G.degreeIn (G.componentEdges F c) v = 0 ∨ G.degreeIn (G.componentEdges F c) v = 2 := by
  -- Let $S := F.filter (fun e => G.EdgeIncident v e)$ and $T := (componentEdges F c).filter (fun e => G.EdgeIncident v e)$.
  set S := F.filter (fun e => G.EdgeIncident v e)
  set T := (G.componentEdges F c).filter (fun e => G.EdgeIncident v e);
  -- By definition of $S$ and $T$, we have $T \subseteq S$.
  have hT_subset_S : T ⊆ S := by
    exact fun x hx => Finset.mem_filter.mpr ⟨ G.componentEdges_subset c ( Finset.mem_filter.mp hx |>.1 ), Finset.mem_filter.mp hx |>.2 ⟩;
  -- By definition of $S$ and $T$, we have $|S| = 0$ or $|S| = 2$.
  have hS_card : S.card = 0 ∨ S.card = 2 := by
    have := hdeg v; rw [ degreeIn_loopless hl F v ] at this; aesop;
  cases' hS_card with hS_card hS_card;
  · simp_all +decide [ Finset.ext_iff ];
    rw [ OrientedMultiGraph.degreeIn_loopless hl ];
    exact Or.inl ( Finset.card_eq_zero.mpr ( Finset.eq_empty_of_forall_notMem fun e he => hS_card e <| hT_subset_S he ) );
  · -- Since $|S| = 2$, let $S = \{e_1, e_2\}$ with $e_1 \neq e_2$.
    obtain ⟨e₁, e₂, he₁, he₂, he_distinct⟩ : ∃ e₁ e₂ : E, e₁ ∈ S ∧ e₂ ∈ S ∧ e₁ ≠ e₂ ∧ S = {e₁, e₂} := by
      rw [ Finset.card_eq_two ] at hS_card; obtain ⟨ e₁, e₂, h ⟩ := hS_card; use e₁, e₂; aesop;
    -- Since $e₁$ and $e₂$ are in the same connected component, they are either both in $T$ or both not in $T$.
    have hT_eq : (e₁ ∈ T ↔ e₂ ∈ T) := by
      grind +suggestions;
    -- Since $T$ is a subset of $S$ and $S$ has exactly two elements, $T$ can only contain $e₁$ and $e₂$ if both are in $T$. Otherwise, $T$ must be empty.
    have hT_cases : T = ∅ ∨ T = {e₁, e₂} := by
      grind;
    cases' hT_cases with hT_cases hT_cases <;> simp_all +decide [ degreeIn_loopless ];
    · exact Or.inl fun x hx hx' => Finset.notMem_empty x <| hT_cases ▸ Finset.mem_filter.mpr ⟨ hx, hx' ⟩;
    · exact Or.inr ( by rw [ show { e ∈ G.componentEdges F c | G.EdgeIncident v e } = { e₁, e₂ } by ext; aesop ] ; simp +decide [ he_distinct ] )

/-
The edge-adjacency graph of a component is connected.
-/
lemma componentEdges_connected {F : Finset E}
    (c : (G.edgeAdj F).ConnectedComponent)
    (hne : (G.componentEdges F c).Nonempty) :
    (G.edgeAdj (G.componentEdges F c)).Connected := by
  have h_iso : Nonempty ((G.edgeAdj (G.componentEdges F c)).Iso (SimpleGraph.induce (fun a : {e // e ∈ F} => (G.edgeAdj F).connectedComponentMk a = c) (G.edgeAdj F))) := by
    refine' ⟨ _, _ ⟩;
    refine' Equiv.ofBijective ( fun x => ⟨ ⟨ x.val, _ ⟩, _ ⟩ ) ⟨ _, _ ⟩;
    all_goals norm_num [ Function.Injective, Function.Surjective ];
    exact G.componentEdges_subset _ x.2;
    · exact mem_componentEdges.mp x.2 |> fun ⟨ h₁, h₂ ⟩ => h₂;
    · exact fun a ha ha' => Finset.mem_image.mpr ⟨ ⟨ a, ha ⟩, Finset.mem_filter.mpr ⟨ Finset.mem_univ _, ha' ⟩, rfl ⟩;
    · unfold OrientedMultiGraph.edgeAdj; aesop;
  convert h_iso.some.connected_iff.mpr _;
  convert c.maximal_connected_induce_supp.1

/-- Each component's edge set is nonempty. -/
lemma componentEdges_nonempty {F : Finset E}
    (c : (G.edgeAdj F).ConnectedComponent) :
    (G.componentEdges F c).Nonempty := by
  obtain ⟨a, ha⟩ := c.exists_rep
  exact ⟨a.1, mem_componentEdges.mpr ⟨a.2, ha⟩⟩

/-- Each component is a genuine cycle. -/
lemma componentEdges_isCycle {F : Finset E} (hl : G.Loopless)
    (hdeg : ∀ v, G.degreeIn F v = 0 ∨ G.degreeIn F v = 2)
    (c : (G.edgeAdj F).ConnectedComponent) :
    G.IsCycle (G.componentEdges F c) := by
  refine ⟨componentEdges_nonempty c, componentEdges_degree hl hdeg c,
    componentEdges_connected c (componentEdges_nonempty c)⟩

/-
**Cycle decomposition lemma.** Any edge set in which every vertex has degree `0` or `2`
is the disjoint union of genuine cycles.
-/
theorem exists_cycle_partition_of_degree_zero_or_two (hl : G.Loopless) (F : Finset E)
    (hdeg : ∀ v, G.degreeIn F v = 0 ∨ G.degreeIn F v = 2) :
    ∃ (n : ℕ) (C : Fin n → Finset E),
      (∀ i, G.IsCycle (C i)) ∧
      (∀ i j, i ≠ j → Disjoint (C i) (C j)) ∧
      F = Finset.univ.biUnion C := by
  use Fintype.card (G.edgeAdj F).ConnectedComponent;
  refine' ⟨ fun i => G.componentEdges F ( Fintype.equivFin _ |>.symm i ), _, _, _ ⟩;
  · exact fun i => componentEdges_isCycle hl hdeg _;
  · intro i j hij; rw [ Finset.disjoint_left ] ; intro e he₁ he₂; simp_all +decide [ Finset.subset_iff ] ;
    obtain ⟨ h₁, h₂ ⟩ := mem_componentEdges.mp he₁; obtain ⟨ h₃, h₄ ⟩ := mem_componentEdges.mp he₂; simp_all +decide [ Fintype.equivFin ] ;
  · ext e;
    simp +decide [ mem_componentEdges ];
    exact ⟨ fun he => ⟨ Fintype.equivFin _ ( ( G.edgeAdj F ).connectedComponentMk ⟨ e, he ⟩ ), he, by simp +decide ⟩, by rintro ⟨ a, he, ha ⟩ ; exact he ⟩

end OrientedMultiGraph

end CycleDoubleCover
