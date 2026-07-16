import RequestProject.BasicMultigraph

open scoped BigOperators

set_option autoImplicit false

namespace CycleDoubleCover

/-- The field with two elements. -/
abbrev F2 := ZMod 2
/-- The group `Γ = 𝔽₂³`. -/
abbrev Gamma := Fin 3 → F2
/-- The dual space `Γ*`. -/
abbrev GammaDual := Module.Dual F2 Gamma

namespace OrientedMultiGraph

variable {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E] [Fintype E]

/-- An `A`-flow: the sum on out-edges equals the sum on in-edges at every vertex. -/
def IsFlow {A : Type*} [AddCommGroup A] (G : OrientedMultiGraph V E) (f : E → A) : Prop :=
  ∀ v : V,
    (∑ e, if G.src e = v then f e else 0) =
    (∑ e, if G.dst e = v then f e else 0)

/-- A map is nowhere zero if it never takes the value `0`. -/
def NowhereZero {A : Type*} [Zero A] (f : E → A) : Prop := ∀ e, f e ≠ 0

/-
Under looplessness, being a `Γ`-flow is equivalent to the incident sum vanishing at each
vertex (characteristic-two reformulation).
-/
lemma isFlow_iff_incident_sum_zero {G : OrientedMultiGraph V E} (hl : G.Loopless) (f : E → Gamma) :
    G.IsFlow f ↔ ∀ v : V, ∑ e ∈ G.incidentEdges v, f e = 0 := by
  refine' ⟨ fun hf v => _, fun hf v => _ ⟩;
  · convert sub_eq_zero.mpr ( hf v ) using 1;
    simp +decide only [incidentEdges, Finset.sum_filter];
    rw [ ← Finset.sum_sub_distrib ] ; congr ; ext e ; unfold OrientedMultiGraph.EdgeIncident ; split_ifs <;> simp_all +decide [ sub_eq_add_neg ] ;
    exact False.elim ( hl e ( by aesop ) );
  · have h_split :
        ∑ e ∈ Finset.univ.filter (fun e => G.EdgeIncident v e), f e =
          ∑ e ∈ Finset.univ.filter (fun e => G.src e = v), f e +
            ∑ e ∈ Finset.univ.filter (fun e => G.dst e = v), f e := by
      rw [← Finset.sum_union]
      · congr with e
        simp +decide [OrientedMultiGraph.EdgeIncident]
      · exact Finset.disjoint_filter.mpr fun e _ he₁ he₂ => hl e <| he₁.trans he₂.symm
    have hzero := hf v
    rw [incidentEdges, h_split] at hzero
    have hout := eq_neg_of_add_eq_zero_left hzero
    have hneg (q : Gamma) : -q = q := by
      funext i
      exact CharTwo.neg_eq (q i)
    rw [hneg] at hout
    simpa [Finset.sum_ite] using hout

/-- Under cubicity and looplessness, each vertex is incident to exactly three edges. -/
lemma card_incidentEdges_of_cubic {G : OrientedMultiGraph V E} (hl : G.Loopless)
    (hc : G.Cubic) (v : V) : (G.incidentEdges v).card = 3 := by
  have := hc v
  rw [degreeIn_loopless hl] at this
  simpa [incidentEdges] using this

end OrientedMultiGraph

end CycleDoubleCover
