import RequestProject.LinAlgDual
import RequestProject.DualParity

open scoped BigOperators
open scoped Classical

set_option autoImplicit false

namespace CycleDoubleCover

namespace OrientedMultiGraph

variable {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E] [Fintype E]
variable (G : OrientedMultiGraph V E)

/-
Under looplessness and cubicity the subtype of edges incident to `v` has exactly three
elements.
-/
lemma card_edgeIncident_subtype (hl : G.Loopless) (hc : G.Cubic) (v : V) :
    Fintype.card {e : E // G.EdgeIncident v e} = 3 := by
  rw [ ← G.card_incidentEdges_of_cubic hl hc v, Fintype.card_subtype ];
  congr

/-- A chosen ordering of the three edges incident to `v`. -/
noncomputable def incEquiv (hl : G.Loopless) (hc : G.Cubic) (v : V) :
    Fin 3 ≃ {e : E // G.EdgeIncident v e} :=
  (Fintype.equivFinOfCardEq (G.card_edgeIncident_subtype hl hc v)).symm

/-- The `i`-th incident edge at `v` in the chosen ordering. -/
noncomputable def edgeOrd (hl : G.Loopless) (hc : G.Cubic) (v : V) (i : Fin 3) : E :=
  (G.incEquiv hl hc v i).1

lemma edgeOrd_incident (hl : G.Loopless) (hc : G.Cubic) (v : V) (i : Fin 3) :
    G.EdgeIncident v (G.edgeOrd hl hc v i) := (G.incEquiv hl hc v i).2

lemma edgeOrd_injective (hl : G.Loopless) (hc : G.Cubic) (v : V) :
    Function.Injective (G.edgeOrd hl hc v) := by
  intro i j hij
  apply (G.incEquiv hl hc v).injective
  exact Subtype.ext hij

/-
The incident edges of `v` are exactly the three ordered edges.
-/
lemma incidentEdges_eq_ordered (hl : G.Loopless) (hc : G.Cubic) (v : V) :
    G.incidentEdges v =
      {G.edgeOrd hl hc v 0, G.edgeOrd hl hc v 1, G.edgeOrd hl hc v 2} := by
  have h_eq : Finset.image (G.edgeOrd hl hc v) {0, 1, 2} = G.incidentEdges v := by
    refine' Finset.eq_of_subset_of_card_le ( Finset.image_subset_iff.mpr _ ) _;
    · exact fun i hi => G.mem_incidentEdges.mpr ( G.edgeOrd_incident hl hc v i );
    · rw [ Finset.card_image_of_injective _ ( G.edgeOrd_injective hl hc v ) ] ; simp +decide [ G.card_incidentEdges_of_cubic hl hc v ];
  grind +qlia

/-- The paper's local correction term `g` (equation (2)). -/
noncomputable def gLocal (hl : G.Loopless) (hc : G.Cubic) (f : E → Gamma) (v : V) (e : E) :
    Gamma :=
  if e = G.edgeOrd hl hc v 1 then f (G.edgeOrd hl hc v 0) else 0

/-- The edge correction `d` (equation before (4)). -/
noncomputable def dEdge (hl : G.Loopless) (hc : G.Cubic) (f : E → Gamma) (e : E) : Gamma :=
  G.gLocal hl hc f (G.src e) e + G.gLocal hl hc f (G.dst e) e

/-- The gluing linear map `L` (equation (4)). -/
noncomputable def Lmap (f : E → Gamma) :
    ((V → Gamma) × (E → F2)) →ₗ[F2] (E → Gamma) where
  toFun q := fun e => q.1 (G.src e) + q.1 (G.dst e) + q.2 e • f e
  map_add' a b := by
    funext e
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, add_smul]
    abel
  map_smul' c a := by
    funext e
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, RingHom.id_apply, smul_add,
      smul_smul, smul_eq_mul]

@[simp] lemma Lmap_apply (f : E → Gamma) (q : (V → Gamma) × (E → F2)) (e : E) :
    G.Lmap f q e = q.1 (G.src e) + q.1 (G.dst e) + q.2 e • f e := rfl

/-- Values of `g` on the three ordered incident edges. -/
lemma gLocal_ord0 (hl : G.Loopless) (hc : G.Cubic) (f : E → Gamma) (v : V) :
    G.gLocal hl hc f v (G.edgeOrd hl hc v 0) = 0 := by
  have h : (G.edgeOrd hl hc v 0) ≠ G.edgeOrd hl hc v 1 := by
    intro hcon; exact (by decide : (0 : Fin 3) ≠ 1) (G.edgeOrd_injective hl hc v hcon)
  simp [gLocal, h]

lemma gLocal_ord1 (hl : G.Loopless) (hc : G.Cubic) (f : E → Gamma) (v : V) :
    G.gLocal hl hc f v (G.edgeOrd hl hc v 1) = f (G.edgeOrd hl hc v 0) := by
  simp [gLocal]

lemma gLocal_ord2 (hl : G.Loopless) (hc : G.Cubic) (f : E → Gamma) (v : V) :
    G.gLocal hl hc f v (G.edgeOrd hl hc v 2) = 0 := by
  have h : (G.edgeOrd hl hc v 2) ≠ G.edgeOrd hl hc v 1 := by
    intro hcon; exact (by decide : (2 : Fin 3) ≠ 1) (G.edgeOrd_injective hl hc v hcon)
  simp [gLocal, h]

/-
At each vertex the three incident flow values sum to zero (an unnumbered identity in the paper).
-/
lemma vertex_incident_sum (hl : G.Loopless) (hc : G.Cubic) (f : E → Gamma)
    (hflow : G.IsFlow f) (v : V) :
    f (G.edgeOrd hl hc v 0) + f (G.edgeOrd hl hc v 1) + f (G.edgeOrd hl hc v 2) = 0 := by
  convert ( G.isFlow_iff_incident_sum_zero hl f ).mp hflow v using 1;
  rw [ G.incidentEdges_eq_ordered hl hc v, Finset.sum_insert, Finset.sum_insert ] <;> simp +decide [ G.edgeOrd_injective hl hc v |> Function.Injective.eq_iff ];
  abel1

/-- The three incident flow values are nonzero and `z = x + y`. -/
lemma vertex_flow_values (hl : G.Loopless) (hc : G.Cubic) (f : E → Gamma)
    (hflow : G.IsFlow f) (hnz : NowhereZero f) (v : V) :
    f (G.edgeOrd hl hc v 2) = f (G.edgeOrd hl hc v 0) + f (G.edgeOrd hl hc v 1) ∧
      f (G.edgeOrd hl hc v 0) ≠ 0 ∧ f (G.edgeOrd hl hc v 1) ≠ 0 ∧
      f (G.edgeOrd hl hc v 2) ≠ 0 := by
  refine ⟨?_, hnz _, hnz _, hnz _⟩
  have h := G.vertex_incident_sum hl hc f hflow v
  have hz : f (G.edgeOrd hl hc v 2)
      = -(f (G.edgeOrd hl hc v 0) + f (G.edgeOrd hl hc v 1)) := eq_neg_of_add_eq_zero_right h
  rw [hz]; ext i; simp [CharTwo.neg_eq]

open CDCDual in
/-- Loopless double counting: summing a quantity `w e v` over each edge's two endpoints equals
summing it over incident edges at each vertex. -/
lemma sum_endpoints_eq_sum_incident {M : Type*} [AddCommMonoid M] (hl : G.Loopless)
    (w : E → V → M) :
    ∑ e, (w e (G.src e) + w e (G.dst e)) = ∑ v, ∑ e ∈ G.incidentEdges v, w e v := by
  simp +decide only [incidentEdges, Finset.sum_filter];
  rw [ Finset.sum_comm, Finset.sum_congr rfl ];
  intro e he; rw [ Finset.sum_eq_add ( G.src e ) ( G.dst e ) ] <;> simp +decide [ hl e, OrientedMultiGraph.EdgeIncident ] ;
  grind

open CDCDual in
/-- Dual constraint on each edge (equation (5), edge part): choosing `t = 0` and `ε` supported
at `e`. -/
lemma dual_constraint_edge (f : E → Gamma) (φ : Module.Dual F2 (E → Gamma))
    (hφ : ∀ x, φ (G.Lmap f x) = 0) (e : E) :
    CDCDual.coordFunctional φ e (f e) = 0 := by
  convert hφ ( 0, Pi.single e 1 ) using 1;
  -- By definition of `Lmap`, we have `Lmap f (0, Pi.single e 1) = Pi.single e (f e)`.
  have hLmap : G.Lmap f (0, Pi.single e 1) = Pi.single e (f e) := by
    ext e'; simp [Lmap];
    by_cases h : e' = e <;> simp +decide [ h, Pi.single_apply ];
  exact hLmap.symm ▸ rfl

open CDCDual in
/-- Dual constraint at each vertex (equation (5), vertex part): choosing `ε = 0` and `t`
supported at `v`. -/
lemma dual_constraint_vertex (hl : G.Loopless) (f : E → Gamma)
    (φ : Module.Dual F2 (E → Gamma)) (hφ : ∀ x, φ (G.Lmap f x) = 0) (v : V) :
    ∑ e ∈ G.incidentEdges v, CDCDual.coordFunctional φ e = 0 := by
  refine' LinearMap.ext fun x => _;
  convert hφ ( Pi.single v x, 0 ) using 1;
  rw [ CDCDual.dual_expansion ];
  rw [ ← Finset.sum_subset ( Finset.subset_univ ( G.incidentEdges v ) ) ];
  · simp +decide [ Lmap_apply, Pi.single_apply ];
    refine' Finset.sum_congr rfl fun e he => _;
    split_ifs <;> simp_all +decide [ OrientedMultiGraph.EdgeIncident ];
    · exact absurd ( hl e ) ( by aesop );
    · exact False.elim ( Finset.mem_filter.mp he |>.2 |> fun h => by cases h <;> tauto );
  · intro e _ he; simp_all +decide [ OrientedMultiGraph.incidentEdges, OrientedMultiGraph.EdgeIncident ] ;

open CDCDual in
/-- Vertex-local dual identity (equation (7)). -/
lemma vertex_dual_identity (hl : G.Loopless) (hc : G.Cubic) (f : E → Gamma)
    (hflow : G.IsFlow f) (hnz : NowhereZero f) (η : E → GammaDual)
    (hcon1 : ∀ v, ∑ e ∈ G.incidentEdges v, η e = 0)
    (hcon2 : ∀ e, η e (f e) = 0) (v : V) :
    ∑ e ∈ G.incidentEdges v, η e (G.gLocal hl hc f v e)
      = ∑ e ∈ G.incidentEdges v, nzBit (η e) := by
  rw [ G.incidentEdges_eq_ordered hl hc v, Finset.sum_insert, Finset.sum_insert ] <;> simp +decide [ G.edgeOrd_injective hl hc v |> Function.Injective.eq_iff ];
  convert local_dual_parity ( f ( G.edgeOrd hl hc v 0 ) ) ( f ( G.edgeOrd hl hc v 1 ) ) ( f ( G.edgeOrd hl hc v 2 ) ) ( η ( G.edgeOrd hl hc v 0 ) ) ( η ( G.edgeOrd hl hc v 1 ) ) ( η ( G.edgeOrd hl hc v 2 ) ) _ _ _ _ _ _ _ _ using 1;
  all_goals try tauto;
  · simp +decide [ gLocal_ord0, gLocal_ord1, gLocal_ord2 ];
  · ring;
  · exact G.vertex_flow_values hl hc f hflow hnz v |>.1;
  · rw [ ← hcon1 v, G.incidentEdges_eq_ordered hl hc v, Finset.sum_insert, Finset.sum_insert ] <;> simp +decide [ G.edgeOrd_injective hl hc v |> Function.Injective.eq_iff ];
    abel1

open CDCDual in
/-- **Lemma 2.2 (the gluing system is solvable).** -/
theorem glue_system_solvable (hl : G.Loopless) (hc : G.Cubic) (f : E → Gamma)
    (hflow : G.IsFlow f) (hnz : NowhereZero f) :
    ∃ (t : V → Gamma) (ε : E → F2),
      ∀ e : E, t (G.src e) + t (G.dst e) + ε e • f e = G.dEdge hl hc f e := by
  have hrange : G.dEdge hl hc f ∈ LinearMap.range (G.Lmap f) := by
    rw [mem_range_iff_annihilated_by_dual]
    intro φ hφ
    set η : E → GammaDual := fun e => CDCDual.coordFunctional φ e with hη
    have hcon1 : ∀ v, ∑ e ∈ G.incidentEdges v, η e = 0 :=
      fun v => G.dual_constraint_vertex hl f φ hφ v
    have hcon2 : ∀ e, η e (f e) = 0 := fun e => G.dual_constraint_edge f φ hφ e
    have hsum : φ (G.dEdge hl hc f)
        = ∑ v, ∑ e ∈ G.incidentEdges v, η e (G.gLocal hl hc f v e) := by
      rw [CDCDual.dual_expansion φ (G.dEdge hl hc f),
        ← G.sum_endpoints_eq_sum_incident hl (fun e v => η e (G.gLocal hl hc f v e))]
      exact Finset.sum_congr rfl fun e _ => map_add (η e) _ _
    rw [hsum,
      Finset.sum_congr rfl fun v _ => G.vertex_dual_identity hl hc f hflow hnz η hcon1 hcon2 v,
      ← G.sum_endpoints_eq_sum_incident hl (fun e _ => nzBit (η e))]
    simp [CharTwo.add_self_eq_zero]
  obtain ⟨q, hq⟩ := hrange
  exact ⟨q.1, q.2, fun e => congr_fun hq e⟩

end OrientedMultiGraph

end CycleDoubleCover
