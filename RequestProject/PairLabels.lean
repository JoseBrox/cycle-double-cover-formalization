import RequestProject.CycleDecomposition
import RequestProject.Flows

open scoped BigOperators
open scoped Classical

set_option autoImplicit false

namespace CycleDoubleCover

/-- The two-element set `{A, A + p}`. -/
def pairSet (A p : Gamma) : Finset Gamma := {A, A + p}

lemma mem_pairSet {A p s : Gamma} : s ∈ pairSet A p ↔ s = A ∨ s = A + p := by
  simp [pairSet]

lemma pairSet_card {A p : Gamma} (hp : p ≠ 0) : (pairSet A p).card = 2 := by
  have hne : A ≠ A + p := by
    intro h
    apply hp
    apply add_left_cancel (a := A)
    simpa using h
  simp [pairSet, hne]

/-
Equality criterion for two-element sets in characteristic two.
-/
lemma pairSet_eq_iff {A B p : Gamma} :
    pairSet A p = pairSet B p ↔ A + B = 0 ∨ A + B = p := by
  have hself (q : Gamma) : q + q = 0 := CharTwo.add_self_eq_zero q
  constructor
  · intro h
    have hm : A ∈ pairSet B p := by
      rw [← h]
      simp [pairSet]
    rcases mem_pairSet.mp hm with hab | hab
    · left
      rw [hab, hself]
    · right
      calc
        A + B = (B + p) + B := by rw [hab]
        _ = (B + B) + p := by ac_rfl
        _ = p := by rw [hself, zero_add]
  · rintro (h | h)
    · have hab : A = B := by
        calc
          A = A + 0 := (add_zero A).symm
          _ = A + (B + B) := by rw [hself]
          _ = (A + B) + B := by rw [add_assoc]
          _ = B := by rw [h, zero_add]
      rw [hab]
    · have hab : A = B + p := by
        calc
          A = A + 0 := (add_zero A).symm
          _ = A + (B + B) := by rw [hself]
          _ = (A + B) + B := by rw [add_assoc]
          _ = B + p := by rw [h, add_comm]
      have hswap : B + p + p = B := by rw [add_assoc, hself, add_zero]
      ext q
      simp only [mem_pairSet]
      rw [hab, hswap]
      tauto

/-
**Equation (3): local evenness.** For `z = x + y` with `x, y, z` nonzero, the three sets
`{t,t+x}`, `{t+x,t+z}`, `{t,t+z}` contain any given `s` either zero or two times.
The proof treats these as the three sides of a triangle with pairwise distinct vertices.
-/
lemma local_evenness_count (t x y z s : Gamma)
    (hz : z = x + y) (hx : x ≠ 0) (hy : y ≠ 0) (hznz : z ≠ 0) :
    ((if s ∈ pairSet t x then 1 else 0) + (if s ∈ pairSet (t + x) y then 1 else 0)
      + (if s ∈ pairSet t z then (1 : ℕ) else 0) = 0) ∨
    ((if s ∈ pairSet t x then 1 else 0) + (if s ∈ pairSet (t + x) y then 1 else 0)
      + (if s ∈ pairSet t z then (1 : ℕ) else 0) = 2) := by
  have huv : t ≠ t + x := by
    intro h
    apply hx
    apply add_left_cancel (a := t)
    simpa using h
  have huw : t ≠ t + z := by
    intro h
    apply hznz
    apply add_left_cancel (a := t)
    simpa using h
  have hvw : t + x ≠ t + z := by
    intro h
    have hxz : x = z := add_left_cancel h
    apply hy
    apply add_left_cancel (a := x)
    rw [← hz, ← hxz]
    simp
  have hmid : (t + x) + y = t + z := by rw [hz, add_assoc]
  unfold pairSet
  rw [hmid]
  by_cases hsu : s = t
  · subst s
    simp [huv, huw]
  by_cases hsv : s = t + x
  · subst s
    simp [hvw, hx]
  by_cases hsw : s = t + z
  · subst s
    have hzx : z ≠ x := by
      intro h
      apply hvw
      rw [h]
    simp [hznz, hzx]
  simp [hsu, hsv, hsw]

namespace OrientedMultiGraph

variable {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E] [Fintype E]
variable {G : OrientedMultiGraph V E}

/-
Convert a cycle double cover indexed by an arbitrary finite type into the `Fin n` form.
-/
lemma hasCycleDoubleCover_of_fintypeFamily {ι : Type*} [Fintype ι] (C : ι → Finset E)
    (hcyc : ∀ i, G.IsCycle (C i))
    (hcov : ∀ e : E, (∑ i, if e ∈ C i then 1 else 0) = 2) :
    G.HasCycleDoubleCover := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, Nonempty (ι ≃ Fin n) := by
    exact ⟨ Fintype.card ι, ⟨ Fintype.equivFin ι ⟩ ⟩;
  obtain ⟨ e ⟩ := hn;
  refine' ⟨ n, fun i => C ( e.symm i ), _, _ ⟩;
  · exact fun i => hcyc _;
  · intro e_1; rw [ ← hcov e_1 ] ; rw [ ← Equiv.sum_comp e ] ; simp +decide ;

/-
If `C : Fin n → Finset E` are pairwise disjoint with union `M`, then each edge is counted
once iff it lies in `M`.
-/
lemma partition_count {n : ℕ} (C : Fin n → Finset E)
    (hdisj : ∀ i j, i ≠ j → Disjoint (C i) (C j)) (M : Finset E)
    (hunion : M = Finset.univ.biUnion C) (e : E) :
    (∑ i, if e ∈ C i then 1 else 0) = (if e ∈ M then 1 else 0) := by
  by_cases he : e ∈ M <;> simp_all +decide [ Finset.sum_ite ];
  exact Finset.card_eq_one.mpr ⟨ he.choose, Finset.eq_singleton_iff_unique_mem.mpr ⟨ Finset.mem_filter.mpr ⟨ Finset.mem_univ _, he.choose_spec ⟩, fun j hj => Classical.not_not.1 fun hj' => Finset.disjoint_left.mp ( hdisj _ _ hj' ) ( Finset.mem_filter.mp hj |>.2 ) he.choose_spec ⟩ ⟩

/-
**Lemma 2.1.** A two-element pair labeling with the local evenness condition yields a
cycle double cover.
-/
/-- Cubicity is unnecessary here: the local multiplicity condition alone supplies the
vertex-degree information needed by the cycle decomposition. -/
theorem pairLabeling_gives_cycleDoubleCover
    (hloopless : G.Loopless)
    (P : E → Finset Gamma) (hcard : ∀ e, (P e).card = 2)
    (hloc : ∀ (v : V) (s : Gamma),
      ((G.incidentEdges v).filter (fun e => s ∈ P e)).card = 0 ∨
      ((G.incidentEdges v).filter (fun e => s ∈ P e)).card = 2) :
    G.HasCycleDoubleCover := by
  -- For each label `s`, decompose the edges carrying `s` into connected cycles.
  -- Choice packages the resulting finite cycle families into one family indexed by `s`.
  obtain ⟨n, C, hC⟩ : ∃ (n : Gamma → ℕ) (C : ∀ s, Fin (n s) → Finset E),
      (∀ s, ∀ i, G.IsCycle (C s i)) ∧
      (∀ s, ∀ i j, i ≠ j → Disjoint (C s i) (C s j)) ∧
      ∀ s, Finset.univ.filter (fun e => s ∈ P e) = Finset.univ.biUnion (C s) := by
        have h_partition : ∀ s : Gamma, ∃ (n : ℕ) (C : Fin n → Finset E),
            (∀ i, G.IsCycle (C i)) ∧
            (∀ i j, i ≠ j → Disjoint (C i) (C j)) ∧
            Finset.univ.filter (fun e => s ∈ P e) = Finset.univ.biUnion C := by
              intro s
              apply exists_cycle_partition_of_degree_zero_or_two;
              · exact hloopless;
              · intro v
                specialize hloc v s
                simp_all +decide [ OrientedMultiGraph.degreeIn_loopless ];
                simp_all +decide [ Finset.filter_filter, OrientedMultiGraph.incidentEdges ];
                simp_all +decide [ and_comm, Finset.filter_congr ];
                exact Or.imp ( fun h x hx hx' => h hx' hx ) id hloc;
        choose n C hC₁ hC₂ hC₃ using h_partition; exact ⟨ n, C, hC₁, hC₂, hC₃ ⟩ ;
  convert hasCycleDoubleCover_of_fintypeFamily ( fun p : Σ s, Fin ( n s ) => C p.fst p.snd ) ( fun p => hC.1 _ _ ) ( fun e => ?_ ) using 1;
  rw [ Fintype.sum_sigma ];
  rw [ Finset.sum_congr rfl fun s hs => ?_ ];
  rotate_left;
  use fun s => if e ∈ Finset.univ.biUnion ( C s ) then 1 else 0;
  · convert partition_count ( C s ) ( hC.2.1 s ) ( Finset.univ.biUnion ( C s ) ) rfl e using 1;
  · simp +decide [ ← hC.2.2, hcard ]

end OrientedMultiGraph

end CycleDoubleCover