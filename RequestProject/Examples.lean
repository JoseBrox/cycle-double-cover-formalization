import RequestProject.Core
import RequestProject.PairLabels
import RequestProject.OrientationInvariance

open scoped BigOperators

set_option autoImplicit false

namespace CycleDoubleCover

namespace OrientedMultiGraph

/-! ## Regression examples -/

/-- Two vertices joined by two parallel edges. -/
def parallelPair : OrientedMultiGraph (Fin 2) (Fin 2) where
  src := fun _ => 0
  dst := fun _ => 1

lemma parallelPair_loopless : parallelPair.Loopless := by
  intro e; fin_cases e <;> decide

/-
Two parallel edges form a genuine cycle (a 2-cycle).
-/
lemma parallelPair_isCycle : parallelPair.IsCycle Finset.univ := by
  refine' ⟨ _, _, _ ⟩ <;> simp +decide [ IsCycle ]

/-- Reversing the orientation of one edge does not change the set of cycle double covers. -/
def parallelPair' : OrientedMultiGraph (Fin 2) (Fin 2) where
  src := ![0, 1]
  dst := ![1, 0]

lemma parallelPair_sameEndpoints : SameEndpoints parallelPair parallelPair' := by
  intro e; fin_cases e <;> decide

/-- Orientation invariance applied to the parallel pair: the reversed orientation has a cycle
double cover iff the original does. -/
lemma parallelPair_orientation_invariant :
    parallelPair.HasCycleDoubleCover ↔ parallelPair'.HasCycleDoubleCover :=
  parallelPair_sameEndpoints.hasCycleDoubleCover

/-! ### A 3-edge-colourable cubic multigraph: the dipole `Θ` (three parallel edges) -/

/-- The dipole: two vertices joined by three parallel edges.  It is loopless, cubic and
3-edge-colourable. -/
def dipole : OrientedMultiGraph (Fin 2) (Fin 3) where
  src := fun _ => 0
  dst := fun _ => 1

lemma dipole_loopless : dipole.Loopless := by
  intro e; fin_cases e <;> decide

lemma dipole_cubic : dipole.Cubic := by
  intro v; fin_cases v <;> decide

/-- A nowhere-zero `Γ`-flow on the dipole (values `(1,0,0), (0,1,0), (1,1,0)` summing to `0`). -/
def dipoleFlow : Fin 3 → Gamma := ![![1, 0, 0], ![0, 1, 0], ![1, 1, 0]]

lemma dipoleFlow_isFlow : dipole.IsFlow dipoleFlow := by
  intro v; fin_cases v <;> simp +decide [ dipole, dipoleFlow ] ;

lemma dipoleFlow_nowhereZero : NowhereZero dipoleFlow := by
  intro e; fin_cases e <;> decide;

/-- The dipole (a 3-edge-colourable cubic multigraph) has a cycle double cover, obtained by
applying the **self-contained core theorem** to a concrete nowhere-zero `Γ`-flow. -/
lemma dipole_hasCycleDoubleCover_via_core : dipole.HasCycleDoubleCover :=
  dipole.cycleDoubleCover_of_nowhereZero_gammaFlow dipole_loopless dipole_cubic dipoleFlow
    dipoleFlow_isFlow dipoleFlow_nowhereZero

/-- The dipole has a cycle double cover, exhibited directly as three `2`-cycles (each pair of
parallel edges), covering every edge exactly twice. -/
lemma dipole_hasCycleDoubleCover : dipole.HasCycleDoubleCover := by
  fconstructor;
  exact 3;
  use fun i => if i = 0 then {0, 1} else if i = 1 then {1, 2} else {0, 2};
  simp +decide [ OrientedMultiGraph.IsCycle ]

end OrientedMultiGraph

end CycleDoubleCover
