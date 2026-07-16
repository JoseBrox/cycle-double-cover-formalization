import RequestProject.Core
import RequestProject.OrientationInvariance
import RequestProject.Global
import RequestProject.Examples

namespace CycleDoubleCover

/-!
# Cycle Double Cover — top-level module

* `OrientedMultiGraph.cycleDoubleCover_of_nowhereZero_gammaFlow` — the paper's self-contained
  core reduction, fully proved (without proof placeholders or project postulates).
* `OrientedMultiGraph.cycleDoubleCoverConjecture_of_gammaFlow_of_cubicReduction` — the
  conditional global conclusion, assembled from the core and two imported theorem interfaces
  (`NowhereZeroGammaFlowTheorem`, `CubicReductionTheorem`) taken as explicit hypotheses.
* `OrientedMultiGraph.SameEndpoints.hasCycleDoubleCover` — orientation invariance.
-/

end CycleDoubleCover
