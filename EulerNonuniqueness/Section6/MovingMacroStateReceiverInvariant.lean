import EulerNonuniqueness.Section6.MovingQuadrupoleMacroState
import EulerNonuniqueness.Section6.MovingQuadrupoleReceiverComparison

noncomputable section

namespace EulerNonuniqueness.Paper.MovingPatchFamilySourceComparison

set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

theorem withQuadrupoleReceivers_relativeMacroState {count : ℕ}
    (comparison : MovingPatchFamilySourceComparison (count * 4)) (receiver source : Fin count)
    (radius : ℝ) (nonnegative : 0 ≤ radius) (firstCenter secondCenter : ℂ) (scale : ℝ) :
    ((comparison.withQuadrupoleReceivers receiver radius nonnegative).quadrupole source).relativeMacroState
      firstCenter secondCenter scale = (comparison.quadrupole source).relativeMacroState firstCenter secondCenter scale := by
  with_reducible_and_instances
    dsimp only [relativeMacroState, withQuadrupoleReceivers, quadrupole, MovingPatchFamilySourceComparison.source,
      MovingPatchSourceComparison.spectralDifferenceBudget]

end EulerNonuniqueness.Paper.MovingPatchFamilySourceComparison
