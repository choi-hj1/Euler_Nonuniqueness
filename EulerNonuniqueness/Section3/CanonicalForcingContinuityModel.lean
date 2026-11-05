import EulerNonuniqueness.Section3.CanonicalForcingAdditiveModel
import EulerNonuniqueness.Section3.DiskNormalizedInteractionContinuity

noncomputable section

open Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] normalizedUniformSlopeC1Group chartedBilinearC1Space
  canonicalForcingAddCommGroup canonicalForcingAdd canonicalForcingZero canonicalForcingNeg canonicalForcingSub

theorem diskNormalizedInteraction_exists_uniform_canonical_continuity :
    ∃ radius > 0, ∀ {curve : ℝ → PeriodicC1HolderHalf} {time frequency : ℝ},
      ‖curve time - standardCircleBanach‖ ≤ radius → ContinuousAt curve time →
      ContinuousAt (fun current => diskPhysicalScaledGroup frequency (-current)
        (diskNormalizedQuadraticObservable (curve current))) time := by
  with_reducible_and_instances
    exact diskNormalizedInteraction_exists_uniform_continuity

end EulerNonuniqueness.Paper
