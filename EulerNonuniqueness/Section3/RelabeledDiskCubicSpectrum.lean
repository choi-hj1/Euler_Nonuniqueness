import EulerNonuniqueness.Section3.DiskPhysicalCubicSpectrum
import EulerNonuniqueness.Section3.FixedRelabelDerivativeConjugacy
import EulerNonuniqueness.General.CubicSpectralConjugacy

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance relabeledCubicC1Space : NormedSpace ℝ PeriodicC1HolderHalf := Submodule.normedSpace periodicC1HolderGraph

theorem relabeledDiskDerivative_cubic (angular : PeriodicC1HolderHalf)
    (angularSmall : ‖angular‖ < 1 / 2)
    (realValues : ∀ label, star (angular.val.1 label) = angular.val.1 label)
    (composedSmall : ‖diskRelabelCurve angular 1 - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)))
    (direction : PeriodicC1HolderHalf) :
    relabeledDiskDerivative angular (relabeledDiskDerivative angular (relabeledDiskDerivative angular direction)) =
      (-1 / 4 : ℝ) • relabeledDiskDerivative angular direction := by
  with_reducible
    exact EulerNonuniqueness.General.cubic_spectrum_of_surjective_intertwines
      (Space := PeriodicC1HolderHalf) (relabeledDiskDerivative angular) diskRotatingDerivative
      (fixedRelabelEquivalence angular angularSmall).toContinuousLinearMap
      (fixedRelabelEquivalence angular angularSmall).surjective
      (relabeledDiskDerivative_intertwines angular angularSmall realValues composedSmall)
      diskRotatingDerivative_cubic direction

end

end EulerNonuniqueness.Paper
