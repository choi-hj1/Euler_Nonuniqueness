import EulerNonuniqueness.Section3.FixedRelabelDerivativeConjugacy
import EulerNonuniqueness.Section3.DiskPhysicalExponential
import EulerNonuniqueness.General.LinearExponentialConjugacy

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance relabeledPeriodHolderSpace : NormedSpace ℝ PeriodicHolderHalf := Submodule.normedSpace periodicHolderGraph
local instance relabeledPeriodC1Space : NormedSpace ℝ PeriodicC1HolderHalf := Submodule.normedSpace periodicC1HolderGraph

theorem relabeledDiskDerivative_exp_conjugacy (angular : PeriodicC1HolderHalf)
    (angularSmall : ‖angular‖ < 1 / 2)
    (realValues : ∀ label, star (angular.val.1 label) = angular.val.1 label)
    (composedSmall : ‖diskRelabelCurve angular 1 - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)))
    (time : ℝ) :
    EulerNonuniqueness.General.linearExponentialGroup (Space := PeriodicC1HolderHalf)
      (relabeledDiskDerivative angular) time =
    (fixedRelabelEquivalence angular angularSmall).toContinuousLinearMap.comp
      ((EulerNonuniqueness.General.linearExponentialGroup (Space := PeriodicC1HolderHalf)
        diskRotatingDerivative time).comp
        (fixedRelabelEquivalence angular angularSmall).symm.toContinuousLinearMap) := by
  with_reducible
    exact EulerNonuniqueness.General.linearExponentialGroup_conjugacy
      (Space := PeriodicC1HolderHalf) (fixedRelabelEquivalence angular angularSmall)
      diskRotatingDerivative (relabeledDiskDerivative angular)
      (relabeledDiskDerivative_intertwines angular angularSmall realValues composedSmall) time

theorem relabeledDiskDerivative_exp_period (angular : PeriodicC1HolderHalf)
    (angularSmall : ‖angular‖ < 1 / 2)
    (realValues : ∀ label, star (angular.val.1 label) = angular.val.1 label)
    (composedSmall : ‖diskRelabelCurve angular 1 - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) :
    EulerNonuniqueness.General.linearExponentialGroup (Space := PeriodicC1HolderHalf)
      (relabeledDiskDerivative angular) (4 * Real.pi) =
      ContinuousLinearMap.id ℝ PeriodicC1HolderHalf := by
  with_reducible
    exact EulerNonuniqueness.General.linearExponentialGroup_period_of_conjugacy
      (Space := PeriodicC1HolderHalf) (fixedRelabelEquivalence angular angularSmall)
      diskRotatingDerivative (relabeledDiskDerivative angular)
      (relabeledDiskDerivative_intertwines angular angularSmall realValues composedSmall)
      diskRotatingDerivative_exp_period

end

end EulerNonuniqueness.Paper
