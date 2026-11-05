import EulerNonuniqueness.Section3.DiskAreaMeanProjection
import EulerNonuniqueness.Section3.DiskPhysicalCoordinates
import EulerNonuniqueness.General.QuadraticRemainderDerivative

namespace EulerNonuniqueness.Paper

noncomputable section

open Filter MeasureTheory
open scoped Topology

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance diskAreaDerivativeHolderSpace : NormedSpace ℝ PeriodicHolderHalf := Submodule.normedSpace periodicHolderGraph
local instance diskAreaDerivativeC1Space : NormedSpace ℝ PeriodicC1HolderHalf := Submodule.normedSpace periodicC1HolderGraph

def diskRadialMeanCLM : PeriodicC1HolderHalf →L[ℝ] ℝ :=
  Complex.reCLM.comp ((contourLabelEvaluation 0).comp
    ((periodicMeanProjectionCCLM.restrictScalars ℝ).comp diskRadialCLM))

theorem diskRadialMeanCLM_apply (direction : PeriodicC1HolderHalf) :
    diskRadialMeanCLM direction = diskRadialMean direction := by
  change ((periodicMeanProjectionCCLM (diskRadialPart direction)).val.1 0).re = diskRadialMean direction
  rw [periodicMeanProjection_diskRadialPart]
  rfl

theorem contourAreaFunctional_zero : contourAreaFunctional (0 : PeriodicC1HolderHalf) = 0 := by
  rw [contourAreaFunctional_eq_boundary]
  change (1 / 2 : ℝ) * (∫ label in (-Real.pi)..Real.pi, contourAreaPair 0 0) = 0
  simp [contourAreaPair]

theorem contourAreaFunctional_standardCircle : contourAreaFunctional standardCircleBanach = Real.pi := by
  have actual := contourAreaFunctional_circle_add (0 : PeriodicC1HolderHalf)
  have meanZero : diskRadialMean (0 : PeriodicC1HolderHalf) = 0 := by
    unfold diskRadialMean
    change (1 / (2 * Real.pi)) * (∫ label in (-Real.pi)..Real.pi, (star (standardCircle label) * 0).re) = 0
    simp
  simpa only [add_zero, meanZero, mul_zero, contourAreaFunctional_zero] using actual

theorem hasFDerivAt_contourAreaFunctional_circle :
    HasFDerivAt contourAreaFunctional ((2 * Real.pi) • diskRadialMeanCLM) standardCircleBanach := by
  have remainder : ∀ᶠ increment in 𝓝 (0 : PeriodicC1HolderHalf),
      ‖contourAreaFunctional (standardCircleBanach + increment) - contourAreaFunctional standardCircleBanach -
        (((2 * Real.pi) • diskRadialMeanCLM) increment)‖ ≤ Real.pi * ‖increment‖ ^ 2 := by
    filter_upwards [] with increment
    have identity : contourAreaFunctional (standardCircleBanach + increment) - contourAreaFunctional standardCircleBanach -
        (((2 * Real.pi) • diskRadialMeanCLM) increment) = contourAreaFunctional increment := by
      rw [contourAreaFunctional_circle_add, contourAreaFunctional_standardCircle,
        ContinuousLinearMap.smul_apply, diskRadialMeanCLM_apply]
      change Real.pi + (2 * Real.pi) * diskRadialMean increment + contourAreaFunctional increment - Real.pi -
        (2 * Real.pi) * diskRadialMean increment = _
      ring
    rw [identity, Real.norm_eq_abs]
    exact contourAreaFunctional_abs_le increment
  with_reducible
    exact EulerNonuniqueness.General.hasFDerivAt_of_eventual_quadratic_remainder
      (Domain := PeriodicC1HolderHalf) (Range := ℝ) contourAreaFunctional
      ((2 * Real.pi) • diskRadialMeanCLM) standardCircleBanach Real.pi_pos.le remainder

end

end EulerNonuniqueness.Paper
