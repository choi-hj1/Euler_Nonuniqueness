import EulerNonuniqueness.Section3.DiskSpectralMovingQuadraticLipschitz
import EulerNonuniqueness.Section3.DiskChartedThirdLipschitz
import EulerNonuniqueness.General.BilinearFiberRegularity

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule
  diskChartedEulerOperatorRing diskChartedEulerOperatorAlgebra diskChartedEulerOperatorComplete
  chartedThirdBilinearGroup chartedThirdBilinearSpace chartedThirdBilinearComplete

local instance spectralFiberRegularityC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

theorem diskSpectralFiberQuadraticBilinear_hasLipschitzDerivativeNear :
    EulerNonuniqueness.General.HasLipschitzDerivativeNear diskSpectralFiberQuadraticBilinear
      (0 : PeriodicC1HolderHalf) := by
  let inverse : PeriodicC1HolderHalf → PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf :=
    fun parameter => Ring.inverse (diskChartedSpectralCoordinates parameter)
  let rawSecond : PeriodicC1HolderHalf → EulerNonuniqueness.General.BilinearEnd PeriodicC1HolderHalf :=
    fderiv ℝ (fderiv ℝ diskChartedEulerField)
  let second : PeriodicC1HolderHalf → EulerNonuniqueness.General.BilinearEnd PeriodicC1HolderHalf :=
    fun parameter => rawSecond (diskRelabelNeutralCLM parameter)
  have coordinateRegular : EulerNonuniqueness.General.HasLipschitzDerivativeNear diskChartedSpectralCoordinates
      (0 : PeriodicC1HolderHalf) := by
    with_reducible_and_instances
      exact diskChartedSpectralCoordinates_hasLipschitzDerivativeNear
  have inverseRegular : EulerNonuniqueness.General.HasLipschitzDerivativeNear inverse (0 : PeriodicC1HolderHalf) := by
    with_reducible_and_instances
      exact EulerNonuniqueness.General.hasLipschitzDerivativeNear_inverse_family_of_identity
        (Space := PeriodicC1HolderHalf) diskChartedSpectralCoordinates
        diskChartedSpectralCoordinates_hasLipschitzDerivativeNear diskChartedSpectralCoordinates_zero
  have rawSecondRegular : EulerNonuniqueness.General.HasLipschitzDerivativeNear rawSecond
      (0 : PeriodicC1HolderHalf) := by
    have third := diskChartedEulerField_derivative_hasLipschitzSecondDerivativeNear
    unfold EulerNonuniqueness.General.HasLipschitzSecondDerivativeNear at third
    with_reducible_and_instances
      exact third.2
  have projectionRegular : EulerNonuniqueness.General.HasLipschitzDerivativeNear
      (fun parameter : PeriodicC1HolderHalf => diskRelabelNeutralCLM parameter) 0 := by
    with_reducible_and_instances
      exact EulerNonuniqueness.General.hasLipschitzDerivativeNear_continuousLinearMap
        (Space := PeriodicC1HolderHalf) (Target := PeriodicC1HolderHalf) diskRelabelNeutralCLM 0
  have secondRegular : EulerNonuniqueness.General.HasLipschitzDerivativeNear second (0 : PeriodicC1HolderHalf) := by
    apply EulerNonuniqueness.General.HasLipschitzDerivativeNear.comp (outer := rawSecond)
      (inner := fun parameter => diskRelabelNeutralCLM parameter)
    · simpa only [map_zero] using rawSecondRegular
    · exact projectionRegular
  have identity (parameter first right : PeriodicC1HolderHalf) :
      diskSpectralFiberQuadraticBilinear parameter first right = inverse parameter
        ((1 / 2 : ℝ) • second parameter
          (diskChartedSpectralCoordinates parameter first) (diskChartedSpectralCoordinates parameter right)) := by
    rw [diskSpectralFiberQuadraticBilinear_apply, diskMovingQuadraticBilinear_apply]
  with_reducible_and_instances
    exact EulerNonuniqueness.General.hasLipschitzDerivativeNear_bilinear_fiber_coefficient
      (Space := PeriodicC1HolderHalf) diskChartedSpectralCoordinates inverse second diskSpectralFiberQuadraticBilinear
      coordinateRegular inverseRegular secondRegular identity

end EulerNonuniqueness.Paper
