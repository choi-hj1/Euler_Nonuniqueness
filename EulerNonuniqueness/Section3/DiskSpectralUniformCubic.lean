import EulerNonuniqueness.Section3.DiskSpectralFiberCubicIdentity
import EulerNonuniqueness.Section3.DiskSpectralFiberCoefficientBounds
import EulerNonuniqueness.Section3.DiskSpectralRawCubic

namespace EulerNonuniqueness.Paper

noncomputable section

open Filter
open scoped Topology

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule
  diskChartedEulerOperatorRing diskChartedEulerOperatorAlgebra diskChartedEulerOperatorComplete

def diskSpectralFiberQuadraticValue (increment : PeriodicC1HolderHalf) : PeriodicC1HolderHalf :=
  let relative := increment - diskRelabelNeutralCLM increment
  let image := diskChartedSpectralCoordinates increment relative
  Ring.inverse (diskChartedSpectralCoordinates increment)
    (diskMovingQuadraticBilinear (diskRelabelNeutralCLM increment) image image)

theorem diskSpectralTubularEulerField_exists_uniform_transverse_cubic :
    ∃ constant ≥ 0, ∀ᶠ increment in 𝓝 (0 : PeriodicC1HolderHalf),
      ‖diskSpectralTubularEulerField increment -
          diskRotatingDerivative (increment - diskRelabelNeutralCLM increment) -
          diskSpectralFiberQuadraticValue increment‖ ≤
        constant * ‖increment - diskRelabelNeutralCLM increment‖ ^ 3 := by
  obtain ⟨remainderConstant, remainderNonnegative, remainderEstimate⟩ :=
    diskSpectralRawFiberRemainder_exists_uniform_cubic
  obtain ⟨quadraticConstant, quadraticNonnegative, quadraticEstimate⟩ :=
    diskSpectralFiberQuadratic_exists_uniform_bound
  obtain ⟨correctionConstant, correctionNonnegative, correctionEstimate⟩ :=
    diskSpectralFiberJacobianDifference_exists_uniform_bound
  obtain ⟨coordinateConstant, coordinateNonnegative, jacobianConstant, jacobianNonnegative, inverses⟩ :=
    diskSpectralFiberInverse_exists_uniform_bounds
  refine ⟨jacobianConstant * remainderConstant +
    jacobianConstant * correctionConstant * coordinateConstant * quadraticConstant, by positivity, ?_⟩
  filter_upwards [remainderEstimate, quadraticEstimate, correctionEstimate, inverses,
    diskSpectralTubularEulerField_eventually_cubic_error_identity]
    with increment remainderBound quadraticBound correctionBound inverseBounds exactError
  obtain ⟨coordinates, jacobian, coordinateIdentity, jacobianIdentity, errorIdentity⟩ := exactError
  have coordinateInverse : Ring.inverse (diskChartedSpectralCoordinates increment) =
      coordinates.symm.toContinuousLinearMap := by
    rw [coordinateIdentity]
    with_reducible
      exact EulerNonuniqueness.General.ring_inverse_continuousLinearEquiv (Space := PeriodicC1HolderHalf) coordinates
  have jacobianInverse : diskSpectralTubularInverseDerivative increment =
      jacobian.symm.toContinuousLinearMap := by
    unfold diskSpectralTubularInverseDerivative
    rw [jacobianIdentity]
    with_reducible
      exact EulerNonuniqueness.General.ring_inverse_continuousLinearEquiv (Space := PeriodicC1HolderHalf) jacobian
  have coordinateAction (value : PeriodicC1HolderHalf) :
      coordinates value = diskChartedSpectralCoordinates increment value :=
    congrArg (fun linear : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf => linear value) coordinateIdentity.symm
  let relative := increment - diskRelabelNeutralCLM increment
  let quadratic := diskMovingQuadraticBilinear (diskRelabelNeutralCLM increment)
    (diskChartedSpectralCoordinates increment relative) (diskChartedSpectralCoordinates increment relative)
  let correction : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf :=
    fderiv ℝ diskSpectralTubularChart increment - diskChartedSpectralCoordinates increment
  let inverseJacobian := diskSpectralTubularInverseDerivative increment
  let inverseCoordinates := Ring.inverse (diskChartedSpectralCoordinates increment)
  let error := diskSpectralTubularEulerField increment - diskRotatingDerivative relative -
    diskSpectralFiberQuadraticValue increment
  have inverseCoordinateAction (value : PeriodicC1HolderHalf) : coordinates.symm value = inverseCoordinates value := by
    exact congrArg (fun linear : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf => linear value) coordinateInverse.symm
  have inverseJacobianAction (value : PeriodicC1HolderHalf) : jacobian.symm value = inverseJacobian value := by
    exact congrArg (fun linear : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf => linear value) jacobianInverse.symm
  have identity : error = inverseJacobian (diskSpectralRawFiberRemainder increment) -
      inverseJacobian (correction (inverseCoordinates quadratic)) := by
    dsimp only at errorIdentity
    simp_rw [coordinateAction, inverseCoordinateAction, inverseJacobianAction] at errorIdentity
    rw [← coordinateIdentity] at errorIdentity
    dsimp only [error, diskSpectralFiberQuadraticValue, diskSpectralRawFiberRemainder,
      relative, quadratic, correction, inverseCoordinates] at errorIdentity ⊢
    with_reducible exact errorIdentity
  with_reducible
    exact EulerNonuniqueness.General.norm_fiber_error_le_of_identity (Space := PeriodicC1HolderHalf)
      (size := ‖relative‖) (remainderConstant := remainderConstant) (quadraticConstant := quadraticConstant)
      (correctionConstant := correctionConstant) (jacobianConstant := jacobianConstant)
      (coordinateConstant := coordinateConstant)
      inverseJacobian inverseCoordinates correction error (diskSpectralRawFiberRemainder increment) quadratic identity
      remainderNonnegative quadraticNonnegative correctionNonnegative jacobianNonnegative coordinateNonnegative
      (norm_nonneg relative) remainderBound quadraticBound correctionBound inverseBounds.2 inverseBounds.1

end

end EulerNonuniqueness.Paper
