import EulerNonuniqueness.Section3.DiskSpectralCubicCorrectionCoefficient
import EulerNonuniqueness.Section3.DiskSpectralUniformCubic

namespace EulerNonuniqueness.Paper

noncomputable section

open Filter
open scoped Topology

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule
  diskChartedEulerOperatorRing diskChartedEulerOperatorAlgebra diskChartedEulerOperatorComplete

theorem diskSpectralTubularEulerField_eventually_relative_cubic_identity :
    ∀ᶠ increment in 𝓝 (0 : PeriodicC1HolderHalf),
      let relative := increment - diskRelabelNeutralCLM increment
      diskSpectralTubularEulerField increment - diskRotatingDerivative relative -
          diskSpectralFiberQuadraticValue increment =
        diskSpectralTubularInverseDerivative increment (diskSpectralRawFiberRemainder increment) -
          diskSpectralTubularInverseDerivative increment
            (fderiv ℝ diskChartedSpectralCoordinates (diskRelabelNeutralCLM increment)
              (diskSpectralFiberQuadraticBilinear increment relative relative) relative) := by
  have neutralLimit : Tendsto diskRelabelNeutralCLM (𝓝 (0 : PeriodicC1HolderHalf)) (𝓝 0) := by
    simpa only [map_zero] using diskRelabelNeutralCLM.continuous.tendsto (0 : PeriodicC1HolderHalf)
  filter_upwards [diskSpectralTubularEulerField_eventually_cubic_error_identity,
    neutralLimit.eventually diskSpectralTubularChart_eventually_fiber_derivative]
    with increment exactError derivative
  obtain ⟨coordinates, jacobian, coordinateIdentity, jacobianIdentity, errorIdentity⟩ := exactError
  have coordinateInverse : Ring.inverse (diskChartedSpectralCoordinates increment) =
      coordinates.symm.toContinuousLinearMap := by
    rw [coordinateIdentity]
    with_reducible
      exact EulerNonuniqueness.General.ring_inverse_continuousLinearEquiv (Space := PeriodicC1HolderHalf) coordinates
  have jacobianInverse : diskSpectralTubularInverseDerivative increment = jacobian.symm.toContinuousLinearMap := by
    unfold diskSpectralTubularInverseDerivative
    rw [jacobianIdentity]
    with_reducible
      exact EulerNonuniqueness.General.ring_inverse_continuousLinearEquiv (Space := PeriodicC1HolderHalf) jacobian
  have coordinateAction (value : PeriodicC1HolderHalf) :
      coordinates value = diskChartedSpectralCoordinates increment value :=
    congrArg (fun linear : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf => linear value) coordinateIdentity.symm
  have inverseCoordinateAction (value : PeriodicC1HolderHalf) :
      coordinates.symm value = Ring.inverse (diskChartedSpectralCoordinates increment) value :=
    congrArg (fun linear : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf => linear value) coordinateInverse.symm
  have inverseJacobianAction (value : PeriodicC1HolderHalf) :
      jacobian.symm value = diskSpectralTubularInverseDerivative increment value :=
    congrArg (fun linear : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf => linear value) jacobianInverse.symm
  let relative := increment - diskRelabelNeutralCLM increment
  have kernel : diskRelabelNeutralCLM relative = 0 := by
    have linearity : diskRelabelNeutralCLM (increment - diskRelabelNeutralCLM increment) =
        diskRelabelNeutralCLM increment - diskRelabelNeutralCLM (diskRelabelNeutralCLM increment) := by
      with_reducible exact map_sub diskRelabelNeutralCLM increment (diskRelabelNeutralCLM increment)
    change diskRelabelNeutralCLM (increment - diskRelabelNeutralCLM increment) = 0
    rw [linearity, diskRelabelNeutralCLM_idempotent]
    with_reducible exact sub_self (diskRelabelNeutralCLM increment)
  have sumIdentity : diskRelabelNeutralCLM increment + relative = increment := by
    dsimp only [relative]
    abel
  have correctionIdentity (direction : PeriodicC1HolderHalf) :
      (fderiv ℝ diskSpectralTubularChart increment - diskChartedSpectralCoordinates increment) direction =
        fderiv ℝ diskChartedSpectralCoordinates (diskRelabelNeutralCLM increment) direction relative := by
    have actual := derivative (diskRelabelNeutralCLM_idempotent increment) relative kernel direction
    rw [sumIdentity, diskChartedSpectralCoordinates_neutral_parameter] at actual
    change fderiv ℝ diskSpectralTubularChart increment direction -
      diskChartedSpectralCoordinates increment direction = _
    rw [actual]
    abel
  dsimp only at errorIdentity
  simp_rw [coordinateAction, inverseCoordinateAction, inverseJacobianAction] at errorIdentity
  rw [← coordinateIdentity] at errorIdentity
  have initialIdentity : diskSpectralTubularEulerField increment - diskRotatingDerivative relative -
      diskSpectralFiberQuadraticValue increment =
      diskSpectralTubularInverseDerivative increment (diskSpectralRawFiberRemainder increment) -
        diskSpectralTubularInverseDerivative increment
          ((fderiv ℝ diskSpectralTubularChart increment - diskChartedSpectralCoordinates increment)
            (diskSpectralFiberQuadraticBilinear increment relative relative)) := by
    dsimp only [diskSpectralRawFiberRemainder, diskSpectralFiberQuadraticValue,
      diskSpectralFiberQuadraticBilinear, EulerNonuniqueness.General.bilinearPostcompose,
      ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.bilinearComp_apply,
      relative]
    with_reducible_and_instances
      exact errorIdentity
  have correctionValue := correctionIdentity (diskSpectralFiberQuadraticBilinear increment relative relative)
  have converted := congrArg (fun value : PeriodicC1HolderHalf =>
    diskSpectralTubularInverseDerivative increment (diskSpectralRawFiberRemainder increment) -
      diskSpectralTubularInverseDerivative increment value) correctionValue
  with_reducible_and_instances
    exact initialIdentity.trans converted

end

end EulerNonuniqueness.Paper
