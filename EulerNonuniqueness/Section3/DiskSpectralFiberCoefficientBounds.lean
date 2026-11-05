import EulerNonuniqueness.Section3.DiskSpectralFiberDerivative
import EulerNonuniqueness.Section3.DiskMovingQuadraticTaylor
import EulerNonuniqueness.General.LocalFiberOperatorBounds
import EulerNonuniqueness.General.IdentityInverseContinuity

namespace EulerNonuniqueness.Paper

noncomputable section

open Filter
open scoped Topology

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule
  diskChartedEulerOperatorRing diskChartedEulerOperatorAlgebra diskChartedEulerOperatorComplete

theorem diskChartedSpectralCoordinates_inverse_continuousAt_zero :
    ContinuousAt (fun increment => Ring.inverse (diskChartedSpectralCoordinates increment))
      (0 : PeriodicC1HolderHalf) := by
  have continuous : ContinuousAt diskChartedSpectralCoordinates (0 : PeriodicC1HolderHalf) := by
    with_reducible
      exact diskChartedSpectralCoordinates_hasLipschitzDerivativeNear.differentiableAt.continuousAt
  with_reducible
    exact EulerNonuniqueness.General.continuousAt_inverse_family_of_identity
      (Space := PeriodicC1HolderHalf) diskChartedSpectralCoordinates continuous diskChartedSpectralCoordinates_zero

theorem diskSpectralTubularInverseDerivative_continuousAt_zero :
    ContinuousAt diskSpectralTubularInverseDerivative (0 : PeriodicC1HolderHalf) := by
  have continuous : ContinuousAt (fderiv ℝ diskSpectralTubularChart) (0 : PeriodicC1HolderHalf) :=
    diskSpectralTubularChart_hasLipschitzDerivativeNear.2.continuousAt
  have identity : fderiv ℝ diskSpectralTubularChart (0 : PeriodicC1HolderHalf) =
      ContinuousLinearMap.id ℝ PeriodicC1HolderHalf := by
    with_reducible
      exact HasFDerivAt.fderiv (𝕜 := ℝ) (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf)
        (HasStrictFDerivAt.hasFDerivAt (𝕜 := ℝ) (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf)
          diskSpectralTubularChart_hasStrictFDerivAt_zero)
  let derivative : PeriodicC1HolderHalf → PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf :=
    fderiv ℝ diskSpectralTubularChart
  unfold diskSpectralTubularInverseDerivative
  with_reducible
    exact EulerNonuniqueness.General.continuousAt_inverse_family_of_identity
      (Space := PeriodicC1HolderHalf) derivative continuous identity

theorem diskSpectralFiberQuadratic_exists_uniform_bound :
    ∃ bound ≥ 0, ∀ᶠ increment in 𝓝 (0 : PeriodicC1HolderHalf),
      let relative := increment - diskRelabelNeutralCLM increment
      ‖diskMovingQuadraticBilinear (diskRelabelNeutralCLM increment)
        (diskChartedSpectralCoordinates increment relative)
        (diskChartedSpectralCoordinates increment relative)‖ ≤ bound * ‖relative‖ ^ 2 := by
  have continuous : ContinuousAt diskChartedSpectralCoordinates (0 : PeriodicC1HolderHalf) := by
    with_reducible
      exact diskChartedSpectralCoordinates_hasLipschitzDerivativeNear.differentiableAt.continuousAt
  let second : PeriodicC1HolderHalf → EulerNonuniqueness.General.BilinearEnd PeriodicC1HolderHalf :=
    fderiv ℝ (fderiv ℝ diskChartedEulerField)
  have secondContinuous : ContinuousAt second (0 : PeriodicC1HolderHalf) :=
    diskChartedEulerField_derivative_hasLipschitzDerivativeNear.2.continuousAt
  simp_rw [diskMovingQuadraticBilinear_apply]
  with_reducible
    exact EulerNonuniqueness.General.exists_eventually_half_quadratic_fiber_bound
      (Space := PeriodicC1HolderHalf) diskRelabelNeutralCLM diskChartedSpectralCoordinates
      second continuous secondContinuous

theorem diskSpectralFiberInverse_exists_uniform_bounds :
    ∃ coordinateBound ≥ 0, ∃ jacobianBound ≥ 0,
      ∀ᶠ increment in 𝓝 (0 : PeriodicC1HolderHalf),
        ‖Ring.inverse (diskChartedSpectralCoordinates increment)‖ ≤ coordinateBound ∧
        ‖diskSpectralTubularInverseDerivative increment‖ ≤ jacobianBound := by
  obtain ⟨coordinateBound, coordinateNonnegative, coordinates⟩ :=
    EulerNonuniqueness.General.exists_eventually_norm_bound (Space := PeriodicC1HolderHalf)
      (Target := PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf)
      diskChartedSpectralCoordinates_inverse_continuousAt_zero
  obtain ⟨jacobianBound, jacobianNonnegative, jacobians⟩ :=
    EulerNonuniqueness.General.exists_eventually_norm_bound (Space := PeriodicC1HolderHalf)
      (Target := PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf)
      diskSpectralTubularInverseDerivative_continuousAt_zero
  exact ⟨coordinateBound, coordinateNonnegative, jacobianBound, jacobianNonnegative,
    coordinates.and jacobians⟩

theorem diskSpectralFiberJacobianDifference_exists_uniform_bound :
    ∃ bound ≥ 0, ∀ᶠ increment in 𝓝 (0 : PeriodicC1HolderHalf),
      ‖fderiv ℝ diskSpectralTubularChart increment - diskChartedSpectralCoordinates increment‖ ≤
        bound * ‖increment - diskRelabelNeutralCLM increment‖ := by
  let differential : PeriodicC1HolderHalf → EulerNonuniqueness.General.BilinearEnd PeriodicC1HolderHalf :=
    fderiv ℝ diskChartedSpectralCoordinates
  let jacobian : PeriodicC1HolderHalf → PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf :=
    fderiv ℝ diskSpectralTubularChart
  have continuous : ContinuousAt differential (0 : PeriodicC1HolderHalf) :=
    diskChartedSpectralCoordinates_hasLipschitzDerivativeNear.2.continuousAt
  with_reducible
    exact EulerNonuniqueness.General.exists_eventually_jacobian_fiber_difference_bound
      (Space := PeriodicC1HolderHalf) diskRelabelNeutralCLM diskChartedSpectralCoordinates jacobian differential
      diskRelabelNeutralCLM_idempotent diskChartedSpectralCoordinates_neutral_parameter continuous
      diskSpectralTubularChart_eventually_fiber_derivative

end

end EulerNonuniqueness.Paper
