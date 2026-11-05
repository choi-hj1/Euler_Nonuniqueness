import EulerNonuniqueness.Section3.DiskSpectralFiberDerivative
import EulerNonuniqueness.Section3.DiskMovingQuadraticTaylor
import EulerNonuniqueness.General.InverseFiberCubicCorrection

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

theorem diskSpectralTubularEulerField_eventually_cubic_error_identity :
    ∀ᶠ increment in 𝓝 (0 : PeriodicC1HolderHalf),
      ∃ coordinates jacobian : PeriodicC1HolderHalf ≃L[ℝ] PeriodicC1HolderHalf,
        diskChartedSpectralCoordinates increment = coordinates.toContinuousLinearMap ∧
        fderiv ℝ diskSpectralTubularChart increment = jacobian.toContinuousLinearMap ∧
        let relative := increment - diskRelabelNeutralCLM increment
        let quadratic := diskMovingQuadraticBilinear (diskRelabelNeutralCLM increment)
          (coordinates relative) (coordinates relative)
        let remainder := diskChartedEulerField (diskSpectralTubularChart increment) -
          coordinates (diskRotatingDerivative relative) - quadratic
        diskSpectralTubularEulerField increment - diskRotatingDerivative relative - coordinates.symm quadratic =
          jacobian.symm remainder - jacobian.symm
            ((fderiv ℝ diskSpectralTubularChart increment - coordinates.toContinuousLinearMap)
              (coordinates.symm quadratic)) := by
  have neutralLimit : Tendsto diskRelabelNeutralCLM (𝓝 (0 : PeriodicC1HolderHalf)) (𝓝 0) := by
    simpa only [map_zero] using diskRelabelNeutralCLM.continuous.tendsto (0 : PeriodicC1HolderHalf)
  filter_upwards [diskChartedSpectralCoordinates_eventually_conjugacy,
    diskSpectralTubularChart_eventually_jacobian_equivalence,
    neutralLimit.eventually diskSpectralTubularChart_eventually_fiber_linear_cancellation]
    with increment equivalent jacobianEquivalent cancellation
  obtain ⟨coordinates, coordinateIdentity, conjugacy⟩ := equivalent
  obtain ⟨jacobian, actualJacobian, inverseIdentity⟩ := jacobianEquivalent
  have jacobianIdentity : fderiv ℝ diskSpectralTubularChart increment = jacobian.toContinuousLinearMap := by
    with_reducible
      exact HasFDerivAt.fderiv (𝕜 := ℝ) (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf) actualJacobian
  refine ⟨coordinates, jacobian, coordinateIdentity, jacobianIdentity, ?_⟩
  let relative := increment - diskRelabelNeutralCLM increment
  have relativeKernel : diskRelabelNeutralCLM relative = 0 := by
    have linearity : diskRelabelNeutralCLM (increment - diskRelabelNeutralCLM increment) =
        diskRelabelNeutralCLM increment - diskRelabelNeutralCLM (diskRelabelNeutralCLM increment) := by
      with_reducible exact map_sub diskRelabelNeutralCLM increment (diskRelabelNeutralCLM increment)
    change diskRelabelNeutralCLM (increment - diskRelabelNeutralCLM increment) = 0
    rw [linearity, diskRelabelNeutralCLM_idempotent]
    with_reducible exact sub_self (diskRelabelNeutralCLM increment)
  have sumIdentity : diskRelabelNeutralCLM increment + relative = increment := by
    dsimp only [relative]
    abel
  have cancelled := cancellation (diskRelabelNeutralCLM_idempotent increment) relative relativeKernel relative
  rw [sumIdentity, diskChartedSpectralCoordinates_neutral_parameter, coordinateIdentity] at cancelled
  let correction : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf :=
    fderiv ℝ diskSpectralTubularChart increment - coordinates.toContinuousLinearMap
  have correctionIdentity : jacobian.toContinuousLinearMap = coordinates.toContinuousLinearMap + correction := by
    dsimp only [correction]
    rw [jacobianIdentity]
    abel
  have correctionCancellation : correction (diskRotatingDerivative relative) = 0 := by
    change fderiv ℝ diskSpectralTubularChart increment (diskRotatingDerivative relative) -
      coordinates (diskRotatingDerivative relative) = 0
    rw [cancelled]
    simpa only [ContinuousLinearEquiv.coe_coe] using sub_self (coordinates (diskRotatingDerivative relative))
  dsimp only
  let quadratic := diskMovingQuadraticBilinear (diskRelabelNeutralCLM increment)
    (coordinates relative) (coordinates relative)
  let remainder := diskChartedEulerField (diskSpectralTubularChart increment) -
    coordinates (diskRotatingDerivative relative) - quadratic
  have velocityIdentity : coordinates (diskRotatingDerivative relative) + quadratic + remainder =
      diskChartedEulerField (diskSpectralTubularChart increment) := by
    dsimp only [remainder]
    abel
  unfold diskSpectralTubularEulerField diskSpectralTubularInverseDerivative
  rw [inverseIdentity]
  change jacobian.symm (diskChartedEulerField (diskSpectralTubularChart increment)) -
    diskRotatingDerivative relative - coordinates.symm quadratic =
      jacobian.symm remainder - jacobian.symm (correction (coordinates.symm quadratic))
  rw [← velocityIdentity]
  with_reducible
    exact EulerNonuniqueness.General.inverse_fiber_cubic_correction_identity
      (Space := PeriodicC1HolderHalf) coordinates jacobian correction
      (diskRotatingDerivative relative) quadratic remainder correctionIdentity correctionCancellation

end

end EulerNonuniqueness.Paper
