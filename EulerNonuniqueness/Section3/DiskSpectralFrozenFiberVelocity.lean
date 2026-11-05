import EulerNonuniqueness.Section3.DiskSpectralInverseFiberTaylor
import EulerNonuniqueness.General.FrozenFiberVelocity

noncomputable section

open Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

local instance spectralFrozenFiberVelocityC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule
  diskChartedEulerOperatorRing diskChartedEulerOperatorAlgebra diskChartedEulerOperatorComplete

theorem diskSpectralTubularChart_exists_uniform_frozen_velocity_defect :
    ∃ constant ≥ 0, ∀ᶠ point in 𝓝 (0 : PeriodicC1HolderHalf), ∀ velocity : PeriodicC1HolderHalf,
      ‖Ring.inverse (diskChartedSpectralCoordinates point)
          (fderiv ℝ diskSpectralTubularChart point velocity) - velocity‖ ≤
        constant * ‖diskRelabelNeutralCLM velocity‖ * ‖point - diskRelabelNeutralCLM point‖ := by
  let differential : PeriodicC1HolderHalf → PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf :=
    fderiv ℝ diskChartedSpectralCoordinates
  have continuous : ContinuousAt differential (0 : PeriodicC1HolderHalf) :=
    diskChartedSpectralCoordinates_hasLipschitzDerivativeNear.2.continuousAt
  obtain ⟨differentialBound, differentialNonnegative, differentialBounds⟩ :=
    EulerNonuniqueness.General.exists_eventually_norm_bound continuous
  obtain ⟨inverseBound, inverseNonnegative, _, _, inverseBounds⟩ :=
    diskSpectralFiberInverse_exists_uniform_bounds
  have neutralLimit : Tendsto diskRelabelNeutralCLM (𝓝 (0 : PeriodicC1HolderHalf)) (𝓝 0) := by
    simpa only [map_zero] using diskRelabelNeutralCLM.continuous.tendsto (0 : PeriodicC1HolderHalf)
  refine ⟨inverseBound * differentialBound, by positivity, ?_⟩
  filter_upwards [inverseBounds, neutralLimit.eventually differentialBounds,
    diskChartedSpectralCoordinates_eventually_conjugacy,
    diskSpectralTubularChart_eventually_derivative_difference,
    neutralLimit.eventually diskChartedSpectralCoordinates_hasLipschitzDerivativeNear.1]
    with point inverseNorm differentialNorm conjugacy derivativeDifference regular velocity
  obtain ⟨coordinates, coordinateIdentity, _⟩ := conjugacy
  have inverseIdentity : Ring.inverse (diskChartedSpectralCoordinates point) =
      coordinates.symm.toContinuousLinearMap := by
    rw [coordinateIdentity]
    exact EulerNonuniqueness.General.ring_inverse_continuousLinearEquiv coordinates
  have actualRegular := regular.hasFDerivAt
  have factors : (differential (diskRelabelNeutralCLM point)).comp diskRelabelNeutralCLM =
      differential (diskRelabelNeutralCLM point) := by
    with_reducible_and_instances
      exact EulerNonuniqueness.General.operator_derivative_factors_projection
        diskRelabelNeutralCLM diskChartedSpectralCoordinates (diskRelabelNeutralCLM point)
        (differential (diskRelabelNeutralCLM point)) diskChartedSpectralCoordinates_neutral_parameter
        (diskRelabelNeutralCLM_idempotent point) actualRegular
  have factorApplied : differential (diskRelabelNeutralCLM point) (diskRelabelNeutralCLM velocity) =
      differential (diskRelabelNeutralCLM point) velocity :=
    congrArg (fun operator : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf =>
      operator velocity) factors
  have differenceApplied := congrArg (fun operator : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf =>
    operator velocity) derivativeDifference
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.flip_apply] at differenceApplied
  have actual : fderiv ℝ diskSpectralTubularChart point velocity = coordinates velocity +
      differential (diskRelabelNeutralCLM point) (diskRelabelNeutralCLM velocity)
        (point - diskRelabelNeutralCLM point) := by
    rw [factorApplied]
    have coordinateApplied : diskChartedSpectralCoordinates point velocity = coordinates velocity := by
      rw [coordinateIdentity]
      rfl
    rw [coordinateApplied] at differenceApplied
    exact sub_eq_iff_eq_add.mp differenceApplied |>.trans (add_comm _ _)
  have coordinateBound : ‖coordinates.symm.toContinuousLinearMap‖ ≤ inverseBound := by
    rw [← inverseIdentity]
    exact inverseNorm.1
  have estimate := EulerNonuniqueness.General.norm_frozen_fiber_velocity_difference_le coordinates
    (fderiv ℝ diskSpectralTubularChart point) diskRelabelNeutralCLM
    (differential (diskRelabelNeutralCLM point)) (point - diskRelabelNeutralCLM point) velocity
    inverseNonnegative differentialNonnegative coordinateBound differentialNorm actual
  rw [inverseIdentity]
  simpa only [ContinuousLinearEquiv.coe_coe] using estimate

end EulerNonuniqueness.Paper
