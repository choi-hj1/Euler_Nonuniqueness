import EulerNonuniqueness.Section3.DiskSpectralFiberCoefficientBounds
import EulerNonuniqueness.General.InversePerturbationTaylor

noncomputable section

open Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

local instance inverseFiberTaylorC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule
  diskChartedEulerOperatorRing diskChartedEulerOperatorAlgebra diskChartedEulerOperatorComplete

theorem diskSpectralTubularChart_eventually_derivative_difference :
    ∀ᶠ value in 𝓝 (0 : PeriodicC1HolderHalf),
      fderiv ℝ diskSpectralTubularChart value - diskChartedSpectralCoordinates value =
        (fderiv ℝ diskChartedSpectralCoordinates (diskRelabelNeutralCLM value)).flip
          (value - diskRelabelNeutralCLM value) := by
  have neutralLimit : Tendsto diskRelabelNeutralCLM (𝓝 (0 : PeriodicC1HolderHalf)) (𝓝 0) := by
    simpa only [map_zero] using diskRelabelNeutralCLM.continuous.tendsto (0 : PeriodicC1HolderHalf)
  filter_upwards [neutralLimit.eventually diskSpectralTubularChart_eventually_fiber_derivative]
    with value derivative
  have kernel : diskRelabelNeutralCLM (value - diskRelabelNeutralCLM value) = 0 := by
    rw [map_sub, diskRelabelNeutralCLM_idempotent, sub_self]
  have sumIdentity : diskRelabelNeutralCLM value + (value - diskRelabelNeutralCLM value) = value := by abel
  apply ContinuousLinearMap.ext
  intro direction
  have actual := derivative (diskRelabelNeutralCLM_idempotent value)
    (value - diskRelabelNeutralCLM value) kernel direction
  rw [sumIdentity, diskChartedSpectralCoordinates_neutral_parameter] at actual
  change fderiv ℝ diskSpectralTubularChart value direction -
    diskChartedSpectralCoordinates value direction =
      fderiv ℝ diskChartedSpectralCoordinates (diskRelabelNeutralCLM value) direction
        (value - diskRelabelNeutralCLM value)
  rw [actual]
  abel

theorem diskChartedSpectralCoordinates_eventually_isUnit :
    ∀ᶠ value in 𝓝 (0 : PeriodicC1HolderHalf), IsUnit (diskChartedSpectralCoordinates value) := by
  filter_upwards [diskChartedSpectralCoordinates_eventually_conjugacy] with value equivalent
  obtain ⟨coordinates, identity, _intertwines⟩ := equivalent
  rw [identity]
  exact ⟨coordinates.toUnit, rfl⟩

theorem diskSpectralTubularChart_eventually_jacobian_isUnit :
    ∀ᶠ value in 𝓝 (0 : PeriodicC1HolderHalf), IsUnit (fderiv ℝ diskSpectralTubularChart value) := by
  filter_upwards [diskSpectralTubularChart_eventually_jacobian_equivalence] with value equivalent
  obtain ⟨coordinates, derivative, _inverse⟩ := equivalent
  rw [derivative.fderiv]
  exact ⟨coordinates.toUnit, rfl⟩

theorem diskSpectralTubularInverseDerivative_exists_fiber_quadratic_remainder :
    ∃ constant ≥ 0, ∀ᶠ value in 𝓝 (0 : PeriodicC1HolderHalf),
      ‖diskSpectralTubularInverseDerivative value - Ring.inverse (diskChartedSpectralCoordinates value) +
        Ring.inverse (diskChartedSpectralCoordinates value) *
          (fderiv ℝ diskChartedSpectralCoordinates (diskRelabelNeutralCLM value)).flip
            (value - diskRelabelNeutralCLM value) *
          Ring.inverse (diskChartedSpectralCoordinates value)‖ ≤
        constant * ‖value - diskRelabelNeutralCLM value‖ ^ 2 := by
  obtain ⟨coordinateBound, coordinateNonnegative, jacobianBound, jacobianNonnegative, inverseBounds⟩ :=
    diskSpectralFiberInverse_exists_uniform_bounds
  obtain ⟨differentialBound, differentialNonnegative, differenceBounds⟩ :=
    diskSpectralFiberJacobianDifference_exists_uniform_bound
  let inverseBound := max coordinateBound jacobianBound
  refine ⟨inverseBound ^ 3 * differentialBound ^ 2, by dsimp only [inverseBound]; positivity, ?_⟩
  filter_upwards [inverseBounds, differenceBounds, diskSpectralTubularChart_eventually_derivative_difference,
    diskChartedSpectralCoordinates_eventually_isUnit, diskSpectralTubularChart_eventually_jacobian_isUnit]
    with value inverses difference derivativeDifference coordinateUnit jacobianUnit
  let increment := fderiv ℝ diskSpectralTubularChart value - diskChartedSpectralCoordinates value
  have sumIdentity : diskChartedSpectralCoordinates value + increment =
      fderiv ℝ diskSpectralTubularChart value := by dsimp only [increment]; abel
  have sumUnit : IsUnit (diskChartedSpectralCoordinates value + increment) := sumIdentity ▸ jacobianUnit
  have baseBound : ‖Ring.inverse (diskChartedSpectralCoordinates value)‖ ≤ inverseBound :=
    inverses.1.trans (le_max_left _ _)
  have sumBound : ‖Ring.inverse (diskChartedSpectralCoordinates value + increment)‖ ≤ inverseBound := by
    rw [sumIdentity]
    exact inverses.2.trans (le_max_right _ _)
  have bound : ‖Ring.inverse (diskChartedSpectralCoordinates value + increment) -
      Ring.inverse (diskChartedSpectralCoordinates value) +
        Ring.inverse (diskChartedSpectralCoordinates value) * increment *
          Ring.inverse (diskChartedSpectralCoordinates value)‖ ≤
      inverseBound ^ 3 * differentialBound ^ 2 * ‖value - diskRelabelNeutralCLM value‖ ^ 2 := by
    with_reducible
      exact EulerNonuniqueness.General.norm_inverse_perturbation_linear_remainder_le_uniform
        (diskChartedSpectralCoordinates value) increment coordinateUnit sumUnit baseBound sumBound difference
  rw [sumIdentity] at bound
  change ‖Ring.inverse (fderiv ℝ diskSpectralTubularChart value) -
      Ring.inverse (diskChartedSpectralCoordinates value) +
        Ring.inverse (diskChartedSpectralCoordinates value) * _ *
          Ring.inverse (diskChartedSpectralCoordinates value)‖ ≤ _
  dsimp only [increment] at bound
  rw [derivativeDifference] at bound
  exact bound

end EulerNonuniqueness.Paper
